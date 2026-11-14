#!/usr/bin/env python3
"""Exercise the built CLI on disk, including refusals and tampered artifacts.

Run from lean/ on the designated Linux build host. All artifacts live in /tmp.
The JSON fixtures also document each adapter's input contract. MPC uses explicitly
small test parameters; custody uses the library's thincsCustody128Params.
"""
import copy
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

LEAN = Path(__file__).resolve().parents[2]
BIN = LEAN / '.lake/build/bin/obend'


def main():
    if os.uname().sysname != 'Linux':
        raise SystemExit('Run CLI smoke tests on hbox, never on macOS')
    checks = 0
    with tempfile.TemporaryDirectory(prefix='obend-s2d-cli-') as tmp:
        root = Path(tmp)

        def write(name, value):
            p = root / name
            p.write_text(json.dumps(value))
            return p

        def run(*args, code=0, timeout=180):
            nonlocal checks
            p = subprocess.run([str(BIN), *map(str, args)], cwd=LEAN,
                               capture_output=True, text=True, timeout=timeout,
                               env={**os.environ, 'XDG_STATE_HOME': str(root / 'xdg')})
            assert p.returncode == code, (args, p.returncode, p.stdout, p.stderr)
            if code in (2, 3):
                assert 'refus' in (p.stdout + p.stderr).lower() or 'reject' in (p.stdout + p.stderr).lower(), (args, p.stdout, p.stderr)
            checks += 1
            print('ok', *args[:2], flush=True)
            return p.stdout

        for help_arg in ('--help', '-h', 'help'):
            assert 'usage:' in run(help_arg)
        for cmd in ('amend', 'custody', 'bazaar', 'mpc', 'pde', 'notebook', 'run', 'run-core'):
            assert 'usage:' in run(cmd, '--help')
        for cmd in ('amend', 'custody', 'bazaar', 'mpc', 'pde', 'notebook'):
            run(cmd, code=2)
        source = root / 'Arithmetic.obend'
        source.write_text('def main() -> Nat:\n  return 6 * 7\n')
        run('run', source, 'NonExistentEntry', code=2)
        run('check', source, 'NonExistentEntry', code=2)
        normal = run('run', source, 'main')
        for flags in (['--jit'], ['--jit=cc'], ['--emit-c99', root / 'out.c']):
            got = run('run', source, 'main', *flags)
            assert re.search(r'result: (\d+)', got).group(1) == re.search(r'result: (\d+)', normal).group(1) == '42'
        assert 'result: 42' in run('run', '--jit=cc', source, 'main')
        assert 'obend_bytecode_jit_run' in (root / 'out.c').read_text()
        subprocess.run(['cc', '-std=c99', '-c', str(root / 'out.c'), '-o', str(root / 'out.o')], check=True)

        packet = dict(schema='dregg.objective-bend.typed-core.v3', types=[], annotations=[], bounds=[], shareableVariables=[], context=[], term=dict(tag='binary', primitive='multiply', left=dict(tag='nat', value='6'), right=dict(tag='nat', value='7')))
        core = write('core.json', packet)
        for flags in ([], ['--jit'], ['--jit=cc'], ['--emit-c99', root / 'core.c']):
            assert json.loads(run('run-core', core, *flags))['value'] == 42
        assert json.loads(run('run-core', '--jit', core))['value'] == 42
        packet['term'] = dict(tag='record', fields=[])
        fallback = write('fallback.json', packet)
        assert run('run-core', fallback) == run('run-core', fallback, '--jit')
        run('run-core', fallback, '--emit-c99', root / 'unsupported.c', code=2)

        good = {'version': 1, 'slot': 0, 'clauses': [{'name': 'recover', 'priority': 1, 'allowed': 192}]}
        req = write('amend.json', good)
        result = json.loads(run('amend', 'live', req))
        assert len(result['receipts'][0]['receiptHex']) == 64
        bad = copy.deepcopy(good)
        bad['clauses'][0]['allowed'] = 0
        run('amend', 'live', write('amend-bad.json', bad), code=3)
        second = {**good, 'slot': 1, 'prevReceipt': result['receipts'][0]['receiptHex']}
        trace = write('trace.json', {'steps': [good, second]})
        assert json.loads(run('amend', 'trace', trace))['generations'] == 2
        second['prevReceipt'] = '00' * 32
        run('amend', 'trace', write('broken.json', {'steps': [good, second]}), code=3)
        malformed = root / 'malformed.json'
        malformed.write_text('{')
        run('amend', 'live', malformed, code=2)

        key = root / 'root.key'
        key.write_bytes(bytes(range(32)))
        receipt = root / 'receipt.cbor'
        run('amend', 'zk-prove', '--root-secret', key, '--out', receipt, '--epoch', '7', '--nonce', '13')
        run('amend', 'zk-verify', '--root-secret', key, '--in', receipt, '--current-epoch', '7', '--nullifier-log', root / 'nullifiers')
        damaged = bytearray(receipt.read_bytes())
        damaged[len(damaged) // 2] ^= 1
        (root / 'damaged.cbor').write_bytes(damaged)
        p = subprocess.run([str(BIN), 'amend', 'zk-verify', '--root-secret', str(key), '--in', str(root / 'damaged.cbor'), '--current-epoch', '7', '--nullifier-log', str(root / 'nullifiers-bad')], capture_output=True, text=True)
        assert p.returncode != 0, p.stdout
        run('amend', 'zk-tamper-test')

        custody = root / 'custody'
        (custody / 'var').mkdir(parents=True)
        payload = custody / 'var/payload.bin'
        payload.write_bytes(b'custody payload')
        run('custody', 'init', custody)
        run('custody', 'prepare', custody)
        run('custody', 'prepare', custody, code=3)
        run('custody', 'reopen', custody)
        run('custody', 'event', custody, 'crash')
        run('custody', 'prepare', custody, code=3)
        run('custody', 'reopen', custody)
        payload.write_bytes(b'Custody payload')
        run('custody', 'reopen', custody, code=3)

        params = dict(w=4, ell1=8, subtreeHeight=2, numLayers=2, forsTrees=4, forsHeight=2, maxSigsLog2=4, statefulLeanSig=False)
        shares = [dict(skSeed=[i + 1] * 32, skPrf=[i + 4] * 32, pkSeed=[7] * 32) for i in range(3)]
        signing = dict(params=params, message=list(b'message'), shares=shares, threshold=2, leafGlobalIdx=0, optRand=[9] * 32, maxGrind=10000)
        sigfile = root / 'signature.json'
        run('mpc', 'sign', write('sign.json', signing), '--out', sigfile)
        run('mpc', 'verify', sigfile)
        sig = json.loads(sigfile.read_text())
        sig['message'][0] ^= 1
        run('mpc', 'verify', write('forged.json', sig), code=3)
        signing['threshold'] = 3
        run('mpc', 'sign', write('threshold.json', signing), code=3)

        system = dict(vars=['u'], flux=[['var', 'u']], state=[0], left=[0], right=[0], aMax=1, cfl={'num': 1, 'den': 2})
        cert = dict(jac=[[1]], eigVecs=[[1]], eigVals=[1], eigInv=[[1]], weights=[1], sym=[[1]])
        grid = dict(format='hyperbolic-fvm@1', system=system, certificate=cert, initial=[[1], [2], [3]], steps=2)
        solution = root / 'solution.json'
        run('pde', 'solve', write('grid.json', grid), '--out', solution)
        run('pde', 'check', solution)
        solved = json.loads(solution.read_text())
        approx = {**solved, 'format': 'pde-approx-defect@1', 'eta': 1, 'tolerance': 0}
        run('pde', 'check', write('approx.json', approx))
        approx['trajectory'][-1][0][0] = 999
        run('pde', 'check', write('defect.json', approx), code=3)
        grid['system']['cfl'] = 2
        run('pde', 'solve', write('cfl.json', grid), code=3)

        bazaar = bazaar_fixture()
        auction = write('bazaar.json', bazaar)
        run('bazaar', 'clear', auction)
        run('bazaar', 'clear', auction, code=3)
        bad = copy.deepcopy(bazaar)
        bad['kkt']['price'] = 100
        run('bazaar', 'clear', write('kkt-bad.json', bad), code=3)
        bad = copy.deepcopy(bazaar)
        bad['orders'][0]['utility']['submittedTotal'] = 999
        run('bazaar', 'clear', write('utility-bad.json', bad), code=3)

        request = dict(op='init', cells=[dict(cellKey='public', id=1, defs=['x'], literalValue=7), dict(cellKey='secret', id=2, defs=['secret'], literalValue=8675309, visibility={'sealed': '1', 'salt': 12345})])
        state = root / 'notebook.json'
        redacted = root / 'redacted.json'
        run('notebook', 'eval', write('cells.json', request), '--out', state)
        run('notebook', 'project', state, '--viewer', '0', '--out', redacted)
        assert '8675309' not in redacted.read_text()
        salted = root / 'salted.json'
        run('notebook', 'project', state, '--viewer', '0', '--salt', '54321', '--out', salted)
        assert json.loads(salted.read_text())['merkleRootHex'] != json.loads(redacted.read_text())['merkleRootHex']
        assert '8675309' not in salted.read_text()
        run('notebook', 'verify', redacted)
        damaged = json.loads(redacted.read_text())
        damaged['merkleRootHex'] = '00' * 32
        run('notebook', 'verify', write('notebook-root-tampered.json', damaged), code=3)
        damaged = json.loads(redacted.read_text())
        damaged['entries'][0]['commitmentHex'] = '00' * 32
        run('notebook', 'verify', write('notebook-cell-tampered.json', damaged), code=3)
    print(f'{checks} CLI checks passed')


def bazaar_fixture():
    q, smudge = 2**54, 2**40

    def mul(a, b):
        out = [0] * 4
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                out[(i+j) % 4] += x*y * (1 if i+j < 4 else -1)
        return out

    keys = [[1,-1,0,1], [0,1,-1,1], [-1,1,1,0]]
    sk = [sum(xs) for xs in zip(*keys)]
    randoms = [[101,202,303,404], [505,606,707,808], [909,111,222,333], [444,555,666,777]]
    noises = [[2,-1,1,0], [-1,2,0,-1], [1,1,-2,1], [-1,1,1,-2]]
    weights = [[10,4,-2,6], [5,3,2,-1], [7,5,-1,2], [6,4,1,-2]]
    features = [[3,3,1,1], [2,2,1,0], [3,1,2,2], [3,1,2,1]]
    rat = lambda n, d: {'num': n, 'den': d}
    orders = []
    for i, (qty, total) in enumerate([(4,48), (2,18), (3,30), (2,22)]):
        side = 'bid' if i < 2 else 'ask'
        sign = 1 if i < 2 else -1
        plain = [qty*sign, total*sign, 0, 0]
        ct = {'c0': [(-v+(q//256)*m+e) % q for v,m,e in zip(mul(sk,randoms[i]),plain,noises[i])], 'c1': randoms[i]}
        bits = lambda n: [bool((n >> k) & 1) for k in range(n.bit_length())]
        utility = dict(tm=dict(coeffs=[[5,1,-1],[2,1,-1],[rat(14,5),1,1],[2,1,1]][i], center=0, domain=dict(lo=rat(-1,2),hi=rat(1,2)), rem=dict(lo=rat(-1,100),hi=rat(1,100))), feature=[rat(1,5),0,rat(1,10),rat(1,10)][i], tickScale=10, side=side, submittedTotal=total)
        orders.append(dict(account=10+i, side=side, maxBits=8, witness=dict(qtyBits=bits(qty),totalBits=bits(total),salt=dict(c0=i+101,c1=i+201)), utility=utility, sable=dict(weights=weights[i],features=features[i],bias=[2,0,2,0][i]), ciphertext=ct))
    c1 = [sum(xs) % q for xs in zip(*randoms)]
    smudges = [[3,-2,1,0],[-1,4,-3,1],[2,-1,2,-4]]
    shares = [dict(guardianId=i+1,sharePoly=[(v+n*smudge) % q for v,n in zip(mul(key,c1),smudges[i])]) for i,key in enumerate(keys)]
    # Non-pigeonhole block basis from inhabitedAjtaiParams; do not weaken the verifier.
    radix = 262141
    matrix = [[radix**(j%4) if j//4 == i else 0 for j in range(32)] for i in range(8)]
    return dict(config=dict(params=dict(d=4,q=q,t=256),quorum=3,encNoiseBound=8,smudgeBound=8*smudge,secBits=40), sableDim=4, committee=[1,2,3],budget=12,epochNullifier=1001,ajtaiParams=dict(rows=8,cols=32,modulus=radix**4,matrix=matrix),orders=orders,thresholdShares=shares,market=dict(currency=1,goods=2,epsilon=0),transfers=[dict(source=a,destination=b,asset=c,amount=d) for a,b,c,d in [(12,10,2,3),(10,12,1,33),(13,10,2,1),(10,13,1,11)]],kkt=dict(price=11,potentials=[1,0],slacks=[2,2,0,0]))


if __name__ == '__main__':
    main()
