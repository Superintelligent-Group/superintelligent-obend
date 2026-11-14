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
        truncated = root / 'truncated.json'
        truncated.write_text(req.read_text()[:-9])
        empty = write('empty.json', {})
        # Decode failures are exit 2 and say "refused"; none is an uncaught panic.
        for cmd, sub in (('amend', 'live'), ('amend', 'trace'), ('mpc', 'sign'), ('mpc', 'verify'), ('pde', 'check'),
                         ('pde', 'solve'), ('bazaar', 'clear'), ('notebook', 'eval'), ('notebook', 'project'), ('notebook', 'verify')):
            for broken in (malformed, truncated, root / 'missing.json'):
                run(cmd, sub, broken, code=2)
            if cmd != 'notebook' or sub == 'verify':
                run(cmd, sub, empty, code=2)
            run(cmd, 'no-such-subcommand', req, code=2)
        run('amend', 'live', req, '--no-such-flag', code=2)
        run('amend', 'live', req, '--out', code=2)
        for flags in (['--emit-c99'], ['--jit=no-such-mode']):
            run('run', source, 'main', *flags, code=2)
            run('run-core', core, *flags, code=2)

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
        run('custody', 'prepare', custody, code=2)
        run('custody', 'init', custody)
        run('custody', 'init', custody, code=3)
        run('custody', 'prepare', custody, '--next-epoch', '2', code=3)
        run('custody', 'prepare', custody, '--next-epoch', '1')
        run('custody', 'prepare', custody, code=3)
        run('custody', 'reopen', custody)
        run('custody', 'event', custody, 'crash')
        run('custody', 'prepare', custody, code=3)
        run('custody', 'reopen', custody)
        for bad in (['prepare', custody, '--no-such-flag', '1'], ['prepare', custody, '--next-epoch'],
                    ['event', custody, 'no-such-event'], ['no-such-subcommand', custody], ['init']):
            run('custody', *bad, code=2)
        payload.write_bytes(b'Custody payload')
        run('custody', 'reopen', custody, code=3)
        payload.write_bytes(b'custody payload')
        run('custody', 'reopen', custody)
        # A damaged durable signature is refused, alone and behind a pending WAL.
        durable = custody / 'durable.json'
        for pending in (False, True):
            if pending:
                run('custody', 'prepare', custody)
            sealed = durable.read_text()
            forged = json.loads(sealed)
            forged['transitionSignature'][len(forged['transitionSignature']) // 2] ^= 1
            durable.write_text(json.dumps(forged))
            run('custody', 'reopen', custody, code=3)
            durable.write_text(sealed)
            run('custody', 'reopen', custody)

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
        run('bazaar', 'clear', auction, '--no-such-flag', code=2)
        # The Rust authority receipt is issued only after every Lean stage accepts.
        organ_receipt = root / 'bazaar-receipt.cbor'
        run('bazaar', 'clear', write('kkt-bad-zk.json', bad), '--zk-receipt', organ_receipt, '--root-secret', key, code=3)
        assert not organ_receipt.exists()
        attested = write('bazaar-zk.json', bazaar)
        run('bazaar', 'clear', attested, '--zk-receipt', organ_receipt, code=2)
        assert not organ_receipt.exists() and not Path(str(attested) + '.state.json').exists()
        cleared = root / 'cleared.json'
        run('bazaar', 'clear', attested, '--zk-receipt', organ_receipt, '--root-secret', key, '--out', cleared)
        cleared = json.loads(cleared.read_text())
        assert cleared['zkAuthorityReceipt'] == str(organ_receipt)
        assert cleared['zkReceiptStatement'] == 'organ-authority-envelope(dark_bazaar)'
        verify = ['amend', 'zk-verify', '--root-secret', key, '--current-epoch', cleared['epoch']]
        damaged = bytearray(organ_receipt.read_bytes())
        damaged[len(damaged) // 2] ^= 1
        (root / 'bazaar-damaged.cbor').write_bytes(damaged)
        # Refused: flipped bytes, and the same receipt presented to another organ's verifier.
        for n, extra in enumerate((['--target-organ', 'dark_bazaar', '--in', root / 'bazaar-damaged.cbor'], ['--in', organ_receipt])):
            p = subprocess.run([str(BIN), *map(str, verify + extra + ['--nullifier-log', root / f'bazaar-nullifiers-{n}'])], capture_output=True, text=True)
            assert p.returncode != 0, (extra, p.stdout, p.stderr)
        run(*verify, '--target-organ', 'dark_bazaar', '--in', organ_receipt, '--nullifier-log', root / 'bazaar-nullifiers')
        run('bazaar', 'clear', attested, '--zk-receipt', root / 'replayed.cbor', '--root-secret', key, code=3)
        assert not (root / 'replayed.cbor').exists()

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
        exported = json.loads(redacted.read_text())
        assert exported['schema'] == 'obend.cli.workbook_redacted.v1'
        shown, hidden = exported['entries']
        assert shown['mode'] == 'visible' and shown['cached']['values'][0] == 7
        assert set(hidden) == {'mode', 'cellId', 'cellKey', 'kind', 'exportedDefs', 'commitmentHex', 'opening'}
        assert hidden['mode'] == 'redacted' and 'secret' in hidden['exportedDefs']
        for entry in exported['entries']:
            assert len(entry['commitmentHex']) == 64 and entry['opening']['valueHex'] == entry['commitmentHex']
        run('notebook', 'verify', redacted)
        run('notebook', 'verify', salted)
        cleared_view = root / 'cleared-view.json'
        run('notebook', 'project', state, '--viewer', '1', '--out', cleared_view)
        assert [e['mode'] for e in json.loads(cleared_view.read_text())['entries']] == ['visible', 'visible']
        assert '8675309' in cleared_view.read_text()
        assert json.loads(run('notebook', 'verify', cleared_view))['status'] == 'accepted'

        def tampered(name, change, code=3, base=redacted):
            damaged = json.loads(base.read_text())
            change(damaged)
            run('notebook', 'verify', write(name, damaged), code=code)

        def set_path(path, value):
            def change(doc):
                for key in path[:-1]:
                    doc = doc[key]
                doc[path[-1]] = value
            return change

        flipped = lambda h: ('1' if h[0] == '0' else '0') + h[1:]
        tampered('notebook-root.json', set_path(['merkleRootHex'], '00' * 32))
        tampered('notebook-visible-commitment.json', set_path(['entries', 0, 'commitmentHex'], '00' * 32))
        tampered('notebook-redacted-commitment.json', set_path(['entries', 1, 'commitmentHex'], '00' * 32))
        tampered('notebook-visible-values.json', set_path(['entries', 0, 'cached', 'values', 0], 8))
        tampered('notebook-visible-body.json', set_path(['entries', 0, 'cached', 'reactive', 'body', 0, 0, 'arg'], 8))
        tampered('notebook-opening-path.json', set_path(['entries', 1, 'opening', 'pathHex', 0], flipped(hidden['opening']['pathHex'][0])))
        tampered('notebook-opening-index.json', set_path(['entries', 1, 'opening', 'index'], 0))
        tampered('notebook-truncated-entries.json', lambda doc: doc['entries'].pop())
        tampered('notebook-no-entries.json', set_path(['entries'], []))
        tampered('notebook-sealed-value.json', set_path(['entries', 1, 'cached', 'values', 0], 1), base=cleared_view)
        tampered('notebook-sealed-salt.json', set_path(['entries', 1, 'cached', 'visibility', 'saltHex'], '00' * 32), base=cleared_view)
        # Malformed exports are decode refusals (2), not verification refusals (3).
        tampered('notebook-schema.json', set_path(['schema'], 'obend.ffi.workbook_redacted.v1'), code=2)
        tampered('notebook-short-hex.json', set_path(['entries', 0, 'commitmentHex'], 'abcd'), code=2)
        tampered('notebook-bad-hex.json', set_path(['merkleRootHex'], 'zz' * 32), code=2)
        tampered('notebook-mode.json', set_path(['entries', 1, 'mode'], 'hidden'), code=2)
        tampered('notebook-no-opening.json', lambda doc: doc['entries'][1].pop('opening'), code=2)
        run('notebook', 'verify', redacted, '--no-such-flag', code=2)
        run('notebook', 'project', state, code=2)
        run('notebook', 'project', state, '--viewer', 'everyone', code=2)
        run('notebook', 'project', state, '--viewer', '0', '--salt', 'pepper', code=2)
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
