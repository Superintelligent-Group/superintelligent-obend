#!/usr/bin/env bash
# End-to-end verification script for Real-World Numerical Relativity 1+1 Bona-Masso / Z4c App
# (`apps/relativity-z4c/`):
#   1. `obend check/run --package apps/relativity-z4c/package.json` (3-layer `.obend` composition)
#   2. `obend pde solve/check` in both `"rat"` and `"q32"` backends (16-cell 8-step planted-Theta
#      & 16-cell smooth 6-variable Apples-with-Apples gauge wave), byte-identity of emitted
#      WGSL / SystemVerilog / SMT-LIB2 LEC artifacts, strict ||Theta^k||_inf decay, q32VsRatMaxDiff
#      bound (< 1e-6), 256-bit receipt tamper refusal, and CFL-violating S-expr refusal
#   3. Yosys + `hardware/lec/smt_share.py` + Z3 LEC (`unsat`) + planted 1-bit output mutation (`sat`)
#   4. Verilator `-Wall` build & 22-cycle 0-ULP Q32.32 simulation emitting `verilator/wave.vcd`
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
OBEND_BIN="${OBEND_BIN:-${REPO_ROOT}/lean/.lake/build/bin/obend}"
OSS_CAD="${OSS_CAD:-${HOME}/tools/oss-cad-suite}"
YOSYS="${YOSYS_BIN:-$([[ -x "${OSS_CAD}/bin/yosys" ]] && echo "${OSS_CAD}/bin/yosys" || command -v yosys)}"
Z3="${Z3_BIN:-$(command -v z3)}"

pick_verilator() {
  if [[ -n "${VERILATOR_BIN:-}" && -x "${VERILATOR_BIN}" ]]; then
    echo "${VERILATOR_BIN}"; return
  fi
  for cand in /tmp/oss-cad-suite/bin/verilator "${OSS_CAD}/bin/verilator" "$(command -v verilator || true)"; do
    if [[ -n "${cand}" && -x "${cand}" ]] && "${cand}" --version >/dev/null 2>&1; then
      echo "${cand}"; return
    fi
  done
  echo "[FAIL] No working verilator binary found (set VERILATOR_BIN)" >&2
  exit 1
}
VERILATOR="$(pick_verilator)"

for t in "${OBEND_BIN}" "${YOSYS}" "${Z3}" "${VERILATOR}"; do
  [[ -x "${t}" ]] || { echo "[FAIL] Required tool not executable: ${t}" >&2; exit 1; }
done

work="$(mktemp -d "${TMPDIR:-/tmp}/obend-relativity-z4c.XXXXXX")"
trap 'rm -rf "${work}"' EXIT

echo "[1/4] Checking & running 3-layer .obend package (apps/relativity-z4c/package.json)..."
(
  cd "${REPO_ROOT}"
  "${OBEND_BIN}" check --package apps/relativity-z4c/package.json >/dev/null
  RUN_OUT="$("${OBEND_BIN}" run --package apps/relativity-z4c/package.json)"
  echo "${RUN_OUT}"
  grep -q "result: 189" <<< "${RUN_OUT}" || { echo "[FAIL] Expected result: 189" >&2; exit 1; }
)
echo "[OK] 3-layer .obend package checked and evaluated (result = 189)"

echo "[2/4] Verifying obend pde solve/check (rat + q32), artifact byte-identity, Theta decay & refusals..."
mkdir -p "${work}/wgsl"
"${OBEND_BIN}" pde solve "${SCRIPT_DIR}/benchmarks/smooth_gauge_wave_rat_req.json" \
  --out "${work}/smooth_gauge_wave_rat_out.json" \
  --emit-wgsl "${work}/wgsl" \
  --emit-sv "${work}/BonaMassoZ4c1D_axis0.sv" \
  --emit-lec "${work}/BonaMassoZ4c1D_lec.smt2"
"${OBEND_BIN}" pde check "${work}/smooth_gauge_wave_rat_out.json" >/dev/null

"${OBEND_BIN}" pde solve "${SCRIPT_DIR}/benchmarks/smooth_gauge_wave_q32_req.json" \
  --out "${work}/smooth_gauge_wave_q32_out.json"
"${OBEND_BIN}" pde check "${work}/smooth_gauge_wave_q32_out.json" >/dev/null

"${OBEND_BIN}" pde solve "${SCRIPT_DIR}/benchmarks/gauge_wave_theta_rat_req.json" \
  --out "${work}/gauge_wave_theta_rat_out.json"
"${OBEND_BIN}" pde check "${work}/gauge_wave_theta_rat_out.json" >/dev/null

"${OBEND_BIN}" pde solve "${SCRIPT_DIR}/benchmarks/gauge_wave_theta_q32_req.json" \
  --out "${work}/gauge_wave_theta_q32_out.json"
"${OBEND_BIN}" pde check "${work}/gauge_wave_theta_q32_out.json" >/dev/null

# Byte-identity against committed SV, LEC SMT2, and WGSL artifacts
cmp -s "${work}/BonaMassoZ4c1D_axis0.sv" "${SCRIPT_DIR}/verilator/BonaMassoZ4c1D_axis0.sv" \
  || { echo "[FAIL] BonaMassoZ4c1D_axis0.sv differs from obend pde solve --emit-sv" >&2; exit 1; }
cmp -s "${work}/BonaMassoZ4c1D_lec.smt2" "${SCRIPT_DIR}/verilator/BonaMassoZ4c1D_lec.smt2" \
  || { echo "[FAIL] BonaMassoZ4c1D_lec.smt2 differs from obend pde solve --emit-lec" >&2; exit 1; }
for f in plan.json stage_0.wgsl stage_1.wgsl; do
  cmp -s "${work}/wgsl/${f}" "${SCRIPT_DIR}/wgsl/${f}" \
    || { echo "[FAIL] wgsl/${f} differs from obend pde solve --emit-wgsl" >&2; exit 1; }
done
echo "[OK] Emitted SV, LEC SMT-LIB2, and WGSL shaders are byte-identical"

# Verify strict monotonic ||Theta^k||_inf decay, q32VsRatMaxDiff < 1e-6, 64-hex receipt, and refusal gates
python3 - "${work}" "${OBEND_BIN}" "${SCRIPT_DIR}" << 'PY'
import json, subprocess, sys
sys.set_int_max_str_digits(0)
work, obend_bin, script_dir = sys.argv[1], sys.argv[2], sys.argv[3]

for label, fname, expected_steps in [
    ("8-step rat", f"{work}/gauge_wave_theta_rat_out.json", 8),
    ("8-step q32", f"{work}/gauge_wave_theta_q32_out.json", 8),
    ("smooth 3-step rat", f"{work}/smooth_gauge_wave_rat_out.json", 3),
    ("smooth 3-step q32", f"{work}/smooth_gauge_wave_q32_out.json", 3),
]:
    d = json.load(open(fname))
    assert d["ok"] is True and d["status"] == "accepted", f"{label} not accepted"
    rh = d["receiptHex"]
    assert len(rh) == 64 and all(c in "0123456789abcdef" for c in rh), f"{label} invalid receiptHex"
    diff = d["q32VsRatMaxDiff"]
    dv = diff["num"] / diff["den"]
    assert dv < 1e-6, f"{label} q32VsRatMaxDiff={dv} >= 1e-6"
    traj = d["trajectory"]
    assert len(traj) == expected_steps + 1, f"{label} wrong trajectory len"
    norms = [max(abs(row[5]["num"] / row[5]["den"]) for row in grid) for grid in traj]
    assert all(norms[k + 1] < norms[k] for k in range(len(norms) - 1)), f"{label} Theta not strictly damped: {norms}"
    print(f"  [OK] {label}: receipt={rh[:16]}... q32VsRatMaxDiff={dv:.3e} ||Theta||_inf={[round(x, 6) for x in norms]}")

# Refusal 1: tampered 256-bit receiptHex must fail at stage "receipt" with exit code 3
tampered = json.load(open(f"{work}/smooth_gauge_wave_rat_out.json"))
tampered["receiptHex"] = ("0" if tampered["receiptHex"][0] != "0" else "1") + tampered["receiptHex"][1:]
tampered_path = f"{work}/tampered_receipt.json"
json.dump(tampered, open(tampered_path, "w"))
r = subprocess.run([obend_bin, "pde", "check", tampered_path], capture_output=True, text=True)
assert r.returncode == 3, f"expected rc=3 for tampered receipt, got {r.returncode}"
resp = json.loads(r.stdout)
assert resp["status"] == "refused" and resp["stage"] == "receipt", f"unexpected tamper response: {resp}"
print("  [OK] Tampered 256-bit receiptHex refused at stage='receipt' (rc=3)")

# Refusal 2: CFL-violating Z4c S-expr must fail at stage "validate-pde-sexpr" with exit code 1
bad_cfl = {
    "format": "nonlinear-conservation@1",
    "sexpr": (
        "(conservation-law (name BadZ4cCfl) (coords x) (vars alpha gxx Ax Dx Kxx Theta) "
        "(params (fBM 2) (beta 1/5) (kappa1 1/2)) (domain (> alpha 0) (> gxx 0)) "
        "(fluxes (x (let ((trK (/ Kxx gxx)) (kHat (- trK (* 2 Theta)))) "
        "(- (* beta alpha)) (- (* beta gxx)) (+ (- (* beta Ax)) (* fBM (* alpha kHat))) "
        "(+ (- (* beta Dx)) (* alpha trK)) (+ (- (* beta Kxx)) (* alpha Ax)) (- (* beta Theta))))) "
        "(sources (- (* (sq alpha) fBM (- (/ Kxx gxx) (* 2 Theta)))) (- (* 2 alpha Kxx)) 0 0 "
        "(- (* alpha (- (* Ax Dx) (/ (sq Kxx) gxx))) (* kappa1 (* alpha Theta))) "
        "(- (* kappa1 (* alpha Theta)))) (max-wavespeed 9) (cfl 1/2) (limiter minmod))"
    ),
    "dims": [16],
    "steps": 1,
    "initial": json.load(open(f"{script_dir}/benchmarks/smooth_gauge_wave_rat_req.json"))["initial"],
}
bad_cfl_path = f"{work}/bad_cfl.json"
json.dump(bad_cfl, open(bad_cfl_path, "w"))
r2 = subprocess.run([obend_bin, "pde", "solve", bad_cfl_path], capture_output=True, text=True)
assert r2.returncode == 1, f"expected rc=1 for CFL-violating S-expr, got {r2.returncode}"
resp2 = json.loads(r2.stdout)
assert resp2["status"] == "refused" and resp2["stage"] == "validate-pde-sexpr", f"unexpected CFL response: {resp2}"
print("  [OK] CFL-violating Z4c S-expr refused at stage='validate-pde-sexpr' (rc=1)")
PY

echo "[3/4] Running Yosys + smt_share.py + Z3 LEC (unsat) & planted 1-bit mutation (sat)..."
sv="${SCRIPT_DIR}/verilator/BonaMassoZ4c1D_axis0.sv"
lec="${SCRIPT_DIR}/verilator/BonaMassoZ4c1D_lec.smt2"
top="BonaMassoZ4c1D_flux_axis0"

"${YOSYS}" -q -p "read_verilog -sv ${sv}; hierarchy -check -top ${top}; proc; flatten; setattr -set keep 1 t:\$dff %co w:* %i; opt_clean; write_smt2 ${work}/${top}.yosys.smt2"
sed '/^; --- counterexample/,$d' "${lec}" > "${work}/lean.smt2"
perl -pe 's/^(\(define-fun \S+ \(\(state \S+\)\) \(_ BitVec (\d+)\) )\(bvmul /$1(|lec_mul_$2| /' "${work}/${top}.yosys.smt2" > "${work}/abs.yosys.smt2"
perl -pe 's/\(bvmul \(\(_ sign_extend 64\)/(|lec_mul_128| ((_ sign_extend 64)/g; s/\(bvmul /(|lec_mul_64| /g' "${work}/lean.smt2" > "${work}/abs.lean.smt2"
{
  grep -ohE 'lec_mul_[0-9]+' "${work}/abs.yosys.smt2" "${work}/abs.lean.smt2" | sort -u \
    | sed -E 's/lec_mul_([0-9]+)/(declare-fun |&| ((_ BitVec \1) (_ BitVec \1)) (_ BitVec \1))/'
  cat "${work}/abs.yosys.smt2" "${work}/abs.lean.smt2"
} > "${work}/abs.combined.smt2"
python3 "${REPO_ROOT}/hardware/lec/smt_share.py" "${work}/abs.combined.smt2" "${work}/abs.shared.smt2" --yosys "${YOSYS}" >/dev/null
lec_verdict="$("${Z3}" -T:60 -in < "${work}/abs.shared.smt2" | head -1)"
if [[ "${lec_verdict}" != "unsat" ]]; then
  echo "[FAIL] LEC ${top}: expected unsat, got ${lec_verdict}" >&2
  exit 1
fi
echo "  [OK] LEC ${top}: unsat (Yosys reading == Lean RtlModule model)"

awk '!done && /^    [A-Za-z_][A-Za-z0-9_]* = .*;$/ && !/^    w_[0-9]+ = / { sub(/ = /, " = 64'\''d1 ^ ("); sub(/;$/, ");"); done = 1 } { print }' "${sv}" > "${work}/${top}.mut.sv"
"${YOSYS}" -q -p "read_verilog -sv ${work}/${top}.mut.sv; hierarchy -check -top ${top}; proc; flatten; setattr -set keep 1 t:\$dff %co w:* %i; opt_clean; write_smt2 ${work}/${top}.mut.yosys.smt2"
awk '
  /^\(define-fun (in|r)_[0-9]+ \(\) \(_ BitVec 64\) / { names[++n] = $2 }
  /^\(declare-const r_[0-9]+ \(_ BitVec 64\)\)$/ { names[++n] = $2 }
  /^\(check-sat\)$/ {
    for (i = 1; i <= n; i++) printf "(assert (= %s (_ bv0 64)))\n", names[i]
  }
  { print }
' "${work}/lean.smt2" > "${work}/seed.lean.smt2"
cat "${work}/${top}.mut.yosys.smt2" "${work}/seed.lean.smt2" > "${work}/mut.raw.smt2"
python3 "${REPO_ROOT}/hardware/lec/smt_share.py" "${work}/mut.raw.smt2" "${work}/mut.shared.smt2" --yosys "${YOSYS}" >/dev/null
mut_verdict="$("${Z3}" -T:10 -in < "${work}/mut.shared.smt2" | head -1)"
if [[ "${mut_verdict}" != "sat" ]]; then
  echo "[FAIL] LEC mutation ${top}: expected sat, got ${mut_verdict}" >&2
  exit 1
fi
echo "  [OK] Planted 1-bit output mutation caught: sat"

echo "[4/4] Building & simulating BonaMassoZ4c1D_axis0.sv with Verilator (-Wall) -> wave.vcd..."
(
  cd "${SCRIPT_DIR}/verilator"
  rm -rf obj_dir wave.vcd
  "${VERILATOR}" --cc --exe --build -j 0 \
    --trace -Wall -Wno-DECLFILENAME -Wno-UNUSED \
    --top-module BonaMassoZ4c1D_flux_axis0 \
    --prefix VBonaMassoZ4c1D_axis0 \
    BonaMassoZ4c1D_axis0.sv relativity_z4c_tb.cpp \
    -o VBonaMassoZ4c1D_axis0
  ./obj_dir/VBonaMassoZ4c1D_axis0
  test -s wave.vcd
  rm -rf obj_dir
)

echo "[PASS] Real-World Numerical Relativity Z4c App (apps/relativity-z4c) fully verified!"
