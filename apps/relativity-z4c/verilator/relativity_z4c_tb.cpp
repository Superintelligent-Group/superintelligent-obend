// Objective Bend Real-World Numerical Relativity App (`apps/relativity-z4c/verilator/relativity_z4c_tb.cpp`)
// Verilator C++ testbench for the Lean-emitted `BonaMassoZ4c1D_flux_axis0` systolic Q32.32 flux unit.
//
// Drives all 16 periodic Apples-with-Apples 1+1 Gauge-Wave + Planted-Theta cells through
// `VBonaMassoZ4c1D_axis0` (plus synchronous reset and pipeline flush, 22 clock cycles total),
// verifies 0-ULP bit-exact equality on `flux_out_0..flux_out_5` against the exact Q32.32
// Newton-Raphson reference model, and emits `wave.vcd`.

#include "VBonaMassoZ4c1D_axis0.h"
#include "verilated.h"
#include "verilated_vcd_c.h"

#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>

namespace {

constexpr uint64_t Q32_ONE = 1ULL << 32;
constexpr uint64_t BETA_Q32 = 858993459ULL;   // floor(1/5 * 2^32)
constexpr uint64_t FBM_Q32  = 8589934592ULL;  // 2 * 2^32

inline uint64_t qmul32(uint64_t a, uint64_t b) {
    __int128 sa = static_cast<__int128>(static_cast<int64_t>(a));
    __int128 sb = static_cast<__int128>(static_cast<int64_t>(b));
    return static_cast<uint64_t>(static_cast<int64_t>((sa * sb) >> 32));
}

// Exact bit-for-bit Q32.32 Newton-Raphson reciprocal matching `BonaMassoZ4c1D_axis0.sv` (`w_12..w_40`).
inline uint64_t q32_inv_nr(uint64_t x) {
    const bool neg = static_cast<int64_t>(x) < 0;
    uint64_t mag = neg ? (0ULL - x) : x;
    uint64_t shift = 0;

    if (mag < 2147483648ULL)         { mag <<= 32; shift += 32; }
    if (mag < 140737488355328ULL)    { mag <<= 16; shift += 16; }
    if (mag < 36028797018963968ULL)  { mag <<= 8;  shift += 8;  }
    if (mag < 576460752303423488ULL) { mag <<= 4;  shift += 4;  }
    if (mag < 2305843009213693952ULL){ mag <<= 2;  shift += 2;  }
    if (mag < 4611686018427387904ULL){ mag <<= 1;  shift += 1;  }

    const uint64_t m = (mag + 1073741824ULL) >> 31;
    uint64_t y = 12126966482ULL - qmul32(8084644321ULL, m);
    for (int iter = 0; iter < 4; ++iter) {
        y = qmul32(y, 8589934592ULL - qmul32(m, y));
    }
    const uint64_t scaled = (shift < 31ULL)
        ? (y >> ((31ULL - shift) & 63ULL))
        : (y << ((shift - 31ULL) & 63ULL));
    return neg ? (0ULL - scaled) : scaled;
}

inline uint64_t rat_to_q32(int64_t num, int64_t den) {
    // Exact for power-of-2 denominators dividing 2^32.
    __int128 scaled = (static_cast<__int128>(num) << 32) / static_cast<__int128>(den);
    return static_cast<uint64_t>(static_cast<int64_t>(scaled));
}

struct StateQ32 {
    uint64_t alpha, gxx, Ax, Dx, Kxx, Theta;
};

struct FluxQ32 {
    uint64_t f0, f1, f2, f3, f4, f5;
};

FluxQ32 ref_flux_axis0(const StateQ32& s) {
    const uint64_t f0 = 0ULL - qmul32(BETA_Q32, s.alpha);
    const uint64_t f1 = 0ULL - qmul32(BETA_Q32, s.gxx);
    const uint64_t inv_gxx = q32_inv_nr(s.gxx);
    const uint64_t trK = qmul32(s.Kxx, inv_gxx);
    const uint64_t two_theta = qmul32(FBM_Q32, s.Theta);
    const uint64_t kHat = trK - two_theta;
    const uint64_t f2 = (0ULL - qmul32(BETA_Q32, s.Ax)) + qmul32(FBM_Q32, qmul32(s.alpha, kHat));
    const uint64_t f3 = (0ULL - qmul32(BETA_Q32, s.Dx)) + qmul32(s.alpha, trK);
    const uint64_t f4 = (0ULL - qmul32(BETA_Q32, s.Kxx)) + qmul32(s.alpha, s.Ax);
    const uint64_t f5 = 0ULL - qmul32(BETA_Q32, s.Theta);
    return {f0, f1, f2, f3, f4, f5};
}

} // namespace

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    Verilated::traceEverOn(true);

    VBonaMassoZ4c1D_axis0* dut = new VBonaMassoZ4c1D_axis0;
    VerilatedVcdC* tfp = new VerilatedVcdC;
    dut->trace(tfp, 99);
    tfp->open("wave.vcd");

    vluint64_t sim_time = 0;
    auto tick = [&]() {
        dut->clk = 0;
        dut->eval();
        tfp->dump(sim_time++);
        dut->clk = 1;
        dut->eval();
        tfp->dump(sim_time++);
    };

    // 16-cell periodic Apples-with-Apples 1+1 Gauge-Wave + Planted-Theta initial slice
    // Exact dyadic rationals (0 initial Q32 quantization error) inside BonaMassoZ4c1D state-box.
    constexpr std::array<int64_t, 16> s_wave = {
        0, 12, 23, 30, 32, 30, 23, 12, 0, -12, -23, -30, -32, -30, -23, -12
    };
    std::array<StateQ32, 16> cells{};
    for (size_t i = 0; i < 16; ++i) {
        const int64_t si = s_wave[i];
        const int64_t ci = s_wave[(i + 4) % 16];
        cells[i] = {
            rat_to_q32(320 + si, 256), // alpha in [9/8, 11/8]
            rat_to_q32(192 + si, 128), // gxx   in [5/4, 7/4]
            rat_to_q32(ci, 256),       // Ax    in [-1/8, 1/8]
            rat_to_q32(ci, 256),       // Dx    in [-1/8, 1/8]
            rat_to_q32(ci, 512),       // Kxx   in [-1/16, 1/16]
            rat_to_q32(ci, 256)        // Theta in [-1/8, 1/8]
        };
    }

    // 1. Synchronous active-high reset (2 cycles)
    dut->rst = 1;
    dut->alpha = Q32_ONE;
    dut->gxx = Q32_ONE;
    dut->Ax = 0;
    dut->Dx = 0;
    dut->Kxx = 0;
    dut->Theta = 0;
    for (int r = 0; r < 2; ++r) {
        tick();
        assert(dut->flux_out_0 == 0ULL);
        assert(dut->flux_out_1 == 0ULL);
        assert(dut->flux_out_2 == 0ULL);
        assert(dut->flux_out_3 == 0ULL);
        assert(dut->flux_out_4 == 0ULL);
        assert(dut->flux_out_5 == 0ULL);
    }
    dut->rst = 0;

    // 2. Drive all 16 gauge-wave cells (1-cycle registered systolic flux pipeline)
    uint32_t checked_cells = 0;
    for (size_t i = 0; i < 16; ++i) {
        const StateQ32& st = cells[i];
        dut->alpha = st.alpha;
        dut->gxx   = st.gxx;
        dut->Ax    = st.Ax;
        dut->Dx    = st.Dx;
        dut->Kxx   = st.Kxx;
        dut->Theta = st.Theta;
        tick();

        const FluxQ32 exp = ref_flux_axis0(st);
        if (dut->flux_out_0 != exp.f0 || dut->flux_out_1 != exp.f1 ||
            dut->flux_out_2 != exp.f2 || dut->flux_out_3 != exp.f3 ||
            dut->flux_out_4 != exp.f4 || dut->flux_out_5 != exp.f5) {
            std::cerr << "[FAIL] Cell " << i << " flux mismatch!" << std::endl;
            std::cerr << "  got: " << dut->flux_out_0 << ", " << dut->flux_out_1 << ", "
                      << dut->flux_out_2 << ", " << dut->flux_out_3 << ", "
                      << dut->flux_out_4 << ", " << dut->flux_out_5 << std::endl;
            std::cerr << "  exp: " << exp.f0 << ", " << exp.f1 << ", "
                      << exp.f2 << ", " << exp.f3 << ", "
                      << exp.f4 << ", " << exp.f5 << std::endl;
            return 1;
        }
        ++checked_cells;
    }

    // 3. Pipeline flush & Minkowski stationary-gauge check (4 cycles, total 22 cycles)
    const std::array<StateQ32, 4> flush_states = {{
        { rat_to_q32(1, 1), rat_to_q32(2, 1), 0ULL, 0ULL, 0ULL, rat_to_q32(1, 16) },
        { rat_to_q32(1, 1), rat_to_q32(2, 1), 0ULL, 0ULL, 0ULL, rat_to_q32(-1, 16) },
        { rat_to_q32(3, 2), rat_to_q32(2, 1), rat_to_q32(1, 4), rat_to_q32(-1, 4), rat_to_q32(1, 8), 0ULL },
        { rat_to_q32(1, 1), rat_to_q32(1, 1), 0ULL, 0ULL, 0ULL, 0ULL }
    }};
    for (size_t k = 0; k < flush_states.size(); ++k) {
        const StateQ32& st = flush_states[k];
        dut->alpha = st.alpha;
        dut->gxx   = st.gxx;
        dut->Ax    = st.Ax;
        dut->Dx    = st.Dx;
        dut->Kxx   = st.Kxx;
        dut->Theta = st.Theta;
        tick();
        const FluxQ32 exp = ref_flux_axis0(st);
        assert(dut->flux_out_0 == exp.f0);
        assert(dut->flux_out_1 == exp.f1);
        assert(dut->flux_out_2 == exp.f2);
        assert(dut->flux_out_3 == exp.f3);
        assert(dut->flux_out_4 == exp.f4);
        assert(dut->flux_out_5 == exp.f5);
        ++checked_cells;
    }

    tfp->close();
    delete tfp;
    delete dut;

    std::cout << "[PASS] VBonaMassoZ4c1D_axis0: 0-ULP bit-exact across "
              << checked_cells << " cells (16 gauge-wave + 4 flush, "
              << (sim_time / 2) << " clock cycles), wrote wave.vcd" << std::endl;
    return 0;
}
