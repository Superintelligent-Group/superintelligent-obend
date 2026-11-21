# Continuum Physics, Relativistic PDE Compilation, Open-Hypergraph Symmetry, and Silicon Verification

This document summarizes the mathematical specifications, machine-checked theorems, and hardware/GPU artifacts in `Obend` covering hyperbolic balance laws and 1+1 ADM/Z4c numerical relativity (`#pde_solver`), discrete exterior calculus and Dirac open systems, open-hypergraph symmetry quotients and adjoint equality saturation, and bit-exact GPU/RTL lowering.

---

## 1. Single-Object Metaprogrammed Hyperbolic Balance-Law & Z4c Relativity Compiler

`#pde_solver` (`lean/Obend/Elab/PdeSolverElab.lean`) parses a declarative system $\partial_t U + \sum_d \partial_d F_d(U) = S(U)$ — spatial coordinates, conserved state variables, exact rational parameters, positivity domain, directional flux expressions, algebraic source terms, declared state box, scaling weights, wavespeed bound $a_{\max}$, Courant number $\nu$, and slope limiter — and elaborates a single `ConservationLawSpec` (`lean/Obend/Analysis/NonlinearMultiDPde.lean`) together with its continuum, numerical, fixed-point, GPU, and RTL theorems checked by the Lean 4 kernel at declaration time (`checkPdeSolverSpec_sound`, `validatePdeSolverSexpr_refuses_invalid`, `checkPdeSolverSpec_refuses_cfl_violation`).

### 1.1 Six-Rung Vertical Certificate on One `ConservationLawSpec` (`EndToEndPdeCert`)

For each accepted specification `S : ConservationLawSpec`, `#pde_solver` synthesizes `<Name>.endToEnd_certified : EndToEndPdeCert <Name>.spec` via `buildEndToEndPdeCert` (`lean/Obend/Hardware/MultiDStencilCorrect.lean`), uniting six proved rungs over the same object `S`:

1. **Continuum Symbolic Fréchet Differentiation, Derived Gershgorin Spectral Radius & Constructive Lipschitz Bound (`lean/Obend/Analysis/NonlinearMultiDPde.lean`, `lean/Obend/Analysis/HyperbolicBalanceLaws.lean`, `lean/Obend/Analysis/NonlinearErrorTube.lean`)**:
   - `symJacobian_frechet_taylor`: for every directional flux entry whose denominators are certified nonzero on the declared domain (`DomainValid`, `checkExprDomainSafe`), exact multivariable symbolic differentiation over $\mathbb{Q}$ satisfies $F_d(U + hV) - F_d(U) = h\,J_d(U)V + h^2 R_d(U, V, h)$ with explicit rational remainder `symDirectionalRem` and zero floating-point truncation.
   - `verifyWavespeedGershgorin_sound`: interval enclosure of every symbolic Jacobian entry over `effectiveStateBox S` and scaled Gershgorin row-sum verification (`verifyWavespeedGershgorin`) bound both the weighted $\ell_\infty$ operator norm $\|J_d(U)\|_{w,\infty} \le a_{\max}$ and every rational eigenvalue $|\lambda| \le a_{\max}$ across the state box.
   - `evalFluxLip_sound` and `verifyFluxLipschitz_sound`: constructive interval-derivative propagation (`verifyFluxLipschitz`) derives `FluxLipOn S d (effectiveStateBox S)` with zero external Lipschitz axioms.

2. **Conservative Rational MUSCL/Rusanov Schemes, Hydrostatic Balance & Z4c Constraint Damping (`lean/Obend/Analysis/NonlinearMultiDPde.lean`, `lean/Obend/Tactic/SymDiffAndFlux.lean`, `lean/Obend/Analysis/HyperbolicBalanceLaws.lean`, `lean/Obend/Analysis/NonlinearPdeCli.lean`)**:
   - `fluctuationConservation_of_reflective` and `symmetrizerReflective_sound`: clearing denominators into canonical multivariate polynomials (`checkFluxEqReflective_sound`) proves exact two-state Rusanov fluctuation conservation $A^-\Delta Q + A^+\Delta Q = F_d(U_R) - F_d(U_L)$ and Friedrichs symmetry of $H(U)J_d(U)$.
   - `tvd_rusanov_minmod_step_nonincreasing` and `tadmor_rusanov_entropy_dissipative`: second-order MUSCL reconstruction with `minmod` slope limiting is total-variation diminishing under $2\nu a_{\max} \le 1$, and Tadmor entropy-conservative fluxes with Rusanov dissipation satisfy the discrete entropy inequality on periodic grids.
   - `evalSchemeStepRat_conserves_sourceless_component`, `rolloutRat_periodic_conserves_integral`, and `rolloutRat_reflective_conserves_component`: multi-dimensional Lie and Strang operator-split steps (`evalSchemeStepRat`) conserve exact discrete integrals on sourceless components across periodic grids and parity-reflected impermeable walls.
   - `z4c_theta_constraint_strict_damped`, `dedner_glm_psi_energy_damped`, and `audusseBouchut_lakeAtRest_wellBalanced`: strict per-step contraction $|\Theta^{n+1}| < |\Theta^n|$ of the Z4c constraint-damping variable under $0 < \Delta t\,\kappa_1 \alpha < 2$, quadratic energy decay of the Dedner GLM divergence-cleaning scalar $\psi$, and exact lake-at-rest preservation $h + b = \text{const},\, q = 0$ under Audusse–Bouchut hydrostatic reconstruction.

3. **Signed Q32.32 Guard-Bit Overflow Freedom, LUT-Free Systolic Reciprocal & Quantitative Step Defect (`lean/Obend/Hardware/MultiDStencilTile.lean`, `lean/Obend/Analysis/NonlinearErrorTube.lean`)**:
   - `specializeFluxSweep_sound` and `compileFluxSsaDag_sound`: Futamura parameter specialization and common-subexpression elimination lower `S` to `FluxSsaDag` without increasing operation count.
   - `evalQ32Reciprocal_residual_bound`: a table-free 4-step Newton–Raphson reciprocal (`evalQ32Reciprocal`, seeded with $48/17 - (32/17)d$ after shift normalization) satisfies $|r \cdot d - 2^{64}| \le 6 \cdot 2^{32} + |d|$ across every 64-bit signed word with $16 \le |d| \le 2^{60}$, with zero signed wrap at any intermediate node.
   - `inferSsaDagQ32Intervals_encloses_eval`, `propagateSsaInterval_encloses`, and `checkPdeQ32Intervals_sound`: every evaluated Q32.32 wire stays strictly inside the guard-bit range $(-2^{62}, 2^{62})$ and equals its unbounded-integer meaning (`propagateSsaInterval_refuses_zero_crossing`, `ratToQ32Checked_refuses_overflow`).
   - `stepQ32Axis_rat_defect_bound`: `computeStepQ32ErrorBound` computes a concrete rational bound $\varepsilon_{\text{step}}$ on $|{\text{decodeQ32}}(\text{evalNonlinearFluxCellQ32}) - \text{evalAxisCellRat}|$ across every five-point stencil in the declared Q32 state box.

4. **Multi-Step Nonlinear Error Tubes (`lean/Obend/Analysis/NonlinearErrorTube.lean`)**:
   - `nonlinear_aposteriori_error_tube`: discrete Gronwall / Lady Windermere error-tube recursion $e_{k+1} \le L_{\text{scheme}} e_k + \delta_k$ bounding the distance between any untrusted floating-point or ML surrogate trajectory and the exact rational `evalSchemeStepRat` rollout.
   - `q32_trajectory_error_tube_derived` and `q32_scheme_trajectory_error_tube`: unconditional *a priori* multi-step error tubes between decoded Q32.32 rollouts (both single-axis sweeps and multi-dimensional Lie/Strang + inhomogeneous source rollouts) and exact rational trajectories, using the derived `verifyFluxLipschitz` and `computeSourceLip` bounds.

5. **Bit-Exact GPU Kernel Lowering & Multi-D Brick Halo Tiling (`lean/Obend/Hardware/MultiDStencilGpuSource.lean`, `lean/Obend/Hardware/MultiDStencilCorrect.lean`, `lean/Obend/Hardware/MultiDStencilTile.lean`)**:
   - `scalarQmul32_eval_eq_qmul32`: the four 32-bit-limb WGSL product equals signed floor Q32.32 multiplication modulo $2^{64}$ on every word pair.
   - `spec_fusedGpuKernel_eq_stepQ32Axis` and `spec_fusedGpuKernel_preserves_constant_state`: the lowered GPU kernel (`compileMultiDNonlinearFluxSweepSource` / `buildSpecFusedGpuKernel`) evaluates bit-for-bit identically to `stepQ32Axis` on every grid, dimension, and boundary policy, and preserves discrete steady states bit-exactly.
   - `multiDBrickTiled_eq_global_sweep` and `multiDBrickHbmReads_lt_global`: multi-dimensional shared-memory halo brick tiling (including non-multiple tail bricks and radius-2 MUSCL stencils) equals the global sweep while strictly reducing off-chip HBM reads.

6. **Universal Systolic RTL Refinement & Yosys SMT-LIB2 Logic Equivalence (`lean/Obend/Hardware/MultiDStencilCorrect.lean`, `lean/Obend/Hardware/YosysLec.lean`, `lean/Obend/Hardware/HDL.lean`)**:
   - `spec_systolicRtl_refines_q32` and `spec_systolicRtl_yosysLec_faithful`: the emitted pipelined systolic `RtlModule` (`buildSpecSystolicRtl`, inlining the 29-wire combinational `reciprocalRtlExprs`) passes `checkRtlModule`, satisfies `moduleFaithful` for SMT-LIB2 miter generation (`emitYosysLecSmt2`, `lecScript_unsat_of_step`), and evaluates bit-identically to `evalFluxSsaDagQ32` across all $2^{64}$ input words per variable.

### 1.2 Canonical Compiled Solver Catalog (`lean/Obend/Hardware/PdeSolvers.lean`)

`Obend.Hardware.PdeSolvers` compiles ten canonical conservation and balance laws once through `#pde_solver` with zero runtime `libLean` dependency (`canonicalPdeSolvers`):

| Solver | Coordinates & State Variables | Physical Regime & Key Verified Properties | Certified Q32 Step Defect $\varepsilon_{\text{step}}$ |
| :--- | :--- | :--- | :--- |
| `Burgers1D` | $x$; $(u)$ | Inviscid nonlinear advection $\partial_t u + \partial_x(\tfrac{1}{2}u^2) = 0$ | $\le 3 \cdot 2^{-32}$ (`3 ULP`) |
| `EulerGas3D` | $x, y, z$; $(\rho, \rho u, \rho v, \rho w, E)$ | 3D compressible ideal gas ($\gamma = 7/5$, $\rho \in [1, 2]$); CSE shares kinetic energy and pressure across flux rows | $\le 5 \cdot 2^{-32}$ (`5 ULP`) |
| `IdealMhd8Wave` | $x, y$; $(\rho, \rho\mathbf{u}, \mathbf{B}, E, \psi)$ | 2D 9-variable Powell/GLM ideal magnetohydrodynamics ($\gamma = 5/3$, $c_h = 2$) | $\le 27 \cdot 2^{-32}$ (`27 ULP`) |
| `DednerGlmMhd2D` | $x, y$; $(\rho, \rho\mathbf{u}, \mathbf{B}, E, \psi)$ | 2D GLM MHD with mixed hyperbolic/parabolic divergence-cleaning source $-\text{damp}\cdot\psi$ (`dedner_glm_psi_energy_damped`) | $\le 27 \cdot 2^{-32}$ (`27 ULP`) |
| `CurvedSpacetimeMaxwell` | $x, y, z$; $(\mathbf{D}, \mathbf{B})$ | 3+1 curved-spacetime ADM electrodynamics with nontrivial lapse $\alpha = 4/5$ and shift $\boldsymbol{\beta}$ | $\le 3 \cdot 2^{-32}$ (`3 ULP`) |
| `VlasovPoissonPhase` | $x, v_x$; $(f, E_x)$ | $1\text{x}1\text{v}$ kinetic Vlasov–Ampère phase-space advection | $\le 3 \cdot 2^{-32}$ (`3 ULP`) |
| `BonaMasso1DPrincipal` | $x$; $(\alpha, g_{xx}, A_x, D_x, K_{xx})$ | Source-free principal operator of 1+1 Bona–Massó hyperbolic ADM relativity ($f = 2$, $\beta = 1/5$, shared $\text{tr}\,K = K_{xx}/g_{xx}$) | $\le 302 \cdot 2^{-32}$ (`302 ULP`) |
| `BonaMasso1D` | $x$; $(\alpha, g_{xx}, A_x, D_x, K_{xx})$ | Inhomogeneous 1+1 Bona–Massó ADM balance law with quadratic extrinsic-curvature sources $-\alpha^2 f K_{xx}/g_{xx}$, $-2\alpha K_{xx}$, $\alpha(A_x D_x - K_{xx}^2/g_{xx})$ | $\le 302 \cdot 2^{-32}$ (`302 ULP`) |
| `BonaMassoZ4c1D` | $x$; $(\alpha, g_{xx}, A_x, D_x, K_{xx}, \Theta)$ | 1+1 Bona–Massó / Z4c formulation coupling $\hat{K} = K_{xx}/g_{xx} - 2\Theta$ and algebraic constraint damping $-\kappa_1 \alpha \Theta$ (`z4c_theta_constraint_strict_damped`) | $\le 302 \cdot 2^{-32}$ (`302 ULP`) |
| `ShallowWater1D` | $x$; $(h, q, b_x)$ | 1D Saint-Venant shallow water with bathymetry source $-g h b_x$ (`audusseBouchut_lakeAtRest_wellBalanced`) | $\le 3 \cdot 2^{-32}$ (`3 ULP`) |

### 1.3 Silicon, Vulkan GPU, and Yosys+Bitwuzla LEC Verification

Stage 5 of `hardware/gpu/verify_gpu.sh` executes end-to-end hardware and shader checks against the compiled `Obend.Hardware.PdeSolvers` artifacts:

- **Vulkan / AMD RDNA2 Execution**: Runs the emitted Q32.32 compute shaders (`burgers-1d-q32`, `euler-3d-q32`, `mhd-8wave-q32`, `bona-masso-1d-q32`, `bona-masso-z4c-1d-q32`) on an AMD Radeon RX 6750 XT (`gfx1030`, RADV) with `0 ULP` disagreement against Lean's `evalFluxSsaDagQ32`, and verifies that planted `addAsSub` and `mulHighZero` shader mutations are rejected. RDNA2 ISA binaries are independently translation-validated by `certifyDump_sound` and `certifyBlockDump_sound` (`lean/Obend/Hardware/Gpu/Rdna2/CertSound.lean`).
- **Verilator 5.020 Cycle-Accurate Simulation**: Compiles all seven systolic SystemVerilog modules (`EulerGas3D` axes 0–2, `IdealMhd8Wave` axes 0–1, `BonaMasso1D`, `BonaMassoZ4c1D`) in Verilator 5.020 with `0 ULP` difference across multi-state testbenches.
- **Yosys + Bitwuzla SMT-LIB2 Formal Equivalence**: Runs Yosys synthesis and Bitwuzla bit-precise equivalence checking between the emitted SystemVerilog (`emitModuleSV`) and Lean's `RtlModule` transition relation (`emitYosysLecSmt2`), proving `unsat` on `EulerGas3D_axis0` and `BonaMassoZ4c1D_axis0` and `sat` on a planted bit-0 fault. During Stage-5 bringup, this miter caught a genuine IEEE 1800-2017 §11.6.1 context-determined width propagation bug in `emitExprSV` (`lean/Obend/Hardware/HDL.lean`): `$signed(a)` inside `128'($signed(a))` widened compound 64-bit subtractions such as `64'd8589934592 - 64'(q)` in `reciprocalRtlExprs` to 128 bits *prior* to sign interpretation whenever `q[63] = 1`; enforcing inner self-determined width `128'($signed(64'(a)))` restored unconditional 64-bit equivalence.

### 1.4 Standalone CLI Rollouts, Receipts, and Artifact Emission (`lean/Obend/Analysis/NonlinearPdeCli.lean`)

`obend pde solve` and `obend pde check` (`runPdeCli`) execute exact rational (`"rat"`) or Q32.32 (`"q32"`) multi-D rollouts for any catalog solver or inline `(conservation-law ...)` S-expression under `periodic`, `transmissive`, or `reflective` boundaries, emit 256-bit `cSHAKE256` trajectory receipts (`pdeTrajectoryDigest_binding` with LEB128 length framing over every statement field), check untrusted surrogate trajectories against the `nonlinear_aposteriori_error_tube` bound, and write out WGSL kernels, SystemVerilog RTL, and Yosys SMT2 miters:

```bash
cat > z4c_pulse.json <<'EOF'
{
  "format": "nonlinear-conservation@1",
  "solver": "BonaMassoZ4c1D",
  "dims": [16],
  "steps": 8,
  "backend": "q32",
  "compareQ32": true,
  "recordTrajectory": true,
  "boundary": "periodic",
  "initial": [
    [1, 1, 0, 0, "1/16", "1/8"], [1, 1, 0, 0, "1/16", "1/8"],
    [1, 1, 0, 0, "1/16", "1/16"], [1, 1, 0, 0, 0, 0],
    [1, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0],
    [1, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0],
    [1, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0],
    [1, 1, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0],
    [1, 1, 0, 0, 0, 0], [1, 1, 0, 0, "1/16", "-1/16"],
    [1, 1, 0, 0, "1/16", "-1/8"], [1, 1, 0, 0, "1/16", "-1/8"]
  ]
}
EOF

obend pde solve z4c_pulse.json --out z4c_solved.json \
  --emit-wgsl ./z4c_wgsl --emit-sv ./bona_masso_z4c.sv --emit-lec ./bona_masso_z4c.smt2
obend pde check z4c_solved.json
```

---

## 2. Discrete Differential Geometry, Exterior Calculus, Spinor/Dirac Systems & Coupled Maxwell Radiation

- **Oriented 3-Skeleton DEC, Gauge Holonomy & Exact Poynting Energy Balance (`lean/Obend/Geometry/CochainAndGauge.lean`)**:
  - Over exact `CanonicalRat` cochains on an oriented 3-complex `CellComplex3D`, `coboundary_sq_zero` proves $d_1 \circ d_0 = 0$ and $d_2 \circ d_1 = 0$, and `discrete_stokes_exact` proves $\langle d_k \alpha, c_{k+1} \rangle = \langle \alpha, \partial_{k+1} c_{k+1} \rangle$.
  - `decMaxwell_divB_invariant` and `decMaxwell_charge_continuity` prove exact preservation of $\nabla \cdot B = 0$ and discrete Gauss charge continuity across arbitrary multi-step Yee trajectories without auxiliary divergence cleaning; `hodgeLaplacian0_psd` proves positive semidefiniteness of the scalar Hodge Laplacian.
  - `dec_maxwell_poynting_energy_balance` and `stepDecMaxwell_yee_bilinear_balance` prove the exact discrete Poynting identity over arbitrary 3-cells: the discrete electromagnetic energy difference across any valid Maxwell step equals $-\Delta t \langle E, J \rangle$ minus the boundary Poynting 2-cochain flux summed over $\partial c_3$.
  - `covariant_commutator_eq_curvature` and `discrete_bianchi_identity` prove $[D_x, D_y] = F_\square$, abelian curvature exactness $d_2 d_1 A = 0$, and the non-abelian six-face cube holonomy Bianchi identity for invertible $2 \times 2$ link transports.
- **Simplicial Finite Element Exterior Calculus (`lean/Obend/Analysis/SimplicialFeecFem.lean`)**:
  - Whitney 1-forms and lowest-order Raviart–Thomas elements with Dirichlet-free SPD stiffness (`stiffnessMatrix_spd_on_dirichlet_free`), global flux equilibration (`rt0_global_greens_equilibration_p1`), the Prager–Synge hypercircle identity and constant-free *a posteriori* continuum error bound (`pragerSynge_hypercircle_identity`, `pragerSynge_continuum_error_bound`), and two-sided Thomson–Dirichlet capacitance brackets (`thomsonDirichlet_capacitance_bracket`).
- **Dirac Structures & Multiscale Double Categories (`lean/Obend/Geometry/DiracDoubleCat.lean`)**:
  - Kernel-represented Dirac structures (`dirac_self_orthogonal_iff`, `dirac_power_conservation`), passive resistive termination (`resistiveDirac_dissipative_power`), power-preserving horizontal interconnection (`horizComp_preserves_power_balance`), cochain-commuting vertical coarse-graining (`coarseGrain_preserves_cohomology_and_conservation`), and the double-category interchange law (`doubleCat_interchange_law`).
- **Hardware Switching Currents Coupled to 3D DEC Maxwell (`lean/Obend/Hardware/GlitchAndTempestSafe.lean`, `lean/Obend/Apps/CyberneticRadioNode.lean`)**:
  - Rather than treating electromagnetic side-channel emission as an uncoupled scalar formula, `switching_current_bounds_radiated_flux` and `dualRail_decMaxwell_poynting_tempest_sound` inject gate-level rail switching currents as 1-cochain sources $J$ into `CellComplex3D` Maxwell steps, bounding radiated boundary Poynting flux and receiver SNR while `balanced_wddl_bus_ssn_secret_independent` proves secret-independent Hamming switching noise on dual-rail WDDL buses (`cybernetic_radio_node_multi_turn_sound`).

---

## 3. Open Hypergraphs, Equitable Symmetry Quotients, Adjoint E-Graphs & Interaction Nets

- **Symmetric Monoidal Open Hypergraphs & Dual RTL/GPU Lowering (`lean/Obend/Hardware/OpenHypergraph.lean`, `lean/Obend/Hardware/Square.lean`)**:
  - `StrictOpenHypergraph` represents multi-input/multi-output dataflow morphisms with whole-graph reverse-mode differentiation (`compileGraphAdjoint`). `compileHypergraphToRtl_sound`, `rtl_eq_gpu`, and `pipelined_eq_comb` prove exact denotational agreement across combinational evaluation, retimed pipelines, synchronous RTL, and GPU kernels.
- **1-WL Color Refinement, Equitable Intertwining & Quotient Adjoints (`lean/Obend/Analysis/Equitable.lean`, `lean/Obend/Hardware/QuantumMatter.lean`)**:
  - `checkEquitablePartition_sound`, `checkWl1ColorRefinementStable`, `equitable_handshake_identity`, and `equitable_intertwining_power` mechanize 1-dimensional Weisfeiler–Leman bisimulation, bipartite symmetrizability $|C_i| Q_{i,j} = |C_j| Q_{j,i}$, and polynomial/power intertwining $H^k S = S Q^k$ over $\mathbb{Z}$ and $\mathbb{Z}[i]$ with zero noncomputable reals.
  - On `StrictOpenHypergraph`, `quotientOpenHypergraph_intertwines_eval_and_adjoint` proves that both forward evaluation and reverse-mode `compileGraphAdjoint` differentiation of `buildSymmetric4LaneHypergraph` factor exactly through its compressed quotient `quotientOpenHypergraph`, and `symmetry_preserving_noise_zero_leakage` proves zero leakage out of the symmetric subspace under equivariant perturbations.
- **Equality-Saturated Adjoint Hypergraphs (`lean/Obend/Analysis/EqSatHypergraph.lean`)**:
  - Lifts primal and `compileGraphAdjoint` hypergraphs into `HyperEGraph`, proves consistency preservation across 16 algebraic and MAC-fusion rules (`saturateHyperEGraph_preserves_consistency`), and proves semantic, cotangent, pipelined-RTL, and discrete Pontryagin ODE adjoint preservation under minimum-cost extraction (`eqSat_preserves_eval_and_adjoint`, `optimizeAdjointHypergraph_preserves_cotangents`, `eqSat_pipelined_rtl_sound`, `pontryagin_flowpipe_adjoint_eqSat_sound`).
- **Commuting Interaction-Net Reductions (`lean/Obend/Hardware/HvmConfluence.lean`)**:
  - `diamond_of_disjoint` and `batch_schedule_invariant` prove strong commutation of disjoint active pairs and schedule invariance of parallel interaction-combinator batches lowered from `Obend.Leaf.Book` (`lean/Obend/Hardware/Hvm/Lower.lean`, `lowerBookToHvm_sound`).

---

## 4. Validated Continuous Analysis & Succinct Hardware Stencil Proofs

- **Taylor Models, Picard ODE Flowpipes & SOS Barriers (`lean/Obend/Analysis/TaylorModel.lean`, `lean/Obend/Analysis/Flowpipe.lean`, `lean/Obend/Analysis/SosLyapunov.lean`)**:
  - Polynomial-plus-interval Taylor models with semantic soundness (`taylorModel_picard_sound`, `verifyFlowpipe_sound`) and sparse Sum-of-Squares / Positivstellensatz certificates for nonlinear Lyapunov functions, control barrier functions, and DAE invariant manifolds (`checkSosLyapunov_sound`, `checkSosCbf_sound`, `checkDaeManifold_sound`).
- **Range-Safe Stencil PIOPs & 4-Tile Hypercube Hardware Prover (`lean/Obend/SymbolicZk/StencilRolloutStark.lean`, `lean/Obend/Hardware/OspcProver.lean`, `lean/Obend/Trailblaze/CathedralApex.lean`)**:
  - `stencil_numerator_mod_exact` and `q32Stencil_gpu_arraySource_sound` bridge `Obend.Core.RangeSafe` interval bounds to Goldilocks prime ($p = 2^{64} - 2^{32} + 1$) quotient/remainder constraints without field-inversion wraparound, backed by dual-track Canopy Merkle + Ajtai MSIS polynomial commitments (`lean/Obend/Crypto/DualSpine.lean`, `canopyAjtaiDualPCS_sound_of_hash_or_sis`).
  - `Obend.Hardware.OspcProver` synthesizes a 4-tile $Q_2$ hypercube hardware prover (`FaceIdeal4` cubical ternary registers with `faceIdeal4_boundary_ne_top`, discrimination-tree LUT, delta-net, and streaming LRAT tiles) with 2-hop XOR-butterfly Sumcheck/Merkle folding (`ospc_four_tile_prover_multi_cycle_sound`, `apex_cathedral_ospc_multi_turn_sound`).

---

## 5. Kernel Soundness & Reproducible Verification

Every module in `lean/Obend/` compiles under Lean 4 module encapsulation (`module` / `public section`), with compile-time axiom, computational-extractor, mutation-sensitivity, and documentation gates enforced by:
- **Axiom & Environment Census (`lean/Obend/AssertAxioms.lean`, `lean/Obend/Census.lean`, `lean/Obend/Tactic/DocsCensus.lean`)**: `#assert_axioms_tree` verifies at compile time that no library declaration depends on unproved obligations or custom axioms, `#assert_compiled` (`lean/Obend/AssertCompiled.lean`) tracks kernel-evaluated vectors, and `#check_docs_census` / `#docs_census` verify backticked module and constant references across root documentation.
- **Constructive Computational Extractors**: `Type`-valued extractors and witness reductions branch constructively via `DecidableEq` / `PSum` without `Classical.choice` or `Lean.trustCompiler`.
- **Mutation-Sensitivity `#tooth` Witnesses (`lean/Obend/Tactic/Tooth.lean`)**: load-bearing checkers and soundness theorems are paired with planted-mutation counterexamples verifying that weakening arithmetic bounds, CFL gates, length framing, or hardware widths causes kernel rejection.

On a Linux build host (never run `lake` on macOS laptops; see `README.md`), build and run the PDE, continuum-physics, and hardware verification suites from `lean/`:

```bash
cd lean
lake build Obend obend obend-emit-gpu obend-emit-sv Obend.Census Teeth
lake build MetaprogPdeCompilerTest PdeAcceleratorBridgeTest NonlinearPdeCliTest CyberneticRadioAndOspcTest
python3 tests/cli/run_live_subcommands.py
bash ../hardware/gpu/verify_gpu.sh --stage 5
```
