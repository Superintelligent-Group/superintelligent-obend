# Continuous, Semiconductor Device, and Manufacturing Verification

Obend verifies continuous-math, semiconductor device physics, radio-frequency DSP, and CNC manufacturing invariants by pairing exact rational interval/polynomial arithmetic in Lean 4 (`CanonicalRat`, `Interval`, `TaylorModel`, `SOSPoly`) with byte-decoded certificate judges in `Obend.Judge.registry`.

---

## 1. Validated Real, Taylor-Model, SOS, and Hybrid Flowpipe Judges

Continuous enclosures rest on exact dyadic/canonical rational arithmetic (`lean/Obend/Analysis/RealAnalysis.lean`, `lean/Obend/Judge/RealAnalysis.lean`, `lean/Obend/Elab/AutoCert.lean`, `lean/Obend/Elab/AutoCertTaylorSound.lean`):

- **Interval Bisection (`interval-bound@1`)**: `Obend.Judge.intervalCheck` (`lean/Obend/Judge/RealAnalysis.lean`) and `Obend.Elab.AutoCert.intervalFormat` (`lean/Obend/Elab/AutoCert.lean`) evaluate rational interval trees over arithmetic and transcendental bounds, backed by `intervalCheck_sound`.
- **Taylor Models (`taylor-model@1`)**: `TaylorModelExpr` and `evalTaylorModelExpr` (`lean/Obend/Analysis/TaylorModel.lean`, `lean/Obend/Elab/AutoCertTaylorSound.lean`) bound polynomial-plus-remainder enclosures over compact intervals, with `evalTaylorModelExpr_models` and `taylorModelJudge_semantic` proving semantic soundness over any `AnalyticModel`.
- **Sum-of-Squares & Gröbner Certificates (`groebner-ideal@1`, `sos-lyapunov-cbf@1`)**:
  - `lean/Obend/Judge/RealAnalysis.lean` proves `sosCheck_sound` for sparse multivariate `SOSPoly` decompositions.
  - `Obend.Elab.AutoCert` (`lean/Obend/Elab/AutoCert.lean`) verifies Buchberger S-polynomial ideal membership and Positivstellensatz non-negativity witnesses (`checkGroebnerJudge_sound`, `checkGroebnerJudge_sound_membership`, `badGroebnerCert_refused`).
  - `Obend.Analysis` (`lean/Obend/Analysis/SosLyapunov.lean`) verifies polynomial Lyapunov functions, control barrier functions (`checkSosLyapunov_sound`, `checkSosCbf_sound`), and DAE manifold invariance (`checkDaeManifold_sound`, `checkSosLyapunovProblem_sound`, `sosLyapunov_bad_refused`).
- **Hybrid Automata Flowpipes (`hybrid-flowpipe@1`)**: `Obend.Analysis` (`lean/Obend/Analysis/Flowpipe.lean`, `lean/Obend/Analysis/Hybrid.lean`) checks discrete guard/reset jumps (`HybridAutomaton`, `HybridProblem`, `HybridCert`) and continuous flowpipe safety (`hybrid_flowpipe_safety_admits_contract`, `hybridFlowpipe_bad_refused`).

---

## 2. Semiconductor Drift-Diffusion Judge (`devsim-dd1d@1`)

`lean/Obend/Hardware/Device` (`lean/Obend/Hardware/Device/Constants.lean`, `lean/Obend/Hardware/Device/Enclosure.lean`, `lean/Obend/Hardware/Device/DriftDiffusion.lean`, `lean/Obend/Hardware/Device/Sky130Diode.lean`) certifies 1D steady-state semiconductor device solutions produced by external TCAD solvers such as DEVSIM:

- **Validated Exponential & Scharfetter–Gummel Enclosures (`lean/Obend/Hardware/Device/Enclosure.lean`)**: Bounds exponential, Bernoulli (`bernOf_mem`), fractional-power (`powBracket_agree`), and square-root (`sqrtBracket_bounds`) functions in exact `CanonicalRat` intervals (`within_sound`, `expEnclosure_of_half`).
- **Poisson & Continuity Residual Checker (`lean/Obend/Hardware/Device/DriftDiffusion.lean`)**:
  - `DdSpec` specifies mesh nodes, doping profiles, boundary potentials, recombination parameters, and residual tolerances; `DdSolution` carries candidate electrostatic potential and electron/hole quasi-Fermi or carrier profiles.
  - `checkDd` verifies mesh monotonicity, boundary conditions, doping consistency, Gauss-law Poisson residuals, and Scharfetter–Gummel electron/hole continuity equations, returning pinpointed `DdClause` refusals (`bad_refused_doping`, `bad_refused`).
  - `ddFormat` registers `devsim-dd1d@1` in `Obend.Judge.registry` with byte-level soundness theorem `ddFormat_sound` (`DdMeaning`).
- **SkyWater 130 nm Junction Specification (`lean/Obend/Hardware/Device/Sky130Diode.lean`)**: `sky130DiodeRecipe` and `sky130DiodeSpec` instantiate `DdSpec` for a physical Sky130 p-well / n+ junction diode across bias sweeps.

---

## 3. Certified CNC Toolpath Gouge Verification (`cam-gouge@1`)

`Obend.Hardware.GeometryCAM` (`lean/Obend/Hardware/GeometryCAM.lean`) and `Obend.Apps.FidgetCam` (`lean/Obend/Apps/FidgetCam.lean`, `lean/Obend/Apps/FidgetCamCert.lean`) verify that multi-pass CNC milling toolpaths never gouge the target functional-representation (`FRepExpr`) solid:

- **Swept-Volume Subdivision Certificates (`lean/Obend/Hardware/GeometryCAM.lean`)**:
  - Target parts are represented as signed-distance / implicit `FRepExpr` trees evaluated over rational 3D boxes (`QBox`, `QIv`).
  - For each cutter-location segment `(CLPoint × CLPoint)` and `ToolAxis`, `CamPassCert` supplies a spatial subdivision cover proving that the swept cutter envelope stays strictly outside the finished part (`CamGougeMeaning`).
  - `camGougeFormat` registers `cam-gouge@1` in `Obend.Judge.registry`, backed by planted refusal `camGougeBad_refused`.
- **Continuous No-Gouge Proof (`lean/Obend/Apps/FidgetCam.lean`, `lean/Obend/Apps/FidgetCamCert.lean`)**:
  - `fidget_post_rotarySafe` and `fidgetCam_liverps_bore_radius` verify rotary post-processor and bore geometry invariants.
  - `fidgetCertAccepted_true`, `fidgetCamObj_meaning`, and `fidget_toolpath_no_gouge_continuous` prove continuous gouge freedom across every pass of `fidgetParams`.
  - Resulting RS-274 `.ngc` G-code and `.stl` meshes parse directly via `NgcToolpath` and `StlMesh` in `crates/obend-gui/src/apps.rs`.

---

## 4. Mixed-Signal Quadrature SDR Verification (`lean/Obend/Apps/SdrFt8Rx.lean`)

`lean/Obend/Apps/SdrFt8Rx.lean` combines bit-accurate RTL semantics with continuous Taylor-model and interval judges for a digital FT8 shortwave receiver:

- **Fixed-Point NCO Phasor Bound**: `nco_fixed_point_ok` and `nco_phasor_error` bound quantized lookup-table phasor error across every phase accumulator state of `sdrNcoModule` (`nco_tt_le`).
- **Image-Rejection Ratio ($\ge 63\,\text{dB}$)**: `irrCos_judge_ok` (`checkTaylorModelJudge`) and `irr_judge_ok` (`Obend.Judge.intervalCheck`) discharge the trigonometric and rational inequalities required by `sdr_irr_ge_63dB` over any `AnalyticModel`.

---

## 5. Metaprogrammed Multi-Dimensional Nonlinear Conservation Laws (`lean/Obend/Elab/PdeSolverElab.lean`)

`#pde_solver Name := "(conservation-law ...)"` (`Obend.Elab.PdeSolverElab`) reads a declarative system $\partial_t U + \sum_d \partial_d F_d(U) = 0$ (coordinates, state variables, rational parameters, positivity domain, one flux row per axis, a wavespeed bound and CFL number, a limiter) and emits, under the solver's namespace, a `ConservationLawSpec` together with theorems that the Lean kernel checks at the point of declaration. A specification that fails any gate is refused with a diagnostic (`validatePdeSolverSexpr_refuses_invalid`, `checkPdeSolverSpec_refuses_cfl_violation`); `checkPdeSolverSpec_sound` states what acceptance guarantees.

- **Exact symbolic differentiation (`lean/Obend/Analysis/NonlinearMultiDPde.lean`)**: `symJacobian_frechet_taylor` proves, for every flux row whose denominators are certified positive on the declared domain (`checkExprDomainSafe`), the identity $F(U + hV) - F(U) = h\,J(U)V + h^2 R(U, V, h)$ over the rationals, with the remainder given explicitly by `symDirectionalRem`. There is no truncation and no floating point.
- **Reflective conservation and symmetrizers (`lean/Obend/Tactic/SymDiffAndFlux.lean`)**: `checkFluxEqReflective_sound` decides identities between rational flux expressions by clearing denominators into `CanonPoly` normal forms. `fluctuationConservation_of_reflective` gives LeVeque fluctuation conservation $A^-\Delta Q + A^+\Delta Q = F(U_R) - F(U_L)$ on every axis and component for all states in the domain; `symmetrizerReflective_sound` gives Friedrichs symmetry of $H(U)J(U)$.
- **Scheme properties**: `tvd_rusanov_minmod_step_nonincreasing` (second-order MUSCL reconstruction with the `minmod` limiter does not increase total variation under $2\nu a_{\max} \le 1$ for a Lipschitz flux, on every grid size and profile), `tadmor_rusanov_entropy_dissipative` (Tadmor's entropy-conservative flux with Rusanov dissipation has summed entropy production of the dissipative sign on every periodic grid), and `multiDSweep_conserves_total_mass_momentum_energy` with its Strang counterpart in `spec_sweep_conserves_integral`. A multi-turn rollout accumulates Courant time and refuses a step exactly when it violates the CFL bound (`runPdeRolloutTrace_invariants`, `stepPdeRolloutTurn_none_iff_cfl_violation`).
- **Systems compiled by the command (`lean/tests/metasystem/MetaprogPdeCompilerTest.lean`)**: `Burgers1D`; `EulerGas3D` (compressible gas dynamics, positive density); `IdealMhd8Wave` (two-dimensional 8-wave GLM magnetohydrodynamics); `CurvedSpacetimeMaxwell` (3+1 ADM electrodynamics with fixed lapse and shift); `VlasovPoissonPhase` (1x1v phase-space advection); and `BonaMasso1D`, the source-free principal flux operator $\partial_t U + \partial_x F^x(U) = 0$ of the Bona–Massó–Seidel–Stela (1995) 1+1 hyperbolic ADM system with $U = (\alpha, g_{xx}, A_x, D_x, K_{xx})$, $\alpha > 0$, $g_{xx} > 0$, shift $\beta = 1/5$, slicing $f = 2$, and the trace $K_{xx}/g_{xx}$ shared between two fluxes. The source terms of the full system are not modelled, and the wavespeed is a declared parameter that Lean does not derive. For each system the theorems above are instances produced by the command, not separate hand proofs.

The fixed-point accelerator lowering of these solvers, including what is proved and what is measured on a GPU and in RTL simulation, is in `HARDWARE.md` §5.4.

---

## 6. Continuum Exterior Calculus, Finite Elements, and Open-System Geometry

- **Discrete exterior calculus and gauge fields (`lean/Obend/Geometry/CochainAndGauge.lean`)**: over exact rationals on an oriented 3-skeleton, `coboundary_sq_zero` and `discrete_stokes_exact` give $d \circ d = 0$ and Stokes' theorem; `decMaxwell_divB_invariant` and `decMaxwell_charge_continuity` give $\nabla \cdot B = 0$ and Gauss's law along arbitrary multi-step Yee trajectories without divergence cleaning; `hodgeLaplacian0_psd` gives a positive semidefinite Hodge Laplacian; `covariant_commutator_eq_curvature` and `discrete_bianchi_identity` give $[D_x, D_y] = F_{xy}$ and the Bianchi identity, the latter for both abelian curvature $d_2 d_1 A = 0$ and the six-face holonomy product of arbitrary invertible $2 \times 2$ link transports.
- **Finite element exterior calculus (`lean/Obend/Analysis/SimplicialFeecFem.lean`)**: Whitney / Raviart–Thomas elements on simplicial meshes with stiffness positive-definiteness (`stiffnessMatrix_spd_on_dirichlet_free`), global flux equilibration (`rt0_global_greens_equilibration_p1`), the Prager–Synge hypercircle identity and constant-free continuum error bound (`pragerSynge_hypercircle_identity`, `pragerSynge_continuum_error_bound`), and two-sided capacitance brackets (`thomsonDirichlet_capacitance_bracket`).
- **Dirac structures and multiscale composition (`lean/Obend/Geometry/DiracDoubleCat.lean`)**: `dirac_self_orthogonal_iff` and `dirac_power_conservation` for kernel-represented Dirac structures, `resistiveDirac_dissipative_power` under passive termination, power balance under interconnection (`horizComp_preserves_power_balance`), coarse-graining that commutes with the coboundary (`coarseGrain_preserves_cohomology_and_conservation`), and the interchange law of the resulting double category (`doubleCat_interchange_law`).
- **Open-hypergraph symmetry (`lean/Obend/Hardware/OpenHypergraph.lean`, `lean/Obend/Hardware/QuantumMatter.lean`)**: for the symmetric four-lane family `buildSymmetric4LaneHypergraph`, `quotientOpenHypergraph_intertwines_eval_and_adjoint` proves that evaluation and whole-graph reverse-mode differentiation (`compileGraphAdjoint`) of the full graph equal the lifted results of its two-cell quotient `quotientOpenHypergraph`; `symmetry_preserving_noise_zero_leakage` proves that perturbations commuting with an equitable partition leak nothing out of the quotient subspace.
- **Interaction-net commutation (`lean/Obend/Hardware/HvmConfluence.lean`)**: `diamond_of_disjoint` and `batch_schedule_invariant` prove that independent firings commute and that a batch reaches one configuration under every schedule. Confluence of the whole reduction relation is not proved; the module says which cases are open.
