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

## 5. Metaprogrammed Multi-Dimensional Nonlinear Balance Laws & Z4c Relativity (`lean/Obend/Elab/PdeSolverElab.lean`, `lean/Obend/Hardware/PdeSolvers.lean`)

`#pde_solver Name := "(conservation-law ...)"` (`Obend.Elab.PdeSolverElab`) reads a declarative hyperbolic conservation or balance law $\partial_t U + \sum_d \partial_d F_d(U) = S(U)$ (coordinates, state variables, rational parameters, positivity domain, directional flux rows, algebraic source terms, state box, scaling weights, wavespeed bound and CFL number, slope limiter) and emits, under the solver's namespace, a `ConservationLawSpec` together with its continuum-to-silicon theorems checked by the Lean kernel at declaration time (`<Name>.endToEnd_certified : EndToEndPdeCert <Name>.spec` via `buildEndToEndPdeCert` in `lean/Obend/Hardware/MultiDStencilCorrect.lean`; see `LANYON.md` §1). A specification that fails any gate is refused with a diagnostic (`validatePdeSolverSexpr_refuses_invalid`, `checkPdeSolverSpec_refuses_cfl_violation`); `checkPdeSolverSpec_sound` states what acceptance guarantees.

- **Exact symbolic differentiation, derived Gershgorin wavespeeds, and Lipschitz bounds (`lean/Obend/Analysis/NonlinearMultiDPde.lean`, `lean/Obend/Analysis/HyperbolicBalanceLaws.lean`, `lean/Obend/Analysis/NonlinearErrorTube.lean`)**: `symJacobian_frechet_taylor` proves, for every flux row whose denominators are certified positive on the declared domain (`checkExprDomainSafe`), the identity $F(U + hV) - F(U) = h\,J(U)V + h^2 R(U, V, h)$ over the rationals with explicit remainder `symDirectionalRem`. Interval evaluation of the symbolic Jacobian over `effectiveStateBox` (`verifyWavespeedGershgorin_sound`) derives both the weighted $\ell_\infty$ operator bound and $|\lambda| \le a_{\max}$ for every rational eigenvalue on the state box, while `evalFluxLip_sound` and `verifyFluxLipschitz_sound` constructively derive weighted flux Lipschitz constants (`verifyFluxLipschitz`).
- **Reflective conservation and symmetrizers (`lean/Obend/Tactic/SymDiffAndFlux.lean`)**: `checkFluxEqReflective_sound` decides identities between rational flux expressions by clearing denominators into `CanonPoly` normal forms. `fluctuationConservation_of_reflective` gives LeVeque fluctuation conservation $A^-\Delta Q + A^+\Delta Q = F(U_R) - F(U_L)$ on every axis and component for all states in the domain; `symmetrizerReflective_sound` gives Friedrichs symmetry of $H(U)J(U)$.
- **Scheme conservation, error tubes, well-balancedness, and Z4c damping**: `tvd_rusanov_minmod_step_nonincreasing` (second-order MUSCL reconstruction with `minmod` does not increase total variation under $2\nu a_{\max} \le 1$), `tadmor_rusanov_entropy_dissipative` (Tadmor entropy-conservative flux with Rusanov dissipation has non-positive discrete entropy production on periodic grids), `evalSchemeStepRat_conserves_sourceless_component`, `rolloutRat_periodic_conserves_integral`, and `rolloutRat_reflective_conserves_component` (`lean/Obend/Analysis/NonlinearPdeCli.lean`) establish exact integral conservation across periodic and reflective walls. `z4c_theta_constraint_strict_damped`, `dedner_glm_psi_energy_damped`, and `audusseBouchut_lakeAtRest_wellBalanced` prove strict Z4c $\Theta$-constraint contraction, Dedner GLM divergence damping, and hydrostatic lake-at-rest preservation. `nonlinear_aposteriori_error_tube` and `q32_scheme_trajectory_error_tube` bound multi-step surrogate and Q32.32 rollout trajectories against `evalSchemeStepRat`, with `pdeTrajectoryDigest_binding` committing standalone CLI trajectories (`obend pde solve`, `obend pde check`).
- **Canonical solver catalog (`lean/Obend/Hardware/PdeSolvers.lean`, `lean/tests/metasystem/MetaprogPdeCompilerTest.lean`)**: `Burgers1D`; `EulerGas3D` (3D compressible gas dynamics, $\varepsilon_{\text{step}} \le 5\,\text{ULP}$); `IdealMhd8Wave` and `DednerGlmMhd2D` (2D 9-variable GLM magnetohydrodynamics without and with parabolic damping, $27\,\text{ULP}$); `CurvedSpacetimeMaxwell` (3+1 ADM electrodynamics, $3\,\text{ULP}$); `VlasovPoissonPhase` ($1\text{x}1\text{v}$ phase-space advection, $3\,\text{ULP}$); `BonaMasso1DPrincipal`, inhomogeneous `BonaMasso1D`, and `BonaMassoZ4c1D` (1+1 Bona–Massó and Z4c hyperbolic numerical relativity with extrinsic-curvature sources and $\Theta$ constraint damping, $302\,\text{ULP}$); and `ShallowWater1D` (bathymetric Saint-Venant equations, $3\,\text{ULP}$).

The fixed-point GPU and systolic RTL lowering of these solvers, together with Vulkan/Verilator/Yosys-LEC verification, is in `HARDWARE.md` §5.4 and `LANYON.md` §1.

---

## 6. Continuum Exterior Calculus, Finite Elements, and Open-System Geometry

- **Discrete exterior calculus, Poynting energy balance, and gauge fields (`lean/Obend/Geometry/CochainAndGauge.lean`, `lean/Obend/Hardware/GlitchAndTempestSafe.lean`)**: over exact rationals on an oriented 3-skeleton, `coboundary_sq_zero` and `discrete_stokes_exact` give $d \circ d = 0$ and Stokes' theorem; `decMaxwell_divB_invariant` and `decMaxwell_charge_continuity` give $\nabla \cdot B = 0$ and Gauss's law along arbitrary multi-step Yee trajectories without divergence cleaning; `dec_maxwell_poynting_energy_balance` and `stepDecMaxwell_yee_bilinear_balance` prove exact discrete Poynting electromagnetic energy conservation across 3-cells and couple gate-level rail switching 1-cochains to radiated boundary flux (`switching_current_bounds_radiated_flux`, `dualRail_decMaxwell_poynting_tempest_sound`); `hodgeLaplacian0_psd` gives a positive semidefinite Hodge Laplacian; `covariant_commutator_eq_curvature` and `discrete_bianchi_identity` give $[D_x, D_y] = F_{\square}$ and the Bianchi identity for both abelian curvature $d_2 d_1 A = 0$ and the six-face holonomy product of invertible $2 \times 2$ link transports.
- **Finite element exterior calculus (`lean/Obend/Analysis/SimplicialFeecFem.lean`)**: Whitney / Raviart–Thomas elements on simplicial meshes with stiffness positive-definiteness (`stiffnessMatrix_spd_on_dirichlet_free`), global flux equilibration (`rt0_global_greens_equilibration_p1`), the Prager–Synge hypercircle identity and constant-free continuum error bound (`pragerSynge_hypercircle_identity`, `pragerSynge_continuum_error_bound`), and two-sided capacitance brackets (`thomsonDirichlet_capacitance_bracket`).
- **Dirac structures and multiscale composition (`lean/Obend/Geometry/DiracDoubleCat.lean`)**: `dirac_self_orthogonal_iff` and `dirac_power_conservation` for kernel-represented Dirac structures, `resistiveDirac_dissipative_power` under passive termination, power balance under interconnection (`horizComp_preserves_power_balance`), coarse-graining that commutes with the coboundary (`coarseGrain_preserves_cohomology_and_conservation`), and the interchange law of the resulting double category (`doubleCat_interchange_law`).
- **Open-hypergraph symmetry (`lean/Obend/Hardware/OpenHypergraph.lean`, `lean/Obend/Hardware/QuantumMatter.lean`)**: for the symmetric four-lane family `buildSymmetric4LaneHypergraph`, `quotientOpenHypergraph_intertwines_eval_and_adjoint` proves that evaluation and whole-graph reverse-mode differentiation (`compileGraphAdjoint`) of the full graph equal the lifted results of its two-cell quotient `quotientOpenHypergraph`; `symmetry_preserving_noise_zero_leakage` proves that perturbations commuting with an equitable partition leak nothing out of the quotient subspace.
- **Interaction-net commutation (`lean/Obend/Hardware/HvmConfluence.lean`)**: `diamond_of_disjoint` and `batch_schedule_invariant` prove that independent firings commute and that a batch reaches one configuration under every schedule. Confluence of the whole reduction relation is not proved; the module says which cases are open.
