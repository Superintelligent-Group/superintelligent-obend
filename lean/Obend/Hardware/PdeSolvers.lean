module
public import Obend.Analysis.NonlinearMultiDPde
public import Obend.Analysis.HyperbolicBalanceLaws
public import Obend.Hardware.BalanceLawLowering
public import Obend.Analysis.NonlinearErrorTube
public import Obend.Hardware.MultiDStencilTile
meta import Obend.Elab.PdeSolverElab
import all Obend.Analysis.HyperbolicPdeCert
import all Obend.Analysis.PdeSexprAndApprox
import all Obend.Analysis.NonlinearMultiDPde
import all Obend.Analysis.HyperbolicBalanceLaws
import all Obend.Analysis.NonlinearErrorTube
import all Obend.Hardware.Gpu.StencilTile
import all Obend.Hardware.HDL
import all Obend.Hardware.MultiDStencilTile
import all Obend.Hardware.BalanceLawLowering
import all Obend.Tactic.SymDiffAndFlux

/-!
# Canonical Verified PDE Solver Catalog (`Obend.Hardware.PdeSolvers`)

Compiles the 10 canonical multi-dimensional nonlinear hyperbolic conservation-law and balance-law
systems once through `#pde_solver` with zero runtime `libLean` dependency (`meta import` only),
so `obend-emit-gpu` and downstream tools link cleanly without `supportInterpreter = true`.
-/

public section
namespace Obend.Hardware.PdeSolvers
open Obend.Analysis.HyperbolicPde
open Obend.Analysis.NonlinearMultiDPde
open Obend.Analysis.HyperbolicBalanceLaws
open Obend.Analysis.NonlinearErrorTube
open Obend.Hardware.MultiDStencilTile
open Obend.Hardware.BalanceLawLowering
open Obend.Tactic.SymDiffAndFlux
set_option autoImplicit false

-- 1. 1D Nonlinear Inviscid Burgers Equation: ∂_t u + ∂_x (1/2 u^2) = 0
#pde_solver Burgers1D :=
  "(conservation-law
     (name Burgers1D)
     (coords x)
     (vars u)
     (params)
     (domain)
     (fluxes
       (x (* 1/2 (sq u))))
     (wavespeed 2 1/4)
     (state-box (u -2 2))
     (limiter minmod))"

-- 2. 3D Compressible Euler Gas Dynamics: (rho, rhou, rhov, rhow, E) with rho > 0
#pde_solver EulerGas3D :=
  "(conservation-law
     (name EulerGas3D)
     (coords x y z)
     (vars rho rhou rhov rhow E)
     (params (gamma 7/5))
     (domain (> rho 0))
     (fluxes
       (x (let ((ke (* 1/2 (/ (+ (sq rhou) (sq rhov) (sq rhow)) rho)))
                (p (* (- gamma 1) (- E ke)))
                (u (/ rhou rho)))
            rhou
            (+ (* rhou u) p)
            (* rhov u)
            (* rhow u)
            (* (+ E p) u)))
       (y (let ((ke (* 1/2 (/ (+ (sq rhou) (sq rhov) (sq rhow)) rho)))
                (p (* (- gamma 1) (- E ke)))
                (v (/ rhov rho)))
            rhov
            (* rhou v)
            (+ (* rhov v) p)
            (* rhow v)
            (* (+ E p) v)))
       (z (let ((ke (* 1/2 (/ (+ (sq rhou) (sq rhov) (sq rhow)) rho)))
                (p (* (- gamma 1) (- E ke)))
                (w (/ rhow rho)))
            rhow
            (* rhou w)
            (* rhov w)
            (+ (* rhow w) p)
            (* (+ E p) w))))
     (wavespeed 4 1/8)
     (state-box (rho 1 2) (rhou -1/4 1/4) (rhov -1/4 1/4) (rhow -1/4 1/4) (E 1 3))
     (wavespeed-weights 1 1 1 1 5/2)
     (limiter minmod))"

-- 3. 2D 8-Wave GLM Divergence-Cleaned Ideal Magnetohydrodynamics (9 state variables, rho > 0)
#pde_solver IdealMhd8Wave :=
  "(conservation-law
     (name IdealMhd8Wave)
     (coords x y)
     (vars rho rhou rhov rhow Bx By Bz E psi)
     (params (gamma 5/3) (ch 2))
     (domain (> rho 0))
     (fluxes
       (x (let ((u (/ rhou rho))
                (v (/ rhov rho))
                (w (/ rhow rho))
                (ke (* 1/2 (/ (+ (sq rhou) (sq rhov) (sq rhow)) rho)))
                (me (* 1/2 (+ (sq Bx) (sq By) (sq Bz))))
                (pGas (* (- gamma 1) (- E (+ ke me))))
                (pTot (+ pGas me))
                (uDotB (+ (* u Bx) (* v By) (* w Bz))))
            rhou
            (- (+ (* rhou u) pTot) (sq Bx))
            (- (* rhov u) (* Bx By))
            (- (* rhow u) (* Bx Bz))
            psi
            (- (* u By) (* v Bx))
            (- (* u Bz) (* w Bx))
            (- (* (+ E pTot) u) (* Bx uDotB))
            (* (sq ch) Bx)))
       (y (let ((u (/ rhou rho))
                (v (/ rhov rho))
                (w (/ rhow rho))
                (ke (* 1/2 (/ (+ (sq rhou) (sq rhov) (sq rhow)) rho)))
                (me (* 1/2 (+ (sq Bx) (sq By) (sq Bz))))
                (pGas (* (- gamma 1) (- E (+ ke me))))
                (pTot (+ pGas me))
                (uDotB (+ (* u Bx) (* v By) (* w Bz))))
            rhov
            (- (* rhou v) (* By Bx))
            (- (+ (* rhov v) pTot) (sq By))
            (- (* rhow v) (* By Bz))
            (- (* v Bx) (* u By))
            psi
            (- (* v Bz) (* w By))
            (- (* (+ E pTot) v) (* By uDotB))
            (* (sq ch) By))))
     (wavespeed 5 1/10)
     (state-box (rho 1 2) (rhou -1/4 1/4) (rhov -1/4 1/4) (rhow -1/4 1/4) (Bx -1/4 1/4)
       (By -1/4 1/4) (Bz -1/4 1/4) (E 1 3) (psi -2 2))
     (wavespeed-weights 1 1 1 1 1/2 1/2 1/2 5/2 1)
     (limiter minmod))"

-- 4. 3+1 Curved-Spacetime ADM Electrodynamics (lapse alpha > 0, shift beta^i)
#pde_solver CurvedSpacetimeMaxwell :=
  "(conservation-law
     (name CurvedSpacetimeMaxwell)
     (coords x y z)
     (vars Dx Dy Dz Bx By Bz)
     (params (alpha 4/5) (betax 1/10) (betay -1/10) (betaz 1/20))
     (domain (> alpha 0))
     (fluxes
       (x (- (* betax Dx))
          (- (* alpha Bz) (* betax Dy))
          (- (- (* alpha By)) (* betax Dz))
          (- (* betax Bx))
          (- (- (* alpha Dz)) (* betax By))
          (- (* alpha Dy) (* betax Bz)))
       (y (- (- (* alpha Bz)) (* betay Dx))
          (- (* betay Dy))
          (- (* alpha Bx) (* betay Dz))
          (- (* alpha Dz) (* betay Bx))
          (- (* betay By))
          (- (- (* alpha Dx)) (* betay Bz)))
       (z (- (* alpha By) (* betaz Dx))
          (- (- (* alpha Bx)) (* betaz Dy))
          (- (* betaz Dz))
          (- (- (* alpha Dy)) (* betaz Bx))
          (- (* alpha Dx) (* betaz By))
          (- (* betaz Bz))))
     (wavespeed 2 1/5)
     (limiter minmod))"

-- 5. 2D Phase-Space (1x1v) Vlasov-Poisson Kinetic Advection (mMass > 0)
#pde_solver VlasovPoissonPhase :=
  "(conservation-law
     (name VlasovPoissonPhase)
     (coords x vx)
     (vars f Ex)
     (params (qCharge -1) (mMass 1) (vChar 3/2) (jCoef -1/4))
     (domain (> mMass 0))
     (fluxes
       (x (* vChar f) (* jCoef f))
       (vx (* (/ qCharge mMass) (* Ex f)) 0))
     (wavespeed 3 1/6)
     (state-box (f -4 4) (Ex -5/2 5/2))
     (wavespeed-weights 8 1)
     (limiter minmod))"

-- 6. 1+1 Bona–Massó hyperbolic ADM relativity, source-free principal part only
#pde_solver BonaMasso1DPrincipal :=
  "(conservation-law
     (name BonaMasso1DPrincipal)
     (coords x)
     (vars alpha gxx Ax Dx Kxx)
     (params (fBM 2) (beta 1/5))
     (domain (> alpha 0) (> gxx 0))
     (fluxes
       (x (let ((trK (/ Kxx gxx)))
            (- (* beta alpha))
            (- (* beta gxx))
            (+ (- (* beta Ax)) (* fBM (* alpha trK)))
            (+ (- (* beta Dx)) (* alpha trK))
            (+ (- (* beta Kxx)) (* alpha Ax)))))
     (wavespeed 9 1/10)
     (wavespeed-weights 1/256 1/256 2 1 1)
     (limiter minmod))"

-- 7. Full inhomogeneous 1+1 Bona–Massó hyperbolic ADM relativity with sources
#pde_solver BonaMasso1D :=
  "(conservation-law
     (name BonaMasso1D)
     (coords x)
     (vars alpha gxx Ax Dx Kxx)
     (params (fBM 2) (beta 1/5))
     (domain (> alpha 0) (> gxx 0))
     (fluxes
       (x (let ((trK (/ Kxx gxx)))
            (- (* beta alpha))
            (- (* beta gxx))
            (+ (- (* beta Ax)) (* fBM (* alpha trK)))
            (+ (- (* beta Dx)) (* alpha trK))
            (+ (- (* beta Kxx)) (* alpha Ax)))))
     (sources
       (- (* (sq alpha) fBM (/ Kxx gxx)))
       (- (* 2 alpha Kxx))
       0
       0
       (* alpha (- (* Ax Dx) (/ (sq Kxx) gxx))))
     (max-wavespeed 9) (cfl 1/10)
     (state-box (alpha 1/2 2) (gxx 1 4) (Ax -1/2 1/2) (Dx -1/2 1/2) (Kxx -1/2 1/2))
     (wavespeed-weights 1/4 1/4 1 1 1)
     (limiter minmod))"

-- 8. 1+1 Bona–Massó / Z4c relativity with constraint-damping variable Theta
-- (Bona, Ledvinka, Palenzuela & Žáček 2003; Bernuzzi & Hilditch 2010)
#pde_solver BonaMassoZ4c1D :=
  "(conservation-law
     (name BonaMassoZ4c1D)
     (coords x)
     (vars alpha gxx Ax Dx Kxx Theta)
     (params (fBM 2) (beta 1/5) (kappa1 1/2))
     (domain (> alpha 0) (> gxx 0))
     (fluxes
       (x (let ((trK (/ Kxx gxx))
                (kHat (- trK (* 2 Theta))))
            (- (* beta alpha))
            (- (* beta gxx))
            (+ (- (* beta Ax)) (* fBM (* alpha kHat)))
            (+ (- (* beta Dx)) (* alpha trK))
            (+ (- (* beta Kxx)) (* alpha Ax))
            (- (* beta Theta)))))
     (sources
       (- (* (sq alpha) fBM (- (/ Kxx gxx) (* 2 Theta))))
       (- (* 2 alpha Kxx))
       0
       0
       (- (* alpha (- (* Ax Dx) (/ (sq Kxx) gxx))) (* kappa1 (* alpha Theta)))
       (- (* kappa1 (* alpha Theta))))
     (max-wavespeed 9) (cfl 1/10)
     (state-box (alpha 1/2 2) (gxx 1 4) (Ax -1/2 1/2) (Dx -1/2 1/2) (Kxx -1/2 1/2) (Theta -1/4 1/4))
     (wavespeed-weights 1/4 1/4 1 1 1 1/4)
     (limiter minmod))"

-- 9. 2D GLM MHD with mixed hyperbolic/parabolic cleaning source -damp*psi (Dedner et al. 2002)
#pde_solver DednerGlmMhd2D :=
  "(conservation-law
     (name DednerGlmMhd2D)
     (coords x y)
     (vars rho rhou rhov rhow Bx By Bz E psi)
     (params (gamma 5/3) (ch 2) (damp 1/2))
     (domain (> rho 0))
     (fluxes
       (x (let ((u (/ rhou rho)) (v (/ rhov rho)) (w (/ rhow rho))
                (ke (* 1/2 (/ (+ (sq rhou) (sq rhov) (sq rhow)) rho)))
                (me (* 1/2 (+ (sq Bx) (sq By) (sq Bz))))
                (pGas (* (- gamma 1) (- E (+ ke me))))
                (pTot (+ pGas me))
                (uDotB (+ (* u Bx) (* v By) (* w Bz))))
            rhou
            (- (+ (* rhou u) pTot) (sq Bx))
            (- (* rhov u) (* Bx By)) (- (* rhow u) (* Bx Bz))
            psi
            (- (* u By) (* v Bx)) (- (* u Bz) (* w Bx))
            (- (* (+ E pTot) u) (* Bx uDotB))
            (* (sq ch) Bx)))
       (y (let ((u (/ rhou rho)) (v (/ rhov rho)) (w (/ rhow rho))
                (ke (* 1/2 (/ (+ (sq rhou) (sq rhov) (sq rhow)) rho)))
                (me (* 1/2 (+ (sq Bx) (sq By) (sq Bz))))
                (pGas (* (- gamma 1) (- E (+ ke me))))
                (pTot (+ pGas me))
                (uDotB (+ (* u Bx) (* v By) (* w Bz))))
            rhov
            (- (* rhou v) (* By Bx)) (- (+ (* rhov v) pTot) (sq By))
            (- (* rhow v) (* By Bz))
            (- (* v Bx) (* u By))
            psi
            (- (* v Bz) (* w By)) (- (* (+ E pTot) v) (* By uDotB))
            (* (sq ch) By))))
     (sources 0 0 0 0 0 0 0 0 (- (* damp psi)))
     (wavespeed 5 1/10)
     (state-box (rho 1 2) (rhou -1/4 1/4) (rhov -1/4 1/4) (rhow -1/4 1/4) (Bx -1/4 1/4)
       (By -1/4 1/4) (Bz -1/4 1/4) (E 1 3) (psi -2 2))
     (wavespeed-weights 1 1 1 1 1/2 1/2 1/2 5/2 1)
     (limiter minmod))"

-- 10. 1D shallow water over bathymetry with topography source -g*h*bx (Audusse et al. 2004)
#pde_solver ShallowWater1D :=
  "(conservation-law
     (name ShallowWater1D)
     (coords x)
     (vars h q bx)
     (params (g 2))
     (domain (> h 0))
     (fluxes (x q (+ (/ (sq q) h) (* 1/2 g (sq h))) 0))
     (sources 0 (- (* g h bx)) 0)
     (max-wavespeed 4) (cfl 1/8)
     (state-box (h 1 2) (q -1/2 1/2) (bx -1/2 1/2))
     (wavespeed-weights 1 2 1)
     (limiter minmod))"

def canonicalPdeSolvers : List (String × Obend.Analysis.NonlinearMultiDPde.ConservationLawSpec) :=
  [("Burgers1D", Burgers1D.spec),
   ("EulerGas3D", EulerGas3D.spec),
   ("IdealMhd8Wave", IdealMhd8Wave.spec),
   ("CurvedSpacetimeMaxwell", CurvedSpacetimeMaxwell.spec),
   ("VlasovPoissonPhase", VlasovPoissonPhase.spec),
   ("BonaMasso1DPrincipal", BonaMasso1DPrincipal.spec),
   ("BonaMasso1D", BonaMasso1D.spec),
   ("BonaMassoZ4c1D", BonaMassoZ4c1D.spec),
   ("DednerGlmMhd2D", DednerGlmMhd2D.spec),
   ("ShallowWater1D", ShallowWater1D.spec)]

def lookupCanonicalPdeSolver (name : String) :
    Option Obend.Analysis.NonlinearMultiDPde.ConservationLawSpec :=
  canonicalPdeSolvers.lookup name

end Obend.Hardware.PdeSolvers
end
