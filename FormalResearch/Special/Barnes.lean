module

public import FormalResearch.Special.BarnesDigammaReal
public import FormalResearch.Special.BarnesDigamma
public import FormalResearch.Special.BarnesLogSeries
public import FormalResearch.Special.BarnesNormalisation
public import FormalResearch.Special.BarnesG
public import FormalResearch.Special.BarnesEntire
public import FormalResearch.Special.BarnesZeroOrder
public import FormalResearch.Special.BarnesGrowth
public import FormalResearch.Special.BarnesKernel
public import FormalResearch.Special.BarnesContourSetup
public import FormalResearch.Special.BarnesDecay
public import FormalResearch.Special.BarnesContour
public import FormalResearch.Special.BarnesIntegral
public import FormalResearch.Special.BarnesBG
public import FormalResearch.Special.BarnesVI
public import FormalResearch.Special.BarnesGTheta

/-!
# Barnes' `G`-function and the Gamma/digamma identities of `thm:BG` and `lem:VI`

Aggregate of the `Barnes*` modules (Weyl/free_fermion/paper/parts/constants.tex: `thm:BG`, `lem:VI`).

* `BarnesDigammaReal`, `BarnesDigamma`: Gauss' series `ψ(z) = -γ + ∑ (1/(k+1) - 1/(k+z))`, `Re z > 0`.
* `BarnesLogSeries`, `BarnesNormalisation`, `BarnesG`: Weierstrass log series, `G(2) = 1` from
  Stirling, `G` on `Re w > 0` with `G(w+1) = Γ(w) G(w)`, `G' = Q G`.
* `BarnesEntire`, `BarnesZeroOrder`: entire extension, zeros `-m` of order `m+1`.
* `BarnesGrowth`, `BarnesKernel`, `BarnesDecay`, `BarnesContourSetup`, `BarnesContour`: the contour
  shift `∫ψ(z(x))/(cosh πx + cos θ) dx = 2[Q(1+b) - Q(1-b)]/sin θ`.
* `BarnesIntegral`, `BarnesBG`: differentiation under the integral, `thm:BG` (real form).
* `BarnesVI`: `lem:VI`.  `BarnesGTheta`: real part of the paper's `g_θ(f(ξ))`.
-/
