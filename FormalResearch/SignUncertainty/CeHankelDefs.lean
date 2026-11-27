module

public import FormalResearch.SignUncertainty.HankelBessel

/-!
# Definitions for the Cohn--Elkies Hankel problem `T_c^CE` (`fourier_mellin.tex`)

* `IsHankelCEFeasible c T h g`: real continuous mutual Hankel transforms `h, g` of finite mass on
  `[0, ∞)` with `h(0) = g(0) > 0`, `g ≥ 0` on `[0, ∞)` and `h ≤ 0` on `[T, ∞)`, `T ≥ 0`.
* `hankelTCE c`: `T_c^CE = inf { T : ℝ | ∃ h g, IsHankelCEFeasible c T h g }`.
-/

@[expose] public section

open MeasureTheory Set

namespace FormalResearch.SignUncertainty

/-- `(h, g)` is a feasible Cohn--Elkies Hankel pair at threshold `T` (`fourier_mellin.tex`): real continuous mutual
Hankel transforms of finite `M`, `h(0) = g(0) > 0`, `g ≥ 0` on `[0, ∞)` and `h ≤ 0` on `[T, ∞)`, `T ≥ 0`. -/
structure IsHankelCEFeasible (c T : ℝ) (h g : ℝ → ℝ) : Prop where
  h_cont : ContinuousOn h (Ici 0)
  g_cont : ContinuousOn g (Ici 0)
  h_int : IntegrableOn (fun Δ => h Δ * hankelRho0 c Δ) (Ioi 0)
  g_int : IntegrableOn (fun Δ => g Δ * hankelRho0 c Δ) (Ioi 0)
  g_eq : ∀ Δ ∈ Ici (0 : ℝ), besselHankelTransform c h Δ = g Δ
  h_eq : ∀ Δ ∈ Ici (0 : ℝ), besselHankelTransform c g Δ = h Δ
  origin : h 0 = g 0
  pos : 0 < g 0
  g_nonneg : ∀ Δ : ℝ, 0 ≤ Δ → 0 ≤ g Δ
  h_tail : ∀ Δ : ℝ, T ≤ Δ → h Δ ≤ 0
  T_nonneg : 0 ≤ T

/-- `T_c^CE`: the infimum of feasible thresholds of Cohn--Elkies Hankel pairs. -/
noncomputable def hankelTCE (c : ℝ) : ℝ := sInf {T : ℝ | ∃ h g, IsHankelCEFeasible c T h g}

end FormalResearch.SignUncertainty
