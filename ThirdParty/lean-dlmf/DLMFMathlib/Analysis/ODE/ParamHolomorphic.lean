/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import DLMFMathlib.Analysis.ODE.PowerSeriesUniqueness
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Holomorphic dependence on a parameter for linear second-order ODEs

Consider `y'' = (p₀(t) + λ p₁(t)) y' + (q₀(t) + λ q₁(t)) y` on `ℝ` with continuous `pᵢ`, `qᵢ`
and a complex parameter `λ`. If `F(·, λ)` solves it for every `λ`, with data at `t₀`
independent of `λ`, then `λ ↦ F(t, λ)` and `λ ↦ F'(t, λ)` are entire for every `t`.

## Main definitions

* `discRetract`: the radial retraction of `ℂ` onto the closed disc of radius `R`, as a
  bounded continuous function.
* `boundedHolomorphicOnBall`: the closed subspace `H_R` of bounded continuous functions
  `ℂ → ℂ` that are holomorphic on the open disc of radius `R`.
* `affineParamCoeff`, `paramVectorField`: the coefficient `c₀ + c₁ λ` in `H_R` and the
  first-order vector field on `H_R × H_R`.

## Main results

* `differentiable_param_of_linear_ode`: holomorphic dependence of the solution and its
  derivative on the parameter.

## Implementation notes

The proof solves the equation once, with values in the Banach space `H_R` (a closed subspace,
as locally uniform limits of holomorphic functions are holomorphic). The parameter `λ` is
replaced by its radial retraction onto the closed disc, a bounded continuous function that is
the identity on the disc. Evaluating the `H_R`-valued solution at `λ` gives the scalar
solution, which agrees with `F(·, λ)` by uniqueness.

The same canonical bounded holomorphic carrier inherits its algebra operations through
`boundedHolomorphicOnBallAlgebra`. Mathlib's `ContinuousMap.curry`, compact-domain supremum
norm, and continuous composition by the radial retraction lift arbitrary jointly continuous
holomorphic families continuously into this Banach algebra.
-/

@[expose] public noncomputable section

open Set Filter Topology Metric BoundedContinuousFunction

namespace ODE

/-- The radial retraction `z ↦ z / max 1 (‖z‖ / R)` of `ℂ` onto the closed disc of radius
`R`, as a bounded continuous function. -/
def discRetract (R : ℝ) (hR : 0 < R) : ℂ →ᵇ ℂ :=
  ofNormedAddCommGroup (fun z => z / ((max 1 (‖z‖ / R) : ℝ) : ℂ))
    (continuous_id.div (Complex.continuous_ofReal.comp
      (continuous_const.max (continuous_norm.div_const R)))
      fun z => Complex.ofReal_ne_zero.mpr (by positivity))
    R (fun z => by
      have hM : (0 : ℝ) < max 1 (‖z‖ / R) := by positivity
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hM.le, div_le_iff₀ hM]
      have := le_max_right 1 (‖z‖ / R)
      calc ‖z‖ = R * (‖z‖ / R) := by field_simp
        _ ≤ R * max 1 (‖z‖ / R) := by gcongr)

/-- Identity under the stated parameter and domain assumptions: `discRetract R hR z = z`. -/
private lemma discRetract_apply_of_mem_closedBall {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) R) :
    discRetract R hR z = z := by
  have : ‖z‖ / R ≤ 1 := by
    rw [div_le_one hR]; simpa using hz
  simp [discRetract, max_eq_left this]

/-- The bounded continuous functions `ℂ → ℂ` holomorphic on the open disc of radius `R`. -/
def boundedHolomorphicOnBall (R : ℝ) : Submodule ℂ (ℂ →ᵇ ℂ) where
  carrier := {f | DifferentiableOn ℂ f (ball 0 R)}
  add_mem' := by
    intro f g hf hg
    simp only [mem_ofPred_eq, coe_add] at *
    exact hf.add hg
  zero_mem' := by
    simp only [mem_ofPred_eq, coe_zero]
    exact differentiableOn_const 0
  smul_mem' := by
    intro c f hf
    simp only [mem_ofPred_eq, coe_smul] at *
    exact hf.const_smul c

/-- Formula under the stated hypotheses: `f * g ∈ boundedHolomorphicOnBall R`. -/
lemma mul_mem_boundedHolomorphicOnBall {R : ℝ} {f g : ℂ →ᵇ ℂ} (hf : f ∈ boundedHolomorphicOnBall R)
    (hg : g ∈ boundedHolomorphicOnBall R) :
    f * g ∈ boundedHolomorphicOnBall R := by
  change DifferentiableOn ℂ (⇑(f * g)) _
  rw [coe_mul]
  exact DifferentiableOn.mul hf hg

/-- Formula under the stated hypotheses: `(1 : ℂ →ᵇ ℂ) ∈ boundedHolomorphicOnBall R`. -/
lemma one_mem_boundedHolomorphicOnBall (R : ℝ) : (1 : ℂ →ᵇ ℂ) ∈ boundedHolomorphicOnBall R := by
  change DifferentiableOn ℂ (⇑(1 : ℂ →ᵇ ℂ)) _
  rw [coe_one]
  exact differentiableOn_const 1

/-- Formula under the stated hypotheses: `discRetract R hR ∈ boundedHolomorphicOnBall R`. -/
lemma discRetract_mem_boundedHolomorphicOnBall {R : ℝ} (hR : 0 < R) : discRetract R hR ∈
    boundedHolomorphicOnBall R := by
  change DifferentiableOn ℂ (⇑(discRetract R hR)) _
  exact differentiableOn_id.congr fun z hz =>
    discRetract_apply_of_mem_closedBall hR (ball_subset_closedBall hz)

/-- The stated relation follows from the given hypotheses:
`IsClosed (boundedHolomorphicOnBall R : Set (ℂ →ᵇ ℂ))`. -/
private lemma isClosed_boundedHolomorphicOnBall (R : ℝ) : IsClosed
    (boundedHolomorphicOnBall R : Set (ℂ →ᵇ ℂ)) := by
  refine isClosed_of_closure_subset fun f hf => ?_
  have hne := mem_closure_iff_nhdsWithin_neBot.mp hf
  have ht : Tendsto (fun g : ℂ →ᵇ ℂ => g)
      (𝓝[(boundedHolomorphicOnBall R : Set (ℂ →ᵇ ℂ))] f) (𝓝 f) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hu := (tendsto_iff_tendstoUniformly.mp ht).tendstoUniformlyOn (s := ball 0 R)
  exact hu.tendstoLocallyUniformlyOn.differentiableOn
    (eventually_mem_nhdsWithin.mono fun g hg => hg) isOpen_ball

/-- The bounded holomorphic-function subspace is closed in the space of bounded continuous
functions. -/
instance (R : ℝ) : IsClosed (boundedHolomorphicOnBall R : Set (ℂ →ᵇ ℂ)) :=
    isClosed_boundedHolomorphicOnBall R

/-- The bounded holomorphic-function subspace is complete in the supremum norm. -/
instance (R : ℝ) : CompleteSpace (boundedHolomorphicOnBall R) :=
  IsClosed.completeSpace_coe (s := (boundedHolomorphicOnBall R : Set (ℂ →ᵇ ℂ)))

/-- The coefficient `c₀ + c₁ λ` (with `λ` retracted onto the closed disc) in `H_R`. -/
def affineParamCoeff (R : ℝ) (hR : 0 < R) (c₀ c₁ : ℂ) : boundedHolomorphicOnBall R :=
  ⟨c₀ • 1 + c₁ • discRetract R hR,
      add_mem (Submodule.smul_mem _ _ (one_mem_boundedHolomorphicOnBall R))
    (Submodule.smul_mem _ _ (discRetract_mem_boundedHolomorphicOnBall hR))⟩

/-- The first-order field `(U, V) ↦ (V, (p₀ + λ p₁) V + (q₀ + λ q₁) U)` on `H_R × H_R`. -/
def paramVectorField (R : ℝ) (hR : 0 < R) (p₀ p₁ q₀ q₁ : ℝ → ℂ) (t : ℝ)
    (y : boundedHolomorphicOnBall R × boundedHolomorphicOnBall R) : boundedHolomorphicOnBall R ×
        boundedHolomorphicOnBall R :=
  (y.2, ⟨(affineParamCoeff R hR (p₀ t) (p₁ t) : ℂ →ᵇ ℂ) * y.2 +
      (affineParamCoeff R hR (q₀ t) (q₁ t) : ℂ →ᵇ ℂ) * y.1,
    add_mem (mul_mem_boundedHolomorphicOnBall (affineParamCoeff R hR _ _).2 y.2.2)
      (mul_mem_boundedHolomorphicOnBall (affineParamCoeff R hR _ _).2 y.1.2)⟩)

/-- The stated relation follows from the given hypotheses:
`LipschitzWith ⟨1 + ‖(affineParamCoeff R hR (p₀ t) (p₁ t) : ℂ →ᵇ ℂ)‖ + ‖(affineParamCoeff R hR (q₀
t) (q₁ t) : ℂ →ᵇ ℂ)‖, by positivity⟩ (paramVectorField R hR p₀ p₁ q₀ q₁ t)`. -/
private lemma lipschitzWith_paramVectorField (R : ℝ) (hR : 0 < R) (p₀ p₁ q₀ q₁ : ℝ → ℂ) (t : ℝ) :
    LipschitzWith ⟨1 + ‖(affineParamCoeff R hR (p₀ t) (p₁ t) : ℂ →ᵇ ℂ)‖ +
        ‖(affineParamCoeff R hR (q₀ t) (q₁ t) : ℂ →ᵇ ℂ)‖, by positivity⟩
      (paramVectorField R hR p₀ p₁ q₀ q₁ t) := by
  set P : ℂ →ᵇ ℂ := ↑(affineParamCoeff R hR (p₀ t) (p₁ t))
  set Qc : ℂ →ᵇ ℂ := ↑(affineParamCoeff R hR (q₀ t) (q₁ t))
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  have h1 : dist y.1 z.1 ≤ dist y z := by rw [Prod.dist_eq]; exact le_max_left _ _
  have h2 : dist y.2 z.2 ≤ dist y z := by rw [Prod.dist_eq]; exact le_max_right _ _
  have hd := dist_nonneg (x := y) (y := z)
  have hP := norm_nonneg P
  have hQ := norm_nonneg Qc
  have key : ∀ (A : ℂ →ᵇ ℂ) (u v : boundedHolomorphicOnBall R),
      dist (A * (u : ℂ →ᵇ ℂ)) (A * (v : ℂ →ᵇ ℂ)) ≤ ‖A‖ * dist u v := by
    intro A u v
    rw [dist_eq_norm, ← mul_sub, Subtype.dist_eq, dist_eq_norm]
    exact norm_mul_le _ _
  rw [Prod.dist_eq]
  change _ ≤ (1 + ‖P‖ + ‖Qc‖) * dist y z
  refine max_le (by change dist y.2 z.2 ≤ _; nlinarith) ?_
  rw [Subtype.dist_eq]
  calc dist (P * (y.2 : ℂ →ᵇ ℂ) + Qc * (y.1 : ℂ →ᵇ ℂ)) (P * (z.2 : ℂ →ᵇ ℂ) + Qc * (z.1 : ℂ →ᵇ ℂ))
      ≤ dist (P * (y.2 : ℂ →ᵇ ℂ)) (P * (z.2 : ℂ →ᵇ ℂ)) +
          dist (Qc * (y.1 : ℂ →ᵇ ℂ)) (Qc * (z.1 : ℂ →ᵇ ℂ)) := dist_add_add_le _ _ _ _
    _ ≤ ‖P‖ * dist y.2 z.2 + ‖Qc‖ * dist y.1 z.1 := add_le_add (key _ _ _) (key _ _ _)
    _ ≤ (1 + ‖P‖ + ‖Qc‖) * dist y z := by nlinarith

variable {p₀ p₁ q₀ q₁ : ℝ → ℂ}

/-- The function `(fun t => (affineParamCoeff R hR (c₀ t) (c₁ t) : ℂ →ᵇ ℂ))` is continuous on `s`.
-/
private lemma continuousOn_affineParamCoeff {R : ℝ} (hR : 0 < R) {s : Set ℝ} {c₀ c₁ : ℝ → ℂ}
    (h₀ : ContinuousOn c₀ s) (h₁ : ContinuousOn c₁ s) :
    ContinuousOn (fun t => (affineParamCoeff R hR (c₀ t) (c₁ t) : ℂ →ᵇ ℂ)) s :=
  (h₀.smul continuousOn_const).add (h₁.smul continuousOn_const)

/-- **Holomorphic parameter dependence on a compact interval**: for `R > 0` there are
`f, f' : ℝ → ℂ → ℂ`, holomorphic in `λ` on the disc `‖λ‖ < R` for every `t`, such that for
every `λ` with `‖λ‖ ≤ R`, `(f(·, λ), f'(·, λ))` solves
`y' = y'`, `(y')' = (p₀ + λ p₁) y' + (q₀ + λ q₁) y` on `[a, b]` with data `(y₀, y₁)` at `a`. -/
private lemma exists_holomorphic_param_solution_Icc {a b R : ℝ} (hab : a ≤ b) (hR : 0 < R)
    (hp₀ : ContinuousOn p₀ (Icc a b)) (hp₁ : ContinuousOn p₁ (Icc a b))
    (hq₀ : ContinuousOn q₀ (Icc a b)) (hq₁ : ContinuousOn q₁ (Icc a b)) (y₀ y₁ : ℂ) :
    ∃ f f' : ℝ → ℂ → ℂ,
      (∀ t, DifferentiableOn ℂ (f t) (ball 0 R) ∧ DifferentiableOn ℂ (f' t) (ball 0 R)) ∧
      ∀ μ ∈ closedBall (0 : ℂ) R, f a μ = y₀ ∧ f' a μ = y₁ ∧ ∀ t ∈ Icc a b,
        HasDerivWithinAt (fun t => f t μ) (f' t μ) (Icc a b) t ∧
        HasDerivWithinAt (fun t => f' t μ)
          ((p₀ t + μ * p₁ t) * f' t μ + (q₀ t + μ * q₁ t) * f t μ) (Icc a b) t := by
  obtain ⟨Bp, hBp⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (continuousOn_affineParamCoeff hR hp₀ hp₁)
  obtain ⟨Bq, hBq⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (continuousOn_affineParamCoeff hR hq₀ hq₁)
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hBp0 : 0 ≤ Bp := (norm_nonneg _).trans (hBp a ha)
  have hBq0 : 0 ≤ Bq := (norm_nonneg _).trans (hBq a ha)
  set M : NNReal := ⟨1 + Bp + Bq, by positivity⟩
  have hlip : ∀ t ∈ Icc a b, LipschitzWith M (paramVectorField R hR p₀ p₁ q₀ q₁ t) := fun t ht =>
    (lipschitzWith_paramVectorField R hR p₀ p₁ q₀ q₁ t).weaken (by
      change 1 + _ + _ ≤ 1 + Bp + Bq
      linarith [hBp t ht, hBq t ht])
  have h0 : ∀ t ∈ Icc a b, paramVectorField R hR p₀ p₁ q₀ q₁ t 0 = 0 := fun t _ => by
    simp only [paramVectorField, Prod.fst_zero, Prod.snd_zero, ZeroMemClass.coe_zero,
        mul_zero, add_zero]
    rfl
  have hcont : ∀ y, ContinuousOn (fun t => paramVectorField R hR p₀ p₁ q₀ q₁ t y) (Icc a b) := by
    intro y
    refine continuousOn_const.prodMk ?_
    refine (Topology.IsInducing.subtypeVal).continuousOn_iff.mpr ?_
    exact ((continuousOn_affineParamCoeff hR hp₀ hp₁).mul continuousOn_const).add
      ((continuousOn_affineParamCoeff hR hq₀ hq₁).mul continuousOn_const)
  set x₀ : boundedHolomorphicOnBall R × boundedHolomorphicOnBall R :=
    (⟨y₀ • 1, Submodule.smul_mem _ _ (one_mem_boundedHolomorphicOnBall R)⟩,
      ⟨y₁ • 1, Submodule.smul_mem _ _ (one_mem_boundedHolomorphicOnBall R)⟩)
  obtain ⟨β, hβ0, hβ⟩ := exists_hasDerivWithinAt_Icc_of_lipschitz hab hlip h0 hcont x₀
  refine ⟨fun t μ => ((β t).1 : ℂ →ᵇ ℂ) μ, fun t μ => ((β t).2 : ℂ →ᵇ ℂ) μ,
    fun t => ⟨(β t).1.2, (β t).2.2⟩, fun μ hμ => ⟨by simp [hβ0, x₀], by simp [hβ0, x₀],
      fun t ht => ?_⟩⟩
  set L : boundedHolomorphicOnBall R →L[ℝ] ℂ :=
    ((evalCLM ℂ μ).comp (boundedHolomorphicOnBall R).subtypeL).restrictScalars ℝ
  have k1 := L.hasFDerivAt.comp_hasDerivWithinAt t (hβ t ht).fst
  have k2 := L.hasFDerivAt.comp_hasDerivWithinAt t (hβ t ht).snd
  refine ⟨k1, ?_⟩
  convert k2 using 1
  · rfl
  · simp only [L, paramVectorField, affineParamCoeff, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.coe_comp, Submodule.coe_subtypeL, Submodule.coe_subtype, evalCLM_apply,
      coe_add, coe_mul, coe_smul, coe_one, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul, mul_one, discRetract_apply_of_mem_closedBall hR hμ, Function.comp_apply]
    ring

/-- The forward case of `ODE.differentiable_param_of_linear_ode`. -/
private lemma differentiableOn_param_of_le (hp₀ : Continuous p₀) (hp₁ : Continuous p₁)
    (hq₀ : Continuous q₀) (hq₁ : Continuous q₁) {t₀ : ℝ} {y₀ y₁ : ℂ} {F F' : ℝ → ℂ → ℂ}
    (hF : ∀ μ t, HasDerivAt (fun t => F t μ) (F' t μ) t ∧
      HasDerivAt (fun t => F' t μ) ((p₀ t + μ * p₁ t) * F' t μ + (q₀ t + μ * q₁ t) * F t μ) t)
    (h₀ : ∀ μ, F t₀ μ = y₀) (h₁ : ∀ μ, F' t₀ μ = y₁) {t : ℝ} (ht : t₀ ≤ t) {R : ℝ}
    (hR : 0 < R) : DifferentiableOn ℂ (F t) (ball 0 R) ∧ DifferentiableOn ℂ (F' t) (ball 0 R) := by
  obtain ⟨f, f', hdiff, hsol⟩ :=
      exists_holomorphic_param_solution_Icc ht hR hp₀.continuousOn hp₁.continuousOn
    hq₀.continuousOn hq₁.continuousOn y₀ y₁
  have heq : ∀ μ ∈ ball (0 : ℂ) R, F t μ = f t μ ∧ F' t μ = f' t μ := by
    intro μ hμ
    obtain ⟨g0, g1, hg⟩ := hsol μ (ball_subset_closedBall hμ)
    have key := eqOn_Icc_of_linear_system (𝕜 := ℂ) (E := ℂ) (⟨le_rfl, ht⟩ : t₀ ∈ Icc t₀ t)
      (a₁₁ := fun _ => 0) (a₁₂ := fun _ => 1) (a₂₁ := fun s => q₀ s + μ * q₁ s)
      (a₂₂ := fun s => p₀ s + μ * p₁ s) continuousOn_const continuousOn_const
      (hq₀.add (continuous_const.mul hq₁)).continuousOn
      (hp₀.add (continuous_const.mul hp₁)).continuousOn
      (u := fun s => F s μ) (v := fun s => F' s μ) (u₁ := fun s => f s μ) (v₁ := fun s => f' s μ)
      (fun s _ => ⟨((hF μ s).1.hasDerivWithinAt).congr_deriv (by simp),
        ((hF μ s).2.hasDerivWithinAt).congr_deriv (by simp only [smul_eq_mul]; ring)⟩)
      (fun s hs => ⟨(hg s hs).1.congr_deriv (by simp),
        (hg s hs).2.congr_deriv (by simp only [smul_eq_mul]; ring)⟩)
      (by rw [h₀, g0]) (by rw [h₁, g1])
    exact ⟨key.1 ⟨ht, le_rfl⟩, key.2 ⟨ht, le_rfl⟩⟩
  exact ⟨(hdiff t).1.congr fun μ hμ => (heq μ hμ).1, (hdiff t).2.congr fun μ hμ => (heq μ hμ).2⟩

/-- **Holomorphic dependence on a parameter**: let `p₀, p₁, q₀, q₁ : ℝ → ℂ` be continuous and
let `F(·, λ)`, with derivative `F'(·, λ)`, solve
`y'' = (p₀ + λ p₁) y' + (q₀ + λ q₁) y` on `ℝ` for every `λ ∈ ℂ`, with data
`F(t₀, λ) = y₀`, `F'(t₀, λ) = y₁` independent of `λ`. Then for every `t` the functions
`λ ↦ F(t, λ)` and `λ ↦ F'(t, λ)` are entire. -/
theorem differentiable_param_of_linear_ode (hp₀ : Continuous p₀) (hp₁ : Continuous p₁)
    (hq₀ : Continuous q₀) (hq₁ : Continuous q₁) {t₀ : ℝ} {y₀ y₁ : ℂ} {F F' : ℝ → ℂ → ℂ}
    (hF : ∀ μ t, HasDerivAt (fun t => F t μ) (F' t μ) t ∧
      HasDerivAt (fun t => F' t μ) ((p₀ t + μ * p₁ t) * F' t μ + (q₀ t + μ * q₁ t) * F t μ) t)
    (h₀ : ∀ μ, F t₀ μ = y₀) (h₁ : ∀ μ, F' t₀ μ = y₁) (t : ℝ) :
    Differentiable ℂ (F t) ∧ Differentiable ℂ (F' t) := by
  suffices h : ∀ R, 0 < R → DifferentiableOn ℂ (F t) (ball 0 R) ∧
      DifferentiableOn ℂ (F' t) (ball 0 R) by
    refine ⟨fun μ => ?_, fun μ => ?_⟩
    · exact ((h (‖μ‖ + 1) (by positivity)).1 μ (by simp)).differentiableAt
        (isOpen_ball.mem_nhds (by simp))
    · exact ((h (‖μ‖ + 1) (by positivity)).2 μ (by simp)).differentiableAt
        (isOpen_ball.mem_nhds (by simp))
  intro R hR
  rcases le_total t₀ t with ht | ht
  · exact differentiableOn_param_of_le hp₀ hp₁ hq₀ hq₁ hF h₀ h₁ ht hR
  -- reflection `s ↦ -s`
  have hG : ∀ μ s, HasDerivAt (fun s => F (-s) μ) (-F' (-s) μ) s ∧
      HasDerivAt (fun s => -F' (-s) μ) ((-p₀ (-s) + μ * -p₁ (-s)) * -F' (-s) μ +
        (q₀ (-s) + μ * q₁ (-s)) * F (-s) μ) s := by
    intro μ s
    have k1 := (hF μ (-s)).1.scomp s (hasDerivAt_neg s)
    have k2 := ((hF μ (-s)).2.scomp s (hasDerivAt_neg s)).neg
    refine ⟨k1.congr_deriv (by simp), k2.congr_deriv (by rw [neg_one_smul]; ring)⟩
  have := differentiableOn_param_of_le (p₀ := fun s => -p₀ (-s)) (p₁ := fun s => -p₁ (-s))
    (q₀ := fun s => q₀ (-s)) (q₁ := fun s => q₁ (-s)) (hp₀.comp continuous_neg).neg
    (hp₁.comp continuous_neg).neg (hq₀.comp continuous_neg) (hq₁.comp continuous_neg)
    (F := fun s μ => F (-s) μ) (F' := fun s μ => -F' (-s) μ) (t₀ := -t₀) (y₀ := y₀) (y₁ := -y₁) hG
    (fun μ => by simp [h₀]) (fun μ => by simp [h₁]) (neg_le_neg ht) hR
  simp only [neg_neg] at this
  exact ⟨this.1, by simpa using this.2.neg⟩

end ODE

namespace ODE

/-- The radial retraction has norm at most its prescribed positive radius. -/
theorem norm_discRetract_le {R : ℝ} (hR : 0 < R) (z : ℂ) : ‖discRetract R hR z‖ ≤ R := by
  refine (BoundedContinuousFunction.norm_coe_le_norm _ z).trans ?_
  unfold discRetract
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hR.le _

/-- The radial retraction fixes every point in its closed disc. -/
theorem discRetract_apply_of_norm_le {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    discRetract R hR z = z :=
  discRetract_apply_of_mem_closedBall hR (mem_closedBall_zero_iff.mpr hz)

/-- The canonical bounded holomorphic subspace with its inherited multiplication and constants. -/
def boundedHolomorphicOnBallAlgebra (R : ℝ) : Subalgebra ℂ (ℂ →ᵇ ℂ) where
  carrier := boundedHolomorphicOnBall R
  zero_mem' := (boundedHolomorphicOnBall R).zero_mem
  add_mem' := (boundedHolomorphicOnBall R).add_mem
  one_mem' := one_mem_boundedHolomorphicOnBall R
  mul_mem' := mul_mem_boundedHolomorphicOnBall
  algebraMap_mem' c := differentiableOn_const c

/-- The algebra structure does not change the canonical subspace's membership predicate. -/
theorem mem_boundedHolomorphicOnBallAlgebra_iff (R : ℝ) (f : ℂ →ᵇ ℂ) :
    f ∈ boundedHolomorphicOnBallAlgebra R ↔ f ∈ boundedHolomorphicOnBall R := Iff.rfl

/-- The bounded holomorphic algebra is complete for the same supremum norm as its subspace. -/
instance boundedHolomorphicOnBallAlgebra.instCompleteSpace (R : ℝ) :
    CompleteSpace (boundedHolomorphicOnBallAlgebra R) :=
  inferInstanceAs (CompleteSpace (boundedHolomorphicOnBall R))

/-- A jointly continuous family on a closed disc, holomorphic in its interior, lifts
continuously to the bounded holomorphic Banach algebra without changing any disc values.
The parameter space is arbitrary. -/
theorem exists_continuous_boundedHolomorphicOnBallAlgebra
    {T : Type*} [TopologicalSpace T] {R : ℝ} (hR : 0 < R) {f : T → ℂ → ℂ}
    (hc : ContinuousOn (Function.uncurry f) (univ ×ˢ closedBall 0 R))
    (hd : ∀ t, DifferentiableOn ℂ (f t) (ball 0 R)) :
    ∃ F : T → boundedHolomorphicOnBallAlgebra R, Continuous F ∧
      ∀ t z, ‖z‖ ≤ R → (F t : ℂ →ᵇ ℂ) z = f t z := by
  let X := closedBall (0 : ℂ) R
  let retract : C(ℂ, X) := ⟨fun z => ⟨discRetract R hR z,
      mem_closedBall_zero_iff.mpr (norm_discRetract_le hR z)⟩,
    (discRetract R hR).continuous.subtype_mk _⟩
  have hf : Continuous (fun x : T × X => f x.1 x.2) := by
    have hm : Continuous (fun x : T × X => (x.1, (x.2 : ℂ))) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    exact hc.comp_continuous hm (fun x => ⟨mem_univ _, x.2.property⟩)
  let g : C(T × X, ℂ) := ⟨_, hf⟩
  let B : T → ℂ →ᵇ ℂ := fun t =>
    (BoundedContinuousFunction.mkOfCompact (g.curry t)).compContinuous retract
  -- Mathlib's compact-open exponential law gives norm-continuity of the slices.
  have hB : Continuous B :=
    (BoundedContinuousFunction.continuous_compContinuous retract).comp
      ((ContinuousMap.linearIsometryBoundedOfCompact X ℂ ℂ).continuous.comp g.curry.continuous)
  have heq (t : T) (z : ℂ) (hz : ‖z‖ ≤ R) : B t z = f t z := by
    change f t (discRetract R hR z) = f t z
    rw [discRetract_apply_of_norm_le hR hz]
  have hhol (t : T) : B t ∈ boundedHolomorphicOnBallAlgebra R := by
    refine (hd t).congr fun z hz => ?_
    exact heq t z (mem_ball_zero_iff.mp hz).le
  exact ⟨fun t => ⟨B t, hhol t⟩, hB.subtype_mk _, fun t z hz => heq t z hz⟩

end ODE
