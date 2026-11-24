module

public import FormalResearch.SignUncertainty.MiddleBandSymbolDiff
public import FormalResearch.CohnElkies.CubicNormalFormBridge
public import Mathlib.Analysis.Complex.Liouville

/-!
# GT.2a: Taylor-type bounds for the normal-form map `τ` of `O.4`

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `cegt:GT2a`, inner difference (inputs of `(e7)`, `(e8)`).

For `τ` with `O4NormalForm L τ` (`L ∈ (0, 0.002]`, so `τ` is holomorphic on `D(0, 0.22)`, `|τ| < 0.45`, odd, `τ'(0) = κ₀(L)`) the real-axis
bounds, for real `|θ| ≤ 0.18`,
`|τ(θ) - κ₀θ| ≤ C|θ|³`, `|τ'(θ) - κ₀| ≤ Cθ²`, `|τ''(θ)| ≤ C|θ|`
follow from the Cauchy estimate for `τ'''` and three mean value steps from `τ(0) = 0`, `τ'(0) = κ₀`, `τ''(0) = 0`.

* `cauchy_iterDeriv_bound`: Cauchy estimate `‖F^{(n)}(x)‖ ≤ n! M / ρ^n` on a disc.
* `tau_taylor_bounds`: the three bounds above, with an absolute constant.

Status: proved, unconditional given `O4NormalForm L τ` (itself conditional on `O4QuotientBound L`).  Not formalised here: the amplitude
`P(u)` and the reparametrisation hypotheses of `symbol_diff_bounds` (the next modules).
-/

@[expose] public section

open Metric Set Filter Topology Complex Function
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- Cauchy estimate for a holomorphic function on a disc `D(0, R)` bounded by `M`, at a point `x` with `‖x‖ + ρ < R`. -/
theorem cauchy_iterDeriv_bound {F : ℂ → ℂ} {R M ρ : ℝ} (hρ : 0 < ρ) (hF : DifferentiableOn ℂ F (ball 0 R))
    (hM : ∀ z ∈ ball (0 : ℂ) R, ‖F z‖ ≤ M) {x : ℂ} (hx : ‖x‖ + ρ < R) (n : ℕ) :
    ‖iteratedDeriv n F x‖ ≤ n.factorial * M / ρ ^ n := by
  have hsub : closedBall x ρ ⊆ ball (0 : ℂ) R := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_ball_zero_iff]
    calc ‖w‖ = ‖(w - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - x‖ + ‖x‖ := norm_add_le _ _
      _ < R := by linarith
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hρ (hF.diffContOnCl_ball hsub)
    fun w hw => hM w (hsub (sphere_subset_closedBall hw))

/-- Mean value bound from the origin: `‖f θ - f 0‖ ≤ B |θ|` if `‖f'‖ ≤ B` between `0` and `θ`. -/
lemma mvt_from_origin {f f' : ℝ → ℂ} {θ B : ℝ} (hf : ∀ s ∈ uIcc 0 θ, HasDerivAt f (f' s) s)
    (hB : ∀ s ∈ uIcc 0 θ, ‖f' s‖ ≤ B) : ‖f θ - f 0‖ ≤ B * |θ| := by
  have := (convex_uIcc 0 θ).norm_image_sub_le_of_norm_hasDerivWithin_le (f := f) (f' := f') (C := B)
    (fun x hx => (hf x hx).hasDerivWithinAt) hB left_mem_uIcc right_mem_uIcc
  simpa [Real.norm_eq_abs] using this

section

variable {L : ℝ} {τ : ℂ → ℂ}

/-- The complex derivative of a holomorphic function on a disc is holomorphic there. -/
lemma differentiableOn_deriv_ball {F : ℂ → ℂ} {R : ℝ} (hF : DifferentiableOn ℂ F (ball 0 R)) :
    DifferentiableOn ℂ (deriv F) (ball 0 R) :=
  (hF.analyticOnNhd isOpen_ball).deriv.differentiableOn

/-- A holomorphic `F` on the disc, restricted to real points, has the real derivative `deriv F`. -/
lemma hasDerivAt_real_of_ball {F : ℂ → ℂ} {R : ℝ} (hF : DifferentiableOn ℂ F (ball 0 R)) {x : ℝ} (hx : |x| < R) :
    HasDerivAt (fun y : ℝ => F (y : ℂ)) (deriv F (x : ℂ)) x := by
  have hm : (x : ℂ) ∈ ball (0 : ℂ) R := by simpa [Complex.norm_real] using hx
  have := (hF.differentiableAt (isOpen_ball.mem_nhds hm)).hasDerivAt
  exact this.comp_ofReal

/-- `F'' (0) = 0` for an odd holomorphic `F` on a disc. -/
lemma deriv_deriv_zero_of_odd {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hF : DifferentiableOn ℂ F (ball 0 R))
    (hodd : ∀ θ ∈ ball (0 : ℂ) R, F (-θ) = -F θ) : deriv (deriv F) 0 = 0 := by
  have hF1 : ∀ θ ∈ ball (0 : ℂ) R, deriv F (-θ) = deriv F θ := by
    intro θ hθ
    have hθ' : -θ ∈ ball (0 : ℂ) R := by simpa using hθ
    have h1 : HasDerivAt (fun z => F (-z)) (deriv F (-θ) * (-1)) θ :=
      HasDerivAt.comp θ (hF.differentiableAt (isOpen_ball.mem_nhds hθ')).hasDerivAt (hasDerivAt_neg θ)
    have h2 : HasDerivAt (fun z => F (-z)) (-deriv F θ) θ := by
      have := (hF.differentiableAt (isOpen_ball.mem_nhds hθ)).hasDerivAt.neg
      refine this.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ball.mem_nhds hθ] with z hz using hodd z hz
    have := h1.unique h2
    linear_combination -this
  have hF2 : DifferentiableOn ℂ (deriv F) (ball 0 R) := differentiableOn_deriv_ball hF
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := by simpa using hR
  have h0' : (-0 : ℂ) ∈ ball (0 : ℂ) R := by simpa using h0
  have h1 : HasDerivAt (fun z => deriv F (-z)) (deriv (deriv F) (-0) * (-1)) 0 :=
    HasDerivAt.comp 0 (hF2.differentiableAt (isOpen_ball.mem_nhds h0')).hasDerivAt (hasDerivAt_neg 0)
  have h2 : HasDerivAt (fun z => deriv F (-z)) (deriv (deriv F) 0) 0 := by
    have := (hF2.differentiableAt (isOpen_ball.mem_nhds h0)).hasDerivAt
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds h0] with z hz using hF1 z hz
  have := h1.unique h2
  simp only [neg_zero] at this
  linear_combination (-(1 : ℂ) / 2) * this

/-- Third derivative bound `‖τ'''(x)‖ ≤ 50000` at real `|x| ≤ 0.18` (Cauchy estimate on `D(x, 0.039) ⊂ D(0, 0.22)`). -/
theorem tau_third_deriv_bound (h : O4NormalForm L τ) :
    ∀ x : ℝ, |x| ≤ 0.18 → ‖deriv (deriv (deriv τ)) (x : ℂ)‖ ≤ 50000 := by
  have hτd := h.differentiableOn
  have hbd : ∀ z ∈ ball (0 : ℂ) 0.22, ‖τ z‖ ≤ 0.45 := fun z hz => (h.norm_lt z hz).le
  intro x hx
  have hx' : ‖(x : ℂ)‖ + 0.039 < 0.22 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  have := cauchy_iterDeriv_bound (by norm_num : (0 : ℝ) < 0.039) hτd hbd hx' 3
  have e3 : iteratedDeriv 3 τ (x : ℂ) = deriv (deriv (deriv τ)) (x : ℂ) := by
    simp [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [e3] at this
  refine this.trans ?_
  norm_num [Nat.factorial]

/-- **Taylor bounds for `τ` on the real axis** (`|θ| ≤ 0.18`): `|τ(θ) - κ₀θ| ≤ C|θ|³`, `|τ'(θ) - κ₀| ≤ Cθ²`, `|τ''(θ)| ≤ C|θ|`,
with `κ₀ = edgeKappa0 L` and `C = 50000`. -/
theorem tau_taylor_bounds (h : O4NormalForm L τ) {θ : ℝ} (hθ : |θ| ≤ 0.18) :
    ‖τ (θ : ℂ) - (edgeKappa0 L : ℂ) * θ‖ ≤ 50000 * |θ| ^ 3 ∧
    ‖deriv τ (θ : ℂ) - (edgeKappa0 L : ℂ)‖ ≤ 50000 * θ ^ 2 ∧
    ‖deriv (deriv τ) (θ : ℂ)‖ ≤ 50000 * |θ| := by
  have hτd := h.differentiableOn
  have hτ1 := differentiableOn_deriv_ball hτd
  have hτ2 := differentiableOn_deriv_ball hτ1
  have hbd : ∀ z ∈ ball (0 : ℂ) 0.22, ‖τ z‖ ≤ 0.45 := fun z hz => (h.norm_lt z hz).le
  have h3 := tau_third_deriv_bound h
  have hlt : ∀ s : ℝ, |s| ≤ 0.18 → |s| < 0.22 := fun s hs => by linarith
  have hs_abs : ∀ s ∈ uIcc 0 θ, |s| ≤ |θ| := fun s hs => by
    rw [mem_uIcc] at hs
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
    · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith
  have hs_le : ∀ s ∈ uIcc 0 θ, |s| ≤ 0.18 := fun s hs => (hs_abs s hs).trans hθ
  have hz2 : deriv (deriv τ) 0 = 0 := deriv_deriv_zero_of_odd (by norm_num) hτd h.odd
  have hz1 : deriv τ 0 = (edgeKappa0 L : ℂ) := h.hasDerivAt_zero.deriv
  have hz0 : τ 0 = 0 := h.zero
  -- step 1: `‖τ''(x)‖ ≤ 50000 |x|`
  have step1 : ∀ x : ℝ, |x| ≤ 0.18 → ‖deriv (deriv τ) (x : ℂ)‖ ≤ 50000 * |x| := by
    intro x hx
    have hxs : ∀ s ∈ uIcc 0 x, |s| ≤ |x| := fun s hs => by
      rw [mem_uIcc] at hs
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
      · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith
    have := mvt_from_origin (f := fun y : ℝ => deriv (deriv τ) (y : ℂ)) (f' := fun y => deriv (deriv (deriv τ)) (y : ℂ))
      (θ := x) (B := 50000)
      (fun s hs => hasDerivAt_real_of_ball hτ2 (hlt s ((hxs s hs).trans hx))) (fun s hs => h3 s ((hxs s hs).trans hx))
    simpa [hz2] using this
  have step2 : ∀ x : ℝ, |x| ≤ 0.18 → ‖deriv τ (x : ℂ) - (edgeKappa0 L : ℂ)‖ ≤ 50000 * x ^ 2 := by
    intro x hx
    have hxs : ∀ s ∈ uIcc 0 x, |s| ≤ |x| := fun s hs => by
      rw [mem_uIcc] at hs
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]; exact h2
      · rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]; linarith
    have := mvt_from_origin (f := fun y : ℝ => deriv τ (y : ℂ) - (edgeKappa0 L : ℂ))
      (f' := fun y => deriv (deriv τ) (y : ℂ)) (θ := x) (B := 50000 * |x|)
      (fun s hs => (hasDerivAt_real_of_ball hτ1 (hlt s ((hxs s hs).trans hx))).sub_const _)
      (fun s hs => (step1 s ((hxs s hs).trans hx)).trans (by
        have := hxs s hs; nlinarith [this]))
    simp only [Complex.ofReal_zero, hz1, sub_self, sub_zero] at this
    calc _ ≤ 50000 * |x| * |x| := this
      _ = 50000 * x ^ 2 := by rw [mul_assoc, ← sq, sq_abs]
  refine ⟨?_, step2 θ hθ, step1 θ hθ⟩
  have hxs : ∀ s ∈ uIcc 0 θ, |s| ≤ |θ| := hs_abs
  have := mvt_from_origin (f := fun y : ℝ => τ (y : ℂ) - (edgeKappa0 L : ℂ) * (y : ℂ))
    (f' := fun y => deriv τ (y : ℂ) - (edgeKappa0 L : ℂ)) (θ := θ) (B := 50000 * θ ^ 2)
    (fun s hs => by
      have h1 := hasDerivAt_real_of_ball hτd (hlt s (hs_le s hs))
      have h2 : HasDerivAt (fun y : ℝ => (edgeKappa0 L : ℂ) * (y : ℂ)) (edgeKappa0 L : ℂ) s := by
        simpa using ((hasDerivAt_id s).ofReal_comp).const_mul (edgeKappa0 L : ℂ)
      exact h1.sub h2)
    (fun s hs => (step2 s (hs_le s hs)).trans (by
      have := hxs s hs
      have h2 : s ^ 2 ≤ θ ^ 2 := by rw [← sq_abs s, ← sq_abs θ]; exact pow_le_pow_left₀ (abs_nonneg s) this 2
      linarith))
  simp only [Complex.ofReal_zero, hz0, mul_zero, sub_zero] at this
  calc _ ≤ 50000 * θ ^ 2 * |θ| := this
    _ = 50000 * |θ| ^ 3 := by rw [← sq_abs θ]; ring

end

/-- info: 'FormalResearch.SignUncertainty.cauchy_iterDeriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.cauchy_iterDeriv_bound

/-- info: 'FormalResearch.SignUncertainty.tau_third_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.tau_third_deriv_bound

/-- info: 'FormalResearch.SignUncertainty.tau_taylor_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.tau_taylor_bounds

end FormalResearch.SignUncertainty
