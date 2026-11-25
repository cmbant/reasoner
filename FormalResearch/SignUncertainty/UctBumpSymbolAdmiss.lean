module

public import FormalResearch.SignUncertainty.UctBumpSymbol
public import FormalResearch.SignUncertainty.StripAdmissLift

/-!
# `uct:bump-symbol`: admissibility hypotheses (M1), (M2) of `ΔW_c(ζ) = c^{-1/3} B̂(cζ)` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:bump-symbol` ("`ΔW_c` satisfies the admissibility conditions of `uct:admiss`").
With `BumpProfile` and `bump_laplace_decay` of `UctBumpSymbol`:
* `bump_stripM1`: `StripM1` of `StripAdmissLift` (holomorphic on the open strip, continuous on the closed strip, real-symmetric, `(1+|τ|)^{-2}` decay; the constant depends on `c, δ, M`).
  Ingredients: holomorphy on `Re s > 0` and continuity on `Re s ≥ 0` of the Laplace transform of an integrable profile (`differentiableOn_laplace`, `continuousOn_laplace`).
* `bump_holder_one`: the Hölder bound at `ζ = 1` (exponent `1/2`, via a Cauchy estimate, in fact Lipschitz).
Not formalised: (M3) at `ζ = 0` (`StripEdge0` with `α = 1/2`: the boundary derivatives of `B̂(icτ)`, i.e. conditionally convergent Laplace transforms of `xB`, `x²B`, to be
handled by integrating by parts after damping and passing to the limit, as in the TeX), the density bounds and `(uct:E0-def)`.

Class: proved, no hypotheses.  Axiom guards are at the end.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

namespace BumpProfile

variable {b δ M α β : ℝ} {K : ℕ → ℝ} {B : ℝ → ℝ}

lemma integrable_self (h : BumpProfile b δ M α β K B) (hbδ : b * δ ≤ 1) (hβ : 1 < β) : Integrable B := by
  simpa using integrable_iteratedDeriv h hbδ hβ 0

lemma norm_exp_mul_le (h : BumpProfile b δ M α β K B) (hb0 : 0 ≤ b * δ) {s : ℂ} (hs : 0 ≤ s.re) (x : ℝ) :
    ‖Complex.exp (-s * (x : ℂ)) * (B x : ℂ)‖ ≤ ‖B x‖ := by
  rcases lt_or_ge x (b * δ) with hx | hx
  · rw [h.support x hx]; simp
  · rw [norm_mul, Complex.norm_exp, Complex.norm_real]
    have : (-s * (x : ℂ)).re ≤ 0 := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, neg_mul]
      nlinarith [mul_nonneg hs (hb0.trans hx)]
    calc Real.exp (-s * (x : ℂ)).re * ‖B x‖ ≤ 1 * ‖B x‖ := by gcongr; exact Real.exp_le_one_iff.mpr this
      _ = _ := one_mul _

lemma continuousOn_laplace (h : BumpProfile b δ M α β K B) (hb0 : 0 ≤ b * δ) (hbδ : b * δ ≤ 1) (hβ : 1 < β) :
    ContinuousOn (bumpLaplace B) {s : ℂ | 0 ≤ s.re} := by
  have hB := h.integrable_self hbδ hβ
  have hBc : Continuous B := by simpa using (h.contDiff_iteratedDeriv 0).continuous
  unfold bumpLaplace
  refine continuousOn_of_dominated (bound := fun x => ‖B x‖) (fun s _ => ?_) (fun s hs => ?_) hB.norm (ae_of_all _ fun x => ?_)
  · exact ((by fun_prop : Continuous fun x : ℝ => Complex.exp (-s * (x : ℂ))).mul
      (Complex.continuous_ofReal.comp hBc)).aestronglyMeasurable
  · exact ae_of_all _ fun x => h.norm_exp_mul_le hb0 hs x
  · exact (by fun_prop : Continuous fun s : ℂ => Complex.exp (-s * (x : ℂ)) * (B x : ℂ)).continuousOn

lemma differentiableOn_laplace (h : BumpProfile b δ M α β K B) (hb0 : 0 ≤ b * δ) (hbδ : b * δ ≤ 1) (hβ : 1 < β) :
    DifferentiableOn ℂ (bumpLaplace B) {s : ℂ | 0 < s.re} := by
  have hB := h.integrable_self hbδ hβ
  have hBc : Continuous B := by simpa using (h.contDiff_iteratedDeriv 0).continuous
  intro s₀ hs₀
  have ha : 0 < s₀.re / 2 := by have : 0 < s₀.re := hs₀; positivity
  set a := s₀.re / 2 with hadef
  have hball : ∀ s ∈ Metric.ball s₀ a, a ≤ s.re := by
    intro s hs
    have := Complex.abs_re_le_norm (s - s₀)
    simp only [Complex.sub_re] at this
    have h2 : ‖s - s₀‖ < a := by simpa [dist_eq_norm] using hs
    have := (abs_le.mp (this.trans h2.le)).1
    have : (0 : ℝ) < s₀.re := hs₀
    linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := s₀) (s := Metric.ball s₀ a)
    (F := fun s x => Complex.exp (-s * (x : ℂ)) * (B x : ℂ))
    (F' := fun s x => -(x : ℂ) * Complex.exp (-s * (x : ℂ)) * (B x : ℂ))
    (bound := fun x => a⁻¹ * ‖B x‖) (Metric.ball_mem_nhds s₀ ha)
    (Eventually.of_forall fun s => ((by fun_prop : Continuous fun x : ℝ => Complex.exp (-s * (x : ℂ))).mul
      (Complex.continuous_ofReal.comp hBc)).aestronglyMeasurable)
    (by
      refine (hB.norm.mono' ?_ (ae_of_all _ fun x => h.norm_exp_mul_le hb0 (by linarith [hball s₀ (Metric.mem_ball_self ha)] : 0 ≤ s₀.re) x))
      exact ((by fun_prop : Continuous fun x : ℝ => Complex.exp (-s₀ * (x : ℂ))).mul (Complex.continuous_ofReal.comp hBc)).aestronglyMeasurable)
    (((by fun_prop : Continuous fun x : ℝ => -(x : ℂ) * Complex.exp (-s₀ * (x : ℂ))).mul
      (Complex.continuous_ofReal.comp hBc)).aestronglyMeasurable)
    (ae_of_all _ fun x s hs => by
      have hsa := hball s hs
      rcases lt_or_ge x (b * δ) with hx | hx
      · rw [h.support x hx]; simp
      · have hx0 : 0 ≤ x := hb0.trans hx
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_exp, Real.norm_eq_abs, abs_of_nonneg hx0, Complex.norm_real]
        have e1 : (-s * (x : ℂ)).re = -(s.re * x) := by
          simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, neg_mul]
        rw [e1]
        have e2 : x * Real.exp (-(s.re * x)) ≤ a⁻¹ := by
          have h3 : Real.exp (-(s.re * x)) ≤ Real.exp (-(a * x)) := Real.exp_le_exp.mpr (by nlinarith)
          have h4 : a * x ≤ Real.exp (a * x) := by linarith [Real.add_one_le_exp (a * x)]
          have h5 : x * Real.exp (-(a * x)) ≤ a⁻¹ := by
            rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _), inv_mul_eq_div, le_div_iff₀ ha]
            nlinarith
          exact (mul_le_mul_of_nonneg_left h3 hx0).trans h5
        calc x * Real.exp (-(s.re * x)) * ‖B x‖ ≤ a⁻¹ * ‖B x‖ := mul_le_mul_of_nonneg_right e2 (norm_nonneg _)
          _ = _ := rfl)
    (hB.norm.const_mul a⁻¹)
    (ae_of_all _ fun x s _ => by
      have h1 : HasDerivAt (fun s : ℂ => -s * (x : ℂ)) (-(x : ℂ)) s := by
        simpa using (hasDerivAt_id s).neg.mul_const (x : ℂ)
      exact (h1.cexp.mul_const (B x : ℂ)).congr_deriv (by ring))
  exact key.2.differentiableAt.differentiableWithinAt

lemma laplace_conj (s : ℂ) :
    bumpLaplace B (starRingEnd ℂ s) = starRingEnd ℂ (bumpLaplace B s) := by
  unfold bumpLaplace
  rw [← integral_conj]
  congr 1; funext x
  rw [map_mul, ← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_ofReal]

end BumpProfile

/-- **`uct:bump-symbol`, (M1) for `ΔW_c(ζ) = c^{-1/3} B̂(cζ)`**: holomorphic on `0 < Re ζ < 1`, continuous on `0 ≤ Re ζ ≤ 1`, real-symmetric, and
`|ΔW_c(σ+iτ)| ≤ C (1+|τ|)^{-2}` there (`C` depending on `c, δ, M`, as allowed in the TeX); i.e. the hypothesis `StripM1` of `uct:admiss`. -/
theorem bump_stripM1 {b α β : ℝ} (hb : 0 < b) (hβ : 3 / 2 ≤ β) (K : ℕ → ℝ) {B : ℝ → ℝ} {δ M c : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hbδ : b * δ ≤ 1) (hM : 0 ≤ M) (hc : 0 < c) (h : BumpProfile b δ M α β K B) :
    StripM1 (fun ζ : ℂ => ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * bumpLaplace B ((c : ℂ) * ζ)) := by
  have hb0 : 0 ≤ b * δ := by positivity
  have hβ1 : 1 < β := by linarith
  have hc3 : 0 < c ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc _
  have hmapre : ∀ ζ : ℂ, ((c : ℂ) * ζ).re = c * ζ.re := fun ζ => by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine DifferentiableOn.const_mul (((h.differentiableOn_laplace hb0 hbδ hβ1).comp (differentiableOn_const _ |>.mul differentiableOn_id)
      (fun ζ hζ => ?_))) _
    show 0 < ((c : ℂ) * ζ).re
    rw [hmapre]; exact mul_pos hc hζ.1
  · refine ContinuousOn.mul continuousOn_const ((h.continuousOn_laplace hb0 hbδ hβ1).comp (continuousOn_const.mul continuousOn_id) (fun ζ hζ => ?_))
    show 0 ≤ ((c : ℂ) * ζ).re
    rw [hmapre]; exact mul_nonneg hc.le hζ.1
  · intro ζ _ _
    rw [map_mul, Complex.conj_ofReal, ← BumpProfile.laplace_conj, map_mul, Complex.conj_ofReal]
  · obtain ⟨C, hC0, hC⟩ := bump_laplace_decay (α := α) hb hβ K 2
    set Λ := bumpLambda α δ
    have hΛ := one_le_bumpLambda (α := α) hδ0 hδ1
    set m : ℝ := max 1 (1 / (c * δ)) with hm
    have hm1 : 1 ≤ m := le_max_left _ _
    refine ⟨c ^ (-(1 / 3 : ℝ)) * (C * M * Λ * m ^ 2), fun ζ hζ0 hζ1 => ?_⟩
    have hζ : ζ = (ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I := (Complex.re_add_im ζ).symm
    have hd := hC B δ M c ζ.re ζ.im hδ0 hδ1 hbδ hM hc hζ0 h
    rw [← hζ] at hd
    have hE : Real.exp (-(b * c * ζ.re * δ)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have : 0 ≤ b * c * ζ.re * δ := by positivity
      linarith)
    set X := c * δ * |ζ.im| with hX
    have hX0 : 0 ≤ X := by positivity
    have hcd : 0 < c * δ := by positivity
    have hmX : 1 + |ζ.im| ≤ m * (1 + X) := by
      rcases le_total 1 (c * δ) with h1 | h1
      · have : m = 1 := by rw [hm]; exact max_eq_left (by rw [div_le_one hcd]; exact h1)
        rw [this, hX]; nlinarith [abs_nonneg ζ.im]
      · have : m = 1 / (c * δ) := by rw [hm]; exact max_eq_right (by rw [le_div_iff₀ hcd]; linarith)
        rw [this, hX, div_mul_eq_mul_div, one_mul, le_div_iff₀ hcd]
        nlinarith [abs_nonneg ζ.im]
    have hp : 0 < 1 + |ζ.im| := by positivity
    have hq : 0 < (1 + X) ^ 2 := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc3, Real.rpow_neg hp.le, Real.rpow_two]
    have h2 : ‖bumpLaplace B ((c : ℂ) * ζ)‖ ≤ C * M * Λ * m ^ 2 / (1 + |ζ.im|) ^ 2 := by
      refine hd.trans ?_
      have h3 : (1 + |ζ.im|) ^ 2 ≤ m ^ 2 * (1 + X) ^ 2 := by rw [← mul_pow]; exact pow_le_pow_left₀ hp.le hmX 2
      have hCMΛ : 0 ≤ C * M * Λ := by positivity
      calc C * M * Λ * Real.exp (-(b * c * ζ.re * δ)) / (1 + X) ^ 2 ≤ C * M * Λ * 1 / (1 + X) ^ 2 := by gcongr
        _ = C * M * Λ / (1 + X) ^ 2 := by rw [mul_one]
        _ ≤ C * M * Λ * m ^ 2 / (1 + |ζ.im|) ^ 2 := by
            rw [div_le_div_iff₀ hq (by positivity)]
            nlinarith [mul_le_mul_of_nonneg_left h3 hCMΛ]
    calc c ^ (-(1 / 3 : ℝ)) * ‖bumpLaplace B ((c : ℂ) * ζ)‖ ≤ c ^ (-(1 / 3 : ℝ)) * (C * M * Λ * m ^ 2 / (1 + |ζ.im|) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 hc3.le
      _ = _ := by rw [mul_div_assoc', ← mul_assoc]; ring


/-- **`uct:bump-symbol`, (M2) at `ζ = 1`** (Hölder exponent `1/2`; in fact Lipschitz, by a Cauchy estimate): for `0 ≤ Re ζ ≤ 1`, `‖1 - ζ‖ ≤ 1/2`,
`‖ΔW_c(ζ) - ΔW_c(1)‖ ≤ C ‖1 - ζ‖^{1/2}`. -/
theorem bump_holder_one {b α β : ℝ} (hb : 0 < b) (hβ : 3 / 2 ≤ β) (K : ℕ → ℝ) {B : ℝ → ℝ} {δ M c : ℝ} (hδ0 : 0 < δ) (hbδ : b * δ ≤ 1)
    (hc : 0 < c) (h : BumpProfile b δ M α β K B) :
    ∃ CH : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖1 - ζ‖ ≤ 1 / 2 →
      ‖(fun ζ : ℂ => ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * bumpLaplace B ((c : ℂ) * ζ)) ζ -
        (fun ζ : ℂ => ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * bumpLaplace B ((c : ℂ) * ζ)) 1‖ ≤ CH * ‖1 - ζ‖ ^ (1 / 2 : ℝ) := by
  have hb0 : 0 ≤ b * δ := by positivity
  have hβ1 : 1 < β := by linarith
  have hc3 : 0 < c ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc _
  set W : ℂ → ℂ := fun ζ => ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * bumpLaplace B ((c : ℂ) * ζ) with hW
  have hmapre : ∀ ζ : ℂ, ((c : ℂ) * ζ).re = c * ζ.re := fun ζ => by simp
  have hdiff : DifferentiableOn ℂ W {ζ : ℂ | 0 < ζ.re} := by
    refine DifferentiableOn.const_mul (((h.differentiableOn_laplace hb0 hbδ hβ1).comp (differentiableOn_const _ |>.mul differentiableOn_id)
      (fun ζ hζ => ?_))) _
    show 0 < ((c : ℂ) * ζ).re
    rw [hmapre]; exact mul_pos hc hζ
  set B1 : ℝ := c ^ (-(1 / 3 : ℝ)) * ∫ x : ℝ, ‖B x‖ with hB1
  have hB10 : 0 ≤ B1 := by positivity
  have hbound : ∀ ζ : ℂ, 0 ≤ ζ.re → ‖W ζ‖ ≤ B1 := by
    intro ζ hζ
    have hs : 0 ≤ ((c : ℂ) * ζ).re := by rw [hmapre]; positivity
    have h1 : ‖bumpLaplace B ((c : ℂ) * ζ)‖ ≤ ∫ x : ℝ, ‖B x‖ := by
      unfold bumpLaplace
      exact norm_integral_le_of_norm_le (h.integrable_self hbδ hβ1).norm (ae_of_all _ fun x => h.norm_exp_mul_le hb0 hs x)
    rw [hW]; dsimp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc3]
    exact mul_le_mul_of_nonneg_left h1 hc3.le
  refine ⟨4 * B1, fun ζ hζ0 hζ1 hζ => ?_⟩
  have hre : ∀ z : ℂ, ‖z - 1‖ ≤ 1 / 2 → 1 / 2 ≤ z.re := by
    intro z hz
    have := Complex.abs_re_le_norm (z - 1)
    simp only [Complex.sub_re, Complex.one_re] at this
    have := (abs_le.mp (this.trans hz)).1
    linarith
  have hderiv : ∀ z ∈ Metric.closedBall (1 : ℂ) (1 / 2), ‖deriv W z‖ ≤ 4 * B1 := by
    intro z hz
    have hz' : ‖z - 1‖ ≤ 1 / 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hsub : Metric.closedBall z (1 / 4) ⊆ {ζ : ℂ | 0 < ζ.re} := by
      intro w hw
      have hw' : ‖w - z‖ ≤ 1 / 4 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
      have h1 := Complex.abs_re_le_norm (w - z)
      simp only [Complex.sub_re] at h1
      have := (abs_le.mp (h1.trans hw')).1
      have := hre z hz'
      show 0 < w.re
      linarith
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := 1 / 4) (C := B1) (f := W) (by norm_num)
      (hdiff.diffContOnCl_ball hsub) (fun w hw => by
        have hw' : ‖w - z‖ = 1 / 4 := by simpa [Metric.mem_sphere, dist_eq_norm] using hw
        have h1 := Complex.abs_re_le_norm (w - z)
        simp only [Complex.sub_re] at h1
        have := (abs_le.mp (h1.trans hw'.le)).1
        have := hre z hz'
        exact hbound w (by linarith))
    calc ‖deriv W z‖ ≤ B1 / (1 / 4) := this
      _ = 4 * B1 := by ring
  have hmem : ζ ∈ Metric.closedBall (1 : ℂ) (1 / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm, ← norm_neg]; simpa using hζ
  have hdiffat : ∀ z ∈ Metric.closedBall (1 : ℂ) (1 / 2), DifferentiableAt ℂ W z := by
    intro z hz
    have hz' : ‖z - 1‖ ≤ 1 / 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have : 0 < z.re := by linarith [hre z hz']
    exact (hdiff z this).differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds this)
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := W) (s := Metric.closedBall (1 : ℂ) (1 / 2)) (C := 4 * B1) (x := 1) (y := ζ)
    hdiffat hderiv (convex_closedBall _ _) (Metric.mem_closedBall_self (by norm_num)) hmem
  have hnn : ‖ζ - 1‖ = ‖1 - ζ‖ := norm_sub_rev _ _
  rw [norm_sub_rev] at hmv
  rw [hnn] at hmv
  show ‖W ζ - W 1‖ ≤ 4 * B1 * ‖1 - ζ‖ ^ (1 / 2 : ℝ)
  have hn0 : 0 ≤ ‖1 - ζ‖ := norm_nonneg _
  have h12 : ‖1 - ζ‖ ≤ ‖1 - ζ‖ ^ (1 / 2 : ℝ) := by
    rcases hn0.eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · have : ‖1 - ζ‖ ^ (1 / 2 : ℝ) * ‖1 - ζ‖ ^ (1 / 2 : ℝ) = ‖1 - ζ‖ := by
        rw [← Real.rpow_add h0]; norm_num
      have hle : ‖1 - ζ‖ ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hn0 (by linarith) (by norm_num)
      nlinarith [Real.rpow_nonneg hn0 (1 / 2 : ℝ)]
  calc ‖W ζ - W 1‖ ≤ 4 * B1 * ‖1 - ζ‖ := by
        rw [norm_sub_rev] at hmv; exact hmv
    _ ≤ 4 * B1 * ‖1 - ζ‖ ^ (1 / 2 : ℝ) := by gcongr

/-- info: 'FormalResearch.SignUncertainty.bump_stripM1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_stripM1

/-- info: 'FormalResearch.SignUncertainty.bump_holder_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_holder_one

end FormalResearch.SignUncertainty
