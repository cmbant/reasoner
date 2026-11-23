module

public import FormalResearch.SignUncertainty.MellinStrip
public import FormalResearch.CohnElkies.VerticalStripShift

/-!
# `O.11ak`, Mellin side: the inverse Mellin lift of a strip multiplier

Source: `CFT/sign_uncertainty/paper/u1c_o1_upper.tex`, Theorem `O.11ak` (`ceo:O11ak`), Proof 1 (Mellin inversion).  Abstract version: a
function `Φ` (the paper's `(2π)^{-z} Γ(z) 𝓜_σ(z)`) holomorphic on `0 < Re z < c`, bounded by `B (1 + |Im z|)^{-2}` on every closed
sub-strip and real (`Φ(z̄) = conj Φ(z)`) has an inverse Mellin lift `f = mellinInv x Φ` which

* does not depend on the line `Re z = x ∈ (0, c)` (`mellinInv_indep`, Cauchy rectangle `strip_shift`),
* is real, continuous on `(0, ∞)` and bounded by `C_x Δ^{-x}` (`liftFun_*`),
* has Mellin transform `Φ` on the open strip (`mellinRaw_liftFun`, Fourier inversion).

Status: proved, unconditional.  Not formalised here: behaviour at `Δ → 0` and `Δ → ∞` beyond the power bound (the tail
`f ρ₀ ∈ L¹` and the Hankel eigen-identity are in `MellinLiftEigen`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- Hypotheses on a Mellin multiplier `Φ` on the strip `0 < Re z < c`. -/
structure MellinLiftData (c : ℝ) (Φ : ℂ → ℂ) : Prop where
  hol : DifferentiableOn ℂ Φ {z : ℂ | 0 < z.re ∧ z.re < c}
  decay : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < c →
    ∃ B : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖Φ z‖ ≤ B * (1 + |z.im|) ^ (-2 : ℝ)
  real : ∀ z : ℂ, 0 < z.re → z.re < c → Φ (starRingEnd ℂ z) = starRingEnd ℂ (Φ z)

section

variable {c : ℝ} {Φ : ℂ → ℂ}

lemma integrable_weight_two (B : ℝ) : Integrable (fun v : ℝ => B * (1 + |v|) ^ (-2 : ℝ)) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
  simpa using this.const_mul B

lemma tendsto_weight_two_atTop (B : ℝ) :
    Tendsto (fun v : ℝ => B * (1 + |v|) ^ (-2 : ℝ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun v : ℝ => 1 + |v|) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_abs_atTop_atTop
  have := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp h1).const_mul B
  simpa using this

lemma tendsto_weight_two_atBot (B : ℝ) :
    Tendsto (fun v : ℝ => B * (1 + |v|) ^ (-2 : ℝ)) atBot (𝓝 0) := by
  have h1 : Tendsto (fun v : ℝ => 1 + |v|) atBot atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_abs_atBot_atTop
  have := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp h1).const_mul B
  simpa using this

lemma norm_cpow_line {Δ : ℝ} (hΔ : 0 < Δ) (x y : ℝ) :
    ‖(Δ : ℂ) ^ (-((x : ℂ) + (y : ℂ) * Complex.I))‖ = Δ ^ (-x) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hΔ]
  simp

lemma MellinLiftData.continuousOn (h : MellinLiftData c Φ) :
    ContinuousOn Φ {z : ℂ | 0 < z.re ∧ z.re < c} := h.hol.continuousOn

lemma continuous_line (h : MellinLiftData c Φ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < c) :
    Continuous fun y : ℝ => Φ ((x : ℂ) + (y : ℂ) * Complex.I) :=
  h.continuousOn.comp_continuous (by fun_prop) fun y => by simpa using ⟨hx0, hx1⟩

lemma MellinLiftData.line_bound (h : MellinLiftData c Φ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < c) :
    ∃ B : ℝ, ∀ y : ℝ, ‖Φ ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ B * (1 + |y|) ^ (-2 : ℝ) := by
  obtain ⟨B, hB⟩ := h.decay hx0 le_rfl hx1
  exact ⟨B, fun y => by simpa using hB ((x : ℂ) + (y : ℂ) * Complex.I) (by simp) (by simp)⟩

lemma MellinLiftData.integrable_line (h : MellinLiftData c Φ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < c) :
    Integrable fun y : ℝ => Φ ((x : ℂ) + (y : ℂ) * Complex.I) := by
  obtain ⟨B, hB⟩ := h.line_bound hx0 hx1
  exact (integrable_weight_two B).mono' (continuous_line h hx0 hx1).aestronglyMeasurable
    (ae_of_all _ hB)

lemma MellinLiftData.integrable_line_cpow (h : MellinLiftData c Φ) {x Δ : ℝ} (hx0 : 0 < x)
    (hx1 : x < c) (hΔ : 0 < Δ) :
    Integrable fun y : ℝ => (Δ : ℂ) ^ (-((x : ℂ) + (y : ℂ) * Complex.I)) • Φ ((x : ℂ) + (y : ℂ) * Complex.I) := by
  obtain ⟨B, hB⟩ := h.line_bound hx0 hx1
  have hcont : Continuous fun y : ℝ => (Δ : ℂ) ^ (-((x : ℂ) + (y : ℂ) * Complex.I)) • Φ ((x : ℂ) + (y : ℂ) * Complex.I) :=
    (Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hΔ.ne'))).smul (continuous_line h hx0 hx1)
  refine (integrable_weight_two (Δ ^ (-x) * B)).mono' hcont.aestronglyMeasurable (ae_of_all _ fun y => ?_)
  rw [norm_smul, norm_cpow_line hΔ]
  calc Δ ^ (-x) * ‖Φ ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Δ ^ (-x) * (B * (1 + |y|) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hB y) (Real.rpow_nonneg hΔ.le _)
    _ = _ := by ring


lemma rpow_neg_le_sum {Δ x x' t : ℝ} (hΔ : 0 < Δ) (h1 : x ≤ t) (h2 : t ≤ x') :
    Δ ^ (-t) ≤ Δ ^ (-x) + Δ ^ (-x') := by
  have p1 : 0 ≤ Δ ^ (-x) := Real.rpow_nonneg hΔ.le _
  have p2 : 0 ≤ Δ ^ (-x') := Real.rpow_nonneg hΔ.le _
  rcases le_total 1 Δ with hd | hd
  · have := Real.rpow_le_rpow_of_exponent_le hd (by linarith : -t ≤ -x)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hΔ hd (by linarith : -x' ≤ -t)
    linarith

/-- The inverse Mellin integral does not depend on the line `Re z = x ∈ (0, c)`. -/
theorem MellinLiftData.mellinInv_indep (h : MellinLiftData c Φ) {x x' : ℝ} (hx0 : 0 < x) (hx1 : x < c)
    (hx0' : 0 < x') (hx1' : x' < c) {Δ : ℝ} (hΔ : 0 < Δ) :
    mellinInv x Φ Δ = mellinInv x' Φ Δ := by
  wlog hxx : x ≤ x' generalizing x x'
  · exact (this hx0' hx1' hx0 hx1 (le_of_not_ge hxx)).symm
  obtain ⟨B, hB⟩ := h.decay hx0 hxx hx1'
  set H : ℂ → ℂ := fun z => (Δ : ℂ) ^ (-z) • Φ z with hH
  have hΔ0 : (Δ : ℂ) ≠ 0 := by exact_mod_cast hΔ.ne'
  have hsub : {w : ℂ | x ≤ w.re ∧ w.re ≤ x'} ⊆ {z : ℂ | 0 < z.re ∧ z.re < c} := fun w hw =>
    ⟨by have := hw.1; simp only [Set.mem_ofPred_eq] at hw ⊢; linarith [hw.1], by linarith [hw.2]⟩
  have hsub' : {w : ℂ | x < w.re ∧ w.re < x'} ⊆ {z : ℂ | 0 < z.re ∧ z.re < c} := fun w hw =>
    ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hcont : ContinuousOn H {w : ℂ | x ≤ w.re ∧ w.re ≤ x'} :=
    (Continuous.const_cpow continuous_neg (Or.inl hΔ0)).continuousOn.smul (h.continuousOn.mono hsub)
  have hd : DifferentiableOn ℂ H {w : ℂ | x < w.re ∧ w.re < x'} :=
    DifferentiableOn.smul (fun w _ => ((differentiableAt_id.neg).const_cpow (Or.inl hΔ0)).differentiableWithinAt)
      (h.hol.mono hsub')
  have key := CohnElkies.strip_shift (H := H) (a := x) (b := x') hxx hcont hd
    (integrable_weight_two ((Δ ^ (-x) + Δ ^ (-x')) * B))
    (fun w hw1 hw2 => by
      have h1 := hB w hw1 hw2
      have h2 := rpow_neg_le_sum hΔ hw1 hw2
      simp only [hH, norm_smul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hΔ]
      simp only [Complex.neg_re]
      calc Δ ^ (-w.re) * ‖Φ w‖ ≤ (Δ ^ (-x) + Δ ^ (-x')) * (B * (1 + |w.im|) ^ (-2 : ℝ)) :=
            mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
        _ = _ := by ring)
    (tendsto_weight_two_atTop _) (tendsto_weight_two_atBot _)
  unfold mellinInv
  congr 1
  exact key.symm


/-- The inverse Mellin lift is real. -/
theorem MellinLiftData.mellinInv_conj (h : MellinLiftData c Φ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < c)
    {Δ : ℝ} (hΔ : 0 < Δ) : starRingEnd ℂ (mellinInv x Φ Δ) = mellinInv x Φ Δ := by
  unfold mellinInv
  have hcj : ∀ y : ℝ, starRingEnd ℂ ((Δ : ℂ) ^ (-((x : ℂ) + (y : ℂ) * Complex.I)) •
        Φ ((x : ℂ) + (y : ℂ) * Complex.I)) =
      (Δ : ℂ) ^ (-((x : ℂ) + ((-y : ℝ) : ℂ) * Complex.I)) • Φ ((x : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) := by
    intro y
    have hargs : (Δ : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hΔ.le]; exact Real.pi_ne_zero.symm
    have e1 : starRingEnd ℂ ((Δ : ℂ) ^ (-((x : ℂ) + (y : ℂ) * Complex.I))) =
        (Δ : ℂ) ^ (-((x : ℂ) + ((-y : ℝ) : ℂ) * Complex.I)) := by
      have := Complex.conj_cpow (Δ : ℂ) (starRingEnd ℂ (-((x : ℂ) + (y : ℂ) * Complex.I))) hargs
      rw [Complex.conj_ofReal, Complex.conj_conj] at this
      rw [← this]
      congr 1
      simp [Complex.conj_ofReal]
    have e2 : starRingEnd ℂ (Φ ((x : ℂ) + (y : ℂ) * Complex.I)) =
        Φ ((x : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) := by
      rw [← h.real _ (by simpa using hx0) (by simpa using hx1)]
      congr 1
      simp [Complex.conj_ofReal]
    rw [smul_eq_mul, smul_eq_mul, map_mul, e1, e2]
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]
  congr 1
  rw [← integral_conj]
  simp_rw [hcj]
  exact integral_neg_eq_self (fun y : ℝ => (Δ : ℂ) ^ (-((x : ℂ) + (y : ℂ) * Complex.I)) • Φ ((x : ℂ) + (y : ℂ) * Complex.I)) volume

theorem MellinLiftData.im_mellinInv (h : MellinLiftData c Φ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < c)
    {Δ : ℝ} (hΔ : 0 < Δ) : (mellinInv x Φ Δ).im = 0 := by
  have := h.mellinInv_conj hx0 hx1 hΔ
  have h2 := congrArg Complex.im this
  simp only [Complex.conj_im] at h2
  linarith

/-- The pointwise bound `|f(Δ)| ≤ C_x Δ^{-x}`. -/
theorem MellinLiftData.norm_mellinInv_le (h : MellinLiftData c Φ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Δ : ℝ, 0 < Δ → ‖mellinInv x Φ Δ‖ ≤ C * Δ ^ (-x) := by
  obtain ⟨B, hB⟩ := h.line_bound hx0 hx1
  refine ⟨(1 / (2 * Real.pi)) * ∫ y : ℝ, |B| * (1 + |y|) ^ (-2 : ℝ), ?_, fun Δ hΔ => ?_⟩
  · exact mul_nonneg (by positivity) (integral_nonneg fun y => by positivity)
  unfold mellinInv
  rw [norm_smul]
  have hint : ‖∫ y : ℝ, (Δ : ℂ) ^ (-((x : ℂ) + (y : ℂ) * Complex.I)) • Φ ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      ∫ y : ℝ, Δ ^ (-x) * (|B| * (1 + |y|) ^ (-2 : ℝ)) := by
    refine norm_integral_le_of_norm_le ((integrable_weight_two |B|).const_mul (Δ ^ (-x))) (ae_of_all _ fun y => ?_)
    rw [norm_smul, norm_cpow_line hΔ]
    exact mul_le_mul_of_nonneg_left ((hB y).trans (mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity))) (Real.rpow_nonneg hΔ.le _)
  rw [integral_const_mul] at hint
  have hn : ‖(1 / (2 * Real.pi) : ℝ)‖ = 1 / (2 * Real.pi) := by
    rw [Real.norm_eq_abs]; exact abs_of_pos (by positivity)
  rw [hn]
  calc 1 / (2 * Real.pi) * ‖∫ y : ℝ, (Δ : ℂ) ^ (-((x : ℂ) + (y : ℂ) * Complex.I)) • Φ ((x : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ 1 / (2 * Real.pi) * (Δ ^ (-x) * ∫ y : ℝ, |B| * (1 + |y|) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by ring

/-- Continuity of the inverse Mellin lift on `(0, ∞)`. -/
theorem MellinLiftData.continuousOn_mellinInv (h : MellinLiftData c Φ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < c) :
    ContinuousOn (mellinInv x Φ) (Ioi 0) := by
  intro Δ₀ hΔ₀
  have hΔ₀' : 0 < Δ₀ := hΔ₀
  have hnhds : Icc (Δ₀ / 2) (2 * Δ₀) ∈ 𝓝 Δ₀ := Icc_mem_nhds (by linarith) (by linarith)
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousOn.continuousAt ?_ hnhds
  obtain ⟨B, hB⟩ := h.line_bound hx0 hx1
  have hcpow : ∀ Δ ∈ Icc (Δ₀ / 2) (2 * Δ₀), 0 < Δ := fun Δ hΔ => by linarith [hΔ.1]
  unfold mellinInv
  refine ContinuousOn.const_smul ?_ _
  refine continuousOn_of_dominated (bound := fun y => (Δ₀ / 2) ^ (-x) * |B| * (1 + |y|) ^ (-2 : ℝ)) ?_ ?_ ?_ ?_
  · intro Δ hΔ
    exact (h.integrable_line_cpow hx0 hx1 (hcpow Δ hΔ)).aestronglyMeasurable
  · intro Δ hΔ
    refine ae_of_all _ fun y => ?_
    rw [norm_smul, norm_cpow_line (hcpow Δ hΔ)]
    have h1 : Δ ^ (-x) ≤ (Δ₀ / 2) ^ (-x) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hΔ.1 (by linarith)
    calc Δ ^ (-x) * ‖Φ ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ (Δ₀ / 2) ^ (-x) * (|B| * (1 + |y|) ^ (-2 : ℝ)) :=
          mul_le_mul h1 ((hB y).trans (mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)))
            (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · exact integrable_weight_two ((Δ₀ / 2) ^ (-x) * |B|)
  · refine ae_of_all _ fun y => ?_
    have hc1 : ContinuousOn (fun Δ : ℝ => (Δ : ℂ) ^ (-((x : ℂ) + (y : ℂ) * Complex.I))) (Icc (Δ₀ / 2) (2 * Δ₀)) :=
      ContinuousOn.cpow_const (Complex.continuous_ofReal.continuousOn) fun Δ hΔ =>
        Complex.ofReal_mem_slitPlane.mpr (hcpow Δ hΔ)
    exact hc1.smul continuousOn_const


/-! ### The Mellin transform of the lift (Fourier inversion) -/

theorem rexp_neg_deriv_aux' :
    ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) univ x :=
  fun x _ ↦ mul_neg_one (Real.exp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

theorem rexp_neg_image_aux' : Real.exp ∘ Neg.neg '' (univ : Set ℝ) = Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ, Real.range_exp]

theorem rexp_neg_injOn_aux' : (univ : Set ℝ).InjOn (Real.exp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

theorem rexp_cexp_aux' (x : ℝ) (s : ℂ) (f : ℂ) :
    Complex.exp (-(x : ℂ)) * (Complex.exp (-(x : ℂ)) ^ (s - 1) * f) = Complex.exp (-(s * (x : ℂ))) * f := by
  have h1 : Complex.exp (-(x : ℂ)) ^ (s - 1) = Complex.exp (-(x : ℂ) * (s - 1)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
      Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_nonneg)]
  rw [h1, ← mul_assoc, ← Complex.exp_add]
  ring_nf

/-- Change of variables `t = e^{-u}`: a convergent Mellin integral is an integrable function of `u`. -/
theorem integrable_exp_neg_smul (f : ℝ → ℂ) (σ : ℝ) (hf : MellinConvergent f σ) :
    Integrable (fun u : ℝ => Real.exp (-σ * u) • f (Real.exp (-u))) := by
  rw [MellinConvergent, ← rexp_neg_image_aux', integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ rexp_neg_deriv_aux' rexp_neg_injOn_aux'] at hf
  simp only [Function.comp_apply, smul_eq_mul, Complex.real_smul, abs_neg,
    abs_of_pos (Real.exp_pos _), Complex.ofReal_exp, Complex.ofReal_neg] at hf
  have hf' : Integrable fun (x : ℝ) ↦ Complex.exp (-(σ : ℂ) * (x : ℂ)) * f (Real.exp (-x)) := by
    refine (integrableOn_univ.mp hf).congr (ae_of_all _ fun u => ?_)
    have := rexp_cexp_aux' u (σ : ℂ) (f (Real.exp (-u)))
    simp only [neg_mul] at this ⊢
    exact this
  refine hf'.congr (ae_of_all _ fun u => ?_)
  simp only [Complex.real_smul]
  push_cast
  ring_nf


theorem MellinLiftData.mellinConvergent (h : MellinLiftData c Φ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < c) :
    MellinConvergent (fun Δ : ℝ => mellinInv x Φ Δ) (x : ℂ) := by
  obtain ⟨C₁, hC₁, hb₁⟩ := h.norm_mellinInv_le (x := x / 2) (by linarith) (by linarith)
  obtain ⟨C₂, hC₂, hb₂⟩ := h.norm_mellinInv_le (x := (x + c) / 2) (by linarith) (by linarith)
  have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ ((x : ℂ) - 1) • mellinInv x Φ t) (Ioi 0) := by
    have hc1 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ ((x : ℂ) - 1)) (Ioi 0) :=
      ContinuousOn.cpow_const (Complex.continuous_ofReal.continuousOn) fun t ht =>
        Complex.ofReal_mem_slitPlane.mpr ht
    exact hc1.smul (h.continuousOn_mellinInv hx0 hx1)
  have e1 : ∀ t : ℝ, 0 < t → mellinInv (x / 2) Φ t = mellinInv x Φ t := fun t ht =>
    h.mellinInv_indep (by linarith) (by linarith) hx0 hx1 ht
  have e2 : ∀ t : ℝ, 0 < t → mellinInv ((x + c) / 2) Φ t = mellinInv x Φ t := fun t ht =>
    h.mellinInv_indep (by linarith) (by linarith) hx0 hx1 ht
  have hnorm : ∀ t : ℝ, 0 < t → ‖(t : ℂ) ^ ((x : ℂ) - 1) • mellinInv x Φ t‖ = t ^ (x - 1) * ‖mellinInv x Φ t‖ := by
    intro t ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp
  unfold MellinConvergent
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  refine IntegrableOn.union ?_ ?_
  · have hint : IntegrableOn (fun t : ℝ => C₁ * t ^ (x / 2 - 1)) (Ioc 0 1) :=
      (((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < x / 2 - 1)))).const_mul C₁
    refine Integrable.mono' hint (hcont.mono Ioc_subset_Ioi_self |>.aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [hnorm t ht.1]
    calc t ^ (x - 1) * ‖mellinInv x Φ t‖ ≤ t ^ (x - 1) * (C₁ * t ^ (-(x / 2))) :=
          mul_le_mul_of_nonneg_left (e1 t ht.1 ▸ hb₁ t ht.1) (Real.rpow_nonneg ht.1.le _)
      _ = C₁ * t ^ (x / 2 - 1) := by
          rw [show x / 2 - 1 = (x - 1) + -(x / 2) by ring, Real.rpow_add ht.1]; ring
  · have hint : IntegrableOn (fun t : ℝ => C₂ * t ^ (x - 1 - (x + c) / 2)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul C₂
    refine Integrable.mono' hint (hcont.mono (fun t ht => lt_trans one_pos ht) |>.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans one_pos ht
    rw [hnorm t ht0]
    calc t ^ (x - 1) * ‖mellinInv x Φ t‖ ≤ t ^ (x - 1) * (C₂ * t ^ (-((x + c) / 2))) :=
          mul_le_mul_of_nonneg_left (e2 t ht0 ▸ hb₂ t ht0) (Real.rpow_nonneg ht0.le _)
      _ = C₂ * t ^ (x - 1 - (x + c) / 2) := by
          rw [show x - 1 - (x + c) / 2 = (x - 1) + -((x + c) / 2) by ring, Real.rpow_add ht0]; ring


open scoped FourierTransform in
/-- **Mellin transform of the inverse Mellin lift**: on every line of the open strip, `mellin f = Φ`. -/
theorem MellinLiftData.mellin_mellinInv (h : MellinLiftData c Φ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < c)
    (y₀ : ℝ) :
    mellin (fun Δ : ℝ => mellinInv x Φ Δ) ((x : ℂ) + (y₀ : ℂ) * Complex.I) =
      Φ ((x : ℂ) + (y₀ : ℂ) * Complex.I) := by
  set f' : ℝ → ℂ := fun Δ => mellinInv x Φ Δ with hf'
  set φ : ℝ → ℂ := fun y => Φ ((x : ℂ) + 2 * Real.pi * y * Complex.I) with hφ
  have hg : Integrable (fun u : ℝ => Real.exp (-x * u) • f' (Real.exp (-u))) :=
    integrable_exp_neg_smul f' x (h.mellinConvergent hx0 hx1)
  have hgeq : (fun u : ℝ => Real.exp (-x * u) • f' (Real.exp (-u))) = 𝓕⁻ φ := by
    funext u
    have := mellinInv_eq_fourierInv x Φ (x := Real.exp (-u)) (Real.exp_pos _)
    simp only [hf']
    rw [this, Real.log_exp, neg_neg]
    simp only [Complex.real_smul, smul_eq_mul]
    rw [← mul_assoc]
    have hr : (Real.exp (-u)) ^ (-x) * Real.exp (-x * u) = 1 := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add]
      rw [show -u * -x + -x * u = 0 by ring, Real.exp_zero]
    have hc : (Real.exp (-u) : ℂ) ^ (-(x : ℂ)) * (Real.exp (-x * u) : ℂ) = 1 := by
      rw [show -(x : ℂ) = ((-x : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (Real.exp_pos _).le,
        ← Complex.ofReal_mul, hr]
      simp
    rw [mul_comm (↑(Real.exp (-x * u)) : ℂ), hc, one_mul]
  have hFφ : Integrable φ := by
    have := (h.integrable_line hx0 hx1).comp_mul_left' (R := 2 * Real.pi) (by positivity)
    refine this.congr (ae_of_all _ fun y => ?_)
    simp only [hφ]
    congr 1
    push_cast; ring
  have hF2 : Integrable (𝓕 φ) := by
    have e : 𝓕 φ = fun u => (fun u : ℝ => Real.exp (-x * u) • f' (Real.exp (-u))) (-u) := by
      funext u
      rw [hgeq, Real.fourierInv_eq_fourier_neg, neg_neg]
    rw [e]
    exact hg.comp_neg
  have hcont : ContinuousAt φ (y₀ / (2 * Real.pi)) := by
    have : Continuous φ := by
      simp only [hφ]
      exact h.continuousOn.comp_continuous (by fun_prop) fun y => by simpa using ⟨hx0, hx1⟩
    exact this.continuousAt
  have key := hFφ.fourier_fourierInv_eq hF2 hcont
  rw [mellin_eq_fourier f']
  have hre : (((x : ℂ) + (y₀ : ℂ) * Complex.I)).re = x := by simp
  have him : (((x : ℂ) + (y₀ : ℂ) * Complex.I)).im = y₀ := by simp
  rw [hre, him, hgeq, key]
  simp only [hφ]
  congr 1
  have : (2 * (Real.pi : ℂ) * ((y₀ / (2 * Real.pi) : ℝ) : ℂ)) = (y₀ : ℂ) := by
    push_cast; field_simp
  rw [this]


/-- The real-valued inverse Mellin lift of `Φ` along `Re z = x₀` (meaningful for `Δ > 0`). -/
noncomputable def liftFun (Φ : ℂ → ℂ) (x₀ : ℝ) : ℝ → ℝ := fun Δ => (mellinInv x₀ Φ Δ).re

lemma ofReal_liftFun (h : MellinLiftData c Φ) {x₀ x : ℝ} (hx₀ : 0 < x₀) (hx₀' : x₀ < c) (hx0 : 0 < x)
    (hx1 : x < c) {Δ : ℝ} (hΔ : 0 < Δ) : (liftFun Φ x₀ Δ : ℂ) = mellinInv x Φ Δ := by
  have h1 := h.mellinInv_indep hx₀ hx₀' hx0 hx1 hΔ
  have h2 := h.im_mellinInv hx₀ hx₀' hΔ
  unfold liftFun
  rw [h1] at h2 ⊢
  apply Complex.ext <;> simp [h2]

lemma continuousOn_liftFun (h : MellinLiftData c Φ) {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀' : x₀ < c) :
    ContinuousOn (liftFun Φ x₀) (Ioi 0) :=
  Complex.continuous_re.comp_continuousOn (h.continuousOn_mellinInv hx₀ hx₀')

lemma norm_liftFun_le (h : MellinLiftData c Φ) {x₀ x : ℝ} (hx₀ : 0 < x₀) (hx₀' : x₀ < c) (hx0 : 0 < x)
    (hx1 : x < c) : ∃ C : ℝ, 0 ≤ C ∧ ∀ Δ : ℝ, 0 < Δ → |liftFun Φ x₀ Δ| ≤ C * Δ ^ (-x) := by
  obtain ⟨C, hC, hb⟩ := h.norm_mellinInv_le hx0 hx1
  refine ⟨C, hC, fun Δ hΔ => ?_⟩
  have := congrArg norm (ofReal_liftFun h hx₀ hx₀' hx0 hx1 hΔ)
  rw [Complex.norm_real, Real.norm_eq_abs] at this
  rw [this]; exact hb Δ hΔ

/-- **Mellin transform of the lift** on the whole open strip. -/
theorem mellinRaw_liftFun (h : MellinLiftData c Φ) {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀' : x₀ < c) {z : ℂ}
    (hz0 : 0 < z.re) (hz1 : z.re < c) : mellinRaw (liftFun Φ x₀) z = Φ z := by
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
  have key := h.mellin_mellinInv hz0 hz1 z.im
  rw [← hz] at key
  rw [← key]
  unfold mellin mellinRaw
  refine setIntegral_congr_fun measurableSet_Ioi fun Δ hΔ => ?_
  have hΔ' : 0 < Δ := hΔ
  simp only [smul_eq_mul]
  rw [mul_comm, ofReal_liftFun h hx₀ hx₀' hz0 hz1 hΔ']

end


/-- info: 'FormalResearch.SignUncertainty.MellinLiftData.mellinInv_indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.MellinLiftData.mellinInv_indep

/-- info: 'FormalResearch.SignUncertainty.mellinRaw_liftFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.mellinRaw_liftFun

/-- info: 'FormalResearch.SignUncertainty.MellinLiftData.mellin_mellinInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.MellinLiftData.mellin_mellinInv

end FormalResearch.SignUncertainty
