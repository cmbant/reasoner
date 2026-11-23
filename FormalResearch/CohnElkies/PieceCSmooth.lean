module

public import FormalResearch.CohnElkies.PieceCUniform
public import FormalResearch.CohnElkies.TwoIBPPhase

/-!
# Piece C, smooth part: discharge of `hsmooth` by `two_ibp_phase`

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, Piece C item 2 (the smooth part). The two-integrations-by-parts
bound `two_ibp_phase` is applied to `a e^{iψ}` with `a` the cut-off smooth amplitude, `ψ = pcPhase` and `s = {0}`.

Status: proved, unconditional (the analytic input on `a` and `ψ` is a hypothesis of each statement).
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace FormalResearch.CohnElkies

/-! ### Weight integrals -/

lemma integrable_w0 {r : ℝ} (hr : 1 < r) : Integrable (fun v : ℝ => (1 + |v|) ^ (-r)) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := r) (by simpa using hr)
  simpa [Real.norm_eq_abs] using this

lemma integrable_w1 : Integrable (fun v : ℝ => |v| * (1 + |v|) ^ (-(5 / 2 : ℝ))) := by
  refine (integrable_w0 (r := 3 / 2) (by norm_num)).mono' (by fun_prop) (ae_of_all _ fun v => ?_)
  have h1 : (0 : ℝ) < 1 + |v| := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : (1 + |v|) ^ (-(5 / 2 : ℝ)) = (1 + |v|) ^ (-(3 / 2 : ℝ)) * (1 + |v|)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add h1]; norm_num
  rw [this, ← mul_assoc]
  have h2 : |v| * (1 + |v|)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one h1]; linarith
  have h3 : 0 ≤ (1 + |v|) ^ (-(3 / 2 : ℝ)) := by positivity
  nlinarith [mul_nonneg h3 (sub_nonneg.mpr h2), mul_le_mul_of_nonneg_left h2 h3]

lemma integrable_of_even_Ioi {f : ℝ → ℝ} (hf : ∀ v, f (-v) = f v) (h : IntegrableOn f (Ioi 0)) : Integrable f := by
  have hneg : IntegrableOn f (Iio 0) := by
    have mp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (MeasurableEquiv.neg ℝ).measurableEmbedding (f := f) (s := Iio 0)
    have h2 : (MeasurableEquiv.neg ℝ) ⁻¹' (Iio 0) = Ioi 0 := by ext x; simp
    have : IntegrableOn (f ∘ (MeasurableEquiv.neg ℝ)) (Ioi 0) := by
      simpa [Function.comp_def, hf] using h
    rw [← h2] at this
    exact mp.mp this
  have hall : IntegrableOn f (Iio 0 ∪ {0} ∪ Ioi 0) :=
    (hneg.union (integrableOn_singleton (x := (0 : ℝ)) (hx := by simp))).union h
  have : (Iio (0 : ℝ) ∪ {0} ∪ Ioi 0) = univ := by
    ext x; simp only [mem_union, mem_Iio, mem_singleton_iff, mem_Ioi, mem_univ, iff_true]
    rcases lt_trichotomy x 0 with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  rw [this] at hall
  exact integrableOn_univ.mp hall

lemma integrable_w2 : Integrable (fun v : ℝ => |v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ))) := by
  refine integrable_of_even_Ioi (fun v => by simp) ?_
  have hmeas : Measurable (fun v : ℝ => |v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ))) := by fun_prop
  have h01 : IntegrableOn (fun v : ℝ => |v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ))) (Ioc 0 1) := by
    have hi : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (Ioc 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))).1
    refine hi.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_pos hx.1]
    have : (1 + x) ^ (-(2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hx.1]) (by norm_num)
    have h0 : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx.1.le _
    nlinarith
  have h1 : IntegrableOn (fun v : ℝ => |v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ))) (Ioi 1) := by
    refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)).mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 < x := hx
    have hx0 : 0 < x := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_pos hx0]
    have ha : x ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by norm_num)
    have hb : (1 + x) ^ (-(2 : ℝ)) ≤ x ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by norm_num)
    have h0 : 0 ≤ (1 + x) ^ (-(2 : ℝ)) := by positivity
    nlinarith [mul_le_mul ha hb h0 zero_le_one]
  have := h01.union h1
  rwa [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] at this

lemma setIntegral_Icc_abs {g : ℝ → ℝ} (hg : ContinuousOn g (Ici 0)) {V : ℝ} (hV : 0 ≤ V) :
    ∫ v in Icc (-V) V, g |v| = 2 * ∫ x in (0 : ℝ)..V, g x := by
  have hc : Continuous fun x : ℝ => g |x| :=
    continuousOn_univ.mp (hg.comp continuous_abs.continuousOn fun x _ => abs_nonneg x)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h1 : ∫ x in (0 : ℝ)..V, g |x| = ∫ x in (0 : ℝ)..V, g x :=
    intervalIntegral.integral_congr fun x hx => by
      show g |x| = g x
      rw [Set.uIcc_of_le hV] at hx
      rw [abs_of_nonneg hx.1]
  have h2 : ∫ x in (-V)..0, g |x| = ∫ x in (0 : ℝ)..V, g |x| := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := V) (fun x : ℝ => g |x|)
    simp only [abs_neg, neg_zero] at this
    exact this.symm
  rw [h2, h1]; ring

lemma integral_Icc_one_add_abs_rpow_neg_half_le {V : ℝ} (hV : 0 ≤ V) :
    ∫ v in Icc (-V) V, (1 + |v|) ^ (-(1 / 2 : ℝ)) ≤ 4 * (1 + V) ^ (1 / 2 : ℝ) := by
  rw [setIntegral_Icc_abs (g := fun x : ℝ => (1 + x) ^ (-(1 / 2 : ℝ)))
    (fun x hx => ((continuousAt_const.add continuousAt_id).rpow_const (Or.inl (by simp at hx ⊢; linarith))).continuousWithinAt) hV]
  have := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := V) (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) 1
  simp only [add_zero] at this
  rw [this, integral_rpow (Or.inl (by norm_num))]
  have h1 : (1 : ℝ) ^ (-(1 / 2 : ℝ) + 1) = 1 := Real.one_rpow _
  rw [h1]
  have h2 : (1 + V) ^ (-(1 / 2 : ℝ) + 1) = (1 + V) ^ (1 / 2 : ℝ) := by norm_num
  rw [h2]
  have : 0 ≤ (1 + V) ^ (1 / 2 : ℝ) := by positivity
  have h3 : (1 : ℝ) ≤ (1 + V) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  norm_num
  nlinarith

lemma frac_le_aux {X p A : ℝ} (hX : 0 ≤ X) (hA : 0 < A) (hp : A / 2 ≤ p) (k : ℕ) :
    X / p ^ k ≤ 2 ^ k * X / A ^ k := by
  have hp0 : 0 < p := by linarith
  have hA2 : A ≤ 2 * p := by linarith
  have h : A ^ k ≤ (2 * p) ^ k := pow_le_pow_left₀ hA.le hA2 k
  rw [mul_pow] at h
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hX (sub_nonneg.mpr h)]

lemma pw_bound {Ca w0 w1 W2 s a0 a1 a2 q2 q3 p A : ℝ} (hCa : 0 ≤ Ca) (hA : 1 ≤ A) (hp : A / 2 ≤ p)
    (ha2 : a2 ≤ Ca * W2) (ha1 : a1 ≤ Ca * w0) (ha0 : a0 ≤ Ca * w0)
    (ha0n : 0 ≤ a0) (ha1n : 0 ≤ a1) (ha2n : 0 ≤ a2) (hw0 : 0 ≤ w0) (hq2 : |q2| ≤ π ^ 2 / 6 * w1)
    (hq3 : |q3| ≤ π ^ 2 / 3) (hs : q2 ^ 2 ≤ s) (hw1 : 0 ≤ w1) :
    a2 / p ^ 2 + 3 * a1 * |q2| / p ^ 3 + a0 * |q3| / p ^ 3 + 3 * a0 * q2 ^ 2 / p ^ 4 ≤
      4 * Ca * W2 / A ^ 2 + 24 * Ca * (π ^ 2 / 6) * (w1 * w0) / A ^ 2 + 8 * Ca * (π ^ 2 / 3) * w0 / A ^ 2 + 48 * Ca * (w0 * s) / A ^ 4 := by
  have hA0 : 0 < A := by linarith
  have hp0 : 0 < p := by linarith
  have hApow : A ^ 2 ≤ A ^ 3 := pow_le_pow_right₀ hA (by norm_num)
  have e1 : a2 / p ^ 2 ≤ 4 * Ca * W2 / A ^ 2 := by
    refine (frac_le_aux ha2n hA0 hp 2).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left ha2 (by norm_num : (0 : ℝ) ≤ 2 ^ 2)
    nlinarith [sq_nonneg A]
  have e2 : 3 * a1 * |q2| / p ^ 3 ≤ 24 * Ca * (π ^ 2 / 6) * (w1 * w0) / A ^ 2 := by
    have hX : 0 ≤ 3 * a1 * |q2| := by positivity
    refine (frac_le_aux hX hA0 hp 3).trans ?_
    have hXle : 3 * a1 * |q2| ≤ 3 * (Ca * w0) * (π ^ 2 / 6 * w1) :=
      mul_le_mul (mul_le_mul_of_nonneg_left ha1 (by norm_num)) hq2 (abs_nonneg _) (by positivity)
    calc 2 ^ 3 * (3 * a1 * |q2|) / A ^ 3 ≤ 2 ^ 3 * (3 * (Ca * w0) * (π ^ 2 / 6 * w1)) / A ^ 3 := by gcongr
      _ ≤ 2 ^ 3 * (3 * (Ca * w0) * (π ^ 2 / 6 * w1)) / A ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) hApow
      _ = 24 * Ca * (π ^ 2 / 6) * (w1 * w0) / A ^ 2 := by ring
  have e3 : a0 * |q3| / p ^ 3 ≤ 8 * Ca * (π ^ 2 / 3) * w0 / A ^ 2 := by
    have hX : 0 ≤ a0 * |q3| := by positivity
    refine (frac_le_aux hX hA0 hp 3).trans ?_
    have hXle : a0 * |q3| ≤ (Ca * w0) * (π ^ 2 / 3) := mul_le_mul ha0 hq3 (abs_nonneg _) (by positivity)
    calc 2 ^ 3 * (a0 * |q3|) / A ^ 3 ≤ 2 ^ 3 * ((Ca * w0) * (π ^ 2 / 3)) / A ^ 3 := by gcongr
      _ ≤ 2 ^ 3 * ((Ca * w0) * (π ^ 2 / 3)) / A ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) hApow
      _ = 8 * Ca * (π ^ 2 / 3) * w0 / A ^ 2 := by ring
  have e4 : 3 * a0 * q2 ^ 2 / p ^ 4 ≤ 48 * Ca * (w0 * s) / A ^ 4 := by
    have hX : 0 ≤ 3 * a0 * q2 ^ 2 := by positivity
    refine (frac_le_aux hX hA0 hp 4).trans ?_
    have hXle : 3 * a0 * q2 ^ 2 ≤ 3 * (Ca * w0) * s :=
      mul_le_mul (mul_le_mul_of_nonneg_left ha0 (by norm_num)) hs (sq_nonneg _) (by positivity)
    calc 2 ^ 4 * (3 * a0 * q2 ^ 2) / A ^ 4 ≤ 2 ^ 4 * (3 * (Ca * w0) * s) / A ^ 4 := by gcongr
      _ = 48 * Ca * (w0 * s) / A ^ 4 := by ring
  linarith

theorem smooth_ibp_key {Ca : ℝ} (hCa : 0 ≤ Ca) {a : ℝ → ℂ} {ψ : ℝ → ℝ} {vs A : ℝ} (hA : 1 ≤ A) (hvs : 0 ≤ vs)
    (ha1 : ContDiff ℝ 1 a) (ha2 : ∀ x : ℝ, x ≠ 0 → DifferentiableAt ℝ (deriv a) x)
    (hsupp : ∀ x : ℝ, x ∉ Icc (-vs) vs → a x = 0)
    (hb0 : ∀ v : ℝ, ‖a v‖ ≤ Ca * (1 + |v|) ^ (-(5 / 2 : ℝ)))
    (hb1 : ∀ v : ℝ, ‖deriv a v‖ ≤ Ca * (1 + |v|) ^ (-(5 / 2 : ℝ)))
    (hb2 : ∀ v : ℝ, v ≠ 0 → ‖deriv (deriv a) v‖ ≤ Ca * (|v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ))))
    (hψ : ContDiff ℝ 3 ψ) (hψ1 : ∀ v ∈ Icc (-vs) vs, A / 2 ≤ deriv ψ v)
    (hψ2 : ∀ v : ℝ, v ≠ 0 → |deriv (deriv ψ) v| ≤ π ^ 2 / 6 * |v|)
    (hψ3 : ∀ v : ℝ, v ≠ 0 → |deriv (deriv (deriv ψ)) v| ≤ π ^ 2 / 3)
    (s : ℝ → ℝ) (hs : ∀ v : ℝ, v ≠ 0 → deriv (deriv ψ) v ^ 2 ≤ s v)
    (hsint : IntegrableOn (fun v : ℝ => (1 + |v|) ^ (-(5 / 2 : ℝ)) * s v) (Icc (-vs) vs)) :
    ‖∫ v, a v * Complex.exp (Complex.I * ψ v)‖ ≤
      (4 * Ca * (∫ v : ℝ, |v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ)))
        + 24 * Ca * (π ^ 2 / 6) * (∫ v : ℝ, |v| * (1 + |v|) ^ (-(5 / 2 : ℝ)))
        + 8 * Ca * (π ^ 2 / 3) * (∫ v : ℝ, (1 + |v|) ^ (-(5 / 2 : ℝ)))) / A ^ 2
      + 48 * Ca * (∫ v in Icc (-vs) vs, (1 + |v|) ^ (-(5 / 2 : ℝ)) * s v) / A ^ 4 := by
  have hA0 : 0 < A := by linarith
  have hpos : ∀ x ∈ Icc (-vs) vs, 0 < deriv ψ x := fun x hx => by linarith [hψ1 x hx]
  have hnull : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    have := (Set.countable_singleton (0 : ℝ)).ae_notMem (volume : Measure ℝ)
    filter_upwards [this] with x hx using hx
  have hint : IntegrableOn (deriv (deriv a)) (Icc (-vs) vs) := by
    refine ((integrable_w2.const_mul Ca).integrableOn (s := Icc (-vs) vs)).mono' (measurable_deriv _).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_of_ae hnull] with x hx
    exact hb2 x hx
  have hI := two_ibp_phase (a := a) (ψ := ψ) (u := -vs) (v := vs) (by linarith) ha1 {0} (Set.countable_singleton 0)
    (fun x hx => ha2 x hx) hint hsupp hψ hpos
  refine hI.trans ?_
  set w0 : ℝ → ℝ := fun v => (1 + |v|) ^ (-(5 / 2 : ℝ)) with hw0
  have hw0n : ∀ v, 0 ≤ w0 v := fun v => by positivity
  set W2 : ℝ → ℝ := fun v => |v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ)) with hW2
  have hint0 : Integrable w0 := integrable_w0 (r := 5 / 2) (by norm_num)
  have hint1 := integrable_w1
  have hint2 := integrable_w2
  set Gm : ℝ → ℝ := fun v => (4 * Ca / A ^ 2) * W2 v + (24 * Ca * (π ^ 2 / 6) / A ^ 2) * (|v| * w0 v)
    + (8 * Ca * (π ^ 2 / 3) / A ^ 2) * w0 v + (48 * Ca / A ^ 4) * (w0 v * s v) with hGm
  have hGmint : IntegrableOn Gm (Icc (-vs) vs) :=
    ((((hint2.integrableOn).const_mul _).add ((hint1.integrableOn).const_mul _)).add ((hint0.integrableOn).const_mul _)).add
      ((hsint).const_mul _)
  have hle : ∫ x in Icc (-vs) vs, (‖deriv (deriv a) x‖ / deriv ψ x ^ 2 + 3 * ‖deriv a x‖ * |deriv (deriv ψ) x| / deriv ψ x ^ 3
        + ‖a x‖ * |deriv (deriv (deriv ψ)) x| / deriv ψ x ^ 3 + 3 * ‖a x‖ * deriv (deriv ψ) x ^ 2 / deriv ψ x ^ 4) ≤ ∫ x in Icc (-vs) vs, Gm x := by
    refine integral_mono_of_nonneg ?_ hGmint ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      have := hpos x hx
      positivity
    · filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hnull] with x hx hx0
      have h := pw_bound (Ca := Ca) (w0 := w0 x) (w1 := |x|) (W2 := W2 x) (s := s x) (a0 := ‖a x‖) (a1 := ‖deriv a x‖)
        (a2 := ‖deriv (deriv a) x‖) (q2 := deriv (deriv ψ) x) (q3 := deriv (deriv (deriv ψ)) x) (p := deriv ψ x) (A := A)
        hCa hA (hψ1 x hx) (hb2 x hx0) (hb1 x) (hb0 x) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (hw0n x)
        (hψ2 x hx0) (hψ3 x hx0) (hs x hx0) (abs_nonneg _)
      refine h.trans (le_of_eq ?_)
      simp only [hGm]; ring
  refine hle.trans ?_
  have iW2 : Integrable (fun x => (4 * Ca / A ^ 2) * W2 x) (volume.restrict (Icc (-vs) vs)) := hint2.integrableOn.const_mul _
  have iW1 : Integrable (fun x => (24 * Ca * (π ^ 2 / 6) / A ^ 2) * (|x| * w0 x)) (volume.restrict (Icc (-vs) vs)) :=
    hint1.integrableOn.const_mul _
  have iW0 : Integrable (fun x => (8 * Ca * (π ^ 2 / 3) / A ^ 2) * w0 x) (volume.restrict (Icc (-vs) vs)) :=
    hint0.integrableOn.const_mul _
  have iW4 : Integrable (fun x => (48 * Ca / A ^ 4) * (w0 x * s x)) (volume.restrict (Icc (-vs) vs)) := hsint.const_mul _
  have hsplit : ∫ x in Icc (-vs) vs, Gm x = (4 * Ca / A ^ 2) * (∫ x in Icc (-vs) vs, W2 x)
      + (24 * Ca * (π ^ 2 / 6) / A ^ 2) * (∫ x in Icc (-vs) vs, |x| * w0 x)
      + (8 * Ca * (π ^ 2 / 3) / A ^ 2) * (∫ x in Icc (-vs) vs, w0 x)
      + (48 * Ca / A ^ 4) * (∫ x in Icc (-vs) vs, w0 x * s x) := by
    have iS2 : Integrable (fun x => (4 * Ca / A ^ 2) * W2 x + (24 * Ca * (π ^ 2 / 6) / A ^ 2) * (|x| * w0 x)) (volume.restrict (Icc (-vs) vs)) :=
      iW2.add iW1
    have iS3 : Integrable (fun x => (4 * Ca / A ^ 2) * W2 x + (24 * Ca * (π ^ 2 / 6) / A ^ 2) * (|x| * w0 x)
        + (8 * Ca * (π ^ 2 / 3) / A ^ 2) * w0 x) (volume.restrict (Icc (-vs) vs)) := iS2.add iW0
    simp only [hGm]
    rw [integral_add iS3 iW4, integral_add iS2 iW0, integral_add iW2 iW1,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hsplit]
  have i2 : ∫ x in Icc (-vs) vs, W2 x ≤ ∫ x, W2 x :=
    setIntegral_le_integral hint2 (ae_of_all _ fun x => by simp only [hW2]; positivity)
  have i1 : ∫ x in Icc (-vs) vs, |x| * w0 x ≤ ∫ x, |x| * w0 x :=
    setIntegral_le_integral hint1 (ae_of_all _ fun x => by have := hw0n x; positivity)
  have i0 : ∫ x in Icc (-vs) vs, w0 x ≤ ∫ x, w0 x :=
    setIntegral_le_integral hint0 (ae_of_all _ hw0n)
  have c1 : 0 ≤ 4 * Ca / A ^ 2 := by positivity
  have c2 : 0 ≤ 24 * Ca * (π ^ 2 / 6) / A ^ 2 := by positivity
  have c3 : 0 ≤ 8 * Ca * (π ^ 2 / 3) / A ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left i2 c1
  have := mul_le_mul_of_nonneg_left i1 c2
  have := mul_le_mul_of_nonneg_left i0 c3
  have e : (4 * Ca * (∫ v : ℝ, W2 v) + 24 * Ca * (π ^ 2 / 6) * (∫ v : ℝ, |v| * w0 v) + 8 * Ca * (π ^ 2 / 3) * (∫ v : ℝ, w0 v)) / A ^ 2 =
      (4 * Ca / A ^ 2) * (∫ v : ℝ, W2 v) + (24 * Ca * (π ^ 2 / 6) / A ^ 2) * (∫ v : ℝ, |v| * w0 v) + (8 * Ca * (π ^ 2 / 3) / A ^ 2) * (∫ v : ℝ, w0 v) := by ring
  have e4 : (48 * Ca / A ^ 4) * (∫ x in Icc (-vs) vs, w0 x * s x) = 48 * Ca * (∫ v in Icc (-vs) vs, w0 v * s v) / A ^ 4 := by ring
  show _ ≤ (4 * Ca * (∫ v : ℝ, W2 v) + 24 * Ca * (π ^ 2 / 6) * (∫ v : ℝ, |v| * w0 v) + 8 * Ca * (π ^ 2 / 3) * (∫ v : ℝ, w0 v)) / A ^ 2 + 48 * Ca * (∫ v in Icc (-vs) vs, w0 v * s v) / A ^ 4
  rw [e, ← e4]
  linarith

/-- The constant of `smooth_ibp_bound`. -/
noncomputable def smoothConst (Ca V : ℝ) : ℝ :=
  4 * Ca * (∫ v : ℝ, |v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ)))
    + 24 * Ca * (π ^ 2 / 6) * (∫ v : ℝ, |v| * (1 + |v|) ^ (-(5 / 2 : ℝ)))
    + 8 * Ca * (π ^ 2 / 3) * (∫ v : ℝ, (1 + |v|) ^ (-(5 / 2 : ℝ)))
    + 48 * max (Ca * (π ^ 2 / 6) ^ 2 * (4 * V)) (Ca * (4 * max ((π ^ 2 / 6) ^ 2) 1) * (∫ v : ℝ, (1 + |v|) ^ (-(9 / 2 : ℝ))))

/-- **Smooth part of Piece C (two integrations by parts).** `a` is `C¹` with `a'` differentiable off `{0}`, supported in
`[-vs, vs]`, with `|a|, |a'| ≤ C_a (1+|v|)^{-5/2}` and `|a''| ≤ C_a |v|^{-1/2}(1+|v|)^{-2}`; `ψ` is `C³` with
`ψ' ≥ A/2` on `[-vs, vs]`, `|ψ''| ≤ min(π²|v|/6, D/|v|)`, `|ψ'''| ≤ π²/3`; and either `√(1+vs) ≤ V A²` or `D ≤ A`
(the two cases `L ≤ 1`, `L > 1` of the paper). Then `|∫ a e^{iψ}| ≤ C_s / A²` with `C_s` depending only on `C_a`, `V`. -/
theorem smooth_ibp_bound {Ca V : ℝ} (hCa : 0 ≤ Ca) (hV : 0 ≤ V) {a : ℝ → ℂ} {ψ : ℝ → ℝ} {vs A D : ℝ}
    (hA : 1 ≤ A) (hvs : 0 ≤ vs) (hD : 0 ≤ D)
    (ha1 : ContDiff ℝ 1 a) (ha2 : ∀ x : ℝ, x ≠ 0 → DifferentiableAt ℝ (deriv a) x)
    (hsupp : ∀ x : ℝ, x ∉ Icc (-vs) vs → a x = 0)
    (hb0 : ∀ v : ℝ, ‖a v‖ ≤ Ca * (1 + |v|) ^ (-(5 / 2 : ℝ)))
    (hb1 : ∀ v : ℝ, ‖deriv a v‖ ≤ Ca * (1 + |v|) ^ (-(5 / 2 : ℝ)))
    (hb2 : ∀ v : ℝ, v ≠ 0 → ‖deriv (deriv a) v‖ ≤ Ca * (|v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ))))
    (hψ : ContDiff ℝ 3 ψ) (hψ1 : ∀ v ∈ Icc (-vs) vs, A / 2 ≤ deriv ψ v)
    (hψ2 : ∀ v : ℝ, v ≠ 0 → |deriv (deriv ψ) v| ≤ π ^ 2 / 6 * |v|)
    (hψ2' : ∀ v : ℝ, v ≠ 0 → |deriv (deriv ψ) v| ≤ D / |v|)
    (hψ3 : ∀ v : ℝ, v ≠ 0 → |deriv (deriv (deriv ψ)) v| ≤ π ^ 2 / 3)
    (hcase : (1 + vs) ^ (1 / 2 : ℝ) ≤ V * A ^ 2 ∨ D ≤ A) :
    ‖∫ v, a v * Complex.exp (Complex.I * ψ v)‖ ≤ smoothConst Ca V / A ^ 2 := by
  have hA0 : 0 < A := by linarith
  have hA2 : 0 < A ^ 2 := by positivity
  have hA4 : A ^ 4 = A ^ 2 * A ^ 2 := by ring
  set J0 := ∫ v : ℝ, (1 + |v|) ^ (-(5 / 2 : ℝ))
  set J1 := ∫ v : ℝ, |v| * (1 + |v|) ^ (-(5 / 2 : ℝ))
  set J2 := ∫ v : ℝ, |v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ))
  set J9 := ∫ v : ℝ, (1 + |v|) ^ (-(9 / 2 : ℝ))
  set K : ℝ := max ((π ^ 2 / 6) ^ 2) 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  have hKπ : (π ^ 2 / 6) ^ 2 ≤ K := le_max_left _ _
  have hJ9 : 0 ≤ J9 := integral_nonneg fun v => by positivity
  have hP : Ca * (π ^ 2 / 6) ^ 2 * (4 * V) ≤ max (Ca * (π ^ 2 / 6) ^ 2 * (4 * V)) (Ca * (4 * K) * J9) := le_max_left _ _
  set C4 := max (Ca * (π ^ 2 / 6) ^ 2 * (4 * V)) (Ca * (4 * K) * J9) with hC4
  have hC4n : 0 ≤ C4 := le_trans (by positivity) hP
  have hfinal : ∀ T : ℝ, 48 * Ca * T / A ^ 4 ≤ 48 * C4 / A ^ 2 → ∀ B : ℝ, B ≤ (4 * Ca * J2 + 24 * Ca * (π ^ 2 / 6) * J1 + 8 * Ca * (π ^ 2 / 3) * J0) / A ^ 2
      + 48 * Ca * T / A ^ 4 → B ≤ smoothConst Ca V / A ^ 2 := fun T hT B hB => by
    refine hB.trans ?_
    have : smoothConst Ca V = 4 * Ca * J2 + 24 * Ca * (π ^ 2 / 6) * J1 + 8 * Ca * (π ^ 2 / 3) * J0 + 48 * C4 := rfl
    have e : smoothConst Ca V / A ^ 2 = (4 * Ca * J2 + 24 * Ca * (π ^ 2 / 6) * J1 + 8 * Ca * (π ^ 2 / 3) * J0) / A ^ 2 + 48 * C4 / A ^ 2 := by
      rw [this]; ring
    rw [e]
    linarith
  rcases hcase with h1 | h2
  · -- case `√(1+vs) ≤ V A²`
    have hc5 : Continuous fun v : ℝ => (1 + |v|) ^ (-(5 / 2 : ℝ)) :=
      Continuous.rpow_const (by fun_prop) fun v => Or.inl (by positivity)
    have key := smooth_ibp_key hCa hA hvs ha1 ha2 hsupp hb0 hb1 hb2 hψ hψ1 hψ2 hψ3 (fun v => (π ^ 2 / 6) ^ 2 * v ^ 2)
      (fun v hv => by
        have := hψ2 v hv
        calc deriv (deriv ψ) v ^ 2 = |deriv (deriv ψ) v| ^ 2 := (sq_abs _).symm
          _ ≤ (π ^ 2 / 6 * |v|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
          _ = (π ^ 2 / 6) ^ 2 * v ^ 2 := by rw [mul_pow, sq_abs])
      (Continuous.integrableOn_Icc (hc5.mul (by fun_prop)))
    refine hfinal _ ?_ _ key
    have hint : ∫ v in Icc (-vs) vs, (1 + |v|) ^ (-(5 / 2 : ℝ)) * ((π ^ 2 / 6) ^ 2 * v ^ 2) ≤
        (π ^ 2 / 6) ^ 2 * (4 * (1 + vs) ^ (1 / 2 : ℝ)) := by
      have hc : Continuous fun v : ℝ => (1 + |v|) ^ (-(1 / 2 : ℝ)) :=
        Continuous.rpow_const (by fun_prop) fun v => Or.inl (by positivity)
      calc ∫ v in Icc (-vs) vs, (1 + |v|) ^ (-(5 / 2 : ℝ)) * ((π ^ 2 / 6) ^ 2 * v ^ 2)
          ≤ ∫ v in Icc (-vs) vs, (π ^ 2 / 6) ^ 2 * (1 + |v|) ^ (-(1 / 2 : ℝ)) := by
            refine setIntegral_mono_on ((hc5.mul (by fun_prop)).integrableOn_Icc) ((hc.const_mul _).integrableOn_Icc)
              measurableSet_Icc fun v _ => ?_
            have h0 : 0 < 1 + |v| := by positivity
            have hv2 : v ^ 2 ≤ (1 + |v|) ^ 2 := by nlinarith [abs_nonneg v, sq_abs v]
            have e : (1 + |v|) ^ (-(1 / 2 : ℝ)) = (1 + |v|) ^ (-(5 / 2 : ℝ)) * (1 + |v|) ^ (2 : ℝ) := by
              rw [← Real.rpow_add h0]; norm_num
            rw [e, Real.rpow_two]
            have : 0 ≤ (1 + |v|) ^ (-(5 / 2 : ℝ)) := by positivity
            have hp : 0 ≤ (π ^ 2 / 6) ^ 2 := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hv2 (mul_nonneg this hp)]
        _ = (π ^ 2 / 6) ^ 2 * ∫ v in Icc (-vs) vs, (1 + |v|) ^ (-(1 / 2 : ℝ)) := integral_const_mul _ _
        _ ≤ (π ^ 2 / 6) ^ 2 * (4 * (1 + vs) ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left (integral_Icc_one_add_abs_rpow_neg_half_le hvs) (by positivity)
    rw [div_le_div_iff₀ (by positivity) hA2]
    have h3 : (π ^ 2 / 6) ^ 2 * (4 * (1 + vs) ^ (1 / 2 : ℝ)) ≤ (π ^ 2 / 6) ^ 2 * (4 * (V * A ^ 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h4 : 48 * Ca * (∫ v in Icc (-vs) vs, (1 + |v|) ^ (-(5 / 2 : ℝ)) * ((π ^ 2 / 6) ^ 2 * v ^ 2)) ≤
        48 * (Ca * (π ^ 2 / 6) ^ 2 * (4 * V)) * A ^ 2 := by
      calc 48 * Ca * (∫ v in Icc (-vs) vs, (1 + |v|) ^ (-(5 / 2 : ℝ)) * ((π ^ 2 / 6) ^ 2 * v ^ 2))
          ≤ 48 * Ca * ((π ^ 2 / 6) ^ 2 * (4 * (V * A ^ 2))) :=
            mul_le_mul_of_nonneg_left (hint.trans h3) (by positivity)
        _ = 48 * (Ca * (π ^ 2 / 6) ^ 2 * (4 * V)) * A ^ 2 := by ring
    calc 48 * Ca * (∫ v in Icc (-vs) vs, (1 + |v|) ^ (-(5 / 2 : ℝ)) * ((π ^ 2 / 6) ^ 2 * v ^ 2)) * A ^ 2
        ≤ 48 * (Ca * (π ^ 2 / 6) ^ 2 * (4 * V)) * A ^ 2 * A ^ 2 := mul_le_mul_of_nonneg_right h4 hA2.le
      _ ≤ 48 * C4 * A ^ 4 := by rw [hA4]; nlinarith [mul_nonneg hA2.le hA2.le]
  · -- case `D ≤ A`
    have hw : ∀ v : ℝ, (1 + |v|) ^ (-(5 / 2 : ℝ)) * (4 * K * A ^ 2 * (1 + |v|) ^ (-(2 : ℝ))) = 4 * K * A ^ 2 * (1 + |v|) ^ (-(9 / 2 : ℝ)) := fun v => by
      have h0 : 0 < 1 + |v| := by positivity
      have : (1 + |v|) ^ (-(9 / 2 : ℝ)) = (1 + |v|) ^ (-(5 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ)) := by
        rw [← Real.rpow_add h0]; norm_num
      rw [this]; ring
    have hc5 : Continuous fun v : ℝ => (1 + |v|) ^ (-(5 / 2 : ℝ)) :=
      Continuous.rpow_const (by fun_prop) fun v => Or.inl (by positivity)
    have hc2 : Continuous fun v : ℝ => (1 + |v|) ^ (-(2 : ℝ)) :=
      Continuous.rpow_const (by fun_prop) fun v => Or.inl (by positivity)
    have key := smooth_ibp_key hCa hA hvs ha1 ha2 hsupp hb0 hb1 hb2 hψ hψ1 hψ2 hψ3 (fun v => 4 * K * A ^ 2 * (1 + |v|) ^ (-(2 : ℝ)))
      (fun v hv => by
        have h2' := hψ2' v hv
        have h2a := hψ2 v hv
        have hvabs : 0 < |v| := abs_pos.mpr hv
        have hsq : deriv (deriv ψ) v ^ 2 = |deriv (deriv ψ) v| ^ 2 := (sq_abs _).symm
        have hK0 : (0 : ℝ) ≤ K := by linarith
        have hA20 : 0 ≤ A ^ 2 := hA2.le
        have hA1 : 1 ≤ A ^ 2 := one_le_pow₀ hA
        have hr : (1 + |v|) ^ (-(2 : ℝ)) = ((1 + |v|) ^ 2)⁻¹ := by
          rw [Real.rpow_neg (by positivity), Real.rpow_two]
        rw [hsq, hr]
        rcases le_or_gt |v| 1 with hv1 | hv1
        · have : |deriv (deriv ψ) v| ^ 2 ≤ K := by
            calc |deriv (deriv ψ) v| ^ 2 ≤ (π ^ 2 / 6 * |v|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2a 2
              _ ≤ (π ^ 2 / 6) ^ 2 * 1 := by rw [mul_pow]; exact mul_le_mul_of_nonneg_left (by nlinarith [abs_nonneg v]) (by positivity)
              _ ≤ K := by linarith
          have h4 : ((1 + |v|) ^ 2)⁻¹ ≥ 1 / 4 := by
            rw [ge_iff_le, one_div, inv_le_inv₀ (by norm_num) (by positivity)]; nlinarith [abs_nonneg v]
          calc |deriv (deriv ψ) v| ^ 2 ≤ K := this
            _ = K * 1 := by ring
            _ ≤ K * A ^ 2 := mul_le_mul_of_nonneg_left hA1 hK0
            _ = 4 * K * A ^ 2 * (1 / 4) := by ring
            _ ≤ 4 * K * A ^ 2 * ((1 + |v|) ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h4 (by positivity)
        · have : |deriv (deriv ψ) v| ^ 2 ≤ A ^ 2 / |v| ^ 2 := by
            calc |deriv (deriv ψ) v| ^ 2 ≤ (D / |v|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2' 2
              _ ≤ (A / |v|) ^ 2 := pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right h2 hvabs.le) 2
              _ = A ^ 2 / |v| ^ 2 := by rw [div_pow]
          refine this.trans ?_
          rw [div_le_iff₀ (by positivity)]
          have h4 : |v| ^ 2 * ((1 + |v|) ^ 2)⁻¹ * 4 ≥ 1 := by
            have hp : 0 < (1 + |v|) ^ 2 := by positivity
            rw [ge_iff_le, ← sub_nonneg]
            have e : |v| ^ 2 * ((1 + |v|) ^ 2)⁻¹ * 4 - 1 = (4 * |v| ^ 2 - (1 + |v|) ^ 2) / (1 + |v|) ^ 2 := by
              field_simp
            rw [e]
            exact div_nonneg (by nlinarith) hp.le
          have hpos : (0 : ℝ) ≤ |v| ^ 2 * ((1 + |v|) ^ 2)⁻¹ * 4 := by positivity
          calc A ^ 2 = A ^ 2 * 1 := by ring
            _ ≤ A ^ 2 * (|v| ^ 2 * ((1 + |v|) ^ 2)⁻¹ * 4) := mul_le_mul_of_nonneg_left h4 hA20
            _ ≤ A ^ 2 * (|v| ^ 2 * ((1 + |v|) ^ 2)⁻¹ * 4) * K := le_mul_of_one_le_right (mul_nonneg hA20 hpos) hK1
            _ = 4 * K * A ^ 2 * ((1 + |v|) ^ 2)⁻¹ * |v| ^ 2 := by ring)
      (Continuous.integrableOn_Icc (hc5.mul (continuous_const.mul hc2)))
    refine hfinal _ ?_ _ key
    have hint : ∫ v in Icc (-vs) vs, (1 + |v|) ^ (-(5 / 2 : ℝ)) * (4 * K * A ^ 2 * (1 + |v|) ^ (-(2 : ℝ))) ≤ 4 * K * A ^ 2 * J9 := by
      simp_rw [hw]
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left (setIntegral_le_integral (integrable_w0 (r := 9 / 2) (by norm_num)) (ae_of_all _ fun v => by positivity)) (by positivity)
    rw [div_le_div_iff₀ (by positivity) hA2]
    have h4 : 48 * Ca * (∫ v in Icc (-vs) vs, (1 + |v|) ^ (-(5 / 2 : ℝ)) * (4 * K * A ^ 2 * (1 + |v|) ^ (-(2 : ℝ)))) ≤
        48 * (Ca * (4 * K) * J9) * A ^ 2 := by
      calc 48 * Ca * (∫ v in Icc (-vs) vs, (1 + |v|) ^ (-(5 / 2 : ℝ)) * (4 * K * A ^ 2 * (1 + |v|) ^ (-(2 : ℝ))))
          ≤ 48 * Ca * (4 * K * A ^ 2 * J9) := mul_le_mul_of_nonneg_left hint (by positivity)
        _ = 48 * (Ca * (4 * K) * J9) * A ^ 2 := by ring
    have hQ : Ca * (4 * K) * J9 ≤ C4 := le_max_right _ _
    calc 48 * Ca * (∫ v in Icc (-vs) vs, (1 + |v|) ^ (-(5 / 2 : ℝ)) * (4 * K * A ^ 2 * (1 + |v|) ^ (-(2 : ℝ)))) * A ^ 2
        ≤ 48 * (Ca * (4 * K) * J9) * A ^ 2 * A ^ 2 := mul_le_mul_of_nonneg_right h4 hA2.le
      _ ≤ 48 * C4 * A ^ 4 := by rw [hA4]; nlinarith [mul_nonneg hA2.le hA2.le]

/-! ### The cut-off amplitude `a = χ₀(v/v_*) g G` -/

lemma deriv_comp_div {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) {vs : ℝ} (hvs : vs ≠ 0) (v : ℝ) :
    deriv (fun x => f (x / vs)) v = (1 / vs : ℝ) • deriv f (v / vs) := by
  have h1 : HasDerivAt (fun x : ℝ => x / vs) (1 / vs) v := by
    simpa using (hasDerivAt_id v).div_const vs
  have := ((hf.differentiable (by norm_num) (v / vs)).hasDerivAt).scomp v h1
  exact this.deriv

lemma bd2_scale {f : ℝ → ℂ} {B0 B1 B2 vs : ℝ} (hvs : 1 ≤ vs) (hf : Bd2 univ f B0 B1 B2) :
    Bd2 univ (fun v => f (v / vs)) B0 B1 B2 := by
  have hvs0 : vs ≠ 0 := by positivity
  have hcd : ContDiff ℝ 2 (fun v => f (v / vs)) := hf.1.comp (contDiff_id.div_const vs)
  have hdf : ContDiff ℝ 1 (deriv f) := (contDiff_succ_iff_deriv (n := 1)).mp (by simpa [one_add_one_eq_two] using hf.1) |>.2.2
  have hn1 : 0 ≤ B1 := (norm_nonneg _).trans (hf.2 0 (mem_univ _)).2.1
  have hn2 : 0 ≤ B2 := (norm_nonneg _).trans (hf.2 0 (mem_univ _)).2.2
  have hd1 : deriv (fun v => f (v / vs)) = fun v => (1 / vs : ℝ) • deriv f (v / vs) := funext fun v => deriv_comp_div hf.1 hvs0 v
  have hd2 : ∀ v, deriv (deriv (fun v => f (v / vs))) v = (1 / vs : ℝ) • ((1 / vs : ℝ) • deriv (deriv f) (v / vs)) := fun v => by
    rw [hd1]
    have h1 : HasDerivAt (fun x : ℝ => x / vs) (1 / vs) v := by simpa using (hasDerivAt_id v).div_const vs
    have := (((hdf.differentiable one_ne_zero (v / vs)).hasDerivAt).scomp v h1).const_smul (1 / vs : ℝ)
    exact this.deriv
  have hivs : (1 / vs : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hvs
  have hivs0 : 0 ≤ (1 / vs : ℝ) := by positivity
  refine ⟨hcd, fun v _ => ⟨(hf.2 (v / vs) (mem_univ _)).1, ?_, ?_⟩⟩
  · rw [hd1]; dsimp only
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hivs0]
    calc 1 / vs * ‖deriv f (v / vs)‖ ≤ 1 * B1 := mul_le_mul hivs (hf.2 (v / vs) (mem_univ _)).2.1 (norm_nonneg _) zero_le_one
      _ = B1 := one_mul _
  · rw [hd2, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hivs0]
    calc 1 / vs * (1 / vs * ‖deriv (deriv f) (v / vs)‖) ≤ 1 * (1 * B2) := by
          exact mul_le_mul hivs (mul_le_mul hivs (hf.2 (v / vs) (mem_univ _)).2.2 (norm_nonneg _) zero_le_one) (by positivity) zero_le_one
      _ = B2 := by ring

/-- The regularity of the subtracted symbol `G_sm` needed for the smooth part of Piece C (the `|G_sm| , |G_sm'| ≲ (1+|v|)^{-5/2}`,
`|G_sm''| ≲ |v|^{-1/2}(1+|v|)^{-2}` bounds of paper Piece C item 1, with `G_sm ∈ C¹` and `G_sm'` differentiable off `0`). This is the interface through which the seed data (`U.1`/`(e27)` for `f₁, g₁, g₁'`, i.e. the square-root
structure at `v = 0` and the symbol decay `|∂^r G_sm| ≲ |v|^{-5/2-r}`) enters; `airySeedU2_smoothSymbol` (`SeedSqrtForm.lean`) proves it for the
actual `G_sm` of every one-level seed. Negative regression: with `γ₀ = 0` (no branch point) the structure asks `G = X̃(i c_s ·)` itself to be `C¹`
off no singularity, and `pieceC_main_term_smooth` then has main term `0`, i.e. `I_C = O(ξ⁻¹A⁻²)` with no `A^{-3/2}` term. -/
structure SmoothSymbol (G : ℝ → ℂ) (CG : ℝ) : Prop where
  contDiff : ContDiff ℝ 1 G
  diff2 : ∀ x : ℝ, x ≠ 0 → DifferentiableAt ℝ (deriv G) x
  b0 : ∀ v : ℝ, ‖G v‖ ≤ CG * (1 + |v|) ^ (-(5 / 2 : ℝ))
  b1 : ∀ v : ℝ, ‖deriv G v‖ ≤ CG * (1 + |v|) ^ (-(5 / 2 : ℝ))
  b2 : ∀ v : ℝ, v ≠ 0 → ‖deriv (deriv G) v‖ ≤ CG * (|v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ)))

lemma w0_le_W2 {v : ℝ} (hv : v ≠ 0) :
    (1 + |v|) ^ (-(5 / 2 : ℝ)) ≤ |v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ)) := by
  have hv0 : 0 < |v| := abs_pos.mpr hv
  have h0 : 0 < 1 + |v| := by positivity
  have e : (1 + |v|) ^ (-(5 / 2 : ℝ)) = (1 + |v|) ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add h0]; norm_num
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact Real.rpow_le_rpow_of_nonpos hv0 (by linarith) (by norm_num)

theorem smooth_amp_data {f1 G : ℝ → ℂ} {F0 F1 F2 CG : ℝ} (hf1 : Bd2 univ f1 F0 F1 F2) (hG : SmoothSymbol G CG) :
    ContDiff ℝ 1 (fun v => f1 v * G v) ∧ (∀ x : ℝ, x ≠ 0 → DifferentiableAt ℝ (deriv (fun v => f1 v * G v)) x) ∧
    (∀ v : ℝ, ‖f1 v * G v‖ ≤ (2 * CG * (F0 + F1 + F2)) * (1 + |v|) ^ (-(5 / 2 : ℝ))) ∧
    (∀ v : ℝ, ‖deriv (fun v => f1 v * G v) v‖ ≤ (2 * CG * (F0 + F1 + F2)) * (1 + |v|) ^ (-(5 / 2 : ℝ))) ∧
    (∀ v : ℝ, v ≠ 0 → ‖deriv (deriv (fun v => f1 v * G v)) v‖ ≤
      (2 * CG * (F0 + F1 + F2)) * (|v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ)))) := by
  have hF0 : 0 ≤ F0 := (norm_nonneg _).trans (hf1.2 0 (mem_univ _)).1
  have hF1 : 0 ≤ F1 := (norm_nonneg _).trans (hf1.2 0 (mem_univ _)).2.1
  have hF2 : 0 ≤ F2 := (norm_nonneg _).trans (hf1.2 0 (mem_univ _)).2.2
  have hCG : 0 ≤ CG := by
    have := hG.b0 0
    have h0 : 0 < (1 + |(0 : ℝ)|) ^ (-(5 / 2 : ℝ)) := by positivity
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans this) h0
  have hGd : Differentiable ℝ G := hG.contDiff.differentiable one_ne_zero
  have hdG : ContinuousAt (deriv G) 0 := (hG.contDiff.continuous_deriv le_rfl).continuousAt
  have hdf1 : ContDiff ℝ 1 (deriv f1) := (contDiff_succ_iff_deriv (n := 1)).mp (by simpa [one_add_one_eq_two] using hf1.1) |>.2.2
  have hd1 : deriv (fun v => f1 v * G v) = fun v => deriv f1 v * G v + f1 v * deriv G v := funext fun v =>
    deriv_mul (hf1.1.differentiable (by norm_num) v) (hGd v)
  refine ⟨((hf1.1.of_le (by norm_num)).mul hG.contDiff), fun x hx => ?_, fun v => ?_, fun v => ?_, fun v hv => ?_⟩
  · rw [hd1]
    exact ((hdf1.differentiable one_ne_zero x).mul (hGd x)).add ((hf1.1.differentiable (by norm_num) x).mul (hG.diff2 x hx))
  · obtain ⟨h0, h1, h2⟩ := hf1.2 v (mem_univ _)
    rw [norm_mul]
    have hw : 0 ≤ (1 + |v|) ^ (-(5 / 2 : ℝ)) := by positivity
    calc ‖f1 v‖ * ‖G v‖ ≤ F0 * (CG * (1 + |v|) ^ (-(5 / 2 : ℝ))) := mul_le_mul h0 (hG.b0 v) (norm_nonneg _) hF0
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hCG hw) hF1, mul_nonneg (mul_nonneg hCG hw) hF2, mul_nonneg (mul_nonneg hCG hw) hF0]
  · obtain ⟨h0, h1, h2⟩ := hf1.2 v (mem_univ _)
    rw [hd1]; dsimp only
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hw : 0 ≤ (1 + |v|) ^ (-(5 / 2 : ℝ)) := by positivity
    have e1 := mul_le_mul h1 (hG.b0 v) (norm_nonneg _) hF1
    have e2 := mul_le_mul h0 (hG.b1 v) (norm_nonneg _) hF0
    nlinarith [mul_nonneg (mul_nonneg hCG hw) hF1, mul_nonneg (mul_nonneg hCG hw) hF2, mul_nonneg (mul_nonneg hCG hw) hF0]
  · obtain ⟨h0, h1, h2⟩ := hf1.2 v (mem_univ _)
    have hdd : deriv (deriv (fun v => f1 v * G v)) v = deriv (deriv f1) v * G v + 2 * (deriv f1 v * deriv G v) + f1 v * deriv (deriv G) v := by
      rw [hd1]
      have a1 := hdf1.differentiable one_ne_zero v
      have a2 := hGd v
      have a3 := hf1.1.differentiable (by norm_num) v
      have a4 := hG.diff2 v hv
      have := ((a1.hasDerivAt.mul a2.hasDerivAt).add (a3.hasDerivAt.mul a4.hasDerivAt)).deriv
      refine this.trans ?_
      ring
    rw [hdd]
    have hw := w0_le_W2 hv
    have hw0 : 0 ≤ (1 + |v|) ^ (-(5 / 2 : ℝ)) := by positivity
    have hW : 0 ≤ |v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ)) := by positivity
    refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    have h2' : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2']
    have e0 := mul_le_mul h2 (hG.b0 v) (norm_nonneg _) hF2
    have e1 := mul_le_mul h1 (hG.b1 v) (norm_nonneg _) hF1
    have e2 := mul_le_mul h0 (hG.b2 v hv) (norm_nonneg _) hF0
    have k0 : CG * (1 + |v|) ^ (-(5 / 2 : ℝ)) ≤ CG * (|v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ))) := mul_le_mul_of_nonneg_left hw hCG
    nlinarith [mul_le_mul_of_nonneg_left k0 hF0, mul_le_mul_of_nonneg_left k0 hF1, mul_le_mul_of_nonneg_left k0 hF2,
      mul_nonneg hF0 (mul_nonneg hCG hW), mul_nonneg hF1 (mul_nonneg hCG hW), mul_nonneg hF2 (mul_nonneg hCG hW)]

lemma bd2_chi {χ₀ : ℝ → ℝ} {Kχ : ℝ} (hχ : ContDiff ℝ 2 χ₀) (h0 : ∀ u, |χ₀ u| ≤ Kχ) (h1 : ∀ u, |deriv χ₀ u| ≤ Kχ)
    (h2 : ∀ u, |deriv (deriv χ₀) u| ≤ Kχ) : Bd2 univ (fun u : ℝ => (χ₀ u : ℂ)) Kχ Kχ Kχ := by
  have hd1 : deriv (fun u : ℝ => (χ₀ u : ℂ)) = fun u => ((deriv χ₀ u : ℝ) : ℂ) := funext fun u =>
    ((hχ.differentiable (by norm_num) u).hasDerivAt.ofReal_comp).deriv
  have hdχ : ContDiff ℝ 1 (deriv χ₀) := (contDiff_succ_iff_deriv (n := 1)).mp (by simpa [one_add_one_eq_two] using hχ) |>.2.2
  have hd2 : ∀ u, deriv (deriv (fun u : ℝ => (χ₀ u : ℂ))) u = ((deriv (deriv χ₀) u : ℝ) : ℂ) := fun u => by
    rw [hd1]; exact ((hdχ.differentiable one_ne_zero u).hasDerivAt.ofReal_comp).deriv
  refine ⟨Complex.ofRealCLM.contDiff.comp hχ, fun u _ => ⟨?_, ?_, ?_⟩⟩
  · rw [Complex.norm_real, Real.norm_eq_abs]; exact h0 u
  · rw [hd1]; dsimp only; rw [Complex.norm_real, Real.norm_eq_abs]; exact h1 u
  · rw [hd2, Complex.norm_real, Real.norm_eq_abs]; exact h2 u

lemma contDiff_pcPhase (c ξ : ℝ) : ContDiff ℝ 3 (pcPhase c ξ) := by
  unfold pcPhase
  exact ((contDiff_const.mul contDiff_id).sub (contDiff_const.mul (contDiff_id.pow 3))).add
    (contDiff_const.mul (edgeR_contDiff.comp (contDiff_const.mul contDiff_id)))

/-- **Piece C, smooth part: `hsmooth` of `pieceC_main_term` from `two_ibp_phase`.** The amplitude `a = χ₀(v/v_*) g G` (with
`G = G_sm` of `SmoothSymbol`), the phase `ψ = pcPhase` with `ψ' ≥ A/2` on `[-v_*, v_*]` (`pcPhase_psibd`, `ε v_* ≤ τ_*(L)`),
and the case condition `√(1+v_*) ≤ V A²` or `c^{2/3} ≤ A` (`L ≤ 1`, `L > 1` of the paper) give
`|∫ χ₀ g e^{iψ} G| ≤ C_s / A²`, `C_s = smoothConst (2 C_G (F₀+F₁+F₂)) V`, uniform in `c ≥ 2`, `ξ`. -/
theorem pieceC_hsmooth (δ₀ : ℝ) (m : ℕ) {c : ℝ} (hc : 2 ≤ c) {ξ : ℝ} (hL : 0 < Real.log (Real.pi ^ 2 * ξ))
    (χ₀ : ℝ → ℝ) (vs : ℝ) (hvs1 : 1 ≤ vs) (hχ₀ : ContDiff ℝ 2 χ₀) (hχ₀s : ∀ u : ℝ, 1 < |u| → χ₀ u = 0) {Kχ : ℝ}
    (k0 : ∀ u, |χ₀ u| ≤ Kχ) (k1 : ∀ u, |deriv χ₀ u| ≤ Kχ) (k2 : ∀ u, |deriv (deriv χ₀) u| ≤ Kχ)
    {B0 B1 B2 : ℝ} (hg : Bd2 univ (pcAmp δ₀ m c) B0 B1 B2) {G : ℝ → ℂ} {CG : ℝ} (hG : SmoothSymbol G CG)
    {A : ℝ} (hAdef : A = c * liftEps c * Real.log (Real.pi ^ 2 * ξ)) (hA : 1 ≤ A)
    (hvsτ : liftEps c * vs ≤ tauStar (Real.log (Real.pi ^ 2 * ξ))) {V : ℝ} (hV : 0 ≤ V)
    (hcase : (1 + vs) ^ (1 / 2 : ℝ) ≤ V * A ^ 2 ∨ c ^ (2 / 3 : ℝ) ≤ A) :
    ‖∫ v : ℝ, (χ₀ (v / vs) : ℂ) * (pcAmp δ₀ m c v * Complex.exp (Complex.I * (pcPhase c ξ v : ℝ)) * G v)‖ ≤
      smoothConst (2 * CG * (Kχ * B0 + (Kχ * B0 + Kχ * B1) + (Kχ * B0 + 2 * (Kχ * B1) + Kχ * B2))) V / A ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hε := liftEps_pos hc0
  have hχB := bd2_scale hvs1 (bd2_chi hχ₀ k0 k1 k2)
  have hf1 := hχB.mul hg
  obtain ⟨d1, d2, e0, e1, e2⟩ := smooth_amp_data hf1 hG
  have hF0 : 0 ≤ Kχ * B0 := (norm_nonneg _).trans (hf1.2 0 (mem_univ _)).1
  have hF1 : 0 ≤ Kχ * B0 + Kχ * B1 := (norm_nonneg _).trans (hf1.2 0 (mem_univ _)).2.1
  have hF2 : 0 ≤ Kχ * B0 + 2 * (Kχ * B1) + Kχ * B2 := (norm_nonneg _).trans (hf1.2 0 (mem_univ _)).2.2
  have hCG : 0 ≤ CG := by
    have := hG.b0 0
    have h0 : 0 < (1 + |(0 : ℝ)|) ^ (-(5 / 2 : ℝ)) := by positivity
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans this) h0
  have hCa : 0 ≤ 2 * CG * (Kχ * B0 + (Kχ * B0 + Kχ * B1) + (Kχ * B0 + 2 * (Kχ * B1) + Kχ * B2)) := by positivity
  obtain ⟨p1, p2, p3⟩ := pcPhase_psibd hc0 hL
  have hψ : ContDiff ℝ 3 (pcPhase c ξ) := by
    unfold pcPhase
    exact ((contDiff_const.mul contDiff_id).sub (contDiff_const.mul (contDiff_id.pow 3))).add
      (contDiff_const.mul (edgeR_contDiff.comp (contDiff_const.mul contDiff_id)))
  have hbound := smooth_ibp_bound (Ca := 2 * CG * (Kχ * B0 + (Kχ * B0 + Kχ * B1) + (Kχ * B0 + 2 * (Kχ * B1) + Kχ * B2))) hCa hV
    (a := fun v => (χ₀ (v / vs) : ℂ) * pcAmp δ₀ m c v * G v) (ψ := pcPhase c ξ) (vs := vs) (A := A) (D := c ^ (2 / 3 : ℝ))
    hA (by linarith) (by positivity) d1 d2
    (fun x hx => by
      have hx1 : 1 < |x / vs| := by
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < vs), lt_div_iff₀ (by linarith)]
        rcases not_and_or.mp (fun h => hx (mem_Icc.mpr h)) with h | h
        · rw [not_le] at h; rw [abs_of_neg (by linarith)]; linarith
        · rw [not_le] at h; rw [abs_of_pos (by linarith)]; linarith
      simp [hχ₀s _ hx1])
    e0 e1 e2 hψ
    (fun v hv => by
      rw [hAdef]
      refine p1 v ?_
      rw [abs_mul, abs_of_pos hε]
      have : |v| ≤ vs := abs_le.mpr hv
      calc liftEps c * |v| ≤ liftEps c * vs := mul_le_mul_of_nonneg_left this hε.le
        _ ≤ _ := hvsτ)
    (fun v hv => (p2 v hv).trans (min_le_left _ _))
    (fun v hv => (p2 v hv).trans (min_le_right _ _)) p3 hcase
  refine le_of_eq_of_le ?_ hbound
  congr 1
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only
  ring

/-- **Piece C main term with the smooth part discharged.** `pieceC_main_term` with `hsmooth` replaced by the regularity of the
subtracted symbol `G_sm` (`SmoothSymbol`), the cut-off `χ₀`, the phase condition `ε v_* ≤ τ_*(L)` and the case condition of
the paper (`√(1+v_*) ≤ V A²` for `L ≤ 1`, `c^{2/3} ≤ A` for `L > 1`); the smooth part is bounded by `two_ibp_phase`
(`pieceC_hsmooth`), with the error constant `C_s = smoothConst (2 C_G (F₀+F₁+F₂)) V`. -/
theorem pieceC_main_term_smooth (X : ℝ → ℝ) (δ₀ : ℝ) (m : ℕ) {c : ℝ} (hc : 2 ≤ c) {ξ : ℝ} (hξ : 0 < ξ)
    (hL : 0 < Real.log (Real.pi ^ 2 * ξ)) (γ₀ : ℝ) (χ₀ χ₁ : ℝ → ℝ) (vs : ℝ) (hvs1 : 1 ≤ vs)
    (hχ0 : ∀ v, χ₁ v ≠ 0 → χ₀ (v / vs) = 1) (hχ1_0 : χ₁ 0 = 1) (hsupp : ∀ v : ℝ, 1 < |v| → χ₁ v = 0)
    (hχ₀ : ContDiff ℝ 2 χ₀) (hχ₀s : ∀ u : ℝ, 1 < |u| → χ₀ u = 0) {Kχ : ℝ}
    (k0 : ∀ u, |χ₀ u| ≤ Kχ) (k1 : ∀ u, |deriv χ₀ u| ≤ Kχ) (k2 : ∀ u, |deriv (deriv χ₀) u| ≤ Kχ)
    (hχ₁c : Continuous χ₁)
    (hφ : ContDiff ℝ 2 (fun v : ℝ => (χ₁ v : ℂ) * pcH δ₀ m c v)) {M : ℝ}
    (b0 : ∀ v, ‖(χ₁ v : ℂ) * pcH δ₀ m c v‖ ≤ M)
    (b1 : ∀ v, ‖deriv (fun v : ℝ => (χ₁ v : ℂ) * pcH δ₀ m c v) v‖ ≤ M)
    (b2 : ∀ v, ‖deriv (deriv (fun v : ℝ => (χ₁ v : ℂ) * pcH δ₀ m c v)) v‖ ≤ M)
    {A : ℝ} (hAdef : A = c * liftEps c * Real.log (Real.pi ^ 2 * ξ)) (hA : 1 ≤ A)
    {B0 B1 B2 : ℝ} (hg : Bd2 univ (pcAmp δ₀ m c) B0 B1 B2) {CG : ℝ}
    (hG : SmoothSymbol (fun v : ℝ => airyTwistedLaplaceC X ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) +
        (γ₀ : ℂ) * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) * Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) * (χ₁ v : ℂ)) CG)
    (hvsτ : liftEps c * vs ≤ tauStar (Real.log (Real.pi ^ 2 * ξ))) {V : ℝ} (hV : 0 ≤ V)
    (hcase : (1 + vs) ^ (1 / 2 : ℝ) ≤ V * A ^ 2 ∨ c ^ (2 / 3 : ℝ) ≤ A) :
    ‖((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * (∫ v : ℝ, (χ₀ (v / vs) : ℂ) * iMainIntegrand X δ₀ m c ξ v) -
        ((γ₀ * Real.sqrt Real.pi * A ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ)‖ ≤
      (smoothConst (2 * CG * (Kχ * B0 + (Kχ * B0 + Kχ * B1) + (Kχ * B0 + 2 * (Kχ * B1) + Kχ * B2))) V +
        |γ₀| * ((12 * (∫ t in Ioi (0 : ℝ), fresnelDom t) + 2) * M)) / (2 * Real.pi * ξ * A ^ 2) :=
  pieceC_main_term X δ₀ m (by linarith) hξ γ₀ χ₀ χ₁ vs hχ0 hχ1_0 hsupp hφ b0 b1 b2 hAdef hA
    (by
      have hc0 : 0 < c := by linarith
      have hcont : Continuous fun v : ℝ => (χ₀ (v / vs) : ℂ) * (pcAmp δ₀ m c v * Complex.exp (Complex.I * (pcPhase c ξ v : ℝ)) *
          (airyTwistedLaplaceC X ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) +
            (γ₀ : ℂ) * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) * Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) * (χ₁ v : ℂ))) :=
        (Complex.continuous_ofReal.comp (hχ₀.continuous.comp (continuous_id.div_const vs))).mul
          ((hg.1.continuous.mul (Complex.continuous_exp.comp (continuous_const.mul
            (Complex.continuous_ofReal.comp (contDiff_pcPhase c ξ).continuous)))).mul hG.contDiff.continuous)
      refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_Icc (a := -vs) (b := vs)) fun v hv => ?_)
      have hv' : vs < |v| := by
        by_contra h; exact hv ⟨(abs_le.mp (not_lt.mp h)).1, (abs_le.mp (not_lt.mp h)).2⟩
      have hx1 : 1 < |v / vs| := by
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < vs), lt_div_iff₀ (by linarith)]; linarith
      simp [hχ₀s _ hx1])
    (by
      have hcont : Continuous fun v : ℝ => (χ₀ (v / vs) : ℂ) * ((γ₀ : ℂ) * pcH δ₀ m c v * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) * (χ₁ v : ℂ) *
          Complex.exp (Complex.I * ((c * liftEps c * Real.log (Real.pi ^ 2 * ξ) : ℝ) : ℂ) * (v : ℂ))) := by
        have hsq : Continuous fun v : ℝ => (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) :=
          continuous_iff_continuousAt.mpr fun v => (Complex.continuousAt_cpow_const_of_re_pos (Or.inl (by simp)) (by norm_num)).comp
            (by fun_prop : Continuous fun v : ℝ => Complex.I * (v : ℂ)).continuousAt
        exact (Complex.continuous_ofReal.comp (hχ₀.continuous.comp (continuous_id.div_const vs))).mul
          ((((continuous_const.mul (contDiff_pcH δ₀ m (by linarith)).continuous).mul hsq).mul
            (Complex.continuous_ofReal.comp hχ₁c)).mul (by fun_prop))
      refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun v hv => ?_)
      have hv' : 1 < |v| := by
        by_contra h; exact hv ⟨(abs_le.mp (not_lt.mp h)).1, (abs_le.mp (not_lt.mp h)).2⟩
      simp [hsupp v hv'])
    (pieceC_hsmooth δ₀ m hc hL χ₀ vs hvs1 hχ₀ hχ₀s k0 k1 k2 hg hG hAdef hA hvsτ hV hcase)

/-- info: 'FormalResearch.CohnElkies.smooth_ibp_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.smooth_ibp_bound
/-- info: 'FormalResearch.CohnElkies.pieceC_hsmooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.pieceC_hsmooth
/-- info: 'FormalResearch.CohnElkies.pieceC_main_term_smooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.pieceC_main_term_smooth

end FormalResearch.CohnElkies
