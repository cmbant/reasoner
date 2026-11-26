module

public import Mathlib
public import FormalResearch.SignUncertainty.CtHalfDiscPoisson

/-!
# `ct:dyadic` Part (2): the area and Lipschitz bounds for the half-disc Poisson kernel (P2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:dyadic` Part (2).  With `A = 4 r_*`,
`N₊ = {r/2 ≤ |z| ≤ 3r, Im z > 0}` (`nPlus`) and `|t| ≤ r/4`:

* `pDiam_area`: `∫_{N₊} P(z,t) dA(z) ≤ 7 r` (TeX: `6 r`; the constant `7` comes from `P ≤ 1/(π|z-t|)` and
  `N₊ - t ⊂ B(0, 7r/2)`, `∫_{B(0,ρ)} 1/(π|w|) = 2ρ`, via `integral_fun_norm_addHaar`);
* `pDiam_lipschitz`: `|P(z,t) - P(z,0)| ≤ 400 |t| / r²` (TeX: `123`; same difference-of-reciprocals argument).

**Proved**, with worse absolute constants than the TeX; downstream uses only that these are absolute constants.
-/

@[expose] public section

open Complex Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtHalfDiscPoisson

/-- The truncated kernel `1_{|w|<ρ} / (π|w|)` on `ℂ`. -/
noncomputable def invKer (ρ : ℝ) (w : ℂ) : ℝ := (Iio ρ).indicator (fun y : ℝ => 1 / (π * y)) ‖w‖

lemma invKer_eq (ρ : ℝ) : (fun w : ℂ => invKer ρ w) =
    fun w => (Metric.ball (0 : ℂ) ρ).indicator (fun w : ℂ => 1 / (π * ‖w‖)) w := by
  ext w
  by_cases h : ‖w‖ < ρ <;> simp [invKer, indicator, h]

lemma invKer_integrable {ρ : ℝ} (hρ : 0 < ρ) : Integrable (invKer ρ) volume := by
  have h := (integrableOn_fun_norm_addHaar (volume : Measure ℂ) (f := fun y : ℝ => 1 / (π * y))
    (r := ρ)).2 (by
      have : IntegrableOn (fun _ : ℝ => (1 / π : ℝ)) (Ioo 0 ρ) volume := by
        simp
      refine this.congr_fun (fun y hy => ?_) measurableSet_Ioo
      have hy0 : 0 < y := hy.1
      simp only [Complex.finrank_real_complex, smul_eq_mul]
      norm_num
      field_simp [Real.pi_pos.ne'])
  have e : invKer ρ = _ := invKer_eq ρ
  rw [e]
  exact (integrable_indicator_iff Metric.isOpen_ball.measurableSet).2 (by simpa using h)

lemma invKer_integral {ρ : ℝ} (hρ : 0 < ρ) : ∫ w, invKer ρ w = 2 * ρ := by
  have h := integral_fun_norm_addHaar (volume : Measure ℂ)
    ((Iio ρ).indicator (fun y : ℝ => 1 / (π * y)))
  unfold invKer
  rw [h]
  have hb : (volume : Measure ℂ).real (Metric.ball 0 1) = π := by
    simp [Measure.real, Complex.volume_ball]
  rw [hb]
  have : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) •
      (Iio ρ).indicator (fun y : ℝ => 1 / (π * y)) y = ρ / π := by
    have e : ∀ y ∈ Ioi (0:ℝ), y ^ (Module.finrank ℝ ℂ - 1) •
        (Iio ρ).indicator (fun y : ℝ => 1 / (π * y)) y
        = (Ioo 0 ρ).indicator (fun _ => 1 / π) y := by
      intro y hy
      have hy0 : 0 < y := hy
      by_cases hyr : y < ρ
      · simp [Complex.finrank_real_complex, hyr, hy0, indicator]
        field_simp [Real.pi_pos.ne']
      · simp [Complex.finrank_real_complex, hyr, indicator]
    rw [setIntegral_congr_fun measurableSet_Ioi e]
    rw [setIntegral_indicator measurableSet_Ioo]
    have : Ioi (0:ℝ) ∩ Ioo 0 ρ = Ioo 0 ρ := by
      ext y; simp only [mem_inter_iff, mem_Ioi, mem_Ioo]; tauto
    rw [this, setIntegral_const]
    simp [Measure.real, Real.volume_Ioo, hρ.le]
    field_simp
  rw [this]
  simp [Complex.finrank_real_complex]
  field_simp [Real.pi_pos.ne']

/-- The annular half-disc `N₊ = {r/2 ≤ |z| ≤ 3r, Im z > 0}` of `ct:dyadic` Part (2). -/
def nPlus (r : ℝ) : Set ℂ := {z | r / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 * r ∧ 0 < z.im}

lemma measurableSet_nPlus (r : ℝ) : MeasurableSet (nPlus r) := by
  have : nPlus r = {z : ℂ | r / 2 ≤ ‖z‖} ∩ ({z : ℂ | ‖z‖ ≤ 3 * r} ∩ {z : ℂ | 0 < z.im}) := by
    ext z; simp [nPlus]
  rw [this]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · exact measurableSet_le measurable_const (by fun_prop)
  · exact measurableSet_le (by fun_prop) measurable_const
  · exact measurableSet_lt measurable_const (by fun_prop)

lemma pDiam_le_invKer {r t : ℝ} (hr : 0 < r) (ht : |t| ≤ r / 4) {z : ℂ} (hz : z ∈ nPlus r) :
    pDiam (4 * r) z t ≤ invKer (7 * r / 2) (z - t) := by
  obtain ⟨h1, h2, h3⟩ := hz
  have hzA : Complex.normSq z < (4 * r) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith
  have htA : |t| < 4 * r := by linarith
  have := (pDiam_le h3 hzA htA).2.2
  have hn : ‖z - t‖ < 7 * r / 2 := by
    calc ‖z - t‖ ≤ ‖z‖ + ‖(t : ℂ)‖ := norm_sub_le _ _
      _ < 7 * r / 2 := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  simp only [invKer, indicator, mem_Iio, hn, ite_true]
  exact this

/-- `ct:dyadic` Part (2), area bound (P2a): `r⁻¹ ∫_{N₊} P(z,t) dA(z) ≤ 7` for `|t| ≤ r/4`, with `A = 4r`.
**Proved.**  (The TeX constant is `6`; this is the easy constant from `P ≤ 1/(π|z-t|)` and
`N₊ - t ⊂ B(0, 7r/2)`, `∫_{B(0,ρ)} 1/(π|w|) = 2ρ`.) -/
theorem pDiam_area {r t : ℝ} (hr : 0 < r) (ht : |t| ≤ r / 4) :
    ∫ z in nPlus r, pDiam (4 * r) z t ≤ 7 * r := by
  have hρ : 0 < 7 * r / 2 := by positivity
  have hint := invKer_integrable hρ
  have hshift : ∫ z : ℂ, invKer (7 * r / 2) (z - t) = 2 * (7 * r / 2) := by
    rw [integral_sub_right_eq_self (fun w => invKer (7 * r / 2) w) (t : ℂ), invKer_integral hρ]
  have hnn : ∀ z, 0 ≤ invKer (7 * r / 2) (z - t) := fun z => by
    unfold invKer indicator; split_ifs <;> positivity
  rw [← integral_indicator (measurableSet_nPlus r)]
  calc ∫ z, (nPlus r).indicator (fun z => pDiam (4 * r) z t) z
      ≤ ∫ z : ℂ, invKer (7 * r / 2) (z - t) := by
        refine integral_mono_of_nonneg ?_ ?_ ?_
        · refine Filter.Eventually.of_forall (fun z => ?_)
          by_cases hz : z ∈ nPlus r
          · simp only [indicator, hz, ite_true]
            obtain ⟨h1, h2, h3⟩ := hz
            have hzA : Complex.normSq z < (4 * r) ^ 2 := by
              rw [Complex.normSq_eq_norm_sq]; nlinarith
            exact (pDiam_le h3 hzA (by linarith)).1
          · simp [indicator, hz]
        · exact (hint.comp_sub_right (t : ℂ))
        · refine Filter.Eventually.of_forall (fun z => ?_)
          by_cases hz : z ∈ nPlus r
          · simp only [indicator, hz, ite_true]; exact pDiam_le_invKer hr ht hz
          · simp [indicator, hz, hnn z]
    _ = 7 * r := by rw [hshift]; ring

lemma lip_F {x t r P s : ℝ} (hr : 0 < r) (ht : |t| ≤ r / 4) (hx : |x| ≤ 3 * r)
    (hP : r ^ 2 / 16 ≤ P) (hs : r ^ 2 / 4 ≤ s) (h : s - P = t * (2 * x - t)) :
    |1 / P - 1 / s| ≤ 400 * |t| / r ^ 3 := by
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hP
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have e : 1 / P - 1 / s = t * (2 * x - t) / (P * s) := by
    field_simp; linarith
  rw [e, abs_div, abs_mul, abs_of_pos (mul_pos hP0 hs0), div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : |2 * x - t| ≤ 25 * r / 4 := by
    have := abs_sub (2 * x) t
    have h2 : |2 * x| = 2 * |x| := by rw [abs_mul]; norm_num
    linarith
  have h3 : r ^ 4 / 64 ≤ P * s := by nlinarith
  have h4 : |t| * |2 * x - t| ≤ |t| * (25 * r / 4) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have h5 : 0 ≤ |t| * |2 * x - t| := by positivity
  calc |t| * |2 * x - t| * r ^ 3 ≤ |t| * (25 * r / 4) * r ^ 3 := by gcongr
    _ = 400 * |t| * (r ^ 4 / 64) := by ring
    _ ≤ 400 * |t| * (P * s) := by gcongr

lemma lip_G {x t r Q s : ℝ} (hr : 0 < r) (ht : |t| ≤ r / 4) (hx : |x| ≤ 3 * r) (hs : s ≤ 9 * r ^ 2)
    (hs0 : 0 ≤ s) (hQ : 225 * r ^ 4 ≤ Q) (h : 256 * r ^ 4 - Q = t * (32 * r ^ 2 * x - t * s)) :
    |16 * r ^ 2 / Q - 16 * r ^ 2 / (256 * r ^ 4)| ≤ |t| / (30 * r ^ 3) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity) hQ
  have e : 16 * r ^ 2 / Q - 16 * r ^ 2 / (256 * r ^ 4) =
      16 * r ^ 2 * (t * (32 * r ^ 2 * x - t * s)) / (Q * (256 * r ^ 4)) := by
    rw [← h]; field_simp
  rw [e, abs_div, abs_mul (16 * r ^ 2), abs_mul t, abs_of_pos (mul_pos hQ0 (by positivity : (0:ℝ) < 256 * r ^ 4)),
    abs_of_pos (by positivity : (0:ℝ) < 16 * r ^ 2),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : |32 * r ^ 2 * x - t * s| ≤ 100 * r ^ 3 := by
    have a1 : |32 * r ^ 2 * x| ≤ 96 * r ^ 3 := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 32 * r ^ 2)]
      nlinarith [sq_nonneg r, mul_le_mul_of_nonneg_left hx (by positivity : (0:ℝ) ≤ 32 * r ^ 2)]
    have a2 : |t * s| ≤ 9 / 4 * r ^ 3 := by
      rw [abs_mul, abs_of_nonneg hs0]
      calc |t| * s ≤ (r / 4) * (9 * r ^ 2) := by gcongr
        _ = 9 / 4 * r ^ 3 := by ring
    obtain ⟨b1, b2⟩ := abs_le.1 a1
    obtain ⟨c1, c2⟩ := abs_le.1 a2
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have h4 : |t| * |32 * r ^ 2 * x - t * s| ≤ |t| * (100 * r ^ 3) :=
    mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have h5 : 0 ≤ |t| := abs_nonneg _
  have h6 : 225 * r ^ 4 * (256 * r ^ 4) ≤ Q * (256 * r ^ 4) := by gcongr
  calc 16 * r ^ 2 * (|t| * |32 * r ^ 2 * x - t * s|) * (30 * r ^ 3)
      ≤ 16 * r ^ 2 * (|t| * (100 * r ^ 3)) * (30 * r ^ 3) := by gcongr
    _ = |t| * (48000 * r ^ 8) := by ring
    _ ≤ |t| * (225 * r ^ 4 * (256 * r ^ 4)) := by
        have h7 : 48000 * r ^ 8 ≤ 225 * r ^ 4 * (256 * r ^ 4) := by nlinarith [pow_pos hr 8]
        exact mul_le_mul_of_nonneg_left h7 h5
    _ ≤ |t| * (Q * (256 * r ^ 4)) := by gcongr

/-- `ct:dyadic` Part (2), Lipschitz estimate (P2a): for `z ∈ N₊`, `|t| ≤ r/4`, `A = 4r`,
`|P(z,t) - P(z,0)| ≤ 400 |t| / r²`.  **Proved.**  (The TeX constant is `123`; the argument is the same
elementary difference of reciprocals, with the cruder bounds `|z-t| ≥ r/4`, `|z| ≥ r/2`.) -/
theorem pDiam_lipschitz {r t : ℝ} (hr : 0 < r) (ht : |t| ≤ r / 4) {z : ℂ} (hz : z ∈ nPlus r) :
    |pDiam (4 * r) z t - pDiam (4 * r) z 0| ≤ 400 * |t| / r ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := hz
  have hA : ((4 * r : ℝ) : ℂ) ^ 2 = ((16 * r ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hnz : z ≠ 0 := by
    intro h; rw [h] at h1; simp at h1; linarith
  have hzt : z ≠ (t : ℂ) := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hP : Complex.normSq (z - t) = (z.re - t) ^ 2 + z.im ^ 2 := by
    simp [Complex.normSq_apply]; ring
  have hQ : Complex.normSq (((4 * r : ℝ) : ℂ) ^ 2 - t * z) = (16 * r ^ 2 - t * z.re) ^ 2 + (t * z.im) ^ 2 := by
    rw [hA]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hQ0 : Complex.normSq (((4 * r : ℝ) : ℂ) ^ 2 - ((0 : ℝ) : ℂ) * z) = 256 * r ^ 4 := by
    rw [hA]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hQb : 225 * r ^ 4 ≤ Complex.normSq (((4 * r : ℝ) : ℂ) ^ 2 - t * z) := by
    rw [Complex.normSq_eq_norm_sq, hA]
    have h5 := norm_sub_norm_le (((16 * r ^ 2 : ℝ) : ℂ)) ((t : ℂ) * z)
    have hn : ‖((16 * r ^ 2 : ℝ) : ℂ)‖ = 16 * r ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hn2 : ‖(t : ℂ) * z‖ = |t| * ‖z‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hn, hn2] at h5
    have h6 : |t| * ‖z‖ ≤ (r / 4) * (3 * r) := mul_le_mul ht h2 (norm_nonneg _) (by positivity)
    have h8 : 15 * r ^ 2 ≤ ‖((16 * r ^ 2 : ℝ) : ℂ) - t * z‖ := by nlinarith [sq_nonneg r]
    nlinarith [sq_nonneg r]
  have hnormQ : ((4 * r : ℝ) : ℂ) ^ 2 - t * z ≠ 0 := by
    intro h
    rw [h] at hQb; simp at hQb; nlinarith [pow_pos hr 4]
  have hnormQ0 : ((4 * r : ℝ) : ℂ) ^ 2 - ((0 : ℝ) : ℂ) * z ≠ 0 := by
    intro h
    have : Complex.normSq (((4 * r : ℝ) : ℂ) ^ 2 - ((0 : ℝ) : ℂ) * z) = 0 := by rw [h]; simp
    rw [hQ0] at this; have := pow_pos hr 4; linarith
  rw [pDiam_eq hzt hnormQ, pDiam_eq (by simpa using hnz) hnormQ0, hP, hQ, hQ0]
  have hx : |z.re| ≤ 3 * r := (abs_re_le_norm z).trans h2
  have hy : z.im ≤ 3 * r := (Complex.im_le_norm z).trans h2
  have hs1 : r ^ 2 / 4 ≤ z.re ^ 2 + z.im ^ 2 := by rw [← hsq]; nlinarith
  have hs2 : z.re ^ 2 + z.im ^ 2 ≤ 9 * r ^ 2 := by rw [← hsq]; nlinarith [norm_nonneg z]
  have hPb : r ^ 2 / 16 ≤ (z.re - t) ^ 2 + z.im ^ 2 := by
    rw [← hP, Complex.normSq_eq_norm_sq]
    have h4 : r / 4 ≤ ‖z - t‖ := by
      have := norm_sub_norm_le z (t : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    nlinarith
  have hF := lip_F (x := z.re) (P := (z.re - t) ^ 2 + z.im ^ 2) (s := z.re ^ 2 + z.im ^ 2) hr ht hx hPb hs1
    (by ring)
  have hG := lip_G (x := z.re) (Q := (16 * r ^ 2 - t * z.re) ^ 2 + (t * z.im) ^ 2)
    (s := z.re ^ 2 + z.im ^ 2) hr ht hx hs2 (by positivity)
    (by have := hQb; rw [hQ] at this; exact this) (by ring)
  have hA2 : (4 * r) ^ 2 = 16 * r ^ 2 := by ring
  have hA4 : (4 * r) ^ 2 = 16 * r ^ 2 := hA2
  have hpi := Real.pi_gt_d2
  have hy0 := h3
  -- assemble
  have hP0 : Complex.normSq (z - ((0 : ℝ) : ℂ)) = z.re ^ 2 + z.im ^ 2 := by
    simp [Complex.normSq_apply]; ring
  rw [hA2, ← mul_sub, hP0]
  have hd : (1 / ((z.re - t) ^ 2 + z.im ^ 2) - 16 * r ^ 2 / ((16 * r ^ 2 - t * z.re) ^ 2 + (t * z.im) ^ 2)) -
      (1 / (z.re ^ 2 + z.im ^ 2) - 16 * r ^ 2 / (256 * r ^ 4)) =
      (1 / ((z.re - t) ^ 2 + z.im ^ 2) - 1 / (z.re ^ 2 + z.im ^ 2)) -
        (16 * r ^ 2 / ((16 * r ^ 2 - t * z.re) ^ 2 + (t * z.im) ^ 2) - 16 * r ^ 2 / (256 * r ^ 4)) := by ring
  rw [hd, abs_mul, abs_div, abs_of_pos hy0, abs_of_pos Real.pi_pos]
  have hB : |(1 / ((z.re - t) ^ 2 + z.im ^ 2) - 1 / (z.re ^ 2 + z.im ^ 2)) -
        (16 * r ^ 2 / ((16 * r ^ 2 - t * z.re) ^ 2 + (t * z.im) ^ 2) - 16 * r ^ 2 / (256 * r ^ 4))|
      ≤ (400 + 1 / 30) * (|t| / r ^ 3) := by
    refine (abs_sub _ _).trans ?_
    have : 400 * |t| / r ^ 3 + |t| / (30 * r ^ 3) = (400 + 1 / 30) * (|t| / r ^ 3) := by
      field_simp
    linarith
  have hK : 0 ≤ |t| / r ^ 3 := by positivity
  have hpi' : (157 / 50 : ℝ) < π := by norm_num at hpi ⊢; linarith
  calc z.im / π * _ ≤ (3 * r / (157 / 50)) * ((400 + 1 / 30) * (|t| / r ^ 3)) := by
        apply mul_le_mul _ hB (abs_nonneg _) (by positivity)
        rw [div_le_div_iff₀ Real.pi_pos (by norm_num)]
        nlinarith
    _ ≤ 400 * |t| / r ^ 2 := by
        have : (3 * r / (157 / 50)) * ((400 + 1 / 30) * (|t| / r ^ 3)) = (3 * (400 + 1 / 30) / (157 / 50)) * (|t| / r ^ 2) := by
          field_simp
        rw [this]
        have h9 : 0 ≤ |t| / r ^ 2 := by positivity
        have h10 : (3 * (400 + 1 / 30) / (157 / 50) : ℝ) ≤ 400 := by norm_num
        have := mul_le_mul_of_nonneg_right h10 h9
        calc _ ≤ 400 * (|t| / r ^ 2) := this
          _ = 400 * |t| / r ^ 2 := by ring

end FormalResearch.SignUncertainty.CtHalfDiscPoisson

/-- info: 'FormalResearch.SignUncertainty.CtHalfDiscPoisson.pDiam_area' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.CtHalfDiscPoisson.pDiam_area

/-- info: 'FormalResearch.SignUncertainty.CtHalfDiscPoisson.pDiam_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.CtHalfDiscPoisson.pDiam_lipschitz

