import FormalResearch.FourQubitEntropy.AH6Stieltjes

/-!
# Integral representation of `g` and its derivative

`g(e) = negMulLog (e/8) = ∫₀¹ κ_r(e) dr` and `g'(e) = -(ln(e/8)+1)/8 = ∫₀¹ ∂_e κ_r(e) dr` for `e > 0`
(fundamental theorem of calculus in `r`, with the antiderivatives `(e/8) ln D_r(e)` and
`(1/8) ln D_r(e) + (e/8)(1-r)/D_r(e)`).
-/

namespace FormalResearch.FourQubitEntropy.AH6

open MeasureTheory intervalIntegral Set

theorem Dr_pos {r t : ℝ} (ht : 0 < t) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : 0 < Dr r t := by
  unfold Dr
  rcases hr1.eq_or_lt with h | h
  · rw [h]; norm_num
  · have : 0 < (1 - r) * t := mul_pos (by linarith) ht
    nlinarith

theorem Dr_hasDerivAt (t r : ℝ) : HasDerivAt (fun r => Dr r t) (8 - t) r := by
  unfold Dr
  have h := ((hasDerivAt_id r).const_sub 1).mul_const t |>.add ((hasDerivAt_id r).const_mul 8)
  convert h using 1
  · funext y; simp only [Pi.add_apply, id]
  · ring

theorem kap_contOn {t : ℝ} (ht : 0 < t) : ContinuousOn (fun r => kap r t) (Icc 0 1) := by
  unfold kap Dr
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro r hr
  have := Dr_pos ht hr.1 hr.2
  unfold Dr at this
  linarith

theorem kapd_contOn {t : ℝ} (ht : 0 < t) : ContinuousOn (fun r => kapd r t) (Icc 0 1) := by
  unfold kapd Dr
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro r hr
  have := Dr_pos ht hr.1 hr.2
  unfold Dr at this
  positivity

/-- `g(e) = ∫₀¹ κ_r(e) dr`. -/
theorem integral_kap {e : ℝ} (he : 0 < e) :
    ∫ r in (0 : ℝ)..1, kap r e = Real.negMulLog (e / 8) := by
  have hderiv : ∀ r ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun r => e / 8 * Real.log (Dr r e)) (kap r e) r := by
    intro r hr
    rw [uIcc_of_le zero_le_one] at hr
    have hD := Dr_pos he hr.1 hr.2
    have h := ((Dr_hasDerivAt e r).log hD.ne').const_mul (e / 8)
    refine HasDerivAt.congr_deriv h ?_
    unfold kap
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hderiv ((kap_contOn he).intervalIntegrable_of_Icc zero_le_one)]
  have h1 : Dr 1 e = 8 := by unfold Dr; ring
  have h0 : Dr 0 e = e := by unfold Dr; ring
  simp only [h1, h0]
  unfold Real.negMulLog
  have : Real.log (e / 8) = Real.log e - Real.log 8 := Real.log_div he.ne' (by norm_num)
  rw [this]; ring

/-- `g'(e) = ∫₀¹ ∂_e κ_r(e) dr`. -/
theorem integral_kapd {n : ℝ} (hn : 0 < n) :
    ∫ r in (0 : ℝ)..1, kapd r n = -(Real.log (n / 8) + 1) / 8 := by
  have hderiv : ∀ r ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun r => 1 / 8 * Real.log (Dr r n) + n / 8 * ((1 - r) / Dr r n)) (kapd r n) r := by
    intro r hr
    rw [uIcc_of_le zero_le_one] at hr
    have hD := Dr_pos hn hr.1 hr.2
    have h1 := ((Dr_hasDerivAt n r).log hD.ne').const_mul (1 / 8)
    have h2 := (((hasDerivAt_id r).const_sub 1).div (Dr_hasDerivAt n r) hD.ne').const_mul (n / 8)
    have h := h1.add h2
    refine HasDerivAt.congr_deriv h ?_
    simp only [id_eq]
    unfold kapd Dr
    unfold Dr at hD
    field_simp
    ring
  rw [integral_eq_sub_of_hasDerivAt hderiv ((kapd_contOn hn).intervalIntegrable_of_Icc zero_le_one)]
  have h1 : Dr 1 n = 8 := by unfold Dr; ring
  have h0 : Dr 0 n = n := by unfold Dr; ring
  simp only [h1, h0]
  have : Real.log (n / 8) = Real.log n - Real.log 8 := Real.log_div hn.ne' (by norm_num)
  rw [this]
  field_simp
  ring


section Newton

variable {n1 n2 n3 i21 i31 i32 : ℝ}

/-- Integration commutes with the (linear) Newton polynomial. -/
theorem integral_newtonP {f1 f2 f3 f4 f5 f6 : ℝ → ℝ} (e : ℝ)
    (h1 : IntervalIntegrable f1 volume 0 1) (h2 : IntervalIntegrable f2 volume 0 1)
    (h3 : IntervalIntegrable f3 volume 0 1) (h4 : IntervalIntegrable f4 volume 0 1)
    (h5 : IntervalIntegrable f5 volume 0 1) (h6 : IntervalIntegrable f6 volume 0 1) :
    ∫ r in (0 : ℝ)..1, newtonP n1 n2 n3 i21 i31 i32 (f1 r) (f2 r) (f3 r) (f4 r) (f5 r) (f6 r) e =
      newtonP n1 n2 n3 i21 i31 i32 (∫ r in (0 : ℝ)..1, f1 r) (∫ r in (0 : ℝ)..1, f2 r)
        (∫ r in (0 : ℝ)..1, f3 r) (∫ r in (0 : ℝ)..1, f4 r) (∫ r in (0 : ℝ)..1, f5 r)
        (∫ r in (0 : ℝ)..1, f6 r) e := by
  set A1 := newtonP n1 n2 n3 i21 i31 i32 1 0 0 0 0 0 e
  set A2 := newtonP n1 n2 n3 i21 i31 i32 0 1 0 0 0 0 e
  set A3 := newtonP n1 n2 n3 i21 i31 i32 0 0 1 0 0 0 e
  set A4 := newtonP n1 n2 n3 i21 i31 i32 0 0 0 1 0 0 e
  set A5 := newtonP n1 n2 n3 i21 i31 i32 0 0 0 0 1 0 e
  set A6 := newtonP n1 n2 n3 i21 i31 i32 0 0 0 0 0 1 e
  have hfun : (fun r => newtonP n1 n2 n3 i21 i31 i32 (f1 r) (f2 r) (f3 r) (f4 r) (f5 r) (f6 r) e) =
      fun r => f1 r * A1 + f2 r * A2 + f3 r * A3 + f4 r * A4 + f5 r * A5 + f6 r * A6 := by
    funext r; exact newtonP_lin _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [hfun, newtonP_lin n1 n2 n3 i21 i31 i32 (∫ r in (0 : ℝ)..1, f1 r) (∫ r in (0 : ℝ)..1, f2 r)
    (∫ r in (0 : ℝ)..1, f3 r) (∫ r in (0 : ℝ)..1, f4 r) (∫ r in (0 : ℝ)..1, f5 r)
    (∫ r in (0 : ℝ)..1, f6 r) e]
  have g1 := h1.mul_const A1
  have g2 := h2.mul_const A2
  have g3 := h3.mul_const A3
  have g4 := h4.mul_const A4
  have g5 := h5.mul_const A5
  have g6 := h6.mul_const A6
  rw [integral_add (((((g1.add g2).add g3).add g4).add g5)) g6,
    integral_add ((((g1.add g2).add g3).add g4)) g5, integral_add (((g1.add g2).add g3)) g4,
    integral_add (g1.add g2) g3, integral_add g1 g2]
  simp only [intervalIntegral.integral_mul_const]
  rfl

end Newton

/-- The weight `8 r (1-r)⁴ / (D_r(n₁)² D_r(n₂)² D_r(n₃)²)` of the Stieltjes representation of the Hermite
remainder. -/
noncomputable def wt (n1 n2 n3 r : ℝ) : ℝ :=
  8 * r * (1 - r) ^ 4 / (Dr r n1 ^ 2 * Dr r n2 ^ 2 * Dr r n3 ^ 2)

/-- `K̃(e) = ∫₀¹ w(r)/D_r(e) dr`, so that `P(e) - g(e) = q(e)² K̃(e)`. -/
noncomputable def Kint (n1 n2 n3 e : ℝ) : ℝ := ∫ r in (0 : ℝ)..1, wt n1 n2 n3 r / Dr r e

theorem wt_contOn {n1 n2 n3 : ℝ} (h1 : 0 < n1) (h2 : 0 < n2) (h3 : 0 < n3) :
    ContinuousOn (wt n1 n2 n3) (Icc 0 1) := by
  unfold wt
  apply ContinuousOn.div (by fun_prop) (by unfold Dr; fun_prop)
  intro r hr
  have a1 := Dr_pos h1 hr.1 hr.2
  have a2 := Dr_pos h2 hr.1 hr.2
  have a3 := Dr_pos h3 hr.1 hr.2
  positivity

theorem wt_nonneg {n1 n2 n3 r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : 0 ≤ wt n1 n2 n3 r := by
  unfold wt
  have : 0 ≤ 1 - r := by linarith
  positivity

theorem wtD_contOn {n1 n2 n3 e : ℝ} (h1 : 0 < n1) (h2 : 0 < n2) (h3 : 0 < n3) (he : 0 < e) :
    ContinuousOn (fun r => wt n1 n2 n3 r / Dr r e) (Icc 0 1) := by
  apply (wt_contOn h1 h2 h3).div (by unfold Dr; fun_prop)
  intro r hr
  exact (Dr_pos he hr.1 hr.2).ne'

section Main

variable {n1 n2 n3 i21 i31 i32 : ℝ}

/-- **Stieltjes form of the Hermite remainder:** `P(e) - g(e) = q(e)² K̃(e)` for the Newton interpolant `P` of
`g = negMulLog (·/8)` on the double nodes `n₁ n₂ n₃`. -/
theorem hermite_stieltjes (hn1 : 0 < n1) (hn2 : 0 < n2) (hn3 : 0 < n3)
    (h21 : (n2 - n1) * i21 = 1) (h31 : (n3 - n1) * i31 = 1) (h32 : (n3 - n2) * i32 = 1)
    {e : ℝ} (he : 0 < e) :
    newtonP n1 n2 n3 i21 i31 i32 (Real.negMulLog (n1 / 8)) (-(Real.log (n1 / 8) + 1) / 8)
        (Real.negMulLog (n2 / 8)) (-(Real.log (n2 / 8) + 1) / 8)
        (Real.negMulLog (n3 / 8)) (-(Real.log (n3 / 8) + 1) / 8) e =
      Real.negMulLog (e / 8) + ((e - n1) * (e - n2) * (e - n3)) ^ 2 * Kint n1 n2 n3 e := by
  rw [← integral_kap hn1, ← integral_kapd hn1, ← integral_kap hn2, ← integral_kapd hn2,
    ← integral_kap hn3, ← integral_kapd hn3]
  rw [← integral_newtonP e ((kap_contOn hn1).intervalIntegrable_of_Icc zero_le_one)
    ((kapd_contOn hn1).intervalIntegrable_of_Icc zero_le_one)
    ((kap_contOn hn2).intervalIntegrable_of_Icc zero_le_one)
    ((kapd_contOn hn2).intervalIntegrable_of_Icc zero_le_one)
    ((kap_contOn hn3).intervalIntegrable_of_Icc zero_le_one)
    ((kapd_contOn hn3).intervalIntegrable_of_Icc zero_le_one)]
  have hae : ∀ᵐ r : ℝ ∂volume, r ∈ Set.uIoc (0 : ℝ) 1 →
      newtonP n1 n2 n3 i21 i31 i32 (kap r n1) (kapd r n1) (kap r n2) (kapd r n2) (kap r n3)
        (kapd r n3) e = kap r e + ((e - n1) * (e - n2) * (e - n3)) ^ 2 * (wt n1 n2 n3 r / Dr r e) := by
    have hne : ∀ᵐ r : ℝ ∂volume, r ∉ ({1} : Set ℝ) :=
      (Set.countable_singleton (1 : ℝ)).ae_notMem volume
    filter_upwards [hne] with r hr hmem
    rw [uIoc_of_le zero_le_one] at hmem
    have hr1 : r < 1 := lt_of_le_of_ne hmem.2 (by simpa using hr)
    have hr0 : 0 ≤ r := hmem.1.le
    have d1 := Dr_pos hn1 hr0 hr1.le
    have d2 := Dr_pos hn2 hr0 hr1.le
    have d3 := Dr_pos hn3 hr0 hr1.le
    have de := Dr_pos he hr0 hr1.le
    have := kap_remainder hr1 h21 h31 h32 d1.ne' d2.ne' d3.ne' de.ne' (e := e)
    unfold wt
    field_simp
    field_simp at this
    linarith
  rw [integral_congr_ae hae]
  have hk : IntervalIntegrable (fun r => kap r e) volume 0 1 :=
    (kap_contOn he).intervalIntegrable_of_Icc zero_le_one
  have hw : IntervalIntegrable (fun r => ((e - n1) * (e - n2) * (e - n3)) ^ 2 * (wt n1 n2 n3 r / Dr r e))
      volume 0 1 :=
    (ContinuousOn.mul continuousOn_const (wtD_contOn hn1 hn2 hn3 he)).intervalIntegrable_of_Icc zero_le_one
  rw [integral_add hk hw, integral_kap he, intervalIntegral.integral_const_mul]
  rfl

end Main

end FormalResearch.FourQubitEntropy.AH6
