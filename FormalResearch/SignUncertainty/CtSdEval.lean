module

public import FormalResearch.SignUncertainty.CtSdEval2

/-!
# Steepest-descent evaluation of the Airy-window integral (`ct:cfu` Step 3, `ct:K-airy`)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3 ("We now evaluate each term of
`[1+(s²+a)Q_ε(s;a)]e^{-B_c(i𝒯(s;a))}` on `Γ_SD`").  **Proved** (abstract form).  In the `w`-plane, `s = λ w` with
`λ = c^{-1/3}`, `a = κ λ² U - λ³ ψ` (so `â = a + ψ/c = κ c^{-2/3} û`), the integral along a chain `Γ` (ray or the
two-segment-plus-ray path) of `w^{1/2} [1 + (s²+a)Q(s)] E(s) e^{iPh_U(w)}` equals
`(1 + c^{-1}(-ψQ₀ + (3i/2)Q₁)) ∫_Γ w^{1/2} e^{iPh_U} + c^{-2/3} Q₀ ∫_Γ w^{1/2}(κU+w²) e^{iPh_U}`
up to `O(λ⁴ (1+|U|)^{1/2})`, given the moment bounds `ct:sd-moments` for `Γ`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real

namespace FormalResearch.SignUncertainty.CtSd

lemma rpow_three_half {x : ℝ} (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x ^ (1 / 2 : ℝ) * x := by
  rcases hx.eq_or_lt with h | h
  · subst h; simp
  · rw [← Real.rpow_add_one h.ne']; norm_num

lemma rpow_half_mul_sq {x : ℝ} (hx : 0 ≤ x) : x ^ (1 / 2 : ℝ) * x ^ 2 = x ^ (3 / 2 : ℝ) * x := by
  rw [rpow_three_half hx]; ring

/-- The pulled-back symbol minus its value at `0`, in the `w`-plane. -/
noncomputable def Gf (lam : ℝ) (Q : ℂ → ℂ) (Q0 : ℂ) (w : ℂ) : ℂ := Q ((lam : ℂ) * w) - Q0

section amp

variable {R₀ ρ0 lam : ℝ} {a Q0 Q1 : ℂ} {Q Q' E : ℂ → ℂ} {CQ CE CB : ℝ}

lemma smem (hR : 0 < R₀) (hlam : 0 < lam) (hρ : lam * R₀ ≤ ρ0) {w : ℂ} (hw : w ∈ ball (0 : ℂ) R₀) :
    (lam : ℂ) * w ∈ ball (0 : ℂ) ρ0 := by
  rw [mem_ball_zero_iff] at *
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam.le]
  calc lam * ‖w‖ < lam * R₀ := mul_lt_mul_of_pos_left hw hlam
    _ ≤ ρ0 := hρ

lemma norm_smul_lam {lam : ℝ} (hlam : 0 < lam) (w : ℂ) : ‖(lam : ℂ) * w‖ = lam * ‖w‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam.le]

lemma hasDerivAt_Gf (amp : SdAmp lam ρ0 a Q0 Q1 Q Q' E CQ CE CB) (hR : 0 < R₀) (hlam : 0 < lam)
    (hρ : lam * R₀ ≤ ρ0) {w : ℂ} (hw : w ∈ ball (0 : ℂ) R₀) :
    HasDerivAt (Gf lam Q Q0) ((lam : ℂ) * Q' ((lam : ℂ) * w)) w := by
  have h1 : HasDerivAt (fun w : ℂ => (lam : ℂ) * w) (lam : ℂ) w := by
    simpa using (hasDerivAt_id w).const_mul (lam : ℂ)
  have h2 := ((amp.hQd _ (smem hR hlam hρ hw)).comp w h1).sub_const Q0
  unfold Gf
  refine h2.congr_deriv ?_
  ring

lemma continuousOn_Gd (amp : SdAmp lam ρ0 a Q0 Q1 Q Q' E CQ CE CB) (hR : 0 < R₀) (hlam : 0 < lam)
    (hρ : lam * R₀ ≤ ρ0) :
    ContinuousOn (fun w : ℂ => (lam : ℂ) * Q' ((lam : ℂ) * w)) (ball 0 R₀) := by
  refine continuousOn_const.mul (amp.hQ'c.comp (continuous_const.mul continuous_id).continuousOn ?_)
  intro w hw
  exact smem hR hlam hρ hw

/-- Second-order bound for `G`. -/
lemma norm_Gf_le (amp : SdAmp lam ρ0 a Q0 Q1 Q Q' E CQ CE CB) (hR : 0 < R₀) (hlam : 0 < lam)
    (hρ : lam * R₀ ≤ ρ0) {w : ℂ} (hw : w ∈ ball (0 : ℂ) R₀) :
    ‖Gf lam Q Q0 w‖ ≤ ‖Q1‖ * (lam * ‖w‖) + CQ * (‖a‖ + (lam * ‖w‖) ^ 2) := by
  have h := amp.hQ1 _ (smem hR hlam hρ hw)
  rw [norm_smul_lam hlam] at h
  have e : Gf lam Q Q0 w = (Q ((lam : ℂ) * w) - Q0 - Q1 * ((lam : ℂ) * w)) + Q1 * ((lam : ℂ) * w) := by
    unfold Gf; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_smul_lam hlam]
  linarith only [h]

/-- First-order bound for `G`: `|G| ≤ (|Q₁| + C_Q ρ₀) λ|w| + C_Q |a|`. -/
lemma norm_Gf_le1 (amp : SdAmp lam ρ0 a Q0 Q1 Q Q' E CQ CE CB) (hR : 0 < R₀) (hlam : 0 < lam)
    (hρ : lam * R₀ ≤ ρ0) {w : ℂ} (hw : w ∈ ball (0 : ℂ) R₀) :
    ‖Gf lam Q Q0 w‖ ≤ (‖Q1‖ + CQ * ρ0) * (lam * ‖w‖) + CQ * ‖a‖ := by
  have h := norm_Gf_le amp hR hlam hρ hw
  have hs : lam * ‖w‖ ≤ ρ0 := by
    have := mem_ball_zero_iff.mp (smem hR hlam hρ hw)
    rw [norm_smul_lam hlam] at this
    exact this.le
  have h0 : 0 ≤ lam * ‖w‖ := by positivity
  have : (lam * ‖w‖) ^ 2 ≤ ρ0 * (lam * ‖w‖) := by nlinarith only [hs, h0]
  have := mul_le_mul_of_nonneg_left this amp.hCQ
  linarith only [h, this]

lemma norm_Gd_le (amp : SdAmp lam ρ0 a Q0 Q1 Q Q' E CQ CE CB) (hR : 0 < R₀) (hlam : 0 < lam)
    (hρ : lam * R₀ ≤ ρ0) {w : ℂ} (hw : w ∈ ball (0 : ℂ) R₀) :
    ‖(lam : ℂ) * Q' ((lam : ℂ) * w)‖ ≤ lam * (‖Q1‖ + CQ * (ρ0 + ‖a‖)) := by
  have h := amp.hQ2 _ (smem hR hlam hρ hw)
  have hs : ‖(lam : ℂ) * w‖ ≤ ρ0 := (mem_ball_zero_iff.mp (smem hR hlam hρ hw)).le
  have e : Q' ((lam : ℂ) * w) = (Q' ((lam : ℂ) * w) - Q1) + Q1 := by ring
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam.le]
  refine mul_le_mul_of_nonneg_left ?_ hlam.le
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have := mul_le_mul_of_nonneg_left (add_le_add_right hs ‖a‖) amp.hCQ
  linarith only [h, this]

lemma rpow_neg_half_mul_sq {x : ℝ} (hx : 0 < x) : x ^ (-(1 / 2 : ℝ)) * x ^ 2 = x ^ (3 / 2 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hx]; norm_num

lemma norm_Gf_sup (amp : SdAmp lam ρ0 a Q0 Q1 Q Q' E CQ CE CB) (hR : 0 < R₀) (hlam : 0 < lam)
    (hρ : lam * R₀ ≤ ρ0) {w : ℂ} (hw : w ∈ ball (0 : ℂ) R₀) :
    ‖Gf lam Q Q0 w‖ ≤ ‖Q1‖ * ρ0 + CQ * (‖a‖ + ρ0 ^ 2) := by
  have h := norm_Gf_le amp hR hlam hρ hw
  have hs : lam * ‖w‖ ≤ ρ0 := by
    have := mem_ball_zero_iff.mp (smem hR hlam hρ hw)
    rw [norm_smul_lam hlam] at this
    exact this.le
  have h0 : 0 ≤ lam * ‖w‖ := by positivity
  have h1 := mul_le_mul_of_nonneg_left hs (norm_nonneg Q1)
  have h2 : (lam * ‖w‖) ^ 2 ≤ ρ0 ^ 2 := by nlinarith only [hs, h0]
  have h3 := mul_le_mul_of_nonneg_left (add_le_add_left h2 ‖a‖) amp.hCQ
  linarith only [h, h1, h3]

lemma Gf_continuousAt (amp : SdAmp lam ρ0 a Q0 Q1 Q Q' E CQ CE CB) (hR : 0 < R₀) (hlam : 0 < lam)
    (hρ : lam * R₀ ≤ ρ0) {w : ℂ} (hw : w ∈ ball (0 : ℂ) R₀) : ContinuousAt (Gf lam Q Q0) w :=
  (hasDerivAt_Gf amp hR hlam hρ hw).continuousAt

lemma E_continuousAt (amp : SdAmp lam ρ0 a Q0 Q1 Q Q' E CQ CE CB) (hR : 0 < R₀) (hlam : 0 < lam)
    (hρ : lam * R₀ ≤ ρ0) {w : ℂ} (hw : w ∈ ball (0 : ℂ) R₀) :
    ContinuousAt (fun w : ℂ => E ((lam : ℂ) * w)) w := by
  have h1 : ContinuousAt E ((lam : ℂ) * w) := amp.hEc.continuousAt (isOpen_ball.mem_nhds (smem hR hlam hρ hw))
  exact h1.comp (f := fun w : ℂ => (lam : ℂ) * w) (continuous_const.mul continuous_id).continuousAt

lemma Q_continuousAt (amp : SdAmp lam ρ0 a Q0 Q1 Q Q' E CQ CE CB) (hR : 0 < R₀) (hlam : 0 < lam)
    (hρ : lam * R₀ ≤ ρ0) {w : ℂ} (hw : w ∈ ball (0 : ℂ) R₀) :
    ContinuousAt (fun w : ℂ => Q ((lam : ℂ) * w)) w := by
  have h := Gf_continuousAt amp hR hlam hρ hw
  have : (fun w : ℂ => Q ((lam : ℂ) * w)) = fun w => Gf lam Q Q0 w + Q0 := by
    funext w; unfold Gf; ring
  rw [this]
  exact h.add continuousAt_const

/-- `csr` is in the class `B3 0 1 0`. -/
lemma B3_csr {p : ℂ} (ch : Chain3 R₀ p) : ch.B3 csr 0 1 0 := by
  refine Chain3.B3.of_pointwise ch le_rfl zero_le_one le_rfl
    (fun z _ hre _ => continuousAt_csr (Or.inl hre)) ?_
  intro z _ _ _
  rw [norm_csr_rpow]; simp

lemma B3_csrW {p : ℂ} (ch : Chain3 R₀ p) (U : ℝ) :
    ch.B3 (fun w => csr w * ((kap : ℂ) * U + w ^ 2)) 0 (kap * |U|) R₀ := by
  have hR : 0 ≤ R₀ := by
    have := (mem_ball_zero_iff.mp ((ch.ok1).2.1 ch.q1.a ⟨le_rfl, ch.ok1.1⟩).1)
    exact (norm_nonneg _).trans this.le
  refine Chain3.B3.of_pointwise ch le_rfl (mul_nonneg kap_pos.le (abs_nonneg _)) hR
    (fun z _ hre _ => (continuousAt_csr (Or.inl hre)).mul (continuousAt_const.add (continuousAt_id.pow 2))) ?_
  intro z hz hre hz0
  have hzR : ‖z‖ < R₀ := by rwa [mem_ball_zero_iff] at hz
  have hq : ‖(kap : ℂ) * U + z ^ 2‖ ≤ kap * |U| + ‖z‖ ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(kap : ℂ) * U‖ = kap * |U| := by rw [norm_mul]; simp [abs_of_pos kap_pos]
    rw [h1, norm_pow]
  rw [norm_mul, norm_csr_rpow]
  have h1 := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ ‖z‖ ^ (1 / 2 : ℝ))
  have h2 := rpow_half_mul_sq (norm_nonneg z)
  have h3 : ‖z‖ ^ (3 / 2 : ℝ) * ‖z‖ ≤ ‖z‖ ^ (3 / 2 : ℝ) * R₀ :=
    mul_le_mul_of_nonneg_left hzR.le (by positivity)
  simp only [zero_mul, zero_add]
  nlinarith only [h1, h2, h3]


lemma Chain3.R₀_nonneg {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) : 0 ≤ R₀ := by
  have := (mem_ball_zero_iff.mp ((ch.ok1).2.1 ch.q1.a ⟨le_rfl, ch.ok1.1⟩).1)
  exact (norm_nonneg _).trans this.le

/-- `csr · G` is in the class with first-order constants. -/
lemma B3_hd {p : ℂ} (ch : Chain3 R₀ p) (amp : SdAmp lam ρ0 a Q0 Q1 Q Q' E CQ CE CB) (hR : 0 < R₀)
    (hlam : 0 < lam) (hρ : lam * R₀ ≤ ρ0) :
    ch.B3 (fun w => csr w * Gf lam Q Q0 w) 0 (CQ * ‖a‖) ((‖Q1‖ + CQ * ρ0) * lam) := by
  have hρ0 : 0 ≤ ρ0 := le_trans (by positivity) hρ
  refine Chain3.B3.of_pointwise ch le_rfl (mul_nonneg amp.hCQ (norm_nonneg _))
    (mul_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg amp.hCQ hρ0)) hlam.le)
    (fun z hz hre _ => (continuousAt_csr (Or.inl hre)).mul (Gf_continuousAt amp hR hlam hρ hz)) ?_
  intro z hz hre hz0
  have h := norm_Gf_le1 amp hR hlam hρ hz
  have h1 := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ ‖z‖ ^ (1 / 2 : ℝ))
  have h2 := rpow_three_half (norm_nonneg z)
  rw [norm_mul, norm_csr_rpow, h2]
  simp only [zero_mul, zero_add]
  nlinarith only [h1]

lemma B3_h3 {p : ℂ} (ch : Chain3 R₀ p) (amp : SdAmp lam ρ0 a Q0 Q1 Q Q' E CQ CE CB) (hR : 0 < R₀)
    (hlam : 0 < lam) (hρ : lam * R₀ ≤ ρ0) (U : ℝ) :
    ch.B3 (fun w => csr w * Gf lam Q Q0 w * ((kap : ℂ) * U + w ^ 2)) 0
      ((‖Q1‖ * ρ0 + CQ * (‖a‖ + ρ0 ^ 2)) * (kap * |U| + R₀ ^ 2)) 0 := by
  have hρ0 : 0 ≤ ρ0 := le_trans (by positivity) hρ
  have hKG : 0 ≤ ‖Q1‖ * ρ0 + CQ * (‖a‖ + ρ0 ^ 2) :=
    add_nonneg (mul_nonneg (norm_nonneg _) hρ0) (mul_nonneg amp.hCQ (add_nonneg (norm_nonneg _) (sq_nonneg _)))
  refine Chain3.B3.of_pointwise ch le_rfl
    (mul_nonneg hKG (add_nonneg (mul_nonneg kap_pos.le (abs_nonneg _)) (sq_nonneg _))) le_rfl
    (fun z hz hre _ => ((continuousAt_csr (Or.inl hre)).mul (Gf_continuousAt amp hR hlam hρ hz)).mul
      (continuousAt_const.add (continuousAt_id.pow 2))) ?_
  intro z hz hre hz0
  have hzR : ‖z‖ < R₀ := by rwa [mem_ball_zero_iff] at hz
  have hq : ‖(kap : ℂ) * U + z ^ 2‖ ≤ kap * |U| + R₀ ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(kap : ℂ) * U‖ = kap * |U| := by rw [norm_mul]; simp [abs_of_pos kap_pos]
    rw [h1, norm_pow]
    have := norm_nonneg z
    nlinarith only [hzR, this]
  rw [norm_mul, norm_mul, norm_csr_rpow]
  have h1 := mul_le_mul (norm_Gf_sup amp hR hlam hρ hz) hq (norm_nonneg _) hKG
  have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ ‖z‖ ^ (1 / 2 : ℝ))
  simp only [zero_mul, zero_add, add_zero]
  linarith only [this]

lemma B3_hR {p : ℂ} (ch : Chain3 R₀ p) (amp : SdAmp lam ρ0 a Q0 Q1 Q Q' E CQ CE CB) (hR : 0 < R₀)
    (hlam : 0 < lam) (hρ : lam * R₀ ≤ ρ0) :
    ch.B3 (fun w => csr w / (2 * w) * (Gf lam Q Q0 w - Q1 * ((lam : ℂ) * w)) +
        csr w * ((lam : ℂ) * (Q' ((lam : ℂ) * w) - Q1)))
      (CQ * ‖a‖ / 2) (CQ * lam * ‖a‖) (3 / 2 * CQ * lam ^ 2) := by
  have hCQ := amp.hCQ
  refine Chain3.B3.of_pointwise ch (by positivity) (by positivity) (by positivity) ?_ ?_
  · intro z hz hre hz0
    have h1 : ContinuousAt (fun w => csr w / (2 * w)) z :=
      (continuousAt_csr (Or.inl hre)).div (continuousAt_const.mul continuousAt_id) (by simpa using hz0)
    have h2 : ContinuousAt (fun w : ℂ => Q' ((lam : ℂ) * w)) z :=
      (amp.hQ'c.continuousAt (isOpen_ball.mem_nhds (smem hR hlam hρ hz))).comp
        (f := fun w : ℂ => (lam : ℂ) * w) (continuous_const.mul continuous_id).continuousAt
    have h3 := Gf_continuousAt amp hR hlam hρ hz
    have h4 : ContinuousAt csr z := continuousAt_csr (Or.inl hre)
    have h6 : ContinuousAt (fun w : ℂ => Q1 * ((lam : ℂ) * w)) z := by fun_prop
    have h7 : ContinuousAt (fun w : ℂ => (lam : ℂ) * (Q' ((lam : ℂ) * w) - Q1)) z :=
      continuousAt_const.mul (h2.sub continuousAt_const)
    exact (h1.mul (h3.sub h6)).add (h4.mul h7)
  · intro z hz hre hz0
    have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hs := smem hR hlam hρ hz
    have q1 : ‖Gf lam Q Q0 z - Q1 * ((lam : ℂ) * z)‖ ≤ CQ * (‖a‖ + (lam * ‖z‖) ^ 2) := by
      have := amp.hQ1 _ hs
      rw [norm_smul_lam hlam] at this
      unfold Gf
      have e : Q ((lam : ℂ) * z) - Q0 - Q1 * ((lam : ℂ) * z) = Q ((lam : ℂ) * z) - Q0 - Q1 * ((lam : ℂ) * z) := rfl
      exact this
    have q2 : ‖Q' ((lam : ℂ) * z) - Q1‖ ≤ CQ * (lam * ‖z‖ + ‖a‖) := by
      have := amp.hQ2 _ hs
      rwa [norm_smul_lam hlam] at this
    have t1 : ‖csr z / (2 * z) * (Gf lam Q Q0 z - Q1 * ((lam : ℂ) * z))‖ ≤
        (CQ * ‖a‖ / 2) * ‖z‖ ^ (-(1 / 2 : ℝ)) + (CQ * lam ^ 2 / 2) * ‖z‖ ^ (3 / 2 : ℝ) := by
      rw [norm_mul, norm_csr_div hz0]
      have h1 := mul_le_mul_of_nonneg_left q1 (by positivity : 0 ≤ (1 / 2) * ‖z‖ ^ (-(1 / 2 : ℝ)))
      have h2 := rpow_neg_half_mul_sq hzp
      rw [← h2]
      nlinarith only [h1]
    have t2 : ‖csr z * ((lam : ℂ) * (Q' ((lam : ℂ) * z) - Q1))‖ ≤
        (CQ * lam * ‖a‖) * ‖z‖ ^ (1 / 2 : ℝ) + (CQ * lam ^ 2) * ‖z‖ ^ (3 / 2 : ℝ) := by
      rw [norm_mul, norm_csr_rpow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlam.le]
      have h1 := mul_le_mul_of_nonneg_left q2 (by positivity : 0 ≤ ‖z‖ ^ (1 / 2 : ℝ) * lam)
      have h2 := rpow_three_half (norm_nonneg z)
      rw [h2]
      nlinarith only [h1]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ _ := by nlinarith only [t1, t2]

lemma B3_hEr {p : ℂ} (ch : Chain3 R₀ p) (amp : SdAmp lam ρ0 a Q0 Q1 Q Q' E CQ CE CB) (hR : 0 < R₀)
    (hlam : 0 < lam) (hρ : lam * R₀ ≤ ρ0) :
    ch.B3 (fun w => csr w * (1 + (((lam : ℂ) * w) ^ 2 + a) * Q ((lam : ℂ) * w)) * (E ((lam : ℂ) * w) - 1))
      0 0 (CB * CE * lam ^ 4) := by
  have hCB := amp.hCB
  have hCE := amp.hCE
  refine Chain3.B3.of_pointwise ch le_rfl le_rfl (by positivity) ?_ ?_
  · intro z hz hre hz0
    have hQ := Q_continuousAt amp hR hlam hρ hz
    have hE := E_continuousAt amp hR hlam hρ hz
    have hl : ContinuousAt (fun w : ℂ => (lam : ℂ) * w) z := (continuous_const.mul continuous_id).continuousAt
    exact ((continuousAt_csr (Or.inl hre)).mul (continuousAt_const.add
      (((hl.pow 2).add continuousAt_const).mul hQ))).mul (hE.sub continuousAt_const)
  · intro z hz hre hz0
    have hs := smem hR hlam hρ hz
    have b1 := amp.hB _ hs
    have e1 := amp.hE _ hs
    rw [norm_smul_lam hlam] at e1
    have hb : ‖1 + (((lam : ℂ) * z) ^ 2 + a) * Q ((lam : ℂ) * z)‖ ≤ CB := b1
    rw [norm_mul, norm_mul, norm_csr_rpow]
    have h1 := mul_le_mul hb e1 (norm_nonneg _) hCB
    have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ ‖z‖ ^ (1 / 2 : ℝ))
    have h2 := rpow_three_half (norm_nonneg z)
    rw [h2]
    simp only [zero_mul, zero_add]
    nlinarith only [this]


/-- Linear combination of four `B3` amplitudes. -/
theorem Chain3.intE_lin4 {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) (U : ℝ) {h1 h2 h3 h4 : ℂ → ℂ}
    {A1 B1 C1 A2 B2 C2 A3 B3' C3 A4 B4 C4 : ℝ}
    (b1 : ch.B3 h1 A1 B1 C1) (b2 : ch.B3 h2 A2 B2 C2) (b3 : ch.B3 h3 A3 B3' C3) (b4 : ch.B3 h4 A4 B4 C4)
    (k1 k2 k3 k4 : ℂ) :
    ch.intE U (fun w => k1 * h1 w + k2 * h2 w + k3 * h3 w + k4 * h4 w) =
      k1 * ch.intE U h1 + k2 * ch.intE U h2 + k3 * ch.intE U h3 + k4 * ch.intE U h4 := by
  have s1 := b1.smul k1
  have s2 := b2.smul k2
  have s3 := b3.smul k3
  have s4 := b4.smul k4
  have s12 : ch.B3 (fun w => k1 * h1 w + k2 * h2 w) _ _ _ := s1.add s2
  have s123 : ch.B3 (fun w => k1 * h1 w + k2 * h2 w + k3 * h3 w) _ _ _ := s12.add s3
  have e3 : ch.intE U (fun w => k1 * h1 w + k2 * h2 w + k3 * h3 w + k4 * h4 w) =
      ch.intE U (fun w => k1 * h1 w + k2 * h2 w + k3 * h3 w) + ch.intE U (fun w => k4 * h4 w) :=
    s123.intE_add s4
  have e2 : ch.intE U (fun w => k1 * h1 w + k2 * h2 w + k3 * h3 w) =
      ch.intE U (fun w => k1 * h1 w + k2 * h2 w) + ch.intE U (fun w => k3 * h3 w) := s12.intE_add s3
  have e1 : ch.intE U (fun w => k1 * h1 w + k2 * h2 w) =
      ch.intE U (fun w => k1 * h1 w) + ch.intE U (fun w => k2 * h2 w) := s1.intE_add s2
  rw [e3, e2, e1, Chain3.intE_const_mul, Chain3.intE_const_mul, Chain3.intE_const_mul, Chain3.intE_const_mul]

theorem Chain3.intE_lin2 {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) (U : ℝ) {h1 h2 : ℂ → ℂ}
    {A1 B1 C1 A2 B2 C2 : ℝ} (b1 : ch.B3 h1 A1 B1 C1) (b2 : ch.B3 h2 A2 B2 C2) (k1 : ℂ) :
    ch.intE U (fun w => k1 * h1 w + h2 w) = k1 * ch.intE U h1 + ch.intE U h2 := by
  have s1 := b1.smul k1
  rw [s1.intE_add b2, Chain3.intE_const_mul]


/-- The error constant of `sd_eval`. -/
noncomputable def sdC (CQ CE CB Cm CU Cend ρ0 q1 ψn : ℝ) : ℝ :=
  CB * CE * Cm + ψn * Cm * (CQ * (kap * CU + ψn) + q1 + CQ * ρ0) + Cend +
    Cm * CQ * ((kap + ψn) / 2 + kap * CU + ψn + 3 / 2)

lemma sd_arith {lam X Xi na ψn q1 CQ CE CB Cm CU Cend ρ0 m1 m2 m3 κ : ℝ}
    (hl0 : 0 < lam) (hl1 : lam ≤ 1) (hX : 1 ≤ X) (hq1 : 0 ≤ q1) (hψ : 0 ≤ ψn)
    (hCQ : 0 ≤ CQ) (hCE : 0 ≤ CE) (hCB : 0 ≤ CB) (hCm : 0 ≤ Cm) (hCU : 0 ≤ CU) (hCend : 0 ≤ Cend)
    (hρ0 : 0 ≤ ρ0) (hκ : 0 ≤ κ) (hna : 0 ≤ na)
    (hm1 : m1 ≤ Cm * Xi) (hm2 : m2 ≤ Cm) (hm3 : m3 ≤ Cm * X)
    (ha1 : na ≤ (κ * CU + ψn) * lam * X) (ha2 : na * Xi ≤ (κ + ψn) * lam ^ 2 * X) :
    lam ^ 3 * ψn * (0 * m1 + CQ * na * m2 + (q1 + CQ * ρ0) * lam * m3) +
      (0 * m1 + 0 * m2 + CB * CE * lam ^ 4 * m3) + Cend * lam ^ 4 +
      lam ^ 2 * ((CQ * na / 2) * m1 + CQ * lam * na * m2 + 3 / 2 * CQ * lam ^ 2 * m3) ≤
    (CB * CE * Cm + ψn * Cm * (CQ * (κ * CU + ψn) + q1 + CQ * ρ0) + Cend +
      Cm * CQ * ((κ + ψn) / 2 + κ * CU + ψn + 3 / 2)) * lam ^ 4 * X := by
  have hl4 : 0 ≤ lam ^ 4 := by positivity
  have hX0 : 0 ≤ X := by linarith
  -- s1
  have s1 : CB * CE * lam ^ 4 * m3 ≤ CB * CE * Cm * lam ^ 4 * X := by
    have := mul_le_mul_of_nonneg_left hm3 (by positivity : 0 ≤ CB * CE * lam ^ 4)
    nlinarith only [this]
  -- s2
  have u1 : na * m2 ≤ (κ * CU + ψn) * lam * X * Cm :=
    (mul_le_mul_of_nonneg_left hm2 hna).trans (mul_le_mul_of_nonneg_right ha1 hCm)
  have s2 : lam ^ 3 * ψn * (0 * m1 + CQ * na * m2 + (q1 + CQ * ρ0) * lam * m3) ≤
      ψn * Cm * (CQ * (κ * CU + ψn) + q1 + CQ * ρ0) * lam ^ 4 * X := by
    have v1 := mul_le_mul_of_nonneg_left u1 hCQ
    have v2 := mul_le_mul_of_nonneg_left hm3 (by positivity : 0 ≤ (q1 + CQ * ρ0) * lam)
    have v3 : CQ * na * m2 + (q1 + CQ * ρ0) * lam * m3 ≤
        (CQ * ((κ * CU + ψn) * lam * X * Cm) + (q1 + CQ * ρ0) * lam * (Cm * X)) := by
      nlinarith only [v1, v2]
    have := mul_le_mul_of_nonneg_left v3 (by positivity : 0 ≤ lam ^ 3 * ψn)
    nlinarith only [this]
  -- s4
  have w1 : na * m1 ≤ Cm * ((κ + ψn) * lam ^ 2 * X) := by
    have := mul_le_mul_of_nonneg_left hm1 hna
    have h2 := mul_le_mul_of_nonneg_left ha2 hCm
    nlinarith only [this, h2]
  have s4 : lam ^ 2 * ((CQ * na / 2) * m1 + CQ * lam * na * m2 + 3 / 2 * CQ * lam ^ 2 * m3) ≤
      Cm * CQ * ((κ + ψn) / 2 + κ * CU + ψn + 3 / 2) * lam ^ 4 * X := by
    have x1 := mul_le_mul_of_nonneg_left w1 (by positivity : 0 ≤ CQ / 2)
    have x2 := mul_le_mul_of_nonneg_left u1 (by positivity : 0 ≤ CQ * lam)
    have x3 := mul_le_mul_of_nonneg_left hm3 (by positivity : 0 ≤ 3 / 2 * CQ * lam ^ 2)
    have x4 : (CQ * na / 2) * m1 + CQ * lam * na * m2 + 3 / 2 * CQ * lam ^ 2 * m3 ≤
        CQ / 2 * (Cm * ((κ + ψn) * lam ^ 2 * X)) + CQ * lam * ((κ * CU + ψn) * lam * X * Cm) +
          3 / 2 * CQ * lam ^ 2 * (Cm * X) := by
      nlinarith only [x1, x2, x3]
    have := mul_le_mul_of_nonneg_left x4 (by positivity : 0 ≤ lam ^ 2)
    nlinarith only [this]
  have s3 : Cend * lam ^ 4 ≤ Cend * lam ^ 4 * X := by
    nlinarith only [mul_nonneg hCend hl4, hX]
  nlinarith only [s1, s2, s3, s4]


lemma norm_a_bounds {lam U CU : ℝ} {a ψ : ℂ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (ha : a = (kap : ℂ) * (lam : ℂ) ^ 2 * (U : ℂ) - (lam : ℂ) ^ 3 * ψ)
    (hCU : 0 ≤ CU) (hU : lam * Real.sqrt |U| ≤ CU) :
    ‖a‖ ≤ (kap * CU + ‖ψ‖) * lam * (1 + |U|) ^ (1 / 2 : ℝ) ∧
      ‖a‖ * (1 + |U|) ^ (-(1 / 2 : ℝ)) ≤ (kap + ‖ψ‖) * lam ^ 2 * (1 + |U|) ^ (1 / 2 : ℝ) := by
  set X : ℝ := (1 + |U|) ^ (1 / 2 : ℝ) with hXd
  set Xi : ℝ := (1 + |U|) ^ (-(1 / 2 : ℝ)) with hXid
  have h1U : 0 < 1 + |U| := by positivity
  have hX1 : 1 ≤ X := Real.one_le_rpow (by linarith [abs_nonneg U]) (by norm_num)
  have hXX : X * X = 1 + |U| := by
    rw [hXd, ← Real.rpow_add h1U]; norm_num
  have hXiX : X * Xi = 1 := by
    rw [hXd, hXid, ← Real.rpow_add h1U]; norm_num
  have hXi0 : 0 ≤ Xi := by positivity
  have hXi1 : Xi ≤ 1 := by nlinarith only [hXiX, hXi0, hX1]
  have hsX : Real.sqrt |U| ≤ X := by
    rw [hXd, ← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsq : Real.sqrt |U| * Real.sqrt |U| = |U| := Real.mul_self_sqrt (abs_nonneg U)
  have hn1 : ‖(kap : ℂ) * (lam : ℂ) ^ 2 * (U : ℂ)‖ = kap * lam ^ 2 * |U| := by
    rw [norm_mul, norm_mul, norm_pow]
    simp [abs_of_pos kap_pos, abs_of_pos hlam]
  have hn2 : ‖(lam : ℂ) ^ 3 * ψ‖ = lam ^ 3 * ‖ψ‖ := by
    rw [norm_mul, norm_pow]
    simp [abs_of_pos hlam]
  have hna : ‖a‖ ≤ kap * lam ^ 2 * |U| + lam ^ 3 * ‖ψ‖ := by
    rw [ha]
    refine (norm_sub_le _ _).trans ?_
    rw [hn1, hn2]
  have hlU : lam ^ 2 * |U| ≤ CU * lam * X := by
    have e : lam ^ 2 * |U| = (lam * Real.sqrt |U|) * (lam * Real.sqrt |U|) := by nlinarith only [hsq]
    rw [e]
    have h2 : lam * Real.sqrt |U| ≤ lam * X := mul_le_mul_of_nonneg_left hsX hlam.le
    calc (lam * Real.sqrt |U|) * (lam * Real.sqrt |U|) ≤ CU * (lam * X) :=
          mul_le_mul hU h2 (by positivity) hCU
      _ = CU * lam * X := by ring
  have hψ := norm_nonneg ψ
  have hl3 : lam ^ 3 ≤ lam := by nlinarith only [hlam, hlam1, mul_pos hlam hlam]
  refine ⟨?_, ?_⟩
  · have h1 := mul_le_mul_of_nonneg_left hlU kap_pos.le
    have h2 := mul_le_mul_of_nonneg_right hl3 hψ
    have h3 : lam * ‖ψ‖ ≤ ‖ψ‖ * lam * X := by
      nlinarith only [mul_nonneg (mul_nonneg hψ hlam.le) (sub_nonneg.2 hX1)]
    nlinarith only [hna, h1, h2, h3]
  · have hUXi : |U| * Xi ≤ X := by
      have e : |U| = X * X - 1 := by linarith only [hXX]
      have : |U| * Xi = X * (X * Xi) - Xi := by rw [e]; ring
      rw [this, hXiX]
      linarith only [hXi0]
    have h1 : kap * lam ^ 2 * |U| * Xi ≤ kap * lam ^ 2 * X := by
      have := mul_le_mul_of_nonneg_left hUXi (mul_nonneg kap_pos.le (sq_nonneg lam))
      nlinarith only [this]
    have h2 : lam ^ 3 * ‖ψ‖ * Xi ≤ ‖ψ‖ * lam ^ 2 * X := by
      have e1 : lam ^ 3 ≤ lam ^ 2 := by nlinarith only [hlam, hlam1, mul_pos hlam hlam]
      have : Xi ≤ X := hXi1.trans hX1
      calc lam ^ 3 * ‖ψ‖ * Xi ≤ lam ^ 2 * ‖ψ‖ * X :=
            mul_le_mul (mul_le_mul_of_nonneg_right e1 hψ) this hXi0 (by positivity)
        _ = ‖ψ‖ * lam ^ 2 * X := by ring
    have := mul_le_mul_of_nonneg_right hna hXi0
    nlinarith only [this, h1, h2]


/-- The abstract steepest-descent evaluation along a chain (`ct:cfu` Step 3). -/
theorem sd_eval {R₀ ρ0 lam U : ℝ} {p : ℂ} (ch : Chain3 R₀ p) {a ψ Q0 Q1 : ℂ} {Q Q' E : ℂ → ℂ}
    {CQ CE CB Cm CU Cend : ℝ}
    (hR : 0 < R₀) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hρ : lam * R₀ ≤ ρ0)
    (ha : a = (kap : ℂ) * (lam : ℂ) ^ 2 * (U : ℂ) - (lam : ℂ) ^ 3 * ψ)
    (amp : SdAmp lam ρ0 a Q0 Q1 Q Q' E CQ CE CB)
    (hm : MomOK Cm U ch) (hCm : 0 ≤ Cm) (hCU : 0 ≤ CU) (hU : lam * Real.sqrt |U| ≤ CU) (hCend : 0 ≤ Cend)
    (hend : lam ^ 2 * (‖csr p‖ * ‖Q ((lam : ℂ) * p) - Q0‖ * Real.exp (-(PhU U p).im)) ≤ Cend * lam ^ 4) :
    ‖ch.intE U (fun w => csr w * ((1 + (((lam : ℂ) * w) ^ 2 + a) * Q ((lam : ℂ) * w)) * E ((lam : ℂ) * w))) -
        ((1 + (lam : ℂ) ^ 3 * (-(ψ * Q0) + 3 * Complex.I / 2 * Q1)) * ch.intE U csr +
          (lam : ℂ) ^ 2 * Q0 * ch.intE U (fun w => csr w * ((kap : ℂ) * U + w ^ 2)))‖ ≤
      sdC CQ CE CB Cm CU Cend ρ0 ‖Q1‖ ‖ψ‖ * lam ^ 4 * (1 + |U|) ^ (1 / 2 : ℝ) := by
  have hρ0 : 0 ≤ ρ0 := le_trans (by positivity) hρ
  have hCQ := amp.hCQ
  have hCE := amp.hCE
  have hCB := amp.hCB
  obtain ⟨ha1, ha2⟩ := norm_a_bounds hlam hlam1 ha hCU hU
  have hX1 : 1 ≤ (1 + |U|) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith [abs_nonneg U]) (by norm_num)
  have hKG : 0 ≤ ‖Q1‖ * ρ0 + CQ * (‖a‖ + ρ0 ^ 2) :=
    add_nonneg (mul_nonneg (norm_nonneg _) hρ0) (mul_nonneg hCQ (add_nonneg (norm_nonneg _) (sq_nonneg _)))
  have hKG' : 0 ≤ lam * (‖Q1‖ + CQ * (ρ0 + ‖a‖)) :=
    mul_nonneg hlam.le (add_nonneg (norm_nonneg _) (mul_nonneg hCQ (add_nonneg hρ0 (norm_nonneg _))))
  -- amplitude classes
  have bcsr := B3_csr ch
  have bW := B3_csrW ch U
  have bd := B3_hd ch amp hR hlam hρ
  have b3 := B3_h3 ch amp hR hlam hρ U
  have bR := B3_hR ch amp hR hlam hρ
  have bE := B3_hEr ch amp hR hlam hρ
  -- integration by parts
  have hibp := Chain3.ibp ch U (G := Gf lam Q Q0) (G' := fun w => (lam : ℂ) * Q' ((lam : ℂ) * w))
    hKG hKG' (fun w hw => hasDerivAt_Gf amp hR hlam hρ hw) (continuousOn_Gd amp hR hlam hρ)
    (fun w hw => norm_Gf_sup amp hR hlam hρ hw) (fun w hw => norm_Gd_le amp hR hlam hρ hw)
  set c0 : ℂ := 1 - (lam : ℂ) ^ 3 * ψ * Q0 with hc0
  -- pointwise decompositions
  have eF : ∀ w : ℂ, csr w * ((1 + (((lam : ℂ) * w) ^ 2 + a) * Q ((lam : ℂ) * w)) * E ((lam : ℂ) * w)) =
      (c0 * csr w + ((lam : ℂ) ^ 2 * Q0) * (csr w * ((kap : ℂ) * U + w ^ 2)) +
        (lam : ℂ) ^ 2 * (csr w * Gf lam Q Q0 w * ((kap : ℂ) * U + w ^ 2)) +
        (-((lam : ℂ) ^ 3 * ψ)) * (csr w * Gf lam Q Q0 w)) +
      csr w * (1 + (((lam : ℂ) * w) ^ 2 + a) * Q ((lam : ℂ) * w)) * (E ((lam : ℂ) * w) - 1) := by
    intro w
    unfold Gf
    rw [ha, hc0]
    ring
  have eX : ∀ w : ℂ, csr w / (2 * w) * Gf lam Q Q0 w + csr w * ((lam : ℂ) * Q' ((lam : ℂ) * w)) =
      (3 / 2 * ((lam : ℂ) * Q1)) * csr w + (csr w / (2 * w) * (Gf lam Q Q0 w - Q1 * ((lam : ℂ) * w)) +
        csr w * ((lam : ℂ) * (Q' ((lam : ℂ) * w) - Q1))) := by
    intro w
    by_cases hw : w = 0
    · subst hw; simp [csr_zero]
    · field_simp
      ring
  -- chain integrals
  have b4 : ch.B3 (fun w => c0 * csr w + ((lam : ℂ) ^ 2 * Q0) * (csr w * ((kap : ℂ) * U + w ^ 2)) +
        (lam : ℂ) ^ 2 * (csr w * Gf lam Q Q0 w * ((kap : ℂ) * U + w ^ 2)) +
        (-((lam : ℂ) ^ 3 * ψ)) * (csr w * Gf lam Q Q0 w)) _ _ _ :=
    (((bcsr.smul c0).add (bW.smul _)).add (b3.smul _)).add (bd.smul _)
  have L4 : ch.intE U (fun w => c0 * csr w + ((lam : ℂ) ^ 2 * Q0) * (csr w * ((kap : ℂ) * U + w ^ 2)) +
        (lam : ℂ) ^ 2 * (csr w * Gf lam Q Q0 w * ((kap : ℂ) * U + w ^ 2)) +
        (-((lam : ℂ) ^ 3 * ψ)) * (csr w * Gf lam Q Q0 w)) =
      c0 * ch.intE U csr + ((lam : ℂ) ^ 2 * Q0) * ch.intE U (fun w => csr w * ((kap : ℂ) * U + w ^ 2)) +
        (lam : ℂ) ^ 2 * ch.intE U (fun w => csr w * Gf lam Q Q0 w * ((kap : ℂ) * U + w ^ 2)) +
        (-((lam : ℂ) ^ 3 * ψ)) * ch.intE U (fun w => csr w * Gf lam Q Q0 w) :=
    Chain3.intE_lin4 ch U bcsr bW b3 bd c0 ((lam : ℂ) ^ 2 * Q0) ((lam : ℂ) ^ 2) (-((lam : ℂ) ^ 3 * ψ))
  have L1 : ch.intE U (fun w => csr w * ((1 + (((lam : ℂ) * w) ^ 2 + a) * Q ((lam : ℂ) * w)) * E ((lam : ℂ) * w))) =
      ch.intE U (fun w => c0 * csr w + ((lam : ℂ) ^ 2 * Q0) * (csr w * ((kap : ℂ) * U + w ^ 2)) +
        (lam : ℂ) ^ 2 * (csr w * Gf lam Q Q0 w * ((kap : ℂ) * U + w ^ 2)) +
        (-((lam : ℂ) ^ 3 * ψ)) * (csr w * Gf lam Q Q0 w)) +
      ch.intE U (fun w => csr w * (1 + (((lam : ℂ) * w) ^ 2 + a) * Q ((lam : ℂ) * w)) *
        (E ((lam : ℂ) * w) - 1)) :=
    (congrArg (fun f => ch.intE U f) (funext eF)).trans (b4.intE_add bE)
  have LX : ch.intE U (fun w => csr w / (2 * w) * Gf lam Q Q0 w + csr w * ((lam : ℂ) * Q' ((lam : ℂ) * w))) =
      (3 / 2 * ((lam : ℂ) * Q1)) * ch.intE U csr +
        ch.intE U (fun w => csr w / (2 * w) * (Gf lam Q Q0 w - Q1 * ((lam : ℂ) * w)) +
          csr w * ((lam : ℂ) * (Q' ((lam : ℂ) * w) - Q1))) :=
    (congrArg (fun f => ch.intE U f) (funext eX)).trans (Chain3.intE_lin2 ch U bcsr bR _)
  have hibp' : ch.intE U (fun w => csr w / (2 * w) * Gf lam Q Q0 w + csr w * ((lam : ℂ) * Q' ((lam : ℂ) * w))) +
      Complex.I * ch.intE U (fun w => csr w * Gf lam Q Q0 w * ((kap : ℂ) * U + w ^ 2)) =
      csr p * Gf lam Q Q0 p * Complex.exp (Complex.I * PhU U p) := hibp
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  set L := ch.intE U (fun w => csr w * ((1 + (((lam : ℂ) * w) ^ 2 + a) * Q ((lam : ℂ) * w)) * E ((lam : ℂ) * w)))
    with hL
  set I0 := ch.intE U csr with hI0
  set I2 := ch.intE U (fun w => csr w * ((kap : ℂ) * U + w ^ 2)) with hI2
  set I3 := ch.intE U (fun w => csr w * Gf lam Q Q0 w * ((kap : ℂ) * U + w ^ 2)) with hI3
  set Id := ch.intE U (fun w => csr w * Gf lam Q Q0 w) with hId
  set IEr := ch.intE U (fun w => csr w * (1 + (((lam : ℂ) * w) ^ 2 + a) * Q ((lam : ℂ) * w)) *
    (E ((lam : ℂ) * w) - 1)) with hIEr
  set IR := ch.intE U (fun w => csr w / (2 * w) * (Gf lam Q Q0 w - Q1 * ((lam : ℂ) * w)) +
    csr w * ((lam : ℂ) * (Q' ((lam : ℂ) * w) - Q1))) with hIR
  set IX := ch.intE U (fun w => csr w / (2 * w) * Gf lam Q Q0 w + csr w * ((lam : ℂ) * Q' ((lam : ℂ) * w)))
    with hIX
  set Ψp := csr p * Gf lam Q Q0 p * Complex.exp (Complex.I * PhU U p) with hΨp
  have key : L - ((1 + (lam : ℂ) ^ 3 * (-(ψ * Q0) + 3 * Complex.I / 2 * Q1)) * I0 + (lam : ℂ) ^ 2 * Q0 * I2) =
      (lam : ℂ) ^ 2 * Complex.I * IR - (lam : ℂ) ^ 2 * Complex.I * Ψp +
        (-((lam : ℂ) ^ 3 * ψ)) * Id + IEr := by
    linear_combination L1 + L4 - (Complex.I * (lam : ℂ) ^ 2) * hibp' + (Complex.I * (lam : ℂ) ^ 2) * LX +
      ((lam : ℂ) ^ 2 * I3) * hI
  rw [key]
  have nIR := bR.norm_intE_le (U := U)
  have nId := bd.norm_intE_le (U := U)
  have nIE := bE.norm_intE_le (U := U)
  have hl2 : ‖(lam : ℂ) ^ 2 * Complex.I‖ = lam ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_I]; simp [abs_of_pos hlam]
  have hl3 : ‖(lam : ℂ) ^ 3 * ψ‖ = lam ^ 3 * ‖ψ‖ := by
    rw [norm_mul, norm_pow]; simp [abs_of_pos hlam]
  have nΨ : ‖(lam : ℂ) ^ 2 * Complex.I * Ψp‖ ≤ Cend * lam ^ 4 := by
    rw [norm_mul, hl2, hΨp, norm_mul, norm_mul, norm_exp_I_mul]
    unfold Gf
    linarith only [hend]
  have t1 : ‖(lam : ℂ) ^ 2 * Complex.I * IR‖ ≤ lam ^ 2 * ‖IR‖ := by
    rw [norm_mul, hl2]
  have t2 : ‖(-((lam : ℂ) ^ 3 * ψ)) * Id‖ ≤ lam ^ 3 * ‖ψ‖ * ‖Id‖ := by
    rw [norm_mul, norm_neg, hl3]
  have u1 := mul_le_mul_of_nonneg_left nIR (sq_nonneg lam)
  have u2 := mul_le_mul_of_nonneg_left nId (by positivity : 0 ≤ lam ^ 3 * ‖ψ‖)
  have hm1 := hm.1
  have hm2 := hm.2.1
  have hm3 := hm.2.2
  have ar := sd_arith (lam := lam) (X := (1 + |U|) ^ (1 / 2 : ℝ)) (Xi := (1 + |U|) ^ (-(1 / 2 : ℝ)))
    (na := ‖a‖) (ψn := ‖ψ‖) (q1 := ‖Q1‖) (CQ := CQ) (CE := CE) (CB := CB) (Cm := Cm) (CU := CU)
    (Cend := Cend) (ρ0 := ρ0) (m1 := ch.mom U (-(1 / 2))) (m2 := ch.mom U (1 / 2)) (m3 := ch.mom U (3 / 2))
    (κ := kap) hlam hlam1 hX1 (norm_nonneg _) (norm_nonneg _) hCQ hCE hCB hCm hCU hCend hρ0 kap_pos.le
    (norm_nonneg _) hm1 hm2 hm3 ha1 ha2
  have nm4 : ∀ A B C D : ℂ, ‖A - B + C + D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
    intro A B C D
    calc ‖A - B + C + D‖ ≤ ‖A - B + C‖ + ‖D‖ := norm_add_le _ _
      _ ≤ ‖A - B‖ + ‖C‖ + ‖D‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by gcongr; exact norm_sub_le _ _
  have hsum := nm4 ((lam : ℂ) ^ 2 * Complex.I * IR) ((lam : ℂ) ^ 2 * Complex.I * Ψp)
    ((-((lam : ℂ) ^ 3 * ψ)) * Id) IEr
  unfold sdC
  linarith only [hsum, t1, t2, nΨ, u1, u2, nIE, ar]

end amp

/-- info: 'FormalResearch.SignUncertainty.CtSd.sd_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sd_eval

end FormalResearch.SignUncertainty.CtSd
