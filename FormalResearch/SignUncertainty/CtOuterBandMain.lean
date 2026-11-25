module

public import FormalResearch.SignUncertainty.CtOuterBandCore

/-!
# The outer-band asymptotic (abstract form)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 4 (`ct:K-outer`).  **Proved** (abstract
form, for `μ₀` larger than a fixed constant).

Assembly of Pieces 1--3 with a smooth partition of unity `1 = χ₀ + χ_loc + χ_∞` at scale `δ τ₀`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped Real Interval

namespace FormalResearch.SignUncertainty.CtOsc

/-- Smooth step with `|X'| ≤ K₁ b/((b-a) τ)`, `|X''| ≤ K₂ b²/((b-a)² τ²)` for `τ > 0`. -/
lemma exists_step_geom : ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧ ∀ a b : ℝ, 0 < a → a < b → ∃ X X1 X2 : ℝ → ℝ,
    (∀ τ, HasDerivAt X (X1 τ) τ) ∧ (∀ τ, HasDerivAt X1 (X2 τ) τ) ∧ Continuous X2 ∧
    (∀ τ, 0 ≤ X τ ∧ X τ ≤ 1) ∧ (∀ τ, τ ≤ a → X τ = 0) ∧ (∀ τ, b ≤ τ → X τ = 1) ∧
    (∀ τ, τ < a → X1 τ = 0 ∧ X2 τ = 0) ∧ (∀ τ, b < τ → X1 τ = 0 ∧ X2 τ = 0) ∧
    (∀ τ, 0 < τ → |X1 τ| ≤ K1 * b / (b - a) / τ) ∧ (∀ τ, 0 < τ → |X2 τ| ≤ K2 * b ^ 2 / (b - a) ^ 2 / τ ^ 2) := by
  obtain ⟨K1, K2, hK1, hK2, H⟩ := exists_step
  refine ⟨K1, K2, hK1, hK2, fun a b ha hab => ?_⟩
  obtain ⟨X, X1, X2, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := H a b hab
  refine ⟨X, X1, X2, h1, h2, h3, h4, h5, h6, h7, h8, fun τ hτ => ?_, fun τ hτ => ?_⟩
  · have hw : 0 < b - a := sub_pos.mpr hab
    by_cases hb : τ ≤ b
    · have hbτ : 1 ≤ b / τ := by rw [le_div_iff₀ hτ]; linarith
      calc |X1 τ| ≤ K1 / (b - a) := h9 τ
        _ = K1 / (b - a) * 1 := by ring
        _ ≤ K1 / (b - a) * (b / τ) := mul_le_mul_of_nonneg_left hbτ (by positivity)
        _ = K1 * b / (b - a) / τ := by field_simp
    · have hb' : b < τ := not_le.mp hb
      rw [(h8 τ hb').1, abs_zero]
      have : 0 < b := by linarith
      positivity
  · have hw : 0 < b - a := sub_pos.mpr hab
    by_cases hb : τ ≤ b
    · have hbτ : 1 ≤ (b / τ) ^ 2 := by
        have : 1 ≤ b / τ := by rw [le_div_iff₀ hτ]; linarith
        nlinarith
      calc |X2 τ| ≤ K2 / (b - a) ^ 2 := h10 τ
        _ = K2 / (b - a) ^ 2 * 1 := by ring
        _ ≤ K2 / (b - a) ^ 2 * (b / τ) ^ 2 := mul_le_mul_of_nonneg_left hbτ (by positivity)
        _ = K2 * b ^ 2 / (b - a) ^ 2 / τ ^ 2 := by field_simp
    · have hb' : b < τ := not_le.mp hb
      rw [(h8 τ hb').2, abs_zero]
      have : 0 < b := by linarith
      positivity

lemma intervalIntegral_split {f : ℝ → ℂ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hf : IntervalIntegrable f volume a c) :
    ∫ x in a..c, f x = (∫ x in a..b, f x) + ∫ x in b..c, f x := by
  have hb : b ∈ Set.uIcc a c := Set.mem_uIcc.2 (Or.inl ⟨hab, hbc⟩)
  have h1 : IntervalIntegrable f volume a b :=
    hf.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc hb)
  have h2 : IntervalIntegrable f volume b c :=
    hf.mono_set (Set.uIcc_subset_uIcc hb Set.right_mem_uIcc)
  exact (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm

lemma intervalIntegral_eq_of_zero_right {f : ℝ → ℂ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hf : IntervalIntegrable f volume a c) (h0 : ∀ x ∈ Ioc b c, f x = 0) :
    ∫ x in a..c, f x = ∫ x in a..b, f x := by
  rw [intervalIntegral_split hab hbc hf]
  have : ∫ x in b..c, f x = 0 := by
    rw [intervalIntegral.integral_of_le hbc]
    exact setIntegral_eq_zero_of_forall_eq_zero h0
  rw [this, add_zero]

lemma intervalIntegral_eq_of_zero_left {f : ℝ → ℂ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hf : IntervalIntegrable f volume a c) (h0 : ∀ x ∈ Ioc a b, f x = 0) :
    ∫ x in a..c, f x = ∫ x in b..c, f x := by
  rw [intervalIntegral_split hab hbc hf]
  have : ∫ x in a..b, f x = 0 := by
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_eq_zero_of_forall_eq_zero h0
  rw [this, zero_add]

/-- Integrability of `B e^{icϕ}` on `[0,T]` for `B = O(τ^{1/2})`, continuous on `(0,∞)`. -/
lemma intInt_BE {B : ℝ → ℂ} {ϕ : ℝ → ℝ} {c KB T : ℝ} (hT : 0 ≤ T) (hKB : 0 ≤ KB)
    (hBc : ContinuousOn B (Ioi 0)) (hϕc : ContinuousOn ϕ (Ioi 0))
    (hbB : ∀ τ : ℝ, 0 < τ → ‖B τ‖ ≤ KB * τ ^ (1 / 2 : ℝ) / (1 + τ)) :
    IntervalIntegrable (fun τ => B τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) volume 0 T := by
  refine intervalIntegrable_of_rpow_bound (K := KB) hT ?_ (fun τ hτ => ?_)
  · refine (hBc.mono Ioc_subset_Ioi_self).mul ?_
    refine Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul ?_)
    exact Complex.continuous_ofReal.comp_continuousOn (hϕc.mono Ioc_subset_Ioi_self)
  · rw [norm_mul]
    simp only [norm_cexp_phase, mul_one]
    refine (hbB τ hτ.1).trans ?_
    exact div_le_self (by have := hτ.1; positivity) (by linarith [hτ.1])

lemma rp_inv_sq {S : ℝ} (hS : 0 < S) :
    ((S ^ 2)⁻¹) ^ (1 / 2 : ℝ) = S⁻¹ ∧ ((S ^ 2)⁻¹) ^ (-1 / 2 : ℝ) = S ∧ ((S ^ 2)⁻¹) ^ (3 / 2 : ℝ) = (S ^ 3)⁻¹ := by
  have key : ∀ r : ℝ, ((S ^ 2)⁻¹) ^ r = S ^ (-(2 * r)) := fun r => by
    rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hS.le, ← Real.rpow_neg hS.le]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [key]; rw [show -(2 * (1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
  · rw [key]; rw [show -(2 * (-1 / 2 : ℝ)) = 1 by norm_num, Real.rpow_one]
  · rw [key]; rw [show -(2 * (3 / 2 : ℝ)) = -(3 : ℕ) by norm_num, Real.rpow_neg hS.le, Real.rpow_natCast]

section
variable {C0 : ℝ} {m m1 m2 m3 : ℝ → ℝ}

/-- Piece 2, in terms of `w₀ = c σ(τ₀)`. -/
theorem outer_P2 (hM : MData C0 m m1 m2 m3) {κ KB c τ0 : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hKB : 0 ≤ KB)
    (hτ0 : 0 < τ0) (hc : 0 < c) (hw : 1 ≤ c * sg τ0 * (κ * τ0))
    {ϕ : ℝ → ℝ} (hϕ : ∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - m τ0) τ)
    {B B1 B2 : ℝ → ℂ} (hB : ∀ τ : ℝ, 0 < τ → HasDerivAt B (B1 τ) τ)
    (hB1 : ∀ τ : ℝ, 0 < τ → HasDerivAt B1 (B2 τ) τ) (hc2 : ContinuousOn B2 (Ioi 0))
    (hbB : ∀ τ : ℝ, 0 < τ → ‖B τ‖ ≤ KB * τ ^ (1 / 2 : ℝ) / (1 + τ))
    (hbB1 : ∀ τ : ℝ, 0 < τ → ‖B1 τ‖ ≤ KB * τ ^ (-1 / 2 : ℝ) / (1 + τ))
    (hbB2 : ∀ τ : ℝ, 0 < τ → ‖B2 τ‖ ≤ KB * τ ^ (-3 / 2 : ℝ) / (1 + τ))
    (hBe : B (κ * τ0) = 0) (hB1e : B1 (κ * τ0) = 0) :
    ‖∫ τ in (0 : ℝ)..(κ * τ0), B τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))‖ ≤
      KB * (2 / 3 + 1 / (κ * (1 - κ)) + (1 + C0 / (κ * (1 - κ)) + 2 * (1 + 4 * C0 / (κ * (1 - κ)) +
        3 * C0 ^ 2 / (κ * (1 - κ)) ^ 2)) / (κ * (1 - κ)) ^ 2) / ((c * sg τ0) * Real.sqrt (c * sg τ0)) := by
  have hC0 := hM.C0nn
  set γ := κ * (1 - κ) with hγ
  have hγ0 : 0 < γ := by rw [hγ]; nlinarith
  set s0 := sg τ0 with hs0
  have hs0p : 0 < s0 := by rw [hs0]; unfold sg; positivity
  set w0 := c * s0 with hw0
  have hw0p : 0 < w0 := by positivity
  set S := Real.sqrt w0 with hS
  have hS0 : 0 < S := Real.sqrt_pos.mpr hw0p
  have hSS : S ^ 2 = w0 := Real.sq_sqrt hw0p.le
  set τs := (S ^ 2)⁻¹ with hτs
  have hτsp : 0 < τs := by positivity
  have hτs_eq : τs = 1 / w0 := by rw [hτs, hSS, one_div]
  have hse : τs ≤ κ * τ0 := by
    rw [hτs_eq, div_le_iff₀ hw0p]
    nlinarith
  set p0 := γ * s0 with hp0
  have hp0p : 0 < p0 := by positivity
  have hstep := hM.step hκ0 hκ1 hτ0
  have hp : ∀ τ ∈ Icc τs (κ * τ0), p0 ≤ |m τ - m τ0| ∧ γ * sg τ ≤ p0 := by
    intro τ hτ
    have hτpos : 0 < τ := lt_of_lt_of_le hτsp hτ.1
    have hmono : m τ ≤ m (κ * τ0) := by
      rcases hτ.2.eq_or_lt with h | h
      · rw [h]
      · exact (hM.strictMonoOn (mem_Ioi.2 hτpos) (mem_Ioi.2 (by positivity)) h).le
    refine ⟨?_, ?_⟩
    · have : m τ - m τ0 ≤ -p0 := by
        have : m τ0 - m (κ * τ0) ≥ κ * (1 - κ) * sg τ0 := hstep
        rw [hp0, hγ, hs0]; linarith
      rw [abs_of_nonpos (by linarith [hp0p])]; linarith
    · have : sg τ ≤ s0 := by
        rw [hs0]; exact sg_mono hτpos.le (hτ.2.trans (by nlinarith))
      rw [hp0]; exact mul_le_mul_of_nonneg_left this hγ0.le
  have hres := piece2 hM hγ0 hKB hc hτsp hse hp0p hϕ hB hB1 hc2 hbB hbB1 hbB2 hBe hB1e hp
  refine hres.trans (le_of_eq ?_)
  obtain ⟨r1, r2, r3⟩ := rp_inv_sq hS0
  rw [← hτs] at r1 r2 r3
  rw [r1, r2, r3]
  have e1 : p0 * c = γ * S ^ 2 := by rw [hp0, hSS, hw0]; ring
  have e2 : p0 ^ 2 * c ^ 2 = γ ^ 2 * S ^ 4 := by
    have : p0 ^ 2 * c ^ 2 = (p0 * c) ^ 2 := by ring
    rw [this, e1]; ring
  have hwS : w0 * S = S ^ 3 := by rw [← hSS]; ring
  rw [e1, e2, hwS]
  field_simp

lemma rpow_neg_nine_half {τ : ℝ} (hτ : 0 < τ) : τ ^ (-9 / 2 : ℝ) = ((Real.sqrt τ) ^ 9)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hτ.le, ← Real.rpow_neg hτ.le]
  norm_num

lemma rpow_neg_three_half {τ : ℝ} (hτ : 0 < τ) : τ ^ (-3 / 2 : ℝ) = ((Real.sqrt τ) ^ 3)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hτ.le, ← Real.rpow_neg hτ.le]
  norm_num

/-- Piece 3, in terms of `w₀ = c σ(τ₀)`. -/
theorem outer_P3 (hM : MData C0 m m1 m2 m3) {κ KB c τ0 : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hKB : 0 ≤ KB)
    (hτ0 : 0 < τ0) (hc : 0 < c) (hw : 4 ≤ c * sg τ0 * τ0)
    {ϕ : ℝ → ℝ} (hϕ : ∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - m τ0) τ)
    {B B1 B2 : ℝ → ℂ} (hB : ∀ τ : ℝ, 0 < τ → HasDerivAt B (B1 τ) τ)
    (hB1 : ∀ τ : ℝ, 0 < τ → HasDerivAt B1 (B2 τ) τ) (hc2 : ContinuousOn B2 (Ioi 0))
    (hbB : ∀ τ : ℝ, 0 < τ → ‖B τ‖ ≤ KB * τ ^ (1 / 2 : ℝ) / (1 + τ))
    (hbB1 : ∀ τ : ℝ, 0 < τ → ‖B1 τ‖ ≤ KB * τ ^ (-1 / 2 : ℝ) / (1 + τ))
    (hbB2 : ∀ τ : ℝ, 0 < τ → ‖B2 τ‖ ≤ KB * τ ^ (-3 / 2 : ℝ) / (1 + τ))
    (hBa : B (τ0 / κ) = 0) (hB1a : B1 (τ0 / κ) = 0) :
    ∃ I : ℂ, Tendsto (fun b : ℝ => ∫ τ in (τ0 / κ)..b, B τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) atTop (𝓝 I) ∧
      ‖I‖ ≤ 4 * KB * (1 + 4 * C0 / (κ * (1 - κ)) + 3 * C0 ^ 2 / (κ * (1 - κ)) ^ 2) / (κ * (1 - κ)) ^ 2 * (8 / 9) /
        ((c * sg τ0) * Real.sqrt (c * sg τ0)) := by
  have hC0 := hM.C0nn
  set γ := κ * (1 - κ) with hγ
  have hγ0 : 0 < γ := by rw [hγ]; nlinarith
  have ha : τ0 < τ0 / κ := by rw [lt_div_iff₀ hκ0]; nlinarith
  have hap : 0 < τ0 / κ := lt_trans hτ0 ha
  have hp : ∀ τ : ℝ, τ0 / κ ≤ τ → γ * sg τ ≤ |m τ - m τ0| := by
    intro τ hτ
    have hτp : 0 < τ := lt_of_lt_of_le hap hτ
    have hκτ : τ0 ≤ κ * τ := by
      have : τ0 / κ ≤ τ := hτ
      rw [div_le_iff₀ hκ0] at this; linarith
    have hmono : m τ0 ≤ m (κ * τ) := by
      rcases hκτ.eq_or_lt with h | h
      · rw [h]
      · exact (hM.strictMonoOn (mem_Ioi.2 hτ0) (mem_Ioi.2 (by positivity)) h).le
    have hstep := hM.step hκ0 hκ1 hτp
    rw [abs_of_nonneg (by linarith [hstep, mul_nonneg (mul_nonneg hκ0.le (sub_nonneg.2 hκ1.le)) (sg_nonneg τ)])]
    linarith
  obtain ⟨I, hI, hIb⟩ := piece3 hM hγ0 hKB hc hap hϕ hB hB1 hc2 hbB hbB1 hbB2 hBa hB1a hp
  refine ⟨I, hI, hIb.trans ?_⟩
  set s0 := sg τ0 with hs0
  have hs0p : 0 < s0 := by rw [hs0]; unfold sg; positivity
  have hs01 : s0 ≤ 1 := sg_le_one τ0
  have hs0t : s0 ≤ τ0 ^ 2 := by
    rw [hs0]; unfold sg; rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg τ0, sq_nonneg (τ0 ^ 2)]
  set w0 := c * s0 with hw0
  have hw0p : 0 < w0 := by positivity
  set S := Real.sqrt w0 with hS
  have hS0 : 0 < S := Real.sqrt_pos.mpr hw0p
  have hSS : S ^ 2 = w0 := Real.sq_sqrt hw0p.le
  set r0 := Real.sqrt τ0 with hr0
  have hr00 : 0 < r0 := Real.sqrt_pos.mpr hτ0
  have hrr : r0 ^ 2 = τ0 := Real.sq_sqrt hτ0.le
  have hu : 4 ≤ c * τ0 ^ 3 := by
    have : c * s0 * τ0 ≤ c * τ0 ^ 3 := by
      calc c * s0 * τ0 ≤ c * τ0 ^ 2 * τ0 := by gcongr
        _ = c * τ0 ^ 3 := by ring
    linarith
  have k9 : S ^ 3 ≤ c ^ 2 * r0 ^ 9 := by
    refine le_of_sq_le_sq ?_ (by positivity)
    have e1 : (S ^ 3) ^ 2 = c ^ 3 * s0 ^ 3 := by
      rw [show (S ^ 3) ^ 2 = (S ^ 2) ^ 3 by ring, hSS, hw0]; ring
    have e2 : (c ^ 2 * r0 ^ 9) ^ 2 = c ^ 4 * τ0 ^ 9 := by
      rw [show (c ^ 2 * r0 ^ 9) ^ 2 = c ^ 4 * (r0 ^ 2) ^ 9 by ring, hrr]
    rw [e1, e2]
    have h1 : s0 ^ 3 ≤ τ0 ^ 6 := by
      calc s0 ^ 3 ≤ (τ0 ^ 2) ^ 3 := pow_le_pow_left₀ hs0p.le hs0t 3
        _ = τ0 ^ 6 := by ring
    have h2 : c ^ 3 * τ0 ^ 6 ≤ c ^ 4 * τ0 ^ 9 := by
      have : 0 ≤ c ^ 3 * τ0 ^ 6 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hu this]
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ c ^ 3)]
  have k3 : S ^ 3 ≤ c ^ 2 * r0 ^ 3 := by
    refine le_of_sq_le_sq ?_ (by positivity)
    have e1 : (S ^ 3) ^ 2 = c ^ 3 * s0 ^ 3 := by
      rw [show (S ^ 3) ^ 2 = (S ^ 2) ^ 3 by ring, hSS, hw0]; ring
    have e2 : (c ^ 2 * r0 ^ 3) ^ 2 = c ^ 4 * τ0 ^ 3 := by
      rw [show (c ^ 2 * r0 ^ 3) ^ 2 = c ^ 4 * (r0 ^ 2) ^ 3 by ring, hrr]
    rw [e1, e2]
    have h1 : s0 ^ 3 ≤ 1 := pow_le_one₀ hs0p.le hs01
    have h2 : c ^ 3 ≤ c ^ 4 * τ0 ^ 3 := by
      have : 0 ≤ c ^ 3 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hu this]
    nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ c ^ 3)]
  have hA9 : (τ0 / κ) ^ (-9 / 2 : ℝ) ≤ ((r0 ^ 9)⁻¹) := by
    rw [← hr0, ← rpow_neg_nine_half hτ0] at *
    exact Real.rpow_le_rpow_of_nonpos hτ0 (by rw [le_div_iff₀ hκ0]; nlinarith) (by norm_num)
  have hA3 : (τ0 / κ) ^ (-3 / 2 : ℝ) ≤ ((r0 ^ 3)⁻¹) := by
    rw [← hr0, ← rpow_neg_three_half hτ0] at *
    exact Real.rpow_le_rpow_of_nonpos hτ0 (by rw [le_div_iff₀ hκ0]; nlinarith) (by norm_num)
  have hwS : w0 * S = S ^ 3 := by rw [← hSS]; ring
  rw [hwS]
  set Pt := 4 * KB * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) / γ ^ 2 with hPt
  have hPt0 : 0 ≤ Pt := by positivity
  have t9 : (c ^ 2)⁻¹ * (r0 ^ 9)⁻¹ ≤ (S ^ 3)⁻¹ := by
    rw [← mul_inv, inv_le_inv₀ (by positivity) (by positivity)]; exact k9
  have t3 : (c ^ 2)⁻¹ * (r0 ^ 3)⁻¹ ≤ (S ^ 3)⁻¹ := by
    rw [← mul_inv, inv_le_inv₀ (by positivity) (by positivity)]; exact k3
  calc Pt / c ^ 2 * ((2 / 9) * (τ0 / κ) ^ (-9 / 2 : ℝ) + (2 / 3) * (τ0 / κ) ^ (-3 / 2 : ℝ)) ≤
      Pt / c ^ 2 * ((2 / 9) * (r0 ^ 9)⁻¹ + (2 / 3) * (r0 ^ 3)⁻¹) := by
        gcongr
    _ = Pt * ((2 / 9) * ((c ^ 2)⁻¹ * (r0 ^ 9)⁻¹) + (2 / 3) * ((c ^ 2)⁻¹ * (r0 ^ 3)⁻¹)) := by
        field_simp
    _ ≤ Pt * ((2 / 9) * (S ^ 3)⁻¹ + (2 / 3) * (S ^ 3)⁻¹) := by gcongr
    _ = Pt * (8 / 9) / S ^ 3 := by field_simp; ring

lemma P1_simplify {τ0 c m1v K KB : ℝ} (hτ0 : 0 < τ0) (hc : 0 < c) (hm : τ0 / (1 + τ0 ^ 2) ≤ m1v)
    (hK : 0 ≤ K) (hKB : 0 ≤ KB) :
    τ0 / 2 * Nn τ0 * K * (4 * KB) / ((c * (τ0 ^ 2 * m1v / 4)) * Real.sqrt (c * (τ0 ^ 2 * m1v / 4))) ≤
      16 * K * KB / ((c * sg τ0) * Real.sqrt (c * sg τ0)) := by
  have hs0p : 0 < sg τ0 := by unfold sg; positivity
  have hw0p : 0 < c * sg τ0 := by positivity
  set w0 := c * sg τ0 with hw0
  set lam := c * (τ0 ^ 2 * m1v / 4) with hlam
  have hlam0 : w0 * τ0 / 4 ≤ lam := by
    rw [hlam, hw0]; unfold sg
    have : τ0 ^ 2 / (1 + τ0 ^ 2) * τ0 / 4 ≤ τ0 ^ 2 * m1v / 4 := by
      have h1 : τ0 ^ 2 / (1 + τ0 ^ 2) * τ0 = τ0 ^ 2 * (τ0 / (1 + τ0 ^ 2)) := by field_simp
      rw [h1]
      have := mul_le_mul_of_nonneg_left hm (sq_nonneg τ0)
      linarith
    nlinarith [mul_le_mul_of_nonneg_left this hc.le]
  have hl0p : 0 < w0 * τ0 / 4 := by positivity
  have hmono : (w0 * τ0 / 4) * Real.sqrt (w0 * τ0 / 4) ≤ lam * Real.sqrt lam :=
    mul_le_mul hlam0 (Real.sqrt_le_sqrt hlam0) (Real.sqrt_nonneg _) (by linarith)
  set r0 := Real.sqrt τ0 with hr0
  have hr00 : 0 < r0 := Real.sqrt_pos.mpr hτ0
  have hrr : r0 * r0 = τ0 := Real.mul_self_sqrt hτ0.le
  set S := Real.sqrt w0 with hS
  have hS0 : 0 < S := Real.sqrt_pos.mpr hw0p
  have hSS : S * S = w0 := Real.mul_self_sqrt hw0p.le
  have hsq : Real.sqrt (w0 * τ0 / 4) = S * r0 / 2 := by
    rw [show w0 * τ0 / 4 = (S * r0 / 2) ^ 2 by rw [← hSS, ← hrr]; ring, Real.sqrt_sq (by positivity)]
  rw [hsq] at hmono
  have hNn : Nn τ0 = r0 / (1 + τ0) := by unfold Nn; rw [← Real.sqrt_eq_rpow]
  have hlam_pos : 0 < lam := lt_of_lt_of_le hl0p hlam0
  have hden : 0 < lam * Real.sqrt lam := by positivity
  rw [div_le_div_iff₀ hden (by positivity)]
  have h1 : τ0 / 2 * Nn τ0 * K * (4 * KB) * (w0 * S) = 2 * K * KB * (τ0 * r0 * w0 * S) / (1 + τ0) := by
    rw [hNn]; field_simp; ring
  rw [h1]
  have h2 : 2 * K * KB * (τ0 * r0 * w0 * S) / (1 + τ0) ≤ 16 * K * KB * (lam * Real.sqrt lam) := by
    have h3 : τ0 * r0 * w0 * S ≤ 8 * (lam * Real.sqrt lam) := by
      have : (w0 * τ0 / 4) * (S * r0 / 2) = w0 * S * τ0 * r0 / 8 := by ring
      rw [this] at hmono
      nlinarith
    have hKK : 0 ≤ K * KB := mul_nonneg hK hKB
    have h4 : 2 * K * KB * (τ0 * r0 * w0 * S) / (1 + τ0) ≤ 2 * K * KB * (τ0 * r0 * w0 * S) :=
      div_le_self (by positivity) (by linarith)
    refine h4.trans ?_
    have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * K * KB)
    linarith
  exact h2

end

end FormalResearch.SignUncertainty.CtOsc
