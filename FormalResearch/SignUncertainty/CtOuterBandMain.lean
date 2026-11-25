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

lemma large_sg {τ0 : ℝ} (hτ0 : 0 < τ0) : min 1 (τ0 ^ 3) ≤ 2 * (sg τ0 * τ0) := by
  unfold sg
  have e : τ0 ^ 2 / (1 + τ0 ^ 2) * τ0 = τ0 ^ 3 / (1 + τ0 ^ 2) := by field_simp
  rw [e]
  rcases le_total τ0 1 with h | h
  · have h3 : τ0 ^ 3 ≤ 1 := pow_le_one₀ hτ0.le h
    have h2 : τ0 ^ 2 ≤ 1 := pow_le_one₀ hτ0.le h
    rw [min_eq_right h3, mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (pow_pos hτ0 3).le (sub_nonneg.2 h2)]
  · have h3 : (1 : ℝ) ≤ τ0 ^ 3 := one_le_pow₀ h
    rw [min_eq_left h3, mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith [pow_pos hτ0 3, pow_pos hτ0 2]

lemma min_le_sg {τ0 : ℝ} (hτ0 : 0 < τ0) : min 1 (τ0 ^ 3) ≤ 3 * (sg τ0 * Real.sqrt (sg τ0)) := by
  have hs0p : 0 < sg τ0 := by unfold sg; positivity
  have hmin0 : 0 < min 1 (τ0 ^ 3) := lt_min one_pos (pow_pos hτ0 3)
  refine le_of_sq_le_sq ?_ (by positivity)
  have e : (3 * (sg τ0 * Real.sqrt (sg τ0))) ^ 2 = 9 * sg τ0 ^ 3 := by
    have := Real.sq_sqrt hs0p.le
    calc (3 * (sg τ0 * Real.sqrt (sg τ0))) ^ 2 = 9 * sg τ0 ^ 2 * (Real.sqrt (sg τ0)) ^ 2 := by ring
      _ = 9 * sg τ0 ^ 3 := by rw [this]; ring
  rw [e]
  unfold sg
  rcases le_total τ0 1 with h | h
  · have h3 : τ0 ^ 3 ≤ 1 := pow_le_one₀ hτ0.le h
    rw [min_eq_right h3, div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
    have h2 : τ0 ^ 2 ≤ 1 := pow_le_one₀ hτ0.le h
    nlinarith [pow_pos hτ0 6, pow_pos hτ0 4, pow_pos hτ0 2, mul_nonneg (pow_pos hτ0 6).le (sub_nonneg.2 h2)]
  · have h3 : (1 : ℝ) ≤ τ0 ^ 3 := one_le_pow₀ h
    rw [min_eq_left h3, div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
    have h2 : 1 ≤ τ0 ^ 2 := one_le_pow₀ h
    nlinarith [pow_pos hτ0 6, pow_pos hτ0 4, pow_pos hτ0 2]

lemma step_ratio_lo {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    (1 - δ / 2) / (δ / 2) ≤ 3 / δ ∧ ((1 - δ / 2) / (δ / 2)) ^ 2 ≤ 9 / δ ^ 2 := by
  have h1 : (1 - δ / 2) / (δ / 2) = (2 - δ) / δ := by field_simp
  have h2 : (2 - δ) / δ ≤ 3 / δ := div_le_div_of_nonneg_right (by linarith) hδ0.le
  refine ⟨h1 ▸ h2, ?_⟩
  rw [h1, div_pow]
  exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)

lemma step_ratio_hi {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    (1 + δ) / (δ / 2) ≤ 3 / δ ∧ ((1 + δ) / (δ / 2)) ^ 2 ≤ 9 / δ ^ 2 := by
  have h1 : (1 + δ) / (δ / 2) = 2 * (1 + δ) / δ := by field_simp
  have h2 : 2 * (1 + δ) / δ ≤ 3 / δ := div_le_div_of_nonneg_right (by linarith) hδ0.le
  refine ⟨h1 ▸ h2, ?_⟩
  rw [h1, div_pow]
  exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)

/-- Step bounds in the form `|X'| ≤ R₁/τ`, `|X''| ≤ R₂/τ²`. -/
lemma step_bounds {K1 K2 δ τ0 a b : ℝ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hδ0 : 0 < δ) (hτ0 : 0 < τ0)
    (hba : b / (b - a) ≤ 3 / δ) (hba2 : (b / (b - a)) ^ 2 ≤ 9 / δ ^ 2) (hab : a < b) (hb : 0 < b)
    {X1 X2 : ℝ → ℝ} (h1 : ∀ τ : ℝ, 0 < τ → |X1 τ| ≤ K1 * b / (b - a) / τ)
    (h2 : ∀ τ : ℝ, 0 < τ → |X2 τ| ≤ K2 * b ^ 2 / (b - a) ^ 2 / τ ^ 2) :
    (∀ τ : ℝ, 0 < τ → |X1 τ| ≤ 3 * K1 / δ / τ) ∧ (∀ τ : ℝ, 0 < τ → |X2 τ| ≤ 9 * K2 / δ ^ 2 / τ ^ 2) := by
  have hw : 0 < b - a := sub_pos.mpr hab
  refine ⟨fun τ hτ => (h1 τ hτ).trans ?_, fun τ hτ => (h2 τ hτ).trans ?_⟩
  · refine div_le_div_of_nonneg_right ?_ hτ.le
    calc K1 * b / (b - a) = K1 * (b / (b - a)) := by ring
      _ ≤ K1 * (3 / δ) := mul_le_mul_of_nonneg_left hba hK1
      _ = 3 * K1 / δ := by ring
  · refine div_le_div_of_nonneg_right ?_ (by positivity)
    calc K2 * b ^ 2 / (b - a) ^ 2 = K2 * (b / (b - a)) ^ 2 := by field_simp
      _ ≤ K2 * (9 / δ ^ 2) := mul_le_mul_of_nonneg_left hba2 hK2
      _ = 9 * K2 / δ ^ 2 := by ring

/-- Decomposition of the integral according to the partition of unity. -/
lemma assemble {A B0 Bl Bi E : ℝ → ℂ} {τe T0 aS : ℝ}
    (hsum : ∀ τ, A τ = B0 τ + Bl τ + Bi τ)
    (h0 : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun τ => B0 τ * E τ) volume 0 T)
    (hl : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun τ => Bl τ * E τ) volume 0 T)
    (hi : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun τ => Bi τ * E τ) volume 0 T)
    (hτe : 0 ≤ τe) (hτeT : τe ≤ T0) (haS : 0 ≤ aS) (haST : aS ≤ T0)
    (z0 : ∀ τ : ℝ, τe < τ → B0 τ = 0) (zl : ∀ τ : ℝ, T0 < τ → Bl τ = 0) (zi : ∀ τ : ℝ, 0 < τ → τ ≤ aS → Bi τ = 0)
    {T : ℝ} (hT : T0 ≤ T) :
    ∫ τ in (0 : ℝ)..T, A τ * E τ = (∫ τ in (0 : ℝ)..τe, B0 τ * E τ) + (∫ τ in (0 : ℝ)..T0, Bl τ * E τ) +
      ∫ τ in aS..T, Bi τ * E τ := by
  have hT0 : 0 ≤ T := hτe.trans (hτeT.trans hT)
  have hpt : ∀ τ, A τ * E τ = B0 τ * E τ + Bl τ * E τ + Bi τ * E τ := fun τ => by rw [hsum τ]; ring
  simp only [hpt]
  rw [intervalIntegral.integral_add ((h0 T hT0).add (hl T hT0)) (hi T hT0),
    intervalIntegral.integral_add (h0 T hT0) (hl T hT0)]
  have e0 : ∫ τ in (0 : ℝ)..T, B0 τ * E τ = ∫ τ in (0 : ℝ)..τe, B0 τ * E τ :=
    intervalIntegral_eq_of_zero_right hτe (hτeT.trans hT) (h0 T hT0) (fun τ hτ => by simp [z0 τ hτ.1])
  have el : ∫ τ in (0 : ℝ)..T, Bl τ * E τ = ∫ τ in (0 : ℝ)..T0, Bl τ * E τ :=
    intervalIntegral_eq_of_zero_right (hτe.trans hτeT) hT (hl T hT0) (fun τ hτ => by simp [zl τ (lt_of_le_of_lt le_rfl hτ.1)])
  have ei : ∫ τ in (0 : ℝ)..T, Bi τ * E τ = ∫ τ in aS..T, Bi τ * E τ :=
    intervalIntegral_eq_of_zero_left haS (haST.trans hT) (hi T hT0) (fun τ hτ => by simp [zi τ hτ.1 hτ.2])
  rw [e0, el, ei]

lemma cut_support {τ0 θ t : ℝ} (hτ0 : 0 < τ0) (hθ : 0 < θ) (ht : θ ≤ |t|) :
    tt τ0 t ≤ τ0 * (1 - θ / 4) ∨ τ0 * (1 + θ / 4) ≤ tt τ0 t := by
  unfold tt
  rcases le_abs'.mp ht with h | h
  · left
    have : τ0 * (1 + t / 2) ≤ τ0 * (1 - θ / 4) := mul_le_mul_of_nonneg_left (by linarith) hτ0.le
    exact this
  · right
    exact mul_le_mul_of_nonneg_left (by linarith) hτ0.le

lemma far_facts {τ0 δ τ : ℝ} (hτ0 : 0 < τ0) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) (h : τ ≤ 0 ∨ 2 * τ0 ≤ τ) :
    τ ≤ τ0 * (1 - δ) ∨ τ0 * (1 + δ) ≤ τ := by
  rcases h with h | h
  · left
    have : 0 < τ0 * (1 - δ) := mul_pos hτ0 (by linarith)
    linarith
  · right
    have : τ0 * (1 + δ) ≤ τ0 * 2 := mul_le_mul_of_nonneg_left (by linarith) hτ0.le
    linarith

lemma cut_zero {τ0 δ τ : ℝ} (hτ0 : 0 < τ0) (hδ0 : 0 < δ) {X0 Xi : ℝ → ℝ}
    (hX0z : ∀ τ, τ ≤ τ0 * (1 - δ) → X0 τ = 0) (hX0o : ∀ τ, τ0 * (1 - δ / 2) ≤ τ → X0 τ = 1)
    (hXiz : ∀ τ, τ ≤ τ0 * (1 + δ / 2) → Xi τ = 0) (hXio : ∀ τ, τ0 * (1 + δ) ≤ τ → Xi τ = 1)
    (h : τ ≤ τ0 * (1 - δ) ∨ τ0 * (1 + δ) ≤ τ) : X0 τ - Xi τ = 0 := by
  rcases h with h | h
  · have h2 : τ ≤ τ0 * (1 + δ / 2) := h.trans (mul_le_mul_of_nonneg_left (by linarith) hτ0.le)
    rw [hX0z _ h, hXiz _ h2]; ring
  · have h2 : τ0 * (1 - δ / 2) ≤ τ := (mul_le_mul_of_nonneg_left (by linarith) hτ0.le).trans h
    rw [hX0o _ h2, hXio _ h]; ring

lemma norm_three {a b L I : ℂ} : ‖a + b + I - L‖ ≤ ‖a‖ + ‖b - L‖ + ‖I‖ := by
  have e : a + b + I - L = a + (b - L) + I := by ring
  rw [e]
  have h1 := norm_add_le (a + (b - L)) I
  have h2 := norm_add_le a (b - L)
  linarith

set_option maxHeartbeats 4000000 in
/-- **Outer-band asymptotics (abstract form).** For `c · min(1, τ₀³) ≥ M₀`, the improper integral
`∫₀^∞ A e^{icϕ}` (`ϕ' = m - m(τ₀)`) exists and equals `e^{iπ/4} √(2π/(c m'(τ₀))) A(τ₀) e^{icϕ(τ₀)} + O(c^{-3/2}/min(1,τ₀³))`. -/
theorem outer_band (C0 CA : ℝ) (hC0 : 0 < C0) (hCA : 0 ≤ CA) :
    ∃ M0 K : ℝ, 0 < M0 ∧ 0 ≤ K ∧
      ∀ {m m1 m2 m3 : ℝ → ℝ} {A A1 A2 : ℝ → ℂ} {ϕ : ℝ → ℝ} {τ0 c : ℝ},
        MData C0 m m1 m2 m3 → AmpBd CA A A1 A2 → 0 < τ0 → 0 < c →
        (∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - m τ0) τ) → M0 ≤ c * min 1 (τ0 ^ 3) →
        ∃ I : ℂ, Tendsto (fun T : ℝ => ∫ τ in (0 : ℝ)..T, A τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) atTop (𝓝 I) ∧
          ‖I - Complex.exp ((π : ℂ) / 4 * Complex.I) * ((Real.sqrt (2 * π / (c * m1 τ0)) : ℝ) : ℂ) * A τ0 *
              Complex.exp (Complex.I * c * (ϕ τ0 : ℂ))‖ ≤ K / (c * Real.sqrt c * min 1 (τ0 ^ 3)) := by
  obtain ⟨θ, Kp, hθ0, hθ1, hKp0, H1⟩ := piece1 C0 hC0
  obtain ⟨K1, K2, hK1, hK2, Hs⟩ := exists_step_geom
  set δ := θ / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 4 := by rw [hδ]; linarith
  set R1 := 3 * K1 / δ with hR1
  set R2 := 9 * K2 / δ ^ 2 with hR2
  have hR1n : 0 ≤ R1 := by positivity
  have hR2n : 0 ≤ R2 := by positivity
  set KB := CA * (1 + 2 * (2 * R1) + 2 * R2) with hKB
  have hKBn : 0 ≤ KB := by positivity
  set κ2 : ℝ := 1 - δ / 4 with hκ2
  set κ3 : ℝ := 1 / (1 + δ / 4) with hκ3
  have hκ2a : 0 < κ2 := by rw [hκ2]; linarith
  have hκ2b : κ2 < 1 := by rw [hκ2]; linarith
  have hκ3a : 0 < κ3 := by rw [hκ3]; positivity
  have hκ3b : κ3 < 1 := by rw [hκ3, div_lt_one (by positivity)]; linarith
  have hγ2 : 0 < κ2 * (1 - κ2) := by nlinarith
  have hγ3 : 0 < κ3 * (1 - κ3) := by nlinarith
  set KP2 := KB * (2 / 3 + 1 / (κ2 * (1 - κ2)) + (1 + C0 / (κ2 * (1 - κ2)) + 2 * (1 + 4 * C0 / (κ2 * (1 - κ2)) +
        3 * C0 ^ 2 / (κ2 * (1 - κ2)) ^ 2)) / (κ2 * (1 - κ2)) ^ 2) with hKP2
  set KP3 := 4 * KB * (1 + 4 * C0 / (κ3 * (1 - κ3)) + 3 * C0 ^ 2 / (κ3 * (1 - κ3)) ^ 2) / (κ3 * (1 - κ3)) ^ 2 * (8 / 9)
    with hKP3
  set KP1 := 16 * Kp * KB with hKP1
  have hKP2n : 0 ≤ KP2 := by rw [hKP2]; positivity
  have hKP3n : 0 ≤ KP3 := by rw [hKP3]; positivity
  have hKP1n : 0 ≤ KP1 := by rw [hKP1]; positivity
  refine ⟨8, 3 * (KP1 + KP2 + KP3), by norm_num, by positivity, ?_⟩
  intro m m1 m2 m3 A A1 A2 ϕ τ0 c hM hA hτ0 hc hϕ hlarge
  have hs0p : 0 < sg τ0 := by unfold sg; positivity
  have hm1pos := hM.m1_pos hτ0
  have hw4 : 4 ≤ c * sg τ0 * τ0 := by
    have h1 := large_sg hτ0
    have h2 : c * min 1 (τ0 ^ 3) ≤ c * (2 * (sg τ0 * τ0)) := mul_le_mul_of_nonneg_left h1 hc.le
    have e : c * (2 * (sg τ0 * τ0)) = 2 * (c * sg τ0 * τ0) := by ring
    linarith
  have hw2 : 1 ≤ c * sg τ0 * (κ2 * τ0) := by
    have e : c * sg τ0 * (κ2 * τ0) = κ2 * (c * sg τ0 * τ0) := by ring
    rw [e]
    have : 15 / 16 ≤ κ2 := by rw [hκ2]; linarith
    have := mul_le_mul_of_nonneg_left hw4 (by linarith : (0 : ℝ) ≤ κ2)
    nlinarith [this]
  have hlam1 : 1 ≤ c * (τ0 ^ 2 * m1 τ0 / 4) := by
    have hm1lo := hM.lo τ0 hτ0
    have h1 : sg τ0 * τ0 ≤ τ0 ^ 2 * m1 τ0 := by
      have e : sg τ0 * τ0 = τ0 ^ 2 * (τ0 / (1 + τ0 ^ 2)) := by unfold sg; field_simp
      rw [e]; exact mul_le_mul_of_nonneg_left hm1lo (sq_nonneg τ0)
    have h2 := mul_le_mul_of_nonneg_left h1 hc.le
    have e1 : c * (sg τ0 * τ0) = c * sg τ0 * τ0 := by ring
    have e2 : c * (τ0 ^ 2 * m1 τ0 / 4) = c * (τ0 ^ 2 * m1 τ0) / 4 := by ring
    rw [e2]; linarith
  have hϕc : ContinuousOn ϕ (Ioi 0) := fun τ hτ => (hϕ τ hτ).continuousAt.continuousWithinAt
  -- cutoffs
  have ha0 : 0 < τ0 * (1 - δ) := by nlinarith
  have hab0 : τ0 * (1 - δ) < τ0 * (1 - δ / 2) := by nlinarith
  have hai : 0 < τ0 * (1 + δ / 2) := by positivity
  have habi : τ0 * (1 + δ / 2) < τ0 * (1 + δ) := by nlinarith
  obtain ⟨X0, X01, X02, hX0d, hX0d1, hX0c, hX0r, hX0z, hX0o, hX0z1, hX0o1, hX0b1, hX0b2⟩ :=
    Hs (τ0 * (1 - δ)) (τ0 * (1 - δ / 2)) ha0 hab0
  obtain ⟨Xi, Xi1, Xi2, hXid, hXid1, hXic, hXir, hXiz, hXio, hXiz1, hXio1, hXib1, hXib2⟩ :=
    Hs (τ0 * (1 + δ / 2)) (τ0 * (1 + δ)) hai habi
  have hδne : δ ≠ 0 := hδ0.ne'
  have hτne : τ0 ≠ 0 := hτ0.ne'
  have hr0 : τ0 * (1 - δ / 2) / (τ0 * (1 - δ / 2) - τ0 * (1 - δ)) = (1 - δ / 2) / (δ / 2) := by
    rw [show τ0 * (1 - δ / 2) - τ0 * (1 - δ) = τ0 * (δ / 2) by ring]
    exact mul_div_mul_left _ _ hτne
  have hri : τ0 * (1 + δ) / (τ0 * (1 + δ) - τ0 * (1 + δ / 2)) = (1 + δ) / (δ / 2) := by
    rw [show τ0 * (1 + δ) - τ0 * (1 + δ / 2) = τ0 * (δ / 2) by ring]
    exact mul_div_mul_left _ _ hτne
  obtain ⟨hX0e1, hX0e2⟩ := step_bounds hK1 hK2 hδ0 hτ0 (hr0 ▸ (step_ratio_lo hδ0 hδ1).1)
    (hr0 ▸ (step_ratio_lo hδ0 hδ1).2) hab0 (by nlinarith) hX0b1 hX0b2
  obtain ⟨hXie1, hXie2⟩ := step_bounds hK1 hK2 hδ0 hτ0 (hri ▸ (step_ratio_hi hδ0 hδ1).1)
    (hri ▸ (step_ratio_hi hδ0 hδ1).2) habi (by nlinarith) hXib1 hXib2
  -- cutoff products
  have hr1 : (0 : ℝ) ≤ 2 * R1 := by positivity
  have hr2 : (0 : ℝ) ≤ 2 * R2 := by positivity
  have hb0ai : τ0 * (1 - δ / 2) ≤ τ0 * (1 + δ / 2) := by nlinarith
  have hXi_le : ∀ τ, Xi τ ≤ X0 τ := by
    intro τ
    by_cases h : τ ≤ τ0 * (1 + δ / 2)
    · rw [hXiz τ h]; exact (hX0r τ).1
    · have : τ0 * (1 - δ / 2) ≤ τ := by linarith [not_le.mp h]
      rw [hX0o τ this]; exact (hXir τ).2
  obtain ⟨hY0d, hY0d1, hY0c, hY0b, hY0b1, hY0b2⟩ := prodB hA (X := fun τ => 1 - X0 τ)
    (X1 := fun τ => -X01 τ) (X2 := fun τ => -X02 τ)
    (fun τ => ((hasDerivAt_const τ (1 : ℝ)).fun_sub (hX0d τ)).congr_deriv (by ring)) (fun τ => (hX0d1 τ).neg) hX0c.neg
    (fun τ => ⟨by linarith [(hX0r τ).2], by linarith [(hX0r τ).1]⟩) hr1 hr2
    (fun τ hτ => by
      rw [abs_neg]; exact (hX0e1 τ hτ).trans (div_le_div_of_nonneg_right (by linarith) hτ.le))
    (fun τ hτ => by
      rw [abs_neg]; exact (hX0e2 τ hτ).trans (div_le_div_of_nonneg_right (by linarith) (by positivity)))
  obtain ⟨hYld, hYld1, hYlc, hYlb, hYlb1, hYlb2⟩ := prodB hA (X := fun τ => X0 τ - Xi τ)
    (X1 := fun τ => X01 τ - Xi1 τ) (X2 := fun τ => X02 τ - Xi2 τ)
    (fun τ => (hX0d τ).fun_sub (hXid τ)) (fun τ => (hX0d1 τ).fun_sub (hXid1 τ)) (hX0c.sub hXic)
    (fun τ => ⟨by linarith [hXi_le τ], by linarith [(hX0r τ).2, (hXir τ).1]⟩) hr1 hr2
    (fun τ hτ => by
      have := abs_sub (X01 τ) (Xi1 τ)
      have h1 := hX0e1 τ hτ
      have h2 := hXie1 τ hτ
      have e : 2 * R1 / τ = 3 * K1 / δ / τ + 3 * K1 / δ / τ := by rw [hR1]; ring
      rw [e]; linarith)
    (fun τ hτ => by
      have := abs_sub (X02 τ) (Xi2 τ)
      have h1 := hX0e2 τ hτ
      have h2 := hXie2 τ hτ
      have e : 2 * R2 / τ ^ 2 = 9 * K2 / δ ^ 2 / τ ^ 2 + 9 * K2 / δ ^ 2 / τ ^ 2 := by rw [hR2]; ring
      rw [e]; linarith)
  obtain ⟨hYid, hYid1, hYic, hYib, hYib1, hYib2⟩ := prodB hA (X := Xi) (X1 := Xi1) (X2 := Xi2)
    hXid hXid1 hXic hXir hr1 hr2
    (fun τ hτ => (hXie1 τ hτ).trans (div_le_div_of_nonneg_right (by linarith) hτ.le))
    (fun τ hτ => (hXie2 τ hτ).trans (div_le_div_of_nonneg_right (by linarith) (by positivity)))
  -- Piece 2
  have hκ2τ : τ0 * (1 - δ / 2) < κ2 * τ0 := by
    have := mul_lt_mul_of_pos_left (show 1 - δ / 2 < 1 - δ / 4 by linarith) hτ0
    have e : (1 - δ / 4) * τ0 = τ0 * (1 - δ / 4) := mul_comm _ _
    rw [hκ2, e]; exact this
  have hP2 := outer_P2 hM hκ2a hκ2b hKBn hτ0 hc hw2 hϕ hY0d hY0d1 hY0c hY0b hY0b1 hY0b2
    (by beta_reduce; rw [hX0o _ hκ2τ.le]; simp)
    (by beta_reduce; rw [(hX0o1 _ hκ2τ).1, hX0o _ hκ2τ.le]; simp)
  -- Piece 3
  have haS : τ0 / κ3 = τ0 * (1 + δ / 4) := by rw [hκ3]; field_simp
  have hxi : τ0 / κ3 < τ0 * (1 + δ / 2) := by
    rw [haS]; exact mul_lt_mul_of_pos_left (by linarith) hτ0
  obtain ⟨I3, hI3, hI3b⟩ := outer_P3 hM hκ3a hκ3b hKBn hτ0 hc hw4 hϕ hYid hYid1 hYic hYib hYib1 hYib2
    (by beta_reduce; rw [hXiz _ hxi.le]; simp)
    (by beta_reduce; rw [(hXiz1 _ hxi).1, hXiz _ hxi.le]; simp)
  -- Piece 1
  have hsupp : ∀ t : ℝ, θ ≤ |t| → ((X0 (tt τ0 t) - Xi (tt τ0 t) : ℝ) : ℂ) * A (tt τ0 t) = 0 := by
    intro t ht
    have h1 := cut_support hτ0 hθ0 ht
    rw [← hδ] at h1
    rw [cut_zero hτ0 hδ0 hX0z hX0o hXiz hXio h1]; simp
  have hB0l : ∀ τ : ℝ, τ ≤ 0 ∨ 2 * τ0 ≤ τ → ((X0 τ - Xi τ : ℝ) : ℂ) * A τ = 0 := by
    intro τ hτ
    rw [cut_zero hτ0 hδ0 hX0z hX0o hXiz hXio (far_facts hτ0 hδ0 hδ1 hτ)]; simp
  have hP1 := H1 hM hτ0 hc (T := 2 * τ0) (by positivity) hKBn hlam1 hϕ hYld hYld1 hYlc hYlb hYlb1 hYlb2 hsupp hB0l
  have hP1' := hP1.trans (P1_simplify hτ0 hc (hM.lo τ0 hτ0) hKp0 hKBn)
  -- assembly
  set E : ℝ → ℂ := fun τ => Complex.exp (Complex.I * c * (ϕ τ : ℂ)) with hE
  have contB : ∀ {B B1 : ℝ → ℂ}, (∀ τ : ℝ, 0 < τ → HasDerivAt B (B1 τ) τ) → ContinuousOn B (Ioi 0) :=
    fun h τ hτ => (h τ hτ).continuousAt.continuousWithinAt
  have hτe0 : 0 ≤ κ2 * τ0 := by positivity
  have hτeT : κ2 * τ0 ≤ 2 * τ0 := by
    have : κ2 * τ0 ≤ 1 * τ0 := mul_le_mul_of_nonneg_right hκ2b.le hτ0.le
    linarith
  have haS0 : 0 ≤ τ0 / κ3 := by positivity
  have haST : τ0 / κ3 ≤ 2 * τ0 := by
    rw [haS]
    have : τ0 * (1 + δ / 4) ≤ τ0 * 2 := mul_le_mul_of_nonneg_left (by linarith) hτ0.le
    linarith
  have hass := fun (T : ℝ) (hT : 2 * τ0 ≤ T) => assemble (A := A) (E := E)
    (B0 := fun τ => ((1 - X0 τ : ℝ) : ℂ) * A τ) (Bl := fun τ => ((X0 τ - Xi τ : ℝ) : ℂ) * A τ)
    (Bi := fun τ => ((Xi τ : ℝ) : ℂ) * A τ) (τe := κ2 * τ0) (T0 := 2 * τ0) (aS := τ0 / κ3)
    (fun τ => by push_cast; ring)
    (fun T hT => intInt_BE hT hKBn (contB hY0d) hϕc hY0b)
    (fun T hT => intInt_BE hT hKBn (contB hYld) hϕc hYlb)
    (fun T hT => intInt_BE hT hKBn (contB hYid) hϕc hYib)
    hτe0 hτeT haS0 haST
    (fun τ hτ => by
      have : τ0 * (1 - δ / 2) ≤ τ := hκ2τ.le.trans hτ.le
      beta_reduce; rw [hX0o _ this]; simp)
    (fun τ hτ => by
      have e1 : τ0 * (1 + δ) ≤ τ0 * 2 := mul_le_mul_of_nonneg_left (by linarith) hτ0.le
      have h2 : τ0 * (1 + δ) ≤ τ := by linarith
      have e2 : τ0 * (1 - δ / 2) ≤ τ0 * (1 + δ) := mul_le_mul_of_nonneg_left (by linarith) hτ0.le
      have h3 : τ0 * (1 - δ / 2) ≤ τ := e2.trans h2
      beta_reduce; rw [hX0o _ h3, hXio _ h2]; simp)
    (fun τ _ hτ => by beta_reduce; rw [hXiz _ (hτ.trans hxi.le)]; simp)
    hT
  have hBl0 : ((X0 τ0 - Xi τ0 : ℝ) : ℂ) * A τ0 = A τ0 := by
    have h1 : X0 τ0 = 1 := hX0o _ (by
      have : τ0 * (1 - δ / 2) ≤ τ0 * 1 := mul_le_mul_of_nonneg_left (by linarith) hτ0.le
      linarith)
    have h2 : Xi τ0 = 0 := hXiz _ (by
      have : τ0 * 1 ≤ τ0 * (1 + δ / 2) := mul_le_mul_of_nonneg_left (by linarith) hτ0.le
      linarith)
    rw [h1, h2]; simp
  rw [hBl0] at hP1'
  refine ⟨(∫ τ in (0 : ℝ)..(κ2 * τ0), ((1 - X0 τ : ℝ) : ℂ) * A τ * E τ) +
      (∫ τ in (0 : ℝ)..(2 * τ0), ((X0 τ - Xi τ : ℝ) : ℂ) * A τ * E τ) + I3, ?_, ?_⟩
  · have hlim := (tendsto_const_nhds (x := (∫ τ in (0 : ℝ)..(κ2 * τ0), ((1 - X0 τ : ℝ) : ℂ) * A τ * E τ) +
      (∫ τ in (0 : ℝ)..(2 * τ0), ((X0 τ - Xi τ : ℝ) : ℂ) * A τ * E τ))).add hI3
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop (2 * τ0)] with T hT
    have := hass T hT
    simp only [hE] at this ⊢
    rw [this, add_assoc]
  · set w := (c * sg τ0) * Real.sqrt (c * sg τ0) with hw
    have hwp : 0 < w := by rw [hw]; positivity
    have hn2 : ‖(∫ τ in (0 : ℝ)..(2 * τ0), ((X0 τ - Xi τ : ℝ) : ℂ) * A τ * E τ) -
        Complex.exp ((π : ℂ) / 4 * Complex.I) * ((Real.sqrt (2 * π / (c * m1 τ0)) : ℝ) : ℂ) * A τ0 *
          Complex.exp (Complex.I * c * (ϕ τ0 : ℂ))‖ ≤ KP1 / w := hP1'
    have hn1 : ‖∫ τ in (0 : ℝ)..(κ2 * τ0), ((1 - X0 τ : ℝ) : ℂ) * A τ * E τ‖ ≤ KP2 / w := hP2
    have hn3 : ‖I3‖ ≤ KP3 / w := hI3b
    have htri : ‖((∫ τ in (0 : ℝ)..(κ2 * τ0), ((1 - X0 τ : ℝ) : ℂ) * A τ * E τ) +
        (∫ τ in (0 : ℝ)..(2 * τ0), ((X0 τ - Xi τ : ℝ) : ℂ) * A τ * E τ) + I3) -
        Complex.exp ((π : ℂ) / 4 * Complex.I) * ((Real.sqrt (2 * π / (c * m1 τ0)) : ℝ) : ℂ) * A τ0 *
          Complex.exp (Complex.I * c * (ϕ τ0 : ℂ))‖ ≤ KP1 / w + KP2 / w + KP3 / w := by
      refine norm_three.trans ?_
      linarith
    refine htri.trans ?_
    have hmin := min_le_sg hτ0
    have hcc : 0 < c * Real.sqrt c := by positivity
    have hmn : 0 < min 1 (τ0 ^ 3) := lt_min one_pos (pow_pos hτ0 3)
    have hww : w = c * Real.sqrt c * (sg τ0 * Real.sqrt (sg τ0)) := by
      rw [hw, Real.sqrt_mul hc.le]; ring
    have hle : c * Real.sqrt c * min 1 (τ0 ^ 3) ≤ 3 * w := by
      rw [hww]
      have := mul_le_mul_of_nonneg_left hmin hcc.le
      linarith
    have hsum : KP1 / w + KP2 / w + KP3 / w = (KP1 + KP2 + KP3) / w := by ring
    rw [hsum, div_le_div_iff₀ hwp (by positivity)]
    have hK : 0 ≤ KP1 + KP2 + KP3 := by positivity
    have := mul_le_mul_of_nonneg_left hle hK
    linarith

/-- info: 'FormalResearch.SignUncertainty.CtOsc.outer_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outer_band

end FormalResearch.SignUncertainty.CtOsc
