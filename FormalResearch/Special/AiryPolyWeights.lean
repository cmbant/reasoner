module

public import FormalResearch.Special.AiryPolyZeros
public import FormalResearch.Special.AiryCftQNCZeros
public import FormalResearch.Special.AiryCft2ComboWeights

/-!
# Weights and position data of the far zeros of `N = P·Ai + Q·Ai'` (Hermite-Biehler `(P, Q)`)

Formalises `general_theorems.tex` Lemma 1.0′(d) (weights `D/N'² ≍ |t|^{-1/2}`, spacing of the zeros) for the polynomial case:

* `airyPQ_D_lower`: for real `t ≤ -T₁`: `W(t)²/2 ≤ D(t)` with `W = max(|P(t)|, |Q(t)| √|t|)` (`D = P² + PQ' - QP' + |t| Q²`; the derivative terms are
  `O(|t|^{-1})` relative, `airyPQ_asymp`; the two cases `deg Q < deg P` and `deg P ≤ deg Q` of the note are the dominance dichotomy);
* `airyPQ_weight_norm_le`: at a real zero `t ≤ -T₁` of `N`: `‖D(t)/N'(t)²‖ ≤ 882 π² / √(-t)` (from `D/N'² = π² M²/D`, `M(t)² = ‖M - iN‖²(t) ≤ 441 W²/√|t|`);
* position data for the sampling bound, for every real `t` with `Ai(t) ≠ 0` (for zeros of `N` beyond the real roots of `Q`, `Ai(t) ≠ 0`): the index
  `airyNIdx t` satisfies `(n+1)² ≤ √(-t)⁶` and the separation up to a shift of one index (`airyPQ_root_growth`, `airyPQ_root_sep_abs`), as in
  `AiryCftQNCZeros` where `Ai(t) ≠ 0` was a consequence of `Q ≠ 0` constant.

All proved.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Polynomial
open scoped Real

namespace FormalResearch.Special

/-! ### The lower bound for `D` -/

lemma airyPQ_deriv_ex (p : ℝ[X]) : ∃ T L : ℝ, 1 ≤ T ∧ 0 ≤ L ∧ ∀ u : ℂ, T ≤ ‖u‖ →
    ‖airyPQc (derivative p) u‖ * ‖u‖ ≤ L * ‖airyPQc p u‖ := by
  by_cases hp : p = 0
  · exact ⟨1, 0, le_rfl, le_rfl, fun u _ => by simp [hp, airyPQc_zero]⟩
  · obtain ⟨T, L, hT1, hL, hT⟩ := airyPQ_asymp p hp
    exact ⟨T, L, hT1, hL, fun u hu => (hT u hu).2.2⟩

lemma airyPQ_D_arith1 {a b c d ρ L1 L2 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hρ : 1 ≤ ρ)
    (hL : L1 + L2 ≤ 8 * ρ) (hcL : c * ρ ^ 2 ≤ L1 * a) (hdL : d * ρ ^ 2 ≤ L2 * b) (hab : 16 * b * ρ ≤ a) :
    a * d + b * c ≤ a ^ 2 / 2 := by
  have h1 : ρ ^ 2 * (a * d + b * c) ≤ (L1 + L2) * (a * b) := by
    nlinarith [mul_le_mul_of_nonneg_left hdL ha, mul_le_mul_of_nonneg_left hcL hb]
  have h2 : (L1 + L2) * (a * b) ≤ 8 * ρ * (a * b) := mul_le_mul_of_nonneg_right hL (mul_nonneg ha hb)
  have h3 : 8 * ρ * (a * b) ≤ a ^ 2 / 2 := by nlinarith
  have h4 : 0 ≤ a * d + b * c := by positivity
  have hρ2 : 1 ≤ ρ ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hρ2 h4]

lemma airyPQ_D_arith2 {a b c d ρ L1 L2 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hρ : 1 ≤ ρ)
    (hL : L1 + L2 ≤ 8 * ρ) (hcL : c * ρ ^ 2 ≤ L1 * a) (hdL : d * ρ ^ 2 ≤ L2 * b) (hab : 16 * a ≤ b * ρ) :
    a * d + b * c ≤ b ^ 2 / 2 := by
  have hρ0 : 0 < ρ ^ 2 := by positivity
  have h1 : ρ ^ 2 * (a * d + b * c) ≤ (L1 + L2) * (a * b) := by
    nlinarith [mul_le_mul_of_nonneg_left hdL ha, mul_le_mul_of_nonneg_left hcL hb]
  have h2 : (L1 + L2) * (a * b) ≤ 8 * ρ * (a * b) := mul_le_mul_of_nonneg_right hL (mul_nonneg ha hb)
  have h3 : 8 * ρ * (a * b) ≤ ρ ^ 2 * (b ^ 2 / 2) := by nlinarith [mul_nonneg hb (by linarith : (0 : ℝ) ≤ ρ)]
  have : ρ ^ 2 * (a * d + b * c) ≤ ρ ^ 2 * (b ^ 2 / 2) := by linarith
  exact le_of_mul_le_mul_left this hρ0

/-- **`D ≥ W²/2` for large negative real `t`.** -/
theorem airyPQ_D_lower (P Q : ℝ[X]) (hPQ : P ≠ 0 ∨ Q ≠ 0) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, t ≤ -T → 0 < airyPQW P Q (t : ℂ) ∧
      airyPQW P Q (t : ℂ) ^ 2 / 2 ≤ airyPQDr P Q t := by
  obtain ⟨T0, hT01, hT0⟩ := airyPQ_dominance P Q
  obtain ⟨T1, L1, hT11, hL1, hT1⟩ := airyPQ_deriv_ex P
  obtain ⟨T2, L2, hT21, hL2, hT2⟩ := airyPQ_deriv_ex Q
  set T := max (max T0 (max T1 T2)) (max 1 (((L1 + L2) / 8) ^ 2)) with hT
  have hT1' : (1 : ℝ) ≤ T := hT01.trans ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨T, hT1', fun t ht => ?_⟩
  have hu : T ≤ ‖(t : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]; linarith [neg_abs_le t]
  have hneg : t < 0 := by linarith
  have hab : ‖(t : ℂ)‖ = -t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg hneg]
  have hu0 : T0 ≤ ‖(t : ℂ)‖ := ((le_max_left _ _).trans (le_max_left _ _)).trans hu
  have hu1 : T1 ≤ ‖(t : ℂ)‖ := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hu
  have hu2 : T2 ≤ ‖(t : ℂ)‖ := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hu
  have hu3 : ((L1 + L2) / 8) ^ 2 ≤ ‖(t : ℂ)‖ := ((le_max_right _ _).trans (le_max_right _ _)).trans hu
  have hu4 : 1 ≤ ‖(t : ℂ)‖ := ((le_max_left _ _).trans (le_max_right _ _)).trans hu
  set ρ := √‖(t : ℂ)‖ with hρ
  have hρ1 : 1 ≤ ρ := by rw [hρ, show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hu4
  have hρ2 : ρ ^ 2 = -t := by rw [hρ, Real.sq_sqrt (by linarith), hab]
  have hρ3 : (L1 + L2) / 8 ≤ ρ := Real.le_sqrt_of_sq_le hu3
  obtain ⟨hdP, hdQ⟩ := hT0 (t : ℂ) hu0
  have hP1 := hT1 (t : ℂ) hu1
  have hQ1 := hT2 (t : ℂ) hu2
  rw [hab] at hP1 hQ1
  set p0 := P.eval t with hp0
  set q0 := Q.eval t with hq0
  set p1 := (derivative P).eval t with hp1
  set q1 := (derivative Q).eval t with hq1
  have hnP : ‖airyPQc P (t : ℂ)‖ = |p0| := by rw [airyPQc_ofReal, Complex.norm_real, Real.norm_eq_abs]
  have hnQ : ‖airyPQc Q (t : ℂ)‖ = |q0| := by rw [airyPQc_ofReal, Complex.norm_real, Real.norm_eq_abs]
  have hnP1 : ‖airyPQc (derivative P) (t : ℂ)‖ = |p1| := by
    rw [airyPQc_ofReal, Complex.norm_real, Real.norm_eq_abs]
  have hnQ1 : ‖airyPQc (derivative Q) (t : ℂ)‖ = |q1| := by
    rw [airyPQc_ofReal, Complex.norm_real, Real.norm_eq_abs]
  rw [hnP1, hnP] at hP1
  rw [hnQ1, hnQ] at hQ1
  have hWdef : airyPQW P Q (t : ℂ) = max |p0| (|q0| * ρ) := by rw [airyPQW, hnP, hnQ]
  have hD : airyPQDr P Q t = p0 ^ 2 + p0 * q1 - q0 * p1 + ρ ^ 2 * q0 ^ 2 := by
    rw [hρ2]; unfold airyPQDr; ring
  have hp1b : |p1| * ρ ^ 2 ≤ L1 * |p0| := by rw [hρ2]; exact hP1
  have hq1b : |q1| * ρ ^ 2 ≤ L2 * |q0| := by rw [hρ2]; exact hQ1
  have hL : L1 + L2 ≤ 8 * ρ := by linarith
  have e1 : p0 * q1 ≥ -(|p0| * |q1|) := by
    have := neg_abs_le (p0 * q1); rw [abs_mul] at this; linarith
  have e2 : q0 * p1 ≤ |q0| * |p1| := by
    have := le_abs_self (q0 * p1); rw [abs_mul] at this; linarith
  have hsq1 : p0 ^ 2 = |p0| ^ 2 := (sq_abs p0).symm
  have hsq2 : q0 ^ 2 = |q0| ^ 2 := (sq_abs q0).symm
  rcases airyPQ_domP_or_domQ P Q hPQ with h | h
  · obtain ⟨hdom, -, hpos⟩ := hdP h
    rw [hnP, hnQ, ← hρ] at hdom
    rw [hnP] at hpos
    have hW : airyPQW P Q (t : ℂ) = |p0| := by
      rw [hWdef]; exact max_eq_left (by linarith)
    refine ⟨by rw [hW]; exact hpos, ?_⟩
    rw [hW, hD]
    have := airyPQ_D_arith1 (abs_nonneg p0) (abs_nonneg q0) (abs_nonneg p1) (abs_nonneg q1) hρ1 hL hp1b hq1b
      (by linarith)
    have h5 : 0 ≤ ρ ^ 2 * q0 ^ 2 := by positivity
    linarith
  · obtain ⟨hdom, -, hpos⟩ := hdQ h
    rw [hnP, hnQ, ← hρ] at hdom
    rw [hnQ] at hpos
    have hρ0 : 0 < ρ := by linarith
    have hW : airyPQW P Q (t : ℂ) = |q0| * ρ := by
      rw [hWdef]; exact max_eq_right (by linarith [abs_nonneg p0])
    refine ⟨by rw [hW]; exact mul_pos hpos hρ0, ?_⟩
    rw [hW, hD]
    have := airyPQ_D_arith2 (abs_nonneg p0) (abs_nonneg q0) hρ1 hL hp1b hq1b
      (by linarith)
    have h6 : (|q0| * ρ) ^ 2 = ρ ^ 2 * q0 ^ 2 := by rw [mul_pow, sq_abs]; ring
    have h7 : q0 ^ 2 ≤ ρ ^ 2 * q0 ^ 2 := by nlinarith [sq_nonneg q0]
    have h8 := sq_nonneg p0
    linarith

/-! ### The weight bound -/

/-- **Weight bound.** For `t ≤ -T` and a zero `t` of `N`: `‖D(t)/N'(t)²‖ ≤ 882 π² / √(-t)`. -/
theorem airyPQ_weight_norm_le {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, t ≤ -T → airyPQN P Q (t : ℂ) = 0 →
      ‖airyPQD P Q (t : ℂ) / airyPQN' P Q (t : ℂ) ^ 2‖ ≤ 882 * π ^ 2 * (1 / √(-t)) := by
  obtain ⟨T, hT1, hT⟩ := airyPQ_D_lower P Q (Or.inr hQ)
  refine ⟨T, hT1, fun t ht h => ?_⟩
  obtain ⟨hWpos, hDl⟩ := hT t ht
  obtain ⟨hD, hd⟩ := airyPQ_zero_weight_pos hHB hQ h
  have htneg : t < 0 := by linarith
  have hab : ‖(t : ℂ)‖ = -t := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg htneg]
  have hM : airyPQM P Q (t : ℂ) = airyPQM P Q (t : ℂ) - I * airyPQN P Q (t : ℂ) := by rw [h]; ring
  have hnum := airyPQ_num_le P Q (u := (t : ℂ)) (by simp) (by rw [hab]; linarith)
  rw [← hM, airyEnv_ofReal_neg htneg, mul_one, hab] at hnum
  have hDn : airyPQD P Q (t : ℂ) = ((airyPQDr P Q t : ℝ) : ℂ) := airyPQD_ofReal P Q t
  have hnt : 0 < ‖airyPQN' P Q (t : ℂ)‖ := norm_pos_iff.mpr hd
  have hprod : ‖airyPQN' P Q (t : ℂ)‖ * ‖airyPQM P Q (t : ℂ)‖ = airyPQDr P Q t / π := by
    have h1 := airyPQ_mul_at_zero (P := P) (Q := Q) h
    have := congrArg norm h1
    rw [norm_mul, norm_neg, norm_mul, hDn, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hD, abs_of_pos (by positivity : (0 : ℝ) < 1 / π)] at this
    rw [this]; field_simp
  rw [hDn, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
  set Dv := airyPQDr P Q t with hDv
  set a := ‖airyPQN' P Q (t : ℂ)‖ with ha
  set m := ‖airyPQM P Q (t : ℂ)‖ with hm
  have hm0 : 0 ≤ m := norm_nonneg _
  have hpi := Real.pi_pos
  have hmpos : 0 < m := by
    rcases hm0.lt_or_eq with h1 | h1
    · exact h1
    · rw [← h1, mul_zero] at hprod
      have : 0 < Dv / π := by positivity
      linarith
  have e1 : Dv / a ^ 2 = π ^ 2 * m ^ 2 / Dv := by
    have ha' : a = Dv / (π * m) := by
      have hpm : π * m ≠ 0 := by positivity
      rw [eq_div_iff hpm]
      calc a * (π * m) = (a * m) * π := by ring
        _ = Dv / π * π := by rw [hprod]
        _ = Dv := by field_simp
    rw [ha']
    field_simp
  rw [e1]
  have hsq : 0 < √(-t) := Real.sqrt_pos.mpr (by linarith)
  have hm2 : m ^ 2 ≤ 441 * airyPQW P Q (t : ℂ) ^ 2 / √(-t) := by simpa using hnum
  rw [div_le_iff₀ hD]
  have h3 : π ^ 2 * m ^ 2 ≤ π ^ 2 * (441 * airyPQW P Q (t : ℂ) ^ 2 / √(-t)) :=
    mul_le_mul_of_nonneg_left hm2 (by positivity)
  have h4 : 882 * π ^ 2 * (1 / √(-t)) * Dv ≥ 882 * π ^ 2 * (1 / √(-t)) * (airyPQW P Q (t : ℂ) ^ 2 / 2) := by
    gcongr
  have h5 : 882 * π ^ 2 * (1 / √(-t)) * (airyPQW P Q (t : ℂ) ^ 2 / 2) =
      π ^ 2 * (441 * airyPQW P Q (t : ℂ) ^ 2 / √(-t)) := by field_simp; ring
  linarith

/-! ### Position data of the zeros (indices in the gaps of `Ai`) -/

/-- The root `x = √(-t)` of a point with index `n ≥ 1` (not a zero of `Ai`) lies above `ρ_n = √(-a_n)`. -/
lemma airyPQ_root_gt {t : ℝ} (hA : airyAi t ≠ 0) (hn : 1 ≤ airyNIdx t) :
    airyZeroRoot (airyNIdx t) < √(-t) := by
  have h1 := (airyNIdx_gap hA (j := airyNIdx t) hn).1 le_rfl
  rw [airyZeroRoot]
  exact Real.sqrt_lt_sqrt (neg_nonneg.mpr (airyZero_nonpos _)) (by linarith)

/-- **Growth**: `(n+1)² ≤ x⁶` for a point `t ≤ -1` of index `n` (not a zero of `Ai`). -/
lemma airyPQ_root_growth {t : ℝ} (hA : airyAi t ≠ 0) (ht : t ≤ -1) :
    ((airyNIdx t : ℝ) + 1) ^ 2 ≤ (√(-t)) ^ 6 := by
  have hx1 := ncRoot_ge_one ht
  rcases Nat.eq_zero_or_pos (airyNIdx t) with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero, zero_add, one_pow]
    exact one_le_pow₀ hx1
  · have hgt := airyPQ_root_gt hA hpos
    have h6 := airyZeroRoot_sixth_ge hpos
    have hρ0 := (airyZeroRoot_pos (airyNIdx t)).le
    have : airyZeroRoot (airyNIdx t) ^ 6 ≤ (√(-t)) ^ 6 := pow_le_pow_left₀ hρ0 hgt.le 6
    have hn1 : (1 : ℝ) ≤ airyNIdx t := by exact_mod_cast hpos
    nlinarith

/-- **Separation up to a shift of one index.** -/
lemma airyPQ_root_sep {t₁ t₂ : ℝ} (h₂ : airyAi t₂ ≠ 0) (ht₁ : t₁ ≤ -1) (hn : airyNIdx t₁ + 2 ≤ airyNIdx t₂) :
    (airyNIdx t₂ : ℝ) - airyNIdx t₁ - 1 ≤ (√(-t₂) - √(-t₁)) * (√(-t₂)) ^ 2 := by
  set n := airyNIdx t₁ with hn1
  set m := airyNIdx t₂ with hm
  have hpos : 1 ≤ m := by omega
  have hgt := airyPQ_root_gt h₂ hpos
  have hlt := ncRoot_lt (t := t₁) (by linarith)
  have hs := airyRoot_sep_lt (n := n) (m := m - 1) (by omega)
  rw [show m - 1 + 1 = m by omega] at hs
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub hpos]; simp
  rw [hcast] at hs
  have hρn : airyZeroRoot (n + 1) < airyZeroRoot m := airyZeroRoot_lt (by omega) (by omega)
  have hρm0 := (airyZeroRoot_pos m).le
  have hd : airyZeroRoot m - airyZeroRoot (n + 1) ≤ √(-t₂) - √(-t₁) := by linarith
  have hsq : airyZeroRoot m ^ 2 ≤ (√(-t₂)) ^ 2 := pow_le_pow_left₀ hρm0 hgt.le 2
  have hpos' : 0 ≤ airyZeroRoot m - airyZeroRoot (n + 1) := by linarith
  calc (m : ℝ) - n - 1 = ((m : ℝ) - 1) - n := by ring
    _ ≤ _ := hs
    _ ≤ (√(-t₂) - √(-t₁)) * (√(-t₂)) ^ 2 := mul_le_mul hd hsq (by positivity) (by linarith)

/-- Symmetric form of the separation, for two points `≤ -1` which are not zeros of `Ai`. -/
lemma airyPQ_root_sep_abs {t₁ t₂ : ℝ} (h₁ : airyAi t₁ ≠ 0) (h₂ : airyAi t₂ ≠ 0) (ht₁ : t₁ ≤ -1) (ht₂ : t₂ ≤ -1) :
    |(airyNIdx t₁ : ℝ) - airyNIdx t₂| - 1 ≤ |√(-t₁) - √(-t₂)| * (max (√(-t₁)) (√(-t₂))) ^ 2 := by
  have hnn : 0 ≤ |√(-t₁) - √(-t₂)| * (max (√(-t₁)) (√(-t₂))) ^ 2 := by positivity
  by_cases hn : airyNIdx t₁ + 2 ≤ airyNIdx t₂
  · have h := airyPQ_root_sep h₂ ht₁ hn
    have hq : (airyNIdx t₁ : ℝ) + 2 ≤ airyNIdx t₂ := by exact_mod_cast hn
    have hc : √(-t₁) < √(-t₂) := by
      by_contra hcon
      push Not at hcon
      have : (√(-t₂) - √(-t₁)) * (√(-t₂)) ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      linarith
    rw [abs_sub_comm (√(-t₁)), abs_of_nonneg (by linarith : (0 : ℝ) ≤ √(-t₂) - √(-t₁)), max_eq_right hc.le,
      abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (airyNIdx t₂ : ℝ) - airyNIdx t₁)]
    linarith
  by_cases hn2 : airyNIdx t₂ + 2 ≤ airyNIdx t₁
  · have h := airyPQ_root_sep h₁ ht₂ hn2
    have hq : (airyNIdx t₂ : ℝ) + 2 ≤ airyNIdx t₁ := by exact_mod_cast hn2
    have hc : √(-t₂) < √(-t₁) := by
      by_contra hcon
      push Not at hcon
      have : (√(-t₁) - √(-t₂)) * (√(-t₁)) ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      linarith
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ √(-t₁) - √(-t₂)), max_eq_left hc.le,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ (airyNIdx t₁ : ℝ) - airyNIdx t₂)]
    linarith
  · have h1 : (airyNIdx t₁ : ℝ) ≤ airyNIdx t₂ + 1 := by exact_mod_cast (by omega : airyNIdx t₁ ≤ airyNIdx t₂ + 1)
    have h2 : (airyNIdx t₂ : ℝ) ≤ airyNIdx t₁ + 1 := by exact_mod_cast (by omega : airyNIdx t₂ ≤ airyNIdx t₁ + 1)
    have : |(airyNIdx t₁ : ℝ) - airyNIdx t₂| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith

/-- `Ai(t) ≠ 0` at a zero of `N` beyond the real roots of `Q`. -/
lemma airyPQ_airyAi_ne {P Q : ℝ[X]} {t : ℝ} (hQt : Q.eval t ≠ 0) (h : airyPQN P Q (t : ℂ) = 0) : airyAi t ≠ 0 := by
  intro h0
  rw [airyPQN_ofReal, Complex.ofReal_eq_zero, h0, mul_zero, zero_add] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact hQt h1
  · exact airyAi_ne_zero_of_deriv_zero h1 h0

/-- info: 'FormalResearch.Special.airyPQ_D_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_D_lower

/-- info: 'FormalResearch.Special.airyPQ_weight_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_weight_norm_le

end FormalResearch.Special
