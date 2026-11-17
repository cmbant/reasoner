module

public import FormalResearch.Special.DiscreteAiryKappaOrderUp
public import FormalResearch.Special.DiscreteAiryKappaMain

/-!
# Order-sharp lower bound for `κ`, abstract part (plan K1, steps 3-5)

Mass accounting `N = Σ Ŷ_k² ≤ Q κ² N^{2/3}` for a sequence `Y = κ g Ai(X) + rest` that is controlled
on the window `[J, k_T]` (`X_J ≍ -δ^{-2}`, `X_{k_T} ≈ δ^{-1}`), bounded on the left by the Hahn bound `kl_hahn_left` (`hleft`) and
monotone beyond `k_T` (`kr_chain_mono`, `hmono`):

* left `k ≤ J + 1`: `Y_k² ≤ C_l(Y_J² + Y_{J+1}²)`, `Ai(X_J)² ≤ 2/√|X_J| ≲ δ` (`kai_sq_le`), so the left mass is `≲ κ² δ^{-2}`;
* window `k ≤ m+1`: `Σ Ai(X_k)² ≲ δ^{-2}` from `kai_sum_upper_bound` (the antiderivative `x Ai² - Ai'²` and `airyKer_diag_neg`);
* `m + 2 ≤ k < k_T`: `|Y_k| ≲ |κ|` and `≲ δ^{-2}` sites;
* `k ≥ k_T`: `Y_k² ≤ Y_{k_T}² ≲ κ² δ` (`Ai(X) ≤ 3e^{-2X/3}`) and `≤ N = δ^{-3}` sites.

**Claim class: proved** (abstract).
-/

@[expose] public section

open Finset

namespace FormalResearch.Special

/-- `|Ai X| ≤ 3 e^{-2X/3}` for `X ≥ 1`. -/
lemma kk_ai_tail {X : ℝ} (hX : 1 ≤ X) : |airyAi X| ≤ 3 * Real.exp (-(2 / 3) * X) := by
  have h := airyAiC_envelope (X : ℂ)
  rw [norm_airyAiC_ofReal, re_ofReal_cpow_three_halves, Complex.norm_real, Real.norm_eq_abs] at h
  have h1 : (1 + |X|) ^ (-(1 / 4) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg X]) (by norm_num)
  have h0 : 0 ≤ X := by linarith
  have h2 : X ≤ (max X 0) ^ (3 / 2 : ℝ) := by
    rw [max_eq_left h0]
    calc X = X ^ (1 : ℝ) := (Real.rpow_one X).symm
      _ ≤ X ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
  have h3 : Real.exp (-(2 / 3) * (max X 0) ^ (3 / 2 : ℝ)) ≤ Real.exp (-(2 / 3) * X) :=
    Real.exp_le_exp.2 (by linarith)
  have h4 : 0 ≤ (1 + |X|) ^ (-(1 / 4) : ℝ) := Real.rpow_nonneg (by positivity) _
  have h5 := Real.exp_pos (-(2 / 3) * (max X 0) ^ (3 / 2 : ℝ))
  calc |airyAi X| ≤ _ := h
    _ ≤ 3 * 1 * Real.exp (-(2 / 3) * X) := by gcongr
    _ = _ := by ring

/-- `e^{-(4/3)X} ≤ δ` for `X ≥ 1/δ`, `0 < δ ≤ 1`... (`δ > 0` suffices). -/
lemma kk_exp_small {δ X : ℝ} (hδ : 0 < δ) (hX : 1 / δ ≤ X) : Real.exp (-(4 / 3) * X) ≤ δ := by
  have h1 : 1 + (4 / 3) * (1 / δ) ≤ Real.exp ((4 / 3) * X) := by
    have := Real.add_one_le_exp ((4 / 3) * X)
    nlinarith
  have h2 : Real.exp (-(4 / 3) * X) = (Real.exp ((4 / 3) * X))⁻¹ := by rw [neg_mul, Real.exp_neg]
  rw [h2]
  have hp : 0 < 1 + (4 / 3) * (1 / δ) := by positivity
  have h3 : (Real.exp ((4 / 3) * X))⁻¹ ≤ (1 + (4 / 3) * (1 / δ))⁻¹ := inv_anti₀ hp h1
  refine h3.trans ?_
  rw [inv_le_comm₀ hp hδ, inv_eq_one_div]
  have : 1 / δ ≤ 1 + (4 / 3) * (1 / δ) := by
    have : 0 ≤ 1 / δ := by positivity
    linarith
  exact this

/-- Pointwise: `Y = κ g A + e`, `|e| ≤ ρ`, `|g| ≤ G` give `Y² ≤ 2 G² κ² A² + 2 ρ²`. -/
lemma kk_y_le {Y g A κ ρ G : ℝ} (hr : |Y - κ * (g * A)| ≤ ρ) (hg : |g| ≤ G) :
    Y ^ 2 ≤ 2 * G ^ 2 * κ ^ 2 * A ^ 2 + 2 * ρ ^ 2 := by
  have h1 : (Y - κ * (g * A)) ^ 2 ≤ ρ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hr 2
  have h2 : (κ * (g * A)) ^ 2 ≤ G ^ 2 * κ ^ 2 * A ^ 2 := by
    have : g ^ 2 ≤ G ^ 2 := by rw [← sq_abs g]; exact pow_le_pow_left₀ (abs_nonneg _) hg 2
    have h3 : (κ * (g * A)) ^ 2 = g ^ 2 * (κ ^ 2 * A ^ 2) := by ring
    rw [h3]; nlinarith [mul_nonneg (sq_nonneg κ) (sq_nonneg A)]
  nlinarith [sq_nonneg (Y - κ * (g * A) - κ * (g * A))]

/-- `Σ_{Ico a c} = Σ_{Ico a b} + Σ_{Ico b c}` over `ℤ`. -/
lemma kk_ico_split (f : ℤ → ℝ) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    ∑ k ∈ Finset.Ico a c, f k = ∑ k ∈ Finset.Ico a b, f k + ∑ k ∈ Finset.Ico b c, f k := by
  rw [← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive a b c), Finset.Ico_union_Ico_eq_Ico hab hbc]

/-- A bound `f ≤ B` on `Ico a b` gives `Σ ≤ (b - a) B`. -/
lemma kk_ico_bound (f : ℤ → ℝ) {a b : ℤ} {B : ℝ} (hab : a ≤ b) (hB : ∀ k ∈ Finset.Ico a b, f k ≤ B) :
    ∑ k ∈ Finset.Ico a b, f k ≤ ((b - a : ℤ) : ℝ) * B := by
  have := Finset.sum_le_card_nsmul (Finset.Ico a b) f B hB
  rw [Int.card_Ico, nsmul_eq_mul] at this
  have e : (((b - a).toNat : ℕ) : ℝ) = ((b - a : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  rwa [e] at this

/-- `Σ_{Ico a b} f = Σ_{i < b - a} f (a + i)`. -/
lemma kk_ico_range (f : ℤ → ℝ) {a b : ℤ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, f k = ∑ i ∈ range (b - a).toNat, f (a + (i : ℤ)) := by
  have hIco : Finset.Ico a b = (Finset.range (b - a).toNat).image (fun i : ℕ => a + (i : ℤ)) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hk
      exact ⟨(k - a).toNat, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [hIco, Finset.sum_image (by intro i _ j _ hij; simpa using hij)]

/-- **The window sum of `Ai²`**: lattice `X` with gaps in `[ε₀, ε']` on `[J, m+1)`, `X_J ≤ -1`, `X_m ≥ 0`, `X_{m+1} ≤ 1/4`:
`Σ_{J ≤ k < m+2} Ai(X_k)² ≤ (√y_J/π + 1/y_J + 2ε' y_J)/ε₀ + 9(5/(4ε₀) + 2)`, `y_J = -X_J`. -/
lemma kk_win_ai {X : ℤ → ℝ} {J m : ℤ} {ε0 ε' : ℝ} (hJm : J ≤ m) (hε0 : 0 < ε0) (hε' : 0 ≤ ε')
    (hgap : ∀ k : ℤ, J ≤ k → k < m + 1 → ε0 ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ ε')
    (hXJ : X J ≤ -1) (hXm : 0 ≤ X m) (hXm1 : X (m + 1) ≤ 1 / 4) :
    ∑ k ∈ Finset.Ico J (m + 2), airyAi (X k) ^ 2 ≤
      (√(-X J) / Real.pi + 1 / (-X J) + 2 * ε' * (-X J)) / ε0 + 9 * (5 / (4 * ε0) + 2) := by
  obtain ⟨kb, hkb1, hkb2, hkb3, hkb4⟩ := kk_ivt (X := X) (t := -1) hXJ (by linarith) hJm
  rw [kk_ico_split _ hkb1 (by omega : kb ≤ m + 2)]
  have hS1 : ∑ k ∈ Finset.Ico J kb, airyAi (X k) ^ 2 ≤
      (√(-X J) / Real.pi + 1 / (-X J) + 2 * ε' * (-X J)) / ε0 := by
    rw [kk_ico_range _ hkb1, le_div_iff₀ hε0, mul_comm]
    have := kai_sum_upper_bound (X := X) (a := J) (ε0 := ε0) (ε' := ε') (kb - J).toNat
      (fun i hi => by
        have h := hgap (J + (i : ℤ)) (by omega) (by omega)
        have e : J + ((i + 1 : ℕ) : ℤ) = J + (i : ℤ) + 1 := by push_cast; ring
        rw [e]; exact h) hε0 hε' hXJ (by rw [show J + ((kb - J).toNat : ℤ) = kb by omega]; exact hkb3)
    exact this
  have hS2 : ∑ k ∈ Finset.Ico kb (m + 2), airyAi (X k) ^ 2 ≤ 9 * (5 / (4 * ε0) + 2) := by
    have hb := kk_ico_bound (fun k => airyAi (X k) ^ 2) (a := kb) (b := m + 2) (B := 9) (by omega)
      (fun k _ => by
        have := kf_abs_airyAi_le (X k)
        have h2 : airyAi (X k) ^ 2 ≤ 3 ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
        linarith)
    have hspan := kk_span (X := X) (J := kb + 1) (m := m + 1) (ε0 := ε0) (by omega)
      (fun k h1 h2 => (hgap k (by omega) h2).1)
    have hc : ((m + 2 - kb : ℤ) : ℝ) ≤ 5 / (4 * ε0) + 2 := by
      have h1 : ((m + 1 - (kb + 1) : ℤ) : ℝ) * ε0 ≤ 5 / 4 := by linarith
      have h2 : ((m + 1 - (kb + 1) : ℤ) : ℝ) ≤ 5 / (4 * ε0) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have e : ((m + 2 - kb : ℤ) : ℝ) = ((m + 1 - (kb + 1) : ℤ) : ℝ) + 2 := by push_cast; ring
      rw [e]; linarith
    calc _ ≤ ((m + 2 - kb : ℤ) : ℝ) * 9 := hb
      _ ≤ (5 / (4 * ε0) + 2) * 9 := mul_le_mul_of_nonneg_right hc (by norm_num)
      _ = _ := by ring
  linarith

/-- info: 'FormalResearch.Special.kk_win_ai' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kk_win_ai

end FormalResearch.Special
