import FormalResearch.FourQubitEntropy.SpinFlipTradeoffOddGHZ

/-!
# The sharp odd-`n` tradeoff `π_m + c_n O ≥ 1/2` with `c_5 = 1`, `c_n = (n+1)/4`

Source: `ResearchNotes/QI/seven_qubit_entanglement/spinflip_tradeoff.tex` (QIprojects PR #200),
`thm:odd-spinflip-tradeoff` (current form) and the interpretation remark.

With `n = 2m + 1 ≥ 5`, `c_n = cn m` (`1` for `m = 2`, `(m+1)/2 = (n+1)/4` for `m ≥ 3`) and the weights
`sharpW m j = w_j^{(n)}` of `eq:odd-tradeoff-weights` (`sharpNum` is the numerator, with `2 c_n C(n-1, j)`):

* `sharpW_eq`: `w_j^{(n)} = oddW m j + (c_n - (n-3)/2) (n-j)/(n 2^{n-1})`; the `c`-dependent part of `w_j` is exactly
  the coefficient of `A_j` in `Omean_eq`, so
* `odd_tradeoff_sharp`: `π_m + c_n O = 1/2 + Σ_{j odd < n} w_j A_j`, derived from `odd_tradeoff_identity`
  (`SpinFlipTradeoffOddGeneral.lean`) and `Omean_eq` by linear algebra (no new generating-function argument);
* `sharpW_top`, `sharpW_pred`: `w_n = 0` and `w_{n-2} = 0`; `sharpW_pos`: `w_j > 0` for odd `j ≤ n-4`
  (the paper's binomial argument for `n ≥ 7`, and `N_1 = 32` for `n = 5`);
* `odd_tradeoff_sharp_ge`: `π_m + c_n O ≥ 1/2`; `odd_tradeoff_sharp_eq_iff`: equality iff `A_j = 0` for every odd
  `j ≤ n - 4`; `ghz_odd_tradeoff_sharp_eq`: the GHZ state attains equality;
* `sharp_five`, `sharp_seven`, `sharp_nine`: `π_2 + O = 1/2 + A_1/5`, `π_3 + 2O = 1/2 + (3/28) A_1 + (3/140) A_3`,
  `π_4 + (5/2) O = 1/2 + (5/96) A_1 + (5/448) A_3 + (11/4032) A_5`;
* the earlier coefficient `(n-3)/2` is a weaker corollary: `cn_le` (`c_n ≤ (n-3)/2`, equality iff `n ∈ {5, 7}`),
  `Omean_nonneg`, `odd_tradeoff_ge_of_sharp`.

Claim class: **proved** (`nsq ψ = 1` is a hypothesis of the identity).  `O` is `Omean`, the Pauli-sector form of
the mean T-odd purity; its identification with `½(tr ρ² - R_ρ)` is `oddPur_eq_half_sub_Rspin` in
`SpinFlipOddOverlap.lean`.  That `c_n` is optimal over all pure states is open in the paper and not addressed.
-/

open Finset
open FormalResearch.FrameFree.NQubit

namespace FormalResearch.FourQubitEntropy.SpinFlip

variable {m : ℕ}

/-- `c_n` of `thm:odd-spinflip-tradeoff`, `n = 2m+1`: `c_5 = 1`, `c_n = (n+1)/4 = (m+1)/2` for `n ≥ 7`. -/
noncomputable def cn (m : ℕ) : ℝ := if m = 2 then 1 else ((m : ℝ) + 1) / 2

/-- The numerator `N_j^{(n)}` of `eq:odd-tradeoff-weights` with `2 c_n C(n-1, j)`. -/
noncomputable def sharpNum (m j : ℕ) : ℝ :=
  2 ^ m * ((m.choose (j - 1) : ℝ) + 3 * (m.choose j : ℝ))
    + (-1) ^ ((2 * m + 1 - j) / 2) * (m.choose ((2 * m + 1 - j) / 2) : ℝ)
    + 2 * cn m * ((2 * m).choose j : ℝ) - ((2 * m + 1).choose j : ℝ)

/-- The weight `w_j^{(n)}` of `eq:odd-tradeoff-weights`, `n = 2m+1`. -/
noncomputable def sharpW (m j : ℕ) : ℝ :=
  sharpNum m j / (2 ^ (2 * m + 1) * ((2 * m + 1).choose j : ℝ))

theorem cn_two : cn 2 = 1 := by simp [cn]

theorem cn_of_ge (hm : 3 ≤ m) : cn m = ((m : ℝ) + 1) / 2 := by
  unfold cn; simp only [show ¬ (m = 2) by omega, ↓reduceIte]

/-- `c_n ≤ (n-3)/2`, with equality at `n = 5, 7`: the old coefficient is weaker. -/
theorem cn_le (hm : 2 ≤ m) : cn m ≤ ((((2 * m + 1 : ℕ) : ℝ) - 3) / 2) := by
  push_cast
  rcases Nat.lt_or_ge m 3 with h | h
  · have : m = 2 := by omega
    subst this; rw [cn_two]; norm_num
  · rw [cn_of_ge h]
    have : (3 : ℝ) ≤ m := by exact_mod_cast h
    linarith

theorem sharpNum_eq (m j : ℕ) :
    sharpNum m j = oddNum m j + (2 * cn m - (2 * (m : ℝ) - 2)) * ((2 * m).choose j : ℝ) := by
  unfold sharpNum oddNum; ring

/-- `C(2m, j) (2m+1) = C(2m+1, j) (2m+1-j)` in `ℝ`, for `j ≤ 2m+1`. -/
theorem choose_key (m j : ℕ) (hj : j ≤ 2 * m + 1) :
    ((2 * m).choose j : ℝ) * (2 * (m : ℝ) + 1)
      = ((2 * m + 1).choose j : ℝ) * (2 * (m : ℝ) + 1 - j) := by
  have h := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_mul_succ_eq (2 * m) j)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at h
  rw [Nat.cast_sub hj] at h
  push_cast at h
  linarith

/-- The `c`-dependent part of `w_j` is exactly the coefficient of `A_j` in `Omean_eq`. -/
theorem sharpW_eq (m j : ℕ) (hj : j ≤ 2 * m + 1) :
    sharpW m j = oddW m j + (cn m - ((((2 * m + 1 : ℕ) : ℝ) - 3) / 2)) *
      ((((2 * m + 1 : ℕ) : ℝ) - j) / ((((2 * m + 1 : ℕ) : ℝ)) * 2 ^ (2 * m + 1 - 1))) := by
  have hc : (0 : ℝ) < ((2 * m + 1).choose j : ℝ) := by exact_mod_cast Nat.choose_pos hj
  have hkey := choose_key m j hj
  unfold sharpW oddW
  rw [sharpNum_eq, add_div]
  congr 1
  rw [Nat.add_sub_cancel]
  push_cast
  have hn : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  have hd : ((2 * m).choose j : ℝ) = ((2 * m + 1).choose j : ℝ) * (2 * (m : ℝ) + 1 - j) / (2 * (m : ℝ) + 1) := by
    field_simp; linarith
  rw [hd]
  have : (2 : ℝ) ^ (2 * m + 1) = 2 * 2 ^ (2 * m) := by ring
  rw [this]
  field_simp
  ring

/-- `O ≥ 0` (all coefficients in `Omean_eq` are nonnegative). -/
theorem Omean_nonneg (hm : 1 ≤ m) (ψ : Ψ (2 * m + 1)) : 0 ≤ Omean ψ := by
  rw [Omean_eq (by omega)]
  refine Finset.sum_nonneg fun j hj => ?_
  have hjn : j ≤ 2 * m + 1 := Nat.lt_succ_iff.mp (mem_range.mp hj)
  by_cases ho : Odd j
  · simp only [ho, ↓reduceIte]
    apply mul_nonneg _ (A_nonneg ψ j)
    have : (j : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by exact_mod_cast hjn
    apply div_nonneg (by linarith) (by positivity)
  · simp [ho]

section Identity

theorem odd_tradeoff_sharp_identity (ψ : Ψ (2 * m + 1)) (hψ : nsq ψ = 1) :
    purMean ψ m + cn m * Omean ψ
      = 1 / 2 + ∑ j ∈ range (2 * m + 1 + 1), (if Odd j then sharpW m j else 0) * A ψ j := by
  have h1 := odd_tradeoff_identity ψ hψ
  have hO := Omean_eq (n := 2 * m + 1) (by omega) ψ
  have hterm : ∀ j ∈ range (2 * m + 1 + 1),
      (if Odd j then sharpW m j else 0) * A ψ j
        = (if Odd j then oddW m j else 0) * A ψ j
          + (cn m - ((((2 * m + 1 : ℕ) : ℝ) - 3) / 2)) *
            ((if Odd j then ((((2 * m + 1 : ℕ) : ℝ)) - j) / ((((2 * m + 1 : ℕ) : ℝ)) * 2 ^ (2 * m + 1 - 1))
              else 0) * A ψ j) := by
    intro j hj
    have hjn : j ≤ 2 * m + 1 := Nat.lt_succ_iff.mp (mem_range.mp hj)
    by_cases ho : Odd j
    · simp only [ho, ↓reduceIte]
      rw [sharpW_eq m j hjn]; ring
    · simp [ho]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← hO]
  have := h1
  linarith

theorem sharpW_top (hm : 1 ≤ m) : sharpW m (2 * m + 1) = 0 := by
  unfold sharpW
  rw [sharpNum_eq, oddNum_top m hm, Nat.choose_eq_zero_of_lt (by omega : 2 * m < 2 * m + 1)]
  simp

theorem sharpW_pred (hm : 2 ≤ m) : sharpW m (2 * m - 1) = 0 := by
  rcases Nat.lt_or_ge m 3 with h | h
  · have : m = 2 := by omega
    subst this
    unfold sharpW
    rw [sharpNum_eq, cn_two]
    have := oddNum_two_three
    norm_num at this ⊢
    simp [this]
  · unfold sharpW
    rw [sharpNum_eq, oddNum_last m h, cn_of_ge h]
    have h3 : (2 * m).choose (2 * m - 1) = 2 * m :=
      (Nat.choose_symm (n := 2 * m) (k := 1) (by omega)).trans (by simp)
    rw [h3]
    push_cast
    ring_nf

end Identity

section Positivity

theorem sharpNum_pos (m i : ℕ) (hm : 3 ≤ m) (hi : i + 2 ≤ m) : 0 < sharpNum m (2 * i + 1) := by
  have e1 : 2 * m + 1 - (2 * i + 1) = 2 * (m - i) := by omega
  have e2 : 2 * (m - i) / 2 = m - i := by omega
  have hkey := choose_key m (2 * i + 1) (by omega)
  have hmi : ((2 * m + 1 : ℕ) : ℝ) - ((2 * i + 1 : ℕ) : ℝ) = 2 * ((m : ℝ) - i) := by
    push_cast; ring
  have hkey' : ((2 * m).choose (2 * i + 1) : ℝ) * (2 * (m : ℝ) + 1)
      = ((2 * m + 1).choose (2 * i + 1) : ℝ) * (2 * ((m : ℝ) - i)) := by
    rw [hkey]; push_cast; ring
  have hcsym : (2 * m + 1).choose (2 * (m - i)) = (2 * m + 1).choose (2 * i + 1) := by
    rw [← e1]; exact Nat.choose_symm (by omega)
  have hle : (m.choose (m - i) : ℝ) ≤ ((2 * m + 1).choose (2 * i + 1) : ℝ) := by
    rw [← hcsym]
    exact_mod_cast choose_le_choose_double m (m - i) (by omega) (by omega)
  have hcpos : (0 : ℝ) < ((2 * m + 1).choose (2 * i + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hk2 : (2 : ℝ) ≤ (m : ℝ) - i := by
    have : (i : ℝ) + 2 ≤ m := by exact_mod_cast hi
    linarith
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hd : 2 * ((2 * m + 1).choose (2 * i + 1) : ℝ)
      < ((m : ℝ) + 1) * ((2 * m).choose (2 * i + 1) : ℝ) := by
    set c := ((2 * m + 1).choose (2 * i + 1) : ℝ)
    set d := ((2 * m).choose (2 * i + 1) : ℝ)
    have h : (2 * (m : ℝ) + 1) * (((m : ℝ) + 1) * d - 2 * c)
        = 2 * c * (((m : ℝ) + 1) * ((m : ℝ) - i) - (2 * m + 1)) := by
      linear_combination ((m : ℝ) + 1) * hkey'
    have h2 : 0 < 2 * c * (((m : ℝ) + 1) * ((m : ℝ) - i) - (2 * m + 1)) := by
      apply mul_pos (by positivity)
      nlinarith
    rw [← h] at h2
    have := (mul_pos_iff_of_pos_left (by positivity : (0 : ℝ) < 2 * (m : ℝ) + 1)).mp h2
    linarith
  have hs : -(m.choose (m - i) : ℝ) ≤ (-1 : ℝ) ^ (m - i) * (m.choose (m - i) : ℝ) := by
    rcases neg_one_pow_eq_or ℝ (m - i) with h | h <;> rw [h] <;>
      nlinarith [(Nat.cast_nonneg (m.choose (m - i)) : (0 : ℝ) ≤ _)]
  have hF : 0 ≤ (2 : ℝ) ^ m * ((m.choose (2 * i + 1 - 1) : ℝ) + 3 * (m.choose (2 * i + 1) : ℝ)) := by
    positivity
  have h2c : 2 * cn m = (m : ℝ) + 1 := by rw [cn_of_ge hm]; ring
  unfold sharpNum
  rw [e1, e2, h2c]
  linarith

/-- `w_j > 0` for odd `j ≤ n - 4`. -/
theorem sharpW_pos (hm : 2 ≤ m) (j : ℕ) (hj : Odd j) (hjn : j + 4 ≤ 2 * m + 1) : 0 < sharpW m j := by
  obtain ⟨i, rfl⟩ := hj
  rcases Nat.lt_or_ge m 3 with h | h
  · have hm2 : m = 2 := by omega
    have hi0 : i = 0 := by omega
    subst hm2; subst hi0
    show 0 < sharpW 2 1
    norm_num [sharpW, sharpNum, cn, Nat.choose]
  · unfold sharpW
    have hden : (0 : ℝ) < 2 ^ (2 * m + 1) * ((2 * m + 1).choose (2 * i + 1) : ℝ) := by
      have : 0 < (2 * m + 1).choose (2 * i + 1) := Nat.choose_pos (by omega)
      positivity
    exact div_pos (sharpNum_pos m i h (by omega)) hden

end Positivity

section Main

theorem sharp_sum_nonneg (hm : 2 ≤ m) (ψ : Ψ (2 * m + 1)) :
    0 ≤ ∑ j ∈ range (2 * m + 1), (if Odd j then sharpW m j else 0) * A ψ j := by
  refine sum_nonneg fun j hj => ?_
  by_cases ho : Odd j
  · simp only [ho, ↓reduceIte]
    have hjn := mem_range.mp hj
    apply mul_nonneg _ (A_nonneg ψ j)
    by_cases h4 : j + 4 ≤ 2 * m + 1
    · exact (sharpW_pos hm j ho h4).le
    · have : j + 2 = 2 * m + 1 := by
        obtain ⟨i, rfl⟩ := ho; omega
      have hj' : j = 2 * m - 1 := by omega
      rw [hj', sharpW_pred hm]
  · simp [ho]

/-- **`thm:odd-spinflip-tradeoff`, identity.** For `n = 2m+1 ≥ 5` and a unit vector,
`π_m + c_n O = 1/2 + Σ_{j odd < n} w_j^{(n)} A_j`. -/
theorem odd_tradeoff_sharp (hm : 2 ≤ m) (ψ : Ψ (2 * m + 1)) (hψ : nsq ψ = 1) :
    purMean ψ m + cn m * Omean ψ
      = 1 / 2 + ∑ j ∈ range (2 * m + 1), (if Odd j then sharpW m j else 0) * A ψ j := by
  rw [odd_tradeoff_sharp_identity ψ hψ, sum_range_succ]
  have : (if Odd (2 * m + 1) then sharpW m (2 * m + 1) else 0) * A ψ (2 * m + 1) = 0 := by
    rw [sharpW_top (by omega)]; simp
  rw [this, add_zero]

/-- **`thm:odd-spinflip-tradeoff`, inequality.** `π_m + c_n O ≥ 1/2`. -/
theorem odd_tradeoff_sharp_ge (hm : 2 ≤ m) (ψ : Ψ (2 * m + 1)) (hψ : nsq ψ = 1) :
    1 / 2 ≤ purMean ψ m + cn m * Omean ψ := by
  rw [odd_tradeoff_sharp hm ψ hψ]
  linarith [sharp_sum_nonneg hm ψ]

/-- **`thm:odd-spinflip-tradeoff`, equality.** `π_m + c_n O = 1/2` iff `A_j = 0` for every odd `j ≤ n - 4`. -/
theorem odd_tradeoff_sharp_eq_iff (hm : 2 ≤ m) (ψ : Ψ (2 * m + 1)) (hψ : nsq ψ = 1) :
    purMean ψ m + cn m * Omean ψ = 1 / 2 ↔
      ∀ j ∈ range (2 * m + 1), Odd j → j + 4 ≤ 2 * m + 1 → A ψ j = 0 := by
  rw [odd_tradeoff_sharp hm ψ hψ]
  have hnn : ∀ j ∈ range (2 * m + 1), 0 ≤ (if Odd j then sharpW m j else 0) * A ψ j := by
    intro j hj
    by_cases ho : Odd j
    · simp only [ho, ↓reduceIte]
      have hjn := mem_range.mp hj
      apply mul_nonneg _ (A_nonneg ψ j)
      by_cases h4 : j + 4 ≤ 2 * m + 1
      · exact (sharpW_pos hm j ho h4).le
      · have : j + 2 = 2 * m + 1 := by
          obtain ⟨i, rfl⟩ := ho; omega
        have hj' : j = 2 * m - 1 := by omega
        rw [hj', sharpW_pred hm]
    · simp [ho]
  have h0 : 1 / 2 + ∑ j ∈ range (2 * m + 1), (if Odd j then sharpW m j else 0) * A ψ j = 1 / 2
      ↔ ∑ j ∈ range (2 * m + 1), (if Odd j then sharpW m j else 0) * A ψ j = 0 := by
    constructor <;> intro h <;> linarith
  rw [h0, sum_eq_zero_iff_of_nonneg hnn]
  refine forall_congr' fun j => forall_congr' fun hj => ?_
  by_cases ho : Odd j
  · simp only [ho, ↓reduceIte]
    simp only [true_implies]
    by_cases h4 : j + 4 ≤ 2 * m + 1
    · have hp := sharpW_pos hm j ho h4
      simp only [h4, true_implies]
      constructor
      · intro h; exact (mul_eq_zero.mp h).resolve_left hp.ne'
      · intro h; rw [h, mul_zero]
    · have : j + 2 = 2 * m + 1 := by
        have hjn := mem_range.mp hj
        obtain ⟨i, rfl⟩ := ho; omega
      have hj' : j = 2 * m - 1 := by omega
      rw [hj', sharpW_pred hm, zero_mul]
      exact ⟨fun _ h => absurd h (by omega), fun _ => rfl⟩
  · simp [ho]

/-- The GHZ state attains `π_m + c_n O = 1/2` for every odd `n = 2m + 1 ≥ 5`. -/
theorem ghz_odd_tradeoff_sharp_eq (hm : 2 ≤ m) :
    purMean (ghz (2 * m + 1)) m + cn m * Omean (ghz (2 * m + 1)) = 1 / 2 := by
  rw [odd_tradeoff_sharp_eq_iff hm _ (nsq_ghz (by omega))]
  intro j hj ho _
  exact A_ghz_odd (by omega) ho (mem_range.mp hj)

/-- The earlier coefficient `(n-3)/2` as a weaker corollary of the sharp inequality. -/
theorem odd_tradeoff_ge_of_sharp (hm : 2 ≤ m) (ψ : Ψ (2 * m + 1)) (hψ : nsq ψ = 1) :
    1 / 2 ≤ purMean ψ m + ((((2 * m + 1 : ℕ) : ℝ) - 3) / 2) * Omean ψ := by
  have h1 := odd_tradeoff_sharp_ge hm ψ hψ
  have h2 := mul_le_mul_of_nonneg_right (cn_le hm) (Omean_nonneg (by omega) ψ)
  linarith

/-- Relation of the new and old weights (the old statements `odd_tradeoff`, `odd_tradeoff_eq_iff` remain valid). -/
theorem sharpW_eq_oddW_of_two (j : ℕ) (hj : j ≤ 5) : sharpW 2 j = oddW 2 j := by
  rw [sharpW_eq 2 j (by omega), cn_two]; norm_num

end Main

section Concrete

theorem sharpW_five : sharpW 2 1 = 1 / 5 := by
  norm_num [sharpW, sharpNum, cn, Nat.choose]

theorem sharpW_seven_one : sharpW 3 1 = 3 / 28 := by
  norm_num [sharpW, sharpNum, cn, Nat.choose]

theorem sharpW_seven_three : sharpW 3 3 = 3 / 140 := by
  norm_num [sharpW, sharpNum, cn, Nat.choose]

theorem sharpW_nine_one : sharpW 4 1 = 5 / 96 := by
  norm_num [sharpW, sharpNum, cn, Nat.choose]

theorem sharpW_nine_three : sharpW 4 3 = 5 / 448 := by
  norm_num [sharpW, sharpNum, cn, Nat.choose]

theorem sharpW_nine_five : sharpW 4 5 = 11 / 4032 := by
  norm_num [sharpW, sharpNum, cn, Nat.choose]

/-- `n = 5`: `π_2 + O = 1/2 + A_1/5`. -/
theorem sharp_five (ψ : Ψ 5) (hψ : nsq ψ = 1) :
    purMean ψ 2 + Omean ψ = 1 / 2 + (1 / 5) * A ψ 1 := by
  have h := odd_tradeoff_sharp (m := 2) le_rfl ψ hψ
  rw [cn_two] at h
  simp only [sum_range_succ, sum_range_zero] at h
  have h3 : sharpW 2 3 = 0 := sharpW_pred le_rfl
  rw [sharpW_five, h3] at h
  norm_num [Nat.odd_iff] at h
  linarith

/-- `n = 7`: `π_3 + 2 O = 1/2 + (3/28) A_1 + (3/140) A_3`. -/
theorem sharp_seven (ψ : Ψ 7) (hψ : nsq ψ = 1) :
    purMean ψ 3 + 2 * Omean ψ = 1 / 2 + (3 / 28) * A ψ 1 + (3 / 140) * A ψ 3 := by
  have h := odd_tradeoff_sharp (m := 3) (by norm_num) ψ hψ
  rw [cn_of_ge le_rfl] at h
  simp only [sum_range_succ, sum_range_zero] at h
  have h5 : sharpW 3 5 = 0 := sharpW_pred (by norm_num)
  rw [sharpW_seven_one, sharpW_seven_three, h5] at h
  norm_num [Nat.odd_iff] at h
  linarith

/-- `n = 9`: `π_4 + (5/2) O = 1/2 + (5/96) A_1 + (5/448) A_3 + (11/4032) A_5`. -/
theorem sharp_nine (ψ : Ψ 9) (hψ : nsq ψ = 1) :
    purMean ψ 4 + (5 / 2) * Omean ψ
      = 1 / 2 + (5 / 96) * A ψ 1 + (5 / 448) * A ψ 3 + (11 / 4032) * A ψ 5 := by
  have h := odd_tradeoff_sharp (m := 4) (by norm_num) ψ hψ
  rw [cn_of_ge (by norm_num)] at h
  simp only [sum_range_succ, sum_range_zero] at h
  have h7 : sharpW 4 7 = 0 := sharpW_pred (by norm_num)
  rw [sharpW_nine_one, sharpW_nine_three, sharpW_nine_five, h7] at h
  norm_num [Nat.odd_iff] at h
  linarith

end Concrete

end FormalResearch.FourQubitEntropy.SpinFlip
