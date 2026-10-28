import FormalResearch.FourQubitEntropy.SpinFlipOddSector

/-!
# Odd-`n` purity--T-odd-purity tradeoff: the concrete cases `n = 5, 7, 9`

Source: `ResearchNotes/QI/seven_qubit_entanglement/spinflip_tradeoff.tex` (QIprojects PR #200),
`thm:odd-spinflip-tradeoff`, instances `n = 5, 7, 9`.

With `π_m = purMean ψ m` (`m = (n-1)/2`) and `O = Omean ψ` (the Pauli-sector form of the mean T-odd purity of
the single-qubit complements, `SpinFlipOddSector.lean`), for a unit vector `ψ`:

* `odd_tradeoff_five`  : `π_2 + O = 1/2 + A_1/5`,
* `odd_tradeoff_seven` : `π_3 + 2 O = 1/2 + (3/28) A_1 + (3/140) A_3`,
* `odd_tradeoff_nine`  : `π_4 + 3 O = 1/2 + (31/576) A_1 + (67/5376) A_3 + (29/8064) A_5 + (1/2304) A_7`,

each proved by `linear_combination` of `Pur_eq`, `Pur_compl`, `A_zero` and `Omean_eq` (multipliers computed
exactly offline).  `_ge` is `π_m + (n-3)/2 · O ≥ 1/2`; `_eq_iff` characterises equality by the vanishing of
`A_j` on the (strictly positive) support of the weights.  Claim class: **proved**.  The general odd `n` is in
`SpinFlipTradeoffOddGeneral.lean`; these concrete cases are independent of it. The paper's sharp coefficient
`c_n` (`c_5 = 1`, `c_n = (n+1)/4` for `n ≥ 7`; the statement of record) is formalized in `SpinFlipTradeoffOddSharp.lean`;
the `(n-3)/2` forms here are weaker for `n ≥ 9` (the same at `n = 5, 7`).
-/

open FormalResearch.FrameFree.NQubit

namespace FormalResearch.FourQubitEntropy.SpinFlip

/-- `thm:odd-spinflip-tradeoff` at `n = 5` (identity; `linear_combination` of `Pur_eq`, `Pur_compl`, `A_zero`
and `Omean_eq`). -/
theorem odd_tradeoff_five (ψ : Ψ 5) (hψ : nsq ψ = 1) :
    purMean ψ 2 + ((5 : ℝ) - 3) / 2 * Omean ψ = 1 / 2 + (1/5) * A ψ 1 := by
  have hO := Omean_eq (n := 5) (by norm_num) ψ
  have hA0 := A_zero ψ
  rw [hψ] at hA0
  have hE2 := Pur_eq ψ 2
  have hE3 := Pur_eq ψ 3
  have hC2 := Pur_compl ψ 2 (by norm_num)
  unfold purMean
  rw [hO]
  norm_num [Finset.sum_range_succ, Nat.choose, Nat.odd_iff] at hE2 hE3 hC2 hA0 ⊢
  linear_combination (3/40) * hE2 + (-1/40) * hE3 + (-1/5) * hC2 + (1/2) * hA0

/-- `thm:odd-spinflip-tradeoff` at `n = 5`: `π_2 + (5-3)/2 · O ≥ 1/2`. -/
theorem odd_tradeoff_five_ge (ψ : Ψ 5) (hψ : nsq ψ = 1) :
    1 / 2 ≤ purMean ψ 2 + ((5 : ℝ) - 3) / 2 * Omean ψ := by
  rw [odd_tradeoff_five ψ hψ]
  have h1 := A_nonneg ψ 1
  linarith

/-- Equality case at `n = 5`: equality iff `A_j = 0` for `j` in the support of the weights. -/
theorem odd_tradeoff_five_eq_iff (ψ : Ψ 5) (hψ : nsq ψ = 1) :
    purMean ψ 2 + ((5 : ℝ) - 3) / 2 * Omean ψ = 1 / 2 ↔ A ψ 1 = 0 := by
  rw [odd_tradeoff_five ψ hψ]
  have h1 := A_nonneg ψ 1
  constructor
  · intro h
    exact by linarith
  · intro e1
    rw [e1]; norm_num


/-- `thm:odd-spinflip-tradeoff` at `n = 7` (identity; `linear_combination` of `Pur_eq`, `Pur_compl`, `A_zero`
and `Omean_eq`). -/
theorem odd_tradeoff_seven (ψ : Ψ 7) (hψ : nsq ψ = 1) :
    purMean ψ 3 + ((7 : ℝ) - 3) / 2 * Omean ψ = 1 / 2 + (3/28) * A ψ 1 + (3/140) * A ψ 3 := by
  have hO := Omean_eq (n := 7) (by norm_num) ψ
  have hA0 := A_zero ψ
  rw [hψ] at hA0
  have hE2 := Pur_eq ψ 2
  have hE3 := Pur_eq ψ 3
  have hE4 := Pur_eq ψ 4
  have hE5 := Pur_eq ψ 5
  have hC2 := Pur_compl ψ 2 (by norm_num)
  have hC3 := Pur_compl ψ 3 (by norm_num)
  unfold purMean
  rw [hO]
  norm_num [Finset.sum_range_succ, Nat.choose, Nat.odd_iff] at hE2 hE3 hE4 hE5 hC2 hC3 hA0 ⊢
  linear_combination (1/14) * hE2 + (-1/20) * hE3 + (3/112) * hE4 + (-1/112) * hE5 + (-2/7) * hC2 + (3/7) * hC3 + (1/2) * hA0

/-- `thm:odd-spinflip-tradeoff` at `n = 7`: `π_3 + (7-3)/2 · O ≥ 1/2`. -/
theorem odd_tradeoff_seven_ge (ψ : Ψ 7) (hψ : nsq ψ = 1) :
    1 / 2 ≤ purMean ψ 3 + ((7 : ℝ) - 3) / 2 * Omean ψ := by
  rw [odd_tradeoff_seven ψ hψ]
  have h1 := A_nonneg ψ 1; have h3 := A_nonneg ψ 3
  linarith

/-- Equality case at `n = 7`: equality iff `A_j = 0` for `j` in the support of the weights. -/
theorem odd_tradeoff_seven_eq_iff (ψ : Ψ 7) (hψ : nsq ψ = 1) :
    purMean ψ 3 + ((7 : ℝ) - 3) / 2 * Omean ψ = 1 / 2 ↔ A ψ 1 = 0 ∧ A ψ 3 = 0 := by
  rw [odd_tradeoff_seven ψ hψ]
  have h1 := A_nonneg ψ 1; have h3 := A_nonneg ψ 3
  constructor
  · intro h
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨e1, e3⟩
    rw [e1, e3]; norm_num


/-- `thm:odd-spinflip-tradeoff` at `n = 9` (identity; `linear_combination` of `Pur_eq`, `Pur_compl`, `A_zero`
and `Omean_eq`). -/
theorem odd_tradeoff_nine (ψ : Ψ 9) (hψ : nsq ψ = 1) :
    purMean ψ 4 + ((9 : ℝ) - 3) / 2 * Omean ψ = 1 / 2 + (31/576) * A ψ 1 + (67/5376) * A ψ 3 + (29/8064) * A ψ 5 + (1/2304) * A ψ 7 := by
  have hO := Omean_eq (n := 9) (by norm_num) ψ
  have hA0 := A_zero ψ
  rw [hψ] at hA0
  have hE2 := Pur_eq ψ 2
  have hE3 := Pur_eq ψ 3
  have hE4 := Pur_eq ψ 4
  have hE5 := Pur_eq ψ 5
  have hE6 := Pur_eq ψ 6
  have hE7 := Pur_eq ψ 7
  have hC2 := Pur_compl ψ 2 (by norm_num)
  have hC3 := Pur_compl ψ 3 (by norm_num)
  have hC4 := Pur_compl ψ 4 (by norm_num)
  unfold purMean
  rw [hO]
  norm_num [Finset.sum_range_succ, Nat.choose, Nat.odd_iff] at hE2 hE3 hE4 hE5 hE6 hE7 hC2 hC3 hC4 hA0 ⊢
  linear_combination (5/72) * hE2 + (-5/96) * hE3 + (5/168) * hE4 + (-59/4032) * hE5 + (5/768) * hE6 + (-5/2304) * hE7 + (-5/18) * hC2 + (5/12) * hC3 + (-59/126) * hC4 + (1/2) * hA0

/-- `thm:odd-spinflip-tradeoff` at `n = 9`: `π_4 + (9-3)/2 · O ≥ 1/2`. -/
theorem odd_tradeoff_nine_ge (ψ : Ψ 9) (hψ : nsq ψ = 1) :
    1 / 2 ≤ purMean ψ 4 + ((9 : ℝ) - 3) / 2 * Omean ψ := by
  rw [odd_tradeoff_nine ψ hψ]
  have h1 := A_nonneg ψ 1; have h3 := A_nonneg ψ 3; have h5 := A_nonneg ψ 5; have h7 := A_nonneg ψ 7
  linarith

/-- Equality case at `n = 9`: equality iff `A_j = 0` for `j` in the support of the weights. -/
theorem odd_tradeoff_nine_eq_iff (ψ : Ψ 9) (hψ : nsq ψ = 1) :
    purMean ψ 4 + ((9 : ℝ) - 3) / 2 * Omean ψ = 1 / 2 ↔ A ψ 1 = 0 ∧ A ψ 3 = 0 ∧ A ψ 5 = 0 ∧ A ψ 7 = 0 := by
  rw [odd_tradeoff_nine ψ hψ]
  have h1 := A_nonneg ψ 1; have h3 := A_nonneg ψ 3; have h5 := A_nonneg ψ 5; have h7 := A_nonneg ψ 7
  constructor
  · intro h
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨e1, e3, e5, e7⟩
    rw [e1, e3, e5, e7]; norm_num


end FormalResearch.FourQubitEntropy.SpinFlip
