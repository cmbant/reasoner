import FormalResearch.FourQubitEntropy.SpinFlipOmega

/-!
# The T-odd purity of single-qubit complements, in Pauli coordinates

Source: `ResearchNotes/QI/seven_qubit_entanglement/spinflip_tradeoff.tex` (QIprojects PR #200),
`lem:odd-sector` (second formula) and the definition of `O(ψ)` before it.

* `oddPur ψ S = 2^{-|S|} Σ_{supp P ⊆ S, wt P odd} ⟨P⟩²` is, by `lem:odd-sector`, the quantity
  `½(tr ρ_S² - R_{ρ_S})`.  **Here it is taken as the definition** (the Pauli-sector form); the
  identification with `½(tr ρ_S² - tr(ρ_S ρ̃_S))` for the explicit spin-flip `ρ̃_S` is proved in
  `SpinFlipOddOverlap.lean` (`oddPur_eq_half_sub_Rspin`), not in this file.
* `Omean ψ = (1/n) Σ_s oddPur ψ ([n] ∖ {s})`: the mean T-odd purity `O(ψ)` of the single-qubit complements.
* `Omean_eq`: `O = Σ_{j odd} (n-j)/(n 2^{n-1}) A_j` (`lem:odd-sector`, last formula), proved for every `n ≥ 1`.
* `PurAvg_eq`: `a_r = Pur ψ r / C(n,r) = 2^{-r} Σ_j C(r,j) A_j / C(n,j)` (the first part of the
  `a_s = Σ_j A_j C(n-j,s-j)/(2^s C(n,s))` formula).

Claim class: **proved** (no hypotheses beyond those displayed).
-/

open scoped ComplexConjugate BigOperators
open FormalResearch.FrameFree.NQubit

namespace FormalResearch.FourQubitEntropy.SpinFlip

variable {n : ℕ}

/-- `2^{-|S|} Σ_{supp P ⊆ S, wt P odd} ⟨P⟩²` (equals `½(tr ρ_S² - R_{ρ_S})`, `lem:odd-sector`). -/
noncomputable def oddPur (ψ : Ψ n) (S : Finset (Fin n)) : ℝ :=
  (∑ a ∈ (wsupp S).filter (fun a => Odd (wt a)), pw ψ a) / 2 ^ S.card

/-- `O(ψ) = (1/n) Σ_s oddPur ψ ([n] ∖ {s})`: mean T-odd purity of the single-qubit complements. -/
noncomputable def Omean (ψ : Ψ n) : ℝ :=
  (1 / (n : ℝ)) * ∑ s : Fin n, oddPur ψ (Finset.univ.erase s)

theorem sum_odd_wsupp (ψ : Ψ n) :
    ∑ s : Fin n, ∑ a ∈ (wsupp (Finset.univ.erase s)).filter (fun a => Odd (wt a)), pw ψ a
      = ∑ a : Fin n → Fin 4, (if Odd (wt a) then ((n : ℝ) - wt a) else 0) * pw ψ a := by
  have h1 : ∀ s : Fin n, ((wsupp (Finset.univ.erase s)).filter (fun a => Odd (wt a)))
      = Finset.univ.filter (fun a : Fin n → Fin 4 => s ∉ nz a ∧ Odd (wt a)) := by
    intro s; ext a
    simp only [Finset.mem_filter, mem_wsupp_iff_nz, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, ho⟩
      refine ⟨fun hs => ?_, ho⟩
      have := h hs; simp at this
    · rintro ⟨h, ho⟩
      refine ⟨fun i hi => ?_, ho⟩
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      rintro rfl; exact h hi
  simp_rw [h1, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ho : Odd (wt a)
  · have : ∑ s : Fin n, (if s ∉ nz a ∧ Odd (wt a) then pw ψ a else 0)
        = ((Finset.univ.filter fun s : Fin n => s ∉ nz a).card : ℝ) * pw ψ a := by
      simp only [ho, and_true]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [this]
    have hc : (Finset.univ.filter fun s : Fin n => s ∉ nz a).card = n - wt a := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
      simp [← card_nz]
    have hle : wt a ≤ n := wt_le a
    rw [hc, Nat.cast_sub hle]
    simp [ho]
  · simp [ho]

/-- **`lem:odd-sector`, last formula.**  `O(ψ) = Σ_{j odd} (n-j)/(n 2^{n-1}) A_j` (`n ≥ 1`). -/
theorem Omean_eq (hn : 1 ≤ n) (ψ : Ψ n) :
    Omean ψ = ∑ j ∈ Finset.range (n + 1),
      (if Odd j then ((n : ℝ) - j) / ((n : ℝ) * 2 ^ (n - 1)) else 0) * A ψ j := by
  unfold Omean oddPur
  have hc : ∀ s : Fin n, (Finset.univ.erase s).card = n - 1 := by
    intro s
    rw [Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ, Fintype.card_fin]
  simp_rw [hc]
  rw [← Finset.sum_div, sum_odd_wsupp, ← sum_A_eq ψ (fun j => if Odd j then ((n : ℝ) - j) else 0)]
  rw [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  by_cases hj : Odd j
  · simp only [hj, ite_true]; field_simp
  · simp [hj]

/-- `π_r(ψ) = (1 / C(n,r)) Σ_{|S| = r} tr ρ_S²`: the mean purity of the `r`-qubit marginals. -/
noncomputable def purMean (ψ : Ψ n) (r : ℕ) : ℝ := Pur ψ r / (Nat.choose n r : ℝ)

/-- **`a_r` in Pauli coordinates.**  For `r ≤ n`,
`Pur ψ r / C(n,r) = Σ_j (1/2)^r C(r,j) (A_j / C(n,j))` (i.e. `a_r = 2^{-r} Σ_j C(r,j) B_j`,
`B_j = A_j / C(n,j)`; first formula of `lem:odd-sector`'s corollary for `a_s`). -/
theorem PurAvg_eq (ψ : Ψ n) {r : ℕ} (hr : r ≤ n) :
    purMean ψ r =
      ∑ j ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ r * (Nat.choose r j : ℝ) * (A ψ j / (Nat.choose n j : ℝ)) := by
  unfold purMean
  have hCr : (Nat.choose n r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hr).ne'
  have h := Pur_eq ψ r
  have h2 : Pur ψ r = (1 / 2 : ℝ) ^ r * ∑ j ∈ Finset.range (n + 1),
      (if j ≤ r then (Nat.choose (n - j) (r - j) : ℝ) else 0) * A ψ j := by
    rw [← h, ← mul_assoc, ← mul_pow]; norm_num
  rw [h2, mul_div_assoc, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hCj : (Nat.choose n j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hjn).ne'
  by_cases hjr : j ≤ r
  · have key : (Nat.choose n r : ℝ) * (Nat.choose r j : ℝ) = (Nat.choose n j : ℝ) * (Nat.choose (n - j) (r - j) : ℝ) := by
      exact_mod_cast Nat.choose_mul (n := n) hjr
    simp only [hjr, ite_true]
    field_simp
    linear_combination (-(A ψ j)) * key
  · have : Nat.choose r j = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [hjr, this]

end FormalResearch.FourQubitEntropy.SpinFlip
