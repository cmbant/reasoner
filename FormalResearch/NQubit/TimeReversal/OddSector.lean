module

public import FormalResearch.NQubit.Reduced.Purity

/-!
# The T-odd purity of single-qubit complements, in Pauli coordinates

* `oddPur ψ S = 2^{-|S|} Σ_{supp P ⊆ S, wt P odd} ⟨P⟩²` is the Pauli-sector form of `½(tr ρ_S² - R_{ρ_S})`; it is
  taken as the definition here, and the identification with `½(tr ρ_S² - tr(ρ_S ρ̃_S))` for the explicit
  spin-flip `ρ̃_S` is `oddPur_eq_half_sub_Rspin` in `TimeReversal/OddOverlap.lean`.
* `Omean ψ = (1/n) Σ_s oddPur ψ ([n] ∖ {s})`: the mean T-odd purity of the single-qubit complements.
* `Omean_eq`: `O = Σ_{j odd} (n-j)/(n 2^{n-1}) A_j`, for every `n ≥ 1`.
* `meanPurity`, `meanPurity_eq_sum_weightEnum`: the mean `a_r = cutPuritySum ψ r / C(n,r)` of the `r`-qubit cut
  purities and `a_r = 2^{-r} Σ_j C(r,j) A_j / C(n,j)`.
-/

@[expose] public section


open scoped ComplexConjugate BigOperators
open FormalResearch.NQubit.Pauli
open FormalResearch.NQubit.Reduced

namespace FormalResearch.NQubit.TimeReversal

variable {n : ℕ}

/-- `2^{-|S|} Σ_{supp P ⊆ S, pauliWeight P odd} ⟨P⟩²` (equals `½(tr ρ_S² - R_{ρ_S})`, see `oddPur_eq_half_sub_Rspin`). -/
noncomputable def oddPur (ψ : Ψ n) (S : Finset (Fin n)) : ℝ :=
  (∑ a ∈ (wsupp S).filter (fun a => Odd (pauliWeight a)), pauliSq ψ a) / 2 ^ S.card

/-- `O(ψ) = (1/n) Σ_s oddPur ψ ([n] ∖ {s})`: mean T-odd purity of the single-qubit complements. -/
noncomputable def Omean (ψ : Ψ n) : ℝ :=
  (1 / (n : ℝ)) * ∑ s : Fin n, oddPur ψ (Finset.univ.erase s)

theorem sum_odd_wsupp (ψ : Ψ n) :
    ∑ s : Fin n, ∑ a ∈ (wsupp (Finset.univ.erase s)).filter (fun a => Odd (pauliWeight a)), pauliSq ψ a
      = ∑ a : Fin n → Fin 4, (if Odd (pauliWeight a) then ((n : ℝ) - pauliWeight a) else 0) * pauliSq ψ a := by
  have h1 : ∀ s : Fin n, ((wsupp (Finset.univ.erase s)).filter (fun a => Odd (pauliWeight a)))
      = Finset.univ.filter (fun a : Fin n → Fin 4 => s ∉ pauliSupport a ∧ Odd (pauliWeight a)) := by
    intro s; ext a
    simp only [Finset.mem_filter, mem_wsupp_iff_pauliSupport, Finset.mem_univ, true_and]
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
  by_cases ho : Odd (pauliWeight a)
  · have : ∑ s : Fin n, (if s ∉ pauliSupport a ∧ Odd (pauliWeight a) then pauliSq ψ a else 0)
        = ((Finset.univ.filter fun s : Fin n => s ∉ pauliSupport a).card : ℝ) * pauliSq ψ a := by
      simp only [ho, and_true]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [this]
    have hc : (Finset.univ.filter fun s : Fin n => s ∉ pauliSupport a).card = n - pauliWeight a := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
      simp [← card_pauliSupport]
    have hle : pauliWeight a ≤ n := pauliWeight_le a
    rw [hc, Nat.cast_sub hle]
    simp [ho]
  · simp [ho]

/-- `O(ψ) = Σ_{j odd} (n-j)/(n 2^{n-1}) A_j` (`n ≥ 1`). -/
theorem Omean_eq (hn : 1 ≤ n) (ψ : Ψ n) :
    Omean ψ = ∑ j ∈ Finset.range (n + 1),
      (if Odd j then ((n : ℝ) - j) / ((n : ℝ) * 2 ^ (n - 1)) else 0) * weightEnum ψ j := by
  unfold Omean oddPur
  have hc : ∀ s : Fin n, (Finset.univ.erase s).card = n - 1 := by
    intro s
    rw [Finset.card_erase_of_mem (Finset.mem_univ s), Finset.card_univ, Fintype.card_fin]
  simp_rw [hc]
  rw [← Finset.sum_div, sum_odd_wsupp, ← sum_weightEnum_eq ψ (fun j => if Odd j then ((n : ℝ) - j) else 0)]
  rw [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  by_cases hj : Odd j
  · simp only [hj, ite_true]; field_simp
  · simp [hj]

/-- `π_r(ψ) = (1 / C(n,r)) Σ_{|S| = r} tr ρ_S²`: the mean purity of the `r`-qubit marginals. -/
noncomputable def meanPurity (ψ : Ψ n) (r : ℕ) : ℝ := cutPuritySum ψ r / (Nat.choose n r : ℝ)

/-- **`a_r` in Pauli coordinates.**  For `r ≤ n`,
`cutPuritySum ψ r / C(n,r) = Σ_j (1/2)^r C(r,j) (A_j / C(n,j))` (i.e. `a_r = 2^{-r} Σ_j C(r,j) B_j`,
`B_j = A_j / C(n,j)`). -/
theorem meanPurity_eq_sum_weightEnum (ψ : Ψ n) {r : ℕ} (hr : r ≤ n) :
    meanPurity ψ r =
      ∑ j ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ r * (Nat.choose r j : ℝ) * (weightEnum ψ j / (Nat.choose n j : ℝ)) := by
  unfold meanPurity
  have hCr : (Nat.choose n r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hr).ne'
  have h := cutPuritySum_eq ψ r
  have h2 : cutPuritySum ψ r = (1 / 2 : ℝ) ^ r * ∑ j ∈ Finset.range (n + 1),
      (if j ≤ r then (Nat.choose (n - j) (r - j) : ℝ) else 0) * weightEnum ψ j := by
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
    linear_combination (-(weightEnum ψ j)) * key
  · have : Nat.choose r j = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [hjr, this]

end FormalResearch.NQubit.TimeReversal
