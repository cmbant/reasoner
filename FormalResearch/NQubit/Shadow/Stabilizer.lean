module

public import FormalResearch.NQubit.Shadow.Basic

/-!
# Weight and shadow enumerators of stabilizer states are non-negative integers

A pure `n`-qubit state is a *stabilizer state* when there is a group `G` of `2^n` pairwise commuting Pauli
words, closed under multiplication (up to phase), each of which has `⟨ψ|P|ψ⟩² = 1`
(`IsStabilizerState`; this is the usual stabilizer-group description, the signs of the eigenvalues
being irrelevant here).

Proved here, for every stabilizer state:

* `pauliSq_eq_ite`: `⟨P⟩² = 1` on `G` and `0` off `G` (Pauli completeness `Σ_P ⟨P⟩² = 2^n`).
* `weightEnum_eq_card`: `A_j = #{P ∈ G : wt P = j}`, a natural number.
* `shadowCoeff_eq_card`: the shadow coefficient `S_i` of Rains' transform equals the number of type vectors `t`
  with `i` non-flip positions on which the sign `∏ᵢ w_{tᵢ}(Pᵢ)` is `1` for every `P ∈ G`; in particular
  `S_i ∈ ℕ` (`shadowCoeff_nat`).  The reason is that, for commuting `P, Q`, the sign of a type vector
  is multiplicative, `φ_t(PQ) = φ_t(P) φ_t(Q)` (`wloc_pmul`, the defect is `-1` exactly at positions where the
  letters anticommute), so `P ↦ φ_t(P)` is a character of `G` and its average over `G` is `0` or `1`.

This is the integrality step of the paper's proof of `prop:stab7`
(`QI/multiqubit_entanglement/seven_qubit_entanglement/icosahedral_state.tex`), for the shadow
enumerator as Rains' transform of `A_j`, which is how `shadowCoeff` is defined.
-/

@[expose] public section


open scoped ComplexConjugate BigOperators
open Polynomial
open FormalResearch.NQubit.Pauli

namespace FormalResearch.NQubit.Shadow

/-! ### Pauli letters up to phase -/

/-- Product of Pauli letters `0 = I, 1, 2, 3 = X, Y, Z` up to phase (addition in `𝔽₂²`). -/
def pmul (a b : Fin 4) : Fin 4 := ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] a b

/-- Two Pauli letters anticommute iff both are non-identity and distinct. -/
def acomm (a b : Fin 4) : Prop := a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b

instance (a b : Fin 4) : Decidable (acomm a b) := by unfold acomm; infer_instance

theorem pmul_comm (a b : Fin 4) : pmul a b = pmul b a := by revert a b; decide

theorem pmul_self (a : Fin 4) : pmul a a = 0 := by revert a; decide

theorem pmul_pmul_self (a b : Fin 4) : pmul (pmul a b) b = a := by revert a b; decide

/-- Letterwise product of Pauli words. -/
def pmulW {n : ℕ} (a b : Fin n → Fin 4) : Fin n → Fin 4 := fun i => pmul (a i) (b i)

/-- Number of positions at which two Pauli words anticommute. -/
def nanti {n : ℕ} (a b : Fin n → Fin 4) : ℕ := (Finset.univ.filter fun i => acomm (a i) (b i)).card

theorem pmulW_pmulW_self {n : ℕ} (a b : Fin n → Fin 4) : pmulW (pmulW a b) b = a := by
  funext i; exact pmul_pmul_self _ _

/-- The sign `∏ᵢ w_{tᵢ}(Pᵢ)` of a type vector `t` on a Pauli word `a`. -/
def phi {n : ℕ} (t a : Fin n → Fin 4) : ℝ := ∏ i, wloc (t i) (a i)

theorem wloc_pmul (τ a b : Fin 4) :
    wloc τ (pmul a b) * wloc τ a * wloc τ b = if acomm a b then -1 else 1 := by
  fin_cases τ <;> fin_cases a <;> fin_cases b <;> simp [wloc, pmul, acomm]

/-- The sign of a type vector is multiplicative up to `(-1)^{#anticommuting positions}`. -/
theorem phi_pmulW {n : ℕ} (t a b : Fin n → Fin 4) :
    phi t (pmulW a b) = phi t a * phi t b * (-1) ^ nanti a b := by
  unfold phi pmulW nanti
  have h : ∀ i, wloc (t i) (pmul (a i) (b i)) = wloc (t i) (a i) * wloc (t i) (b i) *
      (if acomm (a i) (b i) then -1 else 1) := by
    intro i
    have := wloc_pmul (t i) (a i) (b i)
    have hsq : ∀ τ x : Fin 4, wloc τ x * wloc τ x = 1 := by
      intro τ x; fin_cases τ <;> fin_cases x <;> simp [wloc]
    calc wloc (t i) (pmul (a i) (b i))
        = wloc (t i) (pmul (a i) (b i)) * wloc (t i) (a i) * wloc (t i) (b i) *
            (wloc (t i) (a i) * wloc (t i) (b i)) := by
          have := hsq (t i) (a i); have := hsq (t i) (b i)
          calc _ = wloc (t i) (pmul (a i) (b i)) *
                (wloc (t i) (a i) * wloc (t i) (a i)) * (wloc (t i) (b i) * wloc (t i) (b i)) := by
                simp_all
            _ = _ := by ring
      _ = _ := by rw [this]; ring
  simp_rw [h]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]

theorem phi_sq {n : ℕ} (t a : Fin n → Fin 4) : phi t a * phi t a = 1 := by
  unfold phi
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  generalize t i = τ; generalize a i = x
  fin_cases τ <;> fin_cases x <;> simp [wloc]

/-! ### Stabilizer groups and states -/

/-- A stabilizer group of Pauli words on `n` qubits: `2^n` pairwise commuting words closed under
multiplication up to phase. -/
structure IsStabilizerGroup {n : ℕ} (G : Finset (Fin n → Fin 4)) : Prop where
  card : G.card = 2 ^ n
  mul_mem : ∀ a ∈ G, ∀ b ∈ G, pmulW a b ∈ G
  comm : ∀ a ∈ G, ∀ b ∈ G, Even (nanti a b)

/-- A pure state is a stabilizer state when it is fixed (up to sign) by every Pauli word of a stabilizer
group, that is `⟨P⟩² = 1` on the group. -/
def IsStabilizerState {n : ℕ} (ψ : Ψ n) : Prop :=
  nsq ψ = 1 ∧ ∃ G : Finset (Fin n → Fin 4), IsStabilizerGroup G ∧ ∀ a ∈ G, pauliSq ψ a = 1

section
variable {n : ℕ} {ψ : Ψ n} {G : Finset (Fin n → Fin 4)}

/-- **`⟨P⟩² ∈ {0, 1}`**: it is `1` exactly on the stabilizer group. -/
theorem pauliSq_eq_ite (hn : nsq ψ = 1) (hG : IsStabilizerGroup G) (h1 : ∀ a ∈ G, pauliSq ψ a = 1)
    (a : Fin n → Fin 4) : pauliSq ψ a = if a ∈ G then 1 else 0 := by
  have hsum := sum_pauliSq ψ
  rw [hn] at hsum
  have hG1 : ∑ a ∈ G, pauliSq ψ a = 2 ^ n := by
    rw [Finset.sum_congr rfl h1]; simp [hG.card]
  have hrest : ∑ a ∈ Gᶜ, pauliSq ψ a = 0 := by
    have := Finset.sum_add_sum_compl G (pauliSq ψ)
    rw [hsum, hG1] at this
    linarith
  by_cases ha : a ∈ G
  · simp [ha, h1 a ha]
  · have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => pauliSq_nonneg ψ x)).mp hrest a
      (Finset.mem_compl.mpr ha)
    simp [ha, this]

variable (hp : ∀ a, pauliSq ψ a = if a ∈ G then 1 else 0)
include hp

/-- `A_j = #{P ∈ G : wt P = j}`. -/
theorem weightEnum_eq_card (j : ℕ) :
    weightEnum ψ j = ((G.filter fun a => pauliWeight a = j).card : ℝ) := by
  unfold weightEnum
  simp_rw [hp]
  rw [Finset.sum_boole]
  congr 2
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

end

/-! ### The shadow coefficients -/

theorem types_sum {n : ℕ} (a : Fin n → Fin 4) :
    ∑ t : Fin n → Fin 4, (X : ℝ[X]) ^ nzc t * C (phi t a)
      = (1 + 3 * X) ^ (n - pauliWeight a) * (X - 1) ^ pauliWeight a := by
  have h2 : ∀ t : Fin n → Fin 4, (X : ℝ[X]) ^ nzc t * C (phi t a)
      = ∏ i, ((if t i ≠ 0 then (X : ℝ[X]) else 1) * C (wloc (t i) (a i))) := by
    intro t
    rw [Finset.prod_mul_distrib]
    unfold phi
    rw [map_prod]
    have : (∏ i, (if t i ≠ 0 then (X : ℝ[X]) else 1)) = X ^ nzc t := by
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
      rfl
    rw [this]
  simp_rw [h2]
  have h3 : ∑ t : Fin n → Fin 4, ∏ i, ((if t i ≠ 0 then (X : ℝ[X]) else 1) * C (wloc (t i) (a i)))
      = ∏ i, ∑ τ : Fin 4, (if τ ≠ 0 then (X : ℝ[X]) else 1) * C (wloc τ (a i)) := by
    rw [Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin 4)))
      (fun i τ => (if τ ≠ 0 then (X : ℝ[X]) else 1) * C (wloc τ (a i))), Fintype.piFinset_univ]
  rw [h3]
  simp_rw [local_factor]
  exact prod_local a

section
variable {n : ℕ} {ψ : Ψ n} {G : Finset (Fin n → Fin 4)}

/-- The average of a character of the stabilizer group over the group is `0` or `1`. -/
theorem sum_phi_group (hG : IsStabilizerGroup G) (t : Fin n → Fin 4) :
    ∑ a ∈ G, phi t a = if ∀ a ∈ G, phi t a = 1 then (2 : ℝ) ^ n else 0 := by
  split_ifs with h
  · rw [Finset.sum_congr rfl h]; simp [hG.card]
  · 
    push Not at h
    obtain ⟨b, hb, hb1⟩ := h
    have hbm : phi t b = -1 := by
      have := phi_sq t b
      have h' : (phi t b - 1) * (phi t b + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp h' with h0 | h0
      · exact absurd (by linarith) hb1
      · linarith
    have hs : ∑ a ∈ G, phi t a = ∑ a ∈ G, phi t (pmulW a b) := by
      refine Finset.sum_nbij' (fun a => pmulW a b) (fun a => pmulW a b) ?_ ?_ ?_ ?_ ?_
      · intro a ha; exact hG.mul_mem a ha b hb
      · intro a ha; exact hG.mul_mem a ha b hb
      · intro a _; exact pmulW_pmulW_self a b
      · intro a _; exact pmulW_pmulW_self a b
      · intro a _; rw [pmulW_pmulW_self]
    have h2 : ∑ a ∈ G, phi t (pmulW a b) = ∑ a ∈ G, -phi t a := by
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [phi_pmulW, hbm, (hG.comm a ha b hb).neg_one_pow]; ring
    rw [Finset.sum_neg_distrib] at h2
    linarith

variable (hp : ∀ a, pauliSq ψ a = if a ∈ G then 1 else 0)
include hp

/-- `S(1,y) = 2^{-n} Σ_{P ∈ G} Σ_t y^{#nonflip t} φ_t(P)`. -/
theorem shadowPoly_stab :
    shadowPoly ψ = C ((1 / 2 : ℝ) ^ n) *
      ∑ a ∈ G, ∑ t : Fin n → Fin 4, (X : ℝ[X]) ^ nzc t * C (phi t a) := by
  rw [shadowPoly_eq, ← sum_weightEnum_poly ψ (fun j => (1 + 3 * X) ^ (n - j) * (X - 1) ^ j)]
  congr 1
  have hc : ∀ x : Fin n → Fin 4, C (pauliSq ψ x) * ((1 + 3 * X) ^ (n - pauliWeight x) *
      (X - 1) ^ pauliWeight x) = if x ∈ G then (1 + 3 * X) ^ (n - pauliWeight x) *
        (X - 1) ^ pauliWeight x else (0 : ℝ[X]) := by
    intro x; rw [hp x]; split_ifs <;> simp
  simp_rw [hc]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  exact Finset.sum_congr rfl fun a _ => (types_sum a).symm

/-- **Shadow coefficients of a stabilizer state count type vectors**: `S_i` is the number of type vectors with
`i` non-flip positions whose sign is `1` on the whole stabilizer group. -/
theorem shadowCoeff_eq_card (hG : IsStabilizerGroup G) (i : ℕ) :
    shadowCoeff ψ i = ((Finset.univ.filter fun t : Fin n → Fin 4 =>
      nzc t = i ∧ ∀ a ∈ G, phi t a = 1).card : ℝ) := by
  unfold shadowCoeff
  rw [shadowPoly_stab hp, coeff_C_mul, finsetSum_coeff]
  simp_rw [finsetSum_coeff]
  rw [Finset.sum_comm]
  have hco : ∀ (a : Fin n → Fin 4) (t : Fin n → Fin 4),
      ((X : ℝ[X]) ^ nzc t * C (phi t a)).coeff i = if nzc t = i then phi t a else 0 := by
    intro a t
    rw [mul_comm, coeff_C_mul_X_pow]
    simp only [eq_comm]
  simp_rw [hco]
  have : ∀ t : Fin n → Fin 4, ∑ a ∈ G, (if nzc t = i then phi t a else 0)
      = if nzc t = i then (if ∀ a ∈ G, phi t a = 1 then (2 : ℝ) ^ n else 0) else 0 := by
    intro t
    by_cases h : nzc t = i
    · simp only [h, ↓reduceIte, sum_phi_group hG t]
    · simp [h]
  simp_rw [this]
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h1 : nzc t = i <;> by_cases h2 : ∀ a ∈ G, phi t a = 1 <;> simp [h1, h2]

/-- **Integrality of the shadow coefficients.** -/
theorem shadowCoeff_nat (hG : IsStabilizerGroup G) (i : ℕ) : ∃ m : ℕ, shadowCoeff ψ i = m :=
  ⟨_, shadowCoeff_eq_card hp hG i⟩

end

/-! ### Stabilizer states -/

/-- The Pauli weight enumerator of a stabilizer state has non-negative integer coefficients. -/
theorem IsStabilizerState.weightEnum_nat {n : ℕ} {ψ : Ψ n} (h : IsStabilizerState ψ) (j : ℕ) :
    ∃ m : ℕ, weightEnum ψ j = m := by
  obtain ⟨hn, G, hG, h1⟩ := h
  exact ⟨_, weightEnum_eq_card (pauliSq_eq_ite hn hG h1) j⟩

/-- The shadow enumerator of a stabilizer state has non-negative integer coefficients. -/
theorem IsStabilizerState.shadowCoeff_nat {n : ℕ} {ψ : Ψ n} (h : IsStabilizerState ψ) (i : ℕ) :
    ∃ m : ℕ, shadowCoeff ψ i = m := by
  obtain ⟨hn, G, hG, h1⟩ := h
  exact FormalResearch.NQubit.Shadow.shadowCoeff_nat (pauliSq_eq_ite hn hG h1) hG i

/-- info: 'FormalResearch.NQubit.Shadow.IsStabilizerState.shadowCoeff_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsStabilizerState.shadowCoeff_nat

/-- info: 'FormalResearch.NQubit.Shadow.IsStabilizerState.weightEnum_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsStabilizerState.weightEnum_nat

end FormalResearch.NQubit.Shadow
