import FormalResearch.FourQubitEntropy.SevenQubitSpectralPairCore

/-!
# The cross-cut inequality `e_S + 16 v(ρ_S) ≤ R` for a pure seven-qubit state

Second half of `prop:seven-spinflip-spectral-pair`
(`ResearchNotes/QI/seven_qubit_entanglement/seven_qubit_entropy_compatibility.tex`).

For a unit vector `ψ` of seven qubits and a three-site mask `m`, `rhoS m ψ` is the reduced matrix
`ρ_S = Tr_{Sᶜ}|ψ⟩⟨ψ|` (`redEntry` of `SevenQubitConseqPurity`).  The module proves

* `rhoS_e3`:  `e(ρ_S) = excess m ψ` (`8 tr ρ_S² - 1`);
* `rhoS_b3`:  `b(ρ_S) =` the sum of the squared weight-two Pauli expectations supported in `S`;
* `four_b_le`: `R - e_S ≥ 4 b(ρ_S)` (every pair of `S` lies in four other three-subsets, and every
  summand of every `e_T` is nonnegative), with `R = excessSum ψ`;
* `cross_cut`: `e_S + 16 v(ρ_S) ≤ R`, by `b ≥ 4 v` (`b3_ge_four_v3`).

Only pure global states on seven qubits are treated; the closing sentence of the proposition ("also
for mixed global states") is not formalized.
-/

open scoped ComplexConjugate Matrix
open Finset
open FormalResearch.FourQubitEntropy.SevenQubitConseq
open FormalResearch.FourQubitEntropy.SevenQubitIco

namespace FormalResearch.FourQubitEntropy.SevenQubitSpectralPair

/-- The reduced three-qubit matrix `ρ_S` of a seven-qubit pure state across the cut of the mask `m`. -/
noncomputable def rhoS (m : Fin 7 → Bool) (ψ : BitString → ℂ) : Mat3 :=
  Matrix.of (redEntry (maskCut 3 4 m) ψ)

theorem rhoS_apply (m : Fin 7 → Bool) (ψ : BitString → ℂ) (a b : Cfg3) :
    rhoS m ψ a b = redEntry (maskCut 3 4 m) ψ a b := rfl

theorem rhoS_hermitian (m : Fin 7 → Bool) (ψ : BitString → ℂ) : (rhoS m ψ).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, rhoS_apply, redEntry, Matrix.star_apply]
  simp [map_sum, mul_comm]

theorem rhoS_trace (m : Fin 7 → Bool) (hm : weight m = 3) (ψ : BitString → ℂ) (hψ : UnitVec ψ) :
    (rhoS m ψ).trace = 1 := by
  have hf := encode_bijective _ (maskCut_bijective_three m hm)
  have h1 : ∑ z, Complex.normSq (ψ z) =
      ∑ p : Cfg3 × (Fin 4 → Bool), Complex.normSq (ψ (encode (maskCut 3 4 m) p.1 p.2)) :=
    (hf.sum_comp (fun z => Complex.normSq (ψ z))).symm
  rw [Fintype.sum_prod_type] at h1
  have h2 : (rhoS m ψ).trace = ((∑ a : Cfg3, ∑ r : Fin 4 → Bool,
      Complex.normSq (ψ (encode (maskCut 3 4 m) a r)) : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, rhoS_apply, redEntry, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun r _ => ?_
    rw [Complex.mul_conj]
  rw [h2, ← h1, hψ]
  simp

theorem rhoS_e3 (m : Fin 7 → Bool) (ψ : BitString → ℂ) : e3 (rhoS m ψ) = excess m ψ := by
  unfold e3 excess cutPurity
  rw [trace_sq_eq _ (rhoS_hermitian m ψ), Complex.ofReal_re]
  rfl

theorem pwt_extPauli (c : Cut 3 4) (hc : Function.Bijective c) (ν : Fin 3 → Fin 4) :
    pwt (extPauli c ν) = wt3 ν := by
  unfold pwt wt3
  rw [Finset.card_filter, Finset.card_filter]
  have h := Fintype.sum_bijective c hc (fun i => if extPauli c ν i ≠ 0 then 1 else 0)
    (fun s => if Sum.elim ν (fun _ => (0 : Fin 4)) s ≠ 0 then 1 else 0) (fun i => rfl)
  rw [h, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, ne_eq, not_true_eq_false, if_false, Finset.sum_const_zero,
    add_zero]
  exact Finset.sum_congr rfl fun x _ => by by_cases hx : ν x = 0 <;> simp [hx]

/-- `b(ρ_S)` is the sum of the squared weight-two Pauli expectations supported in `S`. -/
theorem rhoS_b3 (m : Fin 7 → Bool) (hm : weight m = 3) (ψ : BitString → ℂ) :
    b3 (rhoS m ψ) = ∑ μ ∈ suppSet m, if pwt μ = 2 then psq ψ μ else 0 := by
  have hc := maskCut_bijective_three m hm
  rw [← sum_ext_mask m hm (fun μ => if pwt μ = 2 then psq ψ μ else 0)]
  unfold b3
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [pwt_extPauli _ hc, psq, pexp_ext _ hc]
  rfl

/-- `R - e_S ≥ 4 b(ρ_S)`. -/
theorem four_b_le (m : Fin 7 → Bool) (hm : weight m = 3) (ψ : BitString → ℂ) (hψ : UnitVec ψ) :
    4 * b3 (rhoS m ψ) ≤ excessSum ψ - excess m ψ := by
  rw [rhoS_b3 m hm]
  have hI1 := purity_mask m hm ψ
  have hS : ∑ m' ∈ tripleMasks, ∑ μ ∈ suppSet m', psq ψ μ =
      ∑ μ : Fin 7 → Fin 4, (cntN (pwt μ) : ℝ) * psq ψ μ := sum_cuts_pauli ψ
  have hS' : ∑ m' ∈ tripleMasks, ∑ μ ∈ suppSet m', psq ψ μ =
      8 * ∑ m' ∈ tripleMasks, cutPurity (maskCut 3 4 m') ψ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m' hm' => purity_mask m' (Finset.mem_filter.1 hm').2 ψ
  set κ : (Fin 7 → Fin 4) → ℝ := fun μ =>
    (cntN (pwt μ) : ℝ) - (if μ ∈ suppSet m then 1 + 4 * (if pwt μ = 2 then 1 else 0) else 0) with hκ
  have hκnn : ∀ μ, 0 ≤ κ μ := by
    intro μ
    simp only [hκ]
    by_cases hμ : μ ∈ suppSet m
    · have h3 := pwt_le_of_mem_suppSet m hm hμ
      rw [if_pos hμ]
      generalize pwt μ = j at h3
      interval_cases j <;> simp [cntN] <;> norm_num
    · rw [if_neg hμ]; simp
  have hK : κ 0 * psq ψ 0 ≤ ∑ μ, κ μ * psq ψ μ :=
    Finset.single_le_sum (f := fun μ => κ μ * psq ψ μ)
      (fun μ _ => mul_nonneg (hκnn μ) (Complex.normSq_nonneg _)) (Finset.mem_univ _)
  have hκ0 : κ 0 = 34 := by
    simp only [hκ]
    rw [if_pos (zero_mem_suppSet m), pwt_zero]
    simp [cntN]
    norm_num
  have hexp : ∑ μ, κ μ * psq ψ μ =
      ∑ μ : Fin 7 → Fin 4, (cntN (pwt μ) : ℝ) * psq ψ μ -
        (∑ μ ∈ suppSet m, psq ψ μ + 4 * ∑ μ ∈ suppSet m, if pwt μ = 2 then psq ψ μ else 0) := by
    have : ∀ μ, κ μ * psq ψ μ = (cntN (pwt μ) : ℝ) * psq ψ μ -
        (if μ ∈ suppSet m then psq ψ μ + 4 * (if pwt μ = 2 then psq ψ μ else 0) else 0) := by
      intro μ
      simp only [hκ]
      split_ifs <;> ring
    simp only [this, Finset.sum_sub_distrib]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hκ0, psq_zero ψ hψ, hexp, ← hS, hS', hI1] at hK
  have hR := excessSum_eq ψ
  unfold meanPurity3 at hR
  unfold excess
  linarith

/-- **`prop:seven-spinflip-spectral-pair`, cross-cut inequality** (pure seven-qubit state).
For every three-site cut `S` (mask `m`), `e_S + 16 v(ρ_S) ≤ R = ∑_{|T|=3} e_T`. -/
theorem cross_cut (m : Fin 7 → Bool) (hm : weight m = 3) (ψ : BitString → ℂ) (hψ : UnitVec ψ) :
    excess m ψ + 16 * v3 (rhoS m ψ) (rhoS_hermitian m ψ) ≤ excessSum ψ := by
  have h1 := b3_ge_four_v3 (rhoS m ψ) (rhoS_hermitian m ψ) (rhoS_trace m hm ψ hψ)
  have h2 := four_b_le m hm ψ hψ
  linarith

end FormalResearch.FourQubitEntropy.SevenQubitSpectralPair
