import FormalResearch.FourQubitEntropy.SevenQubitSpectralPairCross

/-!
# The cross-cut inequality `e_S + 16 v(ρ_S) ≤ R` for mixed seven-qubit states

Last sentence of `prop:seven-spinflip-spectral-pair`
(`ResearchNotes/QI/seven_qubit_entanglement/seven_qubit_entropy_compatibility.tex`): the joint spectral
compatibility inequality `e_S + 16 v(ρ_S) ≤ R = ∑_{|T|=3} e_T` "also holds for mixed global states".
`SevenQubitSpectralPairCross` proves it for a pure global state `ψ`; here the global state is any
seven-qubit matrix `ρ : Mat7` (`ρ a b`, ket `a`, bra `b`, the convention of `redEntry`) that is
Hermitian of trace one, in particular any density matrix (`cross_cut_mixed_density`).
Claim class: **proved** (no hypothesis); positivity of `ρ` is not needed.

The proof is the pure one with `ψ ψ†` replaced by `ρ`:
* `pexpM_ext`, `purity_sumM`, `purity_maskM`: Pauli expansion of the reduced purity,
  `∑_{μ supported in S} ⟨P_μ⟩² = 8 tr ρ_S²`;
* `rhoSM_b3`: `b(ρ_S)` is the sum of the squared weight-two Pauli expectations supported in `S`;
* `four_b_leM`: `R - e_S ≥ 4 b(ρ_S)`, since the coefficient `κ(μ) = #{T ⊇ supp μ} - [μ ⊂ S](1 + 4[wt μ = 2])`
  of `⟨P_μ⟩²` is nonnegative (only `⟨P_0⟩² = (tr ρ)² = 1` is used about the identity string);
* `cross_cut_mixed`: combine with `b ≥ 4 v` (`b3_ge_four_v3`, the three-qubit statement, which only
  needs `ρ_S` Hermitian of trace one).

`rhoSM_pure`, `cross_cut_mixed_pure` check that for `ρ = |ψ⟩⟨ψ|` this specialises to `cross_cut`.
-/

open scoped ComplexConjugate Matrix ComplexOrder
open Finset
open FormalResearch.FourQubitEntropy.SevenQubitConseq
open FormalResearch.FourQubitEntropy.SevenQubitIco

namespace FormalResearch.FourQubitEntropy.SevenQubitSpectralPair

/-- Operators on seven qubits (`ρ a b`: ket `a`, bra `b`). -/
abbrev Mat7 := Matrix BitString BitString ℂ

/-- Reduced matrix entry of a seven-qubit operator across a cut (partial trace over the complement). -/
def redEntryM {k l : ℕ} (c : Cut k l) (ρ : Mat7) (a b : Fin k → Bool) : ℂ :=
  ∑ r : Fin l → Bool, ρ (encode c a r) (encode c b r)

/-- Purity `tr ρ_S²` of the reduced matrix across a cut. -/
def cutPurityM {k l : ℕ} (c : Cut k l) (ρ : Mat7) : ℝ :=
  ∑ a, ∑ b, Complex.normSq (redEntryM c ρ a b)

/-- Squared Pauli expectation `|tr(ρ P_μ)|²`. -/
def psqM (ρ : Mat7) (μ : Fin 7 → Fin 4) : ℝ := Complex.normSq (trP (fun a b => ρ a b) μ)

/-- The reduced three-qubit matrix `ρ_S` of a mask `m`. -/
noncomputable def rhoSM (m : Fin 7 → Bool) (ρ : Mat7) : Mat3 :=
  Matrix.of (redEntryM (maskCut 3 4 m) ρ)

/-- The Pauli excess `e_S = 8 tr ρ_S² - 1`. -/
def excessM (m : Fin 7 → Bool) (ρ : Mat7) : ℝ := 8 * cutPurityM (maskCut 3 4 m) ρ - 1

/-- `R = ∑_{|S|=3} e_S`. -/
noncomputable def excessSumM (ρ : Mat7) : ℝ := ∑ m ∈ tripleMasks, excessM m ρ

/-! ### Specialisation to pure states -/

theorem redEntryM_pure {k l : ℕ} (c : Cut k l) (ψ : BitString → ℂ) (a b : Fin k → Bool) :
    redEntryM c (Matrix.vecMulVec ψ (star ψ)) a b = redEntry c ψ a b := by
  simp [redEntryM, redEntry, Matrix.vecMulVec_apply]

theorem rhoSM_pure (m : Fin 7 → Bool) (ψ : BitString → ℂ) :
    rhoSM m (Matrix.vecMulVec ψ (star ψ)) = rhoS m ψ := by
  ext a b
  simp [rhoSM, rhoS, redEntryM_pure]

theorem excessM_pure (m : Fin 7 → Bool) (ψ : BitString → ℂ) :
    excessM m (Matrix.vecMulVec ψ (star ψ)) = excess m ψ := by
  simp [excessM, excess, cutPurityM, cutPurity, redEntryM_pure]

theorem vecMulVec_hermitian (ψ : BitString → ℂ) : (Matrix.vecMulVec ψ (star ψ)).IsHermitian := by
  ext a b
  simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]

/-! ### Pauli expansion of the reduced purity -/

theorem pexpM_ext {k l : ℕ} (c : Cut k l) (hc : Function.Bijective c) (ρ : Mat7)
    (ν : Fin k → Fin 4) :
    trP (fun a b => ρ a b) (extPauli c ν) = trP (redEntryM c ρ) ν := by
  have hf := encode_bijective c hc
  set G : BitString → BitString → ℂ := fun z w =>
    ρ z w * ∏ i, pauli (extPauli c ν i) (w i) (z i) with hG
  have e1 : ∑ z, ∑ w, G z w =
      ∑ p : (Fin k → Bool) × (Fin l → Bool), ∑ q : (Fin k → Bool) × (Fin l → Bool),
        G (encode c p.1 p.2) (encode c q.1 q.2) := by
    rw [← hf.sum_comp]
    exact Finset.sum_congr rfl fun p _ => (hf.sum_comp (G (encode c p.1 p.2))).symm
  show ∑ z, ∑ w, G z w = _
  rw [e1]
  simp only [Fintype.sum_prod_type, hG, prod_ext_pauli c hc]
  simp only [mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  unfold trP redEntryM
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

theorem purity_sumM {k l : ℕ} (c : Cut k l) (hc : Function.Bijective c) (ρ : Mat7) :
    ∑ ν : Fin k → Fin 4, psqM ρ (extPauli c ν) = 2 ^ k * cutPurityM c ρ := by
  simp only [psqM, pexpM_ext c hc, sum_sq_trP, Fintype.card_fin]
  rfl

theorem purity_maskM (m : Fin 7 → Bool) (hm : weight m = 3) (ρ : Mat7) :
    ∑ μ ∈ suppSet m, psqM ρ μ = 8 * cutPurityM (maskCut 3 4 m) ρ := by
  rw [← sum_ext_mask m hm, purity_sumM _ (maskCut_bijective_three m hm)]
  norm_num

/-- Summing the cut identity over the 35 cuts, for any weight function on Pauli strings. -/
theorem sum_cuts_paulM (F : (Fin 7 → Fin 4) → ℝ) :
    ∑ m ∈ tripleMasks, ∑ μ ∈ suppSet m, F μ = ∑ μ : Fin 7 → Fin 4, (cntN (pwt μ) : ℝ) * F μ := by
  have h1 : ∀ m : Fin 7 → Bool, ∑ μ ∈ suppSet m, F μ =
      ∑ μ : Fin 7 → Fin 4, if (∀ i, μ i ≠ 0 → m i = true) then F μ else 0 := by
    intro m
    unfold suppSet
    rw [Finset.sum_filter]
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, pwt_eq_weight]
  have := mask_count (fun i => decide (μ i ≠ 0))
  simp only [decide_eq_true_eq] at this
  rw [this, mul_comm]

theorem psqM_zero (ρ : Mat7) (htr : ρ.trace = 1) : psqM ρ 0 = 1 := by
  have h : trP (fun a b => ρ a b) 0 = ρ.trace := by
    unfold trP
    simp only [Pi.zero_apply, prod_pauli_zero, mul_ite, mul_one, mul_zero]
    simp [Matrix.trace, eq_comm]
  unfold psqM
  rw [h, htr]
  simp

/-! ### The reduced three-qubit matrix -/

theorem rhoSM_hermitian (m : Fin 7 → Bool) (ρ : Mat7) (hρ : ρ.IsHermitian) :
    (rhoSM m ρ).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, rhoSM, Matrix.of_apply, redEntryM, star_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have := hρ.apply (encode (maskCut 3 4 m) a r) (encode (maskCut 3 4 m) b r)
  simpa using this

theorem rhoSM_trace (m : Fin 7 → Bool) (hm : weight m = 3) (ρ : Mat7) (htr : ρ.trace = 1) :
    (rhoSM m ρ).trace = 1 := by
  have hf := encode_bijective _ (maskCut_bijective_three m hm)
  have h1 : ∑ z, ρ z z = ∑ p : Cfg3 × (Fin 4 → Bool), ρ (encode (maskCut 3 4 m) p.1 p.2)
      (encode (maskCut 3 4 m) p.1 p.2) :=
    (hf.sum_comp (fun z => ρ z z)).symm
  rw [Fintype.sum_prod_type] at h1
  have h2 : (rhoSM m ρ).trace = ∑ a : Cfg3, ∑ r : Fin 4 → Bool,
      ρ (encode (maskCut 3 4 m) a r) (encode (maskCut 3 4 m) a r) := by
    simp [Matrix.trace, rhoSM, redEntryM]
  rw [h2, ← h1]
  exact htr

theorem rhoSM_e3 (m : Fin 7 → Bool) (ρ : Mat7) (hρ : ρ.IsHermitian) :
    e3 (rhoSM m ρ) = excessM m ρ := by
  unfold e3 excessM cutPurityM
  rw [trace_sq_eq _ (rhoSM_hermitian m ρ hρ), Complex.ofReal_re]
  rfl

/-- `b(ρ_S)` is the sum of the squared weight-two Pauli expectations supported in `S`. -/
theorem rhoSM_b3 (m : Fin 7 → Bool) (hm : weight m = 3) (ρ : Mat7) :
    b3 (rhoSM m ρ) = ∑ μ ∈ suppSet m, if pwt μ = 2 then psqM ρ μ else 0 := by
  have hc := maskCut_bijective_three m hm
  rw [← sum_ext_mask m hm (fun μ => if pwt μ = 2 then psqM ρ μ else 0)]
  unfold b3
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [pwt_extPauli _ hc, psqM, pexpM_ext _ hc]
  rfl

/-! ### The cross-cut inequality -/

/-- `R - e_S ≥ 4 b(ρ_S)` for any trace-one seven-qubit operator. -/
theorem four_b_leM (m : Fin 7 → Bool) (hm : weight m = 3) (ρ : Mat7) (htr : ρ.trace = 1) :
    4 * b3 (rhoSM m ρ) ≤ excessSumM ρ - excessM m ρ := by
  rw [rhoSM_b3 m hm]
  have hI1 := purity_maskM m hm ρ
  have hS : ∑ m' ∈ tripleMasks, ∑ μ ∈ suppSet m', psqM ρ μ =
      ∑ μ : Fin 7 → Fin 4, (cntN (pwt μ) : ℝ) * psqM ρ μ := sum_cuts_paulM (psqM ρ)
  have hS' : ∑ m' ∈ tripleMasks, ∑ μ ∈ suppSet m', psqM ρ μ =
      8 * ∑ m' ∈ tripleMasks, cutPurityM (maskCut 3 4 m') ρ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m' hm' => purity_maskM m' (Finset.mem_filter.1 hm').2 ρ
  set κ : (Fin 7 → Fin 4) → ℝ := fun μ =>
    (cntN (pwt μ) : ℝ) - (if μ ∈ suppSet m then 1 + 4 * (if pwt μ = 2 then 1 else 0) else 0) with hκ
  have hκnn : ∀ μ, 0 ≤ κ μ := by
    intro μ
    simp only [hκ]
    by_cases hμ : μ ∈ suppSet m
    · have h3 := pwt_le_of_mem_suppSet m hm hμ
      simp only [hμ, ↓reduceIte]
      generalize pwt μ = j at h3
      interval_cases j <;> simp [cntN] <;> norm_num
    · simp only [hμ, ↓reduceIte]; simp
  have hK : κ 0 * psqM ρ 0 ≤ ∑ μ, κ μ * psqM ρ μ :=
    Finset.single_le_sum (f := fun μ => κ μ * psqM ρ μ)
      (fun μ _ => mul_nonneg (hκnn μ) (Complex.normSq_nonneg _)) (Finset.mem_univ _)
  have hκ0 : κ 0 = 34 := by
    simp only [hκ]
    simp only [zero_mem_suppSet m, ↓reduceIte, pwt_zero]
    simp [cntN]
    norm_num
  have hexp : ∑ μ, κ μ * psqM ρ μ =
      ∑ μ : Fin 7 → Fin 4, (cntN (pwt μ) : ℝ) * psqM ρ μ -
        (∑ μ ∈ suppSet m, psqM ρ μ + 4 * ∑ μ ∈ suppSet m, if pwt μ = 2 then psqM ρ μ else 0) := by
    have : ∀ μ, κ μ * psqM ρ μ = (cntN (pwt μ) : ℝ) * psqM ρ μ -
        (if μ ∈ suppSet m then psqM ρ μ + 4 * (if pwt μ = 2 then psqM ρ μ else 0) else 0) := by
      intro μ
      simp only [hκ]
      split_ifs <;> ring
    simp only [this, Finset.sum_sub_distrib]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hκ0, psqM_zero ρ htr, hexp, ← hS, hS', hI1] at hK
  unfold excessSumM excessM
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, tripleMasks_card, nsmul_eq_mul]
  push_cast
  linarith

/-- **`prop:seven-spinflip-spectral-pair`, cross-cut inequality for mixed global states.**
For a Hermitian trace-one seven-qubit matrix `ρ` (in particular every density matrix) and every three-site
cut `S` (mask `m`), `e_S + 16 v(ρ_S) ≤ R = ∑_{|T|=3} e_T`. -/
theorem cross_cut_mixed (m : Fin 7 → Bool) (hm : weight m = 3) (ρ : Mat7) (hρ : ρ.IsHermitian)
    (htr : ρ.trace = 1) :
    excessM m ρ + 16 * v3 (rhoSM m ρ) (rhoSM_hermitian m ρ hρ) ≤ excessSumM ρ := by
  have h1 := b3_ge_four_v3 (rhoSM m ρ) (rhoSM_hermitian m ρ hρ) (rhoSM_trace m hm ρ htr)
  have h2 := four_b_leM m hm ρ htr
  linarith

/-- The same, for a density matrix (positive semidefinite, trace one). -/
theorem cross_cut_mixed_density (m : Fin 7 → Bool) (hm : weight m = 3) (ρ : Mat7)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    excessM m ρ + 16 * v3 (rhoSM m ρ) (rhoSM_hermitian m ρ hρ.isHermitian) ≤ excessSumM ρ :=
  cross_cut_mixed m hm ρ hρ.isHermitian htr

/-- Consistency: for `ρ = |ψ⟩⟨ψ|` this is the pure-state `cross_cut`. -/
theorem cross_cut_mixed_pure (m : Fin 7 → Bool) (hm : weight m = 3) (ψ : BitString → ℂ)
    (hψ : UnitVec ψ) :
    excessM m (Matrix.vecMulVec ψ (star ψ)) +
        16 * v3 (rhoSM m (Matrix.vecMulVec ψ (star ψ)))
          (rhoSM_hermitian m _ (vecMulVec_hermitian ψ)) ≤
      excessSumM (Matrix.vecMulVec ψ (star ψ)) := by
  have htr : (Matrix.vecMulVec ψ (star ψ)).trace = 1 := by
    have : (Matrix.vecMulVec ψ (star ψ)).trace = ((∑ z, Complex.normSq (ψ z) : ℝ) : ℂ) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Complex.ofReal_sum]
      exact Finset.sum_congr rfl fun z _ => by simp [Complex.mul_conj]
    rw [this, hψ]; simp
  exact cross_cut_mixed m hm _ (vecMulVec_hermitian ψ) htr

end FormalResearch.FourQubitEntropy.SevenQubitSpectralPair

