import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Order.Rearrangement
import FormalResearch.FourQubitEntropy.SevenQubitConseqPurity

/-!
# Spin-flip spectral pairing for three qubits (`prop:seven-spinflip-spectral-pair`, first assertion)

Source: `ResearchNotes/QI/seven_qubit_entanglement/seven_qubit_entropy_compatibility.tex`
(QIprojects PR #200), `prop:seven-spinflip-spectral-pair`.  Claim class: **proved** (no hypothesis).

For a three-qubit matrix `ρ : Mat3` (rows and columns `Fin 3 → Bool`):
* `e3 ρ = 8 tr ρ² - 1`; `b3 ρ = ∑_{wt ν = 2} |tr(ρ P_ν)|²` (the weight-two Pauli squares);
* `lam3 ρ hρ : Fin 8 → ℝ` the eigenvalues in decreasing order `λ₁ ≥ ⋯ ≥ λ₈` and
  `v3 ρ hρ = ∑_{i=1}^4 (λᵢ + λ_{9-i} - 1/4)²`;
* `spinFlip3 ρ = Y^{⊗3} ρᵀ Y^{⊗3}`.

Contents.
* **Von Neumann trace rearrangement** (proved here, Mathlib has none): `rearr_fin` (Birkhoff's theorem
  `doublyStochastic_eq_convexHull_permMatrix` + the rearrangement inequality), `trace_form`,
  `trace_rearrange_aux`, `spectral_pairing_data`: for Hermitian `ρ` and any unitary `V`,
  `∑ λ↓ᵢ λ↓_{rev i} ≤ re tr(ρ · V diag(λ) V*)`.
* **Pauli identities** (`signed_sum`, `trace_flip_cast`, `flip_formula`): for Hermitian `ρ` with
  `tr ρ = 1`, `8 tr(ρ ρ̃) = 1 - e + 2b`; `tr ρ² = (1+e)/8` is the definition of `e3`.
* `flip_conj`: `ρ̃ = V diag(λ) V*` with `V = Y^{⊗3} · conj(U)` unitary (`U` the eigenvector unitary), so
  the rearrangement bound applies to `tr(ρ ρ̃)`.
* `vSpec_eq`, `spectral_pair_abstract`: the algebra on an abstract eight-point spectrum.
* **Main results:** `b3_ge_four_v3` (Hermitian, trace one) and `spinflip_spectral_pair` (density matrices):
  `4 v(ρ) ≤ b(ρ)`.

The cross-cut inequality is in `SevenQubitSpectralPairCross.lean`, the equality family in
`SevenQubitSpectralPairEq.lean`.
-/

open scoped ComplexConjugate Matrix ComplexOrder
open Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitSpectralPair

/-! ### The rearrangement step -/

theorem rearr_perm {N : ℕ} (a b : Fin N → ℝ) (ha : Antitone a) (hb : Antitone b)
    (σ : Equiv.Perm (Fin N)) :
    ∑ i, a i * b (Fin.rev i) ≤ ∑ i, a i * b (σ i) := by
  have hanti : Antivary (fun j => a (Fin.rev j)) b := by
    intro i j hij
    have : j < i := by
      by_contra h
      exact absurd (hb (not_lt.mp h)) (not_le.mpr hij)
    exact ha (Fin.rev_le_rev.mpr this.le)
  have h := hanti.sum_smul_le_sum_comp_perm_smul (σ := σ.symm.trans Fin.revPerm)
  have e1 : ∑ i, a i * b (Fin.rev i) = ∑ j, a (Fin.rev j) • b j := by
    rw [← Equiv.sum_comp Fin.revPerm]
    simp
  have e2 : ∑ i, a i * b (σ i) = ∑ j, a (Fin.rev ((σ.symm.trans Fin.revPerm) j)) • b j := by
    rw [← Equiv.sum_comp σ.symm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  rw [e1, e2]
  exact h

theorem rearr_fin {N : ℕ} (a b : Fin N → ℝ) (ha : Antitone a) (hb : Antitone b)
    (D : Matrix (Fin N) (Fin N) ℝ) (hD : D ∈ doublyStochastic ℝ (Fin N)) :
    ∑ i, a i * b (Fin.rev i) ≤ ∑ i, ∑ j, a i * b j * D i j := by
  obtain ⟨w, hw0, hw1, hwD⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hD
  have hentry : ∀ i j, D i j = ∑ σ, w σ * (if σ i = j then 1 else 0) := by
    intro i j
    rw [← hwD]
    simp [Matrix.sum_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  have key : ∑ i, ∑ j, a i * b j * D i j =
      ∑ σ, w σ * ∑ i, a i * b (σ i) := by
    have h1 : ∀ i j, a i * b j * D i j =
        ∑ σ, w σ * (a i * b j * (if σ i = j then 1 else 0)) := by
      intro i j
      rw [hentry, Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by ring
    have h2 : ∀ i, ∑ j, ∑ σ, w σ * (a i * b j * (if σ i = j then 1 else 0)) =
        ∑ σ, w σ * (a i * b (σ i)) := by
      intro i
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.sum_eq_single (σ i)]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · simp
    simp only [h1, h2]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun σ _ => by rw [Finset.mul_sum]
  rw [key]
  calc ∑ i, a i * b (Fin.rev i) = ∑ σ, w σ * ∑ i, a i * b (Fin.rev i) := by
        rw [← Finset.sum_mul, hw1, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (rearr_perm a b ha hb σ) (hw0 σ)

/-! ### The trace form of two unitarily diagonalised matrices -/

section TraceForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `tr(A B)` for `A = U diag(x) U*`, `B = V diag(y) V*`: `∑_{ij} xᵢ yⱼ |(U*V)_{ij}|²`. -/
theorem trace_form (U V : Matrix ι ι ℂ) (x y : ι → ℝ) :
    ((U * Matrix.diagonal (fun i => (x i : ℂ)) * star U) *
        (V * Matrix.diagonal (fun i => (y i : ℂ)) * star V)).trace =
      ((∑ i, ∑ j, x i * y j * Complex.normSq ((star U * V) i j) : ℝ) : ℂ) := by
  set W : Matrix ι ι ℂ := star U * V with hW
  have h1 : (U * Matrix.diagonal (fun i => (x i : ℂ)) * star U) *
        (V * Matrix.diagonal (fun i => (y i : ℂ)) * star V) =
      U * (Matrix.diagonal (fun i => (x i : ℂ)) * W * Matrix.diagonal (fun i => (y i : ℂ)) * star V) := by
    simp only [hW, Matrix.mul_assoc]
  rw [h1, Matrix.trace_mul_comm]
  have h2 : Matrix.diagonal (fun i => (x i : ℂ)) * W * Matrix.diagonal (fun i => (y i : ℂ)) * star V * U =
      Matrix.diagonal (fun i => (x i : ℂ)) * W * Matrix.diagonal (fun i => (y i : ℂ)) * star W := by
    simp only [hW, Matrix.star_mul, star_star, Matrix.mul_assoc]
  rw [h2]
  set A : Matrix ι ι ℂ := Matrix.diagonal (fun i => (x i : ℂ)) * W * Matrix.diagonal (fun i => (y i : ℂ))
    with hA
  have hAij : ∀ i j, A i j = (x i : ℂ) * W i j * (y j : ℂ) := by
    intro i j
    rw [hA, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hAij, Matrix.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have := Complex.mul_conj (W i j)
  simp only [Complex.star_def]
  push_cast
  linear_combination ((x i : ℂ) * (y j : ℂ)) * this

end TraceForm

/-! ### Von Neumann's trace inequality for a Hermitian matrix and its unitary conjugates -/

section VonNeumann

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trace_rearrange_aux (ρ : Matrix ι ι ℂ) (hρ : ρ.IsHermitian) (V : Matrix ι ι ℂ)
    (hV : star V * V = 1) (hV' : V * star V = 1) :
    ∑ i : Fin (Fintype.card ι), hρ.eigenvalues₀ i * hρ.eigenvalues₀ (Fin.rev i) ≤
      (ρ * (V * Matrix.diagonal (fun i => (hρ.eigenvalues i : ℂ)) * star V)).trace.re := by
  set U : Matrix ι ι ℂ := (hρ.eigenvectorUnitary : Matrix ι ι ℂ) with hUdef
  have hU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hρU : ρ = U * Matrix.diagonal (fun i => (hρ.eigenvalues i : ℂ)) * star U := by
    have := hρ.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  set σ : Matrix ι ι ℂ := V * Matrix.diagonal (fun i => (hρ.eigenvalues i : ℂ)) * star V with hσ
  have h1 : (ρ * σ).trace.re =
      ∑ i, ∑ j, hρ.eigenvalues i * hρ.eigenvalues j * Complex.normSq ((star U * V) i j) := by
    have := congrArg (fun A => (A * σ).trace) hρU
    beta_reduce at this
    rw [this, hσ, trace_form U V]
    simp
  set W : Matrix ι ι ℂ := star U * V with hW
  have hW1 : W * star W = 1 := by
    simp only [hW, Matrix.star_mul, star_star, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V, hV', Matrix.one_mul, hU]
  have hW2 : star W * W = 1 := by
    simp only [hW, Matrix.star_mul, star_star, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U, hU', Matrix.one_mul, hV]
  set e : Fin (Fintype.card ι) ≃ ι := Fintype.equivOfCardEq (Fintype.card_fin _) with he
  set a : Fin (Fintype.card ι) → ℝ := hρ.eigenvalues₀ with ha
  set D : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ :=
    Matrix.of fun k l => Complex.normSq (W (e k) (e l)) with hD
  have hDs : D ∈ doublyStochastic ℝ (Fin (Fintype.card ι)) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun k l => Complex.normSq_nonneg _, fun k => ?_, fun l => ?_⟩
    · have h := congrFun (congrFun hW1 (e k)) (e k)
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
      have h' : ∑ j, Complex.normSq (W (e k) j) = 1 := by
        apply Complex.ofReal_injective
        push_cast
        simp only [← Complex.mul_conj]
        rw [← h]
        simp [Matrix.star_apply]
      simp only [hD, Matrix.of_apply]
      rw [Equiv.sum_comp e (fun j => Complex.normSq (W (e k) j))]
      exact h'
    · have h := congrFun (congrFun hW2 (e l)) (e l)
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
      have h' : ∑ i, Complex.normSq (W i (e l)) = 1 := by
        apply Complex.ofReal_injective
        push_cast
        rw [← h]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.normSq_eq_conj_mul_self]
        simp [Complex.star_def]
      simp only [hD, Matrix.of_apply]
      rw [Equiv.sum_comp e (fun i => Complex.normSq (W i (e l)))]
      exact h'
  have h2 := rearr_fin a a hρ.eigenvalues₀_antitone hρ.eigenvalues₀_antitone D hDs
  rw [h1]
  refine h2.trans (le_of_eq ?_)
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [hD, Matrix.IsHermitian.eigenvalues, he, ha]

end VonNeumann

section SpectralData

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem eigen_decomp (ρ : Matrix ι ι ℂ) (hρ : ρ.IsHermitian) :
    ρ = (hρ.eigenvectorUnitary : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (hρ.eigenvalues i : ℂ)) *
      star (hρ.eigenvectorUnitary : Matrix ι ι ℂ) := by
  have := hρ.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at this
  exact this

/-- The sum of the sorted eigenvalues is the trace, and the sum of their squares is `tr ρ²`. -/
theorem spectral_data (ρ : Matrix ι ι ℂ) (hρ : ρ.IsHermitian) :
    ∑ k, hρ.eigenvalues₀ k = ρ.trace.re ∧ ∑ k, hρ.eigenvalues₀ k ^ 2 = (ρ * ρ).trace.re := by
  set e : Fin (Fintype.card ι) ≃ ι := Fintype.equivOfCardEq (Fintype.card_fin _) with he
  have hev : ∀ i, hρ.eigenvalues i = hρ.eigenvalues₀ (e.symm i) := fun i => rfl
  constructor
  · rw [hρ.trace_eq_sum_eigenvalues, Complex.re_sum]
    simp only [hev]
    exact (Equiv.sum_comp e.symm hρ.eigenvalues₀).symm.trans
      (Finset.sum_congr rfl fun x _ => (Complex.ofReal_re _).symm)
  · set U : Matrix ι ι ℂ := (hρ.eigenvectorUnitary : Matrix ι ι ℂ) with hUdef
    have hU : star U * U = 1 := Unitary.coe_star_mul_self _
    have h3 := congrArg (fun A => (A * A).trace) (eigen_decomp ρ hρ)
    beta_reduce at h3
    rw [h3, trace_form U U]
    simp only [hU, Complex.ofReal_re]
    rw [← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp [Matrix.one_apply, hev, sq]
    · intro j _ hj
      have : (1 : Matrix ι ι ℂ) i j = 0 := Matrix.one_apply_ne (Ne.symm hj)
      simp [this]
    · simp

end SpectralData

/-! ### The algebra of the spectral pairing -/

/-- `v` for an eight-point spectrum: `∑_{i=1}^4 (λᵢ + λ_{9-i} - 1/4)²` (`Fin.rev i = 7 - i`). -/
noncomputable def vSpec (l : Fin 8 → ℝ) : ℝ :=
  ∑ i : Fin 4, (l (Fin.castLE (by norm_num) i) + l (Fin.rev (Fin.castLE (by norm_num) i)) - 1 / 4) ^ 2

theorem vSpec_eq (l : Fin 8 → ℝ) (hl : ∑ i, l i = 1) :
    vSpec l = ∑ i, l i ^ 2 + ∑ i, l i * l (Fin.rev i) - 1 / 4 := by
  simp only [Fin.sum_univ_eight] at hl
  simp only [vSpec, Fin.sum_univ_four, Fin.sum_univ_eight]
  have e0 : Fin.rev (Fin.castLE (by norm_num : 4 ≤ 8) (0 : Fin 4)) = (7 : Fin 8) := by decide
  have e1 : Fin.rev (Fin.castLE (by norm_num : 4 ≤ 8) (1 : Fin 4)) = (6 : Fin 8) := by decide
  have e2 : Fin.rev (Fin.castLE (by norm_num : 4 ≤ 8) (2 : Fin 4)) = (5 : Fin 8) := by decide
  have e3 : Fin.rev (Fin.castLE (by norm_num : 4 ≤ 8) (3 : Fin 4)) = (4 : Fin 8) := by decide
  have c0 : Fin.castLE (by norm_num : 4 ≤ 8) (0 : Fin 4) = (0 : Fin 8) := by decide
  have c1 : Fin.castLE (by norm_num : 4 ≤ 8) (1 : Fin 4) = (1 : Fin 8) := by decide
  have c2 : Fin.castLE (by norm_num : 4 ≤ 8) (2 : Fin 4) = (2 : Fin 8) := by decide
  have c3 : Fin.castLE (by norm_num : 4 ≤ 8) (3 : Fin 4) = (3 : Fin 8) := by decide
  have r0 : Fin.rev (0 : Fin 8) = 7 := by decide
  have r1 : Fin.rev (1 : Fin 8) = 6 := by decide
  have r2 : Fin.rev (2 : Fin 8) = 5 := by decide
  have r3 : Fin.rev (3 : Fin 8) = 4 := by decide
  have r4 : Fin.rev (4 : Fin 8) = 3 := by decide
  have r5 : Fin.rev (5 : Fin 8) = 2 := by decide
  have r6 : Fin.rev (6 : Fin 8) = 1 := by decide
  have r7 : Fin.rev (7 : Fin 8) = 0 := by decide
  rw [e0, e1, e2, e3, c0, c1, c2, c3, r0, r1, r2, r3, r4, r5, r6, r7]
  linear_combination (-1 / 2 : ℝ) * hl

/-- **The algebraic core of the spectral pairing.** For an eight-point spectrum `l` summing to `1`, if
`8 ∑ l² = 1 + e`, `8 T = 1 - e + 2 b` and the rearrangement bound `∑ lᵢ l_{rev i} ≤ T` holds, then
`4 v ≤ b`. -/
theorem spectral_pair_abstract (l : Fin 8 → ℝ) (hl : ∑ i, l i = 1) (e b T : ℝ)
    (hpur : 8 * ∑ i, l i ^ 2 = 1 + e) (hT : 8 * T = 1 - e + 2 * b)
    (hrear : ∑ i, l i * l (Fin.rev i) ≤ T) : 4 * vSpec l ≤ b := by
  rw [vSpec_eq l hl]
  linarith

section Wrapper

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Spectral data of a Hermitian `ρ` and of `σ = V diag(λ) V*` re-indexed by `Fin N`
(`N = |ι|`): `∑ λ = tr ρ`, `∑ λ² = tr ρ²` and von Neumann's `∑ λᵢ λ_{N-1-i} ≤ re tr(ρσ)`. -/
theorem spectral_pairing_data (N : ℕ) (h : Fintype.card ι = N) (ρ : Matrix ι ι ℂ)
    (hρ : ρ.IsHermitian) (V : Matrix ι ι ℂ) (hV : star V * V = 1) (hV' : V * star V = 1) :
    ∑ i : Fin N, hρ.eigenvalues₀ (Fin.cast h.symm i) = ρ.trace.re ∧
    ∑ i : Fin N, hρ.eigenvalues₀ (Fin.cast h.symm i) ^ 2 = (ρ * ρ).trace.re ∧
    ∑ i : Fin N, hρ.eigenvalues₀ (Fin.cast h.symm i) *
        hρ.eigenvalues₀ (Fin.cast h.symm (Fin.rev i)) ≤
      (ρ * (V * Matrix.diagonal (fun i => (hρ.eigenvalues i : ℂ)) * star V)).trace.re := by
  subst h
  simp only [Fin.cast_eq_self]
  exact ⟨(spectral_data ρ hρ).1, (spectral_data ρ hρ).2, trace_rearrange_aux ρ hρ V hV hV'⟩

end Wrapper

/-! ### Three-qubit Pauli identities -/

open FormalResearch.FourQubitEntropy.SevenQubitConseq

/-- Computational-basis configurations of three qubits. -/
abbrev Cfg3 := Fin 3 → Bool
/-- Three-qubit operators. -/
abbrev Mat3 := Matrix Cfg3 Cfg3 ℂ

/-- Pauli weight of a three-qubit Pauli string. -/
def wt3 (ν : Fin 3 → Fin 4) : ℕ := (Finset.univ.filter fun i => ν i ≠ 0).card

/-- The sign `(-1)^{wt ν}` of a three-qubit Pauli string. -/
def sgn3 (ν : Fin 3 → Fin 4) : ℝ := ∏ i, (if ν i = 0 then (1 : ℝ) else -1)

/-- `e(ρ) = 8 tr ρ² - 1`. -/
noncomputable def e3 (ρ : Mat3) : ℝ := 8 * (ρ * ρ).trace.re - 1

/-- `b(ρ)`: the sum of the squares of all weight-two Pauli coefficients `tr(ρ P_ν)`, `wt ν = 2`
(that is `∑_{i<j} ∑_{a,b=1}^3 [tr(ρ σ_a^{(i)} σ_b^{(j)})]²`; for Hermitian `ρ` the coefficients are
real and `normSq` is the square). -/
noncomputable def b3 (ρ : Mat3) : ℝ :=
  ∑ ν ∈ Finset.univ.filter (fun ν : Fin 3 → Fin 4 => wt3 ν = 2), Complex.normSq (trP ρ ν)

/-- The Pauli matrix `Y^{⊗3}` in the computational basis. -/
def Y3 : Mat3 := Matrix.of fun a b => ∏ i, pauli 2 (a i) (b i)

/-- The spin flip `ρ̃ = Y^{⊗3} ρᵀ Y^{⊗3}`. -/
noncomputable def spinFlip3 (ρ : Mat3) : Mat3 := Y3 * ρᵀ * Y3

theorem pauli_two (x y : Bool) : pauli 2 x y = -Complex.I * eps x y := by
  cases x <;> cases y <;> simp [pauli, eps]

theorem eps_swap (a b : Bool) : eps b a = - eps a b := by
  cases a <;> cases b <;> simp [eps]

theorem Y3_apply (a b : Cfg3) : Y3 a b = Complex.I * epsV a b := by
  simp only [Y3, Matrix.of_apply, pauli_two, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, epsV]
  have : (-Complex.I) ^ 3 = Complex.I := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, neg_sq, Complex.I_sq]; ring
  rw [this]

theorem epsV_swap (a b : Cfg3) : epsV b a = - epsV a b := by
  unfold epsV
  rw [Finset.prod_congr rfl (fun i _ => eps_swap (a i) (b i)), Finset.prod_neg]
  simp only [Finset.card_univ, Fintype.card_fin]
  ring

/-- The signed Parseval identity (the `ε`-form), with the Pauli coefficients of an arbitrary
three-qubit operator. -/
theorem signed_sum (M : Mat3) :
    ∑ ν : Fin 3 → Fin 4, (∏ i, (if ν i = 0 then (1 : ℂ) else -1)) * (trP M ν * conj (trP M ν)) =
      8 * ∑ a, ∑ a', ∑ b, ∑ b', (M a b * conj (M a' b')) * (epsV b a' * epsV a b') := by
  rw [weighted_sum (fun m : Fin 4 => if m = 0 then (1 : ℂ) else -1) M]
  have hk : ∀ a a' b b' : Cfg3,
      ∏ i, (∑ m : Fin 4, (if m = 0 then (1 : ℂ) else -1) *
        (pauli m (b i) (a i) * conj (pauli m (b' i) (a' i)))) =
        8 * (epsV b a' * epsV a b') := by
    intro a a' b b'
    simp only [fun i => pauli_complete_sign (b i) (a i) (b' i) (a' i), Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, epsV, Fintype.card_fin]
    norm_num
  simp only [hk]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  ring

theorem trace_sq_eq (ρ : Mat3) (hρ : ρ.IsHermitian) :
    (ρ * ρ).trace = ((∑ a, ∑ b, Complex.normSq (ρ a b) : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have h : ρ b a = conj (ρ a b) := by
    have := hρ.apply a b
    rw [← this]; simp
  rw [h, Complex.mul_conj]

theorem sum_normSq_trP (ρ : Mat3) (hρ : ρ.IsHermitian) :
    ∑ ν, Complex.normSq (trP ρ ν) = 8 * (ρ * ρ).trace.re := by
  have h := sum_sq_trP (κ := Fin 3) ρ
  rw [trace_sq_eq ρ hρ, Complex.ofReal_re]
  simp only [Fintype.card_fin] at h
  rw [h]
  norm_num

theorem Y3_mul_Y3 : Y3 * Y3 = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Y3_apply]
  have h : ∑ c, Complex.I * epsV a c * (Complex.I * epsV c b) = - ∑ c, epsV a c * epsV c b := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    linear_combination (epsV a c * epsV c b) * Complex.I_sq
  have h2 : ∑ c, epsV a c * epsV c b = ∏ i, ∑ x, eps (a i) x * eps x (b i) := by
    simp only [epsV, ← Finset.prod_mul_distrib]
    rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset Bool))
      (fun i x => eps (a i) x * eps x (b i)), Fintype.piFinset_univ]
  have h3 : ∀ x y : Bool, ∑ c, eps x c * eps c y = if x = y then -1 else 0 := by
    intro x y
    cases x <;> cases y <;> simp [eps, Fintype.sum_bool]
  rw [h, h2]
  simp only [h3]
  rw [Finset.prod_ite_zero]
  by_cases hab : a = b
  · subst hab; simp; norm_num
  · have : ¬ ∀ i ∈ (Finset.univ : Finset (Fin 3)), a i = b i := by
      intro hh; exact hab (funext fun i => hh i (Finset.mem_univ i))
    rw [if_neg this, Matrix.one_apply_ne hab]
    simp

theorem Y3_star : star Y3 = Y3 := by
  ext a b
  simp only [Matrix.star_apply, Y3_apply, Complex.star_def, map_mul, Complex.conj_I, conj_epsV]
  rw [epsV_swap a b]
  ring

theorem trace_flip_cast (ρ : Mat3) (hρ : ρ.IsHermitian) :
    8 * (ρ * spinFlip3 ρ).trace = ((∑ ν, sgn3 ν * Complex.normSq (trP ρ ν) : ℝ) : ℂ) := by
  have h1 := signed_sum ρ
  have hL : ((∑ ν, sgn3 ν * Complex.normSq (trP ρ ν) : ℝ) : ℂ) =
      ∑ ν : Fin 3 → Fin 4, (∏ i, (if ν i = 0 then (1 : ℂ) else -1)) *
        (trP ρ ν * conj (trP ρ ν)) := by
    have hc : ∀ m : Fin 4, (((if m = 0 then (1 : ℝ) else -1 : ℝ)) : ℂ) =
        if m = 0 then 1 else -1 := by
      intro m; split_ifs <;> simp
    simp only [sgn3]
    push_cast
    simp only [hc, Complex.mul_conj]
  rw [hL, h1]
  congr 1
  have e1 : (ρ * spinFlip3 ρ).trace =
      ∑ a, ∑ b, ∑ x, ∑ y, ρ a b * (Y3 b x * ρ y x * Y3 y a) := by
    simp only [Matrix.trace, Matrix.diag, spinFlip3, Matrix.mul_apply, Matrix.transpose_apply,
      Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
  rw [e1]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun y _ => ?_
  have hh : conj (ρ x y) = ρ y x := by
    have := hρ.apply x y
    rw [← this]; simp
  rw [hh, Y3_apply, Y3_apply, epsV_swap a y]
  linear_combination (-(ρ a b * ρ y x * epsV b x * epsV a y)) * Complex.I_sq

theorem sgn3_eq (ν : Fin 3 → Fin 4) : sgn3 ν = (-1) ^ wt3 ν := by
  unfold sgn3 wt3
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]

theorem wt3_le (ν : Fin 3 → Fin 4) : wt3 ν ≤ 3 := by
  unfold wt3
  have := Finset.card_le_univ (Finset.univ.filter fun i => ν i ≠ 0)
  simpa using this

theorem wt3_eq_zero_iff (ν : Fin 3 → Fin 4) : wt3 ν = 0 ↔ ν = 0 := by
  unfold wt3
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h; funext i; by_contra hi; exact h (Finset.mem_univ i) hi
  · rintro rfl; simp

theorem trP_zero (ρ : Mat3) : trP ρ 0 = ρ.trace := by
  unfold trP
  simp only [Pi.zero_apply, prod_pauli_zero]
  simp [Matrix.trace, Matrix.diag, eq_comm]

theorem sum_sgn_normSq (ρ : Mat3) (htr : ρ.trace = 1) :
    ∑ ν, sgn3 ν * Complex.normSq (trP ρ ν) =
      2 * (1 + b3 ρ) - ∑ ν, Complex.normSq (trP ρ ν) := by
  set f : (Fin 3 → Fin 4) → ℝ := fun ν => Complex.normSq (trP ρ ν) with hf
  have hpt : ∀ ν, sgn3 ν * f ν =
      2 * ((if wt3 ν = 0 then f ν else 0) + (if wt3 ν = 2 then f ν else 0)) - f ν := by
    intro ν
    have h3 := wt3_le ν
    rw [sgn3_eq]
    generalize wt3 ν = w at h3 ⊢
    interval_cases w <;> simp <;> ring
  have h0 : ∑ ν, (if wt3 ν = 0 then f ν else 0) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp [hf, trP_zero, htr, (wt3_eq_zero_iff 0).2 rfl]
    · intro ν _ hν
      rw [if_neg]
      rwa [wt3_eq_zero_iff]
    · simp
  have h2 : ∑ ν, (if wt3 ν = 2 then f ν else 0) = b3 ρ := by
    unfold b3
    rw [Finset.sum_filter]
  calc ∑ ν, sgn3 ν * Complex.normSq (trP ρ ν) = ∑ ν, sgn3 ν * f ν := rfl
    _ = ∑ ν, (2 * ((if wt3 ν = 0 then f ν else 0) + (if wt3 ν = 2 then f ν else 0)) - f ν) :=
        Finset.sum_congr rfl fun ν _ => hpt ν
    _ = 2 * (1 + b3 ρ) - ∑ ν, f ν := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, h0, h2]

/-- **The spin-flip Pauli identity** `tr(ρ ρ̃) = (1 - e + 2b)/8` (for Hermitian `ρ` of trace one). -/
theorem flip_formula (ρ : Mat3) (hρ : ρ.IsHermitian) (htr : ρ.trace = 1) :
    8 * (ρ * spinFlip3 ρ).trace.re = 1 - e3 ρ + 2 * b3 ρ := by
  have h : 8 * (ρ * spinFlip3 ρ).trace.re = ∑ ν, sgn3 ν * Complex.normSq (trP ρ ν) := by
    have := congrArg Complex.re (trace_flip_cast ρ hρ)
    simpa using this
  rw [h, sum_sgn_normSq ρ htr, sum_normSq_trP ρ hρ]
  unfold e3
  ring

/-! ### The spin-flipped matrix has the spectrum of `ρ` -/

theorem star_map_conj (U : Mat3) : star (U.map conj) = Uᵀ := by
  ext i j; simp [Matrix.star_apply]

theorem transpose_star' (U : Mat3) : (star U)ᵀ = U.map conj := by
  ext i j; simp [Matrix.star_apply]

theorem flip_conj (ρ : Mat3) (hρ : ρ.IsHermitian) :
    (Y3 * (hρ.eigenvectorUnitary : Mat3).map conj) *
        Matrix.diagonal (fun i => (hρ.eigenvalues i : ℂ)) *
        star (Y3 * (hρ.eigenvectorUnitary : Mat3).map conj) = spinFlip3 ρ := by
  set U : Mat3 := (hρ.eigenvectorUnitary : Mat3) with hU
  have hρU := eigen_decomp ρ hρ
  have hT : ρᵀ = U.map conj * Matrix.diagonal (fun i => (hρ.eigenvalues i : ℂ)) * Uᵀ := by
    calc ρᵀ = (U * Matrix.diagonal (fun i => (hρ.eigenvalues i : ℂ)) * star U)ᵀ :=
          congrArg Matrix.transpose hρU
      _ = _ := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose, transpose_star',
          Matrix.mul_assoc]
  unfold spinFlip3
  rw [hT, Matrix.star_mul, star_map_conj, Y3_star]
  simp only [Matrix.mul_assoc]

theorem unitary_conj (ρ : Mat3) (hρ : ρ.IsHermitian) :
    star (Y3 * (hρ.eigenvectorUnitary : Mat3).map conj) * (Y3 * (hρ.eigenvectorUnitary : Mat3).map conj) = 1 ∧
    (Y3 * (hρ.eigenvectorUnitary : Mat3).map conj) * star (Y3 * (hρ.eigenvectorUnitary : Mat3).map conj) = 1 := by
  set U : Mat3 := (hρ.eigenvectorUnitary : Mat3) with hU
  have h1 : star U * U = 1 := Unitary.coe_star_mul_self _
  have h2 : U * star U = 1 := Unitary.coe_mul_star_self _
  have hc1 : star (U.map conj) * U.map conj = 1 := by
    rw [star_map_conj]
    have := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, transpose_star', Matrix.transpose_one] at this
    exact this
  have hc2 : U.map conj * star (U.map conj) = 1 := by
    rw [star_map_conj]
    have := congrArg Matrix.transpose h2
    rw [Matrix.transpose_mul, transpose_star', Matrix.transpose_one] at this
    exact this
  constructor
  · rw [Matrix.star_mul, Y3_star]
    calc star (U.map conj) * Y3 * (Y3 * U.map conj) = star (U.map conj) * (Y3 * Y3) * U.map conj := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Y3_mul_Y3, Matrix.mul_one, hc1]
  · rw [Matrix.star_mul, Y3_star]
    calc Y3 * U.map conj * (star (U.map conj) * Y3) = Y3 * (U.map conj * star (U.map conj)) * Y3 := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hc2, Matrix.mul_one, Y3_mul_Y3]

/-! ### The matrix-level statement -/

theorem card_cfg3 : Fintype.card Cfg3 = 8 := by simp

/-- The sorted spectrum `λ₁ ≥ ⋯ ≥ λ₈` of a three-qubit Hermitian matrix, as a function on `Fin 8`. -/
noncomputable def lam3 (ρ : Mat3) (hρ : ρ.IsHermitian) : Fin 8 → ℝ :=
  fun i => hρ.eigenvalues₀ (Fin.cast card_cfg3.symm i)

/-- `v(ρ) = ∑_{i=1}^4 (λᵢ + λ_{9-i} - 1/4)²`. -/
noncomputable def v3 (ρ : Mat3) (hρ : ρ.IsHermitian) : ℝ := vSpec (lam3 ρ hρ)

/-- **`prop:seven-spinflip-spectral-pair`, first assertion (sharp spectral inequality).**
Every Hermitian three-qubit matrix of trace one (in particular every density matrix) satisfies
`b(ρ) ≥ 4 v(ρ)`. -/
theorem b3_ge_four_v3 (ρ : Mat3) (hρ : ρ.IsHermitian) (htr : ρ.trace = 1) :
    4 * v3 ρ hρ ≤ b3 ρ := by
  obtain ⟨hV, hV'⟩ := unitary_conj ρ hρ
  obtain ⟨hsum, hsq, hrear⟩ := spectral_pairing_data 8 card_cfg3 ρ hρ _ hV hV'
  rw [flip_conj ρ hρ] at hrear
  have hflip := flip_formula ρ hρ htr
  refine spectral_pair_abstract (lam3 ρ hρ) ?_ (e3 ρ) (b3 ρ) ((ρ * spinFlip3 ρ).trace.re) ?_ hflip hrear
  · simp only [lam3]
    rw [hsum, htr]; simp
  · simp only [lam3]
    rw [hsq]; unfold e3; ring

/-- **`prop:seven-spinflip-spectral-pair`, first assertion, for density matrices.** -/
theorem spinflip_spectral_pair (ρ : Mat3) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    4 * v3 ρ hρ.isHermitian ≤ b3 ρ :=
  b3_ge_four_v3 ρ hρ.isHermitian htr

end FormalResearch.FourQubitEntropy.SevenQubitSpectralPair
