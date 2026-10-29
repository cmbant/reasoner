import Mathlib

/-!
# Isospectral overlap lemma (square bipartite case)

Source: `ResearchNotes/QI/four_qubit_entropy/spectral_spinflip_bound.tex`, Lemma
`lem:fqe-isospectral-overlap` (QIprojects PR 208).

A bipartite pure state with `n × n` coefficient matrix `M` has marginals `ρ_A = M M†` and
`ρ_B = (M† M)ᵀ`. Two unit states `M`, `W` with common Schmidt coefficients have
`WW† = P (MM†) P†` and `W†W = Q (M†M) Q†` for unitaries `P`, `Q`. The lemma states

`|⟨ψ,φ⟩|² + ½ (‖ρ_A - σ_A‖²_F + ‖ρ_B - σ_B‖²_F) ≥ (2 λ₁ - 1)₊²`.

* `isospectral_overlap` (**proved**): the lemma for equal local dimensions (`M W : Matrix ι ι ℂ`). The
  top Schmidt coefficient `λ₁` is represented by any eigenvalue `l` of `M M†` with eigenvector `u`;
  for `l > 1/2` it is the largest eigenvalue, and for `l ≤ 1/2` the right side is `0`, so the bound is
  stated for every eigenvalue. The Schmidt bases of the two states are unrelated.
  Not formalized: unequal local dimensions (the paper pads with zeros) and the sharpness statement.
* `antiunitary_overlap` (**proved**): the instance `W = E M̄ F` (`E`, `F` unitary), the shape taken by
  the spin flip of a state.

Proof (the paper's): the top singular pair of `M` is a pair of simple eigenvectors, the quadratic form
`B(W) = ‖W‖² + |tr M†W|² - tr(MM† WW†) - tr(M†M W†W)` equals a positive remainder plus
`tr(S WW†) + tr(S W†W)`, and the rearrangement inequality for doubly stochastic matrices (Birkhoff's
theorem, `rearr_ds`) bounds the latter below (`kfa`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Matrix Finset

namespace FormalResearch.FourQubitEntropy.Isospectral


theorem rearr_ds {ι : Type*} [Fintype ι] [DecidableEq ι] (c μ : ι → ℝ) (hm : Monovary c μ)
    (G : Matrix ι ι ℝ) (hG : G ∈ doublyStochastic ℝ ι) :
    ∑ i, ∑ k, c i * μ k * G i k ≤ ∑ i, c i * μ i := by
  have hG2 : G ∈ (doublyStochastic ℝ ι : Set (Matrix ι ι ℝ)) := hG
  rw [doublyStochastic_eq_convexHull_permMatrix] at hG2
  have hconv : Convex ℝ {G : Matrix ι ι ℝ | ∑ i, ∑ k, c i * μ k * G i k ≤ ∑ i, c i * μ i} := by
    intro A hA B hB a b ha hb hab
    simp only [Set.mem_ofPred_eq] at hA hB ⊢
    have : ∑ i, ∑ k, c i * μ k * (a • A + b • B) i k
        = a * ∑ i, ∑ k, c i * μ k * A i k + b * ∑ i, ∑ k, c i * μ k * B i k := by
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
        Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    have h1 := mul_le_mul_of_nonneg_left hA ha
    have h2 := mul_le_mul_of_nonneg_left hB hb
    have h3 : (a + b) * ∑ i, c i * μ i = ∑ i, c i * μ i := by rw [hab, one_mul]
    linarith
  have hsub : {M | ∃ σ : Equiv.Perm ι, σ.permMatrix ℝ = M} ⊆
      {G : Matrix ι ι ℝ | ∑ i, ∑ k, c i * μ k * G i k ≤ ∑ i, c i * μ i} := by
    rintro _ ⟨σ, rfl⟩
    simp only [Set.mem_ofPred_eq]
    have : ∀ i, ∑ k, c i * μ k * (σ.permMatrix ℝ) i k = c i * μ (σ i) := by
      intro i
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    simp only [this]
    exact hm.sum_mul_comp_perm_le_sum_mul
  exact (convexHull_min hsub hconv) hG2

theorem normSq_unitary_row {ι : Type*} [Fintype ι] [DecidableEq ι] (K : Matrix ι ι ℂ)
    (hK : K ∈ Matrix.unitaryGroup ι ℂ) (i : ι) : ∑ k, Complex.normSq (K i k) = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hK) i) i
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  have : ∑ k, ((Complex.normSq (K i k) : ℝ) : ℂ) = 1 := by
    rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.mul_conj]
  exact_mod_cast this

theorem normSq_unitary_col {ι : Type*} [Fintype ι] [DecidableEq ι] (K : Matrix ι ι ℂ)
    (hK : K ∈ Matrix.unitaryGroup ι ℂ) (k : ι) : ∑ i, Complex.normSq (K i k) = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hK) k) k
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  have : ∑ i, ((Complex.normSq (K i k) : ℝ) : ℂ) = 1 := by
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, mul_comm, Complex.mul_conj]
  exact_mod_cast this

theorem kfa {ι : Type*} [Fintype ι] [DecidableEq ι] (K : Matrix ι ι ℂ)
    (hK : K ∈ Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) (hμ0 : ∀ i, 0 ≤ μ i) (hsum : ∑ i, μ i = 1)
    (i₀ : ι) (hmax : ∀ i, μ i ≤ μ i₀) :
    ∑ i, μ i * (∑ k, μ k * Complex.normSq (K i k))
      - (2 * μ i₀ - 1) * ∑ k, μ k * Complex.normSq (K i₀ k)
      ≤ ∑ i, μ i ^ 2 - (2 * μ i₀ - 1) * μ i₀ := by
  set d : ℝ := 2 * μ i₀ - 1 with hd
  let c : ι → ℝ := fun i => μ i - if i = i₀ then d else 0
  have hG : (Matrix.of fun i k => Complex.normSq (K i k) : Matrix ι ι ℝ) ∈ doublyStochastic ℝ ι := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i k => Complex.normSq_nonneg _, fun i => normSq_unitary_row K hK i,
      fun k => normSq_unitary_col K hK k⟩
  have hmono : Monovary c μ := by
    intro i j hij
    have hr : ∀ i, i ≠ i₀ → μ i ≤ 1 - μ i₀ := by
      intro i hi
      have : μ i + μ i₀ ≤ ∑ k, μ k := by
        have := Finset.sum_le_sum_of_subset_of_nonneg (f := μ) (s := {i, i₀})
          (t := Finset.univ) (Finset.subset_univ _) (fun k _ _ => hμ0 k)
        rwa [Finset.sum_pair hi] at this
      linarith
    by_cases hj : j = i₀
    · subst hj
      have hi : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
      simp only [c, hi, ite_false, ite_true]
      have := hr i hi
      simp only [hd]; linarith
    · by_cases hi : i = i₀
      · subst hi; exact absurd hij (not_lt.mpr (hmax j))
      · simp only [c, hi, hj, ite_false, sub_zero]; exact hij.le
  have h := rearr_ds c μ hmono _ hG
  simp only [Matrix.of_apply] at h
  have e1 : ∑ i, ∑ k, c i * μ k * Complex.normSq (K i k)
      = ∑ i, μ i * (∑ k, μ k * Complex.normSq (K i k))
        - d * ∑ k, μ k * Complex.normSq (K i₀ k) := by
    simp only [c, sub_mul, Finset.sum_sub_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    · rw [Finset.sum_eq_single i₀]
      · simp [Finset.mul_sum, mul_assoc]
      · intro i _ hi; simp [hi]
      · simp
  have e2 : ∑ i, c i * μ i = ∑ i, μ i ^ 2 - d * μ i₀ := by
    simp only [c, sub_mul, Finset.sum_sub_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · rw [Finset.sum_eq_single i₀]
      · simp
      · intro i _ hi; simp [hi]
      · simp
  rw [e1, e2] at h
  exact h

section Aux
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_split2 {M : Type*} [AddCommMonoid M] (g : ι → ι → M) (i₀ j₀ : ι) :
    ∑ i, ∑ j, g i j = g i₀ j₀ + ∑ j ∈ Finset.univ.erase j₀, g i₀ j
      + ∑ i ∈ Finset.univ.erase i₀, g i j₀
      + ∑ i ∈ Finset.univ.erase i₀, ∑ j ∈ Finset.univ.erase j₀, g i j := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), ← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
  have : ∀ i ∈ Finset.univ.erase i₀, ∑ j, g i j = g i j₀ + ∑ j ∈ Finset.univ.erase j₀, g i j :=
    fun i _ => (Finset.add_sum_erase _ _ (Finset.mem_univ j₀)).symm
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
  abel

/-- Squared Frobenius norm. -/
noncomputable def fn2 (A : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (A i j)

theorem fn2_eq_trace (A : Matrix ι ι ℂ) : ((fn2 A : ℝ) : ℂ) = Matrix.trace (A * Aᴴ) := by
  unfold fn2
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj]

theorem cs_complex (s : Finset (ι × ι)) (z w : ι × ι → ℂ) :
    Complex.normSq (∑ p ∈ s, z p * w p)
      ≤ (∑ p ∈ s, Complex.normSq (z p)) * ∑ p ∈ s, Complex.normSq (w p) := by
  have h1 : ‖∑ p ∈ s, z p * w p‖ ≤ ∑ p ∈ s, ‖z p‖ * ‖w p‖ := by
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum fun p _ => by rw [norm_mul]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun p => ‖z p‖) (fun p => ‖w p‖)
  rw [Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_eq_norm_sq]
  calc ‖∑ p ∈ s, z p * w p‖ ^ 2 ≤ (∑ p ∈ s, ‖z p‖ * ‖w p‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2


/-- real diagonal matrix -/
noncomputable def rdiag (μ : ι → ℝ) : Matrix ι ι ℂ := Matrix.diagonal fun i => ((μ i : ℝ) : ℂ)

theorem rdiag_herm (μ : ι → ℝ) : (rdiag μ)ᴴ = rdiag μ := by
  unfold rdiag
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp

theorem conj_diag_apply (P : Matrix ι ι ℂ) (μ : ι → ℝ) (i : ι) :
    (P * rdiag μ * Pᴴ) i i = ((∑ k, μ k * Complex.normSq (P i k) : ℝ) : ℂ) := by
  simp only [rdiag, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Complex.star_def]
  push_cast
  rw [mul_comm (P i j), mul_assoc, Complex.mul_conj]

theorem trace_conj_sq (P : Matrix ι ι ℂ) (hP : P ∈ Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) :
    Matrix.trace ((P * rdiag μ * Pᴴ) * (P * rdiag μ * Pᴴ)) = ((∑ k, μ k ^ 2 : ℝ) : ℂ) := by
  have h1 : Pᴴ * P = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hP
    rwa [Matrix.star_eq_conjTranspose] at this
  have e : (P * rdiag μ * Pᴴ) * (P * rdiag μ * Pᴴ) = P * (rdiag μ * rdiag μ) * Pᴴ := by
    calc (P * rdiag μ * Pᴴ) * (P * rdiag μ * Pᴴ)
        = P * rdiag μ * (Pᴴ * P) * rdiag μ * Pᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, Matrix.mul_assoc P]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  simp only [rdiag, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast; ring

theorem fn2_diag_sub (P : Matrix ι ι ℂ) (hP : P ∈ Matrix.unitaryGroup ι ℂ) (μ : ι → ℝ) :
    fn2 (rdiag μ - P * rdiag μ * Pᴴ)
      = 2 * ∑ k, μ k ^ 2 - 2 * ∑ i, μ i * ∑ k, μ k * Complex.normSq (P i k) := by
  have hY : (P * rdiag μ * Pᴴ)ᴴ = P * rdiag μ * Pᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      rdiag_herm, Matrix.mul_assoc]
  have hA : (rdiag μ - P * rdiag μ * Pᴴ)ᴴ = rdiag μ - P * rdiag μ * Pᴴ := by
    rw [Matrix.conjTranspose_sub, hY, rdiag_herm]
  have key := fn2_eq_trace (rdiag μ - P * rdiag μ * Pᴴ)
  rw [hA] at key
  have e : (rdiag μ - P * rdiag μ * Pᴴ) * (rdiag μ - P * rdiag μ * Pᴴ)
      = rdiag μ * rdiag μ - rdiag μ * (P * rdiag μ * Pᴴ) - (P * rdiag μ * Pᴴ) * rdiag μ
        + (P * rdiag μ * Pᴴ) * (P * rdiag μ * Pᴴ) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
  rw [e] at key
  simp only [Matrix.trace_add, Matrix.trace_sub] at key
  rw [Matrix.trace_mul_comm (P * rdiag μ * Pᴴ) (rdiag μ), trace_conj_sq P hP μ] at key
  have e2 : Matrix.trace (rdiag μ * (P * rdiag μ * Pᴴ))
      = ((∑ i, μ i * ∑ k, μ k * Complex.normSq (P i k) : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag_apply, rdiag, Matrix.diagonal_mul]
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := conj_diag_apply P μ i
    simp only [rdiag] at this
    rw [this]; push_cast; ring
  have e3 : Matrix.trace (rdiag μ * rdiag μ) = ((∑ k, μ k ^ 2 : ℝ) : ℂ) := by
    simp only [rdiag, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast; ring
  rw [e2, e3] at key
  have : ((fn2 (rdiag μ - P * rdiag μ * Pᴴ) : ℝ) : ℂ)
      = ((2 * ∑ k, μ k ^ 2 - 2 * ∑ i, μ i * ∑ k, μ k * Complex.normSq (P i k) : ℝ) : ℂ) := by
    rw [key]; push_cast; ring
  exact_mod_cast this
end Aux

section Core
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rowsum_of_mul_conjT (A : Matrix ι ι ℂ) (D : Matrix ι ι ℂ) (h : A * Aᴴ = D) (i : ι) :
    ((∑ j, Complex.normSq (A i j) : ℝ) : ℂ) = D i i := by
  rw [← h]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj]

theorem colsum_of_conjT_mul (A : Matrix ι ι ℂ) (D : Matrix ι ι ℂ) (h : Aᴴ * A = D) (j : ι) :
    ((∑ i, Complex.normSq (A i j) : ℝ) : ℂ) = D j j := by
  rw [← h]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, mul_comm, Complex.mul_conj]

theorem fn2_of_mul_conjT (A : Matrix ι ι ℂ) (P : Matrix ι ι ℂ) (hP : P ∈ Matrix.unitaryGroup ι ℂ)
    (μ : ι → ℝ) (h : A * Aᴴ = P * rdiag μ * Pᴴ) : fn2 A = ∑ i, μ i := by
  have h1 : Pᴴ * P = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hP
    rwa [Matrix.star_eq_conjTranspose] at this
  have := fn2_eq_trace A
  rw [h, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul] at this
  simp only [rdiag, Matrix.trace_diagonal, ← Complex.ofReal_sum] at this
  exact_mod_cast this

end Core

section Core2
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem core_overlap (N W P Q : Matrix ι ι ℂ) (μ μ' : ι → ℝ) (i₀ j₀ : ι)
    (hP : P ∈ Matrix.unitaryGroup ι ℂ) (hQ : Q ∈ Matrix.unitaryGroup ι ℂ)
    (hμ0 : ∀ i, 0 ≤ μ i) (hμ'0 : ∀ i, 0 ≤ μ' i) (hsum : ∑ i, μ i = 1) (hsum' : ∑ i, μ' i = 1)
    (hmax : ∀ i, μ i ≤ μ i₀) (hmax' : ∀ i, μ' i ≤ μ' j₀) (hlam : μ' j₀ = μ i₀)
    (hhalf : 1 / 2 ≤ μ i₀)
    (hNN : N * Nᴴ = rdiag μ) (hWA : W * Wᴴ = P * rdiag μ * Pᴴ)
    (hWB : Wᴴ * W = Q * rdiag μ' * Qᴴ)
    (hN1 : ∀ i, i ≠ i₀ → N i j₀ = 0) (hN2 : ∀ j, j ≠ j₀ → N i₀ j = 0) :
    (2 * μ i₀ - 1) ^ 2 ≤ Complex.normSq (Matrix.trace (Nᴴ * W))
      + (fn2 (rdiag μ - W * Wᴴ) + fn2 (rdiag μ' - Wᴴ * W)) / 2 := by
  set l : ℝ := μ i₀ with hl
  set d : ℝ := 2 * l - 1 with hd
  -- A side
  have hA1 : fn2 (rdiag μ - W * Wᴴ)
      = 2 * ∑ k, μ k ^ 2 - 2 * ∑ i, μ i * ∑ k, μ k * Complex.normSq (P i k) := by
    rw [hWA]; exact fn2_diag_sub P hP μ
  have hA2 := kfa P hP μ hμ0 hsum i₀ hmax
  have hA0 : ∑ j, Complex.normSq (W i₀ j) = ∑ k, μ k * Complex.normSq (P i₀ k) := by
    have h := rowsum_of_mul_conjT W _ hWA i₀
    rw [conj_diag_apply] at h
    exact_mod_cast h
  -- B side
  have hQ' : Q ∈ Matrix.unitaryGroup ι ℂ := hQ
  have hB1 : fn2 (rdiag μ' - Wᴴ * W)
      = 2 * ∑ k, μ' k ^ 2 - 2 * ∑ i, μ' i * ∑ k, μ' k * Complex.normSq (Q i k) := by
    rw [hWB]; exact fn2_diag_sub Q hQ μ'
  have hB2 := kfa Q hQ μ' hμ'0 hsum' j₀ hmax'
  have hB0 : ∑ i, Complex.normSq (W i j₀) = ∑ k, μ' k * Complex.normSq (Q j₀ k) := by
    have h := colsum_of_conjT_mul W _ hWB j₀
    rw [conj_diag_apply] at h
    exact_mod_cast h
  set A0 := ∑ j, Complex.normSq (W i₀ j) with hA0def
  set B0 := ∑ i, Complex.normSq (W i j₀) with hB0def
  rw [hlam] at hB2
  rw [← hA0] at hA2
  rw [← hB0] at hB2
  have hfin : 2 * l * d - d * (A0 + B0) ≤
      (fn2 (rdiag μ - W * Wᴴ) + fn2 (rdiag μ' - Wᴴ * W)) / 2 := by
    rw [hA1, hB1]
    simp only [hd, hl] at hA2 hB2 ⊢
    nlinarith [hA2, hB2]
  -- totals
  have hWtot : ∑ i, ∑ j, Complex.normSq (W i j) = 1 := by
    have := fn2_of_mul_conjT W P hP μ hWA
    unfold fn2 at this; rw [this, hsum]
  have hNtot : ∑ i, ∑ j, Complex.normSq (N i j) = 1 := by
    have h := fn2_eq_trace N
    rw [hNN] at h
    simp only [rdiag, Matrix.trace_diagonal, ← Complex.ofReal_sum] at h
    unfold fn2 at h
    have : (∑ i, ∑ j, Complex.normSq (N i j)) = ∑ i, μ i := by exact_mod_cast h
    rw [this, hsum]
  have hn0 : Complex.normSq (N i₀ j₀) = l := by
    have h := rowsum_of_mul_conjT N _ hNN i₀
    simp only [rdiag, Matrix.diagonal_apply_eq] at h
    have h' : ∑ j, Complex.normSq (N i₀ j) = μ i₀ := by exact_mod_cast h
    rw [Finset.sum_eq_single j₀ (fun j _ hj => by simp [hN2 j hj]) (by simp)] at h'
    exact h'
  have hNt : ∑ i ∈ Finset.univ.erase i₀, ∑ j ∈ Finset.univ.erase j₀, Complex.normSq (N i j)
      = 1 - l := by
    have := sum_split2 (fun i j => Complex.normSq (N i j)) i₀ j₀
    simp only [hNtot] at this
    have z1 : ∑ j ∈ Finset.univ.erase j₀, Complex.normSq (N i₀ j) = 0 :=
      Finset.sum_eq_zero fun j hj => by simp [hN2 j (Finset.ne_of_mem_erase hj)]
    have z2 : ∑ i ∈ Finset.univ.erase i₀, Complex.normSq (N i j₀) = 0 :=
      Finset.sum_eq_zero fun i hi => by simp [hN1 i (Finset.ne_of_mem_erase hi)]
    rw [z1, z2, hn0] at this
    linarith
  have hWt : ∑ i ∈ Finset.univ.erase i₀, ∑ j ∈ Finset.univ.erase j₀, Complex.normSq (W i j)
      = 1 - A0 - B0 + Complex.normSq (W i₀ j₀) := by
    have := sum_split2 (fun i j => Complex.normSq (W i j)) i₀ j₀
    simp only [hWtot] at this
    have e1 : A0 = Complex.normSq (W i₀ j₀) + ∑ j ∈ Finset.univ.erase j₀, Complex.normSq (W i₀ j) :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ j₀)).symm
    have e2 : B0 = Complex.normSq (W i₀ j₀) + ∑ i ∈ Finset.univ.erase i₀, Complex.normSq (W i j₀) :=
      (Finset.add_sum_erase (Finset.univ) (fun i => Complex.normSq (W i j₀)) (Finset.mem_univ i₀)).symm
    linarith
  -- trace
  have htr : Matrix.trace (Nᴴ * W) = star (N i₀ j₀) * W i₀ j₀ +
      ∑ p ∈ (Finset.univ.erase i₀) ×ˢ (Finset.univ.erase j₀), star (N p.1 p.2) * W p.1 p.2 := by
    have e : Matrix.trace (Nᴴ * W) = ∑ i, ∑ j, star (N i j) * W i j := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [Finset.sum_comm]
    rw [e, sum_split2 (fun i j => star (N i j) * W i j) i₀ j₀, Finset.sum_product]
    have z1 : ∑ j ∈ Finset.univ.erase j₀, star (N i₀ j) * W i₀ j = 0 :=
      Finset.sum_eq_zero fun j hj => by simp [hN2 j (Finset.ne_of_mem_erase hj)]
    have z2 : ∑ i ∈ Finset.univ.erase i₀, star (N i j₀) * W i j₀ = 0 :=
      Finset.sum_eq_zero fun i hi => by simp [hN1 i (Finset.ne_of_mem_erase hi)]
    rw [z1, z2]; ring
  set T := ∑ p ∈ (Finset.univ.erase i₀) ×ˢ (Finset.univ.erase j₀), star (N p.1 p.2) * W p.1 p.2
    with hT
  have hTcs : Complex.normSq T ≤ (1 - l) * (1 - A0 - B0 + Complex.normSq (W i₀ j₀)) := by
    have h := cs_complex ((Finset.univ.erase i₀) ×ˢ (Finset.univ.erase j₀))
      (fun p => star (N p.1 p.2)) (fun p => W p.1 p.2)
    rw [← hT] at h
    have e1 : ∑ p ∈ (Finset.univ.erase i₀) ×ˢ (Finset.univ.erase j₀),
        Complex.normSq (star (N p.1 p.2)) = 1 - l := by
      rw [Finset.sum_product, ← hNt]
      simp only [Complex.star_def, Complex.normSq_conj]
    have e2 : ∑ p ∈ (Finset.univ.erase i₀) ×ˢ (Finset.univ.erase j₀),
        Complex.normSq (W p.1 p.2) = 1 - A0 - B0 + Complex.normSq (W i₀ j₀) := by
      rw [Finset.sum_product, hWt]
    rw [e1, e2] at h
    exact h
  have hWt0 : 0 ≤ 1 - A0 - B0 + Complex.normSq (W i₀ j₀) := by
    rw [← hWt]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hr : 0 ≤ 1 - l := by
    rw [← hNt]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hω : Complex.normSq (star (N i₀ j₀) * W i₀ j₀) = l * Complex.normSq (W i₀ j₀) := by
    rw [Complex.star_def, map_mul, Complex.normSq_conj, hn0]
  rw [htr]
  set ω := star (N i₀ j₀) * W i₀ j₀ with hωdef
  set ww := Complex.normSq (W i₀ j₀) with hww
  -- final arithmetic
  have hcal : 0 ≤ Complex.normSq (ω + T) + d * (1 - A0 - B0) := by
    rcases hr.eq_or_lt with h0 | hpos
    · have hl1 : l = 1 := by linarith
      have hT0 : Complex.normSq T = 0 := by
        have : Complex.normSq T ≤ 0 := by rw [← h0] at hTcs; simpa using hTcs
        exact le_antisymm this (Complex.normSq_nonneg _)
      have hT00 : T = 0 := Complex.normSq_eq_zero.mp hT0
      rw [hT00, add_zero, hω]
      have : d = 1 := by rw [hd, hl1]; norm_num
      rw [this, hl1]; nlinarith
    · have hd0 : 0 ≤ d := by rw [hd]; linarith
      have hl0 : 0 < l := by linarith
      have key : l * ((1 - l) * Complex.normSq (ω + T) - (1 - l) * d * ww + d * Complex.normSq T)
          = Complex.normSq ((1 - l) • ω + l • T) := by
        simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.smul_re,
          Complex.smul_im, smul_eq_mul] at hω ⊢
        have hd' : d = l - (1 - l) := by rw [hd]; ring
        rw [hd']
        linear_combination ((1 - l) * (l - (1 - l))) * hω
      have h2 : 0 ≤ (1 - l) * Complex.normSq (ω + T) - (1 - l) * d * ww + d * Complex.normSq T := by
        have := Complex.normSq_nonneg ((1 - l) • ω + l • T)
        rw [← key] at this
        exact nonneg_of_mul_nonneg_right (by linarith) hl0
      have h3 : d * Complex.normSq T ≤ d * ((1 - l) * (1 - A0 - B0 + ww)) :=
        mul_le_mul_of_nonneg_left hTcs hd0
      have h4 : 0 ≤ (1 - l) * (Complex.normSq (ω + T) + d * (1 - A0 - B0)) := by nlinarith
      exact nonneg_of_mul_nonneg_right h4 hpos
  have : d ^ 2 = 2 * l * d - d := by rw [hd]; ring
  nlinarith [hfin, hcal]

end Core2

section General
open scoped ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem spectral_rdiag (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    ∃ (U : Matrix ι ι ℂ) (μ : ι → ℝ), U ∈ Matrix.unitaryGroup ι ℂ ∧ (∀ i, 0 ≤ μ i) ∧
      A = U * rdiag μ * Uᴴ := by
  have hH := hA.isHermitian
  refine ⟨((hH.eigenvectorUnitary : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ), hH.eigenvalues,
    (hH.eigenvectorUnitary).2, fun i => hA.eigenvalues_nonneg i, ?_⟩
  have := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at this
  have e : rdiag hH.eigenvalues = Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    unfold rdiag; rfl
  rw [e, Matrix.star_eq_conjTranspose] at *
  exact this

theorem unitary_mul_conjT {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) : U * Uᴴ = 1 := by
  have := Matrix.mem_unitaryGroup_iff.mp hU
  rwa [Matrix.star_eq_conjTranspose] at this

theorem unitary_conjT_mul {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) : Uᴴ * U = 1 := by
  have := Matrix.mem_unitaryGroup_iff'.mp hU
  rwa [Matrix.star_eq_conjTranspose] at this

theorem conjT_mem_unitary {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    Uᴴ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  exact unitary_conjT_mul hU

theorem rot_mul_conjT (U V A : Matrix ι ι ℂ) (hV : V * Vᴴ = 1) :
    (Uᴴ * A * V) * (Uᴴ * A * V)ᴴ = Uᴴ * (A * Aᴴ) * U := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc V, hV, Matrix.one_mul]

theorem rot_conjT_mul (U V A : Matrix ι ι ℂ) (hU : U * Uᴴ = 1) :
    (Uᴴ * A * V)ᴴ * (Uᴴ * A * V) = Vᴴ * (Aᴴ * A) * V := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U, hU, Matrix.one_mul]

theorem fn2_nonneg (A : Matrix ι ι ℂ) : 0 ≤ fn2 A :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

theorem fn2_conj_unitary (U A : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    fn2 (Uᴴ * A * U) = fn2 A := by
  have h1 := unitary_mul_conjT hU
  have h2 := fn2_eq_trace (Uᴴ * A * U)
  have h3 := fn2_eq_trace A
  rw [rot_mul_conjT U U A h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul] at h2
  exact_mod_cast h2.trans h3.symm

end General

section General2
open scoped ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem se_coord (μ : ι → ℝ) (hμ0 : ∀ i, 0 ≤ μ i) (hsum : ∑ i, μ i = 1) (a : ι → ℂ)
    (ha : a ≠ 0) (l : ℝ) (hl : 1 / 2 < l) (h : ∀ i, (μ i : ℂ) * a i = (l : ℂ) * a i) :
    ∃ i₀, μ i₀ = l ∧ a i₀ ≠ 0 ∧ (∀ i, i ≠ i₀ → a i = 0) ∧ ∀ i, μ i ≤ μ i₀ := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp ha
  have hμ : μ i₀ = l := by
    have := mul_right_cancel₀ hi₀ (h i₀)
    exact_mod_cast this
  have hsmall : ∀ i, i ≠ i₀ → μ i ≤ 1 - μ i₀ := by
    intro i hi
    have : μ i + μ i₀ ≤ ∑ k, μ k := by
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := μ) (s := {i, i₀})
        (t := Finset.univ) (Finset.subset_univ _) (fun k _ _ => hμ0 k)
      rwa [Finset.sum_pair hi] at this
    linarith
  refine ⟨i₀, hμ, hi₀, fun i hi => ?_, fun i => ?_⟩
  · have h1 := h i
    have h2 : (μ i : ℂ) ≠ (l : ℂ) := by
      have := hsmall i hi
      intro e
      have e' : μ i = l := by exact_mod_cast e
      linarith
    have h3 : ((μ i : ℂ) - l) * a i = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr h2)
  · by_cases hi : i = i₀
    · rw [hi]
    · have := hsmall i hi; linarith
end General2

section General3
open scoped ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fn2_conjT (A : Matrix ι ι ℂ) : fn2 Aᴴ = fn2 A := by
  unfold fn2
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.conjTranspose_apply, Complex.normSq_conj]

theorem rot_eq (U A D : Matrix ι ι ℂ) (hA : A = U * D * Uᴴ) (hU1 : Uᴴ * U = 1) :
    Uᴴ * A * U = D := by
  have : Uᴴ * A * U = (Uᴴ * U) * D * (Uᴴ * U) := by rw [hA]; simp only [Matrix.mul_assoc]
  rw [this, hU1, Matrix.one_mul, Matrix.mul_one]

/-- **Isospectral overlap lemma** (`lem:fqe-isospectral-overlap`), square case. -/
theorem isospectral_overlap (M W P Q : Matrix ι ι ℂ) (hM : fn2 M = 1)
    (hP : P ∈ Matrix.unitaryGroup ι ℂ) (hQ : Q ∈ Matrix.unitaryGroup ι ℂ)
    (hA : W * Wᴴ = P * (M * Mᴴ) * Pᴴ) (hB : Wᴴ * W = Q * (Mᴴ * M) * Qᴴ)
    (u : ι → ℂ) (hu : u ≠ 0) (l : ℝ) (hMu : (M * Mᴴ) *ᵥ u = (l : ℂ) • u) :
    (max (2 * l - 1) 0) ^ 2 ≤ Complex.normSq (Matrix.trace (Mᴴ * W))
      + (fn2 (M * Mᴴ - W * Wᴴ) + fn2 (Mᴴ * M - Wᴴ * W)) / 2 := by
  by_cases hl : l ≤ 1 / 2
  · rw [max_eq_right (by linarith)]
    have := fn2_nonneg (M * Mᴴ - W * Wᴴ)
    have := fn2_nonneg (Mᴴ * M - Wᴴ * W)
    have := Complex.normSq_nonneg (Matrix.trace (Mᴴ * W))
    nlinarith
  rw [not_le] at hl
  rw [max_eq_left (by linarith)]
  obtain ⟨U, μ, hU, hμ0, hXU⟩ := spectral_rdiag (M * Mᴴ) (Matrix.posSemidef_self_mul_conjTranspose M)
  obtain ⟨V, μ', hV, hμ'0, hXV⟩ := spectral_rdiag (Mᴴ * M) (Matrix.posSemidef_conjTranspose_mul_self M)
  have hU1 := unitary_conjT_mul hU
  have hU2 := unitary_mul_conjT hU
  have hV1 := unitary_conjT_mul hV
  have hV2 := unitary_mul_conjT hV
  have hsum : ∑ i, μ i = 1 := by
    rw [← fn2_of_mul_conjT M U hU μ hXU, hM]
  have hsum' : ∑ i, μ' i = 1 := by
    rw [← fn2_of_mul_conjT Mᴴ V hV μ' (by rw [Matrix.conjTranspose_conjTranspose]; exact hXV),
      fn2_conjT, hM]
  set N : Matrix ι ι ℂ := Uᴴ * M * V with hNdef
  have hNN : N * Nᴴ = rdiag μ := by
    rw [hNdef, rot_mul_conjT U V M hV2, rot_eq U _ _ hXU hU1]
  have hNN' : Nᴴ * N = rdiag μ' := by
    rw [hNdef, rot_conjT_mul U V M hU2, rot_eq V _ _ hXV hV1]
  have hl0 : (l : ℂ) ≠ 0 := by
    have : l ≠ 0 := by intro h; rw [h] at hl; norm_num at hl
    exact_mod_cast this
  -- the rotated eigenvector
  set a : ι → ℂ := Uᴴ *ᵥ u with hadef
  have ha0 : a ≠ 0 := by
    intro h
    apply hu
    have : U *ᵥ a = u := by rw [hadef, Matrix.mulVec_mulVec, hU2, Matrix.one_mulVec]
    rw [← this, h, Matrix.mulVec_zero]
  have hUX : Uᴴ * (M * Mᴴ) = rdiag μ * Uᴴ := by
    rw [hXU]
    calc Uᴴ * (U * rdiag μ * Uᴴ) = (Uᴴ * U) * rdiag μ * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU1, Matrix.one_mul]
  have hΛa : rdiag μ *ᵥ a = (l : ℂ) • a := by
    rw [hadef, Matrix.mulVec_mulVec, ← hUX, ← Matrix.mulVec_mulVec, hMu, Matrix.mulVec_smul]
  have hΛa' : ∀ i, (μ i : ℂ) * a i = (l : ℂ) * a i := by
    intro i
    have := congrFun hΛa i
    simpa [rdiag, Matrix.mulVec_diagonal] using this
  obtain ⟨i₀, hμi₀, hai₀, hai, hmax⟩ := se_coord μ hμ0 hsum a ha0 l hl hΛa'
  set b : ι → ℂ := Nᴴ *ᵥ a with hbdef
  have hNb : N *ᵥ b = (l : ℂ) • a := by
    rw [hbdef, Matrix.mulVec_mulVec, hNN, hΛa]
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, Matrix.mulVec_zero] at hNb
    have : (l : ℂ) • a = 0 := hNb.symm
    exact ha0 ((smul_eq_zero.mp this).resolve_left hl0)
  have hΛb : rdiag μ' *ᵥ b = (l : ℂ) • b := by
    rw [← hNN', ← Matrix.mulVec_mulVec, hNb, Matrix.mulVec_smul]
  have hΛb' : ∀ j, (μ' j : ℂ) * b j = (l : ℂ) * b j := by
    intro j
    have := congrFun hΛb j
    simpa [rdiag, Matrix.mulVec_diagonal] using this
  obtain ⟨j₀, hμj₀, hbj₀, hbj, hmax'⟩ := se_coord μ' hμ'0 hsum' b hb0 l hl hΛb'
  have hN2 : ∀ j, j ≠ j₀ → N i₀ j = 0 := by
    intro j hj
    have h1 : b j = 0 := hbj j hj
    have h2 : b j = star (N i₀ j) * a i₀ := by
      rw [hbdef, Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single i₀]
      · simp [Matrix.conjTranspose_apply]
      · intro i _ hi; simp [hai i hi]
      · simp
    rw [h2] at h1
    have := (mul_eq_zero.mp h1).resolve_right hai₀
    simpa using this
  have hN1 : ∀ i, i ≠ i₀ → N i j₀ = 0 := by
    intro i hi
    have h1 := congrFun hNb i
    have h2 : (N *ᵥ b) i = N i j₀ * b j₀ := by
      rw [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single j₀]
      · intro j _ hj; simp [hbj j hj]
      · simp
    rw [h2] at h1
    simp only [Pi.smul_apply, smul_eq_mul, hai i hi, mul_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_right hbj₀
  -- rotated W
  have hP' : Uᴴ * P * U ∈ Matrix.unitaryGroup ι ℂ :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ (conjT_mem_unitary hU) hP) hU
  have hQ' : Vᴴ * Q * V ∈ Matrix.unitaryGroup ι ℂ :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ (conjT_mem_unitary hV) hQ) hV
  have hWA : (Uᴴ * W * V) * (Uᴴ * W * V)ᴴ = (Uᴴ * P * U) * rdiag μ * (Uᴴ * P * U)ᴴ := by
    rw [rot_mul_conjT U V W hV2, hA, hXU]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hWB : (Uᴴ * W * V)ᴴ * (Uᴴ * W * V) = (Vᴴ * Q * V) * rdiag μ' * (Vᴴ * Q * V)ᴴ := by
    rw [rot_conjT_mul U V W hU2, hB, hXV]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hcore := core_overlap N (Uᴴ * W * V) (Uᴴ * P * U) (Vᴴ * Q * V) μ μ' i₀ j₀ hP' hQ' hμ0 hμ'0
    hsum hsum' hmax hmax' (by rw [hμj₀, hμi₀]) (by rw [hμi₀]; linarith) hNN hWA hWB hN1 hN2
  have e1 : fn2 (rdiag μ - (Uᴴ * W * V) * (Uᴴ * W * V)ᴴ) = fn2 (M * Mᴴ - W * Wᴴ) := by
    rw [rot_mul_conjT U V W hV2, ← hNN, hNdef, rot_mul_conjT U V M hV2, ← Matrix.sub_mul,
      ← Matrix.mul_sub, fn2_conj_unitary U _ hU]
  have e2 : fn2 (rdiag μ' - (Uᴴ * W * V)ᴴ * (Uᴴ * W * V)) = fn2 (Mᴴ * M - Wᴴ * W) := by
    rw [rot_conjT_mul U V W hU2, ← hNN', hNdef, rot_conjT_mul U V M hU2, ← Matrix.sub_mul,
      ← Matrix.mul_sub, fn2_conj_unitary V _ hV]
  have etr : Matrix.trace (Nᴴ * (Uᴴ * W * V)) = Matrix.trace (Mᴴ * W) := by
    rw [hNdef]
    have : (Uᴴ * M * V)ᴴ * (Uᴴ * W * V) = Vᴴ * (Mᴴ * W) * V := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U, hU2, Matrix.one_mul]
    rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV2, Matrix.one_mul]
  rw [e1, e2, etr, hμi₀] at hcore
  exact hcore
end General3

section General4
open scoped ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rdiag_map_conj (μ : ι → ℝ) : (rdiag μ).map (starRingEnd ℂ) = rdiag μ := by
  ext i j
  by_cases h : i = j
  · subst h; simp [rdiag]
  · simp [rdiag, Matrix.diagonal_apply, h]

theorem conjT_map_conj (U : Matrix ι ι ℂ) : Uᴴ.map (starRingEnd ℂ) = (U.map (starRingEnd ℂ))ᴴ := by
  ext i j
  simp [Matrix.conjTranspose_apply]

theorem map_conj_mem_unitary {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    U.map (starRingEnd ℂ) ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← conjT_map_conj,
    ← Matrix.map_mul, unitary_mul_conjT hU]
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

/-- Complex conjugation of a positive semidefinite matrix, composed with a unitary conjugation, is
unitarily equivalent to the matrix. -/
theorem conj_iso (X : Matrix ι ι ℂ) (hX : X.PosSemidef) (E : Matrix ι ι ℂ)
    (hE : E ∈ Matrix.unitaryGroup ι ℂ) :
    ∃ P ∈ Matrix.unitaryGroup ι ℂ, E * X.map (starRingEnd ℂ) * Eᴴ = P * X * Pᴴ := by
  obtain ⟨U, μ, hU, hμ0, hXU⟩ := spectral_rdiag X hX
  have hU1 := unitary_conjT_mul hU
  have hb : X.map (starRingEnd ℂ) = U.map (starRingEnd ℂ) * rdiag μ * (U.map (starRingEnd ℂ))ᴴ := by
    conv_lhs => rw [hXU]
    rw [Matrix.map_mul, Matrix.map_mul, rdiag_map_conj, conjT_map_conj]
  refine ⟨E * U.map (starRingEnd ℂ) * Uᴴ,
    Submonoid.mul_mem _ (Submonoid.mul_mem _ hE (map_conj_mem_unitary hU)) (conjT_mem_unitary hU), ?_⟩
  rw [hb]
  conv_rhs => rw [hXU]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hc : ∀ Y : Matrix ι ι ℂ, Uᴴ * (U * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hU1, Matrix.one_mul]
  simp only [hc]
end General4

section General5
open scoped ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Overlap bound for `ψ` against `W = E ψ̄ F` (an antiunitary image). -/
theorem antiunitary_overlap (M E F : Matrix ι ι ℂ) (hM : fn2 M = 1)
    (hE : E ∈ Matrix.unitaryGroup ι ℂ) (hF : F ∈ Matrix.unitaryGroup ι ℂ)
    (u : ι → ℂ) (hu : u ≠ 0) (l : ℝ) (hMu : (M * Mᴴ) *ᵥ u = (l : ℂ) • u) :
    (max (2 * l - 1) 0) ^ 2 ≤
      Complex.normSq (Matrix.trace (Mᴴ * (E * M.map (starRingEnd ℂ) * F)))
      + (fn2 (M * Mᴴ - (E * M.map (starRingEnd ℂ) * F) * (E * M.map (starRingEnd ℂ) * F)ᴴ)
        + fn2 (Mᴴ * M - (E * M.map (starRingEnd ℂ) * F)ᴴ * (E * M.map (starRingEnd ℂ) * F))) / 2 := by
  have hF1 := unitary_mul_conjT hF
  have hE1 := unitary_conjT_mul hE
  obtain ⟨P, hP, hPe⟩ := conj_iso (M * Mᴴ) (Matrix.posSemidef_self_mul_conjTranspose M) E hE
  obtain ⟨Q, hQ, hQe⟩ := conj_iso (Mᴴ * M) (Matrix.posSemidef_conjTranspose_mul_self M) Fᴴ
    (conjT_mem_unitary hF)
  refine isospectral_overlap M _ P Q hM hP hQ ?_ ?_ u hu l hMu
  · rw [← hPe]
    have : (M * Mᴴ).map (starRingEnd ℂ) = M.map (starRingEnd ℂ) * (M.map (starRingEnd ℂ))ᴴ := by
      rw [Matrix.map_mul, conjT_map_conj]
    rw [this]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F, hF1, Matrix.one_mul]
  · rw [← Matrix.conjTranspose_conjTranspose F] at hQe
    rw [Matrix.conjTranspose_conjTranspose] at hQe
    rw [← hQe]
    have : (Mᴴ * M).map (starRingEnd ℂ) = (M.map (starRingEnd ℂ))ᴴ * M.map (starRingEnd ℂ) := by
      rw [Matrix.map_mul, conjT_map_conj]
    rw [this]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    have hc : ∀ Y : Matrix ι ι ℂ, Eᴴ * (E * Y) = Y := fun Y => by
      rw [← Matrix.mul_assoc, hE1, Matrix.one_mul]
    rw [hc]
end General5

end FormalResearch.FourQubitEntropy.Isospectral
