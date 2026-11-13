module

public import FormalResearch.Racah.P2RacahSystemOp
public import FormalResearch.Racah.P2RacahSystemOrth

/-!
# The orthonormal eigenbasis of `H_R` (Weyl P2, `thm:6jfiniteRacah`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `eq:RacahEigenvectors`, `eq:RacahPhiOrthogonality`,
`eq:RacahPhiCompleteness`, `eq:RacahSpectrum`.

Notation of `P2RacahSystemOp`: `D + 1 = |𝒞|`, `c_i = c_min + i`, `f_j = f_0 + j` (`i, j : Fin (D+1)`; the
number of physical `f` equals the number of physical `c` by `eq:Racahdimension`), `ω_i = wgtR`,
`H_R = HR`.  The vectors are `v_j(i) = √((2f_j+1)/2) Φ_{f_j}(c_i)` (`vR`, `eq:RacahEigenvectors`).

## Results

* `vR_eigen`: `H_R v_j = f_j(f_j+1) v_j` (all rows, including both end rows and the `c = 0` row).
* `vR_orthonormal`: `⟨v_j, v_l⟩_ω = δ_{jl}` (from `Phi6_orthogonality`, i.e. DLMF 34.5.14).
* `Phi6_completeness`: `eq:RacahPhiCompleteness`,
  `∑_j (2f_j+1)/2 Φ_{f_j}(c_i) Φ_{f_j}(c_{i'}) = δ_{ii'} / ω_i`
  (the `D+1` orthonormal vectors span the `(D+1)`-dimensional space).
* `HR_spectrum`, `HR_eigenspace`: the eigenvalues of `H_R` are exactly `f_j(f_j+1)`, each simple
  (`eq:RacahSpectrum`).
-/

@[expose] public section

namespace FormalResearch.Racah.SixJ

open FormalResearch.Wigner

lemma cPt_mem {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (i : Fin (D + 1)) :
    cPt a b m n i ∈ physC a b m n := by
  rw [mem_physC_iff h.labels]
  refine ⟨i, ?_, rfl⟩
  have h1 := h.dim
  have h2 : ((i : ℕ) : ℚ) ≤ D := by exact_mod_cast Nat.lt_succ_iff.1 i.2
  linarith

lemma fPt_mem {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (j : Fin (D + 1)) :
    fPt m n j ∈ physF a b m n := by
  rw [mem_physF_iff h.labels]
  refine ⟨j, ?_, rfl⟩
  have h1 := h.dim
  have h3 := cMax_sub_cMin a b m n
  have h2 : ((j : ℕ) : ℚ) ≤ D := by exact_mod_cast Nat.lt_succ_iff.1 j.2
  linarith

/-- The `i`-th row of `H_R Φ_f = f(f+1) Φ_f` with the zero extension of `Φ` outside the lattice,
at the physical rank `f_j` (`Phi6_lattice_eigen` for `c > 0`, `Phi6_lattice_row_zero` for `c = 0`). -/
lemma Phi6_row {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (i j : Fin (D + 1)) :
    (fPt m n j : ℝ) * ((fPt m n j : ℝ) + 1) * Phi6 a b (cPt a b m n i) (fPt m n j) m n =
      -(aPlus a b m n (cPt a b m n i) * Phi6 a b (cPt a b m n i + 1) (fPt m n j) m n) +
        bRow (wA a n) (wB b m) m n (cPt a b m n i) * Phi6 a b (cPt a b m n i) (fPt m n j) m n -
        aMinus a b m n (cPt a b m n i) * Phi6 a b (cPt a b m n i - 1) (fPt m n j) m n := by
  have hcm := cPt_mem h i
  have hfm := fPt_mem h j
  have hcn := cPt_nonneg a b m n i
  generalize cPt a b m n i = c at hcm hcn ⊢
  generalize fPt m n j = f at hfm ⊢
  by_cases hc0 : c = 0
  · subst hc0
    have := Phi6_lattice_row_zero a b f m n hcm.1 hcm.2 hfm.1
    simp only [bRow, Rat.cast_zero, ite_true, zero_add, zero_sub] at this ⊢
    have hz : aMinus a b m n 0 = 0 := by simp [aMinus]
    rw [hz]
    simpa using this
  · have hpos : 0 < c := lt_of_le_of_ne (by exact_mod_cast hcn) (Ne.symm hc0)
    have hne : (c : ℝ) ≠ 0 := by exact_mod_cast hc0
    have := Phi6_lattice_eigen a b c f m n hpos hcm.1 hcm.2
    simp only [bRow, hne, ite_false]
    exact this

/-- **`eq:RacahEigenvectors`**: the vectors `v_j(i) = √((2f_j+1)/2) Φ_{f_j}(c_i)`. -/
noncomputable def vR (a b m n : ℚ) {D : ℕ} (j : Fin (D + 1)) : Fin (D + 1) → ℝ :=
  fun i => Real.sqrt ((2 * (fPt m n j : ℝ) + 1) / 2) * Phi6 a b (cPt a b m n i) (fPt m n j) m n

lemma fPt_nonneg (m n : ℚ) {D : ℕ} (j : Fin (D + 1)) : (0 : ℝ) ≤ (fPt m n j : ℝ) := by
  have h1 : (0 : ℚ) ≤ fPt m n j := by
    unfold fPt
    have : 0 ≤ fMin m n := le_max_of_le_left (abs_nonneg _)
    positivity
  exact_mod_cast h1

lemma fPt_injective (m n : ℚ) {D : ℕ} : Function.Injective (fun j : Fin (D + 1) => fPt m n j) := by
  intro i j hij
  have : ((i : ℕ) : ℚ) = (j : ℕ) := by
    have := hij
    simp only [fPt] at this
    linarith
  exact Fin.ext (by exact_mod_cast this)

lemma aPlus_top {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (i : Fin (D + 1))
    (hi : ¬ (i : ℕ) + 1 < D + 1) : aPlus a b m n (cPt a b m n i) = 0 := by
  have hiD : (i : ℕ) = D := by have := i.2; omega
  have hc : cPt a b m n i = cMax a b m n := by
    unfold cPt
    have := h.dim
    rw [hiD]; linarith
  unfold aPlus
  rw [hc, edgeA_cMax_succ]
  simp

lemma aMinus_bottom {a b m n : ℚ} {D : ℕ} (i : Fin (D + 1)) (hi : ¬ 0 < (i : ℕ)) :
    aMinus a b m n (cPt a b m n i) = 0 := by
  have hi0 : (i : ℕ) = 0 := by omega
  have hc : cPt a b m n i = cMin a b m n := by
    unfold cPt; rw [hi0]; simp
  unfold aMinus
  rw [hc, edgeA_cMin]
  simp

/-- **`eq:RacahEigenvectors`**: `H_R v_f = f(f+1) v_f` for every physical `f`, all rows
(including `c_min`, `c_max`, and the `c = 0` row). -/
theorem vR_eigen {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (j : Fin (D + 1)) :
    (HR a b m n D).mulVec (vR a b m n j) =
      ((fPt m n j : ℝ) * ((fPt m n j : ℝ) + 1)) • vR a b m n j := by
  ext i
  rw [HR_mulVec]
  have hrow := Phi6_row h i j
  simp only [Pi.smul_apply, smul_eq_mul, vR]
  set κ := Real.sqrt ((2 * (fPt m n j : ℝ) + 1) / 2) with hκ
  have hup : aPlus a b m n (cPt a b m n i) *
      (if hh : (i : ℕ) + 1 < D + 1 then
        κ * Phi6 a b (cPt a b m n ⟨(i : ℕ) + 1, hh⟩) (fPt m n j) m n else 0) =
      κ * (aPlus a b m n (cPt a b m n i) * Phi6 a b (cPt a b m n i + 1) (fPt m n j) m n) := by
    by_cases hh : (i : ℕ) + 1 < D + 1
    · simp only [hh, ↓reduceDIte]
      have : cPt a b m n ⟨(i : ℕ) + 1, hh⟩ = cPt a b m n i + 1 := by
        unfold cPt; push_cast; ring
      rw [this]; ring
    · simp only [hh, ↓reduceDIte]
      rw [aPlus_top h i hh]; ring
  have hlo : aMinus a b m n (cPt a b m n i) *
      (if hh : 0 < (i : ℕ) then
        κ * Phi6 a b (cPt (D := D) a b m n ⟨(i : ℕ) - 1, by omega⟩) (fPt m n j) m n else 0) =
      κ * (aMinus a b m n (cPt a b m n i) * Phi6 a b (cPt a b m n i - 1) (fPt m n j) m n) := by
    by_cases hh : 0 < (i : ℕ)
    · simp only [hh, ↓reduceDIte]
      have : cPt (D := D) a b m n ⟨(i : ℕ) - 1, by omega⟩ = cPt a b m n i - 1 := by
        unfold cPt
        have : (((i : ℕ) - 1 : ℕ) : ℚ) = (i : ℕ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        simp only [this]; ring
      rw [this]; ring
    · simp only [hh, ↓reduceDIte]
      rw [aMinus_bottom i hh]; ring
  rw [hup, hlo]
  linear_combination (-κ) * hrow

/-- A sum over the indexed lattice is the sum over the physical lattice `𝒞 = physC a b m n`. -/
lemma sum_fin_eq_finsum {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (F : ℚ → ℝ) :
    ∑ i : Fin (D + 1), F (cPt a b m n i) = ∑ᶠ c ∈ physC a b m n, F c := by
  have hinj : Function.Injective (fun i : ℕ => cMin a b m n + (i : ℚ)) := by
    intro i j hij
    have : (i : ℚ) = j := by simpa using hij
    exact_mod_cast this
  have hset : {i : ℕ | (i : ℚ) ≤ cMax a b m n - cMin a b m n} = ↑(Finset.range (D + 1)) := by
    ext i
    simp only [Set.mem_ofPred_eq, Finset.coe_range, Set.mem_Iio]
    rw [Nat.lt_succ_iff, ← h.dim]
    exact_mod_cast Iff.rfl
  rw [physC_eq_image h.labels, finsum_mem_image hinj.injOn, hset, finsum_mem_coe_finset,
    Finset.sum_range (fun i => F (cMin a b m n + (i : ℚ)))]
  rfl

/-- **`eq:RacahPhiOrthogonality`** in the matrix form `⟨v_j, v_l⟩_ω = δ_{jl}`
(**orthonormality of the eigenbasis** `eq:RacahEigenvectors`). -/
theorem vR_orthonormal {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (j l : Fin (D + 1)) :
    ipR a b m n (vR a b m n j) (vR a b m n l) = if j = l then 1 else 0 := by
  have horth := Phi6_orthogonality (fPt_mem h j) (fPt_mem h l)
  rw [← sum_fin_eq_finsum h (fun c => omegaW (wA a n) (wB b m) c *
    (Phi6 a b c (fPt m n j) m n * Phi6 a b c (fPt m n l) m n))] at horth
  have hj0 := fPt_nonneg m n j
  have hpos : 0 < 2 * (fPt m n j : ℝ) + 1 := by linarith
  have hsum : ipR a b m n (vR a b m n j) (vR a b m n l) =
      Real.sqrt ((2 * (fPt m n j : ℝ) + 1) / 2) * Real.sqrt ((2 * (fPt m n l : ℝ) + 1) / 2) *
        ∑ i : Fin (D + 1), omegaW (wA a n) (wB b m) (cPt a b m n i) *
          (Phi6 a b (cPt a b m n i) (fPt m n j) m n * Phi6 a b (cPt a b m n i) (fPt m n l) m n) := by
    unfold ipR vR wgtR
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum, horth]
  by_cases hjl : j = l
  · subst hjl
    simp only [ite_true]
    rw [Real.mul_self_sqrt (by positivity)]
    field_simp
  · have : fPt m n j ≠ fPt m n l := fun e => hjl (fPt_injective m n e)
    simp [hjl, this]

/-- The matrix `U` of the eigenvectors (`U_{ij} = v_j(i)`) and the weight matrix `W = diag ω`. -/
noncomputable def UR (a b m n : ℚ) (D : ℕ) : Matrix (Fin (D + 1)) (Fin (D + 1)) ℝ :=
  Matrix.of fun i j => vR a b m n j i

/-- `Uᵀ W U = 1` (orthonormality in matrix form). -/
lemma UR_gram {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) :
    (Matrix.transpose (UR a b m n D) * Matrix.diagonal (wgtR a b m n)) * UR a b m n D = 1 := by
  ext j l
  have e := vR_orthonormal h j l
  unfold ipR at e
  rw [Matrix.one_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, UR, Matrix.of_apply]
  rw [← e]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The `(D+1)` orthonormal vectors span: `∑_j v_j(i) v_j(i') ω_{i'} = δ_{ii'}`
(`U Uᵀ W = 1` from `Uᵀ W U = 1`, a square matrix identity). -/
theorem vR_complete_aux {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (i i' : Fin (D + 1)) :
    ∑ j, vR a b m n j i * vR a b m n j i' * wgtR a b m n i' = if i = i' then 1 else 0 := by
  have hG' := mul_eq_one_comm.1 (UR_gram h)
  have := congrFun (congrFun hG' i) i'
  rw [Matrix.one_apply, Matrix.mul_apply] at this
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, UR, Matrix.of_apply] at this
  rw [← this]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- **`eq:RacahPhiCompleteness`**:
`∑_{f} (2f+1)/2 Φ_f(c) Φ_f(c') = δ_{cc'} / ω_c`, the sum over the physical `f`-range
`f_j = f_0 + j`, `j = 0, ..., D`, and `c = c_i`, `c' = c_{i'}`. -/
theorem Phi6_completeness {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (i i' : Fin (D + 1)) :
    ∑ j : Fin (D + 1), ((2 * (fPt m n j : ℝ) + 1) / 2) *
        (Phi6 a b (cPt a b m n i) (fPt m n j) m n * Phi6 a b (cPt a b m n i') (fPt m n j) m n) =
      if i = i' then (wgtR a b m n i)⁻¹ else 0 := by
  have haux := vR_complete_aux h i i'
  have hw := wgtR_pos h i'
  have hS : ∑ j, vR a b m n j i * vR a b m n j i' * wgtR a b m n i' =
      wgtR a b m n i' * ∑ j : Fin (D + 1), ((2 * (fPt m n j : ℝ) + 1) / 2) *
        (Phi6 a b (cPt a b m n i) (fPt m n j) m n * Phi6 a b (cPt a b m n i') (fPt m n j) m n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hj0 := fPt_nonneg m n j
    have := Real.mul_self_sqrt (show 0 ≤ (2 * (fPt m n j : ℝ) + 1) / 2 by linarith)
    unfold vR
    calc _ = (Real.sqrt ((2 * (fPt m n j : ℝ) + 1) / 2) * Real.sqrt ((2 * (fPt m n j : ℝ) + 1) / 2)) *
          (Phi6 a b (cPt a b m n i) (fPt m n j) m n * Phi6 a b (cPt a b m n i') (fPt m n j) m n) *
          wgtR a b m n i' := by ring
      _ = _ := by rw [this]; ring
  rw [hS] at haux
  by_cases hii : i = i'
  · subst hii
    simp only [ite_true] at haux ⊢
    exact eq_inv_of_mul_eq_one_right haux
  · simp only [hii, ite_false] at haux ⊢
    rcases mul_eq_zero.1 haux with h0 | h0
    · exact absurd h0 hw.ne'
    · exact h0

lemma ipR_smul_right (a b m n : ℚ) {D : ℕ} (t : ℝ) (x y : Fin (D + 1) → ℝ) :
    ipR a b m n x (t • y) = t * ipR a b m n x y := by
  simp only [ipR, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; ring

lemma ipR_smul_left (a b m n : ℚ) {D : ℕ} (t : ℝ) (x y : Fin (D + 1) → ℝ) :
    ipR a b m n (t • x) y = t * ipR a b m n x y := by
  simp only [ipR, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; ring

/-- Expansion in the eigenbasis (a consequence of completeness): `q = ∑_j ⟨v_j, q⟩_ω v_j`. -/
theorem vR_expansion {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (q : Fin (D + 1) → ℝ) :
    q = ∑ j, (ipR a b m n (vR a b m n j) q) • vR a b m n j := by
  funext i'
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ipR]
  have e1 : ∀ j, (∑ i, wgtR a b m n i * (vR a b m n j i * q i)) * vR a b m n j i' =
      ∑ i, q i * (vR a b m n j i' * vR a b m n j i * wgtR a b m n i) := by
    intro j
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [Finset.sum_congr rfl (fun j _ => e1 j), Finset.sum_comm]
  simp_rw [← Finset.mul_sum, vR_complete_aux h i']
  simp

lemma vR_ipR_self {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (j : Fin (D + 1)) :
    ipR a b m n (vR a b m n j) (vR a b m n j) = 1 := by
  simpa using vR_orthonormal h j j

/-- The eigenvalue `f_j(f_j+1)`. -/
noncomputable def lamR (m n : ℚ) {D : ℕ} (j : Fin (D + 1)) : ℝ :=
  (fPt m n j : ℝ) * ((fPt m n j : ℝ) + 1)

lemma lamR_injective (m n : ℚ) {D : ℕ} : Function.Injective (lamR m n (D := D)) := by
  intro j l hjl
  have hj := fPt_nonneg m n j
  have hl := fPt_nonneg m n l
  unfold lamR at hjl
  have : (fPt m n j : ℝ) = fPt m n l := by nlinarith
  exact fPt_injective m n (by exact_mod_cast this)

/-- Pairing with an eigenvector: `(μ - f_j(f_j+1)) ⟨v_j, q⟩_ω = 0` if `H_R q = μ q`. -/
lemma pairing_eq {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (j : Fin (D + 1))
    (q : Fin (D + 1) → ℝ) (μ : ℝ) (hq : (HR a b m n D).mulVec q = μ • q) :
    (μ - lamR m n j) * ipR a b m n (vR a b m n j) q = 0 := by
  have := HR_selfadjoint h (vR a b m n j) q
  rw [hq, vR_eigen h j, ipR_smul_right, ipR_smul_left] at this
  unfold lamR
  linarith

/-- **`eq:RacahSpectrum`**: the eigenvalues of `H_R` are exactly `f(f+1)`, `f` in the physical
`f`-range. -/
theorem HR_spectrum {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (μ : ℝ) :
    (∃ q : Fin (D + 1) → ℝ, q ≠ 0 ∧ (HR a b m n D).mulVec q = μ • q) ↔
      ∃ j : Fin (D + 1), μ = lamR m n j := by
  constructor
  · rintro ⟨q, hq0, hq⟩
    by_contra hno
    push Not at hno
    apply hq0
    have hr : ∀ j, ipR a b m n (vR a b m n j) q = 0 := by
      intro j
      rcases mul_eq_zero.1 (pairing_eq h j q μ hq) with h0 | h0
      · exact absurd (by linarith) (hno j)
      · exact h0
    rw [vR_expansion h q]
    simp [hr]
  · rintro ⟨j, rfl⟩
    refine ⟨vR a b m n j, ?_, vR_eigen h j⟩
    intro h0
    have := vR_ipR_self h j
    rw [h0] at this
    simp [ipR] at this

/-- **Simplicity of the spectrum**: each eigenspace of `H_R` is one-dimensional, spanned by `v_j`. -/
theorem HR_eigenspace {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (j : Fin (D + 1))
    (q : Fin (D + 1) → ℝ) (hq : (HR a b m n D).mulVec q = lamR m n j • q) :
    ∃ t : ℝ, q = t • vR a b m n j := by
  refine ⟨ipR a b m n (vR a b m n j) q, ?_⟩
  conv_lhs => rw [vR_expansion h q]
  rw [Finset.sum_eq_single j]
  · intro l _ hlj
    have := pairing_eq h l q (lamR m n j) hq
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd (lamR_injective m n (by linarith)) (Ne.symm hlj)
    · rw [h0]; simp
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- `H_R U = U diag(f_j(f_j+1))`. -/
lemma HR_mul_UR {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) :
    HR a b m n D * UR a b m n D = UR a b m n D * Matrix.diagonal (lamR m n (D := D)) := by
  ext i j
  have := congrFun (vR_eigen h j) i
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simp only [UR, Matrix.of_apply]
  rw [show (∑ k, HR a b m n D i k * vR a b m n j k) = (HR a b m n D).mulVec (vR a b m n j) i from rfl,
    this]
  simp [lamR]
  ring

/-- **Simple spectrum, multiplicities included**: the characteristic polynomial of `H_R` is
`∏_f (X - f(f+1))` over the physical `f`-range. -/
theorem HR_charpoly {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) :
    (HR a b m n D).charpoly = ∏ j : Fin (D + 1), (Polynomial.X - Polynomial.C (lamR m n j)) := by
  have hdet : IsUnit (UR a b m n D).det := by
    have := congrArg Matrix.det (UR_gram h)
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact isUnit_iff_ne_zero.2 (right_ne_zero_of_mul_eq_one this)
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hdet
  have hH : HR a b m n D = u.val * Matrix.diagonal (lamR m n (D := D)) * u.val⁻¹ := by
    rw [hu, ← HR_mul_UR h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  rw [hH, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]

/-- info: 'FormalResearch.Racah.SixJ.vR_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vR_eigen

/-- info: 'FormalResearch.Racah.SixJ.vR_orthonormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vR_orthonormal

/-- info: 'FormalResearch.Racah.SixJ.Phi6_completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_completeness

/-- info: 'FormalResearch.Racah.SixJ.HR_spectrum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HR_spectrum

/-- info: 'FormalResearch.Racah.SixJ.HR_eigenspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HR_eigenspace

/-- info: 'FormalResearch.Racah.SixJ.HR_charpoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HR_charpoly

end FormalResearch.Racah.SixJ
