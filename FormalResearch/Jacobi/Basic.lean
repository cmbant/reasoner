module

public import Mathlib

/-!
# Finite Jacobi matrices: eigen-equation, three-term recurrence, eigenvalues as roots

Generic, elementary finite-Jacobi-matrix library (the shared base of the Weyl P5/M7 notes
`m7_review_and_open_gates.md` §B (Theorem ER) and `dirichlet_block_audit.md` (SP.1, DB.1)).

A real symmetric `n × n` Jacobi matrix is determined by a diagonal `b : ℕ → ℝ` and an
off-diagonal `a : ℕ → ℝ`, where `a j` joins the sites `j` and `j+1`; only `b 0 … b (n-1)` and
`a 0 … a (n-2)` enter.

* `jacobiMatrix n b a` : the matrix; `jacobiMatrix_isSymm`.
* `jacP b a j` : the monic polynomial `P_j` of the leading `j × j` block (defined by the recurrence
  `P_{j+2} = (X - b_{j+1}) P_{j+1} - a_j² P_j`, `P_0 = 1`, `P_1 = X - b_0`); `jacP_monic`,
  `jacP_natDegree`.
* `jacobiMatrix_mulVec` : `(J v)_j = a_{j-1} v_{j-1} + b_j v_j + a_j v_{j+1}` (vectors extended by zero).
* `eigen_prod_eq` : for an eigenvector, `u_j ∏_{i<j} a_i = u_0 P_j(λ)` (the recurrence, no
  nonvanishing hypothesis).
* `jacobi_isEigenval_iff` : for nonzero links, `λ` is an eigenvalue of `J_n` iff `P_n(λ) = 0`;
  every eigenvector has `u_0 ≠ 0` and every eigenspace is a line (`jacobi_eigenvec_unique`).
* `jacobi_eigenvec_eq` : **Theorem ER (eigenvector reconstruction by the recurrence)**, general
  form: an eigenvector with `u_0 = 1` is `u_j = P_j(λ) / ∏_{i<j} a_i`.

Claim class: proved (elementary algebra).  Not formalised: the physical instantiation (Racah
`6j` matrix entries, R0(d) border parity); see `FormalResearch.Jacobi.Reconstruction`.
-/

@[expose] public section

namespace FormalResearch.Jacobi

open Matrix Polynomial Finset

/-- The real symmetric `n × n` Jacobi matrix with diagonal `b` and off-diagonal `a`
(`a j` joins `j` and `j+1`). -/
def jacobiMatrix (n : ℕ) (b a : ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if i = j then b i else if (i : ℕ) + 1 = j then a i else if (j : ℕ) + 1 = i then a j else 0

theorem jacobiMatrix_isSymm (n : ℕ) (b a : ℕ → ℝ) : (jacobiMatrix n b a).IsSymm := by
  ext i j
  simp only [jacobiMatrix, Matrix.transpose_apply, Matrix.of_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : ¬ j = i := fun e => h e.symm
    simp only [h, h', ite_false]
    by_cases h1 : (i : ℕ) + 1 = j
    · have : ¬ (j : ℕ) + 1 = i := by omega
      simp [h1, this]
    · by_cases h2 : (j : ℕ) + 1 = i
      · simp [h1, h2]
      · simp [h1, h2]

/-- The monic characteristic-type polynomials of the leading blocks of a Jacobi matrix. -/
noncomputable def jacP (b a : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X - C (b 0)
  | (j + 2) => (X - C (b (j + 1))) * jacP b a (j + 1) - C (a j ^ 2) * jacP b a j

@[simp] theorem jacP_zero (b a : ℕ → ℝ) : jacP b a 0 = 1 := rfl
@[simp] theorem jacP_one (b a : ℕ → ℝ) : jacP b a 1 = X - C (b 0) := rfl
theorem jacP_succ_succ (b a : ℕ → ℝ) (j : ℕ) :
    jacP b a (j + 2) = (X - C (b (j + 1))) * jacP b a (j + 1) - C (a j ^ 2) * jacP b a j := rfl

/-- `P_j` is monic of degree `j`. -/
theorem jacP_monic_natDegree (b a : ℕ → ℝ) :
    ∀ j, (jacP b a j).Monic ∧ (jacP b a j).natDegree = j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => simp
    | 1, _ => simp [monic_X_sub_C]
    | (j + 2), ih =>
      obtain ⟨h1, h1d⟩ := ih (j + 1) (by omega)
      obtain ⟨h0, h0d⟩ := ih j (by omega)
      have hmul : ((X - C (b (j + 1))) * jacP b a (j + 1)).Monic := (monic_X_sub_C _).mul h1
      have hmuld : ((X - C (b (j + 1))) * jacP b a (j + 1)).natDegree = j + 2 := by
        rw [(monic_X_sub_C _).natDegree_mul h1, natDegree_X_sub_C, h1d]; ring
      have hlt : (C (a j ^ 2) * jacP b a j).degree <
          ((X - C (b (j + 1))) * jacP b a (j + 1)).degree := by
        apply degree_lt_degree
        rw [hmuld]
        have := natDegree_C_mul_le (a j ^ 2) (jacP b a j)
        omega
      refine ⟨hmul.sub_of_left hlt, ?_⟩
      rw [jacP_succ_succ, natDegree_sub_eq_left_of_natDegree_lt]
      · exact hmuld
      · rw [hmuld]
        refine lt_of_le_of_lt (natDegree_C_mul_le _ _) ?_
        omega

theorem jacP_monic (b a : ℕ → ℝ) (j : ℕ) : (jacP b a j).Monic := (jacP_monic_natDegree b a j).1
theorem jacP_natDegree (b a : ℕ → ℝ) (j : ℕ) : (jacP b a j).natDegree = j :=
  (jacP_monic_natDegree b a j).2

/-- Extension of a vector on `Fin n` by zero to `ℕ`. -/
def extVec {n : ℕ} (v : Fin n → ℝ) : ℕ → ℝ := fun i => if h : i < n then v ⟨i, h⟩ else 0

theorem extVec_of_lt {n : ℕ} (v : Fin n → ℝ) {i : ℕ} (h : i < n) : extVec v i = v ⟨i, h⟩ := by
  simp [extVec, h]

theorem extVec_of_ge {n : ℕ} (v : Fin n → ℝ) {i : ℕ} (h : n ≤ i) : extVec v i = 0 := by
  simp [extVec, not_lt.mpr h]

/-- The `j`-th row of the Jacobi eigen-equation applied to a sequence `u`. -/
def jacRow (b a u : ℕ → ℝ) (j : ℕ) : ℝ :=
  (if j = 0 then 0 else a (j - 1) * u (j - 1)) + b j * u j + a j * u (j + 1)

/-- `(J v)_j = a_{j-1} v_{j-1} + b_j v_j + a_j v_{j+1}` with vectors extended by zero. -/
theorem jacobiMatrix_mulVec {n : ℕ} (b a : ℕ → ℝ) (v : Fin n → ℝ) (j : Fin n) :
    (jacobiMatrix n b a *ᵥ v) j = jacRow b a (extVec v) j := by
  have hj := j.2
  simp only [mulVec, dotProduct, jacobiMatrix, Matrix.of_apply]
  have hF : ∀ k : Fin n, (if j = k then b j else if (j : ℕ) + 1 = k then a j
      else if (k : ℕ) + 1 = j then a k else 0) * v k = (fun k : ℕ => (if (j : ℕ) = k then b j
      else if (j : ℕ) + 1 = k then a j else if k + 1 = (j : ℕ) then a k else 0) * extVec v k) k := by
    intro k
    have h := extVec_of_lt v k.2
    rw [Fin.eta] at h
    show _ = (_ : ℝ) * extVec v k
    rw [h]
    exact congrArg (· * v k) (if_congr Fin.ext_iff rfl rfl)
  rw [sum_congr rfl (fun k _ => hF k),
    Fin.sum_univ_eq_sum_range (fun k : ℕ => (if (j : ℕ) = k then b j else if (j : ℕ) + 1 = k then a j
      else if k + 1 = (j : ℕ) then a k else 0) * extVec v k) n]
  · have hterm : ∀ k ∈ range n, (if (j : ℕ) = k then b j else if (j : ℕ) + 1 = k then a j
        else if k + 1 = (j : ℕ) then a k else 0) * extVec v k =
        (if k = (j : ℕ) then b j * extVec v k else 0) +
        (if k = (j : ℕ) + 1 then a j * extVec v k else 0) +
        (if k + 1 = (j : ℕ) then a k * extVec v k else 0) := by
      intro k _
      by_cases h1 : (j : ℕ) = k
      · subst h1
        simp
      · by_cases h5 : (j : ℕ) + 1 = k
        · subst h5
          have : ¬ (j : ℕ) + 1 + 1 = j := by omega
          simp [this]
        · by_cases h6 : k + 1 = (j : ℕ)
          · have h2 : ¬ k = (j : ℕ) := by omega
            have h3 : ¬ k = (j : ℕ) + 1 := by omega
            simp [h1, h5, h6, h2, h3]
          · have h2 : ¬ k = (j : ℕ) := fun e => h1 e.symm
            have h3 : ¬ k = (j : ℕ) + 1 := fun e => h5 e.symm
            simp [h1, h5, h6, h2, h3]
    rw [sum_congr rfl hterm, sum_add_distrib, sum_add_distrib]
    simp only [sum_ite_eq', mem_range, hj, ite_true]
    have hs : ∑ k ∈ range n, (if k + 1 = (j : ℕ) then a k * extVec v k else 0) =
        if (j : ℕ) = 0 then 0 else a ((j : ℕ) - 1) * extVec v ((j : ℕ) - 1) := by
      by_cases h0 : (j : ℕ) = 0
      · simp only [h0, ite_true]
        apply sum_eq_zero
        intro k _
        simp
      · simp only [h0, ite_false]
        rw [sum_eq_single ((j : ℕ) - 1)]
        · have : (j : ℕ) - 1 + 1 = j := by omega
          simp [this]
        · intro k _ hk
          have : ¬ k + 1 = (j : ℕ) := by omega
          simp [this]
        · intro hk
          exact absurd (mem_range.mpr (by omega)) hk
    rw [hs]
    unfold jacRow
    by_cases h1 : (j : ℕ) + 1 < n
    · simp [h1]; ring
    · rw [extVec_of_ge v (by omega : n ≤ (j : ℕ) + 1)]
      simp [h1]; ring

/-- The recurrence: for an eigen-sequence `u` of the first `n` rows,
`u_j ∏_{i<j} a_i = u_0 P_j(λ)` for every `j ≤ n`. -/
theorem eigen_prod_eq (n : ℕ) (b a u : ℕ → ℝ) (lam : ℝ)
    (heq : ∀ j, j < n → jacRow b a u j = lam * u j) :
    ∀ j, j ≤ n → u j * ∏ i ∈ range j, a i = u 0 * (jacP b a j).eval lam := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjn
    match j, ih, hjn with
    | 0, _, _ => simp
    | 1, _, hjn =>
      have h0 := heq 0 (by omega)
      simp only [jacRow, ite_true, zero_add] at h0
      simp [jacP_one]
      linarith
    | (j + 2), ih, hjn =>
      have h1 := ih (j + 1) (by omega) (by omega)
      have h0 := ih j (by omega) (by omega)
      have hr := heq (j + 1) (by omega)
      simp only [jacRow, Nat.add_sub_cancel] at hr
      have hne : ¬ j + 1 = 0 := by omega
      simp only [hne, ite_false] at hr
      rw [jacP_succ_succ, eval_sub, eval_mul, eval_sub, eval_X, eval_C, eval_mul, eval_C]
      have e : u 0 * ((lam - b (j + 1)) * eval lam (jacP b a (j + 1)) -
          a j ^ 2 * eval lam (jacP b a j)) = (lam - b (j + 1)) * (u 0 * eval lam (jacP b a (j + 1)))
          - a j ^ 2 * (u 0 * eval lam (jacP b a j)) := by ring
      rw [e, ← h1, ← h0]
      rw [prod_range_succ] at h1 ⊢
      rw [prod_range_succ]
      linear_combination ((∏ i ∈ range j, a i) * a j) * hr

/-- `μ` is an eigenvalue of the real square matrix `M` (elementary form). -/
def IsEigenval {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (μ : ℝ) : Prop :=
  ∃ v : ι → ℝ, v ≠ 0 ∧ M *ᵥ v = μ • v

section Eigen

variable {n : ℕ} {b a : ℕ → ℝ}

theorem eigenvec_row {lam : ℝ} {v : Fin n → ℝ} (hv : jacobiMatrix n b a *ᵥ v = lam • v) :
    ∀ j, j < n → jacRow b a (extVec v) j = lam * extVec v j := by
  intro j hj
  have h := congrFun hv ⟨j, hj⟩
  rw [jacobiMatrix_mulVec] at h
  simpa [extVec_of_lt v hj] using h

theorem prod_ne_zero_of_links (ha : ∀ j, j + 1 < n → a j ≠ 0) {j : ℕ} (hj : j < n) :
    ∏ i ∈ range j, a i ≠ 0 := by
  rw [prod_ne_zero_iff]
  intro i hi
  exact ha i (by have := mem_range.mp hi; omega)

/-- Every eigenvector of a Jacobi matrix with nonzero links has a nonzero first component
(the tridiagonal vanishing lemma, from the recurrence). -/
theorem eigenvec_zero_ne (ha : ∀ j, j + 1 < n → a j ≠ 0) {lam : ℝ} {v : Fin n → ℝ}
    (hv : jacobiMatrix n b a *ᵥ v = lam • v) (hv0 : v ≠ 0) : extVec v 0 ≠ 0 := by
  intro h0
  apply hv0
  funext j
  have hprod := eigen_prod_eq n b a (extVec v) lam (eigenvec_row hv) j j.2.le
  rw [h0, zero_mul] at hprod
  have := (mul_eq_zero.mp hprod).resolve_right (prod_ne_zero_of_links ha j.2)
  simpa [extVec_of_lt v j.2] using this

/-- An eigenvalue of `J_n` is a root of `P_n`. -/
theorem eval_jacP_eq_zero_of_eigen (ha : ∀ j, j + 1 < n → a j ≠ 0) {lam : ℝ} {v : Fin n → ℝ}
    (hv : jacobiMatrix n b a *ᵥ v = lam • v) (hv0 : v ≠ 0) : (jacP b a n).eval lam = 0 := by
  have hprod := eigen_prod_eq n b a (extVec v) lam (eigenvec_row hv) n le_rfl
  rw [extVec_of_ge v le_rfl, zero_mul] at hprod
  exact (mul_eq_zero.mp hprod.symm).resolve_left (eigenvec_zero_ne ha hv hv0)

/-- **Theorem ER (general form).**  An eigenvector of a Jacobi matrix with nonzero links is
determined by its first component through the recurrence:
`v_j ∏_{i<j} a_i = v_0 P_j(λ)`, i.e. `v_j = v_0 P_j(λ) / ∏_{i<j} a_i`. -/
theorem jacobi_eigenvec_eq (ha : ∀ j, j + 1 < n → a j ≠ 0) {lam : ℝ} {v : Fin n → ℝ}
    (hv : jacobiMatrix n b a *ᵥ v = lam • v) (j : Fin n) :
    v j = v ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) j.2⟩ * ((jacP b a j).eval lam / ∏ i ∈ range j, a i) := by
  have hprod := eigen_prod_eq n b a (extVec v) lam (eigenvec_row hv) j j.2.le
  rw [extVec_of_lt v j.2, extVec_of_lt v (Nat.lt_of_le_of_lt (Nat.zero_le _) j.2)] at hprod
  rw [mul_div_assoc', eq_div_iff (prod_ne_zero_of_links ha j.2)]
  simpa [mul_comm] using hprod

/-- Eigenspaces of a Jacobi matrix with nonzero links are lines. -/
theorem jacobi_eigenvec_unique (ha : ∀ j, j + 1 < n → a j ≠ 0) {lam : ℝ} {v w : Fin n → ℝ}
    (hv : jacobiMatrix n b a *ᵥ v = lam • v) (hw : jacobiMatrix n b a *ᵥ w = lam • w)
    (hw0 : w ≠ 0) : ∃ c : ℝ, v = c • w := by
  have hn : 0 < n := by
    by_contra h
    exact hw0 (funext fun j => absurd j.2 (by omega))
  have h0 := eigenvec_zero_ne ha hw hw0
  rw [extVec_of_lt w hn] at h0
  refine ⟨v ⟨0, hn⟩ / w ⟨0, hn⟩, ?_⟩
  funext j
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [jacobi_eigenvec_eq ha hv j, jacobi_eigenvec_eq ha hw j]
  field_simp

/-- A root of `P_n` is an eigenvalue of `J_n`, with eigenvector `u_j = P_j(λ) / ∏_{i<j} a_i`. -/
theorem exists_eigenvec_of_root (ha : ∀ j, j + 1 < n → a j ≠ 0) {lam : ℝ}
    (hroot : (jacP b a n).eval lam = 0) :
    ∃ v : Fin n → ℝ, v ≠ 0 ∧ jacobiMatrix n b a *ᵥ v = lam • v := by
  have hn : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    subst this
    simp at hroot
  set u : ℕ → ℝ := fun j => if j < n then (jacP b a j).eval lam / ∏ i ∈ range j, a i else 0
    with hu
  let v : Fin n → ℝ := fun j => u j
  have hext : extVec v = u := by
    funext j
    by_cases hj : j < n
    · simp [extVec_of_lt v hj, v]
    · rw [extVec_of_ge v (by omega)]
      simp [hu, hj]
  -- `a_j u_{j+1} = P_{j+1}(λ) / Π_j`
  have hnext : ∀ j, j < n → a j * u (j + 1) = (jacP b a (j + 1)).eval lam / ∏ i ∈ range j, a i := by
    intro j hj
    by_cases h1 : j + 1 < n
    · simp only [hu, h1, ite_true]
      rw [prod_range_succ]
      have hj0 : a j ≠ 0 := ha j h1
      have hp : ∏ i ∈ range j, a i ≠ 0 := prod_ne_zero_of_links ha (by omega)
      field_simp
    · have : j + 1 = n := by omega
      subst this
      simp [hu, hroot]
  have hprev : ∀ m, m + 1 < n → a m * u m = a m ^ 2 * (jacP b a m).eval lam /
      ∏ i ∈ range (m + 1), a i := by
    intro m hm
    simp only [hu, show m < n by omega, ite_true]
    rw [prod_range_succ]
    have hj0 : a m ≠ 0 := ha m hm
    have hp : ∏ i ∈ range m, a i ≠ 0 := prod_ne_zero_of_links ha (by omega)
    field_simp
  refine ⟨v, ?_, ?_⟩
  · intro h
    have := congrFun h ⟨0, hn⟩
    simp [v, hu] at this
  · funext j
    rw [jacobiMatrix_mulVec, hext]
    obtain ⟨j, hj⟩ := j
    show jacRow b a u j = lam * u j
    unfold jacRow
    rw [hnext j hj]
    rcases j with _ | m
    · simp [hu, hn]
    · have hm : m + 1 < n := hj
      have hne : ¬ m + 1 = 0 := by omega
      simp only [hne, ite_false, Nat.add_sub_cancel]
      rw [hprev m hm]
      simp only [hu, hj, ite_true]
      rw [jacP_succ_succ]
      simp only [eval_sub, eval_mul, eval_X, eval_C]
      ring

theorem jacobi_isEigenval_iff (ha : ∀ j, j + 1 < n → a j ≠ 0) (lam : ℝ) :
    IsEigenval (jacobiMatrix n b a) lam ↔ (jacP b a n).eval lam = 0 :=
  ⟨fun ⟨_, hv0, hv⟩ => eval_jacP_eq_zero_of_eigen ha hv hv0, exists_eigenvec_of_root ha⟩

end Eigen

/-- info: 'FormalResearch.Jacobi.jacobi_eigenvec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_eigenvec_eq

/-- info: 'FormalResearch.Jacobi.jacobi_isEigenval_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_isEigenval_iff

/-- info: 'FormalResearch.Jacobi.jacobi_eigenvec_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_eigenvec_unique

end FormalResearch.Jacobi
