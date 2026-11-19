module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbStableCore
public import FormalResearch.JacobiEigenvectors.Setting.JacobiFamily

/-!
# Paper J, Theorem B, L3.D step 4: the Jacobi gauge of `cor:thb-stable` (`Δ = I`)

Source: Paper J `thmB.tex`, Corollary `cor:thb-stable`, proof, last paragraph: "For the Jacobi case,
`J(t) = (1-t) J_h + t J'_h` is a real Jacobi matrix with positive off-diagonal entries and `‖J(t) - J_h‖ ≤ ε`, so the
above applies to it for each `t`.  Its eigenvalues are simple, and the first entry of each eigenvector is nonzero
(otherwise the recurrence forces the vector to vanish), so the eigenvectors with positive first entry depend
continuously on `t`.  The real numbers `V(t)_kk` are then continuous, satisfy `|V(t)_kk| ≥ (1-η²)^{1/2} > 0` and equal `1`
at `t = 0`, hence are positive at `t = 1`, and `Δ = I`."

Claim class: **proved** (no hypothesis beyond the stated ones, no new axiom).

## Proved here (axiom-pinned)

* `IsJacobiPos A`: `A` real symmetric tridiagonal with `A_{i,i+1} > 0`.
* `IsJacobiPos.first_entry_ne_zero`: an eigenvector (over `ℂ`) of an unreduced Jacobi matrix with zero first entry is zero.
* `isJacobiPos_of_eigenSystem`: a real symmetric tridiagonal matrix with non-negative off-diagonal entries that has an
  eigen-system `IsEigenSystem` (`StrictAnti X`, first entries positive) has positive off-diagonal entries.  (This is what
  lets the frozen statements about `F.jacobiMat` carry no positivity hypothesis: `bondA = sqrt E_n ≥ 0`.)
* `adjugate_eigen_proj`: for a unitary diagonalisation `A W = W diag μ`,
  `adj(μ_k - A)_{ij} = (∏_{l ≠ k} (μ_k - μ_l)) W_{ik} conj(W_{jk})`.
* `thb_jacobi_gauge_diag_pos`, `thb_jacobi_gauge`: for real Jacobi matrices `J, J'` with positive off-diagonal entries, with
  eigen-systems `(X, U)`, `(X', U')` in the gauge `(Psi_k)_0 > 0` and `‖J - J'‖ ≤ ε`, `8 ε ≤ γ`, `c_f ε/γ ≤ 1/2`, consecutive
  gaps of `X` at least `γ`: `(Uᵀ U')_kk > 0` for all `k`, and `‖U' - U‖ ≤ 2 c_f ε/γ` (real operator norm), i.e. `Δ = I`.

## The route

The paper's continuity of the eigenvectors in `t` is replaced by the continuity of one real function per `k`: with
`λ_j(t)` the sorted eigenvalues of `J(t)` (Lipschitz in `t` by Weyl's inequality) and `c_k(t) = ∏_{l ≠ k} (λ_k(t) - λ_l(t))`,
`ρ(t) = c_k(t) · Uᵀ_k adj(λ_k(t) - J(t)) e_0` is continuous, since the adjugate is a polynomial in the entries.  By
`adjugate_eigen_proj`, `ρ(t) = c_k(t)² (Σ_i U_ik W_ik(t)) conj(W_0k(t))` for any unitary eigenvector matrix `W(t)` of
`J(t)`, so `ρ(t) ≠ 0` (`thb_stable_pointwise` gives `V(t)_kk ≠ 0`, `first_entry_ne_zero` gives `W_0k ≠ 0`), `ρ(0) > 0`, and the
intermediate value theorem gives `ρ(1) > 0`, i.e. `(Uᵀ U')_kk · U'_0k > 0`.

## Differences from the paper

* Same statement; the eigenvector continuity is replaced by that of the adjugate expression above (no eigenvector is
  followed along the path).

## Not formalised

Nothing of the Jacobi-gauge paragraph.
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace FormalResearch.JacobiEigenvectors.TheoremB

variable {N : ℕ}

lemma adjugate_unitary {W : CMat N} (hW : Wᴴ * W = 1) : adjugate W = W.det • Wᴴ := by
  have h1 : W * adjugate W = W.det • (1 : CMat N) := mul_adjugate W
  calc adjugate W = (Wᴴ * W) * adjugate W := by rw [hW, Matrix.one_mul]
    _ = Wᴴ * (W * adjugate W) := by rw [Matrix.mul_assoc]
    _ = W.det • Wᴴ := by rw [h1, Matrix.mul_smul, Matrix.mul_one]

/-- **The adjugate of `μ_k - A` is a multiple of the spectral projector**:
for a unitary diagonalisation `A W = W diag μ`,
`adj(μ_k - A)_{ij} = (∏_{l ≠ k} (μ_k - μ_l)) W_{ik} conj(W_{jk})`. -/
theorem adjugate_eigen_proj {A W : CMat N} (hW : Wᴴ * W = 1) {μ : Fin (N + 1) → ℝ}
    (hAW : A * W = W * diagonal (fun k => (μ k : ℂ))) (k i j : Fin (N + 1)) :
    (adjugate (((μ k : ℝ) : ℂ) • (1 : CMat N) - A)) i j =
      (∏ l ∈ Finset.univ.erase k, (((μ k - μ l : ℝ)) : ℂ)) * W i k * (starRingEnd ℂ) (W j k) := by
  have hWW : W * Wᴴ = 1 := mul_eq_one_comm.1 hW
  have hA : A = W * (diagonal (fun k => (μ k : ℂ)) * Wᴴ) := by
    rw [← Matrix.mul_assoc, ← hAW, Matrix.mul_assoc, hWW, Matrix.mul_one]
  have hM : ((μ k : ℝ) : ℂ) • (1 : CMat N) - A =
      W * (diagonal (fun l => (((μ k - μ l : ℝ)) : ℂ)) * Wᴴ) := by
    have hd : (diagonal (fun l => (((μ k - μ l : ℝ)) : ℂ)) : CMat N) =
        ((μ k : ℝ) : ℂ) • (1 : CMat N) - diagonal (fun l => (μ l : ℂ)) := by
      ext a b
      by_cases hab : a = b
      · subst hab; simp
      · simp [Matrix.diagonal_apply, hab]
    rw [hd, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, hWW,
      ← hA]
  rw [hM, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, adjugate_unitary hW,
    adjugate_diagonal]
  have hWH : adjugate Wᴴ = Wᴴ.det • W := by
    have h2 : (Wᴴ)ᴴ * Wᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact hWW
    simpa using adjugate_unitary h2
  rw [hWH]
  have hdet : Wᴴ.det * W.det = 1 := by
    rw [← Matrix.det_mul, hW, Matrix.det_one]
  have key : (Wᴴ.det • W * diagonal (fun l => ∏ m ∈ Finset.univ.erase l, (((μ k - μ m : ℝ)) : ℂ)) *
      (W.det • Wᴴ)) i j = (∏ l ∈ Finset.univ.erase k, (((μ k - μ l : ℝ)) : ℂ)) * W i k *
      (starRingEnd ℂ) (W j k) := by
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, Matrix.smul_apply,
      Matrix.mul_apply, smul_eq_mul, smul_eq_mul]
    generalize hc : (∏ m ∈ Finset.univ.erase k, (((μ k - μ m : ℝ)) : ℂ)) = c
    have ha : ∀ l : Fin (N + 1), (∏ m ∈ Finset.univ.erase l, (((μ k - μ m : ℝ)) : ℂ)) =
        if l = k then c else 0 := by
      intro l
      by_cases hl : l = k
      · subst hl; rw [if_pos rfl]; exact hc
      · rw [if_neg hl]
        exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨Ne.symm hl, Finset.mem_univ _⟩) (by simp)
    simp only [Matrix.mul_diagonal, ha, Matrix.conjTranspose_apply, RCLike.star_def]
    simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linear_combination c * W i k * (starRingEnd ℂ) (W j k) * hdet
  exact key


/-- A real Jacobi matrix with positive off-diagonal entries: symmetric, tridiagonal, `A_{i,i+1} > 0`. -/
structure IsJacobiPos (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : Prop where
  symm : Aᵀ = A
  tri : ∀ i j : Fin (N + 1), (i : ℕ) + 1 < (j : ℕ) → A i j = 0
  pos : ∀ i j : Fin (N + 1), (j : ℕ) = (i : ℕ) + 1 → 0 < A i j

lemma IsJacobiPos.tri' {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hA : IsJacobiPos A)
    (i j : Fin (N + 1)) (h : (j : ℕ) + 1 < (i : ℕ)) : A i j = 0 := by
  have := hA.tri j i h
  rw [← hA.symm] at this
  simpa using this

/-- **An eigenvector of an unreduced Jacobi matrix with zero first entry vanishes.** -/
theorem IsJacobiPos.first_entry_ne_zero {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hA : IsJacobiPos A)
    (y : Fin (N + 1) → ℂ) (lam : ℂ) (hy : (cplx A) *ᵥ y = lam • y) (h0 : y 0 = 0) : y = 0 := by
  have key : ∀ n : ℕ, ∀ i : Fin (N + 1), (i : ℕ) ≤ n → y i = 0 := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have : i = 0 := Fin.ext (by simpa using hi)
      rw [this]; exact h0
    | succ n ih =>
      intro i hi
      by_cases hin : (i : ℕ) ≤ n
      · exact ih i hin
      · have hi' : (i : ℕ) = n + 1 := by omega
        have hn : n < N + 1 := by have := i.isLt; omega
        set a : Fin (N + 1) := ⟨n, hn⟩ with ha
        have hrow := congrFun hy a
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at hrow
        have hya : y a = 0 := ih a (by simp [ha])
        rw [hya, mul_zero] at hrow
        rw [Finset.sum_eq_single i] at hrow
        · have hpos : (0:ℝ) < A a i := hA.pos a i (by simp [ha, hi'])
          have hne : ((A a i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
          exact (mul_eq_zero.1 hrow).resolve_left hne
        · intro j _ hji
          by_cases hj : (j : ℕ) ≤ n
          · rw [ih j hj, mul_zero]
          · have hj2 : (a : ℕ) + 1 < (j : ℕ) := by
              have : (j : ℕ) ≠ (i : ℕ) := fun h => hji (Fin.ext h)
              simp [ha]; omega
            rw [hA.tri a j hj2]; simp
        · simp
  funext i
  exact key i i le_rfl


open FormalResearch.JacobiEigenvectors.Setting in
/-- **Positivity of the bonds is forced by an eigen-system** (`StrictAnti X`, first entries positive): a real symmetric
tridiagonal matrix with non-negative off-diagonal entries that has an eigen-system `IsEigenSystem` has positive
off-diagonal entries (a vanishing bond would split the matrix, and a simple eigenvector with positive first entry would
then be supported in the first block, for every `k`, contradicting the orthogonality of `U`). -/
theorem isJacobiPos_of_eigenSystem {A U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} {X : Fin (N + 1) → ℝ}
    (hs : Aᵀ = A) (htri : ∀ i j : Fin (N + 1), (i : ℕ) + 1 < (j : ℕ) → A i j = 0)
    (hnn : ∀ i j : Fin (N + 1), (j : ℕ) = (i : ℕ) + 1 → 0 ≤ A i j)
    (hE : IsEigenSystem A X U) : IsJacobiPos A := by
  refine ⟨hs, htri, fun i j hij => ?_⟩
  refine lt_of_le_of_ne (hnn i j hij) fun h0 => ?_
  have hA0 : A i j = 0 := h0.symm
  set p : Fin (N + 1) → ℝ := fun a => if (a : ℕ) ≤ (i : ℕ) then 1 else 0 with hp
  set P : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := diagonal p with hP
  have hblock : ∀ a b : Fin (N + 1), (a : ℕ) ≤ (i : ℕ) → (i : ℕ) < (b : ℕ) → A a b = 0 := by
    intro a b ha hb
    by_cases hab : (a : ℕ) + 1 < (b : ℕ)
    · exact htri a b hab
    · have hb' : (b : ℕ) = (a : ℕ) + 1 := by omega
      have ha' : a = i := Fin.ext (by omega)
      have hbj : b = j := Fin.ext (by omega)
      rw [ha', hbj]; exact hA0
  have hcomm : A * P = P * A := by
    ext a b
    rw [hP, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [hp]
    by_cases ha : (a : ℕ) ≤ (i : ℕ) <;> by_cases hb : (b : ℕ) ≤ (i : ℕ)
    · simp [ha, hb]
    · have := hblock a b ha (by omega)
      simp [ha, hb, this]
    · have e : A a b = A b a := by simpa using congrFun (congrFun hs b) a
      have h2 : A a b = 0 := e.trans (hblock b a hb (by omega))
      simp [ha, hb, h2]
    · simp [ha, hb]
  have hUU : U * Uᵀ = 1 := mul_eq_one_comm.1 hE.orth
  set D : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := diagonal X with hD
  have hUA : Uᵀ * A = D * Uᵀ := by
    have := congrArg Matrix.transpose hE.eig
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hs, Matrix.diagonal_transpose] at this
    exact this
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ, Y = P * U := ⟨_, rfl⟩
  have hAY : A * Y = Y * D := by
    rw [hY, ← Matrix.mul_assoc, hcomm, Matrix.mul_assoc, hE.eig, ← Matrix.mul_assoc]
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ, C = Uᵀ * Y := ⟨_, rfl⟩
  have hDC : D * C = C * D := by
    calc D * C = D * Uᵀ * Y := by rw [hC, Matrix.mul_assoc]
      _ = Uᵀ * A * Y := by rw [hUA]
      _ = Uᵀ * (A * Y) := by rw [Matrix.mul_assoc]
      _ = Uᵀ * (Y * D) := by rw [hAY]
      _ = C * D := by rw [hC, Matrix.mul_assoc]
  have hCoff : ∀ l k : Fin (N + 1), l ≠ k → C l k = 0 := by
    intro l k hlk
    have := congrFun (congrFun hDC l) k
    rw [hD, Matrix.diagonal_mul, Matrix.mul_diagonal] at this
    have hne : X l - X k ≠ 0 := sub_ne_zero.2 (hE.anti.injective.ne hlk)
    have : (X l - X k) * C l k = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hne
  have hYU : Y = U * C := by rw [hC, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have hYjk : ∀ j k, Y j k = U j k * C k k := by
    intro j k
    rw [hYU, Matrix.mul_apply, Finset.sum_eq_single k]
    · intro l _ hlk; rw [hCoff l k hlk, mul_zero]
    · simp
  have hCkk : ∀ k, C k k = 1 := by
    intro k
    have h1 := hYjk 0 k
    have h2 : Y 0 k = U 0 k := by
      rw [hY, hP, Matrix.diagonal_mul]; simp [hp]
    have hpos := hE.pos k
    rw [h2] at h1
    have : U 0 k * (C k k - 1) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left hpos.ne'
    linarith
  have hrow : ∀ k, U j k = 0 := by
    intro k
    have h1 := hYjk j k
    have h2 : Y j k = 0 := by
      rw [hY, hP, Matrix.diagonal_mul]
      have : ¬ (j : ℕ) ≤ (i : ℕ) := by omega
      have h' : ¬ j ≤ i := fun h => this (Fin.le_def.1 h)
      simp [hp, this, h']
    rw [h2, hCkk k, mul_one] at h1
    exact h1.symm
  have h1 := congrFun (congrFun hUU j) j
  rw [Matrix.mul_apply] at h1
  simp only [Matrix.transpose_apply, hrow, mul_zero, Finset.sum_const_zero, Matrix.one_apply_eq] at h1
  exact zero_ne_one h1


section Cplx

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma cplx_eq_mapMatrix (A : Matrix n n ℝ) : cplx A = Complex.ofRealHom.mapMatrix A := by
  ext i j; simp

lemma cplx_mul (A B : Matrix n n ℝ) : cplx (A * B) = cplx A * cplx B := by
  simp only [cplx_eq_mapMatrix, map_mul]

lemma cplx_sub (A B : Matrix n n ℝ) : cplx (A - B) = cplx A - cplx B := by
  simp only [cplx_eq_mapMatrix, map_sub]

lemma cplx_add (A B : Matrix n n ℝ) : cplx (A + B) = cplx A + cplx B := by
  simp only [cplx_eq_mapMatrix, map_add]

lemma cplx_one : cplx (1 : Matrix n n ℝ) = 1 := by
  simp only [cplx_eq_mapMatrix, map_one]

lemma cplx_smul (c : ℝ) (A : Matrix n n ℝ) : cplx (c • A) = (c : ℂ) • cplx A := by
  ext i j; simp

lemma cplx_diagonal (d : n → ℝ) : cplx (diagonal d) = diagonal (fun k => (d k : ℂ)) := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.diagonal_apply, h]

lemma cplx_conjTranspose (A : Matrix n n ℝ) : (cplx A)ᴴ = cplx Aᵀ := by
  ext i j; simp

lemma cplx_isHermitian {A : Matrix n n ℝ} (h : Aᵀ = A) : (cplx A).IsHermitian := by
  rw [Matrix.IsHermitian, cplx_conjTranspose, h]

lemma cplx_adjugate (A : Matrix n n ℝ) : cplx (adjugate A) = adjugate (cplx A) := by
  simp only [cplx_eq_mapMatrix]
  exact (Complex.ofRealHom).map_adjugate A

end Cplx


open FormalResearch.JacobiEigenvectors.Setting in
/-- The diagonal of `Uᵀ U'` is positive in the Jacobi gauge (continuity along `J(t) = (1-t) J + t J'`). -/
theorem thb_jacobi_gauge_diag_pos {J J' U U' : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    {X X' : Fin (N + 1) → ℝ} {γ ε : ℝ}
    (hJ : IsJacobiPos J) (hJ' : IsJacobiPos J') (hE : IsEigenSystem J X U) (hE' : IsEigenSystem J' X' U')
    (hγ : 0 < γ) (hcons : ∀ i j : Fin (N + 1), (j : ℕ) = (i : ℕ) + 1 → γ ≤ X i - X j)
    (hε : ‖J - J'‖ ≤ ε) (h8 : 8 * ε ≤ γ) (hη : thbCf / γ * ε ≤ 1 / 2) (k : Fin (N + 1)) :
    0 < (Uᵀ * U') k k := by
  -- the path
  set A : ℝ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := fun t => (1 - t) • J + t • J' with hA
  have hAsymm : ∀ t, (A t)ᵀ = A t := by
    intro t; simp only [hA, Matrix.transpose_add, Matrix.transpose_smul, hJ.symm, hJ'.symm]
  have hherm : ∀ t, (cplx (A t)).IsHermitian := fun t => cplx_isHermitian (hAsymm t)
  have hAcont : Continuous A := by
    simp only [hA]; fun_prop
  have hAdiff : ∀ t s, A t - A s = (t - s) • (J' - J) := by
    intro t s; simp only [hA]; ext a b; simp; ring
  set lam : Fin (N + 1) → ℝ → ℝ := fun j t => thbEig (hherm t) j with hlam
  have hlamLip : ∀ j t s, |lam j t - lam j s| ≤ |t - s| * ‖J' - J‖ := by
    intro j t s
    have := thb_weyl_abs_sub_le (hherm t) (hherm s) j
    rw [← cplx_sub, norm_cplx, hAdiff, norm_smul, Real.norm_eq_abs] at this
    exact this
  have hlamcont : ∀ j, Continuous (lam j) := by
    intro j
    refine (LipschitzWith.of_dist_le_mul (K := ‖J' - J‖₊) fun t s => ?_).continuous
    rw [Real.dist_eq, Real.dist_eq, mul_comm]
    simpa using hlamLip j t s
  set Q : ℝ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
    fun t => adjugate ((lam k t) • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) - A t) with hQ
  set cc : ℝ → ℝ := fun t => ∏ l ∈ Finset.univ.erase k, (lam k t - lam l t) with hcc
  set ρ : ℝ → ℝ := fun t => cc t * ∑ i, U i k * Q t i 0 with hρ
  have hQcont : Continuous Q := by
    simp only [hQ]
    exact Continuous.matrix_adjugate ((hlamcont k).smul continuous_const |>.sub hAcont)
  have hcccont : Continuous cc := by
    simp only [hcc]
    exact continuous_finset_prod _ fun l _ => (hlamcont k).sub (hlamcont l)
  have hρcont : Continuous ρ := by
    simp only [hρ]
    refine hcccont.mul (continuous_finset_sum _ fun i _ => continuous_const.mul ?_)
    exact (hQcont.matrix_elem i 0)
  have hform : ∀ (t : ℝ) (W : CMat N), Wᴴ * W = 1 →
      cplx (A t) * W = W * diagonal (fun l => (lam l t : ℂ)) →
      (ρ t : ℂ) = (cc t : ℂ) ^ 2 * (∑ i, (U i k : ℂ) * W i k) * starRingEnd ℂ (W 0 k) := by
    intro t W hW hAW
    have hQc : cplx (Q t) = adjugate (((lam k t : ℝ) : ℂ) • (1 : CMat N) - cplx (A t)) := by
      simp only [hQ]
      rw [cplx_adjugate, cplx_sub, cplx_smul, cplx_one]
    have hent : ∀ i, ((Q t i 0 : ℝ) : ℂ) = (cc t : ℂ) * W i k * starRingEnd ℂ (W 0 k) := by
      intro i
      have h1 := adjugate_eigen_proj hW hAW k i 0
      rw [← hQc] at h1
      simp only [cplx, Matrix.map_apply] at h1
      rw [h1, hcc]
      push_cast
      rfl
    simp only [hρ]
    push_cast
    simp only [hent]
    rw [Finset.mul_sum]
    calc ∑ i, (cc t : ℂ) * ((U i k : ℂ) * ((cc t : ℂ) * W i k * starRingEnd ℂ (W 0 k)))
        = ∑ i, ((cc t : ℂ) ^ 2 * ((U i k : ℂ) * W i k)) * starRingEnd ℂ (W 0 k) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  -- complexified data
  have hcUU : (cplx U)ᴴ * cplx U = 1 := by
    rw [cplx_conjTranspose, ← cplx_mul, hE.orth, cplx_one]
  have hcUU' : (cplx U')ᴴ * cplx U' = 1 := by
    rw [cplx_conjTranspose, ← cplx_mul, hE'.orth, cplx_one]
  have hcJU : cplx J * cplx U = cplx U * diagonal (fun l => (X l : ℂ)) := by
    rw [← cplx_mul, hE.eig, cplx_mul, cplx_diagonal]
  have hcJU' : cplx J' * cplx U' = cplx U' * diagonal (fun l => (X' l : ℂ)) := by
    rw [← cplx_mul, hE'.eig, cplx_mul, cplx_diagonal]
  have hA0 : A 0 = J := by simp [hA]
  have hA1 : A 1 = J' := by simp [hA]
  have hlam0 : ∀ j, lam j 0 = X j := by
    intro j
    have h : cplx (A 0) * cplx U = cplx U * diagonal (fun l => (X l : ℂ)) := by rw [hA0]; exact hcJU
    exact (thbEig_eq_of_eigSystem (hherm 0) hcUU h hE.anti.antitone j).symm
  have hlam1 : ∀ j, lam j 1 = X' j := by
    intro j
    have h : cplx (A 1) * cplx U' = cplx U' * diagonal (fun l => (X' l : ℂ)) := by rw [hA1]; exact hcJU'
    exact (thbEig_eq_of_eigSystem (hherm 1) hcUU' h hE'.anti.antitone j).symm
  have hccne : ∀ t, (StrictAnti fun l => lam l t) → cc t ≠ 0 := by
    intro t hsa
    simp only [hcc]
    refine Finset.prod_ne_zero_iff.2 fun l hl => ?_
    have hlk : l ≠ k := Finset.ne_of_mem_erase hl
    exact sub_ne_zero.2 (hsa.injective.ne (Ne.symm hlk))
  -- t = 0
  have hρ0 : 0 < ρ 0 := by
    have h := hform 0 (cplx U) hcUU (by
      have : (fun l => (lam l 0 : ℂ)) = fun l => (X l : ℂ) := by funext l; rw [hlam0]
      rw [this, hA0]; exact hcJU)
    have hsum : ∑ i, (U i k : ℂ) * (cplx U) i k = 1 := by
      have := congrFun (congrFun hE.orth k) k
      rw [Matrix.mul_apply] at this
      simp only [Matrix.transpose_apply, Matrix.one_apply_eq] at this
      simp only [cplx, Matrix.map_apply]
      exact_mod_cast this
    rw [hsum] at h
    simp only [cplx, Matrix.map_apply, Complex.conj_ofReal, mul_one] at h
    have h2 : ρ 0 = (cc 0) ^ 2 * U 0 k := by exact_mod_cast h
    rw [h2]
    have hsa : StrictAnti fun l => lam l 0 := by
      intro a b hab; show lam b 0 < lam a 0; rw [hlam0, hlam0]; exact hE.anti hab
    have := hccne 0 hsa
    have := hE.pos k
    positivity
  -- t = 1
  have hρ1 : ρ 1 = (cc 1) ^ 2 * (Uᵀ * U') k k * U' 0 k := by
    have h := hform 1 (cplx U') hcUU' (by
      have : (fun l => (lam l 1 : ℂ)) = fun l => (X' l : ℂ) := by funext l; rw [hlam1]
      rw [this, hA1]; exact hcJU')
    simp only [cplx, Matrix.map_apply, Complex.conj_ofReal] at h
    have hm : ((Uᵀ * U') k k : ℝ) = ∑ i, U i k * U' i k := by
      rw [Matrix.mul_apply]; simp
    rw [hm]
    exact_mod_cast (by rw [h]; push_cast; ring : (ρ 1 : ℂ) = ((cc 1) ^ 2 * (∑ i, U i k * U' i k) * U' 0 k : ℝ))
  -- intermediate t
  have hρne : ∀ t ∈ Set.Icc (0 : ℝ) 1, ρ t ≠ 0 := by
    intro t ht
    have hJt : IsJacobiPos (A t) := by
      refine ⟨hAsymm t, fun a b hab => ?_, fun a b hab => ?_⟩
      · simp [hA, hJ.tri a b hab, hJ'.tri a b hab]
      · have h1 := hJ.pos a b hab
        have h2 := hJ'.pos a b hab
        simp only [hA, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        rcases eq_or_lt_of_le ht.1 with h0 | h0
        · rw [← h0]; simpa using h1
        · nlinarith [ht.2, h0]
    obtain ⟨W, hW, hAW⟩ := exists_eigSystem_thbEig (hherm t)
    have hAW' : cplx (A t) * W = W * diagonal (fun l => (lam l t : ℂ)) := hAW
    have hdist : ‖cplx J - cplx (A t)‖ ≤ ε := by
      rw [← cplx_sub, norm_cplx]
      have : J - A t = t • (J - J') := by simp only [hA]; ext a b; simp; ring
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      calc t * ‖J - J'‖ ≤ 1 * ‖J - J'‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ ≤ ε := by rw [one_mul]; exact hε
    have hpt := thb_stable_pointwise (cplx_isHermitian hJ.symm) (hherm t) hcUU hW hcJU hAW'
      hE.anti.antitone (thbEig_antitone (hherm t)) hγ
      (fun i j hij => hcons i j hij) hdist h8 hη
    obtain ⟨hsa, hVne, -⟩ := hpt
    have hsa' : StrictAnti fun l => lam l t := hsa
    have hform' := hform t W hW hAW'
    have hVk : ∑ i, (U i k : ℂ) * W i k ≠ 0 := by
      have := hVne k
      rw [Matrix.mul_apply] at this
      simpa [cplx, Matrix.conjTranspose_apply] using this
    have hW0 : W 0 k ≠ 0 := by
      intro h0
      have hcol : (cplx (A t)) *ᵥ (fun i => W i k) = ((lam k t : ℝ) : ℂ) • (fun i => W i k) := by
        funext i
        have := congrFun (congrFun hAW' i) k
        rw [Matrix.mul_diagonal, Matrix.mul_apply] at this
        simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
        rw [this]; ring
      have hz := hJt.first_entry_ne_zero _ _ hcol h0
      have h1 := congrFun (congrFun hW k) k
      rw [Matrix.mul_apply] at h1
      simp only [Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h1
      have : ∀ i, W i k = 0 := fun i => congrFun hz i
      simp [this] at h1
    have hne : (ρ t : ℂ) ≠ 0 := by
      rw [hform']
      have := hccne t hsa'
      have hc : ((cc t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hc) hVk) (by simpa using hW0)
    exact_mod_cast hne
  -- the intermediate value theorem
  have hρ1pos : 0 < ρ 1 := by
    by_contra hcon
    have hle : ρ 1 ≤ 0 := not_lt.1 hcon
    have hlt : ρ 1 < 0 := lt_of_le_of_ne hle (hρne 1 ⟨zero_le_one, le_rfl⟩)
    have hmem : (0 : ℝ) ∈ Set.Icc (ρ 1) (ρ 0) := ⟨hlt.le, hρ0.le⟩
    obtain ⟨t, ht, ht0⟩ := intermediate_value_Icc' (zero_le_one) hρcont.continuousOn hmem
    exact hρne t ht ht0
  rw [hρ1] at hρ1pos
  have hcc1 : cc 1 ≠ 0 := by
    refine hccne 1 ?_
    intro a b hab; show lam b 1 < lam a 1; rw [hlam1, hlam1]; exact hE'.anti hab
  have hU0 := hE'.pos k
  have hsq : 0 < (cc 1) ^ 2 := by positivity
  by_contra hneg
  have : (cc 1) ^ 2 * (Uᵀ * U') k k * U' 0 k ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hsq.le (not_lt.1 hneg)) hU0.le
  linarith


open FormalResearch.JacobiEigenvectors.Setting in
/-- **The Jacobi gauge** (Paper J, `cor:thb-stable`, last paragraph): if `J, J'` are real Jacobi matrices with positive
off-diagonal entries and `U, U'` their eigenvector matrices in the gauge `(Psi_k)_0 > 0`, then `Δ = I`, i.e.
`‖U' - U‖ ≤ 2 c_f ε / γ` (real operator norm). -/
theorem thb_jacobi_gauge {J J' U U' : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    {X X' : Fin (N + 1) → ℝ} {γ ε : ℝ}
    (hJ : IsJacobiPos J) (hJ' : IsJacobiPos J') (hE : IsEigenSystem J X U) (hE' : IsEigenSystem J' X' U')
    (hγ : 0 < γ) (hcons : ∀ i j : Fin (N + 1), (j : ℕ) = (i : ℕ) + 1 → γ ≤ X i - X j)
    (hε : ‖J - J'‖ ≤ ε) (h8 : 8 * ε ≤ γ) (hη : thbCf / γ * ε ≤ 1 / 2) :
    ‖U' - U‖ ≤ 2 * (thbCf / γ * ε) := by
  have hcUU : (cplx U)ᴴ * cplx U = 1 := by
    rw [cplx_conjTranspose, ← cplx_mul, hE.orth, cplx_one]
  have hcUU' : (cplx U')ᴴ * cplx U' = 1 := by
    rw [cplx_conjTranspose, ← cplx_mul, hE'.orth, cplx_one]
  have hcJU : cplx J * cplx U = cplx U * diagonal (fun l => (X l : ℂ)) := by
    rw [← cplx_mul, hE.eig, cplx_mul, cplx_diagonal]
  have hcJU' : cplx J' * cplx U' = cplx U' * diagonal (fun l => (X' l : ℂ)) := by
    rw [← cplx_mul, hE'.eig, cplx_mul, cplx_diagonal]
  have hdist : ‖cplx J - cplx J'‖ ≤ ε := by rw [← cplx_sub, norm_cplx]; exact hε
  obtain ⟨-, -, hbound⟩ := thb_stable_pointwise (cplx_isHermitian hJ.symm) (cplx_isHermitian hJ'.symm)
    hcUU hcUU' hcJU hcJU' hE.anti.antitone hE'.anti.antitone hγ (fun i j hij => hcons i j hij)
    hdist h8 hη
  have hpos := fun k => thb_jacobi_gauge_diag_pos hJ hJ' hE hE' hγ hcons hε h8 hη k
  have hV : ∀ k, ((cplx U)ᴴ * cplx U') k k = (((Uᵀ * U') k k : ℝ) : ℂ) := by
    intro k; rw [cplx_conjTranspose, ← cplx_mul]; rfl
  have hone : (diagonal fun k => ((‖((cplx U)ᴴ * cplx U') k k‖ : ℝ) : ℂ) /
      ((cplx U)ᴴ * cplx U') k k : CMat N) = 1 := by
    rw [← Matrix.diagonal_one]
    congr 1
    funext k
    rw [hV k, Complex.norm_real, Real.norm_of_nonneg (hpos k).le]
    have : (((Uᵀ * U') k k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos k).ne'
    field_simp
  rw [hone, Matrix.mul_one, ← cplx_sub, norm_cplx] at hbound
  exact hbound

end FormalResearch.JacobiEigenvectors.TheoremB

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.thb_jacobi_gauge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.thb_jacobi_gauge

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.isJacobiPos_of_eigenSystem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.isJacobiPos_of_eigenSystem

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.adjugate_eigen_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.adjugate_eigen_proj
