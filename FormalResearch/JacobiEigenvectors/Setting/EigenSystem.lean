module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Setting.JacobiFamily

/-!
# Paper J setting, L1.3: the spectral theorem for the Jacobi matrix (`exists_eigenSystem`, `eigVec_JacSol`, `bondA_pos`)

Source: Paper J, `main_results.tex` Section 1.1 (the eigen-system `X_0 > ... > X_N`, `U_h = (Psi_0, ..., Psi_N)` orthogonal, gauge
`(Psi_k)_0 > 0`), and `thmA.tex` Section 4.1 (`a_n = sqrt E_n`, the recurrence eq:tha-rec).  Namespace
`FormalResearch.JacobiEigenvectors.Setting`; the definitions are those of `Setting/JacobiFamily.lean` (`IsEigenSystem`, `eigVec`, `JacSol`).

## Statements

* `bondA_pos`: `0 < a_n` for `0 ≤ n < N`, from `G_h > 0` at the nodes `s_n` (the only use of the symbol positivity).
* `jacobiMat_mulVec_apply`: the tridiagonal row of `J_h` (with the zero extension `extV` of a vector, as in `eigVec`).
* `eig_first_zero`: an eigenvector of an unreduced Jacobi matrix (`a_n > 0`, `0 ≤ n < N`) with zero first entry is zero.
* `eigVec_JacSol`: each column of an eigen-system solves `JacSol F μ N (X k) (N+1)` (eq:tha-rec on all rows).
* `exists_eigenSystem`: under `G_h > 0` on the nodes, there is an eigen-system `IsEigenSystem (F.jacobiMat μ N) X U`.

## Construction

`J_h` is real symmetric, so Mathlib's spectral theorem (`Matrix.IsHermitian.eigenvectorUnitary`, `mulVec_eigenvectorBasis`) gives an
orthonormal eigenbasis.  The eigenvalues are sorted decreasingly by `Tuple.sort` (the order of the frozen `IsEigenSystem` is
`StrictAnti X`, i.e. `X_0 > ... > X_N`).  The gauge is the sign `s_k` with `s_k (W 0 (σ k)) > 0`; it is well defined because the first
entry of every eigenvector is nonzero (`eig_first_zero`).  Simple spectrum: two eigenvectors with the same eigenvalue are proportional
(`eig_first_zero` applied to a combination with zero first entry), which contradicts orthogonality.

## Differences from the paper

The gauge and the order are those of `IsEigenSystem` (decreasing `X`, first entry positive).  The positivity of the bonds is a
hypothesis of the eigen-system statements through `G_h > 0` on the nodes (`bondA_pos`); it is implied by `(H1)` and `(D_M)` only for
`h ≤ h_0` (not formalised here: `(H1)` gives `G_0 ≥ g_*`, and `(D_M)` gives `G_h - G_0 = O(h)` on `[0,L]`).

## Not formalised

`(H1)`--`(H3)` and the uniform bound `G_h ≥ g_*/2` for small `h`, which would give `bondA_pos` without the pointwise hypothesis.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Setting

open Set Finset
open scoped Matrix

variable {Par : Type*}

/-- Positivity of the bonds `a_n = sqrt E_n` for `0 ≤ n < N`, from positivity of `G_h` at the nodes `s_n = (n+1) h`. -/
theorem bondA_pos (F : SymbolFamily Par) (μ : Par) (N : ℕ)
    (hG : ∀ n : ℤ, 0 ≤ n → n < N → 0 < F.Gh μ (F.step N) (sNode (F.step N) n))
    (n : ℤ) (hn0 : 0 ≤ n) (hnN : n < N) : 0 < F.bondA μ N n := by
  unfold SymbolFamily.bondA
  rw [if_pos ⟨hn0, hnN⟩]
  apply Real.sqrt_pos.mpr
  unfold SymbolFamily.entryE
  have hh : 0 < F.step N := by
    unfold SymbolFamily.step FormalResearch.JB.stepSize
    have := F.L_pos
    positivity
  have hLh : F.L = ((N : ℝ) + 1) * F.step N := by
    unfold SymbolFamily.step FormalResearch.JB.stepSize
    have : ((N : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  have hn1 : ((n : ℝ) + 1) ≤ N := by
    have : n + 1 ≤ (N : ℤ) := by omega
    exact_mod_cast this
  have hnR : (0 : ℝ) ≤ n := by exact_mod_cast hn0
  have hs : 0 < sNode (F.step N) n := by
    unfold sNode
    exact mul_pos (by linarith) hh
  have hLs : 0 < F.L - sNode (F.step N) n := by
    unfold sNode
    have key : F.L - ((n : ℝ) + 1) * F.step N = ((N : ℝ) - n) * F.step N := by
      rw [hLh]
      ring
    have hpos : 0 < ((N : ℝ) - n) * F.step N := mul_pos (by linarith) hh
    linarith
  exact mul_pos (mul_pos hs hLs) (hG n hn0 hnN)

/-- The zero extension of a vector on `Fin (N+1)` to `ℤ` (the convention of `eigVec`). -/
def extV {N : ℕ} (w : Fin (N + 1) → ℝ) : ℤ → ℝ :=
  fun n => if hn : 0 ≤ n ∧ n ≤ (N : ℤ) then w ⟨n.toNat, by omega⟩ else 0

lemma extV_fin {N : ℕ} (w : Fin (N + 1) → ℝ) (i : Fin (N + 1)) : extV w (i.val : ℤ) = w i := by
  unfold extV
  rw [dif_pos ⟨by positivity, by omega⟩]
  congr 1

lemma extV_nat {N : ℕ} (w : Fin (N + 1) → ℝ) (j : Fin (N + 1)) (n : ℤ) (hn : (j.val : ℤ) = n) :
    extV w n = w j := by
  rw [← hn]
  exact extV_fin w j

lemma extV_neg {N : ℕ} (w : Fin (N + 1) → ℝ) (n : ℤ) (hn : n < 0) : extV w n = 0 := by
  unfold extV
  rw [dif_neg (by omega)]

lemma extV_big {N : ℕ} (w : Fin (N + 1) → ℝ) (n : ℤ) (hn : (N : ℤ) < n) : extV w n = 0 := by
  unfold extV
  rw [dif_neg (by omega)]

/-- The entry of `J_h` at `(i, j)`, split into its three possible contributions (diagonal, the bond `i → i+1`, the bond `j → j+1`). -/
lemma jacobiMat_apply_mul (F : SymbolFamily Par) (μ : Par) (N : ℕ) (w : Fin (N + 1) → ℝ) (i j : Fin (N + 1)) :
    F.jacobiMat μ N i j * w j
      = (if j = i then F.entryB μ N i.val * w j else 0)
        + (if (j.val : ℤ) = (i.val : ℤ) + 1 then F.bondA μ N i.val * w j else 0)
        + (if (i.val : ℤ) = (j.val : ℤ) + 1 then F.bondA μ N j.val * w j else 0) := by
  unfold SymbolFamily.jacobiMat
  simp only [Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> first | omega | simp_all

/-- The tridiagonal row of `J_h`: `(J w)_i = B_i w_i + a_i w_{i+1} + a_{i-1} w_{i-1}`, with `w` extended by zero (`extV`). -/
theorem jacobiMat_mulVec_apply (F : SymbolFamily Par) (μ : Par) (N : ℕ) (w : Fin (N + 1) → ℝ) (i : Fin (N + 1)) :
    (F.jacobiMat μ N *ᵥ w) i = F.entryB μ N i.val * w i + F.bondA μ N i.val * extV w ((i.val : ℤ) + 1)
      + F.bondA μ N ((i.val : ℤ) - 1) * extV w ((i.val : ℤ) - 1) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl (fun j _ => jacobiMat_apply_mul F μ N w i j)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  congr 1
  · -- diagonal
    rw [Finset.sum_ite_eq']
    simp
  · -- the bond `i → i+1`
    by_cases hi : (i.val : ℤ) + 1 ≤ (N : ℤ)
    · rw [Finset.sum_eq_single (⟨i.val + 1, by omega⟩ : Fin (N + 1))]
      · have hx : extV w ((i.val : ℤ) + 1) = w ⟨i.val + 1, by omega⟩ := by
          unfold extV
          rw [dif_pos ⟨by omega, by omega⟩]
          congr 1
        rw [hx, if_pos (by simp)]
      · intro b _ hb
        rw [if_neg]
        intro hbeq
        apply hb
        ext
        simp only
        omega
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have hz : extV w ((i.val : ℤ) + 1) = 0 := extV_big w _ (by omega)
      rw [hz, mul_zero]
      apply Finset.sum_eq_zero
      intro b _
      rw [if_neg]
      have := b.isLt
      omega
  · -- the bond `i-1 → i`
    by_cases hi : 1 ≤ (i.val : ℤ)
    · rw [Finset.sum_eq_single (⟨i.val - 1, by omega⟩ : Fin (N + 1))]
      · have hx : extV w ((i.val : ℤ) - 1) = w ⟨i.val - 1, by omega⟩ := by
          unfold extV
          rw [dif_pos ⟨by omega, by omega⟩]
          congr 1
          apply Fin.ext
          show ((i.val : ℤ) - 1).toNat = i.val - 1
          omega
        have hb : F.bondA μ N (((⟨i.val - 1, by omega⟩ : Fin (N + 1)).val : ℕ) : ℤ) = F.bondA μ N ((i.val : ℤ) - 1) := by
          congr 1
          simp
          omega
        rw [hx, if_pos (by simp; omega), hb]
      · intro b _ hb
        rw [if_neg]
        intro hbeq
        apply hb
        ext
        simp only
        omega
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have hz : extV w ((i.val : ℤ) - 1) = 0 := extV_neg w _ (by omega)
      rw [hz, mul_zero]
      apply Finset.sum_eq_zero
      intro b _
      rw [if_neg]
      omega

/-- **First entry of an eigenvector** of an unreduced Jacobi matrix (`a_n > 0` for `0 ≤ n < N`): a solution of `J w = ν w` with
`w 0 = 0` vanishes.  The row relations propagate the zero from site `0` to every site. -/
theorem eig_first_zero (F : SymbolFamily Par) (μ : Par) (N : ℕ)
    (hpos : ∀ n : ℤ, 0 ≤ n → n < N → 0 < F.bondA μ N n) (ν : ℝ) (w : Fin (N + 1) → ℝ)
    (hw : F.jacobiMat μ N *ᵥ w = ν • w) (h0 : w 0 = 0) : w = 0 := by
  have row : ∀ n : ℕ, n ≤ N →
      F.bondA μ N n * extV w ((n : ℤ) + 1) + F.bondA μ N ((n : ℤ) - 1) * extV w ((n : ℤ) - 1)
        = (ν - F.entryB μ N n) * extV w n := by
    intro n hn
    obtain ⟨i, hi⟩ : ∃ i : Fin (N + 1), i.val = n := ⟨⟨n, by omega⟩, rfl⟩
    have h1 := congrFun hw i
    rw [jacobiMat_mulVec_apply] at h1
    have hiz : extV w (n : ℤ) = w i := by
      rw [← hi]
      exact extV_fin w i
    simp only [Pi.smul_apply, smul_eq_mul, hi] at h1
    rw [hiz]
    linarith
  have claim : ∀ n : ℕ, n ≤ N → extV w (n : ℤ) = 0 ∧ extV w ((n : ℤ) - 1) = 0 := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨?_, extV_neg w _ (by norm_num)⟩
      rw [extV_nat w 0 _ (by simp), h0]
    | succ n ih =>
      intro hn
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hr := row n (by omega)
      rw [h1, h2] at hr
      simp only [mul_zero, add_zero] at hr
      have hapos : 0 < F.bondA μ N n := hpos n (by positivity) (by omega)
      have hv : extV w ((n : ℤ) + 1) = 0 := (mul_eq_zero.mp hr).resolve_left hapos.ne'
      refine ⟨?_, ?_⟩
      · rw [Nat.cast_succ]
        exact hv
      · rw [Nat.cast_succ, add_sub_cancel_right]
        exact h1
  funext i
  have h := (claim i.val (by omega)).1
  rw [extV_fin] at h
  simpa using h

/-- **Each column of an eigen-system solves the recurrence** (`JacSol` of eq:tha-rec, on all rows `0 ≤ n ≤ N`). -/
theorem eigVec_JacSol (F : SymbolFamily Par) (μ : Par) (N : ℕ) (X : Fin (N + 1) → ℝ)
    (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hE : IsEigenSystem (F.jacobiMat μ N) X U) (k : Fin (N + 1)) :
    JacSol F μ N (X k) ((N : ℤ) + 1) (eigVec U k) := by
  intro n hn0 hnN
  obtain ⟨i, hi⟩ : ∃ i : Fin (N + 1), (i.val : ℤ) = n :=
    ⟨⟨n.toNat, by omega⟩, by simp only; omega⟩
  have hcol : (F.jacobiMat μ N *ᵥ (fun j => U j k)) i = X k * U i k := by
    have h1 := congrFun (congrFun hE.eig i) k
    rw [Matrix.mul_diagonal, Matrix.mul_apply] at h1
    simp only [Matrix.mulVec, dotProduct]
    linarith [mul_comm (X k) (U i k)]
  rw [jacobiMat_mulVec_apply] at hcol
  have hU : extV (fun j => U j k) n = U i k := extV_nat _ i n hi
  have hev : ∀ m, eigVec U k m = extV (fun j => U j k) m := fun m => rfl
  simp only [hi] at hcol
  unfold FormalResearch.JacobiEigenvectors.Engine.Lop SymbolFamily.diagQ
  simp only [hev]
  rw [hU]
  linarith [hcol]

/-- The Jacobi matrix is real symmetric. -/
theorem jacobiMat_isHermitian (F : SymbolFamily Par) (μ : Par) (N : ℕ) : (F.jacobiMat μ N).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  rw [Matrix.conjTranspose_apply, star_trivial]
  unfold SymbolFamily.jacobiMat
  simp only [Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> first | omega | simp_all

/-- **Spectral theorem for the Jacobi matrix** (`main_results` Section 1.1, `thmA` Section 4.1): if `G_h > 0` on the nodes, there is an
eigen-system `X_0 > ... > X_N`, `U` orthogonal with columns `Psi_k`, and `(Psi_k)_0 > 0`. -/
theorem exists_eigenSystem (F : SymbolFamily Par) (μ : Par) (N : ℕ)
    (hG : ∀ n : ℤ, 0 ≤ n → n < N → 0 < F.Gh μ (F.step N) (sNode (F.step N) n)) :
    ∃ (X : Fin (N + 1) → ℝ) (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X U := by
  have hpos : ∀ n : ℤ, 0 ≤ n → n < N → 0 < F.bondA μ N n := fun n h0 h1 => bondA_pos F μ N hG n h0 h1
  have hH : (F.jacobiMat μ N).IsHermitian := jacobiMat_isHermitian F μ N
  set J := F.jacobiMat μ N with hJ
  set lam : Fin (N + 1) → ℝ := hH.eigenvalues with hlam
  set W : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := (hH.eigenvectorUnitary : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    with hW
  have heig : ∀ j, J *ᵥ (fun i => W i j) = lam j • (fun i => W i j) := fun j => hH.mulVec_eigenvectorBasis j
  have hWtW : Wᵀ * W = 1 := by
    have h := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have horth : ∀ a b, ∑ i, W i a * W i b = if a = b then 1 else 0 := by
    intro a b
    have h := congrFun (congrFun hWtW a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  -- the first entries of the eigenvectors do not vanish
  have hfirst : ∀ j, W 0 j ≠ 0 := by
    intro j hj0
    have hz := eig_first_zero F μ N hpos (lam j) (fun i => W i j) (heig j) hj0
    have hW0 : ∀ i, W i j = 0 := fun i => congrFun hz i
    have h := horth j j
    simp [hW0] at h
  -- distinct eigenvalues: two eigenvectors with equal eigenvalue are proportional
  have hdist : ∀ i j, i ≠ j → lam i ≠ lam j := by
    intro i j hij hl
    set c : ℝ := W 0 j / W 0 i with hc
    have hc0 : c ≠ 0 := div_ne_zero (hfirst j) (hfirst i)
    have hv : J *ᵥ (fun m => W m j - c * W m i) = lam j • (fun m => W m j - c * W m i) := by
      funext m
      have e1 := congrFun (heig j) m
      have e2 := congrFun (heig i) m
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
      calc ∑ k, J m k * (W k j - c * W k i)
          = ∑ k, J m k * W k j - c * ∑ k, J m k * W k i := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl (fun k _ => by ring)
        _ = lam j * (W m j - c * W m i) := by
            rw [e1, e2, hl]
            ring
    have hzero := eig_first_zero F μ N hpos (lam j) (fun m => W m j - c * W m i) hv (by
      show W 0 j - c * W 0 i = 0
      rw [hc, div_mul_cancel₀ _ (hfirst i)]
      ring)
    have hcW : ∀ m, W m j = c * W m i := by
      intro m
      have := congrFun hzero m
      simp only [Pi.zero_apply] at this
      linarith
    have h1 := horth i j
    have h2 := horth i i
    rw [if_neg hij] at h1
    rw [if_pos rfl] at h2
    have h3 : ∑ m, W m i * W m j = c * ∑ m, W m i * W m i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by rw [hcW m]; ring)
    rw [h1, h2, mul_one] at h3
    exact hc0 h3.symm
  -- sort the eigenvalues decreasingly
  set σ : Equiv.Perm (Fin (N + 1)) := Tuple.sort (fun j => -lam j) with hσ
  have hmono : Monotone ((fun j => -lam j) ∘ σ) := Tuple.monotone_sort _
  have hanti : Antitone (fun k => lam (σ k)) := by
    intro k l hkl
    have h := hmono hkl
    simp only [Function.comp, neg_le_neg_iff] at h
    exact h
  have hinj : Function.Injective (fun k => lam (σ k)) := by
    intro k l hkl
    by_contra hne
    exact hdist (σ k) (σ l) (fun h => hne (σ.injective h)) hkl
  have hstrict : StrictAnti (fun k => lam (σ k)) := hanti.strictAnti_of_injective hinj
  -- the gauge: the sign making the first entry positive
  set s : Fin (N + 1) → ℝ := fun k => if 0 < W 0 (σ k) then 1 else -1 with hs
  set U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ := Matrix.of fun i k => s k * W i (σ k) with hU
  have hs_sq : ∀ k, s k * s k = 1 := by
    intro k
    simp only [hs]
    split_ifs <;> norm_num
  have hU0 : ∀ k, 0 < U 0 k := by
    intro k
    simp only [hU, Matrix.of_apply, hs]
    rcases lt_or_gt_of_ne (hfirst (σ k)) with h | h
    · rw [if_neg (not_lt.mpr h.le)]
      linarith
    · rw [if_pos h]
      linarith
  refine ⟨fun k => lam (σ k), U, ⟨?_, ?_, hstrict, fun k => hU0 k⟩⟩
  · -- orthonormality of the columns
    ext k l
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, hU, Matrix.of_apply]
    have h1 : ∑ i, s k * W i (σ k) * (s l * W i (σ l)) = s k * s l * ∑ i, W i (σ k) * W i (σ l) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [h1, horth]
    by_cases hkl : k = l
    · subst hkl
      simp [hs_sq]
    · have hne : σ k ≠ σ l := fun h => hkl (σ.injective h)
      simp [hne, hkl]
  · -- the eigen equation `J U = U diag X`
    ext i k
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [hU, Matrix.of_apply]
    have e := congrFun (heig (σ k)) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e
    have h1 : ∑ j, J i j * (s k * W j (σ k)) = s k * ∑ j, J i j * W j (σ k) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [h1, e]
    ring

/-- info: 'FormalResearch.JacobiEigenvectors.Setting.bondA_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Setting.bondA_pos

/-- info: 'FormalResearch.JacobiEigenvectors.Setting.eigVec_JacSol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Setting.eigVec_JacSol

/-- info: 'FormalResearch.JacobiEigenvectors.Setting.exists_eigenSystem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Setting.exists_eigenSystem

end FormalResearch.JacobiEigenvectors.Setting

end
