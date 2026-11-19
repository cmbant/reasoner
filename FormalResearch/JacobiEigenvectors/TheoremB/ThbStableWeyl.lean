module

public import FormalResearch.MatrixAnalysis.Spectral.WeylMatrix

/-!
# Paper J, Theorem B, L3.D step 1: Weyl's inequality in Paper J's indexing (`cor:thb-stable`)

Source: Paper J `thmB.tex`, Corollary `cor:thb-stable` (Section `sec:thb-stable`), proof, first step:
for the sorted eigenvalues `X_0 > ... > X_N` of a Hermitian matrix and a Hermitian perturbation of norm `eps`,
`|X'_k - X_k| <= eps`; hence the `X'_k` are simple and `|X_j - X'_k| >= gamma - eps` for `j != k` when
the gaps of `X` are at least `gamma`.

Claim class: **proved** (no hypothesis beyond Hermitian, no new axiom).

## Proved here (axiom-pinned)

* `thbEig hA k`: the `k`-th eigenvalue `X_k` of a Hermitian `(N+1) x (N+1)` matrix, `k : Fin (N+1)`, in
  Paper J's indexing; `thbEig_antitone`: it is decreasing in `k`.
* `thb_weyl_abs_sub_le`: `|X_k(A) - X_k(B)| <= ||A - B||` for every `k`, for Hermitian `A, B` over any
  `RCLike 𝕜` (so real symmetric and complex Hermitian alike), with the spectral norm (`L2` operator norm).
* `thb_weyl_separated`: `gamma - ||A - B|| <= |X_j(A) - X_k(B)|` whenever `gamma <= |X_j(A) - X_k(A)|`.
* `thb_weyl_ne_of_gap`: if `gamma <= |X_j(A) - X_k(A)|` and `2 ||A - B|| < gamma`, then `X_j(B) != X_k(B)`.
* `thb_gap_of_consecutive`: consecutive gaps `X_i - X_{i+1} >= gamma` (the form of `cor:eigen (c)` used by
  Paper J) give `gamma <= X_j - X_k` for all `j < k`.

## Where the analysis is

No new analysis.  `thb_weyl_abs_sub_le` is the repository theorem
`FormalResearch.MatrixAnalysis.Spectral.herm_abs_eigenvalues₀_sub_le_norm`
(`MatrixAnalysis/Spectral/WeylMatrix.lean`, from the Courant--Fischer min-max in `Spectral/MinMax.lean`), re-indexed
by `Fin (N+1)`.  The Mathlib audit recorded in `CorThbStableNote.lean` is right about Mathlib, which has no Weyl
inequality, but the repository already proves one.

## Differences from the paper

* `A` and `B` are arbitrary Hermitian matrices of the same size; the paper's `J_h` and `J'_h` are a special case.
  The paper's statement needs neither tridiagonality nor reality, and neither is used here.
* The paper's gap is between consecutive eigenvalues; the separation and simplicity lemmas take it for the pair
  `j, k`, and `thb_gap_of_consecutive` supplies that from consecutive gaps.

## Not formalised

The eigenvector part of `cor:thb-stable` (`U'_h Delta` close to `U_h`), the threshold `h'_m(K)`, and the
gap constant `c` of `cor:eigen`; the Fourier--Schur step is in `ThbStableSchur.lean`.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator

namespace FormalResearch.JacobiEigenvectors.TheoremB

variable {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}

/-- The `k`-th eigenvalue `X_k` of a Hermitian `(N+1) x (N+1)` matrix, in Paper J's indexing
(`k : Fin (N+1)`, decreasing in `k`).  Mathlib's list `eigenvalues₀` is reindexed from `Fin (card (Fin (N+1)))`. -/
noncomputable def thbEig {A : Matrix (Fin (N+1)) (Fin (N+1)) 𝕜} (hA : A.IsHermitian)
    (k : Fin (N+1)) : ℝ :=
  hA.eigenvalues₀ (Fin.cast (Fintype.card_fin (N+1)).symm k)

/-- The eigenvalues `X_0 >= X_1 >= ... >= X_N` are decreasing. -/
theorem thbEig_antitone {A : Matrix (Fin (N+1)) (Fin (N+1)) 𝕜} (hA : A.IsHermitian) :
    Antitone (thbEig hA) := by
  intro j k hjk
  unfold thbEig
  apply hA.eigenvalues₀_antitone
  exact hjk

/-- **Weyl's inequality** (Paper J, `cor:thb-stable`, first step): `|X_k(A) - X_k(B)| <= ||A - B||`. -/
theorem thb_weyl_abs_sub_le {A B : Matrix (Fin (N+1)) (Fin (N+1)) 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (k : Fin (N+1)) :
    |thbEig hA k - thbEig hB k| ≤ ‖A - B‖ :=
  FormalResearch.MatrixAnalysis.Spectral.herm_abs_eigenvalues₀_sub_le_norm hA hB _

/-- Separation of eigenvalues of `B` from those of `A`: `gamma - ||A - B|| <= |X_j(A) - X_k(B)|`
whenever `gamma <= |X_j(A) - X_k(A)|`. -/
theorem thb_weyl_separated {A B : Matrix (Fin (N+1)) (Fin (N+1)) 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {γ : ℝ} {j k : Fin (N+1)} (hgap : γ ≤ |thbEig hA j - thbEig hA k|) :
    γ - ‖A - B‖ ≤ |thbEig hA j - thbEig hB k| := by
  have h1 := thb_weyl_abs_sub_le hA hB k
  have h2 : |thbEig hA j - thbEig hA k| ≤
      |thbEig hA j - thbEig hB k| + |thbEig hB k - thbEig hA k| :=
    abs_sub_le (thbEig hA j) (thbEig hB k) (thbEig hA k)
  rw [abs_sub_comm (thbEig hB k) (thbEig hA k)] at h2
  linarith

/-- Simplicity: if `A` has a gap `gamma` between `X_j` and `X_k` and `2 ||A - B|| < gamma`, then the
eigenvalues `X_j(B)` and `X_k(B)` differ. -/
theorem thb_weyl_ne_of_gap {A B : Matrix (Fin (N+1)) (Fin (N+1)) 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) {γ : ℝ} {j k : Fin (N+1)} (hgap : γ ≤ |thbEig hA j - thbEig hA k|)
    (hε : 2 * ‖A - B‖ < γ) : thbEig hB j ≠ thbEig hB k := by
  intro h
  have h1 := thb_weyl_abs_sub_le hA hB j
  have h2 := thb_weyl_abs_sub_le hA hB k
  have e1 : |thbEig hA j - thbEig hA k| ≤
      |thbEig hA j - thbEig hB j| + |thbEig hB j - thbEig hA k| := abs_sub_le _ _ _
  have e2 : |thbEig hB j - thbEig hA k| ≤ |thbEig hB k - thbEig hA k| := by rw [h]
  rw [abs_sub_comm (thbEig hB k) (thbEig hA k)] at e2
  have e3 : |thbEig hA k - thbEig hB k| = |thbEig hB k - thbEig hA k| := abs_sub_comm _ _
  linarith

/-- Consecutive gaps give all pairwise gaps: `gamma <= X_i - X_{i+1}` for all `i` implies
`gamma <= X_j - X_k` for all `j < k`. -/
theorem thb_gap_of_consecutive {A : Matrix (Fin (N+1)) (Fin (N+1)) 𝕜} (hA : A.IsHermitian)
    {γ : ℝ}
    (hcons : ∀ (i : ℕ) (hi : i + 1 < N + 1), γ ≤ thbEig hA ⟨i, by omega⟩ - thbEig hA ⟨i + 1, hi⟩)
    {j k : Fin (N+1)} (hjk : j < k) : γ ≤ thbEig hA j - thbEig hA k := by
  have key : ∀ m : ℕ, ∀ j k : Fin (N+1), k.val = j.val + m + 1 →
      γ * ((m : ℝ) + 1) ≤ thbEig hA j - thbEig hA k := by
    intro m
    induction m with
    | zero =>
      intro j k hk
      have hi : j.val + 1 < N + 1 := by have := k.isLt; omega
      have h0 := hcons j.val hi
      have ej : (⟨j.val, by omega⟩ : Fin (N+1)) = j := Fin.ext rfl
      have ek : (⟨j.val + 1, hi⟩ : Fin (N+1)) = k := Fin.ext (by simp only; omega)
      rw [ej, ek] at h0
      simpa using h0
    | succ m ih =>
      intro j k hk
      have hkpos : 1 ≤ k.val := by omega
      set k' : Fin (N+1) := ⟨k.val - 1, by omega⟩ with hk'
      have hk'v : k'.val = j.val + m + 1 := by simp only [hk']; omega
      have hI := ih j k' hk'v
      have hcon : γ ≤ thbEig hA k' - thbEig hA k := by
        have h0 := hcons k'.val (by omega)
        have e : (⟨k'.val + 1, by omega⟩ : Fin (N+1)) = k := Fin.ext (by simp only [hk']; omega)
        have e' : (⟨k'.val, by omega⟩ : Fin (N+1)) = k' := Fin.ext rfl
        rw [e, e'] at h0
        exact h0
      have e2 : γ * (((m + 1 : ℕ) : ℝ) + 1) = γ * ((m : ℝ) + 1) + γ := by push_cast; ring
      rw [e2]
      linarith
  rcases le_or_gt 0 γ with hγ | hγ
  · have hd : k.val = j.val + (k.val - j.val - 1) + 1 := by
      have := hjk; rw [Fin.lt_def] at this; omega
    have hk := key (k.val - j.val - 1) j k hd
    have hm : (1 : ℝ) ≤ ((k.val - j.val - 1 : ℕ) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ ((k.val - j.val - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    exact le_trans (le_mul_of_one_le_right hγ hm) hk
  · have := thbEig_antitone hA hjk.le
    linarith

end FormalResearch.JacobiEigenvectors.TheoremB

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.thbEig_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.thbEig_antitone

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.thb_weyl_abs_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.thb_weyl_abs_sub_le

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.thb_weyl_separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.thb_weyl_separated

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.thb_weyl_ne_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.thb_weyl_ne_of_gap

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.thb_gap_of_consecutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.thb_gap_of_consecutive
