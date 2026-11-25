module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Setting.EigenSystem

/-!
# Paper J: transport of eigen-systems through the gauge `-(-1)^n J (-1)^n` (the lower soft edge, L2.S6 / L3.2)

Source: Paper J `app_thmA.tex`, proof of `thm:smo-BSr` ("At the lower edge apply the same to the matrix `-(-1)^n J~_h^{(t)} (-1)^n` (bonds `a_n`, diagonal `-B_n`), whose spectrum is `-X_k(t)` with index
`N - k` from the top"), and `thmB.tex` / `app_thmB.tex` ("A column in `Sigma^-` is `D_-` times such a vector for `-D_- J_h D_-`, and `D_- Psi_k` is the eigenvector of `-D_- J_h D_-` in the gauge `(.)_0 > 0`").
`negFamily F` of `Setting/JacobiFamily.lean` is the family of that matrix.

## Proved here (axiom-pinned)

* `negConj J = -(D J D)` (`D = diag((-1)^n)`), and `jacobiMat_neg`: `(negFamily F).jacobiMat mu N = negConj (F.jacobiMat mu N)` (entrywise, `jacobiMat_neg_apply`).
* **The transport `IsEigenSystem.negConj`**: if `IsEigenSystem J X U` then `IsEigenSystem (negConj J) (negX X) (negU U)` with the exact conventions
  `negX X i = -X (rev i)` and `negU U j i = (-1)^j U j (rev i)` (`rev = Fin.rev`: `rev i = N - i`; the order reversal `X_0 > ... > X_N` becomes `-X_N > ... > -X_0`, the column `i` of the new system is the column `N - i` of the old one, and the gauge `(.)_0 > 0` is unchanged because `D_0 = 1`).
  `IsEigenSystem.neg` is the same statement for `F.jacobiMat`.  `negX_negX`, `negU_negU`, `negConj_negConj`: the transport is an involution, so it is a bijection of eigen-systems (`IsEigenSystem.neg_iff`).
* `eigVec_negU`: the eigenvector transport `eigVec (negU U) i n = (-1)^n eigVec U (rev i) n` for every `n : Z` (zero outside `0..N` on both sides), with `negX X (rev k) = -X k`
  (`negX_rev`): the eigenvector of the gauge family at the energy `-X_k` is `D Psi_k` (`eigVec_negU_rev`).  Consistent with `negFamily_JacSol`.
* **Frozen family**: `negFrozen_jacobiMat_at_step`: `(negFamily (frozenFamily F Kidx)).jacobiMat (mu, step N) N = (negFamily F).jacobiMat mu N`, and `IsEigenSystem.neg_frozen`: an eigen-system of
  `F.jacobiMat mu N` transports to one of the chart family `negFamily (frozenFamily F Kidx)` at the parameter `(mu, step N)` (= `atStep F mu N`).
* **Band ends**: `negFamily_bandHi`: `(negFamily F).bandHi mu = - F.bandLo mu`, `negFamily_bandLo` (for the frozen family too: `negFrozen_bandHi`).

## Differences from the paper

None; the index conventions that the paper leaves implicit are fixed here (`rev`, `negU`).  The paper's "index `N - k` from the top" is `rev k`.

## Not formalised

Nothing in this file is conditional.  The consequences for the lower soft window and the lower soft columns are in `SpectrumAssemblyLower.lean` and `TheoremB/NegColumns.lean`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Setting

open Finset
open scoped Matrix Pointwise

variable {Par : Type*}

/-! ### The matrix `-D J D` -/

/-- `-D J D` with `D = diag((-1)^n)`: the matrix of the gauge family `negFamily` (bonds unchanged, diagonal negated). -/
def negConj {N : ℕ} (J : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun i j => -((-1 : ℝ) ^ (i : ℕ) * J i j * (-1 : ℝ) ^ (j : ℕ))

theorem negConj_negConj {N : ℕ} (J : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : negConj (negConj J) = J := by
  ext i j
  simp only [negConj, Matrix.of_apply]
  have h1 : (-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have h2 : (-1 : ℝ) ^ (j : ℕ) * (-1 : ℝ) ^ (j : ℕ) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  calc -((-1 : ℝ) ^ (i : ℕ) * -((-1 : ℝ) ^ (i : ℕ) * J i j * (-1 : ℝ) ^ (j : ℕ)) * (-1 : ℝ) ^ (j : ℕ))
      = ((-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ)) * J i j * ((-1 : ℝ) ^ (j : ℕ) * (-1 : ℝ) ^ (j : ℕ)) := by ring
    _ = J i j := by rw [h1, h2]; ring

theorem negFamily_entryB (F : SymbolFamily Par) (μ : Par) (N : ℕ) (n : ℤ) :
    (negFamily F).entryB μ N n = -F.entryB μ N n := rfl

theorem negFamily_entryE (F : SymbolFamily Par) (μ : Par) (N : ℕ) (n : ℤ) :
    (negFamily F).entryE μ N n = F.entryE μ N n := rfl

/-- The entry of the gauge family's matrix: `(J')_{ij} = -(-1)^i J_{ij} (-1)^j`. -/
theorem jacobiMat_neg_apply (F : SymbolFamily Par) (μ : Par) (N : ℕ) (i j : Fin (N + 1)) :
    (negFamily F).jacobiMat μ N i j = -((-1 : ℝ) ^ (i : ℕ) * F.jacobiMat μ N i j * (-1 : ℝ) ^ (j : ℕ)) := by
  have h1 : ∀ n : ℕ, (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := fun n => by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  unfold SymbolFamily.jacobiMat
  simp only [Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    simp only [if_true]
    rw [negFamily_entryB]
    calc -F.entryB μ N (i.val : ℤ) = -(((-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ)) * F.entryB μ N (i.val : ℤ)) := by rw [h1]; ring
      _ = _ := by ring
  · rw [if_neg hij, if_neg hij]
    by_cases h2 : j.val = i.val + 1
    · rw [if_pos h2, if_pos h2]
      rw [h2, pow_succ, negFamily_bondA]
      calc F.bondA μ N (i.val : ℤ) = -(((-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ)) * F.bondA μ N (i.val : ℤ) * (-1)) := by
            rw [h1]; ring
        _ = _ := by ring
    · rw [if_neg h2, if_neg h2]
      by_cases h3 : i.val = j.val + 1
      · rw [if_pos h3, if_pos h3]
        rw [h3, pow_succ, negFamily_bondA]
        calc F.bondA μ N (j.val : ℤ) = -(((-1 : ℝ) ^ (j : ℕ) * (-1 : ℝ) ^ (j : ℕ)) * F.bondA μ N (j.val : ℤ) * (-1)) := by
              rw [h1]; ring
          _ = _ := by ring
      · rw [if_neg h3, if_neg h3]; ring

theorem jacobiMat_neg (F : SymbolFamily Par) (μ : Par) (N : ℕ) :
    (negFamily F).jacobiMat μ N = negConj (F.jacobiMat μ N) := by
  ext i j
  rw [jacobiMat_neg_apply]
  rfl

/-! ### The eigen-system transport -/

/-- The eigenvalues of the transported system: `-X_{N-i}` (so that they are again decreasing). -/
def negX {N : ℕ} (X : Fin (N + 1) → ℝ) : Fin (N + 1) → ℝ := fun i => -X (Fin.rev i)

/-- The eigenvector matrix of the transported system: column `i` is `D` times column `N - i`, `D = diag((-1)^n)`. -/
def negU {N : ℕ} (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun j i => (-1 : ℝ) ^ (j : ℕ) * U j (Fin.rev i)

theorem negX_negX {N : ℕ} (X : Fin (N + 1) → ℝ) : negX (negX X) = X := by
  funext i
  simp [negX]

theorem negU_negU {N : ℕ} (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : negU (negU U) = U := by
  ext j i
  simp only [negU, Matrix.of_apply, Fin.rev_rev]
  have h1 : (-1 : ℝ) ^ (j : ℕ) * (-1 : ℝ) ^ (j : ℕ) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  calc (-1 : ℝ) ^ (j : ℕ) * ((-1 : ℝ) ^ (j : ℕ) * U j i) = ((-1 : ℝ) ^ (j : ℕ) * (-1 : ℝ) ^ (j : ℕ)) * U j i := by ring
    _ = U j i := by rw [h1]; ring

theorem negX_rev {N : ℕ} (X : Fin (N + 1) → ℝ) (k : Fin (N + 1)) : negX X (Fin.rev k) = -X k := by
  simp [negX]

theorem negU_rev {N : ℕ} (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (j k : Fin (N + 1)) :
    negU U j (Fin.rev k) = (-1 : ℝ) ^ (j : ℕ) * U j k := by
  simp [negU]

/-- **The eigen-system transport** (index conventions made exact): an eigen-system of `J` gives the eigen-system `(negX X, negU U)` of `-D J D`. -/
theorem IsEigenSystem.negConj {N : ℕ} {J : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} {X : Fin (N + 1) → ℝ}
    {U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hE : IsEigenSystem J X U) :
    IsEigenSystem (_root_.FormalResearch.JacobiEigenvectors.Setting.negConj J) (negX X) (negU U) := by
  have h1 : ∀ n : ℕ, (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := fun n => by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- orthogonality
    ext a b
    have h := congrFun (congrFun hE.orth (Fin.rev a)) (Fin.rev b)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h ⊢
    simp only [negU, Matrix.of_apply]
    have e : ∀ j : Fin (N + 1), (-1 : ℝ) ^ (j : ℕ) * U j (Fin.rev a) * ((-1 : ℝ) ^ (j : ℕ) * U j (Fin.rev b)) =
        U j (Fin.rev a) * U j (Fin.rev b) := fun j => by
      calc _ = ((-1 : ℝ) ^ (j : ℕ) * (-1 : ℝ) ^ (j : ℕ)) * (U j (Fin.rev a) * U j (Fin.rev b)) := by ring
        _ = _ := by rw [h1]; ring
    rw [Finset.sum_congr rfl (fun j _ => e j), h]
    simp [Fin.rev_inj]
  · -- the eigen equation
    ext j i
    have h := congrFun (congrFun hE.eig j) (Fin.rev i)
    rw [Matrix.mul_diagonal, Matrix.mul_apply] at h
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [negU, negX, Matrix.of_apply, _root_.FormalResearch.JacobiEigenvectors.Setting.negConj]
    have e : ∀ l : Fin (N + 1), -((-1 : ℝ) ^ (j : ℕ) * J j l * (-1 : ℝ) ^ (l : ℕ)) * ((-1 : ℝ) ^ (l : ℕ) * U l (Fin.rev i)) =
        -((-1 : ℝ) ^ (j : ℕ)) * (J j l * U l (Fin.rev i)) := fun l => by
      calc _ = -((-1 : ℝ) ^ (j : ℕ)) * (J j l * U l (Fin.rev i)) * ((-1 : ℝ) ^ (l : ℕ) * (-1 : ℝ) ^ (l : ℕ)) := by ring
        _ = _ := by rw [h1]; ring
    rw [Finset.sum_congr rfl (fun l _ => e l), ← Finset.mul_sum, h]
    ring
  · intro a b hab
    have h1 : Fin.rev b < Fin.rev a := Fin.rev_lt_rev.mpr hab
    have := hE.anti h1
    simp only [negX]
    linarith
  · intro i
    simp only [negU, Matrix.of_apply]
    simpa using hE.pos (Fin.rev i)

/-- The transport for the Jacobi matrix of a family: the matrix of `negFamily F`. -/
theorem IsEigenSystem.neg {F : SymbolFamily Par} {μ : Par} {N : ℕ} {X : Fin (N + 1) → ℝ}
    {U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hE : IsEigenSystem (F.jacobiMat μ N) X U) :
    IsEigenSystem ((negFamily F).jacobiMat μ N) (negX X) (negU U) := by
  rw [jacobiMat_neg]
  exact hE.negConj

/-- The transport is an involution, hence a bijection of eigen-systems. -/
theorem IsEigenSystem.neg_iff {F : SymbolFamily Par} {μ : Par} {N : ℕ} {X : Fin (N + 1) → ℝ}
    {U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} :
    IsEigenSystem ((negFamily F).jacobiMat μ N) (negX X) (negU U) ↔ IsEigenSystem (F.jacobiMat μ N) X U := by
  refine ⟨fun h => ?_, fun h => h.neg⟩
  have h2 := h.neg (F := negFamily F)
  have e : (negFamily (negFamily F)).jacobiMat μ N = F.jacobiMat μ N := by
    rw [jacobiMat_neg, jacobiMat_neg, negConj_negConj]
  rw [e, negX_negX, negU_negU] at h2
  exact h2

/-! ### Eigenvectors -/

/-- **Eigenvector transport**: `Psi'_i = D Psi_{N-i}` on `Z` (both sides vanish outside `0..N`). -/
theorem eigVec_negU {N : ℕ} (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (i : Fin (N + 1)) (n : ℤ) :
    eigVec (negU U) i n = (-1 : ℝ) ^ n * eigVec U (Fin.rev i) n := by
  unfold eigVec
  by_cases hn : 0 ≤ n ∧ n ≤ (N : ℤ)
  · rw [dif_pos hn, dif_pos hn]
    simp only [negU, Matrix.of_apply]
    have : (-1 : ℝ) ^ n = (-1 : ℝ) ^ (n.toNat) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hn.1]
    rw [this]
  · rw [dif_neg hn, dif_neg hn]; ring

/-- The eigenvector of the gauge family at the energy `-X_k` (column `rev k` of the transported system) is `D Psi_k`. -/
theorem eigVec_negU_rev {N : ℕ} (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (k : Fin (N + 1)) (n : ℤ) :
    eigVec (negU U) (Fin.rev k) n = (-1 : ℝ) ^ n * eigVec U k n := by
  rw [eigVec_negU, Fin.rev_rev]

/-- The same in the other direction: `Psi_k = D Psi'_{rev k}`. -/
theorem eigVec_eq_neg_negU {N : ℕ} (U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (k : Fin (N + 1)) (n : ℤ) :
    eigVec U k n = (-1 : ℝ) ^ n * eigVec (negU U) (Fin.rev k) n := by
  rw [eigVec_negU_rev]
  have : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; norm_num
  calc eigVec U k n = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) * eigVec U k n := by rw [this]; ring
    _ = _ := by ring

/-! ### The frozen chart family and the band ends -/

/-- At `t = h` the gauge family of the frozen family is the gauge family of `F`. -/
theorem negFrozen_jacobiMat_at_step (F : SymbolFamily Par) (Kidx : ℕ) (μ : Par) (N : ℕ) :
    (negFamily (frozenFamily F Kidx)).jacobiMat (μ, F.step N) N = (negFamily F).jacobiMat μ N := by
  rw [jacobiMat_neg, frozenFamily_jacobiMat_at_step, jacobiMat_neg]

/-- An eigen-system of `J_h(mu)` transports to an eigen-system of the matrix of the chart family `negFamily (frozenFamily F Kidx)` at `(mu, step N)`. -/
theorem IsEigenSystem.neg_frozen {F : SymbolFamily Par} {Kidx : ℕ} {μ : Par} {N : ℕ} {X : Fin (N + 1) → ℝ}
    {U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hE : IsEigenSystem (F.jacobiMat μ N) X U) :
    IsEigenSystem ((negFamily (frozenFamily F Kidx)).jacobiMat (μ, F.step N) N) (negX X) (negU U) := by
  rw [negFrozen_jacobiMat_at_step]
  exact hE.neg

/-- `X_s^+` of the gauge family is `-X_s^-` of the original (`f_+(-B_0) = -f_-(B_0)`). -/
theorem negFamily_bandHi (F : SymbolFamily Par) (μ : Par) : (negFamily F).bandHi μ = -F.bandLo μ := by
  unfold SymbolFamily.bandHi SymbolFamily.bandLo Xsp Xsm
  have himg : fPlus (negFamily F).L ((negFamily F).G 0 μ) ((negFamily F).B 0 μ) '' Set.Icc 0 (negFamily F).L =
      -(fMinus F.L (F.G 0 μ) (F.B 0 μ) '' Set.Icc 0 F.L) := by
    ext y
    simp only [Set.mem_image, Set.mem_neg]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u, hu, ?_⟩
      simp only [fPlus, fMinus, negFamily]
      ring
    · rintro ⟨u, hu, hy⟩
      refine ⟨u, hu, ?_⟩
      simp only [fPlus, fMinus, negFamily] at hy ⊢
      linarith
  rw [himg, Real.sSup_neg]

theorem negFamily_bandLo (F : SymbolFamily Par) (μ : Par) : (negFamily F).bandLo μ = -F.bandHi μ := by
  unfold SymbolFamily.bandHi SymbolFamily.bandLo Xsp Xsm
  have himg : fMinus (negFamily F).L ((negFamily F).G 0 μ) ((negFamily F).B 0 μ) '' Set.Icc 0 (negFamily F).L =
      -(fPlus F.L (F.G 0 μ) (F.B 0 μ) '' Set.Icc 0 F.L) := by
    ext y
    simp only [Set.mem_image, Set.mem_neg]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u, hu, ?_⟩
      simp only [fPlus, fMinus, negFamily]
      ring
    · rintro ⟨u, hu, hy⟩
      refine ⟨u, hu, ?_⟩
      simp only [fPlus, fMinus, negFamily] at hy ⊢
      linarith
  rw [himg, Real.sInf_neg]

/-- The band end of the gauge family of the frozen family: `X_s^+(-D J^{(t)} D) = - X_s^-(J^{(t)})`. -/
theorem negFrozen_bandHi (F : SymbolFamily Par) (Kidx : ℕ) (p : Par × ℝ) :
    (negFamily (frozenFamily F Kidx)).bandHi p = -(frozenFamily F Kidx).bandLo p :=
  negFamily_bandHi _ p

/-- info: 'FormalResearch.JacobiEigenvectors.Setting.jacobiMat_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Setting.jacobiMat_neg

/-- info: 'FormalResearch.JacobiEigenvectors.Setting.IsEigenSystem.negConj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Setting.IsEigenSystem.negConj

/-- info: 'FormalResearch.JacobiEigenvectors.Setting.IsEigenSystem.neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Setting.IsEigenSystem.neg

/-- info: 'FormalResearch.JacobiEigenvectors.Setting.IsEigenSystem.neg_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Setting.IsEigenSystem.neg_iff

/-- info: 'FormalResearch.JacobiEigenvectors.Setting.eigVec_negU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Setting.eigVec_negU

/-- info: 'FormalResearch.JacobiEigenvectors.Setting.eigVec_negU_rev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Setting.eigVec_negU_rev

/-- info: 'FormalResearch.JacobiEigenvectors.Setting.eigVec_eq_neg_negU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Setting.eigVec_eq_neg_negU

/-- info: 'FormalResearch.JacobiEigenvectors.Setting.negFrozen_jacobiMat_at_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Setting.negFrozen_jacobiMat_at_step

/-- info: 'FormalResearch.JacobiEigenvectors.Setting.IsEigenSystem.neg_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Setting.IsEigenSystem.neg_frozen

/-- info: 'FormalResearch.JacobiEigenvectors.Setting.negFamily_bandHi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Setting.negFamily_bandHi

/-- info: 'FormalResearch.JacobiEigenvectors.Setting.negFamily_bandLo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Setting.negFamily_bandLo

/-- info: 'FormalResearch.JacobiEigenvectors.Setting.negFrozen_bandHi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Setting.negFrozen_bandHi

end FormalResearch.JacobiEigenvectors.Setting
