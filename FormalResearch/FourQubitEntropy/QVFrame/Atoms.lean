module

public import FormalResearch.FourQubitEntropy.QVFrame.Invariants
public import FormalResearch.FourQubitEntropy.QVCert.QVDefect

/-!
# T3, atoms: `N`, `tr R_cut²`, `tr R_cut³` as permutation invariants

* `cutMask j` is the cut `{0, j}`, `cutPerm k m` the per-qubit cyclic slot permutation of `k` copies on the qubits
  of the mask `m` (identity on the others), written so that `⊗_q slotPerm (cutPerm k m q)` is the matrix
  `|c⟩ ↦ |c ∘ rot_k⟩` on the cut qubits of the `routeD/rhs.py` convention (`rot_k : t ↦ t+1`).
* `invG_cut12`: the invariant of the cut `{0,1}` is `Σ_x ∏_t R_{12}(x_t, x_{t+1})`;
  `atom2`, `atom3`: `k = 2, 3` give `tr R²`, `tr R³` for the three cuts (`red12`, `red13`, `red14`).
-/

@[expose] public section


open scoped ComplexConjugate
open scoped Matrix
open Finset

namespace FormalResearch.FourQubitEntropy.QVFrame

open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

/-! ### Sums over `Fin k → A` -/

theorem sum_fin_two {A M : Type*} [Fintype A] [AddCommMonoid M] (f : (Fin 2 → A) → M) :
    ∑ a : Fin 2 → A, f a = ∑ x, ∑ y, f ![x, y] := by
  rw [← (piFinTwoEquiv (fun _ : Fin 2 => A)).symm.sum_comp, Fintype.sum_prod_type]
  rfl

theorem sum_fin_three {A M : Type*} [Fintype A] [AddCommMonoid M] (f : (Fin 3 → A) → M) :
    ∑ a : Fin 3 → A, f a = ∑ x, ∑ y, ∑ w, f ![x, y, w] := by
  rw [← (Fin.consEquiv (fun _ : Fin 3 => A)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sum_fin_two (fun y => f ((Fin.consEquiv (fun _ : Fin 3 => A)) (x, y)))]
  rfl

theorem sum_fin_four {A M : Type*} [Fintype A] [AddCommMonoid M] (f : (Fin 4 → A) → M) :
    ∑ a : Fin 4 → A, f a = ∑ x, ∑ y, ∑ w, ∑ v, f ![x, y, w, v] := by
  rw [← (Fin.consEquiv (fun _ : Fin 4 => A)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sum_fin_three (fun y => f ((Fin.consEquiv (fun _ : Fin 4 => A)) (x, y)))]
  rfl

/-! ### Cuts -/

/-- The cut `{0, j}` as a qubit mask. -/
def cutMask (j : Fin 4) : Fin 4 → Bool := fun q => q == 0 || q == j

/-- The cyclic slot permutation of `k` copies on the masked qubits. -/
def cutPerm (k : ℕ) (m : Fin 4 → Bool) : Fin 4 → Equiv.Perm (Fin k) :=
  fun q => if m q then (finRotate k).symm else 1

/-- `Site ≃ (Fin 2 × Fin 2) × (Fin 2 × Fin 2)`: qubits `(0,1)` and `(2,3)`. -/
def spl : Site ≃ ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) where
  toFun c := ((c 0, c 1), (c 2, c 3))
  invFun x := ![x.1.1, x.1.2, x.2.1, x.2.2]
  left_inv c := by funext q; fin_cases q <;> rfl
  right_inv x := rfl

theorem invG_cut12 (k : ℕ) (z : Psi) :
    invG (Fin k) (cutPerm k (cutMask 1)) (zf z) =
      ∑ x : Fin k → (Fin 2 × Fin 2), ∏ t : Fin k, red12 z (x t) (x (finRotate k t)) := by
  unfold invG
  let E : (Fin k → Site) ≃ (Fin k → (Fin 2 × Fin 2)) × (Fin k → (Fin 2 × Fin 2)) :=
    (Equiv.piCongrRight fun _ => spl).trans (Equiv.arrowProdEquivProdArrow _ _ _)
  rw [← E.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hterm : ∀ y : Fin k → (Fin 2 × Fin 2),
      ∏ t : Fin k, conj (zf z (fun q => (E.symm (x, y)) ((cutPerm k (cutMask 1) q).symm t) q)) *
        zf z ((E.symm (x, y)) t) =
      ∏ t : Fin k, conj (z (x (finRotate k t)).1 (x (finRotate k t)).2 (y t).1 (y t).2) *
        z (x t).1 (x t).2 (y t).1 (y t).2 := by
    intro y
    refine Finset.prod_congr rfl fun t _ => ?_
    have hb : (fun q => (E.symm (x, y)) ((cutPerm k (cutMask 1) q).symm t) q) =
        ![(x (finRotate k t)).1, (x (finRotate k t)).2, (y t).1, (y t).2] := by
      funext q
      fin_cases q <;> simp [cutPerm, cutMask, E, Equiv.arrowProdEquivProdArrow] <;> rfl
    have hk : (E.symm (x, y)) t = ![(x t).1, (x t).2, (y t).1, (y t).2] := by
      funext q
      fin_cases q <;> simp [E, Equiv.arrowProdEquivProdArrow] <;> rfl
    rw [hb, hk]
    simp [zf]
  simp only [hterm]
  have := Fintype.prod_sum (fun (t : Fin k) (r : Fin 2 × Fin 2) =>
    conj (z (x (finRotate k t)).1 (x (finRotate k t)).2 r.1 r.2) * z (x t).1 (x t).2 r.1 r.2)
  simp only [← this]
  refine Finset.prod_congr rfl fun t _ => ?_
  simp only [red12, Matrix.of_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

/-! ### `k = 1, 2, 3` -/

theorem atom2_12 (z : Psi) :
    invG (Fin 2) (cutPerm 2 (cutMask 1)) (zf z) = Matrix.trace (red12 z * red12 z) := by
  rw [invG_cut12, sum_fin_two]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.prod_univ_two]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp

theorem atom3_12 (z : Psi) :
    invG (Fin 3) (cutPerm 3 (cutMask 1)) (zf z) = Matrix.trace (red12 z * red12 z * red12 z) := by
  rw [invG_cut12, sum_fin_three]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.prod_univ_three, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun w _ => ?_
  simp

/-- Qubit relabellings turning the cut `{0,1}` into `{0,2}` and `{0,3}`. -/
def rho2 : Equiv.Perm (Fin 4) := Equiv.swap 1 2
def rho3 : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 2 3

theorem mask2 : ∀ q, cutMask 2 q = cutMask 1 (rho2 q) := by decide
theorem mask3 : ∀ q, cutMask 3 q = cutMask 1 (rho3 q) := by decide

theorem cutPerm_mask {k : ℕ} {j : Fin 4} (ρ : Equiv.Perm (Fin 4)) (h : ∀ q, cutMask j q = cutMask 1 (ρ q)) :
    cutPerm k (cutMask j) = fun q => cutPerm k (cutMask 1) (ρ q) := by
  funext q; simp [cutPerm, h q]

/-- The three cuts `{0,1}, {0,2}, {0,3}` and their reduced matrices. -/
def cutIdx : Fin 3 → Fin 4 := ![1, 2, 3]
noncomputable def redC (c : Fin 3) (z : Psi) : Mat4 := ![red12 z, red13 z, red14 z] c

/-- Coordinate-permuted vectors turning `red13`, `red14` into `red12`. -/
def z13 (z : Psi) : Psi := fun a b c d => z a c b d
def z14 (z : Psi) : Psi := fun a b c d => z a c d b

theorem red12_z13 (z : Psi) : red12 (z13 z) = red13 z := by
  ext i j; simp [red12, red13, z13]

theorem red12_z14 (z : Psi) : red12 (z14 z) = red14 z := by
  ext i j; simp [red12, red14, z14]

theorem zf_z13 (z : Psi) : (fun y : Site => zf z (fun q => y (rho2 q))) = zf (z13 z) := by
  funext y; simp [zf, z13, rho2, Equiv.swap_apply_def]

theorem zf_z14 (z : Psi) : (fun y : Site => zf z (fun q => y (rho3 q))) = zf (z14 z) := by
  funext y; simp [zf, z14, rho3, Equiv.swap_apply_def]

/-- `k = 2`: `tr R_c²`, for each of the three cuts. -/
theorem atom2 (c : Fin 3) (z : Psi) :
    invG (Fin 2) (cutPerm 2 (cutMask (cutIdx c))) (zf z) = Matrix.trace (redC c z * redC c z) := by
  fin_cases c
  · exact atom2_12 z
  · show invG (Fin 2) (cutPerm 2 (cutMask 2)) (zf z) = _
    rw [cutPerm_mask rho2 mask2, invG_qperm, zf_z13, atom2_12, red12_z13]; rfl
  · show invG (Fin 2) (cutPerm 2 (cutMask 3)) (zf z) = _
    rw [cutPerm_mask rho3 mask3, invG_qperm, zf_z14, atom2_12, red12_z14]; rfl

/-- `k = 3`: `tr R_c³`, for each of the three cuts. -/
theorem atom3 (c : Fin 3) (z : Psi) :
    invG (Fin 3) (cutPerm 3 (cutMask (cutIdx c))) (zf z) =
      Matrix.trace (redC c z * redC c z * redC c z) := by
  fin_cases c
  · exact atom3_12 z
  · show invG (Fin 3) (cutPerm 3 (cutMask 2)) (zf z) = _
    rw [cutPerm_mask rho2 mask2, invG_qperm, zf_z13, atom3_12, red12_z13]; rfl
  · show invG (Fin 3) (cutPerm 3 (cutMask 3)) (zf z) = _
    rw [cutPerm_mask rho3 mask3, invG_qperm, zf_z14, atom3_12, red12_z14]; rfl

end FormalResearch.FourQubitEntropy.QVFrame
