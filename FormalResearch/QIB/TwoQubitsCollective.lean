import Mathlib
import FormalResearch.FrameFree.HelstromWindow
import FormalResearch.FrameFree.HelstromSupport
import FormalResearch.QIB.TwoQubitsSl2Rank

/-!
# Collective `sl₂` generators on `d` copies of two qubits

Namespace `FormalResearch.QIB.TwoQubits`.  Claim class: **proved** (finite linear algebra).

For the local frame `kron` of `FrameFree.Helstrom` we define the embedding `emb i X` of an operator `X`
into the `i`-th factor of `α^I`, the collective sum `coll X = Σ_i emb i X`, and on `Copies 2 d` the
two-level collective operator `Lc X = coll (coll X)` (first over the two qubits of a copy, then over the
`d` copies).  Proved:

* `coll_commutator`: `[coll X, coll Y] = coll [X, Y]`; hence `coll_matTriple`, `Lc_matTriple`: the
  collective `H, E, F` satisfy the `sl₂` relations;
* `coll_conj`, `Lc_conj`: `rotK d (fun _ => V) * Lc X * rotK d (fun _ => W) = Lc (V X W)` when `V W = 1`;
* `Lc_conjTranspose`: `(Lc X)ᴴ = Lc Xᴴ`;

The two-qubit stabiliser and the Leibniz rule on `d` copies are in `TwoQubitsStabiliser.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Matrix
open FormalResearch.FrameFree.Helstrom

namespace FormalResearch.QIB.TwoQubits

section Generic

variable {I α : Type*} [Fintype I] [DecidableEq I] [Fintype α] [DecidableEq α]

/-- `X` acting on the `i`-th factor of `α^I` and trivially elsewhere. -/
def emb (i : I) (X : Matrix α α ℂ) : Matrix (I → α) (I → α) ℂ :=
  kron (fun j => if j = i then X else 1)

/-- The collective operator `Σ_i X_i`. -/
def coll (X : Matrix α α ℂ) : Matrix (I → α) (I → α) ℂ := ∑ i : I, emb i X

theorem kron_one : kron (fun _ : I => (1 : Matrix α α ℂ)) = 1 := by
  ext x y
  simp only [kron, Matrix.one_apply]
  simp_rw [Finset.prod_boole]
  have h : ∀ y : I → α, (∀ i, x i = y i) ↔ x = y := fun y => (funext_iff).symm
  simp [h]

theorem emb_apply (i : I) (X : Matrix α α ℂ) (x y : I → α) :
    emb i X x y = X (x i) (y i) * ∏ j ∈ Finset.univ.erase i, (1 : Matrix α α ℂ) (x j) (y j) := by
  unfold emb kron
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [↓reduceIte]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  simp [Finset.ne_of_mem_erase hj]

theorem emb_add (i : I) (X Y : Matrix α α ℂ) : emb i (X + Y) = emb i X + emb i Y := by
  ext x y
  simp [emb_apply, add_mul]

theorem emb_sub (i : I) (X Y : Matrix α α ℂ) : emb i (X - Y) = emb i X - emb i Y := by
  ext x y
  simp [emb_apply, sub_mul]

theorem emb_smul (i : I) (c : ℂ) (X : Matrix α α ℂ) : emb i (c • X) = c • emb i X := by
  ext x y
  simp [emb_apply, mul_assoc]

theorem emb_neg (i : I) (X : Matrix α α ℂ) : emb i (-X) = -emb i X := by
  ext x y
  simp [emb_apply]

theorem emb_mul (i : I) (X Y : Matrix α α ℂ) : emb i X * emb i Y = emb i (X * Y) := by
  unfold emb
  rw [kron_mul]
  congr 1
  funext j
  split_ifs <;> simp

theorem emb_comm {i j : I} (h : i ≠ j) (X Y : Matrix α α ℂ) :
    emb i X * emb j Y = emb j Y * emb i X := by
  unfold emb
  rw [kron_mul, kron_mul]
  congr 1
  funext k
  by_cases hki : k = i
  · subst hki
    simp [h]
  · by_cases hkj : k = j
    · subst hkj
      simp [hki]
    · simp [hki, hkj]

theorem emb_conjTranspose (i : I) (X : Matrix α α ℂ) : (emb i X)ᴴ = emb i Xᴴ := by
  unfold emb
  rw [kron_conjTranspose]
  congr 1
  funext j
  split_ifs <;> simp

theorem coll_add (X Y : Matrix α α ℂ) : coll (I := I) (X + Y) = coll X + coll Y := by
  simp [coll, emb_add, Finset.sum_add_distrib]

theorem coll_sub (X Y : Matrix α α ℂ) : coll (I := I) (X - Y) = coll X - coll Y := by
  simp [coll, emb_sub, Finset.sum_sub_distrib]

theorem coll_smul (c : ℂ) (X : Matrix α α ℂ) : coll (I := I) (c • X) = c • coll X := by
  simp [coll, emb_smul, Finset.smul_sum]

theorem coll_neg (X : Matrix α α ℂ) : coll (I := I) (-X) = -coll X := by
  simp [coll, emb_neg, Finset.sum_neg_distrib]

theorem coll_conjTranspose (X : Matrix α α ℂ) : (coll (I := I) X)ᴴ = coll Xᴴ := by
  simp [coll, emb_conjTranspose, Matrix.conjTranspose_sum]

/-- `[Σ X_i, Σ Y_i] = Σ [X, Y]_i`. -/
theorem coll_commutator (X Y : Matrix α α ℂ) :
    coll (I := I) X * coll Y - coll Y * coll X = coll (X * Y - Y * X) := by
  unfold coll
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (f := fun i j => emb i Y * emb j X)]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  have key : ∀ i j : I, emb i X * emb j Y - emb j Y * emb i X
      = if i = j then emb i (X * Y - Y * X) else 0 := by
    intro i j
    by_cases h : i = j
    · subst h
      simp [emb_mul, emb_sub]
    · simp [h, emb_comm h]
  simp_rw [key]
  simp

theorem coll_matTriple {H E F : Matrix α α ℂ} (h : Sl2Kernel.MatTriple H E F) :
    Sl2Kernel.MatTriple (coll (I := I) H) (coll E) (coll F) where
  HE := by rw [coll_commutator, h.HE, coll_smul]
  HF := by rw [coll_commutator, h.HF, coll_neg, coll_smul]
  EF := by rw [coll_commutator, h.EF]

/-- Conjugation of a collective operator by a collective frame. -/
theorem coll_conj (V W X : Matrix α α ℂ) (hVW : V * W = 1) :
    kron (fun _ : I => V) * coll X * kron (fun _ : I => W) = coll (V * X * W) := by
  unfold coll
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold emb
  rw [kron_mul, kron_mul]
  congr 1
  funext j
  split_ifs <;> simp [Matrix.mul_assoc, hVW]

theorem kron_const_mul (V W : Matrix α α ℂ) (hVW : V * W = 1) :
    kron (fun _ : I => V) * kron (fun _ : I => W) = 1 := by
  rw [kron_mul]
  simp only [hVW]
  exact kron_one

end Generic

section TwoLevel

/-- The two-level collective operator on `d` copies of two qubits. -/
def Lc (d : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Copies 2 d) (Copies 2 d) ℂ :=
  coll (I := Fin d) (coll (I := Fin 2) X)

variable {d : ℕ}

theorem Lc_add (X Y : Matrix (Fin 2) (Fin 2) ℂ) : Lc d (X + Y) = Lc d X + Lc d Y := by
  simp [Lc, coll_add]

theorem Lc_sub (X Y : Matrix (Fin 2) (Fin 2) ℂ) : Lc d (X - Y) = Lc d X - Lc d Y := by
  simp [Lc, coll_sub]

theorem Lc_smul (c : ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) : Lc d (c • X) = c • Lc d X := by
  simp [Lc, coll_smul]

theorem Lc_conjTranspose (X : Matrix (Fin 2) (Fin 2) ℂ) : (Lc d X)ᴴ = Lc d Xᴴ := by
  simp [Lc, coll_conjTranspose]

theorem Lc_matTriple {H E F : Matrix (Fin 2) (Fin 2) ℂ} (h : Sl2Kernel.MatTriple H E F) :
    Sl2Kernel.MatTriple (Lc d H) (Lc d E) (Lc d F) :=
  coll_matTriple (coll_matTriple h)

/-- The frame `rotK d (fun _ => V)` conjugates `Lc X` to `Lc (V X W)`. -/
theorem Lc_conj (V W X : Matrix (Fin 2) (Fin 2) ℂ) (hVW : V * W = 1) :
    rotK d (fun _ : Fin 2 => V) * Lc d X * rotK d (fun _ : Fin 2 => W) = Lc d (V * X * W) := by
  unfold Lc rotK
  rw [coll_conj (kron (fun _ : Fin 2 => V)) (kron (fun _ : Fin 2 => W)) _ (kron_const_mul V W hVW)]
  rw [coll_conj V W X hVW]

end TwoLevel

end FormalResearch.QIB.TwoQubits
