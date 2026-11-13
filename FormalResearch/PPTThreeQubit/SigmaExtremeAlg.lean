module

public import Mathlib
public import FormalResearch.PPTThreeQubit.PartialTranspose
public import FormalResearch.PPTThreeQubit.Basic

/-!
# Face-direction equations as an explicit linear system, over any star ring

For `B : 8 × 5` and a cut `c`, the entries of `(ptG c (B Y B†)) k` are linear in the entries of `Y`:
`(ptG c (B Y B†) *ᵥ k) i = ∑_{a,b} coefD c B k i a b · Y a b`, where `coefD` is the value on the matrix unit
`e_{ab}`.  The coefficients commute with ring homomorphisms that commute with `star`, so the system can be
computed over the exact field `ℚ(ω) = QuadraticAlgebra ℚ (-1) (-1)` and mapped to `ℂ`
(used in `SigmaExtreme.lean`, where the rank is certified by `decide +kernel`).
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix

/-- The partial transpose on qubit `c` (`0 = A`, `1 = B`, `2 = C`) of an `8 × 8` matrix over any type; it agrees
with `ptA`, `ptB`, `ptC` on complex matrices. -/
def ptG {R : Type*} (c : Fin 3) (M : Matrix (Fin 8) (Fin 8) R) : Matrix (Fin 8) (Fin 8) R :=
  match c with
  | 0 => Matrix.of fun i j => M ⟨4 * (j.val / 4) + i.val % 4, by omega⟩ ⟨4 * (i.val / 4) + j.val % 4, by omega⟩
  | 1 => Matrix.of fun i j =>
    M ⟨4 * (i.val / 4) + 2 * (j.val / 2 % 2) + i.val % 2, by omega⟩
      ⟨4 * (j.val / 4) + 2 * (i.val / 2 % 2) + j.val % 2, by omega⟩
  | 2 => Matrix.of fun i j => M ⟨2 * (i.val / 2) + j.val % 2, by omega⟩ ⟨2 * (j.val / 2) + i.val % 2, by omega⟩

theorem ptG_zero (M : Matrix (Fin 8) (Fin 8) ℂ) : ptG 0 M = ptA M := rfl
theorem ptG_one (M : Matrix (Fin 8) (Fin 8) ℂ) : ptG 1 M = ptB M := rfl
theorem ptG_two (M : Matrix (Fin 8) (Fin 8) ℂ) : ptG 2 M = ptC M := rfl

section
variable {R : Type*} [CommRing R] [StarRing R]

/-- `B e_{ab} B†`. -/
def eMat (B : Matrix (Fin 8) (Fin 5) R) (a b : Fin 5) : Matrix (Fin 8) (Fin 8) R :=
  Matrix.vecMulVec (fun i => B i a) (fun j => star (B j b))

/-- The coefficient of `Y a b` in `(ptG c (B Y B†) *ᵥ k) i`. -/
def coefD (c : Fin 3) (B : Matrix (Fin 8) (Fin 5) R) (k : Fin 8 → R) (i : Fin 8) (a b : Fin 5) : R :=
  (ptG c (eMat B a b) *ᵥ k) i

omit [CommRing R] [StarRing R] in
theorem ptG_apply (c : Fin 3) (M : Matrix (Fin 8) (Fin 8) R) (i j : Fin 8) :
    ptG c M i j = M (match c with
      | 0 => ⟨4 * (j.val / 4) + i.val % 4, by omega⟩
      | 1 => ⟨4 * (i.val / 4) + 2 * (j.val / 2 % 2) + i.val % 2, by omega⟩
      | 2 => ⟨2 * (i.val / 2) + j.val % 2, by omega⟩)
      (match c with
      | 0 => ⟨4 * (i.val / 4) + j.val % 4, by omega⟩
      | 1 => ⟨4 * (j.val / 4) + 2 * (i.val / 2 % 2) + j.val % 2, by omega⟩
      | 2 => ⟨2 * (j.val / 2) + i.val % 2, by omega⟩) := by
  fin_cases c <;> rfl

omit [StarRing R] in
theorem sum3_reorder {ι κ ℓ : Type*} [Fintype ι] [Fintype κ] [Fintype ℓ] (f : ι → κ → ℓ → R) :
    ∑ i, ∑ k, ∑ l, f i k l = ∑ l, ∑ k, ∑ i, f i k l := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm]
  rw [Finset.sum_comm]

/-- Linearity: the face-direction equations are the linear forms `coefD`. -/
theorem mulVec_ptG_sandwich (c : Fin 3) (B : Matrix (Fin 8) (Fin 5) R) (k : Fin 8 → R)
    (Y : Matrix (Fin 5) (Fin 5) R) (i : Fin 8) :
    (ptG c (B * Y * Bᴴ) *ᵥ k) i = ∑ a, ∑ b, coefD c B k i a b * Y a b := by
  simp only [coefD, eMat, mulVec, dotProduct, ptG_apply, Matrix.mul_apply, conjTranspose_apply,
    vecMulVec_apply, Finset.sum_mul]
  refine (sum3_reorder _).trans ?_
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Ring homomorphisms commuting with `star` carry the coefficients over. -/
theorem coefD_map {S : Type*} [CommRing S] [StarRing S] (f : R →+* S) (hf : ∀ x, f (star x) = star (f x))
    (c : Fin 3) (B : Matrix (Fin 8) (Fin 5) R) (k : Fin 8 → R) (i : Fin 8) (a b : Fin 5) :
    coefD c (B.map f) (fun j => f (k j)) i a b = f (coefD c B k i a b) := by
  simp only [coefD, eMat, mulVec, dotProduct, ptG_apply, vecMulVec_apply, Matrix.map_apply, hf,
    map_sum, map_mul]

end

/-! ### `ℚ(ω)` and its map to `ℂ` -/

/-- `ℚ(ω)`, `ω² = -1 - ω`, with exact decidable arithmetic. -/
abbrev Kω := QuadraticAlgebra ℚ (-1) (-1)

/-- The embedding `ℚ(ω) → ℂ`, `ω ↦ e^{2πi/3}`. -/
noncomputable def φω : Kω →ₐ[ℚ] ℂ :=
  QuadraticAlgebra.lift ⟨ω, by
    have := ω_sq_add_ω_add_one
    simp only [neg_smul, one_smul]
    linear_combination this⟩

end FormalResearch.PPTThreeQubit
