module

public import Mathlib

/-!
# Gurvits–Barnum separable ball: definitions

Source: L. Gurvits and H. Barnum, *Largest separable balls around the maximally mixed bipartite
quantum state*, Phys. Rev. A 66, 062311 (2002); plan module M1.

Bipartite operators are matrices over `ι × κ` with the Kronecker product `⊗ₖ`.
* `prodRankOne a b = |a⟩⟨a| ⊗ |b⟩⟨b|`;
* `IsSeparable X`: `X` is a finite sum of such product rank-ones (the cone of unnormalised separable
  operators; positive weights are absorbed into the vectors);
* `IsBlockPositive W`: `⟨a ⊗ b| W |a ⊗ b⟩ ≥ 0` for all product vectors (entanglement witnesses), stated
  on the real part of the quadratic form; `isBlockPositive_iff_trace` gives the trace form and
  `isBlockPositive_iff_forall_separable` the duality form.
-/

@[expose] public section


namespace FormalResearch.GurvitsBarnum

set_option linter.unusedSectionVars false

open Matrix
open scoped Kronecker ComplexOrder

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The Kronecker product vector `a ⊗ b` on `ι × κ`. -/
def kroneckerVec (a : ι → ℂ) (b : κ → ℂ) : ι × κ → ℂ := fun p => a p.1 * b p.2

/-- The product rank-one operator `|a⟩⟨a| ⊗ |b⟩⟨b|`. -/
def prodRankOne (a : ι → ℂ) (b : κ → ℂ) : Matrix (ι × κ) (ι × κ) ℂ :=
  (vecMulVec a (star a)) ⊗ₖ (vecMulVec b (star b))

/-- `X` is separable: a finite sum of product rank-one operators. -/
def IsSeparable (X : Matrix (ι × κ) (ι × κ) ℂ) : Prop :=
  ∃ (N : ℕ) (a : Fin N → ι → ℂ) (b : Fin N → κ → ℂ), X = ∑ i, prodRankOne (a i) (b i)

/-- `W` is block-positive: `Re ⟨a ⊗ b, W (a ⊗ b)⟩ ≥ 0` for all `a, b`. -/
def IsBlockPositive (W : Matrix (ι × κ) (ι × κ) ℂ) : Prop :=
  ∀ (a : ι → ℂ) (b : κ → ℂ), 0 ≤ (star (kroneckerVec a b) ⬝ᵥ (W *ᵥ kroneckerVec a b)).re

theorem prodRankOne_eq (a : ι → ℂ) (b : κ → ℂ) :
    prodRankOne a b = vecMulVec (kroneckerVec a b) (star (kroneckerVec a b)) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [prodRankOne, vecMulVec_apply, kroneckerVec]
  ring

theorem posSemidef_prodRankOne (a : ι → ℂ) (b : κ → ℂ) : (prodRankOne a b).PosSemidef := by
  rw [prodRankOne_eq]; exact posSemidef_vecMulVec_self_star _

theorem trace_mul_prodRankOne (W : Matrix (ι × κ) (ι × κ) ℂ) (a : ι → ℂ) (b : κ → ℂ) :
    trace (W * prodRankOne a b) = star (kroneckerVec a b) ⬝ᵥ (W *ᵥ kroneckerVec a b) := by
  rw [prodRankOne_eq, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

/-- Block positivity in trace form. -/
theorem isBlockPositive_iff_trace (W : Matrix (ι × κ) (ι × κ) ℂ) :
    IsBlockPositive W ↔ ∀ (a : ι → ℂ) (b : κ → ℂ), 0 ≤ (trace (W * prodRankOne a b)).re := by
  simp only [IsBlockPositive, trace_mul_prodRankOne]

/-! ### Separable matrices -/

theorem isSeparable_prodRankOne (a : ι → ℂ) (b : κ → ℂ) : IsSeparable (prodRankOne a b) :=
  ⟨1, fun _ => a, fun _ => b, by simp⟩

theorem isSeparable_zero : IsSeparable (0 : Matrix (ι × κ) (ι × κ) ℂ) :=
  ⟨0, Fin.elim0, Fin.elim0, by simp⟩

theorem IsSeparable.add {X Y : Matrix (ι × κ) (ι × κ) ℂ} (hX : IsSeparable X)
    (hY : IsSeparable Y) : IsSeparable (X + Y) := by
  obtain ⟨N, a, b, rfl⟩ := hX
  obtain ⟨M, c, d, rfl⟩ := hY
  refine ⟨N + M, Fin.append a c, Fin.append b d, ?_⟩
  rw [Fin.sum_univ_add]
  simp

theorem isSeparable_sum {s : Finset ℕ} {f : ℕ → Matrix (ι × κ) (ι × κ) ℂ}
    (h : ∀ i ∈ s, IsSeparable (f i)) : IsSeparable (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using isSeparable_zero
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A finite sum (over any finite index type) of separable matrices is separable. -/
theorem isSeparable_sum' {α : Type*} (s : Finset α) {f : α → Matrix (ι × κ) (ι × κ) ℂ}
    (h : ∀ i ∈ s, IsSeparable (f i)) : IsSeparable (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isSeparable_zero
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Separable matrices are stable under nonnegative real scalings. -/
theorem IsSeparable.smul_nonneg {X : Matrix (ι × κ) (ι × κ) ℂ} (hX : IsSeparable X) {r : ℝ}
    (hr : 0 ≤ r) : IsSeparable (r • X) := by
  obtain ⟨N, a, b, rfl⟩ := hX
  refine ⟨N, fun i => (Real.sqrt r : ℂ) • a i, b, ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr]
  ext ⟨p, k⟩ ⟨q, l⟩
  simp only [prodRankOne, kronecker_apply, vecMulVec_apply, Pi.smul_apply, Pi.star_apply,
    smul_eq_mul, star_mul', Complex.star_def, Complex.conj_ofReal, Matrix.smul_apply,
    Complex.real_smul]
  calc (r : ℂ) * (a i p * (starRingEnd ℂ) (a i q) * (b i k * (starRingEnd ℂ) (b i l)))
      = ((Real.sqrt r : ℂ) * (Real.sqrt r : ℂ)) *
        (a i p * (starRingEnd ℂ) (a i q) * (b i k * (starRingEnd ℂ) (b i l))) := by rw [hs]
    _ = _ := by ring

theorem IsSeparable.posSemidef {X : Matrix (ι × κ) (ι × κ) ℂ} (hX : IsSeparable X) :
    X.PosSemidef := by
  obtain ⟨N, a, b, rfl⟩ := hX
  refine Finset.sum_induction _ (fun M : Matrix (ι × κ) (ι × κ) ℂ => M.PosSemidef) (fun _ _ => Matrix.PosSemidef.add)
    Matrix.PosSemidef.zero fun i _ => posSemidef_prodRankOne _ _

theorem IsSeparable.isHermitian {X : Matrix (ι × κ) (ι × κ) ℂ} (hX : IsSeparable X) :
    X.IsHermitian :=
  hX.posSemidef.isHermitian

/-- Block positivity is equivalent to nonnegativity of `Re tr (W S)` on all separable `S`. -/
theorem isBlockPositive_iff_forall_separable (W : Matrix (ι × κ) (ι × κ) ℂ) :
    IsBlockPositive W ↔ ∀ S, IsSeparable S → 0 ≤ (trace (W * S)).re := by
  rw [isBlockPositive_iff_trace]
  refine ⟨fun h S ⟨N, a, b, hS⟩ => ?_, fun h a b => h _ (isSeparable_prodRankOne a b)⟩
  subst hS
  rw [Finset.mul_sum, trace_sum, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => h _ _

theorem IsBlockPositive.trace_nonneg {W : Matrix (ι × κ) (ι × κ) ℂ} (hW : IsBlockPositive W)
    {S : Matrix (ι × κ) (ι × κ) ℂ} (hS : IsSeparable S) : 0 ≤ (trace (W * S)).re :=
  (isBlockPositive_iff_forall_separable W).1 hW S hS

/-- Positive semidefinite matrices are block-positive. -/
theorem IsBlockPositive.of_posSemidef {W : Matrix (ι × κ) (ι × κ) ℂ} (hW : W.PosSemidef) :
    IsBlockPositive W := fun a b => by
  have := hW.dotProduct_mulVec_nonneg (kroneckerVec a b)
  exact Complex.nonneg_iff.1 this |>.1

theorem IsBlockPositive.add {W V : Matrix (ι × κ) (ι × κ) ℂ} (hW : IsBlockPositive W)
    (hV : IsBlockPositive V) : IsBlockPositive (W + V) := fun a b => by
  simpa [add_mulVec, dotProduct_add] using add_nonneg (hW a b) (hV a b)

end

end FormalResearch.GurvitsBarnum
