module

public import Mathlib
public import FormalResearch.JB.JBOneStepDef
public import FormalResearch.JacobiEigenvectors.TheoremB.ComparisonMatrix

/-!
# Paper J, Theorem B, L3.5c (assembly of `PropThbInputs`), part 1: the block decomposition of the columns

Source: Paper J `app_thmB.tex`, (S1) "blocks": the columns of `hat G^{[r]}` are split by the energy `X_k` into the bulk blocks `nu < nb` (the least bulk block containing `X_k`, `blockOf`), the upper soft edge (`X_k > J_hi`, in no
block) and the lower soft edge (the remaining energies).  This is exactly the case split of `compColumn`, so each column of `compMatrix` is the corresponding `bulkColAt` / `softColAt`.

* `thbCols CI Xs : Fin (CI.nb + 2) -> Finset (Fin (N+1))`: block `nu < nb` is bulk block `nu`, block `nb` the upper soft edge, block `nb + 1` the lower soft edge.
* `thbCols_disjoint` (`OneStepInputs.cols_disjoint`), `mem_thbCols_iff`, `exists_mem_thbCols` (every column lies in a block).
* `compColumn_bulk`, `compColumn_up`, `compColumn_lo`: the three cases of `compColumn`; `compMatrix_apply_*`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
open scoped Classical

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
  (CI : ChartInputs F K Kidx t0 m q U V cPC CPC)

/-- The block of an energy: bulk block `nu` (`nu < nb`), `nb` the upper soft edge, `nb + 1` the lower soft edge. -/
def thbBlock (X : ℝ) : Fin (CI.nb + 2) :=
  match blockOf CI X with
  | some ν => ⟨ν.val, by omega⟩
  | none => if CI.Jhi < X then ⟨CI.nb, by omega⟩ else ⟨CI.nb + 1, by omega⟩

/-- The column set of block `nu`: the columns whose energy lies in it. -/
def thbCols {N : ℕ} (Xs : Fin (N + 1) → ℝ) (ν : Fin (CI.nb + 2)) : Finset (Fin (N + 1)) :=
  Finset.univ.filter (fun k => thbBlock CI (Xs k) = ν)

theorem mem_thbCols_iff {N : ℕ} (Xs : Fin (N + 1) → ℝ) (ν : Fin (CI.nb + 2)) (k : Fin (N + 1)) :
    k ∈ thbCols CI Xs ν ↔ thbBlock CI (Xs k) = ν := by
  simp [thbCols]

theorem thbCols_disjoint {N : ℕ} (Xs : Fin (N + 1) → ℝ) (ν ν' : Fin (CI.nb + 2)) (h : ν ≠ ν') :
    Disjoint (thbCols CI Xs ν) (thbCols CI Xs ν') := by
  rw [Finset.disjoint_left]
  intro k hk hk'
  rw [mem_thbCols_iff] at hk hk'
  exact h (hk.symm.trans hk')

theorem exists_mem_thbCols {N : ℕ} (Xs : Fin (N + 1) → ℝ) (k : Fin (N + 1)) : ∃ ν, k ∈ thbCols CI Xs ν :=
  ⟨thbBlock CI (Xs k), (mem_thbCols_iff CI Xs _ k).mpr rfl⟩

theorem thbBlock_bulk (X : ℝ) (ν : Fin CI.nb) (h : blockOf CI X = some ν) : thbBlock CI X = ⟨ν.val, by omega⟩ := by
  unfold thbBlock; rw [h]

theorem thbBlock_up (X : ℝ) (h : blockOf CI X = none) (hX : CI.Jhi < X) : thbBlock CI X = ⟨CI.nb, by omega⟩ := by
  unfold thbBlock; rw [h]; simp [hX]

theorem thbBlock_lo (X : ℝ) (h : blockOf CI X = none) (hX : ¬ CI.Jhi < X) : thbBlock CI X = ⟨CI.nb + 1, by omega⟩ := by
  unfold thbBlock; rw [h]; simp [hX]

/-- block `nu < nb`: the energy lies in the bulk block `nu` and in no earlier one. -/
theorem thbBlock_eq_bulk_iff (X : ℝ) (ν : Fin CI.nb) :
    thbBlock CI X = ⟨ν.val, by omega⟩ ↔ blockOf CI X = some ν := by
  constructor
  · intro h
    unfold thbBlock at h
    cases hb : blockOf CI X with
    | none =>
      rw [hb] at h
      have hν := ν.isLt
      by_cases hX : CI.Jhi < X
      · simp [hX, Fin.ext_iff] at h; omega
      · simp [hX, Fin.ext_iff] at h; omega
    | some ν' =>
      rw [hb] at h
      simp only [Fin.mk.injEq] at h
      rw [Option.some.injEq]
      exact Fin.ext h
  · exact thbBlock_bulk CI X ν

theorem blockOf_some {X : ℝ} {ν : Fin CI.nb} (h : blockOf CI X = some ν) : CI.lo ν ≤ X ∧ X ≤ CI.hi ν := by
  unfold blockOf at h
  by_cases hex : ∃ ν : Fin CI.nb, CI.lo ν ≤ X ∧ X ≤ CI.hi ν
  · rw [dif_pos hex, Option.some.injEq] at h
    rw [← h]; exact blockIdx_spec CI X hex
  · rw [dif_neg hex] at h
    simp at h

theorem blockOf_none {X : ℝ} (h : blockOf CI X = none) : ∀ ν : Fin CI.nb, ¬ (CI.lo ν ≤ X ∧ X ≤ CI.hi ν) := by
  intro ν hν
  unfold blockOf at h
  by_cases hex : ∃ ν : Fin CI.nb, CI.lo ν ≤ X ∧ X ≤ CI.hi ν
  · rw [dif_pos hex] at h
    simp at h
  · exact hex ⟨ν, hν⟩

variable (spl : Fin CI.nb → ℝ) (μ : Par) (N : ℕ)

theorem compColumn_bulk (X : ℝ) (ν : Fin CI.nb) (h : blockOf CI X = some ν) (n : ℤ) :
    compColumn CI spl μ N X n = bulkColAt (CI.bulkL ν) (CI.bulkR ν) (atStep F μ N) X N (nearestRow (F.step N) (spl ν)) n := by
  have hex : ∃ ν : Fin CI.nb, CI.lo ν ≤ X ∧ X ≤ CI.hi ν := ⟨ν, blockOf_some CI h⟩
  have hb : blockIdx CI X hex = ν := by
    unfold blockOf at h
    rw [dif_pos hex, Option.some.injEq] at h
    exact h
  unfold compColumn
  rw [dif_pos hex, hb]

theorem compColumn_up (X : ℝ) (h : blockOf CI X = none) (hX : CI.Jhi < X) (n : ℤ) :
    compColumn CI spl μ N X n =
      softColAt CI.softUpL CI.softUpR (atStep F μ N) X N (nearestRow (F.step N) (CI.softUpL.uc (atStep F μ N))) n := by
  have hex : ¬ ∃ ν : Fin CI.nb, CI.lo ν ≤ X ∧ X ≤ CI.hi ν := fun ⟨ν, hν⟩ => blockOf_none CI h ν hν
  unfold compColumn
  rw [dif_neg hex, if_pos hX]

theorem compColumn_lo (X : ℝ) (h : blockOf CI X = none) (hX : ¬ CI.Jhi < X) (n : ℤ) :
    compColumn CI spl μ N X n = (-1 : ℝ) ^ n *
      softColAt CI.softLoL CI.softLoR (atStep F μ N) (-X) N (nearestRow (F.step N) (CI.softLoL.uc (atStep F μ N))) n := by
  have hex : ¬ ∃ ν : Fin CI.nb, CI.lo ν ≤ X ∧ X ≤ CI.hi ν := fun ⟨ν, hν⟩ => blockOf_none CI h ν hν
  unfold compColumn
  rw [dif_neg hex, if_neg hX]

end FormalResearch.JacobiEigenvectors.TheoremB

end
