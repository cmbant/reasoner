import Mathlib
import FormalResearch.FrameFree.OddWordsSl2

/-!
# The string basis and the commutant of `{L, R}` (Paper P, `prop:oddwords` (iii))

Namespace `FormalResearch.FrameFree.OddWords`.  Claim class: **proved**.

For an `Sl2Data n V` the strings `L^a h_{k,i}` (`h_{k,i}` a basis of `HW_k`, `k ≤ n/2`,
`a ≤ n-2k`) span `V` (`Sl2Data.Str_eq_top`) and number `Σ_k (n-2k+1) dim HW_k = 2^n = dim V`
(`sum_string_dim`), so they form a basis `stringBasis`.  Consequently an operator `Y` commuting with
`L` and `R` is determined by its restrictions to the `HW_k` (`eq_zero_of_res_eq_zero`), and every
family of endomorphisms `B_k` of `HW_k` is the restriction of such a `Y` (`exists_comm_of_res`):
the commutant of `{L, R}` is `⊕_k End(HW_k)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Module LinearMap

namespace FormalResearch.FrameFree.OddWords

/-- Index type of the string basis: `(k, a, i)` with `k ≤ n/2`, `a ≤ n-2k`, `i < dim HW_k`. -/
abbrev StrIdx (n : ℕ) : Type := Σ k : Fin (n / 2 + 1), Fin (n - 2 * k + 1) × Fin (hwDim n k)

theorem card_strIdx (n : ℕ) : Fintype.card (StrIdx n) = 2 ^ n := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun k => (n - 2 * k + 1) * hwDim n k) (n / 2 + 1)]
  exact sum_string_dim n

namespace Sl2Data

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (D : Sl2Data n V)

/-- A basis of `HW_k`, indexed by `Fin (hwDim n k)`. -/
noncomputable def hb (k : Fin (n / 2 + 1)) : Basis (Fin (hwDim n k)) ℝ (D.HW k) :=
  finBasisOfFinrankEq ℝ _ (D.finrank_HW (by have := k.2; omega))

/-- The string vectors. -/
noncomputable def vec : StrIdx n → V := fun p => (D.L ^ (p.2.1 : ℕ)) ((D.hb p.1 p.2.2 : D.HW p.1) : V)

theorem Str_le_span : D.Str ≤ Submodule.span ℝ (Set.range D.vec) := by
  rw [Str, Submodule.span_le]
  rintro v ⟨k, a, h, hh, hk, ha, rfl⟩
  let k' : Fin (n / 2 + 1) := ⟨k, by omega⟩
  have hrep := (D.hb k').sum_repr ⟨h, hh⟩
  have : (D.L ^ a) h = ∑ i, (D.hb k').repr ⟨h, hh⟩ i • D.vec ⟨k', ⟨a, by show a < n - 2 * k + 1; omega⟩, i⟩ := by
    have := congrArg (fun x : D.HW k' => (D.L ^ a) (x : V)) hrep
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul] at this
    rw [← this]; rfl
  rw [SetLike.mem_coe, this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem span_vec : Submodule.span ℝ (Set.range D.vec) = ⊤ := by
  rw [eq_top_iff, ← D.Str_eq_top]; exact D.Str_le_span

theorem linearIndependent_vec : LinearIndependent ℝ D.vec :=
  linearIndependent_of_top_le_span_of_card_eq_finrank (le_of_eq D.span_vec.symm)
    (by rw [card_strIdx, D.finrank_V])

/-- The string basis of `V`. -/
noncomputable def stringBasis : Basis (StrIdx n) ℝ V :=
  Basis.mk D.linearIndependent_vec (le_of_eq D.span_vec.symm)

@[simp] theorem stringBasis_apply (p : StrIdx n) : D.stringBasis p = D.vec p := by
  simp [stringBasis]

/-- `Y` commutes with `L` and `R`. -/
def IsComm (Y : V →ₗ[ℝ] V) : Prop := Y * D.L = D.L * Y ∧ Y * D.R = D.R * Y

variable {D}

theorem IsComm.apply_L {Y : V →ₗ[ℝ] V} (hY : D.IsComm Y) (v : V) : Y (D.L v) = D.L (Y v) :=
  congrArg (fun T : V →ₗ[ℝ] V => T v) hY.1

theorem IsComm.apply_R {Y : V →ₗ[ℝ] V} (hY : D.IsComm Y) (v : V) : Y (D.R v) = D.R (Y v) :=
  congrArg (fun T : V →ₗ[ℝ] V => T v) hY.2

theorem IsComm.apply_H {Y : V →ₗ[ℝ] V} (hY : D.IsComm Y) (v : V) : Y (D.H v) = D.H (Y v) := by
  simp only [H, LinearMap.sub_apply, Module.End.mul_apply, map_sub, hY.apply_L, hY.apply_R]

theorem IsComm.mem_W {Y : V →ₗ[ℝ] V} (hY : D.IsComm Y) {m : ℕ} {v : V} (hv : v ∈ D.W m) :
    Y v ∈ D.W m := by
  rw [D.mem_W] at hv ⊢
  rw [← hY.apply_H, hv, map_smul]

theorem IsComm.mem_HW {Y : V →ₗ[ℝ] V} (hY : D.IsComm Y) {k : ℕ} {v : V} (hv : v ∈ D.HW k) :
    Y v ∈ D.HW k :=
  ⟨hY.mem_W hv.1, LinearMap.mem_ker.2 (by rw [← hY.apply_R, LinearMap.mem_ker.1 hv.2, map_zero])⟩

theorem IsComm.apply_pow {Y : V →ₗ[ℝ] V} (hY : D.IsComm Y) (a : ℕ) (v : V) :
    Y ((D.L ^ a) v) = (D.L ^ a) (Y v) := by
  induction a generalizing v with
  | zero => simp
  | succ a ih => rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hY.apply_L]

theorem IsComm.adjoint {Y : V →ₗ[ℝ] V} (hY : D.IsComm Y) : D.IsComm (LinearMap.adjoint Y) := by
  have h1 := congrArg LinearMap.adjoint hY.1
  have h2 := congrArg LinearMap.adjoint hY.2
  rw [adjoint_mul', adjoint_mul'] at h1 h2
  refine ⟨?_, ?_⟩
  · have e : LinearMap.adjoint D.R = D.L := LinearMap.adjoint_adjoint _
    rw [e] at h2
    exact h2.symm
  · exact h1.symm

theorem eq_zero_of_res_eq_zero {Y : V →ₗ[ℝ] V} (hY : D.IsComm Y)
    (h : ∀ k : ℕ, 2 * k ≤ n → ∀ v ∈ D.HW k, Y v = 0) : Y = 0 := by
  have hs : D.Str ≤ LinearMap.ker Y := by
    rw [Sl2Data.Str, Submodule.span_le]
    rintro v ⟨k, a, x, hx, hk, ha, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hY.apply_pow, h k (by omega) x hx, map_zero]
  rw [D.Str_eq_top, top_le_iff, LinearMap.ker_eq_top] at hs
  exact hs

/-- The operator with prescribed restrictions `B_k` to the highest-weight spaces. -/
noncomputable def Ysys (D : Sl2Data n V) (B : ∀ k : Fin (n / 2 + 1), D.HW k →ₗ[ℝ] D.HW k) :
    V →ₗ[ℝ] V :=
  D.stringBasis.constr ℝ fun p => (D.L ^ (p.2.1 : ℕ)) ((B p.1 (D.hb p.1 p.2.2) : D.HW p.1) : V)

variable (D) (B : ∀ k : Fin (n / 2 + 1), D.HW k →ₗ[ℝ] D.HW k)

theorem Ysys_vec (p : StrIdx n) :
    D.Ysys B (D.vec p) = (D.L ^ (p.2.1 : ℕ)) ((B p.1 (D.hb p.1 p.2.2) : D.HW p.1) : V) := by
  rw [← D.stringBasis_apply, Ysys, Basis.constr_basis]

theorem Ysys_pow (k : Fin (n / 2 + 1)) (h : D.HW k) (a : ℕ) :
    D.Ysys B ((D.L ^ a) (h : V)) = (D.L ^ a) ((B k h : D.HW k) : V) := by
  have hk : 2 * (k : ℕ) ≤ n := by have := k.2; omega
  by_cases ha : a ≤ n - 2 * k
  · have hrep := (D.hb k).sum_repr h
    have e1 : (D.L ^ a) (h : V) = ∑ i, (D.hb k).repr h i • D.vec ⟨k, ⟨a, by omega⟩, i⟩ := by
      have := congrArg (fun x : D.HW k => (D.L ^ a) (x : V)) hrep
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul] at this
      rw [← this]; rfl
    have e2 : B k h = ∑ i, (D.hb k).repr h i • B k (D.hb k i) := by
      conv_lhs => rw [← hrep]
      simp only [map_sum, map_smul]
    rw [e1, map_sum, e2]
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Ysys_vec]
  · have h0 : (D.L ^ a) (h : V) = 0 := by
      have : a = (a - (n - 2 * k + 1)) + (n - 2 * k + 1) := by omega
      rw [this, pow_add, Module.End.mul_apply, D.L_pow_top hk h.2, map_zero]
    have h0' : (D.L ^ a) ((B k h : D.HW k) : V) = 0 := by
      have : a = (a - (n - 2 * k + 1)) + (n - 2 * k + 1) := by omega
      rw [this, pow_add, Module.End.mul_apply, D.L_pow_top hk (B k h).2, map_zero]
    rw [h0, h0', map_zero]

theorem Ysys_hw (k : Fin (n / 2 + 1)) (h : D.HW k) : D.Ysys B (h : V) = (B k h : V) := by
  simpa using D.Ysys_pow B k h 0

theorem Ysys_isComm : D.IsComm (D.Ysys B) := by
  refine ⟨?_, ?_⟩
  · refine D.stringBasis.ext fun p => ?_
    rw [D.stringBasis_apply]
    obtain ⟨k, a, i⟩ := p
    have e : D.L (D.vec ⟨k, a, i⟩) = (D.L ^ ((a : ℕ) + 1)) ((D.hb k i : D.HW k) : V) := by
      simp only [vec]; rw [pow_succ', Module.End.mul_apply]
    simp only [Module.End.mul_apply]
    rw [e, D.Ysys_pow B k (D.hb k i) (a + 1), Ysys_vec]
    simp only [pow_succ', Module.End.mul_apply]
  · refine D.stringBasis.ext fun p => ?_
    rw [D.stringBasis_apply]
    obtain ⟨k, a, i⟩ := p
    simp only [Module.End.mul_apply]
    rcases Nat.eq_zero_or_pos (a : ℕ) with h0 | hpos
    · simp only [vec, h0, pow_zero, Module.End.one_apply]
      rw [LinearMap.mem_ker.1 (D.hb k i).2.2, map_zero]
      rw [D.Ysys_hw B k (D.hb k i)]
      exact (LinearMap.mem_ker.1 (B k (D.hb k i)).2.2).symm
    · obtain ⟨a', ha'⟩ : ∃ a', (a : ℕ) = a' + 1 := ⟨(a : ℕ) - 1, by omega⟩
      have hR := D.R_L_pow_succ (D.hb k i).2 a'
      have hR' := D.R_L_pow_succ (B k (D.hb k i)).2 a'
      simp only [vec, ha']
      rw [hR, map_smul, D.Ysys_pow B k (D.hb k i) a', D.Ysys_pow B k (D.hb k i) (a' + 1), hR']

end Sl2Data

end FormalResearch.FrameFree.OddWords
