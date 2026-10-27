import Mathlib
import FormalResearch.QIB.BlockDecomp

/-!
# Antiunitary block formula and the blind-sector converse (`prop:antiunitary`, `prop:blind`)

Namespace `FormalResearch.QIB`.  Claim class: **proved under explicit hypothesis**
(`IsotypicInvariants`, see `BlockDecomp.lean`), plus the coordinate hypothesis that the second
vector's multiplicity blocks are the entrywise conjugates of the first's (`hconj`), which holds when
the second vector is the entrywise conjugate of the first in real Schur-Weyl coordinates (`tau_star`).

Source: `QI-B/paper/invariant_discrimination_exponents.tex`, Propositions `prop:antiunitary` and
`prop:blind`.

* `imNorm τ = ½ ‖τ - τ̄‖₁`.  Since `τ - τ̄ = 2i Im τ` and multiplication by `i` does not change the
  trace norm, this is `‖Im τ‖₁` of the paper.  (`‖·‖₁` is `tnorm`, defined for Hermitian matrices;
  `τ - τ̄` is Hermitian for Hermitian `τ`.)
* `antiunitary_block`: `1 - 2 P_e = Σ_λ ‖Im τ_λ‖₁`  (unit vectors, `τ^b = τ̄^a`).
* `imNorm_eq_zero_iff`: a sector is blind (`τ^a_λ = τ^b_λ`) iff `τ_λ` is real;
  `blind_of_subsingleton`: every multiplicity-one sector is blind.
* `invErr_ge_blind`, `invErr_ge_multiplicity_one`: `P_e ≥ ½ Σ_{λ blind} p_λ`, in particular
  `P_e ≥ ½ Σ_{dim M_λ = 1} p_λ` (this is `prop:blind`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate
open scoped MatrixOrder ComplexOrder

namespace FormalResearch.QIB

open FormalResearch.FrameFree.Helstrom (IsEffect)

section Antiunitary

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {A B : Λ → Type*}
  [∀ l, Fintype (A l)] [∀ l, DecidableEq (A l)] [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]

/-- `‖Im τ‖₁ = ½ ‖τ - τ̄‖₁`. -/
noncomputable def imNorm {m : Type*} [Fintype m] [DecidableEq m] (τ : Matrix m m ℂ) : ℝ :=
  (1 / 2) * tnorm (τ - τ.map conj)

/-- In coordinates where complex conjugation acts entrywise, the conjugate vector has the conjugate
multiplicity blocks. -/
theorem tau_star (a : Idx A B → ℂ) (l : Λ) : tau (star a) l = (tau a l).map conj := by
  ext b b'
  simp [tau_apply, Matrix.map_apply, map_sum]

theorem tau_trace_re_conj {m : Type*} [Fintype m] [DecidableEq m] (τ : Matrix m m ℂ) :
    (τ.map conj).trace.re = τ.trace.re := by
  simp [Matrix.trace, Matrix.diag, Complex.re_sum]

theorem hermitian_sub_conj {m : Type*} [Fintype m] [DecidableEq m] {τ : Matrix m m ℂ}
    (hτ : τ.IsHermitian) : (τ - τ.map conj).IsHermitian :=
  hτ.sub (hτ.map conj fun x => by simp)

theorem re_trace_mul_tau_nonneg {l : Λ} {X : Matrix (B l) (B l) ℂ} (hX : X.PosSemidef) (v : Idx A B → ℂ) :
    0 ≤ (X * tau v l).trace.re := by
  unfold tau
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_nonneg fun α _ => ?_
  rw [FormalResearch.FrameFree.Helstrom.tr_mul_vecMulVec]
  exact (Complex.nonneg_iff.1 ((Matrix.posSemidef_iff_dotProduct_mulVec.1 hX).2 _)).1

theorem trMin_tau_nonneg (a b : Idx A B → ℂ) (l : Λ) : 0 ≤ trMin (tau a l) (tau b l) := by
  obtain ⟨X, hX, hXe⟩ := sector_attain (tau_isHermitian a l) (tau_isHermitian b l)
  rw [← hXe]
  exact add_nonneg (re_trace_mul_tau_nonneg hX.1 a) (re_trace_mul_tau_nonneg hX.2 b)

/-- **`prop:antiunitary`, block formula.**  For unit vectors `a`, `b` whose multiplicity blocks are
conjugate, `1 - 2 P_e = Σ_λ ‖Im τ_λ‖₁`. -/
theorem antiunitary_block [∀ l, Nonempty (A l)] {G : Set (Matrix (Idx A B) (Idx A B) ℂ)}
    (hG : IsotypicInvariants A G) {a b : Idx A B → ℂ} (ha : star a ⬝ᵥ a = 1) (hb : star b ⬝ᵥ b = 1)
    (hconj : ∀ l, tau b l = (tau a l).map conj) :
    1 - 2 * invErr G a b = ∑ l, imNorm (tau a l) := by
  rw [invErr_eq_one_sub hG ha hb]
  simp only [hconj, imNorm]
  rw [← Finset.mul_sum]
  ring

/-- `prop:antiunitary` for `b = ā` (entrywise conjugate in real Schur-Weyl coordinates). -/
theorem antiunitary_block_star [∀ l, Nonempty (A l)] {G : Set (Matrix (Idx A B) (Idx A B) ℂ)}
    (hG : IsotypicInvariants A G) {a : Idx A B → ℂ} (ha : star a ⬝ᵥ a = 1) :
    1 - 2 * invErr G a (star a) = ∑ l, imNorm (tau a l) := by
  refine antiunitary_block hG ha ?_ (tau_star a)
  rw [star_star, dotProduct_comm]
  exact ha

/-- A sector is blind (`τ^a_λ = τ^b_λ`) exactly when `τ_λ` is real, i.e. `‖Im τ_λ‖₁ = 0`. -/
theorem imNorm_eq_zero_iff {m : Type*} [Fintype m] [DecidableEq m] {τ : Matrix m m ℂ}
    (hτ : τ.IsHermitian) : imNorm τ = 0 ↔ τ.map conj = τ := by
  unfold imNorm
  rw [mul_eq_zero, tnorm_eq_zero_iff (hermitian_sub_conj hτ), sub_eq_zero]
  simp only [one_div, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem sector_blind_iff {a b : Idx A B → ℂ} (hconj : ∀ l, tau b l = (tau a l).map conj) (l : Λ) :
    tau a l = tau b l ↔ imNorm (tau a l) = 0 := by
  rw [imNorm_eq_zero_iff (tau_isHermitian a l), hconj l]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- Every multiplicity-one sector is blind. -/
theorem blind_of_subsingleton (a : Idx A B → ℂ) (l : Λ) [Subsingleton (B l)] :
    (tau a l).map conj = tau a l := by
  ext i j
  obtain rfl : i = j := Subsingleton.elim i j
  have := (tau_isHermitian a l).apply i i
  simpa [Complex.star_def] using this

/-- **`prop:blind`.**  If `τ^b_λ = τ̄^a_λ`, then `P_e ≥ ½ Σ_{λ ∈ T} p_λ` over any set `T` of blind
(real-block) sectors; `p_λ = Re Tr τ_λ`. -/
theorem invErr_ge_blind [∀ l, Nonempty (A l)] {G : Set (Matrix (Idx A B) (Idx A B) ℂ)}
    (hG : IsotypicInvariants A G) {a b : Idx A B → ℂ}
    (hconj : ∀ l, tau b l = (tau a l).map conj) (T : Finset Λ)
    (hT : ∀ l ∈ T, (tau a l).map conj = tau a l) :
    (1 / 2) * ∑ l ∈ T, (tau a l).trace.re ≤ invErr G a b := by
  rw [invErr_eq hG]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    fun l _ _ => trMin_tau_nonneg a b l)
  refine Finset.sum_congr rfl fun l hl => ?_
  have hb : tau b l = tau a l := by rw [hconj l, hT l hl]
  rw [hb]
  unfold trMin
  rw [sub_self, (tnorm_eq_zero_iff Matrix.isHermitian_zero).2 rfl]
  ring

/-- **`prop:blind`** (multiplicity-one form): `P_e ≥ ½ Σ_{dim M_λ = 1} p_λ`. -/
theorem invErr_ge_multiplicity_one [∀ l, Nonempty (A l)] {G : Set (Matrix (Idx A B) (Idx A B) ℂ)}
    (hG : IsotypicInvariants A G) {a b : Idx A B → ℂ}
    (hconj : ∀ l, tau b l = (tau a l).map conj) :
    (1 / 2) * ∑ l ∈ Finset.univ.filter (fun l => Fintype.card (B l) = 1), (tau a l).trace.re
      ≤ invErr G a b := by
  refine invErr_ge_blind hG hconj _ fun l hl => ?_
  have : Subsingleton (B l) := Fintype.card_le_one_iff_subsingleton.1
    (le_of_eq (Finset.mem_filter.1 hl).2)
  exact blind_of_subsingleton a l

end Antiunitary

end FormalResearch.QIB
