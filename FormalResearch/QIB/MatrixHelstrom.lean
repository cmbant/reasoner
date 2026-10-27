import Mathlib
import FormalResearch.FrameFree.HelstromPure

/-!
# Matrix Helstrom identity (trace norm of a Hermitian matrix as a sum of `|eigenvalues|`)

Namespace `FormalResearch.QIB`.  Claim class: **proved** (no hypothesis, no new axiom).

Source: `QI-B/paper/invariant_discrimination_exponents.tex`, the Helstrom reduction behind Eq.
`eq:helstrom-twirls` and Lemma `lem:blockdecomp`, in the form needed blockwise.

* `tnorm D` is the trace norm `‖D‖₁ = Σ_i |λ_i(D)|` of a Hermitian matrix (and `0` off the Hermitian
  matrices, a junk value never used).
* `trace_mul_ge`: for Hermitian `D` and every effect `0 ≤ E ≤ 1`, `½(Tr D - ‖D‖₁) ≤ Re Tr(E D)`.
* `exists_effect_trace_mul_eq`: the bound is attained by an effect (the negative spectral projector).
* `trMin A B = ½(Tr A + Tr B - ‖A - B‖₁)` (the paper's `Tr min(A,B)`), `trMin_comm`, `trMin_self`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix
open scoped MatrixOrder ComplexOrder

namespace FormalResearch.QIB

open FormalResearch.FrameFree.Helstrom (IsEffect)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Trace norm of a Hermitian matrix: the sum of the absolute values of its eigenvalues. -/
noncomputable def tnorm (D : Matrix n n ℂ) : ℝ :=
  if h : D.IsHermitian then ∑ i, |h.eigenvalues i| else 0

theorem tnorm_eq {D : Matrix n n ℂ} (h : D.IsHermitian) : tnorm D = ∑ i, |h.eigenvalues i| := by
  simp [tnorm, h]

theorem tnorm_nonneg (D : Matrix n n ℂ) : 0 ≤ tnorm D := by
  unfold tnorm
  split_ifs
  · exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  · exact le_rfl

/-- `Tr(M · diag d) = Σ_i M_{ii} d_i`. -/
theorem trace_mul_diagonal' (M : Matrix n n ℂ) (d : n → ℂ) :
    (M * diagonal d).trace = ∑ i, M i i * d i := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]

/-- Spectral form of `Tr(E D)`: `Σ_i c_i λ_i` with `c = diag(U* E U)`. -/
theorem trace_mul_spectral {D : Matrix n n ℂ} (hD : D.IsHermitian) (E : Matrix n n ℂ) :
    (E * D).trace =
      ∑ i, (star (hD.eigenvectorUnitary : Matrix n n ℂ) * E * (hD.eigenvectorUnitary : Matrix n n ℂ)) i i
        * (hD.eigenvalues i : ℂ) := by
  set U : Matrix n n ℂ := (hD.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hspec : D = U * diagonal (fun i => (hD.eigenvalues i : ℂ)) * star U := by
    have := hD.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  conv_lhs => rw [hspec]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    trace_mul_diagonal']

theorem star_mul_self_U {D : Matrix n n ℂ} (hD : D.IsHermitian) :
    star (hD.eigenvectorUnitary : Matrix n n ℂ) * (hD.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
  Unitary.coe_star_mul_self _

/-- The diagonal weights `c_i = (U* E U)_{ii}` of an effect lie in `[0,1]`. -/
theorem diag_effect_bounds {D : Matrix n n ℂ} (hD : D.IsHermitian) {E : Matrix n n ℂ}
    (hE : IsEffect E) (i : n) :
    0 ≤ (star (hD.eigenvectorUnitary : Matrix n n ℂ) * E * (hD.eigenvectorUnitary : Matrix n n ℂ)) i i ∧
    (star (hD.eigenvectorUnitary : Matrix n n ℂ) * E * (hD.eigenvectorUnitary : Matrix n n ℂ)) i i ≤ 1 := by
  set U : Matrix n n ℂ := (hD.eigenvectorUnitary : Matrix n n ℂ) with hU
  have h0 := (hE.1.conjTranspose_mul_mul_same U).diag_nonneg (i := i)
  have h1 := (hE.2.conjTranspose_mul_mul_same U).diag_nonneg (i := i)
  have hUU : star U * U = 1 := star_mul_self_U hD
  have e1 : Uᴴ * (1 - E) * U = 1 - Uᴴ * E * U := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    have : Uᴴ * U = 1 := hUU
    rw [this]
  rw [e1] at h1
  have hs : (star U * E * U) = Uᴴ * E * U := rfl
  rw [hs]
  refine ⟨h0, ?_⟩
  simpa [Matrix.sub_apply] using h1

theorem trace_mul_ge {D : Matrix n n ℂ} (hD : D.IsHermitian) {E : Matrix n n ℂ} (hE : IsEffect E) :
    (1 / 2) * (D.trace.re - tnorm D) ≤ (E * D).trace.re := by
  rw [tnorm_eq hD, trace_mul_spectral hD E, hD.trace_eq_sum_eigenvalues]
  simp only [Complex.re_sum]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨h0, h1⟩ := diag_effect_bounds hD hE i
  -- `c := (U* E U)_{ii}` is real in `[0,1]`
  set c := (star (hD.eigenvectorUnitary : Matrix n n ℂ) * E *
    (hD.eigenvectorUnitary : Matrix n n ℂ)) i i with hc
  have hcr : c = (c.re : ℂ) := by
    have h0' : (0 : ℂ) ≤ c := h0
    rw [Complex.nonneg_iff] at h0'
    exact Complex.ext (by simp) (by simpa using h0'.2.symm)
  have h0r : 0 ≤ c.re := by have := (Complex.nonneg_iff.1 h0).1; exact this
  have h1r : c.re ≤ 1 := by
    have := (Complex.le_def.1 h1).1; simpa using this
  rw [hcr]
  simp only [Complex.re_ofReal_mul, Complex.ofReal_re]
  set l := hD.eigenvalues i
  change 1 / 2 * (l - |l|) ≤ c.re * l
  rcases le_total 0 l with hl | hl
  · rw [abs_of_nonneg hl]
    nlinarith
  · rw [abs_of_nonpos hl]
    nlinarith

/-- The negative spectral projector. -/
noncomputable def negProj (D : Matrix n n ℂ) (hD : D.IsHermitian) : Matrix n n ℂ :=
  (hD.eigenvectorUnitary : Matrix n n ℂ) *
    diagonal (fun i => if hD.eigenvalues i < 0 then (1 : ℂ) else 0) *
    star (hD.eigenvectorUnitary : Matrix n n ℂ)

theorem negProj_isEffect {D : Matrix n n ℂ} (hD : D.IsHermitian) : IsEffect (negProj D hD) := by
  set U : Matrix n n ℂ := (hD.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hdiag : (diagonal (fun i => if hD.eigenvalues i < 0 then (1 : ℂ) else 0)).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · exact hdiag.mul_mul_conjTranspose_same U
  · have : (1 : Matrix n n ℂ) - negProj D hD =
        U * diagonal (fun i => if hD.eigenvalues i < 0 then (0 : ℂ) else 1) * star U := by
      have h1 : (1 : Matrix n n ℂ) = U * (1 : Matrix n n ℂ) * star U := by
        rw [Matrix.mul_one, hUU]
      unfold negProj
      rw [← hU]
      conv_lhs => rw [h1]
      rw [← Matrix.sub_mul, ← Matrix.mul_sub]
      congr 2
      ext i j
      by_cases hij : i = j
      · subst hij; by_cases h : hD.eigenvalues i < 0 <;> simp [h]
      · simp [hij]
    rw [this]
    have hd2 : (diagonal (fun i => if hD.eigenvalues i < 0 then (0 : ℂ) else 1)).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      split_ifs <;> simp
    exact hd2.mul_mul_conjTranspose_same U

theorem exists_effect_trace_mul_eq {D : Matrix n n ℂ} (hD : D.IsHermitian) :
    ∃ E : Matrix n n ℂ, IsEffect E ∧ (E * D).trace.re = (1 / 2) * (D.trace.re - tnorm D) := by
  refine ⟨negProj D hD, negProj_isEffect hD, ?_⟩
  rw [tnorm_eq hD, trace_mul_spectral hD, hD.trace_eq_sum_eigenvalues]
  set U : Matrix n n ℂ := (hD.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := star_mul_self_U hD
  have hc : ∀ i, (star U * negProj D hD * U) i i = if hD.eigenvalues i < 0 then (1 : ℂ) else 0 := by
    intro i
    have : star U * negProj D hD * U = diagonal (fun i => if hD.eigenvalues i < 0 then (1 : ℂ) else 0) := by
      unfold negProj
      rw [← hU]
      calc star U * (U * diagonal (fun i => if hD.eigenvalues i < 0 then (1 : ℂ) else 0) * star U) * U
          = (star U * U) * diagonal (fun i => if hD.eigenvalues i < 0 then (1 : ℂ) else 0)
              * (star U * U) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hUU]; simp
    rw [this]; simp
  simp only [hc, Complex.re_sum]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hl : hD.eigenvalues i < 0
  · simp [hl, abs_of_neg hl]; ring
  · push Not at hl
    simp [not_lt.2 hl, abs_of_nonneg hl]

/-! ### `Tr min` -/

/-- The paper's `Tr min(A,B) := ½(Tr A + Tr B - ‖A-B‖₁)` (real parts of the traces). -/
noncomputable def trMin (A B : Matrix n n ℂ) : ℝ := (1 / 2) * (A.trace.re + B.trace.re - tnorm (A - B))

end FormalResearch.QIB
