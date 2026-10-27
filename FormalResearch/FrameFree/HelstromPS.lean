import Mathlib

/-!
# Powers-Stormer test (generic finite-dimensional statement)

Namespace `FormalResearch.FrameFree.Helstrom`.  For positive semidefinite `X, Y` the explicit projector
`P = 1_{>0}(X - Y)` (a continuous functional calculus of the Hermitian matrix `X - Y`) satisfies
`tr(X² (1-P)) + tr(Y² P) ≤ tr(XY)` (`power_stormer`), is a positive semidefinite effect, and commutes
with every `B` commuting with both `X` and `Y`.  With `X² = σ`, `Y² = ρ` this is the Powers-Stormer
inequality `tr(ρ P) + tr(σ (1-P)) ≤ tr(√ρ √σ)` in the form used for the Chernoff-side lower bound.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped MatrixOrder ComplexOrder
open Matrix

namespace FormalResearch.FrameFree.Helstrom

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem cont_spec {D : Matrix ι ι ℂ} (hD : D.IsHermitian) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ D) := by
  rw [hD.spectrum_real_eq_range_eigenvalues]
  exact Set.Finite.continuousOn (Set.finite_range hD.eigenvalues) f

noncomputable def posProj (D : Matrix ι ι ℂ) : Matrix ι ι ℂ := cfc (fun x : ℝ => if 0 < x then (1:ℝ) else 0) D
noncomputable def posPart' (D : Matrix ι ι ℂ) : Matrix ι ι ℂ := cfc (fun x : ℝ => max x 0) D
noncomputable def negPart' (D : Matrix ι ι ℂ) : Matrix ι ι ℂ := cfc (fun x : ℝ => max (-x) 0) D

theorem posProj_sq {D : Matrix ι ι ℂ} (hD : D.IsHermitian) : posProj D * posProj D = posProj D := by
  unfold posProj
  rw [← cfc_mul _ _ D (cont_spec hD _) (cont_spec hD _)]
  congr 1
  funext x
  by_cases h : 0 < x <;> simp [h]

theorem posProj_nonneg {D : Matrix ι ι ℂ} (hD : D.IsHermitian) : 0 ≤ posProj D := by
  unfold posProj
  exact cfc_nonneg (fun x _ => by by_cases h : 0 < x <;> simp [h])

theorem posPart'_nonneg {D : Matrix ι ι ℂ} (hD : D.IsHermitian) : 0 ≤ posPart' D := by
  unfold posPart'
  exact cfc_nonneg (fun x _ => le_max_right _ _)

theorem posProj_mul_D {D : Matrix ι ι ℂ} (hD : D.IsHermitian) : posProj D * D = posPart' D := by
  unfold posProj posPart'
  have h := cfc_mul (fun x : ℝ => if 0 < x then (1:ℝ) else 0) (fun x : ℝ => x) D
    (cont_spec hD _) (cont_spec hD _)
  rw [cfc_id' ℝ D hD.isSelfAdjoint] at h
  rw [← h]
  congr 1
  funext x
  by_cases h : 0 < x <;> simp [h, le_of_lt, not_lt.1]

theorem trace_mul_nonneg_re {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  have hBn : 0 ≤ B := hB.nonneg
  set C := CFC.sqrt B with hC
  have hCs : Cᴴ = C := (CFC.sqrt_nonneg B).posSemidef.1
  have hCC : C * C = B := CFC.sqrt_mul_sqrt_self B hBn
  have h1 : (A * B).trace = (Cᴴ * A * C).trace := by
    rw [hCs, ← hCC, ← Matrix.mul_assoc, Matrix.trace_mul_comm (A * C) C, Matrix.mul_assoc]
  rw [h1]
  exact (Complex.nonneg_iff.1 (Matrix.PosSemidef.trace_nonneg (hA.conjTranspose_mul_mul_same C))).1

theorem negPart'_nonneg {D : Matrix ι ι ℂ} (hD : D.IsHermitian) : 0 ≤ negPart' D := by
  unfold negPart'
  exact cfc_nonneg (fun x _ => le_max_right _ _)

theorem pp_sub_np {D : Matrix ι ι ℂ} (hD : D.IsHermitian) : posPart' D - negPart' D = D := by
  unfold posPart' negPart'
  rw [← cfc_sub _ _ D (cont_spec hD _) (cont_spec hD _)]
  conv_rhs => rw [← cfc_id' ℝ D hD.isSelfAdjoint]
  congr 1
  funext x
  by_cases h : 0 ≤ x
  · simp [h]
  · have h' : x ≤ 0 := (not_le.1 h).le
    simp [h, h']

theorem pp_mul_np {D : Matrix ι ι ℂ} (hD : D.IsHermitian) : posPart' D * negPart' D = 0 := by
  unfold posPart' negPart'
  rw [← cfc_mul _ _ D (cont_spec hD _) (cont_spec hD _)]
  rw [← cfc_zero ℝ D]
  congr 1
  funext x
  by_cases h : 0 ≤ x
  · simp [h]
  · have h' : x ≤ 0 := (not_le.1 h).le
    simp [h']

theorem posProj_herm {D : Matrix ι ι ℂ} (hD : D.IsHermitian) : (posProj D).IsHermitian := by
  have := cfc_predicate (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => if 0 < x then (1:ℝ) else 0) D
  exact this

theorem projector_posSemidef {Q : Matrix ι ι ℂ} (h1 : Q.IsHermitian) (h2 : Q * Q = Q) : Q.PosSemidef := by
  have := Matrix.posSemidef_conjTranspose_mul_self Q
  rw [h1.eq, h2] at this
  exact this

theorem posProj_commute {D B : Matrix ι ι ℂ} (hD : D.IsHermitian) (hB : Commute D B) :
    Commute (posProj D) B := Commute.cfc_real hB _

/-- Purely algebraic part of the Powers-Stormer argument. -/
theorem ps_algebra {X Y D P Dp Dm : Matrix ι ι ℂ} (hD : D = X - Y)
    (hDD : Dp - Dm = D) (hPD : P * D = Dp) (hDP : D * P = P * D) :
    (X * X * (1 - P)).trace + (Y * Y * P).trace + (Y * Dp).trace + (X * Dm).trace = (X * Y).trace := by
  have hDm : Dm = P * D - D := by rw [hPD, ← hDD]; abel
  rw [← hPD, hDm]
  have hc : (P * X * D).trace = (P * D * X).trace := by
    calc (P * X * D).trace = (X * D * P).trace := by rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = (X * (D * P)).trace := by rw [Matrix.mul_assoc]
      _ = (X * (P * D)).trace := by rw [hDP]
      _ = (P * D * X).trace := by rw [Matrix.trace_mul_comm]
  subst hD
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.mul_assoc] at hc ⊢
  have e1 : (X * (X * P)).trace = (X * (P * X)).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have e2 : (Y * (Y * P)).trace = (Y * (P * Y)).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have e3 : (Y * (P * X)).trace = (P * (X * Y)).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have e4 : (X * (P * Y)).trace = (P * (Y * X)).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  linear_combination (-1 : ℂ) * e1 + e2 + e3 - e4 - hc

theorem power_stormer {X Y : Matrix ι ι ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    ∃ P : Matrix ι ι ℂ, P.PosSemidef ∧ (1 - P).PosSemidef ∧
      (∀ B, Commute X B → Commute Y B → Commute P B) ∧
      ((X * X * (1 - P)).trace.re + (Y * Y * P).trace.re ≤ (X * Y).trace.re) := by
  obtain ⟨D, hDdef⟩ : ∃ D, D = X - Y := ⟨_, rfl⟩
  have hD : D.IsHermitian := hDdef ▸ hX.1.sub hY.1
  have hPh := posProj_herm hD
  have hP2 := posProj_sq hD
  refine ⟨posProj D, projector_posSemidef hPh hP2, ?_, ?_, ?_⟩
  · refine projector_posSemidef ?_ ?_
    · exact (Matrix.isHermitian_one).sub hPh
    · rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP2]
      simp
  · intro B hXB hYB
    exact posProj_commute hD (hDdef ▸ hXB.sub_left hYB)
  · have hDD : posPart' D - negPart' D = D := pp_sub_np hD
    have hPD : posProj D * D = posPart' D := posProj_mul_D hD
    have hDP : D * posProj D = posProj D * D := ((posProj_commute hD (Commute.refl D)).eq).symm
    have hpn : posPart' D * negPart' D = 0 := pp_mul_np hD
    have hnp : negPart' D * posPart' D = 0 := by
      have := (cfc_commute_cfc (R := ℝ) (fun x : ℝ => max x 0) (fun x : ℝ => max (-x) 0) D).eq
      rw [show negPart' D * posPart' D = posPart' D * negPart' D from this.symm, hpn]
    have h1 := trace_mul_nonneg_re hY (posPart'_nonneg hD).posSemidef
    have h2 := trace_mul_nonneg_re hX (negPart'_nonneg hD).posSemidef
    have key := ps_algebra hDdef hDD hPD hDP
    have := congrArg Complex.re key
    simp only [Complex.add_re] at this
    linarith

end FormalResearch.FrameFree.Helstrom
