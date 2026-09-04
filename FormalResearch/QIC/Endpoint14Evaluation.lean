import Mathlib

namespace FormalResearch.QIC

abbrev Fin14 := Fin 14
abbrev Fin7 := Fin 7
abbrev P5 := Fin 5 → Int

def p4 (a0 a1 a2 a3 a4 : Int) : P5 := ![a0,a1,a2,a3,a4]

def endpoint14 : Matrix Fin14 Fin14 P5 :=
  !![      p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 8 (-4) 0, p4 0 0 (-4) 4 0, p4 0 0 (-4) 8 0, p4 0 0 2 (-8) 0, p4 0 0 (-18) 0 0, p4 0 0 18 0 0, p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 (-8) 8 0, p4 0 0 8 (-8) 0, p4 0 0 22 (-22) 0, p4 0 0 (-22) 22 0;
      p4 0 0 4 (-4) 0, p4 0 0 4 (-8) 4, p4 0 0 4 (-4) 0, p4 0 0 0 0 0, p4 0 0 (-16) 8 0, p4 0 0 (-16) 8 0, p4 0 0 (-24) 16 0, p4 0 0 (-8) 32 (-16), p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 (-8) 4 0, p4 0 0 8 (-12) 4, p4 0 0 6 (-6) 0, p4 0 0 (-38) 54 (-16);
      p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 0 (-4) 0, p4 0 0 0 4 0, p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 8 0 0, p4 0 0 (-8) 0 0, p4 0 0 4 (-4) 0, p4 0 0 0 0 0, p4 0 0 (-4) 4 0, p4 0 0 4 (-4) 0, p4 0 0 (-10) 10 0, p4 0 0 10 (-10) 0;
      p4 0 0 (-4) 4 0, p4 0 0 (-4) 8 (-4), p4 0 0 16 (-8) 0, p4 0 0 8 (-8) 4, p4 0 0 (-6) 2 0, p4 0 0 (-8) 8 (-2), p4 0 0 (-16) 2 0, p4 0 0 10 6 (-2), p4 0 0 0 0 0, p4 0 0 (-4) 8 (-4), p4 0 0 0 0 0, p4 0 0 8 (-12) 4, p4 0 0 (-10) 10 0, p4 0 0 10 (-10) 0;
      p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 0 (-8) 0, p4 0 0 0 8 0, p4 0 0 8 0 0, p4 0 0 (-8) 0 0, p4 0 0 4 (-4) 0, p4 0 0 0 0 0, p4 0 0 (-8) 8 0, p4 0 0 8 (-8) 0, p4 0 0 (-8) 8 0, p4 0 0 8 (-8) 0;
      p4 0 0 8 (-8) 0, p4 0 0 8 (-16) 8, p4 0 0 (-60) 28 0, p4 0 0 (-64) 88 (-28), p4 0 0 38 (-22) 0, p4 0 0 28 (-40) 14, p4 0 0 (-16) 2 0, p4 0 0 10 6 (-2), p4 0 0 0 0 0, p4 0 0 (-4) 8 (-4), p4 0 0 (-20) 20 0, p4 0 0 (-4) 16 (-12), p4 0 0 0 0 0, p4 0 0 16 (-24) 8;
      p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 16 (-8) 0, p4 0 0 (-8) 16 (-8), p4 0 0 (-8) 0 0, p4 0 0 8 0 0, p4 0 0 4 (-4) 0, p4 0 0 (-4) 8 (-4), p4 0 0 (-16) 8 0, p4 0 0 16 (-24) 8, p4 0 0 (-16) 8 0, p4 0 0 16 (-24) 8;
      p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 (-32) 16 0, p4 0 0 (-32) 80 (-32), p4 0 0 (-16) 0 0, p4 0 0 16 0 0, p4 0 0 8 (-8) 0, p4 0 0 0 0 0, p4 0 0 (-24) 16 0, p4 0 0 8 (-8) 0, p4 0 0 (-16) 16 0, p4 0 0 16 (-16) 0;
      p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 8 (-4) 0, p4 0 0 (-4) 8 (-4), p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 (-8) 0 0, p4 0 0 8 0 0, p4 0 0 4 (-4) 0, p4 0 0 (-4) 8 (-4), p4 0 0 (-8) 4 0, p4 0 0 8 (-12) 4, p4 0 0 (-20) 10 0, p4 0 0 20 (-30) 10;
      p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 (-16) 8 0, p4 0 0 (-16) 40 (-16), p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 (-16) 0 0, p4 0 0 16 0 0, p4 0 0 8 (-8) 0, p4 0 0 0 0 0, p4 0 0 (-8) 8 0, p4 0 0 8 (-8) 0, p4 0 0 (-24) 20 0, p4 0 0 16 (-16) 0;
      p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 0 (-4) 0, p4 0 0 0 8 (-4), p4 0 0 (-12) 8 0, p4 0 0 6 (-16) 8, p4 0 0 18 0 0, p4 0 0 (-18) 0 0, p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 (-16) 8 0, p4 0 0 16 (-24) 8, p4 0 0 44 (-22) 0, p4 0 0 (-44) 66 (-22);
      p4 0 0 (-32) 32 0, p4 0 0 (-32) 64 (-32), p4 0 0 112 (-56) 0, p4 0 0 112 (-152) 48, p4 0 0 (-16) 16 0, p4 0 0 0 0 0, p4 0 0 48 (-32) 0, p4 0 0 16 (-64) 32, p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 24 (-24) 0, p4 0 0 56 (-96) 40, p4 0 0 56 (-28) 0, p4 0 0 (-32) 48 (-16);
      p4 0 0 (-8) 8 0, p4 0 0 (-4) 12 (-8), p4 0 0 20 (-8) 0, p4 0 0 12 (-16) 8, p4 0 0 (-14) 2 0, p4 0 0 (-32) 24 (-2), p4 0 0 (-56) 18 0, p4 0 0 18 38 (-18), p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 (-18) 18 0, p4 0 0 (-18) 36 (-18);
      p4 0 0 16 (-16) 0, p4 0 0 20 (-36) 16, p4 0 0 (-112) 52 0, p4 0 0 (-124) 168 (-52), p4 0 0 46 (-22) 0, p4 0 0 36 (-56) 22, p4 0 0 (-56) 18 0, p4 0 0 18 38 (-18), p4 0 0 0 0 0, p4 0 0 0 0 0, p4 0 0 (-36) 36 0, p4 0 0 (-36) 72 (-36), p4 0 0 0 0 0, p4 0 0 0 0 0]

def evalP5 (p : P5) (t : Int) : Int :=
  p 0 + p 1*t + p 2*t^2 + p 3*t^3 + p 4*t^4

def endpointAt (t : Int) : Matrix Fin14 Fin14 Int := fun i j => evalP5 (endpoint14 i j) t

def p3Int (t : Int) : Int := 2*t^3 - 3*t^2 - t - 3
def p4Int (t : Int) : Int := 144*t^4 - 60*t^3 - 841*t^2 + 633*t + 258
def expectedEndpointDet (t : Int) : Int :=
  195689447424 * t^28 * (t-1)^8 * (t-2)^2 * p3Int t * p4Int t

/-- Row order putting the fixed seven-row pivot block first. -/
def endpointRowOrder : Fin14 → Fin14 :=
  ![0, 1, 2, 3, 4, 6, 7, 5, 8, 9, 10, 11, 12, 13]

def endpointRowOrderInv : Fin14 → Fin14 :=
  ![0, 1, 2, 3, 4, 7, 5, 6, 8, 9, 10, 11, 12, 13]

/-- Column order putting the fixed seven-column pivot block first.  The final two
complement columns are swapped so that the row and column permutations have the
same parity. -/
def endpointColOrder : Fin14 → Fin14 :=
  ![2, 3, 4, 5, 6, 10, 12, 0, 1, 7, 8, 9, 13, 11]

def endpointColOrderInv : Fin14 → Fin14 :=
  ![7, 8, 0, 1, 2, 3, 4, 9, 10, 11, 5, 13, 6, 12]

def endpointRowPerm : Equiv.Perm Fin14 where
  toFun := endpointRowOrder
  invFun := endpointRowOrderInv
  left_inv := by native_decide
  right_inv := by native_decide

def endpointColPerm : Equiv.Perm Fin14 where
  toFun := endpointColOrder
  invFun := endpointColOrderInv
  left_inv := by native_decide
  right_inv := by native_decide

/-- Reindex old row labels into a `7+7` block decomposition. -/
def endpointRowEquiv : Fin14 ≃ (Fin7 ⊕ Fin7) :=
  (finSumFinEquiv.trans endpointRowPerm).symm

/-- Reindex old column labels into a `7+7` block decomposition. -/
def endpointColEquiv : Fin14 ≃ (Fin7 ⊕ Fin7) :=
  (finSumFinEquiv.trans endpointColPerm).symm

/-- The integer endpoint matrix embedded in the rationals. -/
def endpointAtRat (t : Int) : Matrix Fin14 Fin14 ℚ :=
  (endpointAt t).map (Int.castRingHom ℚ)

/-- The endpoint matrix after the fixed independent row/column reindexing. -/
def endpointReindexed (t : Int) : Matrix (Fin7 ⊕ Fin7) (Fin7 ⊕ Fin7) ℚ :=
  Matrix.reindex endpointRowEquiv endpointColEquiv (endpointAtRat t)

/-- The fixed `7×7` pivot block. -/
def endpointPivot (t : Int) : Matrix Fin7 Fin7 ℚ :=
  (endpointReindexed t).toBlocks₁₁

/-- A computable inverse formula for the pivot block.  On the interpolation
points `1,...,56` its determinant is nonzero, so this is its actual inverse. -/
def endpointPivotInv (t : Int) : Matrix Fin7 Fin7 ℚ :=
  (Matrix.det (endpointPivot t))⁻¹ • Matrix.adjugate (endpointPivot t)

/-- The corresponding `7×7` Schur complement. -/
def endpointSchur (t : Int) : Matrix Fin7 Fin7 ℚ :=
  (endpointReindexed t).toBlocks₂₂ -
    (endpointReindexed t).toBlocks₂₁ * endpointPivotInv t *
      (endpointReindexed t).toBlocks₁₂

lemma endpoint_reindex_sign :
    Equiv.Perm.sign (endpointColEquiv.trans endpointRowEquiv.symm) = 1 := by
  native_decide

lemma endpoint_pivot_nonzero :
    ∀ k : Fin 57, k ≠ 0 → Matrix.det (endpointPivot (k : Int)) ≠ 0 := by
  native_decide

lemma endpoint_schur_57_values :
    ∀ k : Fin 57, k ≠ 0 →
      Matrix.det (endpointPivot (k : Int)) * Matrix.det (endpointSchur (k : Int)) =
        (expectedEndpointDet (k : Int) : ℚ) := by
  native_decide

lemma endpointAt_zero : endpointAt 0 = 0 := by
  native_decide

/-- Fifty-seven exact integer evaluations, enough to determine any polynomial of degree at most 56. -/
theorem endpoint_det_57_values :
    ∀ k : Fin 57, Matrix.det (endpointAt (k : Int)) = expectedEndpointDet (k : Int) := by
  intro k
  by_cases hk : k = 0
  · subst k
    change Matrix.det (endpointAt 0) = expectedEndpointDet 0
    rw [endpointAt_zero, Matrix.det_zero]
    norm_num [expectedEndpointDet]
  · have hpivot :
        Matrix.det ((endpointReindexed (k : Int)).toBlocks₁₁) ≠ 0 := by
      simpa [endpointPivot] using endpoint_pivot_nonzero k hk
    letI : Invertible (Matrix.det ((endpointReindexed (k : Int)).toBlocks₁₁)) :=
      invertibleOfNonzero hpivot
    letI : Invertible ((endpointReindexed (k : Int)).toBlocks₁₁) :=
      Matrix.invertibleOfDetInvertible _
    have hinv :
        ⅟((endpointReindexed (k : Int)).toBlocks₁₁) = endpointPivotInv (k : Int) := by
      rfl
    have hschur :
        Matrix.det (endpointReindexed (k : Int)) =
          Matrix.det (endpointPivot (k : Int)) * Matrix.det (endpointSchur (k : Int)) := by
      rw [← Matrix.fromBlocks_toBlocks (endpointReindexed (k : Int))]
      rw [Matrix.det_fromBlocks₁₁]
      rw [hinv]
      rfl
    have hreindex :
        Matrix.det (endpointReindexed (k : Int)) = Matrix.det (endpointAtRat (k : Int)) := by
      rw [endpointReindexed, Matrix.det_reindex, endpoint_reindex_sign]
      norm_num
    have hrat :
        Matrix.det (endpointAtRat (k : Int)) = (expectedEndpointDet (k : Int) : ℚ) := by
      rw [← hreindex, hschur]
      exact endpoint_schur_57_values k hk
    have hcast :
        ((Matrix.det (endpointAt (k : Int)) : Int) : ℚ) =
          Matrix.det (endpointAtRat (k : Int)) := by
      simpa [endpointAtRat] using
        (RingHom.map_det (Int.castRingHom ℚ) (endpointAt (k : Int)))
    exact_mod_cast hcast.trans hrat

end FormalResearch.QIC
