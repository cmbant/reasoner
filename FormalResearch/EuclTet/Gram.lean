module

public import Mathlib
public import FormalResearch.Racah.P3CayleyMenger

/-!
# Cayley--Menger determinant of a tetrahedron is `8·det(Gram) = 288 V²`

Sources: Weyl/P3 `lem:racah-cayley-menger` (appendix, "Geometric check for genuine tetrahedra":
`det CM = 288 𝒱²`), Weyl/P5 `cayley_menger_trichotomy.tex`, `eq:cm` ("a classical identity",
Blumenthal 1953).  Weyl/P3's `P3CayleyMenger` proves the *algebraic* Racah-parametrised identity
only; this module proves the geometric one.

## What is formalised (exact, all statements proved, no numerics)

* `cmDet2 x01 x02 x03 x12 x13 x23`: the bordered `5×5` Cayley--Menger determinant in the six squared
  edge lengths of the vertices `0,1,2,3` (the `P3.cmDet` of `P3CayleyMenger` is the same matrix with
  the entries `a²,…`; `cmDet_eq_cmDet2`).
* `gramX`: the Gram matrix `g_ij = (x_0i + x_0j - x_ij)/2` of the edge vectors `p_i - p_0`
  in terms of the squared edges.
* `cmDet2_eq_eight_det_gramX`: **`det CM = 8 det G`** as a polynomial identity in the six squared
  edges (the `n = 3` case of `det CM_n = (-1)^{n+1} 2^n det G`).
* `cmPts_eq_eight_det_edgeGram`: for four points of an *arbitrary* real inner product space,
  `det CM(‖p_i - p_j‖²) = 8 det (⟪p_i - p_0, p_j - p_0⟫)`.  Hence `det CM ≥ 0`
  (`cmPts_nonneg`), and `det CM > 0` iff the three edge vectors are linearly independent
  (`cmPts_pos_iff`), `det CM = 0` iff they are dependent (`cmPts_eq_zero_iff`): the trichotomy of the
  P5 chassis restricted to the realisable side.
* `cmPts_eq_288_tetVol_sq` (**`eq:cm`, `det CM = 288 V²`**): for four points of `ℝ³`
  (`EuclideanSpace ℝ (Fin 3)`), `det CM = 288 V²` with `V = |det(p₁-p₀, p₂-p₀, p₃-p₀)|/6`
  (`tetVol`), and the same statement with the `P3.cmDet` of the six distances
  (`cmDet_dist_eq_288_tetVol_sq`).
* `exists_points_of_posSemidef_gramX` (Blumenthal, the *realisation* direction in the cheap form): if
  the `3×3` matrix `gramX x` is positive semidefinite then there are four points of `ℝ³` with the six
  squared distances `x`; conversely realisable `x` have PSD `gramX` (`posSemidef_gramX_of_points`).

## Not formalised

* `V` is *defined* as `|det|/6`; the identification with the Lebesgue measure of the convex hull of
  the four points is not formalised.
* Blumenthal's full criterion (`det CM ≥ 0` together with the triangle inequalities on the faces
  implies realisability in `ℝ³`) needs the Sylvester-type criterion for positive semidefiniteness of
  a `3×3` matrix by its principal minors, which is not in Mathlib; only the Gram-matrix form of the
  criterion above is proved.
* The general `n`-simplex version `det CM_n = (-1)^{n+1} 2^n det G` (here only `n = 3`).
-/

@[expose] public section

namespace FormalResearch.EuclTet

open Matrix

/-- The bordered Cayley--Menger determinant of four points with squared edge lengths
`x_{ij}` (vertices `0,1,2,3`; the border row/column has entries `1`, `0` in the corner). -/
def cmDet2 (x01 x02 x03 x12 x13 x23 : ℝ) : ℝ :=
  (!![0, 1, 1, 1, 1;
      1, 0, x01, x02, x03;
      1, x01, 0, x12, x13;
      1, x02, x12, 0, x23;
      1, x03, x13, x23, 0] : Matrix (Fin 5) (Fin 5) ℝ).det

/-- `P3.cmDet a b c d e f` (edges `d₁₂=a, d₂₃=b, d₁₃=c, d₃₄=d, d₁₄=e, d₂₄=f` on vertices `1..4`)
is `cmDet2` of the squares, in the vertex labelling `0..3` (`01=a, 12=b, 02=c, 23=d, 03=e, 13=f`). -/
theorem cmDet_eq_cmDet2 (a b c d e f : ℝ) :
    FormalResearch.Racah.P3.cmDet a b c d e f = cmDet2 (a ^ 2) (c ^ 2) (e ^ 2) (b ^ 2) (f ^ 2) (d ^ 2) :=
  rfl

/-- The Gram matrix of the edge vectors `p₁-p₀, p₂-p₀, p₃-p₀` in terms of the squared edge lengths. -/
noncomputable def gramX (x01 x02 x03 x12 x13 x23 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![x01, (x01 + x02 - x12) / 2, (x01 + x03 - x13) / 2;
     (x01 + x02 - x12) / 2, x02, (x02 + x03 - x23) / 2;
     (x01 + x03 - x13) / 2, (x02 + x03 - x23) / 2, x03]

/-- **`det CM = 8 det G`**, a polynomial identity in the six squared edge lengths. -/
theorem cmDet2_eq_eight_det_gramX (x01 x02 x03 x12 x13 x23 : ℝ) :
    cmDet2 x01 x02 x03 x12 x13 x23 = 8 * (gramX x01 x02 x03 x12 x13 x23).det := by
  simp [cmDet2, gramX, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

section Points

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Squared distance of two of the four points. -/
noncomputable def sqd (p : Fin 4 → E) (i j : Fin 4) : ℝ := ‖p i - p j‖ ^ 2

/-- The Cayley--Menger determinant of four points. -/
noncomputable def cmPts (p : Fin 4 → E) : ℝ :=
  cmDet2 (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3)

/-- The Gram matrix of the edge vectors `p_i - p_0`, `i = 1,2,3`. -/
noncomputable def edgeGram (p : Fin 4 → E) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.gram ℝ (fun i : Fin 3 => p i.succ - p 0)

private lemma sqd_polar (u v : E) :
    ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * inner ℝ u v := by
  rw [norm_sub_sq_real]; ring

/-- Polarisation: the Gram matrix of the edge vectors is `gramX` of the squared distances. -/
theorem gramX_sqd (p : Fin 4 → E) :
    gramX (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3) = edgeGram p := by
  have key : ∀ i j : Fin 4, sqd p i j =
      ‖p i - p 0‖ ^ 2 + ‖p j - p 0‖ ^ 2 - 2 * inner ℝ (p i - p 0) (p j - p 0) := by
    intro i j
    unfold sqd
    have : p i - p j = (p i - p 0) - (p j - p 0) := by abel
    rw [this, sqd_polar]
  have h0 : ∀ i : Fin 4, sqd p 0 i = ‖p i - p 0‖ ^ 2 := by
    intro i; unfold sqd; rw [norm_sub_rev]
  have k12 : sqd p 1 2 = ‖p 1 - p 0‖ ^ 2 + ‖p 2 - p 0‖ ^ 2 - 2 * inner ℝ (p 1 - p 0) (p 2 - p 0) :=
    key 1 2
  have k13 : sqd p 1 3 = ‖p 1 - p 0‖ ^ 2 + ‖p 3 - p 0‖ ^ 2 - 2 * inner ℝ (p 1 - p 0) (p 3 - p 0) :=
    key 1 3
  have k23 : sqd p 2 3 = ‖p 2 - p 0‖ ^ 2 + ‖p 3 - p 0‖ ^ 2 - 2 * inner ℝ (p 2 - p 0) (p 3 - p 0) :=
    key 2 3
  have a1 := h0 1
  have a2 := h0 2
  have a3 := h0 3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramX, edgeGram, Matrix.gram_apply, Fin.succ, real_inner_comm,
      a1, a2, a3] <;> linarith [real_inner_comm (p 1 - p 0) (p 2 - p 0),
        real_inner_comm (p 1 - p 0) (p 3 - p 0), real_inner_comm (p 2 - p 0) (p 3 - p 0)]

/-- **`det CM = 8 det G` for four points of any real inner product space.** -/
theorem cmPts_eq_eight_det_edgeGram (p : Fin 4 → E) : cmPts p = 8 * (edgeGram p).det := by
  unfold cmPts
  rw [cmDet2_eq_eight_det_gramX, gramX_sqd]

/-- `det CM ≥ 0` for every four points of a real inner product space (the Gram determinant is
nonnegative). -/
theorem cmPts_nonneg (p : Fin 4 → E) : 0 ≤ cmPts p := by
  rw [cmPts_eq_eight_det_edgeGram]
  have := (Matrix.posSemidef_gram ℝ (fun i : Fin 3 => p i.succ - p 0)).det_nonneg
  exact mul_nonneg (by norm_num) this

/-- `det CM ≠ 0` iff the three edge vectors are linearly independent (nondegenerate tetrahedron). -/
theorem cmPts_ne_zero_iff (p : Fin 4 → E) :
    cmPts p ≠ 0 ↔ LinearIndependent ℝ (fun i : Fin 3 => p i.succ - p 0) := by
  rw [cmPts_eq_eight_det_edgeGram, ← Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)]
  unfold edgeGram
  constructor
  · intro h h0; apply h; rw [h0]; simp
  · intro h h0; apply h; linarith

theorem cmPts_pos_iff (p : Fin 4 → E) :
    0 < cmPts p ↔ LinearIndependent ℝ (fun i : Fin 3 => p i.succ - p 0) := by
  rw [← cmPts_ne_zero_iff]
  exact ⟨fun h => h.ne', fun h => (cmPts_nonneg p).lt_of_ne' h⟩

theorem cmPts_eq_zero_iff (p : Fin 4 → E) :
    cmPts p = 0 ↔ ¬ LinearIndependent ℝ (fun i : Fin 3 => p i.succ - p 0) := by
  rw [← cmPts_ne_zero_iff]; exact not_not.symm

end Points

section R3

/-- Euclidean `3`-space. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- The matrix whose rows are the edge vectors `p_i - p_0`, `i = 1,2,3`. -/
def edgeMat (p : Fin 4 → R3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => p i.succ j - p 0 j

/-- The signed volume `6 V_signed = det(p₁-p₀, p₂-p₀, p₃-p₀)`. -/
def tetDet (p : Fin 4 → R3) : ℝ := (edgeMat p).det

/-- The volume `V = |det(p₁-p₀, p₂-p₀, p₃-p₀)|/6` of the tetrahedron. -/
noncomputable def tetVol (p : Fin 4 → R3) : ℝ := |tetDet p| / 6

theorem edgeGram_eq_mul (p : Fin 4 → R3) : edgeGram p = edgeMat p * (edgeMat p)ᵀ := by
  ext i j
  simp [edgeGram, Matrix.gram_apply, edgeMat, Matrix.mul_apply, PiLp.inner_apply, mul_comm,
    Fin.sum_univ_succ]

theorem det_edgeGram_eq_sq (p : Fin 4 → R3) : (edgeGram p).det = tetDet p ^ 2 := by
  rw [edgeGram_eq_mul, Matrix.det_mul, Matrix.det_transpose]; unfold tetDet; ring

/-- **`eq:cm`: `det CM = 288 V²`** for four points of `ℝ³`, `V = |det(p₁-p₀,p₂-p₀,p₃-p₀)|/6`. -/
theorem cmPts_eq_288_tetVol_sq (p : Fin 4 → R3) : cmPts p = 288 * tetVol p ^ 2 := by
  rw [cmPts_eq_eight_det_edgeGram, det_edgeGram_eq_sq]
  unfold tetVol
  rw [div_pow, sq_abs]; ring

/-- The same with the Racah/P3 form `P3.cmDet` of the six distances (Mathlib `dist`). -/
theorem cmDet_dist_eq_288_tetVol_sq (p : Fin 4 → R3) :
    FormalResearch.Racah.P3.cmDet (dist (p 0) (p 1)) (dist (p 1) (p 2)) (dist (p 0) (p 2))
      (dist (p 2) (p 3)) (dist (p 0) (p 3)) (dist (p 1) (p 3)) = 288 * tetVol p ^ 2 := by
  rw [← cmPts_eq_288_tetVol_sq, cmDet_eq_cmDet2]
  unfold cmPts sqd
  simp only [dist_eq_norm]

/-- `V > 0` iff the four points are not coplanar iff `det CM > 0`. -/
theorem tetVol_pos_iff (p : Fin 4 → R3) : 0 < tetVol p ↔ 0 < cmPts p := by
  rw [cmPts_eq_288_tetVol_sq]
  constructor
  · intro h; positivity
  · intro h
    rcases (sq_nonneg (tetVol p)).lt_or_eq with h1 | h1
    · exact lt_of_le_of_ne (by unfold tetVol; positivity) (fun h2 => by rw [← h2] at h1; simp at h1)
    · rw [← h1] at h; simp at h

end R3


section Realisation

/-- Realisable squared distances have positive semidefinite `gramX` (the cheap direction of
Blumenthal's criterion). -/
theorem posSemidef_gramX_of_points {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : Fin 4 → E) :
    (gramX (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3)).PosSemidef := by
  rw [gramX_sqd]; exact Matrix.posSemidef_gram ℝ _

open scoped MatrixOrder in
/-- **Blumenthal realisation, Gram form.**  If `gramX x` is positive semidefinite, the six squared
edge lengths `x` are realised by four points of `ℝ³` (`p₀ = 0`, `p_i` the `i`-th column of the
positive square root of the Gram matrix). -/
theorem exists_points_of_posSemidef_gramX {x01 x02 x03 x12 x13 x23 : ℝ}
    (h : (gramX x01 x02 x03 x12 x13 x23).PosSemidef) :
    ∃ p : Fin 4 → R3, sqd p 0 1 = x01 ∧ sqd p 0 2 = x02 ∧ sqd p 0 3 = x03 ∧
      sqd p 1 2 = x12 ∧ sqd p 1 3 = x13 ∧ sqd p 2 3 = x23 := by
  set G := gramX x01 x02 x03 x12 x13 x23 with hG
  set B : Matrix (Fin 3) (Fin 3) ℝ := CFC.sqrt G with hB
  have hBB : B * B = G := CFC.sqrt_mul_sqrt_self G h.nonneg
  have hBsymm : Bᵀ = B := by
    have := (CFC.sqrt_nonneg G).posSemidef.isHermitian
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  let p : Fin 4 → R3 := Fin.cons 0 (fun i => WithLp.toLp 2 (fun k => B k i))
  have hgram : edgeGram p = G := by
    ext i j
    have := congrFun (congrFun hBB i) j
    simp only [edgeGram, Matrix.gram_apply, Matrix.mul_apply] at this ⊢
    rw [← this]
    simp [p, PiLp.inner_apply, mul_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := congrFun (congrFun hBsymm i) k
    simp only [Matrix.transpose_apply] at this
    rw [this]
  have e := gramX_sqd p
  rw [hgram] at e
  have e00 := congrFun (congrFun e 0) 0
  have e11 := congrFun (congrFun e 1) 1
  have e22 := congrFun (congrFun e 2) 2
  have e01 := congrFun (congrFun e 0) 1
  have e02 := congrFun (congrFun e 0) 2
  have e12 := congrFun (congrFun e 1) 2
  simp [gramX, hG] at e00 e11 e22 e01 e02 e12
  exact ⟨p, e00, e11, e22, by linarith, by linarith, by linarith⟩

end Realisation

/-- info: 'FormalResearch.EuclTet.cmDet2_eq_eight_det_gramX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cmDet2_eq_eight_det_gramX

/-- info: 'FormalResearch.EuclTet.cmPts_eq_eight_det_edgeGram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cmPts_eq_eight_det_edgeGram

/-- info: 'FormalResearch.EuclTet.cmPts_eq_288_tetVol_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cmPts_eq_288_tetVol_sq

/-- info: 'FormalResearch.EuclTet.cmDet_dist_eq_288_tetVol_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cmDet_dist_eq_288_tetVol_sq

/-- info: 'FormalResearch.EuclTet.cmPts_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cmPts_pos_iff

/-- info: 'FormalResearch.EuclTet.tetVol_pos_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tetVol_pos_iff

/-- info: 'FormalResearch.EuclTet.exists_points_of_posSemidef_gramX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_points_of_posSemidef_gramX

end FormalResearch.EuclTet
