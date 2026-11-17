module

public import Mathlib
public import FormalResearch.EuclTet.Dichotomy

/-!
# Planar tetrahedra: the affine dependency, `∂D/∂x_ij = 2cλ_iλ_j`, and Radon's dichotomy

Sources: Weyl/P5 `cayley_menger_trichotomy.tex`: `thm:smooth` (`eq:dDlambda`: at a planar wall point
`∂D/∂x_{ij} = 2c λ_iλ_j`, `λ` the affine dependency of the four points; the edge coordinate `x_ij` is
transverse exactly when the faces opposite `i`, `j` are nondegenerate), `prop:inertia` (the planar
coefficient `c` is negative), `thm:radon` (Radon in Cayley--Menger form: the sign pattern of `λ` is `(2,2)` or
`(3,1)`, and the table of the vanishing-angle set `E`), `cor:gradsignature` (`n₊ = |E|`, `n₊ = 4` or `3`).

Setting.  `p : Fin 4 → ℝ³` are four coplanar points (`tetDet p = 0`, equivalently `det CM = 0`) of which
the face `m` is nondegenerate (`Planar p m`).  The area vectors `N_i` (`FormalResearch.EuclTet.AreaVec`) are
then all parallel to the unit normal `n = N_m/‖N_m‖`: `N_i = λ_i n` with `λ_i = ⟪N_i, n⟫` the *signed
area* of the face opposite `p_i` (`λ_m = ‖N_m‖ > 0`).

## What is formalised (exact, proved)

* `areaVec_eq_lam_smul`: `N_i = λ_i n` (from Jacobi's identity `C_ii C_jj = C_ij²` at `det CM = 0`).
* `lam_sum` (`∑ λ_i = 0`) and `lam_affine_dependency` (`∑ λ_i p_i = 0`): `λ` is an affine dependency of the
  four points.
* `cmMat2_mulVec_lam` (`eq:dDlambda`, kernel part): `M · (v₀, λ) = 0` with `v₀ = -∑ λ_j ‖p_j‖²`.
* `cofP_eq_lam` (**`eq:dDlambda`**): `C_ij = -16 λ_i λ_j`, hence `∂D/∂x_ij = 2C_ij = 2c λ_iλ_j` with
  `c = -16 < 0` for the signed-area normalisation of `λ` (`prop:inertia`, planar sign of `c`);
  `hasDerivAt_cmDet2_x01_planar … x23_planar` (the six derivatives, `∂D/∂x_ij = 2·(-16)·λ_iλ_j`),
  `cofP_ne_zero_iff` (**transversality**): `∂D/∂x_ij ≠ 0 ⇔` the faces opposite `i` and `j` are nondegenerate
  (`lam_eq_zero_iff`: `λ_i = 0 ⇔ N_i = 0 ⇔ C_ii = 0`).
* Under `StrictPlanar` (all four faces nondegenerate): `StrictPlanar.lam_ne_zero`, `radon_signs` (**`thm:radon`**: the sign
  pattern of `λ` is `(2,2)`, or `(3,1)` up to an overall sign), `radon_partition` (the Radon partition: the
  positive and negative parts have the same total weight `s > 0` and the same barycentre, i.e. the
  convex hulls of the two classes meet), `radon_interior_point_neg`, `radon_interior_point_pos` (pattern `(3,1)`: the point of
  the singleton class lies in the open triangle spanned by the other three).
* `dihedral_eq_zero_iff` (`cor:combinatorial` for points): `θ_ij = 0 ⇔ λ_iλ_j < 0`, `θ_ij = π ⇔ λ_iλ_j > 0`.
* `nPlus_eq_four_of_22`, `nPlus_eq_three_of_31` (**`cor:gradsignature`**): the number `n₊` of edges with
  `∂D/∂x_ij > 0` is `4` in the `(2,2)` pattern and `3` in the `(3,1)` pattern; `card_flat_eq_nPlus`: `|E| = n₊`
  where `E` is the set of edges at which the dihedral angle vanishes.
* `flat_edge_iff_22`, `flat_edge_iff_31` (**the `thm:radon` table**): for the edge `kl` shared by the faces `i`,
  `j`: in the `(2,2)` pattern `θ = 0 ⇔ λ_kλ_l < 0` (the four sides), in the `(3,1)` pattern `θ = 0 ⇔ λ_kλ_l > 0`
  (the three edges of the outer triangle).

## Not formalised

* The inertia `(1,3,1)` of the bordered distance matrix (`prop:inertia`) and the general-`d` statement; only
  its consequence for the planar sign of `c` (here `c = -16` from the explicit formula).
* The border row/column of the adjugate `adj M = c v vᵀ` (only the vertex block `C_ij` and the kernel
  statement `M v = 0` are proved; corank exactly one is not proved as such).
* The identification of the sign patterns with "convex quadrilateral / point inside a triangle" is the content
  of `radon_partition` and `radon_interior_point_neg/pos` (for the `(2,2)` pattern, only the common point of the
  two chords with positive weights; no statement about convex position); the existence of the planar embedding in `ℝ²` is not
  separately constructed (points are taken in `ℝ³` with `tetDet = 0`).
* The `n`-simplex statement `cor:general-simplex-wall`.
-/

@[expose] public section

namespace FormalResearch.EuclTet

open Matrix

section Planar

/-- Four points of `ℝ³` that are coplanar (`tetDet p = 0`) with the face opposite `p_m` nondegenerate. -/
structure Planar (p : Fin 4 → R3) (m : Fin 4) : Prop where
  det_zero : tetDet p = 0
  face_ne : areaVec p m ≠ 0

/-- The unit normal `N_m/‖N_m‖` of the plane. -/
noncomputable def unitNormal (p : Fin 4 → R3) (m : Fin 4) : R3 := (‖areaVec p m‖)⁻¹ • areaVec p m

/-- The signed area `λ_i = ⟪N_i, n⟫` of the face opposite `p_i` (`N_i = λ_i n`). -/
noncomputable def lam (p : Fin 4 → R3) (m : Fin 4) (i : Fin 4) : ℝ :=
  inner ℝ (areaVec p i) (unitNormal p m)

variable {p : Fin 4 → R3} {m : Fin 4}

theorem cmPts_eq_zero_of_tetDet (h : tetDet p = 0) : cmPts p = 0 := by
  rw [cmPts_eq_288_tetVol_sq]; simp [tetVol, h]

theorem cofP_sq_eq (h : tetDet p = 0) (i j : Fin 4) :
    cofP p i j ^ 2 = cofP p i i * cofP p j j := by
  by_cases hij : i = j
  · subst hij; ring
  · have := cof_jacobi_pair (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3)
      i j hij
    have hD : cmDet2 (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3) = 0 :=
      cmPts_eq_zero_of_tetDet h
    rw [hD] at this
    unfold cofP
    linarith

theorem inner_areaVec_sq_eq (h : tetDet p = 0) (i j : Fin 4) :
    inner ℝ (areaVec p i) (areaVec p j) ^ 2 = ‖areaVec p i‖ ^ 2 * ‖areaVec p j‖ ^ 2 := by
  rw [inner_areaVec', norm_sq_areaVec, norm_sq_areaVec]
  have := cofP_sq_eq h i j
  linear_combination (1 / 256 : ℝ) * this

theorem norm_unitNormal (hp : Planar p m) : ‖unitNormal p m‖ = 1 := by
  unfold unitNormal
  rw [norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp.face_ne)

/-- **All area vectors are parallel to the normal**: `N_i = λ_i n`. -/
theorem areaVec_eq_lam_smul (hp : Planar p m) (i : Fin 4) :
    areaVec p i = lam p m i • unitNormal p m := by
  set w := areaVec p m with hw
  set u := areaVec p i with hu
  have hw0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hp.face_ne
  have hCS : inner ℝ u w ^ 2 = ‖u‖ ^ 2 * ‖w‖ ^ 2 := inner_areaVec_sq_eq hp.det_zero i m
  have hz : inner ℝ (‖w‖ ^ 2 • u - inner ℝ u w • w) (‖w‖ ^ 2 • u - inner ℝ u w • w) = 0 := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      real_inner_self_eq_norm_sq, RCLike.conj_to_real, real_inner_comm u w]
    linear_combination (-‖w‖ ^ 2) * hCS
  have hz' : ‖w‖ ^ 2 • u = inner ℝ u w • w :=
    sub_eq_zero.mp (inner_self_eq_zero.mp hz)
  have hu' : u = (‖w‖ ^ 2)⁻¹ • (inner ℝ u w • w) := by
    have : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero 2 hw0
    rw [← hz', smul_smul, inv_mul_cancel₀ this, one_smul]
  unfold lam unitNormal
  rw [← hw, ← hu, inner_smul_right, hu']
  simp only [smul_smul, real_inner_smul_left, real_inner_self_eq_norm_sq]
  congr 1
  field_simp

theorem lam_eq_zero_iff (hp : Planar p m) (i : Fin 4) : lam p m i = 0 ↔ areaVec p i = 0 := by
  constructor
  · intro h; rw [areaVec_eq_lam_smul hp i, h, zero_smul]
  · intro h
    have := areaVec_eq_lam_smul hp i
    rw [h] at this
    rcases smul_eq_zero.mp this.symm with h0 | h0
    · exact h0
    · exact absurd h0 (by intro hh; have := norm_unitNormal hp; rw [hh] at this; simp at this)

theorem lam_sum (hp : Planar p m) : ∑ i, lam p m i = 0 := by
  have h := areaVec_sum p
  simp_rw [areaVec_eq_lam_smul hp] at h
  rw [← Finset.sum_smul] at h
  rcases smul_eq_zero.mp h with h0 | h0
  · exact h0
  · exact absurd h0 (by intro hh; have := norm_unitNormal hp; rw [hh] at this; simp at this)

/-- **`eq:dDlambda`**: `C_ij = -16 λ_i λ_j`; so `∂D/∂x_ij = 2C_ij = 2c λ_iλ_j` with `c = -16 < 0`. -/
theorem cofP_eq_lam (hp : Planar p m) (i j : Fin 4) :
    cofP p i j = -16 * (lam p m i * lam p m j) := by
  have h := inner_areaVec' p i j
  rw [areaVec_eq_lam_smul hp i, areaVec_eq_lam_smul hp j, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, norm_unitNormal hp] at h
  linarith

/-- **Transversality** (`thm:smooth`): `∂D/∂x_ij = 2 C_ij` is nonzero exactly when the faces opposite
`i` and `j` are nondegenerate. -/
theorem cofP_ne_zero_iff (hp : Planar p m) (i j : Fin 4) :
    cofP p i j ≠ 0 ↔ areaVec p i ≠ 0 ∧ areaVec p j ≠ 0 := by
  rw [cofP_eq_lam hp]
  simp only [ne_eq, ← lam_eq_zero_iff hp, mul_eq_zero, not_or]
  norm_num

/-- The Cramer identity for the three edge vectors. -/
theorem cramer_edges (p : Fin 4 → R3) (v : R3) :
    inner ℝ (areaVec p 1) v • (p 1 - p 0) + inner ℝ (areaVec p 2) v • (p 2 - p 0) +
      inner ℝ (areaVec p 3) v • (p 3 - p 0) = (tetDet p / 2) • v := by
  ext k
  simp only [inner_r3, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  simp only [tetDet, edgeMat, Matrix.det_fin_three, areaVec, cross3]
  fin_cases k <;> simp <;> ring

/-- `λ` is an affine dependency of the four points: `∑ λ_i p_i = 0` (with `∑ λ_i = 0`). -/
theorem lam_affine_dependency (hp : Planar p m) : ∑ i, lam p m i • p i = 0 := by
  have h := cramer_edges p (unitNormal p m)
  rw [hp.det_zero, zero_div, zero_smul] at h
  have hs := lam_sum hp
  rw [Fin.sum_univ_four] at hs ⊢
  have e : lam p m 0 • p 0 + lam p m 1 • p 1 + lam p m 2 • p 2 + lam p m 3 • p 3 =
      (lam p m 1 • (p 1 - p 0) + lam p m 2 • (p 2 - p 0) + lam p m 3 • (p 3 - p 0)) +
        (lam p m 0 + lam p m 1 + lam p m 2 + lam p m 3) • p 0 := by
    simp only [smul_sub, add_smul]; abel
  rw [e, hs, zero_smul, add_zero]
  exact h

theorem sum_lam_inner (hp : Planar p m) (i : Fin 4) : ∑ j, lam p m j * inner ℝ (p i) (p j) = 0 := by
  have := congrArg (fun v => inner ℝ (p i) v) (lam_affine_dependency hp)
  simpa [inner_sum, inner_smul_right] using this

theorem sum_lam_sqd (hp : Planar p m) (i : Fin 4) :
    ∑ j, lam p m j * sqd p i j = ∑ j, lam p m j * ‖p j‖ ^ 2 := by
  have h1 := sum_lam_inner hp i
  have hs := lam_sum hp
  rw [Fin.sum_univ_four] at h1 hs ⊢
  simp only [sqd, norm_sub_sq_real, Fin.sum_univ_four]
  linear_combination (‖p i‖ ^ 2) * hs + (-2) * h1

/-- **`eq:dDlambda`, kernel part**: `M (v₀, λ) = 0` for the bordered Cayley--Menger matrix `M`,
`v₀ = -∑ λ_j ‖p_j‖²`. -/
theorem cmMat2_mulVec_lam (hp : Planar p m) :
    cmMat2 (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3) *ᵥ
      ![-(∑ j, lam p m j * ‖p j‖ ^ 2), lam p m 0, lam p m 1, lam p m 2, lam p m 3] = 0 := by
  have hs := lam_sum hp
  rw [Fin.sum_univ_four] at hs
  have hr := fun i => sum_lam_sqd hp i
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  have h3 := hr 3
  simp only [Fin.sum_univ_four, sqd, sub_self, norm_zero, norm_sub_rev (p 1) (p 0),
    norm_sub_rev (p 2) (p 0), norm_sub_rev (p 3) (p 0), norm_sub_rev (p 2) (p 1),
    norm_sub_rev (p 3) (p 1), norm_sub_rev (p 3) (p 2)] at h0 h1 h2 h3
  ext i
  fin_cases i <;>
    simp [cmMat2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, sqd] <;>
    linarith

end Planar

section Radon

open Real

/-- Four coplanar points all of whose faces are nondegenerate (Hypothesis `hyp:faces` at a planar wall
point). -/
structure StrictPlanar (p : Fin 4 → R3) : Prop where
  planar : Planar p 0
  faces_ne : ∀ i, areaVec p i ≠ 0

variable {p : Fin 4 → R3}

theorem StrictPlanar.lam_ne_zero (hp : StrictPlanar p) (i : Fin 4) : lam p 0 i ≠ 0 :=
  fun h => hp.faces_ne i ((lam_eq_zero_iff hp.planar i).mp h)

/-- Indices of the vertices with positive signed face-area. -/
noncomputable def posSet (p : Fin 4 → R3) : Finset (Fin 4) := Finset.univ.filter fun i => 0 < lam p 0 i

/-- Indices of the vertices with negative signed face-area. -/
noncomputable def negSet (p : Fin 4 → R3) : Finset (Fin 4) := Finset.univ.filter fun i => lam p 0 i < 0

theorem StrictPlanar.card_pos_add_card_neg (hp : StrictPlanar p) :
    (posSet p).card + (negSet p).card = 4 := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 4)))
    (fun i => 0 < lam p 0 i)
  have e : negSet p = Finset.univ.filter fun i => ¬ 0 < lam p 0 i := by
    unfold negSet
    refine Finset.filter_congr fun i _ => ?_
    have := hp.lam_ne_zero i
    constructor
    · intro h; exact not_lt.mpr h.le
    · intro h; exact lt_of_le_of_ne (not_lt.mp h) this
  rw [e]
  simp only [Finset.card_univ, Fintype.card_fin] at h
  exact h

theorem StrictPlanar.one_le_card_pos (hp : StrictPlanar p) : 1 ≤ (posSet p).card := by
  by_contra h
  have h0 : posSet p = ∅ := Finset.card_eq_zero.mp (by omega)
  have hs := lam_sum hp.planar
  rw [Fin.sum_univ_four] at hs
  have hn : ∀ i, lam p 0 i < 0 := fun i => by
    have hi : i ∉ posSet p := by rw [h0]; simp
    have : ¬ 0 < lam p 0 i := by simpa [posSet] using hi
    exact lt_of_le_of_ne (not_lt.mp this) (hp.lam_ne_zero i)
  linarith [hn 0, hn 1, hn 2, hn 3]

theorem StrictPlanar.one_le_card_neg (hp : StrictPlanar p) : 1 ≤ (negSet p).card := by
  by_contra h
  have h0 : negSet p = ∅ := Finset.card_eq_zero.mp (by omega)
  have hs := lam_sum hp.planar
  rw [Fin.sum_univ_four] at hs
  have hn : ∀ i, 0 < lam p 0 i := fun i => by
    have hi : i ∉ negSet p := by rw [h0]; simp
    have : ¬ lam p 0 i < 0 := by simpa [negSet] using hi
    exact lt_of_le_of_ne (not_lt.mp this) (hp.lam_ne_zero i).symm
  linarith [hn 0, hn 1, hn 2, hn 3]

/-- **Radon's theorem, sign pattern (`thm:radon`)**: the signs of the affine dependency `λ` of four
coplanar points with nondegenerate faces form a `(2,2)` or a `(3,1)` pattern (up to overall sign). -/
theorem radon_signs (hp : StrictPlanar p) :
    ((posSet p).card = 2 ∧ (negSet p).card = 2) ∨ ((posSet p).card = 3 ∧ (negSet p).card = 1) ∨
      ((posSet p).card = 1 ∧ (negSet p).card = 3) := by
  have h1 := hp.card_pos_add_card_neg
  have h2 := hp.one_le_card_pos
  have h3 := hp.one_le_card_neg
  omega

/-- **The Radon partition**: the positive and the negative part of `λ` have the same total weight `s > 0`
and the same barycentre `∑_{λ_i>0} (λ_i/s) p_i = ∑_{λ_i<0} (-λ_i/s) p_i`, so the convex hulls of the two
classes of points meet in a point with strictly positive weights. -/
theorem radon_partition (hp : StrictPlanar p) :
    ∃ s : ℝ, 0 < s ∧ ∑ i ∈ posSet p, lam p 0 i = s ∧ ∑ i ∈ negSet p, (-lam p 0 i) = s ∧
      ∑ i ∈ posSet p, lam p 0 i • p i = ∑ i ∈ negSet p, (-lam p 0 i) • p i := by
  have hneg : negSet p = Finset.univ.filter fun i => ¬ 0 < lam p 0 i := by
    unfold negSet
    refine Finset.filter_congr fun i _ => ?_
    have := hp.lam_ne_zero i
    constructor
    · intro h; exact not_lt.mpr h.le
    · intro h; exact lt_of_le_of_ne (not_lt.mp h) this
  have hsum := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin 4)))
    (fun i => 0 < lam p 0 i) (fun i => lam p 0 i)
  have hvec := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin 4)))
    (fun i => 0 < lam p 0 i) (fun i => lam p 0 i • p i)
  rw [lam_sum hp.planar] at hsum
  rw [lam_affine_dependency hp.planar] at hvec
  have hne : (posSet p).Nonempty := Finset.card_pos.mp hp.one_le_card_pos
  refine ⟨∑ i ∈ posSet p, lam p 0 i, Finset.sum_pos (fun i hi => by simpa [posSet] using hi) hne,
    rfl, ?_, ?_⟩
  · rw [Finset.sum_neg_distrib, hneg]
    unfold posSet
    linarith
  · rw [hneg]
    simp only [neg_smul, Finset.sum_neg_distrib]
    unfold posSet
    exact eq_neg_of_add_eq_zero_left hvec

/-- Convex-combination form of a Radon relation: if `μ` is an affine dependency with `μ_j < 0 < μ_i`
for `i ≠ j`, then `p_j` is a convex combination, with positive weights, of the other three points. -/
theorem convex_of_dependency (μ : Fin 4 → ℝ) (j : Fin 4) (hμj : μ j < 0)
    (hμ : ∀ i, i ≠ j → 0 < μ i) (hsum : ∑ i, μ i = 0) (hvec : ∑ i, μ i • p i = 0) :
    (∀ i, i ≠ j → 0 < μ i / (-μ j)) ∧ ∑ i ∈ Finset.univ.erase j, μ i / (-μ j) = 1 ∧
      p j = ∑ i ∈ Finset.univ.erase j, (μ i / (-μ j)) • p i := by
  have hne : -μ j ≠ 0 := by linarith
  refine ⟨fun i hi => div_pos (hμ i hi) (by linarith), ?_, ?_⟩
  · rw [← Finset.sum_div, div_eq_one_iff_eq hne]
    have := Finset.add_sum_erase Finset.univ μ (Finset.mem_univ j)
    linarith
  · have h := Finset.add_sum_erase Finset.univ (fun i => μ i • p i) (Finset.mem_univ j)
    rw [hvec] at h
    have h2 : ∑ i ∈ Finset.univ.erase j, μ i • p i = (-μ j) • p j := by
      rw [neg_smul]; exact eq_neg_of_add_eq_zero_right h
    simp_rw [div_eq_inv_mul, mul_smul]
    rw [← Finset.smul_sum, h2, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- **Radon, pattern `(3,1)`**: if exactly one `λ_j` is negative, the point `p_j` lies in the open
triangle spanned by the other three (convex combination with positive weights). -/
theorem radon_interior_point_neg (hp : StrictPlanar p) {j : Fin 4} (hj : negSet p = {j}) :
    (∀ i, i ≠ j → 0 < lam p 0 i / (-lam p 0 j)) ∧
      ∑ i ∈ Finset.univ.erase j, lam p 0 i / (-lam p 0 j) = 1 ∧
      p j = ∑ i ∈ Finset.univ.erase j, (lam p 0 i / (-lam p 0 j)) • p i := by
  have hj' : lam p 0 j < 0 := by
    have : j ∈ negSet p := by rw [hj]; simp
    simpa [negSet] using this
  have hi : ∀ i, i ≠ j → 0 < lam p 0 i := by
    intro i hij
    by_contra h
    have h' : lam p 0 i < 0 := lt_of_le_of_ne (not_lt.mp h) (hp.lam_ne_zero i)
    have : i ∈ negSet p := by simpa [negSet] using h'
    rw [hj] at this
    exact hij (by simpa using this)
  exact convex_of_dependency (lam p 0) j hj' hi (lam_sum hp.planar) (lam_affine_dependency hp.planar)

/-- **Radon, pattern `(3,1)` (opposite sign)**: if exactly one `λ_j` is positive, `p_j` lies in the open
triangle spanned by the other three. -/
theorem radon_interior_point_pos (hp : StrictPlanar p) {j : Fin 4} (hj : posSet p = {j}) :
    (∀ i, i ≠ j → 0 < (-lam p 0 i) / (lam p 0 j)) ∧
      ∑ i ∈ Finset.univ.erase j, (-lam p 0 i) / (lam p 0 j) = 1 ∧
      p j = ∑ i ∈ Finset.univ.erase j, ((-lam p 0 i) / (lam p 0 j)) • p i := by
  have hj' : 0 < lam p 0 j := by
    have : j ∈ posSet p := by rw [hj]; simp
    simpa [posSet] using this
  have hi : ∀ i, i ≠ j → lam p 0 i < 0 := by
    intro i hij
    by_contra h
    have h' : 0 < lam p 0 i := lt_of_le_of_ne (not_lt.mp h) (hp.lam_ne_zero i).symm
    have : i ∈ posSet p := by simpa [posSet] using h'
    rw [hj] at this
    exact hij (by simpa using this)
  have hv : ∑ i, (-lam p 0 i) • p i = 0 := by
    simp only [neg_smul, Finset.sum_neg_distrib, lam_affine_dependency hp.planar, neg_zero]
  have hsm : ∑ i, (-lam p 0 i) = 0 := by
    simp only [Finset.sum_neg_distrib, lam_sum hp.planar, neg_zero]
  have := convex_of_dependency (fun i => -lam p 0 i) j (by simpa using hj')
    (fun i hij => by simpa using hi i hij) hsm hv
  simpa using this

end Radon

section Angles

open Real

variable {p : Fin 4 → R3}

theorem dihedral_nonneg (p : Fin 4 → R3) (i j : Fin 4) : 0 ≤ dihedral p i j := by
  unfold dihedral; linarith [InnerProductGeometry.angle_le_pi (areaVec p i) (areaVec p j)]

theorem dihedral_le_pi (p : Fin 4 → R3) (i j : Fin 4) : dihedral p i j ≤ Real.pi := by
  unfold dihedral; linarith [InnerProductGeometry.angle_nonneg (areaVec p i) (areaVec p j)]

/-- In the planar case with nondegenerate faces, `cos θ_ij = -λ_iλ_j/|λ_iλ_j|`. -/
theorem cos_dihedral_planar (hp : StrictPlanar p) (i j : Fin 4) :
    Real.cos (dihedral p i j) = -(lam p 0 i * lam p 0 j) / |lam p 0 i * lam p 0 j| := by
  unfold dihedral
  rw [Real.cos_pi_sub, InnerProductGeometry.cos_angle, inner_areaVec', cofP_eq_lam hp.planar]
  have hi := norm_sq_areaVec p i
  have hj := norm_sq_areaVec p j
  have ha : 0 < ‖areaVec p i‖ := norm_pos_iff.mpr (hp.faces_ne i)
  have hb : 0 < ‖areaVec p j‖ := norm_pos_iff.mpr (hp.faces_ne j)
  have e1 : ‖areaVec p i‖ = |lam p 0 i| := by
    rw [areaVec_eq_lam_smul hp.planar i, norm_smul, norm_unitNormal hp.planar]; simp
  have e2 : ‖areaVec p j‖ = |lam p 0 j| := by
    rw [areaVec_eq_lam_smul hp.planar j, norm_smul, norm_unitNormal hp.planar]; simp
  rw [e1, e2, ← abs_mul]
  have hq : |lam p 0 i * lam p 0 j| ≠ 0 :=
    abs_ne_zero.mpr (mul_ne_zero (hp.lam_ne_zero i) (hp.lam_ne_zero j))
  field_simp

/-- `θ_ij = 0` if `λ_iλ_j < 0`. -/
theorem dihedral_eq_zero_of_neg (hp : StrictPlanar p) (i j : Fin 4) (h : lam p 0 i * lam p 0 j < 0) :
    dihedral p i j = 0 := by
  have hc : Real.cos (dihedral p i j) = 1 := by
    rw [cos_dihedral_planar hp, abs_of_neg h]
    exact div_self (neg_ne_zero.mpr h.ne)
  have h2 := dihedral_le_pi p i j
  have := Real.pi_pos
  have := dihedral_nonneg p i j
  exact (Real.cos_eq_one_iff_of_lt_of_lt (by linarith) (by linarith)).mp hc

/-- `θ_ij = π` if `λ_iλ_j > 0`. -/
theorem dihedral_eq_pi_of_pos (hp : StrictPlanar p) (i j : Fin 4) (h : 0 < lam p 0 i * lam p 0 j) :
    dihedral p i j = Real.pi := by
  have hc : Real.cos (dihedral p i j) = Real.cos Real.pi := by
    rw [cos_dihedral_planar hp, abs_of_pos h, Real.cos_pi, neg_div, div_self h.ne']
  exact Real.injOn_cos ⟨dihedral_nonneg p i j, dihedral_le_pi p i j⟩
    ⟨Real.pi_pos.le, le_refl _⟩ hc

/-- **`cor:combinatorial` for planar points**: `θ_ij = 0 ⇔ λ_iλ_j < 0`. -/
theorem dihedral_eq_zero_iff (hp : StrictPlanar p) (i j : Fin 4) :
    dihedral p i j = 0 ↔ lam p 0 i * lam p 0 j < 0 := by
  constructor
  · intro h
    by_contra hn
    have hne : lam p 0 i * lam p 0 j ≠ 0 :=
      mul_ne_zero (hp.lam_ne_zero i) (hp.lam_ne_zero j)
    have := dihedral_eq_pi_of_pos hp i j (lt_of_le_of_ne (not_lt.mp hn) hne.symm)
    rw [h] at this
    exact Real.pi_ne_zero this.symm
  · exact dihedral_eq_zero_of_neg hp i j

/-- **`cor:combinatorial` for planar points**: `θ_ij = π ⇔ λ_iλ_j > 0`. -/
theorem dihedral_eq_pi_iff (hp : StrictPlanar p) (i j : Fin 4) :
    dihedral p i j = Real.pi ↔ 0 < lam p 0 i * lam p 0 j := by
  constructor
  · intro h
    by_contra hn
    have hne : lam p 0 i * lam p 0 j ≠ 0 :=
      mul_ne_zero (hp.lam_ne_zero i) (hp.lam_ne_zero j)
    have := dihedral_eq_zero_of_neg hp i j (lt_of_le_of_ne (not_lt.mp hn) hne)
    rw [h] at this
    exact Real.pi_ne_zero this
  · exact dihedral_eq_pi_of_pos hp i j

end Angles

section Counting

variable {p : Fin 4 → R3}

private theorem boolcount22 : ∀ s : Fin 4 → Bool, (Finset.univ.filter fun i => s i = true).card = 2 →
    (Finset.univ.filter fun ij : Fin 4 × Fin 4 => ij.1 < ij.2 ∧ s ij.1 ≠ s ij.2).card = 4 := by
  decide

private theorem boolcount31 : ∀ s : Fin 4 → Bool,
    ((Finset.univ.filter fun i => s i = true).card = 3 ∨
      (Finset.univ.filter fun i => s i = true).card = 1) →
    (Finset.univ.filter fun ij : Fin 4 × Fin 4 => ij.1 < ij.2 ∧ s ij.1 ≠ s ij.2).card = 3 := by
  decide

private theorem boolperm22 : ∀ s : Fin 4 → Bool, (Finset.univ.filter fun i => s i = true).card = 2 →
    ∀ i j k l : Fin 4, [i, j, k, l].Nodup → (s i ≠ s j ↔ s k ≠ s l) := by
  decide

private theorem boolperm31 : ∀ s : Fin 4 → Bool,
    ((Finset.univ.filter fun i => s i = true).card = 3 ∨
      (Finset.univ.filter fun i => s i = true).card = 1) →
    ∀ i j k l : Fin 4, [i, j, k, l].Nodup → (s i ≠ s j ↔ s k = s l) := by
  decide

/-- The sign vector of `λ`. -/
noncomputable def lamSign (p : Fin 4 → R3) (i : Fin 4) : Bool := decide (0 < lam p 0 i)

theorem filter_lamSign (p : Fin 4 → R3) :
    (Finset.univ.filter fun i => lamSign p i = true) = posSet p := by
  simp [lamSign, posSet]

theorem lam_mul_neg_iff (hp : StrictPlanar p) (i j : Fin 4) :
    lam p 0 i * lam p 0 j < 0 ↔ lamSign p i ≠ lamSign p j := by
  have hi := hp.lam_ne_zero i
  have hj := hp.lam_ne_zero j
  unfold lamSign
  rcases lt_or_gt_of_ne hi with a | a <;> rcases lt_or_gt_of_ne hj with b | b
  · have := mul_pos_of_neg_of_neg a b
    simp [not_lt.mpr a.le, not_lt.mpr b.le, not_lt.mpr this.le]
  · have := mul_neg_of_neg_of_pos a b
    simp [not_lt.mpr a.le, b, this]
  · have := mul_neg_of_pos_of_neg a b
    simp [a, not_lt.mpr b.le, this]
  · have := mul_pos a b
    simp [a, b, not_lt.mpr this.le]

theorem lam_mul_pos_iff (hp : StrictPlanar p) (i j : Fin 4) :
    0 < lam p 0 i * lam p 0 j ↔ lamSign p i = lamSign p j := by
  have hne : lam p 0 i * lam p 0 j ≠ 0 := mul_ne_zero (hp.lam_ne_zero i) (hp.lam_ne_zero j)
  have := lam_mul_neg_iff hp i j
  constructor
  · intro h; by_contra hc; have := this.mpr hc; linarith
  · intro h
    by_contra hc
    have : lam p 0 i * lam p 0 j < 0 := lt_of_le_of_ne (not_lt.mp hc) hne
    exact (lam_mul_neg_iff hp i j |>.mp this) h

/-- The number `n₊` of edges `ij` with `∂D/∂x_ij > 0` (`∂D/∂x_ij = 2 C_ij`). -/
noncomputable def nPlus (p : Fin 4 → R3) : ℕ :=
  (Finset.univ.filter fun ij : Fin 4 × Fin 4 => ij.1 < ij.2 ∧ 0 < cofP p ij.1 ij.2).card

/-- The number `|E|` of edges at which the dihedral angle vanishes (the edge `kl` shared by the faces
opposite `i < j`; `{i,j} ↦ {k,l}` is a bijection of the six edges). -/
noncomputable def nFlat (p : Fin 4 → R3) : ℕ :=
  (Finset.univ.filter fun ij : Fin 4 × Fin 4 => ij.1 < ij.2 ∧ dihedral p ij.1 ij.2 = 0).card

theorem cofP_pos_iff (hp : StrictPlanar p) (i j : Fin 4) :
    0 < cofP p i j ↔ lamSign p i ≠ lamSign p j := by
  rw [cofP_eq_lam hp.planar, ← lam_mul_neg_iff hp]
  constructor <;> intro h <;> nlinarith

theorem nPlus_eq_card_sign (hp : StrictPlanar p) :
    nPlus p = (Finset.univ.filter fun ij : Fin 4 × Fin 4 =>
      ij.1 < ij.2 ∧ lamSign p ij.1 ≠ lamSign p ij.2).card := by
  unfold nPlus
  congr 1
  refine Finset.filter_congr fun ij _ => ?_
  rw [cofP_pos_iff hp]

/-- **`cor:gradsignature`, `(2,2)` pattern**: `n₊ = 4`. -/
theorem nPlus_eq_four_of_22 (hp : StrictPlanar p) (h : (posSet p).card = 2) : nPlus p = 4 := by
  rw [nPlus_eq_card_sign hp]
  exact boolcount22 _ (by rw [filter_lamSign]; exact h)

/-- **`cor:gradsignature`, `(3,1)` pattern**: `n₊ = 3`. -/
theorem nPlus_eq_three_of_31 (hp : StrictPlanar p)
    (h : (posSet p).card = 3 ∨ (posSet p).card = 1) : nPlus p = 3 := by
  rw [nPlus_eq_card_sign hp]
  exact boolcount31 _ (by rw [filter_lamSign]; exact h)

/-- **`eq:Egradient`**: `|E| = n₊`, the number of edges with vanishing dihedral angle equals the number of
edges with positive `∂D/∂x`. -/
theorem card_flat_eq_nPlus (hp : StrictPlanar p) : nFlat p = nPlus p := by
  unfold nFlat nPlus
  congr 1
  refine Finset.filter_congr fun ij _ => ?_
  rw [dihedral_eq_zero_iff hp, cofP_eq_lam hp.planar]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> nlinarith

/-- **`cor:gradsignature`**: `|E| = 4` in the `(2,2)` pattern. -/
theorem nFlat_eq_four_of_22 (hp : StrictPlanar p) (h : (posSet p).card = 2) : nFlat p = 4 := by
  rw [card_flat_eq_nPlus hp, nPlus_eq_four_of_22 hp h]

/-- **`cor:gradsignature`**: `|E| = 3` in the `(3,1)` pattern. -/
theorem nFlat_eq_three_of_31 (hp : StrictPlanar p) (h : (posSet p).card = 3 ∨ (posSet p).card = 1) :
    nFlat p = 3 := by
  rw [card_flat_eq_nPlus hp, nPlus_eq_three_of_31 hp h]

/-- **The `thm:radon` table, `(2,2)`**: the edge `kl` shared by the faces opposite `i`, `j`
(`{i,j,k,l} = {0,1,2,3}`) has vanishing dihedral angle iff `λ_kλ_l < 0` (the four sides of the
convex quadrilateral). -/
theorem flat_edge_iff_22 (hp : StrictPlanar p) (h : (posSet p).card = 2) (i j k l : Fin 4)
    (hn : [i, j, k, l].Nodup) :
    dihedral p i j = 0 ↔ lam p 0 k * lam p 0 l < 0 := by
  rw [dihedral_eq_zero_iff hp, lam_mul_neg_iff hp, lam_mul_neg_iff hp]
  exact boolperm22 _ (by rw [filter_lamSign]; exact h) i j k l hn

/-- **The `thm:radon` table, `(3,1)`**: the edge `kl` shared by the faces opposite `i`, `j` has vanishing
dihedral angle iff `λ_kλ_l > 0` (the three edges of the outer triangle). -/
theorem flat_edge_iff_31 (hp : StrictPlanar p) (h : (posSet p).card = 3 ∨ (posSet p).card = 1)
    (i j k l : Fin 4) (hn : [i, j, k, l].Nodup) :
    dihedral p i j = 0 ↔ 0 < lam p 0 k * lam p 0 l := by
  rw [dihedral_eq_zero_iff hp, lam_mul_neg_iff hp, lam_mul_pos_iff hp]
  exact boolperm31 _ (by rw [filter_lamSign]; exact h) i j k l hn

end Counting

section DerivPlanar

variable {p : Fin 4 → R3} {m : Fin 4}

/-- **`eq:dDlambda`** for the edge `01`: at a planar wall point, `∂D/∂x_{01} = 2 C_{01} = 2c λ_0λ_1`
with `c = -16` (the sign of `c` is `prop:inertia`'s planar sign). -/
theorem hasDerivAt_cmDet2_x01_planar (hp : Planar p m) :
    HasDerivAt (fun s => cmDet2 s (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3))
      (2 * (-16) * (lam p m 0 * lam p m 1)) (sqd p 0 1) := by
  refine (hasDerivAt_cmDet2_x01 (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3)).congr_deriv ?_
  have e : cof01 (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3) = cofP p 0 1 := by simp [cofP, cofM]
  rw [e, cofP_eq_lam hp]
  ring

/-- **`eq:dDlambda`** for the edge `02`: at a planar wall point, `∂D/∂x_{02} = 2 C_{02} = 2c λ_0λ_2`
with `c = -16` (the sign of `c` is `prop:inertia`'s planar sign). -/
theorem hasDerivAt_cmDet2_x02_planar (hp : Planar p m) :
    HasDerivAt (fun s => cmDet2 (sqd p 0 1) s (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3))
      (2 * (-16) * (lam p m 0 * lam p m 2)) (sqd p 0 2) := by
  refine (hasDerivAt_cmDet2_x02 (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3)).congr_deriv ?_
  have e : cof02 (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3) = cofP p 0 2 := by simp [cofP, cofM]
  rw [e, cofP_eq_lam hp]
  ring

/-- **`eq:dDlambda`** for the edge `03`: at a planar wall point, `∂D/∂x_{03} = 2 C_{03} = 2c λ_0λ_3`
with `c = -16` (the sign of `c` is `prop:inertia`'s planar sign). -/
theorem hasDerivAt_cmDet2_x03_planar (hp : Planar p m) :
    HasDerivAt (fun s => cmDet2 (sqd p 0 1) (sqd p 0 2) s (sqd p 1 2) (sqd p 1 3) (sqd p 2 3))
      (2 * (-16) * (lam p m 0 * lam p m 3)) (sqd p 0 3) := by
  refine (hasDerivAt_cmDet2_x03 (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3)).congr_deriv ?_
  have e : cof03 (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3) = cofP p 0 3 := by simp [cofP, cofM]
  rw [e, cofP_eq_lam hp]
  ring

/-- **`eq:dDlambda`** for the edge `12`: at a planar wall point, `∂D/∂x_{12} = 2 C_{12} = 2c λ_1λ_2`
with `c = -16` (the sign of `c` is `prop:inertia`'s planar sign). -/
theorem hasDerivAt_cmDet2_x12_planar (hp : Planar p m) :
    HasDerivAt (fun s => cmDet2 (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) s (sqd p 1 3) (sqd p 2 3))
      (2 * (-16) * (lam p m 1 * lam p m 2)) (sqd p 1 2) := by
  refine (hasDerivAt_cmDet2_x12 (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3)).congr_deriv ?_
  have e : cof12 (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3) = cofP p 1 2 := by simp [cofP, cofM]
  rw [e, cofP_eq_lam hp]
  ring

/-- **`eq:dDlambda`** for the edge `13`: at a planar wall point, `∂D/∂x_{13} = 2 C_{13} = 2c λ_1λ_3`
with `c = -16` (the sign of `c` is `prop:inertia`'s planar sign). -/
theorem hasDerivAt_cmDet2_x13_planar (hp : Planar p m) :
    HasDerivAt (fun s => cmDet2 (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) s (sqd p 2 3))
      (2 * (-16) * (lam p m 1 * lam p m 3)) (sqd p 1 3) := by
  refine (hasDerivAt_cmDet2_x13 (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3)).congr_deriv ?_
  have e : cof13 (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3) = cofP p 1 3 := by simp [cofP, cofM]
  rw [e, cofP_eq_lam hp]
  ring

/-- **`eq:dDlambda`** for the edge `23`: at a planar wall point, `∂D/∂x_{23} = 2 C_{23} = 2c λ_2λ_3`
with `c = -16` (the sign of `c` is `prop:inertia`'s planar sign). -/
theorem hasDerivAt_cmDet2_x23_planar (hp : Planar p m) :
    HasDerivAt (fun s => cmDet2 (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) s)
      (2 * (-16) * (lam p m 2 * lam p m 3)) (sqd p 2 3) := by
  refine (hasDerivAt_cmDet2_x23 (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3)).congr_deriv ?_
  have e : cof23 (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3) = cofP p 2 3 := by simp [cofP, cofM]
  rw [e, cofP_eq_lam hp]
  ring

end DerivPlanar

/-- info: 'FormalResearch.EuclTet.areaVec_eq_lam_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms areaVec_eq_lam_smul

/-- info: 'FormalResearch.EuclTet.lam_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lam_sum

/-- info: 'FormalResearch.EuclTet.lam_affine_dependency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lam_affine_dependency

/-- info: 'FormalResearch.EuclTet.cmMat2_mulVec_lam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cmMat2_mulVec_lam

/-- info: 'FormalResearch.EuclTet.cofP_eq_lam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cofP_eq_lam

/-- info: 'FormalResearch.EuclTet.cofP_ne_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cofP_ne_zero_iff

/-- info: 'FormalResearch.EuclTet.hasDerivAt_cmDet2_x01_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_cmDet2_x01_planar

/-- info: 'FormalResearch.EuclTet.hasDerivAt_cmDet2_x23_planar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_cmDet2_x23_planar

/-- info: 'FormalResearch.EuclTet.radon_signs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms radon_signs

/-- info: 'FormalResearch.EuclTet.radon_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms radon_partition

/-- info: 'FormalResearch.EuclTet.radon_interior_point_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms radon_interior_point_neg

/-- info: 'FormalResearch.EuclTet.radon_interior_point_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms radon_interior_point_pos

/-- info: 'FormalResearch.EuclTet.dihedral_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dihedral_eq_zero_iff

/-- info: 'FormalResearch.EuclTet.dihedral_eq_pi_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dihedral_eq_pi_iff

/-- info: 'FormalResearch.EuclTet.nPlus_eq_four_of_22' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nPlus_eq_four_of_22

/-- info: 'FormalResearch.EuclTet.nPlus_eq_three_of_31' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nPlus_eq_three_of_31

/-- info: 'FormalResearch.EuclTet.card_flat_eq_nPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms card_flat_eq_nPlus

/-- info: 'FormalResearch.EuclTet.nFlat_eq_four_of_22' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nFlat_eq_four_of_22

/-- info: 'FormalResearch.EuclTet.nFlat_eq_three_of_31' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nFlat_eq_three_of_31

/-- info: 'FormalResearch.EuclTet.flat_edge_iff_22' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flat_edge_iff_22

/-- info: 'FormalResearch.EuclTet.flat_edge_iff_31' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms flat_edge_iff_31

end FormalResearch.EuclTet
