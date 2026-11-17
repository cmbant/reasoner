module

public import Mathlib
public import FormalResearch.EuclTet.Cofactor

/-!
# Area vectors of a tetrahedron, cofactors and dihedral angles

Sources: Weyl/P5 `cayley_menger_trichotomy.tex` `thm:sin2` (`eq:sin2`, the classical
`sin θ_{ij} = (3/2) ℓ_{ij} V/(A_k A_l)`), `eq:gramcos` and the dihedral-cosine formula; Weyl/P3
`lem:racah-cayley-menger` ("Geometric check for genuine tetrahedra").

For four points `p₀..p₃` of `ℝ³` (`EuclideanSpace ℝ (Fin 3)`) with edge vectors `a_i = p_i - p₀`, the
**area vectors** are `N₁ = ½ a₂×a₃`, `N₂ = ½ a₃×a₁`, `N₃ = ½ a₁×a₂`, `N₀ = -(N₁+N₂+N₃)`
(`= -½ (p₂-p₁)×(p₃-p₁)`).  `N_i` is normal to the face opposite `p_i`, has length the area of that
face, and (for a nondegenerate tetrahedron) all four point to the same side.

## What is formalised (exact)

* `inner_areaVec` (**the cofactor/area identity**): `⟪N_i, N_j⟫ = -C_{ij}/16` for the Cayley--Menger
  cofactors `C = cofM (‖p_i-p_j‖²)` of `FormalResearch.EuclTet.Cofactor`.
* `areaVec_sum` (`∑ N_i = 0`), `inner_areaVec_face` (`N_i ⊥ p_k - p_l` for `k,l ≠ i`),
  `inner_areaVec_side` (`⟪N_i, p_i - p_k⟫ = 6V_signed/2` for every `k ≠ i`, independent of `i`: all
  four area vectors point towards, or all away from, the opposite vertex).
* `faceArea_sq_heron`: `‖N_i‖² = T²` with `T² = heronT2` of the three edges of the face (Heron).
* `dihedral p i j = π - ∠(N_i, N_j)`: the **interior dihedral angle** between the faces opposite `p_i`
  and `p_j`, i.e. at the edge `kl` the two faces share (`{k,l}` the complement of `{i,j}`).
* `cos_dihedral` (**`cos θ_{ij} = C_{ij}/√(C_{ii}C_{jj})`**, `D > 0`): the cosine of the dihedral
  angle in terms of Cayley--Menger cofactors.  (The exterior angle has cosine
  `-C_{ij}/√(C_{ii}C_{jj})`.)
* `sin_dihedral_mul_*` (**`eq:sin2`, the classical sine formula**): `sin θ_{ij} · A_i A_j =
  (3/2) ℓ_{kl} V` with `A_i = ‖N_i‖`, `V = tetVol`, for each of the six edges `kl`.

## Not formalised

* The dihedral angle is **defined** as `π` minus the angle between the area vectors.  That this is the
  angle between the two half-planes bounded by the common edge is the classical fact supported by
  `inner_areaVec_face` and `inner_areaVec_side` (the normals are normal to their faces and point to
  the same side); no half-plane / `Affine.Simplex` dihedral notion exists in Mathlib, and none is
  introduced.
* The identification of `‖N_i‖` with a measure-theoretic area.
-/

@[expose] public section

namespace FormalResearch.EuclTet

open Matrix

/-- The cross product of two vectors of `ℝ³`. -/
noncomputable def cross3 (u v : R3) : R3 :=
  !₂[u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- The four outward-or-inward area vectors of the tetrahedron `p`: `N_i` is normal to the face
opposite `p_i`, of length the area of that face, and `∑ N_i = 0`. -/
noncomputable def areaVec (p : Fin 4 → R3) : Fin 4 → R3 :=
  let a : Fin 4 → R3 := fun i => p i - p 0
  let N1 : R3 := (1 / 2 : ℝ) • cross3 (a 2) (a 3)
  let N2 : R3 := (1 / 2 : ℝ) • cross3 (a 3) (a 1)
  let N3 : R3 := (1 / 2 : ℝ) • cross3 (a 1) (a 2)
  ![-(N1 + N2 + N3), N1, N2, N3]

theorem inner_r3 (u v : R3) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

theorem sqd_eq (p : Fin 4 → R3) (i j : Fin 4) :
    sqd p i j = (p i 0 - p j 0) ^ 2 + (p i 1 - p j 1) ^ 2 + (p i 2 - p j 2) ^ 2 := by
  simp [sqd, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]

theorem areaVec_sum (p : Fin 4 → R3) : ∑ i, areaVec p i = 0 := by
  simp [Fin.sum_univ_four, areaVec]
  abel

/-- **Cofactor / area identity**: `⟪N_i, N_j⟫ = -C_{ij}/16`. -/
theorem inner_areaVec (p : Fin 4 → R3) (i j : Fin 4) :
    inner ℝ (areaVec p i) (areaVec p j) =
      -(cofM (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3) i j) / 16 := by
  rw [inner_r3]
  simp only [sqd_eq]
  fin_cases i <;> fin_cases j <;>
  simp [areaVec, cross3, cofM, cof00, cof01, cof02, cof03, cof11, cof12, cof13, cof22, cof23,
    cof33] <;> ring

/-- `N_i` is normal to the face opposite `p_i`. -/
theorem inner_areaVec_face (p : Fin 4 → R3) (i k l : Fin 4) (hk : k ≠ i) (hl : l ≠ i) :
    inner ℝ (areaVec p i) (p k - p l) = 0 := by
  rw [inner_r3]
  fin_cases i <;> fin_cases k <;> fin_cases l <;>
  first
  | (exfalso; simp_all; done)
  | (simp [areaVec, cross3]; done)
  | (simp [areaVec, cross3]; ring)

/-- All four area vectors have the same pairing with `p_i - p_k` (`k ≠ i`): `det(a₁,a₂,a₃)/2`.
So they all point to the side of their opposite vertex (or all to the other side). -/
theorem inner_areaVec_side (p : Fin 4 → R3) (i k : Fin 4) (hk : k ≠ i) :
    inner ℝ (areaVec p i) (p i - p k) = tetDet p / 2 := by
  rw [inner_r3]
  simp only [tetDet, edgeMat, Matrix.det_fin_three]
  fin_cases i <;> fin_cases k <;>
  first
  | (exfalso; simp_all; done)
  | (simp [areaVec, cross3]; ring)

/-- The vertex-block cofactors `C_{ij}` of the tetrahedron `p`. -/
noncomputable def cofP (p : Fin 4 → R3) (i j : Fin 4) : ℝ :=
  cofM (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3) i j

theorem inner_areaVec' (p : Fin 4 → R3) (i j : Fin 4) :
    inner ℝ (areaVec p i) (areaVec p j) = -(cofP p i j) / 16 := inner_areaVec p i j

theorem norm_sq_areaVec (p : Fin 4 → R3) (i : Fin 4) :
    ‖areaVec p i‖ ^ 2 = -(cofP p i i) / 16 := by
  rw [← real_inner_self_eq_norm_sq, inner_areaVec']

theorem tetDet_ne_zero_of_cmPts_pos {p : Fin 4 → R3} (hD : 0 < cmPts p) : tetDet p ≠ 0 := by
  intro h
  have := cmPts_eq_288_tetVol_sq p
  simp [tetVol, h] at this
  linarith

theorem areaVec_ne_zero {p : Fin 4 → R3} (hD : 0 < cmPts p) (i : Fin 4) : areaVec p i ≠ 0 := by
  intro h0
  have hk : (if i = 0 then (1 : Fin 4) else 0) ≠ i := by
    fin_cases i <;> simp
  have := inner_areaVec_side p i _ hk
  rw [h0] at this
  simp at this
  exact tetDet_ne_zero_of_cmPts_pos hD (by linarith)

/-- `‖N_i‖` (the area of the face opposite `p_i`) is positive for a nondegenerate tetrahedron. -/
theorem cofP_diag_neg {p : Fin 4 → R3} (hD : 0 < cmPts p) (i : Fin 4) : cofP p i i < 0 := by
  have h := norm_sq_areaVec p i
  have hpos : 0 < ‖areaVec p i‖ := norm_pos_iff.mpr (areaVec_ne_zero hD i)
  nlinarith [sq_pos_of_pos hpos]

/-- The interior dihedral angle between the faces opposite `p_i` and `p_j` (at their common edge):
`π` minus the angle between the area vectors (which all point to the same side,
`inner_areaVec_side`, and are normal to their faces, `inner_areaVec_face`). -/
noncomputable def dihedral (p : Fin 4 → R3) (i j : Fin 4) : ℝ :=
  Real.pi - InnerProductGeometry.angle (areaVec p i) (areaVec p j)

/-- **`cos θ_{ij} = C_{ij}/√(C_{ii}C_{jj})`**: the dihedral cosine in Cayley--Menger cofactors
(`eq:gramcos`), for a nondegenerate tetrahedron (`det CM > 0`). -/
theorem cos_dihedral {p : Fin 4 → R3} (hD : 0 < cmPts p) (i j : Fin 4) :
    Real.cos (dihedral p i j) = cofP p i j / Real.sqrt (cofP p i i * cofP p j j) := by
  unfold dihedral
  rw [Real.cos_pi_sub, InnerProductGeometry.cos_angle, inner_areaVec']
  have hi := norm_sq_areaVec p i
  have hj := norm_sq_areaVec p j
  have ha : 0 < ‖areaVec p i‖ := norm_pos_iff.mpr (areaVec_ne_zero hD i)
  have hb : 0 < ‖areaVec p j‖ := norm_pos_iff.mpr (areaVec_ne_zero hD j)
  have hprod : cofP p i i * cofP p j j = (16 * ‖areaVec p i‖ * ‖areaVec p j‖) ^ 2 := by
    have e1 : cofP p i i = -16 * ‖areaVec p i‖ ^ 2 := by linarith
    have e2 : cofP p j j = -16 * ‖areaVec p j‖ ^ 2 := by linarith
    rw [e1, e2]; ring
  rw [hprod, Real.sqrt_sq (by positivity)]
  field_simp

section Sine

theorem sin_dihedral_mul_of {p : Fin 4 → R3} (hD : 0 < cmPts p) (i j : Fin 4) (X : ℝ) (hX : 0 ≤ X)
    (hJ : cofP p i i * cofP p j j - cofP p i j ^ 2 = 2 * X * cmPts p) :
    Real.sin (dihedral p i j) * (‖areaVec p i‖ * ‖areaVec p j‖) = 3 / 2 * Real.sqrt X * tetVol p := by
  unfold dihedral
  rw [Real.sin_pi_sub, InnerProductGeometry.sin_angle_mul_norm_mul_norm]
  simp only [inner_areaVec']
  have hV : 0 ≤ tetVol p := by unfold tetVol; positivity
  have h288 := cmPts_eq_288_tetVol_sq p
  have : -cofP p i i / 16 * (-cofP p j j / 16) - -cofP p i j / 16 * (-cofP p i j / 16)
      = (3 / 2 * Real.sqrt X * tetVol p) ^ 2 := by
    have hs := Real.sq_sqrt hX
    have : (3 / 2 * Real.sqrt X * tetVol p) ^ 2 = 9 / 4 * Real.sqrt X ^ 2 * tetVol p ^ 2 := by ring
    rw [this, hs]
    nlinarith [hJ, h288]
  rw [this, Real.sqrt_sq (by positivity)]

end Sine

theorem heron16_eq (α β γ : ℝ) :
    2 * (α ^ 2 * β ^ 2 + β ^ 2 * γ ^ 2 + γ ^ 2 * α ^ 2) - α ^ 4 - β ^ 4 - γ ^ 4 =
      16 * FormalResearch.Racah.P3.heronT2 α β γ := by
  unfold FormalResearch.Racah.P3.heronT2; ring

theorem sqd_eq_dist_sq (p : Fin 4 → R3) (i j : Fin 4) : sqd p i j = dist (p i) (p j) ^ 2 := by
  simp [sqd, dist_eq_norm]

theorem sqrt_sqd (p : Fin 4 → R3) (i j : Fin 4) : Real.sqrt (sqd p i j) = dist (p i) (p j) := by
  rw [sqd_eq_dist_sq, Real.sqrt_sq dist_nonneg]

/-- **Heron.**  The squared norm of the area vector of a face is `T²` (`heronT2`) of its three
edge lengths: `A_0² = T²(|p₁p₂|, |p₁p₃|, |p₂p₃|)` and the three analogues. -/
theorem faceArea_sq_heron (p : Fin 4 → R3) :
    ‖areaVec p 0‖ ^ 2 = FormalResearch.Racah.P3.heronT2 (dist (p 1) (p 2)) (dist (p 1) (p 3)) (dist (p 2) (p 3)) ∧
    ‖areaVec p 1‖ ^ 2 = FormalResearch.Racah.P3.heronT2 (dist (p 0) (p 2)) (dist (p 0) (p 3)) (dist (p 2) (p 3)) ∧
    ‖areaVec p 2‖ ^ 2 = FormalResearch.Racah.P3.heronT2 (dist (p 0) (p 1)) (dist (p 0) (p 3)) (dist (p 1) (p 3)) ∧
    ‖areaVec p 3‖ ^ 2 = FormalResearch.Racah.P3.heronT2 (dist (p 0) (p 1)) (dist (p 0) (p 2)) (dist (p 1) (p 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [norm_sq_areaVec, ← mul_right_inj' (show (16 : ℝ) ≠ 0 by norm_num), ← heron16_eq]
    simp only [cofP, cofM, cof00, cof11, cof22, cof33, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Matrix.empty_val', Matrix.cons_val_fin_one,
      sqd_eq_dist_sq]
    ring

/-- **`eq:sin2`**: `sin θ_01 · A_0 A_1 = (3/2) ℓ_23 V` (faces `0,1` share the edge `23`). -/
theorem sin_dihedral_mul_01 {p : Fin 4 → R3} (hD : 0 < cmPts p) :
    Real.sin (dihedral p 0 1) * (‖areaVec p 0‖ * ‖areaVec p 1‖) =
      3 / 2 * dist (p 2) (p 3) * tetVol p := by
  rw [← sqrt_sqd p 2 3]
  refine sin_dihedral_mul_of hD 0 1 _ (by unfold sqd; positivity) ?_
  unfold cofP cmPts
  exact cof_jacobi01 _ _ _ _ _ _

/-- **`eq:sin2`**: `sin θ_02 · A_0 A_2 = (3/2) ℓ_13 V` (faces `0,2` share the edge `13`). -/
theorem sin_dihedral_mul_02 {p : Fin 4 → R3} (hD : 0 < cmPts p) :
    Real.sin (dihedral p 0 2) * (‖areaVec p 0‖ * ‖areaVec p 2‖) =
      3 / 2 * dist (p 1) (p 3) * tetVol p := by
  rw [← sqrt_sqd p 1 3]
  refine sin_dihedral_mul_of hD 0 2 _ (by unfold sqd; positivity) ?_
  unfold cofP cmPts
  exact cof_jacobi02 _ _ _ _ _ _

/-- **`eq:sin2`**: `sin θ_03 · A_0 A_3 = (3/2) ℓ_12 V` (faces `0,3` share the edge `12`). -/
theorem sin_dihedral_mul_03 {p : Fin 4 → R3} (hD : 0 < cmPts p) :
    Real.sin (dihedral p 0 3) * (‖areaVec p 0‖ * ‖areaVec p 3‖) =
      3 / 2 * dist (p 1) (p 2) * tetVol p := by
  rw [← sqrt_sqd p 1 2]
  refine sin_dihedral_mul_of hD 0 3 _ (by unfold sqd; positivity) ?_
  unfold cofP cmPts
  exact cof_jacobi03 _ _ _ _ _ _

/-- **`eq:sin2`**: `sin θ_12 · A_1 A_2 = (3/2) ℓ_03 V` (faces `1,2` share the edge `03`). -/
theorem sin_dihedral_mul_12 {p : Fin 4 → R3} (hD : 0 < cmPts p) :
    Real.sin (dihedral p 1 2) * (‖areaVec p 1‖ * ‖areaVec p 2‖) =
      3 / 2 * dist (p 0) (p 3) * tetVol p := by
  rw [← sqrt_sqd p 0 3]
  refine sin_dihedral_mul_of hD 1 2 _ (by unfold sqd; positivity) ?_
  unfold cofP cmPts
  exact cof_jacobi12 _ _ _ _ _ _

/-- **`eq:sin2`**: `sin θ_13 · A_1 A_3 = (3/2) ℓ_02 V` (faces `1,3` share the edge `02`). -/
theorem sin_dihedral_mul_13 {p : Fin 4 → R3} (hD : 0 < cmPts p) :
    Real.sin (dihedral p 1 3) * (‖areaVec p 1‖ * ‖areaVec p 3‖) =
      3 / 2 * dist (p 0) (p 2) * tetVol p := by
  rw [← sqrt_sqd p 0 2]
  refine sin_dihedral_mul_of hD 1 3 _ (by unfold sqd; positivity) ?_
  unfold cofP cmPts
  exact cof_jacobi13 _ _ _ _ _ _

/-- **`eq:sin2`**: `sin θ_23 · A_2 A_3 = (3/2) ℓ_01 V` (faces `2,3` share the edge `01`). -/
theorem sin_dihedral_mul_23 {p : Fin 4 → R3} (hD : 0 < cmPts p) :
    Real.sin (dihedral p 2 3) * (‖areaVec p 2‖ * ‖areaVec p 3‖) =
      3 / 2 * dist (p 0) (p 1) * tetVol p := by
  rw [← sqrt_sqd p 0 1]
  refine sin_dihedral_mul_of hD 2 3 _ (by unfold sqd; positivity) ?_
  unfold cofP cmPts
  exact cof_jacobi23 _ _ _ _ _ _

/-- info: 'FormalResearch.EuclTet.areaVec_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms areaVec_sum

/-- info: 'FormalResearch.EuclTet.inner_areaVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inner_areaVec

/-- info: 'FormalResearch.EuclTet.inner_areaVec_face' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inner_areaVec_face

/-- info: 'FormalResearch.EuclTet.inner_areaVec_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inner_areaVec_side

/-- info: 'FormalResearch.EuclTet.cofP_diag_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cofP_diag_neg

/-- info: 'FormalResearch.EuclTet.cos_dihedral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cos_dihedral

/-- info: 'FormalResearch.EuclTet.faceArea_sq_heron' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms faceArea_sq_heron

/-- info: 'FormalResearch.EuclTet.sin_dihedral_mul_01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sin_dihedral_mul_01

/-- info: 'FormalResearch.EuclTet.sin_dihedral_mul_02' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sin_dihedral_mul_02

/-- info: 'FormalResearch.EuclTet.sin_dihedral_mul_03' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sin_dihedral_mul_03

/-- info: 'FormalResearch.EuclTet.sin_dihedral_mul_12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sin_dihedral_mul_12

/-- info: 'FormalResearch.EuclTet.sin_dihedral_mul_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sin_dihedral_mul_13

/-- info: 'FormalResearch.EuclTet.sin_dihedral_mul_23' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sin_dihedral_mul_23

end FormalResearch.EuclTet
