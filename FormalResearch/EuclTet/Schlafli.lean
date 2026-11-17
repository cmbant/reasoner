module

public import Mathlib
public import FormalResearch.EuclTet.AreaVec

/-!
# Euclidean Schläfli identity from Cayley--Menger cofactors

Sources: Weyl/P5 `cayley_menger_trichotomy.tex`: "Euclidean Schläfli identity
`∑_i ℓ_i dΘ_i = 0`" (used in `sec:quarter`, `thm:quarter`, `prop:racah-vanvleck`, and as the
Regge/Schläfli integrability `∂_fΘ_e = ∂_eΘ_f` of the six-edge section); Weyl/P3
`lem:racah-cayley-menger`.  The consequences (Regge function, volume derivative, Van Vleck) are in
`FormalResearch.EuclTet.SchlafliApp`.

Setting.  `x_e = ℓ_e²` are the six squared edge lengths of the vertices `0,1,2,3`.  `Nondeg x`
says `x_e > 0`, `det CM > 0` and the four faces satisfy the strict triangle inequalities
(`C_ii < 0`); a nondegenerate tetrahedron of `ℝ³` gives such data (`nondeg_of_points`; the converse,
realisability of every such `x` in `ℝ³`, is Blumenthal's criterion `exists_points_of_blumenthal` of
`FormalResearch.EuclTet.Dichotomy`, which this module does not import and does not use).
`thetaX x i j = arccos(C_ij/√(C_ii C_jj))` is the interior dihedral angle between the faces opposite
`i` and `j`, i.e. at their common edge `kl` (`{i,j,k,l} = {0,1,2,3}`); for points of `ℝ³` it equals
`dihedral p i j` (`dihedral_eq_thetaX`).

## What is formalised (proved; no numerics)

* `pair_deriv`: derivative of one dihedral angle `arccos(c/√(ab))` along a path.
* `schlafli_alg`: the algebraic core (row sums of `C` and of `dC` vanish).
* `schlafli_hasDerivAt`, `schlafli` (**Euclidean Schläfli**): along every path of squared edges
  differentiable at `t₀` and nondegenerate at `t₀`, the six dihedral angles are differentiable and
  `∑_e ℓ_e θ_e' = 0` (`ℓ_e = √x_e`, `θ_e` the angle at `e`).  The proof uses only the
  Cayley--Menger cofactor expressions: `∑_j C_ij = 0` (`cofM_row_sum`), Jacobi's identity
  `C_iiC_jj - C_ij² = 2 x_kl D` (`cof_jacobi*`, which gives `sin θ ∝ ℓ_kl`, i.e. the factor
  `ℓ_kl = √(2D)^{-1}·√(C_iiC_jj - C_ij²)`), and `C_ii < 0`.  No volume formula or angle-sum
  identity enters.
* `nondeg_of_points`, `dihedral_eq_thetaX`, `sqrt_cmDet2_div_eq_tetVol`: link to genuine tetrahedra
  of `ℝ³` (Gram/area-vector modules).

## Not formalised

* Families of embedded point configurations are not treated separately: the statement is about edge
  lengths, which is equivalent for nondegenerate tetrahedra since the angles depend only on them
  (`dihedral_eq_thetaX`).
* Schläfli across the wall `det CM = 0` (the angles stop being differentiable there) and the
  hyperbolic/spherical Schläfli identities.
-/

@[expose] public section

namespace FormalResearch.EuclTet

open Real

section Core

/-- The derivative of one dihedral angle `arccos(c/√(ab))` along a path: with `a = C_ii`, `b = C_jj`,
`c = C_ij`, `(c' - c (a'/(2a) + b'/(2b)))` is `√(ab)·(c/√(ab))'`. -/
theorem pair_deriv {a b c : ℝ → ℝ} {a' b' c' t0 : ℝ} (ha : HasDerivAt a a' t0) (hb : HasDerivAt b b' t0)
    (hc : HasDerivAt c c' t0) (ha0 : a t0 < 0) (hb0 : b t0 < 0) (hlt : c t0 ^ 2 < a t0 * b t0) :
    HasDerivAt (fun t => arccos (c t / √(a t * b t)))
      (-(c' - c t0 * (a' / (2 * a t0) + b' / (2 * b t0))) / √(a t0 * b t0 - c t0 ^ 2)) t0 := by
  have hab : 0 < a t0 * b t0 := mul_pos_of_neg_of_neg ha0 hb0
  have hs : 0 < √(a t0 * b t0) := Real.sqrt_pos.mpr hab
  have hs' : HasDerivAt (fun t => √(a t * b t)) ((a' * b t0 + a t0 * b') / (2 * √(a t0 * b t0))) t0 :=
    (ha.mul hb).sqrt hab.ne'
  have hr : HasDerivAt (fun t => c t / √(a t * b t))
      ((c' * √(a t0 * b t0) - c t0 * ((a' * b t0 + a t0 * b') / (2 * √(a t0 * b t0)))) /
        √(a t0 * b t0) ^ 2) t0 := hc.div hs' hs.ne'
  have hr1 : c t0 / √(a t0 * b t0) ≠ -1 ∧ c t0 / √(a t0 * b t0) ≠ 1 := by
    have h2 : (c t0 / √(a t0 * b t0)) ^ 2 < 1 := by
      rw [div_pow, Real.sq_sqrt hab.le]; rw [div_lt_one hab]; exact hlt
    constructor <;> intro h <;> rw [h] at h2 <;> norm_num at h2
  have hd := (Real.hasDerivAt_arccos hr1.1 hr1.2).comp t0 hr
  refine hd.congr_deriv ?_
  have hpos : 0 < a t0 * b t0 - c t0 ^ 2 := by linarith
  have hq : √(1 - (c t0 / √(a t0 * b t0)) ^ 2) = √(a t0 * b t0 - c t0 ^ 2) / √(a t0 * b t0) := by
    rw [← Real.sqrt_div hpos.le]
    congr 1
    rw [div_pow, Real.sq_sqrt hab.le, sub_div, div_self hab.ne']
  rw [hq]
  have hsq : √(a t0 * b t0) ^ 2 = a t0 * b t0 := Real.sq_sqrt hab.le
  have hq0 : 0 < √(a t0 * b t0 - c t0 ^ 2) := Real.sqrt_pos.mpr hpos
  have ha1 : a t0 ≠ 0 := ha0.ne
  have hb1 : b t0 ≠ 0 := hb0.ne
  field_simp
  rw [hsq]

/-- The algebraic heart of Schläfli: if the rows of the symmetric matrix `(c_ij)` and of its
derivative `(c'_ij)` sum to zero, then `∑_{i<j} (c'_ij - c_ij (a'_i/(2a_i) + a'_j/(2a_j))) = 0`
(`a_i = c_ii`). -/
theorem schlafli_alg {a0 a1 a2 a3 c01 c02 c03 c12 c13 c23 a0' a1' a2' a3' c01' c02' c03' c12' c13'
    c23' : ℝ} (h0 : a0 ≠ 0) (h1 : a1 ≠ 0) (h2 : a2 ≠ 0) (h3 : a3 ≠ 0)
    (r0 : a0 + c01 + c02 + c03 = 0) (r1 : c01 + a1 + c12 + c13 = 0)
    (r2 : c02 + c12 + a2 + c23 = 0) (r3 : c03 + c13 + c23 + a3 = 0)
    (s0 : a0' + c01' + c02' + c03' = 0) (s1 : c01' + a1' + c12' + c13' = 0)
    (s2 : c02' + c12' + a2' + c23' = 0) (s3 : c03' + c13' + c23' + a3' = 0) :
    (c01' - c01 * (a0' / (2 * a0) + a1' / (2 * a1))) +
    (c02' - c02 * (a0' / (2 * a0) + a2' / (2 * a2))) +
    (c03' - c03 * (a0' / (2 * a0) + a3' / (2 * a3))) +
    (c12' - c12 * (a1' / (2 * a1) + a2' / (2 * a2))) +
    (c13' - c13 * (a1' / (2 * a1) + a3' / (2 * a3))) +
    (c23' - c23 * (a2' / (2 * a2) + a3' / (2 * a3))) = 0 := by
  have e0 : c01 + c02 + c03 = -a0 := by linarith
  have e1 : c01 + c12 + c13 = -a1 := by linarith
  have e2 : c02 + c12 + c23 = -a2 := by linarith
  have e3 : c03 + c13 + c23 = -a3 := by linarith
  have key : (c01 * (a0' / (2 * a0) + a1' / (2 * a1)) + c02 * (a0' / (2 * a0) + a2' / (2 * a2)) +
      c03 * (a0' / (2 * a0) + a3' / (2 * a3)) + c12 * (a1' / (2 * a1) + a2' / (2 * a2)) +
      c13 * (a1' / (2 * a1) + a3' / (2 * a3)) + c23 * (a2' / (2 * a2) + a3' / (2 * a3)))
      = (a0' / (2 * a0)) * (c01 + c02 + c03) + (a1' / (2 * a1)) * (c01 + c12 + c13) +
        (a2' / (2 * a2)) * (c02 + c12 + c23) + (a3' / (2 * a3)) * (c03 + c13 + c23) := by ring
  have hsum : c01' + c02' + c03' + c12' + c13' + c23' = -(a0' + a1' + a2' + a3') / 2 := by
    linarith
  rw [show (c01' - c01 * (a0' / (2 * a0) + a1' / (2 * a1))) +
    (c02' - c02 * (a0' / (2 * a0) + a2' / (2 * a2))) +
    (c03' - c03 * (a0' / (2 * a0) + a3' / (2 * a3))) +
    (c12' - c12 * (a1' / (2 * a1) + a2' / (2 * a2))) +
    (c13' - c13 * (a1' / (2 * a1) + a3' / (2 * a3))) +
    (c23' - c23 * (a2' / (2 * a2) + a3' / (2 * a3))) =
    (c01' + c02' + c03' + c12' + c13' + c23') -
    (c01 * (a0' / (2 * a0) + a1' / (2 * a1)) + c02 * (a0' / (2 * a0) + a2' / (2 * a2)) +
      c03 * (a0' / (2 * a0) + a3' / (2 * a3)) + c12 * (a1' / (2 * a1) + a2' / (2 * a2)) +
      c13 * (a1' / (2 * a1) + a3' / (2 * a3)) + c23 * (a2' / (2 * a2) + a3' / (2 * a3))) by ring,
    key, hsum, e0, e1, e2, e3]
  field_simp
  ring

end Core

section Setup

/-- Nondegenerate tetrahedral edge data: positive squared edges, `det CM > 0`, and the four faces
strict triangles (`C_ii < 0`, `-C_ii = 16 T²`). -/
structure Nondeg (x01 x02 x03 x12 x13 x23 : ℝ) : Prop where
  x01_pos : 0 < x01
  x02_pos : 0 < x02
  x03_pos : 0 < x03
  x12_pos : 0 < x12
  x13_pos : 0 < x13
  x23_pos : 0 < x23
  det_pos : 0 < cmDet2 x01 x02 x03 x12 x13 x23
  c00_neg : cof00 x01 x02 x03 x12 x13 x23 < 0
  c11_neg : cof11 x01 x02 x03 x12 x13 x23 < 0
  c22_neg : cof22 x01 x02 x03 x12 x13 x23 < 0
  c33_neg : cof33 x01 x02 x03 x12 x13 x23 < 0

/-- The interior dihedral angle between the faces opposite the vertices `i` and `j`, from the
Cayley--Menger cofactors: `arccos(C_ij/√(C_ii C_jj))`. -/
noncomputable def thetaX (x01 x02 x03 x12 x13 x23 : ℝ) (i j : Fin 4) : ℝ :=
  arccos (cofM x01 x02 x03 x12 x13 x23 i j /
    √(cofM x01 x02 x03 x12 x13 x23 i i * cofM x01 x02 x03 x12 x13 x23 j j))

/-- The tetrahedron volume as a function of the squared edges: `V = √(D/288)`. -/
noncomputable def volX (x01 x02 x03 x12 x13 x23 : ℝ) : ℝ := √(cmDet2 x01 x02 x03 x12 x13 x23 / 288)

/-- A nondegenerate tetrahedron of `ℝ³` gives nondegenerate edge data. -/
theorem nondeg_of_points {p : Fin 4 → R3} (hD : 0 < cmPts p) :
    Nondeg (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3) := by
  have hli := (cmPts_pos_iff p).mp hD
  have hinj : ∀ i j : Fin 4, i ≠ j → 0 < sqd p i j := by
    intro i j hij
    by_contra hle
    have h0 : sqd p i j = 0 := le_antisymm (not_lt.mp hle) (by unfold sqd; positivity)
    have hpe : p i = p j := by
      unfold sqd at h0
      have : ‖p i - p j‖ = 0 := by nlinarith [norm_nonneg (p i - p j)]
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    have hz := hli.ne_zero
    have hi := hli.injective
    have hinj4 : Function.Injective (fun i : Fin 4 => p i - p 0) := by
      intro i j h
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => rfl
        | succ j => exact absurd (by simpa using h.symm) (hz j)
      | succ i =>
        induction j using Fin.cases with
        | zero => exact absurd (by simpa using h) (hz i)
        | succ j => exact congrArg Fin.succ (hi (by simpa using h))
    exact hij (hinj4 (by simp [hpe]))
  refine ⟨hinj 0 1 (by decide), hinj 0 2 (by decide), hinj 0 3 (by decide), hinj 1 2 (by decide),
    hinj 1 3 (by decide), hinj 2 3 (by decide), hD, ?_, ?_, ?_, ?_⟩
  · exact cofP_diag_neg hD 0
  · exact cofP_diag_neg hD 1
  · exact cofP_diag_neg hD 2
  · exact cofP_diag_neg hD 3

/-- For a nondegenerate tetrahedron of `ℝ³`, the geometric dihedral angle `dihedral p i j` equals
the cofactor expression `thetaX`. -/
theorem dihedral_eq_thetaX {p : Fin 4 → R3} (hD : 0 < cmPts p) (i j : Fin 4) :
    dihedral p i j =
      thetaX (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3) i j := by
  have h1 : 0 ≤ dihedral p i j := by
    unfold dihedral; linarith [InnerProductGeometry.angle_le_pi (areaVec p i) (areaVec p j)]
  have h2 : dihedral p i j ≤ Real.pi := by
    unfold dihedral; linarith [InnerProductGeometry.angle_nonneg (areaVec p i) (areaVec p j)]
  have hc := cos_dihedral hD i j
  unfold thetaX
  have : cofM (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3) i j /
      √(cofM (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3) i i *
        cofM (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3) j j) =
      Real.cos (dihedral p i j) := hc.symm
  rw [this, Real.arccos_cos h1 h2]

theorem sqrt_cmDet2_div_eq_tetVol (p : Fin 4 → R3) :
    volX (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3) = tetVol p := by
  unfold volX
  have h : cmDet2 (sqd p 0 1) (sqd p 0 2) (sqd p 0 3) (sqd p 1 2) (sqd p 1 3) (sqd p 2 3) =
      288 * tetVol p ^ 2 := cmPts_eq_288_tetVol_sq p
  rw [h, show 288 * tetVol p ^ 2 / 288 = tetVol p ^ 2 by ring]
  exact Real.sqrt_sq (by unfold tetVol; positivity)

end Setup

section Schlafli

theorem w_mul {a b c a' b' c' X Dd : ℝ} (hX : 0 < X) (hD : 0 < Dd) (hJ : a * b - c ^ 2 = 2 * X * Dd) :
    √X * (-(c' - c * (a' / (2 * a) + b' / (2 * b))) / √(a * b - c ^ 2)) =
      -(1 / √(2 * Dd)) * (c' - c * (a' / (2 * a) + b' / (2 * b))) := by
  rw [hJ, show 2 * X * Dd = X * (2 * Dd) by ring, Real.sqrt_mul hX.le]
  have h1 : 0 < √X := Real.sqrt_pos.mpr hX
  have h2 : 0 < √(2 * Dd) := Real.sqrt_pos.mpr (by positivity)
  field_simp

theorem cofM_symm (x01 x02 x03 x12 x13 x23 : ℝ) (i j : Fin 4) :
    cofM x01 x02 x03 x12 x13 x23 i j = cofM x01 x02 x03 x12 x13 x23 j i := by
  fin_cases i <;> fin_cases j <;> simp [cofM]

end Schlafli

theorem cofM_differentiableAt {x01 x02 x03 x12 x13 x23 : ℝ → ℝ} {t0 : ℝ}
    (d01 : DifferentiableAt ℝ x01 t0) (d02 : DifferentiableAt ℝ x02 t0)
    (d03 : DifferentiableAt ℝ x03 t0) (d12 : DifferentiableAt ℝ x12 t0)
    (d13 : DifferentiableAt ℝ x13 t0) (d23 : DifferentiableAt ℝ x23 t0) (i j : Fin 4) :
    DifferentiableAt ℝ (fun t => cofM (x01 t) (x02 t) (x03 t) (x12 t) (x13 t) (x23 t) i j) t0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [cofM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Matrix.empty_val', Matrix.cons_val_fin_one, Fin.mk_zero,
      Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;>
    simp only [cof00, cof01, cof02, cof03, cof11, cof12, cof13, cof22, cof23, cof33] <;>
    fun_prop

section Main

/-- **Euclidean Schläfli identity**, `∑_e ℓ_e dθ_e = 0`.  For any six squared edge lengths
`x_e(t)` differentiable at `t₀` and nondegenerate at `t₀`, with `ℓ_e = √x_e` and `θ_e` the interior
dihedral angle at `e` (`thetaX … i j` is the angle at the edge `kl` complementary to `ij`), the six
dihedral angles are differentiable at `t₀` and
`ℓ_{23} θ'_{01} + ℓ_{13} θ'_{02} + ℓ_{12} θ'_{03} + ℓ_{03} θ'_{12} + ℓ_{02} θ'_{13} + ℓ_{01} θ'_{23} = 0`. -/
theorem schlafli_hasDerivAt {x01 x02 x03 x12 x13 x23 : ℝ → ℝ}
    {x01' x02' x03' x12' x13' x23' t0 : ℝ}
    (h01 : HasDerivAt x01 x01' t0) (h02 : HasDerivAt x02 x02' t0) (h03 : HasDerivAt x03 x03' t0)
    (h12 : HasDerivAt x12 x12' t0) (h13 : HasDerivAt x13 x13' t0) (h23 : HasDerivAt x23 x23' t0)
    (hnd : Nondeg (x01 t0) (x02 t0) (x03 t0) (x12 t0) (x13 t0) (x23 t0)) :
    ∃ d01 d02 d03 d12 d13 d23 : ℝ,
      HasDerivAt (fun t => thetaX (x01 t) (x02 t) (x03 t) (x12 t) (x13 t) (x23 t) 0 1) d01 t0 ∧
      HasDerivAt (fun t => thetaX (x01 t) (x02 t) (x03 t) (x12 t) (x13 t) (x23 t) 0 2) d02 t0 ∧
      HasDerivAt (fun t => thetaX (x01 t) (x02 t) (x03 t) (x12 t) (x13 t) (x23 t) 0 3) d03 t0 ∧
      HasDerivAt (fun t => thetaX (x01 t) (x02 t) (x03 t) (x12 t) (x13 t) (x23 t) 1 2) d12 t0 ∧
      HasDerivAt (fun t => thetaX (x01 t) (x02 t) (x03 t) (x12 t) (x13 t) (x23 t) 1 3) d13 t0 ∧
      HasDerivAt (fun t => thetaX (x01 t) (x02 t) (x03 t) (x12 t) (x13 t) (x23 t) 2 3) d23 t0 ∧
      √(x23 t0) * d01 + √(x13 t0) * d02 + √(x12 t0) * d03 + √(x03 t0) * d12 + √(x02 t0) * d13
        + √(x01 t0) * d23 = 0 := by
  have d01 := h01.differentiableAt
  have d02 := h02.differentiableAt
  have d03 := h03.differentiableAt
  have d12 := h12.differentiableAt
  have d13 := h13.differentiableAt
  have d23 := h23.differentiableAt
  -- the cofactor functions along the path
  obtain ⟨c, hcdef⟩ : ∃ c : Fin 4 → Fin 4 → ℝ → ℝ,
      c = fun i j t => cofM (x01 t) (x02 t) (x03 t) (x12 t) (x13 t) (x23 t) i j := ⟨_, rfl⟩
  have hcval : ∀ i j t, c i j t = cofM (x01 t) (x02 t) (x03 t) (x12 t) (x13 t) (x23 t) i j := by
    intro i j t; rw [hcdef]
  have hcfun : ∀ i j, c i j = fun t => cofM (x01 t) (x02 t) (x03 t) (x12 t) (x13 t) (x23 t) i j := by
    intro i j; rw [hcdef]
  have hdiff : ∀ i j, DifferentiableAt ℝ (c i j) t0 := fun i j => by
    rw [hcfun]; exact cofM_differentiableAt d01 d02 d03 d12 d13 d23 i j
  have hc : ∀ i j, HasDerivAt (c i j) (deriv (c i j) t0) t0 := fun i j => (hdiff i j).hasDerivAt
  have hsymm : ∀ i j, c i j = c j i := fun i j =>
    funext fun t => by rw [hcval, hcval]; exact cofM_symm _ _ _ _ _ _ i j
  have hrow : ∀ i, ∑ j, deriv (c i j) t0 = 0 := by
    intro i
    have h1 := HasDerivAt.sum (u := Finset.univ) (fun j _ => hc i j)
    have h2 : (∑ j ∈ Finset.univ, c i j) = fun _ => (0 : ℝ) := by
      funext y; rw [Finset.sum_apply]; simp_rw [hcval]; exact cofM_row_sum _ _ _ _ _ _ i
    rw [h2] at h1
    exact ((hasDerivAt_const t0 (0 : ℝ)).unique h1).symm
  have hrow0 : ∀ i, ∑ j, c i j t0 = 0 := fun i => by simp_rw [hcval]; exact cofM_row_sum _ _ _ _ _ _ i
  obtain ⟨hx01, hx02, hx03, hx12, hx13, hx23, hD, hn0, hn1, hn2, hn3⟩ := hnd
  have a0 : c 0 0 t0 < 0 := by rw [hcval]; simpa [cofM] using hn0
  have a1 : c 1 1 t0 < 0 := by rw [hcval]; simpa [cofM] using hn1
  have a2 : c 2 2 t0 < 0 := by rw [hcval]; simpa [cofM] using hn2
  have a3 : c 3 3 t0 < 0 := by rw [hcval]; simpa [cofM] using hn3
  -- Jacobi identities at `t₀`
  have j01 := cof_jacobi01 (x01 t0) (x02 t0) (x03 t0) (x12 t0) (x13 t0) (x23 t0)
  have j02 := cof_jacobi02 (x01 t0) (x02 t0) (x03 t0) (x12 t0) (x13 t0) (x23 t0)
  have j03 := cof_jacobi03 (x01 t0) (x02 t0) (x03 t0) (x12 t0) (x13 t0) (x23 t0)
  have j12 := cof_jacobi12 (x01 t0) (x02 t0) (x03 t0) (x12 t0) (x13 t0) (x23 t0)
  have j13 := cof_jacobi13 (x01 t0) (x02 t0) (x03 t0) (x12 t0) (x13 t0) (x23 t0)
  have j23 := cof_jacobi23 (x01 t0) (x02 t0) (x03 t0) (x12 t0) (x13 t0) (x23 t0)
  have J01 : c 0 0 t0 * c 1 1 t0 - c 0 1 t0 ^ 2 = 2 * x23 t0 * cmDet2 (x01 t0) (x02 t0) (x03 t0) (x12 t0) (x13 t0) (x23 t0) := by
    rw [hcval, hcval, hcval]; simpa [cofM] using j01
  have J02 : c 0 0 t0 * c 2 2 t0 - c 0 2 t0 ^ 2 = 2 * x13 t0 * cmDet2 (x01 t0) (x02 t0) (x03 t0) (x12 t0) (x13 t0) (x23 t0) := by
    rw [hcval, hcval, hcval]; simpa [cofM] using j02
  have J03 : c 0 0 t0 * c 3 3 t0 - c 0 3 t0 ^ 2 = 2 * x12 t0 * cmDet2 (x01 t0) (x02 t0) (x03 t0) (x12 t0) (x13 t0) (x23 t0) := by
    rw [hcval, hcval, hcval]; simpa [cofM] using j03
  have J12 : c 1 1 t0 * c 2 2 t0 - c 1 2 t0 ^ 2 = 2 * x03 t0 * cmDet2 (x01 t0) (x02 t0) (x03 t0) (x12 t0) (x13 t0) (x23 t0) := by
    rw [hcval, hcval, hcval]; simpa [cofM] using j12
  have J13 : c 1 1 t0 * c 3 3 t0 - c 1 3 t0 ^ 2 = 2 * x02 t0 * cmDet2 (x01 t0) (x02 t0) (x03 t0) (x12 t0) (x13 t0) (x23 t0) := by
    rw [hcval, hcval, hcval]; simpa [cofM] using j13
  have J23 : c 2 2 t0 * c 3 3 t0 - c 2 3 t0 ^ 2 = 2 * x01 t0 * cmDet2 (x01 t0) (x02 t0) (x03 t0) (x12 t0) (x13 t0) (x23 t0) := by
    rw [hcval, hcval, hcval]; simpa [cofM] using j23
  set Dd := cmDet2 (x01 t0) (x02 t0) (x03 t0) (x12 t0) (x13 t0) (x23 t0) with hDd
  have lt01 : c 0 1 t0 ^ 2 < c 0 0 t0 * c 1 1 t0 := by have := mul_pos hx23 hD; linarith [J01]
  have lt02 : c 0 2 t0 ^ 2 < c 0 0 t0 * c 2 2 t0 := by have := mul_pos hx13 hD; linarith [J02]
  have lt03 : c 0 3 t0 ^ 2 < c 0 0 t0 * c 3 3 t0 := by have := mul_pos hx12 hD; linarith [J03]
  have lt12 : c 1 2 t0 ^ 2 < c 1 1 t0 * c 2 2 t0 := by have := mul_pos hx03 hD; linarith [J12]
  have lt13 : c 1 3 t0 ^ 2 < c 1 1 t0 * c 3 3 t0 := by have := mul_pos hx02 hD; linarith [J13]
  have lt23 : c 2 3 t0 ^ 2 < c 2 2 t0 * c 3 3 t0 := by have := mul_pos hx01 hD; linarith [J23]
  have p01 := pair_deriv (hc 0 0) (hc 1 1) (hc 0 1) a0 a1 lt01
  have p02 := pair_deriv (hc 0 0) (hc 2 2) (hc 0 2) a0 a2 lt02
  have p03 := pair_deriv (hc 0 0) (hc 3 3) (hc 0 3) a0 a3 lt03
  have p12 := pair_deriv (hc 1 1) (hc 2 2) (hc 1 2) a1 a2 lt12
  have p13 := pair_deriv (hc 1 1) (hc 3 3) (hc 1 3) a1 a3 lt13
  have p23 := pair_deriv (hc 2 2) (hc 3 3) (hc 2 3) a2 a3 lt23
  have hDd0 : 0 < Dd := hD
  have hth : ∀ i j, (fun t => thetaX (x01 t) (x02 t) (x03 t) (x12 t) (x13 t) (x23 t) i j) =
      fun t => arccos (c i j t / √(c i i t * c j j t)) := by
    intro i j; funext t; simp only [thetaX, hcval]
  refine ⟨_, _, _, _, _, _, by rw [hth]; exact p01, by rw [hth]; exact p02, by rw [hth]; exact p03,
    by rw [hth]; exact p12, by rw [hth]; exact p13, by rw [hth]; exact p23, ?_⟩
  rw [w_mul hx23 hDd0 J01, w_mul hx13 hDd0 J02, w_mul hx12 hDd0 J03,
      w_mul hx03 hDd0 J12, w_mul hx02 hDd0 J13, w_mul hx01 hDd0 J23]
  -- row sums (value and derivative), written out
  have r : ∀ i, c i 0 t0 + c i 1 t0 + c i 2 t0 + c i 3 t0 = 0 := by
    intro i; have := hrow0 i; simpa [Fin.sum_univ_four] using this
  have s : ∀ i, deriv (c i 0) t0 + deriv (c i 1) t0 + deriv (c i 2) t0 + deriv (c i 3) t0 = 0 := by
    intro i; have := hrow i; simpa [Fin.sum_univ_four] using this
  have alg := schlafli_alg (a0 := c 0 0 t0) (a1 := c 1 1 t0) (a2 := c 2 2 t0) (a3 := c 3 3 t0)
    (c01 := c 0 1 t0) (c02 := c 0 2 t0) (c03 := c 0 3 t0) (c12 := c 1 2 t0) (c13 := c 1 3 t0)
    (c23 := c 2 3 t0) (a0' := deriv (c 0 0) t0) (a1' := deriv (c 1 1) t0) (a2' := deriv (c 2 2) t0)
    (a3' := deriv (c 3 3) t0) (c01' := deriv (c 0 1) t0) (c02' := deriv (c 0 2) t0)
    (c03' := deriv (c 0 3) t0) (c12' := deriv (c 1 2) t0) (c13' := deriv (c 1 3) t0)
    (c23' := deriv (c 2 3) t0) a0.ne a1.ne a2.ne a3.ne
    (by simpa using r 0) (by have := r 1; rw [hsymm 1 0] at this; simpa using this)
    (by have := r 2; rw [hsymm 2 0, hsymm 2 1] at this; simpa using this)
    (by have := r 3; rw [hsymm 3 0, hsymm 3 1, hsymm 3 2] at this; simpa using this)
    (by simpa using s 0) (by have := s 1; rw [hsymm 1 0] at this; simpa using this)
    (by have := s 2; rw [hsymm 2 0, hsymm 2 1] at this; simpa using this)
    (by have := s 3; rw [hsymm 3 0, hsymm 3 1, hsymm 3 2] at this; simpa using this)
  linear_combination (-(1 / √(2 * Dd))) * alg

/-- **Euclidean Schläfli identity** in the `deriv` form: `∑_e ℓ_e (θ_e)' = 0`. -/
theorem schlafli {x01 x02 x03 x12 x13 x23 : ℝ → ℝ} {x01' x02' x03' x12' x13' x23' t0 : ℝ}
    (h01 : HasDerivAt x01 x01' t0) (h02 : HasDerivAt x02 x02' t0) (h03 : HasDerivAt x03 x03' t0)
    (h12 : HasDerivAt x12 x12' t0) (h13 : HasDerivAt x13 x13' t0) (h23 : HasDerivAt x23 x23' t0)
    (hnd : Nondeg (x01 t0) (x02 t0) (x03 t0) (x12 t0) (x13 t0) (x23 t0)) :
    √(x23 t0) * deriv (fun t => thetaX (x01 t) (x02 t) (x03 t) (x12 t) (x13 t) (x23 t) 0 1) t0
    + √(x13 t0) * deriv (fun t => thetaX (x01 t) (x02 t) (x03 t) (x12 t) (x13 t) (x23 t) 0 2) t0
    + √(x12 t0) * deriv (fun t => thetaX (x01 t) (x02 t) (x03 t) (x12 t) (x13 t) (x23 t) 0 3) t0
    + √(x03 t0) * deriv (fun t => thetaX (x01 t) (x02 t) (x03 t) (x12 t) (x13 t) (x23 t) 1 2) t0
    + √(x02 t0) * deriv (fun t => thetaX (x01 t) (x02 t) (x03 t) (x12 t) (x13 t) (x23 t) 1 3) t0
    + √(x01 t0) * deriv (fun t => thetaX (x01 t) (x02 t) (x03 t) (x12 t) (x13 t) (x23 t) 2 3) t0
      = 0 := by
  obtain ⟨d01, d02, d03, d12, d13, d23, e01, e02, e03, e12, e13, e23, hs⟩ :=
    schlafli_hasDerivAt h01 h02 h03 h12 h13 h23 hnd
  rw [e01.deriv, e02.deriv, e03.deriv, e12.deriv, e13.deriv, e23.deriv]
  exact hs

end Main

/-- info: 'FormalResearch.EuclTet.schlafli_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms schlafli_hasDerivAt

/-- info: 'FormalResearch.EuclTet.schlafli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms schlafli

/-- info: 'FormalResearch.EuclTet.dihedral_eq_thetaX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dihedral_eq_thetaX

/-- info: 'FormalResearch.EuclTet.nondeg_of_points' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nondeg_of_points

end FormalResearch.EuclTet
