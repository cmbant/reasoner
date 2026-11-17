module

public import Mathlib
public import FormalResearch.EuclTet.Schlafli

/-!
# Consequences of Schläfli: Regge function, volume derivative, opposite-edge Van Vleck formula

Sources: Weyl/P5 `cayley_menger_trichotomy.tex`, `prop:racah-vanvleck` (`eq:opposite-edge-vanvleck`,
`eq:regge-mixed-hessian`), the Regge/Schläfli integrability in the six-edge section, and the
`∂D/∂x = 2 cof` differential of `thm:smooth` (in its volume form); Weyl/P3 `lem:racah-cayley-menger`
(volume remark).  Everything is for edge *lengths* `ℓ_e` (`x_e = ℓ_e²`); `thetaL` is `thetaX` of the
squares, `volL` the volume `V = √(D/288)`, `reggeS` the Regge generating function
`S = ∑_e ℓ_e θ_e` (interior angles).  Faces opposite `i`,`j` share the edge `kl`,
`{i,j,k,l} = {0,1,2,3}`, and the angle there is `thetaL … i j`.

## What is formalised (proved)

* `schlafli_lengths_hasDerivAt`: Schläfli `∑ ℓ_e θ_e' = 0` for paths of lengths.
* `hasDerivAt_reggeS_path` (**`dS = ∑ θ_e dℓ_e`**): the Regge function has the differential
  `∑ θ_e dℓ_e`; `regge_S_A`, `regge_S_D`: `∂S/∂A = θ_A`, `∂S/∂D = θ_D` (`A = ℓ₀₁`, `D = ℓ₂₃`).
* `hasDerivAt_volX_x01 … x23` (**volume derivative**): `∂V/∂x_{kl} = ℓ_{ij} cot θ_{ij}/12`, i.e.
  `∂V/∂ℓ_{kl} = ℓ_{kl}ℓ_{ij} cot θ_{ij}/6`, `ij` the opposite edge of `kl`.  The constant was
  checked numerically (30-digit mpmath, random tetrahedron, finite differences) before formalising;
  the Lean statement is the proof.
* `hasDerivAt_theta_opposite`, `hasDerivAt_theta_opposite_swap`, `hasDerivAt_theta_opposite_pts`
  (**`eq:opposite-edge-vanvleck`**): `∂θ_A/∂D = A·D/(6V)` for the *interior* angle `θ_A` at edge `A`
  and the opposite edge `D` (also `∂θ_D/∂A`), the other four edges fixed; the `pts` form is for a
  nondegenerate tetrahedron of `ℝ³` with `V = tetVol` and `θ_A = dihedral p 2 3`.
* `regge_mixed` (**`eq:regge-mixed-hessian`**): `S_{AD} = ∂_D(∂_A S) = A·D/(6V)`, using that
  `∂_A S = θ_A` holds on the open nondegenerate set (`eventually_nondegL_D`).

Sign convention (the P5 footnote): the paper's statement `∂Θ_A/∂D = +AD/(6V)` is for the interior
angle; it is confirmed.  With exterior angles `π - θ` all signs flip, as the footnote says.

## Not formalised

* `S_{AD}` is computed as the mixed derivative in the order `∂_D ∂_A`; the other order is the same
  statement for `θ_D` (`hasDerivAt_theta_opposite_swap`), but openness of the nondegenerate set in `A`
  was not formalised (only in `D`).
* The P5 closed form of the second-order quantities built on these (`Σ₂`, `eq:sixedge-S2-closed`) is
  not touched.
-/

@[expose] public section

namespace FormalResearch.EuclTet

open Real

/-- The interior dihedral angle between the faces opposite `i` and `j`, as a function of the six
edge lengths. -/
noncomputable def thetaL (l01 l02 l03 l12 l13 l23 : ℝ) (i j : Fin 4) : ℝ :=
  thetaX (l01 ^ 2) (l02 ^ 2) (l03 ^ 2) (l12 ^ 2) (l13 ^ 2) (l23 ^ 2) i j

/-- The Regge generating function `S = ∑_e ℓ_e θ_e` (interior angles; the edge `kl` carries the
angle between the two faces opposite `i`, `j`, `{i,j,k,l} = {0,1,2,3}`). -/
noncomputable def reggeS (l01 l02 l03 l12 l13 l23 : ℝ) : ℝ :=
  l23 * thetaL l01 l02 l03 l12 l13 l23 0 1 + l13 * thetaL l01 l02 l03 l12 l13 l23 0 2 +
  l12 * thetaL l01 l02 l03 l12 l13 l23 0 3 + l03 * thetaL l01 l02 l03 l12 l13 l23 1 2 +
  l02 * thetaL l01 l02 l03 l12 l13 l23 1 3 + l01 * thetaL l01 l02 l03 l12 l13 l23 2 3

/-- `Nondeg` for lengths: the six lengths are positive and their squares are nondegenerate edge
data. -/
structure NondegL (l01 l02 l03 l12 l13 l23 : ℝ) : Prop where
  pos01 : 0 < l01
  pos02 : 0 < l02
  pos03 : 0 < l03
  pos12 : 0 < l12
  pos13 : 0 < l13
  pos23 : 0 < l23
  nd : Nondeg (l01 ^ 2) (l02 ^ 2) (l03 ^ 2) (l12 ^ 2) (l13 ^ 2) (l23 ^ 2)

/-- **Euclidean Schläfli for paths of edge lengths.** -/
theorem schlafli_lengths_hasDerivAt {l01 l02 l03 l12 l13 l23 : ℝ → ℝ}
    {l01' l02' l03' l12' l13' l23' t0 : ℝ}
    (h01 : HasDerivAt l01 l01' t0) (h02 : HasDerivAt l02 l02' t0) (h03 : HasDerivAt l03 l03' t0)
    (h12 : HasDerivAt l12 l12' t0) (h13 : HasDerivAt l13 l13' t0) (h23 : HasDerivAt l23 l23' t0)
    (hnd : NondegL (l01 t0) (l02 t0) (l03 t0) (l12 t0) (l13 t0) (l23 t0)) :
    ∃ d01 d02 d03 d12 d13 d23 : ℝ,
      HasDerivAt (fun t => thetaL (l01 t) (l02 t) (l03 t) (l12 t) (l13 t) (l23 t) 0 1) d01 t0 ∧
      HasDerivAt (fun t => thetaL (l01 t) (l02 t) (l03 t) (l12 t) (l13 t) (l23 t) 0 2) d02 t0 ∧
      HasDerivAt (fun t => thetaL (l01 t) (l02 t) (l03 t) (l12 t) (l13 t) (l23 t) 0 3) d03 t0 ∧
      HasDerivAt (fun t => thetaL (l01 t) (l02 t) (l03 t) (l12 t) (l13 t) (l23 t) 1 2) d12 t0 ∧
      HasDerivAt (fun t => thetaL (l01 t) (l02 t) (l03 t) (l12 t) (l13 t) (l23 t) 1 3) d13 t0 ∧
      HasDerivAt (fun t => thetaL (l01 t) (l02 t) (l03 t) (l12 t) (l13 t) (l23 t) 2 3) d23 t0 ∧
      l23 t0 * d01 + l13 t0 * d02 + l12 t0 * d03 + l03 t0 * d12 + l02 t0 * d13 + l01 t0 * d23 = 0 := by
  have sq : ∀ {l : ℝ → ℝ} {l' : ℝ}, HasDerivAt l l' t0 → HasDerivAt (fun t => l t ^ 2) (2 * l t0 * l') t0 :=
    fun h => (h.pow 2).congr_deriv (by simp)
  obtain ⟨d01, d02, d03, d12, d13, d23, e01, e02, e03, e12, e13, e23, hs⟩ :=
    schlafli_hasDerivAt (sq h01) (sq h02) (sq h03) (sq h12) (sq h13) (sq h23) hnd.nd
  refine ⟨d01, d02, d03, d12, d13, d23, e01, e02, e03, e12, e13, e23, ?_⟩
  rw [Real.sqrt_sq hnd.pos01.le, Real.sqrt_sq hnd.pos02.le, Real.sqrt_sq hnd.pos03.le,
    Real.sqrt_sq hnd.pos12.le, Real.sqrt_sq hnd.pos13.le, Real.sqrt_sq hnd.pos23.le] at hs
  exact hs

theorem hasDerivAt_reggeS_path {l01 l02 l03 l12 l13 l23 : ℝ → ℝ}
    {l01' l02' l03' l12' l13' l23' t0 : ℝ}
    (h01 : HasDerivAt l01 l01' t0) (h02 : HasDerivAt l02 l02' t0) (h03 : HasDerivAt l03 l03' t0)
    (h12 : HasDerivAt l12 l12' t0) (h13 : HasDerivAt l13 l13' t0) (h23 : HasDerivAt l23 l23' t0)
    (hnd : NondegL (l01 t0) (l02 t0) (l03 t0) (l12 t0) (l13 t0) (l23 t0)) :
    HasDerivAt (fun t => reggeS (l01 t) (l02 t) (l03 t) (l12 t) (l13 t) (l23 t))
      (l23' * thetaL (l01 t0) (l02 t0) (l03 t0) (l12 t0) (l13 t0) (l23 t0) 0 1
      + l13' * thetaL (l01 t0) (l02 t0) (l03 t0) (l12 t0) (l13 t0) (l23 t0) 0 2
      + l12' * thetaL (l01 t0) (l02 t0) (l03 t0) (l12 t0) (l13 t0) (l23 t0) 0 3
      + l03' * thetaL (l01 t0) (l02 t0) (l03 t0) (l12 t0) (l13 t0) (l23 t0) 1 2
      + l02' * thetaL (l01 t0) (l02 t0) (l03 t0) (l12 t0) (l13 t0) (l23 t0) 1 3
      + l01' * thetaL (l01 t0) (l02 t0) (l03 t0) (l12 t0) (l13 t0) (l23 t0) 2 3) t0 := by
  obtain ⟨d01, d02, d03, d12, d13, d23, e01, e02, e03, e12, e13, e23, hs⟩ :=
    schlafli_lengths_hasDerivAt h01 h02 h03 h12 h13 h23 hnd
  have := (((((h23.mul e01).add (h13.mul e02)).add (h12.mul e03)).add (h03.mul e12)).add
    (h02.mul e13)).add (h01.mul e23)
  simp only [reggeS]
  refine this.congr_deriv ?_
  unfold thetaL at *
  linarith [hs]

theorem vol_deriv_aux {a b c X Dd : ℝ} (hX : 0 < X) (hD : 0 < Dd) (ha : a < 0) (hb : b < 0)
    (hJ : a * b - c ^ 2 = 2 * X * Dd) :
    2 * c / 288 / (2 * √(Dd / 288)) = √X * Real.cot (arccos (c / √(a * b))) / 12 := by
  have hab : 0 < a * b := mul_pos_of_neg_of_neg ha hb
  have hpos : 0 < a * b - c ^ 2 := by rw [hJ]; positivity
  have hs : 0 < √(a * b) := Real.sqrt_pos.mpr hab
  have hr2 : (c / √(a * b)) ^ 2 < 1 := by
    rw [div_pow, Real.sq_sqrt hab.le, div_lt_one hab]; linarith
  have hr : -1 ≤ c / √(a * b) ∧ c / √(a * b) ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (c / √(a * b) + 1), sq_nonneg (c / √(a * b) - 1)]
  rw [Real.cot_eq_cos_div_sin, Real.cos_arccos hr.1 hr.2, Real.sin_arccos]
  have h1 : 1 - (c / √(a * b)) ^ 2 = (2 * X * Dd) / (a * b) := by
    rw [div_pow, Real.sq_sqrt hab.le, ← hJ, sub_div, div_self hab.ne']
  rw [h1, Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 * X * Dd) (a * b),
    show 2 * X * Dd = X * (2 * Dd) by ring, Real.sqrt_mul hX.le,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hX' : 0 < √X := Real.sqrt_pos.mpr hX
  have hD' : 0 < √Dd := Real.sqrt_pos.mpr hD
  have h2 : 0 < √(2 : ℝ) := by positivity
  have h288 : √(Dd / 288) = √Dd / (12 * √2) := by
    rw [Real.sqrt_div hD.le, show (288 : ℝ) = 12 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  have h22 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [h288]
  field_simp
  rw [h22]
  ring

/-- **Volume derivative**: `∂V/∂x01 = ℓ_23 cot θ_{23}/12` (the opposite edge `23` and the
dihedral angle at it, between the faces opposite `0` and `1`). -/
theorem hasDerivAt_volX_x01 {x01 x02 x03 x12 x13 x23 : ℝ} (hnd : Nondeg x01 x02 x03 x12 x13 x23) :
    HasDerivAt (fun s => volX s x02 x03 x12 x13 x23)
      (√x23 * Real.cot (thetaX x01 x02 x03 x12 x13 x23 0 1) / 12) x01 := by
  have hD := hnd.det_pos
  have h := ((hasDerivAt_cmDet2_x01 x01 x02 x03 x12 x13 x23).div_const 288).sqrt (by positivity)
  unfold volX
  refine h.congr_deriv ?_
  have := vol_deriv_aux (a := cof00 x01 x02 x03 x12 x13 x23) (b := cof11 x01 x02 x03 x12 x13 x23) (c := cof01 x01 x02 x03 x12 x13 x23) hnd.x23_pos hD hnd.c00_neg hnd.c11_neg (cof_jacobi01 _ _ _ _ _ _)
  simpa [thetaX, cofM] using this

/-- **Volume derivative**: `∂V/∂x02 = ℓ_13 cot θ_{13}/12` (the opposite edge `13` and the
dihedral angle at it, between the faces opposite `0` and `2`). -/
theorem hasDerivAt_volX_x02 {x01 x02 x03 x12 x13 x23 : ℝ} (hnd : Nondeg x01 x02 x03 x12 x13 x23) :
    HasDerivAt (fun s => volX x01 s x03 x12 x13 x23)
      (√x13 * Real.cot (thetaX x01 x02 x03 x12 x13 x23 0 2) / 12) x02 := by
  have hD := hnd.det_pos
  have h := ((hasDerivAt_cmDet2_x02 x01 x02 x03 x12 x13 x23).div_const 288).sqrt (by positivity)
  unfold volX
  refine h.congr_deriv ?_
  have := vol_deriv_aux (a := cof00 x01 x02 x03 x12 x13 x23) (b := cof22 x01 x02 x03 x12 x13 x23) (c := cof02 x01 x02 x03 x12 x13 x23) hnd.x13_pos hD hnd.c00_neg hnd.c22_neg (cof_jacobi02 _ _ _ _ _ _)
  simpa [thetaX, cofM] using this

/-- **Volume derivative**: `∂V/∂x03 = ℓ_12 cot θ_{12}/12` (the opposite edge `12` and the
dihedral angle at it, between the faces opposite `0` and `3`). -/
theorem hasDerivAt_volX_x03 {x01 x02 x03 x12 x13 x23 : ℝ} (hnd : Nondeg x01 x02 x03 x12 x13 x23) :
    HasDerivAt (fun s => volX x01 x02 s x12 x13 x23)
      (√x12 * Real.cot (thetaX x01 x02 x03 x12 x13 x23 0 3) / 12) x03 := by
  have hD := hnd.det_pos
  have h := ((hasDerivAt_cmDet2_x03 x01 x02 x03 x12 x13 x23).div_const 288).sqrt (by positivity)
  unfold volX
  refine h.congr_deriv ?_
  have := vol_deriv_aux (a := cof00 x01 x02 x03 x12 x13 x23) (b := cof33 x01 x02 x03 x12 x13 x23) (c := cof03 x01 x02 x03 x12 x13 x23) hnd.x12_pos hD hnd.c00_neg hnd.c33_neg (cof_jacobi03 _ _ _ _ _ _)
  simpa [thetaX, cofM] using this

/-- **Volume derivative**: `∂V/∂x12 = ℓ_03 cot θ_{03}/12` (the opposite edge `03` and the
dihedral angle at it, between the faces opposite `1` and `2`). -/
theorem hasDerivAt_volX_x12 {x01 x02 x03 x12 x13 x23 : ℝ} (hnd : Nondeg x01 x02 x03 x12 x13 x23) :
    HasDerivAt (fun s => volX x01 x02 x03 s x13 x23)
      (√x03 * Real.cot (thetaX x01 x02 x03 x12 x13 x23 1 2) / 12) x12 := by
  have hD := hnd.det_pos
  have h := ((hasDerivAt_cmDet2_x12 x01 x02 x03 x12 x13 x23).div_const 288).sqrt (by positivity)
  unfold volX
  refine h.congr_deriv ?_
  have := vol_deriv_aux (a := cof11 x01 x02 x03 x12 x13 x23) (b := cof22 x01 x02 x03 x12 x13 x23) (c := cof12 x01 x02 x03 x12 x13 x23) hnd.x03_pos hD hnd.c11_neg hnd.c22_neg (cof_jacobi12 _ _ _ _ _ _)
  simpa [thetaX, cofM] using this

/-- **Volume derivative**: `∂V/∂x13 = ℓ_02 cot θ_{02}/12` (the opposite edge `02` and the
dihedral angle at it, between the faces opposite `1` and `3`). -/
theorem hasDerivAt_volX_x13 {x01 x02 x03 x12 x13 x23 : ℝ} (hnd : Nondeg x01 x02 x03 x12 x13 x23) :
    HasDerivAt (fun s => volX x01 x02 x03 x12 s x23)
      (√x02 * Real.cot (thetaX x01 x02 x03 x12 x13 x23 1 3) / 12) x13 := by
  have hD := hnd.det_pos
  have h := ((hasDerivAt_cmDet2_x13 x01 x02 x03 x12 x13 x23).div_const 288).sqrt (by positivity)
  unfold volX
  refine h.congr_deriv ?_
  have := vol_deriv_aux (a := cof11 x01 x02 x03 x12 x13 x23) (b := cof33 x01 x02 x03 x12 x13 x23) (c := cof13 x01 x02 x03 x12 x13 x23) hnd.x02_pos hD hnd.c11_neg hnd.c33_neg (cof_jacobi13 _ _ _ _ _ _)
  simpa [thetaX, cofM] using this

/-- **Volume derivative**: `∂V/∂x23 = ℓ_01 cot θ_{01}/12` (the opposite edge `01` and the
dihedral angle at it, between the faces opposite `2` and `3`). -/
theorem hasDerivAt_volX_x23 {x01 x02 x03 x12 x13 x23 : ℝ} (hnd : Nondeg x01 x02 x03 x12 x13 x23) :
    HasDerivAt (fun s => volX x01 x02 x03 x12 x13 s)
      (√x01 * Real.cot (thetaX x01 x02 x03 x12 x13 x23 2 3) / 12) x23 := by
  have hD := hnd.det_pos
  have h := ((hasDerivAt_cmDet2_x23 x01 x02 x03 x12 x13 x23).div_const 288).sqrt (by positivity)
  unfold volX
  refine h.congr_deriv ?_
  have := vol_deriv_aux (a := cof22 x01 x02 x03 x12 x13 x23) (b := cof33 x01 x02 x03 x12 x13 x23) (c := cof23 x01 x02 x03 x12 x13 x23) hnd.x01_pos hD hnd.c22_neg hnd.c33_neg (cof_jacobi23 _ _ _ _ _ _)
  simpa [thetaX, cofM] using this


section VanVleck

/-- Along `x₂₃` (all other squared edges fixed), `thetaX · 2 3` (the angle at the edge `01` between
the faces opposite `2` and `3`) has derivative `2 x₀₁/√(2 x₀₁ D)`. -/
theorem hasDerivAt_thetaX_x23 {x01 x02 x03 x12 x13 x23 : ℝ}
    (hnd : Nondeg x01 x02 x03 x12 x13 x23) :
    HasDerivAt (fun s => thetaX x01 x02 x03 x12 x13 s 2 3)
      (2 * x01 / √(2 * x01 * cmDet2 x01 x02 x03 x12 x13 x23)) x23 := by
  have ha : HasDerivAt (fun s => cof22 x01 x02 x03 x12 x13 s) 0 x23 := hasDerivAt_const _ _
  have hb : HasDerivAt (fun s => cof33 x01 x02 x03 x12 x13 s) 0 x23 := hasDerivAt_const _ _
  have hc : HasDerivAt (fun s => cof23 x01 x02 x03 x12 x13 s) (-2 * x01) x23 :=
    hasDerivAt_of_quad x23 (cof23 x01 x02 x03 x12 x13 x23) (-2 * x01) 0 fun s => by
      unfold cof23; ring
  have hJ := cof_jacobi23 x01 x02 x03 x12 x13 x23
  have hlt : cof23 x01 x02 x03 x12 x13 x23 ^ 2 < cof22 x01 x02 x03 x12 x13 x23 * cof33 x01 x02 x03 x12 x13 x23 := by
    have := mul_pos hnd.x01_pos hnd.det_pos; linarith
  have pd := pair_deriv ha hb hc hnd.c22_neg hnd.c33_neg hlt
  have hfun : (fun s => thetaX x01 x02 x03 x12 x13 s 2 3) =
      fun s => arccos (cof23 x01 x02 x03 x12 x13 s /
        √(cof22 x01 x02 x03 x12 x13 s * cof33 x01 x02 x03 x12 x13 s)) := by
    funext s; simp [thetaX, cofM]
  rw [hfun]
  refine pd.congr_deriv ?_
  rw [hJ]; simp

/-- The same for `x₀₁`: `thetaX · 0 1` (the angle at the edge `23`) has derivative
`2 x₂₃/√(2 x₂₃ D)`. -/
theorem hasDerivAt_thetaX_x01 {x01 x02 x03 x12 x13 x23 : ℝ}
    (hnd : Nondeg x01 x02 x03 x12 x13 x23) :
    HasDerivAt (fun s => thetaX s x02 x03 x12 x13 x23 0 1)
      (2 * x23 / √(2 * x23 * cmDet2 x01 x02 x03 x12 x13 x23)) x01 := by
  have ha : HasDerivAt (fun s => cof00 s x02 x03 x12 x13 x23) 0 x01 := hasDerivAt_const _ _
  have hb : HasDerivAt (fun s => cof11 s x02 x03 x12 x13 x23) 0 x01 := hasDerivAt_const _ _
  have hc : HasDerivAt (fun s => cof01 s x02 x03 x12 x13 x23) (-2 * x23) x01 :=
    hasDerivAt_of_quad x01 (cof01 x01 x02 x03 x12 x13 x23) (-2 * x23) 0 fun s => by
      unfold cof01; ring
  have hJ := cof_jacobi01 x01 x02 x03 x12 x13 x23
  have hlt : cof01 x01 x02 x03 x12 x13 x23 ^ 2 < cof00 x01 x02 x03 x12 x13 x23 * cof11 x01 x02 x03 x12 x13 x23 := by
    have := mul_pos hnd.x23_pos hnd.det_pos; linarith
  have pd := pair_deriv ha hb hc hnd.c00_neg hnd.c11_neg hlt
  have hfun : (fun s => thetaX s x02 x03 x12 x13 x23 0 1) =
      fun s => arccos (cof01 s x02 x03 x12 x13 x23 /
        √(cof00 s x02 x03 x12 x13 x23 * cof11 s x02 x03 x12 x13 x23)) := by
    funext s; simp [thetaX, cofM]
  rw [hfun]
  refine pd.congr_deriv ?_
  rw [hJ]; simp

/-- The tetrahedron volume `V = √(D/288)` as a function of the six edge lengths. -/
noncomputable def volL (l01 l02 l03 l12 l13 l23 : ℝ) : ℝ :=
  volX (l01 ^ 2) (l02 ^ 2) (l03 ^ 2) (l12 ^ 2) (l13 ^ 2) (l23 ^ 2)

theorem vv_alg {L M Dd : ℝ} (hL : 0 < L) (hM : 0 < M) (hD : 0 < Dd) :
    2 * L ^ 2 / √(2 * L ^ 2 * Dd) * (2 * M) = L * M / (6 * √(Dd / 288)) := by
  have hD' : 0 < √Dd := Real.sqrt_pos.mpr hD
  have h2 : 0 < √(2 : ℝ) := by positivity
  have h22 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h288 : √(Dd / 288) = √Dd / (12 * √2) := by
    rw [Real.sqrt_div hD.le, show (288 : ℝ) = 12 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  have h3 : √(2 * L ^ 2 * Dd) = L * (√2 * √Dd) := by
    rw [show 2 * L ^ 2 * Dd = L ^ 2 * (2 * Dd) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hL.le, Real.sqrt_mul (by norm_num)]
  rw [h3, h288]
  field_simp
  rw [h22]
  ring

/-- **`eq:opposite-edge-vanvleck`** (`prop:racah-vanvleck`): for the interior dihedral angle `θ_A` at
the edge `A = ℓ₀₁` of a nondegenerate tetrahedron and the *opposite* edge `D = ℓ₂₃` (all other edges
fixed), `∂θ_A/∂D = A·D/(6V)`.  Here `θ_A = thetaL … 2 3` is the angle between the faces opposite `2`
and `3` (which share the edge `01`). -/
theorem hasDerivAt_theta_opposite {A l02 l03 l12 l13 D0 : ℝ} (hnd : NondegL A l02 l03 l12 l13 D0) :
    HasDerivAt (fun D => thetaL A l02 l03 l12 l13 D 2 3) (A * D0 / (6 * volL A l02 l03 l12 l13 D0))
      D0 := by
  have h2 : HasDerivAt (fun D : ℝ => D ^ 2) (2 * D0) D0 := by simpa using hasDerivAt_pow 2 D0
  have h := HasDerivAt.comp (h := fun D : ℝ => D ^ 2) D0 (hasDerivAt_thetaX_x23 hnd.nd) h2
  unfold thetaL volL volX
  refine h.congr_deriv ?_
  have := vv_alg (L := A) (M := D0) (Dd := cmDet2 (A ^ 2) (l02 ^ 2) (l03 ^ 2) (l12 ^ 2) (l13 ^ 2) (D0 ^ 2))
    hnd.pos01 hnd.pos23 hnd.nd.det_pos
  rw [← this]

/-- The same for the other edge of the pair: `∂θ_D/∂A = A·D/(6V)`, `θ_D = thetaL … 0 1` the interior
angle at `D = ℓ₂₃`. -/
theorem hasDerivAt_theta_opposite_swap {A0 l02 l03 l12 l13 D : ℝ}
    (hnd : NondegL A0 l02 l03 l12 l13 D) :
    HasDerivAt (fun A => thetaL A l02 l03 l12 l13 D 0 1) (A0 * D / (6 * volL A0 l02 l03 l12 l13 D))
      A0 := by
  have h2 : HasDerivAt (fun D : ℝ => D ^ 2) (2 * A0) A0 := by simpa using hasDerivAt_pow 2 A0
  have h := HasDerivAt.comp (h := fun D : ℝ => D ^ 2) A0 (hasDerivAt_thetaX_x01 hnd.nd) h2
  unfold thetaL volL volX
  refine h.congr_deriv ?_
  have := vv_alg (L := D) (M := A0) (Dd := cmDet2 (A0 ^ 2) (l02 ^ 2) (l03 ^ 2) (l12 ^ 2) (l13 ^ 2) (D ^ 2))
    hnd.pos23 hnd.pos01 hnd.nd.det_pos
  rw [mul_comm A0 D, ← this]

end VanVleck

section Points

/-- A nondegenerate tetrahedron of `ℝ³` has nondegenerate edge lengths. -/
theorem nondegL_of_points {p : Fin 4 → R3} (hD : 0 < cmPts p) :
    NondegL (dist (p 0) (p 1)) (dist (p 0) (p 2)) (dist (p 0) (p 3)) (dist (p 1) (p 2))
      (dist (p 1) (p 3)) (dist (p 2) (p 3)) := by
  have h := nondeg_of_points hD
  have hp : ∀ i j : Fin 4, 0 < sqd p i j → 0 < dist (p i) (p j) := by
    intro i j hij
    rw [sqd_eq_dist_sq] at hij
    exact lt_of_le_of_ne dist_nonneg (fun h0 => by rw [← h0] at hij; simp at hij)
  refine ⟨hp 0 1 h.x01_pos, hp 0 2 h.x02_pos, hp 0 3 h.x03_pos, hp 1 2 h.x12_pos, hp 1 3 h.x13_pos,
    hp 2 3 h.x23_pos, ?_⟩
  simpa only [sqd_eq_dist_sq] using h

/-- `volL` of the six distances of four points is `tetVol`. -/
theorem volL_dist (p : Fin 4 → R3) :
    volL (dist (p 0) (p 1)) (dist (p 0) (p 2)) (dist (p 0) (p 3)) (dist (p 1) (p 2))
      (dist (p 1) (p 3)) (dist (p 2) (p 3)) = tetVol p := by
  rw [← sqrt_cmDet2_div_eq_tetVol p]
  simp only [volL, sqd_eq_dist_sq]

/-- For a nondegenerate tetrahedron of `ℝ³`, `thetaL` of its six distances is the geometric `dihedral`. -/
theorem thetaL_dist (p : Fin 4 → R3) (hD : 0 < cmPts p) (i j : Fin 4) :
    thetaL (dist (p 0) (p 1)) (dist (p 0) (p 2)) (dist (p 0) (p 3)) (dist (p 1) (p 2))
      (dist (p 1) (p 3)) (dist (p 2) (p 3)) i j = dihedral p i j := by
  rw [dihedral_eq_thetaX hD]
  simp only [thetaL, sqd_eq_dist_sq]

/-- **`eq:opposite-edge-vanvleck`, geometric form**: for a nondegenerate tetrahedron `p` of `ℝ³`, the
interior dihedral angle `θ_A = dihedral p 2 3` at the edge `A = |p₀p₁|`, as a function of the
opposite edge length `D` (the other four edge lengths fixed) has derivative `A·D/(6V)` at
`D = |p₂p₃|`, `V = tetVol p`. -/
theorem hasDerivAt_theta_opposite_pts {p : Fin 4 → R3} (hD : 0 < cmPts p) :
    HasDerivAt (fun D => thetaL (dist (p 0) (p 1)) (dist (p 0) (p 2)) (dist (p 0) (p 3))
        (dist (p 1) (p 2)) (dist (p 1) (p 3)) D 2 3)
      (dist (p 0) (p 1) * dist (p 2) (p 3) / (6 * tetVol p)) (dist (p 2) (p 3)) := by
  have h := hasDerivAt_theta_opposite (nondegL_of_points hD)
  rwa [volL_dist] at h

end Points

section Regge

/-- `∂S/∂A = θ_A` for the Regge function `S = ∑ ℓ_e θ_e` of a nondegenerate tetrahedron (`A = ℓ₀₁`,
`θ_A = thetaL … 2 3`): a consequence of the Schläfli identity. -/
theorem regge_S_A {A0 l02 l03 l12 l13 D : ℝ} (hnd : NondegL A0 l02 l03 l12 l13 D) :
    HasDerivAt (fun A => reggeS A l02 l03 l12 l13 D) (thetaL A0 l02 l03 l12 l13 D 2 3) A0 := by
  have := hasDerivAt_reggeS_path (l01 := fun A => A) (l02 := fun _ => l02) (l03 := fun _ => l03)
    (l12 := fun _ => l12) (l13 := fun _ => l13) (l23 := fun _ => D) (t0 := A0)
    (hasDerivAt_id A0) (hasDerivAt_const A0 l02) (hasDerivAt_const A0 l03)
    (hasDerivAt_const A0 l12) (hasDerivAt_const A0 l13) (hasDerivAt_const A0 D) hnd
  simpa using this

/-- `∂S/∂D = θ_D` (`D = ℓ₂₃`, `θ_D = thetaL … 0 1`). -/
theorem regge_S_D {A l02 l03 l12 l13 D0 : ℝ} (hnd : NondegL A l02 l03 l12 l13 D0) :
    HasDerivAt (fun D => reggeS A l02 l03 l12 l13 D) (thetaL A l02 l03 l12 l13 D0 0 1) D0 := by
  have := hasDerivAt_reggeS_path (l01 := fun _ => A) (l02 := fun _ => l02) (l03 := fun _ => l03)
    (l12 := fun _ => l12) (l13 := fun _ => l13) (l23 := fun D => D) (t0 := D0)
    (hasDerivAt_const D0 A) (hasDerivAt_const D0 l02) (hasDerivAt_const D0 l03)
    (hasDerivAt_const D0 l12) (hasDerivAt_const D0 l13) (hasDerivAt_id D0) hnd
  simpa using this

/-- Nondegeneracy is an open condition in the opposite edge `D = ℓ₂₃`. -/
theorem eventually_nondegL_D {A l02 l03 l12 l13 D0 : ℝ} (h : NondegL A l02 l03 l12 l13 D0) :
    ∀ᶠ D in nhds D0, NondegL A l02 l03 l12 l13 D := by
  have ev : ∀ f : ℝ → ℝ, Continuous f → 0 < f (D0 ^ 2) → ∀ᶠ D in nhds D0, 0 < f (D ^ 2) :=
    fun f hf h0 => (isOpen_lt continuous_const (hf.comp (continuous_pow 2))).mem_nhds h0
  have hn := h.nd
  have e23 : ∀ᶠ D in nhds D0, 0 < D :=
    (isOpen_lt continuous_const continuous_id).mem_nhds h.pos23
  have eq23 : ∀ᶠ D in nhds D0, 0 < D ^ 2 := ev (fun s => s) continuous_id hn.x23_pos
  have eD : ∀ᶠ D in nhds D0, 0 < cmDet2 (A ^ 2) (l02 ^ 2) (l03 ^ 2) (l12 ^ 2) (l13 ^ 2) (D ^ 2) :=
    ev (fun s => cmDet2 (A ^ 2) (l02 ^ 2) (l03 ^ 2) (l12 ^ 2) (l13 ^ 2) s)
      (continuous_iff_continuousAt.2 fun s => (hasDerivAt_cmDet2_x23 _ _ _ _ _ s).continuousAt)
      hn.det_pos
  have e0 : ∀ᶠ D in nhds D0, cof00 (A ^ 2) (l02 ^ 2) (l03 ^ 2) (l12 ^ 2) (l13 ^ 2) (D ^ 2) < 0 := by
    have := ev (fun s => -cof00 (A ^ 2) (l02 ^ 2) (l03 ^ 2) (l12 ^ 2) (l13 ^ 2) s)
      (by unfold cof00; fun_prop) (by simpa using hn.c00_neg)
    filter_upwards [this] with D hD; simpa using hD
  have e1 : ∀ᶠ D in nhds D0, cof11 (A ^ 2) (l02 ^ 2) (l03 ^ 2) (l12 ^ 2) (l13 ^ 2) (D ^ 2) < 0 := by
    have := ev (fun s => -cof11 (A ^ 2) (l02 ^ 2) (l03 ^ 2) (l12 ^ 2) (l13 ^ 2) s)
      (by unfold cof11; fun_prop) (by simpa using hn.c11_neg)
    filter_upwards [this] with D hD; simpa using hD
  filter_upwards [e23, eq23, eD, e0, e1] with D h23 hq23 hD h0 h1
  exact ⟨h.pos01, h.pos02, h.pos03, h.pos12, h.pos13, h23,
    ⟨hn.x01_pos, hn.x02_pos, hn.x03_pos, hn.x12_pos, hn.x13_pos, hq23, hD, h0, h1,
      hn.c22_neg, hn.c33_neg⟩⟩

/-- **`eq:regge-mixed-hessian`** (`prop:racah-vanvleck`): for the Regge generating function
`S(A,D) = ∑_e ℓ_e θ_e` (interior angles, the four other edges fixed): `S_A = θ_A`
(`regge_S_A`, valid on the open nondegenerate set), `S_D = θ_D` (`regge_S_D`), and the mixed
Hessian `S_{AD} = ∂_D(∂_A S) = A·D/(6V)`. -/
theorem regge_mixed {A0 l02 l03 l12 l13 D0 : ℝ} (hnd : NondegL A0 l02 l03 l12 l13 D0) :
    HasDerivAt (fun D => deriv (fun A => reggeS A l02 l03 l12 l13 D) A0)
      (A0 * D0 / (6 * volL A0 l02 l03 l12 l13 D0)) D0 := by
  have h := hasDerivAt_theta_opposite hnd
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [eventually_nondegL_D hnd] with D hD
  exact ((regge_S_A (D := D) (A0 := A0) (l02 := l02) (l03 := l03) (l12 := l12) (l13 := l13)
    (by simpa using hD)).deriv)

end Regge

/-- info: 'FormalResearch.EuclTet.schlafli_lengths_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms schlafli_lengths_hasDerivAt

/-- info: 'FormalResearch.EuclTet.hasDerivAt_reggeS_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_reggeS_path

/-- info: 'FormalResearch.EuclTet.regge_S_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms regge_S_A

/-- info: 'FormalResearch.EuclTet.regge_S_D' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms regge_S_D

/-- info: 'FormalResearch.EuclTet.regge_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms regge_mixed

/-- info: 'FormalResearch.EuclTet.hasDerivAt_theta_opposite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_theta_opposite

/-- info: 'FormalResearch.EuclTet.hasDerivAt_theta_opposite_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_theta_opposite_swap

/-- info: 'FormalResearch.EuclTet.hasDerivAt_theta_opposite_pts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_theta_opposite_pts

/-- info: 'FormalResearch.EuclTet.hasDerivAt_thetaX_x23' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_thetaX_x23

/-- info: 'FormalResearch.EuclTet.hasDerivAt_thetaX_x01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_thetaX_x01

/-- info: 'FormalResearch.EuclTet.hasDerivAt_volX_x01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_volX_x01

/-- info: 'FormalResearch.EuclTet.hasDerivAt_volX_x02' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_volX_x02

/-- info: 'FormalResearch.EuclTet.hasDerivAt_volX_x03' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_volX_x03

/-- info: 'FormalResearch.EuclTet.hasDerivAt_volX_x12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_volX_x12

/-- info: 'FormalResearch.EuclTet.hasDerivAt_volX_x13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_volX_x13

/-- info: 'FormalResearch.EuclTet.hasDerivAt_volX_x23' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_volX_x23

end FormalResearch.EuclTet
