module

public import Mathlib
public import FormalResearch.EuclTet.Schlafli

/-!
# Consequences of Schläfli: Regge generating function, volume derivative, opposite-edge Van Vleck

(See the docstring of `FormalResearch.EuclTet.Schlafli` for sources.)  Everything here is stated for
paths of edge *lengths* `ℓ_e(t)` (squared edges `ℓ_e²`).
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


end FormalResearch.EuclTet
