import FormalResearch.FourQubitEntropy.RenyiFullTangent
import FormalResearch.FourQubitEntropy.RenyiFullHsTilt

/-!
# `lem:fqe-hs-polynomial`: the one-variable supporting inequality

Paper E, `renyi_hs_analytic.tex`.  Parametrise the one-large spectrum
`((1+3s)/4, (1-s)/4, (1-s)/4, (1-s)/4)` by `x = ((1+3s)/(1-s))^{1/5}`, i.e. by
`(x⁵/N, 1/N, 1/N, 1/N)`, `N = x⁵ + 3`; then `p, t` are rational in `x` and `H_{8/5} = (8/3 ln N - 5/3 ln(x⁸+3))/ln 2`.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open Set

noncomputable def pX (x : ℝ) : ℝ := (x ^ 10 + 3) / (x ^ 5 + 3) ^ 2
noncomputable def tX (x : ℝ) : ℝ := (x ^ 15 + 3) / (x ^ 5 + 3) ^ 3
noncomputable def HX (x : ℝ) : ℝ :=
  ((8 / 3) * Real.log (x ^ 5 + 3) - (5 / 3) * Real.log (x ^ 8 + 3)) / Real.log 2
noncomputable def PhiX (α x : ℝ) : ℝ :=
  HX x + α * (pX x - 1 / 3) + (1 / 12) * (17 * pX x - 12 * tX x - 4) - (10 / 3) * (pX x ^ 2 - 1 / 9)
noncomputable def MX (x : ℝ) : ℝ :=
  (x ^ 2 + x + 1) * (x ^ 5 + 3) ^ 2 / ((x ^ 4 + x ^ 3 + x ^ 2 + x + 1) * (x ^ 8 + 3))
noncomputable def EX (α x : ℝ) : ℝ :=
  -(4 / (3 * Real.log 2)) * MX x - (3 / 2) * (x ^ 5 + 1) / (x ^ 5 + 3) + (α + 17 / 12)
    - (20 / 3) * pX x
noncomputable def BX (x : ℝ) : ℝ := 5 * x ^ 4 * (43 * x ^ 5 - 31) / (x ^ 5 + 3) ^ 3
noncomputable def pdX (x : ℝ) : ℝ := 30 * x ^ 4 * (x ^ 5 - 1) / (x ^ 5 + 3) ^ 3
noncomputable def P13 (x : ℝ) : ℝ :=
  3 * x ^ 13 + 6 * x ^ 12 - 26 * x ^ 11 - 58 * x ^ 10 - 90 * x ^ 9 - 57 * x ^ 8 - 24 * x ^ 7 +
    24 * x ^ 6 + 57 * x ^ 5 + 90 * x ^ 4 + 42 * x ^ 3 - 6 * x ^ 2 - 54 * x - 27
noncomputable def JX (x : ℝ) : ℝ :=
  -4 * (x ^ 5 + 3) ^ 4 * P13 x /
    (15 * x ^ 2 * (43 * x ^ 5 - 31) * (x ^ 8 + 3) ^ 2 * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) ^ 2)

theorem N_pos {x : ℝ} (hx : 0 ≤ x) : 0 < x ^ 5 + 3 := by positivity
theorem G_pos {x : ℝ} (hx : 0 ≤ x) : 0 < x ^ 8 + 3 := by positivity
theorem h4_pos {x : ℝ} (hx : 0 ≤ x) : 0 < x ^ 4 + x ^ 3 + x ^ 2 + x + 1 := by positivity
theorem c43_pos {x : ℝ} (hx : 1 ≤ x) : 0 < 43 * x ^ 5 - 31 := by
  have : 1 ≤ x ^ 5 := one_le_pow₀ hx
  linarith

theorem pX_deriv {x : ℝ} (hx : 0 ≤ x) : HasDerivAt pX (pdX x) x := by
  have hN := (N_pos hx).ne'
  have h1 : HasDerivAt (fun x : ℝ => x ^ 10 + 3) (10 * x ^ 9) x := by
    simpa using (hasDerivAt_pow 10 x).add_const 3
  have h2 : HasDerivAt (fun x : ℝ => (x ^ 5 + 3) ^ 2) (2 * (x ^ 5 + 3) * (5 * x ^ 4)) x := by
    have := ((hasDerivAt_pow 5 x).add_const 3).pow 2
    convert this using 1 <;> simp
  have := h1.div h2 (by positivity)
  unfold pX pdX
  convert this using 1
  field_simp
  ring

theorem tX_deriv {x : ℝ} (hx : 0 ≤ x) : HasDerivAt tX (45 * x ^ 4 * (x ^ 10 - 1) / (x ^ 5 + 3) ^ 4) x := by
  have hN := (N_pos hx).ne'
  have h1 : HasDerivAt (fun x : ℝ => x ^ 15 + 3) (15 * x ^ 14) x := by
    simpa using (hasDerivAt_pow 15 x).add_const 3
  have h2 : HasDerivAt (fun x : ℝ => (x ^ 5 + 3) ^ 3) (3 * (x ^ 5 + 3) ^ 2 * (5 * x ^ 4)) x := by
    have := ((hasDerivAt_pow 5 x).add_const 3).pow 3
    convert this using 1 <;> simp
  have := h1.div h2 (by positivity)
  unfold tX
  convert this using 1
  field_simp
  ring

theorem HX_deriv {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt HX (-(40 * x ^ 4 * (x ^ 3 - 1)) / (Real.log 2 * (x ^ 5 + 3) * (x ^ 8 + 3))) x := by
  have hN := (N_pos hx).ne'
  have hG := (G_pos hx).ne'
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h1 : HasDerivAt (fun x : ℝ => x ^ 5 + 3) (5 * x ^ 4) x := by
    simpa using (hasDerivAt_pow 5 x).add_const 3
  have h2 : HasDerivAt (fun x : ℝ => x ^ 8 + 3) (8 * x ^ 7) x := by
    simpa using (hasDerivAt_pow 8 x).add_const 3
  have h3 := (((h1.log hN).const_mul (8 / 3)).sub ((h2.log hG).const_mul (5 / 3))).div_const
    (Real.log 2)
  unfold HX
  convert h3 using 1
  field_simp
  ring

theorem PhiX_deriv (α : ℝ) {x : ℝ} (hx : 0 ≤ x) : HasDerivAt (PhiX α) (EX α x * pdX x) x := by
  have hN := (N_pos hx).ne'
  have hG := (G_pos hx).ne'
  have hh := (h4_pos hx).ne'
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hp := pX_deriv hx
  have ht := tX_deriv hx
  have hH := HX_deriv hx
  have := (((hH.add (hp.sub_const (1 / 3 : ℝ) |>.const_mul α)).add
    (((hp.const_mul 17).sub (ht.const_mul 12)).sub_const 4 |>.const_mul (1 / 12))).sub
    (((hp.pow 2).sub_const (1 / 9 : ℝ)).const_mul (10 / 3)))
  unfold PhiX
  convert this using 1
  norm_num
  unfold EX MX pX pdX
  field_simp
  ring

theorem MX_deriv {x : ℝ} (hx : 0 ≤ x) : HasDerivAt MX (x ^ 2 * (x ^ 5 + 3) * P13 x /
    ((x ^ 8 + 3) ^ 2 * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) ^ 2)) x := by
  have hx0 : 0 ≤ x := hx
  have hN := (N_pos hx0).ne'
  have hG := (G_pos hx0).ne'
  have hh := (h4_pos hx0).ne'
  have hn : HasDerivAt (fun x : ℝ => (x ^ 2 + x + 1) * (x ^ 5 + 3) ^ 2)
      ((2 * x + 1) * (x ^ 5 + 3) ^ 2 + (x ^ 2 + x + 1) * (2 * (x ^ 5 + 3) * (5 * x ^ 4))) x := by
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2 + x + 1) (2 * x + 1) x := by
      simpa using ((hasDerivAt_pow 2 x).add (hasDerivAt_id x)).add_const 1
    have h2 : HasDerivAt (fun x : ℝ => (x ^ 5 + 3) ^ 2) (2 * (x ^ 5 + 3) * (5 * x ^ 4)) x := by
      have := ((hasDerivAt_pow 5 x).add_const 3).pow 2
      convert this using 1 <;> simp
    exact h1.mul h2
  have hd : HasDerivAt (fun x : ℝ => (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) * (x ^ 8 + 3))
      ((4 * x ^ 3 + 3 * x ^ 2 + 2 * x + 1) * (x ^ 8 + 3) +
        (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) * (8 * x ^ 7)) x := by
    have h1 : HasDerivAt (fun x : ℝ => x ^ 4 + x ^ 3 + x ^ 2 + x + 1)
        (4 * x ^ 3 + 3 * x ^ 2 + 2 * x + 1) x := by
      simpa using ((((hasDerivAt_pow 4 x).add (hasDerivAt_pow 3 x)).add (hasDerivAt_pow 2 x)).add
        (hasDerivAt_id x)).add_const 1
    have h2 : HasDerivAt (fun x : ℝ => x ^ 8 + 3) (8 * x ^ 7) x := by
      simpa using (hasDerivAt_pow 8 x).add_const 3
    exact h1.mul h2
  have := hn.div hd (by positivity)
  unfold MX P13
  convert this using 1
  field_simp
  ring

theorem BX_mul_JX {x : ℝ} (hx : 1 ≤ x) :
    BX x * JX x = -(4 / 3) * (x ^ 2 * (x ^ 5 + 3) * P13 x /
      ((x ^ 8 + 3) ^ 2 * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) ^ 2)) := by
  have hx0 : 0 ≤ x := by linarith
  have hN := (N_pos hx0).ne'
  have hG := (G_pos hx0).ne'
  have hh := (h4_pos hx0).ne'
  have hc := (c43_pos hx).ne'
  have hx1 : x ≠ 0 := by positivity
  unfold BX JX
  generalize 43 * x ^ 5 - 31 = c at hc ⊢
  field_simp
  ring

theorem EX_deriv (α : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    HasDerivAt (EX α) (BX x * JX x / Real.log 2 - BX x) x := by
  have hx0 : 0 ≤ x := by linarith
  have hN := (N_pos hx0).ne'
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hM := MX_deriv hx0
  have hp := pX_deriv hx0
  have hr : HasDerivAt (fun x : ℝ => (x ^ 5 + 1) / (x ^ 5 + 3)) (10 * x ^ 4 / (x ^ 5 + 3) ^ 2) x := by
    have h1 : HasDerivAt (fun x : ℝ => x ^ 5 + 1) (5 * x ^ 4) x := by
      simpa using (hasDerivAt_pow 5 x).add_const 1
    have h2 : HasDerivAt (fun x : ℝ => x ^ 5 + 3) (5 * x ^ 4) x := by
      simpa using (hasDerivAt_pow 5 x).add_const 3
    have := h1.div h2 hN
    convert this using 1
    field_simp
    ring
  have := ((((hM.const_mul (-(4 / (3 * Real.log 2)))).sub (hr.const_mul (3 / 2))).add_const
    (α + 17 / 12)).sub (hp.const_mul (20 / 3)))
  unfold EX
  convert this using 1
  · funext y
    simp only [Pi.sub_apply]
    ring
  · have e := BX_mul_JX hx
    rw [e]
    unfold BX pdX
    field_simp
    ring

/-- The curvature polynomial `Q` of `(HCJ)`, in the paper's coordinates `y = x-1`, `R = x⁵-1`. -/
noncomputable def Qpol (x : ℝ) : ℝ :=
  (225600 + 457600 * (x - 1) + 471040 * (x - 1) ^ 2 + 240000 * (x - 1) ^ 3 + 48640 * (x - 1) ^ 4)
  + (x ^ 5 - 1) * (582160 + 1108000 * (x - 1) + 1118304 * (x - 1) ^ 2 + 557584 * (x - 1) ^ 3 +
      110864 * (x - 1) ^ 4)
  + (x ^ 5 - 1) ^ 2 * (690608 + 1195520 * (x - 1) + 1018512 * (x - 1) ^ 2 + 418768 * (x - 1) ^ 3 +
      68128 * (x - 1) ^ 4)
  + (x ^ 5 - 1) ^ 3 * (756896 + 1304520 * (x - 1) + 1151162 * (x - 1) ^ 2 + 522393 * (x - 1) ^ 3 +
      96703 * (x - 1) ^ 4)
  + (x ^ 5 - 1) ^ 4 * (516296 + 613195 * (x - 1) + 462027 * (x - 1) ^ 2 + 220948 * (x - 1) ^ 3 +
      46208 * (x - 1) ^ 4)
  + (x ^ 5 - 1) ^ 5 * (181031 + 120245 * (x - 1) + 477 * (x - 1) ^ 2 - 23717 * (x - 1) ^ 3 -
      6797 * (x - 1) ^ 4)
  + (x ^ 5 - 1) ^ 6 * (-259 + 2795 * (x - 1) + 1978 * (x - 1) ^ 2 + 774 * (x - 1) ^ 3 +
      129 * (x - 1) ^ 4)
  + (x ^ 5 - 1) ^ 7 * 43

/-- The cross-multiplied `(HCJ)` identity: `n'd - n d' = -360 x (x⁵+3)³ (x⁸+3) h₄ Q`. -/
theorem JX_poly_id (x : ℝ) :
    (-4 * (4 * (x ^ 5 + 3) ^ 3 * (5 * x ^ 4)) * P13 x + (-4 * (x ^ 5 + 3) ^ 4) *
        (39 * x ^ 12 + 72 * x ^ 11 - 286 * x ^ 10 - 580 * x ^ 9 - 810 * x ^ 8 - 456 * x ^ 7 -
          168 * x ^ 6 + 144 * x ^ 5 + 285 * x ^ 4 + 360 * x ^ 3 + 126 * x ^ 2 - 12 * x - 54)) *
      (15 * x ^ 2 * (43 * x ^ 5 - 31) * (x ^ 8 + 3) ^ 2 * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) ^ 2) -
    (-4 * (x ^ 5 + 3) ^ 4 * P13 x) *
      (15 * (2 * x) * (43 * x ^ 5 - 31) * (x ^ 8 + 3) ^ 2 * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) ^ 2 +
        15 * x ^ 2 * (215 * x ^ 4) * (x ^ 8 + 3) ^ 2 * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) ^ 2 +
        15 * x ^ 2 * (43 * x ^ 5 - 31) * (2 * (x ^ 8 + 3) * (8 * x ^ 7)) *
          (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) ^ 2 +
        15 * x ^ 2 * (43 * x ^ 5 - 31) * (x ^ 8 + 3) ^ 2 *
          (2 * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) * (4 * x ^ 3 + 3 * x ^ 2 + 2 * x + 1)))
    = -360 * x * (x ^ 5 + 3) ^ 3 * (x ^ 8 + 3) * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) * Qpol x := by
  unfold Qpol P13
  ring

/-- **`(HCJ)`**: `J'(x) = -8 (x⁵+3)³ Q(x) / (5 x³ (43x⁵-31)² (x⁸+3)³ h₄³)`. -/
theorem JX_deriv {x : ℝ} (hx : 1 ≤ x) :
    HasDerivAt JX (-8 * (x ^ 5 + 3) ^ 3 * Qpol x /
      (5 * x ^ 3 * (43 * x ^ 5 - 31) ^ 2 * (x ^ 8 + 3) ^ 3 * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) ^ 3)) x := by
  have hx0 : 0 ≤ x := by linarith
  have hN := (N_pos hx0).ne'
  have hG := (G_pos hx0).ne'
  have hh := (h4_pos hx0).ne'
  have hc := (c43_pos hx).ne'
  have hx1 : x ≠ 0 := by positivity
  have hP : HasDerivAt P13 (39 * x ^ 12 + 72 * x ^ 11 - 286 * x ^ 10 - 580 * x ^ 9 - 810 * x ^ 8 -
      456 * x ^ 7 - 168 * x ^ 6 + 144 * x ^ 5 + 285 * x ^ 4 + 360 * x ^ 3 + 126 * x ^ 2 - 12 * x - 54) x := by
    unfold P13
    have d13 := (hasDerivAt_pow 13 x).const_mul (3 : ℝ)
    have d12 := (hasDerivAt_pow 12 x).const_mul (6 : ℝ)
    have d11 := (hasDerivAt_pow 11 x).const_mul (26 : ℝ)
    have d10 := (hasDerivAt_pow 10 x).const_mul (58 : ℝ)
    have d9 := (hasDerivAt_pow 9 x).const_mul (90 : ℝ)
    have d8 := (hasDerivAt_pow 8 x).const_mul (57 : ℝ)
    have d7 := (hasDerivAt_pow 7 x).const_mul (24 : ℝ)
    have d6 := (hasDerivAt_pow 6 x).const_mul (24 : ℝ)
    have d5 := (hasDerivAt_pow 5 x).const_mul (57 : ℝ)
    have d4 := (hasDerivAt_pow 4 x).const_mul (90 : ℝ)
    have d3 := (hasDerivAt_pow 3 x).const_mul (42 : ℝ)
    have d2 := (hasDerivAt_pow 2 x).const_mul (6 : ℝ)
    have d1 := (hasDerivAt_id x).const_mul (54 : ℝ)
    have := (((((((((((((d13.add d12).sub d11).sub d10).sub d9).sub d8).sub d7).add d6).add d5).add d4).add d3).sub d2).sub d1).sub_const (27 : ℝ))
    refine this.congr_deriv ?_
    norm_num
    ring
  have hN5 : HasDerivAt (fun x : ℝ => (x ^ 5 + 3) ^ 4) (4 * (x ^ 5 + 3) ^ 3 * (5 * x ^ 4)) x := by
    have := ((hasDerivAt_pow 5 x).add_const 3).pow 4
    convert this using 1 <;> simp
  have hn : HasDerivAt (fun x : ℝ => -4 * (x ^ 5 + 3) ^ 4 * P13 x)
      (-4 * (4 * (x ^ 5 + 3) ^ 3 * (5 * x ^ 4)) * P13 x + (-4 * (x ^ 5 + 3) ^ 4) *
        (39 * x ^ 12 + 72 * x ^ 11 - 286 * x ^ 10 - 580 * x ^ 9 - 810 * x ^ 8 - 456 * x ^ 7 -
          168 * x ^ 6 + 144 * x ^ 5 + 285 * x ^ 4 + 360 * x ^ 3 + 126 * x ^ 2 - 12 * x - 54)) x :=
    (hN5.const_mul (-4)).mul hP
  have hc1 : HasDerivAt (fun x : ℝ => 43 * x ^ 5 - 31) (215 * x ^ 4) x := by
    have := ((hasDerivAt_pow 5 x).const_mul 43).sub_const 31
    refine this.congr_deriv ?_
    norm_num
    ring
  have hG2 : HasDerivAt (fun x : ℝ => (x ^ 8 + 3) ^ 2) (2 * (x ^ 8 + 3) * (8 * x ^ 7)) x := by
    have := ((hasDerivAt_pow 8 x).add_const 3).pow 2
    convert this using 1 <;> simp
  have hh1 : HasDerivAt (fun x : ℝ => x ^ 4 + x ^ 3 + x ^ 2 + x + 1)
      (4 * x ^ 3 + 3 * x ^ 2 + 2 * x + 1) x := by
    simpa using ((((hasDerivAt_pow 4 x).add (hasDerivAt_pow 3 x)).add (hasDerivAt_pow 2 x)).add
      (hasDerivAt_id x)).add_const 1
  have hh2 : HasDerivAt (fun x : ℝ => (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) ^ 2)
      (2 * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) * (4 * x ^ 3 + 3 * x ^ 2 + 2 * x + 1)) x := by
    have := hh1.pow 2
    convert this using 1 <;> simp
  have hd : HasDerivAt (fun x : ℝ => 15 * x ^ 2 * (43 * x ^ 5 - 31) * (x ^ 8 + 3) ^ 2 *
      (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) ^ 2)
      (15 * (2 * x) * (43 * x ^ 5 - 31) * (x ^ 8 + 3) ^ 2 * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) ^ 2 +
        15 * x ^ 2 * (215 * x ^ 4) * (x ^ 8 + 3) ^ 2 * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) ^ 2 +
        15 * x ^ 2 * (43 * x ^ 5 - 31) * (2 * (x ^ 8 + 3) * (8 * x ^ 7)) *
          (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) ^ 2 +
        15 * x ^ 2 * (43 * x ^ 5 - 31) * (x ^ 8 + 3) ^ 2 *
          (2 * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) * (4 * x ^ 3 + 3 * x ^ 2 + 2 * x + 1))) x := by
    have h15 : HasDerivAt (fun x : ℝ => 15 * x ^ 2) (15 * (2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).const_mul 15
    have := (((h15.mul hc1).mul hG2).mul hh2)
    refine this.congr_deriv ?_
    simp only [Pi.mul_apply]
    ring
  have hne : 15 * x ^ 2 * (43 * x ^ 5 - 31) * (x ^ 8 + 3) ^ 2 *
      (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) ^ 2 ≠ 0 := by
    have := mul_ne_zero (mul_ne_zero (mul_ne_zero (by positivity : (15 : ℝ) * x ^ 2 ≠ 0) hc)
      (pow_ne_zero 2 hG)) (pow_ne_zero 2 hh)
    exact this
  have := hn.div hd hne
  unfold JX
  convert this using 1
  have hD1 : (5 * x ^ 3 * (43 * x ^ 5 - 31) ^ 2 * (x ^ 8 + 3) ^ 3 *
      (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) ^ 3) ≠ 0 := by
    have := mul_ne_zero (mul_ne_zero (mul_ne_zero (by positivity : (5 : ℝ) * x ^ 3 ≠ 0)
      (pow_ne_zero 2 hc)) (pow_ne_zero 3 hG)) (pow_ne_zero 3 hh)
    exact this
  rw [div_eq_div_iff hD1 (pow_ne_zero 2 hne)]
  have hW := JX_poly_id x
  linear_combination (-(5 * x ^ 3 * (43 * x ^ 5 - 31) ^ 2 * (x ^ 8 + 3) ^ 3 *
    (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) ^ 3)) * hW

theorem Q_aux {y R : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hR0 : 0 ≤ R) (hR1 : R ≤ 31) :
    0 < (225600 + 457600 * y + 471040 * y ^ 2 + 240000 * y ^ 3 + 48640 * y ^ 4)
      + R * (582160 + 1108000 * y + 1118304 * y ^ 2 + 557584 * y ^ 3 + 110864 * y ^ 4)
      + R ^ 2 * (690608 + 1195520 * y + 1018512 * y ^ 2 + 418768 * y ^ 3 + 68128 * y ^ 4)
      + R ^ 3 * (756896 + 1304520 * y + 1151162 * y ^ 2 + 522393 * y ^ 3 + 96703 * y ^ 4)
      + R ^ 4 * (516296 + 613195 * y + 462027 * y ^ 2 + 220948 * y ^ 3 + 46208 * y ^ 4)
      + R ^ 5 * (181031 + 120245 * y + 477 * y ^ 2 - 23717 * y ^ 3 - 6797 * y ^ 4)
      + R ^ 6 * (-259 + 2795 * y + 1978 * y ^ 2 + 774 * y ^ 3 + 129 * y ^ 4)
      + R ^ 7 * 43 := by
  have y2 : y ^ 3 ≤ 1 := pow_le_one₀ hy0 hy1
  have y4 : y ^ 4 ≤ 1 := pow_le_one₀ hy0 hy1
  have P0 : 0 < 225600 + 457600 * y + 471040 * y ^ 2 + 240000 * y ^ 3 + 48640 * y ^ 4 := by positivity
  have P1 : 0 ≤ R * (582160 + 1108000 * y + 1118304 * y ^ 2 + 557584 * y ^ 3 + 110864 * y ^ 4) := by
    positivity
  have P2 : 0 ≤ R ^ 2 * (690608 + 1195520 * y + 1018512 * y ^ 2 + 418768 * y ^ 3 + 68128 * y ^ 4) := by
    positivity
  have P3 : 0 ≤ R ^ 3 * (756896 + 1304520 * y + 1151162 * y ^ 2 + 522393 * y ^ 3 + 96703 * y ^ 4) := by
    positivity
  have P4 : 0 ≤ R ^ 4 * (516296 + 613195 * y + 462027 * y ^ 2 + 220948 * y ^ 3 + 46208 * y ^ 4) := by
    positivity
  have P7 : 0 ≤ R ^ 7 * 43 := by positivity
  have h5 : 150517 ≤ 181031 + 120245 * y + 477 * y ^ 2 - 23717 * y ^ 3 - 6797 * y ^ 4 := by
    nlinarith [sq_nonneg y]
  have h6 : -259 ≤ -259 + 2795 * y + 1978 * y ^ 2 + 774 * y ^ 3 + 129 * y ^ 4 := by
    have : 0 ≤ 2795 * y + 1978 * y ^ 2 + 774 * y ^ 3 + 129 * y ^ 4 := by positivity
    linarith
  have h56 : 0 ≤ R ^ 5 * (181031 + 120245 * y + 477 * y ^ 2 - 23717 * y ^ 3 - 6797 * y ^ 4) +
      R ^ 6 * (-259 + 2795 * y + 1978 * y ^ 2 + 774 * y ^ 3 + 129 * y ^ 4) := by
    have hR5 : 0 ≤ R ^ 5 := by positivity
    have : 0 ≤ (181031 + 120245 * y + 477 * y ^ 2 - 23717 * y ^ 3 - 6797 * y ^ 4) +
        R * (-259 + 2795 * y + 1978 * y ^ 2 + 774 * y ^ 3 + 129 * y ^ 4) := by
      nlinarith [mul_le_mul_of_nonneg_left h6 hR0]
    have := mul_nonneg hR5 this
    nlinarith
  linarith

theorem Q_pos {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) : 0 < Qpol x := by
  have hR1 : x ^ 5 ≤ 32 := by
    have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ x) hx2 5
    norm_num at this
    linarith
  have hR0 : 1 ≤ x ^ 5 := one_le_pow₀ hx1
  unfold Qpol
  exact Q_aux (by linarith) (by linarith) (by linarith) (by linarith)

theorem JX_anti : StrictAntiOn JX (Icc 1 2) := by
  refine strictAntiOn_of_hasDerivAt_neg (f' := fun x => -8 * (x ^ 5 + 3) ^ 3 * Qpol x /
      (5 * x ^ 3 * (43 * x ^ 5 - 31) ^ 2 * (x ^ 8 + 3) ^ 3 * (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) ^ 3))
    (fun x hx => (JX_deriv hx.1).continuousAt.continuousWithinAt)
    (fun x hx => JX_deriv hx.1.le) (fun x hx => ?_)
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hQ := Q_pos hx.1.le hx.2.le
  have hc := c43_pos hx.1.le
  have hN := N_pos hx0
  have hG := G_pos hx0
  have hh := h4_pos hx0
  have hx3 : 0 < x := by linarith [hx.1]
  apply div_neg_of_neg_of_pos
  · have : 0 < (x ^ 5 + 3) ^ 3 * Qpol x := by positivity
    linarith
  · positivity

end FormalResearch.FourQubitEntropy.RenyiFull
