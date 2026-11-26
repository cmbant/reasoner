module

public import FormalResearch.ModularBootstrap.FiveTerm.OuterRest
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroAmpDeriv

/-!
# Three derivatives of `a_rest`, bounded, with `e^{-π|t|/2}` decay of the second and third (FIVE-S)

`a_rest = 2 log Λ + (5/2) log cosh(πt/4) + (3/4) log cosh(πt/2) - (1/2) log cosh(πt)`.  With
`T = tanh(π v_T)` (so `x_T' = T/2`), `W = E/(1-E)`, `E = e^{-4π x_T}` one has `T' = π(1-T²) v_T'`,
`W' = -2π T W (1+W)`, and `(2 log Λ)' = 4π T W`; `W ≤ C e^{-2π|t|}`.  Hence `a_rest'` is bounded and `a_rest''`,
`a_rest'''` exist and are `O(e^{-π|t|/2})` (the slowest term is `sech²(πt/4)`).  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

lemma hasDerivAt_tanh' (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have e : Real.tanh = Real.sinh / Real.cosh := by
    funext y; exact Real.tanh_eq_sinh_div_cosh y
  rw [e]
  refine h.congr_deriv ?_
  have hc := (Real.cosh_pos x).ne'
  simp only [Pi.div_apply]
  field_simp

/-- `T = tanh(π v_T)`. -/
noncomputable def Tt (t : ℝ) : ℝ := Real.tanh (π * vT t)

/-- `E = e^{-4π x_T}`. -/
noncomputable def Et (t : ℝ) : ℝ := Real.exp (-(4 * π * xT t))

/-- `W = E/(1-E)`. -/
noncomputable def Wt (t : ℝ) : ℝ := Et t / (1 - Et t)

lemma xD_eq_half_tanh (t : ℝ) : xD t = Tt t / 2 := by
  have hc : 0 < Real.cosh (π * t) := Real.cosh_pos _
  have hch : 0 < Real.cosh (π * t / 2) := Real.cosh_pos _
  have hsc : 0 < √(Real.cosh (π * t)) := Real.sqrt_pos.mpr hc
  have h1 : 1 + (√2 * Real.sinh (π * t / 2)) ^ 2 = Real.cosh (π * t) := one_add_two_sinh_sq t
  have hT : Tt t = √2 * Real.sinh (π * t / 2) / √(Real.cosh (π * t)) := by
    unfold Tt vT
    rw [mul_div_cancel₀ _ Real.pi_ne_zero, Real.tanh_arsinh, h1]
  have h2 : √(1 + Real.cosh (π * t)) = √2 * Real.cosh (π * t / 2) := by
    rw [one_add_cosh_eq, Real.sqrt_mul (by norm_num), Real.sqrt_sq hch.le]
  unfold xD
  rw [hT, h2, sinh_double]
  have hs2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  field_simp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring

lemma hasDerivAt_Tt (t : ℝ) : HasDerivAt Tt (π * (1 - Tt t ^ 2) * vD t) t := by
  have h := ((hasDerivAt_vT t).const_mul π)
  have h2 := (hasDerivAt_tanh' (π * vT t)).comp t h
  unfold Tt
  refine h2.congr_deriv ?_
  ring

lemma hasDerivAt_Et (t : ℝ) : HasDerivAt Et (-(2 * π) * Tt t * Et t) t := by
  have h1 := ((hasDerivAt_xT t).const_mul (4 * π)).neg
  have h2 := h1.exp
  unfold Et
  refine h2.congr_deriv ?_
  rw [xD_eq_half_tanh]; simp only [Pi.neg_apply]; ring

lemma Et_pos (t : ℝ) : 0 < Et t := Real.exp_pos _

lemma Et_lt_one (t : ℝ) : Et t < 1 := by
  unfold Et
  rw [← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  have := xT_pos t; have := Real.pi_pos
  nlinarith

lemma Wt_pos (t : ℝ) : 0 < Wt t := div_pos (Et_pos t) (by linarith [Et_lt_one t])

lemma hasDerivAt_Wt (t : ℝ) : HasDerivAt Wt (-(2 * π) * Tt t * Wt t * (1 + Wt t)) t := by
  have hE := hasDerivAt_Et t
  have h1 : 1 - Et t ≠ 0 := by linarith [Et_lt_one t]
  have h := hE.div (hE.const_sub 1) h1
  unfold Wt
  refine h.congr_deriv ?_
  field_simp
  ring


lemma abs_mul_le' {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

lemma abs_Tt_le (t : ℝ) : |Tt t| ≤ 1 := (Real.abs_tanh_lt_one _).le

lemma abs_one_sub_Tt_sq_le (t : ℝ) : |1 - Tt t ^ 2| ≤ 1 := by
  have h := Real.tanh_sq_lt_one (π * vT t)
  have h0 : 0 ≤ Tt t ^ 2 := sq_nonneg _
  unfold Tt at h0 ⊢
  rw [abs_le]; constructor <;> nlinarith

lemma cosh_half_le_sqrt (t : ℝ) : Real.cosh (π * t / 2) ≤ √(Real.cosh (π * t)) := by
  apply Real.le_sqrt_of_sq_le
  have := one_add_cosh_eq t
  nlinarith [Real.one_le_cosh (π * t)]

lemma abs_sinh_half_le (t : ℝ) : √2 * |Real.sinh (π * t / 2)| ≤ √(Real.cosh (π * t)) := by
  have h : (√2 * Real.sinh (π * t / 2)) ^ 2 ≤ Real.cosh (π * t) := by
    have := one_add_two_sinh_sq t; nlinarith [sq_nonneg (√2 * Real.sinh (π * t / 2))]
  have := Real.abs_le_sqrt h
  rwa [abs_mul, abs_of_pos (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))] at this

lemma vD_nonneg (t : ℝ) : 0 ≤ vD t := by
  unfold vD
  have := Real.cosh_pos (π * t / 2)
  have := Real.sqrt_pos.mpr (Real.cosh_pos (π * t))
  positivity

lemma vD_le (t : ℝ) : vD t ≤ 1 := by
  unfold vD
  have hs := Real.sqrt_pos.mpr (Real.cosh_pos (π * t))
  have h2 : √2 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [div_le_one (by positivity)]
  have := cosh_half_le_sqrt t
  have := Real.sqrt_nonneg 2
  nlinarith

lemma abs_vD_le (t : ℝ) : |vD t| ≤ 1 := by
  rw [abs_of_nonneg (vD_nonneg t)]; exact vD_le t

/-- `E ≤ e^{-2π|t|}` since `x_T ≥ |t|/2`. -/
lemma xT_ge_half_abs (t : ℝ) : |t| / 2 ≤ xT t := by
  have hpi := Real.pi_pos
  have h : Real.sinh (π * |t| / 2) ≤ √(Real.cosh (π * t)) := by
    have h0 : 0 ≤ π * |t| / 2 := by positivity
    have : Real.sinh (π * |t| / 2) ^ 2 ≤ Real.cosh (π * t) := by
      have e : Real.sinh (π * |t| / 2) ^ 2 = Real.sinh (π * t / 2) ^ 2 := by
        rcases abs_cases t with ⟨h1, _⟩ | ⟨h1, _⟩
        · rw [h1]
        · rw [h1, show π * -t / 2 = -(π * t / 2) by ring, Real.sinh_neg]; ring
      rw [e]; nlinarith [cosh_eq_one_add_two_sinh_sq t, sq_nonneg (Real.sinh (π * t / 2))]
    exact Real.le_sqrt_of_sq_le this
  unfold xT
  rw [le_div_iff₀ hpi]
  have := Real.arsinh_le_arsinh.mpr h
  rw [Real.arsinh_sinh] at this
  linarith

lemma Et_le_exp (t : ℝ) : Et t ≤ Real.exp (-(2 * π * |t|)) := by
  unfold Et
  apply Real.exp_le_exp.mpr
  have := xT_ge_half_abs t; have := Real.pi_pos
  nlinarith

/-- `E* = e^{-4π ξ*}`. -/
noncomputable def Estar : ℝ := Real.exp (-(4 * π * xiStar))

lemma Estar_lt_one : Estar < 1 := by
  unfold Estar; rw [← Real.exp_zero]; apply Real.exp_lt_exp.mpr
  have := xiStar_pos; have := Real.pi_pos; nlinarith

lemma Et_le_Estar (t : ℝ) : Et t ≤ Estar := by
  unfold Et Estar
  apply Real.exp_le_exp.mpr
  have := xiStar_le_xT t; have := Real.pi_pos; nlinarith

/-- `W ≤ W₀ e^{-2π|t|}`, `W₀ = 1/(1-E*)`. -/
lemma Wt_le (t : ℝ) : Wt t ≤ 1 / (1 - Estar) * Real.exp (-(2 * π * |t|)) := by
  unfold Wt
  have h1 : 0 < 1 - Estar := by linarith [Estar_lt_one]
  have h2 : 1 - Estar ≤ 1 - Et t := by linarith [Et_le_Estar t]
  have h3 : 0 < 1 - Et t := lt_of_lt_of_le h1 h2
  calc Et t / (1 - Et t) ≤ Et t / (1 - Estar) := div_le_div_of_nonneg_left (Et_pos t).le h1 h2
    _ ≤ Real.exp (-(2 * π * |t|)) / (1 - Estar) := div_le_div_of_nonneg_right (Et_le_exp t) h1.le
    _ = 1 / (1 - Estar) * Real.exp (-(2 * π * |t|)) := by ring

lemma Wt_le_W0 (t : ℝ) : Wt t ≤ 1 / (1 - Estar) := by
  have h := Wt_le t
  have h1 : 0 < 1 - Estar := by linarith [Estar_lt_one]
  have h2 : Real.exp (-(2 * π * |t|)) ≤ 1 := by
    rw [← Real.exp_zero]; apply Real.exp_le_exp.mpr
    have := Real.pi_pos; nlinarith [abs_nonneg t]
  calc Wt t ≤ 1 / (1 - Estar) * Real.exp (-(2 * π * |t|)) := h
    _ ≤ 1 / (1 - Estar) * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 1 / (1 - Estar) := mul_one _


/-- The derivative of `v_D`. -/
noncomputable def vD2 (t : ℝ) : ℝ :=
  ((√2 * (Real.sinh (π * t / 2) * (π / 2))) * (2 * √(Real.cosh (π * t))) -
    √2 * Real.cosh (π * t / 2) * (2 * (Real.sinh (π * t) * π / (2 * √(Real.cosh (π * t)))))) /
    (2 * √(Real.cosh (π * t))) ^ 2

lemma hasDerivAt_vD (t : ℝ) : HasDerivAt vD (vD2 t) t := by
  have hc : 0 < Real.cosh (π * t) := Real.cosh_pos _
  have h1 : HasDerivAt (fun t : ℝ => Real.cosh (π * t)) (Real.sinh (π * t) * π) t := by
    simpa using hasDerivAt_cosh_arg 1 t
  have hN : HasDerivAt (fun t : ℝ => √2 * Real.cosh (π * t / 2))
      (√2 * (Real.sinh (π * t / 2) * (π / 2))) t := (hasDerivAt_cosh_arg 2 t).const_mul _
  have hD : HasDerivAt (fun t : ℝ => 2 * √(Real.cosh (π * t)))
      (2 * (Real.sinh (π * t) * π / (2 * √(Real.cosh (π * t))))) t := (h1.sqrt hc.ne').const_mul _
  have hq : 0 < 2 * √(Real.cosh (π * t)) := by have := Real.sqrt_pos.mpr hc; positivity
  have h := hN.div hD hq.ne'
  unfold vD vD2
  exact h

lemma abs_vD2_le (t : ℝ) : |vD2 t| ≤ π := by
  have hpi := Real.pi_pos
  have hc : 0 < Real.cosh (π * t) := Real.cosh_pos _
  set r : ℝ := √(Real.cosh (π * t)) with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr hc
  have hch : 0 < Real.cosh (π * t / 2) := Real.cosh_pos _
  set ch := Real.cosh (π * t / 2) with hchdef
  set sh := Real.sinh (π * t / 2) with hshdef
  have h1 : √2 * |sh| ≤ r := abs_sinh_half_le t
  have h2 : ch ≤ r := cosh_half_le_sqrt t
  have hs2 : 0 < √2 := Real.sqrt_pos.mpr (by norm_num)
  have e : vD2 t = √2 * π * sh / (4 * r) - √2 * π * sh * ch ^ 2 / (2 * r ^ 3) := by
    unfold vD2
    rw [sinh_double]
    field_simp
    ring
  rw [e]
  have a1 : |√2 * π * sh / (4 * r)| ≤ π / 4 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 4 * r), div_le_iff₀ (by positivity)]
    rw [show |√2 * π * sh| = π * (√2 * |sh|) by
      rw [abs_mul, abs_mul, abs_of_pos hs2, abs_of_pos hpi]; ring]
    nlinarith [mul_le_mul_of_nonneg_left h1 hpi.le]
  have a2 : |√2 * π * sh * ch ^ 2 / (2 * r ^ 3)| ≤ π / 2 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * r ^ 3), div_le_iff₀ (by positivity)]
    rw [show |√2 * π * sh * ch ^ 2| = π * (√2 * |sh|) * ch ^ 2 by
      rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos hs2, abs_of_pos hpi, abs_of_pos hch]; ring]
    have h3 : ch ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hch.le h2 2
    have h4 : (√2 * |sh|) * ch ^ 2 ≤ r * r ^ 2 :=
      mul_le_mul h1 h3 (sq_nonneg _) hrpos.le
    nlinarith [mul_le_mul_of_nonneg_left h4 hpi.le]
  calc |√2 * π * sh / (4 * r) - √2 * π * sh * ch ^ 2 / (2 * r ^ 3)|
      ≤ |√2 * π * sh / (4 * r)| + |√2 * π * sh * ch ^ 2 / (2 * r ^ 3)| := abs_sub _ _
    _ ≤ π := by linarith


/-- `T' = π (1 - T²) v_D`. -/
noncomputable def Tp (t : ℝ) : ℝ := π * (1 - Tt t ^ 2) * vD t

/-- `W' = -2π T W (1 + W)`. -/
noncomputable def Wp (t : ℝ) : ℝ := -(2 * π) * Tt t * Wt t * (1 + Wt t)

noncomputable def Tpp (t : ℝ) : ℝ := π * ((-(2 * Tt t * Tp t)) * vD t + (1 - Tt t ^ 2) * vD2 t)

noncomputable def Wpp (t : ℝ) : ℝ :=
  -(2 * π) * (Tp t * Wt t * (1 + Wt t) + Tt t * Wp t * (1 + Wt t) + Tt t * Wt t * Wp t)

lemma hasDerivAt_Tp (t : ℝ) : HasDerivAt Tp (Tpp t) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 - Tt t ^ 2) (-(2 * Tt t * Tp t)) t := by
    have := ((hasDerivAt_Tt t).pow 2).const_sub 1
    refine this.congr_deriv ?_
    unfold Tp; simp
  have h := (h1.const_mul π).mul (hasDerivAt_vD t)
  unfold Tp Tpp
  refine (h.congr_deriv ?_)
  unfold Tp; ring

lemma hasDerivAt_Wp (t : ℝ) : HasDerivAt Wp (Wpp t) t := by
  have hT := hasDerivAt_Tt t
  have hW := hasDerivAt_Wt t
  have h := ((hT.const_mul (-(2 * π))).mul hW).mul (hW.const_add 1)
  unfold Wp Wpp
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply]
  unfold Tp Wp
  ring

lemma abs_Tp_le (t : ℝ) : |Tp t| ≤ π := by
  have hpi := Real.pi_pos
  unfold Tp
  rw [mul_assoc, abs_mul, abs_of_pos hpi]
  calc π * |(1 - Tt t ^ 2) * vD t| ≤ π * (1 * 1) := by
        apply mul_le_mul_of_nonneg_left (abs_mul_le' (abs_one_sub_Tt_sq_le t) (abs_vD_le t)) hpi.le
    _ = π := by ring

lemma abs_Wp_le (t : ℝ) : |Wp t| ≤ 2 * π * (1 + 1 / (1 - Estar)) * Wt t := by
  have hpi := Real.pi_pos
  have hw := Wt_pos t
  have hW0 := Wt_le_W0 t
  have hT := abs_Tt_le t
  unfold Wp
  have e : -(2 * π) * Tt t * Wt t * (1 + Wt t) = (-(2 * π)) * (Tt t * (Wt t * (1 + Wt t))) := by ring
  rw [e, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2 * π), abs_mul, abs_mul, abs_of_pos hw,
    abs_of_pos (by linarith : 0 < 1 + Wt t)]
  have h1 : |Tt t| * (Wt t * (1 + Wt t)) ≤ 1 * (Wt t * (1 + 1 / (1 - Estar))) := by
    apply mul_le_mul hT _ (by positivity) (by norm_num)
    apply mul_le_mul_of_nonneg_left (by linarith) hw.le
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * π)]


/-- `B = 1 + 1/(1 - E*)`. -/
noncomputable def Bw : ℝ := 1 + 1 / (1 - Estar)

lemma Bw_pos : 0 < Bw := by
  unfold Bw
  have : 0 < 1 - Estar := by linarith [Estar_lt_one]
  positivity

lemma W0_pos : 0 < 1 / (1 - Estar) := by
  have : 0 < 1 - Estar := by linarith [Estar_lt_one]
  positivity

lemma abs_Tpp_le (t : ℝ) : |Tpp t| ≤ 3 * π ^ 2 := by
  have hpi := Real.pi_pos
  unfold Tpp
  rw [abs_mul, abs_of_pos hpi]
  have h1 : |(-(2 * Tt t * Tp t)) * vD t| ≤ (2 * (1 * π)) * 1 := by
    apply abs_mul_le' _ (abs_vD_le t)
    rw [abs_neg, mul_assoc]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (abs_mul_le' (abs_Tt_le t) (abs_Tp_le t)) (by norm_num)
  have h2 : |(1 - Tt t ^ 2) * vD2 t| ≤ 1 * π := abs_mul_le' (abs_one_sub_Tt_sq_le t) (abs_vD2_le t)
  calc π * |(-(2 * Tt t * Tp t)) * vD t + (1 - Tt t ^ 2) * vD2 t|
      ≤ π * (|(-(2 * Tt t * Tp t)) * vD t| + |(1 - Tt t ^ 2) * vD2 t|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) hpi.le
    _ ≤ π * ((2 * (1 * π)) * 1 + 1 * π) := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hpi.le
    _ = 3 * π ^ 2 := by ring

lemma abs_Wpp_le (t : ℝ) :
    |Wpp t| ≤ 2 * π * (π * Bw + 2 * π * Bw ^ 2 + 2 * π * Bw * (1 / (1 - Estar))) * Wt t := by
  have hpi := Real.pi_pos
  have hw := Wt_pos t
  have hW0 := Wt_le_W0 t
  have hB : 1 + Wt t ≤ Bw := by unfold Bw; linarith
  have hBp := Bw_pos
  have hwp := abs_Wp_le t
  have hTp := abs_Tp_le t
  have hT := abs_Tt_le t
  have h1 : |Tp t * Wt t * (1 + Wt t)| ≤ π * Wt t * Bw := by
    rw [abs_mul, abs_mul, abs_of_pos hw, abs_of_pos (by linarith : 0 < 1 + Wt t)]
    exact mul_le_mul (mul_le_mul_of_nonneg_right hTp hw.le) hB (by linarith) (by positivity)
  have h2 : |Tt t * Wp t * (1 + Wt t)| ≤ 2 * π * Bw * Wt t * Bw := by
    rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < 1 + Wt t)]
    refine mul_le_mul ?_ hB (by linarith) (by positivity)
    calc |Tt t| * |Wp t| ≤ 1 * (2 * π * Bw * Wt t) := by
          apply mul_le_mul hT _ (abs_nonneg _) (by norm_num)
          have : 2 * π * (1 + 1 / (1 - Estar)) * Wt t = 2 * π * Bw * Wt t := by unfold Bw; ring
          linarith
      _ = 2 * π * Bw * Wt t := one_mul _
  have h3 : |Tt t * Wt t * Wp t| ≤ 1 * (1 / (1 - Estar)) * (2 * π * Bw * Wt t) := by
    rw [abs_mul, abs_mul, abs_of_pos hw]
    refine mul_le_mul (mul_le_mul hT hW0 hw.le (by norm_num)) ?_ (abs_nonneg _) (by have := W0_pos; linarith)
    have : 2 * π * (1 + 1 / (1 - Estar)) * Wt t = 2 * π * Bw * Wt t := by unfold Bw; ring
    linarith
  unfold Wpp
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 2 * π)]
  have := abs_add_le (Tp t * Wt t * (1 + Wt t) + Tt t * Wp t * (1 + Wt t)) (Tt t * Wt t * Wp t)
  have := abs_add_le (Tp t * Wt t * (1 + Wt t)) (Tt t * Wp t * (1 + Wt t))
  have hsum : |Tp t * Wt t * (1 + Wt t) + Tt t * Wp t * (1 + Wt t) + Tt t * Wt t * Wp t| ≤
      (π * Wt t * Bw + 2 * π * Bw * Wt t * Bw) + 1 * (1 / (1 - Estar)) * (2 * π * Bw * Wt t) := by
    linarith
  calc 2 * π * |Tp t * Wt t * (1 + Wt t) + Tt t * Wp t * (1 + Wt t) + Tt t * Wt t * Wp t|
      ≤ 2 * π * ((π * Wt t * Bw + 2 * π * Bw * Wt t * Bw) + 1 * (1 / (1 - Estar)) * (2 * π * Bw * Wt t)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * π * (π * Bw + 2 * π * Bw ^ 2 + 2 * π * Bw * (1 / (1 - Estar))) * Wt t := by ring

/-- `(2 log Λ)' = 4π T W` and its derivatives. -/
noncomputable def m1 (t : ℝ) : ℝ := 4 * π * Tt t * Wt t
noncomputable def m2 (t : ℝ) : ℝ := 4 * π * (Tp t * Wt t + Tt t * Wp t)
noncomputable def m3 (t : ℝ) : ℝ :=
  4 * π * (Tpp t * Wt t + Tp t * Wp t + (Tp t * Wp t + Tt t * Wpp t))

lemma hasDerivAt_m1 (t : ℝ) : HasDerivAt m1 (m2 t) t := by
  have h := ((hasDerivAt_Tt t).const_mul (4 * π)).mul (hasDerivAt_Wt t)
  unfold m1 m2
  refine h.congr_deriv ?_
  unfold Tp Wp
  ring

lemma hasDerivAt_m2 (t : ℝ) : HasDerivAt m2 (m3 t) t := by
  have h := (((hasDerivAt_Tp t).mul (hasDerivAt_Wt t)).add ((hasDerivAt_Tt t).mul (hasDerivAt_Wp t))).const_mul (4 * π)
  unfold m2 m3
  refine h.congr_deriv ?_
  unfold Tp Wp
  ring


lemma exp_neg_two_pi_le (t : ℝ) : Real.exp (-(2 * π * |t|)) ≤ Real.exp (-((π / 2) * |t|)) := by
  apply Real.exp_le_exp.mpr
  have := Real.pi_pos
  nlinarith [abs_nonneg t]

lemma abs_m2_le (t : ℝ) :
    |m2 t| ≤ 4 * π * (π + 2 * π * Bw) * (1 / (1 - Estar)) * Real.exp (-((π / 2) * |t|)) := by
  have hpi := Real.pi_pos
  have hw := Wt_pos t
  have hWe := (Wt_le t).trans (mul_le_mul_of_nonneg_left (exp_neg_two_pi_le t) W0_pos.le)
  have h1 : |Tp t * Wt t| ≤ π * Wt t := by
    rw [abs_mul, abs_of_pos hw]; exact mul_le_mul_of_nonneg_right (abs_Tp_le t) hw.le
  have h2 : |Tt t * Wp t| ≤ 1 * (2 * π * Bw * Wt t) := by
    rw [abs_mul]
    refine mul_le_mul (abs_Tt_le t) ?_ (abs_nonneg _) (by norm_num)
    have := abs_Wp_le t
    have e : 2 * π * (1 + 1 / (1 - Estar)) * Wt t = 2 * π * Bw * Wt t := by unfold Bw; ring
    linarith
  unfold m2
  rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * π)]
  have h3 := abs_add_le (Tp t * Wt t) (Tt t * Wp t)
  have h4 : |Tp t * Wt t + Tt t * Wp t| ≤ (π + 2 * π * Bw) * Wt t := by nlinarith
  calc 4 * π * |Tp t * Wt t + Tt t * Wp t| ≤ 4 * π * ((π + 2 * π * Bw) * Wt t) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ ≤ 4 * π * ((π + 2 * π * Bw) * (1 / (1 - Estar) * Real.exp (-((π / 2) * |t|)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hWe (by have := Bw_pos; positivity)
    _ = 4 * π * (π + 2 * π * Bw) * (1 / (1 - Estar)) * Real.exp (-((π / 2) * |t|)) := by ring

lemma abs_m3_le (t : ℝ) :
    |m3 t| ≤ 4 * π * (3 * π ^ 2 + 2 * (π * (2 * π * Bw)) +
      2 * π * (π * Bw + 2 * π * Bw ^ 2 + 2 * π * Bw * (1 / (1 - Estar)))) * (1 / (1 - Estar)) *
      Real.exp (-((π / 2) * |t|)) := by
  have hpi := Real.pi_pos
  have hw := Wt_pos t
  have hWe := (Wt_le t).trans (mul_le_mul_of_nonneg_left (exp_neg_two_pi_le t) W0_pos.le)
  have hBp := Bw_pos
  have h1 : |Tpp t * Wt t| ≤ 3 * π ^ 2 * Wt t := by
    rw [abs_mul, abs_of_pos hw]; exact mul_le_mul_of_nonneg_right (abs_Tpp_le t) hw.le
  have hwp : |Wp t| ≤ 2 * π * Bw * Wt t := by
    have := abs_Wp_le t
    have e : 2 * π * (1 + 1 / (1 - Estar)) * Wt t = 2 * π * Bw * Wt t := by unfold Bw; ring
    linarith
  have h2 : |Tp t * Wp t| ≤ π * (2 * π * Bw * Wt t) := by
    rw [abs_mul]; exact mul_le_mul (abs_Tp_le t) hwp (abs_nonneg _) hpi.le
  have h3 : |Tt t * Wpp t| ≤ 1 * (2 * π * (π * Bw + 2 * π * Bw ^ 2 + 2 * π * Bw * (1 / (1 - Estar))) * Wt t) := by
    rw [abs_mul]; exact mul_le_mul (abs_Tt_le t) (abs_Wpp_le t) (abs_nonneg _) (by norm_num)
  unfold m3
  rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * π)]
  have a1 := abs_add_le (Tpp t * Wt t + Tp t * Wp t) (Tp t * Wp t + Tt t * Wpp t)
  have a2 := abs_add_le (Tpp t * Wt t) (Tp t * Wp t)
  have a3 := abs_add_le (Tp t * Wp t) (Tt t * Wpp t)
  have h4 : |Tpp t * Wt t + Tp t * Wp t + (Tp t * Wp t + Tt t * Wpp t)| ≤
      (3 * π ^ 2 + 2 * (π * (2 * π * Bw)) +
        2 * π * (π * Bw + 2 * π * Bw ^ 2 + 2 * π * Bw * (1 / (1 - Estar)))) * Wt t := by nlinarith
  calc 4 * π * |Tpp t * Wt t + Tp t * Wp t + (Tp t * Wp t + Tt t * Wpp t)|
      ≤ 4 * π * ((3 * π ^ 2 + 2 * (π * (2 * π * Bw)) +
        2 * π * (π * Bw + 2 * π * Bw ^ 2 + 2 * π * Bw * (1 / (1 - Estar)))) * Wt t) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ ≤ 4 * π * ((3 * π ^ 2 + 2 * (π * (2 * π * Bw)) +
        2 * π * (π * Bw + 2 * π * Bw ^ 2 + 2 * π * Bw * (1 / (1 - Estar)))) *
          (1 / (1 - Estar) * Real.exp (-((π / 2) * |t|)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left hWe
        have hW0 := W0_pos
        generalize 1 / (1 - Estar) = w0 at hW0 ⊢
        positivity
    _ = _ := by ring


lemma hasDerivAt_logcosh (k t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.log (Real.cosh (π * t / k))) ((π / k) * Real.tanh (π * t / k)) t := by
  have h := (hasDerivAt_cosh_arg k t).log (Real.cosh_pos _).ne'
  refine h.congr_deriv ?_
  rw [Real.tanh_eq_sinh_div_cosh]
  ring

lemma hasDerivAt_tanh_arg (k t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.tanh (π * t / k)) ((π / k) * (1 - Real.tanh (π * t / k) ^ 2)) t := by
  have h := (hasDerivAt_tanh' (π * t / k)).comp t (hasDerivAt_arg k t)
  refine h.congr_deriv ?_
  ring

noncomputable def lc1 (k t : ℝ) : ℝ := (π / k) * Real.tanh (π * t / k)
noncomputable def lc2 (k t : ℝ) : ℝ := (π / k) * ((π / k) * (1 - Real.tanh (π * t / k) ^ 2))
noncomputable def lc3 (k t : ℝ) : ℝ :=
  (π / k) * ((π / k) * (-(2 * Real.tanh (π * t / k) * ((π / k) * (1 - Real.tanh (π * t / k) ^ 2)))))

lemma hasDerivAt_lc1 (k t : ℝ) : HasDerivAt (lc1 k) (lc2 k t) t := (hasDerivAt_tanh_arg k t).const_mul (π / k)

lemma hasDerivAt_lc2 (k t : ℝ) : HasDerivAt (lc2 k) (lc3 k t) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 - Real.tanh (π * t / k) ^ 2)
      (-(2 * Real.tanh (π * t / k) * ((π / k) * (1 - Real.tanh (π * t / k) ^ 2)))) t := by
    have := ((hasDerivAt_tanh_arg k t).pow 2).const_sub 1
    refine this.congr_deriv ?_
    simp
  exact (h1.const_mul (π / k)).const_mul (π / k)

lemma one_sub_tanh_sq_le (x : ℝ) : 1 - Real.tanh x ^ 2 ≤ 4 * Real.exp (-(2 * |x|)) := by
  have hc := Real.cosh_pos x
  have h1 : 1 - Real.tanh x ^ 2 = 1 / Real.cosh x ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]; field_simp; nlinarith [Real.cosh_sq x]
  have h2 := exp_abs_div_two_le_cosh x
  rw [h1]
  have h3 : Real.exp (2 * |x|) / 4 ≤ Real.cosh x ^ 2 := by
    have : (Real.exp |x| / 2) ^ 2 = Real.exp (2 * |x|) / 4 := by
      rw [div_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
    rw [← this]; exact pow_le_pow_left₀ (by positivity) h2 2
  have h4 : 0 < Real.exp (2 * |x|) / 4 := by positivity
  calc 1 / Real.cosh x ^ 2 ≤ 1 / (Real.exp (2 * |x|) / 4) := one_div_le_one_div_of_le h4 h3
    _ = 4 * Real.exp (-(2 * |x|)) := by rw [Real.exp_neg]; field_simp

lemma abs_lc1_le {k : ℝ} (hk : 0 < k) (t : ℝ) : |lc1 k t| ≤ π / k := by
  unfold lc1
  have hpi := Real.pi_pos
  rw [abs_mul, abs_of_pos (by positivity : 0 < π / k)]
  calc π / k * |Real.tanh (π * t / k)| ≤ π / k * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_tanh_lt_one _).le (by positivity)
    _ = π / k := mul_one _

lemma exp_two_abs_le {k : ℝ} (hk : 0 < k) (hk4 : k ≤ 4) (t : ℝ) :
    Real.exp (-(2 * |π * t / k|)) ≤ Real.exp (-((π / 2) * |t|)) := by
  apply Real.exp_le_exp.mpr
  have hpi := Real.pi_pos
  have : |π * t / k| = π * |t| / k := by
    rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_pos hk]
  rw [this]
  have h1 : π * |t| / 2 ≤ π * |t| / k * 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by norm_num) hk]
    nlinarith [mul_nonneg hpi.le (abs_nonneg t)]
  nlinarith

lemma abs_lc2_le {k : ℝ} (hk : 0 < k) (hk4 : k ≤ 4) (t : ℝ) :
    |lc2 k t| ≤ (π / k) * ((π / k) * (4 * Real.exp (-((π / 2) * |t|)))) := by
  unfold lc2
  have hpi := Real.pi_pos
  have hpk : 0 < π / k := by positivity
  rw [abs_mul, abs_mul, abs_of_pos hpk]
  have h0 : 0 ≤ 1 - Real.tanh (π * t / k) ^ 2 := by linarith [Real.tanh_sq_lt_one (π * t / k)]
  rw [abs_of_nonneg h0]
  have := (one_sub_tanh_sq_le (π * t / k)).trans (mul_le_mul_of_nonneg_left (exp_two_abs_le hk hk4 t) (by norm_num : (0:ℝ) ≤ 4))
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this hpk.le) hpk.le

lemma abs_lc3_le {k : ℝ} (hk : 0 < k) (hk4 : k ≤ 4) (t : ℝ) :
    |lc3 k t| ≤ (π / k) * ((π / k) * (2 * 1 * ((π / k) * (4 * Real.exp (-((π / 2) * |t|)))))) := by
  unfold lc3
  have hpi := Real.pi_pos
  have hpk : 0 < π / k := by positivity
  have h0 : 0 ≤ 1 - Real.tanh (π * t / k) ^ 2 := by linarith [Real.tanh_sq_lt_one (π * t / k)]
  simp only [abs_mul, abs_neg, abs_of_pos hpk, abs_of_nonneg h0, abs_two]
  have h1 := (one_sub_tanh_sq_le (π * t / k)).trans (mul_le_mul_of_nonneg_left (exp_two_abs_le hk hk4 t) (by norm_num : (0:ℝ) ≤ 4))
  have h2 : 2 * |Real.tanh (π * t / k)| * (π / k * (1 - Real.tanh (π * t / k) ^ 2)) ≤
      2 * 1 * (π / k * (4 * Real.exp (-((π / 2) * |t|)))) := by
    refine mul_le_mul ?_ (mul_le_mul_of_nonneg_left h1 hpk.le) (by positivity) (by norm_num)
    exact mul_le_mul_of_nonneg_left (Real.abs_tanh_lt_one _).le (by norm_num)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hpk.le) hpk.le


lemma two_lamT_deriv (t : ℝ) : 2 * (lD t / lamT t) = m1 t := by
  have h1 : 1 - Et t ≠ 0 := by linarith [Et_lt_one t]
  have h2 : 1 - Real.exp (-(4 * π * xiStar)) ≠ 0 := by
    have : 0 < 1 - Estar := by linarith [Estar_lt_one]
    unfold Estar at this; exact this.ne'
  unfold lD lamT m1 Wt
  rw [xD_eq_half_tanh]
  unfold Et at h1 ⊢
  field_simp

noncomputable def ac1 (t : ℝ) : ℝ := (5 / 2) * lc1 4 t + (3 / 4) * lc1 2 t - (1 / 2) * lc1 1 t
noncomputable def ac2 (t : ℝ) : ℝ := (5 / 2) * lc2 4 t + (3 / 4) * lc2 2 t - (1 / 2) * lc2 1 t
noncomputable def ac3 (t : ℝ) : ℝ := (5 / 2) * lc3 4 t + (3 / 4) * lc3 2 t - (1 / 2) * lc3 1 t

lemma hasDerivAt_aRest' (t : ℝ) : HasDerivAt aRest (ac1 t + m1 t) t := by
  have hl := ((hasDerivAt_lamT t).log (lamT_pos t).ne').const_mul 2
  have h4 := (hasDerivAt_logcosh 4 t).const_mul (5 / 2)
  have h2 := (hasDerivAt_logcosh 2 t).const_mul (3 / 4)
  have h1 := (hasDerivAt_logcosh 1 t).const_mul (1 / 2)
  have h := (((hl.add h4).add h2).sub h1)
  have e : aRest = fun t => 2 * Real.log (lamT t) + (5 / 2) * Real.log (Real.cosh (π * t / 4)) +
      (3 / 4) * Real.log (Real.cosh (π * t / 2)) - (1 / 2) * Real.log (Real.cosh (π * t / 1)) := by
    funext t; unfold aRest; rw [div_one]
  rw [e]
  refine h.congr_deriv ?_
  rw [← two_lamT_deriv t]
  unfold ac1 lc1
  ring

lemma hasDerivAt_ac1 (t : ℝ) : HasDerivAt ac1 (ac2 t) t := by
  have h := (((hasDerivAt_lc1 4 t).const_mul (5 / 2)).add ((hasDerivAt_lc1 2 t).const_mul (3 / 4))).sub
    ((hasDerivAt_lc1 1 t).const_mul (1 / 2))
  unfold ac1 ac2
  exact h

lemma hasDerivAt_ac2 (t : ℝ) : HasDerivAt ac2 (ac3 t) t := by
  have h := (((hasDerivAt_lc2 4 t).const_mul (5 / 2)).add ((hasDerivAt_lc2 2 t).const_mul (3 / 4))).sub
    ((hasDerivAt_lc2 1 t).const_mul (1 / 2))
  unfold ac2 ac3
  exact h

lemma abs_ac1_le (t : ℝ) : |ac1 t| ≤ (5 / 2) * (π / 4) + (3 / 4) * (π / 2) + (1 / 2) * (π / 1) := by
  unfold ac1
  have a := abs_lc1_le (k := 4) (by norm_num) t
  have b := abs_lc1_le (k := 2) (by norm_num) t
  have c := abs_lc1_le (k := 1) (by norm_num) t
  have h1 := abs_sub ((5 / 2) * lc1 4 t + (3 / 4) * lc1 2 t) ((1 / 2) * lc1 1 t)
  have h2 := abs_add_le ((5 / 2) * lc1 4 t) ((3 / 4) * lc1 2 t)
  simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 2), abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4),
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h1 h2
  nlinarith

lemma abs_ac23_le : ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ,
    |ac2 t| ≤ A * Real.exp (-((π / 2) * |t|)) ∧ |ac3 t| ≤ A * Real.exp (-((π / 2) * |t|)) := by
  have hpi := Real.pi_pos
  set Ee : ℝ → ℝ := fun t => Real.exp (-((π / 2) * |t|)) with hEe
  refine ⟨(5 / 2) * ((π / 4) * ((π / 4) * 4)) + (3 / 4) * ((π / 2) * ((π / 2) * 4)) + (1 / 2) * ((π / 1) * ((π / 1) * 4)) +
    ((5 / 2) * ((π / 4) * ((π / 4) * (2 * 1 * ((π / 4) * 4)))) + (3 / 4) * ((π / 2) * ((π / 2) * (2 * 1 * ((π / 2) * 4)))) +
      (1 / 2) * ((π / 1) * ((π / 1) * (2 * 1 * ((π / 1) * 4))))), by positivity, fun t => ?_⟩
  have hE := Real.exp_pos (-((π / 2) * |t|))
  have c2 : ∀ (k : ℝ) (hk : 0 < k) (hk4 : k ≤ 4), |lc2 k t| ≤ (π / k) * ((π / k) * 4) * Real.exp (-((π / 2) * |t|)) := by
    intro k hk hk4; have := abs_lc2_le hk hk4 t; linarith
  have c3 : ∀ (k : ℝ) (hk : 0 < k) (hk4 : k ≤ 4), |lc3 k t| ≤ (π / k) * ((π / k) * (2 * 1 * ((π / k) * 4))) * Real.exp (-((π / 2) * |t|)) := by
    intro k hk hk4; have := abs_lc3_le hk hk4 t; linarith
  have a2 := c2 4 (by norm_num) (by norm_num)
  have b2 := c2 2 (by norm_num) (by norm_num)
  have d2 := c2 1 (by norm_num) (by norm_num)
  have a3 := c3 4 (by norm_num) (by norm_num)
  have b3 := c3 2 (by norm_num) (by norm_num)
  have d3 := c3 1 (by norm_num) (by norm_num)
  constructor
  · unfold ac2
    have h1 := abs_sub ((5 / 2) * lc2 4 t + (3 / 4) * lc2 2 t) ((1 / 2) * lc2 1 t)
    have h2 := abs_add_le ((5 / 2) * lc2 4 t) ((3 / 4) * lc2 2 t)
    simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 2), abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4),
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h1 h2
    have hs : 0 ≤ (5 / 2) * ((π / 4) * ((π / 4) * 4)) + (3 / 4) * ((π / 2) * ((π / 2) * 4)) +
        (1 / 2) * ((π / 1) * ((π / 1) * 4)) + ((5 / 2) * ((π / 4) * ((π / 4) * (2 * 1 * ((π / 4) * 4)))) +
        (3 / 4) * ((π / 2) * ((π / 2) * (2 * 1 * ((π / 2) * 4)))) +
        (1 / 2) * ((π / 1) * ((π / 1) * (2 * 1 * ((π / 1) * 4))))) := by positivity
    nlinarith [mul_nonneg hs hE.le, mul_nonneg (by positivity : 0 ≤ (5 / 2) * ((π / 4) * ((π / 4) * (2 * 1 * ((π / 4) * 4)))) + (3 / 4) * ((π / 2) * ((π / 2) * (2 * 1 * ((π / 2) * 4)))) +
      (1 / 2) * ((π / 1) * ((π / 1) * (2 * 1 * ((π / 1) * 4))))) hE.le]
  · unfold ac3
    have h1 := abs_sub ((5 / 2) * lc3 4 t + (3 / 4) * lc3 2 t) ((1 / 2) * lc3 1 t)
    have h2 := abs_add_le ((5 / 2) * lc3 4 t) ((3 / 4) * lc3 2 t)
    simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 2), abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4),
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h1 h2
    nlinarith [mul_nonneg (by positivity : 0 ≤ (5 / 2) * ((π / 4) * ((π / 4) * 4)) + (3 / 4) * ((π / 2) * ((π / 2) * 4)) +
        (1 / 2) * ((π / 1) * ((π / 1) * 4))) hE.le]


lemma abs_m1_le (t : ℝ) : |m1 t| ≤ 4 * π * (1 / (1 - Estar)) := by
  have hpi := Real.pi_pos
  have hw := Wt_pos t
  have hW0 := Wt_le_W0 t
  unfold m1
  have e : 4 * π * Tt t * Wt t = (4 * π) * (Tt t * Wt t) := by ring
  rw [e, abs_mul, abs_of_pos (by positivity : 0 < 4 * π), abs_mul, abs_of_pos hw]
  have : |Tt t| * Wt t ≤ 1 * (1 / (1 - Estar)) :=
    mul_le_mul (abs_Tt_le t) hW0 hw.le (by norm_num)
  nlinarith

/-- **Three derivatives of `a_rest`:** the first is bounded, the second and third are `O(e^{-π|t|/2})`. -/
theorem aRest_deriv_data : ∃ d1 d2 d3 : ℝ → ℝ,
    (∀ t, HasDerivAt aRest (d1 t) t) ∧ (∀ t, HasDerivAt d1 (d2 t) t) ∧ (∀ t, HasDerivAt d2 (d3 t) t) ∧
    (∃ B : ℝ, ∀ t, |d1 t| ≤ B) ∧
    (∃ A : ℝ, ∀ t, |d2 t| ≤ A * Real.exp (-((π / 2) * |t|)) ∧ |d3 t| ≤ A * Real.exp (-((π / 2) * |t|))) := by
  obtain ⟨A, hA0, hA⟩ := abs_ac23_le
  refine ⟨fun t => ac1 t + m1 t, fun t => ac2 t + m2 t, fun t => ac3 t + m3 t,
    fun t => hasDerivAt_aRest' t, fun t => (hasDerivAt_ac1 t).add (hasDerivAt_m1 t),
    fun t => (hasDerivAt_ac2 t).add (hasDerivAt_m2 t),
    ⟨(5 / 2) * (π / 4) + (3 / 4) * (π / 2) + (1 / 2) * (π / 1) + 4 * π * (1 / (1 - Estar)), fun t => ?_⟩, ⟨A +
      (4 * π * (π + 2 * π * Bw) * (1 / (1 - Estar)) +
      4 * π * (3 * π ^ 2 + 2 * (π * (2 * π * Bw)) +
        2 * π * (π * Bw + 2 * π * Bw ^ 2 + 2 * π * Bw * (1 / (1 - Estar)))) * (1 / (1 - Estar))), fun t => ?_⟩⟩
  · exact (abs_add_le _ _).trans (add_le_add (abs_ac1_le t) (abs_m1_le t))
  · have hE := Real.exp_pos (-((π / 2) * |t|))
    have hm2 := abs_m2_le t
    have hm3 := abs_m3_le t
    obtain ⟨h2, h3⟩ := hA t
    have hK3 : 0 ≤ 4 * π * (3 * π ^ 2 + 2 * (π * (2 * π * Bw)) +
        2 * π * (π * Bw + 2 * π * Bw ^ 2 + 2 * π * Bw * (1 / (1 - Estar)))) * (1 / (1 - Estar)) := by
      have := Bw_pos
      have hW0 := W0_pos
      generalize 1 / (1 - Estar) = w0 at hW0 ⊢
      positivity
    have hK2 : 0 ≤ 4 * π * (π + 2 * π * Bw) * (1 / (1 - Estar)) := by
      have := Bw_pos
      have hW0 := W0_pos
      generalize 1 / (1 - Estar) = w0 at hW0 ⊢
      positivity
    constructor
    · refine (abs_add_le _ _).trans ?_
      nlinarith [mul_nonneg hK3 hE.le]
    · refine (abs_add_le _ _).trans ?_
      nlinarith [mul_nonneg hK2 hE.le]

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.aRest_deriv_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aRest_deriv_data

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
