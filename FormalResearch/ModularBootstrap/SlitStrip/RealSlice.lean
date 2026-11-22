module

public import FormalResearch.ModularBootstrap.SlitStrip.ConformalMap

/-!
# Real-slice preimage coordinates of the slit-strip map

Formalizes the real-slice geometry behind `RealSliceData` (`EntropyAndDeficit.lean`), coming from
`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Lemma G (`vlo:Gap`, "Slit-strip harmonic measure")
and the tip map of `blowup_limit.tex`, Lemma T1 (`bl:T1`) restricted to real `b = ξ_* - δ`.

For real `|b| < ξ_*` the upper-half-plane root of `e^{2πb} z² + (e^{2πb} - 1) z + 1 = 0` is explicit,
`z_b = (1-E)/(2E) + i √(6E - 1 - E²)/(2E)`, `E = e^{2πb}` (`confPreimage`).  We prove
`confB z_b = b` (`confB_confPreimage`), that `z_b` is the only preimage in the upper half-plane
(`eq_confPreimage_of_confB_eq`), and then, for `b = ξ_* - δ`, `0 < δ ≤ ξ_*`,

* `|Re z_b - σ_*| ≤ π δ`  (`sliceRe_sub_sigmaStar_le`),
* `δ^{1/2}/5 ≤ Im z_b ≤ 4 δ^{1/2}` (`sliceIm_lower`, `sliceIm_upper`),

which gives the structure `realSliceData : RealSliceData` as an honest consequence of the map
(`C_e = π`, `c_y = 1/5`, `C_y = 4`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap

private lemma sqrt2_gt' : (1.414 : ℝ) < √2 := by
  rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.414)]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

private lemma sqrt2_lt' : √2 < (1.415 : ℝ) := by
  rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.415)]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

private lemma sqrt2_mul_self'' : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)

/-- `E_* = e^{2πξ_*} = 3 + 2√2` and `E_- = e^{-2πξ_*} = 3 - 2√2`, the two zeros of `E² - 6E + 1`. -/
noncomputable def expTip : ℝ := 3 + 2 * √2

/-- `E_- = 3 - 2√2 = 1/E_*`. -/
noncomputable def expTipInv : ℝ := 3 - 2 * √2

lemma expTip_gt : (5.82 : ℝ) < expTip := by unfold expTip; linarith [sqrt2_gt']
lemma expTip_lt : expTip < (5.83 : ℝ) := by unfold expTip; linarith [sqrt2_lt']
lemma expTipInv_lt : expTipInv < (0.18 : ℝ) := by unfold expTipInv; linarith [sqrt2_gt']
lemma expTipInv_pos : 0 < expTipInv := by unfold expTipInv; linarith [sqrt2_lt']
lemma expTip_mul_expTipInv : expTip * expTipInv = 1 := by
  unfold expTip expTipInv; nlinarith [sqrt2_mul_self'']
lemma expTip_add_expTipInv : expTip + expTipInv = 6 := by unfold expTip expTipInv; ring

/-- `6E - 1 - E² = (E_* - E)(E - E_-)`. -/
lemma six_sub_eq (E : ℝ) : 6 * E - 1 - E ^ 2 = (expTip - E) * (E - expTipInv) := by
  have h1 := expTip_mul_expTipInv
  have h2 := expTip_add_expTipInv
  linear_combination (-E) * h2 + h1

/-! ### The explicit preimage -/

/-- The preimage `z_b ∈ ℍ` of a real `b ∈ (-ξ_*, ξ_*)` under `confB`: the upper-half-plane root
`((1-E) + i √(6E-1-E²)) / (2E)` of `E z² + (E-1) z + 1 = 0`, `E = e^{2πb}`. -/
noncomputable def confPreimage (b : ℝ) : ℂ :=
  ⟨(1 - Real.exp (2 * π * b)) / (2 * Real.exp (2 * π * b)),
    √(6 * Real.exp (2 * π * b) - 1 - Real.exp (2 * π * b) ^ 2) / (2 * Real.exp (2 * π * b))⟩

lemma six_pos_of_abs_lt {b : ℝ} (hb : |b| < xiStar) :
    0 < 6 * Real.exp (2 * π * b) - 1 - Real.exp (2 * π * b) ^ 2 := by
  obtain ⟨h1, h2⟩ := (exp_two_pi_mem_Ioo_iff b).mpr hb
  rw [six_sub_eq]
  exact mul_pos (by unfold expTip; linarith) (by unfold expTipInv; linarith)

lemma confPreimage_im_pos {b : ℝ} (hb : |b| < xiStar) : 0 < (confPreimage b).im := by
  unfold confPreimage
  exact div_pos (Real.sqrt_pos.mpr (six_pos_of_abs_lt hb)) (by positivity)

private lemma quad_of_xy {E x y : ℝ} (hE : 0 < E) (hx : x = (1 - E) / (2 * E))
    (hy : y ^ 2 = (6 * E - 1 - E ^ 2) / (4 * E ^ 2)) :
    (E : ℂ) * ((x : ℂ) + y * I) ^ 2 + ((E : ℂ) - 1) * ((x : ℂ) + y * I) + 1 = 0 := by
  have hre : E * (x ^ 2 - y ^ 2) + (E - 1) * x + 1 = 0 := by
    rw [hy, hx]; field_simp; ring
  have him : 2 * E * x * y + (E - 1) * y = 0 := by
    rw [hx]; field_simp; ring
  apply Complex.ext
  · simp [pow_two]; linarith
  · simp [pow_two]; linarith

lemma confPreimage_quadratic {b : ℝ} (hb : |b| < xiStar) :
    Complex.exp (2 * π * b) * confPreimage b ^ 2 +
      (Complex.exp (2 * π * b) - 1) * confPreimage b + 1 = 0 := by
  have hD := six_pos_of_abs_lt hb
  set E := Real.exp (2 * π * b) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hcE : Complex.exp (2 * π * b) = (E : ℂ) := by
    rw [hE, Complex.ofReal_exp]; push_cast; rfl
  rw [hcE]
  have hz : confPreimage b = (((1 - E) / (2 * E) : ℝ) : ℂ) +
      ((√(6 * E - 1 - E ^ 2) / (2 * E) : ℝ) : ℂ) * I := by
    exact Complex.mk_eq_add_mul_I _ _
  rw [hz]
  refine quad_of_xy hEpos rfl ?_
  rw [div_pow, Real.sq_sqrt hD.le]; ring

/-- **The real-slice preimage is a preimage.** `𝓑(z_b) = b` for real `|b| < ξ_*`. -/
theorem confB_confPreimage {b : ℝ} (hb : |b| < xiStar) : confB (confPreimage b) = b := by
  have hpos := confPreimage_im_pos hb
  have : |((b : ℝ) : ℂ).im| < 1 / 2 := by
    simp
  refine (confB_eq_iff_quadratic hpos this).mpr ?_
  exact confPreimage_quadratic hb

/-- **Uniqueness of the preimage:** the only point of the upper half-plane mapped by `𝓑` to a real
`b ∈ (-ξ_*, ξ_*)` is `z_b`. -/
theorem eq_confPreimage_of_confB_eq {b : ℝ} (hb : |b| < xiStar) {z : ℂ} (hz : 0 < z.im)
    (h : confB z = b) : z = confPreimage b :=
  confB_injOn hz (confPreimage_im_pos hb) (h.trans (confB_confPreimage hb).symm)

/-! ### Coordinates of the preimage of `ξ_* - δ` -/

/-- Real part `x(δ)` of the preimage of `ξ_* - δ`. -/
noncomputable def sliceRe (δ : ℝ) : ℝ := (confPreimage (xiStar - δ)).re

/-- Imaginary part `y(δ)` of the preimage of `ξ_* - δ`. -/
noncomputable def sliceIm (δ : ℝ) : ℝ := (confPreimage (xiStar - δ)).im

private lemma abs_xiStar_sub_lt {δ : ℝ} (hδ : δ ∈ Ioc 0 xiStar) : |xiStar - δ| < xiStar := by
  rw [abs_lt]; constructor <;> linarith [hδ.1, hδ.2, xiStar_pos]

lemma sliceIm_pos {δ : ℝ} (hδ : δ ∈ Ioc 0 xiStar) : 0 < sliceIm δ :=
  confPreimage_im_pos (abs_xiStar_sub_lt hδ)

/-- `𝓑(z(ξ_* - δ)) = ξ_* - δ` for the slice coordinates. -/
theorem confB_slice {δ : ℝ} (hδ : δ ∈ Ioc 0 xiStar) :
    confB ((sliceRe δ : ℂ) + sliceIm δ * I) = ((xiStar - δ : ℝ) : ℂ) := by
  have := confB_confPreimage (abs_xiStar_sub_lt hδ)
  rwa [show (sliceRe δ : ℂ) + sliceIm δ * I = confPreimage (xiStar - δ) from
    (Complex.mk_eq_add_mul_I _ _).symm]

private lemma exp_slice (δ : ℝ) :
    Real.exp (2 * π * (xiStar - δ)) = expTip * Real.exp (-(2 * π * δ)) := by
  have h : Real.exp (2 * π * xiStar) = expTip := exp_two_pi_xiStar
  rw [show 2 * π * (xiStar - δ) = 2 * π * xiStar + -(2 * π * δ) by ring, Real.exp_add, h]

private lemma two_pi_xiStar_lt_two : 2 * π * xiStar < 2 := by
  have h1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h2 : (5.83 : ℝ) < Real.exp 2 := by
    have h3 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h4 : (2.7 : ℝ) ^ 2 < Real.exp 1 ^ 2 := by gcongr
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith
  have : Real.exp (2 * π * xiStar) < Real.exp 2 := by
    rw [exp_two_pi_xiStar]; linarith [sqrt2_lt']
  exact Real.exp_lt_exp.mp this

lemma sigmaStar_eq_expTipInv : sigmaStar = (expTipInv - 1) / 2 := by
  unfold sigmaStar expTipInv; ring

/-- Closed form `x(δ) = (E_-·e^{2πδ} - 1)/2` of the real part of the preimage of `ξ_* - δ`. -/
lemma sliceRe_eq (δ : ℝ) : sliceRe δ = (expTipInv * Real.exp (2 * π * δ) - 1) / 2 := by
  unfold sliceRe confPreimage
  dsimp only
  rw [exp_slice]
  have hEs : expTip ≠ 0 := by have := expTip_gt; positivity
  have ht : Real.exp (2 * π * δ) = (Real.exp (-(2 * π * δ)))⁻¹ := by rw [Real.exp_neg, inv_inv]
  have htpos := Real.exp_pos (-(2 * π * δ))
  have hm : expTipInv = expTip⁻¹ := by
    exact (inv_eq_of_mul_eq_one_right expTip_mul_expTipInv).symm
  rw [ht, hm]
  field_simp

private lemma two_pi_delta_le {δ : ℝ} (hδ : δ ∈ Ioc 0 xiStar) : 2 * π * δ ≤ 2 := by
  have := two_pi_xiStar_lt_two
  nlinarith [hδ.2, Real.pi_pos]

/-- **`|Re z(ξ_*-δ) - σ_*| ≤ π δ`** (the real-part bound of `RealSliceData`). -/
theorem sliceRe_sub_sigmaStar_le {δ : ℝ} (hδ : δ ∈ Ioc 0 xiStar) :
    |sliceRe δ - sigmaStar| ≤ π * δ := by
  rw [sliceRe_eq, sigmaStar_eq_expTipInv]
  set u := 2 * π * δ with hu
  have hu0 : 0 ≤ u := by have := hδ.1; positivity
  have heu : Real.exp u ≤ expTip := by
    have h : Real.exp (2 * π * xiStar) = expTip := exp_two_pi_xiStar
    rw [← h]; exact Real.exp_le_exp.mpr (by rw [hu]; nlinarith [hδ.2, Real.pi_pos])
  have hge : 1 ≤ Real.exp u := Real.one_le_exp hu0
  have hEm := expTipInv_pos
  have habs : |(expTipInv * Real.exp u - 1) / 2 - (expTipInv - 1) / 2| =
      expTipInv * (Real.exp u - 1) / 2 := by
    rw [show (expTipInv * Real.exp u - 1) / 2 - (expTipInv - 1) / 2 =
      expTipInv * (Real.exp u - 1) / 2 by ring]
    exact abs_of_nonneg (by have := sub_nonneg.mpr hge; positivity)
  rw [habs]
  -- `e^u - 1 ≤ u e^u ≤ u E_*`
  have h1 : Real.exp u - 1 ≤ u * Real.exp u := by
    have := Real.add_one_le_exp (-u)
    rw [Real.exp_neg] at this
    have hpos := Real.exp_pos u
    have : 1 - u ≤ (Real.exp u)⁻¹ := by linarith
    calc Real.exp u - 1 = Real.exp u * (1 - (Real.exp u)⁻¹) := by field_simp
      _ ≤ Real.exp u * u := by gcongr; linarith
      _ = u * Real.exp u := by ring
  have h2 : u * Real.exp u ≤ u * expTip := by gcongr
  calc expTipInv * (Real.exp u - 1) / 2 ≤ expTipInv * (u * expTip) / 2 := by gcongr; linarith
    _ = π * δ := by
      have := expTip_mul_expTipInv
      rw [hu]; linear_combination (π * δ) * this

private lemma sliceIm_sq_eq {δ : ℝ} (hδ : δ ∈ Ioc 0 xiStar) :
    sliceIm δ ^ 2 =
      (1 - Real.exp (-(2 * π * δ))) * (expTip * Real.exp (-(2 * π * δ)) - expTipInv) /
        (4 * expTip * Real.exp (-(2 * π * δ)) ^ 2) := by
  have hD := six_pos_of_abs_lt (abs_xiStar_sub_lt hδ)
  unfold sliceIm confPreimage
  dsimp only
  rw [div_pow, Real.sq_sqrt hD.le]
  rw [exp_slice] at hD ⊢
  have hEs : expTip ≠ 0 := by have := expTip_gt; positivity
  have htpos := Real.exp_pos (-(2 * π * δ))
  rw [six_sub_eq]
  field_simp
  ring

private lemma t_ge {δ : ℝ} (hδ : δ ∈ Ioc 0 xiStar) : expTipInv ≤ Real.exp (-(2 * π * δ)) := by
  have h : Real.exp (-(2 * π * xiStar)) = expTipInv := exp_neg_two_pi_xiStar
  rw [← h]
  exact Real.exp_le_exp.mpr (by nlinarith [hδ.2, Real.pi_pos])

private lemma one_sub_t_le (δ : ℝ) :
    1 - Real.exp (-(2 * π * δ)) ≤ 2 * π * δ := by
  have := Real.add_one_le_exp (-(2 * π * δ)); linarith

private lemma one_sub_t_ge {δ : ℝ} (hδ : δ ∈ Ioc 0 xiStar) :
    2 * π * δ / 3 ≤ 1 - Real.exp (-(2 * π * δ)) := by
  set u := 2 * π * δ with hu
  have hu0 : 0 ≤ u := by have := hδ.1; positivity
  have hu2 := two_pi_delta_le hδ
  have h1 := Real.add_one_le_exp u
  have hpos := Real.exp_pos u
  rw [Real.exp_neg]
  have : (Real.exp u)⁻¹ ≤ 1 - u / 3 := by
    refine (inv_le_iff_one_le_mul₀' hpos).mpr ?_
    nlinarith
  linarith

/-- **`Im z(ξ_*-δ) ≤ 4 √δ`** (upper imaginary-part bound of `RealSliceData`). -/
theorem sliceIm_upper {δ : ℝ} (hδ : δ ∈ Ioc 0 xiStar) : sliceIm δ ≤ 4 * √δ := by
  have hy := sliceIm_pos hδ
  have hsq := sliceIm_sq_eq hδ
  set t := Real.exp (-(2 * π * δ)) with ht
  have htpos : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by have := hδ.1; nlinarith [Real.pi_pos])
  have htge := t_ge hδ
  have hEm := expTipInv_pos
  have hEs := expTip_mul_expTipInv
  have hEsb := expTip_lt
  have hEspos : 0 < expTip := by linarith [expTip_gt]
  have h1 := one_sub_t_le δ
  have hnum : (1 - t) * (expTip * t - expTipInv) ≤ 2 * π * δ * (expTip * t) := by
    have : expTip * t - expTipInv ≤ expTip * t := by linarith
    have h0 : 0 ≤ expTip * t - expTipInv := by nlinarith
    exact mul_le_mul h1 this h0 (by have := hδ.1; positivity)
  have hy2 : sliceIm δ ^ 2 ≤ 16 * δ := by
    rw [hsq, div_le_iff₀ (by positivity)]
    have hδ0 := hδ.1
    have hpi := Real.pi_lt_d2
    nlinarith [mul_pos hδ0 htpos, mul_pos (mul_pos hδ0 htpos) (by linarith : (0:ℝ) < expTip)]
  have hs0 := Real.sqrt_nonneg δ
  have hsd : √δ ^ 2 = δ := Real.sq_sqrt hδ.1.le
  by_contra hcon
  push Not at hcon
  nlinarith

/-- **`Im z(ξ_*-δ) ≥ √δ / 5`** (lower imaginary-part bound of `RealSliceData`). -/
theorem sliceIm_lower {δ : ℝ} (hδ : δ ∈ Ioc 0 xiStar) : (1 / 5) * √δ ≤ sliceIm δ := by
  have hy := sliceIm_pos hδ
  have hsq := sliceIm_sq_eq hδ
  set t := Real.exp (-(2 * π * δ)) with ht
  have htpos : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by have := hδ.1; nlinarith [Real.pi_pos])
  have htge := t_ge hδ
  have hEm := expTipInv_pos
  have hEmb := expTipInv_lt
  have hEsb := expTip_lt
  have hEsg := expTip_gt
  have hEspos : 0 < expTip := by linarith [expTip_gt]
  have h1 := one_sub_t_ge hδ
  have hδ0 := hδ.1
  have hpi := Real.pi_gt_d2
  have hfac : (0.82 : ℝ) ≤ expTip * t - expTipInv := by
    have : 1 ≤ expTip * t := by
      have := expTip_mul_expTipInv; nlinarith
    linarith
  have hnum : (2 * π * δ / 3) * 0.82 ≤ (1 - t) * (expTip * t - expTipInv) :=
    mul_le_mul h1 hfac (by norm_num) (by linarith)
  have hy2 : δ / 25 ≤ sliceIm δ ^ 2 := by
    rw [hsq, le_div_iff₀ (by positivity)]
    nlinarith [mul_pos hδ0 htpos, mul_pos hδ0 (by linarith : (0:ℝ) < expTip),
      mul_pos (mul_pos hδ0 htpos) htpos]
  have hs0 := Real.sqrt_nonneg δ
  have hsd : √δ ^ 2 = δ := Real.sq_sqrt hδ.1.le
  by_contra hcon
  push Not at hcon
  nlinarith

/-- **`RealSliceData` as an honest consequence of the map.** The coordinates `x(δ) + i y(δ)` are the
upper-half-plane preimage under `confB` (`confB_slice`, `eq_confPreimage_of_confB_eq`) of
`ξ_* - δ`, with `C_e = π`, `c_y = 1/5`, `C_y = 4` (Lemma G / `bl:T1`, real slice). -/
noncomputable def realSliceData : RealSliceData where
  xUHP := sliceRe
  yUHP := sliceIm
  C_e := π
  c_y := 1 / 5
  C_y := 4
  hC_e := Real.pi_pos.le
  hc_y := by norm_num
  hC_y := by norm_num
  re_bound := fun _ hδ => sliceRe_sub_sigmaStar_le hδ
  im_lower := fun _ hδ => sliceIm_lower hδ
  im_upper := fun _ hδ => sliceIm_upper hδ

/-- The data of `realSliceData` is the preimage under `𝓑` of `ξ_* - δ` in the upper half-plane. -/
theorem realSliceData_preimage {δ : ℝ} (hδ : δ ∈ Ioc 0 xiStar) :
    0 < realSliceData.yUHP δ ∧
      confB ((realSliceData.xUHP δ : ℂ) + realSliceData.yUHP δ * I) = ((xiStar - δ : ℝ) : ℂ) :=
  ⟨sliceIm_pos hδ, confB_slice hδ⟩

/-- Any upper-half-plane preimage of the real point `ξ_* - δ` is the point of `realSliceData`. -/
theorem realSliceData_unique {δ : ℝ} (hδ : δ ∈ Ioc 0 xiStar) {z : ℂ} (hz : 0 < z.im)
    (h : confB z = ((xiStar - δ : ℝ) : ℂ)) :
    z = (realSliceData.xUHP δ : ℂ) + realSliceData.yUHP δ * I := by
  rw [show (realSliceData.xUHP δ : ℂ) + realSliceData.yUHP δ * I = confPreimage (xiStar - δ) from
    (Complex.mk_eq_add_mul_I _ _).symm]
  exact eq_confPreimage_of_confB_eq (abs_xiStar_sub_lt hδ) hz h

/-! ### Consistency with the tip constant `q` of `bl:T1` -/

/-- **`Im z(ξ_* - δ) ~ √(δ/q)`** (`bl:T1`, real slice): `Im z(ξ_*-δ)² / δ → 1/q` as `δ ↓ 0`, with
`q = confTipQ = √2/(2π σ_*(σ_*²-1))`.  This ties the explicit root to the tip expansion
`𝓑(σ_* + w) = ξ_* + q w² + o(w²)` of `confBSlit_tip_expansion`. -/
theorem sliceIm_sq_div_tendsto :
    Tendsto (fun δ : ℝ => sliceIm δ ^ 2 / δ) (𝓝[>] 0) (𝓝 (1 / confTipQ)) := by
  have hEs : 0 < expTip := by linarith [expTip_gt]
  -- `(1 - e^{-2πδ})/δ → 2π`
  have hder : HasDerivAt (fun δ : ℝ => 1 - Real.exp (-(2 * π * δ))) (2 * π) 0 := by
    have h1 : HasDerivAt (fun δ : ℝ => -(2 * π * δ)) (-(2 * π)) 0 := by
      exact (((hasDerivAt_id (0 : ℝ)).const_mul (2 * π)).neg).congr_deriv (by simp)
    have h2 := (h1.exp).const_sub 1
    refine h2.congr_deriv ?_
    simp
  have hslope := (hasDerivAt_iff_tendsto_slope.mp hder).mono_left (nhdsWithin_mono 0
    (fun x (hx : x ∈ Ioi (0 : ℝ)) => (ne_of_gt hx : x ≠ 0)))
  have hslope' : Tendsto (fun δ : ℝ => (1 - Real.exp (-(2 * π * δ))) / δ) (𝓝[>] 0) (𝓝 (2 * π)) := by
    refine hslope.congr fun δ => ?_
    simp [slope_def_field]
  -- the continuous factor
  have hcont : Continuous fun δ : ℝ => (expTip * Real.exp (-(2 * π * δ)) - expTipInv) /
      (4 * expTip * Real.exp (-(2 * π * δ)) ^ 2) := by
    refine Continuous.div (by fun_prop) (by fun_prop) fun δ => ?_
    have := Real.exp_pos (-(2 * π * δ)); positivity
  have hlim2 : Tendsto (fun δ : ℝ => (expTip * Real.exp (-(2 * π * δ)) - expTipInv) /
      (4 * expTip * Real.exp (-(2 * π * δ)) ^ 2)) (𝓝[>] 0)
      (𝓝 ((expTip - expTipInv) / (4 * expTip))) := by
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have hprod := hslope'.mul hlim2
  have hval : 2 * π * ((expTip - expTipInv) / (4 * expTip)) = 1 / confTipQ := by
    unfold confTipQ expTip expTipInv sigmaStar
    have hsq := sqrt2_mul_self''
    have hs := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    have hpi := Real.pi_pos.ne'
    have h1 : (3 + 2 * √2) ≠ 0 := by positivity
    have h2 : (1 - √2) * ((1 - √2) ^ 2 - 1) ≠ 0 := by
      have : (1 - √2) * ((1 - √2) ^ 2 - 1) = 2 * (3 - 2 * √2) := by nlinarith
      rw [this]
      have : (3 - 2 * √2) ≠ 0 := by nlinarith [sqrt2_gt', sqrt2_lt']
      positivity
    rw [one_div, inv_div]
    field_simp
    nlinarith
  rw [hval] at hprod
  refine hprod.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT xiStar_pos] with δ hδ
  rw [sliceIm_sq_eq hδ]
  have : δ ≠ 0 := hδ.1.ne'
  field_simp

/-! ### Axiom checks for the headline theorems -/

/-- info: 'FormalResearch.ModularBootstrap.confB_confPreimage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confB_confPreimage

/-- info: 'FormalResearch.ModularBootstrap.eq_confPreimage_of_confB_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.eq_confPreimage_of_confB_eq

/-- info: 'FormalResearch.ModularBootstrap.confB_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.confB_slice

/-- info: 'FormalResearch.ModularBootstrap.sliceRe_sub_sigmaStar_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.sliceRe_sub_sigmaStar_le

/-- info: 'FormalResearch.ModularBootstrap.sliceIm_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.sliceIm_upper

/-- info: 'FormalResearch.ModularBootstrap.sliceIm_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.sliceIm_lower

/-- info: 'FormalResearch.ModularBootstrap.sliceIm_sq_div_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.sliceIm_sq_div_tendsto

/-- info: 'FormalResearch.ModularBootstrap.realSliceData_preimage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.realSliceData_preimage

/-- info: 'FormalResearch.ModularBootstrap.realSliceData_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.realSliceData_unique

end FormalResearch.ModularBootstrap
