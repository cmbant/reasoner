module

public import Mathlib
public import FormalResearch.SignUncertainty.CtDyadicTaperChart
public import FormalResearch.SignUncertainty.HankelBandChart

/-!
# `ct:dyadic` (4): the real Langer chart in the band variable `L` (`ct:langer-inv`, `ct:taper-harnack` (c))

For the Lean Hankel chart `hankelXi` (series-built, `HankelBandChart`) the Langer variable of the band is explicit in `L`:
`ũ(ξ(L)) = K·y(e^L - 1)`, `K = langerScale c = c^{2/3}κ`, `y(w) = Re chartY etaC w` (`ctYR`), because `π²ξ(x) - 1 = w` and
`y(w) = x/K` (`hankelBandU_hankelXi`).  Hence the band variable `v'(L) = -ũ(ξ(L))` is `K·g(L)`, `g(L) = -y(e^L - 1)`
(`ctChartG`), a `c`-independent function with `g(L) ≍ L` and `L g'(L) ≤ 1.01 g(L)` on `0 < L ≤ log(1 + 5·10⁻⁴)`
(`ctChartG_bounds`, `ctChartG_deriv_bounds`): this is the chart half of the logarithmic-derivative bound
`L ∂_L log v ≤ A_v` of `ct:taper-harnack` (c) (the paper's `L ∂_L log v' = (2/3)ϑ(τ₀)` with `ϑ ∈ [1, 3/2]`; on the Lean
chart disc `L ≤ 5·10⁻⁴` the constant is `1.01`).

* `ctUtildeXi_eq_hankelBandU`: `ũ(ξ) = hankelBandU c ξ` whenever `ξ` is in the image `hankelXi '' [-A, 0]` (no injectivity of
  `hankelXi` is used: any preimage `x` satisfies `x = K y(π²ξ - 1)`).
* `exists_hankelXi_eq`: for `0 ≤ L ≤ log(π² ξ(-r))` (`0 ≤ r ≤ A`) the value `e^L/π²` is attained on `[-r, 0]` (intermediate value).

**Proved**, unconditional.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `y(w) = Re chartY etaC w` for real `w`. -/
noncomputable def ctYR (w : ℝ) : ℝ := (chartY etaC (w : ℂ)).re

/-- `y'(w) = Re chartYD etaC w` for real `w`. -/
noncomputable def ctYRD (w : ℝ) : ℝ := (chartYD etaC (w : ℂ)).re

/-- `g(L) = -y(e^L - 1)`: `v'(L) = -ũ(ξ(L)) = K g(L)`. -/
noncomputable def ctChartG (L : ℝ) : ℝ := -ctYR (Real.exp L - 1)

lemma hankelBandU_eq (c ξ : ℝ) : hankelBandU c ξ = langerScale c * ctYR (π ^ 2 * ξ - 1) := rfl

/-- `ũ ∘ ξ = id` on the Langer disc: `hankelBandU c (hankelXi c x) = x`. -/
lemma hankelBandU_hankelXi {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : |x| ≤ langerRadius c) :
    hankelBandU c (hankelXi c x) = x := by
  have hK := langerScale_pos hc
  have hx' : |x| ≤ langerScale c * 4.94e-4 := hx
  obtain ⟨hreal, hre⟩ := chartYinv_real_point hc hx'
  set y : ℝ := x / langerScale c with hy
  set w : ℝ := (chartYinv etaC (y : ℂ)).re with hw
  have hyn : ‖(y : ℂ)‖ ≤ 4.94e-4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, hy, abs_div, abs_of_pos hK, div_le_iff₀ hK]; linarith
  obtain ⟨_, hspec⟩ := chartYinv_spec etaC (exists_chartY_small langerEta_etaC hyn)
  rw [hreal] at hspec
  have hxi : Real.pi ^ 2 * hankelXi c x - 1 = w := by
    unfold hankelXi
    have : Real.pi ^ 2 ≠ 0 := by positivity
    rw [← hy, ← hw]; field_simp; ring
  rw [hankelBandU_eq, hxi]
  have : ctYR w = y := by
    unfold ctYR; rw [hspec]; simp
  rw [this, hy]; field_simp

/-- **`ũ(ξ) = K y(π²ξ - 1)`** on the image of the chart: if `ξ = ξ(x₀)` for some `x₀ ∈ [-A, 0]` then
`ctUtildeXi c ξ = hankelBandU c ξ`. -/
lemma ctUtildeXi_eq_hankelBandU {c ξ : ℝ} (hc : 0 < c)
    (h : ∃ x ∈ Icc (-(langerRadius c)) 0, hankelXi c x = ξ) : ctUtildeXi c ξ = hankelBandU c ξ := by
  obtain ⟨hmem, hval⟩ := Function.invFunOn_pos h
  unfold ctUtildeXi
  set x₀ := Function.invFunOn (hankelXi c) (Icc (-(langerRadius c)) 0) ξ
  have hx₀ : |x₀| ≤ langerRadius c := abs_le.2 ⟨hmem.1, by linarith [hmem.2, langerRadius_pos hc]⟩
  rw [← hval, hankelBandU_hankelXi hc hx₀]

lemma hankelXi_zero {c : ℝ} (hc : 0 < c) : hankelXi c 0 = 1 / π ^ 2 := by
  have h := hankelXi_w_bounds hc (x := 0) (by rw [abs_zero]; exact (langerRadius_pos hc).le) le_rfl
  have hw : Real.pi ^ 2 * hankelXi c 0 - 1 = 0 := by
    have h3 := h.2.2
    simp only [mul_zero, zero_div] at h3
    linarith [h.1]
  have : Real.pi ^ 2 ≠ 0 := by positivity
  field_simp
  linarith

lemma continuousOn_hankelXi {c : ℝ} (hc : 0 < c) :
    ContinuousOn (hankelXi c) (Icc (-(langerRadius c)) (langerRadius c)) := fun _ hx =>
  (hasDerivAt_hankelXi hc (abs_le.2 hx)).continuousAt.continuousWithinAt

/-- **Surjectivity of the chart onto the band**: for `0 ≤ r ≤ A` and `0 ≤ L ≤ log(π² ξ(-r))`, `e^L/π²` is a value of `ξ` on
`[-r, 0]`. -/
lemma exists_hankelXi_eq {c r L : ℝ} (hc : 0 < c) (hr0 : 0 ≤ r) (hr : r ≤ langerRadius c) (hL0 : 0 ≤ L)
    (hL : L ≤ Real.log (Real.pi ^ 2 * hankelXi c (-r))) :
    ∃ x ∈ Icc (-r) 0, hankelXi c x = Real.exp L / π ^ 2 := by
  have hA := langerRadius_pos hc
  have hpi : 0 < Real.pi ^ 2 := by positivity
  have hxipos : 0 < Real.pi ^ 2 * hankelXi c (-r) := by
    have := hankelXi_pos hc (x := -r) (by rw [abs_neg, abs_of_nonneg hr0]; exact hr)
    positivity
  have hcont : ContinuousOn (hankelXi c) (Icc (-r) 0) :=
    (continuousOn_hankelXi hc).mono fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsub := intermediate_value_Icc' (by linarith : -r ≤ 0) hcont
  have hmem : Real.exp L / π ^ 2 ∈ Icc (hankelXi c 0) (hankelXi c (-r)) := by
    rw [hankelXi_zero hc]
    refine ⟨?_, ?_⟩
    · exact div_le_div_of_nonneg_right (Real.one_le_exp hL0) hpi.le
    · have h1 : Real.exp L ≤ Real.pi ^ 2 * hankelXi c (-r) := by
        have := Real.exp_le_exp.2 hL
        rwa [Real.exp_log hxipos] at this
      rw [div_le_iff₀ hpi]; linarith
  exact hsub hmem

/-! ### Bounds on `y` and `g` -/

lemma ctYR_add_le {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1e-3) : |ctYR w + w| ≤ 1.9e-3 * w := by
  have hn : ‖(w : ℂ)‖ ≤ 1e-3 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have h := norm_chartY_add_le langerEta_etaC hn
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0] at h
  have hre := Complex.abs_re_le_norm (chartY etaC (w : ℂ) + (w : ℂ))
  have : (chartY etaC (w : ℂ) + (w : ℂ)).re = ctYR w + w := by simp [ctYR]
  rw [this] at hre
  exact hre.trans h

lemma ctYR_hasDerivAt {w : ℝ} (hw : |w| ≤ 1e-3) : HasDerivAt ctYR (ctYRD w) w := by
  have hn : ‖(w : ℂ)‖ ≤ 1e-3 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have h := (hasDerivAt_chartY langerEta_etaC hn).real_of_complex
  exact h

lemma ctYRD_add_one_le {w : ℝ} (hw : |w| ≤ 1e-3) : |ctYRD w + 1| ≤ 4e-3 := by
  have hn : ‖(w : ℂ)‖ ≤ 1e-3 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have h := norm_chartYD_add_one_le langerEta_etaC hn
  have hre := Complex.abs_re_le_norm (chartYD etaC (w : ℂ) + 1)
  have : (chartYD etaC (w : ℂ) + 1).re = ctYRD w + 1 := by simp [ctYRD]
  rw [this] at hre
  exact hre.trans h

/-- `e^L - 1 ≤ L e^L`. -/
lemma exp_sub_one_le_mul (L : ℝ) : Real.exp L - 1 ≤ L * Real.exp L := by
  have h := Real.add_one_le_exp (-L)
  have h2 : Real.exp (-L) * Real.exp L = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos L]

/-- Bounds for `g(L) = -y(e^L - 1)` and `K g = v'` on the chart disc `e^L - 1 ≤ 5·10⁻⁴`:
`0.998 (e^L - 1) ≤ g ≤ 1.002 (e^L - 1)`, hence `0.998 L ≤ g(L) ≤ 1.0025 L`. -/
lemma ctChartG_bounds {L : ℝ} (hL0 : 0 ≤ L) (hL : Real.exp L - 1 ≤ 5e-4) :
    0.998 * L ≤ ctChartG L ∧ ctChartG L ≤ 1.0025 * L ∧
      0.998 * (Real.exp L - 1) ≤ ctChartG L ∧ ctChartG L ≤ 1.002 * (Real.exp L - 1) := by
  have hw0 : 0 ≤ Real.exp L - 1 := by linarith [Real.one_le_exp hL0]
  have h := abs_le.1 (ctYR_add_le hw0 (by linarith))
  have hLw : L ≤ Real.exp L - 1 := by linarith [Real.add_one_le_exp L]
  have hwL : Real.exp L - 1 ≤ L * Real.exp L := exp_sub_one_le_mul L
  have he : Real.exp L ≤ 1 + 5e-4 := by linarith
  have hwL' : Real.exp L - 1 ≤ 1.0005 * L := by nlinarith [mul_le_mul_of_nonneg_left he hL0]
  unfold ctChartG
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

lemma ctChartG_pos {L : ℝ} (hL0 : 0 < L) (hL : Real.exp L - 1 ≤ 5e-4) : 0 < ctChartG L := by
  have := (ctChartG_bounds hL0.le hL).1
  linarith

/-- `g'(L) = -y'(e^L - 1) e^L` and its bounds `0.996 ≤ g'(L) ≤ 1.0045` (on the chart disc). -/
lemma ctChartG_hasDerivAt {L : ℝ} (hL0 : 0 ≤ L) (hL : Real.exp L - 1 ≤ 5e-4) :
    HasDerivAt ctChartG (-(ctYRD (Real.exp L - 1)) * Real.exp L) L := by
  have hw0 : 0 ≤ Real.exp L - 1 := by linarith [Real.one_le_exp hL0]
  have hwabs : |Real.exp L - 1| ≤ 1e-3 := by rw [abs_of_nonneg hw0]; linarith
  have h1 : HasDerivAt (fun L : ℝ => Real.exp L - 1) (Real.exp L) L := (Real.hasDerivAt_exp L).sub_const 1
  have h2 := (ctYR_hasDerivAt hwabs).comp L h1
  have h3 : HasDerivAt (fun L : ℝ => -ctYR (Real.exp L - 1)) (-(ctYRD (Real.exp L - 1) * Real.exp L)) L := h2.neg
  rw [neg_mul]
  exact h3

lemma ctChartG_deriv_bounds {L : ℝ} (hL0 : 0 ≤ L) (hL : Real.exp L - 1 ≤ 5e-4) :
    0.996 * Real.exp L ≤ -(ctYRD (Real.exp L - 1)) * Real.exp L ∧
      -(ctYRD (Real.exp L - 1)) * Real.exp L ≤ 1.004 * Real.exp L := by
  have hw0 : 0 ≤ Real.exp L - 1 := by linarith [Real.one_le_exp hL0]
  have hwabs : |Real.exp L - 1| ≤ 1e-3 := by rw [abs_of_nonneg hw0]; linarith
  have h := abs_le.1 (ctYRD_add_one_le hwabs)
  have he := Real.exp_pos L
  constructor <;> nlinarith

/-- **`L g'(L) ≤ 1.01 g(L)`** (the chart half of `L ∂_L log v ≤ A_v`, `ct:taper-harnack` (c)). -/
lemma ctChartG_log_deriv {L : ℝ} (hL0 : 0 < L) (hL : Real.exp L - 1 ≤ 5e-4) :
    L * (-(ctYRD (Real.exp L - 1)) * Real.exp L) ≤ 1.01 * ctChartG L := by
  have hb := ctChartG_bounds hL0.le hL
  have hd := (ctChartG_deriv_bounds hL0.le hL).2
  have he : Real.exp L ≤ 1 + 5e-4 := by linarith
  have : L * (-(ctYRD (Real.exp L - 1)) * Real.exp L) ≤ L * (1.004 * 1.0005) := by
    apply mul_le_mul_of_nonneg_left _ hL0.le
    nlinarith [Real.exp_pos L]
  nlinarith [hb.1]

end FormalResearch.SignUncertainty
