module

public import FormalResearch.SignUncertainty.HankelGaussPeak
public import FormalResearch.SignUncertainty.HankelConnectorBound
public import FormalResearch.SignUncertainty.HankelStripSeries

/-!
# The local phase `Φ(ζ; ℓ) = S̃(ζ) + ζ ℓ` along the contour (`gt:7.7c` (b), (c))

`ℓ = log(π² ξ)` (complex).  `Φ' = g + ℓ`, `Φ'' = g'`.  On a vertical line `Re ζ = σ` (`0 < σ ≤ 0.04`) the real part
`φ(τ) = Re Φ(σ + iτ)` has curvature `φ'' = -Re g' ≤ -(4/5)σ` and a critical point at a root `ζ_+` of `g + ℓ`, so
`φ(τ) ≤ φ(τ₊) - (2/5) σ (τ - τ₊)²` on `|τ| ≤ 1/3` (`hankelLocPhi_vert_peak`); along the horizontal connectors
`Im ζ = ±1/3`, `∂_σ Re Φ ≤ -0.07` (`hankelLocPhi_conn_le`).
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `Φ(ζ; ℓ) = S̃(ζ) + ζ ℓ` with `ℓ = log(π² ξ)`. -/
noncomputable def hankelLocPhi (ℓ ζ : ℂ) : ℂ := SSer etaC ζ + ζ * ℓ

lemma hasDerivAt_hankelLocPhi (ℓ : ℂ) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    HasDerivAt (hankelLocPhi ℓ) (gSer etaC ζ + ℓ) ζ := by
  have := (hasDerivAt_SSer langerEta_etaC hζ).add ((hasDerivAt_id ζ).mul_const ℓ)
  exact this.congr_deriv (by simp)

lemma hasDerivAt_re_line {F : ℂ → ℂ} {F' z0 d : ℂ} {t : ℝ} (h : HasDerivAt F F' (z0 + (t : ℂ) * d)) :
    HasDerivAt (fun s : ℝ => (F (z0 + (s : ℂ) * d)).re) (F' * d).re t := by
  have h1 : HasDerivAt (fun s : ℝ => z0 + (s : ℂ) * d) d t := by
    simpa using (((hasDerivAt_id t).ofReal_comp).mul_const d).const_add z0
  have h2 := h.scomp t h1
  have h3 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h2
  have h3' : HasDerivAt (fun s : ℝ => (F (z0 + (s : ℂ) * d)).re) (Complex.reCLM (d • F')) t := h3
  refine h3'.congr_deriv ?_
  simp [mul_comm]

lemma norm_line_lt {σ τ : ℝ} (hσ : |σ| ≤ 0.1) (hτ : |τ| ≤ 1 / 3) : ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ < 1 := by
  calc ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ ≤ ‖(σ : ℂ)‖ + ‖(τ : ℂ) * Complex.I‖ := norm_add_le _ _
    _ ≤ 0.1 + 1 / 3 := by
        simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one]
        exact add_le_add hσ hτ
    _ < 1 := by norm_num

/-- Vertical peak: `φ(τ) ≤ φ(τ₊) - (2/5) σ (τ - τ₊)²` on `|τ| ≤ 1/3` when `g(σ + iτ₊) + ℓ = 0`. -/
theorem hankelLocPhi_vert_peak (ℓ : ℂ) {σ τ0 : ℝ} (hσ0 : 0 < σ) (hσ : σ ≤ 0.04) (hτ0 : |τ0| ≤ 1 / 3)
    (hcrit : gSer etaC ((σ : ℂ) + (τ0 : ℂ) * Complex.I) + ℓ = 0) :
    ∀ t ∈ Icc (-(1 / 3 : ℝ)) (1 / 3), (hankelLocPhi ℓ ((σ : ℂ) + (t : ℂ) * Complex.I)).re ≤
      (hankelLocPhi ℓ ((σ : ℂ) + (τ0 : ℂ) * Complex.I)).re - (2 / 5) * σ * (t - τ0) ^ 2 := by
  have hσa : |σ| ≤ 0.1 := by rw [abs_of_pos hσ0]; linarith
  have hmem : ∀ t ∈ Icc (-(1 / 3 : ℝ)) (1 / 3), |t| ≤ 1 / 3 := fun t ht => abs_le.2 ⟨ht.1, ht.2⟩
  have h1 : ∀ t ∈ Icc (-(1 / 3 : ℝ)) (1 / 3),
      HasDerivAt (fun s : ℝ => (hankelLocPhi ℓ ((σ : ℂ) + (s : ℂ) * Complex.I)).re)
        ((gSer etaC ((σ : ℂ) + (t : ℂ) * Complex.I) + ℓ) * Complex.I).re t := fun t ht =>
    hasDerivAt_re_line (z0 := (σ : ℂ)) (d := Complex.I) (t := t)
      (hasDerivAt_hankelLocPhi ℓ (norm_line_lt hσa (hmem t ht)))
  have h2 : ∀ t ∈ Icc (-(1 / 3 : ℝ)) (1 / 3),
      HasDerivAt (fun s : ℝ => ((gSer etaC ((σ : ℂ) + (s : ℂ) * Complex.I) + ℓ) * Complex.I).re)
        (gSerD etaC ((σ : ℂ) + (t : ℂ) * Complex.I) * Complex.I * Complex.I).re t := fun t ht =>
    hasDerivAt_re_line (F := fun z => (gSer etaC z + ℓ) * Complex.I)
      (z0 := (σ : ℂ)) (d := Complex.I) (t := t) (F' := gSerD etaC ((σ : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
      (((hasDerivAt_gSer langerEta_etaC (norm_line_lt hσa (hmem t ht))).add_const ℓ).mul_const Complex.I)
  have := quad_peak (φ := fun s : ℝ => (hankelLocPhi ℓ ((σ : ℂ) + (s : ℂ) * Complex.I)).re)
    (φ' := fun t => ((gSer etaC ((σ : ℂ) + (t : ℂ) * Complex.I) + ℓ) * Complex.I).re)
    (φ'' := fun t => (gSerD etaC ((σ : ℂ) + (t : ℂ) * Complex.I) * Complex.I * Complex.I).re)
    (m := (4 / 5) * σ) (τ0 := τ0) (L := 1 / 3)
    (abs_le.1 hτ0 |> fun h => ⟨h.1, h.2⟩) h1 h2
    (fun t ht => by
      have := re_gSerD_ge langerEta_etaC hσ0 hσ (hmem t ht)
      have e : (gSerD etaC ((σ : ℂ) + (t : ℂ) * Complex.I) * Complex.I * Complex.I).re =
          -(gSerD etaC ((σ : ℂ) + (t : ℂ) * Complex.I)).re := by simp
      rw [e]; linarith)
    (by simp [hcrit])
  intro t ht
  have := this t ht
  linarith

/-- Pointwise Gaussian bound along the vertical line: `e^{c φ(t)} ≤ e^{c φ(τ₊)} e^{-(2/5) c σ (t-τ₊)²}`. -/
theorem hankelLocPhi_vert_gauss (ℓ : ℂ) {c σ τ0 : ℝ} (hc : 0 < c) (hσ0 : 0 < σ) (hσ : σ ≤ 0.04)
    (hτ0 : |τ0| ≤ 1 / 3)
    (hcrit : gSer etaC ((σ : ℂ) + (τ0 : ℂ) * Complex.I) + ℓ = 0) :
    ∀ t ∈ Icc (-(1 / 3 : ℝ)) (1 / 3), Real.exp (c * (hankelLocPhi ℓ ((σ : ℂ) + (t : ℂ) * Complex.I)).re) ≤
      Real.exp (c * (hankelLocPhi ℓ ((σ : ℂ) + (τ0 : ℂ) * Complex.I)).re) *
        Real.exp (-((2 / 5) * c * σ) * (t - τ0) ^ 2) := by
  intro t ht
  have h := hankelLocPhi_vert_peak ℓ hσ0 hσ hτ0 hcrit t ht
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have := mul_le_mul_of_nonneg_left h hc.le
  nlinarith

lemma hankel_gauss_interval_le {b : ℝ} (hb : 0 < b) (τ0 : ℝ) :
    ∫ t in (-(1 / 3 : ℝ))..(1 / 3), Real.exp (-b * (t - τ0) ^ 2) ≤ Real.sqrt (Real.pi / b) := by
  have hgint : Integrable (fun t : ℝ => Real.exp (-b * (t - τ0) ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).comp_sub_right τ0
  rw [intervalIntegral.integral_of_le (by norm_num)]
  calc ∫ t in Ioc (-(1 / 3 : ℝ)) (1 / 3), Real.exp (-b * (t - τ0) ^ 2)
      ≤ ∫ t : ℝ, Real.exp (-b * (t - τ0) ^ 2) :=
        setIntegral_le_integral hgint (Eventually.of_forall fun t => (Real.exp_pos _).le)
    _ = Real.sqrt (Real.pi / b) := by
        have := integral_sub_right_eq_self (μ := volume) (fun x : ℝ => Real.exp (-b * x ^ 2)) τ0
        rw [this, integral_gaussian]

lemma hankel_exp_interval_le {a σ σ1 : ℝ} (ha : 0 < a) (h : σ ≤ σ1) :
    ∫ x in σ..σ1, Real.exp (-a * (x - σ)) ≤ 1 / a := by
  have hd : ∀ x ∈ uIcc σ σ1, HasDerivAt (fun x : ℝ => -(1 / a) * Real.exp (-a * (x - σ)))
      (Real.exp (-a * (x - σ))) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => -a * (x - σ)) (-a) x := by
      simpa using ((hasDerivAt_id x).sub_const σ).const_mul (-a)
    have := (h1.exp).const_mul (-(1 / a))
    convert this using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have : 0 < Real.exp (-a * (σ1 - σ)) := Real.exp_pos _
  simp only [sub_self, mul_zero, Real.exp_zero]
  have h1a : 0 < 1 / a := by positivity
  nlinarith

lemma hankel_exp_neg_le_inv_sqrt {t : ℝ} (ht : 0 < t) : Real.exp (-t) ≤ (Real.sqrt t)⁻¹ := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have h1 : Real.sqrt t ≤ Real.exp t := by
    have h2 : 0 ≤ (Real.sqrt t - 1) ^ 2 := sq_nonneg _
    have h3 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
    have h4 := Real.add_one_le_exp t
    nlinarith
  rw [Real.exp_neg]
  exact inv_anti₀ hs h1

/-- Connector bound: along `Im ζ = τ`, `τ² = 1/9`, `∂_σ Re Φ ≤ -0.07` when `Re ℓ ≤ 1/200`. -/
theorem hankelLocPhi_conn_le (ℓ : ℂ) (hl : ℓ.re ≤ 1 / 200) {σ1 σ2 τ : ℝ} (hτ : τ ^ 2 = 1 / 9)
    (h1 : 0 ≤ σ1) (h12 : σ1 ≤ σ2) (h2 : σ2 ≤ 0.1) :
    (hankelLocPhi ℓ ((σ2 : ℂ) + (τ : ℂ) * Complex.I)).re ≤
      (hankelLocPhi ℓ ((σ1 : ℂ) + (τ : ℂ) * Complex.I)).re - 0.07 * (σ2 - σ1) := by
  have hτa : |τ| ≤ 1 / 3 := by
    have h0 : (τ - 1 / 3) * (τ + 1 / 3) = 0 := by nlinarith
    rcases mul_eq_zero.1 h0 with h | h
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_le]; constructor <;> linarith
  set ψ : ℝ → ℝ := fun s => (hankelLocPhi ℓ ((s : ℂ) + (τ : ℂ) * Complex.I)).re with hψ
  have hder : ∀ s ∈ Icc σ1 σ2, HasDerivAt ψ (gSer etaC ((s : ℂ) + (τ : ℂ) * Complex.I) + ℓ).re s := by
    intro s hs
    have hn := norm_line_lt (σ := s) (τ := τ) (by rw [abs_of_nonneg (h1.trans hs.1)]; linarith [hs.2]) hτa
    have hh := hasDerivAt_hankelLocPhi ℓ hn
    rw [show (s : ℂ) + (τ : ℂ) * Complex.I = (τ : ℂ) * Complex.I + (s : ℂ) * 1 by ring] at hh
    have key := hasDerivAt_re_line (z0 := (τ : ℂ) * Complex.I) (d := 1) (t := s) hh
    have hf : (fun s : ℝ => (hankelLocPhi ℓ ((τ : ℂ) * Complex.I + (s : ℂ) * 1)).re) = ψ := by
      funext s; simp only [hψ]; congr 2; ring
    rw [hf] at key
    simpa only [mul_one, add_comm ((τ : ℂ) * Complex.I) (s : ℂ)] using key
  have hbound := (convex_Icc σ1 σ2).image_sub_le_mul_sub_of_deriv_le (f := ψ) (C := -0.07)
    (fun s hs => (hder s hs).continuousAt.continuousWithinAt)
    (fun s hs => by
      rw [interior_Icc] at hs
      exact (hder s ⟨hs.1.le, hs.2.le⟩).differentiableAt.differentiableWithinAt)
    (fun s hs => by
      rw [interior_Icc] at hs
      rw [(hder s ⟨hs.1.le, hs.2.le⟩).deriv]
      have := re_gSer_conn_le langerEta_etaC (σ := s) (τ := τ) (h1.trans hs.1.le) (by linarith [hs.2]) hτ
      simp only [Complex.add_re]
      linarith)
    σ1 ⟨le_rfl, h12⟩ σ2 ⟨h12, le_rfl⟩ h12
  simp only [hψ] at hbound
  linarith
