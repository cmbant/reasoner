module

public import FormalResearch.SignUncertainty.HankelLocalPhase
public import FormalResearch.SignUncertainty.HankelWtBasics
public import FormalResearch.CohnElkies.PieceCUniform

/-!
# The local integrand `J_ξ` and its bounds on the contour rectangle (`gt:7.7c`)

`hankelJ c f ℓ ζ = (1-ζ)^{-1/2} e^{B_c(ζ)} e^{c Φ(ζ;ℓ)} W̃_c(ζ)`, `ℓ = log(π² ξ)`.  For real `ξ > 0` this is
`K₀(ζ,ξ) W̃_c(ζ)` (`hankelJ_eq_mellinK0`), the integrand of `hankel_inversion_line`.  It is holomorphic on
`0 < Re ζ < 1`, `‖ζ‖ < 1` and satisfies `‖J‖ ≤ 2 e^{c Re Φ}` on `0 < Re ζ ≤ 1/10`, `|Im ζ| ≤ 1/3` when `M[f] = 1`,
`c ≥ 2`.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Asymptotics

/-- `J_ξ(ζ) = (1-ζ)^{-1/2} e^{B_c(ζ)} e^{c Φ(ζ;ℓ)} W̃_c(ζ)`, `ℓ = log(π² ξ)`. -/
noncomputable def hankelJ (c : ℝ) (f : ℝ → ℝ) (ℓ ζ : ℂ) : ℂ :=
  (1 - ζ) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c ζ) * Complex.exp ((c : ℂ) * hankelLocPhi ℓ ζ) *
    hankelWt c f ζ

lemma hankelJ_eq_mellinK0 {c ξ : ℝ} {f : ℝ → ℝ} {ζ : ℂ} (hn : ‖ζ‖ ≤ 0.35) (hre : 0 < ζ.re) :
    hankelJ c f (Complex.log (Real.pi ^ 2 * ξ)) ζ = mellinK0 c ζ ξ * hankelWt c f ζ := by
  unfold hankelJ mellinK0 mellinPhi hankelLocPhi
  rw [stripS0Tilde_eq_SSer hn hre]

lemma hankelJ_differentiableOn {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) (ℓ : ℂ) :
    DifferentiableOn ℂ (hankelJ c f ℓ) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1 ∧ ‖ζ‖ < 1} := by
  intro ζ hζ
  obtain ⟨h0, h1, hn⟩ := hζ
  have hA : DifferentiableAt ℂ (fun ζ : ℂ => (1 - ζ) ^ (-(1 / 2 : ℂ))) ζ := by
    refine DifferentiableAt.cpow (by fun_prop) (differentiableAt_const _) ?_
    exact Complex.mem_slitPlane_iff.2 (Or.inl (by simpa using h1))
  have hB : DifferentiableAt ℂ (fun ζ : ℂ => Complex.exp (binetDiff c ζ)) ζ :=
    (((binetDiff_differentiableOn hc).differentiableAt
      ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds h1))).cexp
  have hC : DifferentiableAt ℂ (fun ζ : ℂ => Complex.exp ((c : ℂ) * hankelLocPhi ℓ ζ)) ζ :=
    ((hasDerivAt_hankelLocPhi ℓ hn).differentiableAt.const_mul (c : ℂ)).cexp
  have hopen : IsOpen {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hD : DifferentiableAt ℂ (hankelWt c f) ζ :=
    (hankelWt_differentiableOn hc hf).differentiableAt (hopen.mem_nhds ⟨h0, h1⟩)
  exact (((hA.mul hB).mul hC).mul hD).differentiableWithinAt

/-- `‖J‖ ≤ 2 e^{c Re Φ}` on the contour rectangle when `M[f] = 1`, `c ≥ 2`. -/
lemma norm_hankelJ_le {c ε : ℝ} (hc : 2 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) (ℓ : ℂ) {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re ≤ 1 / 10)
    (him : |ζ.im| ≤ 1 / 3) :
    ‖hankelJ c f ℓ ζ‖ ≤ 2 * Real.exp (c * (hankelLocPhi ℓ ζ).re) := by
  have hc0 : 0 < c := by linarith
  unfold hankelJ
  rw [norm_mul, norm_mul, norm_mul]
  -- the factor `(1 - ζ)^{-1/2}`
  have hz0 : (1 - ζ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hre : (9 : ℝ) / 10 ≤ ‖1 - ζ‖ := by
    have := Complex.re_le_norm (1 - ζ)
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith
  have hA : ‖(1 - ζ) ^ (-(1 / 2 : ℂ))‖ ≤ 10 / 9 := by
    rw [Complex.norm_cpow_of_ne_zero hz0]
    have hre' : (-(1 / 2 : ℂ)).re = -(1 / 2) := by simp
    have him' : (-(1 / 2 : ℂ)).im = 0 := by simp
    rw [hre', him', mul_zero, Real.exp_zero, div_one, Real.rpow_neg (norm_nonneg _)]
    have hs : (9 : ℝ) / 10 ≤ ‖1 - ζ‖ ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      have := Real.sqrt_le_sqrt (show ((9 : ℝ) / 10) ^ 2 ≤ ‖1 - ζ‖ by nlinarith)
      rwa [Real.sqrt_sq (by norm_num)] at this
    calc (‖1 - ζ‖ ^ (1 / 2 : ℝ))⁻¹ ≤ ((9 : ℝ) / 10)⁻¹ := inv_anti₀ (by norm_num) hs
      _ = 10 / 9 := by norm_num
  have hB : ‖Complex.exp (binetDiff c ζ)‖ ≤ 10 / 9 := by
    rw [Complex.norm_exp]
    have h1' := binetDiff_norm_le_strip hc0 h0 h1
    have h2 : (binetDiff c ζ).re ≤ 1 / 10 :=
      (Complex.re_le_norm _).trans (h1'.trans (one_div_le_one_div_of_le (by norm_num) (by linarith)))
    calc Real.exp (binetDiff c ζ).re ≤ Real.exp (1 / 10) := Real.exp_le_exp.2 h2
      _ ≤ 1 / (1 - 1 / 10) := (Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)).le
      _ = 10 / 9 := by norm_num
  have hC : ‖Complex.exp ((c : ℂ) * hankelLocPhi ℓ ζ)‖ = Real.exp (c * (hankelLocPhi ℓ ζ).re) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
  have hD : ‖hankelWt c f ζ‖ ≤ (6 / 5) * (12 / 11) := by
    have h := hankelWt_norm_le (by linarith : 3 / 2 < c) hf hε h0.le (by linarith) 
    rw [hM, one_mul] at h
    have hn : ‖1 + ζ‖ ≤ 1.44 := by
      have h3 := Complex.norm_le_abs_re_add_abs_im ζ
      have h4 := norm_add_le (1 : ℂ) ζ
      rw [abs_of_pos h0] at h3
      simp only [norm_one] at h4
      norm_num
      linarith
    have hs : ‖1 + ζ‖ ^ (1 / 2 : ℝ) ≤ 6 / 5 := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith⟩
    have he : Real.exp (1 / (6 * c)) ≤ 12 / 11 := by
      calc Real.exp (1 / (6 * c)) ≤ Real.exp (1 / 12) :=
            Real.exp_le_exp.2 (one_div_le_one_div_of_le (by norm_num) (by linarith))
        _ ≤ 1 / (1 - 1 / 12) := (Real.exp_bound_div_one_sub_of_interval' (by norm_num) (by norm_num)).le
        _ = 12 / 11 := by norm_num
    calc ‖hankelWt c f ζ‖ ≤ ‖1 + ζ‖ ^ (1 / 2 : ℝ) * Real.exp (1 / (6 * c)) := h
      _ ≤ (6 / 5) * (12 / 11) := by gcongr
  rw [hC]
  have hE := Real.exp_pos (c * (hankelLocPhi ℓ ζ).re)
  calc ‖(1 - ζ) ^ (-(1 / 2 : ℂ))‖ * ‖Complex.exp (binetDiff c ζ)‖ * Real.exp (c * (hankelLocPhi ℓ ζ).re) *
        ‖hankelWt c f ζ‖
      ≤ (10 / 9) * (10 / 9) * Real.exp (c * (hankelLocPhi ℓ ζ).re) * ((6 / 5) * (12 / 11)) := by gcongr
    _ ≤ 2 * Real.exp (c * (hankelLocPhi ℓ ζ).re) := by nlinarith

lemma hankel_density_arith {c σ : ℝ} (hc : 2 ≤ c) (hσ : 0 < σ) :
    2 * Real.sqrt (Real.pi / ((2 / 5) * c * σ)) +
      2 * (2 * Real.exp (-(0.035 * c * σ)) / (0.07 * c)) ≤ 200 * (Real.sqrt (c * σ))⁻¹ := by
  have hc0 : 0 < c := by linarith
  set X := Real.sqrt (c * σ) with hX
  have hx : 0 < c * σ := by positivity
  have hX0 : 0 < X := Real.sqrt_pos.2 hx
  have hXsq : X ^ 2 = c * σ := Real.sq_sqrt hx.le
  have h1 : Real.sqrt (Real.pi / ((2 / 5) * c * σ)) ≤ 3 / X := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have hpi : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
    have : Real.pi / ((2 / 5) * c * σ) = (5 / 2 * Real.pi) / X ^ 2 := by
      rw [hXsq]; field_simp
    rw [this, div_pow, div_le_div_iff_of_pos_right (by positivity)]
    nlinarith
  have h2 : Real.exp (-(0.035 * c * σ)) ≤ 5.6 / X := by
    have ht : 0 < 0.035 * c * σ := by positivity
    have h3 := hankel_exp_neg_le_inv_sqrt ht
    have h4 : 0.18 * X ≤ Real.sqrt (0.035 * c * σ) := by
      refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
      nlinarith
    have h5 : 0 < 0.18 * X := by positivity
    calc Real.exp (-(0.035 * c * σ)) ≤ (Real.sqrt (0.035 * c * σ))⁻¹ := h3
      _ ≤ (0.18 * X)⁻¹ := inv_anti₀ h5 h4
      _ ≤ 5.6 / X := by
        rw [mul_inv, div_eq_mul_inv]
        have : (0.18 : ℝ)⁻¹ ≤ 5.6 := by norm_num
        gcongr
  have h6 : 2 * (2 * Real.exp (-(0.035 * c * σ)) / (0.07 * c)) ≤ 2 * (2 * (5.6 / X) / 0.14) := by
    have : 2 * Real.exp (-(0.035 * c * σ)) / (0.07 * c) ≤ 2 * (5.6 / X) / 0.14 := by
      have hE : 0 ≤ 2 * Real.exp (-(0.035 * c * σ)) := by positivity
      calc 2 * Real.exp (-(0.035 * c * σ)) / (0.07 * c) ≤ 2 * Real.exp (-(0.035 * c * σ)) / 0.14 := by
            apply div_le_div_of_nonneg_left hE (by norm_num) (by linarith)
        _ ≤ 2 * (5.6 / X) / 0.14 := by gcongr
    linarith
  have h7 : 2 * (2 * (5.6 / X) / 0.14) = 160 / X := by field_simp; norm_num
  have h8 : 200 * X⁻¹ = 200 / X := by rw [div_eq_mul_inv]
  rw [h8]
  have h9 : 2 * (3 / X) = 6 / X := by ring
  have : 2 * Real.sqrt (Real.pi / ((2 / 5) * c * σ)) ≤ 6 / X := by linarith
  have h10 : 6 / X + 160 / X = 166 / X := by ring
  have h11 : 166 / X ≤ 200 / X := by gcongr; norm_num
  linarith

lemma hankel_abs_eq_third {τ : ℝ} (hτ : τ ^ 2 = 1 / 9) : |τ| ≤ 1 / 3 := by
  have h0 : (τ - 1 / 3) * (τ + 1 / 3) = 0 := by nlinarith
  rcases mul_eq_zero.1 h0 with h | h
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

/-- Phase on the horizontal connector `Im ζ = τ`, `τ² = 1/9`, below the peak value. -/
lemma hankelLocPhi_conn_total (ℓ : ℂ) (hl : ℓ.re ≤ 1 / 200) {c σ τ0 τ x : ℝ} (hσ0 : 0 < σ)
    (hσ : σ ≤ 0.035) (hτ0 : |τ0| ≤ 0.035)
    (hcrit : gSer etaC ((σ : ℂ) + (τ0 : ℂ) * Complex.I) + ℓ = 0) (hτ : τ ^ 2 = 1 / 9)
    (hx1 : σ ≤ x) (hx2 : x ≤ 0.1) :
    (hankelLocPhi ℓ ((x : ℂ) + (τ : ℂ) * Complex.I)).re ≤
      (hankelLocPhi ℓ ((σ : ℂ) + (τ0 : ℂ) * Complex.I)).re - 0.035 * σ - 0.07 * (x - σ) := by
  have hτa := hankel_abs_eq_third hτ
  have h1 := hankelLocPhi_conn_le ℓ hl hτ hσ0.le hx1 hx2
  have h2 := hankelLocPhi_vert_peak ℓ hσ0 (by linarith) (hτ0.trans (by norm_num)) hcrit τ
    ⟨(abs_le.1 hτa).1, (abs_le.1 hτa).2⟩
  have h3 : (0.0875 : ℝ) ≤ (τ - τ0) ^ 2 := by
    have ha := abs_le.1 hτa
    have hb := abs_le.1 hτ0
    nlinarith [mul_nonneg (sub_nonneg.2 ha.2) (by linarith [hb.2] : (0 : ℝ) ≤ 0.035 + τ0),
      mul_nonneg (by linarith [ha.1] : (0 : ℝ) ≤ 1 / 3 + τ) (by linarith [hb.2] : (0 : ℝ) ≤ 0.035 - τ0),
      sq_nonneg τ0]
  nlinarith

/-- **Local density bound** (`gt:7.7c` (c), before the chart): for normalised `f ∈ 𝒜_c^ε`, `c ≥ 2`, `Re ℓ ≤ 1/200` and
a root `ζ₊ = σ + iτ₀` of `g + ℓ` with `0 < σ ≤ 0.035`, `|τ₀| ≤ 0.035`, the local integral
`∫_{|τ|≤1/3} J(1/10 + iτ) dτ` is at most `200 (cσ)^{-1/2} e^{c Re Φ(ζ₊; ℓ)}` in norm (absolute constant). -/
theorem hankel_local_density_bound {c ε : ℝ} (hc : 2 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) (ℓ : ℂ) (hl : ℓ.re ≤ 1 / 200)
    {σ τ0 : ℝ} (hσ0 : 0 < σ) (hσ : σ ≤ 0.035) (hτ0 : |τ0| ≤ 0.035)
    (hcrit : gSer etaC ((σ : ℂ) + (τ0 : ℂ) * Complex.I) + ℓ = 0) :
    ‖∫ τ in (-(1 / 3 : ℝ))..(1 / 3), hankelJ c f ℓ (((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      200 * (Real.sqrt (c * σ))⁻¹ *
        Real.exp (c * (hankelLocPhi ℓ ((σ : ℂ) + (τ0 : ℂ) * Complex.I)).re) := by
  have hc0 : 0 < c := by linarith
  set P := Real.exp (c * (hankelLocPhi ℓ ((σ : ℂ) + (τ0 : ℂ) * Complex.I)).re) with hP
  have hP0 : 0 < P := Real.exp_pos _
  set F := hankelJ c f ℓ with hF
  set z : ℂ := (σ : ℂ) + ((-(1 / 3 : ℝ) : ℝ) : ℂ) * Complex.I with hz
  set w : ℂ := ((1 / 10 : ℝ) : ℂ) + ((1 / 3 : ℝ) : ℂ) * Complex.I with hw
  have hzre : z.re = σ := by simp [hz]
  have hzim : z.im = -(1 / 3) := by simp [hz]
  have hwre : w.re = 1 / 10 := by simp [hw]
  have hwim : w.im = 1 / 3 := by simp [hw]
  have hdiff : DifferentiableOn ℂ F (uIcc z.re w.re ×ℂ uIcc z.im w.im) := by
    refine (hankelJ_differentiableOn hc0 hf ℓ).mono ?_
    intro p hp
    obtain ⟨hpre, hpim⟩ := hp
    rw [hzre, hwre, uIcc_of_le (by linarith)] at hpre
    rw [hzim, hwim, uIcc_of_le (by norm_num)] at hpim
    have hpn : ‖p‖ < 1 := by
      have := norm_line_lt (σ := p.re) (τ := p.im)
        (by rw [abs_of_pos (by linarith [hpre.1])]; linarith [hpre.2])
        (abs_le.2 ⟨by linarith [hpim.1], hpim.2⟩)
      rwa [Complex.re_add_im] at this
    exact ⟨by linarith [hpre.1], by linarith [hpre.2], hpn⟩
  have hC := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z w hdiff
  simp only [hzre, hzim, hwre, hwim] at hC
  set Ar : ℂ := ∫ y : ℝ in (-(1 / 3 : ℝ))..(1 / 3), F (((1 / 10 : ℝ) : ℂ) + (y : ℂ) * Complex.I) with hAr
  set Al : ℂ := ∫ y : ℝ in (-(1 / 3 : ℝ))..(1 / 3), F ((σ : ℂ) + (y : ℂ) * Complex.I) with hAl
  set B : ℂ := ∫ x : ℝ in σ..(1 / 10), F ((x : ℂ) + ((-(1 / 3 : ℝ) : ℝ) : ℂ) * Complex.I) with hB
  set T : ℂ := ∫ x : ℝ in σ..(1 / 10), F ((x : ℂ) + ((1 / 3 : ℝ) : ℂ) * Complex.I) with hT
  have hrel : Ar = Al + Complex.I * (B - T) := by
    simp only [smul_eq_mul] at hC
    linear_combination (-Complex.I) * hC + (Ar - Al) * Complex.I_sq
  -- the vertical piece
  have hvert : ‖Al‖ ≤ 2 * P * Real.sqrt (Real.pi / ((2 / 5) * c * σ)) := by
    have hb0 : 0 < (2 / 5) * c * σ := by positivity
    have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := -(1 / 3 : ℝ)) (b := 1 / 3)
      (f := fun y : ℝ => F ((σ : ℂ) + (y : ℂ) * Complex.I))
      (g := fun y : ℝ => 2 * P * Real.exp (-((2 / 5) * c * σ) * (y - τ0) ^ 2)) (by norm_num)
      (Eventually.of_forall fun y hy => by
        have hy' : y ∈ Icc (-(1 / 3 : ℝ)) (1 / 3) := ⟨hy.1.le, hy.2⟩
        have h1 := norm_hankelJ_le hc hf hε hM ℓ (ζ := (σ : ℂ) + (y : ℂ) * Complex.I)
          (by simpa using hσ0) (by simp; linarith) (by simpa using abs_le.2 hy')
        have h2 := hankelLocPhi_vert_gauss ℓ hc0 hσ0 (by linarith) (hτ0.trans (by norm_num)) hcrit y hy'
        calc ‖F ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ _ := h1
          _ ≤ 2 * (P * Real.exp (-((2 / 5) * c * σ) * (y - τ0) ^ 2)) := by gcongr
          _ = _ := by ring)
      (by apply Continuous.intervalIntegrable; fun_prop)
    refine hle.trans ?_
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hankel_gauss_interval_le hb0 τ0) (by positivity)
  -- the connectors
  have hconn : ∀ τ : ℝ, τ ^ 2 = 1 / 9 →
      ‖∫ x : ℝ in σ..(1 / 10), F ((x : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        2 * P * Real.exp (-(0.035 * c * σ)) / (0.07 * c) := by
    intro τ hτ
    have hτa := hankel_abs_eq_third hτ
    have ha : 0 < 0.07 * c := by positivity
    have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := σ) (b := 1 / 10)
      (f := fun x : ℝ => F ((x : ℂ) + (τ : ℂ) * Complex.I))
      (g := fun x : ℝ => 2 * P * Real.exp (-(0.035 * c * σ)) * Real.exp (-(0.07 * c) * (x - σ)))
      (by linarith)
      (Eventually.of_forall fun x hx => by
        have h1 := norm_hankelJ_le hc hf hε hM ℓ (ζ := (x : ℂ) + (τ : ℂ) * Complex.I)
          (by simp; linarith [hx.1]) (by simp; linarith [hx.2]) (by simpa using hτa)
        have h2 := hankelLocPhi_conn_total ℓ hl (c := c) hσ0 hσ hτ0 hcrit hτ hx.1.le (by linarith [hx.2])
        have h3 : Real.exp (c * (hankelLocPhi ℓ ((x : ℂ) + (τ : ℂ) * Complex.I)).re) ≤
            P * (Real.exp (-(0.035 * c * σ)) * Real.exp (-(0.07 * c) * (x - σ))) := by
          rw [hP, ← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.2
          nlinarith
        calc ‖F ((x : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ _ := h1
          _ ≤ 2 * (P * (Real.exp (-(0.035 * c * σ)) * Real.exp (-(0.07 * c) * (x - σ)))) := by gcongr
          _ = _ := by ring)
      (by apply Continuous.intervalIntegrable; fun_prop)
    refine hle.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have := hankel_exp_interval_le ha (show σ ≤ 1 / 10 by linarith)
    calc 2 * P * Real.exp (-(0.035 * c * σ)) * ∫ x : ℝ in σ..(1 / 10), Real.exp (-(0.07 * c) * (x - σ))
        ≤ 2 * P * Real.exp (-(0.035 * c * σ)) * (1 / (0.07 * c)) := by gcongr
      _ = _ := by field_simp
  have hB' := hconn (-(1 / 3)) (by norm_num)
  have hT' := hconn (1 / 3) (by norm_num)
  have hnorm : ‖Ar‖ ≤ ‖Al‖ + ‖B‖ + ‖T‖ := by
    rw [hrel]
    calc ‖Al + Complex.I * (B - T)‖ ≤ ‖Al‖ + ‖Complex.I * (B - T)‖ := norm_add_le _ _
      _ ≤ ‖Al‖ + (‖B‖ + ‖T‖) := by
        rw [norm_mul, Complex.norm_I, one_mul]; gcongr; exact norm_sub_le _ _
      _ = _ := by ring
  have hfin := hankel_density_arith (c := c) (σ := σ) hc hσ0
  have hB'' : ‖B‖ ≤ 2 * P * Real.exp (-(0.035 * c * σ)) / (0.07 * c) := hB'
  have hT'' : ‖T‖ ≤ 2 * P * Real.exp (-(0.035 * c * σ)) / (0.07 * c) := hT'
  calc ‖Ar‖ ≤ ‖Al‖ + ‖B‖ + ‖T‖ := hnorm
    _ ≤ 2 * P * Real.sqrt (Real.pi / ((2 / 5) * c * σ)) +
        2 * P * Real.exp (-(0.035 * c * σ)) / (0.07 * c) +
        2 * P * Real.exp (-(0.035 * c * σ)) / (0.07 * c) := by
        gcongr
    _ = P * (2 * Real.sqrt (Real.pi / ((2 / 5) * c * σ)) +
        2 * (2 * Real.exp (-(0.035 * c * σ)) / (0.07 * c))) := by ring
    _ ≤ P * (200 * (Real.sqrt (c * σ))⁻¹) := by gcongr
    _ = _ := by ring

/-- info: 'FormalResearch.SignUncertainty.hankel_local_density_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_local_density_bound

end FormalResearch.SignUncertainty
