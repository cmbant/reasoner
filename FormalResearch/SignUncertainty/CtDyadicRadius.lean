module

public import Mathlib
public import FormalResearch.SignUncertainty.CtDyadicArea
public import FormalResearch.SignUncertainty.CtDyadicGReg
public import FormalResearch.SignUncertainty.CtDyadicRegime
public import FormalResearch.SignUncertainty.AiryEtaUnfold
public import FormalResearch.ModularBootstrap.FiveTerm.LowerGoodCircle
public import FormalResearch.ModularBootstrap.FiveTerm.LowerDyadic

/-!
# `ct:dyadic` (2): one good Airy radius with `η(R) ≤ C c^{-1/3}`

`constant_terms_lower.tex`, `ct:dyadic` (2) (since PR 298, unconditional): there is a good Airy radius
`R ∈ [c₁²c^{2/3}, 4c₁²c^{2/3}]` with `η(R) ≤ C c^{-1/3}`, for the concrete `η = ctEta` and good radii `ctGoodRadius`
(`CtDyadicEta`).  The proof of the paper (two Cauchy moments, an area bound, averaging over a positive-measure set of good
radii) is formalised here down to two named hypotheses about the concrete objects:

* `CtChartComplex c₁` (`CtDyadicEta`): the complex chart facts of `ct:cfu` / `ct:phic-exp`;
* `CtBandData c₁` (`CtDyadicGReg`): the two top-scale outputs of `ct:dyadic` (1) used by (2): `(ct:cov)` on the circle
  `|ũ'| = R_J` and the first `v`-moment of `(ct:half)` at `R_J`, for `A = √R_J`;

Proved from `CtBandData c₁` and the Type-(I) envelope (`CtDyadicGReg`, `ctGRegData_of_band`): the boundary inputs `CtGRegData c₁` of
the Cauchy-moment argument for `G_reg` (`ctGReg`) at `A = √R_J`: the arc mass `∫_0^π ‖G_reg(Ae^{iy})‖ A dy ≤ C/A` and the absolute
second moment `∫ t²‖G_reg(t)‖ dt ≤ C A`.  Proved here from these: the unfolding `ct_eta_transfer` (`CtEtaTransfer c₁`, from `CtChartComplex c₁` and the shared
`airy_eta_le_arcs` of `AiryEtaUnfold`: the two circle integrals of `η` bounded by the half-sector integrals of `G_reg` and
`G_reg ∘ w̃`, `ap:lemU` (a), (c) and the comparability `e(φ_c(u)) ≍ e(u)`), the Cauchy-moment area bound (`HalfDiscMoments`,
`CtDyadicArea`), the Markov selection on the set of good radii (Paper II's `lowerGoodSet`, of measure `≥ r₀/36`), and the
conclusion `ct_dyadic_radius`.
-/

@[expose] public section

open Complex MeasureTheory Set Metric intervalIntegral
open scoped Real ENNReal

namespace FormalResearch.SignUncertainty

open FormalResearch.HalfDiscCauchy FormalResearch.ModularBootstrap.FiveTerm

/-- **The unfolding of `η`** (`ap:lemU`, `ct:dyadic` Part (2), last paragraph; proved from `CtChartComplex c₁` in `ct_eta_transfer`): for `r ∈ [r₀, (3/2) r₀]`,
`r₀ = c₁c^{1/3}`, `η(r²) ≤ C_tr (∫_0^π r‖G_reg(re^{iφ})‖ dφ + ∫_0^π r‖G_reg(w̃(re^{iφ}))‖ dφ)`, where
`w̃(w) = w (φ_c(-w²)/(-w²))^{1/2}` is the `φ_c`-transported coordinate (`lowerGoodWtilde`) and the integrals are Lebesgue
integrals over `φ ∈ (0, π)` (in `[0, ∞]`). -/
def CtEtaTransfer (c₁ : ℝ) : Prop :=
  ∃ Ctr c₀ : ℝ, 0 ≤ Ctr ∧ ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ c : ℝ, c₀ ≤ c → ∀ f : ℝ → ℝ,
    IsHankelEigenfn c ε f → hankelMass c f = 1 → ∀ A : ℝ, 9 * (c₁ * c ^ (1 / 3 : ℝ)) ≤ A →
      A ^ 2 ≤ langerRadius c → ∀ r ∈ Icc (c₁ * c ^ (1 / 3 : ℝ)) (3 / 2 * (c₁ * c ^ (1 / 3 : ℝ))),
        ENNReal.ofReal (ctEta c₁ ε c f (r ^ 2)) ≤ ENNReal.ofReal Ctr *
          ((∫⁻ φ in Ioo (0 : ℝ) π, ENNReal.ofReal (r * ‖ctGReg A c f ((r : ℂ) * Complex.exp (φ * I))‖)) +
            ∫⁻ φ in Ioo (0 : ℝ) π, ENNReal.ofReal (r * ‖ctGReg A c f
              (lowerGoodWtilde (fun c' => ctPhiC c₁ ε c') c ((r : ℂ) * Complex.exp (φ * I)))‖))

/-- **Markov selection for `[0, ∞]`-valued functions** (no measurability of `H`): if `∫⁻_I H ≤ M`, `E ⊆ I` is measurable of
measure `≥ δ > 0`, some `r ∈ E` has `H r ≤ 2M/δ`. -/
lemma markov_lintegral {E I : Set ℝ} (hE : MeasurableSet E) (hEI : E ⊆ I) (H : ℝ → ℝ≥0∞) {M δ : ℝ}
    (hM : 0 < M) (hδ : 0 < δ) (hEδ : δ ≤ volume.real E) (hfin : volume E ≠ ⊤)
    (hint : ∫⁻ r in I, H r ≤ ENNReal.ofReal M) : ∃ r ∈ E, H r ≤ ENNReal.ofReal (2 * M / δ) := by
  by_contra hcon
  push Not at hcon
  have h1 : ∫⁻ _ in E, ENNReal.ofReal (2 * M / δ) ≤ ∫⁻ r in I, H r :=
    (setLIntegral_mono' hE fun r hr => (hcon r hr).le).trans (lintegral_mono_set hEI)
  rw [setLIntegral_const, ← ofReal_measureReal hfin] at h1
  have h2 : ENNReal.ofReal (2 * M / δ) * ENNReal.ofReal δ ≤
      ENNReal.ofReal (2 * M / δ) * ENNReal.ofReal (volume.real E) := by
    gcongr
  rw [← ENNReal.ofReal_mul (by positivity)] at h2
  have h3 := h2.trans (h1.trans hint)
  rw [ENNReal.ofReal_le_ofReal_iff hM.le] at h3
  have : 2 * M / δ * δ = 2 * M := by field_simp
  linarith

/-- Measurability in `r` of the arc integral `∫⁻_φ r‖G(ζ(re^{iφ}))‖` over the half-sector. -/
lemma ct_lint_aem {G ζ : ℂ → ℂ} {A r₀ : ℝ} (hGc : ContinuousOn G (closedBall (0 : ℂ) A))
    (hζc : ContinuousOn ζ {w : ℂ | r₀ / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r₀}) (hr₀ : 0 < r₀)
    (hζA : ∀ r ∈ Ioc r₀ (3 / 2 * r₀), ∀ φ ∈ Ioo (0 : ℝ) π,
      ζ ((r : ℂ) * Complex.exp (φ * I)) ∈ closedBall (0 : ℂ) A) :
    AEMeasurable (fun r : ℝ => ∫⁻ φ in Ioo (0 : ℝ) π,
        ENNReal.ofReal (r * ‖G (ζ ((r : ℂ) * Complex.exp (φ * I)))‖))
      (volume.restrict (Ioc r₀ (3 / 2 * r₀))) := by
  set P : Set (ℝ × ℝ) := (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π) with hP
  have hPm : MeasurableSet P := measurableSet_Ioc.prod measurableSet_Ioo
  have hcont : ContinuousOn (fun p : ℝ × ℝ => p.1 * ‖G (ζ ((p.1 : ℂ) * Complex.exp (p.2 * I)))‖) P := by
    refine continuousOn_fst.mul ?_
    refine ContinuousOn.norm ?_
    refine hGc.comp (g := G) (f := fun p : ℝ × ℝ => ζ ((p.1 : ℂ) * Complex.exp (p.2 * I))) ?_ ?_
    · refine hζc.comp (by fun_prop) fun p hp => ?_
      have hp1 : 0 < p.1 := by linarith [hp.1.1]
      refine ⟨?_, ?_⟩ <;>
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp1,
            Complex.norm_exp_ofReal_mul_I, mul_one]
          linarith [hp.1.1, hp.1.2]
    · exact fun p hp => hζA p.1 hp.1 p.2 hp.2
  have haem : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (p.1 * ‖G (ζ ((p.1 : ℂ) * Complex.exp (p.2 * I)))‖)) (volume.restrict P) :=
    (ENNReal.continuous_ofReal.comp_continuousOn hcont).aemeasurable hPm
  have h_vol : (volume : Measure (ℝ × ℝ)).restrict P =
      (volume.restrict (Ioc r₀ (3 / 2 * r₀))).prod (volume.restrict (Ioo (0 : ℝ) π)) := by
    rw [hP, Measure.volume_eq_prod, Measure.prod_restrict]
  rw [h_vol] at haem
  exact haem.lintegral_prod_right'

lemma norm_polar {r : ℝ} (hr : 0 < r) (φ : ℝ) : ‖(r : ℂ) * Complex.exp (φ * I)‖ = r := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Complex.norm_exp_ofReal_mul_I, mul_one]

lemma im_polar (r φ : ℝ) : ((r : ℂ) * Complex.exp (φ * I)).im = r * Real.sin φ := by
  rw [Complex.exp_mul_I]; simp [Complex.mul_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- The regime of `c` used in `ct_dyadic_radius`: `10 ≤ c₁c^{1/3}`, `C c^{-1/3} ≤ r₀²/256`, `C c^{-1} ≤ 1/4`. -/
lemma ct_regime {c₁ Cφ c : ℝ} (hc₁ : 0 < c₁) (hc1 : 1 ≤ c)
    (hc10 : (10 / c₁) ^ 3 ≤ c) (hcerr : 256 * Cφ / c₁ ^ 2 ≤ c) (hcder : 4 * Cφ ≤ c) :
    10 ≤ c₁ * c ^ (1 / 3 : ℝ) ∧
      Cφ * c ^ (-(1 / 3 : ℝ)) ≤ (c₁ * c ^ (1 / 3 : ℝ)) ^ 2 / 256 ∧ Cφ * c ^ (-1 : ℝ) ≤ 1 / 4 := by
  have hc_pos : 0 < c := by linarith
  set s : ℝ := c ^ (1 / 3 : ℝ) with hs
  have hs_pos : 0 < s := Real.rpow_pos_of_pos hc_pos _
  have hs3 : s ^ 3 = c := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hc_pos.le]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · have h1 : 10 / c₁ ≤ s := by
      by_contra h
      push Not at h
      have := pow_lt_pow_left₀ h hs_pos.le (by norm_num : (3 : ℕ) ≠ 0)
      rw [hs3] at this
      linarith
    calc (10 : ℝ) = c₁ * (10 / c₁) := by field_simp
      _ ≤ c₁ * s := by gcongr
  · rw [Real.rpow_neg hc_pos.le, ← hs]
    have h1 : 256 * Cφ ≤ c₁ ^ 2 * c := by
      rw [div_le_iff₀ (by positivity)] at hcerr
      linarith
    have h2 : (c₁ * s) ^ 2 / 256 - Cφ * s⁻¹ = (c₁ ^ 2 * s ^ 3 - 256 * Cφ) / (256 * s) := by
      field_simp
    rw [← sub_nonneg, h2, hs3]
    exact div_nonneg (by linarith) (by positivity)
  · rw [Real.rpow_neg_one]
    rw [← div_eq_mul_inv, div_le_iff₀ hc_pos]
    linarith

/-- `∫⁻` over `(0, π)` of the `ofReal` of a continuous nonnegative function is `ofReal` of its interval integral. -/
lemma ofReal_integral_eq_lintegral_Ioo {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 π)) (h0 : ∀ φ, 0 ≤ g φ) :
    ENNReal.ofReal (∫ φ in (0 : ℝ)..π, g φ) = ∫⁻ φ in Ioo (0 : ℝ) π, ENNReal.ofReal (g φ) := by
  rw [intervalIntegral.integral_of_le Real.pi_pos.le,
    ofReal_integral_eq_lintegral_ofReal ((hg.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
      (Filter.Eventually.of_forall h0)]
  exact (setLIntegral_congr Ioo_ae_eq_Ioc).symm

/-- **The unfolding of `η`** (`ap:lemU`, `ct:dyadic` Part (2), last paragraph), proved from the complex chart facts: `CtChartComplex c₁`
implies `CtEtaTransfer c₁` (`c₁ > 0`).  It is the instance `Ψ̃ = hankelPsi c f`, `B = langerRadius c` of the shared
`airy_eta_le_arcs` (`AiryEtaUnfold`), with `C_tr = 16 e^{5 c₁ C_φ}`; the integrals over `(0, π)` are `ofReal` of the interval integrals
since the arc integrands are continuous. -/
theorem ct_eta_transfer {c₁ : ℝ} (hc₁ : 0 < c₁) (hch : CtChartComplex c₁) : CtEtaTransfer c₁ := by
  obtain ⟨Cφ, cch, hCφ, hch'⟩ := hch
  refine ⟨16 * Real.exp (5 * c₁ * Cφ), max 1 (max cch (max ((10 / c₁) ^ 3)
    (max (256 * Cφ / c₁ ^ 2) (4 * Cφ)))), by positivity, ?_⟩
  intro ε hε c hc f hfe hmass A hA9 hAR r hr
  simp only [max_le_iff] at hc
  obtain ⟨hc1, hcch, hc10, hcerr, hcder⟩ := hc
  have hc_pos : 0 < c := by linarith
  obtain ⟨hr₀10, h_err, h_der⟩ := ct_regime hc₁ hc1 hc10 hcerr hcder
  obtain ⟨hex, hdom, him, hcl⟩ := hch' ε hε c hcch
  have hρ : ∃ ρ : ℝ, lowerRmax c₁ c < ρ ∧ DifferentiableOn ℂ ((fun c' => ctPhiC c₁ ε c') c) (ball 0 ρ) :=
    (ctPhiC_spec hex).1
  have hΨ : ContinuousOn (hankelPsi c f) (closedBall (0 : ℂ) (langerRadius c)) := by
    rw [langerRadius_eq]; exact (analyticOnNhd_hankelPsi hc_pos hfe).continuousOn
  obtain ⟨h1', h2', hbd'⟩ := airy_eta_le_arcs (c1 := c₁) (c := c) (Cφ := Cφ) (r₀ := c₁ * c ^ (1 / 3 : ℝ)) (A := A)
    (B := langerRadius c) (phi := fun c' => ctPhiC c₁ ε c') (Ψ := hankelPsi c f) hr₀10 hCφ h_err h_der hc_pos rfl hA9 hAR hΨ hρ
    him hcl (C_env := 5 * c₁ * Cφ) rfl r hr
  have h1 : ContinuousOn (fun φ : ℝ => r * ‖ctGReg A c f ((r : ℂ) * Complex.exp (φ * I))‖) (Icc 0 π) := h1'
  have h2 : ContinuousOn (fun φ : ℝ => r * ‖ctGReg A c f
      (lowerGoodWtilde (fun c' => ctPhiC c₁ ε c') c ((r : ℂ) * Complex.exp (φ * I)))‖) (Icc 0 π) := h2'
  have hbd : ctEta c₁ ε c f (r ^ 2) ≤
      2 * (2 * (∫ φ in (0 : ℝ)..π, r * ‖ctGReg A c f ((r : ℂ) * Complex.exp (φ * I))‖) +
        8 * Real.exp (5 * c₁ * Cφ) * (∫ φ in (0 : ℝ)..π, r * ‖ctGReg A c f
          (lowerGoodWtilde (fun c' => ctPhiC c₁ ε c') c ((r : ℂ) * Complex.exp (φ * I)))‖)) := hbd'
  have hr0 : 0 < r := by
    have : 0 < c₁ * c ^ (1 / 3 : ℝ) := by positivity
    linarith [hr.1]
  have hI1 := ofReal_integral_eq_lintegral_Ioo h1 fun φ => mul_nonneg hr0.le (norm_nonneg _)
  have hI2 := ofReal_integral_eq_lintegral_Ioo h2 fun φ => mul_nonneg hr0.le (norm_nonneg _)
  have hnn1 : 0 ≤ ∫ φ in (0 : ℝ)..π, r * ‖ctGReg A c f ((r : ℂ) * Complex.exp (φ * I))‖ :=
    intervalIntegral.integral_nonneg Real.pi_pos.le fun φ _ => mul_nonneg hr0.le (norm_nonneg _)
  have hnn2 : 0 ≤ ∫ φ in (0 : ℝ)..π, r * ‖ctGReg A c f
      (lowerGoodWtilde (fun c' => ctPhiC c₁ ε c') c ((r : ℂ) * Complex.exp (φ * I)))‖ :=
    intervalIntegral.integral_nonneg Real.pi_pos.le fun φ _ => mul_nonneg hr0.le (norm_nonneg _)
  have hexp : 1 ≤ Real.exp (5 * c₁ * Cφ) := Real.one_le_exp (by positivity)
  have hη : ctEta c₁ ε c f (r ^ 2) ≤ 16 * Real.exp (5 * c₁ * Cφ) *
      ((∫ φ in (0 : ℝ)..π, r * ‖ctGReg A c f ((r : ℂ) * Complex.exp (φ * I))‖) +
        ∫ φ in (0 : ℝ)..π, r * ‖ctGReg A c f
          (lowerGoodWtilde (fun c' => ctPhiC c₁ ε c') c ((r : ℂ) * Complex.exp (φ * I)))‖) := by
    refine hbd.trans ?_
    nlinarith only [hnn1, hnn2, mul_nonneg (sub_nonneg.2 hexp) hnn1]
  calc ENNReal.ofReal (ctEta c₁ ε c f (r ^ 2)) ≤ ENNReal.ofReal (16 * Real.exp (5 * c₁ * Cφ) * _) :=
        ENNReal.ofReal_le_ofReal hη
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add hnn1 hnn2, hI1, hI2]

/-- info: 'FormalResearch.SignUncertainty.ct_eta_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.ct_eta_transfer

/-- **`ct:dyadic` (2)**, for the concrete `η = ctEta` and good radii `ctGoodRadius`: for `c ≥ c₀`, `ε = ±1` and every feasible `f` with
`M[f] = 1` and `ũ₁ > φ_c(a₁)`, there is a good Airy radius `R ∈ [c₁²c^{2/3}, 4c₁²c^{2/3}]` with `η(R) ≤ C c^{-1/3}`
(`C, c₀` independent of `c`, `ε`, `f`, `T`).  Conditional on the two named hypotheses `CtChartComplex c₁`, `CtBandData c₁`
(see the module docstring); the proof is `ctGRegData_of_band`, the Cauchy-moment area bound, Markov selection on Paper II's
positive-measure set of good radii, and the unfolding `ct_eta_transfer`. -/
theorem ct_dyadic_radius {c₁ : ℝ} (hc₁ : 0 < c₁) (hch : CtChartComplex c₁) (hband : CtBandData c₁) :
    ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 → 0 < ctGap ε c T →
        ∃ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) ∧ ctGoodRadius R ∧
          ctEta c₁ ε c f R ≤ C * c ^ (-(1 / 3) : ℝ) := by
  obtain ⟨Ctr, ctr, hCtr, htr'⟩ := ct_eta_transfer hc₁ hch
  obtain ⟨Cφ, cch, hCφ, hch'⟩ := hch
  obtain ⟨CSig, CS, cG, hCSig, hCS, hG'⟩ := ctGRegData_of_band hc₁ hband
  set Bκ : ℝ := Real.sqrt (langerKappa * 4.94e-4) with hBκ
  set Minf : ℝ := 14 * CSig + 612 * CS * Bκ / c₁ + 1 with hMinf
  have hBκ0 : 0 ≤ Bκ := Real.sqrt_nonneg _
  have hMinf_pos : 0 < Minf := by rw [hMinf]; positivity
  refine ⟨Ctr * (72 * Minf) / c₁, max 1 (max cch (max cG (max ctr (max ((10 / c₁) ^ 3)
    (max (256 * Cφ / c₁ ^ 2) (4 * Cφ)))))), ?_⟩
  intro c hc ε hε T f hf hmass hgap
  simp only [max_le_iff] at hc
  obtain ⟨hc1, hcch, hcG, hctr, hc10, hcerr, hcder⟩ := hc
  have hc_pos : 0 < c := by linarith
  have hfe := hf.toIsHankelEigenfn
  obtain ⟨hr₀10, h_err, h_der⟩ := ct_regime hc₁ hc1 hc10 hcerr hcder
  set s : ℝ := c ^ (1 / 3 : ℝ) with hs
  have hs_pos : 0 < s := Real.rpow_pos_of_pos hc_pos _
  set r₀ : ℝ := c₁ * s with hr₀def
  have hr₀_pos : 0 < r₀ := by positivity
  have hr0sq : r₀ ^ 2 = c₁ ^ 2 * c ^ (2 / 3 : ℝ) := by
    rw [hr₀def, hs, mul_pow, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_pos.le]
    norm_num
  -- the chart
  obtain ⟨hex, hdom, him, hcl⟩ := hch' ε hε c hcch
  have hρ : ∃ ρ : ℝ, lowerRmax c₁ c < ρ ∧ DifferentiableOn ℂ ((fun c' => ctPhiC c₁ ε c') c) (ball 0 ρ) :=
    (ctPhiC_spec hex).1
  have him' : ∀ x : ℝ, |x| ≤ lowerRmax c₁ c → ((fun c' => ctPhiC c₁ ε c') c (x : ℂ)).im = 0 := him
  have hcl' : ∀ u : ℂ, ‖u‖ ≤ lowerRmax c₁ c →
      ‖(fun c' => ctPhiC c₁ ε c') c u - u‖ ≤ Cφ * c ^ (-(1 / 3 : ℝ)) ∧
        ‖deriv ((fun c' => ctPhiC c₁ ε c') c) u - 1‖ ≤ Cφ * c ^ (-1 : ℝ) := hcl
  have h_err' : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ r₀ ^ 2 / 256 := h_err
  -- the boundary data
  obtain ⟨A, hA9, hAR, hSig, hS2⟩ := hG' ε hε c hcG T f hf hmass hgap
  have hA9' : 9 * r₀ ≤ A := hA9
  have hA : 0 < A := by linarith
  have hGan := ctGReg_analytic hc_pos hfe hA hAR
  have hGc : ContinuousOn (ctGReg A c f) (closedBall (0 : ℂ) A) := hGan.continuousOn
  have hGc' : ContinuousOn (ctGReg A c f) (closedHalfDisc A) :=
    hGc.mono fun z hz => mem_closedBall_zero_iff.mpr hz.1
  have hGd : DifferentiableOn ℂ (ctGReg A c f) (openHalfDisc A) :=
    hGan.differentiableOn.mono fun z hz => mem_closedBall_zero_iff.mpr hz.1.le
  -- area for ζ = id
  have hζid : ∀ r ∈ Ioc r₀ (3 / 2 * r₀), ∀ φ ∈ Ioo (0 : ℝ) π,
      (fun w : ℂ => w) ((r : ℂ) * Complex.exp (φ * I)) ∈ openHalfDisc A ∧
        r₀ / 4 ≤ ‖(fun w : ℂ => w) ((r : ℂ) * Complex.exp (φ * I))‖ ∧
          ‖(fun w : ℂ => w) ((r : ℂ) * Complex.exp (φ * I))‖ ≤ A / 4 := by
    intro r hr φ hφ
    have hr0 : 0 < r := by linarith [hr.1]
    have hn := norm_polar hr0 φ
    have him0 : 0 < ((r : ℂ) * Complex.exp (φ * I)).im := by
      rw [im_polar]; exact mul_pos hr0 (Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2)
    simp only [hn]
    refine ⟨⟨by linarith [hr.2], him0⟩, by linarith [hr.1], by linarith [hr.2]⟩
  have harea1 := ct_area_of_zeta (G := ctGReg A c f) (K := 9 * π / 2) (CSig := CSig) (CS := CS)
    hr₀_pos hA9' (by positivity) hGc' hGd hSig hS2 (fun w => w) continuousOn_id hζid
    (fun t _ => ct_inv_norm_area_id hr₀_pos t)
  -- area for ζ = w̃
  obtain ⟨h_main, h_im, _, _, _, _⟩ :=
    lowerGood_wtilde_props hr₀10 hCφ h_err' h_der hρ him' hcl' hr₀def hc_pos
  have hwt_cont := lowerGood_wtilde_continuousOn hr₀10 h_err' hcl' hρ hr₀def hc_pos
  have hζwt : ∀ r ∈ Ioc r₀ (3 / 2 * r₀), ∀ φ ∈ Ioo (0 : ℝ) π,
      lowerGoodWtilde (fun c' => ctPhiC c₁ ε c') c ((r : ℂ) * Complex.exp (φ * I)) ∈ openHalfDisc A ∧
        r₀ / 4 ≤ ‖lowerGoodWtilde (fun c' => ctPhiC c₁ ε c') c ((r : ℂ) * Complex.exp (φ * I))‖ ∧
          ‖lowerGoodWtilde (fun c' => ctPhiC c₁ ε c') c ((r : ℂ) * Complex.exp (φ * I))‖ ≤ A / 4 := by
    intro r hr φ hφ
    have hr0 : 0 < r := by linarith [hr.1]
    have hn := norm_polar hr0 φ
    have him0 : 0 < ((r : ℂ) * Complex.exp (φ * I)).im := by
      rw [im_polar]; exact mul_pos hr0 (Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2)
    have hm := (h_main ((r : ℂ) * Complex.exp (φ * I)) (by rw [hn]; linarith [hr.1])
      (by rw [hn]; linarith [hr.2]))
    have him1 := h_im ((r : ℂ) * Complex.exp (φ * I)) (by rw [hn]; exact hr.1.le)
      (by rw [hn]; exact hr.2) him0
    exact ⟨⟨by linarith [hm.2.2.2.1], him1⟩, hm.2.2.2.2, by linarith [hm.2.2.2.1]⟩
  have harea2 := ct_area_of_zeta (G := ctGReg A c f) (K := 72 * π) (CSig := CSig) (CS := CS)
    hr₀_pos hA9' (by positivity) hGc' hGd hSig hS2
    (lowerGoodWtilde (fun c' => ctPhiC c₁ ε c') c) hwt_cont hζwt
    (fun t _ => lowerGood_wtilde_inv_norm_area_le hr₀10 hCφ h_err' h_der hρ him' hcl' hr₀def hc_pos t)
  -- measurability and the sum of the two area integrals
  set lint1 : ℝ → ℝ≥0∞ := fun r => ∫⁻ φ in Ioo (0 : ℝ) π,
    ENNReal.ofReal (r * ‖ctGReg A c f ((r : ℂ) * Complex.exp (φ * I))‖) with hl1
  set lint2 : ℝ → ℝ≥0∞ := fun r => ∫⁻ φ in Ioo (0 : ℝ) π, ENNReal.ofReal (r * ‖ctGReg A c f
    (lowerGoodWtilde (fun c' => ctPhiC c₁ ε c') c ((r : ℂ) * Complex.exp (φ * I)))‖) with hl2
  have haem1 : AEMeasurable lint1 (volume.restrict (Ioc r₀ (3 / 2 * r₀))) :=
    ct_lint_aem (ζ := fun w => w) hGc continuousOn_id hr₀_pos fun r hr φ hφ => by
      have hr0 : 0 < r := by linarith [hr.1]
      rw [mem_closedBall_zero_iff]
      show ‖(r : ℂ) * Complex.exp (φ * I)‖ ≤ A
      rw [norm_polar hr0]; linarith [hr.2]
  have hint : ∫⁻ r in Ioc r₀ (3 / 2 * r₀), (lint1 r + lint2 r) ≤
      ENNReal.ofReal ((7 * CSig + 8 * (9 * π / 2) * CS * A / (π * r₀)) +
        (7 * CSig + 8 * (72 * π) * CS * A / (π * r₀))) := by
    rw [lintegral_add_left' haem1, ENNReal.ofReal_add (by positivity) (by positivity)]
    exact add_le_add harea1 harea2
  -- the constant
  have hs2 : s ^ 2 = c ^ (2 / 3 : ℝ) := by
    rw [hs, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_pos.le]; norm_num
  have hAs : A ≤ s * Bκ := by
    have h1 : (A / s) ^ 2 ≤ langerKappa * 4.94e-4 := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      calc A ^ 2 ≤ langerRadius c := hAR
        _ = s ^ 2 * (langerKappa * 4.94e-4) := by rw [langerRadius_eq, hs2]; ring
        _ = _ := by ring
    have h2 : A / s ≤ Bκ := (le_abs_self _).trans (Real.abs_le_sqrt h1)
    rwa [div_le_iff₀ hs_pos, mul_comm] at h2
  have hMsum : (7 * CSig + 8 * (9 * π / 2) * CS * A / (π * r₀)) +
      (7 * CSig + 8 * (72 * π) * CS * A / (π * r₀)) ≤ Minf := by
    have e : (7 * CSig + 8 * (9 * π / 2) * CS * A / (π * r₀)) +
        (7 * CSig + 8 * (72 * π) * CS * A / (π * r₀)) = 14 * CSig + 612 * (CS * A / r₀) := by
      field_simp
      ring
    have h3 : CS * A / r₀ ≤ CS * Bκ / c₁ := by
      rw [div_le_div_iff₀ hr₀_pos hc₁, hr₀def]
      have : A * c₁ ≤ s * Bκ * c₁ := mul_le_mul_of_nonneg_right hAs hc₁.le
      nlinarith [mul_le_mul_of_nonneg_left this hCS]
    rw [e, hMinf]
    have : 612 * (CS * Bκ / c₁) = 612 * CS * Bκ / c₁ := by ring
    linarith
  have hintIcc : ∫⁻ r in Icc r₀ (3 / 2 * r₀), (lint1 r + lint2 r) ≤ ENNReal.ofReal Minf := by
    rw [← setLIntegral_congr Ioc_ae_eq_Icc]
    exact hint.trans (ENNReal.ofReal_le_ofReal hMsum)
  -- Markov selection on the set of good radii
  obtain ⟨r, hrE, hrH⟩ := markov_lintegral (lowerGoodSet_measurable r₀) (fun r hr => hr.1)
    (fun r => lint1 r + lint2 r) hMinf_pos (by positivity : 0 < r₀ / 36) (lowerGoodSet_measure hr₀10)
    (lowerGoodSet_finite_measure r₀) hintIcc
  obtain ⟨hr_Icc, m, hm⟩ := hrE
  have hr_pos : 0 < r := by linarith [hr_Icc.1]
  have hη := htr' ε hε c hctr f hfe hmass A hA9 hAR r hr_Icc
  have hη2 : ENNReal.ofReal (ctEta c₁ ε c f (r ^ 2)) ≤
      ENNReal.ofReal (Ctr * (2 * Minf / (r₀ / 36))) := by
    refine hη.trans ?_
    rw [ENNReal.ofReal_mul hCtr]
    gcongr
  have hη3 : ctEta c₁ ε c f (r ^ 2) ≤ Ctr * (2 * Minf / (r₀ / 36)) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hη2
  refine ⟨r ^ 2, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [← hr0sq]; exact pow_le_pow_left₀ hr₀_pos.le hr_Icc.1 2
  · have : r ^ 2 ≤ (3 / 2 * r₀) ^ 2 := pow_le_pow_left₀ hr_pos.le hr_Icc.2 2
    rw [show 4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ) = 4 * r₀ ^ 2 by rw [hr0sq]; ring]
    nlinarith only [this, hr₀_pos]
  · obtain ⟨N, hN⟩ := lowerGood_circle_of_phase (by linarith [hr_Icc.1]) m hm
    exact hN.1
  · refine hη3.trans (le_of_eq ?_)
    rw [Real.rpow_neg hc_pos.le, ← hs, hr₀def]
    field_simp
    ring

/-- info: 'FormalResearch.SignUncertainty.ct_dyadic_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.ct_dyadic_radius

end FormalResearch.SignUncertainty
