module

public import FormalResearch.ModularBootstrap.Spin.SpinS4Statements
public import FormalResearch.ModularBootstrap.Spin.SpinS1
public import FormalResearch.ModularBootstrap.Spin.SpinS1c
public import FormalResearch.ModularBootstrap.Spin.SpinS2xS24
public import FormalResearch.ModularBootstrap.Duality.ConstrainedThreshold
public import FormalResearch.ModularBootstrap.Spin.SpinS4_2_1
public import FormalResearch.ModularBootstrap.Spin.SpinS4_2_2
public import FormalResearch.ModularBootstrap.Spin.SpinS4_2_3
public import FormalResearch.ModularBootstrap.Spin.SpinS4_2_4
public import FormalResearch.ModularBootstrap.Spin.SpinS4_3_3
public import FormalResearch.ModularBootstrap.Spin.SpinS4_3_4
public import FormalResearch.ModularBootstrap.Spin.SpinS4_4_1
public import FormalResearch.ModularBootstrap.Spin.SpinS4_4_2
public import FormalResearch.ModularBootstrap.Spin.SpinS4_4_3
public import FormalResearch.ModularBootstrap.Spin.SpinS4_5_1
public import FormalResearch.ModularBootstrap.Spin.SpinS4_5_2
public import FormalResearch.ModularBootstrap.Spin.SpinS4_6_1

/-!
# SPIN-S4 Assembly (`s4:4.4` and `s4:S4` modulo the intermediate `s4:*` `Prop`s)

Assembles:
- `spinS4_4_4_of_props : SpinS4_4_3 → SpinS4_5_1 → SpinS4_5_2 → SpinS4_6_1 → SpinS4_4_4`
  (Corollary 6.2 of `spinning_s4.tex`, combining `s4:6.1`, `spinS1c`, and `spinS3`);
- `spinS4_of_props : SpinS4_2_1 → SpinS4_2_2 → SpinS4_2_3 → SpinS4_2_4 → SpinS4_3_3 →
    SpinS4_3_4 → SpinS4_4_1 → SpinS4_4_2 → SpinS4_4_3 → SpinS4_5_1 → SpinS4_5_2 →
    SpinS4_6_1 → SpinS4_4_4 → SpinS4`
  (Theorem S4 of `spinning_s4.tex`, combining `s4:6.1`, `s4:4.4`, `spinS4_consequences_of_S3`,
  `spinS1e`, `spinS24`, `spinDLP`, `spinDSD`, and 1D/2D analytic continuation on `spinStrip (1/2)²`
  for the wider-cone extension `{t_L, t_R ≥ -η a}`, `0 ≤ η < 1/2`).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.LP
open FormalResearch.ModularBootstrap.Duality
open FormalResearch.ModularBootstrap.FixedWeight
open FormalResearch.Special

/-! ### Section 1: Corollary 6.2 (`s4:4.4`) assembly -/

/-- **Corollary 6.2 (`s4:4.4`)** assembled from `SpinS4_4_3`, `SpinS4_5_1`, `SpinS4_5_2`,
`SpinS4_6_1`, together with the unconditional `spinS1c` and `spinS3`. -/
theorem spinS4_4_4_of_props
    (_h43 : SpinS4_4_3) (_h51 : SpinS4_5_1) (_h52 : SpinS4_5_2) (h61 : SpinS4_6_1) :
    SpinS4_4_4 := by
  obtain ⟨C_minus, c₁_61, hCm_pos, hc₁_40, h61_main⟩ := h61
  obtain ⟨_C_lo, C_plus, c₀_S3, _hClo, hCp_pos, hc₀_40, hS3_main⟩ := spinS3
  refine ⟨C_minus, C_plus, max c₁_61 (max 40 c₀_S3), hCm_pos, hCp_pos,
    (le_max_left _ _).trans (le_max_right _ _), fun {c} hc => ?_⟩
  have hc_61 : c₁_61 ≤ c := (le_max_left _ _).trans hc
  have hc_40 : 40 ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hc_S3 : c₀_S3 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  obtain ⟨_, _, hlo⟩ := h61_main hc_61
  obtain ⟨_, hL_spin, hspin_vir⟩ := spinS1c hc_40
  obtain ⟨_, _, _, hvir_hi⟩ := hS3_main hc_S3
  refine ⟨hlo, hL_spin, hspin_vir, hvir_hi⟩

/-! ### Section 2: `spinEvalWider` agreement on `liouvilleCone` and odd-Laguerre tests -/

private lemma spinStrip_isOpen (θ : ℝ) : IsOpen (spinStrip θ) := by
  unfold spinStrip
  exact isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

private lemma spinStrip_isPreconnected (θ : ℝ) : IsPreconnected (spinStrip θ) := by
  have heq : spinStrip θ = {b : ℂ | -θ < b.im} ∩ {b : ℂ | b.im < θ} := by
    ext b; simp [spinStrip, abs_lt]
  rw [heq]
  exact ((convex_halfSpace_im_gt (-θ)).inter (convex_halfSpace_im_lt θ)).isPreconnected

private lemma spin_sep_holo_eq_on_strip {f g : ℂ → ℂ → ℂ}
    (hfL : ∀ bR ∈ spinStrip (1 / 2), DifferentiableOn ℂ (fun bL => f bL bR) (spinStrip (1 / 2)))
    (hfR : ∀ bL ∈ spinStrip (1 / 2), DifferentiableOn ℂ (fun bR => f bL bR) (spinStrip (1 / 2)))
    (hgL : ∀ bR ∈ spinStrip (1 / 2), DifferentiableOn ℂ (fun bL => g bL bR) (spinStrip (1 / 2)))
    (hgR : ∀ bL ∈ spinStrip (1 / 2), DifferentiableOn ℂ (fun bR => g bL bR) (spinStrip (1 / 2)))
    (hreal : ∀ xL xR : ℝ, f (xL : ℂ) (xR : ℂ) = g (xL : ℂ) (xR : ℂ)) :
    ∀ bL ∈ spinStrip (1 / 2), ∀ bR ∈ spinStrip (1 / 2), f bL bR = g bL bR := by
  have hO := spinStrip_isOpen (1 / 2)
  have hP := spinStrip_isPreconnected (1 / 2)
  have h0_mem : (0 : ℂ) ∈ spinStrip (1 / 2) := by simp [spinStrip]
  have hreal_mem : ∀ x : ℝ, (x : ℂ) ∈ spinStrip (1 / 2) := fun x => by simp [spinStrip]
  have htend : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun x hx => Complex.ofReal_ne_zero.mpr hx
  have hstepL : ∀ xR : ℝ, ∀ bL ∈ spinStrip (1 / 2), f bL (xR : ℂ) = g bL (xR : ℂ) := by
    intro xR bL hbL
    have han : AnalyticOnNhd ℂ (fun z => f z (xR : ℂ) - g z (xR : ℂ)) (spinStrip (1 / 2)) :=
      ((hfL (xR : ℂ) (hreal_mem xR)).sub (hgL (xR : ℂ) (hreal_mem xR))).analyticOnNhd hO
    have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z (xR : ℂ) - g z (xR : ℂ) = 0 := by
      refine htend.frequently (Filter.Eventually.frequently (eventually_nhdsWithin_of_forall fun x _ => ?_))
      rw [hreal x xR, sub_self]
    exact sub_eq_zero.mp (han.eqOn_zero_of_preconnected_of_frequently_eq_zero hP h0_mem hfreq hbL)
  intro bL hbL bR hbR
  have han : AnalyticOnNhd ℂ (fun z => f bL z - g bL z) (spinStrip (1 / 2)) :=
    ((hfR bL hbL).sub (hgR bL hbL)).analyticOnNhd hO
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f bL z - g bL z = 0 := by
    refine htend.frequently (Filter.Eventually.frequently (eventually_nhdsWithin_of_forall fun x _ => ?_))
    rw [hstepL x bL hbL, sub_self]
  exact sub_eq_zero.mp (han.eqOn_zero_of_preconnected_of_frequently_eq_zero hP h0_mem hfreq hbR)

private lemma complex_sqrt_ofReal_nonneg {r : ℝ} (hr : 0 ≤ r) :
    Complex.sqrt (r : ℂ) = ((Real.sqrt r : ℝ) : ℂ) := by
  rw [Complex.sqrt_eq_real_add_ite]
  have h1 : (‖(r : ℂ)‖ + (r : ℂ).re) / 2 = r := by
    simp [abs_of_nonneg hr]
  have h2 : (‖(r : ℂ)‖ - (r : ℂ).re) / 2 = 0 := by
    simp [abs_of_nonneg hr]
  rw [h1, h2]
  simp

private lemma complex_sqrt_ofReal_neg {r : ℝ} (hr : r < 0) :
    Complex.sqrt (r : ℂ) = Complex.I * ((Real.sqrt (-r) : ℝ) : ℂ) := by
  rw [Complex.sqrt_eq_real_add_ite]
  have h1 : (‖(r : ℂ)‖ + (r : ℂ).re) / 2 = 0 := by
    simp [abs_of_neg hr]
  have h2 : (‖(r : ℂ)‖ - (r : ℂ).re) / 2 = -r := by
    simp [abs_of_neg hr]; ring
  rw [h1, h2]
  simp; ring

private lemma complex_sqrt_ofReal_sq (r : ℝ) : (Complex.sqrt (r : ℂ)) ^ 2 = (r : ℂ) := by
  rcases lt_or_ge r 0 with hr | hr
  · rw [complex_sqrt_ofReal_neg hr, mul_pow, Complex.I_sq]
    have hsq : ((Real.sqrt (-r) : ℝ) : ℂ) ^ 2 = ((-r : ℝ) : ℂ) := by
      norm_cast; exact Real.sq_sqrt (by linarith)
    rw [hsq]; push_cast; ring
  · rw [complex_sqrt_ofReal_nonneg hr]
    norm_cast; exact Real.sq_sqrt hr

private lemma wider_b_mem_spinStrip {a η t : ℝ} (ha : 0 < a) (_hη0 : 0 ≤ η) (hη1 : η < 1 / 2)
    (ht : -(η * a) ≤ t) :
    Complex.sqrt (2 * (t : ℂ)) / (2 * (Real.sqrt a : ℂ)) ∈ spinStrip (1 / 2) := by
  change |(Complex.sqrt (2 * (t : ℂ)) / (2 * (Real.sqrt a : ℂ))).im| < 1 / 2
  by_cases htnn : 0 ≤ t
  · have h2t : 2 * (t : ℂ) = ((2 * t : ℝ) : ℂ) := by push_cast; rfl
    rw [h2t, complex_sqrt_ofReal_nonneg (by linarith)]
    have him : (((Real.sqrt (2 * t) : ℝ) : ℂ) / (2 * (Real.sqrt a : ℂ))).im = 0 := by
      have hdiv : ((Real.sqrt (2 * t) : ℝ) : ℂ) / (2 * (Real.sqrt a : ℂ)) =
          ((Real.sqrt (2 * t) / (2 * Real.sqrt a) : ℝ) : ℂ) := by push_cast; rfl
      rw [hdiv, Complex.ofReal_im]
    rw [him, abs_zero]; norm_num
  · have htlt : t < 0 := not_le.mp htnn
    have h2t : 2 * (t : ℂ) = ((2 * t : ℝ) : ℂ) := by push_cast; rfl
    rw [h2t, complex_sqrt_ofReal_neg (by linarith)]
    have h2t' : -(2 * t) = -2 * t := by ring
    rw [h2t']
    have hdiv : Complex.I * ((Real.sqrt (-2 * t) : ℝ) : ℂ) / (2 * (Real.sqrt a : ℂ)) =
        ((Real.sqrt (-2 * t) / (2 * Real.sqrt a) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hdiv]
    have him : (((Real.sqrt (-2 * t) / (2 * Real.sqrt a) : ℝ) : ℂ) * Complex.I).im =
        Real.sqrt (-2 * t) / (2 * Real.sqrt a) := by
      rw [Complex.mul_I_im, Complex.ofReal_re]
    rw [him, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (by positivity))]
    have hsqa : 0 < 2 * Real.sqrt a := by positivity
    rw [div_lt_iff₀ hsqa]
    have hlt_sq : -2 * t < a := by nlinarith
    have hsqrt_lt : Real.sqrt (-2 * t) < Real.sqrt a :=
      Real.sqrt_lt_sqrt (by linarith) hlt_sq
    linarith [Real.sqrt_pos.mpr ha]

private lemma spinEvalWider_eq_spinEvalT {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) {p : ℝ × ℝ} (hp1 : 0 ≤ p.1) (hp2 : 0 ≤ p.2) :
    spinEvalWider a Φ p = spinEvalT Φ p := by
  have hc25 : 25 ≤ 12 * a + 1 := by linarith
  have ha_pos : 0 < a := by linarith
  have hS24 := spinS24.1 hc25 (θ := 1 / 4) (by norm_num) (by norm_num)
  obtain ⟨_, _, hagree⟩ := hS24
  have hΦ_alg : SpinTestClass (((12 * a + 1) - 1) / 12) Φ := by
    simpa [show ((12 * a + 1) - 1) / 12 = a by ring] using hΦ
  have hreal_eq := (hagree hΦ_alg).2.2.2.2.1
  set xL : ℝ := Real.sqrt (2 * p.1) / (2 * Real.sqrt a)
  set xR : ℝ := Real.sqrt (2 * p.2) / (2 * Real.sqrt a)
  have hbL : Complex.sqrt (2 * (p.1 : ℂ)) / (2 * (Real.sqrt a : ℂ)) = (xL : ℂ) := by
    have h2 : 2 * (p.1 : ℂ) = ((2 * p.1 : ℝ) : ℂ) := by push_cast; rfl
    rw [h2, complex_sqrt_ofReal_nonneg (by linarith)]
    dsimp [xL]; push_cast; rfl
  have hbR : Complex.sqrt (2 * (p.2 : ℂ)) / (2 * (Real.sqrt a : ℂ)) = (xR : ℂ) := by
    have h2 : 2 * (p.2 : ℂ) = ((2 * p.2 : ℝ) : ℂ) := by push_cast; rfl
    rw [h2, complex_sqrt_ofReal_nonneg (by linarith)]
    dsimp [xR]; push_cast; rfl
  unfold spinEvalWider
  rw [hbL, hbR]
  have hgc := hreal_eq xL xR
  simp only [show ((12 * a + 1) - 1) / 12 = a by ring] at hgc
  rw [hgc, Complex.ofReal_re]
  unfold spinG spinEvalT
  have hsqa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha_pos).ne'
  have hxL : 2 * Real.sqrt a * xL = Real.sqrt (2 * p.1) := by
    dsimp [xL]; field_simp [hsqa]
  have hxR : 2 * Real.sqrt a * xR = Real.sqrt (2 * p.2) := by
    dsimp [xR]; field_simp [hsqa]
  rw [hxL, hxR]

private noncomputable def lagPsiC (w : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (-2 * π * z) * (Polynomial.map (algebraMap ℝ ℂ) (lagPoly w k)).eval (4 * π * z)

private lemma lagPsiC_differentiable (w : ℝ) (k : ℕ) : Differentiable ℂ (lagPsiC w k) := by
  unfold lagPsiC
  exact ((differentiable_id.const_mul (-2 * π : ℂ)).cexp).mul
    ((Polynomial.differentiable _).comp (differentiable_id.const_mul (4 * π : ℂ)))

private lemma lagPsiC_ofReal (w : ℝ) (k : ℕ) (t : ℝ) :
    lagPsiC w k (t : ℂ) = ((lagPsi w k t : ℝ) : ℂ) := by
  unfold lagPsiC lagPsi lagL
  have hexp : Complex.exp (-2 * (π : ℂ) * (t : ℂ)) = ((Real.exp (-2 * π * t) : ℝ) : ℂ) := by
    rw [show (-2 * (π : ℂ) * (t : ℂ)) = ((-2 * π * t : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_exp _).symm
  have hpoly : (Polynomial.map (algebraMap ℝ ℂ) (lagPoly w k)).eval (4 * (π : ℂ) * (t : ℂ)) =
      (((lagPoly w k).eval (4 * π * t) : ℝ) : ℂ) := by
    have h4 : 4 * (π : ℂ) * (t : ℂ) = (algebraMap ℝ ℂ) (4 * π * t) := by
      rw [Complex.coe_algebraMap]; push_cast; ring
    rw [h4, Polynomial.eval_map, Polynomial.eval₂_hom]
    rfl
  rw [hexp, hpoly, Complex.ofReal_mul]

private lemma spinEvalWider_oddLagPoly {a : ℝ} (ha : 2 ≤ a) {N : ℕ} {q : ℝ × ℝ → ℝ}
    (hq : q ∈ spinOddLagPolySpace N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1 / 2)
    {p : ℝ × ℝ} (hp : p ∈ spinConeB (η * a)) :
    spinEvalWider a (spinLiftTToR (fun r => Real.exp (-2 * π * (r.1 + r.2)) * q r)) p =
      Real.exp (-2 * π * (p.1 + p.2)) * q p := by
  have ha_pos : 0 < a := by linarith
  have hc25 : 25 ≤ 12 * a + 1 := by linarith
  have hS24 := spinS24.1 hc25 (θ := 1 / 4) (by norm_num) (by norm_num)
  obtain ⟨_, _, hagree⟩ := hS24
  have hΨ_cert : SpinCertifiedT a (fun r => Real.exp (-2 * π * (r.1 + r.2)) * q r) :=
    exp_mul_mem_SpinCertifiedT hq
  have hΦ_test : SpinTestClass a (spinLiftTToR (fun r => Real.exp (-2 * π * (r.1 + r.2)) * q r)) :=
    (spinLiftTToR_mem_SpinTestClassJ ha hΨ_cert).base
  have hΦ_alg : SpinTestClass (((12 * a + 1) - 1) / 12)
      (spinLiftTToR (fun r => Real.exp (-2 * π * (r.1 + r.2)) * q r)) := by
    simpa [show ((12 * a + 1) - 1) / 12 = a by ring] using hΦ_test
  have hhol := hagree hΦ_alg
  simp only [show ((12 * a + 1) - 1) / 12 = a by ring] at hhol
  -- Build a separately entire complex extension `ΨC` of `exp(-2π(t_L+t_R)) * q(t_L, t_R)`
  have hex_hol : ∃ ΨC : ℂ → ℂ → ℂ,
      (∀ z₂ : ℂ, Differentiable ℂ (fun z₁ => ΨC z₁ z₂)) ∧
      (∀ z₁ : ℂ, Differentiable ℂ (fun z₂ => ΨC z₁ z₂)) ∧
      (∀ tL tR : ℝ, ΨC (tL : ℂ) (tR : ℂ) =
        ((Real.exp (-2 * π * (tL + tR)) * q (tL, tR) : ℝ) : ℂ)) := by
    unfold spinOddLagPolySpace at hq
    refine Submodule.span_induction
      (p := fun q₀ _ => ∃ ΨC : ℂ → ℂ → ℂ,
        (∀ z₂ : ℂ, Differentiable ℂ (fun z₁ => ΨC z₁ z₂)) ∧
        (∀ z₁ : ℂ, Differentiable ℂ (fun z₂ => ΨC z₁ z₂)) ∧
        (∀ tL tR : ℝ, ΨC (tL : ℂ) (tR : ℂ) =
          ((Real.exp (-2 * π * (tL + tR)) * q₀ (tL, tR) : ℝ) : ℂ))) ?_ ?_ ?_ ?_ hq
    · rintro _ ⟨m, n, -, -, rfl⟩
      refine ⟨fun z₁ z₂ => (1 / 2 : ℂ) *
          (lagPsiC (1 / 2) m z₁ * lagPsiC (1 / 2) n z₂ +
            lagPsiC (1 / 2) m z₂ * lagPsiC (1 / 2) n z₁),
        fun z₂ => ?_, fun z₁ => ?_, fun tL tR => ?_⟩
      · exact ((((lagPsiC_differentiable _ _).mul_const _).add
          ((lagPsiC_differentiable _ _).const_mul _))).const_mul _
      · exact ((((lagPsiC_differentiable _ _).const_mul _).add
          ((lagPsiC_differentiable _ _).mul_const _))).const_mul _
      · dsimp only
        rw [lagPsiC_ofReal, lagPsiC_ofReal, lagPsiC_ofReal, lagPsiC_ofReal]
        unfold spinOddLagPolyBasis lagPsi
        have hexp : Real.exp (-2 * π * (tL + tR)) =
            Real.exp (-2 * π * tL) * Real.exp (-2 * π * tR) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [hexp]; push_cast; ring
    · refine ⟨fun _ _ => 0, fun _ => differentiable_const 0, fun _ => differentiable_const 0,
        fun _ _ => by simp⟩
    · rintro f g _ _ ⟨F, hFL, hFR, hFeq⟩ ⟨G, hGL, hGR, hGeq⟩
      refine ⟨fun z₁ z₂ => F z₁ z₂ + G z₁ z₂,
        fun z₂ => (hFL z₂).add (hGL z₂), fun z₁ => (hFR z₁).add (hGR z₁), fun tL tR => ?_⟩
      simp [hFeq, hGeq, mul_add]
    · rintro c f _ ⟨F, hFL, hFR, hFeq⟩
      refine ⟨fun z₁ z₂ => (c : ℂ) * F z₁ z₂,
        fun z₂ => (hFL z₂).const_mul _, fun z₁ => (hFR z₁).const_mul _, fun tL tR => ?_⟩
      simp [hFeq]; ring
  obtain ⟨ΨC, hΨL, hΨR, hΨeq⟩ := hex_hol
  have hcomp_eq : ∀ bL ∈ spinStrip (1 / 2), ∀ bR ∈ spinStrip (1 / 2),
      spinGC a (spinLiftTToR (fun r => Real.exp (-2 * π * (r.1 + r.2)) * q r)) bL bR =
        ΨC (2 * (a : ℂ) * bL ^ 2) (2 * (a : ℂ) * bR ^ 2) := by
    refine spin_sep_holo_eq_on_strip hhol.2.2.1 hhol.2.2.2.1
      (fun bR _ => ((hΨL _).comp ((differentiable_id.pow 2).const_mul _)).differentiableOn)
      (fun bL _ => ((hΨR _).comp ((differentiable_id.pow 2).const_mul _)).differentiableOn)
      fun xL xR => ?_
    rw [hhol.2.2.2.2.1 xL xR]
    have hxL : 2 * (a : ℂ) * (xL : ℂ) ^ 2 = ((2 * a * xL ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    have hxR : 2 * (a : ℂ) * (xR : ℂ) ^ 2 = ((2 * a * xR ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [hxL, hxR, hΨeq]
    unfold spinG spinLiftTToR
    congr 1
    have ht1 : (2 * Real.sqrt a * xL) ^ 2 / 2 = 2 * a * xL ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt ha_pos.le]; ring
    have ht2 : (2 * Real.sqrt a * xR) ^ 2 / 2 = 2 * a * xR ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt ha_pos.le]; ring
    rw [ht1, ht2]
  set bL : ℂ := Complex.sqrt (2 * (p.1 : ℂ)) / (2 * (Real.sqrt a : ℂ))
  set bR : ℂ := Complex.sqrt (2 * (p.2 : ℂ)) / (2 * (Real.sqrt a : ℂ))
  have hbL_mem : bL ∈ spinStrip (1 / 2) := wider_b_mem_spinStrip ha_pos hη0 hη1 hp.1
  have hbR_mem : bR ∈ spinStrip (1 / 2) := wider_b_mem_spinStrip ha_pos hη0 hη1 hp.2
  have hsqa_c : (Real.sqrt a : ℂ) ^ 2 = (a : ℂ) := by norm_cast; exact Real.sq_sqrt ha_pos.le
  have ha_ne_c : (a : ℂ) ≠ 0 := by exact_mod_cast ha_pos.ne'
  have h2a_bL : 2 * (a : ℂ) * bL ^ 2 = (p.1 : ℂ) := by
    dsimp [bL]
    have h2p1 : 2 * (p.1 : ℂ) = ((2 * p.1 : ℝ) : ℂ) := by push_cast; rfl
    rw [div_pow, h2p1, complex_sqrt_ofReal_sq, mul_pow, hsqa_c]
    push_cast
    field_simp [ha_ne_c]
  have h2a_bR : 2 * (a : ℂ) * bR ^ 2 = (p.2 : ℂ) := by
    dsimp [bR]
    have h2p2 : 2 * (p.2 : ℂ) = ((2 * p.2 : ℝ) : ℂ) := by push_cast; rfl
    rw [div_pow, h2p2, complex_sqrt_ofReal_sq, mul_pow, hsqa_c]
    push_cast
    field_simp [ha_ne_c]
  unfold spinEvalWider
  rw [hcomp_eq bL hbL_mem bR hbR_mem, h2a_bL, h2a_bR, hΨeq, Complex.ofReal_re]

/-! ### Section 3: Theorem S4 (`s4:S4`) assembly -/

/-- **Theorem S4 (`s4:S4`)** assembled from the section `s4:*` propositions together with
the already-proved `spinS1c`, `spinS1e`, `spinS3`, `spinS24`, `spinDLP`, `spinDSD`, and
`spinS4_consequences_of_S3`. -/
theorem spinS4_of_props
    (_h21 : SpinS4_2_1) (_h22 : SpinS4_2_2) (_h23 : SpinS4_2_3) (_h24 : SpinS4_2_4)
    (_h33 : SpinS4_3_3) (_h34 : SpinS4_3_4) (_h41 : SpinS4_4_1) (_h42 : SpinS4_4_2)
    (_h43 : SpinS4_4_3) (_h51 : SpinS4_5_1) (_h52 : SpinS4_5_2) (h61 : SpinS4_6_1)
    (h44 : SpinS4_4_4) :
    SpinS4 := by
  obtain ⟨C_minus_61, c₁_61, hCm61_pos, hc₁61_40, h61_main⟩ := h61
  obtain ⟨C_minus_44, C_plus_44, c₁_44, hCm44_pos, hCp44_pos, hc₁44_40, h44_main⟩ := h44
  obtain ⟨_, _, c₁_S3, _, _, hc₁S3_40, hcons⟩ := spinS4_consequences_of_S3 spinS3 spinS1e
  let C_minus : ℝ := max C_minus_61 C_minus_44
  let C_plus : ℝ := C_plus_44
  have hCm_pos : 0 < C_minus := lt_max_of_lt_left hCm61_pos
  have hxiBar_pos : 0 < xiBar := by unfold xiBar; have := xiStar_pos; positivity
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((isLittleO_log_id_atTop.tendsto_div_nhds_zero).eventually
      (gt_mem_nhds (div_pos hxiBar_pos hCm_pos)))
  let c₁ : ℝ := max (max c₁_61 c₁_44) (max (max c₁_S3 40) (N₀ + 2))
  have hc₁_40 : 40 ≤ c₁ := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  refine ⟨C_minus, C_plus, c₁, hCm_pos, hCp44_pos, hc₁_40, fun {c} hc => ?_⟩
  have hc_61 : c₁_61 ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hc_44 : c₁_44 ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hc_S3 : c₁_S3 ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans
    ((le_max_right _ _).trans hc)
  have hc_N0 : N₀ + 2 ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
  have hc_40 : 40 ≤ c := hc₁_40.trans hc
  set n : ℝ := c - 1
  set a : ℝ := n / 12
  have ha2 : 2 ≤ a := by dsimp [a, n]; linarith
  have ha_nn : 0 ≤ a := by linarith
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have h1_le_n : 1 ≤ n := by dsimp [n]; linarith
  have hlogn_nn : 0 ≤ Real.log n := Real.log_nonneg h1_le_n
  obtain ⟨_, hslack61, _⟩ := h61_main hc_61
  obtain ⟨hlo44, hL_spin, hspin_vir, hvir_hi⟩ := h44_main hc_44
  obtain ⟨hthr_pos, _, hL_eq_tau, hattain, _, _⟩ := hcons hc_S3
  have hCm61_le : C_minus_61 ≤ C_minus := le_max_left _ _
  have hCm44_le : C_minus_44 ≤ C_minus := le_max_right _ _
  have hTm_pos : 0 < xiBar * n + Aopt * n ^ ((1 : ℝ) / 3) - C_minus * Real.log n := by
    have hn_N0 : N₀ ≤ n := by dsimp [n]; linarith
    have hlog_div : Real.log n / n < xiBar / C_minus := hN₀ n hn_N0
    have hCm_log : C_minus * Real.log n < xiBar * n := by
      have h1 : C_minus * (Real.log n / n) < C_minus * (xiBar / C_minus) :=
        mul_lt_mul_of_pos_left hlog_div hCm_pos
      have hn_ne : n ≠ 0 := hn_pos.ne'
      have hCm_ne : C_minus ≠ 0 := hCm_pos.ne'
      calc C_minus * Real.log n = n * (C_minus * (Real.log n / n)) := by field_simp [hn_ne]
        _ < n * (C_minus * (xiBar / C_minus)) := mul_lt_mul_of_pos_left h1 hn_pos
        _ = xiBar * n := by field_simp [hCm_ne]
    have hAopt_nn : 0 ≤ Aopt * n ^ ((1 : ℝ) / 3) := by
      have hA : 0 ≤ Aopt := by unfold Aopt; exact mul_nonneg cStar_pos.le (abs_nonneg _)
      exact mul_nonneg hA (Real.rpow_nonneg hn_pos.le _)
    linarith
  have hlo : n / lambdaV + Aopt * n ^ ((1 : ℝ) / 3) - C_minus * Real.log n ≤ spinDeltaL c := by
    have h1 : C_minus_44 * Real.log n ≤ C_minus * Real.log n :=
      mul_le_mul_of_nonneg_right hCm44_le hlogn_nn
    linarith [hlo44]
  have hslack : ∀ {T : ℝ}, T < xiBar * n + Aopt * n ^ ((1 : ℝ) / 3) - C_minus * Real.log n →
      ∀ {Φ : ℝ × ℝ → ℝ}, ¬ SpinIsSlackFeasible a T Φ := by
    intro T hT Φ
    have h1 : C_minus_61 * Real.log n ≤ C_minus * Real.log n :=
      mul_le_mul_of_nonneg_right hCm61_le hlogn_nn
    exact hslack61 (by linarith)
  have hwider : ∀ {η : ℝ}, 0 ≤ η → η < 1 / 2 →
      spinDeltaL c ≤ a + spinWiderThr (SpinTestClass a) a η ∧
      spinDeltaSpin c ≤ a + spinWiderThr (SpinTestClassJ a) a η ∧
      a + spinWiderThr (SpinCertifiedClass a) a η ≤ virasoroProblem.Delta_best n := by
    intro η hη0 hη1
    let Ω₀ : Set (ℝ × ℝ) := spinConeB (η * a)
    have hΩ₀_slice : ∀ τ : ℝ, spinConeSlice Ω₀ τ = widerCone a η τ := fun τ => by
      ext p; simp [Ω₀, spinConeSlice, spinConeB, widerCone, and_assoc]
    have hcert_exists : ∀ {T : ℝ}, virasoroProblem.T_V (12 * a) < T → 0 < T →
        ∃ (N : ℕ) (q : ℝ × ℝ → ℝ), spinOddLagFeasible a N (widerCone a η T) q := by
      intro T hTV hTpos
      by_contra hno
      push Not at hno
      have hB : 0 ≤ η * a := mul_nonneg hη0 ha_nn
      have hXc : IsClosed (widerCone a η T) := by
        rw [← hΩ₀_slice]
        exact isClosed_spinConeSlice (isClosed_spinConeB _) T
      have hXs : IsSwapInvariantSet (widerCone a η T) := by
        rw [← hΩ₀_slice]
        exact isSwapInvariantSet_spinConeSlice (isSwapInvariantSet_spinConeB _) T
      have hXsub : widerCone a η T ⊆ spinConeB (η * a) ∩ {p : ℝ × ℝ | T ≤ p.1 + p.2} := by
        rw [← hΩ₀_slice]; exact Subset.rfl
      obtain ⟨meas, -⟩ := (spinDLPi ha2 hB hTpos hXc hXs hXsub).1 hno
      have hc_pos : (0 : ℝ) < 12 * a := by linarith
      have ha_shift : 12 * virasoroProblem.totalShift ≤ 12 * a := by
        rw [virasoroProblem_totalShift]; linarith
      obtain ⟨τ₁, hτ₁, g₁, hg₁⟩ := exists_feasible_of_compact virasoroProblem hc_pos ha_shift
        isCompact_empty (empty_subset _)
      have hne : (constrainedGaps virasoroProblem (12 * a) ∅).Nonempty := ⟨τ₁, hτ₁, g₁, hg₁⟩
      let meas_12 : SpinCrossingMeasureOn (12 * a / 12) (widerCone a η T) :=
        { ν := meas.ν
          supp := meas.supp
          finite_laplace := meas.finite_laplace
          crossing := fun hL hR => by
            rw [show 12 * a / 12 = a by ring]
            exact meas.crossing hL hR }
      let rmeas : AdmissibleCrossingMeasure virasoroProblem (12 * a / 12) :=
        meas_12.toRadAdmissible (fun _ hp => hTpos.le.trans (hXsub hp).2)
      have hrad_supp : rmeas.ν (∅ ∪ Ici T)ᶜ = 0 := by
        rw [empty_union, Set.compl_Ici]
        exact meas_12.toRadAdmissible_atGap hTpos.le (fun _ hp => (hXsub hp).2)
      have hle_thr : T ≤ constrainedThreshold virasoroProblem (12 * a) ∅ :=
        le_constrainedThreshold_of_crossingMeasure virasoroProblem hc_pos ha_shift hne rmeas hrad_supp
      rw [constrainedThreshold_empty] at hle_thr
      linarith
    have hcert_set_mem : ∀ {T : ℝ}, virasoroProblem.T_V (12 * a) < T → 0 < T →
        T ∈ {T' : ℝ | 0 < T' ∧ ∃ Φ, SpinCertifiedClass a Φ ∧ 0 < spinPhiVac a Φ ∧
          ∀ p ∈ widerCone a η T', 0 ≤ spinEvalWider a Φ p} := by
      intro T hTV hTpos
      obtain ⟨N, q, hq_mem, hq_nn, hq_vac⟩ := hcert_exists hTV hTpos
      let Ψ : ℝ × ℝ → ℝ := fun r => Real.exp (-2 * π * (r.1 + r.2)) * q r
      let Φ : ℝ × ℝ → ℝ := spinLiftTToR Ψ
      have hΨ_cert : SpinCertifiedT a Ψ := exp_mul_mem_SpinCertifiedT hq_mem
      have hΦ_cert : SpinCertifiedClass a Φ := by
        unfold Φ SpinCertifiedClass
        unfold SpinCertifiedT at hΨ_cert
        refine Submodule.span_induction (p := fun Ψ₀ _ => SpinCertifiedClass a (spinLiftTToR Ψ₀))
          ?_ ?_ ?_ ?_ hΨ_cert
        · rintro _ (⟨m, n₀, hmn, rfl⟩ | ⟨β₀, hβ₀0, hβ₀1, rfl⟩)
          · exact Submodule.subset_span (Or.inl ⟨m, n₀, hmn, rfl⟩)
          · have heq : spinLiftTToR (fun p : ℝ × ℝ => hMaj a β₀ (p.1 + p.2)) =
                spinRadialLift (hMaj a β₀) := by
              ext r; dsimp [spinLiftTToR, spinRadialLift]; congr 1; ring
            rw [heq]
            exact Submodule.subset_span (Or.inr ⟨β₀, hβ₀0, hβ₀1, rfl⟩)
        · exact Submodule.zero_mem _
        · intro f g _ _ hf hg; exact Submodule.add_mem _ hf hg
        · intro r f _ hf; exact Submodule.smul_mem _ r hf
      refine ⟨hTpos, Φ, hΦ_cert, hq_vac, fun p hp => ?_⟩
      have hp_cone : p ∈ spinConeB (η * a) := ⟨hp.1, hp.2.1⟩
      rw [spinEvalWider_oddLagPoly ha2 hq_mem hη0 hη1 hp_cone]
      exact hq_nn p hp
    have hTV_nn : 0 ≤ virasoroProblem.T_V (12 * a) := by
      unfold FixedWeightProblem.T_V
      exact Real.sInf_nonneg fun T hT => hT.1.le
    have hne_cert : ({T' : ℝ | 0 < T' ∧ ∃ Φ, SpinCertifiedClass a Φ ∧ 0 < spinPhiVac a Φ ∧
        ∀ p ∈ widerCone a η T', 0 ≤ spinEvalWider a Φ p}).Nonempty :=
      ⟨virasoroProblem.T_V (12 * a) + 1,
        hcert_set_mem (by linarith) (by linarith)⟩
    have hcert_to_J : ∀ {Φ : ℝ × ℝ → ℝ}, SpinCertifiedClass a Φ → SpinTestClassJ a Φ := by
      intro Φ hΦ
      have hΨ : ∃ Ψ : ℝ × ℝ → ℝ, SpinCertifiedT a Ψ ∧ Φ = spinLiftTToR Ψ := by
        unfold SpinCertifiedClass at hΦ
        refine Submodule.span_induction
          (p := fun f _ => ∃ Ψ : ℝ × ℝ → ℝ, SpinCertifiedT a Ψ ∧ f = spinLiftTToR Ψ)
          ?_ ?_ ?_ ?_ hΦ
        · rintro _ (⟨m, n₀, hmn, rfl⟩ | ⟨β₀, hβ₀0, hβ₀1, rfl⟩)
          · exact ⟨spinOddLagBasisT m n₀,
              Submodule.subset_span (Or.inl ⟨m, n₀, hmn, rfl⟩), rfl⟩
          · refine ⟨fun p => hMaj a β₀ (p.1 + p.2),
              Submodule.subset_span (Or.inr ⟨β₀, hβ₀0, hβ₀1, rfl⟩), ?_⟩
            ext r; dsimp [spinLiftTToR, spinRadialLift]; congr 1; ring
        · exact ⟨0, Submodule.zero_mem _, rfl⟩
        · rintro f g _ _ ⟨Ψ₁, h₁, rfl⟩ ⟨Ψ₂, h₂, rfl⟩
          exact ⟨Ψ₁ + Ψ₂, Submodule.add_mem _ h₁ h₂, rfl⟩
        · rintro r f _ ⟨Ψ, hΨ, rfl⟩
          exact ⟨r • Ψ, Submodule.smul_mem _ r hΨ, rfl⟩
      obtain ⟨Ψ, hΨ, rfl⟩ := hΨ
      exact spinLiftTToR_mem_SpinTestClassJ ha2 hΨ
    have hne_J : ({T' : ℝ | 0 < T' ∧ ∃ Φ, SpinTestClassJ a Φ ∧ 0 < spinPhiVac a Φ ∧
        ∀ p ∈ widerCone a η T', 0 ≤ spinEvalWider a Φ p}).Nonempty := by
      obtain ⟨T, hT0, Φ, hΦ, hvac, hpos⟩ := hne_cert
      exact ⟨T, hT0, Φ, hcert_to_J hΦ, hvac, hpos⟩
    have hne_L : ({T' : ℝ | 0 < T' ∧ ∃ Φ, SpinTestClass a Φ ∧ 0 < spinPhiVac a Φ ∧
        ∀ p ∈ widerCone a η T', 0 ≤ spinEvalWider a Φ p}).Nonempty := by
      obtain ⟨T, hT0, Φ, hΦ, hvac, hpos⟩ := hne_J
      exact ⟨T, hT0, Φ, hΦ.base, hvac, hpos⟩
    have hmono_L : spinThrInf (SpinTestClass a) liouvilleCone a ≤ spinWiderThr (SpinTestClass a) a η := by
      unfold spinThrInf spinWiderThr
      refine csInf_le_csInf ⟨0, fun T hT => hT.1.le⟩ hne_L ?_
      rintro T ⟨hT0, Φ, hΦ, hvac, hpos⟩
      refine ⟨hT0, Φ, hΦ, hvac, fun p hp => ?_⟩
      have hpw : p ∈ widerCone a η T := liouvilleCone_subset_widerCone ha_nn hη0 T hp
      rw [← spinEvalWider_eq_spinEvalT ha2 hΦ hp.1 hp.2.1]
      exact hpos p hpw
    have hmono_J : spinThrInf (SpinTestClassJ a) liouvilleCone a ≤ spinWiderThr (SpinTestClassJ a) a η := by
      unfold spinThrInf spinWiderThr
      refine csInf_le_csInf ⟨0, fun T hT => hT.1.le⟩ hne_J ?_
      rintro T ⟨hT0, Φ, hΦ, hvac, hpos⟩
      refine ⟨hT0, Φ, hΦ, hvac, fun p hp => ?_⟩
      have hpw : p ∈ widerCone a η T := liouvilleCone_subset_widerCone ha_nn hη0 T hp
      rw [← spinEvalWider_eq_spinEvalT ha2 hΦ.base hp.1 hp.2.1]
      exact hpos p hpw
    have hcert_le_TV : spinWiderThr (SpinCertifiedClass a) a η ≤ virasoroProblem.T_V (12 * a) := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hle : spinWiderThr (SpinCertifiedClass a) a η ≤ virasoroProblem.T_V (12 * a) + ε := by
        unfold spinWiderThr
        refine csInf_le ⟨0, fun T hT => hT.1.le⟩ (hcert_set_mem (by linarith) (by linarith))
      exact hle
    have hΔ_vir : virasoroProblem.Delta_best n = a + virasoroProblem.T_V (12 * a) := by
      unfold FixedWeightProblem.Delta_best
      change n / 12 + virasoroProblem.T_V n = a + virasoroProblem.T_V (12 * a)
      rw [show 12 * a = n by dsimp [a]; ring]
    have hL_eq : spinDeltaL c = (c - 1) / 12 + spinThrInf (SpinTestClass a) liouvilleCone a := by
      unfold spinDeltaL; rfl
    have hS_eq : spinDeltaSpin c = (c - 1) / 12 + spinThrInf (SpinTestClassJ a) liouvilleCone a := by
      unfold spinDeltaSpin; rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hL_eq]; change a + _ ≤ _; linarith
    · rw [hS_eq]; change a + _ ≤ _; linarith
    · rw [hΔ_vir]; linarith
  refine ⟨hTm_pos, hlo, hL_spin, hspin_vir, hvir_hi, hslack, hthr_pos, ?_, hattain, hwider⟩
  have hCons := hcons hc_S3
  exact hCons.2.2.1

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS4_4_4_of_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS4_4_4_of_props

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS4_of_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS4_of_props

/-- **Corollary 6.2 (`s4:4.4`, unconditional)** of `spinning_s4.tex`. -/
theorem spinS4_4_4 : SpinS4_4_4 :=
  spinS4_4_4_of_props spinS4_4_3 spinS4_5_1 spinS4_5_2 spinS4_6_1

/-- **Theorem S4 (`s4:S4`, unconditional)** of `spinning_s4.tex`: continuous-spin threshold,
slack-feasible obstruction, attainment, and wider-cone extension for `{t_L, t_R ≥ -η a}`. -/
theorem spinS4 : SpinS4 :=
  spinS4_of_props spinS4_2_1 spinS4_2_2 spinS4_2_3 spinS4_2_4 spinS4_3_3 spinS4_3_4
    spinS4_4_1 spinS4_4_2 spinS4_4_3 spinS4_5_1 spinS4_5_2 spinS4_6_1 spinS4_4_4

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS4_4_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS4_4_4

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS4

end FormalResearch.ModularBootstrap.Spin
