module

public import FormalResearch.ModularBootstrap.Mixtures.Jets
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroDatum
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroBounds
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroJet
public import FormalResearch.ModularBootstrap.FiveTerm.OuterRest
public import Mathlib.Analysis.Analytic.OfScalars

/-!
# General-amplitude outer function `G_outer^{(w, A)}` (`ctu:jets`, `ctu:common-functional`)

`constant_term_universality.tex`, Lemma ctu.1 (`ctu:jets`) and Lemma ctu.2 (`ctu:common-functional`);
`positive_mixtures.tex`, Proposition PM.13 (`pmix:jets`):

For any weight `w ≥ 1` and any positive real-analytic bounded amplitude `A : ℝ → ℝ` (`JetAmplitude A`),
constructs the strip amplitude `aWA w A` (`Amp`), the general outer function `GoutWA w A`, the
slit weight `WslitWA w A`, and the edge kernel `KedgeW w`, and proves:

* `goutWA_outerDatum`: `∃ g₁ : ℝ, OuterDatum (WslitWA w A) (KedgeW w) g₁ (GoutWA w A)`.
* `GA4`: the isolated amplitude factor `G_{A,4}(z) = exp h̄_{a_Rel A}(s(z))` (bounded, bounded away
  from zero on `closure Ω`, real-symmetric, `σ`-invariant, holomorphic across `0` and `1`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real ENNReal NNReal

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.Special FormalResearch.SignUncertainty.CtOuter
  FormalResearch.ModularBootstrap.FiveTerm
  FormalResearch.ModularBootstrap.FiveTerm.StripOuter

/-! ### 1. Real-analytic complex extension helper -/

lemma analyticAt_complex_ext {f : ℝ → ℝ} {x₀ : ℝ} (hf : AnalyticAt ℝ f x₀) :
    ∃ R : ℝ, 0 < R ∧ ∃ v : ℂ → ℂ, DifferentiableOn ℂ v (ball (x₀ : ℂ) R) ∧
      ∀ x : ℝ, |x - x₀| < R → v (x : ℂ) = (f x : ℂ) := by
  obtain ⟨p, r, hp⟩ := hf
  have hr_pos : 0 < r := hp.r_pos
  have hr_le : r ≤ p.radius := hp.r_le
  let c : ℕ → ℝ := fun n => p n (fun _ => 1)
  let pC : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ (fun n => (c n : ℂ))
  have hc_norm : ∀ n : ℕ, ‖p n‖ = |c n| := by
    intro n
    refine le_antisymm ?_ ?_
    · refine ContinuousMultilinearMap.opNorm_le_bound (abs_nonneg _) fun m => ?_
      have hm : p n m = (∏ i, m i) * c n := by
        have h1 : ∀ i, m i = m i • (1 : ℝ) := fun i => by simp
        conv_lhs => rw [show m = fun i => m i • (1 : ℝ) from funext h1]
        rw [ContinuousMultilinearMap.map_smul_univ]
        rfl
      rw [hm, Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (by simp [Real.norm_eq_abs, Finset.abs_prod]) (abs_nonneg _)
    · simp [c, Real.norm_eq_abs]
  have hpC_rad : r ≤ pC.radius := by
    by_contra hlt
    push Not at hlt
    obtain ⟨r₀, hr₀1, hr₀2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
    have hlt' : (r₀ : ℝ≥0∞) < p.radius := lt_of_lt_of_le hr₀2 hr_le
    have hsum := p.summable_norm_mul_pow hlt'
    have hle : (r₀ : ℝ≥0∞) ≤ pC.radius := pC.le_radius_of_summable <| by
      simpa [pC, FormalMultilinearSeries.ofScalars_norm, hc_norm] using hsum
    exact not_lt_of_ge hle hr₀1
  obtain ⟨Rnn, hR0, hRlt⟩ : ∃ R : ℝ≥0, 0 < R ∧ (R : ℝ≥0∞) < r := by
    have := ENNReal.lt_iff_exists_nnreal_btwn.1 hr_pos
    rcases this with ⟨R, hR0, hRlt⟩
    exact ⟨R, by exact_mod_cast hR0, hRlt⟩
  have hR_pos : (0 : ℝ) < (Rnn : ℝ) := hR0
  let v : ℂ → ℂ := fun z => pC.sum (z - (x₀ : ℂ))
  have hrad_lt : (Rnn : ℝ≥0∞) < pC.radius := lt_of_lt_of_le hRlt hpC_rad
  have hRnn0 : (0 : ℝ≥0∞) < (Rnn : ℝ≥0∞) := by exact_mod_cast hR0
  have hv_fps : HasFPowerSeriesOnBall pC.sum pC 0 (Rnn : ℝ≥0∞) :=
    (pC.hasFPowerSeriesOnBall (hRnn0.trans hrad_lt)).mono hRnn0 hrad_lt.le
  refine ⟨(Rnn : ℝ), hR_pos, v, fun z hz => ?_, fun x hx => ?_⟩
  · have hze : z - (x₀ : ℂ) ∈ Metric.eball (0 : ℂ) (Rnn : ℝ≥0∞) := by
      simpa [Metric.mem_eball, edist_lt_coe, dist_zero_right, dist_eq_norm] using hz
    exact ((hv_fps.analyticOnNhd _ hze).differentiableAt.comp z
      (differentiableAt_id.sub_const _)).differentiableWithinAt
  · have hxe_lt : edist (x - x₀) 0 < (Rnn : ℝ≥0∞) := by
      rw [edist_dist, dist_zero_right, Real.norm_eq_abs, ← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_lt_ofReal_iff hR_pos).mpr hx
    have hxe : x - x₀ ∈ Metric.eball (0 : ℝ) r := lt_of_lt_of_le hxe_lt hRlt.le
    have hxC : (x : ℂ) - (x₀ : ℂ) ∈ Metric.eball (0 : ℂ) pC.radius := by
      have hed : edist ((x : ℂ) - (x₀ : ℂ)) 0 = edist (x - x₀) 0 := by
        rw [edist_dist, edist_dist, dist_zero_right, dist_zero_right, ← Complex.ofReal_sub,
          Complex.norm_real]
      change edist ((x : ℂ) - (x₀ : ℂ)) 0 < pC.radius
      rw [hed]
      exact hxe_lt.trans hrad_lt
    have hsR : HasSum (fun n : ℕ => c n * (x - x₀) ^ n) (f x) := by
      have h1 := hp.hasSum hxe
      rw [add_sub_cancel] at h1
      have heq : (fun n : ℕ => p n (fun _ => x - x₀)) = fun n => c n * (x - x₀) ^ n := by
        ext n
        have h2 : p n (fun _ => x - x₀) = (x - x₀) ^ n * c n := by
          have h1' : ∀ i : Fin n, x - x₀ = (x - x₀) • (1 : ℝ) := fun _ => by simp
          conv_lhs => rw [show (fun _ => x - x₀) = fun _ : Fin n => (x - x₀) • (1 : ℝ) from funext h1']
          rw [ContinuousMultilinearMap.map_smul_univ]; simp [c]
        rw [h2, mul_comm]
      rwa [heq] at h1
    have hsC : HasSum (fun n : ℕ => (c n : ℂ) * ((x : ℂ) - (x₀ : ℂ)) ^ n) (v (x : ℂ)) := by
      change HasSum (fun n : ℕ => (c n : ℂ) * ((x : ℂ) - (x₀ : ℂ)) ^ n) (pC.sum ((x : ℂ) - (x₀ : ℂ)))
      have h1 := pC.hasSum hxC
      have heq : (fun n : ℕ => pC n (fun _ => (x : ℂ) - (x₀ : ℂ))) =
          fun n => (c n : ℂ) * ((x : ℂ) - (x₀ : ℂ)) ^ n := by
        ext n; simp [pC, mul_comm]
      rwa [heq] at h1
    have hsC' : HasSum (fun n : ℕ => (c n : ℂ) * ((x : ℂ) - (x₀ : ℂ)) ^ n) (f x : ℂ) := by
      have hof := Complex.ofRealCLM.hasSum hsR
      simpa [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub] using hof
    exact hsC.unique hsC'

/-! ### 2. Strip amplitudes `aRel`, `aW`, `aWA` -/

/-- Relative log-amplitude `a_A(τ) = log(A(x_T(τ)) / A(ξ_*))` on the hyperbolic strip line. -/
noncomputable def aRel (A : ℝ → ℝ) (τ : ℝ) : ℝ :=
  Real.log (A (xT τ) / A xiStar)

/-- Weight-shift log-amplitude `a_W(τ) = log(x_T(τ) / ξ_*) + log(b_T(τ) / ξ_*)`. -/
noncomputable def aW (τ : ℝ) : ℝ :=
  Real.log (xT τ / xiStar) + Real.log (bT τ / xiStar)

/-- Combined strip amplitude `a_{w,A}(τ)` for general weight `w ≥ 1` and amplitude `A`. -/
noncomputable def aWA (w : ℕ) (A : ℝ → ℝ) (τ : ℝ) : ℝ :=
  aAmp τ - 2 * Real.log (lamT τ) + (((w - 1 : ℕ) : ℝ) / 2) * aW τ + aRel A τ

lemma aRel_zero (A : ℝ → ℝ) {lo : ℝ} (hlo : 0 < lo) (hA : ∀ x, xiStar ≤ x → lo ≤ A x) :
    aRel A 0 = 0 := by
  have hpos : 0 < A xiStar := lt_of_lt_of_le hlo (hA xiStar le_rfl)
  simp [aRel, xT_zero, div_self hpos.ne']

lemma aW_zero : aW 0 = Real.log (1 / (2 * xiStar)) := by
  have hxi := xiStar_pos
  unfold aW
  rw [xT_zero, bT_zero, div_self hxi.ne', Real.log_one, zero_add]
  congr 1; ring

lemma aWA_zero (w : ℕ) (A : ℝ → ℝ) (hA : JetAmplitude A) :
    aWA w A 0 = -((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4) * Real.log (2 * xiStar) := by
  obtain ⟨lo, hlo, hA_lo⟩ := hA.lower
  have hlam : lamT 0 = 1 := lamT_zero
  unfold aWA
  rw [aAmp_zero, hlam, Real.log_one, mul_zero, sub_zero, aW_zero, aRel_zero A hlo hA_lo, add_zero]
  have hxi := xiStar_pos
  rw [Real.log_div one_ne_zero (by positivity), Real.log_one, zero_sub]
  ring

lemma aRel_even (A : ℝ → ℝ) (τ : ℝ) : aRel A (-τ) = aRel A τ := by
  unfold aRel; rw [xT_even]

lemma aW_even (τ : ℝ) : aW (-τ) = aW τ := by
  unfold aW; rw [xT_even, bT_even]

lemma aWA_even (w : ℕ) (A : ℝ → ℝ) (τ : ℝ) : aWA w A (-τ) = aWA w A τ := by
  unfold aWA; rw [aAmp_even, lamT_even, aW_even, aRel_even]
where
  lamT_even (t : ℝ) : lamT (-t) = lamT t := by unfold lamT; rw [xT_even]

lemma amp_aRel {A : ℝ → ℝ} (hA : JetAmplitude A) : Amp (aRel A) := by
  obtain ⟨lo, hlo, hAlo⟩ := hA.lower
  obtain ⟨hi, hAhi⟩ := hA.upper
  have hAξ : 0 < A xiStar := lt_of_lt_of_le hlo (hAlo xiStar le_rfl)
  have hcontA : ContinuousOn A (Ici xiStar) := fun x hx =>
    (hA.analytic x hx).continuousAt.continuousWithinAt
  have hcont : Continuous (aRel A) := by
    unfold aRel
    refine Real.continuousOn_log.comp_continuous
      ((hcontA.comp_continuous continuous_xT fun τ => xiStar_le_xT τ).div_const _) fun τ => ?_
    exact (div_pos (lt_of_lt_of_le hlo (hAlo _ (xiStar_le_xT τ))) hAξ).ne'
  have hbdd : ExpBdd (aRel A) := by
    have hhi_pos : 0 < hi := lt_of_lt_of_le hlo (hAlo xiStar le_rfl |>.trans (hAhi xiStar le_rfl))
    refine ⟨max |Real.log (lo / A xiStar)| |Real.log (hi / A xiStar)|, fun τ => ?_⟩
    have h1 : lo / A xiStar ≤ A (xT τ) / A xiStar :=
      div_le_div_of_nonneg_right (hAlo _ (xiStar_le_xT τ)) hAξ.le
    have h2 : A (xT τ) / A xiStar ≤ hi / A xiStar :=
      div_le_div_of_nonneg_right (hAhi _ (xiStar_le_xT τ)) hAξ.le
    have hlog1 : Real.log (lo / A xiStar) ≤ aRel A τ :=
      Real.log_le_log (div_pos hlo hAξ) h1
    have hlog2 : aRel A τ ≤ Real.log (hi / A xiStar) :=
      Real.log_le_log (div_pos (lt_of_lt_of_le hlo (hAlo _ (xiStar_le_xT τ))) hAξ) h2
    have habs : |aRel A τ| ≤ max |Real.log (lo / A xiStar)| |Real.log (hi / A xiStar)| := by
      rw [abs_le]
      exact ⟨(neg_le_neg (le_max_left _ _)).trans (by linarith [neg_abs_le (Real.log (lo / A xiStar))]),
        hlog2.trans ((le_abs_self _).trans (le_max_right _ _))⟩
    exact habs.trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (abs_nonneg τ)))
  refine ⟨hcont, aRel_even A, hbdd, fun y₀ => ?_⟩
  obtain ⟨R₀, hR₀, hg⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_goodAt y₀)
  obtain ⟨R₁, hR₁, vA, hvA, hvA_eq⟩ := analyticAt_complex_ext (hA.analytic (xT y₀) (xiStar_le_xT y₀))
  have hxC_cont : ContinuousAt xC (y₀ : ℂ) := (goodAt_ofReal y₀).diff_xC.continuousAt
  obtain ⟨R₂, hR₂, hxC_ball⟩ := Metric.continuousAt_iff.mp hxC_cont R₁ hR₁
  have hvA_cont : ContinuousAt (fun ζ => vA (xC ζ)) (y₀ : ℂ) :=
    (hvA.continuousOn.continuousAt (isOpen_ball.mem_nhds (by
      rw [xC_ofReal]; exact mem_ball_self hR₁))).comp hxC_cont
  have hvA_pos : (vA (xC (y₀ : ℂ))).re = A (xT y₀) ∧ (vA (xC (y₀ : ℂ))).im = 0 := by
    rw [xC_ofReal, hvA_eq (xT y₀) (by simp [hR₁])]
    simp
  have hslit : vA (xC (y₀ : ℂ)) / (A xiStar : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left
    rw [xC_ofReal, hvA_eq _ (by simp [hR₁]), ← Complex.ofReal_div, Complex.ofReal_re]
    exact div_pos (lt_of_lt_of_le hlo (hAlo _ (xiStar_le_xT y₀))) hAξ
  obtain ⟨R₃, hR₃, hvs⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hvA_cont.div_const (A xiStar : ℂ)).eventually (Complex.isOpen_slitPlane.mem_nhds hslit))
  set R := min R₀ (min R₂ R₃)
  refine ⟨R, lt_min hR₀ (lt_min hR₂ hR₃), fun ζ => Complex.log (vA (xC ζ) / (A xiStar : ℂ)), ?_, ?_⟩
  · intro ζ hζ
    have hζ0 : ζ ∈ ball (y₀ : ℂ) R₀ := (mem_ball.1 hζ).trans_le (min_le_left _ _)
    have hζ2 : ζ ∈ ball (y₀ : ℂ) R₂ := (mem_ball.1 hζ).trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hζ3 : ζ ∈ ball (y₀ : ℂ) R₃ := (mem_ball.1 hζ).trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hx_ball : xC ζ ∈ ball (xT y₀ : ℂ) R₁ := by
      have := hxC_ball hζ2
      rwa [xC_ofReal] at this
    have hd1 : DifferentiableAt ℂ xC ζ := (hg ζ hζ0).diff_xC
    have hd2 : DifferentiableAt ℂ vA (xC ζ) := hvA.differentiableAt (isOpen_ball.mem_nhds hx_ball)
    exact ((hd2.comp ζ hd1).div_const _).clog (hvs ζ hζ3) |>.differentiableWithinAt
  · intro t ht
    have ht2 : (t : ℂ) ∈ ball (y₀ : ℂ) R₂ := by
      rw [mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact lt_of_lt_of_le ht ((min_le_right _ _).trans (min_le_left _ _))
    have hxt : |xT t - xT y₀| < R₁ := by
      have := hxC_ball ht2
      rw [xC_ofReal, xC_ofReal, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs] at this
      exact this
    dsimp only; unfold aRel
    rw [xC_ofReal, hvA_eq (xT t) hxt, ← Complex.ofReal_div, ← Complex.ofReal_log
      (div_pos (lt_of_lt_of_le hlo (hAlo _ (xiStar_le_xT t))) hAξ).le]

lemma xT_le_linear (τ : ℝ) : xT τ ≤ |τ| / 2 + 2 * Real.log 2 / π := by
  have hcosh : Real.cosh (π * τ) ≤ Real.exp (π * |τ|) := by
    rw [Real.cosh_eq]
    rcases le_total τ 0 with hτ | hτ
    · rw [abs_of_nonpos hτ]
      have : Real.exp (π * τ) ≤ Real.exp (π * -τ) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      have heneg : -(π * τ) = π * -τ := by ring
      rw [heneg]
      linarith
    · rw [abs_of_nonneg hτ]
      have : Real.exp (-(π * τ)) ≤ Real.exp (π * τ) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      linarith
  have hs : √(Real.cosh (π * τ)) ≤ Real.exp (π * |τ| / 2) := by
    rw [show Real.exp (π * |τ| / 2) = √(Real.exp (π * |τ|)) by
      rw [← Real.exp_half (π * |τ|)]]
    exact Real.sqrt_le_sqrt hcosh
  have ha : Real.arsinh (√(Real.cosh (π * τ))) ≤ π * |τ| / 2 + 2 * Real.log 2 := by
    refine (Real.arsinh_le_arsinh.mpr hs).trans ?_
    rw [Real.arsinh]
    have he := Real.exp_pos (π * |τ| / 2)
    have hsq : √(1 + Real.exp (π * |τ| / 2) ^ 2) ≤ √2 * Real.exp (π * |τ| / 2) := by
      have : 1 + Real.exp (π * |τ| / 2) ^ 2 ≤ 2 * Real.exp (π * |τ| / 2) ^ 2 := by
        have : 1 ≤ Real.exp (π * |τ| / 2) ^ 2 := by
          nlinarith [Real.one_le_exp (by positivity : 0 ≤ π * |τ| / 2)]
        linarith
      calc √(1 + Real.exp (π * |τ| / 2) ^ 2) ≤ √(2 * Real.exp (π * |τ| / 2) ^ 2) :=
            Real.sqrt_le_sqrt this
        _ = √2 * Real.exp (π * |τ| / 2) := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq he.le]
    have h2 : √2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    calc Real.log (Real.exp (π * |τ| / 2) + √(1 + Real.exp (π * |τ| / 2) ^ 2))
        ≤ Real.log (4 * Real.exp (π * |τ| / 2)) := by
          refine Real.log_le_log (by positivity) ?_
          have : 1 ≤ Real.exp (π * |τ| / 2) := Real.one_le_exp (by positivity)
          nlinarith
      _ = Real.log 4 + π * |τ| / 2 := by rw [Real.log_mul (by norm_num) he.ne', Real.log_exp]
      _ = 2 * Real.log 2 + π * |τ| / 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
      _ = π * |τ| / 2 + 2 * Real.log 2 := by ring
  unfold xT
  rw [div_le_iff₀ Real.pi_pos]
  calc Real.arsinh (√(Real.cosh (π * τ))) ≤ π * |τ| / 2 + 2 * Real.log 2 := ha
    _ = (|τ| / 2 + 2 * Real.log 2 / π) * π := by field_simp

lemma vT_abs_le_linear (τ : ℝ) : |vT τ| ≤ |τ| / 2 + 2 * Real.log 2 / π := by
  have hodd : ∀ t, vT (-t) = -vT t := fun t => by
    unfold vT; simp [mul_neg, Real.sinh_neg, Real.arsinh_neg, neg_div]
  have hnonneg : ∀ t ≥ 0, vT t ≤ t / 2 + 2 * Real.log 2 / π := by
    intro t ht
    have hsh : √2 * Real.sinh (π * t / 2) ≤ Real.exp (π * t / 2) := by
      rw [Real.sinh_eq]
      have h2 : √2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      have h3 : 0 ≤ Real.exp (π * t / 2) - Real.exp (-(π * t / 2)) :=
        sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos]))
      nlinarith [Real.exp_pos (π * t / 2), Real.exp_pos (-(π * t / 2))]
    have ha : Real.arsinh (√2 * Real.sinh (π * t / 2)) ≤ π * t / 2 + 2 * Real.log 2 := by
      refine (Real.arsinh_le_arsinh.mpr hsh).trans ?_
      rw [Real.arsinh]
      have he := Real.exp_pos (π * t / 2)
      have hsq : √(1 + Real.exp (π * t / 2) ^ 2) ≤ √2 * Real.exp (π * t / 2) := by
        have : 1 + Real.exp (π * t / 2) ^ 2 ≤ 2 * Real.exp (π * t / 2) ^ 2 := by
          have : 1 ≤ Real.exp (π * t / 2) ^ 2 := by
            nlinarith [Real.one_le_exp (by positivity : 0 ≤ π * t / 2)]
          linarith
        calc √(1 + Real.exp (π * t / 2) ^ 2) ≤ √(2 * Real.exp (π * t / 2) ^ 2) :=
              Real.sqrt_le_sqrt this
          _ = √2 * Real.exp (π * t / 2) := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq he.le]
      have h2 : √2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      calc Real.log (Real.exp (π * t / 2) + √(1 + Real.exp (π * t / 2) ^ 2))
          ≤ Real.log (4 * Real.exp (π * t / 2)) := by
            refine Real.log_le_log (by positivity) ?_
            have : 1 ≤ Real.exp (π * t / 2) := Real.one_le_exp (by positivity)
            nlinarith
        _ = 2 * Real.log 2 + π * t / 2 := by
            rw [Real.log_mul (by norm_num) he.ne', Real.log_exp,
              show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
            push_cast; ring
        _ = π * t / 2 + 2 * Real.log 2 := by ring
    unfold vT
    rw [div_le_iff₀ Real.pi_pos]
    calc Real.arsinh (√2 * Real.sinh (π * t / 2)) ≤ π * t / 2 + 2 * Real.log 2 := ha
      _ = (t / 2 + 2 * Real.log 2 / π) * π := by field_simp
  rcases le_total τ 0 with hτ | hτ
  · have hvnn : vT τ ≤ 0 := by
      have : -vT τ ≥ 0 := by
        rw [← hodd]; unfold vT
        exact div_nonneg (Real.arsinh_nonneg_iff.mpr
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sinh_nonneg_iff.mpr (by nlinarith [Real.pi_pos]))))
          Real.pi_pos.le
      linarith
    rw [abs_of_nonpos hvnn, abs_of_nonpos hτ, ← hodd]
    exact hnonneg (-τ) (neg_nonneg.mpr hτ)
  · have hvnn : 0 ≤ vT τ := by
      unfold vT
      exact div_nonneg (Real.arsinh_nonneg_iff.mpr
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sinh_nonneg_iff.mpr (by nlinarith [Real.pi_pos]))))
        Real.pi_pos.le
    rw [abs_of_nonneg hvnn, abs_of_nonneg hτ]
    exact hnonneg τ hτ

lemma bT_le_linear (τ : ℝ) : bT τ ≤ |τ| / 2 + 2 * Real.log 2 / π + 1 / 2 := by
  have hb : bT τ ≤ |vT τ| + 1 / 2 := by
    unfold bT
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    nlinarith [sq_abs (vT τ), abs_nonneg (vT τ)]
  linarith [vT_abs_le_linear τ]

lemma aW_ge (τ : ℝ) : -Real.log (2 * xiStar) ≤ aW τ := by
  have hxi := xiStar_pos
  have hx : 1 ≤ xT τ / xiStar := (one_le_div hxi).mpr (xiStar_le_xT τ)
  have hb : 1 / 2 ≤ bT τ := by
    unfold bT
    exact Real.le_sqrt_of_sq_le (by linarith [sq_nonneg (vT τ)])
  have h1 : 0 ≤ Real.log (xT τ / xiStar) := Real.log_nonneg hx
  have h2 : -Real.log (2 * xiStar) ≤ Real.log (bT τ / xiStar) := by
    have hinv : Real.log ((1 / 2) / xiStar) = -Real.log (2 * xiStar) := by
      rw [show (1 / 2 : ℝ) / xiStar = (2 * xiStar)⁻¹ by ring, Real.log_inv]
    rw [← hinv]
    exact Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hb hxi.le)
  unfold aW
  linarith

lemma aW_le_of_pos {δ : ℝ} (hδ : 0 < δ) : ∃ β : ℝ, ∀ τ : ℝ, aW τ ≤ δ * |τ| + β := by
  have hxi := xiStar_pos
  let ε : ℝ := δ * xiStar
  have hε : 0 < ε := mul_pos hδ hxi
  let C₀ : ℝ := 2 * Real.log 2 / π + 1 / 2
  refine ⟨2 * (δ * C₀ - 1 - Real.log ε), fun τ => ?_⟩
  have hlog_le : ∀ u : ℝ, 0 < u → Real.log u ≤ ε * u - 1 - Real.log ε := fun u hu => by
    have h1 := Real.log_le_sub_one_of_pos (mul_pos hε hu)
    rw [Real.log_mul hε.ne' hu.ne'] at h1
    linarith
  have hx_le : Real.log (xT τ / xiStar) ≤ δ * |τ| / 2 + (δ * C₀ - 1 - Real.log ε) := by
    have h1 := hlog_le (xT τ / xiStar) (div_pos (xT_pos τ) hxi)
    have h2 : ε * (xT τ / xiStar) = δ * xT τ := by dsimp only [ε]; field_simp
    have h3 : xT τ ≤ |τ| / 2 + C₀ := by
      have := xT_le_linear τ
      dsimp only [C₀]; linarith
    have h4 : δ * xT τ ≤ δ * (|τ| / 2 + C₀) := mul_le_mul_of_nonneg_left h3 hδ.le
    calc Real.log (xT τ / xiStar) ≤ ε * (xT τ / xiStar) - 1 - Real.log ε := h1
      _ = δ * xT τ - 1 - Real.log ε := by rw [h2]
      _ ≤ δ * (|τ| / 2 + C₀) - 1 - Real.log ε := by linarith [h4]
      _ = δ * |τ| / 2 + (δ * C₀ - 1 - Real.log ε) := by ring
  have hb_le : Real.log (bT τ / xiStar) ≤ δ * |τ| / 2 + (δ * C₀ - 1 - Real.log ε) := by
    have h1 := hlog_le (bT τ / xiStar) (div_pos (bT_pos τ) hxi)
    have h2 : ε * (bT τ / xiStar) = δ * bT τ := by dsimp only [ε]; field_simp
    have h3 : bT τ ≤ |τ| / 2 + C₀ := by
      have := bT_le_linear τ
      dsimp only [C₀]; linarith
    have h4 : δ * bT τ ≤ δ * (|τ| / 2 + C₀) := mul_le_mul_of_nonneg_left h3 hδ.le
    calc Real.log (bT τ / xiStar) ≤ ε * (bT τ / xiStar) - 1 - Real.log ε := h1
      _ = δ * bT τ - 1 - Real.log ε := by rw [h2]
      _ ≤ δ * (|τ| / 2 + C₀) - 1 - Real.log ε := by linarith [h4]
      _ = δ * |τ| / 2 + (δ * C₀ - 1 - Real.log ε) := by ring
  unfold aW
  linarith

private lemma amp_add {a b : ℝ → ℝ} (ha : Amp a) (hb : Amp b) :
    Amp (fun t => a t + b t) := by
  refine ⟨ha.cont.add hb.cont, fun t => by simp [ha.even t, hb.even t], ?_, fun y₀ => ?_⟩
  · obtain ⟨Ca, hCa⟩ := ha.bdd
    obtain ⟨Cb, hCb⟩ := hb.bdd
    refine ⟨max Ca 0 + max Cb 0, fun t => ?_⟩
    calc |a t + b t| ≤ |a t| + |b t| := abs_add_le _ _
      _ ≤ Ca * Real.exp |t| + Cb * Real.exp |t| := add_le_add (hCa t) (hCb t)
      _ ≤ (max Ca 0 + max Cb 0) * Real.exp |t| := by
          have := (Real.exp_pos |t|).le
          nlinarith [le_max_left Ca 0, le_max_left Cb 0]
  · obtain ⟨Ra, hRa, va, hva, hva_eq⟩ := ha.loc y₀
    obtain ⟨Rb, hRb, vb, hvb, hvb_eq⟩ := hb.loc y₀
    refine ⟨min Ra Rb, lt_min hRa hRb, fun ζ => va ζ + vb ζ, ?_, fun t ht => ?_⟩
    · exact (hva.mono (Metric.ball_subset_ball (min_le_left _ _))).add
        (hvb.mono (Metric.ball_subset_ball (min_le_right _ _)))
    · dsimp only
      rw [hva_eq t (lt_of_lt_of_le ht (min_le_left _ _)),
        hvb_eq t (lt_of_lt_of_le ht (min_le_right _ _))]
      push_cast; rfl

private lemma amp_smul (c : ℝ) {a : ℝ → ℝ} (ha : Amp a) :
    Amp (fun t => c * a t) := by
  refine ⟨continuous_const.mul ha.cont, fun t => by simp [ha.even t], ?_, fun y₀ => ?_⟩
  · obtain ⟨C, hC⟩ := ha.bdd
    refine ⟨|c| * max C 0, fun t => ?_⟩
    rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((hC t).trans (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (Real.exp_pos _).le)) (abs_nonneg c)
  · obtain ⟨R, hR, v, hv, hv_eq⟩ := ha.loc y₀
    refine ⟨R, hR, fun ζ => (c : ℂ) * v ζ, ?_, fun t ht => ?_⟩
    · exact (differentiableOn_const _).mul hv
    · dsimp only; rw [hv_eq t ht]; push_cast; rfl

lemma lamLog_bounds :
    ∀ τ : ℝ, 0 ≤ Real.log (lamT τ) ∧
      Real.log (lamT τ) ≤ Real.log (1 / (1 - Real.exp (-(4 * π * xiStar)))) := fun τ =>
  ⟨Real.log_nonneg (one_le_lamT τ), Real.log_le_log (lamT_pos τ) (lamT_le τ)⟩

lemma amp_lamLog : Amp (fun t => Real.log (lamT t)) := by
  have hcont : Continuous (fun t => Real.log (lamT t)) :=
    continuous_lamT.log (fun t => (lamT_pos t).ne')
  have heven : ∀ t, Real.log (lamT (-t)) = Real.log (lamT t) := fun t => by
    have : lamT (-t) = lamT t := by unfold lamT; rw [xT_even]
    rw [this]
  have hbdd : ExpBdd (fun t => Real.log (lamT t)) :=
    FiveTerm.OuterStrip.expBdd_of_bounds (α := 0) le_rfl (fun t => (lamLog_bounds t).1)
      (fun t => by simpa using (lamLog_bounds t).2)
  refine ⟨hcont, heven, hbdd, fun y₀ => ?_⟩
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_goodAt y₀)
  refine ⟨R, hR, fun ζ => Complex.log (lamC ζ), ?_, fun t _ => ?_⟩
  · exact fun ζ hζ => ((hball ζ hζ).diff_lamC.clog (hball ζ hζ).c7).differentiableWithinAt
  · dsimp only; rw [lamC_ofReal, ← Complex.ofReal_log (lamT_pos t).le]

lemma amp_aW : Amp aW := by
  have hcont : Continuous aW := by
    unfold aW
    exact (continuous_xT.div_const _ |>.log fun t => (div_pos (xT_pos t) xiStar_pos).ne').add
      (continuous_bT.div_const _ |>.log fun t => (div_pos (bT_pos t) xiStar_pos).ne')
  obtain ⟨β, hβ⟩ := aW_le_of_pos (δ := 1) one_pos
  have hbdd : ExpBdd aW :=
    FiveTerm.OuterStrip.expBdd_of_bounds (α := 1) zero_le_one aW_ge hβ
  refine ⟨hcont, aW_even, hbdd, fun y₀ => ?_⟩
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_goodAt y₀)
  refine ⟨R, hR, fun ζ =>
    Complex.log (xC ζ) + Complex.log (bC ζ) - (2 * Real.log xiStar : ℂ), ?_, fun t _ => ?_⟩
  · intro ζ hζ
    have hg := hball ζ hζ
    exact (((hg.diff_xC.clog hg.c5).add (hg.diff_bC.clog hg.c6)).sub_const _).differentiableWithinAt
  · dsimp only
    rw [xC_ofReal, bC_ofReal, ← Complex.ofReal_log (xT_pos t).le,
      ← Complex.ofReal_log (bT_pos t).le]
    unfold aW
    rw [Real.log_div (xT_pos t).ne' xiStar_pos.ne', Real.log_div (bT_pos t).ne' xiStar_pos.ne']
    push_cast; ring

theorem amp_aWA (w : ℕ) {A : ℝ → ℝ} (hA : JetAmplitude A) : Amp (aWA w A) := by
  have heq : aWA w A = fun τ =>
      (aAmp τ + (-2 : ℝ) * Real.log (lamT τ)) +
        ((((w - 1 : ℕ) : ℝ) / 2) * aW τ + aRel A τ) := by
    ext τ; unfold aWA; ring
  rw [heq]
  exact amp_add (amp_add amp_aAmp (amp_smul (-2) amp_lamLog))
    (amp_add (amp_smul _ amp_aW) (amp_aRel hA))

lemma aWA_bounds (w : ℕ) {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ∃ m β : ℝ, (∀ τ, m ≤ aWA w A τ) ∧ (∀ τ, aWA w A τ ≤ (5 * π / 8) * |τ| + β) := by
  obtain ⟨lo, hlo, hAlo⟩ := hA.lower
  obtain ⟨hi, hAhi⟩ := hA.upper
  have hAξ : 0 < A xiStar := lt_of_lt_of_le hlo (hAlo xiStar le_rfl)
  have hre : ∀ τ, aWA w A τ =
      (FiveTerm.OuterStrip.aRest τ - 2 * Real.log (lamT τ)) +
        ((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4) * aW τ + aRel A τ := by
    intro τ
    have hxb : FiveTerm.OuterStrip.aXb τ = (1 / 4) * aW τ := by
      unfold FiveTerm.OuterStrip.aXb aW
      rw [Real.log_div (xT_pos τ).ne' xiStar_pos.ne', Real.log_div (bT_pos τ).ne' xiStar_pos.ne']
      ring
    have ha : aAmp τ = FiveTerm.OuterStrip.aXb τ + FiveTerm.OuterStrip.aRest τ :=
      FiveTerm.OuterStrip.aAmp_eq_aXb_add_aRest τ
    unfold aWA
    rw [ha, hxb]
    ring
  have hcoef : 0 < (2 * ((w - 1 : ℕ) : ℝ) + 1) / 4 := by positivity
  obtain ⟨βW, hβW⟩ := aW_le_of_pos (δ := (π / 8) / ((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4))
    (div_pos (by positivity) hcoef)
  have hlam_up := (lamLog_bounds 0).2
  set Lmax := Real.log (1 / (1 - Real.exp (-(4 * π * xiStar))))
  refine ⟨-(13 / 4 * Real.log 2) - 2 * Lmax +
      ((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4) * (-Real.log (2 * xiStar)) + Real.log (lo / A xiStar),
    ((1 / 2) * Real.log 2 - 2 * Real.log (1 - Real.exp (-(4 * π * xiStar)))) +
      ((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4) * βW + Real.log (hi / A xiStar),
    fun τ => ?_, fun τ => ?_⟩
  · rw [hre τ]
    have h1 : -(13 / 4 * Real.log 2) ≤ FiveTerm.OuterStrip.aRest τ := FiveTerm.OuterStrip.aRest_ge τ
    have h2 : Real.log (lamT τ) ≤ Lmax := (lamLog_bounds τ).2
    have h3 : -Real.log (2 * xiStar) ≤ aW τ := aW_ge τ
    have h4 : Real.log (lo / A xiStar) ≤ aRel A τ :=
      Real.log_le_log (div_pos hlo hAξ) (div_le_div_of_nonneg_right (hAlo _ (xiStar_le_xT τ)) hAξ.le)
    nlinarith [hcoef.le]
  · rw [hre τ]
    have h1 : FiveTerm.OuterStrip.aRest τ ≤ (π / 2) * |τ| +
        ((1 / 2) * Real.log 2 - 2 * Real.log (1 - Real.exp (-(4 * π * xiStar)))) :=
      FiveTerm.OuterStrip.aRest_le τ
    have h2 : 0 ≤ Real.log (lamT τ) := (lamLog_bounds τ).1
    have h3 := hβW τ
    have h4 : aRel A τ ≤ Real.log (hi / A xiStar) :=
      Real.log_le_log (div_pos (lt_of_lt_of_le hlo (hAlo _ (xiStar_le_xT τ))) hAξ)
        (div_le_div_of_nonneg_right (hAhi _ (xiStar_le_xT τ)) hAξ.le)
    have h3' : ((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4) * aW τ ≤
        (π / 8) * |τ| + ((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4) * βW := by
      have hm := mul_le_mul_of_nonneg_left h3 hcoef.le
      calc ((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4) * aW τ
          ≤ ((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4) *
            ((π / 8 / ((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4)) * |τ| + βW) := hm
        _ = (π / 8) * |τ| + ((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4) * βW := by
            field_simp [hcoef.ne']
    nlinarith

/-! ### 3. `GA4`, `GoutWA`, `WslitWA`, `KedgeW`, and `OuterDatum` -/

/-- The general-amplitude factor `G_{A,4}(z) = exp(h̄_{a_Rel A}(s(z)))` on `closure Ω ∖ {±i, 1}`. -/
noncomputable def GA4 (A : ℝ → ℝ) (z : ℂ) : ℂ :=
  Complex.exp (hbarA (aRel A) (sInv z))

/-- The general-weight, general-amplitude outer function `G_outer^{(w, A)}`. -/
noncomputable def GoutWA (w : ℕ) (A : ℝ → ℝ) (z : ℂ) : ℂ :=
  Complex.exp (hbarA (aWA w A) (sInv z)) * (1 - z) ^ (1 / 2 : ℂ) / (1 + z) ^ 2 *
    (qBd z) ^ (-(((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4 : ℝ) : ℂ))

/-- The slit weight `W_slit^{(w, A)}(y)` of `ctu:moduli` (`ctu:jets`). -/
noncomputable def WslitWA (w : ℕ) (A : ℝ → ℝ) (y : ℝ) : ℝ :=
  (xOf y / xiStar) ^ ((w : ℝ) - 1 / 2) * (A (xOf y) / A xiStar) /
    ((1 - y ^ 2) * √(1 + 6 * y ^ 2 + y ^ 4))

/-- The edge kernel `K_edge^{(w)}(y) = ((-i b_x) / x)^{w-1} K_edge(y)` of `ctu:qy`. -/
noncomputable def KedgeW (w : ℕ) (y : ℝ) : ℂ :=
  Kedge y * (slitVal y) ^ (w - 1)

lemma goutWA_diff (w : ℕ) {A : ℝ → ℝ} (hA : JetAmplitude A) :
    DifferentiableOn ℂ (GoutWA w A) halfDisc := by
  intro z hz
  have hs : sInv z ∈ strip := sInv_mem_strip hz
  have h12 := halfDisc_ne_special hz
  have h_sInv : DifferentiableAt ℂ sInv z := differentiableAt_sInv (subset_closure hz) h12.1 h12.2.1
  have ha : DifferentiableAt ℂ (hbarA (aWA w A)) (sInv z) := by
    refine DifferentiableAt.congr_of_eventuallyEq
      ((differentiableOn_genH (amp_aWA w hA)).differentiableAt (isOpen_strip.mem_nhds hs)) ?_
    filter_upwards [isOpen_strip.mem_nhds hs] with w' hw'
    exact hbarA_of_mem_strip (amp_aWA w hA) hw'
  have h1 : DifferentiableAt ℂ (fun z => Complex.exp (hbarA (aWA w A) (sInv z))) z :=
    (ha.comp z h_sInv).cexp
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (1 - z) ^ (1 / 2 : ℂ)) z :=
    DifferentiableAt.cpow_const (by fun_prop) (one_sub_mem_slit (subset_closure hz) h12.2.2)
  have h3 : DifferentiableAt ℂ (fun z : ℂ => (1 + z) ^ 2) z := by fun_prop
  have h3ne : (1 + z) ^ 2 ≠ 0 := pow_ne_zero 2 (one_add_ne_zero' (subset_closure hz))
  have h4 : DifferentiableAt ℂ (fun z => (qBd z) ^ (-(((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4 : ℝ) : ℂ))) z := by
    have hq : DifferentiableAt ℂ qHat z :=
      differentiableOn_qHat.differentiableAt (isOpen_halfDisc.mem_nhds hz)
    have hqc : DifferentiableAt ℂ qBd z := hq.congr_of_eventuallyEq <| by
      filter_upwards [isOpen_halfDisc.mem_nhds hz] with w' hw'
      exact qBd_of_mem hw'
    exact hqc.cpow_const (qBd_mem_slit ⟨subset_closure hz, not_mem_singPts_of_halfDisc hz⟩)
  exact (((h1.mul h2).div h3 h3ne).mul h4).differentiableWithinAt

lemma goutWA_cont (w : ℕ) {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ContinuousOn (GoutWA w A) (closure halfDisc \ singPts) := by
  have ha : ContinuousOn (fun z => Complex.exp (hbarA (aWA w A) (sInv z)))
      (closure halfDisc \ singPts) :=
    ContinuousOn.cexp ((continuousOn_hbarA (amp_aWA w hA)).comp (continuousOn_sInv.mono sing_subset)
      fun _ hz => sInv_mem_closedStrip' hz)
  have h1 : ContinuousOn (fun z : ℂ => (1 - z) ^ (1 / 2 : ℂ)) (closure halfDisc \ singPts) :=
    continuousOn_one_sub_cpow.mono sdiff_subset
  have h2 : ContinuousOn (fun z : ℂ => (1 + z) ^ 2) (closure halfDisc \ singPts) := by fun_prop
  have h3 : ContinuousOn (fun z => (qBd z) ^ (-(((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4 : ℝ) : ℂ)))
      (closure halfDisc \ singPts) :=
    (continuousOn_qBd.mono sing_subset).cpow_const fun _ hz => Complex.mem_slitPlane_iff.mp (qBd_mem_slit hz)
  exact ((ha.mul h1).div h2 fun z hz => pow_ne_zero 2 (one_add_ne_zero' hz.1)).mul h3

lemma goutWA_conj (w : ℕ) {A : ℝ → ℝ} (hA : JetAmplitude A) {z : ℂ} (hz : z ∈ halfDisc) :
    GoutWA w A (starRingEnd ℂ z) = starRingEnd ℂ (GoutWA w A z) := by
  have hzc : starRingEnd ℂ z ∈ halfDisc := halfDisc_conj hz
  have hs : sInv (starRingEnd ℂ z) = starRingEnd ℂ (sInv z) := sInv_conj hz
  have hbar : hbarA (aWA w A) (starRingEnd ℂ (sInv z)) =
      starRingEnd ℂ (hbarA (aWA w A) (sInv z)) :=
    hbarA_conj (amp_aWA w hA) (strip_subset_closedStrip (sInv_mem_strip hz))
  have hq : qBd (starRingEnd ℂ z) = starRingEnd ℂ (qBd z) := by
    rw [qBd_of_mem hzc, qBd_of_mem hz, qHat_conj hz]
  have h1 : (1 - starRingEnd ℂ z) ^ (1 / 2 : ℂ) = starRingEnd ℂ ((1 - z) ^ (1 / 2 : ℂ)) := by
    have := conj_cpow_slit (one_sub_mem_slit (subset_closure hz) (halfDisc_ne_special hz).2.2) (1 / 2 : ℂ)
    simpa [map_sub, map_one, map_div₀, map_ofNat] using this.symm
  have h2 : (1 + starRingEnd ℂ z) ^ 2 = starRingEnd ℂ ((1 + z) ^ 2) := by
    simp [map_pow, map_add, map_one]
  have h3 : (qBd (starRingEnd ℂ z)) ^ (-(((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4 : ℝ) : ℂ)) =
      starRingEnd ℂ ((qBd z) ^ (-(((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4 : ℝ) : ℂ))) := by
    rw [hq]
    have hc := conj_cpow_slit (qBd_mem_slit ⟨subset_closure hz, not_mem_singPts_of_halfDisc hz⟩)
      (-(((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4 : ℝ) : ℂ))
    have he : starRingEnd ℂ (-(((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4 : ℝ) : ℂ)) =
        -(((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_neg, Complex.conj_ofReal]
    rw [he] at hc
    exact hc.symm
  unfold GoutWA
  rw [hs, hbar, Complex.exp_conj, h1, h2, h3]
  simp only [map_mul, map_div₀]

lemma goutWA_ne_zero (w : ℕ) {A : ℝ → ℝ} {z : ℂ} (hz : z ∈ closure halfDisc \ singPts) :
    GoutWA w A z ≠ 0 := by
  have hne1 : (1 - z) ^ (1 / 2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.slitPlane_ne_zero
      (one_sub_mem_slit hz.1 (ne_of_mem_sing hz).2.2)))
  have hne2 : (1 + z) ^ 2 ≠ 0 := pow_ne_zero 2 (one_add_ne_zero' hz.1)
  have hne3 : (qBd z) ^ (-(((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4 : ℝ) : ℂ)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (qBd_ne_zero hz))
  unfold GoutWA
  exact mul_ne_zero (div_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) hne1) hne2) hne3

lemma goutWA_zero (w : ℕ) {A : ℝ → ℝ} (hA : JetAmplitude A) : GoutWA w A 0 = 1 := by
  have h0cl : (0 : ℂ) ∈ closure halfDisc := by
    have := sTan_mem_closure (s := 0) ⟨by simp, by simp⟩
    have h : sTan 0 = 0 := by simp [sTan]
    rwa [h] at this
  have hre : (hbarA (aWA w A) 0).re = aWA w A 0 := by
    have := re_hbarA_left (amp_aWA w hA) 0
    simpa using this
  have him : (hbarA (aWA w A) 0).im = 0 := by
    have hconj := hbarA_conj (amp_aWA w hA) (ζ := 0) ⟨by simp, by simp⟩
    simp only [map_zero] at hconj
    have := congrArg Complex.im hconj
    simp at this
    linarith
  have hhbar : hbarA (aWA w A) (sInv 0) = (aWA w A 0 : ℂ) := by
    rw [sInv_zero]
    exact Complex.ext hre him
  have hq0 : qBd 0 = ((1 / (2 * xiStar) : ℝ) : ℂ) := by
    rw [qBd_eq_tipExt h0cl (by simp), tipExt_zero]
    congr 1; unfold xiStar; field_simp
  unfold GoutWA
  rw [hhbar, aWA_zero w A hA, hq0]
  simp only [sub_zero, add_zero, Complex.one_cpow, one_pow, mul_one, div_one]
  have hpos : (0 : ℝ) < 1 / (2 * xiStar) := div_pos one_pos (by linarith [xiStar_pos])
  set p : ℝ := (2 * ((w - 1 : ℕ) : ℝ) + 1) / 4
  have h1 : (-(((p : ℝ) : ℂ))) = (((-p : ℝ) : ℂ)) := by push_cast; rfl
  rw [h1, ← Complex.ofReal_cpow hpos.le, ← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Complex.ofReal_one]
  congr 1
  rw [Real.rpow_def_of_pos hpos, one_div, Real.log_inv, ← Real.exp_add]
  rw [show -p * Real.log (2 * xiStar) + -Real.log (2 * xiStar) * -p = 0 by ring, Real.exp_zero]

lemma norm_goutWA (w : ℕ) (A : ℝ → ℝ) {z : ℂ} (_hz : z ∈ closure halfDisc \ singPts) :
    ‖GoutWA w A z‖ =
      Real.exp (hbarA (aWA w A) (sInv z)).re * ‖1 - z‖ ^ (1 / 2 : ℝ) / ‖1 + z‖ ^ 2 *
        ‖qBd z‖ ^ (-((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4)) := by
  have h1 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have h2 : (-(((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4 : ℝ) : ℂ)) =
      (((-((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4) : ℝ) : ℂ)) := by push_cast; ring
  unfold GoutWA
  rw [norm_mul, norm_div, norm_mul, Complex.norm_exp, norm_pow, h1, h2, Complex.norm_cpow_real,
    Complex.norm_cpow_real]

lemma goutWA_near_one (w : ℕ) {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ∃ C c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ z ∈ closure halfDisc, z ≠ 1 → ‖z - 1‖ < r →
      c * ‖z - 1‖ ^ (1 / 2 : ℝ) ≤ ‖GoutWA w A z‖ ∧
        ‖GoutWA w A z‖ ≤ C * ‖z - 1‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨m, β, hm, hβ⟩ := aWA_bounds w hA
  obtain ⟨κ, hκ⟩ := re_hbarA_le (amp_aWA w hA) (α := 5 * π / 8) (β := β) (by positivity) hβ
  have hI : (1 : ℂ) ≠ Complex.I := by
    intro h; have := congrArg Complex.im h; simp at this
  have h1c : (1 : ℂ) ∈ closure halfDisc \ {Complex.I, -Complex.I} := by
    refine ⟨one_mem_closure, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hI, fun h => by have := congrArg Complex.im h; simp at this⟩
  obtain ⟨δ1, hδ1, hS⟩ := Metric.continuousWithinAt_iff.mp (continuousOn_sInv 1 h1c) 1 one_pos
  have hq1 : qBd 1 ≠ 0 := Complex.slitPlane_ne_zero (exists_qBd one_mem_closure
    hI (fun h => by have := congrArg Complex.im h; simp at this)).1
  have hq1n : 0 < ‖qBd 1‖ := norm_pos_iff.mpr hq1
  obtain ⟨δ2, hδ2, hQ⟩ :=
    Metric.continuousWithinAt_iff.mp (continuousOn_qBd 1 h1c) (‖qBd 1‖ / 2) (by positivity)
  set r : ℝ := min (min δ1 δ2) 1
  have hrpos : 0 < r := lt_min (lt_min hδ1 hδ2) one_pos
  set p : ℝ := -((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4)
  set e1 : ℝ := Real.exp m
  set e2 : ℝ := Real.exp (5 * π / 8 * (1 + κ) + β)
  set a : ℝ := ‖qBd 1‖ / 2
  set b : ℝ := 3 * ‖qBd 1‖ / 2
  have ha0 : 0 < a := by positivity
  set q1 : ℝ := min (a ^ p) (b ^ p)
  set q2 : ℝ := max (a ^ p) (b ^ p)
  have hq1pos : 0 < q1 := lt_min (Real.rpow_pos_of_pos ha0 _) (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨e2 * q2 / 1, e1 * q1 / 4, r, by positivity, hrpos, fun z hz hz1 hzr => ?_⟩
  have hdist1 : ‖z - 1‖ < δ1 := hzr.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hdist2 : ‖z - 1‖ < δ2 := hzr.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hdist3 : ‖z - 1‖ < 1 := hzr.trans_le (min_le_right _ _)
  have hzI : z ≠ Complex.I := by
    intro h; rw [h] at hdist3
    have h1 : (1 : ℝ) ≤ ‖Complex.I - 1‖ := by
      have := Complex.abs_im_le_norm (Complex.I - 1)
      simpa using this
    linarith
  have hzI' : z ≠ -Complex.I := by
    intro h; rw [h] at hdist3
    have h1 : (1 : ℝ) ≤ ‖-Complex.I - 1‖ := by
      have := Complex.abs_im_le_norm (-Complex.I - 1)
      simpa using this
    linarith
  have hzD : z ∈ closure halfDisc \ singPts := ⟨hz, fun h => by
    simp only [singPts, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h <;> tauto⟩
  have hzc : z ∈ closure halfDisc \ {Complex.I, -Complex.I} := sing_subset hzD
  have hstrip : sInv z ∈ closedStrip := sInv_mem_closedStrip' hzD
  have hE1 : e1 ≤ Real.exp (hbarA (aWA w A) (sInv z)).re :=
    Real.exp_le_exp.mpr (re_hbarA_ge (amp_aWA w hA) hm hstrip)
  have him : |(sInv z).im| < 1 := by
    have h1 := hS hzc (by simpa [dist_eq_norm] using hdist1)
    rw [dist_eq_norm, sInv_one] at h1
    have him' : |(sInv z - 1).im| ≤ ‖sInv z - 1‖ := Complex.abs_im_le_norm _
    have him'' : (sInv z - 1).im = (sInv z).im := by simp
    rw [him''] at him'
    linarith
  have hE2 : Real.exp (hbarA (aWA w A) (sInv z)).re ≤ e2 :=
    Real.exp_le_exp.mpr (by nlinarith [hκ (sInv z) hstrip, Real.pi_pos])
  have hqd : ‖qBd z - qBd 1‖ < ‖qBd 1‖ / 2 := by
    simpa [dist_eq_norm] using hQ hzc (by simpa [dist_eq_norm] using hdist2)
  have hqn1 : a ≤ ‖qBd z‖ := by
    have := norm_sub_norm_le (qBd 1) (qBd z)
    rw [norm_sub_rev] at this
    dsimp only [a]; linarith
  have hqn2 : ‖qBd z‖ ≤ b := by
    have := norm_sub_norm_le (qBd z) (qBd 1)
    dsimp only [b]; linarith
  have hQb := rpow_between p ha0 hqn1 hqn2
  have hD := one_le_norm_one_add hz
  have hD2 := norm_one_add_le hz
  have hDD : (1 : ℝ) ≤ ‖1 + z‖ ^ 2 ∧ ‖1 + z‖ ^ 2 ≤ 4 :=
    ⟨by nlinarith, by nlinarith [norm_nonneg (1 + z)]⟩
  have hpb := prod_bounds (E := Real.exp (hbarA (aWA w A) (sInv z)).re)
    (Q := ‖qBd z‖ ^ p) (D := ‖1 + z‖ ^ 2) (e1 := e1) (e2 := e2) (q1 := q1) (q2 := q2)
    (d1 := 1) (d2 := 4) (Real.exp_pos _) hq1pos one_pos ⟨hE1, hE2⟩ hQb hDD
  rw [norm_goutWA w A hzD, norm_sub_rev z 1]
  have hN : 0 ≤ ‖1 - z‖ ^ (1 / 2 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have hgeq : Real.exp (hbarA (aWA w A) (sInv z)).re * ‖1 - z‖ ^ (1 / 2 : ℝ) / ‖1 + z‖ ^ 2 *
      ‖qBd z‖ ^ p =
      (Real.exp (hbarA (aWA w A) (sInv z)).re * ‖qBd z‖ ^ p / ‖1 + z‖ ^ 2) * ‖1 - z‖ ^ (1 / 2 : ℝ) := by
    ring
  rw [hgeq]
  exact ⟨mul_le_mul_of_nonneg_right hpb.1 hN, mul_le_mul_of_nonneg_right hpb.2 hN⟩

lemma goutWA_near_I (w : ℕ) {A : ℝ → ℝ} (hA : JetAmplitude A) :
    ∃ C c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ z ∈ closure halfDisc, z ≠ Complex.I → z ≠ -Complex.I →
      (‖z - Complex.I‖ < r ∨ ‖z + Complex.I‖ < r) →
      c ≤ ‖GoutWA w A z‖ ∧ ‖GoutWA w A z‖ ≤ C * ‖1 + z ^ 2‖ ^ (-(5 / 4 : ℝ)) := by
  obtain ⟨m, β, hm, hβ⟩ := aWA_bounds w hA
  obtain ⟨κ, hκ⟩ := re_hbarA_le (amp_aWA w hA) (α := 5 * π / 8) (β := β) (by positivity) hβ
  have hCq : 0 < 1 / Cq := div_pos one_pos Cq_pos
  set p : ℝ := -((2 * ((w - 1 : ℕ) : ℝ) + 1) / 4)
  set e1 : ℝ := Real.exp m * (11 / 12) ^ (1 / 2 : ℝ)
  set n2 : ℝ := (2 : ℝ) ^ (1 / 2 : ℝ)
  set q1 : ℝ := min ((1 / Cq) ^ p) (Cq ^ p)
  set q2 : ℝ := max ((1 / Cq) ^ p) (Cq ^ p)
  have hq1pos : 0 < q1 := lt_min (Real.rpow_pos_of_pos hCq _) (Real.rpow_pos_of_pos Cq_pos _)
  have hn1pos : 0 < (11 / 12 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨Real.exp (β + 5 * π / 8 * κ) * 4 ^ (5 / 4 : ℝ) * n2 * q2, e1 * q1 / 4, 1 / 12,
    by positivity, by norm_num, fun z hz hzI hzI' hr => ?_⟩
  have hz1 : z ≠ 1 := by
    intro h; rw [h] at hr
    rcases hr with h | h
    · have h1 : (1 : ℝ) ≤ ‖(1 : ℂ) - Complex.I‖ := by
        have := Complex.abs_im_le_norm ((1 : ℂ) - Complex.I)
        simpa using this
      linarith
    · have h1 : (1 : ℝ) ≤ ‖(1 : ℂ) + Complex.I‖ := by
        have := Complex.abs_im_le_norm ((1 : ℂ) + Complex.I)
        simpa using this
      linarith
  have hzD : z ∈ closure halfDisc \ singPts := ⟨hz, fun h => by
    simp only [singPts, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h <;> tauto⟩
  have hstrip := sInv_mem_closedStrip' hzD
  have h1z2 : ‖1 + z ^ 2‖ > 0 := norm_pos_iff.mpr (fun h => by
    have hsq : (z - Complex.I) * (z + Complex.I) = 1 + z ^ 2 := by
      ring_nf; rw [Complex.I_sq]; ring
    rw [h] at hsq
    rcases mul_eq_zero.mp hsq with h0 | h0
    · exact hzI (sub_eq_zero.mp h0)
    · exact hzI' (eq_neg_of_add_eq_zero_left h0))
  have hsz : sTan (sInv z) = z := sTan_sInv hzI hzI'
  have hE1 : Real.exp m ≤ Real.exp (hbarA (aWA w A) (sInv z)).re :=
    Real.exp_le_exp.mpr (re_hbarA_ge (amp_aWA w hA) hm hstrip)
  have hE2 : Real.exp (hbarA (aWA w A) (sInv z)).re ≤
      Real.exp (β + 5 * π / 8 * κ) * (4 ^ (5 / 4 : ℝ) * ‖1 + z ^ 2‖ ^ (-(5 / 4) : ℝ)) := by
    have hb : ‖1 + sTan (sInv z) ^ 2‖ ≤ 4 * Real.exp (-(π * |(sInv z).im| / 2)) :=
      norm_one_add_sTan_sq_le hstrip
    rw [hsz] at hb
    have hexp := exp_mul_le_rpow h1z2 hb
    calc Real.exp (hbarA (aWA w A) (sInv z)).re
        ≤ Real.exp (5 * π / 8 * |(sInv z).im| + (β + 5 * π / 8 * κ)) :=
          Real.exp_le_exp.mpr (by nlinarith [hκ (sInv z) hstrip])
      _ = Real.exp (5 * π / 8 * |(sInv z).im|) * Real.exp (β + 5 * π / 8 * κ) := Real.exp_add _ _
      _ ≤ (4 ^ (5 / 4 : ℝ) * ‖1 + z ^ 2‖ ^ (-(5 / 4) : ℝ)) * Real.exp (β + 5 * π / 8 * κ) :=
          mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
      _ = Real.exp (β + 5 * π / 8 * κ) * (4 ^ (5 / 4 : ℝ) * ‖1 + z ^ 2‖ ^ (-(5 / 4) : ℝ)) := by ring
  have hsub1 : 11 / 12 ≤ ‖1 - z‖ := by
    have hsq2 : (1 : ℝ) < √2 := by
      rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rcases hr with h | h
    · have h2 : ‖1 - Complex.I‖ = √2 := by
        have : (1 : ℂ) - Complex.I = (1 : ℝ) + ((-1 : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [this, Complex.norm_add_mul_I]; norm_num
      have ht := norm_sub_le (1 - Complex.I) (z - Complex.I)
      have heq : (1 - Complex.I) - (z - Complex.I) = 1 - z := by ring
      rw [heq] at ht
      have := norm_sub_norm_le (1 - Complex.I) (z - Complex.I)
      rw [heq, h2] at this
      linarith
    · have h2 : ‖1 + Complex.I‖ = √2 := by
        have : (1 : ℂ) + Complex.I = (1 : ℝ) + (1 : ℝ) * Complex.I := by push_cast; ring
        rw [this, Complex.norm_add_mul_I]; norm_num
      have heq : (1 + Complex.I) - (z + Complex.I) = 1 - z := by ring
      have := norm_sub_norm_le (1 + Complex.I) (z + Complex.I)
      rw [heq, h2] at this
      linarith
  have hsub2 := norm_one_sub_le hz
  have hNb := rpow_between (1 / 2 : ℝ) (by norm_num : (0 : ℝ) < 11 / 12) hsub1 hsub2
  have hN1 : (11 / 12 : ℝ) ^ (1 / 2 : ℝ) ≤ ‖1 - z‖ ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) hsub1 (by norm_num)
  have hN2 : ‖1 - z‖ ^ (1 / 2 : ℝ) ≤ n2 :=
    Real.rpow_le_rpow (norm_nonneg _) hsub2 (by norm_num)
  have hqb := norm_qBd_bounds_near_I hz hzI hzI' hr
  have hQb := rpow_between p hCq hqb.1 hqb.2
  have hD := one_le_norm_one_add hz
  have hD2 := norm_one_add_le hz
  have hDD : (1 : ℝ) ≤ ‖1 + z‖ ^ 2 ∧ ‖1 + z‖ ^ 2 ≤ 4 :=
    ⟨by nlinarith, by nlinarith [norm_nonneg (1 + z)]⟩
  have hEN1 : Real.exp m * (11 / 12) ^ (1 / 2 : ℝ) ≤
      Real.exp (hbarA (aWA w A) (sInv z)).re * ‖1 - z‖ ^ (1 / 2 : ℝ) :=
    mul_le_mul hE1 hN1 hn1pos.le (Real.exp_pos _).le
  have hEN2 : Real.exp (hbarA (aWA w A) (sInv z)).re * ‖1 - z‖ ^ (1 / 2 : ℝ) ≤
      Real.exp (β + 5 * π / 8 * κ) * (4 ^ (5 / 4 : ℝ) * ‖1 + z ^ 2‖ ^ (-(5 / 4) : ℝ)) * n2 :=
    mul_le_mul hE2 hN2 (Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
  have hpb := prod_bounds (E := Real.exp (hbarA (aWA w A) (sInv z)).re * ‖1 - z‖ ^ (1 / 2 : ℝ))
    (Q := ‖qBd z‖ ^ p) (D := ‖1 + z‖ ^ 2) (e1 := e1)
    (e2 := Real.exp (β + 5 * π / 8 * κ) * (4 ^ (5 / 4 : ℝ) * ‖1 + z ^ 2‖ ^ (-(5 / 4) : ℝ)) * n2)
    (q1 := q1) (q2 := q2) (d1 := 1) (d2 := 4) (by positivity) hq1pos one_pos ⟨hEN1, hEN2⟩ hQb hDD
  rw [norm_goutWA w A hzD]
  have hgeq : Real.exp (hbarA (aWA w A) (sInv z)).re * ‖1 - z‖ ^ (1 / 2 : ℝ) / ‖1 + z‖ ^ 2 *
      ‖qBd z‖ ^ p =
      (Real.exp (hbarA (aWA w A) (sInv z)).re * ‖1 - z‖ ^ (1 / 2 : ℝ)) * ‖qBd z‖ ^ p /
        ‖1 + z‖ ^ 2 := by ring
  rw [hgeq]
  refine ⟨hpb.1, ?_⟩
  calc (Real.exp (hbarA (aWA w A) (sInv z)).re * ‖1 - z‖ ^ (1 / 2 : ℝ)) * ‖qBd z‖ ^ p / ‖1 + z‖ ^ 2
      ≤ (Real.exp (β + 5 * π / 8 * κ) * (4 ^ (5 / 4 : ℝ) * ‖1 + z ^ 2‖ ^ (-(5 / 4) : ℝ)) * n2) *
          q2 / 1 := hpb.2
    _ = Real.exp (β + 5 * π / 8 * κ) * 4 ^ (5 / 4 : ℝ) * n2 * q2 * ‖1 + z ^ 2‖ ^ (-(5 / 4 : ℝ)) := by
        ring

end FormalResearch.ModularBootstrap.Mixtures

