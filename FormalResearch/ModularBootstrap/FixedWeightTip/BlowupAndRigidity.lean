module

public import FormalResearch.ModularBootstrap.FixedWeightTip.PropositionP
public import FormalResearch.ModularBootstrap.Blowup.PropositionT
public import FormalResearch.ModularBootstrap.TipFront.ConcreteBlowup
public import FormalResearch.ModularBootstrap.FixedWeight.OptimalMeasure

/-!
# General-`(w, Q)` Blow-up, Proposition T, Theorem C, and Rigidity Theorem R (`blowup_limit.tex`, `rigidity.tex`)

Formalizes the blow-up limit and rigidity chain at every fixed `(w, Q)` (`prob : FixedWeightProblem`):
* `FixedBlowupTest`, `FixedBlowupTest.ofWeaklyFeasible` (`blowupTest_of_concrete_general`),
  `FixedBlowupTest.nonempty`: general-`(w, Q)` blow-up tests constructed from any weakly feasible
  functional `prob.IsWeaklyFeasible (c' / 12) T g`.
* `tipRescaleW`: general-`(w, Q)` rescaled strip functional
  `Φ_c(ζ) = W_{w,Q}(b(ζ)) G(b(ζ)) / M[g]`, holomorphic on horizontal strips `{|Im ζ| < 1 / (2 ε)}`
  for `c' ≥ c₀_H`, real on `ℝ`, Schwarz reflection symmetric, and satisfying the mass/vacuum/half-mass
  identities on `(tipSMin c', ∞)`.
* `lemma_T5_general`, `tipRescaleW_pointwise_envelope`, `blowup_left_tail_bound_general`:
  general-`(w, Q)` Lemma `T5` (`bl:T5`), uniform disc-averaged pointwise bounds, and uniform
  left-tail control using `D.lemmaG` + `W_C_prob_norm_le`.
* `tipS₁W_theorem_A_lower_general`: unconditional `s₁ ≥ -C₀` from `theorem_A_general` (and
  compatibility lemma `theorem_A_lower_from_lowerBoundInput` comparing with
  `FixedWeight.FixedWeightLowerBoundInput prob` / Theorem `W1'(1)`).
* `proposition_T_general`, `proposition_T_of_problem`: full **Proposition T** (`bl:T`) (i)–(vi) at
  general `(w, Q)`.
* `blowupFamilyPackage_of_concrete_tests_general`, `rigidityFamilyPackage_of_concrete_tests_general`,
  `concrete_blowup_theorem_C_general`, `concrete_blowup_theorem_R1_general`,
  `concrete_blowup_theorem_R2_general`, `concrete_blowup_theorem_R3_general`,
  `att_of_upper_threshold_general`: unconditional general-`(w, Q)` **Theorem C** and
  **Theorem R `(R1)`–`(R3)`** under `Att`, together with `*_of_problem` wrappers.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.FixedWeightTip

open Crossing PoissonJensen WeightAxioms TipFront FixedWeight
open FormalResearch.Special FormalResearch.ArgPrinciple FormalResearch.Analysis

/-! ### Section 1: Concrete `FixedBlowupTest` and `tipRescaleW` at general `(w, Q)` -/

/-- Concrete per-test interface for weakly feasible fixed-weight bootstrap functionals at `c'`. -/
structure FixedBlowupTest (prob : FixedWeightProblem) (c' : ℝ) where
  g : ℝ → ℝ
  t₁ : ℝ
  ht₁_nonneg : 0 ≤ t₁
  ht₁_least : t₁ = leastThreshold g
  hg_nonneg_tail : ∀ t : ℝ, t₁ ≤ t → 0 ≤ g t
  hg_test : TestClass prob (c' / 12) g
  hnonzero : ∃ t ≥ 0, g t ≠ 0
  hgVac_nonneg : 0 ≤ prob.gVac (c' / 12) g
  hM_pos : 0 < prob.cardyNorm (c' / 12) g

noncomputable def FixedBlowupTest.M {prob : FixedWeightProblem} {c' : ℝ}
    (test : FixedBlowupTest prob c') : ℝ :=
  prob.cardyNorm (c' / 12) test.g

noncomputable def FixedBlowupTest.gVac {prob : FixedWeightProblem} {c' : ℝ}
    (test : FixedBlowupTest prob c') : ℝ :=
  prob.gVac (c' / 12) test.g

noncomputable def FixedBlowupTest.x₁ {prob : FixedWeightProblem} (c' : ℝ)
    (test : FixedBlowupTest prob c') : ℝ :=
  Real.sqrt (3 * test.t₁ / c')

noncomputable def tipS₁W {prob : FixedWeightProblem} (c' : ℝ)
    (test : FixedBlowupTest prob c') : ℝ :=
  (test.x₁ c' - xiStar) / tipEps c'

lemma FixedBlowupTest.t₁_eq_x₁_sq {prob : FixedWeightProblem} {c' : ℝ} (hc' : 0 < c')
    (test : FixedBlowupTest prob c') :
    test.t₁ = c' * (test.x₁ c') ^ 2 / 3 := by
  unfold FixedBlowupTest.x₁
  have hnn : 0 ≤ 3 * test.t₁ / c' := by positivity [test.ht₁_nonneg]
  rw [Real.sq_sqrt hnn]
  field_simp [hc'.ne']

lemma tipS₁W_scaling_eq {prob : FixedWeightProblem} {c' : ℝ} (hc' : 0 < c')
    (test : FixedBlowupTest prob c') :
    test.t₁ = xiBar * c' + (2 / 3 : ℝ) * xiStar * c' ^ (1 / 3 : ℝ) * tipS₁W c' test +
      (1 / 3 : ℝ) * c' ^ (-(1 / 3 : ℝ)) * (tipS₁W c' test) ^ 2 := by
  have hx₁ : test.x₁ c' = xiStar + tipEps c' * tipS₁W c' test := by
    unfold tipS₁W
    have hε : tipEps c' ≠ 0 := (tipEps_pos hc').ne'
    field_simp [hε]; ring
  have hce : c' * tipEps c' = c' ^ (1 / 3 : ℝ) := by
    unfold tipEps
    calc c' * c' ^ (-(2 / 3 : ℝ)) = c' ^ (1 : ℝ) * c' ^ (-(2 / 3 : ℝ)) := by rw [Real.rpow_one]
      _ = c' ^ (1 + -(2 / 3 : ℝ)) := (Real.rpow_add hc' _ _).symm
      _ = c' ^ (1 / 3 : ℝ) := by norm_num
  have hce2 : c' * tipEps c' ^ 2 = c' ^ (-(1 / 3 : ℝ)) := by
    unfold tipEps
    calc c' * (c' ^ (-(2 / 3 : ℝ))) ^ 2
        = c' ^ (1 : ℝ) * c' ^ (-(4 / 3 : ℝ)) := by
            rw [Real.rpow_one, ← Real.rpow_natCast (c' ^ (-(2 / 3 : ℝ))) 2,
              ← Real.rpow_mul hc'.le]
            norm_num
      _ = c' ^ (-(1 / 3 : ℝ)) := by
          rw [← Real.rpow_add hc']; norm_num
  rw [test.t₁_eq_x₁_sq hc', hx₁]
  unfold xiBar
  rw [show c' * (xiStar + tipEps c' * tipS₁W c' test) ^ 2 / 3 =
      xiStar ^ 2 / 3 * c' + (2 / 3 : ℝ) * xiStar * (c' * tipEps c') * tipS₁W c' test +
        (1 / 3 : ℝ) * (c' * tipEps c' ^ 2) * (tipS₁W c' test) ^ 2 by ring,
    hce, hce2]

lemma FixedBlowupTest.isWeaklyFeasible {prob : FixedWeightProblem} {c' : ℝ}
    (test : FixedBlowupTest prob c') :
    prob.IsWeaklyFeasible (c' / 12) test.t₁ test.g :=
  ⟨test.hg_test, test.hnonzero, test.hgVac_nonneg, test.hg_nonneg_tail⟩

/-- Construct a `FixedBlowupTest prob c'` from any concrete weakly feasible test at `(c', T)`. -/
noncomputable def blowupTest_of_concrete_general {prob : FixedWeightProblem} {c' T : ℝ}
    (hc' : prob.totalShift ≤ c' / 12) {g : ℝ → ℝ}
    (hwf : prob.IsWeaklyFeasible (c' / 12) T g) :
    FixedBlowupTest prob c' where
  g := g
  t₁ := leastThreshold g
  ht₁_nonneg := leastThreshold_nonneg g
  ht₁_least := rfl
  hg_nonneg_tail := leastThreshold_tail hwf.1.cont hwf.2.2.2
  hg_test := hwf.1
  hnonzero := hwf.2.1
  hgVac_nonneg := hwf.2.2.1
  hM_pos := cardyNorm_pos_of_nonzero_general prob hc' hwf.1 hwf.2.1

private lemma shift_div12_of_mul24 {prob : FixedWeightProblem} {c' : ℝ}
    (hc' : 24 * prob.totalShift ≤ c') : prob.totalShift ≤ c' / 12 := by
  linarith [prob.totalShift_nonneg]

/-- Non-vacuity of `FixedBlowupTest prob c'` for all `c' > 0` with `c' ≥ 24 * prob.totalShift`. -/
theorem fixedBlowupTest_nonempty (prob : FixedWeightProblem) {c' : ℝ}
    (_hc'_pos : 0 < c') (hc'_shift : 24 * prob.totalShift ≤ c') :
    Nonempty (FixedBlowupTest prob c') := by
  have ha_shift : prob.totalShift ≤ c' / 12 := shift_div12_of_mul24 hc'_shift
  obtain ⟨T, _, g, hg⟩ := prob.feasible_nonempty (by linarith [prob.totalShift_nonneg] : 12 * prob.totalShift ≤ c')
  exact ⟨blowupTest_of_concrete_general ha_shift hg.isWeaklyFeasible⟩

/-- Rescaled complex tip functional at fixed `(w, Q)`:
`Φ_c(ζ) = W_{w,Q}(b(ζ)) · G(b(ζ)) / M[g]`, where `b(ζ) = ξ_* + ε ζ`. -/
noncomputable def tipRescaleW (prob : FixedWeightProblem) (c' : ℝ) (g : ℝ → ℝ) (ζ : ℂ) : ℂ :=
  W_C_prob prob c' (bScale c' ζ) * hankelContinuationW prob.w c' g (bScale c' ζ) /
    (prob.cardyNorm (c' / 12) g : ℂ)

lemma hankelContinuationW_ofReal_all {prob : FixedWeightProblem} {c' : ℝ} (hc' : 0 < c')
    {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g) (b : ℝ) :
    hankelContinuationW prob.w c' g (b : ℂ) = (g (c' * b ^ 2 / 3) : ℂ) :=
  WeightAxioms.hankelContinuationW_ofReal prob.hw hc' hg.cont hg.int_lift hg.fourier_odd b

lemma tipRescaleW_real_on_real {prob : FixedWeightProblem} {c' : ℝ} (hc' : 0 < c')
    {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g) (s : ℝ) :
    tipRescaleW prob c' g (s : ℂ) =
      ((tipEps c' * (2 * c' / 3) * tipBReal c' s *
        prob.cardyV (c' / 12) (tipTReal c' s) * g (tipTReal c' s) /
        prob.cardyNorm (c' / 12) g : ℝ) : ℂ) := by
  unfold tipRescaleW W_C_prob tipTReal
  rw [bScale_ofReal]
  have ht_cast : ((c' : ℂ) * ((tipBReal c' s : ℝ) : ℂ) ^ 2 / 3) =
      (((c' * tipBReal c' s ^ 2 / 3 : ℝ) : ℂ)) := by push_cast; ring
  rw [ht_cast, cardyVC_ofReal, hankelContinuationW_ofReal_all hc' hg (tipBReal c' s)]
  push_cast; ring

lemma tipRescaleW_im_eq_zero {prob : FixedWeightProblem} {c' : ℝ} (hc' : 0 < c')
    {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g) (s : ℝ) :
    (tipRescaleW prob c' g (s : ℂ)).im = 0 := by
  rw [tipRescaleW_real_on_real hc' hg s, Complex.ofReal_im]

lemma W_C_prob_entire (prob : FixedWeightProblem) (c' : ℝ) :
    Differentiable ℂ (W_C_prob prob c') := by
  intro b
  have h1 : DifferentiableAt ℂ
      (fun z : ℂ => ((tipEps c' : ℝ) : ℂ) * ((2 * c' / 3 : ℝ) : ℂ) * z) b :=
    ((differentiableAt_const _).mul (differentiableAt_const _)).mul differentiableAt_id
  have h2 : DifferentiableAt ℂ
      (fun z : ℂ => cardyVC prob (c' / 12) ((c' : ℂ) * z ^ 2 / 3)) b :=
    (cardyVC_entire prob (c' / 12) _).comp b
      (((differentiableAt_const _).mul (differentiableAt_id.pow 2)).div_const _)
  exact h1.mul h2

/-- Holomorphicity of `tipRescaleW` on `{ζ : ℂ | |ζ.im| < 1 / (2 * ε)}` for `c' ≥ c₀_H`. -/
theorem tipRescaleW_holo_exists (prob : FixedWeightProblem) :
    ∃ c₀_H : ℝ, max 1 (24 * prob.totalShift) ≤ c₀_H ∧
      ∀ {c' : ℝ} {g : ℝ → ℝ}, c₀_H ≤ c' → TestClass prob (c' / 12) g →
        DifferentiableOn ℂ (tipRescaleW prob c' g) {ζ : ℂ | |ζ.im| < 1 / (2 * tipEps c')} := by
  obtain ⟨c₀_H, hc₀_ge, hdiff⟩ := WeightAxioms.differentiableOn_hankelContinuationW prob
  refine ⟨c₀_H, hc₀_ge, fun {c' g} hc' hg => ?_⟩
  have hc'_pos : 0 < c' := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans (hc₀_ge.trans hc'))
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'_pos
  have hb_entire : Differentiable ℂ (bScale c') := by
    unfold bScale
    exact (differentiable_const _).add ((differentiable_const _).mul differentiable_id)
  have hW : DifferentiableOn ℂ (fun ζ => W_C_prob prob c' (bScale c' ζ))
      {ζ : ℂ | |ζ.im| < 1 / (2 * tipEps c')} := fun ζ _ =>
    ((W_C_prob_entire prob c' (bScale c' ζ)).comp ζ (hb_entire ζ)).differentiableWithinAt
  have hG : DifferentiableOn ℂ (fun ζ => hankelContinuationW prob.w c' g (bScale c' ζ))
      {ζ : ℂ | |ζ.im| < 1 / (2 * tipEps c')} := by
    refine (hdiff hc' hg).comp hb_entire.differentiableOn fun ζ hζ => ?_
    rw [mem_ofPred_eq] at hζ ⊢
    have him : (bScale c' ζ).im = tipEps c' * ζ.im := by
      unfold bScale; simp [Complex.add_im, Complex.mul_im]
    rw [him, abs_mul, abs_of_pos hε_pos]
    have hlt : |ζ.im| * (2 * tipEps c') < 1 :=
      (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * tipEps c')).mp hζ
    linarith
  intro ζ hζ
  unfold tipRescaleW
  exact (((hW ζ hζ).mul (hG ζ hζ)).div_const _)

lemma tipRescaleW_holo_ball {prob : FixedWeightProblem} {c' R : ℝ} (hc' : 0 < c')
    (hR : 2 * R * tipEps c' < 1) {g : ℝ → ℝ}
    (hholo : DifferentiableOn ℂ (tipRescaleW prob c' g) {ζ : ℂ | |ζ.im| < 1 / (2 * tipEps c')}) :
    DifferentiableOn ℂ (tipRescaleW prob c' g) (ball 0 R) := by
  refine hholo.mono fun ζ hζ => ?_
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'
  have him : |ζ.im| < R := (Complex.abs_im_le_norm ζ).trans_lt (mem_ball_zero_iff.mp hζ)
  rw [mem_ofPred_eq, lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * tipEps c')]
  nlinarith

lemma tipRescaleW_real_symm {prob : FixedWeightProblem} {c' : ℝ} (hc' : 0 < c')
    {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    (hholo : DifferentiableOn ℂ (tipRescaleW prob c' g) {ζ : ℂ | |ζ.im| < 1 / (2 * tipEps c')})
    {ζ : ℂ} (hζ : |ζ.im| < 1 / (2 * tipEps c')) :
    tipRescaleW prob c' g (starRingEnd ℂ ζ) = starRingEnd ℂ (tipRescaleW prob c' g ζ) := by
  let S : Set ℂ := {w : ℂ | |w.im| < 1 / (2 * tipEps c')}
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'
  have hL_pos : 0 < 1 / (2 * tipEps c') := by positivity
  have hS_open : IsOpen S := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hS_conv : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    rw [mem_ofPred_eq] at hx hy ⊢
    let m : ℝ := max |x.im| |y.im|
    have hm_lt : m < 1 / (2 * tipEps c') := max_lt hx hy
    have him_eq : (a • x + b • y).im = a * x.im + b * y.im := by simp
    rw [him_eq]
    calc |a * x.im + b * y.im|
        ≤ |a * x.im| + |b * y.im| := abs_add_le _ _
      _ = a * |x.im| + b * |y.im| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * m + b * m := add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
      _ = m := by linear_combination m * hab
      _ < 1 / (2 * tipEps c') := hm_lt
  have hS_conj : ∀ w ∈ S, starRingEnd ℂ w ∈ S := fun w hw => by
    simpa [S, Complex.conj_im] using hw
  let conjPhi : ℂ → ℂ := fun w => starRingEnd ℂ (tipRescaleW prob c' g (starRingEnd ℂ w))
  have hconj : DifferentiableOn ℂ conjPhi S := fun w hw => by
    have hw' := hS_conj w hw
    have hd := (hholo.differentiableAt (hS_open.mem_nhds hw')).conj_conj
    simp only [Complex.conj_conj] at hd
    exact hd.differentiableWithinAt
  have h0S : (0 : ℂ) ∈ S := by simpa [S] using hL_pos
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), tipRescaleW prob c' g w = conjPhi w := by
    rw [Filter.frequently_iff]
    intro U hU
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    obtain ⟨r, hr_pos, hr_ball⟩ := Metric.mem_nhds_iff.mp hV
    let δ : ℝ := min (r / 2) (1 / (4 * tipEps c'))
    have hδ_pos : 0 < δ := lt_min (by positivity) (by positivity)
    refine ⟨(δ : ℂ), hVU ⟨hr_ball ?_, ?_⟩, ?_⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ_pos]
      exact (min_le_left _ _).trans_lt (half_lt_self hr_pos)
    · exact Complex.ofReal_ne_zero.mpr hδ_pos.ne'
    · dsimp [conjPhi]
      rw [Complex.conj_ofReal, tipRescaleW_real_on_real hc' hg δ, Complex.conj_ofReal]
  have heq : EqOn (tipRescaleW prob c' g) conjPhi S :=
    AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
      (hholo.analyticOnNhd hS_open) (hconj.analyticOnNhd hS_open) hS_conv.isPreconnected h0S hfreq
  have hζc : starRingEnd ℂ ζ ∈ S := hS_conj ζ hζ
  have he := heq hζc
  dsimp [conjPhi] at he
  simpa only [Complex.conj_conj] using he

lemma tipRescaleW_integrableOn_domain {prob : FixedWeightProblem} {c' : ℝ} (hc' : 0 < c')
    (hc'_shift : prob.totalShift ≤ c' / 12) (test : FixedBlowupTest prob c') :
    IntegrableOn (fun s : ℝ => tipRescaleW prob c' test.g (s : ℂ)) (Ioi (tipSMin c')) := by
  have him : tipTReal c' '' Ioi (tipSMin c') = Ioi 0 := by
    have ht0 : tipTReal c' (tipSMin c') = 0 := by
      unfold tipTReal tipBReal
      rw [tipSMin_eq_neg_div_tipEps hc']
      field_simp [(tipEps_pos hc').ne']; ring
    rw [tipTReal_image_Ioi hc' le_rfl, ht0]
  have hM_pos : 0 < test.M := test.hM_pos
  have hint_t : IntegrableOn (fun t => test.g t * prob.cardyV (c' / 12) t * (test.M)⁻¹) (Ioi 0) := by
    have hV_nn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ prob.cardyV (c' / 12) t := fun t ht =>
      prob.cardyV_nonneg hc'_shift (mem_Ioi.mp ht).le
    refine (test.hg_test.int_cardy.mul_const (test.M)⁻¹).mono' ?_ ?_
    · exact (((test.hg_test.cont.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono
        Ioi_subset_Ici_self).mul continuousOn_const).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hMinv : |(test.M)⁻¹| = (test.M)⁻¹ := abs_of_nonneg (inv_nonneg.mpr hM_pos.le)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hV_nn t ht), hMinv]
  have hcomp := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun s _ => (tipTReal_deriv (c' := c') (s := s)).hasDerivWithinAt)
    (tipTReal_injOn hc') (fun t => test.g t * prob.cardyV (c' / 12) t * (test.M)⁻¹)).mp
    (by rwa [him])
  refine hcomp.ofReal.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have hder_nn : 0 ≤ tipEps c' * (2 * c' / 3) * tipBReal c' s :=
    mul_nonneg (mul_nonneg (tipEps_pos hc').le (by positivity))
      ((tipBReal_pos_iff hc').mpr hs).le
  have hscalar : tipEps c' * (2 * c' / 3) * tipBReal c' s *
      prob.cardyV (c' / 12) (tipTReal c' s) * test.g (tipTReal c' s) /
      prob.cardyNorm (c' / 12) test.g =
      |tipEps c' * (2 * c' / 3) * tipBReal c' s| •
        (test.g (tipTReal c' s) * prob.cardyV (c' / 12) (tipTReal c' s) * (test.M)⁻¹) := by
    rw [smul_eq_mul, abs_of_nonneg hder_nn, div_eq_mul_inv]
    unfold FixedBlowupTest.M; ring
  dsimp only
  rw [tipRescaleW_real_on_real hc' test.hg_test s, hscalar]
  rfl

theorem tipRescaleW_norm_integral {prob : FixedWeightProblem} {c' : ℝ} (hc' : 0 < c')
    (hc'_shift : prob.totalShift ≤ c' / 12) (test : FixedBlowupTest prob c') :
    ∫ s in Ioi (tipSMin c'), ‖tipRescaleW prob c' test.g (s : ℂ)‖ = 1 := by
  have him : tipTReal c' '' Ioi (tipSMin c') = Ioi 0 := by
    have ht0 : tipTReal c' (tipSMin c') = 0 := by
      unfold tipTReal tipBReal
      rw [tipSMin_eq_neg_div_tipEps hc']
      field_simp [(tipEps_pos hc').ne']; ring
    rw [tipTReal_image_Ioi hc' le_rfl, ht0]
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun s _ => (tipTReal_deriv (c' := c') (s := s)).hasDerivWithinAt)
    (tipTReal_injOn hc') (fun t => |test.g t| * prob.cardyV (c' / 12) t / test.M)
  rw [him] at hcov
  have heq : EqOn (fun s : ℝ => ‖tipRescaleW prob c' test.g (s : ℂ)‖)
      (fun s => |tipEps c' * (2 * c' / 3) * tipBReal c' s| •
        (|test.g (tipTReal c' s)| * prob.cardyV (c' / 12) (tipTReal c' s) / test.M))
      (Ioi (tipSMin c')) := fun s hs => by
    have hbs : 0 < tipBReal c' s := (tipBReal_pos_iff hc').mpr hs
    have hts : 0 < tipTReal c' s := by unfold tipTReal; positivity
    have hV_nn : 0 ≤ prob.cardyV (c' / 12) (tipTReal c' s) :=
      prob.cardyV_nonneg hc'_shift hts.le
    have h1_nn : 0 ≤ tipEps c' * (2 * c' / 3) := mul_nonneg (tipEps_pos hc').le (by positivity)
    have hder_nn : 0 ≤ tipEps c' * (2 * c' / 3) * tipBReal c' s := mul_nonneg h1_nn hbs.le
    dsimp only
    rw [tipRescaleW_real_on_real hc' test.hg_test s, Complex.norm_real, Real.norm_eq_abs,
      smul_eq_mul, abs_of_nonneg hder_nn, abs_div, abs_of_pos test.hM_pos, abs_mul,
      abs_mul, abs_mul, abs_of_nonneg h1_nn, abs_of_nonneg hbs.le, abs_of_nonneg hV_nn]
    unfold FixedBlowupTest.M; ring
  rw [setIntegral_congr_fun measurableSet_Ioi heq, ← hcov, integral_div]
  change prob.cardyNorm (c' / 12) test.g / test.M = 1
  exact div_self test.hM_pos.ne'

theorem tipRescaleW_integral_vac {prob : FixedWeightProblem} {c' : ℝ} (hc' : 0 < c')
    (test : FixedBlowupTest prob c') :
    ∫ s in Ioi (tipSMin c'), (tipRescaleW prob c' test.g (s : ℂ)).re =
      -test.gVac / (2 * π * test.M) := by
  have him : tipTReal c' '' Ioi (tipSMin c') = Ioi 0 := by
    have ht0 : tipTReal c' (tipSMin c') = 0 := by
      unfold tipTReal tipBReal
      rw [tipSMin_eq_neg_div_tipEps hc']
      field_simp [(tipEps_pos hc').ne']; ring
    rw [tipTReal_image_Ioi hc' le_rfl, ht0]
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun s _ => (tipTReal_deriv (c' := c') (s := s)).hasDerivWithinAt)
    (tipTReal_injOn hc') (fun t => test.g t * prob.cardyV (c' / 12) t / test.M)
  rw [him] at hcov
  have heq : EqOn (fun s : ℝ => (tipRescaleW prob c' test.g (s : ℂ)).re)
      (fun s => |tipEps c' * (2 * c' / 3) * tipBReal c' s| •
        (test.g (tipTReal c' s) * prob.cardyV (c' / 12) (tipTReal c' s) / test.M))
      (Ioi (tipSMin c')) := fun s hs => by
    have hbs : 0 < tipBReal c' s := (tipBReal_pos_iff hc').mpr hs
    have hder_nn : 0 ≤ tipEps c' * (2 * c' / 3) * tipBReal c' s := by positivity [tipEps_pos hc']
    dsimp only
    rw [tipRescaleW_real_on_real hc' test.hg_test s, Complex.ofReal_re, smul_eq_mul,
      abs_of_nonneg hder_nn]
    unfold FixedBlowupTest.M; ring
  have hvac_int : ∫ t in Ioi 0, test.g t * prob.cardyV (c' / 12) t = -test.gVac / (2 * π) := by
    unfold FixedBlowupTest.gVac FixedWeightProblem.gVac
    field_simp [Real.pi_pos.ne']
  rw [setIntegral_congr_fun measurableSet_Ioi heq, ← hcov, integral_div, hvac_int]
  ring

lemma tipRescaleW_nonneg_tail {prob : FixedWeightProblem} {c' : ℝ} (hc' : 0 < c')
    (hc'_shift : prob.totalShift ≤ c' / 12) (test : FixedBlowupTest prob c')
    (s : ℝ) (hs : tipS₁W c' test ≤ s) :
    0 ≤ (tipRescaleW prob c' test.g (s : ℂ)).re := by
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'
  have hx₁_nn : 0 ≤ test.x₁ c' := Real.sqrt_nonneg _
  have hbs_ge : test.x₁ c' ≤ tipBReal c' s := by
    have h1 : tipEps c' * tipS₁W c' test ≤ tipEps c' * s := mul_le_mul_of_nonneg_left hs hε_pos.le
    unfold tipS₁W at h1
    rw [mul_div_cancel₀ _ hε_pos.ne'] at h1
    unfold tipBReal; linarith
  have hbs_nn : 0 ≤ tipBReal c' s := hx₁_nn.trans hbs_ge
  have hts_ge : test.t₁ ≤ tipTReal c' s := by
    rw [test.t₁_eq_x₁_sq hc']
    unfold tipTReal
    have : (test.x₁ c') ^ 2 ≤ (tipBReal c' s) ^ 2 := by nlinarith
    gcongr
  rw [tipRescaleW_real_on_real hc' test.hg_test s, Complex.ofReal_re]
  have ht_nn : 0 ≤ tipTReal c' s := by unfold tipTReal; positivity
  exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg hε_pos.le (by positivity)) hbs_nn)
    (prob.cardyV_nonneg hc'_shift ht_nn)) (test.hg_nonneg_tail _ hts_ge)) test.hM_pos.le

theorem tipRescaleW_half_neg_mass {prob : FixedWeightProblem} {c' : ℝ} (hc' : 0 < c')
    (hc'_shift : prob.totalShift ≤ c' / 12) (test : FixedBlowupTest prob c') :
    (1 / 2 : ℝ) ≤ ∫ s in Ioc (tipSMin c') (tipS₁W c' test),
      max 0 (-(tipRescaleW prob c' test.g (s : ℂ)).re) := by
  let f : ℝ → ℝ := fun s => (tipRescaleW prob c' test.g (s : ℂ)).re
  let fneg : ℝ → ℝ := fun s => max 0 (-f s)
  have hM_pos : 0 < test.M := test.hM_pos
  have hdom : IntegrableOn (fun s : ℝ => tipRescaleW prob c' test.g (s : ℂ)) (Ioi (tipSMin c')) :=
    tipRescaleW_integrableOn_domain hc' hc'_shift test
  have hf_int : IntegrableOn f (Ioi (tipSMin c')) := hdom.re
  have hfnorm_int : IntegrableOn (fun s : ℝ => ‖tipRescaleW prob c' test.g (s : ℂ)‖)
      (Ioi (tipSMin c')) := hdom.norm
  have hfneg_int : IntegrableOn fneg (Ioi (tipSMin c')) := by
    have heq : fneg = fun s => (|f s| - f s) / 2 := by
      funext s; dsimp [fneg]
      rcases le_total (f s) 0 with h | h
      · rw [max_eq_right (neg_nonneg.mpr h), abs_of_nonpos h]; ring
      · rw [max_eq_left (neg_nonpos.mpr h), abs_of_nonneg h]; ring
    rw [heq]
    have habs : IntegrableOn (fun s => |f s|) (Ioi (tipSMin c')) := by
      refine hfnorm_int.congr_fun (fun s _ => ?_) measurableSet_Ioi
      dsimp [f]; rw [tipRescaleW_real_on_real hc' test.hg_test s, Complex.norm_real,
        Complex.ofReal_re, Real.norm_eq_abs]
    exact (habs.sub hf_int).div_const 2
  have hfneg_total : (1 / 2 : ℝ) ≤ ∫ s in Ioi (tipSMin c'), fneg s := by
    have heq : fneg = fun s : ℝ => (‖tipRescaleW prob c' test.g (s : ℂ)‖ - f s) / 2 := by
      funext s; dsimp [fneg, f]
      rw [tipRescaleW_real_on_real hc' test.hg_test s, Complex.norm_real, Complex.ofReal_re,
        Real.norm_eq_abs]
      rcases le_total (tipEps c' * (2 * c' / 3) * tipBReal c' s *
          prob.cardyV (c' / 12) (tipTReal c' s) * test.g (tipTReal c' s) /
          prob.cardyNorm (c' / 12) test.g) 0 with h | h
      · rw [max_eq_right (neg_nonneg.mpr h), abs_of_nonpos h]; ring
      · rw [max_eq_left (neg_nonpos.mpr h), abs_of_nonneg h]; ring
    rw [heq, integral_div, integral_sub hfnorm_int hf_int,
      tipRescaleW_norm_integral hc' hc'_shift test, tipRescaleW_integral_vac hc' test, neg_div]
    have hgvac : 0 ≤ test.gVac / (2 * π * test.M) :=
      div_nonneg test.hgVac_nonneg (by positivity [Real.pi_pos, hM_pos])
    linarith
  have hsMin_le : tipSMin c' ≤ tipS₁W c' test := by
    rw [tipSMin_eq_neg_div_tipEps hc']
    unfold tipS₁W FixedBlowupTest.x₁
    have hε := tipEps_pos hc'
    exact div_le_div_of_nonneg_right (by linarith [Real.sqrt_nonneg (3 * test.t₁ / c')]) hε.le
  have htail_zero : ∫ s in Ioi (tipS₁W c' test), fneg s = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
    dsimp [fneg, f]
    exact max_eq_left (neg_nonpos.mpr (tipRescaleW_nonneg_tail hc' hc'_shift test s (mem_Ioi.mp hs).le))
  have hunion : (∫ s in Ioc (tipSMin c') (tipS₁W c' test), fneg s) +
      (∫ s in Ioi (tipS₁W c' test), fneg s) = ∫ s in Ioi (tipSMin c'), fneg s := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hfneg_int.mono_set Ioc_subset_Ioi_self) (hfneg_int.mono_set (Ioi_subset_Ioi hsMin_le)),
      Ioc_union_Ioi_eq_Ioi hsMin_le]
  linarith

/-! ### Section 2: General-`(w, Q)` Lemma T5 (`bl:T5`), pointwise envelope, and left-tail bound -/

/-- **General-`(w, Q)` Lemma T5 (`blowup_limit.tex`, Lemma `bl:T5`)**:
complex tip majorant for `tipRescaleW prob c' test.g ζ` on `ε ‖ζ‖ ≤ ρ_T5`, `ζ ∉ [0, ∞)`
and `c' ≥ c₀`. -/
theorem lemma_T5_general (prob : FixedWeightProblem) (D : UniformPropositionPData prob) :
    ∃ ρ_T5 C₁ C₂ C₃ c₀ : ℝ,
      0 < ρ_T5 ∧ ρ_T5 ≤ D.r_1 ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧ max D.c₀ 8 ≤ c₀ ∧
      ∀ {c' : ℝ} (test : FixedBlowupTest prob c') {ζ : ℂ},
        c₀ ≤ c' → ¬ (ζ.im = 0 ∧ 0 ≤ ζ.re) →
        tipEps c' * ‖ζ‖ ≤ ρ_T5 →
        tipRescaleW prob c' test.g ζ ≠ 0 →
          Real.log ‖tipRescaleW prob c' test.g ζ‖ ≤
            tipH ζ - Real.log (tipDist ζ) +
              C₁ + C₂ * tipEps c' * ‖ζ‖ ^ (5 / 2 : ℝ) +
              C₃ * (tipEps c' * ‖ζ‖) ^ (1 / 2 : ℝ) * Real.log c' := by
  obtain ⟨ρ₁, C_T1, ψ, hρ₁_pos, hCT1_nn, _, _, _, _, hT1⟩ := lemma_T1
  obtain ⟨ρ₂, C_T2, hρ₂_pos, hCT2_nn, hT2⟩ := lemma_T2 lemmaGPotentialInput_virasoro
  obtain ⟨c_Kw_cx, C_Klo, hcKw8, hCKlo, hPJ_cx⟩ := stripPoissonJensen_complex_general prob
  let P₀ := D.pAt (le_rfl : D.c₀ ≤ D.c₀)
  obtain ⟨c_Q_min, C_Q, hcQ_pos, hcQ_le, hCQ0⟩ := disc_Q_bounds D.hr1_pos.le D.hr1_le (Q_star := D.Q_star)
    (by rw [← D.uniform_Q_star (le_rfl : D.c₀ ≤ D.c₀)]; exact P₀.p2_Q_holo)
    (fun {b} hb => by
      rw [← D.uniform_Q_star (le_rfl : D.c₀ ≤ D.c₀)]
      exact P₀.p2_Q_ne_zero (by rwa [D.uniform_r_1 (le_rfl : D.c₀ ≤ D.c₀)]))
  have hCQ_gt0 : 0 < C_Q := hcQ_pos.trans_le hcQ_le
  let C_W_fac : ℝ := (3 * xiStar / 2) * (3 * xiStar) ^ (prob.w - 1) * (2 / 3 : ℝ) /
    Real.sqrt (2 * π ^ 2 * xiStar / 3)
  have hCW_nn : 0 ≤ C_W_fac := by dsimp [C_W_fac]; positivity [xiStar_pos]
  let C_W_tot : ℝ := C_W_fac * (C_Q + D.η_V_max) + 1
  have hCW_pos : 0 < C_W_tot := by
    have h1 : 0 ≤ C_W_fac * (C_Q + D.η_V_max) :=
      mul_nonneg hCW_nn (add_nonneg hCQ_gt0.le D.hηV_max_nn)
    dsimp [C_W_tot]; linarith
  let C_PJ_cx : ℝ := pjConstOf D.C_e D.c_band C_Klo
    (|majorantU0| + 4 * π / 3 * (Real.log 12 / (2 * π) + 2) ^ 2)
  let ρ_T5 : ℝ := min ρ₁ (min ρ₂ (min D.r_1 (min (1 / (4 * (C_T1 + 1) ^ 2)) 0.25)))
  have hρ_pos : 0 < ρ_T5 := by positivity [D.hr1_pos]
  have hρ_r1 : ρ_T5 ≤ D.r_1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  let c₀ : ℝ := max (max D.c₀ 8) c_Kw_cx
  have hc₀_ge : max D.c₀ 8 ≤ c₀ := le_max_left _ _
  let C₁ : ℝ := Real.log C_W_tot + Real.log (2 * slitQ) + slitEntropyComplexConst + C_PJ_cx
  let C₂ : ℝ := C_T2
  let C₃ : ℝ := (D.p_e + 1 / 2) * (2 / (0.3 * π)) * (3 / (2 * √slitQ))
  have hC₃_nn : 0 ≤ C₃ := by positivity [D.hp_e_nn, slitQ_pos]
  refine ⟨ρ_T5, C₁, C₂, C₃, c₀, hρ_pos, hρ_r1, hCT2_nn, hC₃_nn, hc₀_ge,
    fun {c'} test {ζ} hc' hζ hεζ hΦ_ne => ?_⟩
  have hc'_D : D.c₀ ≤ c' := ((le_max_left D.c₀ 8).trans hc₀_ge).trans hc'
  have hc'_8 : 8 ≤ c' := ((le_max_right D.c₀ 8).trans hc₀_ge).trans hc'
  have hc'_Kw : c_Kw_cx ≤ c' := (le_max_right _ _).trans hc'
  have hc'_pos : 0 < c' := by linarith
  have hc'_gt1 : 1 < c' := by linarith
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'_pos
  have hεζ_1 : tipEps c' * ‖ζ‖ ≤ ρ₁ := hεζ.trans (min_le_left _ _)
  have hεζ_2 : tipEps c' * ‖ζ‖ ≤ ρ₂ := hεζ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεζ_r1 : tipEps c' * ‖ζ‖ ≤ D.r_1 := hεζ.trans hρ_r1
  have hεζ_T1 : tipEps c' * ‖ζ‖ ≤ 1 / (4 * (C_T1 + 1) ^ 2) :=
    hεζ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _))))
  have hεζ_25 : tipEps c' * ‖ζ‖ ≤ 0.25 :=
    hεζ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _))))
  set b := bScale c' ζ
  have hW_ne : W_C_prob prob c' b ≠ 0 := fun h => hΦ_ne (by unfold tipRescaleW; rw [h]; ring)
  have hG_ne : hankelContinuationW prob.w c' test.g b ≠ 0 :=
    fun h => hΦ_ne (by unfold tipRescaleW; rw [h]; simp)
  have hb_im : |b.im| < 1 / 2 := by
    have him : b.im = tipEps c' * ζ.im := by unfold b bScale; simp [Complex.add_im, Complex.mul_im]
    rw [him, abs_mul, abs_of_pos hε_pos]
    exact (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm ζ) hε_pos.le).trans_lt
      (hεζ_25.trans_lt (by norm_num))
  -- Step 1: Lemma T1 gives `z_b` with `slitBoundaryMapC z_b = b`, `‖z_b - σ_*‖ ≤ 0.1`, etc.
  obtain ⟨_, hz_im_pos, hz_cl, hz_map, _, hz_im_bd, _, hz_prod_bd⟩ := hT1 hc'_pos hζ hεζ_1
  set v : ℂ := I * ((√(tipEps c') : ℝ) : ℂ) * (-ζ) ^ (1 / 2 : ℂ)
  set z_b : ℂ := (sigmaStar : ℂ) + ψ v
  have hCT1_sqrt : C_T1 * Real.sqrt (tipEps c' * ‖ζ‖) ≤ 1 / 2 := by
    have hsqrt_le : Real.sqrt (tipEps c' * ‖ζ‖) ≤ 1 / (2 * (C_T1 + 1)) := by
      have h1 : 1 / (4 * (C_T1 + 1) ^ 2) = (1 / (2 * (C_T1 + 1))) ^ 2 := by
        field_simp [show C_T1 + 1 ≠ 0 by positivity]; ring
      calc Real.sqrt (tipEps c' * ‖ζ‖) ≤ Real.sqrt ((1 / (2 * (C_T1 + 1))) ^ 2) :=
            Real.sqrt_le_sqrt (h1 ▸ hεζ_T1)
        _ = 1 / (2 * (C_T1 + 1)) := Real.sqrt_sq (by positivity)
    calc C_T1 * Real.sqrt (tipEps c' * ‖ζ‖)
        ≤ C_T1 * (1 / (2 * (C_T1 + 1))) := mul_le_mul_of_nonneg_left hsqrt_le hCT1_nn
      _ = (C_T1 / (C_T1 + 1)) * (1 / 2) := by
          field_simp [show C_T1 + 1 ≠ 0 by positivity]
      _ ≤ 1 * (1 / 2) := by gcongr; exact (div_le_one (by linarith)).mpr (by linarith)
      _ = 1 / 2 := one_mul _
  -- Step 2: Lower bound `y * |z_b - σ_*|` and upper bound `y`.
  have hd_pos : 0 < tipDist ζ := tipDist_pos_of_not_nonneg hζ
  have hprod_lb : (1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist ζ) ≤
      z_b.im * ‖z_b - (sigmaStar : ℂ)‖ := by
    have hbase_nn : 0 ≤ (tipEps c' / slitQ) * tipDist ζ :=
      mul_nonneg (div_nonneg hε_pos.le slitQ_pos.le) hd_pos.le
    have h1 := (abs_le.mp hz_prod_bd).1
    have h2 : C_T1 * Real.sqrt (tipEps c' * ‖ζ‖) * ((tipEps c' / slitQ) * tipDist ζ) ≤
        (1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist ζ) :=
      mul_le_mul_of_nonneg_right hCT1_sqrt hbase_nn
    linarith
  have hy_ub : z_b.im ≤ (3 / (2 * √slitQ)) * (tipEps c' * ‖ζ‖) ^ (1 / 2 : ℝ) := by
    have hsqrt_re_nn : 0 ≤ ((-ζ) ^ (1 / 2 : ℂ)).re := by
      by_cases h0 : -ζ = 0
      · rw [h0]; simp
      · rw [Complex.cpow_def_of_ne_zero h0, Complex.exp_re]
        refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_)
        · have := Complex.neg_pi_lt_arg (-ζ)
          have him : (Complex.log (-ζ) * (1 / 2 : ℂ)).im = (-ζ).arg / 2 := by
            simp [Complex.log_im]; ring
          rw [him]; linarith
        · have := Complex.arg_le_pi (-ζ)
          have him : (Complex.log (-ζ) * (1 / 2 : ℂ)).im = (-ζ).arg / 2 := by
            simp [Complex.log_im]; ring
          rw [him]; linarith
    have hbase_nn : 0 ≤ Real.sqrt (tipEps c' / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re :=
      mul_nonneg (Real.sqrt_nonneg _) hsqrt_re_nn
    have h1 := (abs_le.mp hz_im_bd).2
    have h2 : C_T1 * Real.sqrt (tipEps c' * ‖ζ‖) *
        (Real.sqrt (tipEps c' / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re) ≤
        (1 / 2 : ℝ) * (Real.sqrt (tipEps c' / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re) :=
      mul_le_mul_of_nonneg_right hCT1_sqrt hbase_nn
    have hre_le : ((-ζ) ^ (1 / 2 : ℂ)).re ≤ Real.sqrt ‖ζ‖ := by
      have hnorm : ‖(-ζ) ^ (1 / 2 : ℂ)‖ = Real.sqrt ‖ζ‖ := by
        simpa [norm_neg] using FormalResearch.Special.norm_cpow_half (-ζ)
      exact (Complex.re_le_norm _).trans_eq hnorm
    calc z_b.im ≤ (3 / 2 : ℝ) * (Real.sqrt (tipEps c' / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re) := by
          linarith
      _ ≤ (3 / 2 : ℝ) * (Real.sqrt (tipEps c' / slitQ) * Real.sqrt ‖ζ‖) := by gcongr
      _ = (3 / (2 * √slitQ)) * Real.sqrt (tipEps c' * ‖ζ‖) := by
          rw [Real.sqrt_div hε_pos.le, Real.sqrt_mul hε_pos.le]; ring
      _ = (3 / (2 * √slitQ)) * (tipEps c' * ‖ζ‖) ^ (1 / 2 : ℝ) := by
          rw [← Real.sqrt_eq_rpow]
  -- Step 3: General complex Strip Poisson-Jensen + Lemma T4.
  have hz_eta : (z_b.re : ℂ) + (z_b.im : ℂ) * I = z_b := Complex.re_add_im z_b
  have hT4 := lemma_T4 hz_im_pos (by rw [hz_eta]; exact hz_cl)
  let P := D.pAt hc'_D
  have hG_PJ := hPJ_cx P hc'_Kw test.hg_test test.hM_pos hz_im_pos hz_cl
    (by simpa [hz_map] using hb_im) (by simpa [hz_map] using hG_ne)
  rw [hz_map, D.uniform_C_e hc'_D, D.uniform_p_e hc'_D, D.uniform_c_band hc'_D] at hG_PJ
  have hlogc'_nn : 0 ≤ Real.log c' := Real.log_nonneg hc'_gt1.le
  have hm_term : (D.p_e + 1 / 2) * (1 - slitMass z_b.re z_b.im) * Real.log c' ≤
      C₃ * (tipEps c' * ‖ζ‖) ^ (1 / 2 : ℝ) * Real.log c' := by
    have h1 : 1 - slitMass z_b.re z_b.im ≤
        (2 / (0.3 * π)) * ((3 / (2 * √slitQ)) * (tipEps c' * ‖ζ‖) ^ (1 / 2 : ℝ)) :=
      hT4.1.trans (mul_le_mul_of_nonneg_left hy_ub (by positivity))
    have hpe : 0 ≤ D.p_e + 1 / 2 := by linarith [D.hp_e_nn]
    calc (D.p_e + 1 / 2) * (1 - slitMass z_b.re z_b.im) * Real.log c'
        ≤ (D.p_e + 1 / 2) * ((2 / (0.3 * π)) * ((3 / (2 * √slitQ)) *
            (tipEps c' * ‖ζ‖) ^ (1 / 2 : ℝ))) * Real.log c' := by gcongr
      _ = C₃ * (tipEps c' * ‖ζ‖) ^ (1 / 2 : ℝ) * Real.log c' := by dsimp [C₃]; ring
  have hS_term : slitEntropy z_b.re z_b.im ≤
      (2 / 3 : ℝ) * Real.log c' + Real.log (2 * slitQ) - Real.log (tipDist ζ) +
        slitEntropyComplexConst := by
    have hz_ne_sigma : ‖z_b - (sigmaStar : ℂ)‖ ≠ 0 := by
      intro h0
      have : z_b.im * ‖z_b - (sigmaStar : ℂ)‖ = 0 := by rw [h0, mul_zero]
      have hpos : 0 < (1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist ζ) := by positivity [slitQ_pos]
      linarith
    have hz_norm_pos : 0 < ‖z_b - (sigmaStar : ℂ)‖ := lt_of_le_of_ne (norm_nonneg _) hz_ne_sigma.symm
    have hprod_pos : 0 < (1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist ζ) := by positivity [slitQ_pos]
    have hlog_inv : Real.log (1 / z_b.im) + Real.log (1 / ‖z_b - (sigmaStar : ℂ)‖) ≤
        (2 / 3 : ℝ) * Real.log c' + Real.log (2 * slitQ) - Real.log (tipDist ζ) := by
      have hmul_inv : Real.log (1 / z_b.im) + Real.log (1 / ‖z_b - (sigmaStar : ℂ)‖) =
          Real.log (1 / (z_b.im * ‖z_b - (sigmaStar : ℂ)‖)) := by
        rw [← Real.log_mul (one_div_pos.mpr hz_im_pos).ne' (one_div_pos.mpr hz_norm_pos).ne']
        ring_nf
      have hinv_le : 1 / (z_b.im * ‖z_b - (sigmaStar : ℂ)‖) ≤
          (c' ^ (2 / 3 : ℝ)) * (2 * slitQ) / tipDist ζ := by
        calc 1 / (z_b.im * ‖z_b - (sigmaStar : ℂ)‖)
            ≤ 1 / ((1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist ζ)) :=
              one_div_le_one_div_of_le hprod_pos hprod_lb
          _ = (tipEps c')⁻¹ * (2 * slitQ) / tipDist ζ := by
              field_simp [hε_pos.ne', slitQ_pos.ne', hd_pos.ne']
          _ = (c' ^ (2 / 3 : ℝ)) * (2 * slitQ) / tipDist ζ := by
              unfold tipEps; rw [← Real.rpow_neg hc'_pos.le, neg_neg]
      have hlog_step : Real.log (1 / (z_b.im * ‖z_b - (sigmaStar : ℂ)‖)) ≤
          Real.log ((c' ^ (2 / 3 : ℝ)) * (2 * slitQ) / tipDist ζ) :=
        Real.log_le_log (one_div_pos.mpr (mul_pos hz_im_pos hz_norm_pos)) hinv_le
      have hlog_rhs : Real.log ((c' ^ (2 / 3 : ℝ)) * (2 * slitQ) / tipDist ζ) =
          (2 / 3 : ℝ) * Real.log c' + Real.log (2 * slitQ) - Real.log (tipDist ζ) := by
        rw [Real.log_div (by positivity [slitQ_pos]) hd_pos.ne',
          Real.log_mul (Real.rpow_pos_of_pos hc'_pos _).ne' (by positivity [slitQ_pos]),
          Real.log_rpow hc'_pos]
      linarith
    have hS' : slitEntropy z_b.re z_b.im ≤
        Real.log (1 / z_b.im) + Real.log (1 / ‖z_b - (sigmaStar : ℂ)‖) +
          slitEntropyComplexConst := by
      simpa [hz_eta] using hT4.2
    linarith
  -- Step 4: Bound `log ‖W_C_prob prob c' b‖` from `W_C_prob_norm_le`.
  have hb_disc : b ∈ closedBall (xiStar : ℂ) P.r_1 := by
    rw [mem_closedBall, dist_eq_norm, D.uniform_r_1 hc'_D]
    have hsub : b - (xiStar : ℂ) = ((tipEps c' : ℝ) : ℂ) * ζ := by
      unfold b bScale; ring
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε_pos]
    exact hεζ_r1
  have hCQ_P : ∀ b' ∈ closedBall (xiStar : ℂ) P.r_1, ‖P.Q_star b'‖ ≤ C_Q := fun b' hb' => by
    have hb0 : b' ∈ closedBall (xiStar : ℂ) D.r_1 := by rwa [← D.uniform_r_1 hc'_D]
    have heq : P.Q_star b' = D.Q_star b' := by rw [D.uniform_Q_star hc'_D]
    rw [heq]
    exact (hCQ0 b' hb0).2
  have hW_ub_raw := W_C_prob_norm_le P hCQ_P hb_disc
  dsimp only at hW_ub_raw
  have hW_ub : ‖W_C_prob prob c' b‖ ≤
      C_W_tot * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re) := by
    have h1 : C_W_fac * (C_Q + P.η_V) ≤ C_W_tot := by
      have hη_le : P.η_V ≤ D.η_V_max := D.uniform_ηV_le hc'_D
      dsimp [C_W_tot]
      linarith [mul_le_mul_of_nonneg_left (add_le_add_left hη_le C_Q) hCW_nn]
    exact hW_ub_raw.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hc'_pos.le _)) (Real.exp_pos _).le)
  have hW_log : Real.log ‖W_C_prob prob c' b‖ ≤
      Real.log C_W_tot - (1 / 6 : ℝ) * Real.log c' + c' * (tipL b).re := by
    have hstep := Real.log_le_log (norm_pos_iff.mpr hW_ne) hW_ub
    have hlog_eq : Real.log (C_W_tot * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re)) =
        Real.log C_W_tot - (1 / 6 : ℝ) * Real.log c' + c' * (tipL b).re := by
      rw [Real.log_mul (mul_pos hCW_pos (Real.rpow_pos_of_pos hc'_pos _)).ne' (Real.exp_pos _).ne',
        Real.log_mul hCW_pos.ne' (Real.rpow_pos_of_pos hc'_pos _).ne',
        Real.log_rpow hc'_pos, Real.log_exp]
      ring
    linarith
  -- Step 5: Lemma T2 bounds `c' * (majorant2D b + Re L b) ≤ tipH ζ + C_T2 * ε * ‖ζ‖^(5/2)`.
  have hT2_bd := (hT2 hc'_pos hζ hεζ_2).2
  rw [lemmaGPotentialInput_virasoro_U] at hT2_bd
  have hpot_bd : c' * (majorant2D b + (tipL b).re) ≤
      tipH ζ + C_T2 * tipEps c' * ‖ζ‖ ^ (5 / 2 : ℝ) := by
    have := (abs_le.mp hT2_bd).2
    linarith
  -- Step 6: Combine all pieces (`-1/6 - 1/2 + 2/3 = 0` cancels identically).
  have hΦ_log : Real.log ‖tipRescaleW prob c' test.g ζ‖ =
      Real.log ‖W_C_prob prob c' b‖ + Real.log ‖hankelContinuationW prob.w c' test.g b‖ -
        Real.log (prob.cardyNorm (c' / 12) test.g) := by
    unfold tipRescaleW
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos test.hM_pos,
      Real.log_div (mul_pos (norm_pos_iff.mpr hW_ne) (norm_pos_iff.mpr hG_ne)).ne'
        test.hM_pos.ne',
      Real.log_mul (norm_pos_iff.mpr hW_ne).ne' (norm_pos_iff.mpr hG_ne).ne']
  dsimp [C₁, C₂, C_PJ_cx] at hG_PJ ⊢
  linarith

/-- Uniform disc-averaged pointwise bounds on `tipRescaleW prob c' test.g`
(`blowup_limit.tex`, Proposition T (i)). -/
theorem tipRescaleW_pointwise_envelope (prob : FixedWeightProblem) (D : UniformPropositionPData prob) :
    ∃ C_env : ℝ, 0 ≤ C_env ∧
      ∀ R : ℝ, 0 ≤ R → ∀ᶠ c' : ℝ in atTop,
        ∀ (test : FixedBlowupTest prob c') (ζ₀ : ℂ), ζ₀ ∈ closedBall (0 : ℂ) R →
          ‖tipRescaleW prob c' test.g ζ₀‖ ≤
            C_env * (1 + ‖ζ₀‖) ^ (1 / 2 : ℝ) * Real.exp (tipH ζ₀) ∧
          (ζ₀.im ≠ 0 → ‖tipRescaleW prob c' test.g ζ₀‖ ≤
            C_env * Real.exp (tipH ζ₀) *
              (1 + min ((1 + ‖ζ₀‖) ^ (1 / 2 : ℝ)) (1 / |ζ₀.im|))) ∧
          (|(-ζ₀).arg| ≤ 2 * π / 3 → 8 ≤ ‖ζ₀‖ →
            ‖tipRescaleW prob c' test.g ζ₀‖ ≤ C_env * Real.exp (tipH ζ₀) / ‖ζ₀‖) := by
  obtain ⟨ρ_T5, C₁, C₂, C₃, c₀, hρ_pos, _, hCT2_nn, hCT3_nn, hc₀_ge, hT5⟩ :=
    lemma_T5_general prob D
  obtain ⟨c₀_H, _, hholo_fn⟩ := tipRescaleW_holo_exists prob
  let C_env : ℝ := Real.exp (3 * KTip / 4 + |C₁| + Real.log 4 + 4 / π + 1)
  have hCenv_pos : 0 < C_env := Real.exp_pos _
  refine ⟨C_env, hCenv_pos.le, fun R hR => ?_⟩
  have hε_tend : Tendsto (fun c' : ℝ => tipEps c' * (R + 1)) atTop (nhds 0) := by
    have h0 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3))
    simpa [tipEps] using h0.mul_const (R + 1)
  have hlog_tend : Tendsto (fun c' : ℝ =>
      C₂ * tipEps c' * (R + 1) ^ (5 / 2 : ℝ) +
        C₃ * (tipEps c' * (R + 1)) ^ (1 / 2 : ℝ) * Real.log c') atTop (nhds 0) := by
    have ht1 : Tendsto (fun c' : ℝ => C₂ * tipEps c' * (R + 1) ^ (5 / 2 : ℝ)) atTop (nhds 0) := by
      have h0 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3))
      simpa [tipEps] using (h0.const_mul C₂).mul_const ((R + 1) ^ (5 / 2 : ℝ))
    have ht2 : Tendsto (fun c' : ℝ =>
        C₃ * (tipEps c' * (R + 1)) ^ (1 / 2 : ℝ) * Real.log c') atTop (nhds 0) := by
      have hmul : Tendsto (fun c' : ℝ => Real.log c' / c' ^ (1 / 3 : ℝ)) atTop (nhds 0) := by
        have h0 : Tendsto (fun c' : ℝ => 6 * c' ^ (-(1 / 6 : ℝ))) atTop (nhds 0) := by
          simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).const_mul 6
        refine squeeze_zero' ?_ ?_ h0
        · filter_upwards [eventually_ge_atTop (1 : ℝ)] with c' hc'
          exact div_nonneg (Real.log_nonneg hc') (by positivity)
        · filter_upwards [eventually_ge_atTop (1 : ℝ)] with c' hc'
          have hc'_pos : 0 < c' := by linarith
          have hlog : Real.log c' ≤ 6 * c' ^ (1 / 6 : ℝ) := by
            have hl := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hc'_pos (1 / 6 : ℝ))
            have h6 : Real.log c' = 6 * Real.log (c' ^ (1 / 6 : ℝ)) := by
              rw [Real.log_rpow hc'_pos]; ring
            linarith
          have hpow : c' ^ (1 / 6 : ℝ) / c' ^ (1 / 3 : ℝ) = c' ^ (-(1 / 6 : ℝ)) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg hc'_pos.le, ← Real.rpow_add hc'_pos]; norm_num
          calc Real.log c' / c' ^ (1 / 3 : ℝ)
              ≤ (6 * c' ^ (1 / 6 : ℝ)) / c' ^ (1 / 3 : ℝ) := by gcongr
            _ = 6 * (c' ^ (1 / 6 : ℝ) / c' ^ (1 / 3 : ℝ)) := by ring
            _ = 6 * c' ^ (-(1 / 6 : ℝ)) := by rw [hpow]
      have hrew : ∀ᶠ c' : ℝ in atTop,
          C₃ * (tipEps c' * (R + 1)) ^ (1 / 2 : ℝ) * Real.log c' =
            (C₃ * (R + 1) ^ (1 / 2 : ℝ)) * (Real.log c' / c' ^ (1 / 3 : ℝ)) := by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with c' hc'
        have hc'_pos : 0 < c' := by linarith
        unfold tipEps
        rw [Real.mul_rpow (Real.rpow_nonneg hc'_pos.le _) (by linarith),
          ← Real.rpow_mul hc'_pos.le, show -(2 / 3 : ℝ) * (1 / 2 : ℝ) = -(1 / 3 : ℝ) by norm_num,
          Real.rpow_neg hc'_pos.le]
        ring
      exact ((hmul.const_mul (C₃ * (R + 1) ^ (1 / 2 : ℝ))).congr' (hrew.mono fun _ h => h.symm)).trans
        (by simp)
    simpa using ht1.add ht2
  filter_upwards [eventually_ge_atTop (max c₀ c₀_H),
    hε_tend.eventually (eventually_le_nhds hρ_pos),
    hε_tend.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hlog_tend.eventually (eventually_lt_nhds zero_lt_one)] with
    c' hc'_both hεR_ρ hεR_half herr_le_lt
  have hc' : c₀ ≤ c' := (le_max_left _ _).trans hc'_both
  have hc'_H : c₀_H ≤ c' := (le_max_right _ _).trans hc'_both
  have herr_le : C₂ * tipEps c' * (R + 1) ^ (5 / 2 : ℝ) +
      C₃ * (tipEps c' * (R + 1)) ^ (1 / 2 : ℝ) * Real.log c' ≤ 1 := herr_le_lt.le
  have hc'_8 : 8 ≤ c' := ((le_max_right D.c₀ 8).trans hc₀_ge).trans hc'
  have hc'_pos : 0 < c' := by linarith
  have hc'_gt1 : 1 < c' := by linarith
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'_pos
  intro test ζ₀ hζ₀
  have hζ₀_norm : ‖ζ₀‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hζ₀
  have hεζ_1 : tipEps c' * (R + 1) ≤ ρ_T5 := hεR_ρ
  let r : ℝ := (1 / 2 : ℝ) * (1 + ‖ζ₀‖) ^ (-(1 / 2 : ℝ))
  have hr_pos : 0 < r := by positivity
  have hr_le_half : r ≤ 1 / 2 := by
    have : (1 + ‖ζ₀‖) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg ζ₀]) (by norm_num)
    dsimp [r]; linarith
  have hball_sub : closedBall ζ₀ r ⊆ ball (0 : ℂ) (R + 1) := by
    intro ζ hζ
    rw [mem_ball, dist_zero_right]
    have h1 := mem_closedBall.mp hζ
    rw [dist_eq_norm] at h1
    calc ‖ζ‖ = ‖(ζ - ζ₀) + ζ₀‖ := by ring_nf
      _ ≤ ‖ζ - ζ₀‖ + ‖ζ₀‖ := norm_add_le _ _
      _ ≤ r + R := add_le_add h1 hζ₀_norm
      _ < R + 1 := by linarith
  have hholo_ball : DifferentiableOn ℂ (tipRescaleW prob c' test.g) (ball (0 : ℂ) (R + 1)) :=
    tipRescaleW_holo_ball hc'_pos (by linarith) (hholo_fn hc'_H test.hg_test)
  have han_ball : AnalyticOnNhd ℂ (tipRescaleW prob c' test.g) (ball (0 : ℂ) (R + 1)) :=
    hholo_ball.analyticOnNhd isOpen_ball
  by_cases hzero : tipRescaleW prob c' test.g ζ₀ = 0
  · rw [hzero, norm_zero]
    refine ⟨by positivity [Real.exp_pos (tipH ζ₀)], fun _ => by positivity [Real.exp_pos (tipH ζ₀)],
      fun _ _ => by positivity [Real.exp_pos (tipH ζ₀)]⟩
  · have hzero_null : volume {ζ ∈ ball ζ₀ r | tipRescaleW prob c' test.g ζ = 0} = 0 := by
      classical
      have han_big : AnalyticOnNhd ℂ (tipRescaleW prob c' test.g) (ball ζ₀ (r + 1 / 4)) := by
        refine han_ball.mono fun ζ hζ => ?_
        rw [mem_ball, dist_zero_right]
        rw [mem_ball, dist_eq_norm] at hζ
        calc ‖ζ‖ = ‖(ζ - ζ₀) + ζ₀‖ := by ring_nf
          _ ≤ ‖ζ - ζ₀‖ + ‖ζ₀‖ := norm_add_le _ _
          _ < r + 1 / 4 + ‖ζ₀‖ := by linarith
          _ < R + 1 := by linarith
      have hnot_zero : ¬ EqOn (tipRescaleW prob c' test.g) 0 (ball ζ₀ (r + 1 / 4)) :=
        fun h => hzero (h (mem_ball_self (by linarith)))
      have hev : ∀ z ∈ ball ζ₀ (r + 1 / 4), ∀ᶠ w in 𝓝[≠] z, tipRescaleW prob c' test.g w ≠ 0 := by
        rcases han_big.eqOn_zero_or_eventually_ne_zero_of_preconnected
            (convex_ball ζ₀ (r + 1 / 4)).isPreconnected with h | h
        · exact absurd h hnot_zero
        · intro z hz
          have h1 := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp h z hz
          have h2 : ball ζ₀ (r + 1 / 4) ∈ 𝓝[≠] z := nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz)
          filter_upwards [h1, h2] with w hw1 hw2
          rcases hw1 with hw | hw
          · exact hw
          · exact absurd hw2 hw
      have hopen : ∀ z ∈ closedBall ζ₀ r, ∃ δ > 0, ∀ w ∈ ball z δ, w ≠ z →
          tipRescaleW prob c' test.g w ≠ 0 := fun z hz => by
        have hzR : z ∈ ball ζ₀ (r + 1 / 4) := closedBall_subset_ball (by linarith) hz
        obtain ⟨U, hU, hUf⟩ := (hev z hzR).exists_mem
        rw [mem_nhdsWithin] at hU
        obtain ⟨V, hV_open, hzV, hVU⟩ := hU
        obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.isOpen_iff.mp hV_open z hzV
        exact ⟨δ, hδ_pos, fun w hw hwz => hUf w (hVU ⟨hδ_sub hw, hwz⟩)⟩
      choose δ hδ_pos hδ_ne using hopen
      obtain ⟨s, hs⟩ := (isCompact_closedBall ζ₀ r).elim_nhds_subcover
        (fun z => if hz : z ∈ closedBall ζ₀ r then ball z (δ z hz) else ∅)
        fun z hz => by simp only [hz, ↓reduceDIte]; exact ball_mem_nhds z (hδ_pos z hz)
      have hsub : {ζ ∈ ball ζ₀ r | tipRescaleW prob c' test.g ζ = 0} ⊆ (s : Set ℂ) := by
        intro ζ ⟨hζ_ball, hζ_f0⟩
        have hζ_cl : ζ ∈ closedBall ζ₀ r := ball_subset_closedBall hζ_ball
        obtain ⟨z, hzs, hζ_in⟩ := mem_iUnion₂.mp (hs.2 hζ_cl)
        have hz_cl : z ∈ closedBall ζ₀ r := hs.1 z hzs
        simp only [hz_cl, ↓reduceDIte] at hζ_in
        by_contra hne
        exact absurd hζ_f0 (hδ_ne z hz_cl ζ hζ_in fun h_eq => hne (h_eq ▸ hzs))
      exact measure_mono_null hsub (s.finite_toSet.measure_zero volume)
    let M_const : ℝ := tipH ζ₀ + 3 * KTip / 4 + |C₁| + 1
    let B : ℂ → ℝ := fun ζ => M_const + (-Real.log (tipDist ζ))
    have havg := disc_avg_neg_log_tipDist ζ₀
    have hB_int : IntegrableOn B (ball ζ₀ r) :=
      (integrableOn_const (by finiteness : volume (ball ζ₀ r) ≠ ⊤)).add havg.1
    have hB_le : ∀ᵐ ζ ∂(volume.restrict (ball ζ₀ r)),
        Real.log ‖tipRescaleW prob c' test.g ζ‖ ≤ B ζ := by
      have hvol0 : volume {ζ : ℂ | ζ.im = 0} = 0 := by
        let L : Submodule ℝ ℂ := LinearMap.ker Complex.imCLM.toLinearMap
        have hne : L ≠ ⊤ := by
          intro htop
          have hI : I ∈ (⊤ : Submodule ℝ ℂ) := Submodule.mem_top
          rw [← htop] at hI
          have h0 : Complex.imCLM.toLinearMap I = 0 := LinearMap.mem_ker.mp hI
          simp at h0
        have hsub : {ζ : ℂ | ζ.im = 0} = (L : Set ℂ) := by
          ext ζ; simp [L, LinearMap.mem_ker]
        rw [hsub]
        exact MeasureTheory.Measure.addHaar_submodule volume L hne
      have h1_ae : ∀ᵐ ζ ∂volume, ζ ∉ ({ζ : ℂ | ζ.im = 0} : Set ℂ) :=
        ae_iff.mpr (by simpa using hvol0)
      have h2_ae : ∀ᵐ ζ ∂volume, ζ ∉ {w ∈ ball ζ₀ r | tipRescaleW prob c' test.g w = 0} :=
        ae_iff.mpr (by simpa using hzero_null)
      filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae h1_ae,
        ae_restrict_of_ae h2_ae] with ζ hζ_ball hζ_im hζ_nz
      have hζ_slit : ¬ (ζ.im = 0 ∧ 0 ≤ ζ.re) := fun ⟨him, _⟩ => hζ_im him
      have hζ_ne0 : tipRescaleW prob c' test.g ζ ≠ 0 := fun h0 => hζ_nz ⟨hζ_ball, h0⟩
      have hζ_R : ‖ζ‖ ≤ R + 1 := by
        rw [← dist_zero_right ζ]
        exact (mem_ball.mp (hball_sub (ball_subset_closedBall hζ_ball))).le
      have hεζ_le : tipEps c' * ‖ζ‖ ≤ ρ_T5 :=
        (mul_le_mul_of_nonneg_left hζ_R hε_pos.le).trans hεζ_1
      have hT5_bd := hT5 test hc' hζ_slit hεζ_le hζ_ne0
      have hosc := (abs_le.mp (tipH_disc_oscillation ζ₀ ζ hζ_ball)).2
      have herr_pt : C₂ * tipEps c' * ‖ζ‖ ^ (5 / 2 : ℝ) +
          C₃ * (tipEps c' * ‖ζ‖) ^ (1 / 2 : ℝ) * Real.log c' ≤ 1 := by
        have hlogc'_nn : 0 ≤ Real.log c' := Real.log_nonneg hc'_gt1.le
        have h1' : C₂ * tipEps c' * ‖ζ‖ ^ (5 / 2 : ℝ) ≤ C₂ * tipEps c' * (R + 1) ^ (5 / 2 : ℝ) := by
          gcongr
        have h2' : C₃ * (tipEps c' * ‖ζ‖) ^ (1 / 2 : ℝ) * Real.log c' ≤
            C₃ * (tipEps c' * (R + 1)) ^ (1 / 2 : ℝ) * Real.log c' := by
          gcongr
        linarith
      have hC₁_le : C₁ ≤ |C₁| := le_abs_self C₁
      dsimp [B, M_const]
      linarith
    have hsub := subharmonic_disc_avg_le hr_pos (fun ζ hζ => han_ball ζ (hball_sub hζ))
      hzero hB_int hB_le
    have hball_vol : volume.real (ball ζ₀ r) = π * r ^ 2 := by
      rw [Measure.real_def, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hr_pos.le, ENNReal.coe_toReal, NNReal.coe_real_pi]
      ring
    have hB_avg : (π * r ^ 2)⁻¹ * ∫ ζ in ball ζ₀ r, B ζ =
        M_const + (π * r ^ 2)⁻¹ * ∫ ζ in ball ζ₀ r, (-Real.log (tipDist ζ)) := by
      dsimp [B]
      rw [integral_add (integrableOn_const (by finiteness : volume (ball ζ₀ r) ≠ ⊤)) havg.1,
        setIntegral_const, hball_vol, smul_eq_mul, mul_add]
      congr 1
      field_simp [Real.pi_pos.ne', hr_pos.ne']
    rw [hB_avg] at hsub
    have hlog_bd1 : Real.log ‖tipRescaleW prob c' test.g ζ₀‖ ≤
        tipH ζ₀ + Real.log C_env + (1 / 2 : ℝ) * Real.log (1 + ‖ζ₀‖) := by
      have h1_r : Real.log (1 / r) = Real.log 2 + (1 / 2 : ℝ) * Real.log (1 + ‖ζ₀‖) := by
        have hpos : 0 < 1 + ‖ζ₀‖ := by positivity
        have h1 : 1 / r = 2 * (1 + ‖ζ₀‖) ^ (1 / 2 : ℝ) := by
          dsimp [r]; rw [Real.rpow_neg hpos.le, one_div_mul_eq_div]; field_simp
        rw [h1, Real.log_mul two_pos.ne' (Real.rpow_pos_of_pos hpos _).ne',
          Real.log_rpow hpos]
      have hlog4 : Real.log 4 = Real.log 2 + Real.log 2 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul two_pos.ne' two_pos.ne']
      have hC_log : Real.log C_env = 3 * KTip / 4 + |C₁| + Real.log 4 + 4 / π + 1 := Real.log_exp _
      dsimp [M_const] at hsub
      linarith [havg.2.1]
    have hbd1 : ‖tipRescaleW prob c' test.g ζ₀‖ ≤
        C_env * (1 + ‖ζ₀‖) ^ (1 / 2 : ℝ) * Real.exp (tipH ζ₀) := by
      have hexp := Real.exp_le_exp.mpr hlog_bd1
      rw [Real.exp_log (norm_pos_iff.mpr hzero), Real.exp_add, Real.exp_add,
        Real.exp_log hCenv_pos, mul_comm (1 / 2 : ℝ) (Real.log (1 + ‖ζ₀‖)),
        ← Real.rpow_def_of_pos (by positivity : 0 < 1 + ‖ζ₀‖)] at hexp
      exact hexp.trans_eq (by ring)
    refine ⟨hbd1, fun him_ne => ?_, fun harg hnorm8 => ?_⟩
    · have him_pos : 0 < |ζ₀.im| := abs_pos.mpr him_ne
      rcases le_or_gt (2 * r) |ζ₀.im| with h2r | h2r
      · have hlog_bd2 : Real.log ‖tipRescaleW prob c' test.g ζ₀‖ ≤
            tipH ζ₀ + Real.log C_env + Real.log (1 / |ζ₀.im|) := by
          have hlog4im : Real.log (4 / |ζ₀.im|) = Real.log 4 + Real.log (1 / |ζ₀.im|) := by
            rw [div_eq_mul_one_div, Real.log_mul (by norm_num) (one_div_pos.mpr him_pos).ne']
          have hC_log : Real.log C_env = 3 * KTip / 4 + |C₁| + Real.log 4 + 4 / π + 1 := Real.log_exp _
          have hpi_nn : 0 ≤ 4 / π := by positivity
          dsimp [M_const] at hsub
          linarith [havg.2.2.1 h2r]
        have hexp := Real.exp_le_exp.mpr hlog_bd2
        rw [Real.exp_log (norm_pos_iff.mpr hzero), Real.exp_add, Real.exp_add,
          Real.exp_log hCenv_pos, Real.exp_log (one_div_pos.mpr him_pos)] at hexp
        have hmin_eq : min ((1 + ‖ζ₀‖) ^ (1 / 2 : ℝ)) (1 / |ζ₀.im|) = 1 / |ζ₀.im| := by
          refine min_eq_right ?_
          have h2r_eq : (1 + ‖ζ₀‖) ^ (1 / 2 : ℝ) = (2 * r)⁻¹ := by
            dsimp [r]
            rw [← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul,
              Real.rpow_neg (by positivity), inv_inv]
          rw [h2r_eq, one_div]
          exact inv_anti₀ (by positivity) h2r
        rw [hmin_eq]
        calc ‖tipRescaleW prob c' test.g ζ₀‖ ≤ Real.exp (tipH ζ₀) * C_env * (1 / |ζ₀.im|) := hexp
          _ ≤ C_env * Real.exp (tipH ζ₀) * (1 + 1 / |ζ₀.im|) := by
              have : 0 ≤ C_env * Real.exp (tipH ζ₀) := by positivity
              nlinarith
      · have hmin_eq : min ((1 + ‖ζ₀‖) ^ (1 / 2 : ℝ)) (1 / |ζ₀.im|) = (1 + ‖ζ₀‖) ^ (1 / 2 : ℝ) := by
          refine min_eq_left ?_
          have h2r_eq : (1 + ‖ζ₀‖) ^ (1 / 2 : ℝ) = (2 * r)⁻¹ := by
            dsimp [r]
            rw [← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul,
              Real.rpow_neg (by positivity), inv_inv]
          rw [h2r_eq, one_div]
          exact (inv_lt_inv₀ (by positivity) him_pos).mpr h2r |>.le
        rw [hmin_eq]
        have : 0 ≤ C_env * Real.exp (tipH ζ₀) := by positivity
        nlinarith [hbd1]
    · have hnorm_pos : 0 < ‖ζ₀‖ := by linarith
      have hlog_bd3 : Real.log ‖tipRescaleW prob c' test.g ζ₀‖ ≤
          tipH ζ₀ + Real.log C_env - Real.log ‖ζ₀‖ := by
        have hlog4norm : -Real.log (‖ζ₀‖ / 4) = Real.log 4 - Real.log ‖ζ₀‖ := by
          rw [Real.log_div hnorm_pos.ne' (by norm_num)]; ring
        have hC_log : Real.log C_env = 3 * KTip / 4 + |C₁| + Real.log 4 + 4 / π + 1 := Real.log_exp _
        have hpi_nn : 0 ≤ 4 / π := by positivity
        dsimp [M_const] at hsub
        linarith [havg.2.2.2 harg hnorm8]
      have hexp := Real.exp_le_exp.mpr hlog_bd3
      rw [Real.exp_log (norm_pos_iff.mpr hzero), sub_eq_add_neg, Real.exp_add, Real.exp_add,
        Real.exp_log hCenv_pos, Real.exp_neg, Real.exp_log hnorm_pos] at hexp
      calc ‖tipRescaleW prob c' test.g ζ₀‖
          ≤ Real.exp (tipH ζ₀) * C_env * ‖ζ₀‖⁻¹ := hexp
        _ = C_env * Real.exp (tipH ζ₀) / ‖ζ₀‖ := by rw [div_eq_mul_inv]; ring

private lemma blowup_band_exp_arg_le {c' C_M1 l : ℝ} (hc'_pos : 0 < c') (hl_ge1 : 1 ≤ l)
    (hlog_c : C_M1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c' ≤ 1) :
    -2.228 * (c' * (tipEps c' * l) ^ ((3 : ℝ) / 2)) +
      C_M1 * Real.sqrt (tipEps c' * l) * Real.log c' ≤ -l := by
  have hl_pos : 0 < l := zero_lt_one.trans_le hl_ge1
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'_pos
  have hcancel_2 : c' * (tipEps c' * l) ^ ((3 : ℝ) / 2) = l ^ ((3 : ℝ) / 2) := by
    rw [Real.mul_rpow hε_pos.le hl_pos.le]; unfold tipEps
    rw [← Real.rpow_mul hc'_pos.le, show -(2 / 3 : ℝ) * (3 / 2) = -1 by norm_num,
      ← mul_assoc, Real.rpow_neg_one, mul_inv_cancel₀ hc'_pos.ne', one_mul]
  have hcancel_3 : Real.sqrt (tipEps c' * l) = c' ^ (-(1 / 3 : ℝ)) * Real.sqrt l := by
    rw [Real.sqrt_mul hε_pos.le, Real.sqrt_eq_rpow]; unfold tipEps
    rw [← Real.rpow_mul hc'_pos.le]; norm_num
  have hCM1_ub : C_M1 * Real.sqrt (tipEps c' * l) * Real.log c' ≤ Real.sqrt l := by
    rw [hcancel_3]
    calc C_M1 * (c' ^ (-(1 / 3 : ℝ)) * Real.sqrt l) * Real.log c'
        = (C_M1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c') * Real.sqrt l := by ring
      _ ≤ 1 * Real.sqrt l := mul_le_mul_of_nonneg_right hlog_c (Real.sqrt_nonneg l)
      _ = Real.sqrt l := one_mul _
  have hsqrt_le_l : Real.sqrt l ≤ l := by
    calc Real.sqrt l ≤ Real.sqrt (l ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = l := Real.sqrt_sq hl_pos.le
  have hl_le_32 : l ≤ l ^ ((3 : ℝ) / 2) := by
    calc l = l ^ (1 : ℝ) := (Real.rpow_one l).symm
      _ ≤ l ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hl_ge1 (by norm_num)
  rw [hcancel_2]
  linarith

private lemma blowup_deep_tail_part {prob : FixedWeightProblem} {c' δ₀ C_deep κ_deep R : ℝ}
    (hc'_pos : 0 < c') (hc'_shift : prob.totalShift ≤ c' / 12)
    (hδ₀_lt : δ₀ < xiStar) (hdeep_le : C_deep * Real.exp (-κ_deep * c') ≤ Real.exp (-R))
    (test : FixedBlowupTest prob c')
    (hg_deep : ∫ t in (0 : ℝ)..(c' * (xiStar - δ₀) ^ 2 / 3),
      |test.g t| * prob.cardyV (c' / 12) t ≤
      C_deep * Real.exp (-κ_deep * c') * prob.cardyNorm (c' / 12) test.g) :
    ∫ s in Ioc (tipSMin c') (-δ₀ / tipEps c'), ‖tipRescaleW prob c' test.g (s : ℂ)‖ ≤
      Real.exp (-R) := by
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'_pos
  have hM_pos : 0 < test.M := test.hM_pos
  let s₀ : ℝ := -δ₀ / tipEps c'
  let t₀ : ℝ := c' * (xiStar - δ₀) ^ 2 / 3
  have ht₀_pos : 0 < t₀ := by positivity [sub_pos.mpr hδ₀_lt]
  have him : tipTReal c' '' Ioc (tipSMin c') s₀ = Ioc 0 t₀ := by
    ext t
    constructor
    · rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
      have hbs_pos : 0 < tipBReal c' s := (tipBReal_pos_iff hc'_pos).mpr hs1
      have hbs_le : tipBReal c' s ≤ xiStar - δ₀ := by
        unfold tipBReal
        have h1 : tipEps c' * s ≤ tipEps c' * s₀ := mul_le_mul_of_nonneg_left hs2 hε_pos.le
        have h2 : tipEps c' * s₀ = -δ₀ := by dsimp [s₀]; field_simp [hε_pos.ne']
        linarith
      have hsq : tipBReal c' s ^ 2 ≤ (xiStar - δ₀) ^ 2 := pow_le_pow_left₀ hbs_pos.le hbs_le 2
      refine ⟨by unfold tipTReal; positivity, ?_⟩
      unfold tipTReal; dsimp [t₀]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hc'_pos.le) (by norm_num)
    · rintro ⟨ht_pos, ht_le⟩
      let s : ℝ := (Real.sqrt (3 * t / c') - xiStar) / tipEps c'
      have hbs : tipBReal c' s = Real.sqrt (3 * t / c') := by
        unfold tipBReal; dsimp [s]; rw [mul_div_cancel₀ _ hε_pos.ne']; ring
      have hs1 : tipSMin c' < s := by rw [← tipBReal_pos_iff hc'_pos, hbs]; positivity
      have hs2 : s ≤ s₀ := by
        have h3t : 3 * t / c' ≤ (xiStar - δ₀) ^ 2 := by
          dsimp [t₀] at ht_le; rw [div_le_iff₀ hc'_pos]; linarith
        have hsq : Real.sqrt (3 * t / c') ≤ xiStar - δ₀ := by
          rw [← Real.sqrt_sq (sub_pos.mpr hδ₀_lt).le]; exact Real.sqrt_le_sqrt h3t
        have h1 : tipEps c' * s ≤ tipEps c' * s₀ := by
          have h2 : tipEps c' * s₀ = -δ₀ := by dsimp [s₀]; field_simp [hε_pos.ne']
          unfold tipBReal at hbs; linarith
        exact le_of_mul_le_mul_left h1 hε_pos
      refine ⟨s, ⟨hs1, hs2⟩, ?_⟩
      unfold tipTReal; rw [hbs, Real.sq_sqrt (by positivity)]; field_simp [hc'_pos.ne']
  have hcov := integral_image_eq_integral_abs_deriv_smul (s := Ioc (tipSMin c') s₀)
    measurableSet_Ioc
    (fun s _ => (tipTReal_deriv (c' := c') (s := s)).hasDerivWithinAt)
    ((tipTReal_injOn hc'_pos).mono Ioc_subset_Ioi_self)
    (fun t => (test.M)⁻¹ * (|test.g t| * prob.cardyV (c' / 12) t))
  rw [him] at hcov
  have heq : EqOn (fun s : ℝ => ‖tipRescaleW prob c' test.g (s : ℂ)‖)
      (fun s => |tipEps c' * (2 * c' / 3) * tipBReal c' s| •
        ((test.M)⁻¹ * (|test.g (tipTReal c' s)| * prob.cardyV (c' / 12) (tipTReal c' s))))
      (Ioc (tipSMin c') s₀) := fun s hs => by
    have hbs : 0 < tipBReal c' s := (tipBReal_pos_iff hc'_pos).mpr hs.1
    have hts : 0 < tipTReal c' s := by unfold tipTReal; positivity
    have h1_nn : 0 ≤ tipEps c' * (2 * c' / 3) := by positivity
    have hder_nn : 0 ≤ tipEps c' * (2 * c' / 3) * tipBReal c' s := mul_nonneg h1_nn hbs.le
    have hV_nn : 0 ≤ prob.cardyV (c' / 12) (tipTReal c' s) :=
      prob.cardyV_nonneg hc'_shift hts.le
    dsimp only
    rw [tipRescaleW_real_on_real hc'_pos test.hg_test s, Complex.norm_real, Real.norm_eq_abs,
      smul_eq_mul, abs_of_nonneg hder_nn, abs_div, abs_of_pos test.hM_pos, abs_mul,
      abs_mul, abs_mul, abs_of_nonneg h1_nn, abs_of_nonneg hbs.le, abs_of_nonneg hV_nn]
    unfold FixedBlowupTest.M; ring
  have hg_bd : ∫ t in (0 : ℝ)..t₀, |test.g t| * prob.cardyV (c' / 12) t ≤
      C_deep * Real.exp (-κ_deep * c') * test.M := by
    simpa [FixedBlowupTest.M] using hg_deep
  dsimp [s₀] at heq hcov
  rw [setIntegral_congr_fun measurableSet_Ioc heq, ← hcov, integral_const_mul,
    ← intervalIntegral.integral_of_le ht₀_pos.le]
  calc (test.M)⁻¹ * ∫ t in (0 : ℝ)..t₀, |test.g t| * prob.cardyV (c' / 12) t
      ≤ (test.M)⁻¹ * (C_deep * Real.exp (-κ_deep * c') * test.M) :=
        mul_le_mul_of_nonneg_left hg_bd (inv_nonneg.mpr hM_pos.le)
    _ = C_deep * Real.exp (-κ_deep * c') := by field_simp [hM_pos.ne']
    _ ≤ Real.exp (-R) := hdeep_le

/-- Uniform left-tail estimate at general `(w, Q)` (`blowup_limit.tex`, Proposition T (v)):
splits at `δ₀ = D.r_1` into the deep lobe `[0, c' (ξ_* - D.r_1)² / 3]` (controlled by
`D.lemmaG`) and the band edge `[ξ_* - D.r_1, ξ_* - ε R]` inside `closedBall ξ_* D.r_1`
(controlled directly by `W_C_prob_norm_le` and `proposition_M_general`, where
`c'^{-1/6} · c'^{-1/2} · ε⁻¹ = 1` cancels identically). -/
theorem blowup_left_tail_bound_general (prob : FixedWeightProblem)
    (D : UniformPropositionPData prob) :
    ∃ η : ℝ → ℝ, Tendsto η atTop (nhds 0) ∧
      ∀ R : ℝ, 1 ≤ R → ∀ᶠ c' : ℝ in atTop,
        prob.totalShift ≤ c' / 12 → ∀ test : FixedBlowupTest prob c',
          ∫ s in Ioc (tipSMin c') (-R), ‖tipRescaleW prob c' test.g (s : ℂ)‖ ≤ η R := by
  have hδ₀_pos : 0 < D.r_1 := D.hr1_pos
  have hδ₀_lt : D.r_1 < xiStar := D.hr1_le.trans_lt (half_lt_self xiStar_pos)
  obtain ⟨c_deep, C_deep, κ_deep, hc_deep1, hC_deep_pos, hκ_deep_pos, hdeep⟩ :=
    D.lemmaG hδ₀_pos hδ₀_lt
  obtain ⟨c_Kw, C_Klo, hcKw8, hCKlo, hPJ_thm⟩ := stripPoissonJensen_general prob
  obtain ⟨C_PJ, hC_PJ_eq⟩ :
      ∃ C_PJ : ℝ, C_PJ = pjConstOf D.C_e D.c_band C_Klo (slitL xiStar) := ⟨_, rfl⟩
  obtain ⟨c_PJ, hc_PJ_eq⟩ : ∃ c_PJ : ℝ, c_PJ = max (max D.c₀ c_Kw) 1 := ⟨_, rfl⟩
  have hcPJ1 : 1 ≤ c_PJ := hc_PJ_eq ▸ le_max_right _ _
  obtain ⟨C_M1, C_M2, hCM1_nn, hpropM⟩ := proposition_M_general realSliceData
    (C_PJ := C_PJ) (p_e := D.p_e) hcPJ1 D.hp_e_nn
  obtain ⟨C_Q, hCQ_gt0, hCQ_D⟩ :
      ∃ C_Q : ℝ, 0 < C_Q ∧ ∀ b ∈ closedBall (xiStar : ℂ) D.r_1, ‖D.Q_star b‖ ≤ C_Q := by
    let P₀ := D.pAt (le_rfl : D.c₀ ≤ D.c₀)
    obtain ⟨c_Q_min, C_Q, hcQ_pos, hcQ_le, hCQ0⟩ :=
      disc_Q_bounds D.hr1_pos.le D.hr1_le (Q_star := D.Q_star)
        (by rw [← D.uniform_Q_star (le_rfl : D.c₀ ≤ D.c₀)]; exact P₀.p2_Q_holo)
        (fun {b} hb => by
          rw [← D.uniform_Q_star (le_rfl : D.c₀ ≤ D.c₀)]
          exact P₀.p2_Q_ne_zero (by rwa [D.uniform_r_1 (le_rfl : D.c₀ ≤ D.c₀)]))
    exact ⟨C_Q, hcQ_pos.trans_le hcQ_le, fun b hb => (hCQ0 b hb).2⟩
  obtain ⟨C_W_tot, hCW_pos, hCW_ge⟩ :
      ∃ C_W_tot : ℝ, 0 < C_W_tot ∧
        ((3 * xiStar / 2) * (3 * xiStar) ^ (prob.w - 1) * (2 / 3 : ℝ) /
          Real.sqrt (2 * π ^ 2 * xiStar / 3)) * (C_Q + D.η_V_max) ≤ C_W_tot ∧
        0 ≤ (3 * xiStar / 2) * (3 * xiStar) ^ (prob.w - 1) * (2 / 3 : ℝ) /
          Real.sqrt (2 * π ^ 2 * xiStar / 3) := by
    let fac : ℝ := (3 * xiStar / 2) * (3 * xiStar) ^ (prob.w - 1) * (2 / 3 : ℝ) /
      Real.sqrt (2 * π ^ 2 * xiStar / 3)
    have hfac : 0 ≤ fac := by dsimp [fac]; positivity [xiStar_pos]
    have hprod_nn : 0 ≤ fac * (C_Q + D.η_V_max) :=
      mul_nonneg hfac (add_nonneg hCQ_gt0.le D.hηV_max_nn)
    exact ⟨fac * (C_Q + D.η_V_max) + 1, by linarith, by linarith, hfac⟩
  obtain ⟨C_pref, hC_pref_pos, hC_pref_eq⟩ :
      ∃ C_pref : ℝ, 0 < C_pref ∧ C_pref = C_W_tot * Real.exp C_M2 :=
    ⟨C_W_tot * Real.exp C_M2, mul_pos hCW_pos (Real.exp_pos C_M2), rfl⟩
  refine ⟨fun R => (C_pref + 1) * Real.exp (-R), ?_, fun R hR => ?_⟩
  · simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul (C_pref + 1)
  have hc_log_bound : ∀ {c' : ℝ}, 1 ≤ c' → (max 1 (6 * C_M1)) ^ 6 ≤ c' →
      C_M1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c' ≤ 1 := fun {c'} _ hc'_log => by
    have hc'_pos : 0 < c' := lt_of_lt_of_le (by positivity) hc'_log
    have hc'_16 : max 1 (6 * C_M1) ≤ c' ^ ((1 : ℝ) / 6) := by
      have := Real.rpow_le_rpow (by positivity) hc'_log (by norm_num : (0 : ℝ) ≤ 1 / 6)
      rwa [← Real.rpow_natCast (max 1 (6 * C_M1)) 6, ← Real.rpow_mul (by positivity),
        show ((6 : ℕ) : ℝ) * (1 / 6) = 1 by norm_num, Real.rpow_one] at this
    have hlog_le : Real.log c' ≤ 6 * c' ^ ((1 : ℝ) / 6) := by
      have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hc'_pos (1 / 6))
      rw [Real.log_rpow hc'_pos] at h1; linarith
    have hpow_comb : c' ^ (-(1 / 3 : ℝ)) * c' ^ ((1 / 6 : ℝ)) = (c' ^ ((1 / 6 : ℝ)))⁻¹ := by
      rw [← Real.rpow_add hc'_pos, ← Real.rpow_neg hc'_pos.le]; norm_num
    calc C_M1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c'
        ≤ C_M1 * c' ^ (-(1 / 3 : ℝ)) * (6 * c' ^ ((1 / 6 : ℝ))) := by gcongr
      _ = (6 * C_M1) * (c' ^ ((1 / 6 : ℝ)))⁻¹ := by rw [← hpow_comb]; ring
      _ ≤ (c' ^ ((1 / 6 : ℝ))) * (c' ^ ((1 / 6 : ℝ)))⁻¹ := by
          gcongr; exact (le_max_right 1 (6 * C_M1)).trans hc'_16
      _ = 1 := mul_inv_cancel₀ (Real.rpow_pos_of_pos hc'_pos _).ne'
  have hdeep_ev : ∀ᶠ c' : ℝ in atTop,
      C_deep * Real.exp (-κ_deep * c') ≤ Real.exp (-R) := by
    have htend : Tendsto (fun c' : ℝ => C_deep * Real.exp (-κ_deep * c')) atTop (nhds 0) := by
      have harg : Tendsto (fun c' : ℝ => -κ_deep * c') atTop atBot := by
        simpa [neg_mul] using tendsto_neg_atBot_iff.mpr (tendsto_id.const_mul_atTop hκ_deep_pos)
      simpa using (Real.tendsto_exp_atBot.comp harg).const_mul C_deep
    exact htend.eventually (eventually_le_nhds (Real.exp_pos (-R)))
  have hεR_ev : ∀ᶠ c' : ℝ in atTop, tipEps c' * R < D.r_1 := by
    have h0 : Tendsto (fun c' : ℝ => tipEps c' * R) atTop (nhds 0) := by
      simpa [tipEps] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).mul_const R
    exact h0.eventually (eventually_lt_nhds hδ₀_pos)
  filter_upwards [eventually_ge_atTop (max c_PJ c_deep),
    eventually_ge_atTop ((max 1 (6 * C_M1)) ^ 6),
    hdeep_ev, hεR_ev] with c' hc'_base hc'_log hdeep_le hεR_lt
  have hc'_PJ : c_PJ ≤ c' := (le_max_left _ _).trans hc'_base
  have hc'_PJ_max : max (max D.c₀ c_Kw) 1 ≤ c' := hc_PJ_eq ▸ hc'_PJ
  have hc'_D : D.c₀ ≤ c' := ((le_max_left D.c₀ c_Kw).trans (le_max_left _ _)).trans hc'_PJ_max
  have hc'_Kw : c_Kw ≤ c' := ((le_max_right D.c₀ c_Kw).trans (le_max_left _ _)).trans hc'_PJ_max
  have hc'_deep : c_deep ≤ c' := (le_max_right _ _).trans hc'_base
  have hc'_ge1 : 1 ≤ c' := hcPJ1.trans hc'_PJ
  have hc'_pos : 0 < c' := by linarith
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'_pos
  intro hc'_shift test
  have hM_pos : 0 < test.M := test.hM_pos
  obtain ⟨s₀, hs₀_eq⟩ : ∃ s₀ : ℝ, s₀ = -D.r_1 / tipEps c' := ⟨_, rfl⟩
  have hs₀_gt_min : tipSMin c' < s₀ := by
    rw [hs₀_eq, tipSMin_eq_neg_div_tipEps hc'_pos]
    exact div_lt_div_of_pos_right (by linarith [hδ₀_lt]) hε_pos
  have hs₀_lt_negR : s₀ < -R := by
    rw [hs₀_eq, div_lt_iff₀ hε_pos]; linarith [hεR_lt]
  have hint_dom : IntegrableOn (fun s : ℝ => ‖tipRescaleW prob c' test.g (s : ℂ)‖)
      (Ioi (tipSMin c')) :=
    (tipRescaleW_integrableOn_domain hc'_pos hc'_shift test).norm
  have hint_Ioc : IntegrableOn (fun s : ℝ => ‖tipRescaleW prob c' test.g (s : ℂ)‖)
      (Ioc (tipSMin c') (-R)) :=
    hint_dom.mono_set Ioc_subset_Ioi_self
  have hsplit : ∫ s in Ioc (tipSMin c') (-R), ‖tipRescaleW prob c' test.g (s : ℂ)‖ =
      (∫ s in Ioc (tipSMin c') s₀, ‖tipRescaleW prob c' test.g (s : ℂ)‖) +
        ∫ s in Ioc s₀ (-R), ‖tipRescaleW prob c' test.g (s : ℂ)‖ := by
    rw [← Ioc_union_Ioc_eq_Ioc hs₀_gt_min.le hs₀_lt_negR.le]
    exact setIntegral_union (Ioc_disjoint_Ioc_of_le (le_rfl : s₀ ≤ s₀)) measurableSet_Ioc
      (hint_Ioc.mono_set (Ioc_subset_Ioc_right hs₀_lt_negR.le))
      (hint_Ioc.mono_set (Ioc_subset_Ioc_left hs₀_gt_min.le))
  -- Part A: Deep tail `[0, c' (xiStar - D.r_1)² / 3]` via `D.lemmaG`.
  have hdeep_part : ∫ s in Ioc (tipSMin c') s₀, ‖tipRescaleW prob c' test.g (s : ℂ)‖ ≤
      Real.exp (-R) := by
    rw [hs₀_eq]
    exact blowup_deep_tail_part hc'_pos hc'_shift hδ₀_lt hdeep_le test
      (hdeep hc'_deep test.hg_test)
  -- Part B: Band edge `s ∈ (s₀, -R]`, where `b = xiStar + ε s ∈ closedBall ξ_* D.r_1`.
  have hband_part : ∫ s in Ioc s₀ (-R), ‖tipRescaleW prob c' test.g (s : ℂ)‖ ≤
      C_pref * Real.exp (-R) := by
    have hPJ_real : ∀ x ∈ Ico 0 xiStar, test.g (c' * x ^ 2 / 3) ≠ 0 →
        Real.log |test.g (c' * x ^ 2 / 3)| ≤ c' * majorantReal x + Real.log test.M -
          (1 / 2 : ℝ) * Real.log c' + (D.p_e + 1 / 2) * (1 - realSliceData.slitMassAt x) * Real.log c' +
          realSliceData.slitEntropyAt x + C_PJ := fun x hx hne => by
      let P := D.pAt hc'_D
      have h1 := hPJ_thm P hc'_Kw test.hg_test test.hM_pos x hx hne
      rw [D.uniform_C_e hc'_D, D.uniform_p_e hc'_D, D.uniform_c_band hc'_D, ← hC_PJ_eq] at h1
      simpa [FixedBlowupTest.M] using h1
    have hprop := hpropM hc'_PJ hM_pos hPJ_real
    have hlog_c := hc_log_bound hc'_ge1 hc'_log
    have hW_bound_disc : ∀ x : ℝ, (x : ℂ) ∈ closedBall (xiStar : ℂ) D.r_1 →
        ‖W_C_prob prob c' (x : ℂ)‖ ≤
          C_W_tot * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * ((2 * π / 3) * x)) := by
      intro x hb_D
      let P := D.pAt hc'_D
      have hb_disc : (x : ℂ) ∈ closedBall (xiStar : ℂ) P.r_1 := by
        rwa [D.uniform_r_1 hc'_D]
      have hCQ_P : ∀ b' ∈ closedBall (xiStar : ℂ) P.r_1, ‖P.Q_star b'‖ ≤ C_Q := fun b' hb' => by
        rw [D.uniform_Q_star hc'_D]
        exact hCQ_D b' (by rwa [← D.uniform_r_1 hc'_D])
      have htre : (tipL (x : ℂ)).re = (2 * π / 3) * x := by
        unfold tipL; rw [Complex.re_ofReal_mul, Complex.ofReal_re]
      have hW_raw := W_C_prob_norm_le P hCQ_P hb_disc
      dsimp only at hW_raw
      rw [htre] at hW_raw
      have h1 : ((3 * xiStar / 2) * (3 * xiStar) ^ (prob.w - 1) * (2 / 3 : ℝ) /
            Real.sqrt (2 * π ^ 2 * xiStar / 3)) * (C_Q + P.η_V) ≤ C_W_tot := by
        have hsum_le : C_Q + P.η_V ≤ C_Q + D.η_V_max := by linarith [D.uniform_ηV_le hc'_D]
        exact (mul_le_mul_of_nonneg_left hsum_le hCW_ge.2).trans hCW_ge.1
      exact hW_raw.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hc'_pos.le _)) (Real.exp_pos _).le)
    have hpt_s : ∀ s ∈ Ioc s₀ (-R),
        ‖tipRescaleW prob c' test.g (s : ℂ)‖ ≤ C_pref * Real.exp s := fun s hs => by
      obtain ⟨x, hx_def⟩ : ∃ x : ℝ, x = tipBReal c' s := ⟨_, rfl⟩
      obtain ⟨l, hl_def⟩ : ∃ l : ℝ, l = -s := ⟨_, rfl⟩
      have hl_ge_R : R ≤ l := by linarith [hl_def, hs.2]
      have hl_ge1 : 1 ≤ l := hR.trans hl_ge_R
      have hl_pos : 0 < l := zero_lt_one.trans_le hl_ge1
      have hεl_le : tipEps c' * l ≤ D.r_1 := by
        have hs1 : -D.r_1 / tipEps c' < s := hs₀_eq ▸ hs.1
        have hs1' : -D.r_1 < s * tipEps c' := (div_lt_iff₀ hε_pos).mp hs1
        linarith [show tipEps c' * l = -(s * tipEps c') by rw [hl_def]; ring]
      have hεl_pos : 0 < tipEps c' * l := mul_pos hε_pos hl_pos
      have hx_eq_sub : x = xiStar - tipEps c' * l := by
        rw [hx_def, hl_def]; unfold tipBReal; ring
      have hx_nn : 0 ≤ x := by linarith [hx_eq_sub, hεl_le, hδ₀_lt]
      have hx_lt_xi : x < xiStar := by linarith [hx_eq_sub, hεl_pos]
      have hx_mem : x ∈ Ico 0 xiStar := ⟨hx_nn, hx_lt_xi⟩
      have hdx : xiStar - x = tipEps c' * l := by linarith [hx_eq_sub]
      have hb_D : (x : ℂ) ∈ closedBall (xiStar : ℂ) D.r_1 := by
        rw [mem_closedBall, dist_eq_norm,
          ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
          abs_of_nonneg (sub_pos.mpr hx_lt_xi).le, hdx]
        exact hεl_le
      have hW_bd := hW_bound_disc x hb_D
      have hG_bd : |test.g (c' * x ^ 2 / 3)| / test.M ≤
          Real.exp C_M2 * c' ^ (-(1 / 2 : ℝ)) * (tipEps c' * l)⁻¹ *
            Real.exp (c' * majorantReal x + C_M1 * Real.sqrt (tipEps c' * l) * Real.log c') := by
        by_cases hg0 : test.g (c' * x ^ 2 / 3) = 0
        · rw [hg0, abs_zero, zero_div]; positivity
        · have hexp := Real.exp_le_exp.mpr (hprop x hx_mem hg0)
          rw [Real.exp_log (abs_pos.mpr hg0), hdx] at hexp
          have hpow : Real.exp (-(1 / 2 : ℝ) * Real.log c') = c' ^ (-(1 / 2 : ℝ)) := by
            rw [Real.rpow_def_of_pos hc'_pos]; ring_nf
          have hdx_eq : Real.exp (Real.log (1 / (tipEps c' * l))) = (tipEps c' * l)⁻¹ := by
            rw [one_div, Real.exp_log (inv_pos.mpr hεl_pos)]
          have hrew_arg : c' * majorantReal x + Real.log test.M - (1 / 2 : ℝ) * Real.log c' +
                C_M1 * Real.sqrt (tipEps c' * l) * Real.log c' +
                Real.log (1 / (tipEps c' * l)) + C_M2 =
              C_M2 + Real.log test.M + (-(1 / 2 : ℝ) * Real.log c') +
                Real.log (1 / (tipEps c' * l)) +
                (c' * majorantReal x + C_M1 * Real.sqrt (tipEps c' * l) * Real.log c') := by
            ring
          have hmul : |test.g (c' * x ^ 2 / 3)| ≤
              Real.exp C_M2 * test.M * c' ^ (-(1 / 2 : ℝ)) * (tipEps c' * l)⁻¹ *
                Real.exp (c' * majorantReal x + C_M1 * Real.sqrt (tipEps c' * l) * Real.log c') := by
            refine hexp.trans_eq ?_
            rw [hrew_arg, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add,
              Real.exp_log hM_pos, hpow, hdx_eq]
          exact (div_le_div_of_nonneg_right hmul hM_pos.le).trans_eq (by
            field_simp [hM_pos.ne'])
      have hPhi_eq : ‖tipRescaleW prob c' test.g (s : ℂ)‖ =
          ‖W_C_prob prob c' (x : ℂ)‖ * (|test.g (c' * x ^ 2 / 3)| / test.M) := by
        unfold tipRescaleW
        rw [bScale_ofReal, ← hx_def]
        change ‖W_C_prob prob c' (x : ℂ) * hankelContinuationW prob.w c' test.g (x : ℂ) /
            (test.M : ℂ)‖ = _
        rw [hankelContinuationW_ofReal_all hc'_pos test.hg_test x, norm_div, norm_mul,
          Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos hM_pos]
        ring
      have hc_cancel : c' ^ (-(1 / 6 : ℝ)) * c' ^ (-(1 / 2 : ℝ)) * (tipEps c' * l)⁻¹ = l⁻¹ := by
        have hp1 : (tipEps c' * l)⁻¹ = c' ^ (2 / 3 : ℝ) * l⁻¹ := by
          unfold tipEps; rw [mul_inv, ← Real.rpow_neg hc'_pos.le, neg_neg]
        rw [hp1, ← mul_assoc, ← Real.rpow_add hc'_pos, ← Real.rpow_add hc'_pos]
        norm_num
      have hexp_arg : c' * (majorantReal x + (2 * π / 3) * x) +
          C_M1 * Real.sqrt (tipEps c' * l) * Real.log c' ≤ -l := by
        have hdef_ub : c' * (majorantReal x + (2 * π / 3) * x) ≤
            -2.228 * (c' * (tipEps c' * l) ^ ((3 : ℝ) / 2)) := by
          have h1 := majorantReal_g_deficit hx_mem
          have h2 := slitDeficit_ge hεl_pos.le (hεl_le.trans hδ₀_lt.le)
          rw [hdx] at h1
          have h3 : majorantReal x + (2 * π / 3) * x ≤
              -2.228 * (tipEps c' * l) ^ ((3 : ℝ) / 2) :=
            (h1.trans (neg_le_neg h2)).trans_eq (by ring)
          exact (mul_le_mul_of_nonneg_left h3 hc'_pos.le).trans_eq (by ring)
        exact (add_le_add hdef_ub le_rfl).trans (blowup_band_exp_arg_le hc'_pos hl_ge1 hlog_c)
      have hW_rhs_nn : 0 ≤ C_W_tot * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * ((2 * π / 3) * x)) :=
        mul_nonneg (mul_nonneg hCW_pos.le (Real.rpow_nonneg hc'_pos.le _)) (Real.exp_pos _).le
      have hprod := mul_le_mul hW_bd hG_bd (div_nonneg (abs_nonneg _) hM_pos.le) hW_rhs_nn
      rw [hPhi_eq]
      calc ‖W_C_prob prob c' (x : ℂ)‖ * (|test.g (c' * x ^ 2 / 3)| / test.M)
          ≤ (C_W_tot * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * ((2 * π / 3) * x))) *
              (Real.exp C_M2 * c' ^ (-(1 / 2 : ℝ)) * (tipEps c' * l)⁻¹ *
                Real.exp (c' * majorantReal x + C_M1 * Real.sqrt (tipEps c' * l) * Real.log c')) := hprod
        _ = (C_W_tot * Real.exp C_M2) * (c' ^ (-(1 / 6 : ℝ)) * c' ^ (-(1 / 2 : ℝ)) * (tipEps c' * l)⁻¹) *
              (Real.exp (c' * ((2 * π / 3) * x)) *
                Real.exp (c' * majorantReal x + C_M1 * Real.sqrt (tipEps c' * l) * Real.log c')) := by
            ring
        _ = C_pref * l⁻¹ *
              Real.exp (c' * (majorantReal x + (2 * π / 3) * x) +
                C_M1 * Real.sqrt (tipEps c' * l) * Real.log c') := by
            rw [hc_cancel, ← Real.exp_add, ← hC_pref_eq]; congr 2; ring
        _ ≤ C_pref * 1 * Real.exp (-l) := by
            have hl_inv : l⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hl_ge1
            have hexp_le : Real.exp (c' * (majorantReal x + (2 * π / 3) * x) +
                C_M1 * Real.sqrt (tipEps c' * l) * Real.log c') ≤ Real.exp (-l) :=
              Real.exp_le_exp.mpr hexp_arg
            exact mul_le_mul (mul_le_mul_of_nonneg_left hl_inv hC_pref_pos.le) hexp_le
              (Real.exp_pos _).le (mul_nonneg hC_pref_pos.le zero_le_one)
        _ = C_pref * Real.exp s := by rw [hl_def, neg_neg, mul_one]
    have hint_rhs : IntegrableOn (fun s : ℝ => C_pref * Real.exp s) (Ioc s₀ (-R)) :=
      (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioc_subset_Icc_self
    have hint_lhs : IntegrableOn (fun s : ℝ => ‖tipRescaleW prob c' test.g (s : ℂ)‖) (Ioc s₀ (-R)) :=
      hint_Ioc.mono_set (Ioc_subset_Ioc_left hs₀_gt_min.le)
    have hmono := setIntegral_mono_on hint_lhs hint_rhs measurableSet_Ioc hpt_s
    have hint_eval : ∫ s in Ioc s₀ (-R), C_pref * Real.exp s ≤ C_pref * Real.exp (-R) := by
      rw [← intervalIntegral.integral_of_le hs₀_lt_negR.le, intervalIntegral.integral_const_mul]
      have hd : ∀ s ∈ uIcc s₀ (-R), HasDerivAt (fun t : ℝ => Real.exp t) (Real.exp s) s :=
        fun s _ => Real.hasDerivAt_exp s
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (Continuous.intervalIntegrable (by fun_prop) _ _)]
      exact mul_le_mul_of_nonneg_left (sub_le_self _ (Real.exp_pos s₀).le) hC_pref_pos.le
    exact hmono.trans hint_eval
  rw [hsplit]
  calc (∫ s in Ioc (tipSMin c') s₀, ‖tipRescaleW prob c' test.g (s : ℂ)‖) +
        ∫ s in Ioc s₀ (-R), ‖tipRescaleW prob c' test.g (s : ℂ)‖
      ≤ Real.exp (-R) + C_pref * Real.exp (-R) := add_le_add hdeep_part hband_part
    _ = (C_pref + 1) * Real.exp (-R) := by ring

/-- Unconditional lower bound `s₁ ≥ -C₀` at general `(w, Q)` derived directly from
`theorem_A_general` (`PoissonJensenGeneral.lean`), requiring NO unproved hypotheses
(Theorem `W1'(1)` is not needed for this a priori bound). -/
theorem tipS₁W_theorem_A_lower_general (prob : FixedWeightProblem) :
    ∃ C₀ c_A : ℝ, 0 < C₀ ∧ max 1 (24 * prob.totalShift) ≤ c_A ∧
      ∀ {c' : ℝ}, c_A ≤ c' → ∀ test : FixedBlowupTest prob c', -C₀ ≤ tipS₁W c' test := by
  obtain ⟨C_A, c_A_raw, hCA_pos, hcA1, hA⟩ := theorem_A_general prob
  let c_A : ℝ := max c_A_raw (max 1 (24 * prob.totalShift))
  let C₀ : ℝ := 3 * C_A / xiStar
  have hC₀_pos : 0 < C₀ := by positivity [xiStar_pos]
  refine ⟨C₀, c_A, hC₀_pos, le_max_right _ _, fun {c'} hc' test => ?_⟩
  have hc'_A : c_A_raw ≤ c' := (le_max_left _ _).trans hc'
  have hc'_ge1 : 1 ≤ c' := (le_max_left 1 (24 * prob.totalShift)).trans ((le_max_right _ _).trans hc')
  have hc'_pos : 0 < c' := lt_of_lt_of_le zero_lt_one hc'_ge1
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'_pos
  have hwt : xiBar * c' - C_A * c' ^ ((1 : ℝ) / 3) ≤ test.t₁ :=
    hA hc'_A test.isWeaklyFeasible
  rcases le_or_gt 0 (tipS₁W c' test) with hpos | _
  · linarith
  · have hdiff_sq : (xiStar - test.x₁ c') * (xiStar + test.x₁ c') =
        xiStar ^ 2 - (test.x₁ c') ^ 2 := by ring
    have hsq_bd : xiStar ^ 2 - (test.x₁ c') ^ 2 ≤ 3 * C_A * tipEps c' := by
      have ht₁ : xiStar ^ 2 / 3 * c' - C_A * c' ^ (1 / 3 : ℝ) ≤ c' * (test.x₁ c') ^ 2 / 3 := by
        rw [test.t₁_eq_x₁_sq hc'_pos, xiBar] at hwt
        linarith
      have hc13 : c' ^ (1 / 3 : ℝ) = c' * tipEps c' := by
        unfold tipEps
        calc c' ^ (1 / 3 : ℝ) = c' ^ (1 + -(2 / 3 : ℝ)) := by norm_num
          _ = c' ^ (1 : ℝ) * c' ^ (-(2 / 3 : ℝ)) := Real.rpow_add hc'_pos _ _
          _ = c' * c' ^ (-(2 / 3 : ℝ)) := by rw [Real.rpow_one]
      have hmul : c' * (xiStar ^ 2 - (test.x₁ c') ^ 2) ≤ c' * (3 * C_A * tipEps c') := by
        rw [hc13] at ht₁; linarith
      exact le_of_mul_le_mul_left hmul hc'_pos
    have hx₁_nn : 0 ≤ test.x₁ c' := Real.sqrt_nonneg _
    have hsum_ge : xiStar ≤ xiStar + test.x₁ c' := by linarith
    have hlt : test.x₁ c' < xiStar := by
      by_contra hge
      push Not at hge
      have : 0 ≤ tipS₁W c' test := div_nonneg (sub_nonneg.mpr hge) hε_pos.le
      linarith [show tipS₁W c' test < 0 from by assumption]
    have hsub_nn : 0 ≤ xiStar - test.x₁ c' := by linarith
    have hlin : (xiStar - test.x₁ c') * xiStar ≤ 3 * C_A * tipEps c' :=
      (mul_le_mul_of_nonneg_left hsum_ge hsub_nn).trans (hdiff_sq ▸ hsq_bd)
    have hdiv : xiStar - test.x₁ c' ≤ C₀ * tipEps c' := by
      dsimp [C₀]
      calc xiStar - test.x₁ c' = ((xiStar - test.x₁ c') * xiStar) / xiStar := by
            field_simp [xiStar_pos.ne']
        _ ≤ (3 * C_A * tipEps c') / xiStar := div_le_div_of_nonneg_right hlin xiStar_pos.le
        _ = (3 * C_A / xiStar) * tipEps c' := by ring
    unfold tipS₁W
    rw [le_div_iff₀ hε_pos]
    linarith

/-- Compatibility bridge with **Theorem W1'(1)** (`FixedWeight.FixedWeightLowerBoundInput prob`):
while `tipS₁W_theorem_A_lower_general` proves `s₁ ≥ -C₀` unconditionally from Theorem `A`
alone (cf. TeX over-citation of `W1'(1)` in `bl:T`), any sequence whose thresholds stay within
`O(1)` below `prob.T_V (c' n)` ALSO satisfies `s₁ ≥ -C₀` directly from
`FixedWeight.FixedWeightLowerBoundInput prob`. -/
theorem theorem_A_lower_from_lowerBoundInput {prob : FixedWeightProblem}
    (hLo : FixedWeightLowerBoundInput prob) {ι : Type*} {p : Filter ι}
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop)
    {tests : ∀ n : ι, FixedBlowupTest prob (c' n)}
    (hTV_le : ∃ D₀ : ℝ, ∀ᶠ n in p,
      prob.T_V (c' n) - D₀ ≤ (tests n).t₁) :
    ∃ C₀ : ℝ, ∀ᶠ n in p, -C₀ ≤ tipS₁W (c' n) (tests n) := by
  obtain ⟨c₁, D_minus, hc1, hD_nn, hbound⟩ := hLo
  obtain ⟨D₀, hD₀_ev⟩ := hTV_le
  let C_shift : ℝ := |Aopt| + D_minus + |D₀|
  have hC_nn : 0 ≤ C_shift := by dsimp [C_shift]; positivity
  refine ⟨3 * C_shift / xiStar + 1, ?_⟩
  filter_upwards [hc'.eventually (eventually_ge_atTop (max c₁ (max 1 (24 * prob.totalShift)))),
    hD₀_ev] with n hc'n ht_n
  have hc1_c' : c₁ ≤ c' n := (le_max_left _ _).trans hc'n
  have hc'_ge1 : 1 ≤ c' n := (le_max_left 1 _).trans ((le_max_right _ _).trans hc'n)
  have hc'_pos : 0 < c' n := lt_of_lt_of_le zero_lt_one hc'_ge1
  have hε_pos : 0 < tipEps (c' n) := tipEps_pos hc'_pos
  have htv := hbound hc1_c'
  unfold TStar at htv
  have hc_le1 : 1 ≤ c' n ^ ((1 : ℝ) / 3) := Real.one_le_rpow hc'_ge1 (by norm_num)
  have hAopt_lb : -(|Aopt| * c' n ^ ((1 : ℝ) / 3)) ≤ Aopt * c' n ^ ((1 : ℝ) / 3) := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le Aopt)
      (by positivity : 0 ≤ c' n ^ ((1 : ℝ) / 3))
    linarith
  have hD_lb : D_minus + D₀ ≤ (D_minus + |D₀|) * c' n ^ ((1 : ℝ) / 3) := by
    have h1 : D₀ ≤ |D₀| := le_abs_self D₀
    have h2 : 0 ≤ D_minus + |D₀| := by positivity
    nlinarith
  have ht1_lt : xiBar * c' n - C_shift * c' n ^ ((1 : ℝ) / 3) ≤ (tests n).t₁ := by
    dsimp [C_shift]
    linarith [htv, ht_n, hAopt_lb, hD_lb]
  rcases le_or_gt 0 (tipS₁W (c' n) (tests n)) with hpos | _
  · linarith [show 0 ≤ 3 * C_shift / xiStar + 1 by positivity [xiStar_pos, hC_nn]]
  · have hx₁_nn : 0 ≤ (tests n).x₁ (c' n) := Real.sqrt_nonneg _
    have hlt : (tests n).x₁ (c' n) < xiStar := by
      by_contra hge
      push Not at hge
      have : 0 ≤ tipS₁W (c' n) (tests n) := div_nonneg (sub_nonneg.mpr hge) hε_pos.le
      linarith [show tipS₁W (c' n) (tests n) < 0 from by assumption]
    have hsq_bd : xiStar ^ 2 - ((tests n).x₁ (c' n)) ^ 2 ≤ 3 * C_shift * tipEps (c' n) := by
      have ht₁ : xiStar ^ 2 / 3 * c' n - C_shift * c' n ^ (1 / 3 : ℝ) ≤
          c' n * ((tests n).x₁ (c' n)) ^ 2 / 3 := by
        rw [(tests n).t₁_eq_x₁_sq hc'_pos, xiBar] at ht1_lt
        linarith
      have hc13 : c' n ^ (1 / 3 : ℝ) = c' n * tipEps (c' n) := by
        unfold tipEps
        calc c' n ^ (1 / 3 : ℝ) = c' n ^ (1 + -(2 / 3 : ℝ)) := by norm_num
          _ = c' n ^ (1 : ℝ) * c' n ^ (-(2 / 3 : ℝ)) := Real.rpow_add hc'_pos _ _
          _ = c' n * c' n ^ (-(2 / 3 : ℝ)) := by rw [Real.rpow_one]
      have hmul : c' n * (xiStar ^ 2 - ((tests n).x₁ (c' n)) ^ 2) ≤
          c' n * (3 * C_shift * tipEps (c' n)) := by
        rw [hc13] at ht₁; linarith
      exact le_of_mul_le_mul_left hmul hc'_pos
    have hdiff_sq : (xiStar - (tests n).x₁ (c' n)) * (xiStar + (tests n).x₁ (c' n)) =
        xiStar ^ 2 - ((tests n).x₁ (c' n)) ^ 2 := by ring
    have hlin : (xiStar - (tests n).x₁ (c' n)) * xiStar ≤ 3 * C_shift * tipEps (c' n) :=
      (mul_le_mul_of_nonneg_left (by linarith) (by linarith)).trans (hdiff_sq ▸ hsq_bd)
    have hdiv : xiStar - (tests n).x₁ (c' n) ≤ (3 * C_shift / xiStar) * tipEps (c' n) := by
      calc xiStar - (tests n).x₁ (c' n)
          = ((xiStar - (tests n).x₁ (c' n)) * xiStar) / xiStar := by field_simp [xiStar_pos.ne']
        _ ≤ (3 * C_shift * tipEps (c' n)) / xiStar := div_le_div_of_nonneg_right hlin xiStar_pos.le
        _ = (3 * C_shift / xiStar) * tipEps (c' n) := by ring
    unfold tipS₁W
    rw [le_div_iff₀ hε_pos]
    have : 0 ≤ tipEps (c' n) := hε_pos.le
    nlinarith

/-! ### Section 3: General-`(w, Q)` Proposition T (`blowup_limit.tex`, Proposition `bl:T`) -/

private lemma intervalIntegral_tendsto_of_tendstoUniformlyOn {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    {a b : ℝ} (hab : a ≤ b)
    (hunif : TendstoUniformlyOn f g atTop (Icc a b))
    (hf_int : ∀ᶠ k in atTop, IntervalIntegrable (f k) volume a b)
    (hg_cont : ContinuousOn g (Icc a b)) :
    Tendsto (fun k => ∫ s in a..b, f k s) atTop (nhds (∫ s in a..b, g s)) := by
  simp_rw [intervalIntegral.integral_of_le hab]
  have hbound_int : IntegrableOn (fun s => ‖g s‖ + 1) (Ioc a b) :=
    ((hg_cont.norm.add continuousOn_const).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hbound : ∀ᶠ k in atTop, ∀ᵐ s ∂volume.restrict (Ioc a b), ‖f k s‖ ≤ ‖g s‖ + 1 := by
    have hu := (Metric.tendstoUniformlyOn_iff.mp hunif) 1 zero_lt_one
    filter_upwards [hu] with k hk
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hd := hk s (Ioc_subset_Icc_self hs)
    rw [Real.dist_eq, abs_sub_comm] at hd
    calc ‖f k s‖ = |f k s| := Real.norm_eq_abs _
      _ ≤ |g s| + |f k s - g s| := by linarith [abs_sub_abs_le_abs_sub (f k s) (g s)]
      _ ≤ ‖g s‖ + 1 := by rw [Real.norm_eq_abs]; linarith
  have hlim : ∀ᵐ s ∂volume.restrict (Ioc a b), Tendsto (fun k => f k s) atTop (nhds (g s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hunif.tendsto_at (Ioc_subset_Icc_self hs)
  exact tendsto_integral_filter_of_dominated_convergence (fun s => ‖g s‖ + 1)
    (hf_int.mono fun _ hk => hk.1.aestronglyMeasurable) hbound hbound_int hlim

/-- **General-`(w, Q)` Proposition T** (`blowup_limit.tex`, Proposition `bl:T`, parts `(i)`–`(vi)`):
given any `UniformPropositionPData prob` and any sequence `c_k → ∞` with weakly feasible tests
`tests k : FixedBlowupTest prob (c_k)` whose normalized tip thresholds `s₁(c_k)` are bounded above,
there exists a subsequence `(ms k)` along which `s₁ → s₁*`, `γ → γLim`, and
`Φ_k = tipRescaleW prob (c_k) (tests k).g` converges locally uniformly on `ℂ` to a real entire
function `Ψ` satisfying `(i)`–`(vi)`. -/
theorem proposition_T_general (prob : FixedWeightProblem) (D : UniformPropositionPData prob)
    {c' : ℕ → ℝ} (hc' : Tendsto c' atTop atTop)
    (tests : ∀ k : ℕ, FixedBlowupTest prob (c' k))
    (hB : ∃ B : ℝ, ∀ k : ℕ, tipS₁W (c' k) (tests k) ≤ B) :
    ∃ (ms : ℕ → ℕ) (s₁Star : ℝ) (Ψ : ℂ → ℂ) (γLim mEsc C_env : ℝ),
      StrictMono ms ∧
      Tendsto (fun k => tipS₁W (c' (ms k)) (tests (ms k))) atTop (nhds s₁Star) ∧
      TendstoLocallyUniformlyOn (fun k => tipRescaleW prob (c' (ms k)) (tests (ms k)).g)
        Ψ atTop univ ∧
      Tendsto (fun k => (tests (ms k)).gVac / (2 * π * (tests (ms k)).M)) atTop (nhds γLim) ∧
      -- (i) entire + growth bounds
      Differentiable ℂ Ψ ∧
      0 ≤ C_env ∧
      (∀ ζ : ℂ, ‖Ψ ζ‖ ≤ C_env * (1 + ‖ζ‖) ^ (1 / 2 : ℝ) * airyEnv (-(betaTip : ℂ) * ζ)) ∧
      (∀ ζ : ℂ, ζ.im ≠ 0 →
        ‖Ψ ζ‖ ≤ C_env * Real.exp (tipH ζ) *
          (1 + min ((1 + ‖ζ‖) ^ (1 / 2 : ℝ)) (1 / |ζ.im|))) ∧
      (∀ ζ : ℂ, |(-ζ).arg| ≤ 2 * π / 3 → 8 ≤ ‖ζ‖ →
        ‖Ψ ζ‖ ≤ C_env * Real.exp (tipH ζ) / ‖ζ‖) ∧
      -- (ii) L¹
      Integrable (fun s : ℝ => Ψ (s : ℂ)) ∧
      (∫ s : ℝ, ‖Ψ (s : ℂ)‖ ≤ 1) ∧
      -- (iii) real on ℝ, nonnegative on [s₁Star, ∞)
      (∀ s : ℝ, (Ψ (s : ℂ)).im = 0) ∧
      (∀ s : ℝ, s₁Star ≤ s → 0 ≤ (Ψ (s : ℂ)).re) ∧
      -- (iv) vacuum + escape mass
      0 ≤ γLim ∧ 0 ≤ mEsc ∧
      (∫ s : ℝ, (Ψ (s : ℂ)).re) = -(γLim + mEsc) ∧
      -- (v) half-mass + non-vanishing
      ((1 / 2 : ℝ) ≤ ∫ s : ℝ, max 0 (-(Ψ (s : ℂ)).re)) ∧
      (∃ z : ℂ, Ψ z ≠ 0) ∧
      -- (vi) `G_{1/2}` rescaling `f(u) = Ψ(-u/β)` and order `≤ 3/2`
      (let f : ℂ → ℂ := fun u => Ψ (-u / (betaTip : ℂ))
       Differentiable ℂ f ∧
       (∃ C_f : ℝ, 0 ≤ C_f ∧ ∀ u : ℂ, ‖f u‖ ≤ C_f * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u) ∧
       Integrable (fun u : ℝ => f (u : ℂ)) ∧
       (∃ u : ℂ, f u ≠ 0) ∧
       (∀ u : ℝ, (f (u : ℂ)).im = 0) ∧
       (∀ u : ℝ, u ≤ -betaTip * s₁Star → 0 ≤ (f (u : ℂ)).re) ∧
       (∫ u : ℝ, (f (u : ℂ)).re) ≤ 0 ∧
       (∀ ε : ℝ, 0 < ε → ∃ C_ord : ℝ, 0 ≤ C_ord ∧
         ∀ ζ : ℂ, ‖Ψ ζ‖ ≤ C_ord * Real.exp ((KTip + ε) * ‖ζ‖ ^ (3 / 2 : ℝ)))) := by
  obtain ⟨B, hB_le⟩ := hB
  obtain ⟨C₀, c_A, hC₀_pos, hcA_shift, hA⟩ := tipS₁W_theorem_A_lower_general prob
  obtain ⟨C_env, hCenv_nn, hEnv⟩ := tipRescaleW_pointwise_envelope prob D
  obtain ⟨η, hη_tend, hTail⟩ := blowup_left_tail_bound_general prob D
  obtain ⟨c₀_H, hc₀H_shift, hholo_fn⟩ := tipRescaleW_holo_exists prob
  let c_base : ℝ := max c_A c₀_H
  have hc_base_shift : max 1 (24 * prob.totalShift) ≤ c_base :=
    le_trans hcA_shift (le_max_left _ _)
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp (hc'.eventually (eventually_ge_atTop c_base))
  let s1_seq : ℕ → ℝ := fun k => tipS₁W (c' (k + K₀)) (tests (k + K₀))
  let γ_seq : ℕ → ℝ := fun k => (tests (k + K₀)).gVac / (2 * π * (tests (k + K₀)).M)
  have hs1_bdd : ∀ k : ℕ, s1_seq k ∈ Icc (-C₀) B := fun k => by
    have hc'k := hK₀ (k + K₀) (Nat.le_add_left K₀ k)
    exact ⟨hA ((le_max_left _ _).trans hc'k) _, hB_le _⟩
  have hγ_bdd : ∀ k : ℕ, γ_seq k ∈ Icc (0 : ℝ) 1 := fun k => by
    have hc'k_base : c_base ≤ c' (k + K₀) := hK₀ (k + K₀) (Nat.le_add_left K₀ k)
    have hc'k_ge1 : 1 ≤ c' (k + K₀) := (le_max_left 1 _).trans (hc_base_shift.trans hc'k_base)
    have hc'k_pos : 0 < c' (k + K₀) := lt_of_lt_of_le zero_lt_one hc'k_ge1
    have hc'k_shift : prob.totalShift ≤ c' (k + K₀) / 12 :=
      shift_div12_of_mul24 ((le_max_right 1 _).trans (hc_base_shift.trans hc'k_base))
    let htest := tests (k + K₀)
    have hvac := tipRescaleW_integral_vac hc'k_pos htest
    have hnorm := tipRescaleW_norm_integral hc'k_pos hc'k_shift htest
    have h_le : -(∫ s in Ioi (tipSMin (c' (k + K₀))),
          (tipRescaleW prob (c' (k + K₀)) htest.g (s : ℂ)).re) ≤
        ∫ s in Ioi (tipSMin (c' (k + K₀))), ‖tipRescaleW prob (c' (k + K₀)) htest.g (s : ℂ)‖ := by
      calc -(∫ s in Ioi (tipSMin (c' (k + K₀))),
              (tipRescaleW prob (c' (k + K₀)) htest.g (s : ℂ)).re)
          ≤ |∫ s in Ioi (tipSMin (c' (k + K₀))),
              (tipRescaleW prob (c' (k + K₀)) htest.g (s : ℂ)).re| := neg_le_abs _
        _ = ‖∫ s in Ioi (tipSMin (c' (k + K₀))),
              (tipRescaleW prob (c' (k + K₀)) htest.g (s : ℂ)).re‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ s in Ioi (tipSMin (c' (k + K₀))),
              ‖(tipRescaleW prob (c' (k + K₀)) htest.g (s : ℂ)).re‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ s in Ioi (tipSMin (c' (k + K₀))),
              ‖tipRescaleW prob (c' (k + K₀)) htest.g (s : ℂ)‖ := by
            refine setIntegral_mono_on
              (tipRescaleW_integrableOn_domain hc'k_pos hc'k_shift htest).re.norm
              (tipRescaleW_integrableOn_domain hc'k_pos hc'k_shift htest).norm measurableSet_Ioi fun s _ => ?_
            exact (Complex.abs_re_le_norm _).trans_eq rfl
    have hvac_nn : 0 ≤ γ_seq k := by
      have hM_pos : 0 < (tests (k + K₀)).M := (tests (k + K₀)).hM_pos
      dsimp [γ_seq, htest]
      exact div_nonneg (tests (k + K₀)).hgVac_nonneg (by positivity [Real.pi_pos, hM_pos])
    refine ⟨hvac_nn, ?_⟩
    dsimp [γ_seq, htest] at hvac hnorm h_le ⊢
    rw [neg_div] at hvac
    linarith [hvac, hnorm]
  obtain ⟨s₁Star, _, φ₁, hφ₁_strict, hs₁_lim⟩ :=
    isCompact_Icc.tendsto_subseq (x := s1_seq) hs1_bdd
  obtain ⟨γLim, _, φ₂, hφ₂_strict, hγ_lim⟩ :=
    isCompact_Icc.tendsto_subseq (x := fun m => γ_seq (φ₁ m)) (fun m => hγ_bdd _)
  let idx₁ : ℕ → ℕ := fun m => φ₁ (φ₂ m) + K₀
  have hidx₁_strict : StrictMono idx₁ :=
    fun a b hab => Nat.add_lt_add_right (hφ₁_strict (hφ₂_strict hab)) K₀
  have hc'_idx₁ : Tendsto (fun m => c' (idx₁ m)) atTop atTop :=
    hc'.comp hidx₁_strict.tendsto_atTop
  let F : ℕ → ℂ → ℂ := fun m => tipRescaleW prob (c' (idx₁ m)) (tests (idx₁ m)).g
  have hF_hol : ∀ R : ℝ, 0 ≤ R → ∀ᶠ m in atTop, DifferentiableOn ℂ (F m) (ball 0 R) := by
    intro R _
    have hεR : Tendsto (fun m => 2 * R * tipEps (c' (idx₁ m))) atTop (nhds 0) := by
      have h0 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc'_idx₁
      simpa [tipEps] using h0.const_mul (2 * R)
    filter_upwards [hc'_idx₁.eventually (eventually_ge_atTop (max 1 c₀_H)),
      hεR.eventually (eventually_lt_nhds one_pos)] with m hm h2R
    exact tipRescaleW_holo_ball (by linarith [le_max_left 1 c₀_H]) h2R
      (hholo_fn ((le_max_right 1 c₀_H).trans hm) (tests (idx₁ m)).hg_test)
  have hF_bdd : ∀ R : ℝ, 0 ≤ R → ∃ M : ℝ, ∀ᶠ m in atTop, ∀ z ∈ ball 0 R, ‖F m z‖ ≤ M := by
    intro R hR
    let M : ℝ := C_env * (1 + R) ^ (1 / 2 : ℝ) * Real.exp (KTip * R ^ (3 / 2 : ℝ))
    refine ⟨M, ?_⟩
    filter_upwards [hc'_idx₁.eventually (hEnv R hR)] with m hm z hz
    have hz_cl : z ∈ closedBall (0 : ℂ) R := ball_subset_closedBall hz
    have h1 := (hm (tests (idx₁ m)) z hz_cl).1
    have hz_le : ‖z‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hz_cl
    have hH_le : tipH z ≤ KTip * R ^ (3 / 2 : ℝ) := by
      unfold tipH
      have hre : -((-z) ^ (3 / 2 : ℂ)).re ≤ ‖z‖ ^ (3 / 2 : ℝ) := by
        simpa [norm_neg] using FormalResearch.Special.re_cpow_three_halves_le (-z)
      have hpow_le : ‖z‖ ^ (3 / 2 : ℝ) ≤ R ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg _) hz_le (by norm_num)
      calc -KTip * ((-z) ^ (3 / 2 : ℂ)).re = KTip * (-((-z) ^ (3 / 2 : ℂ)).re) := by ring
        _ ≤ KTip * ‖z‖ ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_left hre KTip_pos.le
        _ ≤ KTip * R ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_left hpow_le KTip_pos.le
    calc ‖F m z‖ ≤ C_env * (1 + ‖z‖) ^ (1 / 2 : ℝ) * Real.exp (tipH z) := h1
      _ ≤ C_env * (1 + R) ^ (1 / 2 : ℝ) * Real.exp (KTip * R ^ (3 / 2 : ℝ)) := by gcongr
  obtain ⟨φ₃, Ψ, hφ₃_strict, hΨ_diff, hΨ_lim⟩ := montel_exhaustion_entire F hF_hol hF_bdd
  let ms : ℕ → ℕ := fun k => idx₁ (φ₃ k)
  have hms_strict : StrictMono ms := hidx₁_strict.comp hφ₃_strict
  have hs₁_sub : Tendsto (fun k => tipS₁W (c' (ms k)) (tests (ms k))) atTop (nhds s₁Star) :=
    (hs₁_lim.comp hφ₂_strict.tendsto_atTop).comp hφ₃_strict.tendsto_atTop
  have hγ_sub : Tendsto (fun k => (tests (ms k)).gVac / (2 * π * (tests (ms k)).M))
      atTop (nhds γLim) :=
    hγ_lim.comp hφ₃_strict.tendsto_atTop
  have hc'_ms : Tendsto (fun k => c' (ms k)) atTop atTop := hc'.comp hms_strict.tendsto_atTop
  -- Pointwise sharp bounds `(i)` for `Ψ`.
  have hΨ_pt : ∀ ζ : ℂ, tipH ζ ≤ KTip * ‖ζ‖ ^ (3 / 2 : ℝ) := fun ζ => by
    unfold tipH
    have hre : -((-ζ) ^ (3 / 2 : ℂ)).re ≤ ‖ζ‖ ^ (3 / 2 : ℝ) := by
      simpa [norm_neg] using FormalResearch.Special.re_cpow_three_halves_le (-ζ)
    calc -KTip * ((-ζ) ^ (3 / 2 : ℂ)).re = KTip * (-((-ζ) ^ (3 / 2 : ℂ)).re) := by ring
      _ ≤ KTip * ‖ζ‖ ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_left hre KTip_pos.le
  have hΨ_i1 : ∀ ζ : ℂ, ‖Ψ ζ‖ ≤ C_env * (1 + ‖ζ‖) ^ (1 / 2 : ℝ) * airyEnv (-(betaTip : ℂ) * ζ) := by
    intro ζ
    rw [← tipH_eq_airyEnv ζ]
    have hlim : Tendsto (fun k => ‖F (φ₃ k) ζ‖) atTop (nhds ‖Ψ ζ‖) :=
      (continuous_norm.tendsto _).comp (hΨ_lim.tendsto_at (mem_univ ζ))
    have hcl : ζ ∈ closedBall (0 : ℂ) ‖ζ‖ := mem_closedBall_zero_iff.mpr le_rfl
    have hev : ∀ᶠ k in atTop, ‖F (φ₃ k) ζ‖ ≤
        C_env * (1 + ‖ζ‖) ^ (1 / 2 : ℝ) * Real.exp (tipH ζ) := by
      filter_upwards [(hc'_ms.eventually (hEnv ‖ζ‖ (norm_nonneg ζ)))] with k hk
      exact (hk (tests (ms k)) ζ hcl).1
    exact le_of_tendsto hlim hev
  have hΨ_i2 : ∀ ζ : ℂ, ζ.im ≠ 0 →
      ‖Ψ ζ‖ ≤ C_env * Real.exp (tipH ζ) * (1 + min ((1 + ‖ζ‖) ^ (1 / 2 : ℝ)) (1 / |ζ.im|)) := by
    intro ζ him
    have hlim : Tendsto (fun k => ‖F (φ₃ k) ζ‖) atTop (nhds ‖Ψ ζ‖) :=
      (continuous_norm.tendsto _).comp (hΨ_lim.tendsto_at (mem_univ ζ))
    have hcl : ζ ∈ closedBall (0 : ℂ) ‖ζ‖ := mem_closedBall_zero_iff.mpr le_rfl
    have hev : ∀ᶠ k in atTop, ‖F (φ₃ k) ζ‖ ≤
        C_env * Real.exp (tipH ζ) * (1 + min ((1 + ‖ζ‖) ^ (1 / 2 : ℝ)) (1 / |ζ.im|)) := by
      filter_upwards [(hc'_ms.eventually (hEnv ‖ζ‖ (norm_nonneg ζ)))] with k hk
      exact (hk (tests (ms k)) ζ hcl).2.1 him
    exact le_of_tendsto hlim hev
  have hΨ_i3 : ∀ ζ : ℂ, |(-ζ).arg| ≤ 2 * π / 3 → 8 ≤ ‖ζ‖ →
      ‖Ψ ζ‖ ≤ C_env * Real.exp (tipH ζ) / ‖ζ‖ := by
    intro ζ harg h8
    have hlim : Tendsto (fun k => ‖F (φ₃ k) ζ‖) atTop (nhds ‖Ψ ζ‖) :=
      (continuous_norm.tendsto _).comp (hΨ_lim.tendsto_at (mem_univ ζ))
    have hcl : ζ ∈ closedBall (0 : ℂ) ‖ζ‖ := mem_closedBall_zero_iff.mpr le_rfl
    have hev : ∀ᶠ k in atTop, ‖F (φ₃ k) ζ‖ ≤ C_env * Real.exp (tipH ζ) / ‖ζ‖ := by
      filter_upwards [(hc'_ms.eventually (hEnv ‖ζ‖ (norm_nonneg ζ)))] with k hk
      exact (hk (tests (ms k)) ζ hcl).2.2 harg h8
    exact le_of_tendsto hlim hev
  -- `(iii)` real on `ℝ`, nonnegative on `[s₁Star, ∞)`.
  have hΨ_im : ∀ s : ℝ, (Ψ (s : ℂ)).im = 0 := fun s => by
    have hlim : Tendsto (fun k => (F (φ₃ k) (s : ℂ)).im) atTop (nhds (Ψ (s : ℂ)).im) :=
      (Complex.continuous_im.tendsto _).comp (hΨ_lim.tendsto_at (mem_univ (s : ℂ)))
    have hev0 : ∀ᶠ k in atTop, (F (φ₃ k) (s : ℂ)).im = 0 := by
      filter_upwards [hc'_ms.eventually (eventually_gt_atTop (0 : ℝ))] with k hc'k
      exact tipRescaleW_im_eq_zero hc'k (tests (ms k)).hg_test s
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev0.mono fun _ h => h.symm))
  have hΨ_nonneg_open : ∀ s : ℝ, s₁Star < s → 0 ≤ (Ψ (s : ℂ)).re := fun s hs => by
    have hlim : Tendsto (fun k => (F (φ₃ k) (s : ℂ)).re) atTop (nhds (Ψ (s : ℂ)).re) :=
      (Complex.continuous_re.tendsto _).comp (hΨ_lim.tendsto_at (mem_univ (s : ℂ)))
    have hev : ∀ᶠ k in atTop, 0 ≤ (F (φ₃ k) (s : ℂ)).re := by
      filter_upwards [hs₁_sub.eventually (eventually_le_nhds hs),
        hc'_ms.eventually (eventually_ge_atTop (max 1 (24 * prob.totalShift)))] with k hsk hc'k
      have hc'k_pos : 0 < c' (ms k) := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans hc'k)
      have hc'k_sh : prob.totalShift ≤ c' (ms k) / 12 :=
        shift_div12_of_mul24 ((le_max_right 1 _).trans hc'k)
      exact tipRescaleW_nonneg_tail hc'k_pos hc'k_sh (tests (ms k)) s hsk
    exact ge_of_tendsto hlim hev
  have hΨ_nonneg : ∀ s : ℝ, s₁Star ≤ s → 0 ≤ (Ψ (s : ℂ)).re := fun s hs => by
    rcases eq_or_lt_of_le hs with rfl | hlt
    · have hseq : Tendsto (fun n : ℕ => s₁Star + ((n : ℝ) + 1)⁻¹) atTop (nhds s₁Star) := by
        simpa [one_div] using
          (tendsto_const_nhds (x := s₁Star)).add tendsto_one_div_add_atTop_nhds_zero_nat
      have hcont : ContinuousAt (fun t : ℝ => (Ψ (t : ℂ)).re) s₁Star :=
        (Complex.continuous_re.comp (hΨ_diff.continuous.comp Complex.continuous_ofReal)).continuousAt
      exact ge_of_tendsto (hcont.tendsto.comp hseq) (Eventually.of_forall fun n =>
        hΨ_nonneg_open _ (by linarith [show (0 : ℝ) < ((n : ℝ) + 1)⁻¹ by positivity]))
    · exact hΨ_nonneg_open s hlt
  -- `(ii)` `∫_{-R}^R ‖Ψ‖ ≤ 1` -> `Ψ ∈ L¹(ℝ)` and `∫_ℝ ‖Ψ‖ ≤ 1`.
  have hΨ_Ioc_le : ∀ R : ℝ, 0 ≤ R → ∫ s in Ioc (-R) R, ‖Ψ (s : ℂ)‖ ≤ 1 := fun R hR => by
    have hunif : TendstoUniformlyOn (fun k (s : ℝ) => ‖F (φ₃ k) (s : ℂ)‖) (fun (s : ℝ) => ‖Ψ (s : ℂ)‖) atTop
        (Icc (-R) R : Set ℝ) := by
      have hK : IsCompact (Complex.ofReal '' Icc (-R) R) := isCompact_Icc.image Complex.continuous_ofReal
      have hu := ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hΨ_lim)
        _ (subset_univ _) hK
      rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
      intro ε hε
      filter_upwards [hu ε hε] with k hk s hs
      have hd := hk (s : ℂ) (mem_image_of_mem _ hs)
      rw [Real.dist_eq]
      rw [Complex.dist_eq] at hd
      exact (abs_norm_sub_norm_le (Ψ (s : ℂ)) (F (φ₃ k) (s : ℂ))).trans_lt hd
    have hcont_Ψ : ContinuousOn (fun s : ℝ => ‖Ψ (s : ℂ)‖) (Icc (-R) R) :=
      (continuous_norm.comp (hΨ_diff.continuous.comp Complex.continuous_ofReal)).continuousOn
    have hint_ev : ∀ᶠ k in atTop,
        IntervalIntegrable (fun s : ℝ => ‖F (φ₃ k) (s : ℂ)‖) volume (-R) R := by
      filter_upwards [hc'_ms.eventually (eventually_ge_atTop (max 1 c₀_H))] with k hm
      have hc'k : 0 < c' (ms k) := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans hm)
      have hcont : ContinuousOn (fun s : ℝ => ‖F (φ₃ k) (s : ℂ)‖) (Icc (-R) R) := by
        have hb : ContinuousOn (fun s : ℝ => F (φ₃ k) (s : ℂ)) (Icc (-R) R) :=
          (hholo_fn ((le_max_right 1 c₀_H).trans hm) (tests (ms k)).hg_test).continuousOn.comp
            Complex.continuous_ofReal.continuousOn fun s _ => by
              rw [mem_ofPred_eq, Complex.ofReal_im, abs_zero]
              exact one_div_pos.mpr (by positivity [tipEps_pos hc'k])
        exact hb.norm
      exact hcont.intervalIntegrable_of_Icc (by linarith)
    have hlim_int : Tendsto (fun k => ∫ s in (-R)..R, ‖F (φ₃ k) (s : ℂ)‖) atTop
        (nhds (∫ s in (-R)..R, ‖Ψ (s : ℂ)‖)) :=
      intervalIntegral_tendsto_of_tendstoUniformlyOn (by linarith) hunif hint_ev hcont_Ψ
    have hev_le1 : ∀ᶠ k in atTop, ∫ s in (-R)..R, ‖F (φ₃ k) (s : ℂ)‖ ≤ 1 := by
      have hsMin_tend : Tendsto (fun k => tipSMin (c' (ms k))) atTop atBot := by
        unfold tipSMin
        simpa [neg_mul] using tendsto_neg_atBot_iff.mpr
          (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc'_ms).const_mul_atTop
            xiStar_pos)
      filter_upwards [hsMin_tend.eventually (eventually_lt_atBot (-R)),
        hc'_ms.eventually (eventually_ge_atTop (max 1 (24 * prob.totalShift)))] with k hsMin hc'k
      have hc'k_pos : 0 < c' (ms k) := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans hc'k)
      have hc'k_sh : prob.totalShift ≤ c' (ms k) / 12 :=
        shift_div12_of_mul24 ((le_max_right 1 _).trans hc'k)
      rw [intervalIntegral.integral_of_le (by linarith)]
      have hnorm_eq := tipRescaleW_norm_integral hc'k_pos hc'k_sh (tests (ms k))
      have hint_dom : IntegrableOn (fun s : ℝ => ‖F (φ₃ k) (s : ℂ)‖)
          (Ioi (tipSMin (c' (ms k)))) :=
        (tipRescaleW_integrableOn_domain hc'k_pos hc'k_sh (tests (ms k))).norm
      have hsub : Ioc (-R) R ⊆ Ioi (tipSMin (c' (ms k))) := fun s hs => lt_trans hsMin hs.1
      calc ∫ s in Ioc (-R) R, ‖F (φ₃ k) (s : ℂ)‖
          ≤ ∫ s in Ioi (tipSMin (c' (ms k))), ‖F (φ₃ k) (s : ℂ)‖ :=
            setIntegral_mono_set hint_dom (ae_of_all _ fun _ => norm_nonneg _) hsub.eventuallySubset
        _ = 1 := hnorm_eq
    rw [← intervalIntegral.integral_of_le (by linarith)]
    exact le_of_tendsto hlim_int hev_le1
  have hΨ_int : Integrable (fun s : ℝ => Ψ (s : ℂ)) := by
    have hcont : Continuous (fun s : ℝ => Ψ (s : ℂ)) :=
      hΨ_diff.continuous.comp Complex.continuous_ofReal
    have hlint : ∫⁻ s : ℝ, ‖Ψ (s : ℂ)‖ₑ ≤ 1 := by
      let g : ℕ → ℝ → ENNReal := fun n => (Ioc (-(n : ℝ)) n).indicator (fun s => ‖Ψ (s : ℂ)‖ₑ)
      have hmono : Monotone g := fun m n hmn s => by
        dsimp [g]
        by_cases hm : s ∈ Ioc (-(m : ℝ)) m
        · have hn : s ∈ Ioc (-(n : ℝ)) n :=
            ⟨by linarith [hm.1, show (m : ℝ) ≤ n by exact_mod_cast hmn],
             by linarith [hm.2, show (m : ℝ) ≤ n by exact_mod_cast hmn]⟩
          rw [indicator_of_mem hm, indicator_of_mem hn]
        · rw [indicator_of_notMem hm]; exact bot_le
      have hlim : ∀ s : ℝ, Tendsto (fun n : ℕ => g n s) atTop (nhds ‖Ψ (s : ℂ)‖ₑ) := fun s => by
        obtain ⟨n₀, hn₀⟩ := exists_nat_gt |s|
        have hev : ∀ᶠ n in atTop, g n s = ‖Ψ (s : ℂ)‖ₑ := by
          filter_upwards [eventually_ge_atTop n₀] with n hn
          have hmem : s ∈ Ioc (-(n : ℝ)) n := by
            have hle : |s| < n := lt_of_lt_of_le hn₀ (by exact_mod_cast hn)
            rw [abs_lt] at hle
            exact ⟨hle.1, hle.2.le⟩
          exact indicator_of_mem hmem _
        exact tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm)
      have hmeas : ∀ n : ℕ, Measurable (g n) := fun n =>
        hcont.enorm.measurable.indicator measurableSet_Ioc
      have hl := lintegral_tendsto_of_tendsto_of_monotone (μ := volume)
        (fun n => (hmeas n).aemeasurable)
        (ae_of_all volume fun s _ _ hmn => hmono hmn s) (ae_of_all volume hlim)
      have hle1 : ∀ n : ℕ, ∫⁻ s : ℝ, g n s ≤ 1 := fun n => by
        rw [lintegral_indicator measurableSet_Ioc]
        have hIoc_int : IntegrableOn (fun s : ℝ => ‖Ψ (s : ℂ)‖) (Ioc (-(n : ℝ)) n) :=
          (hcont.norm.continuousOn (s := Icc (-(n : ℝ)) n)).integrableOn_Icc.mono_set
            Ioc_subset_Icc_self
        have h_eq : ∫⁻ s in Ioc (-(n : ℝ)) n, ‖Ψ (s : ℂ)‖ₑ =
            ENNReal.ofReal (∫ s in Ioc (-(n : ℝ)) n, ‖Ψ (s : ℂ)‖) := by
          rw [ofReal_integral_eq_lintegral_ofReal hIoc_int (Eventually.of_forall fun _ => norm_nonneg _)]
          congr 1; ext s; exact (ofReal_norm _).symm
        rw [h_eq]
        exact ENNReal.ofReal_le_one.mpr (hΨ_Ioc_le n (Nat.cast_nonneg n))
      exact le_of_tendsto hl (Eventually.of_forall hle1)
    exact ⟨hcont.aestronglyMeasurable, lt_of_le_of_lt hlint ENNReal.one_lt_top⟩
  have hΨ_norm_le : ∫ s : ℝ, ‖Ψ (s : ℂ)‖ ≤ 1 := by
    have htend_int : Tendsto (fun n : ℕ => ∫ s in Ioc (-(n : ℝ)) n, ‖Ψ (s : ℂ)‖) atTop
        (nhds (∫ s : ℝ, ‖Ψ (s : ℂ)‖)) := by
      have heq : ∀ n : ℕ, ∫ s in Ioc (-(n : ℝ)) n, ‖Ψ (s : ℂ)‖ =
          ∫ s : ℝ, (Ioc (-(n : ℝ)) n).indicator (fun t => ‖Ψ (t : ℂ)‖) s :=
        fun n => (integral_indicator measurableSet_Ioc).symm
      simp_rw [heq]
      refine tendsto_integral_of_dominated_convergence (fun s => ‖Ψ (s : ℂ)‖)
        (fun n => (hΨ_int.norm.indicator measurableSet_Ioc).aestronglyMeasurable)
        hΨ_int.norm
        (fun n => Eventually.of_forall fun s => by
          rw [Real.norm_of_nonneg (indicator_nonneg (fun _ _ => norm_nonneg _) _)]
          simp only [Set.indicator]; split_ifs <;> [exact le_rfl; exact norm_nonneg _])
        (Eventually.of_forall fun s => by
          obtain ⟨n₀, hn₀⟩ := exists_nat_gt |s|
          refine tendsto_const_nhds.congr' (eventually_ge_atTop n₀ |>.mono fun n hn => ?_)
          have hle : |s| < n := lt_of_lt_of_le hn₀ (by exact_mod_cast hn)
          rw [abs_lt] at hle
          have hmem : s ∈ Ioc (-(n : ℝ)) n := ⟨hle.1, hle.2.le⟩
          simp [Set.indicator, hmem])
    exact le_of_tendsto htend_int (Eventually.of_forall fun n => hΨ_Ioc_le n (Nat.cast_nonneg n))
  -- `(iv)` `γLim ≥ 0`, `mEsc ≥ 0`, `∫ (Ψ s).re = -(γLim + mEsc)`.
  have hγLim_nn : 0 ≤ γLim := by
    refine ge_of_tendsto hγ_sub (Eventually.of_forall fun k => ?_)
    have hM_pos : 0 < (tests (ms k)).M := (tests (ms k)).hM_pos
    exact div_nonneg (tests (ms k)).hgVac_nonneg (by positivity [Real.pi_pos, hM_pos])
  have hΨ_re_le_neg_γ : ∫ s : ℝ, (Ψ (s : ℂ)).re ≤ -γLim := by
    have hR_bound : ∀ R : ℝ, max 1 (|s₁Star| + 1) ≤ R →
        ∫ s in Ioc (-R) R, (Ψ (s : ℂ)).re ≤ -γLim + η R := by
      intro R hR
      have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
      have hRs1 : s₁Star + 1 ≤ R := by linarith [(le_max_right 1 (|s₁Star| + 1)).trans hR, le_abs_self s₁Star]
      have hunif : TendstoUniformlyOn (fun k (s : ℝ) => (F (φ₃ k) (s : ℂ)).re) (fun (s : ℝ) => (Ψ (s : ℂ)).re)
          atTop (Icc (-R) R : Set ℝ) := by
        have hK : IsCompact (Complex.ofReal '' Icc (-R) R) := isCompact_Icc.image Complex.continuous_ofReal
        have hu := ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hΨ_lim)
          _ (subset_univ _) hK
        rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
        intro ε hε
        filter_upwards [hu ε hε] with k hk s hs
        have hd := hk (s : ℂ) (mem_image_of_mem _ hs)
        rw [Real.dist_eq]
        rw [Complex.dist_eq] at hd
        calc |(Ψ (s : ℂ)).re - (F (φ₃ k) (s : ℂ)).re|
            = |(Ψ (s : ℂ) - F (φ₃ k) (s : ℂ)).re| := by simp [Complex.sub_re]
          _ ≤ ‖Ψ (s : ℂ) - F (φ₃ k) (s : ℂ)‖ := Complex.abs_re_le_norm _
          _ < ε := hd
      have hcont_Ψ : ContinuousOn (fun s : ℝ => (Ψ (s : ℂ)).re) (Icc (-R) R) :=
        (Complex.continuous_re.comp (hΨ_diff.continuous.comp Complex.continuous_ofReal)).continuousOn
      have hint_ev : ∀ᶠ k in atTop,
          IntervalIntegrable (fun s : ℝ => (F (φ₃ k) (s : ℂ)).re) volume (-R) R := by
        filter_upwards [hc'_ms.eventually (eventually_ge_atTop (max 1 c₀_H))] with k hm
        have hc'k : 0 < c' (ms k) := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans hm)
        have hcont : ContinuousOn (fun s : ℝ => (F (φ₃ k) (s : ℂ)).re) (Icc (-R) R) :=
          Complex.continuous_re.comp_continuousOn
            ((hholo_fn ((le_max_right 1 c₀_H).trans hm) (tests (ms k)).hg_test).continuousOn.comp
              Complex.continuous_ofReal.continuousOn fun s _ => by
                rw [mem_ofPred_eq, Complex.ofReal_im, abs_zero]
                exact one_div_pos.mpr (by positivity [tipEps_pos hc'k]))
        exact hcont.intervalIntegrable_of_Icc (by linarith)
      have hlim_int : Tendsto (fun k => ∫ s in (-R)..R, (F (φ₃ k) (s : ℂ)).re) atTop
          (nhds (∫ s in (-R)..R, (Ψ (s : ℂ)).re)) :=
        intervalIntegral_tendsto_of_tendstoUniformlyOn (by linarith) hunif hint_ev hcont_Ψ
      have hsMin_tend : Tendsto (fun k => tipSMin (c' (ms k))) atTop atBot := by
        unfold tipSMin
        simpa [neg_mul] using tendsto_neg_atBot_iff.mpr
          (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc'_ms).const_mul_atTop
            xiStar_pos)
      have hev_le : ∀ᶠ k in atTop,
          ∫ s in (-R)..R, (F (φ₃ k) (s : ℂ)).re ≤
            -((tests (ms k)).gVac / (2 * π * (tests (ms k)).M)) + η R := by
        filter_upwards [hsMin_tend.eventually (eventually_lt_atBot (-R)),
          hc'_ms.eventually (eventually_ge_atTop (max 1 (24 * prob.totalShift))),
          hc'_ms.eventually (hTail R hR1),
          hs₁_sub.eventually (eventually_le_nhds (by linarith : s₁Star < R))] with
          k hsMin hc'k htail_k hs₁_k
        have hc'k_pos : 0 < c' (ms k) := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans hc'k)
        have hc'k_sh : prob.totalShift ≤ c' (ms k) / 12 :=
          shift_div12_of_mul24 ((le_max_right 1 _).trans hc'k)
        have hdom : IntegrableOn (fun s : ℝ => (F (φ₃ k) (s : ℂ)).re)
            (Ioi (tipSMin (c' (ms k)))) :=
          (tipRescaleW_integrableOn_domain hc'k_pos hc'k_sh (tests (ms k))).re
        have hsplit1 : (∫ s in Ioi (tipSMin (c' (ms k))), (F (φ₃ k) (s : ℂ)).re) =
            (∫ s in Ioc (tipSMin (c' (ms k))) R, (F (φ₃ k) (s : ℂ)).re) +
              ∫ s in Ioi R, (F (φ₃ k) (s : ℂ)).re := by
          have hltR : tipSMin (c' (ms k)) ≤ R := by linarith
          dsimp [F]
          rw [← Ioc_union_Ioi_eq_Ioi hltR]
          exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
            (hdom.mono_set Ioc_subset_Ioi_self) (hdom.mono_set (Ioi_subset_Ioi hltR))
        have hsplit2 : (∫ s in Ioc (tipSMin (c' (ms k))) R, (F (φ₃ k) (s : ℂ)).re) =
            (∫ s in Ioc (tipSMin (c' (ms k))) (-R), (F (φ₃ k) (s : ℂ)).re) +
              ∫ s in Ioc (-R) R, (F (φ₃ k) (s : ℂ)).re := by
          dsimp [F]
          rw [← Ioc_union_Ioc_eq_Ioc hsMin.le (by linarith)]
          exact setIntegral_union (Ioc_disjoint_Ioc_of_le (le_rfl : (-R : ℝ) ≤ -R)) measurableSet_Ioc
            (hdom.mono_set Ioc_subset_Ioi_self)
            (hdom.mono_set fun s hs => lt_trans hsMin hs.1)
        have hright_nn : 0 ≤ ∫ s in Ioi R, (F (φ₃ k) (s : ℂ)).re := by
          refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
          exact tipRescaleW_nonneg_tail hc'k_pos hc'k_sh (tests (ms k)) s (hs₁_k.trans (mem_Ioi.mp hs).le)
        have hleft_bd : -η R ≤ ∫ s in Ioc (tipSMin (c' (ms k))) (-R), (F (φ₃ k) (s : ℂ)).re := by
          have h1 : |∫ s in Ioc (tipSMin (c' (ms k))) (-R), (F (φ₃ k) (s : ℂ)).re| ≤ η R := by
            calc |∫ s in Ioc (tipSMin (c' (ms k))) (-R), (F (φ₃ k) (s : ℂ)).re|
                = ‖∫ s in Ioc (tipSMin (c' (ms k))) (-R), (F (φ₃ k) (s : ℂ)).re‖ :=
                  (Real.norm_eq_abs _).symm
              _ ≤ ∫ s in Ioc (tipSMin (c' (ms k))) (-R), ‖(F (φ₃ k) (s : ℂ)).re‖ :=
                  norm_integral_le_integral_norm _
              _ ≤ ∫ s in Ioc (tipSMin (c' (ms k))) (-R), ‖F (φ₃ k) (s : ℂ)‖ := by
                  refine setIntegral_mono_on
                    (IntegrableOn.mono_set (hdom.mono_set Ioc_subset_Ioi_self).norm le_rfl)
                    (IntegrableOn.mono_set
                      (tipRescaleW_integrableOn_domain hc'k_pos hc'k_sh (tests (ms k))).norm Ioc_subset_Ioi_self)
                    measurableSet_Ioc fun s _ => (Complex.abs_re_le_norm _).trans_eq rfl
              _ ≤ η R := htail_k hc'k_sh (tests (ms k))
          exact (abs_le.mp h1).1
        have hvac_k : ∫ s in Ioi (tipSMin (c' (ms k))), (F (φ₃ k) (s : ℂ)).re =
            -((tests (ms k)).gVac / (2 * π * (tests (ms k)).M)) := by
          dsimp [F, ms]
          rw [tipRescaleW_integral_vac hc'k_pos (tests (ms k)), neg_div]
        rw [intervalIntegral.integral_of_le (by linarith)]
        linarith [hvac_k]
      rw [← intervalIntegral.integral_of_le (by linarith)]
      exact le_of_tendsto_of_tendsto hlim_int (hγ_sub.neg.add_const (η R)) hev_le
    have htend_re : Tendsto (fun R : ℝ => ∫ s in Ioc (-R) R, (Ψ (s : ℂ)).re) atTop
        (nhds (∫ s : ℝ, (Ψ (s : ℂ)).re)) := by
      have heq : ∀ R : ℝ, ∫ s in Ioc (-R) R, (Ψ (s : ℂ)).re =
          ∫ s : ℝ, (Ioc (-R) R).indicator (fun t => (Ψ (t : ℂ)).re) s :=
        fun R => (integral_indicator measurableSet_Ioc).symm
      simp_rw [heq]
      refine tendsto_integral_filter_of_dominated_convergence (fun s => ‖(Ψ (s : ℂ)).re‖)
        (Eventually.of_forall fun R =>
          (hΨ_int.re.indicator measurableSet_Ioc).aestronglyMeasurable)
        (Eventually.of_forall fun R => Eventually.of_forall fun s => by
          by_cases hs : s ∈ Ioc (-R) R
          · rw [indicator_of_mem hs]
          · rw [indicator_of_notMem hs, norm_zero]; exact norm_nonneg _)
        hΨ_int.re.norm
        (Eventually.of_forall fun s => by
          refine tendsto_const_nhds.congr' (eventually_ge_atTop (|s| + 1) |>.mono fun R hR => ?_)
          have hle : |s| < R := by linarith
          rw [abs_lt] at hle
          have hmem : s ∈ Ioc (-R) R := ⟨hle.1, hle.2.le⟩
          simp [Set.indicator, hmem])
    have htend_rhs : Tendsto (fun R : ℝ => -γLim + η R) atTop (nhds (-γLim)) := by
      simpa using (tendsto_const_nhds (x := -γLim)).add hη_tend
    exact le_of_tendsto_of_tendsto htend_re htend_rhs
      (eventually_ge_atTop (max 1 (|s₁Star| + 1)) |>.mono fun R hR => hR_bound R hR)
  let mEsc : ℝ := -γLim - ∫ s : ℝ, (Ψ (s : ℂ)).re
  have hmEsc_nn : 0 ≤ mEsc := by dsimp [mEsc]; linarith
  have hre_eq : ∫ s : ℝ, (Ψ (s : ℂ)).re = -(γLim + mEsc) := by dsimp [mEsc]; ring
  -- `(v)` `(1 / 2 : ℝ) ≤ ∫ max 0 (-(Ψ s).re)` and `Ψ ≢ 0`.
  have hneg_int : Integrable (fun s : ℝ => max 0 (-(Ψ (s : ℂ)).re)) := by
    have hcont : Continuous (fun s : ℝ => max 0 (-(Ψ (s : ℂ)).re)) :=
      continuous_const.max (Complex.continuous_re.comp
        (hΨ_diff.continuous.comp Complex.continuous_ofReal)).neg
    refine hΨ_int.norm.mono hcont.aestronglyMeasurable (Eventually.of_forall fun s => ?_)
    have hnn : 0 ≤ max 0 (-(Ψ (s : ℂ)).re) := le_max_left _ _
    rw [Real.norm_of_nonneg hnn, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact max_le (norm_nonneg _) ((neg_le_abs _).trans (Complex.abs_re_le_norm _))
  have hneg_half : (1 / 2 : ℝ) ≤ ∫ s : ℝ, max 0 (-(Ψ (s : ℂ)).re) := by
    obtain ⟨B_s1, hB_s1⟩ := eventually_atTop.mp
      (hs₁_sub.eventually (eventually_le_nhds (by linarith : s₁Star < s₁Star + 1)))
    have hR_bd : ∀ R : ℝ, max 1 (|s₁Star + 1| + 1) ≤ R →
        (1 / 2 : ℝ) - η R ≤ ∫ s : ℝ, max 0 (-(Ψ (s : ℂ)).re) := by
      intro R hR
      have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
      have hRs1 : s₁Star + 1 ≤ R := by linarith [(le_max_right 1 (|s₁Star + 1| + 1)).trans hR, le_abs_self (s₁Star + 1)]
      have hunif : TendstoUniformlyOn (fun k (s : ℝ) => max 0 (-(F (φ₃ k) (s : ℂ)).re))
          (fun (s : ℝ) => max 0 (-(Ψ (s : ℂ)).re)) atTop (Icc (-R) R : Set ℝ) := by
        have hK : IsCompact (Complex.ofReal '' Icc (-R) R) := isCompact_Icc.image Complex.continuous_ofReal
        have hu := ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hΨ_lim)
          _ (subset_univ _) hK
        rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
        intro ε hε
        filter_upwards [hu ε hε] with k hk s hs
        have hd := hk (s : ℂ) (mem_image_of_mem _ hs)
        rw [Real.dist_eq]
        rw [Complex.dist_eq] at hd
        have h1 : |max 0 (-(Ψ (s : ℂ)).re) - max 0 (-(F (φ₃ k) (s : ℂ)).re)| ≤
            |(Ψ (s : ℂ) - F (φ₃ k) (s : ℂ)).re| := by
          have hdist := (LipschitzWith.id.const_max (0 : ℝ)).dist_le_mul
            (-(Ψ (s : ℂ)).re) (-(F (φ₃ k) (s : ℂ)).re)
          rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, id, id,
            show -(Ψ (s : ℂ)).re - -(F (φ₃ k) (s : ℂ)).re =
              -(Ψ (s : ℂ) - F (φ₃ k) (s : ℂ)).re by simp [Complex.sub_re]; ring,
            abs_neg] at hdist
          exact hdist
        exact lt_of_le_of_lt (h1.trans (Complex.abs_re_le_norm _)) hd
      have hcont_Ψ : ContinuousOn (fun s : ℝ => max 0 (-(Ψ (s : ℂ)).re)) (Icc (-R) R) :=
        (continuous_const.max (Complex.continuous_re.comp
          (hΨ_diff.continuous.comp Complex.continuous_ofReal)).neg).continuousOn
      have hint_ev : ∀ᶠ k in atTop,
          IntervalIntegrable (fun s : ℝ => max 0 (-(F (φ₃ k) (s : ℂ)).re)) volume (-R) R := by
        filter_upwards [hc'_ms.eventually (eventually_ge_atTop (max 1 c₀_H))] with k hm
        have hc'k : 0 < c' (ms k) := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans hm)
        have hcont : ContinuousOn (fun s : ℝ => max 0 (-(F (φ₃ k) (s : ℂ)).re)) (Icc (-R) R) :=
          (continuous_const.max (continuous_id : Continuous fun x : ℝ => x)).comp_continuousOn
            ((Complex.continuous_re.comp_continuousOn
              ((hholo_fn ((le_max_right 1 c₀_H).trans hm) (tests (ms k)).hg_test).continuousOn.comp
                Complex.continuous_ofReal.continuousOn fun s _ => by
                  rw [mem_ofPred_eq, Complex.ofReal_im, abs_zero]
                  exact one_div_pos.mpr (by positivity [tipEps_pos hc'k]))).neg)
        exact hcont.intervalIntegrable_of_Icc (by linarith)
      have hlim_int : Tendsto (fun k => ∫ s in (-R)..R, max 0 (-(F (φ₃ k) (s : ℂ)).re)) atTop
          (nhds (∫ s in (-R)..R, max 0 (-(Ψ (s : ℂ)).re))) :=
        intervalIntegral_tendsto_of_tendstoUniformlyOn (by linarith) hunif hint_ev hcont_Ψ
      have hsMin_tend : Tendsto (fun k => tipSMin (c' (ms k))) atTop atBot := by
        unfold tipSMin
        simpa [neg_mul] using tendsto_neg_atBot_iff.mpr
          (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc'_ms).const_mul_atTop
            xiStar_pos)
      have hev_ge : ∀ᶠ k in atTop,
          (1 / 2 : ℝ) - η R ≤ ∫ s in (-R)..R, max 0 (-(F (φ₃ k) (s : ℂ)).re) := by
        filter_upwards [eventually_ge_atTop B_s1,
          hsMin_tend.eventually (eventually_lt_atBot (-R)),
          hc'_ms.eventually (eventually_ge_atTop (max 1 (24 * prob.totalShift))),
          hc'_ms.eventually (hTail R hR1)] with k hkB hsMin hc'k htail_k
        have hc'k_pos : 0 < c' (ms k) := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans hc'k)
        have hc'k_sh : prob.totalShift ≤ c' (ms k) / 12 :=
          shift_div12_of_mul24 ((le_max_right 1 _).trans hc'k)
        have hs1_le_R : tipS₁W (c' (ms k)) (tests (ms k)) ≤ R := (hB_s1 k hkB).trans hRs1
        have hhalf := tipRescaleW_half_neg_mass hc'k_pos hc'k_sh (tests (ms k))
        have hdom_norm : IntegrableOn (fun s : ℝ => ‖F (φ₃ k) (s : ℂ)‖)
            (Ioi (tipSMin (c' (ms k)))) :=
          (tipRescaleW_integrableOn_domain hc'k_pos hc'k_sh (tests (ms k))).norm
        have hfneg_dom : IntegrableOn (fun s : ℝ => max 0 (-(F (φ₃ k) (s : ℂ)).re))
            (Ioi (tipSMin (c' (ms k)))) := by
          refine Integrable.mono hdom_norm
            ((continuous_const.max (continuous_id : Continuous fun x : ℝ => x)).comp_aestronglyMeasurable
              (tipRescaleW_integrableOn_domain hc'k_pos hc'k_sh (tests (ms k))).re.neg.aestronglyMeasurable)
            (Eventually.of_forall fun s => ?_)
          rw [Real.norm_of_nonneg (le_max_left _ _), Real.norm_of_nonneg (norm_nonneg _)]
          exact max_le (norm_nonneg _) ((neg_le_abs _).trans (Complex.abs_re_le_norm _))
        have hsub_tot : Ioc (tipSMin (c' (ms k))) (tipS₁W (c' (ms k)) (tests (ms k))) ⊆
            Ioc (tipSMin (c' (ms k))) R := Ioc_subset_Ioc_right hs1_le_R
        have h1 : (1 / 2 : ℝ) ≤ ∫ s in Ioc (tipSMin (c' (ms k))) R,
            max 0 (-(F (φ₃ k) (s : ℂ)).re) :=
          hhalf.trans (setIntegral_mono_set (hfneg_dom.mono_set Ioc_subset_Ioi_self)
            (ae_of_all _ fun _ => le_max_left _ _) hsub_tot.eventuallySubset)
        have hsplit : (∫ s in Ioc (tipSMin (c' (ms k))) R, max 0 (-(F (φ₃ k) (s : ℂ)).re)) =
            (∫ s in Ioc (tipSMin (c' (ms k))) (-R), max 0 (-(F (φ₃ k) (s : ℂ)).re)) +
              ∫ s in Ioc (-R) R, max 0 (-(F (φ₃ k) (s : ℂ)).re) := by
          rw [← Ioc_union_Ioc_eq_Ioc hsMin.le (by linarith)]
          exact setIntegral_union (Ioc_disjoint_Ioc_of_le (le_rfl : (-R : ℝ) ≤ -R)) measurableSet_Ioc
            (hfneg_dom.mono_set Ioc_subset_Ioi_self)
            (hfneg_dom.mono_set fun s hs => lt_trans hsMin hs.1)
        have htail_neg : ∫ s in Ioc (tipSMin (c' (ms k))) (-R), max 0 (-(F (φ₃ k) (s : ℂ)).re) ≤
            η R := by
          calc ∫ s in Ioc (tipSMin (c' (ms k))) (-R), max 0 (-(F (φ₃ k) (s : ℂ)).re)
              ≤ ∫ s in Ioc (tipSMin (c' (ms k))) (-R), ‖F (φ₃ k) (s : ℂ)‖ := by
                refine setIntegral_mono_on
                  (hfneg_dom.mono_set Ioc_subset_Ioi_self)
                  (IntegrableOn.mono_set hdom_norm Ioc_subset_Ioi_self)
                  measurableSet_Ioc fun s _ =>
                  max_le (norm_nonneg _) ((neg_le_abs _).trans (Complex.abs_re_le_norm _))
            _ ≤ η R := htail_k hc'k_sh (tests (ms k))
        rw [intervalIntegral.integral_of_le (by linarith)]
        linarith
      have hlim_le : ∫ s in (-R)..R, max 0 (-(Ψ (s : ℂ)).re) ≤
          ∫ s : ℝ, max 0 (-(Ψ (s : ℂ)).re) := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact setIntegral_le_integral hneg_int (ae_of_all _ fun _ => le_max_left _ _)
      linarith [ge_of_tendsto hlim_int hev_ge]
    have htend_lhs : Tendsto (fun R : ℝ => (1 / 2 : ℝ) - η R) atTop (nhds (1 / 2)) := by
      simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub hη_tend
    exact le_of_tendsto htend_lhs
      (eventually_ge_atTop (max 1 (|s₁Star + 1| + 1)) |>.mono fun R hR => hR_bd R hR)
  have hΨ_ne_zero : ∃ z : ℂ, Ψ z ≠ 0 := by
    by_contra h0
    push Not at h0
    have hz : ∫ s : ℝ, max 0 (-(Ψ (s : ℂ)).re) = 0 := by simp [h0]
    linarith
  -- `(vi)` `f(u) = Ψ (-u / β)` properties + order `≤ 3/2`.
  let f : ℂ → ℂ := fun u => Ψ (-u / (betaTip : ℂ))
  have hf_diff : Differentiable ℂ f :=
    hΨ_diff.comp ((differentiable_id.neg).div_const _)
  have hCf_pull : ∃ C_f : ℝ, 0 ≤ C_f ∧ ∀ u : ℂ, ‖f u‖ ≤ C_f * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u := by
    let K_f : ℝ := max 1 betaTip⁻¹
    have hKf_pos : 0 < K_f := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    refine ⟨C_env * K_f ^ (1 / 2 : ℝ), by positivity, fun u => ?_⟩
    have hbu := hΨ_i1 (-u / (betaTip : ℂ))
    have hb0 : (betaTip : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr betaTip_pos.ne'
    rw [show -(betaTip : ℂ) * (-u / (betaTip : ℂ)) = u by field_simp] at hbu
    have hnorm_s : ‖-u / (betaTip : ℂ)‖ = ‖u‖ * betaTip⁻¹ := by
      rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos betaTip_pos,
        div_eq_mul_inv]
    have hlin : 1 + ‖-u / (betaTip : ℂ)‖ ≤ K_f * (1 + ‖u‖) := by
      rw [hnorm_s]; have : betaTip⁻¹ ≤ K_f := le_max_right _ _
      nlinarith [norm_nonneg u, le_max_left 1 betaTip⁻¹]
    have hp : (1 + ‖-u / (betaTip : ℂ)‖) ^ (1 / 2 : ℝ) ≤ K_f ^ (1 / 2 : ℝ) * (1 + ‖u‖) ^ (1 / 2 : ℝ) :=
      (Real.rpow_le_rpow (by linarith [norm_nonneg (-u / (betaTip : ℂ))]) hlin (by norm_num)).trans_eq
        (Real.mul_rpow hKf_pos.le (by linarith [norm_nonneg u]))
    calc ‖f u‖ ≤ C_env * (1 + ‖-u / (betaTip : ℂ)‖) ^ (1 / 2 : ℝ) * airyEnv u := hbu
      _ ≤ C_env * (K_f ^ (1 / 2 : ℝ) * (1 + ‖u‖) ^ (1 / 2 : ℝ)) * airyEnv u := by
          gcongr; exact (airyEnv_pos u).le
      _ = (C_env * K_f ^ (1 / 2 : ℝ)) * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u := by ring
  obtain ⟨C_f, hCf_nn, hf_bd⟩ := hCf_pull
  have hf_int : Integrable (fun u : ℝ => f (u : ℂ)) := by
    have hfc : ∀ u : ℝ, f (u : ℂ) = Ψ (((-betaTip⁻¹ * u : ℝ) : ℂ)) := fun u => by
      dsimp [f]; push_cast; ring_nf
    simp_rw [hfc]
    exact hΨ_int.comp_mul_left' (neg_ne_zero.mpr (inv_ne_zero betaTip_pos.ne'))
  have hf_ne_zero : ∃ u : ℂ, f u ≠ 0 := by
    obtain ⟨z, hz⟩ := hΨ_ne_zero
    refine ⟨-(betaTip : ℂ) * z, ?_⟩
    dsimp [f]
    rwa [show -(-(betaTip : ℂ) * z) / (betaTip : ℂ) = z by
      have hβ : (betaTip : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr betaTip_pos.ne'
      field_simp [hβ]]
  have hf_im : ∀ u : ℝ, (f (u : ℂ)).im = 0 := fun u => by
    dsimp [f]
    rw [show -((u : ℂ)) / (betaTip : ℂ) = (((-u / betaTip : ℝ) : ℂ)) by push_cast; ring]
    exact hΨ_im _
  have hf_nonneg : ∀ u : ℝ, u ≤ -betaTip * s₁Star → 0 ≤ (f (u : ℂ)).re := fun u hu => by
    dsimp [f]
    rw [show -((u : ℂ)) / (betaTip : ℂ) = (((-u / betaTip : ℝ) : ℂ)) by push_cast; ring]
    refine hΨ_nonneg _ ?_
    rw [le_div_iff₀ betaTip_pos]
    linarith
  have hf_int_re : ∫ u : ℝ, (f (u : ℂ)).re ≤ 0 := by
    have hsc : ∀ u : ℝ, (f (u : ℂ)).re = (fun s : ℝ => (Ψ (s : ℂ)).re) ((-(betaTip⁻¹)) * u) := fun u => by
      dsimp [f]; congr 2; push_cast; ring
    have hcov := Measure.integral_comp_mul_left (fun s : ℝ => (Ψ (s : ℂ)).re) (-(betaTip⁻¹))
    have h_eq : (fun u : ℝ => (f (u : ℂ)).re) =
        (fun u : ℝ => (fun s : ℝ => (Ψ (s : ℂ)).re) ((-(betaTip⁻¹)) * u)) :=
      funext hsc
    rw [h_eq, hcov, smul_eq_mul]
    have hpref : 0 ≤ |(-(betaTip⁻¹))⁻¹| := abs_nonneg _
    calc |(-(betaTip⁻¹))⁻¹| * ∫ x : ℝ, (Ψ (x : ℂ)).re
        = |(-(betaTip⁻¹))⁻¹| * -(γLim + mEsc) := by rw [hre_eq]
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpref (by linarith)
  have hΨ_ord : ∀ ε : ℝ, 0 < ε → ∃ C_ord : ℝ, 0 ≤ C_ord ∧
      ∀ ζ : ℂ, ‖Ψ ζ‖ ≤ C_ord * Real.exp ((KTip + ε) * ‖ζ‖ ^ (3 / 2 : ℝ)) := by
    intro ε hε
    let R₀ : ℝ := max 1 (ε⁻¹ ^ 2)
    have hR₀_nn : 0 ≤ R₀ := by dsimp [R₀]; positivity
    let C_ord : ℝ := C_env * (1 + R₀)
    refine ⟨C_ord, mul_nonneg hCenv_nn (by linarith), fun ζ => ?_⟩
    have h1 : ‖Ψ ζ‖ ≤ C_env * (1 + ‖ζ‖) ^ (1 / 2 : ℝ) * Real.exp (KTip * ‖ζ‖ ^ (3 / 2 : ℝ)) := by
      have hH := Real.exp_le_exp.mpr (hΨ_pt ζ)
      have hi1 := hΨ_i1 ζ
      rw [← tipH_eq_airyEnv ζ] at hi1
      exact hi1.trans (mul_le_mul_of_nonneg_left hH (by positivity))
    have hpoly : (1 + ‖ζ‖) ^ (1 / 2 : ℝ) ≤ (1 + R₀) * Real.exp (ε * ‖ζ‖ ^ (3 / 2 : ℝ)) := by
      rcases le_or_gt ‖ζ‖ R₀ with hle | hgt
      · have hsqrt : (1 + ‖ζ‖) ^ (1 / 2 : ℝ) ≤ 1 + ‖ζ‖ := by
          calc (1 + ‖ζ‖) ^ (1 / 2 : ℝ) ≤ (1 + ‖ζ‖) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ζ]) (by norm_num)
            _ = 1 + ‖ζ‖ := Real.rpow_one _
        have hexp_ge1 : 1 ≤ Real.exp (ε * ‖ζ‖ ^ (3 / 2 : ℝ)) := Real.one_le_exp (by positivity)
        calc (1 + ‖ζ‖) ^ (1 / 2 : ℝ) ≤ 1 + R₀ := by linarith
          _ = (1 + R₀) * 1 := (mul_one _).symm
          _ ≤ (1 + R₀) * Real.exp (ε * ‖ζ‖ ^ (3 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hexp_ge1 (by linarith)
      · have hr_ge1 : 1 ≤ ‖ζ‖ := (le_max_left 1 (ε⁻¹ ^ 2)).trans hgt.le
        have hr_le : ‖ζ‖ ≤ ε * ‖ζ‖ ^ (3 / 2 : ℝ) := by
          have hpow : ‖ζ‖ ^ (1 / 2 : ℝ) * ‖ζ‖ = ‖ζ‖ ^ (3 / 2 : ℝ) := by
            conv_lhs => arg 2; rw [← Real.rpow_one ‖ζ‖]
            rw [← Real.rpow_add (by linarith)]; norm_num
          have hεr : 1 ≤ ε * ‖ζ‖ ^ (1 / 2 : ℝ) := by
            have hsq : (ε⁻¹) ^ 2 ≤ ‖ζ‖ := (le_max_right 1 (ε⁻¹ ^ 2)).trans hgt.le
            have hhalf : ε⁻¹ ≤ ‖ζ‖ ^ (1 / 2 : ℝ) := by
              rw [← Real.sqrt_sq (inv_nonneg.mpr hε.le), Real.sqrt_eq_rpow]
              exact Real.rpow_le_rpow (by positivity) hsq (by norm_num)
            calc 1 = ε * ε⁻¹ := (mul_inv_cancel₀ hε.ne').symm
              _ ≤ ε * ‖ζ‖ ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hhalf hε.le
          calc ‖ζ‖ = 1 * ‖ζ‖ := (one_mul _).symm
            _ ≤ (ε * ‖ζ‖ ^ (1 / 2 : ℝ)) * ‖ζ‖ := mul_le_mul_of_nonneg_right hεr (norm_nonneg ζ)
            _ = ε * (‖ζ‖ ^ (1 / 2 : ℝ) * ‖ζ‖) := by ring
            _ = ε * ‖ζ‖ ^ (3 / 2 : ℝ) := by rw [hpow]
        have hsqrt : (1 + ‖ζ‖) ^ (1 / 2 : ℝ) ≤ 1 + ‖ζ‖ := by
          calc (1 + ‖ζ‖) ^ (1 / 2 : ℝ) ≤ (1 + ‖ζ‖) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ζ]) (by norm_num)
            _ = 1 + ‖ζ‖ := Real.rpow_one _
        have hexp_ge : 1 + ε * ‖ζ‖ ^ (3 / 2 : ℝ) ≤ Real.exp (ε * ‖ζ‖ ^ (3 / 2 : ℝ)) := by
          linarith [Real.add_one_le_exp (ε * ‖ζ‖ ^ (3 / 2 : ℝ))]
        calc (1 + ‖ζ‖) ^ (1 / 2 : ℝ) ≤ 1 + ‖ζ‖ := hsqrt
          _ ≤ 1 + ε * ‖ζ‖ ^ (3 / 2 : ℝ) := by linarith
          _ ≤ Real.exp (ε * ‖ζ‖ ^ (3 / 2 : ℝ)) := hexp_ge
          _ = 1 * Real.exp (ε * ‖ζ‖ ^ (3 / 2 : ℝ)) := (one_mul _).symm
          _ ≤ (1 + R₀) * Real.exp (ε * ‖ζ‖ ^ (3 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    calc ‖Ψ ζ‖
        ≤ C_env * (1 + ‖ζ‖) ^ (1 / 2 : ℝ) * Real.exp (KTip * ‖ζ‖ ^ (3 / 2 : ℝ)) := h1
      _ = C_env * Real.exp (KTip * ‖ζ‖ ^ (3 / 2 : ℝ)) * (1 + ‖ζ‖) ^ (1 / 2 : ℝ) := by ring
      _ ≤ C_env * Real.exp (KTip * ‖ζ‖ ^ (3 / 2 : ℝ)) *
            ((1 + R₀) * Real.exp (ε * ‖ζ‖ ^ (3 / 2 : ℝ))) := by gcongr
      _ = C_ord * (Real.exp (KTip * ‖ζ‖ ^ (3 / 2 : ℝ)) * Real.exp (ε * ‖ζ‖ ^ (3 / 2 : ℝ))) := by
          dsimp [C_ord]; ring
      _ = C_ord * Real.exp ((KTip + ε) * ‖ζ‖ ^ (3 / 2 : ℝ)) := by
          rw [← Real.exp_add]; congr 2; ring
  exact ⟨ms, s₁Star, Ψ, γLim, mEsc, C_env, hms_strict, hs₁_sub, hΨ_lim, hγ_sub, hΨ_diff,
    hCenv_nn, hΨ_i1, hΨ_i2, hΨ_i3, hΨ_int, hΨ_norm_le, hΨ_im, hΨ_nonneg, hγLim_nn, hmEsc_nn,
    hre_eq, hneg_half, hΨ_ne_zero, hf_diff, ⟨C_f, hCf_nn, hf_bd⟩, hf_int, hf_ne_zero, hf_im,
    hf_nonneg, hf_int_re, hΨ_ord⟩

/-- Unconditional **Proposition T** (`blowup_limit.tex`, Proposition `bl:T`) for every
`prob : FixedWeightProblem` (producing `D : UniformPropositionPData prob` internally). -/
theorem proposition_T_of_problem (prob : FixedWeightProblem)
    {c' : ℕ → ℝ} (hc' : Tendsto c' atTop atTop)
    (tests : ∀ k : ℕ, FixedBlowupTest prob (c' k))
    (hB : ∃ B : ℝ, ∀ k : ℕ, tipS₁W (c' k) (tests k) ≤ B) :
    ∃ (ms : ℕ → ℕ) (s₁Star : ℝ) (Ψ : ℂ → ℂ) (γLim mEsc C_env : ℝ),
      StrictMono ms ∧
      Tendsto (fun k => tipS₁W (c' (ms k)) (tests (ms k))) atTop (nhds s₁Star) ∧
      TendstoLocallyUniformlyOn (fun k => tipRescaleW prob (c' (ms k)) (tests (ms k)).g)
        Ψ atTop univ ∧
      Tendsto (fun k => (tests (ms k)).gVac / (2 * π * (tests (ms k)).M)) atTop (nhds γLim) ∧
      Differentiable ℂ Ψ ∧
      0 ≤ C_env ∧
      (∀ ζ : ℂ, ‖Ψ ζ‖ ≤ C_env * (1 + ‖ζ‖) ^ (1 / 2 : ℝ) * airyEnv (-(betaTip : ℂ) * ζ)) ∧
      (∀ ζ : ℂ, ζ.im ≠ 0 →
        ‖Ψ ζ‖ ≤ C_env * Real.exp (tipH ζ) *
          (1 + min ((1 + ‖ζ‖) ^ (1 / 2 : ℝ)) (1 / |ζ.im|))) ∧
      (∀ ζ : ℂ, |(-ζ).arg| ≤ 2 * π / 3 → 8 ≤ ‖ζ‖ →
        ‖Ψ ζ‖ ≤ C_env * Real.exp (tipH ζ) / ‖ζ‖) ∧
      Integrable (fun s : ℝ => Ψ (s : ℂ)) ∧
      (∫ s : ℝ, ‖Ψ (s : ℂ)‖ ≤ 1) ∧
      (∀ s : ℝ, (Ψ (s : ℂ)).im = 0) ∧
      (∀ s : ℝ, s₁Star ≤ s → 0 ≤ (Ψ (s : ℂ)).re) ∧
      0 ≤ γLim ∧ 0 ≤ mEsc ∧
      (∫ s : ℝ, (Ψ (s : ℂ)).re) = -(γLim + mEsc) ∧
      ((1 / 2 : ℝ) ≤ ∫ s : ℝ, max 0 (-(Ψ (s : ℂ)).re)) ∧
      (∃ z : ℂ, Ψ z ≠ 0) ∧
      (let f : ℂ → ℂ := fun u => Ψ (-u / (betaTip : ℂ))
       Differentiable ℂ f ∧
       (∃ C_f : ℝ, 0 ≤ C_f ∧ ∀ u : ℂ, ‖f u‖ ≤ C_f * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u) ∧
       Integrable (fun u : ℝ => f (u : ℂ)) ∧
       (∃ u : ℂ, f u ≠ 0) ∧
       (∀ u : ℝ, (f (u : ℂ)).im = 0) ∧
       (∀ u : ℝ, u ≤ -betaTip * s₁Star → 0 ≤ (f (u : ℂ)).re) ∧
       (∫ u : ℝ, (f (u : ℂ)).re) ≤ 0 ∧
       (∀ ε : ℝ, 0 < ε → ∃ C_ord : ℝ, 0 ≤ C_ord ∧
         ∀ ζ : ℂ, ‖Ψ ζ‖ ≤ C_ord * Real.exp ((KTip + ε) * ‖ζ‖ ^ (3 / 2 : ℝ)))) :=
  let ⟨D⟩ := UniformPropositionPData.of_problem prob
  proposition_T_general prob D hc' tests hB

/-! ### Section 4: Family packages and Concrete Theorems C and R1--R3 at general `(w, Q)` -/

private lemma concrete_test_threshold_scaling (prob : FixedWeightProblem) {c' T : ℝ}
    (_hc'_pos : 0 < c') (hc'_shift : prob.totalShift ≤ c' / 12) {g : ℝ → ℝ}
    (hwf : prob.IsWeaklyFeasible (c' / 12) T g) :
    let test := blowupTest_of_concrete_general hc'_shift hwf
    test.t₁ = leastThreshold g ∧
    tipS₁W c' test = (Real.sqrt (3 * leastThreshold g / c') - xiStar) / tipEps c' :=
  ⟨rfl, rfl⟩

/-- Unconditional **`BlowupFamilyPackage ι p`** at general `(w, Q)` for any asymptotic family
of concrete weakly feasible tests `prob.IsWeaklyFeasible (c' n / 12) T (g n)`. -/
noncomputable def blowupFamilyPackage_of_concrete_tests_general (prob : FixedWeightProblem)
    {ι : Type*} {p : Filter ι} {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (g : ι → ℝ → ℝ)
    (hg : ∀ᶠ n in p, ∃ T : ℝ, prob.IsWeaklyFeasible (c' n / 12) T (g n)) :
    BlowupFamilyPackage ι p where
  c' := c'
  s₁ := fun n => (Real.sqrt (3 * leastThreshold (g n) / c' n) - xiStar) / tipEps (c' n)
  t₁ := fun n => leastThreshold (g n)
  Φ := fun n => tipRescaleW prob (c' n) (g n)
  γ := fun n => prob.gVac (c' n / 12) (g n) / (2 * π * prob.cardyNorm (c' n / 12) (g n))
  hc'_tendsto := hc'
  hγ_nonneg := by
    filter_upwards [hc'.eventually (eventually_ge_atTop (max 1 (24 * prob.totalShift))), hg] with
      n hc'n ⟨_, hwf⟩
    have hc'0 : 0 < c' n := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans hc'n)
    have hsh : prob.totalShift ≤ c' n / 12 := shift_div12_of_mul24 ((le_max_right 1 _).trans hc'n)
    have hM := cardyNorm_pos_of_nonzero_general prob hsh hwf.1 hwf.2.1
    exact div_nonneg hwf.2.2.1 (by positivity [Real.pi_pos])
  scaling_eq := by
    filter_upwards [hc'.eventually (eventually_ge_atTop (max 1 (24 * prob.totalShift))), hg] with
      n hc'n ⟨_, hwf⟩
    have hc'0 : 0 < c' n := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans hc'n)
    have hsh : prob.totalShift ≤ c' n / 12 := shift_div12_of_mul24 ((le_max_right 1 _).trans hc'n)
    exact tipS₁W_scaling_eq hc'0 (blowupTest_of_concrete_general hsh hwf)
  theorem_A_lower := by
    obtain ⟨C₀, c_A, _, hcA_sh, hA⟩ := tipS₁W_theorem_A_lower_general prob
    refine ⟨C₀, ?_⟩
    filter_upwards [hc'.eventually (eventually_ge_atTop c_A), hg] with n hc'n ⟨_, hwf⟩
    have hsh : prob.totalShift ≤ c' n / 12 :=
      shift_div12_of_mul24 (((le_max_right 1 _).trans hcA_sh).trans hc'n)
    exact hA hc'n (blowupTest_of_concrete_general hsh hwf)
  propT_subseq := fun ns hns hB => by
    classical
    have hc''0 : Tendsto (fun k => c' (ns k)) atTop atTop := hc'.comp hns
    have hmem : ∀ᶠ k in atTop,
        max 1 (24 * prob.totalShift) ≤ c' (ns k) ∧
          ∃ T : ℝ, prob.IsWeaklyFeasible (c' (ns k) / 12) T (g (ns k)) :=
      (hc''0.eventually (eventually_ge_atTop (max 1 (24 * prob.totalShift)))).and (hns.eventually hg)
    obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp hmem
    have hc'' : Tendsto (fun k => c' (ns (k + K₀))) atTop atTop :=
      hc''0.comp (tendsto_add_atTop_nat K₀)
    let tests : ∀ k : ℕ, FixedBlowupTest prob (c' (ns (k + K₀))) := fun k =>
      let hk := hK₀ (k + K₀) (Nat.le_add_left K₀ k)
      have hsh : prob.totalShift ≤ c' (ns (k + K₀)) / 12 :=
        shift_div12_of_mul24 ((le_max_right 1 _).trans hk.1)
      blowupTest_of_concrete_general hsh hk.2.choose_spec
    have hB' : ∃ B : ℝ, ∀ k : ℕ, tipS₁W (c' (ns (k + K₀))) (tests k) ≤ B := by
      obtain ⟨B, hB⟩ := hB
      exact ⟨B, fun k => hB (k + K₀)⟩
    obtain ⟨ms, s₁Star, Ψ, γLim, mEsc, C_env, hms, hs₁, hΦ, hγ, hΨd, hCnn, hΨb, _, _, hΨi,
      hΨnorm, hΨim, hΨnn, hγnn, hmEscnn, hΨre, hneg, hΨne, _⟩ :=
      proposition_T_of_problem prob hc'' tests hB'
    refine ⟨fun j => ms j + K₀, s₁Star, Ψ, γLim, mEsc,
      fun i j hij => Nat.add_lt_add_right (hms hij) K₀, hs₁, hΦ, hγ, hΨd, hΨi,
      ⟨C_env, hCnn, hΨb⟩, hΨne, hΨim, hΨnn, hΨnorm, hγnn, hmEscnn, hΨre, hneg⟩

/-- Unconditional **`RigidityFamilyPackage ι p`** at general `(w, Q)` for any asymptotic family
of concrete weakly feasible tests (`0 < t₁ → g t₁ = 0` follows automatically from `leastThreshold`). -/
noncomputable def rigidityFamilyPackage_of_concrete_tests_general (prob : FixedWeightProblem)
    {ι : Type*} {p : Filter ι} {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (g : ι → ℝ → ℝ)
    (hg : ∀ᶠ n in p, ∃ T : ℝ, prob.IsWeaklyFeasible (c' n / 12) T (g n)) :
    RigidityFamilyPackage ι p where
  toBlowupFamilyPackage := blowupFamilyPackage_of_concrete_tests_general prob hc' g hg
  domain_integrable := by
    filter_upwards [hc'.eventually (eventually_ge_atTop (max 1 (24 * prob.totalShift))), hg] with
      n hc'n hgn
    have hc'0 : 0 < c' n := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans hc'n)
    have hsh : prob.totalShift ≤ c' n / 12 := shift_div12_of_mul24 ((le_max_right 1 _).trans hc'n)
    have h := tipRescaleW_integrableOn_domain hc'0 hsh (blowupTest_of_concrete_general hsh hgn.choose_spec)
    simpa only [blowupFamilyPackage_of_concrete_tests_general, tipSMin, blowupTest_of_concrete_general] using h
  domain_norm_integral := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hc'.eventually (eventually_ge_atTop (max 1 (24 * prob.totalShift))), hg] with
      n hc'n hgn
    have hc'0 : 0 < c' n := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans hc'n)
    have hsh : prob.totalShift ≤ c' n / 12 := shift_div12_of_mul24 ((le_max_right 1 _).trans hc'n)
    have h := (tipRescaleW_norm_integral hc'0 hsh (blowupTest_of_concrete_general hsh hgn.choose_spec)).symm
    simpa only [blowupFamilyPackage_of_concrete_tests_general, tipSMin, blowupTest_of_concrete_general] using h
  holo_balls := fun R => by
    obtain ⟨c₀_H, _, hholo_fn⟩ := tipRescaleW_holo_exists prob
    have hεR : Tendsto (fun n => 2 * R * tipEps (c' n)) p (nhds 0) := by
      have h0 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc'
      simpa [tipEps] using h0.const_mul (2 * R)
    filter_upwards [hc'.eventually (eventually_ge_atTop (max 1 c₀_H)), hg,
      hεR.eventually (eventually_lt_nhds one_pos)] with n hc'n hgn h2R
    have hc'0 : 0 < c' n := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans hc'n)
    dsimp [blowupFamilyPackage_of_concrete_tests_general]
    exact tipRescaleW_holo_ball hc'0 h2R (hholo_fn ((le_max_right 1 _).trans hc'n) hgn.choose_spec.1)
  real_symm := fun R => by
    obtain ⟨c₀_H, _, hholo_fn⟩ := tipRescaleW_holo_exists prob
    have hεR : Tendsto (fun n => 2 * R * tipEps (c' n)) p (nhds 0) := by
      have h0 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc'
      simpa [tipEps] using h0.const_mul (2 * R)
    filter_upwards [hc'.eventually (eventually_ge_atTop (max 1 c₀_H)), hg,
      hεR.eventually (eventually_lt_nhds one_pos)] with n hc'n hgn h2R z hz
    have hc'0 : 0 < c' n := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans hc'n)
    have hε_pos := tipEps_pos hc'0
    have him : |z.im| < 1 / (2 * tipEps (c' n)) := by
      have hzn : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
      have hzr : ‖z‖ < R := mem_ball_zero_iff.mp hz
      rw [lt_div_iff₀ (by positivity)]
      nlinarith
    dsimp [blowupFamilyPackage_of_concrete_tests_general]
    exact tipRescaleW_real_symm hc'0 hgn.choose_spec.1
      (hholo_fn ((le_max_right 1 _).trans hc'n) hgn.choose_spec.1) him
  nonneg_tail := by
    filter_upwards [hc'.eventually (eventually_ge_atTop (max 1 (24 * prob.totalShift))), hg] with
      n hc'n hgn s hs
    have hc'0 : 0 < c' n := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans hc'n)
    have hsh : prob.totalShift ≤ c' n / 12 := shift_div12_of_mul24 ((le_max_right 1 _).trans hc'n)
    dsimp [blowupFamilyPackage_of_concrete_tests_general] at hs ⊢
    exact tipRescaleW_nonneg_tail hc'0 hsh (blowupTest_of_concrete_general hsh hgn.choose_spec) s hs
  s1_is_zero := by
    obtain ⟨C_A, c_A, _, hcA_ge1, hA⟩ := theorem_A_general prob
    have hpos_t1 : Tendsto (fun n => xiBar * c' n - C_A * c' n ^ (1 / 3 : ℝ)) p atTop := by
      have hsub : ∀ᶠ n in p, 1 ≤ c' n →
          xiBar * c' n - C_A * c' n ^ (1 / 3 : ℝ) =
            c' n * (xiBar - C_A * c' n ^ (-(2 / 3 : ℝ))) := by
        filter_upwards [hc'.eventually (eventually_ge_atTop (1 : ℝ))] with n _ _
        have hc'n : 0 < c' n := by linarith
        have h1 : c' n * c' n ^ (-(2 / 3 : ℝ)) = c' n ^ (1 / 3 : ℝ) := by
          conv_lhs => arg 1; rw [← Real.rpow_one (c' n)]
          rw [← Real.rpow_add hc'n]; norm_num
        linarith [show C_A * (c' n * c' n ^ (-(2 / 3 : ℝ))) = C_A * c' n ^ (1 / 3 : ℝ) by rw [h1]]
      have hfac : Tendsto (fun n => c' n * (xiBar - C_A * c' n ^ (-(2 / 3 : ℝ)))) p atTop := by
        have hlim : Tendsto (fun n => xiBar - C_A * c' n ^ (-(2 / 3 : ℝ))) p (nhds xiBar) := by
          have h0 := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc').const_mul C_A
          simpa using tendsto_const_nhds.sub h0
        have hxi_pos : 0 < xiBar := by unfold xiBar; positivity [xiStar_pos]
        exact hc'.atTop_mul_pos hxi_pos hlim
      refine hfac.congr' ?_
      filter_upwards [hc'.eventually (eventually_ge_atTop (1 : ℝ)), hsub] with n hn hs
      exact (hs hn).symm
    filter_upwards [hc'.eventually (eventually_ge_atTop (max c_A (max 1 (24 * prob.totalShift)))), hg,
      hpos_t1.eventually (eventually_gt_atTop (0 : ℝ))] with n hc'n hgn hlb
    have hcA_n : c_A ≤ c' n := (le_max_left _ _).trans hc'n
    have hge_n : max 1 (24 * prob.totalShift) ≤ c' n := (le_max_right _ _).trans hc'n
    have hc'0 : 0 < c' n := lt_of_lt_of_le zero_lt_one ((le_max_left 1 _).trans hge_n)
    have hsh : prob.totalShift ≤ c' n / 12 := shift_div12_of_mul24 ((le_max_right 1 _).trans hge_n)
    let test := blowupTest_of_concrete_general hsh hgn.choose_spec
    have ht1_pos : 0 < test.t₁ := lt_of_lt_of_le hlb (hA hcA_n test.isWeaklyFeasible)
    have hg0 : test.g test.t₁ = 0 :=
      isThreshold_imp_g_t1_eq_zero test.hg_test.cont ht1_pos test.ht₁_least test.hg_nonneg_tail
    have ht_eq : tipTReal (c' n) (tipS₁W (c' n) test) = test.t₁ := by
      unfold tipTReal tipBReal tipS₁W
      have hε : tipEps (c' n) ≠ 0 := (tipEps_pos hc'0).ne'
      rw [show xiStar + tipEps (c' n) * ((test.x₁ (c' n) - xiStar) / tipEps (c' n)) =
          test.x₁ (c' n) by field_simp [hε]; ring, ← test.t₁_eq_x₁_sq hc'0]
    dsimp [blowupFamilyPackage_of_concrete_tests_general]
    change tipRescaleW prob (c' n) test.g (tipS₁W (c' n) test : ℂ) = 0
    rw [tipRescaleW_real_on_real hc'0 test.hg_test, ht_eq, hg0]
    simp

/-- Unconditional **Theorem C** (`local_airy_model.tex`) at general `(w, Q)` for concrete
weakly feasible tests. -/
theorem concrete_blowup_theorem_C_general (prob : FixedWeightProblem)
    {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (g : ι → ℝ → ℝ)
    (hg : ∀ᶠ n in p, ∃ T : ℝ, prob.IsWeaklyFeasible (c' n / 12) T (g n)) :
    (Aopt : EReal) ≤
      Filter.liminf (fun n =>
        (((leastThreshold (g n) - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ) : ℝ) : EReal)) p :=
  theorem_C (blowupFamilyPackage_of_concrete_tests_general prob hc' g hg)

/-- Unconditional **Attainment (`Att`)** from an upper Airy threshold bound
`T ≤ T_up = ξ̄ c' + Aopt c'^{1/3} + o(c'^{1/3})`: by `theorem_C_eventually`, no external
Theorem `W1'(1)` input is needed to pass from an upper threshold bound to two-sided `Att`. -/
theorem att_of_upper_threshold_general (prob : FixedWeightProblem)
    {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (g : ι → ℝ → ℝ)
    (T_up : ι → ℝ)
    (hT_lim : Tendsto (fun n => (T_up n - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ)) p (nhds Aopt))
    (hg_up : ∀ᶠ n in p, ∃ T : ℝ, 0 ≤ T ∧ T ≤ T_up n ∧ prob.IsWeaklyFeasible (c' n / 12) T (g n)) :
    let hg : ∀ᶠ n in p, ∃ T : ℝ, prob.IsWeaklyFeasible (c' n / 12) T (g n) :=
      hg_up.mono fun _ ⟨T, _, _, hwf⟩ => ⟨T, hwf⟩
    Att (blowupFamilyPackage_of_concrete_tests_general prob hc' g hg) := by
  intro hg
  let F := blowupFamilyPackage_of_concrete_tests_general prob hc' g hg
  have hlo := theorem_C_eventually F
  unfold Att
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h1 := hlo (ε / 2) (half_pos hε)
  have h2 := (Metric.tendsto_nhds.mp hT_lim) (ε / 2) (half_pos hε)
  filter_upwards [hc'.eventually (eventually_ge_atTop (1 : ℝ)), h1, h2, hg_up] with
    n hc'n hn_lo hn_hi ⟨T, hT0, hT_up, hwf⟩
  have hc'0 : 0 < c' n := by linarith
  have hp13 : 0 < (c' n) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc'0 _
  have hlt_le : leastThreshold (g n) ≤ T := leastThreshold_le hT0 hwf.2.2.2
  have h_le_up : (leastThreshold (g n) - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ) ≤
      (T_up n - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) hp13.le
  rw [Real.dist_eq, abs_lt]
  have hn_hi' := abs_lt.mp (by simpa [Real.dist_eq] using hn_hi)
  dsimp [F, blowupFamilyPackage_of_concrete_tests_general] at hn_lo ⊢
  exact ⟨by linarith, by linarith⟩

/-- Unconditional **Theorem R `(R1)`** (`rigidity.tex`) at general `(w, Q)` under `Att`. -/
theorem concrete_blowup_theorem_R1_general (prob : FixedWeightProblem)
    {ι : Type*} {p : Filter ι} [p.IsCountablyGenerated]
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (g : ι → ℝ → ℝ)
    (hg : ∀ᶠ n in p, ∃ T : ℝ, prob.IsWeaklyFeasible (c' n / 12) T (g n))
    (hAtt : Att (blowupFamilyPackage_of_concrete_tests_general prob hc' g hg)) :
    let F := blowupFamilyPackage_of_concrete_tests_general prob hc' g hg
    Tendsto F.s₁ p (nhds s1) ∧
    TendstoLocallyUniformlyOn F.Φ phiStar p univ ∧
    Tendsto F.γ p (nhds 0) :=
  theorem_R1 (blowupFamilyPackage_of_concrete_tests_general prob hc' g hg) hAtt

/-- Unconditional **Theorem R `(R2)`** (`rigidity.tex`) at general `(w, Q)` under `Att`. -/
theorem concrete_blowup_theorem_R2_general (prob : FixedWeightProblem)
    {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (g : ι → ℝ → ℝ)
    (hg : ∀ᶠ n in p, ∃ T : ℝ, prob.IsWeaklyFeasible (c' n / 12) T (g n))
    (hAtt : Att (blowupFamilyPackage_of_concrete_tests_general prob hc' g hg)) :
    let R := rigidityFamilyPackage_of_concrete_tests_general prob hc' g hg
    Tendsto (fun n => ∫ s : ℝ, ‖phiExt R n s - phiStar (s : ℂ)‖) p (nhds 0) ∧
    Tendsto (fun n => ∫ s in Ioi (-xiStar * (c' n) ^ (2 / 3 : ℝ)),
      ‖R.Φ n (s : ℂ) - phiStar (s : ℂ)‖) p (nhds 0) ∧
    (∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 0 < R₀ ∧
      ∀ᶠ n in p, ∫ s in Ioi R₀ ∪ Iio (-R₀), ‖phiExt R n s‖ < ε) ∧
    Tendsto (fun R₀ : ℝ => Filter.limsup (fun n => ∫ s in Ioi R₀ ∪ Iio (-R₀), ‖phiExt R n s‖) p)
      atTop (nhds 0) :=
  theorem_R2 (rigidityFamilyPackage_of_concrete_tests_general prob hc' g hg) hAtt

/-- Unconditional **Theorem R `(R3)`** (`rigidity.tex`) at general `(w, Q)` under `Att`. -/
theorem concrete_blowup_theorem_R3_general (prob : FixedWeightProblem)
    {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (g : ι → ℝ → ℝ)
    (hg : ∀ᶠ n in p, ∃ T : ℝ, prob.IsWeaklyFeasible (c' n / 12) T (g n))
    (hAtt : Att (blowupFamilyPackage_of_concrete_tests_general prob hc' g hg)) :
    let R := rigidityFamilyPackage_of_concrete_tests_general prob hc' g hg
    (∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∀ᶠ n in p,
      zeroCount (R.Φ n) (s1 : ℂ) r = 1 ∧ (R.s₁ n : ℂ) ∈ ball (s1 : ℂ) r ∧
      R.Φ n (R.s₁ n : ℂ) = 0 ∧ analyticOrderNatAt (R.Φ n) (R.s₁ n : ℂ) = 1 ∧
      ∀ z ∈ ball (s1 : ℂ) r, R.Φ n z = 0 → z = (R.s₁ n : ℂ)) ∧
    (∀ k : ℕ, 2 ≤ k → ∃ r₀ > 0,
      (∀ r, 0 < r → r ≤ r₀ → ∀ᶠ n in p,
        zeroCount (R.Φ n) (sNode k : ℂ) r = 2 ∧
        ((∃ x : ℝ, (x : ℂ) ∈ ball (sNode k : ℂ) r ∧ R.Φ n (x : ℂ) = 0 ∧
            analyticOrderNatAt (R.Φ n) (x : ℂ) = 2 ∧
            ∀ z ∈ ball (sNode k : ℂ) r, R.Φ n z = 0 → z = (x : ℂ)) ∨
         (∃ z : ℂ, z ∈ ball (sNode k : ℂ) r ∧ z.im ≠ 0 ∧ R.Φ n z = 0 ∧
            R.Φ n (starRingEnd ℂ z) = 0 ∧ analyticOrderNatAt (R.Φ n) z = 1 ∧
            analyticOrderNatAt (R.Φ n) (starRingEnd ℂ z) = 1 ∧
            ∀ w ∈ ball (sNode k : ℂ) r, R.Φ n w = 0 → w = z ∨ w = starRingEnd ℂ z))) ∧
      (∀ z : ι → ℂ, (∀ᶠ n in p, z n ∈ ball (sNode k : ℂ) r₀ ∧ R.Φ n (z n) = 0) →
        Tendsto z p (nhds (sNode k : ℂ)) ∧
        Tendsto (fun n => (tScale (R.c' n) (z n) - ((xiBar * R.c' n : ℝ) : ℂ)) /
            (((R.c' n) ^ (1 / 3 : ℝ) : ℝ) : ℂ)) p
          (nhds ((((|airyZero k| / |airyZero 1|) * Aopt : ℝ) : ℂ))) ∧
        (k = 2 →
          Tendsto (fun n => (tScale (R.c' n) (z n) - (R.t₁ n : ℂ)) /
              ((((R.c' n + 1) ^ (1 / 3 : ℝ) : ℝ) : ℂ))) p
            (nhds ((((|airyZero 2| / |airyZero 1| - 1) * Aopt : ℝ) : ℂ))))) ∧
      (∃ z : ι → ℂ, ∀ᶠ n in p, z n ∈ ball (sNode k : ℂ) r₀ ∧ R.Φ n (z n) = 0)) ∧
    (∀ K : Set ℂ, IsCompact K → (∀ k : ℕ, 1 ≤ k → (sNode k : ℂ) ∉ K) →
      ∀ᶠ n in p, ∀ z ∈ K, R.Φ n z ≠ 0) :=
  theorem_R3 _ hAtt

/-! ### Axiom Checks -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.blowupTest_of_concrete_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms blowupTest_of_concrete_general

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.fixedBlowupTest_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixedBlowupTest_nonempty

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.lemma_T5_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_T5_general

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.blowup_left_tail_bound_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms blowup_left_tail_bound_general

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.tipS₁W_theorem_A_lower_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tipS₁W_theorem_A_lower_general

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.theorem_A_lower_from_lowerBoundInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theorem_A_lower_from_lowerBoundInput

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.proposition_T_of_problem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_T_of_problem

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.concrete_blowup_theorem_C_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms concrete_blowup_theorem_C_general

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.att_of_upper_threshold_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms att_of_upper_threshold_general

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.concrete_blowup_theorem_R1_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms concrete_blowup_theorem_R1_general

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.concrete_blowup_theorem_R2_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms concrete_blowup_theorem_R2_general

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.concrete_blowup_theorem_R3_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms concrete_blowup_theorem_R3_general

end FormalResearch.ModularBootstrap.FixedWeightTip


