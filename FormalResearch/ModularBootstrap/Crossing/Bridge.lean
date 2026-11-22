module

public import FormalResearch.ModularBootstrap.Crossing.SumRule
public import FormalResearch.ModularBootstrap.SlitStrip.EntropyAndDeficit

/-!
# Bridge from Concrete Virasoro Crossing to Slit-Strip `Theorem A`

Formalizes the bridge from concrete weakly feasible Virasoro tests
(`FixedWeightProblem.IsWeaklyFeasible virasoroProblem (c' / 12) T g`) in
`Crossing/Setup.lean` to `WeaklyFeasibleTest` and `theorem_A` in
`SlitStrip/EntropyAndDeficit.lean`:

* `virasoro_Ka_ub`: Direct proof of the Bessel upper bound `hKa_ub` for
  `K_a = kernelK 1 (c' / 12)` on `x ∈ [0.05, xiStar]` with explicit constant
  `C_K = √(15 / 4)`, using `besselI_zero_le_exp_div_sqrt` from `Crossing/SumRule.lean`.
* `LemmaPJInput` and `LemmaGapInput`: Named unproved analytic hypotheses corresponding
  respectively to Lemma `PJ` (`vlo:PJ`, strip Poisson--Jensen bound uniform over nonzero
  `TestClass virasoroProblem (c' / 12)`) and Lemma `G` (`vlo:Gap`, fixed-gap deep-lobe
  concentration at `x₀ = 0.05` uniform over `TestClass virasoroProblem (c' / 12)`).
* `VirasoroStripParams` and `virasoroStripParams_nonvacuous`: Consistency / non-vacuity
  of the geometric slice parameters (`RealSliceData`, `PoissonJensenInput` with
  `C_K = √(15 / 4)`, `FixedGapInput`).
* `weaklyFeasibleTestOfConcrete`: Construction of `WeaklyFeasibleTest pj fg c'` from any
  concrete `virasoroProblem.IsWeaklyFeasible (c' / 12) T g` (`0 ≤ T`, `24 ≤ c'`),
  proving `hM_pos` (continuity + `V > 0` on `(0, ∞)`), `hV_nonneg`, `hV_cont`,
  `hV_le_two_Ka`, `hKa_ub`, and `hHalfMass` directly from the crossing sign conditions.
* `theorem_A_T_weak`, `theorem_A_T_V`, and `theorem_A_Delta_best`: Theorem A for the
  actual Virasoro LP thresholds `T_weak(c')`, `T_V(c')`, and `Delta_best(c')`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Crossing

open FormalResearch.ModularBootstrap

/-! ### Direct proof of `hKa_ub` with `C_K = √(15 / 4)` -/

/-- Direct proof of the `I_0` upper bound `hKa_ub` on `x ∈ [0.05, xiStar]` for
Virasoro (`w = 1`, `a = c' / 12`, `t = c' x² / 3`), with explicit constant `√(15 / 4)`. -/
theorem virasoro_Ka_ub {c' : ℝ} (hc' : 0 < c') {x : ℝ} (hx : x ∈ Icc (0.05 : ℝ) xiStar) :
    kernelK 1 (c' / 12) (c' * x ^ 2 / 3) ≤
      Real.sqrt (15 / 4) * Real.exp (c' * ((2 * π / 3) * x)) / Real.sqrt c' := by
  have hx_pos : 0 < x := by linarith [hx.1]
  have ha_pos : 0 < c' / 12 := by linarith
  have ht_pos : 0 < c' * x ^ 2 / 3 := by positivity
  rw [kernelK_eq_besselI (w := 1) (le_refl 1) ha_pos ht_pos]
  simp only [Nat.sub_self, pow_zero, one_mul]
  let z : ℝ := c' * ((2 * π / 3) * x)
  have hz_arg : 4 * π * Real.sqrt ((c' / 12) * (c' * x ^ 2 / 3)) = z := by
    have hsq : (c' / 12) * (c' * x ^ 2 / 3) = (c' * x / 6) ^ 2 := by ring
    rw [hsq, Real.sqrt_sq (by positivity)]
    dsimp [z]; ring
  have hz_pos : 0 < z := by dsimp [z]; positivity
  rw [hz_arg]
  have hbes := besselI_zero_le_exp_div_sqrt hz_pos
  have hpref : Real.sqrt (π / 8) / Real.sqrt z ≤ Real.sqrt (15 / 4) / Real.sqrt c' := by
    have hsqrt_z : Real.sqrt z = Real.sqrt ((2 * π / 3) * x) * Real.sqrt c' := by
      dsimp [z]
      rw [Real.sqrt_mul hc'.le]
      ring
    rw [hsqrt_z, div_mul_eq_div_div]
    refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg c')
    rw [← Real.sqrt_div (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have h1 : (π / 8) / ((2 * π / 3) * x) = 3 / (16 * x) := by
      have hpi_ne : π ≠ 0 := Real.pi_pos.ne'
      field_simp; ring
    rw [h1, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [hx.1]
  calc besselI 0 z ≤ Real.sqrt (π / 8) * Real.exp z / Real.sqrt z := hbes
    _ = (Real.sqrt (π / 8) / Real.sqrt z) * Real.exp z := by ring
    _ ≤ (Real.sqrt (15 / 4) / Real.sqrt c') * Real.exp z :=
        mul_le_mul_of_nonneg_right hpref (Real.exp_pos z).le
    _ = Real.sqrt (15 / 4) * Real.exp (c' * ((2 * π / 3) * x)) / Real.sqrt c' := by
        dsimp [z]; ring

/-! ### Named unproved analytic inputs (`Lemma PJ` and `Lemma G`) -/

/-- **Unproved analytic input (`Lemma PJ`, `lower_o1_two_edge.tex`, `vlo:PJ`):**
Uniform slit-strip Poisson--Jensen estimate on `x ∈ [0, xiStar)` over all nonzero concrete
Virasoro tests `g ∈ TestClass virasoroProblem (c' / 12)` for `c' ≥ c_PJ`.
Not proved in this module. -/
def LemmaPJInput (rs : RealSliceData) (c_PJ C_PJ : ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ {c' : ℝ}, c_PJ ≤ c' → ∀ {g : ℝ → ℝ},
    TestClass virasoroProblem (c' / 12) g →
    0 < virasoroProblem.cardyNorm (c' / 12) g →
    ∀ x ∈ Ico 0 xiStar, g (c' * x ^ 2 / 3) ≠ 0 →
      Real.log |g (c' * x ^ 2 / 3)| ≤
        c' * U x + Real.log (virasoroProblem.cardyNorm (c' / 12) g) - (1 / 2 : ℝ) * Real.log c' +
          (5 / 2 : ℝ) * (1 - rs.slitMassAt x) * Real.log c' + rs.slitEntropyAt x + C_PJ

/-- **Unproved analytic input (`Lemma G`, `lower_o1_two_edge.tex`, `vlo:Gap` at `x₀ = 0.05`):**
Uniform fixed-gap exponential concentration of `|g| V` on `[0, c' · 0.05² / 3]` over all
concrete Virasoro tests `g ∈ TestClass virasoroProblem (c' / 12)` for `c' ≥ fg.c_deep`.
Not proved in this module. -/
def LemmaGapInput (fg : FixedGapInput) : Prop :=
  ∀ {c' : ℝ}, fg.c_deep ≤ c' → ∀ {g : ℝ → ℝ},
    TestClass virasoroProblem (c' / 12) g →
    ∫ t in (0 : ℝ)..(c' * (0.05 : ℝ) ^ 2 / 3), |g t| * virasoroProblem.cardyV (c' / 12) t ≤
      fg.C_deep * Real.exp (-fg.κ_deep * c') * virasoroProblem.cardyNorm (c' / 12) g

/-- Geometric slice and threshold parameters for the Virasoro strip bridge, bundling the
geometric part of `PoissonJensenInput` (with `C_K = √(15 / 4)` proved in `virasoro_Ka_ub`)
and `FixedGapInput`. -/
structure VirasoroStripParams where
  rs : RealSliceData
  c_PJ : ℝ
  C_PJ : ℝ
  U : ℝ → ℝ
  hc_PJ : 1 ≤ c_PJ
  g_deficit : ∀ x ∈ Ico 0 xiStar, U x + (2 * π / 3) * x ≤ -slitDeficit (xiStar - x)
  fg : FixedGapInput

/-- Convert `VirasoroStripParams` to `PoissonJensenInput` with proved constant `C_K = √(15 / 4)`. -/
noncomputable def VirasoroStripParams.toPoissonJensenInput (p : VirasoroStripParams) :
    PoissonJensenInput where
  rs := p.rs
  c_PJ := p.c_PJ
  C_PJ := p.C_PJ
  C_K := Real.sqrt (15 / 4)
  U := p.U
  hc_PJ := p.hc_PJ
  hC_K := by positivity
  g_deficit := p.g_deficit

/-- Bundled Virasoro strip analytic input combining `VirasoroStripParams` with the two
unproved analytic estimates `LemmaPJInput` and `LemmaGapInput`. Not proved in this module. -/
structure VirasoroStripInput extends VirasoroStripParams where
  hPJ : LemmaPJInput rs c_PJ C_PJ U
  hDeepLobe : LemmaGapInput fg

/-- Non-vacuity of the parameter bundle `VirasoroStripParams` (and hence of the induced
`PoissonJensenInput` with `C_K = √(15 / 4)` and `FixedGapInput`), matching the slit-strip
witness of `slitStrip_hypotheses_nonvacuous`.
(Note: `LemmaPJInput` and `LemmaGapInput` themselves quantify over all `g ∈ TestClass` and
constitute the unproved analytic Lemma PJ / Lemma G inputs of `lower_o1_two_edge.tex`.) -/
theorem virasoroStripParams_nonvacuous :
    ∃ p : VirasoroStripParams, p.toPoissonJensenInput.C_K = Real.sqrt (15 / 4) := by
  let rs : RealSliceData :=
    { xUHP := fun _ => sigmaStar
      yUHP := fun δ => Real.sqrt δ
      C_e := 0
      c_y := 1
      C_y := 1
      hC_e := le_rfl
      hc_y := zero_lt_one
      hC_y := le_rfl
      re_bound := fun _ _ => by simp
      im_lower := fun _ _ => by simp
      im_upper := fun _ _ => by simp }
  let fg : FixedGapInput :=
    { c_deep := 1
      C_deep := 1
      κ_deep := 1
      hc_deep := le_rfl
      hC_deep := zero_le_one
      hκ_deep := zero_lt_one }
  let p : VirasoroStripParams :=
    { rs := rs
      c_PJ := 1
      C_PJ := Real.log 3
      U := fun x => -(2 * π / 3) * x - slitDeficit (xiStar - x)
      hc_PJ := le_rfl
      g_deficit := fun x _ => by linarith
      fg := fg }
  exact ⟨p, rfl⟩

/-! ### Constructing `WeaklyFeasibleTest` from concrete Virasoro tests -/

lemma cardyNorm_pos_of_nonzero {a : ℝ} (ha : virasoroProblem.totalShift ≤ a)
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem a g) (hnonzero : ∃ t ≥ 0, g t ≠ 0) :
    0 < virasoroProblem.cardyNorm a g := by
  unfold FixedWeightProblem.cardyNorm
  have hint : IntegrableOn (fun t => |g t| * virasoroProblem.cardyV a t) (Ioi 0) := hg.int_cardy
  have hcont : ContinuousOn (fun t => |g t| * virasoroProblem.cardyV a t) (Ioi 0) :=
    (hg.cont.abs.mul (continuous_cardyV virasoroProblem a).continuousOn).mono Ioi_subset_Ici_self
  have hnn : 0 ≤ ∫ t in Ioi 0, |g t| * virasoroProblem.cardyV a t :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (abs_nonneg _) (virasoroProblem.cardyV_nonneg ha (Set.mem_Ioi.mp ht).le)
  rcases hnn.eq_or_lt with heq | hlt
  · exfalso
    have hzero_ae : (fun t => |g t| * virasoroProblem.cardyV a t) =ᵐ[volume.restrict (Ioi 0)] 0 := by
      refine (integral_eq_zero_iff_of_nonneg_ae ?_ hint).mp heq.symm
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (abs_nonneg _) (virasoroProblem.cardyV_nonneg ha (Set.mem_Ioi.mp ht).le)
    have hpos_ae : ∀ t ∈ Ioi (0 : ℝ), |g t| * virasoroProblem.cardyV a t = 0 := by
      intro t ht
      by_contra hne
      have hpos : 0 < |g t| * virasoroProblem.cardyV a t :=
        lt_of_le_of_ne (mul_nonneg (abs_nonneg _) (virasoroProblem.cardyV_nonneg ha ht.le))
          (Ne.symm hne)
      obtain ⟨r, hr_pos, hr_lt⟩ := Metric.continuousAt_iff.mp
        (hcont.continuousAt (Ioi_mem_nhds ht))
        ((|g t| * virasoroProblem.cardyV a t) / 2) (half_pos hpos)
      have hopen : (Metric.ball t r ∩ Ioi (0 : ℝ)).Nonempty := ⟨t, Metric.mem_ball_self hr_pos, ht⟩
      have hmeas_pos : 0 < (volume.restrict (Ioi (0 : ℝ))) (Metric.ball t r ∩ Ioi (0 : ℝ)) := by
        rw [Measure.restrict_apply (measurableSet_ball.inter measurableSet_Ioi), Set.inter_assoc,
          Set.inter_self]
        exact (Metric.isOpen_ball.inter isOpen_Ioi).measure_pos _ hopen
      have hsub_null : Metric.ball t r ∩ Ioi (0 : ℝ) ⊆
          {s | |g s| * virasoroProblem.cardyV a s ≠ 0} := by
        intro s hs hzero
        have hdist := hr_lt (Metric.mem_ball.mp hs.1)
        rw [hzero, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hpos] at hdist
        linarith
      have hnull : (volume.restrict (Ioi (0 : ℝ))) (Metric.ball t r ∩ Ioi (0 : ℝ)) = 0 :=
        measure_mono_null hsub_null (ae_iff.mp hzero_ae)
      exact hmeas_pos.ne' hnull
    have hg_pos : ∀ t : ℝ, 0 < t → g t = 0 := fun t ht => by
      have hmul := hpos_ae t ht
      rcases mul_eq_zero.mp hmul with h1 | h2
      · exact abs_eq_zero.mp h1
      · exfalso
        exact (virasoroProblem.cardyV_pos ha ht).ne' h2
    have hg_zero_at_0 : g 0 = 0 := by
      have htend : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) :=
        (hg.cont 0 (le_refl 0)).mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
      exact tendsto_nhds_unique htend (tendsto_const_nhds.congr' (by
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact (hg_pos t ht).symm))
    obtain ⟨t₀, ht₀, hne⟩ := hnonzero
    rcases eq_or_lt_of_le ht₀ with rfl | ht₀_pos
    · exact hne hg_zero_at_0
    · exact hne (hg_pos t₀ ht₀_pos)
  · exact hlt

lemma half_mass_of_weak_sign {a T : ℝ} (ha : virasoroProblem.totalShift ≤ a)
    (hT : 0 ≤ T) {g : ℝ → ℝ} (hg : TestClass virasoroProblem a g)
    (hgVac : 0 ≤ virasoroProblem.gVac a g) (hsign : ∀ t ≥ T, 0 ≤ g t) :
    virasoroProblem.cardyNorm a g / 2 ≤
      ∫ t in (0 : ℝ)..T, |g t| * virasoroProblem.cardyV a t := by
  have hM_int : IntegrableOn (fun t => |g t| * virasoroProblem.cardyV a t) (Ioi 0) := hg.int_cardy
  have hgv_int : IntegrableOn (fun t => g t * virasoroProblem.cardyV a t) (Ioi 0) :=
    hM_int.norm.mono'
      (((hg.cont.mul (continuous_cardyV virasoroProblem a).continuousOn).mono Ioi_subset_Ici_self)
        |>.aestronglyMeasurable measurableSet_Ioi)
      (Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_abs])
  have hg_int_le0 : ∫ t in Ioi 0, g t * virasoroProblem.cardyV a t ≤ 0 := by
    unfold FixedWeightProblem.gVac at hgVac
    nlinarith [Real.pi_pos]
  have hsplit_fun : ∀ f : ℝ → ℝ, IntegrableOn f (Ioi 0) →
      ∫ t in Ioi 0, f t = (∫ t in Ioc 0 T, f t) + (∫ t in Ioi T, f t) := fun f hf => by
    have hdisj : Disjoint (Ioc 0 T) (Ioi T) := Ioc_disjoint_Ioi_same
    have hunion : Ioc 0 T ∪ Ioi T = Ioi 0 := Ioc_union_Ioi_eq_Ioi hT
    rw [← hunion]
    exact setIntegral_union hdisj measurableSet_Ioi (hf.mono_set Ioc_subset_Ioi_self)
      (hf.mono_set (Ioi_subset_Ioi hT))
  have hsplit_gv := hsplit_fun (fun t => g t * virasoroProblem.cardyV a t) hgv_int
  have hsplit_M := hsplit_fun (fun t => |g t| * virasoroProblem.cardyV a t) hM_int
  have htail_eq : ∫ t in Ioi T, g t * virasoroProblem.cardyV a t =
      ∫ t in Ioi T, |g t| * virasoroProblem.cardyV a t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [abs_of_nonneg (hsign t (Set.mem_Ioi.mp ht).le)]
  have hhead_le : -(∫ t in Ioc 0 T, |g t| * virasoroProblem.cardyV a t) ≤
      ∫ t in Ioc 0 T, g t * virasoroProblem.cardyV a t := by
    rw [← integral_neg]
    refine setIntegral_mono_on (hM_int.mono_set Ioc_subset_Ioi_self).neg
      (hgv_int.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc fun t ht => ?_
    have hV : 0 ≤ virasoroProblem.cardyV a t := virasoroProblem.cardyV_nonneg ha ht.1.le
    calc -(|g t| * virasoroProblem.cardyV a t) = (-|g t|) * virasoroProblem.cardyV a t := by ring
      _ ≤ g t * virasoroProblem.cardyV a t :=
          mul_le_mul_of_nonneg_right (neg_abs_le (g t)) hV
  have htail_le_head : ∫ t in Ioi T, |g t| * virasoroProblem.cardyV a t ≤
      ∫ t in Ioc 0 T, |g t| * virasoroProblem.cardyV a t := by
    linarith [hsplit_gv, htail_eq, hhead_le, hg_int_le0]
  have hM_le : virasoroProblem.cardyNorm a g ≤
      2 * ∫ t in Ioc 0 T, |g t| * virasoroProblem.cardyV a t := by
    unfold FixedWeightProblem.cardyNorm
    linarith [hsplit_M, htail_le_head]
  rw [intervalIntegral.integral_of_le hT]
  linarith

/-- Bridge constructor: from a concrete weakly feasible Virasoro test
`virasoroProblem.IsWeaklyFeasible (c' / 12) T g` (with `0 ≤ T` and `24 ≤ c'`) and
a `VirasoroStripInput`, build a `WeaklyFeasibleTest input.toPoissonJensenInput input.fg c'`
with `t₁ = T`. -/
noncomputable def weaklyFeasibleTestOfConcrete (input : VirasoroStripInput)
    {c' T : ℝ} (hc' : 24 ≤ c') (hcPJ : input.c_PJ ≤ c') (hT : 0 ≤ T) {g : ℝ → ℝ}
    (hg : virasoroProblem.IsWeaklyFeasible (c' / 12) T g) :
    WeaklyFeasibleTest input.toPoissonJensenInput input.fg c' :=
  let a : ℝ := c' / 12
  have ha : virasoroProblem.totalShift ≤ a := by
    rw [virasoroProblem_totalShift]; dsimp [a]; linarith
  have ha2 : 2 ≤ a := by rwa [← virasoroProblem_totalShift]
  have hc'_pos : 0 < c' := by linarith
  have hM_pos : 0 < virasoroProblem.cardyNorm a g :=
    cardyNorm_pos_of_nonzero ha hg.1 hg.2.1
  { g := g
    V := virasoroProblem.cardyV a
    K_a := kernelK 1 a
    M := virasoroProblem.cardyNorm a g
    t₁ := T
    hM_pos := hM_pos
    ht₁_nonneg := hT
    hg_cont := hg.1.cont
    hV_cont := (continuous_cardyV virasoroProblem a).continuousOn
    hV_nonneg := fun _ ht => virasoroProblem.cardyV_nonneg ha ht
    hM_int := hg.1.int_cardy
    hM_eq := rfl
    hV_le_two_Ka := fun _ _ =>
      virasoro_cardyV_le_two_Ka ha2 (by positivity)
    hKa_ub := fun _ hx => virasoro_Ka_ub hc'_pos hx
    hPJ := fun x hx hne => input.hPJ hcPJ hg.1 hM_pos x hx hne
    hDeepLobe := fun hcd => input.hDeepLobe hcd hg.1
    hHalfMass := half_mass_of_weak_sign ha hT hg.1 hg.2.2.1 hg.2.2.2 }

/-! ### Theorem A for the real Virasoro crossing thresholds -/

/-- **Theorem A for `T_weak` (`log_free_optimality.tex`, Theorem A):**
Conditional on `VirasoroStripInput` (Lemma PJ and Lemma G), there exist absolute constants
`C_A > 0` and `c_A ≥ 24` such that `virasoroProblem.T_weak c' ≥ xiBar * c' - C_A * c'^{1/3}`
for every `c' ≥ c_A`. -/
theorem theorem_A_T_weak (input : VirasoroStripInput) :
    ∃ C_A c_A : ℝ, 0 < C_A ∧ 24 ≤ c_A ∧ ∀ {c' : ℝ}, c_A ≤ c' →
      xiBar * c' - C_A * c' ^ ((1 : ℝ) / 3) ≤ virasoroProblem.T_weak c' := by
  obtain ⟨C_A, c_A, hCA_pos, _, hthm⟩ := theorem_A input.toPoissonJensenInput input.fg
  refine ⟨C_A, max 24 (max input.c_PJ c_A), hCA_pos, le_max_left _ _, fun {c'} hc' => ?_⟩
  have hc24 : 24 ≤ c' := (le_max_left _ _).trans hc'
  have hcPJ : input.c_PJ ≤ c' := ((le_max_left _ _).trans (le_max_right _ _)).trans hc'
  have hcA : c_A ≤ c' := ((le_max_right _ _).trans (le_max_right _ _)).trans hc'
  have hshift : 12 * virasoroProblem.totalShift ≤ c' := by
    rw [virasoroProblem_totalShift]; linarith
  have hne : {T : ℝ | 0 < T ∧ ∃ g, virasoroProblem.IsWeaklyFeasible (c' / 12) T g}.Nonempty := by
    obtain ⟨T, hT, g, hg⟩ := virasoroProblem.feasible_nonempty hshift
    exact ⟨T, hT, g, hg.isWeaklyFeasible⟩
  unfold FixedWeightProblem.T_weak
  refine le_csInf hne ?_
  rintro T ⟨hT, g, hg⟩
  have hbound := hthm hcA (weaklyFeasibleTestOfConcrete input hc24 hcPJ hT.le hg)
  dsimp [weaklyFeasibleTestOfConcrete] at hbound
  exact hbound

/-- **Theorem A for `T_V` (`log_free_optimality.tex`, Theorem A; `modular_bootstrap_main.tex`):**
Conditional on `VirasoroStripInput` (Lemma PJ and Lemma G), there exist absolute constants
`C_A > 0` and `c_A ≥ 24` such that `virasoroProblem.T_V c' ≥ xiBar * c' - C_A * c'^{1/3}`
for every `c' ≥ c_A`. -/
theorem theorem_A_T_V (input : VirasoroStripInput) :
    ∃ C_A c_A : ℝ, 0 < C_A ∧ 24 ≤ c_A ∧ ∀ {c' : ℝ}, c_A ≤ c' →
      xiBar * c' - C_A * c' ^ ((1 : ℝ) / 3) ≤ virasoroProblem.T_V c' := by
  obtain ⟨C_A, c_A, hCA_pos, hc24, hweak⟩ := theorem_A_T_weak input
  refine ⟨C_A, c_A, hCA_pos, hc24, fun {c'} hc' => ?_⟩
  have hshift : 12 * virasoroProblem.totalShift ≤ c' := by
    rw [virasoroProblem_totalShift]; linarith [hc24.trans hc']
  exact (hweak hc').trans (virasoroProblem.T_weak_le_T_V hshift)

/-- **Theorem A for `Delta_best`:** `Delta_best(c') ≥ c' / lambdaV - C_A * c'^{1/3}` for `c' ≥ c_A`.
Conditional on `VirasoroStripInput`. -/
theorem theorem_A_Delta_best (input : VirasoroStripInput) :
    ∃ C_A c_A : ℝ, 0 < C_A ∧ 24 ≤ c_A ∧ ∀ {c' : ℝ}, c_A ≤ c' →
      c' / lambdaV - C_A * c' ^ ((1 : ℝ) / 3) ≤ virasoroProblem.Delta_best c' := by
  obtain ⟨C_A, c_A, hCA_pos, hc24, hTV⟩ := theorem_A_T_V input
  refine ⟨C_A, c_A, hCA_pos, hc24, fun {c'} hc' => ?_⟩
  unfold FixedWeightProblem.Delta_best
  have hxi : c' / lambdaV = c' / 12 + xiBar * c' := by
    rw [xiBar_eq_inv_lambdaV_sub]; ring
  linarith [hTV hc']

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Crossing.virasoro_Ka_ub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.virasoro_Ka_ub

/-- info: 'FormalResearch.ModularBootstrap.Crossing.virasoroStripParams_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.virasoroStripParams_nonvacuous

/-- info: 'FormalResearch.ModularBootstrap.Crossing.weaklyFeasibleTestOfConcrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.weaklyFeasibleTestOfConcrete

/-- info: 'FormalResearch.ModularBootstrap.Crossing.theorem_A_T_weak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.theorem_A_T_weak

/-- info: 'FormalResearch.ModularBootstrap.Crossing.theorem_A_T_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.theorem_A_T_V

/-- info: 'FormalResearch.ModularBootstrap.Crossing.theorem_A_Delta_best' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Crossing.theorem_A_Delta_best

end FormalResearch.ModularBootstrap.Crossing
