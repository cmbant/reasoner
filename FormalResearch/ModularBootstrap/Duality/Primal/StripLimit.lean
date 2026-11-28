module

public import FormalResearch.ModularBootstrap.Duality.Primal.FixedCharge
public import FormalResearch.ModularBootstrap.Duality.Primal.CompactMass
public import FormalResearch.ModularBootstrap.Duality.Primal.HankelLimit
public import FormalResearch.Complex.Montel

/-!
# The Montel limit of a normalised minimising sequence (`ds:primal`, `dual_spectrum_limit.tex`)

For a normalised sequence `g_j ∈ Ā_w` (`M[g_j] = 1`, `∫ g_j V ≤ 0`, `g_j ≥ 0` on `[R₀, ∞)`), the
Hankel continuations `G_j(b) = g_j(c̃ b² / 3)` are uniformly bounded on the strip `|Im b| ≤ 1/2`
at every fixed charge `c̃ > 0`, `12 S ≤ c̃` (`dsl:strip-fixed`(a)), so Montel gives a locally
uniformly convergent subsequence on `|Im b| < 1/2`.
The limit `g_*(t) = G(√(3t/c̃))` is continuous with locally finite zero set (identity theorem), and
`dsl:compact-mass` gives `g_* ≠ 0`, `M[g_*] ≤ 1`, `g_{*,vac} ≥ 0`; the tail estimate
`t^{w-1} ≤ ε V` gives convergence in `L¹(t^{w-1} dt)`, hence `g_* ∈ Ā_w`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Complex
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeight

open Crossing WeightAxioms

/-- The open strip `|Im b| < 1/2`. -/
def openStrip : Set ℂ := {b : ℂ | |b.im| < 1 / 2}

lemma isOpen_openStrip : IsOpen openStrip :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

lemma isPreconnected_openStrip : IsPreconnected openStrip := by
  have : openStrip = Complex.im ⁻¹' Ioo (-(1 / 2) : ℝ) (1 / 2) := by
    ext b; simp [openStrip, abs_lt]
  rw [this]
  exact ((convex_Ioo (-(1 / 2) : ℝ) (1 / 2)).linear_preimage Complex.imLm).isPreconnected

/-- The real coordinate `b(t) = √(3t/c̃)`. -/
noncomputable def stripCoord (cTilde t : ℝ) : ℝ := Real.sqrt (3 * t / cTilde)

lemma stripCoord_sq {cTilde t : ℝ} (hc : 0 < cTilde) (ht : 0 ≤ t) :
    cTilde * stripCoord cTilde t ^ 2 / 3 = t := by
  unfold stripCoord
  rw [Real.sq_sqrt (by positivity)]
  field_simp

section Montel

variable {prob : FixedWeightProblem} {cTilde : ℝ}

/-- On the real axis the Hankel continuation is the function itself. -/
lemma hankel_ofReal_testClass (hc : 0 < cTilde) {g : ℝ → ℝ} (hg : TestClass prob (cTilde / 12) g)
    (b : ℝ) : hankelContinuationW prob.w cTilde g (b : ℂ) = (g (cTilde * b ^ 2 / 3) : ℂ) :=
  hankelContinuationW_ofReal prob.hw hc hg.cont hg.int_lift hg.fourier_odd b

/-- **Montel step**: for a normalised sequence there is a subsequence whose Hankel continuations
converge locally uniformly on the open strip to a holomorphic `G`. -/
theorem exists_montel_limit (hc_pos : 0 < cTilde) (hc : 12 * prob.totalShift ≤ cTilde)
    {g : ℕ → ℝ → ℝ} (hg : ∀ j, TestClass prob (cTilde / 12) (g j))
    (hM : ∀ j, prob.cardyNorm (cTilde / 12) (g j) = 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℂ → ℂ, DifferentiableOn ℂ G openStrip ∧
      TendstoLocallyUniformlyOn (fun k => hankelContinuationW prob.w cTilde (g (φ k))) G atTop
        openStrip := by
  obtain ⟨C, _, hC⟩ := hankelContinuationW_strip_bound_fixed prob hc_pos hc
  refine FormalResearch.Montel.montel isOpen_openStrip
    (fun j => differentiableOn_hankelContinuationW_fixed prob hc_pos hc (hg j)) ?_
  intro K hK _
  refine ⟨2 * π * C, fun j z hz => ?_⟩
  have := hC (hg j) (le_of_lt (hK hz))
  rwa [hM j, mul_one] at this

/-- The limit function `g_*(t) = Re G(√(3t/c̃))`. -/
noncomputable def limitFn (cTilde : ℝ) (G : ℂ → ℂ) (t : ℝ) : ℝ := (G (stripCoord cTilde t : ℂ)).re

lemma continuous_stripCoord (cTilde : ℝ) : Continuous (stripCoord cTilde) := by
  unfold stripCoord
  exact Real.continuous_sqrt.comp (by fun_prop)

lemma stripCoord_mem (cTilde : ℝ) (t : ℝ) : ((stripCoord cTilde t : ℝ) : ℂ) ∈ openStrip := by
  simp [openStrip]

lemma continuous_limitFn {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G openStrip) (cTilde : ℝ) :
    Continuous (limitFn cTilde G) := by
  unfold limitFn
  refine Complex.continuous_re.comp ?_
  have hc : ContinuousOn G openStrip := hG.continuousOn
  exact hc.comp_continuous (Complex.continuous_ofReal.comp (continuous_stripCoord cTilde))
    (fun t => stripCoord_mem cTilde t)

/-- Uniform convergence of the subsequence on every `[0, R]`, and reality of the limit on the real
axis. -/
theorem limit_converges (hc : 0 < cTilde) {g : ℕ → ℝ → ℝ}
    (hg : ∀ j, TestClass prob (cTilde / 12) (g j)) {φ : ℕ → ℕ} {G : ℂ → ℂ}
    (hTLU : TendstoLocallyUniformlyOn (fun k => hankelContinuationW prob.w cTilde (g (φ k))) G atTop
      openStrip) :
    (∀ R : ℝ, TendstoUniformlyOn (fun k => g (φ k)) (limitFn cTilde G) atTop (Icc 0 R)) ∧
    (∀ t : ℝ, 0 ≤ t → G (stripCoord cTilde t : ℂ) = (limitFn cTilde G t : ℂ)) := by
  have hGk : ∀ k t, 0 ≤ t → hankelContinuationW prob.w cTilde (g (φ k)) (stripCoord cTilde t : ℂ) =
      (g (φ k) t : ℂ) := fun k t ht => by
    rw [hankel_ofReal_testClass hc (hg (φ k)), stripCoord_sq hc ht]
  refine ⟨fun R => ?_, fun t ht => ?_⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set Kc : Set ℂ := (fun t : ℝ => ((stripCoord cTilde t : ℝ) : ℂ)) '' Icc 0 R with hKc
    have hKc_cpt : IsCompact Kc :=
      isCompact_Icc.image (Complex.continuous_ofReal.comp (continuous_stripCoord cTilde))
    have hKc_sub : Kc ⊆ openStrip := by
      rintro _ ⟨t, -, rfl⟩; exact stripCoord_mem cTilde t
    have hunif := ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_openStrip).1 hTLU) Kc hKc_sub
      hKc_cpt
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif ε hε] with k hk t ht
    have h1 := hk _ ⟨t, ht, rfl⟩
    rw [hGk k t ht.1, dist_eq_norm] at h1
    rw [Real.dist_eq]
    have : |limitFn cTilde G t - g (φ k) t| ≤ ‖G (stripCoord cTilde t : ℂ) - (g (φ k) t : ℂ)‖ := by
      have := Complex.abs_re_le_norm (G (stripCoord cTilde t : ℂ) - (g (φ k) t : ℂ))
      simpa [limitFn] using this
    exact lt_of_le_of_lt this h1
  · -- the limit is real on the real axis
    have hb := stripCoord_mem cTilde t
    have hlim : Tendsto (fun k => hankelContinuationW prob.w cTilde (g (φ k)) (stripCoord cTilde t : ℂ))
        atTop (𝓝 (G (stripCoord cTilde t : ℂ))) := hTLU.tendsto_at hb
    have him : Tendsto (fun k => (hankelContinuationW prob.w cTilde (g (φ k))
        (stripCoord cTilde t : ℂ)).im) atTop (𝓝 (G (stripCoord cTilde t : ℂ)).im) :=
      (Complex.continuous_im.tendsto _).comp hlim
    have h0 : ∀ k, (hankelContinuationW prob.w cTilde (g (φ k)) (stripCoord cTilde t : ℂ)).im = 0 :=
      fun k => by rw [hGk k t ht]; simp
    have : (G (stripCoord cTilde t : ℂ)).im = 0 := by
      refine tendsto_nhds_unique him ?_
      simp_rw [h0]; exact tendsto_const_nhds
    apply Complex.ext <;> simp [limitFn, this]

/-- The zero set of a nonzero limit is locally finite (identity theorem on the strip). -/
theorem limitFn_zeros_finite (hc : 0 < cTilde) {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G openStrip)
    (hreal : ∀ t : ℝ, 0 ≤ t → G (stripCoord cTilde t : ℂ) = (limitFn cTilde G t : ℂ))
    (hne : ∃ t : ℝ, 0 ≤ t ∧ limitFn cTilde G t ≠ 0) (R : ℝ) :
    {t ∈ Icc (0 : ℝ) R | limitFn cTilde G t = 0}.Finite := by
  by_contra hinf
  set Z : Set ℝ := {t ∈ Icc (0 : ℝ) R | limitFn cTilde G t = 0} with hZ
  set Z' : Set ℂ := (fun t : ℝ => ((stripCoord cTilde t : ℝ) : ℂ)) '' Z with hZ'
  have hinj : InjOn (fun t : ℝ => ((stripCoord cTilde t : ℝ) : ℂ)) Z := by
    intro t₁ h₁ t₂ h₂ h
    have hb : stripCoord cTilde t₁ = stripCoord cTilde t₂ := by
      have h' : ((stripCoord cTilde t₁ : ℝ) : ℂ) = ((stripCoord cTilde t₂ : ℝ) : ℂ) := h
      exact_mod_cast h'
    have e1 := stripCoord_sq hc h₁.1.1
    have e2 := stripCoord_sq hc h₂.1.1
    rw [← e1, ← e2, hb]
  have hZ'inf : Z'.Infinite := (Set.Infinite.image hinj hinf)
  have hKc : IsCompact ((fun t : ℝ => ((stripCoord cTilde t : ℝ) : ℂ)) '' Icc 0 R) :=
    isCompact_Icc.image (Complex.continuous_ofReal.comp (continuous_stripCoord cTilde))
  have hsub : Z' ⊆ (fun t : ℝ => ((stripCoord cTilde t : ℝ) : ℂ)) '' Icc 0 R :=
    image_mono (fun t ht => ht.1)
  obtain ⟨b₀, hb₀K, hacc⟩ := hZ'inf.exists_accPt_of_subset_isCompact hKc hsub
  have hb₀U : b₀ ∈ openStrip := by
    obtain ⟨t, -, rfl⟩ := hb₀K; exact stripCoord_mem cTilde t
  have hGan : AnalyticOnNhd ℂ G openStrip := hG.analyticOnNhd isOpen_openStrip
  have hzero : ∀ z ∈ Z', G z = 0 := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hreal t ht.1.1]; simp [ht.2]
  have hfreq : ∃ᶠ z in 𝓝[≠] b₀, G z = 0 := by
    have := accPt_iff_frequently_nhdsNE.1 hacc
    exact this.mono fun z hz => hzero z hz
  have hat : AnalyticAt ℂ G b₀ := hGan b₀ hb₀U
  have hev : ∀ᶠ z in 𝓝 b₀, G z = 0 := hat.frequently_zero_iff_eventually_zero.1 hfreq
  have hall : EqOn G 0 openStrip :=
    hGan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_openStrip hb₀U hev
  obtain ⟨t, ht0, htne⟩ := hne
  have := hall (stripCoord_mem cTilde t)
  rw [Pi.zero_apply, hreal t ht0] at this
  exact htne (by exact_mod_cast this)

end Montel

section Mass

/-- `dsl:compact-mass` for the weighted measure `V(t) dt` on `(0, ∞)`: the functions
`f_j = g_j V` (extended by `0` to `t < 0`) satisfy its hypotheses. -/
theorem limit_mass {V : ℝ → ℝ} (hV : Continuous V) (hV0 : ∀ t, 0 ≤ V t) {g : ℕ → ℝ → ℝ}
    {gs : ℝ → ℝ} {R₀ : ℝ} (hgc : ∀ j, ContinuousOn (g j) (Ici 0)) (_hgs : ContinuousOn gs (Ici 0))
    (hint : ∀ j, IntegrableOn (fun t => |g j t| * V t) (Ioi 0))
    (hM : ∀ j, ∫ t in Ioi (0 : ℝ), |g j t| * V t = 1)
    (hv : ∀ j, ∫ t in Ioi (0 : ℝ), g j t * V t ≤ 0) (hneg : ∀ j, ∀ t ≥ R₀, 0 ≤ g j t)
    (hunif : ∀ R : ℝ, TendstoUniformlyOn g gs atTop (Icc 0 R)) :
    IntegrableOn (fun t => |gs t| * V t) (Ioi 0) ∧ ∫ t in Ioi (0 : ℝ), |gs t| * V t ≤ 1 ∧
      ∫ t in Ioi (0 : ℝ), gs t * V t ≤ 0 ∧ (∃ t : ℝ, 0 ≤ t ∧ gs t ≠ 0) ∧
      (0 ≤ ∫ t in Ioi (0 : ℝ), gs t * V t → ∫ t in Ioi (0 : ℝ), |gs t| * V t = 1 ∧
        Tendsto (fun j => ∫ t in Ioi (0 : ℝ), |g j t - gs t| * V t) atTop (𝓝 0)) := by
  classical
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  let ext : (ℝ → ℝ) → ℝ → ℝ := fun h t => (Ici (0 : ℝ)).indicator (fun s => h (max s 0) * V (max s 0)) t
  have hext_eq : ∀ (h : ℝ → ℝ) t, 0 ≤ t → ext h t = h t * V t := fun h t ht => by
    simp [ext, indicator_of_mem (mem_Ici.2 ht), max_eq_left ht]
  have hext_neg : ∀ (h : ℝ → ℝ) t, t < 0 → ext h t = 0 := fun h t ht => by
    simp [ext, indicator_of_notMem (show t ∉ Ici (0 : ℝ) from fun h' => absurd (mem_Ici.1 h') (not_le.2 ht))]
  have hext_meas : ∀ h : ℝ → ℝ, ContinuousOn h (Ici 0) → Measurable (ext h) := fun h hh => by
    refine (Measurable.indicator ?_ measurableSet_Ici)
    have : Continuous fun s : ℝ => h (max s 0) :=
      hh.comp_continuous (continuous_id.max continuous_const) fun s => mem_Ici.2 (le_max_right _ _)
    exact (this.mul (hV.comp (continuous_id.max continuous_const))).measurable
  have hext_cont : ∀ h : ℝ → ℝ, ContinuousOn h (Ici 0) → ContinuousOn (ext h) (Ici 0) := fun h hh => by
    refine ((hh.mul hV.continuousOn).congr ?_)
    intro t ht; exact hext_eq h t ht
  have hext_int : ∀ h : ℝ → ℝ, ∫ t, |ext h t| ∂μ = ∫ t in Ioi (0 : ℝ), |h t| * V t := fun h => by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [hext_eq h t (le_of_lt ht), abs_mul, abs_of_nonneg (hV0 t)]
  have hext_int' : ∀ h : ℝ → ℝ, ∫ t, ext h t ∂μ = ∫ t in Ioi (0 : ℝ), h t * V t := fun h => by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    exact hext_eq h t (le_of_lt ht)
  have hae_pos : ∀ᵐ t ∂μ, 0 < t := by
    rw [hμ]; exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ht
  have habs_ae : ∀ h : ℝ → ℝ, (fun t => |ext h t|) =ᵐ[μ] fun t => |h t| * V t := fun h => by
    filter_upwards [hae_pos] with t ht
    rw [hext_eq h t ht.le, abs_mul, abs_of_nonneg (hV0 t)]
  have hint_ext : ∀ h : ℝ → ℝ, ContinuousOn h (Ici 0) → IntegrableOn (fun t => |h t| * V t) (Ioi 0) →
      Integrable (ext h) μ := fun h hh hi => by
    refine Integrable.mono' (g := fun t => |h t| * V t) hi (hext_meas h hh).aestronglyMeasurable ?_
    filter_upwards [habs_ae h] with t ht
    rw [Real.norm_eq_abs, ht]
  -- bound of `V` on `[0, R₀]`
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := max R₀ 0)).exists_bound_of_continuousOn hV.continuousOn
  have hB0 : ∀ t ∈ Icc (0 : ℝ) (max R₀ 0), V t ≤ max B 1 := fun t ht => by
    have := hB t ht; rw [Real.norm_eq_abs, abs_of_nonneg (hV0 t)] at this
    exact this.trans (le_max_left _ _)
  have hunifK : TendstoUniformlyOn (fun j => ext (g j)) (ext gs) atTop (Icc 0 R₀) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hBpos : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hunif (max R₀ 0)) (ε / max B 1) (by positivity)]
      with j hj t ht
    have ht0 : 0 ≤ t := ht.1
    have htR : t ∈ Icc (0 : ℝ) (max R₀ 0) := ⟨ht0, ht.2.trans (le_max_left _ _)⟩
    rw [hext_eq _ t ht0, hext_eq _ t ht0, Real.dist_eq, ← sub_mul, abs_mul, abs_of_nonneg (hV0 t)]
    have h1 := hj t htR
    rw [Real.dist_eq] at h1
    calc |gs t - g j t| * V t ≤ |gs t - g j t| * max B 1 :=
          mul_le_mul_of_nonneg_left (hB0 t htR) (abs_nonneg _)
      _ < ε / max B 1 * max B 1 := mul_lt_mul_of_pos_right h1 hBpos
      _ = ε := by field_simp
  have hpt : ∀ y, Tendsto (fun j => ext (g j) y) atTop (𝓝 (ext gs y)) := fun y => by
    rcases le_or_gt 0 y with hy | hy
    · simp_rw [hext_eq _ y hy]
      exact ((hunif y).tendsto_at ⟨hy, le_rfl⟩).mul_const (V y)
    · simp_rw [hext_neg _ y hy]; exact tendsto_const_nhds
  obtain ⟨hFi, hF1, hF0, ⟨y, hy⟩, hrest⟩ := Duality.compact_negative_mass (μ := μ) (f := fun j => ext (g j))
    (F := ext gs) (K := Icc 0 R₀) isCompact_Icc (fun j => hext_meas _ (hgc j))
    (fun j => (hext_cont _ (hgc j)).mono Icc_subset_Ici_self)
    (fun j => hint_ext _ (hgc j) (hint j))
    (fun j => by rw [hext_int, hM j]) (fun j => by rw [hext_int']; exact hv j)
    (fun j t ht => by
      rcases lt_or_ge t 0 with h | h
      · rw [hext_neg _ t h]
      · have hR : R₀ < t := lt_of_not_ge fun h' => ht ⟨h, h'⟩
        rw [hext_eq _ t h]
        exact mul_nonneg (hneg j t hR.le) (hV0 t))
    hpt hunifK
  have hgs_int : IntegrableOn (fun t => |gs t| * V t) (Ioi 0) := by
    have := hFi.norm
    refine this.congr ?_
    filter_upwards [habs_ae gs] with t ht using by rw [Real.norm_eq_abs, ht]
  refine ⟨hgs_int, by rw [← hext_int]; exact hF1, by rw [← hext_int']; exact hF0, ?_, fun h0 => ?_⟩
  · refine ⟨y, ?_, ?_⟩
    · by_contra hneg'
      rw [hext_neg _ y (not_le.1 hneg')] at hy; exact lt_irrefl _ hy
    · intro hz
      have hy0 : 0 ≤ y := by
        by_contra hneg'
        rw [hext_neg _ y (not_le.1 hneg')] at hy; exact lt_irrefl _ hy
      rw [hext_eq _ y hy0, hz, zero_mul] at hy; exact lt_irrefl _ hy
  · rw [← hext_int'] at h0
    obtain ⟨-, h2, h3⟩ := hrest h0
    refine ⟨by rw [← hext_int]; exact h2, ?_⟩
    refine h3.congr fun j => ?_
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 ≤ t := le_of_lt ht
    simp only [hext_eq _ t ht0, ← sub_mul, abs_mul, abs_of_nonneg (hV0 t)]

/-- **`L¹(t^{w-1} dt)` control from the weighted bound** (`t^{w-1} ≤ ε V` at infinity): `t^{w-1} g_* ∈ L¹`
and `g_j → g_*` in `L¹((0, ∞), t^{w-1} dt)`. -/
theorem l1_tail_limit {V : ℝ → ℝ} (hV : Continuous V) (hV0 : ∀ t, 0 ≤ V t) {w : ℕ} (hw : 1 ≤ w)
    (hVtail : ∀ ε > 0, ∃ R : ℝ, ∀ t ≥ R, t ^ (w - 1) ≤ ε * V t) {g : ℕ → ℝ → ℝ} {gs : ℝ → ℝ}
    (hgc : ∀ j, ContinuousOn (g j) (Ici 0)) (hgs : ContinuousOn gs (Ici 0))
    (hint : ∀ j, IntegrableOn (fun t => |g j t| * V t) (Ioi 0))
    (hM : ∀ j, ∫ t in Ioi (0 : ℝ), |g j t| * V t ≤ 1)
    (hsint : IntegrableOn (fun t => |gs t| * V t) (Ioi 0))
    (hsM : ∫ t in Ioi (0 : ℝ), |gs t| * V t ≤ 1)
    (hunif : ∀ R : ℝ, TendstoUniformlyOn g gs atTop (Icc 0 R)) :
    IntegrableOn (fun t => t ^ (w - 1) * gs t) (Ioi 0) ∧
      Tendsto (fun j => ∫ t in Ioi (0 : ℝ), t ^ (w - 1) * |g j t - gs t|) atTop (𝓝 0) := by
  -- integrability of `t^{w-1} gs` on `(0, R]` and on `(R, ∞)`
  have hcont_pow : ∀ (h : ℝ → ℝ), ContinuousOn h (Ici 0) →
      ContinuousOn (fun t => t ^ (w - 1) * h t) (Ici 0) := fun h hh =>
    (continuousOn_id.pow _).mul hh
  have hIoc : ∀ (h : ℝ → ℝ), ContinuousOn h (Ici 0) → ∀ R : ℝ,
      IntegrableOn (fun t => t ^ (w - 1) * |h t|) (Ioc 0 R) := fun h hh R => by
    have : ContinuousOn (fun t => t ^ (w - 1) * |h t|) (Icc 0 R) :=
      ((continuousOn_id.pow _).mul hh.abs).mono Icc_subset_Ici_self
    exact (this.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hIoi : ∀ (h : ℝ → ℝ), ContinuousOn h (Ici 0) → IntegrableOn (fun t => |h t| * V t) (Ioi 0) →
      ∀ R : ℝ, 0 ≤ R → ∀ ε > 0, (∀ t ≥ R, t ^ (w - 1) ≤ ε * V t) →
        IntegrableOn (fun t => t ^ (w - 1) * |h t|) (Ioi R) := fun h hh hi R hR ε hε hR' => by
    refine Integrable.mono' (g := fun t => ε * (|h t| * V t))
      ((hi.mono_set (Ioi_subset_Ioi hR)).const_mul ε) ?_ ?_
    · exact (((continuousOn_id.pow (w - 1)).mul hh.abs).mono
        (Ioi_subset_Ici_self.trans (Ici_subset_Ici.2 hR))).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      have ht0 : 0 ≤ t ^ (w - 1) := pow_nonneg (hR.trans (le_of_lt ht)) _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht0, abs_abs]
      calc t ^ (w - 1) * |h t| ≤ ε * V t * |h t| :=
            mul_le_mul_of_nonneg_right (hR' t (le_of_lt ht)) (abs_nonneg _)
        _ = ε * (|h t| * V t) := by ring
  have hIoc' : ∀ (h : ℝ → ℝ), ContinuousOn h (Ici 0) → IntegrableOn (fun t => |h t| * V t) (Ioi 0) →
      ∀ R : ℝ, 1 ≤ R → ∀ ε > 0, (∀ t ≥ R, t ^ (w - 1) ≤ ε * V t) →
        IntegrableOn (fun t => t ^ (w - 1) * |h t|) (Ioi 0) := fun h hh hi R hR ε hε hR' => by
    have h1 := hIoc h hh R
    have h2 := hIoi h hh hi R (by linarith) ε hε hR'
    have := h1.union h2
    rwa [Ioc_union_Ioi_eq_Ioi (by linarith)] at this
  -- integrability of the differences
  have hdiff_int : ∀ j, IntegrableOn (fun t => |g j t - gs t| * V t) (Ioi 0) := fun j => by
    refine Integrable.mono' (g := fun t => |g j t| * V t + |gs t| * V t) ((hint j).add hsint) ?_ ?_
    · exact ((((hgc j).sub hgs).abs.mono Ioi_subset_Ici_self).mul
        hV.continuousOn).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (hV0 t)]
      have := abs_sub (g j t) (gs t)
      nlinarith [hV0 t, abs_nonneg (g j t), abs_nonneg (gs t), mul_le_mul_of_nonneg_right this (hV0 t)]
  obtain ⟨R₁, hR₁⟩ := hVtail 1 one_pos
  have hR₁' : ∀ t ≥ max R₁ 1, t ^ (w - 1) ≤ 1 * V t := fun t ht => hR₁ t ((le_max_left _ _).trans ht)
  have hsI : IntegrableOn (fun t => t ^ (w - 1) * |gs t|) (Ioi 0) :=
    hIoc' gs hgs hsint (max R₁ 1) (le_max_right _ _) 1 one_pos hR₁'
  refine ⟨?_, ?_⟩
  · refine Integrable.mono' hsI ?_ ?_
    · exact ((continuousOn_id.pow _).mul hgs |>.mono Ioi_subset_Ici_self).aestronglyMeasurable
        measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
      have ht0 : 0 ≤ t ^ (w - 1) := pow_nonneg (le_of_lt ht) _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht0]
  · rw [Metric.tendsto_nhds]
    intro ε hε
    set η : ℝ := ε / 2 with hη
    obtain ⟨R₂, hR₂⟩ := hVtail (η / 4) (by positivity)
    set R : ℝ := max R₂ 1 with hR
    have hR1 : 1 ≤ R := le_max_right _ _
    have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
    have hR₂' : ∀ t ≥ R, t ^ (w - 1) ≤ η / 4 * V t := fun t ht => hR₂ t ((le_max_left _ _).trans ht)
    set δ : ℝ := η / (2 * R ^ w) with hδ
    have hδ0 : 0 < δ := by positivity
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hunif R) δ hδ0] with j hj
    rw [Real.dist_eq, sub_zero]
    have hJ_nn : 0 ≤ ∫ t in Ioi (0 : ℝ), t ^ (w - 1) * |g j t - gs t| :=
      setIntegral_nonneg measurableSet_Ioi fun t ht => by
        have : 0 ≤ t ^ (w - 1) := pow_nonneg (le_of_lt ht) _
        positivity
    rw [abs_of_nonneg hJ_nn]
    have hdc : ContinuousOn (fun t => g j t - gs t) (Ici 0) := (hgc j).sub hgs
    have hI1 := hIoc (fun t => g j t - gs t) hdc R
    have hI2 := hIoi (fun t => g j t - gs t) hdc (hdiff_int j) R hR0.le (η / 4) (by positivity) hR₂'
    rw [← Ioc_union_Ioi_eq_Ioi hR0.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hI1 hI2]
    -- the two pieces
    have hpiece1 : ∫ t in Ioc 0 R, t ^ (w - 1) * |g j t - gs t| ≤ δ * R ^ w := by
      have hb : ∀ t ∈ Ioc (0 : ℝ) R, t ^ (w - 1) * |g j t - gs t| ≤ R ^ (w - 1) * δ := fun t ht => by
        have h1 : t ^ (w - 1) ≤ R ^ (w - 1) := pow_le_pow_left₀ ht.1.le ht.2 _
        have h2 : |g j t - gs t| ≤ δ := by
          have := hj t ⟨ht.1.le, ht.2⟩
          rw [Real.dist_eq, abs_sub_comm] at this; exact this.le
        exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      calc ∫ t in Ioc 0 R, t ^ (w - 1) * |g j t - gs t|
          ≤ ∫ _t in Ioc (0 : ℝ) R, R ^ (w - 1) * δ :=
            setIntegral_mono_on hI1 (integrableOn_const (by simp)) measurableSet_Ioc hb
        _ = δ * R ^ w := by
            rw [setIntegral_const, Real.volume_real_Ioc_of_le hR0.le]
            simp only [smul_eq_mul, sub_zero]
            have : R ^ w = R ^ (w - 1) * R := by
              rw [← pow_succ]; congr 1; omega
            rw [this]; ring
    have hnn_g : ∀ (h : ℝ → ℝ), 0 ≤ᵐ[volume.restrict (Ioi R)] fun t => |h t| * V t := fun h =>
      Eventually.of_forall fun t => mul_nonneg (abs_nonneg _) (hV0 t)
    have hpiece2 : ∫ t in Ioi R, t ^ (w - 1) * |g j t - gs t| ≤ η / 2 := by
      have hRsub : Ioi R ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi hR0.le
      have hgj : ∫ t in Ioi R, |g j t| * V t ≤ 1 :=
        (setIntegral_mono_set (hint j) (Eventually.of_forall fun t => mul_nonneg (abs_nonneg _) (hV0 t))
          (Eventually.of_forall hRsub)).trans (hM j)
      have hgsR : ∫ t in Ioi R, |gs t| * V t ≤ 1 :=
        (setIntegral_mono_set hsint (Eventually.of_forall fun t => mul_nonneg (abs_nonneg _) (hV0 t))
          (Eventually.of_forall hRsub)).trans hsM
      have hrhs : IntegrableOn (fun t => η / 4 * (|g j t| * V t + |gs t| * V t)) (Ioi R) :=
        (((hint j).mono_set hRsub).add (hsint.mono_set hRsub)).const_mul _
      calc ∫ t in Ioi R, t ^ (w - 1) * |g j t - gs t|
          ≤ ∫ t in Ioi R, η / 4 * (|g j t| * V t + |gs t| * V t) := by
            refine setIntegral_mono_on hI2 hrhs measurableSet_Ioi fun t ht => ?_
            have ht' : R ≤ t := le_of_lt ht
            have h1 := hR₂' t ht'
            have h2 := abs_sub (g j t) (gs t)
            have h3 : 0 ≤ V t := hV0 t
            have h4 : 0 ≤ |g j t - gs t| := abs_nonneg _
            nlinarith [mul_le_mul h1 h2 h4 (by positivity), mul_nonneg h3 (abs_nonneg (g j t)),
              mul_nonneg h3 (abs_nonneg (gs t))]
        _ = η / 4 * ((∫ t in Ioi R, |g j t| * V t) + ∫ t in Ioi R, |gs t| * V t) := by
            rw [integral_const_mul, integral_add ((hint j).mono_set hRsub) (hsint.mono_set hRsub)]
        _ ≤ η / 4 * (1 + 1) := mul_le_mul_of_nonneg_left (add_le_add hgj hgsR) (by positivity)
        _ = η / 2 := by ring
    have hδR : δ * R ^ w = η / 2 := by
      rw [hδ]; field_simp
    linarith

end Mass

section Assembly

variable {prob : FixedWeightProblem} {cTilde : ℝ}

/-- **The Montel limit of a normalised sequence** (`ds:primal`, proof of (a)): for
`g_j ∈ Ā_w` with `M[g_j] = 1`, `∫ g_j V ≤ 0` and `g_j ≥ 0` on `[R₀, ∞)`, a subsequence converges
locally uniformly on `[0, ∞)` to a `g_* ∈ Ā_w` with `g_* ≥ 0` on `[R₀, ∞)`, `g_* ≠ 0`, `M[g_*] ≤ 1`,
`g_{*,vac} ≥ 0` and locally finite zero set; if moreover `g_{*,vac} ≤ 0` then `M[g_*] = 1` and
`g_{φ(k)} → g_*` in `M`. -/
theorem exists_primal_limit (hc_pos : 0 < cTilde) (hc : 12 * prob.totalShift ≤ cTilde)
    {g : ℕ → ℝ → ℝ} (hg : ∀ j, TestClass prob (cTilde / 12) (g j))
    (hM : ∀ j, prob.cardyNorm (cTilde / 12) (g j) = 1)
    (hv : ∀ j, ∫ t in Ioi (0 : ℝ), g j t * prob.cardyV (cTilde / 12) t ≤ 0) {R₀ : ℝ}
    (hR₀ : 0 ≤ R₀) (hneg : ∀ j, ∀ t ≥ R₀, 0 ≤ g j t) :
    ∃ (φ : ℕ → ℕ) (gs : ℝ → ℝ), StrictMono φ ∧ TestClass prob (cTilde / 12) gs ∧
      (∀ t ≥ R₀, 0 ≤ gs t) ∧
      (∀ R : ℝ, TendstoUniformlyOn (fun k => g (φ k)) gs atTop (Icc 0 R)) ∧
      prob.cardyNorm (cTilde / 12) gs ≤ 1 ∧ 0 ≤ prob.gVac (cTilde / 12) gs ∧
      (∃ t : ℝ, 0 ≤ t ∧ gs t ≠ 0) ∧ (∀ R : ℝ, {t ∈ Icc (0 : ℝ) R | gs t = 0}.Finite) ∧
      (∃ G : ℂ → ℂ, DifferentiableOn ℂ G openStrip ∧
        ∀ t : ℝ, 0 ≤ t → G (stripCoord cTilde t : ℂ) = (gs t : ℂ)) ∧
      (prob.gVac (cTilde / 12) gs ≤ 0 → prob.cardyNorm (cTilde / 12) gs = 1 ∧
        Tendsto (fun k => ∫ t in Ioi (0 : ℝ), |g (φ k) t - gs t| * prob.cardyV (cTilde / 12) t)
          atTop (𝓝 0)) := by
  have ha : prob.totalShift ≤ cTilde / 12 := by linarith
  set a : ℝ := cTilde / 12 with ha_def
  -- the weight, extended by its value at `0` to negative `t`
  set Vt : ℝ → ℝ := fun t => prob.cardyV a (max t 0) with hVt
  have hVt_cont : Continuous Vt :=
    (continuous_cardyV prob a).comp (continuous_id.max continuous_const)
  have hVt0 : ∀ t, 0 ≤ Vt t := fun t => prob.cardyV_nonneg ha (le_max_right _ _)
  have hVt_eq : ∀ t, 0 ≤ t → Vt t = prob.cardyV a t := fun t ht => by simp [hVt, max_eq_left ht]
  have hcongr : ∀ F : ℝ → ℝ, ∫ t in Ioi (0 : ℝ), F t * Vt t = ∫ t in Ioi (0 : ℝ), F t * prob.cardyV a t :=
    fun F => setIntegral_congr_fun measurableSet_Ioi fun t ht => by rw [hVt_eq t (le_of_lt ht)]
  have hcongrI : ∀ F : ℝ → ℝ, IntegrableOn (fun t => F t * Vt t) (Ioi 0) ↔
      IntegrableOn (fun t => F t * prob.cardyV a t) (Ioi 0) := fun F =>
    integrableOn_congr_fun (fun t ht => by rw [hVt_eq t (le_of_lt ht)]) measurableSet_Ioi
  have hVt_tail : ∀ ε > 0, ∃ R : ℝ, ∀ t ≥ R, t ^ (prob.w - 1) ≤ ε * Vt t := fun ε hε => by
    obtain ⟨R, hR⟩ := tail_of_fixed prob hc_pos hc ε hε
    refine ⟨max R 0, fun t ht => ?_⟩
    rw [hVt_eq t ((le_max_right _ _).trans ht)]
    exact hR t ((le_max_left _ _).trans ht)
  obtain ⟨φ, hφ, G, hGd, hTLU⟩ := exists_montel_limit hc_pos hc hg hM
  obtain ⟨hunifR, hreal⟩ := limit_converges hc_pos hg hTLU
  set gs : ℝ → ℝ := limitFn cTilde G with hgs
  have hgs_cont : Continuous gs := continuous_limitFn hGd cTilde
  have hgint : ∀ k, IntegrableOn (fun t => |g (φ k) t| * Vt t) (Ioi 0) := fun k =>
    (hcongrI _).2 (hg (φ k)).int_cardy
  have hgM : ∀ k, ∫ t in Ioi (0 : ℝ), |g (φ k) t| * Vt t = 1 := fun k => by
    rw [hcongr]; exact hM (φ k)
  have hgv : ∀ k, ∫ t in Ioi (0 : ℝ), g (φ k) t * Vt t ≤ 0 := fun k => by
    rw [hcongr]; exact hv (φ k)
  obtain ⟨hsint, hsM, hsv, ⟨t₀, ht₀, hgt₀⟩, hrest⟩ := limit_mass (V := Vt) hVt_cont hVt0
    (g := fun k => g (φ k)) (gs := gs) (R₀ := R₀) (fun k => (hg (φ k)).cont)
    hgs_cont.continuousOn hgint hgM hgv (fun k t ht => hneg (φ k) t ht) hunifR
  obtain ⟨hI, hlim⟩ := l1_tail_limit hVt_cont hVt0 prob.hw hVt_tail (g := fun k => g (φ k))
    (gs := gs) (fun k => (hg (φ k)).cont) hgs_cont.continuousOn hgint (fun k => (hgM k).le)
    hsint hsM hunifR
  have hpt : ∀ t : ℝ, 0 ≤ t → Tendsto (fun k => g (φ k) t) atTop (𝓝 (gs t)) := fun t ht =>
    (hunifR t).tendsto_at ⟨ht, le_rfl⟩
  have hGi : Integrable (radialLift prob.w gs) := (integrable_radialLift_iff prob.hw gs).2 hI
  have htc : TestClass prob a gs :=
    { cont := hgs_cont.continuousOn
      int_lift := hGi
      fourier_odd := radialLift_fourier_odd_of_limit prob.hw (fun k => (hg (φ k)).int_lift)
        (fun k => (hg (φ k)).fourier_odd) hGi hlim hpt
      int_cardy := (hcongrI _).1 hsint }
  have hgvac : prob.gVac a gs = -2 * π * ∫ t in Ioi (0 : ℝ), gs t * prob.cardyV a t := rfl
  have hMgs : prob.cardyNorm a gs = ∫ t in Ioi (0 : ℝ), |gs t| * prob.cardyV a t := rfl
  refine ⟨φ, gs, hφ, htc, fun t ht => ge_of_tendsto (hpt t (hR₀.trans ht)) (Eventually.of_forall fun k => hneg (φ k) t ht), hunifR, ?_, ?_, ⟨t₀, ht₀, hgt₀⟩, ?_, ⟨G, hGd, hreal⟩, ?_⟩
  · rw [hMgs, ← hcongr]; exact hsM
  · rw [hgvac, ← hcongr]; nlinarith [Real.pi_pos]
  · exact limitFn_zeros_finite hc_pos hGd hreal ⟨t₀, ht₀, hgt₀⟩
  · intro hle
    have h0 : 0 ≤ ∫ t in Ioi (0 : ℝ), gs t * Vt t := by
      rw [hcongr]; rw [hgvac] at hle; nlinarith [Real.pi_pos]
    obtain ⟨h1, h2⟩ := hrest h0
    refine ⟨by rw [hMgs, ← hcongr]; exact h1, ?_⟩
    refine h2.congr fun k => ?_
    exact hcongr (fun t => |g (φ k) t - gs t|)

end Assembly

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.exists_primal_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.exists_primal_limit

end FormalResearch.ModularBootstrap.FixedWeight
