module

public import FormalResearch.ModularBootstrap.Upper.Rigidity.Dictionary
public import FormalResearch.ModularBootstrap.FixedWeight.CrossingMeasure

/-!
# From crossing measures to the spectral measure `μ_S` (`spectral_rigidity.tex`, §1)

For `c = c'` (`cTilde`) and `a = c / 12`, the Airy chart of `Upper.Rigidity.Dictionary`
(`uAiry c t = -β (b - ξ_*) c^{2/3}`, `b = √(3t/c)`, `jAiry c t = |dt/du|`) turns a crossing measure
`ν` (`AdmissibleCrossingMeasure prob a`; for a discrete spectrum `ν = Σ d_n δ_{t_n}`) into the
spectral measure
`μ_S := Σ_n d_n δ_{u(t_n)} / (2π V(t_n) J(t_n))`, i.e. the push-forward under `u` of
`(2π V J)^{-1} ν|_{(0,∞)}` (`spectralMeasure`), with `V = cardyV a` the Cardy weight
(`ρ_C = 2π V`).  The inverse chart is `tAiry`; the window test function is
`Ψ_g(u) = g(t) V(t) J(t)`, `t = tAiry c u` (`psiAiry`, `= 0` for `u ≥ β ξ_* c^{2/3}`, outside the
range of the chart).

* `integral_psiAiry`: `∫ Ψ_g du = ∫_0^∞ g V dt` (change of variables, from Mathlib's
  `integral_image_eq_integral_abs_deriv_smul`), with integrability `integrable_psiAiry_iff`;
* `integral_spectralMeasure_psiAiry`, `integrable_spectralMeasure_psiAiry_iff`: for `ν{0} = 0`,
  `∫ Ψ_g dμ_S = (2π)^{-1} ∫ g dν` (this is the identity `d_n g(t_n) = 2π [d_n/(2πVJ)] Ψ_g(u(t_n))`);
* **Proposition 1** (`sr:P1`, `spectral_poisson_summation`): for `g ∈ Ā_w` (`TestClass`) with
  `|g(t)| ≤ C (1+t)^{-q} e^{-4π√(a t)}`, `q > (w+1)/2` (`q > 1` at `w = 1`), `Ψ_g` is
  `μ_S`-integrable and `∫ Ψ_g dμ_S = ∫ Ψ_g du = -g_vac / (2π)`; for comb decay
  `|g| ≤ C e^{-4π√(a t) - π√(3t/c)}` (`spectral_poisson_summation_comb`);
* **Proposition 2** (`sr:P2`, `spectral_complementary_slackness`): `g ≥ 0` on `[τ, ∞)` gives
  `0 ≤ ∫ Ψ_g dμ_S ≤ ∫ Ψ_g du` and `Ψ_g = 0` `μ_S`-a.e. when `g_vac ≥ 0`.

Normalisations: `u`, `J`, `V = cardyV`, `ρ_C = 2π V` and `g_vac = -2π ∫ g V` are exactly those of the
TeX; `cTilde = c' = c - 1`.  The TeX's "no light primaries" is `ν {0} = 0` (automatic for a measure at
a gap `τ > 0`).

All results are unconditional.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal Real

namespace FormalResearch.ModularBootstrap.Upper.Rigidity

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.Duality

/-! ### The inverse chart -/

/-- `e = ε = c^{-2/3}`. -/
noncomputable def epsAiry (c : ℝ) : ℝ := c ^ (-((2 : ℝ) / 3))

/-- The slope `ε / β` of `b = ξ_* - (ε/β) u`. -/
noncomputable def slopeAiry (c : ℝ) : ℝ := epsAiry c / betaTip

/-- The inverse chart `b(u) = max(ξ_* - ε u / β, 0)`. -/
noncomputable def bAiry (c u : ℝ) : ℝ := max (xiStar - u * slopeAiry c) 0

/-- The inverse chart `t(u) = c b(u)² / 3`. -/
noncomputable def tAiry (c u : ℝ) : ℝ := c / 3 * bAiry c u ^ 2

/-- The right end `u₀ = β ξ_* / ε` of the range of the chart: `t(u) > 0` iff `u < u₀`. -/
noncomputable def uEnd (c : ℝ) : ℝ := xiStar / slopeAiry c

lemma epsAiry_pos {c : ℝ} (hc : 0 < c) : 0 < epsAiry c := Real.rpow_pos_of_pos hc _

lemma slopeAiry_pos {c : ℝ} (hc : 0 < c) : 0 < slopeAiry c :=
  div_pos (epsAiry_pos hc) betaTip_pos

lemma rpow_two_thirds_mul_eps {c : ℝ} (hc : 0 < c) : c ^ ((2 : ℝ) / 3) * epsAiry c = 1 := by
  unfold epsAiry
  rw [← Real.rpow_add hc]; norm_num

lemma c_mul_eps {c : ℝ} (hc : 0 < c) : c * epsAiry c = c ^ ((1 : ℝ) / 3) := by
  unfold epsAiry
  have h := Real.rpow_add hc 1 (-((2 : ℝ) / 3))
  rw [Real.rpow_one] at h
  rw [← h]; norm_num

lemma xi_sub_uAiry_mul_slope {c : ℝ} (hc : 0 < c) (t : ℝ) :
    xiStar - uAiry c t * slopeAiry c = √(3 * t / c) := by
  have h1 := rpow_two_thirds_mul_eps hc
  have hb := betaTip_pos.ne'
  unfold uAiry slopeAiry
  have : -betaTip * (√(3 * t / c) - xiStar) * c ^ ((2 : ℝ) / 3) * (epsAiry c / betaTip) =
      -(√(3 * t / c) - xiStar) * (c ^ ((2 : ℝ) / 3) * epsAiry c) := by
    field_simp
  rw [this, h1]; ring

lemma bAiry_uAiry {c : ℝ} (hc : 0 < c) (t : ℝ) : bAiry c (uAiry c t) = √(3 * t / c) := by
  unfold bAiry
  rw [xi_sub_uAiry_mul_slope hc]
  exact max_eq_left (Real.sqrt_nonneg _)

lemma tAiry_uAiry {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) : tAiry c (uAiry c t) = t := by
  unfold tAiry
  rw [bAiry_uAiry hc, Real.sq_sqrt (by positivity)]
  field_simp

lemma bAiry_nonneg (c u : ℝ) : 0 ≤ bAiry c u := le_max_right _ _

lemma tAiry_nonneg {c : ℝ} (hc : 0 < c) (u : ℝ) : 0 ≤ tAiry c u := by
  unfold tAiry; have := bAiry_nonneg c u; positivity

lemma lt_uEnd_iff {c : ℝ} (hc : 0 < c) (u : ℝ) : u < uEnd c ↔ 0 < xiStar - u * slopeAiry c := by
  have hs := slopeAiry_pos hc
  unfold uEnd
  rw [lt_div_iff₀ hs]; constructor <;> intro h <;> linarith

lemma bAiry_eq_of_lt {c : ℝ} (hc : 0 < c) {u : ℝ} (hu : u < uEnd c) :
    bAiry c u = xiStar - u * slopeAiry c :=
  max_eq_left ((lt_uEnd_iff hc u).1 hu).le

lemma bAiry_pos_of_lt {c : ℝ} (hc : 0 < c) {u : ℝ} (hu : u < uEnd c) : 0 < bAiry c u := by
  rw [bAiry_eq_of_lt hc hu]; exact (lt_uEnd_iff hc u).1 hu

lemma bAiry_eq_zero_of_le {c : ℝ} (hc : 0 < c) {u : ℝ} (hu : uEnd c ≤ u) : bAiry c u = 0 := by
  have : ¬ u < uEnd c := not_lt.2 hu
  rw [lt_uEnd_iff hc] at this
  exact max_eq_right (not_lt.1 this)

lemma tAiry_pos_of_lt {c : ℝ} (hc : 0 < c) {u : ℝ} (hu : u < uEnd c) : 0 < tAiry c u := by
  unfold tAiry; have := bAiry_pos_of_lt hc hu; positivity

lemma tAiry_eq_zero_of_le {c : ℝ} (hc : 0 < c) {u : ℝ} (hu : uEnd c ≤ u) : tAiry c u = 0 := by
  unfold tAiry; rw [bAiry_eq_zero_of_le hc hu]; ring

lemma uAiry_lt_uEnd {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t) : uAiry c t < uEnd c := by
  rw [lt_uEnd_iff hc, xi_sub_uAiry_mul_slope hc]
  exact Real.sqrt_pos.2 (by positivity)

lemma jAiry_tAiry {c : ℝ} (hc : 0 < c) (u : ℝ) :
    jAiry c (tAiry c u) = 2 * bAiry c u * c ^ ((1 : ℝ) / 3) / (3 * betaTip) := by
  unfold jAiry tAiry
  have hb := bAiry_nonneg c u
  have : 3 * (c / 3 * bAiry c u ^ 2) / c = bAiry c u ^ 2 := by field_simp
  rw [this, Real.sqrt_sq hb]

lemma jAiry_zero (c : ℝ) : jAiry c 0 = 0 := by simp [jAiry]

lemma jAiry_pos {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 < t) : 0 < jAiry c t := by
  unfold jAiry
  have := betaTip_pos
  have h1 : 0 < √(3 * t / c) := Real.sqrt_pos.2 (by positivity)
  have h2 : 0 < c ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc _
  positivity

lemma continuous_uAiry (c : ℝ) : Continuous (uAiry c) := by
  unfold uAiry; fun_prop

lemma continuous_jAiry (c : ℝ) : Continuous (jAiry c) := by
  unfold jAiry; fun_prop

lemma continuous_bAiry (c : ℝ) : Continuous (bAiry c) := by
  unfold bAiry; fun_prop

lemma continuous_tAiry (c : ℝ) : Continuous (tAiry c) := by
  unfold tAiry; have := continuous_bAiry c; fun_prop

lemma tAiry_antitone {c : ℝ} (hc : 0 < c) : Antitone (tAiry c) := by
  intro u u' h
  have hs := slopeAiry_pos hc
  have hb : bAiry c u' ≤ bAiry c u := by
    unfold bAiry
    exact max_le_max (by nlinarith) le_rfl
  unfold tAiry
  have := bAiry_nonneg c u'
  gcongr

lemma hasDerivAt_tAiry_poly {c : ℝ} (u : ℝ) :
    HasDerivAt (fun u => c / 3 * (xiStar - u * slopeAiry c) ^ 2)
      (c / 3 * (2 * (xiStar - u * slopeAiry c) * (-slopeAiry c))) u := by
  have h1 : HasDerivAt (fun u : ℝ => xiStar - u * slopeAiry c) (-slopeAiry c) u := by
    simpa using ((hasDerivAt_id u).mul_const (slopeAiry c)).const_sub xiStar
  simpa using (h1.pow 2).const_mul (c / 3)

/-- `|t'(u)| = J(t(u))` on the range of the chart. -/
lemma abs_deriv_tAiry {c : ℝ} (hc : 0 < c) {u : ℝ} (hu : u < uEnd c) :
    |c / 3 * (2 * (xiStar - u * slopeAiry c) * (-slopeAiry c))| = jAiry c (tAiry c u) := by
  have hb := bAiry_pos_of_lt hc hu
  rw [jAiry_tAiry hc, bAiry_eq_of_lt hc hu] at *
  have hs := slopeAiry_pos hc
  have hbet := betaTip_pos
  have hce := c_mul_eps hc
  have hpos : 0 < c / 3 * (2 * (xiStar - u * slopeAiry c) * slopeAiry c) := by positivity
  have : c / 3 * (2 * (xiStar - u * slopeAiry c) * (-slopeAiry c)) =
      -(c / 3 * (2 * (xiStar - u * slopeAiry c) * slopeAiry c)) := by ring
  rw [this, abs_neg, abs_of_pos hpos]
  unfold slopeAiry
  rw [← hce]
  field_simp

lemma tAiry_strictAntiOn {c : ℝ} (hc : 0 < c) : StrictAntiOn (tAiry c) (Iio (uEnd c)) := by
  intro u hu u' hu' h
  have hs := slopeAiry_pos hc
  have hb' := bAiry_pos_of_lt hc hu'
  have hlt : bAiry c u' < bAiry c u := by
    rw [bAiry_eq_of_lt hc hu, bAiry_eq_of_lt hc hu']
    nlinarith
  unfold tAiry
  have := pow_lt_pow_left₀ hlt hb'.le (by norm_num : (2 : ℕ) ≠ 0)
  have : 0 < c / 3 := by positivity
  nlinarith

lemma tAiry_image {c : ℝ} (hc : 0 < c) : tAiry c '' Iio (uEnd c) = Ioi 0 := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact tAiry_pos_of_lt hc hu
  · intro ht
    exact ⟨uAiry c t, uAiry_lt_uEnd hc ht, tAiry_uAiry hc (le_of_lt ht)⟩

/-! ### The window test function `Ψ_g` and `∫ Ψ_g du = ∫_0^∞ g V dt` -/

/-- `Ψ_g(u) = g(t) V(t) J(t)` with `t = t(u)` (`sr:sec`, §1); it vanishes for `u ≥ u₀`, where `J = 0`. -/
noncomputable def psiAiry (prob : FixedWeightProblem) (c : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  g (tAiry c u) * prob.cardyV (c / 12) (tAiry c u) * jAiry c (tAiry c u)

lemma psiAiry_eq_zero_of_le {prob : FixedWeightProblem} {c : ℝ} (hc : 0 < c) {g : ℝ → ℝ} {u : ℝ}
    (hu : uEnd c ≤ u) : psiAiry prob c g u = 0 := by
  unfold psiAiry
  rw [tAiry_eq_zero_of_le hc hu, jAiry_zero, mul_zero]

lemma psiAiry_uAiry {prob : FixedWeightProblem} {c : ℝ} (hc : 0 < c) {g : ℝ → ℝ} {t : ℝ}
    (ht : 0 ≤ t) :
    psiAiry prob c g (uAiry c t) = g t * prob.cardyV (c / 12) t * jAiry c t := by
  unfold psiAiry
  rw [tAiry_uAiry hc ht]

lemma continuous_psiAiry {prob : FixedWeightProblem} {c : ℝ} (hc : 0 < c) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici 0)) : Continuous (psiAiry prob c g) := by
  unfold psiAiry
  have ht := continuous_tAiry c
  have hg' : Continuous fun u => g (tAiry c u) :=
    hg.comp_continuous ht fun u => mem_Ici.2 (tAiry_nonneg hc u)
  exact (hg'.mul ((continuous_cardyV prob (c / 12)).comp ht)).mul ((continuous_jAiry c).comp ht)

private lemma psi_change_of_variables {prob : FixedWeightProblem} {c : ℝ} (hc : 0 < c)
    (g : ℝ → ℝ) :
    (∫ t in Ioi 0, g t * prob.cardyV (c / 12) t) = ∫ u in Iio (uEnd c), psiAiry prob c g u := by
  have hderiv : ∀ u ∈ Iio (uEnd c), HasDerivWithinAt (tAiry c)
      (c / 3 * (2 * (xiStar - u * slopeAiry c) * (-slopeAiry c))) (Iio (uEnd c)) u := by
    intro u hu
    refine (hasDerivAt_tAiry_poly (c := c) u).hasDerivWithinAt.congr (fun y hy => ?_) ?_
    · unfold tAiry; rw [bAiry_eq_of_lt hc hy]
    · unfold tAiry; rw [bAiry_eq_of_lt hc hu]
  have key := integral_image_eq_integral_abs_deriv_smul (measurableSet_Iio (a := uEnd c)) hderiv
    (tAiry_strictAntiOn hc).injOn (fun t => g t * prob.cardyV (c / 12) t)
  rw [tAiry_image hc] at key
  rw [key]
  refine setIntegral_congr_fun measurableSet_Iio fun u hu => ?_
  simp only [smul_eq_mul]
  rw [abs_deriv_tAiry hc hu]
  unfold psiAiry; ring

private lemma psi_integrableOn_iff {prob : FixedWeightProblem} {c : ℝ} (hc : 0 < c)
    (g : ℝ → ℝ) :
    IntegrableOn (fun t => g t * prob.cardyV (c / 12) t) (Ioi 0) ↔
      IntegrableOn (psiAiry prob c g) (Iio (uEnd c)) := by
  have hderiv : ∀ u ∈ Iio (uEnd c), HasDerivWithinAt (tAiry c)
      (c / 3 * (2 * (xiStar - u * slopeAiry c) * (-slopeAiry c))) (Iio (uEnd c)) u := by
    intro u hu
    refine (hasDerivAt_tAiry_poly (c := c) u).hasDerivWithinAt.congr (fun y hy => ?_) ?_
    · unfold tAiry; rw [bAiry_eq_of_lt hc hy]
    · unfold tAiry; rw [bAiry_eq_of_lt hc hu]
  have key := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (measurableSet_Iio (a := uEnd c)) hderiv (tAiry_strictAntiOn hc).injOn
    (fun t => g t * prob.cardyV (c / 12) t)
  rw [tAiry_image hc] at key
  rw [key]
  refine integrableOn_congr_fun (fun u hu => ?_) measurableSet_Iio
  simp only [smul_eq_mul]
  rw [abs_deriv_tAiry hc hu]
  unfold psiAiry; ring

/-- `∫ Ψ_g du = ∫_0^∞ g V dt = -g_vac / (2π)` (`sr:sec`, §1). -/
theorem integral_psiAiry (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c) (g : ℝ → ℝ) :
    ∫ u, psiAiry prob c g u = ∫ t in Ioi 0, g t * prob.cardyV (c / 12) t := by
  rw [psi_change_of_variables hc]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu =>
    psiAiry_eq_zero_of_le hc (not_lt.1 hu)).symm

/-- `Ψ_g ∈ L¹(du)` iff `g V ∈ L¹(0, ∞)`. -/
theorem integrable_psiAiry_iff (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c) (g : ℝ → ℝ) :
    Integrable (psiAiry prob c g) ↔
      IntegrableOn (fun t => g t * prob.cardyV (c / 12) t) (Ioi 0) := by
  rw [psi_integrableOn_iff hc]
  constructor
  · intro h; exact h.integrableOn
  · intro h
    rw [IntegrableOn] at h
    have h0 : psiAiry prob c g =ᵐ[volume.restrict (Iio (uEnd c))ᶜ] 0 := by
      refine (ae_restrict_iff' (measurableSet_Iio.compl)).2 (Eventually.of_forall fun u hu => ?_)
      exact psiAiry_eq_zero_of_le hc (not_lt.1 hu)
    have h1 : Integrable (psiAiry prob c g) (volume.restrict (Iio (uEnd c))ᶜ) :=
      (integrable_zero _ _ _).congr h0.symm
    have := h.add_measure h1
    rwa [Measure.restrict_add_restrict_compl measurableSet_Iio] at this

theorem integral_psiAiry_eq_neg_gVac (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c)
    (g : ℝ → ℝ) : ∫ u, psiAiry prob c g u = -prob.gVac (c / 12) g / (2 * π) := by
  rw [integral_psiAiry prob hc]
  unfold FixedWeightProblem.gVac
  field_simp

/-! ### The spectral measure `μ_S` -/

/-- The spectral weight `1 / (2π V(t) J(t))` of an atom at `t`. -/
noncomputable def spectralWeight (prob : FixedWeightProblem) (c t : ℝ) : ℝ :=
  1 / (2 * π * prob.cardyV (c / 12) t * jAiry c t)

lemma spectralWeight_pos {prob : FixedWeightProblem} {c : ℝ} (hc : 0 < c)
    (ha : prob.totalShift ≤ c / 12) {t : ℝ} (ht : 0 < t) : 0 < spectralWeight prob c t := by
  unfold spectralWeight
  have := prob.cardyV_pos ha ht
  have := jAiry_pos hc ht
  positivity

lemma measurable_spectralWeight (prob : FixedWeightProblem) (c : ℝ) :
    Measurable (spectralWeight prob c) := by
  unfold spectralWeight
  exact measurable_const.div ((measurable_const.mul (continuous_cardyV prob (c / 12)).measurable).mul
    (continuous_jAiry c).measurable)

/-- The density `ofReal (1 / (2π V J))` of the spectral measure. -/
noncomputable def spectralDensity (prob : FixedWeightProblem) (c : ℝ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (spectralWeight prob c t)

lemma measurable_spectralDensity (prob : FixedWeightProblem) (c : ℝ) :
    Measurable (spectralDensity prob c) :=
  ENNReal.measurable_ofReal.comp (measurable_spectralWeight prob c)

/-- **The spectral measure** `μ_S` of a crossing measure `ν` (`spectral_rigidity.tex`, §1):
`μ_S = u_*((2π V J)^{-1} ν|_{(0,∞)})`; for `ν = Σ_n d_n δ_{t_n}` with `t_n > 0` this is
`Σ_n d_n δ_{u(t_n)} / (2π V(t_n) J(t_n))`. -/
noncomputable def spectralMeasure (prob : FixedWeightProblem) (c : ℝ) (ν : Measure ℝ) : Measure ℝ :=
  ((ν.restrict (Ioi 0)).withDensity (spectralDensity prob c)).map (uAiry c)

/-- Change of variables for `μ_S`: `∫ f dμ_S = ∫_{t>0} f(u(t)) / (2π V(t) J(t)) dν(t)`. -/
theorem integral_spectralMeasure (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c)
    (ha : prob.totalShift ≤ c / 12) (ν : Measure ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ u, f u ∂(spectralMeasure prob c ν) =
      ∫ t in Ioi 0, spectralWeight prob c t * f (uAiry c t) ∂ν := by
  unfold spectralMeasure
  rw [integral_map (continuous_uAiry c).aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (measurable_spectralDensity prob c)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
  unfold spectralDensity
  rw [ENNReal.toReal_ofReal (spectralWeight_pos hc ha ht).le, smul_eq_mul]

/-- Integrability for `μ_S`. -/
theorem integrable_spectralMeasure_iff (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c)
    (ha : prob.totalShift ≤ c / 12) (ν : Measure ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f (spectralMeasure prob c ν) ↔
      IntegrableOn (fun t => spectralWeight prob c t * f (uAiry c t)) (Ioi 0) ν := by
  unfold spectralMeasure
  rw [integrable_map_measure (hf.aestronglyMeasurable) (continuous_uAiry c).aemeasurable,
    integrable_withDensity_iff_integrable_smul' (measurable_spectralDensity prob c)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
  unfold spectralDensity
  rw [ENNReal.toReal_ofReal (spectralWeight_pos hc ha ht).le, smul_eq_mul]
  rfl

lemma weight_mul_psiAiry {prob : FixedWeightProblem} {c : ℝ} (hc : 0 < c)
    (ha : prob.totalShift ≤ c / 12) (g : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    spectralWeight prob c t * psiAiry prob c g (uAiry c t) = g t / (2 * π) := by
  rw [psiAiry_uAiry hc ht.le]
  have hV := (prob.cardyV_pos ha ht).ne'
  have hJ := (jAiry_pos hc ht).ne'
  unfold spectralWeight
  field_simp

/-- `∫ Ψ_g dμ_S = (2π)^{-1} ∫ g dν`: the identity `d_n g(t_n) = 2π [d_n/(2πVJ)(t_n)] Ψ_g(u(t_n))`
for a general measure `ν` with `ν{0} = 0` (no light primaries). -/
theorem integral_spectralMeasure_psiAiry (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c)
    (ha : prob.totalShift ≤ c / 12) {ν : Measure ℝ} (hν0 : ν {0} = 0) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici 0)) :
    ∫ u, psiAiry prob c g u ∂(spectralMeasure prob c ν) = (∫ t in Ici 0, g t ∂ν) / (2 * π) := by
  rw [integral_spectralMeasure prob hc ha ν (continuous_psiAiry hc hg)]
  have : ∫ t in Ioi 0, spectralWeight prob c t * psiAiry prob c g (uAiry c t) ∂ν =
      ∫ t in Ioi 0, g t / (2 * π) ∂ν :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => weight_mul_psiAiry hc ha g ht
  rw [this, integral_div, setIntegral_congr_set (Ioi_ae_eq_Ici' hν0)]

theorem integrable_spectralMeasure_psiAiry_iff (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c)
    (ha : prob.totalShift ≤ c / 12) {ν : Measure ℝ} (hν0 : ν {0} = 0) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici 0)) :
    Integrable (psiAiry prob c g) (spectralMeasure prob c ν) ↔ IntegrableOn g (Ici 0) ν := by
  rw [integrable_spectralMeasure_iff prob hc ha ν (continuous_psiAiry hc hg)]
  have h1 : IntegrableOn (fun t => spectralWeight prob c t * psiAiry prob c g (uAiry c t))
      (Ioi 0) ν ↔ IntegrableOn (fun t => g t / (2 * π)) (Ioi 0) ν :=
    integrableOn_congr_fun (fun t ht => weight_mul_psiAiry hc ha g ht) measurableSet_Ioi
  rw [h1]
  have h2 : IntegrableOn (fun t => g t / (2 * π)) (Ioi 0) ν ↔ IntegrableOn g (Ioi 0) ν := by
    have hπ : (2 * π) ≠ 0 := by positivity
    simp only [div_eq_mul_inv]
    exact integrable_mul_const_iff (Ne.isUnit (inv_ne_zero hπ)) _
  rw [h2]
  exact integrableOn_congr_set_ae (Ioi_ae_eq_Ici' hν0)

/-! ### Propositions 1 and 2 -/

lemma integrable_psiAiry_of_testClass (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c)
    (ha : prob.totalShift ≤ c / 12) {g : ℝ → ℝ} (hg : TestClass prob (c / 12) g) :
    Integrable (psiAiry prob c g) := by
  rw [integrable_psiAiry_iff prob hc]
  refine hg.int_cardy.mono' ?_ ?_
  · exact (hg.cont.mono Ioi_subset_Ici_self |>.mul
      (continuous_cardyV prob (c / 12)).continuousOn).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (prob.cardyV_nonneg ha (mem_Ioi.1 ht).le)]

/-- **Proposition 1** (`sr:P1`, spectral Poisson summation).  Let `ν` be a crossing measure with no
atom at `0` (no light primaries) and `g ∈ Ā_w` with `|g(t)| ≤ C (1+t)^{-q} e^{-4π√(a t)}`,
`q > (w+1)/2` (`q > 1` at `w = 1`), `a = c/12`.  Then `∫ |Ψ_g| dμ_S < ∞` (`Integrable`) and
`∫ Ψ_g dμ_S = ∫ Ψ_g du = -g_vac/(2π)`.  Source: `spectral_rigidity.tex`, §1 (via
`Duality.proposition_P1` = Lemma FW-X(2)). -/
theorem spectral_poisson_summation (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c)
    (ha : prob.totalShift ≤ c / 12) (meas : AdmissibleCrossingMeasure prob (c / 12))
    (hν0 : meas.ν {0} = 0) {g : ℝ → ℝ} (hg : TestClass prob (c / 12) g) {q C_g : ℝ}
    (hq : (prob.w + 1 : ℝ) / 2 < q) (hC_g : 0 ≤ C_g)
    (hdecay : ∀ t, 0 ≤ t →
      |g t| ≤ C_g * (1 + t) ^ (-q) * Real.exp (-4 * π * Real.sqrt ((c / 12) * t))) :
    Integrable (psiAiry prob c g) (spectralMeasure prob c meas.ν) ∧
      Integrable (psiAiry prob c g) ∧
      ∫ u, psiAiry prob c g u ∂(spectralMeasure prob c meas.ν) = ∫ u, psiAiry prob c g u ∧
      ∫ u, psiAiry prob c g u = -prob.gVac (c / 12) g / (2 * π) := by
  have ha_pos : 0 < c / 12 := by positivity
  obtain ⟨hint, heq⟩ := Duality.proposition_P1 prob ha ha_pos meas hg hq hC_g hdecay
  have hcont := hg.cont
  refine ⟨(integrable_spectralMeasure_psiAiry_iff prob hc ha hν0 hcont).2 hint,
    integrable_psiAiry_of_testClass prob hc ha hg, ?_, integral_psiAiry_eq_neg_gVac prob hc g⟩
  rw [integral_spectralMeasure_psiAiry prob hc ha hν0 hcont, integral_psiAiry_eq_neg_gVac prob hc g]
  congr 1
  linarith

/-- **Proposition 1 for combs** (`sr:P1` with the decay of item (P1) of Property (P)): the
hypothesis is `|g(t)| ≤ C e^{-4π√(a t) - π√(3t/c)}`, i.e. `C e^{-c L(x) - π x}`. -/
theorem spectral_poisson_summation_comb (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c)
    (ha : prob.totalShift ≤ c / 12) (meas : AdmissibleCrossingMeasure prob (c / 12))
    (hν0 : meas.ν {0} = 0) {g : ℝ → ℝ} (hg : TestClass prob (c / 12) g) {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ t, 0 ≤ t →
      |g t| ≤ C * Real.exp (-4 * π * Real.sqrt ((c / 12) * t) - π * Real.sqrt (3 * t / c))) :
    Integrable (psiAiry prob c g) (spectralMeasure prob c meas.ν) ∧
      Integrable (psiAiry prob c g) ∧
      ∫ u, psiAiry prob c g u ∂(spectralMeasure prob c meas.ν) = ∫ u, psiAiry prob c g u := by
  obtain ⟨hint, heq⟩ := FixedWeight.sumRule_of_comb_decay prob (cTilde := c) (by linarith) hc meas
    hg hC hdecay
  have hcont := hg.cont
  refine ⟨(integrable_spectralMeasure_psiAiry_iff prob hc ha hν0 hcont).2 hint,
    integrable_psiAiry_of_testClass prob hc ha hg, ?_⟩
  rw [integral_spectralMeasure_psiAiry prob hc ha hν0 hcont, integral_psiAiry_eq_neg_gVac prob hc g,
    heq]

/-- The spectral measure of a measure at gap `τ` lives on `u ≤ u(τ)` (`u` is decreasing). -/
theorem spectralMeasure_Ioi_eq_zero (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c)
    {a : ℝ} (meas : AdmissibleCrossingMeasure prob a) {τ : ℝ} (hgap : IsAtGap meas τ) :
    spectralMeasure prob c meas.ν (Ioi (uAiry c τ)) = 0 := by
  unfold spectralMeasure
  rw [Measure.map_apply (continuous_uAiry c).measurable measurableSet_Ioi]
  refine withDensity_absolutelyContinuous _ _ ?_
  have hsub : uAiry c ⁻¹' Ioi (uAiry c τ) ⊆ Iio τ := fun t ht => by
    by_contra h
    exact absurd (uAiry_antitone hc (not_lt.1 h)) (not_le.2 ht)
  refine le_antisymm ?_ bot_le
  calc (meas.ν.restrict (Ioi 0)) (uAiry c ⁻¹' Ioi (uAiry c τ))
      ≤ meas.ν (uAiry c ⁻¹' Ioi (uAiry c τ)) := Measure.restrict_le_self _
    _ ≤ meas.ν (Iio τ) := measure_mono hsub
    _ = 0 := hgap

/-- `g ≥ 0` on `[τ, ∞)` gives `Ψ_g ≥ 0` on `u ≤ u(τ)` (item (P2) of Property (P) for the spectral
sum rule). -/
lemma psiAiry_nonneg {prob : FixedWeightProblem} {c : ℝ} (hc : 0 < c)
    (ha : prob.totalShift ≤ c / 12) {τ : ℝ} (hτ : 0 ≤ τ) {g : ℝ → ℝ}
    (hg : ∀ t, τ ≤ t → 0 ≤ g t) {u : ℝ} (hu : u ≤ uAiry c τ) : 0 ≤ psiAiry prob c g u := by
  unfold psiAiry
  have h1 : τ ≤ tAiry c u := by
    have := tAiry_antitone hc hu
    rwa [tAiry_uAiry hc hτ] at this
  have h2 := hg _ h1
  have h3 := prob.cardyV_nonneg ha ((hτ.trans h1))
  have h4 : 0 ≤ jAiry c (tAiry c u) := by
    rw [jAiry_tAiry hc]
    have := bAiry_nonneg c u
    have := betaTip_pos
    have : 0 ≤ c ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hc.le _
    positivity
  positivity

lemma nu_zero_eq_zero {prob : FixedWeightProblem} {a : ℝ} {meas : AdmissibleCrossingMeasure prob a}
    {τ : ℝ} (hτ : 0 < τ) (hgap : IsAtGap meas τ) : meas.ν {0} = 0 :=
  measure_mono_null (fun t (ht : t = 0) => by simp [ht, hτ]) hgap

/-- **Proposition 2** (`sr:P2`, complementary slackness) for `μ_S` of a measure at gap `τ > 0`:
`g ≥ 0` on `[τ, ∞)` gives `Ψ_g ∈ L¹(μ_S)` and `0 ≤ ∫ Ψ_g dμ_S ≤ ∫ Ψ_g du = -g_vac/(2π)`; if
`g_vac ≥ 0` then `Ψ_g = 0` `μ_S`-almost everywhere. -/
theorem spectral_complementary_slackness (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c)
    (ha : prob.totalShift ≤ c / 12) (meas : AdmissibleCrossingMeasure prob (c / 12)) {τ : ℝ}
    (hτ : 0 < τ) (hgap : IsAtGap meas τ) {g : ℝ → ℝ} (hg : TestClass prob (c / 12) g)
    (hg_nn : ∀ t, τ ≤ t → 0 ≤ g t) :
    Integrable (psiAiry prob c g) (spectralMeasure prob c meas.ν) ∧
      0 ≤ ∫ u, psiAiry prob c g u ∂(spectralMeasure prob c meas.ν) ∧
      ∫ u, psiAiry prob c g u ∂(spectralMeasure prob c meas.ν) ≤ ∫ u, psiAiry prob c g u ∧
      (0 ≤ prob.gVac (c / 12) g → ∀ᵐ u ∂(spectralMeasure prob c meas.ν), psiAiry prob c g u = 0) := by
  have ha_pos : 0 < c / 12 := by positivity
  have hν0 := nu_zero_eq_zero hτ hgap
  have hcont := hg.cont
  obtain ⟨hint, h0, hle, hzero⟩ := Duality.proposition_P2 prob ha ha_pos meas hτ hgap hg hg_nn
  have hI := integral_spectralMeasure_psiAiry prob hc ha hν0 hcont (ν := meas.ν)
  refine ⟨(integrable_spectralMeasure_psiAiry_iff prob hc ha hν0 hcont).2 hint, ?_, ?_, fun hv => ?_⟩
  · rw [hI]; positivity
  · rw [hI, integral_psiAiry_eq_neg_gVac prob hc g]
    exact div_le_div_of_nonneg_right hle (by positivity)
  · have hg0 := (hzero hv).2
    unfold spectralMeasure
    have hmeas : MeasurableSet {u | psiAiry prob c g u = 0} :=
      measurableSet_eq_fun (continuous_psiAiry hc hcont).measurable measurable_const
    rw [ae_map_iff (continuous_uAiry c).aemeasurable hmeas]
    refine (withDensity_absolutelyContinuous _ _).ae_le ?_
    have hrestr : ∀ᵐ t ∂(meas.ν.restrict (Ioi 0)), g t = 0 := ae_restrict_of_ae hg0
    filter_upwards [hrestr, ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with t h1 h2
    show psiAiry prob c g (uAiry c t) = 0
    rw [psiAiry_uAiry hc (mem_Ioi.1 h2).le, h1]; ring

/-! ### Local finiteness of `μ_S` for a measure at a positive gap -/

lemma measure_Icc_lt_top {prob : FixedWeightProblem} {a : ℝ} (meas : AdmissibleCrossingMeasure prob a)
    (R : ℝ) : meas.ν (Icc 0 R) < ⊤ := by
  have h1 : IntegrableOn (fun t => Real.exp (-2 * π * 1 * t)) (Icc 0 R) meas.ν :=
    (meas.finite_laplace one_pos).mono_set Icc_subset_Ici_self
  have h2 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc 0 R) meas.ν := by
    refine (h1.const_mul (Real.exp (2 * π * R))).mono' aestronglyMeasurable_const ?_
    filter_upwards [ae_restrict_mem (measurableSet_Icc (a := (0 : ℝ)) (b := R))] with t ht
    rw [norm_one, ← Real.exp_add]
    exact Real.one_le_exp (by nlinarith [ht.2, Real.pi_pos])
  rcases (integrableOn_const_iff).1 h2 with h | h
  · simp at h
  · exact h

/-- `μ_S([A, ∞)) < ∞` for a measure at a positive gap. -/
theorem spectralMeasure_Ici_lt_top (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c)
    (ha : prob.totalShift ≤ c / 12) (meas : AdmissibleCrossingMeasure prob (c / 12)) {τ : ℝ}
    (hτ : 0 < τ) (hgap : IsAtGap meas τ) (A : ℝ) :
    spectralMeasure prob c meas.ν (Ici A) < ⊤ := by
  set T := tAiry c A with hT
  have hcont : ContinuousOn (spectralWeight prob c) (Icc τ T) := by
    unfold spectralWeight
    refine continuousOn_const.div ?_ fun t ht => ?_
    · exact (((continuous_const.mul (continuous_cardyV prob (c / 12))).mul
        (continuous_jAiry c))).continuousOn
    · have ht0 : 0 < t := hτ.trans_le ht.1
      have := prob.cardyV_pos ha ht0
      have := jAiry_pos hc ht0
      positivity
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  unfold spectralMeasure
  rw [Measure.map_apply (continuous_uAiry c).measurable measurableSet_Ici,
    withDensity_apply _ ((continuous_uAiry c).measurable measurableSet_Ici)]
  have hsub : (uAiry c ⁻¹' Ici A) ≤ᵐ[meas.ν.restrict (Ioi 0)] Icc τ T := by
    have hae : ∀ᵐ t ∂meas.ν, τ ≤ t := ae_ge_of_isAtGap hgap
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))]
      with t h1 h2 h3
    refine ⟨h1, ?_⟩
    have := tAiry_antitone hc (show A ≤ uAiry c t from h3)
    rwa [tAiry_uAiry hc (mem_Ioi.1 h2).le] at this
  calc ∫⁻ t in uAiry c ⁻¹' Ici A, spectralDensity prob c t ∂(meas.ν.restrict (Ioi 0))
      ≤ ∫⁻ t in Icc τ T, spectralDensity prob c t ∂(meas.ν.restrict (Ioi 0)) :=
        lintegral_mono_set' hsub
    _ ≤ ∫⁻ t in Icc τ T, ENNReal.ofReal M ∂(meas.ν.restrict (Ioi 0)) := by
        refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
        unfold spectralDensity
        refine ENNReal.ofReal_le_ofReal ?_
        have := hM t ht
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans this
    _ = ENNReal.ofReal M * (meas.ν.restrict (Ioi 0)) (Icc τ T) := setLIntegral_const _ _
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        calc (meas.ν.restrict (Ioi 0)) (Icc τ T) ≤ meas.ν (Icc τ T) := Measure.restrict_le_self _
          _ ≤ meas.ν (Icc 0 T) := measure_mono (Icc_subset_Icc hτ.le le_rfl)
          _ < ⊤ := measure_Icc_lt_top meas T

theorem isLocallyFiniteMeasure_spectralMeasure (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c)
    (ha : prob.totalShift ≤ c / 12) (meas : AdmissibleCrossingMeasure prob (c / 12)) {τ : ℝ}
    (hτ : 0 < τ) (hgap : IsAtGap meas τ) : IsLocallyFiniteMeasure (spectralMeasure prob c meas.ν) := by
  refine ⟨fun x => ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩⟩
  exact lt_of_le_of_lt (measure_mono Icc_subset_Ici_self)
    (spectralMeasure_Ici_lt_top prob hc ha meas hτ hgap (x - 1))

/-! ### The discrete form `μ_S = Σ_n d_n δ_{u(t_n)} / (2π V(t_n) J(t_n))` -/

lemma withDensity_dirac_aux {f : ℝ → ℝ≥0∞} (hf : Measurable f) (x : ℝ) :
    (Measure.dirac x).withDensity f = f x • Measure.dirac x := by
  ext s hs
  classical
  rw [withDensity_apply _ hs, smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs,
    setLIntegral_dirac' hf hs]
  by_cases h : x ∈ s <;> simp [h]

/-- The spectral measure of a discrete spectrum `(d_n, t_n)` (`spectral_rigidity.tex`, §1):
`Σ_n d_n δ_{u(t_n)} / (2π V(t_n) J(t_n))`. -/
noncomputable def discreteSpectralMeasure (prob : FixedWeightProblem) (c : ℝ) {ι : Type*}
    (t d : ι → ℝ) : Measure ℝ :=
  Measure.sum fun n => ENNReal.ofReal (d n * spectralWeight prob c (t n)) •
    Measure.dirac (uAiry c (t n))

/-- For `ν = Σ_n d_n δ_{t_n}` (the measure of a spectrum without light primaries, `t_n > 0`),
`spectralMeasure` is the displayed sum `Σ_n d_n δ_{u(t_n)} / (2π V(t_n) J(t_n))` of the TeX. -/
theorem spectralMeasure_sum_dirac (prob : FixedWeightProblem) {c : ℝ} {ι : Type*} (t d : ι → ℝ)
    (ht : ∀ n, 0 < t n) (hd : ∀ n, 0 ≤ d n) :
    spectralMeasure prob c (Measure.sum fun n => ENNReal.ofReal (d n) • Measure.dirac (t n)) =
      discreteSpectralMeasure prob c t d := by
  unfold spectralMeasure discreteSpectralMeasure
  have hrestr : (Measure.sum fun n => ENNReal.ofReal (d n) • Measure.dirac (t n)).restrict
      (Ioi 0) = Measure.sum fun n => ENNReal.ofReal (d n) • Measure.dirac (t n) := by
    rw [Measure.restrict_sum _ measurableSet_Ioi]
    congr 1
    ext1 n
    rw [Measure.restrict_smul, Measure.restrict_eq_self_of_ae_mem]
    exact (ae_dirac_iff measurableSet_Ioi).2 (ht n)
  rw [hrestr, withDensity_sum, Measure.map_sum]
  · congr 1
    ext1 n
    rw [withDensity_smul_measure, withDensity_dirac_aux (measurable_spectralDensity prob c),
      Measure.map_smul _ (continuous_uAiry c).aemeasurable,
      Measure.map_smul _ (continuous_uAiry c).aemeasurable,
      Measure.map_dirac' (continuous_uAiry c).measurable, smul_smul]
    unfold spectralDensity
    rw [← ENNReal.ofReal_mul (hd n)]
  · exact (continuous_uAiry c).aemeasurable

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.integral_psiAiry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.integral_psiAiry

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.integrable_psiAiry_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.integrable_psiAiry_iff

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.integral_psiAiry_eq_neg_gVac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.integral_psiAiry_eq_neg_gVac

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.integral_spectralMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.integral_spectralMeasure

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.integral_spectralMeasure_psiAiry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.integral_spectralMeasure_psiAiry

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.integrable_spectralMeasure_psiAiry_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.integrable_spectralMeasure_psiAiry_iff

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.spectral_poisson_summation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.spectral_poisson_summation

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.spectral_poisson_summation_comb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.spectral_poisson_summation_comb

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.spectral_complementary_slackness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.spectral_complementary_slackness

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.spectralMeasure_Ioi_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.spectralMeasure_Ioi_eq_zero

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.spectralMeasure_Ici_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.spectralMeasure_Ici_lt_top

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.isLocallyFiniteMeasure_spectralMeasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.isLocallyFiniteMeasure_spectralMeasure

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.spectralMeasure_sum_dirac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.spectralMeasure_sum_dirac

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.psiAiry_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.psiAiry_nonneg

end FormalResearch.ModularBootstrap.Upper.Rigidity
