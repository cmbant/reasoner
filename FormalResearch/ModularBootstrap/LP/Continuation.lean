module

public import FormalResearch.ModularBootstrap.LP.Cayley
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Lemma LP-A (`ds:cont`): all positive temperatures from one neighbourhood

`CFT/modular_bootstrap/paper/dual_spectrum_limit.tex`, Lemma LP-A (line 22).  Let `ν` be a positive
measure on `[0, ∞)`, `Z(β) = ∫ e^{-2πβt} dν`, `w > 0` and `v` real analytic on `(0, ∞)`.  If
`Z(s) < ∞` for some `s ∈ (0,1)` and
`Z(β) + v(β) = β^{-w} [Z(1/β) + v(1/β)]` for `s < β < 1/s`,
then `Z(β) < ∞` and the identity holds for every `β > 0` (`ds_cont`).

The paper continues `Z` holomorphically to a disc around the abscissa of convergence `β_c`
(Landau/Pringsheim).  Here the argument is the real-variable form: `Z` is real analytic on
`(β_c, ∞)` with `Z^{(k)}(β) = (-2π)^k ∫ t^k e^{-2πβt} dν` (Mathlib's `iteratedDeriv_mgf`), the crossing
identity continues `Z` real analytically to a neighbourhood of `β_c` (`landau_step`: monotone
convergence gives `∫ t^k e^{-2πβ_c t} dν = (-2π)^{-k} G^{(k)}(β_c) < ∞`, and the Taylor series of the
continuation at `β_c`, whose terms are nonnegative at `β_c - σ`, integrates termwise by Tonelli).  Only real
analyticity of `v` on `(0, ∞)` is used, which is weaker than the paper's holomorphy on
`{Re β > 0}`.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology ProbabilityTheory
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.LP

/-- `X(t) = -2π t`, so that `mgf lapX ν β = ∫ e^{-2πβt} dν`. -/
noncomputable def lapX (t : ℝ) : ℝ := -2 * π * t

/-- The Laplace transform `Z(β) = ∫ e^{-2πβ t} dν`. -/
noncomputable def lapZ (ν : Measure ℝ) (β : ℝ) : ℝ := ∫ t, Real.exp (-2 * π * β * t) ∂ν

/-- Finiteness of the Laplace transform at `β`. -/
def LapFin (ν : Measure ℝ) (β : ℝ) : Prop := Integrable (fun t => Real.exp (-2 * π * β * t)) ν

lemma exp_lapX (β t : ℝ) : Real.exp (β * lapX t) = Real.exp (-2 * π * β * t) := by
  unfold lapX; ring_nf

lemma mgf_lapX (ν : Measure ℝ) (β : ℝ) : mgf lapX ν β = lapZ ν β := by
  unfold mgf lapZ; simp only [exp_lapX]

lemma mem_integrableExpSet_lapX {ν : Measure ℝ} {β : ℝ} :
    β ∈ integrableExpSet lapX ν ↔ LapFin ν β := by
  simp only [integrableExpSet, mem_ofPred_eq, LapFin, exp_lapX]

lemma LapFin.mono {ν : Measure ℝ} (hν : ν (Iio 0) = 0) {β β' : ℝ} (h : LapFin ν β)
    (hle : β ≤ β') : LapFin ν β' := by
  have hae : ∀ᵐ t ∂ν, 0 ≤ t := by
    have : ∀ᵐ t ∂ν, t ∉ Iio 0 := measure_eq_zero_iff_ae_notMem.1 hν
    filter_upwards [this] with t ht using not_lt.1 ht
  refine Integrable.mono' h (by fun_prop : Continuous fun t : ℝ =>
    Real.exp (-2 * π * β' * t)).aestronglyMeasurable ?_
  filter_upwards [hae] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  have : 0 ≤ 2 * π * t := by positivity
  nlinarith only [this, hle]

/-- The `k`-th moment integrand `t^k e^{-2πβt}`. -/
noncomputable def lapMom (k : ℕ) (β t : ℝ) : ℝ := t ^ k * Real.exp (-2 * π * β * t)

lemma lapMom_nonneg (k : ℕ) (β : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ lapMom k β t := by
  unfold lapMom; positivity

lemma continuous_lapMom (k : ℕ) (β : ℝ) : Continuous (lapMom k β) := by
  unfold lapMom; fun_prop

lemma lapX_pow_mul_exp (k : ℕ) (β t : ℝ) :
    lapX t ^ k * Real.exp (β * lapX t) = (-2 * π) ^ k * lapMom k β t := by
  unfold lapMom lapX
  rw [mul_pow]
  have : Real.exp (β * (-2 * π * t)) = Real.exp (-2 * π * β * t) := by ring_nf
  rw [this]; ring

/-- On an open interval of finiteness, `Z` is `mgf lapX ν`, with the moment integrals as
derivatives. -/
lemma iteratedDeriv_lap {ν : Measure ℝ} {a b : ℝ} (hfin : ∀ β ∈ Ioo a b, LapFin ν β) {G : ℝ → ℝ}
    (hGZ : ∀ β ∈ Ioo a b, G β = lapZ ν β) {β : ℝ} (hβ : β ∈ Ioo a b) (k : ℕ) :
    Integrable (lapMom k β) ν ∧
      iteratedDeriv k G β = (-2 * π) ^ k * ∫ t, lapMom k β t ∂ν := by
  have hint : Ioo a b ⊆ interior (integrableExpSet lapX ν) :=
    interior_maximal (fun x hx => mem_integrableExpSet_lapX.2 (hfin x hx)) isOpen_Ioo
  have hβi := hint hβ
  have h1 := integrable_pow_mul_exp_of_mem_interior_integrableExpSet hβi k
  have hc : (-2 * π) ^ k ≠ 0 := pow_ne_zero _ (by have := Real.pi_pos; linarith)
  refine ⟨?_, ?_⟩
  · refine (h1.const_mul ((-2 * π) ^ k)⁻¹).congr (Eventually.of_forall fun t => ?_)
    simp only [lapX_pow_mul_exp]
    field_simp
  · have heq : G =ᶠ[𝓝 β] mgf lapX ν :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hβ)
        (fun x hx => (hGZ x hx).trans (mgf_lapX ν x).symm)
    rw [heq.iteratedDeriv_eq k, iteratedDeriv_mgf hβi k]
    simp only [lapX_pow_mul_exp]
    rw [integral_const_mul]

/-- **Moments at the boundary** (monotone convergence): if `G` is analytic at `β₀`, finite
and equal to `Z` on `(β₀, β₀ + δ)`, then `∫ t^k e^{-2πβ₀ t} dν = (-2π)^{-k} G^{(k)}(β₀) < ∞`. -/
lemma lintegral_lapMom_boundary {ν : Measure ℝ} (hν : ν (Iio 0) = 0) {β₀ δ : ℝ} (hδ : 0 < δ)
    {G : ℝ → ℝ} (hG : AnalyticAt ℝ G β₀) (hfin : ∀ β ∈ Ioo β₀ (β₀ + δ), LapFin ν β)
    (hGZ : ∀ β ∈ Ioo β₀ (β₀ + δ), G β = lapZ ν β) (k : ℕ) :
    0 ≤ iteratedDeriv k G β₀ / (-2 * π) ^ k ∧
      ∫⁻ t, ENNReal.ofReal (lapMom k β₀ t) ∂ν =
        ENNReal.ofReal (iteratedDeriv k G β₀ / (-2 * π) ^ k) := by
  have hae : ∀ᵐ t ∂ν, 0 ≤ t := by
    have : ∀ᵐ t ∂ν, t ∉ Iio 0 := measure_eq_zero_iff_ae_notMem.1 hν
    filter_upwards [this] with t ht using not_lt.1 ht
  have hc : (-2 * π) ^ k ≠ 0 := pow_ne_zero _ (by have := Real.pi_pos; linarith)
  set D : ℝ := iteratedDeriv k G β₀ / (-2 * π) ^ k with hD
  let β : ℕ → ℝ := fun n => β₀ + δ / ((n : ℝ) + 2)
  have hβmem : ∀ n, β n ∈ Ioo β₀ (β₀ + δ) := by
    intro n
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    refine ⟨by simp only [β]; have := div_pos hδ h2; linarith, ?_⟩
    simp only [β]
    have : δ / ((n : ℝ) + 2) < δ := by
      rw [div_lt_iff₀ h2]; nlinarith only [hδ, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    linarith
  have hβtend : Tendsto β atTop (𝓝 β₀) := by
    have : Tendsto (fun n : ℕ => δ / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    simpa using (tendsto_const_nhds (x := β₀)).add this
  have hβanti : Antitone β := by
    intro m n hmn
    simp only [β]
    have h1 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have : (m : ℝ) + 2 ≤ n + 2 := by exact_mod_cast Nat.add_le_add_right hmn 2
    have := div_le_div_of_nonneg_left hδ.le h1 this
    linarith
  -- values of the derivatives
  have hval : ∀ n, iteratedDeriv k G (β n) / (-2 * π) ^ k = ∫ t, lapMom k (β n) t ∂ν := by
    intro n
    rw [(iteratedDeriv_lap hfin hGZ (hβmem n) k).2]; field_simp
  have hint : ∀ n, Integrable (lapMom k (β n)) ν := fun n =>
    (iteratedDeriv_lap hfin hGZ (hβmem n) k).1
  have hDtend : Tendsto (fun n => iteratedDeriv k G (β n) / (-2 * π) ^ k) atTop (𝓝 D) := by
    have hcont : ContinuousAt (iteratedDeriv k G) β₀ := by
      rw [iteratedDeriv_eq_iterate]; exact (hG.iterated_deriv k).continuousAt
    exact (hcont.tendsto.comp hβtend).div_const _
  have hnn : ∀ n, 0 ≤ iteratedDeriv k G (β n) / (-2 * π) ^ k := fun n => by
    rw [hval n]; exact integral_nonneg_of_ae (by
      filter_upwards [hae] with t ht using lapMom_nonneg k _ ht)
  have hD0 : 0 ≤ D := ge_of_tendsto' hDtend hnn
  refine ⟨hD0, ?_⟩
  -- monotone convergence
  have hmono : ∀ᵐ t ∂ν, Monotone fun n => ENNReal.ofReal (lapMom k (β n) t) := by
    filter_upwards [hae] with t ht m n hmn
    apply ENNReal.ofReal_le_ofReal
    unfold lapMom
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.2
    have := hβanti hmn
    have : 0 ≤ 2 * π * t := by positivity
    nlinarith only [this, hβanti hmn]
  have htend : ∀ᵐ t ∂ν, Tendsto (fun n => ENNReal.ofReal (lapMom k (β n) t)) atTop
      (𝓝 (ENNReal.ofReal (lapMom k β₀ t))) := by
    refine Eventually.of_forall fun t => ?_
    have hc : Continuous fun b : ℝ => lapMom k b t := by unfold lapMom; fun_prop
    exact ENNReal.tendsto_ofReal ((hc.tendsto β₀).comp hβtend)
  have hmc := lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (ENNReal.measurable_ofReal.comp (continuous_lapMom k (β n)).measurable).aemeasurable)
    hmono htend
  have hmc2 : Tendsto (fun n => ∫⁻ t, ENNReal.ofReal (lapMom k (β n) t) ∂ν) atTop
      (𝓝 (ENNReal.ofReal D)) := by
    refine (ENNReal.tendsto_ofReal hDtend).congr fun n => ?_
    rw [hval n]
    exact ofReal_integral_eq_lintegral_ofReal (hint n) (by
      filter_upwards [hae] with t ht using lapMom_nonneg k _ ht)
  exact tendsto_nhds_unique hmc hmc2

/-- **Landau step**: if `G` is analytic at `β₀` and equals the (finite) Laplace transform on
`(β₀, β₀ + δ)`, then the Laplace transform is finite at `β₀ - σ` for some `σ > 0`. -/
theorem landau_step {ν : Measure ℝ} (hν : ν (Iio 0) = 0) {β₀ δ : ℝ} (hδ : 0 < δ)
    {G : ℝ → ℝ} (hG : AnalyticAt ℝ G β₀) (hfin : ∀ β ∈ Ioo β₀ (β₀ + δ), LapFin ν β)
    (hGZ : ∀ β ∈ Ioo β₀ (β₀ + δ), G β = lapZ ν β) :
    ∃ σ : ℝ, 0 < σ ∧ LapFin ν (β₀ - σ) := by
  have hae : ∀ᵐ t ∂ν, 0 ≤ t := by
    have : ∀ᵐ t ∂ν, t ∉ Iio 0 := measure_eq_zero_iff_ae_notMem.1 hν
    filter_upwards [this] with t ht using not_lt.1 ht
  have hmom := lintegral_lapMom_boundary hν hδ hG hfin hGZ
  set D : ℕ → ℝ := fun k => iteratedDeriv k G β₀ / (-2 * π) ^ k with hD
  obtain ⟨r, hr⟩ := hG.hasFPowerSeriesAt
  obtain ⟨σ, hσ0, hσr⟩ : ∃ σ : ℝ, 0 < σ ∧ ENNReal.ofReal σ < r := by
    obtain ⟨s, hs0, hsr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hr.r_pos
    refine ⟨s, by exact_mod_cast hs0, ?_⟩
    rwa [ENNReal.ofReal_coe_nnreal]
  refine ⟨σ, hσ0, ?_⟩
  have hsum := hr.hasSum (y := -σ) (by
    rw [Metric.mem_eball, edist_zero_right]
    simpa [Real.eNorm_eq_ofReal_abs, abs_of_pos hσ0] using hσr)
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at hsum
  -- the terms
  set a : ℕ → ℝ := fun k => D k * (2 * π * σ) ^ k / (k.factorial : ℝ) with ha
  have hterm : ∀ k, iteratedDeriv k G β₀ / (k.factorial : ℝ) * (-σ) ^ k = a k := by
    intro k
    have hc : (-2 * π) ^ k ≠ 0 := pow_ne_zero _ (by have := Real.pi_pos; linarith)
    simp only [ha, hD]
    have : (2 * π * σ) ^ k = (-2 * π) ^ k * (-σ) ^ k := by
      rw [← mul_pow]; ring
    rw [this]; field_simp
  simp only [hterm] at hsum
  have hanonneg : ∀ k, 0 ≤ a k := fun k => by
    simp only [ha]; have := (hmom k).1; positivity
  have hsumm : Summable a := hsum.summable
  -- Tonelli
  set Fk : ℕ → ℝ → ℝ≥0∞ := fun k t =>
    ENNReal.ofReal ((2 * π * σ) ^ k / (k.factorial : ℝ) * lapMom k β₀ t) with hFk
  have hmeas : ∀ k, Measurable (Fk k) := fun k =>
    ENNReal.measurable_ofReal.comp ((continuous_const.mul (continuous_lapMom k β₀)).measurable)
  have hlint : ∀ k, ∫⁻ t, Fk k t ∂ν = ENNReal.ofReal (a k) := by
    intro k
    have hc : 0 ≤ (2 * π * σ) ^ k / (k.factorial : ℝ) := by positivity
    simp only [hFk]
    simp_rw [ENNReal.ofReal_mul hc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, (hmom k).2, ← ENNReal.ofReal_mul hc]
    simp only [ha, hD]; ring_nf
  have hpt : ∀ᵐ t ∂ν, ∑' k, Fk k t = ENNReal.ofReal (Real.exp (-2 * π * (β₀ - σ) * t)) := by
    filter_upwards [hae] with t ht
    have hexp : HasSum (fun k : ℕ => (2 * π * σ * t) ^ k / (k.factorial : ℝ))
        (Real.exp (2 * π * σ * t)) := by
      have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (2 * π * σ * t)
      rwa [← Real.exp_eq_exp_ℝ] at this
    have hnn : ∀ k, 0 ≤ (2 * π * σ) ^ k / (k.factorial : ℝ) * lapMom k β₀ t := fun k => by
      unfold lapMom; positivity
    have hsh : HasSum (fun k => (2 * π * σ) ^ k / (k.factorial : ℝ) * lapMom k β₀ t)
        (Real.exp (-2 * π * (β₀ - σ) * t)) := by
      have := hexp.mul_right (Real.exp (-2 * π * β₀ * t))
      have e1 : Real.exp (2 * π * σ * t) * Real.exp (-2 * π * β₀ * t) =
          Real.exp (-2 * π * (β₀ - σ) * t) := by rw [← Real.exp_add]; ring_nf
      rw [e1] at this
      convert this using 1
      funext k
      unfold lapMom
      rw [mul_pow]; ring
    simp only [hFk]
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsh.summable, hsh.tsum_eq]
  have hlt : ∫⁻ t, ENNReal.ofReal (Real.exp (-2 * π * (β₀ - σ) * t)) ∂ν =
      ENNReal.ofReal (G (β₀ - σ)) := by
    rw [← lintegral_congr_ae hpt, lintegral_tsum (fun k => (hmeas k).aemeasurable)]
    simp_rw [hlint]
    rw [← ENNReal.ofReal_tsum_of_nonneg hanonneg hsumm, hsum.tsum_eq, ← sub_eq_add_neg]
  have hmeas' : AEStronglyMeasurable (fun t => Real.exp (-2 * π * (β₀ - σ) * t)) ν :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-2 * π * (β₀ - σ) * t)).aestronglyMeasurable
  refine ⟨hmeas', ?_⟩
  unfold HasFiniteIntegral
  have : ∀ t, ‖Real.exp (-2 * π * (β₀ - σ) * t)‖ₑ = ENNReal.ofReal (Real.exp (-2 * π * (β₀ - σ) * t)) :=
    fun t => Real.eNorm_eq_ofReal (Real.exp_pos _).le
  simp_rw [this, hlt]
  exact ENNReal.ofReal_lt_top

/-! ### The theorem -/

lemma analyticAt_rpow_neg (w : ℝ) {β : ℝ} (hβ : 0 < β) : AnalyticAt ℝ (fun x : ℝ => x ^ (-w)) β := by
  have h : AnalyticAt ℝ (fun x : ℝ => Real.exp (Real.log x * (-w))) β :=
    (analyticAt_rexp.comp ((analyticAt_log hβ).mul analyticAt_const) : _)
  refine h.congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds hβ] with x hx
  rw [Real.rpow_def_of_pos hx]

/-- `Z` is real analytic on `(c, ∞)` once it is finite there. -/
lemma analyticOnNhd_lapZ {ν : Measure ℝ} {c : ℝ} (hfin : ∀ β, c < β → LapFin ν β) :
    AnalyticOnNhd ℝ (lapZ ν) (Ioi c) := by
  have h : Ioi c ⊆ interior (integrableExpSet lapX ν) :=
    interior_maximal (fun x hx => mem_integrableExpSet_lapX.2 (hfin x hx)) isOpen_Ioi
  have := (analyticOnNhd_mgf (X := lapX) (μ := ν)).mono h
  simpa only [funext (mgf_lapX ν)] using this

/-- The right-hand side of the crossing identity, as a function of `β`. -/
noncomputable def lapG (w : ℝ) (v : ℝ → ℝ) (ν : Measure ℝ) (β : ℝ) : ℝ :=
  β ^ (-w) * (lapZ ν (1 / β) + v (1 / β)) - v β

lemma analyticAt_lapG {w : ℝ} {v : ℝ → ℝ} (hv : AnalyticOnNhd ℝ v (Ioi 0)) {ν : Measure ℝ} {c : ℝ}
    (hfin : ∀ β, c < β → LapFin ν β) {β : ℝ} (hβ : 0 < β) (hβc : c < 1 / β) :
    AnalyticAt ℝ (lapG w v ν) β := by
  have hinv : AnalyticAt ℝ (fun x : ℝ => 1 / x) β := analyticAt_const.div analyticAt_id hβ.ne'
  have hZ : AnalyticAt ℝ (fun x : ℝ => lapZ ν (1 / x)) β :=
    (analyticOnNhd_lapZ hfin (1 / β) hβc).comp hinv
  have hv' : AnalyticAt ℝ (fun x : ℝ => v (1 / x)) β :=
    (hv (1 / β) (by simpa using hβ)).comp hinv
  exact ((analyticAt_rpow_neg w hβ).mul (hZ.add hv')).sub (hv β hβ)

/-- **Lemma LP-A** (`ds:cont`).  Let `w > 0`, `v` real analytic on `(0, ∞)`, `ν` a measure on
`[0, ∞)` and `Z(β) = ∫ e^{-2πβt} dν`.  If `Z(s) < ∞` for some `s ∈ (0, 1)` and
`Z(β) + v(β) = β^{-w} [Z(1/β) + v(1/β)]` for `s < β < 1/s`, then `Z(β) < ∞` and the identity
holds for every `β > 0`. -/
theorem ds_cont {w : ℝ} {v : ℝ → ℝ} (hv : AnalyticOnNhd ℝ v (Ioi 0))
    {ν : Measure ℝ} (hν : ν (Iio 0) = 0) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hZs : LapFin ν s)
    (hcross : ∀ β, s < β → β < 1 / s →
      lapZ ν β + v β = β ^ (-w) * (lapZ ν (1 / β) + v (1 / β))) :
    (∀ β, 0 < β → LapFin ν β) ∧
      ∀ β, 0 < β → lapZ ν β + v β = β ^ (-w) * (lapZ ν (1 / β) + v (1 / β)) := by
  have hcrossG : ∀ β, s < β → β < 1 / s → lapZ ν β = lapG w v ν β := by
    intro β h1 h2
    unfold lapG; linarith [hcross β h1 h2]
  -- Step 1: all positive temperatures have finite Laplace transform
  have hall : ∀ β, 0 < β → LapFin ν β := by
    by_contra hcon
    push Not at hcon
    obtain ⟨β₁, hβ₁0, hβ₁⟩ := hcon
    set S : Set ℝ := {β | 0 < β ∧ LapFin ν β} with hS
    have hSne : S.Nonempty := ⟨s, hs0, hZs⟩
    have hSbdd : BddBelow S := ⟨0, fun β hβ => hβ.1.le⟩
    set c : ℝ := sInf S with hc
    have hc1 : β₁ ≤ c := by
      refine le_csInf hSne fun β hβ => ?_
      by_contra hlt
      exact hβ₁ (hβ.2.mono hν (not_le.1 hlt).le)
    have hc0 : 0 < c := hβ₁0.trans_le hc1
    have hcs : c ≤ s := csInf_le hSbdd ⟨hs0, hZs⟩
    have hc1' : c < 1 := hcs.trans_lt hs1
    have hcfin : ∀ β, c < β → LapFin ν β := by
      intro β hβ
      obtain ⟨β', hβ'S, hβ'lt⟩ := exists_lt_of_csInf_lt hSne (hc ▸ hβ : sInf S < β)
      exact hβ'S.2.mono hν hβ'lt.le
    have hcneg : ∀ β, 0 < β → β < c → ¬ LapFin ν β := by
      intro β hβ0 hβc hfin
      exact absurd (csInf_le hSbdd ⟨hβ0, hfin⟩) (not_le.2 hβc)
    have hcinv : c < 1 / c := by
      rw [lt_div_iff₀ hc0]; nlinarith only [hc0, hc1']
    -- continuation on `(c, 1/c)`
    have hZan : AnalyticOnNhd ℝ (lapZ ν) (Ioo c (1 / c)) :=
      (analyticOnNhd_lapZ hcfin).mono Ioo_subset_Ioi_self
    have hGan : AnalyticOnNhd ℝ (lapG w v ν) (Ioo c (1 / c)) := by
      intro β hβ
      have hβ0 : 0 < β := hc0.trans hβ.1
      refine analyticAt_lapG hv hcfin hβ0 ?_
      have := hβ.2
      rw [lt_div_iff₀ hβ0]
      rw [lt_div_iff₀ hc0] at this
      nlinarith only [this]
    have h1mem : (1 : ℝ) ∈ Ioo c (1 / c) :=
      ⟨by linarith, by rw [lt_div_iff₀ hc0]; linarith⟩
    have hnhds : lapZ ν =ᶠ[𝓝 (1 : ℝ)] lapG w v ν := by
      have : Ioo s (1 / s) ∈ 𝓝 (1 : ℝ) := isOpen_Ioo.mem_nhds
        ⟨hs1, by rw [lt_div_iff₀ hs0]; linarith⟩
      exact Filter.eventuallyEq_of_mem this fun x hx => hcrossG x hx.1 hx.2
    have hEq := hZan.eqOn_of_preconnected_of_eventuallyEq hGan isPreconnected_Ioo h1mem hnhds
    -- Landau step at `c`
    obtain ⟨σ, hσ0, hσ⟩ := landau_step hν (β₀ := c) (δ := 1 / c - c) (sub_pos.2 hcinv)
      (G := lapG w v ν) (analyticAt_lapG hv hcfin hc0 hcinv)
      (fun β hβ => hcfin β hβ.1)
      (fun β hβ => (hEq (by simpa using hβ)).symm)
    have hfinal : LapFin ν (max (c - σ) (c / 2)) :=
      hσ.mono hν (le_max_left _ _)
    exact hcneg _ (lt_max_of_lt_right (by linarith))
      (max_lt (by linarith) (by linarith)) hfinal
  refine ⟨hall, ?_⟩
  -- Step 2: the identity at every `β > 0`
  have hZan : AnalyticOnNhd ℝ (lapZ ν) (Ioi 0) := analyticOnNhd_lapZ (c := 0) hall
  have hGan : AnalyticOnNhd ℝ (lapG w v ν) (Ioi 0) := fun β hβ =>
    analyticAt_lapG hv (c := 0) hall hβ (by simpa using hβ)
  have hnhds : lapZ ν =ᶠ[𝓝 (1 : ℝ)] lapG w v ν := by
    have : Ioo s (1 / s) ∈ 𝓝 (1 : ℝ) := isOpen_Ioo.mem_nhds
      ⟨hs1, by rw [lt_div_iff₀ hs0]; linarith⟩
    exact Filter.eventuallyEq_of_mem this fun x hx => hcrossG x hx.1 hx.2
  have hEq := hZan.eqOn_of_preconnected_of_eventuallyEq hGan isPreconnected_Ioi
    (show (1 : ℝ) ∈ Ioi 0 from one_pos) hnhds
  intro β hβ
  have := hEq (show β ∈ Ioi 0 from hβ)
  unfold lapG at this
  linarith

/-- **Lemma LP-A** (`ds:cont`) for a complex source `v` holomorphic on `{Re β > 0}`, exactly as in
the paper (the identity is read in `ℂ`).  The real part is `ds_cont`; the imaginary part is a
real-analytic identity on `(0, ∞)`, propagated by the identity theorem. -/
theorem ds_cont_complex {w : ℝ} {v : ℂ → ℂ} (hv : DifferentiableOn ℂ v {z : ℂ | 0 < z.re})
    {ν : Measure ℝ} (hν : ν (Iio 0) = 0) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hZs : LapFin ν s)
    (hcross : ∀ β : ℝ, s < β → β < 1 / s →
      (lapZ ν β : ℂ) + v β = ((β : ℂ) ^ (-(w : ℂ))) * ((lapZ ν (1 / β) : ℂ) + v ((1 / β : ℝ) : ℂ))) :
    (∀ β, 0 < β → LapFin ν β) ∧
      ∀ β : ℝ, 0 < β →
        (lapZ ν β : ℂ) + v β = ((β : ℂ) ^ (-(w : ℂ))) * ((lapZ ν (1 / β) : ℂ) + v ((1 / β : ℝ) : ℂ)) := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hvan : AnalyticOnNhd ℂ v {z : ℂ | 0 < z.re} := hv.analyticOnNhd hopen
  have hre : AnalyticOnNhd ℝ (fun x : ℝ => (v x).re) (Ioi 0) := fun x hx =>
    (hvan x (by simpa using hx)).re_ofReal
  have him : AnalyticOnNhd ℝ (fun x : ℝ => (v x).im) (Ioi 0) := fun x hx =>
    (hvan x (by simpa using hx)).im_ofReal
  have hcpow : ∀ β : ℝ, 0 < β → (β : ℂ) ^ (-(w : ℂ)) = ((β ^ (-w) : ℝ) : ℂ) := by
    intro β hβ
    rw [Complex.ofReal_cpow hβ.le]; push_cast; rfl
  -- real and imaginary parts of the hypothesis
  have hcr : ∀ β, s < β → β < 1 / s →
      lapZ ν β + (v β).re = β ^ (-w) * (lapZ ν (1 / β) + (v ((1 / β : ℝ) : ℂ)).re) := by
    intro β h1 h2
    have hβ0 : 0 < β := hs0.trans h1
    have := congrArg Complex.re (hcross β h1 h2)
    rw [hcpow β hβ0] at this
    simpa [Complex.mul_re] using this
  have hci : ∀ β, s < β → β < 1 / s →
      (v β).im = β ^ (-w) * (v ((1 / β : ℝ) : ℂ)).im := by
    intro β h1 h2
    have hβ0 : 0 < β := hs0.trans h1
    have := congrArg Complex.im (hcross β h1 h2)
    rw [hcpow β hβ0] at this
    simpa [Complex.mul_im] using this
  obtain ⟨hall, hreall⟩ := ds_cont (v := fun x : ℝ => (v x).re) hre hν hs0 hs1 hZs hcr
  refine ⟨hall, fun β hβ => ?_⟩
  -- the imaginary identity on `(0, ∞)`
  have hHan : AnalyticOnNhd ℝ (fun x : ℝ => (v x).im - x ^ (-w) * (v ((1 / x : ℝ) : ℂ)).im) (Ioi 0) := by
    intro x hx
    have hx0 : 0 < x := hx
    have hinv : AnalyticAt ℝ (fun y : ℝ => 1 / y) x := analyticAt_const.div analyticAt_id hx0.ne'
    have h2 : AnalyticAt ℝ (fun y : ℝ => (v ((1 / y : ℝ) : ℂ)).im) x :=
      (him (1 / x) (by simpa using hx0)).comp hinv
    exact (him x hx).sub ((analyticAt_rpow_neg w hx0).mul h2)
  have hnh : (fun x : ℝ => (v x).im - x ^ (-w) * (v ((1 / x : ℝ) : ℂ)).im) =ᶠ[𝓝 (1 : ℝ)] 0 := by
    have : Ioo s (1 / s) ∈ 𝓝 (1 : ℝ) := isOpen_Ioo.mem_nhds
      ⟨hs1, by rw [lt_div_iff₀ hs0]; linarith⟩
    filter_upwards [this] with x hx
    simp [hci x hx.1 hx.2]
  have hzero := hHan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioi
    (show (1 : ℝ) ∈ Ioi 0 from one_pos) hnh (show β ∈ Ioi 0 from hβ)
  simp only [Pi.zero_apply] at hzero
  have hre' := hreall β hβ
  rw [hcpow β hβ]
  apply Complex.ext
  · simpa [Complex.mul_re] using hre'
  · simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, zero_add,
      zero_mul, add_zero]
    linarith

/-- info: 'FormalResearch.ModularBootstrap.LP.ds_cont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ds_cont

/-- info: 'FormalResearch.ModularBootstrap.LP.ds_cont_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ds_cont_complex

end FormalResearch.ModularBootstrap.LP
