module

public import FormalResearch.ModularBootstrap.LP.LaguerreGen
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Lemma LP-C (`ds:cay`): the Cayley identity against a measure

`CFT/modular_bootstrap/paper/dual_spectrum_limit.tex`, Lemma LP-C (line 7).  For a positive measure
`ν` on `[0, ∞)`, `θ ∈ (0,1)`, `s_θ = (1-θ)/(1+θ)` and `∫ e^{-2π s_θ t} dν < ∞`, for `|ϖ| < θ` and
`β = (1+ϖ)/(1-ϖ)` (equivalently `β ∈ (s_θ, 1/s_θ)` and `ϖ = (β-1)/(β+1)`):

`∫ Ξ_β dν = 2 (1-ϖ)^w ∑_{k odd} ϖ^k ∫ ψ_k dν`

with absolute convergence (`ds_cay_series`).  Hence for two such measures the crossing identity
`∫ Ξ_β dν = ∫ Ξ_β dν'` on `(s_θ, 1/s_θ)` holds iff `∫ ψ_k dν = ∫ ψ_k dν'` for every odd `k`
(`ds_cay_iff`; uniqueness of power series coefficients, `coeff_zero_of_hasSum_zero`).  Here
`Ξ_β = xiW w β` and `ψ_k = lagPsi w k` of `LP.LaguerreGen`; the pointwise Cayley expansion
(`hasSum_cayley`) and the Cauchy bound (`abs_lagPsi_le`) are proved there.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open scoped ENNReal NNReal

namespace FormalResearch.ModularBootstrap.LP

/-- `s_θ = (1-θ)/(1+θ)`. -/
noncomputable def sTheta (θ : ℝ) : ℝ := (1 - θ) / (1 + θ)

lemma continuous_lagL (w : ℝ) (k : ℕ) : Continuous (lagL w k) :=
  (lagPoly w k).continuous

lemma continuous_lagPsi (w : ℝ) (k : ℕ) : Continuous (lagPsi w k) := by
  unfold lagPsi
  exact (by fun_prop : Continuous fun t : ℝ => Real.exp (-2 * Real.pi * t)).mul
    ((continuous_lagL w k).comp (by fun_prop))

lemma continuous_xiW (w β : ℝ) : Continuous (xiW w β) := by
  unfold xiW; fun_prop

/-! ### Uniqueness of power series coefficients -/

/-- A real power series that sums to zero on `(-r, r)` has all coefficients zero. -/
lemma coeff_zero_of_hasSum_zero {c : ℕ → ℝ} {r : ℝ} (hr : 0 < r)
    (h : ∀ x : ℝ, |x| < r → HasSum (fun k => c k * x ^ k) 0) : ∀ k, c k = 0 := by
  set p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ c with hp
  have hrad : ENNReal.ofReal r ≤ p.radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun r' hr' => ?_
    have hr'r : (r' : ℝ) < r := by
      rw [← ENNReal.ofReal_coe_nnreal] at hr'
      exact (ENNReal.ofReal_lt_ofReal_iff hr).1 hr'
    refine p.le_radius_of_tendsto (l := 0) ?_
    have hsum := h r' (by rw [NNReal.abs_eq]; exact hr'r)
    have ht : Tendsto (fun k => c k * (r' : ℝ) ^ k) atTop (𝓝 0) := hsum.summable.tendsto_atTop_zero
    have ht' := ht.abs
    simp only [abs_zero] at ht'
    refine ht'.congr fun k => ?_
    rw [hp, FormalMultilinearSeries.ofScalars_norm, abs_mul, abs_pow, NNReal.abs_eq]
    simp
  have hball : HasFPowerSeriesOnBall (fun _ : ℝ => (0 : ℝ)) p 0 (ENNReal.ofReal r) :=
    { r_le := hrad
      r_pos := ENNReal.ofReal_pos.2 hr
      hasSum := by
        intro y hy
        have hy' : |y| < r := by
          rw [Metric.mem_eball, edist_zero_right] at hy
          have : ‖y‖ₑ = ENNReal.ofReal |y| := by simp [Real.eNorm_eq_ofReal_abs]
          rw [this] at hy
          exact (ENNReal.ofReal_lt_ofReal_iff hr).1 hy
        have := h y hy'
        simpa [hp, FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using this }
  have h0 := hball.hasFPowerSeriesAt.eq_zero
  have := (FormalMultilinearSeries.ofScalars_series_eq_zero (E := ℝ) (c := c)).1 (by rw [← hp]; exact h0)
  exact fun k => congrFun this k

/-- Odd form: if `∑ x^{2n+1} d_n = 0` on `(-r, r)` then `d = 0`. -/
lemma odd_coeff_zero {d : ℕ → ℝ} {r : ℝ} (hr : 0 < r)
    (h : ∀ x : ℝ, |x| < r → HasSum (fun n => x ^ (2 * n + 1) * d n) 0) : ∀ n, d n = 0 := by
  set c : ℕ → ℝ := fun k => if k % 2 = 1 then d (k / 2) else 0 with hc
  have hinj : Function.Injective (fun n : ℕ => 2 * n + 1) := fun a b hab => by simpa using hab
  have hc0 : ∀ x : ℝ, |x| < r → HasSum (fun k => c k * x ^ k) 0 := by
    intro x hx
    have := h x hx
    have hf : ∀ k ∉ Set.range (fun n : ℕ => 2 * n + 1), c k * x ^ k = 0 := by
      intro k hk
      have : k % 2 ≠ 1 := fun hk1 => hk ⟨k / 2, by show 2 * (k / 2) + 1 = k; omega⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hf).1 ?_
    convert this using 1
    funext n
    have h1 : (2 * n + 1) % 2 = 1 := by omega
    have h2 : (2 * n + 1) / 2 = n := by omega
    simp only [Function.comp_apply, hc, h1, h2, ite_true]
    ring
  intro n
  have := coeff_zero_of_hasSum_zero hr hc0 (2 * n + 1)
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  simpa only [hc, h1, h2, ite_true] using this

/-! ### The Cayley series against a measure -/

lemma sTheta_lt_beta {θ ϖ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hϖ : |ϖ| < θ) :
    sTheta θ < (1 + ϖ) / (1 - ϖ) ∧ sTheta θ < (1 - ϖ) / (1 + ϖ) := by
  have h := abs_lt.1 hϖ
  have h1 : 0 < 1 - ϖ := by linarith
  have h2 : 0 < 1 + ϖ := by linarith
  have h3 : 0 < 1 + θ := by linarith
  unfold sTheta
  constructor
  · rw [div_lt_div_iff₀ h3 h1]; nlinarith only [h.1, h.2]
  · rw [div_lt_div_iff₀ h3 h2]; nlinarith only [h.1, h.2]

lemma abs_xiW_le {w β θ t : ℝ} (hβ : sTheta θ ≤ β) (hβ' : sTheta θ ≤ 1 / β) (hβ0 : 0 < β)
    (ht : 0 ≤ t) :
    |xiW w β t| ≤ (1 + β ^ (-w)) * Real.exp (-2 * Real.pi * sTheta θ * t) := by
  unfold xiW
  have e1 : Real.exp (-2 * Real.pi * β * t) ≤ Real.exp (-2 * Real.pi * sTheta θ * t) := by
    apply Real.exp_le_exp.2
    have : 0 ≤ 2 * Real.pi * t := by positivity
    nlinarith only [this, hβ]
  have e2 : Real.exp (-2 * Real.pi * t / β) ≤ Real.exp (-2 * Real.pi * sTheta θ * t) := by
    apply Real.exp_le_exp.2
    have : -2 * Real.pi * t / β = -2 * Real.pi * t * (1 / β) := by ring
    rw [this]
    have : 0 ≤ 2 * Real.pi * t := by positivity
    nlinarith only [this, hβ']
  have hb : 0 ≤ β ^ (-w) := (Real.rpow_pos_of_pos hβ0 _).le
  have p1 := Real.exp_pos (-2 * Real.pi * β * t)
  have p2 := Real.exp_pos (-2 * Real.pi * t / β)
  refine (abs_sub _ _).trans ?_
  rw [abs_of_pos p1, abs_of_nonneg (mul_nonneg hb p2.le)]
  nlinarith only [e1, e2, hb, mul_le_mul_of_nonneg_left e2 hb]

/-- **Lemma LP-C** (`ds:cay`), series form.  Let `ν` be a measure on `[0, ∞)` with
`∫ e^{-2π s_θ t} dν < ∞`, `|ϖ| < θ` and `β = (1+ϖ)/(1-ϖ)`.  Then every `ψ_k` and `Ξ_β` is
`ν`-integrable and `∫ Ξ_β dν = 2 (1-ϖ)^w ∑_{k odd} ϖ^k ∫ ψ_k dν`, the series converging
absolutely. -/
theorem ds_cay_series {w : ℝ} (hw : 0 < w) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {ν : Measure ℝ} (hν : ν (Iio 0) = 0)
    (hint : Integrable (fun t => Real.exp (-2 * Real.pi * sTheta θ * t)) ν)
    {ϖ β : ℝ} (hϖ : |ϖ| < θ) (hβ : β = (1 + ϖ) / (1 - ϖ)) :
    (∀ k, Integrable (lagPsi w k) ν) ∧ Integrable (xiW w β) ν ∧
      Summable (fun n : ℕ => |ϖ ^ (2 * n + 1) * ∫ t, lagPsi w (2 * n + 1) t ∂ν|) ∧
      HasSum (fun n : ℕ => ϖ ^ (2 * n + 1) * ∫ t, lagPsi w (2 * n + 1) t ∂ν)
        ((∫ t, xiW w β t ∂ν) / (2 * (1 - ϖ) ^ w)) := by
  have hae : ∀ᵐ t ∂ν, 0 ≤ t := by
    have : ∀ᵐ t ∂ν, t ∉ Iio 0 := measure_eq_zero_iff_ae_notMem.1 hν
    filter_upwards [this] with t ht using not_lt.1 ht
  have hθ : |ϖ| < 1 := hϖ.trans hθ1
  have hϖ1 := abs_lt.1 hθ
  have h1ϖ : 0 < 1 - ϖ := by linarith
  have hβ0 : 0 < β := by rw [hβ]; have : 0 < 1 + ϖ := by linarith
                         positivity
  set A : ℝ := (1 - θ) ^ (-w) with hA
  have hApos : 0 < A := Real.rpow_pos_of_pos (by linarith) _
  set r : ℝ := |ϖ| / θ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one hθ0]; exact hϖ
  have hΨ : ∀ k, Integrable (lagPsi w k) ν := fun k =>
    Integrable.mono' (hint.const_mul (A * θ⁻¹ ^ k)) (continuous_lagPsi w k).aestronglyMeasurable (by
      filter_upwards [hae] with t ht
      rw [Real.norm_eq_abs]
      exact abs_lagPsi_le hw hθ0 hθ1 ht k)
  have hbd : ∀ n : ℕ, ∀ᵐ t ∂ν, ‖ϖ ^ (2 * n + 1) * lagPsi w (2 * n + 1) t‖ ≤
      A * r ^ (2 * n + 1) * Real.exp (-2 * Real.pi * sTheta θ * t) := by
    intro n
    filter_upwards [hae] with t ht
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
    have := abs_lagPsi_le hw hθ0 hθ1 ht (2 * n + 1)
    have hrr : r ^ (2 * n + 1) = |ϖ| ^ (2 * n + 1) * θ⁻¹ ^ (2 * n + 1) := by
      rw [hr, div_eq_mul_inv, mul_pow]
    calc |ϖ| ^ (2 * n + 1) * |lagPsi w (2 * n + 1) t|
        ≤ |ϖ| ^ (2 * n + 1) * (A * θ⁻¹ ^ (2 * n + 1) * Real.exp (-2 * Real.pi * sTheta θ * t)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = A * r ^ (2 * n + 1) * Real.exp (-2 * Real.pi * sTheta θ * t) := by rw [hrr]; ring
  have hFint : ∀ n : ℕ, Integrable (fun t => ϖ ^ (2 * n + 1) * lagPsi w (2 * n + 1) t) ν :=
    fun n => (hΨ _).const_mul _
  set I : ℝ := ∫ t, Real.exp (-2 * Real.pi * sTheta θ * t) ∂ν with hI
  have hI0 : 0 ≤ I := integral_nonneg fun t => (Real.exp_pos _).le
  have hnorm : ∀ n : ℕ, ∫ t, ‖ϖ ^ (2 * n + 1) * lagPsi w (2 * n + 1) t‖ ∂ν ≤
      (A * I * r) * (r ^ 2) ^ n := by
    intro n
    have := integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
      (hint.const_mul (A * r ^ (2 * n + 1))) (hbd n)
    rw [integral_const_mul] at this
    calc _ ≤ A * r ^ (2 * n + 1) * I := this
      _ = (A * I * r) * (r ^ 2) ^ n := by rw [pow_succ, pow_mul]; ring
  have hsumm : Summable fun n : ℕ => ∫ t, ‖ϖ ^ (2 * n + 1) * lagPsi w (2 * n + 1) t‖ ∂ν := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) hnorm ?_
    exact (summable_geometric_of_lt_one (by positivity) (by nlinarith only [hr0, hr1])).mul_left _
  have hHas := hasSum_integral_of_summable_integral_norm hFint hsumm
  have hpt : ∀ t, ∑' n : ℕ, ϖ ^ (2 * n + 1) * lagPsi w (2 * n + 1) t =
      xiW w β t / (2 * (1 - ϖ) ^ w) := fun t => (hasSum_cayley hw hθ hβ t).tsum_eq
  have hxi : Integrable (xiW w β) ν := by
    obtain ⟨hb1, hb2⟩ := sTheta_lt_beta hθ0 hθ1 hϖ
    rw [← hβ] at hb1
    have hinv : 1 / β = (1 - ϖ) / (1 + ϖ) := by rw [hβ, one_div, inv_div]
    rw [← hinv] at hb2
    exact Integrable.mono' (hint.const_mul (1 + β ^ (-w))) (continuous_xiW w β).aestronglyMeasurable (by
      filter_upwards [hae] with t ht
      rw [Real.norm_eq_abs]
      exact abs_xiW_le hb1.le hb2.le hβ0 ht)
  have hval : ∫ t, ∑' n : ℕ, ϖ ^ (2 * n + 1) * lagPsi w (2 * n + 1) t ∂ν =
      (∫ t, xiW w β t ∂ν) / (2 * (1 - ϖ) ^ w) := by
    simp_rw [hpt]
    rw [integral_div]
  refine ⟨hΨ, hxi, ?_, ?_⟩
  · have : Summable fun n : ℕ => ‖∫ t, ϖ ^ (2 * n + 1) * lagPsi w (2 * n + 1) t ∂ν‖ :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_integral_le_integral_norm _) hsumm
    simpa [integral_const_mul] using this
  · simpa only [integral_const_mul, hval] using hHas

lemma sTheta_pos {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) : 0 < sTheta θ := by
  unfold sTheta; apply div_pos <;> linarith

lemma one_div_sTheta {θ : ℝ} : 1 / sTheta θ = (1 + θ) / (1 - θ) := by
  unfold sTheta; rw [one_div_div]

/-- The Cayley change of variable `β ↔ ϖ`. -/
lemma varpi_of_beta {θ β : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (h1 : sTheta θ < β)
    (h2 : β < 1 / sTheta θ) :
    |(β - 1) / (β + 1)| < θ ∧ β = (1 + (β - 1) / (β + 1)) / (1 - (β - 1) / (β + 1)) := by
  have hs0 := sTheta_pos hθ0 hθ1
  have hβ0 : 0 < β := hs0.trans h1
  have hb1 : 0 < β + 1 := by linarith
  have h1' : (1 - θ) < β * (1 + θ) := by
    have := h1; unfold sTheta at this
    rwa [div_lt_iff₀ (by linarith)] at this
  have h2' : β * (1 - θ) < 1 + θ := by
    have := h2; rw [one_div_sTheta, lt_div_iff₀ (by linarith)] at this; linarith
  refine ⟨?_, ?_⟩
  · rw [abs_lt]
    constructor
    · rw [lt_div_iff₀ hb1]; nlinarith only [h1']
    · rw [div_lt_iff₀ hb1]; nlinarith only [h2']
  · field_simp
    ring

lemma beta_of_varpi {θ ϖ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hϖ : |ϖ| < θ) :
    sTheta θ < (1 + ϖ) / (1 - ϖ) ∧ (1 + ϖ) / (1 - ϖ) < 1 / sTheta θ := by
  have h := abs_lt.1 hϖ
  have h1 : 0 < 1 - ϖ := by linarith
  refine ⟨(sTheta_lt_beta hθ0 hθ1 hϖ).1, ?_⟩
  rw [one_div_sTheta, div_lt_div_iff₀ h1 (by linarith)]
  nlinarith only [h.1, h.2]

/-- **Lemma LP-C** (`ds:cay`), the equivalence.  For two measures `ν, ν'` on `[0, ∞)` with
`∫ e^{-2π s_θ t} < ∞`, the crossing identity `∫ Ξ_β dν = ∫ Ξ_β dν'` on `β ∈ (s_θ, 1/s_θ)` holds
iff `∫ ψ_k dν = ∫ ψ_k dν'` for every odd `k`. -/
theorem ds_cay_iff {w : ℝ} (hw : 0 < w) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {ν ν' : Measure ℝ} (hν : ν (Iio 0) = 0) (hν' : ν' (Iio 0) = 0)
    (hint : Integrable (fun t => Real.exp (-2 * Real.pi * sTheta θ * t)) ν)
    (hint' : Integrable (fun t => Real.exp (-2 * Real.pi * sTheta θ * t)) ν') :
    (∀ β, sTheta θ < β → β < 1 / sTheta θ → ∫ t, xiW w β t ∂ν = ∫ t, xiW w β t ∂ν') ↔
      ∀ k : ℕ, Odd k → ∫ t, lagPsi w k t ∂ν = ∫ t, lagPsi w k t ∂ν' := by
  constructor
  · intro hcross
    have hz : ∀ n : ℕ, ∫ t, lagPsi w (2 * n + 1) t ∂ν - ∫ t, lagPsi w (2 * n + 1) t ∂ν' = 0 := by
      refine odd_coeff_zero hθ0 (d := fun n => ∫ t, lagPsi w (2 * n + 1) t ∂ν -
        ∫ t, lagPsi w (2 * n + 1) t ∂ν') (fun ϖ hϖ => ?_)
      obtain ⟨hb1, hb2⟩ := beta_of_varpi hθ0 hθ1 hϖ
      obtain ⟨-, -, -, hs⟩ := ds_cay_series hw hθ0 hθ1 hν hint hϖ rfl
      obtain ⟨-, -, -, hs'⟩ := ds_cay_series hw hθ0 hθ1 hν' hint' hϖ rfl
      have := hs.sub hs'
      rw [← sub_div, hcross _ hb1 hb2, sub_self, zero_div] at this
      simpa [mul_sub] using this
    rintro k ⟨n, rfl⟩
    exact sub_eq_zero.1 (hz n)
  · intro hmom β hb1 hb2
    obtain ⟨hϖ, hβ⟩ := varpi_of_beta hθ0 hθ1 hb1 hb2
    obtain ⟨-, -, -, hs⟩ := ds_cay_series hw hθ0 hθ1 hν hint hϖ hβ
    obtain ⟨-, -, -, hs'⟩ := ds_cay_series hw hθ0 hθ1 hν' hint' hϖ hβ
    have hfun : (fun n : ℕ => ((β - 1) / (β + 1)) ^ (2 * n + 1) * ∫ t, lagPsi w (2 * n + 1) t ∂ν) =
        fun n : ℕ => ((β - 1) / (β + 1)) ^ (2 * n + 1) * ∫ t, lagPsi w (2 * n + 1) t ∂ν' := by
      funext n; rw [hmom (2 * n + 1) ⟨n, rfl⟩]
    rw [hfun] at hs
    have := hs.unique hs'
    have hpos : 0 < 2 * (1 - (β - 1) / (β + 1)) ^ w := by
      have h1 := abs_lt.1 (hϖ.trans hθ1)
      have : 0 < 1 - (β - 1) / (β + 1) := by linarith
      positivity
    exact (div_left_inj₀ hpos.ne').1 this

/-- `∫ Ξ_β dν = Z(β) - β^{-w} Z(1/β)` whenever both Laplace transforms are finite. -/
lemma integral_xiW {w β : ℝ} {ν : Measure ℝ}
    (h1 : Integrable (fun t => Real.exp (-2 * Real.pi * β * t)) ν)
    (h2 : Integrable (fun t => Real.exp (-2 * Real.pi * t / β)) ν) :
    ∫ t, xiW w β t ∂ν =
      ∫ t, Real.exp (-2 * Real.pi * β * t) ∂ν - β ^ (-w) * ∫ t, Real.exp (-2 * Real.pi * t / β) ∂ν := by
  unfold xiW
  rw [integral_sub h1 (h2.const_mul _), integral_const_mul]

/-- info: 'FormalResearch.ModularBootstrap.LP.ds_cay_series' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ds_cay_series

/-- info: 'FormalResearch.ModularBootstrap.LP.ds_cay_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ds_cay_iff

end FormalResearch.ModularBootstrap.LP
