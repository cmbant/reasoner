module

public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import FormalResearch.SignUncertainty.SphereAverage

/-!
# Uncertainty for compact supports

A continuous compactly supported `f : ℝ^{n+1} → ℂ` whose Fourier transform vanishes outside a ball is zero
(`fourier_compact_support_eq_zero`). Proof: for fixed `y` and a unit vector `v`, `t ↦ 𝓕 f (y + t v)` is the
restriction to `ℝ` of an entire function (`fourierEntire`, differentiable under the integral because `f` has
compact support) that vanishes for large `t`, hence is zero (identity theorem); so `𝓕 f = 0` and `f = 0` by
Fourier inversion.

Negative regression: compact support of `f` is needed (the Gaussian has `𝓕 f ≠ 0`, not compactly supported);
without the vanishing hypothesis every nonzero continuous compactly supported `f` is a counterexample.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped RealInnerProductSpace FourierTransform Real

namespace FormalResearch.SignUncertainty

variable {d : ℕ}

/-- The entire extension `z ↦ ∫ e^{-2πi(⟪x,y⟫ + z⟪x,v⟫)} f(x) dx` of `t ↦ 𝓕 f (y + t v)`. -/
noncomputable def fourierEntire (f : EuclSp d → ℂ) (y v : EuclSp d) (z : ℂ) : ℂ :=
  ∫ x, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (((⟪x, y⟫ : ℝ) : ℂ) + z * ((⟪x, v⟫ : ℝ) : ℂ))) * f x

lemma fourierEntire_ofReal (f : EuclSp d → ℂ) (y v : EuclSp d) (t : ℝ) :
    fourierEntire f y v (t : ℂ) = 𝓕 f (y + t • v) := by
  rw [fourier_eq_fchar]
  unfold fourierEntire fchar
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [inner_add_right, real_inner_smul_right]
  congr 2
  push_cast
  ring

/-- The exponent `-2πi(⟪x,y⟫ + z⟪x,v⟫)`. -/
noncomputable def entArg (y v : EuclSp d) (z : ℂ) (x : EuclSp d) : ℂ :=
  -(2 * (Real.pi : ℂ) * Complex.I) * (((⟪x, y⟫ : ℝ) : ℂ) + z * ((⟪x, v⟫ : ℝ) : ℂ))

/-- The `z`-derivative of the integrand. -/
noncomputable def entF' (f : EuclSp d → ℂ) (y v : EuclSp d) (z : ℂ) (x : EuclSp d) : ℂ :=
  (Complex.exp (entArg y v z x) * (-(2 * (Real.pi : ℂ) * Complex.I) * ((⟪x, v⟫ : ℝ) : ℂ))) * f x

lemma continuous_entArg (y v : EuclSp d) (z : ℂ) : Continuous (entArg y v z) := by
  unfold entArg; fun_prop

lemma norm_entF'_le {f : EuclSp d → ℂ} {ρ : ℝ} (hρ : ∀ x, f x ≠ 0 → ‖x‖ ≤ |ρ|) (y v : EuclSp d)
    {z₀ z : ℂ} (hz : ‖z - z₀‖ < 1) (x : EuclSp d) :
    ‖entF' f y v z x‖ ≤ (2 * Real.pi * (|ρ| * ‖v‖) *
      Real.exp (2 * Real.pi * (|ρ| * ‖v‖) * (‖z₀‖ + 1))) * ‖f x‖ := by
  by_cases hfx : f x = 0
  · simp [entF', hfx]
  · set m : ℝ := |ρ| * ‖v‖ with hm
    have hb : |⟪x, v⟫| ≤ m := (abs_real_inner_le_norm x v).trans
      (mul_le_mul_of_nonneg_right (hρ x hfx) (norm_nonneg v))
    have hzn : ‖z‖ ≤ ‖z₀‖ + 1 := by
      calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ ≤ ‖z₀‖ + 1 := by linarith
    have hre : (entArg y v z x).re = 2 * Real.pi * ⟪x, v⟫ * z.im := by
      unfold entArg
      simp [Complex.mul_re, Complex.mul_im]
      ring
    have h1 : ‖Complex.exp (entArg y v z x)‖ ≤ Real.exp (2 * Real.pi * m * (‖z₀‖ + 1)) := by
      rw [Complex.norm_exp, hre]
      refine Real.exp_le_exp.2 ?_
      have h2 : ⟪x, v⟫ * z.im ≤ m * (‖z₀‖ + 1) :=
        calc ⟪x, v⟫ * z.im ≤ |⟪x, v⟫ * z.im| := le_abs_self _
          _ = |⟪x, v⟫| * |z.im| := abs_mul _ _
          _ ≤ m * (‖z₀‖ + 1) :=
            mul_le_mul hb ((Complex.abs_im_le_norm z).trans hzn) (abs_nonneg _) (by positivity)
      have hπ := Real.pi_pos
      nlinarith
    have h3 : ‖-(2 * (Real.pi : ℂ) * Complex.I) * ((⟪x, v⟫ : ℝ) : ℂ)‖ ≤ 2 * Real.pi * m := by
      rw [norm_mul, norm_neg, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs]
      simp only [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, mul_one,
        abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_pos]
    have h4 : ‖Complex.exp (entArg y v z x)‖ *
        ‖-(2 * (Real.pi : ℂ) * Complex.I) * ((⟪x, v⟫ : ℝ) : ℂ)‖ ≤
        Real.exp (2 * Real.pi * m * (‖z₀‖ + 1)) * (2 * Real.pi * m) :=
      mul_le_mul h1 h3 (norm_nonneg _) (Real.exp_pos _).le
    unfold entF'
    rw [norm_mul, norm_mul]
    calc ‖Complex.exp (entArg y v z x)‖ * ‖-(2 * (Real.pi : ℂ) * Complex.I) * ((⟪x, v⟫ : ℝ) : ℂ)‖ *
          ‖f x‖ ≤ Real.exp (2 * Real.pi * m * (‖z₀‖ + 1)) * (2 * Real.pi * m) * ‖f x‖ :=
          mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
      _ = _ := by ring

lemma differentiable_fourierEntire {f : EuclSp d → ℂ} (hcont : Continuous f)
    (hsupp : HasCompactSupport f) (y v : EuclSp d) : Differentiable ℂ (fourierEntire f y v) := by
  intro z₀
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, tsupport f ⊆ closedBall (0 : EuclSp d) ρ :=
    hsupp.isCompact.isBounded.subset_closedBall 0
  have hρ' : ∀ x, f x ≠ 0 → ‖x‖ ≤ |ρ| := fun x hx => by
    have := hρ (subset_tsupport f (Function.mem_support.2 hx))
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_abs_self ρ)
  have hint : Integrable f := hcont.integrable_of_hasCompactSupport hsupp
  have hFc : ∀ z, Continuous (fun x => Complex.exp (entArg y v z x) * f x) := fun z =>
    (Complex.continuous_exp.comp (continuous_entArg y v z)).mul hcont
  have hF'c : ∀ z, Continuous (entF' f y v z) := fun z => by
    unfold entF'
    exact ((Complex.continuous_exp.comp (continuous_entArg y v z)).mul (by fun_prop)).mul hcont
  have hFint : Integrable (fun x => Complex.exp (entArg y v z₀ x) * f x) :=
    (hFc z₀).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_left (f := fun x => Complex.exp (entArg y v z₀ x)) hsupp)
  have hdiff : ∀ x, ∀ z ∈ ball z₀ 1, HasDerivAt (fun z => Complex.exp (entArg y v z x) * f x)
      (entF' f y v z x) z := by
    intro x z _
    have h1 : HasDerivAt (fun z : ℂ => entArg y v z x)
        (-(2 * (Real.pi : ℂ) * Complex.I) * ((⟪x, v⟫ : ℝ) : ℂ)) z := by
      have := (((hasDerivAt_id z).mul_const ((⟪x, v⟫ : ℝ) : ℂ)).const_add
        (((⟪x, y⟫ : ℝ) : ℂ))).const_mul (-(2 * (Real.pi : ℂ) * Complex.I))
      simpa [entArg] using this
    exact h1.cexp.mul_const (f x)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (s := ball z₀ 1)
    (F := fun z x => Complex.exp (entArg y v z x) * f x) (F' := entF' f y v)
    (bound := fun x => (2 * Real.pi * (|ρ| * ‖v‖) *
      Real.exp (2 * Real.pi * (|ρ| * ‖v‖) * (‖z₀‖ + 1))) * ‖f x‖) (x₀ := z₀)
    (ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => (hFc z).aestronglyMeasurable) hFint
    (hF'c z₀).aestronglyMeasurable
    (Eventually.of_forall fun x z hz => norm_entF'_le hρ' y v (mem_ball_iff_norm.1 hz) x)
    (hint.norm.const_mul _) (Eventually.of_forall hdiff)
  exact key.2.differentiableAt

/-- **Uncertainty for compact supports.** A continuous compactly supported `f : ℝ^{n+1} → ℂ` whose Fourier
transform vanishes on `‖y‖ ≥ R` is zero. -/
theorem fourier_compact_support_eq_zero {n : ℕ} {f : EuclSp (n + 1) → ℂ} (hcont : Continuous f)
    (hsupp : HasCompactSupport f) (R : ℝ) (hR : ∀ y : EuclSp (n + 1), R ≤ ‖y‖ → 𝓕 f y = 0) :
    f = 0 := by
  have hint : Integrable f := hcont.integrable_of_hasCompactSupport hsupp
  have hF0 : ∀ y : EuclSp (n + 1), 𝓕 f y = 0 := by
    intro y
    set v : EuclSp (n + 1) := EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) with hv
    have hvn : ‖v‖ = 1 := by rw [hv, PiLp.norm_single]; simp
    have hdiff := differentiable_fourierEntire hcont hsupp y v
    have han : AnalyticOnNhd ℂ (fourierEntire f y v) univ := fun z _ => hdiff.analyticAt z
    set T : ℝ := R + ‖y‖ with hT
    have hzero : ∀ t : ℝ, T ≤ t → fourierEntire f y v (t : ℂ) = 0 := by
      intro t ht
      rw [fourierEntire_ofReal]
      refine hR _ ?_
      have h1 : ‖t • v‖ ≤ ‖y + t • v‖ + ‖y‖ := by
        have := norm_sub_le (y + t • v) y
        rwa [add_sub_cancel_left] at this
      rw [norm_smul, hvn, Real.norm_eq_abs, mul_one] at h1
      have := le_abs_self t
      linarith
    have hfreq : ∃ᶠ z in 𝓝[≠] (((T + 1 : ℝ)) : ℂ), fourierEntire f y v z = 0 := by
      have h1 : ∃ᶠ s in 𝓝[≠] (T + 1), T ≤ s := by
        have hev : ∀ᶠ s in 𝓝[≠] (T + 1), T ≤ s :=
          mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds (by linarith : T < T + 1))
        exact hev.frequently
      have htend : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] (T + 1)) (𝓝[≠] (((T + 1 : ℝ)) : ℂ)) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          ((Complex.continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds)
          (eventually_nhdsWithin_of_forall fun s hs => by
            simp only [mem_compl_iff, mem_singleton_iff] at hs ⊢
            exact fun h => hs (Complex.ofReal_injective h))
      exact htend.frequently (h1.mono fun s hs => hzero s hs)
    have h0 := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (mem_univ _) hfreq (mem_univ (0 : ℂ))
    have h00 := fourierEntire_ofReal f y v 0
    simp only [Complex.ofReal_zero, zero_smul, add_zero] at h00
    rw [← h00]
    exact h0
  have h0fun : 𝓕 f = 0 := funext hF0
  have hinv := hcont.fourierInv_fourier_eq hint (by rw [h0fun]; exact integrable_zero _ _ _)
  rw [h0fun] at hinv
  rw [← hinv]
  ext x
  simp [Real.fourierInv_eq]

/-! ### Axiom guards -/

/-- info: 'FormalResearch.SignUncertainty.fourier_compact_support_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fourier_compact_support_eq_zero

end FormalResearch.SignUncertainty
