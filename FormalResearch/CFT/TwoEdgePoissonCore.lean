module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.BoundedVariation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Universal Two-Edge Bootstrap Core: Strip Poisson Bounds, Stirling Bound, and Fixed-Point Closures

Source: `CFT/common/two_edge_bootstrap.tex` (shared by CFT Papers I and II).

## Main components

1. **Lemma TE.1 (`stripPoissonP`, `stripPoissonP1`, `stripPoissonQ`, `stripPoissonCalQ`):**
   * Positivity, evenness, unimodality, and exact `ℝ`-integrals `1 - σ₀` and `σ₀` for `0 < σ₀ < 1`.
   * Pointwise and derivative bounds `(K1)`–`(K3)` for `0 < σ₀ ≤ 0.04`.
   * Total variation and derivative integral bounds `(K4)`, `(Q-a)`, and `(Q-b)`.
2. **Stirling bound `(TE.7)` (`gamma_add_half_le`, `teb_stirling_bound`):**
   * `Real.Gamma (k + 1 / 2) ≤ √(2 * π) * k ^ k * Real.exp (-k)` for `k ≥ 1`.
   * `2 ^ (k + 1) * Real.Gamma (k + 1 / 2) * (π / (4 * ℓ * a)) ^ (k + 1 / 2) ≤ 4 * Real.exp (-k)` for `ℓ * a ≥ (π / 2) * k`.
3. **Theorem TE.2 fixed-point closures (`log_bootstrap_bound`, `poly_absorption_bound_rpow`, `poly_absorption_bound`):**
   * Explicit upper bound `L ≤ 2 * Cstar * Real.log (2 * Cstar)` from `L ≤ Cstar * (1 + Real.log L)`.
   * Polynomial absorption bound `K ≤ max 1 (max (2 * A) ((2 * A * L♯) ^ (1 / (k₀ + 3 / 2))))` from `K ≤ A * (1 + L♯ * K ^ (-(k₀ + 1 / 2)))`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real ENNReal NNReal Interval Nat

namespace FormalResearch.CFT

/-! ### Part 1: Lemma TE.1 — Strip Poisson Kernels and Bounds -/

/-- Left-edge strip Poisson kernel `p(s) = (1/2) sin(π σ₀) / (cosh(π s) - cos(π σ₀))` (TE.1). -/
noncomputable def stripPoissonP (σ₀ s : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.sin (π * σ₀) / (Real.cosh (π * s) - Real.cos (π * σ₀))

/-- Right-edge strip Poisson kernel `p₁(s) = (1/2) sin(π σ₀) / (cosh(π s) + cos(π σ₀))` (TE.1). -/
noncomputable def stripPoissonP1 (σ₀ s : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.sin (π * σ₀) / (Real.cosh (π * s) + Real.cos (π * σ₀))

/-- Combined signed boundary kernel `Q(τ) = p(τ - η₀) + ε p₁(τ + η₀)` (TE.2). -/
noncomputable def stripPoissonQ (σ₀ η₀ ε τ : ℝ) : ℝ :=
  stripPoissonP σ₀ (τ - η₀) + ε * stripPoissonP1 σ₀ (τ + η₀)

/-- Majorant kernel `𝒬(τ) = p(τ - η₀) + p₁(τ + η₀)`. -/
noncomputable def stripPoissonCalQ (σ₀ η₀ τ : ℝ) : ℝ :=
  stripPoissonP σ₀ (τ - η₀) + stripPoissonP1 σ₀ (τ + η₀)

section ElementaryHyperbolic

private lemma nonneg_of_zero_of_hasDerivAt {g g' : ℝ → ℝ} (h0 : g 0 = 0)
    (hd : ∀ x, HasDerivAt g (g' x) x) (hnn : ∀ x ≥ 0, 0 ≤ g' x) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ g x := by
  have hmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt).continuousOn
    · intro s _; exact (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hd s).deriv]
      exact hnn s hs.le
  rw [← h0]
  exact hmono le_rfl hx hx

private lemma abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  rw [abs_le]
  have hp : 0 < Real.exp x := Real.exp_pos x
  have hn : 0 < Real.exp (-x) := Real.exp_pos (-x)
  rw [Real.sinh_eq, Real.cosh_eq]
  constructor <;> linarith

private lemma half_exp_abs_le_cosh (x : ℝ) : (1 / 2 : ℝ) * Real.exp |x| ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    linarith [Real.exp_pos (-x)]
  · rw [abs_of_nonpos hx]
    linarith [Real.exp_pos x]

private lemma one_add_sq_div_two_le_cosh (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  wlog hx : 0 ≤ x
  · have h := this (-x) (by linarith)
    simpa [Real.cosh_neg] using h
  have hsinh : ∀ t ≥ 0, 0 ≤ Real.sinh t - t := fun t ht =>
    nonneg_of_zero_of_hasDerivAt (by simp)
      (fun u => (Real.hasDerivAt_sinh u).sub (hasDerivAt_id u))
      (fun u _ => by
        have hpos : 0 ≤ Real.cosh u - 1 := by
          rw [Real.cosh_eq, Real.exp_neg]
          have he : 0 < Real.exp u := Real.exp_pos u
          have : (Real.exp u - 1) ^ 2 / (2 * Real.exp u) = (Real.exp u + (Real.exp u)⁻¹) / 2 - 1 := by
            field_simp; ring
          rw [← this]
          positivity
        linarith) ht
  have hmain : 0 ≤ Real.cosh x - (1 + x ^ 2 / 2) :=
    nonneg_of_zero_of_hasDerivAt (by simp)
      (fun u => ((Real.hasDerivAt_cosh u).sub ((hasDerivAt_const u 1).add
        ((hasDerivAt_pow 2 u).div_const 2))).congr_deriv (by simp))
      (fun u hu => hsinh u hu) hx
  linarith

private lemma exp_half_ge_sq (x : ℝ) (hx : 0 ≤ x) :
    Real.exp 2 / 16 * x ^ 2 ≤ Real.exp (x / 2) := by
  have h1 : x / 4 ≤ Real.exp (x / 4 - 1) := by linarith [Real.add_one_le_exp (x / 4 - 1)]
  have h2 : (x / 4) ^ 2 ≤ Real.exp (x / 4 - 1) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) h1 2
  have hexp : Real.exp (x / 4 - 1) ^ 2 = Real.exp (x / 2) * Real.exp (-2) := by
    rw [← Real.exp_nat_mul]
    rw [show ((2 : ℕ) : ℝ) * (x / 4 - 1) = x / 2 + (-2) by norm_num; ring, Real.exp_add]
  rw [hexp, Real.exp_neg] at h2
  have h3 : x ^ 2 / 16 ≤ Real.exp (x / 2) / Real.exp 2 := by
    rw [show x ^ 2 / 16 = (x / 4) ^ 2 by ring, div_eq_mul_inv]
    exact h2
  rw [le_div_iff₀ (Real.exp_pos 2)] at h3
  linarith

private lemma hasDerivAt_tanh_real (x : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  have hfun : Real.sinh / Real.cosh = Real.tanh := by
    ext t; exact (Real.tanh_eq_sinh_div_cosh t).symm
  rw [hfun] at h
  refine h.congr_deriv ?_
  have hsq : Real.cosh x ^ 2 - Real.sinh x ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq x
  field_simp
  linarith

private lemma tendsto_tanh_atTop : Tendsto Real.tanh atTop (𝓝 1) := by
  have hfun : Real.tanh = fun x : ℝ => (1 - Real.exp (-2 * x)) / (1 + Real.exp (-2 * x)) := by
    ext x
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    have hx : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
    have h2 : Real.exp (-2 * x) = Real.exp (-x) / Real.exp x := by
      rw [show (-2 : ℝ) * x = -(x + x) by ring, Real.exp_neg, Real.exp_add, Real.exp_neg]
      field_simp
    rw [h2, Real.exp_neg]
    field_simp
  rw [hfun]
  have hexp : Tendsto (fun x : ℝ => Real.exp (-2 * x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num))
  have hnum : Tendsto (fun x : ℝ => 1 - Real.exp (-2 * x)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hexp
  have hden : Tendsto (fun x : ℝ => 1 + Real.exp (-2 * x)) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add hexp
  have hquot : Tendsto (fun x : ℝ => (1 - Real.exp (-2 * x)) / (1 + Real.exp (-2 * x))) atTop
      (𝓝 ((1 - 0) / (1 + 0))) := hnum.div hden (by norm_num)
  simpa using hquot

private lemma tendsto_tanh_atBot : Tendsto Real.tanh atBot (𝓝 (-1)) := by
  have hfun : Real.tanh = fun x => -Real.tanh (-x) := by
    ext x; simp [Real.tanh_neg]
  rw [hfun]
  simpa using (tendsto_tanh_atTop.comp tendsto_neg_atBot_atTop).neg

end ElementaryHyperbolic

section StripPoissonPartA

lemma stripPoisson_sin_pos {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) :
    0 < Real.sin (π * σ₀) :=
  Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos h0) (by nlinarith [Real.pi_pos])

lemma stripPoisson_cos_lt_one {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) :
    Real.cos (π * σ₀) < 1 := by
  rw [← Real.cos_zero]
  exact Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
    ⟨(mul_pos Real.pi_pos h0).le, by nlinarith [Real.pi_pos]⟩ (mul_pos Real.pi_pos h0)

lemma stripPoisson_neg_one_lt_cos {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) :
    -1 < Real.cos (π * σ₀) := by
  rw [← Real.cos_pi]
  exact Real.strictAntiOn_cos
    ⟨(mul_pos Real.pi_pos h0).le, by nlinarith [Real.pi_pos]⟩
    ⟨Real.pi_pos.le, le_rfl⟩ (by nlinarith [Real.pi_pos])

lemma stripPoissonP_den_pos {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) (s : ℝ) :
    0 < Real.cosh (π * s) - Real.cos (π * σ₀) := by
  have hcosh : 1 ≤ Real.cosh (π * s) := Real.one_le_cosh _
  linarith [stripPoisson_cos_lt_one h0 h1]

lemma stripPoissonP1_den_pos {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) (s : ℝ) :
    0 < Real.cosh (π * s) + Real.cos (π * σ₀) := by
  have hcosh : 1 ≤ Real.cosh (π * s) := Real.one_le_cosh _
  linarith [stripPoisson_neg_one_lt_cos h0 h1]

lemma stripPoissonP_pos {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) (s : ℝ) :
    0 < stripPoissonP σ₀ s :=
  div_pos (mul_pos (by norm_num) (stripPoisson_sin_pos h0 h1)) (stripPoissonP_den_pos h0 h1 s)

lemma stripPoissonP1_pos {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) (s : ℝ) :
    0 < stripPoissonP1 σ₀ s :=
  div_pos (mul_pos (by norm_num) (stripPoisson_sin_pos h0 h1)) (stripPoissonP1_den_pos h0 h1 s)

lemma stripPoissonP_even (σ₀ s : ℝ) : stripPoissonP σ₀ (-s) = stripPoissonP σ₀ s := by
  simp [stripPoissonP, mul_neg, Real.cosh_neg]

lemma stripPoissonP1_even (σ₀ s : ℝ) : stripPoissonP1 σ₀ (-s) = stripPoissonP1 σ₀ s := by
  simp [stripPoissonP1, mul_neg, Real.cosh_neg]

lemma stripPoissonP_antitoneOn_Ici {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) :
    AntitoneOn (stripPoissonP σ₀) (Ici 0) := by
  intro s hs t ht hst
  unfold stripPoissonP
  have hnum : 0 ≤ (1 / 2 : ℝ) * Real.sin (π * σ₀) := (mul_pos (by norm_num) (stripPoisson_sin_pos h0 h1)).le
  have hden : Real.cosh (π * s) - Real.cos (π * σ₀) ≤ Real.cosh (π * t) - Real.cos (π * σ₀) := by
    have hcosh : Real.cosh (π * s) ≤ Real.cosh (π * t) :=
      Real.cosh_strictMonoOn.monotoneOn (mul_nonneg Real.pi_pos.le hs) (mul_nonneg Real.pi_pos.le ht)
        (mul_le_mul_of_nonneg_left hst Real.pi_pos.le)
    linarith
  exact div_le_div_of_nonneg_left hnum (stripPoissonP_den_pos h0 h1 s) hden

lemma stripPoissonP1_antitoneOn_Ici {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) :
    AntitoneOn (stripPoissonP1 σ₀) (Ici 0) := by
  intro s hs t ht hst
  unfold stripPoissonP1
  have hnum : 0 ≤ (1 / 2 : ℝ) * Real.sin (π * σ₀) := (mul_pos (by norm_num) (stripPoisson_sin_pos h0 h1)).le
  have hden : Real.cosh (π * s) + Real.cos (π * σ₀) ≤ Real.cosh (π * t) + Real.cos (π * σ₀) := by
    have hcosh : Real.cosh (π * s) ≤ Real.cosh (π * t) :=
      Real.cosh_strictMonoOn.monotoneOn (mul_nonneg Real.pi_pos.le hs) (mul_nonneg Real.pi_pos.le ht)
        (mul_le_mul_of_nonneg_left hst Real.pi_pos.le)
    linarith
  exact div_le_div_of_nonneg_left hnum (stripPoissonP1_den_pos h0 h1 s) hden

lemma stripPoissonP_monotoneOn_Iic {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) :
    MonotoneOn (stripPoissonP σ₀) (Iic 0) := by
  intro s hs t ht hst
  rw [← stripPoissonP_even σ₀ s, ← stripPoissonP_even σ₀ t]
  exact stripPoissonP_antitoneOn_Ici h0 h1 (neg_nonneg.mpr ht) (neg_nonneg.mpr hs) (neg_le_neg hst)

lemma stripPoissonP1_monotoneOn_Iic {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) :
    MonotoneOn (stripPoissonP1 σ₀) (Iic 0) := by
  intro s hs t ht hst
  rw [← stripPoissonP1_even σ₀ s, ← stripPoissonP1_even σ₀ t]
  exact stripPoissonP1_antitoneOn_Ici h0 h1 (neg_nonneg.mpr ht) (neg_nonneg.mpr hs) (neg_le_neg hst)

lemma stripPoissonP_zero_eq {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) :
    stripPoissonP σ₀ 0 = (1 / 2 : ℝ) * (Real.tan (π * σ₀ / 2))⁻¹ := by
  unfold stripPoissonP
  have hy : 0 < π * σ₀ / 2 ∧ π * σ₀ / 2 < π / 2 :=
    ⟨by positivity, by nlinarith [Real.pi_pos]⟩
  have hsin : 0 < Real.sin (π * σ₀ / 2) := Real.sin_pos_of_pos_of_lt_pi hy.1 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos (π * σ₀ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hy.2⟩
  have h2s : Real.sin (π * σ₀) = 2 * Real.sin (π * σ₀ / 2) * Real.cos (π * σ₀ / 2) := by
    have hs := Real.sin_two_mul (π * σ₀ / 2)
    rwa [show 2 * (π * σ₀ / 2) = π * σ₀ by ring] at hs
  have h2c : Real.cos (π * σ₀) = Real.cos (π * σ₀ / 2) ^ 2 - Real.sin (π * σ₀ / 2) ^ 2 := by
    have hc := Real.cos_two_mul (π * σ₀ / 2)
    rw [show 2 * (π * σ₀ / 2) = π * σ₀ by ring] at hc
    linarith [Real.sin_sq_add_cos_sq (π * σ₀ / 2)]
  have htrig : Real.sin (π * σ₀ / 2) ^ 2 + Real.cos (π * σ₀ / 2) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  rw [mul_zero, Real.cosh_zero, h2s, h2c, Real.tan_eq_sin_div_cos]
  have hsne : Real.sin (π * σ₀ / 2) ≠ 0 := hsin.ne'
  have hcne : Real.cos (π * σ₀ / 2) ≠ 0 := hcos.ne'
  have hden : 1 - (Real.cos (π * σ₀ / 2) ^ 2 - Real.sin (π * σ₀ / 2) ^ 2) =
      2 * Real.sin (π * σ₀ / 2) ^ 2 := by linarith [htrig]
  rw [hden]
  field_simp

lemma stripPoissonP1_zero_eq {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) :
    stripPoissonP1 σ₀ 0 = (1 / 2 : ℝ) * Real.tan (π * σ₀ / 2) := by
  unfold stripPoissonP1
  have hy : 0 < π * σ₀ / 2 ∧ π * σ₀ / 2 < π / 2 :=
    ⟨by positivity, by nlinarith [Real.pi_pos]⟩
  have hcos : 0 < Real.cos (π * σ₀ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hy.2⟩
  have h2s : Real.sin (π * σ₀) = 2 * Real.sin (π * σ₀ / 2) * Real.cos (π * σ₀ / 2) := by
    have hs := Real.sin_two_mul (π * σ₀ / 2)
    rwa [show 2 * (π * σ₀ / 2) = π * σ₀ by ring] at hs
  have h2c : Real.cos (π * σ₀) = Real.cos (π * σ₀ / 2) ^ 2 - Real.sin (π * σ₀ / 2) ^ 2 := by
    have hc := Real.cos_two_mul (π * σ₀ / 2)
    rw [show 2 * (π * σ₀ / 2) = π * σ₀ by ring] at hc
    linarith [Real.sin_sq_add_cos_sq (π * σ₀ / 2)]
  have htrig : Real.sin (π * σ₀ / 2) ^ 2 + Real.cos (π * σ₀ / 2) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  rw [mul_zero, Real.cosh_zero, h2s, h2c, Real.tan_eq_sin_div_cos]
  have hcne : Real.cos (π * σ₀ / 2) ≠ 0 := hcos.ne'
  have hden : 1 + (Real.cos (π * σ₀ / 2) ^ 2 - Real.sin (π * σ₀ / 2) ^ 2) =
      2 * Real.cos (π * σ₀ / 2) ^ 2 := by linarith [htrig]
  rw [hden]
  field_simp

private lemma hasDerivAt_stripPoissonP_anti {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) (s : ℝ) :
    HasDerivAt (fun t => (1 / π) * Real.arctan
      (Real.tanh (π * t / 2) * (Real.cos (π * σ₀ / 2) / Real.sin (π * σ₀ / 2))))
      (stripPoissonP σ₀ s) s := by
  set c := Real.cos (π * σ₀ / 2)
  set d := Real.sin (π * σ₀ / 2)
  have hd_pos : 0 < d := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hc_pos : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have harg : HasDerivAt (fun t => π * t / 2) (π / 2) s :=
    (((hasDerivAt_id s).const_mul π).div_const 2).congr_deriv (by ring)
  have htanh := (hasDerivAt_tanh_real (π * s / 2)).comp s harg
  have hu := htanh.mul_const (c / d)
  have harc := (hu.arctan).const_mul (1 / π)
  change HasDerivAt (fun t => (1 / π) * Real.arctan
    (Real.tanh (π * t / 2) * (c / d))) _ s at harc
  refine harc.congr_deriv ?_
  set a := Real.cosh (π * s / 2)
  set b := Real.sinh (π * s / 2)
  have ha_pos : 0 < a := Real.cosh_pos _
  have hab : a ^ 2 - b ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
  have hcd : c ^ 2 + d ^ 2 = 1 := by
    dsimp [c, d]; rw [add_comm]; exact Real.sin_sq_add_cos_sq _
  have h2s : Real.sin (π * σ₀) = 2 * d * c := by
    dsimp [c, d]
    have hs := Real.sin_two_mul (π * σ₀ / 2)
    rwa [show 2 * (π * σ₀ / 2) = π * σ₀ by ring] at hs
  have h2c : Real.cos (π * σ₀) = c ^ 2 - d ^ 2 := by
    dsimp [c, d]
    have hc := Real.cos_two_mul (π * σ₀ / 2)
    rw [show 2 * (π * σ₀ / 2) = π * σ₀ by ring] at hc
    linarith [hcd]
  have h2ch : Real.cosh (π * s) = a ^ 2 + b ^ 2 := by
    dsimp [a, b]
    have hch := Real.cosh_two_mul (π * s / 2)
    rwa [show 2 * (π * s / 2) = π * s by ring] at hch
  have hden_pos : 0 < a ^ 2 * d ^ 2 + b ^ 2 * c ^ 2 := by positivity
  have htanh_eq : Real.tanh (π * s / 2) = b / a := Real.tanh_eq_sinh_div_cosh _
  unfold stripPoissonP
  dsimp only [Function.comp_def]
  rw [htanh_eq, h2s, h2c, h2ch]
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  have hsub_eq : a ^ 2 + b ^ 2 - (c ^ 2 - d ^ 2) = 2 * (a ^ 2 * d ^ 2 + b ^ 2 * c ^ 2) := by
    calc a ^ 2 + b ^ 2 - (c ^ 2 - d ^ 2)
        = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a ^ 2 - b ^ 2) * (c ^ 2 - d ^ 2) := by
          rw [hcd, hab]; ring
      _ = 2 * (a ^ 2 * d ^ 2 + b ^ 2 * c ^ 2) := by ring
  rw [hsub_eq]
  field_simp

private lemma hasDerivAt_stripPoissonP1_anti {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) (s : ℝ) :
    HasDerivAt (fun t => (1 / π) * Real.arctan
      (Real.tanh (π * t / 2) * (Real.sin (π * σ₀ / 2) / Real.cos (π * σ₀ / 2))))
      (stripPoissonP1 σ₀ s) s := by
  set c := Real.cos (π * σ₀ / 2)
  set d := Real.sin (π * σ₀ / 2)
  have hd_pos : 0 < d := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hc_pos : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have harg : HasDerivAt (fun t => π * t / 2) (π / 2) s :=
    (((hasDerivAt_id s).const_mul π).div_const 2).congr_deriv (by ring)
  have htanh := (hasDerivAt_tanh_real (π * s / 2)).comp s harg
  have hu := htanh.mul_const (d / c)
  have harc := (hu.arctan).const_mul (1 / π)
  change HasDerivAt (fun t => (1 / π) * Real.arctan
    (Real.tanh (π * t / 2) * (d / c))) _ s at harc
  refine harc.congr_deriv ?_
  set a := Real.cosh (π * s / 2)
  set b := Real.sinh (π * s / 2)
  have ha_pos : 0 < a := Real.cosh_pos _
  have hab : a ^ 2 - b ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
  have hcd : c ^ 2 + d ^ 2 = 1 := by
    dsimp [c, d]; rw [add_comm]; exact Real.sin_sq_add_cos_sq _
  have h2s : Real.sin (π * σ₀) = 2 * d * c := by
    dsimp [c, d]
    have hs := Real.sin_two_mul (π * σ₀ / 2)
    rwa [show 2 * (π * σ₀ / 2) = π * σ₀ by ring] at hs
  have h2c : Real.cos (π * σ₀) = c ^ 2 - d ^ 2 := by
    dsimp [c, d]
    have hc := Real.cos_two_mul (π * σ₀ / 2)
    rw [show 2 * (π * σ₀ / 2) = π * σ₀ by ring] at hc
    linarith [hcd]
  have h2ch : Real.cosh (π * s) = a ^ 2 + b ^ 2 := by
    dsimp [a, b]
    have hch := Real.cosh_two_mul (π * s / 2)
    rwa [show 2 * (π * s / 2) = π * s by ring] at hch
  have hden_pos : 0 < a ^ 2 * c ^ 2 + b ^ 2 * d ^ 2 := by positivity
  have htanh_eq : Real.tanh (π * s / 2) = b / a := Real.tanh_eq_sinh_div_cosh _
  unfold stripPoissonP1
  dsimp only [Function.comp_def]
  rw [htanh_eq, h2s, h2c, h2ch]
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  have hadd_eq : a ^ 2 + b ^ 2 + (c ^ 2 - d ^ 2) = 2 * (a ^ 2 * c ^ 2 + b ^ 2 * d ^ 2) := by
    calc a ^ 2 + b ^ 2 + (c ^ 2 - d ^ 2)
        = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) + (a ^ 2 - b ^ 2) * (c ^ 2 - d ^ 2) := by
          rw [hcd, hab]; ring
      _ = 2 * (a ^ 2 * c ^ 2 + b ^ 2 * d ^ 2) := by ring
  rw [hadd_eq]
  field_simp

private lemma arctan_cos_div_sin {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) :
    Real.arctan (Real.cos θ / Real.sin θ) = π / 2 - θ := by
  have htan : Real.cos θ / Real.sin θ = Real.tan (π / 2 - θ) := by
    rw [Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos, inv_div]
  rw [htan, Real.arctan_tan (by linarith) (by linarith)]

private lemma integrable_of_hasDerivAt_nonneg_tendsto {F f : ℝ → ℝ} {m n : ℝ}
    (hderiv : ∀ x, HasDerivAt F (f x) x) (hf_nn : ∀ x, 0 ≤ f x)
    (hbot : Tendsto F atBot (𝓝 m)) (htop : Tendsto F atTop (𝓝 n)) :
    Integrable f := by
  have hIoi : IntegrableOn f (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hderiv x) (fun x _ => hf_nn x) htop
  have hIio_neg : IntegrableOn (fun x => f (-x)) (Ioi 0) := by
    refine integrableOn_Ioi_deriv_of_nonneg' (g := fun x => -F (-x)) (l := -m)
      ?_ (fun x _ => hf_nn (-x)) ?_
    · intro x _
      exact ((hderiv (-x)).comp x (hasDerivAt_neg x)).neg.congr_deriv (by ring)
    · simpa using (hbot.comp tendsto_neg_atTop_atBot).neg
  have hIci_neg : IntegrableOn (fun x => f (-x)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by simp)).mpr hIio_neg
  have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  have hemb : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have hpre : IntegrableOn (fun x => f (-x)) ((fun x : ℝ => -x) ⁻¹' Iic (0 : ℝ)) volume := by
    rwa [show ((fun x : ℝ => -x) ⁻¹' Iic (0 : ℝ)) = Ici 0 by ext x; simp]
  have hIic : IntegrableOn f (Iic 0) := (hmp.integrableOn_comp_preimage hemb).mp hpre
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hIoi

lemma stripPoissonP_integrable {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) :
    Integrable (stripPoissonP σ₀) := by
  set F : ℝ → ℝ := fun t => (1 / π) * Real.arctan
    (Real.tanh (π * t / 2) * (Real.cos (π * σ₀ / 2) / Real.sin (π * σ₀ / 2)))
  have htop : Tendsto F atTop (𝓝 ((1 / π) * (π / 2 - π * σ₀ / 2))) := by
    have hmul : Tendsto (fun t => π * t / 2) atTop atTop :=
      (tendsto_id.const_mul_atTop (by positivity : 0 < π / 2)).congr (fun t => by dsimp; ring)
    have ht : Tendsto (fun t => Real.tanh (π * t / 2) * (Real.cos (π * σ₀ / 2) / Real.sin (π * σ₀ / 2)))
        atTop (𝓝 (1 * (Real.cos (π * σ₀ / 2) / Real.sin (π * σ₀ / 2)))) :=
      (tendsto_tanh_atTop.comp hmul).mul_const _
    rw [one_mul] at ht
    rw [← arctan_cos_div_sin (by positivity) (by nlinarith [Real.pi_pos])]
    exact ((Real.continuous_arctan.tendsto _).comp ht).const_mul _
  have hbot : Tendsto F atBot (𝓝 ((1 / π) * (-(π / 2 - π * σ₀ / 2)))) := by
    have hmul : Tendsto (fun t => π * t / 2) atBot atBot :=
      (tendsto_id.const_mul_atBot (by positivity : 0 < π / 2)).congr (fun t => by dsimp; ring)
    have ht : Tendsto (fun t => Real.tanh (π * t / 2) * (Real.cos (π * σ₀ / 2) / Real.sin (π * σ₀ / 2)))
        atBot (𝓝 (-1 * (Real.cos (π * σ₀ / 2) / Real.sin (π * σ₀ / 2)))) :=
      (tendsto_tanh_atBot.comp hmul).mul_const _
    rw [neg_one_mul] at ht
    have ht' := (Real.continuous_arctan.tendsto _).comp ht
    rw [Real.arctan_neg, arctan_cos_div_sin (by positivity) (by nlinarith [Real.pi_pos])] at ht'
    exact ht'.const_mul _
  exact integrable_of_hasDerivAt_nonneg_tendsto (hasDerivAt_stripPoissonP_anti h0 h1)
    (fun s => (stripPoissonP_pos h0 h1 s).le) hbot htop

lemma stripPoissonP1_integrable {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) :
    Integrable (stripPoissonP1 σ₀) := by
  set F : ℝ → ℝ := fun t => (1 / π) * Real.arctan
    (Real.tanh (π * t / 2) * (Real.sin (π * σ₀ / 2) / Real.cos (π * σ₀ / 2)))
  have htan_eq : Real.sin (π * σ₀ / 2) / Real.cos (π * σ₀ / 2) = Real.tan (π * σ₀ / 2) :=
    (Real.tan_eq_sin_div_cos _).symm
  have harc_val : Real.arctan (Real.sin (π * σ₀ / 2) / Real.cos (π * σ₀ / 2)) = π * σ₀ / 2 := by
    rw [htan_eq]; exact Real.arctan_tan (by linarith [Real.pi_pos, mul_pos Real.pi_pos h0])
      (by nlinarith [Real.pi_pos])
  have htop : Tendsto F atTop (𝓝 ((1 / π) * (π * σ₀ / 2))) := by
    have hmul : Tendsto (fun t => π * t / 2) atTop atTop :=
      (tendsto_id.const_mul_atTop (by positivity : 0 < π / 2)).congr (fun t => by dsimp; ring)
    have ht : Tendsto (fun t => Real.tanh (π * t / 2) * (Real.sin (π * σ₀ / 2) / Real.cos (π * σ₀ / 2)))
        atTop (𝓝 (1 * (Real.sin (π * σ₀ / 2) / Real.cos (π * σ₀ / 2)))) :=
      (tendsto_tanh_atTop.comp hmul).mul_const _
    rw [one_mul] at ht
    rw [← harc_val]
    exact ((Real.continuous_arctan.tendsto _).comp ht).const_mul _
  have hbot : Tendsto F atBot (𝓝 ((1 / π) * (-(π * σ₀ / 2)))) := by
    have hmul : Tendsto (fun t => π * t / 2) atBot atBot :=
      (tendsto_id.const_mul_atBot (by positivity : 0 < π / 2)).congr (fun t => by dsimp; ring)
    have ht : Tendsto (fun t => Real.tanh (π * t / 2) * (Real.sin (π * σ₀ / 2) / Real.cos (π * σ₀ / 2)))
        atBot (𝓝 (-1 * (Real.sin (π * σ₀ / 2) / Real.cos (π * σ₀ / 2)))) :=
      (tendsto_tanh_atBot.comp hmul).mul_const _
    rw [neg_one_mul] at ht
    have ht' := (Real.continuous_arctan.tendsto _).comp ht
    rw [Real.arctan_neg, harc_val] at ht'
    exact ht'.const_mul _
  exact integrable_of_hasDerivAt_nonneg_tendsto (hasDerivAt_stripPoissonP1_anti h0 h1)
    (fun s => (stripPoissonP1_pos h0 h1 s).le) hbot htop

/-- Exact total mass `∫ s : ℝ, stripPoissonP σ₀ s = 1 - σ₀` (Lemma TE.1(a)). -/
theorem stripPoissonP_integral {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) :
    ∫ s : ℝ, stripPoissonP σ₀ s = 1 - σ₀ := by
  set F : ℝ → ℝ := fun t => (1 / π) * Real.arctan
    (Real.tanh (π * t / 2) * (Real.cos (π * σ₀ / 2) / Real.sin (π * σ₀ / 2)))
  have htop : Tendsto F atTop (𝓝 ((1 / π) * (π / 2 - π * σ₀ / 2))) := by
    have hmul : Tendsto (fun t => π * t / 2) atTop atTop :=
      (tendsto_id.const_mul_atTop (by positivity : 0 < π / 2)).congr (fun t => by dsimp; ring)
    have ht : Tendsto (fun t => Real.tanh (π * t / 2) * (Real.cos (π * σ₀ / 2) / Real.sin (π * σ₀ / 2)))
        atTop (𝓝 (1 * (Real.cos (π * σ₀ / 2) / Real.sin (π * σ₀ / 2)))) :=
      (tendsto_tanh_atTop.comp hmul).mul_const _
    rw [one_mul] at ht
    rw [← arctan_cos_div_sin (by positivity) (by nlinarith [Real.pi_pos])]
    exact ((Real.continuous_arctan.tendsto _).comp ht).const_mul _
  have hbot : Tendsto F atBot (𝓝 ((1 / π) * (-(π / 2 - π * σ₀ / 2)))) := by
    have hmul : Tendsto (fun t => π * t / 2) atBot atBot :=
      (tendsto_id.const_mul_atBot (by positivity : 0 < π / 2)).congr (fun t => by dsimp; ring)
    have ht : Tendsto (fun t => Real.tanh (π * t / 2) * (Real.cos (π * σ₀ / 2) / Real.sin (π * σ₀ / 2)))
        atBot (𝓝 (-1 * (Real.cos (π * σ₀ / 2) / Real.sin (π * σ₀ / 2)))) :=
      (tendsto_tanh_atBot.comp hmul).mul_const _
    rw [neg_one_mul] at ht
    have ht' := (Real.continuous_arctan.tendsto _).comp ht
    rw [Real.arctan_neg, arctan_cos_div_sin (by positivity) (by nlinarith [Real.pi_pos])] at ht'
    exact ht'.const_mul _
  rw [integral_of_hasDerivAt_of_tendsto (hasDerivAt_stripPoissonP_anti h0 h1)
    (stripPoissonP_integrable h0 h1) hbot htop]
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  field_simp
  ring

/-- Exact total mass `∫ s : ℝ, stripPoissonP1 σ₀ s = σ₀` (Lemma TE.1(a)). -/
theorem stripPoissonP1_integral {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) :
    ∫ s : ℝ, stripPoissonP1 σ₀ s = σ₀ := by
  set F : ℝ → ℝ := fun t => (1 / π) * Real.arctan
    (Real.tanh (π * t / 2) * (Real.sin (π * σ₀ / 2) / Real.cos (π * σ₀ / 2)))
  have htan_eq : Real.sin (π * σ₀ / 2) / Real.cos (π * σ₀ / 2) = Real.tan (π * σ₀ / 2) :=
    (Real.tan_eq_sin_div_cos _).symm
  have harc_val : Real.arctan (Real.sin (π * σ₀ / 2) / Real.cos (π * σ₀ / 2)) = π * σ₀ / 2 := by
    rw [htan_eq]; exact Real.arctan_tan (by linarith [Real.pi_pos, mul_pos Real.pi_pos h0])
      (by nlinarith [Real.pi_pos])
  have htop : Tendsto F atTop (𝓝 ((1 / π) * (π * σ₀ / 2))) := by
    have hmul : Tendsto (fun t => π * t / 2) atTop atTop :=
      (tendsto_id.const_mul_atTop (by positivity : 0 < π / 2)).congr (fun t => by dsimp; ring)
    have ht : Tendsto (fun t => Real.tanh (π * t / 2) * (Real.sin (π * σ₀ / 2) / Real.cos (π * σ₀ / 2)))
        atTop (𝓝 (1 * (Real.sin (π * σ₀ / 2) / Real.cos (π * σ₀ / 2)))) :=
      (tendsto_tanh_atTop.comp hmul).mul_const _
    rw [one_mul] at ht
    rw [← harc_val]
    exact ((Real.continuous_arctan.tendsto _).comp ht).const_mul _
  have hbot : Tendsto F atBot (𝓝 ((1 / π) * (-(π * σ₀ / 2)))) := by
    have hmul : Tendsto (fun t => π * t / 2) atBot atBot :=
      (tendsto_id.const_mul_atBot (by positivity : 0 < π / 2)).congr (fun t => by dsimp; ring)
    have ht : Tendsto (fun t => Real.tanh (π * t / 2) * (Real.sin (π * σ₀ / 2) / Real.cos (π * σ₀ / 2)))
        atBot (𝓝 (-1 * (Real.sin (π * σ₀ / 2) / Real.cos (π * σ₀ / 2)))) :=
      (tendsto_tanh_atBot.comp hmul).mul_const _
    rw [neg_one_mul] at ht
    have ht' := (Real.continuous_arctan.tendsto _).comp ht
    rw [Real.arctan_neg, harc_val] at ht'
    exact ht'.const_mul _
  rw [integral_of_hasDerivAt_of_tendsto (hasDerivAt_stripPoissonP1_anti h0 h1)
    (stripPoissonP1_integrable h0 h1) hbot htop]
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  field_simp
  ring

end StripPoissonPartA

section StripPoissonPartB

lemma stripPoissonQ_abs_le {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) (η₀ : ℝ) {ε : ℝ}
    (hε : |ε| ≤ 1) (τ : ℝ) :
    |stripPoissonQ σ₀ η₀ ε τ| ≤ stripPoissonCalQ σ₀ η₀ τ := by
  unfold stripPoissonQ stripPoissonCalQ
  calc |stripPoissonP σ₀ (τ - η₀) + ε * stripPoissonP1 σ₀ (τ + η₀)|
      ≤ |stripPoissonP σ₀ (τ - η₀)| + |ε * stripPoissonP1 σ₀ (τ + η₀)| := abs_add_le _ _
    _ = stripPoissonP σ₀ (τ - η₀) + |ε| * stripPoissonP1 σ₀ (τ + η₀) := by
        rw [abs_of_pos (stripPoissonP_pos h0 h1 _), abs_mul,
          abs_of_pos (stripPoissonP1_pos h0 h1 _)]
    _ ≤ stripPoissonP σ₀ (τ - η₀) + 1 * stripPoissonP1 σ₀ (τ + η₀) := by
        gcongr; exact (stripPoissonP1_pos h0 h1 _).le
    _ = stripPoissonP σ₀ (τ - η₀) + stripPoissonP1 σ₀ (τ + η₀) := by ring

lemma stripPoissonP_zero_le {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) :
    stripPoissonP σ₀ 0 ≤ 1 / (π * σ₀) := by
  rw [stripPoissonP_zero_eq h0 h1]
  have hy0 : 0 < π * σ₀ / 2 := by positivity
  have hy1 : π * σ₀ / 2 < π / 2 := by nlinarith [Real.pi_pos]
  have htan : π * σ₀ / 2 < Real.tan (π * σ₀ / 2) := Real.lt_tan hy0 hy1
  have hinv : (Real.tan (π * σ₀ / 2))⁻¹ ≤ (π * σ₀ / 2)⁻¹ :=
    inv_anti₀ hy0 htan.le
  calc (1 / 2 : ℝ) * (Real.tan (π * σ₀ / 2))⁻¹
      ≤ (1 / 2 : ℝ) * (π * σ₀ / 2)⁻¹ := by gcongr
    _ = 1 / (π * σ₀) := by field_simp

private lemma one_sub_cos_ge_of_le {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 0.126) :
    0.998 * y ^ 2 / 2 ≤ 1 - Real.cos y := by
  have h1c : 1 - Real.cos y = 2 * Real.sin (y / 2) ^ 2 := by
    have hc := Real.cos_two_mul (y / 2)
    rw [show 2 * (y / 2) = y by ring] at hc
    linarith [Real.sin_sq_add_cos_sq (y / 2)]
  have hsin_lb : y / 2 - (y / 2) ^ 3 / 6 ≤ Real.sin (y / 2) :=
    Real.sin_ge_sub_cube (by linarith)
  have hsin_nn : 0 ≤ y / 2 - (y / 2) ^ 3 / 6 := by
    have : y / 2 - (y / 2) ^ 3 / 6 = y / 2 * (1 - y ^ 2 / 24) := by ring
    rw [this]
    nlinarith [sq_nonneg y]
  have hsq : (y / 2 - (y / 2) ^ 3 / 6) ^ 2 ≤ Real.sin (y / 2) ^ 2 :=
    pow_le_pow_left₀ hsin_nn hsin_lb 2
  have halg : 0.998 * y ^ 2 / 2 ≤ 2 * (y / 2 - (y / 2) ^ 3 / 6) ^ 2 := by
    have hysq : y ^ 2 ≤ 0.126 ^ 2 := by nlinarith
    have h4 : y ^ 4 ≤ 0.126 ^ 2 * y ^ 2 := by nlinarith [sq_nonneg y]
    nlinarith [sq_nonneg y]
  linarith

private lemma cosh_sub_cos_ge_of_le {x y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 0.126) :
    0.998 * (x ^ 2 + y ^ 2) / 2 ≤ Real.cosh x - Real.cos y := by
  have h1 := one_add_sq_div_two_le_cosh x
  have h2 := one_sub_cos_ge_of_le hy0 hy
  nlinarith [sq_nonneg x]

/-- Pointwise bound `(K1)` on `p(s)` for `0 < σ₀ ≤ 0.04`. -/
theorem stripPoissonP_le {σ₀ : ℝ} (h0 : 0 < σ₀) (h4 : σ₀ ≤ 0.04) (s : ℝ) :
    stripPoissonP σ₀ s ≤ σ₀ * Real.exp (-π * |s| / 2) / (s ^ 2 + σ₀ ^ 2) := by
  have h1 : σ₀ < 1 := by linarith
  wlog hs : 0 ≤ s
  · have h := this h0 h4 (-s) h1 (by linarith)
    simpa [stripPoissonP_even, abs_neg] using h
  rw [abs_of_nonneg hs]
  set x := π * s
  set y := π * σ₀
  have hx0 : 0 ≤ x := mul_nonneg Real.pi_pos.le hs
  have hy0 : 0 < y := mul_pos Real.pi_pos h0
  have hy_ub : y ≤ 0.126 := by nlinarith [Real.pi_lt_d4]
  have hsin_le : Real.sin y ≤ y := Real.sin_le hy0.le
  have hr2 : x ^ 2 + y ^ 2 = π ^ 2 * (s ^ 2 + σ₀ ^ 2) := by dsimp [x, y]; ring
  have hpi_gt : (3.1415 : ℝ) < π := Real.pi_gt_d4
  have hpi_lt : π < 3.1416 := Real.pi_lt_d4
  rcases le_or_gt x 2 with hx2 | hx2
  · have hden := cosh_sub_cos_ge_of_le (x := x) hy0.le hy_ub
    have hden_pos : 0 < 0.998 * (x ^ 2 + y ^ 2) / 2 := by positivity
    have hp1 : stripPoissonP σ₀ s ≤ y / (0.998 * (x ^ 2 + y ^ 2)) := by
      unfold stripPoissonP
      calc (1 / 2 : ℝ) * Real.sin y / (Real.cosh x - Real.cos y)
          ≤ (1 / 2 : ℝ) * y / (0.998 * (x ^ 2 + y ^ 2) / 2) := by
            gcongr
        _ = y / (0.998 * (x ^ 2 + y ^ 2)) := by field_simp
    have hexp_ge : Real.exp (-1) ≤ Real.exp (-x / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have hexp_e : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hpi_c : Real.exp 1 ≤ 0.998 * π := by linarith
    calc stripPoissonP σ₀ s
        ≤ y / (0.998 * (x ^ 2 + y ^ 2)) := hp1
      _ = σ₀ / (0.998 * π * (s ^ 2 + σ₀ ^ 2)) := by
          rw [hr2]; dsimp [y]; field_simp [Real.pi_pos.ne']
      _ = (Real.exp 1 / (0.998 * π)) * (σ₀ * Real.exp (-1) / (s ^ 2 + σ₀ ^ 2)) := by
          rw [Real.exp_neg]; field_simp [Real.pi_pos.ne', (Real.exp_pos 1).ne']
      _ ≤ 1 * (σ₀ * Real.exp (-x / 2) / (s ^ 2 + σ₀ ^ 2)) := by
          refine mul_le_mul ((div_le_one (by positivity)).mpr hpi_c) ?_ (by positivity) zero_le_one
          gcongr
      _ = σ₀ * Real.exp (-π * s / 2) / (s ^ 2 + σ₀ ^ 2) := by
          dsimp [x]; ring_nf
  · have hcos_le : Real.cos y ≤ 1 := Real.cos_le_one y
    have hcosh_gt : 1 < Real.cosh x := by
      nlinarith [one_add_sq_div_two_le_cosh x]
    have hp1 : stripPoissonP σ₀ s ≤ y / (2 * (Real.cosh x - 1)) := by
      unfold stripPoissonP
      calc (1 / 2 : ℝ) * Real.sin y / (Real.cosh x - Real.cos y)
          ≤ (1 / 2 : ℝ) * y / (Real.cosh x - 1) := by
            gcongr
        _ = y / (2 * (Real.cosh x - 1)) := by field_simp
    have hfac : (Real.cosh x - 1) * Real.exp (-x / 2) =
        (1 / 2 : ℝ) * (1 - Real.exp (-x)) ^ 2 * Real.exp (x / 2) := by
      rw [Real.cosh_eq, Real.exp_neg]
      have hxpos : 0 < Real.exp x := Real.exp_pos x
      have hx2pos : 0 < Real.exp (x / 2) := Real.exp_pos (x / 2)
      have he_eq : Real.exp x = Real.exp (x / 2) ^ 2 := by
        rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
      have hne_eq : Real.exp (-x / 2) = (Real.exp (x / 2))⁻¹ := by
        rw [← Real.exp_neg]; congr 1; ring
      rw [hne_eq, he_eq]
      field_simp
      ring
    have hexp_neg2 : Real.exp (-x) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
    have h1sub_nn : 0 ≤ 1 - Real.exp (-2) := by
      have : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      linarith
    have h1sub : (1 - Real.exp (-2)) ^ 2 ≤ (1 - Real.exp (-x)) ^ 2 :=
      pow_le_pow_left₀ h1sub_nn (by linarith) 2
    have he2 : Real.exp (-2) = Real.exp (-1) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num
    have h_num_lb : (1 / 2 : ℝ) * (1 - Real.exp (-2)) ^ 2 * (Real.exp 2 / 16) > 0.172 := by
      have he1_gt : (2.71828 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
      have hen1_lt : Real.exp (-1) < 0.36788 := lt_trans Real.exp_neg_one_lt_d9 (by norm_num)
      have he2_eq : Real.exp 2 = Real.exp 1 ^ 2 := by
        rw [← Real.exp_nat_mul]; congr 1; norm_num
      have hprod : (1 - Real.exp (-2)) ^ 2 * Real.exp 2 = (Real.exp 1 - Real.exp (-1)) ^ 2 := by
        rw [he2, he2_eq]
        have h1 : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
        calc (1 - Real.exp (-1) ^ 2) ^ 2 * Real.exp 1 ^ 2
            = ((1 - Real.exp (-1) ^ 2) * Real.exp 1) ^ 2 := by ring
          _ = (Real.exp 1 - Real.exp (-1) * (Real.exp 1 * Real.exp (-1))) ^ 2 := by ring
          _ = (Real.exp 1 - Real.exp (-1)) ^ 2 := by rw [h1, mul_one]
      have hnum_eq : (1 / 2 : ℝ) * (1 - Real.exp (-2)) ^ 2 * (Real.exp 2 / 16) =
          ((1 - Real.exp (-2)) ^ 2 * Real.exp 2) / 32 := by ring
      rw [hnum_eq, hprod]
      have hdiff : (2.3504 : ℝ) < Real.exp 1 - Real.exp (-1) := by linarith
      nlinarith
    have hcosh_lb : 0.172 * x ^ 2 ≤ (Real.cosh x - 1) * Real.exp (-x / 2) := by
      rw [hfac]
      calc (0.172 : ℝ) * x ^ 2
          ≤ ((1 / 2 : ℝ) * (1 - Real.exp (-2)) ^ 2 * (Real.exp 2 / 16)) * x ^ 2 := by
            gcongr
        _ = (1 / 2 : ℝ) * (1 - Real.exp (-2)) ^ 2 * (Real.exp 2 / 16 * x ^ 2) := by ring
        _ ≤ (1 / 2 : ℝ) * (1 - Real.exp (-x)) ^ 2 * Real.exp (x / 2) := by
            gcongr; exact exp_half_ge_sq x hx0
    have hy_x : y ≤ 0.063 * x := by nlinarith
    have hxy_ub : (x ^ 2 + y ^ 2) / (2 * π) ≤ 0.172 * x ^ 2 := by
      have h1 : x ^ 2 + y ^ 2 ≤ (1 + 0.063 ^ 2) * x ^ 2 := by nlinarith [sq_nonneg y]
      have h2 : (1 + 0.063 ^ 2) / (2 * π) ≤ 0.172 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      calc (x ^ 2 + y ^ 2) / (2 * π)
          ≤ ((1 + 0.063 ^ 2) * x ^ 2) / (2 * π) := by gcongr
        _ = ((1 + 0.063 ^ 2) / (2 * π)) * x ^ 2 := by ring
        _ ≤ 0.172 * x ^ 2 := by gcongr
    have hkey : x ^ 2 + y ^ 2 ≤ 2 * π * ((Real.cosh x - 1) * Real.exp (-x / 2)) := by
      have := hxy_ub.trans hcosh_lb
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have hkey' : 1 / (2 * (Real.cosh x - 1)) ≤ π * Real.exp (-x / 2) / (x ^ 2 + y ^ 2) := by
      rw [div_le_div_iff₀ (by linarith) (by positivity)]
      have he_eq : Real.exp (-x / 2) * (2 * (Real.cosh x - 1)) =
          2 * ((Real.cosh x - 1) * Real.exp (-x / 2)) := by ring
      nlinarith
    calc stripPoissonP σ₀ s
        ≤ y / (2 * (Real.cosh x - 1)) := hp1
      _ = y * (1 / (2 * (Real.cosh x - 1))) := by ring
      _ ≤ y * (π * Real.exp (-x / 2) / (x ^ 2 + y ^ 2)) := by gcongr
      _ = σ₀ * Real.exp (-π * s / 2) / (s ^ 2 + σ₀ ^ 2) := by
          rw [hr2]; dsimp [x, y]; field_simp [Real.pi_pos.ne']

lemma stripPoissonP_hasDerivAt {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) (s : ℝ) :
    HasDerivAt (stripPoissonP σ₀)
      (-π * (Real.sinh (π * s) / (Real.cosh (π * s) - Real.cos (π * σ₀))) *
        stripPoissonP σ₀ s) s := by
  have hden : Real.cosh (π * s) - Real.cos (π * σ₀) ≠ 0 :=
    (stripPoissonP_den_pos h0 h1 s).ne'
  have hinner : HasDerivAt (fun t => Real.cosh (π * t) - Real.cos (π * σ₀))
      (Real.sinh (π * s) * π) s := by
    have ha : HasDerivAt (fun t => π * t) π s := by simpa using (hasDerivAt_id s).const_mul π
    exact ((Real.hasDerivAt_cosh (π * s)).comp s ha).sub_const _
  have h := (hinner.inv hden).const_mul ((1 / 2 : ℝ) * Real.sin (π * σ₀))
  have h' : HasDerivAt (stripPoissonP σ₀)
      ((1 / 2 : ℝ) * Real.sin (π * σ₀) *
        (-(Real.sinh (π * s) * π) / (Real.cosh (π * s) - Real.cos (π * σ₀)) ^ 2)) s := by
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp [stripPoissonP, div_eq_mul_inv]
  refine h'.congr_deriv ?_
  unfold stripPoissonP
  field_simp

lemma stripPoissonP1_hasDerivAt {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) (s : ℝ) :
    HasDerivAt (stripPoissonP1 σ₀)
      (-π * (Real.sinh (π * s) / (Real.cosh (π * s) + Real.cos (π * σ₀))) *
        stripPoissonP1 σ₀ s) s := by
  have hden : Real.cosh (π * s) + Real.cos (π * σ₀) ≠ 0 :=
    (stripPoissonP1_den_pos h0 h1 s).ne'
  have hinner : HasDerivAt (fun t => Real.cosh (π * t) + Real.cos (π * σ₀))
      (Real.sinh (π * s) * π) s := by
    have ha : HasDerivAt (fun t => π * t) π s := by simpa using (hasDerivAt_id s).const_mul π
    exact ((Real.hasDerivAt_cosh (π * s)).comp s ha).add_const _
  have h := (hinner.inv hden).const_mul ((1 / 2 : ℝ) * Real.sin (π * σ₀))
  have h' : HasDerivAt (stripPoissonP1 σ₀)
      ((1 / 2 : ℝ) * Real.sin (π * σ₀) *
        (-(Real.sinh (π * s) * π) / (Real.cosh (π * s) + Real.cos (π * σ₀)) ^ 2)) s := by
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp [stripPoissonP1, div_eq_mul_inv]
  refine h'.congr_deriv ?_
  unfold stripPoissonP1
  field_simp

/-- Derivative bound `(K2)` on `p(s)` for `0 < σ₀ ≤ 0.04`. -/
theorem abs_deriv_stripPoissonP_le {σ₀ : ℝ} (h0 : 0 < σ₀) (h4 : σ₀ ≤ 0.04) (s₀ : ℝ) :
    |deriv (stripPoissonP σ₀) s₀| ≤
      π * (1 + 1 / √(s₀ ^ 2 + σ₀ ^ 2)) * stripPoissonP σ₀ s₀ := by
  have h1 : σ₀ < 1 := by linarith
  rw [(stripPoissonP_hasDerivAt h0 h1 s₀).deriv]
  set r := √(s₀ ^ 2 + σ₀ ^ 2)
  have hp_pos : 0 < stripPoissonP σ₀ s₀ := stripPoissonP_pos h0 h1 s₀
  have hden_pos : 0 < Real.cosh (π * s₀) - Real.cos (π * σ₀) := stripPoissonP_den_pos h0 h1 s₀
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos Real.pi_pos, abs_of_pos hp_pos,
    abs_div, abs_of_pos hden_pos]
  suffices hpos_case : ∀ s : ℝ, 0 ≤ s →
      |Real.sinh (π * s)| / (Real.cosh (π * s) - Real.cos (π * σ₀)) ≤
        1 + 1 / √(s ^ 2 + σ₀ ^ 2) by
    have hratio : |Real.sinh (π * s₀)| / (Real.cosh (π * s₀) - Real.cos (π * σ₀)) ≤ 1 + 1 / r := by
      rcases le_total 0 s₀ with hs | hs
      · exact hpos_case s₀ hs
      · have h := hpos_case (-s₀) (neg_nonneg.mpr hs)
        simpa [r, mul_neg, Real.sinh_neg, abs_neg, Real.cosh_neg] using h
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hratio Real.pi_pos.le) hp_pos.le
  intro s hs
  set r' := √(s ^ 2 + σ₀ ^ 2)
  have hr_pos : 0 < r' := Real.sqrt_pos.mpr (by positivity)
  set x := π * s
  set y := π * σ₀
  have hx0 : 0 ≤ x := mul_nonneg Real.pi_pos.le hs
  have hy0 : 0 < y := mul_pos Real.pi_pos h0
  have hy_ub : y ≤ 0.126 := by nlinarith [Real.pi_lt_d4]
  have hsinh_nn : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx0
  rw [abs_of_nonneg hsinh_nn]
  have hpir : π * r' = √(x ^ 2 + y ^ 2) := by
    rw [← Real.sqrt_sq Real.pi_pos.le, ← Real.sqrt_mul (by positivity)]
    congr 1; dsimp [r', x, y]; ring
  have hinv_r : 1 / r' = π / √(x ^ 2 + y ^ 2) := by
    rw [← hpir]
    have hpi : π ≠ 0 := Real.pi_pos.ne'
    field_simp
  rw [hinv_r]
  rcases le_or_gt y x with hyx | hxy
  · have hxpos : 0 < x := lt_of_lt_of_le hy0 hyx
    have hcosh_gt : 1 < Real.cosh x := by nlinarith [one_add_sq_div_two_le_cosh x]
    have h1 : Real.sinh x / (Real.cosh x - Real.cos y) ≤ Real.sinh x / (Real.cosh x - 1) :=
      div_le_div_of_nonneg_left hsinh_nn (by linarith) (by linarith [Real.cos_le_one y])
    have h2 : Real.sinh x / (Real.cosh x - 1) ≤ 1 + 2 / x := by
      have he_gt : 1 < Real.exp (x / 2) := Real.one_lt_exp_iff.mpr (by linarith)
      have he_sub : 0 < Real.exp (x / 2) - Real.exp (-x / 2) := by
        have : Real.exp (-x / 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
        linarith
      have h_id1 : 2 * Real.sinh x =
          (Real.exp (x / 2) - Real.exp (-x / 2)) * (Real.exp (x / 2) + Real.exp (-x / 2)) := by
        rw [Real.sinh_eq]
        have h_e : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
          rw [← Real.exp_add]; ring_nf
        have h_ne : Real.exp (-x) = Real.exp (-x / 2) * Real.exp (-x / 2) := by
          rw [← Real.exp_add]; ring_nf
        rw [h_e, h_ne]; ring
      have h_id2 : 2 * (Real.cosh x - 1) = (Real.exp (x / 2) - Real.exp (-x / 2)) ^ 2 := by
        rw [Real.cosh_eq]
        have h_e : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
          rw [← Real.exp_add]; ring_nf
        have h_ne : Real.exp (-x) = Real.exp (-x / 2) * Real.exp (-x / 2) := by
          rw [← Real.exp_add]; ring_nf
        have h_prod : Real.exp (x / 2) * Real.exp (-x / 2) = 1 := by
          rw [← Real.exp_add]; ring_nf; simp
        rw [h_e, h_ne]
        linear_combination 2 * h_prod
      have h_ratio : Real.sinh x / (Real.cosh x - 1) =
          (Real.exp (x / 2) + Real.exp (-x / 2)) / (Real.exp (x / 2) - Real.exp (-x / 2)) := by
        calc Real.sinh x / (Real.cosh x - 1)
            = (2 * Real.sinh x) / (2 * (Real.cosh x - 1)) := by field_simp
          _ = ((Real.exp (x / 2) - Real.exp (-x / 2)) * (Real.exp (x / 2) + Real.exp (-x / 2))) /
                ((Real.exp (x / 2) - Real.exp (-x / 2)) ^ 2) := by rw [h_id1, h_id2]
          _ = (Real.exp (x / 2) + Real.exp (-x / 2)) / (Real.exp (x / 2) - Real.exp (-x / 2)) := by
              field_simp [he_sub.ne']
      rw [h_ratio, div_le_iff₀ he_sub]
      have hexp_le : x + 1 ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
      have hprod : Real.exp (x / 2) * Real.exp (-x / 2) = 1 := by
        rw [← Real.exp_add]; ring_nf; simp
      have h_mul : Real.exp (-x / 2) * (x + 1) ≤ Real.exp (x / 2) := by
        calc Real.exp (-x / 2) * (x + 1) ≤ Real.exp (-x / 2) * Real.exp x := by
              gcongr
          _ = Real.exp (x / 2) := by rw [← Real.exp_add]; ring_nf
      have hdiff : 0 ≤ (1 + 2 / x) * (Real.exp (x / 2) - Real.exp (-x / 2)) -
          (Real.exp (x / 2) + Real.exp (-x / 2)) := by
        have h_id : (1 + 2 / x) * (Real.exp (x / 2) - Real.exp (-x / 2)) -
            (Real.exp (x / 2) + Real.exp (-x / 2)) =
            2 / x * (Real.exp (x / 2) - (x + 1) * Real.exp (-x / 2)) := by
          field_simp [hxpos.ne']
          ring
        rw [h_id]
        exact mul_nonneg (by positivity) (by linarith)
      linarith
    have h3 : 2 / x ≤ π / √(x ^ 2 + y ^ 2) := by
      have hsq : √(x ^ 2 + y ^ 2) ≤ √2 * x := by
        conv_rhs => rw [← Real.sqrt_sq hx0, ← Real.sqrt_mul (by norm_num)]
        exact Real.sqrt_le_sqrt (by nlinarith)
      have hsqrt2 : √2 < 1.42 := by
        rw [Real.sqrt_lt' (by norm_num)]; norm_num
      have hpi2 : √(x ^ 2 + y ^ 2) ≤ (π / 2) * x := by
        have := Real.pi_gt_d4
        nlinarith
      rw [div_le_div_iff₀ hxpos (Real.sqrt_pos.mpr (by positivity))]
      linarith
    linarith
  · have hsinh_le : Real.sinh x ≤ 2 * x := by
      have hcosh_le : ∀ t ∈ Icc (0 : ℝ) x, Real.cosh t ≤ 2 := fun t ht => by
        have ht_ub : t ≤ 1 := by linarith [ht.2]
        have he1 : Real.exp t ≤ Real.exp 1 := Real.exp_le_exp.mpr ht_ub
        have he2 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
        rw [Real.cosh_eq]
        linarith [Real.exp_one_lt_three]
      have hdiff : ∀ t ∈ Icc (0 : ℝ) x, ‖Real.cosh t‖ ≤ 2 := fun t ht => by
        rw [Real.norm_of_nonneg (Real.cosh_pos t).le]
        exact hcosh_le t ht
      have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := Real.sinh) (f' := Real.cosh) (x := 0) (y := x)
        (fun t _ => (Real.hasDerivAt_sinh t).hasDerivWithinAt) hdiff (convex_Icc 0 x)
        (left_mem_Icc.mpr hx0) (right_mem_Icc.mpr hx0)
      simp only [Real.sinh_zero, sub_zero, Real.norm_of_nonneg hsinh_nn,
        Real.norm_of_nonneg hx0] at hmv
      linarith
    have hden := cosh_sub_cos_ge_of_le (x := x) hy0.le hy_ub
    have hxy_lb : 2 * x * y ≤ x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg (x - y)]
    have hfrac1 : Real.sinh x / (Real.cosh x - Real.cos y) ≤ 2 / (0.998 * y) := by
      have h_num : Real.sinh x ≤ 2 * x := hsinh_le
      have h1 : Real.sinh x / (Real.cosh x - Real.cos y) ≤
          (2 * x) / (0.998 * (x ^ 2 + y ^ 2) / 2) := by
        exact div_le_div₀ (by positivity) h_num (by positivity) hden
      have h2 : (2 * x) / (0.998 * (x ^ 2 + y ^ 2) / 2) ≤ 2 / (0.998 * y) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      exact h1.trans h2
    have hsqrt2 : √(x ^ 2 + y ^ 2) ≤ √2 * y := by
      conv_rhs => rw [← Real.sqrt_sq hy0.le, ← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hsqrt2_lt : √2 < 1.42 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have hfrac2 : 2 / (0.998 * y) ≤ π / √(x ^ 2 + y ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (Real.sqrt_pos.mpr (by positivity))]
      have := Real.pi_gt_d4
      have hmul : 2 * √(x ^ 2 + y ^ 2) ≤ 2 * (1.42 * y) := by nlinarith
      nlinarith
    have := hfrac1.trans hfrac2
    linarith

/-- Pointwise bound `(K3)` on `p₁(s)` for `0 < σ₀ ≤ 0.04`. -/
theorem stripPoissonP1_le {σ₀ : ℝ} (h0 : 0 < σ₀) (h4 : σ₀ ≤ 0.04) (s : ℝ) :
    stripPoissonP1 σ₀ s ≤ π * σ₀ * Real.exp (-π * |s|) := by
  have hy0 : 0 < π * σ₀ := mul_pos Real.pi_pos h0
  have hy_lt : π * σ₀ < π / 2 := by nlinarith [Real.pi_pos]
  have hcos_nn : 0 ≤ Real.cos (π * σ₀) := (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hy_lt⟩).le
  have hden : (1 / 2 : ℝ) * Real.exp (π * |s|) ≤ Real.cosh (π * s) + Real.cos (π * σ₀) := by
    have := half_exp_abs_le_cosh (π * s)
    rw [abs_mul, abs_of_pos Real.pi_pos] at this
    linarith
  have hsin : Real.sin (π * σ₀) ≤ π * σ₀ := Real.sin_le hy0.le
  unfold stripPoissonP1
  calc (1 / 2 : ℝ) * Real.sin (π * σ₀) / (Real.cosh (π * s) + Real.cos (π * σ₀))
      ≤ (1 / 2 : ℝ) * (π * σ₀) / ((1 / 2 : ℝ) * Real.exp (π * |s|)) := by
        exact div_le_div₀ (by positivity) (by gcongr) (by positivity) hden
    _ = π * σ₀ * Real.exp (-π * |s|) := by
        rw [show -π * |s| = -(π * |s|) by ring, Real.exp_neg]
        field_simp

/-- Derivative bound `(K3)` on `p₁(s)` for `0 < σ₀ ≤ 0.04`. -/
theorem abs_deriv_stripPoissonP1_le {σ₀ : ℝ} (h0 : 0 < σ₀) (h4 : σ₀ ≤ 0.04) (s : ℝ) :
    |deriv (stripPoissonP1 σ₀) s| ≤ π * stripPoissonP1 σ₀ s := by
  have h1 : σ₀ < 1 := by linarith
  rw [(stripPoissonP1_hasDerivAt h0 h1 s).deriv]
  have hp1_pos : 0 < stripPoissonP1 σ₀ s := stripPoissonP1_pos h0 h1 s
  have hden_pos : 0 < Real.cosh (π * s) + Real.cos (π * σ₀) := stripPoissonP1_den_pos h0 h1 s
  have hcos_nn : 0 ≤ Real.cos (π * σ₀) :=
    (Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩).le
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos Real.pi_pos, abs_of_pos hp1_pos,
    abs_div, abs_of_pos hden_pos]
  have hratio : |Real.sinh (π * s)| / (Real.cosh (π * s) + Real.cos (π * σ₀)) ≤ 1 := by
    rw [div_le_one hden_pos]
    linarith [abs_sinh_le_cosh (π * s)]
  calc π * (|Real.sinh (π * s)| / (Real.cosh (π * s) + Real.cos (π * σ₀))) * stripPoissonP1 σ₀ s
      ≤ π * 1 * stripPoissonP1 σ₀ s := by gcongr
    _ = π * stripPoissonP1 σ₀ s := by ring

private lemma two_mul_p_add_p1_le_inv_sigma {σ₀ : ℝ} (h0 : 0 < σ₀) (h4 : σ₀ ≤ 0.04) :
    2 * stripPoissonP σ₀ 0 + 2 * stripPoissonP1 σ₀ 0 ≤ 1 / σ₀ := by
  have h1 : σ₀ < 1 := by linarith
  have hp0 : 2 * stripPoissonP σ₀ 0 ≤ 2 / (π * σ₀) := by
    calc 2 * stripPoissonP σ₀ 0 ≤ 2 * (1 / (π * σ₀)) := by
          gcongr; exact stripPoissonP_zero_le h0 h1
      _ = 2 / (π * σ₀) := by ring
  have hp1_0 : 2 * stripPoissonP1 σ₀ 0 ≤ π * σ₀ := by
    rw [stripPoissonP1_zero_eq h0 h1, Real.tan_eq_sin_div_cos]
    have hy0 : 0 < π * σ₀ / 2 := by positivity
    have hy_ub : π * σ₀ / 2 ≤ 0.063 := by nlinarith [Real.pi_lt_d4]
    have hcos_ge : (0.9 : ℝ) ≤ Real.cos (π * σ₀ / 2) := by
      have h1c := Real.one_sub_sq_div_two_le_cos (x := π * σ₀ / 2)
      nlinarith
    have hsin_le : Real.sin (π * σ₀ / 2) ≤ π * σ₀ / 2 := Real.sin_le hy0.le
    have hlin : (π * σ₀ / 2) / 0.9 ≤ π * σ₀ := by
      rw [div_le_iff₀ (by norm_num)]
      linarith [mul_pos Real.pi_pos h0]
    calc 2 * ((1 / 2 : ℝ) * (Real.sin (π * σ₀ / 2) / Real.cos (π * σ₀ / 2)))
        = Real.sin (π * σ₀ / 2) / Real.cos (π * σ₀ / 2) := by ring
      _ ≤ (π * σ₀ / 2) / 0.9 := div_le_div₀ (by positivity) hsin_le (by norm_num) hcos_ge
      _ ≤ π * σ₀ := hlin
  have hpi_gt : (3.1415 : ℝ) < π := Real.pi_gt_d4
  have hpi_lt : π < 3.1416 := Real.pi_lt_d4
  have hmain : 2 / (π * σ₀) + π * σ₀ ≤ 1 / σ₀ := by
    have hden_pos : 0 < π * σ₀ := mul_pos Real.pi_pos h0
    rw [div_add' _ _ _ hden_pos.ne', div_le_div_iff₀ hden_pos h0]
    have h_prod : π * σ₀ ≤ 3.1416 * 0.04 := mul_le_mul hpi_lt.le h4 h0.le (by norm_num)
    have hpi2 : (π * σ₀) ^ 2 ≤ (3.1416 * 0.04) ^ 2 := pow_le_pow_left₀ hden_pos.le h_prod 2
    have hstep : (2 + π * σ₀ * (π * σ₀)) * σ₀ ≤ (2 + (3.1416 * 0.04) ^ 2) * σ₀ := by
      nlinarith [hpi2, show (π * σ₀) ^ 2 = π * σ₀ * (π * σ₀) by ring]
    nlinarith
  linarith

private lemma eVariationOn_add_le {f g : ℝ → ℝ} {s : Set ℝ} :
    eVariationOn (fun x => f x + g x) s ≤ eVariationOn f s + eVariationOn g s := by
  refine iSup_le fun ⟨n, u, hu, hus⟩ => ?_
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) + g (u (i + 1))) (f (u i) + g (u i))
      ≤ ∑ i ∈ Finset.range n, (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) :=
        Finset.sum_le_sum fun i _ => edist_add_add_le _ _ _ _
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
          ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

private lemma eVariationOn_const_mul_le (c : ℝ) (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => c * f x) s ≤ ENNReal.ofReal |c| * eVariationOn f s := by
  refine iSup_le fun ⟨n, u, hu, hus⟩ => ?_
  calc ∑ i ∈ Finset.range n, edist (c * f (u (i + 1))) (c * f (u i))
      = ∑ i ∈ Finset.range n, ENNReal.ofReal |c| * edist (f (u (i + 1))) (f (u i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul,
          ENNReal.ofReal_mul (abs_nonneg c)]
    _ = ENNReal.ofReal |c| * ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) := by
        rw [← Finset.mul_sum]
    _ ≤ ENNReal.ofReal |c| * eVariationOn f s := by
        gcongr; exact eVariationOn.sum_le hu hus

private lemma eVariationOn_even_unimodal_univ {f : ℝ → ℝ} (h0 : ∀ x, 0 ≤ f x)
    (hmono : MonotoneOn f (Iic 0)) (hanti : AntitoneOn f (Ici 0)) :
    eVariationOn f univ ≤ ENNReal.ofReal (2 * f 0) := by
  rw [eVariationOn.eq_biSup_inter_Icc]
  refine iSup₂_le fun p hab => ?_
  rcases p with ⟨a, b⟩
  dsimp only at hab ⊢
  simp only [mem_ofPred_eq, mem_univ, true_and] at hab
  rw [univ_inter]
  rcases le_total b 0 with hb0 | h0b
  · have hm : MonotoneOn f (Icc a b) := hmono.mono (fun x hx => hx.2.trans hb0)
    have hev := hm.eVariationOn_eq (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
    rw [inter_self] at hev
    rw [hev]
    have ha0' : a ≤ 0 := hab.trans hb0
    exact ENNReal.ofReal_le_ofReal (by linarith [hmono ha0' le_rfl ha0', hmono hb0 le_rfl hb0, h0 a])
  · rcases le_total 0 a with h0a | ha0
    · have ha : AntitoneOn f (Icc a b) := hanti.mono (fun x hx => h0a.trans hx.1)
      have hm : MonotoneOn (-f) (Icc a b) := fun x hx y hy hxy => neg_le_neg (ha hx hy hxy)
      have hev : eVariationOn f (Icc a b) = eVariationOn (-f) (Icc a b) := by
        simp only [eVariationOn, Pi.neg_apply, edist_neg_neg]
      have hev1 := hm.eVariationOn_eq (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
      rw [inter_self] at hev1
      rw [hev, hev1]
      simp only [Pi.neg_apply, neg_sub_neg]
      exact ENNReal.ofReal_le_ofReal (by linarith [hanti le_rfl h0a h0a, h0 b, h0 0])
    · have hsplit := eVariationOn.Icc_add_Icc f ha0 h0b (mem_univ (0 : ℝ))
      simp only [univ_inter] at hsplit
      rw [← hsplit]
      have hm1 : MonotoneOn f (Icc a 0) := hmono.mono (fun x hx => hx.2)
      have ha2 : AntitoneOn f (Icc 0 b) := hanti.mono (fun x hx => hx.1)
      have hm2 : MonotoneOn (-f) (Icc 0 b) := fun x hx y hy hxy => neg_le_neg (ha2 hx hy hxy)
      have hev2 : eVariationOn f (Icc 0 b) = eVariationOn (-f) (Icc 0 b) := by
        simp only [eVariationOn, Pi.neg_apply, edist_neg_neg]
      have hev1' := hm1.eVariationOn_eq (left_mem_Icc.mpr ha0) (right_mem_Icc.mpr ha0)
      rw [inter_self] at hev1'
      have hev2' := hm2.eVariationOn_eq (left_mem_Icc.mpr h0b) (right_mem_Icc.mpr h0b)
      rw [inter_self] at hev2'
      rw [hev1', hev2, hev2']
      simp only [Pi.neg_apply, neg_sub_neg]
      rw [← ENNReal.ofReal_add (by linarith [hm1 ⟨le_rfl, ha0⟩ ⟨ha0, le_rfl⟩ ha0])
        (by linarith [ha2 ⟨le_rfl, h0b⟩ ⟨h0b, le_rfl⟩ h0b])]
      exact ENNReal.ofReal_le_ofReal (by linarith [h0 a, h0 b])

/-- Total variation bound `(K4)`: `TV_ℝ(Q) ≤ 2 p(0) + 2 p₁(0) ≤ 1 / σ₀` for `0 < σ₀ ≤ 0.04` and `|ε| ≤ 1`. -/
theorem eVariationOn_stripPoissonQ_le {σ₀ : ℝ} (h0 : 0 < σ₀) (h4 : σ₀ ≤ 0.04)
    (η₀ : ℝ) {ε : ℝ} (hε : |ε| ≤ 1) :
    eVariationOn (stripPoissonQ σ₀ η₀ ε) univ ≤ ENNReal.ofReal (1 / σ₀) := by
  have h1 : σ₀ < 1 := by linarith
  have hp_tv : eVariationOn (fun τ => stripPoissonP σ₀ (τ - η₀)) univ ≤
      ENNReal.ofReal (2 * stripPoissonP σ₀ 0) := by
    calc eVariationOn (fun τ => stripPoissonP σ₀ (τ - η₀)) univ
        ≤ eVariationOn (stripPoissonP σ₀) univ :=
          eVariationOn.comp_le_of_monotoneOn (stripPoissonP σ₀) (fun τ => τ - η₀)
            (fun x _ y _ hxy => by linarith) (mapsTo_univ _ _)
      _ ≤ ENNReal.ofReal (2 * stripPoissonP σ₀ 0) :=
          eVariationOn_even_unimodal_univ (fun x => (stripPoissonP_pos h0 h1 x).le)
            (stripPoissonP_monotoneOn_Iic h0 h1) (stripPoissonP_antitoneOn_Ici h0 h1)
  have hp1_tv : eVariationOn (fun τ => stripPoissonP1 σ₀ (τ + η₀)) univ ≤
      ENNReal.ofReal (2 * stripPoissonP1 σ₀ 0) := by
    calc eVariationOn (fun τ => stripPoissonP1 σ₀ (τ + η₀)) univ
        ≤ eVariationOn (stripPoissonP1 σ₀) univ :=
          eVariationOn.comp_le_of_monotoneOn (stripPoissonP1 σ₀) (fun τ => τ + η₀)
            (fun x _ y _ hxy => by linarith) (mapsTo_univ _ _)
      _ ≤ ENNReal.ofReal (2 * stripPoissonP1 σ₀ 0) :=
          eVariationOn_even_unimodal_univ (fun x => (stripPoissonP1_pos h0 h1 x).le)
            (stripPoissonP1_monotoneOn_Iic h0 h1) (stripPoissonP1_antitoneOn_Ici h0 h1)
  have hq_unfold : stripPoissonQ σ₀ η₀ ε =
      (fun τ => stripPoissonP σ₀ (τ - η₀) + ε * stripPoissonP1 σ₀ (τ + η₀)) := rfl
  rw [hq_unfold]
  calc eVariationOn (fun τ => stripPoissonP σ₀ (τ - η₀) + ε * stripPoissonP1 σ₀ (τ + η₀)) univ
      ≤ eVariationOn (fun τ => stripPoissonP σ₀ (τ - η₀)) univ +
          eVariationOn (fun τ => ε * stripPoissonP1 σ₀ (τ + η₀)) univ := eVariationOn_add_le
    _ ≤ ENNReal.ofReal (2 * stripPoissonP σ₀ 0) +
          ENNReal.ofReal |ε| * eVariationOn (fun τ => stripPoissonP1 σ₀ (τ + η₀)) univ :=
        add_le_add hp_tv (eVariationOn_const_mul_le ε _ univ)
    _ ≤ ENNReal.ofReal (2 * stripPoissonP σ₀ 0) +
          1 * ENNReal.ofReal (2 * stripPoissonP1 σ₀ 0) := by
        gcongr
        simpa using ENNReal.ofReal_le_ofReal hε
    _ = ENNReal.ofReal (2 * stripPoissonP σ₀ 0 + 2 * stripPoissonP1 σ₀ 0) := by
        have hp0_nn : 0 ≤ stripPoissonP σ₀ 0 := (stripPoissonP_pos h0 h1 0).le
        have hp10_nn : 0 ≤ stripPoissonP1 σ₀ 0 := (stripPoissonP1_pos h0 h1 0).le
        rw [one_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (1 / σ₀) :=
        ENNReal.ofReal_le_ofReal (two_mul_p_add_p1_le_inv_sigma h0 h4)

/-- Real-valued total variation bound `(K4)`. -/
theorem stripPoissonQ_tv_le {σ₀ : ℝ} (h0 : 0 < σ₀) (h4 : σ₀ ≤ 0.04)
    (η₀ : ℝ) {ε : ℝ} (hε : |ε| ≤ 1) :
    (eVariationOn (stripPoissonQ σ₀ η₀ ε) univ).toReal ≤ 1 / σ₀ :=
  ENNReal.toReal_le_of_le_ofReal (by positivity) (eVariationOn_stripPoissonQ_le h0 h4 η₀ hε)

/-- Pointwise bound `(Q-a)`: `𝒬(τ) ≤ 1 / σ₀` on `ℝ` for `0 < σ₀ ≤ 0.04`. -/
theorem stripPoissonCalQ_le {σ₀ : ℝ} (h0 : 0 < σ₀) (h4 : σ₀ ≤ 0.04) (η₀ τ : ℝ) :
    stripPoissonCalQ σ₀ η₀ τ ≤ 1 / σ₀ := by
  have h1 : σ₀ < 1 := by linarith
  have hp_le : stripPoissonP σ₀ (τ - η₀) ≤ stripPoissonP σ₀ 0 := by
    rcases le_total 0 (τ - η₀) with h | h
    · exact stripPoissonP_antitoneOn_Ici h0 h1 le_rfl h h
    · exact stripPoissonP_monotoneOn_Iic h0 h1 h le_rfl h
  have hp1_le : stripPoissonP1 σ₀ (τ + η₀) ≤ stripPoissonP1 σ₀ 0 := by
    rcases le_total 0 (τ + η₀) with h | h
    · exact stripPoissonP1_antitoneOn_Ici h0 h1 le_rfl h h
    · exact stripPoissonP1_monotoneOn_Iic h0 h1 h le_rfl h
  have hsum := two_mul_p_add_p1_le_inv_sigma h0 h4
  have hp0_nn : 0 ≤ stripPoissonP σ₀ 0 := (stripPoissonP_pos h0 h1 0).le
  have hp1_nn : 0 ≤ stripPoissonP1 σ₀ 0 := (stripPoissonP1_pos h0 h1 0).le
  unfold stripPoissonCalQ
  linarith

private lemma stripPoissonQ_hasDerivAt {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) (η₀ ε τ : ℝ) :
    HasDerivAt (stripPoissonQ σ₀ η₀ ε)
      (deriv (stripPoissonP σ₀) (τ - η₀) + ε * deriv (stripPoissonP1 σ₀) (τ + η₀)) τ := by
  have h_sub : HasDerivAt (fun t => t - η₀) 1 τ := by simpa using (hasDerivAt_id τ).sub_const η₀
  have h_add : HasDerivAt (fun t => t + η₀) 1 τ := by simpa using (hasDerivAt_id τ).add_const η₀
  have hp : HasDerivAt (fun t => stripPoissonP σ₀ (t - η₀)) (deriv (stripPoissonP σ₀) (τ - η₀)) τ := by
    have hd := (stripPoissonP_hasDerivAt h0 h1 (τ - η₀))
    rw [← hd.deriv] at hd
    exact (hd.comp τ h_sub).congr_deriv (mul_one _)
  have hp1 : HasDerivAt (fun t => stripPoissonP1 σ₀ (t + η₀)) (deriv (stripPoissonP1 σ₀) (τ + η₀)) τ := by
    have hd := (stripPoissonP1_hasDerivAt h0 h1 (τ + η₀))
    rw [← hd.deriv] at hd
    exact (hd.comp τ h_add).congr_deriv (mul_one _)
  exact hp.add (hp1.const_mul ε)

private lemma continuous_deriv_stripPoissonP {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) :
    Continuous (deriv (stripPoissonP σ₀)) := by
  have heq : deriv (stripPoissonP σ₀) = fun s =>
      -π * (Real.sinh (π * s) / (Real.cosh (π * s) - Real.cos (π * σ₀))) * stripPoissonP σ₀ s := by
    ext s; exact (stripPoissonP_hasDerivAt h0 h1 s).deriv
  rw [heq]
  have hden : ∀ s : ℝ, Real.cosh (π * s) - Real.cos (π * σ₀) ≠ 0 :=
    fun s => (stripPoissonP_den_pos h0 h1 s).ne'
  unfold stripPoissonP
  fun_prop (disch := exact hden _)

private lemma continuous_deriv_stripPoissonP1 {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) :
    Continuous (deriv (stripPoissonP1 σ₀)) := by
  have heq : deriv (stripPoissonP1 σ₀) = fun s =>
      -π * (Real.sinh (π * s) / (Real.cosh (π * s) + Real.cos (π * σ₀))) * stripPoissonP1 σ₀ s := by
    ext s; exact (stripPoissonP1_hasDerivAt h0 h1 s).deriv
  rw [heq]
  have hden : ∀ s : ℝ, Real.cosh (π * s) + Real.cos (π * σ₀) ≠ 0 :=
    fun s => (stripPoissonP1_den_pos h0 h1 s).ne'
  unfold stripPoissonP1
  fun_prop (disch := exact hden _)

private lemma continuous_deriv_stripPoissonQ {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) (η₀ ε : ℝ) :
    Continuous (deriv (stripPoissonQ σ₀ η₀ ε)) := by
  have heq : deriv (stripPoissonQ σ₀ η₀ ε) = fun τ =>
      deriv (stripPoissonP σ₀) (τ - η₀) + ε * deriv (stripPoissonP1 σ₀) (τ + η₀) := by
    ext τ; exact (stripPoissonQ_hasDerivAt h0 h1 η₀ ε τ).deriv
  rw [heq]
  exact ((continuous_deriv_stripPoissonP h0 h1).comp (continuous_id.sub continuous_const)).add
    (continuous_const.mul ((continuous_deriv_stripPoissonP1 h0 h1).comp (continuous_id.add continuous_const)))

private lemma integral_abs_deriv_even_unimodal {f : ℝ → ℝ} (hf_pos : ∀ s, 0 ≤ f s)
    (hf_deriv : ∀ s, HasDerivAt f (deriv f s) s) (hf'_cont : Continuous (deriv f))
    (hf'_nonneg : ∀ s ≤ 0, 0 ≤ deriv f s) (hf'_nonpos : ∀ s ≥ 0, deriv f s ≤ 0)
    (a b : ℝ) (hab : a ≤ b) :
    ∫ s in a..b, |deriv f s| ≤ 2 * f 0 := by
  let a' := min a 0
  let b' := max b 0
  have ha' : a' ≤ 0 := min_le_right _ _
  have hb' : 0 ≤ b' := le_max_right _ _
  have hsub : ∫ s in a..b, |deriv f s| ≤ ∫ s in a'..b', |deriv f s| := by
    refine intervalIntegral.integral_mono_interval (min_le_left _ _) hab (le_max_left _ _) ?_ ?_
    · filter_upwards with s; exact abs_nonneg _
    · exact (hf'_cont.abs).intervalIntegrable _ _
  have hsplit : ∫ s in a'..b', |deriv f s| =
      (∫ s in a'..0, |deriv f s|) + ∫ s in 0..b', |deriv f s| :=
    (intervalIntegral.integral_add_adjacent_intervals
      ((hf'_cont.abs).intervalIntegrable a' 0) ((hf'_cont.abs).intervalIntegrable 0 b')).symm
  have hL : ∫ s in a'..0, |deriv f s| = f 0 - f a' := by
    have hcongr : ∫ s in a'..0, |deriv f s| = ∫ s in a'..0, deriv f s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le ha'] at hs
      exact abs_of_nonneg (hf'_nonneg s hs.2)
    rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hf_deriv s)
      (hf'_cont.intervalIntegrable a' 0)]
  have hR : ∫ s in 0..b', |deriv f s| = f 0 - f b' := by
    have hcongr : ∫ s in 0..b', |deriv f s| = ∫ s in 0..b', -deriv f s := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le hb'] at hs
      exact abs_of_nonpos (hf'_nonpos s hs.1)
    rw [hcongr, intervalIntegral.integral_neg,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hf_deriv s)
        (hf'_cont.intervalIntegrable 0 b')]
    ring
  rw [hsplit, hL, hR] at hsub
  linarith [hf_pos a', hf_pos b']

/-- Derivative integral bound `(Q-a)`: `∫ τ in a..b, |Q'(τ)| ≤ 1 / σ₀` for every interval `[a, b]`. -/
theorem integral_abs_deriv_stripPoissonQ_le {σ₀ : ℝ} (h0 : 0 < σ₀) (h4 : σ₀ ≤ 0.04)
    (η₀ : ℝ) {ε : ℝ} (hε : |ε| ≤ 1) {a b : ℝ} (hab : a ≤ b) :
    ∫ τ in a..b, |deriv (stripPoissonQ σ₀ η₀ ε) τ| ≤ 1 / σ₀ := by
  have h1 : σ₀ < 1 := by linarith
  have hpt : ∀ τ, |deriv (stripPoissonQ σ₀ η₀ ε) τ| ≤
      |deriv (stripPoissonP σ₀) (τ - η₀)| + |deriv (stripPoissonP1 σ₀) (τ + η₀)| := fun τ => by
    rw [(stripPoissonQ_hasDerivAt h0 h1 η₀ ε τ).deriv]
    calc |deriv (stripPoissonP σ₀) (τ - η₀) + ε * deriv (stripPoissonP1 σ₀) (τ + η₀)|
        ≤ |deriv (stripPoissonP σ₀) (τ - η₀)| + |ε * deriv (stripPoissonP1 σ₀) (τ + η₀)| :=
          abs_add_le _ _
      _ = |deriv (stripPoissonP σ₀) (τ - η₀)| + |ε| * |deriv (stripPoissonP1 σ₀) (τ + η₀)| := by
          rw [abs_mul]
      _ ≤ |deriv (stripPoissonP σ₀) (τ - η₀)| + 1 * |deriv (stripPoissonP1 σ₀) (τ + η₀)| := by
          gcongr
      _ = |deriv (stripPoissonP σ₀) (τ - η₀)| + |deriv (stripPoissonP1 σ₀) (τ + η₀)| := by ring
  have hiQ : IntervalIntegrable (fun τ => |deriv (stripPoissonQ σ₀ η₀ ε) τ|) volume a b :=
    (continuous_deriv_stripPoissonQ h0 h1 η₀ ε).abs.intervalIntegrable a b
  have hiP : IntervalIntegrable (fun τ => |deriv (stripPoissonP σ₀) (τ - η₀)|) volume a b :=
    ((continuous_deriv_stripPoissonP h0 h1).comp (continuous_id.sub continuous_const)).abs.intervalIntegrable a b
  have hiP1 : IntervalIntegrable (fun τ => |deriv (stripPoissonP1 σ₀) (τ + η₀)|) volume a b :=
    ((continuous_deriv_stripPoissonP1 h0 h1).comp (continuous_id.add continuous_const)).abs.intervalIntegrable a b
  have hmono := intervalIntegral.integral_mono_on hab hiQ (hiP.add hiP1) (fun τ _ => hpt τ)
  rw [intervalIntegral.integral_add hiP hiP1, intervalIntegral.integral_comp_sub_right
    (fun s => |deriv (stripPoissonP σ₀) s|) η₀, intervalIntegral.integral_comp_add_right
    (fun s => |deriv (stripPoissonP1 σ₀) s|) η₀] at hmono
  have hp_d : ∀ s, HasDerivAt (stripPoissonP σ₀) (deriv (stripPoissonP σ₀) s) s := fun s => by
    have hd := stripPoissonP_hasDerivAt h0 h1 s
    rwa [hd.deriv]
  have hp1_d : ∀ s, HasDerivAt (stripPoissonP1 σ₀) (deriv (stripPoissonP1 σ₀) s) s := fun s => by
    have hd := stripPoissonP1_hasDerivAt h0 h1 s
    rwa [hd.deriv]
  have hp_nn : ∀ s ≤ 0, 0 ≤ deriv (stripPoissonP σ₀) s := fun s hs => by
    rw [(stripPoissonP_hasDerivAt h0 h1 s).deriv]
    have hsh : Real.sinh (π * s) ≤ 0 := Real.sinh_nonpos_iff.mpr (mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le hs)
    have hden : 0 < Real.cosh (π * s) - Real.cos (π * σ₀) := stripPoissonP_den_pos h0 h1 s
    have hp_pos : 0 < stripPoissonP σ₀ s := stripPoissonP_pos h0 h1 s
    have hmul : Real.sinh (π * s) / (Real.cosh (π * s) - Real.cos (π * σ₀)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hsh hden.le
    exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith [Real.pi_pos]) hmul) hp_pos.le
  have hp_np : ∀ s ≥ 0, deriv (stripPoissonP σ₀) s ≤ 0 := fun s hs => by
    rw [(stripPoissonP_hasDerivAt h0 h1 s).deriv]
    have hsh : 0 ≤ Real.sinh (π * s) := Real.sinh_nonneg_iff.mpr (mul_nonneg Real.pi_pos.le hs)
    have hden : 0 < Real.cosh (π * s) - Real.cos (π * σ₀) := stripPoissonP_den_pos h0 h1 s
    have hp_pos : 0 < stripPoissonP σ₀ s := stripPoissonP_pos h0 h1 s
    have hmul : 0 ≤ Real.sinh (π * s) / (Real.cosh (π * s) - Real.cos (π * σ₀)) :=
      div_nonneg hsh hden.le
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) hmul) hp_pos.le
  have hp1_nn : ∀ s ≤ 0, 0 ≤ deriv (stripPoissonP1 σ₀) s := fun s hs => by
    rw [(stripPoissonP1_hasDerivAt h0 h1 s).deriv]
    have hsh : Real.sinh (π * s) ≤ 0 := Real.sinh_nonpos_iff.mpr (mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le hs)
    have hden : 0 < Real.cosh (π * s) + Real.cos (π * σ₀) := stripPoissonP1_den_pos h0 h1 s
    have hp1_pos : 0 < stripPoissonP1 σ₀ s := stripPoissonP1_pos h0 h1 s
    have hmul : Real.sinh (π * s) / (Real.cosh (π * s) + Real.cos (π * σ₀)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hsh hden.le
    exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith [Real.pi_pos]) hmul) hp1_pos.le
  have hp1_np : ∀ s ≥ 0, deriv (stripPoissonP1 σ₀) s ≤ 0 := fun s hs => by
    rw [(stripPoissonP1_hasDerivAt h0 h1 s).deriv]
    have hsh : 0 ≤ Real.sinh (π * s) := Real.sinh_nonneg_iff.mpr (mul_nonneg Real.pi_pos.le hs)
    have hden : 0 < Real.cosh (π * s) + Real.cos (π * σ₀) := stripPoissonP1_den_pos h0 h1 s
    have hp1_pos : 0 < stripPoissonP1 σ₀ s := stripPoissonP1_pos h0 h1 s
    have hmul : 0 ≤ Real.sinh (π * s) / (Real.cosh (π * s) + Real.cos (π * σ₀)) :=
      div_nonneg hsh hden.le
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) hmul) hp1_pos.le
  have hI1 := integral_abs_deriv_even_unimodal (fun s => (stripPoissonP_pos h0 h1 s).le)
    hp_d (continuous_deriv_stripPoissonP h0 h1) hp_nn hp_np (a - η₀) (b - η₀) (by linarith)
  have hI2 := integral_abs_deriv_even_unimodal (fun s => (stripPoissonP1_pos h0 h1 s).le)
    hp1_d (continuous_deriv_stripPoissonP1 h0 h1) hp1_nn hp1_np (a + η₀) (b + η₀) (by linarith)
  exact hmono.trans ((add_le_add hI1 hI2).trans (two_mul_p_add_p1_le_inv_sigma h0 h4))

/-- Far-field bound `(Q-b)` on `𝒬(τ)` for `|τ| ≥ 2 √(σ₀² + η₀²)`. -/
theorem stripPoissonCalQ_le_of_two_mul_le {σ₀ : ℝ} (h0 : 0 < σ₀) (h4 : σ₀ ≤ 0.04)
    {η₀ τ : ℝ} (hτ : 2 * √(σ₀ ^ 2 + η₀ ^ 2) ≤ |τ|) :
    stripPoissonCalQ σ₀ η₀ τ ≤ 4 * σ₀ * (1 + τ ^ (-2 : ℝ)) * Real.exp (-π * |τ| / 4) := by
  have hη : |η₀| ≤ √(σ₀ ^ 2 + η₀ ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith [sq_nonneg σ₀])
  have hτ_pos : 0 < |τ| := by
    have : 0 < √(σ₀ ^ 2 + η₀ ^ 2) := Real.sqrt_pos.mpr (by positivity)
    linarith
  have hsub_ge : |τ| / 2 ≤ |τ - η₀| := by
    have : |τ| - |η₀| ≤ |τ - η₀| := abs_sub_abs_le_abs_sub τ η₀
    linarith
  have hadd_ge : |τ| / 2 ≤ |τ + η₀| := by
    have : |τ| - |η₀| ≤ |τ + η₀| := by
      simpa [sub_neg_eq_add, abs_neg] using abs_sub_abs_le_abs_sub τ (-η₀)
    linarith
  have hp_bound : stripPoissonP σ₀ (τ - η₀) ≤ 4 * σ₀ * τ ^ (-2 : ℝ) * Real.exp (-π * |τ| / 4) := by
    have hp := stripPoissonP_le h0 h4 (τ - η₀)
    have hden : τ ^ 2 / 4 ≤ (τ - η₀) ^ 2 + σ₀ ^ 2 := by
      have hsq : τ ^ 2 / 4 ≤ (τ - η₀) ^ 2 := by
        rw [← sq_abs τ, ← sq_abs (τ - η₀)]
        nlinarith [sq_nonneg (|τ - η₀| - |τ| / 2)]
      linarith [sq_nonneg σ₀]
    have hexp : Real.exp (-π * |τ - η₀| / 2) ≤ Real.exp (-π * |τ| / 4) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have hτ_ne : τ ≠ 0 := abs_pos.mp hτ_pos
    have hτ_rpow : τ ^ (-2 : ℝ) = (τ ^ 2)⁻¹ := by
      rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg, zpow_two, ← sq]
    rw [hτ_rpow]
    calc stripPoissonP σ₀ (τ - η₀)
        ≤ σ₀ * Real.exp (-π * |τ - η₀| / 2) / ((τ - η₀) ^ 2 + σ₀ ^ 2) := hp
      _ ≤ σ₀ * Real.exp (-π * |τ| / 4) / (τ ^ 2 / 4) :=
          div_le_div₀ (by positivity) (by gcongr) (by positivity) hden
      _ = 4 * σ₀ * (τ ^ 2)⁻¹ * Real.exp (-π * |τ| / 4) := by ring
  have hp1_bound : stripPoissonP1 σ₀ (τ + η₀) ≤ 4 * σ₀ * Real.exp (-π * |τ| / 4) := by
    have hp1 := stripPoissonP1_le h0 h4 (τ + η₀)
    have hexp1 : Real.exp (-π * |τ + η₀|) ≤ Real.exp (-π * |τ| / 4) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have hpi_le : π ≤ 4 := Real.pi_lt_four.le
    calc stripPoissonP1 σ₀ (τ + η₀)
        ≤ π * σ₀ * Real.exp (-π * |τ + η₀|) := hp1
      _ ≤ 4 * σ₀ * Real.exp (-π * |τ| / 4) := by gcongr
  have hτ_rpow : τ ^ (-2 : ℝ) = (τ ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg, zpow_two, ← sq]
  unfold stripPoissonCalQ
  calc stripPoissonP σ₀ (τ - η₀) + stripPoissonP1 σ₀ (τ + η₀)
      ≤ 4 * σ₀ * τ ^ (-2 : ℝ) * Real.exp (-π * |τ| / 4) +
          4 * σ₀ * Real.exp (-π * |τ| / 4) := add_le_add hp_bound hp1_bound
    _ = 4 * σ₀ * (1 + τ ^ (-2 : ℝ)) * Real.exp (-π * |τ| / 4) := by ring

/-- Far-field derivative bound `(Q-b)` for `|τ| ≥ 2 √(σ₀² + η₀²)` and `|ε| ≤ 1`. -/
theorem abs_deriv_stripPoissonQ_le_of_two_mul_le {σ₀ : ℝ} (h0 : 0 < σ₀) (h4 : σ₀ ≤ 0.04)
    {η₀ ε τ : ℝ} (hε : |ε| ≤ 1) (hτ : 2 * √(σ₀ ^ 2 + η₀ ^ 2) ≤ |τ|) :
    |deriv (stripPoissonQ σ₀ η₀ ε) τ| ≤
      π * (1 + 2 / |τ|) * stripPoissonCalQ σ₀ η₀ τ := by
  have h1 : σ₀ < 1 := by linarith
  have hη : |η₀| ≤ √(σ₀ ^ 2 + η₀ ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith [sq_nonneg σ₀])
  have hτ_pos : 0 < |τ| := by
    have : 0 < √(σ₀ ^ 2 + η₀ ^ 2) := Real.sqrt_pos.mpr (by positivity)
    linarith
  have hsub_ge : |τ| / 2 ≤ |τ - η₀| := by
    have : |τ| - |η₀| ≤ |τ - η₀| := abs_sub_abs_le_abs_sub τ η₀
    linarith
  have hr_ge : |τ| / 2 ≤ √((τ - η₀) ^ 2 + σ₀ ^ 2) := by
    calc |τ| / 2 ≤ |τ - η₀| := hsub_ge
      _ = √((τ - η₀) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ √((τ - η₀) ^ 2 + σ₀ ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg σ₀])
  have hinv_le : 1 / √((τ - η₀) ^ 2 + σ₀ ^ 2) ≤ 2 / |τ| := by
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by positivity)) hτ_pos]
    linarith
  rw [(stripPoissonQ_hasDerivAt h0 h1 η₀ ε τ).deriv]
  have hp_d := abs_deriv_stripPoissonP_le h0 h4 (τ - η₀)
  have hp1_d := abs_deriv_stripPoissonP1_le h0 h4 (τ + η₀)
  have hp_pos := (stripPoissonP_pos h0 h1 (τ - η₀)).le
  have hp1_pos := (stripPoissonP1_pos h0 h1 (τ + η₀)).le
  calc |deriv (stripPoissonP σ₀) (τ - η₀) + ε * deriv (stripPoissonP1 σ₀) (τ + η₀)|
      ≤ |deriv (stripPoissonP σ₀) (τ - η₀)| + |ε| * |deriv (stripPoissonP1 σ₀) (τ + η₀)| := by
        calc _ ≤ |deriv (stripPoissonP σ₀) (τ - η₀)| + |ε * deriv (stripPoissonP1 σ₀) (τ + η₀)| :=
              abs_add_le _ _
          _ = _ := by rw [abs_mul]
    _ ≤ π * (1 + 1 / √((τ - η₀) ^ 2 + σ₀ ^ 2)) * stripPoissonP σ₀ (τ - η₀) +
          1 * (π * stripPoissonP1 σ₀ (τ + η₀)) := by
        gcongr
    _ ≤ π * (1 + 2 / |τ|) * stripPoissonP σ₀ (τ - η₀) +
          π * (1 + 2 / |τ|) * stripPoissonP1 σ₀ (τ + η₀) := by
        refine add_le_add (by gcongr) ?_
        calc 1 * (π * stripPoissonP1 σ₀ (τ + η₀))
            = π * (1 + 0) * stripPoissonP1 σ₀ (τ + η₀) := by ring
          _ ≤ π * (1 + 2 / |τ|) * stripPoissonP1 σ₀ (τ + η₀) := by gcongr; positivity
    _ = π * (1 + 2 / |τ|) * stripPoissonCalQ σ₀ η₀ τ := by
        unfold stripPoissonCalQ; ring

/-- Far-field derivative bound `(Q-b)` on `±[s, 2s]` for `s ≥ 2 √(σ₀² + η₀²)`. -/
theorem integral_abs_deriv_stripPoissonQ_block_le {σ₀ : ℝ} (h0 : 0 < σ₀) (h4 : σ₀ ≤ 0.04)
    {η₀ ε s : ℝ} (hε : |ε| ≤ 1) (hs : 2 * √(σ₀ ^ 2 + η₀ ^ 2) ≤ s) :
    let qJ := 4 * σ₀ * (1 + s ^ (-2 : ℝ)) * Real.exp (-π * s / 4)
    (∀ τ, s ≤ |τ| → |τ| ≤ 2 * s → stripPoissonCalQ σ₀ η₀ τ ≤ qJ) ∧
    (∫ τ in s..(2 * s), |deriv (stripPoissonQ σ₀ η₀ ε) τ|) +
      (∫ τ in (-2 * s)..(-s), |deriv (stripPoissonQ σ₀ η₀ ε) τ|) ≤ 2 * π * (s + 2) * qJ := by
  have h1 : σ₀ < 1 := by linarith
  have hs_pos : 0 < s := lt_of_lt_of_le (by positivity) hs
  intro qJ
  have hq : ∀ τ, s ≤ |τ| → |τ| ≤ 2 * s → stripPoissonCalQ σ₀ η₀ τ ≤ qJ := by
    intro τ hτ_lo _
    have hτ_rho : 2 * √(σ₀ ^ 2 + η₀ ^ 2) ≤ |τ| := hs.trans hτ_lo
    have hcal := stripPoissonCalQ_le_of_two_mul_le h0 h4 hτ_rho
    have hτ_rpow : τ ^ (-2 : ℝ) ≤ s ^ (-2 : ℝ) := by
      rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, Real.rpow_intCast,
        zpow_neg, zpow_neg, zpow_two, zpow_two, ← sq, ← sq, ← sq_abs τ]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hs_pos.le hτ_lo 2)
    have hexp : Real.exp (-π * |τ| / 4) ≤ Real.exp (-π * s / 4) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    calc stripPoissonCalQ σ₀ η₀ τ
        ≤ 4 * σ₀ * (1 + τ ^ (-2 : ℝ)) * Real.exp (-π * |τ| / 4) := hcal
      _ ≤ 4 * σ₀ * (1 + s ^ (-2 : ℝ)) * Real.exp (-π * s / 4) := by gcongr
  refine ⟨hq, ?_⟩
  have hderiv_ub : ∀ τ, s ≤ |τ| → |τ| ≤ 2 * s →
      |deriv (stripPoissonQ σ₀ η₀ ε) τ| ≤ π * (1 + 2 / s) * qJ := by
    intro τ hlo hhi
    have hd := abs_deriv_stripPoissonQ_le_of_two_mul_le h0 h4 hε (hs.trans hlo)
    have hq_τ := hq τ hlo hhi
    have hinv : 2 / |τ| ≤ 2 / s := div_le_div_of_nonneg_left (by norm_num) hs_pos hlo
    have hqJ_nn : 0 ≤ qJ := by dsimp [qJ]; positivity
    have hcal_nn : 0 ≤ stripPoissonCalQ σ₀ η₀ τ := by
      unfold stripPoissonCalQ
      exact add_nonneg (stripPoissonP_pos h0 h1 _).le (stripPoissonP1_pos h0 h1 _).le
    calc |deriv (stripPoissonQ σ₀ η₀ ε) τ|
        ≤ π * (1 + 2 / |τ|) * stripPoissonCalQ σ₀ η₀ τ := hd
      _ ≤ π * (1 + 2 / s) * qJ := by gcongr
  have hiQ := (continuous_deriv_stripPoissonQ h0 h1 η₀ ε).abs
  have hpos_int : ∫ τ in s..(2 * s), |deriv (stripPoissonQ σ₀ η₀ ε) τ| ≤
      s * (π * (1 + 2 / s) * qJ) := by
    have hle : ∀ τ ∈ Icc s (2 * s), |deriv (stripPoissonQ σ₀ η₀ ε) τ| ≤ π * (1 + 2 / s) * qJ :=
      fun τ hτ => hderiv_ub τ (by rw [abs_of_nonneg (by linarith [hτ.1])]; exact hτ.1)
        (by rw [abs_of_nonneg (by linarith [hτ.1])]; exact hτ.2)
    have hthis := intervalIntegral.integral_mono_on (by linarith : s ≤ 2 * s)
      (hiQ.intervalIntegrable _ _) (intervalIntegrable_const (μ := volume)) hle
    rw [intervalIntegral.integral_const, smul_eq_mul] at hthis
    calc ∫ τ in s..(2 * s), |deriv (stripPoissonQ σ₀ η₀ ε) τ|
        ≤ (2 * s - s) * (π * (1 + 2 / s) * qJ) := hthis
      _ = s * (π * (1 + 2 / s) * qJ) := by ring
  have hneg_int : ∫ τ in (-2 * s)..(-s), |deriv (stripPoissonQ σ₀ η₀ ε) τ| ≤
      s * (π * (1 + 2 / s) * qJ) := by
    have hle : ∀ τ ∈ Icc (-2 * s) (-s), |deriv (stripPoissonQ σ₀ η₀ ε) τ| ≤ π * (1 + 2 / s) * qJ :=
      fun τ hτ => hderiv_ub τ (by rw [abs_of_nonpos (by linarith [hτ.2])]; linarith [hτ.2])
        (by rw [abs_of_nonpos (by linarith [hτ.2])]; linarith [hτ.1])
    have hthis := intervalIntegral.integral_mono_on (by linarith : -2 * s ≤ -s)
      (hiQ.intervalIntegrable _ _) (intervalIntegrable_const (μ := volume)) hle
    rw [intervalIntegral.integral_const, smul_eq_mul] at hthis
    calc ∫ τ in (-2 * s)..(-s), |deriv (stripPoissonQ σ₀ η₀ ε) τ|
        ≤ (-s - -2 * s) * (π * (1 + 2 / s) * qJ) := hthis
      _ = s * (π * (1 + 2 / s) * qJ) := by ring
  have halg : s * (π * (1 + 2 / s) * qJ) + s * (π * (1 + 2 / s) * qJ) =
      2 * π * (s + 2) * qJ := by
    field_simp [hs_pos.ne']
    ring
  linarith

end StripPoissonPartB

/-! ### Part 2: Stirling and Factorial Bound `(TE.7)` -/

section StirlingHalfInt

private lemma gamma_add_half_eq_factorial (k : ℕ) :
    Real.Gamma ((k : ℝ) + 1 / 2) = ((2 * k)! : ℝ) / ((4 : ℝ) ^ k * ((k)! : ℝ)) * √π := by
  induction k with
  | zero =>
    rw [Nat.cast_zero, zero_add, mul_zero, Nat.factorial_zero, pow_zero, Nat.cast_one, mul_one,
      div_one, Real.Gamma_one_half_eq, one_mul]
  | succ k ih =>
    have hne : (k : ℝ) + 1 / 2 ≠ 0 := by positivity
    have heq : ((k + 1 : ℕ) : ℝ) + 1 / 2 = ((k : ℝ) + 1 / 2) + 1 := by push_cast; ring
    rw [heq, Real.Gamma_add_one hne, ih]
    have hfac : ((2 * (k + 1))! : ℝ) = (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) * ((2 * k)! : ℝ) := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    have hfac_k : ((k + 1)! : ℝ) = ((k : ℝ) + 1) * ((k)! : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfac, hfac_k, pow_succ]
    have hk_ne : ((k)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    field_simp
    ring

/-- Stirling upper bound for half-integers: `Γ(k + 1/2) ≤ √(2π) k^k e^{-k}` for all `k ≥ 1`. -/
theorem gamma_add_half_le {k : ℕ} (hk : 1 ≤ k) :
    Real.Gamma ((k : ℝ) + 1 / 2) ≤ √(2 * π) * (k : ℝ) ^ k * Real.exp (-(k : ℝ)) := by
  rw [gamma_add_half_eq_factorial]
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hst_k : ((k)! : ℝ) =
      Stirling.stirlingSeq k * (√(2 * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k) := by
    have hden : √(2 * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k ≠ 0 := by positivity
    rw [Stirling.stirlingSeq, div_mul_cancel₀ _ hden]
  have hst_2k : ((2 * k)! : ℝ) =
      Stirling.stirlingSeq (2 * k) * (√(2 * ((2 * k : ℕ) : ℝ)) * (((2 * k : ℕ) : ℝ) / Real.exp 1) ^ (2 * k)) := by
    have hden : √(2 * ((2 * k : ℕ) : ℝ)) * (((2 * k : ℕ) : ℝ) / Real.exp 1) ^ (2 * k) ≠ 0 := by
      positivity
    rw [Stirling.stirlingSeq, div_mul_cancel₀ _ hden]
  have hst_mono : Stirling.stirlingSeq (2 * k) ≤ Stirling.stirlingSeq k := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hm : m ≤ 2 * m + 1 := by omega
    have := Stirling.stirlingSeq'_antitone hm
    simpa [Function.comp_apply, show 2 * (m + 1) = (2 * m + 1) + 1 by ring] using this
  have hst_k_pos : 0 < Stirling.stirlingSeq k := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact Stirling.stirlingSeq'_pos m
  have h_ratio_eq : ((2 * k)! : ℝ) / ((4 : ℝ) ^ k * ((k)! : ℝ)) * √π =
      (Stirling.stirlingSeq (2 * k) / Stirling.stirlingSeq k) *
        (√(2 * π) * (k : ℝ) ^ k * Real.exp (-(k : ℝ))) := by
    rw [hst_2k, hst_k]
    have hsqrt_rel : √(2 * ((2 * k : ℕ) : ℝ)) / √(2 * (k : ℝ)) = √2 := by
      have : (2 * ((2 * k : ℕ) : ℝ)) = 2 * (2 * (k : ℝ)) := by push_cast; ring
      rw [this, Real.sqrt_mul zero_le_two, mul_div_cancel_right₀ _ (Real.sqrt_ne_zero'.mpr (by positivity))]
    have hexp_k : (Real.exp 1) ^ k = Real.exp (k : ℝ) := by
      rw [← Real.exp_nat_mul, mul_one]
    have hexp_2k : (Real.exp 1) ^ (2 * k) = Real.exp (2 * (k : ℝ)) := by
      rw [← Real.exp_nat_mul, mul_one]; push_cast; rfl
    have hexp_neg : Real.exp (-(k : ℝ)) = (Real.exp (k : ℝ))⁻¹ := Real.exp_neg _
    have hexp_2k_sq : Real.exp (2 * (k : ℝ)) = Real.exp (k : ℝ) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1
    have hk_pow : (k : ℝ) ^ (2 * k) = (k : ℝ) ^ k * (k : ℝ) ^ k := by
      rw [two_mul, pow_add]
    have h4_eq : (4 : ℝ) ^ k = (2 : ℝ) ^ (2 * k) := by
      rw [pow_mul]; norm_num
    have hsqrt_2pi : √(2 * π) = √2 * √π := Real.sqrt_mul zero_le_two π
    push_cast
    rw [div_pow, div_pow, mul_pow, hexp_k, hexp_2k, hexp_2k_sq, hk_pow, h4_eq, hexp_neg, hsqrt_2pi]
    have hsqrt_2k_eq : √(2 * (2 * (k : ℝ))) = √2 * √(2 * (k : ℝ)) :=
      Real.sqrt_mul zero_le_two (2 * (k : ℝ))
    rw [hsqrt_2k_eq]
    have hnz1 : √(2 * (k : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have hnz2 : Real.exp (k : ℝ) ≠ 0 := (Real.exp_pos _).ne'
    have hnz3 : (k : ℝ) ^ k ≠ 0 := pow_ne_zero _ hk_pos.ne'
    have hnz4 : (2 : ℝ) ^ (2 * k) ≠ 0 := by positivity
    have hnz5 : Stirling.stirlingSeq k ≠ 0 := hst_k_pos.ne'
    field_simp
  rw [h_ratio_eq]
  calc (Stirling.stirlingSeq (2 * k) / Stirling.stirlingSeq k) *
        (√(2 * π) * (k : ℝ) ^ k * Real.exp (-(k : ℝ)))
      ≤ 1 * (√(2 * π) * (k : ℝ) ^ k * Real.exp (-(k : ℝ))) := by
        gcongr
        exact (div_le_one hst_k_pos).mpr hst_mono
    _ = √(2 * π) * (k : ℝ) ^ k * Real.exp (-(k : ℝ)) := one_mul _

/-- Combined Stirling-arc bound `(TE.7)`:
`2 ^ (k + 1) * Γ(k + 1/2) * (π / (4 * ℓ * a)) ^ (k + 1/2) ≤ 4 * exp(-k)` for `k ≥ 1`, `ℓ * a ≥ (π / 2) * k`. -/
theorem teb_stirling_bound {k : ℕ} {ℓ a : ℝ} (hk : 1 ≤ k) (hℓ : 0 < ℓ) (ha : 0 < a)
    (hla : (π / 2) * (k : ℝ) ≤ ℓ * a) :
    (2 : ℝ) ^ (k + 1) * Real.Gamma ((k : ℝ) + 1 / 2) * (π / (4 * ℓ * a)) ^ ((k : ℝ) + 1 / 2) ≤
      4 * Real.exp (-(k : ℝ)) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have h_arg_le : π / (4 * ℓ * a) ≤ 1 / (2 * (k : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hpow_le : (π / (4 * ℓ * a)) ^ ((k : ℝ) + 1 / 2) ≤ (1 / (2 * (k : ℝ))) ^ ((k : ℝ) + 1 / 2) :=
    Real.rpow_le_rpow (by positivity) h_arg_le (by positivity)
  have hgam := gamma_add_half_le hk
  have hgam_nn : 0 ≤ Real.Gamma ((k : ℝ) + 1 / 2) := (Real.Gamma_pos_of_pos (by positivity)).le
  have h_id : (2 : ℝ) ^ (k + 1) * (√(2 * π) * (k : ℝ) ^ k * Real.exp (-(k : ℝ))) *
      (1 / (2 * (k : ℝ))) ^ ((k : ℝ) + 1 / 2) =
      2 * √π / √(k : ℝ) * Real.exp (-(k : ℝ)) := by
    rw [Real.rpow_add (by positivity : 0 < 1 / (2 * (k : ℝ))), Real.rpow_natCast,
      one_div_pow, mul_pow, one_div (2 * (k : ℝ)), Real.inv_rpow (by positivity),
      ← Real.sqrt_eq_rpow]
    simp_rw [Real.sqrt_mul zero_le_two]
    have hk_pow_ne : (k : ℝ) ^ k ≠ 0 := pow_ne_zero _ hk_pos.ne'
    have hk_sqrt_ne : √(k : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hk_pos).ne'
    have h2_pow_ne : (2 : ℝ) ^ k ≠ 0 := by positivity
    have h2_sqrt_sq : √2 * √2 = 2 := Real.mul_self_sqrt zero_le_two
    rw [pow_succ]
    field_simp
  have hsqrt_k_ge : 1 ≤ √(k : ℝ) := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hk)
  have h2sqrt_pi_le : 2 * √π ≤ 4 := by
    have : √π ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      nlinarith [Real.pi_lt_four]
    linarith
  calc (2 : ℝ) ^ (k + 1) * Real.Gamma ((k : ℝ) + 1 / 2) * (π / (4 * ℓ * a)) ^ ((k : ℝ) + 1 / 2)
      ≤ (2 : ℝ) ^ (k + 1) * (√(2 * π) * (k : ℝ) ^ k * Real.exp (-(k : ℝ))) *
          (1 / (2 * (k : ℝ))) ^ ((k : ℝ) + 1 / 2) := by
        gcongr
    _ = 2 * √π / √(k : ℝ) * Real.exp (-(k : ℝ)) := h_id
    _ ≤ 4 / 1 * Real.exp (-(k : ℝ)) := by gcongr
    _ = 4 * Real.exp (-(k : ℝ)) := by ring

end StirlingHalfInt

/-! ### Part 3: Theorem TE.2 Fixed-Point Closures -/

section FixedPointClosures

/-- Explicit logarithmic fixed-point bound `L♯(C_*) = 2 C_* log(2 C_*)`. -/
noncomputable def tebLogSharp (Cstar : ℝ) : ℝ :=
  2 * Cstar * Real.log (2 * Cstar)

lemma one_le_tebLogSharp {Cstar : ℝ} (hC : 1 ≤ Cstar) : 1 ≤ tebLogSharp Cstar := by
  unfold tebLogSharp
  have h2 : (2 : ℝ) ≤ 2 * Cstar := by linarith
  have hlog : 1 / 2 ≤ Real.log (2 * Cstar) := by
    have h1 : Real.log 2 ≤ Real.log (2 * Cstar) := Real.log_le_log (by norm_num) h2
    have h2' : 1 / 2 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
    linarith
  nlinarith

/-- Theorem TE.2(2) logarithmic bootstrap closure:
if `1 ≤ Cstar`, `1 ≤ L`, and `L ≤ Cstar * (1 + log L)`, then `L ≤ tebLogSharp Cstar`. -/
theorem log_bootstrap_bound {Cstar L : ℝ} (hC : 1 ≤ Cstar) (hL : 1 ≤ L)
    (hle : L ≤ Cstar * (1 + Real.log L)) :
    L ≤ tebLogSharp Cstar := by
  unfold tebLogSharp
  have hC_pos : 0 < Cstar := by linarith
  have hL_pos : 0 < L := by linarith
  have h2C_pos : 0 < 2 * Cstar := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos hL_pos h2C_pos)
  rw [Real.log_div hL_pos.ne' h2C_pos.ne'] at hlog
  have hlogL : Real.log L ≤ Real.log (2 * Cstar) + L / (2 * Cstar) - 1 := by linarith
  have h1 : L ≤ Cstar * (1 + (Real.log (2 * Cstar) + L / (2 * Cstar) - 1)) :=
    hle.trans (mul_le_mul_of_nonneg_left (by linarith) hC_pos.le)
  have h2 : Cstar * (1 + (Real.log (2 * Cstar) + L / (2 * Cstar) - 1)) =
      Cstar * Real.log (2 * Cstar) + L / 2 := by
    field_simp [hC_pos.ne']
    ring
  linarith

/-- General real-exponent polynomial absorption bound:
if `A > 0`, `L♯ ≥ 0`, `r ≥ 0`, `K > 0`, and `K ≤ A * (1 + L♯ * K ^ (-r))`, then
`K ≤ max (2 * A) ((2 * A * L♯) ^ (1 / (r + 1)))`. -/
theorem poly_absorption_bound_rpow {A Lsharp K r : ℝ} (hA : 0 < A) (hL : 0 ≤ Lsharp)
    (hr : 0 ≤ r) (hK : 0 < K) (hle : K ≤ A * (1 + Lsharp * K ^ (-r))) :
    K ≤ max (2 * A) ((2 * A * Lsharp) ^ (1 / (r + 1))) := by
  have _ := hL
  have hKr_pos : 0 < K ^ r := Real.rpow_pos_of_pos hK r
  have hmul : K ^ (r + 1) ≤ A * (K ^ r + Lsharp) := by
    calc K ^ (r + 1) = K * K ^ r := by rw [Real.rpow_add hK, Real.rpow_one, mul_comm]
      _ ≤ A * (1 + Lsharp * K ^ (-r)) * K ^ r := mul_le_mul_of_nonneg_right hle hKr_pos.le
      _ = A * (K ^ r + Lsharp * (K ^ (-r) * K ^ r)) := by ring
      _ = A * (K ^ r + Lsharp) := by
          rw [← Real.rpow_add hK, neg_add_cancel, Real.rpow_zero, mul_one]
  rcases le_or_gt Lsharp (K ^ r) with hbr | hbr
  · have h2 : K * K ^ r ≤ (2 * A) * K ^ r := by
      have : K ^ (r + 1) = K * K ^ r := by rw [Real.rpow_add hK, Real.rpow_one, mul_comm]
      linarith [mul_le_mul_of_nonneg_left (add_le_add_left hbr (K ^ r)) hA.le]
    exact le_trans (le_of_mul_le_mul_right h2 hKr_pos) (le_max_left _ _)
  · have h2 : K ^ (r + 1) ≤ 2 * A * Lsharp := by
      have : A * (K ^ r + Lsharp) ≤ A * (Lsharp + Lsharp) := by nlinarith
      linarith
    have hr1_pos : 0 < r + 1 := by linarith
    have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hK.le _) h2 (by positivity : 0 ≤ 1 / (r + 1))
    rw [← Real.rpow_mul hK.le, mul_one_div_cancel hr1_pos.ne', Real.rpow_one] at hpow
    exact hpow.trans (le_max_right _ _)

/-- Theorem TE.2(3) polynomial absorption bound:
if `A > 0`, `L♯ ≥ 0`, `K > 0`, and `K ≤ A * (1 + L♯ * K ^ (-(k₀ + 1/2)))`, then
`K ≤ max 1 (max (2 * A) ((2 * A * L♯) ^ (1 / (k₀ + 3/2))))`. -/
theorem poly_absorption_bound {A Lsharp K : ℝ} (k₀ : ℕ) (hA : 0 < A) (hL : 0 ≤ Lsharp)
    (hK : 0 < K) (hle : K ≤ A * (1 + Lsharp * K ^ (-((k₀ : ℝ) + 1 / 2)))) :
    K ≤ max 1 (max (2 * A) ((2 * A * Lsharp) ^ (1 / ((k₀ : ℝ) + 3 / 2)))) := by
  have h := poly_absorption_bound_rpow (r := (k₀ : ℝ) + 1 / 2) hA hL (by positivity) hK hle
  have heq : (k₀ : ℝ) + 1 / 2 + 1 = (k₀ : ℝ) + 3 / 2 := by ring
  rw [heq] at h
  exact h.trans (le_max_right _ _)

end FixedPointClosures


/-! ### Axiom Verification -/

/-- info: 'FormalResearch.CFT.stripPoissonP_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CFT.stripPoissonP_integral

/-- info: 'FormalResearch.CFT.stripPoissonP1_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CFT.stripPoissonP1_integral

/-- info: 'FormalResearch.CFT.stripPoissonP_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CFT.stripPoissonP_le

/-- info: 'FormalResearch.CFT.abs_deriv_stripPoissonP_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CFT.abs_deriv_stripPoissonP_le

/-- info: 'FormalResearch.CFT.stripPoissonP1_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CFT.stripPoissonP1_le

/-- info: 'FormalResearch.CFT.abs_deriv_stripPoissonP1_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CFT.abs_deriv_stripPoissonP1_le

/-- info: 'FormalResearch.CFT.eVariationOn_stripPoissonQ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CFT.eVariationOn_stripPoissonQ_le

/-- info: 'FormalResearch.CFT.stripPoissonQ_tv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CFT.stripPoissonQ_tv_le

/-- info: 'FormalResearch.CFT.stripPoissonCalQ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CFT.stripPoissonCalQ_le

/-- info: 'FormalResearch.CFT.integral_abs_deriv_stripPoissonQ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CFT.integral_abs_deriv_stripPoissonQ_le

/-- info: 'FormalResearch.CFT.stripPoissonCalQ_le_of_two_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CFT.stripPoissonCalQ_le_of_two_mul_le

/-- info: 'FormalResearch.CFT.abs_deriv_stripPoissonQ_le_of_two_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CFT.abs_deriv_stripPoissonQ_le_of_two_mul_le

/-- info: 'FormalResearch.CFT.integral_abs_deriv_stripPoissonQ_block_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CFT.integral_abs_deriv_stripPoissonQ_block_le

/-- info: 'FormalResearch.CFT.gamma_add_half_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CFT.gamma_add_half_le

/-- info: 'FormalResearch.CFT.teb_stirling_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CFT.teb_stirling_bound

/-- info: 'FormalResearch.CFT.log_bootstrap_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CFT.log_bootstrap_bound

/-- info: 'FormalResearch.CFT.poly_absorption_bound_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CFT.poly_absorption_bound_rpow

/-- info: 'FormalResearch.CFT.poly_absorption_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CFT.poly_absorption_bound

end FormalResearch.CFT
