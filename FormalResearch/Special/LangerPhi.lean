module

public import Mathlib

/-!
# The Langer function `Φ(z) = arcosh(1+z)²` (`-arccos(1+z)²` for `z < 0`)

`Φ` is the compositional inverse of the entire function `langerP w = ∑_{n ≥ 1} wⁿ/(2n)! = cosh √w - 1`
(`= cos √(-w) - 1` for `w < 0`), whence

* `analyticAt_langerPhi`: `Φ` is real-analytic at the turning point `0` (so `u ↦ Φ(u-1)` is as smooth as `u`
  at a point where `u = 1`); proof: `langerP` is analytic (power series `FormalMultilinearSeries.ofScalars`
  with infinite radius) with derivative `1/2 ≠ 0`, `Φ ∘ langerP = id` near `0` (`langerPhi_langerP`), and
  Mathlib's `analyticAt_comp_iff_of_deriv_ne_zero`;
* `cosh_sqrt_langerPhi`, `cos_sqrt_neg_langerPhi`: `cosh √Φ(z) = 1 + z` (`z ≥ 0`), `cos √(-Φ(z)) = 1 + z`
  (`-2 ≤ z < 0`) (the eikonal relation `cosh η = u`); `langerP_langerPhi`: `langerP (Φ z) = z`, `z ≥ -2`;
* `deriv_langerPhi_zero`, `deriv2_langerPhi_zero`, `deriv3_langerPhi_zero`: `Φ'(0) = 2`, `Φ''(0) = -2/3`,
  `Φ'''(0) = 8/15`, i.e. the Taylor series `2z - z²/3 + 4z³/45 - …` (P3 appendices after
  `eq:general-airy-varpi-local`), obtained by differentiating `langerP (Φ z) = z` three times from the
  Taylor coefficients `langerP'(0) = 1/2`, `langerP''(0) = 1/12`, `langerP'''(0) = 1/120` of `langerP`
  (`iteratedDeriv_langerCosh_zero`).  The fourth coefficient `-1/35` was only checked numerically/with
  `sympy` and is not formalised.
-/

@[expose] public section

open Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- The entire function `w ↦ ∑_{n ≥ 0} wⁿ/(2n)!`, equal to `cosh √w` for `w ≥ 0` and to `cos √(-w)` for
`w ≤ 0`. -/
noncomputable def langerCosh (w : ℝ) : ℝ := ∑' n : ℕ, w ^ n / ((2 * n).factorial : ℝ)

/-- `langerP w = cosh √w - 1` (`w ≥ 0`), `cos √(-w) - 1` (`w ≤ 0`): the entire inverse of `langerPhi`. -/
noncomputable def langerP (w : ℝ) : ℝ := langerCosh w - 1

lemma langerCosh_nonneg {w : ℝ} (hw : 0 ≤ w) : langerCosh w = Real.cosh (√w) := by
  have h := Real.hasSum_cosh (√w)
  have : (fun n : ℕ => (√w) ^ (2 * n) / ((2 * n).factorial : ℝ)) =
      fun n : ℕ => w ^ n / ((2 * n).factorial : ℝ) := by
    funext n
    rw [pow_mul, Real.sq_sqrt hw]
  rw [this] at h
  exact h.tsum_eq

lemma langerCosh_nonpos {w : ℝ} (hw : w ≤ 0) : langerCosh w = Real.cos (√(-w)) := by
  have h := Real.hasSum_cos (√(-w))
  have : (fun n : ℕ => (-1) ^ n * (√(-w)) ^ (2 * n) / ((2 * n).factorial : ℝ)) =
      fun n : ℕ => w ^ n / ((2 * n).factorial : ℝ) := by
    funext n
    rw [pow_mul, Real.sq_sqrt (by linarith)]
    rw [← mul_pow, neg_one_mul, neg_neg]
  rw [this] at h
  exact h.tsum_eq


open FormalMultilinearSeries in
lemma langerCosh_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall langerCosh
      (ofScalars ℝ (fun n : ℕ => (1 : ℝ) / ((2 * n).factorial : ℝ))) 0 ⊤ := by
  set c : ℕ → ℝ := fun n => (1 : ℝ) / ((2 * n).factorial : ℝ) with hc
  have hrad : (ofScalars ℝ c).radius = ⊤ := by
    refine radius_eq_top_of_summable_norm _ fun r => ?_
    have h := (Real.hasSum_cosh (√(r : ℝ))).summable
    refine h.congr fun n => ?_
    rw [ofScalars_norm, hc, pow_mul, Real.sq_sqrt (NNReal.coe_nonneg r)]
    simp only [norm_div, norm_one, Real.norm_natCast]
    ring
  have h := (ofScalars ℝ c).hasFPowerSeriesOnBall (by rw [hrad]; exact ENNReal.zero_lt_top)
  rw [hrad] at h
  convert h using 1
  funext w
  have := ofScalars_sum_eq (E := ℝ) c w
  simp only [ofScalarsSum] at this
  rw [this, langerCosh]
  refine tsum_congr fun n => ?_
  simp [hc, div_eq_inv_mul]


lemma analyticAt_langerCosh (w : ℝ) : AnalyticAt ℝ langerCosh w :=
  langerCosh_hasFPowerSeriesOnBall.analyticOnNhd w (by simp)

lemma analyticAt_langerP (w : ℝ) : AnalyticAt ℝ langerP w :=
  (analyticAt_langerCosh w).sub analyticAt_const

lemma langerP_zero : langerP 0 = 0 := by
  have h := langerCosh_nonneg (le_refl (0 : ℝ))
  simp [langerP, h]

open FormalMultilinearSeries in
/-- Taylor coefficients of `langerCosh`: `iteratedDeriv n langerCosh 0 = n!/(2n)!`. -/
lemma iteratedDeriv_langerCosh_zero (n : ℕ) :
    iteratedDeriv n langerCosh 0 = (n.factorial : ℝ) / ((2 * n).factorial : ℝ) := by
  have h := langerCosh_hasFPowerSeriesOnBall.factorial_smul (y := (1 : ℝ)) n
  rw [← iteratedDeriv_eq_iteratedFDeriv] at h
  rw [← h]
  simp [ofScalars, div_eq_mul_inv]

lemma deriv_langerP : deriv langerP = deriv langerCosh := by
  funext x
  show deriv (fun w => langerCosh w - 1) x = _
  exact deriv_sub_const _

lemma deriv_langerP_zero : deriv langerP 0 = 1 / 2 := by
  have h := iteratedDeriv_langerCosh_zero 1
  simp only [iteratedDeriv_one] at h
  rw [deriv_langerP, h]; norm_num [Nat.factorial]

lemma deriv2_langerP_zero : deriv (deriv langerP) 0 = 1 / 12 := by
  have h := iteratedDeriv_langerCosh_zero 2
  rw [iteratedDeriv_succ, iteratedDeriv_one] at h
  rw [deriv_langerP, h]; norm_num [Nat.factorial]

lemma deriv3_langerP_zero : deriv (deriv (deriv langerP)) 0 = 1 / 120 := by
  have h := iteratedDeriv_langerCosh_zero 3
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one] at h
  rw [deriv_langerP, h]; norm_num [Nat.factorial]

/-- The Langer function `Φ(z) = arcosh(1+z)²` for `z ≥ 0` and `-arccos(1+z)²` for `z < 0`
(the junk values for `z < -2` are irrelevant), so that `cosh √Φ(z) = 1 + z` (`z ≥ 0`) and
`cos √(-Φ(z)) = 1 + z` (`-2 ≤ z ≤ 0`). -/
noncomputable def langerPhi (z : ℝ) : ℝ :=
  if 0 ≤ z then (Real.arcosh (1 + z)) ^ 2 else -(Real.arccos (1 + z)) ^ 2

lemma langerPhi_of_nonneg {z : ℝ} (hz : 0 ≤ z) : langerPhi z = (Real.arcosh (1 + z)) ^ 2 := by
  simp [langerPhi, hz]

lemma langerPhi_zero : langerPhi 0 = 0 := by
  rw [langerPhi_of_nonneg (le_refl _)]; simp [Real.arcosh_zero]

lemma langerPhi_of_neg {z : ℝ} (hz : z < 0) : langerPhi z = -(Real.arccos (1 + z)) ^ 2 := by
  simp [langerPhi, not_le.2 hz]

/-- `cosh √Φ(z) = 1 + z` on the right branch. -/
lemma cosh_sqrt_langerPhi {z : ℝ} (hz : 0 ≤ z) : Real.cosh (√(langerPhi z)) = 1 + z := by
  rw [langerPhi_of_nonneg hz, Real.sqrt_sq (Real.arcosh_nonneg (by linarith))]
  exact Real.cosh_arcosh (by linarith)

/-- `cos √(-Φ(z)) = 1 + z` on the left branch `-2 ≤ z ≤ 0`. -/
lemma cos_sqrt_neg_langerPhi {z : ℝ} (hz : z < 0) (hz2 : -2 ≤ z) :
    Real.cos (√(-langerPhi z)) = 1 + z := by
  rw [langerPhi_of_neg hz, neg_neg, Real.sqrt_sq (Real.arccos_nonneg _)]
  exact Real.cos_arccos (by linarith) (by linarith)

lemma langerP_langerPhi {z : ℝ} (hz : -2 ≤ z) : langerP (langerPhi z) = z := by
  rcases le_or_gt 0 z with h | h
  · have h0 : 0 ≤ langerPhi z := by rw [langerPhi_of_nonneg h]; positivity
    rw [langerP, langerCosh_nonneg h0, cosh_sqrt_langerPhi h]; ring
  · have h0 : langerPhi z ≤ 0 := by rw [langerPhi_of_neg h]; nlinarith [sq_nonneg (Real.arccos (1 + z))]
    rw [langerP, langerCosh_nonpos h0, cos_sqrt_neg_langerPhi h hz]; ring

lemma langerPhi_langerP {w : ℝ} (hw : |w| < π ^ 2) : langerPhi (langerP w) = w := by
  rcases le_or_gt 0 w with h | h
  · have h0 : 0 ≤ langerP w := by
      rw [langerP, langerCosh_nonneg h]
      linarith [Real.one_le_cosh (√w)]
    rw [langerPhi_of_nonneg h0, langerP, langerCosh_nonneg h]
    have : (1 : ℝ) + (Real.cosh (√w) - 1) = Real.cosh (√w) := by ring
    rw [this, Real.arcosh_cosh (Real.sqrt_nonneg _), Real.sq_sqrt h]
  · have hw' : -w < π ^ 2 := by rw [abs_of_neg h] at hw; exact hw
    set s := √(-w) with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
    have hsπ : s ≤ π := by
      rw [hs]; apply Real.sqrt_le_iff.2; exact ⟨Real.pi_pos.le, hw'.le⟩
    have hss : s ^ 2 = -w := Real.sq_sqrt (by linarith)
    have hlt : Real.cos s < 1 := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) hsπ hs0
      simpa using this
    have h1 : langerP w = Real.cos s - 1 := by rw [langerP, langerCosh_nonpos h.le]
    have h0 : langerP w < 0 := by rw [h1]; linarith
    rw [langerPhi_of_neg h0, h1]
    have : (1 : ℝ) + (Real.cos s - 1) = Real.cos s := by ring
    rw [this, Real.arccos_cos hs0.le hsπ, hss]; ring

/-- **`Φ` is analytic at the turning point `0`.** -/
theorem analyticAt_langerPhi : AnalyticAt ℝ langerPhi 0 := by
  have hf := analyticAt_langerP 0
  have hd : deriv langerP 0 ≠ 0 := by rw [deriv_langerP_zero]; norm_num
  have hcomp : AnalyticAt ℝ (langerPhi ∘ langerP) 0 := by
    refine analyticAt_id.congr ?_
    have : ∀ᶠ w in 𝓝 (0 : ℝ), |w| < π ^ 2 := by
      have : (0 : ℝ) < π ^ 2 := by positivity
      exact (isOpen_lt continuous_abs continuous_const).mem_nhds (by simpa using this)
    filter_upwards [this] with w hw
    exact (langerPhi_langerP hw).symm
  have := (analyticAt_comp_iff_of_deriv_ne_zero hf hd).1 hcomp
  rwa [langerP_zero] at this


private lemma hasDerivAt_comp_an {g φ : ℝ → ℝ} {z : ℝ} (hg : AnalyticAt ℝ g (φ z))
    (hφ : AnalyticAt ℝ φ z) :
    HasDerivAt (fun x => g (φ x)) (deriv g (φ z) * deriv φ z) z :=
  HasDerivAt.comp z hg.differentiableAt.hasDerivAt hφ.differentiableAt.hasDerivAt

lemma langerPhi_eventually_analytic : ∀ᶠ z in 𝓝 (0 : ℝ), AnalyticAt ℝ langerPhi z :=
  analyticAt_langerPhi.eventually_analyticAt

private lemma langerP_comp_eventually (z : ℝ) (hz : -2 < z) :
    (fun x => langerP (langerPhi x)) =ᶠ[𝓝 z] id := by
  filter_upwards [Ioi_mem_nhds hz] with x hx
  exact langerP_langerPhi (le_of_lt hx)

private lemma langerPhi_E1 : ∀ᶠ z in 𝓝 (0 : ℝ),
    deriv langerP (langerPhi z) * deriv langerPhi z = 1 := by
  filter_upwards [langerPhi_eventually_analytic, Ioi_mem_nhds (show (-2 : ℝ) < 0 by norm_num)]
    with z hz hz2
  have h := hasDerivAt_comp_an (analyticAt_langerP (langerPhi z)) hz
  have h' := h.congr_of_eventuallyEq (langerP_comp_eventually z hz2).symm
  exact (hasDerivAt_id z).unique h' |>.symm

private lemma langerPhi_E2 : ∀ᶠ z in 𝓝 (0 : ℝ),
    deriv (deriv langerP) (langerPhi z) * deriv langerPhi z ^ 2
      + deriv langerP (langerPhi z) * deriv (deriv langerPhi) z = 0 := by
  filter_upwards [langerPhi_E1.eventually_nhds, langerPhi_eventually_analytic] with z hz hza
  have hφ' : AnalyticAt ℝ (deriv langerPhi) z := hza.deriv
  have h1 := hasDerivAt_comp_an (g := deriv langerP) (analyticAt_langerP (langerPhi z)).deriv hza
  have h2 := h1.mul hφ'.differentiableAt.hasDerivAt
  have h3 : HasDerivAt (fun x => deriv langerP (langerPhi x) * deriv langerPhi x) 0 z :=
    (hasDerivAt_const z (1 : ℝ)).congr_of_eventuallyEq hz
  have := h2.unique h3
  rw [← this]; ring

lemma deriv_langerPhi_zero : deriv langerPhi 0 = 2 := by
  have h := langerPhi_E1.self_of_nhds
  rw [langerPhi_zero, deriv_langerP_zero] at h
  linarith

lemma deriv2_langerPhi_zero : deriv (deriv langerPhi) 0 = -2 / 3 := by
  have h := langerPhi_E2.self_of_nhds
  rw [langerPhi_zero, deriv_langerP_zero, deriv2_langerP_zero, deriv_langerPhi_zero] at h
  linarith

lemma deriv3_langerPhi_zero : deriv (deriv (deriv langerPhi)) 0 = 8 / 15 := by
  have hza := analyticAt_langerPhi
  have hφ' : AnalyticAt ℝ (deriv langerPhi) 0 := hza.deriv
  have hφ'' : AnalyticAt ℝ (deriv (deriv langerPhi)) 0 := hφ'.deriv
  have hE : ∀ᶠ z in 𝓝 (0 : ℝ), deriv (deriv langerP) (langerPhi z) * deriv langerPhi z ^ 2
      + deriv langerP (langerPhi z) * deriv (deriv langerPhi) z = 0 := langerPhi_E2
  have hP2 := hasDerivAt_comp_an (g := deriv (deriv langerP))
    (analyticAt_langerP (langerPhi 0)).deriv.deriv hza
  have hP1 := hasDerivAt_comp_an (g := deriv langerP) (analyticAt_langerP (langerPhi 0)).deriv hza
  have hsq := hφ'.differentiableAt.hasDerivAt.pow 2
  have h2 := hP2.mul hsq
  have h1 := hP1.mul hφ''.differentiableAt.hasDerivAt
  have h3 := h2.add h1
  have h4 : HasDerivAt (fun x => deriv (deriv langerP) (langerPhi x) * deriv langerPhi x ^ 2
      + deriv langerP (langerPhi x) * deriv (deriv langerPhi) x) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hE
  have := h3.unique h4
  rw [langerPhi_zero, deriv_langerP_zero, deriv2_langerP_zero, deriv3_langerP_zero,
    deriv_langerPhi_zero, deriv2_langerPhi_zero] at this
  simp only [Pi.pow_apply, deriv_langerPhi_zero] at this
  linarith

/-- info: 'FormalResearch.Special.analyticAt_langerPhi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.analyticAt_langerPhi

/-- info: 'FormalResearch.Special.deriv_langerPhi_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.deriv_langerPhi_zero

/-- info: 'FormalResearch.Special.deriv2_langerPhi_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.deriv2_langerPhi_zero

/-- info: 'FormalResearch.Special.deriv3_langerPhi_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.deriv3_langerPhi_zero

/-- info: 'FormalResearch.Special.cosh_sqrt_langerPhi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.cosh_sqrt_langerPhi

/-- info: 'FormalResearch.Special.cos_sqrt_neg_langerPhi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.cos_sqrt_neg_langerPhi

/-- info: 'FormalResearch.Special.langerP_langerPhi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.langerP_langerPhi

/-- info: 'FormalResearch.Special.langerPhi_langerP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.langerPhi_langerP

end FormalResearch.Special
