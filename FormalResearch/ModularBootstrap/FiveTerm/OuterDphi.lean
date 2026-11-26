module

public import FormalResearch.ModularBootstrap.FiveTerm.OuterX

/-!
# FIVE-S, S4a: the phase bounds `δφ_δ'`, `δφ_δ''` (`cts:smooth-env` (3), first bullet)

`δφ_δ(x) = -θ_out(y(x)) + ½(arctan((1-δ) y(x)) - arctan y(x))` and `y(x) = tanh(πτ(x)/4)`, so `δφ_δ = Φ_δ ∘ τ` with
`Φ_δ(τ) = -Θ(τ) + g_{1-δ}(τ)`, `g_a(τ) = ½(arctan(a tanh(πτ/4)) - arctan(tanh(πτ/4)))`.  Both `Θ'`, `Θ''` (S2) and
`g_a'`, `g_a''` (`0 ≤ a ≤ 1`) are `O(e^{-πτ/2})` on `τ ≥ 0`, and `chain_bounds` turns this into the `x`-bounds with
`r̃ = min(x - ξ_*, 1)` exactly as in `outerS2`.  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

/-! ### The chain rule `F = Φ ∘ τ` with exponential decay in `τ` -/

lemma chain_bounds {F Φ Φ1 Φ2 : ℝ → ℝ} {D : ℝ} (hD : 0 < D)
    (h1 : ∀ τ, HasDerivAt Φ (Φ1 τ) τ) (h2 : ∀ τ, HasDerivAt Φ1 (Φ2 τ) τ)
    (hb : ∀ τ : ℝ, 0 ≤ τ → |Φ1 τ| ≤ D * Real.exp (-((π / 2) * τ)) ∧ |Φ2 τ| ≤ D * Real.exp (-((π / 2) * τ)))
    (hF : ∀ x : ℝ, xiStar < x → F =ᶠ[𝓝 x] fun w => Φ (tauOfX w)) :
    ∀ x : ℝ, xiStar < x →
      |deriv F x| ≤ (3 * D * KA) * ((min (x - xiStar) 1) ^ (-(1 : ℝ) / 2) * Real.exp (-(π * x))) ∧
      |deriv (deriv F) x| ≤ (3 * D * (KA ^ 2 + KB)) * ((min (x - xiStar) 1) ^ (-(3 : ℝ) / 2) * Real.exp (-(π * x))) := by
  have hKA := KA_pos
  have hKB := KB_pos
  have hpi := Real.pi_pos
  have hth : ∀ y, xiStar < y → HasDerivAt (fun w => Φ (tauOfX w)) (Φ1 (tauOfX y) * tx y) y := fun y hy =>
    (h1 (tauOfX y)).scomp y (hasDerivAt_tauOfX hy) |>.congr_deriv (by simp [smul_eq_mul, mul_comm])
  have hFd : ∀ y, xiStar < y → deriv F y = Φ1 (tauOfX y) * tx y := fun y hy =>
    ((hF y hy).deriv_eq).trans (hth y hy).deriv
  have hFdd : ∀ y, xiStar < y →
      HasDerivAt (deriv F) (Φ2 (tauOfX y) * tx y ^ 2 + Φ1 (tauOfX y) * txx y) y := by
    intro y hy
    have hev' : ∀ᶠ w in 𝓝 y, xiStar < w := Ioi_mem_nhds hy
    have heq : deriv F =ᶠ[𝓝 y] fun w => Φ1 (tauOfX w) * tx w := hev'.mono fun w hw => hFd w hw
    refine HasDerivAt.congr_of_eventuallyEq ?_ heq
    have h3 : HasDerivAt (fun w => Φ1 (tauOfX w)) (Φ2 (tauOfX y) * tx y) y :=
      (h2 (tauOfX y)).scomp y (hasDerivAt_tauOfX hy) |>.congr_deriv (by simp [smul_eq_mul, mul_comm])
    exact (h3.mul (hasDerivAt_tx hy)).congr_deriv (by ring)
  intro x hx
  have hr0 : 0 < x - xiStar := sub_pos.mpr hx
  have hm : 0 < min (x - xiStar) 1 := lt_min hr0 one_pos
  have hm1 : min (x - xiStar) 1 ≤ 1 := min_le_right _ _
  have hτ0 := tauOfX_nonneg hx
  have hbb := hb _ hτ0
  have h2e := exp_tau_le hx
  have h3 := tx_le hx
  have h4 := tx_nonneg hx
  have h5 := abs_txx_le hx
  set m := min (x - xiStar) 1 with hmdef
  have hsm : 0 < √m := Real.sqrt_pos.mpr hm
  have hsm1 : √m ≤ 1 := by rw [Real.sqrt_le_one]; exact hm1
  have hE := Real.exp_pos (-(π * x))
  have hCe : D * Real.exp (-((π / 2) * tauOfX x)) ≤ D * (3 * Real.exp (-(π * x))) :=
    mul_le_mul_of_nonneg_left h2e hD.le
  constructor
  · rw [hFd x hx, rpow_neg_half _ hm, abs_mul, abs_of_nonneg h4]
    calc |Φ1 (tauOfX x)| * tx x ≤ (D * (3 * Real.exp (-(π * x)))) * (KA / √m) :=
          mul_le_mul (hbb.1.trans hCe) h3 h4 (by positivity)
      _ = _ := by ring
  · rw [(hFdd x hx).deriv, rpow_neg_three_half _ hm]
    have htx2 : tx x ^ 2 ≤ KA ^ 2 / (m * √m) := by
      have : tx x ^ 2 ≤ (KA / √m) ^ 2 := pow_le_pow_left₀ h4 h3 2
      refine this.trans ?_
      rw [div_pow, Real.sq_sqrt hm.le, div_le_div_iff₀ hm (by positivity)]
      have : 0 ≤ KA ^ 2 * m := by positivity
      nlinarith
    have hA : |Φ2 (tauOfX x) * tx x ^ 2| ≤ (D * (3 * Real.exp (-(π * x)))) * (KA ^ 2 / (m * √m)) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ tx x ^ 2)]
      exact mul_le_mul (hbb.2.trans hCe) htx2 (by positivity) (by positivity)
    have hB : |Φ1 (tauOfX x) * txx x| ≤ (D * (3 * Real.exp (-(π * x)))) * (KB / (m * √m)) := by
      rw [abs_mul]
      exact mul_le_mul (hbb.1.trans hCe) h5 (abs_nonneg _) (by positivity)
    refine ((abs_add_le _ _).trans (add_le_add hA hB)).trans (le_of_eq ?_)
    ring

/-! ### The arctan part `g_a` -/

noncomputable def tt (τ : ℝ) : ℝ := Real.tanh (π * τ / 4)
noncomputable def t1 (τ : ℝ) : ℝ := (π / 4) * (1 - tt τ ^ 2)
noncomputable def t2 (τ : ℝ) : ℝ := -(π / 2) * tt τ * t1 τ
noncomputable def dd (a τ : ℝ) : ℝ := 1 + (a * tt τ) ^ 2
noncomputable def ee (τ : ℝ) : ℝ := 1 + tt τ ^ 2

lemma dd_pos (a τ : ℝ) : 0 < dd a τ := by unfold dd; positivity
lemma ee_pos (τ : ℝ) : 0 < ee τ := by unfold ee; positivity

/-- `g_a(τ) = ½(arctan(a tanh(πτ/4)) - arctan(tanh(πτ/4)))`. -/
noncomputable def gfun (a τ : ℝ) : ℝ := (1 / 2) * (Real.arctan (a * tt τ) - Real.arctan (tt τ))
noncomputable def g1 (a τ : ℝ) : ℝ := (1 / 2) * (a * t1 τ / dd a τ - t1 τ / ee τ)
noncomputable def g2 (a τ : ℝ) : ℝ :=
  (1 / 2) * (a * t2 τ / dd a τ - 2 * a ^ 3 * tt τ * t1 τ ^ 2 / dd a τ ^ 2 - t2 τ / ee τ +
    2 * tt τ * t1 τ ^ 2 / ee τ ^ 2)

lemma hasDerivAt_tt (τ : ℝ) : HasDerivAt tt (t1 τ) τ := by
  have h := (hasDerivAt_tanh' (π * τ / 4)).comp τ (((hasDerivAt_id τ).const_mul π).div_const 4)
  refine HasDerivAt.congr_deriv (f := tt) h ?_
  unfold t1 tt; ring

lemma hasDerivAt_t1 (τ : ℝ) : HasDerivAt t1 (t2 τ) τ := by
  have h := ((hasDerivAt_tt τ).pow 2).const_sub 1 |>.const_mul (π / 4)
  refine h.congr_deriv ?_
  unfold t2; push_cast; ring

lemma hasDerivAt_dd (a τ : ℝ) : HasDerivAt (dd a) (2 * a ^ 2 * tt τ * t1 τ) τ := by
  have h := (((hasDerivAt_tt τ).const_mul a).pow 2).const_add 1
  refine h.congr_deriv ?_
  push_cast; ring

lemma hasDerivAt_ee (τ : ℝ) : HasDerivAt ee (2 * tt τ * t1 τ) τ := by
  have h := ((hasDerivAt_tt τ).pow 2).const_add 1
  refine h.congr_deriv ?_
  push_cast; ring

lemma hasDerivAt_gfun (a τ : ℝ) : HasDerivAt (gfun a) (g1 a τ) τ := by
  have h1 := (Real.hasDerivAt_arctan (a * tt τ)).comp τ ((hasDerivAt_tt τ).const_mul a)
  have h2 := (Real.hasDerivAt_arctan (tt τ)).comp τ (hasDerivAt_tt τ)
  refine HasDerivAt.congr_deriv (f := gfun a) (((h1.sub h2).const_mul (1 / 2))) ?_
  unfold g1 dd ee
  ring

lemma hasDerivAt_g1 (a τ : ℝ) : HasDerivAt (g1 a) (g2 a τ) τ := by
  have hd := dd_pos a τ
  have he := ee_pos τ
  have h1 : HasDerivAt (fun w => a * t1 w / dd a w)
      ((a * t2 τ * dd a τ - a * t1 τ * (2 * a ^ 2 * tt τ * t1 τ)) / dd a τ ^ 2) τ :=
    ((hasDerivAt_t1 τ).const_mul a).div (hasDerivAt_dd a τ) hd.ne'
  have h2 : HasDerivAt (fun w => t1 w / ee w)
      ((t2 τ * ee τ - t1 τ * (2 * tt τ * t1 τ)) / ee τ ^ 2) τ :=
    (hasDerivAt_t1 τ).div (hasDerivAt_ee τ) he.ne'
  refine ((h1.sub h2).const_mul (1 / 2)).congr_deriv ?_
  unfold g2
  field_simp
  ring

lemma tt_nonneg {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ tt τ := by
  unfold tt
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr (by positivity)) (Real.cosh_pos _).le

lemma tt_lt_one (τ : ℝ) : tt τ < 1 := Real.tanh_lt_one _

lemma t1_nonneg (τ : ℝ) : 0 ≤ t1 τ := by
  unfold t1
  have h : tt τ ^ 2 ≤ 1 := by
    have h1 := tt_lt_one τ
    have h2 : -1 < tt τ := Real.neg_one_lt_tanh _
    nlinarith
  have := Real.pi_pos
  nlinarith

lemma t1_le {τ : ℝ} (hτ : 0 ≤ τ) : t1 τ ≤ π * Real.exp (-((π / 2) * τ)) := by
  have hpi := Real.pi_pos
  have h1 : 1 - tt τ ^ 2 = 1 / Real.cosh (π * τ / 4) ^ 2 := one_sub_tanh_sq _
  have hc : Real.exp (π * τ / 4) / 2 ≤ Real.cosh (π * τ / 4) := by
    have := exp_div_two_le_cosh (π * τ / 4)
    rwa [abs_of_nonneg (by positivity)] at this
  have hcp : 0 < Real.exp (π * τ / 4) / 2 := by positivity
  have h2 : 1 / Real.cosh (π * τ / 4) ^ 2 ≤ 4 * Real.exp (-((π / 2) * τ)) := by
    have : (Real.exp (π * τ / 4) / 2) ^ 2 ≤ Real.cosh (π * τ / 4) ^ 2 := pow_le_pow_left₀ hcp.le hc 2
    have h3 : 1 / Real.cosh (π * τ / 4) ^ 2 ≤ 1 / (Real.exp (π * τ / 4) / 2) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) this
    refine h3.trans (le_of_eq ?_)
    rw [div_pow, ← Real.exp_nat_mul]
    rw [show (-((π / 2) * τ)) = -(↑(2 : ℕ) * (π * τ / 4)) by push_cast; ring, Real.exp_neg]
    field_simp
    norm_num
  unfold t1
  rw [h1]
  nlinarith

lemma abs_div_le_self {n d : ℝ} (hd : 1 ≤ d) : |n / d| ≤ |n| := by
  rw [abs_div, abs_of_pos (by linarith : 0 < d)]
  exact div_le_self (abs_nonneg _) hd

lemma one_le_dd {a : ℝ} (τ : ℝ) : 1 ≤ dd a τ := by unfold dd; nlinarith [sq_nonneg (a * tt τ)]
lemma one_le_ee (τ : ℝ) : 1 ≤ ee τ := by unfold ee; nlinarith [sq_nonneg (tt τ)]

/-- Uniform bounds for `g_a'`, `g_a''` on `τ ≥ 0`, `0 ≤ a ≤ 1`. -/
lemma g_bounds {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    |g1 a τ| ≤ (3 * π ^ 2) * Real.exp (-((π / 2) * τ)) ∧ |g2 a τ| ≤ (3 * π ^ 2) * Real.exp (-((π / 2) * τ)) := by
  have hpi := Real.pi_pos
  set E := Real.exp (-((π / 2) * τ)) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have ht0 := tt_nonneg hτ
  have ht1 := tt_lt_one τ
  have h10 := t1_nonneg τ
  have h1le := t1_le hτ
  rw [← hEdef] at h1le
  have hpi2 : π ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
  have hdd := one_le_dd (a := a) τ
  have hee := one_le_ee τ
  have ht2 : |t2 τ| ≤ (π / 2) * t1 τ := by
    unfold t2
    rw [show -(π / 2) * tt τ * t1 τ = -((π / 2) * tt τ * t1 τ) by ring, abs_neg,
      abs_of_nonneg (by positivity)]
    nlinarith [mul_nonneg (by positivity : 0 ≤ (π / 2)) h10]
  have ht1sq : t1 τ ^ 2 ≤ π ^ 2 * E := by
    have : t1 τ ^ 2 ≤ (π * E) ^ 2 := pow_le_pow_left₀ h10 h1le 2
    nlinarith [mul_nonneg (sq_nonneg π) (mul_nonneg hE0.le (sub_nonneg.mpr hE1))]
  have hbd1 : |a * t1 τ / dd a τ| ≤ t1 τ := by
    refine (abs_div_le_self hdd).trans ?_
    rw [abs_mul, abs_of_nonneg ha0, abs_of_nonneg h10]
    nlinarith
  have hbd2 : |t1 τ / ee τ| ≤ t1 τ := by
    refine (abs_div_le_self hee).trans ?_
    rw [abs_of_nonneg h10]
  constructor
  · unfold g1
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := abs_sub (a * t1 τ / dd a τ) (t1 τ / ee τ)
    nlinarith [mul_le_mul_of_nonneg_right hpi2 hE0.le]
  · unfold g2
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have b1 : |a * t2 τ / dd a τ| ≤ |t2 τ| := by
      refine (abs_div_le_self hdd).trans ?_
      rw [abs_mul, abs_of_nonneg ha0]
      nlinarith [abs_nonneg (t2 τ)]
    have b2 : |t2 τ / ee τ| ≤ |t2 τ| := abs_div_le_self hee
    have b3 : |2 * a ^ 3 * tt τ * t1 τ ^ 2 / dd a τ ^ 2| ≤ 2 * t1 τ ^ 2 := by
      refine (abs_div_le_self (by nlinarith)).trans ?_
      rw [abs_of_nonneg (by positivity)]
      have : a ^ 3 ≤ 1 := pow_le_one₀ ha0 ha1
      have h4 : a ^ 3 * tt τ ≤ 1 := by nlinarith [mul_nonneg (pow_nonneg ha0 3) ht0]
      nlinarith [sq_nonneg (t1 τ)]
    have b4 : |2 * tt τ * t1 τ ^ 2 / ee τ ^ 2| ≤ 2 * t1 τ ^ 2 := by
      refine (abs_div_le_self (by nlinarith)).trans ?_
      rw [abs_of_nonneg (by positivity)]
      nlinarith [sq_nonneg (t1 τ)]
    have s1 := abs_sub (a * t2 τ / dd a τ - 2 * a ^ 3 * tt τ * t1 τ ^ 2 / dd a τ ^ 2 - t2 τ / ee τ)
      (-(2 * tt τ * t1 τ ^ 2 / ee τ ^ 2))
    have s2 := abs_sub (a * t2 τ / dd a τ - 2 * a ^ 3 * tt τ * t1 τ ^ 2 / dd a τ ^ 2) (t2 τ / ee τ)
    have s3 := abs_sub (a * t2 τ / dd a τ) (2 * a ^ 3 * tt τ * t1 τ ^ 2 / dd a τ ^ 2)
    rw [abs_neg] at s1
    have e : a * t2 τ / dd a τ - 2 * a ^ 3 * tt τ * t1 τ ^ 2 / dd a τ ^ 2 - t2 τ / ee τ +
        2 * tt τ * t1 τ ^ 2 / ee τ ^ 2 =
        a * t2 τ / dd a τ - 2 * a ^ 3 * tt τ * t1 τ ^ 2 / dd a τ ^ 2 - t2 τ / ee τ -
          (-(2 * tt τ * t1 τ ^ 2 / ee τ ^ 2)) := by ring
    rw [e]
    nlinarith [sq_nonneg π, mul_nonneg hE0.le (sq_nonneg π)]


/-! ### `y(x) = tanh(πτ(x)/4)` and the bounds on `δφ_δ` -/

lemma yOfX_eq {x : ℝ} (hx : xiStar < x) : yOfX x = tt (tauOfX x) := by
  have hτ := tauOfX_nonneg hx
  have h0 := tt_nonneg hτ
  have hc := cosh_tauOfX_half hx
  have hs2 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : tt (tauOfX x) ^ 2 = (Real.cosh (π * x) - √2) / (Real.cosh (π * x) + √2) := by
    unfold tt
    set w : ℝ := π * tauOfX x / 4 with hw
    have h2w : Real.cosh (2 * w) = Real.cosh (π * x) / √2 := by
      rw [← hc]; congr 1; rw [hw]; ring
    have hcw : Real.cosh w ^ 2 = (Real.cosh (2 * w) + 1) / 2 := by
      rw [Real.cosh_two_mul]; nlinarith [Real.cosh_sq w]
    have hsw : Real.sinh w ^ 2 = (Real.cosh (2 * w) - 1) / 2 := by
      nlinarith [Real.cosh_sq w]
    rw [Real.tanh_eq_sinh_div_cosh, div_pow, hsw, hcw, h2w]
    have hpos : 0 < Real.cosh (π * x) + √2 := by have := Real.cosh_pos (π * x); linarith
    field_simp
  unfold yOfX
  rw [← hsq]
  exact Real.sqrt_sq h0

lemma dphi_eq {δ x : ℝ} (hx : xiStar < x) :
    dphi δ x = -thetaOutT (tauOfX x) + gfun (1 - δ) (tauOfX x) := by
  unfold dphi gfun thetaOutX
  rw [yOfX_eq hx]

/-- **`OuterS4a`** (`cts:smooth-env` (3), first bullet): the `δφ_δ'`, `δφ_δ''` bounds with `min(r,1)`.
Class: proved. -/
theorem outerS4a : OuterS4a := by
  obtain ⟨C, hCpos, Θ1, Θ2, hd1, hd2, hb, -, -, -⟩ := thetaOutT_data
  have hKA := KA_pos
  have hKB := KB_pos
  have hpi := Real.pi_pos
  set D := C + 3 * π ^ 2 with hD
  have hDpos : 0 < D := by positivity
  refine ⟨3 * D * (KA + KA ^ 2 + KB), by positivity, ?_⟩
  intro δ hδ0 hδ1 x hx
  have ha0 : 0 ≤ 1 - δ := by linarith
  have ha1 : 1 - δ ≤ 1 := by linarith
  have hb' := chain_bounds (F := dphi δ) (Φ := fun τ => -thetaOutT τ + gfun (1 - δ) τ)
    (Φ1 := fun τ => -Θ1 τ + g1 (1 - δ) τ) (Φ2 := fun τ => -Θ2 τ + g2 (1 - δ) τ) hDpos
    (fun τ => ((hd1 τ).neg.add (hasDerivAt_gfun (1 - δ) τ)))
    (fun τ => ((hd2 τ).neg.add (hasDerivAt_g1 (1 - δ) τ)))
    (fun τ hτ => by
      have h1 := hb τ hτ
      have h2 := g_bounds ha0 ha1 hτ
      constructor
      · calc |-Θ1 τ + g1 (1 - δ) τ| ≤ |-Θ1 τ| + |g1 (1 - δ) τ| := abs_add_le _ _
          _ ≤ _ := by rw [abs_neg]; linarith [h1.1, h2.1]
      · calc |-Θ2 τ + g2 (1 - δ) τ| ≤ |-Θ2 τ| + |g2 (1 - δ) τ| := abs_add_le _ _
          _ ≤ _ := by rw [abs_neg]; linarith [h1.2, h2.2])
    (fun y hy => by
      have hev : ∀ᶠ w in 𝓝 y, xiStar < w := Ioi_mem_nhds hy
      exact hev.mono fun w hw => dphi_eq hw) x hx
  have hr0 : 0 < x - xiStar := sub_pos.mpr hx
  have hm : 0 < min (x - xiStar) 1 := lt_min hr0 one_pos
  have hE := Real.exp_pos (-(π * x))
  have q1 : 0 ≤ (min (x - xiStar) 1) ^ (-(1 : ℝ) / 2) * Real.exp (-(π * x)) := by positivity
  have q3 : 0 ≤ (min (x - xiStar) 1) ^ (-(3 : ℝ) / 2) * Real.exp (-(π * x)) := by positivity
  have c1 : 3 * D * KA ≤ 3 * D * (KA + KA ^ 2 + KB) :=
    mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg KA]) (by positivity)
  have c2 : 3 * D * (KA ^ 2 + KB) ≤ 3 * D * (KA + KA ^ 2 + KB) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  constructor
  · calc |deriv (dphi δ) x| ≤ _ := hb'.1
      _ ≤ (3 * D * (KA + KA ^ 2 + KB)) * ((min (x - xiStar) 1) ^ (-(1 : ℝ) / 2) * Real.exp (-(π * x))) :=
          mul_le_mul_of_nonneg_right c1 q1
      _ = _ := by ring
  · calc |deriv (deriv (dphi δ)) x| ≤ _ := hb'.2
      _ ≤ (3 * D * (KA + KA ^ 2 + KB)) * ((min (x - xiStar) 1) ^ (-(3 : ℝ) / 2) * Real.exp (-(π * x))) :=
          mul_le_mul_of_nonneg_right c2 q3
      _ = _ := by ring

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.outerS4a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outerS4a

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
