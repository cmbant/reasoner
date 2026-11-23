module

public import FormalResearch.ModularBootstrap.Upper.Hankel.HankelDef

/-!
# The order-`p` Hankel function `H_p¹` on the upper half-plane (Laplace form)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, section `fw:s1` ("Exact order-raising on the
transform only"), kernel relation `fw:e1.2`; plan item A3 (`UPPER_PLAN.md`), order `p`.

`H_p¹(z) = (2/(π i)) e^{-iπp/2} K_p(-i z)` with `K_ν(w) = ∫₀^∞ e^{-w cosh s} cosh(ν s) ds` for `Re w > 0`,
i.e. `Im z > 0`.  The name `hankelP` is taken by the boundary piece of `HankelBoundary`, so the order-`p`
function is `hankelOrd p`.

## Main results
* `laplaceCosh`: Laplace integrals `∫₀^∞ e^{-w cosh s} g(s) ds` with exponentially bounded weights, their
  integrability (`integrableOn_laplace`), holomorphy (`hasDerivAt_laplaceCosh`) and the norm bound
  `‖·‖ ≤` real Laplace integral at any `ρ ≤ Re w` (`norm_laplaceCosh_le`);
* `besselKP ν`: `K_ν`, holomorphy, the three-term relation
  `K_{ν+1}(w) - K_{ν-1}(w) = (2ν/w) K_ν(w)` (`besselKP_add_one_sub`), `K_ν' = -(K_{ν+1} + K_{ν-1})/2`
  (`hasDerivAt_besselKP`) and `d/dw [w^{-p} K_p(w)] = -w^{-p} K_{p+1}(w)`
  (`hasDerivAt_besselKP_ratio`);
* `hankelOrd p`: `hankelOrd 0 = hankel0` (`hankelOrd_zero`), holomorphy (`differentiableOn_hankelOrd`),
  `d/dz [z^{-p} H_p(z)] = -z^{-p} H_{p+1}(z)` (`hasDerivAt_hankelOrd_ratio`), its `x`-form
  `∂_x [(b/x)^p H_p(K x b)] = -K b (b/x)^p H_{p+1}(K x b)` (`hasDerivAt_hankelOrd_scaled`), and the norm
  bound `‖H_p(z)‖ ≤ (2/π) ∫₀^∞ e^{-ρ cosh s} cosh(p s) ds` for `Im z ≥ ρ > 0` (`norm_hankelOrd_le`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.Upper.Hankel

/-! ### Elementary real bounds -/

lemma pow_mul_exp_neg_le (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) {y : ℝ} (hy : 0 ≤ y) :
    y ^ N * Real.exp (-(ρ / 2) * y) ≤ (N ! : ℝ) * (2 / ρ) ^ N := by
  have h := Real.pow_div_factorial_le_exp (ρ / 2 * y) (by positivity) N
  have hf : (0 : ℝ) < N ! := by positivity
  rw [div_le_iff₀ hf] at h
  have e : Real.exp (-(ρ / 2) * y) * Real.exp (ρ / 2 * y) = 1 := by
    rw [← Real.exp_add]; simp
  calc y ^ N * Real.exp (-(ρ / 2) * y)
      = ((2 / ρ) ^ N * (ρ / 2 * y) ^ N) * Real.exp (-(ρ / 2) * y) := by
        rw [← mul_pow]; field_simp
    _ ≤ ((2 / ρ) ^ N * (Real.exp (ρ / 2 * y) * N !)) * Real.exp (-(ρ / 2) * y) := by gcongr
    _ = (N ! : ℝ) * (2 / ρ) ^ N * (Real.exp (-(ρ / 2) * y) * Real.exp (ρ / 2 * y)) := by ring
    _ = _ := by rw [e, mul_one]

/-- Domination constant for `e^{N s} e^{-ρ cosh s} ≤ lapConst N ρ · e^{-s}`. -/
noncomputable def lapConst (N : ℕ) (ρ : ℝ) : ℝ := ((N + 1) ! : ℝ) * (2 / ρ) ^ (N + 1)

lemma lapConst_nonneg (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) : 0 ≤ lapConst N ρ := by
  unfold lapConst; positivity

lemma exp_nat_mul_exp_neg_cosh_le (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (s : ℝ) :
    Real.exp (N * s) * Real.exp (-(ρ * Real.cosh s)) ≤ lapConst N ρ * Real.exp (-s) := by
  have hc : Real.exp s / 2 ≤ Real.cosh s := by
    rw [Real.cosh_eq]; have := Real.exp_pos (-s); linarith
  have h1 : Real.exp (-(ρ * Real.cosh s)) ≤ Real.exp (-(ρ / 2) * Real.exp s) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hc hρ.le]
  have h2 := pow_mul_exp_neg_le (N + 1) hρ (Real.exp_pos s).le
  have e : Real.exp (N * s) = Real.exp s ^ (N + 1) * Real.exp (-s) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  calc Real.exp (N * s) * Real.exp (-(ρ * Real.cosh s))
      ≤ Real.exp (N * s) * Real.exp (-(ρ / 2) * Real.exp s) := by gcongr
    _ = (Real.exp s ^ (N + 1) * Real.exp (-(ρ / 2) * Real.exp s)) * Real.exp (-s) := by rw [e]; ring
    _ ≤ lapConst N ρ * Real.exp (-s) := by unfold lapConst; gcongr

lemma cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

lemma abs_sinh_le_exp_abs (x : ℝ) : |Real.sinh x| ≤ Real.exp |x| := by
  rw [Real.sinh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  have := Real.exp_pos x
  have := Real.exp_pos (-x)
  rw [abs_le]; constructor <;> linarith

/-! ### Laplace integrals against `e^{-w cosh s}` -/

/-- `∫₀^∞ e^{-w cosh s} g(s) ds`. -/
noncomputable def laplaceCosh (g : ℝ → ℝ) (w : ℂ) : ℂ :=
  ∫ s in Ioi (0 : ℝ), Complex.exp (-w * (Real.cosh s : ℂ)) * (g s : ℂ)

/-- `|g(s)| ≤ e^{N s}` for `s ≥ 0`. -/
def ExpBound (g : ℝ → ℝ) (N : ℕ) : Prop := ∀ s : ℝ, 0 ≤ s → |g s| ≤ Real.exp (N * s)

lemma ExpBound.mono {g : ℝ → ℝ} {N M : ℕ} (h : ExpBound g N) (hNM : N ≤ M) : ExpBound g M := by
  intro s hs
  refine (h s hs).trans (Real.exp_le_exp.mpr ?_)
  have : (N : ℝ) ≤ M := by exact_mod_cast hNM
  nlinarith

lemma ExpBound.cosh_mul {ν : ℝ} {N : ℕ} (hν : |ν| ≤ N) :
    ExpBound (fun s => Real.cosh (ν * s)) N := by
  intro s hs
  rw [abs_of_pos (Real.cosh_pos _)]
  refine (cosh_le_exp_abs _).trans (Real.exp_le_exp.mpr ?_)
  rw [abs_mul, abs_of_nonneg hs]
  nlinarith

lemma ExpBound.sinh_mul {ν : ℝ} {N : ℕ} (hν : |ν| ≤ N) :
    ExpBound (fun s => Real.sinh (ν * s)) N := by
  intro s hs
  refine (abs_sinh_le_exp_abs _).trans (Real.exp_le_exp.mpr ?_)
  rw [abs_mul, abs_of_nonneg hs]
  nlinarith

lemma ExpBound.cosh_mul_fun {g : ℝ → ℝ} {N : ℕ} (hg : ExpBound g N) :
    ExpBound (fun s => Real.cosh s * g s) (N + 1) := by
  intro s hs
  rw [abs_mul, abs_of_pos (Real.cosh_pos _)]
  have h1 : Real.cosh s ≤ Real.exp s := by
    rw [Real.cosh_eq]
    have : Real.exp (-s) ≤ Real.exp s := Real.exp_le_exp.mpr (by linarith)
    linarith
  calc Real.cosh s * |g s| ≤ Real.exp s * Real.exp (N * s) :=
        mul_le_mul h1 (hg s hs) (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (((N + 1 : ℕ) : ℝ) * s) := by rw [← Real.exp_add]; congr 1; push_cast; ring

lemma ExpBound.sinh_mul_fun {g : ℝ → ℝ} {N : ℕ} (hg : ExpBound g N) :
    ExpBound (fun s => Real.sinh s * g s) (N + 1) := by
  intro s hs
  rw [abs_mul]
  have h1 : |Real.sinh s| ≤ Real.exp s := by
    refine (abs_sinh_le_exp_abs s).trans (Real.exp_le_exp.mpr ?_)
    rw [abs_of_nonneg hs]
  calc |Real.sinh s| * |g s| ≤ Real.exp s * Real.exp (N * s) :=
        mul_le_mul h1 (hg s hs) (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (((N + 1 : ℕ) : ℝ) * s) := by rw [← Real.exp_add]; congr 1; push_cast; ring

lemma norm_laplace_integrand_le {g : ℝ → ℝ} {N : ℕ} (hg : ExpBound g N) {w : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hw : ρ ≤ w.re) {s : ℝ} (hs : 0 ≤ s) :
    ‖Complex.exp (-w * (Real.cosh s : ℂ)) * (g s : ℂ)‖ ≤ lapConst N ρ * Real.exp (-s) := by
  rw [norm_mul, norm_exp_neg_mul_cosh, Complex.norm_real, Real.norm_eq_abs]
  have h1 : Real.exp (-(w.re * Real.cosh s)) ≤ Real.exp (-(ρ * Real.cosh s)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hw (by linarith [Real.one_le_cosh s] : 0 ≤ Real.cosh s)
    linarith
  calc Real.exp (-(w.re * Real.cosh s)) * |g s|
      ≤ Real.exp (-(ρ * Real.cosh s)) * Real.exp (N * s) :=
        mul_le_mul h1 (hg s hs) (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (N * s) * Real.exp (-(ρ * Real.cosh s)) := mul_comm _ _
    _ ≤ _ := exp_nat_mul_exp_neg_cosh_le N hρ s

lemma integrableOn_lapDom (c : ℝ) :
    IntegrableOn (fun s : ℝ => c * Real.exp (-s)) (Ioi 0) := by
  have := (integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).const_mul c
  exact IntegrableOn.congr_fun this (fun s _ => by simp) measurableSet_Ioi

lemma continuous_laplace_integrand {g : ℝ → ℝ} (hgc : Continuous g) (w : ℂ) :
    Continuous fun s : ℝ => Complex.exp (-w * (Real.cosh s : ℂ)) * (g s : ℂ) :=
  (Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp Real.continuous_cosh))).mul (Complex.continuous_ofReal.comp hgc)

lemma integrableOn_laplace {g : ℝ → ℝ} {N : ℕ} (hg : ExpBound g N) (hgc : Continuous g) {w : ℂ}
    (hw : 0 < w.re) :
    IntegrableOn (fun s : ℝ => Complex.exp (-w * (Real.cosh s : ℂ)) * (g s : ℂ)) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_lapDom (lapConst N w.re)) ?_ ?_
  · exact (continuous_laplace_integrand hgc w).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact norm_laplace_integrand_le hg hw le_rfl (le_of_lt hs)

lemma re_pos_of_mem_ball {w₀ w : ℂ} (hw : w ∈ Metric.ball w₀ (w₀.re / 2)) :
    w₀.re / 2 ≤ w.re := by
  have h1 := Complex.abs_re_le_norm (w - w₀)
  have h2 : ‖w - w₀‖ < w₀.re / 2 := by simpa [Complex.dist_eq] using hw
  have h3 : (w - w₀).re = w.re - w₀.re := by simp
  rw [h3] at h1
  have := (abs_le.mp h1).1
  linarith

/-- Holomorphy of `w ↦ ∫₀^∞ e^{-w cosh s} g(s) ds` on `Re w > 0`: the derivative is the Laplace
integral of `-cosh s · g(s)`. -/
lemma hasDerivAt_laplaceCosh {g : ℝ → ℝ} {N : ℕ} (hg : ExpBound g N) (hgc : Continuous g) {w₀ : ℂ}
    (hw₀ : 0 < w₀.re) :
    HasDerivAt (laplaceCosh g) (laplaceCosh (fun s => -(Real.cosh s * g s)) w₀) w₀ := by
  set ρ := w₀.re with hρ
  have hρ2 : 0 < ρ / 2 := by positivity
  have hs : Metric.ball w₀ (ρ / 2) ∈ 𝓝 w₀ := Metric.ball_mem_nhds _ hρ2
  have hg' : ExpBound (fun s => -(Real.cosh s * g s)) (N + 1) := by
    intro s hs
    rw [abs_neg]; exact hg.cosh_mul_fun s hs
  have hgc' : Continuous fun s => -(Real.cosh s * g s) := (Real.continuous_cosh.mul hgc).neg
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (w : ℂ) (s : ℝ) => Complex.exp (-w * (Real.cosh s : ℂ)) * (g s : ℂ))
    (F' := fun (w : ℂ) (s : ℝ) => Complex.exp (-w * (Real.cosh s : ℂ)) *
      ((-(Real.cosh s * g s) : ℝ) : ℂ))
    (bound := fun s => lapConst (N + 1) (ρ / 2) * Real.exp (-s))
    (x₀ := w₀) hs
    (Filter.Eventually.of_forall fun w => (continuous_laplace_integrand hgc w).aestronglyMeasurable)
    (integrableOn_laplace hg hgc hw₀)
    (continuous_laplace_integrand hgc' w₀).aestronglyMeasurable
    ?_ (integrableOn_lapDom _) ?_
  · exact key.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs w hw
    exact norm_laplace_integrand_le hg' hρ2 (re_pos_of_mem_ball hw) (le_of_lt hs)
  · refine Filter.Eventually.of_forall fun s w _ => ?_
    have h1 : HasDerivAt (fun w : ℂ => -w * (Real.cosh s : ℂ)) (-(Real.cosh s : ℂ)) w := by
      simpa using ((hasDerivAt_id w).neg.mul_const (Real.cosh s : ℂ))
    refine (h1.cexp.mul_const (g s : ℂ)).congr_deriv ?_
    push_cast; ring

lemma differentiableOn_laplaceCosh {g : ℝ → ℝ} {N : ℕ} (hg : ExpBound g N) (hgc : Continuous g) :
    DifferentiableOn ℂ (laplaceCosh g) {w : ℂ | 0 < w.re} := fun _ hw =>
  (hasDerivAt_laplaceCosh hg hgc hw).differentiableAt.differentiableWithinAt

/-! ### Linearity -/

lemma laplaceCosh_add {g₁ g₂ : ℝ → ℝ} {N : ℕ} (h₁ : ExpBound g₁ N) (h₂ : ExpBound g₂ N)
    (c₁ : Continuous g₁) (c₂ : Continuous g₂) {w : ℂ} (hw : 0 < w.re) :
    laplaceCosh (fun s => g₁ s + g₂ s) w = laplaceCosh g₁ w + laplaceCosh g₂ w := by
  unfold laplaceCosh
  rw [← integral_add (integrableOn_laplace h₁ c₁ hw) (integrableOn_laplace h₂ c₂ hw)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  push_cast; ring

lemma laplaceCosh_sub {g₁ g₂ : ℝ → ℝ} {N : ℕ} (h₁ : ExpBound g₁ N) (h₂ : ExpBound g₂ N)
    (c₁ : Continuous g₁) (c₂ : Continuous g₂) {w : ℂ} (hw : 0 < w.re) :
    laplaceCosh (fun s => g₁ s - g₂ s) w = laplaceCosh g₁ w - laplaceCosh g₂ w := by
  unfold laplaceCosh
  rw [← integral_sub (integrableOn_laplace h₁ c₁ hw) (integrableOn_laplace h₂ c₂ hw)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  push_cast; ring

lemma laplaceCosh_const_mul (c : ℝ) (g : ℝ → ℝ) (w : ℂ) :
    laplaceCosh (fun s => c * g s) w = (c : ℂ) * laplaceCosh g w := by
  unfold laplaceCosh
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  push_cast; ring

/-- Norm bound by the real Laplace integral at any `ρ ≤ Re w`. -/
lemma norm_laplaceCosh_le {g : ℝ → ℝ} {N : ℕ} (hg : ExpBound g N) (hgc : Continuous g)
    (hg0 : ∀ s, 0 ≤ g s) {w : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hw : ρ ≤ w.re) :
    ‖laplaceCosh g w‖ ≤ ∫ s in Ioi (0 : ℝ), Real.exp (-(ρ * Real.cosh s)) * g s := by
  have hint : IntegrableOn (fun s : ℝ => Real.exp (-(ρ * Real.cosh s)) * g s) (Ioi 0) := by
    have := integrableOn_laplace hg hgc (w := (ρ : ℂ)) (by simpa using hρ)
    have := this.norm
    refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioi
    rw [norm_mul, norm_exp_neg_mul_cosh, Complex.norm_real, Real.norm_of_nonneg (hg0 s)]
    simp
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => norm_nonneg _) hint ?_
  filter_upwards with s
  rw [norm_mul, norm_exp_neg_mul_cosh, Complex.norm_real, Real.norm_of_nonneg (hg0 s)]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (hg0 s)
  have := mul_le_mul_of_nonneg_right hw (by linarith [Real.one_le_cosh s] : 0 ≤ Real.cosh s)
  linarith

/-! ### `K_ν` -/

/-- `K_ν(w) = ∫₀^∞ e^{-w cosh s} cosh(ν s) ds` (the Macdonald function, `Re w > 0`). -/
noncomputable def besselKP (ν : ℝ) (w : ℂ) : ℂ := laplaceCosh (fun s => Real.cosh (ν * s)) w

lemma continuous_cosh_mul (ν : ℝ) : Continuous fun s : ℝ => Real.cosh (ν * s) :=
  Real.continuous_cosh.comp (continuous_const.mul continuous_id)

lemma continuous_sinh_mul (ν : ℝ) : Continuous fun s : ℝ => Real.sinh (ν * s) :=
  Real.continuous_sinh.comp (continuous_const.mul continuous_id)

lemma besselKP_zero (w : ℂ) : besselKP 0 w = besselK0 w := by
  unfold besselKP laplaceCosh besselK0
  simp

lemma differentiableOn_besselKP (ν : ℝ) : DifferentiableOn ℂ (besselKP ν) {w : ℂ | 0 < w.re} := by
  obtain ⟨N, hN⟩ := exists_nat_ge |ν|
  exact differentiableOn_laplaceCosh (ExpBound.cosh_mul hN) (continuous_cosh_mul ν)

lemma cosh_mul_cosh_mul (ν s : ℝ) :
    Real.cosh s * Real.cosh (ν * s) =
      (Real.cosh ((ν + 1) * s) + Real.cosh ((ν - 1) * s)) / 2 := by
  have e1 : (ν + 1) * s = ν * s + s := by ring
  have e2 : (ν - 1) * s = ν * s - s := by ring
  rw [e1, e2, Real.cosh_add, Real.cosh_sub]; ring

lemma cosh_succ_sub_pred (ν s : ℝ) :
    Real.cosh ((ν + 1) * s) - Real.cosh ((ν - 1) * s) = 2 * (Real.sinh s * Real.sinh (ν * s)) := by
  have e1 : (ν + 1) * s = ν * s + s := by ring
  have e2 : (ν - 1) * s = ν * s - s := by ring
  rw [e1, e2, Real.cosh_add, Real.cosh_sub]; ring

/-- The derivative of `K_ν`: `K_ν' = -(K_{ν+1} + K_{ν-1})/2`. -/
theorem hasDerivAt_besselKP (ν : ℝ) {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt (besselKP ν) (-(1 / 2 : ℂ) * (besselKP (ν + 1) w + besselKP (ν - 1) w)) w := by
  obtain ⟨N, hN⟩ := exists_nat_ge (|ν| + 1)
  have hν : |ν| ≤ N := by linarith [abs_nonneg ν]
  have h1 : |ν + 1| ≤ N := by
    have := abs_add_le ν 1; rw [abs_one] at this; linarith
  have h2 : |ν - 1| ≤ N := by
    have := abs_sub ν 1; rw [abs_one] at this; linarith
  have hd := hasDerivAt_laplaceCosh (ExpBound.cosh_mul hν) (continuous_cosh_mul ν) hw
  refine hd.congr_deriv ?_
  have e : (fun s : ℝ => -(Real.cosh s * Real.cosh (ν * s))) =
      fun s => (-(1 / 2 : ℝ)) * (Real.cosh ((ν + 1) * s) + Real.cosh ((ν - 1) * s)) := by
    funext s; rw [cosh_mul_cosh_mul]; ring
  rw [e, laplaceCosh_const_mul, laplaceCosh_add (ExpBound.cosh_mul h1) (ExpBound.cosh_mul h2)
    (continuous_cosh_mul _) (continuous_cosh_mul _) hw]
  unfold besselKP
  push_cast; ring

/-- The three-term relation `K_{ν+1}(w) - K_{ν-1}(w) = (2ν/w) K_ν(w)`. -/
theorem besselKP_add_one_sub (ν : ℝ) {w : ℂ} (hw : 0 < w.re) :
    besselKP (ν + 1) w - besselKP (ν - 1) w = (2 * (ν : ℂ) / w) * besselKP ν w := by
  obtain ⟨N, hN⟩ := exists_nat_ge (|ν| + 1)
  have hν : |ν| ≤ N := by linarith [abs_nonneg ν]
  have h1 : |ν + 1| ≤ N := by
    have := abs_add_le ν 1; rw [abs_one] at this; linarith
  have h2 : |ν - 1| ≤ N := by
    have := abs_sub ν 1; rw [abs_one] at this; linarith
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
  -- the identity `K_{ν+1} - K_{ν-1} = 2 L(sinh s sinh νs)`
  have hL1 : besselKP (ν + 1) w - besselKP (ν - 1) w =
      (2 : ℂ) * laplaceCosh (fun s => Real.sinh s * Real.sinh (ν * s)) w := by
    unfold besselKP
    rw [← laplaceCosh_sub (ExpBound.cosh_mul h1) (ExpBound.cosh_mul h2)
      (continuous_cosh_mul _) (continuous_cosh_mul _) hw]
    have e : (fun s : ℝ => Real.cosh ((ν + 1) * s) - Real.cosh ((ν - 1) * s)) =
        fun s => (2 : ℝ) * (Real.sinh s * Real.sinh (ν * s)) := by
      funext s; exact cosh_succ_sub_pred ν s
    rw [e, laplaceCosh_const_mul]; push_cast; ring
  -- FTC for `ph(s) = e^{-w cosh s} sinh(ν s)`
  have hsh : ExpBound (fun s => Real.sinh (ν * s)) N := ExpBound.sinh_mul hν
  have hch : ExpBound (fun s => Real.cosh (ν * s)) N := ExpBound.cosh_mul hν
  have hss : ExpBound (fun s => Real.sinh s * Real.sinh (ν * s)) (N + 1) := hsh.sinh_mul_fun
  have hcc : Continuous fun s : ℝ => Real.sinh s * Real.sinh (ν * s) :=
    Real.continuous_sinh.mul (continuous_sinh_mul ν)
  let ph : ℝ → ℂ := fun s => Complex.exp (-w * (Real.cosh s : ℂ)) * (Real.sinh (ν * s) : ℂ)
  let ph' : ℝ → ℂ := fun s => (-w) * (Complex.exp (-w * (Real.cosh s : ℂ)) *
      ((Real.sinh s * Real.sinh (ν * s) : ℝ) : ℂ)) +
    (ν : ℂ) * (Complex.exp (-w * (Real.cosh s : ℂ)) * ((Real.cosh (ν * s) : ℝ) : ℂ))
  have hderiv : ∀ s ∈ Ioi (0 : ℝ), HasDerivAt ph (ph' s) s := by
    intro s _
    have hc : HasDerivAt (fun s : ℝ => (Real.cosh s : ℂ)) (Real.sinh s : ℂ) s :=
      (Real.hasDerivAt_cosh s).ofReal_comp
    have hE : HasDerivAt (fun s : ℝ => Complex.exp (-w * (Real.cosh s : ℂ)))
        (Complex.exp (-w * (Real.cosh s : ℂ)) * (-w * (Real.sinh s : ℂ))) s :=
      (hc.const_mul (-w)).cexp
    have hS : HasDerivAt (fun s : ℝ => (Real.sinh (ν * s) : ℂ))
        ((ν * Real.cosh (ν * s) : ℝ) : ℂ) s := by
      have := ((Real.hasDerivAt_sinh (ν * s)).comp s ((hasDerivAt_id s).const_mul ν))
      simpa [mul_comm] using this.ofReal_comp
    refine (hE.mul hS).congr_deriv ?_
    simp only [ph']; push_cast; ring
  have hint1 : IntegrableOn (fun s : ℝ => Complex.exp (-w * (Real.cosh s : ℂ)) *
      ((Real.sinh s * Real.sinh (ν * s) : ℝ) : ℂ)) (Ioi 0) := integrableOn_laplace hss hcc hw
  have hint2 : IntegrableOn (fun s : ℝ => Complex.exp (-w * (Real.cosh s : ℂ)) *
      ((Real.cosh (ν * s) : ℝ) : ℂ)) (Ioi 0) := integrableOn_laplace hch (continuous_cosh_mul ν) hw
  have hlim : Tendsto ph atTop (𝓝 0) := by
    have hb : ∀ s : ℝ, 0 ≤ s → ‖ph s‖ ≤ lapConst N w.re * Real.exp (-s) := fun s hs =>
      norm_laplace_integrand_le hsh hw le_rfl hs
    have hz : Tendsto (fun s : ℝ => lapConst N w.re * Real.exp (-s)) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul (lapConst N w.re)
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    exact hb s hs
  have hcont : ContinuousWithinAt ph (Ici 0) 0 := by
    have : Continuous ph := continuous_laplace_integrand (continuous_sinh_mul ν) w
    exact this.continuousWithinAt
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    ((hint1.const_mul (-w)).add (hint2.const_mul (ν : ℂ))) hlim
  have hφ0 : ph 0 = 0 := by simp [ph]
  rw [hφ0, sub_zero] at hftc
  rw [integral_add (hint1.const_mul (-w)) (hint2.const_mul (ν : ℂ)), integral_const_mul,
    integral_const_mul] at hftc
  have hLs : laplaceCosh (fun s => Real.sinh s * Real.sinh (ν * s)) w =
      (ν : ℂ) / w * besselKP ν w := by
    have : (-w) * laplaceCosh (fun s => Real.sinh s * Real.sinh (ν * s)) w +
        (ν : ℂ) * besselKP ν w = 0 := hftc
    field_simp
    linear_combination (-1 : ℂ) * this
  rw [hL1, hLs]; field_simp

/-- `d/dw [w^{-p} K_p(w)] = -w^{-p} K_{p+1}(w)` for natural `p`. -/
theorem hasDerivAt_besselKP_ratio (p : ℕ) {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt (fun w : ℂ => w ^ (-(p : ℤ)) * besselKP p w)
      (-(w ^ (-(p : ℤ)) * besselKP ((p : ℝ) + 1) w)) w := by
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
  have hK := hasDerivAt_besselKP (p : ℝ) hw
  have hz := hasDerivAt_zpow (-(p : ℤ)) w (Or.inl hw0)
  have hrec := besselKP_add_one_sub (p : ℝ) hw
  push_cast at hrec
  refine (hz.mul hK).congr_deriv ?_
  have hpm : besselKP ((p : ℝ) - 1) w = besselKP ((p : ℝ) + 1) w - (2 * (p : ℂ) / w) * besselKP p w := by
    rw [← hrec]; ring
  rw [hpm]
  have e1 : w ^ (-(p : ℤ) - 1) = w ^ (-(p : ℤ)) * w⁻¹ := by
    rw [zpow_sub₀ hw0, zpow_one, div_eq_mul_inv]
  rw [e1]
  push_cast
  field_simp
  ring

/-! ### The order-`p` Hankel function -/

/-- `H_p¹(z) = (2/(π i)) e^{-iπp/2} K_p(-i z)`, defined by its Laplace form; meaningful for `Im z > 0`. -/
noncomputable def hankelOrd (p : ℕ) (z : ℂ) : ℂ :=
  (2 / ((π : ℂ) * I)) * Complex.exp (-(I * (π : ℂ) * (p : ℂ) / 2)) * besselKP (p : ℝ) (-I * z)

lemma neg_I_mul_re' (z : ℂ) : (-I * z).re = z.im := by simp

lemma exp_neg_I_pi_half : Complex.exp (-(I * (π : ℂ) / 2)) = -I := by
  rw [show -(I * (π : ℂ) / 2) = (-(π / 2 : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
  simp [Complex.cos_neg, Complex.sin_neg]

lemma hankelOrd_zero (z : ℂ) : hankelOrd 0 z = hankel0 z := by
  unfold hankelOrd hankel0
  simp [besselKP_zero]

lemma differentiableOn_hankelOrd (p : ℕ) : DifferentiableOn ℂ (hankelOrd p) {z : ℂ | 0 < z.im} := by
  unfold hankelOrd
  refine DifferentiableOn.const_mul ?_ _
  refine (differentiableOn_besselKP (p : ℝ)).comp (by fun_prop) ?_
  intro z hz
  simpa using hz

lemma hankelOrd_succ_factor (p : ℕ) :
    Complex.exp (-(I * (π : ℂ) * ((p + 1 : ℕ) : ℂ) / 2)) =
      Complex.exp (-(I * (π : ℂ) * (p : ℂ) / 2)) * (-I) := by
  rw [← exp_neg_I_pi_half, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- `d/dz [z^{-p} H_p(z)] = -z^{-p} H_{p+1}(z)` on `Im z > 0`. -/
theorem hasDerivAt_hankelOrd_ratio (p : ℕ) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (fun z : ℂ => z ^ (-(p : ℤ)) * hankelOrd p z)
      (-(z ^ (-(p : ℤ)) * hankelOrd (p + 1) z)) z := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hw : 0 < (-I * z).re := by rw [neg_I_mul_re']; exact hz
  have hK := hasDerivAt_besselKP (p : ℝ) hw
  have hzp := hasDerivAt_zpow (-(p : ℤ)) z (Or.inl hz0)
  have hrec := besselKP_add_one_sub (p : ℝ) hw
  push_cast at hrec
  have hlin : HasDerivAt (fun z : ℂ => -I * z) (-I) z := by
    simpa using (hasDerivAt_id z).const_mul (-I)
  have hKc := HasDerivAt.scomp z hK hlin
  have hc := (hKc.const_mul ((2 / ((π : ℂ) * I)) * Complex.exp (-(I * (π : ℂ) * (p : ℂ) / 2))))
  refine (hzp.mul hc).congr_deriv ?_
  simp only [Function.comp_apply, smul_eq_mul]
  have hpm : besselKP ((p : ℝ) - 1) (-I * z) = besselKP ((p : ℝ) + 1) (-I * z) -
      (2 * (p : ℂ) / (-I * z)) * besselKP (p : ℝ) (-I * z) := by
    rw [← hrec]; ring
  rw [hpm]
  have e1 : z ^ (-(p : ℤ) - 1) = z ^ (-(p : ℤ)) * z⁻¹ := by
    rw [zpow_sub₀ hz0, zpow_one, div_eq_mul_inv]
  have hsucc : hankelOrd (p + 1) z = (2 / ((π : ℂ) * I)) *
      (Complex.exp (-(I * (π : ℂ) * (p : ℂ) / 2)) * (-I)) * besselKP ((p : ℝ) + 1) (-I * z) := by
    unfold hankelOrd
    rw [← hankelOrd_succ_factor]
    push_cast; ring_nf
  rw [hsucc, e1]
  push_cast
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  field_simp
  ring

/-- The `x`-form of the kernel relation: for `K > 0`, `Im b > 0`, `x > 0`,
`∂_x [(b/x)^p H_p(K x b)] = -K b (b/x)^p H_{p+1}(K x b)`. -/
theorem hasDerivAt_hankelOrd_scaled (p : ℕ) {K : ℝ} (hK : 0 < K) {b : ℂ} (hb : 0 < b.im) {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => (b / (x : ℂ)) ^ p * hankelOrd p ((K : ℂ) * (x : ℂ) * b))
      (-((K : ℂ) * b * ((b / (x : ℂ)) ^ p * hankelOrd (p + 1) ((K : ℂ) * (x : ℂ) * b)))) x := by
  have hb0 : b ≠ 0 := by intro h; rw [h] at hb; simp at hb
  have hK0 : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  set z₀ : ℂ := (K : ℂ) * (x : ℂ) * b with hz₀
  have hzim : 0 < z₀.im := by
    have : z₀ = ((K * x : ℝ) : ℂ) * b := by rw [hz₀]; push_cast; ring
    rw [this, Complex.im_ofReal_mul]; positivity
  have hr := hasDerivAt_hankelOrd_ratio p hzim
  have hz₀' : (K : ℂ) * b * (x : ℂ) = z₀ := by rw [hz₀]; ring
  have hlin : HasDerivAt (fun ξ : ℂ => (K : ℂ) * b * ξ) ((K : ℂ) * b) (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).const_mul ((K : ℂ) * b)
  have hr' : HasDerivAt (fun z : ℂ => z ^ (-(p : ℤ)) * hankelOrd p z)
      (-(z₀ ^ (-(p : ℤ)) * hankelOrd (p + 1) z₀)) ((K : ℂ) * b * (x : ℂ)) := by
    rw [hz₀']; exact hr
  have hcomp := (hr'.scomp (x : ℂ) hlin).const_mul (((K : ℂ) * b ^ 2) ^ p)
  have key : ∀ ξ : ℂ, ξ ≠ 0 → ((K : ℂ) * b ^ 2) ^ p * ((K * b * ξ) ^ (-(p : ℤ))) = (b / ξ) ^ p := by
    intro ξ hξ
    rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, ← div_pow]
    congr 1
    field_simp
  have hev : (fun ξ : ℂ => ((K : ℂ) * b ^ 2) ^ p *
        (((fun z : ℂ => z ^ (-(p : ℤ)) * hankelOrd p z) ∘ fun ξ : ℂ => (K : ℂ) * b * ξ) ξ)) =ᶠ[𝓝 (x : ℂ)]
      fun ξ : ℂ => (b / ξ) ^ p * hankelOrd p ((K : ℂ) * ξ * b) := by
    filter_upwards [isOpen_ne.mem_nhds hx0] with ξ hξ
    simp only [Function.comp_apply]
    rw [← mul_assoc, key ξ hξ]
    congr 2; ring
  have hfin := (hcomp.congr_of_eventuallyEq hev.symm)
  have := hfin.comp_ofReal
  refine this.congr_deriv ?_
  have hk := key (x : ℂ) hx0
  rw [hz₀'] at hk
  rw [smul_eq_mul, ← hk]; ring

/-- The real Laplace integral `∫₀^∞ e^{-ρ cosh s} cosh(p s) ds` (the size of `K_p` on `Re w ≥ ρ`). -/
noncomputable def hankelBoundR (p : ℕ) (ρ : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), Real.exp (-(ρ * Real.cosh s)) * Real.cosh ((p : ℝ) * s)

lemma norm_two_div_pi_I : ‖(2 : ℂ) / ((π : ℂ) * I)‖ = 2 / π := by
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  simp

lemma norm_exp_phase (p : ℕ) : ‖Complex.exp (-(I * (π : ℂ) * (p : ℂ) / 2))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- `‖H_p¹(z)‖ ≤ (2/π) ∫₀^∞ e^{-ρ cosh s} cosh(p s) ds` whenever `Im z ≥ ρ > 0`. -/
theorem norm_hankelOrd_le (p : ℕ) {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hz : ρ ≤ z.im) :
    ‖hankelOrd p z‖ ≤ (2 / π) * hankelBoundR p ρ := by
  obtain ⟨N, hN⟩ := exists_nat_ge |(p : ℝ)|
  have hK := norm_laplaceCosh_le (ExpBound.cosh_mul hN) (continuous_cosh_mul (p : ℝ))
    (fun s => (Real.cosh_pos _).le) (w := -I * z) hρ (by rw [neg_I_mul_re']; exact hz)
  unfold hankelOrd
  rw [norm_mul, norm_mul, norm_two_div_pi_I, norm_exp_phase, mul_one]
  exact mul_le_mul_of_nonneg_left hK (by positivity)

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.besselKP_add_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselKP_add_one_sub

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.hasDerivAt_hankelOrd_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_hankelOrd_ratio

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.hasDerivAt_hankelOrd_scaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_hankelOrd_scaled

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.norm_hankelOrd_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_hankelOrd_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.differentiableOn_hankelOrd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms differentiableOn_hankelOrd

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.hankelOrd_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelOrd_zero

end FormalResearch.ModularBootstrap.Upper.Hankel
