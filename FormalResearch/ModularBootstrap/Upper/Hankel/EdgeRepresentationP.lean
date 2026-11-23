module

public import FormalResearch.ModularBootstrap.Upper.Hankel.OrderRaising
public import FormalResearch.ModularBootstrap.Upper.Hankel.HankelOrderP
public import FormalResearch.ModularBootstrap.Upper.Hankel.EdgeRepresentation

/-!
# Order-`p` upper-edge Hankel representation (`fw:e1.2a`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, section `fw:s1`, formula `fw:e1.2a`; plan item A3,
order `p`.

For `h` satisfying the hypotheses `EdgeHankelHyp h a C` of Lemma `SD_H`, `p : ℕ`, `c' > 0`, `x > 0`,
`k = 4π c' x/3`, `t = c' x²/3`:

`(𝓗_{p+1} h₀)(c' x²/3) = (2π c'/3) ∫_{E₊} h₀(b) (b/x)^p H_p¹(k b) b db`   (`edge_hankel_representation_P`),

where `(𝓗_{p+1} h₀)(t) = 2π ∫₀^∞ h₀(√(3s/c')) (s/t)^{p/2} J_p(4π√(s t)) ds` is `edgeHankelP`.

The proof is the paper's first route: differentiate the order-`0` identity (`edge_hankel_representation`)
`p` times.  On the transform side this is the order raising of `OrderRaising` (`∂_t 𝓗_{p+1} = -2π 𝓗_{p+2}`);
on the contour side it is differentiation under `∫_{E₊}` using
`∂_x [(b/x)^p H_p(K x b)] = -K b (b/x)^p H_{p+1}(K x b)` (`hasDerivAt_hankelOrd_scaled`) and the
`x`-uniform bound `‖H_q(z)‖ ≤ (2/π) ∫₀^∞ e^{-ρ cosh s} cosh(q s) ds` for `Im z ≥ ρ`.  The induction step
equates `-2π (2c'x/3) 𝓗_{p+2}h₀(t)` with `-(2πc'/3) K x ∫_{E₊} …` (`K = 4π c'/3`).  No boundary value of
`H_p¹` on the real axis and no growth estimate at `b = 0` are needed: the contour never moves.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.Upper.Hankel

/-! ### Polynomial times exponential integrability -/

lemma pow_one_add_mul_exp_le (n : ℕ) {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : 0 ≤ u) :
    (1 + u) ^ n * Real.exp (-a * u) ≤
      ((n ! : ℝ) * (2 / a) ^ n * Real.exp (a / 2)) * Real.exp (-(a / 2) * u) := by
  have h := Real.pow_div_factorial_le_exp (a / 2 * (1 + u)) (by positivity) n
  rw [div_le_iff₀ (by positivity)] at h
  have e1 : (1 + u) ^ n = (2 / a) ^ n * (a / 2 * (1 + u)) ^ n := by
    rw [← mul_pow]; field_simp
  have e2 : Real.exp (a / 2 * (1 + u)) * Real.exp (-a * u) =
      Real.exp (a / 2) * Real.exp (-(a / 2) * u) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc (1 + u) ^ n * Real.exp (-a * u)
      = (2 / a) ^ n * (a / 2 * (1 + u)) ^ n * Real.exp (-a * u) := by rw [e1]
    _ ≤ (2 / a) ^ n * (Real.exp (a / 2 * (1 + u)) * n !) * Real.exp (-a * u) := by gcongr
    _ = (n ! : ℝ) * (2 / a) ^ n * (Real.exp (a / 2 * (1 + u)) * Real.exp (-a * u)) := by ring
    _ = _ := by rw [e2]; ring

lemma integrable_pow_mul_exp_neg_abs (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun v : ℝ => (1 + |v|) ^ n * Real.exp (-a * |v|)) := by
  have hint := (integrable_exp_neg_abs (c := a / 2) (by positivity)).const_mul
    ((n ! : ℝ) * (2 / a) ^ n * Real.exp (a / 2))
  refine Integrable.mono' hint ?_ (Filter.Eventually.of_forall fun v => ?_)
  · exact (by fun_prop : Continuous fun v : ℝ => (1 + |v|) ^ n * Real.exp (-a * |v|)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    exact pow_one_add_mul_exp_le n ha (abs_nonneg v)

lemma integrableOn_mul_pow_exp (N : ℕ) {a K : ℝ} (ha : 0 < a) (hK : 0 ≤ K) :
    IntegrableOn (fun r : ℝ => r * (1 + K * r) ^ N * Real.exp (-a * r)) (Ioi 0) := by
  have hint := (integrableOn_exp_mul_Ioi (a := -(a / 2)) (by linarith) 0).const_mul
    (((N + 1) ! : ℝ) * (2 / a) ^ (N + 1) * Real.exp (a / 2) * (1 + K) ^ N)
  refine Integrable.mono' hint ?_ ?_
  · exact (by fun_prop : Continuous fun r : ℝ => r * (1 + K * r) ^ N * Real.exp (-a * r)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 ≤ r := le_of_lt hr
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 : r * (1 + K * r) ^ N ≤ (1 + K) ^ N * (1 + r) ^ (N + 1) := by
      have a1 : r ≤ 1 + r := by linarith
      have a2 : 1 + K * r ≤ (1 + K) * (1 + r) := by nlinarith
      calc r * (1 + K * r) ^ N ≤ (1 + r) * ((1 + K) * (1 + r)) ^ N := by gcongr
        _ = (1 + K) ^ N * (1 + r) ^ (N + 1) := by rw [mul_pow, pow_succ]; ring
    have h2 := pow_one_add_mul_exp_le (N + 1) ha hr0
    calc r * (1 + K * r) ^ N * Real.exp (-a * r)
        ≤ ((1 + K) ^ N * (1 + r) ^ (N + 1)) * Real.exp (-a * r) := by gcongr
      _ = (1 + K) ^ N * ((1 + r) ^ (N + 1) * Real.exp (-a * r)) := by ring
      _ ≤ (1 + K) ^ N * (((N + 1) ! : ℝ) * (2 / a) ^ (N + 1) * Real.exp (a / 2) *
            Real.exp (-(a / 2) * r)) := by gcongr
      _ = _ := by ring

/-! ### The order-`p` edge transform and integral -/

/-- `(𝓗_{p+1} h₀)(t) = 2π ∫₀^∞ h₀(√(3s/c')) (s/t)^{p/2} J_p(4π√(s t)) ds`. -/
noncomputable def edgeHankelP (p : ℕ) (c' : ℝ) (h : ℂ → ℂ) : ℝ → ℂ :=
  hankelTransformOrd p (fun s : ℝ => h ((√(3 * s / c') : ℝ) : ℂ))

lemma edgeHankelP_zero (c' : ℝ) (h : ℂ → ℂ) (t : ℝ) : edgeHankelP 0 c' h t = edgeHankel c' h t := by
  unfold edgeHankelP hankelTransformOrd edgeHankel
  simp

/-- The integrand `h₀(b) (b/x)^p H_p¹(k b) b` of `fw:e1.2a`, `k = 4π c' x/3`, on `b = v + i/2`. -/
noncomputable def edgeIntegrandP (p : ℕ) (c' : ℝ) (h : ℂ → ℂ) (x : ℝ) (v : ℝ) : ℂ :=
  h ((v : ℂ) + I / 2) * (((v : ℂ) + I / 2) / (x : ℂ)) ^ p *
    hankelOrd p (((4 * π * c' * x / 3 : ℝ) : ℂ) * ((v : ℂ) + I / 2)) * ((v : ℂ) + I / 2)

/-- `∫_{E₊} h₀(b) (b/x)^p H_p¹(k b) b db`. -/
noncomputable def edgeIntegralP (p : ℕ) (c' : ℝ) (h : ℂ → ℂ) (x : ℝ) : ℂ :=
  ∫ v : ℝ, edgeIntegrandP p c' h x v

/-! ### Integrability of the profile on `(0, ∞)` -/

lemma continuous_h_ofReal {h : ℂ → ℂ} {a C : ℝ} (hh : EdgeHankelHyp h a C) :
    Continuous fun r : ℝ => h (r : ℂ) :=
  hh.cont.comp_continuous Complex.continuous_ofReal (fun r => by
    show 0 ≤ (r : ℂ).im ∧ (r : ℂ).im ≤ 1 / 2
    simp)

lemma continuous_h_edge {h : ℂ → ℂ} {a C : ℝ} (hh : EdgeHankelHyp h a C) :
    Continuous fun v : ℝ => h ((v : ℂ) + I / 2) :=
  hh.cont.comp_continuous (by fun_prop) (fun v => by
    show 0 ≤ ((v : ℂ) + I / 2).im ∧ ((v : ℂ) + I / 2).im ≤ 1 / 2
    simp)

/-- The profile `s ↦ h₀(√(3s/c'))` satisfies the order-raising hypotheses of every order. -/
theorem orderRaisingHyp_edge {h : ℂ → ℂ} {a C : ℝ} (ha : 0 < a) (hh : EdgeHankelHyp h a C) {c' : ℝ}
    (hc : 0 < c') (N : ℕ) :
    OrderRaisingHyp (fun s : ℝ => h ((√(3 * s / c') : ℝ) : ℂ)) N := by
  have hcont := continuous_h_ofReal hh
  refine ⟨?_, ?_⟩
  · exact (hcont.comp (by fun_prop : Continuous fun s : ℝ => √(3 * s / c'))).aestronglyMeasurable
  · have hderiv : ∀ r ∈ Ioi (0 : ℝ),
        HasDerivWithinAt (fun r : ℝ => c' * r ^ 2 / 3) (2 * c' * r / 3) (Ioi 0) r := by
      intro r _
      have := ((hasDerivAt_pow 2 r).const_mul c').div_const 3
      simpa [mul_assoc, mul_comm, mul_left_comm] using this.hasDerivWithinAt
    have hinj : InjOn (fun r : ℝ => c' * r ^ 2 / 3) (Ioi 0) := by
      intro r hr s hs hrs
      have hr0 : 0 < r := hr
      have hs0 : 0 < s := hs
      have h1 : r ^ 2 = s ^ 2 := by
        have : c' * r ^ 2 = c' * s ^ 2 := by linarith
        exact mul_left_cancel₀ hc.ne' this
      nlinarith [sq_nonneg (r - s), sq_nonneg (r + s)]
    have himg : (fun r : ℝ => c' * r ^ 2 / 3) '' Ioi 0 = Ioi 0 := by
      ext y
      constructor
      · rintro ⟨r, hr, rfl⟩
        have : 0 < r := hr
        exact div_pos (mul_pos hc (pow_pos this 2)) (by norm_num)
      · intro hy
        have hy' : 0 < y := hy
        refine ⟨√(3 * y / c'), Real.sqrt_pos.mpr (by positivity), ?_⟩
        show c' * (√(3 * y / c')) ^ 2 / 3 = y
        rw [Real.sq_sqrt (by positivity)]
        field_simp
    rw [← himg, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj]
    set K : ℝ := √(c' / 3) with hK
    have hK0 : 0 ≤ K := Real.sqrt_nonneg _
    have hg : IntegrableOn (fun r : ℝ => (2 * c' / 3 * C) * (r * (1 + K * r) ^ N * Real.exp (-a * r)))
        (Ioi 0) := (integrableOn_mul_pow_exp N ha hK0).const_mul _
    refine Integrable.mono' hg ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      have : Continuous fun r : ℝ => h (((√(3 * (c' * r ^ 2 / 3) / c') : ℝ)) : ℂ) :=
        hcont.comp (by fun_prop)
      simp only [smul_eq_mul]
      have hn : Continuous fun r : ℝ => ‖h ((√(3 * (c' * r ^ 2 / 3) / c') : ℝ) : ℂ)‖ := this.norm
      have h1 : Continuous fun r : ℝ => (1 + √(c' * r ^ 2 / 3)) ^ N := by fun_prop
      have h2 : Continuous fun r : ℝ => |2 * c' * r / 3| := by fun_prop
      exact h2.mul (hn.mul h1)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0 < r := hr
      have e1 : √(3 * (c' * r ^ 2 / 3) / c') = r := by
        rw [show 3 * (c' * r ^ 2 / 3) / c' = r ^ 2 by field_simp]
        exact Real.sqrt_sq hr0.le
      have e2 : √(c' * r ^ 2 / 3) = K * r := by
        rw [hK, show c' * r ^ 2 / 3 = (c' / 3) * r ^ 2 by ring, Real.sqrt_mul (by positivity),
          Real.sqrt_sq hr0.le]
      simp only [smul_eq_mul]
      rw [e1, e2, abs_of_pos (by positivity : 0 < 2 * c' * r / 3)]
      have hdec := hh.decay (r : ℂ) (by simp) (by simp)
      simp only [Complex.ofReal_re, abs_of_pos hr0] at hdec
      rw [Real.norm_of_nonneg (by positivity)]
      calc 2 * c' * r / 3 * (‖h (r : ℂ)‖ * (1 + K * r) ^ N)
          ≤ 2 * c' * r / 3 * ((C * Real.exp (-a * r)) * (1 + K * r) ^ N) := by gcongr
        _ = _ := by ring

/-! ### Pointwise bounds on `E₊` -/

lemma EdgeHankelHyp.C_nonneg {h : ℂ → ℂ} {a C : ℝ} (hh : EdgeHankelHyp h a C) : 0 ≤ C := by
  have := hh.decay 0 (by simp) (by simp)
  simp only [Complex.zero_re, abs_zero, mul_zero, Real.exp_zero, mul_one] at this
  exact (norm_nonneg _).trans this

lemma norm_edge_point_le (v : ℝ) :
    ‖(v : ℂ) + I / 2‖ ≤ 1 + |v| := by
  have := Complex.norm_le_abs_re_add_abs_im ((v : ℂ) + I / 2)
  simp only [add_re, Complex.ofReal_re, div_ofNat_re, I_re, add_im, Complex.ofReal_im, div_ofNat_im,
    I_im] at this
  have h2 : |(0 : ℝ) + 1 / 2| = 1 / 2 := by norm_num
  have h3 : |v + 0 / 2| = |v| := by simp
  rw [h3] at this
  simp at this
  linarith

/-- The product of the four factors of the integrand on `E₊` (powers `p`, `j`, Hankel order `q`) is bounded by
`C x^{-p} (2/π) B_q(ρ) (1+|v|)^{p+j} e^{-a|v|}` whenever `ρ ≤ k/2`. -/
lemma norm_edge_factor_le {h : ℂ → ℂ} {a C : ℝ} (hh : EdgeHankelHyp h a C) (p q j : ℕ) {x k ρ : ℝ}
    (hx : 0 < x) (hρ : 0 < ρ) (hk : ρ ≤ k / 2) (v : ℝ) :
    ‖h ((v : ℂ) + I / 2)‖ * ‖(((v : ℂ) + I / 2) / (x : ℂ)) ^ p‖ *
        ‖hankelOrd q ((k : ℂ) * ((v : ℂ) + I / 2))‖ * ‖(v : ℂ) + I / 2‖ ^ j ≤
      C * (1 / x) ^ p * ((2 / π) * hankelBoundR q ρ) * ((1 + |v|) ^ (p + j) * Real.exp (-a * |v|)) := by
  set b : ℂ := (v : ℂ) + I / 2 with hb
  have hbim : b.im = 1 / 2 := by simp [hb]
  have hbre : b.re = v := by simp [hb]
  have hC := hh.C_nonneg
  have h1 : ‖h b‖ ≤ C * Real.exp (-a * |v|) := by
    have := hh.decay b (by rw [hbim]; norm_num) (by rw [hbim])
    rwa [hbre] at this
  have hnb : ‖b‖ ≤ 1 + |v| := norm_edge_point_le v
  have h2 : ‖(b / (x : ℂ)) ^ p‖ ≤ (1 + |v|) ^ p * (1 / x) ^ p := by
    rw [norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg hx.le, ← mul_pow, one_div,
      ← div_eq_mul_inv]
    gcongr
  have h3 : ‖hankelOrd q ((k : ℂ) * b)‖ ≤ (2 / π) * hankelBoundR q ρ := by
    refine norm_hankelOrd_le q hρ ?_
    rw [Complex.im_ofReal_mul, hbim]; linarith
  have h4 : ‖b‖ ^ j ≤ (1 + |v|) ^ j := by gcongr
  have hB : 0 ≤ (2 / π) * hankelBoundR q ρ := (norm_nonneg _).trans h3
  calc ‖h b‖ * ‖(b / (x : ℂ)) ^ p‖ * ‖hankelOrd q ((k : ℂ) * b)‖ * ‖b‖ ^ j
      ≤ (C * Real.exp (-a * |v|)) * ((1 + |v|) ^ p * (1 / x) ^ p) * ((2 / π) * hankelBoundR q ρ) *
        (1 + |v|) ^ j := by gcongr
    _ = C * (1 / x) ^ p * ((2 / π) * hankelBoundR q ρ) * ((1 + |v|) ^ (p + j) * Real.exp (-a * |v|)) := by
        rw [pow_add]; ring

/-! ### Differentiation under `∫_{E₊}` -/

lemma continuous_hankelOrd_edge (p : ℕ) {k : ℝ} (hk : 0 < k) :
    Continuous fun v : ℝ => hankelOrd p ((k : ℂ) * ((v : ℂ) + I / 2)) := by
  refine (differentiableOn_hankelOrd p).continuousOn.comp_continuous (by fun_prop) (fun v => ?_)
  show 0 < ((k : ℂ) * ((v : ℂ) + I / 2)).im
  rw [Complex.im_ofReal_mul]
  simp
  exact hk

lemma continuous_edgeIntegrandP {h : ℂ → ℂ} {a C : ℝ} (hh : EdgeHankelHyp h a C) (p : ℕ) {c' x : ℝ}
    (hc : 0 < c') (hx : 0 < x) : Continuous fun v : ℝ => edgeIntegrandP p c' h x v := by
  have hk : 0 < 4 * π * c' * x / 3 := by positivity
  have h1 := continuous_h_edge hh
  have h2 := continuous_hankelOrd_edge p hk
  have h3 : Continuous fun v : ℝ => (((v : ℂ) + I / 2) / (x : ℂ)) ^ p := by fun_prop
  have h4 : Continuous fun v : ℝ => (v : ℂ) + I / 2 := by fun_prop
  unfold edgeIntegrandP
  exact ((h1.mul h3).mul h2).mul h4

/-- The `x`-derivative of `edgeIntegrandP p`. -/
noncomputable def edgeIntegrandDerivP (p : ℕ) (c' : ℝ) (h : ℂ → ℂ) (x : ℝ) (v : ℝ) : ℂ :=
  h ((v : ℂ) + I / 2) * (-(((4 * π * c' / 3 : ℝ) : ℂ) * ((v : ℂ) + I / 2) *
    ((((v : ℂ) + I / 2) / (x : ℂ)) ^ p *
      hankelOrd (p + 1) (((4 * π * c' * x / 3 : ℝ) : ℂ) * ((v : ℂ) + I / 2))))) * ((v : ℂ) + I / 2)

lemma continuous_edgeIntegrandDerivP {h : ℂ → ℂ} {a C : ℝ} (hh : EdgeHankelHyp h a C) (p : ℕ)
    {c' x : ℝ} (hc : 0 < c') (hx : 0 < x) : Continuous fun v : ℝ => edgeIntegrandDerivP p c' h x v := by
  have hk : 0 < 4 * π * c' * x / 3 := by positivity
  have h1 := continuous_h_edge hh
  have h2 := continuous_hankelOrd_edge (p + 1) hk
  have h3 : Continuous fun v : ℝ => (((v : ℂ) + I / 2) / (x : ℂ)) ^ p := by fun_prop
  have h4 : Continuous fun v : ℝ => (v : ℂ) + I / 2 := by fun_prop
  unfold edgeIntegrandDerivP
  exact (h1.mul ((continuous_const.mul h4).mul (h3.mul h2)).neg).mul h4

lemma edgeIntegrandDerivP_eq (p : ℕ) (c' : ℝ) (h : ℂ → ℂ) {x : ℝ} (hx : 0 < x) (v : ℝ) :
    edgeIntegrandDerivP p c' h x v =
      -(((4 * π * c' / 3 : ℝ) : ℂ) * (x : ℂ)) * edgeIntegrandP (p + 1) c' h x v := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  unfold edgeIntegrandDerivP edgeIntegrandP
  rw [pow_succ]
  field_simp

lemma hasDerivAt_edgeIntegrandP (h : ℂ → ℂ) (p : ℕ) {c' : ℝ} (hc : 0 < c') {x : ℝ} (hx : 0 < x) (v : ℝ) :
    HasDerivAt (fun x : ℝ => edgeIntegrandP p c' h x v) (edgeIntegrandDerivP p c' h x v) x := by
  have hK : 0 < 4 * π * c' / 3 := by positivity
  set b : ℂ := (v : ℂ) + I / 2 with hb
  have hbim : 0 < b.im := by simp [hb]
  have hd := hasDerivAt_hankelOrd_scaled p hK hbim hx
  have hfun : (fun x : ℝ => edgeIntegrandP p c' h x v) = fun x : ℝ =>
      h b * ((b / (x : ℂ)) ^ p * hankelOrd p (((4 * π * c' / 3 : ℝ) : ℂ) * (x : ℂ) * b)) * b := by
    funext x
    unfold edgeIntegrandP
    have : ((4 * π * c' * x / 3 : ℝ) : ℂ) = ((4 * π * c' / 3 : ℝ) : ℂ) * (x : ℂ) := by
      push_cast; ring
    rw [this]; ring
  rw [hfun]
  refine ((hd.const_mul (h b)).mul_const b).congr_deriv ?_
  unfold edgeIntegrandDerivP
  have : ((4 * π * c' * x / 3 : ℝ) : ℂ) = ((4 * π * c' / 3 : ℝ) : ℂ) * (x : ℂ) := by
    push_cast; ring
  rw [this]

theorem hasDerivAt_edgeIntegralP {h : ℂ → ℂ} {a C : ℝ} (ha : 0 < a) (hh : EdgeHankelHyp h a C) (p : ℕ)
    {c' : ℝ} (hc : 0 < c') {x₀ : ℝ} (hx₀ : 0 < x₀) :
    HasDerivAt (edgeIntegralP p c' h)
      (-(((4 * π * c' / 3 : ℝ) : ℂ) * (x₀ : ℂ)) * edgeIntegralP (p + 1) c' h x₀) x₀ := by
  set K : ℝ := 4 * π * c' / 3 with hKdef
  have hK : 0 < K := by positivity
  have hC := hh.C_nonneg
  set ρ : ℝ := K * x₀ / 4 with hρ
  have hρ0 : 0 < ρ := by positivity
  set Bd : ℝ := (2 / π) * hankelBoundR (p + 1) ρ with hBd
  have hint : Integrable (fun v : ℝ => (1 + |v|) ^ (p + 2) * Real.exp (-a * |v|)) :=
    integrable_pow_mul_exp_neg_abs (p + 2) ha
  -- integrability at `x₀`
  have hF0 : Integrable (fun v : ℝ => edgeIntegrandP p c' h x₀ v) := by
    have hk0 : 0 < 4 * π * c' * x₀ / 3 := by positivity
    refine Integrable.mono' ((integrable_pow_mul_exp_neg_abs (p + 1) ha).const_mul
      (C * (1 / x₀) ^ p * ((2 / π) * hankelBoundR p (4 * π * c' * x₀ / 3 / 2)))) 
      (continuous_edgeIntegrandP hh p hc hx₀).aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
    have := norm_edge_factor_le hh p p 1 hx₀ (by positivity : 0 < 4 * π * c' * x₀ / 3 / 2) le_rfl v
    unfold edgeIntegrandP
    rw [norm_mul, norm_mul]
    simpa [pow_one] using this
  have hbd : ∀ x ∈ Ioo (x₀ / 2) (3 * x₀ / 2), ∀ v : ℝ,
      ‖edgeIntegrandDerivP p c' h x v‖ ≤ (K * (C * (2 / x₀) ^ p * Bd)) *
        ((1 + |v|) ^ (p + 2) * Real.exp (-a * |v|)) := by
    intro x hx v
    have hx0 : 0 < x := by linarith [hx.1]
    have hρx : ρ ≤ (4 * π * c' * x / 3) / 2 := by
      rw [hρ, hKdef]
      have : 4 * π * c' * x / 3 / 2 = (4 * π * c' / 3) * x / 2 := by ring
      rw [this]
      have : (4 * π * c' / 3) * (x₀ / 2) ≤ (4 * π * c' / 3) * x := mul_le_mul_of_nonneg_left hx.1.le hK.le
      nlinarith
    have h1 := norm_edge_factor_le hh p (p + 1) 2 hx0 hρ0 hρx v
    have hx2 : (1 / x) ^ p ≤ (2 / x₀) ^ p := by
      refine pow_le_pow_left₀ (by positivity) ?_ p
      rw [div_le_div_iff₀ hx0 hx₀]; linarith [hx.1]
    have e : ‖edgeIntegrandDerivP p c' h x v‖ =
        K * (‖h ((v : ℂ) + I / 2)‖ * ‖(((v : ℂ) + I / 2) / (x : ℂ)) ^ p‖ *
          ‖hankelOrd (p + 1) (((4 * π * c' * x / 3 : ℝ) : ℂ) * ((v : ℂ) + I / 2))‖ *
          ‖(v : ℂ) + I / 2‖ ^ 2) := by
      unfold edgeIntegrandDerivP
      have hKn : ‖(4 * π * c' / 3 : ℝ)‖ = 4 * π * c' / 3 := Real.norm_of_nonneg hK.le
      simp only [norm_mul, norm_neg, Complex.norm_real, hKn]
      rw [← hKdef]
      ring
    rw [e]
    calc K * (‖h ((v : ℂ) + I / 2)‖ * ‖(((v : ℂ) + I / 2) / (x : ℂ)) ^ p‖ *
          ‖hankelOrd (p + 1) (((4 * π * c' * x / 3 : ℝ) : ℂ) * ((v : ℂ) + I / 2))‖ *
          ‖(v : ℂ) + I / 2‖ ^ 2)
        ≤ K * (C * (1 / x) ^ p * Bd * ((1 + |v|) ^ (p + 2) * Real.exp (-a * |v|))) := by
          gcongr
      _ ≤ K * (C * (2 / x₀) ^ p * Bd * ((1 + |v|) ^ (p + 2) * Real.exp (-a * |v|))) := by
          have hBd0 : 0 ≤ Bd := by
            have : 0 ≤ hankelBoundR (p + 1) ρ := by
              unfold hankelBoundR
              exact integral_nonneg fun s => by positivity
            rw [hBd]; positivity
          gcongr
      _ = _ := by ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℝ)) (𝕜 := ℝ)
    (F := fun x v => edgeIntegrandP p c' h x v) (F' := fun x v => edgeIntegrandDerivP p c' h x v)
    (bound := fun v => (K * (C * (2 / x₀) ^ p * Bd)) * ((1 + |v|) ^ (p + 2) * Real.exp (-a * |v|)))
    (x₀ := x₀) (s := Ioo (x₀ / 2) (3 * x₀ / 2)) (Ioo_mem_nhds (by linarith) (by linarith))
    (by filter_upwards [Ioi_mem_nhds hx₀] with x hx
        exact (continuous_edgeIntegrandP hh p hc hx).aestronglyMeasurable)
    hF0 (continuous_edgeIntegrandDerivP hh p hc hx₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v x hx => hbd x hx v)
    (hint.const_mul _)
    (Filter.Eventually.of_forall fun v x hx =>
      hasDerivAt_edgeIntegrandP h p hc (by linarith [hx.1]) v)
  refine key.2.congr_deriv ?_
  unfold edgeIntegralP
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  exact edgeIntegrandDerivP_eq p c' h hx₀ v

/-! ### The edge representation of order `p` -/

lemma hasDerivAt_edgeHankelP_comp {h : ℂ → ℂ} {a C : ℝ} (ha : 0 < a) (hh : EdgeHankelHyp h a C) (p : ℕ)
    {c' : ℝ} (hc : 0 < c') {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => edgeHankelP p c' h (c' * x ^ 2 / 3))
      (((2 * c' * x / 3 : ℝ) : ℂ) * (-(2 * (π : ℂ)) * edgeHankelP (p + 1) c' h (c' * x ^ 2 / 3))) x := by
  have ht : 0 < c' * x ^ 2 / 3 := by positivity
  have hF := hasDerivAt_hankelTransformOrd (orderRaisingHyp_edge ha hh hc (p + 1)) ht
  have hT : HasDerivAt (fun x : ℝ => c' * x ^ 2 / 3) (2 * c' * x / 3) x := by
    have := ((hasDerivAt_pow 2 x).const_mul c').div_const 3
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  refine (hF.scomp x hT).congr_deriv ?_
  rw [Complex.real_smul]
  rfl

/-- **Order-`p` upper-edge Hankel representation** (`upper_transfer.tex`, `fw:e1.2a`): for `h` with the
hypotheses `EdgeHankelHyp` of Lemma `SD_H`, `p : ℕ`, `c' > 0`, `x > 0`, `k = 4π c' x/3`:
`(𝓗_{p+1} h)(c' x²/3) = (2π c'/3) ∫_{E₊} h(b) (b/x)^p H_p¹(k b) b db`, `E₊ = ℝ + i/2`. -/
theorem edge_hankel_representation_P {h : ℂ → ℂ} {a C : ℝ} (ha : 0 < a) (hh : EdgeHankelHyp h a C)
    (p : ℕ) {c' : ℝ} (hc : 0 < c') {x : ℝ} (hx : 0 < x) :
    edgeHankelP p c' h (c' * x ^ 2 / 3) = (2 * π * c' / 3 : ℂ) * edgeIntegralP p c' h x := by
  induction p generalizing x with
  | zero =>
    rw [edgeHankelP_zero, edge_hankel_representation ha hh hc hx]
    unfold edgeIntegralP edgeIntegrandP
    simp [hankelOrd_zero]
  | succ n ih =>
    have hL := hasDerivAt_edgeHankelP_comp ha hh n hc hx
    have hR := (hasDerivAt_edgeIntegralP ha hh n hc hx).const_mul (2 * π * c' / 3 : ℂ)
    have hev : (fun x : ℝ => edgeHankelP n c' h (c' * x ^ 2 / 3)) =ᶠ[𝓝 x]
        fun x : ℝ => (2 * π * c' / 3 : ℂ) * edgeIntegralP n c' h x := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact ih hy
    have hD := hL.unique (hR.congr_of_eventuallyEq hev)
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hc0 : (c' : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hne : (2 * (π : ℂ) * (2 * (c' : ℂ) * (x : ℂ) / 3)) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero two_ne_zero hπ) ?_
      exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hc0) hx0) (by norm_num)
    apply mul_left_cancel₀ hne
    push_cast at hD ⊢
    linear_combination (-1 : ℂ) * hD

/-- **`𝓗_w h = (-D_t)^p 𝓗_1 h`** for the edge profile (`fw:e1.1`), `D_t = (2π)^{-1} ∂_t`, `t > 0`. -/
theorem edgeHankelP_eq_iterate {h : ℂ → ℂ} {a C : ℝ} (ha : 0 < a) (hh : EdgeHankelHyp h a C) (p : ℕ)
    {c' : ℝ} (hc : 0 < c') {t : ℝ} (ht : 0 < t) :
    edgeHankelP p c' h t = (negDt^[p] (edgeHankelP 0 c' h)) t :=
  hankelTransformOrd_eq_iterate p (orderRaisingHyp_edge ha hh hc p) ht

/-- The order-`0` case of `edge_hankel_representation_P` is `edge_hankel_representation`, and the
representation of order `p` agrees with the transform `𝓗_{p+1}` of `OrderRaising` (statement check). -/
theorem edge_hankel_representation_P_zero {h : ℂ → ℂ} {a C : ℝ} (ha : 0 < a) (hh : EdgeHankelHyp h a C)
    {c' x : ℝ} (hc : 0 < c') (hx : 0 < x) :
    edgeHankel c' h (c' * x ^ 2 / 3) = (2 * π * c' / 3 : ℂ) * edgeIntegralP 0 c' h x := by
  rw [← edgeHankelP_zero]; exact edge_hankel_representation_P ha hh 0 hc hx

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.edge_hankel_representation_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edge_hankel_representation_P

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.edgeHankelP_eq_iterate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgeHankelP_eq_iterate

end FormalResearch.ModularBootstrap.Upper.Hankel
