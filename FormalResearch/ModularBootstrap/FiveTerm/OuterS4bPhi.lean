module

public import FormalResearch.ModularBootstrap.FiveTerm.OuterStripStatements

/-!
# FIVE-S, S4b (kernel): the potentials `φ_y` on the strip

`φ_y(b) = log(-T_y(b))`, `T_y(b) = tanh(π(b-y)/2) tanh(π(b+y)/2)`, on `0 < Im b < 1`: `-T_y` lies in the slit plane (each
`tanh` factor has positive imaginary part, so `T_y ∉ [0,∞)`), `φ_y' = phiYDeriv`, and the straight-line primitive `phiY`
equals `log(-T_y)` because `-T_y(i/2) = 1`.  On the band `|Im b - 1/2| < 1/4`, uniformly in `y ∈ ℝ` and `Re b`:
`‖φ_y‖ ≤ 19`, `‖φ_y'‖ ≤ 4π`, `‖φ_y''‖ ≤ 8π²`; and `Re φ_y = 0` on `Im b = 1/2`.  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

/-- The strip `0 < Im b < 1`. -/
def imStrip : Set ℂ := {b : ℂ | 0 < b.im ∧ b.im < 1}

lemma isOpen_imStrip : IsOpen imStrip :=
  (isOpen_lt continuous_const Complex.continuous_im).inter (isOpen_lt Complex.continuous_im continuous_const)

lemma sinh_split (w : ℂ) : Complex.sinh w =
    ((Real.sinh w.re * Real.cos w.im : ℝ) : ℂ) + ((Real.cosh w.re * Real.sin w.im : ℝ) : ℂ) * Complex.I := by
  conv_lhs => rw [← Complex.re_add_im w]
  rw [Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast; ring

lemma cosh_split (w : ℂ) : Complex.cosh w =
    ((Real.cosh w.re * Real.cos w.im : ℝ) : ℂ) + ((Real.sinh w.re * Real.sin w.im : ℝ) : ℂ) * Complex.I := by
  conv_lhs => rw [← Complex.re_add_im w]
  rw [Complex.cosh_add, Complex.sinh_mul_I, Complex.cosh_mul_I, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast; ring

lemma re_sinh' (w : ℂ) : (Complex.sinh w).re = Real.sinh w.re * Real.cos w.im := by
  rw [sinh_split w]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im]
  ring
lemma im_sinh' (w : ℂ) : (Complex.sinh w).im = Real.cosh w.re * Real.sin w.im := by
  rw [sinh_split w]
  simp only [Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring
lemma re_cosh' (w : ℂ) : (Complex.cosh w).re = Real.cosh w.re * Real.cos w.im := by
  rw [cosh_split w]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im]
  ring
lemma im_cosh' (w : ℂ) : (Complex.cosh w).im = Real.sinh w.re * Real.sin w.im := by
  rw [cosh_split w]
  simp only [Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

lemma norm_sinh_sq (w : ℂ) : ‖Complex.sinh w‖ ^ 2 = Real.sinh w.re ^ 2 + Real.sin w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, re_sinh', im_sinh']
  nlinarith [Real.cosh_sq w.re, Real.sin_sq_add_cos_sq w.im]

lemma norm_cosh_sq (w : ℂ) : ‖Complex.cosh w‖ ^ 2 = Real.sinh w.re ^ 2 + Real.cos w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, re_cosh', im_cosh']
  nlinarith [Real.cosh_sq w.re, Real.sin_sq_add_cos_sq w.im]

lemma cosh_ne_zero_of {w : ℂ} (h0 : -(π / 2) < w.im) (h1 : w.im < π / 2) : Complex.cosh w ≠ 0 := by
  intro h
  have := norm_cosh_sq w
  rw [h, norm_zero] at this
  have hc : 0 < Real.cos w.im := Real.cos_pos_of_mem_Ioo ⟨h0, h1⟩
  nlinarith [sq_nonneg (Real.sinh w.re), sq_pos_of_pos hc]

lemma sinh_ne_zero_of {w : ℂ} (h0 : 0 < w.im) (h1 : w.im < π) : Complex.sinh w ≠ 0 := by
  intro h
  have := norm_sinh_sq w
  rw [h, norm_zero] at this
  have hc : 0 < Real.sin w.im := Real.sin_pos_of_pos_of_lt_pi h0 h1
  nlinarith [sq_nonneg (Real.sinh w.re), sq_pos_of_pos hc]

lemma im_tanh_pos {w : ℂ} (h0 : 0 < w.im) (h1 : w.im < π / 2) : 0 < (Complex.tanh w).im := by
  have hc := cosh_ne_zero_of (by linarith [Real.pi_pos]) h1
  have hv : 0 < Real.sin w.im * Real.cos w.im :=
    mul_pos (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos]))
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩)
  rw [Complex.tanh_eq_sinh_div_cosh, Complex.div_im, re_sinh', im_sinh', re_cosh',
    im_cosh']
  have hn : 0 < Complex.normSq (Complex.cosh w) := Complex.normSq_pos.mpr hc
  have : Real.cosh w.re * Real.sin w.im * (Real.cosh w.re * Real.cos w.im) -
      Real.sinh w.re * Real.cos w.im * (Real.sinh w.re * Real.sin w.im) =
      Real.sin w.im * Real.cos w.im := by nlinarith [Real.cosh_sq w.re]
  rw [← sub_div, this]
  exact div_pos hv (by rw [Complex.normSq_apply, re_cosh', im_cosh'] at hn; rw [Complex.normSq_apply, re_cosh', im_cosh']; exact hn)

lemma neg_mul_mem_slit {τ₁ τ₂ : ℂ} (h1 : 0 < τ₁.im) (h2 : 0 < τ₂.im) :
    -(τ₁ * τ₂) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : (-(τ₁ * τ₂)).im = 0
  · left
    simp only [Complex.neg_re, Complex.mul_re] at *
    simp only [Complex.neg_im, Complex.mul_im] at him
    set a := τ₁.re; set b := τ₁.im; set c := τ₂.re; set d := τ₂.im
    have e : a * d = -(b * c) := by linarith
    have : d * (b * d - a * c) = b * (d ^ 2 + c ^ 2) := by linear_combination (-c) * e
    have hpos : 0 < d * (b * d - a * c) := by rw [this]; positivity
    have : 0 < b * d - a * c := by
      by_contra hneg
      push Not at hneg
      nlinarith
    linarith
  · right; exact him

/-- `T_y(b) = tanh(π(b-y)/2) tanh(π(b+y)/2)`. -/
noncomputable def Tcx (y : ℝ) (b : ℂ) : ℂ :=
  Complex.tanh ((π : ℂ) * (b - y) / 2) * Complex.tanh ((π : ℂ) * (b + y) / 2)

lemma im_w₁ (y : ℝ) (b : ℂ) : ((π : ℂ) * (b - y) / 2).im = π * b.im / 2 := by simp

lemma im_w₂ (y : ℝ) (b : ℂ) : ((π : ℂ) * (b + y) / 2).im = π * b.im / 2 := by simp

lemma neg_Tcx_mem_slit {y : ℝ} {b : ℂ} (hb : b ∈ imStrip) : -(Tcx y b) ∈ Complex.slitPlane := by
  have hpi := Real.pi_pos
  have h0 : 0 < π * b.im / 2 := by have := hb.1; positivity
  have h1 : π * b.im / 2 < π / 2 := by nlinarith [hb.2]
  exact neg_mul_mem_slit (im_tanh_pos (by rw [im_w₁]; exact h0) (by rw [im_w₁]; exact h1))
    (im_tanh_pos (by rw [im_w₂]; exact h0) (by rw [im_w₂]; exact h1))

lemma hasDerivAt_tanhC {w : ℂ} (hc : Complex.cosh w ≠ 0) : HasDerivAt Complex.tanh (1 / Complex.cosh w ^ 2) w := by
  have h := (Complex.hasDerivAt_sinh w).div (Complex.hasDerivAt_cosh w) hc
  have e : Complex.tanh = Complex.sinh / Complex.cosh := by
    funext z; exact Complex.tanh_eq_sinh_div_cosh z
  rw [e]
  refine h.congr_deriv ?_
  have : Complex.cosh w ^ 2 - Complex.sinh w ^ 2 = 1 := by
    have := Complex.cosh_sq w; linear_combination this
  field_simp
  linear_combination this

lemma sinh_w₁ {y : ℝ} {b : ℂ} (hb : b ∈ imStrip) : Complex.sinh ((π : ℂ) * (b - y)) ≠ 0 := by
  apply sinh_ne_zero_of
  · have := hb.1; simp; positivity
  · have := hb.2; simp; nlinarith [Real.pi_pos]

lemma sinh_w₂ {y : ℝ} {b : ℂ} (hb : b ∈ imStrip) : Complex.sinh ((π : ℂ) * (b + y)) ≠ 0 := by
  apply sinh_ne_zero_of
  · have := hb.1; simp; positivity
  · have := hb.2; simp; nlinarith [Real.pi_pos]

lemma cosh_half₁ {y : ℝ} {b : ℂ} (hb : b ∈ imStrip) : Complex.cosh ((π : ℂ) * (b - y) / 2) ≠ 0 := by
  have hpi := Real.pi_pos
  apply cosh_ne_zero_of
  · rw [im_w₁]; have := hb.1; nlinarith
  · rw [im_w₁]; nlinarith [hb.2]

lemma cosh_half₂ {y : ℝ} {b : ℂ} (hb : b ∈ imStrip) : Complex.cosh ((π : ℂ) * (b + y) / 2) ≠ 0 := by
  have hpi := Real.pi_pos
  apply cosh_ne_zero_of
  · rw [im_w₂]; have := hb.1; nlinarith
  · rw [im_w₂]; nlinarith [hb.2]

lemma tanh_ne_zero_half₁ {y : ℝ} {b : ℂ} (hb : b ∈ imStrip) : Complex.tanh ((π : ℂ) * (b - y) / 2) ≠ 0 := by
  rw [Complex.tanh_eq_sinh_div_cosh]
  refine div_ne_zero ?_ (cosh_half₁ hb)
  have := sinh_w₁ (y := y) hb
  intro h
  apply this
  rw [show (π : ℂ) * (b - y) = 2 * ((π : ℂ) * (b - y) / 2) by ring, Complex.sinh_two_mul, h]; simp

lemma tanh_ne_zero_half₂ {y : ℝ} {b : ℂ} (hb : b ∈ imStrip) : Complex.tanh ((π : ℂ) * (b + y) / 2) ≠ 0 := by
  rw [Complex.tanh_eq_sinh_div_cosh]
  refine div_ne_zero ?_ (cosh_half₂ hb)
  have := sinh_w₂ (y := y) hb
  intro h
  apply this
  rw [show (π : ℂ) * (b + y) = 2 * ((π : ℂ) * (b + y) / 2) by ring, Complex.sinh_two_mul, h]; simp

lemma hasDerivAt_Tcx {y : ℝ} {b : ℂ} (hb : b ∈ imStrip) :
    HasDerivAt (Tcx y) (((π : ℂ) / 2) * (1 / Complex.cosh ((π : ℂ) * (b - y) / 2) ^ 2) *
        Complex.tanh ((π : ℂ) * (b + y) / 2) +
      Complex.tanh ((π : ℂ) * (b - y) / 2) * (((π : ℂ) / 2) * (1 / Complex.cosh ((π : ℂ) * (b + y) / 2) ^ 2))) b := by
  have hw1 : HasDerivAt (fun b : ℂ => (π : ℂ) * (b - y) / 2) ((π : ℂ) / 2) b := by
    have := (((hasDerivAt_id b).sub_const (y : ℂ)).const_mul (π : ℂ)).div_const 2
    refine this.congr_deriv ?_; simp
  have hw2 : HasDerivAt (fun b : ℂ => (π : ℂ) * (b + y) / 2) ((π : ℂ) / 2) b := by
    have := (((hasDerivAt_id b).add_const (y : ℂ)).const_mul (π : ℂ)).div_const 2
    refine this.congr_deriv ?_; simp
  have h1 := (hasDerivAt_tanhC (cosh_half₁ (y := y) hb)).comp b hw1
  have h2 := (hasDerivAt_tanhC (cosh_half₂ (y := y) hb)).comp b hw2
  exact (h1.mul h2).congr_deriv (by simp only [Function.comp_apply]; ring)

/-- `φ_y' = (log(-T_y))'`. -/
lemma hasDerivAt_logTcx {y : ℝ} {b : ℂ} (hb : b ∈ imStrip) :
    HasDerivAt (fun b => Complex.log (-(Tcx y b))) (phiYDeriv y b) b := by
  have h := ((hasDerivAt_Tcx (y := y) hb).neg).clog (neg_Tcx_mem_slit hb)
  refine h.congr_deriv ?_
  have c1 := cosh_half₁ (y := y) hb
  have c2 := cosh_half₂ (y := y) hb
  have t1 := tanh_ne_zero_half₁ (y := y) hb
  have t2 := tanh_ne_zero_half₂ (y := y) hb
  have s1 : Complex.sinh ((π : ℂ) * (b - y) / 2) ≠ 0 := by
    intro h; apply t1; rw [Complex.tanh_eq_sinh_div_cosh, h]; simp
  have s2 : Complex.sinh ((π : ℂ) * (b + y) / 2) ≠ 0 := by
    intro h; apply t2; rw [Complex.tanh_eq_sinh_div_cosh, h]; simp
  simp only [Pi.neg_apply, Tcx, phiYDeriv]
  rw [show (π : ℂ) * (b - y) = 2 * ((π : ℂ) * (b - y) / 2) by ring,
    show (π : ℂ) * (b + y) = 2 * ((π : ℂ) * (b + y) / 2) by ring, Complex.sinh_two_mul, Complex.sinh_two_mul]
  rw [Complex.tanh_eq_sinh_div_cosh, Complex.tanh_eq_sinh_div_cosh]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp


/-! ### The closed form `phiY = log(-T)` -/

lemma norm_tanh_sq (w : ℂ) :
    ‖Complex.tanh w‖ ^ 2 = (Real.sinh w.re ^ 2 + Real.sin w.im ^ 2) / (Real.sinh w.re ^ 2 + Real.cos w.im ^ 2) := by
  rw [Complex.tanh_eq_sinh_div_cosh, norm_div, div_pow, norm_sinh_sq, norm_cosh_sq]

lemma norm_tanh_eq_one {w : ℂ} (h : w.im = π / 4) : ‖Complex.tanh w‖ = 1 := by
  have h2 := norm_tanh_sq w
  rw [h, Real.sin_pi_div_four, Real.cos_pi_div_four] at h2
  have hp : (0 : ℝ) < Real.sinh w.re ^ 2 + (√2 / 2) ^ 2 := by
    have : (0 : ℝ) < (√2 / 2) ^ 2 := by positivity
    positivity
  rw [div_self hp.ne'] at h2
  have hn := norm_nonneg (Complex.tanh w)
  nlinarith

lemma Tcx_half (y : ℝ) : -(Tcx y (Complex.I / 2)) = 1 := by
  have hw : ((π : ℂ) * (Complex.I / 2 + y) / 2) = -(starRingEnd ℂ) ((π : ℂ) * (Complex.I / 2 - y) / 2) := by
    have h2c : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
    apply Complex.ext <;> simp [h2c] <;> ring
  have him : ((π : ℂ) * (Complex.I / 2 - y) / 2).im = π / 4 := by simp; ring
  have hn := norm_tanh_eq_one him
  unfold Tcx
  rw [hw, Complex.tanh_neg, Complex.tanh_conj, mul_neg, neg_neg, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
  simp

lemma sin_ge_half {x : ℝ} (h1 : π / 4 ≤ x) (h2 : x ≤ 3 * π / 4) : 1 / 2 ≤ Real.sin x := by
  have hpi := Real.pi_pos
  rcases le_total x (π / 2) with h | h
  · have := Real.mul_le_sin (by linarith : 0 ≤ x) h
    have : 1 / 2 ≤ 2 / π * x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hpi]; nlinarith
    linarith
  · have h3 : Real.sin x = Real.sin (π - x) := (Real.sin_pi_sub x).symm
    rw [h3]
    have := Real.mul_le_sin (by linarith : 0 ≤ π - x) (by linarith)
    have : 1 / 2 ≤ 2 / π * (π - x) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hpi]; nlinarith
    linarith

/-- the band `|Im b - 1/2| < 1/4`. -/
lemma band_sub_strip {b : ℂ} (hb : |b.im - 1 / 2| < 1 / 4) : b ∈ imStrip := by
  rw [abs_lt] at hb; exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

lemma phiY_eq {y : ℝ} {b : ℂ} (hb : b ∈ imStrip) : phiY y b = Complex.log (-(Tcx y b)) := by
  set cp : ℝ → ℂ := fun t => Complex.I / 2 + (t : ℂ) * (b - Complex.I / 2) with hcp
  have hmem : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → cp t ∈ imStrip := by
    intro t ht
    show 0 < (cp t).im ∧ (cp t).im < 1
    simp only [hcp, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_im, Complex.sub_re, Complex.I_im, Complex.I_re, Complex.div_ofNat_im,
      Complex.div_ofNat_re]
    have h1 := hb.1; have h2 := hb.2
    constructor <;> nlinarith [ht.1, ht.2]
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => Complex.log (-(Tcx y (cp t))))
        (phiYDeriv y (cp t) * (b - Complex.I / 2)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hc : HasDerivAt (fun s : ℂ => Complex.I / 2 + s * (b - Complex.I / 2)) (b - Complex.I / 2) (t : ℂ) :=
      (((hasDerivAt_id (t : ℂ)).mul_const (b - Complex.I / 2)).const_add (Complex.I / 2)).congr_deriv (by simp)
    have h := (hasDerivAt_logTcx (y := y) (hmem t ht)).comp (t : ℂ) hc
    exact h.comp_ofReal
  have hcont : ContinuousOn (fun t : ℝ => phiYDeriv y (cp t) * (b - Complex.I / 2)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    have hc : Continuous cp := by simp only [hcp]; fun_prop
    unfold phiYDeriv
    refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const (ContinuousOn.add ?_ ?_)) continuousOn_const
    · refine ContinuousOn.div continuousOn_const ?_ (fun t ht => sinh_w₁ (hmem t ht))
      exact (Complex.continuous_sinh.comp (by fun_prop)).continuousOn
    · refine ContinuousOn.div continuousOn_const ?_ (fun t ht => sinh_w₂ (hmem t ht))
      exact (Complex.continuous_sinh.comp (by fun_prop)).continuousOn
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)
  unfold phiY
  have h1 : cp 1 = b := by simp [hcp]
  have h0 : cp 0 = Complex.I / 2 := by simp [hcp]
  rw [show (fun t : ℝ => phiYDeriv y (Complex.I / 2 + (t : ℂ) * (b - Complex.I / 2)) * (b - Complex.I / 2)) =
    fun t : ℝ => phiYDeriv y (cp t) * (b - Complex.I / 2) from rfl, hFTC]
  simp only [h1, h0, Tcx_half, Complex.log_one, sub_zero]

/-! ### Uniform bounds on the band -/

lemma norm_sinh_ge {y : ℝ} {b : ℂ} (hb : |b.im - 1 / 2| < 1 / 4) :
    1 / 2 ≤ ‖Complex.sinh ((π : ℂ) * (b - y))‖ ∧ 1 / 2 ≤ ‖Complex.sinh ((π : ℂ) * (b + y))‖ ∧
    ‖Complex.cosh ((π : ℂ) * (b - y))‖ ≤ 2 * ‖Complex.sinh ((π : ℂ) * (b - y))‖ ∧
    ‖Complex.cosh ((π : ℂ) * (b + y))‖ ≤ 2 * ‖Complex.sinh ((π : ℂ) * (b + y))‖ := by
  have hpi := Real.pi_pos
  rw [abs_lt] at hb
  have hs : 1 / 2 ≤ Real.sin (π * b.im) :=
    sin_ge_half (by nlinarith [hb.1]) (by nlinarith [hb.2])
  have key : ∀ w : ℂ, w.im = π * b.im →
      1 / 2 ≤ ‖Complex.sinh w‖ ∧ ‖Complex.cosh w‖ ≤ 2 * ‖Complex.sinh w‖ := by
    intro w hw
    have h1 := norm_sinh_sq w
    have h2 := norm_cosh_sq w
    rw [hw] at h1 h2
    have hsin : 1 / 4 ≤ Real.sin (π * b.im) ^ 2 := by nlinarith
    have hcos : Real.cos (π * b.im) ^ 2 ≤ 1 := by nlinarith [Real.sin_sq_add_cos_sq (π * b.im)]
    have hn := norm_nonneg (Complex.sinh w)
    have hn2 := norm_nonneg (Complex.cosh w)
    constructor
    · nlinarith [sq_nonneg (Real.sinh w.re)]
    · nlinarith [sq_nonneg (Real.sinh w.re)]
  have e1 : ((π : ℂ) * (b - y)).im = π * b.im := by simp
  have e2 : ((π : ℂ) * (b + y)).im = π * b.im := by simp
  obtain ⟨a1, a2⟩ := key _ e1
  obtain ⟨c1, c2⟩ := key _ e2
  exact ⟨a1, c1, a2, c2⟩

lemma norm_phiYDeriv_le {y : ℝ} {b : ℂ} (hb : |b.im - 1 / 2| < 1 / 4) : ‖phiYDeriv y b‖ ≤ 4 * π := by
  obtain ⟨a1, a2, -, -⟩ := norm_sinh_ge (y := y) hb
  have hpi := Real.pi_pos
  unfold phiYDeriv
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  have h1 : ‖1 / Complex.sinh ((π : ℂ) * (b - y))‖ ≤ 2 := by
    rw [norm_div, norm_one, div_le_iff₀ (by linarith)]; linarith
  have h2 : ‖1 / Complex.sinh ((π : ℂ) * (b + y))‖ ≤ 2 := by
    rw [norm_div, norm_one, div_le_iff₀ (by linarith)]; linarith
  have := norm_add_le (1 / Complex.sinh ((π : ℂ) * (b - y))) (1 / Complex.sinh ((π : ℂ) * (b + y)))
  nlinarith

/-- `φ_y'' ` -/
noncomputable def phiYDeriv2 (y : ℝ) (b : ℂ) : ℂ :=
  -((π : ℂ) ^ 2) * (Complex.cosh ((π : ℂ) * (b - y)) / Complex.sinh ((π : ℂ) * (b - y)) ^ 2 +
    Complex.cosh ((π : ℂ) * (b + y)) / Complex.sinh ((π : ℂ) * (b + y)) ^ 2)

lemma hasDerivAt_phiYDeriv {y : ℝ} {b : ℂ} (hb : b ∈ imStrip) :
    HasDerivAt (phiYDeriv y) (phiYDeriv2 y b) b := by
  have hw1 : HasDerivAt (fun b : ℂ => Complex.sinh ((π : ℂ) * (b - y))) (Complex.cosh ((π : ℂ) * (b - y)) * (π : ℂ)) b := by
    have h := (((hasDerivAt_id b).sub_const (y : ℂ)).const_mul (π : ℂ))
    have := (Complex.hasDerivAt_sinh ((π : ℂ) * (b - y))).comp b h
    exact this.congr_deriv (by simp)
  have hw2 : HasDerivAt (fun b : ℂ => Complex.sinh ((π : ℂ) * (b + y))) (Complex.cosh ((π : ℂ) * (b + y)) * (π : ℂ)) b := by
    have h := (((hasDerivAt_id b).add_const (y : ℂ)).const_mul (π : ℂ))
    have := (Complex.hasDerivAt_sinh ((π : ℂ) * (b + y))).comp b h
    exact this.congr_deriv (by simp)
  have i1 := hw1.inv (sinh_w₁ (y := y) hb)
  have i2 := hw2.inv (sinh_w₂ (y := y) hb)
  have := ((i1.add i2).const_mul (π : ℂ))
  have e : phiYDeriv y = fun b => (π : ℂ) * ((Complex.sinh ((π : ℂ) * (b - y)))⁻¹ + (Complex.sinh ((π : ℂ) * (b + y)))⁻¹) := by
    funext b; unfold phiYDeriv; simp only [one_div]
  rw [e]
  refine this.congr_deriv ?_
  unfold phiYDeriv2
  have s1 := sinh_w₁ (y := y) hb
  have s2 := sinh_w₂ (y := y) hb
  field_simp
  ring

lemma norm_phiYDeriv2_le {y : ℝ} {b : ℂ} (hb : |b.im - 1 / 2| < 1 / 4) : ‖phiYDeriv2 y b‖ ≤ 8 * π ^ 2 := by
  obtain ⟨a1, a2, a3, a4⟩ := norm_sinh_ge (y := y) hb
  have hpi := Real.pi_pos
  have q : ∀ c s : ℂ, 1 / 2 ≤ ‖s‖ → ‖c‖ ≤ 2 * ‖s‖ → ‖c / s ^ 2‖ ≤ 4 := by
    intro c s h1 h2
    rw [norm_div, norm_pow, div_le_iff₀ (by positivity)]
    nlinarith
  unfold phiYDeriv2
  rw [norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  have := norm_add_le (Complex.cosh ((π : ℂ) * (b - y)) / Complex.sinh ((π : ℂ) * (b - y)) ^ 2)
    (Complex.cosh ((π : ℂ) * (b + y)) / Complex.sinh ((π : ℂ) * (b + y)) ^ 2)
  have h1 := q _ _ a1 a3
  have h2 := q _ _ a2 a4
  nlinarith [sq_nonneg π]

lemma norm_phiY_le {y : ℝ} {b : ℂ} (hb : |b.im - 1 / 2| < 1 / 4) : ‖phiY y b‖ ≤ 15 + π := by
  have hbs := band_sub_strip hb
  rw [phiY_eq hbs]
  have hpi := Real.pi_pos
  rw [abs_lt] at hb
  -- bounds for the two tanh factors
  have key : ∀ w : ℂ, w.im = π * b.im / 2 → 1 / 4 ≤ ‖Complex.tanh w‖ ∧ ‖Complex.tanh w‖ ≤ 4 := by
    intro w hw
    have hv1 : 1 / 4 ≤ Real.sin w.im := by
      have := Real.mul_le_sin (x := w.im) (by rw [hw]; nlinarith [hb.1]) (by rw [hw]; nlinarith [hb.2])
      rw [hw] at this ⊢
      have : 1 / 4 ≤ 2 / π * (π * b.im / 2) := by
        rw [show 2 / π * (π * b.im / 2) = b.im by field_simp]; linarith [hb.1]
      linarith
    have hv2 : 1 / 4 ≤ Real.cos w.im := by
      rw [← Real.sin_pi_div_two_sub]
      have := Real.mul_le_sin (x := π / 2 - w.im) (by rw [hw]; nlinarith [hb.2]) (by rw [hw]; nlinarith [hb.1])
      have : 1 / 4 ≤ 2 / π * (π / 2 - w.im) := by
        rw [hw, show 2 / π * (π / 2 - π * b.im / 2) = 1 - b.im by field_simp]; linarith [hb.2]
      linarith
    have hsq := Real.sin_sq_add_cos_sq w.im
    have h2 := norm_tanh_sq w
    set S := Real.sinh w.re ^ 2 with hS
    have hS0 : 0 ≤ S := sq_nonneg _
    have hp : 1 / 16 ≤ Real.sin w.im ^ 2 := by nlinarith
    have hq : 1 / 16 ≤ Real.cos w.im ^ 2 := by nlinarith
    have hd : 0 < S + Real.cos w.im ^ 2 := by linarith
    have hn := norm_nonneg (Complex.tanh w)
    have lo : 1 / 15 ≤ ‖Complex.tanh w‖ ^ 2 := by
      rw [h2, le_div_iff₀ hd]; nlinarith
    have hi : ‖Complex.tanh w‖ ^ 2 ≤ 15 := by
      rw [h2, div_le_iff₀ hd]; nlinarith
    constructor <;> nlinarith
  have e1 : ((π : ℂ) * (b - y) / 2).im = π * b.im / 2 := im_w₁ y b
  have e2 : ((π : ℂ) * (b + y) / 2).im = π * b.im / 2 := im_w₂ y b
  obtain ⟨l1, u1⟩ := key _ e1
  obtain ⟨l2, u2⟩ := key _ e2
  have hT : 1 / 16 ≤ ‖Tcx y b‖ ∧ ‖Tcx y b‖ ≤ 16 := by
    unfold Tcx
    rw [norm_mul]
    constructor <;> nlinarith
  have hn : ‖-(Tcx y b)‖ = ‖Tcx y b‖ := norm_neg _
  have hlog : |Real.log ‖-(Tcx y b)‖| ≤ 15 := by
    rw [hn]
    have hp : 0 < ‖Tcx y b‖ := by linarith [hT.1]
    rw [abs_le]
    constructor
    · have := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
      rw [Real.log_inv] at this
      have h3 : (‖Tcx y b‖)⁻¹ ≤ 16 := by
        rw [inv_le_comm₀ hp (by norm_num)]; linarith [hT.1]
      linarith
    · have := Real.log_le_sub_one_of_pos hp
      linarith [hT.2]
  have := Complex.abs_arg_le_pi (-(Tcx y b))
  calc ‖Complex.log (-(Tcx y b))‖
      = ‖((Real.log ‖-(Tcx y b)‖ : ℝ) : ℂ) + ((Complex.arg (-(Tcx y b)) : ℝ) : ℂ) * Complex.I‖ := rfl
    _ ≤ ‖((Real.log ‖-(Tcx y b)‖ : ℝ) : ℂ)‖ + ‖((Complex.arg (-(Tcx y b)) : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ ≤ 15 + π := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
      linarith

lemma re_phiY_half {y v : ℝ} : (phiY y ((v : ℂ) + Complex.I / 2)).re = 0 := by
  have hb : ((v : ℂ) + Complex.I / 2) ∈ imStrip := by
    simp [imStrip]; norm_num
  rw [phiY_eq hb, Complex.log_re]
  have e1 : ((π : ℂ) * (((v : ℂ) + Complex.I / 2) - y) / 2).im = π / 4 := by simp; ring
  have e2 : ((π : ℂ) * (((v : ℂ) + Complex.I / 2) + y) / 2).im = π / 4 := by simp; ring
  have : ‖-(Tcx y ((v : ℂ) + Complex.I / 2))‖ = 1 := by
    rw [norm_neg]; unfold Tcx
    rw [norm_mul, norm_tanh_eq_one e1, norm_tanh_eq_one e2, mul_one]
  rw [this, Real.log_one]

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
