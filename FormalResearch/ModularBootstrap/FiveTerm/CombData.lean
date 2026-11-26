module

public import FormalResearch.ModularBootstrap.FiveTerm.QFactor
public import FormalResearch.ModularBootstrap.FiveTerm.HalfDiscCauchyEdge
public import FormalResearch.ModularBootstrap.Constants
public import FormalResearch.ModularBootstrap.FiveTerm.StripOuterPoisson

/-!
# The Virasoro slit weight `W_slit` and edge kernel `K_edge` (FIVE-0 slice 3; `cts:Wslit`, `cts:Kedge`)

For `y ∈ (0,1)`, with `u₀ = (1 + 6y² + y⁴)/(1 - y²)²`:

* `x(y) = arcsinh(√u₀)/π` (`= arccosh(w)/π`, `w = √2 (1+y²)/(1-y²)`, `xOf`),
* `v_x(y) = arcsinh(√(u₀ - 1))/π` (`= (1/π) arcsinh(2√2 y/(1-y²))`, `vOf`),
* `W_slit(y) = √(x/ξ*) ((1 - e^{-4πx})/(1 - e^{-4πξ*}))² / ((1 - y²) √(1 + 6y² + y⁴))` (`Wslit`),
* `K_edge(y) = √(b_x/(x F'(v_x))) y³ e^{3iψ}`, `b_x = v_x + i/2`, `F'(v_x) = 2y/(1+y²)`, `e^{iψ} = wPt y`, principal
  square root (`Kedge`).

With `y = tanh(πτ/4)` one has `u₀ = cosh(πτ)`, `u₀ - 1 = 2 sinh²(πτ/2)`, `1 - y² = cosh(πτ/4)^{-2}`,
`1 + y² = cosh(πτ/2)/cosh(πτ/4)²` (`uSlit_tanh`, ...), which turns the data into hyperbolic functions of `τ`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- `x(y) = arccosh(√2 (1+y²)/(1-y²))/π = arcsinh(√u₀)/π`. -/
noncomputable def xOf (y : ℝ) : ℝ := Real.arsinh (√(uSlit y)) / π

/-- `v_x(y) = arcsinh(2√2 y/(1-y²))/π = arcsinh(√(u₀ - 1))/π`. -/
noncomputable def vOf (y : ℝ) : ℝ := Real.arsinh (√(uSlit y - 1)) / π

/-- The positive slit weight `W_slit(y)` of `cts:Wslit`. -/
noncomputable def Wslit (y : ℝ) : ℝ :=
  √(xOf y / xiStar) * ((1 - Real.exp (-(4 * π * xOf y))) / (1 - Real.exp (-(4 * π * xiStar)))) ^ 2 /
    ((1 - y ^ 2) * √(1 + 6 * y ^ 2 + y ^ 4))

/-- The complex edge-coupling kernel `K_edge(y)` of `cts:Kedge` (principal square root of `b_x/(x F'(v_x))`). -/
noncomputable def Kedge (y : ℝ) : ℂ :=
  ((((vOf y : ℝ) : ℂ) + Complex.I / 2) / ((xOf y * (2 * y / (1 + y ^ 2)) : ℝ) : ℂ)) ^ (1 / 2 : ℂ) *
    (y : ℂ) ^ 3 * (wPt y) ^ 3

/-! ### `y = tanh(πτ/4)` -/

lemma cosh_two_mul_aux (x : ℝ) : Real.cosh (2 * x) = 2 * Real.cosh x ^ 2 - 1 := by
  rw [Real.cosh_two_mul]; nlinarith [Real.cosh_sq x]

lemma tanh_sq_lt_one (θ : ℝ) : Real.tanh θ ^ 2 < 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, div_pow, div_lt_one (by positivity)]
  nlinarith [Real.cosh_sq θ]

lemma one_sub_tanh_sq (θ : ℝ) : 1 - Real.tanh θ ^ 2 = 1 / Real.cosh θ ^ 2 := by
  have hc : 0 < Real.cosh θ := Real.cosh_pos θ
  rw [Real.tanh_eq_sinh_div_cosh, div_pow]
  field_simp
  linarith [Real.cosh_sq θ]

lemma one_add_tanh_sq (θ : ℝ) : 1 + Real.tanh θ ^ 2 = Real.cosh (2 * θ) / Real.cosh θ ^ 2 := by
  have hc : 0 < Real.cosh θ := Real.cosh_pos θ
  rw [Real.tanh_eq_sinh_div_cosh, div_pow, Real.cosh_two_mul]
  field_simp

lemma uSlit_tanh (θ : ℝ) : uSlit (Real.tanh θ) = Real.cosh (4 * θ) := by
  have hc : 0 < Real.cosh θ := Real.cosh_pos θ
  have h4 : Real.cosh (4 * θ) = 8 * Real.cosh θ ^ 4 - 8 * Real.cosh θ ^ 2 + 1 := by
    have : 4 * θ = 2 * (2 * θ) := by ring
    rw [this, cosh_two_mul_aux, cosh_two_mul_aux]
    ring
  unfold uSlit
  rw [h4, Real.tanh_eq_sinh_div_cosh]
  have hs : Real.sinh θ ^ 2 = Real.cosh θ ^ 2 - 1 := by nlinarith [Real.cosh_sq θ]
  have hs4 : Real.sinh θ ^ 4 = (Real.cosh θ ^ 2 - 1) ^ 2 := by rw [← hs]; ring
  field_simp
  have : (Real.cosh θ ^ 2 - Real.sinh θ ^ 2) = 1 := by rw [hs]; ring
  rw [this]
  nlinarith [hs, hs4]

lemma uSlit_tanh_sub_one (θ : ℝ) : uSlit (Real.tanh θ) - 1 = 2 * Real.sinh (2 * θ) ^ 2 := by
  rw [uSlit_tanh]
  have : 4 * θ = 2 * (2 * θ) := by ring
  rw [this, cosh_two_mul_aux]
  nlinarith [Real.cosh_sq (2 * θ)]

/-! ### The hyperbolic form of the data -/

/-- `x` as a function of `τ` (`y = tanh(πτ/4)`): `arsinh(√cosh(πτ))/π`. -/
noncomputable def xT (t : ℝ) : ℝ := Real.arsinh (√(Real.cosh (π * t))) / π

/-- `v_x` as a function of `τ`: `arsinh(√2 sinh(πτ/2))/π` (odd in `τ`). -/
noncomputable def vT (t : ℝ) : ℝ := Real.arsinh (√2 * Real.sinh (π * t / 2)) / π

/-- `|b_x| = √(v_x² + 1/4)`. -/
noncomputable def bT (t : ℝ) : ℝ := √(vT t ^ 2 + 1 / 4)

/-- `Λ = (1 - e^{-4πx})/(1 - e^{-4πξ*})`. -/
noncomputable def lamT (t : ℝ) : ℝ :=
  (1 - Real.exp (-(4 * π * xT t))) / (1 - Real.exp (-(4 * π * xiStar)))

/-- The amplitude `a(τ) = log W_slit + ¾ log(1+y²) + ¼ log(|b_x|/x)` of the symmetric part of `log G_outer`,
written in hyperbolic form (`aAmp_eq` below). -/
noncomputable def aAmp (t : ℝ) : ℝ :=
  (1 / 4) * Real.log (xT t) + (1 / 4) * Real.log (bT t) - (1 / 2) * Real.log xiStar +
    2 * Real.log (lamT t) + (5 / 2) * Real.log (Real.cosh (π * t / 4)) +
    (3 / 4) * Real.log (Real.cosh (π * t / 2)) - (1 / 2) * Real.log (Real.cosh (π * t))

lemma arsinh_one_pos : 0 < Real.arsinh 1 := Real.arsinh_pos_iff.mpr one_pos

lemma one_le_sqrt_cosh (t : ℝ) : 1 ≤ √(Real.cosh (π * t)) := by
  rw [show (1 : ℝ) = √1 by simp]
  exact Real.sqrt_le_sqrt (Real.one_le_cosh _)

lemma xiStar_le_xT (t : ℝ) : xiStar ≤ xT t := by
  unfold xT xiStar
  exact div_le_div_of_nonneg_right (Real.arsinh_le_arsinh.mpr (one_le_sqrt_cosh t)) Real.pi_pos.le

lemma xT_pos (t : ℝ) : 0 < xT t := lt_of_lt_of_le xiStar_pos (xiStar_le_xT t)

lemma one_le_lamT (t : ℝ) : 1 ≤ lamT t := by
  unfold lamT
  have hd : 0 < 1 - Real.exp (-(4 * π * xiStar)) := by
    rw [sub_pos, ← Real.exp_zero]; apply Real.exp_lt_exp.mpr; have := xiStar_pos; have := Real.pi_pos; nlinarith
  rw [le_div_iff₀ hd]
  have : Real.exp (-(4 * π * xT t)) ≤ Real.exp (-(4 * π * xiStar)) := by
    apply Real.exp_le_exp.mpr
    have := xiStar_le_xT t; have := Real.pi_pos; nlinarith
  linarith

lemma lamT_pos (t : ℝ) : 0 < lamT t := lt_of_lt_of_le one_pos (one_le_lamT t)

lemma lamT_le (t : ℝ) : lamT t ≤ 1 / (1 - Real.exp (-(4 * π * xiStar))) := by
  unfold lamT
  have hd : 0 < 1 - Real.exp (-(4 * π * xiStar)) := by
    rw [sub_pos, ← Real.exp_zero]; apply Real.exp_lt_exp.mpr; have := xiStar_pos; have := Real.pi_pos; nlinarith
  apply div_le_div_of_nonneg_right _ hd.le
  have := Real.exp_pos (-(4 * π * xT t))
  linarith

lemma bT_ge (t : ℝ) : 1 / 2 ≤ bT t := by
  unfold bT
  rw [show (1 / 2 : ℝ) = √((1 / 2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (vT t)])

lemma bT_pos (t : ℝ) : 0 < bT t := lt_of_lt_of_le (by norm_num) (bT_ge t)

lemma xT_even (t : ℝ) : xT (-t) = xT t := by
  unfold xT; rw [mul_neg, Real.cosh_neg]

lemma vT_odd (t : ℝ) : vT (-t) = -vT t := by
  unfold vT
  have : π * (-t) / 2 = -(π * t / 2) := by ring
  rw [this, Real.sinh_neg, mul_neg, Real.arsinh_neg, neg_div]

lemma bT_even (t : ℝ) : bT (-t) = bT t := by
  unfold bT; rw [vT_odd]; ring_nf

lemma aAmp_even (t : ℝ) : aAmp (-t) = aAmp t := by
  unfold aAmp lamT
  rw [xT_even, bT_even]
  have h1 : π * (-t) / 4 = -(π * t / 4) := by ring
  have h2 : π * (-t) / 2 = -(π * t / 2) := by ring
  have h3 : π * (-t) = -(π * t) := by ring
  rw [h1, h2, h3, Real.cosh_neg, Real.cosh_neg, Real.cosh_neg]

lemma continuous_xT : Continuous xT := by
  unfold xT
  refine (Real.continuous_arsinh.comp (Real.continuous_sqrt.comp ?_)).div_const _
  exact Real.continuous_cosh.comp (by fun_prop)

lemma continuous_vT : Continuous vT := by
  unfold vT
  refine (Real.continuous_arsinh.comp ?_).div_const _
  exact continuous_const.mul (Real.continuous_sinh.comp (by fun_prop))

lemma continuous_bT : Continuous bT := by
  unfold bT
  exact Real.continuous_sqrt.comp ((continuous_vT.pow 2).add continuous_const)

lemma continuous_lamT : Continuous lamT := by
  unfold lamT
  exact (continuous_const.sub (Real.continuous_exp.comp (continuous_xT.const_mul _ |>.neg))).div_const _

lemma continuous_aAmp : Continuous aAmp := by
  unfold aAmp
  have hc : ∀ c : ℝ, Continuous fun t : ℝ => Real.cosh (π * t / c) :=
    fun c => Real.continuous_cosh.comp (by fun_prop)
  refine ((((((continuous_const.mul (continuous_xT.log (fun t => (xT_pos t).ne'))).add
    (continuous_const.mul (continuous_bT.log (fun t => (bT_pos t).ne')))).sub continuous_const).add
    (continuous_const.mul (continuous_lamT.log (fun t => (lamT_pos t).ne')))).add
    (continuous_const.mul ((hc 4).log (fun t => (Real.cosh_pos _).ne')))).add
    (continuous_const.mul ((hc 2).log (fun t => (Real.cosh_pos _).ne')))).sub
    (continuous_const.mul ?_)
  have := (Real.continuous_cosh.comp (continuous_const.mul continuous_id : Continuous fun t : ℝ => π * t)).log
    (fun t => (Real.cosh_pos _).ne')
  exact this

/-- On the slit: `x(tanh(πτ/4)) = xT τ`. -/
lemma xOf_tanh (τ : ℝ) : xOf (Real.tanh (π * τ / 4)) = xT τ := by
  unfold xOf xT
  rw [uSlit_tanh]
  congr 3
  ring_nf

/-- On the slit: `v_x(tanh(πτ/4)) = vT τ` (`τ ≥ 0`). -/
lemma vOf_tanh {τ : ℝ} (hτ : 0 ≤ τ) : vOf (Real.tanh (π * τ / 4)) = vT τ := by
  unfold vOf vT
  rw [uSlit_tanh_sub_one]
  have hs : 0 ≤ Real.sinh (2 * (π * τ / 4)) := Real.sinh_nonneg_iff.mpr (by positivity)
  have : √(2 * Real.sinh (2 * (π * τ / 4)) ^ 2) = √2 * Real.sinh (π * τ / 2) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hs]
    congr 2; ring_nf
  rw [this]

/-! ### Growth of the amplitude -/

lemma cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

lemma exp_abs_div_two_le_cosh (x : ℝ) : Real.exp |x| / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; have := Real.exp_pos (-x); linarith
  · rw [h]; have := Real.exp_pos x; linarith

lemma log_cosh_le (x : ℝ) : Real.log (Real.cosh x) ≤ |x| := by
  calc Real.log (Real.cosh x) ≤ Real.log (Real.exp |x|) :=
        Real.log_le_log (Real.cosh_pos x) (cosh_le_exp_abs x)
    _ = |x| := Real.log_exp _

lemma le_log_cosh (x : ℝ) : |x| - Real.log 2 ≤ Real.log (Real.cosh x) := by
  have h := Real.log_le_log (by positivity) (exp_abs_div_two_le_cosh x)
  rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at h
  exact h

lemma arsinh_le_of_le_exp {w y : ℝ} (hw : 0 ≤ w) (hy : 0 ≤ y) (h : w ≤ Real.exp y) :
    Real.arsinh w ≤ Real.log 3 + y := by
  have h1 : Real.arsinh w ≤ Real.log (1 + 2 * w) := by
    unfold Real.arsinh
    apply Real.log_le_log (by positivity)
    have : √(1 + w ^ 2) ≤ 1 + w := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith
    linarith
  have hey : 1 ≤ Real.exp y := Real.one_le_exp hy
  have h2 : 1 + 2 * w ≤ 3 * Real.exp y := by linarith
  calc Real.arsinh w ≤ Real.log (1 + 2 * w) := h1
    _ ≤ Real.log (3 * Real.exp y) := Real.log_le_log (by positivity) h2
    _ = Real.log 3 + y := by rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]

lemma sqrt_cosh_le (t : ℝ) : √(Real.cosh (π * t)) ≤ Real.exp (π * |t| / 2) := by
  rw [Real.sqrt_le_left (Real.exp_pos _).le]
  have h := cosh_le_exp_abs (π * t)
  rw [abs_mul, abs_of_pos Real.pi_pos] at h
  have : Real.exp (π * |t| / 2) ^ 2 = Real.exp (π * |t|) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [this]; exact h

lemma xT_le (t : ℝ) : xT t ≤ Real.log 3 / π + |t| / 2 := by
  unfold xT
  have h := arsinh_le_of_le_exp (Real.sqrt_nonneg _) (by positivity) (sqrt_cosh_le t)
  have hpi := Real.pi_pos
  rw [div_le_iff₀ hpi]
  have : (Real.log 3 / π + |t| / 2) * π = Real.log 3 + π * |t| / 2 := by field_simp
  rw [this]; exact h

lemma abs_vT_le (t : ℝ) : |vT t| ≤ Real.log 3 / π + |t| / 2 := by
  have hpi := Real.pi_pos
  have key : ∀ s : ℝ, 0 ≤ s → |vT s| ≤ Real.log 3 / π + |s| / 2 := by
    intro s hs
    unfold vT
    have hsh : 0 ≤ √2 * Real.sinh (π * s / 2) := by
      have : 0 ≤ Real.sinh (π * s / 2) := Real.sinh_nonneg_iff.mpr (by positivity)
      positivity
    rw [abs_of_nonneg (div_nonneg (Real.arsinh_nonneg_iff.mpr hsh) hpi.le), div_le_iff₀ hpi]
    have h := arsinh_le_of_le_exp hsh (by positivity : 0 ≤ π * |s| / 2) (by
      have e1 : Real.sinh (π * s / 2) ≤ Real.exp (π * |s| / 2) / 2 := by
        rw [Real.sinh_eq, abs_of_nonneg hs]
        have := Real.exp_pos (-(π * s / 2)); linarith
      have h2 : √2 ≤ 2 := by
        rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num)
      have := Real.exp_pos (π * |s| / 2)
      have hs0 : 0 ≤ Real.sinh (π * s / 2) := Real.sinh_nonneg_iff.mpr (by positivity)
      calc √2 * Real.sinh (π * s / 2) ≤ 2 * (Real.exp (π * |s| / 2) / 2) :=
            mul_le_mul h2 e1 hs0 (by norm_num)
        _ = Real.exp (π * |s| / 2) := by ring)
    have : (Real.log 3 / π + |s| / 2) * π = Real.log 3 + π * |s| / 2 := by field_simp
    rw [this]; exact h
  rcases le_total 0 t with ht | ht
  · exact key t ht
  · have := key (-t) (by linarith)
    rwa [vT_odd, abs_neg, abs_neg] at this

lemma bT_le (t : ℝ) : bT t ≤ Real.log 3 / π + |t| / 2 + 1 / 2 := by
  unfold bT
  have h := abs_vT_le t
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_abs (vT t), abs_nonneg (vT t)]

lemma log_le_self_pos {x : ℝ} (hx : 0 < x) : Real.log x ≤ x := by
  have := Real.log_le_sub_one_of_pos hx
  linarith

lemma aAmp_ge (t : ℝ) : -(1 / 4) * Real.log xiStar - (7 / 2) * Real.log 2 ≤ aAmp t := by
  unfold aAmp
  have hxi := xiStar_pos
  have h1 : Real.log xiStar ≤ Real.log (xT t) := Real.log_le_log hxi (xiStar_le_xT t)
  have h2 : Real.log (1 / 2) ≤ Real.log (bT t) := Real.log_le_log (by norm_num) (bT_ge t)
  have h2' : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have h4 : 0 ≤ Real.log (lamT t) := Real.log_nonneg (one_le_lamT t)
  have h5 := le_log_cosh (π * t / 4)
  have h6 := le_log_cosh (π * t / 2)
  have h7 := log_cosh_le (π * t)
  have hpi := Real.pi_pos
  have e5 : |π * t / 4| = π * |t| / 4 := by rw [abs_div, abs_mul, abs_of_pos hpi]; norm_num
  have e6 : |π * t / 2| = π * |t| / 2 := by rw [abs_div, abs_mul, abs_of_pos hpi]; norm_num
  have e7 : |π * t| = π * |t| := by rw [abs_mul, abs_of_pos hpi]
  rw [e5] at h5; rw [e6] at h6; rw [e7] at h7
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [abs_nonneg t]

lemma aAmp_le (t : ℝ) : aAmp t ≤ (5 * π / 8) * |t| +
    (Real.log 3 / (2 * π) + 1 / 8 - (1 / 2) * Real.log xiStar -
      2 * Real.log (1 - Real.exp (-(4 * π * xiStar))) + (1 / 2) * Real.log 2) := by
  unfold aAmp
  have hxi := xiStar_pos
  have hpi := Real.pi_pos
  have h1 : Real.log (xT t) ≤ xT t := log_le_self_pos (xT_pos t)
  have h2 : Real.log (bT t) ≤ bT t := log_le_self_pos (bT_pos t)
  have h1' := xT_le t
  have h2' := bT_le t
  have h4 : Real.log (lamT t) ≤ Real.log (1 / (1 - Real.exp (-(4 * π * xiStar)))) :=
    Real.log_le_log (lamT_pos t) (lamT_le t)
  have hd : 0 < 1 - Real.exp (-(4 * π * xiStar)) := by
    rw [sub_pos, ← Real.exp_zero]; apply Real.exp_lt_exp.mpr; nlinarith
  have h4' : Real.log (1 / (1 - Real.exp (-(4 * π * xiStar)))) =
      -Real.log (1 - Real.exp (-(4 * π * xiStar))) := by rw [one_div, Real.log_inv]
  have h5 := log_cosh_le (π * t / 4)
  have h6 := log_cosh_le (π * t / 2)
  have h7 := le_log_cosh (π * t)
  have e5 : |π * t / 4| = π * |t| / 4 := by rw [abs_div, abs_mul, abs_of_pos hpi]; norm_num
  have e6 : |π * t / 2| = π * |t| / 2 := by rw [abs_div, abs_mul, abs_of_pos hpi]; norm_num
  have e7 : |π * t| = π * |t| := by rw [abs_mul, abs_of_pos hpi]
  rw [e5] at h5; rw [e6] at h6; rw [e7] at h7
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi2 : 2 < π := by linarith [Real.pi_gt_three]
  have hq : Real.log 3 / π = Real.log 3 / (2 * π) * 2 := by field_simp
  nlinarith [abs_nonneg t, mul_nonneg (abs_nonneg t) (by linarith : (0 : ℝ) ≤ π - 2)]

lemma exists_aAmp_bounds : (∃ m : ℝ, ∀ t, m ≤ aAmp t) ∧
    ∃ β : ℝ, ∀ t, aAmp t ≤ (5 * π / 8) * |t| + β :=
  ⟨⟨_, aAmp_ge⟩, ⟨_, aAmp_le⟩⟩

lemma expBdd_aAmp : ExpBdd aAmp := by
  obtain ⟨⟨m, hm⟩, ⟨β, hβ⟩⟩ := exists_aAmp_bounds
  refine ⟨|m| + (5 * π / 8) + |β|, fun t => ?_⟩
  have h1 : |t| ≤ Real.exp |t| := by
    have := Real.add_one_le_exp |t|; linarith
  have h2 : 1 ≤ Real.exp |t| := Real.one_le_exp (abs_nonneg t)
  have hpi := Real.pi_pos
  have hup : aAmp t ≤ (|m| + 5 * π / 8 + |β|) * Real.exp |t| := by
    have := hβ t
    nlinarith [le_abs_self β, abs_nonneg m, abs_nonneg t, mul_nonneg (abs_nonneg m) (by linarith : 0 ≤ Real.exp |t| - 1),
      mul_nonneg (abs_nonneg β) (by linarith : 0 ≤ Real.exp |t| - 1),
      mul_nonneg (by positivity : 0 ≤ 5 * π / 8) (by linarith : 0 ≤ Real.exp |t| - |t|)]
  have hlo : -((|m| + 5 * π / 8 + |β|) * Real.exp |t|) ≤ aAmp t := by
    have := hm t
    nlinarith [neg_abs_le m, abs_nonneg m, abs_nonneg β, mul_nonneg (abs_nonneg m) (by linarith : 0 ≤ Real.exp |t| - 1),
      mul_nonneg (by positivity : 0 ≤ 5 * π / 8) (by linarith : 0 ≤ Real.exp |t|),
      mul_nonneg (abs_nonneg β) (by linarith : 0 ≤ Real.exp |t|)]
  exact abs_le.mpr ⟨hlo, hup⟩

end FormalResearch.ModularBootstrap.FiveTerm
