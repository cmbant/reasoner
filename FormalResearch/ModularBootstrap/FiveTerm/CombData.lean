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

/-! ### Log forms and the holomorphic extension of the amplitude -/

lemma one_add_cosh_eq (t : ℝ) : 1 + Real.cosh (π * t) = 2 * Real.cosh (π * t / 2) ^ 2 := by
  have : π * t = 2 * (π * t / 2) := by ring
  rw [this, cosh_two_mul_aux]; ring_nf

lemma cosh_eq_one_add_two_sinh_sq (t : ℝ) : Real.cosh (π * t) = 1 + 2 * Real.sinh (π * t / 2) ^ 2 := by
  have h := one_add_cosh_eq t
  nlinarith [Real.cosh_sq (π * t / 2)]

lemma xT_eq_log (t : ℝ) :
    xT t = Real.log (√(Real.cosh (π * t)) + √2 * Real.cosh (π * t / 2)) / π := by
  unfold xT Real.arsinh
  have h1 : 1 + √(Real.cosh (π * t)) ^ 2 = 2 * Real.cosh (π * t / 2) ^ 2 := by
    rw [Real.sq_sqrt (Real.cosh_pos _).le]; exact one_add_cosh_eq t
  rw [h1, Real.sqrt_mul (by norm_num), Real.sqrt_sq (Real.cosh_pos _).le]

lemma vT_eq_log (t : ℝ) :
    vT t = Real.log (√(Real.cosh (π * t)) + √2 * Real.sinh (π * t / 2)) / π := by
  unfold vT Real.arsinh
  have h1 : 1 + (√2 * Real.sinh (π * t / 2)) ^ 2 = Real.cosh (π * t) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]; linarith [cosh_eq_one_add_two_sinh_sq t]
  rw [h1, add_comm]

/-- `R(ζ) = cosh(πζ)^{1/2}`. -/
noncomputable def RC (ζ : ℂ) : ℂ := (Complex.cosh ((π : ℂ) * ζ)) ^ (1 / 2 : ℂ)

noncomputable def xC (ζ : ℂ) : ℂ :=
  Complex.log (RC ζ + (√2 : ℂ) * Complex.cosh ((π : ℂ) * ζ / 2)) / (π : ℂ)

noncomputable def vC (ζ : ℂ) : ℂ :=
  Complex.log (RC ζ + (√2 : ℂ) * Complex.sinh ((π : ℂ) * ζ / 2)) / (π : ℂ)

noncomputable def bC (ζ : ℂ) : ℂ := (vC ζ ^ 2 + 1 / 4) ^ (1 / 2 : ℂ)

noncomputable def lamC (ζ : ℂ) : ℂ :=
  (1 - Complex.exp (-(4 * (π : ℂ) * xC ζ))) / (1 - Complex.exp (-(4 * (π : ℂ) * (xiStar : ℂ))))

noncomputable def aC (ζ : ℂ) : ℂ :=
  (1 / 4) * Complex.log (xC ζ) + (1 / 4) * Complex.log (bC ζ) - (1 / 2) * (Real.log xiStar : ℂ) +
    2 * Complex.log (lamC ζ) + (5 / 2) * Complex.log (Complex.cosh ((π : ℂ) * ζ / 4)) +
    (3 / 4) * Complex.log (Complex.cosh ((π : ℂ) * ζ / 2)) - (1 / 2) * Complex.log (Complex.cosh ((π : ℂ) * ζ))

lemma RC_ofReal (t : ℝ) : RC (t : ℂ) = ((√(Real.cosh (π * t)) : ℝ) : ℂ) := by
  unfold RC
  have e : Complex.cosh ((π : ℂ) * (t : ℂ)) = ((Real.cosh (π * t) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cosh]; push_cast; rfl
  rw [e]
  have h := Complex.ofReal_cpow (Real.cosh_pos (π * t)).le (1 / 2 : ℝ)
  rw [show (((1 / 2 : ℝ)) : ℂ) = (1 / 2 : ℂ) by push_cast; ring] at h
  rw [← h, ← Real.sqrt_eq_rpow]

lemma cosh_ofReal' (t : ℝ) (c : ℝ) : Complex.cosh ((π : ℂ) * (t : ℂ) / c) = ((Real.cosh (π * t / c) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cosh]; push_cast; rfl

lemma sinh_ofReal' (t : ℝ) (c : ℝ) : Complex.sinh ((π : ℂ) * (t : ℂ) / c) = ((Real.sinh (π * t / c) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sinh]; push_cast; rfl

lemma xC_ofReal (t : ℝ) : xC (t : ℂ) = ((xT t : ℝ) : ℂ) := by
  unfold xC
  rw [RC_ofReal, xT_eq_log]
  have h2 : Complex.cosh ((π : ℂ) * (t : ℂ) / 2) = ((Real.cosh (π * t / 2) : ℝ) : ℂ) := by
    simp
  rw [h2]
  have hpos : 0 < √(Real.cosh (π * t)) + √2 * Real.cosh (π * t / 2) := by
    have := Real.sqrt_pos.mpr (Real.cosh_pos (π * t))
    have := Real.cosh_pos (π * t / 2)
    positivity
  have : ((√(Real.cosh (π * t)) : ℝ) : ℂ) + (√2 : ℂ) * ((Real.cosh (π * t / 2) : ℝ) : ℂ) =
      ((√(Real.cosh (π * t)) + √2 * Real.cosh (π * t / 2) : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_log hpos.le]
  push_cast; rfl

lemma vC_ofReal (t : ℝ) : vC (t : ℂ) = ((vT t : ℝ) : ℂ) := by
  unfold vC
  rw [RC_ofReal, vT_eq_log]
  have h2 : Complex.sinh ((π : ℂ) * (t : ℂ) / 2) = ((Real.sinh (π * t / 2) : ℝ) : ℂ) := by
    simp
  rw [h2]
  have hpos : 0 < √(Real.cosh (π * t)) + √2 * Real.sinh (π * t / 2) := by
    have hR : 0 < √(Real.cosh (π * t)) := Real.sqrt_pos.mpr (Real.cosh_pos (π * t))
    have hlt : (√2 * Real.sinh (π * t / 2)) ^ 2 < √(Real.cosh (π * t)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (Real.cosh_pos _).le]
      nlinarith [cosh_eq_one_add_two_sinh_sq t]
    have := abs_lt_of_sq_lt_sq hlt hR.le
    linarith [(abs_lt.mp this).1]
  have : ((√(Real.cosh (π * t)) : ℝ) : ℂ) + (√2 : ℂ) * ((Real.sinh (π * t / 2) : ℝ) : ℂ) =
      ((√(Real.cosh (π * t)) + √2 * Real.sinh (π * t / 2) : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_log hpos.le]
  push_cast; rfl

lemma bC_ofReal (t : ℝ) : bC (t : ℂ) = ((bT t : ℝ) : ℂ) := by
  unfold bC bT
  rw [vC_ofReal]
  have h := Complex.ofReal_cpow (show 0 ≤ vT t ^ 2 + 1 / 4 by positivity) (1 / 2 : ℝ)
  rw [show (((1 / 2 : ℝ)) : ℂ) = (1 / 2 : ℂ) by push_cast; ring] at h
  have e : ((vT t : ℝ) : ℂ) ^ 2 + 1 / 4 = ((vT t ^ 2 + 1 / 4 : ℝ) : ℂ) := by push_cast; ring
  rw [e, ← h, ← Real.sqrt_eq_rpow]

lemma lamC_ofReal (t : ℝ) : lamC (t : ℂ) = ((lamT t : ℝ) : ℂ) := by
  unfold lamC lamT
  rw [xC_ofReal]
  push_cast
  rfl

lemma aC_ofReal (t : ℝ) : aC (t : ℂ) = ((aAmp t : ℝ) : ℂ) := by
  unfold aC aAmp
  rw [xC_ofReal, bC_ofReal, lamC_ofReal]
  have h4 : Complex.cosh ((π : ℂ) * (t : ℂ) / 4) = ((Real.cosh (π * t / 4) : ℝ) : ℂ) := by
    simp
  have h2 : Complex.cosh ((π : ℂ) * (t : ℂ) / 2) = ((Real.cosh (π * t / 2) : ℝ) : ℂ) := by
    simp
  have h1 : Complex.cosh ((π : ℂ) * (t : ℂ)) = ((Real.cosh (π * t) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cosh]; push_cast; rfl
  rw [h4, h2, h1]
  rw [← Complex.ofReal_log (xT_pos t).le, ← Complex.ofReal_log (bT_pos t).le,
    ← Complex.ofReal_log (lamT_pos t).le, ← Complex.ofReal_log (Real.cosh_pos _).le,
    ← Complex.ofReal_log (Real.cosh_pos _).le, ← Complex.ofReal_log (Real.cosh_pos _).le]
  push_cast
  ring

/-- All the slit-plane conditions making `aC` holomorphic at `ζ`. -/
structure GoodAt (ζ : ℂ) : Prop where
  c1 : Complex.cosh ((π : ℂ) * ζ) ∈ Complex.slitPlane
  c2 : RC ζ + (√2 : ℂ) * Complex.cosh ((π : ℂ) * ζ / 2) ∈ Complex.slitPlane
  c3 : RC ζ + (√2 : ℂ) * Complex.sinh ((π : ℂ) * ζ / 2) ∈ Complex.slitPlane
  c4 : vC ζ ^ 2 + 1 / 4 ∈ Complex.slitPlane
  c5 : xC ζ ∈ Complex.slitPlane
  c6 : bC ζ ∈ Complex.slitPlane
  c7 : lamC ζ ∈ Complex.slitPlane
  c8 : Complex.cosh ((π : ℂ) * ζ / 4) ∈ Complex.slitPlane
  c9 : Complex.cosh ((π : ℂ) * ζ / 2) ∈ Complex.slitPlane

lemma GoodAt.diff_RC {ζ : ℂ} (h : GoodAt ζ) : DifferentiableAt ℂ RC ζ := by
  unfold RC
  exact DifferentiableAt.cpow_const (by fun_prop) h.c1

lemma GoodAt.diff_xC {ζ : ℂ} (h : GoodAt ζ) : DifferentiableAt ℂ xC ζ := by
  unfold xC
  have h1 := h.diff_RC
  have hin : DifferentiableAt ℂ (fun ζ => RC ζ + (√2 : ℂ) * Complex.cosh ((π : ℂ) * ζ / 2)) ζ :=
    h1.add (by fun_prop)
  exact (hin.clog h.c2).div_const _

lemma GoodAt.diff_vC {ζ : ℂ} (h : GoodAt ζ) : DifferentiableAt ℂ vC ζ := by
  unfold vC
  have h1 := h.diff_RC
  have hin : DifferentiableAt ℂ (fun ζ => RC ζ + (√2 : ℂ) * Complex.sinh ((π : ℂ) * ζ / 2)) ζ :=
    h1.add (by fun_prop)
  exact (hin.clog h.c3).div_const _

lemma GoodAt.diff_bC {ζ : ℂ} (h : GoodAt ζ) : DifferentiableAt ℂ bC ζ := by
  unfold bC
  have h1 := h.diff_vC
  exact DifferentiableAt.cpow_const (by fun_prop) h.c4

lemma GoodAt.diff_lamC {ζ : ℂ} (h : GoodAt ζ) : DifferentiableAt ℂ lamC ζ := by
  unfold lamC
  have h1 := h.diff_xC
  exact (by fun_prop : DifferentiableAt ℂ (fun ζ => 1 - Complex.exp (-(4 * (π : ℂ) * xC ζ))) ζ).div_const _

lemma GoodAt.diff_aC {ζ : ℂ} (h : GoodAt ζ) : DifferentiableAt ℂ aC ζ := by
  unfold aC
  have h1 := h.diff_xC
  have h2 := h.diff_bC
  have h3 := h.diff_lamC
  have e1 : DifferentiableAt ℂ (fun ζ => Complex.log (xC ζ)) ζ := h1.clog h.c5
  have e2 : DifferentiableAt ℂ (fun ζ => Complex.log (bC ζ)) ζ := h2.clog h.c6
  have e3 : DifferentiableAt ℂ (fun ζ => Complex.log (lamC ζ)) ζ := h3.clog h.c7
  have e4 : DifferentiableAt ℂ (fun ζ => Complex.log (Complex.cosh ((π : ℂ) * ζ / 4))) ζ :=
    DifferentiableAt.clog (by fun_prop) h.c8
  have e5 : DifferentiableAt ℂ (fun ζ => Complex.log (Complex.cosh ((π : ℂ) * ζ / 2))) ζ :=
    DifferentiableAt.clog (by fun_prop) h.c9
  have e6 : DifferentiableAt ℂ (fun ζ => Complex.log (Complex.cosh ((π : ℂ) * ζ))) ζ :=
    DifferentiableAt.clog (by fun_prop) h.c1
  fun_prop

lemma ofReal_pos_mem_slit {r : ℝ} (hr : 0 < r) : ((r : ℝ) : ℂ) ∈ Complex.slitPlane :=
  Complex.ofReal_mem_slitPlane.2 hr

lemma goodAt_ofReal (t : ℝ) : GoodAt (t : ℂ) := by
  have h1 : Complex.cosh ((π : ℂ) * (t : ℂ)) = ((Real.cosh (π * t) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cosh]; push_cast; rfl
  have h2 : Complex.cosh ((π : ℂ) * (t : ℂ) / 2) = ((Real.cosh (π * t / 2) : ℝ) : ℂ) := by simp
  have h4 : Complex.cosh ((π : ℂ) * (t : ℂ) / 4) = ((Real.cosh (π * t / 4) : ℝ) : ℂ) := by simp
  have hs2 : Complex.sinh ((π : ℂ) * (t : ℂ) / 2) = ((Real.sinh (π * t / 2) : ℝ) : ℂ) := by simp
  have hR : 0 < √(Real.cosh (π * t)) := Real.sqrt_pos.mpr (Real.cosh_pos _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1]; exact ofReal_pos_mem_slit (Real.cosh_pos _)
  · rw [RC_ofReal, h2]
    have : ((√(Real.cosh (π * t)) : ℝ) : ℂ) + (√2 : ℂ) * ((Real.cosh (π * t / 2) : ℝ) : ℂ) =
        ((√(Real.cosh (π * t)) + √2 * Real.cosh (π * t / 2) : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    exact ofReal_pos_mem_slit (by have := Real.cosh_pos (π * t / 2); positivity)
  · rw [RC_ofReal, hs2]
    have : ((√(Real.cosh (π * t)) : ℝ) : ℂ) + (√2 : ℂ) * ((Real.sinh (π * t / 2) : ℝ) : ℂ) =
        ((√(Real.cosh (π * t)) + √2 * Real.sinh (π * t / 2) : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    refine ofReal_pos_mem_slit ?_
    have hlt : (√2 * Real.sinh (π * t / 2)) ^ 2 < √(Real.cosh (π * t)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (Real.cosh_pos _).le]
      nlinarith [cosh_eq_one_add_two_sinh_sq t]
    have := abs_lt_of_sq_lt_sq hlt hR.le
    linarith [(abs_lt.mp this).1]
  · rw [vC_ofReal]
    have : ((vT t : ℝ) : ℂ) ^ 2 + 1 / 4 = ((vT t ^ 2 + 1 / 4 : ℝ) : ℂ) := by push_cast; ring
    rw [this]; exact ofReal_pos_mem_slit (by positivity)
  · rw [xC_ofReal]; exact ofReal_pos_mem_slit (xT_pos t)
  · rw [bC_ofReal]; exact ofReal_pos_mem_slit (bT_pos t)
  · rw [lamC_ofReal]; exact ofReal_pos_mem_slit (lamT_pos t)
  · rw [h4]; exact ofReal_pos_mem_slit (Real.cosh_pos _)
  · rw [h2]; exact ofReal_pos_mem_slit (Real.cosh_pos _)

lemma eventually_goodAt (t : ℝ) : ∀ᶠ ζ in 𝓝 (t : ℂ), GoodAt ζ := by
  have hg := goodAt_ofReal t
  have hopen := Complex.isOpen_slitPlane
  have ev : ∀ {f : ℂ → ℂ}, ContinuousAt f (t : ℂ) → f (t : ℂ) ∈ Complex.slitPlane →
      ∀ᶠ ζ in 𝓝 (t : ℂ), f ζ ∈ Complex.slitPlane :=
    fun hf hv => hf.eventually (hopen.mem_nhds hv)
  have hRC : ContinuousAt RC (t : ℂ) := hg.diff_RC.continuousAt
  have hxC : ContinuousAt xC (t : ℂ) := hg.diff_xC.continuousAt
  have hvC : ContinuousAt vC (t : ℂ) := hg.diff_vC.continuousAt
  have hbC : ContinuousAt bC (t : ℂ) := hg.diff_bC.continuousAt
  have hlC : ContinuousAt lamC (t : ℂ) := hg.diff_lamC.continuousAt
  have e1 := ev (f := fun ζ => Complex.cosh ((π : ℂ) * ζ)) (by fun_prop) hg.c1
  have e2 := ev (f := fun ζ => RC ζ + (√2 : ℂ) * Complex.cosh ((π : ℂ) * ζ / 2))
    (hRC.add (by fun_prop)) hg.c2
  have e3 := ev (f := fun ζ => RC ζ + (√2 : ℂ) * Complex.sinh ((π : ℂ) * ζ / 2))
    (hRC.add (by fun_prop)) hg.c3
  have e4 := ev (f := fun ζ => vC ζ ^ 2 + 1 / 4) ((hvC.pow 2).add continuousAt_const) hg.c4
  have e5 := ev (f := xC) hxC hg.c5
  have e6 := ev (f := bC) hbC hg.c6
  have e7 := ev (f := lamC) hlC hg.c7
  have e8 := ev (f := fun ζ => Complex.cosh ((π : ℂ) * ζ / 4)) (by fun_prop) hg.c8
  have e9 := ev (f := fun ζ => Complex.cosh ((π : ℂ) * ζ / 2)) (by fun_prop) hg.c9
  filter_upwards [e1, e2, e3, e4, e5, e6, e7, e8, e9] with ζ a1 a2 a3 a4 a5 a6 a7 a8 a9
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩

/-- **`aAmp` is an admissible amplitude** for the strip Schwarz integral. -/
theorem amp_aAmp : StripOuter.Amp aAmp := by
  refine ⟨continuous_aAmp, aAmp_even, expBdd_aAmp, fun y₀ => ?_⟩
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_goodAt y₀)
  refine ⟨R, hR, aC, ?_, fun t _ => ?_⟩
  · intro ζ hζ
    exact (hball ζ hζ).diff_aC.differentiableWithinAt
  · rw [aC_ofReal]

/-- `W_slit` in hyperbolic form: with `y = tanh(πτ/4)`,
`W_slit(y) = √(x_T/ξ*) Λ² cosh(πτ/4)⁴ / √cosh(πτ)`. -/
lemma Wslit_tanh (τ : ℝ) :
    Wslit (Real.tanh (π * τ / 4)) =
      √(xT τ / xiStar) * lamT τ ^ 2 * Real.cosh (π * τ / 4) ^ 4 / √(Real.cosh (π * τ)) := by
  set θ : ℝ := π * τ / 4 with hθ
  have hc : 0 < Real.cosh θ := Real.cosh_pos θ
  have h4 : 4 * θ = π * τ := by rw [hθ]; ring
  have hu : uSlit (Real.tanh θ) = Real.cosh (π * τ) := by rw [uSlit_tanh, h4]
  have h1 : 0 < 1 - Real.tanh θ ^ 2 := by linarith [tanh_sq_lt_one θ]
  have hdef : 1 + 6 * Real.tanh θ ^ 2 + Real.tanh θ ^ 4 = (1 - Real.tanh θ ^ 2) ^ 2 * Real.cosh (π * τ) := by
    rw [← hu]; unfold uSlit
    field_simp
  have hsq : √(1 + 6 * Real.tanh θ ^ 2 + Real.tanh θ ^ 4) = (1 - Real.tanh θ ^ 2) * √(Real.cosh (π * τ)) := by
    rw [hdef, Real.sqrt_mul (by positivity), Real.sqrt_sq h1.le]
  unfold Wslit
  rw [hsq, xOf_tanh, one_sub_tanh_sq]
  unfold lamT
  have hcc : 0 < Real.cosh (π * τ) := Real.cosh_pos _
  have hs : 0 < √(Real.cosh (π * τ)) := Real.sqrt_pos.mpr hcc
  field_simp

lemma aAmp_eq {τ : ℝ} (hτ : 0 ≤ τ) :
    aAmp τ = Real.log (Wslit (Real.tanh (π * τ / 4))) +
      (3 / 4) * Real.log (1 + Real.tanh (π * τ / 4) ^ 2) +
      (1 / 4) * Real.log (√(vOf (Real.tanh (π * τ / 4)) ^ 2 + 1 / 4) / xOf (Real.tanh (π * τ / 4))) := by
  set θ : ℝ := π * τ / 4 with hθ
  have hc : 0 < Real.cosh θ := Real.cosh_pos θ
  have h2θ : 2 * θ = π * τ / 2 := by rw [hθ]; ring
  have hxT := xT_pos τ
  have hlam := lamT_pos τ
  have hb := bT_pos τ
  have hcc : 0 < Real.cosh (π * τ) := Real.cosh_pos _
  have hc2 : 0 < Real.cosh (π * τ / 2) := Real.cosh_pos _
  have hxi := xiStar_pos
  rw [Wslit_tanh, one_add_tanh_sq, h2θ, xOf_tanh, vOf_tanh hτ]
  have hbdef : √(vT τ ^ 2 + 1 / 4) = bT τ := rfl
  rw [hbdef]
  have hsx : 0 < √(xT τ / xiStar) := Real.sqrt_pos.mpr (div_pos hxT hxi)
  have hscc : 0 < √(Real.cosh (π * τ)) := Real.sqrt_pos.mpr hcc
  unfold aAmp
  rw [Real.log_div (by positivity) hscc.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_mul hsx.ne' (by positivity), Real.log_sqrt (div_pos hxT hxi).le,
    Real.log_sqrt hcc.le, Real.log_pow, Real.log_pow, Real.log_div hxT.ne' hxi.ne',
    Real.log_div hc2.ne' (by positivity), Real.log_pow, Real.log_div hb.ne' hxT.ne']
  push_cast
  ring

end FormalResearch.ModularBootstrap.FiveTerm
