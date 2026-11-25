module

public import FormalResearch.ModularBootstrap.Constants
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Reference Blaschke Comb I: Blaschke-Factor Algebra (Lemma K1)

Formalizes Lemma K1 (`cmb:K1`) of `CFT/modular_bootstrap/paper/comb_estimates.tex`:

* `blaschkeT`: the Blaschke factor
  $T_\zeta(b) = \tanh(\frac{\pi}{2}(b - \zeta)) \tanh(\frac{\pi}{2}(b + \zeta))$.
* **K1(a)**: `norm_blaschkeT_real_le_one`, `norm_blaschkeT_real_eq_one`,
  `norm_pair_blaschkeT_le_one`, `norm_pair_blaschkeT_eq_one`, `blaschkeT_half_I`,
  and locally uniform convergence `comb_hasProdLocallyUniformlyOn` (instantiated for
  $B^{(f)}$ in `ZeroLaw.lean` once the quantiles $\chi_k$ are defined).
* **K1(b)**: `blaschkePairQ`, `blaschkePairQ_eq`, `blaschkePairQ_mono_eps`, `deltaDetune`,
  `deltaDetune_le_five_eps_sq_div`, `deltaDetune_le_of_xiStar_le`, `deltaDetune_le_of_dist_ge`.
* **K1(c)**: `combH`, `realLogT`, `realLogT_eq_combH`, derivative formulas and sign/growth bounds.
* **K1(d)**: `phiZeta` (defined by the convergent integral from $\operatorname{Re}\zeta = +\infty$
  to $\zeta$, giving an explicit analytic branch of $\log(-T_\zeta(b))$ on $\mathcal{N}$),
  `cexp_phiZeta`, `phiZeta_half_I`, `tendsto_phiZeta_atTop`, `norm_phiZeta_le`, and
  uniform exponential bounds on all derivatives $\partial_b^i \partial_\zeta^j \varphi_\zeta(b)$
  for $1 \le i + j \le 4$.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Comb

/-! ### Section 1: Basic definitions and identities for `T_ζ(b)` -/

/-- The strip Blaschke factor $T_\zeta(b) = \tanh\frac{\pi(b - \zeta)}{2}\tanh\frac{\pi(b + \zeta)}{2}$. -/
noncomputable def blaschkeT (ζ b : ℂ) : ℂ :=
  Complex.tanh ((π : ℂ) * (b - ζ) / 2) * Complex.tanh ((π : ℂ) * (b + ζ) / 2)

lemma blaschkeT_neg_zeta (ζ b : ℂ) : blaschkeT (-ζ) b = blaschkeT ζ b := by
  unfold blaschkeT
  simp only [sub_neg_eq_add, ← sub_eq_add_neg]
  ring

lemma blaschkeT_neg_b (ζ b : ℂ) : blaschkeT ζ (-b) = blaschkeT ζ b := by
  unfold blaschkeT
  have h1 : (π : ℂ) * (-b - ζ) / 2 = -((π : ℂ) * (b + ζ) / 2) := by ring
  have h2 : (π : ℂ) * (-b + ζ) / 2 = -((π : ℂ) * (b - ζ) / 2) := by ring
  rw [h1, h2, Complex.tanh_neg, Complex.tanh_neg]
  ring

lemma blaschkeT_conj (ζ b : ℂ) :
    blaschkeT (starRingEnd ℂ ζ) (starRingEnd ℂ b) = starRingEnd ℂ (blaschkeT ζ b) := by
  unfold blaschkeT
  have hpi : starRingEnd ℂ (π : ℂ) = (π : ℂ) := Complex.conj_ofReal π
  have h2 : starRingEnd ℂ (2 : ℂ) = (2 : ℂ) := by simp only [map_ofNat]
  have hconj_tanh : ∀ w : ℂ, Complex.tanh (starRingEnd ℂ w) = starRingEnd ℂ (Complex.tanh w) := by
    intro w
    rw [Complex.tanh_eq_sinh_div_cosh, Complex.tanh_eq_sinh_div_cosh, map_div₀,
      Complex.sinh_conj, Complex.cosh_conj]
  rw [map_mul, ← hconj_tanh, ← hconj_tanh]
  congr 2 <;> simp only [map_div₀, map_mul, map_sub, map_add, hpi, h2]

lemma two_mul_cosh_mul_cosh (u v : ℂ) :
    2 * Complex.cosh u * Complex.cosh v = Complex.cosh (u + v) + Complex.cosh (u - v) := by
  rw [Complex.cosh_add, Complex.cosh_sub]; ring

lemma two_mul_sinh_mul_sinh (u v : ℂ) :
    2 * Complex.sinh u * Complex.sinh v = Complex.cosh (u + v) - Complex.cosh (u - v) := by
  rw [Complex.cosh_add, Complex.cosh_sub]; ring

lemma cosh_pi_add_cosh_pi (b ζ : ℂ) :
    Complex.cosh ((π : ℂ) * b) + Complex.cosh ((π : ℂ) * ζ) =
      2 * Complex.cosh ((π : ℂ) * (b - ζ) / 2) * Complex.cosh ((π : ℂ) * (b + ζ) / 2) := by
  have h := two_mul_cosh_mul_cosh ((π : ℂ) * (b - ζ) / 2) ((π : ℂ) * (b + ζ) / 2)
  have h1 : (π : ℂ) * (b - ζ) / 2 + (π : ℂ) * (b + ζ) / 2 = (π : ℂ) * b := by ring
  have h2 : (π : ℂ) * (b - ζ) / 2 - (π : ℂ) * (b + ζ) / 2 = -((π : ℂ) * ζ) := by ring
  rw [h1, h2, Complex.cosh_neg] at h
  exact h.symm

lemma cosh_pi_sub_cosh_pi (b ζ : ℂ) :
    Complex.cosh ((π : ℂ) * b) - Complex.cosh ((π : ℂ) * ζ) =
      2 * Complex.sinh ((π : ℂ) * (b - ζ) / 2) * Complex.sinh ((π : ℂ) * (b + ζ) / 2) := by
  have h := two_mul_sinh_mul_sinh ((π : ℂ) * (b - ζ) / 2) ((π : ℂ) * (b + ζ) / 2)
  have h1 : (π : ℂ) * (b - ζ) / 2 + (π : ℂ) * (b + ζ) / 2 = (π : ℂ) * b := by ring
  have h2 : (π : ℂ) * (b - ζ) / 2 - (π : ℂ) * (b + ζ) / 2 = -((π : ℂ) * ζ) := by ring
  rw [h1, h2, Complex.cosh_neg] at h
  exact h.symm

lemma blaschkeT_eq_cosh_div {ζ b : ℂ}
    (hden : Complex.cosh ((π : ℂ) * b) + Complex.cosh ((π : ℂ) * ζ) ≠ 0) :
    blaschkeT ζ b =
      (Complex.cosh ((π : ℂ) * b) - Complex.cosh ((π : ℂ) * ζ)) /
        (Complex.cosh ((π : ℂ) * b) + Complex.cosh ((π : ℂ) * ζ)) := by
  unfold blaschkeT
  rw [Complex.tanh_eq_sinh_div_cosh, Complex.tanh_eq_sinh_div_cosh]
  rw [cosh_pi_add_cosh_pi, cosh_pi_sub_cosh_pi]
  have h2c : 2 * Complex.cosh ((π : ℂ) * (b - ζ) / 2) * Complex.cosh ((π : ℂ) * (b + ζ) / 2) ≠ 0 := by
    rwa [← cosh_pi_add_cosh_pi]
  have h1 : Complex.cosh ((π : ℂ) * (b - ζ) / 2) ≠ 0 := by
    intro h0; apply h2c; rw [h0]; ring
  have h2 : Complex.cosh ((π : ℂ) * (b + ζ) / 2) ≠ 0 := by
    intro h0; apply h2c; rw [h0]; ring
  field_simp [h1, h2]

/-- $T_\zeta(i/2) = -1$ whenever $|\operatorname{Im} \zeta| < 1/2$. -/
lemma blaschkeT_half_I {ζ : ℂ} (hζ : |ζ.im| < 1 / 2) :
    blaschkeT ζ (Complex.I / 2) = -1 := by
  have hpi := Real.pi_pos
  have hc0 : Complex.cosh ((π : ℂ) * (Complex.I / 2)) = 0 := by
    rw [show (π : ℂ) * (Complex.I / 2) = ((π / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.cosh_mul_I, ← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero]
  have hcosh_ne : Complex.cosh ((π : ℂ) * ζ) ≠ 0 := by
    intro h0
    have hre_im : Complex.cosh ((π : ℂ) * ζ) =
        ((Real.cosh (π * ζ.re) * Real.cos (π * ζ.im) : ℝ) : ℂ) +
          ((Real.sinh (π * ζ.re) * Real.sin (π * ζ.im) : ℝ) : ℂ) * Complex.I := by
      have hpb : (π : ℂ) * ζ = ((π * ζ.re : ℝ) : ℂ) + ((π * ζ.im : ℝ) : ℂ) * Complex.I :=
        Complex.ext (by simp) (by simp)
      rw [hpb, Complex.cosh_add, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh,
        Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast; ring
    have hre := congrArg Complex.re h0
    rw [hre_im] at hre
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_re] at hre
    have hcos : 0 < Real.cos (π * ζ.im) :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [(abs_lt.mp hζ).1], by nlinarith [(abs_lt.mp hζ).2]⟩
    have hcosh : 0 < Real.cosh (π * ζ.re) := Real.cosh_pos _
    linarith [mul_pos hcosh hcos]
  have hden : Complex.cosh ((π : ℂ) * (Complex.I / 2)) + Complex.cosh ((π : ℂ) * ζ) ≠ 0 := by
    rwa [hc0, zero_add]
  rw [blaschkeT_eq_cosh_div hden, hc0, zero_sub, zero_add, neg_div, div_self hcosh_ne]

lemma blaschkeT_neg_half_I {ζ : ℂ} (hζ : |ζ.im| < 1 / 2) :
    blaschkeT ζ (-Complex.I / 2) = -1 := by
  rw [show (-Complex.I / 2 : ℂ) = -(Complex.I / 2) by ring, blaschkeT_neg_b, blaschkeT_half_I hζ]

/-! ### Section 2: Lemma K1(a) — Modulus bounds on the strip and infinite products -/

lemma complex_sinh_normSq (x y : ℝ) :
    Complex.normSq (Complex.sinh ((x : ℂ) + (y : ℂ) * Complex.I)) =
      Real.sinh x ^ 2 + Real.sin y ^ 2 := by
  rw [Complex.sinh_add, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh,
    Complex.sinh_mul_I, Complex.cosh_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
  have hre : (Complex.sinh (x : ℂ) * Complex.cosh ((y : ℂ) * Complex.I) +
      Complex.cosh (x : ℂ) * Complex.sinh ((y : ℂ) * Complex.I)).re = Real.sinh x * Real.cos y := by
    simp [← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.cosh_mul_I, Complex.sinh_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, zero_mul, add_zero, Complex.add_im, Complex.mul_im, mul_one]
  have hcos : Real.cos y ^ 2 = 1 - Real.sin y ^ 2 := by linarith [Real.sin_sq_add_cos_sq y]
  have hcosh : Real.cosh x ^ 2 = Real.sinh x ^ 2 + 1 := by linarith [Real.cosh_sq_sub_sinh_sq x]
  nlinarith

lemma complex_cosh_normSq (x y : ℝ) :
    Complex.normSq (Complex.cosh ((x : ℂ) + (y : ℂ) * Complex.I)) =
      Real.cosh x ^ 2 - Real.sin y ^ 2 := by
  rw [Complex.cosh_add, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh,
    Complex.sinh_mul_I, Complex.cosh_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, zero_mul, add_zero, Complex.add_im, Complex.mul_im, mul_one]
  have hcos : Real.cos y ^ 2 = 1 - Real.sin y ^ 2 := by linarith [Real.sin_sq_add_cos_sq y]
  have hcosh : Real.cosh x ^ 2 = Real.sinh x ^ 2 + 1 := by linarith [Real.cosh_sq_sub_sinh_sq x]
  nlinarith

lemma complex_cosh_ne_zero_of_abs_im_lt_pi_div_two {w : ℂ} (hw : |w.im| < π / 2) :
    Complex.cosh w ≠ 0 := by
  intro h0
  have hw_eq : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := Complex.ext (by simp) (by simp)
  have hns : Complex.normSq (Complex.cosh w) = 0 := by rw [h0, map_zero]
  rw [hw_eq, complex_cosh_normSq] at hns
  have hsin_lt : |Real.sin w.im| < 1 := by
    have h1 := Real.sin_sq_add_cos_sq w.im
    have hcos_pos : 0 < Real.cos w.im := Real.cos_pos_of_mem_Ioo (abs_lt.mp hw)
    rw [abs_lt]
    constructor <;> nlinarith [sq_nonneg (Real.sin w.im), sq_pos_of_pos hcos_pos]
  have hsin_sq : Real.sin w.im ^ 2 < 1 := by nlinarith [abs_lt.mp hsin_lt]
  have hcosh_ge : 1 ≤ Real.cosh w.re ^ 2 := by
    have := Real.one_le_cosh w.re
    nlinarith
  linarith

lemma norm_tanh_sq_eq (w : ℂ) :
    ‖Complex.tanh w‖ ^ 2 =
      (Real.sinh w.re ^ 2 + Real.sin w.im ^ 2) / (Real.cosh w.re ^ 2 - Real.sin w.im ^ 2) := by
  have hw_eq : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := Complex.ext (by simp) (by simp)
  rw [Complex.tanh_eq_sinh_div_cosh, Complex.sq_norm, Complex.normSq_div]
  conv_lhs => rw [hw_eq]
  rw [complex_sinh_normSq, complex_cosh_normSq]

/-- For $|\operatorname{Im} w| \le \pi/4$, $|\tanh w| \le 1$, with equality when $|\operatorname{Im} w| = \pi/4$. -/
lemma norm_tanh_le_one_of_abs_im_le {w : ℂ} (hw : |w.im| ≤ π / 4) :
    ‖Complex.tanh w‖ ≤ 1 := by
  have hpi := Real.pi_pos
  have hw_lt : |w.im| < π / 2 := lt_of_le_of_lt hw (by linarith)
  have hcos_pos : 0 ≤ Real.cos (2 * w.im) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [(abs_le.mp hw).1], by linarith [(abs_le.mp hw).2]⟩
  have hsin_sq : Real.sin w.im ^ 2 = (1 - Real.cos (2 * w.im)) / 2 := by
    rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq w.im]
  have hden_pos : 0 < Real.cosh w.re ^ 2 - Real.sin w.im ^ 2 := by
    rw [hsin_sq]
    have := Real.one_le_cosh w.re
    nlinarith [Real.cos_le_one (2 * w.im)]
  have hsq : ‖Complex.tanh w‖ ^ 2 ≤ 1 := by
    rw [norm_tanh_sq_eq, div_le_one hden_pos]
    rw [hsin_sq]
    have hcosh : Real.cosh w.re ^ 2 = Real.sinh w.re ^ 2 + 1 := by
      linarith [Real.cosh_sq_sub_sinh_sq w.re]
    linarith
  nlinarith [norm_nonneg (Complex.tanh w)]

lemma norm_tanh_eq_one_of_abs_im_eq {w : ℂ} (hw : |w.im| = π / 4) :
    ‖Complex.tanh w‖ = 1 := by
  have hcos0 : Real.cos (2 * w.im) = 0 := by
    rcases abs_eq (by linarith [Real.pi_pos] : 0 ≤ π / 4) |>.mp hw with h | h
    · rw [h, show 2 * (π / 4) = π / 2 by ring, Real.cos_pi_div_two]
    · rw [h, show 2 * (-(π / 4)) = -(π / 2) by ring, Real.cos_neg, Real.cos_pi_div_two]
  have hsin_sq : Real.sin w.im ^ 2 = 1 / 2 := by
    have := Real.cos_two_mul w.im
    rw [hcos0] at this
    nlinarith [Real.sin_sq_add_cos_sq w.im]
  have hden_pos : 0 < Real.cosh w.re ^ 2 - Real.sin w.im ^ 2 := by
    rw [hsin_sq]
    have := Real.one_le_cosh w.re
    nlinarith
  have hsq : ‖Complex.tanh w‖ ^ 2 = 1 := by
    rw [norm_tanh_sq_eq, div_eq_one_iff_eq hden_pos.ne']
    have hcosh : Real.cosh w.re ^ 2 = Real.sinh w.re ^ 2 + 1 := by
      linarith [Real.cosh_sq_sub_sinh_sq w.re]
    linarith [hsin_sq]
  nlinarith [norm_nonneg (Complex.tanh w)]

/-- **K1(a), real factor**: for real $\chi$, $|T_\chi(b)| \le 1$ on $|\operatorname{Im} b| \le 1/2$,
and $|T_\chi(b)| = 1$ on $|\operatorname{Im} b| = 1/2$. -/
theorem norm_blaschkeT_real_le_one (χ : ℝ) {b : ℂ} (hb : |b.im| ≤ 1 / 2) :
    ‖blaschkeT (χ : ℂ) b‖ ≤ 1 := by
  unfold blaschkeT
  rw [norm_mul]
  have hpi := Real.pi_pos
  have him1 : |((π : ℂ) * (b - (χ : ℂ)) / 2).im| ≤ π / 4 := by
    have : ((π : ℂ) * (b - (χ : ℂ)) / 2).im = π * b.im / 2 := by
      simp [Complex.mul_im, Complex.sub_im]
    rw [this, abs_div, abs_mul, abs_of_pos hpi, abs_two]
    nlinarith
  have him2 : |((π : ℂ) * (b + (χ : ℂ)) / 2).im| ≤ π / 4 := by
    have : ((π : ℂ) * (b + (χ : ℂ)) / 2).im = π * b.im / 2 := by
      simp [Complex.mul_im, Complex.add_im]
    rw [this, abs_div, abs_mul, abs_of_pos hpi, abs_two]
    nlinarith
  exact (mul_le_mul (norm_tanh_le_one_of_abs_im_le him1) (norm_tanh_le_one_of_abs_im_le him2)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem norm_blaschkeT_real_eq_one (χ : ℝ) {b : ℂ} (hb : |b.im| = 1 / 2) :
    ‖blaschkeT (χ : ℂ) b‖ = 1 := by
  unfold blaschkeT
  rw [norm_mul]
  have hpi := Real.pi_pos
  have him1 : |((π : ℂ) * (b - (χ : ℂ)) / 2).im| = π / 4 := by
    have : ((π : ℂ) * (b - (χ : ℂ)) / 2).im = π * b.im / 2 := by
      simp [Complex.mul_im, Complex.sub_im]
    rw [this, abs_div, abs_mul, abs_of_pos hpi, abs_two, hb]; ring
  have him2 : |((π : ℂ) * (b + (χ : ℂ)) / 2).im| = π / 4 := by
    have : ((π : ℂ) * (b + (χ : ℂ)) / 2).im = π * b.im / 2 := by
      simp [Complex.mul_im, Complex.add_im]
    rw [this, abs_div, abs_mul, abs_of_pos hpi, abs_two, hb]; ring
  rw [norm_tanh_eq_one_of_abs_im_eq him1, norm_tanh_eq_one_of_abs_im_eq him2, mul_one]

/-- Algebraic core for the conjugate pair: for $|y| \le 1/2$ and $|\varepsilon| \le 1/4$
(in fact $|\varepsilon| < 1/2$),
$\|\tanh(\frac{\pi}{2}(x + i(y - \varepsilon))) \tanh(\frac{\pi}{2}(x + i(y + \varepsilon)))\| \le 1$,
with equality when $|y| = 1/2$. -/
private lemma norm_tanh_pair_le_one (x y ε : ℝ) (hy : |y| ≤ 1 / 2) (hε : |ε| ≤ 1 / 4) :
    ‖Complex.tanh ((π : ℂ) * ((x : ℂ) + ((y - ε : ℝ) : ℂ) * Complex.I) / 2) *
        Complex.tanh ((π : ℂ) * ((x : ℂ) + ((y + ε : ℝ) : ℂ) * Complex.I) / 2)‖ ≤ 1 := by
  have hpi := Real.pi_pos
  set α := π * y / 2
  set β := π * ε / 2
  set S := Real.sinh (π * x / 2) ^ 2
  set C := Real.cosh (π * x / 2) ^ 2
  set u := Real.sin (α - β) ^ 2
  set v := Real.sin (α + β) ^ 2
  have hre1 : ((π : ℂ) * ((x : ℂ) + ((y - ε : ℝ) : ℂ) * Complex.I) / 2).re = π * x / 2 := by
    simp [Complex.mul_re]
  have him1 : ((π : ℂ) * ((x : ℂ) + ((y - ε : ℝ) : ℂ) * Complex.I) / 2).im = α - β := by
    simp [α, β, Complex.mul_im]; ring
  have hre2 : ((π : ℂ) * ((x : ℂ) + ((y + ε : ℝ) : ℂ) * Complex.I) / 2).re = π * x / 2 := by
    simp [Complex.mul_re]
  have him2 : ((π : ℂ) * ((x : ℂ) + ((y + ε : ℝ) : ℂ) * Complex.I) / 2).im = α + β := by
    simp [α, β, Complex.mul_im]; ring
  have hsin_bound : ∀ θ : ℝ, |θ| ≤ 3 * π / 8 → Real.sin θ ^ 2 < 1 := by
    intro θ hθ
    have hcos_pos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_le.mp hθ).1], by linarith [(abs_le.mp hθ).2]⟩
    linarith only [Real.sin_sq_add_cos_sq θ, sq_pos_of_pos hcos_pos]
  have hαβ1 : |α - β| ≤ 3 * π / 8 := by
    dsimp [α, β]; rw [abs_le]; constructor <;> nlinarith only [hpi, (abs_le.mp hy).1, (abs_le.mp hy).2,
      (abs_le.mp hε).1, (abs_le.mp hε).2]
  have hαβ2 : |α + β| ≤ 3 * π / 8 := by
    dsimp [α, β]; rw [abs_le]; constructor <;> nlinarith only [hpi, (abs_le.mp hy).1, (abs_le.mp hy).2,
      (abs_le.mp hε).1, (abs_le.mp hε).2]
  have hC1 : 1 ≤ C := by nlinarith only [Real.one_le_cosh (π * x / 2)]
  have hden1 : 0 < C - u := by linarith [hsin_bound (α - β) hαβ1]
  have hden2 : 0 < C - v := by linarith [hsin_bound (α + β) hαβ2]
  have htrig : 1 - u - v = Real.cos (π * y) * Real.cos (π * ε) := by
    have h1 : u = (1 - Real.cos (2 * α - 2 * β)) / 2 := by
      have := Real.cos_two_mul (α - β)
      rw [show 2 * (α - β) = 2 * α - 2 * β by ring] at this
      linarith only [Real.sin_sq_add_cos_sq (α - β), this]
    have h2 : v = (1 - Real.cos (2 * α + 2 * β)) / 2 := by
      have := Real.cos_two_mul (α + β)
      rw [show 2 * (α + β) = 2 * α + 2 * β by ring] at this
      linarith only [Real.sin_sq_add_cos_sq (α + β), this]
    rw [h1, h2, show 2 * α = π * y by dsimp [α]; ring, show 2 * β = π * ε by dsimp [β]; ring]
    rw [Real.cos_sub, Real.cos_add]
    ring
  have hcos_y : 0 ≤ Real.cos (π * y) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith only [hpi, (abs_le.mp hy).1], by nlinarith only [hpi, (abs_le.mp hy).2]⟩
  have hcos_ε : 0 ≤ Real.cos (π * ε) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith only [hpi, (abs_le.mp hε).1], by nlinarith only [hpi, (abs_le.mp hε).2]⟩
  have hCS : C = S + 1 := by linarith [Real.cosh_sq_sub_sinh_sq (π * x / 2)]
  have hnum_le : (S + u) * (S + v) ≤ (C - u) * (C - v) := by
    have hdiff : (C - u) * (C - v) - (S + u) * (S + v) = (2 * S + 1) * (1 - u - v) := by
      rw [hCS]; ring
    have hnn : 0 ≤ (2 * S + 1) * (1 - u - v) := by
      rw [htrig]
      exact mul_nonneg (by positivity) (mul_nonneg hcos_y hcos_ε)
    linarith
  have hsq : ‖Complex.tanh ((π : ℂ) * ((x : ℂ) + ((y - ε : ℝ) : ℂ) * Complex.I) / 2) *
      Complex.tanh ((π : ℂ) * ((x : ℂ) + ((y + ε : ℝ) : ℂ) * Complex.I) / 2)‖ ^ 2 ≤ 1 := by
    rw [norm_mul, mul_pow, norm_tanh_sq_eq, norm_tanh_sq_eq, hre1, him1, hre2, him2]
    change ((S + u) / (C - u)) * ((S + v) / (C - v)) ≤ 1
    rw [div_mul_div_comm, div_le_one (mul_pos hden1 hden2)]
    exact hnum_le
  exact (sq_le_one_iff₀ (norm_nonneg _)).mp hsq

private lemma norm_tanh_pair_eq_one (x y ε : ℝ) (hy : |y| = 1 / 2) (hε : |ε| ≤ 1 / 4) :
    ‖Complex.tanh ((π : ℂ) * ((x : ℂ) + ((y - ε : ℝ) : ℂ) * Complex.I) / 2) *
        Complex.tanh ((π : ℂ) * ((x : ℂ) + ((y + ε : ℝ) : ℂ) * Complex.I) / 2)‖ = 1 := by
  have hpi := Real.pi_pos
  set α := π * y / 2
  set β := π * ε / 2
  set S := Real.sinh (π * x / 2) ^ 2
  set C := Real.cosh (π * x / 2) ^ 2
  set u := Real.sin (α - β) ^ 2
  set v := Real.sin (α + β) ^ 2
  have hre1 : ((π : ℂ) * ((x : ℂ) + ((y - ε : ℝ) : ℂ) * Complex.I) / 2).re = π * x / 2 := by
    simp [Complex.mul_re]
  have him1 : ((π : ℂ) * ((x : ℂ) + ((y - ε : ℝ) : ℂ) * Complex.I) / 2).im = α - β := by
    simp [α, β, Complex.mul_im]; ring
  have hre2 : ((π : ℂ) * ((x : ℂ) + ((y + ε : ℝ) : ℂ) * Complex.I) / 2).re = π * x / 2 := by
    simp [Complex.mul_re]
  have him2 : ((π : ℂ) * ((x : ℂ) + ((y + ε : ℝ) : ℂ) * Complex.I) / 2).im = α + β := by
    simp [α, β, Complex.mul_im]; ring
  have hsin_bound : ∀ θ : ℝ, |θ| ≤ 3 * π / 8 → Real.sin θ ^ 2 < 1 := by
    intro θ hθ
    have hcos_pos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_le.mp hθ).1], by linarith [(abs_le.mp hθ).2]⟩
    linarith only [Real.sin_sq_add_cos_sq θ, sq_pos_of_pos hcos_pos]
  have hy_le : |y| ≤ 1 / 2 := hy.le
  have hαβ1 : |α - β| ≤ 3 * π / 8 := by
    dsimp [α, β]; rw [abs_le]; constructor <;> nlinarith only [hpi, (abs_le.mp hy_le).1, (abs_le.mp hy_le).2,
      (abs_le.mp hε).1, (abs_le.mp hε).2]
  have hαβ2 : |α + β| ≤ 3 * π / 8 := by
    dsimp [α, β]; rw [abs_le]; constructor <;> nlinarith only [hpi, (abs_le.mp hy_le).1, (abs_le.mp hy_le).2,
      (abs_le.mp hε).1, (abs_le.mp hε).2]
  have hC1 : 1 ≤ C := by nlinarith only [Real.one_le_cosh (π * x / 2)]
  have hden1 : 0 < C - u := by linarith [hsin_bound (α - β) hαβ1]
  have hden2 : 0 < C - v := by linarith [hsin_bound (α + β) hαβ2]
  have hcos_y0 : Real.cos (π * y) = 0 := by
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.mp hy with h | h
    · rw [h, show π * (1 / 2) = π / 2 by ring, Real.cos_pi_div_two]
    · rw [h, show π * (-(1 / 2)) = -(π / 2) by ring, Real.cos_neg, Real.cos_pi_div_two]
  have htrig : 1 - u - v = 0 := by
    have h1 : u = (1 - Real.cos (2 * α - 2 * β)) / 2 := by
      have := Real.cos_two_mul (α - β)
      rw [show 2 * (α - β) = 2 * α - 2 * β by ring] at this
      linarith only [Real.sin_sq_add_cos_sq (α - β), this]
    have h2 : v = (1 - Real.cos (2 * α + 2 * β)) / 2 := by
      have := Real.cos_two_mul (α + β)
      rw [show 2 * (α + β) = 2 * α + 2 * β by ring] at this
      linarith only [Real.sin_sq_add_cos_sq (α + β), this]
    rw [h1, h2, show 2 * α = π * y by dsimp [α]; ring, show 2 * β = π * ε by dsimp [β]; ring]
    rw [Real.cos_sub, Real.cos_add, hcos_y0]
    ring
  have hCS : C = S + 1 := by linarith [Real.cosh_sq_sub_sinh_sq (π * x / 2)]
  have hnum_eq : (S + u) * (S + v) = (C - u) * (C - v) := by
    have hdiff : (C - u) * (C - v) - (S + u) * (S + v) = (2 * S + 1) * (1 - u - v) := by
      rw [hCS]; ring
    rw [htrig, mul_zero] at hdiff
    linarith
  have hsq : ‖Complex.tanh ((π : ℂ) * ((x : ℂ) + ((y - ε : ℝ) : ℂ) * Complex.I) / 2) *
      Complex.tanh ((π : ℂ) * ((x : ℂ) + ((y + ε : ℝ) : ℂ) * Complex.I) / 2)‖ ^ 2 = 1 := by
    rw [norm_mul, mul_pow, norm_tanh_sq_eq, norm_tanh_sq_eq, hre1, him1, hre2, him2]
    change ((S + u) / (C - u)) * ((S + v) / (C - v)) = 1
    rw [div_mul_div_comm, div_eq_one_iff_eq (mul_pos hden1 hden2).ne']
    exact hnum_eq
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hsq

/-- **K1(a), conjugate pair**: for real $\chi$ and $|\varepsilon| \le 1/4$ (in particular $0 \le \varepsilon \le 1/8$),
$|T_{\chi+i\varepsilon}(b) T_{\chi-i\varepsilon}(b)| \le 1$ on $|\operatorname{Im} b| \le 1/2$,
and $= 1$ on $|\operatorname{Im} b| = 1/2$. -/
theorem norm_pair_blaschkeT_le_one (χ ε : ℝ) (hε : |ε| ≤ 1 / 4) {b : ℂ} (hb : |b.im| ≤ 1 / 2) :
    ‖blaschkeT ((χ : ℂ) + (ε : ℂ) * Complex.I) b *
        blaschkeT ((χ : ℂ) - (ε : ℂ) * Complex.I) b‖ ≤ 1 := by
  have hb_eq : b = (b.re : ℂ) + (b.im : ℂ) * Complex.I := Complex.ext (by simp) (by simp)
  unfold blaschkeT
  have hrearrange :
      (Complex.tanh ((π : ℂ) * (b - ((χ : ℂ) + (ε : ℂ) * Complex.I)) / 2) *
          Complex.tanh ((π : ℂ) * (b + ((χ : ℂ) + (ε : ℂ) * Complex.I)) / 2)) *
        (Complex.tanh ((π : ℂ) * (b - ((χ : ℂ) - (ε : ℂ) * Complex.I)) / 2) *
          Complex.tanh ((π : ℂ) * (b + ((χ : ℂ) - (ε : ℂ) * Complex.I)) / 2)) =
      (Complex.tanh ((π : ℂ) * (((b.re - χ : ℝ) : ℂ) + ((b.im - ε : ℝ) : ℂ) * Complex.I) / 2) *
          Complex.tanh ((π : ℂ) * (((b.re - χ : ℝ) : ℂ) + ((b.im + ε : ℝ) : ℂ) * Complex.I) / 2)) *
        (Complex.tanh ((π : ℂ) * (((b.re + χ : ℝ) : ℂ) + ((b.im - ε : ℝ) : ℂ) * Complex.I) / 2) *
          Complex.tanh ((π : ℂ) * (((b.re + χ : ℝ) : ℂ) + ((b.im + ε : ℝ) : ℂ) * Complex.I) / 2)) := by
    have h1 : b - ((χ : ℂ) + (ε : ℂ) * Complex.I) =
        ((b.re - χ : ℝ) : ℂ) + ((b.im - ε : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    have h2 : b - ((χ : ℂ) - (ε : ℂ) * Complex.I) =
        ((b.re - χ : ℝ) : ℂ) + ((b.im + ε : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    have h3 : b + ((χ : ℂ) + (ε : ℂ) * Complex.I) =
        ((b.re + χ : ℝ) : ℂ) + ((b.im + ε : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    have h4 : b + ((χ : ℂ) - (ε : ℂ) * Complex.I) =
        ((b.re + χ : ℝ) : ℂ) + ((b.im - ε : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp; ring_nf
    rw [h1, h2, h3, h4]
    ring
  rw [hrearrange, norm_mul]
  exact (mul_le_mul (norm_tanh_pair_le_one (b.re - χ) b.im ε hb hε)
    (norm_tanh_pair_le_one (b.re + χ) b.im ε hb hε) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem norm_pair_blaschkeT_eq_one (χ ε : ℝ) (hε : |ε| ≤ 1 / 4) {b : ℂ} (hb : |b.im| = 1 / 2) :
    ‖blaschkeT ((χ : ℂ) + (ε : ℂ) * Complex.I) b *
        blaschkeT ((χ : ℂ) - (ε : ℂ) * Complex.I) b‖ = 1 := by
  have hb_eq : b = (b.re : ℂ) + (b.im : ℂ) * Complex.I := Complex.ext (by simp) (by simp)
  unfold blaschkeT
  have hrearrange :
      (Complex.tanh ((π : ℂ) * (b - ((χ : ℂ) + (ε : ℂ) * Complex.I)) / 2) *
          Complex.tanh ((π : ℂ) * (b + ((χ : ℂ) + (ε : ℂ) * Complex.I)) / 2)) *
        (Complex.tanh ((π : ℂ) * (b - ((χ : ℂ) - (ε : ℂ) * Complex.I)) / 2) *
          Complex.tanh ((π : ℂ) * (b + ((χ : ℂ) - (ε : ℂ) * Complex.I)) / 2)) =
      (Complex.tanh ((π : ℂ) * (((b.re - χ : ℝ) : ℂ) + ((b.im - ε : ℝ) : ℂ) * Complex.I) / 2) *
          Complex.tanh ((π : ℂ) * (((b.re - χ : ℝ) : ℂ) + ((b.im + ε : ℝ) : ℂ) * Complex.I) / 2)) *
        (Complex.tanh ((π : ℂ) * (((b.re + χ : ℝ) : ℂ) + ((b.im - ε : ℝ) : ℂ) * Complex.I) / 2) *
          Complex.tanh ((π : ℂ) * (((b.re + χ : ℝ) : ℂ) + ((b.im + ε : ℝ) : ℂ) * Complex.I) / 2)) := by
    have h1 : b - ((χ : ℂ) + (ε : ℂ) * Complex.I) =
        ((b.re - χ : ℝ) : ℂ) + ((b.im - ε : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    have h2 : b - ((χ : ℂ) - (ε : ℂ) * Complex.I) =
        ((b.re - χ : ℝ) : ℂ) + ((b.im + ε : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    have h3 : b + ((χ : ℂ) + (ε : ℂ) * Complex.I) =
        ((b.re + χ : ℝ) : ℂ) + ((b.im + ε : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    have h4 : b + ((χ : ℂ) - (ε : ℂ) * Complex.I) =
        ((b.re + χ : ℝ) : ℂ) + ((b.im - ε : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp; ring_nf
    rw [h1, h2, h3, h4]
    ring
  rw [hrearrange, norm_mul, norm_tanh_pair_eq_one (b.re - χ) b.im ε hb hε,
    norm_tanh_pair_eq_one (b.re + χ) b.im ε hb hε, mul_one]

lemma differentiableAt_blaschkeT {ζ b : ℂ} (hb : |b.im| + |ζ.im| < 1) :
    DifferentiableAt ℂ (blaschkeT ζ) b := by
  have hpi := Real.pi_pos
  have hc_diff : ∀ s : ℝ, |s| = 1 →
      DifferentiableAt ℂ (fun z : ℂ => Complex.tanh ((π : ℂ) * (z + (s : ℂ) * ζ) / 2)) b := by
    intro s hs
    have him : |((π : ℂ) * (b + (s : ℂ) * ζ) / 2).im| < π / 2 := by
      have him_eq : ((π : ℂ) * (b + (s : ℂ) * ζ) / 2).im = π * (b.im + s * ζ.im) / 2 := by
        simp [Complex.mul_im]
      rw [him_eq, abs_div, abs_mul, abs_of_pos hpi, abs_two]
      have habs : |b.im + s * ζ.im| ≤ |b.im| + |ζ.im| := by
        calc |b.im + s * ζ.im| ≤ |b.im| + |s * ζ.im| := abs_add_le _ _
          _ = |b.im| + |s| * |ζ.im| := by rw [abs_mul]
          _ = |b.im| + |ζ.im| := by rw [hs, one_mul]
      nlinarith
    have hc_ne := complex_cosh_ne_zero_of_abs_im_lt_pi_div_two him
    have h_tanh : (fun z : ℂ => Complex.tanh ((π : ℂ) * (z + (s : ℂ) * ζ) / 2)) =
        fun z => Complex.sinh ((π : ℂ) * (z + (s : ℂ) * ζ) / 2) /
          Complex.cosh ((π : ℂ) * (z + (s : ℂ) * ζ) / 2) := by
      ext z; exact Complex.tanh_eq_sinh_div_cosh _
    rw [h_tanh]
    have hlin : DifferentiableAt ℂ (fun z : ℂ => (π : ℂ) * (z + (s : ℂ) * ζ) / 2) b := by
      fun_prop
    exact (Complex.differentiable_sinh.differentiableAt.comp b hlin).div
      (Complex.differentiable_cosh.differentiableAt.comp b hlin) hc_ne
  have h1 := hc_diff (-1) (by norm_num)
  have h2 := hc_diff 1 (by norm_num)
  have h_eq : blaschkeT ζ =
      fun z : ℂ => Complex.tanh ((π : ℂ) * (z + ((-1 : ℝ) : ℂ) * ζ) / 2) *
        Complex.tanh ((π : ℂ) * (z + ((1 : ℝ) : ℂ) * ζ) / 2) := by
    ext z; unfold blaschkeT; congr 3 <;> push_cast <;> ring
  rw [h_eq]
  exact h1.mul h2

lemma blaschkeT_add_one_eq {ζ b : ℂ}
    (hden : Complex.cosh ((π : ℂ) * b) + Complex.cosh ((π : ℂ) * ζ) ≠ 0) :
    blaschkeT ζ b + 1 =
      2 * Complex.cosh ((π : ℂ) * b) /
        (Complex.cosh ((π : ℂ) * b) + Complex.cosh ((π : ℂ) * ζ)) := by
  rw [blaschkeT_eq_cosh_div hden]
  field_simp [hden]
  ring

private lemma norm_cosh_ge_half_exp_sub (z : ℂ) :
    Real.exp (π * |z.re|) / 2 - 1 ≤ ‖Complex.cosh ((π : ℂ) * z)‖ := by
  have hpi := Real.pi_pos
  have hns : ‖Complex.cosh ((π : ℂ) * z)‖ ^ 2 = Real.cosh (π * z.re) ^ 2 - Real.sin (π * z.im) ^ 2 := by
    have hz : (π : ℂ) * z = ((π * z.re : ℝ) : ℂ) + ((π * z.im : ℝ) : ℂ) * Complex.I :=
      Complex.ext (by simp) (by simp)
    rw [Complex.sq_norm, hz, complex_cosh_normSq]
  have hsq : Real.cosh (π * z.re) ^ 2 - 1 ≤ ‖Complex.cosh ((π : ℂ) * z)‖ ^ 2 := by
    rw [hns]; linarith [Real.sin_sq_le_one (π * z.im)]
  have hsinh : Real.sinh (π * |z.re|) ^ 2 = Real.cosh (π * z.re) ^ 2 - 1 := by
    have : Real.cosh (π * |z.re|) = Real.cosh (π * z.re) := by
      rcases le_or_gt 0 z.re with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, mul_neg, Real.cosh_neg]
    rw [← this]
    linarith [Real.cosh_sq_sub_sinh_sq (π * |z.re|)]
  have hge_sinh : Real.sinh (π * |z.re|) ≤ ‖Complex.cosh ((π : ℂ) * z)‖ := by
    have hnn : 0 ≤ Real.sinh (π * |z.re|) := Real.sinh_nonneg_iff.mpr (by positivity)
    nlinarith [norm_nonneg (Complex.cosh ((π : ℂ) * z))]
  have hexp : Real.exp (π * |z.re|) / 2 - 1 ≤ Real.sinh (π * |z.re|) := by
    rw [Real.sinh_eq]
    have h1 : Real.exp (-(π * |z.re|)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    linarith
  exact hexp.trans hge_sinh

private lemma norm_cosh_le_exp (z : ℂ) :
    ‖Complex.cosh ((π : ℂ) * z)‖ ≤ Real.exp (π * |z.re|) := by
  have hpi := Real.pi_pos
  have hz : (π : ℂ) * z = ((π * z.re : ℝ) : ℂ) + ((π * z.im : ℝ) : ℂ) * Complex.I :=
    Complex.ext (by simp) (by simp)
  have hns : ‖Complex.cosh ((π : ℂ) * z)‖ ^ 2 = Real.cosh (π * z.re) ^ 2 - Real.sin (π * z.im) ^ 2 := by
    rw [Complex.sq_norm, hz, complex_cosh_normSq]
  have hle_c : ‖Complex.cosh ((π : ℂ) * z)‖ ≤ Real.cosh (π * |z.re|) := by
    have hc : Real.cosh (π * |z.re|) = Real.cosh (π * z.re) := by
      rcases le_or_gt 0 z.re with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, mul_neg, Real.cosh_neg]
    have hsq : ‖Complex.cosh ((π : ℂ) * z)‖ ^ 2 ≤ Real.cosh (π * |z.re|) ^ 2 := by
      rw [hns, hc]; linarith [sq_nonneg (Real.sin (π * z.im))]
    nlinarith [norm_nonneg (Complex.cosh ((π : ℂ) * z)), Real.cosh_pos (π * |z.re|)]
  have hc_exp : Real.cosh (π * |z.re|) ≤ Real.exp (π * |z.re|) := by
    rw [Real.cosh_eq]
    have h1 : Real.exp (-(π * |z.re|)) ≤ Real.exp (π * |z.re|) :=
      Real.exp_le_exp.mpr (by linarith [mul_nonneg hpi.le (abs_nonneg z.re)])
    linarith
  exact hle_c.trans hc_exp

lemma blaschkeT_pair_sub_one_le {χ ε : ℝ} {b : ℂ} (hε : |ε| ≤ 1 / 8) (hχ : 0 ≤ χ)
    {R : ℝ} (hR : 0 ≤ R) (hbR : |b.re| ≤ R) (hχR : R + 2 ≤ χ) :
    ‖blaschkeT ((χ : ℂ) + (ε : ℂ) * Complex.I) b *
        blaschkeT ((χ : ℂ) - (ε : ℂ) * Complex.I) b - 1‖ ≤
      32 * Real.exp (π * R) * Real.exp (-π * χ) := by
  have hpi := Real.pi_pos
  have hexp8 : 8 * Real.exp (π * R) ≤ Real.exp (π * χ) := by
    have h1 : 8 ≤ Real.exp (2 * π) := by
      have : 2 ≤ Real.exp 1 := by linarith [Real.add_one_lt_exp (one_ne_zero)]
      have hexp3 : 8 ≤ Real.exp 3 := by
        rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]; nlinarith
      exact hexp3.trans (Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three]))
    calc 8 * Real.exp (π * R) ≤ Real.exp (2 * π) * Real.exp (π * R) := by gcongr
      _ = Real.exp (π * (R + 2)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (π * χ) := Real.exp_le_exp.mpr (by nlinarith)
  have hbd_each : ∀ η : ℝ, |η| ≤ 1 / 8 →
      ‖blaschkeT ((χ : ℂ) + (η : ℂ) * Complex.I) b + 1‖ ≤
        8 * Real.exp (π * R) * Real.exp (-π * χ) := by
    intro η hη
    set ζ : ℂ := (χ : ℂ) + (η : ℂ) * Complex.I
    have hζ_re : |ζ.re| = χ := by simp [ζ, abs_of_nonneg hχ]
    have hc_b : ‖Complex.cosh ((π : ℂ) * b)‖ ≤ Real.exp (π * R) :=
      (norm_cosh_le_exp b).trans (Real.exp_le_exp.mpr (by nlinarith))
    have hc_ζ : Real.exp (π * χ) / 2 - 1 ≤ ‖Complex.cosh ((π : ℂ) * ζ)‖ := by
      simpa [hζ_re] using norm_cosh_ge_half_exp_sub ζ
    have hc_ge : Real.exp (π * χ) / 4 ≤ ‖Complex.cosh ((π : ℂ) * ζ)‖ - ‖Complex.cosh ((π : ℂ) * b)‖ := by
      have hR_ge : 1 ≤ Real.exp (π * R) := Real.one_le_exp (by positivity)
      linarith
    have hden_ge : Real.exp (π * χ) / 4 ≤
        ‖Complex.cosh ((π : ℂ) * b) + Complex.cosh ((π : ℂ) * ζ)‖ := by
      have htri : ‖Complex.cosh ((π : ℂ) * ζ)‖ - ‖Complex.cosh ((π : ℂ) * b)‖ ≤
          ‖Complex.cosh ((π : ℂ) * b) + Complex.cosh ((π : ℂ) * ζ)‖ := by
        have := norm_add_le (Complex.cosh ((π : ℂ) * b) + Complex.cosh ((π : ℂ) * ζ))
          (-Complex.cosh ((π : ℂ) * b))
        simp only [norm_neg, add_neg_cancel_comm] at this
        linarith
      exact hc_ge.trans htri
    have hden_pos : 0 < ‖Complex.cosh ((π : ℂ) * b) + Complex.cosh ((π : ℂ) * ζ)‖ :=
      lt_of_lt_of_le (by positivity) hden_ge
    have hden_ne : Complex.cosh ((π : ℂ) * b) + Complex.cosh ((π : ℂ) * ζ) ≠ 0 :=
      norm_pos_iff.mp hden_pos
    rw [blaschkeT_add_one_eq hden_ne, norm_div, norm_mul, Complex.norm_ofNat]
    calc 2 * ‖Complex.cosh ((π : ℂ) * b)‖ /
          ‖Complex.cosh ((π : ℂ) * b) + Complex.cosh ((π : ℂ) * ζ)‖
        ≤ (2 * Real.exp (π * R)) / (Real.exp (π * χ) / 4) := by gcongr
      _ = 8 * Real.exp (π * R) * Real.exp (-π * χ) := by
          rw [show -π * χ = -(π * χ) by ring, Real.exp_neg]; field_simp; ring
  have hpos := hbd_each ε hε
  have hneg := hbd_each (-ε) (by simpa using hε)
  set A := blaschkeT ((χ : ℂ) + (ε : ℂ) * Complex.I) b
  set B := blaschkeT ((χ : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I) b
  have hB_eq : B = blaschkeT ((χ : ℂ) - (ε : ℂ) * Complex.I) b := by
    dsimp [B]
    rw [show (χ : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I = (χ : ℂ) - (ε : ℂ) * Complex.I by
      push_cast; ring]
  rw [← hB_eq]
  have hid : A * B - 1 = (A + 1) * (B + 1) - (A + 1) - (B + 1) := by ring
  have hsmall : 8 * Real.exp (π * R) * Real.exp (-π * χ) ≤ 1 := by
    rw [show -π * χ = -(π * χ) by ring, Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
    linarith
  calc ‖A * B - 1‖
      = ‖(A + 1) * (B + 1) - (A + 1) - (B + 1)‖ := by rw [hid]
    _ ≤ ‖(A + 1) * (B + 1) - (A + 1)‖ + ‖B + 1‖ := norm_sub_le _ _
    _ ≤ ‖(A + 1) * (B + 1)‖ + ‖A + 1‖ + ‖B + 1‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ‖A + 1‖ * ‖B + 1‖ + ‖A + 1‖ + ‖B + 1‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ 1 * ‖B + 1‖ + ‖A + 1‖ + ‖B + 1‖ := by gcongr; exact hpos.trans hsmall
    _ ≤ 1 * (8 * Real.exp (π * R) * Real.exp (-π * χ)) +
          8 * Real.exp (π * R) * Real.exp (-π * χ) +
          8 * Real.exp (π * R) * Real.exp (-π * χ) := by gcongr
    _ ≤ 32 * Real.exp (π * R) * Real.exp (-π * χ) := by
          have : 0 ≤ Real.exp (π * R) * Real.exp (-π * χ) := by positivity
          linarith

/-- **K1(a), infinite-product convergence**: for any sites $\chi_k \ge 0$ with
$\sum_k e^{-\pi \chi_k} < \infty$ and widths $|\varepsilon_k| \le 1/8$, the pair product
converges locally uniformly on $\{|\operatorname{Im} b| < 7/8\}$ to a holomorphic function $P$,
satisfying $\|P(b)\| \le 1$ on $|\operatorname{Im} b| \le 1/2$, $\|P(b)\| = 1$ on $|\operatorname{Im} b| = 1/2$,
and $P(i/2) = 1$. -/
theorem comb_pairProd_hasProdLocallyUniformlyOn
    (χ ε : ℕ → ℝ) (hχ : ∀ k, 0 ≤ χ k) (hε : ∀ k, |ε k| ≤ 1 / 8)
    (hsum : Summable fun k => Real.exp (-π * χ k)) :
    HasProdLocallyUniformlyOn
      (fun k b => blaschkeT ((χ k : ℂ) + (ε k : ℂ) * Complex.I) b *
        blaschkeT ((χ k : ℂ) - (ε k : ℂ) * Complex.I) b)
      (fun b => ∏' k, (blaschkeT ((χ k : ℂ) + (ε k : ℂ) * Complex.I) b *
        blaschkeT ((χ k : ℂ) - (ε k : ℂ) * Complex.I) b))
      {b : ℂ | |b.im| < 7 / 8} := by
  have hopen : IsOpen {b : ℂ | |b.im| < 7 / 8} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  set f : ℕ → ℂ → ℂ := fun k b =>
    blaschkeT ((χ k : ℂ) + (ε k : ℂ) * Complex.I) b *
      blaschkeT ((χ k : ℂ) - (ε k : ℂ) * Complex.I) b
  have key : HasProdLocallyUniformlyOn (fun k b => 1 + (f k b - 1))
      (fun b => ∏' k, (1 + (f k b - 1))) {b : ℂ | |b.im| < 7 / 8} := by
    apply hasProdLocallyUniformlyOn_of_forall_compact hopen
    intro K hK_sub hK_comp
    obtain ⟨r₀, hr₀⟩ := hK_comp.isBounded.exists_norm_le
    set R := max r₀ 0
    have hR : 0 ≤ R := le_max_right _ _
    have h_ev : ∀ᶠ k in cofinite, R + 2 ≤ χ k := by
      have ht := hsum.tendsto_cofinite_zero
      have hpos : 0 < Real.exp (-π * (R + 2)) := Real.exp_pos _
      filter_upwards [ht.eventually (gt_mem_nhds hpos)] with k hk
      by_contra hlt
      push Not at hlt
      have : Real.exp (-π * (R + 2)) ≤ Real.exp (-π * χ k) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      linarith
    refine Summable.hasProdUniformlyOn_one_add hK_comp
      (u := fun k => 32 * Real.exp (π * R) * Real.exp (-π * χ k))
      (hsum.mul_left _) ?_ (fun k => ?_)
    · filter_upwards [h_ev] with k hk b hb
      have hbR : |b.re| ≤ R := (Complex.abs_re_le_norm b).trans ((hr₀ b hb).trans (le_max_left _ _))
      exact blaschkeT_pair_sub_one_le (hε k) (hχ k) hR hbR hk
    · have hdiff : DifferentiableOn ℂ (fun b => f k b - 1) K := by
        intro b hb
        have hbm : |b.im| < 7 / 8 := hK_sub hb
        have h1 : DifferentiableAt ℂ (blaschkeT ((χ k : ℂ) + (ε k : ℂ) * Complex.I)) b :=
          differentiableAt_blaschkeT (by
            have him : |((χ k : ℂ) + (ε k : ℂ) * Complex.I).im| ≤ 1 / 8 := by simpa using hε k
            linarith)
        have h2 : DifferentiableAt ℂ (blaschkeT ((χ k : ℂ) - (ε k : ℂ) * Complex.I)) b :=
          differentiableAt_blaschkeT (by
            have him : |((χ k : ℂ) - (ε k : ℂ) * Complex.I).im| ≤ 1 / 8 := by
              simpa [abs_neg] using hε k
            linarith)
        exact ((h1.mul h2).sub_const 1).differentiableWithinAt
      exact hdiff.continuousOn
  simpa only [add_sub_cancel] using key

theorem comb_pairProd_differentiableOn
    (χ ε : ℕ → ℝ) (hχ : ∀ k, 0 ≤ χ k) (hε : ∀ k, |ε k| ≤ 1 / 8)
    (hsum : Summable fun k => Real.exp (-π * χ k)) :
    DifferentiableOn ℂ
      (fun b => ∏' k, (blaschkeT ((χ k : ℂ) + (ε k : ℂ) * Complex.I) b *
        blaschkeT ((χ k : ℂ) - (ε k : ℂ) * Complex.I) b))
      {b : ℂ | |b.im| < 7 / 8} := by
  have hopen : IsOpen {b : ℂ | |b.im| < 7 / 8} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  apply (comb_pairProd_hasProdLocallyUniformlyOn χ ε hχ hε hsum).differentiableOn _ hopen
  filter_upwards with s
  intro b hb
  have hbm : |b.im| < 7 / 8 := hb
  refine DifferentiableAt.differentiableWithinAt ?_
  change DifferentiableAt ℂ (fun z => ∏ k ∈ s, (blaschkeT ((χ k : ℂ) + (ε k : ℂ) * Complex.I) z *
    blaschkeT ((χ k : ℂ) - (ε k : ℂ) * Complex.I) z)) b
  refine DifferentiableAt.fun_finsetProd fun k _ => ?_
  have h1 : DifferentiableAt ℂ (blaschkeT ((χ k : ℂ) + (ε k : ℂ) * Complex.I)) b :=
    differentiableAt_blaschkeT (by
      have him : |((χ k : ℂ) + (ε k : ℂ) * Complex.I).im| ≤ 1 / 8 := by simpa using hε k
      linarith)
  have h2 : DifferentiableAt ℂ (blaschkeT ((χ k : ℂ) - (ε k : ℂ) * Complex.I)) b :=
    differentiableAt_blaschkeT (by
      have him : |((χ k : ℂ) - (ε k : ℂ) * Complex.I).im| ≤ 1 / 8 := by
        simpa [abs_neg] using hε k
      linarith)
  exact h1.mul h2

theorem comb_pairProd_norm_le_one
    (χ ε : ℕ → ℝ) (hχ : ∀ k, 0 ≤ χ k) (hε : ∀ k, |ε k| ≤ 1 / 8)
    (hsum : Summable fun k => Real.exp (-π * χ k)) {b : ℂ} (hb : |b.im| ≤ 1 / 2) :
    ‖∏' k, (blaschkeT ((χ k : ℂ) + (ε k : ℂ) * Complex.I) b *
      blaschkeT ((χ k : ℂ) - (ε k : ℂ) * Complex.I) b)‖ ≤ 1 := by
  have hb_mem : b ∈ {z : ℂ | |z.im| < 7 / 8} := lt_of_le_of_lt hb (by norm_num)
  have hp := (comb_pairProd_hasProdLocallyUniformlyOn χ ε hχ hε hsum).hasProd hb_mem
  have hnorm : Tendsto
      (fun s : Finset ℕ => ‖∏ k ∈ s, (blaschkeT ((χ k : ℂ) + (ε k : ℂ) * Complex.I) b *
        blaschkeT ((χ k : ℂ) - (ε k : ℂ) * Complex.I) b)‖)
      atTop
      (𝓝 ‖∏' k, (blaschkeT ((χ k : ℂ) + (ε k : ℂ) * Complex.I) b *
        blaschkeT ((χ k : ℂ) - (ε k : ℂ) * Complex.I) b)‖) :=
    continuous_norm.continuousAt.tendsto.comp hp
  refine le_of_tendsto hnorm (Eventually.of_forall fun s => ?_)
  rw [norm_prod]
  induction s using Finset.induction with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.prod_insert hk]
    exact (mul_le_mul (norm_pair_blaschkeT_le_one (χ k) (ε k) ((hε k).trans (by norm_num)) hb)
      ih (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem comb_pairProd_norm_eq_one
    (χ ε : ℕ → ℝ) (hχ : ∀ k, 0 ≤ χ k) (hε : ∀ k, |ε k| ≤ 1 / 8)
    (hsum : Summable fun k => Real.exp (-π * χ k)) {b : ℂ} (hb : |b.im| = 1 / 2) :
    ‖∏' k, (blaschkeT ((χ k : ℂ) + (ε k : ℂ) * Complex.I) b *
      blaschkeT ((χ k : ℂ) - (ε k : ℂ) * Complex.I) b)‖ = 1 := by
  have hb_mem : b ∈ {z : ℂ | |z.im| < 7 / 8} := by change |b.im| < 7 / 8; rw [hb]; norm_num
  have hp := (comb_pairProd_hasProdLocallyUniformlyOn χ ε hχ hε hsum).hasProd hb_mem
  have hnorm : Tendsto
      (fun s : Finset ℕ => ‖∏ k ∈ s, (blaschkeT ((χ k : ℂ) + (ε k : ℂ) * Complex.I) b *
        blaschkeT ((χ k : ℂ) - (ε k : ℂ) * Complex.I) b)‖)
      atTop
      (𝓝 ‖∏' k, (blaschkeT ((χ k : ℂ) + (ε k : ℂ) * Complex.I) b *
        blaschkeT ((χ k : ℂ) - (ε k : ℂ) * Complex.I) b)‖) :=
    continuous_norm.continuousAt.tendsto.comp hp
  have hconst : (fun s : Finset ℕ => ‖∏ k ∈ s, (blaschkeT ((χ k : ℂ) + (ε k : ℂ) * Complex.I) b *
      blaschkeT ((χ k : ℂ) - (ε k : ℂ) * Complex.I) b)‖) = fun _ => 1 := by
    ext s
    rw [norm_prod]
    exact Finset.prod_eq_one fun k _ =>
      norm_pair_blaschkeT_eq_one (χ k) (ε k) ((hε k).trans (by norm_num)) hb
  rw [hconst] at hnorm
  exact tendsto_nhds_unique hnorm tendsto_const_nhds

theorem comb_pairProd_half_I
    (χ ε : ℕ → ℝ) (hε : ∀ k, |ε k| ≤ 1 / 8) :
    (∏' k, (blaschkeT ((χ k : ℂ) + (ε k : ℂ) * Complex.I) (Complex.I / 2) *
      blaschkeT ((χ k : ℂ) - (ε k : ℂ) * Complex.I) (Complex.I / 2))) = 1 := by
  have hfac : ∀ k, blaschkeT ((χ k : ℂ) + (ε k : ℂ) * Complex.I) (Complex.I / 2) *
      blaschkeT ((χ k : ℂ) - (ε k : ℂ) * Complex.I) (Complex.I / 2) = 1 := by
    intro k
    have h1 : blaschkeT ((χ k : ℂ) + (ε k : ℂ) * Complex.I) (Complex.I / 2) = -1 :=
      blaschkeT_half_I (by simp; linarith [hε k])
    have h2 : blaschkeT ((χ k : ℂ) - (ε k : ℂ) * Complex.I) (Complex.I / 2) = -1 :=
      blaschkeT_half_I (by simp [abs_neg]; linarith [hε k])
    rw [h1, h2]; ring
  simp_rw [hfac, tprod_one]

/-! ### Section 3: Lemma K1(b) — Real-axis pair modulus and detuning `δ` -/

/-- Pair modulus on the real axis: $q = |T_{\chi+i\varepsilon}(x) T_{\chi-i\varepsilon}(x)|$. -/
noncomputable def blaschkePairQ (χ ε x : ℝ) : ℝ :=
  ‖blaschkeT ((χ : ℂ) + (ε : ℂ) * Complex.I) (x : ℂ) *
    blaschkeT ((χ : ℂ) - (ε : ℂ) * Complex.I) (x : ℂ)‖

/-- **K1(b), explicit formula**: $q = \prod_\pm \frac{\sinh^2 z_\pm + S^2}{\cosh^2 z_\pm - S^2}$. -/
theorem blaschkePairQ_eq (χ ε x : ℝ) :
    blaschkePairQ χ ε x =
      ((Real.sinh (π * (x - χ) / 2) ^ 2 + Real.sin (π * ε / 2) ^ 2) /
          (Real.cosh (π * (x - χ) / 2) ^ 2 - Real.sin (π * ε / 2) ^ 2)) *
        ((Real.sinh (π * (x + χ) / 2) ^ 2 + Real.sin (π * ε / 2) ^ 2) /
          (Real.cosh (π * (x + χ) / 2) ^ 2 - Real.sin (π * ε / 2) ^ 2)) := by
  unfold blaschkePairQ
  have hconj : blaschkeT ((χ : ℂ) - (ε : ℂ) * Complex.I) (x : ℂ) =
      starRingEnd ℂ (blaschkeT ((χ : ℂ) + (ε : ℂ) * Complex.I) (x : ℂ)) := by
    rw [← blaschkeT_conj, Complex.conj_ofReal]
    congr 1
    simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, sub_eq_add_neg]
  rw [hconj, norm_mul, Complex.norm_conj, ← sq]
  unfold blaschkeT
  rw [norm_mul, mul_pow]
  have h1 : ‖Complex.tanh ((π : ℂ) * ((x : ℂ) - ((χ : ℂ) + (ε : ℂ) * Complex.I)) / 2)‖ ^ 2 =
      (Real.sinh (π * (x - χ) / 2) ^ 2 + Real.sin (π * ε / 2) ^ 2) /
        (Real.cosh (π * (x - χ) / 2) ^ 2 - Real.sin (π * ε / 2) ^ 2) := by
    rw [norm_tanh_sq_eq]
    have hre : ((π : ℂ) * ((x : ℂ) - ((χ : ℂ) + (ε : ℂ) * Complex.I)) / 2).re =
        π * (x - χ) / 2 := by
      simp [Complex.mul_re]
    have him : ((π : ℂ) * ((x : ℂ) - ((χ : ℂ) + (ε : ℂ) * Complex.I)) / 2).im =
        -(π * ε / 2) := by
      simp [Complex.mul_im]; ring
    rw [hre, him, Real.sin_neg, neg_sq]
  have h2 : ‖Complex.tanh ((π : ℂ) * ((x : ℂ) + ((χ : ℂ) + (ε : ℂ) * Complex.I)) / 2)‖ ^ 2 =
      (Real.sinh (π * (x + χ) / 2) ^ 2 + Real.sin (π * ε / 2) ^ 2) /
        (Real.cosh (π * (x + χ) / 2) ^ 2 - Real.sin (π * ε / 2) ^ 2) := by
    rw [norm_tanh_sq_eq]
    have hre : ((π : ℂ) * ((x : ℂ) + ((χ : ℂ) + (ε : ℂ) * Complex.I)) / 2).re =
        π * (x + χ) / 2 := by
      simp [Complex.mul_re]
    have him : ((π : ℂ) * ((x : ℂ) + ((χ : ℂ) + (ε : ℂ) * Complex.I)) / 2).im =
        π * ε / 2 := by
      simp [Complex.mul_im]
    rw [hre, him]
  rw [h1, h2]

theorem blaschkePairQ_zero_eps (χ x : ℝ) :
    blaschkePairQ χ 0 x = (Real.tanh (π * (x - χ) / 2) * Real.tanh (π * (x + χ) / 2)) ^ 2 := by
  rw [blaschkePairQ_eq]
  simp [Real.tanh_eq_sinh_div_cosh]
  ring

/-- **K1(b), monotonicity**: $q$ increases with $\varepsilon \in [0, 1/2]$ and $q \ge T_\chi(x)^2$. -/
theorem blaschkePairQ_mono_eps (χ x : ℝ) {ε₁ ε₂ : ℝ} (hε₁ : 0 ≤ ε₁) (hε₁₂ : ε₁ ≤ ε₂)
    (hε₂ : ε₂ ≤ 1 / 2) :
    blaschkePairQ χ ε₁ x ≤ blaschkePairQ χ ε₂ x := by
  have hpi := Real.pi_pos
  have hS_le : Real.sin (π * ε₁ / 2) ^ 2 ≤ Real.sin (π * ε₂ / 2) ^ 2 := by
    have hs₁ : 0 ≤ Real.sin (π * ε₁ / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith)
    have hmono : Real.sin (π * ε₁ / 2) ≤ Real.sin (π * ε₂ / 2) :=
      Real.strictMonoOn_sin.monotoneOn
        ⟨by nlinarith, by nlinarith⟩ ⟨by nlinarith, by nlinarith⟩ (by nlinarith)
    nlinarith
  have hS_lt : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 2 → Real.sin (π * ε / 2) ^ 2 ≤ 1 / 2 := by
    intro ε h0 h2
    have hs : Real.sin (π * ε / 2) ≤ Real.sin (π / 4) :=
      Real.strictMonoOn_sin.monotoneOn
        ⟨by nlinarith, by nlinarith⟩ ⟨by nlinarith, by nlinarith⟩ (by nlinarith)
    have hs0 : 0 ≤ Real.sin (π * ε / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith)
    rw [Real.sin_pi_div_four] at hs
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hfac : ∀ z : ℝ,
      (Real.sinh z ^ 2 + Real.sin (π * ε₁ / 2) ^ 2) /
          (Real.cosh z ^ 2 - Real.sin (π * ε₁ / 2) ^ 2) ≤
        (Real.sinh z ^ 2 + Real.sin (π * ε₂ / 2) ^ 2) /
          (Real.cosh z ^ 2 - Real.sin (π * ε₂ / 2) ^ 2) ∧
        0 ≤ (Real.sinh z ^ 2 + Real.sin (π * ε₁ / 2) ^ 2) /
          (Real.cosh z ^ 2 - Real.sin (π * ε₁ / 2) ^ 2) := by
    intro z
    have hc1 : 1 ≤ Real.cosh z ^ 2 := by have := Real.one_le_cosh z; nlinarith
    have hden1 : 0 < Real.cosh z ^ 2 - Real.sin (π * ε₁ / 2) ^ 2 := by
      linarith [hS_lt ε₁ hε₁ (hε₁₂.trans hε₂)]
    have hden2 : 0 < Real.cosh z ^ 2 - Real.sin (π * ε₂ / 2) ^ 2 := by
      linarith [hS_lt ε₂ (hε₁.trans hε₁₂) hε₂]
    constructor
    · rw [div_le_div_iff₀ hden1 hden2]
      have hcs : Real.cosh z ^ 2 = Real.sinh z ^ 2 + 1 := by
        linarith [Real.cosh_sq_sub_sinh_sq z]
      rw [hcs]
      nlinarith [sq_nonneg (Real.sinh z)]
    · positivity
  rw [blaschkePairQ_eq, blaschkePairQ_eq]
  have hf1 := hfac (π * (x - χ) / 2)
  have hf2 := hfac (π * (x + χ) / 2)
  exact mul_le_mul hf1.1 hf2.1 hf2.2 (hf1.2.trans hf1.1)

theorem blaschkePairQ_ge_sq (χ ε x : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) :
    (Real.tanh (π * (x - χ) / 2) * Real.tanh (π * (x + χ) / 2)) ^ 2 ≤ blaschkePairQ χ ε x := by
  rw [← blaschkePairQ_zero_eps]
  exact blaschkePairQ_mono_eps χ x le_rfl hε0 hε

/-- Detuning discrepancy $\delta = \log(q / T_\chi(x)^2)$. -/
noncomputable def deltaDetune (χ ε x : ℝ) : ℝ :=
  Real.log (blaschkePairQ χ ε x / (Real.tanh (π * (x - χ) / 2) * Real.tanh (π * (x + χ) / 2)) ^ 2)

private lemma neg_log_one_sub_le {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 0.04) :
    -Real.log (1 - u) ≤ 1.05 * u := by
  have hu1 : 0 < 1 - u := by linarith
  have h1 : Real.log (1 - u) = -Real.log ((1 - u)⁻¹) := by rw [Real.log_inv]; ring
  rw [h1, neg_neg]
  have hinv : (1 - u)⁻¹ = 1 + u / (1 - u) := by field_simp [hu1.ne']; ring
  rw [hinv]
  have hlog : Real.log (1 + u / (1 - u)) ≤ u / (1 - u) :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans_eq (by ring)
  have hbound : u / (1 - u) ≤ 1.05 * u := by
    rw [div_le_iff₀ hu1]
    nlinarith
  exact hlog.trans hbound

private lemma abs_le_sinh_abs (z : ℝ) : |z| ≤ |Real.sinh z| := by
  have hnn : ∀ t : ℝ, 0 ≤ t → t ≤ Real.sinh t := by
    intro t ht
    let g : ℝ → ℝ := fun x => Real.sinh x - x
    have hderiv : ∀ s : ℝ, HasDerivAt g (Real.cosh s - 1) s :=
      fun s => (Real.hasDerivAt_sinh s).sub (hasDerivAt_id s)
    have hmono : (0 : ℝ) ≤ g t := by
      have hm := monotoneOn_of_deriv_nonneg (f := g) (convex_Icc 0 t)
        (Real.continuous_sinh.sub continuous_id).continuousOn
        ((Real.differentiable_sinh.sub differentiable_id).differentiableOn.mono interior_subset)
        (fun s hs => by
          rw [(hderiv s).deriv]
          linarith [Real.one_le_cosh s])
      simpa [g] using hm (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht) ht
    exact sub_nonneg.mp hmono
  rcases le_or_gt 0 z with hz | hz
  · rw [abs_of_nonneg hz, abs_of_nonneg (Real.sinh_nonneg_iff.mpr hz)]
    exact hnn z hz
  · rw [abs_of_neg hz, abs_of_neg (Real.sinh_neg_iff.mpr hz), ← Real.sinh_neg]
    exact hnn (-z) (by linarith)

private lemma abs_le_cosh (z : ℝ) : |z| ≤ Real.cosh z := by
  have h2 : |z| ≤ 1 + z ^ 2 / 2 := by nlinarith [sq_nonneg (|z| - 1), sq_abs z]
  have h1 : 1 + z ^ 2 / 2 ≤ Real.cosh z := by
    let g : ℝ → ℝ := fun x => Real.cosh x - (1 + x ^ 2 / 2)
    have hderiv2 : ∀ t : ℝ, HasDerivAt g (Real.sinh t - t) t := by
      intro t
      have h := (Real.hasDerivAt_cosh t).sub ((hasDerivAt_const t (1 : ℝ)).add
        (((hasDerivAt_id t).pow 2).div_const 2))
      refine h.congr_deriv ?_
      simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      ring
    have hg_cont : Continuous g := Real.continuous_cosh.sub (continuous_const.add ((continuous_id.pow 2).div_const 2))
    have hg_diff : Differentiable ℝ g := Real.differentiable_cosh.sub ((differentiable_const 1).add ((differentiable_id.pow 2).div_const 2))
    rcases le_or_gt 0 z with hz | hz
    · have hm := monotoneOn_of_deriv_nonneg (f := g) (convex_Icc 0 z)
        hg_cont.continuousOn (hg_diff.differentiableOn.mono interior_subset)
        (fun s hs => by
          rw [(hderiv2 s).deriv]
          rw [interior_Icc] at hs
          have hs0 : 0 ≤ s := hs.1.le
          have hle := abs_le_sinh_abs s
          rw [abs_of_nonneg hs0, abs_of_nonneg (Real.sinh_nonneg_iff.mpr hs0)] at hle
          exact sub_nonneg.mpr hle)
      have h0 := hm (left_mem_Icc.mpr hz) (right_mem_Icc.mpr hz) hz
      dsimp [g] at h0
      simp only [Real.cosh_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        zero_div, add_zero, sub_self] at h0
      linarith
    · have hnn : 1 + (-z) ^ 2 / 2 ≤ Real.cosh (-z) := by
        have hm := monotoneOn_of_deriv_nonneg (f := g) (convex_Icc 0 (-z))
          hg_cont.continuousOn (hg_diff.differentiableOn.mono interior_subset)
          (fun s hs => by
            rw [(hderiv2 s).deriv]
            rw [interior_Icc] at hs
            have hs0 : 0 ≤ s := hs.1.le
            have hle := abs_le_sinh_abs s
            rw [abs_of_nonneg hs0, abs_of_nonneg (Real.sinh_nonneg_iff.mpr hs0)] at hle
            exact sub_nonneg.mpr hle)
        have h0 := hm (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith)) (by linarith)
        dsimp [g] at h0
        simp only [Real.cosh_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          zero_div, add_zero, sub_self] at h0
        linarith
      rwa [Real.cosh_neg, neg_sq] at hnn
  exact h2.trans h1

private lemma deltaDetune_split (χ ε x : ℝ) (hχ : 0 ≤ χ) (hx : 0 ≤ x) (hd : x ≠ χ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 8) :
    deltaDetune χ ε x =
      Real.log (1 + Real.sin (π * ε / 2) ^ 2 / Real.sinh (π * (x - χ) / 2) ^ 2) -
        Real.log (1 - Real.sin (π * ε / 2) ^ 2 / Real.cosh (π * (x - χ) / 2) ^ 2) +
        Real.log (1 + Real.sin (π * ε / 2) ^ 2 / Real.sinh (π * (x + χ) / 2) ^ 2) -
        Real.log (1 - Real.sin (π * ε / 2) ^ 2 / Real.cosh (π * (x + χ) / 2) ^ 2) := by
  have hpi := Real.pi_pos
  set z₁ := π * (x - χ) / 2
  set z₂ := π * (x + χ) / 2
  set S := Real.sin (π * ε / 2)
  have hxχ : 0 < x + χ := lt_of_le_of_ne (add_nonneg hx hχ) (fun h0 => hd (by linarith))
  have hz₁_ne : z₁ ≠ 0 := by dsimp [z₁]; exact div_ne_zero (mul_ne_zero hpi.ne' (sub_ne_zero.mpr hd)) two_ne_zero
  have hz₂_pos : 0 < z₂ := by dsimp [z₂]; positivity
  have hsh₁_ne : Real.sinh z₁ ≠ 0 := Real.sinh_ne_zero.mpr hz₁_ne
  have hsh₂_ne : Real.sinh z₂ ≠ 0 := (Real.sinh_pos_iff.mpr hz₂_pos).ne'
  have hch₁_pos : 0 < Real.cosh z₁ := Real.cosh_pos _
  have hch₂_pos : 0 < Real.cosh z₂ := Real.cosh_pos _
  have hS_sq : S ^ 2 ≤ 0.04 := by
    have h1 : |S| ≤ π * ε / 2 := by
      dsimp [S]
      rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
        (by nlinarith only [hpi, hε0, hε]))]
      exact Real.sin_le (by positivity)
    have h2 : |S| ≤ π / 16 := h1.trans (by nlinarith only [hpi, hε0, hε])
    have h3 : S ^ 2 ≤ (π / 16) ^ 2 := by
      rw [← sq_abs S]; exact pow_le_pow_left₀ (abs_nonneg S) h2 2
    nlinarith only [Real.pi_lt_d4, hpi, h3]
  have hu₁_pos : 0 < 1 - S ^ 2 / Real.cosh z₁ ^ 2 := by
    have : S ^ 2 / Real.cosh z₁ ^ 2 ≤ S ^ 2 := div_le_self (sq_nonneg _) (by nlinarith only [Real.one_le_cosh z₁])
    linarith
  have hu₂_pos : 0 < 1 - S ^ 2 / Real.cosh z₂ ^ 2 := by
    have : S ^ 2 / Real.cosh z₂ ^ 2 ≤ S ^ 2 := div_le_self (sq_nonneg _) (by nlinarith only [Real.one_le_cosh z₂])
    linarith
  have hv₁_pos : 0 < 1 + S ^ 2 / Real.sinh z₁ ^ 2 := by positivity
  have hv₂_pos : 0 < 1 + S ^ 2 / Real.sinh z₂ ^ 2 := by positivity
  have hq_ratio : blaschkePairQ χ ε x / (Real.tanh z₁ * Real.tanh z₂) ^ 2 =
      ((1 + S ^ 2 / Real.sinh z₁ ^ 2) / (1 - S ^ 2 / Real.cosh z₁ ^ 2)) *
        ((1 + S ^ 2 / Real.sinh z₂ ^ 2) / (1 - S ^ 2 / Real.cosh z₂ ^ 2)) := by
    rw [blaschkePairQ_eq, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
    field_simp [hsh₁_ne, hsh₂_ne, hch₁_pos.ne', hch₂_pos.ne']
    ring
  unfold deltaDetune
  rw [hq_ratio, Real.log_mul (by positivity) (by positivity),
    Real.log_div hv₁_pos.ne' hu₁_pos.ne', Real.log_div hv₂_pos.ne' hu₂_pos.ne']
  ring

/-- **K1(b), detuning bounds**:
1. $0 \le \delta \le 5 \varepsilon^2 / d^2$ for all $\chi \ge 0$, $x \ge 0$, $d = |x - \chi| > 0$,
   $0 \le \varepsilon \le 1/8$. -/
theorem deltaDetune_bounds_universal {χ ε x : ℝ} (hχ : 0 ≤ χ) (hx : 0 ≤ x) (hd : x ≠ χ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 8) :
    0 ≤ deltaDetune χ ε x ∧ deltaDetune χ ε x ≤ 5 * ε ^ 2 / (x - χ) ^ 2 := by
  have hpi := Real.pi_pos
  have hnonneg : 0 ≤ deltaDetune χ ε x := by
    unfold deltaDetune
    have hq := blaschkePairQ_ge_sq χ ε x hε0 (hε.trans (by norm_num))
    have ht_pos : 0 < (Real.tanh (π * (x - χ) / 2) * Real.tanh (π * (x + χ) / 2)) ^ 2 := by
      have h1 : Real.tanh (π * (x - χ) / 2) ≠ 0 := by
        rw [Real.tanh_eq_sinh_div_cosh, div_ne_zero_iff]
        exact ⟨Real.sinh_ne_zero.mpr (div_ne_zero (mul_ne_zero hpi.ne' (sub_ne_zero.mpr hd)) two_ne_zero),
          (Real.cosh_pos _).ne'⟩
      have h2 : Real.tanh (π * (x + χ) / 2) ≠ 0 := by
        have hxχ : 0 < x + χ := lt_of_le_of_ne (add_nonneg hx hχ) (fun h0 => hd (by linarith))
        rw [Real.tanh_eq_sinh_div_cosh, div_ne_zero_iff]
        exact ⟨(Real.sinh_pos_iff.mpr (by positivity)).ne', (Real.cosh_pos _).ne'⟩
      positivity
    exact Real.log_nonneg ((one_le_div ht_pos).mpr hq)
  refine ⟨hnonneg, ?_⟩
  rw [deltaDetune_split χ ε x hχ hx hd hε0 hε]
  set z₁ := π * (x - χ) / 2
  set z₂ := π * (x + χ) / 2
  set S := Real.sin (π * ε / 2)
  have hS_bd : S ^ 2 ≤ (π * ε / 2) ^ 2 := by
    have h0 : 0 ≤ S := Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith only [hpi, hε0, hε])
    have h1 : S ≤ π * ε / 2 := Real.sin_le (by positivity)
    exact pow_le_pow_left₀ h0 h1 2
  have hS_04 : S ^ 2 ≤ 0.04 := by
    have hpi4 : π ≤ 3.15 := by linarith [Real.pi_lt_d4]
    have : (π * ε / 2) ^ 2 ≤ (3.15 / 16) ^ 2 := by
      have hpe : 0 ≤ π * ε / 2 := by positivity
      have hpe_le : π * ε / 2 ≤ 3.15 / 16 := by nlinarith only [hpi, hε, hpi4]
      exact pow_le_pow_left₀ hpe hpe_le 2
    linarith only [hS_bd, this]
  have hd_pos : 0 < (x - χ) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hd)
  have hz₁_sq : (π * (x - χ) / 2) ^ 2 ≤ Real.sinh z₁ ^ 2 := by
    have := abs_le_sinh_abs z₁
    rw [← sq_abs z₁, ← sq_abs (Real.sinh z₁)]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hz₂_sq : (π * (x - χ) / 2) ^ 2 ≤ Real.sinh z₂ ^ 2 := by
    have h1 : |x - χ| ≤ x + χ := by rw [abs_le]; constructor <;> linarith
    have h2 : z₁ ^ 2 ≤ z₂ ^ 2 := by
      have : |z₁| ≤ z₂ := by
        dsimp [z₁, z₂]
        rw [abs_div, abs_mul, abs_of_pos hpi, abs_two]
        gcongr
      rw [← sq_abs z₁]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have := abs_le_sinh_abs z₂
    have hz₂_sinh : z₂ ^ 2 ≤ Real.sinh z₂ ^ 2 := by
      rw [← sq_abs z₂, ← sq_abs (Real.sinh z₂)]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    exact h2.trans hz₂_sinh
  have hch₁_sq : (π * (x - χ) / 2) ^ 2 ≤ Real.cosh z₁ ^ 2 := by
    have := abs_le_cosh z₁
    change z₁ ^ 2 ≤ Real.cosh z₁ ^ 2
    rw [← sq_abs z₁]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hch₂_sq : (π * (x - χ) / 2) ^ 2 ≤ Real.cosh z₂ ^ 2 := by
    have h1 : |x - χ| ≤ x + χ := by rw [abs_le]; constructor <;> linarith
    have h2 : z₁ ^ 2 ≤ z₂ ^ 2 := by
      have : |z₁| ≤ z₂ := by
        dsimp [z₁, z₂]
        rw [abs_div, abs_mul, abs_of_pos hpi, abs_two]
        gcongr
      rw [← sq_abs z₁]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have := abs_le_cosh z₂
    have hz₂_ch : z₂ ^ 2 ≤ Real.cosh z₂ ^ 2 := by
      rw [← sq_abs z₂]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    exact h2.trans hz₂_ch
  have hpi2_pos : 0 < (π * (x - χ) / 2) ^ 2 := by positivity
  have hratio : S ^ 2 / (π * (x - χ) / 2) ^ 2 ≤ ε ^ 2 / (x - χ) ^ 2 := by
    calc S ^ 2 / (π * (x - χ) / 2) ^ 2
        ≤ (π * ε / 2) ^ 2 / (π * (x - χ) / 2) ^ 2 := by gcongr
      _ = ε ^ 2 / (x - χ) ^ 2 := by field_simp [hpi.ne', sub_ne_zero.mpr hd]
  have l1 : Real.log (1 + S ^ 2 / Real.sinh z₁ ^ 2) ≤ ε ^ 2 / (x - χ) ^ 2 :=
    ((Real.log_le_sub_one_of_pos (by positivity)).trans_eq (by ring)).trans
      ((div_le_div_of_nonneg_left (sq_nonneg S) hpi2_pos hz₁_sq).trans hratio)
  have l2 : Real.log (1 + S ^ 2 / Real.sinh z₂ ^ 2) ≤ ε ^ 2 / (x - χ) ^ 2 :=
    ((Real.log_le_sub_one_of_pos (by positivity)).trans_eq (by ring)).trans
      ((div_le_div_of_nonneg_left (sq_nonneg S) hpi2_pos hz₂_sq).trans hratio)
  have hc_pos : 0 < Real.cosh z₁ ^ 2 := pow_pos (Real.cosh_pos _) 2
  have hc2_pos : 0 < Real.cosh z₂ ^ 2 := pow_pos (Real.cosh_pos _) 2
  have m1 : -Real.log (1 - S ^ 2 / Real.cosh z₁ ^ 2) ≤ 1.05 * (ε ^ 2 / (x - χ) ^ 2) := by
    refine (neg_log_one_sub_le (by positivity) ?_).trans ?_
    · exact (div_le_self (sq_nonneg _) (by nlinarith only [Real.one_le_cosh z₁])).trans hS_04
    · exact mul_le_mul_of_nonneg_left
        ((div_le_div_of_nonneg_left (sq_nonneg S) hpi2_pos hch₁_sq).trans hratio) (by norm_num)
  have m2 : -Real.log (1 - S ^ 2 / Real.cosh z₂ ^ 2) ≤ 1.05 * (ε ^ 2 / (x - χ) ^ 2) := by
    refine (neg_log_one_sub_le (by positivity) ?_).trans ?_
    · exact (div_le_self (sq_nonneg _) (by nlinarith only [Real.one_le_cosh z₂])).trans hS_04
    · exact mul_le_mul_of_nonneg_left
        ((div_le_div_of_nonneg_left (sq_nonneg S) hpi2_pos hch₂_sq).trans hratio) (by norm_num)
  linarith [show (4.1 : ℝ) * (ε ^ 2 / (x - χ) ^ 2) ≤ 5 * ε ^ 2 / (x - χ) ^ 2 by
    rw [mul_div_assoc']; gcongr; norm_num]

/-- **K1(b), refined detuning bound for $\chi \ge \xi_*$**:
$\delta \le \varepsilon^2 / d^2 + C \varepsilon^2 e^{-\pi d}$. -/
theorem deltaDetune_le_of_xiStar_le :
    ∃ C > 0, ∀ {χ ε x : ℝ}, xiStar ≤ χ → 0 ≤ x → x ≠ χ → 0 ≤ ε → ε ≤ 1 / 8 →
      deltaDetune χ ε x ≤ ε ^ 2 / (x - χ) ^ 2 + C * ε ^ 2 * Real.exp (-π * |x - χ|) := by
  have hpi := Real.pi_pos
  have hsh_xi : 0 < Real.sinh (π * xiStar / 2) :=
    Real.sinh_pos_iff.mpr (mul_pos (mul_pos hpi xiStar_pos) (by norm_num))
  set c_sh := (Real.sinh (π * xiStar / 2) / Real.exp (π * xiStar / 2)) ^ 2
  have hc_sh : 0 < c_sh := by positivity
  -- On `z ≥ π * xiStar / 2`, `sinh z / exp z = (1 - exp (-2z)) / 2 ≥ sinh (π * xiStar / 2) / exp (π * xiStar / 2)`
  have hsh_exp : ∀ z : ℝ, π * xiStar / 2 ≤ z → c_sh * Real.exp (2 * z) ≤ Real.sinh z ^ 2 := by
    intro z hz
    have he1 : Real.exp (-(2 * z)) ≤ Real.exp (-(2 * (π * xiStar / 2))) :=
      Real.exp_le_exp.mpr (by linarith)
    have hquot : Real.sinh (π * xiStar / 2) / Real.exp (π * xiStar / 2) ≤
        Real.sinh z / Real.exp z := by
      have hid : ∀ t : ℝ, Real.sinh t / Real.exp t = (1 - Real.exp (-(2 * t))) / 2 := by
        intro t
        rw [Real.sinh_eq, div_div, mul_comm 2 (Real.exp t), ← div_div, sub_div,
          div_self (Real.exp_pos t).ne', ← Real.exp_sub]
        ring_nf
      rw [hid, hid]; linarith
    have hsq : c_sh ≤ (Real.sinh z / Real.exp z) ^ 2 := by
      have h0 : 0 ≤ Real.sinh (π * xiStar / 2) / Real.exp (π * xiStar / 2) := by positivity
      exact pow_le_pow_left₀ h0 hquot 2
    rw [div_pow, le_div_iff₀ (pow_pos (Real.exp_pos _) 2)] at hsq
    rwa [← Real.exp_nat_mul, show (2 : ℕ) * z = 2 * z by ring] at hsq
  set C := (π ^ 2 / 4) * (1 / c_sh + 1.05 * 8)
  refine ⟨C, by positivity, fun {χ ε x} hχ hx hd hε0 hε => ?_⟩
  have hχ0 : 0 ≤ χ := xiStar_pos.le.trans hχ
  rw [deltaDetune_split χ ε x hχ0 hx hd hε0 hε]
  set z₁ := π * (x - χ) / 2
  set z₂ := π * (x + χ) / 2
  set S := Real.sin (π * ε / 2)
  have hS_bd : S ^ 2 ≤ (π * ε / 2) ^ 2 := by
    have h0 : 0 ≤ S := Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith only [hpi, hε0, hε])
    have h1 : S ≤ π * ε / 2 := Real.sin_le (by positivity)
    exact pow_le_pow_left₀ h0 h1 2
  have hS_04 : S ^ 2 ≤ 0.04 := by
    have hpi4 : π ≤ 3.15 := by linarith [Real.pi_lt_d4]
    have hpe : 0 ≤ π * ε / 2 := by positivity
    have hpe_le : π * ε / 2 ≤ 3.15 / 16 := by nlinarith only [hpi, hε, hpi4]
    nlinarith only [hS_bd, hpe, hpe_le]
  have hd_pos : 0 < (x - χ) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hd)
  have hz₁_sq : (π * (x - χ) / 2) ^ 2 ≤ Real.sinh z₁ ^ 2 := by
    have := abs_le_sinh_abs z₁
    rw [← sq_abs z₁, ← sq_abs (Real.sinh z₁)]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hpi2_pos : 0 < (π * (x - χ) / 2) ^ 2 := by positivity
  have hratio : S ^ 2 / (π * (x - χ) / 2) ^ 2 ≤ ε ^ 2 / (x - χ) ^ 2 := by
    calc S ^ 2 / (π * (x - χ) / 2) ^ 2
        ≤ (π * ε / 2) ^ 2 / (π * (x - χ) / 2) ^ 2 := by gcongr
      _ = ε ^ 2 / (x - χ) ^ 2 := by field_simp [hpi.ne', sub_ne_zero.mpr hd]
  have l1 : Real.log (1 + S ^ 2 / Real.sinh z₁ ^ 2) ≤ ε ^ 2 / (x - χ) ^ 2 :=
    ((Real.log_le_sub_one_of_pos (by positivity)).trans_eq (by ring)).trans
      ((div_le_div_of_nonneg_left (sq_nonneg S) hpi2_pos hz₁_sq).trans hratio)
  have h_abs_le : π * |x - χ| ≤ 2 * |z₁| := by
    dsimp [z₁]; rw [abs_div, abs_mul, abs_of_pos hpi, abs_two]; ring_nf; rfl
  have h_abs_le2 : π * |x - χ| ≤ 2 * z₂ := by
    have h1 : |x - χ| ≤ x + χ := by rw [abs_le]; constructor <;> linarith
    dsimp [z₂]; nlinarith only [hpi, h1]
  have hch_exp : ∀ z : ℝ, Real.exp (2 * |z|) / 4 ≤ Real.cosh z ^ 2 := by
    intro z
    have h1 : Real.exp |z| / 2 ≤ Real.cosh z := by
      have hc : Real.cosh |z| = Real.cosh z := by
        rcases le_or_gt 0 z with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_neg h, Real.cosh_neg]
      rw [← hc, Real.cosh_eq]
      linarith [Real.exp_pos (-|z|)]
    have h2 : (Real.exp |z| / 2) ^ 2 ≤ Real.cosh z ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    rwa [div_pow, ← Real.exp_nat_mul, show (2 : ℕ) * |z| = 2 * |z| by ring,
      show (2 : ℝ) ^ 2 = 4 by norm_num] at h2
  have hexp_d1 : Real.exp (-2 * |z₁|) ≤ Real.exp (-π * |x - χ|) :=
    Real.exp_le_exp.mpr (by linarith)
  have hexp_d2 : Real.exp (-2 * z₂) ≤ Real.exp (-π * |x - χ|) :=
    Real.exp_le_exp.mpr (by linarith)
  have l2 : Real.log (1 + S ^ 2 / Real.sinh z₂ ^ 2) ≤
      ((π ^ 2 / 4) / c_sh) * ε ^ 2 * Real.exp (-π * |x - χ|) := by
    have hz₂_lb : π * xiStar / 2 ≤ z₂ := by dsimp [z₂]; nlinarith only [hpi, hχ, hx]
    have hsh₂_lb : c_sh * Real.exp (2 * z₂) ≤ Real.sinh z₂ ^ 2 := hsh_exp z₂ hz₂_lb
    refine ((Real.log_le_sub_one_of_pos (by positivity)).trans_eq (add_sub_cancel_left 1 _)).trans ?_
    calc S ^ 2 / Real.sinh z₂ ^ 2
        ≤ (π * ε / 2) ^ 2 / (c_sh * Real.exp (2 * z₂)) := by gcongr
      _ = ((π ^ 2 / 4) / c_sh) * ε ^ 2 * Real.exp (-2 * z₂) := by
          rw [show -2 * z₂ = -(2 * z₂) by ring, Real.exp_neg]
          field_simp [hc_sh.ne', (Real.exp_pos (2 * z₂)).ne']
          ring
      _ ≤ ((π ^ 2 / 4) / c_sh) * ε ^ 2 * Real.exp (-π * |x - χ|) := by
          exact mul_le_mul_of_nonneg_left hexp_d2 (by positivity)
  have m_bound : ∀ z : ℝ, π * |x - χ| ≤ 2 * |z| →
      -Real.log (1 - S ^ 2 / Real.cosh z ^ 2) ≤
        (1.05 * 4 * (π ^ 2 / 4)) * ε ^ 2 * Real.exp (-π * |x - χ|) := by
    intro z hz
    refine (neg_log_one_sub_le (by positivity) ?_).trans ?_
    · exact (div_le_self (sq_nonneg _) (by nlinarith only [Real.one_le_cosh z])).trans hS_04
    · calc 1.05 * (S ^ 2 / Real.cosh z ^ 2)
          ≤ 1.05 * ((π * ε / 2) ^ 2 / (Real.exp (2 * |z|) / 4)) := by gcongr; exact hch_exp z
        _ = (1.05 * 4 * (π ^ 2 / 4)) * ε ^ 2 * Real.exp (-2 * |z|) := by
            rw [show -2 * |z| = -(2 * |z|) by ring, Real.exp_neg]; ring
        _ ≤ (1.05 * 4 * (π ^ 2 / 4)) * ε ^ 2 * Real.exp (-π * |x - χ|) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  have m1 := m_bound z₁ h_abs_le
  have hz₂_pos : 0 < z₂ := by
    have hxχ : 0 < x + χ := lt_of_le_of_ne (add_nonneg hx hχ0) (fun h0 => hd (by linarith))
    dsimp [z₂]; positivity
  have m2 := m_bound z₂ (by rw [abs_of_pos (a := z₂) hz₂_pos]; exact h_abs_le2)
  have hsum_C : ((π ^ 2 / 4) / c_sh) * ε ^ 2 * Real.exp (-π * |x - χ|) +
      (1.05 * 4 * (π ^ 2 / 4)) * ε ^ 2 * Real.exp (-π * |x - χ|) +
      (1.05 * 4 * (π ^ 2 / 4)) * ε ^ 2 * Real.exp (-π * |x - χ|) =
      C * ε ^ 2 * Real.exp (-π * |x - χ|) := by
    dsimp [C]; ring
  linarith

/-- **K1(b), exponential bound for $d \ge d_0 > 0$**:
for any $d_0 > 0$, $\delta \le C(d_0) \varepsilon^2 e^{-\pi d}$. -/
theorem deltaDetune_le_of_dist_ge {d₀ : ℝ} (hd₀ : 0 < d₀) :
    ∃ C > 0, ∀ {χ ε x : ℝ}, 0 ≤ χ → 0 ≤ x → d₀ ≤ |x - χ| → 0 ≤ ε → ε ≤ 1 / 8 →
      deltaDetune χ ε x ≤ C * ε ^ 2 * Real.exp (-π * |x - χ|) := by
  have hpi := Real.pi_pos
  set c_sh := (Real.sinh (π * d₀ / 2) / Real.exp (π * d₀ / 2)) ^ 2
  have hsh_d0 : 0 < Real.sinh (π * d₀ / 2) := Real.sinh_pos_iff.mpr (by positivity)
  have hc_sh : 0 < c_sh := by positivity
  have hsh_exp : ∀ z : ℝ, π * d₀ / 2 ≤ |z| → c_sh * Real.exp (2 * |z|) ≤ Real.sinh z ^ 2 := by
    intro z hz
    have hsq_abs : Real.sinh |z| ^ 2 = Real.sinh z ^ 2 := by
      rcases le_or_gt 0 z with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, Real.sinh_neg, neg_sq]
    rw [← hsq_abs]
    have hquot : Real.sinh (π * d₀ / 2) / Real.exp (π * d₀ / 2) ≤ Real.sinh |z| / Real.exp |z| := by
      have hid : ∀ t : ℝ, Real.sinh t / Real.exp t = (1 - Real.exp (-(2 * t))) / 2 := by
        intro t
        rw [Real.sinh_eq, div_div, mul_comm 2 (Real.exp t), ← div_div, sub_div,
          div_self (Real.exp_pos t).ne', ← Real.exp_sub]
        ring_nf
      rw [hid, hid]
      have : Real.exp (-(2 * |z|)) ≤ Real.exp (-(2 * (π * d₀ / 2))) := Real.exp_le_exp.mpr (by linarith)
      linarith
    have hsq : c_sh ≤ (Real.sinh |z| / Real.exp |z|) ^ 2 := by
      have : 0 ≤ Real.sinh (π * d₀ / 2) / Real.exp (π * d₀ / 2) := by positivity
      exact pow_le_pow_left₀ this hquot 2
    rw [div_pow, le_div_iff₀ (pow_pos (Real.exp_pos _) 2)] at hsq
    rwa [← Real.exp_nat_mul, show (2 : ℕ) * |z| = 2 * |z| by ring] at hsq
  set C := (π ^ 2 / 4) * (2 / c_sh + 1.05 * 8)
  refine ⟨C, by positivity, fun {χ ε x} hχ hx hd_ge hε0 hε => ?_⟩
  have hd : x ≠ χ := fun h => by subst h; simp at hd_ge; linarith
  rw [deltaDetune_split χ ε x hχ hx hd hε0 hε]
  set z₁ := π * (x - χ) / 2
  set z₂ := π * (x + χ) / 2
  set S := Real.sin (π * ε / 2)
  have hS_bd : S ^ 2 ≤ (π * ε / 2) ^ 2 := by
    have h0 : 0 ≤ S := Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith only [hpi, hε0, hε])
    have h1 : S ≤ π * ε / 2 := Real.sin_le (by positivity)
    exact pow_le_pow_left₀ h0 h1 2
  have hS_04 : S ^ 2 ≤ 0.04 := by
    have hpi4 : π ≤ 3.15 := by linarith [Real.pi_lt_d4]
    have hpe : 0 ≤ π * ε / 2 := by positivity
    have hpe_le : π * ε / 2 ≤ 3.15 / 16 := by nlinarith only [hpi, hε, hpi4]
    nlinarith only [hS_bd, hpe, hpe_le]
  have h_abs_le1 : π * |x - χ| ≤ 2 * |z₁| := by
    dsimp [z₁]; rw [abs_div, abs_mul, abs_of_pos hpi, abs_two]; ring_nf; rfl
  have h_abs_le2 : π * |x - χ| ≤ 2 * |z₂| := by
    have h1 : |x - χ| ≤ x + χ := by rw [abs_le]; constructor <;> linarith
    have hz₂_nn : 0 ≤ z₂ := by dsimp [z₂]; positivity
    rw [abs_of_nonneg hz₂_nn]; dsimp [z₂]; nlinarith only [hpi, h1]
  have hz₁_d0 : π * d₀ / 2 ≤ |z₁| := by nlinarith only [hpi, hd_ge, h_abs_le1]
  have hz₂_d0 : π * d₀ / 2 ≤ |z₂| := by nlinarith only [hpi, hd_ge, h_abs_le2]
  have hsh_bound : ∀ z : ℝ, π * d₀ / 2 ≤ |z| → π * |x - χ| ≤ 2 * |z| →
      Real.log (1 + S ^ 2 / Real.sinh z ^ 2) ≤ ((π ^ 2 / 4) / c_sh) * ε ^ 2 * Real.exp (-π * |x - χ|) := by
    intro z hzd hzx
    refine ((Real.log_le_sub_one_of_pos (by positivity)).trans_eq (add_sub_cancel_left 1 _)).trans ?_
    calc S ^ 2 / Real.sinh z ^ 2
        ≤ (π * ε / 2) ^ 2 / (c_sh * Real.exp (2 * |z|)) := by gcongr; exact hsh_exp z hzd
      _ = ((π ^ 2 / 4) / c_sh) * ε ^ 2 * Real.exp (-2 * |z|) := by
          rw [show -2 * |z| = -(2 * |z|) by ring, Real.exp_neg]
          field_simp [hc_sh.ne', (Real.exp_pos (2 * |z|)).ne']; ring
      _ ≤ ((π ^ 2 / 4) / c_sh) * ε ^ 2 * Real.exp (-π * |x - χ|) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  have hch_exp : ∀ z : ℝ, Real.exp (2 * |z|) / 4 ≤ Real.cosh z ^ 2 := by
    intro z
    have h1 : Real.exp |z| / 2 ≤ Real.cosh z := by
      have hc : Real.cosh |z| = Real.cosh z := by
        rcases le_or_gt 0 z with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_neg h, Real.cosh_neg]
      rw [← hc, Real.cosh_eq]; linarith [Real.exp_pos (-|z|)]
    have h2 : (Real.exp |z| / 2) ^ 2 ≤ Real.cosh z ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    rwa [div_pow, ← Real.exp_nat_mul, show (2 : ℕ) * |z| = 2 * |z| by ring,
      show (2 : ℝ) ^ 2 = 4 by norm_num] at h2
  have hch_bound : ∀ z : ℝ, π * |x - χ| ≤ 2 * |z| →
      -Real.log (1 - S ^ 2 / Real.cosh z ^ 2) ≤
        (1.05 * 4 * (π ^ 2 / 4)) * ε ^ 2 * Real.exp (-π * |x - χ|) := by
    intro z hzx
    refine (neg_log_one_sub_le (by positivity) ?_).trans ?_
    · exact (div_le_self (sq_nonneg _) (by nlinarith only [Real.one_le_cosh z])).trans hS_04
    · calc 1.05 * (S ^ 2 / Real.cosh z ^ 2)
          ≤ 1.05 * ((π * ε / 2) ^ 2 / (Real.exp (2 * |z|) / 4)) := by gcongr; exact hch_exp z
        _ = (1.05 * 4 * (π ^ 2 / 4)) * ε ^ 2 * Real.exp (-2 * |z|) := by
            rw [show -2 * |z| = -(2 * |z|) by ring, Real.exp_neg]; ring_nf
        _ ≤ (1.05 * 4 * (π ^ 2 / 4)) * ε ^ 2 * Real.exp (-π * |x - χ|) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  have l1 := hsh_bound z₁ hz₁_d0 h_abs_le1
  have l2 := hsh_bound z₂ hz₂_d0 h_abs_le2
  have m1 := hch_bound z₁ h_abs_le1
  have m2 := hch_bound z₂ h_abs_le2
  have hsum_C : ((π ^ 2 / 4) / c_sh) * ε ^ 2 * Real.exp (-π * |x - χ|) +
      ((π ^ 2 / 4) / c_sh) * ε ^ 2 * Real.exp (-π * |x - χ|) +
      (1.05 * 4 * (π ^ 2 / 4)) * ε ^ 2 * Real.exp (-π * |x - χ|) +
      (1.05 * 4 * (π ^ 2 / 4)) * ε ^ 2 * Real.exp (-π * |x - χ|) =
      C * ε ^ 2 * Real.exp (-π * |x - χ|) := by
    dsimp [C]; ring
  linarith

/-! ### Section 4: Lemma K1(c) — `combH` and `realLogT` -/

/-- $\mathfrak{h}(z) := \log \tanh(\pi z / 2)$ for real $z > 0$. -/
noncomputable def combH (z : ℝ) : ℝ := Real.log (Real.tanh (π * z / 2))

/-- First derivative $\mathfrak{h}'(z) = \pi / \sinh(\pi z)$. -/
noncomputable def combHDeriv (z : ℝ) : ℝ := π / Real.sinh (π * z)

/-- Second derivative $\mathfrak{h}''(z) = -\pi^2 \cosh(\pi z) / \sinh^2(\pi z)$. -/
noncomputable def combHSecond (z : ℝ) : ℝ := -π ^ 2 * Real.cosh (π * z) / Real.sinh (π * z) ^ 2

/-- Real-axis log Blaschke factor $f_x(y) := \log |T_y(x)|$. -/
noncomputable def realLogT (x y : ℝ) : ℝ := Real.log ‖blaschkeT (y : ℂ) (x : ℂ)‖

lemma tanh_pos_of_pos {t : ℝ} (ht : 0 < t) : 0 < Real.tanh t := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr ht) (Real.cosh_pos t)

private lemma real_hasDerivAt_tanh (t : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh t ^ 2) t := by
  have htanh : Real.tanh = fun s => Real.sinh s / Real.cosh s := by
    ext s; exact Real.tanh_eq_sinh_div_cosh s
  rw [htanh]
  have hd := (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) (Real.cosh_pos t).ne'
  refine hd.congr_deriv ?_
  have hcs : Real.cosh t ^ 2 - Real.sinh t ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq t
  field_simp [(Real.cosh_pos t).ne']
  linarith [hcs]

private lemma complex_tanh_ofReal (x : ℝ) :
    Complex.tanh (x : ℂ) = ((Real.tanh x : ℝ) : ℂ) := by
  rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_div]

lemma hasDerivAt_combH {z : ℝ} (hz : 0 < z) : HasDerivAt combH (combHDeriv z) z := by
  have hpi := Real.pi_pos
  have ht_pos : 0 < Real.tanh (π * z / 2) := tanh_pos_of_pos (by positivity)
  have h_in : HasDerivAt (fun t : ℝ => Real.tanh (π * t / 2))
      ((π / 2) / Real.cosh (π * z / 2) ^ 2) z := by
    have h1 : HasDerivAt (fun t : ℝ => π * t / 2) (π / 2) z := by
      simpa using ((hasDerivAt_id z).const_mul π).div_const 2
    have h2 := (real_hasDerivAt_tanh (π * z / 2)).comp z h1
    refine h2.congr_deriv ?_; ring
  have h_log := h_in.log ht_pos.ne'
  refine h_log.congr_deriv ?_
  unfold combHDeriv
  rw [Real.tanh_eq_sinh_div_cosh]
  have h2s : Real.sinh (π * z) = 2 * Real.sinh (π * z / 2) * Real.cosh (π * z / 2) := by
    have := Real.sinh_two_mul (π * z / 2)
    rwa [show 2 * (π * z / 2) = π * z by ring] at this
  have hsh_ne : Real.sinh (π * z / 2) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
  have hch_ne : Real.cosh (π * z / 2) ≠ 0 := (Real.cosh_pos _).ne'
  rw [h2s]; field_simp [hsh_ne, hch_ne]

lemma hasDerivAt_combHDeriv {z : ℝ} (hz : 0 < z) : HasDerivAt combHDeriv (combHSecond z) z := by
  have hpi := Real.pi_pos
  have hsh_ne : Real.sinh (π * z) ≠ 0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
  have h_den : HasDerivAt (fun t : ℝ => Real.sinh (π * t)) (Real.cosh (π * z) * π) z :=
    (Real.hasDerivAt_sinh (π * z)).comp z (by simpa using (hasDerivAt_id z).const_mul π)
  have h_div := (hasDerivAt_const z π).div h_den hsh_ne
  refine h_div.congr_deriv ?_
  unfold combHSecond; ring

/-- **K1(c), bounds on $\mathfrak{h}'$ and $\mathfrak{h}''$**:
for $z > 0$, $0 < \mathfrak{h}'(z) \le z^{-1}$, $\mathfrak{h}''(z) \le -\mathfrak{h}'(z)/z < 0$,
$|\mathfrak{h}''(z)| \le C z^{-2}$; and for $z \ge 1/2$, $\mathfrak{h}'(z) \le 4\pi e^{-\pi z}$
and $|\mathfrak{h}''(z)| \le C e^{-\pi z}$. -/
theorem combH_bounds :
    ∃ C > 0,
      (∀ z > 0, 0 < combHDeriv z ∧ combHDeriv z ≤ z⁻¹ ∧
        combHSecond z ≤ -combHDeriv z / z ∧ combHSecond z < 0 ∧
        |combHSecond z| ≤ C / z ^ 2) ∧
      (∀ z : ℝ, 1 / 2 ≤ z → combHDeriv z ≤ 4 * π * Real.exp (-π * z) ∧
        |combHSecond z| ≤ C * Real.exp (-π * z)) := by
  have hpi := Real.pi_pos
  have h_u_coth : ∀ u > 0, u * (Real.cosh u / Real.sinh u) ≤ 1 + u := by
    intro u hu
    have hsh : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu
    rw [mul_div_assoc', div_le_iff₀ hsh]
    have he : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_lt_exp (by positivity : 2 * u ≠ 0)]
    have he2 : (1 + 2 * u) * Real.exp (-u) ≤ Real.exp u := by
      have : Real.exp (2 * u) * Real.exp (-u) = Real.exp u := by rw [← Real.exp_add]; ring_nf
      calc (1 + 2 * u) * Real.exp (-u) ≤ Real.exp (2 * u) * Real.exp (-u) := by gcongr
        _ = Real.exp u := this
    rw [Real.cosh_eq, Real.sinh_eq]
    linarith
  have h_sinh_exp : ∀ u : ℝ, 1 ≤ u → Real.exp u / 4 ≤ Real.sinh u := by
    intro u hu
    have h1 : Real.exp (-u) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith [Real.add_one_lt_exp (one_ne_zero)]
    have h3 : Real.exp (-u) ≤ Real.exp u / 2 := by
      have : 1 ≤ Real.exp u := Real.one_le_exp (by linarith)
      linarith
    rw [Real.sinh_eq]; linarith
  have h_coth_bd : ∀ u : ℝ, 1 ≤ u → Real.cosh u / Real.sinh u ≤ 2 := by
    intro u hu
    have hsh : 0 < Real.sinh u := Real.sinh_pos_iff.mpr (by linarith)
    rw [div_le_iff₀ hsh, Real.cosh_eq, Real.sinh_eq]
    have h1 : Real.exp (-u) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith [Real.add_one_lt_exp (one_ne_zero)]
    have h3 : 2 ≤ Real.exp u := by
      have : 2 ≤ Real.exp 1 := by linarith [Real.add_one_lt_exp (one_ne_zero)]
      exact this.trans (Real.exp_le_exp.mpr hu)
    linarith
  have h_sq_le_exp : ∀ u : ℝ, 0 ≤ u → u ^ 2 ≤ 4 * Real.exp u := by
    intro u hu
    have h1 : u / 2 + 1 ≤ Real.exp (u / 2) := Real.add_one_le_exp (u / 2)
    have h2 : (u / 2) ^ 2 ≤ Real.exp u := by
      have : Real.exp (u / 2) ^ 2 = Real.exp u := by rw [sq, ← Real.exp_add]; ring_nf
      rw [← this]
      nlinarith
    linarith
  refine ⟨32 * π ^ 2, by positivity, ?_, ?_⟩
  · intro z hz
    have hsh_pos : 0 < Real.sinh (π * z) := Real.sinh_pos_iff.mpr (by positivity)
    have hch_pos : 0 < Real.cosh (π * z) := Real.cosh_pos _
    have hderiv_pos : 0 < combHDeriv z := by unfold combHDeriv; positivity
    have hderiv_le : combHDeriv z ≤ z⁻¹ := by
      unfold combHDeriv
      have h1 := abs_le_sinh_abs (π * z)
      rw [abs_of_pos (by positivity), abs_of_pos hsh_pos] at h1
      calc π / Real.sinh (π * z) ≤ π / (π * z) := by gcongr
        _ = z⁻¹ := by rw [div_mul_cancel_left₀ hpi.ne']
    have h_sec_eq : combHSecond z = -π * combHDeriv z * (Real.cosh (π * z) / Real.sinh (π * z)) := by
      unfold combHSecond combHDeriv
      field_simp [hsh_pos.ne']
    have h_sec_le : combHSecond z ≤ -combHDeriv z / z := by
      rw [h_sec_eq]
      have htu : Real.sinh (π * z) ≤ (π * z) * Real.cosh (π * z) := by
        let g : ℝ → ℝ := fun t => t * Real.cosh t - Real.sinh t
        have hderiv : ∀ s : ℝ, HasDerivAt g (s * Real.sinh s) s := by
          intro s
          have h := ((hasDerivAt_id s).mul (Real.hasDerivAt_cosh s)).sub (Real.hasDerivAt_sinh s)
          refine h.congr_deriv ?_; simp
        have hm := monotoneOn_of_deriv_nonneg (f := g) (convex_Icc 0 (π * z))
          ((continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh |>.continuousOn)
          (((differentiable_id.mul Real.differentiable_cosh).sub
            Real.differentiable_sinh).differentiableOn.mono interior_subset)
          (fun s hs => by
            rw [(hderiv s).deriv, interior_Icc] at *
            exact mul_nonneg hs.1.le (Real.sinh_nonneg_iff.mpr hs.1.le))
        have h0 := hm (left_mem_Icc.mpr (by positivity)) (right_mem_Icc.mpr (by positivity))
          (by positivity)
        dsimp [g] at h0
        simp only [zero_mul, Real.sinh_zero, sub_self] at h0
        linarith
      have hc_gt : 1 / (π * z) ≤ Real.cosh (π * z) / Real.sinh (π * z) :=
        (div_le_div_iff₀ (by positivity) hsh_pos).mpr (by linarith [htu])
      have hneg : -π * combHDeriv z ≤ 0 := by nlinarith
      calc -π * combHDeriv z * (Real.cosh (π * z) / Real.sinh (π * z))
          ≤ (-π * combHDeriv z) * (1 / (π * z)) :=
            mul_le_mul_of_nonpos_left hc_gt hneg
        _ = -combHDeriv z / z := by field_simp [hpi.ne', hz.ne']
    have h_sec_neg : combHSecond z < 0 := by
      unfold combHSecond
      rw [neg_mul, neg_div, neg_lt_zero]
      positivity
    have h_abs_sec : |combHSecond z| ≤ (32 * π ^ 2) / z ^ 2 := by
      rw [abs_of_neg h_sec_neg]
      rcases le_or_gt (π * z) 1 with hu | hu
      · have h1 := h_u_coth (π * z) (by positivity)
        have h2 : (π * z) * (Real.cosh (π * z) / Real.sinh (π * z)) ≤ 2 := by linarith
        have h3 : -combHSecond z = (combHDeriv z * z) * ((π * z) * (Real.cosh (π * z) / Real.sinh (π * z))) / z ^ 2 := by
          rw [h_sec_eq]; field_simp [hpi.ne', hz.ne']
        rw [h3]
        have hcz' : combHDeriv z * z ≤ 1 := by rwa [← le_div_iff₀ hz, one_div]
        have hnum : combHDeriv z * z * ((π * z) * (Real.cosh (π * z) / Real.sinh (π * z))) ≤ 2 := by
          nlinarith [mul_pos hderiv_pos hz]
        have h2pi : (2 : ℝ) ≤ 32 * π ^ 2 := by nlinarith [Real.pi_gt_three]
        exact (div_le_div_of_nonneg_right (hnum.trans h2pi) (sq_nonneg z))
      · have hsh_bd := h_sinh_exp (π * z) hu.le
        have hch_bd := h_coth_bd (π * z) hu.le
        have hsq_bd := h_sq_le_exp (π * z) (by positivity)
        have h_eq : -combHSecond z = π ^ 2 * ((π * z) ^ 2 / Real.sinh (π * z)) *
            (Real.cosh (π * z) / Real.sinh (π * z)) / (π * z) ^ 2 := by
          unfold combHSecond; field_simp [hpi.ne', hz.ne', hsh_pos.ne']
        rw [h_eq]
        have h1 : (π * z) ^ 2 / Real.sinh (π * z) ≤ 16 := by
          rw [div_le_iff₀ hsh_pos]
          linarith [hsh_bd, hsq_bd]
        have h2 : π ^ 2 * ((π * z) ^ 2 / Real.sinh (π * z)) *
            (Real.cosh (π * z) / Real.sinh (π * z)) ≤ 32 * π ^ 2 := by
          have : 0 ≤ π ^ 2 * ((π * z) ^ 2 / Real.sinh (π * z)) := by positivity
          nlinarith [hch_bd, h1]
        calc π ^ 2 * ((π * z) ^ 2 / Real.sinh (π * z)) * (Real.cosh (π * z) / Real.sinh (π * z)) / (π * z) ^ 2
            ≤ (32 * π ^ 2) / (π * z) ^ 2 := by gcongr
          _ ≤ (32 * π ^ 2) / z ^ 2 := by
              gcongr; nlinarith [Real.pi_gt_three, sq_nonneg z]
    exact ⟨hderiv_pos, hderiv_le, h_sec_le, h_sec_neg, h_abs_sec⟩
  · intro z hz
    have hu : 1 ≤ π * z := by nlinarith [Real.pi_gt_three]
    have hsh_bd := h_sinh_exp (π * z) hu
    have hch_bd := h_coth_bd (π * z) hu
    have hsh_pos : 0 < Real.sinh (π * z) := Real.sinh_pos_iff.mpr (by positivity)
    constructor
    · unfold combHDeriv
      rw [div_le_iff₀ hsh_pos]
      calc π = 4 * π * (1 / 4) := by ring
        _ = 4 * π * Real.exp (-π * z) * (Real.exp (π * z) / 4) := by
            rw [show -π * z = -(π * z) by ring, Real.exp_neg]; field_simp [(Real.exp_pos _).ne']
        _ ≤ 4 * π * Real.exp (-π * z) * Real.sinh (π * z) :=
            mul_le_mul_of_nonneg_left hsh_bd (by positivity)
    · have h_neg : combHSecond z < 0 := by
        unfold combHSecond
        rw [neg_mul, neg_div, neg_lt_zero]
        positivity
      rw [abs_of_neg h_neg]
      have h_eq : -combHSecond z = π ^ 2 * (Real.cosh (π * z) / Real.sinh (π * z)) / Real.sinh (π * z) := by
        unfold combHSecond; field_simp [hsh_pos.ne']
      rw [h_eq, div_le_iff₀ hsh_pos]
      calc π ^ 2 * (Real.cosh (π * z) / Real.sinh (π * z))
          ≤ π ^ 2 * 2 := by gcongr
        _ = 8 * π ^ 2 * (1 / 4) := by ring
        _ = 8 * π ^ 2 * Real.exp (-π * z) * (Real.exp (π * z) / 4) := by
            rw [show -π * z = -(π * z) by ring, Real.exp_neg]; field_simp [(Real.exp_pos _).ne']
        _ ≤ (32 * π ^ 2) * Real.exp (-π * z) * Real.sinh (π * z) := by
            have h1 : 8 * π ^ 2 * Real.exp (-π * z) * (Real.exp (π * z) / 4) ≤
                8 * π ^ 2 * Real.exp (-π * z) * Real.sinh (π * z) :=
              mul_le_mul_of_nonneg_left hsh_bd (by positivity)
            have h2 : 8 * π ^ 2 * Real.exp (-π * z) * Real.sinh (π * z) ≤
                32 * π ^ 2 * Real.exp (-π * z) * Real.sinh (π * z) := by
              gcongr; norm_num
            exact h1.trans h2

lemma realLogT_eq_combH {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : y ≠ x) :
    realLogT x y = combH |x - y| + combH (x + y) := by
  have hpi := Real.pi_pos
  unfold realLogT blaschkeT combH
  have h_re1 : Complex.tanh ((π : ℂ) * ((x : ℂ) - (y : ℂ)) / 2) =
      ((Real.tanh (π * (x - y) / 2) : ℝ) : ℂ) := by
    rw [← complex_tanh_ofReal]; congr 1; push_cast; ring
  have h_re2 : Complex.tanh ((π : ℂ) * ((x : ℂ) + (y : ℂ)) / 2) =
      ((Real.tanh (π * (x + y) / 2) : ℝ) : ℂ) := by
    rw [← complex_tanh_ofReal]; congr 1; push_cast; ring
  rw [norm_mul, h_re1, h_re2, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1_pos : 0 < |Real.tanh (π * (x - y) / 2)| := by
    rw [abs_pos, Real.tanh_eq_sinh_div_cosh, div_ne_zero_iff]
    exact ⟨Real.sinh_ne_zero.mpr (by have := sub_ne_zero.mpr hxy.symm; positivity),
      (Real.cosh_pos _).ne'⟩
  have h2_pos : 0 < Real.tanh (π * (x + y) / 2) := by
    apply tanh_pos_of_pos
    have : 0 < x + y := by
      rcases eq_or_lt_of_le hx with rfl | hx_pos
      · linarith [lt_of_le_of_ne hy hxy.symm]
      · linarith
    positivity
  have h1_eq : |Real.tanh (π * (x - y) / 2)| = Real.tanh (π * |x - y| / 2) := by
    rcases le_or_gt 0 (x - y) with h | h
    · have hpos : 0 < x - y := lt_of_le_of_ne h (sub_ne_zero.mpr hxy.symm).symm
      rw [abs_of_nonneg h, abs_of_nonneg (tanh_pos_of_pos (by positivity)).le]
    · have hneg : x - y < 0 := h
      rw [abs_of_neg hneg, show π * -(x - y) / 2 = -(π * (x - y) / 2) by ring]
      have ht_neg : Real.tanh (π * (x - y) / 2) < 0 := by
        rw [Real.tanh_eq_sinh_div_cosh]
        exact div_neg_of_neg_of_pos (Real.sinh_neg_iff.mpr (by nlinarith)) (Real.cosh_pos _)
      rw [abs_of_neg ht_neg, Real.tanh_neg]
  rw [abs_of_pos h2_pos, h1_eq, Real.log_mul (by rw [← h1_eq]; exact h1_pos.ne') h2_pos.ne']

private lemma realLogT_eq_combH_sub_of_lt {x t : ℝ} (h1 : -x < t) (h2 : t < x) :
    realLogT x t = combH (x - t) + combH (x + t) := by
  have hpi := Real.pi_pos
  have hxt1 : 0 < x - t := by linarith
  have hxt2 : 0 < x + t := by linarith
  unfold realLogT blaschkeT combH
  have h_re1 : Complex.tanh ((π : ℂ) * ((x : ℂ) - (t : ℂ)) / 2) =
      ((Real.tanh (π * (x - t) / 2) : ℝ) : ℂ) := by
    rw [← complex_tanh_ofReal]; congr 1; push_cast; ring
  have h_re2 : Complex.tanh ((π : ℂ) * ((x : ℂ) + (t : ℂ)) / 2) =
      ((Real.tanh (π * (x + t) / 2) : ℝ) : ℂ) := by
    rw [← complex_tanh_ofReal]; congr 1; push_cast; ring
  have ht1 : 0 < Real.tanh (π * (x - t) / 2) := tanh_pos_of_pos (by positivity)
  have ht2 : 0 < Real.tanh (π * (x + t) / 2) := tanh_pos_of_pos (by positivity)
  rw [norm_mul, h_re1, h_re2, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg ht1.le,
    Real.norm_of_nonneg ht2.le, Real.log_mul ht1.ne' ht2.ne']

private lemma realLogT_eq_combH_sub_of_gt {x t : ℝ} (hx : 0 ≤ x) (h : x < t) :
    realLogT x t = combH (t - x) + combH (x + t) := by
  have hpi := Real.pi_pos
  have hxt1 : 0 < t - x := by linarith
  have hxt2 : 0 < x + t := by linarith
  unfold realLogT blaschkeT combH
  have h_re1 : Complex.tanh ((π : ℂ) * ((x : ℂ) - (t : ℂ)) / 2) =
      ((-Real.tanh (π * (t - x) / 2) : ℝ) : ℂ) := by
    rw [show (π : ℂ) * ((x : ℂ) - (t : ℂ)) / 2 = -(((π * (t - x) / 2 : ℝ) : ℂ)) by
      push_cast; ring, Complex.tanh_neg, complex_tanh_ofReal]
    push_cast; ring
  have h_re2 : Complex.tanh ((π : ℂ) * ((x : ℂ) + (t : ℂ)) / 2) =
      ((Real.tanh (π * (x + t) / 2) : ℝ) : ℂ) := by
    rw [← complex_tanh_ofReal]; congr 1; push_cast; ring
  have ht1 : 0 < Real.tanh (π * (t - x) / 2) := tanh_pos_of_pos (by positivity)
  have ht2 : 0 < Real.tanh (π * (x + t) / 2) := tanh_pos_of_pos (by positivity)
  rw [norm_mul, h_re1, h_re2, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_pos ht1, Real.norm_of_nonneg ht2.le, Real.log_mul ht1.ne' ht2.ne']

/-- First derivative of $y \mapsto f_x(y)$ for $y \ne x$. -/
noncomputable def realLogTDeriv (x y : ℝ) : ℝ :=
  if y < x then -combHDeriv (x - y) + combHDeriv (x + y)
  else combHDeriv (y - x) + combHDeriv (x + y)

/-- Second derivative of $y \mapsto f_x(y)$ for $y \ne x$. -/
noncomputable def realLogTSecond (x y : ℝ) : ℝ :=
  combHSecond |x - y| + combHSecond (x + y)

/-- **K1(c), first and second derivatives of $y \mapsto f_x(y)$ for $y \ne x$**. -/
theorem realLogT_hasDerivAt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : y ≠ x) :
    HasDerivAt (fun t => realLogT x t) (realLogTDeriv x y) y ∧
    HasDerivAt (fun t => realLogTDeriv x t) (realLogTSecond x y) y := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have h_ev1 : (fun t => realLogT x t) =ᶠ[𝓝 y] fun t => combH (x - t) + combH (x + t) := by
      filter_upwards [Ioo_mem_nhds (by linarith : -x < y) hlt] with t ht
      exact realLogT_eq_combH_sub_of_lt ht.1 ht.2
    have h_ev2 : (fun t => realLogTDeriv x t) =ᶠ[𝓝 y]
        fun t => -combHDeriv (x - t) + combHDeriv (x + t) := by
      filter_upwards [Ioo_mem_nhds (by linarith : -x < y) hlt] with t ht
      simp [realLogTDeriv, ht.2]
    have d1_sub : HasDerivAt (fun t => combH (x - t)) (-combHDeriv (x - y)) y := by
      have hd := (hasDerivAt_combH (sub_pos.mpr hlt)).comp y
        ((hasDerivAt_id y).const_sub x)
      refine hd.congr_deriv ?_; ring
    have d1_add : HasDerivAt (fun t => combH (x + t)) (combHDeriv (x + y)) y := by
      have hd := (hasDerivAt_combH (by linarith : 0 < x + y)).comp y
        ((hasDerivAt_id y).const_add x)
      refine hd.congr_deriv ?_; ring
    have d2_sub : HasDerivAt (fun t => -combHDeriv (x - t)) (combHSecond (x - y)) y := by
      have hd := ((hasDerivAt_combHDeriv (sub_pos.mpr hlt)).comp y
        ((hasDerivAt_id y).const_sub x)).neg
      refine hd.congr_deriv ?_; ring
    have d2_add : HasDerivAt (fun t => combHDeriv (x + t)) (combHSecond (x + y)) y := by
      have hd := (hasDerivAt_combHDeriv (by linarith : 0 < x + y)).comp y
        ((hasDerivAt_id y).const_add x)
      refine hd.congr_deriv ?_; ring
    constructor
    · refine (d1_sub.add d1_add).congr_of_eventuallyEq h_ev1 |>.congr_deriv ?_
      simp [realLogTDeriv, hlt]
    · refine (d2_sub.add d2_add).congr_of_eventuallyEq h_ev2 |>.congr_deriv ?_
      simp [realLogTSecond, abs_of_pos (sub_pos.mpr hlt)]
  · have h_ev1 : (fun t => realLogT x t) =ᶠ[𝓝 y] fun t => combH (t - x) + combH (x + t) := by
      filter_upwards [Ioi_mem_nhds hgt] with t ht
      exact realLogT_eq_combH_sub_of_gt hx ht
    have h_ev2 : (fun t => realLogTDeriv x t) =ᶠ[𝓝 y]
        fun t => combHDeriv (t - x) + combHDeriv (x + t) := by
      filter_upwards [Ioi_mem_nhds hgt] with t ht
      simp [realLogTDeriv, not_lt.mpr ht.le]
    have d1_sub : HasDerivAt (fun t => combH (t - x)) (combHDeriv (y - x)) y := by
      have hd := (hasDerivAt_combH (sub_pos.mpr hgt)).comp y
        ((hasDerivAt_id y).sub_const x)
      refine hd.congr_deriv ?_; ring
    have d1_add : HasDerivAt (fun t => combH (x + t)) (combHDeriv (x + y)) y := by
      have hd := (hasDerivAt_combH (by linarith : 0 < x + y)).comp y
        ((hasDerivAt_id y).const_add x)
      refine hd.congr_deriv ?_; ring
    have d2_sub : HasDerivAt (fun t => combHDeriv (t - x)) (combHSecond (y - x)) y := by
      have hd := (hasDerivAt_combHDeriv (sub_pos.mpr hgt)).comp y
        ((hasDerivAt_id y).sub_const x)
      refine hd.congr_deriv ?_; ring
    have d2_add : HasDerivAt (fun t => combHDeriv (x + t)) (combHSecond (x + y)) y := by
      have hd := (hasDerivAt_combHDeriv (by linarith : 0 < x + y)).comp y
        ((hasDerivAt_id y).const_add x)
      refine hd.congr_deriv ?_; ring
    constructor
    · refine (d1_sub.add d1_add).congr_of_eventuallyEq h_ev1 |>.congr_deriv ?_
      simp [realLogTDeriv, not_lt.mpr hgt.le]
    · refine (d2_sub.add d2_add).congr_of_eventuallyEq h_ev2 |>.congr_deriv ?_
      simp [realLogTSecond, abs_sub_comm x y, abs_of_pos (sub_pos.mpr hgt)]

/-- **K1(c), derivative signs and bounds for $y \mapsto f_x(y)$**:
- $\partial_y^2 f_x(y) < 0$ for $x, y \ge 0$, $y \ne x$;
- for $0 \le y < x$, $\partial_y f_x(y) \le 0$ (and $< 0$ when $0 < y < x$) with
  $|\partial_y f_x(y)| < 1/(x - y)$;
- for $y > x \ge 0$, $\partial_y f_x(y) > 0$, and if $y \ge \xi_*$ then
  $\partial_y f_x(y) \le 1/(y - x) + \pi$. -/
theorem realLogT_deriv_bounds {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : y ≠ x) :
    realLogTSecond x y < 0 ∧
      (y < x → realLogTDeriv x y ≤ 0 ∧ (0 < y → realLogTDeriv x y < 0) ∧
        |realLogTDeriv x y| < 1 / (x - y)) ∧
      (x < y → 0 < realLogTDeriv x y ∧ (xiStar ≤ y → realLogTDeriv x y ≤ 1 / (y - x) + π)) := by
  obtain ⟨_, _, hbd, _⟩ := combH_bounds
  have hpi := Real.pi_pos
  have h_pos_sum : 0 < x + y := by
    rcases eq_or_lt_of_le hx with rfl | hxp
    · linarith [lt_of_le_of_ne hy hxy.symm]
    · linarith
  have hsec1 := (hbd |x - y| (abs_pos.mpr (sub_ne_zero.mpr hxy.symm))).2.2.2.1
  have hsec2 := (hbd (x + y) h_pos_sum).2.2.2.1
  refine ⟨by unfold realLogTSecond; linarith, ?_, ?_⟩
  · intro hlt
    have h1 := hbd (x - y) (sub_pos.mpr hlt)
    have h2 := hbd (x + y) h_pos_sum
    have hsinh_mono : Real.sinh (π * (x - y)) ≤ Real.sinh (π * (x + y)) :=
      Real.sinh_le_sinh.mpr (by nlinarith)
    have hcomb_le : combHDeriv (x + y) ≤ combHDeriv (x - y) := by
      unfold combHDeriv
      exact div_le_div_of_nonneg_left hpi.le (Real.sinh_pos_iff.mpr (by positivity)) hsinh_mono
    have hderiv_eq : realLogTDeriv x y = -combHDeriv (x - y) + combHDeriv (x + y) := by
      simp [realLogTDeriv, hlt]
    have hle0 : realLogTDeriv x y ≤ 0 := by rw [hderiv_eq]; linarith
    refine ⟨hle0, ?_, ?_⟩
    · intro hy0
      have hsinh_lt : Real.sinh (π * (x - y)) < Real.sinh (π * (x + y)) :=
        Real.sinh_lt_sinh.mpr (by nlinarith only [hpi, hy0])
      have hcomb_lt : combHDeriv (x + y) < combHDeriv (x - y) := by
        unfold combHDeriv
        exact div_lt_div_of_pos_left hpi (Real.sinh_pos_iff.mpr (by positivity)) hsinh_lt
      rw [hderiv_eq]; linarith
    · rw [abs_of_nonpos hle0, hderiv_eq]
      have h1' : combHDeriv (x - y) ≤ 1 / (x - y) := by
        simpa [one_div] using h1.2.1
      have h2' : 0 < combHDeriv (x + y) := h2.1
      linarith
  · intro hgt
    have h1 := hbd (y - x) (sub_pos.mpr hgt)
    have h2 := hbd (x + y) h_pos_sum
    have hderiv_eq : realLogTDeriv x y = combHDeriv (y - x) + combHDeriv (x + y) := by
      simp [realLogTDeriv, not_lt.mpr hgt.le]
    refine ⟨by rw [hderiv_eq]; linarith [h1.1, h2.1], ?_⟩
    intro hy_xi
    rw [hderiv_eq]
    have h1' : combHDeriv (y - x) ≤ 1 / (y - x) := by
      simpa [one_div] using h1.2.1
    have h2' : combHDeriv (x + y) ≤ π := by
      unfold combHDeriv
      have hsh : Real.sinh (π * xiStar) ≤ Real.sinh (π * (x + y)) :=
        Real.sinh_le_sinh.mpr (by nlinarith)
      rw [sinh_pi_mul_xiStar] at hsh
      exact div_le_self hpi.le hsh
    linarith

/-! ### Section 5: Lemma K1(d) — Analytic branch `φ_ζ(b)` on `𝓝` -/

/-- The strip neighbourhood $\mathcal N = \{b \in \mathbb{C} : |\operatorname{Im} b - 1/2| \le 1/4\}$. -/
def combN : Set ℂ := {b : ℂ | |b.im - 1 / 2| ≤ 1 / 4}

/-- Parameter domain for $\zeta$: $\{\zeta \in \mathbb{C} : \operatorname{Re}\zeta \ge 0,\ |\operatorname{Im}\zeta| \le 1/8\}$. -/
def combZ : Set ℂ := {ζ : ℂ | 0 ≤ ζ.re ∧ |ζ.im| ≤ 1 / 8}

/-- Open neighbourhood of $\mathcal N$: $|\operatorname{Im} b - 1/2| < 9/32$. -/
def combNOpen : Set ℂ := {b : ℂ | |b.im - 1 / 2| < 9 / 32}

/-- Open neighbourhood of `combZ`: $\operatorname{Re}\zeta > -1/4$ and $|\operatorname{Im}\zeta| < 5/32$. -/
def combZOpen : Set ℂ := {ζ : ℂ | -1 / 4 < ζ.re ∧ |ζ.im| < 5 / 32}

lemma combN_subset_combNOpen : combN ⊆ combNOpen := fun b hb => by
  change |b.im - 1 / 2| < 9 / 32
  exact lt_of_le_of_lt (show |b.im - 1 / 2| ≤ 1 / 4 from hb) (by norm_num)

lemma combZ_subset_combZOpen : combZ ⊆ combZOpen := fun _ hζ =>
  ⟨by linarith [hζ.1], lt_of_le_of_lt hζ.2 (by norm_num)⟩

lemma isOpen_combNOpen : IsOpen combNOpen :=
  isOpen_lt (continuous_abs.comp (Complex.continuous_im.sub continuous_const)) continuous_const

lemma isOpen_combZOpen : IsOpen combZOpen :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)

/-- Kernel $\pi / \sinh(\pi w)$. -/
noncomputable def sinhKernel (w : ℂ) : ℂ := (π : ℂ) / Complex.sinh ((π : ℂ) * w)

/-- Explicit analytic branch $\varphi_\zeta(b) = \log(-T_\zeta(b))$ on $\mathcal N$:
$\varphi_\zeta(b) := \int_0^\infty \bigl(\frac{\pi}{\sinh\pi(b - \zeta - t)} - \frac{\pi}{\sinh\pi(b + \zeta + t)}\bigr)\,dt$. -/
noncomputable def phiZeta (ζ b : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (sinhKernel (b - (ζ + (t : ℂ))) - sinhKernel (b + (ζ + (t : ℂ))))

private lemma sinh_pi_norm_ge_of_im {s₀ : ℝ} (hs₀ : 0 < s₀) (hs₁ : s₀ < 1 / 2) :
    ∃ c > 0, ∀ w : ℂ, s₀ ≤ w.im → w.im ≤ 1 - s₀ →
      c * Real.exp (π * |w.re|) ≤ ‖Complex.sinh ((π : ℂ) * w)‖ := by
  have hpi := Real.pi_pos
  have hsin_pos : 0 < Real.sin (π * s₀) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  have hsin_le : ∀ θ : ℝ, π * s₀ ≤ θ → θ ≤ π * (1 - s₀) → Real.sin (π * s₀) ≤ Real.sin θ := by
    intro θ hθ1 hθ2
    rcases le_or_gt θ (π / 2) with h | h
    · exact Real.strictMonoOn_sin.monotoneOn
        ⟨by nlinarith, by nlinarith⟩ ⟨by nlinarith, by nlinarith⟩ hθ1
    · rw [← Real.sin_pi_sub θ]
      exact Real.strictMonoOn_sin.monotoneOn
        ⟨by nlinarith, by nlinarith⟩ ⟨by nlinarith, by nlinarith⟩ (by nlinarith)
  set c := min (Real.sin (π * s₀) * Real.exp (-π)) (1 / 4)
  have hc : 0 < c := lt_min (by positivity) (by norm_num)
  refine ⟨c, hc, fun w hw1 hw2 => ?_⟩
  have hns : ‖Complex.sinh ((π : ℂ) * w)‖ ^ 2 =
      Real.sinh (π * w.re) ^ 2 + Real.sin (π * w.im) ^ 2 := by
    have hw : (π : ℂ) * w = ((π * w.re : ℝ) : ℂ) + ((π * w.im : ℝ) : ℂ) * Complex.I :=
      Complex.ext (by simp) (by simp)
    rw [Complex.sq_norm, hw, complex_sinh_normSq]
  rcases le_or_gt |w.re| 1 with hre | hre
  · have hsin_ge : Real.sin (π * s₀) ≤ |Real.sin (π * w.im)| := by
      have h1 := hsin_le (π * w.im) (by nlinarith) (by nlinarith)
      exact h1.trans (le_abs_self _)
    have hnorm_ge : Real.sin (π * s₀) ≤ ‖Complex.sinh ((π : ℂ) * w)‖ := by
      have hsq : Real.sin (π * s₀) ^ 2 ≤ ‖Complex.sinh ((π : ℂ) * w)‖ ^ 2 := by
        rw [hns]
        have : Real.sin (π * s₀) ^ 2 ≤ Real.sin (π * w.im) ^ 2 := by
          nlinarith [sq_abs (Real.sin (π * w.im))]
        linarith [sq_nonneg (Real.sinh (π * w.re))]
      nlinarith [norm_nonneg (Complex.sinh ((π : ℂ) * w))]
    calc c * Real.exp (π * |w.re|)
        ≤ (Real.sin (π * s₀) * Real.exp (-π)) * Real.exp π := by
          refine mul_le_mul (min_le_left _ _) (Real.exp_le_exp.mpr (by nlinarith))
            (Real.exp_pos _).le (by positivity)
      _ = Real.sin (π * s₀) := by rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      _ ≤ ‖Complex.sinh ((π : ℂ) * w)‖ := hnorm_ge
  · have hsh_ge : Real.exp (π * |w.re|) / 4 ≤ |Real.sinh (π * w.re)| := by
      have hsh_abs : |Real.sinh (π * w.re)| = Real.sinh (π * |w.re|) := by
        rcases le_or_gt 0 w.re with h | h
        · rw [abs_of_nonneg h, abs_of_nonneg (Real.sinh_nonneg_iff.mpr (by positivity))]
        · rw [abs_of_neg h, abs_of_neg (Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg hpi h)),
            mul_neg, Real.sinh_neg]
      rw [hsh_abs, Real.sinh_eq]
      have h1 : Real.exp (-(π * |w.re|)) ≤ Real.exp (-π) := by
        have : π ≤ π * |w.re| := le_mul_of_one_le_right hpi.le hre.le
        exact Real.exp_le_exp.mpr (by linarith)
      have h2 : Real.exp (-π) ≤ 1 / 2 := by
        rw [Real.exp_neg]
        calc (Real.exp π)⁻¹ ≤ (Real.exp 1)⁻¹ :=
              inv_anti₀ (Real.exp_pos 1) (Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three]))
          _ ≤ 1 / 2 := by
              rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
              norm_num
              linarith [Real.add_one_lt_exp (one_ne_zero)]
      have h3 : 1 ≤ Real.exp (π * |w.re|) := Real.one_le_exp (by positivity)
      linarith
    have hnorm_ge : |Real.sinh (π * w.re)| ≤ ‖Complex.sinh ((π : ℂ) * w)‖ := by
      have hsq : Real.sinh (π * w.re) ^ 2 ≤ ‖Complex.sinh ((π : ℂ) * w)‖ ^ 2 := by
        rw [hns]; linarith [sq_nonneg (Real.sin (π * w.im))]
      nlinarith [sq_abs (Real.sinh (π * w.re)), norm_nonneg (Complex.sinh ((π : ℂ) * w))]
    calc c * Real.exp (π * |w.re|)
        ≤ (1 / 4) * Real.exp (π * |w.re|) := by gcongr; exact min_le_right _ _
      _ ≤ |Real.sinh (π * w.re)| := by linarith
      _ ≤ ‖Complex.sinh ((π : ℂ) * w)‖ := hnorm_ge

private lemma sinhKernel_bound_of_im {s₀ : ℝ} (hs₀ : 0 < s₀) (hs₁ : s₀ < 1 / 2) :
    ∃ C > 0, ∀ w : ℂ, s₀ ≤ w.im → w.im ≤ 1 - s₀ →
      Complex.sinh ((π : ℂ) * w) ≠ 0 ∧ ‖sinhKernel w‖ ≤ C * Real.exp (-π * |w.re|) := by
  obtain ⟨c, hc, hge⟩ := sinh_pi_norm_ge_of_im hs₀ hs₁
  refine ⟨π / c, div_pos Real.pi_pos hc, fun w hw1 hw2 => ?_⟩
  have hpos : 0 < ‖Complex.sinh ((π : ℂ) * w)‖ :=
    lt_of_lt_of_le (by positivity) (hge w hw1 hw2)
  refine ⟨norm_pos_iff.mp hpos, ?_⟩
  unfold sinhKernel
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    show -π * |w.re| = -(π * |w.re|) by ring, Real.exp_neg]
  calc π / ‖Complex.sinh ((π : ℂ) * w)‖
      ≤ π / (c * Real.exp (π * |w.re|)) := by gcongr; exact hge w hw1 hw2
    _ = (π / c) * (Real.exp (π * |w.re|))⁻¹ := by ring

private lemma sinhKernel_differentiableOn :
    DifferentiableOn ℂ sinhKernel {w : ℂ | 0 < w.im ∧ w.im < 1} := by
  intro w hw
  have hs₀ : 0 < min (w.im / 2) ((1 - w.im) / 2) := lt_min (by linarith [hw.1]) (by linarith [hw.2])
  have hs₁ : min (w.im / 2) ((1 - w.im) / 2) < 1 / 2 :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith [hw.2])
  obtain ⟨_, _, hne⟩ := sinhKernel_bound_of_im hs₀ hs₁
  have h_ne : Complex.sinh ((π : ℂ) * w) ≠ 0 :=
    (hne w (by linarith [min_le_left (w.im / 2) ((1 - w.im) / 2)])
      (by linarith [min_le_right (w.im / 2) ((1 - w.im) / 2)])).1
  unfold sinhKernel
  exact ((differentiableAt_const _).div
    (Complex.differentiable_sinh.differentiableAt.comp w (by fun_prop)) h_ne).differentiableWithinAt

private lemma sinhKernel_iteratedDeriv_bound {k : ℕ} {s₀ : ℝ} (hs₀ : 0 < s₀) (hs₁ : s₀ < 1 / 2) :
    ∃ C > 0, ∀ w : ℂ, 2 * s₀ ≤ w.im → w.im ≤ 1 - 2 * s₀ →
      ‖iteratedDeriv k sinhKernel w‖ ≤ C * Real.exp (-π * |w.re|) := by
  obtain ⟨C₀, hC₀, hbd⟩ := sinhKernel_bound_of_im hs₀ hs₁
  set C := (k.factorial : ℝ) * C₀ * Real.exp (π * s₀) / s₀ ^ k
  refine ⟨C, by positivity, fun w hw1 hw2 => ?_⟩
  have hsub : Metric.closedBall w s₀ ⊆ {z : ℂ | 0 < z.im ∧ z.im < 1} := by
    intro z hz
    have him : |z.im - w.im| ≤ s₀ :=
      (Complex.abs_im_le_norm (z - w)).trans (mem_closedBall_iff_norm.mp hz)
    have him1 : s₀ ≤ z.im := by linarith [(abs_le.mp him).1]
    have him2 : z.im ≤ 1 - s₀ := by linarith [(abs_le.mp him).2]
    exact ⟨lt_of_lt_of_le hs₀ him1, lt_of_le_of_lt him2 (by linarith)⟩
  have hdiff : DiffContOnCl ℂ sinhKernel (Metric.ball w s₀) := by
    refine ⟨sinhKernel_differentiableOn.mono (Metric.ball_subset_closedBall.trans hsub), ?_⟩
    rw [closure_ball w hs₀.ne']
    exact (sinhKernel_differentiableOn.mono hsub).continuousOn
  have hsphere : ∀ z ∈ Metric.sphere w s₀, ‖sinhKernel z‖ ≤ C₀ * Real.exp (π * s₀) * Real.exp (-π * |w.re|) := by
    intro z hz
    have hzw : ‖z - w‖ = s₀ := mem_sphere_iff_norm.mp hz
    have him : |z.im - w.im| ≤ s₀ := (Complex.abs_im_le_norm (z - w)).trans hzw.le
    have hre : |z.re - w.re| ≤ s₀ := (Complex.abs_re_le_norm (z - w)).trans hzw.le
    have h1 := (hbd z (by linarith [(abs_le.mp him).1]) (by linarith [(abs_le.mp him).2])).2
    have hre_lb : |w.re| - s₀ ≤ |z.re| := by
      have : |w.re| - |z.re| ≤ |w.re - z.re| := abs_sub_abs_le_abs_sub _ _
      rw [abs_sub_comm] at this
      linarith
    have hexp_le : Real.exp (-π * |z.re|) ≤ Real.exp (π * s₀) * Real.exp (-π * |w.re|) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    calc ‖sinhKernel z‖ ≤ C₀ * Real.exp (-π * |z.re|) := h1
      _ ≤ C₀ * (Real.exp (π * s₀) * Real.exp (-π * |w.re|)) := by gcongr
      _ = C₀ * Real.exp (π * s₀) * Real.exp (-π * |w.re|) := by ring
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hs₀ hdiff hsphere
  refine hcauchy.trans_eq ?_
  dsimp [C]; ring

private lemma sinhKernel_sub_im_mem {b ζ : ℂ} (hb : |b.im - 1 / 2| < 9 / 32)
    (hζ : |ζ.im| < 5 / 32) :
    ∀ t : ℝ, 1 / 16 ≤ (b - (ζ + (t : ℂ))).im ∧ (b - (ζ + (t : ℂ))).im ≤ 15 / 16 ∧
      1 / 16 ≤ (b + (ζ + (t : ℂ))).im ∧ (b + (ζ + (t : ℂ))).im ≤ 15 / 16 := by
  intro t
  have hb1 := (abs_lt.mp hb).1
  have hb2 := (abs_lt.mp hb).2
  have hζ1 := (abs_lt.mp hζ).1
  have hζ2 := (abs_lt.mp hζ).2
  simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, add_zero]
  norm_num at *
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

private lemma phiZeta_integrable_exp_bound (u : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-π * |u + t|)) (Ioi (0 : ℝ)) := by
  have hpi := Real.pi_pos
  have hdom : IntegrableOn (fun t : ℝ => Real.exp (π * |u|) * Real.exp (-π * t)) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (by linarith : -π < 0) 0).const_mul _
  refine hdom.mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have htri : t ≤ |u + t| + |u| := by
    calc t = |(u + t) - u| := by rw [add_sub_cancel_left, abs_of_pos ht0]
      _ ≤ |u + t| + |u| := abs_sub _ _
  have hle : Real.exp (-π * |u + t|) ≤ Real.exp (π * |u|) * Real.exp (-π * t) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact hle

private lemma integral_exp_neg_pi_abs_le (u : ℝ) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-π * |u + t|) ≤ 2 / π := by
  have hpi := Real.pi_pos
  rcases le_or_gt 0 u with hu | hu
  · have hdom : IntegrableOn (fun t : ℝ => Real.exp (-π * t)) (Ioi (0 : ℝ)) :=
      integrableOn_exp_mul_Ioi (by linarith : -π < 0) 0
    have hle : ∫ t in Ioi (0 : ℝ), Real.exp (-π * |u + t|) ≤
        ∫ t in Ioi (0 : ℝ), Real.exp (-π * t) := by
      refine MeasureTheory.setIntegral_mono_on (phiZeta_integrable_exp_bound u) hdom measurableSet_Ioi ?_
      intro t ht
      have ht0 : 0 < t := ht
      rw [abs_of_pos (by linarith)]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hval : ∫ t in Ioi (0 : ℝ), Real.exp (-π * t) = 1 / π := by
      rw [integral_exp_mul_Ioi (by linarith : -π < 0) 0, mul_zero, Real.exp_zero]
      field_simp [hpi.ne']
    linarith [show (1 / π : ℝ) ≤ 2 / π by gcongr; norm_num]
  · have h_split : Ioi (0 : ℝ) = Ioc 0 (-u) ∪ Ioi (-u) :=
      (Ioc_union_Ioi_eq_Ioi (by linarith : 0 ≤ -u)).symm
    have h_int_all := phiZeta_integrable_exp_bound u
    have h_int1 : IntegrableOn (fun t : ℝ => Real.exp (-π * |u + t|)) (Ioc 0 (-u)) :=
      h_int_all.mono_set Ioc_subset_Ioi_self
    have h_int2 : IntegrableOn (fun t : ℝ => Real.exp (-π * |u + t|)) (Ioi (-u)) :=
      h_int_all.mono_set (Ioi_subset_Ioi (by linarith))
    rw [h_split, MeasureTheory.setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h_int1 h_int2]
    have h1_eq : ∫ t in Ioc 0 (-u), Real.exp (-π * |u + t|) =
        ∫ t in (0 : ℝ)..(-u), Real.exp (π * u) * Real.exp (π * t) := by
      rw [intervalIntegral.integral_of_le (by linarith : 0 ≤ -u)]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      rw [abs_of_nonpos (by linarith [ht.2]), ← Real.exp_add]
      congr 1; ring
    have h_anti : ∀ t ∈ uIcc (0 : ℝ) (-u),
        HasDerivAt (fun s => Real.exp (π * s) / π) (Real.exp (π * t)) t := by
      intro t _
      have hd := ((hasDerivAt_id t).const_mul π).exp.div_const π
      refine hd.congr_deriv ?_; simp [hpi.ne']
    have h_ftc : ∫ t in (0 : ℝ)..(-u), Real.exp (π * t) = (Real.exp (π * (-u)) - 1) / π := by
      have hc : Continuous (fun t : ℝ => Real.exp (π * t)) :=
        Real.continuous_exp.comp (continuous_const.mul continuous_id)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_anti (hc.intervalIntegrable 0 (-u))]
      simp only [mul_zero, Real.exp_zero]; ring
    have h1_val : ∫ t in Ioc 0 (-u), Real.exp (-π * |u + t|) = (1 - Real.exp (π * u)) / π := by
      rw [h1_eq, intervalIntegral.integral_const_mul, h_ftc]
      rw [show Real.exp (π * u) * ((Real.exp (π * (-u)) - 1) / π) =
        (Real.exp (π * u) * Real.exp (-(π * u)) - Real.exp (π * u)) / π by ring_nf]
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h2_eq : ∫ t in Ioi (-u), Real.exp (-π * |u + t|) =
        Real.exp (-π * u) * ∫ t in Ioi (-u), Real.exp (-π * t) := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [abs_of_pos (by linarith [mem_Ioi.mp ht]), ← Real.exp_add]
      congr 1; ring
    have h2_val : ∫ t in Ioi (-u), Real.exp (-π * |u + t|) = 1 / π := by
      rw [h2_eq, integral_exp_mul_Ioi (by linarith : -π < 0) (-u)]
      rw [show -π * (-u) = π * u by ring]
      have hid : Real.exp (-π * u) * (-Real.exp (π * u) / -π) =
          (Real.exp (-π * u) * Real.exp (π * u)) / π := by ring
      rw [hid, ← Real.exp_add, show -π * u + π * u = 0 by ring, Real.exp_zero, one_div]
    rw [h1_val, h2_val]
    have hsum : (1 - Real.exp (π * u)) / π + 1 / π = 2 / π - Real.exp (π * u) / π := by ring
    rw [hsum]
    linarith [div_pos (Real.exp_pos (π * u)) hpi]

private lemma phiZeta_integrand_integrable (ζ b : ℂ) (hb : b ∈ combNOpen) (hζ : ζ ∈ combZOpen) :
    IntegrableOn (fun t : ℝ => sinhKernel (b - (ζ + (t : ℂ))) - sinhKernel (b + (ζ + (t : ℂ))))
      (Ioi (0 : ℝ)) := by
  obtain ⟨C, _, hbd⟩ := sinhKernel_bound_of_im (s₀ := 1 / 32) (by norm_num) (by norm_num)
  have hb' : |b.im - 1 / 2| < 9 / 32 := hb
  have hζ' : |ζ.im| < 5 / 32 := hζ.2
  have him := sinhKernel_sub_im_mem hb' hζ'
  have hmeas : Continuous (fun t : ℝ => sinhKernel (b - (ζ + (t : ℂ))) - sinhKernel (b + (ζ + (t : ℂ)))) := by
    have hm1 : Continuous (fun t : ℝ => b - (ζ + (t : ℂ))) :=
      continuous_const.sub (continuous_const.add Complex.continuous_ofReal)
    have hm2 : Continuous (fun t : ℝ => b + (ζ + (t : ℂ))) :=
      continuous_const.add (continuous_const.add Complex.continuous_ofReal)
    have hs1 : Continuous (fun t : ℝ => sinhKernel (b - (ζ + (t : ℂ)))) :=
      sinhKernel_differentiableOn.continuousOn.comp_continuous hm1 fun t =>
        ⟨by linarith [(him t).1], by linarith [(him t).2.1]⟩
    have hs2 : Continuous (fun t : ℝ => sinhKernel (b + (ζ + (t : ℂ)))) :=
      sinhKernel_differentiableOn.continuousOn.comp_continuous hm2 fun t =>
        ⟨by linarith [(him t).2.2.1], by linarith [(him t).2.2.2]⟩
    exact hs1.sub hs2
  have hdom : IntegrableOn (fun t : ℝ => C * (Real.exp (-π * |ζ.re - b.re + t|) +
      Real.exp (-π * |ζ.re + b.re + t|))) (Ioi (0 : ℝ)) :=
    ((phiZeta_integrable_exp_bound (ζ.re - b.re)).add
      (phiZeta_integrable_exp_bound (ζ.re + b.re))).const_mul C
  refine hdom.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun t => ?_)
  have h1 := (hbd (b - (ζ + (t : ℂ))) (by linarith [(him t).1]) (by linarith [(him t).2.1])).2
  have h2 := (hbd (b + (ζ + (t : ℂ))) (by linarith [(him t).2.2.1]) (by linarith [(him t).2.2.2])).2
  have hr1 : |(b - (ζ + (t : ℂ))).re| = |ζ.re - b.re + t| := by
    rw [Complex.sub_re, Complex.add_re, Complex.ofReal_re, ← abs_neg]; congr 1; ring
  have hr2 : |(b + (ζ + (t : ℂ))).re| = |ζ.re + b.re + t| := by
    rw [Complex.add_re, Complex.add_re, Complex.ofReal_re]; congr 1; ring
  rw [hr1] at h1; rw [hr2] at h2
  calc ‖sinhKernel (b - (ζ + (t : ℂ))) - sinhKernel (b + (ζ + (t : ℂ)))‖
      ≤ ‖sinhKernel (b - (ζ + (t : ℂ)))‖ + ‖sinhKernel (b + (ζ + (t : ℂ)))‖ := norm_sub_le _ _
    _ ≤ C * Real.exp (-π * |ζ.re - b.re + t|) + C * Real.exp (-π * |ζ.re + b.re + t|) := add_le_add h1 h2
    _ = C * (Real.exp (-π * |ζ.re - b.re + t|) + Real.exp (-π * |ζ.re + b.re + t|)) := by ring

/-- First partial derivative of $\varphi_\zeta(b)$ in $b$:
$\partial_b \varphi_\zeta(b) = \frac{\pi}{\sinh\pi(b - \zeta)} + \frac{\pi}{\sinh\pi(b + \zeta)}$. -/
theorem hasDerivAt_phiZeta_b {ζ b : ℂ} (hb : b ∈ combNOpen) (hζ : ζ ∈ combZOpen) :
    HasDerivAt (fun z => phiZeta ζ z) (sinhKernel (b - ζ) + sinhKernel (b + ζ)) b := by
  have hpi := Real.pi_pos
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_combNOpen b hb
  set δ := min r (1 / 32)
  have hδ : 0 < δ := lt_min hr (by norm_num)
  have hball_sub : Metric.ball b δ ⊆ combNOpen := (Metric.ball_subset_ball (min_le_left _ _)).trans hball
  obtain ⟨C₁, hC₁, hbd1⟩ := sinhKernel_iteratedDeriv_bound (k := 1) (s₀ := 1 / 32)
    (by norm_num) (by norm_num)
  let F : ℂ → ℝ → ℂ := fun z t => sinhKernel (z - (ζ + (t : ℂ))) - sinhKernel (z + (ζ + (t : ℂ)))
  let F' : ℂ → ℝ → ℂ := fun z t =>
    deriv sinhKernel (z - (ζ + (t : ℂ))) - deriv sinhKernel (z + (ζ + (t : ℂ)))
  let bound : ℝ → ℝ := fun t => C₁ * Real.exp (π * δ) *
    (Real.exp (-π * |ζ.re - b.re + t|) + Real.exp (-π * |ζ.re + b.re + t|))
  have hF_meas : ∀ᶠ z in 𝓝 b, AEStronglyMeasurable (F z) (volume.restrict (Ioi 0)) := by
    filter_upwards [Metric.ball_mem_nhds b hδ] with z hz
    exact (phiZeta_integrand_integrable ζ z (hball_sub hz) hζ).aestronglyMeasurable
  have hF_int : Integrable (F b) (volume.restrict (Ioi 0)) :=
    phiZeta_integrand_integrable ζ b hb hζ
  have him_ball : ∀ z ∈ Metric.ball b δ, ∀ t : ℝ,
      1 / 16 ≤ (z - (ζ + (t : ℂ))).im ∧ (z - (ζ + (t : ℂ))).im ≤ 15 / 16 ∧
      1 / 16 ≤ (z + (ζ + (t : ℂ))).im ∧ (z + (ζ + (t : ℂ))).im ≤ 15 / 16 :=
    fun z hz t => sinhKernel_sub_im_mem (hball_sub hz) hζ.2 t
  have hF'_meas : AEStronglyMeasurable (F' b) (volume.restrict (Ioi 0)) := by
    have hcont : Continuous (F' b) := by
      have hd_an : AnalyticOnNhd ℂ sinhKernel {w : ℂ | 0 < w.im ∧ w.im < 1} :=
        sinhKernel_differentiableOn.analyticOnNhd
          ((isOpen_lt continuous_const Complex.continuous_im).inter
            (isOpen_lt Complex.continuous_im continuous_const))
      have hd_cont : ContinuousOn (deriv sinhKernel) {w : ℂ | 0 < w.im ∧ w.im < 1} :=
        hd_an.deriv.continuousOn
      have hm1 : Continuous (fun t : ℝ => b - (ζ + (t : ℂ))) :=
        continuous_const.sub (continuous_const.add Complex.continuous_ofReal)
      have hm2 : Continuous (fun t : ℝ => b + (ζ + (t : ℂ))) :=
        continuous_const.add (continuous_const.add Complex.continuous_ofReal)
      have him := sinhKernel_sub_im_mem hb hζ.2
      exact (hd_cont.comp_continuous hm1 fun t => ⟨by linarith [(him t).1], by linarith [(him t).2.1]⟩).sub
        (hd_cont.comp_continuous hm2 fun t => ⟨by linarith [(him t).2.2.1], by linarith [(him t).2.2.2]⟩)
    exact hcont.aestronglyMeasurable
  have h_bound : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ z ∈ Metric.ball b δ, ‖F' z t‖ ≤ bound t := by
    refine ae_of_all _ fun t z hz => ?_
    have him := him_ball z hz t
    have h1 := hbd1 (z - (ζ + (t : ℂ))) (by linarith [him.1]) (by linarith [him.2.1])
    have h2 := hbd1 (z + (ζ + (t : ℂ))) (by linarith [him.2.2.1]) (by linarith [him.2.2.2])
    rw [iteratedDeriv_one] at h1 h2
    have hre : |z.re - b.re| ≤ δ := (Complex.abs_re_le_norm (z - b)).trans (mem_ball_iff_norm.mp hz).le
    have hexp1 : Real.exp (-π * |(z - (ζ + (t : ℂ))).re|) ≤
        Real.exp (π * δ) * Real.exp (-π * |ζ.re - b.re + t|) := by
      have hr : |(z - (ζ + (t : ℂ))).re| = |ζ.re - z.re + t| := by
        rw [Complex.sub_re, Complex.add_re, Complex.ofReal_re, ← abs_neg]; congr 1; ring
      rw [hr, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have htri : |ζ.re - b.re + t| ≤ |ζ.re - z.re + t| + |z.re - b.re| := by
        calc |ζ.re - b.re + t| = |(ζ.re - z.re + t) + (z.re - b.re)| := by ring_nf
          _ ≤ |ζ.re - z.re + t| + |z.re - b.re| := abs_add_le _ _
      have hbd : -|ζ.re - z.re + t| ≤ δ - |ζ.re - b.re + t| := by linarith [htri, hre]
      calc -π * |ζ.re - z.re + t| = π * (-|ζ.re - z.re + t|) := by ring
        _ ≤ π * (δ - |ζ.re - b.re + t|) := mul_le_mul_of_nonneg_left hbd hpi.le
        _ = π * δ + -π * |ζ.re - b.re + t| := by ring
    have hexp2 : Real.exp (-π * |(z + (ζ + (t : ℂ))).re|) ≤
        Real.exp (π * δ) * Real.exp (-π * |ζ.re + b.re + t|) := by
      have hr : |(z + (ζ + (t : ℂ))).re| = |ζ.re + z.re + t| := by
        rw [Complex.add_re, Complex.add_re, Complex.ofReal_re]; congr 1; ring
      rw [hr, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have htri : |ζ.re + b.re + t| ≤ |ζ.re + z.re + t| + |z.re - b.re| := by
        calc |ζ.re + b.re + t| = |(ζ.re + z.re + t) - (z.re - b.re)| := by ring_nf
          _ ≤ |ζ.re + z.re + t| + |z.re - b.re| := abs_sub _ _
      have hbd : -|ζ.re + z.re + t| ≤ δ - |ζ.re + b.re + t| := by linarith [htri, hre]
      calc -π * |ζ.re + z.re + t| = π * (-|ζ.re + z.re + t|) := by ring
        _ ≤ π * (δ - |ζ.re + b.re + t|) := mul_le_mul_of_nonneg_left hbd hpi.le
        _ = π * δ + -π * |ζ.re + b.re + t| := by ring
    calc ‖F' z t‖
        ≤ ‖deriv sinhKernel (z - (ζ + (t : ℂ)))‖ + ‖deriv sinhKernel (z + (ζ + (t : ℂ)))‖ :=
          norm_sub_le _ _
      _ ≤ C₁ * Real.exp (-π * |(z - (ζ + (t : ℂ))).re|) +
            C₁ * Real.exp (-π * |(z + (ζ + (t : ℂ))).re|) := add_le_add h1 h2
      _ ≤ C₁ * (Real.exp (π * δ) * Real.exp (-π * |ζ.re - b.re + t|)) +
            C₁ * (Real.exp (π * δ) * Real.exp (-π * |ζ.re + b.re + t|)) := by gcongr
      _ = bound t := by dsimp [bound]; ring
  have hbound_int : Integrable bound (volume.restrict (Ioi 0)) :=
    ((phiZeta_integrable_exp_bound (ζ.re - b.re)).add
      (phiZeta_integrable_exp_bound (ζ.re + b.re))).const_mul (C₁ * Real.exp (π * δ))
  have h_diff : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ z ∈ Metric.ball b δ,
      HasDerivAt (F · t) (F' z t) z := by
    refine ae_of_all _ fun t z hz => ?_
    have him := him_ball z hz t
    have ho : {w : ℂ | 0 < w.im ∧ w.im < 1} ∈ 𝓝 (z - (ζ + (t : ℂ))) :=
      (isOpen_Ioo.preimage Complex.continuous_im).mem_nhds ⟨by linarith [him.1], by linarith [him.2.1]⟩
    have ho2 : {w : ℂ | 0 < w.im ∧ w.im < 1} ∈ 𝓝 (z + (ζ + (t : ℂ))) :=
      (isOpen_Ioo.preimage Complex.continuous_im).mem_nhds ⟨by linarith [him.2.2.1], by linarith [him.2.2.2]⟩
    have hd1 : HasDerivAt sinhKernel (deriv sinhKernel (z - (ζ + (t : ℂ)))) (z - (ζ + (t : ℂ))) :=
      (sinhKernel_differentiableOn _ ⟨by linarith [him.1], by linarith [him.2.1]⟩).differentiableAt
        ho |>.hasDerivAt
    have hd2 : HasDerivAt sinhKernel (deriv sinhKernel (z + (ζ + (t : ℂ)))) (z + (ζ + (t : ℂ))) :=
      (sinhKernel_differentiableOn _ ⟨by linarith [him.2.2.1], by linarith [him.2.2.2]⟩).differentiableAt
        ho2 |>.hasDerivAt
    have hlin1 : HasDerivAt (fun u : ℂ => u - (ζ + (t : ℂ))) 1 z := (hasDerivAt_id z).sub_const _
    have hlin2 : HasDerivAt (fun u : ℂ => u + (ζ + (t : ℂ))) 1 z := (hasDerivAt_id z).add_const _
    have hsub := (hd1.comp z hlin1).sub (hd2.comp z hlin2)
    refine hsub.congr_deriv ?_
    dsimp [F']; ring
  have hparam := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds b hδ)
    hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  have him0 := sinhKernel_sub_im_mem hb hζ.2
  have hftc_deriv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s : ℝ => -sinhKernel (b - (ζ + (s : ℂ))) - sinhKernel (b + (ζ + (s : ℂ))))
        (F' b t) t := by
    intro t _
    have ho1 : {w : ℂ | 0 < w.im ∧ w.im < 1} ∈ 𝓝 (b - (ζ + (t : ℂ))) :=
      (isOpen_Ioo.preimage Complex.continuous_im).mem_nhds ⟨by linarith [(him0 t).1], by linarith [(him0 t).2.1]⟩
    have ho2 : {w : ℂ | 0 < w.im ∧ w.im < 1} ∈ 𝓝 (b + (ζ + (t : ℂ))) :=
      (isOpen_Ioo.preimage Complex.continuous_im).mem_nhds ⟨by linarith [(him0 t).2.2.1], by linarith [(him0 t).2.2.2]⟩
    have hd1 := (sinhKernel_differentiableOn _ ⟨by linarith [(him0 t).1], by linarith [(him0 t).2.1]⟩).differentiableAt
      ho1 |>.hasDerivAt
    have hd2 := (sinhKernel_differentiableOn _ ⟨by linarith [(him0 t).2.2.1], by linarith [(him0 t).2.2.2]⟩).differentiableAt
      ho2 |>.hasDerivAt
    have hl1 : HasDerivAt (fun s : ℝ => b - (ζ + (s : ℂ))) (-1 : ℂ) t := by
      have := ((hasDerivAt_id t).ofReal_comp.const_add ζ).const_sub b
      refine this.congr_deriv ?_; simp
    have hl2 : HasDerivAt (fun s : ℝ => b + (ζ + (s : ℂ))) (1 : ℂ) t := by
      have := ((hasDerivAt_id t).ofReal_comp.const_add ζ).const_add b
      refine this.congr_deriv ?_; simp
    have hcomp := (hd1.comp t hl1).neg.sub (hd2.comp t hl2)
    refine hcomp.congr_deriv ?_
    dsimp [F']; ring
  have hftc_tend : Tendsto (fun s : ℝ => -sinhKernel (b - (ζ + (s : ℂ))) - sinhKernel (b + (ζ + (s : ℂ))))
      atTop (𝓝 0) := by
    obtain ⟨C₀, hC₀, hbd0⟩ := sinhKernel_bound_of_im (s₀ := 1 / 16) (by norm_num) (by norm_num)
    have h_to_zero : ∀ u : ℝ, Tendsto (fun s : ℝ => Real.exp (-π * |u + s|)) atTop (𝓝 0) := by
      intro u
      have hlin : Tendsto (fun s : ℝ => |u + s|) atTop atTop :=
        tendsto_abs_atTop_atTop.comp (Filter.tendsto_atTop.mpr fun M =>
          Filter.eventually_atTop.mpr ⟨M - u, fun s hs => by linarith⟩)
      have h1 : Tendsto (fun s : ℝ => -π * |u + s|) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg (by linarith) hlin
      exact Real.tendsto_exp_atBot.comp h1
    have h_lim_sum : Tendsto (fun s : ℝ =>
        C₀ * (Real.exp (-π * |ζ.re - b.re + s|) + Real.exp (-π * |ζ.re + b.re + s|))) atTop (𝓝 0) := by
      simpa only [add_zero, mul_zero] using
        ((h_to_zero (ζ.re - b.re)).add (h_to_zero (ζ.re + b.re))).const_mul C₀
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero (fun _ => norm_nonneg _) (fun s => ?_) h_lim_sum
    have h1 := (hbd0 (b - (ζ + (s : ℂ))) (him0 s).1 (by linarith [(him0 s).2.1])).2
    have h2 := (hbd0 (b + (ζ + (s : ℂ))) (him0 s).2.2.1 (by linarith [(him0 s).2.2.2])).2
    have hr1 : |(b - (ζ + (s : ℂ))).re| = |ζ.re - b.re + s| := by
      rw [Complex.sub_re, Complex.add_re, Complex.ofReal_re, ← abs_neg]; congr 1; ring
    have hr2 : |(b + (ζ + (s : ℂ))).re| = |ζ.re + b.re + s| := by
      rw [Complex.add_re, Complex.add_re, Complex.ofReal_re]; congr 1; ring
    rw [hr1] at h1; rw [hr2] at h2
    calc ‖-sinhKernel (b - (ζ + (s : ℂ))) - sinhKernel (b + (ζ + (s : ℂ)))‖
        ≤ ‖-sinhKernel (b - (ζ + (s : ℂ)))‖ + ‖sinhKernel (b + (ζ + (s : ℂ)))‖ := norm_sub_le _ _
      _ = ‖sinhKernel (b - (ζ + (s : ℂ)))‖ + ‖sinhKernel (b + (ζ + (s : ℂ)))‖ := by rw [norm_neg]
      _ ≤ C₀ * Real.exp (-π * |ζ.re - b.re + s|) + C₀ * Real.exp (-π * |ζ.re + b.re + s|) := add_le_add h1 h2
      _ = C₀ * (Real.exp (-π * |ζ.re - b.re + s|) + Real.exp (-π * |ζ.re + b.re + s|)) := by ring
  have hF'_int : IntegrableOn (F' b) (Ioi 0) :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds b hδ)
      hF_meas hF_int hF'_meas h_bound hbound_int h_diff).1
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hftc_deriv hF'_int hftc_tend
  simp only [Complex.ofReal_zero, add_zero, zero_sub] at hftc
  have hval : -(-sinhKernel (b - ζ) - sinhKernel (b + ζ)) = sinhKernel (b - ζ) + sinhKernel (b + ζ) := by
    ring
  rw [hval] at hftc
  change HasDerivAt (fun z => phiZeta ζ z) (∫ t in Ioi (0 : ℝ), F' b t) b at hparam
  rwa [hftc] at hparam

/-- First partial derivative of $\varphi_\zeta(b)$ in $\zeta$:
$\partial_\zeta \varphi_\zeta(b) = -\frac{\pi}{\sinh\pi(b - \zeta)} + \frac{\pi}{\sinh\pi(b + \zeta)}$. -/
theorem hasDerivAt_phiZeta_zeta {ζ b : ℂ} (hb : b ∈ combNOpen) (hζ : ζ ∈ combZOpen) :
    HasDerivAt (fun w => phiZeta w b) (-sinhKernel (b - ζ) + sinhKernel (b + ζ)) ζ := by
  have hpi := Real.pi_pos
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_combZOpen ζ hζ
  set δ := min r (1 / 32)
  have hδ : 0 < δ := lt_min hr (by norm_num)
  have hball_sub : Metric.ball ζ δ ⊆ combZOpen := (Metric.ball_subset_ball (min_le_left _ _)).trans hball
  obtain ⟨C₁, hC₁, hbd1⟩ := sinhKernel_iteratedDeriv_bound (k := 1) (s₀ := 1 / 32)
    (by norm_num) (by norm_num)
  let F : ℂ → ℝ → ℂ := fun w t => sinhKernel (b - (w + (t : ℂ))) - sinhKernel (b + (w + (t : ℂ)))
  let F' : ℂ → ℝ → ℂ := fun w t =>
    -deriv sinhKernel (b - (w + (t : ℂ))) - deriv sinhKernel (b + (w + (t : ℂ)))
  let bound : ℝ → ℝ := fun t => C₁ * Real.exp (π * δ) *
    (Real.exp (-π * |ζ.re - b.re + t|) + Real.exp (-π * |ζ.re + b.re + t|))
  have hF_meas : ∀ᶠ w in 𝓝 ζ, AEStronglyMeasurable (F w) (volume.restrict (Ioi 0)) := by
    filter_upwards [Metric.ball_mem_nhds ζ hδ] with w hw
    exact (phiZeta_integrand_integrable w b hb (hball_sub hw)).aestronglyMeasurable
  have hF_int : Integrable (F ζ) (volume.restrict (Ioi 0)) :=
    phiZeta_integrand_integrable ζ b hb hζ
  have him_ball : ∀ w ∈ Metric.ball ζ δ, ∀ t : ℝ,
      1 / 16 ≤ (b - (w + (t : ℂ))).im ∧ (b - (w + (t : ℂ))).im ≤ 15 / 16 ∧
      1 / 16 ≤ (b + (w + (t : ℂ))).im ∧ (b + (w + (t : ℂ))).im ≤ 15 / 16 :=
    fun w hw t => sinhKernel_sub_im_mem hb (hball_sub hw).2 t
  have hF'_meas : AEStronglyMeasurable (F' ζ) (volume.restrict (Ioi 0)) := by
    have hcont : Continuous (F' ζ) := by
      have hd_an : AnalyticOnNhd ℂ sinhKernel {w : ℂ | 0 < w.im ∧ w.im < 1} :=
        sinhKernel_differentiableOn.analyticOnNhd
          ((isOpen_lt continuous_const Complex.continuous_im).inter
            (isOpen_lt Complex.continuous_im continuous_const))
      have hd_cont : ContinuousOn (deriv sinhKernel) {w : ℂ | 0 < w.im ∧ w.im < 1} :=
        hd_an.deriv.continuousOn
      have hm1 : Continuous (fun t : ℝ => b - (ζ + (t : ℂ))) :=
        continuous_const.sub (continuous_const.add Complex.continuous_ofReal)
      have hm2 : Continuous (fun t : ℝ => b + (ζ + (t : ℂ))) :=
        continuous_const.add (continuous_const.add Complex.continuous_ofReal)
      have him := sinhKernel_sub_im_mem hb hζ.2
      exact (hd_cont.comp_continuous hm1 fun t => ⟨by linarith [(him t).1], by linarith [(him t).2.1]⟩).neg.sub
        (hd_cont.comp_continuous hm2 fun t => ⟨by linarith [(him t).2.2.1], by linarith [(him t).2.2.2]⟩)
    exact hcont.aestronglyMeasurable
  have h_bound : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ w ∈ Metric.ball ζ δ, ‖F' w t‖ ≤ bound t := by
    refine ae_of_all _ fun t w hw => ?_
    have him := him_ball w hw t
    have h1 := hbd1 (b - (w + (t : ℂ))) (by linarith [him.1]) (by linarith [him.2.1])
    have h2 := hbd1 (b + (w + (t : ℂ))) (by linarith [him.2.2.1]) (by linarith [him.2.2.2])
    rw [iteratedDeriv_one] at h1 h2
    have hre : |w.re - ζ.re| ≤ δ := (Complex.abs_re_le_norm (w - ζ)).trans (mem_ball_iff_norm.mp hw).le
    have hexp1 : Real.exp (-π * |(b - (w + (t : ℂ))).re|) ≤
        Real.exp (π * δ) * Real.exp (-π * |ζ.re - b.re + t|) := by
      have hr : |(b - (w + (t : ℂ))).re| = |w.re - b.re + t| := by
        rw [Complex.sub_re, Complex.add_re, Complex.ofReal_re, ← abs_neg]; congr 1; ring
      rw [hr, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have htri : |ζ.re - b.re + t| ≤ |w.re - b.re + t| + |w.re - ζ.re| := by
        calc |ζ.re - b.re + t| = |(w.re - b.re + t) - (w.re - ζ.re)| := by ring_nf
          _ ≤ |w.re - b.re + t| + |w.re - ζ.re| := abs_sub _ _
      have hbd : -|w.re - b.re + t| ≤ δ - |ζ.re - b.re + t| := by linarith [htri, hre]
      calc -π * |w.re - b.re + t| = π * (-|w.re - b.re + t|) := by ring
        _ ≤ π * (δ - |ζ.re - b.re + t|) := mul_le_mul_of_nonneg_left hbd hpi.le
        _ = π * δ + -π * |ζ.re - b.re + t| := by ring
    have hexp2 : Real.exp (-π * |(b + (w + (t : ℂ))).re|) ≤
        Real.exp (π * δ) * Real.exp (-π * |ζ.re + b.re + t|) := by
      have hr : |(b + (w + (t : ℂ))).re| = |w.re + b.re + t| := by
        rw [Complex.add_re, Complex.add_re, Complex.ofReal_re]; congr 1; ring
      rw [hr, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have htri : |ζ.re + b.re + t| ≤ |w.re + b.re + t| + |w.re - ζ.re| := by
        calc |ζ.re + b.re + t| = |(w.re + b.re + t) - (w.re - ζ.re)| := by ring_nf
          _ ≤ |w.re + b.re + t| + |w.re - ζ.re| := abs_sub _ _
      have hbd : -|w.re + b.re + t| ≤ δ - |ζ.re + b.re + t| := by linarith [htri, hre]
      calc -π * |w.re + b.re + t| = π * (-|w.re + b.re + t|) := by ring
        _ ≤ π * (δ - |ζ.re + b.re + t|) := mul_le_mul_of_nonneg_left hbd hpi.le
        _ = π * δ + -π * |ζ.re + b.re + t| := by ring
    calc ‖F' w t‖
        ≤ ‖-deriv sinhKernel (b - (w + (t : ℂ)))‖ + ‖deriv sinhKernel (b + (w + (t : ℂ)))‖ :=
          norm_sub_le _ _
      _ = ‖deriv sinhKernel (b - (w + (t : ℂ)))‖ + ‖deriv sinhKernel (b + (w + (t : ℂ)))‖ := by
          rw [norm_neg]
      _ ≤ C₁ * Real.exp (-π * |(b - (w + (t : ℂ))).re|) +
            C₁ * Real.exp (-π * |(b + (w + (t : ℂ))).re|) := add_le_add h1 h2
      _ ≤ C₁ * (Real.exp (π * δ) * Real.exp (-π * |ζ.re - b.re + t|)) +
            C₁ * (Real.exp (π * δ) * Real.exp (-π * |ζ.re + b.re + t|)) := by gcongr
      _ = bound t := by dsimp [bound]; ring
  have hbound_int : Integrable bound (volume.restrict (Ioi 0)) :=
    ((phiZeta_integrable_exp_bound (ζ.re - b.re)).add
      (phiZeta_integrable_exp_bound (ζ.re + b.re))).const_mul (C₁ * Real.exp (π * δ))
  have h_diff : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ w ∈ Metric.ball ζ δ,
      HasDerivAt (F · t) (F' w t) w := by
    refine ae_of_all _ fun t w hw => ?_
    have him := him_ball w hw t
    have ho1 : {u : ℂ | 0 < u.im ∧ u.im < 1} ∈ 𝓝 (b - (w + (t : ℂ))) :=
      (isOpen_Ioo.preimage Complex.continuous_im).mem_nhds ⟨by linarith [him.1], by linarith [him.2.1]⟩
    have ho2 : {u : ℂ | 0 < u.im ∧ u.im < 1} ∈ 𝓝 (b + (w + (t : ℂ))) :=
      (isOpen_Ioo.preimage Complex.continuous_im).mem_nhds ⟨by linarith [him.2.2.1], by linarith [him.2.2.2]⟩
    have hd1 : HasDerivAt sinhKernel (deriv sinhKernel (b - (w + (t : ℂ)))) (b - (w + (t : ℂ))) :=
      (sinhKernel_differentiableOn _ ⟨by linarith [him.1], by linarith [him.2.1]⟩).differentiableAt
        ho1 |>.hasDerivAt
    have hd2 : HasDerivAt sinhKernel (deriv sinhKernel (b + (w + (t : ℂ)))) (b + (w + (t : ℂ))) :=
      (sinhKernel_differentiableOn _ ⟨by linarith [him.2.2.1], by linarith [him.2.2.2]⟩).differentiableAt
        ho2 |>.hasDerivAt
    have hlin1 : HasDerivAt (fun u : ℂ => b - (u + (t : ℂ))) (-1) w := by
      have := ((hasDerivAt_id w).add_const (t : ℂ)).const_sub b
      refine this.congr_deriv ?_; simp
    have hlin2 : HasDerivAt (fun u : ℂ => b + (u + (t : ℂ))) 1 w := by
      have := ((hasDerivAt_id w).add_const (t : ℂ)).const_add b
      refine this.congr_deriv ?_; simp
    have hsub := (hd1.comp w hlin1).sub (hd2.comp w hlin2)
    refine hsub.congr_deriv ?_
    dsimp [F']; ring
  have hparam := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds ζ hδ)
    hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  have him0 := sinhKernel_sub_im_mem hb hζ.2
  have hftc_deriv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s : ℝ => sinhKernel (b - (ζ + (s : ℂ))) - sinhKernel (b + (ζ + (s : ℂ))))
        (F' ζ t) t := by
    intro t _
    have ho1 : {w : ℂ | 0 < w.im ∧ w.im < 1} ∈ 𝓝 (b - (ζ + (t : ℂ))) :=
      (isOpen_Ioo.preimage Complex.continuous_im).mem_nhds ⟨by linarith [(him0 t).1], by linarith [(him0 t).2.1]⟩
    have ho2 : {w : ℂ | 0 < w.im ∧ w.im < 1} ∈ 𝓝 (b + (ζ + (t : ℂ))) :=
      (isOpen_Ioo.preimage Complex.continuous_im).mem_nhds ⟨by linarith [(him0 t).2.2.1], by linarith [(him0 t).2.2.2]⟩
    have hd1 := (sinhKernel_differentiableOn _ ⟨by linarith [(him0 t).1], by linarith [(him0 t).2.1]⟩).differentiableAt
      ho1 |>.hasDerivAt
    have hd2 := (sinhKernel_differentiableOn _ ⟨by linarith [(him0 t).2.2.1], by linarith [(him0 t).2.2.2]⟩).differentiableAt
      ho2 |>.hasDerivAt
    have hl1 : HasDerivAt (fun s : ℝ => b - (ζ + (s : ℂ))) (-1 : ℂ) t := by
      have := ((hasDerivAt_id t).ofReal_comp.const_add ζ).const_sub b
      refine this.congr_deriv ?_; simp
    have hl2 : HasDerivAt (fun s : ℝ => b + (ζ + (s : ℂ))) (1 : ℂ) t := by
      have := ((hasDerivAt_id t).ofReal_comp.const_add ζ).const_add b
      refine this.congr_deriv ?_; simp
    have hcomp := (hd1.comp t hl1).sub (hd2.comp t hl2)
    refine hcomp.congr_deriv ?_
    dsimp [F']; ring
  have hftc_tend : Tendsto (fun s : ℝ => sinhKernel (b - (ζ + (s : ℂ))) - sinhKernel (b + (ζ + (s : ℂ))))
      atTop (𝓝 0) := by
    obtain ⟨C₀, hC₀, hbd0⟩ := sinhKernel_bound_of_im (s₀ := 1 / 16) (by norm_num) (by norm_num)
    have h_to_zero : ∀ u : ℝ, Tendsto (fun s : ℝ => Real.exp (-π * |u + s|)) atTop (𝓝 0) := by
      intro u
      have hlin : Tendsto (fun s : ℝ => |u + s|) atTop atTop :=
        tendsto_abs_atTop_atTop.comp (Filter.tendsto_atTop.mpr fun M =>
          Filter.eventually_atTop.mpr ⟨M - u, fun s hs => by linarith⟩)
      have h1 : Tendsto (fun s : ℝ => -π * |u + s|) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg (by linarith) hlin
      exact Real.tendsto_exp_atBot.comp h1
    have h_lim_sum : Tendsto (fun s : ℝ =>
        C₀ * (Real.exp (-π * |ζ.re - b.re + s|) + Real.exp (-π * |ζ.re + b.re + s|))) atTop (𝓝 0) := by
      simpa only [add_zero, mul_zero] using
        ((h_to_zero (ζ.re - b.re)).add (h_to_zero (ζ.re + b.re))).const_mul C₀
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero (fun _ => norm_nonneg _) (fun s => ?_) h_lim_sum
    have h1 := (hbd0 (b - (ζ + (s : ℂ))) (him0 s).1 (by linarith [(him0 s).2.1])).2
    have h2 := (hbd0 (b + (ζ + (s : ℂ))) (him0 s).2.2.1 (by linarith [(him0 s).2.2.2])).2
    have hr1 : |(b - (ζ + (s : ℂ))).re| = |ζ.re - b.re + s| := by
      rw [Complex.sub_re, Complex.add_re, Complex.ofReal_re, ← abs_neg]; congr 1; ring
    have hr2 : |(b + (ζ + (s : ℂ))).re| = |ζ.re + b.re + s| := by
      rw [Complex.add_re, Complex.add_re, Complex.ofReal_re]; congr 1; ring
    rw [hr1] at h1; rw [hr2] at h2
    calc ‖sinhKernel (b - (ζ + (s : ℂ))) - sinhKernel (b + (ζ + (s : ℂ)))‖
        ≤ ‖sinhKernel (b - (ζ + (s : ℂ)))‖ + ‖sinhKernel (b + (ζ + (s : ℂ)))‖ := norm_sub_le _ _
      _ ≤ C₀ * Real.exp (-π * |ζ.re - b.re + s|) + C₀ * Real.exp (-π * |ζ.re + b.re + s|) := add_le_add h1 h2
      _ = C₀ * (Real.exp (-π * |ζ.re - b.re + s|) + Real.exp (-π * |ζ.re + b.re + s|)) := by ring
  have hF'_int : IntegrableOn (F' ζ) (Ioi 0) :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds ζ hδ)
      hF_meas hF_int hF'_meas h_bound hbound_int h_diff).1
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hftc_deriv hF'_int hftc_tend
  simp only [Complex.ofReal_zero, add_zero, zero_sub] at hftc
  have hval : -(sinhKernel (b - ζ) - sinhKernel (b + ζ)) = -sinhKernel (b - ζ) + sinhKernel (b + ζ) := by
    ring
  rw [hval] at hftc
  change HasDerivAt (fun w => phiZeta w b) (∫ t in Ioi (0 : ℝ), F' ζ t) ζ at hparam
  rwa [hftc] at hparam

/-- **K1(d), $\varphi_\zeta(i/2) = 0$**. -/
theorem phiZeta_half_I (ζ : ℂ) : phiZeta ζ (Complex.I / 2) = 0 := by
  have heq : ∀ t : ℝ, sinhKernel (Complex.I / 2 - (ζ + (t : ℂ))) =
      sinhKernel (Complex.I / 2 + (ζ + (t : ℂ))) := by
    intro t
    unfold sinhKernel
    congr 1
    have h1 : (π : ℂ) * (Complex.I / 2 - (ζ + (t : ℂ))) =
        ((π / 2 : ℝ) : ℂ) * Complex.I - (π : ℂ) * (ζ + (t : ℂ)) := by
      push_cast; ring
    have h2 : (π : ℂ) * (Complex.I / 2 + (ζ + (t : ℂ))) =
        ((π / 2 : ℝ) : ℂ) * Complex.I + (π : ℂ) * (ζ + (t : ℂ)) := by
      push_cast; ring
    rw [h1, h2, Complex.sinh_sub, Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I,
      ← Complex.ofReal_sin, ← Complex.ofReal_cos, Real.sin_pi_div_two, Real.cos_pi_div_two]
    simp
  unfold phiZeta
  simp_rw [heq, sub_self, integral_zero]

/-- **K1(d), norm bound**: $|\varphi_\zeta(b)| \le C \min(1, e^{-\pi(\operatorname{Re}\zeta - |x|)})$
on $\mathcal{N} \times \{\operatorname{Re}\zeta \ge 0, |\operatorname{Im}\zeta| \le 1/8\}$. -/
theorem norm_phiZeta_le :
    ∃ C > 0, ∀ {ζ b : ℂ}, b ∈ combN → ζ ∈ combZ →
      ‖phiZeta ζ b‖ ≤ C * min 1 (Real.exp (-π * (ζ.re - |b.re|))) := by
  obtain ⟨C₀, hC₀, hbd⟩ := sinhKernel_bound_of_im (s₀ := 1 / 8) (by norm_num) (by norm_num)
  have hpi := Real.pi_pos
  set C := 4 * C₀ / π
  refine ⟨C, by positivity, fun {ζ b} hb hζ => ?_⟩
  have hb' : |b.im - 1 / 2| ≤ 1 / 4 := hb
  have hζ_im : |ζ.im| ≤ 1 / 8 := hζ.2
  have him : ∀ t : ℝ, 1 / 8 ≤ (b - (ζ + (t : ℂ))).im ∧ (b - (ζ + (t : ℂ))).im ≤ 7 / 8 ∧
      1 / 8 ≤ (b + (ζ + (t : ℂ))).im ∧ (b + (ζ + (t : ℂ))).im ≤ 7 / 8 := by
    intro t
    have hb1 := (abs_le.mp hb').1; have hb2 := (abs_le.mp hb').2
    have hζ1 := (abs_le.mp hζ_im).1; have hζ2 := (abs_le.mp hζ_im).2
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, add_zero]
    norm_num at *
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hpt : ∀ t : ℝ,
      ‖sinhKernel (b - (ζ + (t : ℂ))) - sinhKernel (b + (ζ + (t : ℂ)))‖ ≤
        C₀ * (Real.exp (-π * |ζ.re - b.re + t|) + Real.exp (-π * |ζ.re + b.re + t|)) := by
    intro t
    have h1 := (hbd (b - (ζ + (t : ℂ))) (him t).1 (by linarith [(him t).2.1])).2
    have h2 := (hbd (b + (ζ + (t : ℂ))) (him t).2.2.1 (by linarith [(him t).2.2.2])).2
    have hr1 : |(b - (ζ + (t : ℂ))).re| = |ζ.re - b.re + t| := by
      rw [Complex.sub_re, Complex.add_re, Complex.ofReal_re, ← abs_neg]; congr 1; ring
    have hr2 : |(b + (ζ + (t : ℂ))).re| = |ζ.re + b.re + t| := by
      rw [Complex.add_re, Complex.add_re, Complex.ofReal_re]; congr 1; ring
    rw [hr1] at h1; rw [hr2] at h2
    exact (norm_sub_le _ _).trans (by rw [mul_add]; exact add_le_add h1 h2)
  have hint_dom : IntegrableOn (fun t : ℝ => C₀ * (Real.exp (-π * |ζ.re - b.re + t|) +
      Real.exp (-π * |ζ.re + b.re + t|))) (Ioi (0 : ℝ)) :=
    ((phiZeta_integrable_exp_bound (ζ.re - b.re)).add
      (phiZeta_integrable_exp_bound (ζ.re + b.re))).const_mul C₀
  have hnorm_le_int : ‖phiZeta ζ b‖ ≤
      ∫ t in Ioi (0 : ℝ), C₀ * (Real.exp (-π * |ζ.re - b.re + t|) + Real.exp (-π * |ζ.re + b.re + t|)) := by
    unfold phiZeta
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
    exact MeasureTheory.setIntegral_mono_on
      (phiZeta_integrand_integrable ζ b (combN_subset_combNOpen hb) (combZ_subset_combZOpen hζ)).norm
      hint_dom measurableSet_Ioi fun t _ => hpt t
  have h_le_C : ‖phiZeta ζ b‖ ≤ C := by
    refine hnorm_le_int.trans ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add (phiZeta_integrable_exp_bound (ζ.re - b.re))
        (phiZeta_integrable_exp_bound (ζ.re + b.re))]
    have i1 := integral_exp_neg_pi_abs_le (ζ.re - b.re)
    have i2 := integral_exp_neg_pi_abs_le (ζ.re + b.re)
    dsimp [C]
    have hsum : C₀ * (2 / π + 2 / π) = 4 * C₀ / π := by ring
    nlinarith
  rcases le_or_gt ζ.re |b.re| with hle | hlt
  · have hmin : min 1 (Real.exp (-π * (ζ.re - |b.re|))) = 1 :=
      min_eq_left (Real.one_le_exp (by nlinarith))
    rwa [hmin, mul_one]
  · have hmin : min 1 (Real.exp (-π * (ζ.re - |b.re|))) = Real.exp (-π * (ζ.re - |b.re|)) :=
      min_eq_right (Real.exp_le_one_iff.mpr (by nlinarith))
    rw [hmin]
    have hdom2 : IntegrableOn (fun t : ℝ => 2 * C₀ * Real.exp (-π * (ζ.re - |b.re|)) *
        Real.exp (-π * t)) (Ioi (0 : ℝ)) :=
      (integrableOn_exp_mul_Ioi (by linarith : -π < 0) 0).const_mul _
    have hpt2 : ∀ t ∈ Ioi (0 : ℝ),
        C₀ * (Real.exp (-π * |ζ.re - b.re + t|) + Real.exp (-π * |ζ.re + b.re + t|)) ≤
          2 * C₀ * Real.exp (-π * (ζ.re - |b.re|)) * Real.exp (-π * t) := by
      intro t ht
      have ht0 : 0 ≤ t := ht.le
      have h1 : ζ.re - |b.re| + t ≤ |ζ.re - b.re + t| := by
        calc ζ.re - |b.re| + t ≤ ζ.re - b.re + t := by linarith [le_abs_self b.re]
          _ ≤ |ζ.re - b.re + t| := le_abs_self _
      have h2 : ζ.re - |b.re| + t ≤ |ζ.re + b.re + t| := by
        calc ζ.re - |b.re| + t ≤ ζ.re + b.re + t := by linarith [neg_le_abs b.re]
          _ ≤ |ζ.re + b.re + t| := le_abs_self _
      have e1 : Real.exp (-π * |ζ.re - b.re + t|) ≤ Real.exp (-π * (ζ.re - |b.re|)) * Real.exp (-π * t) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
      have e2 : Real.exp (-π * |ζ.re + b.re + t|) ≤ Real.exp (-π * (ζ.re - |b.re|)) * Real.exp (-π * t) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
      calc C₀ * (Real.exp (-π * |ζ.re - b.re + t|) + Real.exp (-π * |ζ.re + b.re + t|))
          ≤ C₀ * (Real.exp (-π * (ζ.re - |b.re|)) * Real.exp (-π * t) +
              Real.exp (-π * (ζ.re - |b.re|)) * Real.exp (-π * t)) :=
            mul_le_mul_of_nonneg_left (add_le_add e1 e2) hC₀.le
        _ = 2 * C₀ * Real.exp (-π * (ζ.re - |b.re|)) * Real.exp (-π * t) := by ring
    have hint2 : ∫ t in Ioi (0 : ℝ), 2 * C₀ * Real.exp (-π * (ζ.re - |b.re|)) * Real.exp (-π * t) =
        (2 * C₀ / π) * Real.exp (-π * (ζ.re - |b.re|)) := by
      rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (by linarith : -π < 0) 0,
        mul_zero, Real.exp_zero]
      ring
    have hle2 : ‖phiZeta ζ b‖ ≤ (2 * C₀ / π) * Real.exp (-π * (ζ.re - |b.re|)) := by
      refine hnorm_le_int.trans ?_
      rw [← hint2]
      exact MeasureTheory.setIntegral_mono_on hint_dom hdom2 measurableSet_Ioi hpt2
    refine hle2.trans ?_
    have hexp_pos : 0 ≤ Real.exp (-π * (ζ.re - |b.re|)) := (Real.exp_pos _).le
    have hC2 : 2 * C₀ / π ≤ C := by dsimp [C]; gcongr; norm_num
    exact mul_le_mul_of_nonneg_right hC2 hexp_pos

/-- **K1(d), limit as $\operatorname{Re} \zeta \to +\infty$**: $\varphi_{\zeta + t}(b) \to 0$ as $t \to +\infty$. -/
theorem tendsto_phiZeta_atTop {ζ b : ℂ} (hb : b ∈ combN) (hζ : ζ ∈ combZ) :
    Tendsto (fun r : ℝ => phiZeta (ζ + (r : ℂ)) b) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbd⟩ := norm_phiZeta_le
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  have h0 : Tendsto (fun r : ℝ => C * Real.exp (-π * (ζ.re + r - |b.re|))) atTop (𝓝 0) := by
    have h_lin : Tendsto (fun r : ℝ => ζ.re + r - |b.re|) atTop atTop :=
      Filter.tendsto_atTop.mpr fun M => Filter.eventually_atTop.mpr ⟨M - ζ.re + |b.re|, fun r hr => by linarith⟩
    have h1 : Tendsto (fun r : ℝ => -π * (ζ.re + r - |b.re|)) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg (by linarith [Real.pi_pos]) h_lin
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul C
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  have hζr : ζ + (r : ℂ) ∈ combZ := ⟨by simp; linarith [hζ.1], by simpa using hζ.2⟩
  refine (hbd hb hζr).trans ?_
  have hre : (ζ + (r : ℂ)).re = ζ.re + r := by simp
  rw [hre]
  exact mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le

/-- **K1(d), exponential identity**: $\exp(\varphi_\zeta(b)) = -T_\zeta(b)$ on $\mathcal{N} \times \text{combZ}$. -/
theorem cexp_phiZeta {ζ b : ℂ} (hb : b ∈ combN) (hζ : ζ ∈ combZ) :
    Complex.exp (phiZeta ζ b) = -blaschkeT ζ b := by
  have hpi := Real.pi_pos
  have hden_ne : ∀ t : ℝ, 0 ≤ t →
      Complex.cosh ((π : ℂ) * b) + Complex.cosh ((π : ℂ) * (ζ + (t : ℂ))) ≠ 0 := by
    intro t _
    rw [cosh_pi_add_cosh_pi]
    have him1 : |((π : ℂ) * (b - (ζ + (t : ℂ))) / 2).im| < π / 2 := by
      have : ((π : ℂ) * (b - (ζ + (t : ℂ))) / 2).im = π * (b.im - ζ.im) / 2 := by
        simp [div_eq_mul_inv, Complex.mul_im]
      rw [this, abs_div, abs_mul, abs_of_pos hpi, abs_two]
      have hb' := abs_le.mp (show |b.im - 1 / 2| ≤ 1 / 4 from hb)
      have hζ' := abs_le.mp hζ.2
      have hbm : |b.im - ζ.im| ≤ 7 / 8 := by rw [abs_le]; constructor <;> linarith
      nlinarith only [hpi, hbm]
    have him2 : |((π : ℂ) * (b + (ζ + (t : ℂ))) / 2).im| < π / 2 := by
      have : ((π : ℂ) * (b + (ζ + (t : ℂ))) / 2).im = π * (b.im + ζ.im) / 2 := by
        simp [div_eq_mul_inv, Complex.mul_im]
      rw [this, abs_div, abs_mul, abs_of_pos hpi, abs_two]
      have hb' := abs_le.mp (show |b.im - 1 / 2| ≤ 1 / 4 from hb)
      have hζ' := abs_le.mp hζ.2
      have hbm : |b.im + ζ.im| ≤ 7 / 8 := by rw [abs_le]; constructor <;> linarith
      nlinarith only [hpi, hbm]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (complex_cosh_ne_zero_of_abs_im_lt_pi_div_two him1))
      (complex_cosh_ne_zero_of_abs_im_lt_pi_div_two him2)
  have hnum_ne : ∀ t : ℝ, 0 ≤ t →
      Complex.cosh ((π : ℂ) * (ζ + (t : ℂ))) - Complex.cosh ((π : ℂ) * b) ≠ 0 := by
    intro t _
    rw [← neg_ne_zero, neg_sub, cosh_pi_sub_cosh_pi]
    have him1 : 0 < ((π : ℂ) * (b - (ζ + (t : ℂ))) / 2).im ∧
        ((π : ℂ) * (b - (ζ + (t : ℂ))) / 2).im < π := by
      have : ((π : ℂ) * (b - (ζ + (t : ℂ))) / 2).im = π * (b.im - ζ.im) / 2 := by
        simp [div_eq_mul_inv, Complex.mul_im]
      rw [this]
      have hb' := abs_le.mp (show |b.im - 1 / 2| ≤ 1 / 4 from hb)
      have hζ' := abs_le.mp hζ.2
      constructor <;> nlinarith only [hpi, hb'.1, hb'.2, hζ'.1, hζ'.2]
    have him2 : 0 < ((π : ℂ) * (b + (ζ + (t : ℂ))) / 2).im ∧
        ((π : ℂ) * (b + (ζ + (t : ℂ))) / 2).im < π := by
      have : ((π : ℂ) * (b + (ζ + (t : ℂ))) / 2).im = π * (b.im + ζ.im) / 2 := by
        simp [div_eq_mul_inv, Complex.mul_im]
      rw [this]
      have hb' := abs_le.mp (show |b.im - 1 / 2| ≤ 1 / 4 from hb)
      have hζ' := abs_le.mp hζ.2
      constructor <;> nlinarith only [hpi, hb'.1, hb'.2, hζ'.1, hζ'.2]
    have hsh_ne : ∀ z : ℂ, 0 < z.im → z.im < π → Complex.sinh z ≠ 0 := by
      intro z hz1 hz2 h0
      have hns : Complex.normSq (Complex.sinh z) = 0 := by rw [h0, map_zero]
      have hz_eq : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := Complex.ext (by simp) (by simp)
      rw [hz_eq, complex_sinh_normSq] at hns
      have hsin : 0 < Real.sin z.im := Real.sin_pos_of_pos_of_lt_pi hz1 hz2
      nlinarith [sq_nonneg (Real.sinh z.re), sq_pos_of_pos hsin]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (hsh_ne _ him1.1 him1.2)) (hsh_ne _ him2.1 him2.2)
  have hnegT_eq : ∀ t : ℝ, 0 ≤ t →
      -blaschkeT (ζ + (t : ℂ)) b =
        (Complex.cosh ((π : ℂ) * (ζ + (t : ℂ))) - Complex.cosh ((π : ℂ) * b)) /
          (Complex.cosh ((π : ℂ) * (ζ + (t : ℂ))) + Complex.cosh ((π : ℂ) * b)) := by
    intro t ht
    rw [blaschkeT_eq_cosh_div (hden_ne t ht)]
    ring
  let Q : ℝ → ℂ := fun t => Complex.exp (phiZeta (ζ + (t : ℂ)) b) / (-blaschkeT (ζ + (t : ℂ)) b)
  have hQ_deriv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt Q 0 t := by
    intro t ht
    have hζt : ζ + (t : ℂ) ∈ combZOpen := by
      change -1 / 4 < (ζ + (t : ℂ)).re ∧ |(ζ + (t : ℂ)).im| < 5 / 32
      have ht0 : 0 ≤ t := ht
      exact ⟨by simp; linarith [hζ.1], by simpa using lt_of_le_of_lt hζ.2 (by norm_num)⟩
    have hd_phi : HasDerivAt (fun s : ℝ => phiZeta (ζ + (s : ℂ)) b)
        (-sinhKernel (b - (ζ + (t : ℂ))) + sinhKernel (b + (ζ + (t : ℂ)))) t := by
      have hd2 := hasDerivAt_phiZeta_zeta (combN_subset_combNOpen hb) hζt
      have hlin : HasDerivAt (fun s : ℝ => ζ + (s : ℂ)) (1 : ℂ) t := by
        simpa using (hasDerivAt_id t).ofReal_comp.const_add ζ
      have hd3 := hd2.scomp t hlin
      simp only [one_smul] at hd3
      exact hd3
    have hd_exp : HasDerivAt (fun s : ℝ => Complex.exp (phiZeta (ζ + (s : ℂ)) b))
        (Complex.exp (phiZeta (ζ + (t : ℂ)) b) *
          (-sinhKernel (b - (ζ + (t : ℂ))) + sinhKernel (b + (ζ + (t : ℂ))))) t :=
      hd_phi.cexp
    have hd_num : HasDerivAt (fun s : ℝ =>
        Complex.cosh ((π : ℂ) * (ζ + (s : ℂ))) - Complex.cosh ((π : ℂ) * b))
        (Complex.sinh ((π : ℂ) * (ζ + (t : ℂ))) * (π : ℂ)) t := by
      have hlin : HasDerivAt (fun s : ℝ => (π : ℂ) * (ζ + (s : ℂ))) (π : ℂ) t := by
        have := ((hasDerivAt_id t).ofReal_comp.const_add ζ).const_mul (π : ℂ)
        refine this.congr_deriv ?_; simp
      exact (((Complex.hasDerivAt_cosh _).scomp t hlin).sub_const _).congr_deriv
        (by simp [smul_eq_mul, mul_comm])
    have hd_den : HasDerivAt (fun s : ℝ =>
        Complex.cosh ((π : ℂ) * (ζ + (s : ℂ))) + Complex.cosh ((π : ℂ) * b))
        (Complex.sinh ((π : ℂ) * (ζ + (t : ℂ))) * (π : ℂ)) t := by
      have hlin : HasDerivAt (fun s : ℝ => (π : ℂ) * (ζ + (s : ℂ))) (π : ℂ) t := by
        have := ((hasDerivAt_id t).ofReal_comp.const_add ζ).const_mul (π : ℂ)
        refine this.congr_deriv ?_; simp
      exact (((Complex.hasDerivAt_cosh _).scomp t hlin).add_const _).congr_deriv
        (by simp [smul_eq_mul, mul_comm])
    have hd_negT_rat : HasDerivAt (fun s : ℝ =>
        (Complex.cosh ((π : ℂ) * (ζ + (s : ℂ))) - Complex.cosh ((π : ℂ) * b)) /
          (Complex.cosh ((π : ℂ) * (ζ + (s : ℂ))) + Complex.cosh ((π : ℂ) * b)))
        (((Complex.sinh ((π : ℂ) * (ζ + (t : ℂ))) * (π : ℂ)) *
            (Complex.cosh ((π : ℂ) * (ζ + (t : ℂ))) + Complex.cosh ((π : ℂ) * b)) -
          (Complex.cosh ((π : ℂ) * (ζ + (t : ℂ))) - Complex.cosh ((π : ℂ) * b)) *
            (Complex.sinh ((π : ℂ) * (ζ + (t : ℂ))) * (π : ℂ))) /
          (Complex.cosh ((π : ℂ) * (ζ + (t : ℂ))) + Complex.cosh ((π : ℂ) * b)) ^ 2) t :=
      hd_num.div hd_den (by rw [add_comm]; exact hden_ne t ht)
    have h_ev : (fun s : ℝ => -blaschkeT (ζ + (s : ℂ)) b) =ᶠ[𝓝 t]
        fun s : ℝ => (Complex.cosh ((π : ℂ) * (ζ + (s : ℂ))) - Complex.cosh ((π : ℂ) * b)) /
          (Complex.cosh ((π : ℂ) * (ζ + (s : ℂ))) + Complex.cosh ((π : ℂ) * b)) := by
      have hopen : IsOpen {s : ℝ | Complex.cosh ((π : ℂ) * b) + Complex.cosh ((π : ℂ) * (ζ + (s : ℂ))) ≠ 0} :=
        isOpen_ne.preimage (by fun_prop)
      filter_upwards [hopen.mem_nhds (hden_ne t ht)] with s hs
      rw [blaschkeT_eq_cosh_div hs]; ring
    have hd_negT := hd_negT_rat.congr_of_eventuallyEq h_ev
    have hnegT_ne : -blaschkeT (ζ + (t : ℂ)) b ≠ 0 := by
      rw [hnegT_eq t ht, div_ne_zero_iff]
      exact ⟨hnum_ne t ht, by rw [add_comm]; exact hden_ne t ht⟩
    have hQ := hd_exp.div hd_negT hnegT_ne
    refine hQ.congr_deriv ?_
    rw [hnegT_eq t ht]
    set Cζ := Complex.cosh ((π : ℂ) * (ζ + (t : ℂ)))
    set Sζ := Complex.sinh ((π : ℂ) * (ζ + (t : ℂ)))
    set Cb := Complex.cosh ((π : ℂ) * b)
    have hcd : Cζ + Cb ≠ 0 := by rw [add_comm]; exact hden_ne t ht
    have hcm : Cζ - Cb ≠ 0 := hnum_ne t ht
    have hker : -sinhKernel (b - (ζ + (t : ℂ))) + sinhKernel (b + (ζ + (t : ℂ))) =
        2 * (π : ℂ) * Sζ * Cb / ((Cζ - Cb) * (Cζ + Cb)) := by
      unfold sinhKernel
      set u := (π : ℂ) * b
      set v := (π : ℂ) * (ζ + (t : ℂ))
      have hu1 : (π : ℂ) * (b - (ζ + (t : ℂ))) = u - v := by ring
      have hu2 : (π : ℂ) * (b + (ζ + (t : ℂ))) = u + v := by ring
      rw [hu1, hu2]
      have hsh_prod : Complex.sinh (u - v) * Complex.sinh (u + v) =
          (Cζ - Cb) * (Cζ + Cb) * (-1) := by
        change Complex.sinh (u - v) * Complex.sinh (u + v) =
          (Complex.cosh v - Complex.cosh u) * (Complex.cosh v + Complex.cosh u) * (-1)
        rw [Complex.sinh_sub, Complex.sinh_add]
        have hch_u : Complex.sinh u ^ 2 = Complex.cosh u ^ 2 - 1 := by
          linear_combination -Complex.cosh_sq_sub_sinh_sq u
        have hch_v : Complex.sinh v ^ 2 = Complex.cosh v ^ 2 - 1 := by
          linear_combination -Complex.cosh_sq_sub_sinh_sq v
        calc (Complex.sinh u * Complex.cosh v - Complex.cosh u * Complex.sinh v) *
              (Complex.sinh u * Complex.cosh v + Complex.cosh u * Complex.sinh v)
            = Complex.sinh u ^ 2 * Complex.cosh v ^ 2 - Complex.cosh u ^ 2 * Complex.sinh v ^ 2 := by ring
          _ = (Complex.cosh u ^ 2 - 1) * Complex.cosh v ^ 2 -
                Complex.cosh u ^ 2 * (Complex.cosh v ^ 2 - 1) := by rw [hch_u, hch_v]
          _ = (Complex.cosh v - Complex.cosh u) * (Complex.cosh v + Complex.cosh u) * (-1) := by ring
      have hsh1_ne : Complex.sinh (u - v) ≠ 0 := by
        intro h0; apply mul_ne_zero hcm hcd
        have := hsh_prod; rw [h0, zero_mul] at this
        have h1 : (Cζ - Cb) * (Cζ + Cb) * (-1) = 0 := this.symm
        linear_combination -h1
      have hsh2_ne : Complex.sinh (u + v) ≠ 0 := by
        intro h0; apply mul_ne_zero hcm hcd
        have := hsh_prod; rw [h0, mul_zero] at this
        have h1 : (Cζ - Cb) * (Cζ + Cb) * (-1) = 0 := this.symm
        linear_combination -h1
      have hsum : Complex.sinh (u + v) - Complex.sinh (u - v) = 2 * Complex.cosh u * Complex.sinh v := by
        rw [Complex.sinh_add, Complex.sinh_sub]; ring
      field_simp [hsh1_ne, hsh2_ne, hcm, hcd]
      have hsum' : -Complex.sinh (u + v) + Complex.sinh (u - v) = -(2 * Cb * Sζ) := by
        change -Complex.sinh (u + v) + Complex.sinh (u - v) = -(2 * Complex.cosh u * Complex.sinh v)
        linear_combination -hsum
      rw [hsum', hsh_prod]
      ring
    rw [hker]
    field_simp [hcd, hcm]
    ring
  have hQ_const : ∀ t : ℝ, 0 ≤ t → Q t = Q 0 := fun t ht => by
    have hQ_pos : ∀ s : ℝ, 0 < s → Q s = Q 1 := fun s hs => by
      refine isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        (fun x hx => (hQ_deriv x hx.le).differentiableAt.differentiableWithinAt)
        (fun x hx => (hQ_deriv x hx.le).deriv) hs (by norm_num)
    have hQ_zero : Q 0 = Q 1 := by
      have hlim0 : Tendsto Q (𝓝[>] 0) (𝓝 (Q 0)) :=
        (hQ_deriv 0 le_rfl).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have hlim1 : Tendsto Q (𝓝[>] 0) (𝓝 (Q 1)) :=
        tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs => (hQ_pos s hs).symm)
      exact tendsto_nhds_unique hlim0 hlim1
    rcases eq_or_lt_of_le ht with rfl | ht_pos
    · rfl
    · exact (hQ_pos t ht_pos).trans hQ_zero.symm
  have hQ_lim : Tendsto Q atTop (𝓝 1) := by
    have h_exp : Tendsto (fun t : ℝ => Complex.exp (phiZeta (ζ + (t : ℂ)) b)) atTop (𝓝 1) := by
      have h1 := Complex.continuous_exp.continuousAt.tendsto.comp (tendsto_phiZeta_atTop hb hζ)
      simpa only [Function.comp_def, Complex.exp_zero] using h1
    have h_negT : Tendsto (fun t : ℝ => -blaschkeT (ζ + (t : ℂ)) b) atTop (𝓝 1) := by
      have h_sub : ∀ᶠ (t : ℝ) in atTop,
          -blaschkeT (ζ + (t : ℂ)) b - 1 =
            -(2 * Complex.cosh ((π : ℂ) * b) /
              (Complex.cosh ((π : ℂ) * b) + Complex.cosh ((π : ℂ) * (ζ + (t : ℂ))))) := by
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        rw [show -blaschkeT (ζ + (t : ℂ)) b - 1 = -(blaschkeT (ζ + (t : ℂ)) b + 1) by ring,
          blaschkeT_add_one_eq (hden_ne t ht)]
      have h_to0 : Tendsto (fun t : ℝ =>
          -(2 * Complex.cosh ((π : ℂ) * b) /
            (Complex.cosh ((π : ℂ) * b) + Complex.cosh ((π : ℂ) * (ζ + (t : ℂ)))))) atTop (𝓝 0) := by
        refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
        have h_lim0 : Tendsto (fun t : ℝ =>
            2 * ‖Complex.cosh ((π : ℂ) * b)‖ / (Real.exp (π * (ζ.re + t)) / 4)) atTop (𝓝 0) := by
          have hexp_top : Tendsto (fun t : ℝ => Real.exp (π * (ζ.re + t)) / 4) atTop atTop :=
            (Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop hpi
              (Filter.tendsto_atTop.mpr fun M => Filter.eventually_atTop.mpr
                ⟨M - ζ.re, fun t ht => by linarith⟩))).atTop_div_const (by norm_num)
          exact tendsto_const_nhds.div_atTop hexp_top
        refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h_lim0
        filter_upwards [eventually_ge_atTop (|b.re| + 2 - ζ.re)] with t ht
        have h1 : Real.exp (π * (ζ.re + t)) / 2 - 1 ≤
            ‖Complex.cosh ((π : ℂ) * (ζ + (t : ℂ)))‖ := by
          have hre : |(ζ + (t : ℂ)).re| = ζ.re + t := by
            simp [abs_of_nonneg (by linarith [abs_nonneg b.re] : 0 ≤ ζ.re + t)]
          have h1' := norm_cosh_ge_half_exp_sub (ζ + (t : ℂ))
          rwa [hre] at h1'
        have h2 : ‖Complex.cosh ((π : ℂ) * b)‖ ≤ Real.exp (π * |b.re|) := norm_cosh_le_exp b
        have h4 : 8 * Real.exp (π * |b.re|) ≤ Real.exp (π * (ζ.re + t)) := by
          have hexp3 : 8 ≤ Real.exp (2 * π) := by
            have : 2 ≤ Real.exp 1 := by linarith [Real.add_one_lt_exp (one_ne_zero)]
            have hsq : 8 ≤ Real.exp 3 := by rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]; nlinarith
            exact hsq.trans (Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three]))
          calc 8 * Real.exp (π * |b.re|) ≤ Real.exp (2 * π) * Real.exp (π * |b.re|) := by gcongr
            _ = Real.exp (π * (|b.re| + 2)) := by rw [← Real.exp_add]; ring_nf
            _ ≤ Real.exp (π * (ζ.re + t)) := Real.exp_le_exp.mpr (by nlinarith)
        have hden_ge : Real.exp (π * (ζ.re + t)) / 4 ≤
            ‖Complex.cosh ((π : ℂ) * b) + Complex.cosh ((π : ℂ) * (ζ + (t : ℂ)))‖ := by
          have htri := norm_add_le (Complex.cosh ((π : ℂ) * b) + Complex.cosh ((π : ℂ) * (ζ + (t : ℂ))))
            (-Complex.cosh ((π : ℂ) * b))
          simp only [norm_neg, add_neg_cancel_comm] at htri
          have hb1 : 1 ≤ Real.exp (π * |b.re|) := Real.one_le_exp (by positivity)
          linarith
        rw [norm_neg, norm_div, norm_mul, Complex.norm_ofNat]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ge
      have h_sub_tend := h_to0.congr' (h_sub.mono fun t ht => ht.symm)
      simpa using h_sub_tend.add_const 1
    have hQ1 : Tendsto Q atTop (𝓝 (1 / 1)) := h_exp.div h_negT one_ne_zero
    rwa [div_one] at hQ1
  have hQ0 : Q 0 = 1 := by
    have hQ_lim0 : Tendsto (fun _ : ℝ => Q 0) atTop (𝓝 1) :=
      hQ_lim.congr' (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht; exact hQ_const t ht)
    exact tendsto_nhds_unique tendsto_const_nhds hQ_lim0
  dsimp [Q] at hQ0
  simp only [add_zero] at hQ0
  have hne0 : -blaschkeT ζ b ≠ 0 := by
    have := hnegT_eq 0 le_rfl
    simp only [Complex.ofReal_zero, add_zero] at this
    rw [this, div_ne_zero_iff]
    exact ⟨by simpa using hnum_ne 0 le_rfl, by rw [add_comm]; simpa using hden_ne 0 le_rfl⟩
  exact (div_eq_one_iff_eq hne0).mp hQ0

/-- Exact formula for mixed partial derivatives $\partial_b^i \partial_\zeta^j \varphi_\zeta(b)$
for $1 \le i + j$ on `combNOpen × combZOpen`. -/
lemma iteratedDeriv_phiZeta_eq (i j : ℕ) (hij : 1 ≤ i + j) :
    ∀ {ζ b : ℂ}, b ∈ combNOpen → ζ ∈ combZOpen →
      iteratedDeriv i (fun b' => iteratedDeriv j (fun ζ' => phiZeta ζ' b') ζ) b =
        (-1 : ℂ) ^ j * iteratedDeriv (i + j - 1) sinhKernel (b - ζ) +
          iteratedDeriv (i + j - 1) sinhKernel (b + ζ) := by
  have h_zeta : ∀ j : ℕ, 1 ≤ j → ∀ {ζ b : ℂ}, b ∈ combNOpen → ζ ∈ combZOpen →
      iteratedDeriv j (fun ζ' => phiZeta ζ' b) ζ =
        (-1 : ℂ) ^ j * iteratedDeriv (j - 1) sinhKernel (b - ζ) +
          iteratedDeriv (j - 1) sinhKernel (b + ζ) := by
    intro j hj
    induction j with
    | zero => omega
    | succ j ih =>
      intro ζ b hb hζ
      rcases eq_or_lt_of_le (Nat.zero_le j) with rfl | hj_pos
      · simp only [zero_add, pow_one, Nat.sub_self, iteratedDeriv_zero, iteratedDeriv_one]
        simpa using (hasDerivAt_phiZeta_zeta hb hζ).deriv
      · have h_ev : (fun ζ' => iteratedDeriv j (fun w => phiZeta w b) ζ') =ᶠ[𝓝 ζ]
            fun ζ' => (-1 : ℂ) ^ j * iteratedDeriv (j - 1) sinhKernel (b - ζ') +
              iteratedDeriv (j - 1) sinhKernel (b + ζ') := by
          filter_upwards [isOpen_combZOpen.mem_nhds hζ] with ζ' hζ'
          exact ih hj_pos hb hζ'
        rw [iteratedDeriv_succ]
        have him := sinhKernel_sub_im_mem hb hζ.2 0
        simp only [Complex.ofReal_zero, add_zero] at him
        have hopenS : IsOpen {w : ℂ | 0 < w.im ∧ w.im < 1} :=
          (isOpen_lt continuous_const Complex.continuous_im).inter
            (isOpen_lt Complex.continuous_im continuous_const)
        have han : AnalyticOnNhd ℂ sinhKernel {w : ℂ | 0 < w.im ∧ w.im < 1} :=
          sinhKernel_differentiableOn.analyticOnNhd hopenS
        have hdiff_k : DifferentiableOn ℂ (iteratedDeriv (j - 1) sinhKernel)
            {w : ℂ | 0 < w.im ∧ w.im < 1} := by
          rw [iteratedDeriv_eq_iterate]
          exact (han.iterated_deriv (j - 1)).differentiableOn
        have hd1 : HasDerivAt (iteratedDeriv (j - 1) sinhKernel)
            (iteratedDeriv j sinhKernel (b - ζ)) (b - ζ) := by
          rw [show j = (j - 1) + 1 by omega, iteratedDeriv_succ]
          exact (hdiff_k _ ⟨by linarith [him.1], by linarith [him.2.1]⟩).differentiableAt
            (hopenS.mem_nhds ⟨by linarith [him.1], by linarith [him.2.1]⟩) |>.hasDerivAt
        have hd2 : HasDerivAt (iteratedDeriv (j - 1) sinhKernel)
            (iteratedDeriv j sinhKernel (b + ζ)) (b + ζ) := by
          rw [show j = (j - 1) + 1 by omega, iteratedDeriv_succ]
          exact (hdiff_k _ ⟨by linarith [him.2.2.1], by linarith [him.2.2.2]⟩).differentiableAt
            (hopenS.mem_nhds ⟨by linarith [him.2.2.1], by linarith [him.2.2.2]⟩) |>.hasDerivAt
        have htot : HasDerivAt
            (fun ζ' => (-1 : ℂ) ^ j * iteratedDeriv (j - 1) sinhKernel (b - ζ') +
              iteratedDeriv (j - 1) sinhKernel (b + ζ'))
            ((-1 : ℂ) ^ (j + 1) * iteratedDeriv j sinhKernel (b - ζ) +
              iteratedDeriv j sinhKernel (b + ζ)) ζ := by
          have hl1 : HasDerivAt (fun ζ' => b - ζ') (-1) ζ := (hasDerivAt_id ζ).const_sub b
          have hl2 : HasDerivAt (fun ζ' => b + ζ') 1 ζ := (hasDerivAt_id ζ).const_add b
          have hd := ((hd1.comp ζ hl1).const_mul ((-1 : ℂ) ^ j)).add (hd2.comp ζ hl2)
          refine hd.congr_deriv ?_; rw [pow_succ]; ring
        rw [(htot.congr_of_eventuallyEq h_ev).deriv]
        simp
  induction i with
  | zero =>
    intro ζ b hb hζ
    simpa using h_zeta j (by omega) hb hζ
  | succ i ih =>
    intro ζ b hb hζ
    rcases eq_or_lt_of_le (Nat.zero_le (i + j)) with hij0 | hij_pos
    · have hi0 : i = 0 := by omega
      have hj0 : j = 0 := by omega
      subst hi0; subst hj0
      simp only [zero_add, iteratedDeriv_zero, pow_zero, one_mul, iteratedDeriv_one, Nat.sub_self]
      exact (hasDerivAt_phiZeta_b hb hζ).deriv
    · have h_ev : (fun b' => iteratedDeriv i (fun z => iteratedDeriv j (fun ζ' => phiZeta ζ' z) ζ) b') =ᶠ[𝓝 b]
          fun b' => (-1 : ℂ) ^ j * iteratedDeriv (i + j - 1) sinhKernel (b' - ζ) +
            iteratedDeriv (i + j - 1) sinhKernel (b' + ζ) := by
        filter_upwards [isOpen_combNOpen.mem_nhds hb] with b' hb'
        exact ih hij_pos hb' hζ
      rw [iteratedDeriv_succ]
      have him := sinhKernel_sub_im_mem hb hζ.2 0
      simp only [Complex.ofReal_zero, add_zero] at him
      have hopenS : IsOpen {w : ℂ | 0 < w.im ∧ w.im < 1} :=
        (isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)
      have han : AnalyticOnNhd ℂ sinhKernel {w : ℂ | 0 < w.im ∧ w.im < 1} :=
        sinhKernel_differentiableOn.analyticOnNhd hopenS
      have hdiff_k : DifferentiableOn ℂ (iteratedDeriv (i + j - 1) sinhKernel)
          {w : ℂ | 0 < w.im ∧ w.im < 1} := by
        rw [iteratedDeriv_eq_iterate]
        exact (han.iterated_deriv (i + j - 1)).differentiableOn
      have hd1 : HasDerivAt (iteratedDeriv (i + j - 1) sinhKernel)
          (iteratedDeriv (i + j) sinhKernel (b - ζ)) (b - ζ) := by
        rw [show i + j = (i + j - 1) + 1 by omega, iteratedDeriv_succ]
        exact (hdiff_k _ ⟨by linarith [him.1], by linarith [him.2.1]⟩).differentiableAt
          (hopenS.mem_nhds ⟨by linarith [him.1], by linarith [him.2.1]⟩) |>.hasDerivAt
      have hd2 : HasDerivAt (iteratedDeriv (i + j - 1) sinhKernel)
          (iteratedDeriv (i + j) sinhKernel (b + ζ)) (b + ζ) := by
        rw [show i + j = (i + j - 1) + 1 by omega, iteratedDeriv_succ]
        exact (hdiff_k _ ⟨by linarith [him.2.2.1], by linarith [him.2.2.2]⟩).differentiableAt
          (hopenS.mem_nhds ⟨by linarith [him.2.2.1], by linarith [him.2.2.2]⟩) |>.hasDerivAt
      have htot : HasDerivAt
          (fun b' => (-1 : ℂ) ^ j * iteratedDeriv (i + j - 1) sinhKernel (b' - ζ) +
            iteratedDeriv (i + j - 1) sinhKernel (b' + ζ))
          ((-1 : ℂ) ^ j * iteratedDeriv (i + j) sinhKernel (b - ζ) +
            iteratedDeriv (i + j) sinhKernel (b + ζ)) b := by
        have hl1 : HasDerivAt (fun b' => b' - ζ) 1 b := (hasDerivAt_id b).sub_const ζ
        have hl2 : HasDerivAt (fun b' => b' + ζ) 1 b := (hasDerivAt_id b).add_const ζ
        have hd := ((hd1.comp b hl1).const_mul ((-1 : ℂ) ^ j)).add (hd2.comp b hl2)
        refine hd.congr_deriv ?_; ring
      rw [(htot.congr_of_eventuallyEq h_ev).deriv]
      simp [Nat.add_assoc, Nat.add_comm 1 j]

/-- **K1(d), derivative bounds**: for all $1 \le i + j \le 4$,
$|\partial_b^i \partial_\zeta^j \varphi_\zeta(b)| \le C e^{-\pi |\operatorname{Re}\zeta - |\operatorname{Re} b||}$
on $\mathcal N \times \{\operatorname{Re}\zeta \ge 0,\ |\operatorname{Im}\zeta| \le 1/8\}$. -/
theorem iteratedDeriv_phiZeta_le :
    ∃ C > 0, ∀ (i j : ℕ), 1 ≤ i + j → i + j ≤ 4 → ∀ {ζ b : ℂ}, b ∈ combN → ζ ∈ combZ →
      ‖iteratedDeriv i (fun b' => iteratedDeriv j (fun ζ' => phiZeta ζ' b') ζ) b‖ ≤
        C * Real.exp (-π * abs (ζ.re - |b.re|)) := by
  obtain ⟨C₀, hC₀, hbd0⟩ := sinhKernel_iteratedDeriv_bound (k := 0) (s₀ := 1 / 16)
    (by norm_num) (by norm_num)
  obtain ⟨C₁, hC₁, hbd1⟩ := sinhKernel_iteratedDeriv_bound (k := 1) (s₀ := 1 / 16)
    (by norm_num) (by norm_num)
  obtain ⟨C₂, hC₂, hbd2⟩ := sinhKernel_iteratedDeriv_bound (k := 2) (s₀ := 1 / 16)
    (by norm_num) (by norm_num)
  obtain ⟨C₃, hC₃, hbd3⟩ := sinhKernel_iteratedDeriv_bound (k := 3) (s₀ := 1 / 16)
    (by norm_num) (by norm_num)
  set M := max (max C₀ C₁) (max C₂ C₃)
  refine ⟨2 * M, by positivity, fun i j hij1 hij4 {ζ b} hb hζ => ?_⟩
  rw [iteratedDeriv_phiZeta_eq i j hij1 (combN_subset_combNOpen hb) (combZ_subset_combZOpen hζ)]
  have him := sinhKernel_sub_im_mem (combN_subset_combNOpen hb) (combZ_subset_combZOpen hζ).2 0
  simp only [Complex.ofReal_zero, add_zero] at him
  have him_18 : 1 / 8 ≤ (b - ζ).im ∧ (b - ζ).im ≤ 7 / 8 ∧ 1 / 8 ≤ (b + ζ).im ∧ (b + ζ).im ≤ 7 / 8 := by
    have hb' := abs_le.mp (show |b.im - 1 / 2| ≤ 1 / 4 from hb)
    have hζ' := abs_le.mp hζ.2
    simp only [Complex.sub_im, Complex.add_im]
    norm_num at *
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hbd_k : ∀ k : ℕ, k ≤ 3 → ∀ w : ℂ, 1 / 8 ≤ w.im → w.im ≤ 7 / 8 →
      ‖iteratedDeriv k sinhKernel w‖ ≤ M * Real.exp (-π * |w.re|) := by
    intro k hk w hw1 hw2
    have hw1' : 2 * (1 / 16 : ℝ) ≤ w.im := by linarith
    have hw2' : w.im ≤ 1 - 2 * (1 / 16 : ℝ) := by linarith
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · exact (hbd0 w hw1' hw2').trans (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_left _ _)) (Real.exp_pos _).le)
    · exact (hbd1 w hw1' hw2').trans (mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_max_left _ _)) (Real.exp_pos _).le)
    · exact (hbd2 w hw1' hw2').trans (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_right _ _)) (Real.exp_pos _).le)
    · exact (hbd3 w hw1' hw2').trans (mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_max_right _ _)) (Real.exp_pos _).le)
  have hk_le : i + j - 1 ≤ 3 := by omega
  have h1 := hbd_k (i + j - 1) hk_le (b - ζ) him_18.1 him_18.2.1
  have h2 := hbd_k (i + j - 1) hk_le (b + ζ) him_18.2.2.1 him_18.2.2.2
  have hre_dist1 : abs (ζ.re - |b.re|) ≤ |(b - ζ).re| := by
    simp only [Complex.sub_re]
    rcases le_or_gt 0 b.re with h | h
    · rw [abs_of_nonneg h, abs_sub_comm]
    · rw [abs_of_neg h]
      have h1' : |ζ.re + b.re| ≤ |b.re - ζ.re| := by
        have hζ0 : 0 ≤ ζ.re := hζ.1
        rw [abs_sub_comm]
        have : |ζ.re + b.re| ≤ ζ.re - b.re := by
          rw [abs_le]; constructor <;> linarith
        exact this.trans (le_abs_self _)
      simpa [sub_neg_eq_add] using h1'
  have hre_dist2 : abs (ζ.re - |b.re|) ≤ |(b + ζ).re| := by
    simp only [Complex.add_re]
    rcases le_or_gt 0 b.re with h | h
    · rw [abs_of_nonneg h]
      have hζ0 : 0 ≤ ζ.re := hζ.1
      have : |ζ.re - b.re| ≤ b.re + ζ.re := by rw [abs_le]; constructor <;> linarith
      exact this.trans (le_abs_self _)
    · rw [abs_of_neg h, sub_neg_eq_add, add_comm]
  have he1 : Real.exp (-π * |(b - ζ).re|) ≤ Real.exp (-π * abs (ζ.re - |b.re|)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have he2 : Real.exp (-π * |(b + ζ).re|) ≤ Real.exp (-π * abs (ζ.re - |b.re|)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  calc ‖(-1 : ℂ) ^ j * iteratedDeriv (i + j - 1) sinhKernel (b - ζ) +
          iteratedDeriv (i + j - 1) sinhKernel (b + ζ)‖
      ≤ ‖(-1 : ℂ) ^ j * iteratedDeriv (i + j - 1) sinhKernel (b - ζ)‖ +
          ‖iteratedDeriv (i + j - 1) sinhKernel (b + ζ)‖ := norm_add_le _ _
    _ = ‖iteratedDeriv (i + j - 1) sinhKernel (b - ζ)‖ +
          ‖iteratedDeriv (i + j - 1) sinhKernel (b + ζ)‖ := by
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    _ ≤ M * Real.exp (-π * |(b - ζ).re|) + M * Real.exp (-π * |(b + ζ).re|) := add_le_add h1 h2
    _ ≤ M * Real.exp (-π * abs (ζ.re - |b.re|)) + M * Real.exp (-π * abs (ζ.re - |b.re|)) := by gcongr
    _ = 2 * M * Real.exp (-π * abs (ζ.re - |b.re|)) := by ring

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.norm_blaschkeT_real_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.norm_blaschkeT_real_le_one

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.norm_pair_blaschkeT_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.norm_pair_blaschkeT_le_one

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.comb_pairProd_hasProdLocallyUniformlyOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.comb_pairProd_hasProdLocallyUniformlyOn

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.blaschkePairQ_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.blaschkePairQ_eq

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.deltaDetune_bounds_universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.deltaDetune_bounds_universal

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.deltaDetune_le_of_xiStar_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.deltaDetune_le_of_xiStar_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.deltaDetune_le_of_dist_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.deltaDetune_le_of_dist_ge

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.realLogT_deriv_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.realLogT_deriv_bounds

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.cexp_phiZeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.cexp_phiZeta

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.norm_phiZeta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.norm_phiZeta_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Comb.iteratedDeriv_phiZeta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Comb.iteratedDeriv_phiZeta_le

end FormalResearch.ModularBootstrap.Upper.Comb
