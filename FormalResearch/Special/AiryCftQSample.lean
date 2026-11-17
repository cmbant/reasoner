module

public import FormalResearch.Special.AiryCftQQuad
public import FormalResearch.Special.AiryCftQSampleZeros
public import FormalResearch.Complex.HardyWeightedArc

/-!
# Theorem Q (3): the sampling bound `Σ_n |f(a_n)|/Ai'(a_n)² ≤ C ‖f‖_b`

Statement formalised (CFT `AIRY_POISSON.md` Theorem Q (3), sampling inequality R34 (PP)): there is an absolute constant `C` such that
for every entire `f` with `‖f(u)‖ ≤ C₀ (1+|u|)^ν e(u)` (**any real `ν`**, complex-valued `f`) and `f ∈ L¹(ℝ)`,

`Σ_{n ≥ 1} ‖f(a_n)‖ / ‖Ai'(a_n)‖² ≤ C ∫_{x<0} ‖f‖`    (`airyQ_sampling`; in particular the series converges absolutely).

Proof (a variant of the note's: the Poisson representation of Lemma H is **not** used).  With `G = airyQG f`
(`z f(-z²) e^{(4/3) i z³}`, entire, polynomially bounded on `Im z ≥ 0`, `G|_ℝ ∈ L¹`, `∫_ℝ ‖G‖ = ‖f‖_b`):

1. (reflection, `airyQG_refl`) `‖G(w)‖ = ‖G(-w)‖ exp(-(8/3) Im w³) ≤ ‖G(-w)‖ exp(8 (Re w)² |Im w|)` for `Im w ≤ 0` — this uses `w ↦ -w` rather
   than the note's `w ↦ w̄`, so `f` need not be real;
2. (sub-mean-value at the real zero `c_n = √(-a_{n+1})` on the circle of radius `r_n = 1/(4c_n²)`, `hardy_sample_real`) the circle average
   splits into the upper semicircles about `±c_n`, each controlled by the weighted Fejér–Riesz arc bound `hardy_arc_weighted`
   (Fejér–Riesz applied to `G(x₀ + z)(r/(z+ir))²`):
   `‖G(c_n)‖ ≤ (r_n/π)(∫ ‖G(t)‖/((t-c_n)²+r_n²) + e⁴ ∫ ‖G(t)‖/((t+c_n)²+r_n²))`;
3. (weights) `1/‖Ai'(a_n)‖² ≤ 36π²/c_n` (`airyZero_inv_deriv_sq_le`) and `‖f(a_n)‖ = ‖G(c_n)‖/c_n`, `1/c_n² = 4 r_n`;
4. (Carleson-type kernel sum) `Σ_n r_n²/((t∓c_n)²+r_n²) ≤ K` uniformly in `t`, from the separation `|c_n - c_m| max(c_n,c_m)² ≥ |n-m|`
   of the zeros (`airyRoot_kernel_sum`, `AiryCftQSampleZeros`), so `Σ_{n<N} ‖f(a_{n+1})/Ai'(a_{n+1})²‖ ≤ 144 π (1+e⁴) K ‖G‖_{L¹}`.

All **proved** (`airyQ_sampling`, `airyQ_sampling_sum`).  The constant is absolute (`C = 144π(1+e⁴)K + 1` where `K` is the kernel-sum bound of
`separated_kernel_sum` with `s = 1`, `κ = 12`, in the form of `airyQ_sampling_sum`; not optimised).

Numerical sanity check of the statement (scipy double precision, terms cross-checked with mpmath at 30 digits for `n = 1, 2, 3, 10`; evidence only,
not used in any proof): for the test function `f(u) = ∫_0^1 τ⁴(1-τ)⁴ Ai(2^{2/3}(u+τ)) dτ` (`f ∈ L¹(ℝ)`, entire, in the class of Theorem Q),
`Σ_{n ≤ 3000} |f(a_n)|/Ai'(a_n)² = 4.97·10⁻³` and `∫_{-1500}^0 |f| = 5.96·10⁻³` (ratio `0.83`, far below the proved constant), while
`Σ_{n ≤ 3000} f(a_n)/Ai'(a_n)² = 1.0026·10⁻³` against `∫_ℝ f = 2^{-2/3} B(5,5) = 0.99994·10⁻³`.

The notes' proof uses the Poisson representation of Lemma H (`|G(ξ+iη)| ≤ ∫ P_η(ξ-t)|g(t)| dt`) and a Carleson-measure sum; here the
Fejér–Riesz arc bound alone (with a Cauchy weight) replaces it, so no Poisson integral is formalised.  The pointwise bounds of Theorem Q (2) that
this proof yields are in `AiryCftQSamplePt` (`airyQ_pointwise_real`, `airyQ_f_point`); the sharp form `‖G(z)‖ ≤ ‖g‖₁/(π Im z)` for non-real `z`
(Lemma H) is **not formalised**.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real

namespace FormalResearch.Special

lemma im_pow_three (w : ℂ) : (w ^ 3).im = 3 * w.re ^ 2 * w.im - w.im ^ 3 := by
  simp [pow_succ, Complex.mul_re, Complex.mul_im]
  ring

/-- **Reflection `w ↦ -w`**: for `Im w ≤ 0`, `‖G(w)‖ ≤ ‖G(-w)‖ exp(8 (Re w)² |Im w|)`. -/
lemma airyQG_refl (f : ℂ → ℂ) {w : ℂ} (hw : w.im ≤ 0) :
    ‖airyQG f w‖ ≤ ‖airyQG f (-w)‖ * Real.exp (8 * w.re ^ 2 * |w.im|) := by
  have hA : ‖cexp ((4 / 3 : ℂ) * I * w ^ 3)‖ = Real.exp (-(4 / 3) * (w ^ 3).im) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, Complex.mul_im]
  have hB : ‖cexp ((4 / 3 : ℂ) * I * (-w) ^ 3)‖ = Real.exp ((4 / 3) * (w ^ 3).im) := by
    rw [Complex.norm_exp]; congr 1
    have : (-w) ^ 3 = -(w ^ 3) := by ring
    rw [this]; simp [Complex.mul_re, Complex.mul_im]
  have h1 : ‖airyQG f w‖ = ‖w‖ * ‖f (-(w ^ 2))‖ * Real.exp (-(4 / 3) * (w ^ 3).im) := by
    unfold airyQG; rw [norm_mul, norm_mul, hA]
  have h2 : ‖airyQG f (-w)‖ = ‖w‖ * ‖f (-(w ^ 2))‖ * Real.exp ((4 / 3) * (w ^ 3).im) := by
    unfold airyQG; rw [norm_mul, norm_mul, hB, norm_neg]
    have : (-w) ^ 2 = w ^ 2 := by ring
    rw [this]
  have hX : 0 ≤ ‖w‖ * ‖f (-(w ^ 2))‖ := by positivity
  have hE : Real.exp (-(4 / 3) * (w ^ 3).im) ≤ Real.exp ((4 / 3) * (w ^ 3).im) * Real.exp (8 * w.re ^ 2 * |w.im|) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    rw [im_pow_three, abs_of_nonpos hw]
    nlinarith [sq_nonneg w.re, mul_nonneg (sq_nonneg w.re) (neg_nonneg.mpr hw),
      mul_nonneg (neg_nonneg.mpr hw) (sq_nonneg w.im)]
  rw [h1, h2]
  calc ‖w‖ * ‖f (-(w ^ 2))‖ * Real.exp (-(4 / 3) * (w ^ 3).im)
      ≤ ‖w‖ * ‖f (-(w ^ 2))‖ * (Real.exp ((4 / 3) * (w ^ 3).im) * Real.exp (8 * w.re ^ 2 * |w.im|)) :=
        mul_le_mul_of_nonneg_left hE hX
    _ = _ := by ring

lemma airy_radius_facts {c : ℝ} (hc : 1 ≤ c) :
    (1 / (4 * c ^ 2)) * c ^ 2 = 1 / 4 ∧ 1 / (4 * c ^ 2) ≤ 1 / 4 ∧ c * (1 / (4 * c ^ 2)) ≤ 1 / 4 := by
  have hc0 : 0 < c := by linarith
  refine ⟨by field_simp, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  · rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith

/-- On the circle `|w - c| = r`, `r = 1/(4c²)`, `c ≥ 1`: `8 (Re w)² |Im w| ≤ 4`. -/
lemma airy_circle_exp_le {c : ℝ} (hc : 1 ≤ c) {w : ℂ} (hw : ‖w - (c : ℂ)‖ = 1 / (4 * c ^ 2)) :
    8 * w.re ^ 2 * |w.im| ≤ 4 := by
  obtain ⟨h1, h2, h3⟩ := airy_radius_facts hc
  set r := 1 / (4 * c ^ 2) with hr
  have hr0 : 0 < r := by positivity
  have him : |w.im| ≤ r := by
    have := Complex.abs_im_le_norm (w - (c : ℂ))
    simpa [hw] using this
  have hre : |w.re - c| ≤ r := by
    have := Complex.abs_re_le_norm (w - (c : ℂ))
    simpa [hw] using this
  have hre2 : |w.re| ≤ c + r := by
    have := abs_le.mp hre
    rw [abs_le]; constructor <;> linarith
  have hsq : w.re ^ 2 ≤ (c + r) ^ 2 := by
    have := sq_le_sq' (by linarith [abs_nonneg w.re, (abs_le.mp hre2).1] : -(c + r) ≤ w.re) (abs_le.mp hre2).2
    exact this
  have : (c + r) ^ 2 * r ≤ 1 / 2 := by
    have e : (c + r) ^ 2 * r = r * c ^ 2 + 2 * (c * r) * r + r ^ 3 := by ring
    rw [e, h1]
    nlinarith [mul_nonneg hr0.le hr0.le, mul_le_mul h3 h2 hr0.le (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  calc 8 * w.re ^ 2 * |w.im| ≤ 8 * (c + r) ^ 2 * r := by
        have := mul_le_mul hsq him (abs_nonneg _) (by positivity)
        linarith
    _ ≤ 4 := by nlinarith

/-- **Sub-mean-value bound for `G = airyQG f` at the real zero root `c ≥ 1`**, radius `r = 1/(4c²)`. -/
lemma airyQ_sample_pt {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) {c : ℝ} (hc : 1 ≤ c) :
    ‖airyQG f (c : ℂ)‖ ≤ ((1 / (4 * c ^ 2)) / π) *
      ((∫ t : ℝ, ‖airyQG f (t : ℂ)‖ / ((t - c) ^ 2 + (1 / (4 * c ^ 2)) ^ 2)) +
        Real.exp 4 * ∫ t : ℝ, ‖airyQG f (t : ℂ)‖ / ((t + c) ^ 2 + (1 / (4 * c ^ 2)) ^ 2)) := by
  obtain ⟨h1, h2, h3⟩ := airyQ_hardy_hyp hf hfi hC hb
  have hc0 : 0 < c := by linarith
  refine FormalResearch.Hardy.hardy_sample_real (airyQ_differentiable_G hf) h2 h3 c (by positivity)
    (Real.exp_pos 4).le (fun w hw hwi => ?_)
  refine (airyQG_refl f hwi).trans ?_
  rw [mul_comm (Real.exp 4)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (airy_circle_exp_le hc hw)) (norm_nonneg _)

/-- `(1 + c²)^{-1/2} ≤ 1/c` for `c > 0`. -/
lemma one_add_sq_rpow_le {c : ℝ} (hc : 0 < c) : (1 + c ^ 2) ^ (-(1 / 2) : ℝ) ≤ 1 / c := by
  have h1 : (c ^ 2) ^ (-(1 / 2) : ℝ) = 1 / c := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq hc.le, one_div]
  rw [← h1]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)

/-- **Single-zero bound.**  For `c = √(-a_{n+1})`, `r = 1/(4c²)`:
`‖f(a_{n+1})/Ai'(a_{n+1})²‖ ≤ 144π (∫ ‖G‖ r²/((t-c)²+r²) + e⁴ ∫ ‖G‖ r²/((t+c)²+r²))`. -/
lemma airyQ_term_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) (n : ℕ) :
    ‖f (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2‖ ≤
      144 * π * ((∫ t : ℝ, ‖airyQG f (t : ℂ)‖ * ((1 / (4 * airyZeroRoot (n + 1) ^ 2)) ^ 2 /
          ((t - airyZeroRoot (n + 1)) ^ 2 + (1 / (4 * airyZeroRoot (n + 1) ^ 2)) ^ 2))) +
        Real.exp 4 * ∫ t : ℝ, ‖airyQG f (t : ℂ)‖ * ((1 / (4 * airyZeroRoot (n + 1) ^ 2)) ^ 2 /
          ((t + airyZeroRoot (n + 1)) ^ 2 + (1 / (4 * airyZeroRoot (n + 1) ^ 2)) ^ 2))) := by
  set c := airyZeroRoot (n + 1) with hcdef
  have hc1 : 1 ≤ c := airyRoot_one_le n
  have hc0 : 0 < c := by linarith
  set r : ℝ := 1 / (4 * c ^ 2) with hr
  have hr0 : 0 < r := by positivity
  have hpt := airyQ_sample_pt hf hfi hC hb hc1
  rw [← hr] at hpt
  have ha : (airyZero (n + 1) : ℂ) = ((-(c ^ 2) : ℝ) : ℂ) := by
    rw [hcdef, airyZero_eq_neg_root_sq]
  -- ‖f a‖ = ‖G c‖ / c
  have hfa : ‖f (airyZero (n + 1) : ℂ)‖ = ‖airyQG f (c : ℂ)‖ / c := by
    rw [airyQ_norm_G_real, abs_of_pos hc0, ha]
    field_simp
  have hw := airyZero_inv_deriv_sq_le (n + 1)
  have hw' : ‖((deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2)⁻¹‖ ≤ 36 * π ^ 2 / c := by
    refine hw.trans ?_
    have e : (1 + -airyZero (n + 1)) = 1 + c ^ 2 := by rw [hcdef, airyZero_eq_neg_root_sq]; ring
    rw [e]
    have := one_add_sq_rpow_le hc0
    calc 36 * π ^ 2 * (1 + c ^ 2) ^ (-(1 / 2) : ℝ) ≤ 36 * π ^ 2 * (1 / c) := by gcongr
      _ = _ := by ring
  rw [div_eq_mul_inv, norm_mul]
  have hG0 : 0 ≤ ‖airyQG f (c : ℂ)‖ := norm_nonneg _
  have hstep : ‖f (airyZero (n + 1) : ℂ)‖ * ‖((deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2)⁻¹‖ ≤
      (‖airyQG f (c : ℂ)‖ / c) * (36 * π ^ 2 / c) := by
    rw [hfa]
    exact mul_le_mul_of_nonneg_left hw' (by positivity)
  refine hstep.trans ?_
  set J1 := ∫ t : ℝ, ‖airyQG f (t : ℂ)‖ / ((t - c) ^ 2 + r ^ 2)
  set J2 := ∫ t : ℝ, ‖airyQG f (t : ℂ)‖ / ((t + c) ^ 2 + r ^ 2)
  have e1 : (∫ t : ℝ, ‖airyQG f (t : ℂ)‖ * (r ^ 2 / ((t - c) ^ 2 + r ^ 2))) = r ^ 2 * J1 :=
    FormalResearch.Hardy.integral_weight_eq (fun t => ‖airyQG f (t : ℂ)‖) c r
  have e2 : (∫ t : ℝ, ‖airyQG f (t : ℂ)‖ * (r ^ 2 / ((t + c) ^ 2 + r ^ 2))) = r ^ 2 * J2 := by
    have := FormalResearch.Hardy.integral_weight_eq (fun t => ‖airyQG f (t : ℂ)‖) (-c) r
    simpa [sub_neg_eq_add] using this
  rw [e1, e2]
  have hinv : 1 / c ^ 2 = 4 * r := by rw [hr]; field_simp
  have : (‖airyQG f (c : ℂ)‖ / c) * (36 * π ^ 2 / c) = 36 * π ^ 2 * (1 / c ^ 2) * ‖airyQG f (c : ℂ)‖ := by
    field_simp
  rw [this, hinv]
  have hpi := Real.pi_pos
  have h36 : 0 ≤ 36 * π ^ 2 * (4 * r) := by positivity
  calc 36 * π ^ 2 * (4 * r) * ‖airyQG f (c : ℂ)‖ ≤ 36 * π ^ 2 * (4 * r) * ((r / π) * (J1 + Real.exp 4 * J2)) :=
        mul_le_mul_of_nonneg_left hpt h36
    _ = _ := by field_simp; ring

lemma integrable_mul_kern {g : ℝ → ℝ} (hg : Integrable g) (c r : ℝ) (hr : 0 < r) :
    Integrable (fun t : ℝ => g t * (r ^ 2 / ((t - c) ^ 2 + r ^ 2))) := by
  refine hg.mul_bdd (c := 1) ?_ (Eventually.of_forall fun t => ?_)
  · have hc : Continuous fun t : ℝ => r ^ 2 / ((t - c) ^ 2 + r ^ 2) :=
      Continuous.div continuous_const (by fun_prop) (fun t => by positivity)
    exact hc.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact FormalResearch.Hardy.kernel_term_le_one hr

/-- **Theorem Q (3), partial sums.** `Σ_{n<N} ‖f(a_{n+1})/Ai'(a_{n+1})²‖ ≤ C ∫_{x<0} ‖f‖` with `C` absolute. -/
theorem airyQ_sampling_sum : ∃ C : ℝ, 0 < C ∧ ∀ {f : ℂ → ℂ} (_ : Differentiable ℂ f)
    (_ : Integrable (fun x : ℝ => f (x : ℂ))) {C₀ ν : ℝ} (_ : 0 ≤ C₀)
    (_ : ∀ u : ℂ, ‖f u‖ ≤ C₀ * (1 + ‖u‖) ^ ν * airyEnv u) (N : ℕ),
    ∑ n ∈ Finset.range N, ‖f (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2‖ ≤
      C * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := by
  obtain ⟨K, hK⟩ := airyRoot_kernel_sum
  have hK0 : 0 ≤ K := by simpa using hK 0 0
  have hpi := Real.pi_pos
  refine ⟨144 * π * (1 + Real.exp 4) * K + 1, by positivity, fun {f} hf hfi {C₀ ν} hC hb N => ?_⟩
  set g : ℝ → ℝ := fun t => ‖airyQG f (t : ℂ)‖ with hg
  have hgi : Integrable g := (airyQ_boundary hf hfi).1.norm
  have hgint : ∫ t : ℝ, g t = ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := (airyQ_boundary hf hfi).2
  have hg0 : ∀ t, 0 ≤ g t := fun t => norm_nonneg _
  set c : ℕ → ℝ := fun n => airyZeroRoot (n + 1) with hc
  set r : ℕ → ℝ := fun n => 1 / (4 * c n ^ 2) with hr
  have hr0 : ∀ n, 0 < r n := fun n => by
    have := airyZeroRoot_pos (n + 1); simp only [hr, hc]; positivity
  have hk1 : ∀ n, Integrable (fun t : ℝ => g t * (r n ^ 2 / ((t - c n) ^ 2 + r n ^ 2))) := fun n =>
    integrable_mul_kern hgi (c n) (r n) (hr0 n)
  have hk2 : ∀ n, Integrable (fun t : ℝ => g t * (r n ^ 2 / ((t + c n) ^ 2 + r n ^ 2))) := fun n => by
    have := integrable_mul_kern hgi (-c n) (r n) (hr0 n)
    simpa [sub_neg_eq_add] using this
  have hS1 : ∑ n ∈ Finset.range N, ∫ t : ℝ, g t * (r n ^ 2 / ((t - c n) ^ 2 + r n ^ 2)) ≤ K * (∫ t, g t) := by
    rw [← integral_finsetSum _ (fun n _ => hk1 n), ← integral_const_mul]
    refine integral_mono (integrable_finsetSum _ fun n _ => hk1 n) (hgi.const_mul K) (fun t => ?_)
    rw [← Finset.mul_sum]
    have := hK t N
    simp only [hr, hc] at this ⊢
    nlinarith [hg0 t]
  have hS2 : ∑ n ∈ Finset.range N, ∫ t : ℝ, g t * (r n ^ 2 / ((t + c n) ^ 2 + r n ^ 2)) ≤ K * (∫ t, g t) := by
    rw [← integral_finsetSum _ (fun n _ => hk2 n), ← integral_const_mul]
    refine integral_mono (integrable_finsetSum _ fun n _ => hk2 n) (hgi.const_mul K) (fun t => ?_)
    rw [← Finset.mul_sum]
    have := hK (-t) N
    have e : ∀ n, (t + c n) ^ 2 = (-t - c n) ^ 2 := fun n => by ring
    simp only [e]
    simp only [hr, hc] at this ⊢
    nlinarith [hg0 t]
  calc ∑ n ∈ Finset.range N, ‖f (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2‖
      ≤ ∑ n ∈ Finset.range N, 144 * π * ((∫ t : ℝ, g t * (r n ^ 2 / ((t - c n) ^ 2 + r n ^ 2))) +
          Real.exp 4 * ∫ t : ℝ, g t * (r n ^ 2 / ((t + c n) ^ 2 + r n ^ 2))) :=
        Finset.sum_le_sum fun n _ => airyQ_term_le hf hfi hC hb n
    _ = 144 * π * ((∑ n ∈ Finset.range N, ∫ t : ℝ, g t * (r n ^ 2 / ((t - c n) ^ 2 + r n ^ 2))) +
          Real.exp 4 * ∑ n ∈ Finset.range N, ∫ t : ℝ, g t * (r n ^ 2 / ((t + c n) ^ 2 + r n ^ 2))) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 144 * π * (K * (∫ t, g t) + Real.exp 4 * (K * (∫ t, g t))) := by
        exact mul_le_mul_of_nonneg_left (add_le_add hS1 (mul_le_mul_of_nonneg_left hS2 (Real.exp_pos 4).le))
          (by positivity)
    _ = 144 * π * (1 + Real.exp 4) * K * (∫ t, g t) := by ring
    _ ≤ _ := by
        rw [hgint]
        have : 0 ≤ ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := integral_nonneg fun x => norm_nonneg _
        nlinarith

/-- **Theorem Q (3), the sampling bound**: the series `Σ_n f(a_n)/Ai'(a_n)²` converges absolutely and
`Σ_n ‖f(a_n)/Ai'(a_n)²‖ ≤ C ∫_{x<0} ‖f‖`, `C` absolute. -/
theorem airyQ_sampling : ∃ C : ℝ, 0 < C ∧ ∀ {f : ℂ → ℂ} (_ : Differentiable ℂ f)
    (_ : Integrable (fun x : ℝ => f (x : ℂ))) {C₀ ν : ℝ} (_ : 0 ≤ C₀)
    (_ : ∀ u : ℂ, ‖f u‖ ≤ C₀ * (1 + ‖u‖) ^ ν * airyEnv u),
    Summable (fun n : ℕ => ‖f (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2‖) ∧
    ∑' n : ℕ, ‖f (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2‖ ≤
      C * ∫ x in Iic (0 : ℝ), ‖f (x : ℂ)‖ := by
  obtain ⟨C, hC, h⟩ := airyQ_sampling_sum
  refine ⟨C, hC, fun {f} hf hfi {C₀ ν} hC₀ hb => ⟨?_, ?_⟩⟩
  · exact summable_of_sum_range_le (fun n => norm_nonneg _) (fun N => h hf hfi hC₀ hb N)
  · exact Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) (fun N => h hf hfi hC₀ hb N)

/-- info: 'FormalResearch.Special.airyQ_sampling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyQ_sampling

end FormalResearch.Special
