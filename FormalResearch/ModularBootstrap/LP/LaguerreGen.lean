module

public import FormalResearch.ModularBootstrap.LP.Laguerre
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The Laguerre generating function and the Cauchy bound for `ψ_k`

For a real weight `w > 0`, real `x` and complex `|z| < 1`:

`∑_k L_k^{(w-1)}(x) z^k = (1 - z)^{-w} exp(-x z / (1 - z))`   (`hasSum_lagL_gen`),

proved from the complex binomial series `(1-z)^{-a} = ∑ C(a+m-1, m) z^m` (Mathlib) and the exponential
series by an absolutely convergent double series over `ℕ × ℕ`.  This is the generating function used in
the proof of Lemma LP-C (`ds:cay`, `dual_spectrum_limit.tex`, line 7).

The bound of that proof, `|ψ_k(t)| ≤ (1-θ)^{-w} θ^{-k} e^{-2π s_θ t}` with
`ψ_k(t) = e^{-2πt} L_k^{(w-1)}(4π t)`, `s_θ = (1-θ)/(1+θ)`, is the Cauchy estimate on `|z| = θ`
(`abs_lagL_le`, `abs_lagPsi_le`), via `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`.
-/

@[expose] public section

open Complex Finset Filter Topology
open scoped Nat

namespace FormalResearch.ModularBootstrap.LP

/-! ### The binomial coefficient as a Pochhammer ratio -/

private lemma poch_cast_eq (a : ℝ) (n : ℕ) :
    ((poch a n : ℝ) : ℂ) = (ascPochhammer ℂ n).eval (a : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [poch_succ, ascPochhammer_succ_eval, ← ih]; push_cast; ring

private lemma choose_eq_poch (a : ℝ) (n : ℕ) :
    Ring.choose ((a : ℂ) + n - 1) n = ((poch a n / (n.factorial : ℝ) : ℝ) : ℂ) := by
  have h1 := Ring.multichoose_eq (a : ℂ) n
  have h2 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (a : ℂ) n
  rw [Polynomial.ascPochhammer_smeval_eq_eval] at h2
  rw [← h1]
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [nsmul_eq_mul] at h2
  push_cast
  rw [poch_cast_eq, eq_div_iff hf, ← h2]
  ring

/-- The binomial series `(1 - z)^{-a} = ∑ (a)_m / m! z^m` for `|z| < 1`, real `a`. -/
lemma hasSum_poch_binom (a : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun m : ℕ => ((poch a m / (m.factorial : ℝ) : ℝ) : ℂ) * z ^ m)
      ((1 - z) ^ (-(a : ℂ))) := by
  have hball : z ∈ Metric.eball (0 : ℂ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
    exact ENNReal.ofReal_lt_one.2 hz
  have h := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (a : ℂ)).hasSum (y := z) hball
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, zero_add, smul_eq_mul] at h
  rw [Complex.cpow_neg, ← one_div]
  convert h using 2 with m
  rw [choose_eq_poch]

/-! ### The generating function -/

/-- The generating function `(1 - z)^{-w} exp(-x z/(1-z))`. -/
noncomputable def lagGen (w x : ℝ) (z : ℂ) : ℂ :=
  (1 - z) ^ (-(w : ℂ)) * Complex.exp (-(x : ℂ) * z / (1 - z))

/-- The doubly indexed terms of the generating function. -/
private noncomputable def genTerm (w x : ℝ) (z : ℂ) (p : ℕ × ℕ) : ℂ :=
  (-(x : ℂ) * z) ^ p.1 / (p.1.factorial : ℂ) * ((lagCoef w p.1 p.2 : ℝ) : ℂ) * z ^ p.2

private lemma norm_genTerm (w x : ℝ) (z : ℂ) (p : ℕ × ℕ) (hw : 0 < w) :
    ‖genTerm w x z p‖ = (|x| * ‖z‖) ^ p.1 / (p.1.factorial : ℝ) * lagCoef w p.1 p.2 * ‖z‖ ^ p.2 := by
  unfold genTerm
  rw [norm_mul, norm_mul, norm_div, norm_pow, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_natCast, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (lagCoef_pos hw _ _)]

/-- Sum over the second index: `∑_m a(j, m) r^m = (1 - r)^{-(w + j)}` for `0 ≤ r < 1`. -/
private lemma hasSum_lagCoef_real (w : ℝ) (j : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    HasSum (fun m : ℕ => lagCoef w j m * r ^ m) ((1 - r) ^ (-(w + j))) := by
  have hrn : ‖(r : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr
  have h := hasSum_poch_binom (w + j) hrn
  have e : ((1 - (r : ℂ)) ^ (-((w + j : ℝ) : ℂ))) = (((1 - r) ^ (-(w + j)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_neg,
      ← Complex.ofReal_cpow (by linarith)]
  rw [e] at h
  have h' : HasSum (fun m : ℕ => ((lagCoef w j m * r ^ m : ℝ) : ℂ)) (((1 - r) ^ (-(w + j)) : ℝ) : ℂ) := by
    convert h using 2 with m
    simp [lagCoef]
  exact Complex.hasSum_ofReal.1 h'

private lemma summable_genTerm_norm (w x : ℝ) (hw : 0 < w) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun p : ℕ × ℕ => ‖genTerm w x z p‖) := by
  set r : ℝ := ‖z‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg z
  have hnn : 0 ≤ fun p : ℕ × ℕ => ‖genTerm w x z p‖ := fun p => norm_nonneg _
  simp_rw [norm_genTerm w x z _ hw]
  refine (summable_prod_of_nonneg (fun p => by
    have := lagCoef_pos hw p.1 p.2
    positivity)).2 ⟨fun j => ?_, ?_⟩
  · have := (hasSum_lagCoef_real w j hr0 hz).summable.mul_left ((|x| * r) ^ j / (j.factorial : ℝ))
    refine this.congr fun m => ?_
    ring
  · have hfun : ∀ j : ℕ, ∑' m : ℕ, (|x| * r) ^ j / (j.factorial : ℝ) * lagCoef w j m * r ^ m =
        (1 - r) ^ (-w) * ((|x| * r / (1 - r)) ^ j / (j.factorial : ℝ)) := by
      intro j
      have h1 := ((hasSum_lagCoef_real w j hr0 hz).mul_left ((|x| * r) ^ j / (j.factorial : ℝ))).tsum_eq
      have h2 : ∀ m : ℕ, (|x| * r) ^ j / (j.factorial : ℝ) * lagCoef w j m * r ^ m =
          (|x| * r) ^ j / (j.factorial : ℝ) * (lagCoef w j m * r ^ m) := fun m => by ring
      simp_rw [h2]
      rw [h1]
      have h1r : 0 < 1 - r := by linarith
      rw [Real.rpow_neg h1r.le, Real.rpow_add h1r, Real.rpow_natCast, Real.rpow_neg h1r.le, div_pow]
      field_simp
    have hsum : Summable (fun j : ℕ => (1 - r) ^ (-w) * ((|x| * r / (1 - r)) ^ j / (j.factorial : ℝ))) :=
      (Real.summable_pow_div_factorial _).mul_left _
    exact hsum.congr fun j => (hfun j).symm


/-- **Generating function of the Laguerre polynomials**: for `|z| < 1`,
`∑_k L_k^{(w-1)}(x) z^k = (1 - z)^{-w} exp(-x z/(1 - z))`. -/
theorem hasSum_lagL_gen {w : ℝ} (hw : 0 < w) (x : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (lagL w k x : ℂ) * z ^ k) (lagGen w x z) := by
  have hS : Summable (genTerm w x z) := Summable.of_norm (summable_genTerm_norm w x hw hz)
  have hz1 : (1 - z) ≠ 0 := by
    intro h
    have : z = 1 := by linear_combination -h
    rw [this] at hz; simp at hz
  -- fibres over the first index
  have hfib : ∀ j : ℕ, HasSum (fun m => genTerm w x z (j, m))
      ((-(x : ℂ) * z) ^ j / (j.factorial : ℂ) * (1 - z) ^ (-((w + j : ℝ) : ℂ))) := by
    intro j
    have h := (hasSum_poch_binom (w + j) hz).mul_left ((-(x : ℂ) * z) ^ j / (j.factorial : ℂ))
    convert h using 1
    ext m
    simp only [genTerm, lagCoef]
    push_cast
    ring
  -- sum over the first index
  have hg : HasSum (fun j : ℕ => (-(x : ℂ) * z) ^ j / (j.factorial : ℂ) * (1 - z) ^ (-((w + j : ℝ) : ℂ)))
      (lagGen w x z) := by
    have hexp : HasSum (fun j : ℕ => (-(x : ℂ) * z / (1 - z)) ^ j / (j.factorial : ℂ))
        (Complex.exp (-(x : ℂ) * z / (1 - z))) := by
      rw [Complex.exp_eq_exp_ℂ]
      exact NormedSpace.expSeries_div_hasSum_exp _
    have h := hexp.mul_left ((1 - z) ^ (-(w : ℂ)))
    unfold lagGen
    convert h using 1
    · ext j
      have e1 : (1 - z) ^ (-((w + j : ℝ) : ℂ)) = (1 - z) ^ (-(w : ℂ)) * ((1 - z)⁻¹) ^ j := by
        rw [show -((w + j : ℝ) : ℂ) = -(w : ℂ) + (-(j : ℂ)) by push_cast; ring,
          Complex.cpow_add _ _ hz1]
        congr 1
        rw [Complex.cpow_neg, Complex.cpow_natCast, inv_pow]
      rw [e1, div_pow, inv_pow]
      field_simp
  have hS' := hS.hasSum
  have hSg : HasSum (fun j : ℕ => (-(x : ℂ) * z) ^ j / (j.factorial : ℂ) * (1 - z) ^ (-((w + j : ℝ) : ℂ)))
      (∑' p, genTerm w x z p) := hS'.prod_fiberwise hfib
  have hSeq : ∑' p, genTerm w x z p = lagGen w x z := hSg.unique hg
  -- regroup along the antidiagonals
  have hσ : HasSum (genTerm w x z ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) (lagGen w x z) := by
    rw [← hSeq]; exact (Equiv.hasSum_iff _).2 hS'
  refine hσ.sigma (fun n => ?_)
  convert hasSum_fintype (fun c : Finset.antidiagonal n =>
    (genTerm w x z ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) ⟨n, c⟩) using 1
  simp only [Function.comp, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
  rw [Finset.sum_coe_sort (Finset.antidiagonal n) (genTerm w x z),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, lagL_eq_sum]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  simp only [genTerm]
  have : z ^ n = z ^ j * z ^ (n - j) := by rw [← pow_add, Nat.add_sub_cancel' hjn]
  rw [this, neg_mul, neg_pow ((x : ℂ) * z) j, mul_pow]
  ring


/-! ### Real form and the majorant `|L_k(x)| ≤ L_k(-x)` -/

/-- Real generating function `(1 - z)^{-w} exp(-x z/(1 - z))` (`z < 1`). -/
noncomputable def lagGenReal (w x z : ℝ) : ℝ := (1 - z) ^ (-w) * Real.exp (-x * z / (1 - z))

lemma lagGen_ofReal {z : ℝ} (hz : z < 1) (w x : ℝ) :
    lagGen w x (z : ℂ) = (lagGenReal w x z : ℂ) := by
  unfold lagGen lagGenReal
  have h1 : (1 - (z : ℂ)) = ((1 - z : ℝ) : ℂ) := by push_cast; ring
  rw [h1, show -(w : ℂ) = ((-w : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by linarith) (-w)]
  push_cast
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
    ← Complex.ofReal_div, ← Complex.ofReal_exp]

/-- **Real generating function**: `∑_k L_k^{(w-1)}(x) z^k = (1 - z)^{-w} exp(-x z/(1 - z))`, `|z| < 1`. -/
theorem hasSum_lagL_gen_real {w : ℝ} (hw : 0 < w) (x : ℝ) {z : ℝ} (hz : |z| < 1) :
    HasSum (fun k : ℕ => lagL w k x * z ^ k) (lagGenReal w x z) := by
  have hzn : ‖(z : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have h := hasSum_lagL_gen hw x hzn
  rw [lagGen_ofReal (lt_of_le_of_lt (le_abs_self z) hz)] at h
  have h' : HasSum (fun k : ℕ => ((lagL w k x * z ^ k : ℝ) : ℂ)) ((lagGenReal w x z : ℝ) : ℂ) := by
    convert h using 2 with k
    push_cast; ring
  exact Complex.hasSum_ofReal.1 h'

lemma lagL_neg_eq (w : ℝ) (k : ℕ) (x : ℝ) :
    lagL w k (-x) = ∑ j ∈ range (k + 1), lagCoef w j (k - j) / (j.factorial : ℝ) * x ^ j := by
  rw [lagL_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [neg_pow x j]
  have : ((-1 : ℝ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
  calc (-1) ^ j * lagCoef w j (k - j) / (j.factorial : ℝ) * ((-1) ^ j * x ^ j)
      = ((-1) ^ j * (-1) ^ j) * (lagCoef w j (k - j) / (j.factorial : ℝ) * x ^ j) := by ring
    _ = _ := by rw [this, one_mul]

lemma abs_lagL_le_neg {w : ℝ} (hw : 0 < w) {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    |lagL w k x| ≤ lagL w k (-x) := by
  rw [lagL_neg_eq, lagL_eq_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
  have h := lagCoef_pos hw j (k - j)
  rw [abs_mul, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos h,
    abs_of_pos (by positivity : (0 : ℝ) < (j.factorial : ℝ)), abs_pow, abs_of_nonneg hx]


/-! ### The Cauchy estimate -/

private lemma summable_abs_lagL {w : ℝ} (hw : 0 < w) {x : ℝ} (hx : 0 ≤ x) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1) : Summable (fun k : ℕ => |lagL w k x| * r ^ k) := by
  have h := (hasSum_lagL_gen_real hw (-x) (z := r) (by rwa [abs_of_nonneg hr0])).summable
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) h
  exact mul_le_mul_of_nonneg_right (abs_lagL_le_neg hw hx k) (pow_nonneg hr0 k)

private lemma hasFPowerSeriesOnBall_lagGen {w : ℝ} (hw : 0 < w) {x : ℝ} (hx : 0 ≤ x) :
    HasFPowerSeriesOnBall (lagGen w x)
      (FormalMultilinearSeries.ofScalars ℂ (fun k => (lagL w k x : ℂ))) 0 1 := by
  refine ⟨?_, one_pos, fun {y} hy => ?_⟩
  · refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    refine FormalMultilinearSeries.le_radius_of_summable _ ?_
    have hr1 : (r : ℝ) < 1 := by exact_mod_cast hr
    refine (summable_abs_lagL hw hx r.2 hr1).congr fun k => ?_
    rw [FormalMultilinearSeries.ofScalars_norm, Complex.norm_real, Real.norm_eq_abs]
    simp
  · have hyn : ‖y‖ < 1 := by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm] at hy
      exact ENNReal.ofReal_lt_one.1 hy
    have := hasSum_lagL_gen hw x hyn
    simp only [FormalMultilinearSeries.ofScalars_apply_eq, zero_add, smul_eq_mul]
    exact this

private lemma differentiableOn_lagGen (w x : ℝ) : DifferentiableOn ℂ (lagGen w x) (Metric.ball 0 1) := by
  intro z hz
  have hz1 : ‖z‖ < 1 := by simpa using hz
  have hre : 0 < (1 - z).re := by
    have : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    simp only [Complex.sub_re, Complex.one_re]
    linarith [(abs_le.1 this).2]
  have hne : (1 - z) ≠ 0 := fun h => by simp [h] at hre
  have h1 : (1 - z) ∈ Complex.slitPlane := Or.inl hre
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold lagGen
  refine DifferentiableAt.mul ?_ ?_
  · exact (differentiableAt_const _ |>.sub differentiableAt_id).cpow (differentiableAt_const _) h1
  · refine DifferentiableAt.cexp ?_
    exact ((differentiableAt_const _).mul differentiableAt_id).div
      (differentiableAt_const _ |>.sub differentiableAt_id) hne

/-- The real part of the exponent on the circle `|z| = θ`. -/
private lemma re_exponent_le {x θ : ℝ} (hx : 0 ≤ x) (hθ0 : 0 < θ) (hθ1 : θ < 1) {z : ℂ}
    (hz : ‖z‖ = θ) : (-(x : ℂ) * z / (1 - z)).re ≤ x * θ / (1 + θ) := by
  have hsq : z.re ^ 2 + z.im ^ 2 = θ ^ 2 := by
    rw [← hz, Complex.sq_norm, Complex.normSq_apply]; ring
  have hare : |z.re| ≤ θ := by rw [← hz]; exact Complex.abs_re_le_norm z
  have ha := abs_le.1 hare
  have hN : 0 < (1 - z.re) ^ 2 + z.im ^ 2 := by nlinarith
  have hre : (-(x : ℂ) * z / (1 - z)).re = -x * (z.re - θ ^ 2) / ((1 - z.re) ^ 2 + z.im ^ 2) := by
    rw [Complex.div_re, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im,
      Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, Complex.mul_im]
    have hN' : (1 - z.re) * (1 - z.re) + (0 - z.im) * (0 - z.im) = (1 - z.re) ^ 2 + z.im ^ 2 := by ring
    rw [hN']
    field_simp
    nlinarith [hsq]
  have hN2 : (1 - z.re) ^ 2 + z.im ^ 2 = 1 - 2 * z.re + θ ^ 2 := by nlinarith
  rw [hre, hN2, div_le_div_iff₀ (by rw [← hN2]; exact hN) (by linarith)]
  nlinarith [mul_nonneg hx (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ) (by linarith : (0 : ℝ) ≤ z.re + θ))]

private lemma norm_lagGen_le {w x θ : ℝ} (hw : 0 < w) (hx : 0 ≤ x) (hθ0 : 0 < θ) (hθ1 : θ < 1) {z : ℂ}
    (hz : ‖z‖ = θ) : ‖lagGen w x z‖ ≤ (1 - θ) ^ (-w) * Real.exp (x * θ / (1 + θ)) := by
  unfold lagGen
  rw [norm_mul, Complex.norm_exp]
  refine mul_le_mul ?_ (Real.exp_le_exp.2 (re_exponent_le hx hθ0 hθ1 hz)) (Real.exp_pos _).le
    (by positivity)
  rw [show -(w : ℂ) = ((-w : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_real]
  have h1 : 1 - θ ≤ ‖1 - z‖ := by
    have := norm_sub_norm_le (1 : ℂ) z
    simpa [hz] using this
  exact Real.rpow_le_rpow_of_nonpos (by linarith) h1 (by linarith)

/-- **Cauchy estimate** for the Laguerre polynomials: for `x ≥ 0`, `0 < θ < 1`,
`|L_k^{(w-1)}(x)| ≤ θ^{-k} (1 - θ)^{-w} exp(x θ/(1 + θ))`. -/
theorem abs_lagL_le {w : ℝ} (hw : 0 < w) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {x : ℝ} (hx : 0 ≤ x)
    (k : ℕ) : |lagL w k x| ≤ θ⁻¹ ^ k * ((1 - θ) ^ (-w) * Real.exp (x * θ / (1 + θ))) := by
  have hps := hasFPowerSeriesOnBall_lagGen hw hx
  have hdc : DiffContOnCl ℂ (lagGen w x) (Metric.ball (0 : ℂ) θ) := by
    refine DifferentiableOn.diffContOnCl ?_
    refine (differentiableOn_lagGen w x).mono ?_
    rw [closure_ball _ hθ0.ne']
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right] at hz
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  have hC : ∀ z ∈ Metric.sphere (0 : ℂ) θ, ‖lagGen w x z‖ ≤ (1 - θ) ^ (-w) * Real.exp (x * θ / (1 + θ)) :=
    fun z hz => norm_lagGen_le hw hx hθ0 hθ1 (by simpa using hz)
  have hcau := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hθ0 hdc hC
  have hfs := hps.factorial_smul 1 k
  have hid : iteratedDeriv k (lagGen w x) 0 = (k.factorial : ℂ) * (lagL w k x : ℂ) := by
    rw [iteratedDeriv_eq_iteratedFDeriv, ← hfs]
    simp
  rw [hid, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs] at hcau
  have hk : (0 : ℝ) < k.factorial := by positivity
  have hcau' : |lagL w k x| ≤ (1 - θ) ^ (-w) * Real.exp (x * θ / (1 + θ)) / θ ^ k := by
    have := hcau
    rw [mul_div_assoc] at this
    exact le_of_mul_le_mul_left (by simpa [mul_comm, mul_assoc, mul_left_comm] using this) hk
  calc |lagL w k x| ≤ _ := hcau'
    _ = θ⁻¹ ^ k * ((1 - θ) ^ (-w) * Real.exp (x * θ / (1 + θ))) := by
      rw [inv_pow]; ring


/-! ### The Cayley expansion of `Ξ_β` -/

/-- `ψ_k(t) = e^{-2πt} L_k^{(w-1)}(4π t)`, a nonzero multiple of `e^{-2πt} P_k(t)`. -/
noncomputable def lagPsi (w : ℝ) (k : ℕ) (t : ℝ) : ℝ := Real.exp (-2 * Real.pi * t) * lagL w k (4 * Real.pi * t)

/-- The thermal difference `Ξ_β(t) = e^{-2πβt} - β^{-w} e^{-2πt/β}` for a real weight `w`. -/
noncomputable def xiW (w β t : ℝ) : ℝ :=
  Real.exp (-2 * Real.pi * β * t) - β ^ (-w) * Real.exp (-2 * Real.pi * t / β)

/-- **Cauchy bound** for `ψ_k` (`dual_spectrum_limit.tex`, proof of Lemma LP-C): for `t ≥ 0`,
`|ψ_k(t)| ≤ (1 - θ)^{-w} θ^{-k} e^{-2π s_θ t}` with `s_θ = (1 - θ)/(1 + θ)`. -/
theorem abs_lagPsi_le {w : ℝ} (hw : 0 < w) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {t : ℝ} (ht : 0 ≤ t)
    (k : ℕ) : |lagPsi w k t| ≤ (1 - θ) ^ (-w) * θ⁻¹ ^ k * Real.exp (-2 * Real.pi * ((1 - θ) / (1 + θ)) * t) := by
  have hx : 0 ≤ 4 * Real.pi * t := by positivity
  have h := abs_lagL_le hw hθ0 hθ1 hx k
  unfold lagPsi
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (-2 * Real.pi * t) * Real.exp (4 * Real.pi * t * θ / (1 + θ)) =
      Real.exp (-2 * Real.pi * ((1 - θ) / (1 + θ)) * t) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  calc Real.exp (-2 * Real.pi * t) * |lagL w k (4 * Real.pi * t)|
      ≤ Real.exp (-2 * Real.pi * t) *
          (θ⁻¹ ^ k * ((1 - θ) ^ (-w) * Real.exp (4 * Real.pi * t * θ / (1 + θ)))) := by gcongr
    _ = (1 - θ) ^ (-w) * θ⁻¹ ^ k * (Real.exp (-2 * Real.pi * t) * Real.exp (4 * Real.pi * t * θ / (1 + θ))) := by ring
    _ = _ := by rw [hexp]

/-- **Cayley expansion** (`dual_spectrum_limit.tex`, `eq:eLagscalar`): for `|ϖ| < 1` and
`β = (1 + ϖ)/(1 - ϖ)`, `Ξ_β(t) = 2 (1 - ϖ)^w ∑_{k odd} ϖ^k ψ_k(t)`. -/
theorem hasSum_cayley {w : ℝ} (hw : 0 < w) {ϖ β : ℝ} (hϖ : |ϖ| < 1) (hβ : β = (1 + ϖ) / (1 - ϖ))
    (t : ℝ) :
    HasSum (fun n : ℕ => ϖ ^ (2 * n + 1) * lagPsi w (2 * n + 1) t)
      (xiW w β t / (2 * (1 - ϖ) ^ w)) := by
  have hϖ1 : -1 < ϖ ∧ ϖ < 1 := abs_lt.1 hϖ
  have h1 : 0 < 1 - ϖ := by linarith
  have h2 : 0 < 1 + ϖ := by linarith
  have hβpos : 0 < β := by rw [hβ]; positivity
  set x : ℝ := 4 * Real.pi * t with hx
  have hA := hasSum_lagL_gen_real hw x hϖ
  have hB := hasSum_lagL_gen_real hw x (z := -ϖ) (by rwa [abs_neg])
  have hdiff : HasSum (fun k : ℕ => Real.exp (-2 * Real.pi * t) *
      ((lagL w k x * ϖ ^ k - lagL w k x * (-ϖ) ^ k) / 2))
      (Real.exp (-2 * Real.pi * t) * ((lagGenReal w x ϖ - lagGenReal w x (-ϖ)) / 2)) :=
    ((hA.sub hB).div_const 2).mul_left _
  -- odd terms
  have hodd : HasSum (fun n : ℕ => ϖ ^ (2 * n + 1) * lagPsi w (2 * n + 1) t)
      (Real.exp (-2 * Real.pi * t) * ((lagGenReal w x ϖ - lagGenReal w x (-ϖ)) / 2)) := by
    have hinj : Function.Injective (fun n : ℕ => 2 * n + 1) := fun a b h => by simpa using h
    have hz : ∀ k ∉ Set.range (fun n : ℕ => 2 * n + 1), Real.exp (-2 * Real.pi * t) *
        ((lagL w k x * ϖ ^ k - lagL w k x * (-ϖ) ^ k) / 2) = 0 := by
      intro k hk
      have : Even k := by
        by_contra hodd
        exact hk ⟨(k - 1) / 2, by rcases Nat.not_even_iff_odd.1 hodd with ⟨m, rfl⟩; simp⟩
      rw [this.neg_pow]; ring
    have := (hinj.hasSum_iff hz).2 hdiff
    convert this using 1
    ext n
    simp only [Function.comp, lagPsi]
    rw [Odd.neg_pow ⟨n, rfl⟩]
    ring
  convert hodd using 1
  -- identify the sum
  have e1 : Real.exp (-2 * Real.pi * t) * Real.exp (-x * ϖ / (1 - ϖ)) = Real.exp (-2 * Real.pi * β * t) := by
    rw [← Real.exp_add]; congr 1
    rw [hx, hβ]; field_simp; ring
  have e2 : Real.exp (-2 * Real.pi * t) * Real.exp (-x * (-ϖ) / (1 - -ϖ)) =
      Real.exp (-2 * Real.pi * t / β) := by
    rw [← Real.exp_add]; congr 1
    have h2' : (1 + ϖ) ≠ 0 := h2.ne'
    rw [hx, hβ, show (1 - -ϖ) = 1 + ϖ by ring]; field_simp; ring
  have e3 : β ^ (-w) * (1 - ϖ) ^ (-w) = (1 + ϖ) ^ (-w) := by
    rw [hβ, ← Real.mul_rpow (by positivity) h1.le]; congr 1; field_simp
  have e4 : (1 - ϖ) ^ w * (1 - ϖ) ^ (-w) = 1 := by
    rw [← Real.rpow_add h1]; simp
  unfold lagGenReal xiW
  have : (1 - -ϖ) = 1 + ϖ := by ring
  rw [this]
  have hne : (1 - ϖ) ^ w ≠ 0 := (Real.rpow_pos_of_pos h1 w).ne'
  have hb : (1 - ϖ) ^ (-w) = ((1 - ϖ) ^ w)⁻¹ := Real.rpow_neg h1.le w
  calc xiW w β t / (2 * (1 - ϖ) ^ w) = ((1 - ϖ) ^ (-w) * Real.exp (-2 * Real.pi * β * t)
        - β ^ (-w) * (1 - ϖ) ^ (-w) * Real.exp (-2 * Real.pi * t / β)) / 2 := by
        rw [hb]
        unfold xiW
        field_simp
    _ = _ := by
        rw [e3, ← e1, ← e2]
        ring_nf


/-- info: 'FormalResearch.ModularBootstrap.LP.hasSum_lagL_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.LP.hasSum_lagL_gen

/-- info: 'FormalResearch.ModularBootstrap.LP.abs_lagL_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.LP.abs_lagL_le

/-- info: 'FormalResearch.ModularBootstrap.LP.abs_lagPsi_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.LP.abs_lagPsi_le

/-- info: 'FormalResearch.ModularBootstrap.LP.hasSum_cayley' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.LP.hasSum_cayley

end FormalResearch.ModularBootstrap.LP
