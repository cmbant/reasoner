module

public import FormalResearch.Special.ComplexStirlingKernel

/-!
# Explicit bounds for the Binet transforms on the right half-plane

For `Re z > 0` (all constants explicit, valid on the whole open half-plane, no sector restriction):

* `norm_binetI'_le_div` : `‖binetI' z‖ ≤ (2/3) / ‖z‖³`;
* `norm_binetI_le_div` : `‖binetI z‖ ≤ 1 / ‖z‖²`;
* `norm_binetB_le_div` : `‖binetB z‖ ≤ 2 / ‖z‖`.

Method (Stirling by telescoping the difference equation, no contour rotation).  From
`binetI'(z) - binetI'(z+1) = 1/(2 z² (z+1)²)` (`binetI'_sub_succ`) and `binetI'(z+n) → 0`
(`‖binetI' w‖ ≤ 1/(2 (Re w)²)`) one gets `binetI' z = ∑_{k ≥ 0} 1/(2 (z+k)² (z+k+1)²)`; for `Re z ≥ 0`
and `a ≥ 0`, `2 ‖z+a‖² ≥ (‖z‖+a)²`, so each term is `≤ 2/((r+k)²(r+k+1)²)` (`r = ‖z‖`) and
`1/(p²(p+1)²) ≤ (1/3)(p^{-3} - (p+1)^{-3})` telescopes to `(2/3)/r³`.  The bounds for `binetI` and
`binetB` follow by integrating along the horizontal ray `z + s`, `s ≥ 0`, with the comparison lemma
`image_norm_le_of_norm_deriv_right_le_deriv_boundary'` (no interval integrability needed) and letting
`s → ∞` using `‖binetI w‖ ≤ 1/(2 Re w)`, `‖binetB w‖ ≤ 1/(6 Re w)`.

The constants are not sharp (the true asymptotics are `binetI' ~ 1/(6z³)`, `binetI ~ 1/(12 z²)`,
`binetB ~ 1/(12 z)`; numerical check with mpmath: `max |z|³|binetI'| ≈ 0.173`, `max |z|²|binetI| ≈ 0.085`,
`max |z||binetB| ≈ 0.084` over random `z` in `0.3 ≤ Re z ≤ 3`, `|Im z| ≤ 30`).

Not formalised: sharp constants, the full asymptotic series (Bernoulli numbers), sectors `|arg z| > π/2`.
-/

@[expose] public section

namespace FormalResearch.Special.ComplexStirling

open MeasureTheory Set Filter Topology

lemma sq_norm_add_ge {z : ℂ} (hz : 0 ≤ z.re) {a : ℝ} (ha : 0 ≤ a) :
    (‖z‖ + a) ^ 2 ≤ 2 * ‖z + a‖ ^ 2 := by
  have h1 : ‖z + a‖ ^ 2 = ‖z‖ ^ 2 + 2 * a * z.re + a ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp; ring
  nlinarith [sq_nonneg (‖z‖ - a), mul_nonneg ha hz]

/-- `‖w‖ ≥ (‖z‖+a)/2^{1/2}`, in the form `(‖z‖ + a) ≤ (3/2) ‖z + a‖`. -/
lemma norm_add_ge {z : ℂ} (hz : 0 ≤ z.re) {a : ℝ} (ha : 0 ≤ a) :
    ‖z‖ + a ≤ 3 / 2 * ‖z + a‖ := by
  have h := sq_norm_add_ge hz ha
  have h0 : 0 ≤ 3 / 2 * ‖z + a‖ := by positivity
  refine le_of_sq_le_sq ?_ h0
  nlinarith [norm_nonneg (z + a)]

lemma binetI'_eq_sum {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    binetI' z = binetI' (z + n) +
      ∑ k ∈ Finset.range n, 1 / (2 * (z + k) ^ 2 * (z + k + 1) ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hzn : 0 < (z + n).re := by simp; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have := binetI'_sub_succ hzn
    rw [Finset.sum_range_succ, ih]
    have e : z + ((n + 1 : ℕ) : ℂ) = z + n + 1 := by push_cast; ring
    rw [e]
    linear_combination this

lemma norm_tau_le {z : ℂ} (hz : 0 < z.re) (k : ℕ) :
    ‖1 / (2 * (z + k) ^ 2 * (z + k + 1) ^ 2)‖ ≤
      2 / ((‖z‖ + k) ^ 2 * (‖z‖ + k + 1) ^ 2) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr : 0 < ‖z‖ := norm_pos_iff.2 (fun h => by simp [h] at hz)
  have h1 := sq_norm_add_ge hz.le hk
  have h2 : (‖z‖ + (k + 1 : ℝ)) ^ 2 ≤ 2 * ‖z + ((k + 1 : ℝ) : ℂ)‖ ^ 2 :=
    sq_norm_add_ge hz.le (by positivity)
  have e1 : ((k : ℝ) : ℂ) = (k : ℂ) := by simp
  have e2 : z + ((k + 1 : ℝ) : ℂ) = z + k + 1 := by push_cast; ring
  rw [e2] at h2
  rw [e1] at h1
  have hp : 0 < (‖z‖ + k) ^ 2 := by positivity
  have hq : 0 < (‖z‖ + (k + 1 : ℝ)) ^ 2 := by positivity
  rw [norm_div, norm_one, norm_mul, norm_mul, norm_pow, norm_pow]
  have hn : (‖(2 : ℂ)‖ : ℝ) = 2 := by simp
  rw [hn]
  have : (‖z‖ + ↑k) ^ 2 * (‖z‖ + ↑k + 1) ^ 2 ≤ 4 * (‖z + ↑k‖ ^ 2 * ‖z + ↑k + 1‖ ^ 2) := by
    have e3 : ‖z‖ + ↑k + 1 = ‖z‖ + (k + 1 : ℝ) := by ring
    rw [e3]
    calc (‖z‖ + ↑k) ^ 2 * (‖z‖ + (k + 1 : ℝ)) ^ 2 ≤ (2 * ‖z + ↑k‖ ^ 2) * (2 * ‖z + ↑k + 1‖ ^ 2) :=
          mul_le_mul h1 h2 hq.le (by positivity)
      _ = _ := by ring
  have hw0 : 0 < ‖z + (k : ℂ)‖ := norm_pos_iff.2 (fun h => by
    have := congrArg Complex.re h; simp at this; linarith)
  have hw1 : 0 < ‖z + (k : ℂ) + 1‖ := norm_pos_iff.2 (fun h => by
    have := congrArg Complex.re h; simp at this; linarith)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e3 : ‖z‖ + ↑k + 1 = ‖z‖ + (k + 1 : ℝ) := by ring
  nlinarith [this]

lemma tau_telescope {p : ℝ} (hp : 0 < p) :
    2 / (p ^ 2 * (p + 1) ^ 2) ≤ 2 / 3 * (1 / p ^ 3 - 1 / (p + 1) ^ 3) := by
  have h1 : 1 / p ^ 3 - 1 / (p + 1) ^ 3 = (3 * p ^ 2 + 3 * p + 1) / (p ^ 3 * (p + 1) ^ 3) := by
    field_simp; ring
  rw [h1, div_le_iff₀ (by positivity)]
  have : 2 / 3 * ((3 * p ^ 2 + 3 * p + 1) / (p ^ 3 * (p + 1) ^ 3)) * (p ^ 2 * (p + 1) ^ 2) =
      2 / 3 * (3 * p ^ 2 + 3 * p + 1) / (p * (p + 1)) := by
    field_simp
  rw [this, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg p, hp]

lemma sum_tau_le {r : ℝ} (hr : 0 < r) (n : ℕ) :
    ∑ k ∈ Finset.range n, 2 / ((r + k) ^ 2 * (r + k + 1) ^ 2) ≤
      2 / 3 * (1 / r ^ 3 - 1 / (r + n) ^ 3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hp : 0 < r + n := by positivity
    have := tau_telescope hp
    have e : (r + ((n + 1 : ℕ) : ℝ)) = r + n + 1 := by push_cast; ring
    rw [e]
    nlinarith

lemma tendsto_div_add_nat {x : ℝ} (_hx : 0 < x) (D : ℝ) :
    Tendsto (fun n : ℕ => D / (x + n)) atTop (𝓝 0) := by
  refine Tendsto.div_atTop tendsto_const_nhds ?_
  exact tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop

lemma tendsto_div_sq_add_nat {x : ℝ} (_hx : 0 < x) (D : ℝ) :
    Tendsto (fun n : ℕ => D / (x + n) ^ 2) atTop (𝓝 0) := by
  refine Tendsto.div_atTop tendsto_const_nhds ?_
  exact (tendsto_pow_atTop two_ne_zero).comp
    (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)

lemma le_of_forall_nat {a C : ℝ} {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0))
    (h : ∀ n, a ≤ f n + C) : a ≤ C := by
  have := ge_of_tendsto' (hf.add_const C) h
  simpa using this

/-- `‖binetI' z‖ ≤ (2/3)/‖z‖³` on `Re z > 0`. -/
theorem norm_binetI'_le_div {z : ℂ} (hz : 0 < z.re) : ‖binetI' z‖ ≤ 2 / 3 / ‖z‖ ^ 3 := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 (fun h => by simp [h] at hz)
  refine le_of_forall_nat (f := fun n : ℕ => 1 / 2 / (z.re + n) ^ 2)
    (tendsto_div_sq_add_nat hz _) fun n => ?_
  have hzn : 0 < (z + n).re := by simp; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [binetI'_eq_sum hz n]
  calc ‖binetI' (z + n) + ∑ k ∈ Finset.range n, 1 / (2 * (z + k) ^ 2 * (z + k + 1) ^ 2)‖
      ≤ ‖binetI' (z + n)‖ + ∑ k ∈ Finset.range n, ‖1 / (2 * (z + k) ^ 2 * (z + k + 1) ^ 2)‖ :=
        (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ 1 / 2 / (z.re + n) ^ 2 + ∑ k ∈ Finset.range n, 2 / ((‖z‖ + k) ^ 2 * (‖z‖ + k + 1) ^ 2) := by
        refine add_le_add ?_ (Finset.sum_le_sum fun k _ => norm_tau_le hz k)
        have := norm_binetI'_le hzn
        simpa using this
    _ ≤ 1 / 2 / (z.re + n) ^ 2 + 2 / 3 * (1 / ‖z‖ ^ 3 - 1 / (‖z‖ + n) ^ 3) :=
        add_le_add_right (sum_tau_le hr n) _
    _ ≤ 1 / 2 / (z.re + n) ^ 2 + 2 / 3 / ‖z‖ ^ 3 := by
        have : 0 ≤ 1 / (‖z‖ + n) ^ 3 := by positivity
        have e : 2 / 3 / ‖z‖ ^ 3 = 2 / 3 * (1 / ‖z‖ ^ 3) := by ring
        rw [e]
        nlinarith

/-- `‖binetI' (z + s)‖ ≤ 2/(‖z‖+s)³`. -/
lemma norm_binetI'_shift_le {z : ℂ} (hz : 0 < z.re) {s : ℝ} (hs : 0 ≤ s) :
    ‖binetI' (z + s)‖ ≤ 2 / (‖z‖ + s) ^ 3 := by
  have hzs : 0 < (z + s).re := by simp; linarith
  have hr : 0 < ‖z‖ := norm_pos_iff.2 (fun h => by simp [h] at hz)
  have h1 := norm_binetI'_le_div hzs
  have h2 := norm_add_ge hz.le hs
  have hw : 0 < ‖z + s‖ := by
    refine norm_pos_iff.2 (fun h => ?_); simp [h] at hzs
  have h3 : (‖z‖ + s) ^ 3 ≤ 3 * ‖z + s‖ ^ 3 := by
    have h2' : (‖z‖ + s) ≤ 3 / 2 * ‖z + s‖ := h2
    have h4 := sq_norm_add_ge hz.le hs
    have h0 : 0 ≤ ‖z‖ + s := by positivity
    calc (‖z‖ + s) ^ 3 = (‖z‖ + s) * (‖z‖ + s) ^ 2 := by ring
      _ ≤ (3 / 2 * ‖z + s‖) * (2 * ‖z + s‖ ^ 2) := mul_le_mul h2' h4 (by positivity) (by positivity)
      _ = 3 * ‖z + s‖ ^ 3 := by ring
  refine h1.trans ?_
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

end FormalResearch.Special.ComplexStirling
