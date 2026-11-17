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

/-! ### Integration along a horizontal ray -/

/-- If `F' ` bounds `‖F'(z+s)‖ ≤ K/(‖z‖+s)^(p+1)` along the ray `z + [0,R]`, then
`‖F z - F (z+R)‖ ≤ (K/p) (‖z‖^{-p} - (‖z‖+R)^{-p})`. -/
lemma ray_bound {F F' : ℂ → ℂ} {z : ℂ} (hz : 0 < z.re) {K : ℝ} {p : ℕ} (hp : 1 ≤ p)
    (hF : ∀ w : ℂ, 0 < w.re → HasDerivAt F (F' w) w)
    (hb : ∀ s : ℝ, 0 ≤ s → ‖F' (z + s)‖ ≤ K / (‖z‖ + s) ^ (p + 1)) {R : ℝ} (hR : 0 ≤ R) :
    ‖F z - F (z + R)‖ ≤ K / p * (((‖z‖) ^ p)⁻¹ - ((‖z‖ + R) ^ p)⁻¹) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hr : 0 < ‖z‖ := norm_pos_iff.2 (fun h => by simp [h] at hz)
  set r := ‖z‖ with hr_def
  set f : ℝ → ℂ := fun τ => F (z + ((R - τ : ℝ) : ℂ)) - F (z + R) with hf
  set f' : ℝ → ℂ := fun τ => -F' (z + ((R - τ : ℝ) : ℂ)) with hf'
  set B : ℝ → ℝ := fun τ => K / ((q + 1 : ℕ) : ℝ) * (((r + R - τ) ^ (q + 1))⁻¹ - ((r + R) ^ (q + 1))⁻¹)
    with hB
  set B' : ℝ → ℝ := fun τ => K / (r + R - τ) ^ (q + 1 + 1) with hB'
  have hfd : ∀ τ ∈ Icc 0 R, HasDerivAt f (f' τ) τ := by
    intro τ hτ
    have hre : 0 < (z + ((R - τ : ℝ) : ℂ)).re := by
      simp; linarith [hτ.2]
    have hg : HasDerivAt (fun x : ℝ => z + ((R - x : ℝ) : ℂ)) (-1) τ := by
      have := (((hasDerivAt_const τ R).sub (hasDerivAt_id τ)).ofReal_comp).const_add z
      refine this.congr_deriv ?_
      simp
    have h := (hF _ hre).scomp τ hg
    have h2 := h.sub_const (F (z + R))
    refine h2.congr_deriv ?_
    simp [hf']
  have hBd : ∀ τ ∈ Ico 0 R, HasDerivAt B (B' τ) τ := by
    intro τ hτ
    have hpos : 0 < r + R - τ := by linarith [hτ.2]
    have hu : HasDerivAt (fun x : ℝ => r + R - x) (-1) τ := by
      have := ((hasDerivAt_const τ (r + R)).sub (hasDerivAt_id τ))
      refine this.congr_deriv ?_
      simp
    have h1 := (hu.pow (q + 1)).inv (pow_ne_zero _ hpos.ne')
    have h2 := (h1.sub_const (((r + R) ^ (q + 1))⁻¹)).const_mul (K / ((q + 1 : ℕ) : ℝ))
    refine h2.congr_deriv ?_
    simp only [hB']
    push_cast
    simp only [Pi.pow_apply]
    field_simp
    ring
  have hcont : ContinuousOn f (Icc 0 R) := fun τ hτ => (hfd τ hτ).continuousAt.continuousWithinAt
  have hBcont : ContinuousOn B (Icc 0 R) := by
    intro τ hτ
    have hpos : 0 < r + R - τ := by linarith [hτ.2]
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hB]
    have : ContinuousAt (fun x : ℝ => ((r + R - x) ^ (q + 1))⁻¹) τ :=
      ((continuousAt_const.sub continuousAt_id).pow _).inv₀ (pow_ne_zero _ hpos.ne')
    exact (this.sub continuousAt_const).const_mul _
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary' (f := f) (a := 0) (b := R)
    (f' := f') hcont (fun τ hτ => (hfd τ ⟨hτ.1, hτ.2.le⟩).hasDerivWithinAt)
    (B := B) (B' := B') (by simp [hf, hB]) hBcont
    (fun τ hτ => (hBd τ hτ).hasDerivWithinAt)
    (fun τ hτ => by
      simp only [hf', hB', norm_neg]
      have := hb (R - τ) (by linarith [hτ.2])
      have e : r + R - τ = r + (R - τ) := by ring
      rw [e]
      exact this)
  have := @key R ⟨hR, le_rfl⟩
  simpa [hf, hB] using this

/-- `‖binetI z‖ ≤ 1/‖z‖²` on `Re z > 0`. -/
theorem norm_binetI_le_div {z : ℂ} (hz : 0 < z.re) : ‖binetI z‖ ≤ 1 / ‖z‖ ^ 2 := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 (fun h => by simp [h] at hz)
  refine le_of_forall_nat (f := fun n : ℕ => 1 / 2 / (z.re + n)) (tendsto_div_add_nat hz _) fun n => ?_
  have hF : ∀ w : ℂ, 0 < w.re → HasDerivAt binetI (-binetI' w) w := fun w hw => hasDerivAt_binetI hw
  have hray := ray_bound (F := binetI) (F' := fun w => -binetI' w) (K := 2) (p := 2) hz (by norm_num)
    hF (fun s hs => by
      rw [norm_neg]
      simpa using norm_binetI'_shift_le hz hs) (R := n) (Nat.cast_nonneg n)
  have hzn : 0 < (z + n).re := by simp; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h1 := norm_binetI_le hzn
  have h2 : (1 : ℝ) / ‖z‖ ^ 2 ≥ 2 / ((2 : ℕ) : ℝ) * (((‖z‖) ^ 2)⁻¹ - ((‖z‖ + n) ^ 2)⁻¹) := by
    have : 0 ≤ ((‖z‖ + n) ^ 2)⁻¹ := by positivity
    push_cast
    rw [one_div]
    nlinarith
  calc ‖binetI z‖ = ‖(binetI z - binetI (z + n)) + binetI (z + n)‖ := by ring_nf
    _ ≤ ‖binetI z - binetI (z + n)‖ + ‖binetI (z + n)‖ := norm_add_le _ _
    _ ≤ 2 / ((2 : ℕ) : ℝ) * (((‖z‖) ^ 2)⁻¹ - ((‖z‖ + n) ^ 2)⁻¹) + 1 / 2 / (z.re + n) := by
        refine add_le_add hray ?_
        simpa using h1
    _ ≤ 1 / 2 / (z.re + n) + 1 / ‖z‖ ^ 2 := by linarith

/-- `‖binetB z‖ ≤ 2/‖z‖` on `Re z > 0`. -/
theorem norm_binetB_le_div {z : ℂ} (hz : 0 < z.re) : ‖binetB z‖ ≤ 2 / ‖z‖ := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 (fun h => by simp [h] at hz)
  refine le_of_forall_nat (f := fun n : ℕ => 1 / 6 / (z.re + n)) (tendsto_div_add_nat hz _) fun n => ?_
  have hF : ∀ w : ℂ, 0 < w.re → HasDerivAt binetB (-binetI w) w := fun w hw => hasDerivAt_binetB hw
  have hray := ray_bound (F := binetB) (F' := fun w => -binetI w) (K := 2) (p := 1) hz (by norm_num)
    hF (fun s hs => by
      rw [norm_neg]
      have hzs : 0 < (z + s).re := by simp; linarith
      have h1 := norm_binetI_le_div hzs
      have h2 := sq_norm_add_ge hz.le hs
      have hw : 0 < ‖z + s‖ := norm_pos_iff.2 (fun h => by simp [h] at hzs)
      refine h1.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      norm_num
      nlinarith) (R := n) (Nat.cast_nonneg n)
  have hzn : 0 < (z + n).re := by simp; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h1 := norm_binetB_le hzn
  have h2 : 2 / ‖z‖ ≥ 2 / ((1 : ℕ) : ℝ) * (((‖z‖) ^ 1)⁻¹ - ((‖z‖ + n) ^ 1)⁻¹) := by
    have : 0 ≤ (‖z‖ + n)⁻¹ := by positivity
    push_cast
    simp only [pow_one, div_one]
    rw [div_eq_mul_inv]
    nlinarith
  calc ‖binetB z‖ = ‖(binetB z - binetB (z + n)) + binetB (z + n)‖ := by ring_nf
    _ ≤ ‖binetB z - binetB (z + n)‖ + ‖binetB (z + n)‖ := norm_add_le _ _
    _ ≤ 2 / ((1 : ℕ) : ℝ) * (((‖z‖) ^ 1)⁻¹ - ((‖z‖ + n) ^ 1)⁻¹) + 1 / 6 / (z.re + n) := by
        refine add_le_add hray ?_
        simpa using h1
    _ ≤ 1 / 6 / (z.re + n) + 2 / ‖z‖ := by linarith

/-- info: 'FormalResearch.Special.ComplexStirling.norm_binetI'_le_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ComplexStirling.norm_binetI'_le_div

/-- info: 'FormalResearch.Special.ComplexStirling.norm_binetI_le_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ComplexStirling.norm_binetI_le_div

/-- info: 'FormalResearch.Special.ComplexStirling.norm_binetB_le_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ComplexStirling.norm_binetB_le_div

end FormalResearch.Special.ComplexStirling
