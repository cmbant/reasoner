module

public import FormalResearch.Special.ComplexStirlingLaplace

/-!
# The Binet kernel `1/2 - 1/t + 1/(e^t - 1)` and its Laplace transforms

`binetKernel t = 1/2 - 1/t + 1/(e^t - 1)` (the kernel of Binet's formula DLMF (5.9.10_2) for `Ln Γ`; its `z`-derivative gives `ψ`).  Elementary bounds, for `t > 0`:

* `0 ≤ binetKernel t ≤ min (1/2) (t/6)` (the sharp bound `t/12` is not needed and not proved);
* hence `binetKernelDiv t = binetKernel t / t ∈ [0, 1/6]`.

On `Re z > 0` (all from `ComplexStirlingLaplace`)

* `binetI z = ∫_0^∞ binetKernel(t) e^{-tz} dt`, `‖binetI z‖ ≤ 1/(2 Re z)`;
* `binetB z = ∫_0^∞ binetKernel(t)/t e^{-tz} dt`, `‖binetB z‖ ≤ 1/(6 Re z)`;
* `HasDerivAt binetB (-binetI z) z` and `HasDerivAt binetI (-binetI' z) z`, `binetI' z = ∫ t·binetKernel(t) e^{-tz}`;
* the difference equation `binetI z - binetI (z+1) = 1/(2z) + 1/(2(z+1)) - log(1+1/z)`
  (`binetI_sub_succ`), obtained from the kernel identity `binetKernel(t)(1-e^{-t}) = (1+e^{-t})/2 - (1-e^{-t})/t`
  and the Frullani-type transform `∫_0^∞ (1-e^{-t})/t e^{-tz} dt = log(1+1/z)` (`lap_frullani`, proved by
  differentiating in `z`: both sides have derivative `-1/(z(z+1))` and tend to `0` as `Re z → ∞`).

All numerical bounds are checked against mpmath (`sup binetKernel(t)/t = 1/12`, attained at `t → 0`).

Not formalised: the sharp bound `binetKernel t ≤ t/12`, the Bernoulli expansion of the kernel.
-/

@[expose] public section

namespace FormalResearch.Special.ComplexStirling

open MeasureTheory Set Filter Topology

/-- The Binet kernel `1/2 - 1/t + 1/(e^t - 1)`. -/
noncomputable def binetKernel (t : ℝ) : ℝ := 1 / 2 - 1 / t + 1 / (Real.exp t - 1)

/-- `binetKernel t / t`. -/
noncomputable def binetKernelDiv (t : ℝ) : ℝ := binetKernel t / t

/-- `∫_0^∞ binetKernel(t) e^{-tz} dt` (so that `ψ(z) = log z - 1/(2z) - binetI z`). -/
noncomputable def binetI (z : ℂ) : ℂ := lap binetKernel z

/-- `∫_0^∞ binetKernel(t)/t e^{-tz} dt` (so that `log Γ(z) = (z-1/2) log z - z + log(2π)/2 + binetB z`). -/
noncomputable def binetB (z : ℂ) : ℂ := lap binetKernelDiv z

lemma exp_sub_one_pos {t : ℝ} (ht : 0 < t) : 0 < Real.exp t - 1 := by
  have := Real.add_one_lt_exp ht.ne'
  linarith

/-- Monotonicity from a nonnegative derivative on `[0,∞)`. -/
private lemma monotoneOn_Ici_of_hasDerivAt {f f' : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (f' x) x)
    (h0 : ∀ x, 0 ≤ x → 0 ≤ f' x) : MonotoneOn f (Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt) ?_
  intro x hx
  rw [interior_Ici] at hx
  rw [(hd x).deriv]; exact h0 x (le_of_lt hx)

/-- `t e^t - e^t + 1 ≥ 0` for `t ≥ 0`. -/
private lemma aux_one {t : ℝ} (ht : 0 ≤ t) : 0 ≤ t * Real.exp t - Real.exp t + 1 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => x * Real.exp x - Real.exp x + 1) (x * Real.exp x) x := by
    intro x
    have h := ((hasDerivAt_id x).mul (Real.hasDerivAt_exp x)).sub (Real.hasDerivAt_exp x)
    refine HasDerivAt.congr_deriv (h.add_const 1) ?_
    show 1 * Real.exp x + x * Real.exp x - Real.exp x = x * Real.exp x
    ring
  have := monotoneOn_Ici_of_hasDerivAt hd (fun x hx => mul_nonneg hx (Real.exp_pos x).le)
    (Set.mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
  simpa using this

/-- `t e^t + t - 2 e^t + 2 ≥ 0` for `t ≥ 0`. -/
private lemma aux_two {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ t * Real.exp t + t - 2 * Real.exp t + 2 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => x * Real.exp x + x - 2 * Real.exp x + 2)
      (x * Real.exp x - Real.exp x + 1) x := by
    intro x
    have h := (((hasDerivAt_id x).mul (Real.hasDerivAt_exp x)).add (hasDerivAt_id x)).sub
      ((Real.hasDerivAt_exp x).const_mul 2)
    refine HasDerivAt.congr_deriv (h.add_const 2) ?_
    show 1 * Real.exp x + x * Real.exp x + 1 - 2 * Real.exp x = x * Real.exp x - Real.exp x + 1
    ring
  have := monotoneOn_Ici_of_hasDerivAt hd (fun x hx => aux_one hx)
    (Set.mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
  simpa using this

lemma binetKernel_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ binetKernel t := by
  unfold binetKernel
  have hu := exp_sub_one_pos ht
  have h2 := aux_two ht.le
  have : 1 / t - 1 / 2 ≤ 1 / (Real.exp t - 1) := by
    rw [div_sub_div _ _ ht.ne' two_ne_zero, div_le_div_iff₀ (by positivity) hu]
    nlinarith
  linarith

lemma binetKernel_le_half {t : ℝ} (ht : 0 < t) : binetKernel t ≤ 1 / 2 := by
  unfold binetKernel
  have hu : t ≤ Real.exp t - 1 := by linarith [Real.add_one_le_exp t]
  have : 1 / (Real.exp t - 1) ≤ 1 / t := one_div_le_one_div_of_le ht hu
  linarith

lemma binetKernel_le_div {t : ℝ} (ht : 0 < t) : binetKernel t ≤ t / 6 := by
  unfold binetKernel
  have hq : t + t ^ 2 / 2 + t ^ 3 / 6 ≤ Real.exp t - 1 := by
    have := Real.sum_le_exp_of_nonneg ht.le 4
    simp [Finset.sum_range_succ, Nat.factorial] at this
    linarith
  have hqpos : 0 < t + t ^ 2 / 2 + t ^ 3 / 6 := by positivity
  have h1 : 1 / (Real.exp t - 1) ≤ 1 / (t + t ^ 2 / 2 + t ^ 3 / 6) :=
    one_div_le_one_div_of_le hqpos hq
  have h2 : 1 / 2 - 1 / t + 1 / (t + t ^ 2 / 2 + t ^ 3 / 6) - t / 6 =
      -(t * (t ^ 2 + 3)) / (6 * (t ^ 2 + 3 * t + 6)) := by
    field_simp
    ring
  have h3 : -(t * (t ^ 2 + 3)) / (6 * (t ^ 2 + 3 * t + 6)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · have : 0 ≤ t * (t ^ 2 + 3) := by positivity
      linarith
    · positivity
  linarith

lemma binetKernelDiv_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ binetKernelDiv t :=
  div_nonneg (binetKernel_nonneg ht) ht.le

lemma binetKernelDiv_le {t : ℝ} (ht : 0 < t) : binetKernelDiv t ≤ 1 / 6 := by
  unfold binetKernelDiv
  rw [div_le_iff₀ ht]
  have := binetKernel_le_div ht
  linarith

lemma abs_binetKernel_le {t : ℝ} (ht : 0 < t) : |binetKernel t| ≤ 1 / 2 := by
  rw [abs_of_nonneg (binetKernel_nonneg ht)]; exact binetKernel_le_half ht

lemma abs_binetKernelDiv_le {t : ℝ} (ht : 0 < t) : |binetKernelDiv t| ≤ 1 / 6 := by
  rw [abs_of_nonneg (binetKernelDiv_nonneg ht)]; exact binetKernelDiv_le ht

lemma binetKernel_continuousOn : ContinuousOn binetKernel (Ioi 0) := by
  intro t ht
  have ht0 : (0 : ℝ) < t := ht
  have hu := (exp_sub_one_pos ht0).ne'
  refine ContinuousAt.continuousWithinAt ?_
  unfold binetKernel
  fun_prop (disch := first | exact ht0.ne' | exact hu)

lemma binetKernelDiv_continuousOn : ContinuousOn binetKernelDiv (Ioi 0) :=
  binetKernel_continuousOn.div continuousOn_id (fun _ ht => ne_of_gt ht)

lemma lap_congr {g h : ℝ → ℝ} (hgh : ∀ t, 0 < t → g t = h t) (z : ℂ) : lap g z = lap h z := by
  unfold lap
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [hgh t ht]

lemma t_mul_binetKernelDiv (t : ℝ) (ht : 0 < t) : t * binetKernelDiv t = binetKernel t := by
  unfold binetKernelDiv; field_simp

lemma norm_binetI_le {z : ℂ} (hz : 0 < z.re) : ‖binetI z‖ ≤ 1 / 2 / z.re :=
  norm_lap_le (fun _ ht => abs_binetKernel_le ht) hz

lemma norm_binetB_le {z : ℂ} (hz : 0 < z.re) : ‖binetB z‖ ≤ 1 / 6 / z.re :=
  norm_lap_le (fun _ ht => abs_binetKernelDiv_le ht) hz

/-- `binetI' z = ∫ t·binetKernel(t) e^{-tz} dt`. -/
noncomputable def binetI' (z : ℂ) : ℂ := lap (fun t => t * binetKernel t) z

lemma hasDerivAt_binetI {z : ℂ} (hz : 0 < z.re) : HasDerivAt binetI (-binetI' z) z :=
  hasDerivAt_lap binetKernel_continuousOn (fun _ ht => abs_binetKernel_le ht) hz

lemma norm_binetI'_le {z : ℂ} (hz : 0 < z.re) : ‖binetI' z‖ ≤ 1 / 2 / z.re ^ 2 :=
  norm_lap_mul_le (fun _ ht => abs_binetKernel_le ht) hz

lemma hasDerivAt_binetB {z : ℂ} (hz : 0 < z.re) : HasDerivAt binetB (-binetI z) z := by
  have h := hasDerivAt_lap binetKernelDiv_continuousOn (fun _ ht => abs_binetKernelDiv_le ht) hz
  have e : lap (fun t => t * binetKernelDiv t) z = binetI z :=
    lap_congr (fun t ht => t_mul_binetKernelDiv t ht) z
  rw [e] at h
  exact h

/-! ### Linearity, shifts and elementary transforms -/

/-- The right half-plane. -/
def rhp : Set ℂ := {z | 0 < z.re}

lemma isOpen_rhp : IsOpen rhp := isOpen_lt continuous_const Complex.continuous_re

lemma isPreconnected_rhp : IsPreconnected rhp := (convex_halfSpace_re_gt 0).isPreconnected

/-- A kernel is *admissible* if continuous and bounded on `(0, ∞)`. -/
def Adm (g : ℝ → ℝ) : Prop := ContinuousOn g (Ioi 0) ∧ ∃ M, ∀ t, 0 < t → |g t| ≤ M

lemma lap_add {g h : ℝ → ℝ} (hg : Adm g) (hh : Adm h) {z : ℂ} (hz : 0 < z.re) :
    lap (fun t => g t + h t) z = lap g z + lap h z := by
  obtain ⟨hgc, M, hM⟩ := hg
  obtain ⟨hhc, N, hN⟩ := hh
  unfold lap
  rw [← integral_add (lap_integrable hgc hM hz) (lap_integrable hhc hN hz)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [Complex.ofReal_add]; ring

lemma lap_const_mul (c : ℝ) (g : ℝ → ℝ) (z : ℂ) :
    lap (fun t => c * g t) z = c * lap g z := by
  unfold lap
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [Complex.ofReal_mul]; ring

lemma lap_sub {g h : ℝ → ℝ} (hg : Adm g) (hh : Adm h) {z : ℂ} (hz : 0 < z.re) :
    lap (fun t => g t - h t) z = lap g z - lap h z := by
  have hh' : Adm (fun t => (-1 : ℝ) * h t) := by
    obtain ⟨hhc, N, hN⟩ := hh
    refine ⟨continuousOn_const.mul hhc, N, fun t ht => ?_⟩
    simpa using hN t ht
  have := lap_add hg hh' hz
  rw [lap_const_mul] at this
  simp only [neg_mul, one_mul, Complex.ofReal_neg, Complex.ofReal_one] at this
  simp only [← sub_eq_add_neg] at this
  rw [← this]

/-- `lap g (z+1) = lap (e^{-t} g) z`. -/
lemma lap_add_one (g : ℝ → ℝ) (z : ℂ) :
    lap g (z + 1) = lap (fun t => Real.exp (-t) * g t) z := by
  unfold lap
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg, mul_add, mul_one,
    Complex.exp_add]
  ring_nf

lemma adm_const (c : ℝ) : Adm (fun _ => c) :=
  ⟨continuousOn_const, |c|, fun _ _ => le_rfl⟩

lemma adm_exp_neg : Adm (fun t => Real.exp (-t)) := by
  refine ⟨(Real.continuous_exp.comp continuous_neg).continuousOn, 1, fun t ht => ?_⟩
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (by linarith)

lemma lap_one {z : ℂ} (hz : 0 < z.re) : lap (fun _ => 1) z = 1 / z := by
  unfold lap
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have := integral_exp_mul_complex_Ioi (a := -z) (by simpa using hz) 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at this
  have e : ∀ t : ℝ, ((1 : ℝ) : ℂ) * Complex.exp (-(t : ℂ) * z) = Complex.exp (-z * (t : ℂ)) := by
    intro t; simp; ring_nf
  simp only [e]
  rw [this]; field_simp

lemma lap_exp_neg {z : ℂ} (hz : 0 < z.re) : lap (fun t => Real.exp (-t)) z = 1 / (z + 1) := by
  unfold lap
  have hz1 : 0 < (z + 1).re := by simp; linarith
  have hz0 : z + 1 ≠ 0 := fun h => by simp [h] at hz1
  have := integral_exp_mul_complex_Ioi (a := -(z + 1)) (by simp; linarith) 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at this
  have e : ∀ t : ℝ, ((Real.exp (-t) : ℝ) : ℂ) * Complex.exp (-(t : ℂ) * z) =
      Complex.exp (-(z + 1) * (t : ℂ)) := by
    intro t
    rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
  simp only [e]
  rw [this]; field_simp

/-! ### The Frullani-type transform `∫ (1-e^{-t})/t e^{-tz} dt = log(1+1/z)` -/

/-- `(1 - e^{-t})/t`. -/
noncomputable def frullaniKernel (t : ℝ) : ℝ := (1 - Real.exp (-t)) / t

lemma frullaniKernel_mem {t : ℝ} (ht : 0 < t) : 0 ≤ frullaniKernel t ∧ frullaniKernel t ≤ 1 := by
  unfold frullaniKernel
  have h1 : Real.exp (-t) < 1 := by
    have := Real.exp_lt_exp.2 (show -t < 0 by linarith)
    simpa using this
  have h2 : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  refine ⟨div_nonneg (by linarith) ht.le, ?_⟩
  rw [div_le_one ht]; linarith

lemma frullaniKernel_adm : Adm frullaniKernel := by
  refine ⟨?_, 1, fun t ht => ?_⟩
  · exact (continuousOn_const.sub (Real.continuous_exp.comp continuous_neg).continuousOn).div
      continuousOn_id (fun t ht => ne_of_gt ht)
  · rw [abs_of_nonneg (frullaniKernel_mem ht).1]; exact (frullaniKernel_mem ht).2

lemma t_mul_frullaniKernel {t : ℝ} (ht : 0 < t) : t * frullaniKernel t = 1 - Real.exp (-t) := by
  unfold frullaniKernel; field_simp

lemma slitPlane_one_add_inv {z : ℂ} (hz : 0 < z.re) : 1 + 1 / z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  have : 0 < (1 / z).re := by
    rw [one_div, Complex.inv_re]
    exact div_pos hz (Complex.normSq_pos.2 (fun h => by simp [h] at hz))
  rw [one_div, Complex.inv_re] at this
  simp only [Complex.add_re, Complex.one_re, one_div, Complex.inv_re]
  linarith

lemma hasDerivAt_log_one_add_inv {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (fun w : ℂ => Complex.log (1 + 1 / w)) (-1 / (z * (z + 1))) z := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hz1 : z + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hin : HasDerivAt (fun w : ℂ => 1 + 1 / w) (-(1 / z ^ 2)) z := by
    have := (hasDerivAt_inv hz0).const_add 1
    simpa [one_div] using this
  have h := hin.clog (slitPlane_one_add_inv hz)
  refine h.congr_deriv ?_
  field_simp

lemma lap_frullani_deriv {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (lap frullaniKernel) (-(1 / z - 1 / (z + 1))) z := by
  have h := hasDerivAt_lap frullaniKernel_adm.1 (M := 1)
    (fun t ht => by rw [abs_of_nonneg (frullaniKernel_mem ht).1]; exact (frullaniKernel_mem ht).2) hz
  have hz1 : 0 < (z + 1).re := by simp; linarith
  have e : lap (fun t => t * frullaniKernel t) z = 1 / z - 1 / (z + 1) := by
    rw [lap_congr (h := fun t => 1 - Real.exp (-t)) (fun t ht => t_mul_frullaniKernel ht),
      lap_sub (adm_const 1) adm_exp_neg hz, lap_one hz, lap_exp_neg hz]
  rw [e] at h
  exact h

/-- Frullani-type transform: `∫_0^∞ (1-e^{-t})/t · e^{-tz} dt = log(1+1/z)` for `Re z > 0`. -/
theorem lap_frullani {z : ℂ} (hz : 0 < z.re) :
    lap frullaniKernel z = Complex.log (1 + 1 / z) := by
  set Φ : ℂ → ℂ := fun w => lap frullaniKernel w - Complex.log (1 + 1 / w) with hΦ
  have hd : ∀ w ∈ rhp, HasDerivAt Φ 0 w := by
    intro w hw
    have h1 := lap_frullani_deriv (z := w) hw
    have h2 := hasDerivAt_log_one_add_inv hw
    have := h1.sub h2
    refine this.congr_deriv ?_
    have hwre : 0 < w.re := hw
    have hw0 : w ≠ 0 := fun h => by simp [h] at hwre
    have hw1 : w + 1 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    field_simp
    ring
  have hconst : ∀ w ∈ rhp, Φ w = Φ 1 := by
    intro w hw
    refine isOpen_rhp.is_const_of_deriv_eq_zero isPreconnected_rhp
      (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt) (fun x hx => (hd x hx).deriv)
      hw (by simp [rhp])
  -- `Φ 1 = 0` by letting `x → ∞`
  have hbound : ∀ x : ℝ, 1 ≤ x → ‖Φ 1‖ ≤ 2 / x := by
    intro x hx
    have hxr : (x : ℂ) ∈ rhp := by simp [rhp]; linarith
    rw [← hconst _ hxr]
    have hx0 : (0 : ℝ) < x := by linarith
    have h1 : ‖lap frullaniKernel (x : ℂ)‖ ≤ 1 / x := by
      have := norm_lap_le (M := 1) (g := frullaniKernel)
        (fun t ht => by rw [abs_of_nonneg (frullaniKernel_mem ht).1]; exact (frullaniKernel_mem ht).2)
        (z := (x : ℂ)) (by simpa using hx0)
      simpa using this
    have h2 : ‖Complex.log (1 + 1 / (x : ℂ))‖ ≤ 1 / x := by
      have e : (1 + 1 / (x : ℂ)) = ((1 + 1 / x : ℝ) : ℂ) := by push_cast; ring
      rw [e, ← Complex.ofReal_log (by positivity), Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg (by have : 0 < 1 / x := by positivity
                                           linarith))]
      have := Real.log_le_sub_one_of_pos (x := 1 + 1 / x) (by positivity)
      linarith
    calc ‖lap frullaniKernel (x : ℂ) - Complex.log (1 + 1 / (x : ℂ))‖
        ≤ ‖lap frullaniKernel (x : ℂ)‖ + ‖Complex.log (1 + 1 / (x : ℂ))‖ := norm_sub_le _ _
      _ ≤ 1 / x + 1 / x := add_le_add h1 h2
      _ = 2 / x := by ring
  have h0 : Φ 1 = 0 := by
    by_contra hne
    have hpos : 0 < ‖Φ 1‖ := norm_pos_iff.2 hne
    have := hbound (max 1 (3 / ‖Φ 1‖)) (le_max_left _ _)
    have hx : 3 / ‖Φ 1‖ ≤ max 1 (3 / ‖Φ 1‖) := le_max_right _ _
    have hxpos : 0 < max 1 (3 / ‖Φ 1‖) := lt_of_lt_of_le one_pos (le_max_left _ _)
    rw [le_div_iff₀ hxpos] at this
    rw [div_le_iff₀ hpos] at hx
    nlinarith
  have := hconst z hz
  rw [h0] at this
  exact sub_eq_zero.1 this

/-! ### The difference equation -/

lemma binetKernel_adm : Adm binetKernel :=
  ⟨binetKernel_continuousOn, 1 / 2, fun _ ht => abs_binetKernel_le ht⟩

lemma adm_exp_neg_mul_binetKernel : Adm (fun t => Real.exp (-t) * binetKernel t) := by
  refine ⟨(Real.continuous_exp.comp continuous_neg).continuousOn.mul binetKernel_continuousOn,
    1 / 2, fun t ht => ?_⟩
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 := abs_binetKernel_le ht
  nlinarith [abs_nonneg (binetKernel t), Real.exp_pos (-t)]

/-- Pointwise kernel identity `k(t)(1-e^{-t}) = (1+e^{-t})/2 - (1-e^{-t})/t`. -/
lemma binetKernel_identity {t : ℝ} (ht : 0 < t) :
    binetKernel t - Real.exp (-t) * binetKernel t =
      1 / 2 * (1 + Real.exp (-t)) - frullaniKernel t := by
  have hu : Real.exp t - 1 ≠ 0 := (exp_sub_one_pos ht).ne'
  have hE : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  unfold binetKernel frullaniKernel
  rw [Real.exp_neg]
  field_simp
  ring

/-- `binetI z - binetI (z+1) = 1/(2z) + 1/(2(z+1)) - log(1+1/z)` for `Re z > 0`. -/
theorem binetI_sub_succ {z : ℂ} (hz : 0 < z.re) :
    binetI z - binetI (z + 1) =
      1 / 2 * z⁻¹ + 1 / 2 * (z + 1)⁻¹ - Complex.log (1 + 1 / z) := by
  unfold binetI
  rw [lap_add_one, ← lap_sub binetKernel_adm adm_exp_neg_mul_binetKernel hz,
    lap_congr (h := fun t => 1 / 2 * (1 + Real.exp (-t)) - frullaniKernel t)
      (fun t ht => binetKernel_identity ht)]
  have hA : Adm (fun t => 1 / 2 * (1 + Real.exp (-t))) := by
    obtain ⟨hc, M, hM⟩ := adm_exp_neg
    refine ⟨continuousOn_const.mul (continuousOn_const.add hc), 1, fun t ht => ?_⟩
    have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [abs_of_nonneg (by positivity)]
    linarith [Real.exp_pos (-t)]
  rw [lap_sub hA frullaniKernel_adm hz, lap_const_mul,
    lap_add (adm_const 1) adm_exp_neg hz, lap_one hz, lap_exp_neg hz, lap_frullani hz]
  simp only [one_div]
  push_cast
  ring

lemma hasDerivAt_rho {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (fun w : ℂ => 1 / 2 * w⁻¹ + 1 / 2 * (w + 1)⁻¹ - Complex.log (1 + 1 / w))
      (-(1 / (2 * z ^ 2 * (z + 1) ^ 2))) z := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hz1 : z + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have h1 := (hasDerivAt_inv hz0).const_mul (1 / 2 : ℂ)
  have h2 := ((hasDerivAt_inv hz1).comp_add_const z 1 |>.const_mul (1 / 2 : ℂ))
  have h3 := hasDerivAt_log_one_add_inv hz
  refine ((h1.add h2).sub h3).congr_deriv ?_
  field_simp
  ring

/-- `binetI' z - binetI' (z+1) = 1/(2 z² (z+1)²)` for `Re z > 0`. -/
theorem binetI'_sub_succ {z : ℂ} (hz : 0 < z.re) :
    binetI' z - binetI' (z + 1) = 1 / (2 * z ^ 2 * (z + 1) ^ 2) := by
  have hz1 : 0 < (z + 1).re := by simp; linarith
  have hL : HasDerivAt (fun w => binetI w - binetI (w + 1)) (-binetI' z + binetI' (z + 1)) z := by
    have h1 := hasDerivAt_binetI hz
    have h2 := (hasDerivAt_binetI hz1).comp_add_const z 1
    refine (h1.sub h2).congr_deriv ?_
    ring
  have hev : (fun w => binetI w - binetI (w + 1)) =ᶠ[𝓝 z]
      (fun w : ℂ => 1 / 2 * w⁻¹ + 1 / 2 * (w + 1)⁻¹ - Complex.log (1 + 1 / w)) := by
    filter_upwards [isOpen_rhp.mem_nhds (show z ∈ rhp from hz)] with w hw
    exact binetI_sub_succ hw
  have := hL.unique (hasDerivAt_rho hz |>.congr_of_eventuallyEq hev)
  linear_combination -this

/-- info: 'FormalResearch.Special.ComplexStirling.lap_frullani' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ComplexStirling.lap_frullani

/-- info: 'FormalResearch.Special.ComplexStirling.binetI_sub_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ComplexStirling.binetI_sub_succ

/-- info: 'FormalResearch.Special.ComplexStirling.binetI'_sub_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ComplexStirling.binetI'_sub_succ

end FormalResearch.Special.ComplexStirling
