module

public import FormalResearch.ModularBootstrap.Mixtures.Source
public import FormalResearch.ModularBootstrap.WeightAxioms.Axioms

/-!
# Cardy asymptotes of a shifted kernel and of an atomic source (`pmix:weight` (b))

`pmix:weight` (b) (`positive_mixtures.tex`, Lemma PM.2 (b)): for every fixed `x₀ > 0`, uniformly on `x ≥ x₀`,
`V_mix(n x²/3) = (2x)^{w-1} as(n L(x)) [A(x) + ε_mix(x)]`, `|ε_mix| ≤ C_{x₀}/n`, and the same holomorphically
on a disc about `ξ_*`, with `A(b) = ∑_j coef_j e^{-4π shift_j b}`.

The paper obtains it from the absolute Cardy expansion `ctu:V-exp-A` (an expansion for any finite signed measure of
shifts).  Here it is derived from the already proved product asymptotes (`cardyV_asymptotic_real`,
`cardyErrC_bound_on_box`) by linearity, *without new Bessel analysis*: for a shift `r > 0`,
`K_{a - r} = K_a - V_{(r)}`, where `V_{(r)}` is the Cardy weight of the one-factor product `Q = 1 - q^r`
(`oneShift`), and `K_a` is the Cardy weight of `Q = 1`; the amplitudes of these are `1 - e^{-4π r x}` and `1`, so
the amplitude of `K_{a-r}` is `e^{-4π r x}` with error `≤ (C_{triv} + C_r)/c'`.

* `kernel_shift_real_asymp`, `kernel_shift_complex_asymp`: one shifted kernel (real line; sectorial box).
* `ShiftSource.real_asymp`, `ShiftSource.complex_asymp`: the atomic source, for charges `c' ≥ max 1 (24 S_λ)`
  (real) resp. `c' ≥ c₀` (box).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.WeightAxioms FormalResearch.ModularBootstrap.Bessel
  FormalResearch.ModularBootstrap.ComplexBessel FormalResearch.ModularBootstrap.FixedWeight

/-! ### The one-factor product `Q = 1 - q^r` -/

/-- The one-factor fixed-weight problem `Q(q) = 1 - q^r` (`m = 1`, `μ = r > 0`). -/
def oneShift (w : ℕ) (hw : 1 ≤ w) (r : ℝ) (hr : 0 < r) : FixedWeightProblem where
  w := w
  hw := hw
  m := 1
  μ := fun _ => r
  hμ := fun _ => hr

private lemma univ_finset_fin_one : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide

private lemma univ_finset_fin_zero : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by decide

lemma oneShift_totalShift (w : ℕ) (hw : 1 ≤ w) {r : ℝ} (hr : 0 < r) :
    (oneShift w hw r hr).totalShift = r := by
  unfold FixedWeightProblem.totalShift oneShift
  simp

lemma oneShift_cardyV (w : ℕ) (hw : 1 ≤ w) {r : ℝ} (hr : 0 < r) (a t : ℝ) :
    (oneShift w hw r hr).cardyV a t = kernelK w a t - kernelK w (a - r) t := by
  unfold FixedWeightProblem.cardyV
  show ∑ s : Finset (Fin 1), (-1 : ℝ) ^ s.card * kernelK w (a - ∑ l ∈ s, r) t = _
  rw [univ_finset_fin_one, Finset.sum_pair (by decide)]
  simp [sub_eq_add_neg]

lemma oneShift_nullPoly (w : ℕ) (hw : 1 ≤ w) {r : ℝ} (hr : 0 < r) (q : ℝ) :
    (oneShift w hw r hr).nullPoly q = 1 - q ^ r := by
  unfold FixedWeightProblem.nullPoly oneShift
  simp

lemma oneShift_cardyVC (w : ℕ) (hw : 1 ≤ w) {r : ℝ} (hr : 0 < r) (a : ℝ) (t : ℂ) :
    cardyVC (oneShift w hw r hr) a t = kernelKC w (a : ℂ) t - kernelKC w ((a - r : ℝ) : ℂ) t := by
  unfold cardyVC
  show ∑ s : Finset (Fin 1), (-1 : ℂ) ^ s.card * kernelKC w ((a - ∑ l ∈ s, r : ℝ) : ℂ) t = _
  rw [univ_finset_fin_one, Finset.sum_pair (by decide)]
  simp [sub_eq_add_neg]

lemma oneShift_nullPolyExpC (w : ℕ) (hw : 1 ≤ w) {r : ℝ} (hr : 0 < r) (b : ℂ) :
    nullPolyExpC (oneShift w hw r hr) b = 1 - Complex.exp (-4 * (Real.pi : ℂ) * (r : ℂ) * b) := by
  unfold nullPolyExpC oneShift
  simp

@[simp] lemma trivialProductProblem_w (w : ℕ) (hw : 1 ≤ w) : (trivialProductProblem w hw).w = w := rfl

lemma trivial_cardyV (w : ℕ) (hw : 1 ≤ w) (a t : ℝ) :
    (trivialProductProblem w hw).cardyV a t = kernelK w a t := by
  unfold FixedWeightProblem.cardyV
  show ∑ s : Finset (Fin 0), (-1 : ℝ) ^ s.card * kernelK w (a - ∑ l ∈ s, (Fin.elim0 l : ℝ)) t = _
  rw [univ_finset_fin_zero, Finset.sum_singleton]
  simp

lemma trivial_cardyVC (w : ℕ) (hw : 1 ≤ w) (a : ℝ) (t : ℂ) :
    cardyVC (trivialProductProblem w hw) a t = kernelKC w (a : ℂ) t := by
  unfold cardyVC
  show ∑ s : Finset (Fin 0), (-1 : ℂ) ^ s.card *
    kernelKC w ((a - ∑ l ∈ s, (Fin.elim0 l : ℝ) : ℝ) : ℂ) t = _
  rw [univ_finset_fin_zero, Finset.sum_singleton]
  simp

lemma trivial_nullPolyExpC (w : ℕ) (hw : 1 ≤ w) (b : ℂ) :
    nullPolyExpC (trivialProductProblem w hw) b = 1 := by
  unfold nullPolyExpC trivialProductProblem
  simp

/-! ### One shifted kernel -/

/-- **Real Cardy asymptote of a shifted kernel**: for `r ≥ 0`, `x₀ > 0`, uniformly in `x ≥ x₀` and `c' ≥ max 1 (24 r)`,
`|K_{c'/12 - r}(c' x²/3) / ((2x)^{w-1} as(c' L(x))) - e^{-4π r x}| ≤ C/c'`. -/
theorem kernel_shift_real_asymp (w : ℕ) (hw : 1 ≤ w) {r : ℝ} (hr : 0 ≤ r) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c' x : ℝ}, max 1 (24 * r) ≤ c' → x₀ ≤ x →
      |kernelK w (c' / 12 - r) (c' * x ^ 2 / 3) /
          ((2 * x) ^ (w - 1) * besselAs (c' * (2 * Real.pi * x / 3))) -
        Real.exp (-4 * Real.pi * r * x)| ≤ C / c' := by
  obtain ⟨C₁, hC₁, h₁⟩ := cardyV_asymptotic_real (trivialProductProblem w hw) hx₀
  rcases hr.eq_or_lt with rfl | hr_pos
  · refine ⟨C₁, hC₁, fun {c' x} hc' hx => ?_⟩
    have := h₁ (c' := c') (x := x) (by simpa using hc') hx
    simpa [trivial_cardyV, trivialProductProblem_nullPoly] using this
  · obtain ⟨C₂, hC₂, h₂⟩ := cardyV_asymptotic_real (oneShift w hw r hr_pos) hx₀
    refine ⟨C₁ + C₂, by positivity, fun {c' x} hc' hx => ?_⟩
    have hc1 : max 1 (24 * (trivialProductProblem w hw).totalShift) ≤ c' := by
      simpa using (le_max_left (1 : ℝ) (24 * r)).trans hc'
    have hc2 : max 1 (24 * (oneShift w hw r hr_pos).totalShift) ≤ c' := by
      rwa [oneShift_totalShift]
    have e1 := h₁ hc1 hx
    have e2 := h₂ hc2 hx
    rw [trivial_cardyV, trivialProductProblem_nullPoly] at e1
    rw [oneShift_cardyV, oneShift_nullPoly] at e2
    have hc_pos : 0 < c' := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hc')
    have hexp : (Real.exp (-4 * Real.pi * x)) ^ r = Real.exp (-4 * Real.pi * r * x) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]; congr 1; ring
    rw [hexp] at e2
    set pref := (2 * x) ^ (w - 1) * besselAs (c' * (2 * Real.pi * x / 3)) with hpref
    have hid : kernelK w (c' / 12 - r) (c' * x ^ 2 / 3) / pref - Real.exp (-4 * Real.pi * r * x) =
        (kernelK w (c' / 12) (c' * x ^ 2 / 3) / pref - 1) -
          ((kernelK w (c' / 12) (c' * x ^ 2 / 3) - kernelK w (c' / 12 - r) (c' * x ^ 2 / 3)) / pref -
            (1 - Real.exp (-4 * Real.pi * r * x))) := by
      rw [sub_div]; ring
    rw [hid]
    calc _ ≤ |kernelK w (c' / 12) (c' * x ^ 2 / 3) / pref - 1| +
          |(kernelK w (c' / 12) (c' * x ^ 2 / 3) - kernelK w (c' / 12 - r) (c' * x ^ 2 / 3)) / pref -
            (1 - Real.exp (-4 * Real.pi * r * x))| := abs_sub _ _
      _ ≤ C₁ / c' + C₂ / c' := add_le_add e1 e2
      _ = (C₁ + C₂) / c' := by ring

/-- The box on which the complex asymptote is controlled (`cardyErrC_bound_on_box`). -/
def Box (m₀ M₀ : ℝ) : Set ℂ := {b : ℂ | m₀ ≤ b.re ∧ |b.im| ≤ b.re ∧ ‖b‖ ≤ M₀}

/-- **Complex Cardy asymptote of a shifted kernel** on the sectorial box `{m₀ ≤ Re b, |Im b| ≤ Re b, ‖b‖ ≤ M₀}`:
`‖K_{c'/12 - r}(c' b²/3) / ((2b)^{w-1} as(c' L(b))) - e^{-4π r b}‖ ≤ C/c'` for `c' ≥ c₀`. -/
theorem kernel_shift_complex_asymp (w : ℕ) (hw : 1 ≤ w) {r : ℝ} (hr : 0 ≤ r) {m₀ M₀ : ℝ}
    (hm : 0 < m₀) (hM : 0 ≤ M₀) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ max 1 (24 * r) ≤ c₀ ∧ ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {b : ℂ}, b ∈ Box m₀ M₀ →
      ‖kernelKC w (((c' / 12 - r : ℝ)) : ℂ) ((c' : ℂ) * b ^ 2 / 3) /
          ((2 * b) ^ (w - 1) * asC ((c' : ℂ) * tipL b)) -
        Complex.exp (-4 * (Real.pi : ℂ) * (r : ℂ) * b)‖ ≤ C / c' := by
  obtain ⟨C₁, c₁, hC₁, hc₁, h₁⟩ := cardyErrC_bound_on_box (trivialProductProblem w hw) hm hM
  rcases hr.eq_or_lt with rfl | hr_pos
  · refine ⟨C₁, c₁, hC₁, by simpa using hc₁, fun {c'} hc' {b} hb => ?_⟩
    have := h₁ hc' hb.1 hb.2.1 hb.2.2
    unfold cardyErrC at this
    rw [trivial_cardyVC, trivial_nullPolyExpC] at this
    simpa using this
  · obtain ⟨C₂, c₂, hC₂, hc₂, h₂⟩ := cardyErrC_bound_on_box (oneShift w hw r hr_pos) hm hM
    refine ⟨C₁ + C₂, max c₁ c₂, by positivity, ?_, fun {c'} hc' {b} hb => ?_⟩
    · rw [oneShift_totalShift] at hc₂
      exact hc₂.trans (le_max_right _ _)
    have e1 := h₁ ((le_max_left _ _).trans hc') hb.1 hb.2.1 hb.2.2
    have e2 := h₂ ((le_max_right _ _).trans hc') hb.1 hb.2.1 hb.2.2
    unfold cardyErrC at e1 e2
    rw [trivial_cardyVC, trivial_nullPolyExpC] at e1
    rw [oneShift_cardyVC, oneShift_nullPolyExpC] at e2
    have hc_pos : 0 < c' := by
      have : 1 ≤ c₁ := (le_max_left _ _).trans hc₁
      exact lt_of_lt_of_le one_pos (this.trans ((le_max_left _ _).trans hc'))
    set den := (2 * b) ^ (w - 1) * asC ((c' : ℂ) * tipL b) with hden
    have hid : kernelKC w (((c' / 12 - r : ℝ)) : ℂ) ((c' : ℂ) * b ^ 2 / 3) / den -
        Complex.exp (-4 * (Real.pi : ℂ) * (r : ℂ) * b) =
        (kernelKC w ((c' / 12 : ℝ) : ℂ) ((c' : ℂ) * b ^ 2 / 3) / den - 1) -
          ((kernelKC w ((c' / 12 : ℝ) : ℂ) ((c' : ℂ) * b ^ 2 / 3) -
            kernelKC w (((c' / 12 - r : ℝ)) : ℂ) ((c' : ℂ) * b ^ 2 / 3)) / den -
            (1 - Complex.exp (-4 * (Real.pi : ℂ) * (r : ℂ) * b))) := by
      rw [sub_div]; ring
    rw [hid]
    calc _ ≤ ‖kernelKC w ((c' / 12 : ℝ) : ℂ) ((c' : ℂ) * b ^ 2 / 3) / den - 1‖ +
          ‖(kernelKC w ((c' / 12 : ℝ) : ℂ) ((c' : ℂ) * b ^ 2 / 3) -
            kernelKC w (((c' / 12 - r : ℝ)) : ℂ) ((c' : ℂ) * b ^ 2 / 3)) / den -
            (1 - Complex.exp (-4 * (Real.pi : ℂ) * (r : ℂ) * b))‖ := norm_sub_le _ _
      _ ≤ C₁ / c' + C₂ / c' := add_le_add e1 e2
      _ = (C₁ + C₂) / c' := by ring

/-! ### The atomic source -/

/-- Entire extension of `V_a` to complex `t`. -/
noncomputable def ShiftSource.cardyVC (src : ShiftSource) (a : ℝ) (t : ℂ) : ℂ :=
  ∑ j, (src.coef j : ℂ) * kernelKC src.w ((a - src.shift j : ℝ) : ℂ) t

lemma ShiftSource.cardyVC_entire (src : ShiftSource) (a : ℝ) : Differentiable ℂ (src.cardyVC a) := by
  unfold ShiftSource.cardyVC
  refine Differentiable.fun_sum fun j _ => ?_
  exact (kernelKC_entire_t src.w _).const_mul _

lemma ShiftSource.cardyVC_ofReal (src : ShiftSource) (a t : ℝ) :
    src.cardyVC a (t : ℂ) = (src.cardyV a t : ℂ) := by
  unfold ShiftSource.cardyVC ShiftSource.cardyV
  simp_rw [kernelKC_ofReal src.w src.hw]
  push_cast
  rfl

lemma ofProblem_cardyVC (prob : FixedWeightProblem) (a : ℝ) (t : ℂ) :
    (ShiftSource.ofProblem prob).cardyVC a t = cardyVC prob a t := by
  unfold ShiftSource.cardyVC cardyVC
  refine Finset.sum_congr rfl fun s _ => ?_
  show (((-1 : ℝ) ^ s.card : ℝ) : ℂ) * _ = _
  push_cast
  rfl

/-- **`pmix:weight` (b), real line** (`pmix:Vasym`): for every `x₀ > 0` there is `C` with, for all
`c' ≥ max 1 (24 S)` (`S ≥` every shift) and `x ≥ x₀`,
`|V(c' x²/3) / ((2x)^{w-1} as(c' L(x))) - A(x)| ≤ C / c'`. -/
theorem ShiftSource.real_asymp (src : ShiftSource) {S : ℝ} (hS : ∀ j, src.shift j ≤ S) {x₀ : ℝ}
    (hx₀ : 0 < x₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c' x : ℝ}, max 1 (24 * S) ≤ c' → x₀ ≤ x →
      |src.cardyV (c' / 12) (c' * x ^ 2 / 3) /
          ((2 * x) ^ (src.w - 1) * besselAs (c' * (2 * Real.pi * x / 3))) - src.ampl x| ≤ C / c' := by
  have hex : ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ {c' x : ℝ}, max 1 (24 * src.shift j) ≤ c' → x₀ ≤ x →
      |kernelK src.w (c' / 12 - src.shift j) (c' * x ^ 2 / 3) /
          ((2 * x) ^ (src.w - 1) * besselAs (c' * (2 * Real.pi * x / 3))) -
        Real.exp (-4 * Real.pi * src.shift j * x)| ≤ C / c' :=
    fun j => kernel_shift_real_asymp src.w src.hw (src.hshift j) hx₀
  choose C hC hbd using hex
  refine ⟨∑ j, |src.coef j| * C j, Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hC j),
    fun {c' x} hc' hx => ?_⟩
  have hc_pos : 0 < c' := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hc')
  have hcj : ∀ j, max 1 (24 * src.shift j) ≤ c' := fun j =>
    (max_le_max le_rfl (by linarith [hS j])).trans hc'
  have hsum : src.cardyV (c' / 12) (c' * x ^ 2 / 3) /
        ((2 * x) ^ (src.w - 1) * besselAs (c' * (2 * Real.pi * x / 3))) - src.ampl x =
      ∑ j, src.coef j * (kernelK src.w (c' / 12 - src.shift j) (c' * x ^ 2 / 3) /
          ((2 * x) ^ (src.w - 1) * besselAs (c' * (2 * Real.pi * x / 3))) -
        Real.exp (-4 * Real.pi * src.shift j * x)) := by
    unfold ShiftSource.cardyV ShiftSource.ampl
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j, |src.coef j * (kernelK src.w (c' / 12 - src.shift j) (c' * x ^ 2 / 3) /
          ((2 * x) ^ (src.w - 1) * besselAs (c' * (2 * Real.pi * x / 3))) -
        Real.exp (-4 * Real.pi * src.shift j * x))|
      ≤ ∑ j, |src.coef j| * (C j / c') := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hbd j (hcj j) hx) (abs_nonneg _)
    _ = (∑ j, |src.coef j| * C j) / c' := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by ring

/-- **`pmix:weight` (b), complex box** (holomorphic form of `pmix:Vasym`): for every box `Box m₀ M₀`
there are `C, c₀` with, for all `c' ≥ c₀` and `b` in the box,
`‖V_C(c' b²/3) / ((2b)^{w-1} as(c' L(b))) - A(b)‖ ≤ C / c'`. -/
theorem ShiftSource.complex_asymp (src : ShiftSource) (S : ℝ)
    {m₀ M₀ : ℝ} (hm : 0 < m₀) (hM : 0 ≤ M₀) :
    ∃ C c₀ : ℝ, 0 ≤ C ∧ max 1 (24 * S) ≤ c₀ ∧ ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {b : ℂ}, b ∈ Box m₀ M₀ →
      ‖src.cardyVC (c' / 12) ((c' : ℂ) * b ^ 2 / 3) /
          ((2 * b) ^ (src.w - 1) * asC ((c' : ℂ) * tipL b)) - src.amplC b‖ ≤ C / c' := by
  have hex : ∀ j, ∃ C c₀ : ℝ, 0 ≤ C ∧ max 1 (24 * src.shift j) ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {b : ℂ}, b ∈ Box m₀ M₀ →
        ‖kernelKC src.w (((c' / 12 - src.shift j : ℝ)) : ℂ) ((c' : ℂ) * b ^ 2 / 3) /
            ((2 * b) ^ (src.w - 1) * asC ((c' : ℂ) * tipL b)) -
          Complex.exp (-4 * (Real.pi : ℂ) * (src.shift j : ℂ) * b)‖ ≤ C / c' :=
    fun j => kernel_shift_complex_asymp src.w src.hw (src.hshift j) hm hM
  choose C c₀ hC hc₀ hbd using hex
  -- a common threshold: max of 1, 24 S and the individual thresholds
  refine ⟨∑ j, |src.coef j| * C j, max (max 1 (24 * S)) (∑ j, |c₀ j|),
    Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hC j), le_max_left _ _,
    fun {c'} hc' {b} hb => ?_⟩
  have hc1 : max 1 (24 * S) ≤ c' := (le_max_left _ _).trans hc'
  have hc_pos : 0 < c' := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hc1)
  have hcj : ∀ j, c₀ j ≤ c' := fun j => by
    have h1 : c₀ j ≤ |c₀ j| := le_abs_self _
    have h2 : |c₀ j| ≤ ∑ i, |c₀ i| :=
      Finset.single_le_sum (f := fun i => |c₀ i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
    exact h1.trans (h2.trans ((le_max_right _ _).trans hc'))
  have hsum : src.cardyVC (c' / 12) ((c' : ℂ) * b ^ 2 / 3) /
        ((2 * b) ^ (src.w - 1) * asC ((c' : ℂ) * tipL b)) - src.amplC b =
      ∑ j, (src.coef j : ℂ) * (kernelKC src.w (((c' / 12 - src.shift j : ℝ)) : ℂ) ((c' : ℂ) * b ^ 2 / 3) /
          ((2 * b) ^ (src.w - 1) * asC ((c' : ℂ) * tipL b)) -
        Complex.exp (-4 * (Real.pi : ℂ) * (src.shift j : ℂ) * b)) := by
    unfold ShiftSource.cardyVC ShiftSource.amplC
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j, ‖(src.coef j : ℂ) * (kernelKC src.w (((c' / 12 - src.shift j : ℝ)) : ℂ)
            ((c' : ℂ) * b ^ 2 / 3) / ((2 * b) ^ (src.w - 1) * asC ((c' : ℂ) * tipL b)) -
          Complex.exp (-4 * (Real.pi : ℂ) * (src.shift j : ℂ) * b))‖
      ≤ ∑ j, |src.coef j| * (C j / c') := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hbd j (hcj j) hb) (abs_nonneg _)
    _ = (∑ j, |src.coef j| * C j) / c' := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by ring

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.ShiftSource.real_asymp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ShiftSource.real_asymp

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.ShiftSource.complex_asymp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ShiftSource.complex_asymp

end FormalResearch.ModularBootstrap.Mixtures
