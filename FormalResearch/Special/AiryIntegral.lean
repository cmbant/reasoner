module

public import FormalResearch.Special.AiryIntegralArc
public import FormalResearch.Special.AiryAbel
public import FormalResearch.Special.AiryFourier

/-!
# The improper integrals `∫_0^∞ Ai = 1/3`, `∫_{-∞}^0 Ai = 2/3`, `∫_ℝ Ai = 1`

`Ai` is not Lebesgue integrable on `(-∞, 0)` (it oscillates with envelope `|x|^{-1/4}`), so the
negative half and the total are improper (conditionally convergent) integrals.  Proved here
(DLMF 9.10.11 for `∫_0^∞ Ai = 1/3`; the total `∫_ℝ Ai = 1` is the value of the Laplace transform
`e^{a³/3}` at `a = 0`):

* `tendsto_integral_airyAi_zero_top`: `∫_0^T Ai → 1/3` (`T → ∞`) and `integral_Ioi_airyAi : ∫_{(0,∞)} Ai = 1/3`
  (Lebesgue; `Ai` is integrable there);
* `tendsto_integral_airyAi_bot_zero`: `∫_{-T}^0 Ai → 2/3`;
* `tendsto_integral_airyAi_interval`: `∫_{-S}^{T} Ai → 1` as `S, T → ∞` independently.

**Proof.**  Let `L = ∫_{(0,∞)} Ai` and `P(z) = ∫_0^z Ai` (`airyPrim`, an entire primitive).
(i) Integrating the rotation identity (`airyPrim_rotation`) at `z = -y` gives
`P(-y) = -P(y e^{iπ/3}) - P(y e^{-iπ/3})`.  (ii) By Cauchy in the sector (the arc estimate
`norm_airyPrim_ray_sub_le`, which uses only the complex envelope `airyAiC_envelope`) both
`P(y e^{±iπ/3}) → L`.  Hence `∫_{-y}^0 Ai = -P(-y) → 2L`, with no asymptotics of `Ai` on the negative
axis.  (iii) The Abel-regularised identity `∫_ℝ Ai(x) e^{εx} dx = e^{ε³/3} → 1` (`AiryFourier`) splits into the
positive half (`→ L` by dominated convergence) and the negative half (`→ 2L` by the Abelian theorem
`tendsto_integral_mul_exp_neg_of_tendsto`, as `∫_{-T}^0 Ai` converges); so `3L = 1`.

Numerical check (mpmath, 30 digits): `∫_0^{60} Ai = 0.333333333333333333333333333333` (to all digits);
`∫_{-T}^0 Ai = 0.7657, 0.66423` for `T = 10, 100` and `(2/3 - ∫_{-T}^0 Ai) T^{3/4} = -0.557, 0.077`
(oscillating, `O(T^{-3/4})`, as expected from the `y^{-1/4}` envelope of `Ai(-y)`).

**Not formalised:** the rate of convergence of the negative half; that `Ai` is not Lebesgue integrable on
`(-∞,0)`; the one-sided Laplace transform `∫_0^∞ Ai(x) e^{-sx} dx` (no elementary closed form).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

lemma integrableOn_airyAi_Ioi : IntegrableOn airyAi (Ioi 0) := by
  have h := (integrable_airyAi_mul_exp one_pos).norm
  refine (h.integrableOn (s := Ioi 0)).mono' differentiable_airyAi.continuous.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have : 1 ≤ Real.exp (1 * x) := Real.one_le_exp (by linarith)
  nlinarith [abs_nonneg (airyAi x)]

/-- `L = ∫_{(0,∞)} Ai`. -/
noncomputable def airyIntPos : ℝ := ∫ x in Ioi (0 : ℝ), airyAi x

lemma tendsto_airyInt_pos :
    Tendsto (fun T : ℝ => ∫ x in (0 : ℝ)..T, airyAi x) atTop (𝓝 airyIntPos) :=
  intervalIntegral_tendsto_integral_Ioi 0 integrableOn_airyAi_Ioi tendsto_id

lemma tendsto_airyPrim_ray {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    Tendsto (fun ρ : ℝ => airyPrim ((ρ : ℂ) * cexp (((σ * (π / 3) : ℝ) : ℂ) * I))) atTop
      (𝓝 (airyIntPos : ℂ)) := by
  have h1 : Tendsto (fun ρ : ℝ => airyPrim (ρ : ℂ)) atTop (𝓝 (airyIntPos : ℂ)) := by
    have := (Complex.continuous_ofReal.tendsto _).comp tendsto_airyInt_pos
    refine this.congr fun T => ?_
    simp [airyPrim_real]
  have h2 : Tendsto (fun ρ : ℝ => airyPrim ((ρ : ℂ) * cexp (((σ * (π / 3) : ℝ) : ℂ) * I)) -
      airyPrim (ρ : ℂ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : Tendsto (fun ρ : ℝ => 3 * π / (2 * √ρ)) atTop (𝓝 0) := by
      have : Tendsto (fun ρ : ℝ => 2 * √ρ) atTop atTop :=
        Real.tendsto_sqrt_atTop.const_mul_atTop (by norm_num)
      exact this.const_div_atTop _
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
    exact norm_airyPrim_ray_sub_le hρ hσ
  have := h2.add h1
  rw [zero_add] at this
  exact this.congr fun ρ => sub_add_cancel _ _

lemma airyInt_neg_one_eq : (-1 : ℂ) = cexp (-(π * I)) := by
  rw [Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num

lemma airyPrim_neg_eq (y : ℝ) :
    airyPrim (-(y : ℂ)) = -(airyPrim ((y : ℂ) * cexp (((1 * (π / 3) : ℝ) : ℂ) * I)) +
      airyPrim ((y : ℂ) * cexp ((((-1 : ℝ) * (π / 3) : ℝ) : ℂ) * I))) := by
  have h := airyPrim_rotation (-(y : ℂ))
  have e1 : airyOmega * (-(y : ℂ)) = (y : ℂ) * cexp ((((-1 : ℝ) * (π / 3) : ℝ) : ℂ) * I) := by
    rw [airyOmega_eq_exp, neg_eq_neg_one_mul, airyInt_neg_one_eq]
    rw [show cexp (2 * π * I / 3) * (cexp (-(π * I)) * (y : ℂ)) =
      (y : ℂ) * (cexp (2 * π * I / 3) * cexp (-(π * I))) by ring, ← Complex.exp_add]
    congr 2
    push_cast; ring
  have e2 : airyOmega ^ 2 * (-(y : ℂ)) = (y : ℂ) * cexp (((1 * (π / 3) : ℝ) : ℂ) * I) := by
    have hω2 : airyOmega ^ 2 = cexp (4 * π * I / 3) := by
      rw [airyOmega_eq_exp, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
    rw [hω2, neg_eq_neg_one_mul, airyInt_neg_one_eq]
    rw [show cexp (4 * π * I / 3) * (cexp (-(π * I)) * (y : ℂ)) =
      (y : ℂ) * (cexp (4 * π * I / 3) * cexp (-(π * I))) by ring, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [e1, e2] at h
  linear_combination h

lemma airyInt_neg_cast (T : ℝ) : ((∫ x in (-T)..0, airyAi x : ℝ) : ℂ) =
    airyPrim ((T : ℂ) * cexp (((1 * (π / 3) : ℝ) : ℂ) * I)) +
      airyPrim ((T : ℂ) * cexp ((((-1 : ℝ) * (π / 3) : ℝ) : ℂ) * I)) := by
  have h1 := airyPrim_real (-T)
  have h2 := airyPrim_neg_eq T
  rw [intervalIntegral.integral_symm] at h1
  push_cast at h1
  rw [h2] at h1
  linear_combination h1

/-- `∫_{-T}^0 Ai → 2 L`, `L = ∫_{(0,∞)} Ai`: Cauchy on the sector `|arg z| ≤ π/3`. -/
lemma tendsto_airyInt_neg :
    Tendsto (fun T : ℝ => ∫ x in (-T)..0, airyAi x) atTop (𝓝 (2 * airyIntPos)) := by
  have h1 := tendsto_airyPrim_ray (σ := 1) (Or.inl rfl)
  have h2 := tendsto_airyPrim_ray (σ := -1) (Or.inr rfl)
  have h := ((Complex.continuous_re.tendsto _).comp (h1.add h2))
  refine (h.congr fun T => ?_).trans (by simp [two_mul])
  simp only [Function.comp, ← airyInt_neg_cast, Complex.ofReal_re]

/-! ### The Abelian step -/

lemma integrable_airyAi_mul_exp_neg {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun y : ℝ => airyAi (-y) * Real.exp (-ε * y)) (Ioi 0) := by
  have := (integrable_airyAi_mul_exp hε).comp_neg
  refine this.integrableOn.congr_fun (fun y _ => ?_) measurableSet_Ioi
  simp

lemma tendsto_airyAbel_neg :
    Tendsto (fun ε : ℝ => ∫ y in Ioi (0 : ℝ), airyAi (-y) * Real.exp (-ε * y)) (𝓝[>] 0)
      (𝓝 (2 * airyIntPos)) := by
  refine tendsto_integral_mul_exp_neg_of_tendsto (f := fun y => airyAi (-y))
    (by have := differentiable_airyAi.continuous; fun_prop) ?_ (fun ε hε => integrable_airyAi_mul_exp_neg hε)
  refine tendsto_airyInt_neg.congr fun T => ?_
  rw [intervalIntegral.integral_comp_neg (fun x => airyAi x)]
  simp

lemma tendsto_airyAbel_pos :
    Tendsto (fun ε : ℝ => ∫ x in Ioi (0 : ℝ), airyAi x * Real.exp (ε * x)) (𝓝[>] 0)
      (𝓝 airyIntPos) := by
  have hb : Integrable (fun x : ℝ => |airyAi x * Real.exp (1 * x)|) :=
    (integrable_airyAi_mul_exp one_pos).abs
  have := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi (0 : ℝ)))
    (l := 𝓝[>] (0 : ℝ)) (F := fun ε x => airyAi x * Real.exp (ε * x))
    (f := fun x => airyAi x) (fun x => |airyAi x * Real.exp (1 * x)|) ?_ ?_ hb.integrableOn ?_
  · simpa [airyIntPos] using this
  · exact Eventually.of_forall fun ε =>
      ((differentiable_airyAi.continuous).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    have : Real.exp (ε * x) ≤ Real.exp (1 * x) := Real.exp_le_exp.mpr (by nlinarith [hε.2])
    exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have : Tendsto (fun ε : ℝ => airyAi x * Real.exp (ε * x)) (𝓝 0) (𝓝 (airyAi x * Real.exp (0 * x))) :=
      (by fun_prop : Continuous fun ε : ℝ => airyAi x * Real.exp (ε * x)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds

lemma airyInt_split (ε : ℝ) (hε : 0 < ε) :
    Real.exp (ε ^ 3 / 3) = (∫ y in Ioi (0 : ℝ), airyAi (-y) * Real.exp (-ε * y)) +
      ∫ x in Ioi (0 : ℝ), airyAi x * Real.exp (ε * x) := by
  have hint := integrable_airyAi_mul_exp hε
  rw [← integral_airyAi_mul_exp hε, ← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn]
  congr 1
  have h := integral_comp_neg_Ioi (0 : ℝ) (fun x => airyAi x * Real.exp (ε * x))
  simp only [neg_zero] at h
  rw [← h]
  simp

/-- `3 L = 1`, i.e. `L = ∫_{(0,∞)} Ai = 1/3`. -/
theorem airyIntPos_eq : airyIntPos = 1 / 3 := by
  have hsum := tendsto_airyAbel_neg.add tendsto_airyAbel_pos
  have hexp : Tendsto (fun ε : ℝ => Real.exp (ε ^ 3 / 3)) (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous fun ε : ℝ => Real.exp (ε ^ 3 / 3) := by fun_prop
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hexp' := hexp.congr' (by
    filter_upwards [self_mem_nhdsWithin] with ε hε using airyInt_split ε hε)
  have := tendsto_nhds_unique hexp' hsum
  linarith

/-- **`∫_0^∞ Ai = 1/3`** (Lebesgue; `Ai` is integrable on `(0, ∞)`). -/
theorem integral_Ioi_airyAi : ∫ x in Ioi (0 : ℝ), airyAi x = 1 / 3 := airyIntPos_eq

/-- **`∫_0^T Ai → 1/3`** as `T → ∞`. -/
theorem tendsto_integral_airyAi_zero_top :
    Tendsto (fun T : ℝ => ∫ x in (0 : ℝ)..T, airyAi x) atTop (𝓝 (1 / 3)) := by
  rw [← airyIntPos_eq]; exact tendsto_airyInt_pos

/-- **`∫_{-T}^0 Ai → 2/3`** as `T → ∞` (conditionally convergent). -/
theorem tendsto_integral_airyAi_bot_zero :
    Tendsto (fun T : ℝ => ∫ x in (-T)..0, airyAi x) atTop (𝓝 (2 / 3)) := by
  have := tendsto_airyInt_neg
  rwa [airyIntPos_eq, show 2 * (1 / 3 : ℝ) = 2 / 3 by norm_num] at this

/-- **`∫_{-S}^T Ai → 1`** as `S, T → ∞` independently: `∫_ℝ Ai = 1` as an improper integral. -/
theorem tendsto_integral_airyAi_interval :
    Tendsto (fun p : ℝ × ℝ => ∫ x in (-p.1)..p.2, airyAi x) (atTop ×ˢ atTop) (𝓝 1) := by
  have h1 := tendsto_integral_airyAi_bot_zero.comp (tendsto_fst (f := (atTop : Filter ℝ)) (g := (atTop : Filter ℝ)))
  have h2 := tendsto_integral_airyAi_zero_top.comp (tendsto_snd (f := (atTop : Filter ℝ)) (g := (atTop : Filter ℝ)))
  have := h1.add h2
  rw [show (2 / 3 + 1 / 3 : ℝ) = 1 by norm_num] at this
  refine this.congr fun p => ?_
  simp only [Function.comp]
  exact intervalIntegral.integral_add_adjacent_intervals
    (differentiable_airyAi.continuous.intervalIntegrable _ _)
    (differentiable_airyAi.continuous.intervalIntegrable _ _)

/-- Symmetric form: `∫_{-T}^T Ai → 1`. -/
theorem tendsto_integral_airyAi_symm :
    Tendsto (fun T : ℝ => ∫ x in (-T)..T, airyAi x) atTop (𝓝 1) :=
  tendsto_integral_airyAi_interval.comp (Filter.Tendsto.prodMk tendsto_id tendsto_id : Tendsto (fun T : ℝ => (T, T)) atTop (atTop ×ˢ atTop))

/-- info: 'FormalResearch.Special.integral_Ioi_airyAi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.integral_Ioi_airyAi

/-- info: 'FormalResearch.Special.tendsto_integral_airyAi_zero_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.tendsto_integral_airyAi_zero_top

/-- info: 'FormalResearch.Special.tendsto_integral_airyAi_bot_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.tendsto_integral_airyAi_bot_zero

/-- info: 'FormalResearch.Special.tendsto_integral_airyAi_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.tendsto_integral_airyAi_interval

end FormalResearch.Special
