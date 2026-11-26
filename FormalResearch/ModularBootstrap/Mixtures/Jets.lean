module

public import FormalResearch.ModularBootstrap.Mixtures.WeightAxioms

/-!
# `pmix:jets`: the parts of Proposition PM.13 that are mixture-specific (`positive_mixtures.tex`)

Proposition PM.13 identifies the exact boundary minimum `j(w, A) = inf 𝒥_{w,A} = α_tip g₁(w, A)` for the amplitude
`A` of a common source (via `ctu:jets`, `ctu:common-functional`: the outer function `G_outer^{(w,A)} = G_outer^{(w,1)} G_{A,4}`,
`G_{A,4} = exp L_f(P(z))`), and compares it with the components of a positive mixture by Jensen's inequality (`pmix:jensen`).

**What is formalised here** (all unconditional unless stated):

* `pmix_jets_hyp` (the first paragraph of the proof): the amplitude `A` of a common source satisfies the hypotheses of
  `ctu:jets` (`JetAmplitude`): real analytic (in fact entire) on a neighbourhood of `[ξ_*, ∞)`, `0 < d_λ Q_0(e^{-4πξ_*}) ≤ A ≤ ‖λ‖_TV`
  there, and `|A'| ≤ 4π S ‖λ‖_TV` (`S` the maximal shift, `≤ a₀`); no finiteness and no separation of the shifts is used.
* `xChart`, `xChart_hasDerivAt`, `shift_integral`: the chart `x(t) = π⁻¹ arsinh √q`, `q = √(1+t²)` of `ctu:jets` and the
  shift integral `∫₀^∞ x'(t)/t dt = ξ_*/√2` (`x'(t)/t = 1/(2π q^{3/2} √(1+q))`, antiderivative
  `(π√2)⁻¹ arsinh(t/(1+q))`).  This is the value of the contribution of a shift `r_i`: `-4π r_i ξ_*/√2`.
* `pmix_jensen`: the Jensen comparison.  For a mixture with `A = ∑ d_i A_i`, `A_i(x) = e^{-4π r_i x} Q_i(e^{-4πx})`,
  `p_i = d_i A_i(ξ_*)/A(ξ_*)`, `F_A(t) = log(A(x(t))/A(ξ_*))`, `F_i(t) = log(A_i(x(t))/A_i(ξ_*))`:
  `∑ p_i ∫₀^∞ F_i/t² dt ≤ ∫₀^∞ F_A/t² dt`, with equality iff the normalised component amplitudes coincide on `[ξ_*, ∞)`.
  (`∫ F/t² dt` is the integrated-by-parts form of `I₁(A) = ∫ ℓ`; the integrability of the six integrands is a named hypothesis,
  discharged in the paper by `F = O(t²)` at `0` and the growth bounds at `∞`.)

**What is not formalised (genuine gap).**  The identification of `∫ F/t²` with `j(w, A)`: `j(w,A) = α_tip g₁(w,A)`,
`g₁(w,A) = 2w - 3 - 2/π + 8 I₁(A)/π` (`ctu:g13A`), the defect identity, equality criterion and regularisation estimate
`ctu:J-quad` for the amplitude `A`, and the constants `c_0^*(w, Q_i)` of a product (`ctu:g13`, via `τ₁(μ)`) are the
content of `ctu:jets`/`ctu:common-functional` for a *general* amplitude: they require the outer function
`G_{A,4} = exp L_f(P(z))` (Poisson integral, boundary regularity, jets).  FIVE-0 has `OuterDatum` (and the minimum of `𝒥`,
`comb_minimum`) only as an interface and has it proved for the Virasoro data alone.  Hence the inequality `pmix:jensen`
for `j(w, A)` itself is not reached; `pmix_jensen` is its exact analytic core.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.WeightAxioms

/-! ### The hypotheses of `ctu:jets` for the amplitude of a common source -/

/-- The hypotheses of `ctu:jets` on an amplitude `A`: real analytic on a neighbourhood of `[ξ_*, ∞)`,
bounded above and below by positive constants, with bounded derivative there. -/
structure JetAmplitude (A : ℝ → ℝ) : Prop where
  analytic : AnalyticOnNhd ℝ A (Ici xiStar)
  lower : ∃ lo : ℝ, 0 < lo ∧ ∀ x : ℝ, xiStar ≤ x → lo ≤ A x
  upper : ∃ hi : ℝ, ∀ x : ℝ, xiStar ≤ x → A x ≤ hi
  deriv_bdd : ∃ D : ℝ, ∀ x : ℝ, xiStar ≤ x → |deriv A x| ≤ D

lemma ShiftSource.hasDerivAt_ampl (src : ShiftSource) (x : ℝ) :
    HasDerivAt src.ampl (∑ j, src.coef j * (-4 * π * src.shift j) *
      Real.exp (-4 * π * src.shift j * x)) x := by
  unfold ShiftSource.ampl
  refine HasDerivAt.fun_sum fun j _ => ?_
  have h1 : HasDerivAt (fun x : ℝ => -4 * π * src.shift j * x) (-4 * π * src.shift j) x := by
    simpa using (hasDerivAt_id x).const_mul (-4 * π * src.shift j)
  have := (h1.exp).const_mul (src.coef j)
  convert this using 1
  ring

lemma ShiftSource.analyticAt_ampl (src : ShiftSource) (x : ℝ) : AnalyticAt ℝ src.ampl x := by
  unfold ShiftSource.ampl
  fun_prop

/-- `|A'(x)| ≤ 4π S ‖λ‖_TV` for `x ≥ 0` when all shifts are `≤ S`. -/
lemma ShiftSource.abs_deriv_ampl_le (src : ShiftSource) {S : ℝ} (hS : ∀ j, src.shift j ≤ S) {x : ℝ}
    (hx : 0 ≤ x) : |deriv src.ampl x| ≤ 4 * π * S * src.tv := by
  rw [(src.hasDerivAt_ampl x).deriv]
  unfold ShiftSource.tv
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hs0 := src.hshift j
  have hexp : Real.exp (-4 * π * src.shift j * x) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, mul_nonneg hs0 hx]
  have hexp0 := Real.exp_pos (-4 * π * src.shift j * x)
  have habs : |(-4 * π * src.shift j)| = 4 * π * src.shift j := by
    rw [abs_of_nonpos (by nlinarith [Real.pi_pos, hs0])]; ring
  rw [abs_mul, abs_mul, abs_of_pos hexp0, habs]
  calc |src.coef j| * (4 * π * src.shift j) * Real.exp (-4 * π * src.shift j * x)
      ≤ |src.coef j| * (4 * π * src.shift j) * 1 :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 4 * π * src.shift j * |src.coef j| := by ring
    _ ≤ 4 * π * S * |src.coef j| :=
        mul_le_mul_of_nonneg_right (by nlinarith [hS j, Real.pi_pos]) (abs_nonneg _)

/-- **`pmix:jets`, hypotheses of `ctu:jets` and `ctu:common-functional`.**  The amplitude `A(x) = ∫ e^{-4πrx} dλ(r)`
of a common source is entire, `d_λ Q_0(e^{-4πξ_*}) ≤ A ≤ ‖λ‖_TV` on `x ≥ ξ_*`, and `|A'| ≤ 4π a₀ ‖λ‖_TV` on `x ≥ 0`
(`a₀` the charge threshold, which bounds every shift). -/
theorem pmix_jets_hyp (C : CommonSource) :
    JetAmplitude C.src.ampl ∧
      (∀ x : ℝ, xiStar ≤ x → C.F.d * C.F.prob.nullPoly (Real.exp (-4 * π * xiStar)) ≤ C.src.ampl x ∧
        C.src.ampl x ≤ C.src.tv) ∧
      (∀ x : ℝ, 0 ≤ x → |deriv C.src.ampl x| ≤ 4 * π * C.a₀ * C.src.tv) := by
  have hξ := xiStar_pos
  have hA0 := C.at_ (le_refl C.a₀)
  obtain ⟨-, hb, -, -, -⟩ := pmix_weight_b C hξ
  have hnp := (nullPoly_exp_bounds C.F.prob hξ).1
  have hlo : 0 < C.F.d * C.F.prob.nullPoly (Real.exp (-4 * π * xiStar)) := mul_pos C.F.hd hnp
  have hdv : ∀ x : ℝ, 0 ≤ x → |deriv C.src.ampl x| ≤ 4 * π * C.a₀ * C.src.tv := fun x hx =>
    C.src.abs_deriv_ampl_le hA0.shift hx
  refine ⟨⟨fun x _ => C.src.analyticAt_ampl x, ⟨_, hlo, fun x hx => (hb hx).1⟩,
    ⟨C.src.tv, fun x hx => (hb hx).2⟩,
    ⟨4 * π * C.a₀ * C.src.tv, fun x hx => hdv x (hξ.le.trans hx)⟩⟩, fun x hx => hb hx, hdv⟩

/-! ### The chart `x(t)` of `ctu:jets` and the shift integral -/

/-- `q(t) = √(1 + t²)`. -/
noncomputable def qChart (t : ℝ) : ℝ := Real.sqrt (1 + t ^ 2)

lemma qChart_pos (t : ℝ) : 0 < qChart t := Real.sqrt_pos.2 (by positivity)

lemma qChart_sq (t : ℝ) : qChart t ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)

lemma one_le_qChart (t : ℝ) : 1 ≤ qChart t := by
  unfold qChart; exact Real.one_le_sqrt.2 (by nlinarith [sq_nonneg t])

lemma qChart_hasDerivAt (t : ℝ) : HasDerivAt qChart (t / qChart t) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
    simpa using ((hasDerivAt_pow 2 t).const_add 1)
  have := h1.sqrt (by positivity)
  unfold qChart
  convert this using 1
  field_simp

/-- The chart `x(t) = π⁻¹ arsinh √q(t)` of `ctu:jets` (`x(0) = ξ_*`, `x(t) ≥ ξ_*`). -/
noncomputable def xChart (t : ℝ) : ℝ := Real.arsinh (Real.sqrt (qChart t)) / π

lemma xChart_zero : xChart 0 = xiStar := by
  unfold xChart xiStar qChart
  simp

lemma xiStar_le_xChart (t : ℝ) : xiStar ≤ xChart t := by
  unfold xChart xiStar
  refine div_le_div_of_nonneg_right ?_ Real.pi_pos.le
  refine Real.arsinh_le_arsinh.2 ?_
  exact Real.one_le_sqrt.2 (one_le_qChart t)

/-- `x'(t) = t / (2π q^{3/2} √(1+q))`, so `x'(t)/t = 1/(2π q^{3/2} √(1+q))` (the weight `ℓ`-factor of `ctu:jets`). -/
lemma xChart_hasDerivAt (t : ℝ) :
    HasDerivAt xChart (t / (2 * π * (qChart t * Real.sqrt (qChart t)) * Real.sqrt (1 + qChart t))) t := by
  have hq := qChart_hasDerivAt t
  have hqp := qChart_pos t
  have hr := hq.sqrt hqp.ne'
  have ha := hr.arsinh
  have := ha.div_const π
  unfold xChart
  convert this using 1
  have h1 : Real.sqrt (qChart t) ^ 2 = qChart t := Real.sq_sqrt hqp.le
  have hs : 0 < Real.sqrt (qChart t) := Real.sqrt_pos.2 hqp
  rw [h1]
  simp only [smul_eq_mul]
  field_simp

/-- The integrand of the shift integral, `x'(t)/t = 1 / (2π q^{3/2} √(1+q))`. -/
noncomputable def shiftDensity (t : ℝ) : ℝ :=
  1 / (2 * π * (qChart t * Real.sqrt (qChart t)) * Real.sqrt (1 + qChart t))

/-- The antiderivative `(π√2)⁻¹ arsinh(t/(1+q))` of `shiftDensity` (`v = tanh(u/2)`, `t = sinh u`). -/
noncomputable def shiftPrim (t : ℝ) : ℝ := Real.arsinh (t / (1 + qChart t)) / (π * Real.sqrt 2)

lemma shiftPrim_hasDerivAt (t : ℝ) : HasDerivAt shiftPrim (shiftDensity t) t := by
  have hq := qChart_hasDerivAt t
  have hqp := qChart_pos t
  have h1q : 0 < 1 + qChart t := by linarith
  have hv : HasDerivAt (fun t => t / (1 + qChart t)) (1 / (qChart t * (1 + qChart t))) t := by
    have h0 := (hasDerivAt_id t).div (hq.const_add 1) h1q.ne'
    have h2 := qChart_sq t
    have e : (1 * (1 + qChart t) - id t * (t / qChart t)) / (1 + qChart t) ^ 2 =
        1 / (qChart t * (1 + qChart t)) := by
      simp only [id]
      field_simp
      nlinarith [h2]
    exact h0.congr_deriv e
  have ha := hv.arsinh
  have := ha.div_const (π * Real.sqrt 2)
  unfold shiftPrim shiftDensity
  convert this using 1
  have h2 := qChart_sq t
  have hsq : 1 + (t / (1 + qChart t)) ^ 2 = 2 * qChart t / (1 + qChart t) := by
    field_simp
    nlinarith [h2]
  rw [hsq]
  have hs : 0 < Real.sqrt (qChart t) := Real.sqrt_pos.2 hqp
  have hs1 : 0 < Real.sqrt (1 + qChart t) := Real.sqrt_pos.2 h1q
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  simp only [smul_eq_mul]
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num)]
  have e1 : Real.sqrt (qChart t) ^ 2 = qChart t := Real.sq_sqrt hqp.le
  have e2 : Real.sqrt (1 + qChart t) ^ 2 = 1 + qChart t := Real.sq_sqrt h1q.le
  have e3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith [e1, e2, e3]

lemma shiftDensity_nonneg (t : ℝ) : 0 ≤ shiftDensity t := by
  unfold shiftDensity
  have := qChart_pos t
  positivity

lemma shiftPrim_zero : shiftPrim 0 = 0 := by
  unfold shiftPrim qChart
  simp

lemma tendsto_shiftPrim : Tendsto shiftPrim atTop (𝓝 (xiStar / Real.sqrt 2)) := by
  have hv : Tendsto (fun t : ℝ => t / (1 + qChart t)) atTop (𝓝 1) := by
    have hup : ∀ t : ℝ, 0 < t → t / (1 + qChart t) ≤ 1 := fun t ht => by
      rw [div_le_one (by linarith [qChart_pos t])]
      have : t ≤ qChart t := by
        unfold qChart
        exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg t])
      linarith
    have hlow : ∀ t : ℝ, 0 < t → 1 - 2 / t ≤ t / (1 + qChart t) := fun t ht => by
      have hq := qChart_pos t
      have hqt : t ≤ qChart t := by
        unfold qChart
        exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg t])
      have hqt2 : qChart t ≤ t + 1 / t := by
        have h2 := qChart_sq t
        have : qChart t ^ 2 ≤ (t + 1 / t) ^ 2 := by
          have : (t + 1 / t) ^ 2 = t ^ 2 + 2 + 1 / t ^ 2 := by field_simp; ring
          rw [h2, this]
          have : 0 ≤ 1 / t ^ 2 := by positivity
          linarith
        exact le_of_sq_le_sq (by simpa using this) (by positivity) |>.trans_eq rfl
      rw [le_div_iff₀ (by linarith)]
      have h3 : 1 - 2 / t = (t - 2) / t := by field_simp
      rw [h3, div_mul_eq_mul_div, div_le_iff₀ ht]
      nlinarith [hqt2, mul_pos ht ht, show t * (1 / t) = 1 by field_simp]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ tendsto_const_nhds
      (Filter.eventually_atTop.2 ⟨1, fun t ht => hlow t (by linarith)⟩)
      (Filter.eventually_atTop.2 ⟨1, fun t ht => hup t (by linarith)⟩)
    have : Tendsto (fun t : ℝ => 2 / t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  have h1 := (Real.continuous_arsinh.tendsto 1).comp hv
  have h2 := h1.div_const (π * Real.sqrt 2)
  have e : xiStar / Real.sqrt 2 = Real.arsinh 1 / (π * Real.sqrt 2) := by
    unfold xiStar; field_simp
  rw [e]
  exact h2

/-- **The shift integral** (`pmix:jets`, proof): `∫₀^∞ x'(t)/t dt = ∫₀^∞ dt / (2π q^{3/2} √(1+q)) = ξ_*/√2`. -/
theorem shift_integral : ∫ t in Ioi (0 : ℝ), shiftDensity t = xiStar / Real.sqrt 2 := by
  have hcont : ContinuousWithinAt shiftPrim (Ici 0) 0 :=
    (HasDerivAt.continuousAt (shiftPrim_hasDerivAt 0)).continuousWithinAt
  have hint : IntegrableOn shiftDensity (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg hcont (fun t _ => shiftPrim_hasDerivAt t)
      (fun t _ => shiftDensity_nonneg t) tendsto_shiftPrim
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun t _ => shiftPrim_hasDerivAt t) hint
    tendsto_shiftPrim
  rw [this, shiftPrim_zero, sub_zero]

/-- `x'(t) / t = shiftDensity t` for `t ≠ 0`. -/
lemma xChart_deriv_div (t : ℝ) (ht : t ≠ 0) : deriv xChart t / t = shiftDensity t := by
  rw [(xChart_hasDerivAt t).deriv]
  unfold shiftDensity
  field_simp

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_jets_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_jets_hyp

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.shift_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shift_integral

end FormalResearch.ModularBootstrap.Mixtures
