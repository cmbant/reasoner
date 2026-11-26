module

public import FormalResearch.ModularBootstrap.Spin.Statements
public import FormalResearch.ModularBootstrap.Spin.SpinS22Strip
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lemma S2.1 (`spinnotes:S21`): Weighted control of the full spinning test class

Proves `SpinS21` (`spinning_foundations.tex`, lines 130–169): for all `c ≥ 40`
(`a = (c - 1) / 12 ≥ 13 / 4`) and `Φ ∈ \overline{\mathcal A}_{\rm spin}`,
`‖Φ‖_∞ ≤ ‖Φ‖_1 ≤ 3.2 M_2[Φ]`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal FourierTransform RealInnerProductSpace

namespace FormalResearch.ModularBootstrap.Spin

/-! ### Section 1: Pointwise bound `|Φ p| ≤ ∫ |Φ|` from Fourier oddness -/

lemma spinTestClass_abs_le_integral_abs {a : ℝ} {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) (p : ℝ × ℝ) :
    |Φ p| ≤ ∫ q : ℝ × ℝ, |Φ q| := by
  let x : EuclideanSpace ℝ (Fin 2) := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![p.1, p.2]
  have hx0 : x 0 = p.1 := rfl
  have hx1 : x 1 = p.2 := rfl
  have hfo := congrFun hΦ.fourier_odd x
  simp only [Real.fourier_eq, Pi.neg_apply, spinToEuc, hx0, hx1] at hfo
  have hnorm_lhs : ‖-((Φ p : ℝ) : ℂ)‖ = |Φ p| := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have hnorm_rhs : ‖∫ v : EuclideanSpace ℝ (Fin 2), 𝐞 (-⟪v, x⟫) • ((Φ (v 0, v 1) : ℝ) : ℂ)‖ ≤
      ∫ q : ℝ × ℝ, |Φ q| := by
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    let e : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))
    have hmpe : Measure.map e (volume : Measure (EuclideanSpace ℝ (Fin 2))) = volume :=
      ((volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).comp
        (PiLp.volume_preserving_ofLp (Fin 2))).map_eq
    have h1 := integral_map_equiv (μ := (volume : Measure (EuclideanSpace ℝ (Fin 2)))) e
      (fun q : ℝ × ℝ => |Φ q|)
    rw [hmpe] at h1
    rw [h1]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    have hev : (v.ofLp 0, v.ofLp 1) = e v := rfl
    dsimp only
    rw [hev, Circle.smul_def, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    simp
  rw [← hnorm_lhs, ← hfo]
  exact hnorm_rhs

/-! ### Section 2: Lower bound on `V_1(r)` and `V_1(r_L) V_1(r_R)` off the central region `E` -/

private lemma spinV1_ge_four_pi_sq_mul_sq {a : ℝ} (ha : 2 ≤ a) (r : ℝ) :
    4 * π ^ 2 * r ^ 2 ≤ spinV1 a r := by
  have habs : spinV1 a r = spinV1 a |r| := by
    rcases le_total 0 r with hr | hr
    · rw [abs_of_nonneg hr]
    · rw [abs_of_nonpos hr, spinV1_even]
  rw [habs, spinV1_eq_mul_sinh a |r|]
  set A : ℝ := Real.sqrt a + Real.sqrt (a - 2)
  set B : ℝ := Real.sqrt a - Real.sqrt (a - 2)
  have hA_pos : 0 < A := by positivity
  have hB_pos : 0 < B := by
    dsimp [B]
    exact sub_pos.mpr (Real.sqrt_lt_sqrt (by linarith) (by linarith))
  have hAB : A * B = 2 := by
    dsimp [A, B]
    have h1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
    have h2 : Real.sqrt (a - 2) ^ 2 = a - 2 := Real.sq_sqrt (by linarith)
    nlinarith
  have hu : π * |r| * A ≤ Real.sinh (π * |r| * A) :=
    Real.self_le_sinh_iff.mpr (by positivity)
  have hv : π * |r| * B ≤ Real.sinh (π * |r| * B) :=
    Real.self_le_sinh_iff.mpr (by positivity)
  have hmul : (π * |r| * A) * (π * |r| * B) ≤
      Real.sinh (π * |r| * A) * Real.sinh (π * |r| * B) :=
    mul_le_mul hu hv (by positivity) (by positivity)
  calc 4 * π ^ 2 * r ^ 2
      = 2 * ((π * |r| * A) * (π * |r| * B)) := by
        rw [← sq_abs r]
        calc 4 * π ^ 2 * |r| ^ 2 = 2 * (π ^ 2 * |r| ^ 2 * 2) := by ring
          _ = 2 * (π ^ 2 * |r| ^ 2 * (A * B)) := by rw [hAB]
          _ = 2 * ((π * |r| * A) * (π * |r| * B)) := by ring
    _ ≤ 2 * (Real.sinh (π * |r| * A) * Real.sinh (π * |r| * B)) := by linarith
    _ = 2 * Real.sinh (π * |r| * A) * Real.sinh (π * |r| * B) := by ring

private lemma spinV1_prod_ge_off_E {a : ℝ} (ha : 13 / 4 ≤ a) {p q : ℝ}
    (hp : 1 / 3 < p) (hq : (1 / 10 : ℝ) * Real.exp (-(π * Real.sqrt a / 2) * p) < q) :
    (0.72 : ℝ) < spinV1 a p * spinV1 a q := by
  have ha2 : 2 ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  have hsqa_pos : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hsqa_ge : (1.802 : ℝ) < Real.sqrt a := by
    refine Real.lt_sqrt_of_sq_lt ?_
    norm_num; linarith
  have hpi_gt : (3.1415 : ℝ) < π := Real.pi_gt_d4
  have hq0 : 0 < q := lt_trans (by positivity) hq
  -- Lower bound on `A = √a + √(a - 2) ≥ 1.62 √a`
  have hA_ge : 1.62 * Real.sqrt a ≤ Real.sqrt a + Real.sqrt (a - 2) := by
    have h1 : 0.62 * Real.sqrt a ≤ Real.sqrt (a - 2) := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [mul_pow, Real.sq_sqrt ha0.le]
      nlinarith
    linarith
  -- Lower bound `sinh(π A p) ≥ 0.49 exp(π A p)`
  have hpiAp_ge : 3 ≤ π * p * (Real.sqrt a + Real.sqrt (a - 2)) := by
    have h1 : 1.62 * 1.802 ≤ Real.sqrt a + Real.sqrt (a - 2) := by nlinarith
    have h2 : 3.1415 * (1 / 3 : ℝ) ≤ π * p := by nlinarith
    nlinarith
  have hsinh_Ap : 0.49 * Real.exp (π * p * (Real.sqrt a + Real.sqrt (a - 2))) ≤
      Real.sinh (π * p * (Real.sqrt a + Real.sqrt (a - 2))) := by
    rw [Real.sinh_eq]
    set X := π * p * (Real.sqrt a + Real.sqrt (a - 2))
    have hX2 : Real.exp (-X) ≤ 0.02 * Real.exp X := by
      have h1 : 6 ≤ 2 * X := by linarith
      have hexp6 : (0.02 : ℝ)⁻¹ ≤ Real.exp 6 := by
        have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 6 by norm_num) 5
        norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
        linarith
      have hexp2X : (0.02 : ℝ)⁻¹ ≤ Real.exp (2 * X) := hexp6.trans (Real.exp_le_exp.mpr h1)
      have hmul : Real.exp (-X) = Real.exp X / Real.exp (2 * X) := by
        rw [eq_div_iff (Real.exp_pos _).ne', ← Real.exp_add]
        congr 1; ring
      rw [hmul, div_le_iff₀ (Real.exp_pos _)]
      nlinarith [Real.exp_pos X]
    linarith
  -- Lower bound `sinh(π B p) ≥ π p / √a`
  have hB_pos : 0 < Real.sqrt a - Real.sqrt (a - 2) :=
    sub_pos.mpr (Real.sqrt_lt_sqrt (by linarith) (by linarith))
  have hB_ge : (Real.sqrt a)⁻¹ ≤ Real.sqrt a - Real.sqrt (a - 2) := by
    have hAB : (Real.sqrt a + Real.sqrt (a - 2)) * (Real.sqrt a - Real.sqrt (a - 2)) = 2 := by
      have h1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha0.le
      have h2 : Real.sqrt (a - 2) ^ 2 = a - 2 := Real.sq_sqrt (by linarith)
      nlinarith
    have hAle : Real.sqrt a + Real.sqrt (a - 2) ≤ 2 * Real.sqrt a := by
      have : Real.sqrt (a - 2) ≤ Real.sqrt a := Real.sqrt_le_sqrt (by linarith)
      linarith
    rw [← one_div, div_le_iff₀ hsqa_pos]
    nlinarith
  have hsinh_Bp : π * p / Real.sqrt a ≤ Real.sinh (π * p * (Real.sqrt a - Real.sqrt (a - 2))) := by
    have h1 : π * p / Real.sqrt a ≤ π * p * (Real.sqrt a - Real.sqrt (a - 2)) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hB_ge (by positivity)
    exact h1.trans (Real.self_le_sinh_iff.mpr (mul_nonneg (by positivity) hB_pos.le))
  -- Combine for `V_1(p)`
  have hV1p : 0.98 * π * (p / Real.sqrt a) *
      Real.exp (π * p * (Real.sqrt a + Real.sqrt (a - 2))) ≤ spinV1 a p := by
    rw [spinV1_eq_mul_sinh]
    have hmul := mul_le_mul hsinh_Ap hsinh_Bp (by positivity) (by positivity)
    calc 0.98 * π * (p / Real.sqrt a) * Real.exp (π * p * (Real.sqrt a + Real.sqrt (a - 2)))
        = 2 * ((0.49 * Real.exp (π * p * (Real.sqrt a + Real.sqrt (a - 2)))) *
            (π * p / Real.sqrt a)) := by ring
      _ ≤ 2 * (Real.sinh (π * p * (Real.sqrt a + Real.sqrt (a - 2))) *
            Real.sinh (π * p * (Real.sqrt a - Real.sqrt (a - 2)))) := by linarith
      _ = 2 * Real.sinh (π * p * (Real.sqrt a + Real.sqrt (a - 2))) *
            Real.sinh (π * p * (Real.sqrt a - Real.sqrt (a - 2))) := by ring
  -- Lower bound for `V_1(q)`
  have hV1q : (4 * π ^ 2 / 100) * Real.exp (-(π * Real.sqrt a * p)) ≤ spinV1 a q := by
    have h1 := spinV1_ge_four_pi_sq_mul_sq ha2 q
    have hq_sq : ((1 / 10 : ℝ) * Real.exp (-(π * Real.sqrt a / 2) * p)) ^ 2 ≤ q ^ 2 := by
      gcongr
    have hexp : Real.exp (-(π * Real.sqrt a / 2) * p) ^ 2 = Real.exp (-(π * Real.sqrt a * p)) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    calc (4 * π ^ 2 / 100) * Real.exp (-(π * Real.sqrt a * p))
        = 4 * π ^ 2 * (((1 / 10 : ℝ) * Real.exp (-(π * Real.sqrt a / 2) * p)) ^ 2) := by
          rw [mul_pow, hexp]; ring
      _ ≤ 4 * π ^ 2 * q ^ 2 := by gcongr
      _ ≤ spinV1 a q := h1
  -- Multiply `V_1(p)` and `V_1(q)`
  have hprod : (0.98 * 4 * π ^ 3 / 100) * (p / Real.sqrt a) *
      Real.exp (0.62 * π * Real.sqrt a * p) ≤ spinV1 a p * spinV1 a q := by
    have hexp_diff : 0.62 * π * Real.sqrt a * p ≤
        π * p * (Real.sqrt a + Real.sqrt (a - 2)) - π * Real.sqrt a * p := by
      have : 0.62 * Real.sqrt a ≤ (Real.sqrt a + Real.sqrt (a - 2)) - Real.sqrt a := by linarith
      nlinarith [Real.pi_pos, hp]
    have hmul := mul_le_mul hV1p hV1q (by positivity) (spinV1_nonneg ha2 p)
    calc (0.98 * 4 * π ^ 3 / 100) * (p / Real.sqrt a) * Real.exp (0.62 * π * Real.sqrt a * p)
        ≤ (0.98 * 4 * π ^ 3 / 100) * (p / Real.sqrt a) *
            Real.exp (π * p * (Real.sqrt a + Real.sqrt (a - 2)) - π * Real.sqrt a * p) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_diff) (by positivity)
      _ = (0.98 * π * (p / Real.sqrt a) * Real.exp (π * p * (Real.sqrt a + Real.sqrt (a - 2)))) *
            ((4 * π ^ 2 / 100) * Real.exp (-(π * Real.sqrt a * p))) := by
          rw [Real.exp_sub, div_eq_mul_inv, Real.exp_neg]; ring
      _ ≤ spinV1 a p * spinV1 a q := hmul
  -- Use `p > 1/3` and `0.62 * π / 3 > 0.649`
  have hconst_pre : (1.215 : ℝ) ≤ 0.98 * 4 * π ^ 3 / 100 := by
    have hpi3 : (3.1415 : ℝ) ^ 3 ≤ π ^ 3 := by gcongr
    linarith
  have hexp_p : Real.exp (0.649 * Real.sqrt a) ≤ Real.exp (0.62 * π * Real.sqrt a * p) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : 0.649 ≤ 0.62 * π / 3 := by linarith
    have h2 : (0.62 * π / 3) * Real.sqrt a ≤ 0.62 * π * Real.sqrt a * p := by
      have : 0 < 0.62 * π * Real.sqrt a := by positivity
      nlinarith
    nlinarith
  have h1 : (1.215 / 3 : ℝ) * (Real.exp (0.649 * Real.sqrt a) / Real.sqrt a) ≤
      spinV1 a p * spinV1 a q := by
    have hdiv : (1 / 3 : ℝ) / Real.sqrt a ≤ p / Real.sqrt a :=
      div_le_div_of_nonneg_right hp.le hsqa_pos.le
    have hnn1 : 0 ≤ (1 / 3 : ℝ) / Real.sqrt a := by positivity
    have hnn2 : 0 ≤ (0.98 * 4 * π ^ 3 / 100) * (p / Real.sqrt a) := by positivity
    have hstep1 : 1.215 * ((1 / 3 : ℝ) / Real.sqrt a) ≤ (0.98 * 4 * π ^ 3 / 100) * (p / Real.sqrt a) :=
      mul_le_mul hconst_pre hdiv hnn1 (by linarith)
    calc (1.215 / 3 : ℝ) * (Real.exp (0.649 * Real.sqrt a) / Real.sqrt a)
        = (1.215 * ((1 / 3 : ℝ) / Real.sqrt a)) * Real.exp (0.649 * Real.sqrt a) := by ring
      _ ≤ ((0.98 * 4 * π ^ 3 / 100) * (p / Real.sqrt a)) *
            Real.exp (0.62 * π * Real.sqrt a * p) :=
          mul_le_mul hstep1 hexp_p (Real.exp_pos _).le hnn2
      _ ≤ spinV1 a p * spinV1 a q := hprod
  -- Monotonicity of `t ↦ exp(0.649 * t) / t` for `t ≥ 1.802`
  have hmono : Real.exp (0.649 * 1.802) / 1.802 ≤ Real.exp (0.649 * Real.sqrt a) / Real.sqrt a := by
    have hf : MonotoneOn (fun t : ℝ => Real.exp (0.649 * t) / t) (Ici (1.802 : ℝ)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici _) ?_ ?_ ?_
      · exact Continuous.continuousOn (Real.continuous_exp.comp (continuous_const.mul continuous_id)) |>.div
          continuousOn_id fun t ht => by simp only [mem_Ici] at ht; linarith
      · exact (DifferentiableOn.div
          (Real.differentiable_exp.comp (differentiable_const _ |>.mul differentiable_id)).differentiableOn
          differentiableOn_id fun t ht => by
            have ht' : (1.802 : ℝ) ≤ t := interior_subset ht
            linarith)
      · intro t ht
        have ht0 : (1.802 : ℝ) < t := by simpa [interior_Ici] using ht
        have hd : HasDerivAt (fun s : ℝ => Real.exp (0.649 * s) / s)
            ((0.649 * Real.exp (0.649 * t) * t - Real.exp (0.649 * t) * 1) / t ^ 2) t := by
          refine HasDerivAt.div ?_ (hasDerivAt_id t) (by linarith)
          have he := (Real.hasDerivAt_exp (0.649 * t)).comp t ((hasDerivAt_id t).const_mul 0.649)
          exact he.congr_deriv (by ring)
        rw [hd.deriv]
        refine div_nonneg ?_ (sq_nonneg t)
        have hpos : 0 < Real.exp (0.649 * t) := Real.exp_pos _
        nlinarith
    exact hf (by norm_num : (1.802 : ℝ) ∈ Ici 1.802) hsqa_ge.le hsqa_ge.le
  -- Numerical evaluation at `1.802` via Taylor series of `exp`
  have hexp_num : (3.216 : ℝ) ≤ Real.exp (0.649 * 1.802) := by
    have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.649 * 1.802 by norm_num) 6
    norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
    linarith
  have hfinal : (0.72 : ℝ) < (1.215 / 3 : ℝ) * (Real.exp (0.649 * 1.802) / 1.802) := by
    have hnum : (0.72 : ℝ) < (1.215 / 3 : ℝ) * (3.216 / 1.802) := by norm_num
    have hle : (1.215 / 3 : ℝ) * (3.216 / 1.802) ≤
        (1.215 / 3 : ℝ) * (Real.exp (0.649 * 1.802) / 1.802) := by gcongr
    linarith
  linarith

/-! ### Section 3: Volume of the central region `E` -/

private noncomputable def spinS21Strip (a : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | 1 / 3 < |p.1| ∧ |p.2| ≤ (1 / 10 : ℝ) * Real.exp (-(π * Real.sqrt a / 2) * |p.1|)}

private lemma spinS21Strip_measurableSet (a : ℝ) : MeasurableSet (spinS21Strip a) := by
  have h1 : Measurable (fun p : ℝ × ℝ => |p.1|) := continuous_abs.comp continuous_fst |>.measurable
  have h2 : Measurable (fun p : ℝ × ℝ => |p.2|) := continuous_abs.comp continuous_snd |>.measurable
  have h3 : Measurable (fun p : ℝ × ℝ => (1 / 10 : ℝ) * Real.exp (-(π * Real.sqrt a / 2) * |p.1|)) :=
    measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul h1))
  exact (measurableSet_lt measurable_const h1).inter (measurableSet_le h2 h3)

private noncomputable def spinS21Region (a : ℝ) : Set (ℝ × ℝ) :=
  (Icc (-(1 / 3 : ℝ)) (1 / 3) ×ˢ Icc (-(1 / 3 : ℝ)) (1 / 3)) ∪
    spinS21Strip a ∪ Prod.swap ⁻¹' spinS21Strip a

private lemma integral_exp_neg_mul_Ioi_third {β : ℝ} (hβ : 0 < β) :
    IntegrableOn (fun x : ℝ => Real.exp (-β * x)) (Ioi (1 / 3 : ℝ)) ∧
      ∫ x in Ioi (1 / 3 : ℝ), Real.exp (-β * x) = Real.exp (-β / 3) / β := by
  have hderiv : ∀ x ∈ Ici (1 / 3 : ℝ),
      HasDerivAt (fun t : ℝ => -Real.exp (-β * t) / β) (Real.exp (-β * x)) x := by
    intro x _
    have he := (Real.hasDerivAt_exp (-β * x)).comp x ((hasDerivAt_id x).const_mul (-β))
    exact (he.neg.div_const β).congr_deriv (by field_simp [hβ.ne'])
  have htend : Tendsto (fun t : ℝ => -Real.exp (-β * t) / β) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => -β * t) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id
    have h2 : Tendsto (fun t : ℝ => Real.exp (-β * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h1
    simpa using (h2.neg.div_const β)
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-β * x)) (Ioi (1 / 3 : ℝ)) :=
    integrableOn_Ioi_of_intervalIntegral_norm_bounded (Real.exp (-β / 3) / β) (1 / 3)
      (fun t => (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      tendsto_id
      (Eventually.of_forall fun t => by
        simp_rw [Real.norm_of_nonneg (Real.exp_pos _).le, id_eq]
        by_cases ht : (1 / 3 : ℝ) ≤ t
        · have hfun : ∫ x in (1 / 3 : ℝ)..t, Real.exp (-β * x) =
              (-Real.exp (-β * t) / β) - (-Real.exp (-β * (1 / 3)) / β) :=
            intervalIntegral.integral_eq_sub_of_hasDerivAt
              (fun x hx => hderiv x (mem_Ici.mpr (by rw [uIcc_of_le ht] at hx; exact hx.1)))
              ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable (1 / 3) t)
          have heq : -Real.exp (-β * t) / β - -Real.exp (-β * (1 / 3)) / β =
              Real.exp (-β / 3) / β - Real.exp (-β * t) / β := by
            have : -β * (1 / 3 : ℝ) = -β / 3 := by ring
            rw [this]; ring
          rw [heq] at hfun
          rw [hfun]
          have hpos : 0 ≤ Real.exp (-β * t) / β := by positivity
          linarith
        · push Not at ht
          have hneg : ∫ x in (1 / 3 : ℝ)..t, Real.exp (-β * x) ≤ 0 := by
            rw [intervalIntegral.integral_symm]
            have : 0 ≤ ∫ x in t..(1 / 3 : ℝ), Real.exp (-β * x) :=
              intervalIntegral.integral_nonneg ht.le fun _ _ => (Real.exp_pos _).le
            linarith
          have hpos : 0 ≤ Real.exp (-β / 3) / β := by positivity
          linarith)
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  refine ⟨hint, ?_⟩
  rw [hval, zero_sub, neg_div, neg_neg]
  congr 2; ring

private lemma volume_spinS21Strip_eq {a : ℝ} (ha : 0 < a) :
    volume (spinS21Strip a) =
      ENNReal.ofReal ((0.4 : ℝ) * Real.exp (-(π * Real.sqrt a / 2) / 3) / (π * Real.sqrt a / 2)) := by
  set β : ℝ := π * Real.sqrt a / 2
  have hβ : 0 < β := by positivity
  have hmeas := spinS21Strip_measurableSet a
  have hvol_eq : volume (spinS21Strip a) =
      ∫⁻ x : ℝ, (volume {y : ℝ | 1 / 3 < |x| ∧ |y| ≤ (1 / 10 : ℝ) * Real.exp (-β * |x|)}) := by
    rw [Measure.volume_eq_prod, Measure.prod_apply hmeas]
    rfl
  have hinner : ∀ x : ℝ,
      volume {y : ℝ | 1 / 3 < |x| ∧ |y| ≤ (1 / 10 : ℝ) * Real.exp (-β * |x|)} =
        Set.indicator {x : ℝ | 1 / 3 < |x|}
          (fun x => ENNReal.ofReal ((0.2 : ℝ) * Real.exp (-β * |x|))) x := by
    intro x
    by_cases hx : 1 / 3 < |x|
    · have hmem : x ∈ {x : ℝ | 1 / 3 < |x|} := hx
      rw [Set.indicator_of_mem hmem]
      have hset : {y : ℝ | 1 / 3 < |x| ∧ |y| ≤ (1 / 10 : ℝ) * Real.exp (-β * |x|)} =
          Icc (-((1 / 10 : ℝ) * Real.exp (-β * |x|))) ((1 / 10 : ℝ) * Real.exp (-β * |x|)) := by
        ext y; simp only [mem_ofPred_eq, mem_Icc, abs_le]
        exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
      rw [hset, Real.volume_Icc]
      congr 1; ring
    · have hnmem : x ∉ {x : ℝ | 1 / 3 < |x|} := hx
      rw [Set.indicator_of_notMem hnmem]
      have hset : {y : ℝ | 1 / 3 < |x| ∧ |y| ≤ (1 / 10 : ℝ) * Real.exp (-β * |x|)} = ∅ := by
        ext y; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]; intro h; exact (hx h).elim
      rw [hset, measure_empty]
  have hlint_eq : (∫⁻ x : ℝ, Set.indicator {x : ℝ | 1 / 3 < |x|}
        (fun x => ENNReal.ofReal ((0.2 : ℝ) * Real.exp (-β * |x|))) x) =
      2 * ∫⁻ x in Ioi (1 / 3 : ℝ), ENNReal.ofReal ((0.2 : ℝ) * Real.exp (-β * x)) := by
    have hsplit : {x : ℝ | 1 / 3 < |x|} = Iio (-(1 / 3 : ℝ)) ∪ Ioi (1 / 3 : ℝ) := by
      ext x; simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi, lt_abs]
      constructor <;> rintro (h | h) <;> [right; left; right; left] <;> linarith
    have hdisj : Disjoint (Iio (-(1 / 3 : ℝ))) (Ioi (1 / 3 : ℝ)) := by
      rw [Set.disjoint_left]; intro x hx1 hx2; linarith [mem_Iio.mp hx1, mem_Ioi.mp hx2]
    rw [hsplit]
    have h1 : ∀ x : ℝ, (Iio (-(1 / 3 : ℝ)) ∪ Ioi (1 / 3 : ℝ)).indicator
          (fun x => ENNReal.ofReal ((0.2 : ℝ) * Real.exp (-β * |x|))) x =
        (Iio (-(1 / 3 : ℝ))).indicator (fun x => ENNReal.ofReal ((0.2 : ℝ) * Real.exp (-β * |x|))) x +
        (Ioi (1 / 3 : ℝ)).indicator (fun x => ENNReal.ofReal ((0.2 : ℝ) * Real.exp (-β * |x|))) x :=
      fun x => congrFun (Set.indicator_union_of_disjoint hdisj _) x
    simp_rw [h1]
    rw [lintegral_add_left]
    · have hleft : (∫⁻ x : ℝ, (Iio (-(1 / 3 : ℝ))).indicator
            (fun x => ENNReal.ofReal ((0.2 : ℝ) * Real.exp (-β * |x|))) x) =
          ∫⁻ x in Ioi (1 / 3 : ℝ), ENNReal.ofReal ((0.2 : ℝ) * Real.exp (-β * x)) := by
        rw [← lintegral_indicator measurableSet_Ioi]
        have hneg := lintegral_neg_eq_self (μ := (volume : Measure ℝ))
          (fun x => (Ioi (1 / 3 : ℝ)).indicator
            (fun x => ENNReal.ofReal ((0.2 : ℝ) * Real.exp (-β * x))) x)
        rw [← hneg]
        refine lintegral_congr (fun x => ?_)
        by_cases hx : x ∈ Iio (-(1 / 3 : ℝ))
        · have hnx : -x ∈ Ioi (1 / 3 : ℝ) := by simp only [mem_Iio] at hx; simp only [mem_Ioi]; linarith
          have hx0 : x ≤ 0 := by simp only [mem_Iio] at hx; linarith
          rw [Set.indicator_of_mem hx, Set.indicator_of_mem hnx, abs_of_nonpos hx0]
        · have hnx : -x ∉ Ioi (1 / 3 : ℝ) := by simp only [mem_Iio] at hx; simp only [mem_Ioi]; linarith
          rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hnx]
      have hright : (∫⁻ x : ℝ, (Ioi (1 / 3 : ℝ)).indicator
            (fun x => ENNReal.ofReal ((0.2 : ℝ) * Real.exp (-β * |x|))) x) =
          ∫⁻ x in Ioi (1 / 3 : ℝ), ENNReal.ofReal ((0.2 : ℝ) * Real.exp (-β * x)) := by
        rw [← lintegral_indicator measurableSet_Ioi]
        refine lintegral_congr (fun x => ?_)
        by_cases hx : x ∈ Ioi (1 / 3 : ℝ)
        · have hx0 : 0 ≤ x := by simp only [mem_Ioi] at hx; linarith
          rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, abs_of_nonneg hx0]
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      rw [hleft, hright, two_mul]
    · exact (measurable_const.mul (Real.measurable_exp.comp
        (measurable_const.mul continuous_abs.measurable))).ennreal_ofReal.indicator
        measurableSet_Iio
  obtain ⟨hint_base, hval_base⟩ := integral_exp_neg_mul_Ioi_third hβ
  have hint_exp : IntegrableOn (fun x : ℝ => (0.2 : ℝ) * Real.exp (-β * x)) (Ioi (1 / 3 : ℝ)) :=
    hint_base.const_mul _
  have hint_val : ∫ x in Ioi (1 / 3 : ℝ), (0.2 : ℝ) * Real.exp (-β * x) =
      (0.2 : ℝ) * (Real.exp (-β / 3) / β) := by
    rw [integral_const_mul, hval_base]
  have hofReal_int : ∫⁻ x in Ioi (1 / 3 : ℝ), ENNReal.ofReal ((0.2 : ℝ) * Real.exp (-β * x)) =
      ENNReal.ofReal ((0.2 : ℝ) * (Real.exp (-β / 3) / β)) := by
    rw [← hint_val, ofReal_integral_eq_lintegral_ofReal hint_exp (Eventually.of_forall fun _ => by positivity)]
  rw [hvol_eq]
  simp_rw [hinner]
  rw [hlint_eq, hofReal_int, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; ring

private lemma volume_real_spinS21Region_lt {a : ℝ} (ha : 13 / 4 ≤ a) :
    volume.real (spinS21Region a) < (0.555 : ℝ) := by
  have ha0 : 0 < a := by linarith
  set β : ℝ := π * Real.sqrt a / 2
  have hβ_ge : (2.83 : ℝ) ≤ β := by
    have hpi : (3.1415 : ℝ) < π := Real.pi_gt_d4
    have hsqa : (1.802 : ℝ) < Real.sqrt a := Real.lt_sqrt_of_sq_lt (by norm_num; linarith)
    dsimp [β]
    nlinarith
  have hstrip1_eq := volume_spinS21Strip_eq ha0
  have hswap : volume (Prod.swap ⁻¹' spinS21Strip a) = volume (spinS21Strip a) := by
    have hmp : Measure.map Prod.swap (volume : Measure (ℝ × ℝ)) = volume := by
      rw [Measure.volume_eq_prod, Measure.prod_swap]
    rw [← Measure.map_apply measurable_swap (spinS21Strip_measurableSet a), hmp]
  have hsq_eq : volume (Icc (-(1 / 3 : ℝ)) (1 / 3) ×ˢ Icc (-(1 / 3 : ℝ)) (1 / 3)) =
      ENNReal.ofReal (4 / 9 : ℝ) := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
      ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hvol_le : volume (spinS21Region a) ≤
      ENNReal.ofReal (4 / 9 : ℝ) +
        ENNReal.ofReal ((0.4 : ℝ) * Real.exp (-β / 3) / β) +
        ENNReal.ofReal ((0.4 : ℝ) * Real.exp (-β / 3) / β) := by
    unfold spinS21Region
    refine (measure_union_le _ _).trans ?_
    refine add_le_add ((measure_union_le _ _).trans ?_) ?_
    · rw [hsq_eq, hstrip1_eq]
    · rw [hswap, hstrip1_eq]
  have hreal_le : volume.real (spinS21Region a) ≤
      4 / 9 + 0.8 * Real.exp (-β / 3) / β := by
    rw [Measure.real_def]
    have hto : (volume (spinS21Region a)).toReal ≤
        (ENNReal.ofReal (4 / 9 + 0.8 * Real.exp (-β / 3) / β)).toReal := by
      refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
      refine hvol_le.trans ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
    exact hto.trans_eq (ENNReal.toReal_ofReal (by positivity))
  -- Numerical bound: `4/9 + 0.8 * exp(-2.83 / 3) / 2.83 < 0.555`
  have hexp_ge : (2.561 : ℝ) ≤ Real.exp (2.83 / 3) := by
    have hsum := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 2.83 / 3 by norm_num) 5
    norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
    linarith
  have hexp_le : Real.exp (-β / 3) ≤ (2.561 : ℝ)⁻¹ := by
    have h1 : Real.exp (-β / 3) ≤ Real.exp (-(2.83 / 3)) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg] at h1
    exact h1.trans (inv_anti₀ (by norm_num) hexp_ge)
  have hdiv_le : 0.8 * Real.exp (-β / 3) / β ≤ 0.8 * (2.561 : ℝ)⁻¹ / 2.83 := by
    have h1 : 0.8 * Real.exp (-β / 3) ≤ 0.8 * (2.561 : ℝ)⁻¹ := by linarith
    exact div_le_div₀ (by positivity) h1 (by norm_num) hβ_ge
  linarith

/-! ### Section 4: Proof of `SpinS21` -/

theorem spinS21 : SpinS21 := by
  intro c hc Φ hΦ
  refine ⟨spinTestClass_abs_le_integral_abs hΦ, ?_⟩
  set a : ℝ := (c - 1) / 12
  have ha : 13 / 4 ≤ a := by dsimp [a]; linarith
  have ha2 : 2 ≤ a := by linarith
  set E : Set (ℝ × ℝ) := spinS21Region a
  have hE_meas : MeasurableSet E := by
    unfold E spinS21Region
    exact ((measurableSet_Icc.prod measurableSet_Icc).union (spinS21Strip_measurableSet a)).union
      (measurable_swap (spinS21Strip_measurableSet a))
  -- Pointwise lower bound `0.72 < V_1(r_L) V_1(r_R)` on `Eᶜ`
  have hoffE : ∀ p ∈ Eᶜ, (0.72 : ℝ) < spinV1 a p.1 * spinV1 a p.2 := by
    intro p hp
    simp only [E, mem_compl_iff, spinS21Region, mem_union, mem_prod, mem_Icc, not_or] at hp
    rcases hp with ⟨⟨hnot_sq, hnot_s1⟩, hnot_s2⟩
    have hV1_even : ∀ r, spinV1 a |r| = spinV1 a r := fun r => by
      rcases le_total 0 r with hr | hr
      · rw [abs_of_nonneg hr]
      · rw [abs_of_nonpos hr, spinV1_even]
    rw [← hV1_even p.1, ← hV1_even p.2]
    rcases le_total |p.1| |p.2| with hle | hle
    · rw [mul_comm]
      have hp2 : 1 / 3 < |p.2| := by
        by_contra hcon
        push Not at hcon
        exact hnot_sq ⟨abs_le.mp (hle.trans hcon), abs_le.mp hcon⟩
      have hp1 : (1 / 10 : ℝ) * Real.exp (-(π * Real.sqrt a / 2) * |p.2|) < |p.1| := by
        by_contra hcon
        push Not at hcon
        exact hnot_s2 ⟨hp2, hcon⟩
      exact spinV1_prod_ge_off_E ha hp2 hp1
    · have hp1 : 1 / 3 < |p.1| := by
        by_contra hcon
        push Not at hcon
        exact hnot_sq ⟨abs_le.mp hcon, abs_le.mp (hle.trans hcon)⟩
      have hp2 : (1 / 10 : ℝ) * Real.exp (-(π * Real.sqrt a / 2) * |p.1|) < |p.2| := by
        by_contra hcon
        push Not at hcon
        exact hnot_s1 ⟨hp1, hcon⟩
      exact spinV1_prod_ge_off_E ha hp1 hp2
  -- Split `∫ |Φ|` over `E` and `Eᶜ`
  have hint_abs : Integrable (fun q : ℝ × ℝ => |Φ q|) := hΦ.int.abs
  have hsplit : (∫ q : ℝ × ℝ, |Φ q|) = (∫ q in E, |Φ q|) + ∫ q in Eᶜ, |Φ q| :=
    (integral_add_compl hE_meas hint_abs).symm
  have hbound_E : ∫ q in E, |Φ q| ≤ (0.555 : ℝ) * ∫ q : ℝ × ℝ, |Φ q| := by
    have h1 : ∫ q in E, |Φ q| ≤ ∫ _ in E, (∫ q : ℝ × ℝ, |Φ q|) := by
      refine setIntegral_mono_on hint_abs.integrableOn ?_ hE_meas fun q _ =>
        spinTestClass_abs_le_integral_abs hΦ q
      have hfin : volume E < ⊤ := by
        have h1 : volume (Icc (-(1 / 3 : ℝ)) (1 / 3) ×ˢ Icc (-(1 / 3 : ℝ)) (1 / 3)) < ⊤ := by
          rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
        have h2 : volume (spinS21Strip a) < ⊤ := by
          rw [volume_spinS21Strip_eq (by linarith)]
          exact ENNReal.ofReal_lt_top
        have h3 : volume (Prod.swap ⁻¹' spinS21Strip a) < ⊤ := by
          have hmp : Measure.map Prod.swap (volume : Measure (ℝ × ℝ)) = volume := by
            rw [Measure.volume_eq_prod, Measure.prod_swap]
          rw [← Measure.map_apply measurable_swap (spinS21Strip_measurableSet a), hmp]
          exact h2
        exact measure_union_lt_top (measure_union_lt_top h1 h2) h3
      exact integrableOn_const (hs := hfin.ne)
    rw [setIntegral_const, smul_eq_mul] at h1
    have hnn : 0 ≤ ∫ q : ℝ × ℝ, |Φ q| := integral_nonneg fun _ => abs_nonneg _
    exact h1.trans (mul_le_mul_of_nonneg_right (volume_real_spinS21Region_lt ha).le hnn)
  have hbound_Ec : ∫ q in Eᶜ, |Φ q| ≤ (1 / 0.72 : ℝ) * spinM2 a Φ := by
    have h1 : ∫ q in Eᶜ, |Φ q| ≤ ∫ q in Eᶜ, (1 / 0.72 : ℝ) * (|Φ q| * spinV1 a q.1 * spinV1 a q.2) := by
      refine setIntegral_mono_on hint_abs.integrableOn (hΦ.int_M2.const_mul _).integrableOn
        hE_meas.compl fun q hq => ?_
      have hq_gt : (0.72 : ℝ) < spinV1 a q.1 * spinV1 a q.2 := hoffE q hq
      have hle : |Φ q| ≤ (1 / 0.72 : ℝ) * (|Φ q| * (spinV1 a q.1 * spinV1 a q.2)) := by
        have hnn : 0 ≤ |Φ q| := abs_nonneg _
        nlinarith
      linarith [show (1 / 0.72 : ℝ) * (|Φ q| * spinV1 a q.1 * spinV1 a q.2) =
        (1 / 0.72 : ℝ) * (|Φ q| * (spinV1 a q.1 * spinV1 a q.2)) by ring]
    rw [integral_const_mul] at h1
    have h2 : ∫ q in Eᶜ, |Φ q| * spinV1 a q.1 * spinV1 a q.2 ≤ spinM2 a Φ :=
      setIntegral_le_integral hΦ.int_M2 (Eventually.of_forall fun q =>
        mul_nonneg (mul_nonneg (abs_nonneg _) (spinV1_nonneg ha2 q.1)) (spinV1_nonneg ha2 q.2))
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have hM2_nn : 0 ≤ spinM2 a Φ := spinM2_nonneg ha2 Φ
  linarith

/-! ### Axiom check -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS21' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS21

end FormalResearch.ModularBootstrap.Spin
