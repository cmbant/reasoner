module

public import FormalResearch.SignUncertainty.CeGauss2

/-!
# Closed-form twisted transforms of `F_*` and `g₁` (`uct:airy-trans` (1), F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:airy-trans` (1) (`(uct:Fstar-int)`, `(uct:g1-int)`).

With `f₁ = Ai²/(u - a₁)` (`ceF1`), `F_* = -f₁`, `g₁ = Ai²/(u - a₁)²` (`ceG1 (airyZero 1)`) and `X̃(i w) = airyTwistedLaplaceC X w`
(`k e^{-w³/12} ∫ X e^{w u} du`), the entire functions
`E(w) = ½ e^{a₁w - w³/12} ∫₀¹ t^{-1/2} e^{ψ(wt)} dt`, `E₁(w) = e^{a₁w - w³/12}`, `E₂(w) = ½ e^{a₁w - w³/12} ∫₀¹ (1-t) t^{-1/2} e^{ψ(wt)} dt`
(`ψ(s) = -a₁ s + s³/12`) satisfy, for `Re w ≥ 0`,
`f̃₁(i w) = (k/√π) w^{1/2} E(w)` and `g̃₁(i w) = k E₁(w) + (k/√π) w^{3/2} E₂(w)`.

Contents: the entire functions and their values at the origin (`uctE_differentiable`, `uctE_zero`, `deriv_uctE_zero`, ...),
the Fubini lemma `airySq_fubini` (with `ceo:O11n.7` = `airy_pair_laplace_eq`), and the closed forms
`airyTwistedLaplaceC_ceF1_closed`, `airyTwistedLaplaceC_ceG1_closed` (proved on `Re w > 0` by Fubini and the identities
`(u - a₁) f₁ = Ai²`, `(u - a₁) g₁ = f₁`, `∫ f₁ = 0`, `∫ g₁ = 1`, and on `Re w = 0` by continuity).

Class: proved.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- `a₁ = airyZero 1`, as a complex number. -/
noncomputable def uctA1 : ℂ := ((airyZero 1 : ℝ) : ℂ)

/-- The exponent `ψ(s) = -a₁ s + s³/12` of `uct:airy-trans`. -/
noncomputable def uctPsi (s : ℂ) : ℂ := -(uctA1 * s) + s ^ 3 / 12

/-- `∫₀¹ κ(t) e^{ψ(w t)} dt`. -/
noncomputable def uctWI (κ : ℝ → ℂ) (w : ℂ) : ℂ :=
  ∫ t in Ioc (0 : ℝ) 1, κ t * cexp (uctPsi (w * (t : ℂ)))

/-- The weight `t^{-1/2}`. -/
noncomputable def uctKap (t : ℝ) : ℂ := (t : ℂ) ^ (-(1 / 2 : ℂ))

/-- The weight `(1 - t) t^{-1/2}`. -/
noncomputable def uctKap1 (t : ℝ) : ℂ := ((1 - t : ℝ) : ℂ) * (t : ℂ) ^ (-(1 / 2 : ℂ))

/-- `E(w) = ½ e^{a₁w - w³/12} ∫₀¹ t^{-1/2} e^{-a₁ w t + w³t³/12} dt` (`(uct:Fstar-int)`). -/
noncomputable def uctE (w : ℂ) : ℂ := (1 / 2) * cexp (uctA1 * w - w ^ 3 / 12) * uctWI uctKap w

/-- `E₁(w) = e^{a₁w - w³/12}` (`(uct:g1-int)`). -/
noncomputable def uctE1 (w : ℂ) : ℂ := cexp (uctA1 * w - w ^ 3 / 12)

/-- `E₂(w) = ½ e^{a₁w - w³/12} ∫₀¹ (1-t) t^{-1/2} e^{-a₁ w t + w³t³/12} dt` (`(uct:g1-int)`). -/
noncomputable def uctE2 (w : ℂ) : ℂ := (1 / 2) * cexp (uctA1 * w - w ^ 3 / 12) * uctWI uctKap1 w

lemma norm_uctPsi_le (s : ℂ) : ‖uctPsi s‖ ≤ ‖uctA1‖ * ‖s‖ + ‖s‖ ^ 3 / 12 := by
  unfold uctPsi
  calc ‖-(uctA1 * s) + s ^ 3 / 12‖ ≤ ‖-(uctA1 * s)‖ + ‖s ^ 3 / 12‖ := norm_add_le _ _
    _ = _ := by rw [norm_neg, norm_mul, norm_div, norm_pow]; simp

lemma hasDerivAt_uctPsi_mul (t : ℂ) (w : ℂ) :
    HasDerivAt (fun w : ℂ => uctPsi (w * t)) (-(uctA1 * t) + w ^ 2 * t ^ 3 / 4) w := by
  unfold uctPsi
  have h1 : HasDerivAt (fun w : ℂ => w * t) t w := by simpa using (hasDerivAt_id w).mul_const t
  have h2 := ((h1.const_mul uctA1).neg).add ((h1.pow 3).div_const 12)
  convert h2 using 1
  simp; ring

lemma norm_exp_uctPsi_le {w t : ℂ} {R : ℝ} (h : ‖w * t‖ ≤ R) :
    ‖cexp (uctPsi (w * t))‖ ≤ Real.exp (‖uctA1‖ * R + R ^ 3 / 12) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ((norm_uctPsi_le _).trans ?_))
  have hn0 : 0 ≤ ‖w * t‖ := norm_nonneg _
  have h3 : ‖w * t‖ ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ hn0 h 3
  nlinarith [norm_nonneg uctA1]

lemma uctWI_hasDerivAt {κ : ℝ → ℂ} (hκ : IntegrableOn κ (Ioc 0 1)) (w₀ : ℂ) :
    HasDerivAt (uctWI κ)
      (∫ t in Ioc (0 : ℝ) 1, κ t * cexp (uctPsi (w₀ * (t : ℂ))) * (-(uctA1 * (t : ℂ)) + w₀ ^ 2 * (t : ℂ) ^ 3 / 4)) w₀ := by
  set R : ℝ := ‖w₀‖ + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  set Bd : ℝ := Real.exp (‖uctA1‖ * R + R ^ 3 / 12) * (‖uctA1‖ + R ^ 2 / 4) with hBd
  have hmeasF : ∀ w : ℂ, AEStronglyMeasurable (fun t : ℝ => κ t * cexp (uctPsi (w * (t : ℂ)))) (volume.restrict (Ioc (0:ℝ) 1)) := by
    intro w
    refine hκ.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_)
    unfold uctPsi; fun_prop
  have hnt : ∀ {w : ℂ}, ‖w‖ ≤ R → ∀ {t : ℝ}, t ∈ Ioc (0:ℝ) 1 → ‖w * (t : ℂ)‖ ≤ R := by
    intro w hw t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
    calc ‖w‖ * t ≤ ‖w‖ * 1 := by gcongr; exact ht.2
      _ ≤ R := by rw [mul_one]; exact hw
  have hw0 : ‖w₀‖ ≤ R := by rw [hR]; linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioc (0:ℝ) 1))
    (F := fun w t => κ t * cexp (uctPsi (w * (t : ℂ))))
    (F' := fun w t => κ t * cexp (uctPsi (w * (t : ℂ))) * (-(uctA1 * (t : ℂ)) + w ^ 2 * (t : ℂ) ^ 3 / 4))
    (x₀ := w₀) (s := Metric.ball w₀ 1) (bound := fun t => ‖κ t‖ * Bd) (Metric.ball_mem_nhds w₀ one_pos)
    (Eventually.of_forall hmeasF) ?_ ?_ ?_ ?_ ?_
  · exact key.2
  · refine (hκ.norm.mul_const (Real.exp (‖uctA1‖ * R + R ^ 3 / 12))).mono' (hmeasF w₀) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_exp_uctPsi_le (hnt hw0 ht)) (norm_nonneg _)
  · refine (hmeasF w₀).mul (Continuous.aestronglyMeasurable ?_)
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht w hw
    have hwR : ‖w‖ ≤ R := by
      have : ‖w - w₀‖ < 1 := by simpa [Complex.dist_eq] using Metric.mem_ball.mp hw
      calc ‖w‖ = ‖(w - w₀) + w₀‖ := by ring_nf
        _ ≤ ‖w - w₀‖ + ‖w₀‖ := norm_add_le _ _
        _ ≤ R := by rw [hR]; linarith
    have hp : ‖-(uctA1 * (t : ℂ)) + w ^ 2 * (t : ℂ) ^ 3 / 4‖ ≤ ‖uctA1‖ + R ^ 2 / 4 := by
      have ht0 : (0:ℝ) < t := ht.1
      have ht1 : t ≤ 1 := ht.2
      calc ‖-(uctA1 * (t : ℂ)) + w ^ 2 * (t : ℂ) ^ 3 / 4‖ ≤ ‖-(uctA1 * (t : ℂ))‖ + ‖w ^ 2 * (t : ℂ) ^ 3 / 4‖ := norm_add_le _ _
        _ = ‖uctA1‖ * t + ‖w‖ ^ 2 * t ^ 3 / 4 := by
          rw [norm_neg, norm_mul, norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; simp
        _ ≤ ‖uctA1‖ * 1 + R ^ 2 * 1 / 4 := by
          have h1 : ‖w‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwR 2
          have h2 : t ^ 3 ≤ 1 := pow_le_one₀ ht0.le ht1
          have : ‖w‖ ^ 2 * t ^ 3 ≤ R ^ 2 * 1 := mul_le_mul h1 h2 (by positivity) (by positivity)
          nlinarith [norm_nonneg uctA1]
        _ = _ := by ring
    rw [norm_mul, norm_mul]
    calc ‖κ t‖ * ‖cexp (uctPsi (w * (t : ℂ)))‖ * ‖-(uctA1 * (t : ℂ)) + w ^ 2 * (t : ℂ) ^ 3 / 4‖
        ≤ ‖κ t‖ * Real.exp (‖uctA1‖ * R + R ^ 3 / 12) * (‖uctA1‖ + R ^ 2 / 4) := by
          gcongr
          exact norm_exp_uctPsi_le (hnt hwR ht)
      _ = ‖κ t‖ * Bd := by rw [hBd]; ring
  · exact hκ.norm.mul_const Bd
  · exact Eventually.of_forall fun t w _ =>
      (((hasDerivAt_uctPsi_mul (t : ℂ) w).cexp).const_mul (κ t)).congr_deriv (by ring)

lemma uctWI_differentiable {κ : ℝ → ℂ} (hκ : IntegrableOn κ (Ioc 0 1)) : Differentiable ℂ (uctWI κ) :=
  fun w => (uctWI_hasDerivAt hκ w).differentiableAt

lemma integrableOn_uctKap : IntegrableOn uctKap (Ioc (0 : ℝ) 1) := by
  have hm : Measurable uctKap := by unfold uctKap; fun_prop
  have h : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
  refine h.mono' hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  unfold uctKap
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
  norm_num

lemma integrableOn_uctKap1 : IntegrableOn uctKap1 (Ioc (0 : ℝ) 1) := by
  have hm : Measurable uctKap1 := by unfold uctKap1; fun_prop
  refine integrableOn_uctKap.norm.mono' hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  unfold uctKap1
  rw [norm_mul]
  have h1 : ‖((1 - t : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]; linarith [ht.1]
  calc ‖((1 - t : ℝ) : ℂ)‖ * ‖(t : ℂ) ^ (-(1 / 2 : ℂ))‖ ≤ 1 * ‖(t : ℂ) ^ (-(1 / 2 : ℂ))‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖uctKap t‖ := by rw [one_mul]; rfl

theorem uctE_differentiable : Differentiable ℂ uctE := by
  unfold uctE
  exact ((((differentiable_const _).mul differentiable_id).sub ((differentiable_id.pow 3).div_const 12)).cexp.const_mul
    (1 / 2 : ℂ)).mul (uctWI_differentiable integrableOn_uctKap)

theorem uctE1_differentiable : Differentiable ℂ uctE1 := by
  unfold uctE1
  exact (((differentiable_const _).mul differentiable_id).sub ((differentiable_id.pow 3).div_const 12)).cexp

theorem uctE2_differentiable : Differentiable ℂ uctE2 := by
  unfold uctE2
  exact ((((differentiable_const _).mul differentiable_id).sub ((differentiable_id.pow 3).div_const 12)).cexp.const_mul
    (1 / 2 : ℂ)).mul (uctWI_differentiable integrableOn_uctKap1)

/-! ### Values at the origin -/

lemma integral_Ioc_rpow_complex (r : ℝ) (hr : -1 < r) :
    ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (r : ℂ) = ((1 / (r + 1) : ℝ) : ℂ) := by
  have h1 : ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (r : ℂ) = ∫ t in Ioc (0 : ℝ) 1, ((t ^ r : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [Complex.ofReal_cpow ht.1.le]
  rw [h1, integral_complex_ofReal, ← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hr)]
  rw [Real.one_rpow, Real.zero_rpow (by linarith), sub_zero]

lemma uctKap_eq {t : ℝ} (ht : 0 < t) : uctKap t = ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  unfold uctKap
  rw [Complex.ofReal_cpow ht.le]; push_cast; rfl

lemma uctKap_mul_t {t : ℝ} (ht : 0 < t) : uctKap t * (t : ℂ) = (t : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by
  unfold uctKap
  have h : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  calc (t : ℂ) ^ (-(1 / 2 : ℂ)) * (t : ℂ) = (t : ℂ) ^ (-(1 / 2 : ℂ)) * (t : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
    _ = (t : ℂ) ^ (-(1 / 2 : ℂ) + 1) := (Complex.cpow_add _ _ h).symm
    _ = _ := by congr 1; push_cast; ring

lemma uctWI_kap_zero : uctWI uctKap 0 = 2 := by
  unfold uctWI
  have : ∀ t ∈ Ioc (0:ℝ) 1, uctKap t * cexp (uctPsi (0 * (t : ℂ))) = (t : ℂ) ^ ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by
    intro t ht
    simp [uctPsi, uctKap]
  rw [setIntegral_congr_fun measurableSet_Ioc this, integral_Ioc_rpow_complex _ (by norm_num)]
  norm_num

lemma uctWI_kap_deriv_zero :
    ∫ t in Ioc (0 : ℝ) 1, uctKap t * cexp (uctPsi ((0 : ℂ) * (t : ℂ))) * (-(uctA1 * (t : ℂ)) + (0 : ℂ) ^ 2 * (t : ℂ) ^ 3 / 4) = -(uctA1 * (2 / 3)) := by
  have : ∀ t ∈ Ioc (0:ℝ) 1, uctKap t * cexp (uctPsi ((0:ℂ) * (t : ℂ))) * (-(uctA1 * (t : ℂ)) + (0 : ℂ) ^ 2 * (t : ℂ) ^ 3 / 4)
      = -uctA1 * (t : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by
    intro t ht
    have h := uctKap_mul_t ht.1
    have e : uctPsi ((0 : ℂ) * (t : ℂ)) = 0 := by simp [uctPsi]
    rw [e, Complex.exp_zero]
    calc uctKap t * 1 * (-(uctA1 * (t : ℂ)) + (0 : ℂ) ^ 2 * (t : ℂ) ^ 3 / 4) = -uctA1 * (uctKap t * (t : ℂ)) := by ring
      _ = _ := by rw [h]
  rw [setIntegral_congr_fun measurableSet_Ioc this, integral_const_mul, integral_Ioc_rpow_complex _ (by norm_num)]
  push_cast; norm_num

lemma uctWI_kap1_zero : uctWI uctKap1 0 = 4 / 3 := by
  unfold uctWI
  have : ∀ t ∈ Ioc (0:ℝ) 1, uctKap1 t * cexp (uctPsi (0 * (t : ℂ))) =
      (((t ^ (-(1 / 2 : ℝ)) - t ^ (1 / 2 : ℝ) : ℝ)) : ℂ) := by
    intro t ht
    have e : uctPsi (0 * (t : ℂ)) = 0 := by simp [uctPsi]
    rw [e, Complex.exp_zero, mul_one]
    unfold uctKap1
    have h1 : (t : ℂ) ^ (-(1 / 2 : ℂ)) = ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow ht.1.le]; push_cast; rfl
    have h2 : t * t ^ (-(1 / 2 : ℝ)) = t ^ (1 / 2 : ℝ) := by
      have := Real.rpow_add ht.1 (1 : ℝ) (-(1 / 2 : ℝ))
      rw [Real.rpow_one, show (1 : ℝ) + -(1 / 2 : ℝ) = 1 / 2 by norm_num] at this
      rw [← this]
    rw [h1]
    rw [show (((1 - t : ℝ)) : ℂ) * ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = (((1 - t) * t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) by push_cast; ring]
    congr 1
    rw [sub_mul, one_mul, h2]
  rw [setIntegral_congr_fun measurableSet_Ioc this, integral_complex_ofReal, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_rpow' (by norm_num)) (intervalIntegral.intervalIntegrable_rpow' (by norm_num)),
    integral_rpow (Or.inl (by norm_num)), integral_rpow (Or.inl (by norm_num))]
  rw [Real.one_rpow, Real.one_rpow, Real.zero_rpow (by norm_num), Real.zero_rpow (by norm_num)]
  push_cast; norm_num

theorem uctE_zero : uctE 0 = 1 := by
  unfold uctE; rw [uctWI_kap_zero]; simp

theorem uctE1_zero : uctE1 0 = 1 := by simp [uctE1]

theorem uctE2_zero : uctE2 0 = 2 / 3 := by
  unfold uctE2; rw [uctWI_kap1_zero]; simp; norm_num

lemma hasDerivAt_uctG (w : ℂ) :
    HasDerivAt (fun w : ℂ => cexp (uctA1 * w - w ^ 3 / 12)) (cexp (uctA1 * w - w ^ 3 / 12) * (uctA1 - w ^ 2 / 4)) w := by
  have a : HasDerivAt (fun w : ℂ => uctA1 * w) uctA1 w := by simpa using (hasDerivAt_id w).const_mul uctA1
  have b : HasDerivAt (fun w : ℂ => w ^ 3 / 12) (w ^ 2 / 4) w := by
    have := (hasDerivAt_pow 3 w).div_const 12
    convert this using 1; push_cast; ring
  exact (a.sub b).cexp

theorem hasDerivAt_uctE1_zero : HasDerivAt uctE1 uctA1 0 := by
  unfold uctE1
  convert hasDerivAt_uctG 0 using 1
  simp

theorem hasDerivAt_uctE_zero : HasDerivAt uctE (2 / 3 * uctA1) 0 := by
  unfold uctE
  have hg := (hasDerivAt_uctG 0).const_mul (1 / 2 : ℂ)
  have hw := uctWI_hasDerivAt integrableOn_uctKap (0 : ℂ)
  have h := hg.mul hw
  rw [uctWI_kap_deriv_zero] at h
  convert h using 1
  simp [uctWI_kap_zero]
  ring

/-! ### The Fubini lemma -/

lemma airySq_real_laplace {s : ℝ} (hs : 0 < s) :
    Integrable (fun u : ℝ => airyAi u ^ 2 * Real.exp (s * u)) ∧
      ∫ u : ℝ, airyAi u ^ 2 * Real.exp (s * u) = (4 * π * s) ^ (-(1 / 2 : ℝ)) * Real.exp (s ^ 3 / 12) := by
  have h := airy_pair_laplace_eq 0 0 (y := (s : ℂ)) (by simpa using hs)
  have hf : ∀ u : ℝ, (airyAi (u + 0) : ℂ) * (airyAi (u + 0) : ℂ) * Complex.exp ((s : ℂ) * (u : ℂ)) =
      ((airyAi u ^ 2 * Real.exp (s * u) : ℝ) : ℂ) := fun u => by
    simp only [add_zero, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp]; ring
  simp_rw [hf] at h
  obtain ⟨hi, hv⟩ := h
  refine ⟨?_, ?_⟩
  · refine hi.norm.congr (ae_of_all _ fun u => ?_)
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  · rw [integral_complex_ofReal] at hv
    have h1 : ((4 * π * s : ℝ) : ℂ) = 4 * (π : ℂ) * (s : ℂ) := by push_cast; ring
    have h2 : (((4 * π * s : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (s ^ 3 / 12) : ℝ) : ℂ) =
        (4 * (π : ℂ) * (s : ℂ)) ^ (-(1 / 2 : ℂ)) * Complex.exp ((s : ℂ) ^ 3 / 12 - (s : ℂ) * (((0 + 0 : ℝ)) : ℂ) / 2 - (((0 - 0 : ℝ)) : ℂ) ^ 2 / (4 * (s : ℂ))) := by
      push_cast
      rw [← h1, Complex.ofReal_cpow (by positivity)]
      simp
    exact_mod_cast hv.trans h2.symm
lemma airySq_complex_laplace {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun u : ℝ => (airyAi u : ℂ) ^ 2 * cexp (z * (u : ℂ))) ∧
      ∫ u : ℝ, (airyAi u : ℂ) ^ 2 * cexp (z * (u : ℂ)) = (4 * (π : ℂ) * z) ^ (-(1 / 2 : ℂ)) * cexp (z ^ 3 / 12) := by
  obtain ⟨hi, hv⟩ := airy_pair_laplace_eq 0 0 hz
  have hf : ∀ u : ℝ, (airyAi (u + 0) : ℂ) * (airyAi (u + 0) : ℂ) * cexp (z * (u : ℂ)) =
      (airyAi u : ℂ) ^ 2 * cexp (z * (u : ℂ)) := fun u => by simp [sq]
  simp_rw [hf] at hi hv
  refine ⟨hi, hv.trans ?_⟩
  simp

lemma airySq_fubini {ω : ℝ → ℝ} (hωc : Continuous ω) (hω : ∀ t ∈ Ioc (0 : ℝ) 1, |ω t| ≤ 1) {y : ℂ} (hy : 0 < y.re) :
    ∫ u : ℝ, (airyAi u : ℂ) ^ 2 * ∫ t in Ioc (0 : ℝ) 1, (ω t : ℂ) * cexp (((u : ℂ) - uctA1) * y * (t : ℂ)) =
      ∫ t in Ioc (0 : ℝ) 1, (ω t : ℂ) * (cexp (-(uctA1 * y * (t : ℂ))) *
        ((4 * (π : ℂ) * (y * (t : ℂ))) ^ (-(1 / 2 : ℂ)) * cexp ((y * (t : ℂ)) ^ 3 / 12))) := by
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hν
  let f : ℝ → ℝ → ℂ := fun u t => (airyAi u : ℂ) ^ 2 * ((ω t : ℂ) * cexp (((u : ℂ) - uctA1) * y * (t : ℂ)))
  have hcont : Continuous (Function.uncurry f) := by
    unfold Function.uncurry f
    have h1 : Continuous fun p : ℝ × ℝ => (airyAi p.1 : ℂ) := Complex.continuous_ofReal.comp (continuous_airyAi.comp continuous_fst)
    have h2 : Continuous fun p : ℝ × ℝ => (ω p.2 : ℂ) := Complex.continuous_ofReal.comp (hωc.comp continuous_snd)
    have h3 : Continuous fun p : ℝ × ℝ => cexp (((p.1 : ℂ) - uctA1) * y * (p.2 : ℂ)) := by
      refine Complex.continuous_exp.comp ?_
      have := Complex.continuous_ofReal.comp (continuous_fst : Continuous fun p : ℝ × ℝ => p.1)
      have h4 := Complex.continuous_ofReal.comp (continuous_snd : Continuous fun p : ℝ × ℝ => p.2)
      exact ((this.sub continuous_const).mul continuous_const).mul h4
    exact (h1.pow 2).mul (h2.mul h3)
  have hcexp : ∀ (t : ℝ) (u : ℝ), cexp (((u : ℂ) - uctA1) * y * (t : ℂ)) = cexp (-(uctA1 * y * (t : ℂ))) * cexp ((y * (t : ℂ)) * (u : ℂ)) := by
    intro t u; rw [← Complex.exp_add]; congr 1; ring
  have hfun : ∀ t : ℝ, (fun u : ℝ => f u t) = fun u => ((ω t : ℂ) * cexp (-(uctA1 * y * (t : ℂ)))) * ((airyAi u : ℂ) ^ 2 * cexp ((y * (t : ℂ)) * (u : ℂ))) := by
    intro t; funext u; simp only [f, hcexp]; ring
  have hre : ∀ {t : ℝ}, t ∈ Ioc (0 : ℝ) 1 → 0 < (y * (t : ℂ)).re := by
    intro t ht; simp [Complex.mul_re]; exact mul_pos hy ht.1
  have hint : Integrable (Function.uncurry f) (volume.prod ν) := by
    rw [integrable_prod_iff' hcont.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simp only [Function.uncurry_apply_pair]
      rw [hfun t]
      exact (airySq_complex_laplace (hre ht)).1.const_mul _
    · set ρ : ℝ := y.re with hρ
      have hρ0 : 0 < ρ := hy
      set Cc : ℝ := Real.exp (|airyZero 1| * ρ) * ((4 * π * ρ) ^ (-(1 / 2 : ℝ)) * Real.exp (ρ ^ 3 / 12)) with hCc
      have hGint : IntegrableOn (fun t : ℝ => Cc * t ^ (-(1 / 2 : ℝ))) (Ioc (0 : ℝ) 1) := by
        have h : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) volume 0 1 :=
          intervalIntegral.intervalIntegrable_rpow' (by norm_num)
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
        exact h.const_mul Cc
      have hmeas : AEStronglyMeasurable (fun t : ℝ => ∫ u : ℝ, ‖Function.uncurry f (u, t)‖ ∂volume) ν :=
        (hcont.aestronglyMeasurable.norm).prod_swap.integral_prod_right'
      refine hGint.mono' hmeas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simp only [Function.uncurry_apply_pair]
      have ht0 : 0 < t := ht.1
      have hs : 0 < ρ * t := mul_pos hρ0 ht.1
      obtain ⟨hAi, hAv⟩ := airySq_real_laplace hs
      have hnorm : ∀ u : ℝ, ‖f u t‖ = ‖(ω t : ℂ) * cexp (-(uctA1 * y * (t : ℂ)))‖ * (airyAi u ^ 2 * Real.exp ((ρ * t) * u)) := by
        intro u
        have := congrFun (hfun t) u
        rw [this, norm_mul]
        congr 1
        rw [norm_mul, Complex.norm_exp]
        simp [Complex.norm_real, Complex.mul_re, ρ]
      have hcn : ‖(ω t : ℂ) * cexp (-(uctA1 * y * (t : ℂ)))‖ ≤ Real.exp (|airyZero 1| * ρ) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
        have h1 : |ω t| ≤ 1 := hω t ht
        have h2 : (-(uctA1 * y * (t : ℂ))).re ≤ |airyZero 1| * ρ := by
          simp [uctA1, Complex.mul_re, ρ]
          have : airyZero 1 * (y.re * t) ≥ -(|airyZero 1| * ρ) := by
            have h3 : |airyZero 1| * (ρ * t) ≤ |airyZero 1| * ρ := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); nlinarith [ht.2, hρ0]
            nlinarith [neg_abs_le (airyZero 1), abs_nonneg (airyZero 1), mul_pos hρ0 ht.1, abs_mul (airyZero 1) (ρ * t), abs_of_pos (mul_pos hρ0 ht.1), le_abs_self (airyZero 1 * (ρ * t)), neg_abs_le (airyZero 1 * (ρ * t))]
          linarith
        calc |ω t| * Real.exp (-(uctA1 * y * (t : ℂ))).re ≤ 1 * Real.exp (|airyZero 1| * ρ) :=
              mul_le_mul h1 (Real.exp_le_exp.mpr h2) (Real.exp_pos _).le zero_le_one
          _ = _ := one_mul _
      have hI : ∫ u : ℝ, ‖f u t‖ = ‖(ω t : ℂ) * cexp (-(uctA1 * y * (t : ℂ)))‖ * ((4 * π * (ρ * t)) ^ (-(1 / 2 : ℝ)) * Real.exp ((ρ * t) ^ 3 / 12)) := by
        simp_rw [hnorm]; rw [integral_const_mul, hAv]
      rw [hI, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hp : (4 * π * (ρ * t)) ^ (-(1 / 2 : ℝ)) = (4 * π * ρ) ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 2 : ℝ)) := by
        rw [show 4 * π * (ρ * t) = (4 * π * ρ) * t by ring]
        exact Real.mul_rpow (by positivity) ht.1.le
      have he : Real.exp ((ρ * t) ^ 3 / 12) ≤ Real.exp (ρ ^ 3 / 12) := by
        apply Real.exp_le_exp.mpr
        have : (ρ * t) ^ 3 ≤ ρ ^ 3 := pow_le_pow_left₀ hs.le (by nlinarith [ht.2, hρ0]) 3
        linarith
      have hpos : 0 ≤ (4 * π * ρ) ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 2 : ℝ)) := by positivity
      calc ‖(ω t : ℂ) * cexp (-(uctA1 * y * (t : ℂ)))‖ * ((4 * π * (ρ * t)) ^ (-(1 / 2 : ℝ)) * Real.exp ((ρ * t) ^ 3 / 12))
          ≤ Real.exp (|airyZero 1| * ρ) * ((4 * π * (ρ * t)) ^ (-(1 / 2 : ℝ)) * Real.exp (ρ ^ 3 / 12)) := by
            apply mul_le_mul hcn (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity) (by positivity)
        _ = Cc * t ^ (-(1 / 2 : ℝ)) := by rw [hp, hCc]; ring
  have hswap := integral_integral_swap hint
  have hL : ∀ u : ℝ, (airyAi u : ℂ) ^ 2 * ∫ t in Ioc (0 : ℝ) 1, (ω t : ℂ) * cexp (((u : ℂ) - uctA1) * y * (t : ℂ)) = ∫ t, f u t ∂ν := by
    intro u; simp only [f]; rw [integral_const_mul]
  calc _ = ∫ u : ℝ, ∫ t, f u t ∂ν := integral_congr_ae (ae_of_all _ hL)
    _ = ∫ t, ∫ u : ℝ, f u t ∂volume ∂ν := hswap
    _ = _ := by
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      show ∫ u, f u t = _
      rw [hfun t, integral_const_mul, (airySq_complex_laplace (hre ht)).2]
      ring
/-! ### Exponential integral identities and pointwise relations -/

lemma exp_sub_one_eq (c : ℂ) :
    cexp c - 1 = c * ∫ t in Ioc (0 : ℝ) 1, cexp (c * (t : ℂ)) := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  by_cases hc : c = 0
  · simp [hc]
  · rw [integral_exp_mul_complex hc]; simp; field_simp

lemma exp_sub_one_sub_eq (c : ℂ) :
    cexp c - 1 - c = c ^ 2 * ∫ t in Ioc (0 : ℝ) 1, ((1 - t : ℝ) : ℂ) * cexp (c * (t : ℂ)) := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  by_cases hc : c = 0
  · simp [hc]
  · have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => ((1 - t : ℝ) : ℂ) * cexp (c * (t : ℂ)) / c + cexp (c * (t : ℂ)) / c ^ 2)
        (((1 - t : ℝ) : ℂ) * cexp (c * (t : ℂ))) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ => ((1 - t : ℝ) : ℂ)) (-1) t := by
        have := ((hasDerivAt_id t).const_sub 1).ofReal_comp
        simpa using this
      have h2 : HasDerivAt (fun t : ℝ => cexp (c * (t : ℂ))) (c * cexp (c * (t : ℂ))) t := by
        have := ((hasDerivAt_id t).ofReal_comp.const_mul c).cexp
        simpa [mul_comm] using this
      have h3 := ((h1.mul h2).div_const c).add (h2.div_const (c ^ 2))
      convert h3 using 1
      field_simp; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (by
      apply Continuous.intervalIntegrable; fun_prop)]
    field_simp
    simp; ring

lemma ceF1_mul_sub (u : ℝ) : ceF1 u * (u - airyZero 1) = airyAi u ^ 2 := by
  by_cases hu : u = airyZero 1
  · subst hu; simp [airyAi_airyZero]
  · unfold ceF1
    rw [dslope_of_ne _ hu, slope_def_field, airyAi_airyZero, sub_zero]
    have : u - airyZero 1 ≠ 0 := sub_ne_zero.mpr hu
    field_simp

lemma ceG1_mul_sub (u : ℝ) : ceG1 (airyZero 1) u * (u - airyZero 1) = ceF1 u := by
  by_cases hu : u = airyZero 1
  · subst hu; simp [ceF1, airyAi_airyZero]
  · unfold ceG1 ceF1
    rw [dslope_of_ne _ hu, slope_def_field, airyAi_airyZero, sub_zero]
    have : u - airyZero 1 ≠ 0 := sub_ne_zero.mpr hu
    field_simp

lemma ceG1_mul_sub_sq (u : ℝ) : ceG1 (airyZero 1) u * (u - airyZero 1) ^ 2 = airyAi u ^ 2 := by
  rw [sq, ← mul_assoc, ceG1_mul_sub, ceF1_mul_sub]

lemma ceF1_pointwise (y : ℂ) (u : ℝ) :
    (ceF1 u : ℂ) * (cexp (((u : ℂ) - uctA1) * y) - 1) =
      y * ((airyAi u : ℂ) ^ 2 * ∫ t in Ioc (0 : ℝ) 1, (((fun _ : ℝ => (1 : ℝ)) t : ℝ) : ℂ) * cexp (((u : ℂ) - uctA1) * y * (t : ℂ))) := by
  simp only [Complex.ofReal_one, one_mul]
  rw [exp_sub_one_eq (((u : ℂ) - uctA1) * y)]
  have h := ceF1_mul_sub u
  have h' : (ceF1 u : ℂ) * ((u : ℂ) - uctA1) = (airyAi u : ℂ) ^ 2 := by
    unfold uctA1; exact_mod_cast h
  calc (ceF1 u : ℂ) * (((u : ℂ) - uctA1) * y * ∫ t in Ioc (0 : ℝ) 1, cexp (((u : ℂ) - uctA1) * y * (t : ℂ)))
      = ((ceF1 u : ℂ) * ((u : ℂ) - uctA1)) * y * ∫ t in Ioc (0 : ℝ) 1, cexp (((u : ℂ) - uctA1) * y * (t : ℂ)) := by ring
    _ = _ := by rw [h']; ring

lemma ceG1_pointwise (y : ℂ) (u : ℝ) :
    (ceG1 (airyZero 1) u : ℂ) * (cexp (((u : ℂ) - uctA1) * y) - 1 - ((u : ℂ) - uctA1) * y) =
      y ^ 2 * ((airyAi u : ℂ) ^ 2 * ∫ t in Ioc (0 : ℝ) 1, (((fun t : ℝ => 1 - t) t : ℝ) : ℂ) * cexp (((u : ℂ) - uctA1) * y * (t : ℂ))) := by
  simp only
  rw [exp_sub_one_sub_eq (((u : ℂ) - uctA1) * y)]
  have h := ceG1_mul_sub_sq u
  have h' : (ceG1 (airyZero 1) u : ℂ) * ((u : ℂ) - uctA1) ^ 2 = (airyAi u : ℂ) ^ 2 := by
    unfold uctA1; exact_mod_cast h
  calc (ceG1 (airyZero 1) u : ℂ) * ((((u : ℂ) - uctA1) * y) ^ 2 * ∫ t in Ioc (0 : ℝ) 1, ((1 - t : ℝ) : ℂ) * cexp (((u : ℂ) - uctA1) * y * (t : ℂ)))
      = ((ceG1 (airyZero 1) u : ℂ) * ((u : ℂ) - uctA1) ^ 2) * y ^ 2 * ∫ t in Ioc (0 : ℝ) 1, ((1 - t : ℝ) : ℂ) * cexp (((u : ℂ) - uctA1) * y * (t : ℂ)) := by ring
    _ = _ := by rw [h']; ring


lemma cpow_mul_ofReal_pos (z : ℂ) {t : ℝ} (ht : 0 < t) (r : ℂ) : (z * (t : ℂ)) ^ r = z ^ r * (t : ℂ) ^ r := by
  rw [mul_comm z, Complex.mul_cpow, mul_comm]
  rw [Complex.arg_ofReal_of_nonneg ht.le, zero_add]
  exact ⟨Complex.neg_pi_lt_arg z, Complex.arg_le_pi z⟩

lemma four_pi_cpow (y : ℂ) : (4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ)) = ((2 * Real.sqrt π : ℝ) : ℂ)⁻¹ * y ^ (-(1 / 2 : ℂ)) := by
  have h4 : (4 * (π : ℂ) * y) = ((4 * π : ℝ) : ℂ) * y := by push_cast; ring
  rw [h4, Complex.mul_cpow]
  · congr 1
    have hp : (0 : ℝ) ≤ 4 * π := by positivity
    rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hp, ← Complex.ofReal_inv]
    congr 1
    rw [Real.rpow_neg hp, ← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  · rw [Complex.arg_ofReal_of_nonneg (by positivity), zero_add]
    exact ⟨Complex.neg_pi_lt_arg y, Complex.arg_le_pi y⟩

lemma mul_cpow_neg_half {y : ℂ} (hy : y ≠ 0) : y * y ^ (-(1 / 2 : ℂ)) = y ^ (1 / 2 : ℂ) := by
  calc y * y ^ (-(1 / 2 : ℂ)) = y ^ (1 : ℂ) * y ^ (-(1 / 2 : ℂ)) := by rw [Complex.cpow_one]
    _ = y ^ (1 + -(1 / 2 : ℂ)) := (Complex.cpow_add _ _ hy).symm
    _ = _ := by congr 1; ring

lemma sq_mul_cpow_neg_half {y : ℂ} (hy : y ≠ 0) : y ^ 2 * y ^ (-(1 / 2 : ℂ)) = y ^ (3 / 2 : ℂ) := by
  calc y ^ 2 * y ^ (-(1 / 2 : ℂ)) = y ^ (2 : ℂ) * y ^ (-(1 / 2 : ℂ)) := by rw [← Complex.cpow_natCast]; norm_num
    _ = y ^ (2 + -(1 / 2 : ℂ)) := (Complex.cpow_add _ _ hy).symm
    _ = _ := by congr 1; ring


lemma fubini_rhs_eq (y : ℂ) {ω : ℝ → ℝ} {κ : ℝ → ℂ} (hκ : ∀ t ∈ Ioc (0 : ℝ) 1, (ω t : ℂ) * uctKap t = κ t) :
    ∫ t in Ioc (0 : ℝ) 1, (ω t : ℂ) * (cexp (-(uctA1 * y * (t : ℂ))) *
        ((4 * (π : ℂ) * (y * (t : ℂ))) ^ (-(1 / 2 : ℂ)) * cexp ((y * (t : ℂ)) ^ 3 / 12))) =
      (4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ)) * uctWI κ y := by
  unfold uctWI
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  rw [← hκ t ht, show 4 * (π : ℂ) * (y * (t : ℂ)) = (4 * (π : ℂ) * y) * (t : ℂ) by ring, cpow_mul_ofReal_pos _ ht.1]
  unfold uctPsi uctKap
  rw [show (-(uctA1 * (y * (t : ℂ))) + (y * (t : ℂ)) ^ 3 / 12) = -(uctA1 * y * (t : ℂ)) + (y * (t : ℂ)) ^ 3 / 12 by ring, Complex.exp_add]
  ring


theorem airyTwistedLaplaceC_ceF1_closed_pos {y : ℂ} (hy : 0 < y.re) :
    airyTwistedLaplaceC ceF1 y = (ceK : ℂ) / (Real.sqrt π : ℂ) * y ^ (1 / 2 : ℂ) * uctE y := by
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  set A : ℂ := ∫ u : ℝ, (ceF1 u : ℂ) * cexp (y * (u : ℂ)) with hA
  have hI1 : Integrable (fun u : ℝ => (ceF1 u : ℂ) * cexp (y * (u : ℂ))) := ceF1_regularity.1 y hy.le
  have hI0 : Integrable (fun u : ℝ => (ceF1 u : ℂ)) := ceF1_integral_eq_zero.1.ofReal
  have hint0 : ∫ u : ℝ, (ceF1 u : ℂ) = 0 := by
    rw [integral_complex_ofReal, ceF1_integral_eq_zero.2]; simp
  have hL : ∫ u : ℝ, (ceF1 u : ℂ) * (cexp (((u : ℂ) - uctA1) * y) - 1) = cexp (-(uctA1 * y)) * A := by
    have : ∀ u : ℝ, (ceF1 u : ℂ) * (cexp (((u : ℂ) - uctA1) * y) - 1) =
        cexp (-(uctA1 * y)) * ((ceF1 u : ℂ) * cexp (y * (u : ℂ))) - (ceF1 u : ℂ) := by
      intro u
      have : cexp (((u : ℂ) - uctA1) * y) = cexp (-(uctA1 * y)) * cexp (y * (u : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; ring
      rw [this]; ring
    simp_rw [this]
    rw [integral_sub (hI1.const_mul _) hI0, integral_const_mul, hint0, sub_zero]
  have hR := airySq_fubini (ω := fun _ => (1 : ℝ)) continuous_const (fun t _ => by simp) hy
  have hpt := fun u : ℝ => ceF1_pointwise y u
  have hmid : ∫ u : ℝ, (ceF1 u : ℂ) * (cexp (((u : ℂ) - uctA1) * y) - 1) =
      y * ∫ t in Ioc (0 : ℝ) 1, (((fun _ : ℝ => (1 : ℝ)) t : ℝ) : ℂ) * (cexp (-(uctA1 * y * (t : ℂ))) *
        ((4 * (π : ℂ) * (y * (t : ℂ))) ^ (-(1 / 2 : ℂ)) * cexp ((y * (t : ℂ)) ^ 3 / 12))) := by
    simp_rw [hpt]
    rw [integral_const_mul]
    congr 1
  rw [hmid, fubini_rhs_eq y (κ := uctKap) (fun t ht => by simp)] at hL
  have hAeq : A = cexp (uctA1 * y) * (cexp (-(uctA1 * y)) * A) := by
    rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  have hsq : ((Real.sqrt π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hexp : cexp (uctA1 * y - y ^ 3 / 12) = cexp (uctA1 * y) * cexp (-(y ^ 3) / 12) := by
    rw [← Complex.exp_add]; congr 1; ring
  have hmul := mul_cpow_neg_half hy0
  unfold airyTwistedLaplaceC uctE
  rw [← hA, hAeq, ← hL, four_pi_cpow, hexp]
  push_cast
  have h2 : ((2 : ℂ) * (Real.sqrt π : ℂ))⁻¹ = (2 : ℂ)⁻¹ * ((Real.sqrt π : ℂ))⁻¹ := by rw [mul_inv]
  calc _ = (ceK : ℂ) * cexp (-(y ^ 3) / 12) * (cexp (uctA1 * y) * (y * ((2 * (Real.sqrt π : ℂ))⁻¹ * y ^ (-(1 / 2 : ℂ))) * uctWI uctKap y)) := by ring
    _ = _ := by
      rw [h2, show y * ((2 : ℂ)⁻¹ * (Real.sqrt π : ℂ)⁻¹ * y ^ (-(1 / 2 : ℂ))) = (2 : ℂ)⁻¹ * (Real.sqrt π : ℂ)⁻¹ * (y * y ^ (-(1 / 2 : ℂ))) by ring, hmul]
      field_simp


theorem airyTwistedLaplaceC_ceG1_closed_pos {y : ℂ} (hy : 0 < y.re) :
    airyTwistedLaplaceC (ceG1 (airyZero 1)) y =
      (ceK : ℂ) * uctE1 y + (ceK : ℂ) / (Real.sqrt π : ℂ) * y ^ (3 / 2 : ℂ) * uctE2 y := by
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  set B : ℂ := ∫ u : ℝ, (ceG1 (airyZero 1) u : ℂ) * cexp (y * (u : ℂ)) with hB
  have hI1 : Integrable (fun u : ℝ => (ceG1 (airyZero 1) u : ℂ) * cexp (y * (u : ℂ))) := hasU2_ceG1.integrable y hy.le
  have hG0 : Integrable (fun u : ℝ => (ceG1 (airyZero 1) u : ℂ)) := ceG1_integrable.ofReal
  have hF0 : Integrable (fun u : ℝ => (ceF1 u : ℂ)) := ceF1_integral_eq_zero.1.ofReal
  have hintG : ∫ u : ℝ, (ceG1 (airyZero 1) u : ℂ) = 1 := by
    rw [integral_complex_ofReal, ceG1_integral_eq_one]; simp
  have hintF : ∫ u : ℝ, (ceF1 u : ℂ) = 0 := by
    rw [integral_complex_ofReal, ceF1_integral_eq_zero.2]; simp
  have hL : ∫ u : ℝ, (ceG1 (airyZero 1) u : ℂ) * (cexp (((u : ℂ) - uctA1) * y) - 1 - ((u : ℂ) - uctA1) * y) = cexp (-(uctA1 * y)) * B - 1 := by
    have : ∀ u : ℝ, (ceG1 (airyZero 1) u : ℂ) * (cexp (((u : ℂ) - uctA1) * y) - 1 - ((u : ℂ) - uctA1) * y) =
        (cexp (-(uctA1 * y)) * ((ceG1 (airyZero 1) u : ℂ) * cexp (y * (u : ℂ))) - (ceG1 (airyZero 1) u : ℂ)) - y * (ceF1 u : ℂ) := by
      intro u
      have h1 : cexp (((u : ℂ) - uctA1) * y) = cexp (-(uctA1 * y)) * cexp (y * (u : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; ring
      have h2 : (ceG1 (airyZero 1) u : ℂ) * ((u : ℂ) - uctA1) = (ceF1 u : ℂ) := by
        have := ceG1_mul_sub u
        unfold uctA1; exact_mod_cast this
      rw [h1, ← h2]; ring
    simp_rw [this]
    have h12 : Integrable (fun u : ℝ => cexp (-(uctA1 * y)) * ((ceG1 (airyZero 1) u : ℂ) * cexp (y * (u : ℂ))) - (ceG1 (airyZero 1) u : ℂ)) :=
      (hI1.const_mul _).sub hG0
    have h1 : Integrable (fun u : ℝ => cexp (-(uctA1 * y)) * ((ceG1 (airyZero 1) u : ℂ) * cexp (y * (u : ℂ)))) := hI1.const_mul _
    have h3 : Integrable (fun u : ℝ => y * (ceF1 u : ℂ)) := hF0.const_mul y
    rw [integral_sub h12 h3, integral_sub h1 hG0, integral_const_mul, integral_const_mul, hintG, hintF, mul_zero, sub_zero]
  have hR := airySq_fubini (ω := fun t => 1 - t) (by fun_prop) (fun t ht => by
    rw [abs_of_nonneg (by linarith [ht.2])]; linarith [ht.1]) hy
  have hpt := fun u : ℝ => ceG1_pointwise y u
  have hmid : ∫ u : ℝ, (ceG1 (airyZero 1) u : ℂ) * (cexp (((u : ℂ) - uctA1) * y) - 1 - ((u : ℂ) - uctA1) * y) =
      y ^ 2 * ∫ t in Ioc (0 : ℝ) 1, (((fun t : ℝ => 1 - t) t : ℝ) : ℂ) * (cexp (-(uctA1 * y * (t : ℂ))) *
        ((4 * (π : ℂ) * (y * (t : ℂ))) ^ (-(1 / 2 : ℂ)) * cexp ((y * (t : ℂ)) ^ 3 / 12))) := by
    simp_rw [hpt]
    rw [integral_const_mul]
    congr 1
  rw [hmid, fubini_rhs_eq y (κ := uctKap1) (fun t ht => by simp [uctKap1, uctKap])] at hL
  have hBeq : B = cexp (uctA1 * y) * (1 + y ^ 2 * ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ)) * uctWI uctKap1 y)) := by
    have : cexp (-(uctA1 * y)) * B = 1 + y ^ 2 * ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ)) * uctWI uctKap1 y) := by
      linear_combination (-1 : ℂ) * hL
    rw [← this, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  have hsq : ((Real.sqrt π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hexp : cexp (uctA1 * y - y ^ 3 / 12) = cexp (uctA1 * y) * cexp (-(y ^ 3) / 12) := by
    rw [← Complex.exp_add]; congr 1; ring
  have hmul := sq_mul_cpow_neg_half hy0
  unfold airyTwistedLaplaceC uctE1 uctE2
  rw [← hB, hBeq, four_pi_cpow, hexp]
  push_cast
  have h2 : ((2 : ℂ) * (Real.sqrt π : ℂ))⁻¹ = (2 : ℂ)⁻¹ * ((Real.sqrt π : ℂ))⁻¹ := by rw [mul_inv]
  have h3 : y ^ 2 * (((2 : ℂ)⁻¹ * (Real.sqrt π : ℂ)⁻¹) * y ^ (-(1 / 2 : ℂ)) * uctWI uctKap1 y) =
      (2 : ℂ)⁻¹ * (Real.sqrt π : ℂ)⁻¹ * (y ^ 2 * y ^ (-(1 / 2 : ℂ))) * uctWI uctKap1 y := by ring
  rw [h2, h3, hmul]
  field_simp


lemma continuousOn_cpow_re_nonneg (w : ℂ) (hw : 0 < w.re) : ContinuousOn (fun y : ℂ => y ^ w) {y : ℂ | 0 ≤ y.re} :=
  fun _ hy => (Complex.continuousAt_cpow_const_of_re_pos (Or.inl hy) hw).continuousWithinAt

/-- The closed form of `f̃₁` of `(uct:Fstar-int)` on `Re y ≥ 0` (`F_* = -f₁`). -/
theorem airyTwistedLaplaceC_ceF1_closed {y : ℂ} (hy : 0 ≤ y.re) :
    airyTwistedLaplaceC ceF1 y = (ceK : ℂ) / (Real.sqrt π : ℂ) * y ^ (1 / 2 : ℂ) * uctE y := by
  have hc : ContinuousOn (fun y : ℂ => (ceK : ℂ) / (Real.sqrt π : ℂ) * y ^ (1 / 2 : ℂ) * uctE y) {y : ℂ | 0 ≤ y.re} :=
    (continuousOn_const.mul (continuousOn_cpow_re_nonneg _ (by norm_num))).mul uctE_differentiable.continuous.continuousOn
  refine Set.EqOn.of_subset_closure (s := {y : ℂ | 0 < y.re}) (fun _ hy => airyTwistedLaplaceC_ceF1_closed_pos hy)
    ceF1_regularity.2.1 hc (fun y (hy : 0 < y.re) => hy.le) ?_ hy
  intro y hy
  rw [Complex.closure_setOfPred_lt_re]; exact hy

/-- The closed form of `g̃₁` of `(uct:g1-int)` on `Re y ≥ 0`. -/
theorem airyTwistedLaplaceC_ceG1_closed {y : ℂ} (hy : 0 ≤ y.re) :
    airyTwistedLaplaceC (ceG1 (airyZero 1)) y =
      (ceK : ℂ) * uctE1 y + (ceK : ℂ) / (Real.sqrt π : ℂ) * y ^ (3 / 2 : ℂ) * uctE2 y := by
  have hc : ContinuousOn (fun y : ℂ => (ceK : ℂ) * uctE1 y + (ceK : ℂ) / (Real.sqrt π : ℂ) * y ^ (3 / 2 : ℂ) * uctE2 y) {y : ℂ | 0 ≤ y.re} :=
    (continuousOn_const.mul uctE1_differentiable.continuous.continuousOn).add
      ((continuousOn_const.mul (continuousOn_cpow_re_nonneg _ (by norm_num))).mul uctE2_differentiable.continuous.continuousOn)
  have hreg : ContinuousOn (airyTwistedLaplaceC (ceG1 (airyZero 1))) {y : ℂ | 0 ≤ y.re} := by
    obtain ⟨C1, hC1, hG1⟩ := ceG1_tail_exp_rpow32
    exact (airyTwistedLaplaceC_regularity (continuous_ceG1 _) ceG1_integrable hC1 hG1).2.1
  refine Set.EqOn.of_subset_closure (s := {y : ℂ | 0 < y.re}) (fun _ hy => airyTwistedLaplaceC_ceG1_closed_pos hy)
    hreg hc (fun y (hy : 0 < y.re) => hy.le) ?_ hy
  intro y hy
  rw [Complex.closure_setOfPred_lt_re]; exact hy

end FormalResearch.SignUncertainty
