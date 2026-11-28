module

public import FormalResearch.SignUncertainty.ConvSourceFarHelpers
public import FormalResearch.SignUncertainty.ConvSourceFamily

/-!
# Far-range transfer lower bound for the convolution source (`S3a`, `ceo:conv` (7))

Reference: `CFT/sign_uncertainty/paper/ce_o1_global_transfer.tex` (`ceo:conv` (7)).

Proves `convSourceFamily_far_transfer`: for `p ∈ (1/2, 1)`, `γ ≥ 0`, `θ > 0`, `λ > 0`, `L_min > 0`,
and spline order `m ≥ 4`, there exists `b_F > 0` independent of `(κ, m, c)` such that for every
`κ > 0`, for all sufficiently large `c` and all `ξ > 0` with `L = log(π² ξ) ≥ L_min`,
`(c ξ) · Re(I_main[S_c](ξ)) ≥ (b_F - C_err c^{-1/6}) (1 + L)^{-3/2}`.
-/

@[expose] public section

noncomputable section

open Real Complex MeasureTheory Set Filter
open FormalResearch.Special FormalResearch.Asymptotics
open scoped BigOperators Topology

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-! ### 1. Linearity of `mainTransferOp` and smooth cutoff helpers -/

lemma mainTransferOp_add {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 1 ≤ m) {c : ℝ} (hc : 1 ≤ c)
    {f₁ f₂ : ℝ → ℂ} (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (L : ℝ) :
    mainTransferOp κ m c (fun X => f₁ X + f₂ X) L =
      mainTransferOp κ m c f₁ L + mainTransferOp κ m c f₂ L := by
  have hc0 : 0 < c := by linarith
  have ha1 : Integrable (mainEdgeAmp κ m c) := integrable_mainEdgeAmp hκ hm hc
  set Ma : ℝ := ∫ τ : ℝ, ‖mainEdgeAmp κ m c τ‖
  have hKc : Continuous (fun y : ℝ => mainEdgeKernel (mainEdgeAmp κ m c) c y) := by
    refine continuous_of_dominated (bound := fun τ => ‖mainEdgeAmp κ m c τ‖) ?_ ?_ ha1.norm ?_
    · intro y
      have hphase : Continuous (fun τ : ℝ => Complex.exp (Complex.I * (c : ℂ) * ((y * τ + edgeR τ : ℝ) : ℂ))) :=
        Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
          ((continuous_const.mul continuous_id).add edgeR_contDiff.continuous)))
      exact ha1.aestronglyMeasurable.mul hphase.aestronglyMeasurable
    · exact fun y => ae_of_all _ fun τ => by
        rw [norm_mul, show Complex.I * (c : ℂ) * ((y * τ + edgeR τ : ℝ) : ℂ) =
          ((c * (y * τ + edgeR τ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]
    · exact ae_of_all _ fun τ => by fun_prop
  have hK_le : ∀ y : ℝ, ‖mainEdgeKernel (mainEdgeAmp κ m c) c y‖ ≤ Ma := fun y => by
    unfold mainEdgeKernel
    refine (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae (ae_of_all _ fun τ => ?_))
    dsimp only
    rw [norm_mul, show Complex.I * (c : ℂ) * ((y * τ + edgeR τ : ℝ) : ℂ) =
      ((c * (y * τ + edgeR τ) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hmeas_K : AEStronglyMeasurable (fun X : ℝ => mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)) volume :=
    (hKc.comp (by fun_prop : Continuous fun X : ℝ => L - ceCs * X)).aestronglyMeasurable
  have hint : ∀ {f : ℝ → ℂ}, Integrable f →
      Integrable (fun X => f X * mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)) := fun hf => by
    refine (hf.norm.const_mul Ma).mono' (hf.aestronglyMeasurable.mul hmeas_K) (ae_of_all _ fun X => ?_)
    rw [norm_mul, mul_comm Ma]
    exact mul_le_mul_of_nonneg_left (hK_le _) (norm_nonneg _)
  unfold mainTransferOp
  have hadd : (fun X : ℝ => (f₁ X + f₂ X) * mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X)) =
      fun X => f₁ X * mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X) +
        f₂ X * mainEdgeKernel (mainEdgeAmp κ m c) c (L - ceCs * X) := funext fun X => by ring
  rw [hadd, integral_add (hint hf₁) (hint hf₂), mul_add]

lemma smoothTransition_deriv_bound :
    ∃ M_st > 0, ∀ t : ℝ, |deriv Real.smoothTransition t| ≤ M_st ∧
      (t ≤ 0 → deriv Real.smoothTransition t = 0) ∧
      (1 ≤ t → deriv Real.smoothTransition t = 0) := by
  have hcd : ContDiff ℝ (1 : ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
  have hc : Continuous (deriv Real.smoothTransition) := hcd.continuous_deriv (by simp)
  obtain ⟨t₀, -, ht₀⟩ := isCompact_Icc.exists_isMaxOn (⟨(0 : ℝ), by norm_num⟩ : (Icc (0 : ℝ) 1).Nonempty)
    (hc.abs.continuousOn)
  let M_st := max |deriv Real.smoothTransition t₀| 1
  refine ⟨M_st, by positivity, fun t => ?_⟩
  have h0 : t ≤ 0 → deriv Real.smoothTransition t = 0 := fun ht => by
    by_cases hlt : t < 0
    · have hev : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
        Filter.eventually_of_mem (isOpen_Iio.mem_nhds hlt) fun s hs =>
          Real.smoothTransition.zero_of_nonpos (le_of_lt hs)
      rw [hev.deriv_eq, deriv_const]
    · have ht0 : t = 0 := le_antisymm ht (not_lt.mp hlt)
      subst ht0
      have h_le : ∀ᶠ s in 𝓝[<] (0 : ℝ), deriv Real.smoothTransition s = 0 :=
        Filter.eventually_of_mem self_mem_nhdsWithin fun s hs => by
          have hev : Real.smoothTransition =ᶠ[𝓝 s] fun _ => (0 : ℝ) :=
            Filter.eventually_of_mem (isOpen_Iio.mem_nhds hs) fun u hu =>
              Real.smoothTransition.zero_of_nonpos (le_of_lt hu)
          rw [hev.deriv_eq, deriv_const]
      have hct : Tendsto (deriv Real.smoothTransition) (𝓝[<] (0 : ℝ)) (𝓝 (deriv Real.smoothTransition 0)) :=
        hc.continuousWithinAt
      exact tendsto_nhds_unique hct (tendsto_const_nhds.congr' (h_le.mono fun _ h => h.symm))
  have h1 : 1 ≤ t → deriv Real.smoothTransition t = 0 := fun ht => by
    by_cases hgt : 1 < t
    · have hev : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) :=
        Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hgt) fun s hs =>
          Real.smoothTransition.one_of_one_le (le_of_lt hs)
      rw [hev.deriv_eq, deriv_const]
    · have ht1 : t = 1 := le_antisymm (not_lt.mp hgt) ht
      subst ht1
      have h_ge : ∀ᶠ s in 𝓝[>] (1 : ℝ), deriv Real.smoothTransition s = 0 :=
        Filter.eventually_of_mem self_mem_nhdsWithin fun s hs => by
          have hev : Real.smoothTransition =ᶠ[𝓝 s] fun _ => (1 : ℝ) :=
            Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hs) fun u hu =>
              Real.smoothTransition.one_of_one_le (le_of_lt hu)
          rw [hev.deriv_eq, deriv_const]
      have hct : Tendsto (deriv Real.smoothTransition) (𝓝[>] (1 : ℝ)) (𝓝 (deriv Real.smoothTransition 1)) :=
        hc.continuousWithinAt
      exact tendsto_nhds_unique hct (tendsto_const_nhds.congr' (h_ge.mono fun _ h => h.symm))
  refine ⟨?_, h0, h1⟩
  by_cases ht_le : t ≤ 0
  · rw [h0 ht_le, abs_zero]; positivity
  · by_cases ht_ge : 1 ≤ t
    · rw [h1 ht_ge, abs_zero]; positivity
    · exact (ht₀ ⟨(not_le.mp ht_le).le, (not_le.mp ht_ge).le⟩).trans (le_max_left _ _)

/-! ### 2. Splitting of `rescaledTail (convSource ...)` -/

/-- Rescaled exponential term `f_exp(Y) = 1_{Y > 0} γ ε⁻² e^{-Y / ε²}`. -/
noncomputable def convFExp (γ ε Y : ℝ) : ℝ :=
  if 0 < Y then γ * (ε ^ 2)⁻¹ * Real.exp (-Y / ε ^ 2) else 0

/-- Rescaled cutoff weight term `w_full(Y) = 1_{Y > 0} θ η(Y/ε²) ρ_p(λ Y) Y^{-3/2}`. -/
noncomputable def convWFull (p θ lam ε Y : ℝ) : ℝ :=
  if 0 < Y then θ * convEta (Y / ε ^ 2) * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ)) else 0

lemma convFExp_nonneg {γ : ℝ} (hγ : 0 ≤ γ) (ε Y : ℝ) : 0 ≤ convFExp γ ε Y := by
  unfold convFExp; split_ifs <;> positivity

private lemma integrableOn_Ioi_exp_neg_mul {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun Y : ℝ => Real.exp (-(a * Y))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (0 : ℝ))
    (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1) ha
  refine h.congr_fun (fun Y _ => ?_) measurableSet_Ioi
  simp

lemma convFExp_integrable {γ ε : ℝ} (hε : 0 < ε) : Integrable (convFExp γ ε) := by
  have h1 : IntegrableOn (fun Y : ℝ => γ * (ε ^ 2)⁻¹ * Real.exp (-((ε ^ 2)⁻¹ * Y))) (Ioi 0) :=
    (integrableOn_Ioi_exp_neg_mul (inv_pos.mpr (pow_pos hε 2))).const_mul (γ * (ε ^ 2)⁻¹)
  rw [show convFExp γ ε = (Ioi 0).indicator (fun Y => γ * (ε ^ 2)⁻¹ * Real.exp (-((ε ^ 2)⁻¹ * Y))) by
    funext Y; unfold convFExp; by_cases hY : 0 < Y <;> simp [hY, mem_Ioi, div_eq_mul_inv, mul_comm]]
  exact (integrable_indicator_iff measurableSet_Ioi).mpr h1

lemma convFExp_integral_norm {γ ε : ℝ} (hγ : 0 ≤ γ) (hε : 0 < ε) :
    ∫ Y : ℝ, ‖convFExp γ ε Y‖ = γ := by
  have h_nn : (fun Y : ℝ => ‖convFExp γ ε Y‖) = convFExp γ ε := funext fun Y =>
    Real.norm_of_nonneg (convFExp_nonneg hγ ε Y)
  rw [h_nn]
  have h_ind : convFExp γ ε = (Ioi 0).indicator (fun Y => γ * (ε ^ 2)⁻¹ * Real.exp (-((ε ^ 2)⁻¹ * Y))) := by
    funext Y; unfold convFExp; by_cases hY : 0 < Y <;> simp [hY, mem_Ioi, div_eq_mul_inv, mul_comm]
  rw [h_ind, integral_indicator measurableSet_Ioi, integral_const_mul]
  have h_pos : (0 : ℝ) < (ε ^ 2)⁻¹ := inv_pos.mpr (pow_pos hε 2)
  have hI : ∫ Y in Ioi (0 : ℝ), Real.exp (-((ε ^ 2)⁻¹ * Y)) = ε ^ 2 := by
    have h_eq : (fun t : ℝ => Real.exp (-((ε ^ 2)⁻¹ * t))) = fun t => Real.exp (-(ε ^ 2)⁻¹ * t) :=
      funext fun t => by ring_nf
    rw [h_eq]
    have hd : ∀ Y ∈ Ici (0 : ℝ), HasDerivAt (fun t : ℝ => -(ε ^ 2) * Real.exp (-(ε ^ 2)⁻¹ * t))
        (Real.exp (-(ε ^ 2)⁻¹ * Y)) Y := fun Y _ => by
      have h1 : HasDerivAt (fun t : ℝ => -(ε ^ 2)⁻¹ * t) (-(ε ^ 2)⁻¹) Y :=
        ((hasDerivAt_id Y).const_mul (-(ε ^ 2)⁻¹)).congr_deriv (mul_one _)
      exact ((Real.hasDerivAt_exp _).comp Y h1).const_mul (-(ε ^ 2)) |>.congr_deriv (by
        field_simp [pow_ne_zero 2 hε.ne'])
    have htend : Tendsto (fun t : ℝ => -(ε ^ 2) * Real.exp (-(ε ^ 2)⁻¹ * t)) atTop (𝓝 0) := by
      have hlin : Tendsto (fun t : ℝ => -(ε ^ 2)⁻¹ * t) atTop atBot :=
        (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop h_pos)).congr (fun t => (neg_mul _ _).symm)
      have h0 : Tendsto (fun t : ℝ => Real.exp (-(ε ^ 2)⁻¹ * t)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp hlin
      simpa using (tendsto_const_nhds (x := -(ε ^ 2))).mul h0
    have hint_neg : IntegrableOn (fun t : ℝ => Real.exp (-(ε ^ 2)⁻¹ * t)) (Ioi 0) := by
      rw [← h_eq]; exact integrableOn_Ioi_exp_neg_mul h_pos
    have hi := integral_Ioi_of_hasDerivAt_of_tendsto' hd hint_neg htend
    simpa using hi
  rw [hI]
  have hε2 : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε.ne'
  field_simp [hε2]

lemma convWFull_nonneg {p θ lam : ℝ} (hθ : 0 ≤ θ) (hlam : 0 ≤ lam) (ε Y : ℝ) :
    0 ≤ convWFull p θ lam ε Y := by
  unfold convWFull
  split_ifs with hY
  · exact mul_nonneg (mul_nonneg (mul_nonneg hθ (convEta_nonneg _)) (convRho_nonneg p (mul_nonneg hlam hY.le)))
      (Real.rpow_nonneg hY.le _)
  · exact le_rfl

lemma convWFull_le {p θ lam : ℝ} (_hp : 0 ≤ p) (hθ : 0 ≤ θ) (hlam : 0 ≤ lam) (ε Y : ℝ) :
    convWFull p θ lam ε Y ≤
      if 0 < Y then θ * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ)) else 0 := by
  unfold convWFull
  split_ifs with hY
  · have h1 := convEta_le_one (Y / ε ^ 2)
    have h2 : 0 ≤ θ * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ)) :=
      mul_nonneg (mul_nonneg hθ (convRho_nonneg p (mul_nonneg hlam hY.le))) (Real.rpow_nonneg hY.le _)
    calc θ * convEta (Y / ε ^ 2) * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ))
        = convEta (Y / ε ^ 2) * (θ * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ))) := by ring
      _ ≤ 1 * (θ * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ))) := by gcongr
      _ = _ := one_mul _
  · exact le_rfl

lemma convRho_mul_rpow_integrable {p θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1)
    (hθ : 0 ≤ θ) (hlam : 0 < lam) :
    Integrable (fun Y : ℝ => if 0 < Y then θ * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ)) else 0) := by
  have hm : AEStronglyMeasurable (fun Y : ℝ => θ * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ))) (volume.restrict (Ioi 0)) :=
    (Measurable.aestronglyMeasurable (by unfold convRho; measurability)).restrict
  have h01 : IntegrableOn (fun Y : ℝ => θ * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ))) (Ioc 0 1) := by
    have hpow : IntegrableOn (fun Y : ℝ => (θ * lam ^ p) * Y ^ (p - 3 / 2)) (Ioc 0 1) := by
      have hi := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1) (r := p - 3 / 2) (by linarith)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp (hi.const_mul (θ * lam ^ p))
    refine hpow.mono' (hm.mono_set Ioc_subset_Ioi_self) (ae_restrict_of_forall_mem measurableSet_Ioc fun Y hY => ?_)
    have hY0 : 0 < Y := hY.1
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hθ (convRho_nonneg p (mul_nonneg hlam.le hY0.le))) (Real.rpow_nonneg hY0.le _))]
    have hρ : convRho p (lam * Y) ≤ (lam * Y) ^ p := by
      unfold convRho
      refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
      exact div_le_self (by positivity) (by linarith [mul_pos hlam hY0])
    calc θ * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ))
        ≤ θ * (lam * Y) ^ p * Y ^ (-(3 / 2 : ℝ)) := by gcongr
      _ = (θ * lam ^ p) * (Y ^ p * Y ^ (-(3 / 2 : ℝ))) := by
          rw [Real.mul_rpow hlam.le hY0.le]; ring
      _ = (θ * lam ^ p) * Y ^ (p - 3 / 2) := by
          rw [← Real.rpow_add hY0, show p + -(3 / 2 : ℝ) = p - 3 / 2 by ring]
  have h1inf : IntegrableOn (fun Y : ℝ => θ * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ))) (Ioi 1) := by
    have hi := (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) zero_lt_one).const_mul θ
    refine hi.mono' (hm.mono_set (Ioi_subset_Ioi zero_le_one))
      (ae_restrict_of_forall_mem measurableSet_Ioi fun Y hY => ?_)
    have hY0 : 0 < Y := zero_lt_one.trans hY
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hθ (convRho_nonneg p (mul_nonneg hlam.le hY0.le))) (Real.rpow_nonneg hY0.le _))]
    have h1 := convRho_le_one (p := p) (by linarith) (mul_nonneg hlam.le hY0.le)
    calc θ * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ))
        ≤ θ * 1 * Y ^ (-(3 / 2 : ℝ)) := by gcongr
      _ = θ * Y ^ (-(3 / 2 : ℝ)) := by ring
  have hIoi : IntegrableOn (fun Y : ℝ => θ * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ))) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
    exact h01.union h1inf
  rw [show (fun Y : ℝ => if 0 < Y then θ * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ)) else 0) =
      (Ioi 0).indicator (fun Y => θ * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ))) by
    funext Y; by_cases hY : 0 < Y <;> simp [hY, mem_Ioi]]
  exact (integrable_indicator_iff measurableSet_Ioi).mpr hIoi

lemma convWFull_integrable {p θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1)
    (hθ : 0 ≤ θ) (hlam : 0 < lam) (ε : ℝ) :
    Integrable (convWFull p θ lam ε) := by
  have hm : AEStronglyMeasurable (convWFull p θ lam ε) volume := by
    unfold convWFull convEta convRho
    exact (Measurable.ite measurableSet_Ioi (by measurability) measurable_const).aestronglyMeasurable
  refine (convRho_mul_rpow_integrable hp hp1 hθ hlam).mono' hm (ae_of_all _ fun Y => ?_)
  rw [Real.norm_of_nonneg (convWFull_nonneg hθ hlam.le ε Y)]
  exact convWFull_le (by linarith) hθ hlam.le ε Y

lemma rescaledTail_convSource_eq {p γ θ lam c : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1)
    (_hγ : 0 ≤ γ) (hθ : 0 ≤ θ) (hlam : 0 < lam) (hc : 1 ≤ c) (X : ℝ) :
    let ε := liftEps c
    rescaledTail (convSource p γ θ ε (lam * ε ^ 2)) ε X =
      realConv (convFExp γ ε) (rescaledG1 ε) X + realConv (convWFull p θ lam ε) (rescaledG1 ε) X := by
  dsimp only
  set ε : ℝ := liftEps c
  have hc0 : 0 < c := by linarith
  have hε : 0 < ε := liftEps_pos hc0
  have hε2 : 0 < ε ^ 2 := pow_pos hε 2
  unfold rescaledTail convSource
  have h_ind : ∫ y in Ioi (0 : ℝ), convWc p γ θ ε (lam * ε ^ 2) y * ceG1 (airyZero 1) (-X / ε ^ 2 + y) =
      ∫ y : ℝ, (Ioi 0).indicator (fun y => convWc p γ θ ε (lam * ε ^ 2) y * ceG1 (airyZero 1) (-X / ε ^ 2 + y)) y :=
    (integral_indicator measurableSet_Ioi).symm
  rw [h_ind]
  have hcov := Measure.integral_comp_mul_left
    (fun y : ℝ => (Ioi 0).indicator (fun y => convWc p γ θ ε (lam * ε ^ 2) y * ceG1 (airyZero 1) (-X / ε ^ 2 + y)) y)
    (ε ^ 2)⁻¹
  simp only [inv_inv, abs_of_pos hε2, smul_eq_mul] at hcov
  have h_sub : (∫ y : ℝ, (Ioi 0).indicator (fun y => convWc p γ θ ε (lam * ε ^ 2) y * ceG1 (airyZero 1) (-X / ε ^ 2 + y)) y) =
      (ε ^ 2)⁻¹ * ∫ Y : ℝ, (Ioi 0).indicator
        (fun y => convWc p γ θ ε (lam * ε ^ 2) y * ceG1 (airyZero 1) (-X / ε ^ 2 + y)) ((ε ^ 2)⁻¹ * Y) := by
    rw [hcov, ← mul_assoc, inv_mul_cancel₀ hε2.ne', one_mul]
  rw [h_sub, ← mul_assoc, ← integral_const_mul]
  have hf_int := convFExp_integrable (γ := γ) hε
  have hw_int := convWFull_integrable hp hp1 hθ hlam ε
  have hk_int := rescaledG1_integrable hε
  rw [realConv_apply, realConv_apply]
  have hsplit_int : ∫ Y : ℝ, (convFExp γ ε Y * rescaledG1 ε (X - Y) + convWFull p θ lam ε Y * rescaledG1 ε (X - Y)) =
      (∫ Y : ℝ, convFExp γ ε Y * rescaledG1 ε (X - Y)) + (∫ Y : ℝ, convWFull p θ lam ε Y * rescaledG1 ε (X - Y)) := by
    obtain ⟨Cg, hCg, hG_poly⟩ := convG1_le_poly
    have hbd_rescaled : ∀ Z : ℝ, |rescaledG1 ε Z| ≤ (ε ^ 2)⁻¹ * Cg := fun Z => by
      rw [abs_of_nonneg (rescaledG1_nonneg ε Z)]
      unfold rescaledG1
      have h1 : (1 + |-Z / ε ^ 2|) ^ (-(5 / 2 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (-Z / ε ^ 2)]) (by norm_num)
      calc (ε ^ 2)⁻¹ * ceG1 (airyZero 1) (-Z / ε ^ 2)
          ≤ (ε ^ 2)⁻¹ * (Cg * (1 + |-Z / ε ^ 2|) ^ (-(5 / 2 : ℝ))) := by gcongr; exact hG_poly _
        _ ≤ (ε ^ 2)⁻¹ * (Cg * 1) := by gcongr
        _ = _ := by ring
    have hi1 : Integrable (fun Y : ℝ => convFExp γ ε Y * rescaledG1 ε (X - Y)) := by
      refine (hf_int.norm.mul_const (max ((ε ^ 2)⁻¹ * Cg) 0)).mono'
        (hf_int.aestronglyMeasurable.mul ((rescaledG1_continuous hε).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
        (ae_of_all _ fun Y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left ((hbd_rescaled _).trans (le_max_left _ _)) (abs_nonneg _)
    have hi2 : Integrable (fun Y : ℝ => convWFull p θ lam ε Y * rescaledG1 ε (X - Y)) := by
      refine (hw_int.norm.mul_const (max ((ε ^ 2)⁻¹ * Cg) 0)).mono'
        (hw_int.aestronglyMeasurable.mul ((rescaledG1_continuous hε).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
        (ae_of_all _ fun Y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left ((hbd_rescaled _).trans (le_max_left _ _)) (abs_nonneg _)
    exact integral_add hi1 hi2
  rw [← hsplit_int]
  refine integral_congr_ae (ae_of_all _ fun Y => ?_)
  by_cases hY : 0 < Y
  · have hY_mem : (ε ^ 2)⁻¹ * Y ∈ Ioi (0 : ℝ) := mul_pos (inv_pos.mpr hε2) hY
    simp only [hY_mem, indicator_of_mem, convFExp, convWFull, hY, ↓reduceIte, rescaledG1, convWc, convWh]
    have harg1 : -X / ε ^ 2 + (ε ^ 2)⁻¹ * Y = -(X - Y) / ε ^ 2 := by ring
    have harg2 : lam * ε ^ 2 * ((ε ^ 2)⁻¹ * Y) = lam * Y := by field_simp [hε2.ne']
    have hpow32 : ((ε ^ 2)⁻¹ * Y) ^ (3 / 2 : ℝ) = ε ^ (-3 : ℝ) * Y ^ (3 / 2 : ℝ) := by
      rw [Real.mul_rpow (inv_nonneg.mpr hε2.le) hY.le, Real.inv_rpow hε2.le,
        ← Real.rpow_natCast ε 2, ← Real.rpow_mul hε.le]
      norm_num
    have hε3_inv : ε ^ (-3 : ℝ) * (ε ^ (-3 : ℝ))⁻¹ = 1 := mul_inv_cancel₀ (Real.rpow_pos_of_pos hε (-3)).ne'
    have hε1 : ε ^ (-3 : ℝ) * ε = (ε ^ 2)⁻¹ := by
      nth_rw 2 [← Real.rpow_one ε]
      rw [← Real.rpow_add hε, show (-3 : ℝ) + 1 = -2 by norm_num, Real.rpow_neg hε.le, Real.rpow_two]
    rw [harg1, harg2, hpow32, show -((ε ^ 2)⁻¹ * Y) = -Y / ε ^ 2 by ring,
      show (ε ^ 2)⁻¹ * Y = Y / ε ^ 2 by ring]
    calc ε ^ (-3 : ℝ) * (ε ^ 2)⁻¹ *
          ((γ * ε * Real.exp (-Y / ε ^ 2) + θ * (convEta (Y / ε ^ 2) * convRho p (lam * Y) / (ε ^ (-3 : ℝ) * Y ^ (3 / 2 : ℝ)))) *
            ceG1 (airyZero 1) (-(X - Y) / ε ^ 2))
        = (γ * (ε ^ (-3 : ℝ) * ε) * Real.exp (-Y / ε ^ 2) +
            θ * convEta (Y / ε ^ 2) * convRho p (lam * Y) * (ε ^ (-3 : ℝ) * (ε ^ (-3 : ℝ))⁻¹) * Y ^ (-(3 / 2 : ℝ))) *
            ((ε ^ 2)⁻¹ * ceG1 (airyZero 1) (-(X - Y) / ε ^ 2)) := by
          rw [Real.rpow_neg hY.le]; field_simp [hε2.ne', (Real.rpow_pos_of_pos hε (-3)).ne']
      _ = _ := by rw [hε1, hε3_inv, mul_one]; ring
  · have hY_not : (ε ^ 2)⁻¹ * Y ∉ Ioi (0 : ℝ) := by
      simp only [mem_Ioi, not_lt] at hY ⊢
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hε2.le) hY
    simp [hY_not, convFExp, convWFull, hY]

/-! ### 3. Pointwise tail bounds for the `f_exp` and `h_L` convolutions -/

lemma exp_neg_le_six_div_cube {t : ℝ} (ht : 0 < t) : Real.exp (-t) ≤ 6 * t ^ (-3 : ℝ) := by
  have hsum := Real.sum_le_exp_of_nonneg ht.le 4
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at hsum
  simp only [Nat.factorial] at hsum
  have h3 : t ^ 3 / 6 ≤ Real.exp t := by linarith [pow_nonneg ht.le 2]
  have ht3 : t ^ (-3 : ℝ) = (t ^ 3)⁻¹ := by
    rw [Real.rpow_neg ht.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [Real.exp_neg, ht3]
  calc (Real.exp t)⁻¹ ≤ (t ^ 3 / 6)⁻¹ := inv_anti₀ (by positivity) h3
    _ = 6 * (t ^ 3)⁻¹ := by ring

lemma two_eps_sq_le_of_c_ge {L_min L c : ℝ} (hLmin : 0 < L_min) (hL : L_min ≤ L)
    (hc : (8 * ceCs / L_min) ^ (3 / 2 : ℝ) ≤ c) (hc0 : 0 < c) :
    2 * liftEps c ^ 2 ≤ L / (4 * ceCs) := by
  have hcs0 : 0 < ceCs := ceCs_pos
  have hε2_eq : liftEps c ^ 2 = c ^ (-(2 / 3 : ℝ)) := by
    unfold liftEps; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have h_bd : c ^ (-(2 / 3 : ℝ)) ≤ L_min / (8 * ceCs) := by
    calc c ^ (-(2 / 3 : ℝ)) ≤ ((8 * ceCs / L_min) ^ (3 / 2 : ℝ)) ^ (-(2 / 3 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hc (by norm_num)
      _ = (8 * ceCs / L_min) ^ (-1 : ℝ) := by rw [← Real.rpow_mul (by positivity)]; norm_num
      _ = L_min / (8 * ceCs) := by rw [Real.rpow_neg_one, inv_div]
  rw [hε2_eq]
  calc 2 * c ^ (-(2 / 3 : ℝ)) ≤ 2 * (L_min / (8 * ceCs)) := by gcongr
    _ = L_min / (4 * ceCs) := by ring
    _ ≤ L / (4 * ceCs) := by gcongr

lemma rescaledG1_tail_bound {Cg : ℝ} (hG_poly : ∀ u, ceG1 (airyZero 1) u ≤ Cg * (1 + |u|) ^ (-(5 / 2 : ℝ)))
    {c L Z : ℝ} (hc0 : 0 < c) (hL0 : 0 < L) (hZ : L / (4 * ceCs) ≤ Z) :
    rescaledG1 (liftEps c) Z ≤ Cg * (4 * ceCs) ^ (5 / 2 : ℝ) * c⁻¹ * L ^ (-(5 / 2 : ℝ)) := by
  have hcs0 : 0 < ceCs := ceCs_pos
  set ε : ℝ := liftEps c
  have hε : 0 < ε := liftEps_pos hc0
  have hε2 : 0 < ε ^ 2 := pow_pos hε 2
  have hε3 : ε ^ 3 = c⁻¹ := by
    dsimp [ε, liftEps]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num; exact Real.rpow_neg_one c
  have hZ0 : 0 < Z := lt_of_lt_of_le (by positivity) hZ
  have h1 : L / (4 * ceCs * ε ^ 2) ≤ 1 + |-Z / ε ^ 2| := by
    rw [abs_div, abs_neg, abs_of_pos hZ0, abs_of_pos hε2]
    have h2 : L / (4 * ceCs * ε ^ 2) ≤ Z / ε ^ 2 := by
      rw [div_mul_eq_div_div]; exact div_le_div_of_nonneg_right hZ hε2.le
    linarith
  have h2 : (1 + |-Z / ε ^ 2|) ^ (-(5 / 2 : ℝ)) ≤ (L / (4 * ceCs * ε ^ 2)) ^ (-(5 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
  have hpow_split : (ε ^ 2)⁻¹ * (L / (4 * ceCs * ε ^ 2)) ^ (-(5 / 2 : ℝ)) =
      (4 * ceCs) ^ (5 / 2 : ℝ) * c⁻¹ * L ^ (-(5 / 2 : ℝ)) := by
    have hε5 : (ε ^ 2) ^ (5 / 2 : ℝ) = ε ^ 5 := by
      rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul hε.le, show (2 : ℕ) * (5 / 2 : ℝ) = ((5 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    have hε3' : (ε ^ 2)⁻¹ * ε ^ 5 = c⁻¹ := by
      rw [← hε3]; field_simp [hε.ne']
    have h_inv_rpow : (L / (4 * ceCs * ε ^ 2)) ^ (-(5 / 2 : ℝ)) =
        (4 * ceCs) ^ (5 / 2 : ℝ) * ε ^ 5 * L ^ (-(5 / 2 : ℝ)) := by
      rw [Real.rpow_neg (by positivity), Real.div_rpow hL0.le (by positivity), inv_div, div_eq_mul_inv,
        Real.mul_rpow (by positivity) hε2.le, hε5, Real.rpow_neg hL0.le]
    rw [h_inv_rpow]
    calc (ε ^ 2)⁻¹ * ((4 * ceCs) ^ (5 / 2 : ℝ) * ε ^ 5 * L ^ (-(5 / 2 : ℝ)))
        = (4 * ceCs) ^ (5 / 2 : ℝ) * ((ε ^ 2)⁻¹ * ε ^ 5) * L ^ (-(5 / 2 : ℝ)) := by ring
      _ = _ := by rw [hε3']
  have hCg0 : 0 ≤ Cg := by
    have h0 := hG_poly 0
    have hnn : 0 ≤ ceG1 (airyZero 1) 0 := by
      have h := rescaledG1_nonneg (1 : ℝ) 0
      unfold rescaledG1 at h
      simpa using h
    simp at h0; linarith
  unfold rescaledG1
  calc (ε ^ 2)⁻¹ * ceG1 (airyZero 1) (-Z / ε ^ 2)
      ≤ (ε ^ 2)⁻¹ * (Cg * (1 + |-Z / ε ^ 2|) ^ (-(5 / 2 : ℝ))) := by gcongr; exact hG_poly _
    _ ≤ (ε ^ 2)⁻¹ * (Cg * (L / (4 * ceCs * ε ^ 2)) ^ (-(5 / 2 : ℝ))) := by gcongr
    _ = Cg * ((ε ^ 2)⁻¹ * (L / (4 * ceCs * ε ^ 2)) ^ (-(5 / 2 : ℝ))) := by ring
    _ = _ := by rw [hpow_split]; ring

lemma convFExp_conv_tail {γ : ℝ} (hγ : 0 ≤ γ) {L_min : ℝ} (hLmin : 0 < L_min) :
    ∃ M_e > 0, ∀ {c L : ℝ}, (8 * ceCs / L_min) ^ (3 / 2 : ℝ) ≤ c → 1 ≤ c → L_min ≤ L →
      ∀ X : ℝ, (3 / (4 * ceCs)) * L < X →
        ‖(realConv (convFExp γ (liftEps c)) (rescaledG1 (liftEps c)) X : ℂ)‖ ≤
          M_e * c⁻¹ * L ^ (-(3 / 2 : ℝ)) := by
  have hcs0 : 0 < ceCs := ceCs_pos
  obtain ⟨Cg, hCg, hG_poly⟩ := convG1_le_poly
  let M_e : ℝ := γ * Cg * (4 * ceCs) ^ (5 / 2 : ℝ) * L_min⁻¹ + 6 * γ * (2 * ceCs) ^ 3 * L_min ^ (-(3 / 2 : ℝ)) + 1
  refine ⟨M_e, by positivity, fun {c L} _ hc1 hL X hX => ?_⟩
  have hc0 : 0 < c := by linarith
  have hL0 : 0 < L := hLmin.trans_le hL
  set ε : ℝ := liftEps c
  have hε : 0 < ε := liftEps_pos hc0
  have hε2 : 0 < ε ^ 2 := pow_pos hε 2
  have hε3 : ε ^ 3 = c⁻¹ := by
    dsimp [ε, liftEps]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num; exact Real.rpow_neg_one c
  have hε4 : ε ^ 4 ≤ c⁻¹ := by
    have h4 : ε ^ 4 = ε ^ 3 * ε := by ring
    have hε_le1 : ε ≤ 1 := liftEps_le_one hc1
    rw [h4, hε3]
    exact mul_le_of_le_one_right (by positivity) hε_le1
  have h_nn : 0 ≤ realConv (convFExp γ ε) (rescaledG1 ε) X := by
    rw [realConv_apply]
    exact integral_nonneg fun Y => mul_nonneg (convFExp_nonneg hγ ε Y) (rescaledG1_nonneg ε (X - Y))
  rw [Complex.norm_real, Real.norm_of_nonneg h_nn, realConv_apply]
  have hf_int := convFExp_integrable (γ := γ) hε
  have hk_int := rescaledG1_integrable hε
  have hbd_rescaled : ∀ Z : ℝ, |rescaledG1 ε Z| ≤ (ε ^ 2)⁻¹ * Cg := fun Z => by
    rw [abs_of_nonneg (rescaledG1_nonneg ε Z)]; unfold rescaledG1
    calc (ε ^ 2)⁻¹ * ceG1 (airyZero 1) (-Z / ε ^ 2)
        ≤ (ε ^ 2)⁻¹ * (Cg * (1 + |-Z / ε ^ 2|) ^ (-(5 / 2 : ℝ))) := by gcongr; exact hG_poly _
      _ ≤ (ε ^ 2)⁻¹ * (Cg * 1) := by gcongr; exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (-Z / ε ^ 2)]) (by norm_num)
      _ = _ := by ring
  have hprod_int : Integrable (fun Y : ℝ => convFExp γ ε Y * rescaledG1 ε (X - Y)) := by
    refine (hf_int.norm.mul_const (max ((ε ^ 2)⁻¹ * Cg) 0)).mono'
      (hf_int.aestronglyMeasurable.mul ((rescaledG1_continuous hε).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (ae_of_all _ fun Y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left ((hbd_rescaled _).trans (le_max_left _ _)) (abs_nonneg _)
  let A : ℝ := Cg * (4 * ceCs) ^ (5 / 2 : ℝ) * c⁻¹ * L ^ (-(5 / 2 : ℝ))
  let B : ℝ := 6 * γ * (2 * ceCs) ^ 3 * c⁻¹ * L ^ (-3 : ℝ)
  have hpiece : ∀ Y : ℝ,
      convFExp γ ε Y * rescaledG1 ε (X - Y) ≤ A * convFExp γ ε Y + B * rescaledG1 ε (X - Y) := fun Y => by
    by_cases hY : Y ≤ L / (2 * ceCs)
    · have hXY : L / (4 * ceCs) ≤ X - Y := by
        have h1 : L / (2 * ceCs) = 2 * (L / (4 * ceCs)) := by ring
        have h2 : 3 / (4 * ceCs) * L = 3 * (L / (4 * ceCs)) := by ring
        linarith
      have hG_bd := rescaledG1_tail_bound hG_poly hc0 hL0 hXY
      have hterm1 : convFExp γ ε Y * rescaledG1 ε (X - Y) ≤ A * convFExp γ ε Y := by
        rw [mul_comm A]; exact mul_le_mul_of_nonneg_left hG_bd (convFExp_nonneg hγ ε Y)
      have hB_nn : 0 ≤ B * rescaledG1 ε (X - Y) := mul_nonneg (by positivity) (rescaledG1_nonneg ε _)
      linarith
    · have hY_gt : L / (2 * ceCs) < Y := lt_of_not_ge hY
      have hY0 : 0 < Y := lt_trans (by positivity) hY_gt
      have hYt : 0 < Y / ε ^ 2 := div_pos hY0 hε2
      have hfY : convFExp γ ε Y ≤ B := by
        simp only [convFExp, hY0, ↓reduceIte]
        have hexp := exp_neg_le_six_div_cube hYt
        have hY_pow : Y ^ (-3 : ℝ) ≤ (L / (2 * ceCs)) ^ (-3 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hY_gt.le (by norm_num)
        have h_eq1 : (ε ^ 2)⁻¹ * (Y / ε ^ 2) ^ (-3 : ℝ) = ε ^ 4 * Y ^ (-3 : ℝ) := by
          have hy3 : Y ^ (-3 : ℝ) = (Y ^ 3)⁻¹ := by
            rw [Real.rpow_neg hY0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          have hq3 : (Y / ε ^ 2) ^ (-3 : ℝ) = ((Y / ε ^ 2) ^ 3)⁻¹ := by
            rw [Real.rpow_neg hYt.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          rw [hq3, hy3]; field_simp [hε.ne', hY0.ne']
        have h_eq2 : (L / (2 * ceCs)) ^ (-3 : ℝ) = (2 * ceCs) ^ 3 * L ^ (-3 : ℝ) := by
          have hl3 : L ^ (-3 : ℝ) = (L ^ 3)⁻¹ := by
            rw [Real.rpow_neg hL0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          have hq3 : (L / (2 * ceCs)) ^ (-3 : ℝ) = ((L / (2 * ceCs)) ^ 3)⁻¹ := by
            rw [Real.rpow_neg (by positivity), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          rw [hq3, hl3]; field_simp [hL0.ne', hcs0.ne']
        calc γ * (ε ^ 2)⁻¹ * Real.exp (-Y / ε ^ 2)
            ≤ γ * (ε ^ 2)⁻¹ * (6 * (Y / ε ^ 2) ^ (-3 : ℝ)) := by
              rw [show -Y / ε ^ 2 = -(Y / ε ^ 2) by ring]; gcongr
          _ = 6 * γ * ((ε ^ 2)⁻¹ * (Y / ε ^ 2) ^ (-3 : ℝ)) := by ring
          _ = 6 * γ * (ε ^ 4 * Y ^ (-3 : ℝ)) := by rw [h_eq1]
          _ ≤ 6 * γ * (c⁻¹ * (L / (2 * ceCs)) ^ (-3 : ℝ)) := by gcongr
          _ = B := by rw [h_eq2]; dsimp [B]; ring
      have hterm2 : convFExp γ ε Y * rescaledG1 ε (X - Y) ≤ B * rescaledG1 ε (X - Y) :=
        mul_le_mul_of_nonneg_right hfY (rescaledG1_nonneg ε _)
      have hA_nn : 0 ≤ A * convFExp γ ε Y := mul_nonneg (by positivity) (convFExp_nonneg hγ ε Y)
      linarith
  have hk_shifted_int : Integrable (fun Y : ℝ => rescaledG1 ε (X - Y)) := hk_int.comp_sub_left X
  have hk_shifted_val : ∫ Y : ℝ, rescaledG1 ε (X - Y) = 1 := by
    have h1 := integral_sub_left_eq_self (rescaledG1 ε) volume X
    simpa [h1] using rescaledG1_integral hε
  have hf_val : ∫ Y : ℝ, convFExp γ ε Y = γ := by
    simpa only [Real.norm_of_nonneg (convFExp_nonneg hγ ε _)] using convFExp_integral_norm hγ hε
  have hL52 : L ^ (-(5 / 2 : ℝ)) ≤ L_min⁻¹ * L ^ (-(3 / 2 : ℝ)) := by
    have hL_eq : L ^ (-(5 / 2 : ℝ)) = L ^ (-1 : ℝ) * L ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_add hL0]; norm_num
    have hL1 : L ^ (-1 : ℝ) ≤ L_min⁻¹ := by rw [Real.rpow_neg_one]; exact inv_anti₀ hLmin hL
    rw [hL_eq]; gcongr
  have hL3 : L ^ (-3 : ℝ) ≤ L_min ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
    have hL_eq : L ^ (-3 : ℝ) = L ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_add hL0]; norm_num
    have hL32 : L ^ (-(3 / 2 : ℝ)) ≤ L_min ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hLmin hL (by norm_num)
    rw [hL_eq]; gcongr
  calc ∫ Y : ℝ, convFExp γ ε Y * rescaledG1 ε (X - Y)
      ≤ ∫ Y : ℝ, (A * convFExp γ ε Y + B * rescaledG1 ε (X - Y)) :=
        integral_mono hprod_int ((hf_int.const_mul A).add (hk_shifted_int.const_mul B)) hpiece
    _ = A * (∫ Y : ℝ, convFExp γ ε Y) + B * (∫ Y : ℝ, rescaledG1 ε (X - Y)) := by
        rw [integral_add (hf_int.const_mul A) (hk_shifted_int.const_mul B),
          integral_const_mul, integral_const_mul]
    _ = A * γ + B := by rw [hf_val, hk_shifted_val, mul_one]
    _ ≤ (γ * Cg * (4 * ceCs) ^ (5 / 2 : ℝ) * c⁻¹ * (L_min⁻¹ * L ^ (-(3 / 2 : ℝ)))) +
          (6 * γ * (2 * ceCs) ^ 3 * c⁻¹ * (L_min ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)))) := by
        dsimp [A, B]
        calc Cg * (4 * ceCs) ^ (5 / 2 : ℝ) * c⁻¹ * L ^ (-(5 / 2 : ℝ)) * γ +
              6 * γ * (2 * ceCs) ^ 3 * c⁻¹ * L ^ (-3 : ℝ)
            ≤ Cg * (4 * ceCs) ^ (5 / 2 : ℝ) * c⁻¹ * (L_min⁻¹ * L ^ (-(3 / 2 : ℝ))) * γ +
              6 * γ * (2 * ceCs) ^ 3 * c⁻¹ * (L_min ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ))) := by gcongr
          _ = _ := by ring
    _ ≤ M_e * c⁻¹ * L ^ (-(3 / 2 : ℝ)) := by
        have h1 : 0 ≤ c⁻¹ * L ^ (-(3 / 2 : ℝ)) := by positivity
        dsimp [M_e]; linarith

/-! ### 4. Smooth cutoff main term `convGL` and remainder `convHL` -/

/-- Smooth cutoff `χ_L(Y) = smoothTransition (4 c_s Y / L - 1)`, zero for `Y ≤ L / (4 c_s)` and one for `Y ≥ L / (2 c_s)`. -/
noncomputable def convChi (L Y : ℝ) : ℝ := Real.smoothTransition (4 * ceCs * Y / L - 1)

/-- Smooth main part `g_L(Y) = 1_{Y > 0} θ χ_L(Y) ρ_p(λ Y) Y^{-3/2}`. -/
noncomputable def convGL (θ p lam L Y : ℝ) : ℝ :=
  if 0 < Y then θ * convChi L Y * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ)) else 0

/-- Omitted cutoff remainder `h_L(Y) = w_full(Y) - g_L(Y)`. -/
noncomputable def convHL (p θ lam ε L Y : ℝ) : ℝ :=
  convWFull p θ lam ε Y - convGL θ p lam L Y

lemma convChi_eq_zero {L Y : ℝ} (hL : 0 < L) (hY : Y ≤ L / (4 * ceCs)) : convChi L Y = 0 := by
  unfold convChi; apply Real.smoothTransition.zero_of_nonpos
  have hcs0 : 0 < ceCs := ceCs_pos
  have h1 : 4 * ceCs * Y ≤ L := by
    calc 4 * ceCs * Y ≤ 4 * ceCs * (L / (4 * ceCs)) := by gcongr
      _ = L := by field_simp [hcs0.ne']
  rw [sub_nonpos, div_le_one hL]; exact h1

lemma convChi_eq_one {L Y : ℝ} (hL : 0 < L) (hY : L / (2 * ceCs) ≤ Y) : convChi L Y = 1 := by
  unfold convChi; apply Real.smoothTransition.one_of_one_le
  have hcs0 : 0 < ceCs := ceCs_pos
  have h1 : 2 * L ≤ 4 * ceCs * Y := by
    calc 2 * L = 4 * ceCs * (L / (2 * ceCs)) := by field_simp [hcs0.ne']; ring
      _ ≤ 4 * ceCs * Y := by gcongr
  rw [le_sub_iff_add_le, show (1 : ℝ) + 1 = 2 by norm_num, le_div_iff₀ hL]
  exact h1

lemma convHL_bounds {p θ lam L_min : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hθ : 0 ≤ θ) (hlam : 0 < lam)
    (hLmin : 0 < L_min) {c L : ℝ} (hc : (8 * ceCs / L_min) ^ (3 / 2 : ℝ) ≤ c) (hc1 : 1 ≤ c)
    (hL : L_min ≤ L) (Y : ℝ) :
    0 ≤ convHL p θ lam (liftEps c) L Y ∧
      convHL p θ lam (liftEps c) L Y ≤ (if 0 < Y then θ * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ)) else 0) ∧
      (L / (2 * ceCs) ≤ Y → convHL p θ lam (liftEps c) L Y = 0) := by
  have hc0 : 0 < c := by linarith
  have hL0 : 0 < L := hLmin.trans_le hL
  have hcs0 : 0 < ceCs := ceCs_pos
  have h2ε2 := two_eps_sq_le_of_c_ge hLmin hL hc hc0
  unfold convHL convWFull convGL
  split_ifs with hY
  · have h_eta_ge : convChi L Y ≤ convEta (Y / liftEps c ^ 2) := by
      by_cases hY1 : Y ≤ L / (4 * ceCs)
      · rw [convChi_eq_zero hL0 hY1]; exact convEta_nonneg _
      · have hY_gt : L / (4 * ceCs) < Y := lt_of_not_ge hY1
        have hY_eps : 2 ≤ Y / liftEps c ^ 2 := by
          rw [le_div_iff₀ (pow_pos (liftEps_pos hc0) 2)]
          linarith
        rw [convEta_eq_one hY_eps]
        exact Real.smoothTransition.le_one _
    have h_diff_le : convEta (Y / liftEps c ^ 2) - convChi L Y ≤ 1 := by
      unfold convChi
      linarith [convEta_le_one (Y / liftEps c ^ 2), Real.smoothTransition.nonneg (4 * ceCs * Y / L - 1)]
    have h_fac_nn : 0 ≤ θ * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ)) :=
      mul_nonneg (mul_nonneg hθ (convRho_nonneg p (mul_nonneg hlam.le hY.le))) (Real.rpow_nonneg hY.le _)
    have h_eq : θ * convEta (Y / liftEps c ^ 2) * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ)) -
          θ * convChi L Y * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ)) =
        (convEta (Y / liftEps c ^ 2) - convChi L Y) * (θ * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ))) := by ring
    refine ⟨?_, ?_, ?_⟩
    · rw [h_eq]; exact mul_nonneg (sub_nonneg.mpr h_eta_ge) h_fac_nn
    · rw [h_eq]
      calc (convEta (Y / liftEps c ^ 2) - convChi L Y) * (θ * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ)))
          ≤ 1 * (θ * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ))) := by gcongr
        _ = _ := one_mul _
    · intro hY2
      have hY_eps : 2 ≤ Y / liftEps c ^ 2 := by
        rw [le_div_iff₀ (pow_pos (liftEps_pos hc0) 2)]
        have : L / (4 * ceCs) ≤ L / (2 * ceCs) := div_le_div_of_nonneg_left hL0.le (by positivity) (by linarith)
        linarith
      rw [h_eq, convEta_eq_one hY_eps, convChi_eq_one hL0 hY2, sub_self, zero_mul]
  · simp

lemma convHL_integrable_and_tail {p θ lam L_min : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1)
    (hθ : 0 ≤ θ) (hlam : 0 < lam) (hLmin : 0 < L_min) :
    ∃ M_h_norm M_h_tail : ℝ, 0 ≤ M_h_norm ∧ 0 < M_h_tail ∧
      ∀ {c L : ℝ}, (8 * ceCs / L_min) ^ (3 / 2 : ℝ) ≤ c → 1 ≤ c → L_min ≤ L →
        Integrable (convHL p θ lam (liftEps c) L) ∧
        (∫ X : ℝ, ‖(realConv (convHL p θ lam (liftEps c) L) (rescaledG1 (liftEps c)) X : ℂ)‖ ≤ M_h_norm) ∧
        (∀ X : ℝ, (3 / (4 * ceCs)) * L < X →
          ‖(realConv (convHL p θ lam (liftEps c) L) (rescaledG1 (liftEps c)) X : ℂ)‖ ≤
            M_h_tail * c⁻¹ * L ^ (-(3 / 2 : ℝ))) := by
  have hcs0 : 0 < ceCs := ceCs_pos
  obtain ⟨Cg, hCg, hG_poly⟩ := convG1_le_poly
  let W₀ : ℝ → ℝ := fun Y => if 0 < Y then θ * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ)) else 0
  have hW0_int : Integrable W₀ := convRho_mul_rpow_integrable hp hp1 hθ hlam
  set M0 : ℝ := ∫ Y : ℝ, W₀ Y
  have hW0_nn : ∀ Y, 0 ≤ W₀ Y := fun Y => by
    dsimp [W₀]; split_ifs with hY; exact mul_nonneg (mul_nonneg hθ (convRho_nonneg p (mul_nonneg hlam.le hY.le))) (Real.rpow_nonneg hY.le _); rfl
  have hM0_nn : 0 ≤ M0 := integral_nonneg hW0_nn
  refine ⟨M0, M0 * Cg * (4 * ceCs) ^ (5 / 2 : ℝ) * L_min⁻¹ + 1, hM0_nn, by positivity,
    fun {c L} hc hc1 hL => ?_⟩
  have hc0 : 0 < c := by linarith
  have hL0 : 0 < L := hLmin.trans_le hL
  set ε : ℝ := liftEps c
  have hε : 0 < ε := liftEps_pos hc0
  have hh_meas : AEStronglyMeasurable (convHL p θ lam ε L) volume := by
    unfold convHL convWFull convGL convEta convChi convRho
    exact ((Measurable.ite measurableSet_Ioi (by measurability) measurable_const).sub
      (Measurable.ite measurableSet_Ioi (by measurability) measurable_const)).aestronglyMeasurable
  have hh_int : Integrable (convHL p θ lam ε L) := by
    refine hW0_int.mono' hh_meas (ae_of_all _ fun Y => ?_)
    have hb := convHL_bounds hp hp1 hθ hlam hLmin hc hc1 hL Y
    rw [Real.norm_of_nonneg hb.1]
    exact hb.2.1
  have hk_int := rescaledG1_integrable hε
  refine ⟨hh_int, ?_, ?_⟩
  · have hconv_int := integrable_realConv hh_int hk_int
    have h_nn : ∀ X : ℝ, 0 ≤ realConv (convHL p θ lam ε L) (rescaledG1 ε) X := fun X => by
      rw [realConv_apply]
      exact integral_nonneg fun Y => mul_nonneg (convHL_bounds hp hp1 hθ hlam hLmin hc hc1 hL Y).1 (rescaledG1_nonneg ε _)
    calc ∫ X : ℝ, ‖(realConv (convHL p θ lam ε L) (rescaledG1 ε) X : ℂ)‖
        = ∫ X : ℝ, realConv (convHL p θ lam ε L) (rescaledG1 ε) X := by
          refine integral_congr_ae (ae_of_all _ fun X => ?_)
          dsimp only
          rw [Complex.norm_real, Real.norm_of_nonneg (h_nn X)]
      _ = (∫ Y : ℝ, convHL p θ lam ε L Y) * (∫ Z : ℝ, rescaledG1 ε Z) := by
          unfold realConv
          exact integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hh_int hk_int
      _ = ∫ Y : ℝ, convHL p θ lam ε L Y := by rw [rescaledG1_integral hε, mul_one]
      _ ≤ ∫ Y : ℝ, W₀ Y := integral_mono hh_int hW0_int fun Y => (convHL_bounds hp hp1 hθ hlam hLmin hc hc1 hL Y).2.1
  · intro X hX
    have h_nn : 0 ≤ realConv (convHL p θ lam ε L) (rescaledG1 ε) X := by
      rw [realConv_apply]
      exact integral_nonneg fun Y => mul_nonneg (convHL_bounds hp hp1 hθ hlam hLmin hc hc1 hL Y).1 (rescaledG1_nonneg ε _)
    rw [Complex.norm_real, Real.norm_of_nonneg h_nn, realConv_apply]
    let B : ℝ := Cg * (4 * ceCs) ^ (5 / 2 : ℝ) * c⁻¹ * L ^ (-(5 / 2 : ℝ))
    have hbd_rescaled : ∀ Z : ℝ, |rescaledG1 ε Z| ≤ (ε ^ 2)⁻¹ * Cg := fun Z => by
      rw [abs_of_nonneg (rescaledG1_nonneg ε Z)]; unfold rescaledG1
      calc (ε ^ 2)⁻¹ * ceG1 (airyZero 1) (-Z / ε ^ 2)
          ≤ (ε ^ 2)⁻¹ * (Cg * (1 + |-Z / ε ^ 2|) ^ (-(5 / 2 : ℝ))) := by gcongr; exact hG_poly _
        _ ≤ (ε ^ 2)⁻¹ * (Cg * 1) := by gcongr; exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (-Z / ε ^ 2)]) (by norm_num)
        _ = _ := by ring
    have hprod_int : Integrable (fun Y : ℝ => convHL p θ lam ε L Y * rescaledG1 ε (X - Y)) := by
      refine (hh_int.norm.mul_const (max ((ε ^ 2)⁻¹ * Cg) 0)).mono'
        (hh_int.aestronglyMeasurable.mul ((rescaledG1_continuous hε).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
        (ae_of_all _ fun Y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left ((hbd_rescaled _).trans (le_max_left _ _)) (abs_nonneg _)
    have hpiece : ∀ Y : ℝ, convHL p θ lam ε L Y * rescaledG1 ε (X - Y) ≤ B * convHL p θ lam ε L Y := fun Y => by
      have hb := convHL_bounds hp hp1 hθ hlam hLmin hc hc1 hL Y
      by_cases hY : Y ≤ L / (2 * ceCs)
      · have hXY : L / (4 * ceCs) ≤ X - Y := by
          have h1 : L / (2 * ceCs) = 2 * (L / (4 * ceCs)) := by ring
          have h2 : 3 / (4 * ceCs) * L = 3 * (L / (4 * ceCs)) := by ring
          linarith
        have hG := rescaledG1_tail_bound hG_poly hc0 hL0 hXY
        rw [mul_comm B]; exact mul_le_mul_of_nonneg_left hG hb.1
      · have hY2 : L / (2 * ceCs) ≤ Y := (not_le.mp hY).le
        rw [hb.2.2 hY2, zero_mul, mul_zero]
    have hL52 : L ^ (-(5 / 2 : ℝ)) ≤ L_min⁻¹ * L ^ (-(3 / 2 : ℝ)) := by
      have hL_eq : L ^ (-(5 / 2 : ℝ)) = L ^ (-1 : ℝ) * L ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hL0]; norm_num
      have hL1 : L ^ (-1 : ℝ) ≤ L_min⁻¹ := by rw [Real.rpow_neg_one]; exact inv_anti₀ hLmin hL
      rw [hL_eq]; gcongr
    calc ∫ Y : ℝ, convHL p θ lam ε L Y * rescaledG1 ε (X - Y)
        ≤ ∫ Y : ℝ, B * convHL p θ lam ε L Y := integral_mono hprod_int (hh_int.const_mul B) hpiece
      _ = B * ∫ Y : ℝ, convHL p θ lam ε L Y := integral_const_mul _ _
      _ ≤ B * M0 := by gcongr; exact integral_mono hh_int hW0_int fun Y => (convHL_bounds hp hp1 hθ hlam hLmin hc hc1 hL Y).2.1
      _ ≤ (M0 * Cg * (4 * ceCs) ^ (5 / 2 : ℝ) * L_min⁻¹ + 1) * c⁻¹ * L ^ (-(3 / 2 : ℝ)) := by
          dsimp [B]
          have h1 : 0 ≤ c⁻¹ * L ^ (-(3 / 2 : ℝ)) := by positivity
          calc Cg * (4 * ceCs) ^ (5 / 2 : ℝ) * c⁻¹ * L ^ (-(5 / 2 : ℝ)) * M0
              ≤ Cg * (4 * ceCs) ^ (5 / 2 : ℝ) * c⁻¹ * (L_min⁻¹ * L ^ (-(3 / 2 : ℝ))) * M0 := by gcongr
            _ = (M0 * Cg * (4 * ceCs) ^ (5 / 2 : ℝ) * L_min⁻¹) * c⁻¹ * L ^ (-(3 / 2 : ℝ)) := by ring
            _ ≤ _ := by nlinarith

/-! ### 5. Derivative and `L²` bounds for `convGL` -/

/-- Derivative of `convGL θ p lam L`. -/
noncomputable def convGLDeriv (θ p lam L Y : ℝ) : ℝ :=
  if 0 < Y then
    θ * ((4 * ceCs / L * deriv Real.smoothTransition (4 * ceCs * Y / L - 1)) * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ)) +
      convChi L Y * (p * (lam * Y / (1 + lam * Y)) ^ (p - 1) * (lam / (1 + lam * Y) ^ 2)) * Y ^ (-(3 / 2 : ℝ)) +
      convChi L Y * convRho p (lam * Y) * (-(3 / 2 : ℝ) * Y ^ (-(5 / 2 : ℝ))))
  else 0

lemma convGL_hasDerivAt {θ p lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) (Y : ℝ) :
    HasDerivAt (convGL θ p lam L) (convGLDeriv θ p lam L Y) Y := by
  have hcs0 : 0 < ceCs := ceCs_pos
  obtain ⟨_, _, hst⟩ := smoothTransition_deriv_bound
  by_cases hY : Y < L / (8 * ceCs)
  · have h_open : IsOpen (Iio (L / (8 * ceCs))) := isOpen_Iio
    have hev : convGL θ p lam L =ᶠ[𝓝 Y] fun _ => (0 : ℝ) := by
      refine Filter.eventually_of_mem (h_open.mem_nhds hY) fun y hy => ?_
      have hy4 : y ≤ L / (4 * ceCs) := le_trans hy.le (by gcongr; norm_num)
      unfold convGL
      split_ifs with hy0
      · rw [convChi_eq_zero hL hy4]; ring
      · rfl
    have h0 : convGLDeriv θ p lam L Y = 0 := by
      have hY4 : Y ≤ L / (4 * ceCs) := le_trans hY.le (by gcongr; norm_num)
      have harg : 4 * ceCs * Y / L - 1 ≤ 0 := by
        have h1 : 4 * ceCs * Y ≤ L := calc 4 * ceCs * Y ≤ 4 * ceCs * (L / (4 * ceCs)) := by gcongr
          _ = L := by field_simp [hcs0.ne']
        rw [sub_nonpos, div_le_one hL]; exact h1
      unfold convGLDeriv
      split_ifs with hY0
      · rw [convChi_eq_zero hL hY4, (hst _).2.1 harg]; ring
      · rfl
    rw [h0]
    exact (hasDerivAt_const Y (0 : ℝ)).congr_of_eventuallyEq hev
  · have hY8 : L / (8 * ceCs) ≤ Y := not_lt.mp hY
    have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY8
    have hev : convGL θ p lam L =ᶠ[𝓝 Y]
        fun y => θ * convChi L y * convRho p (lam * y) * y ^ (-(3 / 2 : ℝ)) := by
      refine Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hY0) fun y hy => ?_
      simp [convGL, mem_Ioi.mp hy]
    have hd_chi : HasDerivAt (convChi L) (4 * ceCs / L * deriv Real.smoothTransition (4 * ceCs * Y / L - 1)) Y := by
      have hcd : ContDiff ℝ (1 : ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
      have h_st : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (4 * ceCs * Y / L - 1)) (4 * ceCs * Y / L - 1) :=
        (hcd.differentiable (by simp) _).hasDerivAt
      have h_lin : HasDerivAt (fun y : ℝ => 4 * ceCs * y / L - 1) (4 * ceCs / L) Y :=
        ((((hasDerivAt_id Y).const_mul (4 * ceCs)).div_const L).sub_const 1).congr_deriv (by ring)
      exact (h_st.comp Y h_lin).congr_deriv (by ring)
    have hd_rho : HasDerivAt (fun y : ℝ => convRho p (lam * y))
        (p * (lam * Y / (1 + lam * Y)) ^ (p - 1) * (lam / (1 + lam * Y) ^ 2)) Y := by
      have hden : 0 < 1 + lam * Y := by positivity
      have hq : 0 < lam * Y / (1 + lam * Y) := by positivity
      have h_in : HasDerivAt (fun y : ℝ => lam * y / (1 + lam * y))
          ((lam * 1 * (1 + lam * Y) - lam * Y * (lam * 1)) / (1 + lam * Y) ^ 2) Y :=
        (((hasDerivAt_id Y).const_mul lam).div (((hasDerivAt_id Y).const_mul lam).const_add 1) hden.ne').congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun _ => rfl)
      have h_in' : HasDerivAt (fun y : ℝ => lam * y / (1 + lam * y)) (lam / (1 + lam * Y) ^ 2) Y :=
        h_in.congr_deriv (by ring)
      have hrp := h_in'.rpow_const (Or.inl hq.ne') (p := p)
      exact hrp.congr_deriv (by ring)
    have hd_pow : HasDerivAt (fun y : ℝ => y ^ (-(3 / 2 : ℝ))) (1 * (-(3 / 2 : ℝ)) * Y ^ (-(3 / 2 : ℝ) - 1)) Y :=
      ((hasDerivAt_id Y).rpow_const (Or.inl hY0.ne') (p := -(3 / 2 : ℝ))).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)
    have hd_pow' : HasDerivAt (fun y : ℝ => y ^ (-(3 / 2 : ℝ))) (-(3 / 2 : ℝ) * Y ^ (-(5 / 2 : ℝ))) Y := by
      refine hd_pow.congr_deriv ?_
      rw [show -(3 / 2 : ℝ) - 1 = -(5 / 2 : ℝ) by norm_num]; ring
    have hd_prod1 : HasDerivAt (fun y : ℝ => θ * convChi L y * convRho p (lam * y))
        ((θ * (4 * ceCs / L * deriv Real.smoothTransition (4 * ceCs * Y / L - 1))) * convRho p (lam * Y) +
          (θ * convChi L Y) * (p * (lam * Y / (1 + lam * Y)) ^ (p - 1) * (lam / (1 + lam * Y) ^ 2))) Y :=
      ((hd_chi.const_mul θ).mul hd_rho).congr_deriv (by ring)
    have hd_prod2 := (hd_prod1.mul hd_pow').congr_deriv (by
      show _ = convGLDeriv θ p lam L Y
      simp only [convGLDeriv, hY0, ↓reduceIte]; ring)
    exact hd_prod2.congr_of_eventuallyEq hev

lemma convGL_bounds {θ p lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hθ : 0 ≤ θ) (hlam : 0 < lam) :
    ∃ M_st > 0, ∀ {L : ℝ}, 0 < L →
      (∀ Y : ℝ, Y ≤ L / (4 * ceCs) → convGL θ p lam L Y = 0 ∧ convGLDeriv θ p lam L Y = 0) ∧
      (∀ Y : ℝ, L / (4 * ceCs) < Y →
        0 ≤ convGL θ p lam L Y ∧ convGL θ p lam L Y ≤ θ * Y ^ (-(3 / 2 : ℝ)) ∧
        |convGLDeriv θ p lam L Y| ≤ θ * (2 * M_st + 5 / 2) * Y ^ (-(5 / 2 : ℝ))) := by
  have hcs0 : 0 < ceCs := ceCs_pos
  obtain ⟨M_st, hMst, hst⟩ := smoothTransition_deriv_bound
  refine ⟨M_st, hMst, fun {L} hL => ⟨fun Y hY => ?_, fun Y hY => ?_⟩⟩
  · have harg : 4 * ceCs * Y / L - 1 ≤ 0 := by
      have h1 : 4 * ceCs * Y ≤ L := calc 4 * ceCs * Y ≤ 4 * ceCs * (L / (4 * ceCs)) := by gcongr
        _ = L := by field_simp [hcs0.ne']
      rw [sub_nonpos, div_le_one hL]; exact h1
    unfold convGL convGLDeriv
    split_ifs with hY0
    · rw [convChi_eq_zero hL hY, (hst _).2.1 harg]; simp
    · exact ⟨rfl, rfl⟩
  · have hY0 : 0 < Y := lt_trans (by positivity) hY
    have hχ_nn : 0 ≤ convChi L Y := Real.smoothTransition.nonneg _
    have hχ_le : convChi L Y ≤ 1 := Real.smoothTransition.le_one _
    have hρ_nn : 0 ≤ convRho p (lam * Y) := convRho_nonneg p (mul_nonneg hlam.le hY0.le)
    have hρ_le : convRho p (lam * Y) ≤ 1 := convRho_le_one (by linarith) (mul_nonneg hlam.le hY0.le)
    have hYp : 0 ≤ Y ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hY0.le _
    refine ⟨?_, ?_, ?_⟩
    · unfold convGL; simp only [hY0, ↓reduceIte]; positivity
    · unfold convGL; simp only [hY0, ↓reduceIte]
      have h1 : convChi L Y * convRho p (lam * Y) ≤ 1 := by nlinarith
      calc θ * convChi L Y * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ))
          = θ * (convChi L Y * convRho p (lam * Y)) * Y ^ (-(3 / 2 : ℝ)) := by ring
        _ ≤ θ * 1 * Y ^ (-(3 / 2 : ℝ)) := by gcongr
        _ = _ := by ring
    · unfold convGLDeriv; simp only [hY0, ↓reduceIte]
      have ht1 : |4 * ceCs / L * deriv Real.smoothTransition (4 * ceCs * Y / L - 1) * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ))| ≤
          2 * M_st * Y ^ (-(5 / 2 : ℝ)) := by
        by_cases hY2 : L / (2 * ceCs) ≤ Y
        · have harg : 1 ≤ 4 * ceCs * Y / L - 1 := by
            have h1 : 2 * L ≤ 4 * ceCs * Y := by
              calc 2 * L = 4 * ceCs * (L / (2 * ceCs)) := by field_simp [hcs0.ne']; ring
                _ ≤ 4 * ceCs * Y := by gcongr
            rw [le_sub_iff_add_le, show (1 : ℝ) + 1 = 2 by norm_num, le_div_iff₀ hL]; exact h1
          rw [(hst _).2.2 harg]
          simp only [mul_zero, zero_mul, abs_zero]
          positivity
        · have hY_lt : Y ≤ L / (2 * ceCs) := (not_le.mp hY2).le
          have hL_inv : 4 * ceCs / L ≤ 2 * Y⁻¹ := by
            have h1 : 2 * ceCs * Y ≤ L := by
              calc 2 * ceCs * Y ≤ 2 * ceCs * (L / (2 * ceCs)) := by gcongr
                _ = L := by field_simp [hcs0.ne']
            rw [div_le_iff₀ hL]
            calc 4 * ceCs = 2 * Y⁻¹ * (2 * ceCs * Y) := by field_simp [hY0.ne']; ring
              _ ≤ 2 * Y⁻¹ * L := by gcongr
          have hd_le := (hst (4 * ceCs * Y / L - 1)).1
          have hYp_split : Y⁻¹ * Y ^ (-(3 / 2 : ℝ)) = Y ^ (-(5 / 2 : ℝ)) := by
            rw [← Real.rpow_neg_one, ← Real.rpow_add hY0]; norm_num
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * ceCs / L),
            abs_of_nonneg hρ_nn, abs_of_nonneg hYp]
          calc (4 * ceCs / L) * |deriv Real.smoothTransition (4 * ceCs * Y / L - 1)| * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ))
              ≤ (2 * Y⁻¹) * M_st * 1 * Y ^ (-(3 / 2 : ℝ)) := by gcongr
            _ = 2 * M_st * (Y⁻¹ * Y ^ (-(3 / 2 : ℝ))) := by ring
            _ = 2 * M_st * Y ^ (-(5 / 2 : ℝ)) := by rw [hYp_split]
      have ht2 : |convChi L Y * (p * (lam * Y / (1 + lam * Y)) ^ (p - 1) * (lam / (1 + lam * Y) ^ 2)) * Y ^ (-(3 / 2 : ℝ))| ≤
          1 * Y ^ (-(5 / 2 : ℝ)) := by
        have h_den : 0 < 1 + lam * Y := by positivity
        have h_base : 0 < lam * Y / (1 + lam * Y) := by positivity
        have h_eq : (lam * Y / (1 + lam * Y)) ^ (p - 1) * (lam / (1 + lam * Y) ^ 2) =
            convRho p (lam * Y) / (Y * (1 + lam * Y)) := by
          unfold convRho
          rw [Real.rpow_sub h_base, Real.rpow_one]
          field_simp [hlam.ne', hY0.ne', h_den.ne']
        have hYp_split : Y⁻¹ * Y ^ (-(3 / 2 : ℝ)) = Y ^ (-(5 / 2 : ℝ)) := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hY0]; norm_num
        rw [mul_assoc p, h_eq, abs_mul, abs_mul, abs_of_nonneg hχ_nn, abs_of_nonneg hYp,
          abs_of_nonneg (by positivity : 0 ≤ p * (convRho p (lam * Y) / (Y * (1 + lam * Y))))]
        have h_frac : convRho p (lam * Y) / (Y * (1 + lam * Y)) ≤ Y⁻¹ := by
          rw [div_le_iff₀ (by positivity)]
          calc convRho p (lam * Y) ≤ 1 := hρ_le
            _ ≤ 1 + lam * Y := by linarith [mul_pos hlam hY0]
            _ = Y⁻¹ * (Y * (1 + lam * Y)) := by field_simp [hY0.ne']
        calc convChi L Y * (p * (convRho p (lam * Y) / (Y * (1 + lam * Y)))) * Y ^ (-(3 / 2 : ℝ))
            ≤ 1 * (1 * Y⁻¹) * Y ^ (-(3 / 2 : ℝ)) := by
              gcongr
          _ = 1 * (Y⁻¹ * Y ^ (-(3 / 2 : ℝ))) := by ring
          _ = 1 * Y ^ (-(5 / 2 : ℝ)) := by rw [hYp_split]
      have ht3 : |convChi L Y * convRho p (lam * Y) * (-(3 / 2 : ℝ) * Y ^ (-(5 / 2 : ℝ)))| ≤
          (3 / 2 : ℝ) * Y ^ (-(5 / 2 : ℝ)) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hχ_nn, abs_of_nonneg hρ_nn, abs_mul,
          show |-(3 / 2 : ℝ)| = 3 / 2 by norm_num, abs_of_nonneg (Real.rpow_nonneg hY0.le _)]
        have h1 : convChi L Y * convRho p (lam * Y) ≤ 1 := by nlinarith
        calc (convChi L Y * convRho p (lam * Y)) * ((3 / 2 : ℝ) * Y ^ (-(5 / 2 : ℝ)))
            ≤ 1 * ((3 / 2 : ℝ) * Y ^ (-(5 / 2 : ℝ))) := by gcongr
          _ = _ := one_mul _
      rw [abs_mul, abs_of_nonneg hθ]
      have htri : |4 * ceCs / L * deriv Real.smoothTransition (4 * ceCs * Y / L - 1) * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ)) +
            convChi L Y * (p * (lam * Y / (1 + lam * Y)) ^ (p - 1) * (lam / (1 + lam * Y) ^ 2)) * Y ^ (-(3 / 2 : ℝ)) +
            convChi L Y * convRho p (lam * Y) * (-(3 / 2 : ℝ) * Y ^ (-(5 / 2 : ℝ)))| ≤
          (2 * M_st + 5 / 2) * Y ^ (-(5 / 2 : ℝ)) := by
        calc _ ≤ |4 * ceCs / L * deriv Real.smoothTransition (4 * ceCs * Y / L - 1) * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ)) +
              convChi L Y * (p * (lam * Y / (1 + lam * Y)) ^ (p - 1) * (lam / (1 + lam * Y) ^ 2)) * Y ^ (-(3 / 2 : ℝ))| +
              |convChi L Y * convRho p (lam * Y) * (-(3 / 2 : ℝ) * Y ^ (-(5 / 2 : ℝ)))| := abs_add_le _ _
          _ ≤ (|4 * ceCs / L * deriv Real.smoothTransition (4 * ceCs * Y / L - 1) * convRho p (lam * Y) * Y ^ (-(3 / 2 : ℝ))| +
              |convChi L Y * (p * (lam * Y / (1 + lam * Y)) ^ (p - 1) * (lam / (1 + lam * Y) ^ 2)) * Y ^ (-(3 / 2 : ℝ))|) +
              |convChi L Y * convRho p (lam * Y) * (-(3 / 2 : ℝ) * Y ^ (-(5 / 2 : ℝ)))| := by gcongr; exact abs_add_le _ _
          _ ≤ (2 * M_st * Y ^ (-(5 / 2 : ℝ)) + 1 * Y ^ (-(5 / 2 : ℝ))) + (3 / 2 : ℝ) * Y ^ (-(5 / 2 : ℝ)) := by gcongr
          _ = (2 * M_st + 5 / 2) * Y ^ (-(5 / 2 : ℝ)) := by ring
      calc θ * |_| ≤ θ * ((2 * M_st + 5 / 2) * Y ^ (-(5 / 2 : ℝ))) := mul_le_mul_of_nonneg_left htri hθ
        _ = _ := by ring

lemma integrable_tail_rpow {a r : ℝ} (ha : 0 < a) (hr : r < -1) :
    Integrable (fun Y : ℝ => if a < Y then Y ^ r else 0) ∧
      ∫ Y : ℝ, (if a < Y then Y ^ r else 0) = -a ^ (r + 1) / (r + 1) := by
  have hi : IntegrableOn (fun Y : ℝ => Y ^ r) (Ioi a) := integrableOn_Ioi_rpow_of_lt hr ha
  have heq : (fun Y : ℝ => if a < Y then Y ^ r else 0) = (Ioi a).indicator (fun Y => Y ^ r) := by
    funext Y; by_cases hY : a < Y <;> simp [hY, mem_Ioi]
  rw [heq]
  refine ⟨(integrable_indicator_iff measurableSet_Ioi).mpr hi, ?_⟩
  rw [integral_indicator measurableSet_Ioi, integral_Ioi_rpow_of_lt hr ha]

lemma convGL_integrable_and_L2 {θ p lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hθ : 0 ≤ θ)
    (hlam : 0 < lam) :
    ∃ C_g > 0, ∀ {L : ℝ}, 0 < L →
      Continuous (convGL θ p lam L) ∧ Integrable (convGL θ p lam L) ∧
      Integrable (convGLDeriv θ p lam L) ∧
      (∃ Mg Mg' : ℝ, 0 ≤ Mg ∧ 0 ≤ Mg' ∧ (∀ Y, |convGL θ p lam L Y| ≤ Mg) ∧
        (∀ Y, |convGLDeriv θ p lam L Y| ≤ Mg')) ∧
      L ^ (-2 : ℝ) * (∫ Y : ℝ, |convGL θ p lam L Y| ^ 2) + ∫ Y : ℝ, |convGLDeriv θ p lam L Y| ^ 2 ≤
        C_g * L ^ (-4 : ℝ) := by
  have hcs0 : 0 < ceCs := ceCs_pos
  obtain ⟨M_st, hMst, hbd⟩ := convGL_bounds hp hp1 hθ hlam
  let C_g : ℝ := (1 / 2 : ℝ) * θ ^ 2 * (4 * ceCs) ^ 2 +
    (1 / 4 : ℝ) * (θ * (2 * M_st + 5 / 2)) ^ 2 * (4 * ceCs) ^ 4 + 1
  refine ⟨C_g, by positivity, fun {L} hL => ?_⟩
  obtain ⟨hleft, hright⟩ := hbd hL
  set a : ℝ := L / (4 * ceCs)
  have ha : 0 < a := by positivity
  have hcont : Continuous (convGL θ p lam L) :=
    continuous_iff_continuousAt.mpr fun Y => (convGL_hasDerivAt hlam hL Y).continuousAt
  have hderiv_eq : convGLDeriv θ p lam L = deriv (convGL θ p lam L) :=
    funext fun Y => (convGL_hasDerivAt hlam hL Y).deriv.symm
  have hm_deriv : AEStronglyMeasurable (convGLDeriv θ p lam L) volume := by
    have hcd : ContDiff ℝ (1 : ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
    have hcont_st : Continuous (deriv Real.smoothTransition) := hcd.continuous_deriv (by simp)
    unfold convGLDeriv convChi convRho
    exact (Measurable.ite measurableSet_Ioi (by measurability) measurable_const).aestronglyMeasurable
  obtain ⟨hi32, _⟩ := integrable_tail_rpow ha (r := -(3 / 2 : ℝ)) (by norm_num)
  obtain ⟨hi52, _⟩ := integrable_tail_rpow ha (r := -(5 / 2 : ℝ)) (by norm_num)
  obtain ⟨hi3, hint3⟩ := integrable_tail_rpow ha (r := -3) (by norm_num)
  obtain ⟨hi5, hint5⟩ := integrable_tail_rpow ha (r := -5) (by norm_num)
  have hg_int : Integrable (convGL θ p lam L) := by
    refine (hi32.const_mul θ).mono' hcont.aestronglyMeasurable (ae_of_all _ fun Y => ?_)
    rw [Real.norm_eq_abs]
    by_cases hY : a < Y
    · simp only [hY, ↓reduceIte, abs_of_nonneg (hright Y hY).1]; exact (hright Y hY).2.1
    · simp only [hY, ↓reduceIte, mul_zero, (hleft Y (not_lt.mp hY)).1, abs_zero, le_refl]
  have hdg_int : Integrable (convGLDeriv θ p lam L) := by
    refine (hi52.const_mul (θ * (2 * M_st + 5 / 2))).mono' hm_deriv (ae_of_all _ fun Y => ?_)
    rw [Real.norm_eq_abs]
    by_cases hY : a < Y
    · simp only [hY, ↓reduceIte]; exact (hright Y hY).2.2
    · simp only [hY, ↓reduceIte, mul_zero, (hleft Y (not_lt.mp hY)).2, abs_zero, le_refl]
  have hMg : ∀ Y, |convGL θ p lam L Y| ≤ θ * a ^ (-(3 / 2 : ℝ)) := fun Y => by
    by_cases hY : a < Y
    · rw [abs_of_nonneg (hright Y hY).1]
      exact (hright Y hY).2.1.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos ha hY.le (by norm_num)) hθ)
    · rw [(hleft Y (not_lt.mp hY)).1, abs_zero]; positivity
  have hMg' : ∀ Y, |convGLDeriv θ p lam L Y| ≤ θ * (2 * M_st + 5 / 2) * a ^ (-(5 / 2 : ℝ)) := fun Y => by
    by_cases hY : a < Y
    · exact (hright Y hY).2.2.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos ha hY.le (by norm_num)) (by positivity))
    · rw [(hleft Y (not_lt.mp hY)).2, abs_zero]; positivity
  have hg_sq_int : Integrable (fun Y => |convGL θ p lam L Y| ^ 2) := by
    refine (hi3.const_mul (θ ^ 2)).mono' (hcont.abs.pow 2).aestronglyMeasurable (ae_of_all _ fun Y => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    by_cases hY : a < Y
    · have hY0 : 0 < Y := ha.trans hY
      simp only [hY, ↓reduceIte, abs_of_nonneg (hright Y hY).1]
      have hsq : (θ * Y ^ (-(3 / 2 : ℝ))) ^ 2 = θ ^ 2 * Y ^ (-3 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast (Y ^ _), ← Real.rpow_mul hY0.le]; norm_num
      calc convGL θ p lam L Y ^ 2 ≤ (θ * Y ^ (-(3 / 2 : ℝ))) ^ 2 := by
            gcongr; exact (hright Y hY).1; exact (hright Y hY).2.1
        _ = _ := hsq
    · simp only [hY, ↓reduceIte, mul_zero, (hleft Y (not_lt.mp hY)).1, abs_zero]; norm_num
  have hdg_sq_int : Integrable (fun Y => |convGLDeriv θ p lam L Y| ^ 2) := by
    refine (hi5.const_mul ((θ * (2 * M_st + 5 / 2)) ^ 2)).mono'
      ((continuous_pow 2 |>.comp continuous_abs).comp_aestronglyMeasurable hm_deriv) (ae_of_all _ fun Y => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    by_cases hY : a < Y
    · have hY0 : 0 < Y := ha.trans hY
      simp only [hY, ↓reduceIte]
      have hsq : (θ * (2 * M_st + 5 / 2) * Y ^ (-(5 / 2 : ℝ))) ^ 2 =
          (θ * (2 * M_st + 5 / 2)) ^ 2 * Y ^ (-5 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast (Y ^ _), ← Real.rpow_mul hY0.le]; norm_num
      calc |convGLDeriv θ p lam L Y| ^ 2 ≤ (θ * (2 * M_st + 5 / 2) * Y ^ (-(5 / 2 : ℝ))) ^ 2 :=
            sq_le_sq' (by linarith [abs_nonneg (convGLDeriv θ p lam L Y), (hright Y hY).2.2]) (hright Y hY).2.2
        _ = _ := hsq
    · simp only [hY, ↓reduceIte, mul_zero, (hleft Y (not_lt.mp hY)).2, abs_zero]; norm_num
  have hint_g2 : ∫ Y : ℝ, |convGL θ p lam L Y| ^ 2 ≤ (1 / 2 : ℝ) * θ ^ 2 * (4 * ceCs) ^ 2 * L ^ (-2 : ℝ) := by
    have h1 : ∫ Y : ℝ, |convGL θ p lam L Y| ^ 2 ≤ ∫ Y : ℝ, θ ^ 2 * (if a < Y then Y ^ (-3 : ℝ) else 0) := by
      refine integral_mono hg_sq_int (hi3.const_mul (θ ^ 2)) fun Y => ?_
      by_cases hY : a < Y
      · have hY0 : 0 < Y := ha.trans hY
        simp only [hY, ↓reduceIte, abs_of_nonneg (hright Y hY).1]
        have hsq : (θ * Y ^ (-(3 / 2 : ℝ))) ^ 2 = θ ^ 2 * Y ^ (-3 : ℝ) := by
          rw [mul_pow, ← Real.rpow_natCast (Y ^ _), ← Real.rpow_mul hY0.le]; norm_num
        exact (pow_le_pow_left₀ (hright Y hY).1 (hright Y hY).2.1 2).trans_eq hsq
      · simp only [hY, ↓reduceIte, mul_zero, (hleft Y (not_lt.mp hY)).1, abs_zero]; norm_num
    rw [integral_const_mul, hint3] at h1
    have ha2 : a ^ (-3 + 1 : ℝ) = (4 * ceCs) ^ 2 * L ^ (-2 : ℝ) := by
      have ha_pos : 0 < a := ha
      rw [show (-3 + 1 : ℝ) = -2 by norm_num, Real.rpow_neg ha_pos.le, Real.rpow_neg hL.le,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
      dsimp [a]; field_simp [hL.ne', hcs0.ne']
    refine h1.trans_eq ?_
    rw [show -a ^ (-3 + 1 : ℝ) / (-3 + 1 : ℝ) = (1 / 2 : ℝ) * a ^ (-3 + 1 : ℝ) by ring, ha2]
    ring
  have hint_dg2 : ∫ Y : ℝ, |convGLDeriv θ p lam L Y| ^ 2 ≤
      (1 / 4 : ℝ) * (θ * (2 * M_st + 5 / 2)) ^ 2 * (4 * ceCs) ^ 4 * L ^ (-4 : ℝ) := by
    have h1 : ∫ Y : ℝ, |convGLDeriv θ p lam L Y| ^ 2 ≤
        ∫ Y : ℝ, (θ * (2 * M_st + 5 / 2)) ^ 2 * (if a < Y then Y ^ (-5 : ℝ) else 0) := by
      refine integral_mono hdg_sq_int (hi5.const_mul _) fun Y => ?_
      by_cases hY : a < Y
      · have hY0 : 0 < Y := ha.trans hY
        simp only [hY, ↓reduceIte]
        have hsq : (θ * (2 * M_st + 5 / 2) * Y ^ (-(5 / 2 : ℝ))) ^ 2 =
            (θ * (2 * M_st + 5 / 2)) ^ 2 * Y ^ (-5 : ℝ) := by
          rw [mul_pow, ← Real.rpow_natCast (Y ^ _), ← Real.rpow_mul hY0.le]; norm_num
        exact (pow_le_pow_left₀ (abs_nonneg _) (hright Y hY).2.2 2).trans_eq hsq
      · simp only [hY, ↓reduceIte, mul_zero, (hleft Y (not_lt.mp hY)).2, abs_zero]; norm_num
    rw [integral_const_mul, hint5] at h1
    have ha4 : a ^ (-5 + 1 : ℝ) = (4 * ceCs) ^ 4 * L ^ (-4 : ℝ) := by
      have ha_pos : 0 < a := ha
      rw [show (-5 + 1 : ℝ) = -4 by norm_num, Real.rpow_neg ha_pos.le, Real.rpow_neg hL.le,
        show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
      dsimp [a]; field_simp [hL.ne', hcs0.ne']
    refine h1.trans_eq ?_
    rw [show -a ^ (-5 + 1 : ℝ) / (-5 + 1 : ℝ) = (1 / 4 : ℝ) * a ^ (-5 + 1 : ℝ) by ring, ha4]
    ring
  refine ⟨hcont, hg_int, hdg_int, ⟨θ * a ^ (-(3 / 2 : ℝ)), θ * (2 * M_st + 5 / 2) * a ^ (-(5 / 2 : ℝ)),
    by positivity, by positivity, hMg, hMg'⟩, ?_⟩
  have hL4 : L ^ (-2 : ℝ) * L ^ (-2 : ℝ) = L ^ (-4 : ℝ) := by
    rw [← Real.rpow_add hL]; norm_num
  have hterm1 : L ^ (-2 : ℝ) * (∫ Y : ℝ, |convGL θ p lam L Y| ^ 2) ≤
      (1 / 2 : ℝ) * θ ^ 2 * (4 * ceCs) ^ 2 * L ^ (-4 : ℝ) := by
    calc L ^ (-2 : ℝ) * (∫ Y : ℝ, |convGL θ p lam L Y| ^ 2)
        ≤ L ^ (-2 : ℝ) * ((1 / 2 : ℝ) * θ ^ 2 * (4 * ceCs) ^ 2 * L ^ (-2 : ℝ)) := by gcongr
      _ = (1 / 2 : ℝ) * θ ^ 2 * (4 * ceCs) ^ 2 * (L ^ (-2 : ℝ) * L ^ (-2 : ℝ)) := by ring
      _ = _ := by rw [hL4]
  have hL4_nn : 0 ≤ L ^ (-4 : ℝ) := Real.rpow_nonneg hL.le _
  calc L ^ (-2 : ℝ) * (∫ Y : ℝ, |convGL θ p lam L Y| ^ 2) + ∫ Y : ℝ, |convGLDeriv θ p lam L Y| ^ 2
      ≤ (1 / 2 : ℝ) * θ ^ 2 * (4 * ceCs) ^ 2 * L ^ (-4 : ℝ) +
          (1 / 4 : ℝ) * (θ * (2 * M_st + 5 / 2)) ^ 2 * (4 * ceCs) ^ 4 * L ^ (-4 : ℝ) := add_le_add hterm1 hint_dg2
    _ ≤ C_g * L ^ (-4 : ℝ) := by dsimp [C_g]; nlinarith

/-! ### 6. Main theorem `convSourceFamily_far_transfer` (`ceo:conv` (7)) -/

private lemma convRho_mono {p t₁ t₂ : ℝ} (hp : 0 ≤ p) (ht₁ : 0 < t₁) (h : t₁ ≤ t₂) :
    convRho p t₁ ≤ convRho p t₂ := by
  unfold convRho
  refine Real.rpow_le_rpow (by positivity) ?_ hp
  have ht₂ : 0 < t₂ := lt_of_lt_of_le ht₁ h
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **Far-range transfer lower bound (`ceo:conv` (7))**:
for `p ∈ (1/2, 1)`, `γ ≥ 0`, `θ > 0`, `λ > 0`, `L_min > 0`, and spline order `m ≥ 4`, there exists
`b_F > 0` independent of `(κ, m, c)` such that for every `κ > 0`, for all sufficiently large `c`
and all `ξ > 0` with `L = log(π² ξ) ≥ L_min`,
`(c ξ) · Re(I_main[S_c](ξ)) ≥ (b_F - C_err c^{-1/6}) (1 + L)^{-3/2}`. -/
theorem convSourceFamily_far_transfer
    {p γ θ lam L_min : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1)
    (hγ : 0 ≤ γ) (hθ : 0 < θ) (hlam : 0 < lam) (hLmin : 0 < L_min)
    {m : ℕ} (hm : 4 ≤ m) :
    ∃ b_F > 0, ∀ {κ : ℝ}, 0 < κ → ∃ C_err > 0, ∃ c₀ ≥ (2 : ℝ),
      ∀ {c ξ : ℝ}, c₀ ≤ c → 0 < ξ →
        let L := Real.log (Real.pi ^ 2 * ξ)
        L_min ≤ L →
        (c * ξ) * (iMain (convSourceFamily p γ θ lam c) (κ * liftEps c) m c ξ).re ≥
          (b_F - C_err * c ^ (-(1 / 6 : ℝ))) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
  have hcs0 : 0 < ceCs := ceCs_pos
  have hk0 : 0 < ceK := ceK_pos
  set b_F : ℝ := ceK * ceCs ^ (1 / 2 : ℝ) * θ * convRho p (lam * (L_min / ceCs))
  have hbF : 0 < b_F := by
    have hρ : 0 < convRho p (lam * (L_min / ceCs)) := by
      unfold convRho; positivity
    positivity
  refine ⟨b_F, hbF, fun {κ} hκ => ?_⟩
  set a : ℝ := 3 / (4 * ceCs)
  have ha0 : 0 < a := by positivity
  have ha1 : ceCs * a < 1 := by
    dsimp [a]; rw [show ceCs * (3 / (4 * ceCs)) = 3 / 4 by field_simp [hcs0.ne']]; norm_num
  obtain ⟨C₁, C₂, hC₁, hC₂, hsplit⟩ := mainTransferOp_split_error hκ hm hLmin ha0 ha1
  obtain ⟨C_f, hCf, hfourier⟩ := mainTransferOp_fourier_approx hκ (by omega : 1 ≤ m)
  obtain ⟨M_e, hMe, htail_e⟩ := convFExp_conv_tail hγ hLmin
  obtain ⟨M_h_norm, M_h_tail, hMh_norm, hMh_tail, hHL_prop⟩ :=
    convHL_integrable_and_tail (p := p) (θ := θ) (lam := lam) hp hp1 hθ.le hlam hLmin
  obtain ⟨C_g, hCg, hGL_prop⟩ := convGL_integrable_and_L2 hp hp1 hθ.le hlam
  set K_L : ℝ := ((1 + L_min) / L_min) ^ (3 / 2 : ℝ)
  have hKL : 0 < K_L := by positivity
  set C_e_part : ℝ := C₁ * γ * (L_min ^ (-(1 / 2 : ℝ)) * K_L) + C₂ * M_e * K_L
  set C_h_part : ℝ := C₁ * M_h_norm * (L_min ^ (-(1 / 2 : ℝ)) * K_L) + C₂ * M_h_tail * K_L
  set C_g_part : ℝ := C_f * Real.sqrt C_g * (L_min ^ (-(1 / 4 : ℝ)) * K_L)
  set C_err : ℝ := ceK * (C_e_part + C_h_part + C_g_part) + 1
  set c₀ : ℝ := max 2 ((8 * ceCs / L_min) ^ (3 / 2 : ℝ))
  refine ⟨C_err, by positivity, c₀, le_max_left _ _, fun {c ξ} hc hξ => ?_⟩
  intro L hL
  have hc2 : 2 ≤ c := (le_max_left _ _).trans hc
  have hc1 : 1 ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have hc_ge : (8 * ceCs / L_min) ^ (3 / 2 : ℝ) ≤ c := (le_max_right _ _).trans hc
  have hL0 : 0 < L := hLmin.trans_le hL
  set ε : ℝ := liftEps c
  have hε : 0 < ε := liftEps_pos hc0
  have hh_lam : 0 < lam * ε ^ 2 := by positivity
  have hfam_eq : convSourceFamily p γ θ lam c = convSource p γ θ ε (lam * ε ^ 2) := rfl
  have hS_int : Integrable (convSourceFamily p γ θ lam c) := by
    rw [hfam_eq]
    exact (convSource_integral hp hp1 hh_lam).1
  have himain := iMain_eq_mainTransferOp hS_int hκ (by omega : 1 ≤ m) hc1 hξ
  have himain_re : (c * ξ) * (iMain (convSourceFamily p γ θ lam c) (κ * ε) m c ξ).re =
      ceK * (mainTransferOp κ m c (fun X => (rescaledTail (convSourceFamily p γ θ lam c) ε X : ℂ)) L).re := by
    have hre := congrArg Complex.re himain
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
    simpa [mul_assoc] using hre
  rw [himain_re]
  obtain ⟨hcont_g, hg_int, hdg_int, hMg, hL2_g⟩ := hGL_prop hL0
  obtain ⟨hh_int, hh_norm, hh_tail⟩ := hHL_prop hc_ge hc1 hL
  have hf_int := convFExp_integrable (γ := γ) hε
  have hk_int := rescaledG1_integrable hε
  set f₁ : ℝ → ℂ := fun X => (realConv (convFExp γ ε) (rescaledG1 ε) X : ℂ)
  set f₂ : ℝ → ℂ := fun X => (realConv (convHL p θ lam ε L) (rescaledG1 ε) X : ℂ)
  set f₃ : ℝ → ℂ := fun X => (realConv (convGL θ p lam L) (rescaledG1 ε) X : ℂ)
  have hf₁_int : Integrable f₁ := (integrable_realConv hf_int hk_int).ofReal
  have hf₂_int : Integrable f₂ := (integrable_realConv hh_int hk_int).ofReal
  have hf₃_int : Integrable f₃ := (integrable_realConv hg_int hk_int).ofReal
  have hf_eq : (fun X : ℝ => (rescaledTail (convSourceFamily p γ θ lam c) ε X : ℂ)) =
      fun X => f₁ X + (f₂ X + f₃ X) := by
    funext X
    rw [hfam_eq, rescaledTail_convSource_eq hp hp1 hγ hθ.le hlam hc1 X]
    rw [show liftEps c = ε from rfl]
    push_cast
    have hadd : realConv (convWFull p θ lam ε) (rescaledG1 ε) X =
        realConv (convHL p θ lam ε L) (rescaledG1 ε) X + realConv (convGL θ p lam L) (rescaledG1 ε) X := by
      rw [realConv_apply, realConv_apply, realConv_apply]
      have hsub_add : ∀ Y : ℝ, convWFull p θ lam ε Y = convHL p θ lam ε L Y + convGL θ p lam L Y := by
        intro Y; unfold convHL; ring
      have hhprod : Integrable (fun Y => convHL p θ lam ε L Y * rescaledG1 ε (X - Y)) := by
        obtain ⟨Cg, _, hG_poly⟩ := convG1_le_poly
        refine (hh_int.norm.mul_const (max ((ε ^ 2)⁻¹ * Cg) 0)).mono'
          (hh_int.aestronglyMeasurable.mul ((rescaledG1_continuous hε).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
          (ae_of_all _ fun Y => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        refine mul_le_mul_of_nonneg_left ((?_ : |rescaledG1 ε (X - Y)| ≤ (ε ^ 2)⁻¹ * Cg).trans (le_max_left _ _)) (abs_nonneg _)
        rw [abs_of_nonneg (rescaledG1_nonneg ε _)]; unfold rescaledG1
        calc (ε ^ 2)⁻¹ * ceG1 (airyZero 1) (-(X - Y) / ε ^ 2)
            ≤ (ε ^ 2)⁻¹ * (Cg * (1 + |-(X - Y) / ε ^ 2|) ^ (-(5 / 2 : ℝ))) := by gcongr; exact hG_poly _
          _ ≤ (ε ^ 2)⁻¹ * (Cg * 1) := by gcongr; exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (-(X - Y) / ε ^ 2)]) (by norm_num)
          _ = _ := by ring
      have hgprod : Integrable (fun Y => convGL θ p lam L Y * rescaledG1 ε (X - Y)) := by
        obtain ⟨Cg, _, hG_poly⟩ := convG1_le_poly
        refine (hg_int.norm.mul_const (max ((ε ^ 2)⁻¹ * Cg) 0)).mono'
          (hg_int.aestronglyMeasurable.mul ((rescaledG1_continuous hε).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
          (ae_of_all _ fun Y => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        refine mul_le_mul_of_nonneg_left ((?_ : |rescaledG1 ε (X - Y)| ≤ (ε ^ 2)⁻¹ * Cg).trans (le_max_left _ _)) (abs_nonneg _)
        rw [abs_of_nonneg (rescaledG1_nonneg ε _)]; unfold rescaledG1
        calc (ε ^ 2)⁻¹ * ceG1 (airyZero 1) (-(X - Y) / ε ^ 2)
            ≤ (ε ^ 2)⁻¹ * (Cg * (1 + |-(X - Y) / ε ^ 2|) ^ (-(5 / 2 : ℝ))) := by gcongr; exact hG_poly _
          _ ≤ (ε ^ 2)⁻¹ * (Cg * 1) := by gcongr; exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (-(X - Y) / ε ^ 2)]) (by norm_num)
          _ = _ := by ring
      rw [← integral_add hhprod hgprod]
      refine integral_congr_ae (ae_of_all _ fun Y => ?_)
      dsimp only
      rw [hsub_add Y, add_mul]
    rw [hadd]
    dsimp [f₁, f₂, f₃]
    push_cast; ring
  have hop_add : mainTransferOp κ m c (fun X => (rescaledTail (convSourceFamily p γ θ lam c) ε X : ℂ)) L =
      mainTransferOp κ m c f₁ L + (mainTransferOp κ m c f₂ L + mainTransferOp κ m c f₃ L) := by
    rw [hf_eq]
    have hadd1 := mainTransferOp_add hκ (by omega : 1 ≤ m) hc1 hf₁_int (hf₂_int.add hf₃_int) L
    have hadd2 := mainTransferOp_add hκ (by omega : 1 ≤ m) hc1 hf₂_int hf₃_int L
    change mainTransferOp κ m c (fun X => f₁ X + (f₂ + f₃) X) L = _ at hadd1
    exact hadd1.trans (congrArg (mainTransferOp κ m c f₁ L + ·) hadd2)
  -- Useful power comparisons in `c` and `L`
  have hc_inv_le : c⁻¹ ≤ c ^ (-(1 / 6 : ℝ)) := by
    rw [← Real.rpow_neg_one]; exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hc_neg12_le : c ^ (-(1 / 2 : ℝ)) ≤ c ^ (-(1 / 6 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have hc_12_mul_inv : c ^ (1 / 2 : ℝ) * c⁻¹ = c ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0]; norm_num
  have hL32_le : L ^ (-(3 / 2 : ℝ)) ≤ K_L * (1 + L) ^ (-(3 / 2 : ℝ)) := by
    have h_ratio : 1 + L ≤ ((1 + L_min) / L_min) * L := by
      have h1 : L_min ≤ L_min * (L / L_min) := by rw [mul_div_cancel₀ _ hLmin.ne']; exact hL
      have h2 : L_min * (1 + L) ≤ (1 + L_min) * L := by nlinarith
      rw [div_mul_eq_mul_div, le_div_iff₀ hLmin]; linarith
    have hpow := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 1 + L) h_ratio (by norm_num : -(3 / 2 : ℝ) ≤ 0)
    rw [Real.mul_rpow (by positivity) hL0.le] at hpow
    have hL32_nn : 0 ≤ (1 + L) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
    have hKL0 : 0 < K_L := by positivity
    have hpow' : L ^ (-(3 / 2 : ℝ)) ≤ K_L * (1 + L) ^ (-(3 / 2 : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_left hpow hKL0.le
      have hKL_inv : K_L * ((1 + L_min) / L_min) ^ (-(3 / 2 : ℝ)) = 1 := by
        dsimp [K_L]; rw [← Real.rpow_add (by positivity), add_neg_cancel, Real.rpow_zero]
      calc L ^ (-(3 / 2 : ℝ))
          = (K_L * ((1 + L_min) / L_min) ^ (-(3 / 2 : ℝ))) * L ^ (-(3 / 2 : ℝ)) := by rw [hKL_inv, one_mul]
        _ = K_L * (((1 + L_min) / L_min) ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ))) := by ring
        _ ≤ K_L * (1 + L) ^ (-(3 / 2 : ℝ)) := hmul
    exact hpow'
  have hL2_le : L ^ (-2 : ℝ) ≤ (L_min ^ (-(1 / 2 : ℝ)) * K_L) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
    have hsplitL : L ^ (-2 : ℝ) = L ^ (-(1 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_add hL0]; norm_num
    have hLm : L ^ (-(1 / 2 : ℝ)) ≤ L_min ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hLmin hL (by norm_num)
    rw [hsplitL]
    calc L ^ (-(1 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ))
        ≤ L_min ^ (-(1 / 2 : ℝ)) * (K_L * (1 + L) ^ (-(3 / 2 : ℝ))) := by gcongr
      _ = _ := by ring
  have hL74_le : L ^ (1 / 4 : ℝ) * L ^ (-2 : ℝ) ≤ (L_min ^ (-(1 / 4 : ℝ)) * K_L) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
    have hsplitL : L ^ (1 / 4 : ℝ) * L ^ (-2 : ℝ) = L ^ (-(1 / 4 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; norm_num
    have hLm : L ^ (-(1 / 4 : ℝ)) ≤ L_min ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hLmin hL (by norm_num)
    rw [hsplitL]
    calc L ^ (-(1 / 4 : ℝ)) * L ^ (-(3 / 2 : ℝ))
        ≤ L_min ^ (-(1 / 4 : ℝ)) * (K_L * (1 + L) ^ (-(3 / 2 : ℝ))) := by gcongr
      _ = _ := by ring
  -- Term 1: `f₁`
  have hf₁_norm : ∫ X : ℝ, ‖f₁ X‖ = γ := by
    have h_nn : ∀ X : ℝ, 0 ≤ realConv (convFExp γ ε) (rescaledG1 ε) X := fun X => by
      rw [realConv_apply]
      exact integral_nonneg fun Y => mul_nonneg (convFExp_nonneg hγ ε Y) (rescaledG1_nonneg ε _)
    calc ∫ X : ℝ, ‖f₁ X‖ = ∫ X : ℝ, realConv (convFExp γ ε) (rescaledG1 ε) X := by
          refine integral_congr_ae (ae_of_all _ fun X => ?_)
          dsimp [f₁]; rw [Complex.norm_real, Real.norm_of_nonneg (h_nn X)]
      _ = (∫ Y : ℝ, convFExp γ ε Y) * (∫ Z : ℝ, rescaledG1 ε Z) := by
          unfold realConv; exact integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hf_int hk_int
      _ = γ := by
          have hint_fe := convFExp_integral_norm hγ hε
          have hfe_eq : ∫ Y : ℝ, ‖convFExp γ ε Y‖ = ∫ Y : ℝ, convFExp γ ε Y :=
            integral_congr_ae (ae_of_all _ fun Y => Real.norm_of_nonneg (convFExp_nonneg hγ ε Y))
          rw [← hfe_eq, hint_fe, rescaledG1_integral hε, mul_one]
  have hbd1 : ‖mainTransferOp κ m c f₁ L‖ ≤ C_e_part * c ^ (-(1 / 6 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
    have hsp := hsplit hc2 hL (by positivity : 0 ≤ M_e * c⁻¹ * L ^ (-(3 / 2 : ℝ))) hf₁_int
      (fun X hX => htail_e hc_ge hc1 hL X hX)
    rw [hf₁_norm] at hsp
    have h1 : C₁ * c⁻¹ * L ^ (-2 : ℝ) * γ ≤
        C₁ * γ * (L_min ^ (-(1 / 2 : ℝ)) * K_L) * c ^ (-(1 / 6 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
      calc C₁ * c⁻¹ * L ^ (-2 : ℝ) * γ = (C₁ * γ) * c⁻¹ * L ^ (-2 : ℝ) := by ring
        _ ≤ (C₁ * γ) * c ^ (-(1 / 6 : ℝ)) * ((L_min ^ (-(1 / 2 : ℝ)) * K_L) * (1 + L) ^ (-(3 / 2 : ℝ))) := by gcongr
        _ = _ := by ring
    have h2 : C₂ * c ^ (1 / 2 : ℝ) * (M_e * c⁻¹ * L ^ (-(3 / 2 : ℝ))) ≤
        C₂ * M_e * K_L * c ^ (-(1 / 6 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
      calc C₂ * c ^ (1 / 2 : ℝ) * (M_e * c⁻¹ * L ^ (-(3 / 2 : ℝ)))
          = (C₂ * M_e) * (c ^ (1 / 2 : ℝ) * c⁻¹) * L ^ (-(3 / 2 : ℝ)) := by ring
        _ = (C₂ * M_e) * c ^ (-(1 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by rw [hc_12_mul_inv]
        _ ≤ (C₂ * M_e) * c ^ (-(1 / 6 : ℝ)) * (K_L * (1 + L) ^ (-(3 / 2 : ℝ))) := by gcongr
        _ = _ := by ring
    calc ‖mainTransferOp κ m c f₁ L‖
        ≤ C₁ * c⁻¹ * L ^ (-2 : ℝ) * γ + C₂ * c ^ (1 / 2 : ℝ) * (M_e * c⁻¹ * L ^ (-(3 / 2 : ℝ))) := hsp
      _ ≤ _ := by dsimp [C_e_part]; linarith
  -- Term 2: `f₂`
  have hbd2 : ‖mainTransferOp κ m c f₂ L‖ ≤ C_h_part * c ^ (-(1 / 6 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
    have hsp := hsplit hc2 hL (by positivity : 0 ≤ M_h_tail * c⁻¹ * L ^ (-(3 / 2 : ℝ))) hf₂_int
      (fun X hX => hh_tail X hX)
    have h1 : C₁ * c⁻¹ * L ^ (-2 : ℝ) * (∫ X : ℝ, ‖f₂ X‖) ≤
        C₁ * M_h_norm * (L_min ^ (-(1 / 2 : ℝ)) * K_L) * c ^ (-(1 / 6 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
      calc C₁ * c⁻¹ * L ^ (-2 : ℝ) * (∫ X : ℝ, ‖f₂ X‖)
          ≤ C₁ * c ^ (-(1 / 6 : ℝ)) * ((L_min ^ (-(1 / 2 : ℝ)) * K_L) * (1 + L) ^ (-(3 / 2 : ℝ))) * M_h_norm := by
            gcongr
        _ = _ := by ring
    have h2 : C₂ * c ^ (1 / 2 : ℝ) * (M_h_tail * c⁻¹ * L ^ (-(3 / 2 : ℝ))) ≤
        C₂ * M_h_tail * K_L * c ^ (-(1 / 6 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
      calc C₂ * c ^ (1 / 2 : ℝ) * (M_h_tail * c⁻¹ * L ^ (-(3 / 2 : ℝ)))
          = (C₂ * M_h_tail) * (c ^ (1 / 2 : ℝ) * c⁻¹) * L ^ (-(3 / 2 : ℝ)) := by ring
        _ = (C₂ * M_h_tail) * c ^ (-(1 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by rw [hc_12_mul_inv]
        _ ≤ (C₂ * M_h_tail) * c ^ (-(1 / 6 : ℝ)) * (K_L * (1 + L) ^ (-(3 / 2 : ℝ))) := by gcongr
        _ = _ := by ring
    calc ‖mainTransferOp κ m c f₂ L‖
        ≤ C₁ * c⁻¹ * L ^ (-2 : ℝ) * (∫ X : ℝ, ‖f₂ X‖) +
            C₂ * c ^ (1 / 2 : ℝ) * (M_h_tail * c⁻¹ * L ^ (-(3 / 2 : ℝ))) := hsp
      _ ≤ _ := by dsimp [C_h_part]; linarith
  -- Term 3: `f₃`
  set main_val : ℝ := ceCs⁻¹ * convGL θ p lam L (L / ceCs)
  have hbd3 : ‖mainTransferOp κ m c f₃ L - (main_val : ℂ)‖ ≤
      C_g_part * c ^ (-(1 / 6 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
    have hfa := hfourier hc1 hL0 hcont_g hg_int hdg_int (convGL_hasDerivAt hlam hL0) hMg
    have hsqrt_le : Real.sqrt (L ^ (-2 : ℝ) * (∫ x : ℝ, |convGL θ p lam L x| ^ 2) +
        ∫ x : ℝ, |convGLDeriv θ p lam L x| ^ 2) ≤ Real.sqrt C_g * L ^ (-2 : ℝ) := by
      have hsq : C_g * L ^ (-4 : ℝ) = (Real.sqrt C_g * L ^ (-2 : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hCg.le, ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le]; norm_num
      calc Real.sqrt (L ^ (-2 : ℝ) * (∫ x : ℝ, |convGL θ p lam L x| ^ 2) +
              ∫ x : ℝ, |convGLDeriv θ p lam L x| ^ 2)
          ≤ Real.sqrt (C_g * L ^ (-4 : ℝ)) := Real.sqrt_le_sqrt hL2_g
        _ = Real.sqrt ((Real.sqrt C_g * L ^ (-2 : ℝ)) ^ 2) := by rw [hsq]
        _ = Real.sqrt C_g * L ^ (-2 : ℝ) := Real.sqrt_sq (by positivity)
    calc ‖mainTransferOp κ m c f₃ L - (main_val : ℂ)‖
        ≤ C_f * c ^ (-(1 / 6 : ℝ)) * L ^ (1 / 4 : ℝ) *
            Real.sqrt (L ^ (-2 : ℝ) * (∫ x : ℝ, |convGL θ p lam L x| ^ 2) +
              ∫ x : ℝ, |convGLDeriv θ p lam L x| ^ 2) := hfa
      _ ≤ C_f * c ^ (-(1 / 6 : ℝ)) * L ^ (1 / 4 : ℝ) * (Real.sqrt C_g * L ^ (-2 : ℝ)) := by gcongr
      _ = C_f * Real.sqrt C_g * c ^ (-(1 / 6 : ℝ)) * (L ^ (1 / 4 : ℝ) * L ^ (-2 : ℝ)) := by ring
      _ ≤ C_f * Real.sqrt C_g * c ^ (-(1 / 6 : ℝ)) * ((L_min ^ (-(1 / 4 : ℝ)) * K_L) * (1 + L) ^ (-(3 / 2 : ℝ))) := by
          gcongr
      _ = C_g_part * c ^ (-(1 / 6 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) := by dsimp [C_g_part]; ring
  -- Lower bound on `main_val`
  have hbd3_final := hbd3
  have hmain_val_lb : b_F * (1 + L) ^ (-(3 / 2 : ℝ)) ≤ ceK * main_val := by
    have hL_half : L / (2 * ceCs) ≤ L / ceCs :=
      div_le_div_of_nonneg_left hL0.le hcs0 (by linarith)
    have hLcs0 : 0 < L / ceCs := by positivity
    have hchi1 : convChi L (L / ceCs) = 1 := convChi_eq_one hL0 hL_half
    have hrho_lb : convRho p (lam * (L_min / ceCs)) ≤ convRho p (lam * (L / ceCs)) :=
      convRho_mono (by linarith) (by positivity) (by gcongr)
    have hrpow_cs : (L / ceCs) ^ (-(3 / 2 : ℝ)) = ceCs ^ (3 / 2 : ℝ) * L ^ (-(3 / 2 : ℝ)) := by
      rw [Real.div_rpow hL0.le hcs0.le, Real.rpow_neg hL0.le, Real.rpow_neg hcs0.le, div_inv_eq_mul, mul_comm]
    have hL_1L : (1 + L) ^ (-(3 / 2 : ℝ)) ≤ L ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hL0 (by linarith) (by norm_num)
    have hcs_pow : ceCs⁻¹ * ceCs ^ (3 / 2 : ℝ) = ceCs ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hcs0]; norm_num
    have hmain_eq : ceK * main_val =
        ceK * (ceCs⁻¹ * (θ * 1 * convRho p (lam * (L / ceCs)) * (ceCs ^ (3 / 2 : ℝ) * L ^ (-(3 / 2 : ℝ))))) := by
      dsimp [main_val]; unfold convGL; simp only [hLcs0, ↓reduceIte, hchi1, hrpow_cs]
    rw [hmain_eq]
    have hrho_nn : 0 ≤ convRho p (lam * (L / ceCs)) := convRho_nonneg p (by positivity)
    calc b_F * (1 + L) ^ (-(3 / 2 : ℝ))
        = ceK * (ceCs⁻¹ * ceCs ^ (3 / 2 : ℝ)) * θ * convRho p (lam * (L_min / ceCs)) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
          dsimp [b_F]; rw [hcs_pow]
      _ ≤ ceK * (ceCs⁻¹ * ceCs ^ (3 / 2 : ℝ)) * θ * convRho p (lam * (L / ceCs)) * L ^ (-(3 / 2 : ℝ)) := by
          gcongr
      _ = _ := by ring
  -- Combine via `(z - m).re ≥ -‖z - m‖`
  have hdiff_norm : ‖mainTransferOp κ m c (fun X => (rescaledTail (convSourceFamily p γ θ lam c) ε X : ℂ)) L - (main_val : ℂ)‖ ≤
      (C_e_part + C_h_part + C_g_part) * c ^ (-(1 / 6 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
    have heq : mainTransferOp κ m c (fun X => (rescaledTail (convSourceFamily p γ θ lam c) ε X : ℂ)) L - (main_val : ℂ) =
        mainTransferOp κ m c f₁ L + mainTransferOp κ m c f₂ L + (mainTransferOp κ m c f₃ L - (main_val : ℂ)) := by
      rw [hop_add]; ring
    rw [heq]
    calc ‖mainTransferOp κ m c f₁ L + mainTransferOp κ m c f₂ L + (mainTransferOp κ m c f₃ L - (main_val : ℂ))‖
        ≤ ‖mainTransferOp κ m c f₁ L + mainTransferOp κ m c f₂ L‖ + ‖mainTransferOp κ m c f₃ L - (main_val : ℂ)‖ :=
          norm_add_le _ _
      _ ≤ (‖mainTransferOp κ m c f₁ L‖ + ‖mainTransferOp κ m c f₂ L‖) + ‖mainTransferOp κ m c f₃ L - (main_val : ℂ)‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ _ := by linarith [hbd1, hbd2, hbd3_final]
  have hre_sub : main_val - (C_e_part + C_h_part + C_g_part) * c ^ (-(1 / 6 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) ≤
      (mainTransferOp κ m c (fun X => (rescaledTail (convSourceFamily p γ θ lam c) ε X : ℂ)) L).re := by
    have hre1 : -‖mainTransferOp κ m c (fun X => (rescaledTail (convSourceFamily p γ θ lam c) ε X : ℂ)) L - (main_val : ℂ)‖ ≤
        (mainTransferOp κ m c (fun X => (rescaledTail (convSourceFamily p γ θ lam c) ε X : ℂ)) L - (main_val : ℂ)).re := by
      linarith [neg_abs_le (mainTransferOp κ m c (fun X => (rescaledTail (convSourceFamily p γ θ lam c) ε X : ℂ)) L - (main_val : ℂ)).re,
        Complex.abs_re_le_norm (mainTransferOp κ m c (fun X => (rescaledTail (convSourceFamily p γ θ lam c) ε X : ℂ)) L - (main_val : ℂ))]
    rw [Complex.sub_re, Complex.ofReal_re] at hre1
    linarith [hdiff_norm]
  have hc16_nn : 0 ≤ c ^ (-(1 / 6 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ)) := by positivity
  have hce_err : ceK * (C_e_part + C_h_part + C_g_part) * (c ^ (-(1 / 6 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ))) ≤
      C_err * (c ^ (-(1 / 6 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ))) := by
    refine mul_le_mul_of_nonneg_right ?_ hc16_nn
    dsimp [C_err]; linarith
  calc (b_F - C_err * c ^ (-(1 / 6 : ℝ))) * (1 + L) ^ (-(3 / 2 : ℝ))
      = b_F * (1 + L) ^ (-(3 / 2 : ℝ)) - C_err * (c ^ (-(1 / 6 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ))) := by ring
    _ ≤ ceK * main_val - ceK * (C_e_part + C_h_part + C_g_part) * (c ^ (-(1 / 6 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ))) :=
        sub_le_sub hmain_val_lb hce_err
    _ = ceK * (main_val - (C_e_part + C_h_part + C_g_part) * c ^ (-(1 / 6 : ℝ)) * (1 + L) ^ (-(3 / 2 : ℝ))) := by ring
    _ ≤ ceK * (mainTransferOp κ m c (fun X => (rescaledTail (convSourceFamily p γ θ lam c) ε X : ℂ)) L).re :=
        mul_le_mul_of_nonneg_left hre_sub hk0.le

/-- info: 'FormalResearch.SignUncertainty.convSourceFamily_far_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convSourceFamily_far_transfer

end FormalResearch.SignUncertainty

