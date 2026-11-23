module

public import FormalResearch.CohnElkies.DualPhaseAndO3
public import FormalResearch.CohnElkies.CancelledSymbolAndLaplace
public import FormalResearch.CohnElkies.PhysicalAndFarTransfer
public import FormalResearch.CohnElkies.PreEdgeAndSplineFloor
public import FormalResearch.CohnElkies.LobeSaddleBounds
public import FormalResearch.CohnElkies.OriginMellinAndS0
public import Mathlib.Analysis.Fourier.Inversion

/-! # Pre-Edge Criterion (`cepe:general`, `PE.3`), Concrete `GT.2b`, and Unconditional `O.11y(3)`
* **Section 1:** Concrete `GT.2b(1)–(3)` (`twoScaleS_gt2bData`, `twoScaleS_gt2b_reflected_mult`, `twoScaleS_gt2b_dual_integral`),
  unconditional `O.11y(3)` / `GT.4` (`twoScale_mellin_origin_unconditional`, `twoScaleFc_at_a1_asymptotic_unconditional`, `twoScaleFc_at_a1_neg`).
* **Section 2:** Unconditional exact reference Mellin inversion (`pe3_reference_mellin_inversion`, `pe3_measure_inversion_of_bounds`, `pe3_measure_inversion`).
* **Section 3:** Theorem `PE.3` compact origin positivity (`pe3_remainder_integral_bound`, `PE3OriginData`, `pe3OriginData_nonvacuous`, `pe3_compact_origin_pos`).
* **Section 4:** Proposition `cepe:general` (`preEdgeU`, `preEdgeDelta1`, `PreEdgeGeneralData`, `preEdge_general_pos`, `preEdgeGeneralData_nonvacuous`). -/

@[expose] public section

open Complex Filter MeasureTheory Set
open scoped Real Topology FourierTransform RealInnerProductSpace

namespace FormalResearch.CohnElkies

open FormalResearch.Special

/-! ## Section 1: Concrete `GT.2b(1)–(3)` for `twoScaleS` and unconditional `O.11y(3)` / `GT.4` -/

/-- Moving-diagonal weights `w_n = θ c_n² (1 - φ_p(h E_n)²)` for `twoScaleS`. -/
noncomputable def twoScaleW (p h θ : ℝ) (n : ℕ) : ℝ :=
  θ * cohnC airyDerivFirstZero n ^ 2 * (1 - ceVarphiP p (h * cohnE n) ^ 2)

/-- Reflected dual line of the fixed positive seed `S₀ = g₁ + g₁'`. -/
noncomputable def twoScaleS0Reflected (ε τ : ℝ) : ℂ :=
  airyTwistedLaplaceC (ceS0 (airyZero 1) airyDerivFirstZero)
    (((ceCs * ε⁻¹ : ℝ) : ℂ) * (1 - Complex.I * (τ : ℂ)))

lemma ceVarphiP_mem_Icc {p x : ℝ} (hx : 0 ≤ x) : 0 ≤ ceVarphiP p x ∧ ceVarphiP p x ≤ 1 := by
  unfold ceVarphiP; exact ⟨by positivity, inv_le_one_of_one_le₀ (by linarith [Real.rpow_nonneg hx p])⟩

lemma twoScaleW_nonneg (p : ℝ) {h θ : ℝ} (hh : 0 ≤ h) (hθ : 0 ≤ θ) (n : ℕ) : 0 ≤ twoScaleW p h θ n :=
  mul_nonneg (mul_nonneg hθ (sq_nonneg _)) (by have := ceVarphiP_mem_Icc (p := p) (mul_nonneg hh (cohnE_nonneg n)); nlinarith)

lemma twoScaleW_summable (p : ℝ) {h θ : ℝ} (hh : 0 ≤ h) (hθ : 0 ≤ θ) : Summable (twoScaleW p h θ) := by
  have hC_sum : Summable (fun n : ℕ => cohnC airyDerivFirstZero n ^ 2) :=
    ((hasSum_inv_sq airyDerivFirstZero (airyAi_ne_zero_of_deriv_zero airyDerivFirstZero_spec.2.2)).congr_fun
      fun n => by rw [cohnC, inv_pow]; ring).summable
  refine (hC_sum.mul_left θ).of_nonneg_of_le (twoScaleW_nonneg p hh hθ) fun n =>
    (mul_le_mul_of_nonneg_left (by linarith [sq_nonneg (ceVarphiP p (h * cohnE n))])
      (mul_nonneg hθ (sq_nonneg _))).trans_eq (mul_one _)

private lemma ceS0_tail_rpow32 :
    ∃ C > 0, ∀ u : ℝ, 0 ≤ u → |ceS0 (airyZero 1) airyDerivFirstZero u| ≤ C * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by
  have ha1 := airyAi_airyZero 1; have ha1' := airyDerivFirstZero_spec.2.2
  obtain ⟨R_plus, C_tl, hC_tl, htail, hR_bd⟩ := ceS0_pos_tail ha1 ha1'
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_ceS0 (airyZero 1) airyDerivFirstZero).continuousOn
  let C_hi : ℝ := (1 / (2 * π) + C_tl) / 2; let C_lo : ℝ := max M₀ 1 * Real.exp (2 / 3)
  refine ⟨max C_hi C_lo, lt_of_lt_of_le (by positivity) (le_max_right _ _), fun u hu => ?_⟩
  rcases le_or_gt u 1 with hu1 | hu1
  · have hu32 : u ^ (3 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hu hu1 (by norm_num)
    exact (hM₀ u ⟨hu, hu1⟩).trans (calc M₀ ≤ max M₀ 1 := le_max_left _ _
      _ = C_lo * Real.exp (-(2 / 3 : ℝ)) := by dsimp [C_lo]; rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ max C_hi C_lo * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) :=
          mul_le_mul (le_max_right _ _) (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le (by positivity))
  · set s : ℝ := Real.sqrt u; have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hu1.le; have hs_pos : 0 < s := by linarith
    have hs2 : u = s ^ 2 := (Real.sq_sqrt hu).symm
    have hs3 : s ^ 3 = u ^ (3 / 2 : ℝ) := by
      rw [hs2, ← Real.rpow_natCast s 3, ← Real.rpow_natCast s 2, ← Real.rpow_mul hs_pos.le]; norm_num
    have hR : R_plus s ≤ C_tl := (le_abs_self _).trans ((hR_bd s hs1).trans (mul_le_of_le_one_right hC_tl (Real.rpow_le_one_of_one_le_of_nonpos hs1 (by norm_num))))
    have hs2_le : s ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs1 (by norm_num)
    have hst := htail s hs1; rw [← hs2] at hst
    have h2s_le : 2 * s * ceS0 (airyZero 1) airyDerivFirstZero u ≤ (1 / (2 * π) + C_tl) * Real.exp (-(4 / 3 : ℝ) * s ^ 3) :=
      hst.trans_le (mul_le_mul_of_nonneg_right (add_le_add (mul_le_of_le_one_right (by positivity) hs2_le) hR) (Real.exp_pos _).le)
    have hce_le : ceS0 (airyZero 1) airyDerivFirstZero u ≤ C_hi * Real.exp (-(4 / 3 : ℝ) * s ^ 3) :=
      calc ceS0 (airyZero 1) airyDerivFirstZero u = (2 * s * ceS0 (airyZero 1) airyDerivFirstZero u) / (2 * s) := by field_simp [hs_pos.ne']
        _ ≤ ((1 / (2 * π) + C_tl) * Real.exp (-(4 / 3 : ℝ) * s ^ 3)) / 2 :=
            (div_le_div_of_nonneg_right h2s_le (by positivity)).trans (div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith))
        _ = C_hi * Real.exp (-(4 / 3 : ℝ) * s ^ 3) := by dsimp [C_hi]; ring
    rw [abs_of_nonneg (ceS0_pos (airyZero 1) airyDerivFirstZero ha1 ha1' u).le]
    refine hce_le.trans (mul_le_mul (le_max_left _ _) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by positivity))
    rw [hs3]; linarith [Real.rpow_pos_of_pos (by linarith : 0 < u) (3 / 2 : ℝ)]

private lemma ceS0_regularity_local :
    (∀ y : ℂ, 0 ≤ y.re → Integrable (fun u : ℝ => (ceS0 (airyZero 1) airyDerivFirstZero u : ℂ) * Complex.exp (y * (u : ℂ)))) ∧
    DifferentiableOn ℂ (airyTwistedLaplaceC (ceS0 (airyZero 1) airyDerivFirstZero)) {y : ℂ | 0 < y.re} := by
  obtain ⟨C_t, hC_t, htail⟩ := ceS0_tail_rpow32
  have h := airyTwistedLaplaceC_regularity (continuous_ceS0 _ _) (ceS0_integrable (airyAi_airyZero 1) airyDerivFirstZero_spec.2.2) hC_t htail
  exact ⟨h.1, h.2.2.1⟩

lemma twoScaleS0Reflected_props :
    ∃ C₀ ≥ 0, (∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ContDiff ℝ 2 (twoScaleS0Reflected ε)) ∧
      (∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ j ≤ 2, ∀ τ : ℝ,
        ‖iteratedDeriv j (twoScaleS0Reflected ε) τ‖ ≤ C₀ * ε ^ (5 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ))) := by
  obtain ⟨C_s0, hC_s0, hbd_s0⟩ := airyTwistedLaplaceC_ceS0_bound
  let α : ℝ := (2 : ℝ) ^ (-(1 / 3 : ℝ)); have hα_pos : 0 < α := by positivity
  have hα_le1 : α ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  let F_sc : ℂ → ℂ := fun w => airyTwistedLaplaceC (ceS0 (airyZero 1) airyDerivFirstZero) (((ceCs * α : ℝ) : ℂ) * w)
  have hF_diff : DifferentiableOn ℂ F_sc {w : ℂ | 0 < w.re} := ceS0_regularity_local.2.comp (by fun_prop) fun w hw => by
    change 0 < (((ceCs * α : ℝ) : ℂ) * w).re; simpa [Complex.mul_re] using mul_pos (mul_pos ceCs_pos hα_pos) hw
  let C_star : ℝ := C_s0 * α ^ (-(5 / 2 : ℝ)); have hC_star : 0 ≤ C_star := by positivity
  have hF_bd : ∀ w : ℂ, 0 < w.re → ‖F_sc w‖ ≤ C_star * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := fun w hw => by
    have hw_re : 0 ≤ ((α : ℂ) * w).re := by simpa [Complex.mul_re] using mul_nonneg hα_pos.le hw.le
    have hnorm_ge : α * ‖1 + w‖ ≤ ‖1 + (α : ℂ) * w‖ := by
      rw [show α * ‖1 + w‖ = ‖(α : ℂ) * (1 + w)‖ by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hα_pos.le],
        mul_add, mul_one, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.add_im, Complex.one_im, Complex.ofReal_im, zero_add]
      nlinarith [hw_re, hα_le1]
    have hrpow := (Real.rpow_le_rpow_of_nonpos (mul_pos hα_pos (lt_of_lt_of_le (by simp; linarith) (Complex.re_le_norm _)))
      hnorm_ge (by norm_num : -(5 / 2 : ℝ) ≤ 0)).trans_eq (Real.mul_rpow hα_pos.le (norm_nonneg _))
    have hce := hbd_s0 ((α : ℂ) * w) hw_re
    rw [show ((ceCs : ℂ) * ((α : ℂ) * w)) = (((ceCs * α : ℝ) : ℂ) * w) by push_cast; ring] at hce
    exact hce.trans ((mul_le_mul_of_nonneg_left hrpow hC_s0.le).trans_eq (by dsimp [C_star]; ring))
  let C₀ : ℝ := (2 : ℝ) ^ ((2 : ℝ) + 5 / 2) * 2 * C_star * (2 : ℝ) ^ (-(5 / 6 : ℝ))
  have hmul_id : ∀ ε > 0, (2 * ε ^ (-3 : ℝ)) ^ (1 / 3 : ℝ) * α = ε⁻¹ := fun ε hε => by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hε.le _), ← Real.rpow_mul hε.le]
    dsimp [α]; rw [mul_assoc, mul_comm _ ((2 : ℝ) ^ (-(1 / 3 : ℝ))), ← mul_assoc, ← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero, one_mul]
    norm_num; exact Real.rpow_neg_one ε
  have h_eq : ∀ {ε : ℝ}, 0 < ε → twoScaleS0Reflected ε =
      fun t : ℝ => F_sc (((2 * ε ^ (-3 : ℝ)) ^ (1 / 3 : ℝ) : ℝ) * (1 - Complex.I * (t : ℂ))) := fun {ε} hε => by
    ext t; dsimp [twoScaleS0Reflected, F_sc]; congr 1; rw [← hmul_id ε hε]; push_cast; ring
  refine ⟨C₀, by positivity, fun {ε} hε _ => ?_, fun {ε} hε hε1 j hj τ => ?_⟩
  · rw [h_eq hε]; exact (o2_reflected_line_contDiff hF_diff (by positivity : 0 < 2 * ε ^ (-3 : ℝ))).of_le (by simp)
  · have h1le : 1 ≤ ε ^ (-3 : ℝ) := by
      rw [show (-3 : ℝ) = -(3 : ℕ) by norm_num, Real.rpow_neg hε.le, Real.rpow_natCast]
      exact (one_le_inv₀ (pow_pos hε 3)).mpr (pow_le_one₀ hε.le hε1)
    have hc56 : (2 * ε ^ (-3 : ℝ)) ^ (-(5 / 6 : ℝ)) = (2 : ℝ) ^ (-(5 / 6 : ℝ)) * ε ^ (5 / 2 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hε.le _), ← Real.rpow_mul hε.le]; norm_num
    rw [h_eq hε]
    refine (o2_reflected_line_deriv_bound hC_star hF_diff hF_bd (by linarith : 2 ≤ 2 * ε ^ (-3 : ℝ)) τ j).trans ?_
    rw [hc56]; have hj_r : (j : ℝ) ≤ 2 := by exact_mod_cast hj
    have hj_fac : (j.factorial : ℝ) ≤ 2 := by exact_mod_cast (Nat.factorial_le hj).trans_eq (by norm_num [Nat.factorial_succ])
    have h2_pow : (2 : ℝ) ^ ((j : ℝ) + 5 / 2) ≤ (2 : ℝ) ^ ((2 : ℝ) + 5 / 2) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hcoeff : (2 : ℝ) ^ ((j : ℝ) + 5 / 2) * (j.factorial : ℝ) * C_star ≤ (2 : ℝ) ^ ((2 : ℝ) + 5 / 2) * 2 * C_star :=
      mul_le_mul_of_nonneg_right (mul_le_mul h2_pow hj_fac (by positivity) (by positivity)) hC_star
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff (by positivity)) (by positivity)).trans_eq (by dsimp [C₀]; ring)

private lemma diagAirySource_integrable_twisted {w : ℕ → ℝ} (hw_nn : ∀ n, 0 ≤ w n)
    (hw_sum : Summable w) {y : ℂ} (hy : 0 < y.re) :
    Integrable (fun u : ℝ => (diagAirySource w u : ℂ) * Complex.exp (y * (u : ℂ))) := by
  have hcohn : ∀ n : ℕ, AEStronglyMeasurable (fun u : ℝ => ((w n * cohnL n u ^ 2 : ℝ) : ℂ)) volume := fun n =>
    ((aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => (w n : ℂ)) volume).mul
      (((Lp.aestronglyMeasurable (cohnLL2 n)).congr (cohnLL2_ae n)).pow 2)).congr
      (ae_of_all _ fun u => by dsimp only [Pi.mul_apply, Pi.pow_apply]; push_cast; ring)
  have hXm : AEStronglyMeasurable (fun u : ℝ => (diagAirySource w u : ℂ)) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun N => Finset.aestronglyMeasurable_fun_sum (Finset.range N) fun n _ => hcohn n)
      (ae_of_all _ fun u => by simpa [diagAirySource, Complex.ofReal_sum] using
        (Complex.ofRealCLM.hasSum (diagAirySource_summable hw_nn hw_sum u).hasSum).tendsto_sum_nat)
  let M : ℝ := (∑' n : ℕ, w n) * 23; have hM : 0 ≤ M := mul_nonneg (tsum_nonneg hw_nn) (by norm_num)
  have h_neg_aux : IntegrableOn (fun u : ℝ => M * ((1 + -u) ^ 1 * Real.exp (-(y.re * -u)))) (Iio 0) := by
    simpa [Set.neg_Ioi] using IntegrableOn.comp_neg ((airyPws_integrableOn_pow_mul_exp 1 hy).const_mul M)
  have h_neg : IntegrableOn (fun u : ℝ => M * (1 + |u|) * airyEnv (u : ℂ) * Real.exp (y.re * u)) (Iio 0) :=
    h_neg_aux.congr_fun (fun u hu => by
      dsimp only; have hu0 : u < 0 := mem_Iio.mp hu; rw [abs_of_neg hu0, airyEnv_ofReal_neg hu0, pow_one, mul_one, show -(y.re * -u) = y.re * u by ring1]; dsimp [M]; ring1) measurableSet_Iio
  have h_pos : IntegrableOn (fun u : ℝ => M * (1 + |u|) * airyEnv (u : ℂ) * Real.exp (y.re * u)) (Ici 0) := by
    let a : ℝ := y.re + 2 / 3; let Cq : ℝ := a ^ 3 / 12
    have hquad_s : ∀ s : ℝ, 0 ≤ s → a * s ^ 2 ≤ (4 / 3 : ℝ) * s ^ 3 + Cq := fun s hs => by
      have hsq : 0 ≤ ((4 * s + a) * (2 * s - a) ^ 2) / 12 := div_nonneg (mul_nonneg (by dsimp [a]; linarith [hy]) (sq_nonneg _)) (by norm_num)
      have heq : ((4 * s + a) * (2 * s - a) ^ 2) / 12 = (4 / 3 : ℝ) * s ^ 3 + Cq - a * s ^ 2 := by dsimp [Cq]; ring
      linarith [hsq, heq]
    have hg_cont : ContinuousOn (fun u : ℝ => M * (1 + u) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (y.re * u)) (Ici 0) :=
      ((continuousOn_const.mul (continuousOn_const.add continuousOn_id)).mul
        (ContinuousOn.rexp (continuousOn_const.mul (continuousOn_id.rpow_const fun _ _ => Or.inr (by norm_num))))).mul (by fun_prop)
    have hmeas : AEStronglyMeasurable (fun u : ℝ => M * (1 + |u|) * airyEnv (u : ℂ) * Real.exp (y.re * u)) (volume.restrict (Ici 0)) :=
      (hg_cont.aestronglyMeasurable measurableSet_Ici).congr (by
        filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
        rw [abs_of_nonneg (mem_Ici.mp hu), airyEnv_ofReal_nonneg (mem_Ici.mp hu)])
    refine ((integrableOn_Ici_iff_integrableOn_Ioi).mpr ((airyPws_integrableOn_pow_mul_exp 1
      (by norm_num : (0 : ℝ) < 2 / 3)).const_mul (M * Real.exp Cq))).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    have hu0 : 0 ≤ u := mem_Ici.mp hu; rw [abs_of_nonneg hu0, airyEnv_ofReal_nonneg hu0, Real.norm_of_nonneg (by positivity)]
    have hs3 : Real.sqrt u ^ 3 = u ^ (3 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hu0]; norm_num
    have hquad := hquad_s (Real.sqrt u) (Real.sqrt_nonneg u); rw [Real.sq_sqrt hu0, hs3] at hquad
    have hexp : Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (y.re * u) ≤ Real.exp Cq * Real.exp (-(2 / 3 : ℝ) * u) := by
      rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.mpr (by dsimp [a] at hquad; linarith)
    calc M * (1 + u) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (y.re * u)
        = M * (1 + u) * (Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (y.re * u)) := by ring
      _ ≤ M * (1 + u) * (Real.exp Cq * Real.exp (-(2 / 3 : ℝ) * u)) := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (M * Real.exp Cq) * ((1 + u) ^ 1 * Real.exp (-(2 / 3 : ℝ) * u)) := by rw [pow_one]; ring
  have h_tot_int : Integrable (fun u : ℝ => M * (1 + |u|) * airyEnv (u : ℂ) * Real.exp (y.re * u)) := by
    rw [← integrableOn_univ, ← Set.Iio_union_Ici (a := (0 : ℝ))]; exact h_neg.union h_pos
  refine h_tot_int.mono' (hXm.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
    (ae_of_all _ fun u => by
      have hle := diagAirySource_le hw_nn hw_sum u
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hle.1, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_le_mul_of_nonneg_right (hle.2.trans_eq (by dsimp [M])) (Real.exp_pos _).le)

/-- **Lemma `GT.2b(1)` (`ce_o1_global_transfer.tex`):** concrete `GT2bReflectedData` for `twoScaleS`. -/
noncomputable def twoScaleS_gt2bData {p h θ : ℝ} (hp : 0 < p) (hh : 0 ≤ h) (hθ : 0 ≤ θ) (γ : ℝ) : GT2bReflectedData :=
  let C_d := Classical.choose dirichletVecS_l2_sq_min_bound; let hC_d := Classical.choose_spec dirichletVecS_l2_sq_min_bound
  let C₀ := Classical.choose twoScaleS0Reflected_props; let hC₀ := Classical.choose_spec twoScaleS0Reflected_props
  { w := twoScaleW p h θ, hw_nn := twoScaleW_nonneg p hh hθ, hw_sum := twoScaleW_summable p hh hθ
    A := √(C_d * θ), hA := Real.sqrt_nonneg _
    hdiag := fun t ht => by
      have hsq : √(C_d * θ) ^ 2 = C_d * θ := Real.sq_sqrt (mul_nonneg hC_d.1.le hθ)
      have hvec : ∀ n : ℕ, twoScaleW p h θ n * dirichletPhi n t ^ 2 = dirichletVecS p h θ t n ^ 2 := fun n => by
        have hvp := ceVarphiP_mem_Icc (p := p) (mul_nonneg hh (cohnE_nonneg n))
        unfold dirichletVecS twoScaleW; rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hθ, Real.sq_sqrt (by nlinarith)]
      simpa [hvec, hsq] using hC_d.2 hp hh hθ ht
    S₀ := twoScaleS0Reflected, C₀ := C₀, hC₀ := hC₀.1
    hS₀_cd := fun {ε} hε hε1 => hC₀.2.1 hε hε1, hS₀_bd := fun {ε} hε hε1 j hj τ => hC₀.2.2 hε hε1 j hj τ, θ := 1, γ := γ }

private lemma airyTwistedLaplaceC_twoScaleS_funext {p lam γ θ κ ε : ℝ} {m : ℕ}
    (hp : 0 < p) (hlam : 0 < lam) (hθ : 0 ≤ θ) (hε : 0 < ε) :
    let d := twoScaleS_gt2bData hp (mul_nonneg hlam.le (sq_nonneg ε)) hθ γ
    (fun t : ℝ => bsplineMult (ceCs * κ / m) m t *
      airyTwistedLaplaceC (twoScaleS p lam γ θ (ε ^ (-3 : ℝ))) (((ceCs * ε⁻¹ : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ)))) =
      fun t => bsplineMult (ceCs * κ / m) m t *
        ((d.θ : ℂ) * airyTwistedLaplaceC (diagAirySource d.w) (((ceCs * ε⁻¹ : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ))) +
          (d.γ : ℂ) * (ε : ℂ) * d.S₀ ε t) := funext fun t => by
  congr 1; let h := lam * ε ^ 2; have hh : 0 ≤ h := mul_nonneg hlam.le (sq_nonneg ε)
  set y : ℂ := ((ceCs * ε⁻¹ : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ))
  have hy_re : 0 < y.re := by simpa [y, Complex.mul_re] using mul_pos ceCs_pos (inv_pos.mpr hε)
  have hc_eq : (ε ^ (-3 : ℝ)) ^ (-(1 / 3 : ℝ)) = ε := by rw [← Real.rpow_mul hε.le]; norm_num
  have h1 := diagAirySource_integrable_twisted (twoScaleW_nonneg p hh hθ) (twoScaleW_summable p hh hθ) hy_re
  have h2 := (ceS0_regularity_local.1 y hy_re.le).const_mul ((γ * ε : ℝ) : ℂ)
  have heq : (fun u : ℝ => (twoScaleS p lam γ θ (ε ^ (-3 : ℝ)) u : ℂ) * Complex.exp (y * (u : ℂ))) =
      fun u => (diagAirySource (twoScaleW p h θ) u : ℂ) * Complex.exp (y * (u : ℂ)) +
        ((γ * ε : ℝ) : ℂ) * ((ceS0 (airyZero 1) airyDerivFirstZero u : ℂ) * Complex.exp (y * (u : ℂ))) := by
    ext u; unfold twoScaleS diagAirySource twoScaleW movingDiagS; rw [hc_eq, ← tsum_mul_left]; simp only [h, mul_assoc]; push_cast; ring
  dsimp [twoScaleS_gt2bData, twoScaleS0Reflected]; unfold airyTwistedLaplaceC
  rw [heq, integral_add h1 h2, integral_const_mul]; dsimp [y, h]; push_cast; ring

private lemma twoScaleS_gt2b_coeff_le {p h θ : ℝ} (hp : 0 < p) (hh : 0 ≤ h) (hθ : 0 ≤ θ) (γ : ℝ) :
    let d := twoScaleS_gt2bData hp hh hθ γ
    let K := max (Classical.choose dirichletVecS_l2_sq_min_bound) (max (Classical.choose twoScaleS0Reflected_props) 1)
    1 ≤ K ∧ |d.θ| * d.A ^ 2 + |d.γ| * d.C₀ ≤ K * (θ + |γ|) := by
  let C_d := Classical.choose dirichletVecS_l2_sq_min_bound; let hC_d := Classical.choose_spec dirichletVecS_l2_sq_min_bound
  let C₀ := Classical.choose twoScaleS0Reflected_props
  refine ⟨(le_max_right _ _).trans (le_max_right _ _), ?_⟩
  dsimp [twoScaleS_gt2bData]; rw [abs_one, one_mul, Real.sq_sqrt (mul_nonneg hC_d.1.le hθ)]
  have h1 : C_d ≤ max C_d (max C₀ 1) := le_max_left _ _; have h2 : C₀ ≤ max C_d (max C₀ 1) := (le_max_left _ _).trans (le_max_right _ _)
  nlinarith [abs_nonneg γ]

/-- **Lemma `GT.2b(2)` (`ce_o1_global_transfer.tex`):** unconditional vertical-line bound for `twoScaleS`. -/
theorem twoScaleS_gt2b_reflected_mult {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 3 ≤ m) :
    ∃ C > 0, ∀ {p lam θ ε : ℝ} (γ : ℝ), 0 < p → 0 < lam → 0 ≤ θ → 0 < ε → ε ≤ 1 → ∀ j ≤ 2, ∀ τ : ℝ,
      ‖iteratedDeriv j (fun t : ℝ => bsplineMult (ceCs * κ / m) m t *
        airyTwistedLaplaceC (twoScaleS p lam γ θ (ε ^ (-3 : ℝ))) (((ceCs * ε⁻¹ : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ)))) τ‖ ≤
        C * (θ + |γ|) * ε ^ (7 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨C₁, hC₁, hgt2b⟩ := gt2b_reflected_combined hκ hm
  let K := max (Classical.choose dirichletVecS_l2_sq_min_bound) (max (Classical.choose twoScaleS0Reflected_props) 1)
  have hK1 : 1 ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C₁ * K, mul_pos hC₁ (by linarith), fun {p lam θ ε} γ hp hlam hθ hε hε1 j hj τ => ?_⟩
  let d := twoScaleS_gt2bData hp (mul_nonneg hlam.le (sq_nonneg ε)) hθ γ
  rw [airyTwistedLaplaceC_twoScaleS_funext hp hlam hθ hε]
  have hK := (twoScaleS_gt2b_coeff_le hp (mul_nonneg hlam.le (sq_nonneg ε)) hθ γ).2
  exact (hgt2b d hε hε1 j hj τ).trans ((by gcongr : C₁ * (|d.θ| * d.A ^ 2 + |d.γ| * d.C₀) * ε ^ (7 / 2 : ℝ) *
    (1 + τ ^ 2) ^ (-(3 / 2 : ℝ)) ≤ C₁ * (K * (θ + |γ|)) * ε ^ (7 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(3 / 2 : ℝ))).trans_eq (by ring))

/-- **Lemma `GT.2b(3)` (`ce_o1_global_transfer.tex`):** unconditional dual-integral bound for `twoScaleS`. -/
theorem twoScaleS_gt2b_dual_integral {m : ℕ} (hm : 3 ≤ m) :
    ∃ C > 0, ∀ {p lam θ γ κ ε L : ℝ},
      0 < p → 0 < lam → 0 ≤ θ → 0 < κ → 0 < ε → 2 ≤ ε ^ (-3 : ℝ) → 0 < L → 1 ≤ L / (Real.pi ^ 2 * ε ^ 2) →
      let c : ℝ := ε ^ (-3 : ℝ)
      c * (Real.exp L / Real.pi ^ 2) * ‖dualEdgeIntegral c L (fun τ => bsplineMult (ceCs * κ / m) m τ *
          airyTwistedLaplaceC (twoScaleS p lam γ θ c) (((ceCs * ε⁻¹ : ℝ) : ℂ) * (1 - Complex.I * (τ : ℂ))))‖ ≤
        C * κ ^ (-(m : ℝ)) * (θ + |γ|) * ε * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨C₁, hC₁, hgt2b⟩ := gt2b_dual_integral_reflected hm
  let K := max (Classical.choose dirichletVecS_l2_sq_min_bound) (max (Classical.choose twoScaleS0Reflected_props) 1)
  have hK1 : 1 ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C₁ * K, mul_pos hC₁ (by linarith), fun {p lam θ γ κ ε L} hp hlam hθ hκ hε hc2 hL hS => ?_⟩
  let d := twoScaleS_gt2bData hp (mul_nonneg hlam.le (sq_nonneg ε)) hθ γ
  dsimp only; rw [airyTwistedLaplaceC_twoScaleS_funext hp hlam hθ hε]
  have hK := (twoScaleS_gt2b_coeff_le hp (mul_nonneg hlam.le (sq_nonneg ε)) hθ γ).2
  exact (hgt2b d hκ hε hc2 hL hS).trans ((by gcongr : C₁ * κ ^ (-(m : ℝ)) * (|d.θ| * d.A ^ 2 + |d.γ| * d.C₀) *
    ε * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) ≤
    C₁ * κ ^ (-(m : ℝ)) * (K * (θ + |γ|)) * ε * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ)))).trans_eq (by ring))

/-- **Unconditional `O.11y(3)` origin tuning (`ce_o1_route.tex`).** -/
theorem twoScale_mellin_origin_unconditional {m : ℕ} (hm : 1 ≤ m) {κ p lam γ R θ : ℝ}
    (hκ : 0 < κ) (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hlam : 0 < lam) (hγ : 0 < γ)
    (hR : max (2 * γ) (γ * max 1 (((airyZero 1 - airyZero 2) / 2)⁻¹)) < R)
    (hθ_spec : ∃ K_star > 0, ∃ c_star > 0, ∃ m_tip > 0, ∃ c_far > 0,
      ∀ {c u : ℝ}, c_star ≤ c → u < airyZero 1 - K_star * c ^ (-(1 / 3 : ℝ)) →
        let ε := c ^ (-(1 / 3 : ℝ)); let v₀ := (airyZero 1 - airyZero 2) / 2
        let C_v0 := max 1 v₀⁻¹; let B := ceG1Deriv airyDerivFirstZero u - ceF1 u
        0 < twoScaleF0 p lam γ θ R c u ∧ (airyZero 1 - v₀ ≤ u → m_tip * ε ≤ twoScaleF0 p lam γ θ R c u) ∧
        (u ≤ airyZero 1 - v₀ → lam * ε ^ 2 * (airyZero 1 - u) ≤ 1 → (R - γ * C_v0) * ε * B ≤ twoScaleF0 p lam γ θ R c u) ∧
        (u ≤ airyZero 1 - v₀ → 1 ≤ lam * ε ^ 2 * (airyZero 1 - u) → (1 / 2) * c_far * B ≤ twoScaleF0 p lam γ θ R c u)) :
    ∃ C_eta > 0, ∃ K_star' > 0, ∃ c_star' > 0,
      (∀ {c : ℝ}, c_star' ≤ c → |twoScaleEta p lam R (bsplineMellinWeight m κ c) c| ≤ C_eta * c ^ (-(5 / 6 : ℝ)) ∧
        Integrable (twoScaleQc p lam R (bsplineMellinWeight m κ c) c) ∧
        bsplineMellinWeight m κ c * airyTwistedLaplace (twoScaleQc p lam R (bsplineMellinWeight m κ c) c) (ceCs * c ^ (1 / 3 : ℝ)) =
          ceK * ∫ u : ℝ, twoScaleQc p lam R (bsplineMellinWeight m κ c) c u ∧
        ceK * ∫ u : ℝ, twoScaleQc p lam R (bsplineMellinWeight m κ c) c u = ceK * twoScaleEta p lam R (bsplineMellinWeight m κ c) c) ∧
      (∀ {c u : ℝ}, c_star' ≤ c → u < airyZero 1 - K_star' * c ^ (-(1 / 3 : ℝ)) →
        0 < twoScaleFc p lam γ θ R (bsplineMellinWeight m κ c) c u) := by
  obtain ⟨C_Q, hC_Q, hQ0_lap⟩ := twoScaleQ0_real_laplace_bound
  exact twoScale_mellin_origin hp hlam hγ hR hθ_spec (fun {c} hc => (bsplineMellinWeight_bounds hm hκ (lt_of_lt_of_le (by positivity) hc)).2)
    hC_Q (fun {c} hc => hQ0_lap hp hlam ((le_trans (by positivity) (le_max_left (2 * γ) _)).trans hR.le) hc)

/-- Variant of `twoScale_mellin_origin_unconditional` supplying `hθ_spec` from `MovingDiagFarTail p`. -/
theorem twoScale_mellin_origin_of_farTail {m : ℕ} (hm : 1 ≤ m) {κ p lam γ R : ℝ}
    (hκ : 0 < κ) (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hft : MovingDiagFarTail p) (hlam : 0 < lam) (hγ : 0 < γ)
    (hR : max (2 * γ) (γ * max 1 (((airyZero 1 - airyZero 2) / 2)⁻¹)) < R) :
    ∃ θ₀ > 0, ∀ {θ : ℝ}, θ ∈ Ioc 0 (min 1 θ₀) → ∃ C_eta > 0, ∃ K_star' > 0, ∃ c_star' > 0,
      (∀ {c : ℝ}, c_star' ≤ c → |twoScaleEta p lam R (bsplineMellinWeight m κ c) c| ≤ C_eta * c ^ (-(5 / 6 : ℝ)) ∧
        Integrable (twoScaleQc p lam R (bsplineMellinWeight m κ c) c) ∧
        bsplineMellinWeight m κ c * airyTwistedLaplace (twoScaleQc p lam R (bsplineMellinWeight m κ c) c) (ceCs * c ^ (1 / 3 : ℝ)) =
          ceK * ∫ u : ℝ, twoScaleQc p lam R (bsplineMellinWeight m κ c) c u ∧
        ceK * ∫ u : ℝ, twoScaleQc p lam R (bsplineMellinWeight m κ c) c u = ceK * twoScaleEta p lam R (bsplineMellinWeight m κ c) c) ∧
      (∀ {c u : ℝ}, c_star' ≤ c → u < airyZero 1 - K_star' * c ^ (-(1 / 3 : ℝ)) →
        0 < twoScaleFc p lam γ θ R (bsplineMellinWeight m κ c) c u) :=
  let ⟨θ₀, hθ₀, hmarg⟩ := twoScaleF0_pos_with_margins hp hft hlam hγ hR
  ⟨θ₀, hθ₀, fun hθ => twoScale_mellin_origin_unconditional hm hκ hp hlam hγ hR (hmarg hθ)⟩

/-- **Unconditional `GT.4` / `O.11y(3)` tip offset.** -/
theorem twoScaleFc_at_a1_asymptotic_unconditional {m : ℕ} (hm : 1 ≤ m) {κ p lam R : ℝ}
    (hκ : 0 < κ) (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hlam : 0 < lam) (hR : 0 ≤ R) (γ θ : ℝ) :
    ∃ c_min ≥ max 1 (R ^ 3), ∃ C > 0, ∀ {c : ℝ}, c_min ≤ c →
      let ε : ℝ := c ^ (-(1 / 3 : ℝ)); let M : ℝ := -airyDerivFirstZero; let c_node : ℝ := cohnC airyDerivFirstZero 0
      |twoScaleFc p lam γ θ R (bsplineMellinWeight m κ c) c (airyZero 1) / (2 * airyAi' (airyZero 1) ^ 2) -
          (-(R * (M - c_node ^ 2) + fracJ2 p * Real.sqrt lam + (γ / 2) * (1 + c_node ^ 2)) * ε)| ≤ C * ε ^ (2 * p) := by
  obtain ⟨C_Q, hC_Q, hQ0_lap⟩ := twoScaleQ0_real_laplace_bound
  exact twoScaleFc_at_a1_asymptotic hp hlam hR γ θ hC_Q
    (fun {c} hc => (bsplineMellinWeight_bounds hm hκ (lt_of_lt_of_le (by positivity) hc)).2) (fun {c} hc => hQ0_lap hp hlam hR hc)

/-- Strict negativity of `F_c(a₁)` for large `c` whenever `0 < γ` and `0 ≤ R`. -/
theorem twoScaleFc_at_a1_neg {m : ℕ} (hm : 1 ≤ m) {κ p lam R γ θ : ℝ}
    (hκ : 0 < κ) (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hlam : 0 < lam) (hR : 0 ≤ R) (hγ : 0 < γ) :
    ∃ c₀ ≥ max 1 (R ^ 3), ∀ {c : ℝ}, c₀ ≤ c → twoScaleFc p lam γ θ R (bsplineMellinWeight m κ c) c (airyZero 1) < 0 := by
  obtain ⟨c_min, hc_min, C, hC, hasymp⟩ := twoScaleFc_at_a1_asymptotic_unconditional hm hκ hp hlam hR γ θ
  have hsum : HasSum (fun n : ℕ => cohnC airyDerivFirstZero n ^ 2) (cohnM airyDerivFirstZero ^ 2 - airyDerivFirstZero) :=
    (hasSum_inv_sq airyDerivFirstZero (airyAi_ne_zero_of_deriv_zero airyDerivFirstZero_spec.2.2)).congr_fun fun n => by rw [cohnC, inv_pow]; ring
  have hma : cohnM airyDerivFirstZero = 0 := by simp [cohnM, airyDerivFirstZero_spec.2.2]
  rw [hma, zero_pow two_ne_zero, zero_sub] at hsum
  have hc0_le : cohnC airyDerivFirstZero 0 ^ 2 ≤ -airyDerivFirstZero := by
    simpa [Finset.sum_range_one] using sum_le_hasSum (Finset.range 1) (fun _ _ => sq_nonneg _) hsum
  have hJ2_nn : 0 ≤ fracJ2 p := by
    unfold fracJ2; refine mul_nonneg (div_nonneg zero_le_one Real.pi_pos.le) (setIntegral_nonneg measurableSet_Ioi fun x hx => ?_)
    have hvp := ceVarphiP_mem_Icc (p := p) (mem_Ioi.mp hx).le; exact mul_nonneg (by nlinarith) (Real.rpow_nonneg (mem_Ioi.mp hx).le _)
  let lead : ℝ := R * (-airyDerivFirstZero - cohnC airyDerivFirstZero 0 ^ 2) + fracJ2 p * Real.sqrt lam + (γ / 2) * (1 + cohnC airyDerivFirstZero 0 ^ 2)
  have hlead_pos : 0 < lead := add_pos_of_nonneg_of_pos (add_nonneg (mul_nonneg hR (sub_nonneg.mpr hc0_le)) (mul_nonneg hJ2_nn (Real.sqrt_nonneg lam))) (by positivity)
  have hp_sub : 0 < 2 * p - 1 := by linarith [hp.1]
  let ε₀ : ℝ := (lead / (2 * C)) ^ (1 / (2 * p - 1)); have hε₀ : 0 < ε₀ := Real.rpow_pos_of_pos (div_pos hlead_pos (by positivity)) _
  refine ⟨max c_min (max 1 (ε₀ ^ (-3 : ℝ))), hc_min.trans (le_max_left _ _), fun {c} hc => ?_⟩
  have hc_min' := (le_max_left _ _).trans hc
  have hc_pos : 0 < c := lt_of_lt_of_le (by linarith [le_max_left 1 (R ^ 3), hc_min]) hc_min'
  let ε : ℝ := c ^ (-(1 / 3 : ℝ)); have hε_pos : 0 < ε := Real.rpow_pos_of_pos hc_pos _
  have hε_le : ε ≤ ε₀ := (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hε₀ (-3))
    ((le_max_right _ _).trans ((le_max_right _ _).trans hc)) (by norm_num : -(1 / 3 : ℝ) ≤ 0)).trans_eq
    (by rw [← Real.rpow_mul hε₀.le]; norm_num)
  have hε_pow : ε ^ (2 * p - 1) ≤ lead / (2 * C) := (Real.rpow_le_rpow hε_pos.le hε_le hp_sub.le).trans_eq
    (by dsimp [ε₀]; rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hp_sub.ne', Real.rpow_one])
  have hCε : C * ε ^ (2 * p) ≤ (lead / 2) * ε := by
    rw [show (2 * p : ℝ) = (2 * p - 1) + 1 by ring, Real.rpow_add hε_pos, Real.rpow_one, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hε_pow hC.le) hε_pos.le).trans_eq (by field_simp [hC.ne'])
  have hval := (abs_le.mp (hasymp hc_min')).2
  have hdiv_neg : twoScaleFc p lam γ θ R (bsplineMellinWeight m κ c) c (airyZero 1) / (2 * airyAi' (airyZero 1) ^ 2) < 0 := by
    rw [neg_mul, sub_neg_eq_add] at hval; have hpos_le := mul_pos hlead_pos hε_pos
    dsimp [lead, ε] at hCε hpos_le; rw [div_mul_eq_mul_div] at hCε; linarith [hval, hCε, hpos_le]
  exact (div_neg_iff.mp hdiv_neg).elim (fun h => by linarith [h.2, sq_nonneg (airyAi' (airyZero 1))]) (·.1)

/-! ## Section 2: Unconditional exact reference Mellin inversion (`ce_o1_pre_edge.tex` `PE.3`) -/

private noncomputable def pe3RefFn (X u : ℝ) : ℂ :=
  ((Real.exp (-Real.exp (-u)) - Real.exp (-Real.exp (ceCs * X) * Real.exp (-u)) : ℝ) : ℂ)

private lemma one_sub_exp_neg_le_self {x : ℝ} (hx : 0 ≤ x) : 0 ≤ 1 - Real.exp (-x) ∧ 1 - Real.exp (-x) ≤ x :=
  ⟨sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)), by linarith [Real.add_one_le_exp (-x)]⟩

private lemma norm_gamma_pure_imag_neg (y : ℝ) :
    ‖Complex.Gamma ((-y : ℂ) * Complex.I)‖ = ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ := by
  have hconj : Complex.Gamma ((-y : ℂ) * Complex.I) = starRingEnd ℂ (Complex.Gamma ((y : ℂ) * Complex.I)) := by
    rw [← Complex.Gamma_conj]; congr 1; simp
  rw [hconj, Complex.norm_conj]

private lemma norm_gamma_pure_imag_abs_small {y : ℝ} (hy0 : y ≠ 0) (hy1 : |y| ≤ 1) : ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ ≤ 1 / |y| := by
  rcases lt_or_gt_of_ne hy0 with hlt | hgt
  · have h1 := norm_gamma_pure_imag_le_small (y := -y) (neg_pos.mpr hlt) (by rwa [abs_of_neg hlt] at hy1)
    rw [Complex.ofReal_neg] at h1; rwa [abs_of_neg hlt, ← norm_gamma_pure_imag_neg y]
  · rw [abs_of_pos hgt]; exact norm_gamma_pure_imag_le_small hgt (by rwa [abs_of_pos hgt] at hy1)

private lemma norm_gamma_pure_imag_abs_large {y : ℝ} (hy1 : 1 ≤ |y|) :
    ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ ≤ √(3 * π) * |y| ^ (-(1 / 2 : ℝ)) * Real.exp (-(π / 2) * |y|) := by
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy] at hy1 ⊢; exact norm_gamma_pure_imag_le_large hy1
  · have h1 := norm_gamma_pure_imag_le_large (y := -y) (by rwa [abs_of_neg hy] at hy1)
    rw [Complex.ofReal_neg] at h1; rwa [abs_of_neg hy, ← norm_gamma_pure_imag_neg y]

private lemma norm_ofReal_cpow_neg_I {r : ℝ} (hr : 0 < r) (y : ℝ) : ‖(r : ℂ) ^ (-(Complex.I * (y : ℂ)))‖ = 1 := by
  rw [show -(Complex.I * (y : ℂ)) = ((-y : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_cpow_eq_rpow_re_of_pos hr, show (((-y : ℝ) : ℂ) * Complex.I).re = 0 by simp, Real.rpow_zero]

private lemma continuous_ofReal_cpow_neg_I {r : ℝ} (hr : 0 < r) : Continuous (fun y : ℝ => (r : ℂ) ^ (-(Complex.I * (y : ℂ)))) := by
  rw [show (fun y : ℝ => (r : ℂ) ^ (-(Complex.I * (y : ℂ)))) = fun y : ℝ => Complex.exp (-(Complex.I * (y : ℂ)) * (Real.log r : ℂ)) from
    funext fun y => by rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'), ← Complex.ofReal_log hr.le, mul_comm]]
  fun_prop

private lemma aestronglyMeasurable_gamma_pure_imag :
    AEStronglyMeasurable (fun y : ℝ => Complex.Gamma (Complex.I * (y : ℂ))) volume := by
  rw [← MeasureTheory.restrict_compl_singleton (μ := volume) 0]
  refine ContinuousOn.aestronglyMeasurable (fun y hy => ?_) (measurableSet_singleton (0 : ℝ)).compl
  have hy0 := mem_compl_singleton_iff.mp hy
  exact ((Complex.differentiableAt_Gamma (Complex.I * (y : ℂ)) fun m h => by
    have := congrArg Complex.im h; simp [hy0] at this).continuousAt.comp
    (f := fun t : ℝ => Complex.I * (t : ℂ)) (continuousAt_const.mul Complex.continuous_ofReal.continuousAt)).continuousWithinAt

private lemma norm_osc_ceCs_le {X : ℝ} (hX : 0 ≤ X) (y : ℝ) :
    ‖1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))‖ ≤ min (ceCs * X * |y|) 2 := by
  have hosc := norm_one_sub_exp_neg_le (v := Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)) (by simp)
  rwa [show ‖Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)‖ = ceCs * X * |y| by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg ceCs_pos.le hX), Real.norm_eq_abs]] at hosc

private lemma exp_neg_mul_Ioi_bd (a : ℝ) {k : ℝ} (hk : 0 < k) :
    IntegrableOn (fun y : ℝ => Real.exp (-k * y)) (Ioi a) ∧ ∫ y in Ioi a, Real.exp (-k * y) = Real.exp (-k * a) / k := by
  simpa only [neg_mul] using integral_exp_neg_lin_Ioi (a := a) hk

private lemma integrable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) : Integrable (fun w : ℝ => Real.exp (-c * |w|)) := by
  have hpos : IntegrableOn (fun w : ℝ => Real.exp (-c * |w|)) (Ici 0) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr (exp_neg_mul_Ioi_bd 0 hc).1).congr_fun
      (fun w hw => by rw [abs_of_nonneg (mem_Ici.mp hw)]) measurableSet_Ici
  have hneg : IntegrableOn (fun w : ℝ => Real.exp (-c * |w|)) (Iio 0) := by
    simpa [Set.neg_Ioi, abs_neg] using IntegrableOn.comp_neg ((integrableOn_Ici_iff_integrableOn_Ioi).mp hpos)
  rw [← integrableOn_univ, ← Iio_union_Ici (a := (0 : ℝ))]; exact hneg.union hpos

private lemma integrable_gamma_piecewise {C₁ C₂ : ℝ} :
    Integrable (fun y : ℝ => (Icc (-1 : ℝ) 1).indicator (fun t => C₁ * |t| ^ (-(1 / 2 : ℝ))) y + C₂ * Real.exp (-(π / 2) * |y|)) := by
  have hpos : IntegrableOn (fun y : ℝ => |y| ^ (-(1 / 2 : ℝ))) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ))).1.congr_fun (fun y hy => by rw [abs_of_pos hy.1]) measurableSet_Ioc
  have hneg : IntegrableOn (fun y : ℝ => |y| ^ (-(1 / 2 : ℝ))) (Ico (-1) 0) := by
    simpa [Set.neg_Ioc, neg_zero, abs_neg] using IntegrableOn.comp_neg hpos
  have h0 : IntegrableOn (fun y : ℝ => |y| ^ (-(1 / 2 : ℝ))) ({(0 : ℝ)} : Set ℝ) := by
    rw [IntegrableOn, Measure.restrict_eq_zero.mpr (by simp)]; exact integrable_zero_measure
  have hcc : Ico (-1 : ℝ) 0 ∪ ({0} ∪ Ioc 0 1) = Icc (-1 : ℝ) 1 := by
    ext y; simp only [mem_union, mem_Ico, mem_singleton_iff, mem_Ioc, mem_Icc]
    exact ⟨by rintro (⟨_, _⟩ | rfl | ⟨_, _⟩) <;> constructor <;> linarith, fun ⟨_, _⟩ => by rcases lt_trichotomy y 0 with h | rfl | h <;> tauto⟩
  exact (IntegrableOn.integrable_indicator ((hcc ▸ (hneg.union (h0.union hpos))).const_mul C₁) measurableSet_Icc).add
    ((integrable_exp_neg_mul_abs (by positivity : 0 < π / 2)).const_mul C₂)

private lemma gamma_mul_min_integrable {A : ℝ} (hA : 0 ≤ A) :
    Integrable (fun y : ℝ => ‖Complex.Gamma (Complex.I * (y : ℂ))‖ * min (A * |y|) 2) := by
  let M : ℝ := max A (2 * √(3 * π))
  have hdom : Integrable (fun y : ℝ => (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ => M) y + M * Real.exp (-(π / 2) * |y|)) :=
    (IntegrableOn.integrable_indicator (integrableOn_const (C := M) (hs := measure_Icc_lt_top.ne)) measurableSet_Icc).add
      ((integrable_exp_neg_mul_abs (by positivity : 0 < π / 2)).const_mul M)
  refine hdom.mono' (aestronglyMeasurable_gamma_pure_imag.norm.mul (by fun_prop)) ?_
  filter_upwards [ae_iff.mpr (by simp : volume {y : ℝ | ¬y ≠ 0} = 0)] with y hy0
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (le_min (mul_nonneg hA (abs_nonneg _)) (by norm_num))), mul_comm Complex.I (y : ℂ)]
  rcases le_or_gt |y| 1 with hy1 | hy1
  · have h1 := mul_le_mul (norm_gamma_pure_imag_abs_small hy0 hy1) (min_le_left (A * |y|) 2) (by positivity) (by positivity)
    rw [mul_left_comm, one_div_mul_cancel (abs_ne_zero.mpr hy0), mul_one] at h1
    rw [indicator_of_mem (mem_Icc.mpr (abs_le.mp hy1))]; exact h1.trans ((le_max_left _ _).trans (le_add_of_nonneg_right (by positivity)))
  · have hy_rpow : |y| ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1.le (by norm_num)
    have h1 := mul_le_mul ((norm_gamma_pure_imag_abs_large hy1.le).trans (by gcongr)) (min_le_right (A * |y|) 2) (by positivity) (by positivity)
    have hM_le : 2 * √(3 * π) ≤ M := le_max_right _ _
    exact h1.trans (calc √(3 * π) * |y| ^ (-(1 / 2 : ℝ)) * Real.exp (-(π / 2) * |y|) * 2
        ≤ √(3 * π) * 1 * Real.exp (-(π / 2) * |y|) * 2 := by gcongr
      _ = (2 * √(3 * π)) * Real.exp (-(π / 2) * |y|) := by ring
      _ ≤ M * Real.exp (-(π / 2) * |y|) := by gcongr
      _ ≤ _ := le_add_of_nonneg_left (indicator_nonneg (fun _ _ => by positivity) _))

private lemma gamma_mul_half_norm_le (G : ℝ → ℂ) {C_H : ℝ} (hG : ∀ y : ℝ, ‖G y‖ ≤ C_H * |y| ^ (1 / 2 : ℝ))
    {Δ : ℝ} (hΔ : 0 < Δ) (y : ℝ) (hy0 : y ≠ 0) :
    ‖(4 : ℂ) ^ (-(Complex.I * (y : ℂ))) * Complex.Gamma (Complex.I * (y : ℂ)) * G y * (Δ : ℂ) ^ (-(Complex.I * (y : ℂ)))‖ ≤
      (Icc (-1 : ℝ) 1).indicator (fun t => C_H * |t| ^ (-(1 / 2 : ℝ))) y + (C_H * √(3 * π)) * Real.exp (-(π / 2) * |y|) := by
  have hC_H : 0 ≤ C_H := by have := hG 1; simp at this; linarith [norm_nonneg (G 1)]
  have h4n : ‖(4 : ℂ) ^ (-(Complex.I * (y : ℂ)))‖ = 1 := by
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num]; exact norm_ofReal_cpow_neg_I (by norm_num) y
  rw [norm_mul, norm_mul, norm_mul, h4n, one_mul, norm_ofReal_cpow_neg_I hΔ y, mul_one, mul_comm Complex.I (y : ℂ)]
  rcases le_or_gt |y| 1 with hy1 | hy1
  · have hid : (1 / |y|) * (C_H * |y| ^ (1 / 2 : ℝ)) = C_H * |y| ^ (-(1 / 2 : ℝ)) := by
      rw [one_div, ← Real.rpow_neg_one |y|, mul_left_comm, ← Real.rpow_add (abs_pos.mpr hy0)]; norm_num
    rw [indicator_of_mem (mem_Icc.mpr (abs_le.mp hy1))]
    exact ((mul_le_mul (norm_gamma_pure_imag_abs_small hy0 hy1) (hG y) (norm_nonneg _) (by positivity)).trans_eq hid).trans
      (le_add_of_nonneg_right (by positivity))
  · have hid : (√(3 * π) * |y| ^ (-(1 / 2 : ℝ)) * Real.exp (-(π / 2) * |y|)) * (C_H * |y| ^ (1 / 2 : ℝ)) =
        (C_H * √(3 * π)) * Real.exp (-(π / 2) * |y|) := by
      calc _ = C_H * √(3 * π) * (|y| ^ (-(1 / 2 : ℝ)) * |y| ^ (1 / 2 : ℝ)) * Real.exp (-(π / 2) * |y|) := by ring
        _ = _ := by rw [← Real.rpow_add (abs_pos.mpr hy0), neg_add_cancel, Real.rpow_zero, mul_one]
    exact ((mul_le_mul (norm_gamma_pure_imag_abs_large hy1.le) (hG y) (norm_nonneg _) (by positivity)).trans_eq hid).trans
      (le_add_of_nonneg_left (indicator_nonneg (fun _ _ => by positivity) _))

private lemma gamma_mul_half_integrable {C_H Δ : ℝ} (hΔ : 0 < Δ) {G : ℝ → ℂ} (hG_cont : Continuous G)
    (hG : ∀ y : ℝ, ‖G y‖ ≤ C_H * |y| ^ (1 / 2 : ℝ)) :
    Integrable (fun y : ℝ => (4 : ℂ) ^ (-(Complex.I * (y : ℂ))) * Complex.Gamma (Complex.I * (y : ℂ)) * G y *
      (Δ : ℂ) ^ (-(Complex.I * (y : ℂ)))) := by
  have h4c : AEStronglyMeasurable (fun y : ℝ => (4 : ℂ) ^ (-(Complex.I * (y : ℂ)))) volume := by
    rw [show (fun y : ℝ => (4 : ℂ) ^ (-(Complex.I * (y : ℂ)))) = fun y : ℝ => ((4 : ℝ) : ℂ) ^ (-(Complex.I * (y : ℂ))) from
      funext fun _ => by norm_num]
    exact (continuous_ofReal_cpow_neg_I (by norm_num : (0 : ℝ) < 4)).aestronglyMeasurable
  refine (integrable_gamma_piecewise (C₁ := C_H) (C₂ := C_H * √(3 * π))).mono'
    (((h4c.mul aestronglyMeasurable_gamma_pure_imag).mul hG_cont.aestronglyMeasurable).mul
      (continuous_ofReal_cpow_neg_I hΔ).aestronglyMeasurable) ?_
  filter_upwards [ae_iff.mpr (by simp : volume {y : ℝ | ¬y ≠ 0} = 0)] with y hy0; exact gamma_mul_half_norm_le G hG hΔ y hy0

private lemma osc_norm_le_mul_min {X : ℝ} (hX : 0 < X) (y : ℝ) :
    ‖1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))‖ ≤ max (ceCs * |y|) 2 * min X 1 := by
  have hosc := norm_osc_ceCs_le hX.le y
  rcases le_or_gt X 1 with hX1 | hX1
  · rw [min_eq_left hX1]; exact (hosc.trans (min_le_left _ _)).trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) hX.le).trans_eq' (by ring))
  · rw [min_eq_right hX1.le, mul_one]; exact (hosc.trans (min_le_right _ _)).trans (le_max_right _ _)

private lemma continuous_osc_setIntegral {ν : Measure ℝ} {S : Set ℝ}
    (hmS : MeasurableSet S) (hS : S ⊆ Ioi 0) (hν : IntegrableOn (fun X : ℝ => min X 1) S ν) :
    Continuous (fun y : ℝ => ∫ X in S, (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))) ∂ν) :=
  continuous_iff_continuousAt.mpr fun y₀ =>
    continuousAt_of_dominated (bound := fun X : ℝ => max (ceCs * (|y₀| + 1)) 2 * min X 1)
      (Eventually.of_forall fun _ => (Continuous.aestronglyMeasurable (by fun_prop)).restrict)
      (by filter_upwards [Metric.ball_mem_nhds y₀ one_pos] with y hy
          have hy_abs : |y| ≤ |y₀| + 1 := by
            have h1 : ‖y - y₀‖ < 1 := Metric.mem_ball.mp hy; rw [Real.norm_eq_abs] at h1; linarith [abs_sub_abs_le_abs_sub y y₀]
          filter_upwards [ae_restrict_mem hmS] with X hX
          refine (osc_norm_le_mul_min (hS hX) y).trans (mul_le_mul_of_nonneg_right ?_ (le_min (hS hX).le zero_le_one))
          exact max_le_max (mul_le_mul_of_nonneg_left hy_abs ceCs_pos.le) le_rfl)
      (hν.const_mul _) (ae_of_all _ fun _ => by fun_prop)

private lemma pe3RefFn_integrable {X : ℝ} (hX : 0 < X) : Integrable (pe3RefFn X) := by
  let a : ℝ := Real.exp (ceCs * X); have ha1 : 1 < a := Real.one_lt_exp_iff.mpr (mul_pos ceCs_pos hX)
  have hcont : Continuous (pe3RefFn X) := by unfold pe3RefFn; fun_prop
  have h_exp_Iic : IntegrableOn Real.exp (Iic 0) volume := by
    simpa [Set.neg_Ici] using ((integrableOn_Ici_iff_integrableOn_Ioi (f := fun x : ℝ => Real.exp (-x))).mpr
      (integrableOn_exp_neg_Ioi 0)).comp_neg
  have hneg : IntegrableOn (pe3RefFn X) (Iic 0) :=
    h_exp_Iic.mono' hcont.aestronglyMeasurable.restrict (by
      filter_upwards [ae_restrict_mem measurableSet_Iic] with u _;
      have hnn : 0 ≤ Real.exp (-Real.exp (-u)) - Real.exp (-a * Real.exp (-u)) := sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith [Real.exp_pos (-u)]))
      rw [pe3RefFn, Complex.norm_real, Real.norm_of_nonneg hnn]
      linarith [Real.exp_le_exp.mpr (by linarith [Real.add_one_le_exp (-u)] : -Real.exp (-u) ≤ u), Real.exp_pos (-a * Real.exp (-u))])
  have hpos : IntegrableOn (pe3RefFn X) (Ioi 0) :=
    ((integrableOn_exp_neg_Ioi 0).const_mul (a - 1)).mono' hcont.aestronglyMeasurable.restrict (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
      have hnn : 0 ≤ Real.exp (-Real.exp (-u)) - Real.exp (-a * Real.exp (-u)) := sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith [Real.exp_pos (-u)]))
      rw [pe3RefFn, Complex.norm_real, Real.norm_of_nonneg hnn, show Real.exp (-Real.exp (-u)) - Real.exp (-a * Real.exp (-u)) =
        Real.exp (-Real.exp (-u)) * (1 - Real.exp (-((a - 1) * Real.exp (-u)))) by rw [mul_sub, mul_one, ← Real.exp_add]; congr 2; ring]
      exact (mul_le_mul (Real.exp_le_one_iff.mpr (by linarith [Real.exp_pos (-u)]))
        (one_sub_exp_neg_le_self (mul_nonneg (sub_nonneg.mpr ha1.le) (Real.exp_pos (-u)).le)).2
        (one_sub_exp_neg_le_self (by positivity)).1 zero_le_one).trans_eq (one_mul _))
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]; exact hneg.union hpos

private lemma fourier_pe3RefFn_eq {X y : ℝ} (hX : 0 < X) (hy : y ≠ 0) :
    𝓕 (pe3RefFn X) (y / (2 * π)) =
      Complex.Gamma ((y : ℂ) * Complex.I) * (1 - Complex.exp (-((ceCs * X : ℝ) : ℂ) * (y : ℂ) * Complex.I)) := by
  let a : ℝ := Real.exp (ceCs * X); have ha1 : 1 < a := Real.one_lt_exp_iff.mpr (mul_pos ceCs_pos hX); have ha0 : 0 < a := by linarith
  let s : ℂ := (y : ℂ) * Complex.I; have hs0 : s ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hy) Complex.I_ne_zero
  have hs1_ne : s - 1 ≠ 0 := fun h => by have := congrArg Complex.im h; simp [s, hy] at this
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hcomp_eq : (fun u : ℝ => Complex.exp (↑(-2 * π * u * (y / (2 * π))) * Complex.I) • pe3RefFn X u) =
      fun u => |-Real.exp (-u)| • ((Real.exp (-u) : ℂ) ^ (s - 1) * ((Real.exp (-Real.exp (-u)) - Real.exp (-a * Real.exp (-u)) : ℝ) : ℂ)) := by
    ext u; rw [abs_of_neg (neg_neg_iff_pos.mpr (Real.exp_pos (-u))), neg_neg, real_smul, smul_eq_mul,
      show -2 * π * u * (y / (2 * π)) = -u * y by field_simp [Real.pi_ne_zero],
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos (-u)).ne'),
      ← Complex.ofReal_log (Real.exp_pos (-u)).le, Real.log_exp,
      show ((-u : ℝ) : ℂ) * (s - 1) = (-(u : ℂ) * s) + (u : ℂ) by dsimp [s]; push_cast; ring,
      Complex.exp_add, show Complex.exp (u : ℂ) = (Real.exp u : ℂ) from (Complex.ofReal_exp u).symm]
    have hexp_inv : (Real.exp (-u) : ℂ) * (Complex.exp (-(u : ℂ) * s) * (Real.exp u : ℂ)) = Complex.exp (-(u : ℂ) * s) :=
      (by push_cast; ring : _ = Complex.exp (-(u : ℂ) * s) * ((Real.exp (-u) * Real.exp u : ℝ) : ℂ)).trans
        (by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, mul_one])
    dsimp [pe3RefFn]; rw [← mul_assoc _ _ ((Real.exp (-Real.exp (-u)) - _ : ℝ) : ℂ), hexp_inv]; congr 2; dsimp [s]; push_cast; ring1
  have him : (fun u : ℝ => Real.exp (-u)) '' univ = Ioi 0 := by
    ext t; simp only [mem_image, mem_univ, true_and, mem_Ioi]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ Real.exp_pos (-u), fun ht => ⟨-Real.log t, by rw [neg_neg, Real.exp_log ht]⟩⟩
  have hsub := integral_image_eq_integral_abs_deriv_smul (f := fun u : ℝ => Real.exp (-u)) (f' := fun u : ℝ => -Real.exp (-u))
    MeasurableSet.univ (fun u _ => ((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).congr_deriv (mul_neg_one _) |>.hasDerivWithinAt)
    (fun u₁ _ u₂ _ h => neg_inj.mp (Real.exp_injective h))
    (fun t : ℝ => (t : ℂ) ^ (s - 1) * ((Real.exp (-t) - Real.exp (-a * t) : ℝ) : ℂ))
  rw [← setIntegral_univ, show ∫ u in univ, Complex.exp (↑(-2 * π * u * (y / (2 * π))) * Complex.I) • pe3RefFn X u =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * ((Real.exp (-t) - Real.exp (-a * t) : ℝ) : ℂ) by rw [hcomp_eq, ← hsub, him]]
  let u_ibp : ℝ → ℂ := fun t => s⁻¹ * (t : ℂ) ^ s; let v_ibp : ℝ → ℂ := fun t => ((Real.exp (-t) - Real.exp (-a * t) : ℝ) : ℂ)
  let u'_ibp : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1); let v'_ibp : ℝ → ℂ := fun t => ((-Real.exp (-t) + a * Real.exp (-a * t) : ℝ) : ℂ)
  have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt u_ibp (u'_ibp t) t := fun t ht =>
    ((hasDerivAt_ofReal_cpow_const (mem_Ioi.mp ht).ne' (r := s) hs0).const_mul s⁻¹).congr_deriv (by rw [← mul_assoc, inv_mul_cancel₀ hs0, one_mul])
  have hv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt v_ibp (v'_ibp t) t := fun t _ => by
    have h1 := (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (-a * x)) (Real.exp (-a * t) * (-a * 1)) t :=
      (Real.hasDerivAt_exp (-a * t)).comp t ((hasDerivAt_id t).const_mul (-a))
    exact (h1.sub h2).ofReal_comp.congr_deriv (by dsimp [v'_ibp]; push_cast; ring)
  have hu_norm : ∀ {t : ℝ}, t ∈ Ioi 0 → ‖(t : ℂ) ^ s‖ = 1 := fun {t} ht => by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, show s.re = 0 by simp [s], Real.rpow_zero]
  have huv'_int : IntegrableOn (u'_ibp * v_ibp) (Ioi 0) := by
    have hm : AEStronglyMeasurable (u'_ibp * v_ibp) (volume.restrict (Ioi 0)) := ContinuousOn.aestronglyMeasurable
      (fun t ht => ((hasDerivAt_ofReal_cpow_const (mem_Ioi.mp ht).ne' (r := s - 1) hs1_ne).continuousAt.continuousWithinAt).mul
        (Complex.continuous_ofReal.comp (by fun_prop)).continuousWithinAt) measurableSet_Ioi
    have h1 : IntegrableOn (u'_ibp * v_ibp) (Ioc 0 1) := by
      refine (integrableOn_const (C := a - 1) (hs := measure_Ioc_lt_top.ne)).mono' (hm.mono_set Ioc_subset_Ioi_self) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hnm : ‖(t : ℂ) ^ (s - 1)‖ = t⁻¹ := by rw [Complex.norm_cpow_eq_rpow_re_of_pos ht.1, show (s - 1).re = -1 by simp [s], Real.rpow_neg_one]
      have hnn : 0 ≤ Real.exp (-t) - Real.exp (-a * t) := sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith [ht.1]))
      have hle : Real.exp (-t) - Real.exp (-a * t) ≤ (a - 1) * t := by
        rw [show Real.exp (-t) - Real.exp (-a * t) = Real.exp (-t) * (1 - Real.exp (-((a - 1) * t))) by rw [mul_sub, mul_one, ← Real.exp_add]; congr 2; ring]
        exact (mul_le_mul (Real.exp_le_one_iff.mpr (by linarith [ht.1])) (one_sub_exp_neg_le_self (mul_nonneg (sub_nonneg.mpr ha1.le) ht.1.le)).2
          (one_sub_exp_neg_le_self (mul_nonneg (sub_nonneg.mpr ha1.le) ht.1.le)).1 zero_le_one).trans_eq (one_mul _)
      simp only [Pi.mul_apply, norm_mul, u'_ibp, v_ibp, hnm, Complex.norm_real, Real.norm_of_nonneg hnn]
      exact (mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr ht.1.le)).trans_eq (by field_simp [ht.1.ne'])
    have h2 : IntegrableOn (u'_ibp * v_ibp) (Ioi 1) := by
      refine (integrableOn_exp_neg_Ioi 1).mono' (hm.mono_set (Ioi_subset_Ioi zero_le_one)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hnm : ‖(t : ℂ) ^ (s - 1)‖ = t⁻¹ := by rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [mem_Ioi.mp ht]), show (s - 1).re = -1 by simp [s], Real.rpow_neg_one]
      have hnn : 0 ≤ Real.exp (-t) - Real.exp (-a * t) := sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith [ha1, mem_Ioi.mp ht]))
      simp only [Pi.mul_apply, norm_mul, u'_ibp, v_ibp, hnm, Complex.norm_real, Real.norm_of_nonneg hnn]
      exact (mul_le_mul (inv_le_one_of_one_le₀ ht.le) (by linarith [Real.exp_pos (-a * t)]) hnn zero_le_one).trans_eq (one_mul _)
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]; exact ⟨h1, h2⟩
  have hcpow_int : ∀ r : ℝ, 0 < r → IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((1 + s) - 1) * Complex.exp (-((r : ℂ) * (t : ℂ)))) (Ioi 0) := fun r hr =>
    (exp_neg_mul_Ioi_bd 0 hr).1.mono' (ContinuousOn.aestronglyMeasurable (fun t ht =>
      ((hasDerivAt_ofReal_cpow_const (mem_Ioi.mp ht).ne' (r := (1 + s) - 1) (by rw [add_sub_cancel_left]; exact hs0)).continuousAt.mul
        (Complex.continuous_exp.comp (by fun_prop)).continuousAt).continuousWithinAt) measurableSet_Ioi)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          rw [show (1 + s) - 1 = s by ring, norm_mul, hu_norm ht, one_mul,
            show Complex.exp (-((r : ℂ) * (t : ℂ))) = (Real.exp (-r * t) : ℂ) by rw [Complex.ofReal_exp]; congr 1; push_cast; ring,
            Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le])
  have hterm1_int := hcpow_int 1 one_pos; have hterm2_int := hcpow_int a ha0
  have huv'_r_int : IntegrableOn (u_ibp * v'_ibp) (Ioi 0) := by
    rw [show u_ibp * v'_ibp = fun t : ℝ => s⁻¹ *
        (-((t : ℂ) ^ ((1 + s) - 1) * Complex.exp (-((1 : ℂ) * (t : ℂ)))) + (a : ℂ) * ((t : ℂ) ^ ((1 + s) - 1) * Complex.exp (-((a : ℂ) * (t : ℂ))))) from
      funext fun t => by dsimp [u_ibp, v'_ibp]; rw [show (1 + s) - 1 = s by ring1]; push_cast; simp only [one_mul, neg_mul]; ring1]
    exact (hterm1_int.neg.add (hterm2_int.const_mul (a : ℂ))).const_mul _
  have h_bd : ∀ t ∈ Ioi (0 : ℝ), ‖(u_ibp * v_ibp) t‖ ≤ ‖s‖⁻¹ * |Real.exp (-t) - Real.exp (-a * t)| := fun t ht => by
    dsimp [u_ibp, v_ibp]; rw [norm_mul, norm_mul, norm_inv, hu_norm ht, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hlim_inf : Tendsto (fun t : ℝ => ‖s‖⁻¹ * |Real.exp (-t) - Real.exp (-a * t)|) atTop (𝓝 0) := by
    have h2 : Tendsto (fun t : ℝ => Real.exp (-a * t)) atTop (𝓝 0) :=
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop ha0)).congr fun t => by simp [neg_mul]
    refine squeeze_zero (fun _ => by positivity) (fun t => mul_le_mul_of_nonneg_left
      ((abs_sub _ _).trans (by rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)])) (by positivity)) ?_
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.add h2).const_mul ‖s‖⁻¹
  have hibp := integral_Ioi_deriv_mul_eq_sub hu hv (huv'_int.add huv'_r_int)
    (tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (by filter_upwards [self_mem_nhdsWithin] with t ht; exact h_bd t ht)
      (by simpa using ((by fun_prop : ContinuousAt (fun t : ℝ => ‖s‖⁻¹ * |Real.exp (-t) - Real.exp (-a * t)|) 0)).tendsto.mono_left nhdsWithin_le_nhds)))
    (tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (by filter_upwards [eventually_gt_atTop 0] with t ht; exact h_bd t ht) hlim_inf))
  have hsum_int : ∫ x in Ioi (0 : ℝ), u'_ibp x * v_ibp x + u_ibp x * v'_ibp x =
      (∫ x in Ioi (0 : ℝ), u'_ibp x * v_ibp x) + ∫ x in Ioi (0 : ℝ), u_ibp x * v'_ibp x := integral_add huv'_int huv'_r_int
  rw [sub_zero, hsum_int, add_eq_zero_iff_eq_neg] at hibp
  have hsp : ∫ t in Ioi (0 : ℝ), -((t : ℂ) ^ (1 + s - 1) * Complex.exp (-(((1 : ℝ) : ℂ) * (t : ℂ)))) +
        (a : ℂ) * ((t : ℂ) ^ (1 + s - 1) * Complex.exp (-((a : ℂ) * (t : ℂ)))) =
      (-∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (1 + s - 1) * Complex.exp (-(((1 : ℝ) : ℂ) * (t : ℂ)))) +
        (a : ℂ) * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (1 + s - 1) * Complex.exp (-((a : ℂ) * (t : ℂ))) := by
    simpa only [Pi.neg_apply, integral_neg, integral_const_mul] using integral_add hterm1_int.neg (hterm2_int.const_mul (a : ℂ))
  rw [show ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * ((Real.exp (-t) - Real.exp (-a * t) : ℝ) : ℂ) = -∫ t in Ioi (0 : ℝ), u_ibp t * v'_ibp t from hibp,
    show (fun t : ℝ => u_ibp t * v'_ibp t) = fun t : ℝ => s⁻¹ * (-((t : ℂ) ^ (1 + s - 1) * Complex.exp (-(((1 : ℝ) : ℂ) * (t : ℂ)))) +
      (a : ℂ) * ((t : ℂ) ^ (1 + s - 1) * Complex.exp (-((a : ℂ) * (t : ℂ))))) from funext fun t => by
        dsimp [u_ibp, v'_ibp]; rw [show (1 + s) - 1 = s by ring1]; push_cast; simp only [one_mul, neg_mul]; ring1, integral_const_mul, hsp]
  have hs1_re : 0 < (1 + s).re := by simp [s]
  have ha_pow : (a : ℂ) * ((1 / (a : ℂ)) ^ (1 + s)) = Complex.exp (-((ceCs * X : ℝ) : ℂ) * s) := by
    rw [Complex.cpow_add _ _ (by simp [ha0.ne']), Complex.cpow_one, ← mul_assoc, mul_one_div_cancel (Complex.ofReal_ne_zero.mpr ha0.ne'),
      one_mul, one_div, ← Complex.ofReal_inv, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (inv_pos.mpr ha0).ne'),
      ← Complex.ofReal_log (inv_pos.mpr ha0).le, Real.log_inv, show Real.log a = ceCs * X from Real.log_exp _]
    congr 1; push_cast; ring1
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := 1 + s) (r := 1) hs1_re one_pos, Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := 1 + s) (r := a) hs1_re ha0]
  simp only [Complex.ofReal_one, div_one, Complex.one_cpow, one_mul]
  rw [neg_add_eq_sub, show (a : ℂ) * ((1 / (a : ℂ)) ^ (1 + s) * Complex.Gamma (1 + s)) = Complex.Gamma (1 + s) * Complex.exp (-((ceCs * X : ℝ) : ℂ) * s) by
      rw [← mul_assoc, ha_pow, mul_comm], show Complex.Gamma (1 + s) = s * Complex.Gamma s by rw [add_comm, Complex.Gamma_add_one s hs0]]
  calc -(s⁻¹ * (s * Complex.Gamma s * Complex.exp (-((ceCs * X : ℝ) : ℂ) * s) - s * Complex.Gamma s))
      = (s⁻¹ * s) * Complex.Gamma s * (1 - Complex.exp (-((ceCs * X : ℝ) : ℂ) * s)) := by ring1
    _ = Complex.Gamma ((y : ℂ) * Complex.I) * (1 - Complex.exp (-((ceCs * X : ℝ) : ℂ) * (y : ℂ) * Complex.I)) := by
        rw [inv_mul_cancel₀ hs0, one_mul]; dsimp [s]; simp only [mul_assoc]

private lemma integrable_fourier_pe3RefFn {X : ℝ} (hX : 0 < X) : Integrable (𝓕 (pe3RefFn X)) := by
  have hcont : Continuous (𝓕 (pe3RefFn X)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ (pe3RefFn_integrable hX)
  have hgam := (gamma_mul_min_integrable (mul_nonneg ceCs_pos.le hX.le)).comp_mul_left' (by positivity : (2 * π : ℝ) ≠ 0)
  refine hgam.mono' hcont.aestronglyMeasurable ?_
  filter_upwards [ae_iff.mpr (by simp : volume {w : ℝ | ¬w ≠ 0} = 0)] with w hw
  have hfw := fourier_pe3RefFn_eq hX (mul_ne_zero (by positivity : (2 * π : ℝ) ≠ 0) hw)
  rw [show (2 * π * w) / (2 * π) = w by field_simp [Real.pi_ne_zero]] at hfw
  rw [hfw, norm_mul,
    show Complex.Gamma (((2 * π * w : ℝ) : ℂ) * Complex.I) = Complex.Gamma (Complex.I * ((2 * π * w : ℝ) : ℂ)) from congrArg Complex.Gamma (mul_comm _ _),
    show -((ceCs * X : ℝ) : ℂ) * ((2 * π * w : ℝ) : ℂ) * Complex.I = -(Complex.I * ((ceCs * X : ℝ) : ℂ) * ((2 * π * w : ℝ) : ℂ)) by push_cast; ring]
  exact mul_le_mul_of_nonneg_left (norm_osc_ceCs_le hX.le (2 * π * w)) (norm_nonneg _)

/-- **Exact reference Mellin inversion (`ce_o1_pre_edge.tex` `PE.3`).** -/
theorem pe3_reference_mellin_inversion {Δ X : ℝ} (hΔ : 0 < Δ) (hX : 0 < X) :
    (1 / (2 * π : ℂ)) * ∫ y : ℝ, (4 : ℂ) ^ (-(Complex.I * (y : ℂ))) *
        Complex.Gamma (Complex.I * (y : ℂ)) * (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))) *
        (Δ : ℂ) ^ (-(Complex.I * (y : ℂ))) =
      ((Real.exp (-4 * Δ) - Real.exp (-4 * Real.exp (ceCs * X) * Δ) : ℝ) : ℂ) ∧
    0 ≤ Real.exp (-4 * Δ) - Real.exp (-4 * Real.exp (ceCs * X) * Δ) := by
  have ha1 : 1 < Real.exp (ceCs * X) := Real.one_lt_exp_iff.mpr (mul_pos ceCs_pos hX)
  refine ⟨?_, sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith))⟩
  have hinv := (show Continuous (pe3RefFn X) by unfold pe3RefFn; fun_prop).fourierInv_fourier_eq
    (pe3RefFn_integrable hX) (integrable_fourier_pe3RefFn hX)
  have hval := congrArg (fun g : ℝ → ℂ => g (-Real.log (4 * Δ))) hinv
  rw [Real.fourierInv_eq'] at hval
  have hscale := Measure.integral_comp_mul_left (fun y : ℝ => (4 : ℂ) ^ (-(Complex.I * (y : ℂ))) * Complex.Gamma (Complex.I * (y : ℂ)) *
      (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))) * (Δ : ℂ) ^ (-(Complex.I * (y : ℂ)))) (2 * π)
  have hsub : ∫ x : ℝ, Complex.exp (↑(2 * π * ⟪x, -Real.log (4 * Δ)⟫) * Complex.I) • 𝓕 (pe3RefFn X) x =
      ∫ x : ℝ, (4 : ℂ) ^ (-(Complex.I * ((2 * π * x : ℝ) : ℂ))) * Complex.Gamma (Complex.I * ((2 * π * x : ℝ) : ℂ)) *
        (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * ((2 * π * x : ℝ) : ℂ)))) * (Δ : ℂ) ^ (-(Complex.I * ((2 * π * x : ℝ) : ℂ))) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_iff.mpr (by simp : volume {w : ℝ | ¬w ≠ 0} = 0)] with w hw
    have hfour := fourier_pe3RefFn_eq hX (mul_ne_zero (by positivity : (2 * π : ℝ) ≠ 0) hw)
    rw [show (2 * π * w) / (2 * π) = w by field_simp [Real.pi_ne_zero]] at hfour
    rw [smul_eq_mul, hfour, RCLike.inner_apply, starRingEnd_apply, star_trivial]
    have hexp_pow : Complex.exp (↑(2 * π * (-Real.log (4 * Δ) * w)) * Complex.I) =
        (4 : ℂ) ^ (-(Complex.I * ((2 * π * w : ℝ) : ℂ))) * (Δ : ℂ) ^ (-(Complex.I * ((2 * π * w : ℝ) : ℂ))) := by
      rw [Complex.cpow_def_of_ne_zero (by norm_num : (4 : ℂ) ≠ 0), Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hΔ.ne'),
        ← Complex.exp_add, ← add_mul, show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 4),
        ← Complex.ofReal_log hΔ.le, ← Complex.ofReal_add, ← Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hΔ.ne']
      congr 1; push_cast; ring
    rw [hexp_pow, show Complex.Gamma (((2 * π * w : ℝ) : ℂ) * Complex.I) = Complex.Gamma (Complex.I * ((2 * π * w : ℝ) : ℂ)) from congrArg Complex.Gamma (mul_comm _ _),
      show -((ceCs * X : ℝ) : ℂ) * ((2 * π * w : ℝ) : ℂ) * Complex.I = -(Complex.I * ((ceCs * X : ℝ) : ℂ) * ((2 * π * w : ℝ) : ℂ)) by ring1]
    ring1
  have hpi_id : ((1 / (2 * π) : ℝ) : ℂ) = 1 / (2 * π : ℂ) := by push_cast; rfl
  rw [hsub, hscale, real_smul, abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * π)), inv_eq_one_div, hpi_id] at hval
  exact hval.trans (by dsimp [pe3RefFn]; rw [neg_neg, Real.exp_log (by positivity : 0 < 4 * Δ)]; congr 2 <;> (congr 1; ring1))

/-- Measure integration of `pe3_reference_mellin_inversion` from `min X 1` integrability and a uniform `O(|y|^{1/2})` truncation bound. -/
theorem pe3_measure_inversion_of_bounds {ν : Measure ℝ}
    (hν_int : IntegrableOn (fun X : ℝ => min X 1) (Ioi 0) ν) {C_H : ℝ} (_hC_H : 0 ≤ C_H)
    (h_trunc : ∀ (n : ℕ) (y : ℝ),
      ‖∫ X in Icc (((n : ℝ) + 1)⁻¹) ((n : ℝ) + 1), (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))) ∂ν‖ ≤ C_H * |y| ^ (1 / 2 : ℝ))
    {Δ : ℝ} (hΔ : 0 < Δ) :
    (1 / (2 * π : ℂ)) * ∫ y : ℝ, (4 : ℂ) ^ (-(Complex.I * (y : ℂ))) * Complex.Gamma (Complex.I * (y : ℂ)) *
        (∫ X in Ioi (0 : ℝ), (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))) ∂ν) * (Δ : ℂ) ^ (-(Complex.I * (y : ℂ))) =
      ((∫ X in Ioi (0 : ℝ), (Real.exp (-4 * Δ) - Real.exp (-4 * Real.exp (ceCs * X) * Δ)) ∂ν : ℝ) : ℂ) ∧
    0 ≤ ∫ X in Ioi (0 : ℝ), (Real.exp (-4 * Δ) - Real.exp (-4 * Real.exp (ceCs * X) * Δ)) ∂ν := by
  have hcs := ceCs_pos
  have hrad_nn : ∀ X ∈ Ioi (0 : ℝ), 0 ≤ Real.exp (-4 * Δ) - Real.exp (-4 * Real.exp (ceCs * X) * Δ) := fun X hX =>
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith [Real.one_lt_exp_iff.mpr (mul_pos hcs (mem_Ioi.mp hX))]))
  have hrad_int : IntegrableOn (fun X : ℝ => Real.exp (-4 * Δ) - Real.exp (-4 * Real.exp (ceCs * X) * Δ)) (Ioi 0) ν := by
    let C_r : ℝ := max (4 * Δ * ceCs * Real.exp ceCs) 1
    refine (hν_int.const_mul C_r).mono' ((Continuous.aestronglyMeasurable (by fun_prop)).restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with X (hX : 0 < X)
    rw [Real.norm_of_nonneg (hrad_nn X hX)]
    rcases le_or_gt X 1 with hX1 | hX1
    · rw [min_eq_left hX1]
      have hsub1 : Real.exp (ceCs * X) - 1 ≤ ceCs * X * Real.exp ceCs := by
        have h2 := mul_le_mul_of_nonneg_right (one_sub_exp_neg_le_self (mul_nonneg hcs.le hX.le)).2 (Real.exp_pos (ceCs * X)).le
        rw [sub_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
        exact h2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity))
      rw [show Real.exp (-4 * Δ) - Real.exp (-4 * Real.exp (ceCs * X) * Δ) =
        Real.exp (-4 * Δ) * (1 - Real.exp (-(4 * Δ * (Real.exp (ceCs * X) - 1)))) by rw [mul_sub, mul_one, ← Real.exp_add]; congr 2; ring]
      exact (mul_le_mul (Real.exp_le_one_iff.mpr (by linarith))
        ((one_sub_exp_neg_le_self (mul_nonneg (by positivity) (sub_nonneg.mpr (Real.one_le_exp (by positivity))))).2.trans
          (mul_le_mul_of_nonneg_left hsub1 (by positivity)))
        (one_sub_exp_neg_le_self (mul_nonneg (by positivity) (sub_nonneg.mpr (Real.one_le_exp (by positivity))))).1 zero_le_one).trans
        (by calc 1 * (4 * Δ * (ceCs * X * Real.exp ceCs)) = (4 * Δ * ceCs * Real.exp ceCs) * X := by ring
          _ ≤ C_r * X := mul_le_mul_of_nonneg_right (le_max_left _ _) hX.le)
    · rw [min_eq_right hX1.le, mul_one]
      exact (show Real.exp (-4 * Δ) - Real.exp (-4 * Real.exp (ceCs * X) * Δ) ≤ 1 by
        linarith [Real.exp_le_one_iff.mpr (by linarith : -4 * Δ ≤ 0), Real.exp_pos (-4 * Real.exp (ceCs * X) * Δ)]).trans (le_max_right _ _)
  refine ⟨?_, setIntegral_nonneg measurableSet_Ioi hrad_nn⟩
  let K : ℕ → Set ℝ := fun n => Icc (((n : ℝ) + 1)⁻¹) ((n : ℝ) + 1)
  have hK_sub : ∀ n : ℕ, K n ⊆ Ioi 0 := fun n X hX => lt_of_lt_of_le (by positivity) hX.1
  have hK_fin : ∀ n : ℕ, ν (K n) < ⊤ := fun n => by
    let c₀ : ℝ := min (((n : ℝ) + 1)⁻¹) 1; have hc₀ : 0 < c₀ := lt_min (by positivity) one_pos
    have hlt : ∫⁻ X in K n, ENNReal.ofReal c₀ ∂ν < ⊤ :=
      (setLIntegral_mono' measurableSet_Icc fun X hX => by
        rw [Real.enorm_of_nonneg (le_min (hK_sub n hX).le zero_le_one)]; exact ENNReal.ofReal_le_ofReal (min_le_min hX.1 le_rfl)).trans_lt
        (hν_int.mono_set (hK_sub n)).2
    rw [setLIntegral_const] at hlt; by_contra htop; rw [not_lt, top_le_iff] at htop
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc₀).ne'] at hlt; exact lt_irrefl ⊤ hlt
  have hcov : AECover (ν.restrict (Ioi 0)) atTop K :=
    { ae_eventually_mem := (ae_restrict_mem measurableSet_Ioi).mono fun X (hX : 0 < X) =>
        (((tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)).eventually
          (Iio_mem_nhds hX)).mono fun _ h => h.le).and ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).eventually_ge_atTop X)
      measurableSet := fun _ => measurableSet_Icc }
  have hnz_y : ∀ᵐ y : ℝ, y ≠ 0 := ae_iff.mpr (by simp)
  have hfubini : ∀ n : ℕ,
      (1 / (2 * π : ℂ)) * ∫ y : ℝ, (4 : ℂ) ^ (-(Complex.I * (y : ℂ))) * Complex.Gamma (Complex.I * (y : ℂ)) *
          (∫ X in K n, (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))) ∂ν) * (Δ : ℂ) ^ (-(Complex.I * (y : ℂ))) =
        ((∫ X in K n, (Real.exp (-4 * Δ) - Real.exp (-4 * Real.exp (ceCs * X) * Δ)) ∂ν : ℝ) : ℂ) := by
    intro n; let μn : Measure ℝ := ν.restrict (K n); have : IsFiniteMeasure μn := ⟨by simpa [μn] using hK_fin n⟩
    let F : ℝ → ℝ → ℂ := fun y X => (4 : ℂ) ^ (-(Complex.I * (y : ℂ))) * Complex.Gamma (Complex.I * (y : ℂ)) *
      (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))) * (Δ : ℂ) ^ (-(Complex.I * (y : ℂ)))
    have h4p : Continuous (fun p : ℝ × ℝ => (4 : ℂ) ^ (-(Complex.I * (p.1 : ℂ)))) := by
      rw [show (fun p : ℝ × ℝ => (4 : ℂ) ^ (-(Complex.I * (p.1 : ℂ)))) = fun p => ((4 : ℝ) : ℂ) ^ (-(Complex.I * (p.1 : ℂ))) from
        funext fun _ => by norm_num]
      exact (continuous_ofReal_cpow_neg_I (by norm_num : (0 : ℝ) < 4)).comp continuous_fst
    have hF_meas : AEStronglyMeasurable (Function.uncurry F) (volume.prod μn) :=
      (((h4p.aestronglyMeasurable.mul (aestronglyMeasurable_gamma_pure_imag.comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst)).mul (Continuous.aestronglyMeasurable (by fun_prop))).mul
          ((continuous_ofReal_cpow_neg_I hΔ).comp continuous_fst).aestronglyMeasurable)
    have hF_prod : Integrable (Function.uncurry F) (volume.prod μn) := by
      refine ((gamma_mul_min_integrable (by positivity : 0 ≤ ceCs * ((n : ℝ) + 1))).mul_prod
        (integrable_const (1 : ℝ))).mono' hF_meas ?_
      filter_upwards [(Measure.ae_prod_iff_ae_ae ((measurableSet_singleton (0 : ℝ)).compl.preimage measurable_fst)).mpr
          (hnz_y.mono fun y hy => ae_of_all _ fun _ => hy),
        (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_snd)).mpr
          (ae_of_all _ fun _ => ae_restrict_mem measurableSet_Icc)] with p hp1 hp2
      dsimp only [Function.uncurry, F]
      have h4n : ‖(4 : ℂ) ^ (-(Complex.I * (p.1 : ℂ)))‖ = 1 := by
        rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num]; exact norm_ofReal_cpow_neg_I (by norm_num) p.1
      rw [norm_mul, norm_mul, norm_mul, h4n, one_mul, norm_ofReal_cpow_neg_I hΔ p.1, mul_one]
      exact (mul_le_mul_of_nonneg_left ((norm_osc_ceCs_le (hK_sub n hp2).le p.1).trans
        (min_le_min (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp2.2 hcs.le) (abs_nonneg _)) le_rfl)) (norm_nonneg _)).trans_eq (mul_one _).symm
    have hlhs_pull : ∫ y : ℝ, (4 : ℂ) ^ (-(Complex.I * (y : ℂ))) * Complex.Gamma (Complex.I * (y : ℂ)) *
          (∫ X in K n, (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))) ∂ν) * (Δ : ℂ) ^ (-(Complex.I * (y : ℂ))) =
        ∫ y : ℝ, ∫ X : ℝ, F y X ∂μn := integral_congr_ae (ae_of_all _ fun y => by dsimp only; rw [← integral_const_mul, ← integral_mul_const])
    rw [hlhs_pull, MeasureTheory.integral_integral_swap hF_prod, ← integral_const_mul,
      setIntegral_congr_fun measurableSet_Icc (fun X hX => (pe3_reference_mellin_inversion hΔ (hK_sub n hX)).1)]
    exact integral_complex_ofReal
  have h_osc_int : ∀ y : ℝ, IntegrableOn (fun X : ℝ => 1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))) (Ioi 0) ν := fun y =>
    (hν_int.const_mul (max (ceCs * |y|) 2)).mono' ((Continuous.aestronglyMeasurable (by fun_prop)).restrict)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX; exact osc_norm_le_mul_min hX y)
  let dom_y : ℝ → ℝ := fun y => (Icc (-1 : ℝ) 1).indicator (fun t => C_H * |t| ^ (-(1 / 2 : ℝ))) y + (C_H * √(3 * π)) * Real.exp (-(π / 2) * |y|)
  have hLHS_tendsto : Tendsto (fun n : ℕ => (1 / (2 * π : ℂ)) * ∫ y : ℝ,
      (4 : ℂ) ^ (-(Complex.I * (y : ℂ))) * Complex.Gamma (Complex.I * (y : ℂ)) *
        (∫ X in K n, (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))) ∂ν) * (Δ : ℂ) ^ (-(Complex.I * (y : ℂ)))) atTop
      (𝓝 ((1 / (2 * π : ℂ)) * ∫ y : ℝ, (4 : ℂ) ^ (-(Complex.I * (y : ℂ))) * Complex.Gamma (Complex.I * (y : ℂ)) *
        (∫ X in Ioi (0 : ℝ), (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))) ∂ν) * (Δ : ℂ) ^ (-(Complex.I * (y : ℂ))))) :=
    tendsto_const_nhds.mul (tendsto_integral_of_dominated_convergence dom_y
      (fun n => (gamma_mul_half_integrable hΔ (continuous_osc_setIntegral measurableSet_Icc (hK_sub n) (hν_int.mono_set (hK_sub n))) (h_trunc n)).aestronglyMeasurable)
      integrable_gamma_piecewise (fun n => hnz_y.mono fun y hy => gamma_mul_half_norm_le _ (h_trunc n) hΔ y hy)
      (ae_of_all _ fun y => (tendsto_const_nhds.mul ((hcov.integral_tendsto_of_countably_generated (h_osc_int y)).congr fun n => by
        rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr (hK_sub n)])).mul tendsto_const_nhds))
  exact tendsto_nhds_unique (hLHS_tendsto.congr fun n => hfubini n)
    (Complex.continuous_ofReal.continuousAt.tendsto.comp ((hcov.integral_tendsto_of_countably_generated hrad_int).congr fun n => by
      rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr (hK_sub n)]))

/-- **Measure integration of reference Mellin inversion (`ce_o1_pre_edge.tex` `PE.3`) for densities `0 ≤ g X ≤ C X^{-3/2}`.** -/
theorem pe3_measure_inversion {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg_meas : AEMeasurable g (volume.restrict (Ioi 0))) (hg_nn : ∀ X ∈ Ioi (0 : ℝ), 0 ≤ g X)
    (hg_le : ∀ X ∈ Ioi (0 : ℝ), g X ≤ C * X ^ (-(3 / 2 : ℝ))) {Δ : ℝ} (hΔ : 0 < Δ) :
    let ν := volume.withDensity fun X => ENNReal.ofReal (g X)
    (1 / (2 * π : ℂ)) * ∫ y : ℝ, (4 : ℂ) ^ (-(Complex.I * (y : ℂ))) * Complex.Gamma (Complex.I * (y : ℂ)) *
        (∫ X in Ioi (0 : ℝ), (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))) ∂ν) * (Δ : ℂ) ^ (-(Complex.I * (y : ℂ))) =
      ((∫ X in Ioi (0 : ℝ), (Real.exp (-4 * Δ) - Real.exp (-4 * Real.exp (ceCs * X) * Δ)) ∂ν : ℝ) : ℂ) ∧
    0 ≤ ∫ X in Ioi (0 : ℝ), (Real.exp (-4 * Δ) - Real.exp (-4 * Real.exp (ceCs * X) * Δ)) ∂ν := by
  have h_trunc : ∀ (n : ℕ) (y : ℝ),
      ‖∫ X in Icc (((n : ℝ) + 1)⁻¹) ((n : ℝ) + 1), (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ))))
          ∂(volume.withDensity fun X => ENNReal.ofReal (g X))‖ ≤ ((2 * ceCs + 4) * C) * |y| ^ (1 / 2 : ℝ) := fun n y => by
    let K := Icc (((n : ℝ) + 1)⁻¹) ((n : ℝ) + 1); let gn : ℝ → ℝ := K.indicator g
    have hgn_le : ∀ X ∈ Ioi (0 : ℝ), gn X ≤ C * X ^ (-(3 / 2 : ℝ)) := fun X hX => by
      by_cases hXK : X ∈ K
      · simp [gn, hXK, hg_le X hX]
      · simp [gn, hXK]; exact mul_nonneg hC (Real.rpow_nonneg (mem_Ioi.mp hX).le _)
    have hz := pe3a_holder_bound hC (hg_meas.indicator measurableSet_Icc) (fun X hX => indicator_nonneg (fun _ _ => hg_nn X hX) X)
      hgn_le (z := (y : ℂ) * Complex.I) (by simp)
    rw [show ‖(y : ℂ) * Complex.I‖ = |y| by simp [Complex.norm_real]] at hz
    have hK_sub : K ⊆ Ioi (0 : ℝ) := fun X hX => lt_of_lt_of_le (by positivity) hX.1
    have hL : (volume.withDensity fun X => ENNReal.ofReal (g X)).restrict K = (volume.withDensity fun X => ENNReal.ofReal (gn X)).restrict (Ioi 0) := by
      have hK_meas : MeasurableSet K := measurableSet_Icc
      ext s hs; rw [Measure.restrict_apply hs, Measure.restrict_apply hs, withDensity_apply _ (hs.inter hK_meas), withDensity_apply _ (hs.inter measurableSet_Ioi),
        ← lintegral_indicator (hs.inter hK_meas), ← lintegral_indicator (hs.inter measurableSet_Ioi)]
      congr 1; ext X; by_cases hX1 : X ∈ K <;> by_cases hX2 : X ∈ s <;> by_cases hX3 : X ∈ Ioi (0 : ℝ) <;> simp [gn, hX1, hX2, hX3]
      exact absurd (hK_sub hX1) hX3
    rw [show ∫ X in K, (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))) ∂(volume.withDensity fun X => ENNReal.ofReal (g X)) =
        ∫ X in Ioi (0 : ℝ), (1 - Complex.exp (-(ceCs : ℂ) * ((y : ℂ) * Complex.I) * (X : ℂ))) ∂(volume.withDensity fun X => ENNReal.ofReal (gn X)) by
      rw [hL]; congr 1; ext X; congr 2; push_cast; ring1]
    exact hz
  exact pe3_measure_inversion_of_bounds (pe3a_min_integrableOn hC hg_meas hg_nn hg_le) (mul_nonneg (by linarith [ceCs_pos]) hC) h_trunc hΔ

/-! ## Section 3: Theorem `PE.3` (`ce_o1_pre_edge.tex`) compact origin positivity -/

private lemma pe3_rem_Ioi_bound {Φ : ℝ → ℂ} {c C_err C_J C_B : ℝ}
    (hc4 : 4 ≤ c) (hC_err : 0 ≤ C_err) (hC_J : 0 ≤ C_J) (hC_B : 0 ≤ C_B)
    (hΦ_meas : AEStronglyMeasurable Φ (volume.restrict (Ioi 0)))
    (hΦ_lo : ∀ y : ℝ, 0 < y → y ≤ (8 / π) * Real.log (c ^ (1 / 3 : ℝ)) →
      ‖Φ y‖ ≤ ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ * (C_err * (c ^ (-(1 / 3 : ℝ))) ^ 2 * (y + y ^ 4)))
    (hΦ_hi : ∀ y : ℝ, (8 / π) * Real.log (c ^ (1 / 3 : ℝ)) < y →
      ‖Φ y‖ ≤ ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ * (Real.exp (c * hB (y / c)) * C_J + C_J + c ^ (-(1 / 3 : ℝ)) * C_B * y ^ (1 / 2 : ℝ))) :
    IntegrableOn Φ (Ioi 0) ∧ ∫ y in Ioi (0 : ℝ), ‖Φ y‖ ≤
      (2 * C_err + 2 * √(3 * π) * C_err * (24 / (π / 4) ^ 4) * (4 / π) + √(3 * π) * C_J * (4 / π) +
        √(3 * π) * C_J * (1 / 3) * (32 / Real.log 2 ^ 2) + (2 / π) * √(3 * π) * (C_J + C_B)) * c ^ (-(2 / 3 : ℝ)) := by
  have hc_pos : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  let ε : ℝ := c ^ (-(1 / 3 : ℝ)); have hε1 : ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
  have hε2 : ε ^ 2 = c ^ (-(2 / 3 : ℝ)) := by dsimp [ε]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc_pos.le]; norm_num
  let T : ℝ := (8 / π) * Real.log (c ^ (1 / 3 : ℝ))
  have hlog_c3 : Real.log (c ^ (1 / 3 : ℝ)) = (1 / 3 : ℝ) * Real.log c := Real.log_rpow hc_pos _
  have hlog4 : 2 * Real.log 2 ≤ Real.log c := (Real.log_pow 2 2).symm.trans_le (Real.log_le_log (by norm_num) (by linarith))
  have hT_ge1 : 1 ≤ T := by rw [show T = (8 * Real.log c) / (3 * π) by dsimp [T]; rw [hlog_c3]; ring, one_le_div (by positivity : 0 < 3 * π)]; nlinarith [Real.log_two_gt_d9, Real.pi_lt_d4]
  have hT_le_c : T ≤ c := by rw [show T = (8 * Real.log c) / (3 * π) by dsimp [T]; rw [hlog_c3]; ring, div_le_iff₀ (by positivity : 0 < 3 * π)]; nlinarith [Real.log_le_sub_one_of_pos hc_pos, Real.pi_gt_three]
  have hexp_T4 : Real.exp (-(π / 4) * T) = c ^ (-(2 / 3 : ℝ)) := by rw [Real.rpow_def_of_pos hc_pos]; congr 1; simp only [T, hlog_c3]; field_simp [Real.pi_ne_zero]; ring
  have hexp_T2 : Real.exp (-(π / 2) * T) = c ^ (-(4 / 3 : ℝ)) := by rw [Real.rpow_def_of_pos hc_pos]; congr 1; simp only [T, hlog_c3]; field_simp [Real.pi_ne_zero]; ring
  have hc43 : c ^ (-(4 / 3 : ℝ)) ≤ c ^ (-(2 / 3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
  have h_Ioc1 : IntegrableOn Φ (Ioc 0 1) ∧ ∫ y in Ioc 0 1, ‖Φ y‖ ≤ 2 * C_err * c ^ (-(2 / 3 : ℝ)) := by
    have hpt1 : ∀ y ∈ Ioc (0 : ℝ) 1, ‖Φ y‖ ≤ 2 * C_err * ε ^ 2 := fun y hy => by
      have hy4 : y ^ 4 ≤ y := ((mul_le_mul_of_nonneg_left (pow_le_one₀ (n := 3) hy.1.le hy.2) hy.1.le).trans_eq (mul_one y)).trans_eq' (by ring)
      exact ((hΦ_lo y hy.1 (hy.2.trans hT_ge1)).trans (mul_le_mul (norm_gamma_pure_imag_le_small hy.1 hy.2)
        (mul_le_mul_of_nonneg_left (by linarith [hy4] : y + y ^ 4 ≤ 2 * y) (mul_nonneg hC_err (sq_nonneg _)))
        (mul_nonneg (mul_nonneg hC_err (sq_nonneg _)) (add_nonneg hy.1.le (pow_nonneg hy.1.le 4))) (div_nonneg zero_le_one hy.1.le))).trans_eq
        (by dsimp [ε]; field_simp [hy.1.ne'])
    have hint1 : IntegrableOn Φ (Ioc 0 1) := (integrableOn_const (C := 2 * C_err * ε ^ 2) (hs := measure_Ioc_lt_top.ne)).mono'
      (hΦ_meas.mono_set Ioc_subset_Ioi_self) (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy; simpa using hpt1 y hy)
    exact ⟨hint1, (setIntegral_mono_on hint1.norm (integrableOn_const (hs := measure_Ioc_lt_top.ne)) measurableSet_Ioc hpt1).trans_eq (by simp [hε2])⟩
  have h_exp0 := exp_neg_mul_Ioi_bd 0 (by positivity : (0 : ℝ) < π / 4)
  have h_IocT : IntegrableOn Φ (Ioc 1 T) ∧
      ∫ y in Ioc 1 T, ‖Φ y‖ ≤ 2 * √(3 * π) * C_err * (24 / (π / 4) ^ 4) * (4 / π) * c ^ (-(2 / 3 : ℝ)) := by
    let K_T : ℝ := 2 * √(3 * π) * C_err * (24 / (π / 4) ^ 4)
    have hptT : ∀ y ∈ Ioc 1 T, ‖Φ y‖ ≤ (K_T * c ^ (-(2 / 3 : ℝ))) * Real.exp (-(π / 4) * y) := fun y hy => by
      have hy0 : 0 < y := by linarith [hy.1]
      have hy4 : y ≤ y ^ 4 := by
        calc y = y * 1 := (mul_one y).symm
          _ ≤ y * y ^ 3 := mul_le_mul_of_nonneg_left (one_le_pow₀ hy.1.le) hy0.le
          _ = y ^ 4 := by ring
      have hgam : ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ ≤ √(3 * π) * Real.exp (-(π / 2) * y) :=
        (norm_gamma_pure_imag_le_large hy.1.le).trans
          ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos hy.1.le (by norm_num)) (by positivity))
            (Real.exp_pos _).le).trans_eq (by ring))
      have hpow_exp : y ^ 4 * Real.exp (-(π / 4) * y) ≤ 24 / (π / 4) ^ 4 := by
        have hterm : ((π / 4) * y) ^ 4 / 24 ≤ Real.exp ((π / 4) * y) :=
          ((Finset.single_le_sum (f := fun i : ℕ => ((π / 4 * y) ^ i) / (Nat.factorial i : ℝ)) (fun _ _ => by positivity)
            (Finset.mem_range.mpr (by decide : 4 < 5))).trans (Real.sum_le_exp_of_nonneg (by positivity) 5)).trans_eq'
            (by norm_num [Nat.factorial_succ])
        have hterm' : ((π / 4) * y) ^ 4 ≤ 24 * Real.exp ((π / 4) * y) := by rw [div_le_iff₀ (by positivity : (0 : ℝ) < 24)] at hterm; linarith
        calc y ^ 4 * Real.exp (-(π / 4) * y) = (((π / 4) * y) ^ 4 * Real.exp (-((π / 4) * y))) / (π / 4) ^ 4 := by field_simp [Real.pi_ne_zero]
          _ ≤ (24 * Real.exp ((π / 4) * y) * Real.exp (-((π / 4) * y))) / (π / 4) ^ 4 := by gcongr
          _ = 24 / (π / 4) ^ 4 := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      calc ‖Φ y‖ ≤ √(3 * π) * Real.exp (-(π / 2) * y) * (C_err * ε ^ 2 * (2 * y ^ 4)) :=
            (hΦ_lo y hy0 hy.2).trans (mul_le_mul hgam (mul_le_mul_of_nonneg_left (by linarith [hy4]) (mul_nonneg hC_err (sq_nonneg _)))
              (mul_nonneg (mul_nonneg hC_err (sq_nonneg _)) (add_nonneg hy0.le (pow_nonneg hy0.le 4))) (by positivity))
        _ = (2 * √(3 * π) * C_err * (y ^ 4 * Real.exp (-(π / 4) * y))) * ε ^ 2 * Real.exp (-(π / 4) * y) := by
            rw [show -(π / 2) * y = -(π / 4) * y + -(π / 4) * y by ring, Real.exp_add]; ring
        _ ≤ (2 * √(3 * π) * C_err * (24 / (π / 4) ^ 4)) * ε ^ 2 * Real.exp (-(π / 4) * y) := by gcongr
        _ = (K_T * c ^ (-(2 / 3 : ℝ))) * Real.exp (-(π / 4) * y) := by dsimp [K_T]; rw [← hε2]
    have hintT : IntegrableOn Φ (Ioc 1 T) :=
      ((h_exp0.1.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi zero_le_one))).const_mul (K_T * c ^ (-(2 / 3 : ℝ)))).mono'
        (hΦ_meas.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi zero_le_one)))
        (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy; simpa using hptT y hy)
    have hbdT := setIntegral_mono_on hintT.norm ((h_exp0.1.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi zero_le_one))).const_mul _) measurableSet_Ioc hptT
    have hmono : ∫ y in Ioc 1 T, Real.exp (-(π / 4) * y) ≤ ∫ y in Ioi (0 : ℝ), Real.exp (-(π / 4) * y) :=
      setIntegral_mono_set h_exp0.1 (ae_of_all _ fun _ => (Real.exp_pos _).le)
        (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi zero_le_one)).eventuallyLE
    rw [integral_const_mul] at hbdT; rw [h_exp0.2, mul_zero, Real.exp_zero, show (1 : ℝ) / (π / 4) = 4 / π by ring] at hmono
    exact ⟨hintT, hbdT.trans ((mul_le_mul_of_nonneg_left hmono (by positivity)).trans_eq (by dsimp [K_T]; ring))⟩
  have h_expT4 := exp_neg_mul_Ioi_bd T (by positivity : (0 : ℝ) < π / 4)
  have h_expT2 := exp_neg_mul_Ioi_bd T (by positivity : (0 : ℝ) < π / 2)
  have hB2_bd : ∀ y ∈ Ioi T, ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ * (C_J + ε * C_B * y ^ (1 / 2 : ℝ)) ≤ √(3 * π) * (C_J + C_B) * Real.exp (-(π / 2) * y) := fun y hy => by
    have hy1 : 1 ≤ y := hT_ge1.trans (mem_Ioi.mp hy).le; have hgam_l := norm_gamma_pure_imag_le_large hy1
    have hy12 : y ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1 (by norm_num)
    have hgam : ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ ≤ √(3 * π) * Real.exp (-(π / 2) * y) := by
      calc ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ ≤ √(3 * π) * y ^ (-(1 / 2 : ℝ)) * Real.exp (-(π / 2) * y) := hgam_l
        _ ≤ √(3 * π) * 1 * Real.exp (-(π / 2) * y) := by gcongr
        _ = √(3 * π) * Real.exp (-(π / 2) * y) := by ring
    have ht1 : ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ * C_J ≤ √(3 * π) * C_J * Real.exp (-(π / 2) * y) := (mul_le_mul_of_nonneg_right hgam hC_J).trans_eq (by ring)
    have ht2 : ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ * (ε * C_B * y ^ (1 / 2 : ℝ)) ≤ √(3 * π) * C_B * Real.exp (-(π / 2) * y) :=
      (by gcongr : _ ≤ (√(3 * π) * y ^ (-(1 / 2 : ℝ)) * Real.exp (-(π / 2) * y)) * (1 * C_B * y ^ (1 / 2 : ℝ))).trans_eq
        (by calc _ = √(3 * π) * C_B * (y ^ (-(1 / 2 : ℝ)) * y ^ (1 / 2 : ℝ)) * Real.exp (-(π / 2) * y) := by ring
          _ = _ := by rw [← Real.rpow_add (by linarith), neg_add_cancel, Real.rpow_zero, mul_one])
    rw [mul_add]; exact (add_le_add ht1 ht2).trans_eq (by ring)
  have hrpow_c : IntegrableOn (fun y : ℝ => (y / c) ^ (-4 : ℝ)) (Ioi c) ∧ ∫ y in Ioi c, (y / c) ^ (-4 : ℝ) = c / 3 := by
    have heq : EqOn (fun y : ℝ => c ^ (4 : ℝ) * y ^ (-4 : ℝ)) (fun y => (y / c) ^ (-4 : ℝ)) (Ioi c) := fun y hy => by
      dsimp only; have hy0 : 0 < y := lt_trans hc_pos (mem_Ioi.mp hy)
      rw [div_eq_mul_inv, Real.mul_rpow hy0.le (inv_nonneg.mpr hc_pos.le), Real.inv_rpow hc_pos.le, Real.rpow_neg hc_pos.le, inv_inv, mul_comm]
    refine ⟨IntegrableOn.congr_fun ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) hc_pos).const_mul (c ^ (4 : ℝ))) heq measurableSet_Ioi, ?_⟩
    rw [← setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) hc_pos,
      show (-4 : ℝ) + 1 = -3 by norm_num, show -(c ^ (-3 : ℝ)) / (-3) = c ^ (-3 : ℝ) / 3 by ring, mul_div_assoc', ← Real.rpow_add hc_pos]; norm_num
  have hc_exp2 : c * (2 : ℝ) ^ (-((c - 4) / 2)) ≤ (32 / Real.log 2 ^ 2) * c ^ (-(2 / 3 : ℝ)) := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hpow : (Real.log 2 / 2 * c) ^ 2 / 2 ≤ Real.exp (Real.log 2 / 2 * c) :=
      ((Finset.single_le_sum (f := fun i : ℕ => (Real.log 2 / 2 * c) ^ i / (Nat.factorial i : ℝ)) (fun _ _ => by positivity)
        (Finset.mem_range.mpr (by decide : 2 < 3))).trans (Real.sum_le_exp_of_nonneg (by positivity) 3)).trans_eq' (by norm_num [Nat.factorial_succ])
    have hc2_le : c ^ 2 ≤ (8 / Real.log 2 ^ 2) * Real.exp (Real.log 2 / 2 * c) :=
      ((mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ 8 / Real.log 2 ^ 2)).trans_eq' (by field_simp [hlog2.ne']; ring)).trans_eq (by ring)
    have h2eq : (2 : ℝ) ^ (-((c - 4) / 2)) = 4 * Real.exp (-(Real.log 2 / 2 * c)) := by
      rw [Real.rpow_def_of_pos two_pos, show Real.log 2 * -((c - 4) / 2) = 2 * Real.log 2 + -(Real.log 2 / 2 * c) by ring,
        Real.exp_add, show (2 : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ (2 : ℕ)) by rw [Real.log_pow]; norm_num, Real.exp_log (by norm_num)]; norm_num
    have hc23 : c ^ (5 / 3 : ℝ) ≤ (8 / Real.log 2 ^ 2) * Real.exp (Real.log 2 / 2 * c) :=
      (Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num : (5 / 3 : ℝ) ≤ 2)).trans (by simpa [Real.rpow_two] using hc2_le)
    have hc_prod : c * (2 : ℝ) ^ (-((c - 4) / 2)) * c ^ (2 / 3 : ℝ) ≤ 32 / Real.log 2 ^ 2 := calc
      c * (2 : ℝ) ^ (-((c - 4) / 2)) * c ^ (2 / 3 : ℝ) = (c ^ (1 : ℝ) * c ^ (2 / 3 : ℝ)) * (4 * Real.exp (-(Real.log 2 / 2 * c))) := by rw [Real.rpow_one, h2eq]; ring
      _ = c ^ (5 / 3 : ℝ) * (4 * Real.exp (-(Real.log 2 / 2 * c))) := by rw [← Real.rpow_add hc_pos]; norm_num
      _ ≤ ((8 / Real.log 2 ^ 2) * Real.exp (Real.log 2 / 2 * c)) * (4 * Real.exp (-(Real.log 2 / 2 * c))) := by gcongr
      _ = 32 / Real.log 2 ^ 2 := by rw [mul_mul_mul_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]; ring
    rw [← le_div_iff₀ (Real.rpow_pos_of_pos hc_pos (2 / 3 : ℝ))] at hc_prod; exact hc_prod.trans_eq (by rw [div_eq_mul_inv, Real.rpow_neg hc_pos.le])
  let fB1 : ℝ → ℝ := fun y => if y ≤ c then Real.exp (-(π / 4) * y) else (2 : ℝ) ^ (-((c - 4) / 2)) * (y / c) ^ (-4 : ℝ)
  have hfB1_Ioc : IntegrableOn fB1 (Ioc T c) := (h_expT4.1.mono_set Ioc_subset_Ioi_self).congr_fun (fun y hy => by dsimp [fB1]; simp [hy.2]) measurableSet_Ioc
  have hfB1_Ioi : IntegrableOn fB1 (Ioi c) :=
    IntegrableOn.congr_fun (hrpow_c.1.const_mul ((2 : ℝ) ^ (-((c - 4) / 2)))) (fun y hy => by dsimp [fB1]; simp [not_le.mpr (mem_Ioi.mp hy)]) measurableSet_Ioi
  have hfB1_int : IntegrableOn fB1 (Ioi T) := (Ioc_union_Ioi_eq_Ioi hT_le_c) ▸ hfB1_Ioc.union hfB1_Ioi
  let B_hi : ℝ → ℝ := fun y => √(3 * π) * C_J * fB1 y + √(3 * π) * (C_J + C_B) * Real.exp (-(π / 2) * y)
  have hB_hi_int : IntegrableOn B_hi (Ioi T) := (hfB1_int.const_mul _).add (h_expT2.1.const_mul _)
  have hpt_hi : ∀ y ∈ Ioi T, ‖Φ y‖ ≤ B_hi y := fun y hy => by
    have hy1 : 1 ≤ y := hT_ge1.trans (mem_Ioi.mp hy).le; have hy12 : y ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1 (by norm_num)
    have h1 : ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ * (Real.exp (c * hB (y / c)) * C_J) ≤ √(3 * π) * C_J * fB1 y := by
      rw [← mul_assoc]; dsimp [fB1]; split_ifs with hyc
      · calc ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ * Real.exp (c * hB (y / c)) * C_J
            ≤ √(3 * π) * y ^ (-(1 / 2 : ℝ)) * Real.exp (-originPsi c y) * C_J := mul_le_mul_of_nonneg_right (norm_gamma_mul_exp_hB_le hc_pos hy1) hC_J
          _ ≤ √(3 * π) * 1 * Real.exp (-(π / 4) * y) * C_J := by gcongr; rw [neg_mul]; exact neg_le_neg (originPsi_ge_linear hc_pos (by linarith) hyc)
          _ = √(3 * π) * C_J * Real.exp (-(π / 4) * y) := by ring
      · calc ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ * Real.exp (c * hB (y / c)) * C_J
            ≤ √(3 * π) * y ^ (-(1 / 2 : ℝ)) * Real.exp (-originPsi c y) * C_J := mul_le_mul_of_nonneg_right (norm_gamma_mul_exp_hB_le hc_pos hy1) hC_J
          _ ≤ √(3 * π) * 1 * ((2 : ℝ) ^ (-((c - 4) / 2)) * (y / c) ^ (-4 : ℝ)) * C_J := by gcongr; exact exp_neg_originPsi_le hc4 (not_le.mp hyc).le
          _ = √(3 * π) * C_J * ((2 : ℝ) ^ (-((c - 4) / 2)) * (y / c) ^ (-4 : ℝ)) := by ring
    exact (hΦ_hi y (mem_Ioi.mp hy)).trans (by rw [add_assoc, mul_add]; exact add_le_add h1 (hB2_bd y hy))
  have h_IoiT : IntegrableOn Φ (Ioi T) := hB_hi_int.mono' (hΦ_meas.mono_set (Ioi_subset_Ioi (by linarith))) (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy; exact hpt_hi y hy)
  have h_IoiT_bd : ∫ y in Ioi T, ‖Φ y‖ ≤ (√(3 * π) * C_J * (4 / π) + √(3 * π) * C_J * (1 / 3) * (32 / Real.log 2 ^ 2) + (2 / π) * √(3 * π) * (C_J + C_B)) * c ^ (-(2 / 3 : ℝ)) := by
    have hfB1_split : ∫ y in Ioi T, fB1 y = (∫ y in Ioc T c, Real.exp (-(π / 4) * y)) + (2 : ℝ) ^ (-((c - 4) / 2)) * (c / 3) := by
      rw [← Ioc_union_Ioi_eq_Ioi hT_le_c, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hfB1_Ioc hfB1_Ioi,
        setIntegral_congr_fun measurableSet_Ioc (fun y hy => show fB1 y = Real.exp (-(π / 4) * y) by dsimp [fB1]; simp [hy.2]),
        setIntegral_congr_fun measurableSet_Ioi (fun y hy => show fB1 y = (2 : ℝ) ^ (-((c - 4) / 2)) * (y / c) ^ (-4 : ℝ) by
          dsimp [fB1]; simp [not_le.mpr (mem_Ioi.mp hy)]), integral_const_mul, hrpow_c.2]
    have h_Ioc_le : ∫ y in Ioc T c, Real.exp (-(π / 4) * y) ≤ (4 / π) * c ^ (-(2 / 3 : ℝ)) :=
      (setIntegral_mono_set h_expT4.1 (ae_of_all _ fun _ => (Real.exp_pos _).le) Ioc_subset_Ioi_self.eventuallyLE).trans_eq (by rw [h_expT4.2, hexp_T4]; field_simp [Real.pi_ne_zero])
    calc ∫ y in Ioi T, ‖Φ y‖ ≤ ∫ y in Ioi T, B_hi y := setIntegral_mono_on h_IoiT.norm hB_hi_int measurableSet_Ioi hpt_hi
      _ = √(3 * π) * C_J * (∫ y in Ioc T c, Real.exp (-(π / 4) * y)) + √(3 * π) * C_J * (1 / 3) * (c * (2 : ℝ) ^ (-((c - 4) / 2))) + (2 / π) * √(3 * π) * (C_J + C_B) * c ^ (-(4 / 3 : ℝ)) := by
          dsimp [B_hi]; rw [MeasureTheory.integral_add (hfB1_int.const_mul _) (h_expT2.1.const_mul _), integral_const_mul, integral_const_mul, h_expT2.2, hfB1_split, hexp_T2]; field_simp [Real.pi_ne_zero]
      _ ≤ √(3 * π) * C_J * ((4 / π) * c ^ (-(2 / 3 : ℝ))) + √(3 * π) * C_J * (1 / 3) * ((32 / Real.log 2 ^ 2) * c ^ (-(2 / 3 : ℝ))) + (2 / π) * √(3 * π) * (C_J + C_B) * c ^ (-(2 / 3 : ℝ)) :=
          add_le_add (add_le_add (by gcongr) (by gcongr)) (mul_le_mul_of_nonneg_left hc43 (by positivity))
      _ = _ := by ring
  have h_eq0T : Ioc (0 : ℝ) 1 ∪ Ioc 1 T = Ioc 0 T := Ioc_union_Ioc_eq_Ioc zero_le_one hT_ge1
  have h_eq0 : Ioc (0 : ℝ) T ∪ Ioi T = Ioi 0 := Ioc_union_Ioi_eq_Ioi (by linarith)
  have h_Ioc0T : IntegrableOn Φ (Ioc 0 T) := h_eq0T ▸ (h_Ioc1.1.union h_IocT.1)
  refine ⟨h_eq0 ▸ (h_Ioc0T.union h_IoiT), ?_⟩
  rw [← h_eq0, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi h_Ioc0T.norm h_IoiT.norm,
    ← h_eq0T, setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc h_Ioc1.1.norm h_IocT.1.norm]
  linarith [h_Ioc1.2, h_IocT.2, h_IoiT_bd]

/-- **Theorem `PE.3` remainder integral bound (`ce_o1_pre_edge.tex`):** `∫_ℝ ‖R_c(i y)‖ dy ≤ K_rem * c ^ (-2/3)`. -/
theorem pe3_remainder_integral_bound {Φ : ℝ → ℂ} {c C_err C_J C_B : ℝ}
    (hc4 : 4 ≤ c) (hC_err : 0 ≤ C_err) (hC_J : 0 ≤ C_J) (hC_B : 0 ≤ C_B) (hΦ_meas : AEStronglyMeasurable Φ volume)
    (hΦ_lo : ∀ y : ℝ, y ≠ 0 → |y| ≤ (8 / π) * Real.log (c ^ (1 / 3 : ℝ)) →
      ‖Φ y‖ ≤ ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ * (C_err * (c ^ (-(1 / 3 : ℝ))) ^ 2 * (|y| + |y| ^ 4)))
    (hΦ_hi : ∀ y : ℝ, (8 / π) * Real.log (c ^ (1 / 3 : ℝ)) < |y| →
      ‖Φ y‖ ≤ ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ * (Real.exp (c * hB (|y| / c)) * C_J + C_J + c ^ (-(1 / 3 : ℝ)) * C_B * |y| ^ (1 / 2 : ℝ))) :
    Integrable Φ ∧ ∫ y : ℝ, ‖Φ y‖ ≤
      2 * (2 * C_err + 2 * √(3 * π) * C_err * (24 / (π / 4) ^ 4) * (4 / π) + √(3 * π) * C_J * (4 / π) +
        √(3 * π) * C_J * (1 / 3) * (32 / Real.log 2 ^ 2) + (2 / π) * √(3 * π) * (C_J + C_B)) * c ^ (-(2 / 3 : ℝ)) := by
  have hTnn : 0 ≤ (8 / π) * Real.log (c ^ (1 / 3 : ℝ)) := mul_nonneg (by positivity) (Real.log_nonneg (Real.one_le_rpow (by linarith) (by norm_num)))
  have hpos := pe3_rem_Ioi_bound hc4 hC_err hC_J hC_B hΦ_meas.restrict
    (fun y hy hyT => by simpa [abs_of_pos hy] using hΦ_lo y hy.ne' (by rwa [abs_of_pos hy]))
    (fun y hyT => by have hy0 : 0 < y := lt_of_le_of_lt hTnn hyT; simpa [abs_of_pos hy0] using hΦ_hi y (by rwa [abs_of_pos hy0]))
  have hneg := pe3_rem_Ioi_bound hc4 hC_err hC_J hC_B
    (hΦ_meas.comp_quasiMeasurePreserving (Measure.measurePreserving_neg _).quasiMeasurePreserving).restrict
    (fun y hy hyT => by have h1 := hΦ_lo (-y) (neg_ne_zero.mpr hy.ne') (by simpa [abs_of_pos hy] using hyT); rw [Complex.ofReal_neg, norm_gamma_pure_imag_neg] at h1; simpa [abs_of_pos hy] using h1)
    (fun y hyT => by have hy0 : 0 < y := lt_of_le_of_lt hTnn hyT; have h1 := hΦ_hi (-y) (by simpa [abs_of_pos hy0] using hyT); rw [Complex.ofReal_neg, norm_gamma_pure_imag_neg] at h1; simpa [abs_of_pos hy0] using h1)
  have h_Iio : IntegrableOn Φ (Iio 0) := by simpa [Set.neg_Ioi] using IntegrableOn.comp_neg hneg.1
  have h_Iio_val : ∫ y in Iio (0 : ℝ), ‖Φ y‖ = ∫ y in Ioi (0 : ℝ), ‖Φ (-y)‖ := by
    rw [← integral_Iic_eq_integral_Iio, show (∫ y in Iic (0 : ℝ), ‖Φ y‖) = ∫ y in Iic (0 : ℝ), ‖Φ (-(-y))‖ by simp, integral_comp_neg_Iic 0 (fun y => ‖Φ (-y)‖), neg_zero]
  have h0 : IntegrableOn Φ ({(0 : ℝ)} : Set ℝ) := by rw [IntegrableOn, Measure.restrict_eq_zero.mpr (by simp)]; exact integrable_zero_measure
  refine ⟨by rw [← integrableOn_univ, show (univ : Set ℝ) = Iio 0 ∪ ({0} ∪ Ioi 0) by ext y; simp only [mem_univ, mem_union, mem_Iio, mem_singleton_iff, mem_Ioi, true_iff]; exact lt_trichotomy y 0]; exact h_Iio.union (h0.union hpos.1), ?_⟩
  rw [← setIntegral_univ, ← Iio_union_Ici (a := (0 : ℝ)), setIntegral_union (Iio_disjoint_Ici le_rfl) measurableSet_Ici h_Iio.norm ((integrableOn_Ici_iff_integrableOn_Ioi).mpr hpos.1.norm), integral_Ici_eq_integral_Ioi, h_Iio_val]
  dsimp only [Function.comp] at hneg; linarith [hpos.2, hneg.2]

/-- Abstract origin Mellin representation data for Theorem `PE.3` (`ce_o1_pre_edge.tex`) on `S ⊆ [0, Δ_cap]`. -/
structure PE3OriginData (fhat : ℝ → ℝ → ℝ) (S : Set ℝ) where
  c_min : ℝ
  b_J : ℝ
  (C_ν C_err C_J C_B Δ_cap : ℝ)
  (hc_min : 4 ≤ c_min) (hb_J : 0 < b_J) (hC_ν : 0 ≤ C_ν) (hC_err : 0 ≤ C_err) (hC_J : 0 ≤ C_J) (hC_B : 0 ≤ C_B)
  (hΔ_cap : ∀ Δ ∈ S, 0 ≤ Δ ∧ Δ ≤ Δ_cap)
  (J₀ : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (R_c : ℝ → ℝ → ℂ)
  (hJ₀ : ∀ {c : ℝ}, c_min ≤ c → b_J * c ^ (-(1 / 3 : ℝ)) ≤ J₀ c)
  (hat0 : ∀ {c : ℝ}, c_min ≤ c → (0 : ℝ) ∈ S → fhat c 0 = J₀ c)
  (hg_meas : ∀ {c : ℝ}, c_min ≤ c → AEMeasurable (g c) (volume.restrict (Ioi 0)))
  (hg_nn : ∀ {c : ℝ}, c_min ≤ c → ∀ X ∈ Ioi (0 : ℝ), 0 ≤ g c X)
  (hg_le : ∀ {c : ℝ}, c_min ≤ c → ∀ X ∈ Ioi (0 : ℝ), g c X ≤ C_ν * X ^ (-(3 / 2 : ℝ)))
  (hR_meas : ∀ {c : ℝ}, c_min ≤ c → AEStronglyMeasurable (R_c c) volume)
  (hR_lo : ∀ {c y : ℝ}, c_min ≤ c → y ≠ 0 → |y| ≤ (8 / π) * Real.log (c ^ (1 / 3 : ℝ)) →
    ‖R_c c y‖ ≤ ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ * (C_err * (c ^ (-(1 / 3 : ℝ))) ^ 2 * (|y| + |y| ^ 4)))
  (hR_hi : ∀ {c y : ℝ}, c_min ≤ c → (8 / π) * Real.log (c ^ (1 / 3 : ℝ)) < |y| →
    ‖R_c c y‖ ≤ ‖Complex.Gamma ((y : ℂ) * Complex.I)‖ * (Real.exp (c * hB (|y| / c)) * C_J + C_J + c ^ (-(1 / 3 : ℝ)) * C_B * |y| ^ (1 / 2 : ℝ)))
  h_mellin : ∀ {c Δ : ℝ}, c_min ≤ c → Δ ∈ S → 0 < Δ →
    let ν := volume.withDensity fun X => ENNReal.ofReal (g c X)
    ((fhat c Δ - J₀ c * Real.exp (-4 * Δ) : ℝ) : ℂ) = (1 / (2 * π : ℂ)) * ∫ y : ℝ,
      ((4 : ℂ) ^ (-(Complex.I * (y : ℂ))) * Complex.Gamma (Complex.I * (y : ℂ)) *
        (((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * ∫ X in Ioi (0 : ℝ), (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))) ∂ν) + R_c c y) *
      (Δ : ℂ) ^ (-(Complex.I * (y : ℂ)))

/-- Restrict `PE3OriginData` to a subset `S' ⊆ S`. -/
def PE3OriginData.mono {fhat : ℝ → ℝ → ℝ} {S S' : Set ℝ} (hsub : S' ⊆ S) (d : PE3OriginData fhat S) : PE3OriginData fhat S' :=
  { d with hΔ_cap := fun Δ hΔ => d.hΔ_cap Δ (hsub hΔ), hat0 := fun hc h0 => d.hat0 hc (hsub h0), h_mellin := fun hc hΔ hΔ0 => d.h_mellin hc (hsub hΔ) hΔ0 }

/-- **Non-vacuity witness for `PE3OriginData`.** -/
theorem pe3OriginData_nonvacuous :
    Nonempty (PE3OriginData (fun c Δ => c ^ (-(1 / 3 : ℝ)) * Real.exp (-4 * Δ)) (Icc 0 1)) :=
  ⟨{ c_min := 4, b_J := 1, C_ν := 0, C_err := 0, C_J := 0, C_B := 0, Δ_cap := 1
     hc_min := le_rfl, hb_J := one_pos, hC_ν := le_rfl, hC_err := le_rfl, hC_J := le_rfl, hC_B := le_rfl
     hΔ_cap := fun _ hΔ => hΔ, J₀ := fun c => c ^ (-(1 / 3 : ℝ)), g := fun _ _ => 0, R_c := fun _ _ => 0
     hJ₀ := fun _ => by rw [one_mul], hat0 := fun _ _ => by simp, hg_meas := fun _ => aemeasurable_const
     hg_nn := fun _ _ _ => le_rfl, hg_le := fun _ _ _ => by simp, hR_meas := fun _ => aestronglyMeasurable_const
     hR_lo := fun _ _ _ => by simp, hR_hi := fun _ _ => by simp, h_mellin := fun _ _ _ => by simp [sub_self] }⟩

/-- **Theorem `PE.3` (`ce_o1_pre_edge.tex`) on any bounded subset `S ⊆ [0, Δ_cap]`.** -/
theorem pe3_compact_origin_pos_on {fhat : ℝ → ℝ → ℝ} {S : Set ℝ} (orig : PE3OriginData fhat S) :
    ∃ c₀ ≥ orig.c_min, ∀ c ≥ c₀, ∀ Δ ∈ S, 0 < fhat c Δ := by
  let K_ioi : ℝ := 2 * orig.C_err + 2 * √(3 * π) * orig.C_err * (24 / (π / 4) ^ 4) * (4 / π) +
    √(3 * π) * orig.C_J * (4 / π) + √(3 * π) * orig.C_J * (1 / 3) * (32 / Real.log 2 ^ 2) + (2 / π) * √(3 * π) * (orig.C_J + orig.C_B)
  have hK_ioi : 0 ≤ K_ioi := by have := orig.hC_err; have := orig.hC_J; have := orig.hC_B; positivity
  let floor_c : ℝ := orig.b_J * Real.exp (-4 * max orig.Δ_cap 0); have hfloor_pos : 0 < floor_c := mul_pos orig.hb_J (Real.exp_pos _)
  let K_rem : ℝ := K_ioi / π; have hK_rem : 0 ≤ K_rem := div_nonneg hK_ioi Real.pi_pos.le
  refine ⟨max orig.c_min (max 1 ((K_rem / floor_c + 1) ^ 3)), le_max_left _ _, fun c hc Δ hΔS => ?_⟩
  have hc_min : orig.c_min ≤ c := (le_max_left _ _).trans hc
  have hc4 : 4 ≤ c := orig.hc_min.trans hc_min; have hc_pos : 0 < c := by linarith
  let ε : ℝ := c ^ (-(1 / 3 : ℝ)); have hε_pos : 0 < ε := Real.rpow_pos_of_pos hc_pos _
  have hΔ_bd := orig.hΔ_cap Δ hΔS
  rcases eq_or_lt_of_le hΔ_bd.1 with rfl | hΔ
  · rw [orig.hat0 hc_min hΔS]; exact lt_of_lt_of_le (mul_pos orig.hb_J hε_pos) (orig.hJ₀ hc_min)
  have h_rem_bd := pe3_remainder_integral_bound hc4 orig.hC_err orig.hC_J orig.hC_B
    (orig.hR_meas hc_min) (fun y => orig.hR_lo hc_min) (fun y => orig.hR_hi hc_min)
  let ν := volume.withDensity fun X => ENNReal.ofReal (orig.g c X)
  let G_osc : ℝ → ℂ := fun y => ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) *
    ∫ X in Ioi (0 : ℝ), (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))) ∂ν
  have hG_cont : Continuous G_osc := continuous_const.mul (continuous_osc_setIntegral measurableSet_Ioi subset_rfl
    (pe3a_min_integrableOn orig.hC_ν (orig.hg_meas hc_min) (orig.hg_nn hc_min) (orig.hg_le hc_min)))
  have hG_bd : ∀ y : ℝ, ‖G_osc y‖ ≤ (ε * ((2 * ceCs + 4) * orig.C_ν)) * |y| ^ (1 / 2 : ℝ) := fun y => by
    dsimp [G_osc, ε]
    have hz := pe3a_holder_bound orig.hC_ν (orig.hg_meas hc_min) (orig.hg_nn hc_min) (orig.hg_le hc_min) (z := (y : ℂ) * Complex.I) (by simp)
    rw [show ‖(y : ℂ) * Complex.I‖ = |y| by simp [Complex.norm_real],
      show (fun X : ℝ => 1 - Complex.exp (-(ceCs : ℂ) * ((y : ℂ) * Complex.I) * (X : ℂ))) =
        fun X => 1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ))) by ext X; congr 2; push_cast; ring1] at hz
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hε_pos.le]; exact (mul_le_mul_of_nonneg_left hz hε_pos.le).trans_eq (by ring)
  have h_ref_int := gamma_mul_half_integrable hΔ hG_cont hG_bd
  have h_rem_int : Integrable (fun y : ℝ => orig.R_c c y * (Δ : ℂ) ^ (-(Complex.I * (y : ℂ)))) :=
    h_rem_bd.1.norm.mono' (h_rem_bd.1.aestronglyMeasurable.mul (continuous_ofReal_cpow_neg_I hΔ).aestronglyMeasurable)
      (ae_of_all _ fun y => by rw [norm_mul, norm_ofReal_cpow_neg_I hΔ y, mul_one])
  have hm := orig.h_mellin hc_min hΔS hΔ; dsimp only at hm
  rw [show (fun y : ℝ => ((4 : ℂ) ^ (-(Complex.I * (y : ℂ))) * Complex.Gamma (Complex.I * (y : ℂ)) * G_osc y + orig.R_c c y) * (Δ : ℂ) ^ (-(Complex.I * (y : ℂ)))) =
      (fun y : ℝ => (4 : ℂ) ^ (-(Complex.I * (y : ℂ))) * Complex.Gamma (Complex.I * (y : ℂ)) * G_osc y * (Δ : ℂ) ^ (-(Complex.I * (y : ℂ))) +
        orig.R_c c y * (Δ : ℂ) ^ (-(Complex.I * (y : ℂ)))) by ext y; ring, integral_add h_ref_int h_rem_int, mul_add] at hm
  have h_ref_eval := pe3_measure_inversion orig.hC_ν (orig.hg_meas hc_min) (orig.hg_nn hc_min) (orig.hg_le hc_min) hΔ
  have h_ref_eq : (1 / (2 * π : ℂ)) * ∫ y : ℝ, (4 : ℂ) ^ (-(Complex.I * (y : ℂ))) * Complex.Gamma (Complex.I * (y : ℂ)) * G_osc y * (Δ : ℂ) ^ (-(Complex.I * (y : ℂ))) =
      ((ε * ∫ X in Ioi (0 : ℝ), (Real.exp (-4 * Δ) - Real.exp (-4 * Real.exp (ceCs * X) * Δ)) ∂ν : ℝ) : ℂ) := by
    rw [show (fun y : ℝ => (4 : ℂ) ^ (-(Complex.I * (y : ℂ))) * Complex.Gamma (Complex.I * (y : ℂ)) * G_osc y * (Δ : ℂ) ^ (-(Complex.I * (y : ℂ)))) =
        fun y : ℝ => (ε : ℂ) * ((4 : ℂ) ^ (-(Complex.I * (y : ℂ))) * Complex.Gamma (Complex.I * (y : ℂ)) *
          (∫ X in Ioi (0 : ℝ), (1 - Complex.exp (-(Complex.I * ((ceCs * X : ℝ) : ℂ) * (y : ℂ)))) ∂ν) * (Δ : ℂ) ^ (-(Complex.I * (y : ℂ)))) by ext y; dsimp [G_osc, ε]; ring,
      integral_const_mul, ← mul_assoc, mul_comm (1 / (2 * π : ℂ)) (ε : ℂ), mul_assoc, h_ref_eval.1]; push_cast; rfl
  have hre_diff := congrArg Complex.re hm; rw [Complex.ofReal_re, Complex.add_re, h_ref_eq, Complex.ofReal_re] at hre_diff
  have h_rem_norm : |((1 / (2 * π : ℂ)) * ∫ y : ℝ, orig.R_c c y * (Δ : ℂ) ^ (-(Complex.I * (y : ℂ)))).re| ≤ K_rem * ε ^ 2 := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_div, norm_one, Complex.norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have heps2 : ε ^ 2 = c ^ (-(2 / 3 : ℝ)) := by dsimp [ε]; rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hc_pos.le]; norm_num
    calc (1 / (2 * π)) * ‖∫ y : ℝ, orig.R_c c y * (Δ : ℂ) ^ (-(Complex.I * (y : ℂ)))‖ ≤ (1 / (2 * π)) * ∫ y : ℝ, ‖orig.R_c c y‖ := by
          gcongr; exact (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae (ae_of_all _ fun y => by dsimp only; rw [norm_mul, norm_ofReal_cpow_neg_I hΔ y, mul_one]))
      _ ≤ (1 / (2 * π)) * (2 * K_ioi * ε ^ 2) := by gcongr; rw [heps2]; exact h_rem_bd.2
      _ = K_rem * ε ^ 2 := by dsimp [K_rem]; field_simp [Real.pi_ne_zero]
  have hJ_lb : floor_c * ε ≤ orig.J₀ c * Real.exp (-4 * Δ) :=
    calc floor_c * ε = (orig.b_J * ε) * Real.exp (-4 * max orig.Δ_cap 0) := by dsimp [floor_c]; ring
      _ ≤ orig.J₀ c * Real.exp (-4 * Δ) := mul_le_mul (orig.hJ₀ hc_min) (Real.exp_le_exp.mpr (by linarith [hΔ_bd.2, le_max_left orig.Δ_cap 0]))
          (Real.exp_pos _).le (mul_nonneg orig.hb_J.le (Real.rpow_nonneg hc_pos.le _) |>.trans (orig.hJ₀ hc_min))
  have h_eps_lt : K_rem * ε ^ 2 < floor_c * ε := by
    have h_inv_pos : 0 < K_rem / floor_c + 1 := by positivity
    have hc_cub : (K_rem / floor_c + 1) ^ (3 : ℝ) ≤ c := by rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; exact (le_max_right _ _).trans ((le_max_right _ _).trans hc)
    have hε_le : ε ≤ (K_rem / floor_c + 1)⁻¹ := (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos h_inv_pos 3) hc_cub (by norm_num)).trans_eq
      (by rw [← Real.rpow_mul h_inv_pos.le, show (3 : ℝ) * -(1 / 3 : ℝ) = -1 by norm_num, Real.rpow_neg_one])
    calc K_rem * ε ^ 2 = (K_rem * ε) * ε := by ring
      _ ≤ (K_rem * (K_rem / floor_c + 1)⁻¹) * ε := by gcongr
      _ < floor_c * ε := mul_lt_mul_of_pos_right (by rw [mul_inv_lt_iff₀ h_inv_pos, mul_add, mul_div_cancel₀ _ hfloor_pos.ne']; linarith) hε_pos
  linarith [hre_diff, hJ_lb, h_eps_lt, mul_nonneg hε_pos.le h_ref_eval.2, (abs_le.mp h_rem_norm).1]

/-- **Theorem `PE.3` (`ce_o1_pre_edge.tex`):** uniform compact origin positivity on `[0, Δ₁]`. -/
theorem pe3_compact_origin_pos {fhat : ℝ → ℝ → ℝ} {Δ₁ : ℝ} (orig : PE3OriginData fhat (Icc 0 Δ₁)) :
    ∃ c₀ ≥ orig.c_min, ∀ c ≥ c₀, ∀ Δ ∈ Icc 0 Δ₁, 0 < fhat c Δ := pe3_compact_origin_pos_on orig

/-! ## Section 4: Proposition `cepe:general` (`ce_o1_pre_edge.tex`) shared pre-edge criterion -/

/-- Uniform saddle cutoff exponent `U(M, Λ) ≥ 1`. -/
noncomputable def preEdgeU (M Λ : ℝ) : ℝ :=
  max (max 1 ((min (3 / 1000 : ℝ) ((4 * M) ^ (-(4 / 3 : ℝ)))) ^ (-(4 / 3 : ℝ)))) ((4 * (8 * M + 54 * Λ + 109)) ^ (4 / 3 : ℝ))

/-- Uniform saddle/origin transition `Δ₁(M, Λ, Λ_add, b) ≥ 1`. -/
noncomputable def preEdgeDelta1 (M Λ Λ_add_max b : ℝ) : ℝ :=
  max (max 1 ((min (3 / 1000 : ℝ) ((4 * M) ^ (-(4 / 3 : ℝ)))) ^ (-2 : ℝ))) (max ((4 * (8 * M + 54 * Λ + 109)) ^ 2) (144 * (430 * Λ_add_max / b)))

lemma one_le_preEdgeU (M Λ : ℝ) : 1 ≤ preEdgeU M Λ := (le_max_left _ _).trans (le_max_left _ _)

lemma one_le_preEdgeDelta1 (M Λ Λ_add_max b : ℝ) : 1 ≤ preEdgeDelta1 M Λ Λ_add_max b := (le_max_left _ _).trans (le_max_left _ _)

/-- Hypotheses of Proposition `cepe:general` (`ce_o1_pre_edge.tex`). -/
structure PreEdgeGeneralData (fhat : ℝ → ℝ → ℝ) where
  (W_S W_D : ℝ → ℂ → ℂ) (c_min M Λ Λ_add_max x₀ b : ℝ)
  (hc_min : 0 ≤ c_min) (hM : 1 ≤ M) (hΛ : 1 ≤ Λ) (hΛ_add : 0 ≤ Λ_add_max) (hx₀ : 0 < x₀) (hb : 0 < b)
  (hW_S_diff : ∀ {c : ℝ}, c_min ≤ c → DifferentiableOn ℂ (W_S c) {w : ℂ | 0 < w.re})
  (hW_D_diff : ∀ {c : ℝ}, c_min ≤ c → DifferentiableOn ℂ (W_D c) {w : ℂ | 0 < w.re})
  (hW_S_real : ∀ {c x : ℝ}, c_min ≤ c → 0 < x → (W_S c (x : ℂ)).im = 0)
  (hW_D_real : ∀ {c x : ℝ}, c_min ≤ c → 0 < x → (W_D c (x : ℂ)).im = 0)
  (hW_S_nonneg : ∀ {c x : ℝ}, c_min ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → 0 ≤ (W_S c (x : ℂ)).re)
  (hW_D_nonneg : ∀ {c x : ℝ}, c_min ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → 0 ≤ (W_D c (x : ℂ)).re)
  (hW0_pos : ∀ {c x_pos x_neg : ℝ}, c_min ≤ c → 0 < x_pos → x_pos ≤ c ^ (1 / 3 : ℝ) →
    0 < x_neg → x_neg ≤ c ^ (1 / 3 : ℝ) → 0 < (W_S c (x_pos : ℂ)).re + (W_D c (x_neg : ℂ)).re)
  (hD_floor : ∀ {c x : ℝ}, c_min ≤ c → 0 < x → x < x₀ → b * c ^ (-(1 / 3 : ℝ)) ≤ (W_D c (x : ℂ)).re)
  (hA1_S : ∀ {c x y : ℝ}, c_min ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → |y| ≤ x / 4 →
    ‖W_S c ((x : ℂ) + (y : ℂ) * Complex.I) - W_S c (x : ℂ)‖ ≤ 4 * M * (|y| / x) * (W_S c (x : ℂ)).re)
  (hA1_D : ∀ {c x y : ℝ}, c_min ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → |y| ≤ x / 4 →
    ‖W_D c ((x : ℂ) + (y : ℂ) * Complex.I) - W_D c (x : ℂ)‖ ≤ 4 * M * (|y| / x) * (W_D c (x : ℂ)).re)
  (hA2_S : ∀ {c x y : ℝ}, c_min ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → ‖W_S c ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Λ * (W_S c (x : ℂ)).re)
  (hA2_D : ∀ {c x y : ℝ}, c_min ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) →
    ‖W_D c ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Λ * (W_D c (x : ℂ)).re +
      (if x < x₀ ∧ x / 2 < |y| then Λ_add_max * min (|y| ^ (1 / 2 : ℝ)) 1 else 0))
  (orig : PE3OriginData fhat (Ico 0 (preEdgeDelta1 M Λ Λ_add_max b)))
    h_saddle : ∀ {c Δ ξ σ_star : ℝ}, c_min ≤ c → preEdgeDelta1 M Λ Λ_add_max b ≤ Δ →
      Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * preEdgeU M Λ * c ^ (-(2 / 3 : ℝ)))) →
      ξ = Δ / c → 0 < σ_star → σ_star < 1 → stripGReal σ_star = -Real.log (π ^ 2 * ξ) →
      fhat c Δ = (lobeSaddleIntegral (W_S c) (W_D c) c ξ σ_star).re

/-- Upgrade `PE3OriginData` on `[0, Δ₁]` into `PreEdgeGeneralData`. -/
def PreEdgeGeneralData.ofFull {fhat : ℝ → ℝ → ℝ} {W_S W_D : ℝ → ℂ → ℂ} {c_min M Λ Λ_add_max x₀ b : ℝ}
    (hc_min : 0 ≤ c_min) (hM : 1 ≤ M) (hΛ : 1 ≤ Λ) (hΛ_add : 0 ≤ Λ_add_max) (hx₀ : 0 < x₀) (hb : 0 < b)
    (hW_S_diff : ∀ {c : ℝ}, c_min ≤ c → DifferentiableOn ℂ (W_S c) {w : ℂ | 0 < w.re})
    (hW_D_diff : ∀ {c : ℝ}, c_min ≤ c → DifferentiableOn ℂ (W_D c) {w : ℂ | 0 < w.re})
    (hW_S_real : ∀ {c x : ℝ}, c_min ≤ c → 0 < x → (W_S c (x : ℂ)).im = 0) (hW_D_real : ∀ {c x : ℝ}, c_min ≤ c → 0 < x → (W_D c (x : ℂ)).im = 0)
    (hW_S_nonneg : ∀ {c x : ℝ}, c_min ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → 0 ≤ (W_S c (x : ℂ)).re)
    (hW_D_nonneg : ∀ {c x : ℝ}, c_min ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → 0 ≤ (W_D c (x : ℂ)).re)
    (hW0_pos : ∀ {c x_pos x_neg : ℝ}, c_min ≤ c → 0 < x_pos → x_pos ≤ c ^ (1 / 3 : ℝ) → 0 < x_neg → x_neg ≤ c ^ (1 / 3 : ℝ) → 0 < (W_S c (x_pos : ℂ)).re + (W_D c (x_neg : ℂ)).re)
    (hD_floor : ∀ {c x : ℝ}, c_min ≤ c → 0 < x → x < x₀ → b * c ^ (-(1 / 3 : ℝ)) ≤ (W_D c (x : ℂ)).re)
    (hA1_S : ∀ {c x y : ℝ}, c_min ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → |y| ≤ x / 4 → ‖W_S c ((x : ℂ) + (y : ℂ) * Complex.I) - W_S c (x : ℂ)‖ ≤ 4 * M * (|y| / x) * (W_S c (x : ℂ)).re)
    (hA1_D : ∀ {c x y : ℝ}, c_min ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → |y| ≤ x / 4 → ‖W_D c ((x : ℂ) + (y : ℂ) * Complex.I) - W_D c (x : ℂ)‖ ≤ 4 * M * (|y| / x) * (W_D c (x : ℂ)).re)
    (hA2_S : ∀ {c x y : ℝ}, c_min ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → ‖W_S c ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Λ * (W_S c (x : ℂ)).re)
    (hA2_D : ∀ {c x y : ℝ}, c_min ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) →
      ‖W_D c ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Λ * (W_D c (x : ℂ)).re + (if x < x₀ ∧ x / 2 < |y| then Λ_add_max * min (|y| ^ (1 / 2 : ℝ)) 1 else 0))
    (orig : PE3OriginData fhat (Icc 0 (preEdgeDelta1 M Λ Λ_add_max b)))
    (h_saddle : ∀ {c Δ ξ σ_star : ℝ}, c_min ≤ c → preEdgeDelta1 M Λ Λ_add_max b ≤ Δ →
      Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * preEdgeU M Λ * c ^ (-(2 / 3 : ℝ)))) → ξ = Δ / c → 0 < σ_star → σ_star < 1 → stripGReal σ_star = -Real.log (π ^ 2 * ξ) →
      fhat c Δ = (lobeSaddleIntegral (W_S c) (W_D c) c ξ σ_star).re) : PreEdgeGeneralData fhat :=
  { W_S, W_D, c_min, M, Λ, Λ_add_max, x₀, b, hc_min, hM, hΛ, hΛ_add, hx₀, hb, hW_S_diff, hW_D_diff, hW_S_real, hW_D_real,
    hW_S_nonneg, hW_D_nonneg, hW0_pos, hD_floor, hA1_S, hA1_D, hA2_S, hA2_D, orig := orig.mono Ico_subset_Icc_self, h_saddle }

private noncomputable def PreEdgeGeneralData.toLobeSaddleAmp {fhat : ℝ → ℝ → ℝ}
    (d : PreEdgeGeneralData fhat) {c σ_star : ℝ}
    (hc : max d.c_min ((2 * d.x₀ + 1) ^ 3) ≤ c) (hσ0 : 0 < σ_star) (hσ1 : σ_star < 1) :
    LobeSaddleAmp σ_star (c ^ (1 / 3 : ℝ) * σ_star) (c ^ (1 / 3 : ℝ) * (1 - σ_star)) :=
  have hc_min : d.c_min ≤ c := (le_max_left _ _).trans hc
  have hc_pos : 0 < c := lt_of_lt_of_le (by have := d.hx₀; positivity) ((le_max_right _ _).trans hc)
  have hxpos : 0 < c ^ (1 / 3 : ℝ) * σ_star := mul_pos (Real.rpow_pos_of_pos hc_pos _) hσ0
  have hxpos_le : c ^ (1 / 3 : ℝ) * σ_star ≤ c ^ (1 / 3 : ℝ) := mul_le_of_le_one_right (Real.rpow_nonneg hc_pos.le _) hσ1.le
  let x_neg := c ^ (1 / 3 : ℝ) * (1 - σ_star)
  have hxneg : 0 < x_neg := mul_pos (Real.rpow_pos_of_pos hc_pos _) (sub_pos.mpr hσ1)
  have hxneg_le : x_neg ≤ c ^ (1 / 3 : ℝ) := mul_le_of_le_one_right (Real.rpow_nonneg hc_pos.le _) (by linarith)
  { W_S := d.W_S c, W_D := d.W_D c, M := d.M, Λ := d.Λ
    Λ_add := if x_neg < d.x₀ then d.Λ_add_max else 0, hM := d.hM, hΛ := d.hΛ
    hΛ_add := by split_ifs <;> [exact d.hΛ_add; exact le_rfl]
    hW_S_diff := d.hW_S_diff hc_min, hW_D_diff := d.hW_D_diff hc_min
    hW_S_real := fun _ hx => d.hW_S_real hc_min hx, hW_D_real := fun _ hx => d.hW_D_real hc_min hx
    hW_S_nonneg := d.hW_S_nonneg hc_min hxpos hxpos_le, hW_D_nonneg := d.hW_D_nonneg hc_min hxneg hxneg_le
    hW0_pos := d.hW0_pos hc_min hxpos hxpos_le hxneg hxneg_le
    hA1_S := fun _ hy => d.hA1_S hc_min hxpos hxpos_le hy, hA1_D := fun _ hy => d.hA1_D hc_min hxneg hxneg_le hy
    hA2_S := fun y => d.hA2_S hc_min hxpos hxpos_le (y := y)
    hA2_D := fun y => (d.hA2_D hc_min hxneg hxneg_le (y := y)).trans_eq
      (by dsimp only [x_neg]; congr 1; by_cases h1 : c ^ (3⁻¹ : ℝ) * (1 - σ_star) < d.x₀ <;> simp [h1])
    hΛ_add_half := fun h => by
      have hxn : x_neg < d.x₀ := by by_contra hn; simp [hn] at h
      have hcr : 2 * d.x₀ + 1 ≤ c ^ (1 / 3 : ℝ) := by
        rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
        exact (Real.pow_rpow_inv_natCast (by linarith [d.hx₀]) (by norm_num : 3 ≠ 0)).symm.le.trans
          (Real.rpow_le_rpow (pow_nonneg (by linarith [d.hx₀]) 3) ((le_max_right _ _).trans hc) (by norm_num))
      have h1s : 1 - σ_star < 1 / 2 := by
        rw [show 1 - σ_star = x_neg / c ^ (1 / 3 : ℝ) by dsimp [x_neg]; field_simp [(Real.rpow_pos_of_pos hc_pos (1 / 3 : ℝ)).ne'],
          div_lt_iff₀ (Real.rpow_pos_of_pos hc_pos _)]; linarith
      linarith }

/-- **Proposition `cepe:general` (`ce_o1_pre_edge.tex`):** shared pre-edge Fourier criterion. -/
theorem preEdge_general_pos {fhat : ℝ → ℝ → ℝ} (d : PreEdgeGeneralData fhat) :
    ∃ U ≥ 1, ∃ c₀ ≥ 2, ∀ c ≥ c₀, ∀ Δ ∈ Icc 0 ((c / π ^ 2) * Real.exp (-π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))), 0 < fhat c Δ := by
  let U := preEdgeU d.M d.Λ; let Δ₁ := preEdgeDelta1 d.M d.Λ d.Λ_add_max d.b
  have hU1 : 1 ≤ U := one_le_preEdgeU d.M d.Λ; have hΔ₁ : 1 ≤ Δ₁ := one_le_preEdgeDelta1 d.M d.Λ d.Λ_add_max d.b
  obtain ⟨c_orig, _, hc_orig⟩ := pe3_compact_origin_pos_on d.orig
  let c₀ : ℝ := max (max d.c_min c_orig) (max (max 2 (max (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ)))) ((2 * d.x₀ + 1) ^ 3))
  refine ⟨U, hU1, c₀, (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _)), fun c hc Δ hΔ => ?_⟩
  have hc_min := (le_max_left _ _).trans ((le_max_left _ _).trans hc); have hcorig := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
  have hc2 : 2 ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hc))
  have hc_sad : max (20 * Δ₁) (60 * U ^ (3 / 2 : ℝ)) ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hc))
  have hc_amp : max d.c_min ((2 * d.x₀ + 1) ^ 3) ≤ c := max_le hc_min ((le_max_right _ _).trans ((le_max_right _ _).trans hc))
  have hc_pos : 0 < c := by linarith
  by_cases hlt : Δ < Δ₁
  · exact hc_orig c hcorig Δ ⟨hΔ.1, hlt⟩
  have hΔ_lo : Δ₁ ≤ Δ := not_lt.mp hlt
  have hΔ_hi : Δ ≤ (c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))) := by simpa [neg_mul] using hΔ.2
  let ξ : ℝ := Δ / c; have hξ_pos : 0 < ξ := div_pos (by linarith) hc_pos
  have hpiξ : π ^ 2 * ξ < 1 := (calc π ^ 2 * ξ ≤ π ^ 2 * ((c / π ^ 2) * Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))) / c) := by dsimp [ξ]; gcongr
    _ = Real.exp (-(π ^ 2 * U * c ^ (-(2 / 3 : ℝ)))) := by field_simp [Real.pi_ne_zero, hc_pos.ne']).trans_lt
    (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos (mul_pos (sq_pos_of_pos Real.pi_pos) (by linarith)) (Real.rpow_pos_of_pos hc_pos _))))
  obtain ⟨σ_star, ⟨⟨hσ0, hσ1⟩, hσ_eq⟩, _⟩ := exists_unique_saddleSigma hξ_pos hpiξ
  let amp := d.toLobeSaddleAmp hc_amp hσ0 hσ1
  let ε₀ : ℝ := min (3 / 1000 : ℝ) ((4 * amp.M) ^ (-(4 / 3 : ℝ))); have hε₀_pos : 0 < ε₀ := lt_min (by norm_num) (Real.rpow_pos_of_pos (by linarith [amp.hM]) _)
  have hU_bnd : (27 / 100 : ℝ) * U ^ (-(3 / 4 : ℝ)) ≤ ε₀ := (mul_le_mul (by norm_num : (27 / 100 : ℝ) ≤ 1)
    ((Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hε₀_pos _) (show ε₀ ^ (-(4 / 3 : ℝ)) ≤ U from (le_max_right _ _).trans (le_max_left _ _))
      (by norm_num : -(3 / 4 : ℝ) ≤ 0)).trans_eq (by rw [← Real.rpow_mul hε₀_pos.le, show (-(4 / 3 : ℝ)) * (-(3 / 4 : ℝ)) = 1 by norm_num, Real.rpow_one]))
    (by positivity) zero_le_one).trans_eq (one_mul _)
  have hΔ_bnd : Δ₁ ^ (-(1 / 2 : ℝ)) ≤ ε₀ := (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hε₀_pos _)
    (show ε₀ ^ (-2 : ℝ) ≤ Δ₁ from (le_max_right _ _).trans (le_max_left _ _)) (by norm_num : -(1 / 2 : ℝ) ≤ 0)).trans_eq
    (by rw [← Real.rpow_mul hε₀_pos.le, show (-2 : ℝ) * (-(1 / 2 : ℝ)) = 1 by norm_num, Real.rpow_one])
  have hasymp := lobe_saddle_asymptotic hΔ₁ hU1 hc_sad hΔ_lo hΔ_hi rfl hσ0 hσ1 hσ_eq amp (max_le hU_bnd hΔ_bnd)
  let C_L2 : ℝ := 8 * amp.M + 54 * amp.Λ + 109; have hC_L2 : 0 < C_L2 := by linarith [amp.hM, amp.hΛ]
  have hU_L2 : (27 / 100 : ℝ) * U ^ (-(3 / 4 : ℝ)) ≤ (4 * C_L2)⁻¹ := (mul_le_mul (by norm_num : (27 / 100 : ℝ) ≤ 1)
    ((Real.rpow_le_rpow_of_nonpos (by positivity) (show (4 * C_L2) ^ (4 / 3 : ℝ) ≤ U from le_max_right _ _) (by norm_num : -(3 / 4 : ℝ) ≤ 0)).trans_eq
      (by rw [← Real.rpow_mul (by positivity), show (4 / 3 : ℝ) * (-(3 / 4 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]))
    (by positivity) zero_le_one).trans_eq (one_mul _)
  have hΔ_L2 : Δ₁ ^ (-(1 / 2 : ℝ)) ≤ (4 * C_L2)⁻¹ := (Real.rpow_le_rpow_of_nonpos (by positivity)
    (show (4 * C_L2) ^ 2 ≤ Δ₁ from (le_max_left _ _).trans (le_max_right _ _)) (by norm_num : -(1 / 2 : ℝ) ≤ 0)).trans_eq
    (by rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), show ((2 : ℕ) : ℝ) * -(1 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one])
  have h_mul_err : C_L2 * saddleEpsL c σ_star ≤ 1 / 4 := (mul_le_mul_of_nonneg_left
    ((saddleEpsL_bounds hΔ₁ hU1 hc_sad hΔ_lo hΔ_hi rfl hσ0 hσ1 hσ_eq).2.2.trans_le (max_le hU_L2 hΔ_L2)).le hC_L2.le).trans_eq (by field_simp [hC_L2.ne'])
  have h_add_err : 430 * amp.Λ_add * (c ^ (-(1 / 3 : ℝ)) /
      ((amp.W_S ((c ^ (1 / 3 : ℝ) * σ_star : ℝ) : ℂ)).re + (amp.W_D ((c ^ (1 / 3 : ℝ) * (1 - σ_star) : ℝ) : ℂ)).re)) *
      Real.exp (-(3 / 320 : ℝ) * (c * (1 - σ_star))) ≤ 1 / 4 := by
    let x_neg := c ^ (1 / 3 : ℝ) * (1 - σ_star)
    by_cases hxn : x_neg < d.x₀
    · have hfl := d.hD_floor hc_min (mul_pos (Real.rpow_pos_of_pos hc_pos _) (sub_pos.mpr hσ1)) hxn
      have hsnn := d.hW_S_nonneg hc_min (mul_pos (Real.rpow_pos_of_pos hc_pos _) hσ0) (mul_le_of_le_one_right (Real.rpow_nonneg hc_pos.le _) hσ1.le)
      have hW0_ge : d.b * c ^ (-(1 / 3 : ℝ)) ≤ (amp.W_S ((c ^ (1 / 3 : ℝ) * σ_star : ℝ) : ℂ)).re + (amp.W_D (x_neg : ℂ)).re := by dsimp [amp, PreEdgeGeneralData.toLobeSaddleAmp] at *; linarith
      have hrat : c ^ (-(1 / 3 : ℝ)) / ((amp.W_S ((c ^ (1 / 3 : ℝ) * σ_star : ℝ) : ℂ)).re + (amp.W_D (x_neg : ℂ)).re) ≤ d.b⁻¹ := by
        rw [div_le_iff₀ amp.hW0_pos]; exact (mul_le_mul_of_nonneg_left hW0_ge (inv_nonneg.mpr d.hb.le)).trans_eq' (by field_simp [d.hb.ne'])
      have hz_gt := (saddle_endpoint_scales hΔ₁ hU1 hc_sad hΔ_lo hΔ_hi rfl hσ0 hσ1 hσ_eq).2.2
      have hexp_le : Real.exp (-(3 / 320 : ℝ) * (c * (1 - σ_star))) ≤ (3 * π / 320 * Δ₁)⁻¹ := by
        rw [← one_div, le_one_div (Real.exp_pos _) (by positivity), neg_mul, Real.exp_neg, div_inv_eq_mul, one_mul]
        linarith [Real.add_one_le_exp (3 * π / 320 * Δ₁), Real.exp_le_exp.mpr (by linarith [hz_gt] : 3 * π / 320 * Δ₁ ≤ (3 / 320 : ℝ) * (c * (1 - σ_star)))]
      calc 430 * amp.Λ_add * (c ^ (-(1 / 3 : ℝ)) / ((amp.W_S ((c ^ (1 / 3 : ℝ) * σ_star : ℝ) : ℂ)).re + (amp.W_D (x_neg : ℂ)).re)) * Real.exp (-(3 / 320 : ℝ) * (c * (1 - σ_star)))
          ≤ 430 * d.Λ_add_max * d.b⁻¹ * (3 * π / 320 * Δ₁)⁻¹ := by
            dsimp [amp, PreEdgeGeneralData.toLobeSaddleAmp]; dsimp [x_neg] at hxn; simp only [hxn, ↓reduceIte]
            exact mul_le_mul (mul_le_mul_of_nonneg_left hrat (by have := d.hΛ_add; positivity)) hexp_le (Real.exp_pos _).le (by have := d.hΛ_add; have := d.hb; positivity)
        _ ≤ 1 / 4 := by
            rw [mul_inv, show 430 * d.Λ_add_max * d.b⁻¹ * ((3 * π / 320)⁻¹ * Δ₁⁻¹) = ((430 * d.Λ_add_max / d.b) * (320 / (3 * π))) * Δ₁⁻¹ by ring, mul_inv_le_iff₀ (by positivity)]
            have hpi3 : (320 : ℝ) / (3 * π) ≤ 36 := by rw [div_le_iff₀ (by positivity)]; linarith [Real.pi_gt_three]
            calc (430 * d.Λ_add_max / d.b) * (320 / (3 * π)) ≤ (430 * d.Λ_add_max / d.b) * 36 := mul_le_mul_of_nonneg_left hpi3 (by have := d.hΛ_add; have := d.hb; positivity)
              _ = (1 / 4) * (144 * (430 * d.Λ_add_max / d.b)) := by ring
              _ ≤ (1 / 4) * Δ₁ := by gcongr; exact (le_max_right _ _).trans (le_max_right _ _)
    · dsimp [amp, PreEdgeGeneralData.toLobeSaddleAmp]; dsimp [x_neg] at hxn; simp only [hxn, ↓reduceIte, mul_zero, zero_mul]; norm_num
  dsimp only at hasymp; dsimp [C_L2] at h_mul_err
  let K₀ := (mellinK0 c (σ_star : ℂ) ξ).re; let W₀ := (amp.W_S ((c ^ (1 / 3 : ℝ) * σ_star : ℝ) : ℂ)).re + (amp.W_D ((c ^ (1 / 3 : ℝ) * (1 - σ_star) : ℝ) : ℂ)).re
  let L_lead := (1 / (2 * π * ξ)) * K₀ * W₀ * Real.sqrt (2 * π / (c * stripGDerivReal σ_star))
  have hL_pos : 0 < L_lead := mul_pos (mul_pos (mul_pos (by positivity) hasymp.2.1) amp.hW0_pos) (Real.sqrt_pos.mpr (div_pos (by positivity) (mul_pos hc_pos (stripGDerivReal_pos hσ0 hσ1))))
  have h1 := (abs_le.mp (hasymp.2.2.2.trans ((add_le_add h_mul_err h_add_err).trans (by norm_num : (1 / 4 : ℝ) + 1 / 4 ≤ 1 / 2)))).1
  rw [le_div_iff₀ hL_pos] at h1
  have hI_pos : 0 < (lobeSaddleIntegral amp.W_S amp.W_D c ξ σ_star).re := by linarith [h1, hL_pos]
  rw [d.h_saddle hc_min hΔ_lo hΔ_hi rfl hσ0 hσ1 hσ_eq]; exact hI_pos

/-- **Non-vacuity witness for `PreEdgeGeneralData`.** -/
theorem preEdgeGeneralData_nonvacuous : ∃ fhat : ℝ → ℝ → ℝ, Nonempty (PreEdgeGeneralData fhat) := by
  let Δ_cut := preEdgeDelta1 1 1 0 (1 / 2); let W_S : ℝ → ℂ → ℂ := fun _ _ => 0
  let W_D : ℝ → ℂ → ℂ := fun c w => ((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * (1 + w)⁻¹
  let fhat : ℝ → ℝ → ℝ := fun c Δ => if Δ < Δ_cut then c ^ (-(1 / 3 : ℝ)) * Real.exp (-4 * Δ)
    else if hξ : 0 < Δ / c ∧ π ^ 2 * (Δ / c) < 1 then
      (lobeSaddleIntegral (W_S c) (W_D c) c (Δ / c) (Classical.choose (exists_unique_saddleSigma hξ.1 hξ.2).exists)).re else 0
  have hinv_re : ∀ x : ℝ, (1 + (x : ℂ))⁻¹ = (((1 + x)⁻¹ : ℝ) : ℂ) := fun x => by push_cast; rfl
  refine ⟨fhat, ⟨{
    W_S, W_D, c_min := 4, M := 1, Λ := 1, Λ_add_max := 0, x₀ := 1, b := 1 / 2
    hc_min := by norm_num, hM := le_rfl, hΛ := le_rfl, hΛ_add := le_rfl, hx₀ := one_pos, hb := by norm_num
    hW_S_diff := fun _ => differentiableOn_const 0
    hW_D_diff := fun _ w hw => (differentiableAt_const _ |>.mul ((differentiableAt_id.const_add 1).inv fun h => by
      have := congrArg Complex.re h; simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this; linarith [show 0 < w.re from hw])).differentiableWithinAt
    hW_S_real := fun _ _ => rfl, hW_D_real := fun {c x} _ _ => by dsimp [W_D]; rw [hinv_re, ← Complex.ofReal_mul, Complex.ofReal_im]
    hW_S_nonneg := fun _ _ _ => by simp [W_S]
    hW_D_nonneg := fun {c x} hc hx _ => by dsimp [W_D]; rw [hinv_re, ← Complex.ofReal_mul, Complex.ofReal_re]; exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (inv_nonneg.mpr (by linarith))
    hW0_pos := fun {c _ x_neg} hc _ _ hxneg _ => by dsimp [W_S, W_D]; rw [zero_add, hinv_re, ← Complex.ofReal_mul, Complex.ofReal_re]; exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) (inv_pos.mpr (by linarith))
    hD_floor := fun {c x} hc hx0 hx1 => by dsimp [W_D]; rw [hinv_re, ← Complex.ofReal_mul, Complex.ofReal_re, mul_comm (1 / 2 : ℝ), ← one_div]; exact mul_le_mul_of_nonneg_left ((le_div_iff₀ (by linarith : 0 < 1 + x)).mpr (by linarith)) (Real.rpow_nonneg (by linarith) _)
    hA1_S := fun _ _ _ _ => by simp [W_S]
    hA1_D := fun {c x y} hc hx _ _ => by
      have hε : 0 ≤ c ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg (by linarith) _
      have hne1 : 1 + ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
      have hne2 : 1 + (x : ℂ) ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
      dsimp [W_D]; rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hε,
        show (1 + ((x : ℂ) + (y : ℂ) * Complex.I))⁻¹ - (1 + (x : ℂ))⁻¹ = -((y : ℂ) * Complex.I) / ((1 + ((x : ℂ) + (y : ℂ) * Complex.I)) * (1 + (x : ℂ))) by field_simp [hne1, hne2]; ring,
        norm_div, norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
        show ‖1 + (x : ℂ)‖ = 1 + x by rw [show 1 + (x : ℂ) = ((1 + x : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_of_nonneg (by linarith)],
        show (((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * (1 + (x : ℂ))⁻¹).re = c ^ (-(1 / 3 : ℝ)) * (1 + x)⁻¹ by rw [hinv_re, ← Complex.ofReal_mul, Complex.ofReal_re]]
      have h_re : 1 + x ≤ ‖1 + ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by simpa using Complex.re_le_norm (1 + ((x : ℂ) + (y : ℂ) * Complex.I))
      calc c ^ (-(1 / 3 : ℝ)) * (|y| / (‖1 + ((x : ℂ) + (y : ℂ) * Complex.I)‖ * (1 + x))) ≤ c ^ (-(1 / 3 : ℝ)) * (|y| / (x * (1 + x))) := by gcongr; linarith
        _ = (|y| / x) * (c ^ (-(1 / 3 : ℝ)) * (1 + x)⁻¹) := by field_simp [hx.ne', (by linarith : 1 + x ≠ 0)]
        _ ≤ 4 * 1 * (|y| / x) * (c ^ (-(1 / 3 : ℝ)) * (1 + x)⁻¹) := by nlinarith [div_nonneg (abs_nonneg y) hx.le, mul_nonneg hε (inv_nonneg.mpr (by linarith : 0 ≤ 1 + x))]
    hA2_S := fun _ _ _ => by simp [W_S]
    hA2_D := fun {c x y} hc hx _ => by
      have hε : 0 ≤ c ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg (by linarith) _
      dsimp [W_D]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hε, norm_inv,
        show (((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) * (1 + (x : ℂ))⁻¹).re = c ^ (-(1 / 3 : ℝ)) * (1 + x)⁻¹ by rw [hinv_re, ← Complex.ofReal_mul, Complex.ofReal_re], one_mul]
      exact (mul_le_mul_of_nonneg_left (inv_anti₀ (by linarith : 0 < 1 + x) (by simpa using Complex.re_le_norm (1 + ((x : ℂ) + (y : ℂ) * Complex.I)))) hε).trans (by split_ifs <;> simp)
    orig :=
      { c_min := 4, b_J := 1, C_ν := 0, C_err := 0, C_J := 0, C_B := 0, Δ_cap := Δ_cut
        hc_min := le_rfl, hb_J := one_pos, hC_ν := le_rfl, hC_err := le_rfl, hC_J := le_rfl, hC_B := le_rfl
        hΔ_cap := fun _ hΔ => ⟨hΔ.1, hΔ.2.le⟩, J₀ := fun c => c ^ (-(1 / 3 : ℝ)), g := fun _ _ => 0, R_c := fun _ _ => 0
        hJ₀ := fun _ => by rw [one_mul],
        hat0 := fun _ h0 => by dsimp [fhat, Δ_cut]; simp only [h0.2, ↓reduceIte, mul_zero, Real.exp_zero, mul_one]
        hg_meas := fun _ => aemeasurable_const, hg_nn := fun _ _ _ => le_rfl, hg_le := fun _ _ _ => by simp
        hR_meas := fun _ => aestronglyMeasurable_const, hR_lo := fun _ _ _ => by simp, hR_hi := fun _ _ => by simp
        h_mellin := fun {c Δ} _ hΔ _ => by dsimp [fhat, Δ_cut]; simp only [hΔ.2, ↓reduceIte]; simp [sub_self] }
    h_saddle := fun {c Δ ξ σ_star} hc hΔ_lo hΔ_hi hξ hσ0 hσ1 hσ_eq => by
      subst hξ
      have hc_pos : 0 < c := by linarith
      have hU1 : 1 ≤ preEdgeU 1 1 := one_le_preEdgeU 1 1
      have hξ_pos : 0 < Δ / c := div_pos ((one_le_preEdgeDelta1 1 1 0 (1 / 2)).trans hΔ_lo |>.trans_lt' zero_lt_one) hc_pos
      have hpiξ : π ^ 2 * (Δ / c) < 1 :=
        (calc π ^ 2 * (Δ / c) ≤ π ^ 2 * ((c / π ^ 2) * Real.exp (-(π ^ 2 * preEdgeU 1 1 * c ^ (-(2 / 3 : ℝ)))) / c) := by gcongr
          _ = Real.exp (-(π ^ 2 * preEdgeU 1 1 * c ^ (-(2 / 3 : ℝ)))) := by field_simp [Real.pi_ne_zero, hc_pos.ne']).trans_lt
          (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos (mul_pos (sq_pos_of_pos Real.pi_pos) (by linarith [hU1])) (Real.rpow_pos_of_pos hc_pos _))))
      have hσ_uniq := (exists_unique_saddleSigma hξ_pos hpiξ).unique ⟨⟨hσ0, hσ1⟩, hσ_eq⟩
        (Classical.choose_spec (exists_unique_saddleSigma hξ_pos hpiξ).exists)
      dsimp [fhat, Δ_cut]; simp only [not_lt.mpr hΔ_lo, ↓reduceIte, hξ_pos, hpiξ, and_self, ↓reduceDIte, hσ_uniq] }⟩⟩

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.CohnElkies.twoScaleS_gt2bData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.twoScaleS_gt2bData
/-- info: 'FormalResearch.CohnElkies.twoScaleS_gt2b_reflected_mult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.twoScaleS_gt2b_reflected_mult
/-- info: 'FormalResearch.CohnElkies.twoScaleS_gt2b_dual_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.twoScaleS_gt2b_dual_integral
/-- info: 'FormalResearch.CohnElkies.twoScale_mellin_origin_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.twoScale_mellin_origin_unconditional
/-- info: 'FormalResearch.CohnElkies.twoScale_mellin_origin_of_farTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.twoScale_mellin_origin_of_farTail
/-- info: 'FormalResearch.CohnElkies.twoScaleFc_at_a1_asymptotic_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.twoScaleFc_at_a1_asymptotic_unconditional
/-- info: 'FormalResearch.CohnElkies.twoScaleFc_at_a1_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.twoScaleFc_at_a1_neg
/-- info: 'FormalResearch.CohnElkies.pe3_reference_mellin_inversion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.pe3_reference_mellin_inversion
/-- info: 'FormalResearch.CohnElkies.pe3_measure_inversion_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.pe3_measure_inversion_of_bounds
/-- info: 'FormalResearch.CohnElkies.pe3_measure_inversion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.pe3_measure_inversion
/-- info: 'FormalResearch.CohnElkies.pe3_remainder_integral_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.pe3_remainder_integral_bound
/-- info: 'FormalResearch.CohnElkies.pe3OriginData_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.pe3OriginData_nonvacuous
/-- info: 'FormalResearch.CohnElkies.pe3_compact_origin_pos_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.pe3_compact_origin_pos_on
/-- info: 'FormalResearch.CohnElkies.pe3_compact_origin_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.pe3_compact_origin_pos
/-- info: 'FormalResearch.CohnElkies.preEdge_general_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.preEdge_general_pos
/-- info: 'FormalResearch.CohnElkies.preEdgeGeneralData_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.preEdgeGeneralData_nonvacuous

end FormalResearch.CohnElkies
