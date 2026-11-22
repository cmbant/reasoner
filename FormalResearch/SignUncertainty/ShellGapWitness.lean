module

public import FormalResearch.SignUncertainty.ShellGap

/-!
# Explicit Airy Non-Vacuity Witnesses for `ShellGapPackage` and `ShellReductionPackage`

Constructs `airyLaplace_airy_normG_bdd`, `shellGapPackage_nonvacuous`, and
`shellReductionPackage_nonvacuous` on `ShellHBData.airy` (`m = 1`, `u_ustar = D.tm`) and
`c k = k + 1000`, using scalar Mellin surrogates `Mtilde_*`/`E_strip` built from
`airyLaplace (-D.normG)` and `h0 k = (2B + 1) M[2 q_k]`. (Since `m = 1` has
`0 < shellLaplaceF D y`, this witness checks consistency of the package fields rather than
triggering the `∃ y > 0, airyLaplace (-D.G) y < 0` strict-gap branch.)
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal Polynomial

namespace FormalResearch.SignUncertainty

open FormalResearch.Special
open FormalResearch.Analysis
open FormalResearch.Montel

/-- Uniform `O(1)` upper bound on `airyLaplace (-ShellHBData.airy.normG) y` for all `y ≥ 0`
(from `abs_airyAi_le_real` and the elementary saddle factor `y u - y³/12 - 4/3 u^{3/2} ≤ 0`). -/
lemma airyLaplace_airy_normG_bdd :
    ∃ B : ℝ, 0 < B ∧ ∀ y : ℝ, 0 ≤ y → airyLaplace (fun u => -ShellHBData.airy.normG u) y ≤ B := by
  let D := ShellHBData.airy
  let N₁ := ∫ x : ℝ, ‖D.G (x : ℂ)‖
  have hN₁ : 0 < N₁ := D.G_l1_pos
  have hG_bound_Ioi : ∀ u : ℝ, 0 ≤ u →
      -(D.G (u : ℂ)).re ≤ 16 * (2 + u) ^ (-(3 / 2 : ℝ)) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by
    intro u hu
    have hprod := D.G_prod_eq (u : ℂ)
    change D.G (u : ℂ) * at47_pr D.S (u : ℂ) =
      (((-1 : ℝ) ^ D.S.card : ℝ) : ℂ) * airyPQN D.P D.Q (u : ℂ) ^ 2 at hprod
    have hS : D.S = {airyZero 1} := rfl
    have hden : at47_pr D.S (u : ℂ) = ((u - airyZero 1 : ℝ) : ℂ) := by
      rw [hS]; unfold at47_pr; rw [Finset.prod_singleton]; push_cast; rfl
    have ha₁ : airyZero 1 < -2.33 := airyZero_one.2
    have hux_pos : 0 < u - airyZero 1 := by linarith
    have hN_eq : airyPQN D.P D.Q (u : ℂ) = airyAiC (u : ℂ) := by
      change airyPQN (Polynomial.C 1) 0 (u : ℂ) = airyAiC (u : ℂ)
      unfold airyPQN; rw [airyPQc_C, airyPQc_zero]; push_cast; ring
    rw [hden, hN_eq] at hprod
    have hSc : D.S.card = 1 := Finset.card_singleton _
    rw [hSc, pow_one] at hprod
    have hnorm : |(D.G (u : ℂ)).re| * (u - airyZero 1) = |airyAi u| ^ 2 := by
      have hc : D.G (u : ℂ) = ((D.G (u : ℂ)).re : ℂ) := Complex.ext rfl (D.G_real u)
      have h1 := congrArg norm hprod
      rw [hc, norm_mul, norm_mul] at h1
      simp_rw [Complex.norm_real, Real.norm_eq_abs] at h1
      rw [abs_of_pos hux_pos, norm_pow, norm_airyAiC_ofReal, abs_neg, abs_one, one_mul] at h1
      exact h1
    have hle_neg : -(D.G (u : ℂ)).re ≤ |(D.G (u : ℂ)).re| := neg_le_abs _
    have hai := abs_airyAi_le_real (by linarith : (-1 : ℝ) ≤ u)
    have hxi : airyXi u = (2 / 3 : ℝ) * u ^ (3 / 2 : ℝ) := by
      unfold airyXi; rw [max_eq_left hu]
    rw [hxi] at hai
    have hsq1 : ((2 + u) ^ (-(1 / 4 : ℝ))) ^ (2 : ℕ) = (2 + u) ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      congr 1; norm_num
    have hsq2 : (Real.exp (-((2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)))) ^ (2 : ℕ) =
        Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hsq : |airyAi u| ^ 2 ≤ 16 * (2 + u) ^ (-(1 / 2 : ℝ)) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by
      calc |airyAi u| ^ 2 ≤ (4 * (2 + u) ^ (-(1 / 4 : ℝ)) * Real.exp (-((2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)))) ^ 2 := by
            gcongr
        _ = 16 * ((2 + u) ^ (-(1 / 4 : ℝ))) ^ (2 : ℕ) *
              (Real.exp (-((2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)))) ^ (2 : ℕ) := by ring
        _ = 16 * (2 + u) ^ (-(1 / 2 : ℝ)) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by
            rw [hsq1, hsq2]
    have h2u_le : 2 + u ≤ u - airyZero 1 := by linarith
    have h2u_pos : 0 < 2 + u := by linarith
    have hrpow_div : (2 + u) ^ (-(1 / 2 : ℝ)) / (2 + u) = (2 + u) ^ (-(3 / 2 : ℝ)) := by
      rw [div_eq_mul_inv]
      conv_lhs => rhs; rw [← Real.rpow_one (2 + u)]
      rw [← Real.rpow_neg h2u_pos.le, ← Real.rpow_add h2u_pos]
      congr 1; norm_num
    calc -(D.G (u : ℂ)).re ≤ |(D.G (u : ℂ)).re| := hle_neg
      _ = |airyAi u| ^ 2 / (u - airyZero 1) := by rw [← hnorm, mul_div_cancel_right₀ _ hux_pos.ne']
      _ ≤ |airyAi u| ^ 2 / (2 + u) := div_le_div_of_nonneg_left (sq_nonneg _) h2u_pos h2u_le
      _ ≤ (16 * (2 + u) ^ (-(1 / 2 : ℝ)) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ))) / (2 + u) :=
          div_le_div_of_nonneg_right hsq h2u_pos.le
      _ = 16 * ((2 + u) ^ (-(1 / 2 : ℝ)) / (2 + u)) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by ring
      _ = 16 * (2 + u) ^ (-(3 / 2 : ℝ)) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by rw [hrpow_div]
  let C_small : ℝ := ∫ u in Ioi (0 : ℝ), 16 * (2 + u) ^ (-(3 / 2 : ℝ)) *
    Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ) + 2 * u)
  have hIic_bd : ∀ y : ℝ, 0 ≤ y → ∫ u in Iic (0 : ℝ), -(D.G (u : ℂ)).re * Real.exp (y * u) ≤ N₁ := by
    intro y hy
    have hi := (D.G_inAiryClass.integrable_exp_nonneg hy).neg
    have hi' : IntegrableOn (fun (u : ℝ) => -(D.G (u : ℂ)).re * Real.exp (y * u)) (Iic 0) :=
      hi.integrableOn.congr (Eventually.of_forall fun u => by simp [neg_mul])
    have hle : ∫ u in Iic (0 : ℝ), -(D.G (u : ℂ)).re * Real.exp (y * u) ≤ ∫ u in Iic (0 : ℝ), ‖D.G (u : ℂ)‖ := by
      refine setIntegral_mono_on hi' D.G_int.norm.integrableOn measurableSet_Iic fun u hu => ?_
      have hc : D.G (u : ℂ) = ((D.G (u : ℂ)).re : ℂ) := Complex.ext rfl (D.G_real u)
      have hnr : ‖D.G (u : ℂ)‖ = |(D.G (u : ℂ)).re| := by
        conv_lhs => rw [hc, Complex.norm_real, Real.norm_eq_abs]
      rw [hnr]
      calc -(D.G (u : ℂ)).re * Real.exp (y * u) ≤ |(D.G (u : ℂ)).re| * Real.exp (y * u) :=
            mul_le_mul_of_nonneg_right (neg_le_abs _) (Real.exp_pos _).le
        _ ≤ |(D.G (u : ℂ)).re| * 1 :=
            mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hy hu))
              (abs_nonneg _)
        _ = |(D.G (u : ℂ)).re| := mul_one _
    exact hle.trans (setIntegral_le_integral D.G_int.norm (Eventually.of_forall fun _ => norm_nonneg _))
  refine ⟨(N₁ + (max C_small 1600 + 1)) / N₁, by positivity, fun y hy => ?_⟩
  have hnorm_eq : airyLaplace (fun u => -D.normG u) y =
      (Real.exp (-(y ^ 3) / 12) * ∫ u : ℝ, -(D.G (u : ℂ)).re * Real.exp (y * u)) / N₁ := by
    change Real.exp (-(y ^ 3) / 12) * ∫ u : ℝ, -((D.G (u : ℂ)).re / N₁) * Real.exp (y * u) = _
    have heq : (fun (u : ℝ) => -((D.G (u : ℂ)).re / N₁) * Real.exp (y * u)) =
        fun (u : ℝ) => (-(D.G (u : ℂ)).re * Real.exp (y * u)) / N₁ := by ext u; ring
    rw [heq, integral_div]; ring
  rw [hnorm_eq]
  have hint_full : Integrable (fun u : ℝ => -(D.G (u : ℂ)).re * Real.exp (y * u)) := by
    simpa [neg_mul] using (D.G_inAiryClass.integrable_exp_nonneg hy).neg
  have hsp := integral_add_compl (measurableSet_Iic (a := (0 : ℝ))) hint_full
  rw [compl_Iic] at hsp
  have hleft := hIic_bd y hy
  have hexp_le1 : Real.exp (-(y ^ 3) / 12) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (pow_nonneg hy 3)) (by norm_num))
  have hsplit_bnd : Real.exp (-(y ^ 3) / 12) * ∫ u : ℝ, -(D.G (u : ℂ)).re * Real.exp (y * u) ≤
      N₁ + Real.exp (-(y ^ 3) / 12) * ∫ u in Ioi (0 : ℝ), -(D.G (u : ℂ)).re * Real.exp (y * u) := by
    rw [← hsp, mul_add]
    have h1 : Real.exp (-(y ^ 3) / 12) * ∫ u in Iic (0 : ℝ), -(D.G (u : ℂ)).re * Real.exp (y * u) ≤ N₁ := by
      rcases le_total 0 (∫ u in Iic (0 : ℝ), -(D.G (u : ℂ)).re * Real.exp (y * u)) with h0 | h0
      · exact (mul_le_of_le_one_left h0 hexp_le1).trans hleft
      · exact (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le h0).trans hN₁.le
    linarith
  suffices hIoi_bnd : Real.exp (-(y ^ 3) / 12) * ∫ u in Ioi (0 : ℝ), -(D.G (u : ℂ)).re * Real.exp (y * u) ≤
      max C_small 1600 + 1 by
    exact div_le_div_of_nonneg_right (by linarith [hsplit_bnd, hIoi_bnd]) hN₁.le
  by_cases hy2 : y ≤ 2
  · have hRHS_int : IntegrableOn (fun u : ℝ => 16 * (2 + u) ^ (-(3 / 2 : ℝ)) *
        Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ) + 2 * u)) (Ioi 0) := by
      have hi := integrableOn_airy_exp_Ioi (ν := (0 : ℝ)) (b := 2) (by norm_num : (0 : ℝ) ≤ 16)
      refine hi.mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : 0 < u) => ?_)
      · refine ((continuousOn_const.mul ((continuousOn_const.add continuousOn_id).rpow_const
          fun u hu => Or.inl (by linarith [mem_Ioi.mp hu] : 0 < 2 + u).ne')).mul
            (((continuousOn_const.mul (continuousOn_id.rpow_const fun _ _ =>
              Or.inr (by norm_num : (0 : ℝ) ≤ 3 / 2))).add
              (continuousOn_const.mul continuousOn_id)).rexp)).aestronglyMeasurable measurableSet_Ioi
      · have hp : (2 + u) ^ (-(3 / 2 : ℝ)) ≤ 1 := by
          rw [Real.rpow_neg (by linarith)]
          exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by linarith) (by norm_num))
        have hpos_lhs : 0 ≤ 16 * (2 + u) ^ (-(3 / 2 : ℝ)) *
            Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ) + 2 * u) := by positivity
        rw [Real.norm_of_nonneg hpos_lhs, at47_env_ofReal_nonneg hu.le]
        rw [Real.rpow_zero, mul_one, Real.exp_add]
        calc 16 * (2 + u) ^ (-(3 / 2 : ℝ)) * (Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (2 * u))
            ≤ 16 * 1 * (Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (2 * u)) := by gcongr
          _ = 16 * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (2 * u) := by ring
    have hIoi_le : ∫ u in Ioi (0 : ℝ), -(D.G (u : ℂ)).re * Real.exp (y * u) ≤ C_small := by
      refine setIntegral_mono_on hint_full.integrableOn hRHS_int measurableSet_Ioi fun u (hu : 0 < u) => ?_
      have h1 := mul_le_mul_of_nonneg_right (hG_bound_Ioi u hu.le) (Real.exp_pos (y * u)).le
      have h2 : Real.exp (y * u) ≤ Real.exp (2 * u) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hy2 hu.le)
      calc -(D.G (u : ℂ)).re * Real.exp (y * u)
          ≤ 16 * (2 + u) ^ (-(3 / 2 : ℝ)) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (y * u) := h1
        _ ≤ 16 * (2 + u) ^ (-(3 / 2 : ℝ)) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (2 * u) := by
            gcongr
        _ = 16 * (2 + u) ^ (-(3 / 2 : ℝ)) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ) + 2 * u) := by
            rw [mul_assoc, ← Real.exp_add]
    have hC0 : 0 ≤ C_small := setIntegral_nonneg measurableSet_Ioi fun u hu => by
      have hu0 : 0 ≤ u := (mem_Ioi.mp hu).le; positivity
    calc Real.exp (-(y ^ 3) / 12) * ∫ u in Ioi (0 : ℝ), -(D.G (u : ℂ)).re * Real.exp (y * u)
        ≤ Real.exp (-(y ^ 3) / 12) * C_small := mul_le_mul_of_nonneg_left hIoi_le (Real.exp_pos _).le
      _ ≤ 1 * C_small := mul_le_mul_of_nonneg_right hexp_le1 hC0
      _ ≤ max C_small 1600 + 1 := by linarith [le_max_left C_small 1600]
  · push Not at hy2
    have hpt_Ioi : ∀ u : ℝ, 0 < u → Real.exp (-(y ^ 3) / 12) * (-(D.G (u : ℂ)).re * Real.exp (y * u)) ≤
        16 * (2 + u) ^ (-(3 / 2 : ℝ)) * Real.exp (-(y ^ 3) / 12 + y * u - (4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by
      intro u hu
      have h1 := mul_le_mul_of_nonneg_right (hG_bound_Ioi u hu.le) (Real.exp_pos (y * u)).le
      have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-(y ^ 3) / 12)).le
      calc Real.exp (-(y ^ 3) / 12) * (-(D.G (u : ℂ)).re * Real.exp (y * u))
          ≤ Real.exp (-(y ^ 3) / 12) *
              (16 * (2 + u) ^ (-(3 / 2 : ℝ)) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) *
                Real.exp (y * u)) := h2
        _ = 16 * (2 + u) ^ (-(3 / 2 : ℝ)) *
              (Real.exp (-(y ^ 3) / 12) * (Real.exp (y * u) *
                Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)))) := by ring
        _ = 16 * (2 + u) ^ (-(3 / 2 : ℝ)) *
              Real.exp (-(y ^ 3) / 12 + y * u - (4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
    let f_env : ℝ → ℝ := fun u =>
      16 * (2 + u) ^ (-(3 / 2 : ℝ)) * Real.exp (-(y ^ 3) / 12 + y * u - (4 / 3 : ℝ) * u ^ (3 / 2 : ℝ))
    have hf_cont : ContinuousOn f_env (Ioi 0) := by
      refine ((continuousOn_const.mul ((continuousOn_const.add continuousOn_id).rpow_const
        fun u hu => Or.inl (by linarith [mem_Ioi.mp hu] : 0 < 2 + u).ne')).mul ?_)
      exact (((continuousOn_const.add (continuousOn_const.mul continuousOn_id)).sub
        (continuousOn_const.mul (continuousOn_id.rpow_const fun _ _ =>
          Or.inr (by norm_num : (0 : ℝ) ≤ 3 / 2))))).rexp
    have hf_int : IntegrableOn f_env (Ioi 0) := by
      have hi := integrableOn_airy_exp_Ioi (ν := (0 : ℝ)) (b := y)
        (by positivity : (0 : ℝ) ≤ 16 * Real.exp (-(y ^ 3) / 12))
      refine hi.mono' (hf_cont.aestronglyMeasurable measurableSet_Ioi)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : 0 < u) => ?_)
      have hp : (2 + u) ^ (-(3 / 2 : ℝ)) ≤ 1 := by
        rw [Real.rpow_neg (by linarith)]
        exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by linarith) (by norm_num))
      rw [Real.norm_of_nonneg (by positivity), at47_env_ofReal_nonneg hu.le, Real.rpow_zero, mul_one]
      have hexp_eq : Real.exp (-(y ^ 3) / 12 + y * u - (4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) =
          Real.exp (-(y ^ 3) / 12) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (y * u) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      dsimp [f_env]; rw [hexp_eq]
      calc 16 * (2 + u) ^ (-(3 / 2 : ℝ)) * (Real.exp (-(y ^ 3) / 12) *
              Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (y * u))
          ≤ 16 * 1 * (Real.exp (-(y ^ 3) / 12) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (y * u)) := by
            gcongr
        _ = 16 * Real.exp (-(y ^ 3) / 12) * Real.exp (-(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (y * u) := by
            ring
    have hmain : Real.exp (-(y ^ 3) / 12) * ∫ u in Ioi (0 : ℝ), -(D.G (u : ℂ)).re * Real.exp (y * u) ≤
        ∫ u in Ioi (0 : ℝ), f_env u := by
      rw [← integral_const_mul]
      exact setIntegral_mono_on (hint_full.integrableOn.const_mul _) hf_int measurableSet_Ioi hpt_Ioi
    let a₁ := y ^ 2 / 16
    let a₂ := y ^ 2
    have ha₁ : 0 < a₁ := by positivity
    have ha₁₂ : a₁ ≤ a₂ := by dsimp [a₁, a₂]; nlinarith
    have hsp1 := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hf_int.mono_set Ioc_subset_Ioi_self) (hf_int.mono_set (Ioi_subset_Ioi ha₁.le))
    rw [Ioc_union_Ioi_eq_Ioi ha₁.le] at hsp1
    have hsp2 := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hf_int.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha₁.le)))
      (hf_int.mono_set (Ioi_subset_Ioi (by positivity : 0 ≤ a₂)))
    rw [Ioc_union_Ioi_eq_Ioi ha₁₂] at hsp2
    have hpart1 : ∫ u in Ioc 0 a₁, f_env u ≤ 24 := by
      have hle_c : ∀ u ∈ Ioc 0 a₁, f_env u ≤ 16 * Real.exp (-(y ^ 3) / 48) := by
        intro u hu
        have hu0 : 0 < u := hu.1
        have hp : (2 + u) ^ (-(3 / 2 : ℝ)) ≤ 1 := by
          rw [Real.rpow_neg (by linarith)]
          exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by linarith) (by norm_num))
        have hexp : Real.exp (-(y ^ 3) / 12 + y * u - (4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) ≤
            Real.exp (-(y ^ 3) / 48) := by
          refine Real.exp_le_exp.mpr ?_
          have hu_rpow : 0 ≤ u ^ (3 / 2 : ℝ) := Real.rpow_nonneg hu0.le _
          have hyu : y * u ≤ y ^ 3 / 16 := by
            have := mul_le_mul_of_nonneg_left hu.2 hy
            linarith [show y * a₁ = y ^ 3 / 16 by dsimp [a₁]; ring]
          linarith
        dsimp [f_env]
        calc 16 * (2 + u) ^ (-(3 / 2 : ℝ)) * Real.exp (-(y ^ 3) / 12 + y * u - (4 / 3 : ℝ) * u ^ (3 / 2 : ℝ))
            ≤ 16 * 1 * Real.exp (-(y ^ 3) / 48) := by gcongr
          _ = 16 * Real.exp (-(y ^ 3) / 48) := by ring
      have hIoc := setIntegral_mono_on (hf_int.mono_set Ioc_subset_Ioi_self)
        (continuousOn_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self) measurableSet_Ioc hle_c
      rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioc, sub_zero,
        ENNReal.toReal_ofReal ha₁.le] at hIoc
      have hexp_eb : 1 + y ^ 3 / 48 ≤ Real.exp (y ^ 3 / 48) := by
        linarith [Real.add_one_le_exp (y ^ 3 / 48)]
      have hy3_pos : 0 < y ^ 3 / 48 := by positivity
      have hinv : y ^ 2 * Real.exp (-(y ^ 3) / 48) ≤ 24 := by
        rw [show -(y ^ 3) / 48 = -(y ^ 3 / 48) by ring, Real.exp_neg, ← div_eq_mul_inv]
        rw [div_le_iff₀ (Real.exp_pos _)]
        have h1 : y ^ 2 ≤ 24 * (y ^ 3 / 48) := by
          have : y ^ 2 = (2 / y) * (24 * (y ^ 3 / 48)) := by field_simp [hy2.ne']; ring
          nlinarith [show 2 ≤ y by linarith]
        linarith
      calc ∫ u in Ioc 0 a₁, f_env u ≤ a₁ * (16 * Real.exp (-(y ^ 3) / 48)) := hIoc
        _ = y ^ 2 * Real.exp (-(y ^ 3) / 48) := by dsimp [a₁]; ring
        _ ≤ 24 := hinv
    have hpart2 : ∫ u in Ioc a₁ a₂, f_env u ≤ 512 := by
      have hle_c : ∀ u ∈ Ioc a₁ a₂, f_env u ≤ 16 * (a₁ ^ (-(3 / 2 : ℝ))) := by
        intro u hu
        have hu0 : 0 ≤ u := (ha₁.trans hu.1).le
        have hsaddle : -(y ^ 3) / 12 + y * u - (4 / 3 : ℝ) * u ^ (3 / 2 : ℝ) ≤ 0 := by
          have hr : u ^ (3 / 2 : ℝ) = (√u) ^ 3 := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hu0]; norm_num
          have husq : u = (√u) ^ 2 := (Real.sq_sqrt hu0).symm
          have hfact : -(y ^ 3) / 12 + y * (√u) ^ 2 - (4 / 3 : ℝ) * (√u) ^ 3 =
              -((y - 2 * √u) ^ 2 * (y + 4 * √u)) / 12 := by ring
          rw [hr]; conv_lhs => lhs; rhs; rw [husq]
          rw [hfact]
          exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr
            (mul_nonneg (sq_nonneg _) (by linarith [Real.sqrt_nonneg u]))) (by norm_num)
        have hexp : Real.exp (-(y ^ 3) / 12 + y * u - (4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) ≤ 1 :=
          Real.exp_le_one_iff.mpr hsaddle
        have hrpow_le : (2 + u) ^ (-(3 / 2 : ℝ)) ≤ a₁ ^ (-(3 / 2 : ℝ)) := by
          rw [Real.rpow_neg (by linarith), Real.rpow_neg ha₁.le, inv_eq_one_div, inv_eq_one_div]
          refine one_div_le_one_div_of_le (Real.rpow_pos_of_pos ha₁ _)
            (Real.rpow_le_rpow ha₁.le (by linarith [hu.1]) (by norm_num))
        dsimp [f_env]
        calc 16 * (2 + u) ^ (-(3 / 2 : ℝ)) * Real.exp (-(y ^ 3) / 12 + y * u - (4 / 3 : ℝ) * u ^ (3 / 2 : ℝ))
            ≤ 16 * (a₁ ^ (-(3 / 2 : ℝ))) * 1 := by gcongr
          _ = 16 * a₁ ^ (-(3 / 2 : ℝ)) := mul_one _
      have hIoc := setIntegral_mono_on (hf_int.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha₁.le)))
        (continuousOn_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self) measurableSet_Ioc hle_c
      rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr ha₁₂)] at hIoc
      have ha₁_eval : a₁ ^ (-(3 / 2 : ℝ)) = 64 / y ^ 3 := by
        have hy4 : a₁ = (y / 4) ^ 2 := by dsimp [a₁]; ring
        rw [hy4, ← Real.rpow_natCast (y / 4), ← Real.rpow_mul (by positivity)]
        norm_num
        field_simp [hy2.ne']; norm_num
      calc ∫ u in Ioc a₁ a₂, f_env u ≤ (a₂ - a₁) * (16 * a₁ ^ (-(3 / 2 : ℝ))) := hIoc
        _ ≤ a₂ * (16 * (64 / y ^ 3)) := by rw [ha₁_eval]; gcongr; linarith
        _ = 1024 / y := by dsimp [a₂]; field_simp [hy2.ne']; ring
        _ ≤ 512 := by rw [div_le_iff₀ (by linarith)]; linarith
    have hpart3 : ∫ u in Ioi a₂, f_env u ≤ 48 := by
      have hi_exp : IntegrableOn (fun u : ℝ => 16 * Real.exp (-(1 / 3 : ℝ) * u)) (Ioi a₂) :=
        (integrableOn_exp_mul_Ioi (by norm_num : -(1 / 3 : ℝ) < 0) a₂).const_mul 16
      have hle_e : ∀ u ∈ Ioi a₂, f_env u ≤ 16 * Real.exp (-(1 / 3 : ℝ) * u) := by
        intro u hu
        have ha₂_ge : 4 ≤ a₂ := by dsimp [a₂]; nlinarith
        have hu4 : 4 ≤ u := ha₂_ge.trans (mem_Ioi.mp hu).le
        have hu1 : 1 ≤ √u := by rw [Real.one_le_sqrt]; linarith
        have hsqrt_ge : y ≤ √u := Real.le_sqrt_of_sq_le (mem_Ioi.mp hu).le
        have h32 : y * u + (1 / 3 : ℝ) * u ≤ (4 / 3 : ℝ) * u ^ (3 / 2 : ℝ) := by
          have hr : u ^ (3 / 2 : ℝ) = √u * u := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one (by linarith : (u : ℝ) ≠ 0)]; norm_num
          rw [hr]
          have h1 : y * u ≤ √u * u := mul_le_mul_of_nonneg_right hsqrt_ge (by linarith)
          have h2 : u ≤ √u * u := le_mul_of_one_le_left (by linarith) hu1
          linarith
        have hexp : Real.exp (-(y ^ 3) / 12 + y * u - (4 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) ≤
            Real.exp (-(1 / 3 : ℝ) * u) := by
          refine Real.exp_le_exp.mpr ?_
          linarith [show 0 ≤ y ^ 3 / 12 by positivity]
        have hp : (2 + u) ^ (-(3 / 2 : ℝ)) ≤ 1 := by
          rw [Real.rpow_neg (by linarith)]
          exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by linarith) (by norm_num))
        dsimp [f_env]
        calc 16 * (2 + u) ^ (-(3 / 2 : ℝ)) * Real.exp (-(y ^ 3) / 12 + y * u - (4 / 3 : ℝ) * u ^ (3 / 2 : ℝ))
            ≤ 16 * 1 * Real.exp (-(1 / 3 : ℝ) * u) := by gcongr
          _ = 16 * Real.exp (-(1 / 3 : ℝ) * u) := by ring
      have hIoi := setIntegral_mono_on (hf_int.mono_set (Ioi_subset_Ioi (by positivity : 0 ≤ a₂)))
        hi_exp measurableSet_Ioi hle_e
      have hcomp := integral_exp_mul_Ioi (by norm_num : -(1 / 3 : ℝ) < 0) (0 : ℝ)
      have hmono := setIntegral_mono_set
        ((integrableOn_exp_mul_Ioi (by norm_num : -(1 / 3 : ℝ) < 0) 0).const_mul 16)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun _ _ => by positivity)
        (Eventually.of_forall (Ioi_subset_Ioi (by positivity : 0 ≤ a₂)))
      have hval : ∫ u in Ioi (0 : ℝ), 16 * Real.exp (-(1 / 3 : ℝ) * u) = 48 := by
        rw [integral_const_mul]
        have he : ∫ u in Ioi (0 : ℝ), Real.exp (-(1 / 3 : ℝ) * u) = 3 := by
          rw [hcomp, mul_zero, Real.exp_zero]; norm_num
        linarith
      linarith
    linarith [hmain, hsp1, hsp2, hpart1, hpart2, hpart3, le_max_right C_small 1600]

/-- Explicit non-vacuity witness for `ShellGapPackage` (and hence `ShellReductionPackage`)
built from `ShellHBData.airy` (`m = 1`). -/
noncomputable def shellGapPackage_nonvacuous : ShellGapPackage ShellHBData.airy := by
  classical
  let D := ShellHBData.airy
  let c : ℕ → ℝ := fun k => (k : ℝ) + 1000
  have hc_pos : ∀ k, 0 < c k := fun k => by dsimp [c]; positivity
  have hc_tend : Tendsto c atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  let cut : ℝ → ℝ := fun Δ => min 1 (max 0 (Δ - 1))
  let bump : ℝ → ℝ := fun u => max 0 (1 - |u + 1|)
  have hbump_cont : Continuous bump := by fun_prop
  have hbump_nn : ∀ u, 0 ≤ bump u := fun u => le_max_left _ _
  have hbump_supp : ∀ u, u ∉ Icc (-2 : ℝ) 0 → bump u = 0 := fun u hu => by
    have hlt : 1 ≤ |u + 1| := by
      rcases not_and_or.mp hu with h | h <;> push Not at h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    exact max_eq_left (by linarith)
  have hbump_int : Integrable bump :=
    hbump_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      fun u hu => by_contra fun h => hu (hbump_supp u h))
  have hbump_pos : 0 < ∫ u : ℝ, bump u := by
    refine (integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hbump_nn) hbump_int).mpr ?_
    have hopen : IsOpen {u : ℝ | 0 < bump u} := isOpen_lt continuous_const hbump_cont
    have hm1 : (-1 : ℝ) ∈ {u : ℝ | 0 < bump u} := by norm_num [bump]
    exact lt_of_lt_of_le (hopen.measure_pos volume ⟨_, hm1⟩)
      (measure_mono fun u hu => Function.mem_support.mpr hu.ne')
  let bumpN : ℝ → ℝ := fun u => bump u / ∫ x : ℝ, bump x
  have hbumpN_int : ∫ u : ℝ, bumpN u = 1 := by
    rw [integral_div, div_self hbump_pos.ne']
  let Δ_of : ℕ → ℝ → ℝ := fun k u => c k / π ^ 2 - (c k) ^ (1 / 3 : ℝ) / shellBeta1 * u
  let χ : ℕ → ℝ → ℝ := fun k u => if 0 < Δ_of k u then cut (Δ_of k u) else 0
  have hχ_bd : ∀ k u, 0 ≤ χ k u ∧ χ k u ≤ 1 := fun k u => by
    dsimp [χ, cut]; split_ifs
    · exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
    · exact ⟨le_rfl, zero_le_one⟩
  have hχ_left : ∀ k, ∀ u ≤ (0 : ℝ), χ k u = 1 := by
    intro k u hu
    have hpi : π ^ 2 < 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
    have hc100 : (2 : ℝ) < c k / π ^ 2 := by
      have hk : (1000 : ℝ) ≤ c k := by dsimp [c]; linarith [Nat.cast_nonneg (α := ℝ) k]
      rw [lt_div_iff₀ (by positivity)]; linarith
    have hΔ2 : 2 ≤ Δ_of k u := by
      have h1 : 0 ≤ (c k) ^ (1 / 3 : ℝ) / shellBeta1 * (-u) :=
        mul_nonneg (div_nonneg (Real.rpow_nonneg (hc_pos k).le _) shellBeta1_pos.le) (neg_nonneg.mpr hu)
      dsimp [Δ_of]; linarith
    dsimp [χ, cut]
    rw [show (if 0 < Δ_of k u then min 1 (max 0 (Δ_of k u - 1)) else 0) =
      min 1 (max 0 (Δ_of k u - 1)) from ite_eq_left_iff.mpr (fun h => absurd (by linarith) h)]
    exact min_eq_left (le_max_of_le_right (by linarith))
  have hχ_tend : ∀ u : ℝ, ∀ᶠ k in atTop, χ k u = 1 := by
    intro u
    have hlim : Tendsto (fun k => Δ_of k u) atTop atTop := by
      have h23 : Tendsto (fun k => (c k) ^ (2 / 3 : ℝ) / π ^ 2 - u / shellBeta1) atTop atTop := by
        rw [Filter.tendsto_atTop]
        intro b
        have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc_tend
        filter_upwards [hp.eventually (eventually_ge_atTop ((b + u / shellBeta1) * π ^ 2))] with k hk
        have h1 : b + u / shellBeta1 ≤ (c k) ^ (2 / 3 : ℝ) / π ^ 2 :=
          (le_div_iff₀ (by positivity)).mpr hk
        linarith
      have heq : ∀ k, Δ_of k u = (c k) ^ (1 / 3 : ℝ) * ((c k) ^ (2 / 3 : ℝ) / π ^ 2 - u / shellBeta1) := by
        intro k
        have hsum : (c k) ^ (1 / 3 : ℝ) * (c k) ^ (2 / 3 : ℝ) = c k := by
          rw [← Real.rpow_add (hc_pos k)]; norm_num
        dsimp [Δ_of]; calc c k / π ^ 2 - (c k) ^ (1 / 3 : ℝ) / shellBeta1 * u
            = ((c k) ^ (1 / 3 : ℝ) * (c k) ^ (2 / 3 : ℝ)) / π ^ 2 -
              (c k) ^ (1 / 3 : ℝ) * (u / shellBeta1) := by rw [hsum]; ring
          _ = _ := by ring
      simp_rw [heq]
      rw [Filter.tendsto_atTop]
      intro b
      filter_upwards [((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hc_tend).eventually
        (eventually_ge_atTop (max b 1)), h23.eventually (eventually_ge_atTop (max b 1))] with k hk1 hk2
      dsimp only [Function.comp_apply] at hk1
      have hb1 : b ≤ max b 1 := le_max_left _ _
      have h1 : 1 ≤ max b 1 := le_max_right _ _
      nlinarith
    filter_upwards [hlim.eventually (eventually_ge_atTop (2 : ℝ))] with k hk
    dsimp [χ, cut]
    rw [show (if 0 < Δ_of k u then min 1 (max 0 (Δ_of k u - 1)) else 0) =
      min 1 (max 0 (Δ_of k u - 1)) from ite_eq_left_iff.mpr (fun h => absurd (by linarith) h)]
    exact min_eq_left (le_max_of_le_right (by linarith))
  let δ : ℕ → ℝ := fun k => ∫ u : ℝ, χ k u * D.normG u
  have hδ_lim : Tendsto δ atTop (𝓝 0) := by
    have h0 : ∫ u : ℝ, D.normG u = 0 := D.normG_integral
    rw [← h0]
    refine tendsto_integral_of_dominated_convergence (fun u => |D.normG u|)
      (fun k => ?_) D.normG_integrable.abs ?_ ?_
    · have hc_meas : Measurable (fun u => χ k u) := by
        refine Measurable.ite (measurableSet_lt measurable_const (by unfold Δ_of; fun_prop))
          (by unfold cut Δ_of; fun_prop) measurable_const
      exact hc_meas.aestronglyMeasurable.mul D.normG_integrable.aestronglyMeasurable
    · intro k; refine Eventually.of_forall fun u => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _)
        (abs_le.mpr ⟨by linarith [(hχ_bd k u).1], (hχ_bd k u).2⟩)
    · refine Eventually.of_forall fun u => ?_
      have hlim := ((tendsto_const_nhds (x := (1 : ℝ))).congr'
        ((hχ_tend u).mono fun _ h => h.symm)).mul_const (D.normG u)
      rwa [one_mul] at hlim
  let W : ℕ → ℝ → ℝ := fun k u => D.normG u - δ k * bumpN u
  let q : ℕ → ℝ → ℝ := fun k Δ =>
    (1 / 2) * cut Δ * (shellBeta1 / (c k) ^ (1 / 3 : ℝ)) *
      W k ((c k / π ^ 2 - Δ) * shellBeta1 / (c k) ^ (1 / 3 : ℝ)) *
      (shellRho0 (c k) (max (1 / 2) Δ))⁻¹
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 10)
  let p : ℕ → ℝ → ℝ := fun k Δ => -q k Δ + ε k * |q k Δ|
  have hW_eq : ∀ k u, shellWindowProfile (c k) (fun Δ => 2 * q k Δ) u = χ k u * W k u := by
    intro k u
    have hc13 : 0 < (c k) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (hc_pos k) _
    unfold shellWindowProfile χ; dsimp only
    have hΔeq : c k / π ^ 2 - u / shellBeta1 * (c k) ^ (1 / 3 : ℝ) = Δ_of k u := by
      dsimp [Δ_of]; ring
    rw [hΔeq]
    split_ifs with h
    · by_cases h1 : Δ_of k u ≤ 1
      · have hcut : cut (Δ_of k u) = 0 := by
          dsimp [cut]; rw [max_eq_left (by linarith), min_eq_right zero_le_one]
        dsimp [q]; rw [hcut]; ring
      · push Not at h1
        have hmax : max (1 / 2) (Δ_of k u) = Δ_of k u := max_eq_right (by linarith)
        have hrho_ne : shellRho0 (c k) (Δ_of k u) ≠ 0 := (shellRho0_pos (hc_pos k) h).ne'
        have hu_back : (c k / π ^ 2 - Δ_of k u) * shellBeta1 / (c k) ^ (1 / 3 : ℝ) = u := by
          dsimp [Δ_of]; field_simp [hc13.ne', shellBeta1_pos.ne']; ring
        dsimp [q]; rw [hmax, hu_back]
        field_simp [hc13.ne', shellBeta1_pos.ne', hrho_ne]
    · simp
  have hW_int : ∀ k, Integrable (fun u => χ k u * W k u) := fun k => by
    have heq : (fun u => χ k u * W k u) = fun u => χ k u * D.normG u - (δ k) * (χ k u * bumpN u) := by
      ext u; dsimp [W]; ring
    rw [heq]
    have hmχ : AEStronglyMeasurable (fun u => χ k u) volume :=
      (Measurable.ite (measurableSet_lt measurable_const (by unfold Δ_of; fun_prop))
        (by unfold cut Δ_of; fun_prop) measurable_const).aestronglyMeasurable
    have hi1 : Integrable (fun u => χ k u * D.normG u) :=
      D.normG_integrable.abs.mono' (hmχ.mul D.normG_integrable.aestronglyMeasurable)
        (Eventually.of_forall fun u => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _)
            (abs_le.mpr ⟨by linarith [(hχ_bd k u).1], (hχ_bd k u).2⟩))
    have hbm_int : Integrable bumpN := hbump_int.div_const (∫ x : ℝ, bump x)
    have hm_prod : AEStronglyMeasurable (fun u => χ k u * bumpN u) volume :=
      hmχ.mul hbm_int.aestronglyMeasurable
    have hi2 : Integrable (fun u => δ k * (χ k u * bumpN u)) :=
      (hbm_int.abs.mono' hm_prod
        (Eventually.of_forall fun u => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _)
            (abs_le.mpr ⟨by linarith [(hχ_bd k u).1], (hχ_bd k u).2⟩))).const_mul _
    exact hi1.sub hi2
  have hχ_bump : ∀ k u, χ k u * bumpN u = bumpN u := fun k u => by
    by_cases hu0 : u ≤ 0
    · rw [hχ_left k u hu0, one_mul]
    · push Not at hu0
      have hb0 : bump u = 0 := hbump_supp u fun h => by linarith [h.2]
      dsimp [bumpN]; rw [hb0, zero_div, mul_zero]
  have hf_int_zero : ∀ k, (∫ Δ in Ioi (0 : ℝ), (2 * q k Δ) * shellRho0 (c k) Δ) = 0 := fun k => by
    rw [← integral_shellWindowProfile (hc_pos k)]
    simp_rw [hW_eq]
    have heq : (fun u => χ k u * W k u) = fun u => χ k u * D.normG u - δ k * bumpN u := by
      ext u; dsimp [W]; rw [mul_sub, ← mul_assoc, mul_comm (χ k u) (δ k), mul_assoc, hχ_bump]
    have hmχ : AEStronglyMeasurable (fun u => χ k u) volume :=
      (Measurable.ite (measurableSet_lt measurable_const (by unfold Δ_of; fun_prop))
        (by unfold cut Δ_of; fun_prop) measurable_const).aestronglyMeasurable
    have hi1 : Integrable (fun u => χ k u * D.normG u) :=
      D.normG_integrable.abs.mono' (hmχ.mul D.normG_integrable.aestronglyMeasurable)
        (Eventually.of_forall fun u => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _)
            (abs_le.mpr ⟨by linarith [(hχ_bd k u).1], (hχ_bd k u).2⟩))
    rw [heq, integral_sub hi1 ((hbump_int.div_const _).const_mul _), integral_const_mul,
      hbumpN_int, mul_one, sub_self]
  have hW_tail_left : ∀ k, ∀ u ≤ D.tm, W k u = D.normG u := fun k u hu => by
    have htm : airyZero 1 < -2.33 := airyZero_one.2
    have hu2 : u < -2.33 := hu.trans_lt htm
    have hnot : u ∉ Icc (-2 : ℝ) 0 := fun h => by linarith [h.1]
    dsimp [W, bumpN]; rw [hbump_supp u hnot, zero_div, mul_zero, sub_zero]
  have hM_lim : Tendsto (fun k => shellMass (c k) (fun Δ => 2 * q k Δ)) atTop (𝓝 1) := by
    have heq : ∀ k, shellMass (c k) (fun Δ => 2 * q k Δ) = ∫ u : ℝ, |χ k u * W k u| := fun k => by
      rw [← integral_abs_shellWindowProfile (hc_pos k)]; simp_rw [hW_eq]
    simp_rw [heq]
    rw [← D.normG_abs_integral]
    have hδ_le1 : ∀ᶠ k in atTop, |δ k| ≤ 1 :=
      hδ_lim.abs.eventually (eventually_lt_nhds (by norm_num : |(0 : ℝ)| < 1)) |>.mono fun _ h => h.le
    obtain ⟨K, hK⟩ := eventually_atTop.mp hδ_le1
    have hlim_shift : Tendsto (fun k => ∫ u : ℝ, |χ (k + K) u * W (k + K) u|) atTop
        (𝓝 (∫ u : ℝ, |D.normG u|)) := by
      refine tendsto_integral_of_dominated_convergence (fun u => |D.normG u| + bumpN u)
        (fun k => (hW_int (k + K)).abs.aestronglyMeasurable)
        (D.normG_integrable.abs.add (hbump_int.div_const _)) ?_ ?_
      · intro k; refine Eventually.of_forall fun u => ?_
        rw [Real.norm_of_nonneg (abs_nonneg _), abs_mul]
        have h1 : |χ (k + K) u| ≤ 1 := abs_le.mpr ⟨by linarith [(hχ_bd (k + K) u).1], (hχ_bd (k + K) u).2⟩
        have h2 : |W (k + K) u| ≤ |D.normG u| + bumpN u := by
          dsimp [W]
          calc |D.normG u - δ (k + K) * bumpN u| ≤ |D.normG u| + |δ (k + K) * bumpN u| := abs_sub _ _
            _ = |D.normG u| + |δ (k + K)| * bumpN u := by
                rw [abs_mul, abs_of_nonneg (div_nonneg (hbump_nn u) hbump_pos.le)]
            _ ≤ |D.normG u| + 1 * bumpN u := by
                gcongr; exact hK (k + K) (Nat.le_add_left K k)
            _ = _ := by ring
        exact (mul_le_of_le_one_left (abs_nonneg _) h1).trans h2
      · refine Eventually.of_forall fun u => ?_
        have hlim_pt : Tendsto (fun k => |χ (k + K) u * W (k + K) u|) atTop (𝓝 |1 * (D.normG u - 0 * bumpN u)|) :=
          (((tendsto_const_nhds (x := (1 : ℝ))).congr' (by
            filter_upwards [(tendsto_add_atTop_nat K).eventually (hχ_tend u)] with k hk
            exact hk.symm)).mul
            (tendsto_const_nhds.sub ((hδ_lim.comp (tendsto_add_atTop_nat K)).mul_const _))).abs
        simpa using hlim_pt
    exact (tendsto_add_atTop_iff_nat K).mp hlim_shift
  have hq_cont : ∀ k, Continuous (q k) := fun k => by
    dsimp [q, W, cut, bumpN, bump, ShellHBData.normG]
    refine (((((continuous_const.mul ((continuous_const.min (continuous_const.max
      (continuous_id.sub continuous_const))))).mul continuous_const).mul ?_).mul ?_))
    · exact ((D.G_diff.continuous.comp Complex.continuous_ofReal |> Complex.continuous_re.comp).div_const _ |>.sub
        (continuous_const.mul ((continuous_const.max (continuous_const.sub
          (continuous_id.add continuous_const).abs)).div_const _))).comp
        (((continuous_const.sub continuous_id).mul continuous_const).div_const _)
    · refine Continuous.inv₀ ?_ fun Δ => ?_
      · exact (continuousOn_shellRho0 (c k)).comp_continuous (continuous_const.max continuous_id)
          fun Δ => lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      · exact (shellRho0_pos (hc_pos k) (lt_of_lt_of_le (by norm_num) (le_max_left _ _))).ne'
  have hp_cont : ∀ k, Continuous (p k) := fun k => (hq_cont k).neg.add (continuous_const.mul (hq_cont k).abs)
  have hq_nz : ∀ k, ∃ Δ : ℝ, 0 ≤ Δ ∧ q k Δ ≠ 0 := by
    intro k
    have h1 : 0 < ∫ x : ℝ, max (D.normG x) 0 := by
      have hpos_eq : (fun x : ℝ => max (D.normG x) 0) = fun x => (|D.normG x| + D.normG x) / 2 :=
        funext fun x => posPart_eq_abs_add_div_two _
      rw [hpos_eq, integral_div, integral_add D.normG_integrable.abs D.normG_integrable,
        D.normG_abs_integral, D.normG_integral, add_zero]
      norm_num
    have hx : ∃ u₀ : ℝ, u₀ ≤ D.tm ∧ D.normG u₀ ≠ 0 := by
      by_contra h0; push Not at h0
      have hm0 : ∀ x : ℝ, max (D.normG x) 0 = 0 := by
        intro x
        by_cases hx : x ≤ D.tm
        · rw [h0 x hx, max_self]
        · push Not at hx
          have hmax : D.S.max' D.S_nonempty < x := by simpa [D, ShellHBData.airy] using hx
          obtain ⟨hform, hNsq, hden⟩ := D.G_re_tail hmax
          have hSc : D.S.card = 1 :=
            D.m_eq.elim (fun h => h.2) (fun h => False.elim (h.1 rfl))
          have hle : D.normG x ≤ 0 := by
            unfold ShellHBData.normG; rw [hform, hSc, pow_one, neg_one_mul, neg_div]
            exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg hNsq.le hden.le))
              D.G_l1_pos.le
          exact max_eq_right hle
      simp_rw [hm0, integral_zero] at h1; linarith
    obtain ⟨u₀, hu₀_le, hu₀_ne⟩ := hx
    have hΔ₀ : 2 < Δ_of k u₀ := by
      have hpi : π ^ 2 < 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
      have hc100 : (2 : ℝ) < c k / π ^ 2 := by
        have hk : (1000 : ℝ) ≤ c k := by dsimp [c]; linarith [Nat.cast_nonneg (α := ℝ) k]
        rw [lt_div_iff₀ (by positivity)]; linarith
      have hu0_neg : u₀ < 0 := hu₀_le.trans_lt (airyZero_one.2.trans (by norm_num))
      have h1 : 0 ≤ (c k) ^ (1 / 3 : ℝ) / shellBeta1 * (-u₀) :=
        mul_nonneg (div_nonneg (Real.rpow_nonneg (hc_pos k).le _) shellBeta1_pos.le) (neg_nonneg.mpr hu0_neg.le)
      dsimp [Δ_of]; linarith
    refine ⟨Δ_of k u₀, (by linarith : (0 : ℝ) ≤ Δ_of k u₀), fun hq0 => hu₀_ne ?_⟩
    have hw := hW_eq k u₀
    have h0' : shellWindowProfile (c k) (fun Δ => 2 * q k Δ) u₀ = 0 := by
      unfold shellWindowProfile; dsimp only
      have hΔeq : c k / π ^ 2 - u₀ / shellBeta1 * (c k) ^ (1 / 3 : ℝ) = Δ_of k u₀ := by dsimp [Δ_of]; ring
      rw [hΔeq]
      rw [ite_eq_left_iff.mpr (fun h => absurd (by linarith : 0 < Δ_of k u₀) h)]
      rw [hq0, mul_zero, zero_mul, mul_zero]
    rw [h0', hχ_left k u₀ (hu₀_le.trans (airyZero_one.2.trans (by norm_num)).le), one_mul,
      hW_tail_left k u₀ hu₀_le] at hw
    exact hw.symm
  have hM_ge_half : ∀ k, (1 / 2 : ℝ) ≤ shellMass (c k) (fun Δ => 2 * q k Δ) := by
    intro k
    have heq : shellMass (c k) (fun Δ => 2 * q k Δ) = ∫ u : ℝ, |χ k u * W k u| := by
      rw [← integral_abs_shellWindowProfile (hc_pos k)]; simp_rw [hW_eq]
    rw [heq]
    have hsp := integral_add_compl (measurableSet_Iic (a := D.tm)) (hW_int k).abs
    have hleft_eq : ∫ u in Iic D.tm, |χ k u * W k u| = ∫ u in Iic D.tm, D.normG u := by
      refine setIntegral_congr_fun measurableSet_Iic fun u hu => ?_
      have hu0 : u ≤ 0 := (mem_Iic.mp hu).trans (airyZero_one.2.trans (by norm_num)).le
      rw [hχ_left k u hu0, one_mul, hW_tail_left k u (mem_Iic.mp hu)]
      exact abs_of_nonneg (div_nonneg (D.G_nonneg_left u (mem_Iic.mp hu)) D.G_l1_pos.le)
    have hright_eq : ∫ u in Iic D.tm, D.normG u = 1 / 2 := by
      have h1 : ∫ u : ℝ, max (D.normG u) 0 = 1 / 2 := by
        have hpos_eq : (fun x : ℝ => max (D.normG x) 0) = fun x => (|D.normG x| + D.normG x) / 2 :=
          funext fun x => posPart_eq_abs_add_div_two _
        rw [hpos_eq, integral_div, integral_add D.normG_integrable.abs D.normG_integrable,
          D.normG_abs_integral, D.normG_integral, add_zero]
      have h2 : ∫ u in Iic D.tm, max (D.normG u) 0 = ∫ u in Iic D.tm, D.normG u :=
        setIntegral_congr_fun measurableSet_Iic fun u hu =>
          max_eq_left (div_nonneg (D.G_nonneg_left u hu) D.G_l1_pos.le)
      have h3 : ∫ u in (Iic D.tm)ᶜ, max (D.normG u) 0 = 0 := by
        refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
        rw [compl_Iic, mem_Ioi] at hu
        have hmax : D.S.max' D.S_nonempty < u := by simpa [D, ShellHBData.airy] using hu
        obtain ⟨hform, hNsq, hden⟩ := D.G_re_tail hmax
        have hSc : D.S.card = 1 := Finset.card_singleton _
        have hle : D.normG u ≤ 0 := by
          unfold ShellHBData.normG; rw [hform, hSc, pow_one, neg_one_mul, neg_div]
          exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg hNsq.le hden.le)) D.G_l1_pos.le
        exact max_eq_right hle
      have hpos_int : Integrable (fun u : ℝ => max (D.normG u) 0) := by
        have hpos_eq : (fun x : ℝ => max (D.normG x) 0) = fun x => (|D.normG x| + D.normG x) / 2 :=
          funext fun x => posPart_eq_abs_add_div_two _
        rw [hpos_eq]; exact (D.normG_integrable.abs.add D.normG_integrable).div_const 2
      have hsp' := integral_add_compl (measurableSet_Iic (a := D.tm)) hpos_int
      rw [h2, h3, add_zero] at hsp'
      linarith
    have hnn_c : 0 ≤ ∫ u in (Iic D.tm)ᶜ, |χ k u * W k u| :=
      setIntegral_nonneg measurableSet_Iic.compl fun _ _ => abs_nonneg _
    linarith
  let B := airyLaplace_airy_normG_bdd.choose
  have hB_pos : 0 < B := airyLaplace_airy_normG_bdd.choose_spec.1
  have hB : ∀ y : ℝ, 0 ≤ y → airyLaplace (fun u => -ShellHBData.airy.normG u) y ≤ B :=
    airyLaplace_airy_normG_bdd.choose_spec.2
  let L_val : ℕ → ℝ → ℝ := fun k σ =>
    shellMass (c k) (fun Δ => 2 * q k Δ) *
      airyLaplace (fun u => -D.normG u) (shellCs * (c k) ^ (1 / 3 : ℝ) * min σ (1 - σ))
  let Mtilde_f : ℕ → ℝ → ℝ := fun k σ =>
    if σ < 1 / 2 then L_val k σ else if 1 / 2 < σ then -L_val k σ else 0
  let Mtilde_hhat : ℕ → ℝ → ℝ := fun k σ => if σ < 1 / 2 then 2 * L_val k σ else L_val k σ
  let Mtilde_h : ℕ → ℝ → ℝ := fun k σ => Mtilde_hhat k (1 - σ)
  let h0 : ℕ → ℝ := fun k => (2 * B + 1) * shellMass (c k) (fun Δ => 2 * q k Δ)
  let E_strip : ℕ → ℝ → ℝ := fun k σ =>
    (shellMass (c k) (fun Δ => p k Δ + q k Δ) /
        shellMass (c k) (fun Δ => 2 * q k Δ)) ^ (-σ) *
      (2 * B + 1) ^ σ
  have h2q_cont : ∀ k, ContinuousOn (fun Δ => 2 * q k Δ) (Ici 0) := fun k =>
    continuousOn_const.mul (hq_cont k).continuousOn
  have h2q_int : ∀ k, IntegrableOn (fun Δ => (2 * q k Δ) * shellRho0 (c k) Δ) (Ioi 0) := fun k =>
    (integrable_shellWindowProfile_iff (hc_pos k) (fun Δ => 2 * q k Δ)).mp (by
      have heq : shellWindowProfile (c k) (fun Δ => 2 * q k Δ) = fun u => χ k u * W k u :=
        funext fun u => hW_eq k u
      rw [heq]; exact hW_int k)
  have hM_hhat_pos : ∀ k, 0 < shellMass (c k) (fun Δ => p k Δ + q k Δ) := by
    intro k
    have h2q := shellMass_pos_of_continuousOn (hc_pos k) (h2q_cont k) (h2q_int k)
      (let ⟨Δ, hΔ, hne⟩ := hq_nz k; ⟨Δ, hΔ, mul_ne_zero two_ne_zero hne⟩)
    have hsum : (fun Δ => p k Δ + q k Δ) = fun Δ => ε k * |q k Δ| := funext fun Δ => by dsimp [p]; ring
    have heq : shellMass (c k) (fun Δ => p k Δ + q k Δ) =
        (ε k / 2) * shellMass (c k) (fun Δ => 2 * q k Δ) := by
      rw [hsum]; unfold shellMass
      have h1 : (fun Δ => abs (ε k * |q k Δ|) * shellRho0 (c k) Δ) =
          fun Δ => (ε k / 2) * (|2 * q k Δ| * shellRho0 (c k) Δ) := by
        ext Δ
        rw [abs_mul (ε k), abs_abs, abs_of_pos (by dsimp [ε]; positivity : 0 < ε k),
          abs_mul (2 : ℝ) (q k Δ), (show |(2 : ℝ)| = 2 by norm_num)]
        ring
      rw [h1, integral_const_mul]
    rw [heq]
    exact mul_pos (by dsimp [ε]; positivity) h2q
  have hL_nn : ∀ k σ, σ ∈ Ioo 0 1 → 0 ≤ L_val k σ := fun k σ hσ => by
    have hm_nn : 0 ≤ shellMass (c k) (fun Δ => 2 * q k Δ) := shellMass_nonneg (hc_pos k) _
    have hy_pos : 0 < shellCs * (c k) ^ (1 / 3 : ℝ) * min σ (1 - σ) :=
      mul_pos (mul_pos shellCs_pos (Real.rpow_pos_of_pos (hc_pos k) _))
        (lt_min hσ.1 (sub_pos.mpr hσ.2))
    have hm1 : D.S.card = 1 := Finset.card_singleton _
    have hL_pos := shellLaplaceF_m1_pos D hm1 hy_pos
    have hnorm_pos : 0 ≤ airyLaplace (fun u => -D.normG u) (shellCs * (c k) ^ (1 / 3 : ℝ) * min σ (1 - σ)) := by
      let y := shellCs * (c k) ^ (1 / 3 : ℝ) * min σ (1 - σ)
      change 0 ≤ Real.exp (-(y ^ 3) / 12) * ∫ u : ℝ, (-D.normG u) * Real.exp (y * u)
      have heq : (fun u : ℝ => (-D.normG u) * Real.exp (y * u)) =
          fun (u : ℝ) => (-(D.G (u : ℂ)).re * Real.exp (y * u)) / ∫ x : ℝ, ‖D.G (x : ℂ)‖ := by
        ext u; unfold ShellHBData.normG; ring
      rw [heq, integral_div, ← mul_div_assoc]
      exact div_nonneg (mul_pos (Real.exp_pos _) hL_pos).le D.G_l1_pos.le
    exact mul_nonneg hm_nn hnorm_pos
  have hq_int : ∀ k, IntegrableOn (fun Δ => q k Δ * shellRho0 (c k) Δ) (Ioi 0) := fun k =>
    IntegrableOn.congr_fun ((h2q_int k).const_mul (1 / 2)) (fun Δ _ => by ring) measurableSet_Ioi
  have hp_int : ∀ k, IntegrableOn (fun Δ => p k Δ * shellRho0 (c k) Δ) (Ioi 0) := fun k => by
    have h1 := (hq_int k).neg
    have h2 := (abs_mul_shellRho0_integrableOn (hc_pos k) (hq_int k)).const_mul (ε k)
    exact (h1.add h2).congr_fun (fun Δ _ => by dsimp [p]; ring) measurableSet_Ioi
  have hE_inv_lim_of : ∀ y : ℝ, 0 < y →
      Tendsto (fun k => (E_strip k ((y / shellCs) * (c k) ^ (-(1 / 3 : ℝ))))⁻¹) atTop (𝓝 1) := by
    intro y hy
    let σ : ℕ → ℝ := fun k => (y / shellCs) * (c k) ^ (-(1 / 3 : ℝ))
    have hσ_pos : ∀ k, 0 < σ k := fun k =>
      mul_pos (div_pos hy shellCs_pos) (Real.rpow_pos_of_pos (hc_pos k) _)
    have hlog_bd : ∀ k, 0 ≤ σ k * Real.log (2 * ((k : ℝ) + 10) * (2 * B + 1)) ∧
        σ k * Real.log (2 * ((k : ℝ) + 10) * (2 * B + 1)) ≤
          6 * (y / shellCs) * ((c k) ^ (-(1 / 6 : ℝ)) +
            (c k) ^ (-(1 / 3 : ℝ)) * Real.log (2 * (2 * B + 1))) := by
      intro k
      have hck_ge : (k : ℝ) + 10 ≤ c k := by dsimp [c]; linarith
      have hk1 : (1 : ℝ) ≤ 2 * ((k : ℝ) + 10) * (2 * B + 1) := by
        have : (1 : ℝ) ≤ (k : ℝ) + 10 := by linarith [Nat.cast_nonneg (α := ℝ) k]
        nlinarith
      refine ⟨mul_nonneg (hσ_pos k).le (Real.log_nonneg hk1), ?_⟩
      have hlog1 : Real.log (c k) ≤ 6 * (c k) ^ (1 / 6 : ℝ) := by
        have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos (hc_pos k) (1 / 6 : ℝ))
        have h2 : Real.log ((c k) ^ (1 / 6 : ℝ)) = (1 / 6 : ℝ) * Real.log (c k) :=
          Real.log_rpow (hc_pos k) _
        linarith
      have hlog_prod : Real.log (2 * ((k : ℝ) + 10) * (2 * B + 1)) ≤
          Real.log (c k) + Real.log (2 * (2 * B + 1)) := by
        rw [← Real.log_mul (hc_pos k).ne' (by positivity)]
        refine Real.log_le_log (by positivity) ?_
        have h2B : 0 < 2 * (2 * B + 1) := by positivity
        nlinarith
      have hmul : σ k * Real.log (2 * ((k : ℝ) + 10) * (2 * B + 1)) ≤
          (y / shellCs) * (c k) ^ (-(1 / 3 : ℝ)) * (6 * (c k) ^ (1 / 6 : ℝ) + Real.log (2 * (2 * B + 1))) :=
        mul_le_mul_of_nonneg_left (hlog_prod.trans (by linarith)) (hσ_pos k).le
      have hrpow_eq : (c k) ^ (-(1 / 3 : ℝ)) * (c k) ^ (1 / 6 : ℝ) = (c k) ^ (-(1 / 6 : ℝ)) := by
        rw [← Real.rpow_add (hc_pos k)]; norm_num
      calc σ k * Real.log (2 * ((k : ℝ) + 10) * (2 * B + 1))
          ≤ (y / shellCs) * (6 * ((c k) ^ (-(1 / 3 : ℝ)) * (c k) ^ (1 / 6 : ℝ)) +
              (c k) ^ (-(1 / 3 : ℝ)) * Real.log (2 * (2 * B + 1))) :=
            hmul.trans_eq (by ring)
        _ ≤ 6 * (y / shellCs) * ((c k) ^ (-(1 / 6 : ℝ)) +
              (c k) ^ (-(1 / 3 : ℝ)) * Real.log (2 * (2 * B + 1))) := by
            rw [hrpow_eq]
            have hc13_nn : 0 ≤ (c k) ^ (-(1 / 3 : ℝ)) * Real.log (2 * (2 * B + 1)) :=
              mul_nonneg (Real.rpow_nonneg (hc_pos k).le _)
                (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * (2 * B + 1)))
            have hyc_nn : 0 ≤ y / shellCs := (div_pos hy shellCs_pos).le
            nlinarith [Real.rpow_nonneg (hc_pos k).le (-(1 / 6 : ℝ))]
    have harg_zero : Tendsto (fun k => σ k * Real.log (2 * ((k : ℝ) + 10) * (2 * B + 1))) atTop (𝓝 0) := by
      have h16 : Tendsto (fun k => (c k) ^ (-(1 / 6 : ℝ))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp hc_tend
      have h13 : Tendsto (fun k => (c k) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hc_tend
      have hrhs : Tendsto (fun k => 6 * (y / shellCs) * ((c k) ^ (-(1 / 6 : ℝ)) +
          (c k) ^ (-(1 / 3 : ℝ)) * Real.log (2 * (2 * B + 1)))) atTop (𝓝 0) := by
        simpa using ((h16.add (h13.mul_const _)).const_mul (6 * (y / shellCs)))
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
        (fun k => (hlog_bd k).1) (fun k => (hlog_bd k).2)
    have heq_E : ∀ k, (E_strip k (σ k))⁻¹ =
        Real.exp (-(σ k * Real.log (2 * ((k : ℝ) + 10) * (2 * B + 1)))) := by
      intro k
      have hm_eq : shellMass (c k) (fun Δ => p k Δ + q k Δ) / shellMass (c k) (fun Δ => 2 * q k Δ) =
          ε k / 2 := by
        have hsum : (fun Δ => p k Δ + q k Δ) = fun Δ => ε k * |q k Δ| := funext fun Δ => by dsimp [p]; ring
        have heq1 : shellMass (c k) (fun Δ => p k Δ + q k Δ) =
            (ε k / 2) * shellMass (c k) (fun Δ => 2 * q k Δ) := by
          rw [hsum]; unfold shellMass
          have h1 : (fun Δ => abs (ε k * |q k Δ|) * shellRho0 (c k) Δ) =
              fun Δ => (ε k / 2) * (|2 * q k Δ| * shellRho0 (c k) Δ) := by
            ext Δ
            rw [abs_mul (ε k), abs_abs, abs_of_pos (by dsimp [ε]; positivity : 0 < ε k),
              abs_mul (2 : ℝ) (q k Δ), (show |(2 : ℝ)| = 2 by norm_num)]
            ring
          rw [h1, integral_const_mul]
        have hfpos : 0 < shellMass (c k) (fun Δ => 2 * q k Δ) := by linarith [hM_ge_half k]
        rw [heq1, mul_div_cancel_right₀ _ hfpos.ne']
      have hk10 : (0 : ℝ) < 2 * ((k : ℝ) + 10) := by positivity
      have hB21 : (0 : ℝ) < 2 * B + 1 := by positivity
      have heq_base : (ε k / 2) = (2 * ((k : ℝ) + 10))⁻¹ := by dsimp [ε]; field_simp
      dsimp [E_strip]
      rw [hm_eq, heq_base, Real.rpow_def_of_pos (inv_pos.mpr hk10), Real.rpow_def_of_pos hB21,
        Real.log_inv, ← Real.exp_add, ← Real.exp_neg]
      congr 1
      rw [Real.log_mul hk10.ne' hB21.ne']
      ring
    change Tendsto (fun k => (E_strip k (σ k))⁻¹) atTop (𝓝 1)
    simp_rw [heq_E]
    simpa only [Function.comp_def, neg_zero, Real.exp_zero] using
      (Real.continuous_exp.continuousAt.tendsto.comp harg_zero.neg)
  let D_l1 := ∫ x : ℝ, ‖D.G (x : ℂ)‖
  let P_inf : ℂ → ℂ := fun z => ((-(1 / (2 * D_l1)) : ℝ) : ℂ) * D.G z
  let Q_inf : ℂ → ℂ := fun z => ((1 / (2 * D_l1) : ℝ) : ℂ) * D.G z
  refine ⟨c, hc_pos, hc_tend, p, q, fun k => (hp_cont k).continuousOn, fun k => (hq_cont k).continuousOn,
    hp_int, hq_int, hq_nz, h0, fun k => mul_nonneg (by positivity) (shellMass_nonneg (hc_pos k) _),
    ⟨2 * B + 1, fun k => by
      have hfpos := shellMass_pos_of_continuousOn (hc_pos k) (h2q_cont k)
        (h2q_int k) (let ⟨Δ, hΔ, hne⟩ := hq_nz k; ⟨Δ, hΔ, mul_ne_zero two_ne_zero hne⟩)
      dsimp [h0]; rw [mul_div_cancel_right₀ _ hfpos.ne']⟩,
    ⟨2, fun k => by
      have hqpos := shellMass_pos_of_continuousOn (hc_pos k) (hq_cont k).continuousOn
        (hq_int k) (hq_nz k)
      have hle : shellMass (c k) (p k) ≤ (1 + ε k) * shellMass (c k) (q k) := by
        unfold shellMass
        have hadd := (abs_mul_shellRho0_integrableOn (hc_pos k) (hq_int k)).const_mul (1 + ε k)
        rw [← integral_const_mul]
        refine setIntegral_mono_on (abs_mul_shellRho0_integrableOn (hc_pos k) (hp_int k)) hadd
          measurableSet_Ioi fun Δ hΔ => ?_
        have htri : |p k Δ| ≤ (1 + ε k) * |q k Δ| := by
          dsimp [p]
          calc abs (-q k Δ + ε k * |q k Δ|) ≤ |-q k Δ| + abs (ε k * |q k Δ|) := abs_add_le _ _
            _ = |q k Δ| + ε k * |q k Δ| := by
                rw [abs_neg, abs_mul (ε k) |q k Δ|, abs_abs, abs_of_pos (by dsimp [ε]; positivity : 0 < ε k)]
            _ = (1 + ε k) * |q k Δ| := by ring
        calc |p k Δ| * shellRho0 (c k) Δ ≤ ((1 + ε k) * |q k Δ|) * shellRho0 (c k) Δ :=
              mul_le_mul_of_nonneg_right htri (shellRho0_nonneg (hc_pos k) hΔ.le)
          _ = (1 + ε k) * (|q k Δ| * shellRho0 (c k) Δ) := by ring
      have hε1 : ε k ≤ 1 := by dsimp [ε]; rw [div_le_one (by positivity)]; linarith
      calc shellMass (c k) (p k) / shellMass (c k) (q k)
          ≤ ((1 + ε k) * shellMass (c k) (q k)) / shellMass (c k) (q k) :=
            div_le_div_of_nonneg_right hle hqpos.le
        _ = 1 + ε k := mul_div_cancel_right₀ _ hqpos.ne'
        _ ≤ 2 := by linarith⟩,
    fun k Δ _ => by
      have hsum : p k Δ + q k Δ = ε k * |q k Δ| := by dsimp [p]; ring
      rw [hsum]; exact mul_nonneg (by dsimp [ε]; positivity) (abs_nonneg _),
    fun k t ht htm => False.elim (htm (Finset.mem_singleton.mp ht)),
    fun _ => D.tm, D.tm, tendsto_const_nhds,
    fun k u hu => by
      have hu0 : u ≤ 0 := hu.trans (airyZero_one.2.trans (by norm_num)).le
      have hΔ2 : 2 ≤ Δ_of k u := by
        have hpi : π ^ 2 < 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
        have hc100 : (2 : ℝ) < c k / π ^ 2 := by
          have hk : (1000 : ℝ) ≤ c k := by dsimp [c]; linarith [Nat.cast_nonneg (α := ℝ) k]
          rw [lt_div_iff₀ (by positivity)]; linarith
        have h1 : 0 ≤ (c k) ^ (1 / 3 : ℝ) / shellBeta1 * (-u) :=
          mul_nonneg (div_nonneg (Real.rpow_nonneg (hc_pos k).le _) shellBeta1_pos.le) (neg_nonneg.mpr hu0)
        dsimp [Δ_of]; linarith
      unfold shellWindowProfile; dsimp only
      have hΔeq : c k / π ^ 2 - u / shellBeta1 * (c k) ^ (1 / 3 : ℝ) = Δ_of k u := by dsimp [Δ_of]; ring
      rw [hΔeq, ite_eq_left_iff.mpr (fun hn => absurd (by linarith : 0 < Δ_of k u) hn)]
      have hq_nn : 0 ≤ q k (Δ_of k u) := by
        have h2q : 2 * q k (Δ_of k u) = (1 * shellBeta1 / (c k) ^ (1 / 3 : ℝ)) * D.normG u *
            (shellRho0 (c k) (Δ_of k u))⁻¹ := by
          have hc13 : 0 < (c k) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos (hc_pos k) _
          have hcut1 : cut (Δ_of k u) = 1 := by
            dsimp [cut]; exact min_eq_left (le_max_of_le_right (by linarith))
          have hmax : max (1 / 2) (Δ_of k u) = Δ_of k u := max_eq_right (by linarith)
          have hu_back : (c k / π ^ 2 - Δ_of k u) * shellBeta1 / (c k) ^ (1 / 3 : ℝ) = u := by
            dsimp [Δ_of]; field_simp [hc13.ne', shellBeta1_pos.ne']; ring
          dsimp [q]; rw [hcut1, hmax, hu_back, hW_tail_left k u hu]; ring
        have hGnn : 0 ≤ D.normG u := div_nonneg (D.G_nonneg_left u hu) D.G_l1_pos.le
        have hrhs_nn : 0 ≤ 2 * q k (Δ_of k u) := by
          rw [h2q]
          exact mul_nonneg
            (mul_nonneg (div_nonneg (mul_nonneg zero_le_one shellBeta1_pos.le) (Real.rpow_nonneg (hc_pos k).le _)) hGnn)
            (inv_nonneg.mpr (shellRho0_nonneg (hc_pos k) (by linarith)))
        linarith
      have hsub_eq : p k (Δ_of k u) - q k (Δ_of k u) = (-2 + ε k) * q k (Δ_of k u) := by
        dsimp [p]; rw [abs_of_nonneg hq_nn]; ring
      have hε2 : -2 + ε k ≤ 0 := by dsimp [ε]; rw [add_comm]; linarith [show (1 : ℝ) / ((k : ℝ) + 10) ≤ 1 by rw [div_le_one (by positivity)]; linarith]
      rw [hsub_eq]
      exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg (Real.rpow_nonneg (hc_pos k).le _) shellBeta1_pos.le)
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hε2 hq_nn)
          (shellRho0_nonneg (hc_pos k) (by linarith))),
    fun k => (hf_int_zero k).le,
    Mtilde_hhat, Mtilde_h, Mtilde_f, E_strip,
    fun k σ _ => mul_pos (Real.rpow_pos_of_pos (div_pos (hM_hhat_pos k) (by linarith [hM_ge_half k])) _)
      (Real.rpow_pos_of_pos (by positivity) _),
    fun _ _ _ => rfl,
    fun k σ hσ => by
      dsimp [Mtilde_h, Mtilde_hhat, Mtilde_f]
      rcases lt_trichotomy σ (1 / 2) with hlt | heq | hgt
      · have hgt' : ¬ 1 - σ < 1 / 2 := by linarith
        rw [ite_eq_right_iff.mpr (fun h => absurd h hgt'),
          ite_eq_left_iff.mpr (fun hn => absurd hlt hn),
          ite_eq_left_iff.mpr (fun hn => absurd hlt hn)]
        have h11 : 1 - (1 - σ) = σ := by ring
        have hmin : min (1 - σ) (1 - (1 - σ)) = min σ (1 - σ) := by rw [h11, min_comm]
        simp only [L_val, hmin]; ring
      · rw [heq, show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num]
        simp only [lt_irrefl, ↓reduceIte, sub_zero]
      · have hnlt : ¬ σ < 1 / 2 := not_lt.mpr hgt.le
        have hlt' : 1 - σ < 1 / 2 := by linarith
        rw [ite_eq_left_iff.mpr (fun hn => absurd hlt' hn),
          ite_eq_right_iff.mpr (fun h => absurd h hnlt),
          ite_eq_right_iff.mpr (fun h => absurd h hnlt),
          ite_eq_left_iff.mpr (fun hn => absurd hgt hn)]
        have h11 : 1 - (1 - σ) = σ := by ring
        have hmin : min (1 - σ) (1 - (1 - σ)) = min σ (1 - σ) := by rw [h11, min_comm]
        simp only [L_val, hmin]; ring,
    fun k σ _ => by
      dsimp [Mtilde_f]
      rcases lt_trichotomy σ (1 / 2) with hlt | heq | hgt
      · have hgt' : 1 / 2 < 1 - σ := by linarith
        have hnlt' : ¬ 1 - σ < 1 / 2 := not_lt.mpr hgt'.le
        rw [ite_eq_right_iff.mpr (fun h => absurd h hnlt'),
          ite_eq_left_iff.mpr (fun hn => absurd hgt' hn),
          ite_eq_left_iff.mpr (fun hn => absurd hlt hn)]
        have h11 : 1 - (1 - σ) = σ := by ring
        have hmin : min (1 - σ) (1 - (1 - σ)) = min σ (1 - σ) := by rw [h11, min_comm]
        simp only [L_val, hmin, neg_neg]
      · rw [heq, show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num]
        simp only [lt_irrefl, ↓reduceIte, neg_zero]
      · have hnlt : ¬ σ < 1 / 2 := not_lt.mpr hgt.le
        have hlt' : 1 - σ < 1 / 2 := by linarith
        rw [ite_eq_left_iff.mpr (fun hn => absurd hlt' hn),
          ite_eq_right_iff.mpr (fun h => absurd h hnlt),
          ite_eq_left_iff.mpr (fun hn => absurd hgt hn)]
        have h11 : 1 - (1 - σ) = σ := by ring
        have hmin : min (1 - σ) (1 - (1 - σ)) = min σ (1 - σ) := by rw [h11, min_comm]
        simp only [L_val, hmin],
    fun k σ hσ => by
      dsimp [Mtilde_hhat]; split_ifs
      · exact mul_nonneg zero_le_two (hL_nn k σ hσ)
      · exact hL_nn k σ hσ,
    fun k σ hσ => by
      have hfpos : 0 < shellMass (c k) (fun Δ => 2 * q k Δ) := by linarith [hM_ge_half k]
      have hEst_eq : E_strip k σ * h0 k ^ (1 - σ) * shellMass (c k) (fun Δ => p k Δ + q k Δ) ^ σ =
          (2 * B + 1) * shellMass (c k) (fun Δ => 2 * q k Δ) := by
        dsimp [E_strip, h0]
        rw [Real.mul_rpow (by positivity) hfpos.le,
          Real.rpow_neg (div_nonneg (hM_hhat_pos k).le hfpos.le),
          Real.div_rpow (hM_hhat_pos k).le hfpos.le, inv_div]
        have h2B : (2 * B + 1) ^ σ * (2 * B + 1) ^ (1 - σ) = 2 * B + 1 := by
          rw [← Real.rpow_add (by positivity), add_sub_cancel, Real.rpow_one]
        have hMsplit : shellMass (c k) (fun Δ => 2 * q k Δ) ^ σ *
            shellMass (c k) (fun Δ => 2 * q k Δ) ^ (1 - σ) =
            shellMass (c k) (fun Δ => 2 * q k Δ) := by
          rw [← Real.rpow_add hfpos, add_sub_cancel, Real.rpow_one]
        have hm1 : shellMass (c k) (fun Δ => p k Δ + q k Δ) ^ σ ≠ 0 :=
          (Real.rpow_pos_of_pos (hM_hhat_pos k) _).ne'
        have hm2 : shellMass (c k) (fun Δ => 2 * q k Δ) ^ σ ≠ 0 :=
          (Real.rpow_pos_of_pos hfpos _).ne'
        calc ((shellMass (c k) (fun Δ => 2 * q k Δ) ^ σ /
                shellMass (c k) (fun Δ => p k Δ + q k Δ) ^ σ) * (2 * B + 1) ^ σ) *
              ((2 * B + 1) ^ (1 - σ) * shellMass (c k) (fun Δ => 2 * q k Δ) ^ (1 - σ)) *
              shellMass (c k) (fun Δ => p k Δ + q k Δ) ^ σ
            = ((2 * B + 1) ^ σ * (2 * B + 1) ^ (1 - σ)) *
              (shellMass (c k) (fun Δ => 2 * q k Δ) ^ σ * shellMass (c k) (fun Δ => 2 * q k Δ) ^ (1 - σ)) *
              (shellMass (c k) (fun Δ => p k Δ + q k Δ) ^ σ / shellMass (c k) (fun Δ => p k Δ + q k Δ) ^ σ) := by ring
          _ = (2 * B + 1) * shellMass (c k) (fun Δ => 2 * q k Δ) * 1 := by
              rw [h2B, hMsplit, div_self hm1]
          _ = _ := mul_one _
      rw [hEst_eq]
      have hLle : ∀ τ ∈ Ioo (0 : ℝ) 1, L_val k τ ≤ B * shellMass (c k) (fun Δ => 2 * q k Δ) := fun τ hτ => by
        dsimp [L_val]
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right
          (hB _ (mul_nonneg (mul_nonneg shellCs_pos.le (Real.rpow_nonneg (hc_pos k).le _))
            (le_min hτ.1.le (sub_nonneg.mpr hτ.2.le)))) hfpos.le
      dsimp [Mtilde_hhat]; split_ifs
      · linarith [hLle (1 - σ) ⟨sub_pos.mpr hσ.2, sub_lt_self 1 hσ.1⟩]
      · linarith [hLle (1 - σ) ⟨sub_pos.mpr hσ.2, sub_lt_self 1 hσ.1⟩, mul_pos hB_pos hfpos],
    id, strictMono_id, P_inf, Q_inf, D.G_inAiryClass.smul _, D.G_inAiryClass.smul _,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    have hQk_eq : ∀ k, shellWindowProfile (c k) (q k) u /
        shellMass (c k) (fun Δ => 2 * q k Δ) =
        ((1 / 2) * (χ k u * W k u)) / shellMass (c k) (fun Δ => 2 * q k Δ) := fun k => by
      have h2 : shellWindowProfile (c k) (fun Δ => 2 * q k Δ) u = 2 * shellWindowProfile (c k) (q k) u := by
        unfold shellWindowProfile; dsimp only; split_ifs <;> ring
      rw [(hW_eq k u).symm.trans h2]; ring
    have hPk_eq : ∀ k, shellWindowProfile (c k) (p k) u /
        shellMass (c k) (fun Δ => 2 * q k Δ) =
        -(shellWindowProfile (c k) (q k) u / shellMass (c k) (fun Δ => 2 * q k Δ)) +
          ε k * |shellWindowProfile (c k) (q k) u / shellMass (c k) (fun Δ => 2 * q k Δ)| := by
      intro k
      have hfpos : 0 < shellMass (c k) (fun Δ => 2 * q k Δ) := by linarith [hM_ge_half k]
      have h1 : shellWindowProfile (c k) (p k) u =
          -shellWindowProfile (c k) (q k) u + ε k * |shellWindowProfile (c k) (q k) u| := by
        unfold shellWindowProfile; dsimp only; split_ifs with h
        · have hc_nn : 0 ≤ (c k) ^ (1 / 3 : ℝ) / shellBeta1 :=
            div_nonneg (Real.rpow_nonneg (hc_pos k).le _) shellBeta1_pos.le
          have hr_nn : 0 ≤ shellRho0 (c k) (c k / π ^ 2 - u / shellBeta1 * (c k) ^ (1 / 3 : ℝ)) :=
            shellRho0_nonneg (hc_pos k) h.le
          rw [abs_mul, abs_of_nonneg hc_nn, abs_mul, abs_of_nonneg hr_nn]
          dsimp [p]; ring
        · simp
      rw [h1, add_div, neg_div, mul_div_assoc (ε k), abs_div, abs_of_pos hfpos]
    simp_rw [hPk_eq]
    have hQlim : Tendsto (fun k => shellWindowProfile (c k) (q k) u /
        shellMass (c k) (fun Δ => 2 * q k Δ)) atTop (𝓝 ((1 / 2) * D.normG u)) := by
      simp_rw [hQk_eq]
      have hWlim : Tendsto (fun k => χ k u * W k u) atTop (𝓝 (D.normG u)) := by
        have h1 : Tendsto (fun k => χ k u) atTop (𝓝 1) :=
          tendsto_const_nhds.congr' ((hχ_tend u).mono fun _ h => h.symm)
        have h2 : Tendsto (fun k => W k u) atTop (𝓝 (D.normG u)) := by
          simpa [W] using tendsto_const_nhds.sub (hδ_lim.mul_const (bumpN u))
        simpa using h1.mul h2
      have hdiv := (hWlim.const_mul (1 / 2)).div hM_lim one_ne_zero
      rw [div_one] at hdiv
      exact hdiv.congr (fun _ => rfl)
    have hεlim : Tendsto ε atTop (𝓝 0) := by
      dsimp [ε]
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hP_re : (P_inf (u : ℂ)).re = -((1 / 2) * D.normG u) := by
      dsimp [P_inf, ShellHBData.normG, D_l1]
      rw [Complex.re_ofReal_mul]; ring
    rw [hP_re]
    simpa using hQlim.neg.add (hεlim.mul hQlim.abs)
  · intro u
    have hQk_eq : ∀ k, shellWindowProfile (c k) (q k) u /
        shellMass (c k) (fun Δ => 2 * q k Δ) =
        ((1 / 2) * (χ k u * W k u)) / shellMass (c k) (fun Δ => 2 * q k Δ) := fun k => by
      have h2 : shellWindowProfile (c k) (fun Δ => 2 * q k Δ) u = 2 * shellWindowProfile (c k) (q k) u := by
        unfold shellWindowProfile; dsimp only; split_ifs <;> ring
      rw [(hW_eq k u).symm.trans h2]; ring
    simp_rw [hQk_eq]
    have hWlim : Tendsto (fun k => χ k u * W k u) atTop (𝓝 (D.normG u)) := by
      have h1 : Tendsto (fun k => χ k u) atTop (𝓝 1) :=
        tendsto_const_nhds.congr' ((hχ_tend u).mono fun _ h => h.symm)
      have h2 : Tendsto (fun k => W k u) atTop (𝓝 (D.normG u)) := by
        simpa [W] using tendsto_const_nhds.sub (hδ_lim.mul_const (bumpN u))
      simpa using h1.mul h2
    have hQ_re : (Q_inf (u : ℂ)).re = (1 / 2) * D.normG u := by
      dsimp [Q_inf, ShellHBData.normG, D_l1]
      rw [Complex.re_ofReal_mul]; ring
    rw [hQ_re]
    have hdiv := (hWlim.const_mul (1 / 2)).div hM_lim one_ne_zero
    rw [div_one] at hdiv
    exact hdiv.congr (fun _ => rfl)
  · obtain ⟨C_G, ν_G, hC_G, hb_G⟩ := D.G_env
    let ν₀ := max ν_G 0
    let C₀ := 3 * (C_G / D_l1 + 1 / ∫ x : ℝ, bump x)
    refine ⟨D.tm - 1, C₀, ν₀, le_rfl, by positivity, fun k u _ => ?_⟩
    have hfpos : 0 < shellMass (c k) (fun Δ => 2 * q k Δ) := by linarith [hM_ge_half k]
    have hQk_eq : shellWindowProfile (c k) (q k) u /
        shellMass (c k) (fun Δ => 2 * q k Δ) =
        ((1 / 2) * (χ k u * W k u)) / shellMass (c k) (fun Δ => 2 * q k Δ) := by
      have h2 : shellWindowProfile (c k) (fun Δ => 2 * q k Δ) u = 2 * shellWindowProfile (c k) (q k) u := by
        unfold shellWindowProfile; dsimp only; split_ifs <;> ring
      rw [(hW_eq k u).symm.trans h2]; ring
    have hPk_bd : |shellWindowProfile (c k) (p k) u / shellMass (c k) (fun Δ => 2 * q k Δ)| ≤
        2 * |shellWindowProfile (c k) (q k) u / shellMass (c k) (fun Δ => 2 * q k Δ)| := by
      have h1 : shellWindowProfile (c k) (p k) u =
          -shellWindowProfile (c k) (q k) u + ε k * |shellWindowProfile (c k) (q k) u| := by
        unfold shellWindowProfile; dsimp only; split_ifs with h
        · have hc_nn : 0 ≤ (c k) ^ (1 / 3 : ℝ) / shellBeta1 :=
            div_nonneg (Real.rpow_nonneg (hc_pos k).le _) shellBeta1_pos.le
          have hr_nn : 0 ≤ shellRho0 (c k) (c k / π ^ 2 - u / shellBeta1 * (c k) ^ (1 / 3 : ℝ)) :=
            shellRho0_nonneg (hc_pos k) h.le
          rw [abs_mul, abs_of_nonneg hc_nn, abs_mul, abs_of_nonneg hr_nn]
          dsimp [p]; ring
        · simp
      rw [h1, add_div, neg_div, mul_div_assoc (ε k)]
      have hdiv_abs : |shellWindowProfile (c k) (q k) u| / shellMass (c k) (fun Δ => 2 * q k Δ) =
          |shellWindowProfile (c k) (q k) u / shellMass (c k) (fun Δ => 2 * q k Δ)| := by
        rw [abs_div, abs_of_pos hfpos]
      rw [hdiv_abs]
      have hε1 : ε k ≤ 1 := by dsimp [ε]; rw [div_le_one (by positivity)]; linarith
      let t := shellWindowProfile (c k) (q k) u / shellMass (c k) (fun Δ => 2 * q k Δ)
      change abs (-t + ε k * |t|) ≤ 2 * |t|
      calc abs (-t + ε k * |t|) ≤ |-t| + abs (ε k * |t|) := abs_add_le _ _
        _ = |t| + ε k * |t| := by
            rw [abs_neg, abs_mul (ε k) |t|, abs_abs, abs_of_pos (by dsimp [ε]; positivity : 0 < ε k)]
        _ ≤ 2 * |t| := by nlinarith [abs_nonneg t]
    have hδ1 : |δ k| ≤ 1 := by
      have hle_abs : ∫ u : ℝ, |χ k u * D.normG u| ≤ 1 := by
        rw [← D.normG_abs_integral]
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) D.normG_integrable.abs
          (Eventually.of_forall fun x => ?_)
        dsimp only
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _)
          (abs_le.mpr ⟨by linarith [(hχ_bd k x).1], (hχ_bd k x).2⟩)
      have hmχ : AEStronglyMeasurable (fun u => χ k u) volume :=
        (Measurable.ite (measurableSet_lt measurable_const (by unfold Δ_of; fun_prop))
          (by unfold cut Δ_of; fun_prop) measurable_const).aestronglyMeasurable
      have hi1 : Integrable (fun u => χ k u * D.normG u) :=
        D.normG_integrable.abs.mono' (hmχ.mul D.normG_integrable.aestronglyMeasurable)
          (Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_of_le_one_left (abs_nonneg _)
              (abs_le.mpr ⟨by linarith [(hχ_bd k x).1], (hχ_bd k x).2⟩))
      exact (norm_integral_le_integral_norm (fun u => χ k u * D.normG u)).trans
        (by simpa [Real.norm_eq_abs] using hle_abs)
    have hQ_bd : |shellWindowProfile (c k) (q k) u / shellMass (c k) (fun Δ => 2 * q k Δ)| ≤
        |D.normG u| + bumpN u := by
      rw [hQk_eq, abs_div, abs_of_pos hfpos, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
        abs_mul]
      have hχ1 : |χ k u| ≤ 1 := abs_le.mpr ⟨by linarith [(hχ_bd k u).1], (hχ_bd k u).2⟩
      have hW1 : |W k u| ≤ |D.normG u| + bumpN u := by
        dsimp [W]
        calc |D.normG u - δ k * bumpN u| ≤ |D.normG u| + |δ k * bumpN u| := abs_sub _ _
          _ = |D.normG u| + |δ k| * bumpN u := by
              rw [abs_mul, abs_of_nonneg (div_nonneg (hbump_nn u) hbump_pos.le)]
          _ ≤ |D.normG u| + 1 * bumpN u := by gcongr
          _ = _ := by ring
      have hM : (1 / 2 : ℝ) ≤ shellMass (c k) (fun Δ => 2 * q k Δ) := hM_ge_half k
      calc (1 / 2 : ℝ) * (|χ k u| * |W k u|) / shellMass (c k) (fun Δ => 2 * q k Δ)
          ≤ (1 / 2) * (1 * (|D.normG u| + bumpN u)) / (1 / 2) := by gcongr
        _ = |D.normG u| + bumpN u := by ring
    have hnorm_env : |D.normG u| ≤ (C_G / D_l1) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) := by
      have hG := hb_G (u : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at hG
      have hre : |(D.G (u : ℂ)).re| ≤ ‖D.G (u : ℂ)‖ := Complex.abs_re_le_norm _
      have hp : (1 + |u|) ^ ν_G ≤ (1 + |u|) ^ ν₀ :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg u]) (le_max_left _ _)
      have he : 0 ≤ airyEnv (u : ℂ) := (airyEnv_pos _).le
      unfold ShellHBData.normG; change |(D.G (u : ℂ)).re / D_l1| ≤ _
      rw [abs_div, abs_of_pos D.G_l1_pos]
      calc |(D.G (u : ℂ)).re| / D_l1 ≤ (C_G * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ)) / D_l1 :=
            div_le_div_of_nonneg_right (hre.trans (hG.trans (by gcongr))) D.G_l1_pos.le
        _ = (C_G / D_l1) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) := by ring
    have hbump_env : bumpN u ≤ (1 / ∫ x : ℝ, bump x) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) := by
      by_cases hu0 : u < 0
      · have hb1 : bump u ≤ 1 := by
          dsimp [bump]; exact max_le (by norm_num) (by linarith [abs_nonneg (u + 1)])
        have he1 : airyEnv (u : ℂ) = 1 := airyEnv_ofReal_neg hu0
        have hp1 : 1 ≤ (1 + |u|) ^ ν₀ :=
          Real.one_le_rpow (by linarith [abs_nonneg u]) (le_max_right _ _)
        dsimp [bumpN]
        calc bump u / ∫ x : ℝ, bump x ≤ 1 / ∫ x : ℝ, bump x :=
              div_le_div_of_nonneg_right hb1 hbump_pos.le
          _ ≤ (1 / ∫ x : ℝ, bump x) * (1 + |u|) ^ ν₀ * 1 := by
              rw [mul_one]; exact le_mul_of_one_le_right (by positivity) hp1
          _ = (1 / ∫ x : ℝ, bump x) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) := by rw [he1]
      · push Not at hu0
        have hb0 : bump u = 0 := by
          dsimp [bump]; rw [abs_of_nonneg (by linarith)]; exact max_eq_left (by linarith)
        dsimp [bumpN]; rw [hb0, zero_div]
        exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith [abs_nonneg u]) _))
          (airyEnv_pos _).le
    calc |shellWindowProfile (c k) (p k) u / shellMass (c k) (fun Δ => 2 * q k Δ)| +
          |shellWindowProfile (c k) (q k) u / shellMass (c k) (fun Δ => 2 * q k Δ)|
        ≤ 3 * |shellWindowProfile (c k) (q k) u / shellMass (c k) (fun Δ => 2 * q k Δ)| := by linarith [hPk_bd]
      _ ≤ 3 * (|D.normG u| + bumpN u) := by linarith [hQ_bd]
      _ ≤ 3 * ((C_G / D_l1) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) +
          (1 / ∫ x : ℝ, bump x) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ)) := by gcongr
      _ = C₀ * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) := by dsimp [C₀]; ring
  · intro y hy
    let σ : ℕ → ℝ := fun k => (y / shellCs) * (c k) ^ (-(1 / 3 : ℝ))
    have hσ_tend : Tendsto σ atTop (𝓝 0) := by
      simpa [σ] using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hc_tend).const_mul _
    have hE_inv_lim : Tendsto (fun k => (E_strip k (σ k))⁻¹) atTop (𝓝 1) := hE_inv_lim_of y hy
    have hconst : ∀ᶠ k in atTop,
        (E_strip k (σ k))⁻¹ * Mtilde_f k (1 - σ k) / shellMass (c k) (fun Δ => 2 * q k Δ) =
          (E_strip k (σ k))⁻¹ * airyLaplace (fun u => 2 * (Q_inf (u : ℂ)).re) y := by
      filter_upwards [hσ_tend.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with k hk
      have hgt : 1 / 2 < 1 - σ k := by linarith
      have hnlt : ¬ 1 - σ k < 1 / 2 := not_lt.mpr hgt.le
      have hmin : min (1 - σ k) (1 - (1 - σ k)) = σ k := by
        rw [show 1 - (1 - σ k) = σ k by ring, min_eq_right (by linarith)]
      have hy_eq : shellCs * (c k) ^ (1 / 3 : ℝ) * σ k = y := by
        dsimp [σ]
        have hinv : (c k) ^ (1 / 3 : ℝ) * (c k) ^ (-(1 / 3 : ℝ)) = 1 := by
          rw [← Real.rpow_add (hc_pos k)]; simp
        calc shellCs * (c k) ^ (1 / 3 : ℝ) * (y / shellCs * (c k) ^ (-(1 / 3 : ℝ)))
            = (shellCs * (y / shellCs)) * ((c k) ^ (1 / 3 : ℝ) * (c k) ^ (-(1 / 3 : ℝ))) := by ring
          _ = y * 1 := by rw [hinv, mul_div_cancel₀ _ shellCs_pos.ne']
          _ = y := mul_one y
      have hQ2_norm : (fun u : ℝ => 2 * (Q_inf (u : ℂ)).re) = D.normG := by
        ext u; dsimp [Q_inf, ShellHBData.normG, D_l1]; rw [Complex.re_ofReal_mul]; ring
      have hL_neg : airyLaplace (fun u => -D.normG u) y = -airyLaplace D.normG y := by
        unfold airyLaplace; simp_rw [neg_mul]; rw [integral_neg, mul_neg]
      have hfpos : 0 < shellMass (c k) (fun Δ => 2 * q k Δ) := by linarith [hM_ge_half k]
      dsimp [Mtilde_f, L_val]
      rw [ite_eq_right_iff.mpr (fun h => absurd h hnlt),
        ite_eq_left_iff.mpr (fun hn => absurd hgt hn), hmin, hy_eq, hQ2_norm, hL_neg]
      field_simp [hfpos.ne']
    simpa only [one_mul, id_eq] using
      (hE_inv_lim.mul_const (airyLaplace (fun u => 2 * (Q_inf (u : ℂ)).re) y)).congr'
        (hconst.mono fun _ h => h.symm)
  · intro y hy
    let σ : ℕ → ℝ := fun k => (y / shellCs) * (c k) ^ (-(1 / 3 : ℝ))
    have hσ_tend : Tendsto σ atTop (𝓝 0) := by
      simpa [σ] using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hc_tend).const_mul _
    have hE_inv_lim : Tendsto (fun k => (E_strip k (σ k))⁻¹) atTop (𝓝 1) := hE_inv_lim_of y hy
    have hconst : ∀ᶠ k in atTop,
        (E_strip k (σ k))⁻¹ * Mtilde_h k (σ k) / shellMass (c k) (fun Δ => 2 * q k Δ) =
          (E_strip k (σ k))⁻¹ * airyLaplace (fun u => (P_inf (u : ℂ) - Q_inf (u : ℂ)).re) y := by
      filter_upwards [hσ_tend.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with k hk
      have hnlt : ¬ 1 - σ k < 1 / 2 := not_lt.mpr (by linarith)
      have hmin : min (1 - σ k) (1 - (1 - σ k)) = σ k := by
        rw [show 1 - (1 - σ k) = σ k by ring, min_eq_right (by linarith)]
      have hy_eq : shellCs * (c k) ^ (1 / 3 : ℝ) * σ k = y := by
        dsimp [σ]
        have hinv : (c k) ^ (1 / 3 : ℝ) * (c k) ^ (-(1 / 3 : ℝ)) = 1 := by
          rw [← Real.rpow_add (hc_pos k)]; simp
        calc shellCs * (c k) ^ (1 / 3 : ℝ) * (y / shellCs * (c k) ^ (-(1 / 3 : ℝ)))
            = (shellCs * (y / shellCs)) * ((c k) ^ (1 / 3 : ℝ) * (c k) ^ (-(1 / 3 : ℝ))) := by ring
          _ = y * 1 := by rw [hinv, mul_div_cancel₀ _ shellCs_pos.ne']
          _ = y := mul_one y
      have hH_norm : (fun u : ℝ => (P_inf (u : ℂ)).re - (Q_inf (u : ℂ)).re) = fun u => -D.normG u := by
        ext u; dsimp [P_inf, Q_inf, ShellHBData.normG, D_l1]
        rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul]; ring
      have hfpos : 0 < shellMass (c k) (fun Δ => 2 * q k Δ) := by linarith [hM_ge_half k]
      dsimp [Mtilde_h, Mtilde_hhat, L_val]
      rw [ite_eq_right_iff.mpr (fun h => absurd h hnlt), hmin, hy_eq, hH_norm]
      field_simp [hfpos.ne']
    simpa only [one_mul, id_eq] using
      (hE_inv_lim.mul_const (airyLaplace (fun u => (P_inf (u : ℂ) - Q_inf (u : ℂ)).re) y)).congr'
        (hconst.mono fun _ h => h.symm)

/-- Explicit non-vacuity witness for `ShellReductionPackage`, projected from
`shellGapPackage_nonvacuous`. -/
noncomputable def shellReductionPackage_nonvacuous : ShellReductionPackage :=
  shellGapPackage_nonvacuous.toShellReductionPackage


/-- info: 'FormalResearch.SignUncertainty.airyLaplace_airy_normG_bdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyLaplace_airy_normG_bdd

/-- info: 'FormalResearch.SignUncertainty.shellGapPackage_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shellGapPackage_nonvacuous

/-- info: 'FormalResearch.SignUncertainty.shellReductionPackage_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shellReductionPackage_nonvacuous

end FormalResearch.SignUncertainty
