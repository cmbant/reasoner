module

public import FormalResearch.SignUncertainty.FineOrderSignedMain

/-!
# Shared signed half-cubic reduction (`fs:half-cubic`): Part (3) Airy pairing

Source: `CFT/common/fine_order_signed.tex`, Lemma FS.1 (`fs:half-cubic`), pairing assertion
`(fs:pairing)`. Phase-free; shared between Paper I (`SignUncertainty`) and Paper II (`ModularBootstrap`).
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.SignUncertainty.FineOrderSigned

open FormalResearch.Special FormalResearch.SignUncertainty CtSd CtAiryHplus HalfCubicInternal

private lemma continuous_fsJ_K_Kp :
    Continuous fsJ ∧ Continuous fsK ∧ Continuous fsKp := by
  have hcAi : Continuous airyAi :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_airyAi x).continuousAt
  have hcAi' : Continuous airyAi' :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_airyAi' x).continuousAt
  have hcBi : Continuous airyBi :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_airyBi x).continuousAt
  have hcBi' : Continuous airyBiDeriv :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_airyBiDeriv x).continuousAt
  refine ⟨hcAi.mul hcBi, continuous_iff_continuousAt.2 fun x => (hasDerivAt_fsK x).continuousAt, ?_⟩
  unfold fsKp
  exact continuous_const.mul (((continuous_const.mul hcAi').mul hcBi').add
    ((continuous_const.mul continuous_id).mul (hcAi.mul hcBi)))

private lemma continuousOn_re_real {f : ℂ → ℂ} {R ρ : ℝ} (hRρ : R < ρ)
    (hf : DifferentiableOn ℂ f (ball 0 ρ)) :
    ContinuousOn (fun x : ℝ => (f (x : ℂ)).re) (Icc (-R) R) :=
  Complex.continuous_re.continuousOn.comp
    (hf.continuousOn.comp Complex.continuous_ofReal.continuousOn fun x hx => by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact (abs_le.2 hx).trans_lt hRρ) (mapsTo_univ _ _)

/-- General Airy pairing bound on `[-R, R]` (`R ≍ n^{2/3}`) against real-symmetric holomorphic
weights `b` and error term bounded by `E_bd`. -/
theorem fs_pairing_coeffs {F b cJ cK cKp : ℂ → ℂ} {err : ℝ → ℝ}
    {n R ρ cl cu Bn MJ MK MKp MF E_bd : ℝ}
    (hn : 1 ≤ n) (hR : 1 ≤ R) (hRρ : R < ρ)
    (hcl : 0 < cl) (hR_lo : cl * n ^ (2 / 3 : ℝ) ≤ R) (hR_hi : R ≤ cu * n ^ (2 / 3 : ℝ))
    (hBn : 0 ≤ Bn) (hMJ : 0 ≤ MJ) (hMK : 0 ≤ MK) (hMKp : 0 ≤ MKp) (hEb : 0 ≤ E_bd)
    (hF_d : DifferentiableOn ℂ F (ball 0 ρ)) (hb_d : DifferentiableOn ℂ b (ball 0 ρ))
    (hcJ_d : DifferentiableOn ℂ cJ (ball 0 ρ)) (hcK_d : DifferentiableOn ℂ cK (ball 0 ρ))
    (hcKp_d : DifferentiableOn ℂ cKp (ball 0 ρ))
    (hF_real : ∀ x : ℝ, |x| ≤ R → (F (x : ℂ)).im = 0)
    (hb_real : ∀ x : ℝ, |x| ≤ R → (b (x : ℂ)).im = 0)
    (hcJ_real : ∀ x : ℝ, |x| ≤ R → (cJ (x : ℂ)).im = 0)
    (hcK_real : ∀ x : ℝ, |x| ≤ R → (cK (x : ℂ)).im = 0)
    (hcKp_real : ∀ x : ℝ, |x| ≤ R → (cKp (x : ℂ)).im = 0)
    (hb_bd : ∀ z ∈ closedBall (0 : ℂ) R, ‖b z‖ ≤ Bn)
    (hcJ_bd : ∀ θ ∈ Icc (0 : ℝ) π, ‖cJ (circleMap 0 R θ)‖ ≤ MJ)
    (hcK_bd : ∀ θ ∈ Icc (0 : ℝ) π, ‖cK (circleMap 0 R θ)‖ ≤ MK)
    (hcKp_bd : ∀ θ ∈ Icc (0 : ℝ) π, ‖cKp (circleMap 0 R θ)‖ ≤ MKp)
    (hMF : ∫ x in (-R)..R, ‖F (x : ℂ)‖ ≤ MF)
    (herr : ∀ x : ℝ, x ∈ Icc (-R) R → |err x| ≤ E_bd)
    (herr_int : IntervalIntegrable (fun x : ℝ => (F (x : ℂ)).re * (b (x : ℂ)).re * err x) volume (-R) R) :
    |∫ x in (-R)..R, (F (x : ℂ)).re * (b (x : ℂ)).re *
      (n⁻¹ * (cK (x : ℂ)).re * fsK x + n ^ (-(2 / 3 : ℝ)) * (cJ (x : ℂ)).re * fsJ x +
        n ^ (-(4 / 3 : ℝ)) * (cKp (x : ℂ)).re * fsKp x + err x)| ≤
      Bn * ((12 * MK + (5 / (2 * π)) * cl ^ (-(1 / 2 : ℝ)) * MJ +
        32 * cu ^ (1 / 2 : ℝ) * MKp) * n⁻¹ *
          ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) +
        E_bd * MF) := by
  have hn0 : 0 < n := by linarith
  have hR0 : 0 < R := by linarith
  have hcu0 : 0 ≤ cu :=
    nonneg_of_mul_nonneg_left (by linarith [mul_pos hcl (Real.rpow_pos_of_pos hn0 (2 / 3 : ℝ))])
      (Real.rpow_pos_of_pos hn0 _)
  have ηpos : 0 ≤ ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) :=
    intervalIntegral.integral_nonneg Real.pi_pos.le fun θ _ =>
      div_nonneg (mul_nonneg hR0.le (norm_nonneg _)) (Real.exp_pos _).le
  have hpair_J := fs_pairing_0 (d := fun z => b z * cJ z) hR hRρ hF_d (hb_d.mul hcJ_d)
    hF_real (fun x hx => by simp [hb_real x hx, hcJ_real x hx])
    (fun θ hθ => by
      have hm := hb_bd (circleMap 0 R θ) (mem_closedBall_zero_iff.2 (by simp [abs_of_pos hR0]))
      rw [norm_mul]; exact mul_le_mul hm (hcJ_bd θ hθ) (norm_nonneg _) hBn)
    (mul_nonneg hBn hMJ)
  have hpair_K := fs_pairing_1 (d := fun z => b z * cK z) hR hRρ hF_d (hb_d.mul hcK_d)
    hF_real (fun x hx => by simp [hb_real x hx, hcK_real x hx])
    (fun θ hθ => by
      have hm := hb_bd (circleMap 0 R θ) (mem_closedBall_zero_iff.2 (by simp [abs_of_pos hR0]))
      rw [norm_mul]; exact mul_le_mul hm (hcK_bd θ hθ) (norm_nonneg _) hBn)
    (mul_nonneg hBn hMK)
  have hpair_Kp := fs_pairing_2 (d := fun z => b z * cKp z) hR hRρ hF_d (hb_d.mul hcKp_d)
    hF_real (fun x hx => by simp [hb_real x hx, hcKp_real x hx])
    (fun θ hθ => by
      have hm := hb_bd (circleMap 0 R θ) (mem_closedBall_zero_iff.2 (by simp [abs_of_pos hR0]))
      rw [norm_mul]; exact mul_le_mul hm (hcKp_bd θ hθ) (norm_nonneg _) hBn)
    (mul_nonneg hBn hMKp)
  have hre_prod : ∀ (c : ℂ → ℂ), (∀ x : ℝ, |x| ≤ R → (c (x : ℂ)).im = 0) →
      ∀ x ∈ Icc (-R) R, (b x * c x).re = (b x).re * (c x).re := fun c hc x hx => by
    have hax : |x| ≤ R := abs_le.2 hx
    simp [Complex.mul_re, hb_real x hax, hc x hax]
  obtain ⟨hfsJ_c, hfsK_c, hfsKp_c⟩ := continuous_fsJ_K_Kp
  have hF_c := continuousOn_re_real hRρ hF_d
  have hb_c := continuousOn_re_real hRρ hb_d
  have hcK_c := continuousOn_re_real hRρ hcK_d
  have hcJ_c := continuousOn_re_real hRρ hcJ_d
  have hcKp_c := continuousOn_re_real hRρ hcKp_d
  have hle_R : -R ≤ R := by linarith
  have hi_K : IntervalIntegrable (fun x : ℝ =>
      n⁻¹ * ((F (x : ℂ)).re * (b x * cK x).re * fsK x)) volume (-R) R :=
    (((hF_c.mul ((hb_c.mul hcK_c).congr (fun x hx => hre_prod cK hcK_real x hx))).mul
      hfsK_c.continuousOn).const_mul _).intervalIntegrable_of_Icc hle_R
  have hi_J : IntervalIntegrable (fun x : ℝ =>
      n ^ (-(2 / 3 : ℝ)) * ((F (x : ℂ)).re * (b x * cJ x).re * fsJ x)) volume (-R) R :=
    (((hF_c.mul ((hb_c.mul hcJ_c).congr (fun x hx => hre_prod cJ hcJ_real x hx))).mul
      hfsJ_c.continuousOn).const_mul _).intervalIntegrable_of_Icc hle_R
  have hi_Kp : IntervalIntegrable (fun x : ℝ =>
      n ^ (-(4 / 3 : ℝ)) * ((F (x : ℂ)).re * (b x * cKp x).re * fsKp x)) volume (-R) R :=
    (((hF_c.mul ((hb_c.mul hcKp_c).congr (fun x hx => hre_prod cKp hcKp_real x hx))).mul
      hfsKp_c.continuousOn).const_mul _).intervalIntegrable_of_Icc hle_R
  have hcongr_main : ∫ x in (-R)..R, (F (x : ℂ)).re * (b (x : ℂ)).re *
      (n⁻¹ * (cK (x : ℂ)).re * fsK x + n ^ (-(2 / 3 : ℝ)) * (cJ (x : ℂ)).re * fsJ x +
        n ^ (-(4 / 3 : ℝ)) * (cKp (x : ℂ)).re * fsKp x + err x) =
      (∫ x in (-R)..R, n⁻¹ * ((F (x : ℂ)).re * (b x * cK x).re * fsK x)) +
      (∫ x in (-R)..R, n ^ (-(2 / 3 : ℝ)) * ((F (x : ℂ)).re * (b x * cJ x).re * fsJ x)) +
      (∫ x in (-R)..R, n ^ (-(4 / 3 : ℝ)) * ((F (x : ℂ)).re * (b x * cKp x).re * fsKp x)) +
      (∫ x in (-R)..R, (F (x : ℂ)).re * (b (x : ℂ)).re * err x) := by
    have hpoint : EqOn (fun x : ℝ => (F (x : ℂ)).re * (b (x : ℂ)).re *
          (n⁻¹ * (cK (x : ℂ)).re * fsK x + n ^ (-(2 / 3 : ℝ)) * (cJ (x : ℂ)).re * fsJ x +
            n ^ (-(4 / 3 : ℝ)) * (cKp (x : ℂ)).re * fsKp x + err x))
        (fun x : ℝ => n⁻¹ * ((F (x : ℂ)).re * (b x * cK x).re * fsK x) +
          n ^ (-(2 / 3 : ℝ)) * ((F (x : ℂ)).re * (b x * cJ x).re * fsJ x) +
          n ^ (-(4 / 3 : ℝ)) * ((F (x : ℂ)).re * (b x * cKp x).re * fsKp x) +
          (F (x : ℂ)).re * (b (x : ℂ)).re * err x) (uIcc (-R) R) := by
      intro x hx
      rw [uIcc_of_le hle_R] at hx
      rw [hre_prod cK hcK_real x hx, hre_prod cJ hcJ_real x hx, hre_prod cKp hcKp_real x hx]
      ring
    rw [intervalIntegral.integral_congr hpoint,
      intervalIntegral.integral_add ((hi_K.add hi_J).add hi_Kp) herr_int,
      intervalIntegral.integral_add (hi_K.add hi_J) hi_Kp,
      intervalIntegral.integral_add hi_K hi_J]
  have hbd_K : |∫ x in (-R)..R, n⁻¹ * ((F (x : ℂ)).re * (b x * cK x).re * fsK x)| ≤
      Bn * (12 * MK * n⁻¹ *
        ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ)) := by
    rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_pos (inv_pos.2 hn0)]
    calc n⁻¹ * |∫ x in (-R)..R, (F (x : ℂ)).re * (b x * cK x).re * fsK x|
        ≤ n⁻¹ * (12 * (Bn * MK) *
            ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ)) :=
          mul_le_mul_of_nonneg_left hpair_K (by positivity)
      _ = _ := by ring
  have hbd_J : |∫ x in (-R)..R, n ^ (-(2 / 3 : ℝ)) * ((F (x : ℂ)).re * (b x * cJ x).re * fsJ x)| ≤
      Bn * ((5 / (2 * π)) * cl ^ (-(1 / 2 : ℝ)) * MJ * n⁻¹ *
        ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ)) := by
    have hRm : R ^ (-(1 / 2 : ℝ)) ≤ cl ^ (-(1 / 2 : ℝ)) * n ^ (-(1 / 3 : ℝ)) := by
      have h1 := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < cl * n ^ (2 / 3 : ℝ)) hR_lo (by norm_num)
      rw [Real.mul_rpow hcl.le (Real.rpow_nonneg hn0.le _), ← Real.rpow_mul hn0.le] at h1
      simpa [show (2 / 3 : ℝ) * -(1 / 2 : ℝ) = -(1 / 3 : ℝ) by norm_num] using h1
    have hpow_n : n ^ (-(2 / 3 : ℝ)) * n ^ (-(1 / 3 : ℝ)) = n⁻¹ := by
      rw [← Real.rpow_add hn0, ← Real.rpow_neg_one]; congr 1; norm_num
    rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
    calc n ^ (-(2 / 3 : ℝ)) * |∫ x in (-R)..R, (F (x : ℂ)).re * (b x * cJ x).re * fsJ x|
        ≤ n ^ (-(2 / 3 : ℝ)) * ((5 / (2 * π)) * (Bn * MJ) * R ^ (-(1 / 2 : ℝ)) *
            ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ)) :=
          mul_le_mul_of_nonneg_left hpair_J (by positivity)
      _ ≤ n ^ (-(2 / 3 : ℝ)) * ((5 / (2 * π)) * (Bn * MJ) *
            (cl ^ (-(1 / 2 : ℝ)) * n ^ (-(1 / 3 : ℝ))) *
            ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ)) := by gcongr
      _ = Bn * ((5 / (2 * π)) * cl ^ (-(1 / 2 : ℝ)) * MJ * (n ^ (-(2 / 3 : ℝ)) * n ^ (-(1 / 3 : ℝ))) *
            ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ)) := by ring
      _ = _ := by rw [hpow_n]
  have hbd_Kp : |∫ x in (-R)..R, n ^ (-(4 / 3 : ℝ)) * ((F (x : ℂ)).re * (b x * cKp x).re * fsKp x)| ≤
      Bn * (32 * cu ^ (1 / 2 : ℝ) * MKp * n⁻¹ *
        ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ)) := by
    have hRp : R ^ (1 / 2 : ℝ) ≤ cu ^ (1 / 2 : ℝ) * n ^ (1 / 3 : ℝ) := by
      have h1 := Real.rpow_le_rpow hR0.le hR_hi (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rw [Real.mul_rpow hcu0 (Real.rpow_nonneg hn0.le _), ← Real.rpow_mul hn0.le] at h1
      simpa [show (2 / 3 : ℝ) * (1 / 2 : ℝ) = 1 / 3 by norm_num] using h1
    have hpow_n : n ^ (-(4 / 3 : ℝ)) * n ^ (1 / 3 : ℝ) = n⁻¹ := by
      rw [← Real.rpow_add hn0, ← Real.rpow_neg_one]; congr 1; norm_num
    rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
    calc n ^ (-(4 / 3 : ℝ)) * |∫ x in (-R)..R, (F (x : ℂ)).re * (b x * cKp x).re * fsKp x|
        ≤ n ^ (-(4 / 3 : ℝ)) * (32 * (Bn * MKp) * R ^ (1 / 2 : ℝ) *
            ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ)) :=
          mul_le_mul_of_nonneg_left hpair_Kp (by positivity)
      _ ≤ n ^ (-(4 / 3 : ℝ)) * (32 * (Bn * MKp) * (cu ^ (1 / 2 : ℝ) * n ^ (1 / 3 : ℝ)) *
            ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ)) := by gcongr
      _ = Bn * (32 * cu ^ (1 / 2 : ℝ) * MKp * (n ^ (-(4 / 3 : ℝ)) * n ^ (1 / 3 : ℝ)) *
            ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ)) := by ring
      _ = _ := by rw [hpow_n]
  have hbd_err : |∫ x in (-R)..R, (F (x : ℂ)).re * (b (x : ℂ)).re * err x| ≤ Bn * (E_bd * MF) := by
    have hF_n_int : IntervalIntegrable (fun x : ℝ => Bn * E_bd * ‖F (x : ℂ)‖) volume (-R) R :=
      ((Complex.continuous_norm.comp (hF_d.continuousOn.comp Complex.continuous_ofReal.continuousOn
        fun x hx => by
          rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
          exact (abs_le.2 hx).trans_lt hRρ)).const_mul _).intervalIntegrable_of_Icc hle_R
    have hmono := intervalIntegral.integral_mono_on hle_R herr_int.norm hF_n_int fun x hx => by
      have hbx : ‖b (x : ℂ)‖ ≤ Bn := hb_bd x (mem_closedBall_zero_iff.2 (by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_le.2 hx))
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |(F (x : ℂ)).re| * |(b (x : ℂ)).re| * |err x|
          ≤ ‖F (x : ℂ)‖ * ‖b (x : ℂ)‖ * E_bd :=
            mul_le_mul (mul_le_mul (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)
              (abs_nonneg _) (norm_nonneg _)) (herr x hx) (abs_nonneg _) (by positivity)
        _ ≤ ‖F (x : ℂ)‖ * Bn * E_bd := by gcongr
        _ = Bn * E_bd * ‖F (x : ℂ)‖ := by ring
    calc |∫ x in (-R)..R, (F (x : ℂ)).re * (b (x : ℂ)).re * err x|
        ≤ ∫ x in (-R)..R, ‖(F (x : ℂ)).re * (b (x : ℂ)).re * err x‖ :=
          intervalIntegral.norm_integral_le_integral_norm hle_R
      _ ≤ ∫ x in (-R)..R, Bn * E_bd * ‖F (x : ℂ)‖ := hmono
      _ = Bn * E_bd * ∫ x in (-R)..R, ‖F (x : ℂ)‖ := intervalIntegral.integral_const_mul _ _
      _ ≤ Bn * E_bd * MF := by gcongr
      _ = Bn * (E_bd * MF) := by ring
  rw [hcongr_main]
  refine (norm_add₄_le _ _ _ _).trans ?_
  calc |∫ x in (-R)..R, n⁻¹ * ((F (x : ℂ)).re * (b x * cK x).re * fsK x)| +
        |∫ x in (-R)..R, n ^ (-(2 / 3 : ℝ)) * ((F (x : ℂ)).re * (b x * cJ x).re * fsJ x)| +
        |∫ x in (-R)..R, n ^ (-(4 / 3 : ℝ)) * ((F (x : ℂ)).re * (b x * cKp x).re * fsKp x)| +
        |∫ x in (-R)..R, (F (x : ℂ)).re * (b (x : ℂ)).re * err x|
      ≤ Bn * (12 * MK * n⁻¹ * ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ)) +
        Bn * ((5 / (2 * π)) * cl ^ (-(1 / 2 : ℝ)) * MJ * n⁻¹ *
          ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ)) +
        Bn * (32 * cu ^ (1 / 2 : ℝ) * MKp * n⁻¹ *
          ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ)) +
        Bn * (E_bd * MF) := add_le_add_four hbd_K hbd_J hbd_Kp hbd_err
    _ = _ := by ring

/-- **Lemma FS.1 Part (3) (`fs:pairing`), principal form**: pairing `L(u) - K(u)` (where `L` is
within `O(n^{-3/2})` of `L_u[B_n]` — take `C_ext = 0` for no external tail) against `F b`. -/
theorem fs_pairing_principal (d : HalfCubicData) {K_E K_O : ℝ} (hKE : 0 ≤ K_E) (hKO : 0 ≤ K_O)
    (hEnorm : ∀ n a, 1 ≤ n → a ∈ ball (0 : ℂ) d.r_a → ‖d.E n (-a) a - 1‖ ≤ K_E * n⁻¹)
    (hOnorm : ∀ n a, 1 ≤ n → a ∈ ball (0 : ℂ) d.r_a → ‖d.O n (-a) a‖ ≤ K_O * n⁻¹)
    {cl cu C_ext : ℝ} (hcl : 0 < cl) (hCext : 0 ≤ C_ext) :
    ∃ C_eta C_rem : ℝ, 0 ≤ C_eta ∧ 0 ≤ C_rem ∧
      ∀ {n R ρ Bn MF : ℝ} {F b aInv : ℂ → ℂ} {L : ℝ → ℝ},
        d.n₀ ≤ n → 1 ≤ R → R < ρ →
        cl * n ^ (2 / 3 : ℝ) ≤ R → R ≤ cu * n ^ (2 / 3 : ℝ) → 0 ≤ Bn →
        DifferentiableOn ℂ F (ball 0 ρ) → DifferentiableOn ℂ b (ball 0 ρ) →
        DifferentiableOn ℂ aInv (ball 0 ρ) →
        (∀ z ∈ ball (0 : ℂ) ρ, aInv z ∈ ball (0 : ℂ) d.rAShrunk) →
        (∀ x : ℝ, |x| ≤ R → (F (x : ℂ)).im = 0) →
        (∀ x : ℝ, |x| ≤ R → (b (x : ℂ)).im = 0) →
        (∀ x : ℝ, |x| ≤ R → (aInv (x : ℂ)).im = 0) →
        (∀ x : ℝ, |x| ≤ R → d.uReal n (aInv (x : ℂ)).re = x) →
        (∀ z ∈ closedBall (0 : ℂ) R, ‖b z‖ ≤ Bn) →
        (∫ x in (-R)..R, ‖F (x : ℂ)‖ ≤ MF) →
        (∀ x : ℝ, |x| ≤ R →
          let lam := n ^ (-(1 / 3 : ℝ))
          let R_c := d.s₁ / lam
          let R₀ := Rs d / lam
          let ax := (aInv (x : ℂ)).re
          ∀ (hR1 : 1 ≤ R_c) (hRR : R_c < R₀) (hUR : kap * |d.uReal n ax| ≤ R_c ^ 2 / 16),
          |L x - fsOpCh (fsChain hR1 hRR hUR) (d.uReal n ax)
            (fun w => d.B n ax ((lam : ℂ) * w))| ≤ C_ext * n ^ (-(3 / 2 : ℝ))) →
        IntervalIntegrable (fun x : ℝ => (F (x : ℂ)).re * (b (x : ℂ)).re * (L x - fsK x)) volume (-R) R →
        |∫ x in (-R)..R, (F (x : ℂ)).re * (b (x : ℂ)).re * (L x - fsK x)| ≤
          Bn * (C_eta * n⁻¹ * ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) +
            (C_rem * n ^ (-(5 / 3 : ℝ)) + C_ext * n ^ (-(3 / 2 : ℝ))) * MF) := by
  obtain ⟨M_C, M_Q, M_T, C_rem, hMC, hMQ, hMT, hCrem, hpr⟩ :=
    fs_principal d hKE hKO hEnorm hOnorm
  set cu' := max cu 0
  set C_eta : ℝ := 12 * M_C + (5 / (2 * π)) * cl ^ (-(1 / 2 : ℝ)) * M_Q +
    32 * cu' ^ (1 / 2 : ℝ) * M_T
  refine ⟨C_eta, C_rem, by dsimp [C_eta]; positivity, hCrem, ?_⟩
  intro n R ρ Bn MF F b aInv L hn hR1 hRρ hRlo hRhi hBn hF_d hb_d ha_d ha_in
    hF_r hb_r ha_r hu_eq hb_bd hMF hL_close hL_int
  have hn1 : 1 ≤ n := d.n₀_ge_one.trans hn
  have hn0 : 0 < n := by linarith
  have hR0 : 0 < R := by linarith
  have hRhi' : R ≤ cu' * n ^ (2 / 3 : ℝ) :=
    hRhi.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  obtain ⟨hCn_d, hQn_d, hTn_d, hcb, hcr, hexp⟩ := hpr n hn
  set cK : ℂ → ℂ := fun u => d.Cn n (aInv u)
  set cJ : ℂ → ℂ := fun u => d.Qn n (aInv u)
  set cKp : ℂ → ℂ := fun u => d.Tn n (aInv u)
  set err : ℝ → ℝ := fun x => L x - (fsK x + n⁻¹ * (cK x).re * fsK x +
    n ^ (-(2 / 3 : ℝ)) * (cJ x).re * fsJ x + n ^ (-(4 / 3 : ℝ)) * (cKp x).re * fsKp x)
  have hL_rew : ∀ x : ℝ, L x - fsK x = n⁻¹ * (cK x).re * fsK x +
      n ^ (-(2 / 3 : ℝ)) * (cJ x).re * fsJ x +
      n ^ (-(4 / 3 : ℝ)) * (cKp x).re * fsKp x + err x := fun x => by dsimp [err]; ring
  have hcK_d : DifferentiableOn ℂ cK (ball 0 ρ) := hCn_d.comp ha_d (fun z hz => ha_in z hz)
  have hcJ_d : DifferentiableOn ℂ cJ (ball 0 ρ) := hQn_d.comp ha_d (fun z hz => ha_in z hz)
  have hcKp_d : DifferentiableOn ℂ cKp (ball 0 ρ) := hTn_d.comp ha_d (fun z hz => ha_in z hz)
  have ha_ball_real : ∀ x : ℝ, |x| ≤ R → |(aInv (x : ℂ)).re| < d.rAShrunk := fun x hx => by
    have hmem : (x : ℂ) ∈ ball (0 : ℂ) ρ := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hx.trans_lt hRρ
    exact (Complex.abs_re_le_norm _).trans_lt (mem_ball_zero_iff.1 (ha_in x hmem))
  have ha_real_eq : ∀ x : ℝ, |x| ≤ R → (((aInv (x : ℂ)).re : ℝ) : ℂ) = aInv (x : ℂ) :=
    fun x hx => Complex.ext rfl (ha_r x hx).symm
  have hcK_r : ∀ x : ℝ, |x| ≤ R → (cK (x : ℂ)).im = 0 := fun x hx => by
    dsimp [cK]; rw [← ha_real_eq x hx]; exact (hcr _ (ha_ball_real x hx)).1
  have hcJ_r : ∀ x : ℝ, |x| ≤ R → (cJ (x : ℂ)).im = 0 := fun x hx => by
    dsimp [cJ]; rw [← ha_real_eq x hx]; exact (hcr _ (ha_ball_real x hx)).2.1
  have hcKp_r : ∀ x : ℝ, |x| ≤ R → (cKp (x : ℂ)).im = 0 := fun x hx => by
    dsimp [cKp]; rw [← ha_real_eq x hx]; exact (hcr _ (ha_ball_real x hx)).2.2
  have hcK_bd : ∀ θ ∈ Icc (0 : ℝ) π, ‖cK (circleMap 0 R θ)‖ ≤ M_C := fun θ _ =>
    (hcb _ (ha_in _ (mem_ball_zero_iff.2 (by simp [abs_of_pos hR0, hRρ])))).1
  have hcJ_bd : ∀ θ ∈ Icc (0 : ℝ) π, ‖cJ (circleMap 0 R θ)‖ ≤ M_Q := fun θ _ =>
    (hcb _ (ha_in _ (mem_ball_zero_iff.2 (by simp [abs_of_pos hR0, hRρ])))).2.1
  have hcKp_bd : ∀ θ ∈ Icc (0 : ℝ) π, ‖cKp (circleMap 0 R θ)‖ ≤ M_T := fun θ _ =>
    (hcb _ (ha_in _ (mem_ball_zero_iff.2 (by simp [abs_of_pos hR0, hRρ])))).2.2
  have herr_bd : ∀ x : ℝ, x ∈ Icc (-R) R →
      |err x| ≤ C_rem * n ^ (-(5 / 3 : ℝ)) + C_ext * n ^ (-(3 / 2 : ℝ)) := by
    intro x hx
    have hax : |x| ≤ R := abs_le.2 hx
    have hax_r := ha_ball_real x hax
    obtain ⟨hRc1, hRcR, hURc, _⟩ := uReal_facts d hn hax_r
    have hc1 := hL_close x hax hRc1 hRcR hURc
    have hc2 := hexp _ hax_r hRc1 hRcR hURc
    rw [hu_eq x hax, ha_real_eq x hax] at hc2
    have he_eq : err x = (L x - fsOpCh (fsChain hRc1 hRcR hURc) (d.uReal n (aInv (x : ℂ)).re)
        (fun w => d.B n (aInv (x : ℂ)).re ((n ^ (-(1 / 3 : ℝ)) : ℝ) * w))) +
        (fsOpCh (fsChain hRc1 hRcR hURc) (d.uReal n (aInv (x : ℂ)).re)
          (fun w => d.B n (aInv (x : ℂ)).re ((n ^ (-(1 / 3 : ℝ)) : ℝ) * w)) -
          (fsK x + n⁻¹ * (cK x).re * fsK x + n ^ (-(2 / 3 : ℝ)) * (cJ x).re * fsJ x +
            n ^ (-(4 / 3 : ℝ)) * (cKp x).re * fsKp x)) := by
      dsimp [err, cK, cJ, cKp]; ring
    rw [he_eq]
    calc |_ + _| ≤ |_| + |_| := abs_add_le _ _
      _ ≤ C_ext * n ^ (-(3 / 2 : ℝ)) + C_rem * n ^ (-(5 / 3 : ℝ)) := add_le_add hc1 hc2
      _ = _ := by ring
  have herr_int : IntervalIntegrable (fun x : ℝ => (F (x : ℂ)).re * (b (x : ℂ)).re * err x) volume (-R) R := by
    obtain ⟨hfsJ_c, hfsK_c, hfsKp_c⟩ := continuous_fsJ_K_Kp
    have hpoly_int : IntervalIntegrable (fun x : ℝ => (F (x : ℂ)).re * (b (x : ℂ)).re *
        (n⁻¹ * (cK x).re * fsK x + n ^ (-(2 / 3 : ℝ)) * (cJ x).re * fsJ x +
          n ^ (-(4 / 3 : ℝ)) * (cKp x).re * fsKp x)) volume (-R) R :=
      (((continuousOn_re_real hRρ hF_d).mul (continuousOn_re_real hRρ hb_d)).mul
        ((((continuousOn_const.mul (continuousOn_re_real hRρ hcK_d)).mul hfsK_c.continuousOn).add
        ((continuousOn_const.mul (continuousOn_re_real hRρ hcJ_d)).mul hfsJ_c.continuousOn)).add
        ((continuousOn_const.mul (continuousOn_re_real hRρ hcKp_d)).mul
          hfsKp_c.continuousOn))).intervalIntegrable_of_Icc (by linarith)
    have herr_eq : (fun x : ℝ => (F (x : ℂ)).re * (b (x : ℂ)).re * err x) =
        fun x : ℝ => (F (x : ℂ)).re * (b (x : ℂ)).re * (L x - fsK x) -
          (F (x : ℂ)).re * (b (x : ℂ)).re * (n⁻¹ * (cK x).re * fsK x +
            n ^ (-(2 / 3 : ℝ)) * (cJ x).re * fsJ x + n ^ (-(4 / 3 : ℝ)) * (cKp x).re * fsKp x) := by
      ext x; rw [hL_rew x]; ring
    rw [herr_eq]; exact hL_int.sub hpoly_int
  have hmain := fs_pairing_coeffs hn1 hR1 hRρ hcl hRlo hRhi' hBn hMQ hMC hMT (by positivity)
    hF_d hb_d hcJ_d hcK_d hcKp_d hF_r hb_r hcJ_r hcK_r hcKp_r hb_bd hcJ_bd hcK_bd hcKp_bd hMF
    herr_bd herr_int
  have hcongr : ∫ x in (-R)..R, (F (x : ℂ)).re * (b (x : ℂ)).re * (L x - fsK x) =
      ∫ x in (-R)..R, (F (x : ℂ)).re * (b (x : ℂ)).re *
        (n⁻¹ * (cK x).re * fsK x + n ^ (-(2 / 3 : ℝ)) * (cJ x).re * fsJ x +
          n ^ (-(4 / 3 : ℝ)) * (cKp x).re * fsKp x + err x) :=
    intervalIntegral.integral_congr fun x _ => by rw [hL_rew x]
  rw [hcongr]; exact hmain

/-- **Lemma FS.1 Part (3) (`fs:pairing`), auxiliary form**: pairing `n⁻¹ L_u[B_n]` (without
saddle normalization) against `F b`, with bound `O(‖b‖_∞ (n⁻¹ η_F + n^{-5/3} M))`. -/
theorem fs_pairing_aux (d : HalfCubicData) {cl cu : ℝ} (hcl : 0 < cl) :
    ∃ C_eta C_rem : ℝ, 0 ≤ C_eta ∧ 0 ≤ C_rem ∧
      ∀ {n R ρ Bn MF : ℝ} {F b aInv : ℂ → ℂ} {L : ℝ → ℝ},
        d.n₀ ≤ n → 1 ≤ R → R < ρ →
        cl * n ^ (2 / 3 : ℝ) ≤ R → R ≤ cu * n ^ (2 / 3 : ℝ) → 0 ≤ Bn →
        DifferentiableOn ℂ F (ball 0 ρ) → DifferentiableOn ℂ b (ball 0 ρ) →
        DifferentiableOn ℂ aInv (ball 0 ρ) →
        (∀ z ∈ ball (0 : ℂ) ρ, aInv z ∈ ball (0 : ℂ) d.rAShrunk) →
        (∀ x : ℝ, |x| ≤ R → (F (x : ℂ)).im = 0) →
        (∀ x : ℝ, |x| ≤ R → (b (x : ℂ)).im = 0) →
        (∀ x : ℝ, |x| ≤ R → (aInv (x : ℂ)).im = 0) →
        (∀ x : ℝ, |x| ≤ R → d.uReal n (aInv (x : ℂ)).re = x) →
        (∀ z ∈ closedBall (0 : ℂ) R, ‖b z‖ ≤ Bn) →
        (∫ x in (-R)..R, ‖F (x : ℂ)‖ ≤ MF) →
        (∀ x : ℝ, |x| ≤ R →
          let lam := n ^ (-(1 / 3 : ℝ))
          let R_c := d.s₁ / lam
          let R₀ := Rs d / lam
          let ax := (aInv (x : ℂ)).re
          ∀ (hR1 : 1 ≤ R_c) (hRR : R_c < R₀) (hUR : kap * |d.uReal n ax| ≤ R_c ^ 2 / 16),
          L x = fsOpCh (fsChain hR1 hRR hUR) (d.uReal n ax)
            (fun w => d.B n ax ((lam : ℂ) * w))) →
        IntervalIntegrable (fun x : ℝ => (F (x : ℂ)).re * (b (x : ℂ)).re * (n⁻¹ * L x)) volume (-R) R →
        |∫ x in (-R)..R, (F (x : ℂ)).re * (b (x : ℂ)).re * (n⁻¹ * L x)| ≤
          Bn * (C_eta * n⁻¹ * ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) +
            C_rem * n ^ (-(5 / 3 : ℝ)) * MF) := by
  obtain ⟨M_C, M_T, C_rem, hMC, hMT, hCrem, hax⟩ := fs_aux d
  set cu' := max cu 0
  set C_eta : ℝ := 12 * M_C + 32 * cu' ^ (1 / 2 : ℝ) * M_T
  refine ⟨C_eta, C_rem, by dsimp [C_eta]; positivity, hCrem, ?_⟩
  intro n R ρ Bn MF F b aInv L hn hR1 hRρ hRlo hRhi hBn hF_d hb_d ha_d ha_in
    hF_r hb_r ha_r hu_eq hb_bd hMF hL_eq hL_int
  have hn1 : 1 ≤ n := d.n₀_ge_one.trans hn
  have hn0 : 0 < n := by linarith
  have hR0 : 0 < R := by linarith
  have hRhi' : R ≤ cu' * n ^ (2 / 3 : ℝ) :=
    hRhi.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  obtain ⟨hCs_d, hTs_d, hcb, hcr, hexp⟩ := hax n hn
  set cK : ℂ → ℂ := fun u => d.CnStar n (aInv u)
  set cJ : ℂ → ℂ := fun _ => 0
  set cKp : ℂ → ℂ := fun u => d.TnStar n (aInv u)
  set err : ℝ → ℝ := fun x => n⁻¹ * L x - (n⁻¹ * (cK x).re * fsK x +
    n ^ (-(2 / 3 : ℝ)) * (cJ x).re * fsJ x + n ^ (-(4 / 3 : ℝ)) * (cKp x).re * fsKp x)
  have hL_rew : ∀ x : ℝ, n⁻¹ * L x = n⁻¹ * (cK x).re * fsK x +
      n ^ (-(2 / 3 : ℝ)) * (cJ x).re * fsJ x +
      n ^ (-(4 / 3 : ℝ)) * (cKp x).re * fsKp x + err x := fun x => by dsimp [err]; ring
  have hcK_d : DifferentiableOn ℂ cK (ball 0 ρ) := hCs_d.comp ha_d (fun z hz => ha_in z hz)
  have hcJ_d : DifferentiableOn ℂ cJ (ball 0 ρ) := differentiableOn_const 0
  have hcKp_d : DifferentiableOn ℂ cKp (ball 0 ρ) := hTs_d.comp ha_d (fun z hz => ha_in z hz)
  have ha_ball_real : ∀ x : ℝ, |x| ≤ R → |(aInv (x : ℂ)).re| < d.rAShrunk := fun x hx => by
    have hmem : (x : ℂ) ∈ ball (0 : ℂ) ρ := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hx.trans_lt hRρ
    exact (Complex.abs_re_le_norm _).trans_lt (mem_ball_zero_iff.1 (ha_in x hmem))
  have ha_real_eq : ∀ x : ℝ, |x| ≤ R → (((aInv (x : ℂ)).re : ℝ) : ℂ) = aInv (x : ℂ) :=
    fun x hx => Complex.ext rfl (ha_r x hx).symm
  have hcK_r : ∀ x : ℝ, |x| ≤ R → (cK (x : ℂ)).im = 0 := fun x hx => by
    dsimp [cK]; rw [← ha_real_eq x hx]; exact (hcr _ (ha_ball_real x hx)).1
  have hcJ_r : ∀ x : ℝ, |x| ≤ R → (cJ (x : ℂ)).im = 0 := fun _ _ => rfl
  have hcKp_r : ∀ x : ℝ, |x| ≤ R → (cKp (x : ℂ)).im = 0 := fun x hx => by
    dsimp [cKp]; rw [← ha_real_eq x hx]; exact (hcr _ (ha_ball_real x hx)).2
  have hcK_bd : ∀ θ ∈ Icc (0 : ℝ) π, ‖cK (circleMap 0 R θ)‖ ≤ M_C := fun θ _ =>
    (hcb _ (ha_in _ (mem_ball_zero_iff.2 (by simp [abs_of_pos hR0, hRρ])))).1
  have hcJ_bd : ∀ θ ∈ Icc (0 : ℝ) π, ‖cJ (circleMap 0 R θ)‖ ≤ 0 := fun _ _ => by simp [cJ]
  have hcKp_bd : ∀ θ ∈ Icc (0 : ℝ) π, ‖cKp (circleMap 0 R θ)‖ ≤ M_T := fun θ _ =>
    (hcb _ (ha_in _ (mem_ball_zero_iff.2 (by simp [abs_of_pos hR0, hRρ])))).2
  have herr_bd : ∀ x : ℝ, x ∈ Icc (-R) R → |err x| ≤ C_rem * n ^ (-(5 / 3 : ℝ)) := by
    intro x hx
    have hax : |x| ≤ R := abs_le.2 hx
    have hax_r := ha_ball_real x hax
    obtain ⟨hRc1, hRcR, hURc, _⟩ := uReal_facts d hn hax_r
    have hL := hL_eq x hax hRc1 hRcR hURc
    have hE := hexp _ hax_r hRc1 hRcR hURc
    rw [hu_eq x hax, ha_real_eq x hax, ← hL] at hE
    have hpow : n⁻¹ * n ^ (-(2 / 3 : ℝ)) = n ^ (-(5 / 3 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hn0]; congr 1; norm_num
    have h43 : n⁻¹ * n ^ (-(1 / 3 : ℝ)) = n ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hn0]; congr 1; norm_num
    have he_eq : err x = n⁻¹ * (L x - ((cK x).re * fsK x + n ^ (-(1 / 3 : ℝ)) * (cKp x).re * fsKp x)) := by
      dsimp [err, cJ, cK, cKp]; simp only [Complex.zero_re, mul_zero, zero_mul, add_zero]
      rw [mul_sub, mul_add, ← mul_assoc, ← mul_assoc, h43]
    rw [he_eq, abs_mul, abs_of_pos (inv_pos.2 hn0)]
    calc n⁻¹ * |L x - ((cK x).re * fsK x + n ^ (-(1 / 3 : ℝ)) * (cKp x).re * fsKp x)|
        ≤ n⁻¹ * (C_rem * n ^ (-(2 / 3 : ℝ))) := mul_le_mul_of_nonneg_left hE (inv_nonneg.2 hn0.le)
      _ = C_rem * (n⁻¹ * n ^ (-(2 / 3 : ℝ))) := by ring
      _ = C_rem * n ^ (-(5 / 3 : ℝ)) := by rw [hpow]
  have herr_int : IntervalIntegrable (fun x : ℝ => (F (x : ℂ)).re * (b (x : ℂ)).re * err x) volume (-R) R := by
    obtain ⟨_, hfsK_c, hfsKp_c⟩ := continuous_fsJ_K_Kp
    have hpoly_int : IntervalIntegrable (fun x : ℝ => (F (x : ℂ)).re * (b (x : ℂ)).re *
        (n⁻¹ * (cK x).re * fsK x + n ^ (-(2 / 3 : ℝ)) * (cJ x).re * fsJ x +
          n ^ (-(4 / 3 : ℝ)) * (cKp x).re * fsKp x)) volume (-R) R := by
      have hsimp : (fun x : ℝ => (F (x : ℂ)).re * (b (x : ℂ)).re *
          (n⁻¹ * (cK x).re * fsK x + n ^ (-(2 / 3 : ℝ)) * (cJ x).re * fsJ x +
            n ^ (-(4 / 3 : ℝ)) * (cKp x).re * fsKp x)) = fun x : ℝ =>
          (F (x : ℂ)).re * (b (x : ℂ)).re * (n⁻¹ * (cK x).re * fsK x +
            n ^ (-(4 / 3 : ℝ)) * (cKp x).re * fsKp x) := by ext x; simp [cJ]
      rw [hsimp]
      exact (((continuousOn_re_real hRρ hF_d).mul (continuousOn_re_real hRρ hb_d)).mul
        (((continuousOn_const.mul (continuousOn_re_real hRρ hcK_d)).mul hfsK_c.continuousOn).add
        ((continuousOn_const.mul (continuousOn_re_real hRρ hcKp_d)).mul
          hfsKp_c.continuousOn))).intervalIntegrable_of_Icc (by linarith)
    have herr_eq : (fun x : ℝ => (F (x : ℂ)).re * (b (x : ℂ)).re * err x) =
        fun x : ℝ => (F (x : ℂ)).re * (b (x : ℂ)).re * (n⁻¹ * L x) -
          (F (x : ℂ)).re * (b (x : ℂ)).re * (n⁻¹ * (cK x).re * fsK x +
            n ^ (-(2 / 3 : ℝ)) * (cJ x).re * fsJ x + n ^ (-(4 / 3 : ℝ)) * (cKp x).re * fsKp x) := by
      ext x; rw [hL_rew x]; ring
    rw [herr_eq]; exact hL_int.sub hpoly_int
  have hmain := fs_pairing_coeffs hn1 hR1 hRρ hcl hRlo hRhi' hBn le_rfl hMC hMT (by positivity)
    hF_d hb_d hcJ_d hcK_d hcKp_d hF_r hb_r hcJ_r hcK_r hcKp_r hb_bd hcJ_bd hcK_bd hcKp_bd hMF
    herr_bd herr_int
  have hcongr : ∫ x in (-R)..R, (F (x : ℂ)).re * (b (x : ℂ)).re * (n⁻¹ * L x) =
      ∫ x in (-R)..R, (F (x : ℂ)).re * (b (x : ℂ)).re *
        (n⁻¹ * (cK x).re * fsK x + n ^ (-(2 / 3 : ℝ)) * (cJ x).re * fsJ x +
          n ^ (-(4 / 3 : ℝ)) * (cKp x).re * fsKp x + err x) :=
    intervalIntegral.integral_congr fun x _ => by rw [hL_rew x]
  rw [hcongr]
  refine hmain.trans_eq ?_
  dsimp [C_eta]; ring

/-- info: 'FormalResearch.SignUncertainty.FineOrderSigned.fs_principal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fs_principal

/-- info: 'FormalResearch.SignUncertainty.FineOrderSigned.fs_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fs_aux

/-- info: 'FormalResearch.SignUncertainty.FineOrderSigned.fs_pairing_principal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fs_pairing_principal

/-- info: 'FormalResearch.SignUncertainty.FineOrderSigned.fs_pairing_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fs_pairing_aux

end FineOrderSigned

end FormalResearch.SignUncertainty
