module

public import FormalResearch.SignUncertainty.WindowKernelApprox
public import FormalResearch.CohnElkies.MellinKernelHolomorphic
public import FormalResearch.CohnElkies.VerticalStripShift
public import FormalResearch.CohnElkies.AiryWindowInversion

/-!
# `O.5`(1): the window translation `(e5)`

Source: `CFT/sign_uncertainty/paper/u1c_o1_upper.tex`, Lemma `O.5`(1) (`u1co:O5`), proof in
`u1c_estimate_proofs.tex`: the main-edge integral `I_main` is moved to `Re w = 1` (`strip_shift`), where
`K₀(ε w, ξ)` is compared with the reference kernel `exp(π² w³/36 + (π² S + ε/2) w)` (`K0_near_approx`, `norm_K0_line_le`);
the reference integral is `(k β₁/(π² ξ)) F_ψ(-β₁ S - ε/(2 c_s))` by `airy_reference_identity`.

Status: proved, unconditional; the threshold `c ≥ 32768` (`ε ≤ 1/32`) replaces the paper's `c ≥ 200`.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-! ### The lift symbol on the closed right half-plane -/

lemma liftSymbol_continuousOn {X : ℝ → ℝ} (h : HasU2 X) (δ₀ : ℝ) (m : ℕ) :
    ContinuousOn (liftSymbol X δ₀ m) {w : ℂ | 0 ≤ w.re} := by
  unfold liftSymbol liftMultiplier
  refine ContinuousOn.mul ?_ ?_
  · exact (differentiable_bsplineE1.continuous.comp (continuous_const.mul continuous_id)).pow m |>.continuousOn
  · refine h.continuousOn.comp (continuous_const.mul continuous_id).continuousOn fun w hw => ?_
    simp only [Set.mem_ofPred_eq, Complex.re_ofReal_mul] at hw ⊢
    exact mul_nonneg ceCs_pos.le hw

lemma liftSymbol_differentiableOn {X : ℝ → ℝ} (h : HasU2 X) (δ₀ : ℝ) (m : ℕ) :
    DifferentiableOn ℂ (liftSymbol X δ₀ m) {w : ℂ | 0 < w.re} := by
  unfold liftSymbol liftMultiplier
  refine DifferentiableOn.mul ?_ ?_
  · exact ((differentiable_bsplineE1.comp ((differentiable_const _).mul differentiable_id)).pow m).differentiableOn
  · refine h.differentiable.comp (differentiableOn_const _ |>.mul differentiableOn_id) fun w hw => ?_
    simp only [Set.mem_ofPred_eq, Complex.re_ofReal_mul] at hw ⊢
    exact mul_pos ceCs_pos hw

/-- The `U.2` bound of the lift symbol, uniformly in the width `δ₀ ≥ 0` and the order `m`. -/
lemma hasU2_norm_liftSymbol_le_unif {X : ℝ → ℝ} (h : HasU2 X) :
    ∃ C > 0, ∀ {δ₀ : ℝ} (m : ℕ) {w : ℂ}, 0 ≤ δ₀ → 0 ≤ w.re → ‖liftSymbol X δ₀ m w‖ ≤ C * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := h.rhp
  refine ⟨C * 2 ^ (5 / 2 : ℝ), by positivity, fun {δ₀} m {w} hδ hw => ?_⟩
  have h1 : 0 < 1 + |w.im| := by positivity
  have hn : 0 < ‖1 + w‖ := by
    have : (1 : ℝ) ≤ (1 + w).re := by simpa using hw
    exact lt_of_lt_of_le one_pos (this.trans (Complex.re_le_norm _))
  have h2 := one_add_abs_im_le_two_mul_norm_one_add hw
  have hpow : ‖1 + w‖ ^ (-(5 / 2 : ℝ)) ≤ 2 ^ (5 / 2 : ℝ) * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by
    have h3 : (1 + |w.im|) / 2 ≤ ‖1 + w‖ := by linarith
    calc ‖1 + w‖ ^ (-(5 / 2 : ℝ)) ≤ ((1 + |w.im|) / 2) ^ (-(5 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h3 (by norm_num)
      _ = 2 ^ (5 / 2 : ℝ) * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by
          rw [Real.div_rpow h1.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
          ring
  unfold liftSymbol
  rw [norm_mul]
  calc ‖liftMultiplier δ₀ m w‖ * ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ 1 * (C * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) :=
        mul_le_mul (norm_liftMultiplier_le_one hδ m hw) (hb w hw) (norm_nonneg _) zero_le_one
    _ ≤ C * (2 ^ (5 / 2 : ℝ) * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) := by rw [one_mul]; exact mul_le_mul_of_nonneg_left hpow hC.le
    _ = _ := by ring

/-! ### The shift with the `(1+|Im w|)^{-5/2}` weight -/

lemma tendsto_weight_atTop (B : ℝ) : Tendsto (fun v : ℝ => B * (1 + |v|) ^ (-(5 / 2 : ℝ))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun v : ℝ => 1 + |v|) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_abs_atTop_atTop)
  have := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5 / 2)).comp h1).const_mul B
  simpa using this

lemma tendsto_weight_atBot (B : ℝ) : Tendsto (fun v : ℝ => B * (1 + |v|) ^ (-(5 / 2 : ℝ))) atBot (𝓝 0) := by
  have h1 : Tendsto (fun v : ℝ => 1 + |v|) atBot atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_abs_atBot_atTop)
  have := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5 / 2)).comp h1).const_mul B
  simpa using this

lemma integrable_weight (B : ℝ) : Integrable (fun v : ℝ => B * (1 + |v|) ^ (-(5 / 2 : ℝ))) :=
  integrable_one_add_abs_rpow.const_mul B

theorem strip_shift_weight {H : ℂ → ℂ} {B : ℝ}
    (hc : ContinuousOn H {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1})
    (hd : DifferentiableOn ℂ H {w : ℂ | 0 < w.re ∧ w.re < 1})
    (hbd : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → ‖H w‖ ≤ B * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) :
    ∫ v : ℝ, H ((1 : ℝ) + (v : ℂ) * Complex.I) = ∫ v : ℝ, H ((0 : ℝ) + (v : ℂ) * Complex.I) :=
  strip_shift (a := 0) (b := 1) zero_le_one hc hd (integrable_weight B) hbd (tendsto_weight_atTop B) (tendsto_weight_atBot B)

/-! ### A polynomial-Gaussian bound -/

lemma cube_le_exp_sq {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ, (1 + |v|) ^ 3 ≤ C * Real.exp (a * v ^ 2) := by
  refine ⟨4 + 2 / a + 4 / a ^ 2, by positivity, fun v => ?_⟩
  set t := |v| with ht
  have ht0 : 0 ≤ t := abs_nonneg v
  have hv2 : v ^ 2 = t ^ 2 := (sq_abs v).symm
  rw [hv2]
  have hexp : 1 + a * t ^ 2 + (a * t ^ 2) ^ 2 / 2 ≤ Real.exp (a * t ^ 2) :=
    Real.quadratic_le_exp_of_nonneg (by positivity)
  have h3 : (1 + t) ^ 3 ≤ 4 + 2 * t ^ 2 + 2 * t ^ 4 := by
    nlinarith [sq_nonneg (t - 1), sq_nonneg t, sq_nonneg (t ^ 2 - t), mul_nonneg ht0 (sq_nonneg (t - 1))]
  have hC : 4 + 2 * t ^ 2 + 2 * t ^ 4 ≤ (4 + 2 / a + 4 / a ^ 2) * (1 + a * t ^ 2 + (a * t ^ 2) ^ 2 / 2) := by
    have e1 : (2 / a) * (a * t ^ 2) = 2 * t ^ 2 := by field_simp
    have e2 : (4 / a ^ 2) * ((a * t ^ 2) ^ 2 / 2) = 2 * t ^ 4 := by field_simp; ring
    have p1 : 0 ≤ 4 * (a * t ^ 2) := by positivity
    have p2 : 0 ≤ 4 * ((a * t ^ 2) ^ 2 / 2) := by positivity
    have p3 : 0 ≤ (2 / a) * 1 := by positivity
    have p4 : 0 ≤ (2 / a) * ((a * t ^ 2) ^ 2 / 2) := by positivity
    have p5 : 0 ≤ (4 / a ^ 2) * 1 := by positivity
    have p6 : 0 ≤ (4 / a ^ 2) * (a * t ^ 2) := by positivity
    nlinarith
  calc (1 + t) ^ 3 ≤ _ := h3
    _ ≤ _ := hC
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)

/-! ### The comparison on `Re w = 1` -/

lemma exists_scale {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 32) :
    ∃ V : ℝ, 1 ≤ V ∧ ε ^ 2 * V ^ 5 = 1 ∧ ε * V ≤ 1 / 8 := by
  set V : ℝ := (ε ^ 2) ^ (-(1 / 5 : ℝ)) with hV
  have h2 : 0 < ε ^ 2 := by positivity
  have hV0 : 0 < V := Real.rpow_pos_of_pos h2 _
  have hV5 : V ^ 5 = (ε ^ 2)⁻¹ := by
    rw [hV, ← Real.rpow_natCast, ← Real.rpow_mul h2.le]
    norm_num
    exact Real.rpow_neg_one _
  have hε21 : ε ^ 2 ≤ 1 := by nlinarith
  have hV1 : 1 ≤ V := by
    by_contra h
    push Not at h
    have : V ^ 5 < 1 := pow_lt_one₀ hV0.le h (by norm_num)
    rw [hV5] at this
    have : 1 < (ε ^ 2)⁻¹ := (one_lt_inv₀ h2).mpr (lt_of_le_of_ne hε21 (by intro h; nlinarith))
    linarith
  refine ⟨V, hV1, ?_, ?_⟩
  · rw [hV5]; field_simp
  · by_contra h
    push Not at h
    have h5 : (1 / 8 : ℝ) ^ 5 < (ε * V) ^ 5 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
    have : (ε * V) ^ 5 = ε ^ 3 := by
      have : (ε * V) ^ 5 = ε ^ 3 * (ε ^ 2 * V ^ 5) := by ring
      rw [this, show ε ^ 2 * V ^ 5 = 1 by rw [hV5]; field_simp, mul_one]
    rw [this] at h5
    have : ε ^ 3 ≤ (1 / 32 : ℝ) ^ 3 := pow_le_pow_left₀ hε.le hε1 3
    norm_num at h5 this
    linarith

lemma exp_neg_sq_le {ε V : ℝ} (hε : 0 < ε) (hV1 : 1 ≤ V) (hV : ε ^ 2 * V ^ 5 = 1) :
    Real.exp (-((3 / 56 : ℝ) * V ^ 2)) ≤ (6 * (56 / 3 : ℝ) ^ 3) * ε ^ 2 := by
  have hy : 0 ≤ (3 / 56 : ℝ) * V ^ 2 := by positivity
  have h := Real.pow_div_factorial_le_exp ((3 / 56 : ℝ) * V ^ 2) hy 3
  have hV6 : (ε ^ 2)⁻¹ ≤ V ^ 6 := by
    have : V ^ 5 = (ε ^ 2)⁻¹ := by field_simp; linarith
    calc (ε ^ 2)⁻¹ = V ^ 5 := this.symm
      _ ≤ V ^ 6 := pow_le_pow_right₀ hV1 (by norm_num)
  have hexp : (3 / 56 : ℝ) ^ 3 / 6 * ((ε ^ 2)⁻¹) ≤ Real.exp ((3 / 56 : ℝ) * V ^ 2) := by
    refine le_trans ?_ h
    simp only [Nat.factorial]
    norm_num
    have : ((3 / 56 : ℝ) * V ^ 2) ^ 3 = (3 / 56 : ℝ) ^ 3 * V ^ 6 := by ring
    rw [this]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 3 / 56) 3]
  rw [Real.exp_neg]
  have : (Real.exp ((3 / 56 : ℝ) * V ^ 2))⁻¹ ≤ ((3 / 56 : ℝ) ^ 3 / 6 * (ε ^ 2)⁻¹)⁻¹ :=
    inv_anti₀ (by positivity) hexp
  refine this.trans (le_of_eq ?_)
  field_simp

lemma rpow_five_mul_neg_le {t : ℝ} (ht : 1 ≤ t) : t ^ 5 * t ^ (-(5 / 2 : ℝ)) ≤ t ^ 3 := by
  have ht0 : 0 < t := by linarith
  have h1 : t ^ 5 = t ^ (5 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
  have h2 : t ^ 3 = t ^ (3 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
  rw [h1, h2, ← Real.rpow_add ht0]
  exact Real.rpow_le_rpow_of_exponent_le ht (by norm_num)

set_option maxHeartbeats 1600000 in
theorem main_line_diff (m : ℕ) (Sw CW : ℝ) (hCW : 0 < CW) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : ℝ → ℝ},
      (∀ {δ₀ : ℝ} {w : ℂ}, 0 ≤ δ₀ → 0 ≤ w.re → ‖liftSymbol X δ₀ m w‖ ≤ CW * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) →
      ∀ {δ₀ c ε ξ S : ℝ}, 0 ≤ δ₀ → 0 < ε → c * ε ^ 3 = 1 → ε ≤ 1 / 32 → 0 < ξ →
      Real.log (Real.pi ^ 2 * ξ) = Real.pi ^ 2 * ε ^ 2 * S → |S| ≤ Sw →
      ‖∫ v : ℝ, (mellinK0 c ((ε : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ -
            refKernel S ε ((1 : ℂ) + (v : ℂ) * Complex.I)) *
          liftSymbol X δ₀ m ((1 : ℂ) + (v : ℂ) * Complex.I)‖ ≤ C * ε ^ 2 := by
  have hpi : 9 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  obtain ⟨Cp, hCp, hpoly⟩ := cube_le_exp_sq (a := Real.pi ^ 2 / 24) (by positivity)
  set B₀ : ℝ := 2 * Real.exp (1 + Real.pi ^ 2 * Sw) with hB₀
  set E : ℝ := Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * Sw + 1) with hE
  set Cexp : ℝ := 6 * (56 / 3 : ℝ) ^ 3 with hCexp
  set Ca : ℝ := 11 * Real.exp (11 * 32) * E * CW * Cp with hCa
  set Cb : ℝ := CW * (B₀ + E) * Cexp with hCb
  set G : ℝ := ∫ v : ℝ, Real.exp (-(Real.pi ^ 2 / 24) * v ^ 2) with hG
  set J : ℝ := ∫ v : ℝ, (1 + |v|) ^ (-(5 / 2 : ℝ)) with hJ
  have hGint : Integrable fun v : ℝ => Real.exp (-(Real.pi ^ 2 / 24) * v ^ 2) :=
    integrable_exp_neg_mul_sq (by positivity)
  have hG0 : 0 ≤ G := integral_nonneg fun v => (Real.exp_pos _).le
  have hJ0 : 0 ≤ J := integral_nonneg fun v => Real.rpow_nonneg (by positivity) _
  have hCa0 : 0 ≤ Ca := by positivity
  have hCb0 : 0 ≤ Cb := by positivity
  refine ⟨Ca * G + Cb * J + 1, by positivity, fun {X} hW {δ₀ c ε ξ S} hδ hε hcube hε1 hξ hL hS => ?_⟩
  have hε2 : ε ≤ 1 / 2 := by linarith
  have hc := eps_cube_inv hε hcube
  obtain ⟨V, hV1, hV5, hεV⟩ := exists_scale hε hε1
  have hSw : S ≤ Sw := (le_abs_self S).trans hS
  have hSabs : |S| ≤ Sw := hS
  have hexpV := exp_neg_sq_le hε hV1 hV5
  have hcε : c * ε = V ^ 5 := by
    have : c * ε = (c * ε ^ 3) * (ε ^ 2)⁻¹ := by field_simp
    rw [this, hcube, one_mul]
    have : V ^ 5 = (ε ^ 2)⁻¹ := by field_simp; linarith
    rw [this]
  -- the pointwise bound
  have hpt : ∀ v : ℝ, ‖(mellinK0 c ((ε : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ -
            refKernel S ε ((1 : ℂ) + (v : ℂ) * Complex.I)) *
          liftSymbol X δ₀ m ((1 : ℂ) + (v : ℂ) * Complex.I)‖ ≤
        ε ^ 2 * (Ca * Real.exp (-(Real.pi ^ 2 / 24) * v ^ 2) + Cb * (1 + |v|) ^ (-(5 / 2 : ℝ))) := by
    intro v
    have hWv := hW (w := (1 : ℂ) + (v : ℂ) * Complex.I) hδ (by simp)
    have him : ((1 : ℂ) + (v : ℂ) * Complex.I).im = v := by simp
    rw [him] at hWv
    have hEref : Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * S + ε / 2) ≤ E := by
      rw [hE]; apply Real.exp_le_exp.mpr; nlinarith only [hSw, hε2, mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.2 hSw)]
    have hp1 : 0 ≤ (1 + |v|) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
    rw [norm_mul]
    by_cases hv : |v| ≤ V
    · -- near region
      have hζ : ε * (1 + |v|) ≤ 1 / 4 := by nlinarith only [hε1, hεV, mul_nonneg hε.le (sub_nonneg.2 hv)]
      have hM : ε ^ 2 * (1 + |v|) ^ 5 ≤ 32 := by
        have h1 : (1 + |v|) ^ 5 ≤ (2 * V) ^ 5 := by
          apply pow_le_pow_left₀ (by positivity); linarith
        calc ε ^ 2 * (1 + |v|) ^ 5 ≤ ε ^ 2 * (2 * V) ^ 5 := by gcongr
          _ = 32 * (ε ^ 2 * V ^ 5) := by ring
          _ = 32 := by rw [hV5]; ring
      have hk := K0_near_approx hε hcube hξ hL hζ hM
      have h1 : ‖mellinK0 c ((ε : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ -
          refKernel S ε ((1 : ℂ) + (v : ℂ) * Complex.I)‖ ≤
          11 * Real.exp (11 * 32) * (ε ^ 2 * (1 + |v|) ^ 5) * (E * Real.exp (-(Real.pi ^ 2 * v ^ 2 / 12))) := by
        refine hk.trans ?_
        gcongr
      have h2 : (1 + |v|) ^ 5 * (1 + |v|) ^ (-(5 / 2 : ℝ)) * Real.exp (-(Real.pi ^ 2 * v ^ 2 / 12)) ≤
          Cp * Real.exp (-(Real.pi ^ 2 / 24) * v ^ 2) := by
        have h3 := rpow_five_mul_neg_le (t := 1 + |v|) (by linarith [abs_nonneg v])
        have h4 := hpoly v
        calc (1 + |v|) ^ 5 * (1 + |v|) ^ (-(5 / 2 : ℝ)) * Real.exp (-(Real.pi ^ 2 * v ^ 2 / 12))
            ≤ (1 + |v|) ^ 3 * Real.exp (-(Real.pi ^ 2 * v ^ 2 / 12)) := by gcongr
          _ ≤ (Cp * Real.exp (Real.pi ^ 2 / 24 * v ^ 2)) * Real.exp (-(Real.pi ^ 2 * v ^ 2 / 12)) := by gcongr
          _ = Cp * Real.exp (-(Real.pi ^ 2 / 24) * v ^ 2) := by
              rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      calc ‖mellinK0 c ((ε : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ -
            refKernel S ε ((1 : ℂ) + (v : ℂ) * Complex.I)‖ *
            ‖liftSymbol X δ₀ m ((1 : ℂ) + (v : ℂ) * Complex.I)‖
          ≤ (11 * Real.exp (11 * 32) * (ε ^ 2 * (1 + |v|) ^ 5) * (E * Real.exp (-(Real.pi ^ 2 * v ^ 2 / 12)))) *
            (CW * (1 + |v|) ^ (-(5 / 2 : ℝ))) := by gcongr
        _ = 11 * Real.exp (11 * 32) * E * CW * ε ^ 2 *
            ((1 + |v|) ^ 5 * (1 + |v|) ^ (-(5 / 2 : ℝ)) * Real.exp (-(Real.pi ^ 2 * v ^ 2 / 12))) := by ring
        _ ≤ 11 * Real.exp (11 * 32) * E * CW * ε ^ 2 * (Cp * Real.exp (-(Real.pi ^ 2 / 24) * v ^ 2)) := by gcongr
        _ = ε ^ 2 * (Ca * Real.exp (-(Real.pi ^ 2 / 24) * v ^ 2)) := by rw [hCa]; ring
        _ ≤ _ := by
            have : 0 ≤ ε ^ 2 * (Cb * (1 + |v|) ^ (-(5 / 2 : ℝ))) := by positivity
            nlinarith only [this]
    · -- far region
      have hv' : V < |v| := not_le.mp hv
      have hv2 : V ^ 2 ≤ v ^ 2 := by rw [← sq_abs v]; exact pow_le_pow_left₀ (by linarith) hv'.le 2
      have hmin : V ^ 2 ≤ min (v ^ 2) (c * ε) := by
        refine le_min hv2 ?_
        rw [hcε]; exact pow_le_pow_right₀ hV1 (by norm_num)
      have hK := norm_K0_line_le (v := v) hε hcube hε2 hξ hL
      have hK' : ‖mellinK0 c ((ε : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ‖ ≤ B₀ * (Cexp * ε ^ 2) := by
        refine hK.trans ?_
        have h1 : Real.exp (-((3 / 56 : ℝ) * min (v ^ 2) (c * ε))) ≤ Real.exp (-((3 / 56 : ℝ) * V ^ 2)) := by
          apply Real.exp_le_exp.mpr; linarith only [hmin]
        have h2 : 2 * Real.exp (1 + Real.pi ^ 2 * |S|) ≤ B₀ := by
          rw [hB₀]
          have := Real.exp_le_exp.mpr (by nlinarith only [hSabs, mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.2 hSabs)] : 1 + Real.pi ^ 2 * |S| ≤ 1 + Real.pi ^ 2 * Sw)
          linarith
        exact mul_le_mul h2 (h1.trans hexpV) (Real.exp_pos _).le (by positivity)
      have hR : ‖refKernel S ε ((1 : ℂ) + (v : ℂ) * Complex.I)‖ ≤ E * (Cexp * ε ^ 2) := by
        rw [norm_refKernel_line]
        have h1 : Real.exp (-(Real.pi ^ 2 * v ^ 2 / 12)) ≤ Cexp * ε ^ 2 := by
          refine le_trans ?_ hexpV
          apply Real.exp_le_exp.mpr
          nlinarith only [hv2, hpi, mul_nonneg (sub_nonneg.2 hpi.le) (sq_nonneg v), sq_nonneg V]
        exact mul_le_mul hEref h1 (Real.exp_pos _).le (by positivity)
      have hdiff : ‖mellinK0 c ((ε : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ -
          refKernel S ε ((1 : ℂ) + (v : ℂ) * Complex.I)‖ ≤ (B₀ + E) * (Cexp * ε ^ 2) := by
        refine (norm_sub_le _ _).trans ?_
        linarith
      calc ‖mellinK0 c ((ε : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ -
            refKernel S ε ((1 : ℂ) + (v : ℂ) * Complex.I)‖ *
            ‖liftSymbol X δ₀ m ((1 : ℂ) + (v : ℂ) * Complex.I)‖
          ≤ ((B₀ + E) * (Cexp * ε ^ 2)) * (CW * (1 + |v|) ^ (-(5 / 2 : ℝ))) := by gcongr
        _ = ε ^ 2 * (Cb * (1 + |v|) ^ (-(5 / 2 : ℝ))) := by rw [hCb]; ring
        _ ≤ _ := by
            have : 0 ≤ ε ^ 2 * (Ca * Real.exp (-(Real.pi ^ 2 / 24) * v ^ 2)) := by positivity
            nlinarith only [this]
  have hPsi : Integrable fun v : ℝ => ε ^ 2 * (Ca * Real.exp (-(Real.pi ^ 2 / 24) * v ^ 2) +
      Cb * (1 + |v|) ^ (-(5 / 2 : ℝ))) :=
    ((hGint.const_mul Ca).add (integrable_one_add_abs_rpow.const_mul Cb)).const_mul _
  refine (norm_integral_le_of_norm_le hPsi (ae_of_all _ hpt)).trans ?_
  rw [integral_const_mul, integral_add (hGint.const_mul Ca) (integrable_one_add_abs_rpow.const_mul Cb),
    integral_const_mul, integral_const_mul]
  have hε2' : 0 ≤ ε ^ 2 := by positivity
  nlinarith only [hε2']

/-! ### The shift of `I_main` and of the reference integral -/

lemma re_strip_cube (σ v : ℝ) : ((((σ : ℂ) + (v : ℂ) * Complex.I)) ^ 3).re = σ ^ 3 - 3 * σ * v ^ 2 := by
  simp [pow_succ, Complex.mul_re, Complex.mul_im]; ring

lemma norm_refKernel_strip_le {S ε σ v Sw : ℝ} (hε1 : ε ≤ 1) (hS : |S| ≤ Sw) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ‖refKernel S ε ((σ : ℂ) + (v : ℂ) * Complex.I)‖ ≤ Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * Sw + 1) := by
  unfold refKernel
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have h3 := re_strip_cube σ v
  have e : ((Real.pi ^ 2 / 36 : ℂ) * ((σ : ℂ) + (v : ℂ) * Complex.I) ^ 3 +
      ((Real.pi ^ 2 * S + ε / 2 : ℝ) : ℂ) * ((σ : ℂ) + (v : ℂ) * Complex.I)).re =
      Real.pi ^ 2 / 36 * (σ ^ 3 - 3 * σ * v ^ 2) + (Real.pi ^ 2 * S + ε / 2) * σ := by
    have : ((Real.pi ^ 2 / 36 : ℂ)) = ((Real.pi ^ 2 / 36 : ℝ) : ℂ) := by push_cast; ring
    rw [Complex.add_re, this, Complex.re_ofReal_mul, h3, Complex.re_ofReal_mul]
    simp
  rw [e]
  have hpi := Real.pi_pos
  have hS' : S ≤ Sw := (le_abs_self S).trans hS
  have h1 : σ ^ 3 ≤ 1 := pow_le_one₀ hσ0 hσ1
  have h2 : 0 ≤ 3 * σ * v ^ 2 := by positivity
  have h4 : (Real.pi ^ 2 * S + ε / 2) * σ ≤ Real.pi ^ 2 * Sw + 1 := by
    have : Real.pi ^ 2 * S + ε / 2 ≤ Real.pi ^ 2 * Sw + 1 := by nlinarith only [hε1, hS', mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.2 hS')]
    have hA : (Real.pi ^ 2 * S + ε / 2) * σ ≤ (Real.pi ^ 2 * Sw + 1) * σ := by
      by_cases hσ : σ = 0
      · simp [hσ]
      · exact mul_le_mul_of_nonneg_right this hσ0
    nlinarith only [hA, mul_nonneg (add_nonneg (mul_nonneg (sq_nonneg Real.pi) ((abs_nonneg S).trans hS)) zero_le_one) (sub_nonneg.mpr hσ1)]
  nlinarith only [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ Real.pi ^ 2 / 36),
    mul_nonneg (by positivity : (0 : ℝ) ≤ Real.pi ^ 2 / 36) h2, h4]

/-- Shift of `∫ K(v i) W(v i) dv` to `Re w = 1` for a kernel `K` that is holomorphic and bounded on the strip. -/
theorem shift_kernel_lift {X : ℝ → ℝ} (hX : HasU2 X) {δ₀ : ℝ} (_hδ : 0 ≤ δ₀) (m : ℕ) {CW BK : ℝ}
    (hW : ∀ {w : ℂ}, 0 ≤ w.re → ‖liftSymbol X δ₀ m w‖ ≤ CW * (1 + |w.im|) ^ (-(5 / 2 : ℝ)))
    {Kf : ℂ → ℂ} (hKc : ContinuousOn Kf {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1})
    (hKd : DifferentiableOn ℂ Kf {w : ℂ | 0 < w.re ∧ w.re < 1})
    (hKb : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → ‖Kf w‖ ≤ BK) :
    ∫ v : ℝ, Kf ((1 : ℂ) + (v : ℂ) * Complex.I) * liftSymbol X δ₀ m ((1 : ℂ) + (v : ℂ) * Complex.I) =
      ∫ v : ℝ, Kf ((v : ℂ) * Complex.I) * liftSymbol X δ₀ m ((v : ℂ) * Complex.I) := by
  have hBK : 0 ≤ BK := (norm_nonneg _).trans (hKb 0 le_rfl (by simp))
  have := strip_shift_weight (H := fun w => Kf w * liftSymbol X δ₀ m w) (B := BK * CW)
    (hKc.mul ((liftSymbol_continuousOn hX δ₀ m).mono fun w hw => hw.1))
    (hKd.mul ((liftSymbol_differentiableOn hX δ₀ m).mono fun w hw => hw.1))
    (fun w h0 h1 => by
      rw [norm_mul]
      calc ‖Kf w‖ * ‖liftSymbol X δ₀ m w‖ ≤ BK * (CW * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) :=
            mul_le_mul (hKb w h0 h1) (hW h0) (norm_nonneg _) hBK
        _ = _ := by ring)
  simpa using this

theorem integrable_kernel_lift {X : ℝ → ℝ} (hX : HasU2 X) {δ₀ : ℝ} (m : ℕ) {CW BK : ℝ}
    (hW : ∀ {w : ℂ}, 0 ≤ w.re → ‖liftSymbol X δ₀ m w‖ ≤ CW * (1 + |w.im|) ^ (-(5 / 2 : ℝ)))
    {Kf : ℂ → ℂ} (hKc : ContinuousOn Kf {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1})
    (hKb : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → ‖Kf w‖ ≤ BK) (hBK : 0 ≤ BK) :
    Integrable fun v : ℝ => Kf ((1 : ℂ) + (v : ℂ) * Complex.I) * liftSymbol X δ₀ m ((1 : ℂ) + (v : ℂ) * Complex.I) := by
  have hline : Continuous fun v : ℝ => ((1 : ℂ) + (v : ℂ) * Complex.I) := by fun_prop
  have hmem : ∀ v : ℝ, ((1 : ℂ) + (v : ℂ) * Complex.I) ∈ {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1} := fun v => by simp
  have hc1 : Continuous fun v : ℝ => Kf ((1 : ℂ) + (v : ℂ) * Complex.I) := hKc.comp_continuous hline hmem
  have hc2 : Continuous fun v : ℝ => liftSymbol X δ₀ m ((1 : ℂ) + (v : ℂ) * Complex.I) :=
    (liftSymbol_continuousOn hX δ₀ m).comp_continuous hline fun v => by simp
  refine (integrable_weight (BK * CW)).mono' (hc1.mul hc2).aestronglyMeasurable (ae_of_all _ fun v => ?_)
  rw [norm_mul]
  have := hW (w := (1 : ℂ) + (v : ℂ) * Complex.I) (by simp)
  simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
    Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add] at this
  calc ‖Kf ((1 : ℂ) + (v : ℂ) * Complex.I)‖ * ‖liftSymbol X δ₀ m ((1 : ℂ) + (v : ℂ) * Complex.I)‖
      ≤ BK * (CW * (1 + |v|) ^ (-(5 / 2 : ℝ))) :=
        mul_le_mul (hKb _ (by simp) (by simp)) this (norm_nonneg _) hBK
    _ = _ := by ring

lemma mem_edgeStrip_scaled {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {w : ℂ} (h1 : w.re ≤ 1) (h0 : 0 ≤ w.re) :
    (ε : ℂ) * w ∈ edgeStrip := by
  simp only [edgeStrip, Set.mem_ofPred_eq, Complex.re_ofReal_mul]
  rw [abs_of_nonneg (mul_nonneg hε.le h0)]
  nlinarith

theorem K0_kernel_props {c ε ξ S : ℝ} (hε : 0 < ε) (hcube : c * ε ^ 3 = 1) (hε2 : ε ≤ 1 / 2) (hξ : 0 < ξ)
    (hL : Real.log (Real.pi ^ 2 * ξ) = Real.pi ^ 2 * ε ^ 2 * S) :
    ContinuousOn (fun w : ℂ => mellinK0 c ((ε : ℂ) * w) ξ) {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1} ∧
    DifferentiableOn ℂ (fun w : ℂ => mellinK0 c ((ε : ℂ) * w) ξ) {w : ℂ | 0 < w.re ∧ w.re < 1} ∧
    ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → ‖mellinK0 c ((ε : ℂ) * w) ξ‖ ≤ 2 * Real.exp (1 + Real.pi ^ 2 * |S|) := by
  have hc := eps_cube_inv hε hcube
  have hD := differentiableOn_mellinK0 hc ξ
  have hlin : Differentiable ℂ (fun w : ℂ => (ε : ℂ) * w) := differentiable_const _ |>.mul differentiable_id
  have hε1 : ε < 1 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · exact (DifferentiableOn.comp (s := {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1}) hD hlin.differentiableOn
      fun w hw => mem_edgeStrip_scaled hε hε1 hw.2 hw.1).continuousOn
  · exact DifferentiableOn.comp (s := {w : ℂ | 0 < w.re ∧ w.re < 1}) hD hlin.differentiableOn
      fun w hw => mem_edgeStrip_scaled hε hε1 hw.2.le hw.1.le
  · intro w h0 h1
    have := norm_K0_strip_le (c := c) (ε := ε) (ξ := ξ) (S := S) (σ := w.re) (v := w.im) hε hcube hε2 hξ hL h0 h1
    rwa [Complex.re_add_im] at this

lemma exp_matches (S ε v : ℝ) :
    refKernel S ε ((v : ℂ) * Complex.I) =
      Complex.exp (Complex.I * (((Real.pi ^ 2 * S + ε / 2) * v - Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) := by
  unfold refKernel
  congr 1
  have : ((v : ℂ) * Complex.I) ^ 3 = -(((v : ℂ) ^ 3) * Complex.I) := by
    calc ((v : ℂ) * Complex.I) ^ 3 = (v : ℂ) ^ 3 * (Complex.I ^ 2 * Complex.I) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [this]; push_cast; ring

lemma liftEps_le_of_large {c : ℝ} (hc : 32768 ≤ c) : liftEps c ≤ 1 / 32 := by
  have hc0 : 0 < c := by linarith
  have hε := liftEps_pos hc0
  have h3 := liftEps_cube_mul hc0
  by_contra hlt
  push Not at hlt
  have h1 : (1 / 32 : ℝ) ^ 3 < liftEps c ^ 3 := pow_lt_pow_left₀ hlt (by norm_num) (by norm_num)
  nlinarith [h3]

/-- **`O.5`(1), main part.**  `I_main` equals the reference integral up to `(2πξ)⁻¹ C ε²`; `C` depends only on
`m`, the bound `S_w` of `|S|` and the constant `C_W` of the lift-symbol bound. -/
theorem window_main_approx (m : ℕ) (Sw CW : ℝ) (hCW : 0 < CW) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : ℝ → ℝ}, HasU2 X →
      (∀ {δ₀ : ℝ} {w : ℂ}, 0 ≤ δ₀ → 0 ≤ w.re → ‖liftSymbol X δ₀ m w‖ ≤ CW * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) →
      ∀ {δ₀ c ξ : ℝ}, 0 ≤ δ₀ → 32768 ≤ c → 0 < ξ → |hbS c ξ| ≤ Sw →
      ‖iMain X δ₀ m c ξ - ((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, liftSymbol X δ₀ m ((v : ℂ) * Complex.I) *
          Complex.exp (Complex.I * (((Real.pi ^ 2 * hbS c ξ + liftEps c / 2) * v - Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ))‖ ≤
        (2 * Real.pi * ξ)⁻¹ * (C * liftEps c ^ 2) := by
  obtain ⟨C, hC, hmain⟩ := main_line_diff m Sw CW hCW
  refine ⟨C, hC, fun {X} hX hW {δ₀ c ξ} hδ hc hξ hS => ?_⟩
  have hc0 : 0 < c := by linarith
  set ε := liftEps c with hεdef
  have hε := liftEps_pos hc0
  have hcube : c * ε ^ 3 = 1 := by have := liftEps_cube_mul hc0; linarith
  have hε1 := liftEps_le_of_large hc
  have hε2 : ε ≤ 1 / 2 := by linarith
  set S := hbS c ξ with hSdef
  have hL : Real.log (Real.pi ^ 2 * ξ) = Real.pi ^ 2 * ε ^ 2 * S := hb_L_eq hc0
  have hW' : ∀ {w : ℂ}, 0 ≤ w.re → ‖liftSymbol X δ₀ m w‖ ≤ CW * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) :=
    fun {w} h => hW hδ h
  obtain ⟨hKc, hKd, hKb⟩ := K0_kernel_props (c := c) (S := S) hε hcube hε2 hξ hL
  have hBK : 0 ≤ 2 * Real.exp (1 + Real.pi ^ 2 * |S|) := by positivity
  have hRdiff : Differentiable ℂ (refKernel S ε) := by unfold refKernel; fun_prop
  have hRb : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 → ‖refKernel S ε w‖ ≤ Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * Sw + 1) := by
    intro w h0 h1
    have := norm_refKernel_strip_le (S := S) (ε := ε) (σ := w.re) (v := w.im) (Sw := Sw) (by linarith) hS h0 h1
    rwa [Complex.re_add_im] at this
  have hRBK : 0 ≤ Real.exp (Real.pi ^ 2 / 36 + Real.pi ^ 2 * Sw + 1) := (Real.exp_pos _).le
  have sh1 := shift_kernel_lift hX hδ m hW' hKc hKd hKb
  have sh2 := shift_kernel_lift hX hδ m hW' hRdiff.continuous.continuousOn hRdiff.differentiableOn hRb
  have int1 := integrable_kernel_lift hX m hW' hKc hKb hBK
  have int2 := integrable_kernel_lift hX m hW' hRdiff.continuous.continuousOn hRb hRBK
  have hdiff := hmain hW hδ hε hcube hε1 hξ hL hS
  have e1 : ∫ v : ℝ, iMainIntegrand X δ₀ m c ξ v =
      ∫ v : ℝ, mellinK0 c ((ε : ℂ) * ((v : ℂ) * Complex.I)) ξ * liftSymbol X δ₀ m ((v : ℂ) * Complex.I) := by
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    unfold iMainIntegrand
    simp only [hεdef]
    congr 2; push_cast; ring
  have e2 : ∫ v : ℝ, liftSymbol X δ₀ m ((v : ℂ) * Complex.I) *
      Complex.exp (Complex.I * (((Real.pi ^ 2 * S + ε / 2) * v - Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) =
      ∫ v : ℝ, refKernel S ε ((v : ℂ) * Complex.I) * liftSymbol X δ₀ m ((v : ℂ) * Complex.I) := by
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    show _ = _
    simp only []
    rw [exp_matches, mul_comm]
  have e3 : iMain X δ₀ m c ξ - ((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, liftSymbol X δ₀ m ((v : ℂ) * Complex.I) *
      Complex.exp (Complex.I * (((Real.pi ^ 2 * S + ε / 2) * v - Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) =
      ((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, (mellinK0 c ((ε : ℂ) * ((1 : ℂ) + (v : ℂ) * Complex.I)) ξ -
            refKernel S ε ((1 : ℂ) + (v : ℂ) * Complex.I)) * liftSymbol X δ₀ m ((1 : ℂ) + (v : ℂ) * Complex.I) := by
    unfold iMain
    rw [e1, e2, ← mul_sub]
    congr 1
    simp only [sub_mul]
    rw [integral_sub int1 int2, sh1, sh2]
  rw [e3, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  gcongr

/-- info: 'FormalResearch.SignUncertainty.window_main_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms window_main_approx

/-! ### The dual term -/

lemma norm_liftMultiplier_le {δ₀ : ℝ} (hδ : 0 ≤ δ₀) {m : ℕ} (hm : 1 ≤ m) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖liftMultiplier δ₀ m w‖ ≤ (3 / min 1 (ceCs / m)) ^ m * ((1 + δ₀ * w.re) ^ m)⁻¹ := by
  unfold liftMultiplier
  rw [norm_pow]
  set a : ℝ := ceCs * δ₀ / m with ha
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have ha0 : 0 ≤ a := by rw [ha]; have := ceCs_pos; positivity
  set μ : ℝ := min 1 (ceCs / m) with hμ
  have hμ0 : 0 < μ := lt_min one_pos (div_pos ceCs_pos hm0)
  have hre : 0 ≤ (((a : ℝ) : ℂ) * w).re := by rw [Complex.re_ofReal_mul]; exact mul_nonneg ha0 hw
  have h3 := (norm_iteratedDeriv_bsplineE1_le 0 hre).2.2
  rw [iteratedDeriv_zero] at h3
  have hnorm : a * w.re ≤ ‖((a : ℝ) : ℂ) * w‖ := by
    have := Complex.re_le_norm (((a : ℝ) : ℂ) * w)
    rwa [Complex.re_ofReal_mul] at this
  have hlow : μ * (1 + δ₀ * w.re) ≤ 1 + ‖((a : ℝ) : ℂ) * w‖ := by
    have h1 : μ ≤ 1 := min_le_left _ _
    have h2 : μ ≤ ceCs / m := min_le_right _ _
    have : μ * (δ₀ * w.re) ≤ a * w.re := by
      rw [ha]
      calc μ * (δ₀ * w.re) ≤ (ceCs / m) * (δ₀ * w.re) := by gcongr
        _ = ceCs * δ₀ / m * w.re := by ring
    nlinarith [mul_nonneg hδ hw]
  have hbase : ‖bsplineE1 (((a : ℝ) : ℂ) * w)‖ ≤ 3 / (μ * (1 + δ₀ * w.re)) := by
    have h3' : ‖bsplineE1 (((a : ℝ) : ℂ) * w)‖ ≤ 3 / (1 + ‖((a : ℝ) : ℂ) * w‖) := by simpa using h3
    refine h3'.trans ?_
    have : 0 < μ * (1 + δ₀ * w.re) := by positivity
    exact div_le_div_of_nonneg_left (by norm_num) this hlow
  calc ‖bsplineE1 (((a : ℝ) : ℂ) * w)‖ ^ m ≤ (3 / (μ * (1 + δ₀ * w.re))) ^ m :=
        pow_le_pow_left₀ (norm_nonneg _) hbase m
    _ = (3 / μ) ^ m * ((1 + δ₀ * w.re) ^ m)⁻¹ := by
        have : 3 / (μ * (1 + δ₀ * w.re)) = (3 / μ) * (1 + δ₀ * w.re)⁻¹ := by field_simp
        rw [this, mul_pow, inv_pow]

theorem dual_bound_window (m : ℕ) (hm : 1 ≤ m) (CD : ℝ) (hCD : 0 < CD) :
    ∃ C : ℝ, 0 < C ∧ ∀ {D : ℝ → ℝ},
      (∀ {w : ℂ}, 0 ≤ w.re → ‖airyTwistedLaplaceC D ((ceCs : ℂ) * w)‖ ≤ CD * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) →
      ∀ {δ₀ c ξ : ℝ}, 0 ≤ δ₀ → 0 < c → 0 < ξ →
      ‖iDual D δ₀ m c ξ‖ ≤ (2 * Real.pi * ξ)⁻¹ * (C * ((1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ * c ^ (-(1 / 2 : ℝ))) := by
  set J : ℝ := ∫ u : ℝ, (1 + |u|) ^ (-(5 / 2 : ℝ)) with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun v => Real.rpow_nonneg (by positivity) _
  set A : ℝ := (3 / min 1 (ceCs / m)) ^ m with hA
  have hA0 : 0 ≤ A := by
    have : 0 < min 1 (ceCs / (m : ℝ)) := lt_min one_pos (div_pos ceCs_pos (by exact_mod_cast hm))
    positivity
  refine ⟨A * CD * 2 ^ (5 / 2 : ℝ) * J + 1, by positivity, fun {D} hD {δ₀ c ξ} hδ hc hξ => ?_⟩
  set R : ℝ := c ^ (1 / 3 : ℝ) with hR
  have hR0 : 0 < R := Real.rpow_pos_of_pos hc _
  have hpt : ∀ v : ℝ, ‖iDualIntegrand D δ₀ m c ξ v‖ ≤
      A * CD * 2 ^ (5 / 2 : ℝ) * R ^ (-(5 / 2 : ℝ)) * ((1 + δ₀ * R) ^ m)⁻¹ * (1 + |R⁻¹ * v|) ^ (-(5 / 2 : ℝ)) := by
    intro v
    unfold iDualIntegrand
    rw [norm_mul]
    have hK : ‖mellinK0 c (((liftEps c * v : ℝ) : ℂ) * Complex.I) ξ‖ ≤ 1 :=
      ((norm_mellinK0_imag_le hc hξ _).2).trans (Real.rpow_le_one_of_one_le_of_nonpos
        (by nlinarith [sq_nonneg (liftEps c * v)]) (by norm_num))
    set w : ℂ := ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) - (v : ℂ) * Complex.I with hw
    have hwre : w.re = R := by simp [hw, hR]
    have hwim : w.im = -v := by simp [hw]
    have hM := norm_liftMultiplier_le hδ hm (w := w) (by rw [hwre]; exact hR0.le)
    rw [hwre] at hM
    have hD' := hD (w := w) (by rw [hwre]; exact hR0.le)
    have hn1 : ‖1 + w‖ ^ (-(5 / 2 : ℝ)) ≤ 2 ^ (5 / 2 : ℝ) * R ^ (-(5 / 2 : ℝ)) * (1 + |R⁻¹ * v|) ^ (-(5 / 2 : ℝ)) := by
      have h1 : R * (1 + |R⁻¹ * v|) = R + |v| := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr hR0)]; field_simp
      have hlow : R * (1 + |R⁻¹ * v|) / 2 ≤ ‖1 + w‖ := by
        rw [h1]
        have hre' : R ≤ (1 + w).re := by simp [hwre]
        have him' : |v| = |(1 + w).im| := by simp [hwim]
        have hn : ‖1 + w‖ ^ 2 = (1 + w).re ^ 2 + (1 + w).im ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; ring
        have hsq : (R + |v|) ^ 2 ≤ 4 * ‖1 + w‖ ^ 2 := by
          rw [hn, him']
          have : R ^ 2 ≤ (1 + w).re ^ 2 := by nlinarith
          nlinarith [sq_abs (1 + w).im, sq_nonneg (R - |(1 + w).im|)]
        by_contra hcon
        push Not at hcon
        nlinarith [norm_nonneg (1 + w)]
      have hpos : 0 < R * (1 + |R⁻¹ * v|) / 2 := by positivity
      calc ‖1 + w‖ ^ (-(5 / 2 : ℝ)) ≤ (R * (1 + |R⁻¹ * v|) / 2) ^ (-(5 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos hpos hlow (by norm_num)
        _ = 2 ^ (5 / 2 : ℝ) * R ^ (-(5 / 2 : ℝ)) * (1 + |R⁻¹ * v|) ^ (-(5 / 2 : ℝ)) := by
            rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) , div_inv_eq_mul,
              Real.mul_rpow hR0.le (by positivity)]
            ring
    have hL : ‖liftSymbol D δ₀ m w‖ ≤ A * ((1 + δ₀ * R) ^ m)⁻¹ * (CD * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) := by
      unfold liftSymbol
      rw [norm_mul]
      exact mul_le_mul hM hD' (norm_nonneg _) (by positivity)
    calc ‖mellinK0 c (((liftEps c * v : ℝ) : ℂ) * Complex.I) ξ‖ * ‖liftSymbol D δ₀ m w‖
        ≤ 1 * (A * ((1 + δ₀ * R) ^ m)⁻¹ * (CD * (2 ^ (5 / 2 : ℝ) * R ^ (-(5 / 2 : ℝ)) * (1 + |R⁻¹ * v|) ^ (-(5 / 2 : ℝ))))) := by
          refine mul_le_mul hK (hL.trans ?_) (norm_nonneg _) zero_le_one
          gcongr
      _ = _ := by ring
  have hgint : Integrable fun v : ℝ => (1 + |R⁻¹ * v|) ^ (-(5 / 2 : ℝ)) :=
    integrable_one_add_abs_rpow.comp_mul_left' (inv_ne_zero hR0.ne')
  have hbint : Integrable fun v : ℝ => A * CD * 2 ^ (5 / 2 : ℝ) * R ^ (-(5 / 2 : ℝ)) * ((1 + δ₀ * R) ^ m)⁻¹ *
      (1 + |R⁻¹ * v|) ^ (-(5 / 2 : ℝ)) := hgint.const_mul _
  have hI : ‖∫ v : ℝ, iDualIntegrand D δ₀ m c ξ v‖ ≤
      A * CD * 2 ^ (5 / 2 : ℝ) * R ^ (-(5 / 2 : ℝ)) * ((1 + δ₀ * R) ^ m)⁻¹ * (R * J) := by
    refine (norm_integral_le_of_norm_le hbint (ae_of_all _ hpt)).trans (le_of_eq ?_)
    rw [integral_const_mul, Measure.integral_comp_mul_left (fun u : ℝ => (1 + |u|) ^ (-(5 / 2 : ℝ))) R⁻¹, inv_inv,
      abs_of_pos hR0, smul_eq_mul]
  have hRpow : R ^ (-(5 / 2 : ℝ)) * R = c ^ (-(1 / 2 : ℝ)) := by
    rw [hR, ← Real.rpow_mul hc.le, ← Real.rpow_add hc]
    norm_num
  unfold iDual
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hX0 : 0 ≤ ((1 + δ₀ * R) ^ m)⁻¹ := by positivity
  have hcpow : 0 ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hc.le _
  gcongr
  calc _ ≤ _ := hI
    _ = (A * CD * 2 ^ (5 / 2 : ℝ) * J) * ((1 + δ₀ * R) ^ m)⁻¹ * (R ^ (-(5 / 2 : ℝ)) * R) := by ring
    _ = (A * CD * 2 ^ (5 / 2 : ℝ) * J) * ((1 + δ₀ * R) ^ m)⁻¹ * c ^ (-(1 / 2 : ℝ)) := by rw [hRpow]
    _ ≤ _ := by
        have : 0 ≤ ((1 + δ₀ * R) ^ m)⁻¹ * c ^ (-(1 / 2 : ℝ)) := mul_nonneg hX0 hcpow
        nlinarith

/-- info: 'FormalResearch.SignUncertainty.dual_bound_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dual_bound_window

/-! ### `O.5`(1): the window translation `(e5)` -/

/-- **`O.5`(1), `(e5)`, uniform form.**  For `m ≥ 1`, `S_w`, and the constants `C_W`, `C_D` of the `U.2` right-half-plane bounds of
the main seed `X` (through `‖W_X(w)‖ ≤ C_W (1 + |Im w|)^{-5/2}`) and of the dual seed `D` (`‖D̃(c_s w)‖ ≤ C_D ‖1 + w‖^{-5/2}`), there is
`C` such that for `δ₀ ≥ 0`, `c ≥ 32768`, `ξ > 0` and `|S_eff(ξ)| ≤ S_w`,
`|I_main[X] + I_dual[D] - (k β₁/(π² ξ)) F_ψ(-β₁ S - ε/(2 c_s))| ≤ C ξ⁻¹ [ε² + (1 + δ₀ c^{1/3})^{-m} c^{-1/2}]`.
`C` is chosen after `(m, S_w, C_W, C_D)` and before `X, D, δ₀, c, ξ`, so it is uniform over every family of seeds with these constants.
Differences from the paper statement: the threshold `c ≥ 32768` (`ε ≤ 1/32`) replaces `c ≥ 200` (the range `200 ≤ c < 32768` is not
formalised; the paper's later uses of `(e5)` are asymptotic in `c`); `δ₀ ≥ 0` is arbitrary (paper: `δ₀ ∈ (0, 2]`) and `S_w` is any real
(paper: `S_w ≥ 1`); the seed `X` is assumed continuous (used by `airy_reference_identity`); the dual seed `D` enters only through the
stated bound (no `HasU2 D` is needed here); `HasU2 X` is used only qualitatively (integrability, holomorphy), never through a constant.
The bounded-family constants `C_W, C_D` are hypotheses: deriving them from a family (the Phragmén–Lindelöf step of `u1c:U2`) is not
part of this file (for one fixed seed see `window_translation_seed`). -/
theorem window_translation (m : ℕ) (hm : 1 ≤ m) (Sw CW CD : ℝ) (hCW : 0 < CW) (hCD : 0 < CD) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X D : ℝ → ℝ}, HasU2 X → Continuous X →
      (∀ {δ₀ : ℝ} {w : ℂ}, 0 ≤ δ₀ → 0 ≤ w.re → ‖liftSymbol X δ₀ m w‖ ≤ CW * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) →
      (∀ {w : ℂ}, 0 ≤ w.re → ‖airyTwistedLaplaceC D ((ceCs : ℂ) * w)‖ ≤ CD * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) →
      ∀ {δ₀ c ξ : ℝ}, 0 ≤ δ₀ → 32768 ≤ c → 0 < ξ → |hbS c ξ| ≤ Sw →
      ‖iMain X δ₀ m c ξ + iDual D δ₀ m c ξ -
          ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * windowSmooth δ₀ m X (-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs)) : ℝ) : ℂ)‖ ≤
        C * ξ⁻¹ * (liftEps c ^ 2 + ((1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ * c ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨C₁, hC₁, hmain⟩ := window_main_approx m Sw CW hCW
  obtain ⟨C₂, hC₂, hdual⟩ := dual_bound_window m hm CD hCD
  refine ⟨(C₁ + C₂) / (2 * Real.pi), by positivity, fun {X D} hX hXc hW hD {δ₀ c ξ} hδ hc hξ hS => ?_⟩
  have hc0 : 0 < c := by linarith
  have hε := liftEps_pos hc0
  have h1 := hmain hX hW hδ hc hξ hS
  have h2 := hdual hD hδ hc0 hξ
  have href := airy_reference_identity hX hXc hδ m hξ (Real.pi ^ 2 * hbS c ξ + liftEps c / 2)
  have hcs := ceCs_pos
  have hcm := ceCs_mul_ceBeta1
  have ha : -((Real.pi ^ 2 * hbS c ξ + liftEps c / 2) / ceCs) = -(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs) := by
    have : Real.pi ^ 2 = ceCs * ceBeta1 := hcm.symm
    rw [this]; field_simp; ring
  have hk : (ceK : ℂ) / ((ceCs : ℂ) * (ξ : ℂ)) = ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) : ℝ) : ℂ) := by
    have : Real.pi ^ 2 = ceCs * ceBeta1 := hcm.symm
    have hb := ceBeta1_pos
    have hb' : (ceBeta1 : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    rw [this]; push_cast
    field_simp
  rw [ha, hk] at href
  have hT : ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * windowSmooth δ₀ m X (-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs)) : ℝ) : ℂ) =
      ((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, liftSymbol X δ₀ m ((v : ℂ) * Complex.I) *
          Complex.exp (Complex.I * (((Real.pi ^ 2 * hbS c ξ + liftEps c / 2) * v - Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) := by
    rw [href]; push_cast; ring
  rw [hT]
  have e : iMain X δ₀ m c ξ + iDual D δ₀ m c ξ - ((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, liftSymbol X δ₀ m ((v : ℂ) * Complex.I) *
          Complex.exp (Complex.I * (((Real.pi ^ 2 * hbS c ξ + liftEps c / 2) * v - Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) =
      (iMain X δ₀ m c ξ - ((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ * ∫ v : ℝ, liftSymbol X δ₀ m ((v : ℂ) * Complex.I) *
          Complex.exp (Complex.I * (((Real.pi ^ 2 * hbS c ξ + liftEps c / 2) * v - Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ))) +
        iDual D δ₀ m c ξ := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have hpi := Real.pi_pos
  have hX0 : 0 ≤ ((1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ := by positivity
  have hcp : 0 ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hc0.le _
  have hid : (2 * Real.pi * ξ)⁻¹ = (2 * Real.pi)⁻¹ * ξ⁻¹ := by rw [mul_inv]
  calc _ ≤ (2 * Real.pi * ξ)⁻¹ * (C₁ * liftEps c ^ 2) +
        (2 * Real.pi * ξ)⁻¹ * (C₂ * ((1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ * c ^ (-(1 / 2 : ℝ))) := add_le_add h1 h2
    _ = (C₁ + C₂) / (2 * Real.pi) * ξ⁻¹ * 0 + (2 * Real.pi)⁻¹ * ξ⁻¹ * (C₁ * liftEps c ^ 2 + C₂ * (((1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ * c ^ (-(1 / 2 : ℝ)))) := by
        rw [hid]; ring
    _ ≤ _ := by
        have hξ0 : 0 ≤ ξ⁻¹ := by positivity
        have hq : 0 ≤ ((1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ * c ^ (-(1 / 2 : ℝ)) := mul_nonneg hX0 hcp
        have hε2 : 0 ≤ liftEps c ^ 2 := by positivity
        have : (2 * Real.pi)⁻¹ * (C₁ * liftEps c ^ 2 + C₂ * (((1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ * c ^ (-(1 / 2 : ℝ)))) ≤
            (C₁ + C₂) / (2 * Real.pi) * (liftEps c ^ 2 + ((1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ * c ^ (-(1 / 2 : ℝ))) := by
          have h2π : 0 < (2 * Real.pi)⁻¹ := by positivity
          calc (2 * Real.pi)⁻¹ * (C₁ * liftEps c ^ 2 + C₂ * (((1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ * c ^ (-(1 / 2 : ℝ))))
              ≤ (2 * Real.pi)⁻¹ * ((C₁ + C₂) * (liftEps c ^ 2 + ((1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ * c ^ (-(1 / 2 : ℝ)))) := by
                gcongr
                linarith only [mul_nonneg hC₁.le hq, mul_nonneg hC₂.le hε2]
            _ = _ := by field_simp
        linarith only [mul_le_mul_of_nonneg_left this hξ0]

/-- **`O.5`(1), `(e5)`, for fixed seeds.**  For seeds `X, D` with `HasU2` (and `X` continuous), `m ≥ 1` and any `S_w`, there is
`C` (depending on `X, D, m, S_w`) with the estimate of `window_translation` for all `δ₀ ≥ 0`, `c ≥ 32768`, `ξ > 0`, `|S_eff(ξ)| ≤ S_w`;
the constants `C_W, C_D` come from `hasU2_norm_liftSymbol_le_unif` and `HasU2.rhp`. -/
theorem window_translation_seed {X D : ℝ → ℝ} (hX : HasU2 X) (hXc : Continuous X) (hD : HasU2 D) (m : ℕ) (hm : 1 ≤ m) (Sw : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {δ₀ c ξ : ℝ}, 0 ≤ δ₀ → 32768 ≤ c → 0 < ξ → |hbS c ξ| ≤ Sw →
      ‖iMain X δ₀ m c ξ + iDual D δ₀ m c ξ -
          ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * windowSmooth δ₀ m X (-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs)) : ℝ) : ℂ)‖ ≤
        C * ξ⁻¹ * (liftEps c ^ 2 + ((1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ * c ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨CW, hCW, hW⟩ := hasU2_norm_liftSymbol_le_unif hX
  obtain ⟨CD, hCD, hDb⟩ := hD.rhp
  obtain ⟨C, hC, h⟩ := window_translation m hm Sw CW CD hCW hCD
  exact ⟨C, hC, fun {δ₀ c ξ} hδ hc hξ hS => h hX hXc (fun {δ₀'} {w} h0 h1 => hW m h0 h1) (fun {w} hw => hDb w hw) hδ hc hξ hS⟩

/-- info: 'FormalResearch.SignUncertainty.window_translation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms window_translation
/-- info: 'FormalResearch.SignUncertainty.window_translation_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms window_translation_seed

/-- info: 'FormalResearch.SignUncertainty.main_line_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms main_line_diff
/-- info: 'FormalResearch.SignUncertainty.shift_kernel_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms shift_kernel_lift

end FormalResearch.SignUncertainty
