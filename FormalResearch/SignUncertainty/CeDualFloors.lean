module

public import FormalResearch.SignUncertainty.AiryLaplaceGeneral
public import FormalResearch.SignUncertainty.GenRationalAiryTail
public import FormalResearch.SignUncertainty.GenRationalAiryU1
public import FormalResearch.SignUncertainty.WindowTranslation
public import FormalResearch.SignUncertainty.UctPosFloorWpos
public import FormalResearch.SignUncertainty.UctAiryTransSmall

/-!
# Dual-line floors and relative strip helpers (`eq:ce-dual-floors`)

Source: `CFT/sign_uncertainty/paper/ce_lift_proofs.tex`, `(eq:ce-dual-floors)` and helpers for
Lemma `lem:ce-dual-line`.

* `airyTwistedLaplaceC_zero_eq`: exact evaluation `X̃(0) = k ∫_ℝ X(u) du`.
* `ce_dual_floors` (`eq:ce-dual-floors`): for any `X ∈ ℛ_Ai^gen` with `∫ X = 0`, `β_∞(X) < 0`, and
  `β_+(X) > 0`, there exist `0 < x₀ < B`, `c₁', d₀ > 0` with `c₁' √x ≤ X̃(c_s x)` on `[0, x₀]`
  and `d₀ (1 + x)^{-5/2} ≤ X̃(c_s x)` on `[B/2, ∞)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

lemma norm_cpow_half_eq {y : ℂ} :
    ‖y ^ (1 / 2 : ℂ)‖ = ‖y‖ ^ (1 / 2 : ℝ) := by
  by_cases hy0 : y = 0
  · simp [hy0]
  · rw [Complex.norm_cpow_of_ne_zero hy0]
    have hre : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
    have him : (1 / 2 : ℂ).im = 0 := by norm_num
    rw [hre, him, mul_zero, Real.exp_zero, div_one]

lemma e1r_lower {t : ℝ} (ht : 0 ≤ t) : (1 + t)⁻¹ ≤ uctE1r t := by
  rcases eq_or_lt_of_le ht with rfl | ht0
  · have : uctE1r 0 = 1 := by
      have h0 := uctE1r_cast 0
      simp only [Complex.ofReal_zero, bsplineE1_zero] at h0
      exact Complex.ofReal_injective h0.symm
    simp [this]
  · have hexp : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    have hexp' : Real.exp (-t) * (1 + t) ≤ 1 := by
      calc Real.exp (-t) * (1 + t) ≤ Real.exp (-t) * Real.exp t :=
            mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have hmul := uctE1r_mul t
    have h1 : t ≤ (1 + t) * (1 - Real.exp (-t)) := by nlinarith
    rw [← hmul] at h1
    have h2 : (1 + t)⁻¹ * t ≤ uctE1r t * t := by
      calc (1 + t)⁻¹ * t = t * (1 + t)⁻¹ := by ring
        _ ≤ ((1 + t) * (uctE1r t * t)) * (1 + t)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = uctE1r t * t := by field_simp [show (1 + t) ≠ 0 by positivity]
    exact le_of_mul_le_mul_right h2 ht0

/-- Evaluation of `airyTwistedLaplaceC` at `w = 0`. -/
lemma airyTwistedLaplaceC_zero_eq (X : ℝ → ℝ) :
    airyTwistedLaplaceC X 0 = ((ceK * ∫ u : ℝ, X u : ℝ) : ℂ) := by
  unfold airyTwistedLaplaceC
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_div,
    Complex.exp_zero, mul_one, zero_mul]
  rw [integral_complex_ofReal]
  push_cast; rfl

/-- **`eq:ce-dual-floors` (`ce_lift_proofs.tex`):** positive-real dual-line floors near `x = 0` (`x^{1/2}`)
and at infinity (`(1 + x)^{-5/2}`) for any `F ∈ ℛ_Ai^gen` with `∫ X = 0`, `β_∞(F) < 0`, and
`β_+(F) > 0`. -/
theorem ce_dual_floors {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ} (hF : HasGenRationalAiryCoeffs F β₀₀ β₁₁)
    (hmass : ∫ u : ℝ, (F (u : ℂ)).re = 0)
    (hbinf : airyBetaInf F < 0) (hbplus : 0 < airyBetaPlus F) :
    ∃ x₀ B c₁' d₀ : ℝ, 0 < x₀ ∧ x₀ < B ∧ 0 < c₁' ∧ 0 < d₀ ∧
      (∀ x ∈ Icc (0 : ℝ) x₀, c₁' * Real.sqrt x ≤ (airyTwistedLaplaceC (fun u => (F (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ)).re) ∧
      (∀ x : ℝ, B / 2 ≤ x → d₀ * (1 + x) ^ (-(5 / 2 : ℝ)) ≤
        (airyTwistedLaplaceC (fun u => (F (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ)).re) := by
  let X : ℝ → ℝ := fun u => (F (u : ℂ)).re
  obtain ⟨_, _, hβinf, _⟩ := hF.beta_eq
  have hβinf_neg : β₀₀ + β₁₁ < 0 := by linarith
  obtain ⟨C₀, hC₀, hexp⟩ := u1c_expansion_of_genRational hF ceCs ceCs_pos.le
  let c_lead : ℝ := -(β₀₀ + β₁₁) * (2 * ceK * cA) * Real.sqrt ceCs
  have hc_lead : 0 < c_lead := by
    have := ceK_pos; have := cA_pos; have := ceCs_pos; have : 0 < -(β₀₀ + β₁₁) := by linarith
    positivity
  let denom : ℝ := 2 * (C₀ * ceCs + 1)
  have hdenom : 0 < denom := by have := ceCs_pos; positivity
  let x₀ : ℝ := min 1 ((c_lead / denom) ^ 2)
  have hx₀ : 0 < x₀ := lt_min one_pos (by positivity)
  have hsmall : ∀ x ∈ Icc (0 : ℝ) x₀, (c_lead / 2) * Real.sqrt x ≤
      (airyTwistedLaplaceC X ((ceCs * x : ℝ) : ℂ)).re := by
    intro x ⟨hx0, hxx₀⟩
    have hx1 : x ≤ 1 := hxx₀.trans (min_le_left _ _)
    have hx_le : Real.sqrt x ≤ c_lead / denom := by
      have hsq : x ≤ (c_lead / denom) ^ 2 := hxx₀.trans (min_le_right _ _)
      exact (Real.sqrt_le_sqrt hsq).trans (Real.sqrt_sq (by positivity)).le
    let y : ℂ := ((ceCs * x : ℝ) : ℂ)
    have hyre : 0 ≤ y.re := by simp [y]; exact mul_nonneg ceCs_pos.le hx0
    have hynorm : ‖y‖ ≤ ceCs := by
      rw [show y = ((ceCs * x : ℝ) : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg ceCs_pos.le hx0)]
      exact mul_le_of_le_one_right ceCs_pos.le hx1
    have h0eq : airyTwistedLaplaceC X 0 = 0 := by rw [airyTwistedLaplaceC_zero_eq]; simp [X, hmass]
    have hpow : (y ^ (1 / 2 : ℂ) : ℂ) = ((Real.sqrt (ceCs * x) : ℝ) : ℂ) := by
      dsimp [y]
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_cpow (mul_nonneg ceCs_pos.le hx0), Real.sqrt_eq_rpow]
    have hbd : ‖airyTwistedLaplaceC X y + (((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) *
        ((Real.sqrt (ceCs * x) : ℝ) : ℂ)‖ ≤ C₀ * ‖y‖ := by
      have h1 := hexp hyre hynorm
      change ‖airyTwistedLaplaceC X y - airyTwistedLaplaceC X 0 +
          (((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)‖ ≤ C₀ * ‖y‖ at h1
      rwa [h0eq, sub_zero, hpow] at h1
    have hre_bd : |(airyTwistedLaplaceC X y).re + (β₀₀ + β₁₁) * (2 * ceK * cA) * Real.sqrt (ceCs * x)| ≤
        C₀ * (ceCs * x) := by
      have hab := Complex.abs_re_le_norm (airyTwistedLaplaceC X y +
        (((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) * ((Real.sqrt (ceCs * x) : ℝ) : ℂ))
      have hre_eq : (airyTwistedLaplaceC X y + (((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) *
            ((Real.sqrt (ceCs * x) : ℝ) : ℂ)).re =
          (airyTwistedLaplaceC X y).re + (β₀₀ + β₁₁) * (2 * ceK * cA) * Real.sqrt (ceCs * x) := by
        simp [Complex.add_re, Complex.mul_re]
      have hyabs : ‖y‖ = ceCs * x := by
        rw [show y = ((ceCs * x : ℝ) : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg ceCs_pos.le hx0)]
      rw [hre_eq] at hab; rw [hyabs] at hbd; exact hab.trans hbd
    have hre_lower : c_lead * Real.sqrt x - C₀ * ceCs * x ≤ (airyTwistedLaplaceC X y).re := by
      have := (abs_le.mp hre_bd).1
      dsimp [c_lead]
      rw [Real.sqrt_mul ceCs_pos.le x] at this
      linarith
    have hx_err : C₀ * ceCs * x ≤ (c_lead / 2) * Real.sqrt x := by
      have h1 : C₀ * ceCs * Real.sqrt x ≤ (C₀ * ceCs + 1) * (c_lead / denom) := by
        calc C₀ * ceCs * Real.sqrt x ≤ (C₀ * ceCs + 1) * Real.sqrt x := by
              nlinarith [Real.sqrt_nonneg x]
          _ ≤ (C₀ * ceCs + 1) * (c_lead / denom) :=
              mul_le_mul_of_nonneg_left hx_le (by have := ceCs_pos; positivity)
      have h2 : (C₀ * ceCs + 1) * (c_lead / denom) = c_lead / 2 := by
        dsimp [denom]
        have hne : C₀ * ceCs + 1 ≠ 0 := by have := ceCs_pos; positivity
        field_simp [hne]
      calc C₀ * ceCs * x = C₀ * ceCs * (Real.sqrt x * Real.sqrt x) := by rw [Real.mul_self_sqrt hx0]
        _ = (C₀ * ceCs * Real.sqrt x) * Real.sqrt x := by ring
        _ ≤ (c_lead / 2) * Real.sqrt x := by
            rw [← h2]; exact mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg x)
    linarith
  let L_pos : ℝ := airyBetaPlus F * (2 / Real.sqrt Real.pi)
  have hL_pos : 0 < L_pos := by positivity
  have htend := airyLaplace_genRational_tendsto hF
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨Y0, hY0⟩ := htend (L_pos / 2) (by positivity)
  let Y : ℝ := max Y0 1
  have hY1 : 1 ≤ Y := le_max_right _ _
  have hY_floor : ∀ y : ℝ, Y ≤ y → (L_pos / 2) * y ^ (-(5 / 2 : ℝ)) ≤ airyLaplace X y := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one (hY1.trans hy)
    have hdist := hY0 y (le_trans (le_max_left Y0 1) hy)
    rw [Real.dist_eq, abs_lt] at hdist
    have hup : L_pos / 2 ≤ y ^ (5 / 2 : ℝ) * airyLaplace X y := by
      have : -(L_pos / 2) < y ^ (5 / 2 : ℝ) * airyLaplace X y - L_pos := hdist.1
      linarith
    have hp := mul_le_mul_of_nonneg_right hup (Real.rpow_nonneg hy0.le (-(5 / 2 : ℝ)))
    have hpow1 : y ^ (5 / 2 : ℝ) * airyLaplace X y * y ^ (-(5 / 2 : ℝ)) = airyLaplace X y := by
      calc y ^ (5 / 2 : ℝ) * airyLaplace X y * y ^ (-(5 / 2 : ℝ))
          = airyLaplace X y * (y ^ (5 / 2 : ℝ) * y ^ (-(5 / 2 : ℝ))) := by ring
        _ = airyLaplace X y * 1 := by rw [← Real.rpow_add hy0]; norm_num
        _ = airyLaplace X y := mul_one _
    linarith
  let B : ℝ := max (2 * x₀ + 2) (2 * Y / ceCs + 2)
  have hx₀B : x₀ < B := by have := le_max_left (2 * x₀ + 2) (2 * Y / ceCs + 2); linarith
  let M_scale : ℝ := max 1 ceCs
  have hM_scale : 0 < M_scale := by positivity
  let d₀ : ℝ := ceK * (L_pos / 2) * M_scale ^ (-(5 / 2 : ℝ))
  have hd₀ : 0 < d₀ := by have := ceK_pos; positivity
  refine ⟨x₀, B, c_lead / 2, d₀, hx₀, hx₀B, by positivity, hd₀, hsmall, fun x hx => ?_⟩
  have hBY : Y / ceCs ≤ B / 2 := by
    have h1 : 2 * (Y / ceCs) ≤ B := by
      have hmax : 2 * Y / ceCs + 2 ≤ B := le_max_right _ _
      linarith [show 2 * (Y / ceCs) = 2 * Y / ceCs by ring]
    linarith
  have hxY : Y ≤ ceCs * x := (div_le_iff₀' ceCs_pos).mp (hBY.trans hx)
  have hx0 : 0 ≤ x := by
    have : 0 ≤ Y / ceCs := div_nonneg (zero_le_one.trans hY1) ceCs_pos.le
    linarith
  have hce_scale : ceCs * x ≤ M_scale * (1 + x) :=
    mul_le_mul (le_max_right 1 ceCs) (by linarith) hx0 hM_scale.le
  have hrpow_cmp : M_scale ^ (-(5 / 2 : ℝ)) * (1 + x) ^ (-(5 / 2 : ℝ)) ≤ (ceCs * x) ^ (-(5 / 2 : ℝ)) := by
    rw [← Real.mul_rpow hM_scale.le (by linarith)]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos ceCs_pos (lt_of_lt_of_le (div_pos (zero_lt_one.trans_le hY1) ceCs_pos) (hBY.trans hx)))
      hce_scale (by norm_num)
  have hlap := hY_floor (ceCs * x) hxY
  have hre_eq : (airyTwistedLaplaceC X ((ceCs * x : ℝ) : ℂ)).re = ceK * airyLaplace X (ceCs * x) := by
    rw [airyTwistedLaplaceC_ofReal, Complex.ofReal_re]; unfold airyTwistedLaplace airyLaplace; ring
  rw [hre_eq]
  calc d₀ * (1 + x) ^ (-(5 / 2 : ℝ))
      = ceK * ((L_pos / 2) * (M_scale ^ (-(5 / 2 : ℝ)) * (1 + x) ^ (-(5 / 2 : ℝ)))) := by
          dsimp [d₀]; ring
    _ ≤ ceK * ((L_pos / 2) * (ceCs * x) ^ (-(5 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrpow_cmp (by positivity)) ceK_pos.le
    _ ≤ ceK * airyLaplace X (ceCs * x) := mul_le_mul_of_nonneg_left hlap ceK_pos.le

lemma airyTwistedLaplace_eq_ceK_airyLaplace (X : ℝ → ℝ) (y : ℝ) :
    airyTwistedLaplace X y = ceK * airyLaplace X y := by
  unfold airyTwistedLaplace airyLaplace; ring

lemma liftEps_le_one_of_two_le {c : ℝ} (hc : 2 ≤ c) : liftEps c ≤ 1 := by
  have hc0 : 0 < c := by linarith
  have hcube := liftEps_cube_mul hc0
  by_contra hgt
  push Not at hgt
  have hpow : 1 < liftEps c ^ 3 := by simpa using pow_lt_pow_left₀ hgt zero_le_one (by norm_num : 3 ≠ 0)
  nlinarith

lemma ceDualLine_hsmall_bound {X : ℝ → ℝ} (c₁' m_Z CZ_loc c_min : ℝ)
    (hX_small : ∀ x ∈ Icc (0 : ℝ) x₀, c₁' * Real.sqrt x ≤ airyTwistedLaplace X (ceCs * x))
    (Z : ℝ → ℝ → ℝ)
    (hZ0 : ∀ c : ℝ, c_min ≤ c → ceK * m_Z ≤ airyTwistedLaplace (Z c) 0)
    (hZ_loc : ∀ c x : ℝ, c_min ≤ c → x ∈ Icc (0 : ℝ) x₀ →
      |airyTwistedLaplace (Z c) (ceCs * x) - airyTwistedLaplace (Z c) 0| ≤ CZ_loc * Real.sqrt x)
    {c x : ℝ} (hc_min : c_min ≤ c) (hc0 : 0 < c) (hx : x ∈ Icc (0 : ℝ) x₀)
    (hε : liftEps c * CZ_loc ≤ c₁' / 2) :
    (c₁' / 2) * Real.sqrt x + ceK * m_Z * liftEps c ≤
      airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x) := by
  have hX := hX_small x hx
  have hZ_lo : ceK * m_Z - CZ_loc * Real.sqrt x ≤ airyTwistedLaplace (Z c) (ceCs * x) := by
    have h1 := (abs_le.mp (hZ_loc c x hc_min hx)).1
    have h2 := hZ0 c hc_min
    linarith
  have hε0 := (liftEps_pos hc0).le
  have hmul : liftEps c * (ceK * m_Z - CZ_loc * Real.sqrt x) ≤ liftEps c * airyTwistedLaplace (Z c) (ceCs * x) :=
    mul_le_mul_of_nonneg_left hZ_lo hε0
  have h1 : (c₁' / 2) * Real.sqrt x ≤ (c₁' - liftEps c * CZ_loc) * Real.sqrt x :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg x)
  linarith

lemma ceDualLine_htail_bound {X : ℝ → ℝ} (d₀ B₀ CZ_rhp c_min : ℝ)
    (hX_tail : ∀ x : ℝ, B₀ / 2 ≤ x → d₀ * (1 + x) ^ (-(5 / 2 : ℝ)) ≤ airyTwistedLaplace X (ceCs * x))
    (Z : ℝ → ℝ → ℝ)
    (hZ : ∀ c x : ℝ, c_min ≤ c → 0 ≤ x →
      |airyTwistedLaplace (Z c) (ceCs * x)| ≤ CZ_rhp * (1 + x) ^ (-(5 / 2 : ℝ)))
    {c x : ℝ} (hc_min : c_min ≤ c) (hc0 : 0 < c) (hxB : B₀ / 2 ≤ x) (hx0 : 0 ≤ x)
    (hε : liftEps c * CZ_rhp ≤ d₀ / 2) :
    (d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ)) ≤
      airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x) := by
  have hX := hX_tail x hxB
  have hZ_lo : -(CZ_rhp * (1 + x) ^ (-(5 / 2 : ℝ))) ≤ airyTwistedLaplace (Z c) (ceCs * x) :=
    (abs_le.mp (hZ c x hc_min hx0)).1
  have hε0 := (liftEps_pos hc0).le
  have hpow : 0 ≤ (1 + x) ^ (-(5 / 2 : ℝ)) := by positivity
  have hmul : liftEps c * (-(CZ_rhp * (1 + x) ^ (-(5 / 2 : ℝ)))) ≤ liftEps c * airyTwistedLaplace (Z c) (ceCs * x) :=
    mul_le_mul_of_nonneg_left hZ_lo hε0
  have h1 : (d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ)) ≤ (d₀ - liftEps c * CZ_rhp) * (1 + x) ^ (-(5 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith) hpow
  linarith

lemma ceDualLine_hA1_aux {X : ℝ → ℝ} {Z : ℝ → ℝ → ℝ} {D : ℝ → ℝ → ℝ}
    (hD_eq : ∀ c u, D c u = X u + liftEps c * Z c u)
    (hUX : HasU2 X) (hUZ : ∀ c, HasU2 (Z c)) (hUD : ∀ c, HasU2 (D c))
    {x₀ B₀ c₁' d₀ CX_loc CX_rhp CZ_rhp m_Z c₀ K M_small M_tail M : ℝ}
    (_hx₀ : 0 < x₀) (hB₀ : 0 ≤ B₀) (hc₁' : 0 < c₁') (hd₀ : 0 < d₀)
    (hCX_loc : 0 < CX_loc) (hCX_rhp : 0 ≤ CX_rhp) (hCZ_rhp : 0 < CZ_rhp) (hm_Z : 0 < m_Z)
    (hc₀_2 : 2 ≤ c₀)
    (hM_small_def : M_small = (2 : ℝ) ^ m * max (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z)))
    (hM_tail_def : M_tail = (2 : ℝ) ^ m * (2 ^ (5 / 2 : ℝ) * (CX_rhp + CZ_rhp) / (d₀ / 2)))
    (hM_sm : M_small ≤ M) (hM_tl : M_tail ≤ M)
    (hX_loc : ∀ {w : ℂ}, 0 ≤ w.re → ‖w‖ ≤ x₀ + 2 → ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ CX_loc * ‖w‖ ^ (1 / 2 : ℝ))
    (hX_rhp : ∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ CX_rhp * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    (hZ_rhp : ∀ {c : ℝ} {w : ℂ}, c₀ ≤ c → 0 ≤ w.re → ‖airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ ≤ CZ_rhp * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    (hD_small : ∀ {c x : ℝ}, c₀ ≤ c → x ∈ Icc (0 : ℝ) x₀ →
      (c₁' / 2) * Real.sqrt x + ceK * m_Z * liftEps c ≤
        airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))
    (hD_tail : ∀ {c x : ℝ}, c₀ ≤ c → B₀ / 2 ≤ x →
      (d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ)) ≤
        airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))
    (hWD_re : ∀ {c x : ℝ}, 0 ≤ x →
      (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re =
        uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x) ^ m *
          (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)))
    (hK : 0 < K) (hm : 1 ≤ m)
    {c x y : ℝ} (hc : c₀ ≤ c) (hx : 0 < x) (hx_not : x ∉ Icc (x₀ / 3) (2 * B₀)) (hy : |y| ≤ x / 4) :
    ‖liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m ((x : ℂ) + (y : ℂ) * Complex.I) -
        liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)‖ ≤
      4 * M * (|y| / x) * (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re := by
  have hc0 : 0 < c := by linarith
  set a : ℝ := ceCs * (ceBeta1 * K * liftEps c / 2) / m
  have ha0 : 0 < a := by have := ceCs_pos; have := ceBeta1_pos; have := liftEps_pos hc0; positivity
  have hball_rel : ∀ w : ℂ, x / 2 ≤ w.re → ‖w - (x : ℂ)‖ ≤ x / 2 →
      ‖liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m w‖ ≤
        M * (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re := by
    intro w hw_re hw_ball
    have hw0 : 0 ≤ w.re := by linarith
    have hM_pow : ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ ≤
        (2 : ℝ) ^ m * uctE1r (a * x) ^ m := by
      refine (norm_liftMultiplier_le_pow (ceBeta1 * K * liftEps c / 2) m w).trans ?_
      have h1 : uctE1r (a * w.re) ≤ uctE1r (a * x / 2) := uctE1r_anti (by nlinarith)
      have h2 : uctE1r (a * x / 2) ≤ 2 * uctE1r (a * x) := uctE1r_half (by positivity)
      calc uctE1r (a * w.re) ^ m ≤ (2 * uctE1r (a * x)) ^ m :=
            pow_le_pow_left₀ (uctE1r_pos _).le (h1.trans h2) m
        _ = _ := by rw [mul_pow]
    have hD_split : airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w) =
        airyTwistedLaplaceC X ((ceCs : ℂ) * w) +
          (liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w) := by
      have hre : 0 ≤ ((ceCs : ℂ) * w).re := by simp; exact mul_nonneg ceCs_pos.le hw0
      have hfn : D c = fun u => X u + liftEps c * Z c u := funext (hD_eq c)
      rw [hfn, airyTwistedLaplaceC_add (hUX.integrable _ hre) (((hUZ c).smul _).integrable _ hre),
        airyTwistedLaplaceC_const_mul]
    have hWD_norm : ‖liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m w‖ =
        ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ * ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ := by
      unfold liftSymbol; rw [norm_mul]
    have hcases : x < x₀ / 3 ∨ 2 * B₀ < x := by
      by_contra hcon; push Not at hcon; exact hx_not ⟨hcon.1, hcon.2⟩
    rcases hcases with hx_sm | hx_lg
    · have hwn : ‖w‖ ≤ 3 / 2 * x := by
        calc ‖w‖ = ‖(w - (x : ℂ)) + (x : ℂ)‖ := by ring_nf
          _ ≤ ‖w - (x : ℂ)‖ + ‖(x : ℂ)‖ := norm_add_le _ _
          _ ≤ x / 2 + x := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]; linarith
          _ = 3 / 2 * x := by ring
      have hXw := hX_loc hw0 (by linarith)
      have hwn_sqrt : ‖w‖ ^ (1 / 2 : ℝ) ≤ Real.sqrt (3 / 2) * Real.sqrt x := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.mul_rpow (by norm_num) hx.le]
        exact Real.rpow_le_rpow (norm_nonneg w) hwn (by norm_num)
      have hZw := hZ_rhp hc hw0
      have h1w : 1 ≤ ‖1 + w‖ := by
        have := Complex.re_le_norm (1 + w)
        simp only [Complex.add_re, Complex.one_re] at this; linarith
      have hZw1 : ‖airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ ≤ CZ_rhp :=
        hZw.trans (mul_le_of_le_one_right hCZ_rhp.le (Real.rpow_le_one_of_one_le_of_nonpos h1w (by norm_num)))
      have hDw : ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤
          CX_loc * Real.sqrt (3 / 2) * Real.sqrt x + liftEps c * CZ_rhp := by
        rw [hD_split]
        calc ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w) + (liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖
            ≤ ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ +
                ‖(liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ := norm_add_le _ _
          _ ≤ CX_loc * (Real.sqrt (3 / 2) * Real.sqrt x) + liftEps c * CZ_rhp := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (liftEps_pos hc0)]
              exact add_le_add (hXw.trans (mul_le_mul_of_nonneg_left hwn_sqrt hCX_loc.le))
                (mul_le_mul_of_nonneg_left hZw1 (liftEps_pos hc0).le)
          _ = _ := by ring
      have hDs := hD_small hc ⟨hx.le, by linarith⟩
      have hterm1 : CX_loc * Real.sqrt (3 / 2) * Real.sqrt x ≤
          (2 * CX_loc * Real.sqrt (3 / 2) / c₁') * ((c₁' / 2) * Real.sqrt x) := by
        have heq : (2 * CX_loc * Real.sqrt (3 / 2) / c₁') * ((c₁' / 2) * Real.sqrt x) =
            CX_loc * Real.sqrt (3 / 2) * Real.sqrt x := by field_simp [hc₁'.ne']
        linarith
      have hterm2 : liftEps c * CZ_rhp ≤ (CZ_rhp / (ceK * m_Z)) * (ceK * m_Z * liftEps c) := by
        have := ceK_pos
        have heq : (CZ_rhp / (ceK * m_Z)) * (ceK * m_Z * liftEps c) = liftEps c * CZ_rhp := by
          field_simp [this.ne', hm_Z.ne']
        linarith
      have hMs1 := le_max_left (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z))
      have hMs2 := le_max_right (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z))
      have hD_rel : ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤
          max (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z)) *
            (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)) := by
        calc ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖
            ≤ (2 * CX_loc * Real.sqrt (3 / 2) / c₁') * ((c₁' / 2) * Real.sqrt x) +
                (CZ_rhp / (ceK * m_Z)) * (ceK * m_Z * liftEps c) := by linarith
          _ ≤ max (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z)) *
                ((c₁' / 2) * Real.sqrt x + ceK * m_Z * liftEps c) := by
              rw [mul_add]
              exact add_le_add (mul_le_mul_of_nonneg_right hMs1 (by positivity))
                (mul_le_mul_of_nonneg_right hMs2 (by have := ceK_pos; have := liftEps_pos hc0; positivity))
          _ ≤ _ := mul_le_mul_of_nonneg_left hDs (by have := ceK_pos; positivity)
      rw [hWD_norm, hWD_re hx.le]
      calc ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ * ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖
          ≤ ((2 : ℝ) ^ m * uctE1r (a * x) ^ m) *
              (max (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z)) *
                (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) :=
            mul_le_mul hM_pow hD_rel (norm_nonneg _) (mul_nonneg (by positivity) (pow_nonneg (uctE1r_pos _).le _))
        _ = M_small * (uctE1r (a * x) ^ m *
              (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) := by
            rw [hM_small_def]; dsimp [a]; ring
        _ ≤ M * (uctE1r (a * x) ^ m *
              (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) := by
            have hnn1 : 0 ≤ (c₁' / 2) * Real.sqrt x := by positivity
            have hnn2 : 0 ≤ ceK * m_Z * liftEps c := by have := ceK_pos; have := liftEps_pos hc0; positivity
            have hnn : 0 ≤ uctE1r (a * x) ^ m *
                (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)) :=
              mul_nonneg (pow_nonneg (uctE1r_pos _).le _) (le_trans (add_nonneg hnn1 hnn2) hDs)
            exact mul_le_mul_of_nonneg_right hM_sm hnn
    · have h1w_ge : 1 + x / 2 ≤ ‖1 + w‖ := by
        have := Complex.re_le_norm (1 + w)
        simp only [Complex.add_re, Complex.one_re] at this; linarith
      have hpow_w : ‖1 + w‖ ^ (-(5 / 2 : ℝ)) ≤ 2 ^ (5 / 2 : ℝ) * (1 + x) ^ (-(5 / 2 : ℝ)) := by
        have h1 : ‖1 + w‖ ^ (-(5 / 2 : ℝ)) ≤ (1 + x / 2) ^ (-(5 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) h1w_ge (by norm_num)
        have h2 : (1 + x / 2) ^ (-(5 / 2 : ℝ)) ≤ (2⁻¹ * (1 + x)) ^ (-(5 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
        have h3 : ((2 : ℝ)⁻¹) ^ (-(5 / 2 : ℝ)) = 2 ^ (5 / 2 : ℝ) := by
          rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
        rw [Real.mul_rpow (by norm_num) (by linarith), h3] at h2
        exact h1.trans h2
      have hXw := (hX_rhp w hw0).trans (mul_le_mul_of_nonneg_left hpow_w hCX_rhp)
      have hZw := (hZ_rhp hc hw0).trans (mul_le_mul_of_nonneg_left hpow_w hCZ_rhp.le)
      have hε1 : liftEps c ≤ 1 := liftEps_le_one_of_two_le (hc₀_2.trans hc)
      have hDw : ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤
          (CX_rhp + CZ_rhp) * (2 ^ (5 / 2 : ℝ) * (1 + x) ^ (-(5 / 2 : ℝ))) := by
        rw [hD_split]
        calc ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w) + (liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖
            ≤ ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ +
                ‖(liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ := norm_add_le _ _
          _ ≤ CX_rhp * (2 ^ (5 / 2 : ℝ) * (1 + x) ^ (-(5 / 2 : ℝ))) +
                1 * (CZ_rhp * (2 ^ (5 / 2 : ℝ) * (1 + x) ^ (-(5 / 2 : ℝ)))) := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (liftEps_pos hc0)]
              exact add_le_add hXw (mul_le_mul hε1 hZw (norm_nonneg _) zero_le_one)
          _ = _ := by ring
      have hB0_nn := hB₀
      have hDt := hD_tail (x := x) hc (by linarith)
      have hD_rel : ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤
          (2 ^ (5 / 2 : ℝ) * (CX_rhp + CZ_rhp) / (d₀ / 2)) *
            (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)) := by
        have heq : (2 ^ (5 / 2 : ℝ) * (CX_rhp + CZ_rhp) / (d₀ / 2)) * ((d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ))) =
            (CX_rhp + CZ_rhp) * (2 ^ (5 / 2 : ℝ) * (1 + x) ^ (-(5 / 2 : ℝ))) := by field_simp [hd₀.ne']
        calc ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖
            ≤ (2 ^ (5 / 2 : ℝ) * (CX_rhp + CZ_rhp) / (d₀ / 2)) * ((d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ))) := by linarith
          _ ≤ _ := mul_le_mul_of_nonneg_left hDt (by positivity)
      rw [hWD_norm, hWD_re hx.le]
      calc ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ * ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖
          ≤ ((2 : ℝ) ^ m * uctE1r (a * x) ^ m) *
              ((2 ^ (5 / 2 : ℝ) * (CX_rhp + CZ_rhp) / (d₀ / 2)) *
                (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) :=
            mul_le_mul hM_pow hD_rel (norm_nonneg _) (mul_nonneg (by positivity) (pow_nonneg (uctE1r_pos _).le _))
        _ = M_tail * (uctE1r (a * x) ^ m *
              (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) := by
            rw [hM_tail_def]; dsimp [a]; ring
        _ ≤ M * (uctE1r (a * x) ^ m *
              (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) := by
            have hnn : 0 ≤ uctE1r (a * x) ^ m *
                (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)) :=
              mul_nonneg (pow_nonneg (uctE1r_pos _).le _) (le_trans (by positivity) hDt)
            exact mul_le_mul_of_nonneg_right hM_tl hnn
  have hv := local_variation_right (liftSymbol_differentiableOn (hUD c) (ceBeta1 * K * liftEps c / 2) m) hx
    (B := M * (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re) hball_rel y hy
  calc ‖liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m ((x : ℂ) + (y : ℂ) * Complex.I) -
          liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)‖
      ≤ 4 * (M * (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re) / x * |y| := hv
    _ = 4 * M * (|y| / x) * (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re := by ring

lemma ceDualLine_hA2_aux {X : ℝ → ℝ} {Z : ℝ → ℝ → ℝ} {D : ℝ → ℝ → ℝ}
    (hD_eq : ∀ c u, D c u = X u + liftEps c * Z c u)
    (hUX : HasU2 X) (hUZ : ∀ c, HasU2 (Z c))
    {x₀ B₀ c₁' d₀ CX_loc CX_rhp CZ_rhp m_Z c₀ K M_tail M Λ_add_max : ℝ}
    (hx₀ : 0 < x₀) (hx₀B : x₀ < B₀) (hB₀ : 0 ≤ B₀) (hc₁' : 0 < c₁') (hd₀ : 0 < d₀)
    (hCX_loc : 0 < CX_loc) (hCX_rhp : 0 ≤ CX_rhp) (hCZ_rhp : 0 < CZ_rhp) (hm_Z : 0 < m_Z)
    (hc₀_2 : 2 ≤ c₀)
    (hM_sm : (2 : ℝ) ^ m * max (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z)) ≤ M)
    (hM_tail_def : M_tail = (2 : ℝ) ^ m * (2 ^ (5 / 2 : ℝ) * (CX_rhp + CZ_rhp) / (d₀ / 2)))
    (hM_tl : M_tail ≤ M)
    (hL1 : CX_loc * Real.sqrt 3 ≤ Λ_add_max) (hL2 : CX_rhp ≤ Λ_add_max)
    (hX_loc : ∀ {w : ℂ}, 0 ≤ w.re → ‖w‖ ≤ x₀ + 2 → ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ CX_loc * ‖w‖ ^ (1 / 2 : ℝ))
    (hX_rhp : ∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ CX_rhp * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    (hZ_rhp : ∀ {c : ℝ} {w : ℂ}, c₀ ≤ c → 0 ≤ w.re → ‖airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ ≤ CZ_rhp * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    (hD_small : ∀ {c x : ℝ}, c₀ ≤ c → x ∈ Icc (0 : ℝ) x₀ →
      (c₁' / 2) * Real.sqrt x + ceK * m_Z * liftEps c ≤
        airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))
    (hD_tail : ∀ {c x : ℝ}, c₀ ≤ c → B₀ / 2 ≤ x →
      (d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ)) ≤
        airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))
    (hWD_re : ∀ {c x : ℝ}, 0 ≤ x →
      (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re =
        uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x) ^ m *
          (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)))
    (hK : 0 < K)
    {c x y : ℝ} (hc : c₀ ≤ c) (hx : 0 < x) (hx_not : x ∉ Icc (x₀ / 3) (2 * B₀)) :
    ‖liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      M * (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re +
        (if x < x₀ ∧ x / 2 < |y| then Λ_add_max * min (|y| ^ (1 / 2 : ℝ)) 1 else 0) := by
  have hc0 : 0 < c := by linarith
  have hδ0 : 0 ≤ ceBeta1 * K * liftEps c / 2 := by
    have := ceBeta1_pos; have := liftEps_pos hc0; positivity
  set w : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  have hw_re : w.re = x := by simp [w]
  have hw0 : 0 ≤ w.re := by linarith
  have hD_split : airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w) =
      airyTwistedLaplaceC X ((ceCs : ℂ) * w) +
        (liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w) := by
    have hre : 0 ≤ ((ceCs : ℂ) * w).re := by simp; exact mul_nonneg ceCs_pos.le hw0
    have hfn : D c = fun u => X u + liftEps c * Z c u := funext (hD_eq c)
    rw [hfn, airyTwistedLaplaceC_add (hUX.integrable _ hre) (((hUZ c).smul _).integrable _ hre),
      airyTwistedLaplaceC_const_mul]
  set a : ℝ := ceCs * (ceBeta1 * K * liftEps c / 2) / m
  have hM_le : ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ ≤ uctE1r (a * x) ^ m := by
    simpa [a, hw_re] using norm_liftMultiplier_le_pow (ceBeta1 * K * liftEps c / 2) m w
  have hM_le1 : ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ ≤ 1 :=
    norm_liftMultiplier_le_one hδ0 m hw0
  have hcases : x < x₀ / 3 ∨ 2 * B₀ < x := by
    by_contra hcon; push Not at hcon; exact hx_not ⟨hcon.1, hcon.2⟩
  rcases hcases with hx_sm | hx_lg
  · have hx_lt_x0 : x < x₀ := by linarith
    have hZw : ‖airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ ≤ CZ_rhp := by
      have h1 := hZ_rhp hc hw0
      have h1w : 1 ≤ ‖1 + w‖ := by
        have := Complex.re_le_norm (1 + w)
        simp only [Complex.add_re, Complex.one_re, hw_re] at this; linarith
      exact h1.trans (mul_le_of_le_one_right hCZ_rhp.le (Real.rpow_le_one_of_one_le_of_nonpos h1w (by norm_num)))
    have hDs := hD_small hc ⟨hx.le, hx_lt_x0.le⟩
    have hC_le_M : CZ_rhp / (ceK * m_Z) ≤ M := by
      have h2m : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
      have h1 : CZ_rhp / (ceK * m_Z) ≤
          (2 : ℝ) ^ m * max (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z)) :=
        (le_max_right _ _).trans (le_mul_of_one_le_left (by have := ceK_pos; positivity) h2m)
      exact h1.trans hM_sm
    have hZ_to_WD : uctE1r (a * x) ^ m * (liftEps c * CZ_rhp) ≤
        M * (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re := by
      rw [hWD_re hx.le]
      have hM_nn : 0 ≤ uctE1r (a * x) ^ m := pow_nonneg (uctE1r_pos _).le m
      have hterm2 : liftEps c * CZ_rhp ≤ (CZ_rhp / (ceK * m_Z)) *
          (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)) := by
        have heq : (CZ_rhp / (ceK * m_Z)) * (ceK * m_Z * liftEps c) = liftEps c * CZ_rhp := by
          have := ceK_pos; field_simp [this.ne', hm_Z.ne']
        calc liftEps c * CZ_rhp = (CZ_rhp / (ceK * m_Z)) * (ceK * m_Z * liftEps c) := heq.symm
          _ ≤ (CZ_rhp / (ceK * m_Z)) * ((c₁' / 2) * Real.sqrt x + ceK * m_Z * liftEps c) := by
              have := ceK_pos
              exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left hDs (by have := ceK_pos; positivity)
      have hnn_rhs : 0 ≤ uctE1r (a * x) ^ m *
          (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)) := by
        have := ceK_pos; have := liftEps_pos hc0
        exact mul_nonneg hM_nn (le_trans (by positivity) hDs)
      calc uctE1r (a * x) ^ m * (liftEps c * CZ_rhp)
          ≤ uctE1r (a * x) ^ m * ((CZ_rhp / (ceK * m_Z)) *
              (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) :=
            mul_le_mul_of_nonneg_left hterm2 hM_nn
        _ = (CZ_rhp / (ceK * m_Z)) * (uctE1r (a * x) ^ m *
              (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) := by
            dsimp [a]; ring
        _ ≤ M * _ := mul_le_mul_of_nonneg_right hC_le_M hnn_rhs
    have hWD_Z_term : ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ *
          ‖(liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ ≤
        M * (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re := by
      calc ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ *
            ‖(liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖
          ≤ uctE1r (a * x) ^ m * (liftEps c * CZ_rhp) := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (liftEps_pos hc0)]
            exact mul_le_mul hM_le (mul_le_mul_of_nonneg_left hZw (liftEps_pos hc0).le)
              (mul_nonneg (liftEps_pos hc0).le (norm_nonneg _)) (pow_nonneg (uctE1r_pos _).le _)
        _ ≤ _ := hZ_to_WD
    by_cases hy2 : x / 2 < |y|
    · simp only [hx_lt_x0, hy2, and_self, ↓reduceIte]
      have hXw_add : ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ *
            ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ Λ_add_max * min (|y| ^ (1 / 2 : ℝ)) 1 := by
        rcases le_or_gt |y| 1 with hy1 | hy1
        · rw [min_eq_left (Real.rpow_le_one (abs_nonneg y) hy1 (by norm_num))]
          have hwn : ‖w‖ ≤ x + |y| := by
            calc ‖w‖ ≤ ‖(x : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
              _ = x + |y| := by simp [abs_of_pos hx]
          have hwn3 : ‖w‖ ≤ 3 * |y| := by linarith
          have hXw := hX_loc hw0 (by linarith)
          have hsqrt3 : ‖w‖ ^ (1 / 2 : ℝ) ≤ Real.sqrt 3 * |y| ^ (1 / 2 : ℝ) := by
            rw [Real.sqrt_eq_rpow, ← Real.mul_rpow (by norm_num) (abs_nonneg y)]
            exact Real.rpow_le_rpow (norm_nonneg w) hwn3 (by norm_num)
          calc ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ * ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖
              ≤ 1 * (CX_loc * (Real.sqrt 3 * |y| ^ (1 / 2 : ℝ))) :=
                mul_le_mul hM_le1 (hXw.trans (mul_le_mul_of_nonneg_left hsqrt3 hCX_loc.le))
                  (norm_nonneg _) zero_le_one
            _ = (CX_loc * Real.sqrt 3) * |y| ^ (1 / 2 : ℝ) := by ring
            _ ≤ Λ_add_max * |y| ^ (1 / 2 : ℝ) :=
                mul_le_mul_of_nonneg_right hL1 (by positivity)
        · rw [min_eq_right (Real.one_le_rpow hy1.le (by norm_num)), mul_one]
          have h1w : 1 ≤ ‖1 + w‖ := by
            have := Complex.re_le_norm (1 + w)
            simp only [Complex.add_re, Complex.one_re, hw_re] at this; linarith
          have hXw := (hX_rhp w hw0).trans
            (mul_le_of_le_one_right hCX_rhp (Real.rpow_le_one_of_one_le_of_nonpos h1w (by norm_num)))
          calc ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ * ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖
              ≤ 1 * CX_rhp := mul_le_mul hM_le1 hXw (norm_nonneg _) zero_le_one
            _ = CX_rhp := one_mul _
            _ ≤ Λ_add_max := hL2
      calc ‖liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m w‖
          = ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ * ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ := by
              unfold liftSymbol; rw [norm_mul]
        _ ≤ ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ *
              (‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ +
                ‖(liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖) := by
            rw [hD_split]; exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
        _ = ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ * ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ +
              ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ *
                ‖(liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ := by ring
        _ ≤ Λ_add_max * min (|y| ^ (1 / 2 : ℝ)) 1 +
              M * (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re :=
            add_le_add hXw_add hWD_Z_term
        _ = _ := by ring
    · push Not at hy2
      have hnot : ¬ (x < x₀ ∧ x / 2 < |y|) := fun h => absurd h.2 (not_lt.mpr hy2)
      simp only [hnot, ↓reduceIte, add_zero]
      have hwn : ‖w‖ ≤ 3 / 2 * x := by
        calc ‖w‖ ≤ ‖(x : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = x + |y| := by simp [abs_of_pos hx]
          _ ≤ 3 / 2 * x := by linarith
      have hXw := hX_loc hw0 (by linarith)
      have hwn_sqrt : ‖w‖ ^ (1 / 2 : ℝ) ≤ Real.sqrt (3 / 2) * Real.sqrt x := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.mul_rpow (by norm_num) hx.le]
        exact Real.rpow_le_rpow (norm_nonneg w) hwn (by norm_num)
      have hDw : ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤
          CX_loc * Real.sqrt (3 / 2) * Real.sqrt x + liftEps c * CZ_rhp := by
        rw [hD_split]
        calc ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w) + (liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖
            ≤ ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ +
                ‖(liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ := norm_add_le _ _
          _ ≤ CX_loc * (Real.sqrt (3 / 2) * Real.sqrt x) + liftEps c * CZ_rhp := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (liftEps_pos hc0)]
              exact add_le_add (hXw.trans (mul_le_mul_of_nonneg_left hwn_sqrt hCX_loc.le))
                (mul_le_mul_of_nonneg_left hZw (liftEps_pos hc0).le)
          _ = _ := by ring
      have hD_rel : ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤
          max (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z)) *
            (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)) := by
        have hterm1 : CX_loc * Real.sqrt (3 / 2) * Real.sqrt x ≤
            (2 * CX_loc * Real.sqrt (3 / 2) / c₁') * ((c₁' / 2) * Real.sqrt x) := by
          have heq : (2 * CX_loc * Real.sqrt (3 / 2) / c₁') * ((c₁' / 2) * Real.sqrt x) =
              CX_loc * Real.sqrt (3 / 2) * Real.sqrt x := by field_simp [hc₁'.ne']
          linarith
        have hterm2 : liftEps c * CZ_rhp ≤ (CZ_rhp / (ceK * m_Z)) * (ceK * m_Z * liftEps c) := by
          have := ceK_pos
          have heq : (CZ_rhp / (ceK * m_Z)) * (ceK * m_Z * liftEps c) = liftEps c * CZ_rhp := by
            field_simp [this.ne', hm_Z.ne']
          linarith
        have hMs1 := le_max_left (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z))
        have hMs2 := le_max_right (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z))
        calc ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖
            ≤ (2 * CX_loc * Real.sqrt (3 / 2) / c₁') * ((c₁' / 2) * Real.sqrt x) +
                (CZ_rhp / (ceK * m_Z)) * (ceK * m_Z * liftEps c) := by linarith
          _ ≤ max (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z)) *
                ((c₁' / 2) * Real.sqrt x + ceK * m_Z * liftEps c) := by
              rw [mul_add]
              exact add_le_add (mul_le_mul_of_nonneg_right hMs1 (by positivity))
                (mul_le_mul_of_nonneg_right hMs2 (by have := ceK_pos; have := liftEps_pos hc0; positivity))
          _ ≤ _ := mul_le_mul_of_nonneg_left hDs (by have := ceK_pos; positivity)
      have hC_le_M : max (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z)) ≤ M := by
        have h2m : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
        exact (le_mul_of_one_le_left (by have := ceK_pos; positivity) h2m).trans hM_sm
      rw [show liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m w =
          liftMultiplier (ceBeta1 * K * liftEps c / 2) m w *
            airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w) from rfl, norm_mul, hWD_re hx.le]
      calc ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ * ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖
          ≤ uctE1r (a * x) ^ m * (M *
              (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) := by
            have hnn1 : 0 ≤ (c₁' / 2) * Real.sqrt x := by positivity
            have hnn2 : 0 ≤ ceK * m_Z * liftEps c := by have := ceK_pos; have := liftEps_pos hc0; positivity
            exact mul_le_mul hM_le (hD_rel.trans (mul_le_mul_of_nonneg_right hC_le_M (le_trans (add_nonneg hnn1 hnn2) hDs)))
              (norm_nonneg _) (pow_nonneg (uctE1r_pos _).le _)
        _ = M * (uctE1r (a * x) ^ m *
              (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) := by
            dsimp [a]; ring
  · have hnot : ¬ (x < x₀ ∧ x / 2 < |y|) := fun h => by linarith [h.1, hx₀B]
    simp only [hnot, ↓reduceIte, add_zero]
    have h1w_ge : 1 + x ≤ ‖1 + w‖ := by
      have := Complex.re_le_norm (1 + w)
      simp only [Complex.add_re, Complex.one_re, hw_re] at this; linarith
    have hpow_w : ‖1 + w‖ ^ (-(5 / 2 : ℝ)) ≤ (1 + x) ^ (-(5 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) h1w_ge (by norm_num)
    have hXw := (hX_rhp w hw0).trans (mul_le_mul_of_nonneg_left hpow_w hCX_rhp)
    have hZw := (hZ_rhp hc hw0).trans (mul_le_mul_of_nonneg_left hpow_w hCZ_rhp.le)
    have hε1 : liftEps c ≤ 1 := liftEps_le_one_of_two_le (hc₀_2.trans hc)
    have hDw : ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤
        (CX_rhp + CZ_rhp) * (1 + x) ^ (-(5 / 2 : ℝ)) := by
      rw [hD_split]
      calc ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w) + (liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖
          ≤ ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ +
              ‖(liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ := norm_add_le _ _
        _ ≤ CX_rhp * (1 + x) ^ (-(5 / 2 : ℝ)) + 1 * (CZ_rhp * (1 + x) ^ (-(5 / 2 : ℝ))) := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (liftEps_pos hc0)]
            exact add_le_add hXw (mul_le_mul hε1 hZw (norm_nonneg _) zero_le_one)
        _ = _ := by ring
    have hB0_nn := hB₀
    have hDt := hD_tail (x := x) hc (by linarith)
    have hD_rel : ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤
        M_tail * (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)) := by
      have hMt1 : CX_rhp + CZ_rhp ≤ M_tail * (d₀ / 2) := by
        rw [hM_tail_def]
        have h1 : 1 ≤ (2 : ℝ) ^ m * 2 ^ (5 / 2 : ℝ) := by
          have h2m : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
          have h25 : (1 : ℝ) ≤ (2 : ℝ) ^ (5 / 2 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
          nlinarith
        have heq : (2 : ℝ) ^ m * (2 ^ (5 / 2 : ℝ) * (CX_rhp + CZ_rhp) / (d₀ / 2)) * (d₀ / 2) =
            ((2 : ℝ) ^ m * 2 ^ (5 / 2 : ℝ)) * (CX_rhp + CZ_rhp) := by field_simp [hd₀.ne']
        rw [heq]
        exact le_mul_of_one_le_left (by positivity) h1
      calc ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖
          ≤ (M_tail * (d₀ / 2)) * (1 + x) ^ (-(5 / 2 : ℝ)) :=
            hDw.trans (mul_le_mul_of_nonneg_right hMt1 (by positivity))
        _ = M_tail * ((d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hDt (by rw [hM_tail_def]; positivity)
    rw [show liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m w =
        liftMultiplier (ceBeta1 * K * liftEps c / 2) m w *
          airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w) from rfl, norm_mul, hWD_re hx.le]
    calc ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ * ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖
        ≤ uctE1r (a * x) ^ m * (M *
            (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) :=
          mul_le_mul hM_le (hD_rel.trans (mul_le_mul_of_nonneg_right hM_tl (le_trans (by positivity) hDt)))
            (norm_nonneg _) (pow_nonneg (uctE1r_pos _).le _)
      _ = M * (uctE1r (a * x) ^ m *
            (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) := by
          dsimp [a]; ring

/-- info: 'FormalResearch.SignUncertainty.ce_dual_floors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_dual_floors

end FormalResearch.SignUncertainty
