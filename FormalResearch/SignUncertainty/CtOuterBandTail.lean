module

public import FormalResearch.SignUncertainty.CtOuterBandAmp
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The right non-stationary piece (Piece 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 4, Piece 3 (`χ_∞`, two integrations by
parts with vanishing boundary terms, `|Φ'| ≥ c₀ τ²/(1+τ²)`).  **Proved.**
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped Real Interval

namespace FormalResearch.SignUncertainty.CtOsc

lemma wt_div_sg_sq_le {τ : ℝ} (hτ : 0 < τ) : wt τ / sg τ ^ 2 ≤ 4 * (τ ^ (-11 / 2 : ℝ) + τ ^ (-5 / 2 : ℝ)) := by
  have e1 : τ ^ (-11 / 2 : ℝ) = τ ^ (-3 / 2 : ℝ) / τ ^ 4 := by
    rw [show (-11 / 2 : ℝ) = -3 / 2 - 4 by norm_num, Real.rpow_sub hτ]; norm_cast
  have e2 : τ ^ (-5 / 2 : ℝ) = τ ^ (-3 / 2 : ℝ) / τ ^ 4 * τ ^ 3 := by
    rw [← e1, ← Real.rpow_natCast, ← Real.rpow_add hτ]; norm_num
  have hw : 0 < τ ^ (-3 / 2 : ℝ) := by positivity
  unfold wt sg
  have h1 : (1 + τ ^ 2) ^ 2 ≤ (1 + τ) ^ 4 := by nlinarith [sq_nonneg τ, hτ.le, mul_pos hτ hτ]
  have h2 : (1 + τ) ^ 3 ≤ 4 * (1 + τ ^ 3) := by
    nlinarith [sq_nonneg (τ - 1), mul_nonneg hτ.le (sq_nonneg (τ - 1)), hτ.le]
  rw [e1, e2]
  have : τ ^ (-3 / 2 : ℝ) / (1 + τ) / (τ ^ 2 / (1 + τ ^ 2)) ^ 2 =
      τ ^ (-3 / 2 : ℝ) / τ ^ 4 * ((1 + τ ^ 2) ^ 2 / (1 + τ)) := by
    field_simp
  rw [this]
  have hq : (1 + τ ^ 2) ^ 2 / (1 + τ) ≤ 4 * (1 + τ ^ 3) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [h1, h2, mul_pos hτ hτ]
  have hnn : 0 ≤ τ ^ (-3 / 2 : ℝ) / τ ^ 4 := by positivity
  calc τ ^ (-3 / 2 : ℝ) / τ ^ 4 * ((1 + τ ^ 2) ^ 2 / (1 + τ)) ≤ τ ^ (-3 / 2 : ℝ) / τ ^ 4 * (4 * (1 + τ ^ 3)) :=
        mul_le_mul_of_nonneg_left hq hnn
    _ = _ := by ring

lemma norm_inv_I_mul {lam : ℝ} (hlam : 0 < lam) : ‖(1 / (Complex.I * (lam : ℂ)))‖ = 1 / lam := by
  rw [norm_div, norm_one, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam]

lemma rpow_half_le_div {b : ℝ} (hb : 1 ≤ b) : b ^ (1 / 2 : ℝ) / (1 + b) ≤ b ^ (-1 / 2 : ℝ) := by
  have hb0 : 0 < b := by linarith
  rw [← rpow_half_div hb0]
  exact div_le_div_of_nonneg_left (by positivity) hb0 (by linarith)

section
variable {C0 : ℝ} {m m1 m2 m3 : ℝ → ℝ}

/-- **Piece 3, with boundary terms at `a`.** For `|m - L| ≥ γ σ` on `[a, ∞)`, the improper integral of `B e^{iλϕ}` over
`[a,∞)` exists and equals the two explicit boundary terms at `a` plus `(iλ)^{-2} J` with `J = O(a^{-9/2} + a^{-3/2})`. -/
theorem piece3_gen (hM : MData C0 m m1 m2 m3) {γ KB lam L a : ℝ} (hγ : 0 < γ) (hKB : 0 ≤ KB) (hlam : 0 < lam)
    (ha : 0 < a) {ϕ : ℝ → ℝ} (hϕ : ∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - L) τ)
    {B B1 B2 : ℝ → ℂ} (hB : ∀ τ : ℝ, 0 < τ → HasDerivAt B (B1 τ) τ)
    (hB1 : ∀ τ : ℝ, 0 < τ → HasDerivAt B1 (B2 τ) τ) (hc2 : ContinuousOn B2 (Ioi 0))
    (hbB : ∀ τ : ℝ, 0 < τ → ‖B τ‖ ≤ KB * τ ^ (1 / 2 : ℝ) / (1 + τ))
    (hbB1 : ∀ τ : ℝ, 0 < τ → ‖B1 τ‖ ≤ KB * τ ^ (-1 / 2 : ℝ) / (1 + τ))
    (hbB2 : ∀ τ : ℝ, 0 < τ → ‖B2 τ‖ ≤ KB * τ ^ (-3 / 2 : ℝ) / (1 + τ))
    (hp : ∀ τ : ℝ, a ≤ τ → γ * sg τ ≤ |m τ - L|) :
    ∃ J : ℂ, Tendsto (fun b : ℝ => ∫ τ in a..b, B τ * Complex.exp (Complex.I * lam * (ϕ τ : ℂ))) atTop
        (𝓝 (-((1 / (Complex.I * lam)) * (B a / ((m a - L : ℝ) : ℂ) * Complex.exp (Complex.I * lam * (ϕ a : ℂ)))) +
          (1 / (Complex.I * lam)) ^ 2 * (ibpH B B1 (fun τ => m τ - L) m1 a / ((m a - L : ℝ) : ℂ) *
            Complex.exp (Complex.I * lam * (ϕ a : ℂ))) + (1 / (Complex.I * lam)) ^ 2 * J)) ∧
      ‖J‖ ≤ (4 * KB * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) / γ ^ 2) *
        ((2 / 9) * a ^ (-9 / 2 : ℝ) + (2 / 3) * a ^ (-3 / 2 : ℝ)) := by
  set K0 := 1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2 with hK0
  set K1 := 4 * KB * K0 / γ ^ 2 with hK1
  have hC0 := hM.C0nn
  have hK0nn : 0 ≤ K0 := by positivity
  have hK1nn : 0 ≤ K1 := by positivity
  have hpos : ∀ τ : ℝ, a ≤ τ → 0 < τ := fun τ h => lt_of_lt_of_le ha h
  have hsgpos : ∀ τ : ℝ, 0 < τ → 0 < sg τ := fun τ hτ => by unfold sg; positivity
  set ϕ1 : ℝ → ℝ := fun τ => m τ - L with hϕ1
  have hne : ∀ τ : ℝ, a ≤ τ → ϕ1 τ ≠ 0 := by
    intro τ h h0
    have h1 := hp τ h
    have hs := hsgpos τ (hpos τ h)
    have h2 : m τ - L = 0 := h0
    rw [h2, abs_zero] at h1
    nlinarith
  have hd0 : ∀ τ : ℝ, 0 < τ → HasDerivAt ϕ1 (m1 τ) τ := fun τ hτ => by
    exact (hM.d0 τ hτ).sub_const L
  set Q := ibpQ B B1 B2 ϕ1 m1 m2 with hQ
  have hQb : ∀ τ : ℝ, a ≤ τ → ‖Q τ‖ ≤ K1 * (τ ^ (-11 / 2 : ℝ) + τ ^ (-5 / 2 : ℝ)) := by
    intro τ h
    have hτ := hpos τ h
    have hsg := hsgpos τ hτ
    have h1 := Q_pt (τ := τ) (p := γ * sg τ) (γ := γ) (C0 := C0) (KB := KB) hτ (by positivity) hγ hC0 hKB le_rfl
      (ϕ1 := ϕ1) (ϕ2 := m1) (ϕ3 := m2) (B := B) (B1 := B1) (B2 := B2) (hp τ h) (hM.abs_m1 hτ) (hM.b2 τ hτ)
      (hbB τ hτ) (hbB1 τ hτ) (hbB2 τ hτ)
    refine h1.trans ?_
    have h4 := wt_div_sg_sq_le hτ
    calc KB * K0 * wt τ / (γ * sg τ) ^ 2 = (KB * K0 / γ ^ 2) * (wt τ / sg τ ^ 2) := by field_simp
      _ ≤ (KB * K0 / γ ^ 2) * (4 * (τ ^ (-11 / 2 : ℝ) + τ ^ (-5 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = K1 * (τ ^ (-11 / 2 : ℝ) + τ ^ (-5 / 2 : ℝ)) := by rw [hK1]; ring
  have hgint : IntegrableOn (fun τ : ℝ => K1 * (τ ^ (-11 / 2 : ℝ) + τ ^ (-5 / 2 : ℝ))) (Ioi a) :=
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) ha).add (integrableOn_Ioi_rpow_of_lt (by norm_num) ha)).const_mul K1
  set E : ℝ → ℂ := fun τ => Complex.exp (Complex.I * lam * (ϕ τ : ℂ)) with hE
  have hcont_ϕ : ∀ τ : ℝ, 0 < τ → ContinuousAt ϕ τ := fun τ hτ => (hϕ τ hτ).continuousAt
  have hQc : ContinuousOn Q (Ici a) := by
    refine continuousOn_ibpQ (S := Ici a) ?_ ?_ (hc2.mono fun τ hτ => hpos τ hτ) ?_ ?_ ?_ (fun τ hτ => hne τ hτ)
    · exact fun τ hτ => (hB τ (hpos τ hτ)).continuousAt.continuousWithinAt
    · exact fun τ hτ => (hB1 τ (hpos τ hτ)).continuousAt.continuousWithinAt
    · exact fun τ hτ => (((hM.d0 τ (hpos τ hτ)).sub_const L).continuousAt).continuousWithinAt
    · exact hM.cont_m1.mono fun τ hτ => hpos τ hτ
    · exact hM.cont_m2.mono fun τ hτ => hpos τ hτ
  have hQEc : ContinuousOn (fun τ => Q τ * E τ) (Ioi a) := by
    refine (hQc.mono Ioi_subset_Ici_self).mul ?_
    refine Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul ?_)
    exact Complex.continuous_ofReal.comp_continuousOn
      (fun τ hτ => (hcont_ϕ τ (hpos τ (le_of_lt hτ))).continuousWithinAt)
  have hQEint : IntegrableOn (fun τ => Q τ * E τ) (Ioi a) := by
    refine Integrable.mono' hgint (hQEc.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun τ hτ => ?_)
    rw [norm_mul, norm_cexp_phase, mul_one]
    exact hQb τ (le_of_lt hτ)
  set J : ℂ := ∫ τ in Ioi a, Q τ * E τ with hJ
  have hJt : Tendsto (fun b : ℝ => ∫ τ in a..b, Q τ * E τ) atTop (𝓝 J) :=
    intervalIntegral_tendsto_integral_Ioi a hQEint tendsto_id
  have hJb : ‖J‖ ≤ K1 * ((2 / 9) * a ^ (-9 / 2 : ℝ) + (2 / 3) * a ^ (-3 / 2 : ℝ)) := by
    have h1 : ‖J‖ ≤ ∫ τ in Ioi a, K1 * (τ ^ (-11 / 2 : ℝ) + τ ^ (-5 / 2 : ℝ)) :=
      norm_integral_le_of_norm_le hgint ((ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun τ hτ => by rw [norm_mul, norm_cexp_phase, mul_one]; exact hQb τ hτ.le))
    refine h1.trans (le_of_eq ?_)
    have i1 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-11 / 2 : ℝ) < -1) ha
    have i2 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-5 / 2 : ℝ) < -1) ha
    rw [integral_const_mul, integral_add i1 i2, integral_Ioi_rpow_of_lt (by norm_num : (-11 / 2 : ℝ) < -1) ha,
      integral_Ioi_rpow_of_lt (by norm_num : (-5 / 2 : ℝ) < -1) ha]
    have e1 : (-11 / 2 : ℝ) + 1 = -9 / 2 := by norm_num
    have e2 : (-5 / 2 : ℝ) + 1 = -3 / 2 := by norm_num
    rw [e1, e2]; ring
  have hF : ∀ b : ℝ, a ≤ b → ∫ τ in a..b, B τ * E τ =
      (1 / (Complex.I * lam)) * (B b / (ϕ1 b : ℂ) * E b) -
        (1 / (Complex.I * lam)) ^ 2 * (ibpH B B1 ϕ1 m1 b / (ϕ1 b : ℂ) * E b) +
        (1 / (Complex.I * lam)) ^ 2 * (∫ τ in a..b, Q τ * E τ) -
      ((1 / (Complex.I * lam)) * (B a / (ϕ1 a : ℂ) * E a) -
        (1 / (Complex.I * lam)) ^ 2 * (ibpH B B1 ϕ1 m1 a / (ϕ1 a : ℂ) * E a)) := by
    intro b hab
    have hI : ∀ x ∈ Icc a b, 0 < x := fun x hx => hpos x hx.1
    have := ibp_twice hab hlam.ne' (ϕ := ϕ) (ϕ1 := ϕ1) (ϕ2 := m1) (ϕ3 := m2) (B := B) (B1 := B1) (B2 := B2)
      (fun x hx => hϕ x (hI x hx)) (fun x hx => hd0 x (hI x hx)) (fun x hx => hM.d1 x (hI x hx))
      (fun x hx => hne x hx.1) (fun x hx => hB x (hI x hx)) (fun x hx => hB1 x (hI x hx))
      (hc2.mono (fun x hx => hI x hx)) (hM.cont_m2.mono (fun x hx => hI x hx))
    rw [this]
    simp only [hE, hQ]
    ring
  have hrpow0 : Tendsto (fun b : ℝ => b ^ (-1 / 2 : ℝ)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)
    simpa [neg_div] using this
  have hbig : ∀ b : ℝ, max a 1 ≤ b → 0 < b ∧ 1 ≤ b ∧ a ≤ b ∧ γ / 2 ≤ |ϕ1 b| := by
    intro b hb
    have hb1 : 1 ≤ b := (le_max_right _ _).trans hb
    have hba : a ≤ b := (le_max_left _ _).trans hb
    have hb0 : 0 < b := by linarith
    have hsg : 1 / 2 ≤ sg b := by
      unfold sg; rw [le_div_iff₀ (by positivity)]; nlinarith
    have := hp b hba
    exact ⟨hb0, hb1, hba, by nlinarith⟩
  have hT1 : Tendsto (fun b : ℝ => (1 / (Complex.I * lam)) * (B b / (ϕ1 b : ℂ) * E b)) atTop (𝓝 0) := by
    have hm : Tendsto (fun b : ℝ => (2 * KB / (γ * lam)) * b ^ (-1 / 2 : ℝ)) atTop (𝓝 0) := by
      simpa using hrpow0.const_mul (2 * KB / (γ * lam))
    refine squeeze_zero_norm' ?_ hm
    filter_upwards [eventually_ge_atTop (max a 1)] with b hb
    obtain ⟨hb0, hb1, hba, hϕb⟩ := hbig b hb
    have hBb : ‖B b‖ ≤ KB * b ^ (-1 / 2 : ℝ) := by
      refine (hbB b hb0).trans ?_
      calc KB * b ^ (1 / 2 : ℝ) / (1 + b) = KB * (b ^ (1 / 2 : ℝ) / (1 + b)) := by ring
        _ ≤ KB * b ^ (-1 / 2 : ℝ) := mul_le_mul_of_nonneg_left (rpow_half_le_div hb1) hKB
    rw [norm_mul, norm_inv_I_mul hlam, norm_mul, norm_div, hE]
    simp only [norm_cexp_phase, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hg2 : 0 < γ / 2 := by positivity
    calc 1 / lam * (‖B b‖ / |ϕ1 b|) ≤ 1 / lam * (KB * b ^ (-1 / 2 : ℝ) / (γ / 2)) := by
          gcongr
      _ = 2 * KB / (γ * lam) * b ^ (-1 / 2 : ℝ) := by field_simp
  have hT2 : Tendsto (fun b : ℝ => (1 / (Complex.I * lam)) ^ 2 * (ibpH B B1 ϕ1 m1 b / (ϕ1 b : ℂ) * E b)) atTop (𝓝 0) := by
    have hm : Tendsto (fun b : ℝ => (4 * KB * (1 + C0 / γ) / (γ ^ 2 * lam ^ 2)) * b ^ (-1 / 2 : ℝ)) atTop (𝓝 0) := by
      simpa using hrpow0.const_mul (4 * KB * (1 + C0 / γ) / (γ ^ 2 * lam ^ 2))
    refine squeeze_zero_norm' ?_ hm
    filter_upwards [eventually_ge_atTop (max a 1)] with b hb
    obtain ⟨hb0, hb1, hba, hϕb⟩ := hbig b hb
    have hsg : 1 / 2 ≤ sg b := by
      unfold sg; rw [le_div_iff₀ (by positivity)]; nlinarith
    have hHb := H_pt (τ := b) (p := γ * sg b) (γ := γ) (C0 := C0) (KB := KB) hb0 (by positivity) hγ hC0 hKB le_rfl
      (ϕ1 := ϕ1) (ϕ2 := m1) (B := B) (B1 := B1) (hp b hba) (hM.abs_m1 hb0) (hbB b hb0) (hbB1 b hb0)
    have hwb : b ^ (-1 / 2 : ℝ) / (1 + b) ≤ b ^ (-1 / 2 : ℝ) :=
      div_le_self (by positivity) (by linarith)
    have hHb2 : ‖ibpH B B1 ϕ1 m1 b‖ ≤ KB * (1 + C0 / γ) * b ^ (-1 / 2 : ℝ) / (γ / 2) := by
      refine hHb.trans ?_
      have : γ / 2 ≤ γ * sg b := by nlinarith
      have step : KB * (1 + C0 / γ) * (b ^ (-1 / 2 : ℝ) / (1 + b)) / (γ * sg b) ≤
          KB * (1 + C0 / γ) * b ^ (-1 / 2 : ℝ) / (γ / 2) := by
        have h5 : KB * (1 + C0 / γ) * (b ^ (-1 / 2 : ℝ) / (1 + b)) ≤ KB * (1 + C0 / γ) * b ^ (-1 / 2 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hwb (by positivity)
        exact div_le_div₀ (by positivity) h5 (by positivity) this
      exact step
    rw [norm_mul, norm_pow, norm_inv_I_mul hlam, norm_mul, norm_div, hE]
    simp only [norm_cexp_phase, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hg2 : 0 < γ / 2 := by positivity
    calc (1 / lam) ^ 2 * (‖ibpH B B1 ϕ1 m1 b‖ / |ϕ1 b|) ≤
        (1 / lam) ^ 2 * (KB * (1 + C0 / γ) * b ^ (-1 / 2 : ℝ) / (γ / 2) / (γ / 2)) := by
          gcongr
      _ = 4 * KB * (1 + C0 / γ) / (γ ^ 2 * lam ^ 2) * b ^ (-1 / 2 : ℝ) := by field_simp; ring
  refine ⟨J, ?_, hJb⟩
  have hsum := (((hT1.sub hT2).add (hJt.const_mul ((1 / (Complex.I * lam)) ^ 2))).sub
    (tendsto_const_nhds (x := (1 / (Complex.I * lam)) * (B a / (ϕ1 a : ℂ) * E a) -
        (1 / (Complex.I * lam)) ^ 2 * (ibpH B B1 ϕ1 m1 a / (ϕ1 a : ℂ) * E a))))
  refine (hsum.congr' ?_).trans_eq ?_
  · filter_upwards [eventually_ge_atTop a] with b hb
    exact (hF b hb).symm
  · simp only [sub_zero, zero_add, ϕ1, E]
    ring

/-- **Piece 3.** For `B` vanishing (with `B'`) at `a`, `|m - L| ≥ γ σ` on `[a, ∞)`, the improper integral of `B e^{iλϕ}`
over `[a,∞)` exists and is `O(λ^{-2}(a^{-9/2} + a^{-3/2}))`. -/
theorem piece3 (hM : MData C0 m m1 m2 m3) {γ KB lam L a : ℝ} (hγ : 0 < γ) (hKB : 0 ≤ KB) (hlam : 0 < lam)
    (ha : 0 < a) {ϕ : ℝ → ℝ} (hϕ : ∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - L) τ)
    {B B1 B2 : ℝ → ℂ} (hB : ∀ τ : ℝ, 0 < τ → HasDerivAt B (B1 τ) τ)
    (hB1 : ∀ τ : ℝ, 0 < τ → HasDerivAt B1 (B2 τ) τ) (hc2 : ContinuousOn B2 (Ioi 0))
    (hbB : ∀ τ : ℝ, 0 < τ → ‖B τ‖ ≤ KB * τ ^ (1 / 2 : ℝ) / (1 + τ))
    (hbB1 : ∀ τ : ℝ, 0 < τ → ‖B1 τ‖ ≤ KB * τ ^ (-1 / 2 : ℝ) / (1 + τ))
    (hbB2 : ∀ τ : ℝ, 0 < τ → ‖B2 τ‖ ≤ KB * τ ^ (-3 / 2 : ℝ) / (1 + τ))
    (hB0 : B a = 0) (hB10 : B1 a = 0) (hp : ∀ τ : ℝ, a ≤ τ → γ * sg τ ≤ |m τ - L|) :
    ∃ I : ℂ, Tendsto (fun b : ℝ => ∫ τ in a..b, B τ * Complex.exp (Complex.I * lam * (ϕ τ : ℂ))) atTop (𝓝 I) ∧
      ‖I‖ ≤ (4 * KB * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) / γ ^ 2 / lam ^ 2) *
        ((2 / 9) * a ^ (-9 / 2 : ℝ) + (2 / 3) * a ^ (-3 / 2 : ℝ)) := by
  obtain ⟨J, hJt, hJb⟩ := piece3_gen hM hγ hKB hlam ha hϕ hB hB1 hc2 hbB hbB1 hbB2 hp
  refine ⟨(1 / (Complex.I * lam)) ^ 2 * J, ?_, ?_⟩
  · have hH : ibpH B B1 (fun τ => m τ - L) m1 a = 0 := by unfold ibpH; simp [hB0, hB10]
    simpa [hB0, hH] using hJt
  · rw [norm_mul, norm_pow, norm_inv_I_mul hlam]
    calc (1 / lam) ^ 2 * ‖J‖ ≤ (1 / lam) ^ 2 * ((4 * KB * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) / γ ^ 2) *
          ((2 / 9) * a ^ (-9 / 2 : ℝ) + (2 / 3) * a ^ (-3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hJb (by positivity)
      _ = _ := by ring

end

/-- info: 'FormalResearch.SignUncertainty.CtOsc.piece3_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms piece3_gen

end FormalResearch.SignUncertainty.CtOsc
