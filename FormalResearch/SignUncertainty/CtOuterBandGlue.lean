module

public import FormalResearch.SignUncertainty.CtOuterBandExp
public import FormalResearch.SignUncertainty.BinetVertical
public import FormalResearch.SignUncertainty.CtOuterPart3Plus
public import FormalResearch.SignUncertainty.CtDualIdBinet
public import FormalResearch.SignUncertainty.CtOuterBandSqrt

/-!
# The outer amplitude is an `AmpBd`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 4 (`ct:A-derivs`).  **Proved.**
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.SignUncertainty.CtOsc

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem hasDerivAt_iter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → E}
    (hF : ContDiff ℝ ∞' F) (k : ℕ) (τ : ℝ) :
    HasDerivAt (iteratedDeriv k F) (iteratedDeriv (k + 1) F τ) τ := by
  have hd := (hF.differentiable_iteratedDeriv k (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top k))) τ
  have := hd.hasDerivAt
  rwa [← iteratedDeriv_succ] at this

theorem contDiff_binet {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ ∞' (fun τ : ℝ => FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ))) := by
  have hd := BinetDecay.differentiableOn_binetDiff_vertical hc
  have hU : IsOpen {τ : ℂ | -1 < τ.im} := isOpen_lt continuous_const Complex.continuous_im
  have h1 : ContDiffOn ℂ ∞' (fun τ : ℂ => FormalResearch.Asymptotics.binetDiff c (Complex.I * τ)) {τ : ℂ | -1 < τ.im} :=
    hd.contDiffOn hU
  have h2 := h1.restrict_scalars ℝ
  exact h2.comp_contDiff Complex.ofRealCLM.contDiff (fun τ => by simp)

/-- The exponent `g = i(π/4 + θ_ε) - B_c(iτ)`. -/
noncomputable def ampExp (ε c τ : ℝ) : ℂ :=
  Complex.I * ((π / 4 + CtOuter.outerTheta ε τ : ℝ) : ℂ) -
    FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ))

/-- The outer amplitude `A_ε(τ) = √(6 m'(τ)/π²) e^{i(π/4+θ_ε(τ))} e^{-B_c(iτ)}`. -/
noncomputable def outerAmp (ε c τ : ℝ) : ℂ :=
  ((sqf (iteratedDeriv 1 hankelEdgeM) τ : ℝ) : ℂ) * Complex.exp (ampExp ε c τ)

lemma outerAmp_eq {ε c τ : ℝ} (hτ : 0 < τ) :
    outerAmp ε c τ = ((Real.sqrt (6 / π ^ 2 * CtOuter.mPrime τ) : ℝ) : ℂ) *
      (Complex.exp (Complex.I * ((π / 4 + CtOuter.outerTheta ε τ : ℝ) : ℂ)) *
        Complex.exp (-(FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ))))) := by
  unfold outerAmp ampExp sqf
  rw [iteratedDeriv_one_m hτ, sub_eq_add_neg, Complex.exp_add]

/-- **`ct:A-derivs`**: the outer amplitude satisfies `‖A^{(k)}(τ)‖ ≤ C_A τ^{1/2-k}/(1+τ)`, `k = 0,1,2`, uniformly in `c ≥ 2`. -/
theorem outerAmp_ampBd {ε : ℝ} (hε : ε = -1 ∨ ε = 1) :
    ∃ CA : ℝ, 0 ≤ CA ∧ ∀ c : ℝ, 2 ≤ c → ∃ A1 A2 : ℝ → ℂ, AmpBd CA (outerAmp ε c) A1 A2 := by
  obtain ⟨C0, hC0, hMd⟩ := mdata_hankel
  obtain ⟨KF, hKF, hsq⟩ := sqf_bounds hMd
  obtain ⟨-, hθ1⟩ := (CtOuter.ct_outer_part3.2 ε hε 1 le_rfl)
  obtain ⟨-, hθ2⟩ := (CtOuter.ct_outer_part3.2 ε hε 2 (by norm_num))
  obtain ⟨Cθ1, hCθ1⟩ := hθ1
  obtain ⟨Cθ2, hCθ2⟩ := hθ2
  have hθ : ContDiff ℝ ∞' (CtOuter.outerTheta ε) := by
    rcases hε with rfl | rfl <;> exact (CtOuter.contDiff_outerTheta _).of_le le_top
  set Kg : ℝ := |Cθ1| + |Cθ2| + 16 with hKg
  have hKg0 : 0 ≤ Kg := by positivity
  set e12 : ℝ := Real.exp (1 / 12) with he12
  have he12p : 0 < e12 := Real.exp_pos _
  refine ⟨KF * (e12 + 2 * (Kg * e12) + (Kg + Kg ^ 2) * e12), by positivity, fun c hc2 => ?_⟩
  have hc : 0 < c := by linarith
  set β : ℝ → ℂ := fun τ => FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ)) with hβdef
  have hβ : ContDiff ℝ ∞' β := contDiff_binet hc
  set g1 : ℝ → ℂ := fun τ => Complex.I * ((iteratedDeriv 1 (CtOuter.outerTheta ε) τ : ℝ) : ℂ) - iteratedDeriv 1 β τ
    with hg1def
  set g2 : ℝ → ℂ := fun τ => Complex.I * ((iteratedDeriv 2 (CtOuter.outerTheta ε) τ : ℝ) : ℂ) - iteratedDeriv 2 β τ
    with hg2def
  have hgd : ∀ τ : ℝ, 0 < τ → HasDerivAt (ampExp ε c) (g1 τ) τ := by
    intro τ _
    have h1 : HasDerivAt (CtOuter.outerTheta ε) (iteratedDeriv 1 (CtOuter.outerTheta ε) τ) τ := by
      simpa using hasDerivAt_iter hθ 0 τ
    have h2 : HasDerivAt β (iteratedDeriv 1 β τ) τ := by simpa using hasDerivAt_iter hβ 0 τ
    have := (((h1.const_add (π / 4)).ofReal_comp).const_mul Complex.I).sub h2
    exact this
  have hgd1 : ∀ τ : ℝ, 0 < τ → HasDerivAt g1 (g2 τ) τ := by
    intro τ _
    have h1 := hasDerivAt_iter hθ 1 τ
    have h2 := hasDerivAt_iter hβ 1 τ
    exact ((h1.ofReal_comp).const_mul Complex.I).sub h2
  have hg2c : ContinuousOn g2 (Ioi 0) := by
    have c1 : Continuous (iteratedDeriv 2 (CtOuter.outerTheta ε)) := hθ.continuous_iteratedDeriv 2 (by simp)
    have c2 : Continuous (iteratedDeriv 2 β) := hβ.continuous_iteratedDeriv 2 (by simp)
    exact ((continuousOn_const.mul (Complex.continuous_ofReal.comp c1).continuousOn).sub c2.continuousOn)
  have hbeta0 : ∀ τ : ℝ, ‖β τ‖ ≤ 1 / (6 * c) := fun τ =>
    Asymptotics.binetDiff_norm_le_left hc (by simp)
  have hre : ∀ τ : ℝ, 0 < τ → (ampExp ε c τ).re ≤ 1 / 12 := by
    intro τ _
    have h1 : (ampExp ε c τ).re = -(β τ).re := by
      unfold ampExp; simp [hβdef]
    rw [h1]
    have := (neg_le_abs (β τ).re).trans (Complex.abs_re_le_norm (β τ))
    have h3 : 1 / (6 * c) ≤ 1 / 12 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith [hbeta0 τ]
  have hb1 : ∀ τ : ℝ, 0 < τ → ‖g1 τ‖ ≤ Kg / (1 + τ) ^ 2 := by
    intro τ hτ
    have hab : |τ| = τ := abs_of_pos hτ
    have t1 : ‖Complex.I * ((iteratedDeriv 1 (CtOuter.outerTheta ε) τ : ℝ) : ℂ)‖ ≤ |Cθ1| / (1 + τ) ^ 2 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have := hCθ1 τ
      rw [hab] at this
      refine this.trans ?_
      exact div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
    have t2 : ‖iteratedDeriv 1 β τ‖ ≤ 2 / (1 + τ) ^ 2 := by
      have := BinetDecay.binetDiff_vertical_decay hc (r := 1) le_rfl τ
      rw [hab] at this
      rw [show (1 : ℕ) + 1 = 2 from rfl] at this
      simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one] at this
      refine this.trans ?_
      have hp : 0 < (1 + τ) ^ 2 := by positivity
      rw [div_le_div_iff₀ (by positivity) hp]
      nlinarith [mul_le_mul_of_nonneg_right hc2 hp.le]
    refine (norm_sub_le _ _).trans ?_
    have : |Cθ1| / (1 + τ) ^ 2 + 2 / (1 + τ) ^ 2 ≤ Kg / (1 + τ) ^ 2 := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by rw [hKg]; linarith [abs_nonneg Cθ2]) (by positivity)
    linarith
  have hb2 : ∀ τ : ℝ, 0 < τ → ‖g2 τ‖ ≤ Kg / (1 + τ) ^ 3 := by
    intro τ hτ
    have hab : |τ| = τ := abs_of_pos hτ
    have t1 : ‖Complex.I * ((iteratedDeriv 2 (CtOuter.outerTheta ε) τ : ℝ) : ℂ)‖ ≤ |Cθ2| / (1 + τ) ^ 3 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have := hCθ2 τ
      rw [hab] at this
      refine this.trans ?_
      exact div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
    have t2 : ‖iteratedDeriv 2 β τ‖ ≤ 16 / (1 + τ) ^ 3 := by
      have := BinetDecay.binetDiff_vertical_decay hc (r := 2) (by norm_num) τ
      rw [hab] at this
      rw [show (2 : ℕ) + 1 = 3 from rfl] at this
      have h5 : ((2 : ℕ).factorial : ℝ) * 4 ^ 2 = 32 := by norm_num [Nat.factorial]
      rw [h5] at this
      refine this.trans ?_
      have hp : 0 < (1 + τ) ^ 3 := by positivity
      rw [div_le_div_iff₀ (by positivity) hp]
      nlinarith [mul_le_mul_of_nonneg_right hc2 hp.le]
    refine (norm_sub_le _ _).trans ?_
    have : |Cθ2| / (1 + τ) ^ 3 + 16 / (1 + τ) ^ 3 ≤ Kg / (1 + τ) ^ 3 := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by rw [hKg]; linarith [abs_nonneg Cθ1]) (by positivity)
    linarith
  obtain ⟨hG1, hG2, hG2c, hGb0, hGb1, hGb2⟩ := exp_factor hKg0 hgd hgd1 hg2c hre hb1 hb2
  have := ampBd_mul (KF := KF) (KG := e12) (K' := Kg * e12) (K'' := (Kg + Kg ^ 2) * e12) hKF he12p.le
    (by positivity) (by positivity)
    (f := sqf (iteratedDeriv 1 hankelEdgeM)) (f1 := sqf1 (iteratedDeriv 1 hankelEdgeM) (iteratedDeriv 2 hankelEdgeM))
    (f2 := sqf2 (iteratedDeriv 1 hankelEdgeM) (iteratedDeriv 2 hankelEdgeM) (iteratedDeriv 3 hankelEdgeM))
    (fun τ hτ => hasDerivAt_sqf hMd hτ) (fun τ hτ => hasDerivAt_sqf1 hMd hτ) (continuousOn_sqf2 hMd)
    (fun τ hτ => (hsq τ hτ).1) (fun τ hτ => (hsq τ hτ).2.1) (fun τ hτ => (hsq τ hτ).2.2)
    hG1 hG2 hG2c hGb0 hGb1 hGb2
  exact ⟨_, _, this⟩

end FormalResearch.SignUncertainty.CtOsc
