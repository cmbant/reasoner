module

public import FormalResearch.ModularBootstrap.FiveTerm.OuterPhase
public import FormalResearch.ModularBootstrap.FiveTerm.OuterRestDeriv
public import FormalResearch.ModularBootstrap.FiveTerm.OuterStripStatements
public import FormalResearch.Complex.StripBdryFunctional

/-!
# `θ_out` in the strip variable: master formula, derivatives and decay (FIVE-S, S2 core)

`thetaOutT τ = (1/4) arctan sinh πτ - (5/2) arctan tanh(πτ/4) + F_{a_rest}(τ)` (`thetaOutT_eq`), obtained from
`Im H_xb(iτ) = (1/4)(arctan sinh πτ - arctan 2 v_T)` (`OuterPhase`) and `Im h̄_{a_rest}(iτ) = F_{a_rest}(τ)`.  Then
`thetaOutT` is twice differentiable with `|θ'|, |θ''| ≤ C e^{-πτ/2}` (`τ ≥ 0`), odd, and approaches a limit
`L` exponentially (`thetaOutT_data`).  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

lemma im_hbarA_aRest (τ : ℝ) : (hbarA aRest ((τ : ℂ) * Complex.I)).im = bdryF aRest τ := by
  obtain ⟨d1, d2, d3, h1, h2, h3, ⟨B1, hB1⟩, ⟨A, hA⟩⟩ := aRest_deriv_data
  obtain ⟨M, hM⟩ := aRest_wlog
  have hc : Continuous d1 := continuous_iff_continuousAt.2 fun t => (h2 t).continuousAt
  rw [mul_comm]
  exact im_hbarA_eq_bdryF amp_aRest hM (fun τ => localLip_of_deriv h1 hc τ) τ

/-- **The master formula for `θ_out`.** -/
theorem thetaOutT_eq (τ : ℝ) :
    thetaOutT τ = (1 / 4) * Real.arctan (Real.sinh (π * τ)) - (5 / 2) * Real.arctan (Real.tanh (π * τ / 4)) +
      bdryF aRest τ := by
  unfold thetaOutT
  have h : hbarA aAmp ((τ : ℂ) * Complex.I) = Hxb ((τ : ℂ) * Complex.I) + hbarA aRest ((τ : ℂ) * Complex.I) := by
    unfold Hxb; ring
  rw [h, Complex.add_im, im_Hxb_left_edge, im_hbarA_aRest]
  unfold thetaXb
  ring

lemma thetaOutT_zero : thetaOutT 0 = 0 := by
  have h := hbarA_conj amp_aAmp (ζ := (0 : ℂ)) ⟨by simp, by simp⟩
  rw [map_zero] at h
  have him : (hbarA aAmp 0).im = 0 := by
    have := congrArg Complex.im h; simp at this; linarith
  unfold thetaOutT
  simp only [Complex.ofReal_zero, zero_mul]
  rw [him, vT_zero]; simp

lemma thetaOutT_neg (τ : ℝ) : thetaOutT (-τ) = -thetaOutT τ := by
  unfold thetaOutT
  have h := hbarA_conj amp_aAmp (ζ := (τ : ℂ) * Complex.I) ⟨by simp, by simp⟩
  have hz : starRingEnd ℂ ((τ : ℂ) * Complex.I) = ((-τ : ℝ) : ℂ) * Complex.I := by simp
  rw [hz] at h
  have him : (hbarA aAmp (((-τ : ℝ) : ℂ) * Complex.I)).im = -(hbarA aAmp ((τ : ℂ) * Complex.I)).im := by
    rw [h]; simp
  rw [him, vT_odd, show π * -τ / 4 = -(π * τ / 4) by ring, Real.tanh_neg]
  simp only [mul_neg, Real.arctan_neg]
  ring

lemma sech_le (a x : ℝ) (ha : 0 < a) : 1 / Real.cosh (a * x) ≤ 2 * Real.exp (-(a * |x|)) := by
  have h := exp_abs_div_two_le_cosh (a * x)
  have h1 : |a * x| = a * |x| := by rw [abs_mul, abs_of_pos ha]
  rw [h1] at h
  have hp : 0 < Real.exp (a * |x|) / 2 := by positivity
  calc 1 / Real.cosh (a * x) ≤ 1 / (Real.exp (a * |x|) / 2) := one_div_le_one_div_of_le hp h
    _ = 2 * Real.exp (-(a * |x|)) := by rw [Real.exp_neg]; field_simp

lemma abs_sinh_div_cosh_sq_le (a x : ℝ) (ha : 0 < a) :
    |Real.sinh (a * x) / Real.cosh (a * x) ^ 2| ≤ 2 * Real.exp (-(a * |x|)) := by
  have hc := Real.cosh_pos (a * x)
  have h1 : |Real.sinh (a * x)| ≤ Real.cosh (a * x) := by
    have := abs_le_of_sq_le_sq' (a := Real.sinh (a * x)) (b := Real.cosh (a * x))
      (by nlinarith [Real.cosh_sq (a * x)]) hc.le
    exact abs_le.mpr this
  rw [abs_div, abs_of_pos (by positivity : 0 < Real.cosh (a * x) ^ 2)]
  calc |Real.sinh (a * x)| / Real.cosh (a * x) ^ 2 ≤ Real.cosh (a * x) / Real.cosh (a * x) ^ 2 :=
        div_le_div_of_nonneg_right h1 (by positivity)
    _ = 1 / Real.cosh (a * x) := by field_simp
    _ ≤ _ := sech_le a x ha


/-- A `C¹` function whose derivative is `O(e^{-πτ/2})` on `[0,∞)` converges exponentially. -/
lemma exists_limit_of_decay {f f' : ℝ → ℝ} (hd : ∀ τ, HasDerivAt f (f' τ) τ) {C : ℝ}
    (hC : ∀ τ : ℝ, 0 ≤ τ → |f' τ| ≤ C * Real.exp (-((π / 2) * τ))) :
    ∃ L : ℝ, ∀ τ : ℝ, 0 ≤ τ → |f τ - L| ≤ 2 * C / π * Real.exp (-((π / 2) * τ)) := by
  have hpi := Real.pi_pos
  have hC0 : 0 ≤ C := by
    have := hC 0 le_rfl
    simp at this
    exact (abs_nonneg _).trans this
  set c : ℝ := 2 * C / π with hc
  have hc0 : 0 ≤ c := by positivity
  have hE : ∀ τ : ℝ, HasDerivAt (fun τ => Real.exp (-((π / 2) * τ))) (-(π / 2) * Real.exp (-((π / 2) * τ))) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℝ => -((π / 2) * τ)) (-(π / 2)) τ := by
      exact (((hasDerivAt_id τ).const_mul (π / 2)).neg).congr_deriv (by simp)
    have h2 := h1.exp
    refine h2.congr_deriv ?_
    ring
  have hcpi : c * (π / 2) = C := by rw [hc]; field_simp
  set u : ℝ → ℝ := fun τ => f τ + c * Real.exp (-((π / 2) * τ)) with hu
  set v : ℝ → ℝ := fun τ => f τ - c * Real.exp (-((π / 2) * τ)) with hv
  have hu' : ∀ τ, HasDerivAt u (f' τ + c * (-(π / 2) * Real.exp (-((π / 2) * τ)))) τ :=
    fun τ => (hd τ).add ((hE τ).const_mul c)
  have hv' : ∀ τ, HasDerivAt v (f' τ - c * (-(π / 2) * Real.exp (-((π / 2) * τ)))) τ :=
    fun τ => (hd τ).sub ((hE τ).const_mul c)
  have hanti : AntitoneOn u (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) (fun τ _ => (hu' τ).continuousAt.continuousWithinAt)
      (fun τ _ => (hu' τ).differentiableAt.differentiableWithinAt) (fun τ hτ => ?_)
    rw [(hu' τ).deriv]
    have hτ0 : 0 ≤ τ := le_of_lt (by simpa using hτ)
    have := hC τ hτ0
    have h2 := (abs_le.mp this).2
    have : c * (-(π / 2) * Real.exp (-((π / 2) * τ))) = -(C * Real.exp (-((π / 2) * τ))) := by
      rw [← hcpi]; ring
    rw [this]; linarith
  have hmono : MonotoneOn v (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun τ _ => (hv' τ).continuousAt.continuousWithinAt)
      (fun τ _ => (hv' τ).differentiableAt.differentiableWithinAt) (fun τ hτ => ?_)
    rw [(hv' τ).deriv]
    have hτ0 : 0 ≤ τ := le_of_lt (by simpa using hτ)
    have := hC τ hτ0
    have h2 := (abs_le.mp this).1
    have : c * (-(π / 2) * Real.exp (-((π / 2) * τ))) = -(C * Real.exp (-((π / 2) * τ))) := by
      rw [← hcpi]; ring
    rw [this]; linarith
  have hvu : ∀ τ, v τ ≤ u τ := fun τ => by
    simp only [hu, hv]; nlinarith [mul_nonneg hc0 (Real.exp_pos (-((π / 2) * τ))).le]
  have hbdd : BddAbove (v '' Ici 0) := by
    refine ⟨u 0, ?_⟩
    rintro _ ⟨τ, hτ, rfl⟩
    exact (hvu τ).trans (hanti (show (0 : ℝ) ∈ Ici 0 from le_rfl) hτ hτ)
  refine ⟨sSup (v '' Ici 0), fun τ hτ => ?_⟩
  have hne : (v '' Ici 0).Nonempty := ⟨v 0, 0, le_rfl, rfl⟩
  have h1 : v τ ≤ sSup (v '' Ici 0) := le_csSup hbdd ⟨τ, hτ, rfl⟩
  have h2 : sSup (v '' Ici 0) ≤ u τ := by
    refine csSup_le hne ?_
    rintro _ ⟨τ', hτ', rfl⟩
    rcases le_total τ' τ with h | h
    · exact (hmono hτ' hτ h).trans (hvu τ)
    · exact (hvu τ').trans (hanti hτ hτ' h)
  rw [abs_le]
  simp only [hu, hv] at h1 h2
  constructor <;> linarith


/-- `ε(τ) = (1/4) arctan sinh πτ - (5/2) arctan tanh(πτ/4)`. -/
noncomputable def epsT (τ : ℝ) : ℝ :=
  (1 / 4) * Real.arctan (Real.sinh (π * τ)) - (5 / 2) * Real.arctan (Real.tanh (π * τ / 4))

lemma hasDerivAt_sech (k t : ℝ) :
    HasDerivAt (fun t : ℝ => (Real.cosh (π * t / k))⁻¹)
      (-(Real.sinh (π * t / k) * (π / k)) / Real.cosh (π * t / k) ^ 2) t :=
  (hasDerivAt_cosh_arg k t).inv (Real.cosh_pos _).ne'

/-- `ε' = (π/4) sech πτ - (5π/8) sech(πτ/2)`. -/
noncomputable def e1 (τ : ℝ) : ℝ :=
  (π / 4) * (Real.cosh (π * τ / 1))⁻¹ - (5 * π / 8) * (Real.cosh (π * τ / 2))⁻¹

noncomputable def e2 (τ : ℝ) : ℝ :=
  (π / 4) * (-(Real.sinh (π * τ / 1) * (π / 1)) / Real.cosh (π * τ / 1) ^ 2) -
    (5 * π / 8) * (-(Real.sinh (π * τ / 2) * (π / 2)) / Real.cosh (π * τ / 2) ^ 2)

lemma hasDerivAt_epsT (τ : ℝ) : HasDerivAt epsT (e1 τ) τ := by
  have hpi := Real.pi_pos
  have hs : HasDerivAt (fun τ : ℝ => Real.sinh (π * τ)) (Real.cosh (π * τ) * π) τ := by
    simpa using hasDerivAt_sinh_arg 1 τ
  have h1 := (hs.arctan).const_mul (1 / 4)
  have h2 := ((hasDerivAt_tanh_arg 4 τ).arctan).const_mul (5 / 2)
  have h := h1.sub h2
  unfold epsT e1
  refine h.congr_deriv ?_
  have hc1 : 0 < Real.cosh (π * τ) := Real.cosh_pos _
  have hc2 : 0 < Real.cosh (π * τ / 2) := Real.cosh_pos _
  have hc4 : 0 < Real.cosh (π * τ / 4) := Real.cosh_pos _
  have e1' : 1 + Real.sinh (π * τ) ^ 2 = Real.cosh (π * τ) ^ 2 := by nlinarith [Real.cosh_sq (π * τ)]
  have e2' : Real.cosh (π * τ / 2) = Real.cosh (π * τ / 4) ^ 2 + Real.sinh (π * τ / 4) ^ 2 := by
    rw [show π * τ / 2 = 2 * (π * τ / 4) by ring, Real.cosh_two_mul]
  rw [e1', Real.tanh_eq_sinh_div_cosh, e2']
  field_simp
  nlinarith [Real.cosh_sq (π * τ / 4)]


lemma hasDerivAt_e1 (τ : ℝ) : HasDerivAt e1 (e2 τ) τ := by
  have h := (((hasDerivAt_sech 1 τ).const_mul (π / 4)).sub ((hasDerivAt_sech 2 τ).const_mul (5 * π / 8)))
  unfold e1 e2
  exact h

lemma abs_e1_e2_le (τ : ℝ) :
    |e1 τ| ≤ (π / 2 + 5 * π / 4) * Real.exp (-((π / 2) * |τ|)) ∧
    |e2 τ| ≤ (π ^ 2 / 2 + 5 * π ^ 2 / 8) * Real.exp (-((π / 2) * |τ|)) := by
  have hpi := Real.pi_pos
  have s1 := sech_le π τ hpi
  have s2 := sech_le (π / 2) τ (by positivity)
  have t1 := abs_sinh_div_cosh_sq_le π τ hpi
  have t2 := abs_sinh_div_cosh_sq_le (π / 2) τ (by positivity)
  have hp1 : Real.cosh (π * τ / 1) = Real.cosh (π * τ) := by rw [div_one]
  have hp2 : Real.cosh (π * τ / 2) = Real.cosh (π / 2 * τ) := by congr 1; ring
  have hq1 : Real.sinh (π * τ / 1) = Real.sinh (π * τ) := by rw [div_one]
  have hq2 : Real.sinh (π * τ / 2) = Real.sinh (π / 2 * τ) := by congr 1; ring
  have hE1 : Real.exp (-(π * |τ|)) ≤ Real.exp (-((π / 2) * |τ|)) := by
    apply Real.exp_le_exp.mpr; nlinarith [abs_nonneg τ]
  have hE0 := Real.exp_pos (-((π / 2) * |τ|))
  constructor
  · unfold e1
    rw [hp1, hp2]
    have a1 : |(π / 4) * (Real.cosh (π * τ))⁻¹| ≤ (π / 4) * (2 * Real.exp (-(π * |τ|))) := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < π / 4), abs_of_pos (inv_pos.mpr (Real.cosh_pos _))]
      exact mul_le_mul_of_nonneg_left (by simpa [one_div] using s1) (by positivity)
    have a2 : |(5 * π / 8) * (Real.cosh (π / 2 * τ))⁻¹| ≤ (5 * π / 8) * (2 * Real.exp (-(π / 2 * |τ|))) := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 5 * π / 8), abs_of_pos (inv_pos.mpr (Real.cosh_pos _))]
      exact mul_le_mul_of_nonneg_left (by simpa [one_div] using s2) (by positivity)
    have := abs_sub ((π / 4) * (Real.cosh (π * τ))⁻¹) ((5 * π / 8) * (Real.cosh (π / 2 * τ))⁻¹)
    nlinarith
  · unfold e2
    rw [hp1, hp2, hq1, hq2]
    have a1 : |(π / 4) * (-(Real.sinh (π * τ) * (π / 1)) / Real.cosh (π * τ) ^ 2)| ≤
        (π / 4) * (π * (2 * Real.exp (-(π * |τ|)))) := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < π / 4)]
      have : |-(Real.sinh (π * τ) * (π / 1)) / Real.cosh (π * τ) ^ 2| =
          π * |Real.sinh (π * τ) / Real.cosh (π * τ) ^ 2| := by
        rw [show -(Real.sinh (π * τ) * (π / 1)) / Real.cosh (π * τ) ^ 2 =
          -(π * (Real.sinh (π * τ) / Real.cosh (π * τ) ^ 2)) by ring, abs_neg, abs_mul, abs_of_pos hpi]
      rw [this]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left t1 hpi.le) (by positivity)
    have a2 : |(5 * π / 8) * (-(Real.sinh (π / 2 * τ) * (π / 2)) / Real.cosh (π / 2 * τ) ^ 2)| ≤
        (5 * π / 8) * (π / 2 * (2 * Real.exp (-(π / 2 * |τ|)))) := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < 5 * π / 8)]
      have : |-(Real.sinh (π / 2 * τ) * (π / 2)) / Real.cosh (π / 2 * τ) ^ 2| =
          π / 2 * |Real.sinh (π / 2 * τ) / Real.cosh (π / 2 * τ) ^ 2| := by
        rw [show -(Real.sinh (π / 2 * τ) * (π / 2)) / Real.cosh (π / 2 * τ) ^ 2 =
          -(π / 2 * (Real.sinh (π / 2 * τ) / Real.cosh (π / 2 * τ) ^ 2)) by ring, abs_neg, abs_mul,
          abs_of_pos (by positivity : 0 < π / 2)]
      rw [this]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left t2 (by positivity)) (by positivity)
    have := abs_sub ((π / 4) * (-(Real.sinh (π * τ) * (π / 1)) / Real.cosh (π * τ) ^ 2))
      ((5 * π / 8) * (-(Real.sinh (π / 2 * τ) * (π / 2)) / Real.cosh (π / 2 * τ) ^ 2))
    nlinarith


/-- **`θ_out` in the strip variable (S2 core).**  `thetaOutT` is twice differentiable, odd, vanishes at `0`,
`|θ'|, |θ''| ≤ C e^{-πτ/2}` on `τ ≥ 0`, and `|θ - L| ≤ C e^{-πτ/2}` for some limit `L`. -/
theorem thetaOutT_data : ∃ C : ℝ, 0 < C ∧ ∃ Θ1 Θ2 : ℝ → ℝ,
    (∀ τ, HasDerivAt thetaOutT (Θ1 τ) τ) ∧ (∀ τ, HasDerivAt Θ1 (Θ2 τ) τ) ∧
    (∀ τ : ℝ, 0 ≤ τ → |Θ1 τ| ≤ C * Real.exp (-((π / 2) * τ)) ∧ |Θ2 τ| ≤ C * Real.exp (-((π / 2) * τ))) ∧
    thetaOutT 0 = 0 ∧ (∀ τ, thetaOutT (-τ) = -thetaOutT τ) ∧
    ∃ L : ℝ, ∀ τ : ℝ, 0 ≤ τ → |thetaOutT τ - L| ≤ C * Real.exp (-((π / 2) * τ)) := by
  have hpi := Real.pi_pos
  obtain ⟨d1, d2, d3, h1, h2, h3, ⟨B1, hB1⟩, ⟨A, hA⟩⟩ := aRest_deriv_data
  obtain ⟨C0, hC0pos, hC0⟩ := StripBdry.abs_bdryF_decay_half
  have hA0 : 0 ≤ A := by
    have := (hA 0).1
    simp at this
    exact (abs_nonneg _).trans this
  have hexp1 : ∀ t : ℝ, Real.exp (-((π / 2) * |t|)) ≤ 1 := fun t => by
    rw [← Real.exp_zero]; apply Real.exp_le_exp.mpr; nlinarith [abs_nonneg t]
  have hd2 : ∀ t, |d2 t| ≤ A := fun t => ((hA t).1).trans (by nlinarith [hexp1 t, Real.exp_pos (-((π / 2) * |t|))])
  have hd3 : ∀ t, |d3 t| ≤ A := fun t => ((hA t).2).trans (by nlinarith [hexp1 t, Real.exp_pos (-((π / 2) * |t|))])
  have hF1 : ∀ τ, HasDerivAt (bdryF aRest) (bdryF d1 τ) τ :=
    fun τ => StripBdry.hasDerivAt_bdryF_lin h1 h2 hB1 hd2 τ
  have hF2 : ∀ τ, HasDerivAt (bdryF d1) (bdryF d2 τ) τ :=
    fun τ => StripBdry.hasDerivAt_bdryF_lin h2 h3 hd2 hd3 τ
  have hfun : thetaOutT = fun τ => epsT τ + bdryF aRest τ := by
    funext τ; rw [thetaOutT_eq]; unfold epsT; ring
  have hth : ∀ τ, HasDerivAt thetaOutT (e1 τ + bdryF d1 τ) τ := by
    intro τ; rw [hfun]; exact (hasDerivAt_epsT τ).add (hF1 τ)
  have hth2 : ∀ τ, HasDerivAt (fun τ => e1 τ + bdryF d1 τ) (e2 τ + bdryF d2 τ) τ :=
    fun τ => (hasDerivAt_e1 τ).add (hF2 τ)
  have conv : ∀ {A' : ℝ} {g' : ℝ → ℝ}, (∀ t, |g' t| ≤ A' * Real.exp (-((π / 2) * |t|))) →
      ∀ t, |g' t| ≤ A' * Real.exp (-(π / 2) * |t|) := fun {A'} {g'} h t => by rw [neg_mul]; exact h t
  have b1 : ∀ τ : ℝ, 0 ≤ τ → |bdryF d1 τ| ≤ C0 * (A + B1) * Real.exp (-((π / 2) * τ)) := by
    intro τ hτ
    have := hC0 h2 (conv (fun t => (hA t).1)) hB1 τ hτ
    rwa [neg_mul] at this
  have b2 : ∀ τ : ℝ, 0 ≤ τ → |bdryF d2 τ| ≤ C0 * (A + A) * Real.exp (-((π / 2) * τ)) := by
    intro τ hτ
    have := hC0 h3 (conv (fun t => (hA t).2)) hd2 τ hτ
    rwa [neg_mul] at this
  set K : ℝ := (π / 2 + 5 * π / 4) + C0 * (A + B1) + ((π ^ 2 / 2 + 5 * π ^ 2 / 8) + C0 * (A + A)) + 1 with hK
  have hB1' : 0 ≤ B1 := (abs_nonneg _).trans (hB1 0)
  have hKpos : 0 < K := by
    have : 0 ≤ C0 * (A + B1) := by positivity
    have : 0 ≤ C0 * (A + A) := by positivity
    rw [hK]; positivity
  have hΘ1 : ∀ τ : ℝ, 0 ≤ τ → |e1 τ + bdryF d1 τ| ≤ K * Real.exp (-((π / 2) * τ)) := by
    intro τ hτ
    have hE := Real.exp_pos (-((π / 2) * τ))
    have ha := (abs_e1_e2_le τ).1
    rw [abs_of_nonneg hτ] at ha
    have := b1 τ hτ
    have h0 : 0 ≤ C0 * (A + A) := by positivity
    have h5 : 0 ≤ C0 * (A + B1) := by positivity
    refine (abs_add_le _ _).trans ?_
    nlinarith [mul_nonneg h0 hE.le, mul_nonneg (by positivity : 0 ≤ π ^ 2 / 2 + 5 * π ^ 2 / 8) hE.le, hE]
  have hΘ2 : ∀ τ : ℝ, 0 ≤ τ → |e2 τ + bdryF d2 τ| ≤ K * Real.exp (-((π / 2) * τ)) := by
    intro τ hτ
    have hE := Real.exp_pos (-((π / 2) * τ))
    have ha := (abs_e1_e2_le τ).2
    rw [abs_of_nonneg hτ] at ha
    have := b2 τ hτ
    have h0 : 0 ≤ C0 * (A + B1) := by positivity
    refine (abs_add_le _ _).trans ?_
    nlinarith [mul_nonneg h0 hE.le, mul_nonneg (by positivity : 0 ≤ π / 2 + 5 * π / 4) hE.le, hE]
  obtain ⟨L, hL⟩ := exists_limit_of_decay (f := thetaOutT) hth hΘ1
  refine ⟨K + 2 * K / π, by positivity, fun τ => e1 τ + bdryF d1 τ, fun τ => e2 τ + bdryF d2 τ, hth, hth2,
    fun τ hτ => ⟨?_, ?_⟩, thetaOutT_zero, thetaOutT_neg, L, fun τ hτ => ?_⟩
  · have := hΘ1 τ hτ
    have hE := Real.exp_pos (-((π / 2) * τ))
    nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * K / π) hE.le]
  · have := hΘ2 τ hτ
    have hE := Real.exp_pos (-((π / 2) * τ))
    nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * K / π) hE.le]
  · have := hL τ hτ
    have hE := Real.exp_pos (-((π / 2) * τ))
    nlinarith [mul_nonneg hKpos.le hE.le]

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.thetaOutT_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thetaOutT_data

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
