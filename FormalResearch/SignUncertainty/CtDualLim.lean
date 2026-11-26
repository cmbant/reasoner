module

public import FormalResearch.SignUncertainty.CtDualFubini

/-!
# `ct:dual-id` (2): uniform bounds and the limit `δ ↓ 0`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:dual-id` (2), proof (uniform bounds for the
regularised amplitudes, convergence of `K_{ε,δ}` to `K_ε`).  **Proved.**
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

set_option linter.unusedSectionVars false

namespace FormalResearch.SignUncertainty.CtDual

open CtOuter FormalResearch.Asymptotics FormalResearch.CohnElkies CtOsc

lemma improper_split {F : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a) (hint : ∀ b : ℝ, 0 ≤ b → IntervalIntegrable F volume 0 b)
    {I V : ℂ} (hI : Tendsto (fun b : ℝ => ∫ τ in (0 : ℝ)..b, F τ) atTop (𝓝 I))
    (hV : Tendsto (fun b : ℝ => ∫ τ in a..b, F τ) atTop (𝓝 V)) : I = (∫ τ in (0 : ℝ)..a, F τ) + V := by
  have h2 : Tendsto (fun b : ℝ => ∫ τ in (0 : ℝ)..b, F τ) atTop (𝓝 ((∫ τ in (0 : ℝ)..a, F τ) + V)) := by
    refine (hV.const_add _).congr' ?_
    filter_upwards [eventually_ge_atTop a] with b hb
    exact (intervalIntegral_split ha hb (hint b (ha.trans hb))).symm
  exact tendsto_nhds_unique hI h2

lemma hp_eventually {C0 L : ℝ} {m m1 m2 m3 : ℝ → ℝ} (hM : MData C0 m m1 m2 m3) (hm0 : ∀ τ : ℝ, 0 < τ → 0 ≤ m τ)
    (hroot : 0 < L → ∃ τ0 : ℝ, 0 < τ0 ∧ m τ0 = L) :
    ∃ a0 : ℝ, 2 ≤ a0 ∧ ∀ τ : ℝ, a0 ≤ τ → (1 / 4 : ℝ) * sg τ ≤ |m τ - L| := by
  by_cases hL : L ≤ 0
  · refine ⟨2, le_rfl, fun τ hτ => ?_⟩
    have hτp : 0 < τ := by linarith
    have h1 := hM.step (κ := 1 / 2) (by norm_num) (by norm_num) hτp
    have h2 := hm0 (1 / 2 * τ) (by positivity)
    have h3 : (1 / 4 : ℝ) * sg τ ≤ m τ - L := by linarith
    exact h3.trans (le_abs_self _)
  · push_neg at hL
    obtain ⟨τ0, hτ0, rfl⟩ := hroot hL
    exact ⟨max 2 (2 * τ0), le_max_left _ _, fun τ hτ => hp_two hM hτ0 (le_trans (le_max_right _ _) hτ)⟩

/-- Uniform bound for the regularised integrals, `δ ∈ [0,1]`, all `L`, all `c ≥ 2`. -/
lemma unif_data {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ {c : ℝ}, 2 ≤ c → ∀ (L δ : ℝ), 0 ≤ δ → δ ≤ 1 →
      ∃ I : ℂ, Tendsto (fun T : ℝ => ∫ τ in (0 : ℝ)..T,
          outerAmp ε c τ * CtOsc.gcut δ τ * Complex.exp (Complex.I * c * (CtSd.phaseL L τ : ℂ))) atTop (𝓝 I) ∧
        Real.sqrt c * ‖I‖ ≤ Kb := by
  obtain ⟨C0, hC0, hMd⟩ := mdata_hankel
  obtain ⟨CA, hCA, H⟩ := outerAmp_ampBd (ε := ε) (by rcases hε with h | h <;> simp [h])
  obtain ⟨Kb, hKb, HU⟩ := uniform_L C0 (CA * (1 + 2 * 4 + 36)) hC0 (by positivity)
  refine ⟨Kb, hKb, fun {c} hc L δ hδ hδ1 => ?_⟩
  obtain ⟨A1, A2, hA⟩ := H c hc
  exact HU (A := fun τ => outerAmp ε c τ * CtOsc.gcut δ τ) hMd (gcut_ampBd hA hδ hδ1) hc
    (fun τ hτ => (hankelEdgeM_pos hτ).le)
    (fun hL => by
      obtain ⟨τ, hτ0, hτ⟩ := hankelEdgeM_exists_root hL.le
      refine ⟨τ, ?_, hτ⟩
      rcases hτ0.lt_or_eq with h | h
      · exact h
      · rw [← h, hankelEdgeM_zero] at hτ; linarith)
    (fun τ hτ => CtSd.phaseL_deriv L hτ)

lemma norm_gcut_sub_one {δ τ a : ℝ} (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hτa : τ ≤ a) (h1 : δ * (a ^ 2 + a) ≤ 1) :
    ‖CtOsc.gcut δ τ - 1‖ ≤ 2 * (δ * (a ^ 2 + a)) := by
  have hz : ‖(-(δ : ℂ) * ((τ : ℂ) ^ 2 + Complex.I * τ))‖ ≤ δ * (a ^ 2 + a) := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ]
    apply mul_le_mul_of_nonneg_left _ hδ
    refine (norm_add_le _ _).trans ?_
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ]
    nlinarith
  have := Complex.norm_exp_sub_one_le (hz.trans h1)
  unfold CtOsc.gcut
  linarith

/-- Convergence `I_δ → I_0` of the regularised improper integrals as `δ ↓ 0`. -/
lemma delta_conv {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {c : ℝ} (hc : 2 ≤ c) (L : ℝ) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ δ0 → ∀ I I0 : ℂ,
      Tendsto (fun T : ℝ => ∫ τ in (0 : ℝ)..T,
        outerAmp ε c τ * CtOsc.gcut δ τ * Complex.exp (Complex.I * c * (CtSd.phaseL L τ : ℂ))) atTop (𝓝 I) →
      Tendsto (fun T : ℝ => ∫ τ in (0 : ℝ)..T,
        outerAmp ε c τ * CtOsc.gcut 0 τ * Complex.exp (Complex.I * c * (CtSd.phaseL L τ : ℂ))) atTop (𝓝 I0) →
      ‖I - I0‖ ≤ ε' := by
  obtain ⟨C0, hC0, hMd⟩ := mdata_hankel
  obtain ⟨CA, hCA, H⟩ := outerAmp_ampBd (ε := ε) (by rcases hε with h | h <;> simp [h])
  obtain ⟨CA1, hCA1, H1⟩ := outer_amp_data hε
  obtain ⟨-, hbd⟩ := H1 hc
  obtain ⟨A1, A2, hA⟩ := H c hc
  have hc0 : 0 < c := by linarith
  have hmc : ∀ τ : ℝ, 0 < τ → 0 ≤ hankelEdgeM τ := fun τ hτ => (hankelEdgeM_pos hτ).le
  have hroot : 0 < L → ∃ τ0 : ℝ, 0 < τ0 ∧ hankelEdgeM τ0 = L := fun hL => by
    obtain ⟨τ, hτ0, hτ⟩ := hankelEdgeM_exists_root hL.le
    refine ⟨τ, ?_, hτ⟩
    rcases hτ0.lt_or_eq with h | h
    · exact h
    · rw [← h, hankelEdgeM_zero] at hτ; linarith
  obtain ⟨a0, ha0, hp⟩ := hp_eventually hMd hmc hroot
  set CA' : ℝ := CA * (1 + 2 * 4 + 36) with hCA'
  set Kt : ℝ := 5 * CA' + 25 * (CA' * (1 + 4 * C0)) + 64 * CA' * (1 + 16 * C0 + 48 * C0 ^ 2) with hKt
  have hCA'0 : 0 ≤ CA' := by rw [hCA']; positivity
  have hKt0 : 0 ≤ Kt := by rw [hKt]; positivity
  set a : ℝ := max a0 ((4 * Kt / ε') ^ 2) with hadef
  have ha2 : 2 ≤ a := ha0.trans (le_max_left _ _)
  have ha0' : 0 < a := by linarith
  have hsqa : 4 * Kt / ε' ≤ Real.sqrt a := by
    have : (4 * Kt / ε') ^ 2 ≤ a := le_max_right _ _
    calc 4 * Kt / ε' = Real.sqrt ((4 * Kt / ε') ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt a := Real.sqrt_le_sqrt this
  have hsa0 : 0 < Real.sqrt a := Real.sqrt_pos.2 ha0'
  have hKtsa : Kt / Real.sqrt a + Kt / Real.sqrt a ≤ ε' / 2 := by
    have h1 : 4 * Kt ≤ ε' * Real.sqrt a := by
      rw [div_le_iff₀ hε'] at hsqa; linarith
    rw [← two_mul, ← mul_div_assoc, div_le_iff₀ hsa0]
    linarith
  have hq : 0 < a ^ 2 + a := by positivity
  refine ⟨min (1 / (a ^ 2 + a)) (ε' / (4 * a * CA1 * (a ^ 2 + a) + 1)), by positivity, fun δ hδ hδ0 I I0 hI hI0 => ?_⟩
  have hδa : δ * (a ^ 2 + a) ≤ 1 := by
    have : δ ≤ 1 / (a ^ 2 + a) := hδ0.trans (min_le_left _ _)
    rw [le_div_iff₀ hq] at this
    exact this
  have hδ1 : δ ≤ 1 := by
    have : δ ≤ 1 / (a ^ 2 + a) := hδ0.trans (min_le_left _ _)
    refine this.trans ?_
    rw [div_le_one hq]; nlinarith
  have hδe : δ * (4 * a * CA1 * (a ^ 2 + a) + 1) ≤ ε' := by
    have : δ ≤ ε' / (4 * a * CA1 * (a ^ 2 + a) + 1) := hδ0.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    exact this
  have hϕ : ∀ τ : ℝ, 0 < τ → HasDerivAt (CtSd.phaseL L) (hankelEdgeM τ - L) τ := fun τ hτ => CtSd.phaseL_deriv L hτ
  have hϕc : ContinuousOn (CtSd.phaseL L) (Ioi 0) := fun τ hτ => (hϕ τ hτ).continuousAt.continuousWithinAt
  have hAδ := gcut_ampBd hA hδ hδ1
  have hA0 := gcut_ampBd hA (le_refl (0 : ℝ)) zero_le_one
  have hintδ : ∀ b : ℝ, 0 ≤ b → IntervalIntegrable (fun τ => outerAmp ε c τ * CtOsc.gcut δ τ *
      Complex.exp (Complex.I * c * (CtSd.phaseL L τ : ℂ))) volume 0 b := fun b hb =>
    intInt_BE hb hAδ.CA0 (fun τ hτ => (hAδ.d1 τ hτ).continuousAt.continuousWithinAt) hϕc hAδ.b0
  have hint0 : ∀ b : ℝ, 0 ≤ b → IntervalIntegrable (fun τ => outerAmp ε c τ * CtOsc.gcut 0 τ *
      Complex.exp (Complex.I * c * (CtSd.phaseL L τ : ℂ))) volume 0 b := fun b hb =>
    intInt_BE hb hA0.CA0 (fun τ hτ => (hA0.d1 τ hτ).continuousAt.continuousWithinAt) hϕc hA0.b0
  obtain ⟨Vδ, hVδ, hVδb⟩ := tail_small (c := c) (A := fun τ => outerAmp ε c τ * CtOsc.gcut δ τ) hMd hAδ (by linarith) ha2 hϕ
    (fun τ hτ => hp τ ((le_max_left _ _).trans hτ))
  obtain ⟨V0, hV0, hV0b⟩ := tail_small (c := c) (A := fun τ => outerAmp ε c τ * CtOsc.gcut 0 τ) hMd hA0 (by linarith) ha2 hϕ
    (fun τ hτ => hp τ ((le_max_left _ _).trans hτ))
  have eI := improper_split ha0'.le hintδ hI hVδ
  have eI0 := improper_split ha0'.le hint0 hI0 hV0
  set Sδ : ℂ := ∫ τ in (0 : ℝ)..a, outerAmp ε c τ * CtOsc.gcut δ τ *
    Complex.exp (Complex.I * c * (CtSd.phaseL L τ : ℂ)) with hSδ
  set S0 : ℂ := ∫ τ in (0 : ℝ)..a, outerAmp ε c τ * CtOsc.gcut 0 τ *
    Complex.exp (Complex.I * c * (CtSd.phaseL L τ : ℂ)) with hS0
  have hdiff : ‖Sδ - S0‖ ≤ CA1 * (2 * (δ * (a ^ 2 + a))) * a := by
    rw [hSδ, hS0, ← intervalIntegral.integral_sub (hintδ a ha0'.le) (hint0 a ha0'.le)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := a)
      (C := CA1 * (2 * (δ * (a ^ 2 + a))))
      (f := fun τ => outerAmp ε c τ * CtOsc.gcut δ τ * Complex.exp (Complex.I * c * (CtSd.phaseL L τ : ℂ)) -
        outerAmp ε c τ * CtOsc.gcut 0 τ * Complex.exp (Complex.I * c * (CtSd.phaseL L τ : ℂ))) (fun τ hτ => by
        rw [Set.uIoc_of_le ha0'.le] at hτ
        have hτ0 : 0 < τ := hτ.1
        rw [← sub_mul, ← mul_sub]
        rw [norm_mul]
        have hex : ‖Complex.exp (Complex.I * c * (CtSd.phaseL L τ : ℂ))‖ = 1 := by
          rw [show Complex.I * (c : ℂ) * (CtSd.phaseL L τ : ℂ) = ((c * CtSd.phaseL L τ : ℝ) : ℂ) * Complex.I by
            push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I _
        rw [hex, mul_one, norm_mul]
        have h0 : CtOsc.gcut 0 τ = 1 := by simp [CtOsc.gcut]
        rw [h0]
        exact mul_le_mul (hbd τ hτ0) (norm_gcut_sub_one hδ hτ0.le hτ.2 hδa) (norm_nonneg _) hCA1)
    rw [sub_zero, abs_of_nonneg ha0'.le] at this
    exact this
  have hfin : CA1 * (2 * (δ * (a ^ 2 + a))) * a ≤ ε' / 2 := by
    have h1 : 0 ≤ CA1 * a * (a ^ 2 + a) := by positivity
    nlinarith [mul_nonneg hδ h1, hδe]
  rw [← hCA', ← hKt] at hVδb hV0b
  rw [eI, eI0]
  calc ‖(Sδ + Vδ) - (S0 + V0)‖ = ‖(Sδ - S0) + (Vδ - V0)‖ := by congr 1; ring
    _ ≤ ‖Sδ - S0‖ + ‖Vδ - V0‖ := norm_add_le _ _
    _ ≤ ‖Sδ - S0‖ + (‖Vδ‖ + ‖V0‖) := add_le_add le_rfl (norm_sub_le _ _)
    _ ≤ ε' := by linarith only [hdiff, hfin, hVδb, hV0b, hKtsa]

/-- The improper integral `∫_0^∞ A_ε(τ) e^{-icΦ_Ph(τ;ξ)} dτ` of `(ct:Keps)` (a limit; a junk value if it does not converge). -/
noncomputable def dualI (ε c ξ : ℝ) : ℂ :=
  limUnder atTop (fun T : ℝ => ∫ τ in (0 : ℝ)..T, outerAmp ε c τ * dualP c ξ τ)

/-- `K_ε(ξ; c) = -√(πc/12) Re ∫_0^∞ G_ε(iτ)(1-iτ)^{1/2} e^{-B_c(iτ)} e^{-icΦ_Ph(τ;ξ)} dτ` (`ct:Keps`). -/
noncomputable def dualK (ε c ξ : ℝ) : ℝ := -Real.sqrt (Real.pi * c / 12) * (dualI ε c ξ).re

/-- For `δ > 0`, `ξ > 0`: the Lebesgue integral `J_δ(ξ)` is the improper limit. -/
lemma Jd_tendsto {c ε : ℝ} (hc : 2 ≤ c) (hε : ε = 1 ∨ ε = -1) {δ : ℝ} (hδ : 0 < δ) {ξ : ℝ} (hξ : 0 < ξ) :
    Tendsto (fun T : ℝ => ∫ τ in (0 : ℝ)..T, outerAmp ε c τ * CtOsc.gcut δ τ *
      Complex.exp (Complex.I * c * (CtSd.phaseL (Real.log (Real.pi ^ 2 * ξ)) τ : ℂ))) atTop
      (𝓝 (Jd c ε δ ξ)) := by
  obtain ⟨CA, hCA0, hCA⟩ := outer_amp_data hε
  obtain ⟨hcont, hbd⟩ := hCA hc
  have hG : IntegrableOn (fun τ => outerAmp ε c τ * CtOsc.gcut δ τ * dualP c ξ τ) (Ioi (0 : ℝ)) := by
    refine Integrable.mono' (integrable_gauss_Ioi CA hδ) ?_ ?_
    · have h1 : ContinuousOn (fun τ : ℝ => dualP c ξ τ) (Ioi (0 : ℝ)) :=
        (continuousOn_dualP c).comp (by fun_prop : ContinuousOn (fun τ : ℝ => (τ, ξ)) (Ioi (0 : ℝ)))
          (fun τ hτ => ⟨hτ, hξ⟩)
      exact ((hcont.mul (continuous_gcut δ).continuousOn).mul h1).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun τ hτ => ?_)
      simp only [norm_mul, norm_dualP, mul_one, CtOsc.norm_gcut]
      exact mul_le_mul_of_nonneg_right (hbd τ hτ) (Real.exp_pos _).le
  have := intervalIntegral_tendsto_integral_Ioi 0 hG tendsto_id
  refine this.congr (fun T => ?_)
  refine intervalIntegral.integral_congr (fun τ _ => ?_)
  simp only [dualP_eq]

lemma gcut_zero (τ : ℝ) : CtOsc.gcut 0 τ = 1 := by simp [CtOsc.gcut]

/-- **`ct:dual-id` (2).**  For `ε = ±1` there is `K_b` (independent of `ξ`, `c`) such that for every `c ≥ 2`:
the improper integral `∫_0^∞ A_ε e^{-icΦ_Ph(τ;ξ)} dτ` of `(ct:Keps)` converges for every `ξ > 0`, `|K_ε(ξ;c)| ≤ K_b`
(in particular `≤ K_b √c`), and for every `f ∈ 𝒜_c^ε` the exact Cauchy duality `∫_0^∞ K_ε(ξ;c) dm(ξ) = 0` holds,
`dm = c (fρ₀)(cξ) dξ`. -/
theorem ct_dual_id_part2 {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ {c : ℝ}, 2 ≤ c →
      (∀ ξ : ℝ, 0 < ξ → Tendsto (fun T : ℝ => ∫ τ in (0 : ℝ)..T, outerAmp ε c τ * dualP c ξ τ) atTop
          (𝓝 (dualI ε c ξ)) ∧ |dualK ε c ξ| ≤ Kb) ∧
      ∀ {f : ℝ → ℝ}, IsHankelEigenfn c ε f → ∫ ξ in Ioi (0 : ℝ), dualK ε c ξ * hankelDmDens c f ξ = 0 := by
  obtain ⟨Kb0, hKb0, HU⟩ := unif_data hε
  have hpi := Real.pi_pos
  refine ⟨Real.sqrt (Real.pi / 12) * Kb0, by positivity, fun {c} hc => ?_⟩
  have hc0 : 0 < c := by linarith
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc0
  -- the `δ = 0` data
  have h0 : ∀ ξ : ℝ, ∃ I : ℂ, Tendsto (fun T : ℝ => ∫ τ in (0 : ℝ)..T, outerAmp ε c τ * dualP c ξ τ) atTop (𝓝 I) ∧
      Real.sqrt c * ‖I‖ ≤ Kb0 := fun ξ => by
    obtain ⟨I, hI, hb⟩ := HU hc (Real.log (Real.pi ^ 2 * ξ)) 0 le_rfl zero_le_one
    refine ⟨I, hI.congr (fun T => ?_), hb⟩
    refine intervalIntegral.integral_congr (fun τ _ => ?_)
    simp only [gcut_zero, mul_one, dualP_eq]
  have h1 : ∀ ξ : ℝ, Tendsto (fun T : ℝ => ∫ τ in (0 : ℝ)..T, outerAmp ε c τ * dualP c ξ τ) atTop
      (𝓝 (dualI ε c ξ)) ∧ Real.sqrt c * ‖dualI ε c ξ‖ ≤ Kb0 := fun ξ => by
    obtain ⟨I, hI, hb⟩ := h0 ξ
    have e : dualI ε c ξ = I := hI.limUnder_eq
    rw [e]
    exact ⟨hI, hb⟩
  have hI0 := fun ξ => (h1 ξ).1
  have hbound0 := fun ξ => (h1 ξ).2
  have hK : ∀ ξ : ℝ, |dualK ε c ξ| ≤ Real.sqrt (Real.pi / 12) * Kb0 := fun ξ => by
    unfold dualK
    have e : Real.sqrt (Real.pi * c / 12) = Real.sqrt (Real.pi / 12) * Real.sqrt c := by
      rw [show Real.pi * c / 12 = Real.pi / 12 * c by ring, Real.sqrt_mul (by positivity)]
    rw [abs_mul, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _), e]
    have h1 : |(dualI ε c ξ).re| ≤ ‖dualI ε c ξ‖ := Complex.abs_re_le_norm _
    calc Real.sqrt (Real.pi / 12) * Real.sqrt c * |(dualI ε c ξ).re| =
        Real.sqrt (Real.pi / 12) * (Real.sqrt c * |(dualI ε c ξ).re|) := by ring
      _ ≤ Real.sqrt (Real.pi / 12) * Kb0 := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact (mul_le_mul_of_nonneg_left h1 hsc.le).trans (hbound0 ξ)
  refine ⟨fun ξ _ => ⟨hI0 ξ, hK ξ⟩, fun {f} hf => ?_⟩
  -- the identity, by dominated convergence as `δ ↓ 0`
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set g0 : ℝ → ℝ := hankelDmDens c f with hg0
  set F : ℝ → ℝ → ℝ := fun δ ξ => (((g0 ξ : ℝ) : ℂ) * Jd c ε δ ξ).re with hF
  have hJb : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ξ : ℝ, 0 < ξ → Real.sqrt c * ‖Jd c ε δ ξ‖ ≤ Kb0 := by
    intro δ hδ hδ1 ξ hξ
    obtain ⟨I, hI, hb⟩ := HU hc (Real.log (Real.pi ^ 2 * ξ)) δ hδ.le hδ1
    have := tendsto_nhds_unique hI (Jd_tendsto hc hε hδ hξ)
    rw [← this]; exact hb
  have hl : (𝓝[>] (0 : ℝ)).NeBot := inferInstance
  have hmeas : ∀ᶠ δ in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (F δ) μ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact ((dual_fubini hc hf hε hδ).1.re).aestronglyMeasurable
  have hbdd : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᵐ ξ ∂μ, ‖F δ ξ‖ ≤ ‖g0 ξ‖ * (Kb0 / Real.sqrt c) := by
    filter_upwards [self_mem_nhdsWithin, Ioc_mem_nhdsGT zero_lt_one] with δ hδ hδ1
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ξ hξ => ?_)
    simp only [hF]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_real]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [le_div_iff₀ hsc, mul_comm]
    exact hJb δ hδ hδ1.2 ξ hξ
  have hint : Integrable (fun ξ => ‖g0 ξ‖ * (Kb0 / Real.sqrt c)) μ := by
    have := (hankelDmDens_integrableOn hc0 hf).norm
    exact this.mul_const _
  have hlim : ∀ᵐ ξ ∂μ, Tendsto (fun δ => F δ ξ) (𝓝[>] (0 : ℝ)) (𝓝 (g0 ξ * (dualI ε c ξ).re)) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ξ hξ => ?_)
    have hJ : Tendsto (fun δ => Jd c ε δ ξ) (𝓝[>] (0 : ℝ)) (𝓝 (dualI ε c ξ)) := by
      rw [Metric.tendsto_nhdsWithin_nhds]
      intro e he
      obtain ⟨δ0, hδ0, H⟩ := delta_conv hε hc (Real.log (Real.pi ^ 2 * ξ)) (half_pos he)
      refine ⟨δ0, hδ0, fun δ hδ hdist => ?_⟩
      have hδp : 0 < δ := hδ
      have hδle : δ ≤ δ0 := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hδp] at hdist; exact hdist.le
      have := H δ hδp.le hδle (Jd c ε δ ξ) (dualI ε c ξ) (Jd_tendsto hc hε hδp hξ) (by
        refine (hI0 ξ).congr (fun T => ?_)
        refine intervalIntegral.integral_congr (fun τ _ => ?_)
        simp only [gcut_zero, mul_one, dualP_eq])
      rw [dist_eq_norm]
      linarith [half_lt_self he]
    have h2 := (Complex.continuous_re.tendsto _).comp (hJ.const_mul ((g0 ξ : ℝ) : ℂ))
    have h3 : Complex.re (((g0 ξ : ℝ) : ℂ) * dualI ε c ξ) = g0 ξ * (dualI ε c ξ).re := by
      simp [Complex.mul_re]
    rw [h3] at h2
    exact h2
  have hdct := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[>] (0 : ℝ))
    (F := F) (f := fun ξ => g0 ξ * (dualI ε c ξ).re) _ hmeas hbdd hint hlim
  have hzero : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∫ ξ, F δ ξ ∂μ = 0 := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    obtain ⟨hi, hz⟩ := dual_fubini hc hf hε hδ
    have := integral_re hi
    simp only [RCLike.re_to_complex] at this
    simp only [hF]
    rw [this]
    exact hz
  have hL : ∫ ξ, g0 ξ * (dualI ε c ξ).re ∂μ = 0 :=
    tendsto_nhds_unique hdct (tendsto_const_nhds.congr' (hzero.mono fun δ h => h.symm))
  have : ∀ ξ : ℝ, dualK ε c ξ * hankelDmDens c f ξ = (-Real.sqrt (Real.pi * c / 12)) * (g0 ξ * (dualI ε c ξ).re) := by
    intro ξ
    unfold dualK
    ring
  calc _ = ∫ ξ, (-Real.sqrt (Real.pi * c / 12)) * (g0 ξ * (dualI ε c ξ).re) ∂μ :=
        integral_congr_ae (Eventually.of_forall this)
    _ = (-Real.sqrt (Real.pi * c / 12)) * ∫ ξ, g0 ξ * (dualI ε c ξ).re ∂μ := integral_const_mul _ _
    _ = 0 := by rw [hL, mul_zero]

/-- info: 'FormalResearch.SignUncertainty.CtDual.delta_conv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms delta_conv

/-- info: 'FormalResearch.SignUncertainty.CtDual.ct_dual_id_part2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_dual_id_part2

end FormalResearch.SignUncertainty.CtDual
