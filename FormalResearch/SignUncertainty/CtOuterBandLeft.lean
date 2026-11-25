module

public import FormalResearch.SignUncertainty.CtOuterBandTail

/-!
# The left non-stationary piece (Piece 2)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 4, Piece 2 (`χ_0`: the trivial bound on
`[0, τ_s]` and two integrations by parts on `[τ_s, ·]`).  **Proved.**
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped Real Interval

namespace FormalResearch.SignUncertainty.CtOsc

lemma intervalIntegrable_of_rpow_bound {f : ℝ → ℂ} {T K : ℝ} (hT : 0 ≤ T) (hc : ContinuousOn f (Ioc 0 T))
    (hb : ∀ τ ∈ Ioc 0 T, ‖f τ‖ ≤ K * τ ^ (1 / 2 : ℝ)) : IntervalIntegrable f volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  have hg : IntegrableOn (fun τ : ℝ => K * τ ^ (1 / 2 : ℝ)) (Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1
      ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T) (r := 1 / 2) (by norm_num)).const_mul K)
  exact Integrable.mono' hg (hc.aestronglyMeasurable measurableSet_Ioc)
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hb))

section
variable {C0 : ℝ} {m m1 m2 m3 : ℝ → ℝ}

/-- **Piece 2.** The left piece `∫_0^{τ_e} B e^{iλϕ}` for `B` vanishing (with `B'`) at `τ_e`, `|m - L| ≥ p₀` on
`[τ_s, τ_e]`, `γσ ≤ p₀`. -/
theorem piece2 (hM : MData C0 m m1 m2 m3) {γ KB lam L τs τe p0 : ℝ} (hγ : 0 < γ) (hKB : 0 ≤ KB) (hlam : 0 < lam)
    (hs : 0 < τs) (hse : τs ≤ τe) (hp0 : 0 < p0)
    {ϕ : ℝ → ℝ} (hϕ : ∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - L) τ)
    {B B1 B2 : ℝ → ℂ} (hB : ∀ τ : ℝ, 0 < τ → HasDerivAt B (B1 τ) τ)
    (hB1 : ∀ τ : ℝ, 0 < τ → HasDerivAt B1 (B2 τ) τ) (hc2 : ContinuousOn B2 (Ioi 0))
    (hbB : ∀ τ : ℝ, 0 < τ → ‖B τ‖ ≤ KB * τ ^ (1 / 2 : ℝ) / (1 + τ))
    (hbB1 : ∀ τ : ℝ, 0 < τ → ‖B1 τ‖ ≤ KB * τ ^ (-1 / 2 : ℝ) / (1 + τ))
    (hbB2 : ∀ τ : ℝ, 0 < τ → ‖B2 τ‖ ≤ KB * τ ^ (-3 / 2 : ℝ) / (1 + τ))
    (hBe : B τe = 0) (hB1e : B1 τe = 0)
    (hp : ∀ τ ∈ Icc τs τe, p0 ≤ |m τ - L| ∧ γ * sg τ ≤ p0) :
    ‖∫ τ in (0 : ℝ)..τe, B τ * Complex.exp (Complex.I * lam * (ϕ τ : ℂ))‖ ≤
      (2 / 3) * KB * τs ^ (3 / 2 : ℝ) + KB * τs ^ (1 / 2 : ℝ) / (p0 * lam) +
        KB * (1 + C0 / γ + 2 * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2)) * τs ^ (-1 / 2 : ℝ) / (p0 ^ 2 * lam ^ 2) := by
  have hC0 := hM.C0nn
  set f : ℝ → ℂ := fun τ => B τ * Complex.exp (Complex.I * lam * (ϕ τ : ℂ)) with hf
  have hcf : ContinuousOn f (Ioi 0) := by
    refine ContinuousOn.mul (fun τ hτ => (hB τ hτ).continuousAt.continuousWithinAt) ?_
    refine Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul ?_)
    exact Complex.continuous_ofReal.comp_continuousOn (fun τ hτ => (hϕ τ hτ).continuousAt.continuousWithinAt)
  have hbf : ∀ τ : ℝ, 0 < τ → ‖f τ‖ ≤ KB * τ ^ (1 / 2 : ℝ) := by
    intro τ hτ
    rw [hf, norm_mul]
    simp only [norm_cexp_phase, mul_one]
    refine (hbB τ hτ).trans ?_
    have : KB * τ ^ (1 / 2 : ℝ) / (1 + τ) ≤ KB * τ ^ (1 / 2 : ℝ) :=
      div_le_self (by positivity) (by linarith)
    exact this
  have hint1 : IntervalIntegrable f volume 0 τs :=
    intervalIntegrable_of_rpow_bound hs.le (hcf.mono Ioc_subset_Ioi_self) (fun τ hτ => hbf τ hτ.1)
  have hint2 : IntervalIntegrable f volume τs τe :=
    (hcf.mono (fun τ (hτ : τ ∈ Icc τs τe) => (lt_of_lt_of_le hs hτ.1 : τ ∈ Ioi (0 : ℝ)))).intervalIntegrable_of_Icc hse
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  rw [add_assoc]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · -- trivial bound on [0, τs]
    have h1 := intervalIntegral.norm_integral_le_of_norm_le hs.le
      (Eventually.of_forall fun τ (hτ : τ ∈ Ioc 0 τs) => hbf τ hτ.1)
      ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := τs) (r := 1 / 2) (by norm_num)).const_mul KB)
    refine h1.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
    have e : (1 / 2 : ℝ) + 1 = 3 / 2 := by norm_num
    rw [e, Real.zero_rpow (by norm_num)]
    ring
  · have hpos : ∀ τ ∈ Icc τs τe, 0 < τ := fun τ hτ => lt_of_lt_of_le hs hτ.1
    have hR := region_bound hM hγ hKB hlam hs hse (L := L) hϕ (B := B) (B1 := B1) (B2 := B2)
      (fun τ hτ => hB τ (hpos τ hτ)) (fun τ hτ => hB1 τ (hpos τ hτ)) (hc2.mono fun τ hτ => hpos τ hτ)
      (fun τ hτ => hbB τ (hpos τ hτ)) (fun τ hτ => hbB1 τ (hpos τ hτ)) (fun τ hτ => hbB2 τ (hpos τ hτ))
      (p := fun _ => p0) continuousOn_const (fun τ hτ => ⟨hp0, (hp τ hτ).1, (hp τ hτ).2⟩)
    refine hR.trans ?_
    set K0 := 1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2 with hK0
    have hK0nn : 0 ≤ K0 := by positivity
    have hss : τs ∈ Icc τs τe := ⟨le_rfl, hse⟩
    have hpa := hp τs hss
    have hBs : ‖B τs‖ / |m τs - L| ≤ KB * τs ^ (1 / 2 : ℝ) / p0 := by
      have h1 : ‖B τs‖ ≤ KB * τs ^ (1 / 2 : ℝ) :=
        (hbB τs hs).trans (div_le_self (by positivity) (by linarith))
      exact div_le_div₀ (by positivity) h1 hp0 hpa.1
    have hHe : ibpH B B1 (fun τ => m τ - L) m1 τe = 0 := by unfold ibpH; simp [hBe, hB1e]
    have hHs : ‖ibpH B B1 (fun τ => m τ - L) m1 τs‖ / |m τs - L| ≤ KB * (1 + C0 / γ) * τs ^ (-1 / 2 : ℝ) / p0 ^ 2 := by
      have h1 := H_pt (τ := τs) (p := p0) (γ := γ) (C0 := C0) (KB := KB) hs hp0 hγ hC0 hKB hpa.2
        (ϕ1 := fun τ => m τ - L) (ϕ2 := m1) (B := B) (B1 := B1) hpa.1 (hM.abs_m1 hs) (hbB τs hs) (hbB1 τs hs)
      have hw : τs ^ (-1 / 2 : ℝ) / (1 + τs) ≤ τs ^ (-1 / 2 : ℝ) := div_le_self (by positivity) (by linarith)
      have h2 : ‖ibpH B B1 (fun τ => m τ - L) m1 τs‖ ≤ KB * (1 + C0 / γ) * τs ^ (-1 / 2 : ℝ) / p0 := by
        refine h1.trans ?_
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by positivity)) hp0.le
      calc ‖ibpH B B1 (fun τ => m τ - L) m1 τs‖ / |m τs - L| ≤ KB * (1 + C0 / γ) * τs ^ (-1 / 2 : ℝ) / p0 / p0 :=
            div_le_div₀ (by positivity) h2 hp0 hpa.1
        _ = _ := by field_simp
    have hQ : ∫ τ in τs..τe, KB * K0 * wt τ / p0 ^ 2 ≤ 2 * KB * K0 * τs ^ (-1 / 2 : ℝ) / p0 ^ 2 := by
      have hcont1 : ContinuousOn (fun τ : ℝ => KB * K0 * wt τ / p0 ^ 2) (Icc τs τe) :=
        ((continuousOn_const.mul (continuousOn_wt hs)).div_const _)
      have hcont2 : ContinuousOn (fun τ : ℝ => KB * K0 / p0 ^ 2 * τ ^ (-3 / 2 : ℝ)) (Icc τs τe) :=
        continuousOn_const.mul (fun τ hτ => (Real.continuousAt_rpow_const _ _ (Or.inl (hpos τ hτ).ne')).continuousWithinAt)
      have h1 : ∫ τ in τs..τe, KB * K0 * wt τ / p0 ^ 2 ≤ ∫ τ in τs..τe, KB * K0 / p0 ^ 2 * τ ^ (-3 / 2 : ℝ) := by
        refine intervalIntegral.integral_mono_on hse (hcont1.intervalIntegrable_of_Icc hse)
          (hcont2.intervalIntegrable_of_Icc hse) fun τ hτ => ?_
        have hτ0 := hpos τ hτ
        have hw : wt τ ≤ τ ^ (-3 / 2 : ℝ) := div_le_self (by positivity) (by linarith)
        calc KB * K0 * wt τ / p0 ^ 2 = KB * K0 / p0 ^ 2 * wt τ := by ring
          _ ≤ KB * K0 / p0 ^ 2 * τ ^ (-3 / 2 : ℝ) := mul_le_mul_of_nonneg_left hw (by positivity)
      have h2 : ∫ τ in τs..τe, τ ^ (-3 / 2 : ℝ) ≤ 2 * τs ^ (-1 / 2 : ℝ) := by
        rw [integral_rpow (Or.inr ⟨by norm_num, by
          rw [uIcc_of_le hse]; exact fun h => absurd h.1 (not_le.mpr hs)⟩)]
        have e : (-3 / 2 : ℝ) + 1 = -1 / 2 := by norm_num
        rw [e]
        have : 0 ≤ τe ^ (-1 / 2 : ℝ) := by
          have : 0 < τe := lt_of_lt_of_le hs hse
          positivity
        have : (τe ^ (-1 / 2 : ℝ) - τs ^ (-1 / 2 : ℝ)) / (-1 / 2) = 2 * (τs ^ (-1 / 2 : ℝ) - τe ^ (-1 / 2 : ℝ)) := by
          field_simp; ring
        rw [this]; linarith
      refine h1.trans ?_
      rw [intervalIntegral.integral_const_mul]
      calc KB * K0 / p0 ^ 2 * ∫ τ in τs..τe, τ ^ (-3 / 2 : ℝ) ≤ KB * K0 / p0 ^ 2 * (2 * τs ^ (-1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by ring
    have hl2 : 0 < lam ^ 2 := by positivity
    have e1 : ‖B τe‖ = 0 := by rw [hBe, norm_zero]
    simp only [e1, hHe, norm_zero, zero_div, zero_add]
    have a1 : ‖B τs‖ / |m τs - L| / lam ≤ KB * τs ^ (1 / 2 : ℝ) / p0 / lam :=
      div_le_div_of_nonneg_right hBs hlam.le
    have a2 : ‖ibpH B B1 (fun τ => m τ - L) m1 τs‖ / |m τs - L| / lam ^ 2 ≤
        KB * (1 + C0 / γ) * τs ^ (-1 / 2 : ℝ) / p0 ^ 2 / lam ^ 2 := div_le_div_of_nonneg_right hHs hl2.le
    have a3 : (∫ τ in τs..τe, KB * K0 * wt τ / p0 ^ 2) / lam ^ 2 ≤ 2 * KB * K0 * τs ^ (-1 / 2 : ℝ) / p0 ^ 2 / lam ^ 2 :=
      div_le_div_of_nonneg_right hQ hl2.le
    have e2 : KB * τs ^ (1 / 2 : ℝ) / p0 / lam = KB * τs ^ (1 / 2 : ℝ) / (p0 * lam) := by field_simp
    have e3 : KB * (1 + C0 / γ) * τs ^ (-1 / 2 : ℝ) / p0 ^ 2 / lam ^ 2 +
        2 * KB * K0 * τs ^ (-1 / 2 : ℝ) / p0 ^ 2 / lam ^ 2 =
        KB * (1 + C0 / γ + 2 * K0) * τs ^ (-1 / 2 : ℝ) / (p0 ^ 2 * lam ^ 2) := by field_simp
    show _ ≤ KB * τs ^ (1 / 2 : ℝ) / (p0 * lam) + KB * (1 + C0 / γ + 2 * K0) * τs ^ (-1 / 2 : ℝ) / (p0 ^ 2 * lam ^ 2)
    rw [← e2, ← e3]
    linarith

end

end FormalResearch.SignUncertainty.CtOsc
