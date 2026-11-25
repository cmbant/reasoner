module

public import FormalResearch.SignUncertainty.CtOuterBandPt
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Region bound for the non-stationary pieces (outer band)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 4, Pieces 2 and 3.  **Proved.**

`MData C₀ m m₁ m₂ m₃`: the dispersion `m` with `τ/(1+τ²) ≤ m' ≤ C₀ τ/(1+τ²)`, `|m''| ≤ C₀/(1+τ)²`, `|m'''| ≤ C₀/(1+τ)³`.
`region_bound`: double integration by parts of `∫_a^b B e^{iλϕ}` with `ϕ' = m - L`, in terms of the pointwise lower
bound `p ≤ |m - L|`, `γ σ ≤ p`.
-/

@[expose] public section

open Set MeasureTheory
open scoped Real Interval

namespace FormalResearch.SignUncertainty.CtOsc

/-- Data on the dispersion `m` (with `m₁ = m'`, `m₂ = m''`, `m₃ = m'''`). -/
structure MData (C0 : ℝ) (m m1 m2 m3 : ℝ → ℝ) : Prop where
  C0nn : 0 ≤ C0
  d0 : ∀ τ : ℝ, 0 < τ → HasDerivAt m (m1 τ) τ
  d1 : ∀ τ : ℝ, 0 < τ → HasDerivAt m1 (m2 τ) τ
  d2 : ∀ τ : ℝ, 0 < τ → HasDerivAt m2 (m3 τ) τ
  c3 : ContinuousOn m3 (Ioi 0)
  lo : ∀ τ : ℝ, 0 < τ → τ / (1 + τ ^ 2) ≤ m1 τ
  hi : ∀ τ : ℝ, 0 < τ → m1 τ ≤ C0 * (τ / (1 + τ ^ 2))
  b2 : ∀ τ : ℝ, 0 < τ → |m2 τ| ≤ C0 / (1 + τ) ^ 2
  b3 : ∀ τ : ℝ, 0 < τ → |m3 τ| ≤ C0 / (1 + τ) ^ 3

section
variable {C0 : ℝ} {m m1 m2 m3 : ℝ → ℝ}

lemma sg_div (τ : ℝ) (hτ : 0 < τ) : sg τ / τ = τ / (1 + τ ^ 2) := by
  unfold sg; field_simp

lemma MData.m1_pos (h : MData C0 m m1 m2 m3) {τ : ℝ} (hτ : 0 < τ) : 0 < m1 τ :=
  lt_of_lt_of_le (by positivity) (h.lo τ hτ)

lemma MData.abs_m1 (h : MData C0 m m1 m2 m3) {τ : ℝ} (hτ : 0 < τ) : |m1 τ| ≤ C0 * (sg τ / τ) := by
  rw [abs_of_pos (h.m1_pos hτ), sg_div τ hτ]; exact h.hi τ hτ

lemma MData.cont_m (h : MData C0 m m1 m2 m3) : ContinuousOn m (Ioi 0) :=
  fun τ hτ => (h.d0 τ hτ).continuousAt.continuousWithinAt

lemma MData.cont_m1 (h : MData C0 m m1 m2 m3) : ContinuousOn m1 (Ioi 0) :=
  fun τ hτ => (h.d1 τ hτ).continuousAt.continuousWithinAt

lemma MData.cont_m2 (h : MData C0 m m1 m2 m3) : ContinuousOn m2 (Ioi 0) :=
  fun τ hτ => (h.d2 τ hτ).continuousAt.continuousWithinAt

/-- `m` is strictly increasing on `(0,∞)`. -/
lemma MData.strictMonoOn (h : MData C0 m m1 m2 m3) : StrictMonoOn m (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) h.cont_m ?_
  intro τ hτ
  rw [interior_Ioi] at hτ
  rw [(h.d0 τ hτ).deriv]; exact h.m1_pos hτ

/-- `m(τ) - m(κτ) ≥ κ(1-κ) σ(τ)`. -/
lemma MData.step (h : MData C0 m m1 m2 m3) {κ τ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hτ : 0 < τ) :
    κ * (1 - κ) * sg τ ≤ m τ - m (κ * τ) := by
  have hlt : κ * τ < τ := by nlinarith
  have hpos : 0 < κ * τ := by positivity
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope m m1 hlt
    (fun x hx => (h.d0 x (lt_of_lt_of_le hpos hx.1)).continuousAt.continuousWithinAt)
    (fun x hx => h.d0 x (lt_trans hpos hx.1))
  have hξ0 : 0 < ξ := lt_trans hpos hξ.1
  have h1 : κ * τ / (1 + τ ^ 2) ≤ m1 ξ := by
    refine le_trans ?_ (h.lo ξ hξ0)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : ξ ^ 2 ≤ τ ^ 2 := by nlinarith [hξ.1, hξ.2]
    nlinarith [hξ.1, hξ0.le, mul_nonneg hκ0.le hτ.le]
  have hd : 0 < τ - κ * τ := by nlinarith
  have : m τ - m (κ * τ) = m1 ξ * (τ - κ * τ) := by
    rw [hξe]; field_simp
  rw [this]
  unfold sg
  calc κ * (1 - κ) * (τ ^ 2 / (1 + τ ^ 2)) = κ * τ / (1 + τ ^ 2) * (τ - κ * τ) := by field_simp
    _ ≤ m1 ξ * (τ - κ * τ) := mul_le_mul_of_nonneg_right h1 hd.le

lemma continuousOn_wt {a b : ℝ} (ha : 0 < a) : ContinuousOn wt (Icc a b) := by
  intro τ hτ
  have h0 : 0 < τ := lt_of_lt_of_le ha hτ.1
  unfold wt
  refine ContinuousAt.continuousWithinAt ?_
  exact ((Real.continuousAt_rpow_const _ _ (Or.inl h0.ne')).div (continuousAt_const.add continuousAt_id)
    (by positivity))

/-- Double integration by parts on `[a,b]` with a pointwise lower bound `p` of `|ϕ'|`. -/
lemma region_bound (hM : MData C0 m m1 m2 m3) {γ KB lam L a b : ℝ} (hγ : 0 < γ) (hKB : 0 ≤ KB) (hlam : 0 < lam)
    (ha : 0 < a) (hab : a ≤ b) {ϕ : ℝ → ℝ} (hϕ : ∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - L) τ)
    {B B1 B2 : ℝ → ℂ} (hB : ∀ τ ∈ Icc a b, HasDerivAt B (B1 τ) τ)
    (hB1 : ∀ τ ∈ Icc a b, HasDerivAt B1 (B2 τ) τ) (hc2 : ContinuousOn B2 (Icc a b))
    (hbB : ∀ τ ∈ Icc a b, ‖B τ‖ ≤ KB * τ ^ (1 / 2 : ℝ) / (1 + τ))
    (hbB1 : ∀ τ ∈ Icc a b, ‖B1 τ‖ ≤ KB * τ ^ (-1 / 2 : ℝ) / (1 + τ))
    (hbB2 : ∀ τ ∈ Icc a b, ‖B2 τ‖ ≤ KB * τ ^ (-3 / 2 : ℝ) / (1 + τ))
    {p : ℝ → ℝ} (hpc : ContinuousOn p (Icc a b))
    (hp : ∀ τ ∈ Icc a b, 0 < p τ ∧ p τ ≤ |m τ - L| ∧ γ * sg τ ≤ p τ) :
    ‖∫ τ in a..b, B τ * Complex.exp (Complex.I * lam * (ϕ τ : ℂ))‖ ≤
      (‖B b‖ / |m b - L| + ‖B a‖ / |m a - L|) / lam +
      (‖ibpH B B1 (fun τ => m τ - L) m1 b‖ / |m b - L| + ‖ibpH B B1 (fun τ => m τ - L) m1 a‖ / |m a - L|) / lam ^ 2 +
      (∫ τ in a..b, KB * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) * wt τ / p τ ^ 2) / lam ^ 2 := by
  have hpos : ∀ τ ∈ Icc a b, 0 < τ := fun τ hτ => lt_of_lt_of_le ha hτ.1
  have hne : ∀ τ ∈ Icc a b, m τ - L ≠ 0 := fun τ hτ => by
    have := hp τ hτ
    intro h0
    rw [h0, abs_zero] at this
    linarith [this.1, this.2.1]
  have hd0 : ∀ τ ∈ Icc a b, HasDerivAt (fun τ => m τ - L) (m1 τ) τ := fun τ hτ => by
    simpa using (hM.d0 τ (hpos τ hτ)).sub_const L
  have hbase := ibp_twice_bound hab hlam.ne' (ϕ := ϕ) (ϕ1 := fun τ => m τ - L) (ϕ2 := m1) (ϕ3 := m2)
    (fun τ hτ => hϕ τ (hpos τ hτ)) hd0 (fun τ hτ => hM.d1 τ (hpos τ hτ)) hne hB hB1 hc2
    (hM.cont_m2.mono (fun τ hτ => hpos τ hτ))
  rw [abs_of_pos hlam] at hbase
  refine hbase.trans ?_
  have hint : (∫ x in a..b, ‖ibpQ B B1 B2 (fun τ => m τ - L) m1 m2 x‖) ≤
      ∫ τ in a..b, KB * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) * wt τ / p τ ^ 2 := by
    -- continuity of both integrands
    have hcB : ContinuousOn B (Icc a b) := fun τ hτ => (hB τ hτ).continuousAt.continuousWithinAt
    have hcB1 : ContinuousOn B1 (Icc a b) := fun τ hτ => (hB1 τ hτ).continuousAt.continuousWithinAt
    have hc1 : ContinuousOn (fun τ => (m τ - L : ℝ)) (Icc a b) := fun τ hτ => (hd0 τ hτ).continuousAt.continuousWithinAt
    have hcm1 : ContinuousOn m1 (Icc a b) := hM.cont_m1.mono (fun τ hτ => hpos τ hτ)
    have hcm2 : ContinuousOn m2 (Icc a b) := hM.cont_m2.mono (fun τ hτ => hpos τ hτ)
    have hC1 : ContinuousOn (fun τ => ((m τ - L : ℝ) : ℂ)) (Icc a b) := Complex.continuous_ofReal.comp_continuousOn hc1
    have hC2 : ContinuousOn (fun τ => ((m1 τ : ℝ) : ℂ)) (Icc a b) := Complex.continuous_ofReal.comp_continuousOn hcm1
    have hC3 : ContinuousOn (fun τ => ((m2 τ : ℝ) : ℂ)) (Icc a b) := Complex.continuous_ofReal.comp_continuousOn hcm2
    have hneC : ∀ τ ∈ Icc a b, ((m τ - L : ℝ) : ℂ) ≠ 0 := fun τ hτ => by exact_mod_cast hne τ hτ
    have hQc : ContinuousOn (fun x => ibpQ B B1 B2 (fun τ => m τ - L) m1 m2 x) (Icc a b) := by
      unfold ibpQ
      refine ContinuousOn.add (ContinuousOn.sub (ContinuousOn.sub ?_ ?_) ?_) ?_
      · exact hc2.div (hC1.pow 2) (fun τ hτ => pow_ne_zero 2 (hneC τ hτ))
      · exact ((continuousOn_const.mul hcB1).mul hC2).div (hC1.pow 3) (fun τ hτ => pow_ne_zero 3 (hneC τ hτ))
      · exact (hcB.mul hC3).div (hC1.pow 3) (fun τ hτ => pow_ne_zero 3 (hneC τ hτ))
      · exact ((continuousOn_const.mul hcB).mul (hC2.pow 2)).div (hC1.pow 4) (fun τ hτ => pow_ne_zero 4 (hneC τ hτ))
    have hgc : ContinuousOn (fun τ => KB * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) * wt τ / p τ ^ 2) (Icc a b) :=
      ((continuousOn_const.mul (continuousOn_wt ha)).div (hpc.pow 2) (fun τ hτ => (pow_pos (hp τ hτ).1 2).ne'))
    refine intervalIntegral.integral_mono_on hab (hQc.norm.intervalIntegrable_of_Icc hab)
      (hgc.intervalIntegrable_of_Icc hab) fun τ hτ => ?_
    have := hp τ hτ
    exact Q_pt (hpos τ hτ) this.1 hγ hM.C0nn hKB this.2.2 this.2.1 (hM.abs_m1 (hpos τ hτ))
      (hM.b2 τ (hpos τ hτ) |> fun h => by simpa using h) (hbB τ hτ) (hbB1 τ hτ) (hbB2 τ hτ)
  have hl2 : 0 < lam ^ 2 := by positivity
  have := div_le_div_of_nonneg_right hint hl2.le
  linarith

end

end FormalResearch.SignUncertainty.CtOsc
