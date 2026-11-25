module

public import FormalResearch.SignUncertainty.UctStripSplit
public import FormalResearch.CohnElkies.MellinAiryToolkit

/-!
# `uct:strip-split` (2): the exact floor-oscillation cancellation integrals (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:strip-split` (2), `(uct:int-star)`, `(uct:int-ce)`, `(uct:int-hhat)`.
Notation as in `UctStripSplit` (`uctM τ = m(τ) = ℓ(πτ/2)`, envelopes `uctIfl`, `uctIoscStar`, `uctIoscCE`, `uctIoscH`).

* `uct_strip_split_integrals` (headline):
  `∫_0^∞ (I_osc^* - I_fl) dL = 0`, `∫_0^∞ (I_osc^CE - I_fl) dL = -(π/2) α_osc`, `∫_0^∞ I_osc^ĥ dL = (π/2) α_osc`, each as an integrable function on `(0,∞)`
  (the differences are integrable although `I_osc^*`, `I_osc^CE`, `I_fl` are separately not integrable at `L = 0`).
* Method (the paper's): substitute `L = m(τ)` (`uct_subst`, the one-variable change of variables for the strictly increasing `m`), which cancels `m'(τ)` and
  leaves the primitives `π/(e^{πρ}-1)` and `π/(e^{πρ}+1)`; the tail `∫_{m(ρ)}^∞ I_fl = 2 α_fl m(ρ)^{-1/2}`; and the limit `ρ ↓ 0`
  (`uct_Phi_limit`, using `ℓ(x) = x²/3 - O(x⁴)` and the Taylor bounds `1 + y + y²/2 ≤ e^y ≤ 1 + y + y²/2 + (2/9)y³`).
  Integrability on `(0,∞)` comes from `integrableOn_Ioi_zero_of_trunc` (monotone truncation of a nonnegative function; `I_fl - I_osc^CE ≥ 0` is
  `uct_strip_split_ratios`), and the `(uct:int-star)` line from the pointwise identity `I_osc^* = I_osc^CE + I_osc^ĥ`
  (`uctIoscStar_eq`, a consequence of `(uct:H-split)`: `|H_*(iτ)| = |H_CE(iτ)| + H_CE(1+iτ)`).
* Not formalised in this file: the small-`L` expansions `I_osc^* - I_fl = (47/20) α_fl L^{-1/2} + O(L^{1/2})`,
  `I_osc^CE - I_fl = -(13/20) α_fl L^{-1/2} + O(L^{1/2})` and the `τ ↓ 0` expansions of `r_CE`, `r_ĥ`.

Class: proved, no hypotheses.  Axiom guards are at the end.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- `m(τ) = ℓ(πτ/2) = log((πτ/2) coth(πτ/2))`. -/
noncomputable def uctM (τ : ℝ) : ℝ := ceEll (π * τ / 2)

lemma uctM_pos {τ : ℝ} (hτ : 0 < τ) : 0 < uctM τ := ceEll_pos (by positivity)

lemma uctM_strictMonoOn : StrictMonoOn uctM (Ioi 0) := fun a ha b hb hab =>
  ceEll_strictMonoOn (mem_Ioi.mpr (by have : 0 < a := ha; positivity)) (mem_Ioi.mpr (by have : 0 < b := hb; positivity))
    (by have := Real.pi_pos; nlinarith)

lemma uctMderiv_pos {τ : ℝ} (hτ : 0 < τ) : 0 < uctMderiv τ := by
  unfold uctMderiv
  have := uctEllDeriv_pos (show 0 < π * τ / 2 by positivity)
  positivity

lemma uctM_image {ρ : ℝ} (hρ : 0 < ρ) : uctM '' Ioi ρ = Ioi (uctM ρ) := by
  ext L
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact uctM_strictMonoOn (mem_Ioi.mpr hρ) (mem_Ioi.mpr (hρ.trans hτ)) hτ
  · intro hL
    have hL' : uctM ρ < L := hL
    have hL0 : 0 < L := (uctM_pos hρ).trans hL'
    have hτ := tau0_pos hL0
    have hm : uctM (tau0 L) = L := ceEll_tau0 hL0
    refine ⟨tau0 L, ?_, hm⟩
    by_contra hle
    have := uctM_strictMonoOn.monotoneOn (mem_Ioi.mpr hτ) (mem_Ioi.mpr hρ) (not_lt.mp hle)
    rw [hm] at this
    linarith

lemma uctM_tendsto_zero : Tendsto uctM (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h1 : Tendsto (fun τ : ℝ => π * τ / 2) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Tendsto (fun τ : ℝ => π * τ / 2) (𝓝 0) (𝓝 (π * 0 / 2)) :=
          ((continuous_const.mul continuous_id).div_const 2).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with τ hτ
        exact mem_Ioi.mpr (by have : 0 < τ := hτ; positivity)
    exact ceEll_tendsto_zero.comp h1
  · filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact mem_Ioi.mpr (uctM_pos hτ)

/-- Change of variables `L = m(τ)` on `(ρ, ∞)`. -/
lemma uct_subst {ρ : ℝ} (hρ : 0 < ρ) (g : ℝ → ℝ) :
    ∫ L in Ioi (uctM ρ), g L = ∫ τ in Ioi ρ, uctMderiv τ * g (uctM τ) := by
  rw [← uctM_image hρ, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi (f := uctM) (f' := uctMderiv)
    (fun τ hτ => (hasDerivAt_uctM (hρ.trans hτ)).hasDerivWithinAt)
    (uctM_strictMonoOn.injOn.mono fun τ hτ => hρ.trans hτ) g]
  refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
  simp only [smul_eq_mul]
  rw [abs_of_pos (uctMderiv_pos (hρ.trans hτ))]

lemma uct_subst_integrableOn {ρ : ℝ} (hρ : 0 < ρ) (g : ℝ → ℝ) :
    IntegrableOn g (Ioi (uctM ρ)) ↔ IntegrableOn (fun τ => uctMderiv τ * g (uctM τ)) (Ioi ρ) := by
  rw [← uctM_image hρ, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi (f := uctM) (f' := uctMderiv)
    (fun τ hτ => (hasDerivAt_uctM (hρ.trans hτ)).hasDerivWithinAt)
    (uctM_strictMonoOn.injOn.mono fun τ hτ => hρ.trans hτ) g]
  refine integrableOn_congr_fun (fun τ hτ => ?_) measurableSet_Ioi
  simp only [smul_eq_mul]
  rw [abs_of_pos (uctMderiv_pos (hρ.trans hτ))]


lemma uctMderiv_mul_uctIoscCE {τ : ℝ} (hτ : 0 < τ) :
    uctMderiv τ * uctIoscCE (uctM τ) = uctAlphaOsc * (π ^ 2 / (4 * Real.sinh (π * τ / 2) ^ 2)) := by
  have hm := (uctMderiv_pos hτ).ne'
  unfold uctIoscCE
  rw [show uctM τ = ceEll (π * τ / 2) from rfl, tau0_ceEll hτ, norm_uctHCE_imag hτ]
  field_simp

lemma uctMderiv_mul_uctIoscH {τ : ℝ} (hτ : 0 < τ) :
    uctMderiv τ * uctIoscH (uctM τ) = uctAlphaOsc * (π ^ 2 / (4 * Real.cosh (π * τ / 2) ^ 2)) := by
  have hm := (uctMderiv_pos hτ).ne'
  unfold uctIoscH
  rw [show uctM τ = ceEll (π * τ / 2) from rfl, tau0_ceEll hτ, uctHCE_one_add_imag_re]
  field_simp

lemma pi_sq_div_sinh (τ : ℝ) (hτ : 0 < τ) :
    π ^ 2 / (4 * Real.sinh (π * τ / 2) ^ 2) = π ^ 2 * Real.exp (π * τ) / (Real.exp (π * τ) - 1) ^ 2 := by
  have hE : Real.exp (π * τ) = Real.exp (π * τ / 2) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hE1 : 1 < Real.exp (π * τ / 2) := Real.one_lt_exp_iff.mpr (by positivity)
  have hneg : Real.exp (-(π * τ / 2)) = (Real.exp (π * τ / 2))⁻¹ := Real.exp_neg _
  rw [Real.sinh_eq, hneg, hE]
  have h0 : Real.exp (π * τ / 2) ≠ 0 := by positivity
  have h1 : Real.exp (π * τ / 2) ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp
  ring

lemma pi_sq_div_cosh (τ : ℝ) :
    π ^ 2 / (4 * Real.cosh (π * τ / 2) ^ 2) = π ^ 2 * Real.exp (π * τ) / (Real.exp (π * τ) + 1) ^ 2 := by
  have hE : Real.exp (π * τ) = Real.exp (π * τ / 2) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hneg : Real.exp (-(π * τ / 2)) = (Real.exp (π * τ / 2))⁻¹ := Real.exp_neg _
  rw [Real.cosh_eq, hneg, hE]
  have h0 : 0 < Real.exp (π * τ / 2) := by positivity
  have h1 : Real.exp (π * τ / 2) ^ 2 + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma ftc_Ioi {F f' : ℝ → ℝ} {ρ : ℝ} (hd : ∀ τ : ℝ, ρ ≤ τ → HasDerivAt F (f' τ) τ) (hnn : ∀ τ : ℝ, ρ < τ → 0 ≤ f' τ)
    (hlim : Tendsto F atTop (𝓝 0)) : IntegrableOn f' (Ioi ρ) ∧ ∫ τ in Ioi ρ, f' τ = -F ρ := by
  have hc : ContinuousWithinAt F (Ici ρ) ρ := (hd ρ le_rfl).continuousAt.continuousWithinAt
  have hi : IntegrableOn f' (Ioi ρ) :=
    integrableOn_Ioi_deriv_of_nonneg hc (fun τ hτ => hd τ (le_of_lt hτ)) (fun τ hτ => hnn τ hτ) hlim
  refine ⟨hi, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hc (fun τ hτ => hd τ (le_of_lt hτ)) hi hlim]
  ring

lemma tendsto_exp_pi_mul_atTop : Tendsto (fun τ : ℝ => Real.exp (π * τ)) atTop atTop :=
  Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop Real.pi_pos)

/-- `∫_ρ^∞ π² e^{πτ}/(e^{πτ}-1)² dτ = π/(e^{πρ}-1)`. -/
lemma integral_sinh_tail {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun τ : ℝ => π ^ 2 * Real.exp (π * τ) / (Real.exp (π * τ) - 1) ^ 2) (Ioi ρ) ∧
      ∫ τ in Ioi ρ, π ^ 2 * Real.exp (π * τ) / (Real.exp (π * τ) - 1) ^ 2 = π / (Real.exp (π * ρ) - 1) := by
  have key := ftc_Ioi (F := fun τ => -(π / (Real.exp (π * τ) - 1))) (f' := fun τ => π ^ 2 * Real.exp (π * τ) / (Real.exp (π * τ) - 1) ^ 2) (ρ := ρ)
    (fun τ hτ => by
      have hτ0 : 0 < τ := hρ.trans_le hτ
      have h1 : 1 < Real.exp (π * τ) := Real.one_lt_exp_iff.mpr (by positivity)
      have hne : Real.exp (π * τ) - 1 ≠ 0 := by linarith
      have h2 : HasDerivAt (fun τ : ℝ => Real.exp (π * τ) - 1) (Real.exp (π * τ) * π) τ :=
        (((hasDerivAt_id τ).const_mul π).exp).sub_const 1 |>.congr_deriv (by simp)
      have h3 := (h2.inv hne).const_mul π |>.neg
      refine h3.congr_deriv ?_
      field_simp)
    (fun τ hτ => by
      have : 0 ≤ Real.exp (π * τ) := (Real.exp_pos _).le
      positivity)
    (by
      have h1 : Tendsto (fun τ : ℝ => Real.exp (π * τ) - 1) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_exp_pi_mul_atTop
      have := (tendsto_const_nhds (x := π)).div_atTop h1
      simpa using this.neg)
  refine ⟨key.1, ?_⟩
  rw [key.2]; ring

/-- `∫_ρ^∞ π² e^{πτ}/(e^{πτ}+1)² dτ = π/(e^{πρ}+1)`. -/
lemma integral_cosh_tail (ρ : ℝ) :
    IntegrableOn (fun τ : ℝ => π ^ 2 * Real.exp (π * τ) / (Real.exp (π * τ) + 1) ^ 2) (Ioi ρ) ∧
      ∫ τ in Ioi ρ, π ^ 2 * Real.exp (π * τ) / (Real.exp (π * τ) + 1) ^ 2 = π / (Real.exp (π * ρ) + 1) := by
  have key := ftc_Ioi (F := fun τ => -(π / (Real.exp (π * τ) + 1))) (f' := fun τ => π ^ 2 * Real.exp (π * τ) / (Real.exp (π * τ) + 1) ^ 2) (ρ := ρ)
    (fun τ hτ => by
      have hne : Real.exp (π * τ) + 1 ≠ 0 := by positivity
      have h2 : HasDerivAt (fun τ : ℝ => Real.exp (π * τ) + 1) (Real.exp (π * τ) * π) τ :=
        (((hasDerivAt_id τ).const_mul π).exp).add_const 1 |>.congr_deriv (by simp)
      have h3 := (h2.inv hne).const_mul π |>.neg
      refine h3.congr_deriv ?_
      field_simp)
    (fun τ hτ => by
      have : 0 ≤ Real.exp (π * τ) := (Real.exp_pos _).le
      positivity)
    (by
      have h1 : Tendsto (fun τ : ℝ => Real.exp (π * τ) + 1) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_exp_pi_mul_atTop
      have := (tendsto_const_nhds (x := π)).div_atTop h1
      simpa using this.neg)
  refine ⟨key.1, ?_⟩
  rw [key.2]; ring


lemma exp_two_mul_bounds {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) :
    2 * x + 2 * x ^ 2 ≤ Real.exp (2 * x) - 1 ∧ Real.exp (2 * x) - 1 ≤ 2 * x + 2 * x ^ 2 + 16 / 9 * x ^ 3 := by
  constructor
  · have := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ 2 * x)
    nlinarith
  · have hb := Real.exp_bound (x := 2 * x) (by rw [abs_of_nonneg (by linarith)]; linarith) (n := 3) (by norm_num)
    have h := (abs_le.mp hb).2
    rw [abs_of_nonneg (by linarith : 0 ≤ 2 * x)] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h
    nlinarith

/-- `T(x) = (3ℓ(x))^{-1/2} - 2/(e^{2x} - 1)`. -/
noncomputable def uctTlim (x : ℝ) : ℝ := (Real.sqrt (3 * ceEll x))⁻¹ - 2 / (Real.exp (2 * x) - 1)

lemma uctTlim_close {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) : |uctTlim x - 1| ≤ 2 * x := by
  have hl := ceEll_pos hx0
  have hlt := ceEll_lt_sq_div_three hx0
  have hge : x ^ 2 / 3 - 2 / 15 * x ^ 4 ≤ ceEll x := by
    have h1 := ceHth_le_of_le_one hx0 (by linarith : x ≤ 1)
    have e : ceEll x = x ^ 2 / 3 - ceHth x := by
      unfold ceEll ceHth
      rw [show x / Real.tanh x = (Real.tanh x / x)⁻¹ by rw [inv_div], Real.log_inv]; ring
    linarith
  set s := Real.sqrt (3 * ceEll x) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs1 : s < x := by rw [hs]; exact (Real.sqrt_lt' hx0).mpr (by linarith)
  have hq0 : 0 < 1 + x ^ 2 / 2 := by positivity
  have hs2 : x / (1 + x ^ 2 / 2) ≤ s := by
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    rw [div_pow, div_le_iff₀ (by positivity)]
    have h3 : 1 ≤ (1 - 2 / 5 * x ^ 2) * (1 + x ^ 2 / 2) ^ 2 := by
      have hu : x ^ 2 ≤ 1 / 4 := by nlinarith
      have hu2 : x ^ 4 ≤ 1 / 16 := by nlinarith [pow_pos hx0 2]
      have : 0 ≤ x ^ 2 * (3 / 5 - 3 / 20 * x ^ 2 - 1 / 10 * x ^ 4) := mul_nonneg (sq_nonneg x) (by nlinarith)
      nlinarith [this]
    nlinarith [pow_pos hx0 2, pow_pos hx0 4, mul_le_mul_of_nonneg_left h3 (pow_pos hx0 2).le]
  have hxp1 : 1 < x * s⁻¹ := by
    rw [← div_eq_mul_inv, lt_div_iff₀ hs0]; linarith
  have hxp2 : x * s⁻¹ ≤ 1 + x ^ 2 / 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hs0]
    have := (div_le_iff₀ hq0).mp hs2
    linarith
  obtain ⟨hE1, hE2⟩ := exp_two_mul_bounds hx0 hx1
  set E := Real.exp (2 * x) - 1 with hE
  have hE0 : 0 < E := by nlinarith [pow_pos hx0 2]
  have hxb1 : x * (2 / E) ≤ 1 / (1 + x) := by
    rw [← mul_div_assoc, div_le_div_iff₀ hE0 (by linarith)]
    nlinarith [pow_pos hx0 2]
  have hxb2 : 1 - x - 8 / 9 * x ^ 2 ≤ x * (2 / E) := by
    rw [← mul_div_assoc, le_div_iff₀ hE0]
    have hpos : 0 ≤ 1 - x - 8 / 9 * x ^ 2 := by nlinarith [sq_nonneg x]
    have := mul_le_mul_of_nonneg_left hE2 hpos
    nlinarith [pow_pos hx0 3, pow_pos hx0 4, pow_pos hx0 5]
  have hxb1' : x * (2 / E) ≤ 1 - x / (1 + x) := by
    have : 1 / (1 + x) = 1 - x / (1 + x) := by field_simp; ring
    linarith
  unfold uctTlim
  rw [← hs, ← hE]
  rw [abs_le]
  constructor
  · -- T - 1 ≥ -2x
    have h1 : x * (s⁻¹ - 2 / E) ≥ x / (1 + x) := by nlinarith [hxp1]
    have h2 : x / (1 + x) ≥ x * (1 - x) := by
      rw [ge_iff_le, le_div_iff₀ (by linarith)]
      nlinarith [pow_pos hx0 3]
    have : x * (s⁻¹ - 2 / E) ≥ x * (1 - x) := le_trans h2 h1
    have h4 : s⁻¹ - 2 / E ≥ 1 - x := le_of_mul_le_mul_left (by linarith) hx0
    linarith
  · have h1 : x * (s⁻¹ - 2 / E - 1) ≤ x * (2 * x) := by nlinarith [hxp2, hxb2, pow_pos hx0 2]
    have := le_of_mul_le_mul_left h1 hx0
    linarith


lemma uct_Phi_eq {ρ : ℝ} (hρ : 0 < ρ) :
    2 * uctAlphaFl * uctM ρ ^ (-(1 / 2 : ℝ)) - uctAlphaOsc * (π / (Real.exp (π * ρ) - 1)) =
      2 * Real.sqrt 3 * uctAlphaFl * uctTlim (π * ρ / 2) := by
  have hx : 0 < π * ρ / 2 := by positivity
  have hl := ceEll_pos hx
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsl : 0 < Real.sqrt (ceEll (π * ρ / 2)) := Real.sqrt_pos.mpr hl
  have hE : 0 < Real.exp (π * ρ) - 1 := by
    have : 1 < Real.exp (π * ρ) := Real.one_lt_exp_iff.mpr (by positivity)
    linarith
  have hexp : Real.exp (2 * (π * ρ / 2)) = Real.exp (π * ρ) := by congr 1; ring
  unfold uctTlim
  rw [hexp, Real.sqrt_mul (by norm_num), show uctM ρ = ceEll (π * ρ / 2) from rfl, Real.rpow_neg hl.le, ← Real.sqrt_eq_rpow,
    uctAlphaOsc_eq]
  have hpi := Real.pi_pos
  field_simp
  ring

/-- `Φ_CE(ρ) = 2 α_fl m(ρ)^{-1/2} - α_osc π/(e^{πρ}-1) → (π/2) α_osc` as `ρ ↓ 0` (so `∫_{m(ρ)}^∞ (I_fl - I_osc^CE) → (π/2) α_osc`). -/
lemma uct_Phi_limit :
    Tendsto (fun ρ : ℝ => 2 * uctAlphaFl * uctM ρ ^ (-(1 / 2 : ℝ)) - uctAlphaOsc * (π / (Real.exp (π * ρ) - 1))) (𝓝[>] 0)
      (𝓝 (uctAlphaOsc * (π / 2))) := by
  have hT : Tendsto (fun ρ : ℝ => uctTlim (π * ρ / 2)) (𝓝[>] 0) (𝓝 1) := by
    have h0 : Tendsto (fun ρ : ℝ => π * ρ) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun ρ : ℝ => π * ρ) (𝓝 0) (𝓝 (π * 0)) := (continuous_const.mul continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have hb : ∀ᶠ ρ : ℝ in 𝓝[>] 0, ‖uctTlim (π * ρ / 2) - 1‖ ≤ π * ρ := by
      have h1 : ∀ᶠ ρ : ℝ in 𝓝[>] 0, ρ < 1 / π := nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
      filter_upwards [h1, self_mem_nhdsWithin] with ρ h1 h2
      have hρ : 0 < ρ := h2
      have := uctTlim_close (x := π * ρ / 2) (by positivity) (by
        have : π * ρ < 1 := by rwa [lt_div_iff₀ Real.pi_pos, mul_comm] at h1
        linarith)
      rw [Real.norm_eq_abs]; linarith
    have := squeeze_zero_norm' hb h0
    have h2 : Tendsto (fun ρ : ℝ => uctTlim (π * ρ / 2) - 1 + 1) (𝓝[>] 0) (𝓝 (0 + 1)) := this.add tendsto_const_nhds
    simpa using h2
  have hc : uctAlphaOsc * (π / 2) = 2 * Real.sqrt 3 * uctAlphaFl * 1 := by
    rw [uctAlphaOsc_eq]; have := Real.pi_pos; field_simp; ring
  rw [hc]
  refine (hT.const_mul (2 * Real.sqrt 3 * uctAlphaFl)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  exact (uct_Phi_eq hρ).symm

lemma uct_PhiH_limit :
    Tendsto (fun ρ : ℝ => uctAlphaOsc * (π / (Real.exp (π * ρ) + 1))) (𝓝[>] 0) (𝓝 (uctAlphaOsc * (π / 2))) := by
  have : Tendsto (fun ρ : ℝ => uctAlphaOsc * (π / (Real.exp (π * ρ) + 1))) (𝓝 0) (𝓝 (uctAlphaOsc * (π / (Real.exp (π * 0) + 1)))) := by
    refine Continuous.tendsto ?_ 0
    exact continuous_const.mul (continuous_const.div ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).add continuous_const)
      fun ρ => (add_pos (Real.exp_pos _) one_pos).ne')
  have h2 : Real.exp (π * 0) + 1 = 2 := by norm_num
  rw [h2] at this
  exact this.mono_left nhdsWithin_le_nhds


lemma uctIoscCE_tail {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn uctIoscCE (Ioi (uctM ρ)) ∧
      ∫ L in Ioi (uctM ρ), uctIoscCE L = uctAlphaOsc * (π / (Real.exp (π * ρ) - 1)) := by
  have hf := integral_sinh_tail hρ
  have hfun : ∀ τ ∈ Ioi ρ, uctMderiv τ * uctIoscCE (uctM τ) =
      uctAlphaOsc * (π ^ 2 * Real.exp (π * τ) / (Real.exp (π * τ) - 1) ^ 2) := by
    intro τ hτ
    have hτ0 : 0 < τ := hρ.trans hτ
    rw [uctMderiv_mul_uctIoscCE hτ0, pi_sq_div_sinh τ hτ0]
  constructor
  · rw [uct_subst_integrableOn hρ]
    have h1 : IntegrableOn (fun τ : ℝ => uctAlphaOsc * (π ^ 2 * Real.exp (π * τ) / (Real.exp (π * τ) - 1) ^ 2)) (Ioi ρ) := hf.1.const_mul uctAlphaOsc
    exact IntegrableOn.congr_fun h1 (fun τ hτ => (hfun τ hτ).symm) measurableSet_Ioi
  · rw [uct_subst hρ, setIntegral_congr_fun measurableSet_Ioi hfun, integral_const_mul, hf.2]

lemma uctIoscH_tail {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn uctIoscH (Ioi (uctM ρ)) ∧
      ∫ L in Ioi (uctM ρ), uctIoscH L = uctAlphaOsc * (π / (Real.exp (π * ρ) + 1)) := by
  have hf := integral_cosh_tail ρ
  have hfun : ∀ τ ∈ Ioi ρ, uctMderiv τ * uctIoscH (uctM τ) =
      uctAlphaOsc * (π ^ 2 * Real.exp (π * τ) / (Real.exp (π * τ) + 1) ^ 2) := by
    intro τ hτ
    have hτ0 : 0 < τ := hρ.trans hτ
    rw [uctMderiv_mul_uctIoscH hτ0, pi_sq_div_cosh τ]
  constructor
  · rw [uct_subst_integrableOn hρ]
    have h1 : IntegrableOn (fun τ : ℝ => uctAlphaOsc * (π ^ 2 * Real.exp (π * τ) / (Real.exp (π * τ) + 1) ^ 2)) (Ioi ρ) := hf.1.const_mul uctAlphaOsc
    exact IntegrableOn.congr_fun h1 (fun τ hτ => (hfun τ hτ).symm) measurableSet_Ioi
  · rw [uct_subst hρ, setIntegral_congr_fun measurableSet_Ioi hfun, integral_const_mul, hf.2]

lemma uctIfl_tail {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn uctIfl (Ioi ε) ∧ ∫ L in Ioi ε, uctIfl L = 2 * uctAlphaFl * ε ^ (-(1 / 2 : ℝ)) := by
  constructor
  · exact (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) hε).const_mul uctAlphaFl
  · unfold uctIfl
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) hε]
    rw [show -(3 / 2 : ℝ) + 1 = -(1 / 2) by norm_num]
    field_simp

/-- A nonnegative function on `(0,∞)` that is integrable on each `(m(ρ), ∞)`, whose truncated integrals converge to `J` as `ρ ↓ 0`,
is integrable on `(0, ∞)` with integral `J`. -/
lemma integrableOn_Ioi_zero_of_trunc {H : ℝ → ℝ} {J : ℝ} (hH0 : ∀ L : ℝ, 0 < L → 0 ≤ H L)
    (hint : ∀ ρ : ℝ, 0 < ρ → IntegrableOn H (Ioi (uctM ρ)))
    (hlim : Tendsto (fun ρ : ℝ => ∫ L in Ioi (uctM ρ), H L) (𝓝[>] 0) (𝓝 J)) :
    IntegrableOn H (Ioi 0) ∧ ∫ L in Ioi 0, H L = J := by
  set r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hr
  have hr0 : ∀ n, 0 < r n := fun n => by simp only [hr]; positivity
  have hrlim : Tendsto r atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun n => mem_Ioi.mpr (hr0 n)⟩
  set ε : ℕ → ℝ := fun n => uctM (r n) with hε
  have hε0 : ∀ n, 0 < ε n := fun n => uctM_pos (hr0 n)
  have hεlim : Tendsto ε atTop (𝓝 0) := (tendsto_nhdsWithin_iff.mp (uctM_tendsto_zero.comp hrlim)).1
  have hcov : AECover (volume.restrict (Ioi (0 : ℝ))) atTop (fun n => Ioi (ε n)) :=
    { ae_eventually_mem := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact (hεlim.eventually (gt_mem_nhds (mem_Ioi.mp hx)))
      measurableSet := fun _ => measurableSet_Ioi }
  have hsub : ∀ n, Ioi (ε n) ⊆ Ioi (0 : ℝ) := fun n => Ioi_subset_Ioi (hε0 n).le
  have hres : ∀ n (f : ℝ → ℝ), ∫ x in Ioi (ε n), f x ∂(volume.restrict (Ioi (0 : ℝ))) = ∫ x in Ioi (ε n), f x := by
    intro n f
    rw [Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.mpr (hsub n)]
  have hlimn : Tendsto (fun n => ∫ L in Ioi (ε n), H L) atTop (𝓝 J) := hlim.comp hrlim
  have hI : Integrable H (volume.restrict (Ioi (0 : ℝ))) := by
    refine hcov.integrable_of_integral_norm_bounded (|J| + 1) (fun n => ?_) ?_
    · have h := hint (r n) (hr0 n)
      show Integrable H ((volume.restrict (Ioi (0 : ℝ))).restrict (Ioi (ε n)))
      rw [Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.mpr (hsub n)]
      exact h
    · filter_upwards [hlimn.eventually (Metric.ball_mem_nhds J one_pos)] with n hn
      rw [hres n (fun x => ‖H x‖)]
      have : ∫ x in Ioi (ε n), ‖H x‖ = ∫ x in Ioi (ε n), H x :=
        setIntegral_congr_fun measurableSet_Ioi fun x hx => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hH0 x ((hε0 n).trans hx))]
      rw [this]
      rw [Real.dist_eq] at hn
      have := (abs_lt.mp hn).2
      linarith [le_abs_self J]
  refine ⟨hI, ?_⟩
  have h2 := hcov.integral_tendsto_of_countably_generated hI
  have h3 : Tendsto (fun n => ∫ L in Ioi (ε n), H L) atTop (𝓝 (∫ L in Ioi (0 : ℝ), H L)) := by
    refine h2.congr fun n => ?_
    exact hres n H
  exact tendsto_nhds_unique h3 hlimn


lemma uctIoscH_nonneg {L : ℝ} (hL : 0 < L) : 0 ≤ uctIoscH L := by
  have hτ := tau0_pos hL
  unfold uctIoscH
  rw [uctHCE_one_add_imag_re]
  have := uctMderiv_pos hτ
  have := uctAlphaOsc_pos
  positivity

lemma uctIoscCE_le {L : ℝ} (hL : 0 < L) : uctIoscCE L ≤ uctIfl L := by
  have hτ := tau0_pos hL
  have h := (uct_strip_split_ratios.1 (tau0 L) hτ).1
  rw [ceEll_tau0 hL] at h
  have hI : 0 < uctIfl L := by unfold uctIfl; have := uctAlphaFl_pos; positivity
  exact ((div_lt_one hI).mp h).le

lemma uct_int_hhat :
    IntegrableOn uctIoscH (Ioi 0) ∧ ∫ L in Ioi 0, uctIoscH L = π / 2 * uctAlphaOsc := by
  have := integrableOn_Ioi_zero_of_trunc (H := uctIoscH) (J := uctAlphaOsc * (π / 2)) (fun L hL => uctIoscH_nonneg hL)
    (fun ρ hρ => (uctIoscH_tail hρ).1)
    (uct_PhiH_limit.congr' (by
      filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact (uctIoscH_tail hρ).2.symm))
  exact ⟨this.1, by rw [this.2]; ring⟩

lemma uct_int_ce :
    IntegrableOn (fun L => uctIoscCE L - uctIfl L) (Ioi 0) ∧
      ∫ L in Ioi 0, (uctIoscCE L - uctIfl L) = -(π / 2) * uctAlphaOsc := by
  have h := integrableOn_Ioi_zero_of_trunc (H := fun L => uctIfl L - uctIoscCE L) (J := uctAlphaOsc * (π / 2))
    (fun L hL => sub_nonneg.mpr (uctIoscCE_le hL))
    (fun ρ hρ => (uctIfl_tail (uctM_pos hρ)).1.sub (uctIoscCE_tail hρ).1)
    (uct_Phi_limit.congr' (by
      filter_upwards [self_mem_nhdsWithin] with ρ hρ
      have hρ' : 0 < ρ := hρ
      rw [integral_sub (uctIfl_tail (uctM_pos hρ')).1 (uctIoscCE_tail hρ').1, (uctIfl_tail (uctM_pos hρ')).2, (uctIoscCE_tail hρ').2]))
  refine ⟨?_, ?_⟩
  · have := h.1.neg
    refine this.congr_fun (fun L _ => by simp) measurableSet_Ioi
  · have := integral_neg (μ := volume.restrict (Ioi (0 : ℝ))) (fun L => uctIfl L - uctIoscCE L)
    simp only [neg_sub] at this
    rw [this, h.2]; ring

lemma uctHstar_imag_norm {τ : ℝ} (hτ : 0 < τ) :
    ‖uctHstar ((τ : ℂ) * Complex.I)‖ = π ^ 2 / (4 * Real.sinh (π * τ / 2) ^ 2) + π ^ 2 / (4 * Real.cosh (π * τ / 2) ^ 2) := by
  have hint : ∀ n : ℤ, (τ : ℂ) * Complex.I ≠ n := by
    intro n h
    have := congrArg Complex.im h
    simp at this
    exact hτ.ne' this
  have h1 := uct_H_split hint
  have h2 : (1 : ℂ) - (τ : ℂ) * Complex.I = 1 + ((-τ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h1, h2, uctHCE_imag, uctHCE_one_add_imag]
  have hsh : 0 < Real.sinh (π * τ / 2) := Real.sinh_pos_iff.mpr (by positivity)
  have e : (π * (-τ) / 2) = -(π * τ / 2) := by ring
  rw [e, Real.cosh_neg]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have : 0 < π ^ 2 / (4 * Real.sinh (π * τ / 2) ^ 2) := by positivity
  have : 0 < π ^ 2 / (4 * Real.cosh (π * τ / 2) ^ 2) := by positivity
  rw [abs_of_neg (by linarith)]; ring

lemma uctIoscStar_eq {L : ℝ} (hL : 0 < L) : uctIoscStar L = uctIoscCE L + uctIoscH L := by
  have hτ := tau0_pos hL
  unfold uctIoscStar uctIoscCE uctIoscH
  rw [uctHstar_imag_norm hτ, norm_uctHCE_imag hτ, uctHCE_one_add_imag_re]
  ring

/-- **`(uct:int-star)`, `(uct:int-ce)`, `(uct:int-hhat)`** of `uct:strip-split` (2): the three exact cancellation integrals,
with integrability of the (individually non-integrable at `L = 0`) differences on `(0,∞)`. -/
theorem uct_strip_split_integrals :
    (IntegrableOn (fun L => uctIoscStar L - uctIfl L) (Ioi 0) ∧ ∫ L in Ioi 0, (uctIoscStar L - uctIfl L) = 0) ∧
      (IntegrableOn (fun L => uctIoscCE L - uctIfl L) (Ioi 0) ∧
        ∫ L in Ioi 0, (uctIoscCE L - uctIfl L) = -(π / 2) * uctAlphaOsc) ∧
      (IntegrableOn uctIoscH (Ioi 0) ∧ ∫ L in Ioi 0, uctIoscH L = π / 2 * uctAlphaOsc) := by
  obtain ⟨hce1, hce2⟩ := uct_int_ce
  obtain ⟨hh1, hh2⟩ := uct_int_hhat
  refine ⟨⟨?_, ?_⟩, ⟨hce1, hce2⟩, ⟨hh1, hh2⟩⟩
  · refine (hce1.add hh1).congr_fun (fun L hL => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]
    rw [uctIoscStar_eq (mem_Ioi.mp hL)]; ring
  · have h : ∀ L ∈ Ioi (0 : ℝ), uctIoscStar L - uctIfl L = (uctIoscCE L - uctIfl L) + uctIoscH L := fun L hL => by
      rw [uctIoscStar_eq (mem_Ioi.mp hL)]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi h, integral_add hce1 hh1, hce2, hh2]; ring

/-- info: 'FormalResearch.SignUncertainty.uct_strip_split_integrals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_strip_split_integrals

/-- info: 'FormalResearch.SignUncertainty.uct_Phi_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_Phi_limit

/-- info: 'FormalResearch.SignUncertainty.uct_subst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_subst

/-- info: 'FormalResearch.SignUncertainty.integrableOn_Ioi_zero_of_trunc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integrableOn_Ioi_zero_of_trunc

end FormalResearch.SignUncertainty
