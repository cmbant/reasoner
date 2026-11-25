module

public import FormalResearch.SignUncertainty.StripAdmissTail
public import FormalResearch.SignUncertainty.MiddleBandSmall
public import FormalResearch.SignUncertainty.Gt1Interface
public import FormalResearch.SignUncertainty.MellinLiftSymbol

/-!
# Edge traces: from symbol bounds to `StripEdge0 (1/2)` (M6, `ceo:O11ak`, `uct:admiss`)

`edge_integral_tail` (`StripAdmissTail`) bounds `∫ K₀(iτ, ξ) W̃(iτ) dτ` by `L^{-1-α}` once the trace `τ ↦ W̃(iτ)` satisfies `StripEdge0 α W`.  The lift integrals
`I_main[X]`, `I_dual[X]` are of this form after the substitution `τ = ε v`, with the traces `v ↦ W_X(iv)` (main edge `ζ = 0`) and `v ↦ W_X(c^{1/3} - iv)` (reflected edge `ζ = 1`).
This module gives the regularity side:

* `EdgeTrace V`: the regularity a trace `V : ℝ → ℂ` needs: continuous, `C²` off `0` (derivatives `V1`, `V2`), `|V - V(0)| ≲ |s|^{1/2}`, `|V'| ≲ |s|^{-1/2}`, `|V''| ≲ |s|^{-3/2}` for
  `0 < |s| ≤ 1` and `|V^{(j)}| ≲ (1+|s|)^{-2}` for `|s| ≥ 1`;
* `EdgeTrace.of_gt1`: every symbol with the `GT.1` bounds `(cegt:eqGT1)` (`Gt1Bounds`) is an `EdgeTrace`;
* `stripEdge0_of_edgeTrace`: `V` an `EdgeTrace` and `0 < ε ≤ 1/2` give `StripEdge0 (1/2)` for the rescaled trace `τ ↦ V(τ/ε)`;
* `edgeTrace_dual`: for every seed with the `U.2` package (`HasU2 X`), `δ₀ ≥ 0`, `m` and `c ≥ 1`, the reflected trace `v ↦ W_X(c^{1/3} - iv)` is an `EdgeTrace`
  (it lies in the interior of the half plane, so Cauchy estimates replace the boundary analysis).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- The regularity of a trace `V : ℝ → ℂ` needed by `StripEdge0 (1/2)` (see the module docstring). -/
structure EdgeTrace (V : ℝ → ℂ) : Prop where
  cont : Continuous V
  deriv : ∃ V1 V2 : ℝ → ℂ, (∀ s : ℝ, s ≠ 0 → HasDerivAt V (V1 s) s ∧ HasDerivAt V1 (V2 s) s) ∧
    (∀ s : ℝ, s ≠ 0 → ContinuousAt V2 s) ∧ ∃ A : ℝ, 0 ≤ A ∧ ‖V 0‖ ≤ A ∧
    (∀ s : ℝ, 0 < |s| → |s| ≤ 1 → ‖V s - V 0‖ ≤ A * |s| ^ (1 / 2 : ℝ) ∧ ‖V1 s‖ ≤ A * |s| ^ (-(1 / 2) : ℝ) ∧
      ‖V2 s‖ ≤ A * |s| ^ (-(3 / 2) : ℝ)) ∧
    (∀ s : ℝ, 1 ≤ |s| → ‖V s‖ ≤ A * (1 + |s|) ^ (-(2 : ℝ)) ∧ ‖V1 s‖ ≤ A * (1 + |s|) ^ (-(2 : ℝ)) ∧
      ‖V2 s‖ ≤ A * (1 + |s|) ^ (-(2 : ℝ)))

lemma rpow_neg_five_halves_le {t : ℝ} (ht : 1 ≤ t) : t ^ (-(5 / 2) : ℝ) ≤ 4 * (1 + t) ^ (-(2 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have h1 : t ^ (-(5 / 2) : ℝ) ≤ t ^ (-(2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le ht (by norm_num)
  have h2 : t ^ (-(2 : ℝ)) = (t ^ 2)⁻¹ := by rw [Real.rpow_neg ht0.le, Real.rpow_two]
  have h3 : (1 + t) ^ (-(2 : ℝ)) = ((1 + t) ^ 2)⁻¹ := by rw [Real.rpow_neg (by linarith), Real.rpow_two]
  rw [h2] at h1
  rw [h3]
  refine h1.trans ?_
  have h4 : (1 + t) ^ 2 ≤ 4 * t ^ 2 := by nlinarith
  have h5 : (t ^ 2)⁻¹ ≤ 4 * ((1 + t) ^ 2)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  exact h5

/-- A symbol with the `GT.1` bounds is an `EdgeTrace`. -/
theorem EdgeTrace.of_gt1 {A : ℝ} {V : ℝ → ℂ} (h : Gt1Bounds A V) : EdgeTrace V := by
  obtain ⟨W1, W2, W3, hd, hl, hh, h0, hH⟩ := h
  have hA : 0 ≤ A := (norm_nonneg _).trans h0
  have hcont0 : ContinuousAt V 0 := by
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun s : ℝ => A * |s| ^ (1 / 2 : ℝ)) (𝓝 0) (𝓝 0) := by
      have : Tendsto (fun s : ℝ => |s| ^ (1 / 2 : ℝ)) (𝓝 0) (𝓝 0) := by
        have hc : Continuous fun s : ℝ => |s| ^ (1 / 2 : ℝ) := continuous_abs.rpow_const (fun _ => Or.inr (by norm_num))
        simpa using hc.tendsto 0
      simpa using this.const_mul A
    refine squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _) ?_ hlim
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with s hs
    rcases eq_or_ne s 0 with rfl | hs0
    · simp
    · exact hH s (abs_pos.mpr hs0) (by rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs; exact hs.le)
  have hcont : Continuous V := by
    refine continuous_iff_continuousAt.mpr fun s => ?_
    rcases eq_or_ne s 0 with rfl | hs0
    · exact hcont0
    · exact ((hd s hs0).1).continuousAt
  refine ⟨hcont, W1, W2, fun s hs => ⟨(hd s hs).1, (hd s hs).2.1⟩, fun s hs => (hd s hs).2.2.continuousAt, 4 * A,
    by positivity, h0.trans (by linarith), ?_, ?_⟩
  · intro s hs hs1
    obtain ⟨a, b, c⟩ := hl s hs hs1
    have hp : 0 ≤ |s| ^ (1 / 2 : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
    have hp1 : 0 ≤ |s| ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
    have hp2 : 0 ≤ |s| ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
    refine ⟨(hH s hs hs1).trans ?_, a.trans ?_, b.trans ?_⟩ <;> nlinarith [mul_nonneg hA hp, mul_nonneg hA hp1, mul_nonneg hA hp2]
  · intro s hs
    obtain ⟨a, b, c, d⟩ := hh s hs
    have hs0 : 0 < |s| := lt_of_lt_of_le one_pos hs
    have h5 := rpow_neg_five_halves_le hs
    have m1 : |s| ^ (-(7 / 2) : ℝ) ≤ |s| ^ (-(5 / 2) : ℝ) := Real.rpow_le_rpow_of_exponent_le hs (by norm_num)
    have m2 : |s| ^ (-(9 / 2) : ℝ) ≤ |s| ^ (-(5 / 2) : ℝ) := Real.rpow_le_rpow_of_exponent_le hs (by norm_num)
    have key : ∀ {x : ℝ}, x ≤ |s| ^ (-(5 / 2) : ℝ) → A * x ≤ 4 * A * (1 + |s|) ^ (-(2 : ℝ)) := fun {x} hx => by
      calc A * x ≤ A * (4 * (1 + |s|) ^ (-(2 : ℝ))) := mul_le_mul_of_nonneg_left (hx.trans h5) hA
        _ = _ := by ring
    exact ⟨a.trans (key le_rfl), b.trans (key m1), c.trans (key m2)⟩

set_option maxHeartbeats 800000 in
/-- The rescaled trace `τ ↦ V(ε⁻¹ τ)` of an `EdgeTrace` has `StripEdge0 (1/2)`, for `0 < ε ≤ 1/2` (the edge `ζ = iτ` of the function `ζ ↦ V(ε⁻¹ Im ζ)`). -/
theorem stripEdge0_of_edgeTrace {V : ℝ → ℂ} (hV : EdgeTrace V) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) :
    StripEdge0 (1 / 2) (fun ζ : ℂ => V (ε⁻¹ * ζ.im)) := by
  obtain ⟨V1, V2, hchain, hV2c, A, hA, hV0, hnear, hfar⟩ := hV.deriv
  have hR : 2 ≤ ε⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hε0]; simpa using hε
  set R : ℝ := ε⁻¹ with hRdef
  have hR0 : 0 < R := by linarith
  have hg : ∀ τ : ℝ, stripEdge0 (fun ζ : ℂ => V (R * ζ.im)) τ = V (R * τ) := fun τ => by simp [stripEdge0]
  have hgf : stripEdge0 (fun ζ : ℂ => V (R * ζ.im)) = fun τ => V (R * τ) := funext hg
  -- derivative chain of the rescaled trace
  have hlin : ∀ τ : ℝ, HasDerivAt (fun x : ℝ => R * x) R τ := fun τ => by
    simpa using (hasDerivAt_id τ).const_mul R
  have hd1 : ∀ τ : ℝ, τ ≠ 0 → HasDerivAt (fun x : ℝ => V (R * x)) (R • V1 (R * τ)) τ := fun τ hτ => by
    have hne : R * τ ≠ 0 := mul_ne_zero hR0.ne' hτ
    exact ((hchain _ hne).1).scomp τ (hlin τ)
  have hd2 : ∀ τ : ℝ, τ ≠ 0 → HasDerivAt (fun x : ℝ => R • V1 (R * x)) (R • (R • V2 (R * τ))) τ := fun τ hτ => by
    have hne : R * τ ≠ 0 := mul_ne_zero hR0.ne' hτ
    exact (((hchain _ hne).2).scomp τ (hlin τ)).const_smul R
  have hderiv1 : ∀ τ : ℝ, τ ≠ 0 → deriv (fun x : ℝ => V (R * x)) τ = R • V1 (R * τ) := fun τ hτ => (hd1 τ hτ).deriv
  have hderiv2 : ∀ τ : ℝ, τ ≠ 0 → deriv (deriv (fun x : ℝ => V (R * x))) τ = R • (R • V2 (R * τ)) := fun τ hτ => by
    have hev : deriv (fun x : ℝ => V (R * x)) =ᶠ[𝓝 τ] fun x => R • V1 (R * x) := by
      filter_upwards [isOpen_ne.mem_nhds hτ] with x hx using hderiv1 x hx
    rw [hev.deriv_eq]
    exact (hd2 τ hτ).deriv
  have hDc : ContinuousOn (fun x : ℝ => R • (R • V2 (R * x))) {y : ℝ | y ≠ 0} := fun y hy => by
    have h1 : ContinuousAt (fun x : ℝ => V2 (R * x)) y :=
      ContinuousAt.comp (g := V2) (f := fun x : ℝ => R * x) (hV2c _ (mul_ne_zero hR0.ne' hy))
        (continuousAt_const.mul continuousAt_id)
    exact ((h1.const_smul R).const_smul R).continuousWithinAt
  -- helper inequalities for the rescaling
  have hneg : ∀ (t e : ℝ), 0 ≤ t → e ≤ 0 → (R * t) ^ e ≤ t ^ e := fun t e ht he => by
    rw [Real.mul_rpow hR0.le ht]
    exact mul_le_of_le_one_left (Real.rpow_nonneg ht _) (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) he)
  have hpos : ∀ t : ℝ, 0 ≤ t → (R * t) ^ (1 / 2 : ℝ) ≤ R * t ^ (1 / 2 : ℝ) := fun t ht => by
    rw [Real.mul_rpow hR0.le ht]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg ht _)
    calc R ^ (1 / 2 : ℝ) ≤ R ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = R := Real.rpow_one R
  have hR1 : 1 ≤ R := by linarith
  have hR2 : R ≤ R ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hgf]
    intro τ hτ
    have hτ' : τ ≠ 0 := hτ
    have hD0 : ContDiffAt ℝ ((0 : ℕ) : WithTop ℕ∞) (fun x : ℝ => R • (R • V2 (R * x))) τ := by
      exact_mod_cast contDiffAt_zero.2 ⟨{y | y ≠ 0}, isOpen_ne.mem_nhds hτ', hDc⟩
    have hC1 : ContDiffAt ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) (fun x : ℝ => R • V1 (R * x)) τ := by
      refine contDiffAt_succ_of_hasDerivAt' (D := fun x => R • (R • V2 (R * x))) ?_ hD0
      filter_upwards [isOpen_ne.mem_nhds hτ'] with y hy using hd2 y hy
    have hC0 : ContDiffAt ℝ ((0 + 1 + 1 : ℕ) : WithTop ℕ∞) (fun x : ℝ => V (R * x)) τ := by
      refine contDiffAt_succ_of_hasDerivAt' (D := fun x => R • V1 (R * x)) ?_ hC1
      filter_upwards [isOpen_ne.mem_nhds hτ'] with y hy using hd1 y hy
    exact (show ContDiffAt ℝ 2 (fun x : ℝ => V (R * x)) τ by exact_mod_cast hC0).contDiffWithinAt
  · refine ⟨2 * A * R ^ 2, fun τ hτ hτ1 => ?_⟩
    rw [hgf]
    show ‖V (R * τ) - V (R * 0)‖ ≤ _ ∧ ‖deriv (fun x : ℝ => V (R * x)) τ‖ ≤ _ ∧
      ‖deriv (deriv (fun x : ℝ => V (R * x))) τ‖ ≤ _
    rw [hderiv1 τ hτ, hderiv2 τ hτ, mul_zero, norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hR0]
    have ht0 : 0 < |τ| := abs_pos.mpr hτ
    have hv : |R * τ| = R * |τ| := by rw [abs_mul, abs_of_pos hR0]
    have e1 : (1 / 2 : ℝ) - 1 = -(1 / 2) := by norm_num
    have e2 : (1 / 2 : ℝ) - 2 = -(3 / 2) := by norm_num
    rw [e1, e2]
    have p1 : 0 ≤ |τ| ^ (1 / 2 : ℝ) := Real.rpow_nonneg ht0.le _
    have p2 : 0 ≤ |τ| ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg ht0.le _
    have p3 : 0 ≤ |τ| ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg ht0.le _
    have q2 : 1 ≤ |τ| ^ (-(1 / 2) : ℝ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 hτ1 (by norm_num)
    have q3 : 1 ≤ |τ| ^ (-(3 / 2) : ℝ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 hτ1 (by norm_num)
    have hAR : 0 ≤ A * R ^ 2 := by positivity
    by_cases hv1 : |R * τ| ≤ 1
    · obtain ⟨a, b, c⟩ := hnear (R * τ) (by rw [hv]; positivity) hv1
      rw [hv] at a b c
      have a' := a.trans (mul_le_mul_of_nonneg_left (hpos _ ht0.le) hA)
      have b' := b.trans (mul_le_mul_of_nonneg_left (hneg _ _ ht0.le (by norm_num)) hA)
      have c' := c.trans (mul_le_mul_of_nonneg_left (hneg _ _ ht0.le (by norm_num)) hA)
      refine ⟨?_, ?_, ?_⟩
      · nlinarith [mul_nonneg hA p1, mul_nonneg (mul_nonneg hA p1) (by linarith : (0 : ℝ) ≤ R ^ 2 - R)]
      · have := mul_le_mul_of_nonneg_left b' hR0.le
        nlinarith [mul_nonneg (mul_nonneg hA p2) (by linarith : (0 : ℝ) ≤ R ^ 2 - R)]
      · have := mul_le_mul_of_nonneg_left c' (by positivity : (0 : ℝ) ≤ R * R)
        nlinarith [mul_nonneg (mul_nonneg hA p3) (by positivity : (0 : ℝ) ≤ R ^ 2)]
    · rw [not_le] at hv1
      obtain ⟨f0, f1, f2⟩ := hfar (R * τ) hv1.le
      have hb1 : (1 + |R * τ|) ^ (-(2 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (R * τ)]) (by norm_num)
      have g0 : ‖V (R * τ)‖ ≤ A := f0.trans (by nlinarith [mul_nonneg hA (by positivity : (0 : ℝ) ≤ (1 + |R * τ|) ^ (-(2 : ℝ)))])
      have g1 : ‖V1 (R * τ)‖ ≤ A := f1.trans (by nlinarith [mul_nonneg hA (by positivity : (0 : ℝ) ≤ (1 + |R * τ|) ^ (-(2 : ℝ)))])
      have g2 : ‖V2 (R * τ)‖ ≤ A := f2.trans (by nlinarith [mul_nonneg hA (by positivity : (0 : ℝ) ≤ (1 + |R * τ|) ^ (-(2 : ℝ)))])
      -- `R * |τ|^{1/2} ≥ 1`
      have hlow : 1 ≤ R * |τ| ^ (1 / 2 : ℝ) := by
        have h1 : 1 / R < |τ| := by rw [div_lt_iff₀ hR0]; rw [hv] at hv1; linarith
        have h2 : (1 / R) ^ (1 / 2 : ℝ) ≤ |τ| ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) h1.le (by norm_num)
        have h3 : 1 / R ≤ (1 / R) ^ (1 / 2 : ℝ) := by
          calc 1 / R = (1 / R) ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ (1 / R) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge (by positivity) (by rw [div_le_one hR0]; exact hR1) (by norm_num)
        have h4 : 1 / R ≤ |τ| ^ (1 / 2 : ℝ) := h3.trans h2
        rw [div_le_iff₀ hR0] at h4
        linarith
      have hRP : 1 ≤ R * (R * |τ| ^ (1 / 2 : ℝ)) := one_le_mul_of_one_le_of_one_le hR1 hlow
      have hARQ : 0 ≤ A * R ^ 2 := by positivity
      refine ⟨?_, ?_, ?_⟩
      · have h1 : ‖V (R * τ) - V 0‖ ≤ 2 * A := by
          have := norm_sub_le (V (R * τ)) (V 0)
          linarith
        calc ‖V (R * τ) - V 0‖ ≤ 2 * A := h1
          _ = 2 * A * 1 := by ring
          _ ≤ 2 * A * (R * (R * |τ| ^ (1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hRP (by positivity)
          _ = 2 * A * R ^ 2 * |τ| ^ (1 / 2 : ℝ) := by ring
      · calc R * ‖V1 (R * τ)‖ ≤ R * A := mul_le_mul_of_nonneg_left g1 hR0.le
          _ ≤ (A * R ^ 2) * 1 := by nlinarith [mul_nonneg hA (sub_nonneg.2 hR2)]
          _ ≤ (A * R ^ 2) * |τ| ^ (-(1 / 2) : ℝ) := mul_le_mul_of_nonneg_left q2 hARQ
          _ ≤ 2 * A * R ^ 2 * |τ| ^ (-(1 / 2) : ℝ) := by nlinarith [mul_nonneg hARQ p2]
      · calc R * (R * ‖V2 (R * τ)‖) ≤ R * (R * A) := by gcongr
          _ = (A * R ^ 2) * 1 := by ring
          _ ≤ (A * R ^ 2) * |τ| ^ (-(3 / 2) : ℝ) := mul_le_mul_of_nonneg_left q3 hARQ
          _ ≤ 2 * A * R ^ 2 * |τ| ^ (-(3 / 2) : ℝ) := by nlinarith [mul_nonneg hARQ p3]
  · refine ⟨A * R ^ 2, fun τ hτ => ?_⟩
    have hτ0 : τ ≠ 0 := by intro h0; rw [h0, abs_zero] at hτ; linarith
    rw [hgf]
    show ‖V (R * τ)‖ ≤ _ ∧ ‖deriv (fun x : ℝ => V (R * x)) τ‖ ≤ _ ∧ ‖deriv (deriv (fun x : ℝ => V (R * x))) τ‖ ≤ _
    rw [hderiv1 τ hτ0, hderiv2 τ hτ0, norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hR0]
    have hv : |R * τ| = R * |τ| := by rw [abs_mul, abs_of_pos hR0]
    have hv1 : 1 ≤ |R * τ| := by
      rw [hv]
      have := mul_le_mul hR hτ (by norm_num) (by linarith)
      linarith
    obtain ⟨f0, f1, f2⟩ := hfar (R * τ) hv1
    have hmono : (1 + |R * τ|) ^ (-(2 : ℝ)) ≤ (1 + |τ|) ^ (-(2 : ℝ)) := by
      refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by norm_num)
      rw [hv]
      have := mul_le_mul_of_nonneg_right hR1 (abs_nonneg τ)
      linarith
    have hp : 0 ≤ (1 + |τ|) ^ (-(2 : ℝ)) := Real.rpow_nonneg (by positivity) _
    have k0 : A * (1 + |R * τ|) ^ (-(2 : ℝ)) ≤ A * (1 + |τ|) ^ (-(2 : ℝ)) := mul_le_mul_of_nonneg_left hmono hA
    have hAp : 0 ≤ A * (1 + |τ|) ^ (-(2 : ℝ)) := mul_nonneg hA hp
    refine ⟨?_, ?_, ?_⟩
    · calc ‖V (R * τ)‖ ≤ A * (1 + |τ|) ^ (-(2 : ℝ)) := f0.trans k0
        _ = 1 * (A * (1 + |τ|) ^ (-(2 : ℝ))) := by ring
        _ ≤ R ^ 2 * (A * (1 + |τ|) ^ (-(2 : ℝ))) := mul_le_mul_of_nonneg_right (by nlinarith [hR1]) hAp
        _ = A * R ^ 2 * (1 + |τ|) ^ (-(2 : ℝ)) := by ring
    · calc R * ‖V1 (R * τ)‖ ≤ R * (A * (1 + |τ|) ^ (-(2 : ℝ))) := mul_le_mul_of_nonneg_left (f1.trans k0) hR0.le
        _ ≤ R ^ 2 * (A * (1 + |τ|) ^ (-(2 : ℝ))) := mul_le_mul_of_nonneg_right hR2 hAp
        _ = A * R ^ 2 * (1 + |τ|) ^ (-(2 : ℝ)) := by ring
    · calc R * (R * ‖V2 (R * τ)‖) ≤ R * (R * (A * (1 + |τ|) ^ (-(2 : ℝ)))) := by
            gcongr; exact f2.trans k0
        _ = A * R ^ 2 * (1 + |τ|) ^ (-(2 : ℝ)) := by ring

/-! ### The reflected trace: Cauchy estimates -/

lemma edgeDual_half_rpow_le {x y : ℝ} (h : |x - y| ≤ 1 / 4) :
    (1 + |x|) ^ (-(5 / 2) : ℝ) ≤ 8 * (1 + |y|) ^ (-(5 / 2) : ℝ) := by
  have hle : (1 + |y|) * 2⁻¹ ≤ 1 + |x| := by
    have h1 : |y| ≤ |x| + |x - y| := by
      have := abs_sub_abs_le_abs_sub y x
      rw [abs_sub_comm] at this; linarith [abs_nonneg (x - y)]
    linarith [abs_nonneg x]
  have h1 : (1 + |x|) ^ (-(5 / 2) : ℝ) ≤ ((1 + |y|) * 2⁻¹) ^ (-(5 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hle (by norm_num)
  have h2 : ((1 + |y|) * 2⁻¹) ^ (-(5 / 2) : ℝ) = (1 + |y|) ^ (-(5 / 2) : ℝ) * 2 ^ (5 / 2 : ℝ) := by
    rw [Real.mul_rpow (by positivity) (by norm_num), Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  have h3 : (2 : ℝ) ^ (5 / 2 : ℝ) ≤ 8 := by
    calc (2 : ℝ) ^ (5 / 2 : ℝ) ≤ 2 ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 8 := by norm_num
  rw [h2] at h1
  calc _ ≤ (1 + |y|) ^ (-(5 / 2) : ℝ) * 2 ^ (5 / 2 : ℝ) := h1
    _ ≤ (1 + |y|) ^ (-(5 / 2) : ℝ) * 8 := mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg (by positivity) _)
    _ = _ := by ring

/-- Cauchy estimate on the half plane: a bound `N (1 + |Im w|)^{-5/2}` on `Re w ≥ ρ` gives `32 N (1 + |Im w₀|)^{-5/2}` for the derivative on `Re w₀ ≥ ρ + 1/4`. -/
lemma cauchy_decay {H : ℂ → ℂ} (hd : DifferentiableOn ℂ H {w : ℂ | 0 < w.re}) {ρ N : ℝ} (hρ : 0 < ρ)
    (hb : ∀ w : ℂ, ρ ≤ w.re → ‖H w‖ ≤ N * (1 + |w.im|) ^ (-(5 / 2) : ℝ)) {w₀ : ℂ} (hw₀ : ρ + 1 / 4 ≤ w₀.re) :
    ‖deriv H w₀‖ ≤ 32 * N * (1 + |w₀.im|) ^ (-(5 / 2) : ℝ) := by
  have hr : (0 : ℝ) < 1 / 4 := by norm_num
  have hdist : ∀ w : ℂ, dist w w₀ ≤ 1 / 4 → ρ ≤ w.re ∧ |w.im - w₀.im| ≤ 1 / 4 := fun w hw => by
    rw [dist_eq_norm] at hw
    have h1 : |(w - w₀).re| ≤ 1 / 4 := (Complex.abs_re_le_norm _).trans hw
    have h2 : |(w - w₀).im| ≤ 1 / 4 := (Complex.abs_im_le_norm _).trans hw
    simp only [Complex.sub_re, Complex.sub_im] at h1 h2
    exact ⟨by linarith [(abs_le.mp h1).1], h2⟩
  have hsub : Metric.closedBall w₀ (1 / 4) ⊆ {w : ℂ | 0 < w.re} := fun w hw => by
    have := (hdist w (Metric.mem_closedBall.mp hw)).1
    exact lt_of_lt_of_le hρ this
  have hcl : DiffContOnCl ℂ H (Metric.ball w₀ (1 / 4)) :=
    (hd.mono (by rw [closure_ball w₀ hr.ne']; exact hsub)).diffContOnCl
  have hbd : ∀ w ∈ Metric.sphere w₀ (1 / 4), ‖H w‖ ≤ N * 8 * (1 + |w₀.im|) ^ (-(5 / 2) : ℝ) := fun w hw => by
    obtain ⟨h1, h2⟩ := hdist w (Metric.mem_sphere.mp hw).le
    have hN : 0 ≤ N * (1 + |w.im|) ^ (-(5 / 2) : ℝ) := (norm_nonneg _).trans (hb w h1)
    have hpos : 0 < (1 + |w.im|) ^ (-(5 / 2) : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    have hN0 : 0 ≤ N := by
      by_contra hneg
      rw [not_le] at hneg
      have := mul_neg_of_neg_of_pos hneg hpos
      linarith
    calc ‖H w‖ ≤ N * (1 + |w.im|) ^ (-(5 / 2) : ℝ) := hb w h1
      _ ≤ N * (8 * (1 + |w₀.im|) ^ (-(5 / 2) : ℝ)) := mul_le_mul_of_nonneg_left (edgeDual_half_rpow_le h2) hN0
      _ = _ := by ring
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hcl hbd
  refine this.trans (le_of_eq ?_)
  field_simp
  ring

/-- **The reflected trace** `v ↦ W_X(c^{1/3} - iv)` of a `U.2` seed is an `EdgeTrace` (`c ≥ 1`, `δ₀ ≥ 0`): holomorphy on `Re w > 0` and the bound
`C (1+|Im w|)^{-5/2}` give the decay of the first two derivatives by Cauchy estimates; no boundary analysis is needed because `Re w = c^{1/3} ≥ 1`. -/
theorem edgeTrace_dual {X : ℝ → ℝ} (hX : HasU2 X) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ) {c : ℝ} (hc : 1 ≤ c) :
    EdgeTrace (fun v : ℝ => liftSymbol X δ₀ m ((((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) - (v : ℂ) * Complex.I)) := by
  have hG := liftSymbolData_of_hasU2 hX hδ m
  have hd := hG.diff
  obtain ⟨B, hB⟩ := hG.bound
  set G := liftSymbol X δ₀ m with hGdef
  have hop : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdd := hd.deriv hop
  have hdd2 := hdd.deriv hop
  set a : ℝ := c ^ (1 / 3 : ℝ) with ha
  have ha1 : 1 ≤ a := Real.one_le_rpow hc (by norm_num)
  have hB' : ∀ w : ℂ, (1 / 4 : ℝ) ≤ w.re → ‖G w‖ ≤ |B| * (1 + |w.im|) ^ (-(5 / 2) : ℝ) := fun w hw =>
    (hB w (by linarith)).trans (mul_le_mul_of_nonneg_right (le_abs_self B) (Real.rpow_nonneg (by positivity) _))
  have hB0 : 0 ≤ |B| := abs_nonneg B
  have hb1 : ∀ w : ℂ, (1 / 2 : ℝ) ≤ w.re → ‖deriv G w‖ ≤ 32 * |B| * (1 + |w.im|) ^ (-(5 / 2) : ℝ) := fun w hw =>
    cauchy_decay hd (ρ := 1 / 4) (by norm_num) hB' (by linarith)
  have hb2 : ∀ w : ℂ, (3 / 4 : ℝ) ≤ w.re → ‖deriv (deriv G) w‖ ≤ 32 * (32 * |B|) * (1 + |w.im|) ^ (-(5 / 2) : ℝ) :=
    fun w hw => cauchy_decay hdd (ρ := 1 / 2) (by norm_num) hb1 (by linarith)
  set φ : ℝ → ℂ := fun v => (a : ℂ) - (v : ℂ) * Complex.I with hφdef
  have hφre : ∀ v : ℝ, (φ v).re = a := fun v => by simp [hφdef]
  have hφim : ∀ v : ℝ, (φ v).im = -v := fun v => by simp [hφdef]
  have hφd : ∀ v : ℝ, HasDerivAt φ (-Complex.I) v := fun v => by
    have := (((hasDerivAt_id v).ofReal_comp).mul_const Complex.I).const_sub (a : ℂ)
    simpa using this
  have hpos : ∀ v : ℝ, 0 < (φ v).re := fun v => by rw [hφre]; linarith
  have hGd : ∀ (H : ℂ → ℂ), DifferentiableOn ℂ H {w : ℂ | 0 < w.re} → ∀ w : ℂ, 0 < w.re →
      HasDerivAt H (deriv H w) w := fun H hH w hw => ((hH w hw).differentiableAt (hop.mem_nhds hw)).hasDerivAt
  set V1 : ℝ → ℂ := fun v => (-Complex.I) • deriv G (φ v) with hV1
  set V2 : ℝ → ℂ := fun v => (-Complex.I) • ((-Complex.I) • deriv (deriv G) (φ v)) with hV2
  have hV : ∀ v : ℝ, HasDerivAt (fun v : ℝ => G (φ v)) (V1 v) v := fun v =>
    (hGd G hd (φ v) (hpos v)).scomp v (hφd v)
  have hV1d : ∀ v : ℝ, HasDerivAt V1 (V2 v) v := fun v =>
    (((hGd (deriv G) hdd (φ v) (hpos v)).scomp v (hφd v)).const_smul (-Complex.I))
  set A : ℝ := 1024 * |B| with hAdef
  have hA : 0 ≤ A := by positivity
  have hnI : ‖(-Complex.I)‖ = 1 := by simp
  have hbd : ∀ v : ℝ, ‖G (φ v)‖ ≤ A * (1 + |v|) ^ (-(5 / 2) : ℝ) ∧ ‖V1 v‖ ≤ A * (1 + |v|) ^ (-(5 / 2) : ℝ) ∧
      ‖V2 v‖ ≤ A * (1 + |v|) ^ (-(5 / 2) : ℝ) := fun v => by
    have hp : 0 ≤ (1 + |v|) ^ (-(5 / 2) : ℝ) := Real.rpow_nonneg (by positivity) _
    have e0 := hB' (φ v) (by rw [hφre]; linarith)
    have e1 := hb1 (φ v) (by rw [hφre]; linarith)
    have e2 := hb2 (φ v) (by rw [hφre]; linarith)
    rw [hφim, abs_neg] at e0 e1 e2
    refine ⟨e0.trans ?_, ?_, ?_⟩
    · gcongr; rw [hAdef]; nlinarith
    · simp only [hV1, norm_smul, hnI, one_mul]
      refine e1.trans ?_
      gcongr; rw [hAdef]; nlinarith
    · simp only [hV2, norm_smul, hnI, one_mul]
      refine e2.trans ?_
      gcongr; rw [hAdef]; nlinarith
  have hle1 : ∀ v : ℝ, (1 + |v|) ^ (-(5 / 2) : ℝ) ≤ 1 :=
    fun v => Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg v]) (by norm_num)
  refine ⟨continuous_iff_continuousAt.mpr fun v => (hV v).continuousAt, V1, V2, fun s _ => ⟨hV s, hV1d s⟩, fun s _ => ?_, A, hA, ?_, ?_, ?_⟩
  · have h2 : ContinuousAt (fun v : ℝ => deriv (deriv G) (φ v)) s := by
      have hc2 : ContinuousAt (deriv (deriv G)) (φ s) := hdd2.continuousOn.continuousAt (hop.mem_nhds (hpos s))
      have hφc : ContinuousAt φ s := (hφd s).continuousAt
      exact hc2.comp hφc
    exact (h2.const_smul (-Complex.I)).const_smul (-Complex.I)
  · have := (hbd 0).1
    simp only [abs_zero, add_zero, Real.one_rpow, mul_one] at this
    exact this
  · intro s hs hs1
    have hlip : ‖G (φ s) - G (φ 0)‖ ≤ A * ‖s - 0‖ := by
      refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun v : ℝ => G (φ v)) (f' := V1) (s := Set.univ)
        (fun x _ => (hV x).hasDerivWithinAt) (fun x _ => ?_) convex_univ trivial trivial
      exact (hbd x).2.1.trans (by nlinarith [mul_nonneg hA (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + |x|) (-(5 / 2) : ℝ)), mul_le_mul_of_nonneg_left (hle1 x) hA])
    have hp1 : 1 ≤ |s| ^ (-(1 / 2) : ℝ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs hs1 (by norm_num)
    have hp3 : 1 ≤ |s| ^ (-(3 / 2) : ℝ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs hs1 (by norm_num)
    have hsq : |s| ≤ |s| ^ (1 / 2 : ℝ) := by
      calc |s| = |s| ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ |s| ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hs hs1 (by norm_num)
    have hv1 := (hbd s).2.1
    have hv2 := (hbd s).2.2
    have hAle : ∀ x : ℝ, A * (1 + |s|) ^ (-(5 / 2) : ℝ) ≤ A * x → ‖V1 s‖ ≤ A * x := fun x hx => hv1.trans hx
    refine ⟨?_, ?_, ?_⟩
    · rw [sub_zero, Real.norm_eq_abs] at hlip
      exact hlip.trans (mul_le_mul_of_nonneg_left hsq hA)
    · exact hv1.trans ((mul_le_mul_of_nonneg_left (hle1 s) hA).trans (by nlinarith))
    · exact hv2.trans ((mul_le_mul_of_nonneg_left (hle1 s) hA).trans (by nlinarith))
  · intro s hs
    have hmono : (1 + |s|) ^ (-(5 / 2) : ℝ) ≤ (1 + |s|) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg s]) (by norm_num)
    obtain ⟨b0, b1, b2⟩ := hbd s
    exact ⟨b0.trans (mul_le_mul_of_nonneg_left hmono hA), b1.trans (mul_le_mul_of_nonneg_left hmono hA),
      b2.trans (mul_le_mul_of_nonneg_left hmono hA)⟩

/-- info: 'FormalResearch.SignUncertainty.EdgeTrace.of_gt1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EdgeTrace.of_gt1

/-- info: 'FormalResearch.SignUncertainty.stripEdge0_of_edgeTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stripEdge0_of_edgeTrace

/-- info: 'FormalResearch.SignUncertainty.edgeTrace_dual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgeTrace_dual

end FormalResearch.SignUncertainty
