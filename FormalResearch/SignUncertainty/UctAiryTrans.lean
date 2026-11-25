module

public import FormalResearch.SignUncertainty.UctAiryTransPhi

/-!
# `uct:airy-trans`: closed-form twisted transforms, asymptotics and origin expansion (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:airy-trans` (Lemma of Section "Closed-form twisted transforms of `F_*` and `g₁`").
Notation: `f₁ = ceF1`, `F_* = -f₁`, `F_{*,δ} = F_* - δ g₁` (`uctFstarDelta δ`), `g₁ = ceG1 (airyZero 1)`, `X̃(i w) = airyTwistedLaplaceC X w`
(`k e^{-w³/12} ∫ X e^{w u}`), `E, E₁, E₂ = uctE, uctE1, uctE2`, `c_* = uctC = k/√π`.

Where each part lives (all proved, no hypotheses):
* **(1) exact representations** (`UctAiryTransClosed`, here): `uct_airy_trans_int_rep_F`, `uct_airy_trans_int_rep_g1` (both lines of
  `(uct:Fstar-int)`, `(uct:g1-int)` on `Re w ≥ 0`, the contour integrals over the segment `[0,w]` being `uctSegInt`);
  `uctE_differentiable`, `uctE1_differentiable`, `uctE2_differentiable` (entire), `uctE_zero`, `hasDerivAt_uctE_zero` (`E(0)=1`, `E'(0)=2a₁/3`),
  `uctE1_zero`, `hasDerivAt_uctE1_zero`, `uctE2_zero` (`E₁(0)=1`, `E₁'(0)=a₁`, `E₂(0)=2/3`).  **Not formalised:** the two ray identities
  `∫_{S±} s^{-1/2} e^{ψ(s)} ds = 0`, `(2√π)^{-1} ∫_{S±} s^{1/2} e^{ψ(s)} ds = 1` (used nowhere downstream: the TeX uses them only to rotate the
  contour in (2), which is replaced here by the ODE/barrier argument).
* **(2) asymptotics** (`UctAiryTransAsymp`, `UctAiryTransPhi`): `uct_airy_trans_asymp_Fstar`, `uct_airy_trans_asymp_g1`, `uct_airy_trans_phi`
  (`(uct:Fstar-asym)`, `(uct:phicd-bnds)`, all derivative orders, derivatives of the integral-defined functions on the closed half plane).
* **(3) origin expansion and real-axis bounds** (`UctAiryTransSmall`, here): `uct_airy_trans_small`, `uct_airy_trans_small_deriv_R2`,
  `uct_airy_trans_small_deriv_F`, `uct_airy_trans_pos`, `uct_airy_trans_real`, `uct_airy_trans_loc`, `uct_airy_trans_vert`.

Reading of the paper: in `(uct:Fstar-small)` the bounds of `∂_q^j F̃_{*,δ}(iq)` are formalised as derivatives with respect to the real parameter
`q` of `q ↦ F̃_{*,δ}(i·(iq))` (the imaginary-axis derivative, the same convention as `R^{(2)}_{*,δ}(iq)`); the literal argument `iq` would put
`w̃ = q` on the real axis, where for `q < 0` the transform is not defined.  `F̃(ix)`, `x > 0` in `(uct:Fstar-real)` is the real transform
`airyTwistedLaplace`.  In `(uct:Fstar-vert)` the term `C 1_{x<1, |y|>x/2} min(|y|^{1/2},1)` is an `if`.

Class: proved.  Axiom guards are in this file.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- **`(uct:Fstar-small)`, first estimate**. -/
theorem uct_airy_trans_small : ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ w : ℂ, 0 ≤ w.re → ‖w‖ ≤ 2 →
    ‖airyTwistedLaplaceC (uctFstarDelta δ) w + (ceK : ℂ) * δ + uctC * w ^ (1 / 2 : ℂ) + (δ : ℂ) * (ceK : ℂ) * uctA1 * w‖ ≤
      C * ‖w‖ ^ (3 / 2 : ℝ) := by
  obtain ⟨M, hM0, hM⟩ := uctR2_bound
  refine ⟨M, hM0, fun δ hδ0 hδ1 w hw hw2 => ?_⟩
  rw [airyTwistedLaplaceC_uctFstarDelta_R2 δ hw]
  exact hM δ hδ0 hδ1 w (by linarith)

/-- **`(uct:Fstar-small)`, second estimate**: derivatives of `R^{(2)}_{*,δ}(i q)` along the imaginary axis. -/
theorem uct_airy_trans_small_deriv_R2 (j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ q : ℝ, q ≠ 0 → |q| ≤ 2 →
    ‖iteratedDeriv j (fun t : ℝ => airyTwistedLaplaceC (uctFstarDelta δ) (Complex.I * (t : ℂ)) + (ceK : ℂ) * δ +
        uctC * (Complex.I * (t : ℂ)) ^ (1 / 2 : ℂ) + (δ : ℂ) * (ceK : ℂ) * uctA1 * (Complex.I * (t : ℂ))) q‖ ≤
      C * |q| ^ ((3 / 2 : ℝ) - j) := by
  obtain ⟨C, hC0, hC⟩ := uctR2_deriv_bound j
  refine ⟨C, hC0, fun δ hδ0 hδ1 q hq0 hq2 => ?_⟩
  have : (fun t : ℝ => airyTwistedLaplaceC (uctFstarDelta δ) (Complex.I * (t : ℂ)) + (ceK : ℂ) * δ +
        uctC * (Complex.I * (t : ℂ)) ^ (1 / 2 : ℂ) + (δ : ℂ) * (ceK : ℂ) * uctA1 * (Complex.I * (t : ℂ))) =
      fun t : ℝ => uctR2 δ (Complex.I * (t : ℂ)) := by
    funext t
    exact airyTwistedLaplaceC_uctFstarDelta_R2 δ (by simp)
  rw [this]
  exact hC δ hδ0 hδ1 q hq0 hq2

lemma iteratedDeriv_succ_sub_const (f : ℝ → ℂ) (c : ℂ) (j : ℕ) :
    iteratedDeriv (j + 1) (fun t => f t - c) = iteratedDeriv (j + 1) f := by
  rw [iteratedDeriv_succ', iteratedDeriv_succ']
  congr 1
  funext t
  exact deriv_sub_const c

/-- **`(uct:Fstar-small)`, third estimate**: `∂_q^j F̃_{*,δ}(i·(iq)) = O(|q|^{1/2-j})`, `j ≥ 1`. -/
theorem uct_airy_trans_small_deriv_F (j : ℕ) (hj : 1 ≤ j) : ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → ∀ q : ℝ, q ≠ 0 → |q| ≤ 2 →
    ‖iteratedDeriv j (fun t : ℝ => airyTwistedLaplaceC (uctFstarDelta δ) (Complex.I * (t : ℂ))) q‖ ≤
      C * |q| ^ ((1 / 2 : ℝ) - j) := by
  obtain ⟨C, hC0, hC⟩ := uctGd_deriv_bound j
  refine ⟨C, hC0, fun δ hδ0 hδ1 q hq0 hq2 => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have : (fun t : ℝ => airyTwistedLaplaceC (uctFstarDelta δ) (Complex.I * (t : ℂ))) =
      fun t : ℝ => uctGd δ (Complex.I * (t : ℂ)) - (δ : ℂ) * (ceK : ℂ) := by
    funext t
    exact airyTwistedLaplaceC_uctFstarDelta_eq_Gd δ (by simp)
  rw [this, iteratedDeriv_succ_sub_const (fun t : ℝ => uctGd δ (Complex.I * (t : ℂ)))]
  exact hC δ hδ0 hδ1 q hq0 hq2


/-- The contour integral `∫_{[0,w]} f(s) ds` over the segment from `0` to `w` (`s = t w`). -/
noncomputable def uctSegInt (f : ℂ → ℂ) (w : ℂ) : ℂ := w * ∫ t in Ioc (0 : ℝ) 1, f ((t : ℂ) * w)

lemma uctSegInt_kap (w : ℂ) :
    uctSegInt (fun s => s ^ (-(1 / 2 : ℂ)) * cexp (uctPsi s)) w = w ^ (1 / 2 : ℂ) * uctWI uctKap w := by
  unfold uctSegInt uctWI
  have h : ∫ t in Ioc (0 : ℝ) 1, ((t : ℂ) * w) ^ (-(1 / 2 : ℂ)) * cexp (uctPsi ((t : ℂ) * w)) =
      w ^ (-(1 / 2 : ℂ)) * ∫ t in Ioc (0 : ℝ) 1, uctKap t * cexp (uctPsi (w * (t : ℂ))) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    show ((t : ℂ) * w) ^ (-(1 / 2 : ℂ)) * cexp (uctPsi ((t : ℂ) * w)) = _
    rw [mul_comm (t : ℂ) w, cpow_mul_ofReal_pos w ht.1]
    unfold uctKap; ring
  rw [h]
  by_cases hw : w = 0
  · subst hw; simp [Complex.zero_cpow]
  · rw [← mul_assoc, mul_cpow_neg_half hw]

lemma uctSegInt_kap1 (w : ℂ) :
    uctSegInt (fun s => (w - s) * (s ^ (-(1 / 2 : ℂ)) * cexp (uctPsi s))) w = w ^ (3 / 2 : ℂ) * uctWI uctKap1 w := by
  unfold uctSegInt uctWI
  have h : ∫ t in Ioc (0 : ℝ) 1, (w - (t : ℂ) * w) * (((t : ℂ) * w) ^ (-(1 / 2 : ℂ)) * cexp (uctPsi ((t : ℂ) * w))) =
      w * w ^ (-(1 / 2 : ℂ)) * ∫ t in Ioc (0 : ℝ) 1, uctKap1 t * cexp (uctPsi (w * (t : ℂ))) := by
    rw [mul_assoc, ← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    show (w - (t : ℂ) * w) * (((t : ℂ) * w) ^ (-(1 / 2 : ℂ)) * cexp (uctPsi ((t : ℂ) * w))) = _
    rw [mul_comm (t : ℂ) w, cpow_mul_ofReal_pos w ht.1]
    unfold uctKap1; push_cast; ring
  rw [h]
  by_cases hw : w = 0
  · subst hw; simp [Complex.zero_cpow]
  · have : w * w * w ^ (-(1 / 2 : ℂ)) = w ^ (3 / 2 : ℂ) := by
      rw [mul_assoc, mul_cpow_neg_half hw, mul_comm]; exact cpow_half_mul_self hw
    rw [← this]; ring


/-- **`(uct:Fstar-int)` of `uct:airy-trans` (1)**: both integral representations of `F̃_*(i w)` on `Re w ≥ 0`. -/
theorem uct_airy_trans_int_rep_F {w : ℂ} (hw : 0 ≤ w.re) :
    airyTwistedLaplaceC (fun u => -ceF1 u) w =
        -((ceK : ℂ) / (2 * (Real.sqrt π : ℂ))) * cexp (uctA1 * w - w ^ 3 / 12) *
          uctSegInt (fun s => s ^ (-(1 / 2 : ℂ)) * cexp (uctPsi s)) w ∧
      airyTwistedLaplaceC (fun u => -ceF1 u) w = -((ceK : ℂ) / (Real.sqrt π : ℂ)) * w ^ (1 / 2 : ℂ) * uctE w := by
  have h0 : airyTwistedLaplaceC (fun u => -ceF1 u) w = -uctF1Ext w := by
    rw [← uctFstarDelta_zero, airyTwistedLaplaceC_uctFstarDelta 0 hw]; simp
  have hs : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  refine ⟨?_, ?_⟩
  · rw [h0, uctSegInt_kap]
    unfold uctF1Ext uctE uctC
    field_simp
  · rw [h0]; unfold uctF1Ext uctC; ring

/-- **`(uct:g1-int)` of `uct:airy-trans` (1)**: both integral representations of `g̃₁(i w)` on `Re w ≥ 0`. -/
theorem uct_airy_trans_int_rep_g1 {w : ℂ} (hw : 0 ≤ w.re) :
    airyTwistedLaplaceC (ceG1 (airyZero 1)) w =
        (ceK : ℂ) * cexp (uctA1 * w - w ^ 3 / 12) * (1 + 1 / (2 * (Real.sqrt π : ℂ)) *
          uctSegInt (fun s => (w - s) * (s ^ (-(1 / 2 : ℂ)) * cexp (uctPsi s))) w) ∧
      airyTwistedLaplaceC (ceG1 (airyZero 1)) w =
        (ceK : ℂ) * uctE1 w + (ceK : ℂ) / (Real.sqrt π : ℂ) * w ^ (3 / 2 : ℂ) * uctE2 w := by
  have h0 := airyTwistedLaplaceC_ceG1_closed hw
  have hs : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  refine ⟨?_, h0⟩
  rw [h0, uctSegInt_kap1]
  unfold uctE1 uctE2
  field_simp


/-- Positivity statements of `uct:airy-trans` (3): `-F̃_*(i x) > 0` for `x > 0` and `g̃₁(i x) > 0` for `x ≥ 0` (real transforms). -/
theorem uct_airy_trans_pos :
    (∀ x : ℝ, 0 < x → 0 < -airyTwistedLaplace (fun u => -ceF1 u) x) ∧
      (∀ x : ℝ, 0 ≤ x → 0 < airyTwistedLaplace (ceG1 (airyZero 1)) x) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [← uctFstarDelta_zero, airyTwistedLaplace_uctFstarDelta hx.le]
    simpa using uctFr_pos hx
  · obtain ⟨bg, Cg, hbg, -, hG⟩ := airyTwistedLaplace_ceG1_nonneg_bounds
    exact lt_of_lt_of_le (by positivity) (hG x hx).1

/-- info: 'FormalResearch.SignUncertainty.uct_airy_trans_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_airy_trans_pos

/-- info: 'FormalResearch.SignUncertainty.uct_airy_trans_int_rep_F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_airy_trans_int_rep_F

/-- info: 'FormalResearch.SignUncertainty.uct_airy_trans_int_rep_g1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_airy_trans_int_rep_g1

/-- info: 'FormalResearch.SignUncertainty.uct_airy_trans_asymp_Fstar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_airy_trans_asymp_Fstar

/-- info: 'FormalResearch.SignUncertainty.uct_airy_trans_asymp_g1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_airy_trans_asymp_g1

/-- info: 'FormalResearch.SignUncertainty.uct_airy_trans_phi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_airy_trans_phi

/-- info: 'FormalResearch.SignUncertainty.uct_airy_trans_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_airy_trans_small

/-- info: 'FormalResearch.SignUncertainty.uct_airy_trans_small_deriv_R2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_airy_trans_small_deriv_R2

/-- info: 'FormalResearch.SignUncertainty.uct_airy_trans_small_deriv_F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_airy_trans_small_deriv_F

/-- info: 'FormalResearch.SignUncertainty.uct_airy_trans_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_airy_trans_real

/-- info: 'FormalResearch.SignUncertainty.uct_airy_trans_loc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_airy_trans_loc

/-- info: 'FormalResearch.SignUncertainty.uct_airy_trans_vert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_airy_trans_vert

/-- info: 'FormalResearch.SignUncertainty.uctE_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uctE_differentiable

/-- info: 'FormalResearch.SignUncertainty.hasDerivAt_uctE_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_uctE_zero

end FormalResearch.SignUncertainty
