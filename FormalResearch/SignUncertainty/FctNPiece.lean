/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctNBlocks

/-!
# The pieces `L₁ Re/Im φ_kill(iτ₀(L̃); a)/L̃` of the `φ_kill` factor are symbols of class `(M, -1, 0)` (`fct:bump-sym-check` (a))

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (a), fourth item.  For `|L₁| ≤ κ a⁸` (`a = c^{-1/12}`,
`|L₁| ≤ K c^{-2/3}` by `physL1_le`):

`L₁ L(φ_kill(iτ₀(x - s); a))/(x - s) ∈ SymW [x₀, ∞) (pw M (-1) 0)`, i.e. `|∂_x^r (·)| ≤ K_r M min(x^{1-r}, x^{-r})`, `M = M(κ)`,
`K` absolute, uniformly in `L ∈ {Re, Im}`, `a ≤ 1`, `|s| ≤ x₀/2`, `x₀ ≤ 1/2`.

The proof joins the two regimes `x ≤ 1/2` (`block_small`: `L₁ Θ a^{-8} x⁴ · x^{-1} ≤ κ Θ x³ ≤ κ Θ x`) and `x ≥ 1/2` (`block_large`:
`L = L(1) - L(1 - φ_kill)`, weight `|L₁| x^{-1} ≤ 2 κ`).

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Filter Topology Finset
open scoped ContDiff Real

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter
  FormalResearch.SignUncertainty.FctPhiKill

lemma USym.mono_hyp {P : Type*} {H H' : P → Prop} {S : P → Set ℝ} {w f : P → ℝ → ℝ} (h : USym H S w f)
    (hH : ∀ p, H' p → H p) : USym H' S w f := by
  obtain ⟨K, hK⟩ := h
  exact ⟨K, fun p hp => hK p (hH p hp)⟩

lemma pw_neg_one_zero_of_le {M x : ℝ} (hx : x ≤ 1) : pw M (-1) 0 x = M * x := by
  unfold pw
  rw [if_pos hx]
  simp

lemma pw_neg_one_zero_of_gt {M x : ℝ} (hx : 1 < x) : pw M (-1) 0 x = M := by
  unfold pw
  rw [if_neg (not_le.mpr hx)]
  simp

lemma pw_ge_half {M x : ℝ} (hM : 0 ≤ M) (hx : 1 / 2 ≤ x) : M / 2 ≤ pw M (-1) 0 x := by
  rcases le_or_gt x 1 with h | h
  · rw [pw_neg_one_zero_of_le h]; nlinarith
  · rw [pw_neg_one_zero_of_gt h]; linarith

/-- `x ↦ (x - s)^{-1}` as a uniform symbol on `[x₀, ∞)`. -/
lemma usym_inv_shift : USym NHyp (fun p => Ici p.x₀) (fun _ x => |(1 : ℝ)| * x ^ (-1 : ℝ))
    (fun p x => 1 * (x - p.s) ^ (-1 : ℝ)) :=
  ⟨SymW.Kpow (-1), fun p hp => SymW.rpow_sub hp.2.2.2.1 1 (-1) p.s hp.2.2.2.2.2⟩

/-- **The `φ_kill` pieces** (see the module docstring). -/
theorem pieceN_usym (κ : ℝ) (hκ : 0 ≤ κ) : ∃ M : ℝ, 0 ≤ M ∧
    USym (fun p : NPar => NHyp p ∧ |p.L₁| ≤ κ * p.a ^ 8) (fun p => Ici p.x₀) (fun _ => pw M (-1) 0)
      (fun p x => p.L₁ * p.L (phiKill p.a ((tau0 (x - p.s) : ℂ) * Complex.I)) / (x - p.s)) := by
  obtain ⟨Θ, hΘ, hsm⟩ := block_small
  have hlg := block_large
  set M : ℝ := κ * Θ + 4 * κ with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨M, hM0, ?_⟩
  set H : NPar → Prop := fun p => NHyp p ∧ |p.L₁| ≤ κ * p.a ^ 8 with hH
  have hHN : ∀ p, H p → NHyp p := fun p hp => hp.1
  have rps := usym_inv_shift.mono_hyp hHN
  have hsU : ∀ p, H p → ∀ x, p.x₀ ≤ x → p.s < x := fun p hp x hx => by
    have := hp.1.2.2.2.2.2
    have := hp.1.2.2.2.1
    linarith [(abs_le.mp ‹|p.s| ≤ p.x₀ / 2›).2]
  -- weights
  have wsmall : ∀ p, H p → ∀ x ∈ Icc p.x₀ (1 / 2 : ℝ),
      (|p.L₁| * (Θ * (p.a ^ 8)⁻¹ * x ^ 4)) * (|(1 : ℝ)| * x ^ (-1 : ℝ)) ≤ pw M (-1) 0 x := by
    intro p hp x hx
    have hx0 : 0 < x := lt_of_lt_of_le hp.1.2.2.2.1 hx.1
    have ha := hp.1.2.1
    have ha8 : 0 < p.a ^ 8 := by positivity
    rw [pw_neg_one_zero_of_le (hx.2.trans (by norm_num)), abs_one, Real.rpow_neg_one]
    have h1 : |p.L₁| ≤ κ * p.a ^ 8 := hp.2
    have h2 : 0 ≤ Θ * (p.a ^ 8)⁻¹ * x ^ 4 * (1 * x⁻¹) := by positivity
    calc (|p.L₁| * (Θ * (p.a ^ 8)⁻¹ * x ^ 4)) * (1 * x⁻¹)
        = |p.L₁| * (Θ * (p.a ^ 8)⁻¹ * x ^ 4 * (1 * x⁻¹)) := by ring
      _ ≤ (κ * p.a ^ 8) * (Θ * (p.a ^ 8)⁻¹ * x ^ 4 * (1 * x⁻¹)) := mul_le_mul_of_nonneg_right h1 h2
      _ = κ * Θ * x ^ 3 := by field_simp
      _ ≤ κ * Θ * x := by
          have : x ^ 3 ≤ x := by
            have hx1 : x ≤ 1 := hx.2.trans (by norm_num)
            nlinarith [pow_pos hx0 2, mul_pos hx0 hx0]
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ M * x := by
          rw [hM]; nlinarith [mul_nonneg hκ hx0.le]
  have wlarge : ∀ p, H p → ∀ x ∈ Ici (1 / 2 : ℝ),
      (|p.L₁| * 1) * (|(1 : ℝ)| * x ^ (-1 : ℝ)) ≤ pw M (-1) 0 x := by
    intro p hp x hx
    have hx' : (1 / 2 : ℝ) ≤ x := hx
    have hx0 : 0 < x := by linarith
    have ha := hp.1.2.1
    have ha1 := hp.1.2.2.1
    have h1 : |p.L₁| ≤ κ := hp.2.trans (by
      have : p.a ^ 8 ≤ 1 := pow_le_one₀ ha.le ha1
      nlinarith)
    refine le_trans ?_ (pw_ge_half hM0 hx')
    rw [abs_one, Real.rpow_neg_one]
    have : x⁻¹ ≤ 2 := by rw [inv_le_comm₀ hx0 (by norm_num)]; linarith
    calc (|p.L₁| * 1) * (1 * x⁻¹) = |p.L₁| * x⁻¹ := by ring
      _ ≤ κ * 2 := mul_le_mul h1 this (inv_nonneg.mpr hx0.le) hκ
      _ ≤ M / 2 := by rw [hM]; nlinarith [mul_nonneg hκ hΘ]
  -- the target function on `Ioi s`
  have eq_small : ∀ p, H p → EqOn (fun x => (p.L₁ * p.L (phiKill p.a ((tau0 (x - p.s) : ℂ) * Complex.I))) *
      (1 * (x - p.s) ^ (-1 : ℝ))) (fun x => p.L₁ * p.L (phiKill p.a ((tau0 (x - p.s) : ℂ) * Complex.I)) / (x - p.s))
      (Ioi p.s) := by
    intro p hp x hx
    have : 0 < x - p.s := sub_pos.mpr hx
    simp only [Real.rpow_neg_one, one_mul]
    rw [div_eq_mul_inv]
  have eq_large : ∀ p, H p → EqOn (fun x => (p.L₁ * (p.L 1 + (-1) * p.L (1 - phiKill p.a ((tau0 (x - p.s) : ℂ) * Complex.I)))) *
      (1 * (x - p.s) ^ (-1 : ℝ))) (fun x => p.L₁ * p.L (phiKill p.a ((tau0 (x - p.s) : ℂ) * Complex.I)) / (x - p.s))
      (Ioi p.s) := by
    intro p hp x hx
    simp only [Real.rpow_neg_one, one_mul, map_sub]
    rw [div_eq_mul_inv]; ring
  -- small side
  have s1 := (hsm.mono_hyp hHN).smul (fun p => p.L₁)
  have s2 := s1.mul (rps.mono_set (fun p hp x hx => (hx.1 : p.x₀ ≤ x)))
  have s3 := (s2.of_le (w' := fun _ => pw M (-1) 0) (fun p hp x hx => wsmall p hp x hx)).congr
    (U := fun p => Ioi p.s) (fun _ _ => isOpen_Ioi)
    (fun p hp x hx => hsU p hp x hx.1) eq_small
  -- large side
  have l1 := hlg.mono_hyp hHN
  have l2 : USym H (fun _ => Ici (1 / 2 : ℝ)) (fun _ _ => 1)
      (fun p x => p.L 1 + (-1) * p.L (1 - phiKill p.a ((tau0 (x - p.s) : ℂ) * Complex.I))) := by
    have c1 := (USym.const (H := H) (S := fun _ => Ici (1 / 2 : ℝ)) (fun p _ x hx => by
      have : (1 / 2 : ℝ) ≤ x := hx
      linarith) (fun p => p.L 1)).of_le (w' := fun _ _ => 1) (fun p hp x hx => by
        have := hp.1.1 1
        simpa using this)
    have c2 := (l1.smul (fun _ => (-1 : ℝ))).of_le (w' := fun _ _ => 1) (fun p hp x hx => by simp)
    exact c1.add c2
  have l3 := (l2.smul (fun p => p.L₁)).mul (rps.mono_set (fun p hp x hx => by
    have : (1 / 2 : ℝ) ≤ x := hx
    have := hp.1.2.2.2.2.1
    exact (by linarith : p.x₀ ≤ x)))
  have l4 := (l3.of_le (w' := fun _ => pw M (-1) 0) (fun p hp x hx => wlarge p hp x hx)).congr
    (U := fun p => Ioi p.s) (fun _ _ => isOpen_Ioi)
    (fun p hp x hx => by
      have : (1 / 2 : ℝ) ≤ x := hx
      have := NHyp.s_le hp.1
      show p.s < x
      linarith [(abs_le.mp this).2]) eq_large
  exact (s3.union l4).mono_set (fun p hp x hx => by
    rcases le_or_gt x (1 / 2) with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr h.le)

/-- info: 'FormalResearch.SignUncertainty.FctSym.pieceN_usym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pieceN_usym

end FormalResearch.SignUncertainty.FctSym
