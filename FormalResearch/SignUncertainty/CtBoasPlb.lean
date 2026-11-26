module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasHankelCoeff
public import FormalResearch.SignUncertainty.CtBoasStrip

/-!
# `ct:boas` Step 4: the choice of `σ` and the abstract `ct:P-lb`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:boas` Step 4 (the display for `σ`, `ct:csigma-lb`) and
`ct:P-lb`.  With `Δ_{3/2} = m(3τ₀/2) - m(τ₀)`, `L₀ = m(τ₀)`, `N² = W²c²τ₀²` and

`σ = min(Δ_{3/2}/(4cW²), N²/(1200 c L₀), τ₀/40, 1/4)`,

* `sigma_choice_props`: `0 < σ ≤ min(τ₀/4, 1/4)`, `W²c²σ²/2 ≤ cσΔ_{3/2}/8`, `cσΔ_{3/2} ≥ 40 log c` (under the four
  regime inequalities (i)-(iv) of the paper), and `W²c²σ²/2 + cσL₀ + cπ²σ³/20 ≤ N²/500` (from `hankelEdgeM_lower`: `m(t) ≥ (3/20) min(t², 1)`);
* `hankel_P_lb`: the Fejér lower bound `ct:P-lb` for the Gaussian-windowed Hankel density, with error
  `n ∫g₋ + (2/n) ∫|g| + 6 n M[f] c^{-20}(1 + (√(2π)W)^{-1})`.

The regime inequalities (i)-(iv) and `N²` large are hypotheses here; checking them in the paper's adaptive blocks is Step 3.
**Proved**, unconditional (`c > 3/2`, `ε = ±1`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtBoasWindow

/-- Lower bound for the edge phase `m`: `m(t) ≥ (3/20) min(t², 1)` for `t > 0` (mean value theorem on `[t/2, t]`
with `m'(ξ) ≥ π²ξ/(6 + π²ξ²)`, and monotonicity of `m`). -/
theorem hankelEdgeM_lower {t : ℝ} (ht : 0 < t) : (3 / 20) * min (t ^ 2) 1 ≤ hankelEdgeM t := by
  have hπ2 : 9 < π ^ 2 := by nlinarith [Real.pi_gt_three]
  have key : ∀ u : ℝ, 0 < u → u ≤ 1 → (3 / 20) * u ^ 2 ≤ hankelEdgeM u := by
    intro u hu hu1
    have hlt : u / 2 < u := by linarith
    obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope hankelEdgeM hankelEdgeM' hlt
      (hankelEdgeM_continuousOn.mono (fun x hx => le_trans (by linarith) hx.1))
      (fun x hx => hankelEdgeM_hasDerivAt (lt_trans (by linarith) hx.1))
    have hξ0 : 0 < ξ := lt_trans (by linarith) hξ.1
    have hd : hankelEdgeM u - hankelEdgeM (u / 2) = hankelEdgeM' ξ * (u / 2) := by
      have : u - u / 2 = u / 2 := by ring
      rw [this] at hξe
      field_simp at hξe ⊢
      linarith
    have hm' : π ^ 2 * (u / 2) / (6 + π ^ 2) ≤ hankelEdgeM' ξ := by
      refine le_trans ?_ (hankelEdgeM'_ge hξ0).2
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : ξ ^ 2 ≤ 1 := by nlinarith [hξ.2]
      have ha : (u / 2) * (6 + π ^ 2 * ξ ^ 2) ≤ (u / 2) * (6 + π ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg π)]) (by positivity)
      have hb : (u / 2) * (6 + π ^ 2) ≤ ξ * (6 + π ^ 2) :=
        mul_le_mul_of_nonneg_right hξ.1.le (by positivity)
      nlinarith [ha, hb]
    have hm0 := hankelEdgeM_nonneg (by linarith : 0 ≤ u / 2)
    have h3 : π ^ 2 * (u / 2) / (6 + π ^ 2) * (u / 2) ≤ hankelEdgeM' ξ * (u / 2) :=
      mul_le_mul_of_nonneg_right hm' (by positivity)
    have h4 : (3 / 20) * u ^ 2 ≤ π ^ 2 * (u / 2) / (6 + π ^ 2) * (u / 2) := by
      have e : π ^ 2 * (u / 2) / (6 + π ^ 2) * (u / 2) = π ^ 2 * u ^ 2 / (4 * (6 + π ^ 2)) := by
        field_simp; ring
      rw [e, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg u, mul_pos hu hu, hπ2]
    linarith
  rcases le_or_gt t 1 with h | h
  · rw [min_eq_left (by nlinarith)]; exact key t ht h
  · rw [min_eq_right (by nlinarith)]
    have := key 1 one_pos le_rfl
    have hmono := hankelEdgeM_strictMonoOn.monotoneOn (Set.mem_Ici.2 (by norm_num : (0 : ℝ) ≤ 1))
      (Set.mem_Ici.2 ht.le) h.le
    linarith

/-- The choice of `σ` of Step 4 and its properties (`ct:csigma-lb` and the smallness of `Q`). -/
theorem sigma_choice_props {c W τ0 : ℝ} (hc : 1 < c) (hW : 0 < W) (hτ0 : 0 < τ0)
    (hR1 : 40 * Real.log c ≤ (hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0) ^ 2 / (4 * W ^ 2))
    (hR2 : 40 * Real.log c ≤ W ^ 2 * c ^ 2 * τ0 ^ 2 * (hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0) /
      (1200 * hankelEdgeM τ0))
    (hR3 : 40 * Real.log c ≤ c * τ0 * (hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0) / 40)
    (hR4 : 40 * Real.log c ≤ c * (hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0) / 4) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ τ0 / 4 ∧ σ ≤ 1 / 4 ∧
      W ^ 2 * c ^ 2 * σ ^ 2 / 2 ≤ c * σ * (hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0) / 8 ∧
      40 * Real.log c ≤ c * σ * (hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0) ∧
      W ^ 2 * c ^ 2 * σ ^ 2 / 2 + c * σ * hankelEdgeM τ0 + c * π ^ 2 * σ ^ 3 / 20 ≤
        W ^ 2 * c ^ 2 * τ0 ^ 2 / 500 := by
  have hc0 : 0 < c := by linarith
  have hπ2 : π ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  set L0 : ℝ := hankelEdgeM τ0 with hL0
  set Δ : ℝ := hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0 with hΔ
  have hL0p : 0 < L0 := lt_of_lt_of_le (mul_pos (by norm_num) (lt_min (pow_pos hτ0 2) one_pos)) (hankelEdgeM_lower hτ0)
  have hΔp : 0 < Δ := by
    have := hankelEdgeM_strictMonoOn (Set.mem_Ici.2 hτ0.le) (Set.mem_Ici.2 (by linarith : (0 : ℝ) ≤ 3 * τ0 / 2))
      (by linarith : τ0 < 3 * τ0 / 2)
    rw [hΔ]; linarith
  set N2 : ℝ := W ^ 2 * c ^ 2 * τ0 ^ 2 with hN2
  have hN2p : 0 < N2 := by positivity
  set σ : ℝ := min (min (Δ / (4 * c * W ^ 2)) (N2 / (1200 * c * L0))) (min (τ0 / 40) (1 / 4)) with hσ
  have hσ1 : σ ≤ Δ / (4 * c * W ^ 2) := (min_le_left _ _).trans (min_le_left _ _)
  have hσ2 : σ ≤ N2 / (1200 * c * L0) := (min_le_left _ _).trans (min_le_right _ _)
  have hσ3 : σ ≤ τ0 / 40 := (min_le_right _ _).trans (min_le_left _ _)
  have hσ4 : σ ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hσp : 0 < σ := lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by norm_num))
  refine ⟨σ, hσp, by linarith, hσ4, ?_, ?_, ?_⟩
  · -- `hA`
    have : σ * (4 * c * W ^ 2) ≤ Δ := by rwa [le_div_iff₀ (by positivity)] at hσ1
    nlinarith [mul_nonneg (mul_nonneg hc0.le hσp.le) (sq_nonneg W), mul_pos hc0 hσp]
  · -- `40 log c ≤ cσΔ`
    have h1 : 40 * Real.log c ≤ c * σ * Δ := by
      rcases min_cases (min (Δ / (4 * c * W ^ 2)) (N2 / (1200 * c * L0))) (min (τ0 / 40) (1 / 4)) with ⟨e, _⟩ | ⟨e, _⟩
      · rcases min_cases (Δ / (4 * c * W ^ 2)) (N2 / (1200 * c * L0)) with ⟨e2, _⟩ | ⟨e2, _⟩
        · have : σ = Δ / (4 * c * W ^ 2) := by rw [hσ, e, e2]
          rw [this]
          have : c * (Δ / (4 * c * W ^ 2)) * Δ = Δ ^ 2 / (4 * W ^ 2) := by field_simp
          rw [this]; exact hR1
        · have : σ = N2 / (1200 * c * L0) := by rw [hσ, e, e2]
          rw [this]
          have : c * (N2 / (1200 * c * L0)) * Δ = N2 * Δ / (1200 * L0) := by field_simp
          rw [this]; exact hR2
      · rcases min_cases (τ0 / 40) (1 / 4) with ⟨e2, _⟩ | ⟨e2, _⟩
        · have : σ = τ0 / 40 := by rw [hσ, e, e2]
          rw [this]
          have : c * (τ0 / 40) * Δ = c * τ0 * Δ / 40 := by ring
          rw [this]; exact hR3
        · have : σ = 1 / 4 := by rw [hσ, e, e2]
          rw [this]
          have : c * (1 / 4) * Δ = c * Δ / 4 := by ring
          rw [this]; exact hR4
    exact h1
  · -- smallness of `Q`
    have hs2 : σ * (1200 * c * L0) ≤ N2 := by rwa [le_div_iff₀ (by positivity)] at hσ2
    have hA1 : W ^ 2 * c ^ 2 * σ ^ 2 / 2 ≤ N2 / 3200 := by
      have : σ ^ 2 ≤ (τ0 / 40) ^ 2 := pow_le_pow_left₀ hσp.le hσ3 2
      have h := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ W ^ 2 * c ^ 2)
      rw [hN2]; nlinarith [h]
    have hA2 : c * σ * L0 ≤ N2 / 1200 := by nlinarith [hs2]
    have hsq : σ ^ 2 ≤ min (τ0 ^ 2) 1 / 16 := by
      rcases le_total (τ0 ^ 2) 1 with h | h
      · rw [min_eq_left h]
        have : σ ^ 2 ≤ (τ0 / 4) ^ 2 := pow_le_pow_left₀ hσp.le (by linarith) 2
        nlinarith
      · rw [min_eq_right h]
        have : σ ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ hσp.le hσ4 2
        nlinarith
    have hL := hankelEdgeM_lower hτ0
    have hmin0 : 0 ≤ min (τ0 ^ 2) 1 := le_min (sq_nonneg _) zero_le_one
    have hA3 : c * π ^ 2 * σ ^ 3 / 20 ≤ c * σ * L0 := by
      have h1 : π ^ 2 * σ ^ 2 / 20 ≤ L0 := by nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg π)]
      have h2 := mul_le_mul_of_nonneg_left h1 (mul_pos hc0 hσp).le
      nlinarith [h2]
    linarith [hA1, hA2, hA3]

/-- **`ct:boas` `ct:P-lb`** (Fejér lower bound for the Gaussian-windowed Hankel density, abstract regime): under the
regime inequalities (i)-(iv) of Step 4, `(3cτ₀/2π) e^{-W²c²τ₀²/9} ≤ c^{-20}` and `n ≥ 2`,
`∫ g (1 + 2cos(cτ₀L + φ)) ≥ -n ∫g₋ - (2/n) ∫|g| - 6 n M[f] c^{-20} (1 + √(π/(2π²W²)))`. -/
theorem hankel_P_lb {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {W : ℝ} (hW : 0 < W) {τ0 : ℝ} (hτ0 : 0 < τ0)
    (hR1 : 40 * Real.log c ≤ (hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0) ^ 2 / (4 * W ^ 2))
    (hR2 : 40 * Real.log c ≤ W ^ 2 * c ^ 2 * τ0 ^ 2 * (hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0) /
      (1200 * hankelEdgeM τ0))
    (hR3 : 40 * Real.log c ≤ c * τ0 * (hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0) / 40)
    (hR4 : 40 * Real.log c ≤ c * (hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0) / 4)
    (hBig : 3 * c * τ0 / (2 * π) * Real.exp (-(W ^ 2 * c ^ 2 * τ0 ^ 2 / 9)) ≤ ((c ^ 20)⁻¹ : ℝ))
    {n : ℕ} (hn : 2 ≤ n) (φ : ℝ) :
    -((n : ℝ) * ∫ x, max (-(gaussK W (x - hankelEdgeM τ0) * hankelHL c f x)) 0) -
        (2 / n) * (∫ x, |gaussK W (x - hankelEdgeM τ0) * hankelHL c f x|) -
        6 * n * hankelMass c f * ((c ^ 20)⁻¹ * (1 + √(π / (2 * π ^ 2 * W ^ 2)))) ≤
      ∫ x, gaussK W (x - hankelEdgeM τ0) * hankelHL c f x * (1 + 2 * Real.cos (c * τ0 * x + φ)) := by
  have hc1 : 1 < c := by linarith
  have hc0 : 0 < c := by linarith
  obtain ⟨σ, hσ0, hσ, hσ4, hA, h40, hQ⟩ := sigma_choice_props hc1 hW hτ0 hR1 hR2 hR3 hR4
  have hF := hankel_window_fejer hc hf hε hW hτ0 hσ0 hσ hσ4 rfl hA hn φ
  refine le_trans ?_ hF
  set Δ : ℝ := hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0 with hΔ
  have hm := hankelMass_nonneg hc0 f
  have hexpA : Real.exp (-(c * σ * Δ / 2)) ≤ (c ^ 20)⁻¹ := by
    have : -(c * σ * Δ / 2) ≤ -(20 * Real.log c) := by linarith
    refine (Real.exp_le_exp.2 this).trans (le_of_eq ?_)
    rw [Real.exp_neg, show (20 * Real.log c) = ((20 : ℕ) : ℝ) * Real.log c by norm_num,
      Real.exp_nat_mul, Real.exp_log hc0]
  have hexpB : Real.exp (-(W ^ 2 * c ^ 2 * τ0 ^ 2 / 8 -
      (W ^ 2 * c ^ 2 * σ ^ 2 / 2 + c * σ * hankelEdgeM τ0 + c * π ^ 2 * σ ^ 3 / 20))) ≤
      Real.exp (-(W ^ 2 * c ^ 2 * τ0 ^ 2 / 9)) := by
    apply Real.exp_le_exp.2
    have hN : 0 ≤ W ^ 2 * c ^ 2 * τ0 ^ 2 := by positivity
    linarith
  have hsq : 0 ≤ √(π / (2 * π ^ 2 * W ^ 2)) := Real.sqrt_nonneg _
  have hB1 : 3 * c * τ0 / (2 * π) * Real.exp (-(W ^ 2 * c ^ 2 * τ0 ^ 2 / 8 -
      (W ^ 2 * c ^ 2 * σ ^ 2 / 2 + c * σ * hankelEdgeM τ0 + c * π ^ 2 * σ ^ 3 / 20))) ≤ (c ^ 20)⁻¹ :=
    (mul_le_mul_of_nonneg_left hexpB (by positivity)).trans hBig
  have hsum : 3 * c * τ0 / (2 * π) * Real.exp (-(W ^ 2 * c ^ 2 * τ0 ^ 2 / 8 -
      (W ^ 2 * c ^ 2 * σ ^ 2 / 2 + c * σ * hankelEdgeM τ0 + c * π ^ 2 * σ ^ 3 / 20))) +
      Real.exp (-(c * σ * Δ / 2)) * √(π / (2 * π ^ 2 * W ^ 2)) ≤
      (c ^ 20)⁻¹ * (1 + √(π / (2 * π ^ 2 * W ^ 2))) := by
    have := mul_le_mul_of_nonneg_right hexpA hsq
    nlinarith [hB1, this]
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 3 * hankelMass c f)
  nlinarith [mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 2 * (n : ℝ))]

/-- info: 'FormalResearch.SignUncertainty.hankelEdgeM_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelEdgeM_lower

/-- info: 'FormalResearch.SignUncertainty.sigma_choice_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sigma_choice_props

/-- info: 'FormalResearch.SignUncertainty.hankel_P_lb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_P_lb

end FormalResearch.SignUncertainty
