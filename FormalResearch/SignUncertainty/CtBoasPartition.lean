/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasBlocks
public import FormalResearch.SignUncertainty.CtBoasMBounds
public import FormalResearch.SignUncertainty.CtOuterBandCut

/-!
# Telescoping smooth partition of unity and `τ₀`-Harnack window (`ct:boas` Steps 3–4)

Partition geometry for `ct:boas` (`CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Steps 3–4):

* `tau0_block_window`: `0.9 τ₀(L_j) ≤ τ₀(L) ≤ 1.1 τ₀(L_j)` and `L - L_j ≤ (2/5) Δ_{3/2}(τ₀(L_j))` whenever
  `|L - L_j| ≤ min L_j 1 / 100`.
* `smoothStep`, `partGrid`, `partCount`, `partChi`, `part_facts`: explicit geometric-linear telescoping
  smooth partition of unity on `[A, B]` (`0 < A ≤ 1 ≤ B`) with `O(log(1/A) + B)` blocks,
  `0 ≤ χ_j ≤ 1`, `supp χ_j ⊆ [L_j - ℓ_j / 150, L_j + ℓ_j / 150]`, and `O(ℓ_j^{-r})` derivatives (`r = 1, 2`).

Class: proved, unconditional.
-/

@[expose] public section

open Set Filter Topology
open scoped Real ContDiff

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### `τ₀`-Harnack ratio `.9 ≤ τ₀(L)/τ₀(L_j) ≤ 1.1` on narrow blocks -/

/-- If `L, L_j > 0` satisfy `|L - L_j| ≤ min L_j 1 / 100`, then
`0.9 * τ₀(L_j) ≤ τ₀(L) ≤ 1.1 * τ₀(L_j)` and `L - L_j ≤ (2 / 5) * (m(3 τ₀(L_j) / 2) - m(τ₀(L_j)))`. -/
theorem tau0_block_window {L L_j : ℝ} (hL : 0 < L) (hLj : 0 < L_j)
    (hw : |L - L_j| ≤ min L_j 1 / 100) :
    0.9 * tau0 L_j ≤ tau0 L ∧ tau0 L ≤ 1.1 * tau0 L_j ∧
      L - L_j ≤ (2 / 5) * (hankelEdgeM (3 * tau0 L_j / 2) - hankelEdgeM (tau0 L_j)) := by
  set τ := tau0 L_j with hτdef
  have hτ := tau0_pos hLj
  have hτL := tau0_pos hL
  have hm : hankelEdgeM τ = L_j := hankelEdgeM_tau0 hLj
  have hmL : hankelEdgeM (tau0 L) = L := hankelEdgeM_tau0 hL
  have hdelta := hankelEdge_delta32_ge_L hτ
  rw [hm] at hdelta
  refine ⟨?_, ?_, ?_⟩
  · by_contra hcon
    rw [not_le] at hcon
    have hlt : 0.9 * τ < τ := by linarith
    obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope hankelEdgeM hankelEdgeM' hlt
      (hankelEdgeM_continuousOn.mono (fun x hx => le_trans (mul_pos (by norm_num) hτ).le hx.1))
      (fun x hx => hankelEdgeM_hasDerivAt (lt_trans (mul_pos (by norm_num) hτ) hx.1))
    have hξ0 : 0 < ξ := lt_trans (mul_pos (by norm_num) hτ) hξ.1
    have hq := hankelEdgeM'_ge_simple hξ0
    have hq2 : (0.9 * τ) / (1 + τ ^ 2) ≤ ξ / (1 + ξ ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg hτ.le (sub_nonneg.2 hξ.2.le), hξ.1, hξ.2]
    have hdiff : hankelEdgeM τ - hankelEdgeM (0.9 * τ) = hankelEdgeM' ξ * (0.1 * τ) := by
      have hsub : τ - 0.9 * τ = 0.1 * τ := by ring
      rw [hξd, hsub, div_mul_cancel₀ _ (by positivity)]
    have hmono : hankelEdgeM (tau0 L) ≤ hankelEdgeM (0.9 * τ) :=
      hankelEdgeM_strictMonoOn.monotoneOn (mem_Ici.2 hτL.le) (mem_Ici.2 (by linarith)) hcon.le
    rw [hmL] at hmono
    have hΔ : 0.09 * τ ^ 2 / (1 + τ ^ 2) ≤ L_j - L := by
      have : (0.9 * τ) / (1 + τ ^ 2) * (0.1 * τ) ≤ hankelEdgeM' ξ * (0.1 * τ) :=
        mul_le_mul_of_nonneg_right (hq2.trans hq) (by positivity)
      have e : (0.9 * τ) / (1 + τ ^ 2) * (0.1 * τ) = 0.09 * τ ^ 2 / (1 + τ ^ 2) := by field_simp; ring
      linarith
    have h12 : 12 * L_j ≤ π ^ 2 * τ ^ 2 := by
      have := hankelEdgeM_le_sq hτ.le; rw [hm] at this; linarith
    have hπ : π ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have h12' : 1.2 * L_j ≤ τ ^ 2 := by nlinarith [sq_nonneg τ]
    have hle := (abs_le.1 hw).1
    rw [div_le_iff₀ (by positivity)] at hΔ
    rcases le_total L_j 1 with h1 | h1
    · rw [min_eq_left h1] at hle
      nlinarith [sq_nonneg τ, h12']
    · rw [min_eq_right h1] at hle
      have h12'' : 1.2 ≤ τ ^ 2 := by linarith
      nlinarith [sq_nonneg τ, h12'']
  · by_contra hcon
    rw [not_le] at hcon
    have hlt : τ < 1.1 * τ := by linarith
    obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope hankelEdgeM hankelEdgeM' hlt
      (hankelEdgeM_continuousOn.mono (fun x hx => le_trans hτ.le hx.1))
      (fun x hx => hankelEdgeM_hasDerivAt (lt_trans hτ hx.1))
    have hξ0 : 0 < ξ := lt_trans hτ hξ.1
    have hq := hankelEdgeM'_ge_simple hξ0
    have hq2 : τ / (1 + 1.21 * τ ^ 2) ≤ ξ / (1 + ξ ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hξ2 : ξ ≤ 1.1 * τ := hξ.2.le
      nlinarith [mul_nonneg hτ.le (sub_nonneg.2 hξ2), mul_pos hτ hξ0, hξ.1]
    have hdiff : hankelEdgeM (1.1 * τ) - hankelEdgeM τ = hankelEdgeM' ξ * (0.1 * τ) := by
      have hsub : 1.1 * τ - τ = 0.1 * τ := by ring
      rw [hξd, hsub, div_mul_cancel₀ _ (by positivity)]
    have hmono : hankelEdgeM (1.1 * τ) ≤ hankelEdgeM (tau0 L) :=
      hankelEdgeM_strictMonoOn.monotoneOn (mem_Ici.2 (by linarith)) (mem_Ici.2 hτL.le) hcon.le
    rw [hmL] at hmono
    have hΔ : 0.1 * τ ^ 2 / (1 + 1.21 * τ ^ 2) ≤ L - L_j := by
      have : τ / (1 + 1.21 * τ ^ 2) * (0.1 * τ) ≤ hankelEdgeM' ξ * (0.1 * τ) :=
        mul_le_mul_of_nonneg_right (hq2.trans hq) (by positivity)
      have e : τ / (1 + 1.21 * τ ^ 2) * (0.1 * τ) = 0.1 * τ ^ 2 / (1 + 1.21 * τ ^ 2) := by field_simp
      linarith
    have h12 : 12 * L_j ≤ π ^ 2 * τ ^ 2 := by
      have := hankelEdgeM_le_sq hτ.le; rw [hm] at this; linarith
    have hπ : π ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have h12' : 1.2 * L_j ≤ τ ^ 2 := by nlinarith [sq_nonneg τ]
    have hle := (abs_le.1 hw).2
    rw [div_le_iff₀ (by positivity)] at hΔ
    rcases le_total L_j 1 with h1 | h1
    · rw [min_eq_left h1] at hle
      nlinarith [sq_nonneg τ]
    · rw [min_eq_right h1] at hle
      have h12'' : 1.2 ≤ τ ^ 2 := by linarith
      nlinarith [sq_nonneg τ, h12'']
  · have h1 := (abs_le.1 hw).2
    have h2 : (0 : ℝ) ≤ min L_j 1 := le_min hLj.le zero_le_one
    linarith [hdelta.2]

/-! ### Telescoping smooth step partition of unity on `[A, B]` -/

/-- Smooth monotone step from `0` (`L ≤ a`) to `1` (`L ≥ b`) for `a < b`. -/
noncomputable def smoothStep (a b L : ℝ) : ℝ :=
  Real.smoothTransition ((L - a) / (b - a))

lemma contDiff_smoothStep (a b : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (smoothStep a b) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

lemma smoothStep_nonneg (a b L : ℝ) : 0 ≤ smoothStep a b L :=
  Real.smoothTransition.nonneg _

lemma smoothStep_le_one (a b L : ℝ) : smoothStep a b L ≤ 1 :=
  Real.smoothTransition.le_one _

lemma smoothStep_zero_of_le {a b L : ℝ} (hab : a < b) (hL : L ≤ a) : smoothStep a b L = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_pos.2 hab).le)

lemma smoothStep_one_of_le {a b L : ℝ} (hab : a < b) (hL : b ≤ L) : smoothStep a b L = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (sub_pos.2 hab)).2 (by linarith))

lemma exists_smoothStep_deriv_bounds : ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧
    ∀ {a b : ℝ}, a < b →
      (∀ L, |deriv (smoothStep a b) L| ≤ K1 / (b - a)) ∧
      (∀ L₁ L₂, |deriv (smoothStep a b) L₁ - deriv (smoothStep a b) L₂| ≤
        K2 / (b - a) ^ 2 * |L₁ - L₂|) := by
  obtain ⟨K1, hK1, hb1⟩ := CtOsc.bdd_deriv_zeta
  obtain ⟨K2, hK2, hb2⟩ := CtOsc.bdd_deriv_deriv_zeta
  refine ⟨K1, K2, hK1, hK2, fun {a b} hab => ?_⟩
  have hw : 0 < b - a := sub_pos.2 hab
  have hd : ∀ L : ℝ, deriv (smoothStep a b) L =
      (b - a)⁻¹ * deriv Real.smoothTransition ((L - a) / (b - a)) := fun L => by
    have h1 : HasDerivAt (fun x => (x - a) / (b - a)) (b - a)⁻¹ L := by
      simpa using ((hasDerivAt_id L).sub_const a).div_const (b - a)
    have h2 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition ((L - a) / (b - a))) ((L - a) / (b - a)) :=
      ((Real.smoothTransition.contDiffAt (x := (L - a) / (b - a)) (n := (1 : ℕ∞))).differentiableAt
        one_ne_zero).hasDerivAt
    have h3 : HasDerivAt (smoothStep a b)
        (deriv Real.smoothTransition ((L - a) / (b - a)) * (b - a)⁻¹) L := h2.comp L h1
    rw [h3.deriv, mul_comm]
  refine ⟨fun L => ?_, fun L₁ L₂ => ?_⟩
  · rw [hd L, abs_mul, abs_of_pos (inv_pos.2 hw)]
    calc (b - a)⁻¹ * |deriv Real.smoothTransition ((L - a) / (b - a))|
        ≤ (b - a)⁻¹ * K1 := mul_le_mul_of_nonneg_left (hb1 _) (inv_pos.2 hw).le
      _ = K1 / (b - a) := by rw [div_eq_inv_mul]
  · rw [hd L₁, hd L₂, ← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hw)]
    have hdiff_d : Differentiable ℝ (deriv Real.smoothTransition) :=
      CtOsc.contDiff_deriv_zeta.differentiable (by simp)
    have hmv := convex_univ.norm_image_sub_le_of_norm_deriv_le (f := deriv Real.smoothTransition)
      (fun t _ => hdiff_d t)
      (fun t _ => by rw [Real.norm_eq_abs]; exact hb2 t)
      (mem_univ ((L₂ - a) / (b - a))) (mem_univ ((L₁ - a) / (b - a)))
    rw [Real.norm_eq_abs] at hmv
    rw [Real.norm_eq_abs] at hmv
    have hsub : |(L₁ - a) / (b - a) - (L₂ - a) / (b - a)| = |L₁ - L₂| / (b - a) := by
      rw [show (L₁ - a) / (b - a) - (L₂ - a) / (b - a) = (L₁ - L₂) / (b - a) by ring,
        abs_div, abs_of_pos hw]
    rw [hsub] at hmv
    calc (b - a)⁻¹ * |deriv Real.smoothTransition ((L₁ - a) / (b - a)) -
            deriv Real.smoothTransition ((L₂ - a) / (b - a))|
        ≤ (b - a)⁻¹ * (K2 * (|L₁ - L₂| / (b - a))) := mul_le_mul_of_nonneg_left hmv (inv_pos.2 hw).le
      _ = K2 / (b - a) ^ 2 * |L₁ - L₂| := by field_simp

/-- Geometric-linear knot count for `A / 4 * (201/200)^K_lo ≥ 1`. -/
noncomputable def partKloR (A : ℝ) : ℕ :=
  ⌈Real.log (4 / A) / Real.log (201 / 200)⌉₊

noncomputable def partGrid (A : ℝ) (k : ℕ) : ℝ :=
  if k ≤ partKloR A then (A / 4) * (201 / 200 : ℝ) ^ k
  else (A / 4) * (201 / 200 : ℝ) ^ partKloR A + ((k - partKloR A : ℕ) : ℝ) / 200

/-- Partition count `N`: `partGrid A N ≥ B + 2` cleanly for `0 < A ≤ 1`, `1 ≤ B`. -/
noncomputable def partCount (A B : ℝ) : ℕ :=
  partKloR A + Nat.ceil (200 * (B + 2)) + 2

/-- Partition function `χ_j(L) = S_{j-1}(L) - S_j(L)`. -/
noncomputable def partChi (A : ℝ) (j : ℕ) (L : ℝ) : ℝ :=
  smoothStep (partGrid A j) (partGrid A (j + 1)) L -
    smoothStep (partGrid A (j + 1)) (partGrid A (j + 2)) L

lemma partKloR_ge {A : ℝ} (hA0 : 0 < A) (hA1 : A ≤ 1) :
    1 ≤ (A / 4) * (201 / 200 : ℝ) ^ partKloR A ∧
    (A / 4) * (201 / 200 : ℝ) ^ partKloR A ≤ 201 / 200 ∧
    1 ≤ partKloR A ∧
    (partKloR A : ℝ) ≤ 250 * Real.log (4 / A) + 1 := by
  have hr1 : (1 : ℝ) < 201 / 200 := by norm_num
  have hlogr : 0 < Real.log (201 / 200) := Real.log_pos hr1
  have hlogr_lb : 1 / 250 ≤ Real.log (201 / 200) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 201 / 200 by positivity)
    norm_num at h; linarith
  have h4A : 4 ≤ 4 / A := (le_div_iff₀ hA0).2 (by linarith)
  have hlog4A : 0 < Real.log (4 / A) := Real.log_pos (by linarith)
  have hceil_le : (partKloR A : ℝ) < Real.log (4 / A) / Real.log (201 / 200) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hle_ceil : Real.log (4 / A) / Real.log (201 / 200) ≤ (partKloR A : ℝ) :=
    Nat.le_ceil _
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : Real.log (4 / A) ≤ (partKloR A : ℝ) * Real.log (201 / 200) := by
      rwa [div_le_iff₀ hlogr] at hle_ceil
    have h2 : 4 / A ≤ (201 / 200 : ℝ) ^ partKloR A := by
      calc 4 / A = Real.exp (Real.log (4 / A)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp ((partKloR A : ℝ) * Real.log (201 / 200)) := Real.exp_le_exp.2 h1
        _ = (201 / 200 : ℝ) ^ partKloR A := by
            rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
    have h2' := mul_le_mul_of_nonneg_left h2 (show 0 ≤ A / 4 by positivity)
    rwa [show (A / 4) * (4 / A) = 1 by field_simp] at h2'
  · have hge1 : 1 ≤ partKloR A := Nat.ceil_pos.2 (div_pos hlog4A hlogr)
    have hlt : ((partKloR A - 1 : ℕ) : ℝ) < Real.log (4 / A) / Real.log (201 / 200) := by
      have hm1 : (partKloR A : ℝ) - 1 = ((partKloR A - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hge1]; simp
      linarith
    have h1 : ((partKloR A - 1 : ℕ) : ℝ) * Real.log (201 / 200) < Real.log (4 / A) := by
      rwa [lt_div_iff₀ hlogr] at hlt
    have h2 : (201 / 200 : ℝ) ^ (partKloR A - 1) < 4 / A := by
      calc (201 / 200 : ℝ) ^ (partKloR A - 1)
          = Real.exp (((partKloR A - 1 : ℕ) : ℝ) * Real.log (201 / 200)) := by
            rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
        _ < Real.exp (Real.log (4 / A)) := Real.exp_lt_exp.2 h1
        _ = 4 / A := Real.exp_log (by positivity)
    have hp : (201 / 200 : ℝ) ^ partKloR A = (201 / 200) * (201 / 200 : ℝ) ^ (partKloR A - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hge1, pow_succ']
    rw [hp]
    have hmul : (A / 4) * ((201 / 200) ^ (partKloR A - 1)) < 1 := by
      have := mul_lt_mul_of_pos_left h2 (show 0 < A / 4 by positivity)
      rwa [show (A / 4) * (4 / A) = 1 by field_simp] at this
    nlinarith
  · exact Nat.ceil_pos.2 (div_pos hlog4A hlogr)
  · have hdiv : Real.log (4 / A) / Real.log (201 / 200) ≤ 250 * Real.log (4 / A) := by
      rw [div_le_iff₀ hlogr]
      calc Real.log (4 / A) = 250 * Real.log (4 / A) * (1 / 250) := by ring
        _ ≤ 250 * Real.log (4 / A) * Real.log (201 / 200) :=
          mul_le_mul_of_nonneg_left hlogr_lb (by positivity)
    linarith

lemma partGrid_step {A : ℝ} (hA0 : 0 < A) (hA1 : A ≤ 1) (k : ℕ) :
    0 < partGrid A k ∧
    min (partGrid A k) 1 / 200 ≤ partGrid A (k + 1) - partGrid A k ∧
    partGrid A (k + 1) - partGrid A k ≤ min (partGrid A k) 1 / 199 := by
  have hklo := partKloR_ge hA0 hA1
  by_cases h : k < partKloR A
  · have hk1 : k + 1 ≤ partKloR A := h
    have hle : k ≤ partKloR A := h.le
    simp only [partGrid, hle, hk1, ↓reduceIte, pow_succ]
    have hxpos : 0 < (A / 4) * (201 / 200 : ℝ) ^ k := by positivity
    have hxlt : (A / 4) * (201 / 200 : ℝ) ^ k ≤ 1 := by
      have hpow : (201 / 200 : ℝ) ^ partKloR A = (201 / 200) ^ (partKloR A - k) * (201 / 200) ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hle]
      have hge : (201 / 200 : ℝ) ^ (partKloR A - k) ≥ 201 / 200 := by
        have hpos : 1 ≤ partKloR A - k := by omega
        calc (201 / 200 : ℝ) = (201 / 200) ^ 1 := (pow_one _).symm
          _ ≤ (201 / 200) ^ (partKloR A - k) := pow_le_pow_right₀ (by norm_num) hpos
      have hm := hklo.2.1
      rw [hpow] at hm
      have hmul := mul_le_mul_of_nonneg_right hge hxpos.le
      have hassoc : (201 / 200 : ℝ) ^ (partKloR A - k) * (A / 4 * (201 / 200) ^ k) =
          A / 4 * ((201 / 200 : ℝ) ^ (partKloR A - k) * (201 / 200) ^ k) := by ring
      rw [hassoc] at hmul
      exact le_of_mul_le_mul_left (by linarith [hmul, hm]) (by norm_num : (0 : ℝ) < 201 / 200)
    have heq : (A / 4) * ((201 / 200 : ℝ) ^ k * (201 / 200)) - (A / 4) * (201 / 200 : ℝ) ^ k =
        (A / 4) * (201 / 200 : ℝ) ^ k / 200 := by ring
    rw [heq, min_eq_left hxlt]
    exact ⟨hxpos, le_rfl, by nlinarith⟩
  · push Not at h
    unfold partGrid
    by_cases he : k = partKloR A
    · subst he
      have hk1 : ¬ (partKloR A + 1 ≤ partKloR A) := by omega
      simp only [le_rfl, ↓reduceIte, hk1, Nat.add_sub_cancel_left, Nat.cast_one]
      have hx1 : 1 ≤ (A / 4) * (201 / 200 : ℝ) ^ partKloR A := hklo.1
      have heq : ((A / 4) * (201 / 200 : ℝ) ^ partKloR A + 1 / 200) - (A / 4) * (201 / 200 : ℝ) ^ partKloR A = 1 / 200 := by ring
      rw [heq, min_eq_right hx1]
      exact ⟨by linarith, by norm_num, by norm_num⟩
    · have hk0 : ¬ (k ≤ partKloR A) := fun h1 => he (le_antisymm h1 h)
      have hk1 : ¬ (k + 1 ≤ partKloR A) := by omega
      simp only [hk0, ↓reduceIte, hk1]
      have hge1 : 1 ≤ (A / 4) * (201 / 200 : ℝ) ^ partKloR A + ((k - partKloR A : ℕ) : ℝ) / 200 := by
        have := hklo.1
        have hpos : (0 : ℝ) ≤ ((k - partKloR A : ℕ) : ℝ) / 200 := by positivity
        linarith
      have hsub : ((k + 1 - partKloR A : ℕ) : ℝ) - ((k - partKloR A : ℕ) : ℝ) = 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub h]; push_cast; ring
      have heq : ((A / 4) * (201 / 200 : ℝ) ^ partKloR A + ((k + 1 - partKloR A : ℕ) : ℝ) / 200) -
          ((A / 4) * (201 / 200 : ℝ) ^ partKloR A + ((k - partKloR A : ℕ) : ℝ) / 200) = 1 / 200 := by
        have : (((k + 1 - partKloR A : ℕ) : ℝ) / 200 - ((k - partKloR A : ℕ) : ℝ) / 200) = 1 / 200 := by
          rw [← sub_div, hsub]
        linarith
      rw [heq, min_eq_right hge1]
      exact ⟨by linarith, by norm_num, by norm_num⟩

/-- **Partition of unity facts on `[A, B]`**: `∑_{j < N} χ_j(L) = 1` on `[A, B]`, `0 ≤ χ_j ≤ 1`,
`supp(χ_j) ⊆ [L_j - min L_j 1 / 150, L_j + min L_j 1 / 150]` where `L_j = partGrid A (j + 1)`,
and `|χ_j'| ≤ C / min L_j 1`, `Lip(χ_j') ≤ C / (min L_j 1)²`. -/
theorem part_facts : ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧
    ∀ {A B : ℝ}, 0 < A → A ≤ 1 → 1 ≤ B →
      let N := partCount A B
      (N : ℝ) ≤ 250 * Real.log (4 / A) + 200 * B + 810 ∧
      (∀ L ∈ Icc A B, ∑ j ∈ Finset.range N, partChi A j L = 1) ∧
      ∀ j ∈ Finset.range N,
        let Lj := partGrid A (j + 1)
        let ℓj := min Lj 1
        A / 4 < Lj ∧ Lj ≤ B + 4 ∧ 0 < ℓj ∧
        (∀ L, 0 ≤ partChi A j L ∧ partChi A j L ≤ 1) ∧
        (∀ L, L ∉ Icc (Lj - ℓj / 150) (Lj + ℓj / 150) → partChi A j L = 0) ∧
        (∀ L, |deriv (partChi A j) L| ≤ K1 / ℓj) ∧
        (∀ L₁ L₂, |deriv (partChi A j) L₁ - deriv (partChi A j) L₂| ≤ K2 / ℓj ^ 2 * |L₁ - L₂|) := by
  obtain ⟨S1, S2, hS1, hS2, hstepD⟩ := exists_smoothStep_deriv_bounds
  refine ⟨810 * S1, 324000 * S2, by positivity, by positivity, ?_⟩
  intro A B hA0 hA1 hB1
  set N := partCount A B with hNdef
  have hklo := partKloR_ge hA0 hA1
  have hstep : ∀ k, 0 < partGrid A k ∧
      min (partGrid A k) 1 / 200 ≤ partGrid A (k + 1) - partGrid A k ∧
      partGrid A (k + 1) - partGrid A k ≤ min (partGrid A k) 1 / 199 := fun k => partGrid_step hA0 hA1 k
  have hx_mono : Monotone (partGrid A) := by
    refine monotone_nat_of_le_succ fun k => ?_
    have h1 := (hstep k).2.1
    have h2 : 0 ≤ min (partGrid A k) 1 / 200 := div_nonneg (le_min (hstep k).1.le zero_le_one) (by norm_num)
    linarith
  have hx0 : partGrid A 0 = A / 4 := by
    have hk0 : (0 : ℕ) ≤ partKloR A := Nat.zero_le _
    simp only [partGrid, hk0, ↓reduceIte, pow_zero, mul_one]
  have hx1 : partGrid A 1 ≤ A / 2 := by
    have h1 : (1 : ℕ) ≤ partKloR A := hklo.2.2.1
    simp only [partGrid, h1, ↓reduceIte, pow_one]; linarith
  have hxN : B + 2 ≤ partGrid A N := by
    have hne : ¬ (N ≤ partKloR A) := by unfold N partCount; omega
    simp only [partGrid, hne, ↓reduceIte]
    have hdiff : ((N - partKloR A : ℕ) : ℝ) ≥ 200 * (B + 2) := by
      have : Nat.ceil (200 * (B + 2)) ≤ N - partKloR A := by unfold N partCount; omega
      exact (Nat.le_ceil _).trans (by exact_mod_cast this)
    linarith [hklo.1]
  refine ⟨?_, ?_, ?_⟩
  · have hc_le : (Nat.ceil (200 * (B + 2)) : ℝ) < 200 * (B + 2) + 1 := Nat.ceil_lt_add_one (by positivity)
    unfold N partCount
    push_cast
    linarith [hklo.2.2.2]
  · intro L hL
    have hsum : ∀ m : ℕ, ∑ j ∈ Finset.range m, partChi A j L =
        smoothStep (partGrid A 0) (partGrid A 1) L -
        smoothStep (partGrid A m) (partGrid A (m + 1)) L := fun m => by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        unfold partChi; ring
    rw [hsum N]
    have h01 : partGrid A 0 < partGrid A 1 := by
      have hstep0 := (hstep 0).2.1
      have hmin : 0 < min (partGrid A 0) 1 / 200 := div_pos (lt_min (hstep 0).1 one_pos) (by norm_num)
      linarith
    have hNN : partGrid A N < partGrid A (N + 1) := by
      have hstepN := (hstep N).2.1
      have hmin : 0 < min (partGrid A N) 1 / 200 := div_pos (lt_min (hstep N).1 one_pos) (by norm_num)
      linarith
    rw [smoothStep_one_of_le h01 (by linarith [hL.1, hx1]),
        smoothStep_zero_of_le hNN (by linarith [hL.2, hxN])]
    ring
  · intro j hj
    have hjN : j + 1 ≤ N := Finset.mem_range.1 hj
    set Lj := partGrid A (j + 1) with hLj
    set ℓj := min Lj 1 with hℓj
    have hAj : A / 4 < Lj := by
      have h01 : partGrid A 0 < partGrid A 1 := by
        have := (hstep 0).2.1
        have := div_pos (lt_min (hstep 0).1 one_pos) (by norm_num : (0 : ℝ) < 200)
        linarith
      have h1j : partGrid A 1 ≤ Lj := hx_mono (by omega)
      linarith
    have hLj_le : Lj ≤ B + 4 := by
      have h1 : partGrid A (j + 1) ≤ partGrid A N := hx_mono hjN
      have hle : ¬ (N ≤ partKloR A) := by unfold N partCount; omega
      have hN_le : partGrid A N ≤ B + 4 := by
        simp only [partGrid, hle, ↓reduceIte]
        have hc : ((N - partKloR A : ℕ) : ℝ) ≤ 200 * (B + 2) + 3 := by
          have : N - partKloR A = Nat.ceil (200 * (B + 2)) + 2 := by unfold N partCount; omega
          rw [this]
          have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 200 * (B + 2) by positivity)
          push_cast; linarith
        nlinarith [hklo.2.1]
      linarith
    have hℓ0 : 0 < ℓj := lt_min (hstep (j + 1)).1 one_pos
    have hlt_j : partGrid A j < Lj := by
      have := (hstep j).2.1
      have := div_pos (lt_min (hstep j).1 one_pos) (by norm_num : (0 : ℝ) < 200)
      linarith
    have hlt_j1 : Lj < partGrid A (j + 2) := by
      have := (hstep (j + 1)).2.1; linarith [hℓ0]
    have hratio : ℓj / 2 ≤ min (partGrid A j) 1 := by
      have hxj := (hstep j).1
      have hw : Lj - partGrid A j ≤ min (partGrid A j) 1 / 199 := (hstep j).2.2
      have hle_j : Lj ≤ 2 * partGrid A j := by linarith [min_le_left (partGrid A j) 1]
      rcases le_total (partGrid A j) 1 with hj1 | hj1
      · rw [min_eq_left hj1]
        have : ℓj ≤ 2 * partGrid A j := (min_le_left _ _).trans hle_j
        linarith
      · rw [min_eq_right hj1]
        have : ℓj ≤ 1 := min_le_right _ _
        linarith
    have hw_j_lb : ℓj / 400 ≤ Lj - partGrid A j := by linarith [(hstep j).2.1, hratio]
    have hw_j1_lb : ℓj / 200 ≤ partGrid A (j + 2) - Lj := (hstep (j + 1)).2.1
    have hw_j_ub : Lj - partGrid A j ≤ ℓj / 150 := by
      have hw := (hstep j).2.2
      have hmin : min (partGrid A j) 1 ≤ ℓj := min_le_min (hx_mono (Nat.le_succ j)) le_rfl
      linarith
    have hw_j1_ub : partGrid A (j + 2) - Lj ≤ ℓj / 150 := by
      have hw := (hstep (j + 1)).2.2
      linarith
    obtain ⟨hb1_j, hb2_j⟩ := hstepD hlt_j
    obtain ⟨hb1_j1, hb2_j1⟩ := hstepD hlt_j1
    refine ⟨hAj, hLj_le, hℓ0, ?_, ?_, ?_, ?_⟩
    · intro L
      unfold partChi
      have hm : smoothStep (partGrid A (j + 1)) (partGrid A (j + 2)) L ≤
          smoothStep (partGrid A j) (partGrid A (j + 1)) L := by
        rcases le_or_gt L Lj with hL | hL
        · rw [smoothStep_zero_of_le hlt_j1 hL]
          exact smoothStep_nonneg _ _ _
        · rw [smoothStep_one_of_le hlt_j hL.le]
          exact smoothStep_le_one _ _ _
      constructor <;> [linarith; linarith [smoothStep_le_one (partGrid A j) (partGrid A (j + 1)) L,
        smoothStep_nonneg (partGrid A (j + 1)) (partGrid A (j + 2)) L]]
    · intro L hL
      unfold partChi
      rw [Set.mem_Icc] at hL; push Not at hL
      rcases lt_or_ge L (Lj - ℓj / 150) with h1 | h1
      · have hLj1 : L ≤ partGrid A j := by linarith
        have hLj2 : L ≤ Lj := hLj1.trans hlt_j.le
        rw [smoothStep_zero_of_le hlt_j hLj1, smoothStep_zero_of_le hlt_j1 hLj2, sub_zero]
      · have h2 : Lj + ℓj / 150 < L := hL h1
        have hLj1 : Lj ≤ L := by linarith
        have hLj2 : partGrid A (j + 2) ≤ L := by linarith
        rw [smoothStep_one_of_le hlt_j hLj1, smoothStep_one_of_le hlt_j1 hLj2, sub_self]
    · intro L
      have hd1 : Differentiable ℝ (smoothStep (partGrid A j) Lj) :=
        (contDiff_smoothStep _ _).differentiable (by simp)
      have hd2 : Differentiable ℝ (smoothStep Lj (partGrid A (j + 2))) :=
        (contDiff_smoothStep _ _).differentiable (by simp)
      have e : deriv (partChi A j) L = deriv (smoothStep (partGrid A j) Lj) L -
          deriv (smoothStep Lj (partGrid A (j + 2))) L := deriv_sub (hd1 L) (hd2 L)
      rw [e]
      have h_a : |deriv (smoothStep (partGrid A j) Lj) L| ≤ 400 * S1 / ℓj := by
        refine (hb1_j L).trans ?_
        rw [div_le_div_iff₀ (sub_pos.2 hlt_j) hℓ0]
        nlinarith [hw_j_lb, hS1]
      have h_b : |deriv (smoothStep Lj (partGrid A (j + 2))) L| ≤ 200 * S1 / ℓj := by
        refine (hb1_j1 L).trans ?_
        rw [div_le_div_iff₀ (sub_pos.2 hlt_j1) hℓ0]
        nlinarith [hw_j1_lb, hS1]
      calc |deriv (smoothStep (partGrid A j) Lj) L - deriv (smoothStep Lj (partGrid A (j + 2))) L|
          ≤ |deriv (smoothStep (partGrid A j) Lj) L| + |deriv (smoothStep Lj (partGrid A (j + 2))) L| :=
            abs_sub _ _
        _ ≤ 400 * S1 / ℓj + 200 * S1 / ℓj := add_le_add h_a h_b
        _ = 600 * S1 / ℓj := by ring
        _ ≤ 810 * S1 / min Lj 1 := by
            rw [← hℓj]
            exact div_le_div_of_nonneg_right (by linarith [hS1]) hℓ0.le
    · intro L₁ L₂
      have hd1 : Differentiable ℝ (smoothStep (partGrid A j) Lj) :=
        (contDiff_smoothStep _ _).differentiable (by simp)
      have hd2 : Differentiable ℝ (smoothStep Lj (partGrid A (j + 2))) :=
        (contDiff_smoothStep _ _).differentiable (by simp)
      have hchi : partChi A j = smoothStep (partGrid A j) Lj - smoothStep Lj (partGrid A (j + 2)) := rfl
      have e1 := deriv_sub (hd1 L₁) (hd2 L₁)
      have e2 := deriv_sub (hd1 L₂) (hd2 L₂)
      change |deriv (partChi A j) L₁ - deriv (partChi A j) L₂| ≤ _
      rw [hchi, e1, e2, show (deriv (smoothStep (partGrid A j) Lj) L₁ - deriv (smoothStep Lj (partGrid A (j + 2))) L₁) -
        (deriv (smoothStep (partGrid A j) Lj) L₂ - deriv (smoothStep Lj (partGrid A (j + 2))) L₂) =
        (deriv (smoothStep (partGrid A j) Lj) L₁ - deriv (smoothStep (partGrid A j) Lj) L₂) -
        (deriv (smoothStep Lj (partGrid A (j + 2))) L₁ - deriv (smoothStep Lj (partGrid A (j + 2))) L₂) by ring]
      have h_a : S2 / (Lj - partGrid A j) ^ 2 ≤ 160000 * S2 / ℓj ^ 2 := by
        rw [div_le_div_iff₀ (sq_pos_of_pos (sub_pos.2 hlt_j)) (sq_pos_of_pos hℓ0)]
        have hsq : (ℓj / 400) ^ 2 ≤ (Lj - partGrid A j) ^ 2 := pow_le_pow_left₀ (by positivity) hw_j_lb 2
        nlinarith [hS2]
      have h_b : S2 / (partGrid A (j + 2) - Lj) ^ 2 ≤ 40000 * S2 / ℓj ^ 2 := by
        rw [div_le_div_iff₀ (sq_pos_of_pos (sub_pos.2 hlt_j1)) (sq_pos_of_pos hℓ0)]
        have hsq : (ℓj / 200) ^ 2 ≤ (partGrid A (j + 2) - Lj) ^ 2 := pow_le_pow_left₀ (by positivity) hw_j1_lb 2
        nlinarith [hS2]
      have hsub1 : S2 / (Lj - partGrid A j) ^ 2 * |L₁ - L₂| ≤ 160000 * S2 / ℓj ^ 2 * |L₁ - L₂| :=
        mul_le_mul_of_nonneg_right h_a (abs_nonneg _)
      have hsub2 : S2 / (partGrid A (j + 2) - Lj) ^ 2 * |L₁ - L₂| ≤ 40000 * S2 / ℓj ^ 2 * |L₁ - L₂| :=
        mul_le_mul_of_nonneg_right h_b (abs_nonneg _)
      have hle_sum : 200000 * S2 / ℓj ^ 2 * |L₁ - L₂| ≤ 324000 * S2 / min Lj 1 ^ 2 * |L₁ - L₂| := by
        rw [← hℓj]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        exact div_le_div_of_nonneg_right (by linarith [hS2]) (sq_nonneg ℓj)
      calc _ ≤ |deriv (smoothStep (partGrid A j) Lj) L₁ - deriv (smoothStep (partGrid A j) Lj) L₂| +
              |deriv (smoothStep Lj (partGrid A (j + 2))) L₁ - deriv (smoothStep Lj (partGrid A (j + 2))) L₂| := abs_sub _ _
        _ ≤ S2 / (Lj - partGrid A j) ^ 2 * |L₁ - L₂| + S2 / (partGrid A (j + 2) - Lj) ^ 2 * |L₁ - L₂| :=
            add_le_add (hb2_j L₁ L₂) (hb2_j1 L₁ L₂)
        _ ≤ 160000 * S2 / ℓj ^ 2 * |L₁ - L₂| + 40000 * S2 / ℓj ^ 2 * |L₁ - L₂| := add_le_add hsub1 hsub2
        _ = 200000 * S2 / ℓj ^ 2 * |L₁ - L₂| := by ring
        _ ≤ _ := hle_sum

end FormalResearch.SignUncertainty
