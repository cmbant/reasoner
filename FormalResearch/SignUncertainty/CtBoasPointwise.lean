module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasKdW

/-!
# `ct:boas-ineq`: the field `pointwise` of `BoasInputs` (`ct:Bj-pointwise`, (a)-(d))

`constant_terms_lower.tex`, proof of `ct:boas` Step 5, `(ct:Bj-pointwise)`: for every `L ∈ I_j^{**}`,
`A_jW_j + B_jW_j² ≤ 3s_j + K_* e(L)`, `s_j = M_j^σ W_j`, `e(L) = w̃(L)[c(1+τ²)W²/τ + W/τ + W/ℓ]`, with
`τ = τ₀(L)`, `W = W(L) = N(L)/(cτ₀(L))`, `N(L)² = 10⁶(1+L)log c`, `ℓ = min(L,1)`.

Here `A_j = 3M_j' + 2S_jC_l`, `B_j = 2S_jC_q` (the `freeze` coefficients of `boas_freeze_field`).  The geometric facts of (a), (b)
are proved: `W_j ≤ 5W(L)` (`boasW_le_five`, `(1+L_j) ≤ 2(1+L)` and the Harnack ratio `tentBlock_tau0_ratio`), `C_l ≤ 729C_θ/τ`,
`C_q ≤ 81c(1+τ²)/τ` (`boasCl_le`, `boasCq_le`).  The taper facts of (c), (d) enter as the two named hypotheses
`hMp_bd` (`M_j' ≤ M_j^σ + K_mp w̃(L)/ℓ(L)`, from `ct:taper-harnack` and `|χ_j'| ≤ 3/δ_j`) and `hS_bd` (`S_j ≤ K_w w̃(L)`,
`ct:taper-harnack`).  The conclusion holds with `K_* = 15K_mp + 7290K_wC_θ + 4050K_w`.  **Proved** from those hypotheses.
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `W(L) = N(L)/(cτ₀(L))`, `N(L)² = 10⁶(1 + L) log c` (`boasW c a j = boasWf c (x_{j+1})`). -/
noncomputable def boasWf (c L : ℝ) : ℝ := √(1000000 * (1 + L) * Real.log c) / (c * tau0 L)

/-- The weight `e(L) = w̃(L)[c(1+τ²)W²/τ + W/τ + W/ℓ]` of `ct:Bj-pointwise`, `τ = τ₀(L)`, `W = W(L)`, `ℓ = min(L,1)`. -/
noncomputable def boasE (c : ℝ) (wt : ℝ → ℝ) (L : ℝ) : ℝ :=
  wt L * (c * (1 + tau0 L ^ 2) / tau0 L * boasWf c L ^ 2 + boasWf c L / tau0 L + boasWf c L / min L 1)

lemma boasW_eq (c a : ℝ) (j : ℕ) : boasW c a j = boasWf c (tentNode a (j + 1)) := rfl

lemma boasWf_nonneg {c L : ℝ} (hc : 0 < c) (hL : 0 < L) : 0 ≤ boasWf c L := by
  unfold boasWf
  have := tau0_pos hL
  positivity

/-- **`W_j ≤ 5W(L)`** on `I_j^{**}` (`(ct:Wj-harnack)`). -/
lemma boasW_le_five {c a : ℝ} (hc : 1 ≤ c) (ha : 0 < a) {j : ℕ} {L : ℝ} (hL : L ∈ tentQ a j) :
    boasW c a j ≤ 5 * boasWf c L := by
  have hc0 : 0 < c := by linarith
  have hlog : 0 ≤ Real.log c := Real.log_nonneg hc
  have hLj0 : 0 < tentNode a (j + 1) := tentNode_pos ha _
  have hδ := tentDelta_pos ha j
  have hLjQ : tentNode a (j + 1) ∈ tentQ a j := by unfold tentQ; exact ⟨by linarith, by linarith⟩
  obtain ⟨_, hL0, hr1, hr2⟩ := tentBlock_tau0_ratio (Lj := tentNode a (j + 1)) (δ := tentDelta a j) hLj0 rfl hLjQ hL
  set Lj := tentNode a (j + 1) with hLjdef
  have hτj := tau0_pos hLj0
  have hτ := tau0_pos hL0
  -- `1 + L_j ≤ 2 (1 + L)`
  have hLq : Lj - 3 * tentDelta a j ≤ L := hL.1
  have hδ36 : 3 * tentDelta a j ≤ Lj / 12 := by
    unfold tentDelta; have := min_le_left Lj 1; linarith
  have h1L : 1 + Lj ≤ 2 * (1 + L) := by linarith only [hLq, hδ36, hL0]
  have hN : √(1000000 * (1 + Lj) * Real.log c) ≤ 3 / 2 * √(1000000 * (1 + L) * Real.log c) := by
    have hsq : 1000000 * (1 + Lj) * Real.log c ≤ 2 * (1000000 * (1 + L) * Real.log c) := by
      nlinarith only [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1000000) hlog) (sub_nonneg.2 h1L)]
    calc √(1000000 * (1 + Lj) * Real.log c) ≤ √(2 * (1000000 * (1 + L) * Real.log c)) :=
          Real.sqrt_le_sqrt hsq
      _ = √2 * √(1000000 * (1 + L) * Real.log c) := Real.sqrt_mul (by norm_num) _
      _ ≤ 3 / 2 * √(1000000 * (1 + L) * Real.log c) := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hNn := Real.sqrt_nonneg (1000000 * (1 + L) * Real.log c)
  unfold boasW boasWf
  rw [← hLjdef]
  rw [div_le_iff₀ (by positivity)]
  have hτ' : tau0 L / 3 ≤ tau0 Lj := by linarith
  calc √(1000000 * (1 + Lj) * Real.log c)
      ≤ 3 / 2 * √(1000000 * (1 + L) * Real.log c) := hN
    _ = 5 * (√(1000000 * (1 + L) * Real.log c) / (c * tau0 L)) * (c * (tau0 L)) * (3 / 10) := by
        field_simp; ring
    _ ≤ 5 * (√(1000000 * (1 + L) * Real.log c) / (c * tau0 L)) * (c * tau0 Lj) := by
        have hW0 : 0 ≤ √(1000000 * (1 + L) * Real.log c) / (c * tau0 L) := by positivity
        have : c * tau0 L * (3 / 10) ≤ c * tau0 Lj := by nlinarith [mul_pos hc0 hτ]
        calc 5 * (√(1000000 * (1 + L) * Real.log c) / (c * tau0 L)) * (c * tau0 L) * (3 / 10)
            = 5 * (√(1000000 * (1 + L) * Real.log c) / (c * tau0 L)) * (c * tau0 L * (3 / 10)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)

/-- `C_l ≤ 729 C_θ/τ₀(L)` on `I_j^{**}`. -/
lemma boasCl_le {Cθ a : ℝ} (hCθ : 0 ≤ Cθ) (ha : 0 < a) {j : ℕ} {L : ℝ} (hL : L ∈ tentQ a j) :
    boasCl Cθ a j ≤ 729 * Cθ / tau0 L := by
  have hLj0 : 0 < tentNode a (j + 1) := tentNode_pos ha _
  have hδ := tentDelta_pos ha j
  have hLjQ : tentNode a (j + 1) ∈ tentQ a j := by unfold tentQ; exact ⟨by linarith, by linarith⟩
  obtain ⟨_, hL0, hr1, hr2⟩ := tentBlock_tau0_ratio (Lj := tentNode a (j + 1)) (δ := tentDelta a j) hLj0 rfl hLjQ hL
  have hτj := tau0_pos hLj0
  have hτ := tau0_pos hL0
  set r := tau0 (tentNode a (j + 1)) with hr
  have h1 : boasCl Cθ a j ≤ 243 * Cθ / r := by
    unfold boasCl boasLam
    rw [← hr]
    rw [show 27 * (1 + r ^ 2) / r * (Cθ / (1 + r / 3) ^ 2) = 27 * Cθ * (1 + r ^ 2) / (r * (1 + r / 3) ^ 2) by
      field_simp]
    rw [div_le_div_iff₀ (by positivity) hτj]
    nlinarith [mul_nonneg hCθ (sq_nonneg r), mul_nonneg hCθ hτj.le, mul_nonneg (mul_nonneg hCθ hτj.le) hτj.le]
  refine h1.trans ?_
  rw [div_le_div_iff₀ hτj hτ]
  nlinarith [mul_nonneg hCθ hτ.le, mul_nonneg hCθ hτj.le]

/-- `C_q ≤ 81 c(1 + τ²)/τ` with `τ = τ₀(L)`, on `I_j^{**}`. -/
lemma boasCq_le {c a : ℝ} (hc : 0 ≤ c) (ha : 0 < a) {j : ℕ} {L : ℝ} (hL : L ∈ tentQ a j) :
    boasCq c a j ≤ 81 * (c * (1 + tau0 L ^ 2) / tau0 L) := by
  have hLj0 : 0 < tentNode a (j + 1) := tentNode_pos ha _
  have hδ := tentDelta_pos ha j
  have hLjQ : tentNode a (j + 1) ∈ tentQ a j := by unfold tentQ; exact ⟨by linarith, by linarith⟩
  obtain ⟨_, hL0, hr1, hr2⟩ := tentBlock_tau0_ratio (Lj := tentNode a (j + 1)) (δ := tentDelta a j) hLj0 rfl hLjQ hL
  have hτj := tau0_pos hLj0
  have hτ := tau0_pos hL0
  set r := tau0 (tentNode a (j + 1)) with hr
  unfold boasCq boasLam
  rw [← hr]
  have e1 : c * (27 * (1 + r ^ 2) / r) = 27 * c * (1 + r ^ 2) / r := by ring
  have e2 : 81 * (c * (1 + tau0 L ^ 2) / tau0 L) = 81 * c * (1 + tau0 L ^ 2) / tau0 L := by ring
  rw [e1, e2, div_le_div_iff₀ hτj hτ]
  have hr3 : r ≤ 3 * tau0 L := by linarith
  have hr4 : tau0 L ≤ 3 * r := hr2
  nlinarith [mul_nonneg hc hτ.le, mul_nonneg hc hτj.le, mul_nonneg (mul_nonneg hc hτ.le) hτj.le,
    mul_nonneg (mul_nonneg hc hτj.le) (sub_nonneg.2 hr3), mul_nonneg (mul_nonneg hc hτ.le) (sub_nonneg.2 hr4),
    mul_nonneg (mul_nonneg hc (mul_nonneg hτ.le hτj.le)) (sub_nonneg.2 hr3),
    mul_nonneg (mul_nonneg hc (mul_nonneg hτ.le hτj.le)) (sub_nonneg.2 hr4)]

/-- **The field `pointwise` of `BoasInputs`** (`ct:Bj-pointwise`): for `L ∈ I_j^{**}`,
`A_jW_j + B_jW_j² ≤ 3s_j + K_* e(L)`, `A_j = 3M_j' + 2S_jC_l`, `B_j = 2S_jC_q`, `s_j = M_j^σ W_j` and
`K_* = 15K_mp + 7290K_wC_θ + 4050K_w`, from `hMp_bd` (`M_j' ≤ M_j^σ + K_mp w̃(L)/min(L,1)`) and `hS_bd`
(`S_j ≤ K_w w̃(L)`), the consequences of `ct:taper-harnack` (see the module docstring). -/
theorem boas_pointwise_field {c Cθ a Kmp Kw : ℝ} {J : ℕ} (hc : 1 ≤ c) (hCθ : 0 ≤ Cθ) (ha : 0 < a)
    (hKmp : 0 ≤ Kmp) (hKw : 0 ≤ Kw) {wt : ℝ → ℝ} (hw0 : ∀ L, 0 ≤ wt L) {Mp S Msig : ℕ → ℝ}
    (hS0 : ∀ j < J, 0 ≤ S j)
    (hMp_bd : ∀ j < J, ∀ L ∈ tentQ a j, Mp j ≤ Msig j + Kmp * wt L / min L 1)
    (hS_bd : ∀ j < J, ∀ L ∈ tentQ a j, S j ≤ Kw * wt L) :
    ∀ j < J, ∀ L ∈ tentQ a j,
      (3 * Mp j + 2 * S j * boasCl Cθ a j) * boasW c a j + (2 * S j * boasCq c a j) * boasW c a j ^ 2 ≤
        3 * (Msig j * boasW c a j) + (15 * Kmp + 7290 * Kw * Cθ + 4050 * Kw) * boasE c wt L := by
  intro j hj L hL
  have hc0 : 0 < c := by linarith
  have hLj0 : 0 < tentNode a (j + 1) := tentNode_pos ha _
  have hδ := tentDelta_pos ha j
  have hLjQ : tentNode a (j + 1) ∈ tentQ a j := by unfold tentQ; exact ⟨by linarith, by linarith⟩
  obtain ⟨_, hL0, _, _⟩ := tentBlock_tau0_ratio (Lj := tentNode a (j + 1)) (δ := tentDelta a j) hLj0 rfl hLjQ hL
  have hτ := tau0_pos hL0
  have hℓ : 0 < min L 1 := lt_min hL0 one_pos
  set Wj := boasW c a j with hWj
  set W := boasWf c L with hW
  have hW0 : 0 ≤ W := boasWf_nonneg hc0 hL0
  have hWj0 : 0 ≤ Wj := by rw [hWj, boasW_eq]; exact boasWf_nonneg hc0 hLj0
  have hW5 : Wj ≤ 5 * W := boasW_le_five hc ha hL
  have hCl := boasCl_le hCθ ha hL
  have hCq := boasCq_le hc0.le ha hL
  have hCl0 : 0 ≤ boasCl Cθ a j := by
    have := boasLam_pos ha j
    unfold boasCl; exact mul_nonneg this.le (by positivity)
  have hCq0 : 0 ≤ boasCq c a j := mul_nonneg hc0.le (boasLam_pos ha j).le
  have hwt := hw0 L
  have hMpb := hMp_bd j hj L hL
  have hSb := hS_bd j hj L hL
  have hS := hS0 j hj
  -- the three terms of `e(L)`
  set T1 := c * (1 + tau0 L ^ 2) / tau0 L * W ^ 2 with hT1
  set T2 := W / tau0 L with hT2
  set T3 := W / min L 1 with hT3
  have hT10 : 0 ≤ T1 := by positivity
  have hT20 : 0 ≤ T2 := by positivity
  have hT30 : 0 ≤ T3 := by positivity
  have he : boasE c wt L = wt L * (T1 + T2 + T3) := rfl
  -- (i) the taper term
  have i1 : 3 * Mp j * Wj ≤ 3 * (Msig j * Wj) + 15 * Kmp * (wt L * T3) := by
    have h1 : Mp j * Wj ≤ (Msig j + Kmp * wt L / min L 1) * Wj := mul_le_mul_of_nonneg_right hMpb hWj0
    have h2 : Kmp * wt L / min L 1 * Wj ≤ Kmp * wt L / min L 1 * (5 * W) :=
      mul_le_mul_of_nonneg_left hW5 (by positivity)
    have e : Kmp * wt L / min L 1 * (5 * W) = 5 * Kmp * (wt L * T3) := by
      rw [hT3]; field_simp
    linarith [h1, h2, e]
  -- (ii) the `θ` term
  have i2 : 2 * S j * boasCl Cθ a j * Wj ≤ 7290 * Kw * Cθ * (wt L * T2) := by
    have a1 : S j * boasCl Cθ a j ≤ (Kw * wt L) * (729 * Cθ / tau0 L) :=
      mul_le_mul hSb hCl hCl0 (by positivity)
    have a2 : S j * boasCl Cθ a j * Wj ≤ (Kw * wt L) * (729 * Cθ / tau0 L) * (5 * W) :=
      mul_le_mul a1 hW5 hWj0 (by positivity)
    have e : (Kw * wt L) * (729 * Cθ / tau0 L) * (5 * W) = 3645 * Kw * Cθ * (wt L * T2) := by
      rw [hT2]; field_simp; ring
    linarith [a2, e]
  -- (iii) the curvature term
  have i3 : 2 * S j * boasCq c a j * Wj ^ 2 ≤ 4050 * Kw * (wt L * T1) := by
    have a1 : S j * boasCq c a j ≤ (Kw * wt L) * (81 * (c * (1 + tau0 L ^ 2) / tau0 L)) :=
      mul_le_mul hSb hCq hCq0 (by positivity)
    have hW2 : Wj ^ 2 ≤ (5 * W) ^ 2 := pow_le_pow_left₀ hWj0 hW5 2
    have a2 : S j * boasCq c a j * Wj ^ 2 ≤ (Kw * wt L) * (81 * (c * (1 + tau0 L ^ 2) / tau0 L)) * (5 * W) ^ 2 :=
      mul_le_mul a1 hW2 (sq_nonneg _) (by positivity)
    have e : (Kw * wt L) * (81 * (c * (1 + tau0 L ^ 2) / tau0 L)) * (5 * W) ^ 2 =
        2025 * Kw * (wt L * T1) := by
      rw [hT1]; ring
    linarith [a2, e]
  have hwT1 : 0 ≤ wt L * T1 := mul_nonneg hwt hT10
  have hwT2 : 0 ≤ wt L * T2 := mul_nonneg hwt hT20
  have hwT3 : 0 ≤ wt L * T3 := mul_nonneg hwt hT30
  rw [he]
  have hK2 : 0 ≤ Kw * Cθ := mul_nonneg hKw hCθ
  set Ks : ℝ := 15 * Kmp + 7290 * Kw * Cθ + 4050 * Kw with hKs
  have k1 : 4050 * Kw * (wt L * T1) ≤ Ks * (wt L * T1) :=
    mul_le_mul_of_nonneg_right (by rw [hKs]; linarith only [hKmp, hKw, hK2]) hwT1
  have k2 : 7290 * Kw * Cθ * (wt L * T2) ≤ Ks * (wt L * T2) :=
    mul_le_mul_of_nonneg_right (by rw [hKs]; linarith only [hKmp, hKw, hK2]) hwT2
  have k3 : 15 * Kmp * (wt L * T3) ≤ Ks * (wt L * T3) :=
    mul_le_mul_of_nonneg_right (by rw [hKs]; linarith only [hKmp, hKw, hK2]) hwT3
  have hdist : Ks * (wt L * (T1 + T2 + T3)) = Ks * (wt L * T1) + Ks * (wt L * T2) + Ks * (wt L * T3) := by ring
  have hlhs : (3 * Mp j + 2 * S j * boasCl Cθ a j) * Wj + (2 * S j * boasCq c a j) * Wj ^ 2 =
      3 * Mp j * Wj + 2 * S j * boasCl Cθ a j * Wj + 2 * S j * boasCq c a j * Wj ^ 2 := by ring
  rw [hlhs, hdist]
  linarith [i1, i2, i3, k1, k2, k3]

/-- info: 'FormalResearch.SignUncertainty.boas_pointwise_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_pointwise_field

end FormalResearch.SignUncertainty
