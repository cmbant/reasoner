module

public import Mathlib
public import FormalResearch.SignUncertainty.CtDyadicPointwise
public import FormalResearch.SignUncertainty.CtBoasSigmaLip

/-!
# `ct:Bj-pointwise` (e): the two classes of `s_j = M_j^σ W_j`

`constant_terms_lower.tex`, proof of `ct:boas` Step 5 (e) (`ct:sigma-prime`): `s_j = M_j^σ W_j` with `M_j^σ = sigLip c Rt_j`
(`tapMsig`, `Rt_j = L_j + 3δ_j`), `W_j = boasW c a j`, `L_j = x_{j+1}` (`tentNode a (j + 1)`).  With `L_far = log(π² log c)`
(`e^{L_far} = π² log c`, i.e. `Δ(L_far) = D = c log c`), for a block `L_j ≤ L_far + 1`:

* `sigLip_le_of_far` (`ct:sigma-prime`, Gaussian factor): if `Δ(Rt) ≤ D/2` then `sigLip c Rt ≤ 2 log c e^{-2(log c)²}`;
* `sigLip_le_four` : `sigLip c Rt ≤ 4 e^{Rt}/π²` (`G_W ≤ 1/(√(2π)W)`, `W_far = c/4`);
* **`boas_s_classes`** (the hypothesis `hcls` of `boas_s_moment_split`): either `s_j ≤ e^{-(log c)²}` (`L_j < L_far - 2`, using
  `W_j ≤ 1`), or `s_j ≤ 2000 log c/c` and `Q_j ⊆ [L_far - 5/2, ∞)` (`L_j ≥ L_far - 2`, using `e^{L_j} ≤ πτ₀(L_j)`,
  `τ₀ ≍ e^L` for `L ≥ 1`).  Regime hypotheses: `3 ≤ L_far`, `L_far + 2 ≤ 2 log c`, `2000 log c ≤ c√a` (`a ≍ c^{-2/21}`,
  `W_j ≤ 1`).

**Proved**, unconditional given those regime inequalities (all hold for large `c`).
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtBoasWindow
open FormalResearch.SignUncertainty.FctCuspEdge

/-- **`ct:sigma-prime` (Gaussian factor)**: if `Δ(Rt) = c e^{Rt}/π² ≤ D/2` then `sigLip c Rt ≤ 2 log c · e^{-2(log c)²}`. -/
lemma sigLip_le_of_far {c Rt : ℝ} (hc : 1 < c) (hΔ : c * (Real.exp Rt / π ^ 2) ≤ farD c / 2) :
    sigLip c Rt ≤ 2 * Real.log c * Real.exp (-(2 * Real.log c ^ 2)) := by
  have hc0 : 0 < c := by linarith
  have hlog : 0 < Real.log c := Real.log_pos hc
  have hD : farD c = c * Real.log c := rfl
  have hW : farW c = c / 4 := rfl
  set Δ := c * (Real.exp Rt / π ^ 2) with hΔdef
  have hΔ0 : 0 ≤ Δ := by positivity
  have hm : max 0 (farD c - Δ) = farD c - Δ := max_eq_right (by linarith [hD ▸ hΔ, mul_pos hc0 hlog])
  unfold sigLip
  rw [← hΔdef, hm]
  have hm2 : (c * Real.log c / 2) ^ 2 ≤ (farD c - Δ) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    rw [hD] at hΔ ⊢; linarith
  have hexp : Real.exp (-(1 / (2 * farW c ^ 2)) * (farD c - Δ) ^ 2) ≤ Real.exp (-(2 * Real.log c ^ 2)) := by
    apply Real.exp_le_exp.2
    rw [hW]
    have h1 : 1 / (2 * (c / 4) ^ 2) = 8 / c ^ 2 := by field_simp; ring
    rw [h1]
    have : 8 / c ^ 2 * (c * Real.log c / 2) ^ 2 = 2 * Real.log c ^ 2 := by field_simp; ring
    have h3 : 8 / c ^ 2 * (c * Real.log c / 2) ^ 2 ≤ 8 / c ^ 2 * (farD c - Δ) ^ 2 :=
      mul_le_mul_of_nonneg_left hm2 (by positivity)
    nlinarith
  have hG : gaussK (farW c) (farD c - Δ) ≤ Real.exp (-(2 * Real.log c ^ 2)) * (4 / c) := by
    unfold gaussK
    rw [hW]
    have hs : 1 ≤ √(2 * π) := by
      rw [Real.one_le_sqrt]; nlinarith [Real.pi_gt_three]
    have hden : c / 4 ≤ √(2 * π) * (c / 4) := by nlinarith [mul_pos hc0 hc0]
    calc Real.exp (-(1 / (2 * (c / 4) ^ 2)) * (farD c - Δ) ^ 2) / (√(2 * π) * (c / 4))
        ≤ Real.exp (-(2 * Real.log c ^ 2)) / (√(2 * π) * (c / 4)) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          rw [hW] at hexp; exact hexp
      _ ≤ Real.exp (-(2 * Real.log c ^ 2)) / (c / 4) :=
          div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hden
      _ = Real.exp (-(2 * Real.log c ^ 2)) * (4 / c) := by field_simp
  have hΔD : Δ ≤ c * Real.log c / 2 := by rw [hD] at hΔ; exact hΔ
  calc Δ * gaussK (farW c) (farD c - Δ) ≤ (c * Real.log c / 2) * (Real.exp (-(2 * Real.log c ^ 2)) * (4 / c)) :=
        mul_le_mul hΔD hG (gaussK_nonneg' _ _ (by rw [hW]; positivity)) (by positivity)
    _ = 2 * Real.log c * Real.exp (-(2 * Real.log c ^ 2)) := by field_simp; norm_num

/-- `sigLip c Rt ≤ 4 e^{Rt}/π²` (`G_{c/4} ≤ 1/(√(2π) c/4) ≤ 4/c`). -/
lemma sigLip_le_four {c Rt : ℝ} (hc : 1 < c) : sigLip c Rt ≤ 4 * Real.exp Rt / π ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hW : farW c = c / 4 := rfl
  unfold sigLip
  have hs : 1 ≤ √(2 * π) := by
    rw [Real.one_le_sqrt]; nlinarith [Real.pi_gt_three]
  have hG : gaussK (farW c) (max 0 (farD c - c * (Real.exp Rt / π ^ 2))) ≤ 4 / c := by
    unfold gaussK
    rw [hW]
    have hden : c / 4 ≤ √(2 * π) * (c / 4) := by nlinarith [mul_pos hc0 hc0]
    have hex : Real.exp (-(1 / (2 * (c / 4) ^ 2)) * max 0 (farD c - c * (Real.exp Rt / π ^ 2)) ^ 2) ≤ 1 := by
      apply Real.exp_le_one_iff.2
      have : 0 ≤ 1 / (2 * (c / 4) ^ 2) * max 0 (farD c - c * (Real.exp Rt / π ^ 2)) ^ 2 := by positivity
      linarith
    calc _ ≤ 1 / (√(2 * π) * (c / 4)) := div_le_div_of_nonneg_right hex (by positivity)
      _ ≤ 1 / (c / 4) := one_div_le_one_div_of_le (by positivity) hden
      _ = 4 / c := by field_simp
  have hπ : 0 < π ^ 2 := by positivity
  calc c * (Real.exp Rt / π ^ 2) * gaussK (farW c) _ ≤ c * (Real.exp Rt / π ^ 2) * (4 / c) :=
        mul_le_mul_of_nonneg_left hG (by positivity)
    _ = 4 * Real.exp Rt / π ^ 2 := by field_simp

/-- `1 + L_j ≤ L_far + 2 ≤ 2 log c` gives `N_j ≤ 1415 log c`. -/
lemma boasN_le {c L : ℝ} (hc : 3 ≤ c) (hL : 1 + L ≤ 2 * Real.log c) :
    √(1000000 * (1 + L) * Real.log c) ≤ 1415 * Real.log c := by
  have hlog := one_le_log_of_three_le hc
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ 1000000 * Real.log c)]

/-- `τ₀(L) ≥ 0.86 √a` for `a ≤ L`, `a ≤ 1`. -/
lemma tau0_ge_sqrt_a {a L : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hL : a ≤ L) : 0.86 * √a ≤ tau0 L := by
  have hL0 : 0 < L := lt_of_lt_of_le ha hL
  have hsa : √a ≤ 1 := by rw [Real.sqrt_le_one]; exact ha1
  rcases le_total L 1 with h1 | h1
  · obtain ⟨hs, -, -⟩ := tau0_small_bounds hL0 h1
    have : √a ≤ √L := Real.sqrt_le_sqrt hL
    nlinarith [Real.sqrt_nonneg a]
  · obtain ⟨hlo, -⟩ := tau0_large_bounds h1
    have he : Real.exp 1 ≤ Real.exp L := Real.exp_le_exp.2 h1
    have h2 : 0.86 ≤ Real.exp L / π := by
      rw [le_div_iff₀ Real.pi_pos]
      nlinarith [Real.exp_one_gt_d9, Real.pi_lt_d2]
    nlinarith [Real.sqrt_nonneg a]

/-- `e^x ≤ 12/11` for `x ≤ 1/12` (from `e^{-x} ≥ 1 - x`). -/
lemma exp_le_twelve_eleven {x : ℝ} (hx : x ≤ 1 / 12) : Real.exp x ≤ 12 / 11 := by
  have h := Real.add_one_le_exp (-x)
  have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hp := Real.exp_pos x
  nlinarith [mul_le_mul_of_nonneg_left h hp.le]

/-- **The two classes of `s_j`** (`ct:Bj-pointwise` (e), `ct:sigma-prime`): the hypothesis `hcls` of `boas_s_moment_split` for
`s_j = tapMsig c a j * boasW c a j`, `Q_j = tentQ a j`, `L_cut = L_far - 5/2`, `s₁ = e^{-(log c)²}`, `s₂ = 2000 log c/c`, for blocks
with `L_j ≤ L_far + 1`, where `e^{L_far} = π² log c`. -/
theorem boas_s_classes {c a Lfar : ℝ} (hc : 3 ≤ c) (ha : 0 < a) (ha1 : a ≤ 1) (hLfar : Real.exp Lfar = π ^ 2 * Real.log c)
    (hLf3 : 3 ≤ Lfar) (hLf : Lfar + 2 ≤ 2 * Real.log c) (hreg : 2000 * Real.log c ≤ c * √a) {j : ℕ}
    (hj : tentNode a (j + 1) ≤ Lfar + 1) :
    tapMsig c a j * boasW c a j ≤ Real.exp (-(Real.log c ^ 2)) ∨
      (tapMsig c a j * boasW c a j ≤ 2000 * Real.log c / c ∧ tentQ a j ⊆ Ici (Lfar - 5 / 2)) := by
  have hc0 : 0 < c := by linarith
  have hc1 : 1 < c := by linarith
  have hlog1 := one_le_log_of_three_le hc
  set Lj := tentNode a (j + 1) with hLjdef
  have hLj0 : 0 < Lj := tentNode_pos ha _
  have haL : a ≤ Lj := (tentNode_strictMono ha).monotone (Nat.zero_le (j + 1))
  have hδ : 3 * tentDelta a j ≤ 1 / 12 := by
    unfold tentDelta; have := min_le_right Lj 1; linarith
  have hδ0 := tentDelta_pos ha j
  have hτ := tau0_pos hLj0
  have hτa := tau0_ge_sqrt_a ha ha1 haL
  have hsa0 : 0 < √a := Real.sqrt_pos.2 ha
  have hN : √(1000000 * (1 + Lj) * Real.log c) ≤ 1415 * Real.log c := boasN_le hc (by linarith [hj, hLf])
  have hW0 : 0 ≤ boasW c a j := by
    have := boasWf_nonneg hc0 hLj0
    exact this
  have hW1 : boasW c a j ≤ 1 := by
    show √(1000000 * (1 + Lj) * Real.log c) / (c * tau0 Lj) ≤ 1
    rw [div_le_one (by positivity)]
    have : c * (0.86 * √a) ≤ c * tau0 Lj := mul_le_mul_of_nonneg_left hτa hc0.le
    nlinarith only [hN, this, hreg, hlog1]
  have hs0 : 0 ≤ tapMsig c a j := sigLip_nonneg hc1 _
  have hRt : Real.exp (Lj + 3 * tentDelta a j) = Real.exp Lj * Real.exp (3 * tentDelta a j) := Real.exp_add _ _
  rcases lt_or_ge Lj (Lfar - 2) with h1 | h1
  · left
    have hexp : Real.exp (Lj + 3 * tentDelta a j) ≤ Real.exp Lfar / 2 := by
      have h2 : Real.exp (Lj + 3 * tentDelta a j) ≤ Real.exp (Lfar - 19 / 10) :=
        Real.exp_le_exp.2 (by linarith)
      rw [Real.exp_sub] at h2
      have h3 : 2 ≤ Real.exp (19 / 10) := by linarith [Real.add_one_le_exp (19 / 10 : ℝ)]
      have h4 := Real.exp_pos Lfar
      calc Real.exp (Lj + 3 * tentDelta a j) ≤ Real.exp Lfar / Real.exp (19 / 10) := h2
        _ ≤ Real.exp Lfar / 2 := div_le_div_of_nonneg_left h4.le (by norm_num) h3
    have hΔ : c * (Real.exp (Lj + 3 * tentDelta a j) / π ^ 2) ≤ farD c / 2 := by
      have hπ : 0 < π ^ 2 := by positivity
      calc c * (Real.exp (Lj + 3 * tentDelta a j) / π ^ 2) ≤ c * (Real.exp Lfar / 2 / π ^ 2) := by
            gcongr
        _ = farD c / 2 := by
            rw [hLfar]; unfold farD; field_simp
    have hσ := sigLip_le_of_far hc1 hΔ
    have hsj : tapMsig c a j * boasW c a j ≤ 2 * Real.log c * Real.exp (-(2 * Real.log c ^ 2)) := by
      calc tapMsig c a j * boasW c a j ≤ (2 * Real.log c * Real.exp (-(2 * Real.log c ^ 2))) * 1 :=
            mul_le_mul hσ hW1 hW0 (by positivity)
        _ = _ := mul_one _
    refine hsj.trans ?_
    have h2L : 2 * Real.log c ≤ Real.exp (Real.log c ^ 2) := by
      nlinarith [Real.add_one_le_exp (Real.log c ^ 2), sq_nonneg (Real.log c - 1)]
    calc 2 * Real.log c * Real.exp (-(2 * Real.log c ^ 2))
        ≤ Real.exp (Real.log c ^ 2) * Real.exp (-(2 * Real.log c ^ 2)) :=
          mul_le_mul_of_nonneg_right h2L (Real.exp_pos _).le
      _ = Real.exp (-(Real.log c ^ 2)) := by rw [← Real.exp_add]; ring_nf
  · right
    have hLj1 : 1 ≤ Lj := by linarith
    obtain ⟨hlo, -⟩ := tau0_large_bounds hLj1
    have hexpτ : Real.exp Lj ≤ π * tau0 Lj := by rwa [div_le_iff₀ Real.pi_pos, mul_comm] at hlo
    have hexp3 := exp_le_twelve_eleven hδ
    have hRt' : Real.exp (Lj + 3 * tentDelta a j) ≤ 12 / 11 * (π * tau0 Lj) := by
      rw [hRt]
      calc Real.exp Lj * Real.exp (3 * tentDelta a j) ≤ (π * tau0 Lj) * (12 / 11) :=
            mul_le_mul hexpτ hexp3 (Real.exp_pos _).le (by positivity)
        _ = _ := by ring
    have hσ := sigLip_le_four (Rt := Lj + 3 * tentDelta a j) hc1
    have hσ' : tapMsig c a j ≤ 48 / 11 * tau0 Lj / π := by
      refine hσ.trans ?_
      have hπ : 0 < π := Real.pi_pos
      rw [div_le_iff₀ (by positivity)]
      have : 4 * Real.exp (Lj + 3 * tentDelta a j) ≤ 4 * (12 / 11 * (π * tau0 Lj)) := by linarith
      calc 4 * Real.exp (Lj + 3 * tentDelta a j) ≤ 4 * (12 / 11 * (π * tau0 Lj)) := this
        _ = 48 / 11 * tau0 Lj / π * π ^ 2 := by field_simp; norm_num
    refine ⟨?_, ?_⟩
    · have hW : boasW c a j = √(1000000 * (1 + Lj) * Real.log c) / (c * tau0 Lj) := rfl
      calc tapMsig c a j * boasW c a j ≤ (48 / 11 * tau0 Lj / π) * (√(1000000 * (1 + Lj) * Real.log c) / (c * tau0 Lj)) :=
            mul_le_mul hσ' le_rfl hW0 (by positivity)
        _ = 48 / (11 * π) * (√(1000000 * (1 + Lj) * Real.log c) / c) := by
            field_simp
        _ ≤ 48 / (11 * π) * (1415 * Real.log c / c) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hN hc0.le) (by positivity)
        _ ≤ 2000 * Real.log c / c := by
            rw [← mul_div_assoc, div_le_div_iff_of_pos_right hc0]
            have : 48 / (11 * π) ≤ 1.4 := by
              rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_d2]
            nlinarith [mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ 1415 * Real.log c)]
    · intro x hx
      have := hx.1
      show Lfar - 5 / 2 ≤ x
      linarith

/-- info: 'FormalResearch.SignUncertainty.boas_s_classes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_s_classes

/-- **The pointwise hypotheses of `boas_e_moment_split`** (`ct:Bj-pointwise` (f)): for `e = boasE c (ctTaper ε c R)`, `v = v' =
-ũ∘ξ` (`ctVprime`; `v' ≤ ctTaperV`, so `ctE_small_v` gives the same with `ctTaperV`), `Λ = ctTaperLam ε c R`, `Λ₀ ≤ Λ`, and any set
`U ⊆ (0, ∞)` on which `v' ≥ 1` below `Λ` (the paper's `U = ⋃ I_j^{**} ⊂ [½L_min, L_far + 3/2]`): `hsm`, `hlg` with
`α_e = 2·10¹¹ P log c/(R²√R)` and `β_e = 7·10⁷ log c/(cΛ₀^{3/2})`, both nonnegative. -/
theorem ctE_moment_pointwise {ε c R : ℝ} (hB : TaperBand ε c R) (hc3 : 3 ≤ c) {Λ₀ : ℝ} (hΛ0 : 0 < Λ₀)
    (hΛ : Λ₀ ≤ ctTaperLam ε c R) {U : Set ℝ} (hU : ∀ L ∈ U, 0 < L ∧ (L ≤ ctTaperLam ε c R → 1 ≤ ctVprime c L)) :
    (∀ L ∈ U, L ≤ ctTaperLam ε c R → boasE c (ctTaper ε c R) L ≤
      (200000000000 * √((1.0025 * langerKappa) ^ 3) * Real.log c / (R ^ 2 * √R)) * ctVprime c L) ∧
    (∀ L ∈ U, ctTaperLam ε c R < L → boasE c (ctTaper ε c R) L ≤ 70000000 * Real.log c / (c * (Λ₀ * √Λ₀))) ∧
    0 ≤ 200000000000 * √((1.0025 * langerKappa) ^ 3) * Real.log c / (R ^ 2 * √R) ∧
    0 ≤ 70000000 * Real.log c / (c * (Λ₀ * √Λ₀)) := by
  have hc0 : 0 < c := by linarith
  have hlog := Real.log_nonneg (by linarith : (1 : ℝ) ≤ c)
  have hR := hB.inputs.R_pos
  have hκ := langerKappa_pos
  refine ⟨fun L hL hLΛ => ctE_small hB hc3 (hU L hL).1 hLΛ ((hU L hL).2 hLΛ),
    fun L hL hLΛ => ctE_large hB hc3 hΛ0 hΛ hLΛ, by positivity, by positivity⟩

/-- info: 'FormalResearch.SignUncertainty.ctE_moment_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctE_moment_pointwise

end FormalResearch.SignUncertainty
