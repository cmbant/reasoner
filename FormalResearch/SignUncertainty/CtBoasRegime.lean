module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasMBounds
public import FormalResearch.SignUncertainty.CtBoasPlb

/-!
# `ct:boas` Step 4: the regime check for the paper's `W_j`, `N_j`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:boas` Step 4, items (i)-(iv) and `ct:P-lb`.
Block data: `τ_j > 0`, `L_j ≥ 0`, `L₀ = m(τ₀)` with `τ₀/3 ≤ τ_j ≤ 3τ₀`, `L₀ ≤ 1 + L_j ≤ 2(1 + L₀)` and
`c^{-1/3} ≤ L₀ ≤ log c` (the paper's `L_min = c^{-2/21}` and `L ≤ L_far + 1` are inside this range for large `c`).
`N'² = C_N (1+L_j) log c` with `C_N = 10^6` (the paper's remark "one may enlarge `C_N`"; the TeX value `2·10^5` gives
`(ii)` only with the sharper `Δ_{3/2} ≥ 0.24` for `τ₀ > 1`), `W = N'/(cτ_j)`.

* `hankel_P_lb_regime_of`: for `c` with `1.56·10^{11} (log c)² ≤ c^{1}` and `8320 log c ≤ c^{1/3}` (both eventually true),
  the Fejér lower bound `ct:P-lb` holds with error `n∫g₋ + (2/n)∫|g| + 6nM[f] c^{-20}(1 + (√(2π)W)^{-1})`;
* `hankel_P_lb_regime`: the same for all `c ≥ c₀`.

**Proved**, unconditional (`c > 3/2`, `ε = ±1`).
-/

@[expose] public section

open Set Filter Topology MeasureTheory Asymptotics
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtBoasWindow

set_option maxHeartbeats 1000000 in
theorem hankel_P_lb_regime_of {c ε : ℝ} (hc3 : 3 ≤ c)
    (hF1 : 156000000000 * Real.log c ^ 2 ≤ (c ^ (1 / 3 : ℝ)) ^ 3)
    (hF2 : 8320 * Real.log c ≤ c ^ (1 / 3 : ℝ))
    {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1)
    {τ0 τj Lj : ℝ} (hτ0 : 0 < τ0) (hτj1 : τ0 / 3 ≤ τj) (hτj2 : τj ≤ 3 * τ0) (hLj : 0 ≤ Lj)
    (hL1 : hankelEdgeM τ0 ≤ 1 + Lj) (hL2 : 1 + Lj ≤ 2 * (1 + hankelEdgeM τ0))
    (hlo : c ^ (-(1 / 3) : ℝ) ≤ hankelEdgeM τ0) (hhi : hankelEdgeM τ0 ≤ Real.log c)
    {n : ℕ} (hn : 2 ≤ n) (φ : ℝ) {Np2 W : ℝ} (hNpd : Np2 = 1000000 * (1 + Lj) * Real.log c)
    (hWd : W = √Np2 / (c * τj)) :
    -((n : ℝ) * ∫ x, max (-(gaussK W (x - hankelEdgeM τ0) * hankelHL c f x)) 0) -
        (2 / n) * (∫ x, |gaussK W (x - hankelEdgeM τ0) * hankelHL c f x|) -
        6 * n * hankelMass c f * ((c ^ 20)⁻¹ * (1 + √(π / (2 * π ^ 2 * W ^ 2)))) ≤
      ∫ x, gaussK W (x - hankelEdgeM τ0) * hankelHL c f x * (1 + 2 * Real.cos (c * τ0 * x + φ)) := by
  have hc0 : 0 < c := by linarith
  have hc1 : 1 < c := by linarith
  have hτj : 0 < τj := lt_of_lt_of_le (by positivity) hτj1
  have hlog1 : 1 ≤ Real.log c := by
    have : Real.exp 1 ≤ c := by
      have := Real.exp_one_lt_d9; linarith
    simpa using Real.log_le_log (Real.exp_pos 1) this
  set L0 : ℝ := hankelEdgeM τ0 with hL0
  set Δ : ℝ := hankelEdgeM (3 * τ0 / 2) - hankelEdgeM τ0 with hΔ
  obtain ⟨hτL, hΔge⟩ := hankelEdge_delta32_ge_L hτ0
  rw [← hL0] at hτL hΔge
  set q : ℝ := c ^ (1 / 3 : ℝ) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hc0 _
  have hqc : q ^ 3 = c := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hqinv : c ^ (-(1 / 3) : ℝ) = q⁻¹ := by rw [hq, Real.rpow_neg hc0.le]
  have hq1 : 1 ≤ q := by
    rw [hq]; exact Real.one_le_rpow hc1.le (by norm_num)
  have hL0pos : 0 < L0 := by
    have : 0 < c ^ (-(1 / 3) : ℝ) := Real.rpow_pos_of_pos hc0 _
    linarith
  set s : ℝ := min L0 1 with hs
  have hspos : 0 < s := lt_min hL0pos one_pos
  have hs1 : s ≤ 1 := min_le_right _ _
  have hsL : s ≤ L0 := min_le_left _ _
  set M : ℝ := max L0 1 with hM
  have hsM : s * M = L0 := by rw [hs, hM, min_mul_max]; ring
  have hM1 : 1 ≤ M := le_max_right _ _
  have hML : L0 ≤ M := le_max_left _ _
  have hqs : q⁻¹ ≤ s := by
    have h1 : q⁻¹ ≤ L0 := by rw [← hqinv]; exact hlo
    have h2 : q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq1
    exact le_min h1 h2
  have hsq : 1 ≤ s * q := by
    calc (1 : ℝ) = q⁻¹ * q := (inv_mul_cancel₀ hq0.ne').symm
      _ ≤ s * q := mul_le_mul_of_nonneg_right hqs hq0.le
  have hcs3 : 1 ≤ c * s ^ 3 := by
    rw [← hqc]
    have := one_le_pow₀ hsq (n := 3)
    calc (1 : ℝ) ≤ (s * q) ^ 3 := this
      _ = q ^ 3 * s ^ 3 := by ring
  have hcge : 156000000000 * Real.log c ^ 2 ≤ c := by have := hF1; rwa [hqc] at this
  have hτ0s : s ≤ τ0 := by
    by_contra h
    push Not at h
    nlinarith [hspos, hs1, hsL, hτL, hτ0, mul_pos hspos hspos]
  have hΔ' : 5 / 26 * s ≤ Δ := hΔge
  have hNp0 : 0 < Np2 := by
    have : 0 < 1 + Lj := by linarith
    rw [hNpd]; positivity
  have hW0 : 0 < W := by
    have : 0 < √Np2 := Real.sqrt_pos.2 hNp0
    rw [hWd]; positivity
  have hW2 : W ^ 2 = Np2 / (c * τj) ^ 2 := by
    rw [hWd, div_pow, Real.sq_sqrt hNp0.le]
  have hNe : W ^ 2 * c ^ 2 * τ0 ^ 2 = Np2 * (τ0 / τj) ^ 2 := by
    rw [hW2]; field_simp
  have hratio : 1 / 9 ≤ (τ0 / τj) ^ 2 := by
    have h : 1 / 3 ≤ τ0 / τj := by rw [le_div_iff₀ hτj]; linarith
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 3) h 2
    linarith only [this]
  have hNp9 : Np2 ≤ 9 * (W ^ 2 * c ^ 2 * τ0 ^ 2) := by
    rw [hNe]
    have := mul_le_mul_of_nonneg_left hratio hNp0.le
    linarith
  have hM4 : 1 + Lj ≤ 4 * M := by linarith
  have hMLj : M ≤ 1 + Lj := max_le hL1 (by linarith)
  have hlogc : 0 < Real.log c := by linarith
  -- (i)
  have hR1 : 40 * Real.log c ≤ Δ ^ 2 / (4 * W ^ 2) := by
    have hWp : 0 < 4 * W ^ 2 := by positivity
    rw [le_div_iff₀ hWp, hW2]
    have hcτ : 0 < (c * τj) ^ 2 := by positivity
    have key : 160 * Real.log c * Np2 ≤ Δ ^ 2 * (c * τj) ^ 2 := by
      have hD2 : (5 / 26 * s) ^ 2 ≤ Δ ^ 2 := pow_le_pow_left₀ (by positivity) hΔ' 2
      have hT : c ^ 2 * L0 / 9 ≤ (c * τj) ^ 2 := by
        have : (c * (τ0 / 3)) ^ 2 ≤ (c * τj) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hτj1 hc0.le) 2
        have e : (c * (τ0 / 3)) ^ 2 = c ^ 2 * τ0 ^ 2 / 9 := by ring
        have : c ^ 2 * τ0 ^ 2 / 9 ≥ c ^ 2 * L0 / 9 := by
          have := mul_le_mul_of_nonneg_left hτL (sq_nonneg c); linarith
        linarith
      have h3 : (5 / 26 * s) ^ 2 * (c ^ 2 * L0 / 9) ≤ Δ ^ 2 * (c * τj) ^ 2 :=
        mul_le_mul hD2 hT (by positivity) (sq_nonneg _)
      have h4 : (5 / 26 * s) ^ 2 * (c ^ 2 * L0 / 9) = 25 / 6084 * (M * c * (c * s ^ 3)) := by
        rw [← hsM]; ring
      have h5 : M * c ≤ M * c * (c * s ^ 3) := by
        have : 0 ≤ M * c := by positivity
        calc M * c = M * c * 1 := (mul_one _).symm
          _ ≤ M * c * (c * s ^ 3) := mul_le_mul_of_nonneg_left hcs3 this
      have h6 : 156000000000 * Real.log c ^ 2 * M ≤ c * M := mul_le_mul_of_nonneg_right hcge (by linarith)
      have h7 : Np2 = 1000000 * (1 + Lj) * Real.log c := hNpd
      have h8 : 160 * Real.log c * Np2 ≤ 640000000 * M * Real.log c ^ 2 := by
        rw [h7]
        have := mul_le_mul_of_nonneg_left hM4 (by positivity : (0 : ℝ) ≤ 160000000 * Real.log c ^ 2)
        linarith only [this]
      have hpos : 0 ≤ Real.log c ^ 2 * M := by positivity
      linarith only [h3, h4, h5, h6, h8, hpos]
    have : 40 * Real.log c * (4 * (Np2 / (c * τj) ^ 2)) = 160 * Real.log c * Np2 / (c * τj) ^ 2 := by ring
    rw [this, div_le_iff₀ hcτ]
    exact key
  -- (ii)
  have hR2 : 40 * Real.log c ≤ Np2 * Δ / (1200 * hankelEdgeM τ0) := by
    rw [← hL0, le_div_iff₀ (by positivity)]
    have h1 : 1000000 * M * Real.log c * (5 / 26 * s) ≤ Np2 * Δ := by
      have a1 : 1000000 * M * Real.log c ≤ Np2 := by
        have : M * Real.log c ≤ (1 + Lj) * Real.log c := mul_le_mul_of_nonneg_right hMLj hlogc.le
        have h7 : Np2 = 1000000 * (1 + Lj) * Real.log c := hNpd
        rw [h7]; nlinarith [this]
      exact mul_le_mul a1 hΔ' (by positivity) hNp0.le
    have e : 1000000 * M * Real.log c * (5 / 26 * s) = 1000000 * 5 / 26 * L0 * Real.log c := by
      rw [← hsM]; ring
    have := mul_pos hL0pos hlogc
    linarith only [h1, e, this]
  -- (iii)
  have hq3 : q ≤ c * s ^ 2 := by
    have : q * (s * q) ^ 2 = c * s ^ 2 := by rw [← hqc]; ring
    rw [← this]
    nlinarith [one_le_pow₀ hsq (n := 2), hq0]
  have hR3 : 40 * Real.log c ≤ c * τ0 * Δ / 40 := by
    rw [le_div_iff₀ (by norm_num)]
    have h1 : c * s * (5 / 26 * s) ≤ c * τ0 * Δ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hτ0s hc0.le) hΔ' (by positivity) (by positivity)
    linarith only [hq3, hF2, h1, hlogc]
  have hR4 : 40 * Real.log c ≤ c * Δ / 4 := by
    rw [le_div_iff₀ (by norm_num)]
    have h1 : c * (5 / 26 * s) ≤ c * Δ := mul_le_mul_of_nonneg_left hΔ' hc0.le
    have h2 : q ≤ c * s := by
      have : c * s = q ^ 2 * (s * q) := by rw [← hqc]; ring
      rw [this]
      nlinarith [hsq, hq1]
    linarith only [hF2, h1, h2, hlogc]
  -- big
  have hτc : τ0 ≤ c := by
    have h := hankelEdgeM_sub_log_mono (le_refl (0 : ℝ)) hτ0.le
    simp only [hankelEdgeM_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      Real.log_one, zero_div] at h
    have h2 : Real.log (1 + τ0 ^ 2) ≤ Real.log (c ^ 2) := by
      rw [Real.log_pow]; push_cast; linarith
    have h3 := (Real.log_le_log_iff (by positivity) (by positivity)).1 h2
    nlinarith only [sq_nonneg τ0, hτ0, hc0, h3]
  have hx : 22 * Real.log c ≤ W ^ 2 * c ^ 2 * τ0 ^ 2 / 10 := by
    rw [hNe]
    have h7 : Np2 = 1000000 * (1 + Lj) * Real.log c := hNpd
    have h8 : 1000000 * Real.log c ≤ Np2 := by
      rw [h7]
      have := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ 1 + Lj) (by positivity : (0 : ℝ) ≤ 1000000 * Real.log c)
      linarith only [this]
    have h9 := mul_le_mul_of_nonneg_left hratio hNp0.le
    linarith only [h8, h9, hlogc]
  have hBig : 3 * c * τ0 / (2 * π) * Real.exp (-(W ^ 2 * c ^ 2 * τ0 ^ 2 / 10)) ≤ ((c ^ 20)⁻¹ : ℝ) := by
    have hexp : Real.exp (-(W ^ 2 * c ^ 2 * τ0 ^ 2 / 10)) ≤ (c ^ 22)⁻¹ := by
      calc Real.exp (-(W ^ 2 * c ^ 2 * τ0 ^ 2 / 10)) ≤ Real.exp (-(22 * Real.log c)) :=
            Real.exp_le_exp.2 (by linarith only [hx])
        _ = (c ^ 22)⁻¹ := by
            rw [Real.exp_neg, show (22 * Real.log c) = ((22 : ℕ) : ℝ) * Real.log c by norm_num,
              Real.exp_nat_mul, Real.exp_log hc0]
    have hpi := Real.pi_pos
    have h3 : 3 * c * τ0 / (2 * π) ≤ c ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have a : c * τ0 ≤ c * c := mul_le_mul_of_nonneg_left hτc hc0.le
      have b : 3 * c ^ 2 ≤ c ^ 2 * (2 * π) := by
        have := mul_le_mul_of_nonneg_left (by linarith [Real.pi_gt_three] : (3 : ℝ) ≤ 2 * π) (sq_nonneg c)
        linarith only [this]
      nlinarith only [a, b]
    have h4 : c ^ 2 * (c ^ 22)⁻¹ = (c ^ 20)⁻¹ := by
      have : c ^ 22 = c ^ 2 * c ^ 20 := by ring
      rw [this, mul_inv]; field_simp
    calc 3 * c * τ0 / (2 * π) * Real.exp (-(W ^ 2 * c ^ 2 * τ0 ^ 2 / 10)) ≤ c ^ 2 * (c ^ 22)⁻¹ :=
          mul_le_mul h3 hexp (Real.exp_pos _).le (by positivity)
      _ = (c ^ 20)⁻¹ := h4
  exact hankel_P_lb (by linarith) hf hε hW0 hτ0 hNp0 hNp9 hR1 hR2 hR3 hR4 hBig hn φ

/-- The two largeness conditions of `hankel_P_lb_regime_of` hold for all large `c`. -/
theorem regime_large : ∃ c0 : ℝ, 3 ≤ c0 ∧ ∀ c : ℝ, c0 ≤ c →
    156000000000 * Real.log c ^ 2 ≤ (c ^ (1 / 3 : ℝ)) ^ 3 ∧ 8320 * Real.log c ≤ c ^ (1 / 3 : ℝ) := by
  have h1 : (fun x : ℝ => Real.log x ^ 2) =o[atTop] id := by
    simpa using Real.isLittleO_pow_log_id_atTop (n := 2)
  have h2 : Real.log =o[atTop] fun x : ℝ => x ^ (1 / 3 : ℝ) := isLittleO_log_rpow_atTop (by norm_num)
  have e1 := h1.def (by norm_num : (0 : ℝ) < 1 / 156000000000)
  have e2 := h2.def (by norm_num : (0 : ℝ) < 1 / 8320)
  obtain ⟨a, ha⟩ := eventually_atTop.1 (e1.and (e2.and (eventually_ge_atTop (3 : ℝ))))
  refine ⟨max a 3, le_max_right _ _, fun c hc => ?_⟩
  obtain ⟨u1, u2, u3⟩ := ha c (le_trans (le_max_left _ _) hc)
  have hc0 : 0 < c := by linarith [le_max_right a 3]
  have hq : (c ^ (1 / 3 : ℝ)) ^ 3 = c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  rw [hq]
  have hq0 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  simp only [Real.norm_eq_abs, id, abs_of_pos hc0, abs_pow, sq_abs, abs_of_pos hq0] at u1 u2
  refine ⟨?_, ?_⟩
  · have : |Real.log c| ^ 2 = Real.log c ^ 2 := sq_abs _
    rw [← this]; linarith
  · have := le_abs_self (Real.log c); linarith

/-- info: 'FormalResearch.SignUncertainty.hankel_P_lb_regime_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_P_lb_regime_of

/-- info: 'FormalResearch.SignUncertainty.regime_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms regime_large

end FormalResearch.SignUncertainty
