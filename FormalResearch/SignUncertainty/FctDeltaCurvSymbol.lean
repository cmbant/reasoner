/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctThetaBounds
public import FormalResearch.SignUncertainty.FctMInvSymbol
public import FormalResearch.SignUncertainty.FctExpDecay

/-!
# `Δ_curv` as a `t`-symbol, uniformly in `c` (Lemma FCT.7b (b), factor `D`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (b); `fct:comp-D` (1), `(fct:th-inner)`, `(fct:th-tail)`:
`Δ_curv = (1/2c)(ϑ''/m' - ϑ'/m)`, `ϑ = ϑ_{D₀}`.

`deltaCurv_symW`: for `lam > 0` (`lam τ₁` is the left end of the range, `τ₀(3δ_L/4) ≥ lam τ₁`) and `τ₁ ≤ τ_c`,
`Δ_curv ∈ SymW [lam τ₁, ∞) (C_w τ₁³ (1+x)^{-8})` with `K, C_w` independent of `c, α, τ₁`.
* `x ≤ 12τ₁`: `ϑ'' = O(1)·x^{-k}`, `ϑ' = O(τ₁) x^{-k}`, `1/m' = x A(x) ≲ x^{-1}`, `1/m ≲ x^{-2}`, so `Δ_curv ≲ τ₁⁴(1/(lam τ₁))`;
* `x ≥ 12τ₁`: `ϑ^{(r)} ≲ τ₁³ x^{-(r+1)} e^{-πx/2}`, so `Δ_curv ≲ τ₁⁷ x^{-2} max(1, x^{-2}) e^{-πx/2}`.

`deltaCurv_contDiffOn`: `Δ_curv` is `C^∞` on `(0, ∞)`.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Finset
open scoped ContDiff Real

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter
  FormalResearch.SignUncertainty.FctCompD FormalResearch.SignUncertainty.FctMoment

lemma inv_pow_le_scale {τ x a : ℝ} (hτ : 0 < τ) (hx : 0 < x) (hxa : x ≤ a * τ) (k : ℕ) :
    (τ ^ k)⁻¹ ≤ a ^ k * (x ^ k)⁻¹ := by
  have h10 : x ^ k ≤ (a * τ) ^ k := pow_le_pow_left₀ hx.le hxa k
  rw [mul_pow] at h10
  have hxr0 : 0 < x ^ k := pow_pos hx k
  have ht0 : 0 < τ ^ k := pow_pos hτ k
  have ha0 : 0 < a ^ k := pow_pos (by nlinarith) k
  calc (τ ^ k)⁻¹ = (a ^ k * (x ^ k)⁻¹) * (x ^ k / (a ^ k * τ ^ k)) := by field_simp
    _ ≤ (a ^ k * (x ^ k)⁻¹) * 1 := by
        gcongr
        rw [div_le_one (by positivity)]; exact h10
    _ = _ := mul_one _

lemma tail_weight_le {τ x : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hx : 12 * τ ≤ x) :
    τ ^ 4 * ((x ^ 2)⁻¹ * wA x) ≤ 1 := by
  have hx0 : 0 < x := by linarith
  unfold wA
  rcases le_total x 1 with h | h
  · have h1 : (1 : ℝ) ≤ (x ^ 2)⁻¹ := one_le_inv₀ (pow_pos hx0 2) |>.mpr (pow_le_one₀ hx0.le h)
    rw [max_eq_right h1]
    have h4 : τ ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ hτ.le (by linarith) 4
    calc τ ^ 4 * ((x ^ 2)⁻¹ * (x ^ 2)⁻¹) = τ ^ 4 / x ^ 4 := by field_simp
      _ ≤ 1 := (div_le_one (by positivity)).mpr h4
  · have h1 : (x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h)
    rw [max_eq_left h1, mul_one]
    exact (mul_le_mul (pow_le_one₀ hτ.le hτ1) h1 (inv_nonneg.mpr (sq_nonneg x)) zero_le_one).trans (by norm_num)

lemma deltaCurv_contDiffOn {c : ℝ} {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) :
    ContDiffOn ℝ ∞ (stripDeltaCurv c θ) (Ioi 0) := by
  have hd1 : ContDiff ℝ ∞ (deriv θ) := by
    have := contDiff_iteratedDeriv_infty hθ 1
    rwa [iteratedDeriv_one] at this
  have hd2 : ContDiff ℝ ∞ (iteratedDeriv 2 θ) := contDiff_iteratedDeriv_infty hθ 2
  have hmp : ContDiffOn ℝ ∞ uctMderiv (Ioi 0) :=
    CtMDeriv.contDiffOn_mPrime.congr (fun x hx => uctMderiv_eq_mPrime hx)
  unfold stripDeltaCurv
  exact contDiffOn_const.mul ((hd2.contDiffOn.div hmp (fun x hx => (uctMderiv_pos hx).ne')).sub
    (hd1.contDiffOn.div contDiffOn_uctM (fun x hx => (uctM_pos hx).ne')))

/-- **`Δ_curv` is a `t`-symbol on `[lam τ₁, ∞)`, uniformly in `c`.** -/
theorem deltaCurv_symW (kind : StripKernelChoice) (K4 : ℝ) (hK4 : 1 ≤ K4) {lam : ℝ} (hlam : 0 < lam) :
    ∃ (τc : ℝ) (K : ℕ → ℝ) (Cw : ℝ), 0 < τc ∧ τc ≤ 1 / 100 ∧ 0 ≤ Cw ∧ (∀ r, 0 ≤ K r) ∧
      ∀ {c α τ₁ : ℝ}, 0 < c → 0 < τ₁ → τ₁ ≤ τc → τ₁ ^ 4 * c = 1 → |α| ≤ τ₁ ^ 2 →
        SymW (Ici (lam * τ₁)) (fun x => Cw * τ₁ ^ 3 * ((1 + x) ^ 8)⁻¹) K
          (stripDeltaCurv c (fctThetaD (v0 kind K4 τ₁))) := by
  obtain ⟨τθ, Mi, Tt, hτθ, hτθ20, hMT, hθ⟩ := theta_bounds kind K4 hK4
  obtain ⟨Ku1, hu1⟩ := mDerivInv_symW
  obtain ⟨Ku2a, hu2a⟩ := mInv_symW_Ioc
  obtain ⟨Ku2b, hu2b⟩ := mInv_symW_all
  obtain ⟨C8, hC8, hexp8⟩ := pow_le_exp 8
  set Kg1a : ℕ → ℝ := fun k => Mi (k + 1) * 12 ^ k with hKg1a
  set Kg2a : ℕ → ℝ := fun k => Mi (k + 2) * 12 ^ k with hKg2a
  set Kg1b : ℕ → ℝ := fun k => Tt (k + 1) with hKg1b
  set Kg2b : ℕ → ℝ := fun k => Tt (k + 2) with hKg2b
  have hKg1a0 : ∀ k, 0 ≤ Kg1a k := fun k => mul_nonneg (hMT _).1 (by positivity)
  have hKg2a0 : ∀ k, 0 ≤ Kg2a k := fun k => mul_nonneg (hMT _).1 (by positivity)
  have hKg1b0 : ∀ k, 0 ≤ Kg1b k := fun k => (hMT _).2
  have hKg2b0 : ∀ k, 0 ≤ Kg2b k := fun k => (hMT _).2
  set KS1 : ℕ → ℝ := fun r => SymW.Kmul Kg2a Ku1 r + SymW.Kmul Kg1a Ku2a r with hKS1
  set KS2 : ℕ → ℝ := fun r => SymW.Kmul Kg2b Ku1 r + SymW.Kmul Kg1b Ku2b r with hKS2
  have hKm1 : ∀ r, 0 ≤ SymW.Kmul Kg2a Ku1 r := SymW.Kmul_nonneg hKg2a0 hu1.K_nonneg
  have hKm2 : ∀ r, 0 ≤ SymW.Kmul Kg1a Ku2a r := SymW.Kmul_nonneg hKg1a0 hu2a.K_nonneg
  have hKm3 : ∀ r, 0 ≤ SymW.Kmul Kg2b Ku1 r := SymW.Kmul_nonneg hKg2b0 hu1.K_nonneg
  have hKm4 : ∀ r, 0 ≤ SymW.Kmul Kg1b Ku2b r := SymW.Kmul_nonneg hKg1b0 hu2b.K_nonneg
  have hlami : 0 < lam⁻¹ := inv_pos.mpr hlam
  refine ⟨min τθ (1 / 100), fun r => max (KS1 r) (KS2 r), 128 * (lam⁻¹ + lam⁻¹ ^ 2) + C8, lt_min hτθ (by norm_num),
    min_le_right _ _, by positivity, fun r => le_max_of_le_left (add_nonneg (hKm1 r) (hKm2 r)), ?_⟩
  intro c α τ₁ hc hτ₁ hτ₁le hceq hαle
  have hτθ' : τ₁ ≤ τθ := hτ₁le.trans (min_le_left _ _)
  have hτ100 : τ₁ ≤ 1 / 100 := hτ₁le.trans (min_le_right _ _)
  have hτ1 : τ₁ ≤ 1 := by linarith
  have hc_inv : c⁻¹ = τ₁ ^ 4 := by
    rw [inv_eq_iff_eq_inv]; field_simp [hc.ne', hτ₁.ne'] at hceq ⊢; linarith
  obtain ⟨hθcd, hin, htail⟩ := hθ hc hτ₁ hτθ' hceq hαle
  set θ := fctThetaD (v0 kind K4 τ₁) with hθdef
  have hd1 : ContDiff ℝ ∞ (deriv θ) := by
    have := contDiff_iteratedDeriv_infty hθcd 1
    rwa [iteratedDeriv_one] at this
  have hd2 : ContDiff ℝ ∞ (iteratedDeriv 2 θ) := contDiff_iteratedDeriv_infty hθcd 2
  have hg1d : ∀ k, iteratedDeriv k (deriv θ) = iteratedDeriv (k + 1) θ := fun k => (iteratedDeriv_succ' ..).symm
  have hg2d : ∀ k, iteratedDeriv k (iteratedDeriv 2 θ) = iteratedDeriv (k + 2) θ := fun k => by
    rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, ← Function.iterate_add_apply]
  have hac : |1 / (2 * c)| = τ₁ ^ 4 / 2 := by
    rw [abs_of_pos (by positivity), show 1 / (2 * c) = c⁻¹ / 2 by field_simp, hc_inv]
  have hEq : ∀ x : ℝ, 0 < x → stripDeltaCurv c θ x =
      1 / (2 * c) * (iteratedDeriv 2 θ x * (uctMderiv x)⁻¹ + (-1) * (deriv θ x * (uctM x)⁻¹)) := by
    intro x _
    unfold stripDeltaCurv
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  -- Region `S₁ = [lam τ₁, 12 τ₁]`
  have hpos1 : ∀ x ∈ Icc (lam * τ₁) (12 * τ₁), 0 < x := fun x hx => lt_of_lt_of_le (by positivity) hx.1
  have hS1sub : Icc (lam * τ₁) (12 * τ₁) ⊆ Ioc (0 : ℝ) (1 / 8) := fun x hx => ⟨hpos1 x hx, by linarith [hx.2]⟩
  have hg1S1 : SymW (Icc (lam * τ₁) (12 * τ₁)) (fun _ => τ₁) Kg1a (deriv θ) :=
  { pos := hpos1
    smooth := ⟨univ, isOpen_univ, subset_univ _, hd1.contDiffOn⟩
    K_nonneg := hKg1a0
    w_nonneg := fun _ _ => hτ₁.le
    bound := fun k x hx => by
      rw [hg1d]
      refine (hin (k + 1) x (hpos1 x hx) hx.2).trans ?_
      have e : τ₁ ^ 2 * (τ₁ ^ (k + 1))⁻¹ = τ₁ * (τ₁ ^ k)⁻¹ := by
        rw [pow_succ]; field_simp; ring
      rw [e]
      have h := inv_pow_le_scale hτ₁ (hpos1 x hx) hx.2 k
      have hM := (hMT (k + 1)).1
      calc Mi (k + 1) * (τ₁ * (τ₁ ^ k)⁻¹) ≤ Mi (k + 1) * (τ₁ * (12 ^ k * (x ^ k)⁻¹)) := by gcongr
        _ = Kg1a k * τ₁ * (x ^ k)⁻¹ := by rw [hKg1a]; ring }
  have hg2S1 : SymW (Icc (lam * τ₁) (12 * τ₁)) (fun _ => (1 : ℝ)) Kg2a (iteratedDeriv 2 θ) :=
  { pos := hpos1
    smooth := ⟨univ, isOpen_univ, subset_univ _, hd2.contDiffOn⟩
    K_nonneg := hKg2a0
    w_nonneg := fun _ _ => zero_le_one
    bound := fun k x hx => by
      rw [hg2d]
      refine (hin (k + 2) x (hpos1 x hx) hx.2).trans ?_
      have e : τ₁ ^ 2 * (τ₁ ^ (k + 2))⁻¹ = (τ₁ ^ k)⁻¹ := by
        rw [pow_add]; field_simp
      rw [e]
      have h := inv_pow_le_scale hτ₁ (hpos1 x hx) hx.2 k
      have hM := (hMT (k + 2)).1
      calc Mi (k + 2) * (τ₁ ^ k)⁻¹ ≤ Mi (k + 2) * (12 ^ k * (x ^ k)⁻¹) := by gcongr
        _ = Kg2a k * 1 * (x ^ k)⁻¹ := by rw [hKg2a]; ring }
  have hu1S1 := (hu1.mono_set (fun x hx => hpos1 x hx)).of_le (w' := fun _ => (lam * τ₁)⁻¹) (K' := Ku1)
    (fun x hx => by
      have hx0 := hpos1 x hx
      have hx1 : x ≤ 1 := by linarith [hx.2]
      have h1 : wA x = (x ^ 2)⁻¹ := by
        unfold wA
        exact max_eq_right (one_le_inv₀ (pow_pos hx0 2) |>.mpr (pow_le_one₀ hx0.le hx1))
      show |(1 : ℝ)| * x ^ (1 : ℝ) * wA x ≤ (lam * τ₁)⁻¹
      rw [h1, Real.rpow_one, abs_one, one_mul]
      calc x * (x ^ 2)⁻¹ = x⁻¹ := by field_simp
        _ ≤ (lam * τ₁)⁻¹ := inv_anti₀ (by positivity) hx.1) (fun _ => le_rfl)
  have hu2S1 := (hu2a.mono_set hS1sub).of_le (w' := fun _ => ((lam * τ₁) ^ 2)⁻¹) (K' := Ku2a)
    (fun x hx => inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hx.1 2)) (fun _ => le_rfl)
  set W₁ : ℝ := (lam⁻¹ + lam⁻¹ ^ 2) * τ₁⁻¹ with hW₁
  have hP1 := (hg2S1.mul hu1S1).of_le (w' := fun _ => W₁) (K' := SymW.Kmul Kg2a Ku1) (fun x hx => by
    show 1 * (lam * τ₁)⁻¹ ≤ W₁
    rw [hW₁, one_mul, mul_inv]
    have : 0 ≤ lam⁻¹ ^ 2 * τ₁⁻¹ := by positivity
    nlinarith) (fun _ => le_rfl)
  have hP2 := ((hg1S1.mul hu2S1).smul (-1)).of_le (w' := fun _ => W₁) (K' := SymW.Kmul Kg1a Ku2a) (fun x hx => by
    show |(-1 : ℝ)| * (τ₁ * ((lam * τ₁) ^ 2)⁻¹) ≤ W₁
    rw [hW₁, abs_neg, abs_one, one_mul, mul_pow, mul_inv]
    have e : τ₁ * ((lam ^ 2)⁻¹ * (τ₁ ^ 2)⁻¹) = lam⁻¹ ^ 2 * τ₁⁻¹ := by field_simp
    rw [e]
    have : 0 ≤ lam⁻¹ * τ₁⁻¹ := by positivity
    nlinarith) (fun _ => le_rfl)
  have hΔ1 := ((hP1.add hP2).smul (1 / (2 * c))).congr (U := Ioi 0) isOpen_Ioi (fun x hx => hpos1 x hx)
    (g := stripDeltaCurv c θ) (fun x hx => by
      have := hEq x hx
      simp only [this])
  have hΔ1' := hΔ1.of_le (w' := fun x => (128 * (lam⁻¹ + lam⁻¹ ^ 2) + C8) * τ₁ ^ 3 * ((1 + x) ^ 8)⁻¹)
    (K' := fun r => max (KS1 r) (KS2 r)) (fun x hx => by
      have hx0 := hpos1 x hx
      have hx1 : 1 + x ≤ 2 := by linarith [hx.2]
      have h8 : (1 + x) ^ 8 ≤ 2 ^ 8 := pow_le_pow_left₀ (by linarith) hx1 8
      have hD : 0 < (1 + x) ^ 8 := by positivity
      have h256 : (1 / 256 : ℝ) ≤ ((1 + x) ^ 8)⁻¹ := by
        rw [one_div]; exact inv_anti₀ hD (by norm_num at h8 ⊢; linarith)
      show |1 / (2 * c)| * W₁ ≤ _
      rw [hac, hW₁]
      have e : τ₁ ^ 4 / 2 * ((lam⁻¹ + lam⁻¹ ^ 2) * τ₁⁻¹) = (lam⁻¹ + lam⁻¹ ^ 2) / 2 * τ₁ ^ 3 := by field_simp
      rw [e]
      have h3 : 0 ≤ τ₁ ^ 3 := by positivity
      have h4 : 0 ≤ C8 := hC8.le
      have h5 : 0 ≤ lam⁻¹ + lam⁻¹ ^ 2 := by positivity
      nlinarith [mul_nonneg h3 h5, mul_nonneg h3 h4, mul_nonneg (mul_nonneg h3 h5) (sub_nonneg.mpr h256),
        mul_nonneg (mul_nonneg h3 h4) (le_trans (by norm_num) h256)])
    (fun r => le_max_left (KS1 r) (KS2 r))
  -- Region `S₂ = [12 τ₁, ∞)`
  have hpos2 : ∀ x ∈ Ici (12 * τ₁), 0 < x := fun x hx => lt_of_lt_of_le (by positivity) hx
  have hg1S2 : SymW (Ici (12 * τ₁)) (fun x => τ₁ ^ 3 * ((x ^ 2)⁻¹ * Real.exp (-(π * x / 2)))) Kg1b (deriv θ) :=
  { pos := hpos2
    smooth := ⟨univ, isOpen_univ, subset_univ _, hd1.contDiffOn⟩
    K_nonneg := hKg1b0
    w_nonneg := fun x hx => by have := hpos2 x hx; positivity
    bound := fun k x hx => by
      rw [hg1d]
      refine (htail (k + 1) x hx).trans (le_of_eq ?_)
      have e : (x ^ (k + 1 + 1))⁻¹ = (x ^ 2)⁻¹ * (x ^ k)⁻¹ := by
        rw [show k + 1 + 1 = 2 + k by ring, pow_add, mul_inv]
      rw [e, hKg1b]; ring }
  have hg2S2 : SymW (Ici (12 * τ₁)) (fun x => τ₁ ^ 3 * ((x ^ 3)⁻¹ * Real.exp (-(π * x / 2)))) Kg2b (iteratedDeriv 2 θ) :=
  { pos := hpos2
    smooth := ⟨univ, isOpen_univ, subset_univ _, hd2.contDiffOn⟩
    K_nonneg := hKg2b0
    w_nonneg := fun x hx => by have := hpos2 x hx; positivity
    bound := fun k x hx => by
      rw [hg2d]
      refine (htail (k + 2) x hx).trans (le_of_eq ?_)
      have e : (x ^ (k + 2 + 1))⁻¹ = (x ^ 3)⁻¹ * (x ^ k)⁻¹ := by
        rw [show k + 2 + 1 = 3 + k by ring, pow_add, mul_inv]
      rw [e, hKg2b]; ring }
  have hS2sub : Ici (12 * τ₁) ⊆ Ioi (0 : ℝ) := fun x hx => hpos2 x hx
  set W₂ : ℝ → ℝ := fun x => τ₁ ^ 3 * ((x ^ 2)⁻¹ * wA x * Real.exp (-(π * x / 2))) with hW₂
  have hQ1 := (hg2S2.mul (hu1.mono_set hS2sub)).of_le (w' := W₂) (K' := SymW.Kmul Kg2b Ku1) (fun x hx => by
    have hx0 := hpos2 x hx
    show τ₁ ^ 3 * ((x ^ 3)⁻¹ * Real.exp (-(π * x / 2))) * (|(1 : ℝ)| * x ^ (1 : ℝ) * wA x) ≤ W₂ x
    rw [hW₂, Real.rpow_one, abs_one]
    refine le_of_eq ?_
    field_simp) (fun _ => le_rfl)
  have hQ2 := ((hg1S2.mul (hu2b.mono_set hS2sub)).smul (-1)).of_le (w' := W₂) (K' := SymW.Kmul Kg1b Ku2b) (fun x hx => by
    have hx0 := hpos2 x hx
    show |(-1 : ℝ)| * (τ₁ ^ 3 * ((x ^ 2)⁻¹ * Real.exp (-(π * x / 2))) * wA x) ≤ W₂ x
    rw [hW₂, abs_neg, abs_one]
    refine le_of_eq ?_
    ring) (fun _ => le_rfl)
  have hΔ2 := ((hQ1.add hQ2).smul (1 / (2 * c))).congr (U := Ioi 0) isOpen_Ioi hS2sub
    (g := stripDeltaCurv c θ) (fun x hx => by
      have := hEq x hx
      simp only [this])
  have hΔ2' := hΔ2.of_le (w' := fun x => (128 * (lam⁻¹ + lam⁻¹ ^ 2) + C8) * τ₁ ^ 3 * ((1 + x) ^ 8)⁻¹)
    (K' := fun r => max (KS1 r) (KS2 r)) (fun x hx => by
      have hx0 := hpos2 x hx
      have hD : 0 < (1 + x) ^ 8 := by positivity
      have hex : Real.exp (-(π * x / 2)) ≤ C8 * ((1 + x) ^ 8)⁻¹ := by
        have h := hexp8 x hx0.le
        rw [← div_eq_mul_inv, le_div_iff₀ hD]
        have e1 : Real.exp (-(π * x / 2)) * Real.exp (π * x / 2) = 1 := by rw [← Real.exp_add]; simp
        calc Real.exp (-(π * x / 2)) * (1 + x) ^ 8 ≤ Real.exp (-(π * x / 2)) * (C8 * Real.exp (π * x / 2)) :=
              mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
          _ = C8 := by rw [mul_left_comm, e1, mul_one]
      have hT := tail_weight_le hτ₁ hτ1 hx
      show |1 / (2 * c)| * W₂ x ≤ _
      rw [hac, hW₂]
      have e : τ₁ ^ 4 / 2 * (τ₁ ^ 3 * ((x ^ 2)⁻¹ * wA x * Real.exp (-(π * x / 2)))) =
          τ₁ ^ 3 * (τ₁ ^ 4 * ((x ^ 2)⁻¹ * wA x) / 2 * Real.exp (-(π * x / 2))) := by ring
      rw [e]
      have h3 : 0 ≤ τ₁ ^ 3 := by positivity
      have h5 : 0 ≤ lam⁻¹ + lam⁻¹ ^ 2 := by positivity
      have hE0 := (Real.exp_pos (-(π * x / 2))).le
      have hDi : 0 ≤ ((1 + x) ^ 8)⁻¹ := by positivity
      have h6 : τ₁ ^ 4 * ((x ^ 2)⁻¹ * wA x) / 2 * Real.exp (-(π * x / 2)) ≤ C8 * ((1 + x) ^ 8)⁻¹ := by
        calc τ₁ ^ 4 * ((x ^ 2)⁻¹ * wA x) / 2 * Real.exp (-(π * x / 2)) ≤ 1 / 2 * Real.exp (-(π * x / 2)) := by
              gcongr
          _ ≤ Real.exp (-(π * x / 2)) := by nlinarith
          _ ≤ _ := hex
      calc τ₁ ^ 3 * (τ₁ ^ 4 * ((x ^ 2)⁻¹ * wA x) / 2 * Real.exp (-(π * x / 2))) ≤ τ₁ ^ 3 * (C8 * ((1 + x) ^ 8)⁻¹) :=
            mul_le_mul_of_nonneg_left h6 h3
        _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg h3 h5) hDi, mul_nonneg h3 hDi])
    (fun r => le_max_right (KS1 r) (KS2 r))
  have hU := hΔ1'.union hΔ2'
  refine (hU.mono_set (fun x hx => ?_)).of_le (fun _ _ => le_rfl) (fun r => by simp)
  rcases le_total x (12 * τ₁) with h | h
  · exact Or.inl ⟨hx, h⟩
  · exact Or.inr h

/-- info: 'FormalResearch.SignUncertainty.FctSym.deltaCurv_symW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deltaCurv_symW

end FormalResearch.SignUncertainty.FctSym
