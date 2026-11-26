/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctMLarge
public import FormalResearch.SignUncertainty.FctExpDecay
public import FormalResearch.SignUncertainty.FctSymExpm1

/-!
# `r₀` as a `t`-symbol on `(0, ∞)` (Lemma FCT.7b (b), factor `R`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (b) (`fct:bump-sym-check`) and `fct:comp-D` (1);
`r₀(t) = α_osc |H₀(it)| m(t)^{3/2} / (α_fl m'(t))`.

`stripR0_t_symbol`: `r₀` is `C^∞` on `(0, ∞)` and, with one constant sequence `P` (depending only on the kernel `H₀`),
`|t^j ∂^j (r₀ - 1)| ≤ P_j min(t², 1)` and `|t^j ∂^j r₀| ≤ P_j min(1, t^{-8})` for all `t > 0`.

* `t ≤ 1/8`: `r₀ = exp(-f₀)` with `f₀ = -log r₀^{smooth}` even and smooth, so `|∂^r f₀| ≤ C_r t^{2-r}` (`even_smooth_target_bounds`);
* `t ≥ 1/8`: `r₀ = (α_osc/α_fl) F(t) m^{3/2} (t A(t))`, `F = ‖H₀(it)‖ = Φ(e^{-πt})` with `Φ` rational (`symW_comp_expNeg`),
  `m^{3/2}` (`mPow32_symW`), `A = 1/(t m')` (`tauA_symW`).

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Finset
open scoped ContDiff Real Nat

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter
  FormalResearch.SignUncertainty.FctCompD FormalResearch.SignUncertainty.FctMoment

/-! ### Small `t` -/

/-- `r₀ - 1 ∈ SymW (0, 1/8] t²`. -/
lemma r0_small_symW (kind : StripKernelChoice) :
    ∃ K : ℕ → ℝ, SymW (Ioc (0 : ℝ) (1 / 8)) (fun x => x ^ 2) K (fun x => stripR0 kind x - 1) := by
  choose C hC0 hC using even_smooth_target_bounds (contDiffOn_f0Base kind) (fun t ht => f0Base_even ht)
    (f0Base_zero kind)
  have hf : SymW (Ioc (0 : ℝ) (1 / 8)) (fun x => x ^ 2) (fun r => C r * 3 ^ r) (f0Base kind) :=
  { pos := fun x hx => hx.1
    smooth := ⟨Ioo (-1 / 4) (1 / 4), isOpen_Ioo, fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩, contDiffOn_f0Base kind⟩
    K_nonneg := fun r => mul_nonneg (hC0 r) (by positivity)
    w_nonneg := fun x _ => sq_nonneg x
    bound := fun r x hx => by
      have hx0 : 0 < x := hx.1
      have hτ : 0 < x / 3 := by positivity
      have h := hC r (τ₁ := x / 3) hτ (by linarith [hx.2]) x ⟨by linarith, by linarith⟩
      refine h.trans ?_
      have e : (x / 3) ^ ((2 : ℤ) - (r : ℤ)) = (x / 3) ^ 2 / (x / 3) ^ r := by
        rw [zpow_sub₀ hτ.ne']; simp
      rw [e, div_pow, div_pow]
      have hx3 : (0 : ℝ) < 3 ^ r := by positivity
      have hxr : 0 < x ^ r := pow_pos hx0 r
      have hC0r := hC0 r
      field_simp
      have : x ^ 2 * 3 ^ r * (x ^ r) ≤ x ^ 2 * 3 ^ r * 9 * (x ^ r) := by nlinarith [mul_pos (pow_pos hx0 2) hx3]
      nlinarith [mul_pos (mul_pos (pow_pos hx0 2) hx3) hxr] }
  have hg := (hf.smul (-1)).of_le (w' := fun x => x ^ 2) (K' := fun r => C r * 3 ^ r)
    (fun x hx => by simp) (fun _ => le_rfl)
  have hex := symW_exp_sub_one (B := 1) hg (fun x hx => by
    have := hx.2
    nlinarith [hx.1])
  obtain ⟨K, hK⟩ : ∃ K, SymW (Ioc (0 : ℝ) (1 / 8)) (fun x => x ^ 2) K (fun x => Real.exp (-1 * f0Base kind x) - 1) := ⟨_, hex⟩
  refine ⟨K, hK.congr (U := Ioo 0 (1 / 4)) isOpen_Ioo (fun x hx => ⟨hx.1, by linarith [hx.2]⟩) (fun x hx => ?_)⟩
  have habs : |x| < 1 / 4 := by rw [abs_of_pos hx.1]; exact hx.2
  have hpos := r0Smooth_pos (kind := kind) habs
  simp only [f0Base]
  rw [show -1 * -Real.log (r0Smooth kind x) = Real.log (r0Smooth kind x) by ring, Real.exp_log hpos,
    r0Smooth_eq_stripR0 habs]

/-! ### The decaying factor `F(t) = ‖H₀(it)‖` -/

/-- `π² y / (1 - y)²`, with `y = e^{-πt}`: `π²/(4 sinh²(πt/2))`. -/
noncomputable def phiSh (y : ℝ) : ℝ := π ^ 2 * y / (1 - y) ^ 2

/-- `π² y / (1 + y)²`, with `y = e^{-πt}`: `π²/(4 cosh²(πt/2))`. -/
noncomputable def phiCh (y : ℝ) : ℝ := π ^ 2 * y / (1 + y) ^ 2

lemma phiSh_eq {t : ℝ} (ht : 0 < t) : π ^ 2 / (4 * Real.sinh (π * t / 2) ^ 2) = phiSh (Real.exp (-π * t)) := by
  set E := Real.exp (π * t / 2) with hE
  have hE1 : 1 < E := Real.one_lt_exp_iff.mpr (by positivity)
  have hE0 : 0 < E := by linarith
  have hu : Real.exp (-π * t) = (E * E)⁻¹ := by
    rw [← Real.exp_add, ← Real.exp_neg]; congr 2; ring
  have hs : Real.sinh (π * t / 2) = (E - E⁻¹) / 2 := by
    rw [Real.sinh_eq, ← Real.exp_neg]
  rw [hu, hs]
  unfold phiSh
  have h1 : E * E - 1 ≠ 0 := by nlinarith
  have h2 : E ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp
  ring

lemma phiCh_eq {t : ℝ} (ht : 0 < t) : π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2) = phiCh (Real.exp (-π * t)) := by
  set E := Real.exp (π * t / 2) with hE
  have hE1 : 1 < E := Real.one_lt_exp_iff.mpr (by positivity)
  have hE0 : 0 < E := by linarith
  have hu : Real.exp (-π * t) = (E * E)⁻¹ := by
    rw [← Real.exp_add, ← Real.exp_neg]; congr 2; ring
  have hs : Real.cosh (π * t / 2) = (E + E⁻¹) / 2 := by
    rw [Real.cosh_eq, ← Real.exp_neg]
  rw [hu, hs]
  unfold phiCh
  have h1 : E * E + 1 ≠ 0 := by nlinarith
  field_simp
  ring

lemma u0_lt_one : Real.exp (-π / 8) < 1 := by
  rw [Real.exp_lt_one_iff]; have := Real.pi_pos; linarith

lemma phiSh_symW : ∃ K : ℕ → ℝ, SymW (Ici (1 / 8 : ℝ)) (fun x => Real.exp (-(π * x / 2))) K
    (fun x => π ^ 2 / (4 * Real.sinh (π * x / 2) ^ 2)) := by
  have hu0 := u0_lt_one
  have hΦ : ContDiffOn ℝ ∞ phiSh (Ioo (-1) 1) := by
    unfold phiSh
    refine (contDiffOn_const.mul contDiffOn_id).div ((contDiffOn_const.sub contDiffOn_id).pow 2) (fun y hy => ?_)
    have : 0 < 1 - y := by linarith [hy.2]
    positivity
  obtain ⟨K, hK⟩ := symW_comp_expNeg (L := π ^ 2 / (1 - Real.exp (-π / 8)) ^ 2) hΦ (by
    have : 0 < 1 - Real.exp (-π / 8) := by linarith
    positivity) (fun y hy => by
    unfold phiSh
    have h1 : 0 < 1 - Real.exp (-π / 8) := by linarith
    have h2 : 1 - Real.exp (-π / 8) ≤ 1 - y := by linarith [hy.2]
    have h3 : (1 - Real.exp (-π / 8)) ^ 2 ≤ (1 - y) ^ 2 := pow_le_pow_left₀ h1.le h2 2
    have hy0 : 0 ≤ y := hy.1
    rw [abs_of_nonneg (by positivity)]
    calc π ^ 2 * y / (1 - y) ^ 2 ≤ π ^ 2 * y / (1 - Real.exp (-π / 8)) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h3
      _ = _ := by ring)
  exact ⟨K, hK.congr (U := Ioi 0) isOpen_Ioi (fun x hx => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ x from hx))
    (fun x hx => (phiSh_eq hx).symm)⟩

lemma phiCh_symW : ∃ K : ℕ → ℝ, SymW (Ici (1 / 8 : ℝ)) (fun x => Real.exp (-(π * x / 2))) K
    (fun x => π ^ 2 / (4 * Real.cosh (π * x / 2) ^ 2)) := by
  have hu0 := u0_lt_one
  have hΦ : ContDiffOn ℝ ∞ phiCh (Ioo (-1) 1) := by
    unfold phiCh
    refine (contDiffOn_const.mul contDiffOn_id).div ((contDiffOn_const.add contDiffOn_id).pow 2) (fun y hy => ?_)
    have : 0 < 1 + y := by linarith [hy.1]
    positivity
  obtain ⟨K, hK⟩ := symW_comp_expNeg (L := π ^ 2) hΦ (by positivity) (fun y hy => by
    unfold phiCh
    have h2 : 0 ≤ y := hy.1
    rw [abs_of_nonneg (by positivity)]
    have h3 : 1 ≤ (1 + y) ^ 2 := by nlinarith
    calc π ^ 2 * y / (1 + y) ^ 2 ≤ π ^ 2 * y / 1 :=
          div_le_div_of_nonneg_left (by positivity) one_pos h3
      _ = _ := by ring)
  exact ⟨K, hK.congr (U := Ioi 0) isOpen_Ioi (fun x hx => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ x from hx))
    (fun x hx => (phiCh_eq hx).symm)⟩

lemma normH_symW (kind : StripKernelChoice) : ∃ K : ℕ → ℝ, SymW (Ici (1 / 8 : ℝ)) (fun x => Real.exp (-(π * x / 2))) K
    (fun x => ‖stripH0 kind ((x : ℂ) * Complex.I)‖) := by
  obtain ⟨K₁, h₁⟩ := phiSh_symW
  obtain ⟨K₂, h₂⟩ := phiCh_symW
  have hpos : ∀ x ∈ Ici (1 / 8 : ℝ), 0 < x := fun x hx => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ x from hx)
  cases kind with
  | star =>
    exact ⟨_, (h₁.add h₂).congr (U := Ioi 0) isOpen_Ioi hpos (fun x hx => (norm_stripH0_star_imag hx).symm)⟩
  | ce =>
    exact ⟨_, h₁.congr (U := Ioi 0) isOpen_Ioi hpos (fun x hx => (norm_stripH0_ce_imag hx).symm)⟩

/-! ### Large `t` -/

lemma stripR0_eq_factors (kind : StripKernelChoice) {x : ℝ} (hx : 0 < x) :
    stripR0 kind x = (uctAlphaOsc / uctAlphaFl) * (‖stripH0 kind ((x : ℂ) * Complex.I)‖ *
      (uctM x ^ (3 / 2 : ℝ) * ((1 * x ^ (1 : ℝ)) * tauA x))) := by
  unfold stripR0
  rw [ite_eq_right_iff.mpr fun h => absurd h hx.ne', abs_of_pos hx]
  have hmp := mPrime_pos hx
  have hmd : uctMderiv x = mPrime x := uctMderiv_eq_mPrime hx
  unfold tauA
  rw [hmd, Real.rpow_one]
  have := uctAlphaFl_pos
  field_simp

lemma wA_le_of_ge {x : ℝ} (hx : 1 / 8 ≤ x) : wA x ≤ 64 := by
  unfold wA
  refine max_le (by norm_num) ?_
  have h1 : (1 / 8 : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) hx 2
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  norm_num at h1 ⊢; linarith

/-- `r₀ ∈ SymW [1/8, ∞) (C₀ (1+x)^{-8})`. -/
lemma r0_large_symW (kind : StripKernelChoice) :
    ∃ (C₀ : ℝ) (K : ℕ → ℝ), 0 ≤ C₀ ∧ SymW (Ici (1 / 8 : ℝ)) (fun x => C₀ * ((1 + x) ^ 8)⁻¹) K (stripR0 kind) := by
  obtain ⟨K₁, h₁⟩ := normH_symW kind
  obtain ⟨K₂, h₂⟩ := mPow32_symW
  obtain ⟨K₃, h₃⟩ := tauA_symW
  have hpos : ∀ x ∈ Ici (1 / 8 : ℝ), 0 < x := fun x hx => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ x from hx)
  have hid := SymW.rpow_gen (S := Ici (1 / 8 : ℝ)) hpos 1 (1 : ℝ)
  have h3' := h₃.mono_set (S' := Ici (1 / 8 : ℝ)) (fun x hx => hpos x hx)
  have hprod := (h₁.mul (h₂.mul (hid.mul h3'))).smul (uctAlphaOsc / uctAlphaFl)
  obtain ⟨C, hC, hexp⟩ := pow_le_exp 11
  set a : ℝ := |uctAlphaOsc / uctAlphaFl| with ha
  refine ⟨256 * a * C, _, by positivity, (hprod.of_le (w' := fun x => 256 * a * C * ((1 + x) ^ 8)⁻¹)
    (K' := _) (fun x hx => ?_) (fun _ => le_rfl)).congr (U := Ioi 0) isOpen_Ioi (fun x hx => hpos x hx)
    (fun x hx => (stripR0_eq_factors kind hx).symm)⟩
  have hx' : 1 / 8 ≤ x := hx
  have hx0 : 0 < x := hpos x hx
  have hm0 := uctM_pos hx0
  have hm1 : uctM x ≤ 2 * (1 + x) := by
    have := uctM_le_linear hx0
    nlinarith [Real.pi_lt_four]
  have hm32 : uctM x ^ (3 / 2 : ℝ) ≤ 4 * (1 + x) ^ 2 := by
    calc uctM x ^ (3 / 2 : ℝ) ≤ (2 * (1 + x)) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow hm0.le hm1 (by norm_num)
      _ ≤ (2 * (1 + x)) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = 4 * (1 + x) ^ 2 := by rw [Real.rpow_two]; ring
  have hwA := wA_le_of_ge hx'
  have hwA0 : 0 ≤ wA x := (zero_le_one).trans (le_max_left _ _)
  have hex := hexp x hx0.le
  have hexp_pos := Real.exp_pos (π * x / 2)
  have hxx : |(1 : ℝ)| * x ^ (1 : ℝ) = x := by rw [Real.rpow_one]; simp
  simp only [hxx]
  have h1x : 0 < 1 + x := by linarith
  have e1 : Real.exp (-(π * x / 2)) * Real.exp (π * x / 2) = 1 := by rw [← Real.exp_add]; simp
  have hD : 0 < ((1 + x) ^ 8) := by positivity
  -- target: `a * (e * (m^{3/2} * (x * wA))) ≤ 256 a C (1+x)^{-8}`
  have hmain : Real.exp (-(π * x / 2)) * (uctM x ^ (3 / 2 : ℝ) * (x * wA x)) ≤
      256 * C * ((1 + x) ^ 8)⁻¹ := by
    have h4 : uctM x ^ (3 / 2 : ℝ) * (x * wA x) ≤ 4 * (1 + x) ^ 2 * ((1 + x) * 64) := by
      have : x * wA x ≤ (1 + x) * 64 := by nlinarith
      exact mul_le_mul hm32 this (mul_nonneg hx0.le hwA0) (by positivity)
    have h5 : Real.exp (-(π * x / 2)) * (4 * (1 + x) ^ 2 * ((1 + x) * 64)) ≤ 256 * C * ((1 + x) ^ 8)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hD]
      have e3 : Real.exp (-(π * x / 2)) * (4 * (1 + x) ^ 2 * ((1 + x) * 64)) * (1 + x) ^ 8 =
          256 * (Real.exp (-(π * x / 2)) * (1 + x) ^ 11) := by ring
      rw [e3]
      have e4 : Real.exp (-(π * x / 2)) * (1 + x) ^ 11 ≤ Real.exp (-(π * x / 2)) * (C * Real.exp (π * x / 2)) :=
        mul_le_mul_of_nonneg_left hex (Real.exp_pos _).le
      have e2 : Real.exp (-(π * x / 2)) * (C * Real.exp (π * x / 2)) = C := by rw [mul_left_comm, e1, mul_one]
      nlinarith
    exact (mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le).trans h5
  calc a * (Real.exp (-(π * x / 2)) * (uctM x ^ (3 / 2 : ℝ) * (x * wA x))) ≤ a * (256 * C * ((1 + x) ^ 8)⁻¹) :=
        mul_le_mul_of_nonneg_left hmain (abs_nonneg _)
    _ = _ := by ring

/-! ### Assembly -/

/-- **`r₀` as a `t`-symbol on `(0, ∞)`** (Lemma FCT.7b (b), the factor `r₀`): smooth, `|t^j ∂^j (r₀ - 1)| ≤ P_j min(t², 1)`,
`|t^j ∂^j r₀| ≤ P_j min(1, t^{-8})`, with `P` depending only on the kernel. -/
theorem stripR0_t_symbol (kind : StripKernelChoice) :
    ∃ P : ℕ → ℝ, (∀ j, 0 ≤ P j) ∧ ContDiffOn ℝ ∞ (stripR0 kind) (Ioi 0) ∧
      (∀ j : ℕ, ∀ t : ℝ, 0 < t → |t ^ j * iteratedDeriv j (fun u => stripR0 kind u - 1) t| ≤ P j * min (t ^ 2) 1) ∧
      (∀ j : ℕ, ∀ t : ℝ, 0 < t → |t ^ j * iteratedDeriv j (fun u => stripR0 kind u - 0) t| ≤ P j * min 1 ((t ^ 8)⁻¹)) := by
  obtain ⟨K₁, h₁⟩ := r0_small_symW kind
  obtain ⟨C₀, K₂, hC₀, h₂⟩ := r0_large_symW kind
  have hIoi : Ioi (0 : ℝ) ⊆ Ioc (0 : ℝ) (1 / 8) ∪ Ici (1 / 8) := fun x hx => by
    rcases le_total x (1 / 8) with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr h
  have hpos1 : ∀ x ∈ Ioc (0 : ℝ) (1 / 8), 0 < x := fun x hx => hx.1
  have hpos2 : ∀ x ∈ Ici (1 / 8 : ℝ), 0 < x := fun x hx => lt_of_lt_of_le (by norm_num) (show (1 / 8 : ℝ) ≤ x from hx)
  have hsmall : ∀ x ∈ Ioc (0 : ℝ) (1 / 8), x ^ 2 ≤ 1 / 64 := fun x hx => by nlinarith [hx.1, hx.2]
  have hinv1 : ∀ x ∈ Ici (1 / 8 : ℝ), ((1 + x) ^ 8)⁻¹ ≤ 1 := fun x hx =>
    inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [hpos2 x hx]))
  -- `r₀ - 1`
  have hA1 := h₁.of_le (w' := fun x => 64 * (C₀ + 1) * min (x ^ 2) 1) (K' := K₁) (fun x hx => by
    have : x ^ 2 ≤ 1 := by linarith [hsmall x hx]
    rw [min_eq_left this]; nlinarith [sq_nonneg x]) (fun _ => le_rfl)
  have hc2 : SymW (Ici (1 / 8 : ℝ)) (fun _ => |(-1 : ℝ)|) SymW.Kone (fun _ => (-1 : ℝ)) := SymW.const hpos2 (-1)
  have hA2 := (h₂.of_le (w' := fun _ => C₀ + 1) (K' := K₂) (fun x hx => by
      have := hinv1 x hx; nlinarith) (fun _ => le_rfl)).add
    (hc2.of_le (w' := fun _ => C₀ + 1) (K' := SymW.Kone) (fun x hx => by simp; linarith) (fun _ => le_rfl))
  have hA2' := (hA2.of_le (w' := fun x => 64 * (C₀ + 1) * min (x ^ 2) 1) (K' := fun r => K₂ r + SymW.Kone r) (fun x hx => by
      have hx' : (1 / 8 : ℝ) ≤ x := hx
      have : (1 / 64 : ℝ) ≤ min (x ^ 2) 1 := le_min (by nlinarith) (by norm_num)
      nlinarith) (fun _ => le_rfl)).congr (U := Ioi 0) isOpen_Ioi (fun x hx => hpos2 x hx)
      (g := fun x => stripR0 kind x - 1) (fun x _ => by simp [sub_eq_add_neg])
  have hA := ((hA1.union hA2').mono_set hIoi)
  -- `r₀`
  have hb1 := (h₁.of_le (w' := fun _ => 2) (K' := K₁) (fun x hx => by linarith [hsmall x hx]) (fun _ => le_rfl)).add
    ((SymW.const hpos1 (1 : ℝ)).of_le (w' := fun _ => 2) (K' := SymW.Kone) (fun x hx => by simp) (fun _ => le_rfl))
  have hb1' := (hb1.of_le (w' := fun x => (2 + C₀) * min 1 ((x ^ 8)⁻¹)) (K' := fun r => K₁ r + SymW.Kone r) (fun x hx => by
      have hx0 := hx.1
      have h8 : (1 : ℝ) ≤ (x ^ 8)⁻¹ := one_le_inv₀ (pow_pos hx0 8) |>.mpr (pow_le_one₀ hx0.le (by linarith [hx.2]))
      rw [min_eq_left h8]; nlinarith) (fun _ => le_rfl)).congr (U := Ioi 0) isOpen_Ioi (fun x hx => hx.1)
      (g := stripR0 kind) (fun x _ => by simp)
  have hb2 := h₂.of_le (w' := fun x => (2 + C₀) * min 1 ((x ^ 8)⁻¹)) (K' := K₂) (fun x hx => by
      have hx0 := hpos2 x hx
      have h1 := hinv1 x hx
      have h2 : ((1 + x) ^ 8)⁻¹ ≤ (x ^ 8)⁻¹ :=
        inv_anti₀ (pow_pos hx0 8) (pow_le_pow_left₀ hx0.le (by linarith) 8)
      have h3 : ((1 + x) ^ 8)⁻¹ ≤ min 1 ((x ^ 8)⁻¹) := le_min h1 h2
      have h4 : 0 ≤ min 1 ((x ^ 8)⁻¹) := le_min zero_le_one (inv_nonneg.mpr (pow_nonneg hx0.le 8))
      nlinarith) (fun _ => le_rfl)
  have hB := ((hb1'.union hb2).mono_set hIoi)
  refine ⟨fun j => max (max (K₁ j) (K₂ j + SymW.Kone j) * (64 * (C₀ + 1))) (max (K₁ j + SymW.Kone j) (K₂ j) * (2 + C₀)),
    fun j => ?_, ?_, fun j t ht => ?_, fun j t ht => ?_⟩
  · exact le_max_of_le_left (mul_nonneg (le_max_of_le_left (hA1.K_nonneg j)) (by positivity))
  · obtain ⟨U, hU, hSU, hfU⟩ := hB.smooth
    exact hfU.mono hSU
  · have h := hA.raw_bound j (show t ∈ Ioi (0 : ℝ) from ht)
    have hm : 0 ≤ min (t ^ 2) 1 := le_min (sq_nonneg t) zero_le_one
    refine h.trans ?_
    calc _ = (max (K₁ j) (K₂ j + SymW.Kone j) * (64 * (C₀ + 1))) * min (t ^ 2) 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hm
  · have h := hB.raw_bound j (show t ∈ Ioi (0 : ℝ) from ht)
    have hm : 0 ≤ min 1 ((t ^ 8)⁻¹) := le_min zero_le_one (inv_nonneg.mpr (pow_nonneg ht.le 8))
    have e : (fun u => stripR0 kind u - 0) = stripR0 kind := by funext u; simp
    rw [e]
    refine h.trans ?_
    calc _ = (max (K₁ j + SymW.Kone j) (K₂ j) * (2 + C₀)) * min 1 ((t ^ 8)⁻¹) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hm

/-- info: 'FormalResearch.SignUncertainty.FctSym.stripR0_t_symbol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stripR0_t_symbol

end FormalResearch.SignUncertainty.FctSym
