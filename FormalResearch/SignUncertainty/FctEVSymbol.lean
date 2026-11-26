/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSymExpm1
public import FormalResearch.SignUncertainty.FctSymInv
public import FormalResearch.SignUncertainty.FctVacuumPointwise

/-!
# `e^{v} - 1` as a `t`-symbol, uniformly in `c` (Lemma FCT.7b (b), factor `E`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (b) and `fct:comp-D` (1):
`|v^{(r)}| ≤ C_r τ₁^{2-r}`, `supp v ⊆ (-10τ₁, 10τ₁)`, `|α| ≤ τ₁²`.

`vTotal_symW`: `v = vTotal ∈ SymW (0, 10τ₁] τ₁²` (`|v^{(r)}(x)| ≤ K_r τ₁² x^{-r}` for `x ≤ 10τ₁`, since `τ₁^{-r} ≤ 10^r x^{-r}`);
`expV_symW`: `e^v - 1 ∈ SymW (0, ∞) (256 τ₁² (1+x)^{-8})` with `K` independent of `c, α, τ₁` (`τ₁ ≤ τ₀`, `τ₁⁴ c = 1`, `|α| ≤ τ₁²`).

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Finset
open scoped ContDiff Real

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctCompD
  FormalResearch.SignUncertainty.FctMoment

lemma iteratedDeriv_add_cd {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (r : ℕ) (x : ℝ) :
    iteratedDeriv r (fun t => f t + g t) x = iteratedDeriv r f x + iteratedDeriv r g x :=
  iteratedDeriv_fun_add (hf.contDiffAt.of_le (by exact_mod_cast le_top)) (hg.contDiffAt.of_le (by exact_mod_cast le_top))

lemma zpow_sub_nat' {τ : ℝ} (hτ : τ ≠ 0) (n : ℤ) (r : ℕ) : τ ^ (n - (r : ℤ)) = τ ^ n * (τ ^ r)⁻¹ := by
  rw [zpow_sub₀ hτ, zpow_natCast, div_eq_mul_inv]

/-- **`v = vTotal` is a `t`-symbol of weight `τ₁²` on `(0, 10τ₁]`, uniformly.** -/
theorem vTotal_symW (kind : StripKernelChoice) (K4 : ℝ) (hK4 : 1 ≤ K4) :
    ∃ (τc : ℝ) (Kv : ℕ → ℝ), 0 < τc ∧ τc ≤ 1 / 20 ∧ (∀ r, 0 ≤ Kv r) ∧
      ∀ {c α τ₁ : ℝ}, 0 < c → 0 < τ₁ → τ₁ ≤ τc → τ₁ ^ 4 * c = 1 → |α| ≤ τ₁ ^ 2 →
        ContDiff ℝ ∞ (vTotal kind K4 c α τ₁) ∧ tsupport (vTotal kind K4 c α τ₁) ⊆ Ioo (-10 * τ₁) (10 * τ₁) ∧
        SymW (Ioc 0 (10 * τ₁)) (fun _ => τ₁ ^ 2) Kv (vTotal kind K4 c α τ₁) := by
  obtain ⟨τ₀, hτ₀, hτ₀20, Cv0b, Cv0m, Cva, Cv1b, Cv1m, Cth0b, Cth0m, Ctha, Cth1b, Cth1m,
    CL1_0b, CL1_0m, CL1_a, CL1_1b, CL1_1m, C_tail, C_int, hCv_nn, hCth_nn, hCL1_nn, hCti_nn, hpart1⟩ :=
    fct_comp_D_part1 kind
  have hK40 : 0 ≤ K4 := by linarith
  set B : ℕ → ℝ := fun r => Cv0b r + K4 * Cv0m r + Cva r + Cv1b r + K4 * Cv1m r with hB
  have hB0 : ∀ r, 0 ≤ B r := fun r => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hCv_nn r
    rw [hB]; positivity
  refine ⟨τ₀, fun r => B r * 10 ^ r, hτ₀, hτ₀20, fun r => by have := hB0 r; positivity, ?_⟩
  intro c α τ₁ hc hτ₁ hτ₁_le hc_eq hα_le
  have hτ₁_1 : τ₁ ≤ 1 := by linarith
  have hc_inv : c⁻¹ = τ₁ ^ 4 := by
    rw [inv_eq_iff_eq_inv]; field_simp [hc.ne', hτ₁.ne'] at hc_eq ⊢; linarith
  obtain ⟨⟨hb0_cd, hm0_cd, hva_cd, hb1_cd, hm1_cd, hv_cd⟩, _, _, ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, htsv, _⟩,
    _, _, hderivs, _⟩ := hpart1 hK4 hc hτ₁ hτ₁_le hc_eq hα_le
  refine ⟨hv_cd, htsv, ?_⟩
  have hsum : ∀ r x, iteratedDeriv r (vTotal kind K4 c α τ₁) x =
      (iteratedDeriv r (v0Base kind τ₁) x + K4 * iteratedDeriv r (v0Marg τ₁) x) +
        (iteratedDeriv r (v1Base kind c τ₁) x + K4 * iteratedDeriv r (v1Marg c τ₁) x) +
        iteratedDeriv r (vAlpha α τ₁) x := by
    intro r x
    have e : vTotal kind K4 c α τ₁ = fun t => ((v0Base kind τ₁ t + K4 * v0Marg τ₁ t) +
        (v1Base kind c τ₁ t + K4 * v1Marg c τ₁ t)) + vAlpha α τ₁ t := rfl
    rw [e, iteratedDeriv_add_cd ((hb0_cd.add (contDiff_const.mul hm0_cd)).add (hb1_cd.add (contDiff_const.mul hm1_cd))) hva_cd,
      iteratedDeriv_add_cd (hb0_cd.add (contDiff_const.mul hm0_cd)) (hb1_cd.add (contDiff_const.mul hm1_cd)),
      iteratedDeriv_add_cd hb0_cd (contDiff_const.mul hm0_cd), iteratedDeriv_add_cd hb1_cd (contDiff_const.mul hm1_cd),
      iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  refine
  { pos := fun x hx => hx.1
    smooth := ⟨univ, isOpen_univ, subset_univ _, hv_cd.contDiffOn⟩
    K_nonneg := fun r => by have := hB0 r; positivity
    w_nonneg := fun _ _ => sq_nonneg _
    bound := fun r x hx => ?_ }
  have hx0 : 0 < x := hx.1
  have hq : 0 < (τ₁ ^ r)⁻¹ := inv_pos.mpr (pow_pos hτ₁ r)
  have hτ2 : τ₁ ^ 4 ≤ τ₁ ^ 2 := pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
  have hτ3 : τ₁ ^ 3 ≤ τ₁ ^ 2 := pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
  have hτ5 : τ₁ ^ 5 ≤ τ₁ ^ 2 := pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
  obtain ⟨d1, d2, d3, d4, d5⟩ := hderivs r x
  rw [zpow_sub_nat' hτ₁.ne'] at d1 d2 d3 d4 d5
  simp only [zpow_ofNat, zpow_neg, pow_one] at d1 d2 d3 d4 d5
  obtain ⟨h1, h2, h3, h4, h5⟩ := hCv_nn r
  have hqτ : 0 ≤ τ₁ ^ 2 * (τ₁ ^ r)⁻¹ := by positivity
  have e1 : |iteratedDeriv r (v0Base kind τ₁) x| ≤ Cv0b r * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹) := d1
  have e2 : |iteratedDeriv r (v0Marg τ₁) x| ≤ Cv0m r * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹) :=
    d2.trans (by
      have : Cv0m r * (τ₁ ^ 4 * (τ₁ ^ r)⁻¹) ≤ Cv0m r * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹) := by gcongr
      exact this)
  have e3 : |iteratedDeriv r (vAlpha α τ₁) x| ≤ Cva r * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹) := by
    refine d3.trans ?_
    have : |α| * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹) ≤ 1 * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹) := by
      gcongr; exact hα_le.trans (pow_le_one₀ hτ₁.le hτ₁_1)
    nlinarith
  have e4 : |iteratedDeriv r (v1Base kind c τ₁) x| ≤ Cv1b r * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹) := by
    refine d4.trans ?_
    have : c⁻¹ * (τ₁⁻¹ * (τ₁ ^ r)⁻¹) = τ₁ ^ 3 * (τ₁ ^ r)⁻¹ := by
      rw [hc_inv]; field_simp
    rw [mul_assoc, this]
    gcongr
  have e5 : |iteratedDeriv r (v1Marg c τ₁) x| ≤ Cv1m r * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹) := by
    refine d5.trans ?_
    have : c⁻¹ * (τ₁ * (τ₁ ^ r)⁻¹) = τ₁ ^ 5 * (τ₁ ^ r)⁻¹ := by
      rw [hc_inv]; field_simp
    rw [mul_assoc, this]
    gcongr
  have hxr : (τ₁ ^ r)⁻¹ ≤ 10 ^ r * (x ^ r)⁻¹ := by
    have h10 : x ^ r ≤ (10 * τ₁) ^ r := pow_le_pow_left₀ hx0.le hx.2 r
    rw [mul_pow] at h10
    have hxr0 : 0 < x ^ r := pow_pos hx0 r
    have ht0 : 0 < τ₁ ^ r := pow_pos hτ₁ r
    calc (τ₁ ^ r)⁻¹ = (10 ^ r * (x ^ r)⁻¹) * (x ^ r / (10 ^ r * τ₁ ^ r)) := by field_simp
      _ ≤ (10 ^ r * (x ^ r)⁻¹) * 1 := by
          gcongr
          rw [div_le_one (by positivity)]; exact h10
      _ = _ := mul_one _
  rw [hsum]
  have hab : ∀ a b : ℝ, |a + K4 * b| ≤ |a| + K4 * |b| := fun a b =>
    (abs_add_le _ _).trans (by rw [abs_mul, abs_of_nonneg hK40])
  calc |iteratedDeriv r (v0Base kind τ₁) x + K4 * iteratedDeriv r (v0Marg τ₁) x +
        (iteratedDeriv r (v1Base kind c τ₁) x + K4 * iteratedDeriv r (v1Marg c τ₁) x) +
        iteratedDeriv r (vAlpha α τ₁) x|
      ≤ (|iteratedDeriv r (v0Base kind τ₁) x| + K4 * |iteratedDeriv r (v0Marg τ₁) x|) +
        (|iteratedDeriv r (v1Base kind c τ₁) x| + K4 * |iteratedDeriv r (v1Marg c τ₁) x|) +
        |iteratedDeriv r (vAlpha α τ₁) x| :=
        (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (hab _ _) (hab _ _))) le_rfl)
    _ ≤ (Cv0b r * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹) + K4 * (Cv0m r * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹))) +
        (Cv1b r * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹) + K4 * (Cv1m r * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹))) +
        Cva r * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹) := by gcongr
    _ = B r * (τ₁ ^ 2 * (τ₁ ^ r)⁻¹) := by rw [hB]; ring
    _ ≤ B r * (τ₁ ^ 2 * (10 ^ r * (x ^ r)⁻¹)) := by
        have := hB0 r
        gcongr
    _ = B r * 10 ^ r * τ₁ ^ 2 * (x ^ r)⁻¹ := by ring

/-- **`e^v - 1` is a `t`-symbol on `(0, ∞)`, uniformly in `c`** (`fct:comp-D` (1): `|v^{(r)}| ≤ C_r τ₁^{2-r}`,
`supp v ⊆ (-10τ₁, 10τ₁)`; `|e^v - 1| ≲ τ₁²`). -/
theorem expV_symW (kind : StripKernelChoice) (K4 : ℝ) (hK4 : 1 ≤ K4) :
    ∃ (τc : ℝ) (K : ℕ → ℝ), 0 < τc ∧ τc ≤ 1 / 20 ∧ (∀ r, 0 ≤ K r) ∧
      ∀ {c α τ₁ : ℝ}, 0 < c → 0 < τ₁ → τ₁ ≤ τc → τ₁ ^ 4 * c = 1 → |α| ≤ τ₁ ^ 2 →
        SymW (Ioi 0) (fun x => 256 * τ₁ ^ 2 * ((1 + x) ^ 8)⁻¹) K
          (fun x => Real.exp (vTotal kind K4 c α τ₁ x) - 1) := by
  obtain ⟨τc, Kv, hτc, hτc20, hKv0, hmain⟩ := vTotal_symW kind K4 hK4
  set K : ℕ → ℝ := fun r => max (compK (Kv 0 * Real.exp (Kv 0 * 1)) (fun _ => Real.exp (Kv 0 * 1) + 1)
    (fun k => Kv (k + 1)) 1 r) (SymW.Kone r) with hK
  have hKnn : ∀ r, 0 ≤ K r := fun r => le_max_of_le_right (SymW.Kone_nonneg r)
  refine ⟨τc, K, hτc, hτc20, hKnn, fun {c α τ₁} hc hτ₁ hτ₁_le hc_eq hα_le => ?_⟩
  have hτ₁_1 : τ₁ ≤ 1 / 20 := hτ₁_le.trans hτc20
  obtain ⟨hv_cd, htsv, hv⟩ := hmain hc hτ₁ hτ₁_le hc_eq hα_le
  have hE := symW_exp_sub_one (B := 1) hv (fun x hx => by
    have : τ₁ ^ 2 ≤ 1 := pow_le_one₀ hτ₁.le (by linarith)
    exact this)
  have hE' := hE.of_le (w' := fun x => 256 * τ₁ ^ 2 * ((1 + x) ^ 8)⁻¹) (K' := K) (fun x hx => by
    have hx0 : 0 < x := hx.1
    have hx1 : 1 + x ≤ 2 := by linarith [hx.2]
    have h8 : (1 + x) ^ 8 ≤ 2 ^ 8 := pow_le_pow_left₀ (by linarith) hx1 8
    have hD : 0 < (1 + x) ^ 8 := by positivity
    have : (1 / 256 : ℝ) ≤ ((1 + x) ^ 8)⁻¹ := by
      rw [one_div]; exact inv_anti₀ hD (by norm_num at h8 ⊢; linarith)
    have hτ2 : 0 ≤ τ₁ ^ 2 := sq_nonneg _
    nlinarith) (fun r => le_max_left _ _)
  have hU : IsOpen (tsupport (vTotal kind K4 c α τ₁))ᶜ := (isClosed_tsupport _).isOpen_compl
  have hnot : ∀ x ∈ Ici (10 * τ₁), x ∉ tsupport (vTotal kind K4 c α τ₁) := fun x hx hxt => by
    have := (htsv hxt).2
    have : 10 * τ₁ ≤ x := hx
    linarith [(htsv hxt).2]
  have hpos0 : ∀ x ∈ Ici (10 * τ₁), 0 < x := fun x hx => lt_of_lt_of_le (by positivity) hx
  have hZ := ((SymW.const hpos0 (0 : ℝ)).congr (U := (tsupport (vTotal kind K4 c α τ₁))ᶜ) hU
    (fun x hx => hnot x hx) (g := fun x => Real.exp (vTotal kind K4 c α τ₁ x) - 1) (fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx])).of_le (w' := fun x => 256 * τ₁ ^ 2 * ((1 + x) ^ 8)⁻¹) (K' := K)
    (fun x hx => by
      have hx0 : 0 < x := hpos0 x hx
      have : 0 ≤ ((1 + x) ^ 8)⁻¹ := by positivity
      have hτ2 : 0 ≤ τ₁ ^ 2 := sq_nonneg _
      simp only [abs_zero]; positivity) (fun r => le_max_right _ _)
  have hU2 := hE'.union hZ
  refine (hU2.mono_set (fun x hx => ?_)).of_le (fun _ _ => le_rfl) (fun r => by simp)
  rcases le_total x (10 * τ₁) with h | h
  · exact Or.inl ⟨hx, h⟩
  · exact Or.inr h

/-- info: 'FormalResearch.SignUncertainty.FctSym.expV_symW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expV_symW

end FormalResearch.SignUncertainty.FctSym
