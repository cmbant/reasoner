/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSymChain
public import FormalResearch.SignUncertainty.FctCompDTargets
public import FormalResearch.SignUncertainty.UctStripSplit

/-!
# `τ₀` is a symbol of weight `L^{1/2}` on `(0, L₀]` (`fct:bump-sym-check`, the change of variable `L ↦ τ₀(L̃)`)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b: `τ₀(L̃) ≍ L^{1/2}` for `L ≤ 1`
and `m(t) = t² mQ(t)` (`FctCompD.mQ`, even, smooth, positive on `|t| < 1/4`).

With `φ(t) = t √(mQ t)` (smooth near `0`, `φ'(0) = √(π²/12) > 0`) one has `m(t) = φ(t)²` for `t > 0`, so
`τ₀(L) = ψ(√L)` for small `L > 0`, where `ψ` is the local `C^∞` inverse of `φ`.  Hence `τ₀ = ψ ∘ √` is the composition
of a smooth function with `x^{1/2}` (`SymW.comp_smooth`), a profile of weight `x^{1/2}`:

* `tau0_symW`: `∃ L₀ ∈ (0, 1], K, SymW (Ioc 0 L₀) (x ↦ x^{1/2}) K τ₀`.
* `tau0_pow4_symW`: `τ₀⁴ ∈ SymW` of weight `x²` on the same set.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Filter Topology Finset
open scoped ContDiff Real

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCompD FormalResearch.CohnElkies

/-- `φ(t) = t √(mQ t)`, with `m(t) = φ(t)²` for `t > 0`. -/
noncomputable def tauPhi (t : ℝ) : ℝ := t * Real.sqrt (mQ t)

lemma contDiffOn_tauPhi : ContDiffOn ℝ ∞ tauPhi (Ioo (-1 / 4) (1 / 4)) := by
  unfold tauPhi
  refine contDiffOn_id.mul (contDiffOn_mQ.sqrt fun t ht => ?_)
  exact (mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).ne'

lemma tauPhi_zero : tauPhi 0 = 0 := by simp [tauPhi]

lemma tauPhi_sq {t : ℝ} (ht : 0 < t) (ht1 : t < 1 / 4) : tauPhi t ^ 2 = uctM t := by
  unfold tauPhi
  rw [mul_pow, Real.sq_sqrt (mQ_pos_of_mem (abs_lt.mpr ⟨by linarith, ht1⟩)).le, uctM_eq_sq_mul_mQ ht]

/-- The local `C^∞` inverse `ψ` of `φ = tauPhi` at `0`, on `(-η, η)`. -/
lemma exists_tauPsi : ∃ (ψ : ℝ → ℝ) (η : ℝ), 0 < η ∧ ContDiffOn ℝ ∞ ψ (Ioo (-η) η) ∧ ψ 0 = 0 ∧
    ∀ y ∈ Ioo (-η) η, ψ y ∈ Ioo (-1 / 4 : ℝ) (1 / 4) ∧ tauPhi (ψ y) = y := by
  have hI : Ioo (-1 / 4 : ℝ) (1 / 4) ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hφ0 : ContDiffAt ℝ ∞ tauPhi 0 := contDiffOn_tauPhi.contDiffAt hI
  have hpos0 : 0 < mQ 0 := mQ_pos_of_mem (by simp)
  have hcdg : ContDiffAt ℝ ∞ (fun t => Real.sqrt (mQ t)) 0 := (contDiffOn_mQ.contDiffAt hI).sqrt hpos0.ne'
  have hd0 : HasDerivAt tauPhi (Real.sqrt (mQ 0)) 0 := by
    have hg := (hcdg.differentiableAt (by simp)).hasDerivAt
    have h := (hasDerivAt_id' (0 : ℝ)).mul hg
    exact h.congr_deriv (by simp)
  have hne : Real.sqrt (mQ 0) ≠ 0 := (Real.sqrt_pos.mpr hpos0).ne'
  have hf' := hd0.hasFDerivAt_equiv hne
  set Ψ := hφ0.toOpenPartialHomeomorph tauPhi hf' (by simp) with hΨ
  have hsrc : (0 : ℝ) ∈ Ψ.source := hφ0.mem_toOpenPartialHomeomorph_source hf' (by simp)
  have hcoe : (Ψ : ℝ → ℝ) = tauPhi := rfl
  have h0t : (0 : ℝ) ∈ Ψ.target := by
    have := hφ0.image_mem_toOpenPartialHomeomorph_target hf' (by simp)
    rwa [tauPhi_zero] at this
  have hsymm0 : Ψ.symm 0 = 0 := by
    have := Ψ.left_inv hsrc
    rwa [hcoe, tauPhi_zero] at this
  -- a neighbourhood of `0` on which `φ' ≠ 0`, inside the source and `(-1/4, 1/4)`
  have hcont : ContinuousAt (deriv tauPhi) 0 :=
    (contDiffOn_tauPhi.deriv_of_isOpen isOpen_Ioo (m := 0) (by simp)).continuousOn.continuousAt hI
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Ψ.source ∧ t ∈ Ioo (-1 / 4 : ℝ) (1 / 4) ∧ deriv tauPhi t ≠ 0 := by
    have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Ψ.source := Ψ.open_source.mem_nhds hsrc
    have h3 : ∀ᶠ t in 𝓝 (0 : ℝ), deriv tauPhi t ≠ 0 := by
      have : deriv tauPhi 0 = Real.sqrt (mQ 0) := hd0.deriv
      exact hcont.eventually_ne (by rw [this]; exact hne)
    have hI' : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Ioo (-1 / 4 : ℝ) (1 / 4) := hI
    exact (h1.and (hI'.and h3)).mono fun t ht => ⟨ht.1, ht.2.1, ht.2.2⟩
  obtain ⟨a, ha, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hball' : ∀ t ∈ Ioo (-a) a, t ∈ Ψ.source ∧ t ∈ Ioo (-1 / 4 : ℝ) (1 / 4) ∧ deriv tauPhi t ≠ 0 := fun t ht =>
    hball (by rw [Real.dist_eq, sub_zero, abs_lt]; exact ht)
  set W := Ψ.target ∩ Ψ.symm ⁻¹' (Ioo (-a) a) with hW
  have hWo : IsOpen W := Ψ.continuousOn_symm.isOpen_inter_preimage Ψ.open_target isOpen_Ioo
  have h0W : (0 : ℝ) ∈ W := ⟨h0t, by
    show Ψ.symm 0 ∈ Ioo (-a) a
    rw [hsymm0]; exact ⟨by linarith, ha⟩⟩
  have hcdW : ContDiffOn ℝ ∞ Ψ.symm W := by
    intro y hy
    obtain ⟨hyt, hya⟩ := hy
    obtain ⟨_, hmem, hnz⟩ := hball' _ hya
    have hdiff : HasDerivAt tauPhi (deriv tauPhi (Ψ.symm y)) (Ψ.symm y) :=
      ((contDiffOn_tauPhi.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hmem)).hasDerivAt
    exact (Ψ.contDiffAt_symm_deriv (n := ∞) hnz hyt hdiff
      (contDiffOn_tauPhi.contDiffAt (isOpen_Ioo.mem_nhds hmem))).contDiffWithinAt
  obtain ⟨η, hη, hηW⟩ := Metric.isOpen_iff.mp hWo 0 h0W
  have hηW' : ∀ y ∈ Ioo (-η) η, y ∈ W := fun y hy => hηW (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; exact hy)
  refine ⟨Ψ.symm, η, hη, hcdW.mono hηW', hsymm0, fun y hy => ?_⟩
  obtain ⟨hyt, hya⟩ := hηW' y hy
  obtain ⟨_, hmem, _⟩ := hball' _ hya
  exact ⟨hmem, by simpa [hcoe] using Ψ.right_inv hyt⟩

lemma tau0_eq_psi {ψ : ℝ → ℝ} {η : ℝ} (hη : 0 < η) (hψ : ∀ y ∈ Ioo (-η) η, ψ y ∈ Ioo (-1 / 4 : ℝ) (1 / 4) ∧ tauPhi (ψ y) = y)
    {L : ℝ} (hL : L ∈ Ioo 0 (η ^ 2)) : tau0 L = ψ (L ^ (1 / 2 : ℝ)) := by
  obtain ⟨hL0, hL1⟩ := hL
  have hy0 : 0 < L ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hηpos := hη
  have hyη : L ^ (1 / 2 : ℝ) < η := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.sqrt_lt' hηpos).mpr hL1
  obtain ⟨hmem, hφ⟩ := hψ _ ⟨by linarith, hyη⟩
  set t := ψ (L ^ (1 / 2 : ℝ)) with ht
  have hmQ : 0 < mQ t := mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [hmem.1], hmem.2⟩)
  have htpos : 0 < t := by
    by_contra h
    have : t * Real.sqrt (mQ t) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) (Real.sqrt_nonneg _)
    unfold tauPhi at hφ
    linarith
  have hM : uctM t = L := by
    rw [← tauPhi_sq htpos hmem.2, hφ, ← Real.sqrt_eq_rpow, Real.sq_sqrt hL0.le]
  have hτ := tau0_pos hL0
  have hM' : uctM (tau0 L) = L := ceEll_tau0 hL0
  exact uctM_strictMonoOn.injOn hτ htpos (hM'.trans hM.symm)

/-- **`τ₀` is a symbol of weight `L^{1/2}`** on `(0, L₀]` (Lemma FCT.7b, `τ₀(L̃) ≍ L^{1/2}` for `L ≤ 1`, with all derivatives
`|τ₀^{(r)}(L)| ≤ K_r L^{1/2 - r}`). -/
theorem tau0_symW : ∃ (L₀ : ℝ) (K : ℕ → ℝ), 0 < L₀ ∧ L₀ ≤ 1 ∧
    SymW (Ioc 0 L₀) (fun x => x ^ (1 / 2 : ℝ)) K tau0 := by
  obtain ⟨ψ, η, hη, hψ, hψ0, hψη⟩ := exists_tauPsi
  set L₀ : ℝ := min 1 ((η / 2) ^ 2) with hL₀
  have hL₀pos : 0 < L₀ := lt_min one_pos (by positivity)
  have hL₀η : L₀ ≤ (η / 2) ^ 2 := min_le_right _ _
  have hV : IsOpen (Ioo (-η) η) := isOpen_Ioo
  -- bounds on the derivatives of `ψ` on `[0, η/2]`
  have hbd : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Icc (0 : ℝ) (η / 2), |iteratedDeriv j ψ y| ≤ C := by
    intro j
    have hc : ContinuousOn (iteratedDeriv j ψ) (Icc 0 (η / 2)) :=
      (contDiffOn_iteratedDeriv_of_isOpen hV hψ j).continuousOn.mono fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := η / 2)).exists_bound_of_continuousOn hc
    refine ⟨max C 0, le_max_right _ _, fun y hy => ?_⟩
    have h1 : |iteratedDeriv j ψ y| ≤ C := by simpa using hC y hy
    exact h1.trans (le_max_left _ _)
  choose P hP0 hP using hbd
  -- `|ψ y| ≤ P 1 * y`
  have hlin : ∀ y ∈ Icc (0 : ℝ) (η / 2), |ψ y| ≤ P 1 * y := by
    intro y hy
    have hdiff : ∀ z ∈ Icc (0 : ℝ) (η / 2), DifferentiableAt ℝ ψ z := fun z hz =>
      (hψ.differentiableOn (by simp)).differentiableAt
        (hV.mem_nhds ⟨by linarith [hz.1], by linarith [hz.2]⟩)
    have hder : ∀ z ∈ Icc (0 : ℝ) (η / 2), ‖deriv ψ z‖ ≤ P 1 := fun z hz => by
      simpa [iteratedDeriv_one] using hP 1 z hz
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := ψ) (s := Icc (0 : ℝ) (η / 2)) (C := P 1) hdiff
      hder (convex_Icc _ _) (x := 0) ⟨le_rfl, by linarith⟩ hy
    simpa [hψ0, abs_of_nonneg hy.1] using this
  have hfS := SymW.rpow_gen (S := Ioc 0 L₀) (fun x hx => hx.1) 1 (1 / 2 : ℝ)
  have hsq : ∀ x ∈ Ioc 0 L₀, x ^ (1 / 2 : ℝ) ∈ Icc (0 : ℝ) (η / 2) := by
    intro x hx
    refine ⟨(Real.rpow_pos_of_pos hx.1 _).le, ?_⟩
    have : x ^ (1 / 2 : ℝ) ≤ ((η / 2) ^ 2) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hx.1.le (hx.2.trans hL₀η) (by norm_num)
    simp only [← Real.sqrt_eq_rpow] at this
    rw [Real.sqrt_sq (by linarith)] at this
    rw [← Real.sqrt_eq_rpow]; exact this
  have hfV : ∀ x ∈ Ioc 0 L₀, (fun x : ℝ => 1 * x ^ (1 / 2 : ℝ)) x ∈ Ioo (-η) η := fun x hx => by
    have := hsq x hx
    simp only [one_mul]
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hPf : ∀ (j : ℕ) (x : ℝ), x ∈ Ioc 0 L₀ →
      |iteratedDeriv j ψ ((fun x : ℝ => 1 * x ^ (1 / 2 : ℝ)) x)| ≤ P j := fun j x hx => by
    simpa using hP j _ (hsq x hx)
  have hwB : ∀ x ∈ Ioc 0 L₀, (fun x : ℝ => |(1 : ℝ)| * x ^ (1 / 2 : ℝ)) x ≤ 1 := fun x hx => by
    simp only [abs_one, one_mul]
    exact Real.rpow_le_one hx.1.le (hx.2.trans (min_le_left _ _)) (by norm_num)
  have h0 : ∀ x ∈ Ioc 0 L₀, |ψ ((fun x : ℝ => 1 * x ^ (1 / 2 : ℝ)) x)| ≤
      P 1 * (fun x : ℝ => |(1 : ℝ)| * x ^ (1 / 2 : ℝ)) x := fun x hx => by
    simpa using hlin _ (hsq x hx)
  have hcomp := SymW.comp_smooth (f := fun x : ℝ => 1 * x ^ (1 / 2 : ℝ)) (Φ := ψ) (V := Ioo (-η) η) (P := P) (B := 1)
    (L := P 1) hfS hV hψ hfV hPf hP0 hwB (hP0 1) h0
  refine ⟨L₀, compK (P 1) P (fun k => ∏ i ∈ range (k + 1), |(1 / 2 : ℝ) - (i : ℝ)|) 1, hL₀pos, min_le_left _ _, ?_⟩
  refine (hcomp.congr (U := Ioo 0 (η ^ 2)) isOpen_Ioo
    (fun x hx => ⟨hx.1, lt_of_le_of_lt (hx.2.trans hL₀η) (by nlinarith)⟩) ?_).of_le
    (fun x _ => by simp) (fun _ => le_rfl)
  intro x hx
  simp only [one_mul]
  exact (tau0_eq_psi hη hψη hx).symm

/-- **`τ₀⁴ I_fl` is a symbol of weight `|α_fl| L^{1/2}` on `(0, L₀]`** (Lemma FCT.7b (c), the transition bump `B_tr`:
`m(t) = t² mQ(t)`, `τ₀⁴ ≍ L²`, `I_fl = α_fl L^{-3/2}`): `|∂_L^r (τ₀⁴ I_fl)| ≤ K_r |α_fl| L^{1/2 - r}`. -/
theorem tauT_symW : ∃ (L₀ : ℝ) (K : ℕ → ℝ), 0 < L₀ ∧ L₀ ≤ 1 ∧
    SymW (Ioc 0 L₀) (fun x => |uctAlphaFl| * x ^ (1 / 2 : ℝ)) K (fun L => tau0 L ^ 4 * uctIfl L) := by
  obtain ⟨L₀, K, hL₀, hL₀1, h⟩ := tau0_symW
  have h2 := h.mul h
  have h4 := h2.mul h2
  have hfl := SymW.rpow_gen (S := Ioc 0 L₀) (fun x hx => hx.1) uctAlphaFl (-(3 / 2 : ℝ))
  have hm := h4.mul hfl
  refine ⟨L₀, _, hL₀, hL₀1, (hm.congr (U := univ) isOpen_univ (subset_univ _) ?_).of_le ?_ (fun _ => le_rfl)⟩
  · intro x _
    simp only [uctIfl]
    ring
  · intro x hx
    have hxp := hx.1
    have e : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) * (x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) * x ^ (-(3 / 2 : ℝ)) =
        x ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hxp, ← Real.rpow_add hxp, ← Real.rpow_add hxp]
      norm_num
    calc x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) * (x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) * (|uctAlphaFl| * x ^ (-(3 / 2 : ℝ)))
        = |uctAlphaFl| * (x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) * (x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) * x ^ (-(3 / 2 : ℝ))) := by ring
      _ = |uctAlphaFl| * x ^ (1 / 2 : ℝ) := by rw [e]
      _ ≤ _ := le_rfl

/-- info: 'FormalResearch.SignUncertainty.FctSym.tau0_symW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tau0_symW

/-- info: 'FormalResearch.SignUncertainty.FctSym.tauT_symW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tauT_symW

end FormalResearch.SignUncertainty.FctSym
