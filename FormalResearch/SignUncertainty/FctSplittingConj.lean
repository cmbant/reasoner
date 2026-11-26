/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSplittingWarp

/-!
# Real symmetry of `Ψ_c`, `F`, `F_±`, `Φ^warp_c` and `Φ̂_c` (`fct:splitting` (2))

Paper I (`constant_terms_five.tex`), `fct:splitting` (2) ("`Φ̂_c` ... is real-symmetric") and `(fct:A-Psi-def)` ("`Ψ_c` is ... real-symmetric").

* `mellinK0_conj`: `K₀(ζ̄, ξ) = conj K₀(ζ, ξ)` for `Re ζ ≤ 1`, `|Re ζ| ≤ 1`, `ξ > 0` (Binet remainder, `S̃₀`, `(1-ζ)^{-1/2}`).
* `fctWarpA_conj`, `fctPsi_conj`, `fctFint_conj`: `A_ε`, `Ψ_c`, `F` commute with conjugation on `{0 ≤ Re ζ < 1}` (given `D_{τ₁}` real-symmetric).
* `fctCauchy_conj`: `F_±(ζ̄) = conj F_±(ζ)` (the substitution `y ↦ -y`).
* `fctPhiWarp_conj`, `fctPhiHatAt_conj`: the glued `Φ^warp_c` and `Φ̂_c = Φ^warp_c/N_c + β_c q₁` are real-symmetric on `S̄` (`N_c`, `β_c` are real).
* `fctPhiHat_conj`: the `conj` clause of `SplittingData` for `fctPhiHat h`, from `FctDescentStmt h`.

Class: proved from `FctDescentStmt` (named input).
-/
@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

lemma intervalIntegral_conj01 (f : ℝ → ℂ) :
    (∫ s in (0 : ℝ)..1, starRingEnd ℂ (f s)) = starRingEnd ℂ (∫ s in (0 : ℝ)..1, f s) := by
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  exact integral_conj

lemma binetRem_conj (w : ℂ) :
    FormalResearch.Asymptotics.binetRem (starRingEnd ℂ w) = starRingEnd ℂ (FormalResearch.Asymptotics.binetRem w) := by
  unfold FormalResearch.Asymptotics.binetRem
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg]

/-- `∀ᵐ s, s ≠ 1`. -/
lemma ae_ne_one : ∀ᵐ s : ℝ ∂volume, s ≠ 1 := by
  have := (Set.countable_singleton (1 : ℝ)).ae_notMem volume
  simpa using this

lemma stripS0Tilde_conj' {ζ : ℂ} (hζ : |ζ.re| ≤ 1) :
    stripS0Tilde (starRingEnd ℂ ζ) = starRingEnd ℂ (stripS0Tilde ζ) := by
  unfold stripS0Tilde
  rw [← intervalIntegral_conj01]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_ne_one] with s hs1 hs
  rw [Set.uIoc_of_le zero_le_one] at hs
  have hs1' : s < 1 := lt_of_le_of_ne hs.2 hs1
  have hre : |((s : ℂ) * ζ).re| < 1 := by
    have : ((s : ℂ) * ζ).re = s * ζ.re := by simp
    rw [this, abs_mul, abs_of_pos hs.1]
    nlinarith [abs_nonneg ζ.re, mul_le_mul_of_nonneg_left hζ hs.1.le]
  have : (s : ℂ) * starRingEnd ℂ ζ = starRingEnd ℂ ((s : ℂ) * ζ) := by simp
  rw [this, stripG_conj hre, map_mul]

lemma conj_log_pi_sq_mul {ξ : ℝ} (hξ : 0 < ξ) :
    starRingEnd ℂ (Complex.log ((π : ℂ) ^ 2 * (ξ : ℂ))) = Complex.log ((π : ℂ) ^ 2 * (ξ : ℂ)) := by
  have hx : (0 : ℝ) < π ^ 2 * ξ := by positivity
  have : (π : ℂ) ^ 2 * (ξ : ℂ) = ((π ^ 2 * ξ : ℝ) : ℂ) := by push_cast; ring
  rw [this, ← Complex.ofReal_log hx.le, Complex.conj_ofReal]

lemma mellinPhi_conj {ζ : ℂ} (hζ : |ζ.re| ≤ 1) {ξ : ℝ} (hξ : 0 < ξ) :
    mellinPhi (starRingEnd ℂ ζ) ξ = starRingEnd ℂ (mellinPhi ζ ξ) := by
  unfold mellinPhi
  rw [stripS0Tilde_conj' hζ, map_add, map_mul, conj_log_pi_sq_mul hξ]


lemma binetDiff_conj (c : ℝ) (ζ : ℂ) :
    FormalResearch.Asymptotics.binetDiff c (starRingEnd ℂ ζ) = starRingEnd ℂ (FormalResearch.Asymptotics.binetDiff c ζ) := by
  unfold FormalResearch.Asymptotics.binetDiff
  have h1 : (c : ℂ) * (1 - starRingEnd ℂ ζ) = starRingEnd ℂ ((c : ℂ) * (1 - ζ)) := by simp
  have h3 : FormalResearch.Asymptotics.binetRem (c : ℂ) = starRingEnd ℂ (FormalResearch.Asymptotics.binetRem (c : ℂ)) := by
    have := binetRem_conj (c : ℂ)
    rwa [Complex.conj_ofReal] at this
  rw [h1, binetRem_conj, map_sub]
  rw [← h3]

/-- **`K₀` is real-symmetric** on `{|Re ζ| ≤ 1}` for `ξ > 0`. -/
lemma mellinK0_conj (c : ℝ) {ξ : ℝ} (hξ : 0 < ξ) {ζ : ℂ} (h1 : |ζ.re| ≤ 1) :
    mellinK0 c (starRingEnd ℂ ζ) ξ = starRingEnd ℂ (mellinK0 c ζ ξ) := by
  have hre : 0 ≤ (1 - ζ).re := by
    have := (abs_le.mp h1).2; simp; linarith
  have hc : (1 - starRingEnd ℂ ζ) ^ (-(1 / 2 : ℂ)) = starRingEnd ℂ ((1 - ζ) ^ (-(1 / 2 : ℂ))) := by
    have e : starRingEnd ℂ (-(1 / 2 : ℂ)) = -(1 / 2 : ℂ) := by
      rw [map_neg, map_div₀, map_one, map_ofNat]
    have := Complex.conj_cpow (1 - ζ) (-(1 / 2 : ℂ)) (arg_ne_pi_of_re_nonneg hre)
    rw [e] at this
    rw [show 1 - starRingEnd ℂ ζ = starRingEnd ℂ (1 - ζ) by simp]
    exact this
  unfold mellinK0
  rw [hc, binetDiff_conj, mellinPhi_conj h1 hξ]
  have hE : Complex.exp ((c : ℂ) * starRingEnd ℂ (mellinPhi ζ ξ)) = starRingEnd ℂ (Complex.exp ((c : ℂ) * mellinPhi ζ ξ)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  simp only [map_mul, Complex.exp_conj, hE]

lemma fctXi1_pos (L1 : ℝ) : 0 < fctXi1 L1 := by unfold fctXi1; positivity

/-- **`A_ε` is real-symmetric** on `{0 ≤ Re t < 1}` when `D_{τ₁}` is real-symmetric on `S̄`. -/
lemma fctWarpA_conj {K4 ε c L1 α : ℝ}
    (hD : ∀ ζ ∈ closedStrip, fctDcompAt K4 c α (starRingEnd ℂ ζ) = starRingEnd ℂ (fctDcompAt K4 c α ζ))
    {t : ℂ} (h0 : 0 ≤ t.re) (h1 : t.re < 1) :
    fctWarpA K4 ε c L1 α (starRingEnd ℂ t) = starRingEnd ℂ (fctWarpA K4 ε c L1 α t) := by
  have hre : |t.re| < 1 := by rw [abs_lt]; constructor <;> linarith
  have htS : t ∈ closedStrip := ⟨h0, h1.le⟩
  unfold fctWarpA
  rw [stripG_conj hre, ctHG_conj ε htS, hD t htS]
  unfold FctPhiKill.phiKill
  rw [FctPhiKill.phiPQ_conj]
  simp only [map_mul, map_add, Complex.conj_ofReal]

/-- **`Ψ_c` is real-symmetric** on `{0 ≤ Re ζ < 1}`. -/
lemma fctPsi_conj {K4 ε c L1 α : ℝ}
    (hD : ∀ ζ ∈ closedStrip, fctDcompAt K4 c α (starRingEnd ℂ ζ) = starRingEnd ℂ (fctDcompAt K4 c α ζ))
    {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re < 1) :
    fctPsi K4 ε c L1 α (starRingEnd ℂ ζ) = starRingEnd ℂ (fctPsi K4 ε c L1 α ζ) := by
  have hre : |ζ.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  unfold fctPsi
  rw [mellinK0_conj c (fctXi1_pos L1) hre, map_mul, map_inv₀, map_mul, ← intervalIntegral_conj01]
  congr 2
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  have hsc : (s : ℂ) * starRingEnd ℂ ζ = starRingEnd ℂ ((s : ℂ) * ζ) := by simp
  have hsre : ((s : ℂ) * ζ).re = s * ζ.re := by simp
  have h0' : 0 ≤ ((s : ℂ) * ζ).re := by rw [hsre]; exact mul_nonneg hs.1 h0
  have h1' : ((s : ℂ) * ζ).re < 1 := by rw [hsre]; nlinarith [hs.1, hs.2]
  have hK : |((s : ℂ) * ζ).re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  rw [hsc, mellinK0_conj c (fctXi1_pos L1) hK, fctWarpA_conj hD h0' h1', map_mul]

/-- **`F` is real-symmetric** on `{0 ≤ Re ζ < 1}`. -/
lemma fctFint_conj {K4 ε c L1 α : ℝ}
    (hD : ∀ ζ ∈ closedStrip, fctDcompAt K4 c α (starRingEnd ℂ ζ) = starRingEnd ℂ (fctDcompAt K4 c α ζ))
    {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re < 1) :
    fctFint K4 ε c L1 α (starRingEnd ℂ ζ) = starRingEnd ℂ (fctFint K4 ε c L1 α ζ) := by
  have htS : ζ ∈ closedStrip := ⟨h0, h1.le⟩
  unfold fctFint fctPhiC
  rw [fctPsi_conj hD h0 h1, hD ζ htS, ctHG_conj ε htS]
  simp only [map_sub, map_div₀, map_mul, Complex.conj_ofReal, map_one]

/-- **`K_sp` is real-symmetric**: `K_sp(t̄, ζ̄) = conj K_sp(t, ζ)`. -/
lemma fctKsp_conj (t ζ : ℂ) : fctKsp (starRingEnd ℂ t) (starRingEnd ℂ ζ) = starRingEnd ℂ (fctKsp t ζ) := by
  unfold fctKsp
  simp only [map_mul, map_div₀, map_pow, map_add, map_one]

/-- **`F_±` are real-symmetric**: `fctCauchy σ ζ̄ = conj (fctCauchy σ ζ)` for `0 ≤ σ < 1` (substitution `y ↦ -y`; `F(σ - iy) = conj F(σ + iy)`). -/
lemma fctCauchy_conj {K4 ε c L1 α σ : ℝ}
    (hD : ∀ ζ ∈ closedStrip, fctDcompAt K4 c α (starRingEnd ℂ ζ) = starRingEnd ℂ (fctDcompAt K4 c α ζ))
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (ζ : ℂ) :
    fctCauchy K4 ε c L1 α σ (starRingEnd ℂ ζ) = starRingEnd ℂ (fctCauchy K4 ε c L1 α σ ζ) := by
  unfold fctCauchy
  rw [map_mul, Complex.conj_ofReal]
  congr 1
  rw [← integral_conj, ← integral_neg_eq_self (fun y : ℝ => fctCauchyIntegrand K4 ε c L1 α σ (starRingEnd ℂ ζ) y)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hl : (σ : ℂ) + ((-y : ℝ) : ℂ) * Complex.I = starRingEnd ℂ ((σ : ℂ) + (y : ℂ) * Complex.I) := by
    simp [map_add, map_mul]
  simp only [fctCauchyIntegrand]
  have hF := fctFint_conj (K4 := K4) (ε := ε) (c := c) (L1 := L1) (α := α) hD (ζ := (σ : ℂ) + (y : ℂ) * Complex.I)
    (by simpa using hσ0) (by simpa using hσ1)
  rw [hl, hF, fctKsp_conj]
  simp only [map_div₀, map_mul, map_sub]


/-- **`Φ^warp_c` is real-symmetric** on `{Re ζ ≥ 0}`. -/
lemma fctPhiWarp_conj {K4 ε c L1 α : ℝ}
    (hD : ∀ ζ ∈ closedStrip, fctDcompAt K4 c α (starRingEnd ℂ ζ) = starRingEnd ℂ (fctDcompAt K4 c α ζ))
    {ζ : ℂ} (h0 : 0 ≤ ζ.re) :
    fctPhiWarp K4 ε c L1 α (starRingEnd ℂ ζ) = starRingEnd ℂ (fctPhiWarp K4 ε c L1 α ζ) := by
  unfold fctPhiWarp
  simp only [Complex.conj_re]
  split_ifs with h
  · have hF := fctFint_conj (K4 := K4) (ε := ε) (c := c) (L1 := L1) (α := α) hD h0 (by linarith)
    have hF' : fctPhiC K4 ε c L1 α (starRingEnd ℂ ζ) = starRingEnd ℂ (fctPhiC K4 ε c L1 α ζ) := by
      rw [fctPhiC_eq, fctPhiC_eq, map_add, map_one, hF]
    rw [map_sub, hF', fctCauchy_conj hD (by norm_num) (by norm_num)]
  · rw [map_sub, map_one, fctCauchy_conj hD (by norm_num) (by norm_num)]

/-- A holomorphic function that is real on `[1/2, 1]` has real derivative at `1`. -/
lemma deriv_conj_of_real_on {g : ℂ → ℂ} (hg : DifferentiableAt ℂ g 1) (hr : ∀ x : ℝ, 1 / 2 ≤ x → x ≤ 1 → (g x).im = 0) :
    starRingEnd ℂ (deriv g 1) = deriv g 1 := by
  have hd : HasDerivAt g (deriv g 1) ((1 : ℝ) : ℂ) := by simpa using hg.hasDerivAt
  have he : HasDerivAt (fun z : ℂ => -Complex.I * g z) (-Complex.I * deriv g 1) ((1 : ℝ) : ℂ) := hd.const_mul _
  have h1 := he.real_of_complex
  have h2 : HasDerivAt (fun x : ℝ => (g x).im) (deriv g 1).im 1 := by
    simpa [Complex.mul_re] using h1
  have h3 : HasDerivWithinAt (fun x : ℝ => (g x).im) (deriv g 1).im (Icc (1 / 2 : ℝ) 1) 1 := h2.hasDerivWithinAt
  have h4 : HasDerivWithinAt (fun x : ℝ => (g x).im) 0 (Icc (1 / 2 : ℝ) 1) 1 :=
    (hasDerivWithinAt_const (1 : ℝ) (Icc (1 / 2 : ℝ) 1) (0 : ℝ)).congr (fun x hx => hr x hx.1 hx.2)
      (hr 1 (by norm_num) le_rfl)
  have hu : UniqueDiffWithinAt ℝ (Icc (1 / 2 : ℝ) 1) 1 :=
    uniqueDiffOn_Icc (by norm_num) 1 ⟨by norm_num, le_rfl⟩
  have := hu.eq_deriv _ h3 h4
  exact Complex.conj_eq_iff_im.mpr this

/-- **`Φ̂_c` is real-symmetric** on `{Re ζ ≥ 0}` (`N_c = Φ^warp_c(1)` and `β_c = Φ^warp_c'(1)/N_c` are real). -/
theorem fctPhiHatAt_conj {K4 ε c L1 α B : ℝ} (hc : 0 < c) (hDh : DifferentiableOn ℂ (fctDcompAt K4 c α) strip)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B)
    (hF : ∀ σ y : ℝ, 3 / 8 ≤ σ → σ ≤ 7 / 16 → ‖fctFint K4 ε c L1 α ((σ : ℂ) + y * Complex.I)‖ ≤ B)
    (hD : ∀ ζ ∈ closedStrip, fctDcompAt K4 c α (starRingEnd ℂ ζ) = starRingEnd ℂ (fctDcompAt K4 c α ζ))
    {ζ : ℂ} (h0 : 0 ≤ ζ.re) :
    fctPhiHatAt K4 ε c L1 α (starRingEnd ℂ ζ) = starRingEnd ℂ (fctPhiHatAt K4 ε c L1 α ζ) := by
  have hNc : starRingEnd ℂ (fctNcC K4 ε c L1 α) = fctNcC K4 ε c L1 α := by
    unfold fctNcC
    have := fctPhiWarp_conj (K4 := K4) (ε := ε) (c := c) (L1 := L1) (α := α) hD (ζ := 1) (by simp)
    simpa using this.symm
  have hreal : ∀ x : ℝ, 1 / 2 ≤ x → x ≤ 1 → (fctPhiWarp K4 ε c L1 α x).im = 0 := by
    intro x hx1 hx2
    have := fctPhiWarp_conj (K4 := K4) (ε := ε) (c := c) (L1 := L1) (α := α) hD (ζ := (x : ℂ)) (by simp; linarith)
    rw [Complex.conj_ofReal] at this
    exact Complex.conj_eq_iff_im.mp this.symm
  have hdiff : DifferentiableAt ℂ (fctPhiWarp K4 ε c L1 α) 1 :=
    (fctPhiWarp_differentiableOn hc hDh hDc hDb hF).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp))
  have hβ : starRingEnd ℂ (fctBetaC K4 ε c L1 α) = fctBetaC K4 ε c L1 α := by
    unfold fctBetaC
    rw [map_div₀, hNc, deriv_conj_of_real_on hdiff hreal]
  unfold fctPhiHatAt
  rw [map_add, map_mul, map_div₀, hNc, hβ, fctPhiWarp_conj hD h0]
  congr 2
  unfold fctQ1
  simp only [map_div₀, map_mul, map_pow, map_sub, map_add, map_one, map_ofNat]


/-- **`fct:splitting` (2), real symmetry** (from the descent bound): for `ε = ±1`, `c ≥ c₀`, `Φ̂_c(ζ̄) = conj Φ̂_c(ζ)` on `S̄` (the `conj` clause of `SplittingData`). -/
theorem fctPhiHat_conj {K4 : ℝ} (hK4 : 1 ≤ K4) {h : FctWarpSolveStmt K4} (hD : FctDescentStmt h) :
    ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → ∀ ζ ∈ closedStrip,
      fctPhiHat h ε c (starRingEnd ℂ ζ) = starRingEnd ℂ (fctPhiHat h ε c ζ) := by
  obtain ⟨c₀, B, hB⟩ := fctSplitting_setup hK4 hD
  refine ⟨c₀, fun ε c hε hc ζ hζ => ?_⟩
  obtain ⟨hc0, hDh, hDc, hDb, hF, hDconj⟩ := hB ε c hε hc
  exact fctPhiHatAt_conj hc0 hDh hDc hDb hF hDconj hζ.1

/-- info: 'FormalResearch.SignUncertainty.fctPhiHat_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctPhiHat_conj

end FormalResearch.SignUncertainty
