/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalResearch
-/
module

public import FormalResearch.ModularBootstrap.Upper.Window.LobeAndTail
public import FormalResearch.ModularBootstrap.WeightAxioms.ComplexAsymptotics
public import FormalResearch.ModularBootstrap.Crossing.Setup

/-!
# Window Limit (`ut:W`, Lemma W)

This module formalizes **Lemma W** (`ut:W`) from `upper_transfer.tex` (lines 475–520):

* `ModifiedCombData` and `CompactCombFamily`: explicit encoding of finite modifications `B_D^{(f)}`
  of the reference comb `B_{ref}^{(f)}` indexed over a compact family `𝒦` as in `ut:P(b)` (including
  both general compact families and the designs `D(N, η_*, d)` via `designCombData`).
* `windowNormKTilde` (`K̃_c^{(f)}`) and `windowMeasureNormK` (`FK_c^{(f)}` for any `prob : FixedWeightProblem`).
* `windowFiniteProd` (`M_K(σ)`) and `tildeW` (`W̃^{±(f)}(σ) := lim_{K → ∞} M_K(σ)`), together with
  uniform convergence (`tendsto_windowFiniteProd_uniform`) and continuity (`continuous_tildeW`).
* `lemma_W_comb`: the second convergence `h₀(x) e^{c' L(x)} / K̃_c^{(f)} → W̃^{±(f)}(σ)`
  uniformly on `σ ∈ [-S, Φ_{N₁ + 1}]` and `D ∈ 𝒦` as `c' → ∞`.
* `lemma_W_measure`: the first convergence `h₀(x) V(c' x^2 / 3) (dt / dσ) / FK_c^{(f)} → W̃^{±(f)}(σ)`
  deduced from `lemma_W_comb` and Step (i) via `cardyV_asymptotic_real`.
-/

namespace FormalResearch.ModularBootstrap.Upper.Window

open Complex Real MeasureTheory Filter Topology Set
open scoped BigOperators
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Holes
open FormalResearch.ModularBootstrap.Bessel
open FormalResearch.ModularBootstrap.WeightAxioms
open FormalResearch.ModularBootstrap.Crossing

@[expose] public section

/-! ### Section 1: Modified Comb Data, Compact Families, and `W̃^{±(f)}` -/

/-- Explicit parameterization of a finite modification `B_D^{(f)}` of `B_{ref}^{(f)}` (`ut:P(b)`):
simple zero at `χ'_f = ξ_* + λ σ_f(c')`, modified conjugate pairs for `f < k ≤ N` at
`χ'_k ± i λ ε̂_k(c')` with `χ'_k = ξ_* + λ σ_k(c')`, and reference tail for `k > N` with width
parameter `η₀ ∈ [0, 1/4]`, converging to `(σ_f^*, σ_k^*, ε̂_k^*)` as `c' → ∞`. -/
structure ModifiedCombData (f N : ℕ) where
  sigmaF : ℝ → ℝ
  sigmaK : ℝ → ℕ → ℝ
  epsHat : ℝ → ℕ → ℝ
  eta0 : ℝ
  sigmaFLim : ℝ
  sigmaKLim : ℕ → ℝ
  epsHatLim : ℕ → ℝ

namespace ModifiedCombData

/-- Full limit site sequence `(σ_k^*)_{k ≥ f + 1}` agreeing with `phiWKB k` for `k > N`. -/
noncomputable def allSigmaLim {f N : ℕ} (d : ModifiedCombData f N) (k : ℕ) : ℝ :=
  if k ≤ N then d.sigmaKLim k else phiWKB k

/-- Full limit width sequence `(ε̂_k^*)_{k ≥ f + 1}` agreeing with `η₀ (Φ_{k+1} - Φ_k)` for `k > N`. -/
noncomputable def allEpsLim {f N : ℕ} (d : ModifiedCombData f N) (k : ℕ) : ℝ :=
  if k ≤ N then d.epsHatLim k else d.eta0 * (phiWKB (k + 1) - phiWKB k)

lemma tail_bound_all {f N : ℕ} (d : ModifiedCombData f N) (hη0 : 0 ≤ d.eta0) (hη1 : d.eta0 ≤ 1 / 4) :
    ∀ k : ℕ, N < k →
      |d.allSigmaLim k - phiWKB k| ≤ 1 * (k : ℝ) ^ (-(4 / 3 : ℝ)) ∧
        |d.allEpsLim k| ≤ 1 * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
  intro k hk
  have hnot : ¬ k ≤ N := by omega
  simp only [allSigmaLim, allEpsLim, hnot, ↓reduceIte, sub_self, abs_zero]
  refine ⟨by positivity, ?_⟩
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hdiff : 0 ≤ phiWKB (k + 1) - phiWKB k ∧
      phiWKB (k + 1) - phiWKB k ≤ (4 / 3 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
    have hk_half : (k : ℝ) / 2 ≤ (k : ℝ) - 1 / 4 := by
      have : (1 / 2 : ℝ) ≤ (k : ℝ) / 2 := by linarith
      linarith
    have hcont : ContinuousOn (fun t : ℝ => (t - 1 / 4) ^ (2 / 3 : ℝ)) (Icc (k : ℝ) ((k : ℝ) + 1)) :=
      ContinuousOn.rpow_const (continuous_id.sub continuous_const).continuousOn
        (fun t ht => Or.inl (by linarith [ht.1]))
    have hderiv : ∀ t ∈ Ioo (k : ℝ) ((k : ℝ) + 1),
        HasDerivAt (fun y : ℝ => (y - 1 / 4) ^ (2 / 3 : ℝ))
          ((2 / 3 : ℝ) * (t - 1 / 4) ^ (-(1 / 3 : ℝ))) t := by
      intro t ht
      have ht_pos : 0 < t - 1 / 4 := by linarith [ht.1]
      have hd := ((hasDerivAt_id t).sub_const (1 / 4 : ℝ)).rpow_const (Or.inl ht_pos.ne') (p := (2 / 3 : ℝ))
      refine hd.congr_deriv ?_
      simp only [id]
      rw [show (2 / 3 : ℝ) - 1 = -(1 / 3 : ℝ) by norm_num]
      ring
    have hint : IntervalIntegrable (fun t : ℝ => (2 / 3 : ℝ) * (t - 1 / 4) ^ (-(1 / 3 : ℝ)))
        volume (k : ℝ) ((k : ℝ) + 1) := by
      refine (ContinuousOn.mul continuousOn_const (ContinuousOn.rpow_const
        (continuous_id.sub continuous_const).continuousOn
        (fun t ht => Or.inl (by linarith [ht.1] : t - 1 / 4 ≠ 0)))).intervalIntegrable_of_Icc (by linarith)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)
      hcont hderiv hint
    have hphi_eq : phiWKB (k + 1) - phiWKB k =
        ∫ t in (k : ℝ)..((k : ℝ) + 1), (2 / 3 : ℝ) * (t - 1 / 4) ^ (-(1 / 3 : ℝ)) := by
      rw [hftc]; unfold phiWKB; push_cast; ring
    rw [hphi_eq]
    refine ⟨intervalIntegral.integral_nonneg (by linarith) (fun t ht =>
      mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith [ht.1]) _)), ?_⟩
    · have h_ub : ∀ t ∈ Icc (k : ℝ) ((k : ℝ) + 1),
          (2 / 3 : ℝ) * (t - 1 / 4) ^ (-(1 / 3 : ℝ)) ≤ (4 / 3 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
        intro t ht
        have h1 : (k : ℝ) / 2 ≤ t - 1 / 4 := by linarith [ht.1]
        have h2 : (t - 1 / 4) ^ (-(1 / 3 : ℝ)) ≤ ((k : ℝ) / 2) ^ (-(1 / 3 : ℝ)) := by
          rw [Real.rpow_neg (by linarith [ht.1]), Real.rpow_neg (by positivity)]
          exact inv_anti₀ (by positivity) (Real.rpow_le_rpow (by positivity) h1 (by norm_num))
        have h3 : ((k : ℝ) / 2) ^ (-(1 / 3 : ℝ)) ≤ 2 * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
          rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by norm_num)]
          have hpow2 : (2⁻¹ : ℝ) ^ (-(1 / 3 : ℝ)) = (2 : ℝ) ^ (1 / 3 : ℝ) := by
            rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), neg_neg]
          have hpow2_le : (2 : ℝ) ^ (1 / 3 : ℝ) ≤ 2 := by
            simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 3 : ℝ) ≤ 1)
          rw [hpow2]
          calc (k : ℝ) ^ (-(1 / 3 : ℝ)) * (2 : ℝ) ^ (1 / 3 : ℝ)
              ≤ (k : ℝ) ^ (-(1 / 3 : ℝ)) * 2 := mul_le_mul_of_nonneg_left hpow2_le (Real.rpow_nonneg hk_pos.le _)
            _ = 2 * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by ring
        linarith [h2, h3]
      calc ∫ t in (k : ℝ)..((k : ℝ) + 1), (2 / 3 : ℝ) * (t - 1 / 4) ^ (-(1 / 3 : ℝ))
          ≤ ∫ _t in (k : ℝ)..((k : ℝ) + 1), (4 / 3 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) :=
            intervalIntegral.integral_mono_on (by linarith) hint intervalIntegrable_const
              (fun t ht => h_ub t ht)
        _ = (4 / 3 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by simp
  rw [abs_of_nonneg (mul_nonneg hη0 hdiff.1)]
  nlinarith [Real.rpow_nonneg hk_pos.le (-(1 / 3 : ℝ))]

end ModifiedCombData

/-- A compact family `𝒦` of finite modifications `B_D^{(f)}` (`ut:W` / `ut:P(b)`):
uniform bounds on the modified sites/widths and uniform convergence to their `c' → ∞` limits. -/
structure CompactCombFamily (f N : ℕ) where
  members : Set (ModifiedCombData f N)
  hf : 1 ≤ f
  hN : f ≤ N
  M : ℝ
  hM : 0 < M
  eta0_bounds : ∀ d ∈ members, 0 ≤ d.eta0 ∧ d.eta0 ≤ 1 / 4
  finite_bounds : ∀ d ∈ members, ∀ {c' : ℝ}, 0 < c' →
    |d.sigmaF c'| ≤ M ∧
      ∀ k ∈ Finset.Icc (f + 1) N,
        |d.sigmaK c' k| ≤ M ∧ 0 ≤ d.epsHat c' k ∧ d.epsHat c' k ≤ M
  lim_bounds : ∀ d ∈ members,
    |d.sigmaFLim| ≤ M ∧
      ∀ k ∈ Finset.Icc (f + 1) N,
        |d.sigmaKLim k| ≤ M ∧ 0 ≤ d.epsHatLim k ∧ d.epsHatLim k ≤ M
  uniform_tendsto : ∀ {ε : ℝ}, 0 < ε → ∃ C₀ > 0, ∀ {c' : ℝ}, C₀ ≤ c' →
    ∀ d ∈ members,
      |d.sigmaF c' - d.sigmaFLim| ≤ ε ∧
        ∀ k ∈ Finset.Icc (f + 1) N,
          |d.sigmaK c' k - d.sigmaKLim k| ≤ ε ∧ |d.epsHat c' k - d.epsHatLim k| ≤ ε

/-- Complex Blaschke product `B_D^{(f)}(z)` for `D : ModifiedCombData f N`. -/
noncomputable def modifiedCombB (f N : ℕ) (d : ModifiedCombData f N) (c' : ℝ) (z : ℂ) : ℂ :=
  let χf : ℝ := xiStar + lambdaComb c' * d.sigmaF c'
  blaschkeT (χf : ℂ) z *
    (∏ k ∈ Finset.Icc (f + 1) N,
      let χk : ℝ := xiStar + lambdaComb c' * d.sigmaK c' k
      let εk : ℝ := lambdaComb c' * d.epsHat c' k
      blaschkeT ((χk : ℂ) + (εk : ℂ) * Complex.I) z *
        blaschkeT ((χk : ℂ) - (εk : ℂ) * Complex.I) z) *
    (∏' m : ℕ,
      let χm : ℝ := chiQuantile c' (N + 1 + m : ℕ)
      let εm : ℝ := d.eta0 * siteGap c' (N + 1 + m)
      blaschkeT ((χm : ℂ) + (εm : ℂ) * Complex.I) z *
        blaschkeT ((χm : ℂ) - (εm : ℂ) * Complex.I) z)

/-- Real test function `h₀(x) = sech^2(π x / 2) Re B_D^{(f)}(x)` on `ℝ`. -/
noncomputable def modifiedH0 (f N : ℕ) (d : ModifiedCombData f N) (c' x : ℝ) : ℝ :=
  (1 / Real.cosh (π * x / 2) ^ 2) * (modifiedCombB f N d c' (x : ℂ)).re

/-- Normalization constant `K̃_c^{(f)} := sech^2(π ξ_* / 2) (2 √2 / (π λ))^{2 n_1}` (`n_1 = f - 1/4`). -/
noncomputable def windowNormKTilde (f : ℕ) (c' : ℝ) : ℝ :=
  (1 / Real.cosh (π * xiStar / 2) ^ 2) *
    (2 * Real.sqrt 2 / (π * lambdaComb c')) ^ (2 * ((f : ℝ) - 1 / 4))

/-- Measure normalization constant `FK_c^{(f)}` matching `V(c' x^2 / 3) (dt / dσ) = (FK_c^{(f)} / K̃_c^{(f)}) e^{c' L} (1 + o(1))`. -/
noncomputable def windowMeasureNormK (prob : FixedWeightProblem) (f : ℕ) (c' : ℝ) : ℝ :=
  windowNormKTilde f c' *
    ((2 * xiStar) ^ (prob.w - 1) * prob.nullPoly (Real.exp (-4 * π * xiStar)) *
      (1 / π) * Real.sqrt (xiStar / 3) * Real.sqrt c' * lambdaComb c')

/-- Finite-`K` window approximant
`M_K(σ) = exp(FQ_{A_K}(σ) - 2π σ_-^{3/2}) (σ - σ_f) ∏_{k=f+1}^K ((σ - σ_k)^2 + ε̂_k^2)`. -/
noncomputable def windowFiniteProd (f : ℕ) (σf : ℝ) (σSeq εHat : ℕ → ℝ) (K : ℕ) (σ : ℝ) : ℝ :=
  Real.exp (continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ)) *
    (σ - σf) * ∏ k ∈ Finset.Icc (f + 1) K, ((σ - σSeq k) ^ 2 + (εHat k) ^ 2)

/-- Window limit `W̃^{±(f)}(σ) := lim_{K → ∞} M_K(σ)`. -/
noncomputable def tildeW (f : ℕ) (σf : ℝ) (σSeq εHat : ℕ → ℝ) (σ : ℝ) : ℝ :=
  limUnder atTop (fun K : ℕ => windowFiniteProd f σf σSeq εHat K σ)

lemma real_sign_mul_abs (t : ℝ) : Real.sign t * |t| = t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [Real.sign_of_neg ht, abs_of_neg ht]; ring
  · simp
  · rw [Real.sign_of_pos ht, abs_of_pos ht]; ring

lemma windowFiniteProd_eq_sign (f : ℕ) (σf : ℝ) (σSeq εHat : ℕ → ℝ) (K : ℕ) (σ : ℝ) :
    windowFiniteProd f σf σSeq εHat K σ =
      Real.sign (σ - σf) *
        (Real.exp (continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ)) *
          |σ - σf| * ∏ k ∈ Finset.Icc (f + 1) K, ((σ - σSeq k) ^ 2 + (εHat k) ^ 2)) := by
  unfold windowFiniteProd
  have hs := real_sign_mul_abs (σ - σf)
  calc Real.exp _ * (σ - σf) * _
      = Real.exp _ * (Real.sign (σ - σf) * |σ - σf|) * _ := by rw [hs]
    _ = Real.sign (σ - σf) * (Real.exp _ * |σ - σf| * _) := by ring

lemma tildeW_eq_sign_lim (f : ℕ) (σf : ℝ) (σSeq εHat : ℕ → ℝ) (σ : ℝ)
    (hconv : ∃ L : ℝ, Tendsto (fun K : ℕ => windowFiniteProd f σf σSeq εHat K σ) atTop (𝓝 L)) :
    tildeW f σf σSeq εHat σ =
      Real.sign (σ - σf) *
        limUnder atTop (fun K : ℕ =>
          Real.exp (continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ)) *
            |σ - σf| * ∏ k ∈ Finset.Icc (f + 1) K, ((σ - σSeq k) ^ 2 + (εHat k) ^ 2)) := by
  obtain ⟨L, hL⟩ := hconv
  rcases eq_or_ne σ σf with rfl | hne
  · simp [windowFiniteProd, tildeW, tendsto_const_nhds.limUnder_eq]
  · have hdiff_ne : σ - σf ≠ 0 := sub_ne_zero.mpr hne
    have hsign_inv : Real.sign (σ - σf) ^ 2 = 1 := by
      rcases lt_or_gt_of_ne hdiff_ne with h | h
      · simp [Real.sign_of_neg h]
      · simp [Real.sign_of_pos h]
    have hL' : Tendsto (fun K : ℕ => Real.sign (σ - σf) * windowFiniteProd f σf σSeq εHat K σ)
        atTop (𝓝 (Real.sign (σ - σf) * L)) := hL.const_mul _
    have h_abs_seq : (fun K : ℕ =>
        Real.exp (continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ)) *
          |σ - σf| * ∏ k ∈ Finset.Icc (f + 1) K, ((σ - σSeq k) ^ 2 + (εHat k) ^ 2)) =
        (fun K : ℕ => Real.sign (σ - σf) * windowFiniteProd f σf σSeq εHat K σ) := by
      ext K
      rw [windowFiniteProd_eq_sign]
      calc _ = 1 * (Real.exp _ * |σ - σf| * _) := (one_mul _).symm
        _ = (Real.sign (σ - σf) ^ 2) * (Real.exp _ * |σ - σf| * _) := by rw [hsign_inv]
        _ = Real.sign (σ - σf) * (Real.sign (σ - σf) * (Real.exp _ * |σ - σf| * _)) := by ring
    rw [h_abs_seq, hL'.limUnder_eq, tildeW, hL.limUnder_eq]
    calc L = 1 * L := (one_mul L).symm
      _ = Real.sign (σ - σf) ^ 2 * L := by rw [hsign_inv]
      _ = Real.sign (σ - σf) * (Real.sign (σ - σf) * L) := by ring

/-! ### Section 2: Continuity of `continuumFQ` and Uniform Convergence of `windowFiniteProd` -/

private lemma abs_exp_sub_one_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.exp u - 1| ≤ 2 * |u| := by
  have hu_le : u ≤ 1 / 2 := (abs_le.mp hu).2
  have hu_ge : -(1 / 2) ≤ u := (abs_le.mp hu).1
  have h1 : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have h2 : Real.exp u ≤ (1 - u)⁻¹ := by
    have hpos : 0 < 1 - u := by linarith
    have hneg : 1 - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
    rw [Real.exp_neg] at hneg
    have hinv := inv_anti₀ hpos hneg
    simpa [inv_inv] using hinv
  have h3 : (1 - u)⁻¹ - 1 ≤ 2 * |u| := by
    have hpos : 0 < 1 - u := by linarith
    have hid : (1 - u)⁻¹ - 1 = u / (1 - u) := by field_simp [hpos.ne']; ring
    rw [hid]
    calc u / (1 - u) ≤ |u| / (1 - u) := by gcongr; exact le_abs_self u
      _ ≤ |u| / (1 / 2 : ℝ) := by gcongr; linarith
      _ = 2 * |u| := by ring
  rw [abs_le]
  constructor
  · linarith [neg_abs_le u]
  · linarith

private lemma continuous_continuumAnti_nonneg (t : ℝ) (_ht : 0 ≤ t) :
    Continuous (fun σ : ℝ =>
      -2 * (t ^ 2 + t * Real.sqrt σ + Real.sqrt σ ^ 2) * ((t - Real.sqrt σ) * Real.log (t - Real.sqrt σ)) -
        2 * (t ^ 2 - t * Real.sqrt σ + Real.sqrt σ ^ 2) * ((t + Real.sqrt σ) * Real.log (t + Real.sqrt σ)) +
        (4 / 3 : ℝ) * t ^ 3 + 4 * σ * t) := by
  have hs : Continuous fun σ : ℝ => Real.sqrt σ := Real.continuous_sqrt
  have h1 : Continuous fun σ : ℝ => (t ^ 2 + t * Real.sqrt σ + Real.sqrt σ ^ 2) :=
    (continuous_const.add (continuous_const.mul hs)).add (hs.pow 2)
  have h2 : Continuous fun σ : ℝ => (t - Real.sqrt σ) * Real.log (t - Real.sqrt σ) :=
    Real.continuous_mul_log.comp (continuous_const.sub hs)
  have h3 : Continuous fun σ : ℝ => (t ^ 2 - t * Real.sqrt σ + Real.sqrt σ ^ 2) :=
    (continuous_const.sub (continuous_const.mul hs)).add (hs.pow 2)
  have h4 : Continuous fun σ : ℝ => (t + Real.sqrt σ) * Real.log (t + Real.sqrt σ) :=
    Real.continuous_mul_log.comp (continuous_const.add hs)
  fun_prop

lemma continuous_continuumFQ (A : ℝ) (hA : 0 ≤ A) : Continuous (continuumFQ A) := by
  have heq : continuumFQ A = fun σ => continuumAnti σ (Real.sqrt A) := by
    ext σ; exact continuumFQ_eq_continuumAnti hA
  rw [heq]
  set t := Real.sqrt A
  have ht : 0 ≤ t := Real.sqrt_nonneg A
  let fPos : ℝ → ℝ := fun σ =>
    -2 * (t ^ 2 + t * Real.sqrt σ + Real.sqrt σ ^ 2) * ((t - Real.sqrt σ) * Real.log (t - Real.sqrt σ)) -
      2 * (t ^ 2 - t * Real.sqrt σ + Real.sqrt σ ^ 2) * ((t + Real.sqrt σ) * Real.log (t + Real.sqrt σ)) +
      (4 / 3 : ℝ) * t ^ 3 + 4 * σ * t
  have hfPos_cont : Continuous fPos := continuous_continuumAnti_nonneg t ht
  have hfPos_eq : ∀ σ, 0 ≤ σ → continuumAnti σ t = fPos σ := by
    intro σ hσ
    rcases eq_or_lt_of_le hσ with rfl | hσ_pos
    · dsimp [fPos]; unfold continuumAnti
      simp only [↓reduceIte, Real.sqrt_zero, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, sub_zero]
      ring
    · unfold continuumAnti
      simp only [hσ_pos.ne', not_lt.mpr hσ_pos.le, ↓reduceIte]
      dsimp [fPos]
      have hsub1 : t ^ 3 - Real.sqrt σ ^ 3 = (t ^ 2 + t * Real.sqrt σ + Real.sqrt σ ^ 2) * (t - Real.sqrt σ) := by
        ring
      have hsub2 : t ^ 3 + Real.sqrt σ ^ 3 = (t ^ 2 - t * Real.sqrt σ + Real.sqrt σ ^ 2) * (t + Real.sqrt σ) := by
        ring
      rw [Real.log_abs, hsub1, hsub2]
      ring
  let fNeg : ℝ → ℝ := fun σ =>
    if σ < 0 then
      -2 * t ^ 3 * Real.log (t ^ 2 - σ) + (4 / 3 : ℝ) * t ^ 3 + 4 * σ * t +
        4 * (-σ) ^ (3 / 2 : ℝ) * Real.arctan (t / Real.sqrt (-σ))
    else -4 * t ^ 3 * Real.log t + (4 / 3 : ℝ) * t ^ 3
  have hfNeg_eq : ∀ σ, σ ≤ 0 → continuumAnti σ t = fNeg σ := by
    intro σ hσ
    rcases eq_or_lt_of_le hσ with rfl | hσ_neg
    · simp [fNeg, continuumAnti]
    · unfold continuumAnti; dsimp [fNeg]
      simp [hσ_neg.ne, hσ_neg]
  have hfNeg_contOn : ContinuousOn fNeg (Iic 0) := by
    intro σ hσ
    rcases eq_or_lt_of_le (Set.mem_Iic.mp hσ) with rfl | hσ_neg
    · refine ContinuousAt.continuousWithinAt ?_
      rw [Metric.continuousAt_iff]
      intro ε hε
      have hterm1 : Tendsto (fun x : ℝ => -2 * t ^ 3 * Real.log (t ^ 2 - x)) (𝓝[<] 0)
          (𝓝 (-4 * t ^ 3 * Real.log t)) := by
        rcases eq_or_lt_of_le ht with ht0 | ht_pos
        · simp [← ht0]
        · have hlog_t : ContinuousAt (fun x : ℝ => -2 * t ^ 3 * Real.log (t ^ 2 - x)) 0 := by
            have hpos0 : t ^ 2 - (0 : ℝ) ≠ 0 := by rw [sub_zero]; positivity
            fun_prop (disch := exact hpos0)
          have heq0 : -2 * t ^ 3 * Real.log (t ^ 2 - (0 : ℝ)) = -4 * t ^ 3 * Real.log t := by
            rw [sub_zero, Real.log_pow]; push_cast; ring
          rw [← heq0]
          exact hlog_t.tendsto.mono_left nhdsWithin_le_nhds
      have hterm2_bd : ∀ᶠ x in 𝓝[<] (0 : ℝ), |4 * (-x) ^ (3 / 2 : ℝ) * Real.arctan (t / Real.sqrt (-x))| ≤
          2 * π * (-x) ^ (3 / 2 : ℝ) := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        have hpow_nn : 0 ≤ (-x) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by linarith [hx.out]) _
        have harc_bd : |Real.arctan (t / Real.sqrt (-x))| ≤ π / 2 := by
          rw [abs_le]
          exact ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_nonneg hpow_nn]
        calc 4 * (-x) ^ (3 / 2 : ℝ) * |Real.arctan (t / Real.sqrt (-x))|
            ≤ 4 * (-x) ^ (3 / 2 : ℝ) * (π / 2) :=
              mul_le_mul_of_nonneg_left harc_bd (by positivity)
          _ = 2 * π * (-x) ^ (3 / 2 : ℝ) := by ring
      have hzero : Tendsto (fun x : ℝ => 2 * π * (-x) ^ (3 / 2 : ℝ)) (𝓝[<] 0) (𝓝 0) := by
        have hc : Continuous fun x : ℝ => 2 * π * (-x) ^ (3 / 2 : ℝ) :=
          continuous_const.mul (Continuous.rpow_const continuous_neg fun _ => Or.inr (by norm_num))
        have h0 := hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Iio 0))
        simpa using h0
      have hlin : Tendsto (fun x : ℝ => (4 / 3 : ℝ) * t ^ 3 + 4 * x * t) (𝓝[<] 0)
          (𝓝 ((4 / 3 : ℝ) * t ^ 3)) := by
        have hc : Continuous fun x : ℝ => (4 / 3 : ℝ) * t ^ 3 + 4 * x * t := by fun_prop
        have h0 := hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Iio 0))
        simpa using h0
      have hlt_1 := Metric.tendsto_nhds.mp hterm1 (ε / 3) (by linarith)
      have hlt_2 := Metric.tendsto_nhds.mp hzero (ε / 3) (by linarith)
      have hlt_3 := Metric.tendsto_nhds.mp hlin (ε / 3) (by linarith)
      have hall := hlt_1.and (hlt_2.and (hlt_3.and hterm2_bd))
      rw [eventually_nhdsWithin_iff] at hall
      obtain ⟨δ, hδ_pos, hδ⟩ := Metric.eventually_nhds_iff.mp hall
      refine ⟨δ, hδ_pos, fun x hx => ?_⟩
      by_cases hx0 : x < 0
      · obtain ⟨h1, h2, h3, h4⟩ := hδ hx hx0
        rw [Real.dist_eq] at h1 h2 h3 ⊢
        simp only [fNeg, hx0, ↓reduceIte] at ⊢
        simp only [lt_irrefl (0 : ℝ), ↓reduceIte] at h2 ⊢
        simp only [sub_zero] at h2
        have hb2 : |4 * (-x) ^ (3 / 2 : ℝ) * Real.arctan (t / Real.sqrt (-x))| < ε / 3 := by
          have : 2 * π * (-x) ^ (3 / 2 : ℝ) ≤ |2 * π * (-x) ^ (3 / 2 : ℝ)| := le_abs_self _
          linarith
        have hdif : (-2 * t ^ 3 * Real.log (t ^ 2 - x) + (4 / 3 : ℝ) * t ^ 3 + 4 * x * t +
              4 * (-x) ^ (3 / 2 : ℝ) * Real.arctan (t / Real.sqrt (-x))) -
            (-4 * t ^ 3 * Real.log t + (4 / 3 : ℝ) * t ^ 3) =
            (-2 * t ^ 3 * Real.log (t ^ 2 - x) - (-4 * t ^ 3 * Real.log t)) +
              (((4 / 3 : ℝ) * t ^ 3 + 4 * x * t) - (4 / 3 : ℝ) * t ^ 3) +
              4 * (-x) ^ (3 / 2 : ℝ) * Real.arctan (t / Real.sqrt (-x)) := by ring
        rw [hdif]
        have ha1 := abs_add_le
          ((-2 * t ^ 3 * Real.log (t ^ 2 - x) - (-4 * t ^ 3 * Real.log t)) +
            (((4 / 3 : ℝ) * t ^ 3 + 4 * x * t) - (4 / 3 : ℝ) * t ^ 3))
          (4 * (-x) ^ (3 / 2 : ℝ) * Real.arctan (t / Real.sqrt (-x)))
        have ha2 := abs_add_le
          (-2 * t ^ 3 * Real.log (t ^ 2 - x) - (-4 * t ^ 3 * Real.log t))
          (((4 / 3 : ℝ) * t ^ 3 + 4 * x * t) - (4 / 3 : ℝ) * t ^ 3)
        linarith
      · simp [fNeg, hx0, hε]
    · have hcont : ContinuousAt (fun x : ℝ =>
          -2 * t ^ 3 * Real.log (t ^ 2 - x) + (4 / 3 : ℝ) * t ^ 3 + 4 * x * t +
            4 * (-x) ^ (3 / 2 : ℝ) * Real.arctan (t / Real.sqrt (-x))) σ := by
        have hpos1 : t ^ 2 - σ ≠ 0 := by nlinarith [sq_nonneg t]
        have hpos2 : -σ ≠ 0 := by linarith
        have hab : ContinuousAt (fun x : ℝ => -2 * t ^ 3 * Real.log (t ^ 2 - x) + (4 / 3 : ℝ) * t ^ 3 + 4 * x * t) σ := by
          fun_prop (disch := exact hpos1)
        have hc : ContinuousAt (fun x : ℝ => 4 * (-x) ^ (3 / 2 : ℝ) * Real.arctan (t / Real.sqrt (-x))) σ :=
          ContinuousAt.mul (ContinuousAt.mul continuousAt_const
            (ContinuousAt.rpow_const continuousAt_neg (Or.inl hpos2)))
            (Real.continuous_arctan.continuousAt.comp (continuousAt_const.div
              ((Real.continuous_sqrt.comp continuous_neg).continuousAt (x := σ))
              (Real.sqrt_pos.mpr (neg_pos.mpr hσ_neg)).ne'))
        exact hab.add hc
      have hev : (fun x : ℝ =>
          -2 * t ^ 3 * Real.log (t ^ 2 - x) + (4 / 3 : ℝ) * t ^ 3 + 4 * x * t +
            4 * (-x) ^ (3 / 2 : ℝ) * Real.arctan (t / Real.sqrt (-x))) =ᶠ[𝓝 σ] fNeg := by
        filter_upwards [Iio_mem_nhds hσ_neg] with x hx
        simp only [Set.mem_Iio] at hx
        simp [fNeg, hx]
      exact (hcont.congr hev).continuousWithinAt
  have hfPos_contOn : ContinuousOn (fun σ => continuumAnti σ t) (Ici 0) :=
    hfPos_cont.continuousOn.congr (fun σ hσ => hfPos_eq σ hσ)
  have hfNeg_contOn' : ContinuousOn (fun σ => continuumAnti σ t) (Iic 0) :=
    hfNeg_contOn.congr (fun σ hσ => hfNeg_eq σ hσ)
  have hunion : Ici (0 : ℝ) ∪ Iic (0 : ℝ) = univ := by ext x; simp
  have hcomb := ContinuousOn.union_of_isClosed hfPos_contOn hfNeg_contOn' isClosed_Ici isClosed_Iic
  rwa [hunion, continuousOn_univ] at hcomb

private lemma continuous_windowFiniteProd (f : ℕ) (σf : ℝ) (σSeq εHat : ℕ → ℝ) (K : ℕ) :
    Continuous (windowFiniteProd f σf σSeq εHat K) := by
  unfold windowFiniteProd
  have h1 : Continuous fun σ : ℝ =>
      Real.exp (continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ)) := by
    refine Real.continuous_exp.comp ((continuous_continuumFQ (continuumAK K) (continuumAK_nonneg K)).sub ?_)
    exact continuous_const.mul (Continuous.rpow_const (continuous_neg.max continuous_const)
      fun _ => Or.inr (by norm_num))
  have h2 : Continuous fun σ : ℝ => σ - σf := continuous_id.sub continuous_const
  have h3 : Continuous fun σ : ℝ => ∏ k ∈ Finset.Icc (f + 1) K, ((σ - σSeq k) ^ 2 + (εHat k) ^ 2) :=
    continuous_finsetProd _ fun _ _ => by fun_prop
  exact (h1.mul h2).mul h3

private lemma windowFiniteProd_step_ratio {f N K₀ K : ℕ} {σf : ℝ} {σSeq εHat : ℕ → ℝ} {σ : ℝ}
    (hN : f ≤ N) (hK₀ : N ≤ K₀) (hK : K₀ ≤ K)
    (hpos : ∀ k ∈ Finset.Icc (K₀ + 1) K, 0 < (σ - σSeq k) ^ 2 + (εHat k) ^ 2) :
    windowFiniteProd f σf σSeq εHat K σ =
      windowFiniteProd f σf σSeq εHat K₀ σ *
        Real.exp ((continuumFQ (continuumAK K) σ - continuumFQ (continuumAK K₀) σ) +
          ∑ k ∈ Finset.Icc (K₀ + 1) K, Real.log ((σ - σSeq k) ^ 2 + (εHat k) ^ 2)) := by
  unfold windowFiniteProd
  have hsub : Finset.Icc (f + 1) K = Finset.Icc (f + 1) K₀ ∪ Finset.Icc (K₀ + 1) K := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc (f + 1) K₀) (Finset.Icc (K₀ + 1) K) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1 hk2
    omega
  rw [hsub, Finset.prod_union hdisj]
  have hprod_eq : ∏ k ∈ Finset.Icc (K₀ + 1) K, ((σ - σSeq k) ^ 2 + (εHat k) ^ 2) =
      Real.exp (∑ k ∈ Finset.Icc (K₀ + 1) K, Real.log ((σ - σSeq k) ^ 2 + (εHat k) ^ 2)) := by
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun k hk => (Real.exp_log (hpos k hk)).symm
  rw [hprod_eq]
  have hexp : continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) =
      (continuumFQ (continuumAK K₀) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ)) +
        (continuumFQ (continuumAK K) σ - continuumFQ (continuumAK K₀) σ) := by ring
  rw [hexp, Real.exp_add, Real.exp_add]
  ring

/-- Uniform Cauchy rate and convergence of `windowFiniteProd` on `[-S, S]` (`ut:W`), uniform
over all sequences sharing the finite parameter bound `M` and tail bound `(N, C_t)`. -/
theorem tendsto_windowFiniteProd_uniform (f N : ℕ) (_hf : 1 ≤ f) (hN : f ≤ N)
    {M C_t S : ℝ} (hM : 0 < M) (hC_t : 0 < C_t) (hS : 0 ≤ S) :
    ∃ (K_min : ℕ) (C : ℝ), N ≤ K_min ∧ 1 ≤ K_min ∧ 0 < C ∧
      ∀ {σf : ℝ} {σSeq εHat : ℕ → ℝ},
        |σf| ≤ M →
        (∀ k ∈ Finset.Icc (f + 1) N, |σSeq k| ≤ M ∧ |εHat k| ≤ M) →
        (∀ k : ℕ, N < k →
          |σSeq k - phiWKB k| ≤ C_t * (k : ℝ) ^ (-(4 / 3 : ℝ)) ∧ |εHat k| ≤ C_t * (k : ℝ) ^ (-(1 / 3 : ℝ))) →
        (∀ {K₁ K₂ : ℕ} {σ : ℝ}, K_min ≤ K₁ → K₁ ≤ K₂ → σ ∈ Icc (-S) S →
          |windowFiniteProd f σf σSeq εHat K₂ σ - windowFiniteProd f σf σSeq εHat K₁ σ| ≤ C / (K₁ : ℝ)) ∧
        (∀ {K : ℕ} {σ : ℝ}, K_min ≤ K → σ ∈ Icc (-S) S →
          |windowFiniteProd f σf σSeq εHat K σ - tildeW f σf σSeq εHat σ| ≤ C / (K : ℝ)) := by
  obtain ⟨K_c, C_c, hKc_N, hKc_1, hCc_pos, hcauchy⟩ :=
    window_tail_cauchy_log_bound (N := N) hC_t hS
  let K_min : ℕ := max K_c (Nat.ceil (2 * C_c) + 1)
  have hKmin_Kc : K_c ≤ K_min := le_max_left _ _
  have hKmin_N : N ≤ K_min := hKc_N.trans hKmin_Kc
  have hKmin_1 : 1 ≤ K_min := hKc_1.trans hKmin_Kc
  have hKmin_pos : (0 : ℝ) < (K_min : ℝ) := by exact_mod_cast hKmin_1
  have hCc_half : C_c / (K_min : ℝ) ≤ 1 / 2 := by
    have h1 : 2 * C_c ≤ (Nat.ceil (2 * C_c) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (2 * C_c) + 1 : ℕ) : ℝ) ≤ (K_min : ℝ) := by exact_mod_cast le_max_right K_c _
    have h3 : 2 * C_c ≤ (K_min : ℝ) := by push_cast at h2; linarith
    rw [div_le_iff₀ hKmin_pos]; linarith
  have hcont_fq : Continuous (continuumFQ (continuumAK K_min)) :=
    continuous_continuumFQ (continuumAK K_min) (continuumAK_nonneg K_min)
  obtain ⟨B_fq, _, hB_fq⟩ : ∃ B_fq : ℝ, 0 ≤ B_fq ∧ ∀ σ ∈ Icc (-S) S,
      |continuumFQ (continuumAK K_min) σ| ≤ B_fq := by
    obtain ⟨σ₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (⟨0, by simp [hS]⟩ : (Icc (-S) S).Nonempty)
      (continuous_abs.comp hcont_fq).continuousOn
    refine ⟨max 0 |continuumFQ (continuumAK K_min) σ₀|, le_max_left _ _, fun σ hσ => ?_⟩
    exact (hmax hσ).trans (le_max_right _ _)
  let B_tail_Kmin : ℝ := ∏ k ∈ Finset.Icc (N + 1) K_min,
    ((S + phiWKB k + C_t) ^ 2 + C_t ^ 2)
  have hB_tail_nn : 0 ≤ B_tail_Kmin := Finset.prod_nonneg fun _ _ => by positivity
  let B_W : ℝ := Real.exp B_fq * (S + M) * (((S + M) ^ 2 + M ^ 2) ^ (N - f)) * max B_tail_Kmin 1
  have hB_W_pos : 0 < B_W := by dsimp [B_W]; positivity
  let C : ℝ := 4 * B_W * C_c
  refine ⟨K_min, C, hKmin_N, hKmin_1, by positivity, fun {σf σSeq εHat} hσf hmod htail => ?_⟩
  have hstep_base : ∀ {K₁ K₂ : ℕ} {σ : ℝ}, K_min ≤ K₁ → K₁ ≤ K₂ → σ ∈ Icc (-S) S →
      |windowFiniteProd f σf σSeq εHat K₂ σ - windowFiniteProd f σf σSeq εHat K₁ σ| ≤ C / (K₁ : ℝ) := by
    intro K₁ K₂ σ hK₁ hK₁₂ hσ
    have hσ_abs : |σ| ≤ S := abs_le.mpr ⟨hσ.1, hσ.2⟩
    have hKc_le1 : K_c ≤ K₁ := hKmin_Kc.trans hK₁
    obtain ⟨hpos01, hcau01⟩ := hcauchy htail hKmin_Kc hK₁ hσ_abs
    obtain ⟨hpos12, hcau12⟩ := hcauchy htail hKc_le1 hK₁₂ hσ_abs
    have hcau01' : |continuumFQ (continuumAK K₁) σ - continuumFQ (continuumAK K_min) σ +
        ∑ k ∈ Finset.Icc (K_min + 1) K₁, Real.log ((σ - σSeq k) ^ 2 + (εHat k) ^ 2)| ≤ 1 / 2 :=
      hcau01.trans hCc_half
    have hK₁_ge : (K_min : ℝ) ≤ (K₁ : ℝ) := by exact_mod_cast hK₁
    have hcau12' : |continuumFQ (continuumAK K₂) σ - continuumFQ (continuumAK K₁) σ +
        ∑ k ∈ Finset.Icc (K₁ + 1) K₂, Real.log ((σ - σSeq k) ^ 2 + (εHat k) ^ 2)| ≤ 1 / 2 := by
      refine hcau12.trans ?_
      have : C_c / (K₁ : ℝ) ≤ C_c / (K_min : ℝ) := div_le_div_of_nonneg_left hCc_pos.le hKmin_pos hK₁_ge
      linarith
    have hMKmin_bd : |windowFiniteProd f σf σSeq εHat K_min σ| ≤ B_W := by
      unfold windowFiniteProd
      have hexp_le : continuumFQ (continuumAK K_min) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) ≤ B_fq := by
        have h1 : continuumFQ (continuumAK K_min) σ ≤ B_fq := (le_abs_self _).trans (hB_fq σ hσ)
        have h2 : 0 ≤ 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) := by positivity
        linarith
      have hexp_bd : Real.exp (continuumFQ (continuumAK K_min) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ)) ≤
          Real.exp B_fq := Real.exp_le_exp.mpr hexp_le
      have hlin_bd : |σ - σf| ≤ S + M := (abs_sub _ _).trans (add_le_add hσ_abs hσf)
      have hIcc_split : Finset.Icc (f + 1) K_min = Finset.Icc (f + 1) N ∪ Finset.Icc (N + 1) K_min := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Icc (f + 1) N) (Finset.Icc (N + 1) K_min) := by
        rw [Finset.disjoint_left]; intro k hk1 hk2; simp only [Finset.mem_Icc] at hk1 hk2; omega
      have hmod_prod : |∏ k ∈ Finset.Icc (f + 1) N, ((σ - σSeq k) ^ 2 + (εHat k) ^ 2)| ≤
          ((S + M) ^ 2 + M ^ 2) ^ (N - f) := by
        have hle1 : ∏ k ∈ Finset.Icc (f + 1) N, ((σ - σSeq k) ^ 2 + (εHat k) ^ 2) ≤
            ∏ _k ∈ Finset.Icc (f + 1) N, ((S + M) ^ 2 + M ^ 2) := by
          refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun k hk => ?_
          obtain ⟨hsk, hek⟩ := hmod k hk
          have hs1 : |σ - σSeq k| ≤ S + M := (abs_sub _ _).trans (add_le_add hσ_abs hsk)
          have hs2 : (σ - σSeq k) ^ 2 ≤ (S + M) ^ 2 := by simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hs1 2
          have he2 : (εHat k) ^ 2 ≤ M ^ 2 := by simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hek 2
          linarith
        have hnn_p : 0 ≤ ∏ k ∈ Finset.Icc (f + 1) N, ((σ - σSeq k) ^ 2 + (εHat k) ^ 2) :=
          Finset.prod_nonneg fun _ _ => by positivity
        rw [abs_of_nonneg hnn_p]
        refine hle1.trans_eq ?_
        rw [Finset.prod_const, Nat.card_Icc]
        have hsub_eq : N + 1 - (f + 1) = N - f := by omega
        rw [hsub_eq]
      have htail_prod : |∏ k ∈ Finset.Icc (N + 1) K_min, ((σ - σSeq k) ^ 2 + (εHat k) ^ 2)| ≤ B_tail_Kmin := by
        have hle1 : ∏ k ∈ Finset.Icc (N + 1) K_min, ((σ - σSeq k) ^ 2 + (εHat k) ^ 2) ≤ B_tail_Kmin := by
          dsimp [B_tail_Kmin]
          refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun k hk => ?_
          have hk_gt : N < k := by simp only [Finset.mem_Icc] at hk; omega
          have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
          obtain ⟨hs, he⟩ := htail k hk_gt
          have hkr43 : (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 := by
            rw [Real.rpow_neg (by positivity)]; exact inv_le_one_of_one_le₀ (Real.one_le_rpow hk1 (by norm_num))
          have hkr13 : (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 := by
            rw [Real.rpow_neg (by positivity)]; exact inv_le_one_of_one_le₀ (Real.one_le_rpow hk1 (by norm_num))
          have hσk_abs : |σ - σSeq k| ≤ S + phiWKB k + C_t := by
            have h1 : |σSeq k| ≤ phiWKB k + C_t := by
              have hphi_nn : 0 ≤ phiWKB k := by
                unfold phiWKB; exact Real.rpow_nonneg (by linarith [hk1]) _
              have := abs_sub_abs_le_abs_sub (σSeq k) (phiWKB k)
              rw [abs_of_nonneg hphi_nn] at this
              nlinarith only [this, hs, hkr43, hC_t]
            exact (abs_sub _ _).trans (by linarith)
          have hs2 : (σ - σSeq k) ^ 2 ≤ (S + phiWKB k + C_t) ^ 2 := by
            simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hσk_abs 2
          have he2 : (εHat k) ^ 2 ≤ C_t ^ 2 := by
            have he' : |εHat k| ≤ C_t := by nlinarith only [he, hkr13, hC_t]
            simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) he' 2
          linarith
        have hnn_p : 0 ≤ ∏ k ∈ Finset.Icc (N + 1) K_min, ((σ - σSeq k) ^ 2 + (εHat k) ^ 2) :=
          Finset.prod_nonneg fun _ _ => by positivity
        rwa [abs_of_nonneg hnn_p]
      rw [hIcc_split, Finset.prod_union hdisj, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hmul1 : Real.exp (continuumFQ (continuumAK K_min) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ)) *
          |σ - σf| ≤ Real.exp B_fq * (S + M) :=
        mul_le_mul hexp_bd hlin_bd (abs_nonneg _) (Real.exp_pos _).le
      have hmp := mul_le_mul hmod_prod (htail_prod.trans (le_max_left B_tail_Kmin 1))
        (abs_nonneg _) (by positivity)
      exact (mul_le_mul hmul1 hmp (by positivity) (by positivity)).trans_eq (by dsimp [B_W]; ring)
    have hMK1_bd : |windowFiniteProd f σf σSeq εHat K₁ σ| ≤ 2 * B_W := by
      rw [windowFiniteProd_step_ratio hN hKmin_N hK₁ hpos01, abs_mul]
      have hexp_d : Real.exp ((continuumFQ (continuumAK K₁) σ - continuumFQ (continuumAK K_min) σ) +
          ∑ k ∈ Finset.Icc (K_min + 1) K₁, Real.log ((σ - σSeq k) ^ 2 + (εHat k) ^ 2)) ≤ 2 := by
        have h1 : _ ≤ (1 / 2 : ℝ) := (le_abs_self _).trans hcau01'
        have h2 := Real.exp_le_exp.mpr h1
        have hexp_half : Real.exp (1 / 2 : ℝ) ≤ 2 := by
          have hs : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
            rw [← Real.exp_nat_mul]; norm_num
          have hlt4 : Real.exp (1 / 2 : ℝ) ^ 2 < 2 ^ 2 := by
            rw [hs]; exact Real.exp_one_lt_d9.trans (by norm_num)
          nlinarith only [hlt4, Real.exp_pos (1 / 2 : ℝ)]
        exact h2.trans hexp_half
      rw [abs_of_pos (Real.exp_pos _)]
      calc |windowFiniteProd f σf σSeq εHat K_min σ| * _
          ≤ B_W * 2 := mul_le_mul hMKmin_bd hexp_d (Real.exp_pos _).le hB_W_pos.le
        _ = 2 * B_W := by ring
    have hMK1_pos_N : N ≤ K₁ := hKmin_N.trans hK₁
    rw [windowFiniteProd_step_ratio hN hMK1_pos_N hK₁₂ hpos12]
    set Δ := (continuumFQ (continuumAK K₂) σ - continuumFQ (continuumAK K₁) σ) +
      ∑ k ∈ Finset.Icc (K₁ + 1) K₂, Real.log ((σ - σSeq k) ^ 2 + (εHat k) ^ 2)
    have hΔ_exp := abs_exp_sub_one_le hcau12'
    calc |windowFiniteProd f σf σSeq εHat K₁ σ * Real.exp Δ -
          windowFiniteProd f σf σSeq εHat K₁ σ|
        = |windowFiniteProd f σf σSeq εHat K₁ σ| * |Real.exp Δ - 1| := by
            rw [show _ * Real.exp Δ - _ = _ * (Real.exp Δ - 1) by ring, abs_mul]
      _ ≤ (2 * B_W) * (2 * |Δ|) :=
          mul_le_mul hMK1_bd hΔ_exp (abs_nonneg _) (by positivity)
      _ ≤ (2 * B_W) * (2 * (C_c / (K₁ : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcau12 (by norm_num)) (by positivity)
      _ = C / (K₁ : ℝ) := by dsimp [C]; ring
  refine ⟨hstep_base, fun {K σ} hK hσ => ?_⟩
  have hcauchySeq : CauchySeq (fun K' : ℕ => windowFiniteProd f σf σSeq εHat K' σ) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N_c, hNc⟩ := exists_nat_gt (C / ε)
    refine ⟨max K_min N_c, fun m hm n hn => ?_⟩
    wlog hmn : m ≤ n generalizing m n
    · rw [dist_comm]; exact this n hn m hm (le_of_not_ge hmn)
    have hm_min : K_min ≤ m := (le_max_left _ _).trans hm
    have hm_Nc : (N_c : ℝ) ≤ (m : ℝ) := by exact_mod_cast (le_max_right K_min N_c).trans hm
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (hKmin_1.trans hm_min)
    rw [Real.dist_eq, abs_sub_comm]
    calc |windowFiniteProd f σf σSeq εHat n σ - windowFiniteProd f σf σSeq εHat m σ|
        ≤ C / (m : ℝ) := hstep_base hm_min hmn hσ
      _ < ε := by
          rw [div_lt_iff₀ hm_pos]
          have h1 : C / ε < (m : ℝ) := hNc.trans_le hm_Nc
          rw [div_lt_iff₀ hε] at h1
          linarith
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchySeq
  have hlim_eq : tildeW f σf σSeq εHat σ = L := hL.limUnder_eq
  rw [hlim_eq, abs_sub_comm]
  have h_ev : ∀ᶠ K' in atTop,
      |windowFiniteProd f σf σSeq εHat K' σ - windowFiniteProd f σf σSeq εHat K σ| ≤ C / (K : ℝ) := by
    filter_upwards [eventually_ge_atTop K] with K' hK'
    exact hstep_base hK hK' hσ
  have htend_abs : Tendsto (fun K' : ℕ =>
      |windowFiniteProd f σf σSeq εHat K' σ - windowFiniteProd f σf σSeq εHat K σ|)
      atTop (𝓝 |L - windowFiniteProd f σf σSeq εHat K σ|) :=
    (hL.sub tendsto_const_nhds).abs
  exact le_of_tendsto htend_abs h_ev

/-- Continuity of the window limit `tildeW f σf σSeq εHat` on `ℝ`. -/
theorem continuous_tildeW (f N : ℕ) (hf : 1 ≤ f) (hN : f ≤ N)
    {M C_t : ℝ} (hM : 0 < M) (hC_t : 0 < C_t)
    {σf : ℝ} {σSeq εHat : ℕ → ℝ}
    (hσf : |σf| ≤ M)
    (hmod : ∀ k ∈ Finset.Icc (f + 1) N, |σSeq k| ≤ M ∧ |εHat k| ≤ M)
    (htail : ∀ k : ℕ, N < k →
      |σSeq k - phiWKB k| ≤ C_t * (k : ℝ) ^ (-(4 / 3 : ℝ)) ∧ |εHat k| ≤ C_t * (k : ℝ) ^ (-(1 / 3 : ℝ))) :
    Continuous (tildeW f σf σSeq εHat) := by
  rw [continuous_iff_continuousAt]
  intro σ₀
  set S : ℝ := |σ₀| + 1
  have hS : 0 ≤ S := by positivity
  obtain ⟨K_min, C, _, hKmin_1, _, hrate⟩ :=
    tendsto_windowFiniteProd_uniform f N hf hN hM hC_t hS
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨K, hK_ge, _⟩ : ∃ K : ℕ, K_min ≤ K ∧ C / (K : ℝ) < ε / 3 := by
    obtain ⟨K₁, hK₁⟩ := exists_nat_gt (3 * C / ε)
    refine ⟨max K_min (K₁ + 1), le_max_left _ _, ?_⟩
    have hK_pos : (0 : ℝ) < ((max K_min (K₁ + 1) : ℕ) : ℝ) := by
      exact_mod_cast hKmin_1.trans (le_max_left _ _)
    rw [div_lt_iff₀ hK_pos]
    have hK₁_le : (K₁ : ℝ) < ((max K_min (K₁ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (by omega : K₁ < max K_min (K₁ + 1))
    have h1 : 3 * C / ε < ((max K_min (K₁ + 1) : ℕ) : ℝ) := hK₁.trans hK₁_le
    rw [div_lt_iff₀ hε] at h1
    linarith
  have hcontK := Metric.continuousAt_iff.mp
    ((continuous_windowFiniteProd f σf σSeq εHat K).continuousAt (x := σ₀)) (ε / 3) (by linarith)
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := hcontK
  refine ⟨min δ₀ 1, lt_min hδ₀_pos zero_lt_one, fun {σ} hσ_dist => ?_⟩
  have hσ_mem : σ ∈ Icc (-S) S := by
    rw [Real.dist_eq] at hσ_dist
    have h1 : |σ - σ₀| < 1 := hσ_dist.trans_le (min_le_right _ _)
    have h2 : |σ| ≤ |σ₀| + 1 := by
      calc |σ| = |(σ - σ₀) + σ₀| := by ring_nf
        _ ≤ |σ - σ₀| + |σ₀| := abs_add_le _ _
        _ ≤ 1 + |σ₀| := by linarith
        _ = S := by ring
    exact abs_le.mp h2
  have hσ₀_mem : σ₀ ∈ Icc (-S) S := by
    have : |σ₀| ≤ S := by dsimp [S]; linarith
    exact abs_le.mp this
  have h1 := hrate hσf hmod htail |>.2 hK_ge hσ_mem
  have h2 := hrate hσf hmod htail |>.2 hK_ge hσ₀_mem
  have h3 := hδ₀ (hσ_dist.trans_le (min_le_left _ _))
  rw [Real.dist_eq] at h3 ⊢
  have hid : tildeW f σf σSeq εHat σ - tildeW f σf σSeq εHat σ₀ =
      (tildeW f σf σSeq εHat σ - windowFiniteProd f σf σSeq εHat K σ) +
      (windowFiniteProd f σf σSeq εHat K σ - windowFiniteProd f σf σSeq εHat K σ₀) +
      (windowFiniteProd f σf σSeq εHat K σ₀ - tildeW f σf σSeq εHat σ₀) := by ring
  rw [hid]
  have ha1 := abs_add_le
    ((tildeW f σf σSeq εHat σ - windowFiniteProd f σf σSeq εHat K σ) +
      (windowFiniteProd f σf σSeq εHat K σ - windowFiniteProd f σf σSeq εHat K σ₀))
    (windowFiniteProd f σf σSeq εHat K σ₀ - tildeW f σf σSeq εHat σ₀)
  have ha2 := abs_add_le
    (tildeW f σf σSeq εHat σ - windowFiniteProd f σf σSeq εHat K σ)
    (windowFiniteProd f σf σSeq εHat K σ - windowFiniteProd f σf σSeq εHat K σ₀)
  rw [abs_sub_comm (tildeW f σf σSeq εHat σ) _] at ha2
  linarith

/-! ### Section 3: Blaschke Real-Axis Identities and Window Splitting -/

private lemma blaschkeT_ofReal_eq (χ x : ℝ) :
    blaschkeT (χ : ℂ) (x : ℂ) =
      ((Real.tanh (π * (x - χ) / 2) * Real.tanh (π * (x + χ) / 2) : ℝ) : ℂ) := by
  unfold blaschkeT
  have hc1 : Complex.tanh ((π : ℂ) * ((x : ℂ) - (χ : ℂ)) / 2) =
      ((Real.tanh (π * (x - χ) / 2) : ℝ) : ℂ) := by
    have h1 : Complex.tanh ((π * (x - χ) / 2 : ℝ) : ℂ) =
        ((Real.tanh (π * (x - χ) / 2) : ℝ) : ℂ) := by
      rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
        ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_div]
    rw [← h1]; congr 1; push_cast; ring
  have hc2 : Complex.tanh ((π : ℂ) * ((x : ℂ) + (χ : ℂ)) / 2) =
      ((Real.tanh (π * (x + χ) / 2) : ℝ) : ℂ) := by
    have h1 : Complex.tanh ((π * (x + χ) / 2 : ℝ) : ℂ) =
        ((Real.tanh (π * (x + χ) / 2) : ℝ) : ℂ) := by
      rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
        ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_div]
    rw [← h1]; congr 1; push_cast; ring
  rw [hc1, hc2, ← Complex.ofReal_mul]

private lemma tanh_conj_complex (w : ℂ) :
    Complex.tanh (star w) = star (Complex.tanh w) := by
  change Complex.tanh ((starRingEnd ℂ) w) = (starRingEnd ℂ) (Complex.tanh w)
  rw [Complex.tanh_eq_sinh_div_cosh, Complex.tanh_eq_sinh_div_cosh,
    map_div₀, Complex.sinh_conj, Complex.cosh_conj]

private lemma blaschkeT_pair_real (χ ε x : ℝ) :
    blaschkeT ((χ : ℂ) + (ε : ℂ) * Complex.I) (x : ℂ) *
        blaschkeT ((χ : ℂ) - (ε : ℂ) * Complex.I) (x : ℂ) =
      ((blaschkePairQ χ ε x : ℝ) : ℂ) := by
  have hconj_eq : blaschkeT ((χ : ℂ) - (ε : ℂ) * Complex.I) (x : ℂ) =
      star (blaschkeT ((χ : ℂ) + (ε : ℂ) * Complex.I) (x : ℂ)) := by
    unfold blaschkeT
    have h1 : (π : ℂ) * ((x : ℂ) - ((χ : ℂ) - (ε : ℂ) * Complex.I)) / 2 =
        star ((π : ℂ) * ((x : ℂ) - ((χ : ℂ) + (ε : ℂ) * Complex.I)) / 2) := by
      change _ = (starRingEnd ℂ) _
      simp only [map_div₀, map_mul, map_sub, map_add, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
      ring
    have h2 : (π : ℂ) * ((x : ℂ) + ((χ : ℂ) - (ε : ℂ) * Complex.I)) / 2 =
        star ((π : ℂ) * ((x : ℂ) + ((χ : ℂ) + (ε : ℂ) * Complex.I)) / 2) := by
      change _ = (starRingEnd ℂ) _
      simp only [map_div₀, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
      ring
    rw [h1, h2, tanh_conj_complex, tanh_conj_complex]
    change _ = (starRingEnd ℂ) _
    rw [map_mul]; rfl
  rw [hconj_eq]
  set z : ℂ := blaschkeT ((χ : ℂ) + (ε : ℂ) * Complex.I) (x : ℂ)
  have hz : z * star z = ((Complex.normSq z : ℝ) : ℂ) := by
    rw [mul_comm, Complex.normSq_eq_conj_mul_self]; rfl
  rw [hz, Complex.normSq_eq_norm_sq]
  have hp : blaschkePairQ χ ε x = ‖z‖ ^ 2 := by
    unfold blaschkePairQ
    have hconj : ‖blaschkeT ((χ : ℂ) - (ε : ℂ) * Complex.I) (x : ℂ)‖ = ‖z‖ := by
      rw [hconj_eq, norm_star]
    dsimp [z] at hconj ⊢
    rw [norm_mul, hconj, sq]
  rw [hp]

private lemma tanh_pi_mul_xiStar : Real.tanh (π * xiStar) = 1 / Real.sqrt 2 := by
  have h1 : Real.cosh (π * xiStar) ^ 2 - Real.sinh (π * xiStar) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (π * xiStar)
  rw [sinh_pi_mul_xiStar, one_pow] at h1
  have hpos : 0 < Real.cosh (π * xiStar) := Real.cosh_pos _
  have hcosh : Real.cosh (π * xiStar) = Real.sqrt 2 := by
    rw [← Real.sqrt_sq hpos.le, show Real.cosh (π * xiStar) ^ 2 = 2 by linarith]
  rw [Real.tanh_eq_sinh_div_cosh, sinh_pi_mul_xiStar, hcosh]

private lemma lambdaComb_pos {c' : ℝ} (hc' : 0 < c') : 0 < lambdaComb c' := by
  have := kTip_pos
  unfold lambdaComb
  positivity

private noncomputable def combTailFactor (c' η₀ x : ℝ) (N m : ℕ) : ℂ :=
  let χm : ℝ := chiQuantile c' (N + 1 + m : ℕ)
  let εm : ℝ := η₀ * siteGap c' (N + 1 + m)
  blaschkeT ((χm : ℂ) + (εm : ℂ) * Complex.I) (x : ℂ) *
    blaschkeT ((χm : ℂ) - (εm : ℂ) * Complex.I) (x : ℂ)

private lemma riesz_tail_log_mul_id {c' : ℝ} {N K₀ : ℕ} {η₀ x : ℝ}
    (hc' : 0 < c') (hη0 : 0 ≤ η₀) (hη1 : η₀ ≤ 1 / 4) (hgap : siteGap c' 1 ≤ 1 / 2)
    (hx_nn : 0 ≤ x) (hx_lt : x < chiQuantile c' (K₀ : ℕ)) (hN1 : N + 1 ≤ K₀) :
    (∏' m : ℕ, combTailFactor c' η₀ x N m).re =
      (∏ k ∈ Finset.Icc (N + 1) K₀, pairModQ c' η₀ x k) *
        Real.exp (∑' m : ℕ, Real.log (pairModQ c' η₀ x (K₀ + 1 + m))) := by
  have hχ_nn : ∀ m : ℕ, 0 ≤ chiQuantile c' (N + 1 + m : ℕ) := fun m => by
    have ha : (1 / 4 : ℝ) ≤ ((N + 1 + m : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((N + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N + 1 + m)
      linarith
    exact xiStar_pos.le.trans (chiQuantile_spec hc' ha).1
  have hε_bd : ∀ m : ℕ, |η₀ * siteGap c' (N + 1 + m)| ≤ 1 / 8 := fun m => by
    have hgk : siteGap c' (N + 1 + m) ≤ siteGap c' 1 := by
      have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ N + m by omega)
      have heq : (N + m) + 1 = N + 1 + m := by omega
      simpa [heq] using hanti
    have hgk_nn : 0 ≤ siteGap c' (N + 1 + m) := by
      unfold siteGap
      have hm1 : (1 : ℝ) ≤ ((N + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N + 1 + m)
      exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn
        (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) (by linarith))
    rw [abs_of_nonneg (mul_nonneg hη0 hgk_nn)]
    nlinarith
  have hsum := summable_exp_neg_pi_chiQuantile hc' N
  have hhasProd := (comb_pairProd_hasProdLocallyUniformlyOn _ _ hχ_nn hε_bd hsum).hasProd
    (by simp : (x : ℂ) ∈ {b : ℂ | |b.im| < 7 / 8})
  have hhead_eq : ∏ i ∈ Finset.range (K₀ - N), combTailFactor c' η₀ x N i =
      ((∏ k ∈ Finset.Icc (N + 1) K₀, pairModQ c' η₀ x k : ℝ) : ℂ) := by
    have hbij : ∏ i ∈ Finset.range (K₀ - N), pairModQ c' η₀ x (N + 1 + i) =
        ∏ k ∈ Finset.Icc (N + 1) K₀, pairModQ c' η₀ x k := by
      symm
      refine Finset.prod_bij (fun k _ => k - (N + 1)) ?_ ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        simp only [Finset.mem_range]; omega
      · intro a ha b hb h
        simp only [Finset.mem_Icc] at ha hb
        omega
      · intro b hb
        simp only [Finset.mem_range] at hb
        refine ⟨N + 1 + b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        congr 1; omega
    rw [← hbij, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold combTailFactor pairModQ; exact blaschkeT_pair_real _ _ _
  have hK₀_gt1 : 1 ≤ K₀ := by omega
  have hχ_mono : ∀ {a b : ℝ}, (1 / 4 : ℝ) ≤ a → a ≤ b → chiQuantile c' a ≤ chiQuantile c' b :=
    fun ha hab => (chiQuantile_strictMonoOn hc').monotoneOn ha (ha.trans hab) hab
  have hχ_strict : ∀ {a b : ℝ}, (1 / 4 : ℝ) ≤ a → a < b → chiQuantile c' a < chiQuantile c' b :=
    fun ha hab => chiQuantile_strictMonoOn hc' ha (ha.trans hab.le) hab
  have hK1_ge : (1 / 4 : ℝ) ≤ ((K₀ + 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((K₀ + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ K₀ + 1)
    linarith
  have hK_lt : chiQuantile c' (K₀ : ℕ) < chiQuantile c' (K₀ + 1 : ℕ) := by
    have hK_r : (1 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hK₀_gt1
    exact hχ_strict (by linarith only [hK_r]) (by push_cast; linarith)
  have hx_lt_next : x < chiQuantile c' (K₀ + 1 : ℕ) := hx_lt.trans hK_lt
  have hf_ne : chiQuantile c' (K₀ : ℕ) ≠ x := hx_lt.ne'
  have hq_pos : ∀ m : ℕ, 0 < pairModQ c' η₀ x (K₀ + 1 + m) := fun m => by
    unfold pairModQ
    have hm_gt : ((K₀ + 1 : ℕ) : ℝ) ≤ ((K₀ + 1 + m : ℕ) : ℝ) := by
      exact_mod_cast (by omega : K₀ + 1 ≤ K₀ + 1 + m)
    have hχ_gt : x < chiQuantile c' ((K₀ + 1 + m : ℕ) : ℝ) :=
      lt_of_lt_of_le hx_lt_next (hχ_mono hK1_ge hm_gt)
    have hm_14 : (1 / 4 : ℝ) ≤ ((K₀ + 1 + m : ℕ) : ℝ) := hK1_ge.trans hm_gt
    have hχ_xi : xiStar ≤ chiQuantile c' ((K₀ + 1 + m : ℕ) : ℝ) :=
      (chiQuantile_spec hc' hm_14).1
    have hgap_nn : 0 ≤ siteGap c' (K₀ + 1 + m) := by
      unfold siteGap
      have hlt := hχ_strict hm_14 (by linarith : ((K₀ + 1 + m : ℕ) : ℝ) < ((K₀ + 1 + m : ℕ) : ℝ) + 1)
      linarith
    have hgap_le : siteGap c' (K₀ + 1 + m) ≤ siteGap c' 1 := by
      have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ K₀ + m by omega)
      have heq : (K₀ + m) + 1 = K₀ + 1 + m := by omega
      simpa [heq] using hanti
    have hε_bd' : |η₀ * siteGap c' (K₀ + 1 + m)| ≤ 1 / 4 := by
      rw [abs_of_nonneg (mul_nonneg hη0 hgap_nn)]
      nlinarith
    exact blaschkePairQ_pos_of_ne hχ_gt.ne hε_bd' hx_nn (xiStar_pos.le.trans hχ_xi)
  obtain ⟨hsumm_q, _⟩ := refComb_norm_log_eq_tsum hc' hx_nn (f := K₀) hK₀_gt1 hη0 hη1 hgap hf_ne hq_pos
  have hshift_m : ∀ m : ℕ, combTailFactor c' η₀ x N ((K₀ - N) + m) =
      ((pairModQ c' η₀ x (K₀ + 1 + m) : ℝ) : ℂ) := fun m => by
    have hid : N + 1 + ((K₀ - N) + m) = K₀ + 1 + m := by omega
    unfold combTailFactor; rw [hid]; unfold pairModQ; exact blaschkeT_pair_real _ _ _
  have h_prod_exp : HasProd (fun m : ℕ => pairModQ c' η₀ x (K₀ + 1 + m))
      (Real.exp (∑' m : ℕ, Real.log (pairModQ c' η₀ x (K₀ + 1 + m)))) := by
    refine (Real.continuous_exp.continuousAt.tendsto.comp hsumm_q.hasSum).congr fun s => ?_
    dsimp [Function.comp_def]
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun m _ => Real.exp_log (hq_pos m)
  have hrange_top0 : Tendsto (Finset.range : ℕ → Finset ℕ) atTop atTop := by
    rw [tendsto_atTop]
    intro s
    rw [Filter.eventually_atTop]
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨0, fun _ _ => Finset.empty_subset _⟩
    · refine ⟨s.max' hs + 1, fun M hM y hy => Finset.mem_range.mpr ?_⟩
      have h1 : y ≤ s.max' hs := Finset.le_max' s y hy
      omega
  have hrange_top : Tendsto (fun M : ℕ => Finset.range (K₀ - N + M)) atTop atTop :=
    hrange_top0.comp (tendsto_atTop_atTop.mpr fun b => ⟨b, fun M hM => by omega⟩)
  have ht1 : Tendsto (fun M : ℕ => ∏ m ∈ Finset.range (K₀ - N + M), combTailFactor c' η₀ x N m)
      atTop (𝓝 (∏' m : ℕ, combTailFactor c' η₀ x N m)) :=
    hhasProd.comp hrange_top
  have ht2 : Tendsto (fun M : ℕ => ∏ m ∈ Finset.range (K₀ - N + M), combTailFactor c' η₀ x N m)
      atTop (𝓝 ((∏ i ∈ Finset.range (K₀ - N), combTailFactor c' η₀ x N i) *
        ((Real.exp (∑' m : ℕ, Real.log (pairModQ c' η₀ x (K₀ + 1 + m))) : ℝ) : ℂ))) := by
    have ht_tail : Tendsto (fun M : ℕ => ∏ m ∈ Finset.range M, ((pairModQ c' η₀ x (K₀ + 1 + m) : ℝ) : ℂ))
        atTop (𝓝 ((Real.exp (∑' m : ℕ, Real.log (pairModQ c' η₀ x (K₀ + 1 + m))) : ℝ) : ℂ)) := by
      have h1 := Complex.continuous_ofReal.continuousAt.tendsto.comp (h_prod_exp.comp hrange_top0)
      refine h1.congr fun M => ?_
      dsimp [Function.comp_def]
      rw [Complex.ofReal_prod]
    refine (tendsto_const_nhds.mul ht_tail).congr fun M => ?_
    rw [Finset.prod_range_add]
    congr 1
    exact Finset.prod_congr rfl fun m _ => (hshift_m m).symm
  have hprod_eq : (∏' m : ℕ, combTailFactor c' η₀ x N m) =
      (((∏ k ∈ Finset.Icc (N + 1) K₀, pairModQ c' η₀ x k) *
        Real.exp (∑' m : ℕ, Real.log (pairModQ c' η₀ x (K₀ + 1 + m))) : ℝ) : ℂ) := by
    rw [tendsto_nhds_unique ht1 ht2, hhead_eq, ← Complex.ofReal_mul]
  rw [hprod_eq, Complex.ofReal_re]

private lemma modifiedH0_window_factorization
    {f N K₀ : ℕ} (d : ModifiedCombData f N) {c' x : ℝ}
    (_hf : 1 ≤ f) (hN : f ≤ N) (hK₀ : N + 1 ≤ K₀)
    (hc' : 0 < c') (hη0 : 0 ≤ d.eta0) (hη1 : d.eta0 ≤ 1 / 4) (hgap : siteGap c' 1 ≤ 1 / 2)
    (hx_nn : 0 ≤ x) (hx_lt : x < chiQuantile c' (K₀ : ℕ)) :
    let P₀ : ℝ := π * lambdaComb c' / (2 * Real.sqrt 2)
    let a₀ : ℝ := (K₀ : ℝ) + 1 / 2
    let χf : ℝ := xiStar + lambdaComb c' * d.sigmaF c'
    let tailRem : ℝ := (∑' m : ℕ, Real.log (pairModQ c' d.eta0 x (K₀ + 1 + m))) -
      2 * ∫ a in Set.Ioi a₀, phiVar c' x a
    (modifiedH0 f N d c' x * Real.exp (c' * slitL x)) / windowNormKTilde f c' =
      (Real.cosh (π * xiStar / 2) ^ 2 / Real.cosh (π * x / 2) ^ 2) *
        (P₀⁻¹ * (Real.tanh (π * (x - χf) / 2) * Real.tanh (π * (x + χf) / 2))) *
        (∏ k ∈ Finset.Icc (f + 1) N,
          P₀ ^ (-2 : ℤ) * blaschkePairQ (xiStar + lambdaComb c' * d.sigmaK c' k)
            (lambdaComb c' * d.epsHat c' k) x) *
        (∏ k ∈ Finset.Icc (N + 1) K₀, P₀ ^ (-2 : ℤ) * pairModQ c' d.eta0 x k) *
        Real.exp (-2 * (∫ a in (1 / 4 : ℝ)..a₀, (phiVar c' x a - Real.log P₀)) +
          c' * (majorantReal x + slitL x)) *
        Real.exp tailRem := by
  intro P₀ a₀ χf tailRem
  have hlam_pos : 0 < lambdaComb c' := lambdaComb_pos hc'
  have hP₀_pos : 0 < P₀ := by dsimp [P₀]; positivity
  have hsplit_B : (modifiedCombB f N d c' (x : ℂ)).re =
      (Real.tanh (π * (x - χf) / 2) * Real.tanh (π * (x + χf) / 2)) *
        (∏ k ∈ Finset.Icc (f + 1) N,
          blaschkePairQ (xiStar + lambdaComb c' * d.sigmaK c' k) (lambdaComb c' * d.epsHat c' k) x) *
        ((∏ k ∈ Finset.Icc (N + 1) K₀, pairModQ c' d.eta0 x k) *
          Real.exp (∑' m : ℕ, Real.log (pairModQ c' d.eta0 x (K₀ + 1 + m)))) := by
    have htail_eq := riesz_tail_log_mul_id (N := N) (K₀ := K₀) hc' hη0 hη1 hgap hx_nn hx_lt hK₀
    have hT_eq : blaschkeT ((xiStar + lambdaComb c' * d.sigmaF c' : ℝ) : ℂ) (x : ℂ) =
        ((Real.tanh (π * (x - χf) / 2) * Real.tanh (π * (x + χf) / 2) : ℝ) : ℂ) := by
      dsimp [χf]; exact blaschkeT_ofReal_eq (xiStar + lambdaComb c' * d.sigmaF c') x
    have hfin_eq :
        (∏ k ∈ Finset.Icc (f + 1) N,
          blaschkeT (((xiStar + lambdaComb c' * d.sigmaK c' k : ℝ) : ℂ) +
              ((lambdaComb c' * d.epsHat c' k : ℝ) : ℂ) * Complex.I) (x : ℂ) *
            blaschkeT (((xiStar + lambdaComb c' * d.sigmaK c' k : ℝ) : ℂ) -
              ((lambdaComb c' * d.epsHat c' k : ℝ) : ℂ) * Complex.I) (x : ℂ)) =
        ((∏ k ∈ Finset.Icc (f + 1) N,
          blaschkePairQ (xiStar + lambdaComb c' * d.sigmaK c' k) (lambdaComb c' * d.epsHat c' k) x : ℝ) : ℂ) := by
      rw [Complex.ofReal_prod]
      exact Finset.prod_congr rfl fun k _ =>
        blaschkeT_pair_real (xiStar + lambdaComb c' * d.sigmaK c' k) (lambdaComb c' * d.epsHat c' k) x
    have hmb_eq : modifiedCombB f N d c' (x : ℂ) =
        blaschkeT ((xiStar + lambdaComb c' * d.sigmaF c' : ℝ) : ℂ) (x : ℂ) *
          (∏ k ∈ Finset.Icc (f + 1) N,
            blaschkeT (((xiStar + lambdaComb c' * d.sigmaK c' k : ℝ) : ℂ) +
                ((lambdaComb c' * d.epsHat c' k : ℝ) : ℂ) * Complex.I) (x : ℂ) *
              blaschkeT (((xiStar + lambdaComb c' * d.sigmaK c' k : ℝ) : ℂ) -
                ((lambdaComb c' * d.epsHat c' k : ℝ) : ℂ) * Complex.I) (x : ℂ)) *
          ∏' m : ℕ, combTailFactor c' d.eta0 x N m := by
      unfold modifiedCombB; rfl
    rw [hmb_eq, hT_eq, hfin_eq, ← Complex.ofReal_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, htail_eq]
  have hriesz_full := (riesz_real_identities hc' hx_nn 1 le_rfl).2
  have hint_full : IntegrableOn (phiVar c' x) (Set.Ioi (1 / 4 : ℝ)) volume := hriesz_full.1
  have hmaj_eq : 2 * ∫ a in Set.Ioi (1 / 4 : ℝ), phiVar c' x a = c' * majorantReal x := hriesz_full.2.1
  have hsplit_int : (∫ a in Set.Ioi (1 / 4 : ℝ), phiVar c' x a) =
      (∫ a in (1 / 4 : ℝ)..a₀, phiVar c' x a) + ∫ a in Set.Ioi a₀, phiVar c' x a := by
    have ha0_ge : (1 / 4 : ℝ) ≤ a₀ := by dsimp [a₀]; linarith [Nat.cast_nonneg (α := ℝ) K₀]
    have h1 : IntervalIntegrable (phiVar c' x) volume (1 / 4) a₀ :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ha0_ge).mpr
        (hint_full.mono_set Set.Ioc_subset_Ioi_self)
    have h2 : IntegrableOn (phiVar c' x) (Set.Ioi a₀) volume :=
      hint_full.mono_set (Set.Ioi_subset_Ioi ha0_ge)
    have h_union : Set.Ioi (1 / 4 : ℝ) = Set.Ioc (1 / 4) a₀ ∪ Set.Ioi a₀ := by
      ext y; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro hy; by_cases hya : y ≤ a₀; exact Or.inl ⟨hy, hya⟩; exact Or.inr (lt_of_not_ge hya)
      · rintro (⟨hy, _⟩ | hy); exact hy; exact ha0_ge.trans_lt hy
    have h_disj : Disjoint (Set.Ioc (1 / 4) a₀) (Set.Ioi a₀) := by
      rw [Set.disjoint_left]; intro y hy1 hy2; exact absurd hy2.out (not_lt.mpr hy1.2)
    rw [h_union, MeasureTheory.setIntegral_union h_disj measurableSet_Ioi
      (hint_full.mono_set Set.Ioc_subset_Ioi_self) h2,
      intervalIntegral.integral_of_le ha0_ge]
  have hint_sub : ∫ a in (1 / 4 : ℝ)..a₀, (phiVar c' x a - Real.log P₀) =
      (∫ a in (1 / 4 : ℝ)..a₀, phiVar c' x a) - (a₀ - 1 / 4) * Real.log P₀ := by
    have ha0_ge : (1 / 4 : ℝ) ≤ a₀ := by dsimp [a₀]; linarith [Nat.cast_nonneg (α := ℝ) K₀]
    have h1 : IntervalIntegrable (phiVar c' x) volume (1 / 4) a₀ :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ha0_ge).mpr
        (hint_full.mono_set Set.Ioc_subset_Ioi_self)
    rw [intervalIntegral.integral_sub h1 intervalIntegrable_const, intervalIntegral.integral_const,
      smul_eq_mul]
  have hlog_pow : Real.exp (2 * ((a₀ - 1 / 4) * Real.log P₀)) =
      P₀ ^ (2 * ((K₀ : ℝ) + 1 / 4)) := by
    have ha0_sub : a₀ - 1 / 4 = (K₀ : ℝ) + 1 / 4 := by dsimp [a₀]; ring
    rw [ha0_sub, show 2 * (((K₀ : ℝ) + 1 / 4) * Real.log P₀) = Real.log P₀ * (2 * ((K₀ : ℝ) + 1 / 4)) by ring,
      ← Real.rpow_def_of_pos hP₀_pos]
  have hP0_pull1 : ∏ k ∈ Finset.Icc (f + 1) N,
        P₀ ^ (-2 : ℤ) * blaschkePairQ (xiStar + lambdaComb c' * d.sigmaK c' k)
          (lambdaComb c' * d.epsHat c' k) x =
      (P₀ ^ (-2 : ℤ)) ^ (N - f) *
        ∏ k ∈ Finset.Icc (f + 1) N,
          blaschkePairQ (xiStar + lambdaComb c' * d.sigmaK c' k) (lambdaComb c' * d.epsHat c' k) x := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
    have hs : N + 1 - (f + 1) = N - f := by omega
    rw [hs]
  have hP0_pull2 : ∏ k ∈ Finset.Icc (N + 1) K₀, P₀ ^ (-2 : ℤ) * pairModQ c' d.eta0 x k =
      (P₀ ^ (-2 : ℤ)) ^ (K₀ - N) * ∏ k ∈ Finset.Icc (N + 1) K₀, pairModQ c' d.eta0 x k := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc]
    have hs : K₀ + 1 - (N + 1) = K₀ - N := by omega
    rw [hs]
  have hP0_net : P₀⁻¹ * (P₀ ^ (-2 : ℤ)) ^ (N - f) * (P₀ ^ (-2 : ℤ)) ^ (K₀ - N) *
      P₀ ^ (2 * ((K₀ : ℝ) + 1 / 4)) =
      P₀ ^ (2 * ((f : ℝ) - 1 / 4)) := by
    rw [← Real.rpow_neg_one P₀, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul,
      ← Real.rpow_intCast P₀, ← Real.rpow_intCast P₀,
      ← Real.rpow_add hP₀_pos, ← Real.rpow_add hP₀_pos, ← Real.rpow_add hP₀_pos]
    congr 1
    have hNf : (f : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNK : (N : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast (by omega : N ≤ K₀)
    push_cast [Nat.cast_sub hN, Nat.cast_sub (by omega : N ≤ K₀)]
    ring
  have hKT_inv : (windowNormKTilde f c')⁻¹ =
      Real.cosh (π * xiStar / 2) ^ 2 * P₀ ^ (2 * ((f : ℝ) - 1 / 4)) := by
    unfold windowNormKTilde
    have hP_eq : (2 * Real.sqrt 2 / (π * lambdaComb c'))⁻¹ = P₀ := by
      dsimp [P₀]; rw [inv_div]
    rw [mul_inv, one_div, inv_inv, ← Real.inv_rpow (by positivity), hP_eq]
  have hexp_split : Real.exp (-2 * (∫ a in (1 / 4 : ℝ)..a₀, (phiVar c' x a - Real.log P₀)) +
        c' * (majorantReal x + slitL x)) * Real.exp tailRem =
      P₀ ^ (2 * ((K₀ : ℝ) + 1 / 4)) * Real.exp (c' * slitL x) *
        Real.exp (∑' m : ℕ, Real.log (pairModQ c' d.eta0 x (K₀ + 1 + m))) := by
    have ha_id : -2 * (∫ a in (1 / 4 : ℝ)..a₀, (phiVar c' x a - Real.log P₀)) +
        c' * (majorantReal x + slitL x) + tailRem =
        2 * ((a₀ - 1 / 4) * Real.log P₀) + c' * slitL x +
          ∑' m : ℕ, Real.log (pairModQ c' d.eta0 x (K₀ + 1 + m)) := by
      rw [mul_add, hint_sub, ← hmaj_eq, hsplit_int]
      dsimp [tailRem]
      ring
    rw [← Real.exp_add, ha_id, Real.exp_add, Real.exp_add, hlog_pow]
  unfold modifiedH0
  rw [div_eq_mul_inv, hKT_inv, hsplit_B]
  have hcosh_ne : Real.cosh (π * x / 2) ^ 2 ≠ 0 := by positivity
  rw [show ((1 / Real.cosh (π * x / 2) ^ 2 *
          ((Real.tanh (π * (x - χf) / 2) * Real.tanh (π * (x + χf) / 2) *
              ∏ k ∈ Finset.Icc (f + 1) N,
                blaschkePairQ (xiStar + lambdaComb c' * d.sigmaK c' k)
                  (lambdaComb c' * d.epsHat c' k) x) *
            ((∏ k ∈ Finset.Icc (N + 1) K₀, pairModQ c' d.eta0 x k) *
              Real.exp (∑' m : ℕ, Real.log (pairModQ c' d.eta0 x (K₀ + 1 + m))))) *
          Real.exp (c' * slitL x)) *
        (Real.cosh (π * xiStar / 2) ^ 2 * P₀ ^ (2 * ((f : ℝ) - 1 / 4))))
      = (Real.cosh (π * xiStar / 2) ^ 2 / Real.cosh (π * x / 2) ^ 2) *
          (Real.tanh (π * (x - χf) / 2) * Real.tanh (π * (x + χf) / 2)) *
          (∏ k ∈ Finset.Icc (f + 1) N,
            blaschkePairQ (xiStar + lambdaComb c' * d.sigmaK c' k)
              (lambdaComb c' * d.epsHat c' k) x) *
          (∏ k ∈ Finset.Icc (N + 1) K₀, pairModQ c' d.eta0 x k) *
          (Real.exp (c' * slitL x) *
            Real.exp (∑' m : ℕ, Real.log (pairModQ c' d.eta0 x (K₀ + 1 + m)))) *
          P₀ ^ (2 * ((f : ℝ) - 1 / 4)) by field_simp [hcosh_ne]]
  rw [← hP0_net]
  have hrhs : (Real.cosh (π * xiStar / 2) ^ 2 / Real.cosh (π * x / 2) ^ 2) *
      (P₀⁻¹ * (Real.tanh (π * (x - χf) / 2) * Real.tanh (π * (x + χf) / 2))) *
      (∏ k ∈ Finset.Icc (f + 1) N, P₀ ^ (-2 : ℤ) * blaschkePairQ (xiStar + lambdaComb c' * d.sigmaK c' k)
        (lambdaComb c' * d.epsHat c' k) x) *
      (∏ k ∈ Finset.Icc (N + 1) K₀, P₀ ^ (-2 : ℤ) * pairModQ c' d.eta0 x k) *
      Real.exp (-2 * (∫ a in (1 / 4 : ℝ)..a₀, (phiVar c' x a - Real.log P₀)) +
        c' * (majorantReal x + slitL x)) *
      Real.exp tailRem =
      (Real.cosh (π * xiStar / 2) ^ 2 / Real.cosh (π * x / 2) ^ 2) *
      (P₀⁻¹ * (Real.tanh (π * (x - χf) / 2) * Real.tanh (π * (x + χf) / 2))) *
      ((P₀ ^ (-2 : ℤ)) ^ (N - f) *
        ∏ k ∈ Finset.Icc (f + 1) N, blaschkePairQ (xiStar + lambdaComb c' * d.sigmaK c' k)
          (lambdaComb c' * d.epsHat c' k) x) *
      ((P₀ ^ (-2 : ℤ)) ^ (K₀ - N) * ∏ k ∈ Finset.Icc (N + 1) K₀, pairModQ c' d.eta0 x k) *
      (P₀ ^ (2 * ((K₀ : ℝ) + 1 / 4)) * Real.exp (c' * slitL x) *
        Real.exp (∑' m : ℕ, Real.log (pairModQ c' d.eta0 x (K₀ + 1 + m)))) := by
    rw [hP0_pull1, hP0_pull2, mul_assoc _ _ (Real.exp tailRem), hexp_split]
  rw [hrhs]
  ring

/-! ### Section 4: Finite-Part Window Asymptotics (Step (ii)) -/

private lemma abs_tanh_le_abs (u : ℝ) : |Real.tanh u| ≤ |u| := by
  have hpos : ∀ t : ℝ, 0 ≤ t → Real.tanh t ≤ t := by
    intro t ht
    let f : ℝ → ℝ := fun y => y - Real.tanh y
    have hf : ∀ y : ℝ, HasDerivAt f (1 - (Real.cosh y)⁻¹ ^ 2) y := fun y => by
      have ht_d : HasDerivAt Real.tanh ((Real.cosh y)⁻¹ ^ 2) y := by
        rw [show Real.tanh = fun s => Real.sinh s / Real.cosh s from funext Real.tanh_eq_sinh_div_cosh]
        refine ((Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) (Real.cosh_pos y).ne').congr_deriv ?_
        field_simp [(Real.cosh_pos y).ne']
        linarith [Real.cosh_sq_sub_sinh_sq y]
      exact (hasDerivAt_id y).sub ht_d
    have hm : Monotone f := monotone_of_deriv_nonneg (fun y => (hf y).differentiableAt) fun y => by
      rw [(hf y).deriv]
      have h1 : (Real.cosh y)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_cosh y)
      nlinarith [inv_nonneg.mpr (Real.cosh_pos y).le]
    have h0 := hm ht
    dsimp [f] at h0; simp only [Real.tanh_zero, sub_zero] at h0
    linarith
  rcases le_total 0 u with hu | hu
  · have htnn : 0 ≤ Real.tanh u := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.mpr hu) (Real.cosh_pos u).le
    rw [abs_of_nonneg htnn, abs_of_nonneg hu]; exact hpos u hu
  · have htnp : Real.tanh u ≤ 0 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonpos_of_nonpos_of_nonneg (Real.sinh_nonpos_iff.mpr hu) (Real.cosh_pos u).le
    rw [abs_of_nonpos htnp, abs_of_nonpos hu]
    simpa [Real.tanh_neg] using hpos (-u) (neg_nonneg.mpr hu)

private lemma abs_tanh_sub_self_le (u : ℝ) : |Real.tanh u - u| ≤ |u| ^ 3 := by
  have hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ t - Real.tanh t ∧ t - Real.tanh t ≤ t ^ 3 := by
    intro t ht
    have h1 : 0 ≤ t - Real.tanh t := by
      have := (abs_le.mp (abs_tanh_le_abs t)).2
      rw [abs_of_nonneg ht] at this; linarith
    refine ⟨h1, ?_⟩
    have hf : ∀ y : ℝ, HasDerivAt (fun s => s - Real.tanh s) (1 - (Real.cosh y)⁻¹ ^ 2) y := fun y => by
      have ht_d : HasDerivAt Real.tanh ((Real.cosh y)⁻¹ ^ 2) y := by
        rw [show Real.tanh = fun s => Real.sinh s / Real.cosh s from funext Real.tanh_eq_sinh_div_cosh]
        refine ((Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) (Real.cosh_pos y).ne').congr_deriv ?_
        field_simp [(Real.cosh_pos y).ne']
        linarith [Real.cosh_sq_sub_sinh_sq y]
      exact (hasDerivAt_id y).sub ht_d
    have hderiv_id : ∀ y : ℝ, 1 - (Real.cosh y)⁻¹ ^ 2 = Real.tanh y ^ 2 := fun y => by
      rw [Real.tanh_eq_sinh_div_cosh]; field_simp [(Real.cosh_pos y).ne']
      linarith [Real.cosh_sq_sub_sinh_sq y]
    have hcont : Continuous fun y : ℝ => 1 - (Real.cosh y)⁻¹ ^ 2 := by
      refine continuous_const.sub ((Real.continuous_cosh.inv₀ (fun y => (Real.cosh_pos y).ne')).pow 2)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hf y) (hcont.intervalIntegrable 0 t)
    simp only [Real.tanh_zero, sub_zero] at hftc
    have hint_le : ∫ y in (0 : ℝ)..t, (1 - (Real.cosh y)⁻¹ ^ 2) ≤ ∫ y in (0 : ℝ)..t, y ^ 2 := by
      refine intervalIntegral.integral_mono_on ht (hcont.intervalIntegrable 0 t)
        ((continuous_id.pow 2).intervalIntegrable 0 t) fun y hy => ?_
      rw [hderiv_id y]
      have hty := abs_tanh_le_abs y
      rw [abs_of_nonneg hy.1] at hty
      simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hty 2
    have hpow : ∫ y in (0 : ℝ)..t, y ^ 2 = t ^ 3 / 3 := by rw [integral_pow]; norm_num
    rw [← hftc]
    linarith [hint_le, hpow, pow_nonneg ht 3]
  rcases le_total 0 u with hu | hu
  · obtain ⟨h0, h1⟩ := hnonneg u hu
    rw [abs_sub_comm, abs_of_nonneg h0, abs_of_nonneg hu]; exact h1
  · obtain ⟨h0, h1⟩ := hnonneg (-u) (neg_nonneg.mpr hu)
    have hid : Real.tanh u - u = (-u) - Real.tanh (-u) := by
      rw [Real.tanh_neg]
      ring
    rw [hid, abs_of_nonneg h0]
    exact h1.trans (by rw [abs_of_nonpos hu])

private lemma abs_cosh_sub_one_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.cosh u - 1| ≤ 2 * u ^ 2 := by
  have hu_le : u ≤ 1 / 2 := (abs_le.mp hu).2
  have hu_ge : -(1 / 2) ≤ u := (abs_le.mp hu).1
  have h1 : Real.exp u ≤ 1 + u + 2 * u ^ 2 := by
    have hinv : Real.exp u ≤ (1 - u)⁻¹ := by
      have hneg : 1 - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
      rw [Real.exp_neg] at hneg
      have := inv_anti₀ (by linarith : 0 < 1 - u) hneg
      simpa [inv_inv] using this
    have halg : (1 - u)⁻¹ ≤ 1 + u + 2 * u ^ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg u]
    linarith
  have h2 : Real.exp (-u) ≤ 1 - u + 2 * u ^ 2 := by
    have hinv : Real.exp (-u) ≤ (1 + u)⁻¹ := by
      have hpos : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
      have := inv_anti₀ (by linarith : 0 < 1 + u) hpos
      simpa [Real.exp_neg] using this
    have halg : (1 + u)⁻¹ ≤ 1 - u + 2 * u ^ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg u]
    linarith
  have hc_ge : 1 ≤ Real.cosh u := Real.one_le_cosh u
  have hc_le : Real.cosh u ≤ 1 + 2 * u ^ 2 := by rw [Real.cosh_eq]; linarith
  rw [abs_of_nonneg (sub_nonneg.mpr hc_ge)]
  linarith

private lemma abs_sinh_sub_self_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.sinh u - u| ≤ 2 * |u| ^ 3 := by
  have hnonneg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 → 0 ≤ Real.sinh t - t ∧ Real.sinh t - t ≤ 2 * t ^ 3 := by
    intro t ht0 ht1
    have hftc : Real.sinh t - t = ∫ y in (0 : ℝ)..t, (Real.cosh y - 1) := by
      have hd : ∀ y : ℝ, HasDerivAt (fun s => Real.sinh s - s) (Real.cosh y - 1) y :=
        fun y => (Real.hasDerivAt_sinh y).sub (hasDerivAt_id y)
      have hc : Continuous fun y : ℝ => Real.cosh y - 1 := Real.continuous_cosh.sub continuous_const
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y) (hc.intervalIntegrable 0 t)
      simp only [Real.sinh_zero, sub_zero] at h
      exact h.symm
    rw [hftc]
    refine ⟨intervalIntegral.integral_nonneg ht0 (fun y _ => sub_nonneg.mpr (Real.one_le_cosh y)), ?_⟩
    have hc : Continuous fun y : ℝ => Real.cosh y - 1 := Real.continuous_cosh.sub continuous_const
    have hint_le : ∫ y in (0 : ℝ)..t, (Real.cosh y - 1) ≤ ∫ y in (0 : ℝ)..t, 2 * y ^ 2 := by
      refine intervalIntegral.integral_mono_on ht0 (hc.intervalIntegrable 0 t)
        ((continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 t) fun y hy => ?_
      have hy_abs : |y| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have := (abs_le.mp (abs_cosh_sub_one_le hy_abs)).2
      linarith
    have hpow : ∫ y in (0 : ℝ)..t, 2 * y ^ 2 = 2 / 3 * t ^ 3 := by
      rw [intervalIntegral.integral_const_mul, integral_pow]; norm_num; ring
    linarith [hint_le, hpow, pow_nonneg ht0 3]
  rcases le_total 0 u with hu0 | hu0
  · obtain ⟨h0, h1⟩ := hnonneg u hu0 ((abs_of_nonneg hu0).symm ▸ hu)
    rw [abs_of_nonneg h0, abs_of_nonneg hu0]; exact h1
  · obtain ⟨h0, h1⟩ := hnonneg (-u) (neg_nonneg.mpr hu0) ((abs_of_nonpos hu0).symm ▸ hu)
    rw [show Real.sinh u - u = -(Real.sinh (-u) - (-u)) by rw [Real.sinh_neg]; ring,
      abs_neg, abs_of_nonneg h0, abs_of_nonpos hu0]
    exact h1

private lemma abs_sin_sub_self_le {v : ℝ} (hv : 0 ≤ v) : |Real.sin v - v| ≤ v ^ 3 := by
  have h1 : 0 ≤ v - Real.sin v := sub_nonneg.mpr (Real.sin_le hv)
  have hd : ∀ y : ℝ, HasDerivAt (fun s => s - Real.sin s) (1 - Real.cos y) y :=
    fun y => (hasDerivAt_id y).sub (Real.hasDerivAt_sin y)
  have hc : Continuous fun y : ℝ => 1 - Real.cos y := continuous_const.sub Real.continuous_cos
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y) (hc.intervalIntegrable 0 v)
  simp only [Real.sin_zero, sub_zero] at hftc
  have hcos : ∀ y : ℝ, 0 ≤ y → 1 - Real.cos y ≤ y ^ 2 := fun y hy => by
    have hhd : ∀ t : ℝ, HasDerivAt (fun s => 1 - Real.cos s) (Real.sin t) t := fun t => by
      simpa using ((Real.hasDerivAt_cos t).const_sub (1 : ℝ))
    have hfc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hhd t)
      (Real.continuous_sin.intervalIntegrable 0 y)
    simp only [Real.cos_zero, sub_self] at hfc
    have hm : ∫ t in (0 : ℝ)..y, Real.sin t ≤ ∫ t in (0 : ℝ)..y, t :=
      intervalIntegral.integral_mono_on hy (Real.continuous_sin.intervalIntegrable 0 y)
        (continuous_id.intervalIntegrable 0 y) fun t ht => Real.sin_le ht.1
    have hp : ∫ t in (0 : ℝ)..y, t = y ^ 2 / 2 := by rw [integral_id]; ring
    linarith [hfc, hm, hp, sq_nonneg y]
  have hint_le : ∫ y in (0 : ℝ)..v, (1 - Real.cos y) ≤ ∫ y in (0 : ℝ)..v, y ^ 2 :=
    intervalIntegral.integral_mono_on hv (hc.intervalIntegrable 0 v)
      ((continuous_id.pow 2).intervalIntegrable 0 v) fun y hy => hcos y hy.1
  have hp : ∫ y in (0 : ℝ)..v, y ^ 2 = v ^ 3 / 3 := by rw [integral_pow]; norm_num
  rw [abs_sub_comm, abs_of_nonneg h1]
  linarith [hftc, hint_le, hp, pow_nonneg hv 3]

private lemma continuous_tanh_real : Continuous Real.tanh := by
  have heq : Real.tanh = fun t : ℝ => Real.sinh t / Real.cosh t := funext Real.tanh_eq_sinh_div_cosh
  rw [heq]
  exact Real.continuous_sinh.div Real.continuous_cosh (fun t => (Real.cosh_pos t).ne')

private lemma blaschkeT_window_factor_bound {M₀ : ℝ} (hM₀ : 0 ≤ M₀) :
    ∀ ε > 0, ∃ C₀ > 0, ∀ {c' σ s sLim : ℝ}, C₀ ≤ c' →
      |σ| ≤ M₀ → |s| ≤ M₀ → |s - sLim| ≤ ε / (4 * (1 + M₀)) →
      |(π * lambdaComb c' / (2 * Real.sqrt 2))⁻¹ *
          (Real.tanh (π * ((xiStar + lambdaComb c' * σ) - (xiStar + lambdaComb c' * s)) / 2) *
            Real.tanh (π * ((xiStar + lambdaComb c' * σ) + (xiStar + lambdaComb c' * s)) / 2)) -
        (σ - sLim)| ≤ ε := by
  intro ε hε
  have hcont_tanh : ContinuousAt (fun t : ℝ => Real.sqrt 2 * Real.tanh t) (π * xiStar) :=
    continuousAt_const.mul continuous_tanh_real.continuousAt
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.continuousAt_iff.mp hcont_tanh
    (min 1 (ε / (8 * (M₀ + 1)))) (by positivity)
  have ht_lim : Tendsto (fun c' : ℝ => lambdaComb c') atTop (𝓝 0) := tendsto_lambdaComb_atTop
  have h_small : ∀ᶠ c' : ℝ in atTop,
      0 < c' ∧ π * lambdaComb c' * M₀ < δ₁ ∧
        (π * lambdaComb c' * M₀) ^ 2 * (2 * M₀) * 2 ≤ ε / 4 := by
    have h1 : ∀ᶠ c' : ℝ in atTop, (0 : ℝ) < c' := eventually_gt_atTop (0 : ℝ)
    have h2 : ∀ᶠ c' in atTop, π * lambdaComb c' * M₀ < δ₁ := by
      have ht := (ht_lim.const_mul π).mul_const M₀
      rw [mul_zero, zero_mul] at ht
      exact ht.eventually_lt_const hδ₁_pos
    have h3 : ∀ᶠ c' in atTop, (π * lambdaComb c' * M₀) ^ 2 * (2 * M₀) * 2 ≤ ε / 4 := by
      have ht : Tendsto (fun c' : ℝ => (π * lambdaComb c' * M₀) ^ 2 * (2 * M₀) * 2) atTop (𝓝 0) := by
        simpa using ((((ht_lim.const_mul π).mul_const M₀).pow 2).mul_const (2 * M₀)).mul_const 2
      exact ht.eventually_le_const (by linarith)
    filter_upwards [h1, h2, h3] with c' hc1 hc2 hc3
    exact ⟨hc1, hc2, hc3⟩
  obtain ⟨C₀, hC₀⟩ := eventually_atTop.mp h_small
  refine ⟨max C₀ 1, by positivity, fun {c' σ s sLim} hc' hσ hs hs_lim => ?_⟩
  obtain ⟨hc'_pos, hlam_δ, hlam_sq⟩ := hC₀ c' ((le_max_left _ _).trans hc')
  set lam := lambdaComb c'
  have hlam_pos : 0 < lam := lambdaComb_pos hc'_pos
  set z₁ := π * ((xiStar + lam * σ) - (xiStar + lam * s)) / 2
  set z₂ := π * ((xiStar + lam * σ) + (xiStar + lam * s)) / 2
  have hz₁_eq : z₁ = (π * lam / 2) * (σ - s) := by dsimp [z₁]; ring
  have hz₂_eq : z₂ = π * xiStar + (π * lam / 2) * (σ + s) := by dsimp [z₂]; ring
  have hz₂_dist : dist z₂ (π * xiStar) < δ₁ := by
    rw [Real.dist_eq, hz₂_eq, add_sub_cancel_left, abs_mul, abs_of_pos (by positivity : 0 < π * lam / 2)]
    have hss : |σ + s| ≤ 2 * M₀ := (abs_add_le σ s).trans (by linarith)
    calc (π * lam / 2) * |σ + s| ≤ (π * lam / 2) * (2 * M₀) := by gcongr
      _ = π * lam * M₀ := by ring
      _ < δ₁ := hlam_δ
  have hδ₁_val := hδ₁ hz₂_dist
  rw [Real.dist_eq, show Real.sqrt 2 * Real.tanh (π * xiStar) = 1 by
    rw [tanh_pi_mul_xiStar]; field_simp [(Real.sqrt_pos.mpr two_pos).ne']] at hδ₁_val
  have hT2_err : |Real.sqrt 2 * Real.tanh z₂ - 1| ≤ min 1 (ε / (8 * (M₀ + 1))) := hδ₁_val.le
  have hT2_bd : |Real.sqrt 2 * Real.tanh z₂| ≤ 2 := by
    have h1 := hT2_err.trans (min_le_left _ _)
    have := abs_sub_abs_le_abs_sub (Real.sqrt 2 * Real.tanh z₂) 1
    rw [abs_one] at this; linarith
  have h1_step : |(π * lam / 2)⁻¹ * Real.tanh z₁ - (σ - s)| ≤ (π * lam * M₀) ^ 2 * (2 * M₀) := by
    have ht1 := abs_tanh_sub_self_le z₁
    have hσs : |σ - s| ≤ 2 * M₀ := (abs_sub σ s).trans (by linarith)
    have hz₁_bd : |z₁| ≤ π * lam * M₀ := by
      rw [hz₁_eq, abs_mul, abs_of_pos (by positivity : 0 < π * lam / 2)]
      calc (π * lam / 2) * |σ - s| ≤ (π * lam / 2) * (2 * M₀) := by gcongr
        _ = π * lam * M₀ := by ring
    have hdiv : |(π * lam / 2)⁻¹ * (Real.tanh z₁ - z₁)| ≤ (π * lam * M₀) ^ 2 * (2 * M₀) := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr (by positivity : 0 < π * lam / 2))]
      calc (π * lam / 2)⁻¹ * |Real.tanh z₁ - z₁| ≤ (π * lam / 2)⁻¹ * |z₁| ^ 3 := by gcongr
        _ = (π * lam / 2)⁻¹ * (|z₁| ^ 2 * |z₁|) := by ring
        _ ≤ (π * lam / 2)⁻¹ * ((π * lam * M₀) ^ 2 * ((π * lam / 2) * |σ - s|)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hz₁_bd 2) ?_ (abs_nonneg _) (by positivity)
            rw [hz₁_eq, abs_mul, abs_of_pos (by positivity : 0 < π * lam / 2)]
        _ = (π * lam * M₀) ^ 2 * |σ - s| := by field_simp [Real.pi_ne_zero, hlam_pos.ne']
        _ ≤ (π * lam * M₀) ^ 2 * (2 * M₀) := mul_le_mul_of_nonneg_left hσs (by positivity)
    rwa [show (π * lam / 2)⁻¹ * Real.tanh z₁ - (σ - s) = (π * lam / 2)⁻¹ * (Real.tanh z₁ - z₁) by
      rw [hz₁_eq]; field_simp [Real.pi_ne_zero, hlam_pos.ne']]
  have hmul_eq : (π * lam / (2 * Real.sqrt 2))⁻¹ * (Real.tanh z₁ * Real.tanh z₂) =
      ((π * lam / 2)⁻¹ * Real.tanh z₁) * (Real.sqrt 2 * Real.tanh z₂) := by
    field_simp [Real.pi_ne_zero, hlam_pos.ne', (Real.sqrt_pos.mpr two_pos).ne']
  rw [hmul_eq]
  have hid : ((π * lam / 2)⁻¹ * Real.tanh z₁) * (Real.sqrt 2 * Real.tanh z₂) - (σ - sLim) =
      ((π * lam / 2)⁻¹ * Real.tanh z₁ - (σ - s)) * (Real.sqrt 2 * Real.tanh z₂) +
      (σ - s) * (Real.sqrt 2 * Real.tanh z₂ - 1) - (s - sLim) := by ring
  rw [hid]
  have hp1 : |((π * lam / 2)⁻¹ * Real.tanh z₁ - (σ - s)) * (Real.sqrt 2 * Real.tanh z₂)| ≤ ε / 4 := by
    rw [abs_mul]
    calc _ ≤ ((π * lam * M₀) ^ 2 * (2 * M₀)) * 2 :=
          mul_le_mul h1_step hT2_bd (abs_nonneg _) (by positivity)
      _ ≤ ε / 4 := hlam_sq
  have hp2 : |(σ - s) * (Real.sqrt 2 * Real.tanh z₂ - 1)| ≤ ε / 4 := by
    rw [abs_mul]
    have hσs : |σ - s| ≤ 2 * M₀ := (abs_sub σ s).trans (by linarith)
    have ht2 := hT2_err.trans (min_le_right _ _)
    calc |σ - s| * |Real.sqrt 2 * Real.tanh z₂ - 1|
        ≤ (2 * M₀) * (ε / (8 * (M₀ + 1))) := mul_le_mul hσs ht2 (abs_nonneg _) (by positivity)
      _ ≤ ε / 4 := by
          have : 2 * M₀ ≤ 2 * (M₀ + 1) := by linarith
          calc (2 * M₀) * (ε / (8 * (M₀ + 1))) ≤ (2 * (M₀ + 1)) * (ε / (8 * (M₀ + 1))) := by gcongr
            _ = ε / 4 := by field_simp [(by positivity : M₀ + 1 ≠ 0)]; ring
  have hp3 : |s - sLim| ≤ ε / 4 := by
    refine hs_lim.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [hε, hM₀]
  calc |((π * lam / 2)⁻¹ * Real.tanh z₁ - (σ - s)) * (Real.sqrt 2 * Real.tanh z₂) +
        (σ - s) * (Real.sqrt 2 * Real.tanh z₂ - 1) - (s - sLim)|
      ≤ |((π * lam / 2)⁻¹ * Real.tanh z₁ - (σ - s)) * (Real.sqrt 2 * Real.tanh z₂) +
          (σ - s) * (Real.sqrt 2 * Real.tanh z₂ - 1)| + |s - sLim| := abs_sub _ _
    _ ≤ (|((π * lam / 2)⁻¹ * Real.tanh z₁ - (σ - s)) * (Real.sqrt 2 * Real.tanh z₂)| +
          |(σ - s) * (Real.sqrt 2 * Real.tanh z₂ - 1)|) + |s - sLim| :=
        add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (ε / 4 + ε / 4) + ε / 4 := add_le_add (add_le_add hp1 hp2) hp3
    _ ≤ ε := by linarith

private lemma blaschkePairQ_inner_factor_bound {α M₀ R σ s e : ℝ}
    (hα_pos : 0 < α) (hR_nn : 0 ≤ R) (_hM₀ : 0 ≤ M₀)
    (hσ : |σ| ≤ M₀) (hs : |s| ≤ M₀) (he0 : 0 ≤ e) (heM : e ≤ M₀)
    (hR_half : R ≤ 1 / 2)
    (hu1_bd : |α * (σ - s)| ≤ R) (hv1_bd : α * e ≤ R) :
    |α ^ (-2 : ℤ) * ((Real.sinh (α * (σ - s)) ^ 2 + Real.sin (α * e) ^ 2) /
        (Real.cosh (α * (σ - s)) ^ 2 - Real.sin (α * e) ^ 2)) - ((σ - s) ^ 2 + e ^ 2)| ≤
      64 * R ^ 2 * (5 * M₀ ^ 2 + 1) := by
  set u1 := α * (σ - s)
  set v1 := α * e
  have hv1_nn : 0 ≤ v1 := mul_nonneg hα_pos.le he0
  have hu1_half : |u1| ≤ 1 / 2 := hu1_bd.trans hR_half
  have hv1_half : v1 ≤ 1 / 2 := hv1_bd.trans hR_half
  have hden1_ge : 1 / 2 ≤ Real.cosh u1 ^ 2 - Real.sin v1 ^ 2 := by
    have hch : 1 ≤ Real.cosh u1 ^ 2 := by nlinarith [Real.one_le_cosh u1]
    have hsn : Real.sin v1 ^ 2 ≤ v1 ^ 2 := by
      have : |Real.sin v1| ≤ v1 := by simpa [abs_of_nonneg hv1_nn] using Real.abs_sin_le_abs (x := v1)
      simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) this 2
    have hv1_sq : v1 ^ 2 ≤ 1 / 4 := by nlinarith
    linarith
  have hsh_dif : |Real.sinh u1 ^ 2 - u1 ^ 2| ≤ 12 * u1 ^ 4 := by
    have h1 := abs_sinh_sub_self_le hu1_half
    have hsum : |Real.sinh u1 + u1| ≤ 3 * |u1| := by
      have hsh_bd : |Real.sinh u1| ≤ 2 * |u1| := by
        have htri := abs_sub_abs_le_abs_sub (Real.sinh u1) u1
        have hle1 : |u1| ≤ 1 / 2 := hu1_half
        have hsq : |u1| ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg u1, hle1]
        have hcu : 2 * |u1| ^ 3 ≤ |u1| := by nlinarith [abs_nonneg u1, hsq]
        linarith [htri, h1, hcu]
      exact (abs_add_le _ _).trans (by linarith)
    rw [show Real.sinh u1 ^ 2 - u1 ^ 2 = (Real.sinh u1 - u1) * (Real.sinh u1 + u1) by ring, abs_mul]
    calc |Real.sinh u1 - u1| * |Real.sinh u1 + u1| ≤ (2 * |u1| ^ 3) * (3 * |u1|) :=
          mul_le_mul h1 hsum (abs_nonneg _) (by positivity)
      _ = 6 * |u1| ^ 4 := by ring
      _ ≤ 12 * u1 ^ 4 := by
          have h4_eq : u1 ^ 4 = |u1| ^ 4 := by
            calc u1 ^ 4 = (u1 ^ 2) ^ 2 := by ring
              _ = (|u1| ^ 2) ^ 2 := by rw [sq_abs]
              _ = |u1| ^ 4 := by ring
          rw [h4_eq]; linarith [pow_nonneg (abs_nonneg u1) 4]
  have hsn_dif : |Real.sin v1 ^ 2 - v1 ^ 2| ≤ 2 * v1 ^ 4 := by
    have h1 := abs_sin_sub_self_le hv1_nn
    have hsum : |Real.sin v1 + v1| ≤ 2 * v1 := by
      have : |Real.sin v1| ≤ v1 := by simpa [abs_of_nonneg hv1_nn] using Real.abs_sin_le_abs (x := v1)
      exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hv1_nn]; linarith)
    rw [show Real.sin v1 ^ 2 - v1 ^ 2 = (Real.sin v1 - v1) * (Real.sin v1 + v1) by ring, abs_mul]
    calc |Real.sin v1 - v1| * |Real.sin v1 + v1| ≤ v1 ^ 3 * (2 * v1) :=
          mul_le_mul h1 hsum (abs_nonneg _) (by positivity)
      _ = 2 * v1 ^ 4 := by ring
  have hden_dif : |(Real.cosh u1 ^ 2 - Real.sin v1 ^ 2) - 1| ≤ 12 * u1 ^ 2 + v1 ^ 2 := by
    have hch := abs_cosh_sub_one_le hu1_half
    have hch_sum : Real.cosh u1 + 1 ≤ 3 := by
      have := (abs_le.mp hch).2
      have hu2 : u1 ^ 2 ≤ 1 / 4 := by
        calc u1 ^ 2 = |u1| ^ 2 := (sq_abs u1).symm
          _ ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hu1_half 2
          _ = 1 / 4 := by norm_num
      linarith
    have hch_sq : |Real.cosh u1 ^ 2 - 1| ≤ 6 * u1 ^ 2 := by
      rw [show Real.cosh u1 ^ 2 - 1 = (Real.cosh u1 - 1) * (Real.cosh u1 + 1) by ring,
        abs_mul, abs_of_pos (by linarith [Real.one_le_cosh u1] : 0 < Real.cosh u1 + 1)]
      exact (mul_le_mul hch hch_sum (by positivity) (by positivity)).trans_eq (by ring)
    have hsn_sq : Real.sin v1 ^ 2 ≤ v1 ^ 2 := by
      have : |Real.sin v1| ≤ v1 := by simpa [abs_of_nonneg hv1_nn] using Real.abs_sin_le_abs (x := v1)
      simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) this 2
    have h1 := abs_sub (Real.cosh u1 ^ 2 - 1) (Real.sin v1 ^ 2)
    rw [abs_of_nonneg (sq_nonneg (Real.sin v1))] at h1
    have h_eq : Real.cosh u1 ^ 2 - Real.sin v1 ^ 2 - 1 = (Real.cosh u1 ^ 2 - 1) - Real.sin v1 ^ 2 := by ring
    rw [h_eq]
    linarith [sq_nonneg u1, sq_nonneg (Real.sin v1)]
  set A := Real.sinh u1 ^ 2 + Real.sin v1 ^ 2
  set D := Real.cosh u1 ^ 2 - Real.sin v1 ^ 2
  set B := u1 ^ 2 + v1 ^ 2
  have hB_eq : α ^ (-2 : ℤ) * B = (σ - s) ^ 2 + e ^ 2 := by
    dsimp [B, u1, v1]; rw [zpow_neg, zpow_two]; field_simp [hα_pos.ne']
  have hid_AD : α ^ (-2 : ℤ) * (A / D) - ((σ - s) ^ 2 + e ^ 2) =
      (α ^ (-2 : ℤ) * (A - B) + ((σ - s) ^ 2 + e ^ 2) * (1 - D)) / D := by
    rw [← hB_eq]
    have hD_ne : D ≠ 0 := by linarith
    field_simp [hD_ne, hα_pos.ne']
    dsimp [A, B]; ring
  have h_res_eq : α ^ (-2 : ℤ) * ((Real.sinh (α * (σ - s)) ^ 2 + Real.sin (α * e) ^ 2) /
      (Real.cosh (α * (σ - s)) ^ 2 - Real.sin (α * e) ^ 2)) - ((σ - s) ^ 2 + e ^ 2) =
      (α ^ (-2 : ℤ) * (A - B) + ((σ - s) ^ 2 + e ^ 2) * (1 - D)) / D := hid_AD
  rw [h_res_eq, abs_div, abs_of_pos (by linarith : 0 < D)]
  have hnum_bd : |α ^ (-2 : ℤ) * (A - B) + ((σ - s) ^ 2 + e ^ 2) * (1 - D)| ≤
      32 * R ^ 2 * (5 * M₀ ^ 2 + 1) := by
    have hAB : |α ^ (-2 : ℤ) * (A - B)| ≤ 14 * R ^ 2 * ((σ - s) ^ 2 + e ^ 2) := by
      have h1 : |A - B| ≤ 12 * u1 ^ 4 + 2 * v1 ^ 4 := by
        rw [show A - B = (Real.sinh u1 ^ 2 - u1 ^ 2) + (Real.sin v1 ^ 2 - v1 ^ 2) by dsimp [A, B]; ring]
        exact (abs_add_le _ _).trans (add_le_add hsh_dif hsn_dif)
      have h2 : 12 * u1 ^ 4 + 2 * v1 ^ 4 ≤ 14 * R ^ 2 * (u1 ^ 2 + v1 ^ 2) := by
        have hu_le : u1 ^ 2 ≤ R ^ 2 := by simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hu1_bd 2
        have hv_le : v1 ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hv1_nn hv1_bd 2
        nlinarith only [sq_nonneg u1, sq_nonneg v1, hu_le, hv_le]
      rw [abs_mul, abs_of_pos (by positivity : 0 < α ^ (-2 : ℤ))]
      calc α ^ (-2 : ℤ) * |A - B| ≤ α ^ (-2 : ℤ) * (14 * R ^ 2 * (u1 ^ 2 + v1 ^ 2)) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
        _ = 14 * R ^ 2 * (α ^ (-2 : ℤ) * B) := by dsimp [B]; ring
        _ = 14 * R ^ 2 * ((σ - s) ^ 2 + e ^ 2) := by rw [hB_eq]
    have hBD : |((σ - s) ^ 2 + e ^ 2) * (1 - D)| ≤ 13 * R ^ 2 * ((σ - s) ^ 2 + e ^ 2) := by
      have h1D : |1 - D| ≤ 13 * R ^ 2 := by
        rw [abs_sub_comm]
        have hu_le : u1 ^ 2 ≤ R ^ 2 := by simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hu1_bd 2
        have hv_le : v1 ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hv1_nn hv1_bd 2
        linarith [hden_dif]
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (σ - s) ^ 2 + e ^ 2)]
      calc ((σ - s) ^ 2 + e ^ 2) * |1 - D| ≤ ((σ - s) ^ 2 + e ^ 2) * (13 * R ^ 2) :=
            mul_le_mul_of_nonneg_left h1D (by positivity)
        _ = 13 * R ^ 2 * ((σ - s) ^ 2 + e ^ 2) := by ring
    have hse_bd : (σ - s) ^ 2 + e ^ 2 ≤ 5 * M₀ ^ 2 + 1 := by
      have hσs : (σ - s) ^ 2 ≤ (2 * M₀) ^ 2 := by
        have : |σ - s| ≤ 2 * M₀ := (abs_sub σ s).trans (by linarith)
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) this 2
      have he_sq : e ^ 2 ≤ M₀ ^ 2 := pow_le_pow_left₀ he0 heM 2
      nlinarith only [hσs, he_sq]
    calc _ ≤ |α ^ (-2 : ℤ) * (A - B)| + |((σ - s) ^ 2 + e ^ 2) * (1 - D)| := abs_add_le _ _
      _ ≤ 14 * R ^ 2 * ((σ - s) ^ 2 + e ^ 2) + 13 * R ^ 2 * ((σ - s) ^ 2 + e ^ 2) := add_le_add hAB hBD
      _ = 27 * R ^ 2 * ((σ - s) ^ 2 + e ^ 2) := by ring
      _ ≤ 27 * R ^ 2 * (5 * M₀ ^ 2 + 1) := by gcongr
      _ ≤ 32 * R ^ 2 * (5 * M₀ ^ 2 + 1) := by
          have : 0 ≤ R ^ 2 * (5 * M₀ ^ 2 + 1) := by positivity
          linarith
  calc |α ^ (-2 : ℤ) * (A - B) + ((σ - s) ^ 2 + e ^ 2) * (1 - D)| / D
      ≤ (32 * R ^ 2 * (5 * M₀ ^ 2 + 1)) / D := div_le_div_of_nonneg_right hnum_bd (by linarith)
    _ ≤ (32 * R ^ 2 * (5 * M₀ ^ 2 + 1)) / (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hden1_ge
    _ = 64 * R ^ 2 * (5 * M₀ ^ 2 + 1) := by ring

private noncomputable def pairRatioG2 (u v : ℝ) : ℝ :=
  (Real.sinh u ^ 2 + Real.sin v ^ 2) / (Real.cosh u ^ 2 - Real.sin v ^ 2)

private lemma blaschkePairQ_window_factor_bound {M₀ : ℝ} (hM₀ : 0 ≤ M₀) :
    ∀ ε > 0, ∃ C₀ > 0, ∀ {c' σ s sLim e eLim : ℝ}, C₀ ≤ c' →
      |σ| ≤ M₀ → |s| ≤ M₀ → 0 ≤ e → e ≤ M₀ →
      |s - sLim| ≤ min 1 (ε / (18 * (M₀ + 1) + 6)) →
      |e - eLim| ≤ min 1 (ε / (18 * (M₀ + 1) + 6)) →
      |(π * lambdaComb c' / (2 * Real.sqrt 2)) ^ (-2 : ℤ) *
          blaschkePairQ (xiStar + lambdaComb c' * s) (lambdaComb c' * e) (xiStar + lambdaComb c' * σ) -
        ((σ - sLim) ^ 2 + eLim ^ 2)| ≤ ε := by
  intro ε hε
  have hden_pos : Real.cosh (π * xiStar) ^ 2 - Real.sin 0 ^ 2 ≠ 0 := by
    simp [(Real.cosh_pos _).ne']
  have hcont_g2 : ContinuousAt (fun p : ℝ × ℝ => pairRatioG2 p.1 p.2) (π * xiStar, 0) := by
    unfold pairRatioG2
    have hnum : ContinuousAt (fun p : ℝ × ℝ => Real.sinh p.1 ^ 2 + Real.sin p.2 ^ 2) (π * xiStar, 0) :=
      ((Real.continuous_sinh.comp continuous_fst).pow 2).add
        ((Real.continuous_sin.comp continuous_snd).pow 2) |>.continuousAt
    have hden : ContinuousAt (fun p : ℝ × ℝ => Real.cosh p.1 ^ 2 - Real.sin p.2 ^ 2) (π * xiStar, 0) :=
      ((Real.continuous_cosh.comp continuous_fst).pow 2).sub
        ((Real.continuous_sin.comp continuous_snd).pow 2) |>.continuousAt
    exact hnum.div hden hden_pos
  have hg2_val : 2 * pairRatioG2 (π * xiStar) 0 = 1 := by
    unfold pairRatioG2
    simp only [Real.sin_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      sub_zero]
    rw [← div_pow, ← Real.tanh_eq_sinh_div_cosh, tanh_pi_mul_xiStar]
    norm_num
  have hcont_2g : ContinuousAt (fun p : ℝ × ℝ => 2 * pairRatioG2 p.1 p.2) (π * xiStar, 0) :=
    continuousAt_const.mul hcont_g2
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.continuousAt_iff.mp hcont_2g
    (min 1 (ε / (16 * (M₀ + 1) ^ 2 + 1))) (by positivity)
  have h_small : ∀ᶠ c' : ℝ in atTop,
      0 < c' ∧ π * lambdaComb c' * (2 * M₀ + 1) < min (1 / 2) δ₂ ∧
        (128 : ℝ) * (π * lambdaComb c' * (2 * M₀ + 1)) ^ 2 * (5 * M₀ ^ 2 + 1) ≤ ε / 4 := by
    have ht := tendsto_lambdaComb_atTop
    have h1 : ∀ᶠ c' : ℝ in atTop, (0 : ℝ) < c' := eventually_gt_atTop (0 : ℝ)
    have h2 : ∀ᶠ c' in atTop, π * lambdaComb c' * (2 * M₀ + 1) < min (1 / 2) δ₂ := by
      have ht' : Tendsto (fun c' : ℝ => π * lambdaComb c' * (2 * M₀ + 1)) atTop (𝓝 0) := by
        simpa using (ht.const_mul π).mul_const (2 * M₀ + 1)
      exact ht'.eventually_lt_const (lt_min (by norm_num) hδ₂_pos)
    have h3 : ∀ᶠ c' in atTop,
        (128 : ℝ) * (π * lambdaComb c' * (2 * M₀ + 1)) ^ 2 * (5 * M₀ ^ 2 + 1) ≤ ε / 4 := by
      have ht' : Tendsto (fun c' : ℝ =>
          (128 : ℝ) * (π * lambdaComb c' * (2 * M₀ + 1)) ^ 2 * (5 * M₀ ^ 2 + 1)) atTop (𝓝 0) := by
        simpa using ((((ht.const_mul π).mul_const (2 * M₀ + 1)).pow 2).const_mul 128).mul_const (5 * M₀ ^ 2 + 1)
      exact ht'.eventually_le_const (by linarith)
    filter_upwards [h1, h2, h3] with c' hc1 hc2 hc3
    exact ⟨hc1, hc2, hc3⟩
  obtain ⟨C₀, hC₀⟩ := eventually_atTop.mp h_small
  refine ⟨max C₀ 1, by positivity, fun {c' σ s sLim e eLim} hc' hσ hs he0 heM hs_lim he_lim => ?_⟩
  obtain ⟨hc'_pos, hlam_lt, hlam_err⟩ := hC₀ c' ((le_max_left _ _).trans hc')
  set lam := lambdaComb c'
  have hlam_pos : 0 < lam := lambdaComb_pos hc'_pos
  set α := π * lam / 2
  have hα_pos : 0 < α := by dsimp [α]; positivity
  set u1 := α * (σ - s)
  set v1 := α * e
  set u2 := π * xiStar + α * (σ + s)
  have hpair_eq : blaschkePairQ (xiStar + lam * s) (lam * e) (xiStar + lam * σ) =
      pairRatioG2 u1 v1 * pairRatioG2 u2 v1 := by
    rw [blaschkePairQ_eq]
    unfold pairRatioG2
    dsimp [u1, v1, u2, α]
    have ha1 : π * (xiStar + lam * σ - (xiStar + lam * s)) / 2 = π * lam / 2 * (σ - s) := by ring
    have ha2 : π * (xiStar + lam * σ + (xiStar + lam * s)) / 2 = π * xiStar + π * lam / 2 * (σ + s) := by ring
    have ha3 : π * (lam * e) / 2 = π * lam / 2 * e := by ring
    rw [ha1, ha2, ha3]
  have hu1_bd : |u1| ≤ π * lam * (2 * M₀ + 1) := by
    rw [abs_mul, abs_of_pos hα_pos]
    have h1 : |σ - s| ≤ 2 * M₀ + 1 := (abs_sub σ s).trans (by linarith)
    calc α * |σ - s| ≤ α * (2 * M₀ + 1) := by gcongr
      _ ≤ π * lam * (2 * M₀ + 1) := by
          dsimp [α]
          have hnn : 0 ≤ π * lam * (2 * M₀ + 1) := by positivity
          linarith
  have hv1_nn : 0 ≤ v1 := mul_nonneg hα_pos.le he0
  have hv1_bd : v1 ≤ π * lam * (2 * M₀ + 1) := by
    dsimp [v1, α]
    have he' : e ≤ 2 * M₀ + 1 := by linarith
    calc (π * lam / 2) * e ≤ (π * lam / 2) * (2 * M₀ + 1) :=
          mul_le_mul_of_nonneg_left he' (by positivity)
      _ ≤ π * lam * (2 * M₀ + 1) := by
          have hnn : 0 ≤ π * lam * (2 * M₀ + 1) := by positivity
          linarith
  have hg1_err : |α ^ (-2 : ℤ) * pairRatioG2 u1 v1 - ((σ - s) ^ 2 + e ^ 2)| ≤ ε / 8 := by
    have hinner := blaschkePairQ_inner_factor_bound hα_pos (by positivity : 0 ≤ π * lam * (2 * M₀ + 1)) hM₀
      hσ hs he0 heM (hlam_lt.le.trans (min_le_left _ _)) hu1_bd hv1_bd
    exact hinner.trans (by linarith [hlam_err])
  have hp_dist : dist (u2, v1) (π * xiStar, 0) < δ₂ := by
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    refine ⟨?_, ?_⟩
    · rw [show u2 - π * xiStar = α * (σ + s) by dsimp [u2]; ring, abs_mul, abs_of_pos hα_pos]
      have hss : |σ + s| ≤ 2 * M₀ + 1 := (abs_add_le σ s).trans (by linarith)
      have h1 : α * |σ + s| ≤ π * lam * (2 * M₀ + 1) := by
        dsimp [α]; nlinarith only [mul_pos Real.pi_pos hlam_pos, hss, abs_nonneg (σ + s)]
      exact h1.trans_lt (hlam_lt.trans_le (min_le_right _ _))
    · rw [sub_zero, abs_of_nonneg hv1_nn]
      exact hv1_bd.trans_lt (hlam_lt.trans_le (min_le_right _ _))
  have hg2_err : |2 * pairRatioG2 u2 v1 - 1| ≤ min 1 (ε / (16 * (M₀ + 1) ^ 2 + 1)) := by
    have h := (hδ₂ hp_dist).le
    rwa [Real.dist_eq, hg2_val] at h
  have hg2_bd : |2 * pairRatioG2 u2 v1| ≤ 2 := by
    have := abs_sub_abs_le_abs_sub (2 * pairRatioG2 u2 v1) 1
    rw [abs_one] at this
    linarith [hg2_err.trans (min_le_left _ _)]
  have hpow_split : (π * lam / (2 * Real.sqrt 2)) ^ (-2 : ℤ) = 2 * α ^ (-2 : ℤ) := by
    dsimp [α]
    rw [zpow_neg, zpow_neg, zpow_two, zpow_two]
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp [Real.pi_ne_zero, hlam_pos.ne']
    nlinarith only [hs2]
  have hmul_eq : (π * lam / (2 * Real.sqrt 2)) ^ (-2 : ℤ) *
      blaschkePairQ (xiStar + lam * s) (lam * e) (xiStar + lam * σ) =
      (α ^ (-2 : ℤ) * pairRatioG2 u1 v1) * (2 * pairRatioG2 u2 v1) := by
    rw [hpow_split, hpair_eq]; ring
  rw [hmul_eq]
  have hid : (α ^ (-2 : ℤ) * pairRatioG2 u1 v1) * (2 * pairRatioG2 u2 v1) - ((σ - sLim) ^ 2 + eLim ^ 2) =
      (α ^ (-2 : ℤ) * pairRatioG2 u1 v1 - ((σ - s) ^ 2 + e ^ 2)) * (2 * pairRatioG2 u2 v1) +
      ((σ - s) ^ 2 + e ^ 2) * (2 * pairRatioG2 u2 v1 - 1) +
      (((σ - s) ^ 2 - (σ - sLim) ^ 2) + (e ^ 2 - eLim ^ 2)) := by ring
  rw [hid]
  have hse_bd : |(σ - s) ^ 2 + e ^ 2| ≤ 5 * M₀ ^ 2 + 1 := by
    rw [abs_of_nonneg (by positivity)]
    have hσs : (σ - s) ^ 2 ≤ (2 * M₀) ^ 2 := by
      have : |σ - s| ≤ 2 * M₀ := (abs_sub σ s).trans (by linarith)
      simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) this 2
    have he_sq : e ^ 2 ≤ M₀ ^ 2 := pow_le_pow_left₀ he0 heM 2
    nlinarith only [hσs, he_sq]
  have hp1 : |(α ^ (-2 : ℤ) * pairRatioG2 u1 v1 - ((σ - s) ^ 2 + e ^ 2)) * (2 * pairRatioG2 u2 v1)| ≤ ε / 4 := by
    rw [abs_mul]
    calc _ ≤ (ε / 8) * 2 := mul_le_mul hg1_err hg2_bd (abs_nonneg _) (by positivity)
      _ = ε / 4 := by ring
  have hp2 : |((σ - s) ^ 2 + e ^ 2) * (2 * pairRatioG2 u2 v1 - 1)| ≤ ε / 3 := by
    rw [abs_mul]
    have ht2 := hg2_err.trans (min_le_right _ _)
    have hcoef_2 : 5 * M₀ ^ 2 + 1 ≤ (16 * (M₀ + 1) ^ 2 + 1) / 3 := by linarith [sq_nonneg M₀, hM₀]
    calc |((σ - s) ^ 2 + e ^ 2)| * |2 * pairRatioG2 u2 v1 - 1|
        ≤ (5 * M₀ ^ 2 + 1) * (ε / (16 * (M₀ + 1) ^ 2 + 1)) :=
          mul_le_mul hse_bd ht2 (abs_nonneg _) (by positivity)
      _ ≤ (16 * (M₀ + 1) ^ 2 + 1) / 3 * (ε / (16 * (M₀ + 1) ^ 2 + 1)) :=
          mul_le_mul_of_nonneg_right hcoef_2 (by positivity)
      _ = ε / 3 := by field_simp [(by positivity : 16 * (M₀ + 1) ^ 2 + 1 ≠ 0)]
  have hp3 : |((σ - s) ^ 2 - (σ - sLim) ^ 2) + (e ^ 2 - eLim ^ 2)| ≤ ε / 3 := by
    have hs1 : |s - sLim| ≤ 1 := hs_lim.trans (min_le_left _ _)
    have he1 : |e - eLim| ≤ 1 := he_lim.trans (min_le_left _ _)
    have hs_e : |s - sLim| ≤ ε / (18 * (M₀ + 1) + 6) := hs_lim.trans (min_le_right _ _)
    have he_e : |e - eLim| ≤ ε / (18 * (M₀ + 1) + 6) := he_lim.trans (min_le_right _ _)
    have hsum1 : |2 * σ - s - sLim| ≤ 4 * M₀ + 1 := by
      have hid1 : 2 * σ - s - sLim = 2 * (σ - s) + (s - sLim) := by ring
      rw [hid1]
      calc |2 * (σ - s) + (s - sLim)| ≤ |2 * (σ - s)| + |s - sLim| := abs_add_le _ _
        _ = 2 * |σ - s| + |s - sLim| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        _ ≤ 2 * (|σ| + |s|) + 1 := add_le_add (mul_le_mul_of_nonneg_left (abs_sub σ s) (by norm_num)) hs1
        _ ≤ 4 * M₀ + 1 := by linarith [hσ, hs]
    have hsum2 : |e + eLim| ≤ 2 * M₀ + 1 := by
      have hid2 : e + eLim = 2 * e - (e - eLim) := by ring
      rw [hid2]
      calc |2 * e - (e - eLim)| ≤ |2 * e| + |e - eLim| := abs_sub _ _
        _ = 2 * e + |e - eLim| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg he0]
        _ ≤ 2 * M₀ + 1 := by linarith [heM, he1]
    have ht1 : |(σ - s) ^ 2 - (σ - sLim) ^ 2| ≤ (ε / (18 * (M₀ + 1) + 6)) * (4 * M₀ + 1) := by
      rw [show (σ - s) ^ 2 - (σ - sLim) ^ 2 = (sLim - s) * (2 * σ - s - sLim) by ring, abs_mul, abs_sub_comm]
      exact mul_le_mul hs_e hsum1 (abs_nonneg _) (by positivity)
    have ht2 : |e ^ 2 - eLim ^ 2| ≤ (ε / (18 * (M₀ + 1) + 6)) * (2 * M₀ + 1) := by
      rw [show e ^ 2 - eLim ^ 2 = (e - eLim) * (e + eLim) by ring, abs_mul]
      exact mul_le_mul he_e hsum2 (abs_nonneg _) (by positivity)
    have htot := (abs_add_le _ _).trans (add_le_add ht1 ht2)
    have hcoef : (4 * M₀ + 1) + (2 * M₀ + 1) ≤ (18 * (M₀ + 1) + 6) / 3 := by linarith
    calc |((σ - s) ^ 2 - (σ - sLim) ^ 2) + (e ^ 2 - eLim ^ 2)|
        ≤ ((4 * M₀ + 1) + (2 * M₀ + 1)) * (ε / (18 * (M₀ + 1) + 6)) := by linarith only [htot]
      _ ≤ ((18 * (M₀ + 1) + 6) / 3) * (ε / (18 * (M₀ + 1) + 6)) := mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = ε / 3 := by field_simp [(by positivity : 18 * (M₀ + 1) + 6 ≠ 0)]
  have ha1 := abs_add_le
    ((α ^ (-2 : ℤ) * pairRatioG2 u1 v1 - ((σ - s) ^ 2 + e ^ 2)) * (2 * pairRatioG2 u2 v1) +
      ((σ - s) ^ 2 + e ^ 2) * (2 * pairRatioG2 u2 v1 - 1))
    (((σ - s) ^ 2 - (σ - sLim) ^ 2) + (e ^ 2 - eLim ^ 2))
  have ha2 := abs_add_le
    ((α ^ (-2 : ℤ) * pairRatioG2 u1 v1 - ((σ - s) ^ 2 + e ^ 2)) * (2 * pairRatioG2 u2 v1))
    (((σ - s) ^ 2 + e ^ 2) * (2 * pairRatioG2 u2 v1 - 1))
  linarith

private lemma neg_log_le_two_mul_rpow_neg_half {u : ℝ} (hu : 0 < u) :
    -Real.log u ≤ 2 * u ^ (-(1 / 2 : ℝ)) := by
  have h1 : Real.log (u ^ (-(1 / 2 : ℝ))) ≤ u ^ (-(1 / 2 : ℝ)) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hu _)
  rw [Real.log_rpow hu] at h1
  linarith

private lemma integral_rpow_neg_half_abs_le {B M₀ σ : ℝ} (hB : 0 ≤ B) (hM₀ : 0 ≤ M₀) (hσ : |σ| ≤ M₀) :
    ∫ s in (0 : ℝ)..B, |σ - s| ^ (-(1 / 2 : ℝ)) ≤ 4 * Real.sqrt (M₀ + B + 1) := by
  let R : ℝ := M₀ + B + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hint_pos : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) volume 0 R :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))
  have hval_rpow : ∫ t in (0 : ℝ)..R, t ^ (-(1 / 2 : ℝ)) = 2 * Real.sqrt R := by
    have h1 := integral_rpow (a := (0 : ℝ)) (b := R) (r := -(1 / 2 : ℝ)) (Or.inl (by norm_num))
    rw [Real.zero_rpow (by norm_num : -(1 / 2 : ℝ) + 1 ≠ 0), sub_zero] at h1
    rw [h1, Real.sqrt_eq_rpow]
    norm_num; ring
  have hint_abs : IntervalIntegrable (fun t : ℝ => |t| ^ (-(1 / 2 : ℝ))) volume (-R) R := by
    have h_l : IntervalIntegrable (fun t : ℝ => (-t) ^ (-(1 / 2 : ℝ))) volume (-R) 0 := by
      simpa using (IntervalIntegrable.comp_sub_left hint_pos 0).symm
    have h1 : IntervalIntegrable (fun t : ℝ => |t| ^ (-(1 / 2 : ℝ))) volume (-R) 0 := by
      refine h_l.congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      rw [Set.uIoc_of_le (by linarith)] at ht
      rw [abs_of_nonpos ht.2]
    have h2 : IntervalIntegrable (fun t : ℝ => |t| ^ (-(1 / 2 : ℝ))) volume 0 R := by
      refine hint_pos.congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      rw [Set.uIoc_of_le hR.le] at ht
      rw [abs_of_nonneg ht.1.le]
    exact h1.trans h2
  have hshift : ∫ s in (0 : ℝ)..B, |σ - s| ^ (-(1 / 2 : ℝ)) =
      ∫ t in (-σ)..(B - σ), |t| ^ (-(1 / 2 : ℝ)) := by
    have hcon : (fun s : ℝ => |σ - s| ^ (-(1 / 2 : ℝ))) = (fun s : ℝ => |s - σ| ^ (-(1 / 2 : ℝ))) := by
      ext s; rw [abs_sub_comm]
    rw [hcon]
    simpa [sub_eq_add_neg, zero_sub] using intervalIntegral.integral_comp_sub_right
      (fun t : ℝ => |t| ^ (-(1 / 2 : ℝ))) σ (a := 0) (b := B)
  have hσ_bds : -R ≤ -σ ∧ -σ ≤ B - σ ∧ B - σ ≤ R := by
    have := abs_le.mp hσ
    dsimp [R]; exact ⟨by linarith, by linarith, by linarith⟩
  have hle_R : ∫ t in (-σ)..(B - σ), |t| ^ (-(1 / 2 : ℝ)) ≤
      ∫ t in (-R)..R, |t| ^ (-(1 / 2 : ℝ)) := by
    have ha1 : IntervalIntegrable (fun t : ℝ => |t| ^ (-(1 / 2 : ℝ))) volume (-R) (-σ) :=
      hint_abs.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc
        (Set.mem_uIcc.mpr (Or.inl ⟨hσ_bds.1, by linarith⟩)))
    have ha2 : IntervalIntegrable (fun t : ℝ => |t| ^ (-(1 / 2 : ℝ))) volume (-σ) (B - σ) :=
      hint_abs.mono_set (Set.uIcc_subset_uIcc
        (Set.mem_uIcc.mpr (Or.inl ⟨hσ_bds.1, by linarith⟩))
        (Set.mem_uIcc.mpr (Or.inl ⟨by linarith, hσ_bds.2.2⟩)))
    have ha3 : IntervalIntegrable (fun t : ℝ => |t| ^ (-(1 / 2 : ℝ))) volume (B - σ) R :=
      hint_abs.mono_set (Set.uIcc_subset_uIcc
        (Set.mem_uIcc.mpr (Or.inl ⟨by linarith, hσ_bds.2.2⟩)) Set.right_mem_uIcc)
    have hsp1 := intervalIntegral.integral_add_adjacent_intervals ha1 ha2
    have hsp2 := intervalIntegral.integral_add_adjacent_intervals (ha1.trans ha2) ha3
    have hnn1 : 0 ≤ ∫ t in (-R)..(-σ), |t| ^ (-(1 / 2 : ℝ)) :=
      intervalIntegral.integral_nonneg hσ_bds.1 (fun _ _ => by positivity)
    have hnn3 : 0 ≤ ∫ t in (B - σ)..R, |t| ^ (-(1 / 2 : ℝ)) :=
      intervalIntegral.integral_nonneg hσ_bds.2.2 (fun _ _ => by positivity)
    linarith
  have heven : ∫ t in (-R)..R, |t| ^ (-(1 / 2 : ℝ)) = 4 * Real.sqrt R := by
    have h_l : IntervalIntegrable (fun t : ℝ => |t| ^ (-(1 / 2 : ℝ))) volume (-R) 0 :=
      hint_abs.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc
        (Set.mem_uIcc.mpr (Or.inl ⟨by linarith, hR.le⟩)))
    have h_r : IntervalIntegrable (fun t : ℝ => |t| ^ (-(1 / 2 : ℝ))) volume 0 R :=
      hint_abs.mono_set (Set.uIcc_subset_uIcc
        (Set.mem_uIcc.mpr (Or.inl ⟨by linarith, hR.le⟩)) Set.right_mem_uIcc)
    have hsp := intervalIntegral.integral_add_adjacent_intervals h_l h_r
    have hl_eq : ∫ t in (-R)..0, |t| ^ (-(1 / 2 : ℝ)) = ∫ t in (0 : ℝ)..R, t ^ (-(1 / 2 : ℝ)) := by
      have hc : ∫ t in (-R)..0, |t| ^ (-(1 / 2 : ℝ)) = ∫ t in (-R)..0, (-t) ^ (-(1 / 2 : ℝ)) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards with t ht
        rw [Set.uIoc_of_le (by linarith)] at ht
        rw [abs_of_nonpos ht.2]
      rw [hc, intervalIntegral.integral_comp_neg (a := -R) (b := 0) (fun t : ℝ => t ^ (-(1 / 2 : ℝ)))]
      simp
    have hr_eq : ∫ t in (0 : ℝ)..R, |t| ^ (-(1 / 2 : ℝ)) = ∫ t in (0 : ℝ)..R, t ^ (-(1 / 2 : ℝ)) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with t ht
      rw [Set.uIoc_of_le hR.le] at ht
      rw [abs_of_nonneg ht.1.le]
    rw [← hsp, hl_eq, hr_eq, hval_rpow]
    ring
  linarith

private lemma integral_sqrt_mul_abs_log_le {B M₀ σ : ℝ} (hB : 0 ≤ B) (hM₀ : 0 ≤ M₀) (hσ : |σ| ≤ M₀) :
    (∫ s in (0 : ℝ)..B, Real.sqrt s * |Real.log (|σ - s|)|) ≤
      Real.sqrt B * (B * (B + M₀ + 1) + 8 * Real.sqrt (M₀ + B + 1)) := by
  let C₁ : ℝ := B + M₀ + 1
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hpoint : ∀ s ∈ Set.Ioc 0 B,
      Real.sqrt s * |Real.log (|σ - s|)| ≤
        Real.sqrt B * (C₁ + 2 * |σ - s| ^ (-(1 / 2 : ℝ))) := by
    intro s hs
    have hs_pos : Real.sqrt s ≤ Real.sqrt B := Real.sqrt_le_sqrt hs.2
    have h_abs_log : |Real.log (|σ - s|)| ≤ C₁ + 2 * |σ - s| ^ (-(1 / 2 : ℝ)) := by
      by_cases hzero : σ = s
      · subst hzero; simp [Real.log_zero]; positivity
      · have hd : 0 < |σ - s| := abs_pos.mpr (sub_ne_zero.mpr hzero)
        rcases le_or_gt 1 |σ - s| with h1 | h1
        · rw [abs_of_nonneg (Real.log_nonneg h1)]
          have h2 : Real.log |σ - s| ≤ |σ - s| := (Real.log_le_sub_one_of_pos hd).trans (by linarith)
          have h3 : |σ - s| ≤ C₁ := by
            have htri := abs_sub σ s
            rw [abs_of_pos hs.1] at htri
            have hσ_le : |σ| ≤ M₀ := hσ
            dsimp [C₁]; linarith [hs.2, htri, hσ_le]
          have h4 : 0 ≤ 2 * |σ - s| ^ (-(1 / 2 : ℝ)) := by positivity
          linarith
        · rw [abs_of_nonpos (Real.log_nonpos hd.le h1.le)]
          have h2 := neg_log_le_two_mul_rpow_neg_half hd
          linarith
    have hnn1 : 0 ≤ |Real.log (|σ - s|)| := abs_nonneg _
    have hnn2 : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
    calc Real.sqrt s * |Real.log (|σ - s|)| ≤ Real.sqrt B * |Real.log (|σ - s|)| :=
          mul_le_mul_of_nonneg_right hs_pos hnn1
      _ ≤ Real.sqrt B * (C₁ + 2 * |σ - s| ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left h_abs_log (Real.sqrt_nonneg B)
  have hint_rpow : IntervalIntegrable (fun s : ℝ => |σ - s| ^ (-(1 / 2 : ℝ))) volume 0 B := by
    have hcomp : IntervalIntegrable (fun s : ℝ => |s - σ| ^ (-(1 / 2 : ℝ))) volume 0 B := by
      have hpos_r : 0 < M₀ + B + 1 := by positivity
      have hint0 : IntervalIntegrable (fun t : ℝ => |t| ^ (-(1 / 2 : ℝ))) volume (-σ) (B - σ) := by
        let R := M₀ + B + 1
        have hint_p : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) volume 0 R :=
          intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))
        have hint_l : IntervalIntegrable (fun t : ℝ => (-t) ^ (-(1 / 2 : ℝ))) volume (-R) 0 := by
          simpa using (IntervalIntegrable.comp_sub_left hint_p 0).symm
        have h1 : IntervalIntegrable (fun t : ℝ => |t| ^ (-(1 / 2 : ℝ))) volume (-R) 0 := by
          refine hint_l.congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
          rw [Set.uIoc_of_le (by linarith)] at ht
          rw [abs_of_nonpos ht.2]
        have h2 : IntervalIntegrable (fun t : ℝ => |t| ^ (-(1 / 2 : ℝ))) volume 0 R := by
          refine hint_p.congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
          rw [Set.uIoc_of_le hpos_r.le] at ht
          rw [abs_of_nonneg ht.1.le]
        have hall := h1.trans h2
        have hb1 := (abs_le.mp hσ).1
        have hb2 := (abs_le.mp hσ).2
        exact hall.mono_set (Set.uIcc_subset_uIcc
          (Set.mem_uIcc.mpr (Or.inl ⟨by dsimp [R]; linarith, by dsimp [R]; linarith⟩))
          (Set.mem_uIcc.mpr (Or.inl ⟨by dsimp [R]; linarith, by dsimp [R]; linarith⟩)))
      simpa [sub_eq_add_neg, zero_sub] using hint0.comp_sub_right σ
    exact hcomp.congr_ae (Eventually.of_forall fun s => by dsimp only; rw [abs_sub_comm])
  have hint_rhs : IntervalIntegrable (fun s : ℝ => Real.sqrt B * (C₁ + 2 * |σ - s| ^ (-(1 / 2 : ℝ)))) volume 0 B :=
    (intervalIntegrable_const.add (hint_rpow.const_mul 2)).const_mul _
  have hint_lhs : IntervalIntegrable (fun s : ℝ => Real.sqrt s * |Real.log (|σ - s|)|) volume 0 B := by
    have hlog_int : IntervalIntegrable (fun s : ℝ => Real.log |σ - s|) volume 0 B := by
      rw [show (fun s : ℝ => Real.log |σ - s|) = fun s : ℝ => Real.log |s - σ| by
        ext s; rw [abs_sub_comm]]
      have hl0 : IntervalIntegrable Real.log volume (-σ) (B - σ) :=
        intervalIntegral.intervalIntegrable_log'
      have hlog_eq : (fun s : ℝ => Real.log (s - σ)) = fun s : ℝ => Real.log |s - σ| :=
        funext fun s => (Real.log_abs (s - σ)).symm
      simpa [sub_eq_add_neg, zero_sub] using (hl0.comp_sub_right σ).congr_ae
        (Eventually.of_forall fun s => congrFun hlog_eq s)
    have h_asm : AEStronglyMeasurable (fun s : ℝ => Real.sqrt s * |Real.log (|σ - s|)|)
        (volume.restrict (Set.uIoc 0 B)) := by
      rw [Set.uIoc_of_le hB]
      have h2 := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hB).mp hlog_int.abs).1
      exact Real.continuous_sqrt.aestronglyMeasurable.mul h2
    refine IntervalIntegrable.mono_fun hint_rhs h_asm ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [Set.uIoc_of_le hB] at hs
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)),
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (add_nonneg hC₁ (by positivity)))]
    exact hpoint s hs
  have hm := intervalIntegral.integral_mono_on_of_le_Ioo hB hint_lhs hint_rhs fun s hs => hpoint s ⟨hs.1, hs.2.le⟩
  have h_rpow_le := integral_rpow_neg_half_abs_le hB hM₀ hσ
  have hrhs_eq : ∫ s in (0 : ℝ)..B, Real.sqrt B * (C₁ + 2 * |σ - s| ^ (-(1 / 2 : ℝ))) =
      Real.sqrt B * (B * C₁ + 2 * ∫ s in (0 : ℝ)..B, |σ - s| ^ (-(1 / 2 : ℝ))) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const (hint_rpow.const_mul 2),
      intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul]
    ring
  rw [hrhs_eq] at hm
  refine hm.trans ?_
  have h1 : B * C₁ + 2 * ∫ s in (0 : ℝ)..B, |σ - s| ^ (-(1 / 2 : ℝ)) ≤
      B * (B + M₀ + 1) + 8 * Real.sqrt (M₀ + B + 1) := by linarith
  exact mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg B)

private lemma rpow_neg_half_abs_integrableOn {σ A B : ℝ} (_hAB : A ≤ B) :
    IntervalIntegrable (fun s : ℝ => Real.log |σ - s|) volume A B := by
  have hl0 : IntervalIntegrable Real.log volume (A - σ) (B - σ) :=
    intervalIntegral.intervalIntegrable_log'
  have hc := hl0.comp_sub_right σ
  rw [show A - σ + σ = A by ring, show B - σ + σ = B by ring] at hc
  refine hc.congr_ae (Eventually.of_forall fun s => ?_)
  change Real.log (s - σ) = Real.log |σ - s|
  rw [← Real.log_abs, abs_sub_comm]

private lemma intervalIntegrable_rhoU_mul_log (c' lam σ B : ℝ) (hlam : 0 ≤ lam) (hB : 0 ≤ B) :
    IntervalIntegrable (fun s : ℝ => (c' * lam * rhoU (xiStar + lam * s) / 2) * Real.log |σ - s|)
      volume 0 B := by
  have h_log := rpow_neg_half_abs_integrableOn (σ := σ) (A := 0) (B := B) hB
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hB] at h_log ⊢
  have hcont_φ' : ContinuousOn (fun s : ℝ => c' * lam * rhoU (xiStar + lam * s) / 2) (Set.Icc 0 B) := by
    refine (ContinuousOn.mul continuousOn_const
      (continuousOn_rhoU.comp (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
        fun s hs => by change xiStar ≤ xiStar + lam * s; linarith only [mul_nonneg hlam hs.1])).div_const 2
  obtain ⟨B_φ, hB_φ⟩ := (isCompact_Icc.image_of_continuousOn hcont_φ'.abs).isBounded.exists_norm_le
  exact h_log.bdd_mul (hcont_φ'.aestronglyMeasurable measurableSet_Icc |>.mono_set Set.Ioc_subset_Icc_self)
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs => by
      have hb := hB_φ |c' * lam * rhoU (xiStar + lam * s) / 2| ⟨s, ⟨hs.1.le, hs.2⟩, rfl⟩
      rwa [Real.norm_eq_abs, abs_abs, ← Real.norm_eq_abs] at hb))

private lemma stepA_integral_bound {c' x P₀ lam a₀ A M₀ σ ε : ℝ} (hpos_a : 0 < a₀ - 1 / 4)
    (hε_nn : 0 ≤ ε)
    (hint_phi : IntervalIntegrable (phiVar c' x) volume (1 / 4) a₀)
    (hint_σa : IntervalIntegrable (fun a : ℝ => Real.log |σ - siteRadius c' a / lam|) volume (1 / 4) a₀)
    (hae_ne : ∀ᵐ a ∂(volume.restrict (Set.Ioc (1 / 4 : ℝ) a₀)), chiQuantile c' a ≠ x)
    (h_pt_err : ∀ a ∈ Set.Ioc (1 / 4 : ℝ) a₀, chiQuantile c' a ≠ x →
      |((phiVar c' x a - Real.log P₀) - Real.log (|σ - siteRadius c' a / lam|))| ≤
        (π * lam * (M₀ + A + 1)) ^ 2 / 2 + ε / (12 * (a₀ - 1 / 4) + 1))
    (hlam_z1 : (π * lam * (M₀ + A + 1)) ^ 2 / 2 * (2 * (a₀ - 1 / 4)) ≤ ε / 6) :
    |-2 * (∫ a in (1 / 4 : ℝ)..a₀, (phiVar c' x a - Real.log P₀)) -
        (-2 * (∫ a in (1 / 4 : ℝ)..a₀, Real.log |σ - siteRadius c' a / lam|))| ≤ ε / 3 := by
  have ha0_gt : (1 / 4 : ℝ) < a₀ := by linarith
  have hsub : -2 * (∫ a in (1 / 4 : ℝ)..a₀, (phiVar c' x a - Real.log P₀)) -
      (-2 * (∫ a in (1 / 4 : ℝ)..a₀, Real.log |σ - siteRadius c' a / lam|)) =
      -2 * (∫ a in (1 / 4 : ℝ)..a₀, ((phiVar c' x a - Real.log P₀) - Real.log |σ - siteRadius c' a / lam|)) := by
    rw [intervalIntegral.integral_sub (hint_phi.sub intervalIntegrable_const) hint_σa, mul_sub]
  rw [hsub, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hle_int : |∫ a in (1 / 4 : ℝ)..a₀,
      ((phiVar c' x a - Real.log P₀) - Real.log |σ - siteRadius c' a / lam|)| ≤
      ((π * lam * (M₀ + A + 1)) ^ 2 / 2 + ε / (12 * (a₀ - 1 / 4) + 1)) * (a₀ - 1 / 4) := by
    let B_e := (π * lam * (M₀ + A + 1)) ^ 2 / 2 + ε / (12 * (a₀ - 1 / 4) + 1)
    have hae_ne' : ∀ᵐ a ∂volume, a ∈ Set.Ioc (1 / 4 : ℝ) a₀ → chiQuantile c' a ≠ x :=
      (ae_restrict_iff' measurableSet_Ioc).mp hae_ne
    have hae_bd : ∀ᵐ a ∂volume, a ∈ Set.uIoc (1 / 4 : ℝ) a₀ →
        ‖(phiVar c' x a - Real.log P₀) - Real.log |σ - siteRadius c' a / lam|‖ ≤ B_e := by
      filter_upwards [hae_ne'] with a hne ha_mem
      rw [Set.uIoc_of_le ha0_gt.le] at ha_mem
      rw [Real.norm_eq_abs]; exact h_pt_err a ha_mem (hne ha_mem)
    have h2 := intervalIntegral.norm_integral_le_of_norm_le_const_ae hae_bd
    rw [Real.norm_eq_abs, abs_of_nonneg hpos_a.le] at h2
    exact h2
  calc 2 * |∫ a in (1 / 4 : ℝ)..a₀, ((phiVar c' x a - Real.log P₀) - Real.log |σ - siteRadius c' a / lam|)|
      ≤ 2 * (((π * lam * (M₀ + A + 1)) ^ 2 / 2 + ε / (12 * (a₀ - 1 / 4) + 1)) * (a₀ - 1 / 4)) :=
        mul_le_mul_of_nonneg_left hle_int (by norm_num)
    _ = (π * lam * (M₀ + A + 1)) ^ 2 / 2 * (2 * (a₀ - 1 / 4)) +
          ε * (2 * (a₀ - 1 / 4) / (12 * (a₀ - 1 / 4) + 1)) := by ring
    _ ≤ ε / 6 + ε / 6 := by
        refine add_le_add hlam_z1 ?_
        calc ε * (2 * (a₀ - 1 / 4) / (12 * (a₀ - 1 / 4) + 1))
            ≤ ε * (2 * (a₀ - 1 / 4) / (12 * (a₀ - 1 / 4))) := by gcongr; linarith
          _ = ε / 6 := by
              have h2_ne : 2 * (a₀ - 1 / 4) ≠ 0 := by linarith only [hpos_a]
              rw [show 12 * (a₀ - 1 / 4) = (2 * (a₀ - 1 / 4)) * 6 by ring,
                div_mul_eq_div_div, div_self h2_ne]
              ring
    _ = ε / 3 := by ring

private lemma stepB_integral_bound {c' σ a₀ Sa0 A M₀ C_I R_tail ε : ℝ}
    (hc'_pos : 0 < c') (ha0_gt : 1 / 4 < a₀) (hA_pos : 0 < A) (hM₀ : 0 ≤ M₀)
    (hσ_le : σ ≤ A / 2) (hσ_abs : |σ| ≤ M₀)
    (hSa0_eq : Sa0 = siteRadius c' a₀ / lambdaComb c')
    (hSa0_diff : |Sa0 - A| ≤ (2 * c1K0 / 3) * A ^ 2 * lambdaComb c')
    (hSa0_bds : 3 / 4 * A ≤ Sa0 ∧ Sa0 ≤ A + 1)
    (hlam_xi : lambdaComb c' * (M₀ + A + 1) ≤ xiStar / 2)
    (hlam_jac : (3 * (π / (4 * Real.sqrt 2)) * lambdaComb c' * (A + 1)) * C_I ≤ ε / 6)
    (hlam_tail : 6 * Real.sqrt (A + 1) * R_tail * ((2 * c1K0 / 3) * A ^ 2 * lambdaComb c') ≤ ε / 6)
    (hCI_eq : C_I = Real.sqrt (A + 1) * ((A + 1) * (A + 1 + M₀ + 1) + 8 * Real.sqrt (M₀ + (A + 1) + 1)))
    (hR_eq : R_tail = max (|Real.log (A / 4)|) (|Real.log (A + 1 + M₀ + 1)|) + 1) :
    IntervalIntegrable (fun a : ℝ => Real.log |σ - siteRadius c' a / lambdaComb c'|) volume (1 / 4) a₀ ∧
      |-2 * (∫ a in (1 / 4 : ℝ)..a₀, Real.log |σ - siteRadius c' a / lambdaComb c'|) - continuumFQ A σ| ≤
        ε / 3 := by
  let lam : ℝ := lambdaComb c'
  have hlam_pos : 0 < lam := lambdaComb_pos hc'_pos
  have hSa0_pos : 0 < Sa0 := by linarith only [hA_pos, hSa0_bds.1]
  let φ : ℝ → ℝ := fun s => 1 / 4 + c' * cumulN (xiStar + lam * s)
  let φ' : ℝ → ℝ := fun s => c' * lam * rhoU (xiStar + lam * s) / 2
  have hφ_deriv : ∀ s ∈ Set.Ioo 0 Sa0, HasDerivWithinAt φ (φ' s) (Set.Ioo 0 Sa0) s := by
    intro s hs
    have hxi : xiStar < xiStar + lam * s := by linarith only [mul_pos hlam_pos hs.1]
    have hinner : HasDerivAt (fun t : ℝ => xiStar + lam * t) lam s := by
      simpa using ((hasDerivAt_id s).const_mul lam).const_add xiStar
    have hcomp := (hasDerivAt_cumulN hxi).comp s hinner
    have htot := ((hcomp.const_mul c').const_add (1 / 4 : ℝ)).congr_deriv
      (show c' * (rhoU (xiStar + lam * s) / 2 * lam) = φ' s by dsimp [φ']; ring)
    exact (htot.hasDerivWithinAt : HasDerivWithinAt (fun x : ℝ => 1 / 4 + c' * cumulN (xiStar + lam * x))
      (φ' s) (Set.Ioo 0 Sa0) s)
  have hφ_strictMono : StrictMonoOn φ (Set.Ici 0) := by
    intro s₁ hs₁ s₂ hs₂ hs₁₂
    have h1 : xiStar ≤ xiStar + lam * s₁ := by linarith only [mul_nonneg hlam_pos.le (Set.mem_Ici.mp hs₁)]
    have h2 : xiStar + lam * s₁ < xiStar + lam * s₂ := by linarith only [mul_lt_mul_of_pos_left hs₁₂ hlam_pos]
    have hcm := cumulN_strictMonoOn h1 (h1.trans h2.le) h2
    dsimp [φ]; linarith only [mul_lt_mul_of_pos_left hcm hc'_pos]
  have hφ_inj : InjOn φ (Set.Ioo 0 Sa0) :=
    (hφ_strictMono.mono fun _ (hx : _ ∈ Set.Ioo (0 : ℝ) _) => Set.mem_Ici.mpr hx.1.le).injOn
  have hφ_im : φ '' Set.Ioo 0 Sa0 = Set.Ioo (1 / 4 : ℝ) a₀ := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      have h0 : φ 0 = 1 / 4 := by dsimp [φ]; simp [cumulN_xiStar]
      have hSa : φ Sa0 = a₀ := by
        dsimp [φ]; rw [hSa0_eq]; unfold siteRadius
        rw [show xiStar + lam * ((chiQuantile c' a₀ - xiStar) / lam) = chiQuantile c' a₀ by
          field_simp [hlam_pos.ne']; ring, (chiQuantile_spec hc'_pos ha0_gt.le).2]
        ring
      have hlt1 : φ 0 < φ s := hφ_strictMono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs.1.le) hs.1
      have hlt2 : φ s < φ Sa0 := hφ_strictMono (Set.mem_Ici.mpr hs.1.le) (Set.mem_Ici.mpr hSa0_pos.le) hs.2
      exact ⟨by linarith only [h0, hlt1], by linarith only [hSa, hlt2]⟩
    · intro hy
      have hχ_lt : chiQuantile c' y < chiQuantile c' a₀ :=
        chiQuantile_strictMonoOn hc'_pos (Set.mem_Ici.mpr hy.1.le) (Set.mem_Ici.mpr (hy.1.le.trans hy.2.le)) hy.2
      refine ⟨(chiQuantile c' y - xiStar) / lam, ⟨div_pos (by linarith only [xiStar_lt_chiQuantile hc'_pos hy.1]) hlam_pos, ?_⟩, ?_⟩
      · rw [hSa0_eq]; unfold siteRadius
        exact div_lt_div_of_pos_right (by linarith only [hχ_lt]) hlam_pos
      · dsimp [φ]
        rw [show xiStar + lam * ((chiQuantile c' y - xiStar) / lam) = chiQuantile c' y by
          field_simp [hlam_pos.ne']; ring, (chiQuantile_spec hc'_pos hy.1.le).2]
        ring
  have h_inv_id : ∀ s ∈ Set.Ioo 0 Sa0, siteRadius c' (φ s) / lam = s := by
    intro s hs
    have hs_mem : φ s ∈ Set.Ioo (1 / 4 : ℝ) a₀ := hφ_im ▸ Set.mem_image_of_mem φ hs
    have hχ_eq : chiQuantile c' (φ s) = xiStar + lam * s := by
      refine chiQuantile_eq_of_cumulN hc'_pos hs_mem.1.le (by linarith only [mul_pos hlam_pos hs.1]) ?_
      dsimp [φ]; ring
    unfold siteRadius; rw [hχ_eq]; field_simp [hlam_pos.ne']; ring
  have hφ'_nn : ∀ s : ℝ, 0 ≤ s → 0 ≤ φ' s := fun s _ => by
    dsimp [φ']
    exact div_nonneg (mul_nonneg (mul_nonneg hc'_pos.le hlam_pos.le) (rhoU_nonneg _)) (by norm_num)
  have hc_lam_kTip : c' * kTip * lam ^ (3 / 2 : ℝ) = 1 := by
    dsimp [lam]; unfold lambdaComb
    have hkc : 0 < kTip * c' := mul_pos kTip_pos hc'_pos
    rw [← Real.rpow_mul hkc.le, show -(2 / 3 : ℝ) * (3 / 2) = -1 by norm_num, Real.rpow_neg_one, mul_inv]
    field_simp [hc'_pos.ne', kTip_pos.ne']
  have hφ'_diff : ∀ s ∈ Set.Ioc 0 (A + 1),
      |2 * φ' s - 3 * Real.sqrt s| ≤ 3 * (π / (4 * Real.sqrt 2)) * lam * (A + 1) * Real.sqrt s := by
    intro s hs
    have hrho := rhoU_tip_asymptotic (lam * s) (mul_nonneg hlam_pos.le hs.1.le)
    have h_scale : c' * lam * (3 * kTip * Real.sqrt (lam * s)) = 3 * Real.sqrt s := by
      rw [Real.sqrt_mul hlam_pos.le, Real.sqrt_eq_rpow lam]
      calc c' * lam * (3 * kTip * (lam ^ (1 / 2 : ℝ) * Real.sqrt s))
          = 3 * (c' * kTip * (lam * lam ^ (1 / 2 : ℝ))) * Real.sqrt s := by ring
        _ = 3 * (c' * kTip * lam ^ (3 / 2 : ℝ)) * Real.sqrt s := by
            rw [← Real.rpow_one_add' hlam_pos.le (by norm_num : (1 : ℝ) + 1 / 2 ≠ 0)]; norm_num
        _ = 3 * Real.sqrt s := by rw [hc_lam_kTip]; ring
    have h2φ : 2 * φ' s = c' * lam * rhoU (xiStar + lam * s) := by dsimp [φ']; ring
    rw [h2φ]
    have h_lo : 3 * Real.sqrt s ≤ c' * lam * rhoU (xiStar + lam * s) := by
      calc 3 * Real.sqrt s = c' * lam * (3 * kTip * Real.sqrt (lam * s)) := h_scale.symm
        _ ≤ c' * lam * rhoU (xiStar + lam * s) := mul_le_mul_of_nonneg_left hrho.1 (by positivity)
    have h_hi : c' * lam * rhoU (xiStar + lam * s) ≤
        3 * Real.sqrt s * (1 + (π / (4 * Real.sqrt 2)) * (lam * s)) := by
      calc c' * lam * rhoU (xiStar + lam * s)
          ≤ c' * lam * (3 * kTip * Real.sqrt (lam * s) * (1 + (π / (4 * Real.sqrt 2)) * (lam * s))) :=
            mul_le_mul_of_nonneg_left hrho.2 (by positivity)
        _ = (c' * lam * (3 * kTip * Real.sqrt (lam * s))) * (1 + (π / (4 * Real.sqrt 2)) * (lam * s)) := by ring
        _ = 3 * Real.sqrt s * (1 + (π / (4 * Real.sqrt 2)) * (lam * s)) := by rw [h_scale]
    rw [abs_of_nonneg (sub_nonneg.mpr h_lo)]
    calc c' * lam * rhoU (xiStar + lam * s) - 3 * Real.sqrt s
        ≤ 3 * Real.sqrt s * (1 + (π / (4 * Real.sqrt 2)) * (lam * s)) - 3 * Real.sqrt s := by linarith only [h_hi]
      _ = 3 * (π / (4 * Real.sqrt 2)) * lam * s * Real.sqrt s := by ring
      _ ≤ 3 * (π / (4 * Real.sqrt 2)) * lam * (A + 1) * Real.sqrt s := by gcongr; exact hs.2
  have hcov : ∫ a in (1 / 4 : ℝ)..a₀, Real.log |σ - siteRadius c' a / lam| =
      ∫ s in (0 : ℝ)..Sa0, φ' s * Real.log |σ - s| := by
    rw [intervalIntegral.integral_of_le ha0_gt.le, intervalIntegral.integral_of_le hSa0_pos.le,
      ← MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc,
      ← MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc, ← hφ_im,
      integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hφ_deriv hφ_inj]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    rw [smul_eq_mul, abs_of_nonneg (hφ'_nn s hs.1.le), h_inv_id s hs]
  have hint_log_φ' : ∀ B : ℝ, 0 ≤ B →
      IntervalIntegrable (fun s : ℝ => φ' s * Real.log |σ - s|) volume 0 B :=
    fun B hB => intervalIntegrable_rhoU_mul_log c' lam σ B hlam_pos.le hB
  have hint_σa : IntervalIntegrable (fun a : ℝ => Real.log |σ - siteRadius c' a / lam|) volume (1 / 4) a₀ := by
    have h1 : IntegrableOn (fun a : ℝ => Real.log |σ - siteRadius c' a / lam|) (Set.Ioo (1 / 4 : ℝ) a₀) volume := by
      rw [← hφ_im, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hφ_deriv hφ_inj]
      have hi := (hint_log_φ' Sa0 hSa0_pos.le)
      rw [intervalIntegral.integral_of_le hSa0_pos.le] at *
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hSa0_pos.le] at hi
      refine (hi.mono_set Set.Ioo_subset_Ioc_self).congr_fun (fun s hs => ?_) measurableSet_Ioo
      rw [smul_eq_mul, abs_of_nonneg (hφ'_nn s hs.1.le), h_inv_id s hs]
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha0_gt.le]
    simpa [MeasureTheory.IntegrableOn, ← MeasureTheory.Measure.restrict_congr_set Ioo_ae_eq_Ioc] using h1
  refine ⟨hint_σa, ?_⟩
  have hint_sqrt_log : ∀ B : ℝ, 0 ≤ B →
      IntervalIntegrable (fun s : ℝ => Real.sqrt s * Real.log |σ - s|) volume 0 B := by
    intro B hB
    have hl := rpow_neg_half_abs_integrableOn (σ := σ) (A := 0) (B := B) hB
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hB] at hl ⊢
    exact hl.bdd_mul (Real.continuous_sqrt.aestronglyMeasurable.mono_ac Measure.restrict_le_self.absolutelyContinuous)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg s)]
        exact Real.sqrt_le_sqrt hs.2))
  have hstepB1 : |-2 * (∫ s in (0 : ℝ)..A, φ' s * Real.log |σ - s|) - continuumFQ A σ| ≤ ε / 6 := by
    have hfq_eq : continuumFQ A σ = -3 * ∫ s in (0 : ℝ)..A, Real.sqrt s * Real.log |σ - s| := by
      unfold continuumFQ
      congr 1
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs => ?_)
      rw [Set.uIoc_of_le hA_pos.le] at hs
      rw [Real.sqrt_eq_rpow]
    have hsub : -2 * (∫ s in (0 : ℝ)..A, φ' s * Real.log |σ - s|) - continuumFQ A σ =
        -∫ s in (0 : ℝ)..A, (2 * φ' s - 3 * Real.sqrt s) * Real.log |σ - s| := by
      rw [hfq_eq, ← intervalIntegral.integral_const_mul (-2 : ℝ),
        ← intervalIntegral.integral_const_mul (-3 : ℝ),
        ← intervalIntegral.integral_sub ((hint_log_φ' A hA_pos.le).const_mul (-2))
          ((hint_sqrt_log A hA_pos.le).const_mul (-3)),
        ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun s _ => by ring
    rw [hsub, abs_neg]
    have h_abs_int : |∫ s in (0 : ℝ)..A, (2 * φ' s - 3 * Real.sqrt s) * Real.log (|σ - s|)| ≤
        (3 * (π / (4 * Real.sqrt 2)) * lam * (A + 1)) * (∫ s in (0 : ℝ)..A, Real.sqrt s * |Real.log (|σ - s|)|) := by
      rw [← Real.norm_eq_abs, ← intervalIntegral.integral_const_mul]
      refine (intervalIntegral.norm_integral_le_of_norm_le hA_pos.le ?_
        ((hint_sqrt_log A hA_pos.le).abs.congr_ae (Eventually.of_forall fun s => ?_) |>.const_mul _))
      · filter_upwards with s hs
        rw [Real.norm_eq_abs, abs_mul]
        have hs' : s ∈ Set.Ioc 0 (A + 1) := ⟨hs.1, hs.2.trans (by linarith only [])⟩
        have hd := hφ'_diff s hs'
        calc |2 * φ' s - 3 * Real.sqrt s| * |Real.log (|σ - s|)|
            ≤ (3 * (π / (4 * Real.sqrt 2)) * lam * (A + 1) * Real.sqrt s) * |Real.log (|σ - s|)| :=
              mul_le_mul_of_nonneg_right hd (abs_nonneg _)
          _ = _ := by ring
      · simp [abs_mul, abs_of_nonneg (Real.sqrt_nonneg s)]
    have h_I : (∫ s in (0 : ℝ)..A, Real.sqrt s * |Real.log (|σ - s|)|) ≤ C_I := by
      have h1 := integral_sqrt_mul_abs_log_le hA_pos.le hM₀ hσ_abs
      have hle_CI : Real.sqrt A * (A * (A + M₀ + 1) + 8 * Real.sqrt (M₀ + A + 1)) ≤ C_I := by
        rw [hCI_eq]
        gcongr <;> linarith only [hA_pos]
      exact h1.trans hle_CI
    calc |(∫ s in (0 : ℝ)..A, (2 * φ' s - 3 * Real.sqrt s) * Real.log |σ - s|)|
        ≤ (3 * (π / (4 * Real.sqrt 2)) * lam * (A + 1)) * C_I :=
          h_abs_int.trans (mul_le_mul_of_nonneg_left h_I (by positivity))
      _ ≤ ε / 6 := hlam_jac
  have hstepB2 : |-2 * (∫ s in A..Sa0, φ' s * Real.log |σ - s|)| ≤ ε / 6 := by
    have h_diff_int : ∀ s ∈ Set.uIcc A Sa0,
        |2 * φ' s * Real.log (|σ - s|)| ≤ 6 * Real.sqrt (A + 1) * R_tail := by
      intro s hs
      have hs_range : (3 / 4 : ℝ) * A ≤ s ∧ s ≤ A + 1 := by
        rcases Set.mem_uIcc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨by linarith only [hA_pos, h1], h2.trans hSa0_bds.2⟩
        · exact ⟨hSa0_bds.1.trans h1, h2.trans (by linarith only [])⟩
      have h2φ_bd : |2 * φ' s| ≤ 6 * Real.sqrt (A + 1) := by
        have hpos_2φ : 0 ≤ 2 * φ' s := mul_nonneg (by norm_num) (hφ'_nn s (by linarith only [hA_pos, hs_range.1]))
        rw [abs_of_nonneg hpos_2φ]
        have hs_mem : s ∈ Set.Ioc 0 (A + 1) := ⟨by linarith only [hA_pos, hs_range.1], hs_range.2⟩
        have hd := (abs_le.mp (hφ'_diff s hs_mem)).2
        have h1 : 3 * (π / (4 * Real.sqrt 2)) * lam * (A + 1) ≤ 3 := by
          have hpi4 : π / (4 * Real.sqrt 2) ≤ 1 := by
            have hpi : π < 4 := Real.pi_lt_four
            have hsqrt2 : 1 < Real.sqrt 2 := by
              rw [← Real.sqrt_one]; exact Real.sqrt_lt_sqrt zero_le_one (by norm_num)
            have h4 : 4 < 4 * Real.sqrt 2 := by linarith only [hsqrt2]
            exact (div_le_one (by positivity)).mpr (by linarith only [hpi, h4])
          have hlam_1 : lam * (A + 1) ≤ 1 := by
            have hA_le : A + 1 ≤ M₀ + A + 1 := by linarith only [hM₀]
            have hxi_le : xiStar < 1 := by
              by_contra h
              have hsinh1 : Real.sinh (π * xiStar) = 1 := sinh_pi_mul_xiStar
              have hle3 : (3 : ℝ) ≤ π * xiStar := by
                have hpi3 := Real.pi_gt_three
                have hxi1 : (1 : ℝ) ≤ xiStar := not_lt.mp h
                calc (3 : ℝ) ≤ π * 1 := by linarith only [hpi3]
                  _ ≤ π * xiStar := mul_le_mul_of_nonneg_left hxi1 (by positivity)
              have hsinh_le := Real.sinh_le_sinh.mpr hle3
              have h3 : (3 : ℝ) ≤ Real.sinh 3 := by
                have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
                have he3 : (8 : ℝ) ≤ Real.exp 3 := by
                  have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he1 3
                  rw [← Real.exp_nat_mul] at this
                  norm_num at this
                  exact this
                have hexp_neg : Real.exp (-3) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
                rw [Real.sinh_eq]
                linarith only [he3, hexp_neg]
              linarith only [hsinh1, hsinh_le, h3]
            calc lam * (A + 1) ≤ lam * (M₀ + A + 1) := mul_le_mul_of_nonneg_left hA_le hlam_pos.le
              _ ≤ xiStar / 2 := hlam_xi
              _ ≤ 1 := by linarith only [hxi_le]
          calc 3 * (π / (4 * Real.sqrt 2)) * lam * (A + 1)
              = 3 * (π / (4 * Real.sqrt 2)) * (lam * (A + 1)) := by ring
            _ ≤ 3 * 1 * 1 := mul_le_mul (mul_le_mul_of_nonneg_left hpi4 (by norm_num)) hlam_1
                (mul_nonneg hlam_pos.le (by linarith only [hA_pos])) (by norm_num)
            _ = 3 := by ring
        calc 2 * φ' s ≤ 3 * Real.sqrt s + (3 * (π / (4 * Real.sqrt 2)) * lam * (A + 1)) * Real.sqrt s := by
              linarith only [hd]
          _ ≤ 3 * Real.sqrt s + 3 * Real.sqrt s :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg s))
          _ = 6 * Real.sqrt s := by ring
          _ ≤ 6 * Real.sqrt (A + 1) := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs_range.2) (by norm_num)
      have hlog_bd : |Real.log (|σ - s|)| ≤ R_tail := by
        have hdiff_lo : A / 4 ≤ s - σ := by linarith only [hσ_le, hs_range.1]
        have hdiff_hi : s - σ ≤ A + 1 + M₀ + 1 := by
          have := (abs_le.mp hσ_abs).1
          linarith only [this, hs_range.2]
        rw [show |σ - s| = s - σ by rw [abs_sub_comm, abs_of_pos (by linarith only [hA_pos, hdiff_lo])]]
        have h1 : Real.log (A / 4) ≤ Real.log (s - σ) := Real.log_le_log (by positivity) hdiff_lo
        have h2 : Real.log (s - σ) ≤ Real.log (A + 1 + M₀ + 1) := Real.log_le_log (by linarith only [hA_pos, hdiff_lo]) hdiff_hi
        have hab : |Real.log (s - σ)| ≤ max |Real.log (A / 4)| |Real.log (A + 1 + M₀ + 1)| := by
          rw [abs_le]
          refine ⟨le_trans (neg_le_neg (le_max_left _ _)) ?_, le_trans ?_ (le_max_right _ _)⟩
          · linarith only [neg_abs_le (Real.log (A / 4)), h1]
          · exact h2.trans (le_abs_self _)
        rw [hR_eq]; linarith only [hab]
      rw [abs_mul]
      exact mul_le_mul h2φ_bd hlog_bd (abs_nonneg _) (by positivity)
    have hneg_eq : -2 * (∫ s in A..Sa0, φ' s * Real.log |σ - s|) =
        -∫ s in A..Sa0, (2 * φ' s * Real.log |σ - s|) := by
      have h2 := intervalIntegral.integral_const_mul (μ := volume) (2 : ℝ) (fun s => φ' s * Real.log |σ - s|) (a := A) (b := Sa0)
      have h2' : ∫ s in A..Sa0, 2 * φ' s * Real.log |σ - s| = 2 * ∫ s in A..Sa0, φ' s * Real.log |σ - s| := by
        calc ∫ s in A..Sa0, 2 * φ' s * Real.log |σ - s|
            = ∫ s in A..Sa0, 2 * (φ' s * Real.log |σ - s|) := by
              refine intervalIntegral.integral_congr fun s _ => by ring
          _ = 2 * ∫ s in A..Sa0, φ' s * Real.log |σ - s| := h2
      rw [h2']; ring
    rw [hneg_eq, abs_neg, ← Real.norm_eq_abs]
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := A) (b := Sa0)
      (f := fun s => 2 * φ' s * Real.log |σ - s|) fun s hs => by
        rw [Real.norm_eq_abs]
        refine h_diff_int s ?_
        rcases Set.mem_uIoc.mp hs with h | h
        · exact Set.mem_uIcc.mpr (Or.inl ⟨h.1.le, h.2⟩)
        · exact Set.mem_uIcc.mpr (Or.inr ⟨h.1.le, h.2⟩)
    have hR_nn : 0 ≤ R_tail := by
      rw [hR_eq]
      exact add_nonneg (le_max_of_le_left (abs_nonneg _)) zero_le_one
    calc ‖∫ s in A..Sa0, 2 * φ' s * Real.log |σ - s|‖
        ≤ (6 * Real.sqrt (A + 1) * R_tail) * |Sa0 - A| := by simpa [Real.dist_eq, abs_sub_comm] using hnorm
      _ ≤ (6 * Real.sqrt (A + 1) * R_tail) * ((2 * c1K0 / 3) * A ^ 2 * lam) :=
          mul_le_mul_of_nonneg_left hSa0_diff (by positivity)
      _ ≤ ε / 6 := hlam_tail
  have hsplit_B : ∫ s in (0 : ℝ)..Sa0, φ' s * Real.log |σ - s| =
      (∫ s in (0 : ℝ)..A, φ' s * Real.log |σ - s|) + ∫ s in A..Sa0, φ' s * Real.log |σ - s| := by
    have h1 := hint_log_φ' (A + 1) (by positivity)
    have ha1 := h1.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc
      (Set.mem_uIcc.mpr (Or.inl ⟨hA_pos.le, by linarith only []⟩)))
    have ha2 := h1.mono_set (Set.uIcc_subset_uIcc
      (Set.mem_uIcc.mpr (Or.inl ⟨hA_pos.le, by linarith only []⟩))
      (Set.mem_uIcc.mpr (Or.inl ⟨hSa0_pos.le, hSa0_bds.2⟩)))
    exact (intervalIntegral.integral_add_adjacent_intervals ha1 ha2).symm
  rw [hcov, hsplit_B]
  rw [show -2 * ((∫ s in (0 : ℝ)..A, φ' s * Real.log |σ - s|) +
        ∫ s in A..Sa0, φ' s * Real.log |σ - s|) - continuumFQ A σ =
      (-2 * (∫ s in (0 : ℝ)..A, φ' s * Real.log |σ - s|) - continuumFQ A σ) +
      (-2 * (∫ s in A..Sa0, φ' s * Real.log |σ - s|)) by ring]
  exact (abs_add_le _ _).trans ((add_le_add hstepB1 hstepB2).trans_eq (by ring))

private lemma integral_phiVar_sub_continuumFQ {N₁ K₀ : ℕ} {S : ℝ}
    (hK₀ : 4 * N₁ + 6 ≤ K₀) (hS : 0 ≤ S) :
    ∀ ε > 0, ∃ C₀ > 0, ∀ {c' σ : ℝ}, C₀ ≤ c' →
      σ ∈ Icc (-S) (phiWKB (N₁ + 1)) →
      |(-2 * (∫ a in (1 / 4 : ℝ)..((K₀ : ℝ) + 1 / 2),
          (phiVar c' (xiStar + lambdaComb c' * σ) a - Real.log (π * lambdaComb c' / (2 * Real.sqrt 2))))) -
        continuumFQ (continuumAK K₀) σ| ≤ ε := by
  intro ε hε
  let a₀ : ℝ := (K₀ : ℝ) + 1 / 2
  have ha0_gt : (1 / 4 : ℝ) < a₀ := by dsimp [a₀]; linarith [Nat.cast_nonneg (α := ℝ) K₀]
  let A : ℝ := continuumAK K₀
  have hA_pos : 0 < A := continuumAK_pos K₀
  let M₀ : ℝ := max S (phiWKB (N₁ + 1))
  have hM₀ : 0 ≤ M₀ := le_max_of_le_left hS
  have hφ_le_A : phiWKB (N₁ + 1) ≤ A / 2 := by
    dsimp [A]; unfold phiWKB continuumAK
    have h4N : 4 * (((N₁ + 1 : ℕ) : ℝ) - 1 / 4) ≤ (K₀ : ℝ) + 1 / 4 := by
      have hK_r : 4 * (N₁ : ℝ) + 6 ≤ (K₀ : ℝ) := by exact_mod_cast hK₀
      push_cast; linarith
    have hbase : 0 ≤ ((N₁ + 1 : ℕ) : ℝ) - 1 / 4 := by
      have : (1 : ℝ) ≤ ((N₁ + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N₁ + 1)
      linarith
    have hpow4 : (2 : ℝ) ≤ (4 : ℝ) ^ (2 / 3 : ℝ) := by
      have h1 : ((2 : ℝ) ^ (3 : ℕ)) ≤ ((4 : ℝ) ^ (2 / 3 : ℝ)) ^ (3 : ℕ) := by
        have hr : ((4 : ℝ) ^ (2 / 3 : ℝ)) ^ (3 : ℕ) = 16 := by
          rw [← Real.rpow_natCast ((4 : ℝ) ^ (2 / 3 : ℝ)) 3, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
          norm_num
        rw [hr]; norm_num
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h1
    calc (((N₁ + 1 : ℕ) : ℝ) - 1 / 4) ^ (2 / 3 : ℝ)
        ≤ (4 : ℝ) ^ (2 / 3 : ℝ) / 2 * (((N₁ + 1 : ℕ) : ℝ) - 1 / 4) ^ (2 / 3 : ℝ) := by
          nlinarith [Real.rpow_nonneg hbase (2 / 3 : ℝ)]
      _ = (4 * (((N₁ + 1 : ℕ) : ℝ) - 1 / 4)) ^ (2 / 3 : ℝ) / 2 := by
          rw [Real.mul_rpow (by norm_num) hbase]; ring
      _ ≤ ((K₀ : ℝ) + 1 / 4) ^ (2 / 3 : ℝ) / 2 := by
          gcongr
  have hcont_log_tanh : ContinuousAt (fun t : ℝ => Real.log (Real.sqrt 2 * Real.tanh t)) (π * xiStar) := by
    have ht_pos : 0 < Real.sqrt 2 * Real.tanh (π * xiStar) := by
      rw [tanh_pi_mul_xiStar]; positivity
    exact ContinuousAt.comp (g := Real.log) (f := fun t : ℝ => Real.sqrt 2 * Real.tanh t)
      (Real.continuousAt_log ht_pos.ne') (continuousAt_const.mul continuous_tanh_real.continuousAt)
  obtain ⟨δ_t, hδt_pos, hδt⟩ := Metric.continuousAt_iff.mp hcont_log_tanh
    (ε / (12 * (a₀ - 1 / 4) + 1)) (by positivity)
  let C_I : ℝ := Real.sqrt (A + 1) * ((A + 1) * (A + 1 + M₀ + 1) + 8 * Real.sqrt (M₀ + (A + 1) + 1))
  have hCI_nn : 0 ≤ C_I := by dsimp [C_I]; positivity
  let R_tail : ℝ := max (|Real.log (A / 4)|) (|Real.log (A + 1 + M₀ + 1)|) + 1
  have h_small : ∀ᶠ c' : ℝ in atTop,
      0 < c' ∧
      lambdaComb c' * (M₀ + A + 1) ≤ xiStar / 2 ∧
      lambdaComb c' * a₀ ≤ 1 ∧
      (π * lambdaComb c' * (M₀ + A + 1)) ^ 2 / 2 * (2 * (a₀ - 1 / 4)) ≤ ε / 6 ∧
      (π / 2 * lambdaComb c' * (M₀ + A + 1)) < δ_t ∧
      (2 * c1K0 / 3) * A ^ 2 * lambdaComb c' ≤ min (A / 4) 1 ∧
      (3 * (π / (4 * Real.sqrt 2)) * lambdaComb c' * (A + 1)) * C_I ≤ ε / 6 ∧
      (6 * Real.sqrt (A + 1) * R_tail * ((2 * c1K0 / 3) * A ^ 2 * lambdaComb c')) ≤ ε / 6 := by
    have ht := tendsto_lambdaComb_atTop
    have h1 : ∀ᶠ c' : ℝ in atTop, (0 : ℝ) < c' := eventually_gt_atTop (0 : ℝ)
    have h2 : ∀ᶠ c' in atTop, lambdaComb c' * (M₀ + A + 1) ≤ xiStar / 2 := by
      have ht' : Tendsto (fun c' => lambdaComb c' * (M₀ + A + 1)) atTop (𝓝 0) := by
        simpa using ht.mul_const (M₀ + A + 1)
      exact ht'.eventually_le_const (half_pos xiStar_pos)
    have h3 : ∀ᶠ c' in atTop, lambdaComb c' * a₀ ≤ 1 := by
      have ht' : Tendsto (fun c' => lambdaComb c' * a₀) atTop (𝓝 0) := by
        simpa using ht.mul_const a₀
      exact ht'.eventually_le_const zero_lt_one
    have h4 : ∀ᶠ c' in atTop, (π * lambdaComb c' * (M₀ + A + 1)) ^ 2 / 2 * (2 * (a₀ - 1 / 4)) ≤ ε / 6 := by
      have ht' : Tendsto (fun c' : ℝ => (π * lambdaComb c' * (M₀ + A + 1)) ^ 2 / 2 * (2 * (a₀ - 1 / 4)))
          atTop (𝓝 0) := by
        simpa using ((((ht.const_mul π).mul_const (M₀ + A + 1)).pow 2).div_const 2).mul_const (2 * (a₀ - 1 / 4))
      exact ht'.eventually_le_const (by linarith)
    have h5 : ∀ᶠ c' in atTop, (π / 2 * lambdaComb c' * (M₀ + A + 1)) < δ_t := by
      have ht' : Tendsto (fun c' : ℝ => π / 2 * lambdaComb c' * (M₀ + A + 1)) atTop (𝓝 0) := by
        simpa using ((ht.const_mul (π / 2)).mul_const (M₀ + A + 1))
      exact ht'.eventually_lt_const hδt_pos
    have h6 : ∀ᶠ c' in atTop, (2 * c1K0 / 3) * A ^ 2 * lambdaComb c' ≤ min (A / 4) 1 := by
      have ht' : Tendsto (fun c' : ℝ => (2 * c1K0 / 3) * A ^ 2 * lambdaComb c') atTop (𝓝 0) := by
        simpa using ht.const_mul ((2 * c1K0 / 3) * A ^ 2)
      exact ht'.eventually_le_const (lt_min (by positivity) zero_lt_one)
    have h7 : ∀ᶠ c' in atTop, (3 * (π / (4 * Real.sqrt 2)) * lambdaComb c' * (A + 1)) * C_I ≤ ε / 6 := by
      have ht' : Tendsto (fun c' : ℝ =>
          (3 * (π / (4 * Real.sqrt 2)) * lambdaComb c' * (A + 1)) * C_I) atTop (𝓝 0) := by
        simpa using (((ht.const_mul (3 * (π / (4 * Real.sqrt 2)))).mul_const (A + 1)).mul_const C_I)
      exact ht'.eventually_le_const (by linarith)
    have h8 : ∀ᶠ c' in atTop, (6 * Real.sqrt (A + 1) * R_tail * ((2 * c1K0 / 3) * A ^ 2 * lambdaComb c')) ≤ ε / 6 := by
      have ht' : Tendsto (fun c' : ℝ =>
          (6 * Real.sqrt (A + 1) * R_tail * ((2 * c1K0 / 3) * A ^ 2 * lambdaComb c'))) atTop (𝓝 0) := by
        simpa using (ht.const_mul ((2 * c1K0 / 3) * A ^ 2)).const_mul (6 * Real.sqrt (A + 1) * R_tail)
      exact ht'.eventually_le_const (by linarith)
    exact h1.and (h2.and (h3.and (h4.and (h5.and (h6.and (h7.and h8))))))
  obtain ⟨C₀, hC₀⟩ := eventually_atTop.mp h_small
  refine ⟨max C₀ 1, by positivity, fun {c' σ} hc' hσ => ?_⟩
  obtain ⟨hc'_pos, hlam_xi, hlam_a0, hlam_z1, hlam_dt, hlam_sa0, hlam_jac, hlam_tail⟩ :=
    hC₀ c' ((le_max_left _ _).trans hc')
  set lam := lambdaComb c'
  have hlam_pos : 0 < lam := lambdaComb_pos hc'_pos
  set P₀ : ℝ := π * lam / (2 * Real.sqrt 2)
  have hP₀_pos : 0 < P₀ := by dsimp [P₀]; positivity
  set x : ℝ := xiStar + lam * σ
  have hσ_abs : |σ| ≤ M₀ := by
    have h1 : phiWKB (N₁ + 1) ≤ M₀ := le_max_right _ _
    have h2 : -M₀ ≤ -S := neg_le_neg (le_max_left _ _)
    exact abs_le.mpr ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hx_nn : 0 ≤ x := by
    have := (abs_le.mp hσ_abs).1
    have : lam * M₀ ≤ xiStar / 2 := by nlinarith
    dsimp [x]; nlinarith only [xiStar_pos, hlam_pos, (abs_le.mp hσ_abs).1, this]
  set Sa0 : ℝ := siteRadius c' a₀ / lam
  have hSa0_diff : |Sa0 - A| ≤ (2 * c1K0 / 3) * A ^ 2 * lam := by
    have hsr := siteRadius_asymptotic hc'_pos ha0_gt.le
    have hphi_a0 : phiQuantile a₀ = A := by
      unfold phiQuantile A continuumAK a₀
      congr 1; ring
    rw [hphi_a0] at hsr
    rw [show Sa0 - A = (siteRadius c' a₀ - lam * A) / lam by dsimp [Sa0]; field_simp [hlam_pos.ne'],
      abs_div, abs_of_pos hlam_pos, div_le_iff₀ hlam_pos]
    calc |siteRadius c' a₀ - lam * A| ≤ (2 * c1K0 / 3) * (lam * A) ^ 2 := hsr
      _ = (2 * c1K0 / 3) * A ^ 2 * lam * lam := by ring
  have hSa0_bds : 3 / 4 * A ≤ Sa0 ∧ Sa0 ≤ A + 1 := by
    have h1 := abs_le.mp (hSa0_diff.trans hlam_sa0)
    have hmin1 := h1.1
    have hmin2 := h1.2
    have h1' : -(A / 4) ≤ Sa0 - A := by linarith [min_le_left (A / 4) 1]
    have h2' : Sa0 - A ≤ 1 := by linarith [min_le_right (A / 4) 1]
    constructor <;> linarith
  have hSa0_pos : 0 < Sa0 := by linarith
  have hσa_le : ∀ a ∈ Ioc (1 / 4 : ℝ) a₀, 0 ≤ siteRadius c' a / lam ∧ siteRadius c' a / lam ≤ Sa0 := by
    intro a ha
    have hmono : xiStar ≤ chiQuantile c' a ∧ chiQuantile c' a ≤ chiQuantile c' a₀ :=
      ⟨(chiQuantile_spec hc'_pos ha.1.le).1,
        (chiQuantile_strictMonoOn hc'_pos).monotoneOn (Set.mem_Ici.mpr ha.1.le)
          (Set.mem_Ici.mpr ha0_gt.le) ha.2⟩
    dsimp [Sa0]
    unfold siteRadius at *
    constructor
    · exact div_nonneg (by linarith only [hmono.1]) hlam_pos.le
    · exact div_le_div_of_nonneg_right (by linarith only [hmono.2]) hlam_pos.le
  -- Step A: `phiVar c' x a - log P₀` vs `log |σ - siteRadius c' a / lam|` a.e. on `Ioc (1/4) a₀`
  have hae_ne : ∀ᵐ a ∂(volume.restrict (Ioc (1 / 4 : ℝ) a₀)), chiQuantile c' a ≠ x := by
    have hsub : Set.Subsingleton {a ∈ Ioc (1 / 4 : ℝ) a₀ | chiQuantile c' a = x} := by
      intro a ha b hb
      exact (chiQuantile_strictMonoOn hc'_pos).injOn (Set.mem_Ici.mpr ha.1.1.le)
        (Set.mem_Ici.mpr hb.1.1.le) (ha.2.trans hb.2.symm)
    have hzero : volume {a ∈ Ioc (1 / 4 : ℝ) a₀ | chiQuantile c' a = x} = 0 :=
      hsub.countable.measure_zero _
    rw [ae_restrict_iff' measurableSet_Ioc]
    have hm : {a ∈ Ioc (1 / 4 : ℝ) a₀ | chiQuantile c' a = x}ᶜ ∈ ae volume := by
      rw [mem_ae_iff, compl_compl]; exact hzero
    filter_upwards [hm] with a ha ha_mem
    intro heq
    exact ha ⟨ha_mem, heq⟩
  have h_pt_err : ∀ a ∈ Ioc (1 / 4 : ℝ) a₀, chiQuantile c' a ≠ x →
      |((phiVar c' x a - Real.log P₀) - Real.log (|σ - siteRadius c' a / lam|))| ≤
        (π * lam * (M₀ + A + 1)) ^ 2 / 2 + ε / (12 * (a₀ - 1 / 4) + 1) := by
    intro a ha hne
    set σa := siteRadius c' a / lam
    have hσa_bd := hσa_le a ha
    have hχa_eq : chiQuantile c' a = xiStar + lam * σa := by
      dsimp [σa]; unfold siteRadius; field_simp [hlam_pos.ne']; ring
    have hχa_nn : 0 ≤ chiQuantile c' a := xiStar_pos.le.trans (chiQuantile_spec hc'_pos ha.1.le).1
    have hphi_eq : phiVar c' x a =
        Real.log (|Real.tanh (π * (x - chiQuantile c' a) / 2)| * Real.tanh (π * (x + chiQuantile c' a) / 2)) := by
      unfold phiVar realLogT
      rw [blaschkeT_ofReal_eq, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      have ht2_pos : 0 < Real.tanh (π * (x + chiQuantile c' a) / 2) := by
        have hsum : 0 < x + chiQuantile c' a := by
          have : 0 < chiQuantile c' a := xiStar_pos.trans (xiStar_lt_chiQuantile hc'_pos ha.1)
          linarith
        rw [Real.tanh_eq_sinh_div_cosh]
        exact div_pos (Real.sinh_pos_iff.mpr (by positivity)) (Real.cosh_pos _)
      rw [abs_of_pos ht2_pos]
    set z₁ := π * (x - chiQuantile c' a) / 2
    set z₂ := π * (x + chiQuantile c' a) / 2
    have hz₁_ne : z₁ ≠ 0 := by
      dsimp [z₁]; exact div_ne_zero (mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr hne.symm)) two_ne_zero
    have hz₁_eq : z₁ = (π * lam / 2) * (σ - σa) := by
      dsimp [z₁, x]; rw [hχa_eq]; ring
    have ht1_pos : 0 < |Real.tanh z₁| := by
      rw [abs_pos, Real.tanh_eq_sinh_div_cosh]
      exact div_ne_zero (Real.sinh_ne_zero.mpr hz₁_ne) (Real.cosh_pos _).ne'
    have ht2_pos : 0 < Real.tanh z₂ := by
      have : 0 < x + chiQuantile c' a := by
        have := xiStar_pos.trans (xiStar_lt_chiQuantile hc'_pos ha.1)
        linarith
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr (by dsimp [z₂]; positivity)) (Real.cosh_pos _)
    have hlog_split : phiVar c' x a - Real.log P₀ - Real.log |σ - σa| =
        Real.log (|Real.tanh z₁| / |z₁|) + Real.log (Real.sqrt 2 * Real.tanh z₂) := by
      have hne_σ : σ - σa ≠ 0 := by
        intro h
        apply hne
        rw [hχa_eq, show x = xiStar + lam * σ by rfl, show σ = σa by linarith]
      have hz_abs : |z₁| = (π * lam / 2) * |σ - σa| := by
        rw [hz₁_eq, abs_mul, abs_of_pos (by positivity : 0 < π * lam / 2)]
      have hid_mul : |Real.tanh z₁| * Real.tanh z₂ =
          P₀ * |σ - σa| * (|Real.tanh z₁| / |z₁|) * (Real.sqrt 2 * Real.tanh z₂) := by
        rw [hz_abs]
        have hsqrt2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr two_pos).ne'
        dsimp [P₀]
        field_simp [Real.pi_ne_zero, hlam_pos.ne', hsqrt2, (abs_pos.mpr hne_σ).ne']
      rw [hphi_eq, hid_mul,
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul hP₀_pos.ne' (abs_pos.mpr hne_σ).ne']
      ring
    rw [hlog_split]
    have hterm1 : |Real.log (|Real.tanh z₁| / |z₁|)| ≤ (π * lam * (M₀ + A + 1)) ^ 2 / 2 := by
      have hb1 : |Real.tanh z₁| / |z₁| ≤ 1 := by
        rw [div_le_one (abs_pos.mpr hz₁_ne)]
        exact abs_tanh_le_abs z₁
      -- standard bound `z₁^2 / 2` via `1 - z₁^2/2` or `Real.tanh`:
      have ht_ge : 1 / Real.cosh |z₁| ≤ |Real.tanh z₁| / |z₁| := by
        have ht_abs : |Real.tanh z₁| = Real.tanh |z₁| := by
          rcases le_total 0 z₁ with hz | hz
          · have htnn : 0 ≤ Real.tanh z₁ := by
              rw [Real.tanh_eq_sinh_div_cosh]
              exact div_nonneg (Real.sinh_nonneg_iff.mpr hz) (Real.cosh_pos _).le
            rw [abs_of_nonneg htnn, abs_of_nonneg hz]
          · have htnp : Real.tanh z₁ ≤ 0 := by
              rw [Real.tanh_eq_sinh_div_cosh]
              exact div_nonpos_of_nonpos_of_nonneg (Real.sinh_nonpos_iff.mpr hz) (Real.cosh_pos _).le
            rw [abs_of_nonpos htnp, abs_of_nonpos hz, Real.tanh_neg]
        rw [ht_abs, Real.tanh_eq_sinh_div_cosh, div_div,
          div_le_div_iff₀ (Real.cosh_pos _) (mul_pos (Real.cosh_pos _) (abs_pos.mpr hz₁_ne))]
        have hsinh_ge : |z₁| ≤ Real.sinh |z₁| := by
          let k : ℝ → ℝ := fun t => Real.sinh t - t
          have hk : ∀ t, HasDerivAt k (Real.cosh t - 1) t :=
            fun t => (Real.hasDerivAt_sinh t).sub (hasDerivAt_id t)
          have hkm : Monotone k := monotone_of_deriv_nonneg (fun t => (hk t).differentiableAt)
            fun t => by rw [(hk t).deriv]; exact sub_nonneg.mpr (Real.one_le_cosh t)
          have h0 := hkm (abs_nonneg z₁)
          dsimp [k] at h0; simp only [Real.sinh_zero, sub_zero] at h0
          linarith
        calc 1 * (Real.cosh |z₁| * |z₁|) = Real.cosh |z₁| * |z₁| := one_mul _
          _ ≤ Real.cosh |z₁| * Real.sinh |z₁| := mul_le_mul_of_nonneg_left hsinh_ge (Real.cosh_pos _).le
          _ = Real.sinh |z₁| * Real.cosh |z₁| := by ring
      have hlog_cosh : Real.log (Real.cosh |z₁|) ≤ |z₁| ^ 2 / 2 := by
        let k : ℝ → ℝ := fun t => t ^ 2 / 2 - Real.log (Real.cosh t)
        have hk : ∀ t, HasDerivAt k (t - Real.tanh t) t := fun t => by
          have h1 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) t t := by
            simpa using ((hasDerivAt_pow 2 t).div_const 2).congr_deriv (by ring)
          have h2 : HasDerivAt (fun y : ℝ => Real.log (Real.cosh y)) (Real.tanh t) t := by
            exact ((Real.hasDerivAt_log (Real.cosh_pos t).ne').comp t (Real.hasDerivAt_cosh t)).congr_deriv (by
              rw [Real.tanh_eq_sinh_div_cosh]; ring)
          exact h1.sub h2
        have hkm : MonotoneOn k (Set.Ici 0) := monotoneOn_of_deriv_nonneg (convex_Ici 0)
          (fun t _ => (hk t).continuousAt.continuousWithinAt)
          (fun t _ => (hk t).differentiableAt.differentiableWithinAt)
          fun t ht => by
            rw [(hk t).deriv]
            have := (abs_le.mp (abs_tanh_le_abs t)).2
            rw [abs_of_nonneg (Set.mem_Ici.mp (interior_subset ht))] at this
            linarith
        have h0 := hkm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (abs_nonneg z₁)) (abs_nonneg z₁)
        dsimp [k] at h0; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
          Real.cosh_zero, Real.log_one, sub_self] at h0
        linarith
      have h_bd : |Real.log (|Real.tanh z₁| / |z₁|)| ≤ z₁ ^ 2 / 2 := by
        have hle0 : Real.log (|Real.tanh z₁| / |z₁|) ≤ 0 :=
          Real.log_nonpos (div_pos ht1_pos (abs_pos.mpr hz₁_ne)).le hb1
        have hge0 : -(z₁ ^ 2 / 2) ≤ Real.log (|Real.tanh z₁| / |z₁|) := by
          have h1 := Real.log_le_log (one_div_pos.mpr (Real.cosh_pos |z₁|)) ht_ge
          rw [one_div, Real.log_inv] at h1
          rw [sq_abs] at hlog_cosh
          linarith
        rw [abs_of_nonpos hle0]; linarith
      have hz1_le : |z₁| ≤ π * lam * (M₀ + A + 1) := by
        rw [hz₁_eq, abs_mul, abs_of_pos (by positivity : 0 < π * lam / 2)]
        have hdif : |σ - σa| ≤ M₀ + A + 1 := by
          calc |σ - σa| ≤ |σ| + |σa| := abs_sub _ _
            _ ≤ M₀ + (A + 1) := add_le_add hσ_abs (by rw [abs_of_nonneg hσa_bd.1]; linarith [hSa0_bds.2])
            _ = M₀ + A + 1 := by ring
        calc (π * lam / 2) * |σ - σa| ≤ (π * lam / 2) * (M₀ + A + 1) :=
              mul_le_mul_of_nonneg_left hdif (by positivity)
          _ ≤ π * lam * (M₀ + A + 1) := by
              have hnn : 0 ≤ π * lam * (M₀ + A + 1) := by positivity
              linarith
      have hz1_sq : z₁ ^ 2 ≤ (π * lam * (M₀ + A + 1)) ^ 2 := by
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hz1_le 2
      linarith [h_bd, hz1_sq]
    have hterm2 : |Real.log (Real.sqrt 2 * Real.tanh z₂)| ≤ ε / (12 * (a₀ - 1 / 4) + 1) := by
      have hz2_dist : dist z₂ (π * xiStar) < δ_t := by
        rw [Real.dist_eq, show z₂ - π * xiStar = (π * lam / 2) * (σ + σa) by
          dsimp [z₂, x]; rw [hχa_eq]; ring, abs_mul, abs_of_pos (by positivity : 0 < π * lam / 2)]
        have hsum_le : |σ + σa| ≤ M₀ + A + 1 := by
          calc |σ + σa| ≤ |σ| + |σa| := abs_add_le _ _
            _ ≤ M₀ + (A + 1) := add_le_add hσ_abs (by rw [abs_of_nonneg hσa_bd.1]; linarith [hSa0_bds.2])
            _ = M₀ + A + 1 := by ring
        calc (π * lam / 2) * |σ + σa| ≤ (π * lam / 2) * (M₀ + A + 1) :=
              mul_le_mul_of_nonneg_left hsum_le (by positivity)
          _ = π / 2 * lam * (M₀ + A + 1) := by ring
          _ < δ_t := hlam_dt
      have hd := (hδt hz2_dist).le
      rw [Real.dist_eq, show Real.sqrt 2 * Real.tanh (π * xiStar) = 1 by
        rw [tanh_pi_mul_xiStar]; field_simp [(Real.sqrt_pos.mpr two_pos).ne'], Real.log_one, sub_zero] at hd
      exact hd
    exact (abs_add_le _ _).trans (add_le_add hterm1 hterm2)
  -- Step B: Change of variables `a(s) = 1/4 + c' * cumulN (xiStar + lam * s)` on `Ioo 0 Sa0`
  obtain ⟨hint_σa, hstepB⟩ := stepB_integral_bound hc'_pos ha0_gt hA_pos hM₀
    (hσ.2.trans hφ_le_A) hσ_abs rfl hSa0_diff hSa0_bds hlam_xi hlam_jac hlam_tail rfl rfl
  have hint_phi : IntervalIntegrable (phiVar c' x) volume (1 / 4) a₀ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha0_gt.le).mpr
      ((riesz_real_identities hc'_pos hx_nn 1 le_rfl).2.1.mono_set Set.Ioc_subset_Ioi_self)
  have hstepA : |-2 * (∫ a in (1 / 4 : ℝ)..a₀, (phiVar c' x a - Real.log P₀)) -
      (-2 * (∫ a in (1 / 4 : ℝ)..a₀, Real.log |σ - siteRadius c' a / lam|))| ≤ ε / 3 :=
    stepA_integral_bound (sub_pos.mpr ha0_gt) hε.le hint_phi hint_σa hae_ne h_pt_err hlam_z1
  have hid : -2 * (∫ a in (1 / 4 : ℝ)..a₀, (phiVar c' x a - Real.log P₀)) - continuumFQ A σ =
      (-2 * (∫ a in (1 / 4 : ℝ)..a₀, (phiVar c' x a - Real.log P₀)) -
        (-2 * (∫ a in (1 / 4 : ℝ)..a₀, Real.log |σ - siteRadius c' a / lam|))) +
      (-2 * (∫ a in (1 / 4 : ℝ)..a₀, Real.log |σ - siteRadius c' a / lam|) - continuumFQ A σ) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans ((add_le_add hstepA hstepB).trans (by linarith only [hε]))

/-! ### Section 5: Main Window Limit (`ut:W`) and Design Instantiation -/

private lemma prod_sub_prod_bound {ι : Type*} [DecidableEq ι] (s : Finset ι) {f g : ι → ℝ} {B δ : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hf : ∀ i ∈ s, |f i| ≤ B) (hg : ∀ i ∈ s, |g i| ≤ B) (hfg : ∀ i ∈ s, |f i - g i| ≤ δ) :
    |∏ i ∈ s, f i - ∏ i ∈ s, g i| ≤ (s.card : ℝ) * B ^ (s.card - 1) * δ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s' ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have hf' : ∀ i ∈ s', |f i| ≤ B := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' : ∀ i ∈ s', |g i| ≤ B := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hfg' : ∀ i ∈ s', |f i - g i| ≤ δ := fun i hi => hfg i (Finset.mem_insert_of_mem hi)
    have ih' := ih hf' hg' hfg'
    have h_prod_g : |∏ i ∈ s', g i| ≤ B ^ s'.card := by
      rw [Finset.abs_prod]
      calc ∏ i ∈ s', |g i| ≤ ∏ _i ∈ s', B := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) hg'
        _ = B ^ s'.card := by simp [Finset.prod_const]
    have hid : f a * (∏ i ∈ s', f i) - g a * (∏ i ∈ s', g i) =
        (f a - g a) * (∏ i ∈ s', g i) + f a * (∏ i ∈ s', f i - ∏ i ∈ s', g i) := by ring
    rw [hid]
    have ha_f := hf a (Finset.mem_insert_self a s')
    have ha_fg := hfg a (Finset.mem_insert_self a s')
    have ht1 : |(f a - g a) * ∏ i ∈ s', g i| ≤ δ * B ^ s'.card := by
      rw [abs_mul]; exact mul_le_mul ha_fg h_prod_g (abs_nonneg _) hδ
    have ht2 : |f a * (∏ i ∈ s', f i - ∏ i ∈ s', g i)| ≤
        (s'.card : ℝ) * B ^ s'.card * δ := by
      rw [abs_mul]
      calc |f a| * |∏ i ∈ s', f i - ∏ i ∈ s', g i|
          ≤ B * ((s'.card : ℝ) * B ^ (s'.card - 1) * δ) :=
            mul_le_mul ha_f ih' (abs_nonneg _) hB
        _ = (s'.card : ℝ) * (B * B ^ (s'.card - 1)) * δ := by ring
        _ ≤ (s'.card : ℝ) * B ^ s'.card * δ := by
            cases hs0 : s'.card with
            | zero => simp
            | succ m =>
                have : B * B ^ (m + 1 - 1) = B ^ (m + 1) := by simp [pow_succ']
                rw [this]
    have hsum := (abs_add_le _ _).trans (add_le_add ht1 ht2)
    rw [Nat.add_sub_cancel]
    push_cast
    linarith [hsum]

lemma compactFamily_tildeW_bound {f N K_min : ℕ} (𝒦 : CompactCombFamily f N)
    {C_W S_win : ℝ} (hS_win : 0 ≤ S_win) (hKmin_N : N ≤ K_min) (hKmin_1 : 1 ≤ K_min)
    (hCW_pos : 0 < C_W)
    (hW_rate : ∀ {σf : ℝ} {σSeq εHat : ℕ → ℝ},
      |σf| ≤ max 𝒦.M 1 →
      (∀ k ∈ Finset.Icc (f + 1) N, |σSeq k| ≤ max 𝒦.M 1 ∧ |εHat k| ≤ max 𝒦.M 1) →
      (∀ k : ℕ, N < k →
        |σSeq k - phiWKB k| ≤ 1 * (k : ℝ) ^ (-(4 / 3 : ℝ)) ∧ |εHat k| ≤ 1 * (k : ℝ) ^ (-(1 / 3 : ℝ))) →
      (∀ {K₁ K₂ : ℕ} {σ : ℝ}, K_min ≤ K₁ → K₁ ≤ K₂ → σ ∈ Icc (-S_win) S_win →
        |windowFiniteProd f σf σSeq εHat K₂ σ - windowFiniteProd f σf σSeq εHat K₁ σ| ≤ C_W / (K₁ : ℝ)) ∧
      (∀ {K : ℕ} {σ : ℝ}, K_min ≤ K → σ ∈ Icc (-S_win) S_win →
        |windowFiniteProd f σf σSeq εHat K σ - tildeW f σf σSeq εHat σ| ≤ C_W / (K : ℝ))) :
    ∃ B_W > 0, ∀ d ∈ 𝒦.members, ∀ σ ∈ Icc (-S_win) S_win,
      |tildeW f d.sigmaFLim d.allSigmaLim d.allEpsLim σ| ≤ B_W := by
  let M_lim : ℝ := max 𝒦.M 1
  have hfN : f ≤ N := 𝒦.hN
  have hcont_fq := continuous_continuumFQ (continuumAK K_min) (continuumAK_nonneg K_min)
  obtain ⟨B_fq, _, hB_fq⟩ : ∃ B_fq : ℝ, 0 ≤ B_fq ∧ ∀ σ ∈ Icc (-S_win) S_win,
      |continuumFQ (continuumAK K_min) σ| ≤ B_fq := by
    obtain ⟨σ₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (⟨0, by simp [hS_win]⟩ : (Icc (-S_win) S_win).Nonempty)
      (continuous_abs.comp hcont_fq).continuousOn
    exact ⟨max 0 |continuumFQ (continuumAK K_min) σ₀|, le_max_left _ _,
      fun σ hσ => (hmax hσ).trans (le_max_right _ _)⟩
  let B_K : ℝ := Real.exp B_fq * (S_win + M_lim) * (((S_win + M_lim) ^ 2 + M_lim ^ 2) ^ (N - f)) *
    (∏ k ∈ Finset.Icc (N + 1) K_min, ((S_win + phiWKB k + 1) ^ 2 + 1))
  refine ⟨B_K + C_W + 1, by positivity, fun d hd σ hσ => ?_⟩
  have hd_lim := 𝒦.lim_bounds d hd
  have hrate_d := (hW_rate (σf := d.sigmaFLim) (σSeq := d.allSigmaLim) (εHat := d.allEpsLim)
    ((hd_lim.1).trans (le_max_left _ _))
    (fun k hk => by
      have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
      simp only [ModifiedCombData.allSigmaLim, ModifiedCombData.allEpsLim, hkN, ↓reduceIte]
      have hk' := hd_lim.2 k hk
      exact ⟨hk'.1.trans (le_max_left _ _), by rw [abs_of_nonneg hk'.2.1]; exact hk'.2.2.trans (le_max_left _ _)⟩)
    (d.tail_bound_all (𝒦.eta0_bounds d hd).1 (𝒦.eta0_bounds d hd).2)).2
    le_rfl hσ
  have hMK_bd : |windowFiniteProd f d.sigmaFLim d.allSigmaLim d.allEpsLim K_min σ| ≤ B_K := by
    unfold windowFiniteProd
    have hexp_le : continuumFQ (continuumAK K_min) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) ≤ B_fq := by
      have h1 := (le_abs_self _).trans (hB_fq σ hσ)
      have : 0 ≤ 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) := by positivity
      linarith
    have hσ_abs : |σ| ≤ S_win := abs_le.mpr hσ
    have hlin : |σ - d.sigmaFLim| ≤ S_win + M_lim :=
      (abs_sub _ _).trans (add_le_add hσ_abs ((hd_lim.1).trans (le_max_left _ _)))
    have hIcc : Finset.Icc (f + 1) K_min = Finset.Icc (f + 1) N ∪ Finset.Icc (N + 1) K_min := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc (f + 1) N) (Finset.Icc (N + 1) K_min) := by
      rw [Finset.disjoint_left]; intro k hk1 hk2; simp only [Finset.mem_Icc] at hk1 hk2; omega
    have hp1 : |∏ k ∈ Finset.Icc (f + 1) N, ((σ - d.allSigmaLim k) ^ 2 + (d.allEpsLim k) ^ 2)| ≤
        ((S_win + M_lim) ^ 2 + M_lim ^ 2) ^ (N - f) := by
      rw [abs_of_nonneg (Finset.prod_nonneg fun _ _ => by positivity)]
      calc ∏ k ∈ Finset.Icc (f + 1) N, _
          ≤ ∏ _k ∈ Finset.Icc (f + 1) N, ((S_win + M_lim) ^ 2 + M_lim ^ 2) := by
            refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun k hk => ?_
            have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
            simp only [ModifiedCombData.allSigmaLim, ModifiedCombData.allEpsLim, hkN, ↓reduceIte]
            have hk' := hd_lim.2 k hk
            have h1 : |σ - d.sigmaKLim k| ≤ S_win + M_lim :=
              (abs_sub _ _).trans (add_le_add hσ_abs (hk'.1.trans (le_max_left _ _)))
            have h2 : (σ - d.sigmaKLim k) ^ 2 ≤ (S_win + M_lim) ^ 2 := by
              simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h1 2
            have h3 : d.epsHatLim k ^ 2 ≤ M_lim ^ 2 :=
              pow_le_pow_left₀ hk'.2.1 (hk'.2.2.trans (le_max_left _ _)) 2
            linarith
        _ = _ := by
            rw [Finset.prod_const, Nat.card_Icc, show N + 1 - (f + 1) = N - f by omega]
    have hp2 : |∏ k ∈ Finset.Icc (N + 1) K_min, ((σ - d.allSigmaLim k) ^ 2 + (d.allEpsLim k) ^ 2)| ≤
        ∏ k ∈ Finset.Icc (N + 1) K_min, ((S_win + phiWKB k + 1) ^ 2 + 1) := by
      rw [abs_of_nonneg (Finset.prod_nonneg fun _ _ => by positivity)]
      refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun k hk => ?_
      have hkN : ¬ k ≤ N := by simp only [Finset.mem_Icc] at hk; omega
      have ht := d.tail_bound_all (𝒦.eta0_bounds d hd).1 (𝒦.eta0_bounds d hd).2 k (by omega)
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
      have hkr13 : (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 := by
        rw [Real.rpow_neg (by positivity)]; exact inv_le_one_of_one_le₀ (Real.one_le_rpow hk1 (by norm_num))
      have hkr43 : (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 := by
        rw [Real.rpow_neg (by positivity)]; exact inv_le_one_of_one_le₀ (Real.one_le_rpow hk1 (by norm_num))
      have hs1 : |σ - d.allSigmaLim k| ≤ S_win + phiWKB k + 1 := by
        have hphi_nn : 0 ≤ phiWKB k := by
          unfold phiWKB
          exact Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 1 / 4) _
        have : |d.allSigmaLim k| ≤ phiWKB k + 1 := by
          have := abs_sub_abs_le_abs_sub (d.allSigmaLim k) (phiWKB k)
          rw [abs_of_nonneg hphi_nn] at this; nlinarith [ht.1]
        exact (abs_sub _ _).trans (by linarith)
      have hs2 : (σ - d.allSigmaLim k) ^ 2 ≤ (S_win + phiWKB k + 1) ^ 2 := by
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hs1 2
      have he2 : (d.allEpsLim k) ^ 2 ≤ 1 := by
        have : |d.allEpsLim k| ≤ 1 := by nlinarith [ht.2]
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) this 2
      linarith
    rw [hIcc, Finset.prod_union hdisj, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), ← mul_assoc]
    have hm1 := mul_le_mul (Real.exp_le_exp.mpr hexp_le) hlin (abs_nonneg _) (Real.exp_pos _).le
    have hm2 := mul_le_mul hm1 hp1 (abs_nonneg _) (by positivity)
    exact (mul_le_mul hm2 hp2 (abs_nonneg _) (by positivity)).trans_eq rfl
  have hKmin_ge1 : (1 : ℝ) ≤ (K_min : ℝ) := by exact_mod_cast hKmin_1
  have hCW_le : C_W / (K_min : ℝ) ≤ C_W := div_le_self hCW_pos.le hKmin_ge1
  have h_abs_diff := abs_sub_abs_le_abs_sub (tildeW f d.sigmaFLim d.allSigmaLim d.allEpsLim σ)
    (windowFiniteProd f d.sigmaFLim d.allSigmaLim d.allEpsLim K_min σ)
  have hcomm : |tildeW f d.sigmaFLim d.allSigmaLim d.allEpsLim σ -
      windowFiniteProd f d.sigmaFLim d.allSigmaLim d.allEpsLim K_min σ| =
      |windowFiniteProd f d.sigmaFLim d.allSigmaLim d.allEpsLim K_min σ -
      tildeW f d.sigmaFLim d.allSigmaLim d.allEpsLim σ| := abs_sub_comm _ _
  linarith [h_abs_diff, hrate_d, hMK_bd, hCW_le, hcomm]

/-- `W̃^{±(f)}` is bounded on `[-S, S]` uniformly over a compact family
(the bound used inside `lemma_W_measure`). -/
theorem CompactCombFamily.tildeW_bound {f N : ℕ} (𝒦 : CompactCombFamily f N) {S : ℝ} (hS : 0 ≤ S) :
    ∃ B > 0, ∀ d ∈ 𝒦.members, ∀ σ ∈ Icc (-S) S,
      |tildeW f d.sigmaFLim d.allSigmaLim d.allEpsLim σ| ≤ B := by
  obtain ⟨K_min, C_W, hKmin_N, hKmin_1, hCW_pos, hW_rate⟩ :=
    tendsto_windowFiniteProd_uniform f N 𝒦.hf 𝒦.hN (M := max 𝒦.M 1) (C_t := 1) (S := S)
      (by have := 𝒦.hM; positivity) zero_lt_one hS
  exact compactFamily_tildeW_bound 𝒦 hS hKmin_N hKmin_1 hCW_pos hW_rate

private lemma eta_diff_eq (eta0 s1 s0 lam p1 p0 : ℝ) (hlam : lam ≠ 0) :
    eta0 * ((s1 - s0) / lam) - eta0 * (p1 - p0) =
      eta0 * ((s1 / lam - p1) - (s0 / lam - p0)) := by
  field_simp [hlam]; ring

private lemma min_one_div_half_le (δ M : ℝ) (hδ : 0 ≤ δ) (hM : 0 ≤ M) :
    (1 / 2 : ℝ) * min 1 (δ / (36 * (M + 1) + 12)) ≤ min 1 (δ / (18 * (M + 1) + 6)) ∧
      min 1 (δ / (36 * (M + 1) + 12)) ≤ min 1 (δ / (18 * (M + 1) + 6)) := by
  have hden1 : (0 : ℝ) < 18 * (M + 1) + 6 := by linarith
  have hden2 : 18 * (M + 1) + 6 ≤ 36 * (M + 1) + 12 := by linarith
  have hle : δ / (36 * (M + 1) + 12) ≤ δ / (18 * (M + 1) + 6) :=
    div_le_div_of_nonneg_left hδ hden1 hden2
  have hmin : min 1 (δ / (36 * (M + 1) + 12)) ≤ min 1 (δ / (18 * (M + 1) + 6)) :=
    min_le_min le_rfl hle
  refine ⟨?_, hmin⟩
  rw [le_min_iff]
  refine ⟨(mul_le_of_le_one_right (by norm_num) (min_le_left _ _)).trans (by norm_num), ?_⟩
  calc (1 / 2 : ℝ) * min 1 (δ / (36 * (M + 1) + 12))
      ≤ (1 / 2 : ℝ) * (δ / (36 * (M + 1) + 12)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
    _ ≤ 1 * (δ / (18 * (M + 1) + 6)) := mul_le_mul (by norm_num) hle (by positivity) (by norm_num)
    _ = δ / (18 * (M + 1) + 6) := one_mul _

private lemma pairMod_window_err_step {c' η₀ σ δ_q M_all C_Q : ℝ} {K₀ k : ℕ}
    (hk1 : 1 ≤ k) (hk_le : k ≤ K₀) (hc'_pos : 0 < c') (hη0 : 0 ≤ η₀) (hη1 : η₀ ≤ 1 / 4)
    (hδq_pos : 0 < δ_q) (hMall_nn : 0 ≤ M_all) (hσ_abs : |σ| ≤ M_all)
    (hPhiM : phiWKB (K₀ + 1) + 1 ≤ M_all)
    (hK₀_gap : (2 * c1K0 / 3) * phiWKB (K₀ + 1) ^ 2 * lambdaComb c' ≤ min 1 (δ_q / (36 * (M_all + 1) + 12)))
    (hCQ_le : C_Q ≤ c')
    (hCQ : ∀ {c' σ s sLim e eLim : ℝ}, C_Q ≤ c' →
      |σ| ≤ M_all → |s| ≤ M_all → 0 ≤ e → e ≤ M_all →
      |s - sLim| ≤ min 1 (δ_q / (18 * (M_all + 1) + 6)) →
      |e - eLim| ≤ min 1 (δ_q / (18 * (M_all + 1) + 6)) →
      |(π * lambdaComb c' / (2 * Real.sqrt 2)) ^ (-2 : ℤ) *
          blaschkePairQ (xiStar + lambdaComb c' * s) (lambdaComb c' * e) (xiStar + lambdaComb c' * σ) -
        ((σ - sLim) ^ 2 + eLim ^ 2)| ≤ δ_q) :
    |(π * lambdaComb c' / (2 * Real.sqrt 2)) ^ (-2 : ℤ) * pairModQ c' η₀ (xiStar + lambdaComb c' * σ) k -
      ((σ - phiWKB k) ^ 2 + (η₀ * (phiWKB (k + 1) - phiWKB k)) ^ 2)| ≤ δ_q := by
  set lam := lambdaComb c'
  have hlam_pos : 0 < lam := lambdaComb_pos hc'_pos
  have hk_ge1 : (1 / 4 : ℝ) ≤ (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have hk_le_K0 : (k : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hk_le
  have hsr_k := siteRadius_asymptotic hc'_pos hk_ge1
  have hsr_k1 := siteRadius_asymptotic hc'_pos (by linarith : (1 / 4 : ℝ) ≤ (k : ℝ) + 1)
  have hphi_k_eq : phiQuantile (k : ℝ) = phiWKB k := rfl
  have hphi_k1_eq : phiQuantile ((k : ℝ) + 1) = phiWKB (k + 1) := by
    unfold phiQuantile phiWKB; push_cast; ring
  have hphi_k_le : phiWKB k ≤ phiWKB (K₀ + 1) := by
    unfold phiWKB
    exact Real.rpow_le_rpow (by linarith [hk_ge1]) (by push_cast; linarith [hk_le_K0]) (by norm_num)
  have hphi_k1_le : phiWKB (k + 1) ≤ phiWKB (K₀ + 1) := by
    unfold phiWKB
    exact Real.rpow_le_rpow (by push_cast; linarith [hk_ge1]) (by push_cast; linarith [hk_le_K0]) (by norm_num)
  set σk := siteRadius c' k / lam
  set εk := η₀ * (siteGap c' k / lam)
  have hpk_nn : 0 ≤ phiWKB k := by
    unfold phiWKB; exact Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 1 / 4) _
  have hpk1_nn : 0 ≤ phiWKB (k + 1) := by
    unfold phiWKB; exact Real.rpow_nonneg (by push_cast; linarith : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) - 1 / 4) _
  have hsk_diff : |σk - phiWKB k| ≤ (2 * c1K0 / 3) * phiWKB (K₀ + 1) ^ 2 * lam := by
    rw [show σk - phiWKB k = (siteRadius c' k - lam * phiQuantile k) / lam by
      dsimp [σk]; rw [hphi_k_eq]; field_simp [hlam_pos.ne'],
      abs_div, abs_of_pos hlam_pos, div_le_iff₀ hlam_pos]
    have hsq_le : phiWKB k ^ 2 ≤ phiWKB (K₀ + 1) ^ 2 := pow_le_pow_left₀ hpk_nn hphi_k_le 2
    calc |siteRadius c' k - lam * phiQuantile k| ≤ (2 * c1K0 / 3) * (lam * phiQuantile k) ^ 2 := hsr_k
      _ = (2 * c1K0 / 3) * phiWKB k ^ 2 * lam * lam := by rw [hphi_k_eq]; ring
      _ ≤ (2 * c1K0 / 3) * phiWKB (K₀ + 1) ^ 2 * lam * lam := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsq_le (by have := c1K0_pos; positivity)) hlam_pos.le) hlam_pos.le
  have hsk1_diff : |siteRadius c' ((k : ℝ) + 1) / lam - phiWKB (k + 1)| ≤
      (2 * c1K0 / 3) * phiWKB (K₀ + 1) ^ 2 * lam := by
    rw [show siteRadius c' ((k : ℝ) + 1) / lam - phiWKB (k + 1) =
        (siteRadius c' ((k : ℝ) + 1) - lam * phiQuantile ((k : ℝ) + 1)) / lam by
      rw [hphi_k1_eq]; field_simp [hlam_pos.ne'],
      abs_div, abs_of_pos hlam_pos, div_le_iff₀ hlam_pos]
    have hsq_le : phiWKB (k + 1) ^ 2 ≤ phiWKB (K₀ + 1) ^ 2 := pow_le_pow_left₀ hpk1_nn hphi_k1_le 2
    calc |siteRadius c' ((k : ℝ) + 1) - lam * phiQuantile ((k : ℝ) + 1)|
        ≤ (2 * c1K0 / 3) * (lam * phiQuantile ((k : ℝ) + 1)) ^ 2 := hsr_k1
      _ = (2 * c1K0 / 3) * phiWKB (k + 1) ^ 2 * lam * lam := by rw [hphi_k1_eq]; ring
      _ ≤ (2 * c1K0 / 3) * phiWKB (K₀ + 1) ^ 2 * lam * lam := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsq_le (by have := c1K0_pos; positivity)) hlam_pos.le) hlam_pos.le
  have hsk_m : |σk| ≤ M_all := by
    have h1 := hsk_diff.trans (hK₀_gap.trans (min_le_left _ _))
    have : |σk| ≤ phiWKB k + 1 := by
      have := abs_sub_abs_le_abs_sub σk (phiWKB k)
      rw [abs_of_nonneg hpk_nn] at this; linarith
    linarith [hphi_k_le, hphi_k1_le, hPhiM]
  have hek_nn : 0 ≤ εk := by
    dsimp [εk]; refine mul_nonneg hη0 (div_nonneg ?_ hlam_pos.le)
    unfold siteGap
    exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc'_pos).monotoneOn
      (Set.mem_Ici.mpr hk_ge1) (Set.mem_Ici.mpr (by linarith)) (by linarith))
  have hek_m : εk ≤ M_all := by
    have hgap_sr : siteGap c' k = siteRadius c' ((k : ℝ) + 1) - siteRadius c' (k : ℝ) := by
      change chiQuantile c' ((k : ℝ) + 1) - chiQuantile c' (k : ℝ) =
        (chiQuantile c' ((k : ℝ) + 1) - xiStar) - (chiQuantile c' (k : ℝ) - xiStar)
      ring
    have hdif : εk - η₀ * (phiWKB (k + 1) - phiWKB k) =
        η₀ * ((siteRadius c' ((k : ℝ) + 1) / lam - phiWKB (k + 1)) - (σk - phiWKB k)) := by
      change η₀ * (siteGap c' k / lam) - η₀ * (phiWKB (k + 1) - phiWKB k) =
        η₀ * ((siteRadius c' ((k : ℝ) + 1) / lam - phiWKB (k + 1)) - (siteRadius c' (k : ℝ) / lam - phiWKB k))
      rw [hgap_sr]; exact eta_diff_eq η₀ _ _ lam _ _ hlam_pos.ne'
    have h1 : |εk - η₀ * (phiWKB (k + 1) - phiWKB k)| ≤ 1 / 2 := by
      rw [hdif, abs_mul, abs_of_nonneg hη0]
      have ha := hsk_diff.trans (hK₀_gap.trans (min_le_left _ _))
      have hb := hsk1_diff.trans (hK₀_gap.trans (min_le_left _ _))
      have h2 : |(siteRadius c' ((k : ℝ) + 1) / lam - phiWKB (k + 1)) - (σk - phiWKB k)| ≤ 2 :=
        (abs_sub _ _).trans (by linarith [ha, hb])
      calc η₀ * |(siteRadius c' ((k : ℝ) + 1) / lam - phiWKB (k + 1)) - (σk - phiWKB k)|
          ≤ (1 / 4) * 2 := mul_le_mul hη1 h2 (abs_nonneg _) (by norm_num)
        _ = 1 / 2 := by norm_num
    have hphi_diff_le : phiWKB (k + 1) - phiWKB k ≤ phiWKB (K₀ + 1) := by linarith [hpk_nn, hphi_k1_le]
    have h3 : η₀ * (phiWKB (k + 1) - phiWKB k) ≤ (1 / 4) * phiWKB (K₀ + 1) := by
      have hsub_nn : 0 ≤ phiWKB (k + 1) - phiWKB k := by
        unfold phiWKB
        exact sub_nonneg.mpr (Real.rpow_le_rpow (by linarith [hk_ge1]) (by push_cast; linarith) (by norm_num))
      exact mul_le_mul hη1 hphi_diff_le hsub_nn (by norm_num)
    have hup := (abs_le.mp h1).2
    have hpk0_nn : 0 ≤ phiWKB (K₀ + 1) := hpk1_nn.trans hphi_k1_le
    linarith [hup, h3, hPhiM, hpk0_nn]
  have hsk_lim_d : |σk - phiWKB k| ≤ min 1 (δ_q / (18 * (M_all + 1) + 6)) :=
    (hsk_diff.trans hK₀_gap).trans (min_one_div_half_le δ_q M_all hδq_pos.le hMall_nn).2
  have hgap_sr : siteGap c' k = siteRadius c' ((k : ℝ) + 1) - siteRadius c' (k : ℝ) := by
    change chiQuantile c' ((k : ℝ) + 1) - chiQuantile c' (k : ℝ) =
      (chiQuantile c' ((k : ℝ) + 1) - xiStar) - (chiQuantile c' (k : ℝ) - xiStar)
    ring
  have hdif : εk - η₀ * (phiWKB (k + 1) - phiWKB k) =
      η₀ * ((siteRadius c' ((k : ℝ) + 1) / lam - phiWKB (k + 1)) - (σk - phiWKB k)) := by
    change η₀ * (siteGap c' k / lam) - η₀ * (phiWKB (k + 1) - phiWKB k) =
      η₀ * ((siteRadius c' ((k : ℝ) + 1) / lam - phiWKB (k + 1)) - (siteRadius c' (k : ℝ) / lam - phiWKB k))
    rw [hgap_sr]; exact eta_diff_eq η₀ _ _ lam _ _ hlam_pos.ne'
  have hek_lim_d : |εk - η₀ * (phiWKB (k + 1) - phiWKB k)| ≤ min 1 (δ_q / (18 * (M_all + 1) + 6)) := by
    rw [hdif, abs_mul, abs_of_nonneg hη0]
    have h2 : |(siteRadius c' ((k : ℝ) + 1) / lam - phiWKB (k + 1)) - (σk - phiWKB k)| ≤
        2 * min 1 (δ_q / (36 * (M_all + 1) + 12)) :=
      (abs_sub _ _).trans ((add_le_add (hsk1_diff.trans hK₀_gap) (hsk_diff.trans hK₀_gap)).trans_eq (two_mul _).symm)
    calc η₀ * |(siteRadius c' ((k : ℝ) + 1) / lam - phiWKB (k + 1)) - (σk - phiWKB k)|
        ≤ (1 / 4) * (2 * min 1 (δ_q / (36 * (M_all + 1) + 12))) :=
          mul_le_mul hη1 h2 (abs_nonneg _) (by norm_num)
      _ = (1 / 2) * min 1 (δ_q / (36 * (M_all + 1) + 12)) := by ring
      _ ≤ min 1 (δ_q / (18 * (M_all + 1) + 6)) :=
          (min_one_div_half_le δ_q M_all hδq_pos.le hMall_nn).1
  have hpair_eq' : pairModQ c' η₀ (xiStar + lam * σ) k =
      blaschkePairQ (xiStar + lam * σk) (lam * εk) (xiStar + lam * σ) := by
    change blaschkePairQ (chiQuantile c' (k : ℝ)) (η₀ * siteGap c' k) (xiStar + lam * σ) =
      blaschkePairQ (xiStar + lam * (siteRadius c' (k : ℝ) / lam))
        (lam * (η₀ * (siteGap c' k / lam))) (xiStar + lam * σ)
    have h1 : chiQuantile c' (k : ℝ) = xiStar + lam * (siteRadius c' (k : ℝ) / lam) := by
      change chiQuantile c' (k : ℝ) = xiStar + lam * ((chiQuantile c' (k : ℝ) - xiStar) / lam)
      rw [mul_div_cancel₀ _ hlam_pos.ne']; ring
    have h2 : η₀ * siteGap c' k = lam * (η₀ * (siteGap c' k / lam)) := by
      rw [mul_left_comm, mul_div_cancel₀ _ hlam_pos.ne']
    rw [h1, h2]
  rw [hpair_eq']
  exact hCQ hCQ_le hσ_abs hsk_m hek_nn hek_m hsk_lim_d hek_lim_d

private lemma mul6_assoc_helper (a b c d e f : ℝ) :
    ((a * b * c) * d) * e * f = (a * b * (c * d) * e) * f := by ring

private lemma four_sum_abs_le (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith only [h1, h2, h3]

/-- **Lemma W (`ut:W`), second convergence**: for fixed `f ≥ 1`, `N ≥ f`, compact family
`𝒦 : CompactCombFamily f N`, `S ≥ 0`, and `N₁ : ℕ`, as `c' → ∞`,
`h₀(x) e^{c' L(x)} / K̃_c^{(f)} → W̃^{±(f)}(σ)` uniformly for `σ ∈ [-S, Φ_{N₁ + 1}]` and `D ∈ 𝒦`. -/
theorem lemma_W_comb {f N : ℕ} (𝒦 : CompactCombFamily f N) {S : ℝ} (hS : 0 ≤ S) (N₁ : ℕ) :
    ∀ ε > 0, ∃ C₀ > 0, ∀ {c' : ℝ}, C₀ ≤ c' →
      ∀ d ∈ 𝒦.members, ∀ σ ∈ Icc (-S) (phiWKB (N₁ + 1)),
        |(modifiedH0 f N d c' (xiStar + lambdaComb c' * σ) *
            Real.exp (c' * slitL (xiStar + lambdaComb c' * σ))) / windowNormKTilde f c' -
          tildeW f d.sigmaFLim d.allSigmaLim d.allEpsLim σ| ≤ ε := by
  intro ε hε
  let S_win : ℝ := max S (phiWKB (N₁ + 1))
  have hS_win : 0 ≤ S_win := le_max_of_le_left hS
  let M_lim : ℝ := max 𝒦.M 1
  obtain ⟨K_min, C_W, hKmin_N, hKmin_1, hCW_pos, hW_rate⟩ :=
    tendsto_windowFiniteProd_uniform f N 𝒦.hf 𝒦.hN (M := M_lim) (C_t := 1) (S := S_win)
      (by positivity) zero_lt_one hS_win
  obtain ⟨C_tail, hCtail_pos, htail_bd⟩ := tail_log_error_bound
  obtain ⟨K_tail, hKtail⟩ := exists_nat_gt (6 * C_tail + 1)
  obtain ⟨B_W0, hBW0_pos, hBW0_bd⟩ :=
    compactFamily_tildeW_bound 𝒦 hS_win hKmin_N hKmin_1 hCW_pos hW_rate
  obtain ⟨K_eps, hK_eps⟩ := exists_nat_gt (max (3 * C_W / min 1 ε) (24 * C_tail * (B_W0 + 1) / ε + N₁ + 3))
  let K₀ : ℕ := max (max K_min K_eps) (max (4 * N₁ + 6) (max (N + 1) (max (f + 1) (Nat.ceil (6 * C_tail) + N₁ + 4))))
  have hK₀_min : K_min ≤ K₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hK₀_N1 : 4 * N₁ + 6 ≤ K₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hK₀_N : N + 1 ≤ K₀ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hK₀_f : f + 1 ≤ K₀ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hK₀_N1_3 : N₁ + 3 ≤ K₀ := by omega
  have hK₀_tail_half : C_tail / ((K₀ : ℝ) - (N₁ : ℝ) - 2) ≤ 1 / 6 := by
    have h1 : 6 * C_tail ≤ (Nat.ceil (6 * C_tail) : ℝ) := Nat.le_ceil _
    have h2 : Nat.ceil (6 * C_tail) + N₁ + 4 ≤ K₀ :=
      (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
    have h3 : (Nat.ceil (6 * C_tail) : ℝ) + (N₁ : ℝ) + 4 ≤ (K₀ : ℝ) := by exact_mod_cast h2
    have h4 : 0 < (K₀ : ℝ) - (N₁ : ℝ) - 2 := by
      have : (N₁ : ℝ) + 3 ≤ (K₀ : ℝ) := by exact_mod_cast hK₀_N1_3
      linarith
    rw [div_le_iff₀ h4]; linarith
  have hK₀_tail_eps : (C_tail / ((K₀ : ℝ) - (N₁ : ℝ) - 2)) * (2 * (B_W0 + 2)) ≤ ε / 6 := by
    have h1 : 24 * C_tail * (B_W0 + 1) / ε + (N₁ : ℝ) + 3 < (K₀ : ℝ) := by
      have hk1 : K_eps ≤ K₀ := (le_max_right _ _).trans (le_max_left _ _)
      have hk2 : (K_eps : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hk1
      have hk3 := lt_of_le_of_lt (le_max_right (3 * C_W / min 1 ε) _) hK_eps
      linarith
    have h4 : 0 < (K₀ : ℝ) - (N₁ : ℝ) - 2 := by
      have : (N₁ : ℝ) + 3 ≤ (K₀ : ℝ) := by exact_mod_cast hK₀_N1_3
      linarith
    have h5 : 24 * C_tail * (B_W0 + 1) / ε < (K₀ : ℝ) - (N₁ : ℝ) - 2 := by linarith
    rw [div_lt_iff₀ hε] at h5
    rw [mul_comm, mul_div_assoc', div_le_iff₀ h4]
    have hbw : B_W0 + 2 ≤ 2 * (B_W0 + 1) := by linarith [hBW0_pos]
    calc 2 * (B_W0 + 2) * C_tail ≤ 2 * (2 * (B_W0 + 1)) * C_tail :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbw (by norm_num)) hCtail_pos.le
      _ = (24 * C_tail * (B_W0 + 1)) / 6 := by ring
      _ ≤ (ε * ((K₀ : ℝ) - (N₁ : ℝ) - 2)) / 6 := by linarith
      _ = ε / 6 * ((K₀ : ℝ) - (N₁ : ℝ) - 2) := by ring
  have hK₀_W_eps : C_W / (K₀ : ℝ) ≤ min 1 (ε / 3) := by
    have hk1 : K_eps ≤ K₀ := (le_max_right _ _).trans (le_max_left _ _)
    have hk2 : (K_eps : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hk1
    have hk3 := lt_of_le_of_lt (le_max_left _ (24 * C_tail * (B_W0 + 1) / ε + N₁ + 3)) hK_eps
    have hK₀_pos : (0 : ℝ) < (K₀ : ℝ) := by exact_mod_cast (by omega : 0 < K₀)
    have hmin_pos : 0 < min 1 ε := lt_min zero_lt_one hε
    have h1 : 3 * C_W / min 1 ε < (K₀ : ℝ) := hk3.trans_le hk2
    rw [div_lt_iff₀ hmin_pos] at h1
    rw [le_min_iff]
    constructor
    · rw [div_le_one hK₀_pos]
      have h3 : min 1 ε ≤ 1 := min_le_left _ _
      nlinarith [hCW_pos, min_le_left (1 : ℝ) ε]
    · rw [div_le_iff₀ hK₀_pos]
      have h3 : min 1 ε ≤ ε := min_le_right _ _
      nlinarith [hCW_pos]
  have hMK0_err : ∀ d ∈ 𝒦.members, ∀ σ ∈ Icc (-S) (phiWKB (N₁ + 1)),
      |windowFiniteProd f d.sigmaFLim d.allSigmaLim d.allEpsLim K₀ σ -
        tildeW f d.sigmaFLim d.allSigmaLim d.allEpsLim σ| ≤ min 1 (ε / 3) := by
    intro d hd σ hσ
    have hσ_mem : σ ∈ Icc (-S_win) S_win :=
      ⟨le_trans (neg_le_neg (le_max_left _ _)) hσ.1, le_trans hσ.2 (le_max_right _ _)⟩
    have hd_lim := 𝒦.lim_bounds d hd
    have hr := (hW_rate (σf := d.sigmaFLim) (σSeq := d.allSigmaLim) (εHat := d.allEpsLim)
      ((hd_lim.1).trans (le_max_left _ _))
      (fun k hk => by
        have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
        simp only [ModifiedCombData.allSigmaLim, ModifiedCombData.allEpsLim, hkN, ↓reduceIte]
        have hk' := hd_lim.2 k hk
        exact ⟨hk'.1.trans (le_max_left _ _), by rw [abs_of_nonneg hk'.2.1]; exact hk'.2.2.trans (le_max_left _ _)⟩)
      (d.tail_bound_all (𝒦.eta0_bounds d hd).1 (𝒦.eta0_bounds d hd).2)).2 hK₀_min hσ_mem
    exact hr.trans hK₀_W_eps
  let B_M : ℝ := B_W0 + 1
  let η_target : ℝ := min 1 (ε / 3)
  have hη_pos : 0 < η_target := by positivity
  obtain ⟨B_fq0, hB_fq0_nn, hB_fq0⟩ : ∃ B_fq0 : ℝ, 0 ≤ B_fq0 ∧ ∀ σ ∈ Icc (-S_win) S_win,
      |continuumFQ (continuumAK K₀) σ| ≤ B_fq0 := by
    have hc := continuous_continuumFQ (continuumAK K₀) (continuumAK_nonneg K₀)
    obtain ⟨σ₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (⟨0, by simp [hS_win]⟩ : (Icc (-S_win) S_win).Nonempty)
      (continuous_abs.comp hc).continuousOn
    exact ⟨max 0 |continuumFQ (continuumAK K₀) σ₀|, le_max_left _ _, fun σ hσ => (hmax hσ).trans (le_max_right _ _)⟩
  let B_each : ℝ := max 1 (max (Real.exp (B_fq0 + 1)) (max (S_win + M_lim)
    ((S_win + M_lim + phiWKB K₀ + 1) ^ 2 + M_lim ^ 2 + 1)))
  have hBe_ge1 : 1 ≤ B_each := le_max_left _ _
  let B_4 : ℝ := (B_each + 1) ^ (K₀ + 1) + 1
  let δ₅ : ℝ := min (1 / 2) (η_target / (4 * B_4 ^ 3))
  have hδ₅_pos : 0 < δ₅ := by positivity
  have hcont_cosh : ContinuousAt (fun x : ℝ => Real.cosh (π * xiStar / 2) ^ 2 / Real.cosh (π * x / 2) ^ 2) xiStar := by
    have hc : Real.cosh (π * xiStar / 2) ^ 2 ≠ 0 := by positivity
    fun_prop (disch := exact hc)
  obtain ⟨δ_ch, hδch_pos, hδch⟩ := Metric.continuousAt_iff.mp hcont_cosh (min 1 δ₅) (by positivity)
  let M_all : ℝ := max S_win (max M_lim (phiWKB (K₀ + 1) + 1))
  have hMall_nn : 0 ≤ M_all := le_max_of_le_left hS_win
  obtain ⟨C_T, hCT_pos, hCT⟩ := blaschkeT_window_factor_bound hMall_nn δ₅ hδ₅_pos
  let δ_q : ℝ := δ₅ / ((K₀ : ℝ) * ((B_each + 1) ^ K₀ + 1))
  have hδq_pos : 0 < δ_q := by positivity
  obtain ⟨C_Q, hCQ_pos, hCQ⟩ := blaschkePairQ_window_factor_bound hMall_nn δ_q hδq_pos
  -- 4. Integral + lobe:
  have h_lobe := lobe_window_asymptotic
  obtain ⟨C_lobe, hClobe_pos, hClobe⟩ := h_lobe
  obtain ⟨C_int, hCint_pos, hCint⟩ := integral_phiVar_sub_continuumFQ hK₀_N1 hS (δ₅ / (4 * (Real.exp B_fq0 + 1))) (by positivity)
  -- 5. Uniform convergence of `𝒦` parameters:
  let δ_lim : ℝ := min (δ₅ / (4 * (1 + M_all))) (min 1 (δ_q / (18 * (M_all + 1) + 6)))
  have hδlim_pos : 0 < δ_lim := by positivity
  obtain ⟨C_unif, hCunif_pos, hCunif⟩ := 𝒦.uniform_tendsto hδlim_pos
  -- 6. Eventually as `c' → ∞` for `lam` and `c'`:
  have hphi_gap_pos : 0 < phiQuantile ((N₁ + 2 : ℕ) : ℝ) - phiWKB (N₁ + 1) := by
    unfold phiQuantile phiWKB
    have h1 : (0 : ℝ) < ((N₁ + 1 : ℕ) : ℝ) - 1 / 4 := by
      have : (1 : ℝ) ≤ ((N₁ + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N₁ + 1)
      linarith
    have h2 : ((N₁ + 1 : ℕ) : ℝ) - 1 / 4 < ((N₁ + 2 : ℕ) : ℝ) - 1 / 4 := by
      push_cast; linarith
    exact sub_pos.mpr (Real.rpow_lt_rpow h1.le h2 (by norm_num))
  have hsiteGap1_tend : Tendsto (fun c' : ℝ => siteGap c' 1) atTop (𝓝 0) := by
    have ht1 : Tendsto (fun c' : ℝ => lambdaComb c' * phiQuantile 2) atTop (𝓝 0) := by
      simpa using tendsto_lambdaComb_atTop.mul_const (phiQuantile 2)
    rw [Metric.tendsto_nhds]
    intro δ hδ
    filter_upwards [eventually_gt_atTop 0, Metric.tendsto_nhds.mp ht1 δ hδ] with c' hc' hlt
    have h1 : xiStar ≤ chiQuantile c' 1 := (chiQuantile_spec hc' (by norm_num)).1
    have h2 : chiQuantile c' 1 ≤ chiQuantile c' 2 :=
      (chiQuantile_strictMonoOn hc').monotoneOn (by norm_num) (by norm_num) (by norm_num)
    have hgap_nn : 0 ≤ siteGap c' 1 := by
      unfold siteGap
      rw [show (1 : ℕ) = (1 : ℝ) by norm_num, show (1 : ℝ) + 1 = 2 by norm_num]
      linarith
    have hgap_ub : siteGap c' 1 ≤ lambdaComb c' * phiQuantile 2 := by
      unfold siteGap
      have hsr := (siteRadius_bounds hc' (by norm_num : (1 / 4 : ℝ) ≤ 2)).2
      unfold siteRadius at hsr
      rw [show ((1 : ℕ) : ℝ) = 1 by norm_num, show (1 : ℝ) + 1 = 2 by norm_num]
      linarith
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hgap_nn]
    have hnn_lp : 0 ≤ lambdaComb c' * phiQuantile 2 := by
      have := kTip_pos; unfold lambdaComb phiQuantile
      exact mul_nonneg (Real.rpow_nonneg (mul_nonneg kTip_pos.le hc'.le) _) (Real.rpow_nonneg (by norm_num) _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn_lp] at hlt
    exact hgap_ub.trans_lt hlt
  have h_ev_all : ∀ᶠ c' : ℝ in atTop,
      0 < c' ∧
      lambdaComb c' * M_all < min (xiStar / 2) δ_ch ∧
      siteGap c' 1 ≤ 1 / 2 ∧
      (1 / 4 : ℝ) * π * siteGap c' 1 ≤ min (1 / 6) (ε / (12 * (B_W0 + 2))) ∧
      C_lobe * M_all ^ (5 / 2 : ℝ) * lambdaComb c' ≤ δ₅ / (4 * (Real.exp B_fq0 + 1)) ∧
      (2 * c1K0 / 3) * phiQuantile ((N₁ + 2 : ℕ) : ℝ) ^ 2 * lambdaComb c' ≤
        phiQuantile ((N₁ + 2 : ℕ) : ℝ) - phiWKB (N₁ + 1) ∧
      (2 * c1K0 / 3) * phiWKB (K₀ + 1) ^ 2 * lambdaComb c' ≤ min 1 (δ_q / (36 * (M_all + 1) + 12)) := by
    have ht := tendsto_lambdaComb_atTop
    have h1 : ∀ᶠ c' : ℝ in atTop, (0 : ℝ) < c' := eventually_gt_atTop (0 : ℝ)
    have h2 : ∀ᶠ c' in atTop, lambdaComb c' * M_all < min (xiStar / 2) δ_ch := by
      have ht' : Tendsto (fun c' => lambdaComb c' * M_all) atTop (𝓝 0) := by
        simpa using ht.mul_const M_all
      exact ht'.eventually_lt_const (lt_min (half_pos xiStar_pos) hδch_pos)
    have h3 : ∀ᶠ c' in atTop, siteGap c' 1 ≤ 1 / 2 :=
      hsiteGap1_tend.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)
    have h4 : ∀ᶠ c' in atTop, (1 / 4 : ℝ) * π * siteGap c' 1 ≤ min (1 / 6) (ε / (12 * (B_W0 + 2))) := by
      have ht1 : Tendsto (fun c' => (1 / 4 : ℝ) * π * siteGap c' 1) atTop (𝓝 0) := by
        simpa using (hsiteGap1_tend.const_mul ((1 / 4 : ℝ) * π))
      exact ht1.eventually_le_const (lt_min (by norm_num) (by positivity))
    have h5 : ∀ᶠ c' in atTop, C_lobe * M_all ^ (5 / 2 : ℝ) * lambdaComb c' ≤ δ₅ / (4 * (Real.exp B_fq0 + 1)) := by
      have ht' : Tendsto (fun c' => C_lobe * M_all ^ (5 / 2 : ℝ) * lambdaComb c') atTop (𝓝 0) := by
        simpa using ht.const_mul (C_lobe * M_all ^ (5 / 2 : ℝ))
      exact ht'.eventually_le_const (by positivity)
    have h6 : ∀ᶠ c' in atTop, (2 * c1K0 / 3) * phiQuantile ((N₁ + 2 : ℕ) : ℝ) ^ 2 * lambdaComb c' ≤
        phiQuantile ((N₁ + 2 : ℕ) : ℝ) - phiWKB (N₁ + 1) := by
      have ht' : Tendsto (fun c' => (2 * c1K0 / 3) * phiQuantile ((N₁ + 2 : ℕ) : ℝ) ^ 2 * lambdaComb c') atTop (𝓝 0) := by
        simpa using ht.const_mul ((2 * c1K0 / 3) * phiQuantile ((N₁ + 2 : ℕ) : ℝ) ^ 2)
      exact ht'.eventually_le_const hphi_gap_pos
    have h7 : ∀ᶠ c' in atTop,
        (2 * c1K0 / 3) * phiWKB (K₀ + 1) ^ 2 * lambdaComb c' ≤ min 1 (δ_q / (36 * (M_all + 1) + 12)) := by
      have ht' : Tendsto (fun c' => (2 * c1K0 / 3) * phiWKB (K₀ + 1) ^ 2 * lambdaComb c') atTop (𝓝 0) := by
        simpa using ht.const_mul ((2 * c1K0 / 3) * phiWKB (K₀ + 1) ^ 2)
      exact ht'.eventually_le_const (lt_min zero_lt_one (by positivity))
    filter_upwards [h1, h2, h3, h4, h5, h6, h7] with c' hc1 hc2 hc3 hc4 hc5 hc6 hc7
    exact ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩
  obtain ⟨C_ev, hCev⟩ := eventually_atTop.mp h_ev_all
  let C_tot : ℝ := max (max C_ev C_unif) (max C_T (max C_Q C_int))
  refine ⟨max C_tot 1, by positivity, fun {c'} hc' d hd σ hσ => ?_⟩
  have hCev_le : C_ev ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hc'))
  have hCunif_le : C_unif ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hc'))
  have hCT_le : C_T ≤ c' := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hc'))
  have hCQ_le : C_Q ≤ c' := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hc')))
  have hCint_le : C_int ≤ c' := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hc')))
  obtain ⟨hc'_pos, hlam_M, hgap1, hgap_eps, hlobe_eps, hN12_gap, hK₀_gap⟩ := hCev c' hCev_le
  set lam := lambdaComb c'
  have hlam_pos : 0 < lam := lambdaComb_pos hc'_pos
  set x := xiStar + lam * σ
  have hσ_win : σ ∈ Icc (-S_win) S_win :=
    ⟨le_trans (neg_le_neg (le_max_left _ _)) hσ.1, le_trans hσ.2 (le_max_right _ _)⟩
  have hσ_abs : |σ| ≤ M_all := (abs_le.mpr hσ_win).trans (le_max_left _ _)
  have hx_nn : 0 ≤ x := by
    have := (abs_le.mp (abs_le.mpr hσ_win)).1
    have : lam * |σ| ≤ xiStar / 2 := (mul_le_mul_of_nonneg_left hσ_abs hlam_pos.le).trans (hlam_M.le.trans (min_le_left _ _))
    have : |lam * σ| ≤ xiStar / 2 := by rwa [abs_mul, abs_of_pos hlam_pos]
    linarith [(abs_le.mp this).1, xiStar_pos]
  have hx_le_N12 : x ≤ chiQuantile c' (N₁ + 2) := by
    have hsr := siteRadius_asymptotic hc'_pos (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) N₁] :
      (1 / 4 : ℝ) ≤ ((N₁ + 2 : ℕ) : ℝ))
    have h1 : lam * phiQuantile ((N₁ + 2 : ℕ) : ℝ) - siteRadius c' ((N₁ + 2 : ℕ) : ℝ) ≤
        (2 * c1K0 / 3) * (lam * phiQuantile ((N₁ + 2 : ℕ) : ℝ)) ^ 2 := by
      linarith [(abs_le.mp hsr).1]
    have h2 : (2 * c1K0 / 3) * (lam * phiQuantile ((N₁ + 2 : ℕ) : ℝ)) ^ 2 ≤
        lam * (phiQuantile ((N₁ + 2 : ℕ) : ℝ) - phiWKB (N₁ + 1)) := by
      calc (2 * c1K0 / 3) * (lam * phiQuantile ((N₁ + 2 : ℕ) : ℝ)) ^ 2
          = ((2 * c1K0 / 3) * phiQuantile ((N₁ + 2 : ℕ) : ℝ) ^ 2 * lam) * lam := by ring
        _ ≤ (phiQuantile ((N₁ + 2 : ℕ) : ℝ) - phiWKB (N₁ + 1)) * lam :=
            mul_le_mul_of_nonneg_right hN12_gap hlam_pos.le
        _ = lam * (phiQuantile ((N₁ + 2 : ℕ) : ℝ) - phiWKB (N₁ + 1)) := by ring
    have h3 : lam * phiWKB (N₁ + 1) ≤ siteRadius c' ((N₁ + 2 : ℕ) : ℝ) := by linarith
    have h4 : lam * σ ≤ lam * phiWKB (N₁ + 1) := mul_le_mul_of_nonneg_left hσ.2 hlam_pos.le
    dsimp [x]; unfold siteRadius at h3; push_cast at h3 ⊢; linarith
  have hx_lt_K0 : x < chiQuantile c' (K₀ : ℕ) := by
    have h1 : (1 / 4 : ℝ) ≤ (N₁ + 2 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) N₁]
    have h2 : (N₁ + 2 : ℝ) < (K₀ : ℝ) := by exact_mod_cast (by omega : N₁ + 2 < K₀)
    exact lt_of_le_of_lt hx_le_N12 (chiQuantile_strictMonoOn hc'_pos h1 (h1.trans h2.le) h2)
  have hη_bd := 𝒦.eta0_bounds d hd
  have hfin_bd := 𝒦.finite_bounds d hd hc'_pos
  have hlim_bd := 𝒦.lim_bounds d hd
  have hunif_d := hCunif hCunif_le d hd
  -- Apply exact window factorization:
  have hfac := modifiedH0_window_factorization d 𝒦.hf 𝒦.hN hK₀_N hc'_pos hη_bd.1 hη_bd.2 hgap1 hx_nn hx_lt_K0
  set P₀ : ℝ := π * lam / (2 * Real.sqrt 2)
  set a₀ : ℝ := (K₀ : ℝ) + 1 / 2
  set χf : ℝ := xiStar + lam * d.sigmaF c'
  set tailRem : ℝ := (∑' m : ℕ, Real.log (pairModQ c' d.eta0 x (K₀ + 1 + m))) -
    2 * ∫ a in Set.Ioi a₀, phiVar c' x a
  -- Tail bound: `0 ≤ tailRem ≤ 1/6 + 1/6 = 1/3`, so `|exp tailRem - 1| ≤ 2 * tailRem`:
  have htail_rem := htail_bd hc'_pos hη_bd.1 hη_bd.2 hgap1 hx_nn hx_le_N12 hK₀_N1_3
  have htail_le_half : |tailRem| ≤ 1 / 2 := by
    rw [abs_of_nonneg htail_rem.1]
    have h1 := hgap_eps.trans (min_le_left _ _)
    linarith [htail_rem.2, hK₀_tail_half]
  have hexp_tail_err : |Real.exp tailRem - 1| ≤ 2 * (C_tail / ((K₀ : ℝ) - (N₁ : ℝ) - 2) + (1 / 4 : ℝ) * π * siteGap c' 1) := by
    calc |Real.exp tailRem - 1| ≤ 2 * |tailRem| := abs_exp_sub_one_le htail_le_half
      _ = 2 * tailRem := by rw [abs_of_nonneg htail_rem.1]
      _ ≤ 2 * (C_tail / ((K₀ : ℝ) - (N₁ : ℝ) - 2) + (1 / 4 : ℝ) * π * siteGap c' 1) :=
          mul_le_mul_of_nonneg_left htail_rem.2 (by norm_num)
  -- Error on the 4 main factors of `M_{K₀}`:
  -- Factor 0: cosh ratio
  have hf0_err : |Real.cosh (π * xiStar / 2) ^ 2 / Real.cosh (π * x / 2) ^ 2 - 1| ≤ δ₅ := by
    have hdist : dist x xiStar < δ_ch := by
      rw [Real.dist_eq, show x - xiStar = lam * σ by dsimp [x]; ring, abs_mul, abs_of_pos hlam_pos]
      calc lam * |σ| ≤ lam * M_all := mul_le_mul_of_nonneg_left hσ_abs hlam_pos.le
        _ < min (xiStar / 2) δ_ch := hlam_M
        _ ≤ δ_ch := min_le_right _ _
    have hd_ch := (hδch hdist).le
    rw [Real.dist_eq, div_self (by positivity : Real.cosh (π * xiStar / 2) ^ 2 ≠ 0)] at hd_ch
    exact hd_ch.trans (min_le_right _ _)
  -- Factor 1: simple zero T
  have hf1_err : |P₀⁻¹ * (Real.tanh (π * (x - χf) / 2) * Real.tanh (π * (x + χf) / 2)) -
      (σ - d.sigmaFLim)| ≤ δ₅ := by
    have hsf_bd : |d.sigmaF c'| ≤ M_all := hfin_bd.1.trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _)))
    have hsf_lim : |d.sigmaF c' - d.sigmaFLim| ≤ δ₅ / (4 * (1 + M_all)) :=
      hunif_d.1.trans (min_le_left _ _)
    exact hCT hCT_le hσ_abs hsf_bd hsf_lim
  -- Factor 2: product of `(K₀ - f)` pairs
  let pairA : ℕ → ℝ := fun k =>
    if k ≤ N then P₀ ^ (-2 : ℤ) * blaschkePairQ (xiStar + lam * d.sigmaK c' k) (lam * d.epsHat c' k) x
    else P₀ ^ (-2 : ℤ) * pairModQ c' d.eta0 x k
  let pairB : ℕ → ℝ := fun k => (σ - d.allSigmaLim k) ^ 2 + (d.allEpsLim k) ^ 2
  have hpair_err : ∀ k ∈ Finset.Icc (f + 1) K₀, |pairA k - pairB k| ≤ δ_q := by
    intro k hk
    have hk_mem := Finset.mem_Icc.mp hk
    by_cases hkN : k ≤ N
    · simp only [pairA, pairB, ModifiedCombData.allSigmaLim, ModifiedCombData.allEpsLim, hkN, ↓reduceIte]
      have hk_bd := hfin_bd.2 k (Finset.mem_Icc.mpr ⟨hk_mem.1, hkN⟩)
      have hsk_lim := hunif_d.2 k (Finset.mem_Icc.mpr ⟨hk_mem.1, hkN⟩)
      have hs_m : |d.sigmaK c' k| ≤ M_all := hk_bd.1.trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _)))
      have he_m : d.epsHat c' k ≤ M_all := hk_bd.2.2.trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _)))
      have hs_d : |d.sigmaK c' k - d.sigmaKLim k| ≤ min 1 (δ_q / (18 * (M_all + 1) + 6)) := by
        refine hsk_lim.1.trans ((min_le_right _ _).trans ?_)
        refine min_le_min le_rfl ?_
        gcongr
      have he_d : |d.epsHat c' k - d.epsHatLim k| ≤ min 1 (δ_q / (18 * (M_all + 1) + 6)) := by
        refine hsk_lim.2.trans ((min_le_right _ _).trans ?_)
        refine min_le_min le_rfl ?_
        gcongr
      exact hCQ hCQ_le hσ_abs hs_m hk_bd.2.1 he_m hs_d he_d
    · simp only [pairA, pairB, ModifiedCombData.allSigmaLim, ModifiedCombData.allEpsLim, hkN, ↓reduceIte]
      have hk1 : 1 ≤ k := by omega
      exact pairMod_window_err_step hk1 hk_mem.2 hc'_pos hη_bd.1 hη_bd.2 hδq_pos hMall_nn hσ_abs
        (le_trans (le_max_right M_lim (phiWKB (K₀ + 1) + 1))
          (le_max_right S_win (max M_lim (phiWKB (K₀ + 1) + 1))))
        hK₀_gap hCQ_le hCQ
  have hB_bd : ∀ k ∈ Finset.Icc (f + 1) K₀, |pairB k| ≤ B_each := fun k hk => by
    have hk_mem := Finset.mem_Icc.mp hk
    have hnn : 0 ≤ pairB k := by dsimp [pairB]; positivity
    rw [abs_of_nonneg hnn]
    by_cases hkN : k ≤ N
    · simp only [pairB, ModifiedCombData.allSigmaLim, ModifiedCombData.allEpsLim, hkN, ↓reduceIte]
      have hk' := hlim_bd.2 k (Finset.mem_Icc.mpr ⟨hk_mem.1, hkN⟩)
      have hs1 : |σ - d.sigmaKLim k| ≤ S_win + M_lim :=
        (abs_sub _ _).trans (add_le_add (abs_le.mpr hσ_win) (hk'.1.trans (le_max_left _ _)))
      have hs2 : (σ - d.sigmaKLim k) ^ 2 ≤ (S_win + M_lim) ^ 2 := by
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hs1 2
      have he2 : d.epsHatLim k ^ 2 ≤ M_lim ^ 2 :=
        pow_le_pow_left₀ hk'.2.1 (hk'.2.2.trans (le_max_left _ _)) 2
      have h1 : (S_win + M_lim) ^ 2 + M_lim ^ 2 ≤ B_each := by
        have hpos_m : 0 ≤ S_win + M_lim := by positivity
        have hk0_ge1 : 1 ≤ K₀ := by omega
        have hpk0 : 0 ≤ phiWKB K₀ := by
          unfold phiWKB
          have hk0_r : (1 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hk0_ge1
          exact Real.rpow_nonneg (by linarith only [hk0_r]) _
        have hsq1 : (S_win + M_lim) ^ 2 ≤ (S_win + M_lim + phiWKB K₀ + 1) ^ 2 :=
          pow_le_pow_left₀ hpos_m (by linarith only [hpk0]) 2
        calc (S_win + M_lim) ^ 2 + M_lim ^ 2
            ≤ (S_win + M_lim + phiWKB K₀ + 1) ^ 2 + M_lim ^ 2 + 1 := by linarith only [hsq1]
          _ ≤ B_each := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
      linarith only [hs2, he2, h1]
    · simp only [pairB, ModifiedCombData.allSigmaLim, ModifiedCombData.allEpsLim, hkN, ↓reduceIte]
      have hk_ge1 : 1 ≤ k := by omega
      have hphi_k : phiWKB k ≤ phiWKB K₀ := by
        unfold phiWKB
        have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge1
        have hkK' : (k : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hk_mem.2
        exact Real.rpow_le_rpow (by linarith only [hk1']) (by linarith only [hkK']) (by norm_num)
      have hpk0 : 0 ≤ phiWKB K₀ := by
        unfold phiWKB
        have hk0_r : (1 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast (by omega : 1 ≤ K₀)
        exact Real.rpow_nonneg (by linarith only [hk0_r]) _
      have hpk : 0 ≤ phiWKB k := by
        unfold phiWKB
        have hk_r : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge1
        exact Real.rpow_nonneg (by linarith only [hk_r]) _
      have hs1 : |σ - phiWKB k| ≤ S_win + phiWKB K₀ :=
        (abs_sub _ _).trans (add_le_add (abs_le.mpr hσ_win) (by rw [abs_of_nonneg hpk]; exact hphi_k))
      have hM_nn : 0 ≤ M_lim := by positivity
      have hs1' : |σ - phiWKB k| ≤ S_win + M_lim + phiWKB K₀ + 1 := by linarith only [hs1, hM_nn]
      have hs2 : (σ - phiWKB k) ^ 2 ≤ (S_win + M_lim + phiWKB K₀ + 1) ^ 2 := by
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hs1' 2
      have ht := (d.tail_bound_all hη_bd.1 hη_bd.2 k (by omega)).2
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge1
      have hr13 : (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 1 := by
        rw [Real.rpow_neg (by positivity)]; exact inv_le_one_of_one_le₀ (Real.one_le_rpow hk1 (by norm_num))
      have he1 : |d.eta0 * (phiWKB (k + 1) - phiWKB k)| ≤ 1 := by
        have ht' : |d.eta0 * (phiWKB (k + 1) - phiWKB k)| ≤ (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
          simpa [ModifiedCombData.allEpsLim, hkN] using ht
        exact ht'.trans hr13
      have he2 : (d.eta0 * (phiWKB (k + 1) - phiWKB k)) ^ 2 ≤ 1 := by
        simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) he1 2
      have hbe : (S_win + M_lim + phiWKB K₀ + 1) ^ 2 + M_lim ^ 2 + 1 ≤ B_each :=
        (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
      have hm2 : 0 ≤ M_lim ^ 2 := sq_nonneg M_lim
      calc (σ - phiWKB k) ^ 2 + (d.eta0 * (phiWKB (k + 1) - phiWKB k)) ^ 2
          ≤ (S_win + M_lim + phiWKB K₀ + 1) ^ 2 + 1 := add_le_add hs2 he2
        _ ≤ (S_win + M_lim + phiWKB K₀ + 1) ^ 2 + M_lim ^ 2 + 1 := by linarith only [hm2]
        _ ≤ B_each := hbe
  have hprod2_err : |(∏ k ∈ Finset.Icc (f + 1) N, pairA k) * (∏ k ∈ Finset.Icc (N + 1) K₀, pairA k) -
      ∏ k ∈ Finset.Icc (f + 1) K₀, pairB k| ≤ δ₅ := by
    have hsplit_Icc : Finset.Icc (f + 1) K₀ = Finset.Icc (f + 1) N ∪ Finset.Icc (N + 1) K₀ := by
      have hfN := 𝒦.hN; have hNK := hK₀_N
      ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc (f + 1) N) (Finset.Icc (N + 1) K₀) := by
      rw [Finset.disjoint_left]; intro k h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
    rw [show (∏ k ∈ Finset.Icc (f + 1) N, pairA k) * (∏ k ∈ Finset.Icc (N + 1) K₀, pairA k) =
        ∏ k ∈ Finset.Icc (f + 1) K₀, pairA k by rw [hsplit_Icc, Finset.prod_union hdisj]]
    have hBe1_nn : 0 ≤ B_each + 1 := add_nonneg (le_trans zero_le_one hBe_ge1) zero_le_one
    have hA_bd : ∀ k ∈ Finset.Icc (f + 1) K₀, |pairA k| ≤ B_each + 1 := fun k hk => by
      have h1 := hB_bd k hk
      have h2 := hpair_err k hk
      have h3 : δ_q ≤ 1 := by
        have hδ5_1 : δ₅ ≤ 1 / 2 := min_le_left _ _
        have h1' : (1 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast (by omega : 1 ≤ K₀)
        have h2' : 1 ≤ (B_each + 1) ^ K₀ + 1 :=
          le_add_of_nonneg_left (pow_nonneg hBe1_nn K₀)
        have hK1 : (1 : ℝ) ≤ (K₀ : ℝ) * ((B_each + 1) ^ K₀ + 1) :=
          one_le_mul_of_one_le_of_one_le h1' h2'
        exact (div_le_one (by linarith only [hK1])).mpr (by linarith only [hδ5_1, hK1])
      have htri := abs_sub_abs_le_abs_sub (pairA k) (pairB k)
      linarith only [htri, h1, h2, h3]
    have hB_bd' : ∀ k ∈ Finset.Icc (f + 1) K₀, |pairB k| ≤ B_each + 1 :=
      fun k hk => (hB_bd k hk).trans (by linarith only [])
    have hps := prod_sub_prod_bound (Finset.Icc (f + 1) K₀) hBe1_nn hδq_pos.le
      hA_bd hB_bd' hpair_err
    refine hps.trans ?_
    have hcard : (Finset.Icc (f + 1) K₀).card ≤ K₀ := by rw [Nat.card_Icc]; omega
    have hpow_le : (B_each + 1) ^ ((Finset.Icc (f + 1) K₀).card - 1) ≤ (B_each + 1) ^ K₀ + 1 := by
      calc (B_each + 1) ^ ((Finset.Icc (f + 1) K₀).card - 1)
          ≤ (B_each + 1) ^ K₀ := pow_le_pow_right₀ (by linarith only [hBe_ge1]) (by omega)
        _ ≤ (B_each + 1) ^ K₀ + 1 := le_add_of_nonneg_right zero_le_one
    have hcard_r : ((Finset.Icc (f + 1) K₀).card : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hcard
    have hprod_le : ((Finset.Icc (f + 1) K₀).card : ℝ) *
        (B_each + 1) ^ ((Finset.Icc (f + 1) K₀).card - 1) * δ_q ≤
        (K₀ : ℝ) * ((B_each + 1) ^ K₀ + 1) * δ_q :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hcard_r hpow_le (pow_nonneg hBe1_nn _) (Nat.cast_nonneg _)) hδq_pos.le
    refine hprod_le.trans_eq ?_
    dsimp [δ_q]
    have hK_r_pos : (0 : ℝ) < (K₀ : ℝ) := by exact_mod_cast (by omega : 0 < K₀)
    have hpow1_pos : (0 : ℝ) < (B_each + 1) ^ K₀ + 1 :=
      add_pos_of_nonneg_of_pos (pow_nonneg hBe1_nn K₀) zero_lt_one
    have hne : (K₀ : ℝ) * ((B_each + 1) ^ K₀ + 1) ≠ 0 := (mul_pos hK_r_pos hpow1_pos).ne'
    exact mul_div_cancel₀ δ₅ hne
  -- Factor 3: exponential of integral + lobe
  have hexp_err : |Real.exp (-2 * (∫ a in (1 / 4 : ℝ)..a₀, (phiVar c' x a - Real.log P₀)) +
        c' * (majorantReal x + slitL x)) -
      Real.exp (continuumFQ (continuumAK K₀) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ))| ≤ δ₅ := by
    set u := -2 * (∫ a in (1 / 4 : ℝ)..a₀, (phiVar c' x a - Real.log P₀)) + c' * (majorantReal x + slitL x)
    set v := continuumFQ (continuumAK K₀) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ)
    have h_int_err := hCint hCint_le hσ
    have h_lobe_err := hClobe hc'_pos (by
      rw [mul_comm]; exact (mul_le_mul_of_nonneg_left hσ_abs hlam_pos.le).trans
        (hlam_M.le.trans (min_le_left _ _)))
    have h_lobe_le : C_lobe * (max (-σ) 0) ^ (5 / 2 : ℝ) * lam ≤ δ₅ / (4 * (Real.exp B_fq0 + 1)) := by
      have hmax_le : max (-σ) 0 ≤ M_all := max_le (by linarith [(abs_le.mp hσ_abs).1]) hMall_nn
      have hp_le : (max (-σ) 0) ^ (5 / 2 : ℝ) ≤ M_all ^ (5 / 2 : ℝ) :=
        Real.rpow_le_rpow (le_max_right _ _) hmax_le (by norm_num)
      calc C_lobe * (max (-σ) 0) ^ (5 / 2 : ℝ) * lam
          ≤ C_lobe * M_all ^ (5 / 2 : ℝ) * lam := by gcongr
        _ ≤ δ₅ / (4 * (Real.exp B_fq0 + 1)) := hlobe_eps
    have huv : |u - v| ≤ δ₅ / (2 * (Real.exp B_fq0 + 1)) := by
      have hid : u - v =
          (-2 * (∫ a in (1 / 4 : ℝ)..a₀, (phiVar c' x a - Real.log P₀)) - continuumFQ (continuumAK K₀) σ) +
          (c' * (majorantReal x + slitL x) + 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ)) := by
        dsimp [u, v]; ring
      rw [hid]
      have hsum := (abs_add_le _ _).trans (add_le_add h_int_err (h_lobe_err.trans h_lobe_le))
      exact hsum.trans_eq (by
        have hpos_b : (0 : ℝ) < Real.exp B_fq0 + 1 := by positivity
        field_simp [hpos_b.ne']
        ring)
    have huv_half : |u - v| ≤ 1 / 2 := by
      have h1 : δ₅ ≤ 1 / 2 := min_le_left _ _
      have h2 : 1 ≤ Real.exp B_fq0 + 1 := by linarith [Real.exp_pos B_fq0]
      calc |u - v| ≤ δ₅ / (2 * (Real.exp B_fq0 + 1)) := huv
        _ ≤ (1 / 2 : ℝ) / (2 * 1) := by gcongr
        _ ≤ 1 / 2 := by norm_num
    have hv_le : v ≤ B_fq0 := by
      have h1 := (le_abs_self _).trans (hB_fq0 σ hσ_win)
      have h2 : 0 ≤ 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) := by positivity
      dsimp [v]; linarith
    calc |Real.exp u - Real.exp v| = Real.exp v * |Real.exp (u - v) - 1| := by
          rw [show Real.exp u - Real.exp v = Real.exp v * (Real.exp (u - v) - 1) by
            rw [mul_sub, ← Real.exp_add, add_sub_cancel, mul_one], abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp B_fq0 * (2 * |u - v|) :=
          mul_le_mul (Real.exp_le_exp.mpr hv_le) (abs_exp_sub_one_le huv_half)
            (abs_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp B_fq0 * (2 * (δ₅ / (2 * (Real.exp B_fq0 + 1)))) := by gcongr
      _ ≤ δ₅ := by
          have hpos_e : 0 < Real.exp B_fq0 + 1 := by positivity
          calc Real.exp B_fq0 * (2 * (δ₅ / (2 * (Real.exp B_fq0 + 1))))
              = (Real.exp B_fq0 / (Real.exp B_fq0 + 1)) * δ₅ := by field_simp [hpos_e.ne']
            _ ≤ 1 * δ₅ := by gcongr; rw [div_le_one hpos_e]; linarith [Real.exp_pos B_fq0]
            _ = δ₅ := one_mul _
  -- Combine the 4 factors for `M_{K₀}`:
  let f₀ : ℝ := Real.cosh (π * xiStar / 2) ^ 2 / Real.cosh (π * x / 2) ^ 2
  let f₁ : ℝ := P₀⁻¹ * (Real.tanh (π * (x - χf) / 2) * Real.tanh (π * (x + χf) / 2))
  let f₂ : ℝ := (∏ k ∈ Finset.Icc (f + 1) N,
      P₀ ^ (-2 : ℤ) * blaschkePairQ (xiStar + lam * d.sigmaK c' k) (lam * d.epsHat c' k) x) *
    (∏ k ∈ Finset.Icc (N + 1) K₀, P₀ ^ (-2 : ℤ) * pairModQ c' d.eta0 x k)
  let f₃ : ℝ := Real.exp (-2 * (∫ a in (1 / 4 : ℝ)..a₀, (phiVar c' x a - Real.log P₀)) +
    c' * (majorantReal x + slitL x))
  let g₀ : ℝ := 1
  let g₁ : ℝ := σ - d.sigmaFLim
  let g₂ : ℝ := ∏ k ∈ Finset.Icc (f + 1) K₀, pairB k
  let g₃ : ℝ := Real.exp (continuumFQ (continuumAK K₀) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ))
  have hf₂_eq : f₂ = (∏ k ∈ Finset.Icc (f + 1) N, pairA k) * (∏ k ∈ Finset.Icc (N + 1) K₀, pairA k) := by
    dsimp [f₂, pairA]
    congr 1
    · refine Finset.prod_congr rfl fun k hk => ?_
      have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
      simp only [hkN, ↓reduceIte]
    · refine Finset.prod_congr rfl fun k hk => ?_
      have hkN : ¬ k ≤ N := by simp only [Finset.mem_Icc] at hk; omega
      simp only [hkN, ↓reduceIte]
  have hg_sub : |g₀| ≤ (B_each + 1) ^ (K₀ + 1) ∧ |g₁| ≤ (B_each + 1) ^ (K₀ + 1) ∧
      |g₂| ≤ (B_each + 1) ^ (K₀ + 1) ∧ |g₃| ≤ (B_each + 1) ^ (K₀ + 1) := by
    have hBe_gt : 1 ≤ B_each + 1 := by linarith only [hBe_ge1]
    have hBe_sub : B_each ≤ (B_each + 1) ^ (K₀ + 1) := by
      have h1 : B_each + 1 ≤ (B_each + 1) ^ (K₀ + 1) := by
        simpa using pow_le_pow_right₀ hBe_gt (by omega : 1 ≤ K₀ + 1)
      linarith only [h1]
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp [g₀]; rw [abs_one]; exact one_le_pow₀ hBe_gt
    · have h1 : |g₁| ≤ S_win + M_lim := (abs_sub _ _).trans (add_le_add (abs_le.mpr hσ_win)
        (hlim_bd.1.trans (le_max_left _ _)))
      have h2 : S_win + M_lim ≤ B_each := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
      linarith only [h1, h2, hBe_sub]
    · have h1 : 0 ≤ g₂ := Finset.prod_nonneg fun _ _ => by dsimp [pairB]; positivity
      rw [abs_of_nonneg h1]
      have hp : ∏ k ∈ Finset.Icc (f + 1) K₀, pairB k ≤ ∏ _k ∈ Finset.Icc (f + 1) K₀, (B_each + 1) :=
        Finset.prod_le_prod₀ (fun _ _ => by dsimp [pairB]; positivity) fun k hk => by
          have hk' := hB_bd k hk
          have hnn : 0 ≤ pairB k := by dsimp [pairB]; positivity
          rw [abs_of_nonneg hnn] at hk'
          linarith only [hk']
      calc ∏ k ∈ Finset.Icc (f + 1) K₀, pairB k ≤ ∏ _k ∈ Finset.Icc (f + 1) K₀, (B_each + 1) := hp
        _ = (B_each + 1) ^ (Finset.Icc (f + 1) K₀).card := Finset.prod_const _
        _ ≤ (B_each + 1) ^ (K₀ + 1) := pow_le_pow_right₀ hBe_gt (by rw [Nat.card_Icc]; omega)
    · rw [abs_of_pos (Real.exp_pos _)]
      have h1 : continuumFQ (continuumAK K₀) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) ≤ B_fq0 + 1 := by
        have h1' := (le_abs_self _).trans (hB_fq0 σ hσ_win)
        have h2' : 0 ≤ 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) := by positivity
        linarith only [h1', h2']
      have h2 : Real.exp (B_fq0 + 1) ≤ B_each := (le_max_left _ _).trans (le_max_right _ _)
      exact (Real.exp_le_exp.mpr h1).trans (h2.trans hBe_sub)
  have hg_bd : |g₀| ≤ B_4 ∧ |g₁| ≤ B_4 ∧ |g₂| ≤ B_4 ∧ |g₃| ≤ B_4 :=
    ⟨hg_sub.1.trans (by dsimp [B_4]; linarith only []), hg_sub.2.1.trans (by dsimp [B_4]; linarith only []),
     hg_sub.2.2.1.trans (by dsimp [B_4]; linarith only []), hg_sub.2.2.2.trans (by dsimp [B_4]; linarith only [])⟩
  have hprod2_err' : |f₂ - g₂| ≤ δ₅ := by rw [hf₂_eq]; exact hprod2_err
  have hf_bd : |f₀| ≤ B_4 ∧ |f₁| ≤ B_4 ∧ |f₂| ≤ B_4 ∧ |f₃| ≤ B_4 := by
    have hδ_half : δ₅ ≤ 1 / 2 := min_le_left _ _
    have hB_gap : ∀ t a : ℝ, |a| ≤ (B_each + 1) ^ (K₀ + 1) → |t - a| ≤ δ₅ → |t| ≤ B_4 := fun t a ha hta => by
      have := abs_sub_abs_le_abs_sub t a
      dsimp [B_4]; linarith only [this, ha, hta, hδ_half]
    exact ⟨hB_gap f₀ g₀ hg_sub.1 hf0_err, hB_gap f₁ g₁ hg_sub.2.1 hf1_err,
      hB_gap f₂ g₂ hg_sub.2.2.1 hprod2_err', hB_gap f₃ g₃ hg_sub.2.2.2 hexp_err⟩
  let M_approx : ℝ := f₀ * f₁ * f₂ * f₃
  let M_K0_lim : ℝ := g₀ * g₁ * g₂ * g₃
  have hMK0_lim_eq : M_K0_lim = windowFiniteProd f d.sigmaFLim d.allSigmaLim d.allEpsLim K₀ σ := by
    dsimp [M_K0_lim, g₀, g₁, g₂, g₃, pairB]
    unfold windowFiniteProd
    ring
  have hM_diff : |M_approx - M_K0_lim| ≤ η_target := by
    have hB4_nn : 0 ≤ B_4 := by dsimp [B_4]; positivity
    have hid_sub : f₀ * f₁ * f₂ * f₃ - g₀ * g₁ * g₂ * g₃ =
        (f₀ - g₀) * f₁ * f₂ * f₃ + g₀ * (f₁ - g₁) * f₂ * f₃ +
          g₀ * g₁ * (f₂ - g₂) * f₃ + g₀ * g₁ * g₂ * (f₃ - g₃) := by ring
    have h3 : ∀ a b c d : ℝ, |a| ≤ B_4 → |b| ≤ B_4 → |c| ≤ B_4 → |d| ≤ δ₅ →
        |a * b * c * d| ≤ B_4 ^ 3 * δ₅ := fun a b c d ha hb hc hd => by
      rw [abs_mul, abs_mul, abs_mul]
      calc |a| * |b| * |c| * |d| ≤ B_4 * B_4 * B_4 * δ₅ :=
            mul_le_mul (mul_le_mul (mul_le_mul ha hb (abs_nonneg _) hB4_nn) hc (abs_nonneg _) (by positivity))
              hd (abs_nonneg _) (by positivity)
        _ = B_4 ^ 3 * δ₅ := by ring
    have ht0 : |(f₀ - g₀) * f₁ * f₂ * f₃| ≤ B_4 ^ 3 * δ₅ := by
      have := h3 f₁ f₂ f₃ (f₀ - g₀) hf_bd.2.1 hf_bd.2.2.1 hf_bd.2.2.2 hf0_err
      rwa [show |(f₀ - g₀) * f₁ * f₂ * f₃| = |f₁ * f₂ * f₃ * (f₀ - g₀)| by congr 1; ring]
    have ht1 : |g₀ * (f₁ - g₁) * f₂ * f₃| ≤ B_4 ^ 3 * δ₅ := by
      have := h3 g₀ f₂ f₃ (f₁ - g₁) hg_bd.1 hf_bd.2.2.1 hf_bd.2.2.2 hf1_err
      rwa [show |g₀ * (f₁ - g₁) * f₂ * f₃| = |g₀ * f₂ * f₃ * (f₁ - g₁)| by congr 1; ring]
    have ht2 : |g₀ * g₁ * (f₂ - g₂) * f₃| ≤ B_4 ^ 3 * δ₅ := by
      have := h3 g₀ g₁ f₃ (f₂ - g₂) hg_bd.1 hg_bd.2.1 hf_bd.2.2.2 hprod2_err'
      rwa [show |g₀ * g₁ * (f₂ - g₂) * f₃| = |g₀ * g₁ * f₃ * (f₂ - g₂)| by congr 1; ring]
    have ht3 : |g₀ * g₁ * g₂ * (f₃ - g₃)| ≤ B_4 ^ 3 * δ₅ :=
      h3 g₀ g₁ g₂ (f₃ - g₃) hg_bd.1 hg_bd.2.1 hg_bd.2.2.1 hexp_err
    have h4 : |M_approx - M_K0_lim| ≤ 4 * B_4 ^ 3 * δ₅ := by
      dsimp [M_approx, M_K0_lim]
      rw [hid_sub]
      have htri := four_sum_abs_le ((f₀ - g₀) * f₁ * f₂ * f₃) (g₀ * (f₁ - g₁) * f₂ * f₃)
        (g₀ * g₁ * (f₂ - g₂) * f₃) (g₀ * g₁ * g₂ * (f₃ - g₃))
      linarith only [htri, ht0, ht1, ht2, ht3]
    have hB4_pos : 0 < B_4 := lt_add_of_le_of_pos (pow_nonneg (by positivity : 0 ≤ B_each + 1) _) zero_lt_one
    have hδ_le : δ₅ ≤ η_target / (4 * B_4 ^ 3) := min_le_right _ _
    have h4_le : 4 * B_4 ^ 3 * δ₅ ≤ η_target := by
      calc 4 * B_4 ^ 3 * δ₅ ≤ 4 * B_4 ^ 3 * (η_target / (4 * B_4 ^ 3)) := by gcongr
        _ = η_target := by field_simp
    exact h4.trans h4_le
  have hMapprox_bd : |M_approx| ≤ B_W0 + 2 := by
    have hW_bd := hBW0_bd d hd σ hσ_win
    have hMK_bd := hMK0_err d hd σ hσ
    have h1 := abs_sub_abs_le_abs_sub M_approx M_K0_lim
    have h2 := abs_sub_abs_le_abs_sub M_K0_lim (tildeW f d.sigmaFLim d.allSigmaLim d.allEpsLim σ)
    have hη_le1 : η_target ≤ 1 := min_le_left _ _
    have hW_le1 : |M_K0_lim - tildeW f d.sigmaFLim d.allSigmaLim d.allEpsLim σ| ≤ 1 := by
      rw [hMK0_lim_eq]; exact hMK_bd.trans (min_le_left _ _)
    linarith only [hW_bd, h1, h2, hη_le1, hW_le1, hM_diff]
  have h_fac_eq : (modifiedH0 f N d c' x * Real.exp (c' * slitL x)) / windowNormKTilde f c' =
      M_approx * Real.exp tailRem := by
    rw [hfac]
    exact mul6_assoc_helper _ _ _ _ _ _
  have h_tail_total : |Real.exp tailRem - 1| * |M_approx| ≤ ε / 3 := by
    have hgap_e : (1 / 4 : ℝ) * π * siteGap c' 1 ≤ ε / (12 * (B_W0 + 2)) := hgap_eps.trans (min_le_right _ _)
    have hexp1 : |Real.exp tailRem - 1| ≤
        2 * (C_tail / ((K₀ : ℝ) - (N₁ : ℝ) - 2)) + 2 * ((1 / 4 : ℝ) * π * siteGap c' 1) := by
      calc |Real.exp tailRem - 1| ≤ 2 * (C_tail / ((K₀ : ℝ) - (N₁ : ℝ) - 2) + (1 / 4 : ℝ) * π * siteGap c' 1) := hexp_tail_err
        _ = 2 * (C_tail / ((K₀ : ℝ) - (N₁ : ℝ) - 2)) + 2 * ((1 / 4 : ℝ) * π * siteGap c' 1) := by ring
    have hterm1 : 2 * (C_tail / ((K₀ : ℝ) - (N₁ : ℝ) - 2)) * (B_W0 + 2) ≤ ε / 6 := by
      calc 2 * (C_tail / ((K₀ : ℝ) - (N₁ : ℝ) - 2)) * (B_W0 + 2)
          = (C_tail / ((K₀ : ℝ) - (N₁ : ℝ) - 2)) * (2 * (B_W0 + 2)) := by ring
        _ ≤ ε / 6 := hK₀_tail_eps
    have hterm2 : 2 * ((1 / 4 : ℝ) * π * siteGap c' 1) * (B_W0 + 2) ≤ ε / 6 := by
      have hbw_pos : 0 < B_W0 + 2 := by linarith only [hBW0_pos]
      calc 2 * ((1 / 4 : ℝ) * π * siteGap c' 1) * (B_W0 + 2)
          ≤ 2 * (ε / (12 * (B_W0 + 2))) * (B_W0 + 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgap_e (by norm_num)) hbw_pos.le
        _ = ε / 6 := by field_simp [hbw_pos.ne']; ring
    have hpos_rhs : 0 ≤ 2 * (C_tail / ((K₀ : ℝ) - (N₁ : ℝ) - 2)) + 2 * ((1 / 4 : ℝ) * π * siteGap c' 1) :=
      (abs_nonneg _).trans hexp1
    calc |Real.exp tailRem - 1| * |M_approx|
        ≤ (2 * (C_tail / ((K₀ : ℝ) - (N₁ : ℝ) - 2)) + 2 * ((1 / 4 : ℝ) * π * siteGap c' 1)) * (B_W0 + 2) :=
          mul_le_mul hexp1 hMapprox_bd (abs_nonneg _) hpos_rhs
      _ = 2 * (C_tail / ((K₀ : ℝ) - (N₁ : ℝ) - 2)) * (B_W0 + 2) +
            2 * ((1 / 4 : ℝ) * π * siteGap c' 1) * (B_W0 + 2) := by ring
      _ ≤ ε / 6 + ε / 6 := add_le_add hterm1 hterm2
      _ = ε / 3 := by ring
  have h1 : |M_approx * Real.exp tailRem - M_approx| ≤ ε / 3 := by
    rw [show M_approx * Real.exp tailRem - M_approx = (Real.exp tailRem - 1) * M_approx by ring, abs_mul]
    exact h_tail_total
  have h2 : |M_approx - M_K0_lim| ≤ ε / 3 := hM_diff.trans (min_le_right _ _)
  have h3 : |M_K0_lim - tildeW f d.sigmaFLim d.allSigmaLim d.allEpsLim σ| ≤ ε / 3 := by
    rw [hMK0_lim_eq]; exact (hMK0_err d hd σ hσ).trans (min_le_right _ _)
  change |(modifiedH0 f N d c' x * Real.exp (c' * slitL x)) / windowNormKTilde f c' -
    tildeW f d.sigmaFLim d.allSigmaLim d.allEpsLim σ| ≤ ε
  rw [h_fac_eq]
  have ht1 := abs_sub_le (M_approx * Real.exp tailRem) M_approx (tildeW f d.sigmaFLim d.allSigmaLim d.allEpsLim σ)
  have ht2 := abs_sub_le M_approx M_K0_lim (tildeW f d.sigmaFLim d.allSigmaLim d.allEpsLim σ)
  linarith only [ht1, ht2, h1, h2, h3]

/-- **Lemma W (`ut:W`), first (measure) convergence**: for any `prob : FixedWeightProblem`,
compact family `𝒦 : CompactCombFamily f N`, `S ≥ 0`, and `N₁ : ℕ`, as `c' → ∞`,
`h₀(x) V(c' x² / 3) (dt / dσ) / FK_c^{(f)} → W̃^{±(f)}(σ)`
uniformly for `σ ∈ [-S, Φ_{N₁ + 1}]` and `D ∈ 𝒦`. -/
theorem lemma_W_measure (prob : FixedWeightProblem) {f N : ℕ} (𝒦 : CompactCombFamily f N)
    {S : ℝ} (hS : 0 ≤ S) (N₁ : ℕ) :
    ∀ ε > 0, ∃ C₀ > 0, ∀ {c' : ℝ}, C₀ ≤ c' →
      ∀ d ∈ 𝒦.members, ∀ σ ∈ Icc (-S) (phiWKB (N₁ + 1)),
        let x := xiStar + lambdaComb c' * σ
        let dt_dσ := (2 * c' * x / 3) * lambdaComb c'
        |(modifiedH0 f N d c' x * prob.cardyV (c' / 12) (c' * x ^ 2 / 3) * dt_dσ) /
            windowMeasureNormK prob f c' -
          tildeW f d.sigmaFLim d.allSigmaLim d.allEpsLim σ| ≤ ε := by
  intro ε hε
  let S_win : ℝ := max S (phiWKB (N₁ + 1))
  have hS_win : 0 ≤ S_win := le_max_of_le_left hS
  let M_lim : ℝ := max 𝒦.M 1
  obtain ⟨K_min, C_W, hKmin_N, hKmin_1, hCW_pos, hW_rate⟩ :=
    tendsto_windowFiniteProd_uniform f N 𝒦.hf 𝒦.hN (M := M_lim) (C_t := 1) (S := S_win)
      (by positivity) zero_lt_one hS_win
  obtain ⟨B_W, hBW_pos, hBW_bd⟩ :=
    compactFamily_tildeW_bound 𝒦 hS_win hKmin_N hKmin_1 hCW_pos hW_rate
  obtain ⟨C_comb, hCcomb_pos, hcomb⟩ := lemma_W_comb 𝒦 hS N₁ (min 1 (ε / 2)) (by positivity)
  obtain ⟨C_V, hCV_nn, hCV⟩ := cardyV_asymptotic_real prob (half_pos xiStar_pos)
  set Q_star : ℝ := prob.nullPoly (Real.exp (-4 * π * xiStar))
  have hQ_pos : 0 < Q_star := (nullPoly_exp_bounds prob xiStar_pos).1
  let G : ℝ → ℝ := fun x =>
    ((2 * x) ^ (prob.w - 1) * prob.nullPoly (Real.exp (-4 * π * x)) * Real.sqrt (x / 3)) /
      ((2 * xiStar) ^ (prob.w - 1) * Q_star * Real.sqrt (xiStar / 3))
  have hG_cont : ContinuousAt G xiStar := by
    have hQ_cont : ContinuousAt (fun x : ℝ => prob.nullPoly (Real.exp (-4 * π * x))) xiStar := by
      unfold FixedWeightProblem.nullPoly
      exact (continuous_finsetProd _ fun l _ =>
        continuous_const.sub ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).rpow_const
          (fun x => Or.inl (Real.exp_pos _).ne'))).continuousAt
    have hden_ne : (2 * xiStar) ^ (prob.w - 1) * Q_star * Real.sqrt (xiStar / 3) ≠ 0 := by
      have := xiStar_pos; positivity
    have hx3_ne : xiStar / 3 ≠ 0 := by have := xiStar_pos; positivity
    dsimp [G]
    fun_prop (disch := first | exact hx3_ne | exact hden_ne)
  have hG_at : G xiStar = 1 := by
    dsimp [G, Q_star]
    have hden_ne : (2 * xiStar) ^ (prob.w - 1) * prob.nullPoly (Real.exp (-4 * π * xiStar)) * Real.sqrt (xiStar / 3) ≠ 0 := by
      have := xiStar_pos; positivity
    exact div_self hden_ne
  let q₀ : ℝ := prob.nullPoly (Real.exp (-4 * π * (xiStar / 2)))
  have hq₀_pos : 0 < q₀ := (nullPoly_exp_bounds prob (half_pos xiStar_pos)).1
  let δ_rv : ℝ := ε / (2 * (B_W + 1))
  have hδrv_pos : 0 < δ_rv := by positivity
  obtain ⟨δ_G, hδG_pos, hδG⟩ := Metric.continuousAt_iff.mp hG_cont (min 1 (δ_rv / 2)) (by positivity)
  have h_ev : ∀ᶠ c' : ℝ in atTop,
      0 < c' ∧
      max 1 (24 * prob.totalShift) ≤ c' ∧
      lambdaComb c' * S_win < min (xiStar / 2) (δ_G / 2) ∧
      (C_V / c') * (2 / q₀) ≤ δ_rv / 2 := by
    have h1 : ∀ᶠ c' : ℝ in atTop, 0 < c' := eventually_gt_atTop 0
    have h2 : ∀ᶠ c' : ℝ in atTop, max 1 (24 * prob.totalShift) ≤ c' := eventually_ge_atTop _
    have h3 : ∀ᶠ c' : ℝ in atTop, lambdaComb c' * S_win < min (xiStar / 2) (δ_G / 2) := by
      have ht' : Tendsto (fun c' => lambdaComb c' * S_win) atTop (𝓝 0) := by
        simpa using tendsto_lambdaComb_atTop.mul_const S_win
      exact ht'.eventually_lt_const (lt_min (half_pos xiStar_pos) (half_pos hδG_pos))
    have h4 : ∀ᶠ c' : ℝ in atTop, (C_V / c') * (2 / q₀) ≤ δ_rv / 2 := by
      have ht : Tendsto (fun c' : ℝ => (C_V / c') * (2 / q₀)) atTop (𝓝 0) := by
        simpa using ((tendsto_const_nhds.div_atTop tendsto_id).mul_const (2 / q₀))
      exact ht.eventually_le_const (half_pos hδrv_pos)
    filter_upwards [h1, h2, h3, h4] with c' hc1 hc2 hc3 hc4
    exact ⟨hc1, hc2, hc3, hc4⟩
  obtain ⟨C_ev, hCev⟩ := eventually_atTop.mp h_ev
  refine ⟨max C_comb (max C_ev 1), by positivity, fun {c'} hc' d hd σ hσ => ?_⟩
  have hCcomb_le : C_comb ≤ c' := (le_max_left _ _).trans hc'
  have hCev_le : C_ev ≤ c' := (le_max_left _ _).trans ((le_max_right _ _).trans hc')
  obtain ⟨hc'_pos, hcV_le, hlam_bd, hcV_eps⟩ := hCev c' hCev_le
  have hlam_pos : 0 < lambdaComb c' := lambdaComb_pos hc'_pos
  set x := xiStar + lambdaComb c' * σ
  have hσ_win : σ ∈ Icc (-S_win) S_win :=
    ⟨le_trans (neg_le_neg (le_max_left _ _)) hσ.1, le_trans hσ.2 (le_max_right _ _)⟩
  have hdist_x : dist x xiStar < δ_G := by
    rw [Real.dist_eq, show x - xiStar = lambdaComb c' * σ by dsimp [x]; ring, abs_mul, abs_of_pos hlam_pos]
    calc lambdaComb c' * |σ| ≤ lambdaComb c' * S_win := mul_le_mul_of_nonneg_left (abs_le.mpr hσ_win) hlam_pos.le
      _ < min (xiStar / 2) (δ_G / 2) := hlam_bd
      _ ≤ δ_G / 2 := min_le_right _ _
      _ < δ_G := half_lt_self hδG_pos
  have hx_ge_half : xiStar / 2 ≤ x := by
    have h1 : lambdaComb c' * |σ| ≤ xiStar / 2 :=
      (mul_le_mul_of_nonneg_left (abs_le.mpr hσ_win) hlam_pos.le).trans (hlam_bd.le.trans (min_le_left _ _))
    have h2 : |lambdaComb c' * σ| ≤ xiStar / 2 := by rwa [abs_mul, abs_of_pos hlam_pos]
    linarith [(abs_le.mp h2).1]
  have hx_pos : 0 < x := lt_of_lt_of_le (half_pos xiStar_pos) hx_ge_half
  have h_bessel_eq : besselAs (c' * (2 * π * x / 3)) * ((2 * c' * x / 3) * lambdaComb c') =
      Real.exp (c' * slitL x) * ((1 / π) * Real.sqrt (x / 3) * Real.sqrt c' * lambdaComb c') := by
    unfold besselAs slitL
    rw [abs_of_pos hx_pos]
    have hs_eq : Real.sqrt (2 * π * (c' * (2 * π * x / 3))) =
        2 * π * Real.sqrt (x / 3) * Real.sqrt c' := by
      have harg : 2 * π * (c' * (2 * π * x / 3)) = (2 * π) ^ 2 * ((x / 3) * c') := by ring
      rw [harg, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), Real.sqrt_mul (by positivity)]
      ring
    have hsq_x : x / 3 = Real.sqrt (x / 3) * Real.sqrt (x / 3) := (Real.mul_self_sqrt (by positivity)).symm
    have hsq_c : c' = Real.sqrt c' * Real.sqrt c' := (Real.mul_self_sqrt hc'_pos.le).symm
    have hne : 2 * π * Real.sqrt (x / 3) * Real.sqrt c' ≠ 0 := by positivity
    rw [hs_eq]
    calc Real.exp (c' * (2 * π * x / 3)) / (2 * π * Real.sqrt (x / 3) * Real.sqrt c') *
          (2 * c' * x / 3 * lambdaComb c')
        = Real.exp (c' * (2 * π * x / 3)) * ((2 * (x / 3) * c' * lambdaComb c') /
            (2 * π * Real.sqrt (x / 3) * Real.sqrt c')) := by ring
      _ = Real.exp (c' * (2 * π * x / 3)) * ((2 * (Real.sqrt (x / 3) * Real.sqrt (x / 3)) *
            (Real.sqrt c' * Real.sqrt c') * lambdaComb c') /
            (2 * π * Real.sqrt (x / 3) * Real.sqrt c')) := by rw [← hsq_x, ← hsq_c]
      _ = Real.exp (c' * (2 * π * x / 3)) * ((1 / π) * Real.sqrt (x / 3) * Real.sqrt c' * lambdaComb c') := by
            field_simp [hne]
  set denomV : ℝ := (2 * x) ^ (prob.w - 1) * besselAs (c' * (2 * π * x / 3))
  have hdenomV_pos : 0 < denomV := by
    dsimp [denomV]; exact mul_pos (by positivity) (besselAs_pos (by positivity))
  set facX : ℝ := ((2 * x) ^ (prob.w - 1) * Real.sqrt (x / 3)) /
      ((2 * xiStar) ^ (prob.w - 1) * Q_star * Real.sqrt (xiStar / 3))
  set R_V : ℝ := (prob.cardyV (c' / 12) (c' * x ^ 2 / 3) / denomV) * facX
  have hG_err := (hδG hdist_x).le
  rw [Real.dist_eq, hG_at] at hG_err
  have hQ_ge : q₀ ≤ prob.nullPoly (Real.exp (-4 * π * x)) :=
    ((nullPoly_exp_bounds prob (half_pos xiStar_pos)).2 hx_ge_half).1
  have h_fac_rv :
      (modifiedH0 f N d c' x * prob.cardyV (c' / 12) (c' * x ^ 2 / 3) * ((2 * c' * x / 3) * lambdaComb c')) /
          windowMeasureNormK prob f c' =
        ((modifiedH0 f N d c' x * Real.exp (c' * slitL x)) / windowNormKTilde f c') * R_V := by
    unfold windowMeasureNormK
    have hK_ne : windowNormKTilde f c' ≠ 0 := by
      unfold windowNormKTilde
      have h1 : 0 < Real.cosh (π * xiStar / 2) ^ 2 := by positivity
      have h2 : 0 < 2 * Real.sqrt 2 / (π * lambdaComb c') := by positivity
      exact mul_ne_zero (div_ne_zero one_ne_zero h1.ne') (Real.rpow_pos_of_pos h2 _).ne'
    have hrest_ne : (2 * xiStar) ^ (prob.w - 1) * Q_star * (1 / π) * Real.sqrt (xiStar / 3) *
        Real.sqrt c' * lambdaComb c' ≠ 0 := by
      have := xiStar_pos; positivity
    have hcardy_eq : prob.cardyV (c' / 12) (c' * x ^ 2 / 3) * ((2 * c' * x / 3) * lambdaComb c') =
        Real.exp (c' * slitL x) * ((prob.cardyV (c' / 12) (c' * x ^ 2 / 3) / denomV) *
          ((2 * x) ^ (prob.w - 1) * ((1 / π) * Real.sqrt (x / 3) * Real.sqrt c' * lambdaComb c'))) := by
      have h_v : prob.cardyV (c' / 12) (c' * x ^ 2 / 3) * ((2 * c' * x / 3) * lambdaComb c') =
          (prob.cardyV (c' / 12) (c' * x ^ 2 / 3) / denomV) *
            ((2 * x) ^ (prob.w - 1) * (besselAs (c' * (2 * π * x / 3)) * ((2 * c' * x / 3) * lambdaComb c'))) := by
        rw [show (prob.cardyV (c' / 12) (c' * x ^ 2 / 3) / denomV) *
            ((2 * x) ^ (prob.w - 1) * (besselAs (c' * (2 * π * x / 3)) * ((2 * c' * x / 3) * lambdaComb c'))) =
            (prob.cardyV (c' / 12) (c' * x ^ 2 / 3) * ((2 * c' * x / 3) * lambdaComb c')) * (denomV / denomV) by
              dsimp [denomV]; ring,
          div_self hdenomV_pos.ne', mul_one]
      rw [h_v, h_bessel_eq]; ring
    rw [mul_assoc (modifiedH0 f N d c' x), hcardy_eq]
    dsimp [R_V, facX, Q_star] at *
    change _ / (windowNormKTilde f c' * ((2 * xiStar) ^ (prob.w - 1) *
        prob.nullPoly (Real.exp (-4 * π * xiStar)) * (1 / π) *
        Real.sqrt (xiStar / 3) * Real.sqrt c' * lambdaComb c')) = _
    field_simp [hK_ne, hrest_ne]
  have hfacX_nn : 0 ≤ facX := by dsimp [facX]; have := xiStar_pos; positivity
  have hGq : G x = prob.nullPoly (Real.exp (-4 * π * x)) * facX := by
    dsimp [G, facX]; ring
  have hfacX_bd : |facX| ≤ 2 / q₀ := by
    rw [abs_of_nonneg hfacX_nn]
    have hG_le2 : G x ≤ 2 := by
      have h1 : |G x| ≤ 2 := by
        have := abs_sub_abs_le_abs_sub (G x) 1
        rw [abs_one] at this
        have h1' : |G x - 1| ≤ 1 := hG_err.trans (min_le_left _ _)
        linarith
      exact (le_abs_self _).trans h1
    rw [le_div_iff₀ hq₀_pos]
    calc facX * q₀ ≤ facX * prob.nullPoly (Real.exp (-4 * π * x)) := mul_le_mul_of_nonneg_left hQ_ge hfacX_nn
      _ = G x := by rw [hGq, mul_comm]
      _ ≤ 2 := hG_le2
  have hCV_x := hCV hcV_le hx_ge_half
  have hRV_err : |R_V - 1| ≤ δ_rv := by
    have hid : R_V - 1 = (prob.cardyV (c' / 12) (c' * x ^ 2 / 3) / denomV -
        prob.nullPoly (Real.exp (-4 * π * x))) * facX + (G x - 1) := by
      dsimp [R_V]; rw [hGq]; ring
    rw [hid]
    have ht1 : |(prob.cardyV (c' / 12) (c' * x ^ 2 / 3) / denomV -
        prob.nullPoly (Real.exp (-4 * π * x))) * facX| ≤ δ_rv / 2 := by
      rw [abs_mul]
      calc |prob.cardyV (c' / 12) (c' * x ^ 2 / 3) / denomV -
              prob.nullPoly (Real.exp (-4 * π * x))| * |facX|
          ≤ (C_V / c') * (2 / q₀) := mul_le_mul hCV_x hfacX_bd (abs_nonneg _) (by positivity)
        _ ≤ δ_rv / 2 := hcV_eps
    have ht2 : |G x - 1| ≤ δ_rv / 2 := hG_err.trans (min_le_right _ _)
    exact (abs_add_le _ _).trans (add_le_add ht1 ht2 |>.trans (by linarith))
  have hcomb_d := hcomb hCcomb_le d hd σ hσ
  set M_comb : ℝ := (modifiedH0 f N d c' x * Real.exp (c' * slitL x)) / windowNormKTilde f c'
  set W_lim : ℝ := tildeW f d.sigmaFLim d.allSigmaLim d.allEpsLim σ
  have hM_bd : |M_comb| ≤ B_W + 1 := by
    have h1 : |M_comb - W_lim| ≤ 1 := by
      simpa [M_comb, W_lim, x] using hcomb_d.trans (min_le_left _ _)
    have h2 : |W_lim| ≤ B_W := hBW_bd d hd σ hσ_win
    have := abs_sub_abs_le_abs_sub M_comb W_lim
    linarith
  have hMW_eps : |M_comb - W_lim| ≤ ε / 2 := by
    simpa [M_comb, W_lim, x] using hcomb_d.trans (min_le_right _ _)
  dsimp only
  change |(modifiedH0 f N d c' x * prob.cardyV (c' / 12) (c' * x ^ 2 / 3) * ((2 * c' * x / 3) * lambdaComb c')) /
      windowMeasureNormK prob f c' - W_lim| ≤ ε
  rw [h_fac_rv]
  rw [show M_comb * R_V - W_lim = M_comb * (R_V - 1) + (M_comb - W_lim) by ring]
  have hm_rv : |M_comb * (R_V - 1)| ≤ ε / 2 := by
    rw [abs_mul]
    calc |M_comb| * |R_V - 1| ≤ (B_W + 1) * δ_rv :=
          mul_le_mul hM_bd hRV_err (abs_nonneg _) (by positivity)
      _ = ε / 2 := by
          dsimp [δ_rv]
          have hne : B_W + 1 ≠ 0 := by positivity
          field_simp [hne]
  exact (abs_add_le _ _).trans (add_le_add hm_rv hMW_eps |>.trans (by linarith))

/-- Explicit `ModifiedCombData` realization of the `f = 1` design `D(N, η_*, d)`
(`designWindowW` in `Product.lean`) in Airy-window coordinates `(s_1 + d / κ, s_k, η_* (Φ_{k+1} - Φ_k))`. -/
noncomputable def designCombData (N : ℕ) (etaStar d : ℝ) : ModifiedCombData 1 N where
  sigmaF _ := sNodeAiry 1 + d / kappaAiry
  sigmaK _ k := sNodeAiry k
  epsHat _ k := etaStar * (phiWKB (k + 1) - phiWKB k)
  eta0 := 1 / 4
  sigmaFLim := sNodeAiry 1 + d / kappaAiry
  sigmaKLim k := sNodeAiry k
  epsHatLim k := etaStar * (phiWKB (k + 1) - phiWKB k)

/-- Compact family of designs `D(N, η_*, d)` for fixed `N ≥ 1`, `η_* ∈ [0, 1/4]`, and `|d| ≤ D_bd`. -/
noncomputable def designCombFamily (N : ℕ) (hN : 1 ≤ N) {D_bd : ℝ} (_hD : 0 ≤ D_bd) :
    CompactCombFamily 1 N where
  members := {m | ∃ etaStar ∈ Icc (0 : ℝ) (1 / 4), ∃ d ∈ Icc (-D_bd) D_bd, m = designCombData N etaStar d}
  hf := le_rfl
  hN := hN
  M := max 1 (max (|sNodeAiry 1| + D_bd / kappaAiry)
    ((Finset.Icc 2 N).sum fun k => |sNodeAiry k| + (1 / 4 : ℝ) * |phiWKB (k + 1) - phiWKB k|))
  hM := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  eta0_bounds := by
    rintro m ⟨etaStar, _, d, _, rfl⟩
    norm_num [designCombData]
  finite_bounds := by
    rintro m ⟨etaStar, hη, d, hd, rfl⟩ c' _
    have hκ : 0 < kappaAiry := kappaAiry_pos
    refine ⟨?_, fun k hk => ?_⟩
    · refine le_trans ?_ (le_max_right _ _)
      refine le_trans ?_ (le_max_left _ _)
      refine (abs_add_le _ _).trans ?_
      rw [abs_div, abs_of_pos hκ]
      have hd_abs : |d| ≤ D_bd := abs_le.mpr hd
      gcongr
    · have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      have hphi_nn : 0 ≤ phiWKB (k + 1) - phiWKB k := by
        unfold phiWKB
        refine sub_nonneg.mpr (Real.rpow_le_rpow ?_ ?_ (by norm_num))
        · have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
          linarith
        · push_cast; linarith
      refine ⟨?_, mul_nonneg hη.1 hphi_nn, ?_⟩
      · refine le_trans ?_ (le_max_right _ _)
        refine le_trans ?_ (le_max_right _ _)
        exact Finset.single_le_sum (fun j _ => by positivity) hk |>.trans' (le_add_of_nonneg_right (by positivity))
      · refine le_trans ?_ (le_max_right _ _)
        refine le_trans ?_ (le_max_right _ _)
        calc etaStar * (phiWKB (k + 1) - phiWKB k)
            ≤ (1 / 4 : ℝ) * |phiWKB (k + 1) - phiWKB k| := by
              rw [abs_of_nonneg hphi_nn]
              exact mul_le_mul_of_nonneg_right hη.2 hphi_nn
          _ ≤ |sNodeAiry k| + (1 / 4 : ℝ) * |phiWKB (k + 1) - phiWKB k| := le_add_of_nonneg_left (abs_nonneg _)
          _ ≤ (Finset.Icc 2 N).sum fun j => |sNodeAiry j| + (1 / 4 : ℝ) * |phiWKB (j + 1) - phiWKB j| :=
              Finset.single_le_sum (f := fun j : ℕ => |sNodeAiry j| + (1 / 4 : ℝ) * |phiWKB (j + 1) - phiWKB j|)
                (fun j _ => by positivity) hk
  lim_bounds := by
    rintro m ⟨etaStar, hη, d, hd, rfl⟩
    have hκ : 0 < kappaAiry := kappaAiry_pos
    refine ⟨?_, fun k hk => ?_⟩
    · refine le_trans ?_ (le_max_right _ _)
      refine le_trans ?_ (le_max_left _ _)
      refine (abs_add_le _ _).trans ?_
      rw [abs_div, abs_of_pos hκ]
      have hd_abs : |d| ≤ D_bd := abs_le.mpr hd
      gcongr
    · have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      have hphi_nn : 0 ≤ phiWKB (k + 1) - phiWKB k := by
        unfold phiWKB
        refine sub_nonneg.mpr (Real.rpow_le_rpow ?_ ?_ (by norm_num))
        · have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
          linarith
        · push_cast; linarith
      refine ⟨?_, mul_nonneg hη.1 hphi_nn, ?_⟩
      · refine le_trans ?_ (le_max_right _ _)
        refine le_trans ?_ (le_max_right _ _)
        exact Finset.single_le_sum (fun j _ => by positivity) hk |>.trans' (le_add_of_nonneg_right (by positivity))
      · refine le_trans ?_ (le_max_right _ _)
        refine le_trans ?_ (le_max_right _ _)
        calc etaStar * (phiWKB (k + 1) - phiWKB k)
            ≤ (1 / 4 : ℝ) * |phiWKB (k + 1) - phiWKB k| := by
              rw [abs_of_nonneg hphi_nn]
              exact mul_le_mul_of_nonneg_right hη.2 hphi_nn
          _ ≤ |sNodeAiry k| + (1 / 4 : ℝ) * |phiWKB (k + 1) - phiWKB k| := le_add_of_nonneg_left (abs_nonneg _)
          _ ≤ (Finset.Icc 2 N).sum fun j => |sNodeAiry j| + (1 / 4 : ℝ) * |phiWKB (j + 1) - phiWKB j| :=
              Finset.single_le_sum (f := fun j : ℕ => |sNodeAiry j| + (1 / 4 : ℝ) * |phiWKB (j + 1) - phiWKB j|)
                (fun j _ => by positivity) hk
  uniform_tendsto := by
    intro ε hε
    refine ⟨1, zero_lt_one, fun _ m hm => ?_⟩
    rcases hm with ⟨etaStar, _, d, _, rfl⟩
    simp [designCombData, hε.le]

lemma designCombData_mem_compactFamily (N : ℕ) (hN : 1 ≤ N) {D_bd : ℝ} (hD : 0 ≤ D_bd)
    {etaStar d : ℝ} (hη : etaStar ∈ Icc (0 : ℝ) (1 / 4)) (hd : d ∈ Icc (-D_bd) D_bd) :
    designCombData N etaStar d ∈ (designCombFamily N hN hD).members :=
  ⟨etaStar, hη, d, hd, rfl⟩

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.tendsto_windowFiniteProd_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_windowFiniteProd_uniform

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.continuous_tildeW' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuous_tildeW

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.lemma_W_comb' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_W_comb

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.lemma_W_measure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_W_measure

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.designCombData_mem_compactFamily' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designCombData_mem_compactFamily

end

end FormalResearch.ModularBootstrap.Upper.Window

