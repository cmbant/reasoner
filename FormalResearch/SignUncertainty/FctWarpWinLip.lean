/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctWarpWinInner

/-!
# Spectral-parameter Lipschitz bound for `fctS` and `winMuMix L1 - 1` estimate (`fct:warp-win`)

Leaf helper module for `FctWarpWinRSq.lean`:
* `win_fctS_û_lipschitz`: for `p ≤ 20`, `û ↦ fctS û κ` is `C B`-Lipschitz on `[-M, M]`;
* `win_mu_diag_sub_one`: `winMuMix K4 ε c L1 L1 α - 1 ∈ 𝒮^8_{10}(C c^{-4/3})` on `[0, fctUc c]` when `|α| ≤ Cα c^{-2/3}`.

Class: proved.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped Real ContDiff BigOperators
open FormalResearch.CohnElkies FormalResearch.Special FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD FormalResearch.SignUncertainty.FctSymA

namespace FormalResearch.SignUncertainty

/-! ### 1. Lipschitz bound of `fctS û κ` with respect to `û` -/

private lemma win_id_symCls : FctSymCls 8 1 2 (fun u : ℝ => (u : ℂ)) := by
  refine ⟨(Complex.ofRealCLM.contDiff.of_le le_top).contDiffOn, fun r hr u hu => ?_⟩
  have hu0 : 0 ≤ u := mem_Ici.mp hu
  have hDi : UniqueDiffOn ℝ (Ici (0 : ℝ)) := uniqueDiffOn_Ici 0
  have hd1 : ∀ x ∈ Ici (0 : ℝ), derivWithin (fun y : ℝ => (y : ℂ)) (Ici 0) x = 1 :=
    fun x hx => ((hasDerivAt_id x).ofReal_comp.hasDerivWithinAt).derivWithin (hDi.uniqueDiffWithinAt hx)
  have hconst_zero : ∀ (k : ℕ) (x : ℝ), x ∈ Ici (0 : ℝ) →
      iteratedDerivWithin (k + 1) (fun _ : ℝ => (1 : ℂ)) (Ici 0) x = 0 := by
    intro k
    induction k with
    | zero =>
        intro x hx
        rw [iteratedDerivWithin_one]
        exact (hasDerivWithinAt_const x (Ici 0) (1 : ℂ)).derivWithin (hDi.uniqueDiffWithinAt hx)
    | succ m _ =>
        intro x hx
        rw [iteratedDerivWithin_succ']
        have hc : iteratedDerivWithin (m + 1) (derivWithin (fun _ : ℝ => (1 : ℂ)) (Ici 0)) (Ici 0) x =
            iteratedDerivWithin (m + 1) (fun _ : ℝ => (0 : ℂ)) (Ici 0) x :=
          iteratedDerivWithin_congr (fun y hy =>
            (hasDerivWithinAt_const y (Ici 0) (1 : ℂ)).derivWithin (hDi.uniqueDiffWithinAt hy)) hx
        have h0 : iteratedDerivWithin (m + 1) (fun _ : ℝ => (0 : ℂ)) (Ici 0) x = 0 := by
          have hz_eq : (fun _ : ℝ => (0 : ℂ)) = fun _ => (0 : ℂ) * (fun _ : ℝ => (1 : ℂ)) 0 := by
            ext; simp
          rw [hz_eq, iteratedDerivWithin_const_mul hx hDi (0 : ℂ) contDiffWithinAt_const, zero_mul]
        exact hc.trans h0
  rcases Nat.lt_trichotomy r 1 with hr0 | rfl | hr2
  · obtain rfl : r = 0 := by omega
    rw [iteratedDerivWithin_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
    simp only [Nat.cast_zero, sub_zero, Real.rpow_one]; linarith
  · rw [iteratedDerivWithin_one, hd1 u hu, norm_one]
    simp only [Nat.cast_one, sub_self, Real.rpow_zero]; norm_num
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, r = m + 2 := ⟨r - 2, by omega⟩
    have hz : iteratedDerivWithin (m + 2) (fun y : ℝ => (y : ℂ)) (Ici 0) u = 0 := by
      rw [iteratedDerivWithin_succ']
      exact (iteratedDerivWithin_congr hd1 hu).trans (hconst_zero m u hu)
    rw [hz, norm_zero]
    exact mul_nonneg (by positivity) (Real.rpow_pos_of_pos (by linarith) _).le

private lemma win_u_mul_symCls {p B : ℝ} {κ : ℝ → ℂ} (_hB : 0 ≤ B)
    (hκ : FctSymCls 8 p B κ) :
    FctSymCls 8 (p + 1) (2 ^ 8 * 2 * B) (fun u : ℝ => (u : ℂ) * κ u) := by
  simpa only [add_comm 1 p] using win_id_symCls.mul Set.Subset.rfl (uniqueDiffOn_Ici 0) hκ

private lemma win_exp_fac_12 {ε u : ℝ} (hε : 0 < ε) (hu1 : 1 ≤ u) :
    Real.exp (-(ε * u ^ 2)) ≤ (Nat.factorial 12 : ℝ) * ε ^ (-12 : ℤ) * u ^ (-24 : ℝ) := by
  have hu0 : 0 < u := by linarith
  have hfac := Real.pow_div_factorial_le_exp (ε * u ^ 2) (by positivity) 12
  have hpow_eq : (ε * u ^ 2) ^ 12 = ε ^ (12 : ℕ) * u ^ (24 : ℝ) := by
    rw [mul_pow, ← pow_mul, ← Real.rpow_natCast u 24]; norm_num
  rw [hpow_eq] at hfac
  have hcoef_nn : 0 ≤ (Nat.factorial 12 : ℝ) * ε ^ (-12 : ℤ) * u ^ (-24 : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hfac hcoef_nn
  have hleft : (Nat.factorial 12 : ℝ) * ε ^ (-12 : ℤ) * u ^ (-24 : ℝ) *
      (ε ^ (12 : ℕ) * u ^ (24 : ℝ) / (Nat.factorial 12 : ℝ)) = 1 := by
    have hz : ε ^ (-12 : ℤ) * ε ^ (12 : ℕ) = 1 := by simp [zpow_neg, hε.ne']
    have hr : u ^ (-24 : ℝ) * u ^ (24 : ℝ) = 1 := by
      rw [Real.rpow_neg hu0.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hu0 24).ne']
    have hf : (Nat.factorial 12 : ℝ) / (Nat.factorial 12 : ℝ) = 1 :=
      div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero 12))
    calc (Nat.factorial 12 : ℝ) * ε ^ (-12 : ℤ) * u ^ (-24 : ℝ) *
          (ε ^ (12 : ℕ) * u ^ (24 : ℝ) / (Nat.factorial 12 : ℝ))
        = ((Nat.factorial 12 : ℝ) / (Nat.factorial 12 : ℝ)) *
            (ε ^ (-12 : ℤ) * ε ^ (12 : ℕ)) * (u ^ (-24 : ℝ) * u ^ (24 : ℝ)) := by ring
      _ = 1 := by rw [hf, hz, hr]; ring
  rw [hleft] at hmul
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  exact hmul

private lemma win_1u_sm {p : ℕ} (hp : p ≤ 20) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    (1 + u) ^ (p : ℝ) ≤ (2 : ℝ) ^ (20 : ℕ) :=
  calc (1 + u) ^ (p : ℝ) ≤ (2 : ℝ) ^ (p : ℝ) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (Nat.cast_nonneg _)
    _ ≤ (2 : ℝ) ^ (20 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast hp)
    _ = (2 : ℝ) ^ (20 : ℕ) := Real.rpow_natCast _ _

private lemma win_1u_lg {p : ℕ} (hp : p ≤ 20) {u : ℝ} (hu1 : 1 ≤ u) :
    (1 + u) ^ (p : ℝ) ≤ (2 : ℝ) ^ (20 : ℕ) * u ^ (20 : ℝ) := by
  have hu0 : 0 < u := by linarith
  calc (1 + u) ^ (p : ℝ) ≤ (2 * u) ^ (p : ℝ) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (Nat.cast_nonneg _)
    _ ≤ (2 * u) ^ (20 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by exact_mod_cast hp)
    _ = (2 : ℝ) ^ (20 : ℝ) * u ^ (20 : ℝ) := Real.mul_rpow (by norm_num) hu0.le
    _ = (2 : ℝ) ^ (20 : ℕ) * u ^ (20 : ℝ) := by norm_cast

private lemma win_fctS_û_lipschitz_le {M : ℝ} {p : ℕ} (hM : 0 < M) (hp : p ≤ 20)
    (C_u : ℝ)
    (hCu : ∀ (û B : ℝ) (κ : ℝ → ℂ), |û| ≤ M → 0 ≤ B → FctSymCls 8 (p + 1) B κ →
      ∀ ε ∈ Ioo (0 : ℝ) 1, ‖fctSEps û ε κ‖ ≤ C_u * B)
    {û₁ û₂ B : ℝ} {κ : ℝ → ℂ} (hû₁ : |û₁| ≤ M) (hû₂ : |û₂| ≤ M)
    (hle : û₁ ≤ û₂) (hB : 0 ≤ B) (hκ : FctSymCls 8 p B κ) :
    ‖fctS û₂ κ - fctS û₁ κ‖ ≤ (C_u * (2 ^ 8 * 2)) * B * |û₂ - û₁| := by
  have hκ' : FctSymCls 8 (p + 1) (2 ^ 8 * 2 * B) (fun u : ℝ => (u : ℂ) * κ u) :=
    win_u_mul_symCls hB hκ
  have h1 := (FctSymA.fctInnerSymbolsA M 8 p hM (by norm_num)
    (by linarith [show (p : ℝ) ≤ 20 by exact_mod_cast hp])).choose_spec.2 û₁ B κ hû₁ hB hκ
  have h2 := (FctSymA.fctInnerSymbolsA M 8 p hM (by norm_num)
    (by linarith [show (p : ℝ) ≤ 20 by exact_mod_cast hp])).choose_spec.2 û₂ B κ hû₂ hB hκ
  obtain ⟨L1, hL1⟩ := h1.1
  obtain ⟨L2, hL2⟩ := h2.1
  have hS1 : Tendsto (fun ε : ℝ => fctSEps û₁ ε κ) (𝓝[>] (0 : ℝ)) (𝓝 (fctS û₁ κ)) :=
    hL1.fctS_eq ▸ hL1
  have hS2 : Tendsto (fun ε : ℝ => fctSEps û₂ ε κ) (𝓝[>] (0 : ℝ)) (𝓝 (fctS û₂ κ)) :=
    hL2.fctS_eq ▸ hL2
  have hsub : Tendsto (fun ε : ℝ => ‖fctSEps û₂ ε κ - fctSEps û₁ ε κ‖) (𝓝[>] (0 : ℝ))
      (𝓝 ‖fctS û₂ κ - fctS û₁ κ‖) := (hS2.sub hS1).norm
  refine le_of_tendsto hsub ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε hε
  have hε0 : 0 < ε := hε.1
  let ph : ℂ := Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I)
  let F : ℝ → ℝ → ℂ := fun t u =>
    ph * ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * ((t * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ)) *
      ((-Complex.I) * ((u : ℂ) * κ u))
  let F₀ : ℝ → ℝ → ℂ := fun t u =>
    ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * ((t * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ)) * κ u
  have hexp_norm : ∀ t u : ℝ,
      ‖Complex.exp (-(Complex.I * ((t * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ))‖ =
        Real.exp (-(ε * u ^ 2)) := fun t u => by
    rw [Complex.norm_exp]; congr 1
    simp only [Complex.sub_re, Complex.neg_re, Complex.I_mul_re, Complex.ofReal_re,
      Complex.ofReal_im, neg_zero, zero_sub]
  have hF_bd : ∀ t u : ℝ, 0 < u →
      ‖F t u‖ ≤ B * u ^ (1 / 2 : ℝ) * (1 + u) ^ (p : ℝ) * Real.exp (-(ε * u ^ 2)) :=
    fun t u hu0 => by
      have hκ_u := hκ.2 0 (Nat.zero_le _) u hu0.le
      rw [iteratedDerivWithin_zero, Nat.cast_zero, sub_zero] at hκ_u
      have hph : ‖ph‖ = 1 := by dsimp only [ph]; rw [mul_comm, Complex.norm_exp_I_mul_ofReal]
      have hup : ‖((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ * ‖(u : ℂ)‖ = u ^ (1 / 2 : ℝ) := by
        rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (Real.rpow_pos_of_pos hu0 _), abs_of_pos hu0]
        nth_rw 2 [← Real.rpow_one u]
        rw [← Real.rpow_add hu0]; congr 1; norm_num
      calc ‖F t u‖ = ‖ph‖ * ‖((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
            ‖Complex.exp (-(Complex.I * ((t * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ))‖ *
            (‖(-Complex.I : ℂ)‖ * (‖(u : ℂ)‖ * ‖κ u‖)) := by simp only [F, norm_mul]
        _ = (‖((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ * ‖(u : ℂ)‖) * Real.exp (-(ε * u ^ 2)) * ‖κ u‖ := by
            rw [hph, hexp_norm, norm_neg, Complex.norm_I]; ring
        _ ≤ u ^ (1 / 2 : ℝ) * Real.exp (-(ε * u ^ 2)) * (B * (1 + u) ^ (p : ℝ)) := by rw [hup]; gcongr
        _ = B * u ^ (1 / 2 : ℝ) * (1 + u) ^ (p : ℝ) * Real.exp (-(ε * u ^ 2)) := by ring
  set C_g : ℝ := B * 2 ^ (20 : ℕ) * (Nat.factorial 12 : ℝ) * ε ^ (-12 : ℤ)
  let g : ℝ → ℝ := fun u =>
    (Ioc (0 : ℝ) 1).indicator (fun _ => B * 2 ^ (20 : ℕ)) u +
    (Ioi (1 : ℝ)).indicator (fun u => C_g * u ^ (-3 : ℝ)) u
  have hg_int : IntegrableOn g (Ioi 0) volume := by
    have h1 : IntegrableOn (fun _ : ℝ => B * 2 ^ (20 : ℕ)) (Ioc 0 1) volume :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    have h2 : IntegrableOn (fun u : ℝ => C_g * u ^ (-3 : ℝ)) (Ioi 1) volume :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) zero_lt_one).const_mul C_g
    exact (h1.integrable_indicator measurableSet_Ioc).integrableOn.add
      (h2.integrable_indicator measurableSet_Ioi).integrableOn
  have hg_bd : ∀ t u : ℝ, 0 < u → ‖F t u‖ ≤ g u := fun t u hu0 => by
    rcases le_or_gt u 1 with hu1 | hu1
    · have hm : u ∈ Ioc (0 : ℝ) 1 := ⟨hu0, hu1⟩
      have hn : u ∉ Ioi (1 : ℝ) := not_lt.mpr hu1
      have hg_eq : g u = B * 2 ^ (20 : ℕ) := by
        dsimp only [g]; rw [Set.indicator_of_mem hm, Set.indicator_of_notMem hn, add_zero]
      rw [hg_eq]
      have hu12 : u ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hu0.le hu1 (by norm_num)
      have hexp1 : Real.exp (-(ε * u ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
      calc ‖F t u‖ ≤ B * u ^ (1 / 2 : ℝ) * (1 + u) ^ (p : ℝ) * Real.exp (-(ε * u ^ 2)) := hF_bd t u hu0
        _ ≤ B * 1 * (2 : ℝ) ^ (20 : ℕ) * 1 := by have := win_1u_sm hp hu0 hu1; gcongr
        _ = B * 2 ^ (20 : ℕ) := by ring
    · have hm : u ∈ Ioi (1 : ℝ) := hu1
      have hn : u ∉ Ioc (0 : ℝ) 1 := fun h => not_le.mpr hu1 h.2
      have hg_eq : g u = C_g * u ^ (-3 : ℝ) := by
        dsimp only [g]; rw [Set.indicator_of_notMem hn, Set.indicator_of_mem hm, zero_add]
      rw [hg_eq]
      have hu12 : u ^ (1 / 2 : ℝ) ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1.le (by norm_num)
      have hupow : u ^ (1 : ℝ) * u ^ (20 : ℝ) * u ^ (-24 : ℝ) = u ^ (-3 : ℝ) := by
        rw [← Real.rpow_add hu0, ← Real.rpow_add hu0]; congr 1; norm_num
      calc ‖F t u‖ ≤ B * u ^ (1 / 2 : ℝ) * (1 + u) ^ (p : ℝ) * Real.exp (-(ε * u ^ 2)) := hF_bd t u hu0
        _ ≤ B * u ^ (1 : ℝ) * ((2 : ℝ) ^ (20 : ℕ) * u ^ (20 : ℝ)) *
              ((Nat.factorial 12 : ℝ) * ε ^ (-12 : ℤ) * u ^ (-24 : ℝ)) := by
            have := win_1u_lg hp hu1.le; have := win_exp_fac_12 hε0 hu1.le; gcongr
        _ = C_g * (u ^ (1 : ℝ) * u ^ (20 : ℝ) * u ^ (-24 : ℝ)) := by dsimp [C_g]; ring
        _ = C_g * u ^ (-3 : ℝ) := by rw [hupow]
  have hF_meas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Ioc û₁ û₂)).prod (volume.restrict (Ioi 0))) := by
    have hcont_F : ContinuousOn (Function.uncurry F) (univ ×ˢ Ioi 0) := by
      have h1 : ContinuousOn (fun q : ℝ × ℝ => ((q.2 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (univ ×ˢ Ioi 0) :=
        Complex.continuous_ofReal.continuousOn.comp
          (continuousOn_snd.rpow_const fun q hq => Or.inl hq.2.ne') (mapsTo_univ _ _)
      have h2 : ContinuousOn (fun q : ℝ × ℝ => Complex.exp (-(Complex.I * ((q.1 * q.2 + q.2 ^ 3 / 12 : ℝ) : ℂ)) -
          ((ε * q.2 ^ 2 : ℝ) : ℂ))) (univ ×ˢ Ioi 0) :=
        Continuous.continuousOn (Complex.continuous_exp.comp
          (((continuous_const.mul (Complex.continuous_ofReal.comp
            ((continuous_fst.mul continuous_snd).add ((continuous_snd.pow 3).div_const 12)))).neg).sub
            (Complex.continuous_ofReal.comp (continuous_const.mul (continuous_snd.pow 2)))))
      have h3 : ContinuousOn (fun q : ℝ × ℝ => (-Complex.I) * ((q.2 : ℂ) * κ q.2)) (univ ×ˢ Ioi 0) :=
        continuousOn_const.mul ((Complex.continuous_ofReal.continuousOn.comp continuousOn_snd (mapsTo_univ _ _)).mul
          (hκ.1.continuousOn.comp continuousOn_snd fun q hq => hq.2.le))
      exact ((continuousOn_const.mul h1).mul h2).mul h3
    rw [Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))]
    exact (hcont_F.aestronglyMeasurable (MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi)).mono_measure
      (Measure.restrict_mono (Set.prod_mono (subset_univ _) subset_rfl) le_rfl)
  have h_prod_int : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc û₁ û₂)).prod (volume.restrict (Ioi 0))) := by
    have hdom : Integrable (fun q : ℝ × ℝ => (1 : ℝ) * g q.2)
        ((volume.restrict (Ioc û₁ û₂)).prod (volume.restrict (Ioi 0))) :=
      (integrableOn_const (hs := measure_Ioc_lt_top.ne)).integrable.mul_prod hg_int
    refine hdom.mono' hF_meas ?_
    rw [Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))]
    filter_upwards [ae_restrict_mem (MeasurableSet.prod measurableSet_Ioc measurableSet_Ioi)] with q hq
    simp only [one_mul]
    exact hg_bd q.1 q.2 hq.2
  have hswap := MeasureTheory.integral_integral_swap h_prod_int
  have hint_t : ∀ u ∈ Ioi (0 : ℝ), ∫ t in Ioc û₁ û₂, F t u = ph * (F₀ û₂ u - F₀ û₁ u) := fun u _ => by
    have hftc : ∫ t in û₁..û₂, ((-Complex.I * (u : ℂ)) * Complex.exp (-(Complex.I * ((t * u : ℝ) : ℂ)))) =
        Complex.exp (-(Complex.I * ((û₂ * u : ℝ) : ℂ))) - Complex.exp (-(Complex.I * ((û₁ * u : ℝ) : ℂ))) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (a := û₁) (b := û₂)
        (f := fun t => Complex.exp (-(Complex.I * ((t * u : ℝ) : ℂ)))) (fun t _ => ?_) ?_
      · have hd := ((((hasDerivAt_id t).mul_const u).ofReal_comp).const_mul (-Complex.I)).cexp
        refine (hd.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
        · dsimp only [Function.comp_def, id_eq]; congr 1; push_cast; ring
        · simp only [id_eq]; push_cast; ring
      · exact Continuous.intervalIntegrable (continuous_const.mul (Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_id.mul continuous_const))).neg)) _ _
    have hlin : (fun t : ℝ => F t u) = fun t =>
        (ph * ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * ((u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ)) * κ u) *
          ((-Complex.I * (u : ℂ)) * Complex.exp (-(Complex.I * ((t * u : ℝ) : ℂ)))) := by
      ext t; dsimp only [F]
      have he : -(Complex.I * ((t * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ) =
          (-(Complex.I * ((u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ)) + -(Complex.I * ((t * u : ℝ) : ℂ)) := by
        push_cast; ring
      rw [he, Complex.exp_add]; ring
    rw [hlin, ← intervalIntegral.integral_of_le hle, intervalIntegral.integral_const_mul, hftc]
    dsimp only [F₀]
    have e2 : -(Complex.I * ((û₂ * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ) =
        -(Complex.I * ((û₂ * u : ℝ) : ℂ)) + (-(Complex.I * ((u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ)) := by
      push_cast; ring
    have e1 : -(Complex.I * ((û₁ * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ) =
        -(Complex.I * ((û₁ * u : ℝ) : ℂ)) + (-(Complex.I * ((u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ)) := by
      push_cast; ring
    rw [e2, e1, Complex.exp_add, Complex.exp_add]; ring
  have hF0_int : ∀ û : ℝ, IntegrableOn (F₀ û) (Ioi 0) volume := fun û => by
    have hcont : ContinuousOn (F₀ û) (Ioi 0) :=
      ((Complex.continuous_ofReal.continuousOn.comp
          (continuousOn_id.rpow_const fun x (hx : x ∈ Ioi (0 : ℝ)) => Or.inl hx.ne') (mapsTo_univ _ _)).mul
        (Continuous.continuousOn (Complex.continuous_exp.comp
          (((continuous_const.mul (Complex.continuous_ofReal.comp
            ((continuous_const.mul continuous_id).add ((continuous_id.pow 3).div_const 12)))).neg).sub
            (Complex.continuous_ofReal.comp (continuous_const.mul (continuous_id.pow 2))))))).mul
        (hκ.1.continuousOn.mono Ioi_subset_Ici_self)
    let g0 : ℝ → ℝ := fun u =>
      (Ioc (0 : ℝ) 1).indicator (fun u => B * 2 ^ (20 : ℕ) * u ^ (-(1 / 2 : ℝ))) u +
      (Ioi (1 : ℝ)).indicator (fun u => C_g * u ^ (-4 : ℝ)) u
    have hg0_int : IntegrableOn g0 (Ioi 0) volume := by
      have hi1 : IntegrableOn (fun u : ℝ => B * 2 ^ (20 : ℕ) * u ^ (-(1 / 2 : ℝ))) (Ioc 0 1) volume :=
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
          (intervalIntegral.intervalIntegrable_rpow' (by norm_num))).const_mul _
      have hi2 : IntegrableOn (fun u : ℝ => C_g * u ^ (-4 : ℝ)) (Ioi 1) volume :=
        (integrableOn_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) zero_lt_one).const_mul _
      exact (hi1.integrable_indicator measurableSet_Ioc).integrableOn.add
        (hi2.integrable_indicator measurableSet_Ioi).integrableOn
    refine hg0_int.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
    have hκ_u := hκ.2 0 (Nat.zero_le _) u hu.le
    rw [iteratedDerivWithin_zero, Nat.cast_zero, sub_zero] at hκ_u
    have hn : ‖F₀ û u‖ ≤ B * u ^ (-(1 / 2 : ℝ)) * (1 + u) ^ (p : ℝ) * Real.exp (-(ε * u ^ 2)) := by
      simp only [F₀, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hu _), hexp_norm]
      calc u ^ (-(1 / 2 : ℝ)) * Real.exp (-(ε * u ^ 2)) * ‖κ u‖
          ≤ u ^ (-(1 / 2 : ℝ)) * Real.exp (-(ε * u ^ 2)) * (B * (1 + u) ^ (p : ℝ)) := by gcongr
        _ = B * u ^ (-(1 / 2 : ℝ)) * (1 + u) ^ (p : ℝ) * Real.exp (-(ε * u ^ 2)) := by ring
    rcases le_or_gt u 1 with hu1 | hu1
    · have hm : u ∈ Ioc (0 : ℝ) 1 := ⟨hu, hu1⟩
      have hnot : u ∉ Ioi (1 : ℝ) := not_lt.mpr hu1
      have hg0_eq : g0 u = B * 2 ^ (20 : ℕ) * u ^ (-(1 / 2 : ℝ)) := by
        dsimp only [g0]; rw [Set.indicator_of_mem hm, Set.indicator_of_notMem hnot, add_zero]
      rw [hg0_eq]
      have hexp1 : Real.exp (-(ε * u ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
      calc ‖F₀ û u‖ ≤ B * u ^ (-(1 / 2 : ℝ)) * (1 + u) ^ (p : ℝ) * Real.exp (-(ε * u ^ 2)) := hn
        _ ≤ B * u ^ (-(1 / 2 : ℝ)) * (2 : ℝ) ^ (20 : ℕ) * 1 := by have := win_1u_sm hp hu hu1; gcongr
        _ = B * 2 ^ (20 : ℕ) * u ^ (-(1 / 2 : ℝ)) := by ring
    · have hm : u ∈ Ioi (1 : ℝ) := hu1
      have hnot : u ∉ Ioc (0 : ℝ) 1 := fun h => not_le.mpr hu1 h.2
      have hg0_eq : g0 u = C_g * u ^ (-4 : ℝ) := by
        dsimp only [g0]; rw [Set.indicator_of_notMem hnot, Set.indicator_of_mem hm, zero_add]
      rw [hg0_eq]
      have hu12 : u ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu1.le (by norm_num)
      have hupow : u ^ (20 : ℝ) * u ^ (-24 : ℝ) = u ^ (-4 : ℝ) := by
        rw [← Real.rpow_add hu]; congr 1; norm_num
      calc ‖F₀ û u‖ ≤ B * u ^ (-(1 / 2 : ℝ)) * (1 + u) ^ (p : ℝ) * Real.exp (-(ε * u ^ 2)) := hn
        _ ≤ B * 1 * ((2 : ℝ) ^ (20 : ℕ) * u ^ (20 : ℝ)) *
              ((Nat.factorial 12 : ℝ) * ε ^ (-12 : ℤ) * u ^ (-24 : ℝ)) := by
            have := win_1u_lg hp hu1.le; have := win_exp_fac_12 hε0 hu1.le; gcongr
        _ = C_g * (u ^ (20 : ℝ) * u ^ (-24 : ℝ)) := by dsimp [C_g]; ring
        _ = C_g * u ^ (-4 : ℝ) := by rw [hupow]
  have hdiff_eq : fctSEps û₂ ε κ - fctSEps û₁ ε κ =
      ∫ t in û₁..û₂, (-Complex.I) * fctSEps t ε (fun u => (u : ℂ) * κ u) := by
    have hleft : fctSEps û₂ ε κ - fctSEps û₁ ε κ = ∫ u in Ioi 0, ph * (F₀ û₂ u - F₀ û₁ u) := by
      dsimp only [fctSEps, F₀, ph]
      rw [← mul_sub, ← integral_sub (hF0_int û₂) (hF0_int û₁), ← integral_const_mul]
    have hright : ∫ t in Ioc û₁ û₂, (-Complex.I) * fctSEps t ε (fun u => (u : ℂ) * κ u) =
        ∫ t in Ioc û₁ û₂, ∫ u in Ioi 0, F t u := by
      refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
      unfold fctSEps
      rw [← integral_const_mul, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      dsimp only [F, ph]; ring
    rw [hleft, ← setIntegral_congr_fun measurableSet_Ioi hint_t, ← hswap, ← hright,
      intervalIntegral.integral_of_le hle]
  rw [hdiff_eq]
  have hint_const : ∀ t ∈ Set.uIoc û₁ û₂, ‖(-Complex.I) * fctSEps t ε (fun u => (u : ℂ) * κ u)‖ ≤
      (C_u * (2 ^ 8 * 2)) * B := fun t ht => by
    have htm : |t| ≤ M := abs_le.mpr (by
      have hmem : t ∈ Icc û₁ û₂ := Set.uIcc_of_le hle ▸ Ioc_subset_Icc_self ht
      exact ⟨(abs_le.mp hû₁).1.trans hmem.1, hmem.2.trans (abs_le.mp hû₂).2⟩)
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact (hCu t (2 ^ 8 * 2 * B) _ htm (by positivity) hκ' ε hε).trans_eq (by ring)
  calc ‖∫ t in û₁..û₂, (-Complex.I) * fctSEps t ε (fun u => (u : ℂ) * κ u)‖
      ≤ (C_u * (2 ^ 8 * 2)) * B * |û₂ - û₁| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hint_const

lemma win_fctS_û_lipschitz {M : ℝ} {p : ℕ} (hM : 0 < M) (hp : p ≤ 20) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {û₁ û₂ B : ℝ} {κ : ℝ → ℂ},
      |û₁| ≤ M → |û₂| ≤ M → 0 ≤ B → FctSymCls 8 p B κ →
      ‖fctS û₂ κ - fctS û₁ κ‖ ≤ C * B * |û₂ - û₁| := by
  obtain ⟨C_u, hCu0, hCu⟩ := FctSymA.fctInnerSymbolsA_unif M 8 (p + 1) hM (by omega)
    (by linarith [show (p : ℝ) ≤ 20 by exact_mod_cast hp])
  refine ⟨C_u * (2 ^ 8 * 2), by positivity, fun {û₁ û₂ B κ} hû₁ hû₂ hB hκ => ?_⟩
  rcases le_total û₁ û₂ with hle | hle
  · exact win_fctS_û_lipschitz_le hM hp C_u hCu hû₁ hû₂ hle hB hκ
  · rw [norm_sub_rev, abs_sub_comm]
    exact win_fctS_û_lipschitz_le hM hp C_u hCu hû₂ hû₁ hle hB hκ

/-! ### 2. `winMuMix L1 - 1` symbol class bound `O(c^{-4/3})` -/

lemma win_mu_diag_sub_one {K4 : ℝ} (hK4 : 1 ≤ K4) {Cα : ℝ} (hCα : 0 ≤ Cα) :
    ∃ (C_1 c₀ : ℝ), 0 ≤ C_1 ∧ 10000 ≤ c₀ ∧ ∀ {ε c L1 α : ℝ},
      (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      (concreteInnerFamily K4 ε).adm c L1 α → |α| ≤ Cα * c ^ (-(2 / 3 : ℝ)) →
      FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C_1 * c ^ (-(4 / 3 : ℝ)))
        (fun u => winMuMix K4 ε c L1 L1 α u - 1) := by
  let B3_p := concreteInnerB3 (K4 := K4) (ε := 1) hK4
  let B3_m := concreteInnerB3 (K4 := K4) (ε := -1) hK4
  let C3 : ℝ := max (|B3_p.choose|) (|B3_m.choose|)
  let c3 : ℝ := max B3_p.choose_spec.choose B3_m.choose_spec.choose
  let cbase : ℝ := max 10000 ((30 * pbC0 + 1) ^ 2)
  have hc_ev : ∀ᶠ c : ℝ in atTop,
      cbase ≤ c ∧ c3 ≤ c ∧ pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) ≤ 0.5 := by
    refine Eventually.and (eventually_ge_atTop cbase) (Eventually.and (eventually_ge_atTop c3) ?_)
    have ht : Tendsto (fun c : ℝ => pbcV * pbC0 * c ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
      simpa [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _
    exact ht.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 0.5))
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.mp hc_ev
  let C_1 : ℝ := C3 + 9 * 2 ^ 10 * Cα
  refine ⟨C_1, max 10000 c₀, by positivity, le_max_left _ _, fun {ε c L1 α} hε hc hadm hα => ?_⟩
  obtain ⟨hcbase, hcc3, hV0_sm⟩ := hc₀ c ((le_max_right _ _).trans hc)
  have hfacts' : max 100 ((30 * pbC0 + 1) ^ 2) ≤ c :=
    le_trans (max_le_max (by norm_num) le_rfl) hcbase
  have hfc := concrete_adm_facts hfacts' hadm
  have hc0 : 0 < c := hfc.1
  have hDu := uniqueDiffOn_Icc (fctUc_pos hc0)
  have hb3 : FctSymClsOn (Icc 0 (fctUc c)) 8 10 (C3 * c ^ (-(4 / 3 : ℝ)))
      (fun u => (concreteInnerFamily K4 ε).mu c L1 α u - 1 -
        ((c ^ (-(2 / 3 : ℝ)) * α * (concreteInnerFamily K4 ε).c2 c L1 α * u ^ 2 : ℝ) : ℂ)) := by
    rcases hε with rfl | rfl
    · have h0 := B3_p.choose_spec.choose_spec c ((le_max_left _ _).trans hcc3) L1 α hadm
      exact h0.mono_B Icc_subset_Ici_self
        (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_max_left _ _)) (by positivity))
    · have h0 := B3_m.choose_spec.choose_spec c ((le_max_right _ _).trans hcc3) L1 α hadm
      exact h0.mono_B Icc_subset_Ici_self
        (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_max_right _ _)) (by positivity))
  have hc2_bd : |(concreteInnerFamily K4 ε).c2 c L1 α| ≤ 9 := by
    dsimp only [concreteInnerFamily]
    have hV0_abs := abs_le.mp (hfc.2.2.2.2.2.2.2.2.2.2.2.trans hV0_sm)
    have hτs_lt : warpTauStar < 2 := by
      have h12 : (12 : ℝ) / π ^ 2 < 8 := by rw [div_lt_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three]
      calc warpTauStar < (8 : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_lt_rpow (by positivity) h12 (by norm_num)
        _ = 2 := by
            rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast,
              ← Real.rpow_mul (by norm_num)]; norm_num
    have hV0_eq := (hfc.2.2.2.2.2.2.2.2.2.1.2 0 ⟨le_rfl, by norm_num⟩).symm
    have hV0_2 : |concreteInnerV K4 ε c L1 α 0| ≤ 3 := by
      have hτs0 := warpTauStar_ge
      rw [show (12 / π ^ 2) ^ (1 / 3 : ℝ) = warpTauStar from rfl] at hV0_abs
      rw [abs_le]; constructor <;> linarith only [hV0_abs.1, hV0_abs.2, hτs_lt, hτs0]
    have h243 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    change |(2 : ℝ) ^ (-(4 / 3 : ℝ)) * ((concreteBoxS K4 ε c).V ((concreteEll1 ε c L1, 1, α), 0)) ^ 2| ≤ 9
    rw [hV0_eq, abs_mul, abs_of_pos (by positivity), abs_sq, ← sq_abs]
    calc (2 : ℝ) ^ (-(4 / 3 : ℝ)) * |concreteInnerV K4 ε c L1 α 0| ^ 2 ≤ 1 * 3 ^ 2 := by gcongr
      _ = 9 := by norm_num
  have hc2_fac : |c ^ (-(2 / 3 : ℝ)) * α * (concreteInnerFamily K4 ε).c2 c L1 α| ≤
      9 * Cα * c ^ (-(4 / 3 : ℝ)) := by
    have hc43 : c ^ (-(2 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) = c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hc0 _)]
    calc c ^ (-(2 / 3 : ℝ)) * |α| * |(concreteInnerFamily K4 ε).c2 c L1 α|
        ≤ c ^ (-(2 / 3 : ℝ)) * (Cα * c ^ (-(2 / 3 : ℝ))) * 9 := by gcongr
      _ = 9 * Cα * c ^ (-(4 / 3 : ℝ)) := by
          rw [show c ^ (-(2 / 3 : ℝ)) * (Cα * c ^ (-(2 / 3 : ℝ))) * 9 =
            9 * Cα * (c ^ (-(2 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ))) by ring, hc43]
  have hu2_on : FctSymClsOn (Icc 0 (fctUc c)) 8 10 (2 ^ 10) (fun u : ℝ => ((u ^ 2 : ℝ) : ℂ)) := by
    have hsq := (win_id_symCls.mul Set.Subset.rfl (uniqueDiffOn_Ici 0) win_id_symCls).mono_set
      Icc_subset_Ici_self hDu (uniqueDiffOn_Ici 0)
    have hsq' : FctSymClsOn (Icc 0 (fctUc c)) 8 10 (2 ^ 10) (fun u : ℝ => (u : ℂ) * (u : ℂ)) :=
      (hsq.mono_p Icc_subset_Ici_self (by positivity) (by norm_num : (1 + 1 : ℝ) ≤ 10)).mono_B
        Icc_subset_Ici_self (by norm_num)
    exact FctSymClsOn.congr hDu hsq' fun u _ => by push_cast; ring
  let c2f : ℝ := c ^ (-(2 / 3 : ℝ)) * α * (concreteInnerFamily K4 ε).c2 c L1 α
  have hlin_on : FctSymClsOn (Icc 0 (fctUc c)) 8 10 (9 * 2 ^ 10 * Cα * c ^ (-(4 / 3 : ℝ)))
      (fun u : ℝ => ((c2f * u ^ 2 : ℝ) : ℂ)) := by
    have hc : FctSymClsOn (Icc 0 (fctUc c)) 8 10 (‖(c2f : ℂ)‖ * 2 ^ 10)
        (fun u : ℝ => ((c2f * u ^ 2 : ℝ) : ℂ)) :=
      FctSymClsOn.congr hDu (FctSymClsOn.const_mul hDu (c2f : ℂ) hu2_on)
        fun u _ => by push_cast; ring
    refine hc.mono_B Icc_subset_Ici_self ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc |c2f| * 2 ^ 10 ≤ (9 * Cα * c ^ (-(4 / 3 : ℝ))) * 2 ^ 10 := by gcongr
      _ = 9 * 2 ^ 10 * Cα * c ^ (-(4 / 3 : ℝ)) := by ring
  have hadd := hb3.add hDu hlin_on
  have hfinal : FctSymClsOn (Icc 0 (fctUc c)) 8 10 ((C3 + 9 * 2 ^ 10 * Cα) * c ^ (-(4 / 3 : ℝ)))
      (fun u => winMuMix K4 ε c L1 L1 α u - 1) := by
    refine (FctSymClsOn.congr hDu hadd fun u _ => ?_).mono_B Icc_subset_Ici_self
      (le_of_eq (by ring))
    dsimp only [c2f]; rw [winMuMix_diag_eq]; push_cast; ring
  exact hfinal

end FormalResearch.SignUncertainty
