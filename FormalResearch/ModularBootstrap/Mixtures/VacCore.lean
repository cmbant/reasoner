module

public import FormalResearch.ModularBootstrap.Mixtures.VacWindow

/-!
# `pmix:vac`, vacuum part: the vacuum core of the bumped `f = 1` designs for a common source

`positive_mixtures.tex`, Proposition PM.9 (`pmix:vac`), second limit of `pmix:fixed-transfer`, `(f, r) = (1, 0)`; this is
`vacuum_core_bumped` (W-P5, `ut:Vac`, `fw:e3.6`) for the weight `V_s = C.src.cardyV (c'/12)` of a `CommonSource`.

The pieces of the W-P5 proof are re-run for `V_s`; the weight enters only through

* the deep lobe: `h^{(p)} V_s ≤ 0` for `x < ξ_* - λ n` (`h ≤ 0` there by `sig_lobe_nonpos` at `triv` and `V_t > 0`, `R_bump ≥ 1`, `V_s ≥ 0`);
* the window: `bump_part1_src` (comparison on compact `σ`-windows);
* the band and the far band: `|h^{(p)}| V_s ≤ ‖λ‖_TV |h^{(p)}| V_t` (`cmp_global`) and Lemma `T` at `triv`
  (`lemma_T_sig1_prob_mul` with the multiplier `R_bump ∈ [0, K_b]`), the constants `‖λ‖_TV C_T/A(ξ_*)` and `‖λ‖_TV C_far`.

* `vacuum_core_bumped_src`: `∫_0^∞ h^{(p)} V_s dt ≤ FK^{mix}_c (C_* V_D + ε)`, uniformly in the cut `N' ≥ N`.

All results are proved unconditionally.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Mixtures

open Real Filter Topology Set MeasureTheory
open scoped Real
open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight FormalResearch.ModularBootstrap.Upper.Window.Cardy
  FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Rigidity
  FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Positivity
  FormalResearch.ModularBootstrap.Upper.Assembly FormalResearch.ModularBootstrap.Upper.Bump
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Holes FormalResearch.Special

/-- **Vacuum core of the bumped `f = 1` designs for a common source** (`pmix:vac`, second limit): for every `ε > 0`, `c'` large and
every cut `N' ≥ N`, `∫_0^∞ h^{(p)} V_s dt ≤ FK^{mix}_c (C_* V_D + ε)`, `V_D = windowIntegralSig N η σs`. -/
theorem vacuum_core_bumped_src (C : CommonSource) (d : BumpData) (N : ℕ) (hN : 1 ≤ N) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c' in atTop, ∀ N' : ℕ, N ≤ N' →
      ∫ t in Ioi 0, combProfile c' (bumpSigComb d c' N N' η σs) t * C.src.cardyV (c' / 12) t ≤
        FKc C.src.qMix 1 c' * (CStar * windowIntegralSig N η σs + ε) := by
  have hξ := xiStar_pos
  have hAs := C.ampl_pos hξ
  have htv := (C.at_ (le_refl C.a₀)).tv_pos
  set tv : ℝ := C.src.tv with htvdef
  set As : ℝ := C.src.ampl xiStar with hAsdef
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k, 1 ≤ k → k ≤ N → |σs k| ≤ M :=
    ⟨∑ k ∈ Finset.Icc 1 N, |σs k|, fun k hk hkN =>
      Finset.single_le_sum (f := fun j => |σs j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_Icc.mpr ⟨hk, hkN⟩)⟩
  obtain ⟨N₂, C_T, C_far, hCT, hCf, hT⟩ := lemma_T_sig1_prob_mul C.src.triv (r₀ := 3 / 10) (by norm_num) N hN
    hη0 hη1 σs M hM (bumpC d (1 / 4)) (bumpC_pos d _).le
  have hCT' : 0 ≤ tv / As * C_T := by positivity
  obtain ⟨n, hn1, hn2, hn3, hn4⟩ :=
    (eventually_n_choice_sig N₂ (C_T := tv / As * C_T) hε N hN η σs).exists
  have hn1' : 1 ≤ n := by have := (le_max_left 4 N₂).trans hn1; omega
  have hΦ0 : 0 ≤ phiWKB (n + 1) := phiWKB_nonneg (by omega)
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hwc := continuous_windowLimit_sig N hN η σs
  obtain ⟨e1, he1⟩ : ∃ e1 : ℝ, e1 = ε / 4 / (phiWKB (n + 1) + n + 1) := ⟨_, rfl⟩
  have he1pos : 0 < e1 := by rw [he1]; positivity
  have he1le : e1 * (phiWKB (n + 1) + n) ≤ ε / 4 := by
    rw [he1, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  filter_upwards [bump_part1_src C d N hN hη0 hη1 σs hnR n he1pos,
    sig_lobe_nonpos C.src.triv N σs hn2, hT n hn1,
    bumpFactor_one_le d (η₀ := 1 / 4) (by norm_num) le_rfl,
    bumpFactor_le d (η₀ := 1 / 4) (by norm_num) le_rfl, combProfile_bumped_eq d,
    bumpSig_integrand_props C.src.triv d N hN hη0 hη1 σs,
    bumpSig_phaseHyp d N hN hη0 hη1 σs,
    designComb_innerCombHyp_of_admissible 1 le_rfl (η₀ := 1 / 4) (by norm_num) (by norm_num),
    FKc_ge_mul_sqrt_of_pos C.qMix_pos (tv * C_far / (ε / 4)),
    lambda_mul_le (n : ℝ) (half_pos xiStar_pos),
    lambda_mul_le (phiWKB (n + 1)) (by norm_num : (0 : ℝ) < 3 / 10),
    eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (12 * C.a₀)]
    with c' hwin hneg hTc hR1 hRle hval hprops hph hin hFKbig hln hlΦ hcpos hcA N' hNN'
  have hlpos := lambdaComb_pos' hcpos
  have hcA' : C.a₀ ≤ c' / 12 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 12)]
    linarith
  have hAt : C.F.At (c' / 12) := C.at_ hcA'
  have hFKt := FKc_pos (qProb_pos C.src.triv) 1 hcpos
  have hFKs : FKc C.src.qMix 1 c' = As * FKc (qProb C.src.triv) 1 c' := FKc_qMix C.src c'
  have hFKpos := FKc_pos C.qMix_pos 1 hcpos
  -- geometry
  have ha : (1 / 4 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
    linarith
  have hχ1 : xiStar ≤ chiQuantile c' ((n + 1 : ℕ) : ℝ) := (chiQuantile_spec hcpos ha).1
  have hχ2 : chiQuantile c' ((n + 1 : ℕ) : ℝ) ≤ xiStar + lambdaComb c' * phiWKB (n + 1) := by
    have h := (siteRadius_bounds hcpos ha).2
    unfold siteRadius at h
    rw [phiWKB_eq_phiQuantile (n + 1)]
    linarith
  have hy0 : 0 ≤ xiStar + lambdaComb c' * (-(n : ℝ)) := by linarith
  have hy1 : 0 ≤ xiStar + lambdaComb c' * phiWKB (n + 1) := by
    have := mul_nonneg hlpos.le hΦ0
    linarith
  have hSΦ : c' * (xiStar + lambdaComb c' * (-(n : ℝ))) ^ 2 / 3 ≤
      c' * (xiStar + lambdaComb c' * phiWKB (n + 1)) ^ 2 / 3 := by
    have h1 : xiStar + lambdaComb c' * (-(n : ℝ)) ≤ xiStar + lambdaComb c' * phiWKB (n + 1) := by
      have := mul_le_mul_of_nonneg_left (show -(n : ℝ) ≤ phiWKB (n + 1) by linarith) hlpos.le
      linarith
    have := pow_le_pow_left₀ hy0 h1 2
    nlinarith only [mul_le_mul_of_nonneg_left this hcpos.le]
  have hNΦ : c' * chiQuantile c' ((n + 1 : ℕ) : ℝ) ^ 2 / 3 ≤
      c' * (xiStar + lambdaComb c' * phiWKB (n + 1)) ^ 2 / 3 := by
    have := pow_le_pow_left₀ (by linarith) hχ2 2
    nlinarith only [mul_le_mul_of_nonneg_left this hcpos.le]
  have hΦR : c' * (xiStar + lambdaComb c' * phiWKB (n + 1)) ^ 2 / 3 ≤ c' * (xiStar + 3 / 10) ^ 2 / 3 := by
    have := pow_le_pow_left₀ hy1 (show xiStar + lambdaComb c' * phiWKB (n + 1) ≤ xiStar + 3 / 10 by linarith) 2
    nlinarith only [mul_le_mul_of_nonneg_left this hcpos.le]
  have hN0 : 0 < c' * chiQuantile c' ((n + 1 : ℕ) : ℝ) ^ 2 / 3 := by
    have := lt_of_lt_of_le hξ hχ1
    positivity
  have hS0 : 0 ≤ c' * (xiStar + lambdaComb c' * (-(n : ℝ))) ^ 2 / 3 := by positivity
  -- the integrands
  obtain ⟨hcontP, hintP⟩ := hprops N' hNN'
  obtain ⟨hfN, hA, -⟩ := hph N' hNN'
  have hI : InnerCombHyp c' (bumpSigComb d c' N N' η σs) := hin N' _ _ hfN hA
  have hcontH := hI.continuousOn_combProfile hcpos
  set F : ℝ → ℝ := fun t => combProfile c' (bumpSigComb d c' N N' η σs) t * C.src.cardyV (c' / 12) t with hF
  set P : ℝ → ℝ := fun t => combProfile c' (bumpSigComb d c' N N' η σs) t *
    C.src.triv.cardyV (c' / 12) t with hP
  have hcontF : ContinuousOn F (Ici 0) :=
    hcontH.mul (C.src.continuous_cardyV (c' / 12)).continuousOn
  have hFP : ∀ t, 0 ≤ t → |F t| ≤ tv * |P t| := by
    intro t ht
    obtain ⟨hV0, hVle⟩ := cmp_global (C := C) (c' := c') hcA' ht
    have hVt0 : 0 ≤ C.src.triv.cardyV (c' / 12) t := triv_cardyV_nonneg C.src hcpos ht
    simp only [hF, hP]
    rw [abs_mul, abs_mul, abs_of_nonneg hV0, abs_of_nonneg hVt0]
    calc |combProfile c' (bumpSigComb d c' N N' η σs) t| * C.src.cardyV (c' / 12) t
        ≤ |combProfile c' (bumpSigComb d c' N N' η σs) t| * (tv * C.src.triv.cardyV (c' / 12) t) :=
          mul_le_mul_of_nonneg_left hVle (abs_nonneg _)
      _ = tv * (|combProfile c' (bumpSigComb d c' N N' η σs) t| * C.src.triv.cardyV (c' / 12) t) := by ring
  have hintF : IntegrableOn F (Ioi 0) := by
    refine (hintP.abs.const_mul tv).mono' ?_ ?_
    · exact (hcontF.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs]
      exact hFP t (le_of_lt ht)
  have hFabs : IntegrableOn (fun t => |F t|) (Ioi 0) := hintF.abs
  have hPabsI : IntegrableOn (fun t => tv * |P t|) (Ioi 0) := hintP.abs.const_mul tv
  -- the deep lobe
  have hneg' : ∀ t ∈ Ioc 0 (c' * (xiStar + lambdaComb c' * (-(n : ℝ))) ^ 2 / 3), F t ≤ 0 := by
    intro t ht
    have h1 := hneg t ht
    have hVt : 0 < C.src.triv.cardyV (c' / 12) t := triv_cardyV_pos hcpos ht.1
    have hv := hval N N' σs (designWidth1 c' η) hN hNN' t
    have hh : combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t ≤ 0 := by
      by_contra hpos
      push Not at hpos
      have := mul_pos hpos hVt
      exact absurd h1 (not_le.mpr this)
    have e : combProfile c' (bumpSigComb d c' N N' η σs) t =
        bumpFactor d c' (1 / 4) N N' (xOf c' t) *
          combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t := hv
    have hR0 : 0 ≤ bumpFactor d c' (1 / 4) N N' (xOf c' t) := by linarith only [hR1 N N' (xOf c' t)]
    have hV0 := (cmp_global (C := C) (c' := c') hcA' ht.1.le).1
    simp only [hF]
    rw [e]
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hR0 hh) hV0
  have hsplit := split_integral_le (F := F) hS0 hN0 hSΦ hNΦ hΦR hintF hneg'
  -- window
  have hwin' := window_part_le (c' := c') (FK := FKc C.src.qMix 1 c') (ε' := e1) (S := (n : ℝ))
    (Φ := phiWKB (n + 1)) hcpos.le hcontF hwc (by linarith) (fun σ hσ => by
      have hb := hwin N' hNN' σ hσ
      rw [tildeW_sigMod N hN η σs σ]
      have hb2 := (div_le_iff₀ hFKpos).mp (sub_le_iff_le_add.mp (abs_le.mp hb).2)
      show combProfile c' (bumpSigComb d c' N N' η σs) (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) *
          C.src.cardyV (c' / 12) (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) *
          ((2 * c' * (xiStar + lambdaComb c' * σ) / 3) * lambdaComb c') ≤ _
      calc _ ≤ (e1 + CStar * kappaAiry * sigWinW N η σs (-kappaAiry * σ)) * FKc C.src.qMix 1 c' := hb2
        _ = _ := by unfold sigWinW; ring)
  -- band and far band
  obtain ⟨hband0, hfar0⟩ := hTc (fun t => bumpFactor d c' (1 / 4) N N' (xOf c' t))
    (fun t => ⟨by linarith only [hR1 N N' (xOf c' t)], hRle N N' (xOf c' t) (xOf_nonneg c' t)⟩)
  have hPabs : ∀ t, 0 ≤ t → |P t| = bumpFactor d c' (1 / 4) N N' (xOf c' t) *
      (|combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t| *
        C.src.triv.cardyV (c' / 12) t) := by
    intro t ht
    have hv := hval N N' σs (designWidth1 c' η) hN hNN' t
    have e : combProfile c' (bumpSigComb d c' N N' η σs) t =
        bumpFactor d c' (1 / 4) N N' (xOf c' t) *
          combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t := hv
    have hR0 : 0 ≤ bumpFactor d c' (1 / 4) N N' (xOf c' t) := by linarith only [hR1 N N' (xOf c' t)]
    have hVt0 : 0 ≤ C.src.triv.cardyV (c' / 12) t := triv_cardyV_nonneg C.src hcpos ht
    simp only [hP]
    rw [e, abs_mul, abs_mul, abs_of_nonneg hR0, abs_of_nonneg hVt0]
    ring
  have hsubI : Icc (c' * chiQuantile c' ((n + 1 : ℕ) : ℝ) ^ 2 / 3) (c' * (xiStar + 3 / 10) ^ 2 / 3) ⊆ Ioi 0 :=
    fun t ht => lt_of_lt_of_le hN0 ht.1
  have hband : (∫ t in Icc (c' * chiQuantile c' ((n + 1 : ℕ) : ℝ) ^ 2 / 3) (c' * (xiStar + 3 / 10) ^ 2 / 3),
      |F t|) ≤ FKc C.src.qMix 1 c' * (tv / As * C_T * (n : ℝ) ^ (-(1 / 3 : ℝ))) := by
    calc (∫ t in Icc (c' * chiQuantile c' ((n + 1 : ℕ) : ℝ) ^ 2 / 3) (c' * (xiStar + 3 / 10) ^ 2 / 3), |F t|)
        ≤ ∫ t in Icc (c' * chiQuantile c' ((n + 1 : ℕ) : ℝ) ^ 2 / 3) (c' * (xiStar + 3 / 10) ^ 2 / 3),
            tv * |P t| :=
          setIntegral_mono_on (hFabs.mono_set hsubI) (hPabsI.mono_set hsubI)
            measurableSet_Icc (fun t ht => hFP t (le_trans hN0.le ht.1))
      _ = tv * ∫ t in Icc (c' * chiQuantile c' ((n + 1 : ℕ) : ℝ) ^ 2 / 3) (c' * (xiStar + 3 / 10) ^ 2 / 3),
            |P t| := integral_const_mul _ _
      _ = tv * ∫ t in Icc (c' * chiQuantile c' ((n + 1 : ℕ) : ℝ) ^ 2 / 3) (c' * (xiStar + 3 / 10) ^ 2 / 3),
            bumpFactor d c' (1 / 4) N N' (xOf c' t) *
              (|combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t| *
                C.src.triv.cardyV (c' / 12) t) := by
          congr 1
          exact setIntegral_congr_fun measurableSet_Icc fun t ht => hPabs t (le_trans hN0.le ht.1)
      _ ≤ tv * (FKc (qProb C.src.triv) 1 c' * C_T * (n : ℝ) ^ (-(1 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_left hband0 htv.le
      _ = FKc C.src.qMix 1 c' * (tv / As * C_T * (n : ℝ) ^ (-(1 / 3 : ℝ))) := by
          rw [hFKs]; field_simp
  have hRpos : 0 < c' * (xiStar + 3 / 10) ^ 2 / 3 := by positivity
  have hfar : (∫ t in Ici (c' * (xiStar + 3 / 10) ^ 2 / 3), |F t|) ≤ ε / 4 * FKc C.src.qMix 1 c' := by
    have hsubR : Ici (c' * (xiStar + 3 / 10) ^ 2 / 3) ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le hRpos ht
    calc (∫ t in Ici (c' * (xiStar + 3 / 10) ^ 2 / 3), |F t|)
        ≤ ∫ t in Ici (c' * (xiStar + 3 / 10) ^ 2 / 3), tv * |P t| :=
          setIntegral_mono_on (hFabs.mono_set hsubR) (hPabsI.mono_set hsubR)
            measurableSet_Ici (fun t ht => hFP t (le_trans hRpos.le ht))
      _ = tv * ∫ t in Ici (c' * (xiStar + 3 / 10) ^ 2 / 3), |P t| := integral_const_mul _ _
      _ = tv * ∫ t in Ici (c' * (xiStar + 3 / 10) ^ 2 / 3),
            bumpFactor d c' (1 / 4) N N' (xOf c' t) *
              (|combProfile c' (designComb c' 1 N (1 / 4) σs (designWidth1 c' η)) t| *
                C.src.triv.cardyV (c' / 12) t) := by
          congr 1
          exact setIntegral_congr_fun measurableSet_Ici fun t ht => hPabs t (le_trans hRpos.le ht)
      _ ≤ tv * (C_far * √c') := mul_le_mul_of_nonneg_left hfar0 htv.le
      _ ≤ ε / 4 * FKc C.src.qMix 1 c' := by
          have h := mul_le_mul_of_nonneg_left hFKbig (show 0 ≤ ε / 4 by positivity)
          have e : ε / 4 * (tv * C_far / (ε / 4) * √c') = tv * (C_far * √c') := by field_simp
          calc tv * (C_far * √c') = ε / 4 * (tv * C_far / (ε / 4) * √c') := e.symm
            _ ≤ ε / 4 * FKc C.src.qMix 1 c' := h
  exact final_arith hFKpos hsplit hwin' hn4 he1le hband hn3 hfar

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.vacuum_core_bumped_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vacuum_core_bumped_src

end FormalResearch.ModularBootstrap.Mixtures
