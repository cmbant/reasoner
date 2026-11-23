module

public import FormalResearch.ModularBootstrap.Upper.Positivity.VacuumDesign

/-!
# Proposition V: `V_c ≤ FK_c (C_* V_D + ε)` (`ut:Vac`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, proof of Proposition V (`ut:Vac`): for the designs
`D(N, η_*, d)` and every `ε > 0`, for large `c'`,
`V_c := ∫_0^∞ h₀ V dt ≤ FK_c^{(1)} (C_* V_D + ε)`, `V_D = ∫_ℝ W du`.

Proof (as in the paper): `split_integral_le` drops the negative lobe `x < ξ_* - S λ` (`design_lobe_nonpos`),
keeps the window `[-S, Φ_{N₁+1}]` (`lemma_W_measure`, `tildeW_designMod`, `window_part_le`) and bounds the
intermediate band by `FK_c C_T N₁^{-1/3}` and the far band by `C_far √c'` (`lemma_T_design1`), with
`FK_c ≫ √c'` (`FKc_ge_mul_sqrt`).  `S = N₁ = n` is taken large so that `∫_{-n}^{Φ_{n+1}} W̃ → C_* V_D`
(`windowLimit_integral_tendsto`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Positivity

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Window.Cardy FormalResearch.ModularBootstrap.Upper.Holes
  FormalResearch.ModularBootstrap.Upper.Membership FormalResearch.ModularBootstrap.Upper.Window.Tail

lemma continuous_windowLimit_sig (N : ℕ) (hN : 1 ≤ N) (η : ℝ) (σs : ℕ → ℝ) :
    Continuous fun σ : ℝ => tildeW 1 (sigMod N η σs).sigmaFLim (sigMod N η σs).allSigmaLim
      (sigMod N η σs).allEpsLim σ := by
  have : (fun σ : ℝ => tildeW 1 (sigMod N η σs).sigmaFLim (sigMod N η σs).allSigmaLim
      (sigMod N η σs).allEpsLim σ) =
      fun σ : ℝ => CStar * kappaAiry * (sigWindowW N η σs ((-kappaAiry * σ : ℝ) : ℂ)).re :=
    funext fun σ => tildeW_sigMod N hN η σs σ
  rw [this]
  exact continuous_const.mul ((continuous_sigWindowRe hN η σs).comp (by fun_prop))

lemma continuous_windowLimit (N : ℕ) (hN : 1 ≤ N) (η d : ℝ) :
    Continuous fun σ : ℝ => tildeW 1 (designMod N η d).sigmaFLim (designMod N η d).allSigmaLim
      (designMod N η d).allEpsLim σ :=
  continuous_windowLimit_sig N hN η (designSigma1 d)

lemma eventually_n_choice_sig (N₂ : ℕ) {C_T ε : ℝ} (hε : 0 < ε) (N : ℕ) (hN : 1 ≤ N) (η : ℝ) (σs : ℕ → ℝ) :
    ∀ᶠ n : ℕ in atTop, max 4 N₂ ≤ n ∧ |σs 1| < n ∧
      C_T * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ ε / 4 ∧
      (∫ σ in (-(n : ℝ))..(phiWKB (n + 1)),
        tildeW 1 (sigMod N η σs).sigmaFLim (sigMod N η σs).allSigmaLim
          (sigMod N η σs).allEpsLim σ) ≤ CStar * windowIntegralSig N η σs + ε / 4 := by
  have h1 := eventually_ge_atTop (max 4 N₂)
  have h2 : ∀ᶠ n : ℕ in atTop, |σs 1| < n :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop _
  have h3 : ∀ᶠ n : ℕ in atTop, C_T * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ ε / 4 := by
    have := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop).const_mul C_T
    rw [mul_zero] at this
    exact this.eventually_le_const (by positivity)
  have h4 : ∀ᶠ n : ℕ in atTop, (∫ σ in (-(n : ℝ))..(phiWKB (n + 1)),
        tildeW 1 (sigMod N η σs).sigmaFLim (sigMod N η σs).allSigmaLim
          (sigMod N η σs).allEpsLim σ) ≤ CStar * windowIntegralSig N η σs + ε / 4 :=
    (windowLimit_integral_tendsto_sig N hN η σs).eventually_le_const
      (by linarith [show 0 < ε / 4 by positivity] : CStar * windowIntegralSig N η σs <
        CStar * windowIntegralSig N η σs + ε / 4)
  filter_upwards [h1, h2, h3, h4] with n a b c e
  exact ⟨a, b, c, e⟩

lemma eventually_n_choice (N₂ : ℕ) {C_T ε : ℝ} (hε : 0 < ε) (N : ℕ) (hN : 1 ≤ N) (η d : ℝ) :
    ∀ᶠ n : ℕ in atTop, max 4 N₂ ≤ n ∧ |designSigma1 d 1| < n ∧
      C_T * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ ε / 4 ∧
      (∫ σ in (-(n : ℝ))..(phiWKB (n + 1)),
        tildeW 1 (designMod N η d).sigmaFLim (designMod N η d).allSigmaLim
          (designMod N η d).allEpsLim σ) ≤ CStar * windowIntegralVD N η d + ε / 4 :=
  by
  simp only [windowIntegralVD_eq_sig]
  exact eventually_n_choice_sig N₂ hε N hN η (designSigma1 d)

lemma final_arith {FK I Wi Bd Fr L A e1 T ε : ℝ} (hFK : 0 < FK) (h1 : I ≤ Wi + Bd + Fr)
    (h2 : Wi ≤ FK * (A + e1)) (hA : A ≤ L + ε / 4) (he1 : e1 ≤ ε / 4) (h3 : Bd ≤ FK * T)
    (hT : T ≤ ε / 4) (h4 : Fr ≤ ε / 4 * FK) : I ≤ FK * (L + ε) := by
  have a1 := mul_le_mul_of_nonneg_left (show A + e1 ≤ L + ε / 2 by linarith) hFK.le
  have a2 := mul_le_mul_of_nonneg_left hT hFK.le
  nlinarith

lemma abs_profile_mul {c' : ℝ} (hc24 : 24 ≤ c') (cp : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    |cp t * Crossing.virasoroProblem.cardyV (c' / 12) t| =
      |cp t| * Crossing.virasoroProblem.cardyV (c' / 12) t := by
  rw [abs_mul, abs_of_nonneg (Crossing.virasoroProblem.cardyV_nonneg
    (by rw [Crossing.virasoroProblem_totalShift]; linarith) ht)]

/-- `V_c ≤ FK_c (C_* V + ε)` for the `f = 1` finite modifications with arbitrary offsets `σs`
(`V = windowIntegralSig`): see `vacuum_core`, the case `σs = designSigma1 d`. -/
theorem vacuum_core_sig (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (σs : ℕ → ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ c' in atTop,
      ∫ t in Ioi 0, combProfile c' (designComb c' 1 N (1 / 4) (σs) (designWidth1 c' η)) t *
          Crossing.virasoroProblem.cardyV (c' / 12) t ≤
        FKc 1 1 c' * (CStar * windowIntegralSig N η σs + ε) := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k, 1 ≤ k → k ≤ N → |σs k| ≤ M :=
    ⟨∑ k ∈ Finset.Icc 1 N, |σs k|, fun k hk hkN =>
      Finset.single_le_sum (f := fun j => |σs j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_Icc.mpr ⟨hk, hkN⟩)⟩
  obtain ⟨N₂, C_T, C_far, hCT, hCf, hT⟩ := lemma_T_sig1 (r₀ := 3 / 10) (by norm_num) N hN hη0 hη1
    σs M hM
  obtain ⟨n, hn1, hn2, hn3, hn4⟩ := (eventually_n_choice_sig N₂ (C_T := C_T) hε N hN η σs).exists
  have hn1' : 1 ≤ n := by have := (le_max_left 4 N₂).trans hn1; omega
  have hΦ0 : 0 ≤ phiWKB (n + 1) := phiWKB_nonneg (by omega)
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨e1, he1⟩ : ∃ e1 : ℝ, e1 = ε / 4 / (phiWKB (n + 1) + n + 1) := ⟨_, rfl⟩
  have he1pos : 0 < e1 := by rw [he1]; positivity
  have he1le : e1 * (phiWKB (n + 1) + n) ≤ ε / 4 := by
    rw [he1, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [show 0 < ε by exact hε]
  filter_upwards [sig_window_pointwise N hN hη0 hη1 σs (S := n) hnR n he1pos,
    sig_lobe_nonpos N σs hn2, hT n hn1, sig_integrand_props N hN hη0 hη1 σs M hM,
    FKc_ge_mul_sqrt (C_far / (ε / 4)), lambda_mul_le (n : ℝ) (half_pos xiStar_pos),
    lambda_mul_le (phiWKB (n + 1)) (by norm_num : (0 : ℝ) < 3 / 10), eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (24 : ℝ)]
    with c' hpw hneg hTc hprops hFKbig hln hlΦ hcpos hc24
  obtain ⟨hcont, hint⟩ := hprops
  have hxi := xiStar_pos
  have hlpos := lambdaComb_pos' hcpos
  have hFK := FKc_pos (q := 1) one_pos 1 hcpos
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
    nlinarith
  have hNΦ : c' * chiQuantile c' ((n + 1 : ℕ) : ℝ) ^ 2 / 3 ≤
      c' * (xiStar + lambdaComb c' * phiWKB (n + 1)) ^ 2 / 3 := by
    have := pow_le_pow_left₀ (by linarith) hχ2 2
    nlinarith
  have hΦR : c' * (xiStar + lambdaComb c' * phiWKB (n + 1)) ^ 2 / 3 ≤ c' * (xiStar + 3 / 10) ^ 2 / 3 := by
    have := pow_le_pow_left₀ hy1 (show xiStar + lambdaComb c' * phiWKB (n + 1) ≤ xiStar + 3 / 10 by linarith) 2
    nlinarith
  have hsplit := split_integral_le (F := fun t => combProfile c'
      (designComb c' 1 N (1 / 4) (σs) (designWidth1 c' η)) t *
      Crossing.virasoroProblem.cardyV (c' / 12) t)
    (by positivity) (by have := lt_of_lt_of_le hxi hχ1; positivity) hSΦ hNΦ hΦR hint hneg
  have hw := continuous_windowLimit_sig N hN η σs
  have hwin := window_part_le (c' := c') (FK := FKc 1 1 c') (ε' := e1) (S := (n : ℝ))
    (Φ := phiWKB (n + 1)) hcpos.le hcont hw (by linarith) (fun σ hσ => by
      rw [tildeW_sigMod N hN η σs σ]
      exact hpw σ hσ)
  have hband : (∫ t in Icc (c' * chiQuantile c' ((n + 1 : ℕ) : ℝ) ^ 2 / 3) (c' * (xiStar + 3 / 10) ^ 2 / 3),
      |combProfile c' (designComb c' 1 N (1 / 4) (σs) (designWidth1 c' η)) t *
        Crossing.virasoroProblem.cardyV (c' / 12) t|) ≤ FKc 1 1 c' * C_T * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    refine le_of_eq_of_le (setIntegral_congr_fun measurableSet_Icc fun t ht => ?_) hTc.1
    exact abs_profile_mul hc24 _ (le_trans (by have := lt_of_lt_of_le hxi hχ1; positivity) ht.1)
  have hfar : (∫ t in Ici (c' * (xiStar + 3 / 10) ^ 2 / 3),
      |combProfile c' (designComb c' 1 N (1 / 4) (σs) (designWidth1 c' η)) t *
        Crossing.virasoroProblem.cardyV (c' / 12) t|) ≤ C_far * √c' := by
    refine le_of_eq_of_le (setIntegral_congr_fun measurableSet_Ici fun t ht => ?_) hTc.2
    exact abs_profile_mul hc24 _ (le_trans (by positivity) ht)
  have hsc : 0 < √c' := Real.sqrt_pos.mpr hcpos
  have hfk4 : C_far * √c' ≤ ε / 4 * FKc 1 1 c' := by
    have h := mul_le_mul_of_nonneg_left hFKbig (show 0 ≤ ε / 4 by positivity)
    have e : ε / 4 * (C_far / (ε / 4) * √c') = C_far * √c' := by field_simp
    linarith
  refine final_arith hFK hsplit hwin hn4 he1le (by simpa [mul_assoc] using hband : _ ≤ FKc 1 1 c' * (C_T * (n : ℝ) ^ (-(1 / 3 : ℝ)))) hn3 ((hfar.trans hfk4))

theorem vacuum_core (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) (d : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ c' in atTop,
      ∫ t in Ioi 0, combProfile c' (designComb c' 1 N (1 / 4) (designSigma1 d) (designWidth1 c' η)) t *
          Crossing.virasoroProblem.cardyV (c' / 12) t ≤
        FKc 1 1 c' * (CStar * windowIntegralVD N η d + ε) :=
  by
  simp only [windowIntegralVD_eq_sig]
  exact vacuum_core_sig N hN hη0 hη1 (designSigma1 d) hε

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.vacuum_core_sig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vacuum_core_sig

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.vacuum_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vacuum_core

end FormalResearch.ModularBootstrap.Upper.Positivity
