module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroBumpVacuumWindow
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroVacuum

/-!
# The vacuum limsup and the vacuum positivity for the bumped two-zero comb at every weight (`ut:T2`, S5-S6)

Source: `upper_transfer.tex`, Theorem T2 (`ut:T2`) at fixed `(w, Q)`.  For `g = twoZeroBumpG prob d c = ½(h₂^{(p)} - 𝓗_w h₂^{(p)})`
(`h₂^{(p)} = sech² T_{χ(p)} B₁^{(p)}`, the bump of `rpParams (w - 1)` and the cut `bumpCut`), `F = twoZeroF prob`,
`C₂ = twoZeroC₂ = C_* κ / 2`, every compact family `𝒦` of admissible designs:

* `twoZeroBump_integrand_props`, `twoZeroBump_vacuum_core`: `∫_0^∞ h₂^{(p)} V dt ≤ F_{2,c} (C_* κ ∫ W₂ + ε)`, uniformly in
  the cut (deep lobe, window, band and far band at every weight);
* `twoZeroBump_gVac_bounds`: the vacuum identity `|g_vac + π ∫_0^∞ h₂^{(p)} V| ≤ 2^m` (`K7` at every weight);
* `twoZeroBump_integrable`, `twoZeroBump_limsup_field`, `twoZeroBump_vac_field_of_threshold`: the `integrable`,
  `limsup_le` and `vac` fields of `TwoZeroTransferData`;
* `twoZeroBump_fields_eventually`: the `testClass`, `decay`, `pos` fields.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Hankel FormalResearch.ModularBootstrap.Upper.Rigidity
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Assembly
  FormalResearch.ModularBootstrap.Upper.Window.Cardy FormalResearch.ModularBootstrap.Upper.Bump
open TwoZeroDesign

/-- `h₂^{(p)} V` is continuous on `[0, ∞)` and integrable on `(0, ∞)`, uniformly on a compact family and in the cut
(decay from `K7` at every weight). -/
theorem twoZeroBump_integrand_props (prob : FixedWeightProblem) (bd : BumpData) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' →
      ContinuousOn (fun t => combProfile c (d.bumpComb bd c N') t * prob.cardyV (c / 12) t) (Ici 0) ∧
      IntegrableOn (fun t => combProfile c (d.bumpComb bd c N') t * prob.cardyV (c / 12) t) (Ioi 0) := by
  filter_upwards [twoZeroBump_innerCombHyp bd hK hA, twoZeroBump_k7W prob bd hK hA,
    eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (12 * prob.totalShift)]
    with c hI hK7 hpos hcS d hd N' hN'
  obtain ⟨C, hC0, hdec, -⟩ := hK7 d hd N' hN'
  have hcont := (hI d hd N' hN').continuousOn_combProfile hpos
  have hk := kernelIntegrable_of_decay (w := prob.w) prob.hw hpos hcont hdec
  exact ⟨hcont.mul (Crossing.continuous_cardyV prob (c / 12)).continuousOn,
    integrableOn_mul_cardyV (prob := prob) (by linarith) hcont hk⟩

/-- **The vacuum identity of `K7` at every weight**: for `c` large, `d ∈ 𝒦` and every cut `N' ≥ n + 2`,
`|g_vac + π ∫_0^∞ h₂^{(p)} V dt| ≤ 2^m`. -/
theorem twoZeroBump_gVac_bounds (prob : FixedWeightProblem) (bd : BumpData) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' →
      |prob.gVac (c / 12) (twoZeroBumpGN prob bd d c N') + π * (∫ t in Ioi 0,
        combProfile c (d.bumpComb bd c N') t * prob.cardyV (c / 12) t)| ≤ 2 ^ prob.m := by
  filter_upwards [twoZeroBump_k7W prob bd hK hA] with c hK7 d hd N' hN'
  obtain ⟨C, hC0, -, -, -, hvac, hn⟩ := hK7 d hd N' hN'
  have hre := congrArg Complex.re hvac
  rw [Complex.ofReal_re, Complex.sub_re] at hre
  have h2 : ((π : ℂ) * ((∫ t in Ioi (0 : ℝ),
      combProfile c (d.bumpComb bd c N') t * prob.cardyV (c / 12) t : ℝ) : ℂ)).re =
      π * (∫ t in Ioi (0 : ℝ), combProfile c (d.bumpComb bd c N') t * prob.cardyV (c / 12) t) := by
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  rw [h2] at hre
  have h3 := (Complex.abs_re_le_norm _).trans hn
  unfold twoZeroBumpGN
  have : prob.gVac (c / 12) (pairOdd (combProfile c (d.bumpComb bd c N'))
      (hankelTransform prob.w (combProfile c (d.bumpComb bd c N')))) + π * (∫ t in Ioi (0 : ℝ),
      combProfile c (d.bumpComb bd c N') t * prob.cardyV (c / 12) t) =
      ((1 / 2 : ℂ) * ∑ s : Finset (Fin prob.m), (-1 : ℂ) ^ s.card *
          combH0 (d.bumpComb bd c N') (bAlpha c (c / 12 - prob.shiftSum s))).re := by
    linarith
  rw [this]
  exact h3

/-- **`V_c ≤ F_{2,c} (C_* κ V_𝒟 + ε)`** (`ut:T2`, "Far band and assembly"), uniformly on a compact family of admissible designs:
for every `ε > 0`, `c` large and all `d ∈ 𝒦`,
`∫_0^∞ h₂ V dt ≤ F_{2,c} (C_* κ ∫_ℝ W_2 du + ε)`; no sign assumption on `∫ W_2`. -/
theorem twoZeroBump_vacuum_core (prob : FixedWeightProblem) (bd : BumpData) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' →
      ∫ t in Ioi 0, combProfile c (d.bumpComb bd c N') t * prob.cardyV (c / 12) t ≤
        twoZeroF prob c * (CStar * kappaAiry * (∫ u, d.Wr u) + ε) := by
  have hξ := xiStar_pos
  have hκ := kappaAiry_pos
  obtain ⟨C_L, S₀, hCL, hS₀, hlobe⟩ := twoZeroBump_lobe_bound prob bd hK hA
  obtain ⟨N₂, C_T, hCT, hband⟩ := twoZeroBump_band_bound prob bd (r₀ := 3 / 10) (by norm_num) hK hA
  obtain ⟨C_far, hCfar, hfar⟩ := twoZeroBump_far_bound prob bd (r₀ := 3 / 10) (by norm_num) hK hA
  obtain ⟨R, hR0, hRb⟩ := hK.exists_bound
  obtain ⟨m, hmN, hmS, hm1, hmL, hmT, hmR, hmΦR⟩ :=
    exists_core_index (C_L := C_L) (C_T := C_T) (S₀ := S₀) (R := R) (N₂ := N₂) hε
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℝ, Φ = phiWKB (m + 1) := ⟨_, rfl⟩
  rw [← hΦdef] at hmΦR
  have hΦ0 : 0 ≤ Φ := by rw [hΦdef]; exact phiWKB_nonneg (by omega)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  obtain ⟨e1, he1⟩ : ∃ e1 : ℝ, e1 = ε / 8 / (Φ + m + 1) := ⟨_, rfl⟩
  have he1pos : 0 < e1 := by rw [he1]; positivity
  have he1le : e1 * (Φ + m) ≤ ε / 8 := by
    rw [he1, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [show 0 < ε by exact hε]
  have hev_c : ∀ᶠ c in atTop, C_far / (ε / 8 * twoZeroFConst prob) ≤ c := eventually_ge_atTop _
  filter_upwards [hlobe (m : ℝ) hmS (ε / 8) (by positivity), hband m hmN, hfar,
    twoZeroBump_window_comb prob bd hK hA hm0 m he1pos, twoZeroBump_integrand_props prob bd hK hA,
    lambda_mul_le (m : ℝ) (half_pos hξ), lambda_mul_le Φ (by norm_num : (0 : ℝ) < 3 / 10),
    eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (12 * prob.totalShift), hev_c]
    with c hLb hBb hFr hWc hprops hlm hlΦ hc hcS hcbig d hd N' hN'
  obtain ⟨hcont, hint⟩ := hprops d hd N' hN'
  have hlam := lambdaComb_pos' hc
  have hFpos := twoZeroF_pos prob hc
  have ha : (1 / 4 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
    linarith
  have hχ1 : xiStar ≤ chiQuantile c ((m + 1 : ℕ) : ℝ) := (chiQuantile_spec hc ha).1
  have hχ2 : chiQuantile c ((m + 1 : ℕ) : ℝ) ≤ xiStar + lambdaComb c * Φ := by
    have h := (siteRadius_bounds hc ha).2
    unfold siteRadius at h
    rw [hΦdef, phiWKB_eq_phiQuantile (m + 1)]
    linarith
  have hχpos : 0 < chiQuantile c ((m + 1 : ℕ) : ℝ) := lt_of_lt_of_le hξ hχ1
  obtain ⟨hSΦ, hNΦ, hΦR⟩ := core_geom hc hlam hξ hχ1 hχ2 hlm hlΦ hΦ0 hm0
  have hwcont : Continuous fun σ : ℝ => CStar * kappaAiry ^ 2 * d.Wr (-kappaAiry * σ) :=
    continuous_const.mul (d.continuous_Wr.comp (by fun_prop))
  have hwin := window_piece (c := c) (F := twoZeroF prob c) (e1 := e1) (m := (m : ℝ)) (Φ := Φ)
    (g := fun t => combProfile c (d.bumpComb bd c N') t * prob.cardyV (c / 12) t) hc.le hFpos hcont hwcont
    (by linarith) (fun σ hσ => hWc d hd N' hN' σ ⟨hσ.1, hσ.2.trans hΦdef.le⟩)
  have hq : -(kappaAiry * Φ) ≤ d.q := by
    have := (abs_le.mp (hRb d hd).2.1).1
    have h1 : R ≤ kappaAiry * Φ := by
      have := (div_le_iff₀ hκ).mp hmΦR
      linarith
    linarith
  have hp : d.p ≤ kappaAiry * (m : ℝ) := by
    have := (abs_le.mp (hRb d hd).1).2
    have h1 : R ≤ kappaAiry * (m : ℝ) := by
      have := (div_le_iff₀ hκ).mp hmR
      linarith
    linarith
  have hWint := window_integral_le d (hA d hd) (S := (m : ℝ)) (Φ := Φ) (by linarith) hq hp
  have hlobe' : ∫ t in Ioc 0 (c * (xiStar + lambdaComb c * (-(m : ℝ))) ^ 2 / 3),
      |combProfile c (d.bumpComb bd c N') t * prob.cardyV (c / 12) t| ≤
      twoZeroF prob c * (C_L * (m : ℝ) ^ (-(3 / 2 : ℝ)) + ε / 8) := by
    rw [setIntegral_abs_profile prob hcS _ measurableSet_Ioc (fun t ht => ht.1.le)]
    exact hLb d hd N' hN'
  have hband' : ∫ t in Icc (c * chiQuantile c ((m + 1 : ℕ) : ℝ) ^ 2 / 3) (c * (xiStar + 3 / 10) ^ 2 / 3),
      |combProfile c (d.bumpComb bd c N') t * prob.cardyV (c / 12) t| ≤
      twoZeroF prob c * C_T * (m : ℝ)⁻¹ := by
    have h0 : 0 ≤ c * chiQuantile c ((m + 1 : ℕ) : ℝ) ^ 2 / 3 := by positivity
    rw [setIntegral_abs_profile prob hcS _ measurableSet_Icc (fun t ht => h0.trans ht.1)]
    exact hBb d hd N' hN'
  have hfar' : ∫ t in Ici (c * (xiStar + 3 / 10) ^ 2 / 3),
      |combProfile c (d.bumpComb bd c N') t * prob.cardyV (c / 12) t| ≤ C_far * √c := by
    have h0 : 0 ≤ c * (xiStar + 3 / 10) ^ 2 / 3 := by positivity
    rw [setIntegral_abs_profile prob hcS _ measurableSet_Ici (fun t ht => h0.trans ht)]
    exact hFr d hd N' hN'
  have hfar'' := far_small prob hc hε hcbig (C_far := C_far)
  refine core_assemble (g := fun t => combProfile c (d.bumpComb bd c N') t * prob.cardyV (c / 12) t)
    (CLm := C_L * (m : ℝ) ^ (-(3 / 2 : ℝ))) (K := CStar * kappaAiry * ∫ u, d.Wr u) (m := (m : ℝ)) (e1 := e1)
    (Φ := Φ) (by positivity) (by positivity) hSΦ hNΦ hΦR hint hFpos hε hlobe' hmL hwin hWint he1le ?_ ?_
  · refine hband'.trans ?_
    have : twoZeroF prob c * C_T * (m : ℝ)⁻¹ = twoZeroF prob c * (C_T * (m : ℝ)⁻¹) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hmT hFpos.le
  · exact hfar'.trans hfar''


/-- `g_w ∈ Ā_w`, the decay of `g_w` and `g_w > 0` for `t ≥ t(q) + 1`: the fields `testClass`, `decay`, `pos` of
`TwoZeroTransferData` for `g = twoZeroBumpG prob`, for `c` large. -/
theorem twoZeroBump_fields_eventually (prob : FixedWeightProblem) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c : ℝ in atTop, 0 < c ∧ ∀ d ∈ 𝒦, TestClass prob (c / 12) (twoZeroBumpG prob d c) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
        |twoZeroBumpG prob d c t| ≤
          C * Real.exp (-4 * π * Real.sqrt (c / 12 * t) - π * Real.sqrt (3 * t / c))) ∧
      ∀ t : ℝ, tAiry c d.q + 1 ≤ t → 0 < twoZeroBumpG prob d c t := by
  filter_upwards [twoZeroBump_pos_g prob hK hA, twoZeroBump_k7W prob (probBump prob) hK hA,
    eventually_gt_atTop (0 : ℝ)] with c hpos hK7 hc
  refine ⟨hc, fun d hd => ?_⟩
  obtain ⟨C, hC0, hd1, hd2, hT, -⟩ := hK7 d hd _ (le_bumpCut (probBump prob) (n + 2) c)
  refine ⟨hT, ⟨C, hC0, fun t ht => ?_⟩, hpos d hd⟩
  have := (hd1.pairOdd hd2) t ht
  unfold decayEnv at this
  rw [decay_exponent_eq hc ht] at this
  have e : -(4 * π * √(c / 12 * t)) - π * xOf c t = -4 * π * √(c / 12 * t) - π * √(3 * t / c) := by
    unfold xOf; ring
  rw [e] at this
  exact this

/-- **Integrability of `Ψ_g`** for the bumped two-zero comb at every weight. -/
theorem twoZeroBump_integrable (prob : FixedWeightProblem) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c : ℝ in atTop, ∀ d ∈ 𝒦, Integrable (psiAiry prob c (twoZeroBumpG prob d c)) := by
  filter_upwards [twoZeroBump_fields_eventually prob hK hA, eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (12 * prob.totalShift)] with c hT hc hcS d hd
  exact integrable_psiAiry_of_testClass prob hT.1 (by linarith) ((hT.2 d hd).1)

/-- **The `limsup_le` field of `TwoZeroTransferData` at every weight**, with the exact quantifiers of the field. -/
theorem twoZeroBump_limsup_field (prob : FixedWeightProblem) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ c : ℝ in atTop, ∀ d ∈ 𝒦,
      (twoZeroF prob c)⁻¹ * (∫ u, psiAiry prob c (twoZeroBumpG prob d c) u) ≤
        twoZeroC₂ * (∫ u, d.Wr u) + ε := by
  intro ε hε
  filter_upwards [twoZeroBump_vacuum_core prob (probBump prob) hK hA hε,
    twoZeroBump_gVac_bounds prob (probBump prob) hK hA,
    eventually_gt_atTop (0 : ℝ), twoZeroF_eventually_ge prob (2 ^ prob.m / (π * ε))]
    with c hV hg hc hFbig d hd
  have hFpos := twoZeroF_pos prob hc
  have hN := le_bumpCut (probBump prob) (n + 2) c
  rw [integral_psiAiry_eq_neg_gVac prob hc]
  refine limsup_arith (I := ∫ t in Ioi 0, combProfile c (twoZeroBumpB prob d c) t * prob.cardyV (c / 12) t)
    hFpos (hg d hd _ hN) ?_ ?_
  · have : 2 * twoZeroC₂ = CStar * kappaAiry := by unfold twoZeroC₂; ring
    rw [this]
    exact hV d hd _ hN
  · have hπ := Real.pi_pos
    rw [div_le_iff₀ (by positivity)] at hFbig
    linarith

/-- **Vacuum positivity at every weight**: if `∫ W₂ ≤ -δ` on `𝒦`, there are `κ > 0` and a threshold beyond which
`κ c^{3/2} ≤ g_vac` for all `d ∈ 𝒦`. -/
theorem twoZeroBump_vac_eventually (prob : FixedWeightProblem) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm)
    (hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ d ∈ 𝒦, ∫ u, d.Wr u ≤ -δ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ c : ℝ in atTop, ∀ d ∈ 𝒦,
      κ * c ^ ((3 : ℝ) / 2) ≤ prob.gVac (c / 12) (twoZeroBumpG prob d c) := by
  obtain ⟨δ, hδ0, hW⟩ := hδ
  have hC := CStar_pos
  have hκ := kappaAiry_pos
  obtain ⟨A, B, hA0, hB0, hAB⟩ := twoZeroF_asymp prob
  have hK0 : 0 < CStar * kappaAiry := by positivity
  have hε : 0 < CStar * kappaAiry * δ / 2 := by positivity
  have hπ := Real.pi_pos
  refine ⟨π * (CStar * kappaAiry) * δ / 4 * A, by positivity, ?_⟩
  filter_upwards [twoZeroBump_vacuum_core prob (probBump prob) hK hA hε,
    twoZeroBump_gVac_bounds prob (probBump prob) hK hA,
    eventually_gt_atTop (0 : ℝ),
    twoZeroF_eventually_ge prob (2 ^ prob.m / (π * (CStar * kappaAiry) * δ / 4))]
    with c hV hg hc hFbig d hd
  have hFpos := twoZeroF_pos prob hc
  have hN := le_bumpCut (probBump prob) (n + 2) c
  have hpos : 0 < π * (CStar * kappaAiry) * δ / 4 := by positivity
  rw [div_le_iff₀ hpos] at hFbig
  have h := vac_arith (F := twoZeroF prob c) (K := CStar * kappaAiry) (δ := δ) hFpos hK0 (hg d hd _ hN)
    (hW d hd) rfl (hV d hd _ hN) (by linarith)
  have h2 := mul_le_mul_of_nonneg_left (hAB c hc).1 hpos.le
  rw [twoZeroBumpG_eq]
  linarith

/-- The `vac` field in the form of `TwoZeroTransferData`. -/
theorem twoZeroBump_vac_field_of_threshold (prob : FixedWeightProblem) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm)
    (hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ d ∈ 𝒦, ∫ u, d.Wr u ≤ -δ) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ c₁ : ℝ, ∀ c₀ : ℝ, c₁ ≤ c₀ → ∀ c : ℝ, c₀ ≤ c → ∀ d ∈ 𝒦,
      κ * c ^ ((3 : ℝ) / 2) ≤ prob.gVac (c / 12) (twoZeroBumpG prob d c) := by
  obtain ⟨κ, hκ, h⟩ := twoZeroBump_vac_eventually prob hK hA hδ
  obtain ⟨c₁, hc₁⟩ := eventually_atTop.mp h
  exact ⟨κ, hκ, c₁, fun c₀ h0 c hc d hd => hc₁ c (h0.trans hc) d hd⟩

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroBump_vacuum_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_vacuum_core

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroBump_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_integrable

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroBump_limsup_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_limsup_field

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroBump_vac_field_of_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_vac_field_of_threshold

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroBump_fields_eventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_fields_eventually

end FormalResearch.ModularBootstrap.TwoLevel
