module

public import FormalResearch.ModularBootstrap.Mixtures.VacTwoZeroWindow
public import FormalResearch.ModularBootstrap.Mixtures.VacCore
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroBumpVacuum

/-!
# `pmix:vac` for `(f, r) = (2, 1)`: the vacuum core for a common source

`positive_mixtures.tex`, Proposition PM.9 (`pmix:vac`), second limit of `pmix:fixed-transfer` at `(f, r) = (2, 1)`: the weight `V_s`
of a `CommonSource` replaces `V_t = C.src.triv.cardyV (c'/12)` in `twoZeroBump_vacuum_core` (W-T2w).  At `f = 2` the deep lobe is
bounded in absolute value at every weight, so no sign of `h₂^{(p)} V_s` is needed: lobe, band and far band are transferred by
the global domination `0 ≤ V_s ≤ ‖λ‖_TV V_t` (`cmp_global`), the window by `twoZeroBump_window_comb_src`.

* `integrableOn_src`, `int_abs_src_le`: `∫_s |h V_s| ≤ ‖λ‖_TV ∫_s |h| V_t`;
* `twoZeroBump_vacuum_core_src`: `∫_0^∞ h₂^{(p)} V_s ≤ F^{mix}_{2,c} (C_* κ ∫ W_2 + ε)` uniformly in the cut;
* `twoZeroBump_gVac_bounds_src`: `g_vac ∈ Ā_s` and `|g_vac + π ∫_0^∞ h₂^{(p)} V_s| ≤ ‖λ‖_TV` (`k7_src`);
* `twoZeroBump_limsup_field_src`, `twoZeroBump_vac_eventually_src`: the second limit and vacuum positivity.

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
  FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.TwoLevel FormalResearch.Special
open TwoZeroDesign

/-- `|h V_s| ≤ ‖λ‖_TV |h V_t|` pointwise on `[0, ∞)`. -/
lemma abs_src_le_tv_mul (C : CommonSource) {c : ℝ} (hc : 0 < c) (hcA : C.a₀ ≤ c / 12) (cp : ℝ → ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    |cp t * C.src.cardyV (c / 12) t| ≤ C.src.tv * |cp t * C.src.triv.cardyV (c / 12) t| := by
  obtain ⟨hV0, hVle⟩ := cmp_global (C := C) (c' := c) hcA ht
  have hVt0 : 0 ≤ C.src.triv.cardyV (c / 12) t := triv_cardyV_nonneg C.src hc ht
  rw [abs_mul, abs_mul, abs_of_nonneg hV0, abs_of_nonneg hVt0]
  calc |cp t| * C.src.cardyV (c / 12) t ≤ |cp t| * (C.src.tv * C.src.triv.cardyV (c / 12) t) :=
        mul_le_mul_of_nonneg_left hVle (abs_nonneg _)
    _ = C.src.tv * (|cp t| * C.src.triv.cardyV (c / 12) t) := by ring

/-- `h V_s` is integrable on `s ⊆ (0, ∞)` once `h V_t` is integrable on `(0, ∞)` (domination by `‖λ‖_TV |h V_t|`). -/
lemma integrableOn_src (C : CommonSource) {c : ℝ} (hc : 0 < c) (hcA : C.a₀ ≤ c / 12) {cp : ℝ → ℝ}
    (hcont : ContinuousOn cp (Ici 0))
    (hint : IntegrableOn (fun t => cp t * C.src.triv.cardyV (c / 12) t) (Ioi 0)) {s : Set ℝ}
    (hs : MeasurableSet s) (hsub : s ⊆ Ioi 0) :
    IntegrableOn (fun t => cp t * C.src.cardyV (c / 12) t) s := by
  have hAbs : IntegrableOn (fun t => |cp t * C.src.triv.cardyV (c / 12) t|) (Ioi 0) := hint.abs
  have hI : IntegrableOn (fun t => |cp t * C.src.triv.cardyV (c / 12) t|) s := hAbs.mono_set hsub
  have hmeas : AEStronglyMeasurable (fun t => cp t * C.src.cardyV (c / 12) t) (volume.restrict s) :=
    ((hcont.mono (fun t ht => le_of_lt (hsub ht))).mul
      (C.src.continuous_cardyV (c / 12)).continuousOn).aestronglyMeasurable hs
  refine (hI.const_mul C.src.tv).mono' hmeas ?_
  refine (ae_restrict_iff' hs).mpr (Eventually.of_forall fun t ht => ?_)
  rw [Real.norm_eq_abs]
  exact abs_src_le_tv_mul C hc hcA cp (le_of_lt (hsub ht))

/-- `∫_s |h V_s| ≤ ‖λ‖_TV ∫_s |h V_t|` for `s ⊆ (0, ∞)`. -/
lemma int_abs_src_le (C : CommonSource) {c : ℝ} (hc : 0 < c) (hcA : C.a₀ ≤ c / 12) {cp : ℝ → ℝ}
    (hcont : ContinuousOn cp (Ici 0))
    (hint : IntegrableOn (fun t => cp t * C.src.triv.cardyV (c / 12) t) (Ioi 0)) {s : Set ℝ}
    (hs : MeasurableSet s) (hsub : s ⊆ Ioi 0) :
    ∫ t in s, |cp t * C.src.cardyV (c / 12) t| ≤
      C.src.tv * ∫ t in s, |cp t * C.src.triv.cardyV (c / 12) t| := by
  have hAbs : IntegrableOn (fun t => |cp t * C.src.triv.cardyV (c / 12) t|) (Ioi 0) := hint.abs
  have hI : IntegrableOn (fun t => |cp t * C.src.triv.cardyV (c / 12) t|) s := hAbs.mono_set hsub
  have hF := integrableOn_src C hc hcA hcont hint hs hsub
  calc ∫ t in s, |cp t * C.src.cardyV (c / 12) t|
      ≤ ∫ t in s, C.src.tv * |cp t * C.src.triv.cardyV (c / 12) t| :=
        setIntegral_mono_on hF.abs (hI.const_mul C.src.tv) hs
          (fun t ht => abs_src_le_tv_mul C hc hcA cp (le_of_lt (hsub ht)))
    _ = C.src.tv * ∫ t in s, |cp t * C.src.triv.cardyV (c / 12) t| := integral_const_mul _ _

/-- **Vacuum core of the bumped `(2, 1)` designs for a common source** (`pmix:vac`, second limit): for every `ε > 0`, `c` large,
`d ∈ 𝒦` and every cut `N' ≥ n + 2`, `∫_0^∞ h₂^{(p)} V_s dt ≤ F^{mix}_{2,c} (C_* κ ∫ W_2 + ε)`. -/
theorem twoZeroBump_vacuum_core_src (C : CommonSource) (bd : BumpData) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' →
      ∫ t in Ioi 0, combProfile c (d.bumpComb bd c N') t * C.src.cardyV (c / 12) t ≤
        twoZeroFSrc C.src c * (CStar * kappaAiry * (∫ u, d.Wr u) + ε) := by
  have hξ := xiStar_pos
  have hκ := kappaAiry_pos
  have hAs := C.ampl_pos hξ
  have htv := (C.at_ (le_refl C.a₀)).tv_pos
  set tv : ℝ := C.src.tv with htvdef
  set As : ℝ := C.src.ampl xiStar with hAsdef
  obtain ⟨C_L, S₀, hCL, hS₀, hlobe⟩ := twoZeroBump_lobe_bound C.src.triv bd hK hA
  obtain ⟨N₂, C_T, hCT, hband⟩ := twoZeroBump_band_bound C.src.triv bd (r₀ := 3 / 10) (by norm_num) hK hA
  obtain ⟨C_far, hCfar, hfar⟩ := twoZeroBump_far_bound C.src.triv bd (r₀ := 3 / 10) (by norm_num) hK hA
  obtain ⟨R, hR0, hRb⟩ := hK.exists_bound
  obtain ⟨m, hmN, hmS, hm1, hmL, hmT, hmR, hmΦR⟩ :=
    exists_core_index (C_L := tv / As * C_L) (C_T := tv / As * C_T) (S₀ := S₀) (R := R) (N₂ := N₂) hε
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℝ, Φ = phiWKB (m + 1) := ⟨_, rfl⟩
  rw [← hΦdef] at hmΦR
  have hΦ0 : 0 ≤ Φ := by rw [hΦdef]; exact phiWKB_nonneg (by omega)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  obtain ⟨e1, he1⟩ : ∃ e1 : ℝ, e1 = ε / 8 / (Φ + m + 1) := ⟨_, rfl⟩
  have he1pos : 0 < e1 := by rw [he1]; positivity
  have he1le : e1 * (Φ + m) ≤ ε / 8 := by
    rw [he1, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [show 0 < ε by exact hε]
  have hev_c : ∀ᶠ c in atTop,
      (tv * C_far / As) / (ε / 8 * twoZeroFConst C.src.triv) ≤ c := eventually_ge_atTop _
  filter_upwards [hlobe (m : ℝ) hmS (As / tv * (ε / 8)) (by positivity), hband m hmN, hfar,
    twoZeroBump_window_comb_src C bd hK hA hm0 m he1pos,
    twoZeroBump_integrand_props C.src.triv bd hK hA, twoZeroBump_innerCombHyp bd hK hA,
    lambda_mul_le (m : ℝ) (half_pos hξ), lambda_mul_le Φ (by norm_num : (0 : ℝ) < 3 / 10),
    eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (12 * C.src.triv.totalShift),
    eventually_ge_atTop (12 * C.a₀), hev_c]
    with c hLb hBb hFr hWc hprops hI hlm hlΦ hc hcS hcA0 hcbig d hd N' hN'
  have hcA : C.a₀ ≤ c / 12 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 12)]
    linarith
  obtain ⟨-, hintP⟩ := hprops d hd N' hN'
  have hcontH := (hI d hd N' hN').continuousOn_combProfile hc
  have hlam := lambdaComb_pos' hc
  have hFs : twoZeroFSrc C.src c = As * twoZeroF C.src.triv c := twoZeroFSrc_eq C.src c
  have hFpos := twoZeroFSrc_pos C hc
  have hFt := twoZeroF_pos C.src.triv hc
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
  have hcontF : ContinuousOn (fun t => combProfile c (d.bumpComb bd c N') t * C.src.cardyV (c / 12) t)
      (Ici 0) := hcontH.mul (C.src.continuous_cardyV (c / 12)).continuousOn
  have hint := integrableOn_src C hc hcA hcontH hintP measurableSet_Ioi (subset_refl _)
  have hwcont : Continuous fun σ : ℝ => CStar * kappaAiry ^ 2 * d.Wr (-kappaAiry * σ) :=
    continuous_const.mul (d.continuous_Wr.comp (by fun_prop))
  have hwin := window_piece (c := c) (F := twoZeroFSrc C.src c) (e1 := e1) (m := (m : ℝ)) (Φ := Φ)
    (g := fun t => combProfile c (d.bumpComb bd c N') t * C.src.cardyV (c / 12) t) hc.le hFpos hcontF
    hwcont (by linarith) (fun σ hσ => hWc d hd N' hN' σ ⟨hσ.1, hσ.2.trans hΦdef.le⟩)
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
  have hS0 : 0 ≤ c * (xiStar + lambdaComb c * (-(m : ℝ))) ^ 2 / 3 := by positivity
  have hN0 : 0 < c * chiQuantile c ((m + 1 : ℕ) : ℝ) ^ 2 / 3 := by positivity
  have hRpos : 0 < c * (xiStar + 3 / 10) ^ 2 / 3 := by positivity
  have hlobe' : ∫ t in Ioc 0 (c * (xiStar + lambdaComb c * (-(m : ℝ))) ^ 2 / 3),
      |combProfile c (d.bumpComb bd c N') t * C.src.cardyV (c / 12) t| ≤
      twoZeroFSrc C.src c * (tv / As * C_L * (m : ℝ) ^ (-(3 / 2 : ℝ)) + ε / 8) := by
    have h1 := int_abs_src_le C hc hcA hcontH hintP (measurableSet_Ioc (a := 0)
      (b := c * (xiStar + lambdaComb c * (-(m : ℝ))) ^ 2 / 3)) (fun t ht => ht.1)
    rw [setIntegral_abs_profile C.src.triv hcS _ measurableSet_Ioc (fun t ht => ht.1.le)] at h1
    have h2 := mul_le_mul_of_nonneg_left (hLb d hd N' hN') htv.le
    refine h1.trans (h2.trans (le_of_eq ?_))
    rw [hFs]
    field_simp
  have hband' : ∫ t in Icc (c * chiQuantile c ((m + 1 : ℕ) : ℝ) ^ 2 / 3) (c * (xiStar + 3 / 10) ^ 2 / 3),
      |combProfile c (d.bumpComb bd c N') t * C.src.cardyV (c / 12) t| ≤
      twoZeroFSrc C.src c * (ε / 8) := by
    have h1 := int_abs_src_le C hc hcA hcontH hintP (measurableSet_Icc (a := c * chiQuantile c ((m + 1 : ℕ) : ℝ) ^ 2 / 3)
      (b := c * (xiStar + 3 / 10) ^ 2 / 3)) (fun t ht => lt_of_lt_of_le hN0 ht.1)
    rw [setIntegral_abs_profile C.src.triv hcS _ measurableSet_Icc (fun t ht => hN0.le.trans ht.1)] at h1
    have h2 := mul_le_mul_of_nonneg_left (hBb d hd N' hN') htv.le
    have h3 : twoZeroFSrc C.src c * ((tv / As * C_T) * (m : ℝ)⁻¹) ≤ twoZeroFSrc C.src c * (ε / 8) :=
      mul_le_mul_of_nonneg_left hmT hFpos.le
    refine h1.trans (h2.trans (le_trans (le_of_eq ?_) h3))
    rw [hFs]
    field_simp
  have hfar' : ∫ t in Ici (c * (xiStar + 3 / 10) ^ 2 / 3),
      |combProfile c (d.bumpComb bd c N') t * C.src.cardyV (c / 12) t| ≤
      ε / 8 * twoZeroFSrc C.src c := by
    have h1 := int_abs_src_le C hc hcA hcontH hintP (measurableSet_Ici (a := c * (xiStar + 3 / 10) ^ 2 / 3))
      (fun t ht => lt_of_lt_of_le hRpos ht)
    rw [setIntegral_abs_profile C.src.triv hcS _ measurableSet_Ici (fun t ht => hRpos.le.trans ht)] at h1
    have h2 := mul_le_mul_of_nonneg_left (hFr d hd N' hN') htv.le
    have h3 := far_small C.src.triv hc hε hcbig (C_far := tv * C_far / As)
    have h4 := mul_le_mul_of_nonneg_left h3 hAs.le
    refine h1.trans (h2.trans ?_)
    rw [hFs]
    have e : As * (tv * C_far / As * √c) = tv * (C_far * √c) := by field_simp
    nlinarith only [h4, e]
  refine core_assemble (g := fun t => combProfile c (d.bumpComb bd c N') t * C.src.cardyV (c / 12) t)
    (CLm := tv / As * C_L * (m : ℝ) ^ (-(3 / 2 : ℝ))) (K := CStar * kappaAiry * ∫ u, d.Wr u)
    (m := (m : ℝ)) (e1 := e1) (Φ := Φ) (by positivity) (by positivity) hSΦ hNΦ hΦR hint hFpos hε
    hlobe' hmL hwin hWint he1le hband' hfar'

/-! ### The vacuum identity for the source -/

/-- **The vacuum identity of `K7` for the source** (`pmix:crossing`(b)): for `c` large, `d ∈ 𝒦` and every cut `N' ≥ n + 2`,
the bumped functional `g = ½(h₂^{(p)} - 𝓗_w h₂^{(p)})` is in the source test class and
`|g_vac + π ∫_0^∞ h₂^{(p)} V_s dt| ≤ ‖λ‖_TV`. -/
theorem twoZeroBump_gVac_bounds_src (C : CommonSource) (bd : BumpData) {n : ℕ}
    {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' →
      TestClass C.src (c / 12) (twoZeroBumpGN C.src.triv bd d c N') ∧
      |C.src.gVac (c / 12) (twoZeroBumpGN C.src.triv bd d c N') + π * (∫ t in Ioi 0,
        combProfile c (d.bumpComb bd c N') t * C.src.cardyV (c / 12) t)| ≤ C.src.tv := by
  filter_upwards [twoZeroBump_k7W C.src.triv bd hK hA, twoZeroBump_innerCombHyp bd hK hA,
    eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (12 * C.a₀)] with c hK7 hI hc hcA0 d hd N' hN'
  have hcA : C.a₀ ≤ c / 12 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 12)]
    linarith
  obtain ⟨hTest, hid, hn⟩ := k7_src hc (C.at_ hcA) (hI d hd N' hN') (hK7 d hd N' hN')
  refine ⟨hTest, ?_⟩
  have hre := congrArg Complex.re hid
  rw [← Complex.ofReal_mul, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re] at hre
  have h3 := (Complex.abs_re_le_norm _).trans hn
  show |C.src.gVac (c / 12) (pairOdd (combProfile c (d.bumpComb bd c N'))
      (hankelTransform C.src.w (combProfile c (d.bumpComb bd c N')))) + π * (∫ t in Ioi 0,
        combProfile c (d.bumpComb bd c N') t * C.src.cardyV (c / 12) t)| ≤ C.src.tv
  rw [hre, sub_add_cancel]
  exact h3

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.int_abs_src_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms int_abs_src_le

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.twoZeroBump_vacuum_core_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_vacuum_core_src

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.twoZeroBump_gVac_bounds_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_gVac_bounds_src

end FormalResearch.ModularBootstrap.Mixtures
