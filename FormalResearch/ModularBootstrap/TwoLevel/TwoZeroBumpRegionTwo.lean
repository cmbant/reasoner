module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroBump
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroBumpRegionOne
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroRegionTwo
public import FormalResearch.ModularBootstrap.Upper.Positivity.PropositionIIIRegionII

/-!
# Region II for the bumped two-zero comb at every weight (`ut:IIF`, `ut:III`, `ut:T2`)

Source: `upper_transfer.tex`, Lemma II-F (`ut:IIF`, `f = 2`, `r = 1`, `n_eff = 5/4`) and Proposition III (`ut:III`),
Region II at `w > 1`: the bump only raises `h₂` (`fw:e3.1`), the floor of `ut:IIF` is divided by `T_{χ(p)}`
(`Lev₂ = T_{χ(p)} Lev^{(2)}`), the order-`p` transform is bounded by `ρ_∞ R_p (1 + w) Lev` (`fw:e1.6`, with
`vρ_∞(x; 5/4) T_{ξ_*} = vρ_∞(x; 7/4)` and `T_{ξ_*} ≤ (1 + 1/1000) T_{χ(p)}`), and the three ranges of `ut:III` close with
`fw:e2.2`, `fw:e2.3` and the macroscopic floor `bump_floor_family`.

* `twoZeroBump_regionII`: for `c` large, every cut `N' ≥ n + 2` above the block and `x ≥ ξ_* + c^{-2/5}`,
  `Lev₂(x)/20 ≤ 2 g_w(c x²/3)`;
* `twoZeroBump_regionII_pos`: `2 g_w > 0` there.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Upper.Hankel FormalResearch.ModularBootstrap.Upper.Saddle
  FormalResearch.ModularBootstrap.Upper.Bump FormalResearch.ModularBootstrap.Upper.Ramped
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Holes
open TwoZeroDesign

/-! ### 1. Margins with the factor `T_{ξ_*} ≤ 1.001 T_{χ(p)}` -/

/-- The margin `q (1001/1000) (1 + w) + 1/20 ≤ c` from `q ≤ Q`, `w ≤ 1/50` and the numerical margin for `Q`. -/
lemma margin_aux {q Q w c : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ Q) (hw0 : 0 ≤ w) (hw : w ≤ 1 / 50)
    (h : Q * (1001 / 1000) * (1 + 1 / 50) + 1 / 20 ≤ c) :
    q * (1001 / 1000) * (1 + w) + 1 / 20 ≤ c := by
  have h1 : q * (1001 / 1000) * (1 + w) ≤ Q * (1001 / 1000) * (1 + 1 / 50) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

/-- Near-tip margin: `Q = 1/10`. -/
lemma nu_margin_near' : (1 / 10 : ℝ) * (1001 / 1000) * (1 + 1 / 50) + 1 / 20 ≤
    (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000) := by norm_num

/-- Far margin: `Q = 6/10`. -/
lemma nu_margin_far' : (6 / 10 : ℝ) * (1001 / 1000) * (1 + 1 / 50) + 1 / 20 ≤
    (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000) := by norm_num

/-- Macroscopic margin: `bumpFloor H > 2 M + 1`, `M ≥ 0` gives
`M (1001/1000) (1 + 1/50) + 1/20 ≤ (1 - 1/100) ((16/5)(H² + 1/4)) ν`. -/
lemma macro_margin' {M H : ℝ} (hM : 0 ≤ M) (hfl : 2 * M + 1 < bumpFloor H) :
    M * (1001 / 1000) * (1 + 1 / 50) + 1 / 20 ≤
      (1 - 1 / 100 : ℝ) * ((16 / 5) * (H ^ 2 + 1 / 4)) *
        ((7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000)) := by
  unfold bumpFloor at hfl
  have h : (1 - 1 / 100 : ℝ) * ((16 / 5) * (H ^ 2 + 1 / 4)) *
        ((7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000)) =
      (7 / 10 * (16 / 5 * (H ^ 2 + 1 / 4))) *
        ((1 - 1 / 100 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000)) := by ring
  rw [h]
  have hk : (98 / 100 : ℝ) ≤ (1 - 1 / 100 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000) := by
    norm_num
  have h2 : (98 / 100 : ℝ) * (2 * M + 1) ≤
      (7 / 10 * (16 / 5 * (H ^ 2 + 1 / 4))) *
        ((1 - 1 / 100 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000)) := by
    have hpos : 0 ≤ 7 / 10 * (16 / 5 * (H ^ 2 + 1 / 4)) := by positivity
    calc (98 / 100 : ℝ) * (2 * M + 1) ≤ (98 / 100 : ℝ) * (7 / 10 * (16 / 5 * (H ^ 2 + 1 / 4))) :=
          mul_le_mul_of_nonneg_left hfl.le (by norm_num)
      _ ≤ _ := by nlinarith only [hk, hpos]
  linarith only [h2, hM]

/-! ### 2. The transform against the level, with the real factor -/

/-- **The transform against the level for `T_{χ(p)} B^{(p)}`** (`fw:e1.6`, `ut:IIF`): from
`‖𝓗_{p+1} h‖ ≤ 𝒜_x R_p (1 + w)`, `x > χ_{5/2}`, `x > ξ_*` and `T_{ξ_*}(x) ≤ (1001/1000) T`:
`‖𝓗_{p+1} h‖ ≤ ρ_∞ R_p (1001/1000)(1 + w) · (T · Lev^{(2)})`. -/
lemma norm_le_rhoRp_mul_lev_T {c x T : ℝ} (hc : 0 < c)
    (hx : chiQuantile c (((2 : ℕ) : ℝ) + 1 / 2) < x) (hxi : xiStar < x) (p : ℕ) {nh w : ℝ} (hw : 0 ≤ w)
    (hT : tFac xiStar x ≤ (1001 / 1000 : ℝ) * T)
    (h : nh ≤ combAmplitude c x * fwsdRatio p x * (1 + w)) :
    nh ≤ (rhoRp p x * (1001 / 1000)) * (1 + w) * (T * levComb c 2 x) := by
  have hA := combAmplitude_le_vRhoInfty_mul_levComb hc (f := 2) (by norm_num) hx
  have hn1 : n1Comb 2 = 5 / 4 + 1 / 2 := by unfold n1Comb; norm_num
  rw [hn1, vRhoInfty_add_half hxi] at hA
  have hR := rhoRp_neff_le p (n := 5 / 4) (by norm_num) hxi
  have hR0 : 0 ≤ rAmp p x := rAmp_nonneg p (xiStar_pos.trans hxi).le
  have hlev := levComb_pos c 2 x
  have hTξ : 0 ≤ tFac xiStar x := (tFac_pos xiStar_pos.le hxi).le
  rw [fwsdRatio_eq_rAmp p hxi] at h
  refine h.trans ?_
  have h1 : combAmplitude c x * rAmp p x ≤
      vRhoInfty x (5 / 4) * tFac xiStar x * levComb c 2 x * rAmp p x :=
    mul_le_mul_of_nonneg_right hA hR0
  have h2 : vRhoInfty x (5 / 4) * tFac xiStar x * levComb c 2 x * rAmp p x ≤
      rhoRp p x * (tFac xiStar x * levComb c 2 x) := by
    have e : vRhoInfty x (5 / 4) * tFac xiStar x * levComb c 2 x * rAmp p x =
        (vRhoInfty x (5 / 4) * rAmp p x) * (tFac xiStar x * levComb c 2 x) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hR (mul_nonneg hTξ hlev.le)
  have h3 : tFac xiStar x * levComb c 2 x ≤ (1001 / 1000 : ℝ) * (T * levComb c 2 x) := by
    nlinarith only [hT, hlev]
  have hq0 : 0 ≤ rhoRp p x := rhoRp_nonneg p hxi
  have h4 : combAmplitude c x * rAmp p x ≤ rhoRp p x * ((1001 / 1000 : ℝ) * (T * levComb c 2 x)) :=
    h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 hq0))
  calc combAmplitude c x * rAmp p x * (1 + w) ≤
      (rhoRp p x * ((1001 / 1000 : ℝ) * (T * levComb c 2 x))) * (1 + w) :=
        mul_le_mul_of_nonneg_right h4 (by linarith)
    _ = (rhoRp p x * (1001 / 1000)) * (1 + w) * (T * levComb c 2 x) := by ring

/-! ### 3. Region II -/

/-- **Region II for the bumped two-zero comb at every weight** (`ut:IIF`, `ut:III`; `fw:e1.6`, `fw:e2.2`, `fw:e2.3`,
`fw:e3.1`, `fw:e3.5`).  Fix `p` and `P : RpParams p`.  For `c` large, every `d` of a compact family of admissible designs,
every cut `N' ≥ n + 2` above the block (every index with `χ_k ≤ X_p` is `≤ N'`) and every `x ≥ ξ_* + c^{-2/5}`:
`Lev₂(x)/20 ≤ 2 g_w(c x²/3)`, `Lev₂ = T_{χ(p)}(x) Lev^{(2)}(x)`. -/
theorem twoZeroBump_regionII (p : ℕ) (P : RpParams p) {n : ℕ} {𝒦 : Set (TwoZeroDesign n)}
    (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' →
      (∀ k : ℕ, 1 ≤ k → chiQuantile c (k : ℝ) ≤ P.X → k ≤ N') →
      ∀ x : ℝ, xiStar + c ^ (-(2 / 5 : ℝ)) ≤ x →
        1 / 20 * (tFac (d.chiP c) x * levComb c 2 x) ≤
          (sechSqProfile (x : ℂ) * d.bumpComb P.bumpData c N' (x : ℂ) -
            edgeHankelP p c (fun b => sechSqProfile b * d.bumpComb P.bumpData c N' b)
              (c * x ^ 2 / 3)).re := by
  obtain ⟨M, E, hM, hE, hb⟩ := hK.exists_comb_bounds hA
  obtain ⟨C, hC, htr⟩ := twoZeroBump_transformP P.bumpData p hK hA (θ := 2 / 5) (by norm_num) (by norm_num)
  have hexp : (-1 + 3 * (2 / 5 : ℝ) / 2) = -(2 / 5 : ℝ) := by norm_num
  have e8 : ∀ᶠ c in atTop, C * c ^ (-(2 / 5 : ℝ)) ≤ 1 / 50 :=
    (tendsto_rpow_neg_two_fifths.const_mul C).eventually_le_const (by norm_num)
  filter_upwards [htr, e8, proposition_II_floor 2 (n + 2) (by norm_num) (by omega) M E,
    bump_floor_family P.bumpData 2 (n + 2) (by norm_num) (by omega) M E (τ := 1 / 100) (by norm_num),
    bumped_value P.bumpData (η₀ := 1 / 4) (by norm_num) le_rfl,
    bumpFactor_one_le P.bumpData (η₀ := 1 / 4) (by norm_num) le_rfl, twoZeroT_ratio_le hK,
    eventually_ge_atTop (1 : ℝ)]
    with c htrc he8 hII hfloorfam hv hR1 hrat hc1 d hd N' hN' hcut x hx
  have hc : 0 < c := lt_of_lt_of_le one_pos hc1
  have hu0 : 0 < c ^ (-(2 / 5 : ℝ)) := Real.rpow_pos_of_pos hc _
  have hxi : xiStar < x := by linarith only [hx, hu0]
  have hl : 0 < lambdaComb c := Real.rpow_pos_of_pos (mul_pos kTip_pos hc) _
  obtain ⟨hσ, hε⟩ := comb_family_bounds hl (hb d hd)
  obtain ⟨hnode, R, r, hR, hr, hD, hfl, hlog⟩ :=
    hII d.sigmaSeq (fun k => lambdaComb c * d.epsHatSite k) hσ hε x hx
  obtain ⟨hTpos, hTle⟩ := hrat d hd x hx
  obtain ⟨hbase, hbump⟩ := hv 2 (n + 2) N' d.sigmaSeq (fun k => lambdaComb c * d.epsHatSite k) x
    (by omega) hN'
  have hrr : r = combReal c 2 (n + 2) (1 / 4) d.sigmaSeq (fun k => lambdaComb c * d.epsHatSite k) x := by
    have := hD.symm.trans hbase
    exact_mod_cast this
  set Rb := bumpFactor P.bumpData c (1 / 4) (n + 2) N' x with hRb
  have hRb1 : 1 ≤ Rb := hR1 (n + 2) N' x
  set T : ℝ := tFac (d.chiP c) x with hT
  set s : ℝ := 1 / Real.cosh (π * x / 2) ^ 2 with hs
  have hspos : 0 < s := by positivity
  have hLev := levComb_pos c 2 x
  have hTL : 0 < T * levComb c 2 x := mul_pos hTpos hLev
  have hbc : d.bumpComb P.bumpData c N' (x : ℂ) = ((T * (Rb * r) : ℝ) : ℂ) := by
    unfold bumpComb bumpedBase
    rw [hbump, hrr, tFac_eq]
    push_cast
    ring
  have hre : (sechSqProfile (x : ℂ) * d.bumpComb P.bumpData c N' (x : ℂ)).re = s * (T * (Rb * r)) := by
    rw [Upper.Positivity.sechSqProfile_ofReal, hbc, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hbfl := base_floor_nu hspos.le hR hr hfl hlog
  have hmono : s * r ≤ s * (Rb * r) := by
    refine mul_le_mul_of_nonneg_left ?_ hspos.le
    nlinarith only [hRb1, hr]
  have hlow0 : (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000) * (T * levComb c 2 x) ≤
      s * (T * (Rb * r)) := by
    have := mul_le_mul_of_nonneg_left (hbfl.trans hmono) hTpos.le
    nlinarith only [this]
  have hw0 : 0 ≤ C * c ^ (-(2 / 5 : ℝ)) := mul_nonneg hC hu0.le
  have hw1 : C * c ^ (-(2 / 5 : ℝ)) ≤ 1 / 50 := he8
  have htx := htrc d hd N' hN' x hx
  rw [hexp] at htx
  have hnorm := norm_le_rhoRp_mul_lev_T hc hnode hxi p (T := T) hw0 hTle htx
  have hhh := (Complex.re_le_norm _).trans hnorm
  have hq0 : 0 ≤ rhoRp p x * (1001 / 1000) := mul_nonneg (rhoRp_nonneg p hxi) (by norm_num)
  rw [Complex.sub_re, hre]
  by_cases hnear : x ≤ xiStar + 3 * P.r
  · have hq : rhoRp p x ≤ 1 / 10 := P.near x hxi (by linarith [P.r_pos])
    exact close_of_bounds hTL hq0 hw0 hhh hlow0
      (margin_aux (rhoRp_nonneg p hxi) hq hw0 hw1 nu_margin_near')
  · push Not at hnear
    by_cases hmac : x ≤ P.X - 1
    · have hq : rhoRp p x ≤ P.M := P.macro_le ⟨hnear.le, hmac⟩
      obtain ⟨rb, hrb, hfin⟩ := hfloorfam N' d.sigmaSeq (fun k => lambdaComb c * d.epsHatSite k) hN' hcut hσ hε x
        hnear.le hmac
      have hrb' : rb = Rb * r := by
        have h1 : bumpedComb P.bumpData c 2 (n + 2) N' (1 / 4) d.sigmaSeq
            (fun k => lambdaComb c * d.epsHatSite k) (x : ℂ) = (rb : ℂ) := hrb
        have h2 := h1.symm.trans hbump
        have h3 : rb = Rb * combReal c 2 (n + 2) (1 / 4) d.sigmaSeq
            (fun k => lambdaComb c * d.epsHatSite k) x := by exact_mod_cast h2
        rw [h3, hrr]
      rw [hrb'] at hfin
      have hfin' := mul_le_mul_of_nonneg_left hfin hTpos.le
      refine close_of_bounds hTL hq0 hw0 hhh (c := (1 - 1 / 100 : ℝ) * ((16 / 5) * (P.bumpData.H ^ 2 + 1 / 4)) *
        ((7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000))) ?_ ?_
      · calc _ = T * ((1 - 1 / 100 : ℝ) * ((16 / 5) * (P.bumpData.H ^ 2 + 1 / 4)) *
              ((7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000) * levComb c 2 x)) := by ring
          _ ≤ T * (1 / Real.cosh (π * x / 2) ^ 2 * (Rb * r)) := hfin'
          _ = s * (T * (Rb * r)) := by rw [hs]; ring
      · have hmg := macro_margin' P.M_nonneg P.floor_gt
        have hHd : P.bumpData.H = P.eta := rfl
        rw [hHd]
        exact margin_aux (rhoRp_nonneg p hxi) hq hw0 hw1 hmg
    · push Not at hmac
      have hq : rhoRp p x ≤ 6 / 10 := P.far x hmac.le
      exact close_of_bounds hTL hq0 hw0 hhh hlow0
        (margin_aux (rhoRp_nonneg p hxi) hq hw0 hw1 nu_margin_far')

/-- **Positivity form**: `2 g_w > 0` on `x ≥ ξ_* + c^{-2/5}` for the bumped two-zero comb. -/
theorem twoZeroBump_regionII_pos (p : ℕ) (P : RpParams p) {n : ℕ} {𝒦 : Set (TwoZeroDesign n)}
    (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' →
      (∀ k : ℕ, 1 ≤ k → chiQuantile c (k : ℝ) ≤ P.X → k ≤ N') →
      ∀ x : ℝ, xiStar + c ^ (-(2 / 5 : ℝ)) ≤ x →
        0 < (sechSqProfile (x : ℂ) * d.bumpComb P.bumpData c N' (x : ℂ) -
          edgeHankelP p c (fun b => sechSqProfile b * d.bumpComb P.bumpData c N' b) (c * x ^ 2 / 3)).re := by
  filter_upwards [twoZeroBump_regionII p P hK hA, twoZeroT_ratio_le hK] with c h hr d hd N' hN' hcut x hx
  have hpos := mul_pos (hr d hd x hx).1 (levComb_pos c 2 x)
  have := h d hd N' hN' hcut x hx
  linarith only [this, hpos]

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroBump_regionII' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_regionII

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroBump_regionII_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_regionII_pos

end FormalResearch.ModularBootstrap.TwoLevel
