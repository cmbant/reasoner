module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedBumpFloors
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedBumpSeparation
public import FormalResearch.ModularBootstrap.Upper.Positivity.PropositionIIIRegionII

/-!
# Region II of Lemma `U*(w)`: the bumped ramped comb at every weight (`fw:Ustar` Steps 4 and 5)

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma `U*(w)` (`fw:Ustar`), Steps 4 (near-tip Region II) and 5 (macroscopic Region II),
with `fw:e1.6`, `fw:e2.2`, `fw:e2.3`, `fw:e3.1`, `fw:e3.5` of `upper_transfer.tex`.

Fix `p` (`w = p + 1`) and the bump parameters `Pp : RpParams p`.  The bumped ramped comb is the `designComb` with cut
`N' = rampedBumpCut` (above the block and above `n_cap + 6`) of the data `(bumpSigma .. (rampedSigma d c'),
bumpEps .. (rampedEps P c'))`; `twoGW p` is `2 g_w` (`h₀^{(p)}(x) - 𝓗_{p+1} h₀^{(p)}(t)`, real part).

* `rampedBumped_regionII`: there is `C₀ ≥ 1` such that for every `P` with `C₀ ≤ P.C_mid` (any `C_I`, `M_0`), `c'` large, `d ∈ [0, 1]` and
  every `x ≥ ξ_I = ξ_* + c'^{-3/5}`: `2 g_w(c' x²/3) > 0`.  The constant is `C₀ = max(C_mid^{II}(w), C_mid^{sep}(r_p))` of the
  paper: `C_mid^{II}(w)² = max(1, C_2/(4 c_fl))` with `C_2 = C_p (2/k_tip)^{5/6}`, `C_p` the near-tip constant of
  `ρ_∞ R_p` (`rhoRp_near_tip`, replacing `C_v R̄_p`), and `C_mid^{sep}` the separation constant of `rampedBlockAbove`.
* the three ranges: near tip (cells `N₀ ≤ n ≤ n_cap + 6`: `rampedD_nearTip_floor`, `R_bump ≥ 1`, the transform of
  `phase_packageP` against `ρ_∞ R_p ≤ C_p (x - ξ_*)^{5/4}`, `nearTip_gap_pos`), macroscopic `x ≤ ξ_* + 3 r_p` (floor `ν`
  against `ρ_∞ R_p ≤ 0.10`), the bump block `ξ_* + 3 r_p ≤ x ≤ X_p - 1` (`bump_floor` against `M_amp`) and the far range
  (`ρ_∞ R_p ≤ 0.60`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Design Upper.Holes Upper.Positivity Upper.Hankel Upper.Bump

/-- The dichotomy that closes the near-tip range (the proof of `rampedNearTip`): for `C_mid² ≥ C_2/(4 c_fl)`, either
`2 C_2 q ≤ 16 c_fl η_n²` (`n < n_cap`) or `η_n = 1/4` and `C_2 q ≤ c_fl/2` (`n_cap ≤ n ≤ n_cap + 6`), `q = (n/c')^{5/6}`. -/
lemma nearTip_disj (P : RampedParams) {c' C2 cF : ℝ} (hc'0 : 0 < c') (hcF : 0 < cF) (hC2 : 0 < C2)
    (hPsq : C2 / (4 * cF) ≤ P.Cmid ^ 2) (hcap : (1 / (32 * P.Cmid ^ 2)) ^ (6 / 5 : ℝ) * c' ≤ nCap P c')
    (hc'13 : 13 / (1 / (32 * P.Cmid ^ 2)) ^ (6 / 5 : ℝ) ≤ c') {n : ℕ} (hn1 : 1 ≤ n)
    (hnc : n ≤ nCap P c' + 6) :
    2 * (C2 * ((n : ℝ) / c') ^ (5 / 6 : ℝ)) ≤ 16 * cF * rampedEta P c' n ^ 2 ∨
      (rampedEta P c' n = 1 / 4 ∧ C2 * ((n : ℝ) / c') ^ (5 / 6 : ℝ) ≤ cF / 2) := by
  have hCm : 0 < P.Cmid ^ 2 := by have := P.one_le_Cmid; positivity
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  set q : ℝ := ((n : ℝ) / c') ^ (5 / 6 : ℝ) with hq
  have hq0 : 0 < q := by positivity
  have hC2q : C2 * q = (C2 / (4 * cF) * q) * (4 * cF) := by field_simp
  have h3 : C2 / (4 * cF) * q ≤ P.Cmid ^ 2 * q := mul_le_mul_of_nonneg_right hPsq hq0.le
  by_cases hlt : n < nCap P c'
  · left
    have h1 := etaArg_lt_of_lt_nCap P c' hlt
    have h2 := etaArg_ge_second P hc'0 n
    rw [rampedEta_sq P hc'0, etaSq, min_eq_right h1.le]
    have h5 : P.Cmid ^ 2 * q ≤ etaArg P c' n := h2
    have h6 : C2 / (4 * cF) * q ≤ etaArg P c' n := h3.trans h5
    have h7 : 4 * cF * (C2 / (4 * cF) * q) ≤ 4 * cF * etaArg P c' n :=
      mul_le_mul_of_nonneg_left h6 (by positivity)
    have h8 : 4 * cF * (C2 / (4 * cF) * q) = C2 * q := by rw [hC2q]; ring
    have h9 : 0 < C2 * q := mul_pos hC2 hq0
    linarith
  · right
    have hge : nCap P c' ≤ n := not_lt.1 hlt
    refine ⟨rampedEta_eq_quarter P hc'0 hge, ?_⟩
    have hs : 0 < (1 / (32 * P.Cmid ^ 2)) ^ (6 / 5 : ℝ) := by positivity
    have h13 : (13 : ℝ) ≤ nCap P c' := by
      have := (div_le_iff₀ hs).1 hc'13
      linarith
    have hnc1 : 1 ≤ nCap P c' := by exact_mod_cast (by linarith : (1 : ℝ) ≤ nCap P c')
    have hlt' := etaArg_lt_of_lt_nCap P c' (k := nCap P c' - 1) (by omega)
    have h2 := etaArg_ge_second P hc'0 (nCap P c' - 1)
    have hcast : ((nCap P c' - 1 : ℕ) : ℝ) = (nCap P c' : ℝ) - 1 := by
      rw [Nat.cast_sub hnc1]; simp
    rw [hcast] at h2
    have hsec : P.Cmid ^ 2 * (((nCap P c' : ℝ) - 1) / c') ^ (5 / 6 : ℝ) < 1 / 16 := lt_of_le_of_lt h2 hlt'
    have hnle : (n : ℝ) ≤ 2 * ((nCap P c' : ℝ) - 1) := by
      have : (n : ℝ) ≤ nCap P c' + 6 := by exact_mod_cast hnc
      linarith
    generalize hm : ((nCap P c' : ℝ) - 1) / c' = m at hsec
    have hm0 : 0 ≤ m := by rw [← hm]; apply div_nonneg _ hc'0.le; linarith
    have h1 : (n : ℝ) / c' ≤ 2 * m := by
      rw [← hm, ← mul_div_assoc]; exact div_le_div_of_nonneg_right hnle hc'0.le
    have h2' : (2 : ℝ) ^ (5 / 6 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (5 / 6 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hmp : 0 ≤ m ^ (5 / 6 : ℝ) := Real.rpow_nonneg hm0 _
    have hqle : q ≤ 2 * m ^ (5 / 6 : ℝ) := by
      calc q ≤ (2 * m) ^ (5 / 6 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by norm_num)
        _ = (2 : ℝ) ^ (5 / 6 : ℝ) * m ^ (5 / 6 : ℝ) := Real.mul_rpow (by norm_num) hm0
        _ ≤ 2 * m ^ (5 / 6 : ℝ) := mul_le_mul_of_nonneg_right h2' hmp
    have hqle2 : P.Cmid ^ 2 * q ≤ 1 / 8 := by
      have h5 := mul_le_mul_of_nonneg_left hqle hCm.le
      have h6 : P.Cmid ^ 2 * (2 * m ^ (5 / 6 : ℝ)) = 2 * (P.Cmid ^ 2 * m ^ (5 / 6 : ℝ)) := by ring
      linarith
    have h7 : (C2 / (4 * cF) * q) * (4 * cF) ≤ (1 / 8) * (4 * cF) :=
      mul_le_mul_of_nonneg_right (h3.trans hqle2) (by positivity)
    linarith

/-- **Region II of Lemma `U*(w)`** (`fw:Ustar`, Steps 4 and 5): for every `p` and bump parameters `Pp`, there is `C₀ ≥ 1`
such that for every ramped parameter set with `C₀ ≤ C_mid` (any `C_I`, `M_0`), for `c'` large, `d ∈ [0, 1]` and every
`x ≥ ξ_I = ξ_* + c'^{-3/5}`, the order-`p` test `2 g_w(c' x²/3)` of the bumped ramped comb is positive. -/
theorem rampedBumped_regionII (p : ℕ) (Pp : RpParams p) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ P : RampedParams, C₀ ≤ P.Cmid → ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ 1 →
      ∀ x : ℝ, xiStar + c' ^ (-(3 / 5 : ℝ)) ≤ x →
        0 < twoGW p c' 1 (rampedBumpCut Pp.bumpData P c') (1 / 4)
          (bumpSigma c' (nCap P c' + 6) (rampedSigma d c'))
          (bumpEps Pp.bumpData c' (nCap P c' + 6) (1 / 4) (rampedEps P c')) x := by
  obtain ⟨Cρ, hCρ, hρ⟩ := rhoRp_near_tip p
  obtain ⟨K, A, Cε, Ctr, KG, hK, hA, hCε, hCtr, hKG, hpk⟩ :=
    phase_packageP p 1 le_rfl (η₀ := 1 / 4) (P := 1 + 1) (θ := 3 / 5) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Csep, hsep⟩ := rampedBlockAbove Pp.bumpData
  have hk := kTip_pos
  have hcF := cFl_pos
  set C2 : ℝ := Cρ * (2 / kTip) ^ (5 / 6 : ℝ) with hC2def
  have hC2 : 0 < C2 := by positivity
  set Cm2 : ℝ := max 1 (C2 / (4 * cFl)) with hCm2
  have hCm2_1 : 1 ≤ Cm2 := le_max_left _ _
  have hCm2_2 : C2 / (4 * cFl) ≤ Cm2 := le_max_right _ _
  refine ⟨max (max (Real.sqrt Cm2) Csep) 1, le_max_right _ _, fun P hP => ?_⟩
  have hPC1 : Real.sqrt Cm2 ≤ P.Cmid := (le_max_left _ _).trans ((le_max_left _ _).trans hP)
  have hPC2 : Csep ≤ P.Cmid := (le_max_right _ _).trans ((le_max_left _ _).trans hP)
  have hPsq : C2 / (4 * cFl) ≤ P.Cmid ^ 2 := by
    have h1 : Cm2 ≤ P.Cmid ^ 2 := by
      calc Cm2 = (Real.sqrt Cm2) ^ 2 := (Real.sq_sqrt (by linarith)).symm
        _ ≤ P.Cmid ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hPC1 2
    exact hCm2_2.trans h1
  obtain ⟨N0, hnear⟩ := rampedD_nearTip_floor P (ε := 1 / 8) (by norm_num) (by norm_num)
  obtain ⟨Cg, hCg, hgev⟩ := siteGap_eventually_le
  have hexp : (-1 + 3 * (3 / 5 : ℝ) / 2) = -(1 / 10 : ℝ) := by norm_num
  have e8 : ∀ᶠ c' in atTop, Ctr * c' ^ (-(1 / 10 : ℝ)) ≤ 1 / 50 :=
    ((tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).const_mul Ctr).eventually_le_const
      (by norm_num)
  have hν : (0 : ℝ) < (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000) := by norm_num
  filter_upwards [hnear, rampedMacro_floor P, hsep P hPC2, hpk, ramped_phaseHyp,
    bumped_phaseHyp Pp.bumpData 1 le_rfl (η₀ := 1 / 4) (by norm_num) le_rfl,
    bumped_value Pp.bumpData (η₀ := 1 / 4) (by norm_num) le_rfl,
    bumpFactor_one_le Pp.bumpData (η₀ := 1 / 4) (by norm_num) le_rfl,
    bump_floor Pp.bumpData (η₀ := 1 / 4) (by norm_num) le_rfl (τ := 1 / 100) (by norm_num),
    nCap_ge P, e8, exists_cell_of_xiI (max N0 1) (le_max_right _ _),
    eventually_chi_le_xiI (a := 2) (by norm_num),
    eventually_ge_atTop (13 / (1 / (32 * P.Cmid ^ 2)) ^ (6 / 5 : ℝ)),
    eventually_ge_atTop (10000 : ℝ), hgev]
    with c' hflr hmac hba hpkc hph hbph hv hR1 hbfl hcap he8 hcellx hchi2 hc'13 hc'4 hgapev d hd hd1 x hx
  obtain ⟨-, -, -, hgap⟩ := hgapev
  have hc'0 : 0 < c' := by linarith
  have hu0 : 0 < c' ^ (-(3 / 5 : ℝ)) := Real.rpow_pos_of_pos hc'0 _
  have hxs : xiStar < x := by linarith only [hx, hu0]
  have hx32 : chiQuantile c' (((1 : ℕ) : ℝ) + 1 / 2) < x := by
    rw [Nat.cast_one]
    refine lt_of_lt_of_le ?_ (hchi2.trans hx)
    exact (chiQuantile_strictMonoOn hc'0) (Set.mem_Ici.mpr (by norm_num)) (Set.mem_Ici.mpr (by norm_num))
      (by norm_num)
  set bd := Pp.bumpData with hbd
  set N₀ : ℕ := nCap P c' + 6 with hN₀
  set N' : ℕ := rampedBumpCut bd P c' with hN'
  have hN0N : N₀ ≤ N' := le_rampedBumpCut bd P c'
  have hcut : ∀ k : ℕ, 1 ≤ k → chiQuantile c' (k : ℝ) ≤ bd.X → k ≤ N' := rampedBumpCut_spec bd P hc'0
  -- the transform
  have hPH := hbph N₀ N' (rampedSigma d c') (rampedEps P c') 1 (hph P d hd hd1) hN0N
  obtain ⟨-, -, htrans, -⟩ := hpkc N' _ _ hPH
  rw [hexp] at htrans
  have hw0 : 0 ≤ Ctr * c' ^ (-(1 / 10 : ℝ)) := by
    have : 0 ≤ c' ^ (-(1 / 10 : ℝ)) := Real.rpow_nonneg hc'0.le _
    positivity
  have hnorm := norm_le_rhoRp_mul_lev hc'0 (f := 1) le_rfl hx32 hxs p
    (nh := ‖edgeHankelP p c' (designProfile c' 1 N' (1 / 4) (bumpSigma c' N₀ (rampedSigma d c'))
      (bumpEps bd c' N₀ (1 / 4) (rampedEps P c'))) (c' * x ^ 2 / 3)‖) (w := Ctr * c' ^ (-(1 / 10 : ℝ))) hw0
    (htrans x hx)
  have hq0 : 0 ≤ rhoRp p x := rhoRp_nonneg p hxs
  have hhh := (Complex.re_le_norm _).trans hnorm
  have hLev := levComb_pos c' 1 x
  -- the bumped value
  obtain ⟨hbase, hbump⟩ := hv 1 N₀ N' (rampedSigma d c') (rampedEps P c') x (by omega) hN0N
  set r : ℝ := combReal c' 1 N₀ (1 / 4) (rampedSigma d c') (rampedEps P c') x with hr
  set Rb : ℝ := bumpFactor bd c' (1 / 4) N₀ N' x with hRb
  have hRb1 : 1 ≤ Rb := hR1 N₀ N' x
  set s : ℝ := 1 / Real.cosh (π * x / 2) ^ 2 with hs
  have hspos : 0 < s := by positivity
  have hbc : designComb c' 1 N' (1 / 4) (bumpSigma c' N₀ (rampedSigma d c'))
      (bumpEps bd c' N₀ (1 / 4) (rampedEps P c')) (x : ℂ) = ((Rb * r : ℝ) : ℂ) := by
    have h := hbump
    unfold bumpedComb at h
    exact h
  have hprof : (designProfile c' 1 N' (1 / 4) (bumpSigma c' N₀ (rampedSigma d c'))
      (bumpEps bd c' N₀ (1 / 4) (rampedEps P c')) (x : ℂ)).re = s * (Rb * r) := by
    rw [designProfile_ofReal hbc, Complex.ofReal_re]
  have hrc : rampedComb P d c' = designComb c' 1 N₀ (1 / 4) (rampedSigma d c') (rampedEps P c') := rfl
  -- the closing inequality: `s r ≥ F Lev` and `‖H‖ ≤ q (1 + w) Lev` with `F > q (1 + w)` give `0 < 2 g_w`
  have hw50 : Ctr * c' ^ (-(1 / 10 : ℝ)) ≤ 1 / 50 := he8
  unfold twoGW
  rw [Complex.sub_re, hprof]
  -- cell
  obtain ⟨n, hnM, hcell⟩ := hcellx x hx
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hnM
  by_cases hnear' : n ≤ nCap P c' + 6
  · -- near-tip range
    have hnN0 : N0 ≤ n := (le_max_left _ _).trans hnM
    obtain ⟨hfs, hfl⟩ := hflr d hd hd1 n x hnN0 hnear' hcell hx
    have hf0 : 0 ≤ designSite c' (rampedSigma d c') 1 :=
      xiStar_pos.le.trans (designSite_ramped_nonneg hc'0 hd le_rfl)
    obtain ⟨r', hr', hr'0⟩ := designComb_real_nonneg hc'0 hgap 1 N₀ (rampedSigma d c') (rampedEps P c')
      (by omega) hfs hf0
    have hrr : r' = r := by
      have := hr'.symm.trans hbase
      exact_mod_cast this
    rw [hrr] at hr'0 hr'
    have hnormc : ‖rampedComb P d c' (x : ℂ)‖ = r := by
      rw [hrc, hr', Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr'0]
    rw [hnormc] at hfl
    have hmono : s * r ≤ s * (Rb * r) := by
      exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hr'0 hRb1) hspos.le
    -- the amplitude
    have hx1 : x ≤ xiStar + 1 := by
      have h1 : x < chiQuantile c' (((n + 1 : ℕ) : ℝ)) := hcell.2
      have hcap' := nCap_le P hc'4
      have h2 : ((n + 1 : ℕ) : ℝ) ≤ 37 / 1000 * c' := by
        have : (n : ℝ) ≤ nCap P c' + 6 := by exact_mod_cast hnear'
        push_cast; linarith
      have := siteRadius_le_fifth hc'0 (by push_cast; linarith : (1 / 4 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)) h2
      unfold siteRadius at this
      linarith only [h1, this]
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    set q : ℝ := ((n : ℝ) / c') ^ (5 / 6 : ℝ) with hqdef
    have hq : 0 < q := by positivity
    have hcellb := cell_pow_bound hc'0 hn1 hcell
    have hrho : rhoRp p x ≤ C2 * q := by
      refine (hρ x hxs hx1).trans ?_
      calc Cρ * (x - xiStar) ^ (5 / 4 : ℝ) ≤ Cρ * ((2 / kTip) ^ (5 / 6 : ℝ) * q) :=
            mul_le_mul_of_nonneg_left hcellb hCρ.le
        _ = C2 * q := by rw [hC2def]; ring
    have hw8 : Ctr * c' ^ (-(1 / 10 : ℝ)) ≤ 1 / 8 := hw50.trans (by norm_num)
    have hdisj := nearTip_disj P hc'0 hcF hC2 hPsq hcap hc'13 hn1 hnear'
    have hgap' := nearTip_gap_pos (cF := cFl) (C2 := C2) (q := q) (η := rampedEta P c' n) (E := 1 / 8)
      (w := Ctr * c' ^ (-(1 / 10 : ℝ))) hcF (mul_pos hC2 hq) (rampedEta_nonneg P c' n)
      (rampedEta_le P c' n) le_rfl hw8 hdisj
    have hamp : (edgeHankelP p c' (designProfile c' 1 N' (1 / 4) (bumpSigma c' N₀ (rampedSigma d c'))
        (bumpEps bd c' N₀ (1 / 4) (rampedEps P c'))) (c' * x ^ 2 / 3)).re ≤
          (C2 * q * (1 + Ctr * c' ^ (-(1 / 10 : ℝ)))) * levComb c' 1 x := by
      refine hhh.trans ?_
      calc rhoRp p x * (1 + Ctr * c' ^ (-(1 / 10 : ℝ))) * levComb c' 1 x
          ≤ (C2 * q) * (1 + Ctr * c' ^ (-(1 / 10 : ℝ))) * levComb c' 1 x := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrho (by linarith)) hLev.le
        _ = _ := by ring
    have hfl' : cFl * min 1 (16 * rampedEta P c' n ^ 2) * (1 - 1 / 8) * levComb c' 1 x ≤ s * r :=
      (le_div_iff₀ hLev).1 hfl
    have : 0 < (cFl * min 1 (16 * rampedEta P c' n ^ 2) * (1 - 1 / 8) -
        C2 * q * (1 + Ctr * c' ^ (-(1 / 10 : ℝ)))) * levComb c' 1 x := mul_pos (by linarith) hLev
    linarith only [this, hfl', hmono, hamp]
  · -- macroscopic range
    push Not at hnear'
    obtain ⟨hfs, hfl⟩ := hmac d hd hd1 n x (by omega) hcell
    have hf0 : 0 ≤ designSite c' (rampedSigma d c') 1 :=
      xiStar_pos.le.trans (designSite_ramped_nonneg hc'0 hd le_rfl)
    obtain ⟨r', hr', hr'0⟩ := designComb_real_nonneg hc'0 hgap 1 N₀ (rampedSigma d c') (rampedEps P c')
      (by omega) hfs hf0
    have hrr : r' = r := by
      have := hr'.symm.trans hbase
      exact_mod_cast this
    rw [hrr] at hr'0 hr'
    have hnormc : ‖rampedComb P d c' (x : ℂ)‖ = r := by
      rw [hrc, hr', Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr'0]
    rw [hnormc] at hfl
    have hmono : s * r ≤ s * (Rb * r) := by
      exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hr'0 hRb1) hspos.le
    have hhh' : _ ≤ rhoRp p x * (1 + Ctr * c' ^ (-(1 / 10 : ℝ))) * levComb c' 1 x := hhh
    have hq1 : ∀ q : ℝ, 0 ≤ q → q * (1 + Ctr * c' ^ (-(1 / 10 : ℝ))) ≤ q * (1 + 1 / 50) := fun q hq =>
      mul_le_mul_of_nonneg_left (by linarith) hq
    have key : 1 / 20 * levComb c' 1 x ≤ s * (Rb * r) - (edgeHankelP p c' (designProfile c' 1 N'
        (1 / 4) (bumpSigma c' N₀ (rampedSigma d c')) (bumpEps bd c' N₀ (1 / 4) (rampedEps P c')))
          (c' * x ^ 2 / 3)).re := by
      by_cases hnr : x ≤ xiStar + 3 * bd.r
      · have hbr : bd.r = Pp.r := rfl
        have hq : rhoRp p x ≤ 1 / 10 := Pp.near x hxs (by linarith [Pp.r_pos])
        refine close_of_bounds hLev hq0 hw0 hhh'
          (c := (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000)) (hfl.trans hmono) ?_
        have := hq1 _ hq0
        linarith only [this, hq, nu_margin_near]
      · push Not at hnr
        by_cases hmac' : x ≤ bd.X - 1
        · have hq : rhoRp p x ≤ Pp.M := Pp.macro_le ⟨hnr.le, hmac'⟩
          obtain ⟨rb, hrb, hfin⟩ := hbfl 1 N₀ N' (rampedSigma d c') (rampedEps P c') x _ (by omega) hN0N
            hba hcut hnr.le hmac' hν hfl
          have hrb' : rb = Rb * r := by
            have h1 : designComb c' 1 N' (1 / 4) (bumpSigma c' N₀ (rampedSigma d c'))
                (bumpEps bd c' N₀ (1 / 4) (rampedEps P c')) (x : ℂ) = (rb : ℂ) := hrb
            have := h1.symm.trans hbc
            exact_mod_cast this
          rw [hrb'] at hfin
          have hg : (bd.H ^ 2 + 1 / 4) / ((1 / 4 : ℝ) ^ 2 + 1 / 4) = (16 / 5) * (bd.H ^ 2 + 1 / 4) := by
            field_simp; norm_num
          rw [hg] at hfin
          refine close_of_bounds hLev hq0 hw0 hhh' (c := (1 - 1 / 100 : ℝ) * ((16 / 5) * (bd.H ^ 2 + 1 / 4)) *
            ((7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000))) ?_ ?_
          · refine le_trans (le_of_eq ?_) hfin
            ring
          · have hmg := macro_margin Pp.M_nonneg Pp.floor_gt
            have hMq : rhoRp p x * (1 + 1 / 50) ≤ Pp.M * (1 + 1 / 50) :=
              mul_le_mul_of_nonneg_right hq (by norm_num)
            have := hq1 _ hq0
            have hHd : bd.H = Pp.eta := rfl
            rw [hHd]
            linarith only [hmg, hMq, this]
        · push Not at hmac'
          have hq : rhoRp p x ≤ 6 / 10 := Pp.far x hmac'.le
          refine close_of_bounds hLev hq0 hw0 hhh'
            (c := (7 / 10 : ℝ) * (998 / 1000) * (998 / 1000) * (999 / 1000)) (hfl.trans hmono) ?_
          have := hq1 _ hq0
          linarith only [this, hq, nu_margin_far]
    linarith

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedBumped_regionII' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedBumped_regionII

end FormalResearch.ModularBootstrap.Upper.Ramped
