module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedRegionTwoGeom

/-!
# Near-tip Region II of Lemma U* for the ramped comb (`rem:thmU` Step (3))

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Step (3), "Amplitude" and the closing choice
`C_mid² ≥ C_2/(8 c_fl)`.

`rampedNearTip`: there is `C_mid ≥ 1` (a number depending on nothing but the absolute constants `C_v`, `c_fl`) such
that for every parameter set `P` with `P.C_mid = C_mid` (any `C_I ≥ 1`, any `M_0`) there are `N₀` and `c₀` such that
for `c' ≥ c₀`, `d ∈ [0, 1]`, `N₀ ≤ n ≤ n_cap + 6`, `x` in the reference cell `n` with `x ≥ ξ_I = ξ_* + c'^{-3/5}`,
the test function of the ramped design is positive: `0 < twoG c' 1 (n_cap + 6) (1/4) σ ε' x`.

Proof, as in the paper: the transform bound of `ramped_phase_package` (`θ = 3/5`) and `combAmplitude_le_vRhoInfty_mul_levComb`
give `‖ĥ₀‖ ≤ vρ_∞(x; 3/4)(1 + w) Lev`, `w = C c'^{-1/10}`; `nearTip_amp_le` and `x - ξ_* ≲ (n/c')^{2/3}` give the
amplitude `C_2 (n/c')^{5/6}(1 + w)` with `C_2 = C_v (2/k_tip)^{5/6}`; the floor of `rampedD_nearTip_twoG` is
`c_fl min(1, 16η_n²)(1 - 1/8)`; `nearTip_gap_pos` closes with `η_n² ≥ C_mid²(n/c')^{5/6}` for `n < n_cap` and, for
`n_cap ≤ n ≤ n_cap + 6` (`η_n = 1/4`), with the definition of `n_cap` (`η_{n_cap - 1}² < 1/16`).  The choice here is
`C_mid² = max(1, C_2/(4c_fl))`, which satisfies the paper's `C_mid² ≥ C_2/(8c_fl)` with room to spare.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Design Upper.Holes Upper.Positivity Upper.Hankel

/-- `(x - ξ_*)^{5/4} ≤ (2/k_tip)^{5/6} (n/c')^{5/6}` for `x` in the reference cell `n ≥ 1`. -/
lemma cell_pow_bound {c' x : ℝ} {n : ℕ} (hc' : 0 < c') (hn : 1 ≤ n) (hcell : inCell c' n x) :
    (x - xiStar) ^ (5 / 4 : ℝ) ≤ (2 / kTip) ^ (5 / 6 : ℝ) * ((n : ℝ) / c') ^ (5 / 6 : ℝ) := by
  have hk := kTip_pos
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hxs0 : 0 ≤ x - xiStar := by
    have := xiStar_le_chiQuantile_nat hc' hn
    linarith [hcell.1]
  have h1 : x < chiQuantile c' (((n + 1 : ℕ) : ℝ)) := hcell.2
  have hn14 : (1 / 4 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have h2 := (siteRadius_bounds hc' hn14).2
  have hn14 : (1 / 4 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have h3 := lambda_mul_phi_le hc' (a := ((n + 1 : ℕ) : ℝ)) hn14
  unfold siteRadius at h2
  have hB : ((n + 1 : ℕ) : ℝ) / (kTip * c') ≤ (2 / kTip) * ((n : ℝ) / c') := by
    push_cast
    rw [div_le_iff₀ (by positivity)]
    have : (2 / kTip) * ((n : ℝ) / c') * (kTip * c') = 2 * n := by field_simp
    rw [this]; linarith
  have hx : x - xiStar ≤ (((n + 1 : ℕ) : ℝ) / (kTip * c')) ^ (2 / 3 : ℝ) := by linarith
  have hB0 : 0 ≤ ((n + 1 : ℕ) : ℝ) / (kTip * c') := by positivity
  calc (x - xiStar) ^ (5 / 4 : ℝ) ≤ ((((n + 1 : ℕ) : ℝ) / (kTip * c')) ^ (2 / 3 : ℝ)) ^ (5 / 4 : ℝ) :=
        Real.rpow_le_rpow hxs0 hx (by norm_num)
    _ = (((n + 1 : ℕ) : ℝ) / (kTip * c')) ^ (5 / 6 : ℝ) := by
        rw [← Real.rpow_mul hB0]; norm_num
    _ ≤ ((2 / kTip) * ((n : ℝ) / c')) ^ (5 / 6 : ℝ) := Real.rpow_le_rpow hB0 hB (by norm_num)
    _ = (2 / kTip) ^ (5 / 6 : ℝ) * ((n : ℝ) / c') ^ (5 / 6 : ℝ) :=
        Real.mul_rpow (by positivity) (by positivity)

lemma etaArg_ge_second (P : RampedParams) {c' : ℝ} (hc' : 0 < c') (k : ℕ) :
    P.Cmid ^ 2 * ((k : ℝ) / c') ^ (5 / 6 : ℝ) ≤ etaArg P c' k := by
  unfold etaArg
  have := nTr_nonneg hc'
  have hs : 0 < √c' := Real.sqrt_pos.2 hc'
  have h0 : 0 ≤ P.CI ^ 2 * min (k : ℝ) (nTr c') / √c' := by
    have : 0 ≤ min (k : ℝ) (nTr c') := le_min (by positivity) this
    positivity
  linarith

/-- **Near-tip Region II for `D_*`** (`rem:thmU` Step (3)). -/
theorem rampedNearTip : ∃ Cmid : ℝ, 1 ≤ Cmid ∧ ∀ P : RampedParams, P.Cmid = Cmid →
    ∃ N0 : ℕ, ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ 1 → ∀ (n : ℕ) (x : ℝ), N0 ≤ n →
      n ≤ nCap P c' + 6 → inCell c' n x → xiStar + c' ^ (-(3 / 5 : ℝ)) ≤ x →
      0 < twoG c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c') x := by
  obtain ⟨Cv, hCv, hamp⟩ := nearTip_amp_le
  obtain ⟨K, A, Cph, KG, hK, hA, hCph, hKG, hph⟩ := ramped_phase_package
  have hk := kTip_pos
  have hcF := cFl_pos
  set C2 : ℝ := Cv * (2 / kTip) ^ (5 / 6 : ℝ) with hC2def
  have hC2 : 0 < C2 := by positivity
  set Cm2 : ℝ := max 1 (C2 / (4 * cFl)) with hCm2
  have hCm2_1 : 1 ≤ Cm2 := le_max_left _ _
  have hCm2_2 : C2 / (4 * cFl) ≤ Cm2 := le_max_right _ _
  refine ⟨Real.sqrt Cm2, by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hCm2_1, fun P hP => ?_⟩
  have hPsq : P.Cmid ^ 2 = Cm2 := by rw [hP]; exact Real.sq_sqrt (by linarith)
  obtain ⟨N0, hnear⟩ := rampedD_nearTip_twoG P (ε := 1 / 8) (by norm_num) (by norm_num)
  refine ⟨max N0 1, ?_⟩
  filter_upwards [hnear, hph, nCap_ge P, eventually_ge_atTop (10000 : ℝ),
    eventually_rpow_neg_le (p := 1 / 10) (by norm_num) (show 0 < 1 / (8 * (Cph + 1)) by positivity),
    eventually_chi_le_xiI (a := 2) (by norm_num),
    eventually_ge_atTop (13 / (1 / (32 * P.Cmid ^ 2)) ^ (6 / 5 : ℝ))]
    with c' hn' hph' hcap hc'4 hw hchi2 hc'13 d hd hd1 n x hn hnc hcell hxξ
  have hc'0 : 0 < c' := by linarith
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnN0 : N0 ≤ n := (le_max_left _ _).trans hn
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hCm : 0 < P.Cmid ^ 2 := by have := P.one_le_Cmid; positivity
  -- the amplitude
  set w : ℝ := Cph * c' ^ (-(1 / 10 : ℝ)) with hwdef
  have hw0 : 0 ≤ w := by
    have : 0 ≤ c' ^ (-(1 / 10 : ℝ)) := Real.rpow_nonneg hc'0.le _
    positivity
  have hw8 : w ≤ 1 / 8 := by
    have h1 : c' ^ (-(1 / 10 : ℝ)) ≤ 1 / (8 * (Cph + 1)) := hw
    have h2 : Cph * c' ^ (-(1 / 10 : ℝ)) ≤ (Cph + 1) * (1 / (8 * (Cph + 1))) := by
      have : 0 ≤ c' ^ (-(1 / 10 : ℝ)) := Real.rpow_nonneg hc'0.le _
      calc Cph * c' ^ (-(1 / 10 : ℝ)) ≤ (Cph + 1) * c' ^ (-(1 / 10 : ℝ)) := by nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (Cph + 1) * (1 / (8 * (Cph + 1))) = 1 / 8 := by field_simp
    linarith
  have hx32 : chiQuantile c' (((1 : ℕ) : ℝ) + 1 / 2) < x := by
    rw [Nat.cast_one]
    refine lt_of_lt_of_le ?_ (hchi2.trans hxξ)
    exact (chiQuantile_strictMonoOn hc'0) (Set.mem_Ici.mpr (by norm_num)) (Set.mem_Ici.mpr (by norm_num))
      (by norm_num)
  have hxs : xiStar < x := by
    have : 0 < c' ^ (-(3 / 5 : ℝ)) := Real.rpow_pos_of_pos hc'0 _
    linarith
  have hx1 : x ≤ xiStar + 1 := by
    have h1 : x < chiQuantile c' (((n + 1 : ℕ) : ℝ)) := hcell.2
    have hcap' := nCap_le P hc'4
    have h2 : ((n + 1 : ℕ) : ℝ) ≤ 37 / 1000 * c' := by
      have : (n : ℝ) ≤ nCap P c' + 6 := by exact_mod_cast hnc
      push_cast; linarith
    have := siteRadius_le_fifth hc'0 (by push_cast; linarith : (1 / 4 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)) h2
    unfold siteRadius at this
    linarith
  have hlev := levComb_pos c' 1 x
  set q : ℝ := ((n : ℝ) / c') ^ (5 / 6 : ℝ) with hq
  have hq0 : 0 < q := by positivity
  have hcellb := cell_pow_bound hc'0 hn1 hcell
  obtain ⟨-, -, hamp3, -⟩ := hph' P d hd hd1
  have hamp4 := hamp3 x hxξ
  have hcv := combAmplitude_le_vRhoInfty_mul_levComb hc'0 (f := 1) le_rfl hx32
  have hn1c : n1Comb 1 = 3 / 4 := by unfold n1Comb; norm_num
  rw [hn1c] at hcv
  have hv := hamp x w hxs hx1 hw0
  have hAmp : ‖edgeHankel c' (designProfile c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c'))
      (c' * x ^ 2 / 3)‖ ≤ (C2 * q * (1 + w)) * levComb c' 1 x := by
    refine hamp4.trans ?_
    have hw' : (1 + Cph * c' ^ (-(1 / 10 : ℝ))) = 1 + w := rfl
    rw [hw']
    calc combAmplitude c' x * (1 + w) ≤ (vRhoInfty x (3 / 4) * levComb c' 1 x) * (1 + w) :=
          mul_le_mul_of_nonneg_right hcv (by linarith)
      _ = (vRhoInfty x (3 / 4) * (1 + w)) * levComb c' 1 x := by ring
      _ ≤ (Cv * (x - xiStar) ^ (5 / 4 : ℝ) * (1 + w)) * levComb c' 1 x :=
          mul_le_mul_of_nonneg_right hv hlev.le
      _ ≤ (C2 * q * (1 + w)) * levComb c' 1 x := by
          apply mul_le_mul_of_nonneg_right _ hlev.le
          have : Cv * (x - xiStar) ^ (5 / 4 : ℝ) ≤ C2 * q := by
            calc Cv * (x - xiStar) ^ (5 / 4 : ℝ) ≤ Cv * ((2 / kTip) ^ (5 / 6 : ℝ) * q) :=
                  mul_le_mul_of_nonneg_left hcellb hCv.le
              _ = C2 * q := by rw [hC2def]; ring
          exact mul_le_mul_of_nonneg_right this (by linarith)
  have hfloor := hn' d hd hd1 n x (C2 * q * (1 + w)) hnN0 hnc hcell hxξ hAmp
  -- the closing arithmetic
  have hC2q : C2 * q = (C2 / (4 * cFl) * q) * (4 * cFl) := by field_simp
  have h3 : C2 / (4 * cFl) * q ≤ P.Cmid ^ 2 * q := by
    rw [hPsq]; exact mul_le_mul_of_nonneg_right hCm2_2 hq0.le
  have hdisj : 2 * (C2 * q) ≤ 16 * cFl * rampedEta P c' n ^ 2 ∨
      (rampedEta P c' n = 1 / 4 ∧ C2 * q ≤ cFl / 2) := by
    by_cases hlt : n < nCap P c'
    · left
      have h1 := etaArg_lt_of_lt_nCap P c' hlt
      have h2 := etaArg_ge_second P hc'0 n
      rw [rampedEta_sq P hc'0, etaSq, min_eq_right h1.le]
      have h5 : P.Cmid ^ 2 * q ≤ etaArg P c' n := h2
      have h6 : C2 / (4 * cFl) * q ≤ etaArg P c' n := h3.trans h5
      have h7 : 4 * cFl * (C2 / (4 * cFl) * q) ≤ 4 * cFl * etaArg P c' n :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
      have h8 : 4 * cFl * (C2 / (4 * cFl) * q) = C2 * q := by rw [hC2q]; ring
      have h9 : 0 < C2 * q := mul_pos hC2 hq0
      linarith
    · right
      have hge : nCap P c' ≤ n := not_lt.1 hlt
      refine ⟨rampedEta_eq_quarter P hc'0 hge, ?_⟩
      have hcapr : (1 / (32 * P.Cmid ^ 2)) ^ (6 / 5 : ℝ) * c' ≤ nCap P c' := hcap
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
      have h7 : (C2 / (4 * cFl) * q) * (4 * cFl) ≤ (1 / 8) * (4 * cFl) :=
        mul_le_mul_of_nonneg_right (h3.trans hqle2) (by positivity)
      linarith
  have hgap := nearTip_gap_pos (cF := cFl) (C2 := C2) (q := q) (η := rampedEta P c' n) (E := 1 / 8) (w := w)
    hcF (mul_pos hC2 hq0) (rampedEta_nonneg P c' n) (rampedEta_le P c' n) le_rfl hw8 hdisj
  have hpos : 0 < twoG c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c') x /
      levComb c' 1 x := by
    have : cFl * min 1 (16 * rampedEta P c' n ^ 2) * (1 - 1 / 8) - C2 * q * (1 + w) > 0 := by linarith
    linarith [hfloor]
  exact (div_pos_iff_of_pos_right hlev).1 hpos

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedNearTip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedNearTip

end FormalResearch.ModularBootstrap.Upper.Ramped
