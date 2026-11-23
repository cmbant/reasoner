module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedRegionTwoGeom
public import FormalResearch.ModularBootstrap.Upper.Ramped.CombBridge

/-!
# Macroscopic Region II of Lemma U* for the ramped comb (`rem:thmU` Step (4))

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Step (4): for `x ≥ χ'_{n_cap+6}` the hole
`H = {n-3, …, n+4}` consists of reference pairs (`η = 1/4`, `Δ_k = 0`), so `ρ_k = 1` on `H` and the shift cost is
`S = O(λ)`; with `e_L = O(λ)` and the amplitude of `ramped_phase_package`, `ramped_macro_margin` gives the margin
`2g/Lev ≥ 0.158 - o(1)`.

`rampedMacro`: for fixed `(C_I, C_mid)` (any `P : RampedParams`), `c'` large, `d ∈ [0, 1]`, every `x` in a reference cell
`n ≥ n_cap + 7` has `0 < twoG c' 1 (n_cap + 6) (1/4) σ ε' x`.  (The paper's range `x ≥ χ'_{n_cap+6}` is covered by
`rampedMacro` together with `rampedNearTip` at the cells `n ≤ n_cap + 6`.)  The shift cost is bounded directly through
`holeShiftCost_le_dist` with `a_k = C_s λ k^{-4/3}` (`k ≤ N_Ai`), `a_k = 0` beyond, and `D_k = r/2` for `k ≤ N_Ai`,
where `r` is the lower tip bound `χ_a - ξ_* ≥ r` for `a ≥ s c'` (`siteRadius_ge_const`, `s` from `nCap_ge`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Design Upper.Holes Upper.Positivity Upper.Hankel

lemma one_le_nAi {c' : ℝ} (hc' : 1 ≤ c') : 1 ≤ nAi c' := by
  unfold nAi
  exact Nat.ceil_pos.2 (Real.rpow_pos_of_pos (by linarith) _)

/-- A site below the Airy cut is `≥ r/2` to the left of `x`, and its displaced copy too. -/
lemma near_aux {s χ x ξ r : ℝ} (hr : 0 < r) (hΔ : |s - χ| ≤ r / 4) (hχ : χ - ξ ≤ r / 4)
    (hxr : r ≤ x - ξ) :
    s + r / 2 ≤ x ∧ r / 2 ≤ |x - χ| := by
  have h2 := (abs_le.mp hΔ).2
  refine ⟨by linarith, ?_⟩
  have : r / 2 ≤ x - χ := by linarith
  exact this.trans (le_abs_self _)

/-! ### 1. The weights of the shift-cost estimate -/

/-- `a_k = C_s λ k^{-4/3}` for `k ≤ N_Ai` and `0` beyond (`Δ_k = 0` for `k > N_Ai`). -/
noncomputable def macroA (c' Cs : ℝ) (k : ℕ) : ℝ :=
  if k ≤ nAi c' then Cs * lambdaComb c' * (k : ℝ) ^ (-(4 / 3 : ℝ)) else 0

/-- `D_k = r/2` for `k ≤ N_Ai`, `1` on the hole, and `|x - χ_k|` elsewhere. -/
noncomputable def macroD (c' x r : ℝ) (n k : ℕ) : ℝ :=
  if k ≤ nAi c' then r / 2 else if k ∈ holeSet n 4 then 1 else |x - chiQuantile c' (k : ℝ)|

lemma macroD_nonneg {c' x r : ℝ} (hr : 0 < r) (n k : ℕ) : 0 ≤ macroD c' x r n k := by
  unfold macroD
  split_ifs
  · positivity
  · exact zero_le_one
  · exact abs_nonneg _

lemma macroD_pos {c' x r : ℝ} (hc' : 0 < c') (hr : 0 < r) {n : ℕ} (hn1 : 1 ≤ n) (hcell : inCell c' n x)
    {k : ℕ} (hk : 1 ≤ k) : 0 < macroD c' x r n k := by
  unfold macroD
  split_ifs with h1 h2
  · positivity
  · exact one_pos
  · have hne : k ≠ n := by
      intro h; apply h2; rw [h]; simp only [Finset.mem_Icc]; omega
    exact abs_pos.2 (sub_ne_zero.2 (ne_chiQuantile_of_inCell hc' hn1 hk hcell hne))

lemma macroA_of_le {c' Cs : ℝ} {k : ℕ} (h : k ≤ nAi c') :
    macroA c' Cs k = Cs * lambdaComb c' * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
  unfold macroA; simp [h]

lemma macroA_of_gt {c' Cs : ℝ} {k : ℕ} (h : nAi c' < k) : macroA c' Cs k = 0 := by
  unfold macroA; simp [not_le.2 h]

lemma macroD_of_le {c' x r : ℝ} {n k : ℕ} (h : k ≤ nAi c') : macroD c' x r n k = r / 2 := by
  unfold macroD; simp [h]

lemma macroD_of_gt {c' x r : ℝ} {n k : ℕ} (h : nAi c' < k) (hk : k ∉ holeSet n 4) :
    macroD c' x r n k = |x - chiQuantile c' (k : ℝ)| := by
  unfold macroD; simp [not_le.2 h, hk]

lemma macroA_nonneg {c' Cs : ℝ} (hc' : 0 < c') (hCs : 0 ≤ Cs) (k : ℕ) : 0 ≤ macroA c' Cs k := by
  have := lambdaComb_pos' hc'
  by_cases h : k ≤ nAi c'
  · rw [macroA_of_le h]; positivity
  · rw [macroA_of_gt (not_le.1 h)]

lemma macro_term {c' x r Cs : ℝ} (hc' : 0 < c') (hr : 0 < r) (hCs : 0 ≤ Cs) (n k : ℕ) :
    (2 / macroD c' x r n k + π) * macroA c' Cs k ≤
      (4 / r + π) * (Cs * lambdaComb c' * (k : ℝ) ^ (-(4 / 3 : ℝ))) := by
  have hl := lambdaComb_pos' hc'
  have hpi := Real.pi_pos
  by_cases h : k ≤ nAi c'
  · rw [macroD_of_le h, macroA_of_le h]
    refine le_of_eq ?_
    congr 1
    field_simp
    ring
  · rw [macroA_of_gt (not_le.1 h), mul_zero]
    positivity

/-- The weighted sum of the shift cost: `T_1 + ∑_{k ∉ H} 2 T_k ≤ 7 β` when `T_k ≤ β k^{-4/3}`. -/
lemma macro_sum_bound {β : ℝ} (hβ : 0 ≤ β) (T : ℕ → ℝ) (hT : ∀ k, T k ≤ β * (k : ℝ) ^ (-(4 / 3 : ℝ)))
    (N n : ℕ) :
    T 1 + ∑ k ∈ (Finset.Icc (1 + 1) N).filter (fun k => k ∉ holeSet n 4), 2 * T k ≤ 7 * β := by
  have hB0 : ∀ k : ℕ, 0 ≤ β * (k : ℝ) ^ (-(4 / 3 : ℝ)) := fun k => by positivity
  have h1 : T 1 ≤ β := by
    have := hT 1
    simpa using this
  have hsum : ∑ k ∈ (Finset.Icc (1 + 1) N).filter (fun k => k ∉ holeSet n 4), 2 * T k ≤ 6 * β := by
    calc ∑ k ∈ (Finset.Icc (1 + 1) N).filter (fun k => k ∉ holeSet n 4), 2 * T k
        ≤ ∑ k ∈ (Finset.Icc (1 + 1) N).filter (fun k => k ∉ holeSet n 4),
            2 * (β * (k : ℝ) ^ (-(4 / 3 : ℝ))) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hT k) (by norm_num)
      _ ≤ ∑ k ∈ Finset.Ioc 1 N, 2 * (β * (k : ℝ) ^ (-(4 / 3 : ℝ))) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun k _ _ => by
            have := hB0 k; linarith)
          have := Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
          exact Finset.mem_Ioc.mpr ⟨by omega, this.2⟩
      _ = 2 * β * ∑ k ∈ Finset.Ioc 1 N, (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ ≤ 2 * β * 3 := by
          have h := sum_Ioc_rpow_neg_gt_one (p := 4 / 3) (by norm_num) (a := 1) le_rfl N
          simp only [Nat.cast_one, Real.one_rpow] at h
          have : ∑ k ∈ Finset.Ioc 1 N, (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 3 := by linarith
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = 6 * β := by ring
  linarith

/-! ### 2. The shift cost and the hole in the macroscopic range -/

/-- **The shift cost in the macroscopic range**: `S ≤ 7(4/r + π) C_s λ` for `x - χ_k ≥ r/2` (`k ≤ N_Ai`). -/
lemma macro_shiftCost (P : RampedParams) {c' x r Cs d : ℝ} (hc' : 0 < c') (hd : 0 ≤ d) (hr : 0 < r)
    (hCs : 0 ≤ Cs) (hAi1 : 1 ≤ nAi c') {n : ℕ} (hn1 : 1 ≤ n) (hcell : inCell c' n x) (hxs : xiStar ≤ x)
    (hnear : ∀ k : ℕ, 1 ≤ k → k ≤ nAi c' → r / 2 ≤ |x - chiQuantile c' (k : ℝ)|)
    (hsh : ∀ k : ℕ, 1 ≤ k →
      |designSite c' (rampedSigma d c') k - chiQuantile c' (k : ℝ)| ≤ Cs * lambdaComb c' * (k : ℝ) ^ (-(4 / 3 : ℝ)))
    (hCsl : Cs * lambdaComb c' ≤ r / 4) :
    holeShiftCost c' x (rampedSigma d c') 1 (nCap P c' + 6) n 4 ≤ 7 * ((4 / r + π) * (Cs * lambdaComb c')) := by
  have hl := lambdaComb_pos' hc'
  have hbound := holeShiftCost_le_dist (c' := c') hxs (rampedSigma d c') (f := 1) (N := nCap P c' + 6)
    (by omega) n (macroA c' Cs) (macroD c' x r n) (fun k h1 _ => macroD_pos hc' hr hn1 hcell h1)
    (fun k h1 _ => ⟨xiStar_pos.le.trans (designSite_ramped_nonneg hc' hd h1),
      xiStar_pos.le.trans (xiStar_le_chiQuantile_nat hc' h1)⟩)
    (fun k h1 _ _ => by
      by_cases h : k ≤ nAi c'
      · rw [macroA_of_le h]; exact hsh k h1
      · have hk := not_le.1 h
        rw [macroA_of_gt hk, designSite_ramped_eq_of_gt hc' d hk (by omega), sub_self, abs_zero])
    (fun k h1 _ _ => by
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast h1
      have hkp : (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hk1 (by norm_num)
      have hD0 := macroD_nonneg (c' := c') (x := x) hr n k
      by_cases h : k ≤ nAi c'
      · rw [macroA_of_le h, macroD_of_le h]
        have : Cs * lambdaComb c' * (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ Cs * lambdaComb c' * 1 :=
          mul_le_mul_of_nonneg_left hkp (by positivity)
        linarith
      · rw [macroA_of_gt (not_le.1 h)]
        linarith)
    (fun k h1 h2 hk => by
      by_cases h : k ≤ nAi c'
      · rw [macroD_of_le h]; exact hnear k h1 h
      · have hkH : k ∉ holeSet n 4 := by
          rcases hk with rfl | hk
          · exact absurd hAi1 h
          · exact hk
        rw [macroD_of_gt (not_le.1 h) hkH])
  refine hbound.trans ?_
  have hβ : 0 ≤ (4 / r + π) * (Cs * lambdaComb c') := by
    have := Real.pi_pos; positivity
  have := macro_sum_bound hβ (fun k => (2 / macroD c' x r n k + π) * macroA c' Cs k) (fun k => by
    have := macro_term hc' hr hCs (x := x) n k
    calc (2 / macroD c' x r n k + π) * macroA c' Cs k ≤
        (4 / r + π) * (Cs * lambdaComb c' * (k : ℝ) ^ (-(4 / 3 : ℝ))) := this
      _ = (4 / r + π) * (Cs * lambdaComb c') * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by ring) (nCap P c' + 6) n
  simpa using this

/-- The hole hypothesis for cells beyond the cut. -/
lemma macro_holeHyp (P : RampedParams) {c' d : ℝ} (hc' : 0 < c') (hd : 0 ≤ d) (hAi : nAi c' ≤ nCap P c')
    {n : ℕ} (hn : nCap P c' + 7 ≤ n) :
    RampedHoleHyp c' 1 (nCap P c' + 6) n (rampedSigma d c') (rampedEta P c') 0 := by
  refine ⟨fun k _ _ => ⟨rampedEta_nonneg P c' k, rampedEta_le P c' k⟩,
    fun k _ _ => rampedEta_mono P hc' (Nat.le_succ k),
    fun k hk _ => rampedSigma_nonneg hc' hd hk, ?_, ?_⟩
  · intro k hk1 hkN hkH
    have hkH' := Finset.mem_Icc.mp hkH
    have hk : nAi c' < k := by omega
    rw [designSite_ramped_eq_of_gt hc' d hk (by omega), sub_self, abs_zero, zero_mul]
  · intro k hk1 hkN hkn
    omega

lemma macro_eta14 (P : RampedParams) {c' : ℝ} (hc' : 0 < c') {n : ℕ} (hn : nCap P c' + 7 ≤ n) :
    ∀ k, 1 < k → k ≤ nCap P c' + 6 → k ∈ holeSet n 4 → rampedEta P c' k = 1 / 4 := by
  intro k hk1 hkN hkH
  have hkH' := Finset.mem_Icc.mp hkH
  exact rampedEta_eq_quarter P hc' (by omega)

/-- Sites other than the hole stay off `x`, and the first site is left of `x`. -/
lemma macro_out (P : RampedParams) {c' x r d : ℝ} (hc' : 0 < c') (hAi1 : 1 ≤ nAi c')
    {n : ℕ} (hn1 : 1 ≤ n) (hcell : inCell c' n x)
    (hnear : ∀ k : ℕ, 1 ≤ k → k ≤ nAi c' → designSite c' (rampedSigma d c') k + r / 2 ≤ x) (hr : 0 < r) :
    designSite c' (rampedSigma d c') 1 < x ∧
      ∀ k, 1 < k → k ≤ nCap P c' + 6 → k ∉ holeSet n 4 → designSite c' (rampedSigma d c') k ≠ x := by
  refine ⟨by have := hnear 1 le_rfl hAi1; linarith, ?_⟩
  intro k hk1 hkN hkH
  by_cases hkn : k ≤ nAi c'
  · have := hnear k (by omega) hkn
    intro h
    linarith
  · have hk : nAi c' < k := not_le.1 hkn
    rw [designSite_ramped_eq_of_gt hc' d hk (by omega)]
    have hne : k ≠ n := by
      intro h; apply hkH; rw [h]; simp only [Finset.mem_Icc]; omega
    exact (ne_chiQuantile_of_inCell hc' hn1 (by omega) hcell hne).symm

/-- The amplitude of `ĥ₀` in the macroscopic range, as `vρ_∞(x; 3/4)(1 + w) Lev`. -/
lemma macro_amp (P : RampedParams) {c' x d Cph : ℝ} (hc' : 0 < c') (hCph : 0 ≤ Cph) {n : ℕ} (hn : 7 ≤ n)
    (hcell : inCell c' n x)
    (hamp : ‖edgeHankel c' (designProfile c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c'))
        (c' * x ^ 2 / 3)‖ ≤ combAmplitude c' x * (1 + Cph * c' ^ (-(1 / 10 : ℝ)))) :
    ‖edgeHankel c' (designProfile c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c')
      (fun k => rampedEta P c' k * siteGap c' k)) (c' * x ^ 2 / 3)‖ ≤
      vRhoInfty x (3 / 4) * (1 + Cph * c' ^ (-(1 / 10 : ℝ))) * levComb c' 1 x := by
  have hx32 : chiQuantile c' (((1 : ℕ) : ℝ) + 1 / 2) < x := by
    rw [Nat.cast_one]
    refine lt_of_lt_of_le ?_ hcell.1
    have h7 : (7 : ℝ) ≤ n := by exact_mod_cast hn
    exact (chiQuantile_strictMonoOn hc') (Set.mem_Ici.mpr (by norm_num)) (Set.mem_Ici.mpr (by linarith))
      (by linarith)
  have hcv := combAmplitude_le_vRhoInfty_mul_levComb hc' (f := 1) le_rfl hx32
  have hn1c : n1Comb 1 = 3 / 4 := by unfold n1Comb; norm_num
  rw [hn1c] at hcv
  have hw0 : 0 ≤ Cph * c' ^ (-(1 / 10 : ℝ)) := by
    have : 0 ≤ c' ^ (-(1 / 10 : ℝ)) := Real.rpow_nonneg hc'.le _
    positivity
  refine hamp.trans ?_
  calc combAmplitude c' x * (1 + Cph * c' ^ (-(1 / 10 : ℝ))) ≤
        (vRhoInfty x (3 / 4) * levComb c' 1 x) * (1 + Cph * c' ^ (-(1 / 10 : ℝ))) :=
        mul_le_mul_of_nonneg_right hcv (by linarith)
    _ = vRhoInfty x (3 / 4) * (1 + Cph * c' ^ (-(1 / 10 : ℝ))) * levComb c' 1 x := by ring

/-- `C l ≤ ε` from `0 ≤ l ≤ ε/(C+1)`. -/
lemma mul_le_of_le_div_succ {C l ε : ℝ} (hC : 0 ≤ C) (hl0 : 0 ≤ l) (hε : 0 ≤ ε) (hl : l ≤ ε / (C + 1)) : C * l ≤ ε := by
  have h1 : C * l ≤ (C + 1) * l := by nlinarith
  have h2 : (C + 1) * l ≤ (C + 1) * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hl (by linarith)
  have h3 : (C + 1) * (ε / (C + 1)) = ε := by field_simp
  linarith

/-- **Macroscopic Region II for `D_*`** (`rem:thmU` Step (4)). -/
theorem rampedMacro (P : RampedParams) :
    ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ 1 → ∀ (n : ℕ) (x : ℝ), nCap P c' + 7 ≤ n →
      inCell c' n x →
      0 < twoG c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (rampedEps P c') x := by
  obtain ⟨N₀, Cm, hCm, hmarg⟩ := ramped_macro_margin
  obtain ⟨Cs, hCs, hsh⟩ := rampedShift_le
  obtain ⟨CL, hCL, hLev⟩ := eLeftComb_bounds
  obtain ⟨Cg, hCg, hgev⟩ := siteGap_eventually_le
  obtain ⟨K, A, Cph, KG, hK, hA, hCph, hKG, hph⟩ := ramped_phase_package
  have hCmid : 0 < P.Cmid ^ 2 := by have := P.one_le_Cmid; positivity
  have hs : 0 < (1 / (32 * P.Cmid ^ 2)) ^ (6 / 5 : ℝ) := by positivity
  obtain ⟨r, hr, hrr⟩ := siteRadius_ge_const hs
  obtain ⟨Sc, hSc⟩ : ∃ Sc : ℝ, Sc = 7 * (4 / r + π) * Cs := ⟨_, rfl⟩
  have hSc0 : 0 ≤ Sc := by have := Real.pi_pos; rw [hSc]; positivity
  obtain ⟨ε0, hε0⟩ : ∃ ε0 : ℝ, ε0 = min (min ((1 / 16) / (Cg + 1)) ((r / 4) / (Cs + 1)))
    ((1 / 20) / (Cm * Cg + 2 * CL / r + Sc + 1)) := ⟨_, rfl⟩
  have hε0pos : 0 < ε0 := by
    rw [hε0]; exact lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  filter_upwards [hmarg, hgev, hLev, hph, nCap_ge P, eventually_nAi_le_nCap P,
    eventually_siteRadius_nAi_le (show 0 < r / 4 by positivity),
    hrr, eventually_lam_pow_le (q := 0) (by norm_num) hε0pos,
    eventually_ge_atTop ((20 * Cm + N₀) / (1 / (32 * P.Cmid ^ 2)) ^ (6 / 5 : ℝ)),
    eventually_rpow_neg_le (p := 1 / 10) (by norm_num) (show 0 < (1 / 10) / (Cph + 1) by positivity),
    eventually_gt_atTop (1 : ℝ), eventually_rpow_neg_le (p := 3 / 5) (by norm_num) hr]
    with c' hm hg hL hp hcap hAi hrad hrc hlam hcs hw hc'1 hr3 d hd hd1 n x hn hcell
  have hc'0 : 0 < c' := by linarith
  have hl := lambdaComb_pos' hc'0
  have hlam' : lambdaComb c' ≤ ε0 := by simpa using hlam
  have hn1 : 1 ≤ n := by omega
  have hnr : (1 / (32 * P.Cmid ^ 2)) ^ (6 / 5 : ℝ) * c' ≤ n := by
    have h2 : (nCap P c' : ℝ) ≤ n := by exact_mod_cast (by omega : nCap P c' ≤ n)
    linarith
  have hcs' : 20 * Cm + N₀ ≤ (1 / (32 * P.Cmid ^ 2)) ^ (6 / 5 : ℝ) * c' := by
    have := (div_le_iff₀ hs).1 hcs
    linarith
  have hN₀ : N₀ ≤ n := by
    have : (N₀ : ℝ) ≤ n := by linarith [hCm.le]
    exact_mod_cast this
  have hxr : r ≤ x - xiStar := by
    have h1 := hrc (n : ℝ) hnr
    unfold siteRadius at h1
    linarith [hcell.1]
  have hxs : xiStar < x := by linarith
  have hnAi1 := one_le_nAi hc'1.le
  -- small parameters
  have hlam_a : Cg * lambdaComb c' ≤ 1 / 16 := by
    refine mul_le_of_le_div_succ hCg.le hl.le (by norm_num) ?_
    rw [hε0] at hlam'; exact hlam'.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hlam_b : Cs * lambdaComb c' ≤ r / 4 := by
    refine mul_le_of_le_div_succ hCs.le hl.le (by positivity) ?_
    rw [hε0] at hlam'; exact hlam'.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hlam_c : (Cm * Cg + 2 * CL / r + Sc) * lambdaComb c' ≤ 1 / 20 := by
    refine mul_le_of_le_div_succ (by positivity) hl.le (by norm_num) ?_
    rw [hε0] at hlam'; exact hlam'.trans (min_le_right _ _)
  -- the sites below the Airy cut
  have hnear : ∀ k : ℕ, 1 ≤ k → k ≤ nAi c' →
      designSite c' (rampedSigma d c') k + r / 2 ≤ x ∧ r / 2 ≤ |x - chiQuantile c' (k : ℝ)| := by
    intro k hk hkn
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hkp : (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hk1 (by norm_num)
    have hΔ : |designSite c' (rampedSigma d c') k - chiQuantile c' (k : ℝ)| ≤ r / 4 := by
      refine (hsh c' hc'0 d hd hd1 k hk).trans ?_
      calc Cs * lambdaComb c' * (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ Cs * lambdaComb c' * 1 :=
            mul_le_mul_of_nonneg_left hkp (by positivity)
        _ ≤ r / 4 := by linarith
    have hχ := hrad k hk hkn
    unfold siteRadius at hχ
    exact near_aux hr hΔ hχ hxr
  obtain ⟨hfx, hout⟩ := macro_out P hc'0 hnAi1 hn1 hcell (fun k a b => (hnear k a b).1) hr
  have hS := macro_shiftCost P hc'0 hd hr hCs.le hnAi1 hn1 hcell hxs.le (fun k a b => (hnear k a b).2)
    (fun k hk => hsh c' hc'0 d hd hd1 k hk) hlam_b
  have hHole := macro_holeHyp P hc'0 hd hAi hn
  have hη14 := macro_eta14 P hc'0 hn
  -- e_L and the gap
  have heL : eLeftComb c' 1 n 4 x ≤ CL * lambdaComb c' / r := by
    refine (hL 1 n 4 x le_rfl hxs).2.trans ?_
    exact div_le_div_of_nonneg_left (by positivity) hr hxr
  have heL0 : 0 ≤ CL * lambdaComb c' / r := by positivity
  have hgap : siteGap c' n ≤ Cg * lambdaComb c' := by
    obtain ⟨g1, g2, g3, -⟩ := hg
    exact (g1 n hn1).trans (g2.trans g3)
  have hgap16 : siteGap c' n ≤ 1 / 16 := hgap.trans hlam_a
  -- the amplitude
  have hlev := levComb_pos c' 1 x
  have hw0 : 0 ≤ Cph * c' ^ (-(1 / 10 : ℝ)) := by
    have : 0 ≤ c' ^ (-(1 / 10 : ℝ)) := Real.rpow_nonneg hc'0.le _
    positivity
  have hw10 : Cph * c' ^ (-(1 / 10 : ℝ)) ≤ 1 / 10 :=
    mul_le_of_le_div_succ hCph (Real.rpow_nonneg hc'0.le _) (by norm_num) hw
  obtain ⟨-, -, hamp3, -⟩ := hp P d hd hd1
  have hxξ : xiStar + c' ^ (-(3 / 5 : ℝ)) ≤ x := by linarith
  have hAmp := macro_amp P hc'0 hCph (by omega : 7 ≤ n) hcell (hamp3 x hxξ)
  have hE : Cm * (1 / (n : ℝ) + siteGap c' n) +
      (2 * (CL * lambdaComb c' / r) + Sc * lambdaComb c') ≤ 1 / 10 := by
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn1
    have h1 : Cm * (1 / (n : ℝ)) ≤ 1 / 20 := by
      rw [← div_eq_mul_one_div, div_le_iff₀ hn0]
      have : 20 * Cm ≤ (1 / (32 * P.Cmid ^ 2)) ^ (6 / 5 : ℝ) * c' := by
        have : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg N₀
        linarith
      linarith
    have h2 : Cm * siteGap c' n ≤ Cm * Cg * lambdaComb c' := by
      have := mul_le_mul_of_nonneg_left hgap hCm.le
      linarith
    have h3 : 2 * (CL * lambdaComb c' / r) = 2 * CL / r * lambdaComb c' := by ring
    have h4 : Cm * (1 / (n : ℝ) + siteGap c' n) = Cm * (1 / (n : ℝ)) + Cm * siteGap c' n := by ring
    have h5 : (Cm * Cg + 2 * CL / r + Sc) * lambdaComb c' =
        Cm * Cg * lambdaComb c' + 2 * CL / r * lambdaComb c' + Sc * lambdaComb c' := by ring
    linarith
  have hS' : holeShiftCost c' x (rampedSigma d c') 1 (nCap P c' + 6) n 4 ≤ Sc * lambdaComb c' := by
    rw [hSc]; linarith [hS]
  have hmain := hm 1 (nCap P c' + 6) n x (rampedSigma d c') (rampedEta P c') (CL * lambdaComb c' / r)
    (Sc * lambdaComb c') (Cph * c' ^ (-(1 / 10 : ℝ))) (3 / 4) le_rfl (by omega) hN₀ (by omega) hcell hHole
    hη14 heL0 hw0 hfx hout heL hS' hgap16 (by linarith) le_rfl hxs hAmp
  have hpos : 0 < twoG c' 1 (nCap P c' + 6) (1 / 4) (rampedSigma d c') (fun k => rampedEta P c' k * siteGap c' k) x /
      levComb c' 1 x := by
    have : (0 : ℝ) < 158 / 1000 - 7 / 10 * (Cm * (1 / (n : ℝ) + siteGap c' n) +
        (2 * (CL * lambdaComb c' / r) + Sc * lambdaComb c')) - 542 / 1000 * (Cph * c' ^ (-(1 / 10 : ℝ))) := by
      linarith
    linarith
  exact (div_pos_iff_of_pos_right hlev).1 hpos

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedMacro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedMacro

end FormalResearch.ModularBootstrap.Upper.Ramped
