module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedDesignShiftCore
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedShift
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedHolePairs

/-!
# `RampedHoleHyp` for `D_*` and the discharge of `ShiftSumEstimate` (`rem:thmU` Step (3))

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma `U*` (`rem:thmU`), Step (3) ("Shifts", "The pair at `k₀`", "The other
seven hole pairs").

* `rampedHoleHyp_D`: `RampedHoleHyp c' 1 (n_cap + 6) n σ η (C_κ/n)` for `8 ≤ n ≤ n_cap + 8`, `C_κ` absolute
  (`|Δ_k| ≤ C λ k^{-4/3}`, `ℓ_n ≥ c λ n^{-1/3}`; a displaced pair at `k₀ ∈ {n, n+1}` lies below `N_Ai`, where
  `η² ≤ 1/32`);
* `shiftSumEstimate_of_weights`: the named hypothesis `ShiftSumEstimate` of `RampedShift.lean`, proved for
  `a_k = C_s λ k^{-4/3}` and the distance weights `shiftD` (`D_1 = c'^{-3/5}/2`, `D_k = (λ/L)|Φ_k - [Φ_n, Φ_{n+1}]|`):
  for every `c' ≥ 1`, every cut `N` and `n ≥ 8`;
* `rampedShift_package`: for `D_*`, `x` in the reference cell `n` with `x ≥ ξ_* + c'^{-3/5}`: the first site and the
  sites outside the hole stay off `x`, and the shift cost is `S ≤ C_S(n^{-2/3} + n^{-1}log n) + C_S λ c'^{3/5}`.
  The constants `C_S`, `N₀` and the threshold in `c'` do not depend on `C_I, C_mid, d`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Design FormalResearch.ModularBootstrap.Upper.Window
  Upper.Holes

lemma eventually_lam_pow_le {q ε : ℝ} (hq : q < 2 / 3) (hε : 0 < ε) :
    ∀ᶠ c' : ℝ in atTop, lambdaComb c' * c' ^ q ≤ ε := by
  have hk := kTip_pos
  have hK : 0 < kTip ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hk _
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_rpow_neg_le (p := 2 / 3 - q) (by linarith) (div_pos hε hK)] with c' hc' h
  unfold lambdaComb
  rw [Real.mul_rpow hk.le hc'.le, mul_assoc, ← Real.rpow_add hc']
  have : kTip ^ (-(2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ) + q) ≤ kTip ^ (-(2 / 3 : ℝ)) * (ε / kTip ^ (-(2 / 3 : ℝ))) := by
    refine mul_le_mul_of_nonneg_left ?_ hK.le
    rwa [show (-(2 / 3 : ℝ) + q) = -(2 / 3 - q) by ring]
  rwa [mul_div_cancel₀ _ hK.ne'] at this

/-- The shift cost weights for `D_*`: `a_k = C_s λ k^{-4/3}` (bound on `|Δ_k|`), and the distance weights
`D_1 = c'^{-3/5}/2`, `D_k = (λ/L)·|Φ_k - [Φ_n, Φ_{n+1}]|` outside the hole. -/
noncomputable def shiftA (Cs c' : ℝ) (k : ℕ) : ℝ := Cs * lambdaComb c' * (k : ℝ) ^ (-(4 / 3 : ℝ))

noncomputable def shiftD (L c' : ℝ) (n k : ℕ) : ℝ :=
  if k = 1 then c' ^ (-(3 / 5 : ℝ)) / 2 else if k ∈ holeSet n 4 then 1 else lambdaComb c' / L * eGap n k

/-- **`ShiftSumEstimate` for the ramped shifts** (`rem:thmU` Step (3), "Shifts"): with `a_k = C_s λ k^{-4/3}` and the
distance weights `shiftD`, for every `c' ≥ 1`, every cut `N` and `n ≥ 8`,
`(2/D_1 + π) a_1 + ∑_{k ∉ H} 2(2/D_k + π) a_k ≤ C_S(n^{-2/3} + n^{-1} log n) + C_S λ c'^{3/5}`, with
`C_S = 72 C_s L + (4 + 7π) C_s` (the three-range summation of Lemma `E`). -/
theorem shiftSumEstimate_of_weights {Cs L : ℝ} (hCs : 0 < Cs) (hL : 0 < L) :
    ∃ C_S : ℝ, 0 < C_S ∧ ∀ (c' : ℝ), 1 ≤ c' → ∀ (N n : ℕ), 8 ≤ n →
      ShiftSumEstimate C_S (lambdaComb c' * c' ^ (3 / 5 : ℝ)) 1 N n (shiftA Cs c') (shiftD L c' n) := by
  refine ⟨72 * Cs * L + (4 + 7 * π) * Cs, by positivity, fun c' hc'1 N n hn => ?_⟩
  have hc'0 : 0 < c' := by linarith
  have hl := lambdaComb_pos' hc'0
  have hT : 1 ≤ c' ^ (3 / 5 : ℝ) := Real.one_le_rpow hc'1 (by norm_num)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  unfold ShiftSumEstimate
  have hD1 : shiftD L c' n 1 = c' ^ (-(3 / 5 : ℝ)) / 2 := by simp [shiftD]
  have hA1 : shiftA Cs c' 1 = Cs * lambdaComb c' := by simp [shiftA]
  have hinv : c' ^ (-(3 / 5 : ℝ)) = (c' ^ (3 / 5 : ℝ))⁻¹ := Real.rpow_neg hc'0.le _
  have hfirst : (2 / shiftD L c' n 1 + π) * shiftA Cs c' 1 = (4 * c' ^ (3 / 5 : ℝ) + π) * (Cs * lambdaComb c') := by
    rw [hD1, hA1, hinv]
    have : (c' ^ (3 / 5 : ℝ)) ≠ 0 := by positivity
    field_simp
    ring
  -- the sum
  have hsum_eq : ((Finset.Icc (1 + 1) N).filter (fun k => k ∉ holeSet n 4)) = shiftIdx n N := rfl
  rw [hsum_eq, hfirst]
  have hpt : ∀ k ∈ shiftIdx n N, 2 * ((2 / shiftD L c' n k + π) * shiftA Cs c' k) ≤
      4 * Cs * L * ((k : ℝ) ^ (-(4 / 3 : ℝ)) / eGap n k) + 2 * π * Cs * lambdaComb c' * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
    intro k hk
    have hk' := (mem_shiftIdx hn).1 hk
    have hout : k ∉ holeSet n 4 := by
      have := hk'.2.2
      simp only [Finset.mem_Icc]
      omega
    have hk1 : k ≠ 1 := by omega
    have he := eGap_pos hk'.1 hk'.2.2
    have hD : shiftD L c' n k = lambdaComb c' / L * eGap n k := by simp [shiftD, hk1, hout]
    have hkr : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hp : 0 < (k : ℝ) ^ (-(4 / 3 : ℝ)) := Real.rpow_pos_of_pos hkr _
    rw [hD]
    unfold shiftA
    refine le_of_eq ?_
    field_simp
    ring
  refine le_trans (add_le_add le_rfl (Finset.sum_le_sum hpt)) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hcore := shift_core_sum hn N
  have hsk : ∑ k ∈ shiftIdx n N, (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 3 := by
    have := sum_Ioc_rpow_neg_gt_one (p := 4 / 3) (by norm_num) (a := 1) le_rfl N
    simp only [Nat.cast_one, Real.one_rpow] at this
    refine le_trans ?_ (this.trans (by norm_num))
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun k _ _ => by positivity)
    have := (mem_shiftIdx hn).1 hk
    exact Finset.mem_Ioc.mpr ⟨by omega, this.2.1⟩
  have hq1 : 0 ≤ (n : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
  have hq2 : 0 ≤ Real.log n / n := div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))) hn0.le
  have hq3 : 0 ≤ lambdaComb c' * c' ^ (3 / 5 : ℝ) := by positivity
  have hpi := Real.pi_pos
  have hCL : 0 ≤ Cs * L := by positivity
  have hs1 : 4 * Cs * L * ∑ k ∈ shiftIdx n N, (k : ℝ) ^ (-(4 / 3 : ℝ)) / eGap n k ≤
      4 * Cs * L * (18 * (n : ℝ) ^ (-(2 / 3 : ℝ)) + 6 * (Real.log n / n)) :=
    mul_le_mul_of_nonneg_left (by simpa using hcore) (by positivity)
  have hs2 : 2 * π * Cs * lambdaComb c' * ∑ k ∈ shiftIdx n N, (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤
      2 * π * Cs * lambdaComb c' * 3 :=
    mul_le_mul_of_nonneg_left hsk (by positivity)
  have hlT : lambdaComb c' ≤ lambdaComb c' * c' ^ (3 / 5 : ℝ) := by nlinarith
  have hA : 0 ≤ Cs * lambdaComb c' := by positivity
  have hK0 : 0 ≤ (4 + 7 * π) * Cs := by positivity
  have hpC : 0 ≤ π * Cs := by positivity
  nlinarith [mul_nonneg hK0 hq1, mul_nonneg hK0 hq2, mul_nonneg hq3 hCL, mul_nonneg hCL hq2,
    mul_le_mul_of_nonneg_left hlT hpC]


lemma rampedEta_pos (P : RampedParams) {c' : ℝ} (hc' : 0 < c') {k : ℕ} (hk : 1 ≤ k) :
    0 < rampedEta P c' k := by
  unfold rampedEta
  apply Real.sqrt_pos.2
  refine lt_min (by norm_num) ?_
  unfold etaArg
  have hnT := nTr_nonneg hc'
  have hs : 0 < √c' := Real.sqrt_pos.2 hc'
  have h1 : 0 ≤ P.CI ^ 2 * min (k : ℝ) (nTr c') / √c' := by
    have : 0 ≤ min (k : ℝ) (nTr c') := le_min (by positivity) hnT
    positivity
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have h2 : 0 < P.Cmid ^ 2 * ((k : ℝ) / c') ^ (5 / 6 : ℝ) := by
    have := P.one_le_Cmid
    positivity
  linarith

/-- **`RampedHoleHyp` for `D_*`** (`rem:thmU` Step (3)): on the near-tip range `8 ≤ n ≤ n_cap + 8` the hole shifts
are at most `κ ℓ_n` with `κ = C_κ/n` (`C_κ = 3 C_s/c_g` absolute), the heights are monotone in `[0, 1/4]`, and a
displaced pair at `k₀ ∈ {n, n+1}` has `η² ≤ 1/32`. -/
theorem rampedHoleHyp_D : ∃ Cκ : ℝ, 0 < Cκ ∧ ∀ P : RampedParams, ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ 1 →
    ∀ n : ℕ, 8 ≤ n → n ≤ nCap P c' + 8 →
      RampedHoleHyp c' 1 (nCap P c' + 6) n (rampedSigma d c') (rampedEta P c') (Cκ / n) := by
  obtain ⟨cg, Cg, c0g, hcg, hCg, hc0g, hgap⟩ := rampedGap_two_sided
  obtain ⟨Cs, hCs, hsh⟩ := rampedShift_le
  refine ⟨3 * Cs / cg, by positivity, fun P => ?_⟩
  filter_upwards [eventually_ge_atTop (max c0g 10000), etaSq_le_of_le_nAi P] with c' hc' hη32 d hd hd1 n hn hnc
  have hc'0 : 0 < c' := lt_of_lt_of_le (by positivity) hc'
  have hcg' : c0g ≤ c' := (le_max_left _ _).trans hc'
  have hl := lambdaComb_pos' hc'0
  have hnr : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  refine ⟨fun k _ _ => ⟨rampedEta_nonneg P c' k, rampedEta_le P c' k⟩,
    fun k _ _ => rampedEta_mono P hc'0 (Nat.le_succ k),
    fun k hk _ => (rampedSigma_nonneg hc'0 hd hk), ?_, ?_⟩
  · intro k hk1 hkN hkH
    have hkH' := Finset.mem_Icc.mp hkH
    have hk2 : n ≤ 2 * k := by omega
    have hkr : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have h1 := hsh c' hc'0 d hd hd1 k (by omega)
    have h2 : (n : ℝ) / 2 ≤ k := by
      have : (n : ℝ) ≤ 2 * k := by exact_mod_cast hk2
      linarith
    have h3 : (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 3 * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
      have h3 : (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ ((n : ℝ) / 2) ^ (-(4 / 3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by norm_num)
      have h4 : ((n : ℝ) / 2) ^ (-(4 / 3 : ℝ)) = 2 ^ (4 / 3 : ℝ) * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
        rw [Real.div_rpow hn0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul,
          mul_comm]
      have h5 : (2 : ℝ) ^ (4 / 3 : ℝ) ≤ 3 := by
        by_contra hcon
        push Not at hcon
        have h6 : (3 : ℝ) ^ 3 < ((2 : ℝ) ^ (4 / 3 : ℝ)) ^ 3 := pow_lt_pow_left₀ hcon (by norm_num) (by norm_num)
        have h7 : ((2 : ℝ) ^ (4 / 3 : ℝ)) ^ 3 = 2 ^ 4 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
        norm_num [h7] at h6
      have hnn : 0 ≤ (n : ℝ) ^ (-(4 / 3 : ℝ)) := by positivity
      nlinarith
    obtain ⟨hgl, -⟩ := hgap P c' hcg' n (by omega) hnc
    have hp : 0 < (n : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hn0 _
    have h43 : (n : ℝ) ^ (-(4 / 3 : ℝ)) = (n : ℝ) ^ (-(1 / 3 : ℝ)) * (n : ℝ)⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hn0]; norm_num
    refine h1.trans ?_
    calc Cs * lambdaComb c' * (k : ℝ) ^ (-(4 / 3 : ℝ))
        ≤ Cs * lambdaComb c' * (3 * (n : ℝ) ^ (-(4 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 3 * Cs / cg / n * (cg * lambdaComb c' * (n : ℝ) ^ (-(1 / 3 : ℝ))) := by
          rw [h43]; field_simp
      _ ≤ 3 * Cs / cg / n * siteGap c' n := by gcongr
  · intro k hk1 hkN hk
    by_cases hAi : nAi c' < k
    · exact Or.inl (designSite_ramped_eq_of_gt hc'0 d hAi (by omega))
    · right
      have hle : k ≤ nAi c' := not_lt.1 hAi
      rw [rampedEta_sq P hc'0 k]
      exact hη32 k hle


/-- Indices up to `n_cap + 8` lie in the tip window `χ_k - ξ_* ≤ 0.63`. -/
lemma radius_le_of_le_nCap (P : RampedParams) {c' : ℝ} (hc' : 10000 ≤ c') {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ nCap P c' + 8) : siteRadius c' (k : ℝ) ≤ 63 / 100 := by
  have hcap := nCap_le P hc'
  have : (k : ℝ) ≤ c' / 20 := by
    have : (k : ℝ) ≤ nCap P c' + 8 := by exact_mod_cast hkn
    linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact siteRadius_le_window (by linarith) (by linarith) this

/-- **The shift cost of `D_*`** (`rem:thmU` Step (3), "Shifts"; this discharges `ShiftSumEstimate`).  There are an
absolute `C_S` and `N₀` such that for `c'` large (threshold absolute), all `C_I, C_mid ≥ 1`, `d ∈ [0, 1]`, every
`N₀ ≤ n ≤ n_cap + 6` and every `x` in the reference cell `n` with `x ≥ ξ_* + c'^{-3/5}` (Region II):
the first site and every site outside the hole `{n-3, …, n+4}` stay off `x`, and
`S ≤ C_S(n^{-2/3} + n^{-1} log n) + C_S λ c'^{3/5}`. -/
theorem rampedShift_package : ∃ C_S : ℝ, 0 < C_S ∧ ∃ N0 : ℕ, 8 ≤ N0 ∧ ∀ᶠ c' : ℝ in atTop,
    ∀ (P : RampedParams) (d : ℝ), 0 ≤ d → d ≤ 1 → ∀ (n : ℕ) (x : ℝ), N0 ≤ n → n ≤ nCap P c' + 6 →
      inCell c' n x → xiStar + c' ^ (-(3 / 5 : ℝ)) ≤ x →
      designSite c' (rampedSigma d c') 1 < x ∧
      (∀ k, 1 < k → k ≤ nCap P c' + 6 → k ∉ holeSet n 4 → designSite c' (rampedSigma d c') k ≠ x) ∧
      holeShiftCost c' x (rampedSigma d c') 1 (nCap P c' + 6) n 4 ≤
        C_S * ((n : ℝ) ^ (-(2 / 3 : ℝ)) + Real.log n / n) + C_S * (lambdaComb c' * c' ^ (3 / 5 : ℝ)) := by
  obtain ⟨Cs, hCs, hsh⟩ := rampedShift_le
  obtain ⟨L0, hL0⟩ := langerTau_deriv_bound_compact (a := xiStar / 2) (b := xiStar + 1)
    (by have := xiStar_pos; linarith)
  set L := max L0 1 with hLdef
  have hL : 0 < L := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hLb : ∀ z ∈ Icc (xiStar / 2) (xiStar + 1), |deriv langerTau z| ≤ L :=
    fun z hz => (hL0 z hz).1.trans (le_max_left _ _)
  obtain ⟨C_S, hCS, hS⟩ := shiftSumEstimate_of_weights hCs hL
  obtain ⟨cg, Cg, c0g, hcg, hCg, hc0g, hgap⟩ := rampedGap_two_sided
  obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, ∀ n : ℕ, N1 ≤ n → 6 * Cs * L ≤ (n : ℝ) ^ (2 / 3 : ℝ) := by
    have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp tendsto_natCast_atTop_atTop
    obtain ⟨N1, hN1⟩ := eventually_atTop.1 (h.eventually_ge_atTop (6 * Cs * L))
    exact ⟨N1, fun n hn => hN1 n hn⟩
  refine ⟨C_S, hCS, max 8 N1, le_max_left _ _, ?_⟩
  filter_upwards [eventually_ge_atTop (max (max c0g 10000) 1),
    eventually_lam_pow_le (q := 3 / 5) (by norm_num) (show 0 < min (1 / 2) (1 / (4 * Cs)) by positivity)]
    with c' hc' hlam P d hd hd1 n x hn hnc hx hxξ
  have hc'1 : 1 ≤ c' := (le_max_right _ _).trans hc'
  have hc'4 : 10000 ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans hc')
  have hcg' : c0g ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hc')
  have hc'0 : 0 < c' := by linarith
  have hl := lambdaComb_pos' hc'0
  have hn8 : 8 ≤ n := (le_max_left _ _).trans hn
  have hn1 : N1 ≤ n := (le_max_right _ _).trans hn
  have hT : 1 ≤ c' ^ (3 / 5 : ℝ) := Real.one_le_rpow hc'1 (by norm_num)
  have hT0 : 0 < c' ^ (3 / 5 : ℝ) := by positivity
  have hlam1 : lambdaComb c' * c' ^ (3 / 5 : ℝ) ≤ 1 / 2 := hlam.trans (min_le_left _ _)
  have hlam2 : lambdaComb c' * c' ^ (3 / 5 : ℝ) ≤ 1 / (4 * Cs) := hlam.trans (min_le_right _ _)
  have hinv : c' ^ (-(3 / 5 : ℝ)) = (c' ^ (3 / 5 : ℝ))⁻¹ := Real.rpow_neg hc'0.le _
  have hnr : (8 : ℝ) ≤ n := by exact_mod_cast hn8
  have hn0 : (0 : ℝ) < n := by linarith
  -- the first site
  have hD1 : shiftD L c' n 1 = c' ^ (-(3 / 5 : ℝ)) / 2 := by simp [shiftD]
  have hD1pos : 0 < shiftD L c' n 1 := by rw [hD1]; positivity
  have h2a1 : 2 * shiftA Cs c' 1 ≤ shiftD L c' n 1 := by
    rw [hD1, hinv]
    unfold shiftA
    simp only [Nat.cast_one, Real.one_rpow, mul_one]
    have h4 : lambdaComb c' * c' ^ (3 / 5 : ℝ) * (4 * Cs) ≤ 1 := (le_div_iff₀ (by positivity)).1 hlam2
    calc 2 * (Cs * lambdaComb c') = (4 * Cs * (lambdaComb c' * c' ^ (3 / 5 : ℝ))) / (2 * c' ^ (3 / 5 : ℝ)) := by
          field_simp; ring
      _ ≤ 1 / (2 * c' ^ (3 / 5 : ℝ)) := div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = (c' ^ (3 / 5 : ℝ))⁻¹ / 2 := by field_simp
  -- window facts
  have hrad : ∀ k : ℕ, 1 ≤ k → k ≤ nCap P c' + 8 → chiQuantile c' (k : ℝ) ≤ xiStar + 1 := by
    intro k hk hkn
    have := radius_le_of_le_nCap P hc'4 hk hkn
    unfold siteRadius at this
    linarith
  have hchi1 : chiQuantile c' ((1 : ℕ) : ℝ) - xiStar ≤ c' ^ (-(3 / 5 : ℝ)) / 2 := by
    have h1 := (siteRadius_bounds hc'0 (by norm_num : (1 / 4 : ℝ) ≤ ((1 : ℕ) : ℝ))).2
    have h2 : lambdaComb c' * phiQuantile ((1 : ℕ) : ℝ) ≤ lambdaComb c' := by
      have : phiQuantile ((1 : ℕ) : ℝ) ≤ 1 := by
        unfold phiQuantile
        exact Real.rpow_le_one (by norm_num) (by norm_num) (by norm_num)
      nlinarith
    have h3 : lambdaComb c' ≤ c' ^ (-(3 / 5 : ℝ)) / 2 := by
      rw [hinv]
      calc lambdaComb c' = (lambdaComb c' * c' ^ (3 / 5 : ℝ)) / c' ^ (3 / 5 : ℝ) := by field_simp
        _ ≤ (1 / 2) / c' ^ (3 / 5 : ℝ) := div_le_div_of_nonneg_right hlam1 hT0.le
        _ = (c' ^ (3 / 5 : ℝ))⁻¹ / 2 := by field_simp
    exact le_trans h1 (h2.trans h3)
  have hx1 : shiftD L c' n 1 ≤ |x - chiQuantile c' ((1 : ℕ) : ℝ)| := by
    rw [hD1]
    have : c' ^ (-(3 / 5 : ℝ)) / 2 ≤ x - chiQuantile c' ((1 : ℕ) : ℝ) := by linarith
    exact this.trans (le_abs_self _)
  -- outside the hole
  have hdist : ∀ k : ℕ, 2 ≤ k → k ≤ nCap P c' + 6 → (k + 4 ≤ n ∨ n + 5 ≤ k) →
      shiftD L c' n k ≤ |x - chiQuantile c' (k : ℝ)| := by
    intro k hk2 hkN hk
    have hk1 : k ≠ 1 := by omega
    have hout : k ∉ holeSet n 4 := by
      simp only [Finset.mem_Icc]; omega
    have hD : shiftD L c' n k = lambdaComb c' / L * eGap n k := by simp [shiftD, hk1, hout]
    rw [hD]
    rcases hk with hk | hk
    · have hkn : k < n := by omega
      have hxk : chiQuantile c' (k : ℝ) ≤ chiQuantile c' (n : ℝ) :=
        chiQuantile_mono_le hc'0 (by have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
                                     linarith) (by exact_mod_cast hkn.le)
      have h := lam_phi_sub_le hLb hc'0 (a := (k : ℝ)) (b := (n : ℝ))
        (by have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
            linarith) (by exact_mod_cast hkn.le) (hrad n (by omega) (by omega))
      have hcell := hx.1
      have heq : eGap n k = phiQuantile (n : ℝ) - phiQuantile (k : ℝ) := by
        simp only [eGap, hkn, ↓reduceIte]; rfl
      rw [heq, abs_of_nonneg (by linarith)]
      rw [div_mul_eq_mul_div, div_le_iff₀ hL]
      nlinarith
    · have hkn : n + 1 ≤ k := by omega
      have hxk : chiQuantile c' ((n + 1 : ℕ) : ℝ) ≤ chiQuantile c' (k : ℝ) :=
        chiQuantile_mono_le hc'0 (by have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
                                      exact_mod_cast (by omega : 1 ≤ n + 1)
                                     linarith) (by exact_mod_cast hkn)
      have h := lam_phi_sub_le hLb hc'0 (a := ((n + 1 : ℕ) : ℝ)) (b := (k : ℝ))
        (by have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
            linarith) (by exact_mod_cast hkn) (hrad k (by omega) (by omega))
      have hcell := hx.2
      have heq : eGap n k = phiQuantile (k : ℝ) - phiQuantile ((n + 1 : ℕ) : ℝ) := by
        simp only [eGap, show ¬ k < n by omega, ↓reduceIte]; rfl
      rw [heq, abs_of_nonpos (by linarith)]
      rw [div_mul_eq_mul_div, div_le_iff₀ hL]
      nlinarith
  have h2a : ∀ k : ℕ, 2 ≤ k → (k + 4 ≤ n ∨ n + 5 ≤ k) → 2 * shiftA Cs c' k ≤ shiftD L c' n k := by
    intro k hk2 hk
    have hk1 : k ≠ 1 := by omega
    have hout : k ∉ holeSet n 4 := by
      simp only [Finset.mem_Icc]; omega
    have hD : shiftD L c' n k = lambdaComb c' / L * eGap n k := by simp [shiftD, hk1, hout]
    have he := eGap_pos hk2 hk
    have hr := ratio_le_three hn8 hk2 hk
    have hkr : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hp : 0 < (k : ℝ) ^ (-(4 / 3 : ℝ)) := Real.rpow_pos_of_pos hkr _
    rw [div_le_iff₀ he] at hr
    have hq : 0 < (n : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
    have hqq : (n : ℝ) ^ (-(2 / 3 : ℝ)) * (6 * Cs * L) ≤ 1 := by
      have h := hN1 n hn1
      have e2 : (n : ℝ) ^ (-(2 / 3 : ℝ)) = ((n : ℝ) ^ (2 / 3 : ℝ))⁻¹ := Real.rpow_neg hn0.le _
      rw [e2, ← div_eq_inv_mul, div_le_one (by positivity)]
      exact h
    unfold shiftA
    rw [hD]
    have : 2 * (Cs * lambdaComb c' * (k : ℝ) ^ (-(4 / 3 : ℝ))) ≤
        2 * (Cs * lambdaComb c' * (3 * (n : ℝ) ^ (-(2 / 3 : ℝ)) * eGap n k)) := by gcongr
    refine this.trans ?_
    have h5 : 0 < lambdaComb c' * eGap n k := mul_pos hl he
    calc 2 * (Cs * lambdaComb c' * (3 * (n : ℝ) ^ (-(2 / 3 : ℝ)) * eGap n k))
        = (n : ℝ) ^ (-(2 / 3 : ℝ)) * (6 * Cs * L) * (lambdaComb c' / L * eGap n k) := by
          field_simp
          norm_num
      _ ≤ 1 * (lambdaComb c' / L * eGap n k) := by
          gcongr
      _ = _ := one_mul _
  have hoh : ∀ k : ℕ, 2 ≤ k → k ∉ holeSet n 4 → (k + 4 ≤ n ∨ n + 5 ≤ k) := by
    intro k hk2 hk
    simp only [Finset.mem_Icc] at hk
    omega
  have hDpos : ∀ k : ℕ, 1 ≤ k → shiftD L c' n k > 0 := by
    intro k hk
    by_cases hk1 : k = 1
    · subst hk1; exact hD1pos
    · by_cases hH : k ∈ holeSet n 4
      · simp [shiftD, hk1, hH]
      · have he := eGap_pos (n := n) (k := k) (by omega) (hoh k (by omega) hH)
        simp only [shiftD, hk1, hH, ite_false]
        positivity
  have ha : ∀ k : ℕ, 1 ≤ k → |designSite c' (rampedSigma d c') k - chiQuantile c' (k : ℝ)| ≤ shiftA Cs c' k :=
    fun k hk => hsh c' hc'0 d hd hd1 k hk
  have h2a' : ∀ k : ℕ, 1 ≤ k → (k = 1 ∨ k ∉ holeSet n 4) → 2 * shiftA Cs c' k ≤ shiftD L c' n k := by
    intro k hk hH
    by_cases hk1 : k = 1
    · subst hk1; exact h2a1
    · exact h2a k (by omega) (hoh k (by omega) (hH.resolve_left hk1))
  have hdist' : ∀ k : ℕ, 1 ≤ k → k ≤ nCap P c' + 6 → (k = 1 ∨ k ∉ holeSet n 4) →
      shiftD L c' n k ≤ |x - chiQuantile c' (k : ℝ)| := by
    intro k hk hkN hH
    by_cases hk1 : k = 1
    · subst hk1; exact hx1
    · exact hdist k (by omega) hkN (hoh k (by omega) (hH.resolve_left hk1))
  have hxs : xiStar ≤ x := by
    have : 0 < c' ^ (-(3 / 5 : ℝ)) := by positivity
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have h1 := ha 1 le_rfl
    have h2 := h2a' 1 le_rfl (Or.inl rfl)
    have h3 := hx1
    have h4 := hDpos 1 le_rfl
    rw [abs_le] at h1
    have h5 : chiQuantile c' ((1 : ℕ) : ℝ) ≤ x := by
      have := hD1pos
      have h6 := hchi1
      have hT' : 0 < c' ^ (-(3 / 5 : ℝ)) := by positivity
      calc chiQuantile c' ((1 : ℕ) : ℝ) ≤ xiStar + c' ^ (-(3 / 5 : ℝ)) / 2 := by linarith [h6]
        _ ≤ xiStar + c' ^ (-(3 / 5 : ℝ)) := by linarith
        _ ≤ x := hxξ
    rw [abs_of_nonneg (by linarith)] at h3
    linarith [h1.1, h1.2]
  · intro k hk1 hkN hH hEq
    have h1 := ha k (by omega)
    have h2 := h2a' k (by omega) (Or.inr hH)
    have h3 := hdist' k (by omega) hkN (Or.inr hH)
    have h4 := hDpos k (by omega)
    rw [hEq] at h1
    linarith
  · refine holeShiftCost_le_estimate hxs (rampedSigma d c') (show 1 ≤ nCap P c' + 6 by omega) n
      (shiftA Cs c') (shiftD L c' n) (fun k hk _ => hDpos k hk)
      (fun k hk _ => ⟨xiStar_pos.le.trans (designSite_ramped_nonneg hc'0 hd hk),
        xiStar_pos.le.trans (xiStar_le_chiQuantile_nat hc'0 hk)⟩)
      (fun k hk _ _ => ha k hk) (fun k hk _ hH => h2a' k hk hH) (fun k hk hkN hH => hdist' k hk hkN hH)
      (hS c' hc'1 (nCap P c' + 6) n hn8)



/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.shiftSumEstimate_of_weights' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shiftSumEstimate_of_weights

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedHoleHyp_D' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedHoleHyp_D

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedShift_package' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedShift_package

end FormalResearch.ModularBootstrap.Upper.Ramped
