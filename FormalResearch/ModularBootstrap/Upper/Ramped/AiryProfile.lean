module

public import FormalResearch.ModularBootstrap.Upper.Ramped.ProfileV

/-!
# Lemma `P_unif`: the profile-uniform Airy product, `R_1`, Lemma V and Lemma E

Formalises Lemma `P_unif` (`rem:profile`, `CFT/notes/n2_ramped_comb.tex`) together with the profile
versions of Lemma V (`ut:V`) and Lemma E (`ut:E`) of `upper_transfer.tex`.  An *admissible profile*
is a pair of sequences `(u_k, ε_k)` with `|u_k - a_k| ≤ C₀ k^{-4/3}` and `0 ≤ ε_k ≤ C₀ k^{-1/3}`
(`ProfHyp`).  The *ramped profile* is `u_k = a_k` for `2 ≤ k ≤ N`, `u_k = u_k^W` beyond
(`designSiteU N`) and `ε_k = η_k gap^W_k = κ η_k (Φ_{k+1} - Φ_k)` with arbitrary heights
`0 ≤ η_k ≤ 1/4` (`rampedWidthU η`, `AdmHeights η`).

* `profPi0_le_unif`: `Π_n(0) ≤ C_P ((a_n - u_n)² + ε_n²) n^{-2/3}` for every admissible profile
  (the off-diagonal product is bounded by `prof_prod_except_le`).
* `profR1_bounds_unif`: `1/2 ≤ R_1 ≤ C` for `N ≥ N₀` and `u_k = a_k` on `2 ≤ k ≤ N`.
* `rampedProfile_profHyp`: the ramped profile is admissible, with `C₀` independent of `N`, `η`.
* `pUnif_Pi0_le`, `pUnif_E0_tsum`, `pUnif_E0`: `Π_n(0) ≤ C (η_n² n^{-4/3} + 1_{n>N} n^{-10/3})` and
  `E_0 ≤ C (∑_{n=2}^N η_n² n^{-4/3} + ∑_{n>N} (η_n² n^{-4/3} + n^{-10/3}))`  (P-unif).

The growth bound itself is `pUnif_bound` (`Ramped/ProfileBound.lean`), the profile Lemma V is
`profV_identity` (`Ramped/ProfileV.lean`), and the packaged statement `lemma_P_unif` with
`pUnif_V_ramped` is in `Ramped/PUnif.lean`.  Consumers: the Region-I estimate uses
`‖W(u)‖ ≤ C (1 + |u|)^{-3/2} e(u)`; the vacuum step uses `R_1 ≥ 1/2` and `∫ W ≤ -d R_1 + E_0` with
`E_0 = O(c'^{-1/3})`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window

/-- `|a_n - a_1| ≥ (9/10) n^{2/3}` for `n ≥ 2`. -/
lemma airyZero_sub_one_ge :
    ∀ n : ℕ, 2 ≤ n → (9 / 10 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) ≤ |airyZero n - airyZero 1| := by
  intro n hn
  have hsep := airyZero_abs_sub_ge le_rfl (by omega : 1 ≤ n) (by omega : 1 ≠ n)
  rw [max_eq_left (by omega : 1 ≤ n)] at hsep
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdiff : (n : ℝ) / 2 ≤ |(n : ℝ) - 1| := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    rw [abs_of_nonneg (by linarith)]; linarith
  have hn_pow : (n : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) = (n : ℝ) ^ (2 / 3 : ℝ) := by
    conv_lhs => arg 1; rw [← Real.rpow_one (n : ℝ)]
    rw [← Real.rpow_add hn_pos]; norm_num
  have h1' : (9 / 10 : ℝ) * (n : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤
      (9 / 5 : ℝ) * |(n : ℝ) - 1| * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    have : 0 < (n : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
    nlinarith
  rw [mul_assoc, hn_pow] at h1'
  linarith

lemma ProfHyp.sq_le {C0 : ℝ} {uSite epsU : ℕ → ℝ} (hP : ProfHyp C0 uSite epsU) {k : ℕ} (hk : 2 ≤ k) :
    (epsU k) ^ 2 ≤ C0 ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨_, h0, h1⟩ := hP k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  calc (epsU k) ^ 2 ≤ (C0 * (k : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = C0 ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
        rw [mul_pow, ← Real.rpow_natCast ((k : ℝ) ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hk0.le,
          show -(1 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(2 / 3 : ℝ) by norm_num]

lemma ProfHyp.site_le {C0 : ℝ} {uSite epsU : ℕ → ℝ} (hP : ProfHyp C0 uSite epsU) {k : ℕ} (hk : 2 ≤ k) :
    |airyZero k - uSite k| ≤ C0 * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
  rw [abs_sub_comm]; exact (hP k hk).1

/-- **Lemma E (i)/(ii) for profiles**: `Π_n(0) ≤ C_P ((a_n - u_n)² + ε_n²) n^{-2/3}` uniformly over the
admissible profiles `ProfHyp C₀`. -/
theorem profPi0_le_unif {C0 : ℝ} (hC0 : 0 < C0) :
    ∃ C > 0, ∀ uSite epsU : ℕ → ℝ, ProfHyp C0 uSite epsU → ∀ n : ℕ, 2 ≤ n →
      profPi0 uSite epsU n ≤
        C * ((airyZero n - uSite n) ^ 2 + (epsU n) ^ 2) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨C_prod, hC_prod, hprod_bd⟩ := prof_prod_except_le C0 C0 hC0
  refine ⟨C_prod / (9 / 10 : ℝ), by positivity, fun uSite epsU hP n hn => ?_⟩
  have hH := ProfHyp.tailHyp (f := 1) le_rfl hC0 hP
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hprod := hprod_bd uSite epsU hH (fun k hk => hP.site_le hk) (fun k hk => hP.sq_le hk) n hn
  have hprod_nn : 0 ≤ ∏' m : ℕ, (if m + 2 = n then 1 else profRealFactor uSite epsU n (m + 2)) := by
    have hp := (profPi0_hasProd uSite epsU hH hn).1
    refine ge_of_tendsto hp (Eventually.of_forall fun s =>
      Finset.prod_nonneg fun m _ => by split_ifs; exact zero_le_one; unfold profRealFactor; positivity)
  have hsep := airyZero_sub_one_ge n hn
  have hsep_pos : 0 < (9 / 10 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) := by positivity
  have hrp : (n : ℝ) ^ (-(2 / 3 : ℝ)) = ((n : ℝ) ^ (2 / 3 : ℝ))⁻¹ := Real.rpow_neg hn_pos.le _
  unfold profPi0
  calc ((airyZero n - uSite n) ^ 2 + (epsU n) ^ 2) / |airyZero n - airyZero 1| *
        ∏' m : ℕ, (if m + 2 = n then 1 else profRealFactor uSite epsU n (m + 2))
      ≤ ((airyZero n - uSite n) ^ 2 + (epsU n) ^ 2) / ((9 / 10 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ)) * C_prod := by
        gcongr
    _ = C_prod / (9 / 10 : ℝ) * ((airyZero n - uSite n) ^ 2 + (epsU n) ^ 2) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
        rw [hrp]; field_simp

/-- **Lemma E (iv) for profiles**: `R_1` is bounded above and below uniformly.  If `u_k = a_k` for
`2 ≤ k ≤ N` and `N ≥ N₀(C₀)`, then `1/2 ≤ R_1 ≤ C`. -/
theorem profR1_bounds_unif {C0 : ℝ} (hC0 : 0 < C0) :
    ∃ C : ℝ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ uSite epsU : ℕ → ℝ, ProfHyp C0 uSite epsU →
      (∀ k : ℕ, 2 ≤ k → k ≤ N → uSite k = airyZero k) →
      1 / 2 ≤ profR1 uSite epsU ∧ profR1 uSite epsU ≤ C := by
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (4 * (C0 / (9 / 10 : ℝ)) / Real.log 2)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (√(2 * (C0 / (9 / 10 : ℝ))))
  refine ⟨Real.exp ((2 * (C0 / (9 / 10 : ℝ)) + (C0 ^ 2 + C0 ^ 2) / (9 / 10 : ℝ) ^ 2) *
      ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2), max 1 (max N₁ N₂), fun N hN uSite epsU hP hex => ?_⟩
  have hN_1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hN1_le : N₁ ≤ N := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hN
  have hN2_le : N₂ ≤ N := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hN
  exact prof_R1_bounds C0 C0 hC0 N₁ N₂ hN₁ hN₂ uSite epsU (ProfHyp.tailHyp (f := 1) le_rfl hC0 hP)
    N hN_1 hN1_le hN2_le hex (fun k hk => hP.site_le hk) (fun k hk => hP.sq_le hk) airyZero_sub_one_ge

/-- The constant `C_gap` in `gap^W_k ≤ C_gap k^{-1/3}` (`gapWKB_le_mul_rpow`). -/
noncomputable def gapConst : ℝ := (2 / 3 : ℝ) * kappaAiry * (4 / 3 : ℝ) ^ (1 / 3 : ℝ)

lemma gapConst_pos : 0 < gapConst := by
  unfold gapConst; have := kappaAiry_pos; positivity

/-- The ramped width `ε_k = η_k gap^W_k = κ η_k (Φ_{k+1} - Φ_k)`. -/
noncomputable def rampedWidthU (η : ℕ → ℝ) (k : ℕ) : ℝ := η k * gapWKB k

/-- Admissible height profile: `0 ≤ η_k ≤ 1/4` for `k ≥ 2`. -/
def AdmHeights (η : ℕ → ℝ) : Prop := ∀ k : ℕ, 2 ≤ k → 0 ≤ η k ∧ η k ≤ 1 / 4

/-- The ramped profile is admissible, with a constant independent of `N` and of the heights. -/
theorem rampedProfile_profHyp :
    ∃ C0 > 0, ∀ (N : ℕ) (η : ℕ → ℝ), AdmHeights η →
      ProfHyp C0 (designSiteU N) (rampedWidthU η) := by
  obtain ⟨C_Z, hC_Z, hδ⟩ := deltaWKB_le_exists
  have hg := gapConst_pos
  refine ⟨max C_Z (gapConst / 4), lt_max_of_lt_left hC_Z, fun N η hη k hk => ?_⟩
  have hk1 : 1 ≤ k := by omega
  have hk43 : 0 ≤ (k : ℝ) ^ (-(4 / 3 : ℝ)) := by positivity
  have hk13 : 0 ≤ (k : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold designSiteU
    split_ifs
    · rw [sub_self, abs_zero]; positivity
    · have h1 := hδ k hk1
      unfold deltaWKB at h1
      rw [abs_sub_comm]
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hk43)
  · exact mul_nonneg (hη k hk).1 (gapWKB_pos hk1).le
  · unfold rampedWidthU
    have hgap := gapWKB_le_mul_rpow hk1
    calc η k * gapWKB k ≤ (1 / 4 : ℝ) * (gapConst * (k : ℝ) ^ (-(1 / 3 : ℝ))) :=
          mul_le_mul (hη k hk).2 hgap (gapWKB_pos hk1).le (by norm_num)
      _ = (gapConst / 4) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by ring
      _ ≤ max C_Z (gapConst / 4) * (k : ℝ) ^ (-(1 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hk13

/-- The profile-uniform bound on the zero-shift weights: for the ramped profile, with `η` arbitrary in
`[0, 1/4]`, `Π_n(0) ≤ C (η_n² n^{-4/3} + 1_{n > N} n^{-10/3})` (`P-unif`, proof of `rem:profile`: the
diagonal factor `((a_n - u_n)² + ε_n²)/|a_n - a_1|` times the bounded off-diagonal product). -/
theorem pUnif_Pi0_le :
    ∃ C > 0, ∀ (N : ℕ) (η : ℕ → ℝ), AdmHeights η → ∀ n : ℕ, 2 ≤ n →
      profPi0 (designSiteU N) (rampedWidthU η) n ≤
        C * (η n ^ 2 * (n : ℝ) ^ (-(4 / 3 : ℝ)) + (if N < n then (n : ℝ) ^ (-(10 / 3 : ℝ)) else 0)) := by
  obtain ⟨C0, hC0, hprof⟩ := rampedProfile_profHyp
  obtain ⟨CP, hCP, hbd⟩ := profPi0_le_unif hC0
  have hg := gapConst_pos
  refine ⟨CP * max (gapConst ^ 2) (C0 ^ 2), by positivity, fun N η hη n hn => ?_⟩
  have hP := hprof N η hη
  have hn1 : 1 ≤ n := by omega
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmain := hbd (designSiteU N) (rampedWidthU η) hP n hn
  have hgap_sq : (rampedWidthU η n) ^ 2 ≤ η n ^ 2 * gapConst ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
    unfold rampedWidthU
    rw [mul_pow]
    have hsq := pow_le_pow_left₀ (gapWKB_pos hn1).le (gapWKB_le_mul_rpow hn1) 2
    change gapWKB n ^ 2 ≤ (gapConst * (n : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 at hsq
    rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hn_pos.le,
      show -(1 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(2 / 3 : ℝ) by norm_num] at hsq
    calc η n ^ 2 * gapWKB n ^ 2 ≤ η n ^ 2 * (gapConst ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = η n ^ 2 * gapConst ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by ring
  have hdelta : (airyZero n - designSiteU N n) ^ 2 ≤
      (if N < n then C0 ^ 2 * (n : ℝ) ^ (-(8 / 3 : ℝ)) else 0) := by
    by_cases hnN : n ≤ N
    · have : designSiteU N n = airyZero n := by simp [designSiteU, hnN]
      rw [this, sub_self]; simp [not_lt.mpr hnN]
    · have hNn : N < n := by omega
      simp only [hNn, ↓reduceIte]
      have h1 := hP.site_le hn
      have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs, mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (-(4 / 3 : ℝ))) 2,
        ← Real.rpow_mul hn_pos.le, show -(4 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(8 / 3 : ℝ) by norm_num] at h2
      exact h2
  have e1 : (n : ℝ) ^ (-(8 / 3 : ℝ)) * (n : ℝ) ^ (-(2 / 3 : ℝ)) = (n : ℝ) ^ (-(10 / 3 : ℝ)) := by
    rw [← Real.rpow_add hn_pos]; norm_num
  have e2 : (n : ℝ) ^ (-(2 / 3 : ℝ)) * (n : ℝ) ^ (-(2 / 3 : ℝ)) = (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
    rw [← Real.rpow_add hn_pos]; norm_num
  have hp23 : 0 ≤ (n : ℝ) ^ (-(2 / 3 : ℝ)) := by positivity
  have hmax1 : gapConst ^ 2 ≤ max (gapConst ^ 2) (C0 ^ 2) := le_max_left _ _
  have hmax2 : C0 ^ 2 ≤ max (gapConst ^ 2) (C0 ^ 2) := le_max_right _ _
  have hsum_le : ((airyZero n - designSiteU N n) ^ 2 + (rampedWidthU η n) ^ 2) * (n : ℝ) ^ (-(2 / 3 : ℝ)) ≤
      (if N < n then C0 ^ 2 * (n : ℝ) ^ (-(10 / 3 : ℝ)) else 0) +
        η n ^ 2 * gapConst ^ 2 * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_right (add_le_add hdelta hgap_sq) hp23
    refine h1.trans (le_of_eq ?_)
    split_ifs
    · linear_combination C0 ^ 2 * e1 + (η n ^ 2 * gapConst ^ 2) * e2
    · linear_combination (η n ^ 2 * gapConst ^ 2) * e2
  have hmaxnn : 0 ≤ max (gapConst ^ 2) (C0 ^ 2) := le_trans (by positivity) hmax1
  calc profPi0 (designSiteU N) (rampedWidthU η) n
      ≤ CP * ((airyZero n - designSiteU N n) ^ 2 + (rampedWidthU η n) ^ 2) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := hmain
    _ = CP * (((airyZero n - designSiteU N n) ^ 2 + (rampedWidthU η n) ^ 2) * (n : ℝ) ^ (-(2 / 3 : ℝ))) := by ring
    _ ≤ CP * ((if N < n then C0 ^ 2 * (n : ℝ) ^ (-(10 / 3 : ℝ)) else 0) +
          η n ^ 2 * gapConst ^ 2 * (n : ℝ) ^ (-(4 / 3 : ℝ))) := mul_le_mul_of_nonneg_left hsum_le hCP.le
    _ ≤ CP * max (gapConst ^ 2) (C0 ^ 2) *
          (η n ^ 2 * (n : ℝ) ^ (-(4 / 3 : ℝ)) + (if N < n then (n : ℝ) ^ (-(10 / 3 : ℝ)) else 0)) := by
        have h43 : 0 ≤ (n : ℝ) ^ (-(4 / 3 : ℝ)) := by positivity
        have h103 : 0 ≤ (n : ℝ) ^ (-(10 / 3 : ℝ)) := by positivity
        rw [mul_assoc CP (max (gapConst ^ 2) (C0 ^ 2))]
        refine mul_le_mul_of_nonneg_left ?_ hCP.le
        split_ifs
        · nlinarith [mul_le_mul_of_nonneg_right hmax1 (mul_nonneg (sq_nonneg (η n)) h43),
            mul_le_mul_of_nonneg_right hmax2 h103]
        · nlinarith [mul_le_mul_of_nonneg_right hmax1 (mul_nonneg (sq_nonneg (η n)) h43)]

/-- Reindexing `∑_{i < N-1} f(i+2) = ∑_{k=2}^N f(k)`. -/
lemma sum_range_add_two_eq_Icc (f : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ Finset.range (N - 1), f (i + 2) = ∑ k ∈ Finset.Icc 2 N, f k := by
  have h : Finset.Icc 2 N = (Finset.range (N - 1)).image (· + 2) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hk; exact ⟨k - 2, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩; omega
  rw [h, Finset.sum_image (fun a _ b _ hab => by simpa using hab)]

/-- The majorant `G(n) = η_{n+2}² (n+2)^{-4/3} + 1_{n+2 > N} (n+2)^{-10/3}` of `Π_{n+2}(0)`. -/
noncomputable def pUnifG (N : ℕ) (η : ℕ → ℝ) (n : ℕ) : ℝ :=
  η (n + 2) ^ 2 * ((n + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) +
    (if N < n + 2 then ((n + 2 : ℕ) : ℝ) ^ (-(10 / 3 : ℝ)) else 0)

lemma pUnifG_nonneg (N : ℕ) (η : ℕ → ℝ) (n : ℕ) : 0 ≤ pUnifG N η n := by
  unfold pUnifG; split_ifs <;> positivity

lemma pUnifG_summable (N : ℕ) {η : ℕ → ℝ} (hη : AdmHeights η) : Summable (pUnifG N η) := by
  have hG_le : ∀ n, pUnifG N η n ≤ 2 * ((n + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) := fun n => by
    have h2 : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 2)
    have h43 : 0 ≤ ((n + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) := by positivity
    have h103 : ((n + 2 : ℕ) : ℝ) ^ (-(10 / 3 : ℝ)) ≤ ((n + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le h2 (by norm_num)
    obtain ⟨h0, h1⟩ := hη (n + 2) (by omega)
    have hη2 : η (n + 2) ^ 2 ≤ 1 := by nlinarith
    have : η (n + 2) ^ 2 * ((n + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) ≤ ((n + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) := by
      nlinarith
    unfold pUnifG; split_ifs <;> linarith
  have hZ43 : Summable (fun n : ℕ => ((n + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ))) :=
    (summable_nat_add_iff 2).mpr (Real.summable_nat_rpow.mpr (by norm_num : -(4 / 3 : ℝ) < -1))
  exact Summable.of_nonneg_of_le (pUnifG_nonneg N η) hG_le (hZ43.mul_left 2)

/-- **`E_0` bound, series form** (`P-unif`): `E_0 ≤ C ∑_{n ≥ 2} (η_n² n^{-4/3} + 1_{n > N} n^{-10/3})`,
with the summability of `Π_n(0)`. -/
theorem pUnif_E0_tsum :
    ∃ C > 0, ∀ (N : ℕ) (η : ℕ → ℝ), AdmHeights η →
      Summable (fun n : ℕ => profPi0 (designSiteU N) (rampedWidthU η) (n + 2)) ∧
      profE0 (designSiteU N) (rampedWidthU η) ≤ C * ∑' n : ℕ, pUnifG N η n := by
  obtain ⟨C0, hC0, hprof⟩ := rampedProfile_profHyp
  obtain ⟨C, hC, hpi⟩ := pUnif_Pi0_le
  refine ⟨C, hC, fun N η hη => ?_⟩
  have hH : AiryProdTailHypothesis 1 (designSiteU N) (rampedWidthU η) :=
    ProfHyp.tailHyp (f := 1) le_rfl hC0 (hprof N η hη)
  have hGs := pUnifG_summable N hη
  have hle : ∀ n, profPi0 (designSiteU N) (rampedWidthU η) (n + 2) ≤ C * pUnifG N η n := fun n =>
    hpi N η hη (n + 2) (by omega)
  have hPs : Summable (fun n : ℕ => profPi0 (designSiteU N) (rampedWidthU η) (n + 2)) :=
    Summable.of_nonneg_of_le (fun n => profPi0_nonneg _ _ hH (by omega)) hle (hGs.mul_left C)
  refine ⟨hPs, ?_⟩
  unfold profE0
  calc ∑' n : ℕ, profPi0 (designSiteU N) (rampedWidthU η) (n + 2)
      ≤ ∑' n : ℕ, C * pUnifG N η n := hPs.tsum_le_tsum hle (hGs.mul_left C)
    _ = C * ∑' n : ℕ, pUnifG N η n := tsum_mul_left

/-- **`E_0` bound** (`P-unif`, `rem:profile`): for every `N ≥ 1` and every height profile
`0 ≤ η_k ≤ 1/4`,
`E_0 ≤ C (∑_{n=2}^N η_n² n^{-4/3} + ∑_{n>N} (η_n² n^{-4/3} + n^{-10/3}))`. -/
theorem pUnif_E0 :
    ∃ C > 0, ∀ (N : ℕ), 1 ≤ N → ∀ η : ℕ → ℝ, AdmHeights η →
      profE0 (designSiteU N) (rampedWidthU η) ≤ C *
        (∑ n ∈ Finset.Icc 2 N, η n ^ 2 * (n : ℝ) ^ (-(4 / 3 : ℝ)) +
          ∑' m : ℕ, (η (N + 1 + m) ^ 2 * ((N + 1 + m : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) +
            ((N + 1 + m : ℕ) : ℝ) ^ (-(10 / 3 : ℝ)))) := by
  obtain ⟨C, hC, htsum⟩ := pUnif_E0_tsum
  refine ⟨C, hC, fun N hN η hη => ?_⟩
  obtain ⟨hPs, hE⟩ := htsum N η hη
  refine hE.trans (mul_le_mul_of_nonneg_left (le_of_eq ?_) hC.le)
  have hGs := pUnifG_summable N hη
  have hsplit := hGs.sum_add_tsum_nat_add (N - 1)
  rw [← hsplit]
  congr 1
  · rw [← sum_range_add_two_eq_Icc (fun n => η n ^ 2 * (n : ℝ) ^ (-(4 / 3 : ℝ))) N]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have hnot : ¬ N < i + 2 := by omega
    simp [pUnifG, hnot]
  · refine tsum_congr fun m => ?_
    have hidx : m + (N - 1) + 2 = N + 1 + m := by omega
    have hnl : ¬ N + 1 + m ≤ N := by omega
    simp [pUnifG, hidx, hnl]

end FormalResearch.ModularBootstrap.Upper.Ramped
