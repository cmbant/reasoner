module

public import FormalResearch.ModularBootstrap.Upper.Ramped.CombBridge
public import FormalResearch.ModularBootstrap.Upper.Ramped.PUnif
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedDesignPhase
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedDesignShift
public import FormalResearch.ModularBootstrap.Upper.Window.AiryProdPositive

/-!
# The Airy profile of the ramped comb and `E_0 = O(c'^{-1/3})` (`rem:thmU` Step (5), first part)

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`) Step (5) and Lemma `P_unif` (`rem:profile`).

* `designAiryW_ramped_eq`: the Airy window of the ramped comb, `designAiryW (rampedNode d c') (rampedEta P c')`
  (the `W_D` of `rampedComb_amplitude`), is the profile product `profW (designSiteU N_Ai) (rampedWidthU η) d` of
  Lemma `P_unif` (`N = N_Ai`, `η = rampedEta P c'`);
* `rampedE0_le`: `E_0 ≤ C c'^{-1/3}` for the ramped heights, `C = C(C_I, C_mid)`.  The four contributions of the
  paper are `N_Ai^{-7/3} ≤ c'^{-7/18}`, `C_I² N_tr c'^{-1/2} ≲ c'^{-2/5}` (the paper's `c'^{-13/30}` is the sharper
  count of `Σ min(n, N_tr) n^{-4/3}`), `C_mid² c'^{-5/6} M^{1/2} ≲ c'^{-1/3}` and `M^{-1/3} ≲ c'^{-1/3}`; all are
  `O(c'^{-1/3})`;
* `rampedW_package`: the consequences of `lemma_P_unif` and the profile Lemma `V` for `W_D` that the vacuum step
  uses: the bound `‖W_D(u)‖ ≤ C_w (1 + |u|)^{-3/2}` (`C_w` absolute), the sign structure
  `W_D(u) = -(u - (a_1 - d)) S(u)`, `S > 0`, and `∫ Re W_D ≤ -d/2 + C_E c'^{-1/3}`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Design FormalResearch.Special
  FormalResearch.ModularBootstrap.Upper.Window

lemma airyWindowProd_congr (f : ℕ) (uF : ℝ) {uSite uSite' epsU epsU' : ℕ → ℝ}
    (hs : ∀ k, f < k → uSite k = uSite' k) (he : ∀ k, f < k → epsU k = epsU' k) :
    airyWindowProd f uF uSite epsU = airyWindowProd f uF uSite' epsU' := by
  have hf : ∀ u, airyProdTail f uSite epsU u = airyProdTail f uSite' epsU' u := fun u => by
    unfold airyProdTail airyProdFactor
    refine tprod_congr fun m => ?_
    rw [hs (f + 1 + m) (by omega), he (f + 1 + m) (by omega)]
  have hex : ∀ n u, f < n → airyProdTailExcept f n uSite epsU u = airyProdTailExcept f n uSite' epsU' u := fun n u _ => by
    unfold airyProdTailExcept airyProdFactor
    refine tprod_congr fun m => ?_
    split_ifs
    · rfl
    · rw [hs (f + 1 + m) (by omega), he (f + 1 + m) (by omega)]
  funext u
  unfold airyWindowProd
  by_cases h : ∃ n : ℕ, 1 ≤ n ∧ u = (airyZero n : ℂ)
  · simp only [h, dite_true]
    split_ifs with hnf
    · rw [hf]
    · have hfn : f < Nat.find h := by omega
      rw [hs _ hfn, he _ hfn, hex _ _ hfn]
  · simp only [h, dite_false]
    rw [hf]

lemma designAiryW_ramped_eq (P : RampedParams) (c' d : ℝ) (u : ℝ) :
    designAiryW (rampedNode d c') (rampedEta P c') u =
      profW (designSiteU (nAi c')) (rampedWidthU (rampedEta P c')) d (u : ℂ) := by
  have hκ := kappaAiry_pos
  unfold designAiryW profW
  have hfun := airyWindowProd_congr 1 (airyZero 1 - d)
    (uSite := fun k => -kappaAiry * rampedNode d c' k) (uSite' := designSiteU (nAi c'))
    (epsU := fun k => kappaAiry * epsHat (rampedEta P c') k) (epsU' := rampedWidthU (rampedEta P c'))
    (fun k hk => by
      have hk2 : k ≠ 1 := by omega
      unfold designSiteU rampedNode
      simp only [hk2, ↓reduceIte]
      split_ifs with h
      · unfold sNodeAiry
        rw [abs_of_neg (airyZero_neg k)]
        field_simp
      · rfl)
    (fun k hk => by
      unfold rampedWidthU epsHat gapWKB uWKB phiWKB phiQuantile
      push_cast
      ring)
  have h1 : -kappaAiry * rampedNode d c' 1 = airyZero 1 - d := by
    unfold rampedNode sNodeAiry
    simp only [↓reduceIte]
    rw [abs_of_neg (airyZero_neg 1)]
    field_simp
    ring
  rw [← hfun, h1]

lemma sum_two_shift (g : ℕ → ℝ) (K : ℕ) :
    ∑ n ∈ Finset.range K, g (n + 2) = ∑ k ∈ Finset.Ioc 1 (1 + K), g k := by
  have := sum_range_shift g 1 K
  rw [← this]
  exact Finset.sum_congr rfl fun n _ => by rw [show 1 + 1 + n = n + 2 by omega]

/-- Sum of the capped ramp over `Ioc 1 b`. -/
lemma sum_min_le {B : ℝ} (hB : 0 ≤ B) {M : ℕ} (hM : 1 ≤ M) (b : ℕ) :
    ∑ k ∈ Finset.Ioc 1 b, min (1 / 16 : ℝ) (B * (k : ℝ) ^ (5 / 6 : ℝ)) * (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤
      2 * B * (M : ℝ) ^ (1 / 2 : ℝ) + 3 / 16 * (M : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hpt : ∀ k ∈ Finset.Ioc 1 b,
      min (1 / 16 : ℝ) (B * (k : ℝ) ^ (5 / 6 : ℝ)) * (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤
        (if k ≤ M then B * (k : ℝ) ^ (-(1 / 2 : ℝ)) else 0) +
          (if k ≤ M then 0 else 1 / 16 * (k : ℝ) ^ (-(4 / 3 : ℝ))) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Ioc.1 hk).1.le
    have hk0 : (0 : ℝ) < k := by linarith
    have h43 : 0 ≤ (k : ℝ) ^ (-(4 / 3 : ℝ)) := by positivity
    by_cases hkM : k ≤ M
    · simp only [hkM, ↓reduceIte, add_zero]
      calc min (1 / 16 : ℝ) (B * (k : ℝ) ^ (5 / 6 : ℝ)) * (k : ℝ) ^ (-(4 / 3 : ℝ))
          ≤ (B * (k : ℝ) ^ (5 / 6 : ℝ)) * (k : ℝ) ^ (-(4 / 3 : ℝ)) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) h43
        _ = B * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
            rw [mul_assoc, ← Real.rpow_add hk0]; norm_num
    · simp only [hkM, ↓reduceIte, zero_add]
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) h43
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · rw [← Finset.sum_filter]
    calc ∑ k ∈ (Finset.Ioc 1 b).filter (· ≤ M), B * (k : ℝ) ^ (-(1 / 2 : ℝ))
        ≤ ∑ k ∈ Finset.Icc 1 M, B * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => by positivity)
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢
          omega
      _ = B * ∑ k ∈ Finset.Icc 1 M, (k : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ B * ((M : ℝ) ^ (1 - 1 / 2 : ℝ) / (1 - 1 / 2)) :=
          mul_le_mul_of_nonneg_left (sum_Icc_rpow_neg_lt_one (by norm_num) (by norm_num) M) hB
      _ = 2 * B * (M : ℝ) ^ (1 / 2 : ℝ) := by norm_num; ring
  · have : ∑ k ∈ Finset.Ioc 1 b, (if k ≤ M then (0 : ℝ) else 1 / 16 * (k : ℝ) ^ (-(4 / 3 : ℝ))) =
        ∑ k ∈ (Finset.Ioc 1 b).filter (fun k => ¬ k ≤ M), 1 / 16 * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp_all
    rw [this]
    calc ∑ k ∈ (Finset.Ioc 1 b).filter (fun k => ¬ k ≤ M), 1 / 16 * (k : ℝ) ^ (-(4 / 3 : ℝ))
        ≤ ∑ k ∈ Finset.Ioc M b, 1 / 16 * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => by positivity)
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hk ⊢
          omega
      _ = 1 / 16 * ∑ k ∈ Finset.Ioc M b, (k : ℝ) ^ (-(4 / 3 : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ 1 / 16 * ((M : ℝ) ^ (1 - 4 / 3 : ℝ) / (4 / 3 - 1)) :=
          mul_le_mul_of_nonneg_left (sum_Ioc_rpow_neg_gt_one (by norm_num) hM b) (by norm_num)
      _ = 3 / 16 * (M : ℝ) ^ (-(1 / 3 : ℝ)) := by norm_num; ring

lemma pUnifG_tsum_le {N : ℕ} (hN : 1 ≤ N) {η : ℕ → ℝ} (hη : AdmHeights η) {A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hηAB : ∀ k : ℕ, 2 ≤ k → η k ^ 2 ≤ A + min (1 / 16 : ℝ) (B * (k : ℝ) ^ (5 / 6 : ℝ)))
    {M : ℕ} (hM : 1 ≤ M) :
    ∑' n : ℕ, pUnifG N η n ≤ 3 * A + (2 * B * (M : ℝ) ^ (1 / 2 : ℝ) + 3 / 16 * (M : ℝ) ^ (-(1 / 3 : ℝ))) +
      3 / 7 * (N : ℝ) ^ (-(7 / 3 : ℝ)) := by
  refine (pUnifG_summable N hη).tsum_le_of_sum_range_le fun K => ?_
  have hpt : ∀ n : ℕ, pUnifG N η n =
      η (n + 2) ^ 2 * ((n + 2 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) +
        (if N < n + 2 then ((n + 2 : ℕ) : ℝ) ^ (-(10 / 3 : ℝ)) else 0) := fun n => rfl
  have e1 : ∑ n ∈ Finset.range K, pUnifG N η n =
      ∑ k ∈ Finset.Ioc 1 (1 + K), ((η k ^ 2 * (k : ℝ) ^ (-(4 / 3 : ℝ))) +
        (if N < k then (k : ℝ) ^ (-(10 / 3 : ℝ)) else 0)) := by
    rw [← sum_two_shift (fun k => η k ^ 2 * (k : ℝ) ^ (-(4 / 3 : ℝ)) +
      (if N < k then (k : ℝ) ^ (-(10 / 3 : ℝ)) else 0)) K]
    exact Finset.sum_congr rfl fun n _ => hpt n
  rw [e1]
  have hpt2 : ∀ k ∈ Finset.Ioc 1 (1 + K), (η k ^ 2 * (k : ℝ) ^ (-(4 / 3 : ℝ)) +
        (if N < k then (k : ℝ) ^ (-(10 / 3 : ℝ)) else 0)) ≤
      (A * (k : ℝ) ^ (-(4 / 3 : ℝ)) + min (1 / 16 : ℝ) (B * (k : ℝ) ^ (5 / 6 : ℝ)) *
        (k : ℝ) ^ (-(4 / 3 : ℝ))) + (if N < k then (k : ℝ) ^ (-(10 / 3 : ℝ)) else 0) := by
    intro k hk
    have hk2 : 2 ≤ k := by have := (Finset.mem_Ioc.1 hk).1; omega
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have h43 : 0 ≤ (k : ℝ) ^ (-(4 / 3 : ℝ)) := by positivity
    have := mul_le_mul_of_nonneg_right (hηAB k hk2) h43
    nlinarith
  refine (Finset.sum_le_sum hpt2).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have s1 : ∑ k ∈ Finset.Ioc 1 (1 + K), A * (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 3 * A := by
    rw [← Finset.mul_sum]
    have := sum_Ioc_rpow_neg_gt_one (p := 4 / 3) (by norm_num) (a := 1) le_rfl (1 + K)
    norm_num at this
    nlinarith
  have s2 := sum_min_le hB hM (1 + K)
  have s3 : ∑ k ∈ Finset.Ioc 1 (1 + K), (if N < k then (k : ℝ) ^ (-(10 / 3 : ℝ)) else 0) ≤
      3 / 7 * (N : ℝ) ^ (-(7 / 3 : ℝ)) := by
    rw [← Finset.sum_filter]
    calc ∑ k ∈ (Finset.Ioc 1 (1 + K)).filter (fun k => N < k), (k : ℝ) ^ (-(10 / 3 : ℝ))
        ≤ ∑ k ∈ Finset.Ioc N (1 + K), (k : ℝ) ^ (-(10 / 3 : ℝ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => by positivity)
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hk ⊢
          omega
      _ ≤ (N : ℝ) ^ (1 - 10 / 3 : ℝ) / (10 / 3 - 1) :=
          sum_Ioc_rpow_neg_gt_one (by norm_num) hN _
      _ = 3 / 7 * (N : ℝ) ^ (-(7 / 3 : ℝ)) := by norm_num; ring
  linarith

lemma min_add_le_add_min {p a b : ℝ} (ha : 0 ≤ a) : min p (a + b) ≤ a + min p b := by
  rcases le_total p b with h | h
  · rw [min_eq_left h]; exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_right h]; exact (min_le_right _ _).trans (by linarith)

lemma etaSq_le_AB (P : RampedParams) {c' : ℝ} (hc' : 0 < c') (k : ℕ) :
    etaSq P c' k ≤ P.CI ^ 2 * nTr c' / √c' +
      min (1 / 16 : ℝ) (P.Cmid ^ 2 * c' ^ (-(5 / 6 : ℝ)) * (k : ℝ) ^ (5 / 6 : ℝ)) := by
  have hnT := nTr_nonneg hc'
  have hs : 0 < √c' := Real.sqrt_pos.2 hc'
  have hA : 0 ≤ P.CI ^ 2 * nTr c' / √c' := by positivity
  have e : P.Cmid ^ 2 * ((k : ℝ) / c') ^ (5 / 6 : ℝ) =
      P.Cmid ^ 2 * c' ^ (-(5 / 6 : ℝ)) * (k : ℝ) ^ (5 / 6 : ℝ) := by
    rw [Real.div_rpow (Nat.cast_nonneg k) hc'.le, Real.rpow_neg hc'.le]; ring
  have h1 : P.CI ^ 2 * min (k : ℝ) (nTr c') / √c' ≤ P.CI ^ 2 * nTr c' / √c' := by
    apply div_le_div_of_nonneg_right _ hs.le
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
  unfold etaSq etaArg
  refine (min_le_min_left _ ?_).trans (min_add_le_add_min hA)
  rw [e] at *
  linarith [h1]

lemma one_le_nAi_of_pos {c' : ℝ} (hc' : 0 < c') : 1 ≤ nAi c' := by
  unfold nAi
  exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hc' _)).ne'

lemma rpow_le_nAi (c' : ℝ) : c' ^ (1 / 6 : ℝ) ≤ (nAi c' : ℝ) := Nat.le_ceil _

/-- **`E_0 = O(c'^{-1/3})` for the ramped heights** (`rem:thmU` Step (5)): for every parameter set `P` there is
`C` such that, for `c'` large, `E_0 ≤ C c'^{-1/3}`.  The four contributions are `N_Ai^{-7/3} ≤ c'^{-7/18}`,
`C_I² N_tr c'^{-1/2} ≲ c'^{-2/5}`, `C_mid² c'^{-5/6} M^{1/2} ≲ c'^{-1/3}` and `M^{-1/3} ≲ c'^{-1/3}`. -/
theorem rampedE0_le (P : RampedParams) :
    ∃ C : ℝ, 0 < C ∧ ∀ c' : ℝ, 1 ≤ c' →
      profE0 (designSiteU (nAi c')) (rampedWidthU (rampedEta P c')) ≤ C * c' ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨C1, hC1, hE⟩ := pUnif_E0_tsum
  obtain ⟨a, b, ha, hb, hnT⟩ := nTr_bounds
  refine ⟨C1 * (3 * P.CI ^ 2 * b + 2 * P.Cmid ^ 2 + 3 / 8 + 3 / 7), by positivity, fun c' hc'1 => ?_⟩
  have hc' : 0 < c' := by linarith
  have hadm : AdmHeights (rampedEta P c') := fun k _ => ⟨rampedEta_nonneg P c' k, rampedEta_le P c' k⟩
  obtain ⟨-, hE'⟩ := hE (nAi c') (rampedEta P c') hadm
  set A : ℝ := P.CI ^ 2 * nTr c' / √c' with hAdef
  set B : ℝ := P.Cmid ^ 2 * c' ^ (-(5 / 6 : ℝ)) with hBdef
  have hs : 0 < √c' := Real.sqrt_pos.2 hc'
  have hA0 : 0 ≤ A := by have := nTr_nonneg hc'; positivity
  have hB0 : 0 ≤ B := by positivity
  have hηAB : ∀ k : ℕ, 2 ≤ k → rampedEta P c' k ^ 2 ≤ A + min (1 / 16 : ℝ) (B * (k : ℝ) ^ (5 / 6 : ℝ)) :=
    fun k _ => by rw [rampedEta_sq P hc' k]; exact etaSq_le_AB P hc' k
  set M : ℕ := ⌊c'⌋₊ with hMdef
  have hM1 : 1 ≤ M := Nat.le_floor (by simpa using hc'1)
  have hMle : (M : ℝ) ≤ c' := Nat.floor_le hc'.le
  have hMge : c' / 2 ≤ (M : ℝ) := by
    have h1 := Nat.lt_floor_add_one c'
    have h2 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
    rw [← hMdef] at h1
    linarith
  have hT := pUnifG_tsum_le (one_le_nAi_of_pos hc') hadm hA0 hB0 hηAB hM1
  have hc13 : 0 < c' ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc' _
  -- the four terms
  have t1 : A ≤ P.CI ^ 2 * b * c' ^ (-(1 / 3 : ℝ)) := by
    have h1 := (hnT c' hc'1).2
    have hsq : √c' = c' ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow c'
    have e1 : A = P.CI ^ 2 * nTr c' * c' ^ (-(1 / 2 : ℝ)) := by
      rw [hAdef, hsq, Real.rpow_neg hc'.le]; ring
    have e2 : c' ^ (1 / 10 : ℝ) * c' ^ (-(1 / 2 : ℝ)) = c' ^ (-(2 / 5 : ℝ)) := by
      rw [← Real.rpow_add hc']; norm_num
    have e3 : c' ^ (-(2 / 5 : ℝ)) ≤ c' ^ (-(1 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hc'1 (by norm_num)
    rw [e1]
    calc P.CI ^ 2 * nTr c' * c' ^ (-(1 / 2 : ℝ))
        ≤ P.CI ^ 2 * (b * c' ^ (1 / 10 : ℝ)) * c' ^ (-(1 / 2 : ℝ)) := by gcongr
      _ = P.CI ^ 2 * b * (c' ^ (1 / 10 : ℝ) * c' ^ (-(1 / 2 : ℝ))) := by ring
      _ = P.CI ^ 2 * b * c' ^ (-(2 / 5 : ℝ)) := by rw [e2]
      _ ≤ P.CI ^ 2 * b * c' ^ (-(1 / 3 : ℝ)) := by gcongr
  have t2 : B * (M : ℝ) ^ (1 / 2 : ℝ) ≤ P.Cmid ^ 2 * c' ^ (-(1 / 3 : ℝ)) := by
    have h1 : (M : ℝ) ^ (1 / 2 : ℝ) ≤ c' ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg M) hMle (by norm_num)
    have e : c' ^ (-(5 / 6 : ℝ)) * c' ^ (1 / 2 : ℝ) = c' ^ (-(1 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc']; norm_num
    calc B * (M : ℝ) ^ (1 / 2 : ℝ) ≤ P.Cmid ^ 2 * c' ^ (-(5 / 6 : ℝ)) * c' ^ (1 / 2 : ℝ) := by
          rw [hBdef]; gcongr
      _ = P.Cmid ^ 2 * (c' ^ (-(5 / 6 : ℝ)) * c' ^ (1 / 2 : ℝ)) := by ring
      _ = P.Cmid ^ 2 * c' ^ (-(1 / 3 : ℝ)) := by rw [e]
  have t3 : (M : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 2 * c' ^ (-(1 / 3 : ℝ)) := by
    have h1 : (M : ℝ) ^ (-(1 / 3 : ℝ)) ≤ (c' / 2) ^ (-(1 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hMge (by norm_num)
    have h2 : (c' / 2) ^ (-(1 / 3 : ℝ)) = c' ^ (-(1 / 3 : ℝ)) * (2 : ℝ) ^ (1 / 3 : ℝ) := by
      rw [Real.div_rpow hc'.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      rw [div_eq_mul_inv, inv_inv]
    have h3 : (2 : ℝ) ^ (1 / 3 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    rw [h2] at h1
    nlinarith
  have t4 : (nAi c' : ℝ) ^ (-(7 / 3 : ℝ)) ≤ c' ^ (-(1 / 3 : ℝ)) := by
    have h1 : (nAi c' : ℝ) ^ (-(7 / 3 : ℝ)) ≤ (c' ^ (1 / 6 : ℝ)) ^ (-(7 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hc' _) (rpow_le_nAi c') (by norm_num)
    have h2 : (c' ^ (1 / 6 : ℝ)) ^ (-(7 / 3 : ℝ)) = c' ^ (-(7 / 18 : ℝ)) := by
      rw [← Real.rpow_mul hc'.le]; norm_num
    have h3 : c' ^ (-(7 / 18 : ℝ)) ≤ c' ^ (-(1 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hc'1 (by norm_num)
    linarith
  have hfin : ∑' n : ℕ, pUnifG (nAi c') (rampedEta P c') n ≤
      (3 * P.CI ^ 2 * b + 2 * P.Cmid ^ 2 + 3 / 8 + 3 / 7) * c' ^ (-(1 / 3 : ℝ)) := by
    have : 2 * B * (M : ℝ) ^ (1 / 2 : ℝ) = 2 * (B * (M : ℝ) ^ (1 / 2 : ℝ)) := by ring
    nlinarith
  calc profE0 (designSiteU (nAi c')) (rampedWidthU (rampedEta P c'))
      ≤ C1 * ∑' n : ℕ, pUnifG (nAi c') (rampedEta P c') n := hE'
    _ ≤ C1 * ((3 * P.CI ^ 2 * b + 2 * P.Cmid ^ 2 + 3 / 8 + 3 / 7) * c' ^ (-(1 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hfin hC1.le
    _ = _ := by ring


lemma rampedProfile_tailHyp (P : RampedParams) (c' : ℝ) :
    AiryProdTailHypothesis 1 (designSiteU (nAi c')) (rampedWidthU (rampedEta P c')) := by
  obtain ⟨C0, hC0, hprof⟩ := rampedProfile_profHyp
  exact ProfHyp.tailHyp (f := 1) le_rfl hC0
    (hprof (nAi c') (rampedEta P c') fun k _ => ⟨rampedEta_nonneg P c' k, rampedEta_le P c' k⟩)

/-- **Sign structure of `W_D` on the real line**: `W_D(u) = -(u - (a_1 - d)) S(u)` with `S(u) > 0`. -/
theorem rampedW_form (P : RampedParams) {c' : ℝ} (hc' : 0 < c') (d : ℝ) (u : ℝ) :
    ∃ S : ℝ, 0 < S ∧ designAiryW (rampedNode d c') (rampedEta P c') u =
      ((-(u - (airyZero 1 - d)) * S : ℝ) : ℂ) := by
  rw [designAiryW_ramped_eq]
  unfold profW
  exact airyWindowProd_eq_neg_mul_pos (airyZero 1 - d) (rampedProfile_tailHyp P c')
    (fun k hk => by
      unfold rampedWidthU
      exact mul_ne_zero (rampedEta_pos P hc' (by omega)).ne' (gapWKB_pos (by omega)).ne') u

/-- **Consequences of `lemma_P_unif` and the profile Lemma `V` for `W_D`** (`rem:profile`, `ut:V`): for every `P`
there are `C_w` (absolute) and `C_E = C_E(P)` such that for `c'` large and `d ∈ [0, 1]`, `‖W_D(u)‖ ≤ C_w
(1 + |u|)^{-3/2}`, `Re W_D` is continuous and integrable on `ℝ`, and `∫ Re W_D ≤ -d/2 + C_E c'^{-1/3}`. -/
theorem rampedW_package (P : RampedParams) :
    ∃ Cw CE : ℝ, 0 < Cw ∧ 0 < CE ∧ ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ 1 →
      (∀ u : ℝ, ‖designAiryW (rampedNode d c') (rampedEta P c') u‖ ≤ Cw * (1 + |u|) ^ (-(3 / 2 : ℝ))) ∧
      Continuous (fun u : ℝ => (designAiryW (rampedNode d c') (rampedEta P c') u).re) ∧
      Integrable (fun u : ℝ => (designAiryW (rampedNode d c') (rampedEta P c') u).re) ∧
      (∫ u : ℝ, (designAiryW (rampedNode d c') (rampedEta P c') u).re) ≤
        -d / 2 + CE * c' ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨C, hC, N0, hN0, hPU⟩ := lemma_P_unif
  obtain ⟨N0', hint⟩ := pUnif_integral_le
  obtain ⟨CE, hCE, hE⟩ := rampedE0_le P
  refine ⟨C, CE, hC, hCE, ?_⟩
  have hnA : ∀ᶠ c' : ℝ in atTop, (max N0 N0' : ℝ) ≤ (nAi c' : ℝ) := by
    have h1 : Tendsto (fun c' : ℝ => c' ^ (1 / 6 : ℝ)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num)
    filter_upwards [h1.eventually_ge_atTop (max N0 N0' : ℝ)] with c' hc'
    exact hc'.trans (rpow_le_nAi c')
  filter_upwards [hnA, eventually_ge_atTop (1 : ℝ)] with c' hn hc1 d hd0 hd1
  have hc' : 0 < c' := by linarith
  have hN0c : N0 ≤ nAi c' := by
    have : (N0 : ℝ) ≤ (nAi c' : ℝ) := (le_max_left _ _).trans hn
    exact_mod_cast this
  have hN0'c : N0' ≤ nAi c' := by
    have : (N0' : ℝ) ≤ (nAi c' : ℝ) := (le_max_right _ _).trans hn
    exact_mod_cast this
  have hadm : AdmHeights (rampedEta P c') :=
    fun k _ => ⟨rampedEta_nonneg P c' k, rampedEta_le P c' k⟩
  obtain ⟨hG, -, -⟩ := hPU (nAi c') hN0c d hd0 hd1 (rampedEta P c') hadm
  have hH := rampedProfile_tailHyp P c'
  have hdiff := profW_differentiable _ _ hH d
  have hcont : Continuous (fun u : ℝ => profW (designSiteU (nAi c')) (rampedWidthU (rampedEta P c')) d
      (u : ℂ)) := hdiff.continuous.comp Complex.continuous_ofReal
  refine ⟨fun u => ?_, ?_, ?_, ?_⟩
  · rw [designAiryW_ramped_eq]
    have := hG (u : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    refine this.trans ?_
    have h1 := airyEnv_ofReal_le_one u
    have : 0 ≤ C * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by positivity
    nlinarith
  · simp only [designAiryW_ramped_eq]
    exact Complex.continuous_re.comp hcont
  · simp only [designAiryW_ramped_eq]
    exact (profW_integrable _ _ hH d).re
  · simp only [designAiryW_ramped_eq]
    exact (hint (nAi c') hN0'c d hd0 hd1 (rampedEta P c') hadm).trans
      (by linarith [hE c' hc1])

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedE0_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedE0_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedW_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedW_form

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedW_package' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedW_package

end FormalResearch.ModularBootstrap.Upper.Ramped
