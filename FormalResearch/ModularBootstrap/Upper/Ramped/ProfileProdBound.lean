module

public import FormalResearch.ModularBootstrap.Upper.Ramped.ProfileProducts

/-!
# Lemma E for profiles: the off-diagonal Airy product (`ut:E`, `rem:profile`)

`prof_prod_except_le`: for a profile with `|a_k - u_k| ≤ C_Z k^{-4/3}` and `ε_k² ≤ C_ε² k^{-2/3}`
(`k ≥ 2`), the product `∏_{k ≥ 2, k ≠ n} ((a_n - u_k)² + ε_k²)/(a_n - a_k)²` is bounded by an
absolute constant depending only on `(C_Z, C_ε)`, uniformly in `n ≥ 2`, in `N`, and in the profile.
This is the three-range estimate `k < n/2`, `|k - n| ≤ n/2`, `k > 2n` of the proof of
Lemma E (`ut:E`); the proof is that of `design_prod_except_le_exists` (Window/Quadrature.lean)
with the profile explicit.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window

/-- **Lemma E, off-diagonal product** (three ranges): uniform in the profile. -/
lemma prof_prod_except_le (C_Z C_eps : ℝ) (hC_Z : 0 < C_Z) :
    ∃ C_prod > 0, ∀ uSite epsU : ℕ → ℝ, AiryProdTailHypothesis 1 uSite epsU →
      (∀ k : ℕ, 2 ≤ k → |airyZero k - uSite k| ≤ C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ))) →
      (∀ k : ℕ, 2 ≤ k → (epsU k) ^ 2 ≤ C_eps ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ))) →
      ∀ n : ℕ, 2 ≤ n →
        ∏' m : ℕ, (if m + 2 = n then 1 else profRealFactor uSite epsU n (m + 2)) ≤ C_prod := by
  set C_sq := C_Z ^ 2 + C_eps ^ 2
  set Z43 : ℝ := ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ))
  have hZ43 : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ))) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num : -(4 / 3 : ℝ) < -1))
    simpa using this
  set Z2 : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 2
  have hZ2 : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using this
  have hZ43_nn : 0 ≤ Z43 := tsum_nonneg fun _ => by positivity
  have hZ2_nn : 0 ≤ Z2 := tsum_nonneg fun _ => by positivity
  -- Uniform exponent bound across the three ranges `2*k < n`, `n ≤ 2*k ≤ 4*n`, `2*n < k`
  set B_left : ℝ := 2 * C_Z / (9 / 10 : ℝ) * Z43 + 3 * C_sq / (9 / 10 : ℝ) ^ 2
  set c_mid : ℝ := (9 / 10 : ℝ) * (1 / 2 : ℝ) ^ (1 / 3 : ℝ)
  set B_mid : ℝ := 4 * (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) +
    2 * (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) * Z2
  set B_right : ℝ := (2 * C_Z / (9 / 10 : ℝ) + C_sq / (9 / 10 : ℝ) ^ 2) * Z2
  set B := B_left + B_mid + B_right
  refine ⟨Real.exp B, Real.exp_pos _, fun uSite epsU hH h_site_le h_width_le n hn => ?_⟩
  have hp := (profPi0_hasProd uSite epsU hH hn).1
  refine le_of_tendsto hp (Eventually.of_forall fun s => ?_)
  -- Bound each factor by `exp(...)`
  have h_fac : ∀ m : ℕ,
      (if m + 2 = n then (1 : ℝ) else profRealFactor uSite epsU n (m + 2)) ≤
        Real.exp (if m + 2 = n then 0 else
          2 * |airyZero (m + 2) - uSite (m + 2)| / |airyZero n - airyZero (m + 2)| +
          (|airyZero (m + 2) - uSite (m + 2)| ^ 2 + (epsU (m + 2)) ^ 2) /
            (airyZero n - airyZero (m + 2)) ^ 2) := by
    intro m
    split_ifs with hm
    · simp
    · unfold profRealFactor
      have hne : airyZero n - airyZero (m + 2) ≠ 0 := by
        intro h
        exact hm (airyZero_injective_on (by omega) (by omega) (sub_eq_zero.mp h)).symm
      have h_decomp : ((airyZero n - uSite (m + 2)) ^ 2 + (epsU (m + 2)) ^ 2) /
          (airyZero n - airyZero (m + 2)) ^ 2 =
          1 + (2 * (airyZero n - airyZero (m + 2)) * (airyZero (m + 2) - uSite (m + 2)) +
            ((airyZero (m + 2) - uSite (m + 2)) ^ 2 + (epsU (m + 2)) ^ 2)) /
            (airyZero n - airyZero (m + 2)) ^ 2 := by
        field_simp [hne]; ring
      rw [h_decomp]
      have h1 : 1 + (2 * (airyZero n - airyZero (m + 2)) * (airyZero (m + 2) - uSite (m + 2)) +
          ((airyZero (m + 2) - uSite (m + 2)) ^ 2 + (epsU (m + 2)) ^ 2)) /
          (airyZero n - airyZero (m + 2)) ^ 2 ≤
          1 + (2 * |airyZero (m + 2) - uSite (m + 2)| / |airyZero n - airyZero (m + 2)| +
            (|airyZero (m + 2) - uSite (m + 2)| ^ 2 + (epsU (m + 2)) ^ 2) /
              (airyZero n - airyZero (m + 2)) ^ 2) := by
        have h_cross : 2 * (airyZero n - airyZero (m + 2)) * (airyZero (m + 2) - uSite (m + 2)) /
            (airyZero n - airyZero (m + 2)) ^ 2 ≤
            2 * |airyZero (m + 2) - uSite (m + 2)| / |airyZero n - airyZero (m + 2)| := by
          have h_simp : 2 * (airyZero n - airyZero (m + 2)) * (airyZero (m + 2) - uSite (m + 2)) /
              (airyZero n - airyZero (m + 2)) ^ 2 =
              2 * (airyZero (m + 2) - uSite (m + 2)) / (airyZero n - airyZero (m + 2)) := by
            field_simp [hne]
          rw [h_simp]
          refine (le_abs_self _).trans (le_of_eq ?_)
          rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        rw [add_div, ← sq_abs (airyZero (m + 2) - uSite (m + 2))]
        linarith
      exact h1.trans (by rw [add_comm 1 _]; exact Real.add_one_le_exp _)
  have h_prod : ∏ m ∈ s, (if m + 2 = n then (1 : ℝ) else profRealFactor uSite epsU n (m + 2)) ≤
      Real.exp (∑ m ∈ s, if m + 2 = n then 0 else
        2 * |airyZero (m + 2) - uSite (m + 2)| / |airyZero n - airyZero (m + 2)| +
        (|airyZero (m + 2) - uSite (m + 2)| ^ 2 + (epsU (m + 2)) ^ 2) /
          (airyZero n - airyZero (m + 2)) ^ 2) := by
    calc ∏ m ∈ s, _ ≤ ∏ m ∈ s, Real.exp _ :=
          Finset.prod_le_prod₀ (fun m _ => by split_ifs; exact zero_le_one; unfold profRealFactor; positivity)
            (fun m _ => h_fac m)
      _ = Real.exp _ := (Real.exp_sum s _).symm
  refine h_prod.trans (Real.exp_le_exp.mpr ?_)
  -- Split `s` into the three ranges via `m + 2`
  have h_sq_le : ∀ k : ℕ, 2 ≤ k →
      |airyZero k - uSite k| ^ 2 + (epsU k) ^ 2 ≤ C_sq * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
    intro k hk
    have hk1 : 1 ≤ k := by omega
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk1
    have h1 := pow_le_pow_left₀ (abs_nonneg _) (h_site_le k hk) 2
    rw [mul_pow, ← Real.rpow_natCast ((k : ℝ) ^ (-(4 / 3 : ℝ))) 2, ← Real.rpow_mul hk_pos.le,
      show -(4 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(8 / 3 : ℝ) by norm_num] at h1
    have h1' : |airyZero k - uSite k| ^ 2 ≤ C_Z ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      exact h1.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hk' (by norm_num)) (by positivity))
    have h2 := h_width_le k hk
    dsimp [C_sq]; linarith
  let term : ℕ → ℝ := fun k =>
    if k = n then 0 else
      2 * |airyZero k - uSite k| / |airyZero n - airyZero k| +
      (|airyZero k - uSite k| ^ 2 + (epsU k) ^ 2) / (airyZero n - airyZero k) ^ 2
  have hterm_nn : ∀ k, 0 ≤ term k := fun k => by
    dsimp [term]; split_ifs <;> positivity
  set S_k := s.image (fun m => m + 2)
  have h_eq_Sk : ∑ m ∈ s, (if m + 2 = n then 0 else
        2 * |airyZero (m + 2) - uSite (m + 2)| / |airyZero n - airyZero (m + 2)| +
        (|airyZero (m + 2) - uSite (m + 2)| ^ 2 + (epsU (m + 2)) ^ 2) /
          (airyZero n - airyZero (m + 2)) ^ 2) =
      ∑ k ∈ S_k, term k := by
    rw [Finset.sum_image (fun a _ b _ h => by omega)]
  rw [h_eq_Sk]
  have hSk_ge2 : ∀ k ∈ S_k, 2 ≤ k := fun k hk => by
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hk; omega
  set S1 := S_k.filter (fun k => 2 * k < n)
  set S2 := S_k.filter (fun k => k ≠ n ∧ n ≤ 2 * k ∧ k ≤ 2 * n)
  set S3 := S_k.filter (fun k => 2 * n < k)
  have h_part : ∑ k ∈ S_k, term k ≤ ∑ k ∈ S1, term k + ∑ k ∈ S2, term k + ∑ k ∈ S3, term k := by
    have h_each : ∀ k ∈ S_k, term k ≤
        (if 2 * k < n then term k else 0) +
        (if k ≠ n ∧ n ≤ 2 * k ∧ k ≤ 2 * n then term k else 0) +
        (if 2 * n < k then term k else 0) := by
      intro k _
      by_cases hkn : k = n
      · subst hkn; simp [term]
      · by_cases h1 : 2 * k < n
        · have h2 : ¬(k ≠ n ∧ n ≤ 2 * k ∧ k ≤ 2 * n) := by omega
          have h3 : ¬(2 * n < k) := by omega
          simp [h1, h2, h3]
        · by_cases h2 : k ≤ 2 * n
          · have h3 : ¬(2 * n < k) := by omega
            have hmid : k ≠ n ∧ n ≤ 2 * k ∧ k ≤ 2 * n := ⟨hkn, by omega, h2⟩
            simp [h1, hmid, h3]
          · have h3 : 2 * n < k := by omega
            have hmid : ¬(k ≠ n ∧ n ≤ 2 * k ∧ k ≤ 2 * n) := by omega
            simp [h1, hmid, h3]
    have hs := Finset.sum_le_sum h_each
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hs
    have e1 : ∑ k ∈ S_k, (if 2 * k < n then term k else 0) = ∑ k ∈ S1, term k := by
      dsimp [S1]; rw [Finset.sum_filter]
    have e2 : ∑ k ∈ S_k, (if k ≠ n ∧ n ≤ 2 * k ∧ k ≤ 2 * n then term k else 0) = ∑ k ∈ S2, term k := by
      dsimp [S2]; rw [Finset.sum_filter]
    have e3 : ∑ k ∈ S_k, (if 2 * n < k then term k else 0) = ∑ k ∈ S3, term k := by
      dsimp [S3]; rw [Finset.sum_filter]
    linarith
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  -- Bound S1: 2*k < n
  have hS1_bd : ∑ k ∈ S1, term k ≤ B_left := by
    have h1 : ∀ k ∈ S1, term k ≤
        (2 * C_Z / (9 / 10 : ℝ)) * (k : ℝ) ^ (-(4 / 3 : ℝ)) +
        (C_sq / (9 / 10 : ℝ) ^ 2) * (n : ℝ) ^ (-(4 / 3 : ℝ)) * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
      intro k hk
      have hk_mem := Finset.mem_filter.mp hk
      have hk2 : 2 ≤ k := hSk_ge2 k hk_mem.1
      have h2kn : 2 * k < n := hk_mem.2
      have hkn : k ≠ n := by omega
      have hsep := airyZero_abs_sub_ge (by omega : 1 ≤ k) (by omega : 1 ≤ n) hkn
      have hmax : max n k = n := max_eq_left (by omega)
      rw [hmax] at hsep
      have hdiff : (n : ℝ) / 2 ≤ |(n : ℝ) - k| := by
        have : (2 * k : ℝ) < n := by exact_mod_cast h2kn
        rw [abs_of_nonneg (by linarith)]
        linarith
      have h_lb : (9 / 10 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) ≤ |airyZero n - airyZero k| := by
        have hn_pow : 0 < (n : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
        have h1' : (9 / 10 : ℝ) * (n : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤
            (9 / 5 : ℝ) * |(n : ℝ) - k| * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by nlinarith
        have h2' : (n : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) = (n : ℝ) ^ (2 / 3 : ℝ) := by
          conv_lhs => arg 1; rw [← Real.rpow_one (n : ℝ)]
          rw [← Real.rpow_add hn_pos]; norm_num
        rw [mul_assoc, h2'] at h1'
        linarith
      have h_lb_ge : (9 / 10 : ℝ) ≤ |airyZero n - airyZero k| := by
        have h1' : 1 ≤ (n : ℝ) ^ (2 / 3 : ℝ) := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
        linarith
      have h_lb_sq : (9 / 10 : ℝ) ^ 2 * (n : ℝ) ^ (4 / 3 : ℝ) ≤ (airyZero n - airyZero k) ^ 2 := by
        have hsq := pow_le_pow_left₀ (by positivity) h_lb 2
        rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (2 / 3 : ℝ)) 2, ← Real.rpow_mul hn_pos.le,
          show (2 / 3 : ℝ) * ((2 : ℕ) : ℝ) = 4 / 3 by norm_num, sq_abs] at hsq
        exact hsq
      have ht_eq : term k = 2 * |airyZero k - uSite k| / |airyZero n - airyZero k| +
          (|airyZero k - uSite k| ^ 2 + (epsU k) ^ 2) / (airyZero n - airyZero k) ^ 2 := by
        simp [term, hkn]
      rw [ht_eq]
      have hn43 : (n : ℝ) ^ (-(4 / 3 : ℝ)) = ((n : ℝ) ^ (4 / 3 : ℝ))⁻¹ := Real.rpow_neg hn_pos.le _
      have ha : 2 * |airyZero k - uSite k| / |airyZero n - airyZero k| ≤
          (2 * C_Z / (9 / 10 : ℝ)) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
        calc 2 * |airyZero k - uSite k| / |airyZero n - airyZero k|
            ≤ 2 * (C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ))) / (9 / 10 : ℝ) := by
              gcongr; exact h_site_le k (by omega)
          _ = (2 * C_Z / (9 / 10 : ℝ)) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by ring
      have hb : (|airyZero k - uSite k| ^ 2 + (epsU k) ^ 2) /
          (airyZero n - airyZero k) ^ 2 ≤
          (C_sq / (9 / 10 : ℝ) ^ 2) * (n : ℝ) ^ (-(4 / 3 : ℝ)) * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
        calc (|airyZero k - uSite k| ^ 2 + (epsU k) ^ 2) / (airyZero n - airyZero k) ^ 2
            ≤ (C_sq * (k : ℝ) ^ (-(2 / 3 : ℝ))) / ((9 / 10 : ℝ) ^ 2 * (n : ℝ) ^ (4 / 3 : ℝ)) := by
              gcongr; exact h_sq_le k (by omega)
          _ = (C_sq / (9 / 10 : ℝ) ^ 2) * (n : ℝ) ^ (-(4 / 3 : ℝ)) * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
              rw [hn43]; ring
      exact add_le_add ha hb
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h2
    have hs1 : ∑ k ∈ S1, (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ Z43 := by
      let φ : ℕ → ℕ := fun k => k - 1
      have hinj : Set.InjOn φ S1 := fun a ha b hb h => by
        have ha2 := hSk_ge2 a (Finset.mem_filter.mp ha).1
        have hb2 := hSk_ge2 b (Finset.mem_filter.mp hb).1
        dsimp [φ] at h; omega
      have him : ∑ k ∈ S1, (k : ℝ) ^ (-(4 / 3 : ℝ)) =
          ∑ j ∈ S1.image φ, ((j + 1 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk2 := hSk_ge2 k (Finset.mem_filter.mp hk).1
        dsimp [φ]; rw [show k - 1 + 1 = k by omega]
      rw [him]
      exact hZ43.sum_le_tsum _ fun _ _ => by positivity
    have hs2 : ∑ k ∈ S1, (k : ℝ) ^ (-(2 / 3 : ℝ)) ≤ 3 * (n : ℝ) ^ (1 / 3 : ℝ) := by
      have hsub : S1 ⊆ Finset.Icc 1 n := fun k hk => by
        have hm := Finset.mem_filter.mp hk
        exact Finset.mem_Icc.mpr ⟨by have := hSk_ge2 k hm.1; omega, by omega⟩
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans
        (rpow_neg_two_thirds_partial_sum_q n)
    have hmul_n : (n : ℝ) ^ (-(4 / 3 : ℝ)) * (n : ℝ) ^ (1 / 3 : ℝ) ≤ 1 := by
      rw [← Real.rpow_add hn_pos, show -(4 / 3 : ℝ) + 1 / 3 = -1 by norm_num, Real.rpow_neg_one]
      rw [inv_le_one_iff₀]; right; exact_mod_cast (by omega : 1 ≤ n)
    calc ∑ k ∈ S1, term k
        ≤ (2 * C_Z / (9 / 10 : ℝ)) * Z43 +
            (C_sq / (9 / 10 : ℝ) ^ 2) * (n : ℝ) ^ (-(4 / 3 : ℝ)) * (3 * (n : ℝ) ^ (1 / 3 : ℝ)) := by
          refine h2.trans (add_le_add (mul_le_mul_of_nonneg_left hs1 (by positivity)) ?_)
          exact mul_le_mul_of_nonneg_left hs2 (by positivity)
      _ = (2 * C_Z / (9 / 10 : ℝ)) * Z43 +
            3 * C_sq / (9 / 10 : ℝ) ^ 2 * ((n : ℝ) ^ (-(4 / 3 : ℝ)) * (n : ℝ) ^ (1 / 3 : ℝ)) := by ring
      _ ≤ (2 * C_Z / (9 / 10 : ℝ)) * Z43 + 3 * C_sq / (9 / 10 : ℝ) ^ 2 * 1 :=
          add_le_add_right (mul_le_mul_of_nonneg_left hmul_n (by positivity)) _
      _ = B_left := by dsimp [B_left]; ring
  -- Bound S2: n ≤ 2*k and k ≤ 2*n and k ≠ n
  have hS2_bd : ∑ k ∈ S2, term k ≤ B_mid := by
    have h1 : ∀ k ∈ S2, term k ≤
        (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) / (n : ℝ) +
        (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) / ((n : ℝ) - k) ^ 2 := by
      intro k hk
      have hm := Finset.mem_filter.mp hk
      have hk2 : 2 ≤ k := hSk_ge2 k hm.1
      obtain ⟨hkn, hn2k, hk2n⟩ := hm.2
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hsep := airyZero_abs_sub_ge (by omega : 1 ≤ k) (by omega : 1 ≤ n) hkn
      have hmax_le : ((max n k : ℕ) : ℝ) ≤ 2 * n := by
        exact_mod_cast max_le (by omega) hk2n
      have hmax_pow : (1 / 2 : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤
          ((max n k : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) := by
        have hpow := Real.rpow_le_rpow_of_nonpos (by positivity) hmax_le (by norm_num : -(1 / 3 : ℝ) ≤ 0)
        rw [Real.mul_rpow (by norm_num) hn_pos.le,
          show (2 : ℝ) ^ (-(1 / 3 : ℝ)) = (1 / 2 : ℝ) ^ (1 / 3 : ℝ) by
            rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num), one_div]; norm_num] at hpow
        exact hpow
      have hsep' : 2 * c_mid * |(n : ℝ) - k| * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ |airyZero n - airyZero k| := by
        have hc : 2 * c_mid = (9 / 5 : ℝ) * (1 / 2 : ℝ) ^ (1 / 3 : ℝ) := by dsimp [c_mid]; ring
        have := mul_le_mul_of_nonneg_left hmax_pow (by positivity : 0 ≤ (9 / 5 : ℝ) * |(n : ℝ) - k|)
        calc 2 * c_mid * |(n : ℝ) - k| * (n : ℝ) ^ (-(1 / 3 : ℝ))
            = (9 / 5 : ℝ) * |(n : ℝ) - k| * ((1 / 2 : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ))) := by
              rw [hc]; ring
          _ ≤ (9 / 5 : ℝ) * |(n : ℝ) - k| * ((max n k : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) := this
          _ ≤ |airyZero n - airyZero k| := by linarith
      have hnk_ge1 : (1 : ℝ) ≤ |(n : ℝ) - k| := by
        have h_int : (1 : ℤ) ≤ |(n : ℤ) - k| := by
          have : (n : ℤ) - k ≠ 0 := fun h0 => hkn (by omega)
          exact Int.one_le_abs this
        exact_mod_cast h_int
      have h_lb1 : c_mid * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ |airyZero n - airyZero k| := by
        have hn13 : 0 < (n : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
        have hc_pos : 0 < c_mid := by dsimp [c_mid]; positivity
        calc c_mid * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 2 * c_mid * 1 * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by nlinarith
          _ ≤ 2 * c_mid * |(n : ℝ) - k| * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by gcongr
          _ ≤ |airyZero n - airyZero k| := hsep'
      have h_lb_sq : c_mid ^ 2 * ((n : ℝ) - k) ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ)) ≤
          (airyZero n - airyZero k) ^ 2 := by
        have h1' : c_mid * |(n : ℝ) - k| * (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ |airyZero n - airyZero k| := by
          have : 0 ≤ c_mid * |(n : ℝ) - k| * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by dsimp [c_mid]; positivity
          linarith
        have hsq := pow_le_pow_left₀ (by dsimp [c_mid]; positivity) h1' 2
        rw [mul_pow, mul_pow, sq_abs, sq_abs, ← Real.rpow_natCast ((n : ℝ) ^ (-(1 / 3 : ℝ))) 2,
          ← Real.rpow_mul hn_pos.le,
          show -(1 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(2 / 3 : ℝ) by norm_num] at hsq
        exact hsq
      have h_k_ge : (n : ℝ) / 2 ≤ k := by
        have : (n : ℝ) ≤ 2 * k := by exact_mod_cast hn2k
        linarith
      have h_site_k : |airyZero k - uSite k| ≤
          C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
        have hpow := Real.rpow_le_rpow_of_nonpos (by positivity) h_k_ge (by norm_num : -(4 / 3 : ℝ) ≤ 0)
        have hpow_eq : ((n : ℝ) / 2) ^ (-(4 / 3 : ℝ)) = (n : ℝ) ^ (-(4 / 3 : ℝ)) * (2 : ℝ) ^ (4 / 3 : ℝ) := by
          rw [show (n : ℝ) / 2 = (n : ℝ) * (2 : ℝ)⁻¹ by ring, Real.mul_rpow hn_pos.le (by norm_num),
            show (2 : ℝ)⁻¹ ^ (-(4 / 3 : ℝ)) = (2 : ℝ) ^ (4 / 3 : ℝ) by
              rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]]
        rw [hpow_eq] at hpow
        calc |airyZero k - uSite k| ≤ C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ)) := h_site_le k (by omega)
          _ ≤ C_Z * ((n : ℝ) ^ (-(4 / 3 : ℝ)) * (2 : ℝ) ^ (4 / 3 : ℝ)) := mul_le_mul_of_nonneg_left hpow hC_Z.le
          _ = C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by ring
      have h_sq_k : |airyZero k - uSite k| ^ 2 + (epsU k) ^ 2 ≤
          C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
        have hpow := Real.rpow_le_rpow_of_nonpos (by positivity) h_k_ge (by norm_num : -(2 / 3 : ℝ) ≤ 0)
        have hpow_eq : ((n : ℝ) / 2) ^ (-(2 / 3 : ℝ)) = (n : ℝ) ^ (-(2 / 3 : ℝ)) * (2 : ℝ) ^ (2 / 3 : ℝ) := by
          rw [show (n : ℝ) / 2 = (n : ℝ) * (2 : ℝ)⁻¹ by ring, Real.mul_rpow hn_pos.le (by norm_num),
            show (2 : ℝ)⁻¹ ^ (-(2 / 3 : ℝ)) = (2 : ℝ) ^ (2 / 3 : ℝ) by
              rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]]
        rw [hpow_eq] at hpow
        calc |airyZero k - uSite k| ^ 2 + (epsU k) ^ 2 ≤ C_sq * (k : ℝ) ^ (-(2 / 3 : ℝ)) :=
              h_sq_le k (by omega)
          _ ≤ C_sq * ((n : ℝ) ^ (-(2 / 3 : ℝ)) * (2 : ℝ) ^ (2 / 3 : ℝ)) :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by ring
      have ht_eq : term k = 2 * |airyZero k - uSite k| / |airyZero n - airyZero k| +
          (|airyZero k - uSite k| ^ 2 + (epsU k) ^ 2) / (airyZero n - airyZero k) ^ 2 := by
        simp [term, hkn]
      rw [ht_eq]
      have h_n_rpow : (n : ℝ) ^ (-(4 / 3 : ℝ)) / (n : ℝ) ^ (-(1 / 3 : ℝ)) = 1 / (n : ℝ) := by
        rw [← Real.rpow_sub hn_pos, show -(4 / 3 : ℝ) - -(1 / 3 : ℝ) = -1 by norm_num, Real.rpow_neg_one, one_div]
      have ha : 2 * |airyZero k - uSite k| / |airyZero n - airyZero k| ≤
          (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) / (n : ℝ) := by
        have hc_pos : 0 < c_mid := by dsimp [c_mid]; positivity
        calc 2 * |airyZero k - uSite k| / |airyZero n - airyZero k|
            ≤ 2 * (C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) * (n : ℝ) ^ (-(4 / 3 : ℝ))) /
                (c_mid * (n : ℝ) ^ (-(1 / 3 : ℝ))) := by gcongr
          _ = (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) *
                ((n : ℝ) ^ (-(4 / 3 : ℝ)) / (n : ℝ) ^ (-(1 / 3 : ℝ))) := by ring
          _ = (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) * (1 / (n : ℝ)) := by rw [h_n_rpow]
          _ = (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) / (n : ℝ) := by ring
      have hb : (|airyZero k - uSite k| ^ 2 + (epsU k) ^ 2) /
          (airyZero n - airyZero k) ^ 2 ≤
          (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) / ((n : ℝ) - k) ^ 2 := by
        have hc_pos : 0 < c_mid := by dsimp [c_mid]; positivity
        have hnk_ne : ((n : ℝ) - k) ^ 2 ≠ 0 := pow_ne_zero 2 (by
          intro h0; apply hkn; exact_mod_cast (sub_eq_zero.mp h0).symm)
        have hn23_ne : (n : ℝ) ^ (-(2 / 3 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hn_pos _).ne'
        calc (|airyZero k - uSite k| ^ 2 + (epsU k) ^ 2) / (airyZero n - airyZero k) ^ 2
            ≤ (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (-(2 / 3 : ℝ))) /
                (c_mid ^ 2 * ((n : ℝ) - k) ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ))) := by
              gcongr
          _ = (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) / ((n : ℝ) - k) ^ 2 := by
              field_simp [hc_pos.ne', hnk_ne, hn23_ne]
      exact add_le_add ha hb
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_add_distrib] at h2
    have hcard : (S2.card : ℝ) ≤ 2 * n := by
      have hsub : S2 ⊆ Finset.Icc 1 (2 * n) := fun k hk => by
        have hm := Finset.mem_filter.mp hk
        exact Finset.mem_Icc.mpr ⟨by have := hSk_ge2 k hm.1; omega, hm.2.2.2⟩
      have hc : S2.card ≤ (Finset.Icc 1 (2 * n)).card := Finset.card_le_card hsub
      rw [Nat.card_Icc] at hc
      have : S2.card ≤ 2 * n := by omega
      exact_mod_cast this
    have hs1 : ∑ _k ∈ S2, (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) / (n : ℝ) ≤
        4 * (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcoef : 0 ≤ 2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid := by dsimp [c_mid]; positivity
      calc (S2.card : ℝ) * ((2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) / (n : ℝ))
          ≤ (2 * n) * ((2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) / (n : ℝ)) := by gcongr
        _ = 2 * (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) := by field_simp [hn_pos.ne']
        _ ≤ 4 * (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) := by linarith
    have hs2 : ∑ k ∈ S2, (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) / ((n : ℝ) - k) ^ 2 ≤
        2 * (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) * Z2 := by
      have hsplit : S2 = S2.filter (fun k => n < k) ∪ S2.filter (fun k => k < n) := by
        ext k; simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hk
          have hk' := hk
          dsimp [S2] at hk'
          rcases lt_or_gt_of_ne (Finset.mem_filter.mp hk').2.1 with hlt | hgt
          · exact Or.inr ⟨hk, hlt⟩
          · exact Or.inl ⟨hk, hgt⟩
        · rintro (⟨hk, _⟩ | ⟨hk, _⟩) <;> exact hk
      have hdisj : Disjoint (S2.filter (fun k => n < k)) (S2.filter (fun k => k < n)) :=
        Finset.disjoint_filter.mpr fun k _ h1 h2 => by omega
      have h_hi : ∑ k ∈ S2.filter (fun k => n < k), 1 / ((n : ℝ) - k) ^ 2 ≤ Z2 := by
        let φ : ℕ → ℕ := fun k => k - n - 1
        have hinj : Set.InjOn φ (S2.filter (fun k => n < k)) := fun a ha b hb h => by
          have ha' := (Finset.mem_filter.mp ha).2
          have hb' := (Finset.mem_filter.mp hb).2
          dsimp [φ] at h; omega
        have him : ∑ k ∈ S2.filter (fun k => n < k), 1 / ((n : ℝ) - k) ^ 2 =
            ∑ j ∈ (S2.filter (fun k => n < k)).image φ, 1 / ((j : ℝ) + 1) ^ 2 := by
          rw [Finset.sum_image hinj]
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' := (Finset.mem_filter.mp hk).2
          have hcast : ((φ k : ℕ) : ℝ) + 1 = (k : ℝ) - n := by
            dsimp [φ]
            have h2 : (k - n - 1 + 1 : ℕ) + n = k := by omega
            have h2' : ((k - n - 1 + 1 : ℕ) : ℝ) + (n : ℝ) = (k : ℝ) := by exact_mod_cast h2
            push_cast at h2' ⊢; linarith
          rw [hcast, show ((n : ℝ) - k) ^ 2 = ((k : ℝ) - n) ^ 2 by ring]
        rw [him]
        exact hZ2.sum_le_tsum _ fun _ _ => by positivity
      have h_lo : ∑ k ∈ S2.filter (fun k => k < n), 1 / ((n : ℝ) - k) ^ 2 ≤ Z2 := by
        let ψ : ℕ → ℕ := fun k => n - k - 1
        have hinj : Set.InjOn ψ (S2.filter (fun k => k < n)) := fun a ha b hb h => by
          have ha' := (Finset.mem_filter.mp ha).2
          have hb' := (Finset.mem_filter.mp hb).2
          dsimp [ψ] at h; omega
        have him : ∑ k ∈ S2.filter (fun k => k < n), 1 / ((n : ℝ) - k) ^ 2 =
            ∑ j ∈ (S2.filter (fun k => k < n)).image ψ, 1 / ((j : ℝ) + 1) ^ 2 := by
          rw [Finset.sum_image hinj]
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk' := (Finset.mem_filter.mp hk).2
          have hcast : ((ψ k : ℕ) : ℝ) + 1 = (n : ℝ) - k := by
            dsimp [ψ]
            have h2 : (n - k - 1 + 1 : ℕ) + k = n := by omega
            have h2' : ((n - k - 1 + 1 : ℕ) : ℝ) + (k : ℝ) = (n : ℝ) := by exact_mod_cast h2
            push_cast at h2' ⊢; linarith
          rw [hcast]
        rw [him]
        exact hZ2.sum_le_tsum _ fun _ _ => by positivity
      have hsum_s2 : ∑ k ∈ S2, (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) / ((n : ℝ) - k) ^ 2 =
          (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) * ∑ k ∈ S2, 1 / ((n : ℝ) - k) ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
      rw [hsum_s2, hsplit, Finset.sum_union hdisj]
      have hcoef : 0 ≤ C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2 := by dsimp [c_mid]; positivity
      calc (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) *
            (∑ k ∈ S2.filter (fun k => n < k), 1 / ((n : ℝ) - k) ^ 2 +
              ∑ k ∈ S2.filter (fun k => k < n), 1 / ((n : ℝ) - k) ^ 2)
          ≤ (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) * (Z2 + Z2) :=
            mul_le_mul_of_nonneg_left (add_le_add h_hi h_lo) hcoef
        _ = 2 * (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) * Z2 := by ring
    dsimp [B_mid]
    have hsum_rewrite : ∑ k ∈ S2, ((2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) / (n : ℝ) +
          (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) / ((n : ℝ) - k) ^ 2) =
        ∑ k ∈ S2, (2 * C_Z * (2 : ℝ) ^ (4 / 3 : ℝ) / c_mid) / (n : ℝ) +
        ∑ k ∈ S2, (C_sq * (2 : ℝ) ^ (2 / 3 : ℝ) / c_mid ^ 2) / ((n : ℝ) - k) ^ 2 :=
      Finset.sum_add_distrib
    linarith [h2, hsum_rewrite]
  -- Bound S3: 2*n < k
  have hS3_bd : ∑ k ∈ S3, term k ≤ B_right := by
    have h1 : ∀ k ∈ S3, term k ≤ (2 * C_Z / (9 / 10 : ℝ) + C_sq / (9 / 10 : ℝ) ^ 2) / (k : ℝ) ^ 2 := by
      intro k hk
      have hm := Finset.mem_filter.mp hk
      have hk2 : 2 ≤ k := hSk_ge2 k hm.1
      have h2nk : 2 * n < k := hm.2
      have hkn : k ≠ n := by omega
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hsep := airyZero_abs_sub_ge (by omega : 1 ≤ k) (by omega : 1 ≤ n) hkn
      have hmax : max n k = k := max_eq_right (by omega)
      rw [hmax] at hsep
      have hdiff : (k : ℝ) / 2 ≤ |(n : ℝ) - k| := by
        have : (2 * n : ℝ) < k := by exact_mod_cast h2nk
        rw [abs_of_neg (by linarith)]
        linarith
      have h_lb : (9 / 10 : ℝ) * (k : ℝ) ^ (2 / 3 : ℝ) ≤ |airyZero n - airyZero k| := by
        have hk13 : 0 < (k : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
        have h1' : (9 / 10 : ℝ) * (k : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤
            (9 / 5 : ℝ) * |(n : ℝ) - k| * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by nlinarith
        have h2' : (k : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) = (k : ℝ) ^ (2 / 3 : ℝ) := by
          conv_lhs => arg 1; rw [← Real.rpow_one (k : ℝ)]
          rw [← Real.rpow_add hk_pos]; norm_num
        rw [mul_assoc, h2'] at h1'
        linarith
      have h_lb_sq : (9 / 10 : ℝ) ^ 2 * (k : ℝ) ^ (4 / 3 : ℝ) ≤ (airyZero n - airyZero k) ^ 2 := by
        have hsq := pow_le_pow_left₀ (by positivity) h_lb 2
        rw [mul_pow, ← Real.rpow_natCast ((k : ℝ) ^ (2 / 3 : ℝ)) 2, ← Real.rpow_mul hk_pos.le,
          show (2 / 3 : ℝ) * ((2 : ℕ) : ℝ) = 4 / 3 by norm_num, sq_abs] at hsq
        exact hsq
      have ht_eq : term k = 2 * |airyZero k - uSite k| / |airyZero n - airyZero k| +
          (|airyZero k - uSite k| ^ 2 + (epsU k) ^ 2) / (airyZero n - airyZero k) ^ 2 := by
        simp [term, hkn]
      rw [ht_eq]
      have hk_m2_a : (k : ℝ) ^ (-(4 / 3 : ℝ)) / (k : ℝ) ^ (2 / 3 : ℝ) = 1 / (k : ℝ) ^ 2 := by
        rw [← Real.rpow_sub hk_pos, show -(4 / 3 : ℝ) - 2 / 3 = -(2 : ℕ) by norm_num,
          Real.rpow_neg hk_pos.le, Real.rpow_natCast, one_div]
      have hk_m2_b : (k : ℝ) ^ (-(2 / 3 : ℝ)) / (k : ℝ) ^ (4 / 3 : ℝ) = 1 / (k : ℝ) ^ 2 := by
        rw [← Real.rpow_sub hk_pos, show -(2 / 3 : ℝ) - 4 / 3 = -(2 : ℕ) by norm_num,
          Real.rpow_neg hk_pos.le, Real.rpow_natCast, one_div]
      have ha : 2 * |airyZero k - uSite k| / |airyZero n - airyZero k| ≤
          (2 * C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2 := by
        calc 2 * |airyZero k - uSite k| / |airyZero n - airyZero k|
            ≤ 2 * (C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ))) / ((9 / 10 : ℝ) * (k : ℝ) ^ (2 / 3 : ℝ)) := by
              gcongr; exact h_site_le k (by omega)
          _ = (2 * C_Z / (9 / 10 : ℝ)) * ((k : ℝ) ^ (-(4 / 3 : ℝ)) / (k : ℝ) ^ (2 / 3 : ℝ)) := by ring
          _ = (2 * C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2 := by rw [hk_m2_a]; ring
      have hb : (|airyZero k - uSite k| ^ 2 + (epsU k) ^ 2) /
          (airyZero n - airyZero k) ^ 2 ≤ (C_sq / (9 / 10 : ℝ) ^ 2) / (k : ℝ) ^ 2 := by
        calc (|airyZero k - uSite k| ^ 2 + (epsU k) ^ 2) / (airyZero n - airyZero k) ^ 2
            ≤ (C_sq * (k : ℝ) ^ (-(2 / 3 : ℝ))) / ((9 / 10 : ℝ) ^ 2 * (k : ℝ) ^ (4 / 3 : ℝ)) := by
              gcongr; exact h_sq_le k (by omega)
          _ = (C_sq / (9 / 10 : ℝ) ^ 2) * ((k : ℝ) ^ (-(2 / 3 : ℝ)) / (k : ℝ) ^ (4 / 3 : ℝ)) := by ring
          _ = (C_sq / (9 / 10 : ℝ) ^ 2) / (k : ℝ) ^ 2 := by rw [hk_m2_b]; ring
      exact (add_le_add ha hb).trans_eq (by ring)
    have h2 := Finset.sum_le_sum h1
    let φ : ℕ → ℕ := fun k => k - 1
    have hinj : Set.InjOn φ S3 := fun a ha b hb h => by
      have ha2 := hSk_ge2 a (Finset.mem_filter.mp ha).1
      have hb2 := hSk_ge2 b (Finset.mem_filter.mp hb).1
      dsimp [φ] at h; omega
    have him : ∑ k ∈ S3, 1 / (k : ℝ) ^ 2 = ∑ j ∈ S3.image φ, 1 / ((j : ℝ) + 1) ^ 2 := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk2 := hSk_ge2 k (Finset.mem_filter.mp hk).1
      dsimp [φ]
      have hcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by exact_mod_cast (by omega : k - 1 + 1 = k)
      rw [hcast]
    have hsum_z2 : ∑ k ∈ S3, 1 / (k : ℝ) ^ 2 ≤ Z2 := by
      rw [him]; exact hZ2.sum_le_tsum _ fun _ _ => by positivity
    have hmul : ∑ k ∈ S3, (2 * C_Z / (9 / 10 : ℝ) + C_sq / (9 / 10 : ℝ) ^ 2) / (k : ℝ) ^ 2 =
        (2 * C_Z / (9 / 10 : ℝ) + C_sq / (9 / 10 : ℝ) ^ 2) * ∑ k ∈ S3, 1 / (k : ℝ) ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
    rw [hmul] at h2
    have hcoef_nn : 0 ≤ 2 * C_Z / (9 / 10 : ℝ) + C_sq / (9 / 10 : ℝ) ^ 2 := by positivity
    exact h2.trans (mul_le_mul_of_nonneg_left hsum_z2 hcoef_nn)
  exact h_part.trans (add_le_add (add_le_add hS1_bd hS2_bd) hS3_bd)

end FormalResearch.ModularBootstrap.Upper.Ramped
