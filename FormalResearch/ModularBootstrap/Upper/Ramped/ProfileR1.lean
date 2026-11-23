module

public import FormalResearch.ModularBootstrap.Upper.Ramped.ProfileProdBound

/-!
# Lemma E (iv) for profiles: `1/2 ≤ R_1 ≤ C` (`ut:E`, `rem:profile`)

`prof_R1_bounds`: for a profile whose sites are the Airy zeros `a_k` for `2 ≤ k ≤ N` and satisfy
`|a_k - u_k| ≤ C_Z k^{-4/3}` beyond, with `ε_k² ≤ C_ε² k^{-2/3}`, one has `R_1 ≥ 1/2` as soon as
`N ≥ N₀(C_Z)` and `R_1 ≤ exp(C_{R,ub} Z₂)` with an explicit constant depending on `(C_Z, C_ε)` only.
The factors with `k ≤ N` are `≥ 1`; those with `k > N` are `≥ (1 - C k^{-2})²` and the product of the
latter is `≥ 1/2` for `N` large.  The proof is that of `designR1_bounds_aux`
(`Window/Quadrature.lean`) with the profile explicit.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window

/-- **Lemma E (iv) for profiles.** -/
lemma prof_R1_bounds (C_Z C_eps : ℝ) (hC_Z : 0 < C_Z)
    (N₁ N₂ : ℕ) (hN₁ : 4 * (C_Z / (9 / 10 : ℝ)) / Real.log 2 < (N₁ : ℝ))
    (hN₂ : √(2 * (C_Z / (9 / 10 : ℝ))) < (N₂ : ℝ))
    (uSite epsU : ℕ → ℝ) (hH : AiryProdTailHypothesis 1 uSite epsU)
    (N : ℕ) (hN_1 : 1 ≤ N) (hN_N1 : N₁ ≤ N) (hN_N2 : N₂ ≤ N)
    (hexact : ∀ k : ℕ, 2 ≤ k → k ≤ N → uSite k = airyZero k)
    (hsite : ∀ k : ℕ, 2 ≤ k → |airyZero k - uSite k| ≤ C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ)))
    (hwidth : ∀ k : ℕ, 2 ≤ k → (epsU k) ^ 2 ≤ C_eps ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)))
    (h_a1_sep : ∀ n : ℕ, 2 ≤ n → (9 / 10 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) ≤ |airyZero n - airyZero 1|) :
    1 / 2 ≤ profR1 uSite epsU ∧
      profR1 uSite epsU ≤ Real.exp ((2 * (C_Z / (9 / 10 : ℝ)) + (C_Z ^ 2 + C_eps ^ 2) / (9 / 10 : ℝ) ^ 2) *
        ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2) := by
  have hp := (profR1_hasProd uSite epsU hH).1
  have hZ2 : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using this
  have hR1_lb : 1 / 2 ≤ profR1 uSite epsU := by
    refine ge_of_tendsto hp (Eventually.of_forall fun s => ?_)
    have h_fac_lb : ∀ m : ℕ,
        (if m + 2 ≤ N then (1 : ℝ) else Real.exp (-4 * (C_Z / (9 / 10 : ℝ)) / ((m + 2 : ℕ) : ℝ) ^ 2)) ≤
          profRealFactor uSite epsU 1 (m + 2) := by
      intro m
      set k := m + 2
      have hk2 : 2 ≤ k := by omega
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      unfold profRealFactor
      split_ifs with hkN
      · have hs : uSite k = airyZero k := hexact k hk2 hkN
        rw [hs]
        have hne : (airyZero 1 - airyZero k) ^ 2 > 0 := sq_pos_of_pos (by
          linarith [airyZero_lt_of_lt le_rfl (by omega : 1 < k)])
        rw [one_le_div hne]
        linarith [sq_nonneg (epsU k)]
      · have hsep := h_a1_sep k hk2
        rw [abs_sub_comm] at hsep
        have hδk : |airyZero k - uSite k| ≤ C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ)) := hsite k hk2
        have h_ratio : |airyZero k - uSite k| / |airyZero 1 - airyZero k| ≤
            (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2 := by
          have hk_rpow : (k : ℝ) ^ (-(4 / 3 : ℝ)) / (k : ℝ) ^ (2 / 3 : ℝ) = 1 / (k : ℝ) ^ 2 := by
            rw [← Real.rpow_sub hk_pos, show -(4 / 3 : ℝ) - 2 / 3 = -(2 : ℕ) by norm_num,
              Real.rpow_neg hk_pos.le, Real.rpow_natCast, one_div]
          calc |airyZero k - uSite k| / |airyZero 1 - airyZero k|
              ≤ (C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ))) / ((9 / 10 : ℝ) * (k : ℝ) ^ (2 / 3 : ℝ)) := by gcongr
            _ = (C_Z / (9 / 10 : ℝ)) * ((k : ℝ) ^ (-(4 / 3 : ℝ)) / (k : ℝ) ^ (2 / 3 : ℝ)) := by ring
            _ = (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2 := by rw [hk_rpow]; ring
        have hk_gt_N : N < k := by omega
        have hN2_lt : (N₂ : ℝ) < k := by
          have h2 : (N₂ : ℝ) ≤ N := by exact_mod_cast hN_N2
          have h3 : (N : ℝ) < k := by exact_mod_cast hk_gt_N
          linarith
        have h_t_le : (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2 ≤ 1 / 2 := by
          have hsq : 2 * (C_Z / (9 / 10 : ℝ)) < (k : ℝ) ^ 2 := by
            have h1 : √(2 * (C_Z / (9 / 10 : ℝ))) < k := lt_trans hN₂ hN2_lt
            have h2 := pow_lt_pow_left₀ h1 (Real.sqrt_nonneg _) two_ne_zero
            rwa [Real.sq_sqrt (by positivity)] at h2
          rw [div_le_iff₀ (sq_pos_of_pos hk_pos)]
          linarith
        have hexp1 := exp_neg_two_mul_le_one_sub (t := (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2) (by positivity) h_t_le
        have h_base : 1 - (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2 ≤
            |airyZero 1 - uSite k| / |airyZero 1 - airyZero k| := by
          have htri : |airyZero 1 - airyZero k| ≤ |airyZero 1 - uSite k| + |airyZero k - uSite k| := by
            rw [abs_sub_comm (airyZero k) (uSite k)]
            simpa [sub_add_sub_cancel] using abs_sub_le (airyZero 1) (uSite k) (airyZero k)
          have h_abs_pos : 0 < |airyZero 1 - airyZero k| := lt_of_lt_of_le (by positivity) hsep
          rw [le_div_iff₀ h_abs_pos]
          calc (1 - (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2) * |airyZero 1 - airyZero k|
              ≤ (1 - |airyZero k - uSite k| / |airyZero 1 - airyZero k|) * |airyZero 1 - airyZero k| := by gcongr
            _ = |airyZero 1 - airyZero k| - |airyZero k - uSite k| := by
                rw [sub_mul, one_mul, div_mul_cancel₀ _ h_abs_pos.ne']
            _ ≤ |airyZero 1 - uSite k| := by linarith
        have h_sq_ge : (1 - (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2) ^ 2 ≤
            (airyZero 1 - uSite k) ^ 2 / (airyZero 1 - airyZero k) ^ 2 := by
          have hexp_nn : 0 ≤ 1 - (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2 := by linarith
          have hsq := pow_le_pow_left₀ hexp_nn h_base 2
          rwa [div_pow, sq_abs, sq_abs] at hsq
        have hexp2 : Real.exp (-4 * (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2) =
            (Real.exp (-2 * ((C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2))) ^ 2 := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        have hexp_sq : Real.exp (-4 * (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2) ≤
            (1 - (C_Z / (9 / 10 : ℝ)) / (k : ℝ) ^ 2) ^ 2 := by
          rw [hexp2]
          exact pow_le_pow_left₀ (Real.exp_pos _).le hexp1 2
        have h_ge_fac : (airyZero 1 - uSite k) ^ 2 / (airyZero 1 - airyZero k) ^ 2 ≤
            ((airyZero 1 - uSite k) ^ 2 + (epsU k) ^ 2) / (airyZero 1 - airyZero k) ^ 2 := by
          gcongr; linarith [sq_nonneg (epsU k)]
        exact hexp_sq.trans (h_sq_ge.trans h_ge_fac)
    have h_prod_ge : ∏ m ∈ s, (if m + 2 ≤ N then (1 : ℝ)
          else Real.exp (-4 * (C_Z / (9 / 10 : ℝ)) / ((m + 2 : ℕ) : ℝ) ^ 2)) ≤
        ∏ m ∈ s, profRealFactor uSite epsU 1 (m + 2) :=
      Finset.prod_le_prod₀ (fun m _ => by split_ifs; exact zero_le_one; exact (Real.exp_pos _).le)
        (fun m _ => h_fac_lb m)
    have h_exp_prod : ∏ m ∈ s, (if m + 2 ≤ N then (1 : ℝ)
          else Real.exp (-4 * (C_Z / (9 / 10 : ℝ)) / ((m + 2 : ℕ) : ℝ) ^ 2)) =
        Real.exp (∑ m ∈ s, if m + 2 ≤ N then 0 else -4 * (C_Z / (9 / 10 : ℝ)) / ((m + 2 : ℕ) : ℝ) ^ 2) := by
      rw [Real.exp_sum]
      refine Finset.prod_congr rfl fun m _ => by split_ifs <;> simp
    rw [h_exp_prod] at h_prod_ge
    have h_sum_ge : -Real.log 2 ≤
        ∑ m ∈ s, if m + 2 ≤ N then 0 else -4 * (C_Z / (9 / 10 : ℝ)) / ((m + 2 : ℕ) : ℝ) ^ 2 := by
      set s' := s.filter (fun m => ¬(m + 2 ≤ N))
      have h_flip : (∑ m ∈ s, if m + 2 ≤ N then (0 : ℝ)
            else -4 * (C_Z / (9 / 10 : ℝ)) / ((m + 2 : ℕ) : ℝ) ^ 2) =
          ∑ m ∈ s, if ¬(m + 2 ≤ N) then -4 * (C_Z / (9 / 10 : ℝ)) / ((m + 2 : ℕ) : ℝ) ^ 2 else 0 :=
        Finset.sum_congr rfl fun m _ => by split_ifs <;> rfl
      have hs'_eq : (∑ m ∈ s, if m + 2 ≤ N then (0 : ℝ)
            else -4 * (C_Z / (9 / 10 : ℝ)) / ((m + 2 : ℕ) : ℝ) ^ 2) =
          -(4 * (C_Z / (9 / 10 : ℝ))) * ∑ m ∈ s', 1 / ((m + 2 : ℕ) : ℝ) ^ 2 := by
        rw [h_flip, ← Finset.sum_filter, Finset.mul_sum]
        dsimp [s']
        refine Finset.sum_congr rfl fun m _ => by ring
      rw [hs'_eq]
      let φ : ℕ → ℕ := fun m => m + 2 - (N + 1)
      have hinj : Set.InjOn φ s' := fun a ha b hb h => by
        have ha' := (Finset.mem_filter.mp ha).2
        have hb' := (Finset.mem_filter.mp hb).2
        dsimp [φ] at h; omega
      have him : ∑ m ∈ s', 1 / ((m + 2 : ℕ) : ℝ) ^ 2 =
          ∑ j ∈ s'.image φ, 1 / ((N + 1 + j : ℕ) : ℝ) ^ 2 := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hm' := (Finset.mem_filter.mp hm).2
        have hcast : ((N + 1 + φ m : ℕ) : ℝ) = ((m + 2 : ℕ) : ℝ) := by
          dsimp [φ]; exact_mod_cast (by omega : N + 1 + (m + 2 - (N + 1)) = m + 2)
        rw [hcast]
      have hsum_tail : Summable (fun j : ℕ => 1 / ((N + 1 + j : ℕ) : ℝ) ^ 2) := by
        have h1 := (summable_nat_add_iff (N + 1)).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
        exact h1.congr fun j => by rw [Nat.add_comm j (N + 1)]
      have h_sum_le : ∑ m ∈ s', 1 / ((m + 2 : ℕ) : ℝ) ^ 2 ≤ 1 / (N : ℝ) := by
        rw [him]
        exact (hsum_tail.sum_le_tsum _ fun _ _ => by positivity).trans (one_div_sq_sum_tail_le N hN_1)
      have hN1_lt : 4 * (C_Z / (9 / 10 : ℝ)) / Real.log 2 < (N : ℝ) := by
        have h2 : (N₁ : ℝ) ≤ N := by exact_mod_cast hN_N1
        linarith
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN_1
      have h4CR : 4 * (C_Z / (9 / 10 : ℝ)) / (N : ℝ) ≤ Real.log 2 := by
        rw [div_le_iff₀ hN_pos]
        rw [div_lt_iff₀ hlog2] at hN1_lt
        linarith
      calc -Real.log 2 ≤ -(4 * (C_Z / (9 / 10 : ℝ)) / (N : ℝ)) := by linarith
        _ = -(4 * (C_Z / (9 / 10 : ℝ))) * (1 / (N : ℝ)) := by ring
        _ ≤ -(4 * (C_Z / (9 / 10 : ℝ))) * ∑ m ∈ s', 1 / ((m + 2 : ℕ) : ℝ) ^ 2 :=
            mul_le_mul_of_nonpos_left h_sum_le (neg_nonpos.mpr (by positivity))
    have hexp_half : 1 / 2 ≤ Real.exp (-Real.log 2) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    exact hexp_half.trans ((Real.exp_le_exp.mpr h_sum_ge).trans h_prod_ge)
  have hR1_ub : profR1 uSite epsU ≤
      Real.exp ((2 * (C_Z / (9 / 10 : ℝ)) + (C_Z ^ 2 + C_eps ^ 2) / (9 / 10 : ℝ) ^ 2) *
        ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2) := by
    refine le_of_tendsto hp (Eventually.of_forall fun s => ?_)
    set C_sq := C_Z ^ 2 + C_eps ^ 2
    set C_R := C_Z / (9 / 10 : ℝ)
    set C_R_ub := 2 * C_R + C_sq / (9 / 10 : ℝ) ^ 2
    have h_fac_ub : ∀ m : ℕ, profRealFactor uSite epsU 1 (m + 2) ≤
        Real.exp (C_R_ub / ((m + 1 : ℕ) : ℝ) ^ 2) := by
      intro m
      set k := m + 2
      have hk2 : 2 ≤ k := by omega
      have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hsep := h_a1_sep k hk2
      rw [abs_sub_comm] at hsep
      have h_site_k : |airyZero k - uSite k| ≤ C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ)) := hsite k hk2
      have h_width_k : (epsU k) ^ 2 ≤ C_eps ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) := hwidth k hk2
      have h_sq_k : |airyZero k - uSite k| ^ 2 + (epsU k) ^ 2 ≤
          C_sq * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
        have h1 := pow_le_pow_left₀ (abs_nonneg _) h_site_k 2
        rw [mul_pow, ← Real.rpow_natCast ((k : ℝ) ^ (-(4 / 3 : ℝ))) 2, ← Real.rpow_mul hk_pos.le,
          show -(4 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(8 / 3 : ℝ) by norm_num] at h1
        have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
        have h1' : |airyZero k - uSite k| ^ 2 ≤ C_Z ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) :=
          h1.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hk1' (by norm_num)) (by positivity))
        dsimp [C_sq]; linarith
      have hk_m2_a : (k : ℝ) ^ (-(4 / 3 : ℝ)) / (k : ℝ) ^ (2 / 3 : ℝ) = 1 / (k : ℝ) ^ 2 := by
        rw [← Real.rpow_sub hk_pos, show -(4 / 3 : ℝ) - 2 / 3 = -(2 : ℕ) by norm_num,
          Real.rpow_neg hk_pos.le, Real.rpow_natCast, one_div]
      have hk_m2_b : (k : ℝ) ^ (-(2 / 3 : ℝ)) / (k : ℝ) ^ (4 / 3 : ℝ) = 1 / (k : ℝ) ^ 2 := by
        rw [← Real.rpow_sub hk_pos, show -(2 / 3 : ℝ) - 4 / 3 = -(2 : ℕ) by norm_num,
          Real.rpow_neg hk_pos.le, Real.rpow_natCast, one_div]
      have h_lb_sq : (9 / 10 : ℝ) ^ 2 * (k : ℝ) ^ (4 / 3 : ℝ) ≤ (airyZero 1 - airyZero k) ^ 2 := by
        have hsq := pow_le_pow_left₀ (by positivity) hsep 2
        rw [mul_pow, ← Real.rpow_natCast ((k : ℝ) ^ (2 / 3 : ℝ)) 2, ← Real.rpow_mul hk_pos.le,
          show (2 / 3 : ℝ) * ((2 : ℕ) : ℝ) = 4 / 3 by norm_num, sq_abs] at hsq
        exact hsq
      have hne : airyZero 1 - airyZero k ≠ 0 := fun h0 =>
        (lt_of_lt_of_le (by positivity) hsep).ne' (abs_eq_zero.mpr h0)
      unfold profRealFactor
      have h_decomp : ((airyZero 1 - uSite k) ^ 2 + (epsU k) ^ 2) /
          (airyZero 1 - airyZero k) ^ 2 =
          1 + (2 * (airyZero 1 - airyZero k) * (airyZero k - uSite k) +
            ((airyZero k - uSite k) ^ 2 + (epsU k) ^ 2)) /
            (airyZero 1 - airyZero k) ^ 2 := by
        field_simp [hne]; ring
      rw [h_decomp]
      have hcross : 2 * (airyZero 1 - airyZero k) * (airyZero k - uSite k) /
          (airyZero 1 - airyZero k) ^ 2 ≤ 2 * C_R / (k : ℝ) ^ 2 := by
        have h_simp : 2 * (airyZero 1 - airyZero k) * (airyZero k - uSite k) /
            (airyZero 1 - airyZero k) ^ 2 =
            2 * (airyZero k - uSite k) / (airyZero 1 - airyZero k) := by
          field_simp [hne]
        rw [h_simp]
        refine (le_abs_self _).trans ?_
        rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        calc 2 * |airyZero k - uSite k| / |airyZero 1 - airyZero k|
            ≤ 2 * (C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ))) / ((9 / 10 : ℝ) * (k : ℝ) ^ (2 / 3 : ℝ)) := by gcongr
          _ = 2 * C_R * ((k : ℝ) ^ (-(4 / 3 : ℝ)) / (k : ℝ) ^ (2 / 3 : ℝ)) := by dsimp [C_R]; ring
          _ = 2 * C_R / (k : ℝ) ^ 2 := by rw [hk_m2_a]; ring
      have hsqterm : ((airyZero k - uSite k) ^ 2 + (epsU k) ^ 2) /
          (airyZero 1 - airyZero k) ^ 2 ≤ (C_sq / (9 / 10 : ℝ) ^ 2) / (k : ℝ) ^ 2 := by
        have h_num' : (airyZero k - uSite k) ^ 2 + (epsU k) ^ 2 ≤
            C_sq * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
          rw [← sq_abs (airyZero k - uSite k)]; exact h_sq_k
        calc ((airyZero k - uSite k) ^ 2 + (epsU k) ^ 2) / (airyZero 1 - airyZero k) ^ 2
            ≤ (C_sq * (k : ℝ) ^ (-(2 / 3 : ℝ))) / ((9 / 10 : ℝ) ^ 2 * (k : ℝ) ^ (4 / 3 : ℝ)) := by gcongr
          _ = (C_sq / (9 / 10 : ℝ) ^ 2) * ((k : ℝ) ^ (-(2 / 3 : ℝ)) / (k : ℝ) ^ (4 / 3 : ℝ)) := by ring
          _ = (C_sq / (9 / 10 : ℝ) ^ 2) / (k : ℝ) ^ 2 := by rw [hk_m2_b]; ring
      have hk_m1_le : ((m + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : m + 1 ≤ k)
      have hk2_le : ((m + 1 : ℕ) : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hk_m1_le 2
      have h_1div : C_R_ub / (k : ℝ) ^ 2 ≤ C_R_ub / ((m + 1 : ℕ) : ℝ) ^ 2 := by
        have : 0 ≤ C_R_ub := by dsimp [C_R_ub, C_R]; positivity
        gcongr
      have h_crub_eq : 2 * C_R / (k : ℝ) ^ 2 + (C_sq / (9 / 10 : ℝ) ^ 2) / (k : ℝ) ^ 2 =
          C_R_ub / (k : ℝ) ^ 2 := by dsimp [C_R_ub]; ring
      have hsum1 : 1 + (2 * (airyZero 1 - airyZero k) * (airyZero k - uSite k) +
          ((airyZero k - uSite k) ^ 2 + (epsU k) ^ 2)) / (airyZero 1 - airyZero k) ^ 2 ≤
          1 + C_R_ub / ((m + 1 : ℕ) : ℝ) ^ 2 := by
        rw [add_div]
        linarith
      exact hsum1.trans (by rw [add_comm 1 _]; exact Real.add_one_le_exp _)
    calc ∏ m ∈ s, profRealFactor uSite epsU 1 (m + 2)
        ≤ ∏ m ∈ s, Real.exp (C_R_ub / ((m + 1 : ℕ) : ℝ) ^ 2) :=
          Finset.prod_le_prod₀ (fun _ _ => by unfold profRealFactor; positivity) (fun m _ => h_fac_ub m)
      _ = Real.exp (∑ m ∈ s, C_R_ub / ((m + 1 : ℕ) : ℝ) ^ 2) := (Real.exp_sum s _).symm
      _ ≤ Real.exp (C_R_ub * ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2) := by
          refine Real.exp_le_exp.mpr ?_
          have h1 : ∑ m ∈ s, C_R_ub / ((m + 1 : ℕ) : ℝ) ^ 2 =
              C_R_ub * ∑ m ∈ s, 1 / ((m : ℝ) + 1) ^ 2 := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => by push_cast; ring
          rw [h1]
          exact mul_le_mul_of_nonneg_left (hZ2.sum_le_tsum _ fun _ _ => by positivity) (by positivity)
  exact ⟨hR1_lb, hR1_ub⟩

end FormalResearch.ModularBootstrap.Upper.Ramped
