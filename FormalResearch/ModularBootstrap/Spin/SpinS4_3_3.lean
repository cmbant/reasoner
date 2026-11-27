/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_3_3_Cap

/-!
# Section 3.1 (`s4:3.3`): Fixed Airy-Window Tightness of the Negative Weighted Mass

This module proves `SpinS4_3_3` (`spinning_s4.tex`, Theorem 3.3 / `s4:3.3`):
for every fixed `C_x > 0`, there exist constants `C, c_exp, R₀ > 0` such that for all `R ≥ R₀`
and all sufficiently large `n' = c - 1` (after fixing `R`), the negative weighted mass inside
`b_△ ≤ ξ_* - R ε` inside the gap disc is at most `C exp(-c_exp R^{3/2})`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

/-- **`s4:3.3` (`spinning_s4.tex`, Theorem 3.3): fixed Airy-window tightness of the
negative weighted mass.** -/
theorem spinS4_3_3 : SpinS4_3_3 := by
  intro C_x hCx
  obtain ⟨_k, C_22b, κ, δ₀, n₀, _hk0, hC22_pos, hκ_pos, hδ₀_pos, hn₀, hS22b_main⟩ := spinS22b
  obtain ⟨K_1, C_1, c₀₁, hK1_pos, hC1_pos, hc01, h21_all⟩ :=
    spinS4_2_1_all_quads (C_x := C_x) (p := 1) (by norm_num)
  let c_22 : ℝ := κ * (2 : ℝ) ^ (-(5 / 2 : ℝ))
  let c_exp : ℝ := min (π * xiStar) (c_22 / 2)
  have hcexp_pos : 0 < c_exp := by
    have := xiStar_pos; have := Real.pi_pos; positivity
  let C_cap : ℝ := 4 * (2 * C_22b * (2 * xiStar + C_22b) * (2 / κ)) * (4 / c_exp ^ 2)
  let C : ℝ := 4 * (1 + 3 + C_cap) + 1
  refine ⟨C, c_exp, 2, by positivity, hcexp_pos, by norm_num, ?_⟩
  intro R hR
  let N : ℕ := Nat.ceil (R ^ (3 / 2 : ℝ))
  have hR_pos : 0 < R := by linarith
  have hR32_ge1 : 1 ≤ R ^ (3 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hN_ge : R ^ (3 / 2 : ℝ) ≤ (N : ℝ) := Nat.le_ceil _
  have hN_le : (N : ℝ) ≤ 2 * R ^ (3 / 2 : ℝ) := by
    have hlt := Nat.ceil_lt_add_one (le_trans zero_le_one hR32_ge1)
    linarith
  have hN_pos : 1 ≤ N := Nat.ceil_pos.mpr (by positivity)
  have ht_delta : Tendsto (fun n' : ℝ => K_1 * n' ^ (-(2 / 3 : ℝ)) * Real.log n') atTop (𝓝 0) := by
    have ht0 : Tendsto (fun n' : ℝ => Real.log n' / n' ^ (2 / 3 : ℝ)) atTop (𝓝 0) :=
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).tendsto_div_nhds_zero
    have hrew : (fun n' : ℝ => K_1 * n' ^ (-(2 / 3 : ℝ)) * Real.log n') =ᶠ[atTop]
        fun n' => K_1 * (Real.log n' / n' ^ (2 / 3 : ℝ)) := by
      filter_upwards [eventually_gt_atTop 0] with n' hn'
      rw [Real.rpow_neg hn'.le, div_eq_mul_inv]; ring
    exact (ht0.const_mul K_1).congr' (by simpa using hrew.symm) |>.trans (by simp)
  have ht_Cx : Tendsto (fun n' : ℝ => C_x * n' ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul C_x
  have ht_inv_eps : Tendsto (fun n' : ℝ => (96 * (N : ℝ) * xiStar + 24 * xiStar) * n' ^ (-(1 / 3 : ℝ)))
      atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul
      (96 * (N : ℝ) * xiStar + 24 * xiStar)
  have ht_inv : Tendsto (fun n' : ℝ => 16 * C_1 * n' ^ (-1 : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).const_mul (16 * C_1)
  have hev_base : ∀ᶠ n' : ℝ in atTop,
      49 ≤ n' + 1 ∧ n₀ + 1 ≤ n' + 1 ∧ c₀₁ ≤ n' + 1 ∧ 768 * (N : ℝ) ≤ n' :=
    (eventually_ge_atTop (max (max 48 n₀) (max (c₀₁ - 1) (768 * (N : ℝ))))).mono fun n' hn' => by
      refine ⟨by linarith [le_max_left (48 : ℝ) n₀, le_max_left (max (48 : ℝ) n₀) (max (c₀₁ - 1) (768 * (N : ℝ)))],
        by linarith [le_max_right (48 : ℝ) n₀, le_max_left (max (48 : ℝ) n₀) (max (c₀₁ - 1) (768 * (N : ℝ)))],
        by linarith [le_max_left (c₀₁ - 1) (768 * (N : ℝ)), le_max_right (max (48 : ℝ) n₀) (max (c₀₁ - 1) (768 * (N : ℝ)))],
        by linarith [le_max_right (c₀₁ - 1) (768 * (N : ℝ)), le_max_right (max (48 : ℝ) n₀) (max (c₀₁ - 1) (768 * (N : ℝ)))]⟩
  have hev_δ : ∀ᶠ n' : ℝ in atTop,
      K_1 * n' ^ (-(2 / 3 : ℝ)) * Real.log n' < min (xiStar / 32) (δ₀ / 2) :=
    ht_delta.eventually (gt_mem_nhds (by have := xiStar_pos; positivity))
  have hev_Cx : ∀ᶠ n' : ℝ in atTop, C_x * n' ^ (-(2 / 3 : ℝ)) < xiStar / 32 :=
    ht_Cx.eventually (gt_mem_nhds (by have := xiStar_pos; positivity))
  have hev_ie : ∀ᶠ n' : ℝ in atTop,
      (96 * (N : ℝ) * xiStar + 24 * xiStar) * n' ^ (-(1 / 3 : ℝ)) < R / 4 :=
    ht_inv_eps.eventually (gt_mem_nhds (by positivity))
  have hev_exp : ∀ᶠ n' : ℝ in atTop,
      16 * C_1 * n' ^ (-1 : ℝ) < Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) :=
    ht_inv.eventually (gt_mem_nhds (Real.exp_pos _))
  filter_upwards [hev_base, hev_δ, hev_Cx, hev_ie, hev_exp] with n'
    ⟨hc49, hcn0, hcc01, hN_n⟩ hδ_lt hCx_lt hie_lt hexp_lt
  intro c ε a x₁ Φ hx₁_gap hslack
  obtain ⟨hx₁0, hΦ, hM2, _hvac, _hgap⟩ := hslack
  have hn_pos : 0 < n' := by linarith
  have ha2 : 2 < a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  have hε_pos : 0 < ε := Real.rpow_pos_of_pos hn_pos _
  have hε_eq : n' * ε ^ (3 / 2 : ℝ) = 1 := by
    dsimp [ε]
    rw [← Real.rpow_mul hn_pos.le, show -(2 / 3 : ℝ) * (3 / 2 : ℝ) = -1 by norm_num,
      Real.rpow_neg_one, mul_inv_cancel₀ hn_pos.ne']
  have hc_sub : c - 1 = n' := by dsimp [c]; ring
  have ha_eq : (c - 1) / 12 = a := by rw [hc_sub]
  rw [ha_eq] at hΦ hM2
  have hx₁_ub : x₁ ≤ xiStar + C_x * n' ^ (-(2 / 3 : ℝ)) := by linarith [(abs_le.mp hx₁_gap).2]
  have hG_int : Integrable (fun q : ℝ × ℝ => |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2) :=
    integrable_spinG_wc ha0 hΦ
  let E_all : Set (ℝ × ℝ) := {q : ℝ × ℝ | (q.1 + q.2) ^ 2 / 4 + (q.1 - q.2) ^ 2 / 4 < x₁ ^ 2 ∧
    spinLongDist q ≤ xiStar - ε * R}
  let E_pp : Set (ℝ × ℝ) := {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧
    (q.1 ^ 2 + q.2 ^ 2) / 2 < x₁ ^ 2 ∧ (q.1 + q.2) / 2 ≤ xiStar - ε * R}
  have hmE_all : MeasurableSet E_all := by
    have h1 : Continuous (fun q : ℝ × ℝ => (q.1 + q.2) ^ 2 / 4 + (q.1 - q.2) ^ 2 / 4) := by fun_prop
    have h2 : Continuous spinLongDist := by unfold spinLongDist; fun_prop
    exact (isOpen_lt h1 continuous_const).measurableSet.inter
      (isClosed_le h2 continuous_const).measurableSet
  have hmax_le_abs : ∫ p in E_all, max (-spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2 ≤
      ∫ p in E_all, |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 := by
    refine setIntegral_mono_on ?_ hG_int.integrableOn hmE_all fun p _ => ?_
    · refine hG_int.integrableOn.mono' ?_ (Eventually.of_forall fun p => ?_)
      · have hGm : Measurable (fun p : ℝ × ℝ => max (-spinG a Φ p.1 p.2) 0) :=
          ((hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk
            (continuous_const.mul continuous_snd))).neg.max continuous_const).measurable
        have hWc : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
        exact ((hGm.mul (hWc.comp continuous_fst).measurable).mul
          (hWc.comp continuous_snd).measurable).aestronglyMeasurable
      · have hw1 := spinWc_nonneg ha2.le p.1
        have hw2 := spinWc_nonneg ha2.le p.2
        have h1 : max (-spinG a Φ p.1 p.2) 0 ≤ |spinG a Φ p.1 p.2| := max_le (neg_le_abs _) (abs_nonneg _)
        rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (le_max_right _ _) hw1) hw2)]
        gcongr
    · have hw1 := spinWc_nonneg ha2.le p.1
      have hw2 := spinWc_nonneg ha2.le p.2
      have h1 : max (-spinG a Φ p.1 p.2) 0 ≤ |spinG a Φ p.1 p.2| := max_le (neg_le_abs _) (abs_nonneg _)
      gcongr
  let g : ℝ × ℝ → ℝ := fun q => |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2
  have hE_all_eq : ∫ q in E_all, g q = 4 * ∫ q in E_pp, g q :=
    spinS4_d4_four_quadrants ha2 hΦ
  let δ_n := ε * Real.log n'
  let E_far : Set (ℝ × ℝ) := {q ∈ E_pp | (q.1 + q.2) / 2 < xiStar - K_1 * δ_n}
  let E_cap : Set (ℝ × ℝ) := {q ∈ E_pp | xiStar - K_1 * δ_n ≤ (q.1 + q.2) / 2}
  have hm_pp : MeasurableSet E_pp :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      ((isOpen_lt continuous_const continuous_snd).measurableSet.inter
        ((isOpen_lt (((continuous_fst.pow 2).add (continuous_snd.pow 2)).div_const 2)
          continuous_const).measurableSet.inter
        (isClosed_le ((continuous_fst.add continuous_snd).div_const 2) continuous_const).measurableSet))
  have hm_far : MeasurableSet E_far := hm_pp.inter
    (isOpen_lt ((continuous_fst.add continuous_snd).div_const 2) continuous_const).measurableSet
  have hm_cap : MeasurableSet E_cap := hm_pp.inter
    (isClosed_le continuous_const ((continuous_fst.add continuous_snd).div_const 2)).measurableSet
  have hpp_split : ∫ q in E_pp, g q = (∫ q in E_far, g q) + ∫ q in E_cap, g q := by
    have hU : E_pp = E_far ∪ E_cap := by
      ext q; simp only [E_pp, E_far, E_cap, Set.mem_union, Set.mem_sep_iff]
      constructor
      · intro hq
        rcases lt_or_ge ((q.1 + q.2) / 2) (xiStar - K_1 * δ_n) with h | h
        · exact Or.inl ⟨hq, h⟩
        · exact Or.inr ⟨hq, h⟩
      · rintro (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
    have hd : Disjoint E_far E_cap := Set.disjoint_left.mpr fun q h1 h2 => not_le_of_gt h1.2 h2.2
    rw [hU, ← integral_indicator (hm_far.union hm_cap), ← integral_indicator hm_far,
      ← integral_indicator hm_cap, ← integral_add (hG_int.indicator hm_far) (hG_int.indicator hm_cap)]
    congr 1; ext q
    by_cases h1 : q ∈ E_far <;> by_cases h2 : q ∈ E_cap
    · exact absurd h2 (Set.disjoint_left.mp hd h1)
    · rw [Set.indicator_of_mem (Or.inl h1), Set.indicator_of_mem h1, Set.indicator_of_notMem h2, add_zero]
    · rw [Set.indicator_of_mem (Or.inr h2), Set.indicator_of_notMem h1, Set.indicator_of_mem h2, zero_add]
    · rw [Set.indicator_of_notMem (by rintro (h | h) <;> contradiction),
        Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, add_zero]
  have hfar_bd : ∫ q in E_far, g q ≤ 4 * C_1 * n' ^ (-1 : ℝ) := by
    have hsub : E_far ⊆ {q : ℝ × ℝ | (q.1 ^ 2 + q.2 ^ 2) / 2 < x₁ ^ 2 ∧
        spinLongDist q < xiStar - K_1 * n' ^ (-(2 / 3 : ℝ)) * Real.log n'} := by
      intro q hq
      have hp := hq.1
      refine ⟨hp.2.2.1, ?_⟩
      unfold spinLongDist; rw [abs_of_pos hp.1, abs_of_pos hp.2.1]
      linarith [hq.2, show K_1 * δ_n = K_1 * n' ^ (-(2 / 3 : ℝ)) * Real.log n' by dsimp [δ_n, ε]; ring]
    have hmono := setIntegral_mono_set hG_int.integrableOn
      (Eventually.of_forall fun q => mul_nonneg (mul_nonneg (abs_nonneg _)
        (spinWc_nonneg ha2.le _)) (spinWc_nonneg ha2.le _)) hsub.eventuallyLE
    have h21 := h21_all hcc01 hx₁0 hx₁_ub (by simpa [hc_sub, ha_eq] using hΦ)
      (by simpa [hc_sub, ha_eq] using hM2)
    refine hmono.trans ?_
    simpa [g, hc_sub, ha_eq] using h21
  have hKδ_lt : K_1 * δ_n < min (xiStar / 32) (δ₀ / 2) := by
    simpa [δ_n, ε, mul_assoc] using hδ_lt
  have hcap_geom : ∀ q ∈ E_cap, xiStar / 2 ≤ q.1 ∧ xiStar / 2 ≤ q.2 ∧
      q.1 ≤ 2 * xiStar ∧ q.2 ≤ 2 * xiStar ∧ |(q.1 - q.2) / 2| ≤ 3 * xiStar / 8 := by
    intro q ⟨⟨hq1, hq2, hq_rad, hq_sum⟩, hq_lb⟩
    have hxi_nn := xiStar_pos.le
    have h1 : x₁ < (33 / 32 : ℝ) * xiStar := by linarith
    have h2 : (31 / 32 : ℝ) * xiStar < (q.1 + q.2) / 2 := by
      linarith [hKδ_lt.trans_le (min_le_left _ _)]
    have hsq_diff : ((q.1 - q.2) / 2) ^ 2 < (3 * xiStar / 8) ^ 2 := by
      have h0 : ((q.1 + q.2) / 2) ^ 2 + ((q.1 - q.2) / 2) ^ 2 = (q.1 ^ 2 + q.2 ^ 2) / 2 := by ring
      have hrad : ((q.1 + q.2) / 2) ^ 2 + ((q.1 - q.2) / 2) ^ 2 < x₁ ^ 2 := by linarith
      have hx1_sq : x₁ ^ 2 < ((33 / 32 : ℝ) * xiStar) ^ 2 :=
        pow_lt_pow_left₀ h1 hx₁0 (by norm_num)
      have hsum_sq : ((31 / 32 : ℝ) * xiStar) ^ 2 < ((q.1 + q.2) / 2) ^ 2 :=
        pow_lt_pow_left₀ h2 (by positivity) (by norm_num)
      nlinarith [sq_nonneg xiStar]
    have hd_abs : |(q.1 - q.2) / 2| < 3 * xiStar / 8 := by
      rw [← sq_abs ((q.1 - q.2) / 2)] at hsq_diff
      exact abs_lt.mpr ⟨by nlinarith [xiStar_pos], by nlinarith [xiStar_pos]⟩
    have hd_le := abs_lt.mp hd_abs
    have hq_sum_le : (q.1 + q.2) / 2 ≤ xiStar := by linarith [show 0 < ε * R by positivity]
    refine ⟨by linarith, by linarith, by linarith, by linarith, hd_abs.le⟩
  let r : ℝ := xiStar / 2
  have hr_pos : 0 < r := half_pos xiStar_pos
  have hcap_sub_r : E_cap ⊆ {q : ℝ × ℝ | r ≤ q.1 ∧ r ≤ q.2} := fun q hq =>
    ⟨(hcap_geom q hq).1, (hcap_geom q hq).2.1⟩
  obtain ⟨h0N_int, h0N_bd⟩ := integrable_dilate_and_bound_s4 ha2 hr_pos hΦ 0 N
  obtain ⟨hN0_int, hN0_bd⟩ := integrable_dilate_and_bound_s4 ha2 hr_pos hΦ N 0
  obtain ⟨hNN_int, hNN_bd⟩ := integrable_dilate_and_bound_s4 ha2 hr_pos hΦ N N
  have h0N_e : (fun p : ℝ × ℝ => |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2) =
      (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ 0 * p.1) (spinLambda a ^ N * p.2)| *
        spinWc a p.1 * spinWc a p.2) := by ext p; rw [pow_zero, one_mul]
  have hN0_e : (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2) =
      (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ 0 * p.2)| *
        spinWc a p.1 * spinWc a p.2) := by ext p; rw [pow_zero, one_mul]
  rw [← h0N_e] at h0N_int h0N_bd
  rw [← hN0_e] at hN0_int hN0_bd
  have hG_c : Continuous (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) := by
    unfold spinG; exact hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
  have hW_c : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
  have hDa_c : Continuous (fun p : ℝ × ℝ => spinDa a Φ p.1 p.2) := by
    unfold spinDa
    exact (((hG_c.sub (hG_c.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd))).sub
      (hG_c.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd)))).add
      (hG_c.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))))
  have hDelta_c : Continuous (fun p : ℝ × ℝ => spinDeltaA a Φ p.1 p.2) := by
    unfold spinDeltaA
    exact hDa_c.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
  have hT_c : Continuous (fun p : ℝ × ℝ => spinTruncInv a N Φ p.1 p.2) := by
    unfold spinTruncInv
    have hsc : ∀ c1 c2 : ℝ, Continuous (fun p : ℝ × ℝ => spinG a Φ (c1 * p.1) (c2 * p.2)) := fun c1 c2 =>
      hG_c.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
    have hsum_fn : ∀ (M : ℕ) (F : ℕ → ℝ × ℝ → ℝ), (∀ j < M, Continuous (F j)) →
        Continuous (fun x => ∑ j ∈ Finset.range M, F j x) := fun M F hF => by
      induction M with
      | zero => simpa using continuous_const
      | succ k ih =>
        simp_rw [Finset.sum_range_succ]
        exact (ih fun j hj => hF j (Nat.lt_succ_of_lt hj)).add (hF k (Nat.lt_succ_self k))
    refine hsum_fn N _ fun j _ => hsum_fn N _ fun ℓ _ => ?_
    simp only [spinDeltaA, spinDa, ← mul_assoc]
    exact (((hsc _ _).sub (hsc _ _)).sub (hsc _ _)).add (hsc _ _)
  have hdiff_i : Integrable (fun p : ℝ × ℝ =>
      |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) := by
    refine ((h0N_int.add hN0_int).add hNN_int).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (((hG_c.sub hT_c).abs.mul (hW_c.comp continuous_fst)).mul
        (hW_c.comp continuous_snd)).aestronglyMeasurable
    · have hw1 := spinWc_nonneg ha2.le p.1
      have hw2 := spinWc_nonneg ha2.le p.2
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hw1) hw2),
        spinG_sub_spinTruncInv ha2]
      have hab1 := abs_add_le (spinG a Φ p.1 (spinLambda a ^ N * p.2)) (spinG a Φ (spinLambda a ^ N * p.1) p.2)
      have hab2 := abs_sub_le (spinG a Φ p.1 (spinLambda a ^ N * p.2) + spinG a Φ (spinLambda a ^ N * p.1) p.2) 0
        (spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2))
      rw [sub_zero, zero_sub, abs_neg] at hab2
      have hab : |spinG a Φ p.1 (spinLambda a ^ N * p.2) +
          spinG a Φ (spinLambda a ^ N * p.1) p.2 -
          spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| ≤
          |spinG a Φ p.1 (spinLambda a ^ N * p.2)| +
            |spinG a Φ (spinLambda a ^ N * p.1) p.2| +
            |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| := by linarith
      calc _ ≤ (|spinG a Φ p.1 (spinLambda a ^ N * p.2)| +
              |spinG a Φ (spinLambda a ^ N * p.1) p.2| +
              |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)|) *
              spinWc a p.1 * spinWc a p.2 := by gcongr
        _ = |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 +
            |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2 +
            |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 := by ring
  have htail_cap : ∫ q in E_cap, |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| *
      spinWc a q.1 * spinWc a q.2 ≤ 3 * Real.exp (-2 * π * xiStar * R ^ (3 / 2 : ℝ)) := by
    let S_r : Set (ℝ × ℝ) := {q : ℝ × ℝ | r ≤ q.1 ∧ r ≤ q.2}
    have hS_meas : MeasurableSet S_r := by
      have : S_r = Set.Ici r ×ˢ Set.Ici r := rfl
      rw [this]; exact measurableSet_Ici.prod measurableSet_Ici
    have hsub_int : ∫ q in E_cap, |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| *
        spinWc a q.1 * spinWc a q.2 ≤
        ∫ q in S_r, |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| *
        spinWc a q.1 * spinWc a q.2 :=
      setIntegral_mono_set hdiff_i.integrableOn
        (Eventually.of_forall fun p => mul_nonneg (mul_nonneg (abs_nonneg _)
          (spinWc_nonneg ha2.le _)) (spinWc_nonneg ha2.le _)) hcap_sub_r.eventuallyLE
    have hpt_S : ∀ p ∈ S_r,
        |spinG a Φ p.1 p.2 - spinTruncInv a N Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 ≤
          |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 +
          |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2 +
          |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 := by
      intro p _
      have hw1 := spinWc_nonneg ha2.le p.1
      have hw2 := spinWc_nonneg ha2.le p.2
      rw [spinG_sub_spinTruncInv ha2]
      have hab1 := abs_add_le (spinG a Φ p.1 (spinLambda a ^ N * p.2)) (spinG a Φ (spinLambda a ^ N * p.1) p.2)
      have hab2 := abs_sub_le (spinG a Φ p.1 (spinLambda a ^ N * p.2) + spinG a Φ (spinLambda a ^ N * p.1) p.2) 0
        (spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2))
      rw [sub_zero, zero_sub, abs_neg] at hab2
      have hab : |spinG a Φ p.1 (spinLambda a ^ N * p.2) +
          spinG a Φ (spinLambda a ^ N * p.1) p.2 -
          spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| ≤
          |spinG a Φ p.1 (spinLambda a ^ N * p.2)| +
            |spinG a Φ (spinLambda a ^ N * p.1) p.2| +
            |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| := by linarith
      calc _ ≤ (|spinG a Φ p.1 (spinLambda a ^ N * p.2)| +
              |spinG a Φ (spinLambda a ^ N * p.1) p.2| +
              |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)|) *
              spinWc a p.1 * spinWc a p.2 := by gcongr
        _ = |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 +
            |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2 +
            |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 := by ring
    have h0N_S : Integrable (fun p : ℝ × ℝ => |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2)
        (volume.restrict S_r) := h0N_int.integrableOn
    have hN0_S : Integrable (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2)
        (volume.restrict S_r) := hN0_int.integrableOn
    have hNN_S : Integrable (fun p : ℝ × ℝ => |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| *
        spinWc a p.1 * spinWc a p.2) (volume.restrict S_r) := hNN_int.integrableOn
    have hmono := setIntegral_mono_on hdiff_i.integrableOn ((h0N_S.add hN0_S).add hNN_S) hS_meas hpt_S
    have hadd1 := integral_add (h0N_S.add hN0_S) hNN_S
    have hadd2 := integral_add h0N_S hN0_S
    rw [hM2, mul_one] at h0N_bd hN0_bd hNN_bd
    have hexp_NN : Real.exp (-4 * π * r * ((N + N : ℕ) : ℝ)) ≤ Real.exp (-4 * π * r * (N : ℝ)) := by
      refine Real.exp_le_exp.mpr ?_; push_cast; nlinarith [Real.pi_pos, hr_pos, Nat.cast_nonneg (α := ℝ) N]
    have h4r : -4 * π * r * (N : ℝ) ≤ -2 * π * xiStar * R ^ (3 / 2 : ℝ) := by
      dsimp [r]; nlinarith [Real.pi_pos, xiStar_pos, hN_ge]
    have hexp_R : Real.exp (-4 * π * r * (N : ℝ)) ≤ Real.exp (-2 * π * xiStar * R ^ (3 / 2 : ℝ)) :=
      Real.exp_le_exp.mpr h4r
    calc ∫ q in E_cap, |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2
        ≤ ∫ q in S_r, |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 := hsub_int
      _ ≤ ∫ p in S_r, (|spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2 +
            |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2 +
            |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2) := hmono
      _ = (∫ p in S_r, |spinG a Φ p.1 (spinLambda a ^ N * p.2)| * spinWc a p.1 * spinWc a p.2) +
          (∫ p in S_r, |spinG a Φ (spinLambda a ^ N * p.1) p.2| * spinWc a p.1 * spinWc a p.2) +
          (∫ p in S_r, |spinG a Φ (spinLambda a ^ N * p.1) (spinLambda a ^ N * p.2)| *
            spinWc a p.1 * spinWc a p.2) := by
          rw [← hadd2]; exact hadd1
      _ ≤ Real.exp (-4 * π * r * (N : ℝ)) + Real.exp (-4 * π * r * (N : ℝ)) +
          Real.exp (-4 * π * r * (N : ℝ)) :=
          add_le_add (add_le_add (by simpa [S_r] using h0N_bd) (by simpa [S_r] using hN0_bd))
            ((by simpa [S_r] using hNN_bd).trans hexp_NN)
      _ = 3 * Real.exp (-4 * π * r * (N : ℝ)) := by ring
      _ ≤ 3 * Real.exp (-2 * π * xiStar * R ^ (3 / 2 : ℝ)) := by gcongr
  have hc_sub_n0 : n₀ + 1 ≤ c := by dsimp [c]; linarith
  obtain ⟨⟨hS_int, hS_le, hS_ae⟩, _hfold_b, hfold_c⟩ := hS22b_main hc_sub_n0
    (by simpa [hc_sub, ha_eq] using hΦ) (by simpa [hc_sub, ha_eq] using hM2)
  let bStar := spinBStar a
  let D := 3 * bStar / 4
  have hγ_half : (3 / 4 : ℝ) ≤ spinGamma a := by
    have ha4 : 4 ≤ a := by dsimp [a]; linarith
    have : (9 / 16 : ℝ) ≤ 1 - 2 / a := by
      have : 2 / a ≤ 2 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) ha4
      linarith
    unfold spinGamma
    calc (3 / 4 : ℝ) = Real.sqrt (9 / 16) := by norm_num
      _ ≤ Real.sqrt (1 - 2 / a) := Real.sqrt_le_sqrt this
  have hbStar_ge : 3 * xiStar / 4 ≤ bStar := by
    dsimp [bStar]; unfold spinBStar; nlinarith [xiStar_pos]
  have hbStar_le : bStar ≤ xiStar := by
    dsimp [bStar]; unfold spinBStar; nlinarith [spinGamma_lt_one ha2, xiStar_pos]
  have hξ_bStar : xiStar - bStar ≤ 24 * xiStar / n' := by
    have h1γ : 1 - spinGamma a ≤ 2 / a := by
      have hdiff : 1 - spinGamma a ^ 2 = 2 / a := by rw [spinGamma_sq ha2.le]; ring
      have hpos : 0 < 1 + spinGamma a := by linarith [spinGamma_pos ha2]
      calc 1 - spinGamma a = (2 / a) / (1 + spinGamma a) := by
            rw [← hdiff, show 1 - spinGamma a ^ 2 = (1 - spinGamma a) * (1 + spinGamma a) by ring,
              mul_div_cancel_right₀ _ hpos.ne']
        _ ≤ (2 / a) / 1 := div_le_div_of_nonneg_left (by positivity) one_pos (by linarith [spinGamma_pos ha2])
        _ = 2 / a := div_one _
    have h2a : 2 / a = 24 / n' := by dsimp [a]; ring
    calc xiStar - bStar = xiStar * (1 - spinGamma a) := by dsimp [bStar]; unfold spinBStar; ring
      _ ≤ xiStar * (2 / a) := mul_le_mul_of_nonneg_left h1γ xiStar_pos.le
      _ = 24 * xiStar / n' := by rw [h2a]; ring
  have hlamN_sub : spinLambda a ^ N - 1 ≤ 48 * (N : ℝ) / n' := by
    refine spinLambda_pow_sub_one_le (by simpa [hc_sub] using hc49) ?_
    rw [hc_sub, div_le_iff₀ hn_pos]; linarith
  have hN_eps : (48 * (N : ℝ) / n') * (2 * xiStar) + 24 * xiStar / n' ≤ ε * (R / 4) := by
    have hn_rew : n' ^ (-1 : ℝ) = ε * n' ^ (-(1 / 3 : ℝ)) := by
      dsimp [ε]; rw [← Real.rpow_add hn_pos]; congr 1; norm_num
    have h1 : (48 * (N : ℝ) / n') * (2 * xiStar) + 24 * xiStar / n' =
        (96 * (N : ℝ) * xiStar + 24 * xiStar) * n' ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one]; ring
    rw [h1, hn_rew]
    calc (96 * (N : ℝ) * xiStar + 24 * xiStar) * (ε * n' ^ (-(1 / 3 : ℝ)))
        = ε * ((96 * (N : ℝ) * xiStar + 24 * xiStar) * n' ^ (-(1 / 3 : ℝ))) := by ring
      _ ≤ ε * (R / 4) := mul_le_mul_of_nonneg_left hie_lt.le hε_pos.le
  let A_box : Set (ℝ × ℝ) := {y : ℝ × ℝ | 0 < y.1 ∧ 0 < y.2 ∧
    (y.1 + y.2) / 2 ≤ bStar - ε * (R / 2) ∧ bStar - xiStar ≤ (y.1 + y.2) / 2 ∧
    |(y.1 - y.2) / 2| ≤ D}
  have hAbox_meas : MeasurableSet A_box :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      ((isOpen_lt continuous_const continuous_snd).measurableSet.inter
        ((isClosed_le ((continuous_fst.add continuous_snd).div_const 2) continuous_const).measurableSet.inter
          ((isClosed_le continuous_const ((continuous_fst.add continuous_snd).div_const 2)).measurableSet.inter
            (isClosed_le (((continuous_fst.sub continuous_snd).div_const 2).abs)
              continuous_const).measurableSet)))
  have hterm_bd : ∀ j ℓ : ℕ, j < N → ℓ < N →
      ∫⁻ q in E_cap, ENNReal.ofReal
        (|spinDeltaA a Φ (spinLambda a ^ j * q.1) (spinLambda a ^ ℓ * q.2)| *
          spinWc a q.1 * spinWc a q.2) ≤
        ENNReal.ofReal (2 * C_22b * (2 * D + C_22b) * (2 / κ) *
          Real.exp (-c_22 * R ^ (3 / 2 : ℝ))) := by
    intro j ℓ hj hℓ
    have hlam_gt1 := spinLambda_gt_one_s4 ha2
    have hlj_pos : 0 < spinLambda a ^ j := pow_pos (lt_trans zero_lt_one hlam_gt1) j
    have hll_pos : 0 < spinLambda a ^ ℓ := pow_pos (lt_trans zero_lt_one hlam_gt1) ℓ
    have hlj_ge1 : 1 ≤ spinLambda a ^ j := one_le_pow₀ hlam_gt1.le
    have hll_ge1 : 1 ≤ spinLambda a ^ ℓ := one_le_pow₀ hlam_gt1.le
    have hlj_leN : spinLambda a ^ j ≤ spinLambda a ^ N := pow_le_pow_right₀ hlam_gt1.le hj.le
    have hll_leN : spinLambda a ^ ℓ ≤ spinLambda a ^ N := pow_le_pow_right₀ hlam_gt1.le hℓ.le
    let fA : ℝ × ℝ → ℝ≥0∞ := A_box.indicator (fun y =>
      ENNReal.ofReal (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2))
    have hpt_q : ∀ q ∈ E_cap,
        ENNReal.ofReal (|spinDeltaA a Φ (spinLambda a ^ j * q.1) (spinLambda a ^ ℓ * q.2)| *
          spinWc a q.1 * spinWc a q.2) ≤
        fA (spinLambda a ^ j * q.1, spinLambda a ^ ℓ * q.2) := by
      intro q hq
      obtain ⟨hq1_ge, hq2_ge, hq1_le, hq2_le, hq_d_le⟩ := hcap_geom q hq
      have hq1_pos : 0 < q.1 := hq.1.1
      have hq2_pos : 0 < q.2 := hq.1.2.1
      set y1 := spinLambda a ^ j * q.1
      set y2 := spinLambda a ^ ℓ * q.2
      have hy1_pos : 0 < y1 := mul_pos hlj_pos hq1_pos
      have hy2_pos : 0 < y2 := mul_pos hll_pos hq2_pos
      have hdiff_j : y1 - q.1 ≤ (48 * (N : ℝ) / n') * (2 * xiStar) := by
        calc y1 - q.1 = (spinLambda a ^ j - 1) * q.1 := by dsimp [y1]; ring
          _ ≤ (spinLambda a ^ N - 1) * (2 * xiStar) :=
              mul_le_mul (by linarith) hq1_le hq1_pos.le (by linarith [hlj_leN, hlj_ge1])
          _ ≤ (48 * (N : ℝ) / n') * (2 * xiStar) := by gcongr
      have hdiff_l : y2 - q.2 ≤ (48 * (N : ℝ) / n') * (2 * xiStar) := by
        calc y2 - q.2 = (spinLambda a ^ ℓ - 1) * q.2 := by dsimp [y2]; ring
          _ ≤ (spinLambda a ^ N - 1) * (2 * xiStar) :=
              mul_le_mul (by linarith) hq2_le hq2_pos.le (by linarith [hll_leN, hll_ge1])
          _ ≤ (48 * (N : ℝ) / n') * (2 * xiStar) := by gcongr
      have hsum_y_ub : (y1 + y2) / 2 ≤ bStar - ε * (R / 2) := by
        have hq_ub : (q.1 + q.2) / 2 ≤ xiStar - ε * R := hq.1.2.2.2
        linarith
      have hsum_y_lb : bStar - xiStar ≤ (y1 + y2) / 2 := by
        have hq_lb : xiStar - K_1 * δ_n ≤ (q.1 + q.2) / 2 := hq.2
        have hy1_ge : q.1 ≤ y1 := le_mul_of_one_le_left hq1_pos.le hlj_ge1
        have hy2_ge : q.2 ≤ y2 := le_mul_of_one_le_left hq2_pos.le hll_ge1
        have hK_le : K_1 * δ_n ≤ xiStar / 4 :=
          (hKδ_lt.trans_le (min_le_left _ _)).le.trans (by linarith [xiStar_pos])
        have : xiStar - bStar ≤ xiStar / 4 := by linarith
        linarith [hbStar_le]
      have hd_y : |(y1 - y2) / 2| ≤ D := by
        have h48N : 48 * (N : ℝ) / n' ≤ 1 / 16 := by rw [div_le_iff₀ hn_pos]; linarith
        have hdj_xi : y1 - q.1 ≤ xiStar / 8 := hdiff_j.trans (by nlinarith [xiStar_pos])
        have hdl_xi : y2 - q.2 ≤ xiStar / 8 := hdiff_l.trans (by nlinarith [xiStar_pos])
        have hy1_ge : 0 ≤ y1 - q.1 := sub_nonneg.mpr (le_mul_of_one_le_left hq1_pos.le hlj_ge1)
        have hy2_ge : 0 ≤ y2 - q.2 := sub_nonneg.mpr (le_mul_of_one_le_left hq2_pos.le hll_ge1)
        have hdq := abs_le.mp hq_d_le
        have hd_y_le : |(y1 - y2) / 2| ≤ xiStar / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
        have hD_ge : xiStar / 2 ≤ D := by dsimp [D]; linarith [hbStar_ge, xiStar_pos]
        exact hd_y_le.trans hD_ge
      have hy_mem : (y1, y2) ∈ A_box := ⟨hy1_pos, hy2_pos, hsum_y_ub, hsum_y_lb, hd_y⟩
      dsimp [fA]; rw [Set.indicator_of_mem hy_mem]
      refine ENNReal.ofReal_le_ofReal ?_
      have hw1 : spinWc a q.1 ≤ spinWc a y1 := spinWc_mono_abs ha2.le (by
        rw [abs_of_pos hq1_pos, abs_of_pos hy1_pos]; exact le_mul_of_one_le_left hq1_pos.le hlj_ge1)
      have hw2 : spinWc a q.2 ≤ spinWc a y2 := spinWc_mono_abs ha2.le (by
        rw [abs_of_pos hq2_pos, abs_of_pos hy2_pos]; exact le_mul_of_one_le_left hq2_pos.le hll_ge1)
      have hw_mul : spinWc a q.1 * spinWc a q.2 ≤ spinWc a y1 * spinWc a y2 :=
        mul_le_mul hw1 hw2 (spinWc_nonneg ha2.le _) (spinWc_nonneg ha2.le _)
      calc |spinDeltaA a Φ y1 y2| * spinWc a q.1 * spinWc a q.2
          = |spinDeltaA a Φ y1 y2| * (spinWc a q.1 * spinWc a q.2) := by ring
        _ ≤ |spinDeltaA a Φ y1 y2| * (spinWc a y1 * spinWc a y2) :=
            mul_le_mul_of_nonneg_left hw_mul (abs_nonneg _)
        _ = |spinDeltaA a Φ y1 y2| * spinWc a y1 * spinWc a y2 := by ring
    have hgam_le1 : (spinLambda a ^ j)⁻¹ * (spinLambda a ^ ℓ)⁻¹ ≤ 1 :=
      mul_le_one₀ (inv_le_one_of_one_le₀ hlj_ge1) (inv_nonneg.mpr hlj_pos.le) (inv_le_one_of_one_le₀ hll_ge1)
    have hcap_bd := spinS4_3_3_cap_term hR hε_pos (by linarith [hc_sub])
      (by simpa [hc_sub] using hε_eq) hC22_pos hκ_pos (by dsimp [D]; linarith)
      (by linarith [xiStar_pos]) (by simpa [hc_sub, ha_eq] using hΦ)
      (by simpa [hc_sub, ha_eq] using hS_int) (by simpa [hc_sub, ha_eq] using hS_le)
      (by simpa [hc_sub, ha_eq] using hS_ae) (by simpa [hc_sub, ha_eq] using hfold_c)
      (by simpa [hc_sub, ha_eq] using ha2) hAbox_meas (fun y hy => hy)
    calc ∫⁻ q in E_cap, ENNReal.ofReal
            (|spinDeltaA a Φ (spinLambda a ^ j * q.1) (spinLambda a ^ ℓ * q.2)| *
              spinWc a q.1 * spinWc a q.2)
        ≤ ∫⁻ q : ℝ × ℝ, fA (spinLambda a ^ j * q.1, spinLambda a ^ ℓ * q.2) := by
            rw [← lintegral_indicator hm_cap]
            refine lintegral_mono fun q => ?_
            by_cases hq : q ∈ E_cap
            · rw [Set.indicator_of_mem hq]; exact hpt_q q hq
            · rw [Set.indicator_of_notMem hq]; exact zero_le _
      _ = ENNReal.ofReal ((spinLambda a ^ j)⁻¹ * (spinLambda a ^ ℓ)⁻¹) * ∫⁻ y : ℝ × ℝ, fA y :=
            lintegral_prod_scale_s4_3 hlj_pos hll_pos fA
      _ ≤ ENNReal.ofReal 1 * ∫⁻ y in A_box, ENNReal.ofReal
            (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2) := by
            rw [lintegral_indicator hAbox_meas]; gcongr
      _ ≤ 1 * ENNReal.ofReal (2 * C_22b * (2 * D + C_22b) * (2 / κ) *
            Real.exp (-c_22 * R ^ (3 / 2 : ℝ))) := by
            rw [ENNReal.ofReal_one]; gcongr; simpa [hc_sub, ha_eq] using hcap_bd
      _ = ENNReal.ofReal (2 * C_22b * (2 * D + C_22b) * (2 / κ) *
            Real.exp (-c_22 * R ^ (3 / 2 : ℝ))) := one_mul _
  have hcap_bd : ∫ q in E_cap, g q ≤ (3 + C_cap) * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by
    have hnn_g : ∀ q : ℝ × ℝ, 0 ≤ g q := fun q =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha2.le _)) (spinWc_nonneg ha2.le _)
    let tailFn : ℝ × ℝ → ℝ≥0∞ := fun q =>
      ENNReal.ofReal (|spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2)
    let termFn : ℕ → ℕ → ℝ × ℝ → ℝ≥0∞ := fun j ℓ q =>
      ENNReal.ofReal (|spinDeltaA a Φ (spinLambda a ^ j * q.1) (spinLambda a ^ ℓ * q.2)| *
        spinWc a q.1 * spinWc a q.2)
    have htail_meas : Measurable tailFn :=
      (ENNReal.continuous_ofReal.comp (((hG_c.sub hT_c).abs.mul (hW_c.comp continuous_fst)).mul
        (hW_c.comp continuous_snd))).measurable
    have hterm_meas : ∀ j ℓ : ℕ, Measurable (termFn j ℓ) := fun j ℓ =>
      (ENNReal.continuous_ofReal.comp (((hDelta_c.comp ((continuous_const.mul continuous_fst).prodMk
        (continuous_const.mul continuous_snd))).abs.mul (hW_c.comp continuous_fst)).mul
        (hW_c.comp continuous_snd))).measurable
    have hpt_le : ∀ q : ℝ × ℝ, ENNReal.ofReal (g q) ≤
        tailFn q + ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N, termFn j ℓ q := by
      intro q
      have hw1 := spinWc_nonneg ha2.le q.1
      have hw2 := spinWc_nonneg ha2.le q.2
      have hG_abs : |spinG a Φ q.1 q.2| ≤ |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| +
          ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N,
            |spinDeltaA a Φ (spinLambda a ^ j * q.1) (spinLambda a ^ ℓ * q.2)| := by
        have htri : |spinG a Φ q.1 q.2| ≤
            |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| + |spinTruncInv a N Φ q.1 q.2| := by
          have := abs_add_le (spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2) (spinTruncInv a N Φ q.1 q.2)
          simpa [sub_add_cancel] using this
        have hsum1 : |spinTruncInv a N Φ q.1 q.2| ≤
            ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N,
              |spinDeltaA a Φ (spinLambda a ^ j * q.1) (spinLambda a ^ ℓ * q.2)| := by
          unfold spinTruncInv
          exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
        linarith
      have hr : g q ≤ |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 +
          ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N,
            |spinDeltaA a Φ (spinLambda a ^ j * q.1) (spinLambda a ^ ℓ * q.2)| * spinWc a q.1 * spinWc a q.2 := by
        dsimp [g]
        calc |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2
            ≤ (|spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| +
                ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N,
                  |spinDeltaA a Φ (spinLambda a ^ j * q.1) (spinLambda a ^ ℓ * q.2)|) *
                spinWc a q.1 * spinWc a q.2 := by gcongr
          _ = |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 +
              ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N,
                |spinDeltaA a Φ (spinLambda a ^ j * q.1) (spinLambda a ^ ℓ * q.2)| *
                  spinWc a q.1 * spinWc a q.2 := by
              rw [add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
              congr 1; refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_mul, Finset.sum_mul]
      refine (ENNReal.ofReal_le_ofReal hr).trans ?_
      have hnn1 : 0 ≤ |spinG a Φ q.1 q.2 - spinTruncInv a N Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 := by
        positivity
      have hnn2 : ∀ j ℓ : ℕ, 0 ≤ |spinDeltaA a Φ (spinLambda a ^ j * q.1) (spinLambda a ^ ℓ * q.2)| *
          spinWc a q.1 * spinWc a q.2 := fun j ℓ => by positivity
      rw [ENNReal.ofReal_add hnn1 (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun ℓ _ => hnn2 j ℓ)]
      congr 1
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => Finset.sum_nonneg fun ℓ _ => hnn2 j ℓ)]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact ENNReal.ofReal_sum_of_nonneg (fun ℓ _ => hnn2 j ℓ)
    have hsum_bd : ∫⁻ q in E_cap, (tailFn q + ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N, termFn j ℓ q) =
        (∫⁻ q in E_cap, tailFn q) +
          ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N, ∫⁻ q in E_cap, termFn j ℓ q := by
      rw [lintegral_add_left htail_meas]
      congr 1
      rw [lintegral_finset_sum _ fun j _ => Finset.measurable_sum _ fun ℓ _ => hterm_meas j ℓ]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact lintegral_finset_sum _ fun ℓ _ => hterm_meas j ℓ
    have htail_enn : ∫⁻ q in E_cap, tailFn q ≤
        ENNReal.ofReal (3 * Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hdiff_i.integrableOn
        (Eventually.of_forall fun q => by positivity)]
      refine ENNReal.ofReal_le_ofReal (htail_cap.trans ?_)
      have hpi_le : c_exp ≤ 2 * π * xiStar := (min_le_left _ _).trans (by
        have := Real.pi_pos; have := xiStar_pos; linarith)
      gcongr
    have hcap_N2 : ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N, ∫⁻ q in E_cap, termFn j ℓ q ≤
        ENNReal.ofReal (C_cap * Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) := by
      let M_one : ℝ := 2 * C_22b * (2 * D + C_22b) * (2 / κ) * Real.exp (-c_22 * R ^ (3 / 2 : ℝ))
      have hsum_le : ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N, ∫⁻ q in E_cap, termFn j ℓ q ≤
          ∑ _j ∈ Finset.range N, ∑ _ℓ ∈ Finset.range N, ENNReal.ofReal M_one :=
        Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun ℓ hℓ =>
          hterm_bd j ℓ (Finset.mem_range.mp hj) (Finset.mem_range.mp hℓ)
      have hcard : (∑ _j ∈ Finset.range N, ∑ _ℓ ∈ Finset.range N, ENNReal.ofReal M_one) =
          ENNReal.ofReal ((N : ℝ) ^ 2 * M_one) := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1; ring
      refine hsum_le.trans (hcard.le.trans (ENNReal.ofReal_le_ofReal ?_))
      have hD_le : D ≤ xiStar := by dsimp [D]; linarith [hbStar_le, xiStar_pos]
      have hN2_le : (N : ℝ) ^ 2 ≤ 4 * (R ^ (3 / 2 : ℝ)) ^ 2 := by
        have : (N : ℝ) ^ 2 ≤ (2 * R ^ (3 / 2 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hN_le 2
        linarith
      have hcexp_le : 2 * c_exp ≤ c_22 := by linarith [min_le_right (π * xiStar) (c_22 / 2)]
      have hexp_split : Real.exp (-c_22 * R ^ (3 / 2 : ℝ)) ≤
          Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have : 0 ≤ R ^ (3 / 2 : ℝ) := by positivity
        nlinarith
      have habsorb := sq_mul_exp_neg_le (u := R ^ (3 / 2 : ℝ)) (c := c_exp) (by positivity) hcexp_pos
      calc (N : ℝ) ^ 2 * M_one
          ≤ (4 * (R ^ (3 / 2 : ℝ)) ^ 2) *
              (2 * C_22b * (2 * xiStar + C_22b) * (2 / κ) *
                (Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)))) := by
              dsimp [M_one]; gcongr
        _ = 4 * (2 * C_22b * (2 * xiStar + C_22b) * (2 / κ)) *
              ((R ^ (3 / 2 : ℝ)) ^ 2 * Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) *
              Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by ring
        _ ≤ 4 * (2 * C_22b * (2 * xiStar + C_22b) * (2 / κ)) * (4 / c_exp ^ 2) *
              Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by gcongr
        _ = C_cap * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by dsimp [C_cap]; ring
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity),
      ofReal_integral_eq_lintegral_ofReal hG_int.integrableOn (Eventually.of_forall hnn_g)]
    calc ∫⁻ q in E_cap, ENNReal.ofReal (g q)
        ≤ ∫⁻ q in E_cap, (tailFn q + ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N, termFn j ℓ q) :=
            lintegral_mono fun q => hpt_le q
      _ = (∫⁻ q in E_cap, tailFn q) +
            ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N, ∫⁻ q in E_cap, termFn j ℓ q := hsum_bd
      _ ≤ ENNReal.ofReal (3 * Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) +
            ENNReal.ofReal (C_cap * Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) := add_le_add htail_enn hcap_N2
      _ = ENNReal.ofReal ((3 + C_cap) * Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; ring
  have hpp_bd : ∫ q in E_pp, g q ≤ (1 + 3 + C_cap) * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by
    have hfar' : ∫ q in E_far, g q ≤ 1 * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by linarith
    calc ∫ q in E_pp, g q = (∫ q in E_far, g q) + ∫ q in E_cap, g q := hpp_split
      _ ≤ 1 * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) + (3 + C_cap) * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) :=
          add_le_add hfar' hcap_bd
      _ = (1 + 3 + C_cap) * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by ring
  calc ∫ p in E_all, max (-spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2
      ≤ ∫ p in E_all, g p := hmax_le_abs
    _ = 4 * ∫ q in E_pp, g q := hE_all_eq
    _ ≤ 4 * ((1 + 3 + C_cap) * Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) := by linarith
    _ ≤ C * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        dsimp [C]; linarith

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS4_3_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS4_3_3

end FormalResearch.ModularBootstrap.Spin