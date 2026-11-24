module

public import FormalResearch.ModularBootstrap.Upper.Bump.Value
public import FormalResearch.ModularBootstrap.Upper.Positivity.RegionII

/-!
# `R_bump`: the bounds `1 ≤ R_bump ≤ C_p` and `R_bump = 1 + O(1/c')` (`fw:e3.3`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, "Quantitative macroscopic bump lemma"
(display `fw:e3.3`) with the two-case block-sum argument of TeX issue T8.

With `bumpFactor` (`Value.lean`) the product over `N₀ < k ≤ N` of `bumpRatio`:

* `bumpRatio_one_le`, `bumpRatio_le_exp`: each ratio is `≥ 1` (`fw:e3.1`) and, in the block, at most
  `exp (2 K ℓ_k² / ((x - χ_k)² + ℓ_k²))` (`fw:e3.2a`);
* `bumpFactor_one_le`, `bumpFactor_le` (`fw:e3.3`, first display): `1 ≤ R_bump ≤ C_p` for all `x ≥ 0`,
  `C_p = exp (2K (2 + 4 (ρ_U(X_p+1)/ρ_U(ξ_*+2r_p))²))`, uniformly in the cuts and the base comb;
* `bumpFactor_le_one_add` (`fw:e3.3`, second display): `R_bump ≤ 1 + C/c'` for `0 ≤ x ≤ ξ_* + r_p`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Bump

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Window
open scoped Classical

/-- The ratio of the bumped to the unbumped pair modulus at the pair `k`. -/
noncomputable def bumpRatio (d : BumpData) (c' η₀ x : ℝ) (k : ℕ) : ℝ :=
  blaschkePairQ (chiQuantile c' (k : ℝ)) (bumpHeight d c' η₀ k) x /
    blaschkePairQ (chiQuantile c' (k : ℝ)) (η₀ * siteGap c' k) x

lemma bumpFactor_eq_prod (d : BumpData) (c' η₀ : ℝ) (N₀ N : ℕ) (x : ℝ) :
    bumpFactor d c' η₀ N₀ N x = ∏ k ∈ Finset.Ioc N₀ N, bumpRatio d c' η₀ x k := rfl

lemma chi_nonneg {c' : ℝ} (hc' : 0 < c') {k : ℕ} (hk : 1 ≤ k) : 0 ≤ chiQuantile c' (k : ℝ) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1

/-- The facts on the ratio of pair `k` that hold for `c'` large, uniformly in `k`, `x`, the cuts and the base. -/
theorem bumpRatio_facts (d : BumpData) {η₀ : ℝ} (hη₀ : 0 < η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ k : ℕ, 1 ≤ k → ∀ x : ℝ,
      0 < blaschkePairQ (chiQuantile c' (k : ℝ)) (η₀ * siteGap c' k) x ∧
      (¬ d.InBlock c' k → bumpRatio d c' η₀ x k = 1) ∧
      (d.InBlock c' k → 1 ≤ bumpRatio d c' η₀ x k ∧ (0 ≤ x →
        bumpRatio d c' η₀ x k ≤ Real.exp (2 * pairK η₀ d.H * siteGap c' k ^ 2 /
          ((x - chiQuantile c' (k : ℝ)) ^ 2 + siteGap c' k ^ 2)))) := by
  obtain ⟨_, _, h_ev⟩ := siteGap_eventually_le
  filter_upwards [h_ev, block_gap_bounds d, eventually_ge_atTop (4 * d.H / d.rhoLo),
    eventually_gt_atTop 0] with c' ⟨hmono, _, _, hgap⟩ hbg hc4 hc' k hk x
  have hℓpos := siteGap_pos_of hc' hk
  have hℓle : siteGap c' k ≤ 1 / 2 := (hmono k hk).trans hgap
  have hε : η₀ * siteGap c' k ≤ 1 / 2 := by nlinarith
  have hQ0 : 0 < blaschkePairQ (chiQuantile c' (k : ℝ)) (η₀ * siteGap c' k) x :=
    blaschkePairQ_pos_of_eps (by positivity) hε
  refine ⟨hQ0, fun hnb => ?_, fun hb => ?_⟩
  · unfold bumpRatio bumpHeight
    simp only [hnb, ite_false]
    exact div_self hQ0.ne'
  · have hL := (hbg k hk hb).2
    have hρ := d.rhoLo_pos
    have hHℓ : d.H * siteGap c' k ≤ 1 / 2 := by
      have h1 : d.H * siteGap c' k ≤ d.H * (2 / (c' * d.rhoLo)) :=
        mul_le_mul_of_nonneg_left hL d.H_pos.le
      have h2 : d.H * (2 / (c' * d.rhoLo)) ≤ 1 / 2 := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        rw [div_le_iff₀ hρ] at hc4
        nlinarith
      linarith
    have h01 : η₀ * siteGap c' k ≤ d.H * siteGap c' k :=
      mul_le_mul_of_nonneg_right (hη₀1.trans d.H_ge) hℓpos.le
    have hheight : bumpHeight d c' η₀ k = d.H * siteGap c' k := by
      unfold bumpHeight; simp [hb]
    have hone : 1 ≤ bumpRatio d c' η₀ x k := by
      unfold bumpRatio
      rw [hheight, one_le_div hQ0]
      exact blaschkePairQ_mono_eps x (by positivity) h01 hHℓ
    refine ⟨hone, fun hx => ?_⟩
    unfold bumpRatio
    rw [hheight, div_le_iff₀ hQ0]
    exact blaschkePairQ_le_exp_mul hη₀ hℓpos (hℓle.trans (by norm_num)) le_rfl h01 le_rfl hHℓ
      (chi_nonneg hc' hk) hx

/-- `R_bump ≥ 1` (`fw:e3.3`, lower bound; `fw:e3.1`). -/
theorem bumpFactor_one_le (d : BumpData) {η₀ : ℝ} (hη₀ : 0 < η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ (N₀ N : ℕ) (x : ℝ), 1 ≤ bumpFactor d c' η₀ N₀ N x := by
  filter_upwards [bumpRatio_facts d hη₀ hη₀1] with c' h N₀ N x
  rw [bumpFactor_eq_prod]
  calc (1 : ℝ) = ∏ _k ∈ Finset.Ioc N₀ N, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) fun k hk => by
        have hk1 : 1 ≤ k := by
          have := (Finset.mem_Ioc.mp hk).1; omega
        by_cases hb : d.InBlock c' k
        · exact ((h k hk1 x).2.2 hb).1
        · exact ((h k hk1 x).2.1 hb).ge

/-- The constant `C_p` of `fw:e3.3`. -/
noncomputable def bumpC (d : BumpData) (η₀ : ℝ) : ℝ :=
  Real.exp (2 * pairK η₀ d.H * (2 + 4 * (d.rhoHi / d.rhoLo) ^ 2))

/-- `R_bump ≤ C_p` for all `x ≥ 0`, uniformly in the cuts (`fw:e3.3`, upper bound; `fw:e3.2a` and the block sum). -/
theorem bumpFactor_le (d : BumpData) {η₀ : ℝ} (hη₀ : 0 < η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ (N₀ N : ℕ) (x : ℝ), 0 ≤ x → bumpFactor d c' η₀ N₀ N x ≤ bumpC d η₀ := by
  filter_upwards [bumpRatio_facts d hη₀ hη₀1, block_sum_le d] with c' h hsum N₀ N x hx
  rw [bumpFactor_eq_prod]
  set a : ℕ → ℝ := fun k => 2 * pairK η₀ d.H * siteGap c' k ^ 2 /
    ((x - chiQuantile c' (k : ℝ)) ^ 2 + siteGap c' k ^ 2) with ha
  have hpt : ∀ k ∈ Finset.Ioc N₀ N, bumpRatio d c' η₀ x k ≤
      if d.InBlock c' k then Real.exp (a k) else 1 := by
    intro k hk
    have hk1 : 1 ≤ k := by
      have := (Finset.mem_Ioc.mp hk).1; omega
    by_cases hb : d.InBlock c' k
    · simp only [hb, ↓reduceIte]; exact ((h k hk1 x).2.2 hb).2 hx
    · simp only [hb, ↓reduceIte]; exact ((h k hk1 x).2.1 hb).le
  have hnn : ∀ k ∈ Finset.Ioc N₀ N, 0 ≤ bumpRatio d c' η₀ x k := by
    intro k hk
    have hk1 : 1 ≤ k := by
      have := (Finset.mem_Ioc.mp hk).1; omega
    by_cases hb : d.InBlock c' k
    · exact zero_le_one.trans ((h k hk1 x).2.2 hb).1
    · exact ((h k hk1 x).2.1 hb).ge.trans' zero_le_one
  calc ∏ k ∈ Finset.Ioc N₀ N, bumpRatio d c' η₀ x k
      ≤ ∏ k ∈ Finset.Ioc N₀ N, (if d.InBlock c' k then Real.exp (a k) else 1) :=
        Finset.prod_le_prod₀ hnn hpt
    _ = ∏ k ∈ d.blockSet c' N₀ N, Real.exp (a k) := by
        rw [BumpData.blockSet, Finset.prod_filter]
    _ = Real.exp (∑ k ∈ d.blockSet c' N₀ N, a k) := by rw [Real.exp_sum]
    _ ≤ bumpC d η₀ := by
        unfold bumpC
        apply Real.exp_le_exp.mpr
        have hK := pairK_nonneg η₀ d.H
        have : ∑ k ∈ d.blockSet c' N₀ N, a k =
            2 * pairK η₀ d.H * ∑ k ∈ d.blockSet c' N₀ N,
              siteGap c' k ^ 2 / ((x - chiQuantile c' (k : ℝ)) ^ 2 + siteGap c' k ^ 2) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [ha]; ring
        rw [this]
        exact mul_le_mul_of_nonneg_left (hsum N₀ N x) (by positivity)

/-- The constant of the `1 + O(1/c')` bound. -/
noncomputable def bumpC' (d : BumpData) (η₀ : ℝ) : ℝ :=
  4 * (((d.X - d.lo) * d.rhoHi / 2 + 1) * (8 * pairK η₀ d.H / (d.rhoLo ^ 2 * d.r ^ 2)))

/-- `R_bump ≤ 1 + C/c'` on `0 ≤ x ≤ ξ_* + r_p` (`fw:e3.3`, second display). -/
theorem bumpFactor_le_one_add (d : BumpData) {η₀ : ℝ} (hη₀ : 0 < η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ (N₀ N : ℕ) (x : ℝ), 0 ≤ x → x ≤ xiStar + d.r →
      bumpFactor d c' η₀ N₀ N x ≤ 1 + bumpC' d η₀ / c' := by
  have hρlo := d.rhoLo_pos
  have hρhi := d.rhoHi_pos
  have hK := pairK_nonneg η₀ d.H
  set C1 : ℝ := ((d.X - d.lo) * d.rhoHi / 2 + 1) * (8 * pairK η₀ d.H / (d.rhoLo ^ 2 * d.r ^ 2)) with hC1
  have hC1nn : 0 ≤ C1 := by
    have := d.lo_lt_X
    have := d.r_pos
    rw [hC1]; positivity
  filter_upwards [bumpRatio_facts d hη₀ hη₀1, block_gap_bounds d, block_card_le d,
    eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (2 * C1 + 1)]
    with c' h hbg hcard hc1 hc2 N₀ N x hx hxr
  have hc' : 0 < c' := lt_of_lt_of_le one_pos hc1
  rw [bumpFactor_eq_prod]
  set a : ℕ → ℝ := fun k => 2 * pairK η₀ d.H * siteGap c' k ^ 2 /
    ((x - chiQuantile c' (k : ℝ)) ^ 2 + siteGap c' k ^ 2) with ha
  have hpt : ∀ k ∈ Finset.Ioc N₀ N, bumpRatio d c' η₀ x k ≤
      if d.InBlock c' k then Real.exp (a k) else 1 := by
    intro k hk
    have hk1 : 1 ≤ k := by
      have := (Finset.mem_Ioc.mp hk).1; omega
    by_cases hb : d.InBlock c' k
    · simp only [hb, ↓reduceIte]; exact ((h k hk1 x).2.2 hb).2 hx
    · simp only [hb, ↓reduceIte]; exact ((h k hk1 x).2.1 hb).le
  have hnn : ∀ k ∈ Finset.Ioc N₀ N, 0 ≤ bumpRatio d c' η₀ x k := by
    intro k hk
    have hk1 : 1 ≤ k := by
      have := (Finset.mem_Ioc.mp hk).1; omega
    by_cases hb : d.InBlock c' k
    · exact zero_le_one.trans ((h k hk1 x).2.2 hb).1
    · exact ((h k hk1 x).2.1 hb).ge.trans' zero_le_one
  have hprod : ∏ k ∈ Finset.Ioc N₀ N, bumpRatio d c' η₀ x k ≤
      Real.exp (∑ k ∈ d.blockSet c' N₀ N, a k) := by
    calc ∏ k ∈ Finset.Ioc N₀ N, bumpRatio d c' η₀ x k
        ≤ ∏ k ∈ Finset.Ioc N₀ N, (if d.InBlock c' k then Real.exp (a k) else 1) :=
          Finset.prod_le_prod₀ hnn hpt
      _ = ∏ k ∈ d.blockSet c' N₀ N, Real.exp (a k) := by
          rw [BumpData.blockSet, Finset.prod_filter]
      _ = _ := by rw [Real.exp_sum]
  -- each block term
  have hterm : ∀ k ∈ d.blockSet c' N₀ N, a k ≤ 2 * pairK η₀ d.H * (4 / (c' ^ 2 * d.rhoLo ^ 2)) / d.r ^ 2 := by
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    have hk1 : 1 ≤ k := by
      have := (Finset.mem_Ioc.mp hk'.1).1; omega
    have hb := hk'.2
    obtain ⟨hlo, hhi⟩ := hbg k hk1 hb
    have hℓpos : 0 < siteGap c' k := lt_of_lt_of_le (by positivity) hlo
    have hdist : d.r ^ 2 ≤ (x - chiQuantile c' (k : ℝ)) ^ 2 := by
      have h1 : chiQuantile c' (k : ℝ) - x ≥ d.r := by
        have := hb.1
        unfold BumpData.lo at this
        linarith
      calc d.r ^ 2 ≤ (chiQuantile c' (k : ℝ) - x) ^ 2 := pow_le_pow_left₀ d.r_pos.le h1 2
        _ = (x - chiQuantile c' (k : ℝ)) ^ 2 := by ring
    have hrpos := d.r_pos
    rw [ha]
    show 2 * pairK η₀ d.H * siteGap c' k ^ 2 / ((x - chiQuantile c' (k : ℝ)) ^ 2 + siteGap c' k ^ 2) ≤ _
    calc 2 * pairK η₀ d.H * siteGap c' k ^ 2 / ((x - chiQuantile c' (k : ℝ)) ^ 2 + siteGap c' k ^ 2)
        ≤ 2 * pairK η₀ d.H * siteGap c' k ^ 2 / d.r ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          nlinarith [sq_nonneg (siteGap c' k)]
      _ ≤ 2 * pairK η₀ d.H * (4 / (c' ^ 2 * d.rhoLo ^ 2)) / d.r ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : siteGap c' k ^ 2 ≤ (2 / (c' * d.rhoLo)) ^ 2 :=
            pow_le_pow_left₀ hℓpos.le hhi 2
          calc siteGap c' k ^ 2 ≤ (2 / (c' * d.rhoLo)) ^ 2 := this
            _ = 4 / (c' ^ 2 * d.rhoLo ^ 2) := by field_simp; ring
  have hsum : ∑ k ∈ d.blockSet c' N₀ N, a k ≤ C1 / c' := by
    calc ∑ k ∈ d.blockSet c' N₀ N, a k
        ≤ ∑ _k ∈ d.blockSet c' N₀ N, 2 * pairK η₀ d.H * (4 / (c' ^ 2 * d.rhoLo ^ 2)) / d.r ^ 2 :=
          Finset.sum_le_sum hterm
      _ = ((d.blockSet c' N₀ N).card : ℝ) *
          (2 * pairK η₀ d.H * (4 / (c' ^ 2 * d.rhoLo ^ 2)) / d.r ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((d.X - d.lo) * c' * d.rhoHi / 2 + 1) *
          (2 * pairK η₀ d.H * (4 / (c' ^ 2 * d.rhoLo ^ 2)) / d.r ^ 2) :=
          mul_le_mul_of_nonneg_right (hcard N₀ N) (by have := d.r_pos; positivity)
      _ ≤ (((d.X - d.lo) * d.rhoHi / 2 + 1) * c') *
          (2 * pairK η₀ d.H * (4 / (c' ^ 2 * d.rhoLo ^ 2)) / d.r ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by have := d.r_pos; positivity)
          have := d.lo_lt_X
          nlinarith [mul_pos (sub_pos.mpr this) hρhi]
      _ = C1 / c' := by
          rw [hC1]; field_simp; ring
  have hz0 : 0 ≤ ∑ k ∈ d.blockSet c' N₀ N, a k :=
    Finset.sum_nonneg fun k hk => by
      have hk' := Finset.mem_filter.mp hk
      have hK := pairK_nonneg η₀ d.H
      rw [ha]; positivity
  have hz1 : ∑ k ∈ d.blockSet c' N₀ N, a k ≤ 1 / 2 := by
    refine hsum.trans ?_
    rw [div_le_iff₀ hc']
    linarith
  have hexp : Real.exp (∑ k ∈ d.blockSet c' N₀ N, a k) ≤ 1 + 2 * (∑ k ∈ d.blockSet c' N₀ N, a k) := by
    set z := ∑ k ∈ d.blockSet c' N₀ N, a k with hz
    rcases hz0.eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have := Real.exp_bound_div_one_sub_of_interval' hpos (by linarith : z < 1)
      have h2 : 1 / (1 - z) ≤ 1 + 2 * z := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      linarith
  calc ∏ k ∈ Finset.Ioc N₀ N, bumpRatio d c' η₀ x k ≤ _ := hprod
    _ ≤ 1 + 2 * (∑ k ∈ d.blockSet c' N₀ N, a k) := hexp
    _ ≤ 1 + 2 * (C1 / c') := by linarith
    _ ≤ 1 + bumpC' d η₀ / c' := by
        have : bumpC' d η₀ = 4 * C1 := by rw [bumpC', hC1]
        rw [this]
        have : 0 ≤ C1 / c' := by positivity
        have e : 4 * C1 / c' = 4 * (C1 / c') := by ring
        rw [e]
        linarith

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.bumpFactor_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumpFactor_one_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.bumpFactor_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumpFactor_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.bumpFactor_le_one_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumpFactor_le_one_add

end FormalResearch.ModularBootstrap.Upper.Bump
