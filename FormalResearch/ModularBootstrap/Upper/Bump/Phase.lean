module

public import FormalResearch.ModularBootstrap.Upper.Bump.Nearest

/-!
# The bumped comb is an admissible finite modification with pair change `O(1/c')` (`fw:e3.4`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, "Edge-phase stability": the bump changes the heights of
`O(c')` pairs by `O(c'^{-1})` each in the squared form, so that `Σ_{bump} ℓ_k² = O(c'^{-1})` and the saddle
(`C²`) bounds of Lemma `Φ` / `SD_V` are preserved.  In this formalisation the pair-change interface of
`Upper.Design.PerturbPhi` (`designPairChange`, `DesignAdmissible`) carries that statement.

* `bumped_pairChange`: `designPairChange` of the bumped comb is at most that of the base comb plus `C/c'`
  (`fw:e3.4`);
* `bumped_admissible`: the bumped data are `DesignAdmissible` whenever the base data are.

`PhaseHyp` itself (the hypothesis of `Ramped.phase_package`) is assembled in `PhaseHyp.lean`.  All results are
proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Bump

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Design
open scoped Classical

/-- The constant of `bumped_pairChange`. -/
noncomputable def pairChangeC (d : BumpData) : ℝ :=
  d.H ^ 2 * (((d.X - d.lo) * d.rhoHi / 2 + 1) * (4 / d.rhoLo ^ 2))

/-- **Pair change of the bump** (`fw:e3.4`): raising the block heights from `η₀ ℓ_k` to `η_big ℓ_k` adds at most
`C/c'` to the total pair change, uniformly in the base data and the cuts. -/
theorem bumped_pairChange (d : BumpData) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ (f N₀ N : ℕ) (σ₀ ε₀ : ℕ → ℝ), f ≤ N₀ → N₀ ≤ N →
      designPairChange c' f N η₀ (bumpSigma c' N₀ σ₀) (bumpEps d c' N₀ η₀ ε₀) ≤
        designPairChange c' f N₀ η₀ σ₀ ε₀ + pairChangeC d / c' := by
  have hρlo := d.rhoLo_pos
  have hρhi := d.rhoHi_pos
  filter_upwards [block_gap_bounds d, block_card_le d, eventually_ge_atTop (1 : ℝ)]
    with c' hbg hcard hc1 f N₀ N σ₀ ε₀ hfN₀ hN
  have hc' : 0 < c' := lt_of_lt_of_le one_pos hc1
  set σ' := bumpSigma c' N₀ σ₀ with hσ'
  set ε' := bumpEps d c' N₀ η₀ ε₀ with hε'
  have hNf : N - f = (N₀ - f) + (N - N₀) := by omega
  have hsite_f : designSite c' σ' f = designSite c' σ₀ f := designSite_bumpSigma_of_le hfN₀
  unfold designPairChange
  rw [hNf, Finset.sum_range_add, hsite_f]
  have hfirst : ∑ i ∈ Finset.range (N₀ - f),
      (|ε' (f + 1 + i) ^ 2 - (η₀ * siteGap c' (f + 1 + i)) ^ 2| +
        2 * |designSite c' σ' (f + 1 + i) - chiQuantile c' ((f + 1 + i : ℕ) : ℝ)|) =
      ∑ i ∈ Finset.range (N₀ - f),
      (|ε₀ (f + 1 + i) ^ 2 - (η₀ * siteGap c' (f + 1 + i)) ^ 2| +
        2 * |designSite c' σ₀ (f + 1 + i) - chiQuantile c' ((f + 1 + i : ℕ) : ℝ)|) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hk : f + 1 + i ≤ N₀ := by have := Finset.mem_range.mp hi; omega
    rw [designSite_bumpSigma_of_le hk, hε', bumpEps_of_le hk]
  have hsecond : ∑ i ∈ Finset.range (N - N₀),
      (|ε' (f + 1 + (N₀ - f + i)) ^ 2 - (η₀ * siteGap c' (f + 1 + (N₀ - f + i))) ^ 2| +
        2 * |designSite c' σ' (f + 1 + (N₀ - f + i)) - chiQuantile c' ((f + 1 + (N₀ - f + i) : ℕ) : ℝ)|) ≤
      ∑ i ∈ Finset.range (N - N₀), (if d.InBlock c' (N₀ + 1 + i) then d.H ^ 2 * siteGap c' (N₀ + 1 + i) ^ 2 else 0) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have e : f + 1 + (N₀ - f + i) = N₀ + 1 + i := by omega
    rw [e]
    have hk' : N₀ < N₀ + 1 + i := by omega
    rw [designSite_bumpSigma_of_gt hc' hk', sub_self, abs_zero, mul_zero, add_zero]
    have hℓ0 : 0 ≤ siteGap c' (N₀ + 1 + i) := siteGap_nonneg hc' (by omega)
    by_cases hb : d.InBlock c' (N₀ + 1 + i)
    · simp only [hb, ↓reduceIte]; rw [hε', bumpEps_of_gt_block hk' hb]
      have h1 : 0 ≤ (d.H * siteGap c' (N₀ + 1 + i)) ^ 2 - (η₀ * siteGap c' (N₀ + 1 + i)) ^ 2 := by
        have : η₀ ≤ d.H := hη₀1.trans d.H_ge
        have := mul_le_mul_of_nonneg_right this hℓ0
        nlinarith [mul_nonneg hη₀0 hℓ0]
      rw [abs_of_nonneg h1]
      nlinarith [sq_nonneg (η₀ * siteGap c' (N₀ + 1 + i))]
    · simp only [hb, ↓reduceIte]; rw [hε', bumpEps_of_gt_not_block hk' hb]
      simp
  have hsum : ∑ i ∈ Finset.range (N - N₀),
      (if d.InBlock c' (N₀ + 1 + i) then d.H ^ 2 * siteGap c' (N₀ + 1 + i) ^ 2 else 0) ≤
      pairChangeC d / c' := by
    have e1 : ∑ i ∈ Finset.range (N - N₀),
        (if d.InBlock c' (N₀ + 1 + i) then d.H ^ 2 * siteGap c' (N₀ + 1 + i) ^ 2 else 0) =
        ∑ k ∈ d.blockSet c' N₀ N, d.H ^ 2 * siteGap c' k ^ 2 := by
      rw [BumpData.blockSet, Finset.sum_filter,
        sum_Ioc_eq_sum_range (fun k => if d.InBlock c' k then d.H ^ 2 * siteGap c' k ^ 2 else 0)]
    rw [e1]
    have hterm : ∀ k ∈ d.blockSet c' N₀ N, d.H ^ 2 * siteGap c' k ^ 2 ≤
        d.H ^ 2 * (4 / (c' ^ 2 * d.rhoLo ^ 2)) := by
      intro k hk
      have hk' := Finset.mem_filter.mp hk
      have hk1 : 1 ≤ k := by have := (Finset.mem_Ioc.mp hk'.1).1; omega
      obtain ⟨hlo, hhi⟩ := hbg k hk1 hk'.2
      have hℓ0 : 0 ≤ siteGap c' k := siteGap_nonneg hc' hk1
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      calc siteGap c' k ^ 2 ≤ (2 / (c' * d.rhoLo)) ^ 2 := pow_le_pow_left₀ hℓ0 hhi 2
        _ = 4 / (c' ^ 2 * d.rhoLo ^ 2) := by field_simp; ring
    calc ∑ k ∈ d.blockSet c' N₀ N, d.H ^ 2 * siteGap c' k ^ 2
        ≤ ∑ _k ∈ d.blockSet c' N₀ N, d.H ^ 2 * (4 / (c' ^ 2 * d.rhoLo ^ 2)) :=
          Finset.sum_le_sum hterm
      _ = ((d.blockSet c' N₀ N).card : ℝ) * (d.H ^ 2 * (4 / (c' ^ 2 * d.rhoLo ^ 2))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (((d.X - d.lo) * d.rhoHi / 2 + 1) * c') * (d.H ^ 2 * (4 / (c' ^ 2 * d.rhoLo ^ 2))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          refine (hcard N₀ N).trans ?_
          have := d.lo_lt_X
          nlinarith [mul_pos (sub_pos.mpr this) hρhi]
      _ = pairChangeC d / c' := by
          unfold pairChangeC; field_simp
  rw [hfirst]
  linarith

/-- The bumped data are admissible whenever the base data are (`f ≥ 1`; the threshold depends on `f`, `η₀` and
`η_big` only). -/
theorem bumped_admissible (d : BumpData) (f : ℕ) (hf : 1 ≤ f) {η₀ : ℝ} (hη₀0 : 0 ≤ η₀)
    (hη₀1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, ∀ (N₀ N : ℕ) (σ₀ ε₀ : ℕ → ℝ), f ≤ N₀ → N₀ ≤ N →
      DesignAdmissible c' f N₀ η₀ σ₀ ε₀ →
      DesignAdmissible c' f N η₀ (bumpSigma c' N₀ σ₀) (bumpEps d c' N₀ η₀ ε₀) := by
  obtain ⟨Cg, hCg, h_ev⟩ := siteGap_eventually_le
  have hlam : ∀ᶠ c' in atTop, d.H * (Cg * lambdaComb c') ≤ 1 / 8 := by
    have := tendsto_lambdaComb_atTop.const_mul (d.H * Cg)
    simp only [mul_zero] at this
    filter_upwards [this.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 8)] with c' h
    linarith [mul_assoc d.H Cg (lambdaComb c')]
  filter_upwards [designAdmissible_of_nonneg f hf hη₀0 hη₀1, h_ev, hlam, eventually_gt_atTop 0]
    with c' hadm ⟨hmono, hg1, hg2, hgap⟩ hl hc' N₀ N σ₀ ε₀ hfN₀ hN hbase
  refine hadm N _ _ (hfN₀.trans hN) ?_ ?_ ?_
  · rw [designSite_bumpSigma_of_le hfN₀]; exact hbase.first
  · intro i hi
    by_cases hk : f + 1 + i ≤ N₀
    · rw [designSite_bumpSigma_of_le hk]
      exact hbase.site i (by omega)
    · rw [designSite_bumpSigma_of_gt hc' (by omega)]
      exact chi_nonneg hc' (by omega)
  · intro i hi
    by_cases hk : f + 1 + i ≤ N₀
    · rw [bumpEps_of_le hk]
      exact hbase.width i (by omega)
    · have hk' : N₀ < f + 1 + i := by omega
      have hℓ0 : 0 ≤ siteGap c' (f + 1 + i) := siteGap_nonneg hc' (by omega)
      have hℓ : siteGap c' (f + 1 + i) ≤ Cg * lambdaComb c' :=
        (hmono _ (by omega)).trans (hg1.trans hg2)
      have hH : (if d.InBlock c' (f + 1 + i) then d.H else η₀) ≤ d.H := by
        split_ifs
        · exact le_rfl
        · exact hη₀1.trans d.H_ge
      have hH0 : 0 ≤ (if d.InBlock c' (f + 1 + i) then d.H else η₀) := by
        split_ifs
        · exact d.H_pos.le
        · exact hη₀0
      have hbound : (if d.InBlock c' (f + 1 + i) then d.H else η₀) * siteGap c' (f + 1 + i) ≤ 1 / 8 := by
        calc _ ≤ d.H * (Cg * lambdaComb c') := mul_le_mul hH hℓ hℓ0 d.H_pos.le
          _ ≤ 1 / 8 := hl
      simp only [bumpEps, not_le.mpr hk', ite_false]
      rw [abs_of_nonneg (mul_nonneg hH0 hℓ0)]
      exact hbound

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.bumped_pairChange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumped_pairChange

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.bumped_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bumped_admissible

end FormalResearch.ModularBootstrap.Upper.Bump
