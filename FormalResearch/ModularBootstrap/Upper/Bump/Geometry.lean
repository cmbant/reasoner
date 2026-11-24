module

public import FormalResearch.ModularBootstrap.Upper.Bump.Defs
public import FormalResearch.ModularBootstrap.Upper.Bump.Sum

/-!
# Geometry of the quantile sites on the bump block

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, the bump block "lies a fixed distance from the Airy
tip; their count is `O_p(c')`, their gaps `ℓ_n ≍_p c'^{-1}`" and the separation
`|χ_{n+j} - χ_n| ≥ c_I |j| / c'` used in `fw:e3.2a` and `fw:e3.3` (TeX issue T8).

On the block `ξ_* + 2 r_p ≤ χ_k ≤ X_p` (`BumpData.InBlock`):

* `block_gap_bounds`: `2/(c' ρ_U(X_p+1)) ≤ ℓ_k ≤ 2/(c' ρ_U(ξ_*+2r_p))`;
* `block_spacing`: `χ_j - χ_k ≥ (j - k) · 2/(c' ρ_U(X_p+1))` for block indices `k ≤ j`;
* `block_card_le`: the block has at most `(X_p - ξ_* - 2r_p) c' ρ_U(X_p+1)/2 + 1` indices;
* `block_sum_le`: `Σ_{k ∈ block} ℓ_k² / ((x - χ_k)² + ℓ_k²) ≤ 2 + 4 (ρ_U(X_p+1)/ρ_U(ξ_*+2r_p))²` for every real `x`
  (the two-case argument of TeX issue T8 is the `sum_inv_quad_le` splitting at `u`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Bump

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Window
open scoped Classical

lemma chi_mono_nat {c' : ℝ} (hc' : 0 < c') {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    chiQuantile c' (a : ℝ) ≤ chiQuantile c' (b : ℝ) := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  exact (chiQuantile_strictMonoOn hc').monotoneOn (Set.mem_Ici.mpr (by linarith))
    (Set.mem_Ici.mpr (by linarith)) hab'

lemma siteGap_eq (c' : ℝ) (k : ℕ) :
    siteGap c' k = chiQuantile c' ((k + 1 : ℕ) : ℝ) - chiQuantile c' (k : ℝ) := by
  unfold siteGap
  push_cast
  rfl

/-- On the block the quantile gaps are comparable to `1/c'`. -/
theorem block_gap_bounds (d : BumpData) :
    ∀ᶠ c' in atTop, ∀ k : ℕ, 1 ≤ k → d.InBlock c' k →
      2 / (c' * d.rhoHi) ≤ siteGap c' k ∧ siteGap c' k ≤ 2 / (c' * d.rhoLo) := by
  obtain ⟨_, _, h_ev⟩ := siteGap_eventually_le
  filter_upwards [h_ev, eventually_gt_atTop 0] with c' ⟨hmono, _, _, hℓ1⟩ hc' k hk hb
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk14 : (1 / 4 : ℝ) ≤ k := by linarith
  have hξ : xiStar ≤ chiQuantile c' (k : ℝ) := (chiQuantile_spec hc' hk14).1
  have hρlo := d.rhoLo_pos
  have hρhi := d.rhoHi_pos
  refine ⟨?_, ?_⟩
  · -- lower bound: `χ'_{k+1} ≤ ℓ_k`
    have hprev := chiDeriv_le_siteGap_prev hc' (k := k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hprev
    have hχ1 : chiQuantile c' ((k + 1 : ℕ) : ℝ) ≤ d.X + 1 := by
      have := siteGap_eq c' k
      have h2 := hmono k hk
      linarith [hb.2]
    have hχ1lo : d.lo ≤ chiQuantile c' ((k + 1 : ℕ) : ℝ) := by
      have := siteGap_eq c' k
      have h0 : 0 ≤ siteGap c' k := siteGap_nonneg hc' hk
      linarith [hb.1]
    have hρ1 : rhoU (chiQuantile c' ((k + 1 : ℕ) : ℝ)) ≤ d.rhoHi :=
      rhoU_strictMonoOn.monotoneOn
        (Set.mem_Ici.mpr (d.xiStar_lt_lo.le.trans hχ1lo)) (Set.mem_Ici.mpr (by
          have := d.lo_lt_X; linarith [d.xiStar_lt_lo])) hχ1
    have hρ1pos : 0 < rhoU (chiQuantile c' ((k + 1 : ℕ) : ℝ)) :=
      rhoU_pos (lt_of_lt_of_le d.xiStar_lt_lo hχ1lo)
    refine le_trans ?_ hprev
    unfold chiDeriv
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left hρ1 hc'.le)
  · have hup : siteGap c' k ≤ chiDeriv c' (k : ℝ) := siteGap_le_chiDeriv hc' hk
    have hρk : d.rhoLo ≤ rhoU (chiQuantile c' (k : ℝ)) :=
      rhoU_strictMonoOn.monotoneOn (Set.mem_Ici.mpr d.xiStar_lt_lo.le) (Set.mem_Ici.mpr hξ) hb.1
    refine le_trans hup ?_
    unfold chiDeriv
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left hρk hc'.le)

/-- The block sites are separated: `χ_j - χ_k ≥ (j - k) · 2/(c' ρ_U(X_p + 1))`. -/
theorem block_spacing (d : BumpData) :
    ∀ᶠ c' in atTop, ∀ k j : ℕ, 1 ≤ k → k ≤ j → d.InBlock c' k → d.InBlock c' j →
      2 / (c' * d.rhoHi) * ((j : ℝ) - k) ≤ chiQuantile c' (j : ℝ) - chiQuantile c' (k : ℝ) := by
  filter_upwards [block_gap_bounds d, eventually_gt_atTop 0] with c' hgap hc' k j hk hkj hbk hbj
  induction j, hkj using Nat.le_induction with
  | base => simp
  | succ j hkj ih =>
    have hj1 : 1 ≤ j := le_trans hk hkj
    have hbj' : d.InBlock c' j := by
      refine ⟨hbk.1.trans (chi_mono_nat hc' hk hkj), (chi_mono_nat hc' hj1 (Nat.le_succ j)).trans hbj.2⟩
    have h1 := ih hbj'
    have h2 := (hgap j hj1 hbj').1
    have h3 := siteGap_eq c' j
    simp only [Nat.cast_add, Nat.cast_one] at h3 ⊢
    nlinarith

/-- The block has `O(c')` indices. -/
theorem block_card_le (d : BumpData) :
    ∀ᶠ c' in atTop, ∀ N₀ N : ℕ,
      ((d.blockSet c' N₀ N).card : ℝ) ≤ (d.X - d.lo) * c' * d.rhoHi / 2 + 1 := by
  filter_upwards [block_spacing d, eventually_gt_atTop 0] with c' hsp hc' N₀ N
  have hρ := d.rhoHi_pos
  have hXlo := d.lo_lt_X
  set S := d.blockSet c' N₀ N with hS
  have hmem : ∀ k ∈ S, 1 ≤ k ∧ d.InBlock c' k := fun k hk => by
    unfold BumpData.blockSet at hS
    rw [hS, Finset.mem_filter, Finset.mem_Ioc] at hk
    exact ⟨by omega, hk.2⟩
  rcases S.eq_empty_or_nonempty with he | hne
  · rw [he]; simp; positivity
  set m := S.min' hne with hm
  set M := S.max' hne with hM
  have hmS : m ∈ S := Finset.min'_mem S hne
  have hMS : M ∈ S := Finset.max'_mem S hne
  have hmM : m ≤ M := Finset.min'_le S M hMS
  have hsub : S ⊆ Finset.Icc m M := fun k hk =>
    Finset.mem_Icc.mpr ⟨Finset.min'_le S k hk, Finset.le_max' S k hk⟩
  have hcard : S.card ≤ M + 1 - m := by
    have := Finset.card_le_card hsub
    simpa using this
  have hspc := hsp m M (hmem m hmS).1 hmM (hmem m hmS).2 (hmem M hMS).2
  have hdist : chiQuantile c' (M : ℝ) - chiQuantile c' (m : ℝ) ≤ d.X - d.lo := by
    linarith [(hmem M hMS).2.2, (hmem m hmS).2.1]
  have hMm : ((M : ℝ) - m) ≤ (d.X - d.lo) * c' * d.rhoHi / 2 := by
    have hδ : 0 < 2 / (c' * d.rhoHi) := by positivity
    have h1 : 2 / (c' * d.rhoHi) * ((M : ℝ) - m) ≤ d.X - d.lo := hspc.trans hdist
    have h2 : (M : ℝ) - m ≤ (d.X - d.lo) / (2 / (c' * d.rhoHi)) := by
      rw [le_div_iff₀ hδ]; linarith
    refine h2.trans (le_of_eq ?_)
    field_simp
  calc (S.card : ℝ) ≤ ((M + 1 - m : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (M : ℝ) - m + 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    _ ≤ _ := by linarith

/-- The Lorentzian sum over the block is `O(1)`, uniformly in the base cut, the top cut and `x`. -/
theorem block_sum_le (d : BumpData) :
    ∀ᶠ c' in atTop, ∀ (N₀ N : ℕ) (x : ℝ),
      ∑ k ∈ d.blockSet c' N₀ N,
        siteGap c' k ^ 2 / ((x - chiQuantile c' (k : ℝ)) ^ 2 + siteGap c' k ^ 2) ≤
        2 + 4 * (d.rhoHi / d.rhoLo) ^ 2 := by
  filter_upwards [block_gap_bounds d, block_spacing d, eventually_gt_atTop 0]
    with c' hgap hsp hc' N₀ N x
  have hρlo := d.rhoLo_pos
  have hρhi := d.rhoHi_pos
  set L := 2 / (c' * d.rhoLo) with hL
  set δ := 2 / (c' * d.rhoHi) with hδ
  have hLpos : 0 < L := by positivity
  have hδpos : 0 < δ := by positivity
  set S := d.blockSet c' N₀ N with hS
  have hmem : ∀ k ∈ S, 1 ≤ k ∧ d.InBlock c' k := fun k hk => by
    rw [hS, BumpData.blockSet, Finset.mem_filter, Finset.mem_Ioc] at hk
    exact ⟨by omega, hk.2⟩
  have hterm : ∀ k ∈ S, siteGap c' k ^ 2 / ((x - chiQuantile c' (k : ℝ)) ^ 2 + siteGap c' k ^ 2) ≤
      1 / (1 + ((x - chiQuantile c' (k : ℝ)) / L) ^ 2) := by
    intro k hk
    obtain ⟨hk1, hkb⟩ := hmem k hk
    obtain ⟨hlo, hhi⟩ := hgap k hk1 hkb
    have hℓpos : 0 < siteGap c' k := lt_of_lt_of_le hδpos hlo
    set a := x - chiQuantile c' (k : ℝ) with ha
    have hℓL : siteGap c' k ≤ L := hhi
    rw [show 1 / (1 + (a / L) ^ 2) = L ^ 2 / (a ^ 2 + L ^ 2) by field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg a, mul_nonneg (sq_nonneg a) (sub_nonneg.mpr (pow_le_pow_left₀ hℓpos.le hℓL 2))]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hspS : ∀ k ∈ S, ∀ j ∈ S, k ≤ j →
      δ * ((j : ℝ) - k) ≤ chiQuantile c' (j : ℝ) - chiQuantile c' (k : ℝ) := fun k hk j hj hkj =>
    hsp k j (hmem k hk).1 hkj (hmem k hk).2 (hmem j hj).2
  have := sum_inv_quad_le (S := S) (p := fun k : ℕ => chiQuantile c' (k : ℝ)) hδpos hLpos hspS x
  refine this.trans (le_of_eq ?_)
  have : L / δ = d.rhoHi / d.rhoLo := by
    rw [hL, hδ]; field_simp
  rw [this]

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.block_gap_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms block_gap_bounds

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.block_spacing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms block_spacing

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.block_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms block_card_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.block_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms block_sum_le

end FormalResearch.ModularBootstrap.Upper.Bump
