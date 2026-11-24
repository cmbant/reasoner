module

public import FormalResearch.ModularBootstrap.Upper.Positivity.RegionOne

/-!
# Proposition I, general level: the overshoot window and the final comparison (`ut:I`, `ut:T2`)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, Proposition I (`ut:I`) and Theorem T2 (`ut:T2`),
Region I.  `RegionOne` proves the two regions at `f = 1` for the designs `D(N, η_*, d)`.  This module proves the
parts that depend neither on `f` nor on the family; they are the cores of `proposition_I_a_sig` and
`proposition_I_b_sig` and are used at `f = 2` by the two-zero comb of `ut:T2` (`TwoLevel.TwoZeroRegionOne`).  Folding
this module into `RegionOne`, which then re-derives both from these lemmas, is the pending in-place generalisation:

* `pos_of_lower_hankel`: from a lower bound `Q ≤ h e^{c'L}` and the `SD_G` bound `e^{c'L} ‖ĥ‖ ≤ K √(c'/x)`
  one gets `h - Re ĥ > 0` as soon as `K √(2/ξ_*) √c' < Q` (`x ≥ ξ_*/2`);
* `pow_overshoot_gen`: `(2/π)^a c'^{2a/5} ≤ (2/(π u))^a` for `0 < u ≤ c'^{-2/5}`;
* `designProfile_overshoot_lower`: **the overshoot of a finite modification at level `f`** on
  `ξ_* + λ Σ₀ ≤ x ≤ ξ_* + c'^{-2/5}`: `Re h₀^D e^{c'L} ≥ c (2/(π(x - ξ_*)))^{2 n₁}` (`n₁ = f - 1/4`), uniformly on
  the family `|σ_k| ≤ M`, `0 ≤ ε'_k ≤ E λ` of `lemma_P_b` (`lemma_P_b`: `B_D ≥ ½ B_ref`; `band_overshoot_K5`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Positivity

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Saddle FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Holes FormalResearch.ModularBootstrap.Upper.Window

/-- **The final comparison of Region I**: `Q ≤ h e^{c'L}`, `e^{c'L} ‖ĥ‖ ≤ K √(c'/x)` and
`K √(2/ξ_*) √c' < Q` give `h - Re ĥ > 0` (for `x ≥ ξ_*/2`). -/
lemma pos_of_lower_hankel {c' x E K Hre Q : ℝ} {Hh : ℂ} (hc' : 0 < c') (hxhalf : xiStar / 2 ≤ x)
    (hK0 : 0 ≤ K) (hE : 0 < E) (hglob : E * ‖Hh‖ ≤ K * √(c' / x)) (hQ : Q ≤ Hre * E)
    (hbig : K * √(2 / xiStar) * √c' < Q) : 0 < Hre - Hh.re :=
  sub_pos_of_bounds hE (Complex.re_le_norm Hh) hQ (edge_bound_sqrt hK0 hc' hxhalf hglob) hbig

/-- `(2/π)^a c'^{2a/5} ≤ (2/(π u))^a` for `0 < u ≤ c'^{-2/5}`, `a ≥ 0`. -/
lemma pow_overshoot_gen {c' u a : ℝ} (hc' : 0 < c') (hu : 0 < u) (huup : u ≤ c' ^ (-(2 / 5 : ℝ)))
    (ha : 0 ≤ a) : (2 / π) ^ a * c' ^ (2 / 5 * a : ℝ) ≤ (2 / (π * u)) ^ a := by
  have hπ := Real.pi_pos
  have hw : 0 < c' ^ (2 / 5 : ℝ) := Real.rpow_pos_of_pos hc' _
  have hwu : c' ^ (2 / 5 : ℝ) ≤ 1 / u := by
    rw [le_div_iff₀ hu]
    have hneg : c' ^ (-(2 / 5 : ℝ)) = (c' ^ (2 / 5 : ℝ))⁻¹ := Real.rpow_neg hc'.le _
    rw [hneg] at huup
    calc c' ^ (2 / 5 : ℝ) * u ≤ c' ^ (2 / 5 : ℝ) * (c' ^ (2 / 5 : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_left huup hw.le
      _ = 1 := mul_inv_cancel₀ hw.ne'
  have h1 : (2 / π) * c' ^ (2 / 5 : ℝ) ≤ 2 / (π * u) := by
    calc (2 / π) * c' ^ (2 / 5 : ℝ) ≤ (2 / π) * (1 / u) :=
          mul_le_mul_of_nonneg_left hwu (by positivity)
      _ = 2 / (π * u) := by field_simp
  have h2 := Real.rpow_le_rpow (by positivity) h1 ha
  rwa [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hc'.le] at h2

/-- **The overshoot window of Region I(b) at level `f`** (`ut:I`(b), `ut:T2` Region I(b)): for every `f ≥ 1`,
`N ≥ f`, `M`, `E ≥ 0` there are `Σ₀ > 0` and `c > 0` such that for large `c'`, every finite modification with
`|σ_k| ≤ M` (`f ≤ k ≤ N`), `0 ≤ ε'_k ≤ E λ` (`f < k ≤ N`) and every `x` with
`ξ_* + λ Σ₀ ≤ x ≤ ξ_* + c'^{-2/5}`:
`Re h₀^D(x) e^{c' L(x)} ≥ c (2/(π(x - ξ_*)))^{2 n₁}`, `n₁ = f - 1/4`.  `Σ₀` is chosen so that `lemma_P_b` gives
`B_D ≥ ½ B_ref` and `x` lies in a cell `n ≥ max(N_ov, f + 1)` of `band_overshoot_K5`. -/
theorem designProfile_overshoot_lower (f N : ℕ) (hf : 1 ≤ f) (hfN : f ≤ N) (M E : ℝ) :
    ∃ Sg0 cc : ℝ, 0 < Sg0 ∧ 0 < cc ∧ ∀ᶠ c' in atTop, ∀ σ ε : ℕ → ℝ,
      (∀ k, f ≤ k → k ≤ N → |σ k| ≤ M) →
      (∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ E * lambdaComb c') →
      ∀ x : ℝ, xiStar + lambdaComb c' * Sg0 ≤ x → x ≤ xiStar + c' ^ (-(2 / 5 : ℝ)) →
        cc * (2 / (π * (x - xiStar))) ^ (2 * n1Comb f) ≤
          (designProfile c' f N (1 / 4) σ ε (x : ℂ)).re * Real.exp (c' * edgeL x) := by
  obtain ⟨CP, hCP, hP⟩ := lemma_P_b f N hf hfN M E
  obtain ⟨Nov, cT, hNov, hcT, hov⟩ := band_overshoot_K5 (η₀ := 1 / 4) (by norm_num) le_rfl
  obtain ⟨Cg', hCg', hgapev⟩ := siteGap_eventually_le
  have hxi := xiStar_pos
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = max (phiQuantile ((N : ℝ) + 2)) M := ⟨_, rfl⟩
  obtain ⟨Mov, hMov⟩ : ∃ Mov : ℕ, Mov = max Nov (f + 1) := ⟨_, rfl⟩
  have hMov1 : 1 ≤ Mov := by omega
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hΦ0 : 0 ≤ phiQuantile ((Mov : ℝ) + 2) := phiQuantile_add_two_nonneg Mov
  have hΦN0 : 0 < phiQuantile ((N : ℝ) + 2) := phiQuantile_add_two_pos N
  have hsge : phiQuantile ((N : ℝ) + 2) ≤ s := hsdef ▸ le_max_left _ _
  have hMs : M ≤ s := hsdef ▸ le_max_right _ _
  have _hs0 : 0 < s := lt_of_lt_of_le hΦN0 hsge
  have hCPl : 0 ≤ CP / Real.log 2 := div_nonneg hCP hlog2.le
  obtain ⟨Sg0, hSg0⟩ : ∃ Sg0 : ℝ, Sg0 = 4 * s + CP / Real.log 2 + phiQuantile ((Mov : ℝ) + 2) + 1 :=
    ⟨_, rfl⟩
  have hSg0pos : 0 < Sg0 := by rw [hSg0]; linarith
  have hS1 : 4 * s ≤ Sg0 := by rw [hSg0]; linarith
  have hS2 : CP / Real.log 2 ≤ Sg0 := by rw [hSg0]; linarith
  have hS3 : phiQuantile ((Mov : ℝ) + 2) ≤ Sg0 := by rw [hSg0]; linarith
  have hS4 : phiQuantile ((N : ℝ) + 2) < Sg0 := by rw [hSg0]; linarith
  obtain ⟨cc, hcc⟩ : ∃ cc : ℝ, cc = (1 / 2) * cT * (1 / Real.cosh (π * (xiStar + 1) / 2) ^ 2) := ⟨_, rfl⟩
  have hccpos : 0 < cc := by rw [hcc]; positivity
  refine ⟨Sg0, cc, hSg0pos, hccpos, ?_⟩
  have hlamM : ∀ᶠ c' in atTop, lambdaComb c' * M ≤ xiStar := by
    have h := tendsto_lambdaComb_atTop.mul_const M
    rw [zero_mul] at h
    exact h.eventually_le_const hxi
  have hlamE : ∀ᶠ c' in atTop, E * lambdaComb c' ≤ 1 / 2 := by
    have h := tendsto_lambdaComb_atTop.const_mul E
    rw [mul_zero] at h
    exact h.eventually_le_const (by norm_num)
  filter_upwards [hP (η₀ := 1 / 4) (by norm_num) le_rfl, hov, hgapev, hlamM, hlamE,
    tail_ne_zero_of_refComb_ne_zero f N hfN (η₀ := 1 / 4) (by norm_num) le_rfl,
    eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (1 : ℝ)]
    with c' hPc hovc hgapc hlM hlE htailc hcpos hc1 σ ε hM hεE x hx1 hx2
  obtain ⟨hgap_k, hgap_1_bd, hcd1_bd, hgap_half⟩ := hgapc
  have hlam : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hcpos) _
  have hlam0 : 0 ≤ lambdaComb c' := hlam.le
  have hu1 : c' ^ (-(2 / 5 : ℝ)) ≤ 1 := rpow_neg_two_fifths_le_one hc1
  have hux : lambdaComb c' * Sg0 ≤ x - xiStar := by linarith
  have hupos : 0 < x - xiStar := lt_of_lt_of_le (mul_pos hlam hSg0pos) hux
  have hx0 : 0 < x := by linarith
  have h4s : 4 * s * lambdaComb c' ≤ 1 * (lambdaComb c' * Sg0) := by
    have := mul_le_mul_of_nonneg_left hS1 hlam0
    linarith
  have hsite := design_site_facts (s := s) (x := x) (u := lambdaComb c' * Sg0) hlam0 hlM hMs h4s
    (mul_pos hlam hSg0pos) (by linarith) hM
  have hεw : ∀ k, f < k → k ≤ N → 0 ≤ ε k ∧ ε k ≤ 1 / 2 := fun k hk hkN =>
    ⟨(hεE k hk hkN).1, (hεE k hk hkN).2.trans hlE⟩
  obtain ⟨r, hr, hr0, hrpos⟩ := designComb_ofReal hcpos (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num) hgap_half f N σ ε hsite hεw hfN
  have hχMov : chiQuantile c' (Mov : ℝ) ≤ x := by
    have h := (refSite_bounds hcpos hMov1 (le_refl Mov)).2
    have := mul_le_mul_of_nonneg_left hS3 hlam0
    linarith
  have hχ1 : chiQuantile c' (f : ℝ) < x := by
    have h1 : chiQuantile c' (f : ℝ) ≤ xiStar + lambdaComb c' * phiQuantile ((N : ℝ) + 2) :=
      (refSite_bounds hcpos hf hfN).2
    have h2 := mul_lt_mul_of_pos_left hS4 hlam
    linarith
  obtain ⟨-, -, -, -, h0_norm⟩ := refComb_re_nonneg_of_gt hcpos (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num) hgap_half hf hχ1
  have hsech : 0 < 1 / Real.cosh (π * x / 2) ^ 2 := by positivity
  have hov1 := hovc f x hf (hMov ▸ hχMov)
  have hsechlow := sech_lower hx0.le (by linarith : x ≤ xiStar + 1)
  have hnormD : ‖designComb c' f N (1 / 4) σ ε (x : ℂ)‖ = r := by
    rw [hr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hHre : (designProfile c' f N (1 / 4) σ ε (x : ℂ)).re =
      1 / Real.cosh (π * x / 2) ^ 2 * r := by
    rw [designProfile_ofReal hr, Complex.ofReal_re]
  have hE : 0 < Real.exp (c' * slitL x) := Real.exp_pos _
  have hPi : 0 < 2 / (π * (x - xiStar)) := by have := Real.pi_pos; positivity
  have hrhs : 0 < cT * (1 / Real.cosh (π * x / 2) ^ 2) *
      (2 / (π * (x - xiStar))) ^ (2 * n1Comb f) :=
    mul_pos (mul_pos hcT hsech) (Real.rpow_pos_of_pos hPi _)
  have hovpos : 0 < h0Comb c' f (1 / 4) x * Real.exp (c' * slitL x) := lt_of_lt_of_le hrhs hov1
  have hh0pos : 0 < h0Comb c' f (1 / 4) x := by
    by_contra hneg
    push Not at hneg
    exact absurd hovpos (not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg hneg hE.le))
  have hrefpos : 0 < ‖refComb c' f (1 / 4) (x : ℂ)‖ := by
    rw [h0_norm] at hh0pos
    exact pos_of_mul_pos_right hh0pos hsech.le
  have hrp : 0 < r := hrpos (htailc x (norm_pos_iff.mp hrefpos))
  have h4s' : xiStar + 4 * max (phiQuantile ((N : ℝ) + 2)) M * lambdaComb c' ≤ x := by
    rw [← hsdef]; linarith
  have hPbd := hPc σ ε hM hεE x h4s'
  rw [hnormD] at hPbd
  have hlogle : |Real.log (r / ‖refComb c' f (1 / 4) (x : ℂ)‖)| ≤ Real.log 2 := by
    refine hPbd.trans ?_
    have hl : lambdaComb c' / (x - xiStar) ≤ 1 / Sg0 := by
      rw [div_le_div_iff₀ hupos hSg0pos]; linarith
    calc CP * (lambdaComb c' / (x - xiStar)) ≤ CP * (1 / Sg0) := mul_le_mul_of_nonneg_left hl hCP
      _ = CP / Sg0 := by ring
      _ ≤ Real.log 2 := by
        rw [div_le_iff₀ hSg0pos]
        have := (div_le_iff₀ hlog2).mp hS2
        linarith
  have hr_ge := half_le_of_log_le hrp hrefpos hlogle
  have hex : Real.exp (c' * slitL x) = Real.exp (c' * edgeL x) := by rw [exp_slitL_eq_edgeL hx0.le]
  rw [hHre, ← hex, hcc]
  have hov2 : cT * (1 / Real.cosh (π * x / 2) ^ 2) * (2 / (π * (x - xiStar))) ^ (2 * n1Comb f) ≤
      1 / Real.cosh (π * x / 2) ^ 2 * ‖refComb c' f (1 / 4) (x : ℂ)‖ * Real.exp (c' * slitL x) := by
    rw [← h0_norm]; exact hov1
  have hsl : 0 ≤ 1 / Real.cosh (π * (xiStar + 1) / 2) ^ 2 := by positivity
  have hP0 : 0 ≤ (2 / (π * (x - xiStar))) ^ (2 * n1Comb f) := Real.rpow_nonneg hPi.le _
  have := lowerH_alg hcT.le hsl hP0 hsech.le hE.le hsechlow le_rfl hov2 hr_ge
  calc 1 / 2 * cT * (1 / Real.cosh (π * (xiStar + 1) / 2) ^ 2) * (2 / (π * (x - xiStar))) ^ (2 * n1Comb f)
      ≤ 1 / Real.cosh (π * x / 2) ^ 2 * r * Real.exp (c' * slitL x) := this
    _ = _ := by rw [hex]

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.pos_of_lower_hankel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pos_of_lower_hankel

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.pow_overshoot_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pow_overshoot_gen

/-- info: 'FormalResearch.ModularBootstrap.Upper.Positivity.designProfile_overshoot_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms designProfile_overshoot_lower

end FormalResearch.ModularBootstrap.Upper.Positivity
