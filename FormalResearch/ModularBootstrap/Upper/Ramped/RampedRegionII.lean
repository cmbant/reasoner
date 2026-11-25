module

public import FormalResearch.ModularBootstrap.Upper.Positivity.RegionII
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedFloor
public import FormalResearch.ModularBootstrap.Upper.Ramped.NearTipRatio

/-!
# Region II of Lemma U*, statements for an abstract modified comb (`rem:thmU` Steps (3), (4))

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Steps (3) and (4).

Consumers (the ramped comb of `Upper.Design`, `Upper.Membership`) verify `RampedHoleHyp` (site shifts, heights,
the pair at `k₀`) and the amplitude bound of `ut:II`, step (1).  This file turns those into the positivity of
`2g/Lev = twoG / levComb`:

* `ramped_nearTip_twoG` (Step (3)): `c_fl · min(1, 16η_n²)(1 - E) - amp ≤ 2g(c'x²/3)/Lev(x)` with the loss `E` of
  `rampedHoleLoss`, for every amplitude bound `‖ĥ₀‖ ≤ amp · Lev`;
* `nearTip_amp_le`: `vρ_∞(x; 3/4)(1 + w) ≤ C_v (x - ξ_*)^{5/4}(1 + w)` for `ξ_* < x ≤ ξ_* + 1`;
* `nearTip_gap_pos` (end of Step (3)): the arithmetic that `C_mid² ≥ C_2/(8c_fl)` closes `h_0 > |ĥ_0|`;
* `ramped_macro_twoG`, `ramped_macro_margin` (Step (4)): when the hole consists of reference pairs
  (`η_k = 1/4`, `Δ_k = 0` on `H`), `ρ_k = 1`, and
  `2g/Lev ≥ 0.158 - 0.7(A + B) - 0.542 w` with `A = C(1/n + ℓ_n)`, `B = 2e_L + S`: the analytic margin
  `0.700 - ½(11/8)^{1/4} - o(1)` of `K8` (`vRhoInfty_le`, `regionII_margin_gt`).
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Holes
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Positivity
  FormalResearch.ModularBootstrap.Upper.Hankel

/-- For real `x` to the right of the first site, `B_D(x)` is a real number `r ≥ 0` (the pair factors are
nonnegative whether or not their sites lie to the left of `x`). -/
theorem designComb_real_nonneg {c' x : ℝ} (hc' : 0 < c') (hgap : siteGap c' 1 ≤ 1 / 2) (f N : ℕ)
    (σ ε : ℕ → ℝ) (_hfN : f ≤ N) (hfx : designSite c' σ f < x) (hf0 : 0 ≤ designSite c' σ f) :
    ∃ r : ℝ, designComb c' f N (1 / 4) σ ε (x : ℂ) = (r : ℂ) ∧ 0 ≤ r := by
  obtain ⟨him, hre⟩ := combTail_real_nonneg (η₀ := 1 / 4) (x := x) hc' (by norm_num) (by norm_num) hgap N
  set t : ℝ := (combTail c' N (1 / 4) (x : ℂ)).re with ht
  have htail : combTail c' N (1 / 4) (x : ℂ) = (t : ℂ) :=
    Complex.ext (by rw [Complex.ofReal_re]) (by rw [Complex.ofReal_im]; exact him)
  set tf : ℝ := Real.tanh (π * (x - designSite c' σ f) / 2) *
    Real.tanh (π * (x + designSite c' σ f) / 2) with htf
  have htf0 : 0 < tf := tanh_prod_pos_of_lt hf0 hfx
  set q : ℝ := ∏ i ∈ Finset.range (N - f),
    blaschkePairQ (designSite c' σ (f + 1 + i)) (ε (f + 1 + i)) x with hq
  have hq0 : 0 ≤ q := Finset.prod_nonneg fun i _ => by unfold blaschkePairQ; positivity
  have hD : designComb c' f N (1 / 4) σ ε (x : ℂ) = ((tf * q * t : ℝ) : ℂ) := by
    unfold designComb
    rw [htail, blaschkeT_ofReal_eq]
    have hprod : (∏ i ∈ Finset.range (N - f),
        pairT (designSite c' σ (f + 1 + i)) (ε (f + 1 + i)) (x : ℂ)) = (q : ℂ) := by
      rw [hq, Complex.ofReal_prod]
      exact Finset.prod_congr rfl fun i _ => pairT_ofReal _ _ _
    rw [hprod, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  exact ⟨tf * q * t, hD, mul_nonneg (mul_nonneg htf0.le hq0) hre⟩

/-- `2g/Lev ≥ h₀^D/Lev - amp` for every amplitude bound `‖ĥ₀‖ ≤ amp · Lev`. -/
theorem twoG_ge_floor_sub {c' x amp : ℝ} (hc' : 0 < c') (hgap : siteGap c' 1 ≤ 1 / 2) (f N : ℕ)
    (σ ε : ℕ → ℝ) (hfN : f ≤ N) (hfx : designSite c' σ f < x) (hf0 : 0 ≤ designSite c' σ f)
    (hAmp : ‖edgeHankel c' (designProfile c' f N (1 / 4) σ ε) (c' * x ^ 2 / 3)‖ ≤ amp * levComb c' f x) :
    (1 / Real.cosh (π * x / 2) ^ 2 * ‖designComb c' f N (1 / 4) σ ε (x : ℂ)‖) / levComb c' f x - amp ≤
      twoG c' f N (1 / 4) σ ε x / levComb c' f x := by
  obtain ⟨r, hr, hr0⟩ := designComb_real_nonneg hc' hgap f N σ ε hfN hfx hf0
  have hnorm : ‖designComb c' f N (1 / 4) σ ε (x : ℂ)‖ = r := by
    rw [hr, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hh0 : (designProfile c' f N (1 / 4) σ ε (x : ℂ)).re = 1 / Real.cosh (π * x / 2) ^ 2 * r := by
    rw [designProfile_ofReal hr, Complex.ofReal_re]
  have hlev := levComb_pos c' f x
  unfold twoG
  rw [Complex.sub_re, hh0, hnorm]
  have hre : (edgeHankel c' (designProfile c' f N (1 / 4) σ ε) (c' * x ^ 2 / 3)).re ≤ amp * levComb c' f x :=
    (Complex.re_le_norm _).trans hAmp
  rw [sub_div, sub_le_sub_iff_left, div_le_iff₀ hlev]
  exact hre

/-- **Step (3), `2g/Lev` near the tip**: with the floor of `ramped_hole_floor` and an amplitude bound
`‖ĥ₀‖ ≤ amp · Lev`, `c_fl · min(1, 16η_n²)(1 - E) - amp ≤ 2g(c' x²/3)/Lev(x)`. -/
theorem ramped_nearTip_twoG :
    ∃ (N₀ : ℕ) (C : ℝ), 0 < C ∧ ∀ᶠ c' in atTop, ∀ (f N n : ℕ) (x : ℝ) (σ η : ℕ → ℝ) (κ eL S amp : ℝ),
      1 ≤ f → f ≤ N → N₀ ≤ n → f + 4 ≤ n → inCell c' n x → RampedHoleHyp c' f N n σ η κ →
      0 ≤ κ → κ ≤ 1 / 98 → 0 ≤ eL →
      designSite c' σ f < x →
      (∀ k, f < k → k ≤ N → k ∉ holeSet n 4 → designSite c' σ k ≠ x) →
      (∀ k, f < k → k ≤ N → k ∈ holeSet n 4 → designSite c' σ k ≠ x ∨ 0 < η k) →
      eLeftComb c' f n 4 x ≤ eL → holeShiftCost c' x σ f N n 4 ≤ S →
      rampedHoleLoss C (siteGap c' n) eL S κ (n : ℝ) ≤ 1 →
      ‖edgeHankel c' (designProfile c' f N (1 / 4) σ (fun k => η k * siteGap c' k))
          (c' * x ^ 2 / 3)‖ ≤ amp * levComb c' f x →
      cFl * min 1 (16 * η n ^ 2) * (1 - rampedHoleLoss C (siteGap c' n) eL S κ (n : ℝ)) - amp ≤
        twoG c' f N (1 / 4) σ (fun k => η k * siteGap c' k) x / levComb c' f x := by
  obtain ⟨N₀, C, hC, hfl⟩ := ramped_hole_floor
  obtain ⟨_, _, hgap_ev⟩ := siteGap_eventually_le
  refine ⟨N₀, C, hC, ?_⟩
  filter_upwards [hfl, hgap_ev, eventually_gt_atTop (0 : ℝ)] with c' hf hgp hc'
  intro f N n x σ η κ eL S amp h1 h2 h3 h4 h5 H hκ0 hκ heL0 hfx hout hpos heL hS hE hAmp
  have hfne : designSite c' σ f ≠ x := hfx.ne
  have hf0 : 0 ≤ designSite c' σ f :=
    xiStar_pos.le.trans (designSite_ge_xiStar hc' (H.sigma_nonneg f le_rfl h2))
  have hfl' := hf f N n x σ η κ eL S h1 h2 h3 h4 h5 H hκ0 hκ heL0 hfne hout hpos heL hS hE
  have hsub := twoG_ge_floor_sub hc' hgp.2.2.2 f N σ (fun k => η k * siteGap c' k) h2 hfx hf0 hAmp
  linarith only [hfl', hsub]

/-- `vρ_∞(x; 3/4)(1 + w) ≤ C_v (x - ξ_*)^{5/4}(1 + w)` for `ξ_* < x ≤ ξ_* + 1`. -/
theorem nearTip_amp_le : ∃ C_v : ℝ, 0 < C_v ∧ ∀ x w : ℝ, xiStar < x → x ≤ xiStar + 1 → 0 ≤ w →
    vRhoInfty x (3 / 4) * (1 + w) ≤ C_v * (x - xiStar) ^ (5 / 4 : ℝ) * (1 + w) := by
  obtain ⟨C_v, hC, h⟩ := nearTip_ratio
  refine ⟨C_v, hC, fun x w hx hx1 hw => ?_⟩
  have := h (x - xiStar) (by linarith) (by linarith)
  rw [show xiStar + (x - xiStar) = x by ring] at this
  exact mul_le_mul_of_nonneg_right this (by linarith)

/-- The arithmetic closing Step (3): if `2 C₂ q ≤ 16 c_fl η²` (the choice `C_mid² ≥ C₂/(8 c_fl)` with
`q = (n/c')^{5/6}`) or `η = 1/4` with `C₂ q ≤ c_fl/2`, and `E, w ≤ 1/8`, then
`C₂ q (1 + w) < c_fl min(1, 16η²)(1 - E)`. -/
theorem nearTip_gap_pos {cF C2 q η E w : ℝ} (hcF : 0 < cF) (hC2q : 0 < C2 * q) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / 4) (hE : E ≤ 1 / 8) (hw : w ≤ 1 / 8)
    (h : 2 * (C2 * q) ≤ 16 * cF * η ^ 2 ∨ (η = 1 / 4 ∧ C2 * q ≤ cF / 2)) :
    C2 * q * (1 + w) < cF * min 1 (16 * η ^ 2) * (1 - E) := by
  rcases h with h | ⟨rfl, h⟩
  · have hmin : min 1 (16 * η ^ 2) = 16 * η ^ 2 := min_eq_right (by nlinarith)
    rw [hmin]
    nlinarith
  · have hmin : min 1 (16 * (1 / 4 : ℝ) ^ 2) = 1 := by norm_num
    rw [hmin]
    nlinarith

/-- **Step (4), the floor with a reference hole**: if the hole `H = {n-3, …, n+4}` consists of reference pairs
(`η_k = 1/4`, `Δ_k = 0`), then `ρ_k = 1` and the floor is `μ₄ (1 - C(1/n + ℓ_n)) e^{-(2e_L + S)}`
(`ramped_floor_pre` with `∏ ρ_k = 1`), uniformly in the modification outside the hole. -/
theorem ramped_macro_floor :
    ∃ (N₀ : ℕ) (C : ℝ), 100000 ≤ N₀ ∧ 0 < C ∧ ∀ᶠ c' in atTop, ∀ (f N n : ℕ) (x : ℝ) (σ η : ℕ → ℝ) (eL S : ℝ),
      1 ≤ f → f ≤ N → N₀ ≤ n → f + 4 ≤ n → inCell c' n x → RampedHoleHyp c' f N n σ η 0 →
      (∀ k, f < k → k ≤ N → k ∈ holeSet n 4 → η k = 1 / 4) → 0 ≤ eL →
      designSite c' σ f ≠ x →
      (∀ k, f < k → k ≤ N → k ∉ holeSet n 4 → designSite c' σ k ≠ x) →
      eLeftComb c' f n 4 x ≤ eL → holeShiftCost c' x σ f N n 4 ≤ S →
      siteGap c' n ≤ 1 / 16 → C * (1 / (n : ℝ) + siteGap c' n) ≤ 1 →
      muHole 4 (1 / 4) * (1 - C * (1 / (n : ℝ) + siteGap c' n)) * Real.exp (-(2 * eL + S)) ≤
        (1 / Real.cosh (π * x / 2) ^ 2 *
            ‖designComb c' f N (1 / 4) σ (fun k => η k * siteGap c' k) (x : ℂ)‖) / levComb c' f x := by
  obtain ⟨N₀, C, hN₀, hC, hpre⟩ := ramped_floor_pre
  refine ⟨N₀, C, hN₀, hC, ?_⟩
  filter_upwards [hpre, eventually_gt_atTop (0 : ℝ)] with c' hp hc'
  intro f N n x σ η eL S hf hfN hn hfn hx H hη14 heL0 hfne hout heL hS hℓ16 hA1
  have hpos : ∀ k, f < k → k ≤ N → k ∈ holeSet n 4 → designSite c' σ k ≠ x ∨ 0 < η k :=
    fun k a b c => Or.inr (by rw [hη14 k a b c]; norm_num)
  have hR := hp f N n x σ η 0 eL S hf hfN hn hfn hx H heL0 hfne hout hpos heL hS hℓ16 hA1
  have hprod : ∏ k ∈ holeModSet f N n, holeRho c' x σ η k = 1 := by
    refine Finset.prod_eq_one fun k hk => ?_
    have hk' := Finset.mem_filter.mp hk
    have h2 := Finset.mem_Icc.mp hk'.1
    have hshift := H.hole_shift k (by omega) h2.2 hk'.2
    have hsite : designSite c' σ k = chiQuantile c' (k : ℝ) := by
      rw [zero_mul, abs_nonpos_iff, sub_eq_zero] at hshift
      exact hshift
    have hq : 0 < pairModQ c' (1 / 4) x k := by
      have hn5 : 100000 ≤ n := hN₀.trans hn
      have hx0 : 0 < x := by
        have := (xiStar_le_chiQuantile_nat hc' (by omega : 1 ≤ n)).trans hx.1
        exact xiStar_pos.trans_le this
      obtain ⟨hℓpos, -⟩ := hole_gap_bounds hc' (by omega : 20 ≤ n)
      obtain ⟨hg1, hg2⟩ := hole_gap_numeric hc' hn5 hℓ16 hk'.2
      have hnr : (100000 : ℝ) ≤ n := by exact_mod_cast hn5
      refine blaschkePairQ_pos_of
        (xiStar_pos.le.trans (xiStar_le_chiQuantile_nat hc' (by omega))) hx0 (by linarith)
        ?_ (Or.inr (by linarith))
      have : siteGap c' k ≤ 1.0002 * siteGap c' n := hg2
      linarith
    unfold holeRho
    rw [hsite, hη14 k (by omega) h2.2 hk'.2, div_eq_one_iff_eq hq.ne']
    rfl
  rw [hprod, mul_one] at hR
  exact hR

/-- **Step (4), `2g/Lev ≥ 0.158 - 0.7(A + B) - 0.542 w`** (`rem:thmU` Step (4), `cmb:K8`): with a reference hole
and the amplitude bound `‖ĥ₀‖ ≤ vρ_∞(x; n₁)(1 + w) Lev`, `n₁ ≥ 3/4`, `x > ξ_*`, the analytic margin of `K8`
`μ₄ - ½(11/8)^{1/4} > 0.158` survives the losses `A = C(1/n + ℓ_n)`, `B = 2e_L + S`. -/
theorem ramped_macro_margin :
    ∃ (N₀ : ℕ) (C : ℝ), 0 < C ∧ ∀ᶠ c' in atTop, ∀ (f N n : ℕ) (x : ℝ) (σ η : ℕ → ℝ) (eL S w n₁ : ℝ),
      1 ≤ f → f ≤ N → N₀ ≤ n → f + 4 ≤ n → inCell c' n x → RampedHoleHyp c' f N n σ η 0 →
      (∀ k, f < k → k ≤ N → k ∈ holeSet n 4 → η k = 1 / 4) → 0 ≤ eL → 0 ≤ w →
      designSite c' σ f < x →
      (∀ k, f < k → k ≤ N → k ∉ holeSet n 4 → designSite c' σ k ≠ x) →
      eLeftComb c' f n 4 x ≤ eL → holeShiftCost c' x σ f N n 4 ≤ S →
      siteGap c' n ≤ 1 / 16 →
      C * (1 / (n : ℝ) + siteGap c' n) + (2 * eL + S) ≤ 1 → 3 / 4 ≤ n₁ → xiStar < x →
      ‖edgeHankel c' (designProfile c' f N (1 / 4) σ (fun k => η k * siteGap c' k))
          (c' * x ^ 2 / 3)‖ ≤ vRhoInfty x n₁ * (1 + w) * levComb c' f x →
      158 / 1000 - 7 / 10 * (C * (1 / (n : ℝ) + siteGap c' n) + (2 * eL + S)) - 542 / 1000 * w ≤
        twoG c' f N (1 / 4) σ (fun k => η k * siteGap c' k) x / levComb c' f x := by
  obtain ⟨N₀, C, hN₀, hC, hfl⟩ := ramped_macro_floor
  obtain ⟨_, _, hgap_ev⟩ := siteGap_eventually_le
  refine ⟨N₀, C, hC, ?_⟩
  filter_upwards [hfl, hgap_ev, eventually_gt_atTop (0 : ℝ)] with c' hf hgp hc'
  intro f N n x σ η eL S w n₁ h1 h2 h3 h4 h5 H hη14 heL0 hw hfx hout heL hS hℓ16 hE hn₁ hxξ hAmp
  have hn20 : 20 ≤ n := by omega
  have hS0 : 0 ≤ S := (holeShiftCost_nonneg c' x σ f N n 4).trans hS
  have hA0 : 0 ≤ C * (1 / (n : ℝ) + siteGap c' n) := by
    obtain ⟨hℓpos, -⟩ := hole_gap_bounds hc' hn20
    positivity
  have hB0 : 0 ≤ 2 * eL + S := by linarith only [heL0, hS0]
  have hA1 : C * (1 / (n : ℝ) + siteGap c' n) ≤ 1 := by linarith only [hE, hB0]
  have hfne : designSite c' σ f ≠ x := hfx.ne
  have hf0 : 0 ≤ designSite c' σ f :=
    xiStar_pos.le.trans (designSite_ge_xiStar hc' (H.sigma_nonneg f le_rfl h2))
  have hfl' := hf f N n x σ η eL S h1 h2 h3 h4 h5 H hη14 heL0 hfne hout heL hS hℓ16 hA1
  obtain ⟨hv1, hv2, hv3, -⟩ := vRhoInfty_le hn₁ hxξ
  have hLev := levComb_pos c' f x
  have hamp : ‖edgeHankel c' (designProfile c' f N (1 / 4) σ (fun k => η k * siteGap c' k))
      (c' * x ^ 2 / 3)‖ ≤ (542 / 1000 * (1 + w)) * levComb c' f x := by
    refine hAmp.trans ?_
    apply mul_le_mul_of_nonneg_right _ hLev.le
    have : vRhoInfty x n₁ ≤ 542 / 1000 := by linarith only [hv1, hv2, hv3]
    nlinarith
  have hsub := twoG_ge_floor_sub hc' hgp.2.2.2 f N σ (fun k => η k * siteGap c' k) h2 hfx hf0 hamp
  have hμ := muHole_four_quarter_gt
  have hexp := Real.add_one_le_exp (-(2 * eL + S))
  have hA' : 0 ≤ 1 - C * (1 / (n : ℝ) + siteGap c' n) := by linarith only [hA1]
  have hB' : 0 ≤ 1 - (2 * eL + S) := by linarith only [hE, hA0]
  have hF : muHole 4 (1 / 4) * (1 - C * (1 / (n : ℝ) + siteGap c' n)) * Real.exp (-(2 * eL + S)) ≥
      7 / 10 * (1 - (C * (1 / (n : ℝ) + siteGap c' n) + (2 * eL + S))) := by
    have h1' : (1 - C * (1 / (n : ℝ) + siteGap c' n)) * (1 - (2 * eL + S)) ≤
        (1 - C * (1 / (n : ℝ) + siteGap c' n)) * Real.exp (-(2 * eL + S)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hexp]) hA'
    have h2' : 1 - (C * (1 / (n : ℝ) + siteGap c' n) + (2 * eL + S)) ≤
        (1 - C * (1 / (n : ℝ) + siteGap c' n)) * (1 - (2 * eL + S)) := by
      nlinarith only [mul_nonneg hA0 hB0]
    have hμ0 : 0 ≤ muHole 4 (1 / 4) := by linarith only [hμ]
    have h3' : 0 ≤ (1 - C * (1 / (n : ℝ) + siteGap c' n)) * Real.exp (-(2 * eL + S)) :=
      mul_nonneg hA' (Real.exp_pos _).le
    have hE0 : 0 ≤ 1 - (C * (1 / (n : ℝ) + siteGap c' n) + (2 * eL + S)) := by linarith only [hE]
    calc 7 / 10 * (1 - (C * (1 / (n : ℝ) + siteGap c' n) + (2 * eL + S)))
        ≤ muHole 4 (1 / 4) * (1 - (C * (1 / (n : ℝ) + siteGap c' n) + (2 * eL + S))) :=
          mul_le_mul_of_nonneg_right hμ.le hE0
      _ ≤ muHole 4 (1 / 4) * ((1 - C * (1 / (n : ℝ) + siteGap c' n)) * Real.exp (-(2 * eL + S))) :=
          mul_le_mul_of_nonneg_left (h2'.trans h1') hμ0
      _ = muHole 4 (1 / 4) * (1 - C * (1 / (n : ℝ) + siteGap c' n)) * Real.exp (-(2 * eL + S)) := by
          ring
  linarith only [hfl', hF, hsub]

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.designComb_real_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.designComb_real_nonneg

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.twoG_ge_floor_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.twoG_ge_floor_sub

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.ramped_nearTip_twoG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.ramped_nearTip_twoG

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.nearTip_amp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.nearTip_amp_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.nearTip_gap_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.nearTip_gap_pos

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.ramped_macro_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.ramped_macro_floor

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.ramped_macro_margin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.ramped_macro_margin

end FormalResearch.ModularBootstrap.Upper.Ramped
