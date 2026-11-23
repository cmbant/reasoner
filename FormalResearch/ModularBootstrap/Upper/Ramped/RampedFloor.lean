module

public import FormalResearch.ModularBootstrap.Upper.Holes.HoleFloor
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedHolePairs

/-!
# The near-tip floor of a modified ramped comb (`rem:thmU` Step (3), "Reference floor", "Comparison")

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Step (3), concluding display
`h_0/Lev ≥ (c_fl - o(1)) min(1, 16η_n²)`.

`ramped_hole_floor`: for the modified comb `B_D = designComb c' f N (1/4) σ ε`, `ε_k = η_k ℓ_k`, satisfying
`RampedHoleHyp`, at `x` in the reference cell `n` (`n ≥ N₀`, in particular `n ≥ 10⁵`),
`c_fl · min(1, 16η_n²) · (1 - E) ≤ sech²(πx/2) ‖B_D(x)‖/Lev^{(f)}(x)`
with the explicit relative loss `E = rampedHoleLoss` made of
`C(1/n + ℓ_n)` (the reference floor `K4`, `K5`), `2e_L + S` (`e_L` and the site-shift cost `S` of the
paper), and `16ℓ_n + 128κ² + 7(10κ + ℓ_n²) + 3500/n` (the hole pairs).
The positive constant is `c_fl = 0.7 · 16647192576/23591176505 > 0.493` (`cFl`, `cFl_gt`).
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Holes
  FormalResearch.ModularBootstrap.Upper.Design

/-- The relative loss in the floor of a modified comb. -/
noncomputable def rampedHoleLoss (C ℓ eL S κ n : ℝ) : ℝ :=
  C * (1 / n + ℓ) + 2 * eL + S + 16 * ℓ + 128 * κ ^ 2 + 7 * (10 * κ + ℓ ^ 2) + 3500 / n

lemma mul_one_sub_ge {s a x : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hx : 1 - s ≤ x) :
    1 - (s + a) ≤ x * (1 - a) := by
  have h1 : (1 - s) * (1 - a) ≤ x * (1 - a) := mul_le_mul_of_nonneg_right hx (by linarith)
  nlinarith [mul_nonneg hs ha]

/-- Combination of the reference floor, the exponential factor and the hole product. -/
lemma floor_combine {μ P M A B L K D G U e R : ℝ} (hμ : 7 / 10 ≤ μ) (hP : 0 < P) (hM : 0 ≤ M)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L) (hK : 0 ≤ K) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hE : A + B + L + K + D + G ≤ 1)
    (hR : μ * (1 - A) * (e * U) ≤ R) (he : 1 - B ≤ e)
    (hU : (1 - L) * (M * (1 - K)) * ((1 - D) * P * (1 - G)) ≤ U) :
    7 / 10 * P * M * (1 - (A + B + L + K + D + G)) ≤ R := by
  have hA1 : A ≤ 1 := by linarith
  have hB1 : B ≤ 1 := by linarith
  have hL1 : L ≤ 1 := by linarith
  have hK1 : K ≤ 1 := by linarith
  have hD1 : D ≤ 1 := by linarith
  have hG1 : G ≤ 1 := by linarith
  have hU0 : 0 ≤ U := le_trans (by
    have : 0 ≤ (1 - L) := by linarith
    have : 0 ≤ (1 - K) := by linarith
    have : 0 ≤ (1 - D) := by linarith
    have : 0 ≤ (1 - G) := by linarith
    positivity) hU
  have hμ0 : 0 ≤ μ := by linarith
  have hA' : 0 ≤ 1 - A := by linarith
  have hB' : 0 ≤ 1 - B := by linarith
  have h1 : μ * (1 - A) * ((1 - B) * U) ≤ R :=
    le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he hU0) (mul_nonneg hμ0 hA')) hR
  have h2 : μ * (1 - A) * ((1 - B) * ((1 - L) * (M * (1 - K)) * ((1 - D) * P * (1 - G)))) ≤ R :=
    le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU hB')
      (mul_nonneg hμ0 hA')) h1
  have hZ1 := mul_one_sub_ge hA hB hB1 (x := 1 - A) (by linarith)
  have hZ1' : 1 - (A + B) ≤ (1 - A) * (1 - B) := hZ1
  have hZ2 := mul_one_sub_ge (by linarith : 0 ≤ A + B) hL hL1 hZ1'
  have hZ3 := mul_one_sub_ge (by linarith : 0 ≤ A + B + L) hK hK1 hZ2
  have hZ4 := mul_one_sub_ge (by linarith : 0 ≤ A + B + L + K) hD hD1 hZ3
  have hZ5 := mul_one_sub_ge (by linarith : 0 ≤ A + B + L + K + D) hG hG1 hZ4
  have hZ : 1 - (A + B + L + K + D + G) ≤
      (1 - A) * (1 - B) * (1 - L) * (1 - K) * (1 - D) * (1 - G) := hZ5
  have hPM : 0 ≤ P * M := by positivity
  have hrew : μ * (1 - A) * ((1 - B) * ((1 - L) * (M * (1 - K)) * ((1 - D) * P * (1 - G)))) =
      μ * (P * M) * ((1 - A) * (1 - B) * (1 - L) * (1 - K) * (1 - D) * (1 - G)) := by ring
  rw [hrew] at h2
  refine le_trans ?_ h2
  have hE0 : 0 ≤ 1 - (A + B + L + K + D + G) := by linarith
  calc 7 / 10 * P * M * (1 - (A + B + L + K + D + G))
      = 7 / 10 * (P * M) * (1 - (A + B + L + K + D + G)) := by ring
    _ ≤ μ * (P * M) * (1 - (A + B + L + K + D + G)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμ hPM) hE0
    _ ≤ μ * (P * M) * ((1 - A) * (1 - B) * (1 - L) * (1 - K) * (1 - D) * (1 - G)) :=
        mul_le_mul_of_nonneg_left hZ (mul_nonneg hμ0 hPM)

/-- Numerical consequences of `E ≤ 1`. -/
lemma loss_bounds {C ℓ n eL S κ : ℝ} (hC : 0 < C) (hℓ : 0 < ℓ) (hn : 0 < n) (heL : 0 ≤ eL)
    (hS : 0 ≤ S) (hκ : 0 ≤ κ)
    (hE : rampedHoleLoss C ℓ eL S κ n ≤ 1) :
    ℓ ≤ 1 / 16 ∧ 0 ≤ C * (1 / n + ℓ) ∧ C * (1 / n + ℓ) + (2 * eL + S) + 16 * ℓ + 128 * κ ^ 2 +
      7 * (10 * κ + ℓ ^ 2) + 3500 / n ≤ 1 ∧ 0 ≤ 3500 / n := by
  have hA : 0 ≤ C * (1 / n + ℓ) := by positivity
  have hG : 0 ≤ 3500 / n := by positivity
  have hκ2 : 0 ≤ κ ^ 2 := sq_nonneg κ
  have hℓ2 : 0 ≤ ℓ ^ 2 := sq_nonneg ℓ
  have hdef : rampedHoleLoss C ℓ eL S κ n = C * (1 / n + ℓ) + (2 * eL + S) + 16 * ℓ + 128 * κ ^ 2 +
      7 * (10 * κ + ℓ ^ 2) + 3500 / n := by
    unfold rampedHoleLoss; ring
  rw [hdef] at hE
  refine ⟨?_, hA, hE, hG⟩
  by_contra hcon
  push Not at hcon
  have hκ10 : 0 ≤ 7 * (10 * κ + ℓ ^ 2) := by positivity
  linarith only [hE, hA, hG, hκ2, hℓ2, heL, hS, hκ10, hcon]

lemma ramped_hqpos {c' x κ : ℝ} (hc' : 0 < c') {n : ℕ} (hn5 : 100000 ≤ n) (hℓ16 : siteGap c' n ≤ 1 / 16)
    (hgapk : ∀ k, 1 ≤ k → siteGap c' k ≤ 1 / 2) {f N : ℕ} {σ η : ℕ → ℝ}
    (H : RampedHoleHyp c' f N n σ η κ) (hx0 : 0 < x)
    (hpos : ∀ k, f < k → k ≤ N → k ∈ holeSet n 4 → designSite c' σ k ≠ x ∨ 0 < η k) :
    ∀ k, f < k → k ≤ N → k ∈ holeSet n 4 →
      0 < blaschkePairQ (designSite c' σ k) (η k * siteGap c' k) x ∧ 0 < pairModQ c' (1 / 4) x k := by
  intro k hk1 hk2 hkH
  have hη := H.eta_mem k hk1 hk2
  obtain ⟨hg1, -⟩ := hole_gap_numeric hc' hn5 hℓ16 hkH
  obtain ⟨hℓpos, -⟩ := hole_gap_bounds hc' (by omega : 20 ≤ n)
  have h1 := hgapk k (by omega)
  have hgpos : 0 < siteGap c' k := by linarith
  have hsite : 0 ≤ designSite c' σ k :=
    xiStar_pos.le.trans (designSite_ge_xiStar hc' (H.sigma_nonneg k hk1.le hk2))
  refine ⟨?_, ?_⟩
  · refine blaschkePairQ_pos_of hsite hx0 (mul_nonneg hη.1 hgpos.le)
      (by nlinarith [hη.2, hη.1]) ?_
    rcases hpos k hk1 hk2 hkH with h | h
    · exact Or.inl h
    · exact Or.inr (mul_pos h hgpos)
  · exact blaschkePairQ_pos_of (xiStar_pos.le.trans (xiStar_le_chiQuantile_nat hc' (by omega)))
      hx0 (by linarith) (by linarith) (Or.inr (by linarith))

lemma ramped_hexpHole {c' x : ℝ} {n : ℕ} {f N : ℕ} {σ η : ℕ → ℝ}
    (hq : ∀ k, f < k → k ≤ N → k ∈ holeSet n 4 →
      0 < blaschkePairQ (designSite c' σ k) (η k * siteGap c' k) x ∧ 0 < pairModQ c' (1 / 4) x k) :
    Real.exp (holeLogRho c' (1 / 4) x σ (fun k => η k * siteGap c' k) f N n 4) =
      ∏ k ∈ holeModSet f N n, holeRho c' x σ η k := by
  unfold holeLogRho
  rw [exp_sum_log_sub (T := (Finset.Icc (f + 1) N).filter (fun k => k ∈ holeSet n 4))
    (fun k => blaschkePairQ (designSite c' σ k) (η k * siteGap c' k) x)
    (fun k => pairModQ c' (1 / 4) x k)]
  · rfl
  · intro k hk
    have := Finset.mem_filter.mp hk
    have h2 := Finset.mem_Icc.mp this.1
    exact (hq k (by omega) h2.2 this.2).1
  · intro k hk
    have := Finset.mem_filter.mp hk
    have h2 := Finset.mem_Icc.mp this.1
    exact (hq k (by omega) h2.2 this.2).2

/-- **The reference floor with the modified hole pairs** (`rem:thmU` Step (3), "Comparison"):
`μ₄(1 - C(1/n + ℓ_n)) · e^{-(2e_L + S)} ∏_{k∈H} ρ_k ≤ sech²(πx/2)‖B_D(x)‖/Lev^{(f)}(x)`. -/
theorem ramped_floor_pre :
    ∃ (N₀ : ℕ) (C : ℝ), 100000 ≤ N₀ ∧ 0 < C ∧ ∀ᶠ c' in atTop, ∀ (f N n : ℕ) (x : ℝ) (σ η : ℕ → ℝ) (κ eL S : ℝ),
      1 ≤ f → f ≤ N → N₀ ≤ n → f + 4 ≤ n → inCell c' n x → RampedHoleHyp c' f N n σ η κ →
      0 ≤ eL →
      designSite c' σ f ≠ x →
      (∀ k, f < k → k ≤ N → k ∉ holeSet n 4 → designSite c' σ k ≠ x) →
      (∀ k, f < k → k ≤ N → k ∈ holeSet n 4 → designSite c' σ k ≠ x ∨ 0 < η k) →
      eLeftComb c' f n 4 x ≤ eL → holeShiftCost c' x σ f N n 4 ≤ S →
      siteGap c' n ≤ 1 / 16 → C * (1 / (n : ℝ) + siteGap c' n) ≤ 1 →
      muHole 4 (1 / 4) * (1 - C * (1 / (n : ℝ) + siteGap c' n)) *
          (Real.exp (-(2 * eL + S)) * ∏ k ∈ holeModSet f N n, holeRho c' x σ η k) ≤
        (1 / Real.cosh (π * x / 2) ^ 2 *
            ‖designComb c' f N (1 / 4) σ (fun k => η k * siteGap c' k) (x : ℂ)‖) / levComb c' f x := by
  obtain ⟨N_j, C, hNj, hC, hev⟩ := designComb_floor (j := 4) (η₀ := 1 / 4) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨_, _, hgap_ev⟩ := siteGap_eventually_le
  refine ⟨max N_j 100000, C, le_max_right _ _, hC, ?_⟩
  filter_upwards [hev, hgap_ev, eventually_gt_atTop (0 : ℝ)] with c' hfl hgp hc'
  intro f N n x σ η κ eL S hf hfN hn hfn hx H heL0 hfne hout hpos heL hS hℓ16 hA1'
  have hn5 : 100000 ≤ n := (le_max_right _ _).trans hn
  have hNjn : N_j ≤ n := (le_max_left _ _).trans hn
  obtain ⟨hℓpos, -⟩ := hole_gap_bounds hc' (by omega : 20 ≤ n)
  have hxξ : xiStar ≤ x := (xiStar_le_chiQuantile_nat hc' (by omega : 1 ≤ n)).trans hx.1
  have hx0 : 0 < x := xiStar_pos.trans_le hxξ
  have hgapk : ∀ k, 1 ≤ k → siteGap c' k ≤ 1 / 2 := fun k hk => (hgp.1 k hk).trans hgp.2.2.2
  have hεmem : ∀ k, f < k → k ≤ N → 0 ≤ (fun k => η k * siteGap c' k) k ∧
      (fun k => η k * siteGap c' k) k ≤ 1 / 2 := by
    intro k hk1 hk2
    have hη := H.eta_mem k hk1 hk2
    have h0 : 0 ≤ siteGap c' k := siteGap_nonneg hc' (by omega)
    have h1 := hgapk k (by omega)
    constructor
    · exact mul_nonneg hη.1 h0
    · show η k * siteGap c' k ≤ 1 / 2
      nlinarith [hη.2, hη.1]
  have hsite : ∀ k, f ≤ k → k ≤ N → 0 ≤ designSite c' σ k := fun k hk1 hk2 =>
    xiStar_pos.le.trans (designSite_ge_xiStar hc' (H.sigma_nonneg k hk1 hk2))
  have hq := ramped_hqpos hc' hn5 hℓ16 hgapk H hx0 hpos
  have hfloor := hfl f N n x σ (fun k => η k * siteGap c' k) hf hfN (max_le hNjn hfn) hx hεmem hsite
    hfne hout (fun k a b c => (hq k a b c).1)
  have hexpHole := ramped_hexpHole (c' := c') (x := x) (n := n) (f := f) (N := N) (σ := σ)
    (η := η) hq
  have hmod := modLogRatio_ge c' (1 / 4) x σ (fun k => η k * siteGap c' k) f N n 4
  have hexp_ge : Real.exp (-(2 * eL + S)) * Real.exp
      (holeLogRho c' (1 / 4) x σ (fun k => η k * siteGap c' k) f N n 4) ≤
      Real.exp (-2 * eLeftComb c' f n 4 x +
        modLogRatio c' (1 / 4) x σ (fun k => η k * siteGap c' k) f N n 4) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith only [hmod, hS, heL]
  have hμ := muHole_four_quarter_gt
  have hA1 : 0 ≤ 1 - C * (1 / (n : ℝ) + siteGap c' n) := by linarith only [hA1']
  refine le_trans ?_ hfloor
  rw [← hexpHole]
  exact mul_le_mul_of_nonneg_left hexp_ge (mul_nonneg (by linarith) hA1)

/-- **The near-tip floor of a modified ramped comb** (`rem:thmU` Step (3)):
`c_fl · min(1, 16η_n²) · (1 - E) ≤ sech²(πx/2) ‖B_D(x)‖ / Lev^{(f)}(x)` with `E = rampedHoleLoss`. -/
theorem ramped_hole_floor :
    ∃ (N₀ : ℕ) (C : ℝ), 0 < C ∧ ∀ᶠ c' in atTop, ∀ (f N n : ℕ) (x : ℝ) (σ η : ℕ → ℝ) (κ eL S : ℝ),
      1 ≤ f → f ≤ N → N₀ ≤ n → f + 4 ≤ n → inCell c' n x → RampedHoleHyp c' f N n σ η κ →
      0 ≤ κ → κ ≤ 1 / 98 → 0 ≤ eL →
      designSite c' σ f ≠ x →
      (∀ k, f < k → k ≤ N → k ∉ holeSet n 4 → designSite c' σ k ≠ x) →
      (∀ k, f < k → k ≤ N → k ∈ holeSet n 4 → designSite c' σ k ≠ x ∨ 0 < η k) →
      eLeftComb c' f n 4 x ≤ eL → holeShiftCost c' x σ f N n 4 ≤ S →
      rampedHoleLoss C (siteGap c' n) eL S κ (n : ℝ) ≤ 1 →
      cFl * min 1 (16 * η n ^ 2) * (1 - rampedHoleLoss C (siteGap c' n) eL S κ (n : ℝ)) ≤
        (1 / Real.cosh (π * x / 2) ^ 2 *
            ‖designComb c' f N (1 / 4) σ (fun k => η k * siteGap c' k) (x : ℂ)‖) / levComb c' f x := by
  obtain ⟨N₀, C, hN₀, hC, hpre⟩ := ramped_floor_pre
  refine ⟨N₀, C, hC, ?_⟩
  filter_upwards [hpre, eventually_gt_atTop (0 : ℝ)] with c' hp hc'
  intro f N n x σ η κ eL S hf hfN hn hfn hx H hκ0 hκ heL0 hfne hout hpos heL hS hE
  have hn5 : 100000 ≤ n := hN₀.trans hn
  obtain ⟨hℓpos, -⟩ := hole_gap_bounds hc' (by omega : 20 ≤ n)
  have hnr : (100000 : ℝ) ≤ n := by exact_mod_cast hn5
  have hnpos : (0 : ℝ) < n := by linarith
  have hS0 : 0 ≤ S := (holeShiftCost_nonneg c' x σ f N n 4).trans hS
  obtain ⟨hℓ16, hA0, hEs, hG0⟩ := loss_bounds hC hℓpos hnpos heL0 hS0 hκ0 hE
  have hB0 : 0 ≤ 2 * eL + S := by linarith only [heL0, hS0]
  have hL0 : 0 ≤ 16 * siteGap c' n := by linarith only [hℓpos]
  have hK0 : 0 ≤ 128 * κ ^ 2 := by positivity
  have hδ : 0 ≤ 10 * κ + siteGap c' n ^ 2 := by positivity
  have hD0 : 0 ≤ 7 * (10 * κ + siteGap c' n ^ 2) := by positivity
  have hA1' : C * (1 / (n : ℝ) + siteGap c' n) ≤ 1 := by
    linarith only [hEs, hA0, hB0, hL0, hK0, hD0, hG0]
  have hR := hp f N n x σ η κ eL S hf hfN hn hfn hx H heL0 hfne hout hpos heL hS hℓ16 hA1'
  have hprod := rampedHole_prod_lower hc' hn5 hx H hfn hℓ16 hκ0 hκ
  have hμ := muHole_four_quarter_gt
  have hδ1 : 10 * κ + siteGap c' n ^ 2 ≤ 1 := by nlinarith only [hκ, hℓ16, hℓpos]
  have hBern : 1 - 7 * (10 * κ + siteGap c' n ^ 2) ≤ (1 - (10 * κ + siteGap c' n ^ 2)) ^ 7 := by
    have := one_add_mul_le_pow (a := -(10 * κ + siteGap c' n ^ 2)) (by linarith only [hδ1]) 7
    simp only [Nat.cast_ofNat] at this
    linarith only [this]
  have hGn : 7 / 4 * ((1 + 2000 / (n : ℝ)) - 1) = 3500 / (n : ℝ) := by ring
  rw [hGn] at hprod
  have hG1 : 0 ≤ 1 - 3500 / (n : ℝ) := by
    linarith only [hEs, hA0, hB0, hL0, hK0, hD0, hG0]
  have hb0 : 0 ≤ (1 - 16 * siteGap c' n) * (min 1 (16 * η n ^ 2) * (1 - 128 * κ ^ 2)) := by
    have h16 : 0 ≤ 1 - 16 * siteGap c' n := by linarith only [hℓ16]
    have hκ2 : 0 ≤ 1 - 128 * κ ^ 2 := by nlinarith only [hκ0, hκ]
    exact mul_nonneg h16 (mul_nonneg (le_min zero_le_one (by positivity)) hκ2)
  have hP := holeProdConst_pos
  have hU : (1 - 16 * siteGap c' n) * (min 1 (16 * η n ^ 2) * (1 - 128 * κ ^ 2)) *
      ((1 - 7 * (10 * κ + siteGap c' n ^ 2)) * holeProdConst * (1 - 3500 / (n : ℝ))) ≤
      ∏ k ∈ holeModSet f N n, holeRho c' x σ η k := by
    refine le_trans ?_ hprod
    refine mul_le_mul_of_nonneg_left ?_ hb0
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBern hP.le) hG1
  have hcomb := floor_combine (μ := muHole 4 (1 / 4)) (P := holeProdConst)
    (M := min 1 (16 * η n ^ 2)) (A := C * (1 / (n : ℝ) + siteGap c' n)) (B := 2 * eL + S)
    (L := 16 * siteGap c' n) (K := 128 * κ ^ 2) (D := 7 * (10 * κ + siteGap c' n ^ 2))
    (G := 3500 / (n : ℝ)) (U := ∏ k ∈ holeModSet f N n, holeRho c' x σ η k)
    (e := Real.exp (-(2 * eL + S)))
    (R := (1 / Real.cosh (π * x / 2) ^ 2 *
        ‖designComb c' f N (1 / 4) σ (fun k => η k * siteGap c' k) (x : ℂ)‖) / levComb c' f x)
    (by linarith only [hμ]) hP (le_min zero_le_one (by positivity)) hA0 hB0 hL0 hK0 hD0 hG0
    (by linarith only [hEs])
    hR (by linarith only [Real.add_one_le_exp (-(2 * eL + S))]) hU
  have hrew : cFl * min 1 (16 * η n ^ 2) *
      (1 - rampedHoleLoss C (siteGap c' n) eL S κ (n : ℝ)) =
      7 / 10 * holeProdConst * min 1 (16 * η n ^ 2) *
        (1 - (C * (1 / (n : ℝ) + siteGap c' n) + (2 * eL + S) + 16 * siteGap c' n + 128 * κ ^ 2 +
          7 * (10 * κ + siteGap c' n ^ 2) + 3500 / (n : ℝ))) := by
    unfold cFl rampedHoleLoss; ring
  rw [hrew]
  exact hcomb

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.ramped_floor_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.ramped_floor_pre

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.ramped_hole_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.ramped_hole_floor

end FormalResearch.ModularBootstrap.Upper.Ramped
