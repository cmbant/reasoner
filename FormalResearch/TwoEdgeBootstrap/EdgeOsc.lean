module

public import FormalResearch.Analysis.VanDerCorput
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Universal Two-Edge Bootstrap: Oscillatory Edge Estimate (Lemma TE.1a)

Source: `CFT/common/two_edge_bootstrap.tex` (shared by CFT Papers I and II).
Splits `TwoEdgePoissonCore` (Parts 1–3) and `TwoEdgeVanDerCorput` (van der Corput IBP/estimates)
from the dyadic oscillatory edge estimate `teb_edge_osc_interval`, `teb_edge_osc_tendsto`
(improper Riemann–Stieltjes limit matching `8f29b5221` without `IntegrableOn`), `teb_edge_osc`, and `teb_edge_osc_id`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal NNReal Interval

namespace FormalResearch.TwoEdgeBootstrap

open FormalResearch.Analysis

/-! ### Part 4b: Lemma TE.1a — Dyadic Oscillatory Edge Estimate -/

section EdgeOscEstimate

private lemma geom_sum_le_inv_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, r ^ j ≤ 1 / (1 - r) := by
  have hmul : (1 - r) * ∑ j ∈ Finset.range n, r ^ j = 1 - r ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      ring
  have hle : (1 - r) * ∑ j ∈ Finset.range n, r ^ j ≤ 1 := by
    rw [hmul]
    linarith [pow_nonneg hr0 n]
  exact (le_div_iff₀' (sub_pos.mpr hr1)).mpr hle

private lemma rpow_mul_exp_neg_sq_le {p q : ℝ} {x : ℝ} (hx : 1 ≤ x) :
    x ^ p * Real.exp (-x ^ 2) ≤ (Nat.factorial (Nat.ceil ((p + q) / 2)) : ℝ) * x ^ (-q) := by
  set m := Nat.ceil ((p + q) / 2)
  have hm : (p + q) / 2 ≤ m := Nat.le_ceil _
  have hm2 : p + q ≤ 2 * (m : ℝ) := by linarith
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hexp : (x ^ 2) ^ m / (Nat.factorial m : ℝ) ≤ Real.exp (x ^ 2) := by
    have hsum := Real.sum_le_exp_of_nonneg (sq_nonneg x) (m + 1)
    have hterm : (x ^ 2) ^ m / (Nat.factorial m : ℝ) ≤
        ∑ i ∈ Finset.range (m + 1), (x ^ 2) ^ i / (Nat.factorial i : ℝ) :=
      Finset.single_le_sum (f := fun i => (x ^ 2) ^ i / (Nat.factorial i : ℝ))
        (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self m))
    exact hterm.trans hsum
  have hexp_inv : Real.exp (-x ^ 2) ≤ (Nat.factorial m : ℝ) * x ^ (-2 * (m : ℝ)) := by
    rw [Real.exp_neg]
    have hpow : x ^ (2 * (m : ℝ)) = (x ^ 2) ^ m := by
      rw [← Real.rpow_natCast (x ^ 2) m, ← Real.rpow_natCast x 2, ← Real.rpow_mul hx_pos.le]
      ring_nf
    have hexp' : x ^ (2 * (m : ℝ)) / (Nat.factorial m : ℝ) ≤ Real.exp (x ^ 2) := hpow ▸ hexp
    have h1 : (Real.exp (x ^ 2))⁻¹ ≤ (x ^ (2 * (m : ℝ)) / (Nat.factorial m : ℝ))⁻¹ :=
      inv_anti₀ (by positivity) hexp'
    rw [show (-2 * (m : ℝ)) = -(2 * (m : ℝ)) by ring, Real.rpow_neg hx_pos.le]
    calc (Real.exp (x ^ 2))⁻¹ ≤ (x ^ (2 * (m : ℝ)) / (Nat.factorial m : ℝ))⁻¹ := h1
      _ = (Nat.factorial m : ℝ) * (x ^ (2 * (m : ℝ)))⁻¹ := by rw [inv_div, mul_comm, div_eq_mul_inv]
  calc x ^ p * Real.exp (-x ^ 2)
      ≤ x ^ p * ((Nat.factorial m : ℝ) * x ^ (-2 * (m : ℝ))) := by gcongr
    _ = (Nat.factorial m : ℝ) * (x ^ p * x ^ (-2 * (m : ℝ))) := by ring
    _ = (Nat.factorial m : ℝ) * x ^ (p - 2 * (m : ℝ)) := by
        rw [← Real.rpow_add hx_pos, show p - 2 * (m : ℝ) = p + -2 * (m : ℝ) by ring]
    _ ≤ (Nat.factorial m : ℝ) * x ^ (-q) := by
        gcongr
        linarith

private lemma sum_dyadic_two_pow_neg_half (k₀ k₁ : ℤ) :
    ∑ k ∈ Finset.Ico k₀ (min k₁ 1), ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ) ≤ 4 := by
  have hsub : Finset.Ico k₀ (min k₁ 1) ⊆ Finset.Ico (min k₀ 1) 1 :=
    Finset.Ico_subset_Ico (min_le_left _ _) (min_le_right _ _)
  have h1 : ∑ k ∈ Finset.Ico k₀ (min k₁ 1), ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ) ≤
      ∑ k ∈ Finset.Ico (min k₀ 1) 1, ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  set n := (1 - min k₀ 1).toNat
  have hbij : ∑ k ∈ Finset.Ico (min k₀ 1) 1, ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ) =
      ∑ j ∈ Finset.range n, ((2 : ℝ) ^ (-(j : ℤ))) ^ (1 / 2 : ℝ) := by
    refine Finset.sum_bij (fun k _ => (-k).toNat) ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_Ico] at hk
      rw [Finset.mem_range]
      omega
    · intro a ha b hb hab
      rw [Finset.mem_Ico] at ha hb
      omega
    · intro j hj
      rw [Finset.mem_range] at hj
      refine ⟨-(j : ℤ), Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro k hk
      rw [Finset.mem_Ico] at hk
      congr 2; omega
  have hgeom : ∑ j ∈ Finset.range n, ((2 : ℝ) ^ (-(j : ℤ))) ^ (1 / 2 : ℝ) ≤ 4 := by
    set r := (2 : ℝ) ^ (-(1 / 2 : ℝ))
    have hr_nn : 0 ≤ r := by positivity
    have hr_lt : r < 1 := by
      dsimp [r]
      rw [Real.rpow_neg zero_le_two, inv_lt_one_iff₀]
      right; exact Real.one_lt_rpow one_lt_two (by norm_num)
    have hpow_eq : ∀ j : ℕ, ((2 : ℝ) ^ (-(j : ℤ))) ^ (1 / 2 : ℝ) = r ^ j := fun j => by
      rw [zpow_neg, zpow_natCast, ← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_neg zero_le_two,
        ← Real.rpow_mul zero_le_two, ← Real.rpow_natCast r j, ← Real.rpow_mul zero_le_two]
      ring_nf
    simp_rw [hpow_eq]
    have hsum := geom_sum_le_inv_one_sub hr_nn hr_lt n
    have hr_ub : r ≤ 3 / 4 := by
      have hsq : r ^ 2 = 1 / 2 := by
        rw [← Real.rpow_natCast r 2, ← Real.rpow_mul zero_le_two]
        norm_num
      have : r ^ 2 ≤ (3 / 4 : ℝ) ^ 2 := by rw [hsq]; norm_num
      exact le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) this
    have hinv : 1 / (1 - r) ≤ 4 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  linarith

private lemma sum_dyadic_two_pow_neg_one (k₀ k₁ : ℤ) :
    ∑ k ∈ Finset.Ico (max k₀ 1) k₁, ((2 : ℝ) ^ k) ^ (-1 : ℝ) ≤ 1 := by
  rcases le_or_gt k₁ (max k₀ 1) with hk | hk
  · simp [Finset.Ico_eq_empty_of_le hk]
  have hsub : Finset.Ico (max k₀ 1) k₁ ⊆ Finset.Ico 1 (max k₁ 1) :=
    Finset.Ico_subset_Ico (le_max_right _ _) (le_max_left _ _)
  have h1 : ∑ k ∈ Finset.Ico (max k₀ 1) k₁, ((2 : ℝ) ^ k) ^ (-1 : ℝ) ≤
      ∑ k ∈ Finset.Ico 1 (max k₁ 1), ((2 : ℝ) ^ k) ^ (-1 : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  set n := (max k₁ 1 - 1).toNat
  have hbij : ∑ k ∈ Finset.Ico 1 (max k₁ 1), ((2 : ℝ) ^ k) ^ (-1 : ℝ) =
      ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ (j + 1) := by
    refine Finset.sum_bij (fun k _ => (k - 1).toNat) ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_Ico] at hk
      rw [Finset.mem_range]
      omega
    · intro a ha b hb hab
      rw [Finset.mem_Ico] at ha hb
      omega
    · intro j hj
      rw [Finset.mem_range] at hj
      refine ⟨(j : ℤ) + 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro k hk
      rw [Finset.mem_Ico] at hk
      rw [show (-1 : ℝ) = ((-1 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg, zpow_one,
        ← inv_zpow, show ((2 : ℝ)⁻¹) = (1 / 2 : ℝ) by norm_num, ← zpow_natCast]
      congr 1; omega
  have hgeom : ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ (j + 1) ≤ 1 := by
    have : ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ (j + 1) =
        (1 / 2 : ℝ) * ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j := by
      simp_rw [pow_succ', ← Finset.mul_sum]
    rw [this]
    have hs := geom_sum_le_inv_one_sub (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) n
    linarith
  linarith

private lemma dyadic_grid_sum_le {scale a b : ℝ} (hscale : 0 < scale) (hab : a ≤ b)
    {k₀ k₁ : ℤ} (hk₀ : (2 : ℝ) ^ k₀ * scale ≤ a) (hk₁ : b ≤ (2 : ℝ) ^ k₁ * scale)
    (F : ℝ → ℂ) (hF_int : IntervalIntegrable F volume a b)
    (term : ℤ → ℝ) (hterm_nn : ∀ k ∈ Finset.Ico k₀ k₁, 0 ≤ term k)
    (hterm : ∀ k ∈ Finset.Ico k₀ k₁, ∀ u v, a ≤ u → v ≤ b →
      (2 : ℝ) ^ k * scale ≤ u → u < v → v ≤ 2 * ((2 : ℝ) ^ k * scale) →
      ‖∫ τ in u..v, F τ‖ ≤ term k) :
    ‖∫ τ in a..b, F τ‖ ≤ ∑ k ∈ Finset.Ico k₀ k₁, term k := by
  have hk01 : k₀ ≤ k₁ := by
    by_contra hlt
    have hlt_pow : (2 : ℝ) ^ k₁ < (2 : ℝ) ^ k₀ :=
      zpow_lt_zpow_right₀ one_lt_two (not_le.mp hlt)
    have : (2 : ℝ) ^ k₁ * scale < (2 : ℝ) ^ k₀ * scale :=
      mul_lt_mul_of_pos_right hlt_pow hscale
    linarith
  let cgrid : ℤ → ℝ := fun k => max a (min b ((2 : ℝ) ^ k * scale))
  have hcgrid_mono : Monotone cgrid := fun i j hij =>
    max_le_max_left a (min_le_min_left b
      (mul_le_mul_of_nonneg_right (zpow_le_zpow_right₀ one_le_two hij) hscale.le))
  have hcgrid_k0 : cgrid k₀ = a := by
    dsimp [cgrid]
    rw [min_eq_right (hk₀.trans hab), max_eq_left hk₀]
  have hcgrid_k1 : cgrid k₁ = b := by
    dsimp [cgrid]
    rw [min_eq_left hk₁, max_eq_right hab]
  let n := (k₁ - k₀).toNat
  let grid : ℕ → ℝ := fun i => cgrid (k₀ + i)
  have hgrid0 : grid 0 = a := by simpa [grid] using hcgrid_k0
  have hgridn : grid n = b := by
    dsimp [grid, n]
    rw [Int.ofNat_toNat, max_eq_left (sub_nonneg.mpr hk01), add_sub_cancel]
    exact hcgrid_k1
  have hgrid_mono : Monotone grid := fun i j hij => hcgrid_mono (by omega)
  have hgrid_mem : ∀ i ≤ n, grid i ∈ Icc a b := fun i hi => by
    rw [← hgrid0, ← hgridn]
    exact ⟨hgrid_mono (Nat.zero_le i), hgrid_mono hi⟩
  have hsum_int : ∫ τ in a..b, F τ =
      ∑ i ∈ Finset.range n, ∫ τ in grid i..grid (i + 1), F τ := by
    rw [← hgrid0, ← hgridn]
    symm
    refine intervalIntegral.sum_integral_adjacent_intervals fun i hi => ?_
    refine hF_int.mono_set (uIcc_subset_uIcc ?_ ?_)
    · rw [uIcc_of_le hab]; exact hgrid_mem i (by omega)
    · rw [uIcc_of_le hab]; exact hgrid_mem (i + 1) (by omega)
  have hterm_i : ∀ i ∈ Finset.range n,
      ‖∫ τ in grid i..grid (i + 1), F τ‖ ≤ term (k₀ + i) := by
    intro i hi
    have hi_lt : i < n := Finset.mem_range.mp hi
    have hk_mem : k₀ + (i : ℤ) ∈ Finset.Ico k₀ k₁ := by
      rw [Finset.mem_Ico]; omega
    rcases eq_or_lt_of_le (hgrid_mono (Nat.le_succ i)) with heq | hlt
    · rw [heq, intervalIntegral.integral_same, norm_zero]
      exact hterm_nn _ hk_mem
    · set k : ℤ := k₀ + i
      set s : ℝ := (2 : ℝ) ^ k * scale
      have hs_u : s ≤ grid i := by
        by_contra hlt_s
        have hlt_grid : grid i < s := not_le.mp hlt_s
        have hmin_lt : min b s < s := lt_of_le_of_lt (le_max_right a _) hlt_grid
        have hbs : b < s := by
          by_contra hs_le_b
          rw [min_eq_right (not_lt.mp hs_le_b)] at hmin_lt
          exact lt_irrefl _ hmin_lt
        have hgi : grid i = b := by
          dsimp [grid, cgrid, s, k]
          rw [min_eq_left hbs.le, max_eq_right hab]
        have hgi1 : grid (i + 1) = b := by
          dsimp [grid, cgrid]
          have hs1 : b ≤ (2 : ℝ) ^ (k₀ + ((i : ℤ) + 1)) * scale :=
            hbs.le.trans (mul_le_mul_of_nonneg_right
              (zpow_le_zpow_right₀ one_le_two (by omega)) hscale.le)
          rw [min_eq_left hs1, max_eq_right hab]
        linarith
      have hv_le : grid (i + 1) ≤ 2 * s := by
        have hk1_eq : k₀ + ((i + 1 : ℕ) : ℤ) = k + 1 := by dsimp [k]; omega
        have h2s : 2 * s = (2 : ℝ) ^ (k + 1) * scale := by
          dsimp [s]
          conv_rhs => rw [zpow_add₀ two_ne_zero, zpow_one]
          ring
        rw [h2s]
        change cgrid (k₀ + ((i + 1 : ℕ) : ℤ)) ≤ (2 : ℝ) ^ (k + 1) * scale
        rw [hk1_eq]
        dsimp [cgrid]
        apply max_le
        · have ha_lt_min : a < min b ((2 : ℝ) ^ (k + 1) * scale) := by
            by_contra hle
            have hgi1 : grid (i + 1) = a := by
              change cgrid (k₀ + ((i + 1 : ℕ) : ℤ)) = a
              rw [hk1_eq]
              exact max_eq_left (not_lt.mp hle)
            have hgi : a ≤ grid i := (hgrid_mem i hi_lt.le).1
            linarith
          exact (ha_lt_min.trans_le (min_le_right _ _)).le
        · exact min_le_right _ _
      exact hterm k hk_mem (grid i) (grid (i + 1)) (hgrid_mem i hi_lt.le).1
        (hgrid_mem (i + 1) hi_lt).2 hs_u hlt hv_le
  have h_eq_sum : ∑ i ∈ Finset.range n, term (k₀ + i) = ∑ k ∈ Finset.Ico k₀ k₁, term k := by
    refine Finset.sum_bij (fun i _ => k₀ + (i : ℤ)) ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_range] at hi
      rw [Finset.mem_Ico]; omega
    · intro i _ j _ hij; omega
    · intro k hk
      rw [Finset.mem_Ico] at hk
      refine ⟨(k - k₀).toNat, Finset.mem_range.mpr (by omega), by omega⟩
    · intro i _; rfl
  calc ‖∫ τ in a..b, F τ‖
      ≤ ∑ i ∈ Finset.range n, ‖∫ τ in grid i..grid (i + 1), F τ‖ := by
        rw [hsum_int]; exact norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, term (k₀ + i) := Finset.sum_le_sum hterm_i
    _ = ∑ k ∈ Finset.Ico k₀ k₁, term k := h_eq_sum

private lemma dyadic_upper_sum_le (N : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (F : ℝ → ℂ) {g : ℝ → ℝ}
    (hg : ∀ s > 0, ∀ u v, a ≤ u → v ≤ b → s ≤ u → u ≤ v → v ≤ 2 * s →
      ‖∫ τ in u..v, F τ‖ ≤ g s * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2) / min (s ^ 2) 1)
    {G : ℝ} (hG_nn : 0 ≤ G) (hg_le : ∀ s > 0, g s ≤ G)
    (hF_int : IntervalIntegrable F volume a b) :
    ‖∫ τ in a..b, F τ‖ ≤
      G * (4 * (2 : ℝ) ^ max N 0 + (2 : ℝ) ^ max N 0 *
        ((Nat.factorial (Nat.ceil ((5 / 2 + max N 0 + 1) / 2)) : ℝ))) := by
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℤ, (2 : ℝ) ^ k₀ ≤ a := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (a⁻¹) one_lt_two
    refine ⟨-(n : ℤ), ?_⟩
    rw [zpow_neg, zpow_natCast, inv_le_comm₀ (by positivity) ha]
    exact hn.le
  obtain ⟨k₁, hk₁⟩ : ∃ k₁ : ℤ, b ≤ (2 : ℝ) ^ k₁ := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt b one_lt_two
    exact ⟨(n : ℤ), by simpa using hn.le⟩
  set m := Nat.ceil ((5 / 2 + max N 0 + 1) / 2)
  let term : ℤ → ℝ := fun k => G * ((2 : ℝ) ^ max N 0 *
    (if k < 1 then ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ) else (Nat.factorial m : ℝ) * ((2 : ℝ) ^ k) ^ (-1 : ℝ)))
  have hgrid := dyadic_grid_sum_le zero_lt_one hab (by simpa using hk₀) (by simpa using hk₁)
    F hF_int term (fun _ _ => by dsimp [term]; split_ifs <;> positivity)
    (fun k _ u v hau hvb hsu huv hv2s => by
      dsimp [term]
      rw [mul_one] at hsu hv2s
      set s : ℝ := (2 : ℝ) ^ k
      have hs_pos : 0 < s := by positivity
      have h_vdc := hg s hs_pos u v hau hvb hsu huv.le hv2s
      have h_g : g s ≤ G := hg_le s hs_pos
      have h_1s : (1 + s) ^ N ≤ (2 : ℝ) ^ max N 0 * (max 1 s) ^ max N 0 := by
        have h1 : (1 + s) ^ N ≤ (1 + s) ^ max N 0 :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left N 0)
        have h2 : 1 + s ≤ 2 * max 1 s := by
          have := le_max_left (1 : ℝ) s
          have := le_max_right (1 : ℝ) s
          linarith
        have h3 : (1 + s) ^ max N 0 ≤ (2 * max 1 s) ^ max N 0 :=
          Real.rpow_le_rpow (by linarith) h2 (le_max_right N 0)
        rw [Real.mul_rpow (by norm_num) (by positivity)] at h3
        exact h1.trans h3
      split_ifs with hk1_lt
      · have hs_le_one : s ≤ 1 := by
          dsimp [s]; rw [← zpow_zero (2 : ℝ)]; exact zpow_le_zpow_right₀ one_le_two (by omega)
        have hmin : min (s ^ 2) 1 = s ^ 2 := min_eq_left (by nlinarith)
        have hmax : max 1 s = 1 := max_eq_left hs_le_one
        rw [hmax] at h_1s
        have hexp : Real.exp (-s ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        have h_srpow : s ^ (5 / 2 : ℝ) / s ^ 2 = s ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_natCast s 2, ← Real.rpow_sub hs_pos]; norm_num
        have hnum : g s * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2) ≤
            G * s ^ (5 / 2 : ℝ) * ((2 : ℝ) ^ max N 0 * (1 : ℝ) ^ max N 0) * 1 :=
          mul_le_mul
            (mul_le_mul (mul_le_mul_of_nonneg_right h_g (by positivity)) h_1s (by positivity) (by positivity))
            hexp (by positivity) (by positivity)
        calc ‖∫ τ in u..v, F τ‖
            ≤ g s * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2) / min (s ^ 2) 1 := h_vdc
          _ ≤ G * s ^ (5 / 2 : ℝ) * ((2 : ℝ) ^ max N 0 * 1 ^ max N 0) * 1 / s ^ 2 := by
              rw [hmin]
              exact div_le_div_of_nonneg_right hnum (by positivity)
          _ = G * ((2 : ℝ) ^ max N 0 * (s ^ (5 / 2 : ℝ) / s ^ 2)) := by
              simp only [Real.one_rpow, mul_one]; ring
          _ = G * ((2 : ℝ) ^ max N 0 * s ^ (1 / 2 : ℝ)) := by rw [h_srpow]
      · have hs_ge_one : 1 ≤ s := by
          dsimp [s]; rw [← zpow_zero (2 : ℝ)]; exact zpow_le_zpow_right₀ one_le_two (by omega)
        have hmin : min (s ^ 2) 1 = 1 := min_eq_right (by nlinarith)
        have hmax : max 1 s = s := max_eq_right hs_ge_one
        rw [hmax] at h_1s
        have hrpow := rpow_mul_exp_neg_sq_le (p := 5 / 2 + max N 0) (q := 1) hs_ge_one (x := s)
        have h_pow_comb : s ^ (5 / 2 : ℝ) * s ^ max N 0 = s ^ (5 / 2 + max N 0) :=
          (Real.rpow_add hs_pos _ _).symm
        have hnum : g s * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2) ≤
            G * s ^ (5 / 2 : ℝ) * ((2 : ℝ) ^ max N 0 * s ^ max N 0) * Real.exp (-s ^ 2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (mul_le_mul_of_nonneg_right h_g (by positivity)) h_1s (by positivity) (by positivity))
            (by positivity)
        calc ‖∫ τ in u..v, F τ‖
            ≤ g s * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2) / min (s ^ 2) 1 := h_vdc
          _ ≤ G * s ^ (5 / 2 : ℝ) * ((2 : ℝ) ^ max N 0 * s ^ max N 0) * Real.exp (-s ^ 2) / 1 := by
              rw [hmin]
              exact div_le_div_of_nonneg_right hnum zero_le_one
          _ = G * ((2 : ℝ) ^ max N 0 * (s ^ (5 / 2 + max N 0) * Real.exp (-s ^ 2))) := by
              rw [← h_pow_comb]; ring
          _ ≤ G * ((2 : ℝ) ^ max N 0 * ((Nat.factorial m : ℝ) * s ^ (-1 : ℝ))) := by gcongr)
  have h_sum_term : ∑ k ∈ Finset.Ico k₀ k₁, term k ≤
      G * (4 * (2 : ℝ) ^ max N 0 + (2 : ℝ) ^ max N 0 * (Nat.factorial m : ℝ)) := by
    dsimp [term]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hG_nn
    have hsplit : ∀ k : ℤ,
        (if k < 1 then ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ) else (Nat.factorial m : ℝ) * ((2 : ℝ) ^ k) ^ (-1 : ℝ)) =
        (if k < 1 then ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ) else 0) +
        (if 1 ≤ k then (Nat.factorial m : ℝ) * ((2 : ℝ) ^ k) ^ (-1 : ℝ) else 0) := fun k => by
      split_ifs <;> first | omega | ring
    simp_rw [hsplit, Finset.sum_add_distrib]
    have hA : ∑ k ∈ Finset.Ico k₀ k₁,
        (if k < 1 then ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ) else 0) ≤ 4 := by
      rw [← Finset.sum_filter,
        show Finset.filter (· < 1) (Finset.Ico k₀ k₁) = Finset.Ico k₀ (min k₁ 1) by ext; simp]
      exact sum_dyadic_two_pow_neg_half k₀ k₁
    have hB : ∑ k ∈ Finset.Ico k₀ k₁,
        (if 1 ≤ k then (Nat.factorial m : ℝ) * ((2 : ℝ) ^ k) ^ (-1 : ℝ) else 0) ≤
        (Nat.factorial m : ℝ) := by
      rw [← Finset.sum_filter,
        show Finset.filter (1 ≤ ·) (Finset.Ico k₀ k₁) = Finset.Ico (max k₀ 1) k₁ by ext; simp,
        ← Finset.mul_sum]
      calc (Nat.factorial m : ℝ) * ∑ k ∈ Finset.Ico (max k₀ 1) k₁, ((2 : ℝ) ^ k) ^ (-1 : ℝ)
          ≤ (Nat.factorial m : ℝ) * 1 := by gcongr; exact sum_dyadic_two_pow_neg_one k₀ k₁
        _ = (Nat.factorial m : ℝ) := mul_one _
    calc (2 : ℝ) ^ max N 0 *
          (∑ x ∈ Finset.Ico k₀ k₁, (if x < 1 then ((2 : ℝ) ^ x) ^ (1 / 2 : ℝ) else 0) +
           ∑ x ∈ Finset.Ico k₀ k₁, (if 1 ≤ x then (Nat.factorial m : ℝ) * ((2 : ℝ) ^ x) ^ (-1 : ℝ) else 0))
        ≤ (2 : ℝ) ^ max N 0 * (4 + (Nat.factorial m : ℝ)) :=
          mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity)
      _ = 4 * (2 : ℝ) ^ max N 0 + (2 : ℝ) ^ max N 0 * (Nat.factorial m : ℝ) := by ring
  exact hgrid.trans h_sum_term

private lemma dyadic_lower_small_sum_le (N : ℝ) {τ₀ a b : ℝ} (hτ₀_pos : 0 < τ₀) (hτ₀_le : τ₀ ≤ 1)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ τ₀ / 2)
    (F : ℝ → ℂ) {g : ℝ → ℝ}
    (hg : ∀ s > 0, ∀ u v, a ≤ u → v ≤ b → s ≤ u → u ≤ v → v ≤ 2 * s →
      ‖∫ τ in u..v, F τ‖ ≤ g s * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2) / (τ₀ ^ 2))
    {G : ℝ} (hG_nn : 0 ≤ G) (hg_le : ∀ s > 0, g s ≤ G)
    (hF_int : IntervalIntegrable F volume a b) :
    ‖∫ τ in a..b, F τ‖ ≤ G * (2 : ℝ) ^ max N 0 := by
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℤ, (2 : ℝ) ^ k₀ * τ₀ ≤ a := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (τ₀ / a) one_lt_two
    refine ⟨-(n : ℤ), ?_⟩
    rw [zpow_neg, zpow_natCast, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    have h1 := hn.le
    rw [div_le_iff₀ ha] at h1
    linarith
  have hk₁ : b ≤ (2 : ℝ) ^ (-1 : ℤ) * τ₀ := by
    calc b ≤ τ₀ / 2 := hb
      _ = (2 : ℝ) ^ (-1 : ℤ) * τ₀ := by norm_num; ring
  let term : ℤ → ℝ := fun k => G * (2 : ℝ) ^ max N 0 * ((2 : ℝ) ^ k) ^ (5 / 2 : ℝ)
  have hgrid := dyadic_grid_sum_le hτ₀_pos hab hk₀ hk₁ F hF_int term
    (fun _ _ => by dsimp [term]; positivity)
    (fun k hk_mem u v hau hvb hsu huv hv2s => by
      dsimp [term]
      rw [Finset.mem_Ico] at hk_mem
      set s : ℝ := (2 : ℝ) ^ k * τ₀
      have hs_pos : 0 < s := by positivity
      have hk_le_m2 : k ≤ -2 := by omega
      have hs_le_one : s ≤ 1 := by
        have : (2 : ℝ) ^ k ≤ 1 := by
          rw [← zpow_zero (2 : ℝ)]; exact zpow_le_zpow_right₀ one_le_two (by omega)
        calc s = (2 : ℝ) ^ k * τ₀ := rfl
          _ ≤ 1 * 1 := mul_le_mul this hτ₀_le hτ₀_pos.le zero_le_one
          _ = 1 := one_mul 1
      have h_vdc := hg s hs_pos u v hau hvb hsu huv.le hv2s
      have h_1s : (1 + s) ^ N ≤ (2 : ℝ) ^ max N 0 := by
        have h1 : (1 + s) ^ N ≤ (1 + s) ^ max N 0 :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left N 0)
        have h2 : (1 + s) ^ max N 0 ≤ 2 ^ max N 0 :=
          Real.rpow_le_rpow (by linarith) (by linarith) (le_max_right N 0)
        exact h1.trans h2
      have hexp : Real.exp (-s ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have h_g : g s ≤ G := hg_le s hs_pos
      have hs_rpow : s ^ (5 / 2 : ℝ) / τ₀ ^ 2 =
          ((2 : ℝ) ^ k) ^ (5 / 2 : ℝ) * τ₀ ^ (1 / 2 : ℝ) := by
        dsimp [s]
        rw [Real.mul_rpow (by positivity) hτ₀_pos.le, ← Real.rpow_natCast τ₀ 2]
        simp only [Nat.cast_ofNat]
        have hτ_div : τ₀ ^ (5 / 2 : ℝ) / τ₀ ^ (2 : ℝ) = τ₀ ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_sub hτ₀_pos]; norm_num
        rw [mul_div_assoc, hτ_div]
      have hτ_half : τ₀ ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hτ₀_pos.le hτ₀_le (by norm_num)
      have hnum : g s * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2) ≤
          G * s ^ (5 / 2 : ℝ) * (2 : ℝ) ^ max N 0 * 1 :=
        mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right h_g (by positivity))
          h_1s (by positivity) (by positivity)) hexp (by positivity) (by positivity)
      calc ‖∫ τ in u..v, F τ‖
          ≤ g s * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2) / τ₀ ^ 2 := h_vdc
        _ ≤ G * s ^ (5 / 2 : ℝ) * (2 : ℝ) ^ max N 0 * 1 / τ₀ ^ 2 :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ = G * (2 : ℝ) ^ max N 0 * (s ^ (5 / 2 : ℝ) / τ₀ ^ 2) := by ring
        _ = G * (2 : ℝ) ^ max N 0 * (((2 : ℝ) ^ k) ^ (5 / 2 : ℝ) * τ₀ ^ (1 / 2 : ℝ)) := by rw [hs_rpow]
        _ ≤ G * (2 : ℝ) ^ max N 0 * (((2 : ℝ) ^ k) ^ (5 / 2 : ℝ) * 1) := by gcongr
        _ = G * (2 : ℝ) ^ max N 0 * ((2 : ℝ) ^ k) ^ (5 / 2 : ℝ) := by ring)
  have h_sum_geom : ∑ k ∈ Finset.Ico k₀ (-1), term k ≤ G * (2 : ℝ) ^ max N 0 := by
    dsimp [term]
    rw [← Finset.mul_sum]
    nth_rw 2 [← mul_one (G * (2 : ℝ) ^ max N 0)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    set r := (2 : ℝ) ^ (-(5 / 2 : ℝ))
    set n := (-1 - k₀).toNat
    have hr_nn : 0 ≤ r := by positivity
    have hr_lt : r < 1 := by
      dsimp [r]
      rw [Real.rpow_neg zero_le_two, inv_lt_one_iff₀]
      right; exact Real.one_lt_rpow one_lt_two (by norm_num)
    have hbij : ∑ k ∈ Finset.Ico k₀ (-1), ((2 : ℝ) ^ k) ^ (5 / 2 : ℝ) =
        ∑ j ∈ Finset.range n, r ^ (j + 2) := by
      refine Finset.sum_bij (fun k _ => (-2 - k).toNat) ?_ ?_ ?_ ?_
      · intro k hk
        rw [Finset.mem_Ico] at hk
        rw [Finset.mem_range]
        dsimp [n]; omega
      · intro a ha b hb hab
        rw [Finset.mem_Ico] at ha hb
        omega
      · intro j hj
        rw [Finset.mem_range] at hj
        dsimp [n] at hj
        refine ⟨-((j + 2 : ℕ) : ℤ), Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro k hk
        rw [Finset.mem_Ico] at hk
        have hk2 : k = -((((-2 - k).toNat + 2 : ℕ) : ℤ)) := by omega
        conv_lhs => rw [hk2]
        rw [zpow_neg, zpow_natCast, ← Real.rpow_natCast (2 : ℝ) ((-2 - k).toNat + 2),
          ← Real.rpow_neg zero_le_two, ← Real.rpow_mul zero_le_two,
          ← Real.rpow_natCast r ((-2 - k).toNat + 2), ← Real.rpow_mul zero_le_two]
        ring_nf
    have hr2 : r ^ 2 ≤ 1 / 4 := by
      have hsq : r ^ 2 = (2 : ℝ) ^ (-5 : ℝ) := by
        rw [← Real.rpow_natCast r 2, ← Real.rpow_mul zero_le_two]; norm_num
      rw [hsq, show (-5 : ℝ) = ((-5 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg]
      norm_num
    have hr_ub : r ≤ 1 / 2 := by nlinarith
    have hsum_tail : ∑ j ∈ Finset.range n, r ^ (j + 2) ≤ 1 := by
      have : ∑ j ∈ Finset.range n, r ^ (j + 2) = r ^ 2 * ∑ j ∈ Finset.range n, r ^ j := by
        calc ∑ j ∈ Finset.range n, r ^ (j + 2)
            = ∑ j ∈ Finset.range n, r ^ 2 * r ^ j := Finset.sum_congr rfl fun j _ => by ring
          _ = r ^ 2 * ∑ j ∈ Finset.range n, r ^ j := (Finset.mul_sum _ _ _).symm
      rw [this]
      have hgs := geom_sum_le_inv_one_sub hr_nn hr_lt n
      have h1r : 1 / (1 - r) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      nlinarith
    exact hbij.symm ▸ hsum_tail
  exact hgrid.trans h_sum_geom

private lemma nonneg_of_hh_bv_unit {h : ℝ → ℂ} {N M : ℝ}
    (hh_bv : ∀ s > 0, BoundedVariationOn h (Icc s (2 * s)) ∧
      ∀ τ ∈ Icc s (2 * s), ‖h τ‖ + (eVariationOn h (Icc s (2 * s))).toReal ≤
        M * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2)) :
    0 ≤ M := by
  have h1 := (hh_bv 1 zero_lt_one).2 1 ⟨le_rfl, by norm_num⟩
  have h_pos : 0 < (1 : ℝ) ^ (5 / 2 : ℝ) * (1 + 1) ^ N * Real.exp (-1 ^ 2) := by positivity
  have h_le : 0 ≤ M * ((1 : ℝ) ^ (5 / 2 : ℝ) * (1 + 1) ^ N * Real.exp (-1 ^ 2)) := by
    calc 0 ≤ ‖h 1‖ + (eVariationOn h (Icc 1 (2 * 1))).toReal := by positivity
      _ ≤ M * (1 : ℝ) ^ (5 / 2 : ℝ) * (1 + 1) ^ N * Real.exp (-1 ^ 2) := h1
      _ = M * ((1 : ℝ) ^ (5 / 2 : ℝ) * (1 + 1) ^ N * Real.exp (-1 ^ 2)) := by ring
  exact nonneg_of_mul_nonneg_left h_le h_pos

private lemma teb_middle_envelope (N : ℝ) {τ₀ s : ℝ} (hs : s ∈ Icc (τ₀ / 2) τ₀) (hτ₀ : 0 < τ₀) :
    s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2) ≤
      τ₀ ^ (5 / 2 : ℝ) * (1 + τ₀) ^ max N 0 * Real.exp (-τ₀ ^ 2 / 4) := by
  have hs_pos : 0 < s := lt_of_lt_of_le (by positivity) hs.1
  have h1 : s ^ (5 / 2 : ℝ) ≤ τ₀ ^ (5 / 2 : ℝ) :=
    Real.rpow_le_rpow hs_pos.le hs.2 (by norm_num)
  have h2 : (1 + s) ^ N ≤ (1 + τ₀) ^ max N 0 := by
    have ha1 : (1 + s) ^ N ≤ (1 + s) ^ max N 0 :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left N 0)
    have ha2 : (1 + s) ^ max N 0 ≤ (1 + τ₀) ^ max N 0 :=
      Real.rpow_le_rpow (by linarith) (by linarith [hs.2]) (le_max_right N 0)
    exact ha1.trans ha2
  have h3 : Real.exp (-s ^ 2) ≤ Real.exp (-τ₀ ^ 2 / 4) :=
    Real.exp_le_exp.mpr (by nlinarith [hs.1])
  gcongr

private lemma teb_middle_core_le (N : ℝ) {τ₀ : ℝ} (hτ₀ : 0 < τ₀) :
    τ₀ ^ 2 * √(1 + τ₀ ^ 3) * (1 + τ₀) ^ max N 0 * Real.exp (-τ₀ ^ 2 / 4) ≤
      √2 * (2 : ℝ) ^ max N 0 *
        max 1 ((Nat.factorial (Nat.ceil ((7 / 2 + max N 0) / 2)) : ℝ) *
          4 ^ (Nat.ceil ((7 / 2 + max N 0) / 2))) *
        min (τ₀ ^ 2) 1 := by
  set m_idx := Nat.ceil ((7 / 2 + max N 0) / 2)
  rcases le_or_gt τ₀ 1 with hle1 | hgt1
  · have hmin : min (τ₀ ^ 2) 1 = τ₀ ^ 2 := min_eq_left (by nlinarith)
    have h1 : √(1 + τ₀ ^ 3) ≤ √2 := Real.sqrt_le_sqrt (by nlinarith [pow_nonneg hτ₀.le 3])
    have h2 : (1 + τ₀) ^ max N 0 ≤ (2 : ℝ) ^ max N 0 :=
      Real.rpow_le_rpow (by linarith) (by linarith) (le_max_right N 0)
    have h3 : Real.exp (-τ₀ ^ 2 / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hmax : (1 : ℝ) ≤ max 1 ((Nat.factorial m_idx : ℝ) * 4 ^ m_idx) := le_max_left _ _
    rw [hmin]
    calc τ₀ ^ 2 * √(1 + τ₀ ^ 3) * (1 + τ₀) ^ max N 0 * Real.exp (-τ₀ ^ 2 / 4)
        ≤ τ₀ ^ 2 * √2 * (2 : ℝ) ^ max N 0 * 1 := by gcongr
      _ = √2 * (2 : ℝ) ^ max N 0 * 1 * τ₀ ^ 2 := by ring
      _ ≤ √2 * (2 : ℝ) ^ max N 0 * max 1 ((Nat.factorial m_idx : ℝ) * 4 ^ m_idx) * τ₀ ^ 2 := by
          gcongr
  · have hmin : min (τ₀ ^ 2) 1 = 1 := min_eq_right (by nlinarith)
    have h1 : √(1 + τ₀ ^ 3) ≤ √2 * τ₀ ^ (3 / 2 : ℝ) := by
      have hone : (1 : ℝ) ≤ τ₀ ^ 3 := one_le_pow₀ hgt1.le
      have hle : 1 + τ₀ ^ 3 ≤ 2 * τ₀ ^ 3 := by linarith
      calc √(1 + τ₀ ^ 3) ≤ √(2 * τ₀ ^ 3) := Real.sqrt_le_sqrt hle
        _ = √2 * √(τ₀ ^ 3) := Real.sqrt_mul zero_le_two _
        _ = √2 * τ₀ ^ (3 / 2 : ℝ) := by
            congr 1
            rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast τ₀ 3, ← Real.rpow_mul hτ₀.le]
            norm_num
    have h2 : (1 + τ₀) ^ max N 0 ≤ (2 : ℝ) ^ max N 0 * τ₀ ^ max N 0 := by
      have hle : 1 + τ₀ ≤ 2 * τ₀ := by linarith
      rw [← Real.mul_rpow (by norm_num) hτ₀.le]
      exact Real.rpow_le_rpow (by linarith) hle (le_max_right N 0)
    have hexp_bound : τ₀ ^ (7 / 2 + max N 0) * Real.exp (-τ₀ ^ 2 / 4) ≤
        (Nat.factorial m_idx : ℝ) * 4 ^ m_idx := by
      have h_taylor : (τ₀ ^ 2 / 4) ^ m_idx / (Nat.factorial m_idx : ℝ) ≤ Real.exp (τ₀ ^ 2 / 4) := by
        have hs := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ τ₀ ^ 2 / 4) (m_idx + 1)
        exact (Finset.single_le_sum (f := fun i => (τ₀ ^ 2 / 4) ^ i / (Nat.factorial i : ℝ))
          (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self m_idx))).trans hs
      have hm_ge : 7 / 2 + max N 0 ≤ 2 * (m_idx : ℝ) := by
        have := Nat.le_ceil ((7 / 2 + max N 0) / 2)
        change (7 / 2 + max N 0) / 2 ≤ (m_idx : ℝ) at this
        linarith
      have hexp_inv : Real.exp (-τ₀ ^ 2 / 4) ≤
          (Nat.factorial m_idx : ℝ) * 4 ^ m_idx * τ₀ ^ (-(2 * (m_idx : ℝ))) := by
        rw [show -τ₀ ^ 2 / 4 = -(τ₀ ^ 2 / 4) by ring, Real.exp_neg]
        have hpow : (τ₀ ^ 2 / 4) ^ m_idx = τ₀ ^ (2 * (m_idx : ℝ)) / 4 ^ m_idx := by
          rw [div_pow, ← Real.rpow_natCast (τ₀ ^ 2) m_idx, ← Real.rpow_natCast τ₀ 2,
            ← Real.rpow_mul hτ₀.le]
          ring_nf
        rw [hpow] at h_taylor
        have hinv : (Real.exp (τ₀ ^ 2 / 4))⁻¹ ≤
            (τ₀ ^ (2 * (m_idx : ℝ)) / 4 ^ m_idx / (Nat.factorial m_idx : ℝ))⁻¹ :=
          inv_anti₀ (by positivity) h_taylor
        rw [Real.rpow_neg hτ₀.le]
        calc (Real.exp (τ₀ ^ 2 / 4))⁻¹
            ≤ (τ₀ ^ (2 * (m_idx : ℝ)) / 4 ^ m_idx / (Nat.factorial m_idx : ℝ))⁻¹ := hinv
          _ = (Nat.factorial m_idx : ℝ) * 4 ^ m_idx * (τ₀ ^ (2 * (m_idx : ℝ)))⁻¹ := by
              rw [inv_div, div_eq_mul_inv, inv_div]; ring
      have h_rpow_le : τ₀ ^ (7 / 2 + max N 0 - 2 * (m_idx : ℝ)) ≤ 1 := by
        calc τ₀ ^ (7 / 2 + max N 0 - 2 * (m_idx : ℝ))
            ≤ τ₀ ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hgt1.le (by linarith)
          _ = 1 := Real.rpow_zero _
      calc τ₀ ^ (7 / 2 + max N 0) * Real.exp (-τ₀ ^ 2 / 4)
          ≤ τ₀ ^ (7 / 2 + max N 0) *
              ((Nat.factorial m_idx : ℝ) * 4 ^ m_idx * τ₀ ^ (-(2 * (m_idx : ℝ)))) := by gcongr
        _ = (Nat.factorial m_idx : ℝ) * 4 ^ m_idx *
              (τ₀ ^ (7 / 2 + max N 0) * τ₀ ^ (-(2 * (m_idx : ℝ)))) := by ring
        _ = (Nat.factorial m_idx : ℝ) * 4 ^ m_idx * τ₀ ^ (7 / 2 + max N 0 - 2 * (m_idx : ℝ)) := by
            rw [← Real.rpow_add hτ₀, sub_eq_add_neg]
        _ ≤ (Nat.factorial m_idx : ℝ) * 4 ^ m_idx * 1 := by gcongr
        _ = (Nat.factorial m_idx : ℝ) * 4 ^ m_idx := mul_one _
    have h_comb : τ₀ ^ 2 * τ₀ ^ (3 / 2 : ℝ) * τ₀ ^ max N 0 = τ₀ ^ (7 / 2 + max N 0) := by
      rw [← Real.rpow_natCast τ₀ 2, ← Real.rpow_add hτ₀, ← Real.rpow_add hτ₀]
      congr 1; norm_num
    rw [hmin, mul_one]
    calc τ₀ ^ 2 * √(1 + τ₀ ^ 3) * (1 + τ₀) ^ max N 0 * Real.exp (-τ₀ ^ 2 / 4)
        ≤ τ₀ ^ 2 * (√2 * τ₀ ^ (3 / 2 : ℝ)) * ((2 : ℝ) ^ max N 0 * τ₀ ^ max N 0) *
            Real.exp (-τ₀ ^ 2 / 4) := by gcongr
      _ = √2 * (2 : ℝ) ^ max N 0 * (τ₀ ^ (7 / 2 + max N 0) * Real.exp (-τ₀ ^ 2 / 4)) := by
          rw [← h_comb]; ring
      _ ≤ √2 * (2 : ℝ) ^ max N 0 * ((Nat.factorial m_idx : ℝ) * 4 ^ m_idx) := by gcongr
      _ ≤ √2 * (2 : ℝ) ^ max N 0 * max 1 ((Nat.factorial m_idx : ℝ) * 4 ^ m_idx) := by
          gcongr; exact le_max_right _ _

private lemma teb_middle_alg {b₀ N M c τ₀ : ℝ} (hb₀ : 0 < b₀) (hc : 0 < c) (hτ₀ : 0 < τ₀) :
    16 * (M * (τ₀ ^ (5 / 2 : ℝ) * (1 + τ₀) ^ max N 0 * Real.exp (-τ₀ ^ 2 / 4))) /
        √(c * (b₀ * τ₀ / (1 + τ₀ ^ 3))) =
      16 * (√b₀)⁻¹ * M * c ^ (-(1 / 2 : ℝ)) *
        (τ₀ ^ 2 * √(1 + τ₀ ^ 3) * (1 + τ₀) ^ max N 0 * Real.exp (-τ₀ ^ 2 / 4)) := by
  have hsqrt_prod : √(c * (b₀ * τ₀ / (1 + τ₀ ^ 3))) =
      √c * √b₀ * √τ₀ / √(1 + τ₀ ^ 3) := by
    rw [Real.sqrt_mul hc.le, Real.sqrt_div (mul_nonneg hb₀.le hτ₀.le), Real.sqrt_mul hb₀.le]
    ring
  have h_rpow_half : c ^ (-(1 / 2 : ℝ)) = (√c)⁻¹ := by
    rw [Real.rpow_neg hc.le, Real.sqrt_eq_rpow]
  have hτ_split : τ₀ ^ (5 / 2 : ℝ) / √τ₀ = τ₀ ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hτ₀, ← Real.rpow_natCast τ₀ 2]
    norm_num
  rw [hsqrt_prod, h_rpow_half]
  have hc_ne : √c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hb_ne : √b₀ ≠ 0 := (Real.sqrt_pos.mpr hb₀).ne'
  have ht_ne : √τ₀ ≠ 0 := (Real.sqrt_pos.mpr hτ₀).ne'
  have h1t_ne : √(1 + τ₀ ^ 3) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  calc 16 * (M * (τ₀ ^ (5 / 2 : ℝ) * (1 + τ₀) ^ max N 0 * Real.exp (-τ₀ ^ 2 / 4))) /
        (√c * √b₀ * √τ₀ / √(1 + τ₀ ^ 3))
      = 16 * (√b₀)⁻¹ * M * (√c)⁻¹ *
          ((τ₀ ^ (5 / 2 : ℝ) / √τ₀) * √(1 + τ₀ ^ 3) * (1 + τ₀) ^ max N 0 *
            Real.exp (-τ₀ ^ 2 / 4)) := by field_simp
    _ = 16 * (√b₀)⁻¹ * M * (√c)⁻¹ *
          (τ₀ ^ 2 * √(1 + τ₀ ^ 3) * (1 + τ₀) ^ max N 0 * Real.exp (-τ₀ ^ 2 / 4)) := by
          rw [hτ_split]

/-- Explicit constant `C(b₀, N)` in Lemma TE.1a (`teb:edge-osc`). -/
noncomputable def tebOscConst (b₀ N : ℝ) : ℝ :=
  let C_poly := (2 : ℝ) ^ max N 0 * (4 + (Nat.factorial (Nat.ceil ((5 / 2 + max N 0 + 1) / 2)) : ℝ))
  let C_mid := 16 * (√b₀)⁻¹ * √2 * (2 : ℝ) ^ max N 0 *
    max 1 ((Nat.factorial (Nat.ceil ((7 / 2 + max N 0) / 2)) : ℝ) * 4 ^ (Nat.ceil ((7 / 2 + max N 0) / 2)))
  max (6 * b₀⁻¹ * C_poly + 3 * b₀⁻¹ * (2 : ℝ) ^ max N 0) C_mid

lemma tebOscConst_pos {b₀ : ℝ} (hb₀ : 0 < b₀) (N : ℝ) : 0 < tebOscConst b₀ N := by
  unfold tebOscConst
  dsimp only
  have h1 : 0 < 6 * b₀⁻¹ * ((2 : ℝ) ^ max N 0 *
      (4 + (Nat.factorial (Nat.ceil ((5 / 2 + max N 0 + 1) / 2)) : ℝ))) + 3 * b₀⁻¹ * (2 : ℝ) ^ max N 0 := by
    positivity
  exact lt_of_lt_of_le h1 (le_max_left _ _)

private lemma teb_osc_continuousOn {w w' φ φ' : ℝ → ℝ} {h : ℝ → ℂ} (c : ℝ)
    (hw : ∀ τ, 0 < τ → HasDerivAt w (w' τ) τ)
    (hw_cont : ContinuousOn w' (Ioi 0))
    (hφ : ∀ y ∈ w '' Ioi 0, HasDerivAt φ (φ' y) y)
    (hh_cont : ContinuousOn h (Ioi 0)) :
    ContinuousOn
      (fun τ => h τ * (w' τ : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ (w τ) : ℂ)))
      (Ioi 0) := by
  have hw_cont_val : ContinuousOn w (Ioi 0) := fun τ hτ => (hw τ hτ).continuousAt.continuousWithinAt
  have hφ_cont : ContinuousOn φ (w '' Ioi 0) := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact (hφ (w τ) ⟨τ, hτ, rfl⟩).continuousAt.continuousWithinAt
  refine (hh_cont.mul (Complex.continuous_ofReal.continuousOn.comp hw_cont (mapsTo_univ _ _))).mul ?_
  exact Complex.continuous_exp.continuousOn.comp (continuousOn_const.mul
    (Complex.continuous_ofReal.continuousOn.comp
      (hφ_cont.comp hw_cont_val (fun τ hτ => ⟨τ, hτ, rfl⟩)) (mapsTo_univ _ _)))
    (mapsTo_univ _ _)

private lemma teb_osc_intervalIntegrable {w w' φ φ' : ℝ → ℝ} {h : ℝ → ℂ} (c : ℝ) {u v : ℝ}
    (hw : ∀ τ, 0 < τ → HasDerivAt w (w' τ) τ)
    (hw_cont : ContinuousOn w' (Ioi 0))
    (hφ : ∀ y ∈ w '' Ioi 0, HasDerivAt φ (φ' y) y)
    (hh_cont : ContinuousOn h (Ioi 0))
    (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable
      (fun τ => h τ * (w' τ : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ (w τ) : ℂ)))
      volume u v := by
  have hsub : uIcc u v ⊆ Ioi 0 := fun τ hτ => lt_of_lt_of_le (lt_min hu hv) hτ.1
  exact ((teb_osc_continuousOn c hw hw_cont hφ hh_cont).mono hsub).intervalIntegrable

private lemma teb_osc_vdc1_block {w w' φ φ' φ'' : ℝ → ℝ} {h : ℝ → ℂ}
    {N M c u v s lam : ℝ}
    (hc_pos : 0 < c)
    (hw : ∀ τ, 0 < τ → HasDerivAt w (w' τ) τ)
    (hw_cont : ContinuousOn w' (Ioi 0))
    (hw_pos : ∀ τ, 0 < τ → 0 < w' τ)
    (hφ : ∀ y ∈ w '' Ioi 0, HasDerivAt φ (φ' y) y)
    (hφ' : ∀ y ∈ w '' Ioi 0, HasDerivAt φ' (φ'' y) y)
    (hφ'_mono : MonotoneOn φ' (w '' Ioi 0) ∨ AntitoneOn φ' (w '' Ioi 0))
    (hh_cont : ContinuousOn h (Ioi 0))
    (hh_bv : ∀ s > 0, BoundedVariationOn h (Icc s (2 * s)) ∧
      ∀ τ ∈ Icc s (2 * s), ‖h τ‖ + (eVariationOn h (Icc s (2 * s))).toReal ≤
        M * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2))
    (hs : 0 < s) (hsu : s ≤ u) (huv : u ≤ v) (hv2s : v ≤ 2 * s) (hlam : 0 < lam)
    (hlb : ∀ τ ∈ Icc u v, lam ≤ |φ' (w τ)|) :
    ‖∫ τ in u..v, h τ * (w' τ : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ (w τ) : ℂ))‖ ≤
      (3 / (c * lam)) * M * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2) := by
  have hw_cont_val : ContinuousOn w (Ioi 0) := fun τ hτ => (hw τ hτ).continuousAt.continuousWithinAt
  have hφ'_cont : ContinuousOn φ' (w '' Ioi 0) := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact (hφ' (w τ) ⟨τ, hτ, rfl⟩).continuousAt.continuousWithinAt
  have hu_pos : 0 < u := lt_of_lt_of_le hs hsu
  have hsub_0 : Icc u v ⊆ Ioi 0 := fun τ hτ => lt_of_lt_of_le hu_pos hτ.1
  have hsub_s : Icc u v ⊆ Icc s (2 * s) := Icc_subset_Icc hsu hv2s
  have hsub_w : Icc (w u) (w v) ⊆ w '' Ioi 0 := by
    intro y hy
    obtain ⟨τ, hτ, rfl⟩ := intermediate_value_Icc huv (hw_cont_val.mono hsub_0) hy
    exact ⟨τ, hsub_0 hτ, rfl⟩
  obtain ⟨hbv_s, hbound_s⟩ := hh_bv s hs
  have hbv_uv : BoundedVariationOn h (Icc u v) := hbv_s.mono hsub_s
  have htv_uv : (eVariationOn h (Icc u v)).toReal ≤ (eVariationOn h (Icc s (2 * s))).toReal :=
    ENNReal.toReal_mono hbv_s (eVariationOn.mono h hsub_s)
  have h_vdc := van_der_corput_first_comp
    (M := M * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2) -
      (eVariationOn h (Icc s (2 * s))).toReal)
    huv hc_pos hlam
    (fun τ hτ => hw τ (hsub_0 hτ)) (hw_cont.mono hsub_0) (fun τ hτ => (hw_pos τ (hsub_0 hτ)).le)
    (fun y hy => hφ y (hsub_w hy)) (hφ'_cont.mono hsub_w)
    (Or.elim hφ'_mono (fun hm => Or.inl (hm.mono hsub_w)) (fun ha => Or.inr (ha.mono hsub_w)))
    hlb (hh_cont.mono hsub_0) hbv_uv
    (fun τ hτ => by
      have h1 := hbound_s τ (hsub_s hτ)
      linarith)
  calc ‖∫ τ in u..v, h τ * (w' τ : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ (w τ) : ℂ))‖
      ≤ 3 * ((M * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2) -
          (eVariationOn h (Icc s (2 * s))).toReal) + (eVariationOn h (Icc u v)).toReal) / (c * lam) :=
        h_vdc
    _ ≤ 3 * (M * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2)) / (c * lam) := by
        gcongr; linarith
    _ = (3 / (c * lam)) * M * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2) := by ring

/-- Lemma TE.1a on compact subintervals `[a, b] ⊆ (0, ∞)` (uniform in `a, b`, no global `Ioi 0`
integrability needed). -/
theorem teb_edge_osc_interval {w w' φ φ' φ'' : ℝ → ℝ} {h : ℝ → ℂ}
    {τ₀ A b₀ N M c a b : ℝ}
    (hτ₀ : 0 ≤ τ₀) (hA : 0 < A) (hb₀ : 0 < b₀) (hc : 1 ≤ c) (ha : 0 < a) (hab : a ≤ b)
    (hw : ∀ τ, 0 < τ → HasDerivAt w (w' τ) τ)
    (hw_cont : ContinuousOn w' (Ioi 0))
    (hw_pos : ∀ τ, 0 < τ → 0 < w' τ)
    (hφ : ∀ y ∈ w '' Ioi 0, HasDerivAt φ (φ' y) y)
    (hφ' : ∀ y ∈ w '' Ioi 0, HasDerivAt φ' (φ'' y) y)
    (hφ'_mono : MonotoneOn φ' (w '' Ioi 0) ∨ AntitoneOn φ' (w '' Ioi 0))
    (h_upper : ∀ τ, 2 * τ₀ < τ → b₀ * min (τ ^ 2) 1 ≤ |φ' (w τ)|)
    (h_lower : ∀ τ, 0 < τ → τ < τ₀ / 2 → b₀ * min (τ₀ ^ 2) 1 ≤ |φ' (w τ)|)
    (h_mid : 0 < τ₀ → ∀ τ, τ₀ / 2 ≤ τ → τ ≤ 2 * τ₀ →
      b₀ * τ₀ / (1 + τ₀ ^ 3) ≤ |φ'' (w τ)|)
    (hh_cont : ContinuousOn h (Ioi 0))
    (hh_vanish : ∀ τ, 0 < τ → τ ≤ 2 * A * c ^ (-(1 / 3 : ℝ)) → h τ = 0)
    (hh_bv : ∀ s > 0, BoundedVariationOn h (Icc s (2 * s)) ∧
      ∀ τ ∈ Icc s (2 * s), ‖h τ‖ + (eVariationOn h (Icc s (2 * s))).toReal ≤
        M * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2)) :
    ‖∫ τ in a..b, h τ * (w' τ : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ (w τ) : ℂ))‖ ≤
      tebOscConst b₀ N * M *
        (c⁻¹ + c ^ (-(1 / 2 : ℝ)) * min (τ₀ ^ 2) 1 * if A * c ^ (-(1 / 3 : ℝ)) < τ₀ then 1 else 0) := by
  have hc_pos : 0 < c := by linarith
  have hM_nn : 0 ≤ M := nonneg_of_hh_bv_unit hh_bv
  have hφ'_cont : ContinuousOn φ' (w '' Ioi 0) := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact (hφ' (w τ) ⟨τ, hτ, rfl⟩).continuousAt.continuousWithinAt
  have hw_cont_val : ContinuousOn w (Ioi 0) := fun τ hτ => (hw τ hτ).continuousAt.continuousWithinAt
  let F_osc : ℝ → ℂ := fun τ =>
    h τ * (w' τ : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ (w τ) : ℂ))
  have hF_int : ∀ u v, 0 < u → u ≤ v → IntervalIntegrable F_osc volume u v := fun u v hu huv =>
    teb_osc_intervalIntegrable c hw hw_cont hφ hh_cont hu (lt_of_lt_of_le hu huv)
  set eps := 2 * A * c ^ (-(1 / 3 : ℝ))
  have heps_pos : 0 < eps := by positivity
  -- Helper to bound `F_osc` on a first-derivative subinterval `[u, v] ⊆ [s, 2s]`
  have vdc1_block : ∀ {u v s lam : ℝ}, 0 < s → s ≤ u → u ≤ v → v ≤ 2 * s → 0 < lam →
      (∀ τ ∈ Icc u v, lam ≤ |φ' (w τ)|) →
      ‖∫ τ in u..v, F_osc τ‖ ≤
        (3 / (c * lam)) * M * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2) :=
    fun hs hsu huv hv2s hlam hlb =>
      teb_osc_vdc1_block hc_pos hw hw_cont hw_pos hφ hφ' hφ'_mono hh_cont hh_bv hs hsu huv hv2s hlam hlb
  -- Truncate `[a, b]` to `[max a eps, b]` if `eps < b`, else `0`
  rcases le_or_gt b eps with hb_le | h_eps_lt
  · have hzero : ∫ τ in a..b, F_osc τ = 0 := by
      have : EqOn F_osc (fun _ => 0) (Icc a b) := fun τ hτ => by
        dsimp [F_osc]; rw [hh_vanish τ (lt_of_lt_of_le ha hτ.1) (hτ.2.trans hb_le), zero_mul, zero_mul]
      rw [intervalIntegral.integral_congr (by rw [uIcc_of_le hab]; exact this), intervalIntegral.integral_zero]
    rw [hzero, norm_zero]
    have hC := (tebOscConst_pos hb₀ N).le
    positivity
  · set a₁ := max a eps
    have ha₁_pos : 0 < a₁ := lt_of_lt_of_le ha (le_max_left _ _)
    have ha₁_le_b : a₁ ≤ b := max_le hab h_eps_lt.le
    have ha₁_ge_eps : eps ≤ a₁ := le_max_right _ _
    have h_trunc : ∫ τ in a..b, F_osc τ = ∫ τ in a₁..b, F_osc τ := by
      rcases le_or_gt eps a with ha_ge | ha_lt
      · have : a₁ = a := max_eq_left ha_ge
        rw [this]
      · have : a₁ = eps := max_eq_right ha_lt.le
        rw [this, ← intervalIntegral.integral_add_adjacent_intervals (hF_int a eps ha ha_lt.le)
          (hF_int eps b heps_pos h_eps_lt.le)]
        have h_van : ∫ τ in a..eps, F_osc τ = 0 := by
          have : EqOn F_osc (fun _ => 0) (Icc a eps) := fun τ hτ => by
            dsimp [F_osc]; rw [hh_vanish τ (lt_of_lt_of_le ha hτ.1) hτ.2, zero_mul, zero_mul]
          rw [intervalIntegral.integral_congr (by rw [uIcc_of_le ha_lt.le]; exact this),
            intervalIntegral.integral_zero]
        rw [h_van, zero_add]
    rw [h_trunc]
    have h_upper_ge : ∀ τ, 0 < τ → 2 * τ₀ ≤ τ → b₀ * min (τ ^ 2) 1 ≤ |φ' (w τ)| := by
      intro τ hτ_pos hτ_ge
      rcases eq_or_lt_of_le hτ_ge with heq | hlt
      · have hcont_g : ContinuousAt (fun t => |φ' (w t)|) τ :=
          (hφ'_cont.comp hw_cont_val (fun x hx => ⟨x, hx, rfl⟩) τ hτ_pos).abs.continuousAt
            (isOpen_Ioi.mem_nhds hτ_pos)
        have hcont_l : ContinuousAt (fun t => b₀ * min (t ^ 2) 1) τ := by fun_prop
        have h_ev : ∀ᶠ t in 𝓝[>] τ, b₀ * min (t ^ 2) 1 ≤ |φ' (w t)| := by
          filter_upwards [self_mem_nhdsWithin] with t ht
          exact h_upper t (by linarith [mem_Ioi.mp ht])
        exact le_of_tendsto_of_tendsto (hcont_l.tendsto.mono_left nhdsWithin_le_nhds)
          (hcont_g.tendsto.mono_left nhdsWithin_le_nhds) h_ev
      · exact h_upper τ hlt
    have h_lower_le : 0 < τ₀ → ∀ τ, 0 < τ → τ ≤ τ₀ / 2 → b₀ * min (τ₀ ^ 2) 1 ≤ |φ' (w τ)| := by
      intro hτ₀_pos τ hτ_pos hτ_le
      rcases eq_or_lt_of_le hτ_le with heq | hlt
      · have hcont_g : ContinuousAt (fun t => |φ' (w t)|) τ :=
          (hφ'_cont.comp hw_cont_val (fun x hx => ⟨x, hx, rfl⟩) τ hτ_pos).abs.continuousAt
            (isOpen_Ioi.mem_nhds hτ_pos)
        have h_ev : ∀ᶠ t in 𝓝[<] τ, b₀ * min (τ₀ ^ 2) 1 ≤ |φ' (w t)| := by
          have hmem : Ioi (0 : ℝ) ∈ 𝓝[<] τ := nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hτ_pos)
          filter_upwards [self_mem_nhdsWithin, hmem] with t ht ht0
          exact h_lower t ht0 (by linarith [mem_Iio.mp ht])
        exact ge_of_tendsto (hcont_g.tendsto.mono_left nhdsWithin_le_nhds) h_ev
      · exact h_lower τ hτ_pos hlt
    set C_poly : ℝ := (2 : ℝ) ^ max N 0 * (4 + (Nat.factorial (Nat.ceil ((5 / 2 + max N 0 + 1) / 2)) : ℝ))
    have hC_poly_nn : 0 ≤ C_poly := by positivity
    -- Upper region helper on `[u, v] ⊆ [2 * τ₀, ∞)`
    have upper_region_bound : ∀ {u v : ℝ}, 0 < u → u ≤ v → 2 * τ₀ ≤ u →
        ‖∫ τ in u..v, F_osc τ‖ ≤ (3 * b₀⁻¹ * C_poly) * M * c⁻¹ := by
      intro u v hu huv h2τ₀
      have h_dyadic := dyadic_upper_sum_le N hu huv F_osc (g := fun _ => 3 * M / (c * b₀))
        (fun s hs u' v' hau' hv'b hsu' hu'v' hv'2s => by
          have hlb : ∀ τ ∈ Icc u' v', b₀ * min (s ^ 2) 1 ≤ |φ' (w τ)| := fun τ hτ => by
            have hτ_pos : 0 < τ := lt_of_lt_of_le (lt_of_lt_of_le hs hsu') hτ.1
            have hτ_ge_2τ₀ : 2 * τ₀ ≤ τ := h2τ₀.trans (hau'.trans hτ.1)
            have hs_le_τ : s ≤ τ := hsu'.trans hτ.1
            have hsq_le : s ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ hs.le hs_le_τ 2
            have hmin_le : min (s ^ 2) 1 ≤ min (τ ^ 2) 1 := min_le_min_right 1 hsq_le
            calc b₀ * min (s ^ 2) 1 ≤ b₀ * min (τ ^ 2) 1 := by gcongr
              _ ≤ |φ' (w τ)| := h_upper_ge τ hτ_pos hτ_ge_2τ₀
          have h1 := vdc1_block hs hsu' hu'v' hv'2s (by positivity) hlb
          refine h1.trans_eq ?_
          ring)
        (by positivity) (fun _ _ => le_rfl) (hF_int u v hu huv)
      refine h_dyadic.trans_eq ?_
      dsimp [C_poly]; ring
    -- Main split on whether `τ₀ ≤ A * c ^ (-(1 / 3 : ℝ))`
    rcases le_or_gt τ₀ (A * c ^ (-(1 / 3 : ℝ))) with hτ₀_small | hτ₀_big
    · simp only [not_lt.mpr hτ₀_small, ↓reduceIte, mul_zero, add_zero]
      have h2τ₀ : 2 * τ₀ ≤ a₁ := by linarith
      have hub := upper_region_bound ha₁_pos ha₁_le_b h2τ₀
      have hC_le : 3 * b₀⁻¹ * C_poly ≤ tebOscConst b₀ N := by
        unfold tebOscConst
        dsimp only
        have h3_nn : 0 ≤ 3 * b₀⁻¹ * C_poly := by positivity
        have h2_nn : 0 ≤ 3 * b₀⁻¹ * (2 : ℝ) ^ max N 0 := by positivity
        calc 3 * b₀⁻¹ * C_poly
            ≤ 3 * b₀⁻¹ * C_poly + (3 * b₀⁻¹ * C_poly + 3 * b₀⁻¹ * (2 : ℝ) ^ max N 0) :=
              le_add_of_nonneg_right (add_nonneg h3_nn h2_nn)
          _ = 6 * b₀⁻¹ * C_poly + 3 * b₀⁻¹ * (2 : ℝ) ^ max N 0 := by ring
          _ ≤ max (6 * b₀⁻¹ * C_poly + 3 * b₀⁻¹ * (2 : ℝ) ^ max N 0) _ := le_max_left _ _
      calc ‖∫ τ in a₁..b, F_osc τ‖
          ≤ (3 * b₀⁻¹ * C_poly) * M * c⁻¹ := hub
        _ ≤ tebOscConst b₀ N * M * c⁻¹ := by gcongr
    · simp only [hτ₀_big, ↓reduceIte, mul_one]
      have hτ₀_pos : 0 < τ₀ := lt_of_le_of_lt (by positivity) hτ₀_big
      let x₁ := min b (max a₁ (τ₀ / 2))
      let x₂ := min b (max a₁ (2 * τ₀))
      have ha₁_le_x1 : a₁ ≤ x₁ := le_min ha₁_le_b (le_max_left _ _)
      have hx1_le_x2 : x₁ ≤ x₂ := min_le_min_left b (max_le_max_left a₁ (by linarith))
      have hx2_le_b : x₂ ≤ b := min_le_left _ _
      have hx1_pos : 0 < x₁ := lt_of_lt_of_le ha₁_pos ha₁_le_x1
      have hx2_pos : 0 < x₂ := lt_of_lt_of_le hx1_pos hx1_le_x2
      have h_split3 : ∫ τ in a₁..b, F_osc τ =
          (∫ τ in a₁..x₁, F_osc τ) + (∫ τ in x₁..x₂, F_osc τ) + (∫ τ in x₂..b, F_osc τ) := by
        have h12 := intervalIntegral.integral_add_adjacent_intervals
          (hF_int a₁ x₁ ha₁_pos ha₁_le_x1) (hF_int x₁ x₂ hx1_pos hx1_le_x2)
        have h23 := intervalIntegral.integral_add_adjacent_intervals
          (hF_int a₁ x₂ ha₁_pos (ha₁_le_x1.trans hx1_le_x2)) (hF_int x₂ b hx2_pos hx2_le_b)
        rw [← h23, ← h12]
      -- 1. Lower region `[a₁, x₁]`
      have h_low_bound : ‖∫ τ in a₁..x₁, F_osc τ‖ ≤
          (3 * b₀⁻¹ * C_poly + 3 * b₀⁻¹ * (2 : ℝ) ^ max N 0) * M * c⁻¹ := by
        rcases eq_or_lt_of_le ha₁_le_x1 with heq | hlt
        · rw [heq, intervalIntegral.integral_same, norm_zero]
          positivity
        · have hx1_le_half : x₁ ≤ τ₀ / 2 := by
            have hlt_max : a₁ < max a₁ (τ₀ / 2) := lt_of_lt_of_le hlt (min_le_right _ _)
            have ha_lt_half : a₁ < τ₀ / 2 := by
              rcases lt_max_iff.mp hlt_max with h | h
              · exact absurd h (lt_irrefl a₁)
              · exact h
            exact (min_le_right _ _).trans (max_le ha_lt_half.le le_rfl)
          rcases le_or_gt τ₀ 1 with hτ₀_le1 | hτ₀_gt1
          · have h_dy := dyadic_lower_small_sum_le N hτ₀_pos hτ₀_le1 ha₁_pos ha₁_le_x1 hx1_le_half F_osc
              (g := fun _ => 3 * M / (c * b₀))
              (fun s hs u' v' hau' hv'b hsu' hu'v' hv'2s => by
                have hlb : ∀ τ ∈ Icc u' v', b₀ * τ₀ ^ 2 ≤ |φ' (w τ)| := fun τ hτ => by
                  have hτ_pos : 0 < τ := lt_of_lt_of_le (lt_of_lt_of_le hs hsu') hτ.1
                  have hτ_le : τ ≤ τ₀ / 2 := hτ.2.trans (hv'b.trans hx1_le_half)
                  have hmin : min (τ₀ ^ 2) 1 = τ₀ ^ 2 := min_eq_left (by nlinarith)
                  simpa [hmin] using h_lower_le hτ₀_pos τ hτ_pos hτ_le
                have h1 := vdc1_block hs hsu' hu'v' hv'2s (by positivity) hlb
                refine h1.trans_eq ?_
                ring)
              (by positivity) (fun _ _ => le_rfl) (hF_int a₁ x₁ ha₁_pos ha₁_le_x1)
            calc ‖∫ τ in a₁..x₁, F_osc τ‖
                ≤ 3 * M / (c * b₀) * (2 : ℝ) ^ max N 0 := h_dy
              _ = (3 * b₀⁻¹ * (2 : ℝ) ^ max N 0) * M * c⁻¹ := by ring
              _ ≤ (3 * b₀⁻¹ * C_poly + 3 * b₀⁻¹ * (2 : ℝ) ^ max N 0) * M * c⁻¹ := by
                  have : 0 ≤ 3 * b₀⁻¹ * C_poly * M * c⁻¹ := by positivity
                  linarith
          · have h_dy := dyadic_upper_sum_le N ha₁_pos ha₁_le_x1 F_osc
              (g := fun _ => 3 * M / (c * b₀))
              (fun s hs u' v' hau' hv'b hsu' hu'v' hv'2s => by
                have hlb : ∀ τ ∈ Icc u' v', b₀ * min (s ^ 2) 1 ≤ |φ' (w τ)| := fun τ hτ => by
                  have hτ_pos : 0 < τ := lt_of_lt_of_le (lt_of_lt_of_le hs hsu') hτ.1
                  have hτ_le : τ ≤ τ₀ / 2 := hτ.2.trans (hv'b.trans hx1_le_half)
                  have hmin1 : min (τ₀ ^ 2) 1 = 1 := min_eq_right (by nlinarith)
                  have hlow := h_lower_le hτ₀_pos τ hτ_pos hτ_le
                  rw [hmin1, mul_one] at hlow
                  calc b₀ * min (s ^ 2) 1
                      ≤ b₀ * 1 := mul_le_mul_of_nonneg_left (min_le_right _ _) hb₀.le
                    _ = b₀ := mul_one _
                    _ ≤ |φ' (w τ)| := hlow
                have h1 := vdc1_block hs hsu' hu'v' hv'2s (by positivity) hlb
                refine h1.trans_eq ?_
                ring)
              (by positivity) (fun _ _ => le_rfl) (hF_int a₁ x₁ ha₁_pos ha₁_le_x1)
            calc ‖∫ τ in a₁..x₁, F_osc τ‖
                ≤ 3 * M / (c * b₀) * C_poly := by refine h_dy.trans_eq ?_; dsimp [C_poly]; ring
              _ = (3 * b₀⁻¹ * C_poly) * M * c⁻¹ := by ring
              _ ≤ (3 * b₀⁻¹ * C_poly + 3 * b₀⁻¹ * (2 : ℝ) ^ max N 0) * M * c⁻¹ := by
                  have : 0 ≤ 3 * b₀⁻¹ * (2 : ℝ) ^ max N 0 * M * c⁻¹ := by positivity
                  linarith
      -- 2. Middle region `[x₁, x₂]`
      set m_idx := Nat.ceil ((7 / 2 + max N 0) / 2)
      set C_mid : ℝ := 16 * (√b₀)⁻¹ * √2 * (2 : ℝ) ^ max N 0 *
        max 1 ((Nat.factorial m_idx : ℝ) * 4 ^ m_idx)
      have h_mid_bound : ‖∫ τ in x₁..x₂, F_osc τ‖ ≤
          C_mid * M * c ^ (-(1 / 2 : ℝ)) * min (τ₀ ^ 2) 1 := by
        rcases eq_or_lt_of_le hx1_le_x2 with heq | hlt
        · rw [heq, intervalIntegral.integral_same, norm_zero]
          positivity
        · have hx1_ge_half : τ₀ / 2 ≤ x₁ := by
            have hlt_b : max a₁ (τ₀ / 2) < b := by
              by_contra hle
              have hx1_b : x₁ = b := min_eq_left (not_lt.mp hle)
              linarith [hx2_le_b]
            have hx1_eq : x₁ = max a₁ (τ₀ / 2) := min_eq_right hlt_b.le
            rw [hx1_eq]
            exact le_max_right _ _
          have hx2_le_2 : x₂ ≤ 2 * τ₀ := by
            have ha1_lt_2 : a₁ < 2 * τ₀ := by
              have ha1_lt_x2 : a₁ < x₂ := ha₁_le_x1.trans_lt hlt
              by_contra hge
              have hle : 2 * τ₀ ≤ a₁ := not_lt.mp hge
              have h1 : x₁ = a₁ := by dsimp [x₁]; rw [max_eq_left (by linarith), min_eq_right ha₁_le_b]
              have h2 : x₂ = a₁ := by dsimp [x₂]; rw [max_eq_left hle, min_eq_right ha₁_le_b]
              linarith
            exact (min_le_right _ _).trans (max_le ha1_lt_2.le le_rfl)
          let m := min x₂ (max x₁ τ₀)
          have hx1_le_m : x₁ ≤ m := le_min hx1_le_x2 (le_max_left _ _)
          have hm_le_x2 : m ≤ x₂ := min_le_left _ _
          have hm_pos : 0 < m := lt_of_lt_of_le hx1_pos hx1_le_m
          have h_split_mid : ∫ τ in x₁..x₂, F_osc τ =
              (∫ τ in x₁..m, F_osc τ) + (∫ τ in m..x₂, F_osc τ) :=
            (intervalIntegral.integral_add_adjacent_intervals
              (hF_int x₁ m hx1_pos hx1_le_m) (hF_int m x₂ hm_pos hm_le_x2)).symm
          have vdc2_sub : ∀ {u v s : ℝ}, 0 < s → s ≤ u → u ≤ v → v ≤ 2 * s →
              τ₀ / 2 ≤ u → v ≤ 2 * τ₀ →
              ‖∫ τ in u..v, F_osc τ‖ ≤
                8 * (M * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2)) /
                  √(c * (b₀ * τ₀ / (1 + τ₀ ^ 3))) := by
            intro u v s hs hsu huv hv2s hu_half hv_2
            have hu_pos : 0 < u := lt_of_lt_of_le hs hsu
            have hsub_0 : Icc u v ⊆ Ioi 0 := fun τ hτ => lt_of_lt_of_le hu_pos hτ.1
            have hsub_s : Icc u v ⊆ Icc s (2 * s) := Icc_subset_Icc hsu hv2s
            have hsub_w : Icc (w u) (w v) ⊆ w '' Ioi 0 := by
              intro y hy
              obtain ⟨τ, hτ, rfl⟩ := intermediate_value_Icc huv (hw_cont_val.mono hsub_0) hy
              exact ⟨τ, hsub_0 hτ, rfl⟩
            have hlam_pos : 0 < b₀ * τ₀ / (1 + τ₀ ^ 3) := by positivity
            have h_lb2 : ∀ y ∈ Icc (w u) (w v), b₀ * τ₀ / (1 + τ₀ ^ 3) ≤ |φ'' y| := by
              intro y hy
              obtain ⟨τ, hτ, rfl⟩ := intermediate_value_Icc huv (hw_cont_val.mono hsub_0) hy
              exact h_mid hτ₀_pos τ (hu_half.trans hτ.1) (hτ.2.trans hv_2)
            obtain ⟨hbv_s, hbound_s⟩ := hh_bv s hs
            have hbv_uv : BoundedVariationOn h (Icc u v) := hbv_s.mono hsub_s
            have htv_uv : (eVariationOn h (Icc u v)).toReal ≤ (eVariationOn h (Icc s (2 * s))).toReal :=
              ENNReal.toReal_mono hbv_s (eVariationOn.mono h hsub_s)
            have h_vdc2 := van_der_corput_second_comp
              (M := M * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2) -
                (eVariationOn h (Icc s (2 * s))).toReal)
              huv hc_pos hlam_pos
              (fun τ hτ => hw τ (hsub_0 hτ)) (hw_cont.mono hsub_0) (fun τ hτ => (hw_pos τ (hsub_0 hτ)).le)
              (fun y hy => hφ y (hsub_w hy)) (fun y hy => hφ' y (hsub_w hy))
              (Or.elim hφ'_mono (fun hm => Or.inl (hm.mono hsub_w)) (fun ha => Or.inr (ha.mono hsub_w)))
              h_lb2 (hh_cont.mono hsub_0) hbv_uv
              (fun τ hτ => by have h1 := hbound_s τ (hsub_s hτ); linarith)
            calc ‖∫ τ in u..v, F_osc τ‖
                ≤ 8 * ((M * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2) -
                    (eVariationOn h (Icc s (2 * s))).toReal) + (eVariationOn h (Icc u v)).toReal) /
                    √(c * (b₀ * τ₀ / (1 + τ₀ ^ 3))) := h_vdc2
              _ ≤ 8 * (M * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2)) /
                    √(c * (b₀ * τ₀ / (1 + τ₀ ^ 3))) := by gcongr; linarith
          have h_left_half : ‖∫ τ in x₁..m, F_osc τ‖ ≤
              8 * (M * (τ₀ ^ (5 / 2 : ℝ) * (1 + τ₀) ^ max N 0 * Real.exp (-τ₀ ^ 2 / 4))) /
                √(c * (b₀ * τ₀ / (1 + τ₀ ^ 3))) := by
            rcases eq_or_lt_of_le hx1_le_m with heq | hlt'
            · rw [heq, intervalIntegral.integral_same, norm_zero]
              positivity
            · have hm_le_tau0 : m ≤ τ₀ := by
                dsimp [m] at hlt' ⊢
                rcases le_or_gt x₁ τ₀ with hx1_le | hx1_gt
                · exact (min_le_right _ _).trans (max_eq_right hx1_le).le
                · rw [max_eq_left hx1_gt.le, min_eq_right hx1_le_x2] at hlt'; linarith
              have h_vdc := vdc2_sub (s := τ₀ / 2) (by positivity) hx1_ge_half hx1_le_m
                (by linarith) hx1_ge_half (hm_le_tau0.trans (by linarith))
              have henv := teb_middle_envelope N (s := τ₀ / 2) ⟨le_rfl, by linarith⟩ hτ₀_pos
              calc ‖∫ τ in x₁..m, F_osc τ‖
                  ≤ 8 * (M * (τ₀ / 2) ^ (5 / 2 : ℝ) * (1 + τ₀ / 2) ^ N * Real.exp (-(τ₀ / 2) ^ 2)) /
                      √(c * (b₀ * τ₀ / (1 + τ₀ ^ 3))) := h_vdc
                _ = 8 * (M * ((τ₀ / 2) ^ (5 / 2 : ℝ) * (1 + τ₀ / 2) ^ N * Real.exp (-(τ₀ / 2) ^ 2))) /
                      √(c * (b₀ * τ₀ / (1 + τ₀ ^ 3))) := by ring
                _ ≤ 8 * (M * (τ₀ ^ (5 / 2 : ℝ) * (1 + τ₀) ^ max N 0 * Real.exp (-τ₀ ^ 2 / 4))) /
                      √(c * (b₀ * τ₀ / (1 + τ₀ ^ 3))) := by gcongr
          have h_right_half : ‖∫ τ in m..x₂, F_osc τ‖ ≤
              8 * (M * (τ₀ ^ (5 / 2 : ℝ) * (1 + τ₀) ^ max N 0 * Real.exp (-τ₀ ^ 2 / 4))) /
                √(c * (b₀ * τ₀ / (1 + τ₀ ^ 3))) := by
            rcases eq_or_lt_of_le hm_le_x2 with heq | hlt'
            · rw [heq, intervalIntegral.integral_same, norm_zero]
              positivity
            · have hm_ge_tau0 : τ₀ ≤ m := by
                have hmax_lt : max x₁ τ₀ < x₂ := by
                  by_contra hle
                  have hm_eq : m = x₂ := min_eq_left (not_lt.mp hle)
                  linarith
                have hm_eq : m = max x₁ τ₀ := min_eq_right hmax_lt.le
                rw [hm_eq]
                exact le_max_right _ _
              have h_vdc := vdc2_sub (s := τ₀) hτ₀_pos hm_ge_tau0 hm_le_x2 hx2_le_2
                (by linarith) hx2_le_2
              have henv := teb_middle_envelope N (s := τ₀) ⟨by linarith, le_rfl⟩ hτ₀_pos
              calc ‖∫ τ in m..x₂, F_osc τ‖
                  ≤ 8 * (M * τ₀ ^ (5 / 2 : ℝ) * (1 + τ₀) ^ N * Real.exp (-τ₀ ^ 2)) /
                      √(c * (b₀ * τ₀ / (1 + τ₀ ^ 3))) := h_vdc
                _ = 8 * (M * (τ₀ ^ (5 / 2 : ℝ) * (1 + τ₀) ^ N * Real.exp (-τ₀ ^ 2))) /
                      √(c * (b₀ * τ₀ / (1 + τ₀ ^ 3))) := by ring
                _ ≤ 8 * (M * (τ₀ ^ (5 / 2 : ℝ) * (1 + τ₀) ^ max N 0 * Real.exp (-τ₀ ^ 2 / 4))) /
                      √(c * (b₀ * τ₀ / (1 + τ₀ ^ 3))) := by gcongr
          have h_core_le := teb_middle_core_le N hτ₀_pos
          have h_alg_mid := teb_middle_alg (N := N) (M := M) hb₀ hc_pos hτ₀_pos
          calc ‖∫ τ in x₁..x₂, F_osc τ‖
              ≤ ‖∫ τ in x₁..m, F_osc τ‖ + ‖∫ τ in m..x₂, F_osc τ‖ := by
                rw [h_split_mid]; exact norm_add_le _ _
            _ ≤ 16 * (M * (τ₀ ^ (5 / 2 : ℝ) * (1 + τ₀) ^ max N 0 * Real.exp (-τ₀ ^ 2 / 4))) /
                  √(c * (b₀ * τ₀ / (1 + τ₀ ^ 3))) :=
                (add_le_add h_left_half h_right_half).trans_eq (by ring)
            _ = 16 * (√b₀)⁻¹ * M * c ^ (-(1 / 2 : ℝ)) *
                  (τ₀ ^ 2 * √(1 + τ₀ ^ 3) * (1 + τ₀) ^ max N 0 * Real.exp (-τ₀ ^ 2 / 4)) := h_alg_mid
            _ ≤ 16 * (√b₀)⁻¹ * M * c ^ (-(1 / 2 : ℝ)) *
                  (√2 * (2 : ℝ) ^ max N 0 * max 1 ((Nat.factorial m_idx : ℝ) * 4 ^ m_idx) * min (τ₀ ^ 2) 1) := by
                gcongr
            _ = C_mid * M * c ^ (-(1 / 2 : ℝ)) * min (τ₀ ^ 2) 1 := by
                dsimp [C_mid]; ring
      -- 3. Upper region `[x₂, b]`
      have h_up_bound : ‖∫ τ in x₂..b, F_osc τ‖ ≤ (3 * b₀⁻¹ * C_poly) * M * c⁻¹ := by
        rcases eq_or_lt_of_le hx2_le_b with heq | hlt
        · rw [heq, intervalIntegral.integral_same, norm_zero]
          positivity
        · have hx2_ge : 2 * τ₀ ≤ x₂ := by
            have hmax_lt : max a₁ (2 * τ₀) < b := by
              by_contra hle
              have hx2_eq : x₂ = b := min_eq_left (not_lt.mp hle)
              linarith
            have hx2_eq : x₂ = max a₁ (2 * τ₀) := min_eq_right hmax_lt.le
            rw [hx2_eq]
            exact le_max_right _ _
          exact upper_region_bound hx2_pos hx2_le_b hx2_ge
      have h_teb_lo : 6 * b₀⁻¹ * C_poly + 3 * b₀⁻¹ * (2 : ℝ) ^ max N 0 ≤ tebOscConst b₀ N := by
        unfold tebOscConst; exact le_max_left _ _
      have h_teb_mid : C_mid ≤ tebOscConst b₀ N := by
        unfold tebOscConst; exact le_max_right _ _
      calc ‖∫ τ in a₁..b, F_osc τ‖
          ≤ ‖∫ τ in a₁..x₁, F_osc τ‖ + ‖∫ τ in x₁..x₂, F_osc τ‖ + ‖∫ τ in x₂..b, F_osc τ‖ := by
            rw [h_split3]
            exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ (3 * b₀⁻¹ * C_poly + 3 * b₀⁻¹ * (2 : ℝ) ^ max N 0) * M * c⁻¹ +
              C_mid * M * c ^ (-(1 / 2 : ℝ)) * min (τ₀ ^ 2) 1 +
              (3 * b₀⁻¹ * C_poly) * M * c⁻¹ :=
            add_le_add (add_le_add h_low_bound h_mid_bound) h_up_bound
        _ = (6 * b₀⁻¹ * C_poly + 3 * b₀⁻¹ * (2 : ℝ) ^ max N 0) * M * c⁻¹ +
              C_mid * M * c ^ (-(1 / 2 : ℝ)) * min (τ₀ ^ 2) 1 := by ring
        _ ≤ tebOscConst b₀ N * M * c⁻¹ +
              tebOscConst b₀ N * M * (c ^ (-(1 / 2 : ℝ)) * min (τ₀ ^ 2) 1) := by
            refine add_le_add ?_ ?_
            · gcongr
            · rw [← mul_assoc (tebOscConst b₀ N * M)]
              gcongr
        _ = tebOscConst b₀ N * M * (c⁻¹ + c ^ (-(1 / 2 : ℝ)) * min (τ₀ ^ 2) 1) := by ring

/-- **Lemma TE.1a (`teb:edge-osc`)**: Oscillatory edge estimate on `(0, ∞)`. -/
theorem teb_edge_osc {w w' φ φ' φ'' : ℝ → ℝ} {h : ℝ → ℂ}
    {τ₀ A b₀ N M c : ℝ}
    (hτ₀ : 0 ≤ τ₀) (hA : 0 < A) (hb₀ : 0 < b₀) (hc : 1 ≤ c)
    (hw : ∀ τ, 0 < τ → HasDerivAt w (w' τ) τ)
    (hw_cont : ContinuousOn w' (Ioi 0))
    (hw_pos : ∀ τ, 0 < τ → 0 < w' τ)
    (hφ : ∀ y ∈ w '' Ioi 0, HasDerivAt φ (φ' y) y)
    (hφ' : ∀ y ∈ w '' Ioi 0, HasDerivAt φ' (φ'' y) y)
    (hφ'_mono : MonotoneOn φ' (w '' Ioi 0) ∨ AntitoneOn φ' (w '' Ioi 0))
    (h_upper : ∀ τ, 2 * τ₀ < τ → b₀ * min (τ ^ 2) 1 ≤ |φ' (w τ)|)
    (h_lower : ∀ τ, 0 < τ → τ < τ₀ / 2 → b₀ * min (τ₀ ^ 2) 1 ≤ |φ' (w τ)|)
    (h_mid : 0 < τ₀ → ∀ τ, τ₀ / 2 ≤ τ → τ ≤ 2 * τ₀ →
      b₀ * τ₀ / (1 + τ₀ ^ 3) ≤ |φ'' (w τ)|)
    (hh_cont : ContinuousOn h (Ioi 0))
    (hh_vanish : ∀ τ, 0 < τ → τ ≤ 2 * A * c ^ (-(1 / 3 : ℝ)) → h τ = 0)
    (hh_bv : ∀ s > 0, BoundedVariationOn h (Icc s (2 * s)) ∧
      ∀ τ ∈ Icc s (2 * s), ‖h τ‖ + (eVariationOn h (Icc s (2 * s))).toReal ≤
        M * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2))
    (hint : IntegrableOn
      (fun τ => h τ * (w' τ : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ (w τ) : ℂ))) (Ioi 0)) :
    ‖∫ τ in Ioi (0 : ℝ), h τ * (w' τ : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ (w τ) : ℂ))‖ ≤
      tebOscConst b₀ N * M *
        (c⁻¹ + c ^ (-(1 / 2 : ℝ)) * min (τ₀ ^ 2) 1 * if A * c ^ (-(1 / 3 : ℝ)) < τ₀ then 1 else 0) := by
  have hc_pos : 0 < c := by linarith
  set a₀ := A * c ^ (-(1 / 3 : ℝ))
  have ha₀_pos : 0 < a₀ := by positivity
  let F_osc : ℝ → ℂ := fun τ =>
    h τ * (w' τ : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ (w τ) : ℂ))
  have h_eq_Ioi : ∫ τ in Ioi (0 : ℝ), F_osc τ = ∫ τ in Ioi a₀, F_osc τ := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    by_cases hτ_pos : 0 < τ
    · by_cases hτ_a0 : a₀ < τ
      · simp only [Set.indicator_apply, Set.mem_Ioi, hτ_pos, hτ_a0, ↓reduceIte]
      · have h_le : τ ≤ 2 * A * c ^ (-(1 / 3 : ℝ)) := by
          have : τ ≤ a₀ := not_lt.mp hτ_a0
          dsimp [a₀] at this
          linarith
        have hv : F_osc τ = 0 := by
          dsimp [F_osc]; rw [hh_vanish τ hτ_pos h_le, zero_mul, zero_mul]
        simp only [Set.indicator_apply, Set.mem_Ioi, hτ_pos, hτ_a0, ↓reduceIte, hv]
    · have hτ_not_a0 : ¬ a₀ < τ := fun h => hτ_pos (ha₀_pos.trans h)
      simp only [Set.indicator_apply, Set.mem_Ioi, hτ_pos, hτ_not_a0, ↓reduceIte]
  rw [h_eq_Ioi]
  have hint_a0 : IntegrableOn F_osc (Ioi a₀) := hint.mono_set (Ioi_subset_Ioi ha₀_pos.le)
  have htend : Tendsto (fun b => ∫ τ in a₀..b, F_osc τ) atTop (𝓝 (∫ τ in Ioi a₀, F_osc τ)) :=
    intervalIntegral_tendsto_integral_Ioi a₀ hint_a0 tendsto_id
  have h_ev : ∀ᶠ b in atTop, ‖∫ τ in a₀..b, F_osc τ‖ ≤ tebOscConst b₀ N * M *
      (c⁻¹ + c ^ (-(1 / 2 : ℝ)) * min (τ₀ ^ 2) 1 * if A * c ^ (-(1 / 3 : ℝ)) < τ₀ then 1 else 0) := by
    filter_upwards [eventually_ge_atTop a₀] with b hb
    exact teb_edge_osc_interval hτ₀ hA hb₀ hc ha₀_pos hb hw hw_cont hw_pos hφ hφ' hφ'_mono
      h_upper h_lower h_mid hh_cont hh_vanish hh_bv
  exact le_of_tendsto (htend.norm) h_ev

/-- **Lemma TE.1a (`teb:edge-osc`)**, improper Riemann–Stieltjes limit form (`8f29b5221`):
the truncated integrals converge as `a ↘ 0`, `b → ∞` without assuming `IntegrableOn` or any
growth bound on `w'`, and the limit satisfies the same oscillatory edge bound. -/
theorem teb_edge_osc_tendsto {w w' φ φ' φ'' : ℝ → ℝ} {h : ℝ → ℂ}
    {τ₀ A b₀ N M c : ℝ}
    (hτ₀ : 0 ≤ τ₀) (hA : 0 < A) (hb₀ : 0 < b₀) (hc : 1 ≤ c)
    (hw : ∀ τ, 0 < τ → HasDerivAt w (w' τ) τ)
    (hw_cont : ContinuousOn w' (Ioi 0))
    (hw_pos : ∀ τ, 0 < τ → 0 < w' τ)
    (hφ : ∀ y ∈ w '' Ioi 0, HasDerivAt φ (φ' y) y)
    (hφ' : ∀ y ∈ w '' Ioi 0, HasDerivAt φ' (φ'' y) y)
    (hφ'_mono : MonotoneOn φ' (w '' Ioi 0) ∨ AntitoneOn φ' (w '' Ioi 0))
    (h_upper : ∀ τ, 2 * τ₀ < τ → b₀ * min (τ ^ 2) 1 ≤ |φ' (w τ)|)
    (h_lower : ∀ τ, 0 < τ → τ < τ₀ / 2 → b₀ * min (τ₀ ^ 2) 1 ≤ |φ' (w τ)|)
    (h_mid : 0 < τ₀ → ∀ τ, τ₀ / 2 ≤ τ → τ ≤ 2 * τ₀ →
      b₀ * τ₀ / (1 + τ₀ ^ 3) ≤ |φ'' (w τ)|)
    (hh_cont : ContinuousOn h (Ioi 0))
    (hh_vanish : ∀ τ, 0 < τ → τ ≤ 2 * A * c ^ (-(1 / 3 : ℝ)) → h τ = 0)
    (hh_bv : ∀ s > 0, BoundedVariationOn h (Icc s (2 * s)) ∧
      ∀ τ ∈ Icc s (2 * s), ‖h τ‖ + (eVariationOn h (Icc s (2 * s))).toReal ≤
        M * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2)) :
    ∃ L : ℂ,
      Filter.Tendsto
        (fun p : ℝ × ℝ =>
          ∫ τ in p.1..p.2, h τ * (w' τ : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ (w τ) : ℂ)))
        (𝓝[>] (0 : ℝ) ×ˢ Filter.atTop) (𝓝 L) ∧
      ‖L‖ ≤ tebOscConst b₀ N * M *
        (c⁻¹ + c ^ (-(1 / 2 : ℝ)) * min (τ₀ ^ 2) 1 * (if A * c ^ (-(1 / 3 : ℝ)) < τ₀ then 1 else 0)) := by
  have hc_pos : 0 < c := by linarith
  have hM_nn : 0 ≤ M := nonneg_of_hh_bv_unit hh_bv
  let F_osc : ℝ → ℂ := fun τ =>
    h τ * (w' τ : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ (w τ) : ℂ))
  let F_int : ℝ × ℝ → ℂ := fun p => ∫ τ in p.1..p.2, F_osc τ
  have hF_int : ∀ x y, 0 < x → 0 < y → IntervalIntegrable F_osc volume x y :=
    fun _ _ hx hy => teb_osc_intervalIntegrable c hw hw_cont hφ hh_cont hx hy
  set eps := 2 * A * c ^ (-(1 / 3 : ℝ))
  have heps_pos : 0 < eps := by positivity
  set a_max := min (1 : ℝ) eps
  have ha_max_pos : 0 < a_max := lt_min one_pos heps_pos
  set R₀ := max (2 * τ₀ + 1) (max 2 (eps + 1))
  have hR₀_ge2 : 2 ≤ R₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hR₀_pos : 0 < R₀ := by linarith
  set C_poly1 : ℝ :=
    4 * (2 : ℝ) ^ max (N + 1) 0 + (2 : ℝ) ^ max (N + 1) 0 *
      (Nat.factorial (Nat.ceil ((5 / 2 + max (N + 1) 0 + 1) / 2)) : ℝ)
  set K_tail : ℝ := 6 * M / (c * b₀) * C_poly1
  have hK_nn : 0 ≤ K_tail := by positivity
  -- Upper tail bound: `O(1 / b₁)` on `[b₁, b₂]` for `R₀ ≤ b₁ ≤ b₂`
  have h_upper_tail : ∀ {b₁ b₂ : ℝ}, R₀ ≤ b₁ → b₁ ≤ b₂ →
      ‖∫ τ in b₁..b₂, F_osc τ‖ ≤ K_tail / b₁ := by
    intro b₁ b₂ hb₁ hb₁₂
    have hb₁_ge2 : 2 ≤ b₁ := hR₀_ge2.trans hb₁
    have hb₁_pos : 0 < b₁ := by linarith
    have h_dyadic := dyadic_upper_sum_le (N + 1) hb₁_pos hb₁₂ F_osc
      (g := fun _ => 6 * M / (c * b₀ * b₁))
      (fun s hs u v hbu hvb hsu huv hv2s => by
        have hs_ge_one : 1 ≤ s := by linarith
        have hs_min : min (s ^ 2) 1 = 1 := min_eq_right (by nlinarith)
        have h1s_pos : 0 < 1 + s := by linarith
        have h_extra : 1 ≤ (2 / b₁) * (1 + s) := by
          have hb1_le_2s : b₁ ≤ 2 * s := hbu.trans (huv.trans hv2s)
          rw [div_mul_eq_mul_div, one_le_div hb₁_pos]
          linarith
        have hlb : ∀ τ ∈ Icc u v, b₀ ≤ |φ' (w τ)| := fun τ hτ => by
          have h2τ₀ : 2 * τ₀ < τ := by linarith [le_max_left (2 * τ₀ + 1) (max 2 (eps + 1)), hbu.trans hτ.1]
          have hτ1 : 1 ≤ τ := by linarith [hbu.trans hτ.1]
          have hmin : min (τ ^ 2) 1 = 1 := min_eq_right (by nlinarith)
          simpa [hmin] using h_upper τ h2τ₀
        have hvdc := teb_osc_vdc1_block hc_pos hw hw_cont hw_pos hφ hφ' hφ'_mono hh_cont hh_bv
          hs hsu huv hv2s hb₀ hlb
        have hpow_succ : (1 + s) ^ N * (1 + s) = (1 + s) ^ (N + 1) := by
          rw [Real.rpow_add h1s_pos, Real.rpow_one]
        calc ‖∫ τ in u..v, F_osc τ‖
            ≤ (3 / (c * b₀)) * M * s ^ (5 / 2 : ℝ) * ((1 + s) ^ N * 1) * Real.exp (-s ^ 2) := by
                simpa only [mul_one] using hvdc
          _ ≤ (3 / (c * b₀)) * M * s ^ (5 / 2 : ℝ) * ((1 + s) ^ N * ((2 / b₁) * (1 + s))) *
                Real.exp (-s ^ 2) := by gcongr
          _ = (6 * M / (c * b₀ * b₁)) * s ^ (5 / 2 : ℝ) * ((1 + s) ^ N * (1 + s)) *
                Real.exp (-s ^ 2) := by ring
          _ = (6 * M / (c * b₀ * b₁)) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (N + 1) *
                Real.exp (-s ^ 2) / min (s ^ 2) 1 := by
              rw [hpow_succ, hs_min, div_one])
      (by positivity) (fun _ _ => le_rfl) (hF_int b₁ b₂ hb₁_pos (hb₁_pos.trans_le hb₁₂))
    refine h_dyadic.trans_eq ?_
    dsimp [K_tail, C_poly1]
    ring
  -- Lower tail vanishes on `(0, a_max]`
  have h_lower_vanish : ∀ {a₁ a₂ : ℝ}, 0 < a₁ → a₁ ≤ a_max → 0 < a₂ → a₂ ≤ a_max →
      ∫ τ in a₁..a₂, F_osc τ = 0 := by
    intro a₁ a₂ ha₁ ha₁m ha₂ ha₂m
    have hzero : EqOn F_osc (fun _ => 0) (uIcc a₁ a₂) := fun τ hτ => by
      have hτ_pos : 0 < τ := lt_of_lt_of_le (lt_min ha₁ ha₂) hτ.1
      have hτ_le : τ ≤ eps := hτ.2.trans ((max_le ha₁m ha₂m).trans (min_le_right _ _))
      dsimp [F_osc]
      rw [hh_vanish τ hτ_pos hτ_le, zero_mul, zero_mul]
    rw [intervalIntegral.integral_congr hzero, intervalIntegral.integral_zero]
  -- `F_int` is Cauchy along `𝓝[>] 0 ×ˢ Filter.atTop`
  have hCauchy : Cauchy (Filter.map F_int (𝓝[>] (0 : ℝ) ×ˢ Filter.atTop)) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    set B : ℝ := max R₀ (2 * K_tail / ε + 1)
    have hB_pos : 0 < B := lt_of_lt_of_le hR₀_pos (le_max_left _ _)
    have hS_mem : Ioo (0 : ℝ) a_max ×ˢ Ici B ∈ 𝓝[>] (0 : ℝ) ×ˢ Filter.atTop :=
      Filter.prod_mem_prod (Ioo_mem_nhdsGT ha_max_pos) (Ici_mem_atTop B)
    refine ⟨F_int '' (Ioo (0 : ℝ) a_max ×ˢ Ici B), Filter.image_mem_map hS_mem, ?_⟩
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    rcases hp with ⟨⟨hp1_pos, hp1_lt⟩, hp2⟩
    rcases hq with ⟨⟨hq1_pos, hq1_lt⟩, hq2⟩
    have hp2_pos : 0 < p.2 := lt_of_lt_of_le hB_pos hp2
    have hq2_pos : 0 < q.2 := lt_of_lt_of_le hB_pos hq2
    have h_add1 := intervalIntegral.integral_add_adjacent_intervals
      (hF_int p.1 q.1 hp1_pos hq1_pos) (hF_int q.1 p.2 hq1_pos hp2_pos)
    have h_add2 := intervalIntegral.integral_add_adjacent_intervals
      (hF_int q.1 p.2 hq1_pos hp2_pos) (hF_int p.2 q.2 hp2_pos hq2_pos)
    have h_diff : F_int p - F_int q =
        (∫ τ in p.1..q.1, F_osc τ) - (∫ τ in p.2..q.2, F_osc τ) := by
      dsimp [F_int]
      rw [← h_add1, ← h_add2]
      ring
    have h_low : ∫ τ in p.1..q.1, F_osc τ = 0 :=
      h_lower_vanish hp1_pos hp1_lt.le hq1_pos hq1_lt.le
    have h_tail_lt : K_tail / B < ε := by
      have hB_gt : 2 * K_tail / ε < B := by linarith [le_max_right R₀ (2 * K_tail / ε + 1)]
      rw [div_lt_iff₀ hB_pos]
      have h1 : 2 * K_tail < B * ε := (div_lt_iff₀ hε).mp hB_gt
      linarith
    have h_hi : ‖∫ τ in p.2..q.2, F_osc τ‖ ≤ K_tail / B := by
      rcases le_total p.2 q.2 with hpq | hqp
      · have h1 := h_upper_tail ((le_max_left _ _).trans hp2) hpq
        exact h1.trans (div_le_div_of_nonneg_left hK_nn hB_pos hp2)
      · have h1 := h_upper_tail ((le_max_left _ _).trans hq2) hqp
        rw [intervalIntegral.integral_symm, norm_neg]
        exact h1.trans (div_le_div_of_nonneg_left hK_nn hB_pos hq2)
    rw [dist_eq_norm, h_diff, h_low, zero_sub, norm_neg]
    exact h_hi.trans_lt h_tail_lt
  obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.mp hCauchy
  refine ⟨L, hL, ?_⟩
  have h_ev : ∀ᶠ p : ℝ × ℝ in 𝓝[>] (0 : ℝ) ×ˢ Filter.atTop,
      ‖F_int p‖ ≤ tebOscConst b₀ N * M *
        (c⁻¹ + c ^ (-(1 / 2 : ℝ)) * min (τ₀ ^ 2) 1 * if A * c ^ (-(1 / 3 : ℝ)) < τ₀ then 1 else 0) := by
    have hS_mem : Ioo (0 : ℝ) a_max ×ˢ Ici R₀ ∈ 𝓝[>] (0 : ℝ) ×ˢ Filter.atTop :=
      Filter.prod_mem_prod (Ioo_mem_nhdsGT ha_max_pos) (Ici_mem_atTop R₀)
    filter_upwards [hS_mem] with p hp
    rcases hp with ⟨⟨hp1_pos, hp1_lt⟩, hp2⟩
    have hp1_le : p.1 ≤ p.2 := by
      have ha_le : a_max ≤ eps := min_le_right _ _
      have heps_le : eps ≤ R₀ := by
        linarith [le_max_right (2 * τ₀ + 1) (max 2 (eps + 1)), le_max_right (2 : ℝ) (eps + 1)]
      linarith [mem_Ici.mp hp2]
    exact teb_edge_osc_interval hτ₀ hA hb₀ hc hp1_pos hp1_le hw hw_cont hw_pos hφ hφ' hφ'_mono
      h_upper h_lower h_mid hh_cont hh_vanish hh_bv
  exact le_of_tendsto hL.norm h_ev

/-- Specialization of **Lemma TE.1a** to `w = id` (`dw(τ) = dτ`), with integrability proved
automatically from the Gaussian decay hypothesis. -/
theorem teb_edge_osc_id {φ φ' φ'' : ℝ → ℝ} {h : ℝ → ℂ}
    {τ₀ A b₀ N M c : ℝ}
    (hτ₀ : 0 ≤ τ₀) (hA : 0 < A) (hb₀ : 0 < b₀) (hc : 1 ≤ c)
    (hφ : ∀ y ∈ Ioi 0, HasDerivAt φ (φ' y) y)
    (hφ' : ∀ y ∈ Ioi 0, HasDerivAt φ' (φ'' y) y)
    (hφ'_mono : MonotoneOn φ' (Ioi 0) ∨ AntitoneOn φ' (Ioi 0))
    (h_upper : ∀ τ, 2 * τ₀ < τ → b₀ * min (τ ^ 2) 1 ≤ |φ' τ|)
    (h_lower : ∀ τ, 0 < τ → τ < τ₀ / 2 → b₀ * min (τ₀ ^ 2) 1 ≤ |φ' τ|)
    (h_mid : 0 < τ₀ → ∀ τ, τ₀ / 2 ≤ τ → τ ≤ 2 * τ₀ →
      b₀ * τ₀ / (1 + τ₀ ^ 3) ≤ |φ'' τ|)
    (hh_cont : ContinuousOn h (Ioi 0))
    (hh_vanish : ∀ τ, 0 < τ → τ ≤ 2 * A * c ^ (-(1 / 3 : ℝ)) → h τ = 0)
    (hh_bv : ∀ s > 0, BoundedVariationOn h (Icc s (2 * s)) ∧
      ∀ τ ∈ Icc s (2 * s), ‖h τ‖ + (eVariationOn h (Icc s (2 * s))).toReal ≤
        M * s ^ (5 / 2 : ℝ) * (1 + s) ^ N * Real.exp (-s ^ 2)) :
    ‖∫ τ in Ioi (0 : ℝ), h τ * Complex.exp (Complex.I * (c : ℂ) * (φ τ : ℂ))‖ ≤
      tebOscConst b₀ N * M *
        (c⁻¹ + c ^ (-(1 / 2 : ℝ)) * min (τ₀ ^ 2) 1 * if A * c ^ (-(1 / 3 : ℝ)) < τ₀ then 1 else 0) := by
  have hc_pos : 0 < c := by linarith
  have hM_nn : 0 ≤ M := nonneg_of_hh_bv_unit hh_bv
  have hφ_cont : ContinuousOn φ (Ioi 0) := fun y hy => (hφ y hy).continuousAt.continuousWithinAt
  let F_osc : ℝ → ℂ := fun τ => h τ * Complex.exp (Complex.I * (c : ℂ) * (φ τ : ℂ))
  have haesm : AEStronglyMeasurable F_osc (volume.restrict (Ioi 0)) := by
    have hcont : ContinuousOn F_osc (Ioi 0) :=
      hh_cont.mul (Complex.continuous_exp.continuousOn.comp
        (continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.comp hφ_cont (mapsTo_univ _ _)))
        (mapsTo_univ _ _))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hint : IntegrableOn F_osc (Ioi 0) := by
    set eps := 2 * A * c ^ (-(1 / 3 : ℝ))
    have heps_pos : 0 < eps := by positivity
    have h_split : Ioi (0 : ℝ) ⊆ Ioc 0 (max 1 eps) ∪ Ioi 1 := fun τ hτ => by
      rcases le_or_gt τ 1 with hle | hgt
      · left; exact ⟨hτ, hle.trans (le_max_left _ _)⟩
      · right; exact hgt
    refine IntegrableOn.mono_set ?_ h_split
    refine IntegrableOn.union ?_ ?_
    · have h_sub : Ioc (0 : ℝ) (max 1 eps) ⊆ Ioc 0 eps ∪ Icc eps (max 1 eps) := fun τ hτ => by
        rcases le_or_gt τ eps with hle | hgt
        · left; exact ⟨hτ.1, hle⟩
        · right; exact ⟨hgt.le, hτ.2⟩
      refine IntegrableOn.mono_set ?_ h_sub
      refine IntegrableOn.union ?_ ?_
      · have hzero : EqOn F_osc 0 (Ioc 0 eps) := fun τ hτ => by
          dsimp [F_osc]; rw [hh_vanish τ hτ.1 hτ.2, zero_mul]
        exact (integrableOn_zero.congr_fun hzero.symm measurableSet_Ioc)
      · have hsub_0 : Icc eps (max 1 eps) ⊆ Ioi 0 := fun τ hτ => lt_of_lt_of_le heps_pos hτ.1
        have hcont : ContinuousOn F_osc (Icc eps (max 1 eps)) :=
          (hh_cont.mono hsub_0).mul (Complex.continuous_exp.continuousOn.comp
            (continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.comp
              (hφ_cont.mono hsub_0) (mapsTo_univ _ _))) (mapsTo_univ _ _))
        exact hcont.integrableOn_Icc
    · set m := Nat.ceil ((5 / 2 + max N 0 + 2) / 2)
      have h_maj_int : IntegrableOn
          (fun τ : ℝ => M * (2 : ℝ) ^ max N 0 * (Nat.factorial m : ℝ) * τ ^ (-2 : ℝ)) (Ioi 1) :=
        ((integrableOn_Ioi_rpow_iff (s := (-2 : ℝ)) zero_lt_one).mpr (by norm_num)).const_mul _
      refine h_maj_int.mono' (haesm.mono_set (Ioi_subset_Ioi zero_le_one)) ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine ae_of_all _ fun τ hτ => ?_
      have hτ1 : 1 ≤ τ := le_of_lt hτ
      have hτ0 : 0 < τ := lt_of_lt_of_le zero_lt_one hτ1
      have h_norm_eq : ‖F_osc τ‖ = ‖h τ‖ := by
        dsimp [F_osc]
        rw [norm_mul, show Complex.I * (c : ℂ) * (φ τ : ℂ) = ((c * φ τ : ℝ) : ℂ) * Complex.I by
          push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]
      rw [h_norm_eq]
      have hbv_τ := (hh_bv τ hτ0).2 τ ⟨le_rfl, by linarith⟩
      have h_h_le : ‖h τ‖ ≤ M * τ ^ (5 / 2 : ℝ) * (1 + τ) ^ N * Real.exp (-τ ^ 2) := by
        have : 0 ≤ (eVariationOn h (Icc τ (2 * τ))).toReal := ENNReal.toReal_nonneg
        linarith
      have h_1τ : (1 + τ) ^ N ≤ (2 : ℝ) ^ max N 0 * τ ^ max N 0 := by
        have h1 : (1 + τ) ^ N ≤ (1 + τ) ^ max N 0 :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left N 0)
        have h2 : (1 + τ) ^ max N 0 ≤ (2 * τ) ^ max N 0 :=
          Real.rpow_le_rpow (by linarith) (by linarith) (le_max_right N 0)
        rw [Real.mul_rpow (by norm_num) hτ0.le] at h2
        exact h1.trans h2
      have h_rpow_bound := rpow_mul_exp_neg_sq_le (p := 5 / 2 + max N 0) (q := 2) hτ1
      have h_comb : τ ^ (5 / 2 : ℝ) * τ ^ max N 0 = τ ^ (5 / 2 + max N 0) :=
        (Real.rpow_add hτ0 _ _).symm
      calc ‖h τ‖
          ≤ M * τ ^ (5 / 2 : ℝ) * (1 + τ) ^ N * Real.exp (-τ ^ 2) := h_h_le
        _ ≤ M * τ ^ (5 / 2 : ℝ) * ((2 : ℝ) ^ max N 0 * τ ^ max N 0) * Real.exp (-τ ^ 2) := by
            gcongr
        _ = M * (2 : ℝ) ^ max N 0 * (τ ^ (5 / 2 + max N 0) * Real.exp (-τ ^ 2)) := by
            rw [← h_comb]; ring
        _ ≤ M * (2 : ℝ) ^ max N 0 * ((Nat.factorial m : ℝ) * τ ^ (-2 : ℝ)) := by gcongr
        _ = M * (2 : ℝ) ^ max N 0 * (Nat.factorial m : ℝ) * τ ^ (-2 : ℝ) := by ring
  have him : id '' Ioi (0 : ℝ) = Ioi 0 := Set.image_id _
  have h_res := teb_edge_osc (w := id) (w' := fun _ => 1) hτ₀ hA hb₀ hc
    (fun τ _ => hasDerivAt_id τ) continuousOn_const (fun _ _ => zero_lt_one)
    (by simpa [him] using hφ) (by simpa [him] using hφ') (by simpa [him] using hφ'_mono)
    h_upper h_lower h_mid hh_cont hh_vanish hh_bv (by simpa [id, Complex.ofReal_one, mul_one] using hint)
  simpa only [id, Complex.ofReal_one, mul_one] using h_res

end EdgeOscEstimate

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.TwoEdgeBootstrap.teb_edge_osc_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.teb_edge_osc_interval

/-- info: 'FormalResearch.TwoEdgeBootstrap.teb_edge_osc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.teb_edge_osc

/-- info: 'FormalResearch.TwoEdgeBootstrap.teb_edge_osc_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.teb_edge_osc_tendsto

/-- info: 'FormalResearch.TwoEdgeBootstrap.teb_edge_osc_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.TwoEdgeBootstrap.teb_edge_osc_id

end FormalResearch.TwoEdgeBootstrap
