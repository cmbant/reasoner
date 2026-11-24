module

public import FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuumNode
public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityApprox

/-!
# Uniform bounds for the Airy product factors of approximating designs (`virasoro_two_level.tex`, `gt:2.6`)

The designs approximating an ideal datum have sites `s_k` (`3 ≤ k ≤ K`), `a_k` (up to `n + 2`) and the reference sites
beyond, and half-widths `η gap_k` (`η → 0`) or `gap_k / 4`.  All of them satisfy the *uniform tail bound* `UnifTail`:
`|S_j(k) - a_k| ≤ A k^{-4/3}`, `|W_j(k)| ≤ A k^{-1/3}` with one `A` for the whole family.

* `factor_dev_core`: for `c · k^{2/3} ≤ |u - a_k|`, `u ∈ ℂ`, `|s - a_k| ≤ A k^{-4/3}`, `|w| ≤ A k^{-1/3}`: the factor
  `((u - s)² + w²)/(u - a_k)²` is within `C/k²` of `1` (the node case `u = a_n` of `NegativeVacuum.factor_dev` and the
  generic case `‖u‖ ≤ R`, `k` large);
* `exists_tail_bound`: for `‖u‖ ≤ R` the factors `k ≥ N₀` of a `UnifTail` family are within `C/k²` of `1`;
* `norm_airyProdTail_le`: `‖Π_{k > N}‖ ≤ B` uniformly in the family and in `‖u‖ ≤ R` (`N ≥ N₀`);
* `tendsto_airyProdTail_one`: the tails tend to `1` when the sites tend to `a_k` and the widths to `0`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel.IdealApprox

open FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window
open FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum

/-- Uniform WKB bounds: `|a_k - u_k^W| ≤ A k^{-4/3}` and `gap_k ≤ A k^{-1/3}`. -/
lemma uniform_wkb_bound : ∃ A : ℝ, 0 < A ∧ ∀ k : ℕ, 1 ≤ k →
    |airyZero k - uWKB k| ≤ A * (k : ℝ) ^ (-(4 / 3 : ℝ)) ∧ gapWKB k ≤ A * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨C₀, hC₀, h₀⟩ := deltaWKB_le_exists
  refine ⟨max C₀ ((2 / 3 : ℝ) * kappaAiry * (4 / 3 : ℝ) ^ (1 / 3 : ℝ)), ?_, fun k hk => ⟨?_, ?_⟩⟩
  · have := kappaAiry_pos
    positivity
  · have := h₀ k hk
    unfold deltaWKB at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · exact (gapWKB_le_mul_rpow hk).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

/-- A family `(S j, W j)` of sites and widths with one uniform tail bound. -/
def UnifTail (S W : ℕ → ℕ → ℝ) : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ j k : ℕ, 1 ≤ k →
    |S j k - airyZero k| ≤ A * (k : ℝ) ^ (-(4 / 3 : ℝ)) ∧ |W j k| ≤ A * (k : ℝ) ^ (-(1 / 3 : ℝ))

/-- The tail hypothesis of the Airy product for sites and widths with the bounds of `UnifTail`. -/
lemma tailHyp_of_unif {S W : ℕ → ℝ} {A : ℝ} (hA : 0 < A)
    (h : ∀ k : ℕ, 1 ≤ k → |S k - airyZero k| ≤ A * (k : ℝ) ^ (-(4 / 3 : ℝ)) ∧
      |W k| ≤ A * (k : ℝ) ^ (-(1 / 3 : ℝ))) (f : ℕ) : AiryProdTailHypothesis f S W := by
  obtain ⟨A₀, hA₀, hb⟩ := uniform_wkb_bound
  refine tailHyp_of_bound (M := 0) (C := A + A₀) (by positivity) fun k hk => ?_
  have hk1 : 1 ≤ k := hk
  obtain ⟨h1, h2⟩ := h k hk1
  obtain ⟨h3, -⟩ := hb k hk1
  have hp : 0 ≤ (k : ℝ) ^ (-(4 / 3 : ℝ)) := by positivity
  have hp' : 0 ≤ (k : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
  refine ⟨?_, by nlinarith⟩
  have : |S k - uWKB k| ≤ |S k - airyZero k| + |airyZero k - uWKB k| := by
    have e : S k - uWKB k = (S k - airyZero k) + (airyZero k - uWKB k) := by ring
    rw [e]; exact abs_add_le _ _
  nlinarith

/-- **Deviation of a factor from `1`** (`u` a point at distance `≥ c k^{2/3}` from `a_k`). -/
lemma factor_dev_core {k : ℕ} (hk1 : 1 ≤ k) {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) {u : ℂ} {s w : ℝ}
    (hD : c * ((k : ℝ) ^ (1 / 3 : ℝ)) ^ 2 ≤ ‖u - (airyZero k : ℂ)‖)
    (hs : |s - airyZero k| ≤ A * (k : ℝ) ^ (-(4 / 3 : ℝ))) (hw : |w| ≤ A * (k : ℝ) ^ (-(1 / 3 : ℝ))) :
    ‖((u - (s : ℂ)) ^ 2 + (w : ℂ) ^ 2) / (u - (airyZero k : ℂ)) ^ 2 - 1‖ ≤
      (2 * A / c + 2 * A ^ 2 / c ^ 2) / (k : ℝ) ^ 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  set r : ℝ := (k : ℝ) ^ (1 / 3 : ℝ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hk0 _
  have hr3 : r ^ 3 = k := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hk0.le]; norm_num
  have hr1 : 1 ≤ r := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    exact Real.one_le_rpow this (by norm_num)
  have e13 : (k : ℝ) ^ (-(1 / 3 : ℝ)) = (r)⁻¹ := by rw [Real.rpow_neg hk0.le]
  have e43 : (k : ℝ) ^ (-(4 / 3 : ℝ)) = (r ^ 4)⁻¹ := by
    rw [Real.rpow_neg hk0.le, hr, ← Real.rpow_natCast, ← Real.rpow_mul hk0.le]; norm_num
  rw [e13] at hw
  rw [e43] at hs
  set D : ℝ := ‖u - (airyZero k : ℂ)‖ with hDdef
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD
  set t : ℝ := airyZero k - s with ht
  have htr : |t| * r ^ 4 ≤ A := by
    have h1 : |t| ≤ A * (r ^ 4)⁻¹ := by rw [ht, abs_sub_comm]; exact hs
    have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ r ^ 4)
    rwa [mul_assoc, inv_mul_cancel₀ (by positivity), mul_one] at this
  have hwr : |w| * r ≤ A := by
    have := mul_le_mul_of_nonneg_right hw hr0.le
    rwa [mul_assoc, inv_mul_cancel₀ hr0.ne', mul_one] at this
  have hd0 : u - (airyZero k : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hDdef; linarith
  have hnum : ((u - (s : ℂ)) ^ 2 + (w : ℂ) ^ 2) / (u - (airyZero k : ℂ)) ^ 2 - 1 =
      (2 * (u - (airyZero k : ℂ)) * (t : ℂ) + (t : ℂ) ^ 2 + (w : ℂ) ^ 2) / (u - (airyZero k : ℂ)) ^ 2 := by
    rw [ht]; push_cast
    field_simp
    ring
  rw [hnum, norm_div, norm_pow]
  change _ / D ^ 2 ≤ _
  have habs : ‖2 * (u - (airyZero k : ℂ)) * (t : ℂ) + (t : ℂ) ^ 2 + (w : ℂ) ^ 2‖ ≤
      2 * D * |t| + |t| ^ 2 + |w| ^ 2 := by
    calc ‖2 * (u - (airyZero k : ℂ)) * (t : ℂ) + (t : ℂ) ^ 2 + (w : ℂ) ^ 2‖
        ≤ ‖2 * (u - (airyZero k : ℂ)) * (t : ℂ)‖ + ‖(t : ℂ) ^ 2‖ + ‖(w : ℂ) ^ 2‖ := norm_add₃_le
      _ = 2 * D * |t| + |t| ^ 2 + |w| ^ 2 := by
          rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, Complex.norm_ofNat]
  have hk2 : (k : ℝ) ^ 2 = r ^ 6 := by rw [← hr3]; ring
  have hmain : (2 * D * |t| + |t| ^ 2 + |w| ^ 2) / D ^ 2 ≤ (2 * A / c + 2 * A ^ 2 / c ^ 2) / (k : ℝ) ^ 2 := by
    rw [hk2, div_le_div_iff₀ (by positivity) (by positivity)]
    have hr2D : r ^ 2 ≤ D / c := by rw [le_div_iff₀ hc]; linarith
    have hc2 : c ^ 2 * r ^ 4 ≤ D ^ 2 := by
      nlinarith [mul_pos hc (by positivity : (0 : ℝ) < r ^ 2)]
    have ht0 := abs_nonneg t
    have hw0 := abs_nonneg w
    have t1 : 2 * D * |t| * r ^ 6 ≤ (2 * A / c) * D ^ 2 := by
      calc 2 * D * |t| * r ^ 6 = 2 * D * (|t| * r ^ 4) * r ^ 2 := by ring
        _ ≤ 2 * D * A * r ^ 2 := by gcongr
        _ ≤ 2 * D * A * (D / c) := by gcongr
        _ = (2 * A / c) * D ^ 2 := by ring
    have t2 : |t| ^ 2 * r ^ 6 ≤ (A ^ 2 / c ^ 2) * D ^ 2 := by
      have h6 : r ^ 6 ≤ r ^ 8 := pow_le_pow_right₀ hr1 (by norm_num)
      have hcD : c ≤ D := by nlinarith [one_le_pow₀ (n := 2) hr1]
      have hc2' : c ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hc.le hcD 2
      calc |t| ^ 2 * r ^ 6 ≤ |t| ^ 2 * r ^ 8 := by gcongr
        _ = (|t| * r ^ 4) ^ 2 := by ring
        _ ≤ A ^ 2 := by gcongr
        _ = (A ^ 2 / c ^ 2) * c ^ 2 := by field_simp
        _ ≤ (A ^ 2 / c ^ 2) * D ^ 2 := mul_le_mul_of_nonneg_left hc2' (by positivity)
    have t3 : |w| ^ 2 * r ^ 6 ≤ (A ^ 2 / c ^ 2) * D ^ 2 := by
      calc |w| ^ 2 * r ^ 6 = (|w| * r) ^ 2 * r ^ 4 := by ring
        _ ≤ A ^ 2 * r ^ 4 := by gcongr
        _ = (A ^ 2 / c ^ 2) * (c ^ 2 * r ^ 4) := by field_simp
        _ ≤ (A ^ 2 / c ^ 2) * D ^ 2 := mul_le_mul_of_nonneg_left hc2 (by positivity)
    calc (2 * D * |t| + |t| ^ 2 + |w| ^ 2) * r ^ 6
        = 2 * D * |t| * r ^ 6 + |t| ^ 2 * r ^ 6 + |w| ^ 2 * r ^ 6 := by ring
      _ ≤ (2 * A / c) * D ^ 2 + (A ^ 2 / c ^ 2) * D ^ 2 + (A ^ 2 / c ^ 2) * D ^ 2 := by linarith
      _ = (2 * A / c + 2 * A ^ 2 / c ^ 2) * D ^ 2 := by ring
  exact (div_le_div_of_nonneg_right habs (by positivity)).trans hmain

/-- For `‖u‖ ≤ R` and `k ≥ N₀` the factors of a `UnifTail` family are within `C / k²` of `1`. -/
lemma exists_tail_bound {S W : ℕ → ℕ → ℝ} (hU : UnifTail S W) (R : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (u : ℂ), ‖u‖ ≤ R → ∀ k : ℕ, N₀ ≤ k →
      ‖airyProdFactor (S j) (W j) k u - 1‖ ≤ C / (k : ℝ) ^ 2 := by
  obtain ⟨A, hA, hb⟩ := hU
  obtain ⟨N₀, hN₀, hN⟩ := norm_sub_airyZero_ge_eventually R
  refine ⟨N₀, hN₀, 2 * A / 1 + 2 * A ^ 2 / 1 ^ 2, by positivity, fun j u hu k hk => ?_⟩
  have hk1 : 1 ≤ k := by omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  obtain ⟨h1, h2⟩ := hb j k hk1
  have hD : 1 * ((k : ℝ) ^ (1 / 3 : ℝ)) ^ 2 ≤ ‖u - (airyZero k : ℂ)‖ := by
    rw [one_mul, ← Real.rpow_natCast, ← Real.rpow_mul hk0.le]
    have := hN k hk u hu
    norm_num
    exact this
  unfold airyProdFactor
  exact factor_dev_core hk1 hA.le one_pos hD h1 h2

/-- The summable bound used for the products. -/
lemma summable_bound (C : ℝ) : Summable (fun m : ℕ => C / ((m : ℝ) + 1) ^ 2) := by
  have h := ((summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))).mul_left C
  refine h.congr fun m => ?_
  push_cast
  rw [mul_one_div]

lemma bound_le {C : ℝ} (hC : 0 ≤ C) (N m : ℕ) :
    C / (((N + 1 + m : ℕ) : ℝ)) ^ 2 ≤ C / ((m : ℝ) + 1) ^ 2 := by
  have h1 : (m : ℝ) + 1 ≤ ((N + 1 + m : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  exact div_le_div_of_nonneg_left hC (by positivity) (pow_le_pow_left₀ (by positivity) h1 2)

/-- The tail products of a `UnifTail` family are uniformly bounded on `‖u‖ ≤ R` (`N ≥ N₀`). -/
lemma norm_airyProdTail_le {S W : ℕ → ℕ → ℝ} (hU : UnifTail S W) (R : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ (j : ℕ) (u : ℂ), ‖u‖ ≤ R → ∀ N : ℕ, N₀ ≤ N →
      ‖airyProdTail N (S j) (W j) u‖ ≤ B := by
  obtain ⟨N₀, hN₀, C, hC, hbd⟩ := exists_tail_bound hU R
  obtain ⟨A, hA, hb⟩ := hU
  obtain ⟨K₀, hK₀2, hK₀⟩ := norm_sub_airyZero_ge_eventually R
  refine ⟨max N₀ K₀, le_trans hN₀ (le_max_left _ _), Real.exp (∑' m : ℕ, C / ((m : ℝ) + 1) ^ 2),
    (Real.exp_pos _).le, fun j u hu N hN => ?_⟩
  have hN₁ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN₂ : K₀ ≤ N := le_trans (le_max_right _ _) hN
  have hne : ∀ k : ℕ, N < k → u ≠ (airyZero k : ℂ) := fun k hk h => by
    have := hK₀ k (by omega) u hu
    rw [h, sub_self, norm_zero] at this
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have := Real.rpow_pos_of_pos hk0 (2 / 3 : ℝ)
    linarith
  have hH := tailHyp_of_unif hA (fun k hk => hb j k hk) N
  have hp := hasProd_airyProdTail hH hne
  have hnorm : Tendsto (fun s : Finset ℕ => ‖∏ m ∈ s, airyProdFactor (S j) (W j) (N + 1 + m) u - 1‖)
      atTop (𝓝 ‖airyProdTail N (S j) (W j) u - 1‖) :=
    (continuous_norm.comp (continuous_id.sub continuous_const)).continuousAt.tendsto.comp hp
  have hsum := summable_bound C
  have hle : ‖airyProdTail N (S j) (W j) u - 1‖ ≤ Real.exp (∑' m : ℕ, C / ((m : ℝ) + 1) ^ 2) - 1 := by
    refine le_of_tendsto hnorm (Eventually.of_forall fun s => ?_)
    have := Finset.norm_prod_one_add_sub_one_le s
      (fun m => airyProdFactor (S j) (W j) (N + 1 + m) u - 1)
    simp only [add_sub_cancel] at this
    refine this.trans ?_
    gcongr
    calc ∑ m ∈ s, ‖airyProdFactor (S j) (W j) (N + 1 + m) u - 1‖
        ≤ ∑ m ∈ s, C / ((m : ℝ) + 1) ^ 2 :=
          Finset.sum_le_sum fun m _ => (hbd j u hu (N + 1 + m) (by omega)).trans (bound_le hC N m)
      _ ≤ ∑' m : ℕ, C / ((m : ℝ) + 1) ^ 2 :=
          hsum.sum_le_tsum _ fun m _ => by positivity
  have h1 : ‖airyProdTail N (S j) (W j) u‖ ≤ 1 + ‖airyProdTail N (S j) (W j) u - 1‖ := by
    have := norm_add_le (1 : ℂ) (airyProdTail N (S j) (W j) u - 1)
    simpa using this
  linarith

/-- The tails tend to `1` when the sites tend to `a_k` and the widths to `0` (Tannery for infinite products). -/
lemma tendsto_airyProdTail_one {S W : ℕ → ℕ → ℝ} {R : ℝ} {u : ℂ} (hu : ‖u‖ ≤ R) {N₀ N : ℕ}
    (hbd : ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (u : ℂ), ‖u‖ ≤ R → ∀ k : ℕ, N₀ ≤ k →
      ‖airyProdFactor (S j) (W j) k u - 1‖ ≤ C / (k : ℝ) ^ 2)
    (hS : ∀ k, N < k → Tendsto (fun j => S j k) atTop (𝓝 (airyZero k)))
    (hW : ∀ k, N < k → Tendsto (fun j => W j k) atTop (𝓝 0)) (hN : N₀ ≤ N)
    (hne : ∀ k : ℕ, N < k → u ≠ (airyZero k : ℂ)) :
    Tendsto (fun j => airyProdTail N (S j) (W j) u) atTop (𝓝 1) := by
  obtain ⟨C, hC, hb⟩ := hbd
  have key : ∀ j, airyProdTail N (S j) (W j) u =
      ∏' m : ℕ, (1 + (airyProdFactor (S j) (W j) (N + 1 + m) u - 1)) := fun j => by
    unfold airyProdTail
    exact tprod_congr fun m => by ring
  simp only [key]
  have h := tendsto_tprod_one_add_of_dominated_convergence (𝓕 := (atTop : Filter ℕ))
    (f := fun j m => airyProdFactor (S j) (W j) (N + 1 + m) u - 1) (g := fun _ => (0 : ℂ))
    (bound := fun m : ℕ => C / ((m : ℝ) + 1) ^ 2) (summable_bound C) ?_ ?_
  · simpa using h
  · intro m
    have hk : N < N + 1 + m := by omega
    have hden : (u - (airyZero (N + 1 + m) : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (hne _ hk))
    unfold airyProdFactor
    have h1 := Complex.continuous_ofReal.continuousAt.tendsto.comp (hS (N + 1 + m) hk)
    have h2 := Complex.continuous_ofReal.continuousAt.tendsto.comp (hW (N + 1 + m) hk)
    have h3 : Tendsto (fun j => ((u - ((S j (N + 1 + m) : ℝ) : ℂ)) ^ 2 + ((W j (N + 1 + m) : ℝ) : ℂ) ^ 2) /
        (u - (airyZero (N + 1 + m) : ℂ)) ^ 2) atTop
        (𝓝 (((u - ((airyZero (N + 1 + m) : ℝ) : ℂ)) ^ 2 + ((0 : ℝ) : ℂ) ^ 2) /
          (u - (airyZero (N + 1 + m) : ℂ)) ^ 2)) :=
      (((tendsto_const_nhds.sub h1).pow 2).add (h2.pow 2)).div_const _
    have e : ((u - ((airyZero (N + 1 + m) : ℝ) : ℂ)) ^ 2 + ((0 : ℝ) : ℂ) ^ 2) /
          (u - (airyZero (N + 1 + m) : ℂ)) ^ 2 = 1 := by
      simp only [Complex.ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
      exact div_self hden
    rw [e] at h3
    simpa using h3.sub_const 1
  · refine Eventually.of_forall fun j m => ?_
    exact (hb j u hu (N + 1 + m) (by omega)).trans (bound_le hC N m)

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.IdealApprox.norm_airyProdTail_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_airyProdTail_le

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.IdealApprox.tendsto_airyProdTail_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_airyProdTail_one

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.IdealApprox.factor_dev_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms factor_dev_core

end FormalResearch.ModularBootstrap.TwoLevel.IdealApprox
