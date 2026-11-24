module

public import FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuumNode
public import FormalResearch.ModularBootstrap.TwoLevel.WindowOptimumLimit

/-!
# The approximating two-simple-zero designs of Theorem 2.5, Step 1

For a Clark angle `α`, `K ≥ 3`, the second zero `q = u₂`, `n ≥ 1` modified pairs (`N = n + 2`) and `η > 0` the design
`negDesign α K n η q` has first zero `p = z₁ - η` and modified pairs `k = 3, …, N` at the Clark nodes `z_k`
(`k ≤ K`) and the Airy zeros `a_k` (`K < k ≤ N`) with half-widths `η · gapWKB k`; beyond `N` the reference pairs.
The limit data `siteLim`, zero widths, are those of `f_K`.

* `negDesign_adm`: admissibility for `q < z₂`, `0 < η < z₁ - z₂`, `η ≤ 1/4`... (see the statement);
* `negDesign_site`, `negDesign_width`: the design's site and width sequences are `siteSeq`, `widthSeq`;
* `tailHyp_siteSeq`, `tailHyp_siteLim`: tail hypotheses of the Airy product;
* `factor_dev`: for `n ≤ K < k` the factor `((a_n - s)² + w²)/(a_n - a_k)²` of a pair with `|s - a_k| ≲ k^{-4/3}`,
  `|w| ≲ k^{-1/3}` is within `C/k²` of `1`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum

open FormalResearch.Special FormalResearch.SignUncertainty FormalResearch.ModularBootstrap.Upper.Window

/-- Uniform WKB bounds: `|a_k - u_k^W| ≤ A k^{-4/3}` and `gap_k ≤ A k^{-1/3}`. -/
lemma exists_uniform_bound : ∃ A : ℝ, 0 < A ∧ ∀ k : ℕ, 1 ≤ k →
    |airyZero k - uWKB k| ≤ A * (k : ℝ) ^ (-(4 / 3 : ℝ)) ∧ gapWKB k ≤ A * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨C₀, hC₀, h₀⟩ := deltaWKB_le_exists
  refine ⟨max C₀ ((2 / 3 : ℝ) * kappaAiry * (4 / 3 : ℝ) ^ (1 / 3 : ℝ)), ?_, fun k hk => ⟨?_, ?_⟩⟩
  · have := kappaAiry_pos
    positivity
  · have := h₀ k hk
    unfold deltaWKB at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · exact (gapWKB_le_mul_rpow hk).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

/-- Sites of the design `negDesign`: `k ∈ [3, n+2]` at `z_k` (`k ≤ K`) or `a_k`, reference beyond. -/
noncomputable def siteSeq (α : ℝ) (K n : ℕ) (k : ℕ) : ℝ :=
  if 3 ≤ k ∧ k ≤ n + 2 then (if k ≤ K then clarkNode α k else airyZero k) else uWKB k

/-- Half-widths of the design `negDesign`. -/
noncomputable def widthSeq (n : ℕ) (η : ℝ) (k : ℕ) : ℝ :=
  (if 3 ≤ k ∧ k ≤ n + 2 then η else 1 / 4) * gapWKB k

/-- The limit sites (`n = ∞`) of the designs; the limit widths are `0`. -/
noncomputable def siteLim (α : ℝ) (K : ℕ) (k : ℕ) : ℝ :=
  if 3 ≤ k then (if k ≤ K then clarkNode α k else airyZero k) else uWKB k

/-- The approximating design of Theorem 2.5, Step 1. -/
noncomputable def negDesign (α : ℝ) (K n : ℕ) (η q : ℝ) : TwoZeroDesign n where
  p := clarkNode α 1 - η
  q := q
  s := fun i => if (i : ℕ) + 3 ≤ K then clarkNode α ((i : ℕ) + 3) else airyZero ((i : ℕ) + 3)
  e := fun i => η * gapWKB ((i : ℕ) + 3)

lemma negDesign_site (α : ℝ) (K n : ℕ) (η q : ℝ) : (negDesign α K n η q).site = siteSeq α K n := by
  funext k
  unfold TwoZeroDesign.site siteSeq
  by_cases h : 3 ≤ k ∧ k ≤ n + 2
  · simp only [h, and_self, dite_true, ↓reduceIte, negDesign]
    rw [Nat.sub_add_cancel h.1]
  · simp only [h, dite_false, ↓reduceIte]

lemma negDesign_width (α : ℝ) (K n : ℕ) (η q : ℝ) : (negDesign α K n η q).width = widthSeq n η := by
  funext k
  unfold TwoZeroDesign.width widthSeq
  by_cases h : 3 ≤ k ∧ k ≤ n + 2
  · simp only [h, and_self, dite_true, ↓reduceIte, negDesign]
    rw [Nat.sub_add_cancel h.1]
  · simp only [h, dite_false, ↓reduceIte]

lemma clarkNode_lt_zero_of_ge {α : ℝ} {k : ℕ} (hk : 2 ≤ k) : clarkNode α k < 0 := by
  rcases hk.eq_or_lt with rfl | h
  · exact clarkNode_two_lt_zero α
  · exact (clarkNode_lt_of_lt (n := 2) (by norm_num) h α).trans (clarkNode_two_lt_zero α)

/-- Admissibility of `negDesign`. -/
lemma negDesign_adm (α : ℝ) {K n : ℕ} {η q : ℝ} (hη : 0 < η) (hq : q < clarkNode α 2)
    (hη2 : η < clarkNode α 1 - clarkNode α 2) : (negDesign α K n η q).Adm := by
  have h2 := clarkNode_two_lt_zero α
  refine ⟨?_, ?_, fun i => ?_, ?_, fun i => ?_⟩
  · show q < clarkNode α 1 - η
    linarith
  · show q < 0
    linarith
  · show (if (i : ℕ) + 3 ≤ K then clarkNode α ((i : ℕ) + 3) else airyZero ((i : ℕ) + 3)) < 0
    split_ifs
    · exact clarkNode_lt_zero_of_ge (by omega)
    · exact airyZero_neg _
  · intro i j hij
    have hij' : (if (i : ℕ) + 3 ≤ K then clarkNode α ((i : ℕ) + 3) else airyZero ((i : ℕ) + 3)) =
        (if (j : ℕ) + 3 ≤ K then clarkNode α ((j : ℕ) + 3) else airyZero ((j : ℕ) + 3)) := hij
    apply Fin.ext
    by_contra hne
    have hne' : (i : ℕ) ≠ j := fun h => hne h
    rcases lt_or_gt_of_ne hne' with hl | hl
    · by_cases hi : (i : ℕ) + 3 ≤ K <;> by_cases hj : (j : ℕ) + 3 ≤ K <;> simp only [hi, hj, ↓reduceIte] at hij'
      · have := clarkNode_lt_of_lt (n := (i : ℕ) + 3) (m := (j : ℕ) + 3) (by omega) (by omega) α
        linarith
      · exact clarkNode_ne_airyZero α (by omega) (by omega) hij'
      · exact absurd hj (by omega)
      · have := airyZero_lt_of_lt (n := (i : ℕ) + 3) (m := (j : ℕ) + 3) (by omega) (by omega)
        linarith
    · by_cases hi : (i : ℕ) + 3 ≤ K <;> by_cases hj : (j : ℕ) + 3 ≤ K <;> simp only [hi, hj, ↓reduceIte] at hij'
      · have := clarkNode_lt_of_lt (n := (j : ℕ) + 3) (m := (i : ℕ) + 3) (by omega) (by omega) α
        linarith
      · exact absurd hj (by omega)
      · exact (clarkNode_ne_airyZero α (by omega) (by omega)) hij'.symm
      · have := airyZero_lt_of_lt (n := (j : ℕ) + 3) (m := (i : ℕ) + 3) (by omega) (by omega)
        linarith
  · show 0 < η * gapWKB ((i : ℕ) + 3)
    exact mul_pos hη (gapWKB_pos (by omega))

lemma negDesign_p (α : ℝ) (K n : ℕ) (η q : ℝ) : (negDesign α K n η q).p = clarkNode α 1 - η := rfl

lemma negDesign_q (α : ℝ) (K n : ℕ) (η q : ℝ) : (negDesign α K n η q).q = q := rfl

/-- Tail hypothesis for the design sequences. -/
lemma tailHyp_siteSeq (α : ℝ) (K n : ℕ) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    AiryProdTailHypothesis 2 (siteSeq α K n) (widthSeq n η) := by
  obtain ⟨A, hA, hb⟩ := exists_uniform_bound
  refine tailHyp_of_bound (M := K) hA fun k hk => ?_
  have hk1 : 1 ≤ k := by omega
  obtain ⟨h1, h2⟩ := hb k hk1
  have hp : 0 ≤ (k : ℝ) ^ (-(4 / 3 : ℝ)) := by positivity
  constructor
  · unfold siteSeq
    by_cases h : 3 ≤ k ∧ k ≤ n + 2
    · simp only [h, and_self, ↓reduceIte, show ¬(k ≤ K) by omega]
      exact h1
    · simp only [h, ↓reduceIte, sub_self, abs_zero]
      positivity
  · unfold widthSeq
    have hg := (gapWKB_pos hk1).le
    rw [abs_mul, abs_of_nonneg hg]
    have hη : |(if 3 ≤ k ∧ k ≤ n + 2 then η else (1 / 4 : ℝ))| ≤ 1 := by
      split_ifs
      · rw [abs_of_nonneg hη0]; exact hη1
      · rw [abs_of_nonneg (by norm_num)]; norm_num
    calc |(if 3 ≤ k ∧ k ≤ n + 2 then η else (1 / 4 : ℝ))| * gapWKB k ≤ 1 * gapWKB k :=
        mul_le_mul_of_nonneg_right hη hg
      _ ≤ A * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by linarith

/-- Tail hypothesis for the limit data (zero widths). -/
lemma tailHyp_siteLim (α : ℝ) {K : ℕ} (hK : 3 ≤ K) : AiryProdTailHypothesis 2 (siteLim α K) (fun _ => 0) := by
  obtain ⟨A, hA, hb⟩ := exists_uniform_bound
  refine tailHyp_of_bound (M := K) hA fun k hk => ?_
  have hk1 : 1 ≤ k := by omega
  obtain ⟨h1, h2⟩ := hb k hk1
  refine ⟨?_, by simp only [abs_zero]; positivity⟩
  unfold siteLim
  simp only [show 3 ≤ k by omega, ↓reduceIte, show ¬(k ≤ K) by omega]
  exact h1

/-- **Deviation of a far factor from `1`.**  For `1 ≤ n ≤ K < k`, a pair with `|s - a_k| ≤ A k^{-4/3}` and
`|w| ≤ A k^{-1/3}` has factor `((a_n - s)² + w²)/(a_n - a_k)²` within `C / k²` of `1`. -/
lemma factor_dev {K n : ℕ} (hn : 1 ≤ n) (hnK : n ≤ K) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, K < k → ∀ s w : ℝ, |s - airyZero k| ≤ A * (k : ℝ) ^ (-(4 / 3 : ℝ)) →
      |w| ≤ A * (k : ℝ) ^ (-(1 / 3 : ℝ)) →
      |((airyZero n - s) ^ 2 + w ^ 2) / (airyZero n - airyZero k) ^ 2 - 1| ≤ C / (k : ℝ) ^ 2 := by
  set c : ℝ := 1.8 / ((K : ℝ) + 1) with hc
  have hc0 : 0 < c := by positivity
  refine ⟨2 * A / c + 2 * A ^ 2 / c ^ 2, by positivity, fun k hk s w hs hw => ?_⟩
  have hk1 : 1 ≤ k := by omega
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
  -- lower bound for the distance
  have hD : c * r ^ 2 ≤ |airyZero n - airyZero k| := by
    have hsep := airyZero_abs_sub_ge (k := k) (n := n) hk1 hn (by omega)
    rw [max_eq_right (by omega : n ≤ k)] at hsep
    have hKk : (K : ℝ) + 1 ≤ k := by exact_mod_cast hk
    have hnK' : (n : ℝ) ≤ K := by exact_mod_cast hnK
    have hkn : (k : ℝ) - n ≥ (k : ℝ) / ((K : ℝ) + 1) := by
      rw [ge_iff_le, div_le_iff₀ (by positivity)]
      nlinarith
    rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - n)] at hsep
    have hkr : (k : ℝ) ^ (-(1 / 3 : ℝ)) = r⁻¹ := e13
    rw [hkr] at hsep
    refine le_trans ?_ hsep
    have : c * r ^ 2 = 1.8 * ((k : ℝ) / ((K : ℝ) + 1)) * r⁻¹ := by
      rw [hc, ← hr3]; field_simp
    rw [this]
    have h18 : (0 : ℝ) ≤ 1.8 * r⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hkn h18]
  set D : ℝ := |airyZero n - airyZero k| with hDdef
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD
  have hD2 : (airyZero n - airyZero k) ^ 2 = D ^ 2 := (sq_abs _).symm
  set t : ℝ := airyZero k - s with ht
  have htr : |t| * r ^ 4 ≤ A := by
    have h1 : |t| ≤ A * (r ^ 4)⁻¹ := by rw [ht, abs_sub_comm]; exact hs
    have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ r ^ 4)
    rwa [mul_assoc, inv_mul_cancel₀ (by positivity), mul_one] at this
  have hwr : |w| * r ≤ A := by
    have := mul_le_mul_of_nonneg_right hw hr0.le
    rwa [mul_assoc, inv_mul_cancel₀ hr0.ne', mul_one] at this
  have hnum : (airyZero n - s) ^ 2 + w ^ 2 - D ^ 2 = 2 * (airyZero n - airyZero k) * t + t ^ 2 + w ^ 2 := by
    rw [← hD2, ht]; ring
  have hlhs : ((airyZero n - s) ^ 2 + w ^ 2) / (airyZero n - airyZero k) ^ 2 - 1 =
      (2 * (airyZero n - airyZero k) * t + t ^ 2 + w ^ 2) / D ^ 2 := by
    rw [hD2, ← hnum]; field_simp
  rw [hlhs, abs_div, abs_of_pos (by positivity : 0 < D ^ 2)]
  have habs : |2 * (airyZero n - airyZero k) * t + t ^ 2 + w ^ 2| ≤ 2 * D * |t| + |t| ^ 2 + |w| ^ 2 := by
    calc |2 * (airyZero n - airyZero k) * t + t ^ 2 + w ^ 2|
        ≤ |2 * (airyZero n - airyZero k) * t| + |t ^ 2| + |w ^ 2| := abs_add_three _ _ _
      _ = 2 * D * |t| + |t| ^ 2 + |w| ^ 2 := by
          rw [abs_mul, abs_mul, abs_two, abs_pow, abs_pow]
  have hk2 : (k : ℝ) ^ 2 = r ^ 6 := by rw [← hr3]; ring
  rw [hk2, div_le_div_iff₀ (by positivity) (by positivity)]
  have hr2D : r ^ 2 ≤ D / c := by rw [le_div_iff₀ hc0]; linarith
  have hc2 : c ^ 2 * r ^ 4 ≤ D ^ 2 := by
    have : c * r ^ 2 ≤ D := hD
    nlinarith [mul_pos hc0 (by positivity : (0 : ℝ) < r ^ 2)]
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
    have hc2' : c ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hc0.le hcD 2
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
  calc |2 * (airyZero n - airyZero k) * t + t ^ 2 + w ^ 2| * r ^ 6
      ≤ (2 * D * |t| + |t| ^ 2 + |w| ^ 2) * r ^ 6 := by gcongr
    _ = 2 * D * |t| * r ^ 6 + |t| ^ 2 * r ^ 6 + |w| ^ 2 * r ^ 6 := by ring
    _ ≤ (2 * A / c) * D ^ 2 + (A ^ 2 / c ^ 2) * D ^ 2 + (A ^ 2 / c ^ 2) * D ^ 2 := by linarith
    _ = (2 * A / c + 2 * A ^ 2 / c ^ 2) * D ^ 2 := by ring

end FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum
