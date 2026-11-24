module

public import FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuumNode
public import FormalResearch.ModularBootstrap.TwoLevel.WindowOptimumLimit
public import FormalResearch.ModularBootstrap.TwoLevel.IdealApproxTail

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
open FormalResearch.ModularBootstrap.TwoLevel.IdealApprox

/-- Uniform WKB bounds: `|a_k - u_k^W| ≤ A k^{-4/3}` and `gap_k ≤ A k^{-1/3}`. -/
lemma exists_uniform_bound : ∃ A : ℝ, 0 < A ∧ ∀ k : ℕ, 1 ≤ k →
    |airyZero k - uWKB k| ≤ A * (k : ℝ) ^ (-(4 / 3 : ℝ)) ∧ gapWKB k ≤ A * (k : ℝ) ^ (-(1 / 3 : ℝ)) :=
  uniform_wkb_bound

/-- Sites of the design `negDesign`: `k ∈ [3, n+2]` at `z_k` (`k ≤ K`) or `a_k`, reference beyond. -/
noncomputable def siteSeq (α : ℝ) (K n : ℕ) (k : ℕ) : ℝ := idealSite (clarkNode α) K n k

/-- Half-widths of the design `negDesign`. -/
noncomputable def widthSeq (n : ℕ) (η : ℝ) (k : ℕ) : ℝ := idealWidth n η k

/-- The limit sites (`n = ∞`) of the designs; the limit widths are `0`. -/
noncomputable def siteLim (α : ℝ) (K : ℕ) (k : ℕ) : ℝ := idealLim (clarkNode α) K k

/-- The approximating design of Theorem 2.5, Step 1. -/
noncomputable def negDesign (α : ℝ) (K n : ℕ) (η q : ℝ) : TwoZeroDesign n where
  p := clarkNode α 1 - η
  q := q
  s := fun i => if (i : ℕ) + 3 ≤ K then clarkNode α ((i : ℕ) + 3) else airyZero ((i : ℕ) + 3)
  e := fun i => η * gapWKB ((i : ℕ) + 3)

lemma negDesign_site (α : ℝ) (K n : ℕ) (η q : ℝ) : (negDesign α K n η q).site = siteSeq α K n := by
  funext k
  unfold TwoZeroDesign.site siteSeq idealSite
  by_cases h : 3 ≤ k ∧ k ≤ n + 2
  · simp only [h, and_self, dite_true, ↓reduceIte, negDesign]
    rw [Nat.sub_add_cancel h.1]
  · simp only [h, dite_false, ↓reduceIte]

lemma negDesign_width (α : ℝ) (K n : ℕ) (η q : ℝ) : (negDesign α K n η q).width = widthSeq n η := by
  funext k
  unfold TwoZeroDesign.width widthSeq idealWidth
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
    AiryProdTailHypothesis 2 (siteSeq α K n) (widthSeq n η) :=
  tailHyp_ideal (clarkNode α) K n hη0 hη1 2

/-- Tail hypothesis for the limit data (zero widths). -/
lemma tailHyp_siteLim (α : ℝ) {K : ℕ} (hK : 3 ≤ K) : AiryProdTailHypothesis 2 (siteLim α K) (fun _ => 0) :=
  tailHyp_of_eventually_airy (M₀ := K) (fun _ hk => idealLim_eq_airy (clarkNode α) (by omega) hk)
    (fun _ _ => rfl) 2

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
  have e13 : (k : ℝ) ^ (-(1 / 3 : ℝ)) = (r)⁻¹ := by rw [Real.rpow_neg hk0.le]
  have hD : c * r ^ 2 ≤ |airyZero n - airyZero k| := by
    have hsep := airyZero_abs_sub_ge (k := k) (n := n) hk1 hn (by omega)
    rw [max_eq_right (by omega : n ≤ k)] at hsep
    have hKk : (K : ℝ) + 1 ≤ k := by exact_mod_cast hk
    have hnK' : (n : ℝ) ≤ K := by exact_mod_cast hnK
    have hkn : (k : ℝ) - n ≥ (k : ℝ) / ((K : ℝ) + 1) := by
      rw [ge_iff_le, div_le_iff₀ (by positivity)]
      nlinarith
    rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - n)] at hsep
    rw [e13] at hsep
    refine le_trans ?_ hsep
    have : c * r ^ 2 = 1.8 * ((k : ℝ) / ((K : ℝ) + 1)) * r⁻¹ := by
      rw [hc, ← hr3]; field_simp
    rw [this]
    have h18 : (0 : ℝ) ≤ 1.8 * r⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hkn h18]
  have key := factor_dev_core hk1 hA hc0 (u := (airyZero n : ℂ)) (s := s) (w := w)
    (by rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hD) hs hw
  have e : (((airyZero n : ℂ) - (s : ℂ)) ^ 2 + (w : ℂ) ^ 2) / ((airyZero n : ℂ) - (airyZero k : ℂ)) ^ 2 - 1 =
      ((((airyZero n - s) ^ 2 + w ^ 2) / (airyZero n - airyZero k) ^ 2 - 1 : ℝ) : ℂ) := by
    push_cast; rfl
  rw [e, Complex.norm_real, Real.norm_eq_abs] at key
  exact key

end FormalResearch.ModularBootstrap.TwoLevel.NegativeVacuum
