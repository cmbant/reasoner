module

public import FormalResearch.Special.AiryPositive

/-!
# `Ai` is positive on `[-1, 0]`, with an explicit lower bound

`airyAi_ge_on_Icc`: for `x ∈ [-1, 0]`, `Ai(x) ≥ Ai(0) cos x ≥ Ai(0)(1 - x²/2)`; in particular `Ai > 0`
on `[-1, ∞)` (`airyAi_pos_of_neg_one_le`).  The first zero of `Ai` is `≈ -2.338`; this file does not
locate it (it is located in `(-2.35, -2.33)` by `airy_exists_zero_first` and `airyZero_one` in `AiryFirstZeros`,
`AiryZeroOrder`), it only gets past `x = -1` by a Sturm-type argument using only `Ai(0) > 0`, `Ai'(0) < 0`
(`airyAi_pos`, `airyAi'_neg`) and `Ai'' = x Ai`:

with `H(x) = Ai'(x) cos x + Ai(x) sin x` one has `H' = (1 + x) cos x · Ai`, so `H' ≥ 0` on `[-1, 0]` as long
as `Ai ≥ 0`, hence `H ≤ H(0) = Ai'(0) < 0` there, i.e. `(Ai / cos)' = H / cos² < 0`, so
`Ai(x) / cos x ≥ Ai(0)`.  A continuity argument at the zero of `Ai` nearest to `0` in `[-1, 0]`
(if there were one) gives the contradiction.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.Special

private noncomputable def sturmH (x : ℝ) : ℝ := airyAi' x * Real.cos x + airyAi x * Real.sin x

private lemma hasDerivAt_sturmH (x : ℝ) :
    HasDerivAt sturmH ((1 + x) * airyAi x * Real.cos x) x := by
  have h1 := (hasDerivAt_airyAi' x).mul (Real.hasDerivAt_cos x)
  have h2 := (hasDerivAt_airyAi x).mul (Real.hasDerivAt_sin x)
  convert h1.add h2 using 1
  · ext y; rfl
  · ring

private lemma cos_pos_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) : 0 < Real.cos x := by
  apply Real.cos_pos_of_mem_Ioo
  have := Real.pi_gt_three
  rw [abs_le] at hx
  constructor <;> linarith

/-- If `Ai ≥ 0` on `[m, 0]` with `-1 ≤ m ≤ 0`, then `Ai(m) ≥ Ai(0) cos m`. -/
private lemma airyAi_ge_of_nonneg {m : ℝ} (hm1 : -1 ≤ m) (hm0 : m ≤ 0)
    (hpos : ∀ x ∈ Icc m 0, 0 ≤ airyAi x) : airyAi 0 * Real.cos m ≤ airyAi m := by
  have hA := airyAi'_neg (le_refl (0 : ℝ))
  have hAi0 := airyAi_pos (le_refl (0 : ℝ))
  have habs : ∀ x ∈ Icc m 0, |x| ≤ 1 := fun x hx => by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  -- `H ≤ H 0 = Ai'(0)` on `[m, 0]`
  have hH : ∀ x ∈ Icc m 0, sturmH x ≤ airyAi' 0 := by
    intro x hx
    have hmono : MonotoneOn sturmH (Icc m 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc m 0)
        (fun y _ => (hasDerivAt_sturmH y).continuousAt.continuousWithinAt)
        (fun y _ => (hasDerivAt_sturmH y).differentiableAt.differentiableWithinAt) ?_
      intro y hy
      rw [interior_Icc] at hy
      rw [(hasDerivAt_sturmH y).deriv]
      have hy1 : 0 ≤ 1 + y := by linarith [hy.1]
      have hc := cos_pos_of_abs_le_one (habs y (Ioo_subset_Icc_self hy))
      have := hpos y (Ioo_subset_Icc_self hy)
      positivity
    have := hmono hx ⟨hm0, le_refl 0⟩ hx.2
    simpa [sturmH] using this
  -- `K = Ai / cos` is antitone on `[m, 0]`
  have hK : AntitoneOn (fun x => airyAi x / Real.cos x) (Icc m 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc m 0) ?_ ?_ ?_
    · refine fun y hy => ContinuousAt.continuousWithinAt ?_
      exact ((hasDerivAt_airyAi y).div (Real.hasDerivAt_cos y)
        (cos_pos_of_abs_le_one (habs y hy)).ne').continuousAt
    · intro y hy
      rw [interior_Icc] at hy
      exact ((hasDerivAt_airyAi y).div (Real.hasDerivAt_cos y)
        (cos_pos_of_abs_le_one (habs y (Ioo_subset_Icc_self hy))).ne').differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hyI := Ioo_subset_Icc_self hy
      have hc := cos_pos_of_abs_le_one (habs y hyI)
      have hd := (hasDerivAt_airyAi y).div (Real.hasDerivAt_cos y) hc.ne'
      have hd' : HasDerivAt (fun x => airyAi x / Real.cos x)
          ((airyAi' y * Real.cos y - airyAi y * -Real.sin y) / Real.cos y ^ 2) y := hd
      rw [hd'.deriv]
      have : airyAi' y * Real.cos y - airyAi y * -Real.sin y = sturmH y := by
        simp [sturmH]
      rw [this]
      exact div_nonpos_of_nonpos_of_nonneg ((hH y hyI).trans hA.le) (by positivity)
  have := hK ⟨le_refl m, hm0⟩ ⟨hm0, le_refl 0⟩ hm0
  simp only [Real.cos_zero, div_one] at this
  have hc := cos_pos_of_abs_le_one (habs m ⟨le_refl m, hm0⟩)
  rw [le_div_iff₀ hc] at this
  linarith

/-- `Ai > 0` on `[-1, 0]`. -/
theorem airyAi_pos_Icc {x : ℝ} (hx1 : -1 ≤ x) (hx0 : x ≤ 0) : 0 < airyAi x := by
  have hAi0 := airyAi_pos (le_refl (0 : ℝ))
  by_contra hcon
  rw [not_lt] at hcon
  -- the set of points of `[-1,0]` where `Ai ≤ 0` is nonempty and compact
  set S : Set ℝ := Icc (-1) 0 ∩ {y | airyAi y ≤ 0} with hS
  have hSc : IsCompact S :=
    isCompact_Icc.inter_right (isClosed_le differentiable_airyAi.continuous continuous_const)
  have hSne : S.Nonempty := ⟨x, ⟨hx1, hx0⟩, hcon⟩
  obtain ⟨m, hmS, hmmax⟩ := hSc.exists_isMaxOn hSne continuous_id.continuousOn
  have hmax : ∀ y ∈ S, y ≤ m := fun y hy => by
    simpa using isMaxOn_iff.mp hmmax y hy
  have hm1 : -1 ≤ m := hmS.1.1
  have hm0 : m ≤ 0 := hmS.1.2
  have hAm : airyAi m ≤ 0 := hmS.2
  have hmlt : m < 0 := by
    rcases hm0.lt_or_eq with h | h
    · exact h
    · rw [h] at hAm; exact absurd hAm (not_le.mpr hAi0)
  -- `Ai ≥ 0` on `[m, 0]`
  have hpos : ∀ y ∈ Icc m 0, 0 ≤ airyAi y := by
    intro y hy
    rcases hy.1.lt_or_eq with h | h
    · by_contra hneg
      rw [not_le] at hneg
      have hyS : y ∈ S := ⟨⟨by linarith [hy.1], hy.2⟩, hneg.le⟩
      linarith [hmax y hyS]
    · rw [← h]
      by_contra hneg
      rw [not_le] at hneg
      have hcont := differentiable_airyAi.continuous.continuousAt (x := m)
      have hev : ∀ᶠ t in 𝓝 m, airyAi t < 0 := hcont.eventually (gt_mem_nhds hneg)
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
      set t := min (m + ε / 2) 0 with ht
      have ht1 : m < t := lt_min (by linarith) hmlt
      have htS : t ∈ S := ⟨⟨by linarith, min_le_right _ _⟩, (hball (by
          rw [Real.dist_eq, abs_lt]; constructor <;> linarith [min_le_left (m + ε / 2) 0])).le⟩
      linarith [hmax t htS]
  have hge := airyAi_ge_of_nonneg hm1 hm0 hpos
  have hcm : 0 < Real.cos m := cos_pos_of_abs_le_one (by rw [abs_le]; constructor <;> linarith)
  have : 0 < airyAi 0 * Real.cos m := mul_pos hAi0 hcm
  linarith

/-- **`Ai ≥ Ai(0) cos x` on `[-1, 0]`.** -/
theorem airyAi_ge_on_Icc {x : ℝ} (hx1 : -1 ≤ x) (hx0 : x ≤ 0) :
    airyAi 0 * Real.cos x ≤ airyAi x :=
  airyAi_ge_of_nonneg hx1 hx0 fun y hy => (airyAi_pos_Icc (by linarith [hy.1]) hy.2).le

/-- **`Ai > 0` on `[-1, ∞)`.** -/
theorem airyAi_pos_of_neg_one_le {x : ℝ} (hx : -1 ≤ x) : 0 < airyAi x := by
  rcases le_or_gt x 0 with h | h
  · exact airyAi_pos_Icc hx h
  · exact airyAi_pos h.le

/-- info: 'FormalResearch.Special.airyAi_ge_on_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_ge_on_Icc

/-- info: 'FormalResearch.Special.airyAi_pos_of_neg_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_pos_of_neg_one_le

/-- info: 'FormalResearch.Special.airyAi_pos_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_pos_Icc

end FormalResearch.Special
