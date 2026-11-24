module

public import FormalResearch.ModularBootstrap.TwoLevel.A2StarCurve

/-!
# `A_2^*` is Lipschitz on compact subsets of `(-∞, A_opt)` (`soft_edge_two_level_stability.tex`, proof of `se:3.2`)

`A_2^*(A₁) = -c_* z_2(Ai'(u)/Ai(u))` with `u = -A₁/c_*` (`A2star_eq`), so the Lipschitz property is that of the
two maps `u ↦ m(u) = Ai'/Ai` on a compact subset of `(a₁, ∞)` and `c ↦ z_2(c)`, the inverse of `m` on `(a₂, a₁)`.

* `airyRatio_expand_gap_two`: `m' = -(Ai'² - x Ai²)/Ai² ≤ -δ` on the whole gap `(a₂, a₁)` with one `δ > 0`
  (`Ai'² - x Ai²` has a positive minimum and `Ai²` a maximum on `[a₂, a₁]`), hence `|m x - m y| ≥ δ |x - y|`;
* `airyClarkNode_two_lipschitz`: `|z_2(c) - z_2(c')| ≤ δ⁻¹ |c - c'|` for all real `c, c'`;
* `airyRatio_lipschitz_Icc`: `m` is Lipschitz on `[a, b]` for `a₁ < a`;
* `A2star_lipschitzOn`: `A_2^*` is Lipschitz on every compact `J ⊆ (-∞, A_opt)`.
-/

@[expose] public section

open Set Filter Topology

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special

/-- On the whole gap `G_2 = (a₂, a₁)` the ratio `m = Ai'/Ai` decreases at rate at least `δ > 0`. -/
lemma airyRatio_expand_gap_two :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ airyClarkGap 2, ∀ y ∈ airyClarkGap 2, x ≤ y →
      δ * (y - x) ≤ airyRatio x - airyRatio y := by
  have hKc : Continuous (fun x : ℝ => airyAi' x ^ 2 - x * airyAi x ^ 2) :=
    (continuous_airyAi'.pow 2).sub (continuous_id.mul (continuous_airyAi.pow 2))
  have hlt : airyZero 2 ≤ airyZero 1 := (airyZero_lt_of_lt (n := 1) (m := 2) le_rfl (by norm_num)).le
  have hne : (Icc (airyZero 2) (airyZero 1)).Nonempty := ⟨airyZero 2, le_rfl, hlt⟩
  obtain ⟨x0, hx0, hmin⟩ := isCompact_Icc.exists_isMinOn hne hKc.continuousOn
  obtain ⟨x1, hx1, hmax⟩ := isCompact_Icc.exists_isMaxOn hne (continuous_airyAi.pow 2).continuousOn
  set κ : ℝ := airyAi' x0 ^ 2 - x0 * airyAi x0 ^ 2 with hκ
  set M : ℝ := airyAi x1 ^ 2 with hM
  have hκpos : 0 < κ := airyKer_pos' x0
  have hM0 : 0 ≤ M := by positivity
  refine ⟨κ / (M + 1), by positivity, ?_⟩
  set δ : ℝ := κ / (M + 1) with hδ
  have hδpos : 0 < δ := by positivity
  have hgap : ∀ x ∈ airyClarkGap 2, x ∈ Icc (airyZero 2) (airyZero 1) := by
    intro x hx
    rw [mem_airyClarkGap] at hx
    exact ⟨hx.1.le, (hx.2.resolve_left (by norm_num)).le⟩
  have hder : ∀ x ∈ airyClarkGap 2, HasDerivAt (fun y => airyRatio y + δ * y)
      (-(airyAi' x ^ 2 - x * airyAi x ^ 2) / airyAi x ^ 2 + δ * 1) x := fun x hx =>
    (hasDerivAt_airyRatio (airyAi_ne_zero_of_mem_gap (by norm_num) hx)).add
      ((hasDerivAt_id x).const_mul δ)
  have hanti : AntitoneOn (fun y => airyRatio y + δ * y) (airyClarkGap 2) := by
    refine antitoneOn_of_deriv_nonpos (convex_airyClarkGap 2) ?_ ?_ ?_
    · intro x hx
      exact (hder x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [(isOpen_airyClarkGap 2).interior_eq] at hx
      exact (hder x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(isOpen_airyClarkGap 2).interior_eq] at hx
      rw [(hder x hx).deriv]
      have hAi := airyAi_ne_zero_of_mem_gap (n := 2) (by norm_num) hx
      have hApos : 0 < airyAi x ^ 2 := by positivity
      have hK : κ ≤ airyAi' x ^ 2 - x * airyAi x ^ 2 := hmin (hgap x hx)
      have hA2 : airyAi x ^ 2 ≤ M := hmax (hgap x hx)
      have : δ * airyAi x ^ 2 ≤ airyAi' x ^ 2 - x * airyAi x ^ 2 := by
        have h1 : δ * airyAi x ^ 2 ≤ δ * (M + 1) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hδpos.le
        have h2 : δ * (M + 1) = κ := by rw [hδ]; field_simp
        linarith
      have h3 : δ ≤ (airyAi' x ^ 2 - x * airyAi x ^ 2) / airyAi x ^ 2 := by
        rw [le_div_iff₀ hApos]; exact this
      have h4 : -(airyAi' x ^ 2 - x * airyAi x ^ 2) / airyAi x ^ 2 =
          -((airyAi' x ^ 2 - x * airyAi x ^ 2) / airyAi x ^ 2) := by ring
      rw [h4]
      linarith
  intro x hx y hy hxy
  have := hanti hx hy hxy
  simp only at this
  linarith

/-- `δ |x - y| ≤ |m x - m y|` on the gap `G_2`. -/
lemma airyRatio_expand_abs_gap_two :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ airyClarkGap 2, ∀ y ∈ airyClarkGap 2,
      δ * |x - y| ≤ |airyRatio x - airyRatio y| := by
  obtain ⟨δ, hδ, h⟩ := airyRatio_expand_gap_two
  refine ⟨δ, hδ, fun x hx y hy => ?_⟩
  rcases le_total x y with hxy | hxy
  · have := h x hx y hy hxy
    have hp : 0 ≤ δ * (y - x) := mul_nonneg hδ.le (by linarith)
    rw [abs_of_nonpos (by linarith : x - y ≤ 0), abs_of_nonneg (by linarith : 0 ≤ airyRatio x - airyRatio y)]
    linarith
  · have := h y hy x hx hxy
    have hp : 0 ≤ δ * (x - y) := mul_nonneg hδ.le (by linarith)
    rw [abs_of_nonneg (by linarith : 0 ≤ x - y), abs_of_nonpos (by linarith : airyRatio x - airyRatio y ≤ 0)]
    linarith

/-- **The second Clark node is Lipschitz in the label**: `|z_2(c) - z_2(c')| ≤ δ⁻¹ |c - c'|` for all `c, c'`. -/
theorem airyClarkNode_two_lipschitz :
    ∃ L : ℝ, 0 < L ∧ ∀ c c' : ℝ, |airyClarkNode c 2 - airyClarkNode c' 2| ≤ L * |c - c'| := by
  obtain ⟨δ, hδ, h⟩ := airyRatio_expand_abs_gap_two
  refine ⟨δ⁻¹, inv_pos.mpr hδ, fun c c' => ?_⟩
  have key := h _ (airyClarkNode_mem_gap (n := 2) (by norm_num) c) _
    (airyClarkNode_mem_gap (n := 2) (by norm_num) c')
  rw [airyRatio_airyClarkNode (by norm_num), airyRatio_airyClarkNode (by norm_num)] at key
  rw [inv_mul_eq_div, le_div_iff₀ hδ, mul_comm]
  exact key

/-- `m = Ai'/Ai` is Lipschitz on `[a, b]` whenever `a₁ < a`. -/
theorem airyRatio_lipschitz_Icc {a b : ℝ} (ha : airyZero 1 < a) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |airyRatio x - airyRatio y| ≤ L * |x - y| := by
  have hAi : ∀ x ∈ Icc a b, airyAi x ≠ 0 := fun x hx =>
    airyAi_ne_zero_of_mem_gap (n := 1) le_rfl (by rw [airyClarkGap_one]; exact ha.trans_le hx.1)
  have hcont : ContinuousOn (fun x : ℝ => -(airyAi' x ^ 2 - x * airyAi x ^ 2) / airyAi x ^ 2) (Icc a b) := by
    refine ContinuousOn.div ?_ (continuous_airyAi.pow 2).continuousOn (fun x hx => pow_ne_zero 2 (hAi x hx))
    exact ((continuous_airyAi'.pow 2).sub (continuous_id.mul (continuous_airyAi.pow 2))).neg.continuousOn
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun x hx y hy => ?_⟩
  have := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := airyRatio) (f' := fun x => -(airyAi' x ^ 2 - x * airyAi x ^ 2) / airyAi x ^ 2)
    (C := max C 0) (fun x hx => (hasDerivAt_airyRatio (hAi x hx)).hasDerivWithinAt)
    (fun x hx => (hC x hx).trans (le_max_left _ _)) hy hx
  simpa [Real.norm_eq_abs, abs_sub_comm] using this

/-- **`A_2^*` is Lipschitz on compact subsets of `(-∞, A_opt)`** (`soft_edge_two_level_stability.tex`,
proof of `se:3.2`: the constant `L_J`, there written as `max_J (A_2^*)'`). -/
theorem A2star_lipschitzOn {J : Set ℝ} (hJ : IsCompact J) (hJsub : J ⊆ Iio Aopt) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ A ∈ J, ∀ B ∈ J, |A2star A - A2star B| ≤ L * |A - B| := by
  rcases J.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, le_rfl, by simp⟩
  have hc := cStar_pos
  obtain ⟨hi, hhiJ, hhi⟩ := hJ.exists_isMaxOn hne continuous_id.continuousOn
  obtain ⟨lo, hloJ, hlo⟩ := hJ.exists_isMinOn hne continuous_id.continuousOn
  have hhiA : hi < Aopt := hJsub hhiJ
  obtain ⟨Lm, hLm0, hLm⟩ := airyRatio_lipschitz_Icc (a := -hi / cStar) (b := -lo / cStar)
    (mem_gap_one_of_lt_Aopt hhiA)
  obtain ⟨Lz, hLz, hz⟩ := airyClarkNode_two_lipschitz
  have hmem : ∀ A ∈ J, -A / cStar ∈ Icc (-hi / cStar) (-lo / cStar) := fun A hA =>
    ⟨div_le_div_of_nonneg_right (by have h : A ≤ hi := hhi hA; linarith) hc.le,
     div_le_div_of_nonneg_right (by have h : lo ≤ A := hlo hA; linarith) hc.le⟩
  refine ⟨Lz * Lm, by positivity, fun A hA B hB => ?_⟩
  rw [A2star_eq (hJsub hA), A2star_eq (hJsub hB)]
  have h1 := hz (airyRatio (-A / cStar)) (airyRatio (-B / cStar))
  have h2 := hLm _ (hmem A hA) _ (hmem B hB)
  have h3 : |-A / cStar - -B / cStar| = |A - B| / cStar := by
    have : -A / cStar - -B / cStar = -(A - B) / cStar := by ring
    rw [this, abs_div, abs_neg, abs_of_pos hc]
  have h4 : |-(cStar * airyClarkNode (airyRatio (-A / cStar)) 2) -
      -(cStar * airyClarkNode (airyRatio (-B / cStar)) 2)| =
      cStar * |airyClarkNode (airyRatio (-A / cStar)) 2 - airyClarkNode (airyRatio (-B / cStar)) 2| := by
    have : -(cStar * airyClarkNode (airyRatio (-A / cStar)) 2) -
        -(cStar * airyClarkNode (airyRatio (-B / cStar)) 2) =
        -(cStar * (airyClarkNode (airyRatio (-A / cStar)) 2 -
          airyClarkNode (airyRatio (-B / cStar)) 2)) := by ring
    rw [this, abs_neg, abs_mul, abs_of_pos hc]
  rw [h4]
  rw [h3] at h2
  calc cStar * |airyClarkNode (airyRatio (-A / cStar)) 2 - airyClarkNode (airyRatio (-B / cStar)) 2|
      ≤ cStar * (Lz * (Lm * (|A - B| / cStar))) := by
        gcongr
        exact h1.trans (by gcongr)
    _ = Lz * Lm * |A - B| := by field_simp

end FormalResearch.ModularBootstrap.TwoLevel

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.A2star_lipschitzOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.TwoLevel.A2star_lipschitzOn
