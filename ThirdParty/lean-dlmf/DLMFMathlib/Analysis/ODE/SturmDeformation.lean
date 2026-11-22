/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import DLMFMathlib.Topology.Order.ZeroEnumeration

/-!
# Zero counts in families of functions

Let `y(t, x)` be a family of real functions of `x`, depending on a parameter `t` in a
topological space, such that `y` and `∂ₓ y` are jointly continuous and all zeros in `x` are
simple. Then the number of zeros of `y(t, ·)` in a compact interval `[a, b]` is a locally
constant function of `t`, as long as `y(t, a) ≠ 0 ≠ y(t, b)`: zeros cannot appear or disappear
in the interior. No differential equation is used; the argument combines the intermediate value
theorem near each zero with a compactness argument away from the zeros.

This is the deformation step in Sturm's oscillation theory: an exact zero count at one parameter
value (for instance a polynomial case) propagates along a connected parameter set on which no
zero crosses the ends.

## Main results

* `ODE.SturmDeformation.finite`: simple zeros in a compact interval are finite in number.
* `ODE.SturmDeformation.eventually_ncard_eq`: local constancy of the zero count in `[a, b]`.
* `ODE.SturmDeformation.ncard_eq_of_isPreconnected`: constancy along a preconnected parameter set.
* `ODE.SturmDeformation.ncard_Ici_eq_of_isPreconnected`: the same for `[a, ∞)` with a zero-free
  region `[b, ∞)` that is uniform in the parameter.
-/

@[expose] public section

open Set Filter Topology

namespace ODE

variable {T : Type*} [TopologicalSpace T] {Y Y' : T → ℝ → ℝ} {Λ : Set T} {U : Set ℝ}

/-- Simple zeros of a differentiable function in a compact interval are finite in number. -/
theorem SturmDeformation.finite {f f' : ℝ → ℝ} {a b : ℝ} (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hs : ∀ x ∈ Icc a b, f x = 0 → f' x ≠ 0) : {x | x ∈ Icc a b ∧ f x = 0}.Finite := by
  have hc : ContinuousOn f (Icc a b) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hK : IsCompact {x | x ∈ Icc a b ∧ f x = 0} :=
    isCompact_Icc.of_isClosed_subset
        (hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton)
      fun x hx => hx.1
  by_contra hinf
  obtain ⟨z, hz, hne⟩ := exists_nhds_ne_inf_principal_neBot hK hinf
  have hev := (hd z hz.1).eventually_ne (c := 0) (hs z hz.1 hz.2)
  have : 𝓝[≠] z ⊓ 𝓟 {x | x ∈ Icc a b ∧ f x = 0} = ⊥ := by
    rw [inf_principal_eq_bot]
    filter_upwards [hev] with x hx hmem
    exact hx hmem.2
  exact hne.ne this

/-- Continuity of `t ↦ y(t, x)` and joint continuity at interior points. -/
theorem SturmDeformation.continuousAt (hΛ : IsOpen Λ) (hU : IsOpen U)
    (hc : ContinuousOn (Function.uncurry Y) (Λ ×ˢ U)) {t : T} {x : ℝ} (ht : t ∈ Λ) (hx : x ∈ U) :
    ContinuousAt (Function.uncurry Y) (t, x) :=
  hc.continuousAt ((hΛ.prod hU).mem_nhds ⟨ht, hx⟩)

/-- One zero, positive slope: for every small `δ`, nearby members of the family have exactly one
zero in `(z - δ, z + δ)`. -/
theorem SturmDeformation.local_pos (hΛ : IsOpen Λ) (hU : IsOpen U)
    (hcY : ContinuousOn (Function.uncurry Y) (Λ ×ˢ U))
    (hcY' : ContinuousOn (Function.uncurry Y') (Λ ×ˢ U))
    (hd : ∀ t ∈ Λ, ∀ x ∈ U, HasDerivAt (Y t) (Y' t x) x) {t₀ : T} {z : ℝ} (ht₀ : t₀ ∈ Λ)
    (hz : z ∈ U) (hz0 : Y t₀ z = 0) (hpos : 0 < Y' t₀ z) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ᶠ t in 𝓝 t₀, ∃! x, x ∈ Ioo (z - δ) (z + δ) ∧ Y t x = 0 := by
  have hmem : Λ ×ˢ U ∈ 𝓝 (t₀, z) := (hΛ.prod hU).mem_nhds ⟨ht₀, hz⟩
  have hev : ∀ᶠ p in 𝓝 (t₀, z), p.1 ∈ Λ ∧ p.2 ∈ U ∧ 0 < Y' p.1 p.2 := by
    filter_upwards [hmem,
        (SturmDeformation.continuousAt hΛ hU hcY' ht₀ hz).eventually (lt_mem_nhds hpos)]
      with p hp hp'
    exact ⟨hp.1, hp.2, hp'⟩
  rw [nhds_prod_eq] at hev
  obtain ⟨u, hu, v, hv, huv⟩ := mem_prod_iff.mp hev
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hv
  refine ⟨r / 2, by positivity, fun δ hδ hδr => ?_⟩
  have hI : ∀ x ∈ Icc (z - δ) (z + δ), x ∈ v := fun x hx => hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2])
  have hgood : ∀ t ∈ u, ∀ x ∈ Icc (z - δ) (z + δ), t ∈ Λ ∧ x ∈ U ∧ 0 < Y' t x :=
    fun t ht x hx => huv (show (t, x) ∈ u ×ˢ v from ⟨ht, hI x hx⟩)
  have hmono : ∀ t ∈ u, StrictMonoOn (Y t) (Icc (z - δ) (z + δ)) := by
    intro t ht
    refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
      (fun x hx => ((hd t (hgood t ht x hx).1 x
          (hgood t ht x hx).2.1).continuousAt).continuousWithinAt)
      (fun x hx => (hd t (hgood t ht x (interior_subset hx)).1 x
        (hgood t ht x (interior_subset hx)).2.1).hasDerivWithinAt)
      fun x hx => (hgood t ht x (interior_subset hx)).2.2
  have hm : z - δ ∈ Icc (z - δ) (z + δ) := ⟨le_rfl, by linarith⟩
  have hp : z + δ ∈ Icc (z - δ) (z + δ) := ⟨by linarith, le_rfl⟩
  have hz' : z ∈ Icc (z - δ) (z + δ) := ⟨by linarith, by linarith⟩
  have hu0 : t₀ ∈ u := mem_of_mem_nhds hu
  have h1 : Y t₀ (z - δ) < 0 := hz0 ▸ hmono t₀ hu0 hm hz' (by linarith)
  have h2 : 0 < Y t₀ (z + δ) := hz0 ▸ hmono t₀ hu0 hz' hp (by linarith)
  have hcm : ContinuousAt (fun t => Y t (z - δ)) t₀ :=
    ContinuousAt.comp (g := Function.uncurry Y) (f := fun t => (t, z - δ))
      (SturmDeformation.continuousAt hΛ hU hcY ht₀ (hgood t₀ hu0 _ hm).2.1)
      (continuousAt_id.prodMk continuousAt_const)
  have hcp : ContinuousAt (fun t => Y t (z + δ)) t₀ :=
    ContinuousAt.comp (g := Function.uncurry Y) (f := fun t => (t, z + δ))
      (SturmDeformation.continuousAt hΛ hU hcY ht₀ (hgood t₀ hu0 _ hp).2.1)
      (continuousAt_id.prodMk continuousAt_const)
  filter_upwards [hu, hcm.eventually (gt_mem_nhds h1), hcp.eventually (lt_mem_nhds h2)]
    with t ht htm htp
  exact zcount_existsUnique_zero (by linarith)
    (fun x hx => (hd t (hgood t ht x hx).1 x (hgood t ht x hx).2.1).continuousAt.continuousWithinAt)
    (hmono t ht) htm htp

/-- One simple zero: for every small `δ`, nearby members of the family have exactly one zero in
`(z - δ, z + δ)`. -/
theorem SturmDeformation.local (hΛ : IsOpen Λ) (hU : IsOpen U)
    (hcY : ContinuousOn (Function.uncurry Y) (Λ ×ˢ U))
    (hcY' : ContinuousOn (Function.uncurry Y') (Λ ×ˢ U))
    (hd : ∀ t ∈ Λ, ∀ x ∈ U, HasDerivAt (Y t) (Y' t x) x) {t₀ : T} {z : ℝ} (ht₀ : t₀ ∈ Λ)
    (hz : z ∈ U) (hz0 : Y t₀ z = 0) (hne : Y' t₀ z ≠ 0) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ᶠ t in 𝓝 t₀, ∃! x, x ∈ Ioo (z - δ) (z + δ) ∧ Y t x = 0 := by
  rcases hne.lt_or_gt with hneg | hpos
  · obtain ⟨δ₀, hδ₀, h⟩ :=
        SturmDeformation.local_pos (Y := fun t x => -Y t x) (Y' := fun t x => -Y' t x)
      hΛ hU hcY.neg hcY'.neg -- PATCH: v4.35 simp normal form differs; the terms are defeq, so pass them directly
      (fun t ht x hx => (hd t ht x hx).neg) ht₀ hz (by simp [hz0]) (by linarith)
    refine ⟨δ₀, hδ₀, fun δ hδ hδ₀' => (h δ hδ hδ₀').mono fun t ht => ?_⟩
    simpa only [neg_eq_zero] using ht
  · exact SturmDeformation.local_pos hΛ hU hcY hcY' hd ht₀ hz hz0 hpos

/-- **Local constancy of the zero count.** Let `y` and `∂ₓ y` be jointly continuous on `Λ × U`
(both open), with simple zeros, and let `[a, b] ⊆ U`. If `y(t₀, a) ≠ 0` and `y(t₀, b) ≠ 0`, then
for `t` near `t₀` the number of zeros of `y(t, ·)` in `[a, b]` equals that of `y(t₀, ·)`. -/
theorem SturmDeformation.eventually_ncard_eq (hΛ : IsOpen Λ) (hU : IsOpen U) {a b : ℝ}
    (hab : Icc a b ⊆ U) (hcY : ContinuousOn (Function.uncurry Y) (Λ ×ˢ U))
    (hcY' : ContinuousOn (Function.uncurry Y') (Λ ×ˢ U))
    (hd : ∀ t ∈ Λ, ∀ x ∈ U, HasDerivAt (Y t) (Y' t x) x)
    (hs : ∀ t ∈ Λ, ∀ x ∈ U, Y t x = 0 → Y' t x ≠ 0) {t₀ : T} (ht₀ : t₀ ∈ Λ)
    (ha : Y t₀ a ≠ 0) (hb : Y t₀ b ≠ 0) :
    ∀ᶠ t in 𝓝 t₀, {x | x ∈ Icc a b ∧ Y t x = 0}.ncard = {x | x ∈ Icc a b ∧ Y t₀ x = 0}.ncard := by
  set Z := {x | x ∈ Icc a b ∧ Y t₀ x = 0} with hZ
  have hZf : Z.Finite := SturmDeformation.finite (fun x hx => hd t₀ ht₀ x (hab hx))
    fun x hx => hs t₀ ht₀ x (hab hx)
  have hZo : ∀ z ∈ Z, z ∈ Ioo a b := fun z hz =>
    ⟨lt_of_le_of_ne hz.1.1 fun h => ha (h ▸ hz.2), lt_of_le_of_ne hz.1.2 fun h => hb (h ▸ hz.2)⟩
  -- a radius for each zero: isolation from the other zeros, room inside `(a, b)`, and the local
  -- one-zero property
  have hrad : ∀ z ∈ Z, ∃ δ > 0, Icc (z - δ) (z + δ) ⊆ Ioo a b ∧
      (∀ w ∈ Z, w ≠ z → 2 * δ < |w - z|) ∧
      ∀ᶠ t in 𝓝 t₀, ∃! x, x ∈ Ioo (z - δ) (z + δ) ∧ Y t x = 0 := by
    intro z hz
    obtain ⟨δ₀, hδ₀, hloc⟩ := SturmDeformation.local hΛ hU hcY hcY' hd ht₀ (hab hz.1) hz.2
      (hs t₀ ht₀ z (hab hz.1) hz.2)
    have hclosed : IsClosed (Z \ {z}) := (hZf.sdiff).isClosed
    have hnot : z ∉ Z \ {z} := fun h => h.2 rfl
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl z hnot
    obtain ⟨hza, hzb⟩ := hZo z hz
    set δ := min (min (δ₀) (r / 3)) (min ((z - a) / 2) ((b - z) / 2))
    have hδ : 0 < δ := lt_min (lt_min hδ₀ (by positivity)) (lt_min (by linarith) (by linarith))
    have hδ1 : δ ≤ δ₀ := (min_le_left _ _).trans (min_le_left _ _)
    have hδ2 : δ ≤ r / 3 := (min_le_left _ _).trans (min_le_right _ _)
    have hδ3 : δ ≤ (z - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hδ4 : δ ≤ (b - z) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨δ, hδ, fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩, fun w hw hwz => ?_,
      hloc δ hδ hδ1⟩
    by_contra hle
    push Not at hle
    have : w ∈ Metric.ball z r := by
      rw [Metric.mem_ball, Real.dist_eq]; linarith
    exact hball this ⟨hw, hwz⟩
  choose! δ hδpos hδsub hδsep hδev using hrad
  -- away from the small intervals, `y(t₀, ·)` does not vanish
  set K := Icc a b \ ⋃ z ∈ Z, Ioo (z - δ z) (z + δ z) with hK
  have hKc : IsCompact K := isCompact_Icc.diff (isOpen_biUnion fun z _ => isOpen_Ioo)
  have hK0 : ∀ x ∈ K, Y t₀ x ≠ 0 := by
    intro x hx h0
    refine hx.2 (mem_iUnion₂.mpr ⟨x, ⟨hx.1, h0⟩, ?_⟩)
    have := hδpos x ⟨hx.1, h0⟩
    exact ⟨by linarith, by linarith⟩
  have hKev : ∀ᶠ t in 𝓝 t₀, ∀ x ∈ K, Y t x ≠ 0 := by
    refine hKc.eventually_forall_of_forall_eventually fun x hx => ?_
    have hc := SturmDeformation.continuousAt hΛ hU hcY ht₀ (hab hx.1)
    exact hc.eventually (isOpen_ne.mem_nhds (hK0 x hx))
  filter_upwards [hKev, (hZf.eventually_all).mpr hδev] with t hKt hzt
  -- the bijection between the zeros of `y(t₀, ·)` and those of `y(t, ·)`
  have hdisj : ∀ z ∈ Z, ∀ w ∈ Z, ∀ x, x ∈ Ioo (z - δ z) (z + δ z) →
      x ∈ Ioo (w - δ w) (w + δ w) → z = w := by
    intro z hz w hw x hx hx'
    by_contra hne
    have h1 := hδsep z hz w hw (Ne.symm hne)
    have h2 := hδsep w hw z hz hne
    rw [abs_sub_comm] at h2
    have : |w - z| < δ z + δ w := by
      rw [abs_lt]; constructor <;> linarith [hx.1, hx.2, hx'.1, hx'.2]
    linarith
  symm
  refine Set.ncard_congr (fun z hz => (hzt z hz).exists.choose) (fun z hz => ?_) ?_ ?_
  · obtain ⟨hx, hx0⟩ := (hzt z hz).exists.choose_spec
    exact ⟨⟨(hδsub z hz (Ioo_subset_Icc_self hx)).1.le, (hδsub z hz (Ioo_subset_Icc_self hx)).2.le⟩,
      hx0⟩
  · intro z w hz hw h
    exact hdisj z hz w hw _ (hzt z hz).exists.choose_spec.1 (h ▸ (hzt w hw).exists.choose_spec.1)
  · rintro x ⟨hx, hx0⟩
    have hxK : x ∉ K := fun h => hKt x h hx0
    have hxU : x ∈ ⋃ z ∈ Z, Ioo (z - δ z) (z + δ z) := by
      by_contra h; exact hxK ⟨hx, h⟩
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp hxU
    exact ⟨z, hz, (hzt z hz).unique (hzt z hz).exists.choose_spec ⟨hxz, hx0⟩⟩

/-- **Constancy of the zero count along a preconnected parameter set** on which the ends of
`[a, b]` are never zeros. -/
theorem SturmDeformation.ncard_eq_of_isPreconnected (hΛ : IsOpen Λ) (hU : IsOpen U) {a b : ℝ}
    (hab : Icc a b ⊆ U) (hcY : ContinuousOn (Function.uncurry Y) (Λ ×ˢ U))
    (hcY' : ContinuousOn (Function.uncurry Y') (Λ ×ˢ U))
    (hd : ∀ t ∈ Λ, ∀ x ∈ U, HasDerivAt (Y t) (Y' t x) x)
    (hs : ∀ t ∈ Λ, ∀ x ∈ U, Y t x = 0 → Y' t x ≠ 0) {S : Set T} (hS : IsPreconnected S)
    (hSΛ : S ⊆ Λ) (hend : ∀ t ∈ S, Y t a ≠ 0 ∧ Y t b ≠ 0) {t₁ t₂ : T} (h₁ : t₁ ∈ S)
    (h₂ : t₂ ∈ S) :
    {x | x ∈ Icc a b ∧ Y t₁ x = 0}.ncard = {x | x ∈ Icc a b ∧ Y t₂ x = 0}.ncard := by
  refine hS.constant (f := fun t => {x | x ∈ Icc a b ∧ Y t x = 0}.ncard) (fun t ht => ?_) h₁ h₂
  refine ContinuousAt.continuousWithinAt ?_
  have := SturmDeformation.eventually_ncard_eq hΛ hU hab hcY hcY' hd hs (hSΛ ht) (hend t ht).1
    (hend t ht).2
  exact tendsto_nhds_of_eventually_eq this

/-- **Constancy of the zero count on `[a, ∞)`** along a preconnected parameter set, when `y(t, a)`
never vanishes and `[b, ∞)` is zero-free for every parameter in the set. -/
theorem SturmDeformation.ncard_Ici_eq_of_isPreconnected (hΛ : IsOpen Λ) (hU : IsOpen U) {a b : ℝ}
    (hab : Icc a b ⊆ U) (hcY : ContinuousOn (Function.uncurry Y) (Λ ×ˢ U))
    (hcY' : ContinuousOn (Function.uncurry Y') (Λ ×ˢ U))
    (hd : ∀ t ∈ Λ, ∀ x ∈ U, HasDerivAt (Y t) (Y' t x) x)
    (hs : ∀ t ∈ Λ, ∀ x ∈ U, Y t x = 0 → Y' t x ≠ 0) {S : Set T} (hS : IsPreconnected S)
    (hSΛ : S ⊆ Λ) (ha : ∀ t ∈ S, Y t a ≠ 0) (hfar : ∀ t ∈ S, ∀ x, b ≤ x → Y t x ≠ 0)
    {t₁ t₂ : T} (h₁ : t₁ ∈ S) (h₂ : t₂ ∈ S) :
    {x | x ∈ Ici a ∧ Y t₁ x = 0}.ncard = {x | x ∈ Ici a ∧ Y t₂ x = 0}.ncard := by
  have hset : ∀ t ∈ S, {x | x ∈ Ici a ∧ Y t x = 0} = {x | x ∈ Icc a b ∧ Y t x = 0} := by
    intro t ht
    ext x
    refine ⟨fun ⟨hx, hx0⟩ => ⟨⟨hx, ?_⟩, hx0⟩, fun ⟨hx, hx0⟩ => ⟨hx.1, hx0⟩⟩
    by_contra hlt
    exact hfar t ht x (not_le.mp hlt).le hx0
  rw [hset t₁ h₁, hset t₂ h₂]
  exact SturmDeformation.ncard_eq_of_isPreconnected hΛ hU hab hcY hcY' hd hs hS hSΛ
    (fun t ht => ⟨ha t ht, hfar t ht b le_rfl⟩) h₁ h₂

end ODE
