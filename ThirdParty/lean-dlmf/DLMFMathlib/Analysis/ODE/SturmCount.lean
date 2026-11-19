/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import DLMFMathlib.Analysis.ODE.SturmComparison

/-!
# Elementary zero counting for second-order equations

Sign and zero arguments for real solutions of second-order equations `y'' = F(x, y, y')`
that only use the value of `y''` at critical points of `y`. They apply equally to
homogeneous equations `y'' = q y` and to inhomogeneous ones such as the Scorer equation
`y'' = x y ± 1/π`.

## Main results

* `ODE.sturmCount_eventually_lt_right`, `ODE.sturmCount_eventually_lt_left`: a critical point
  with positive second derivative is a strict local minimum (from each side), for functions
  that are only once differentiable near the point and whose derivative is differentiable at
  the point.
* `ODE.sturmCount_not_isLocalMax`: such a point is not a local maximum.
* `ODE.sturmCount_nonpos_of_maxPrinciple`, `ODE.sturmCount_neg_of_maxPrinciple`: the
  maximum principle. If `y ≤ 0` (resp. `y < 0`) at the ends of `[a, b]` and `y'' > 0` at every
  interior critical point where `y > 0` (resp. `y ≥ 0`), then `y ≤ 0` (resp. `y < 0`) on
  `[a, b]`.
* `ODE.sturmCount_deriv_zero_unique`: if `y'' < 0` at every critical point in an open
  interval, there is at most one critical point there.
* `ODE.sturmCount_infinite_zeros_atBot`, `ODE.sturmCount_infinite_zeros_atTop`: a continuous
  function taking both signs arbitrarily far out has infinitely many zeros there
  (oscillation).
* `ODE.sturmCount_infinite_deriv_zeros`: by Rolle's theorem, infinitely many zeros of `y` in
  an interval give infinitely many zeros of `y'` there.
* `ODE.sturmCount_existsUnique_zero_between`, `ODE.sturmCount_zero_unique_of_wronskian`,
  `ODE.sturmCount_existsUnique_zero_right`, `ODE.sturmCount_existsUnique_zero_left`,
  `ODE.sturmCount_existsUnique_zero_of_signs`: separation of zeros by a Wronskian
  `p q' - q p' > 0`, with no differential equation assumed. Between consecutive zeros of `p`
  (or next to an end where `q / p` is unbounded) `q` has exactly one zero.
* `ODE.sturmCount_exists_pos_of_deriv_ge`, `ODE.sturmCount_exists_neg_of_deriv_ge`: a function
  whose derivative is at least `c / (b - y)` is unbounded above near `b` (logarithmic
  divergence), used for the ratio `q / p` near a singular endpoint.
* `ODE.sturmCount_ncard_of_partition`: exactly one zero in each cell of a partition
  `t₀ < ⋯ < t_m` and none at the interior points gives exactly `m` zeros.
-/

@[expose] public section

open Set Filter Topology

namespace ODE

variable {g g' g'' : ℝ → ℝ} {x₀ d : ℝ}

/-- If `g' x₀ = 0` and `g'` has positive derivative at `x₀`, then `g` increases strictly just to
the right of `x₀`. -/
theorem sturmCount_eventually_lt_right (hg : ∀ᶠ x in 𝓝 x₀, HasDerivAt g (g' x) x)
    (hg' : HasDerivAt g' d x₀) (h0 : g' x₀ = 0) (hd : 0 < d) :
    ∀ᶠ x in 𝓝[>] x₀, g x₀ < g x := by
  have hsl := hasDerivAt_iff_tendsto_slope.mp hg'
  have h1 : ∀ᶠ x in 𝓝[>] x₀, 0 < g' x := by
    have : ∀ᶠ x in 𝓝[≠] x₀, 0 < slope g' x₀ x := hsl.eventually (lt_mem_nhds hd)
    filter_upwards [nhdsGT_le_nhdsNE x₀ this, self_mem_nhdsWithin] with x hx hx'
    rw [slope_def_field, h0, sub_zero] at hx
    exact (div_pos_iff_of_pos_right (sub_pos.mpr hx')).mp hx
  obtain ⟨c, hc, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h1
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hg
  have hc' : x₀ < min c (x₀ + ε) := lt_min hc.out (by linarith)
  filter_upwards [Ioo_mem_nhdsGT hc'] with x hx
  have hxc : x < c := hx.2.trans_le (min_le_left _ _)
  have hxε : x < x₀ + ε := hx.2.trans_le (min_le_right _ _)
  have hD : ∀ t ∈ Icc x₀ x, HasDerivAt g (g' t) t := fun t ht => hball (by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope g g' hx.1
    (fun t ht => (hD t ht).continuousAt.continuousWithinAt)
    (fun t ht => hD t (Ioo_subset_Icc_self ht))
  have hpos : 0 < g' ξ := hsub ⟨hξ.1, hξ.2.trans hxc⟩
  rw [hξeq] at hpos
  have := (div_pos_iff_of_pos_right (sub_pos.mpr hx.1)).mp hpos
  linarith

/-- If `g' x₀ = 0` and `g'` has positive derivative at `x₀`, then `g` decreases strictly just
before `x₀`, i.e. `g x₀ < g x` for `x` slightly less than `x₀`. -/
theorem sturmCount_eventually_lt_left (hg : ∀ᶠ x in 𝓝 x₀, HasDerivAt g (g' x) x)
    (hg' : HasDerivAt g' d x₀) (h0 : g' x₀ = 0) (hd : 0 < d) :
    ∀ᶠ x in 𝓝[<] x₀, g x₀ < g x := by
  have hsl := hasDerivAt_iff_tendsto_slope.mp hg'
  have h1 : ∀ᶠ x in 𝓝[<] x₀, g' x < 0 := by
    have : ∀ᶠ x in 𝓝[≠] x₀, 0 < slope g' x₀ x := hsl.eventually (lt_mem_nhds hd)
    filter_upwards [nhdsLT_le_nhdsNE x₀ this, self_mem_nhdsWithin] with x hx hx'
    rw [slope_def_field, h0, sub_zero] at hx
    rcases div_pos_iff.mp hx with ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd h (not_lt.mpr (sub_neg.mpr hx').le)
    · exact h
  obtain ⟨c, hc, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp h1
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hg
  have hc' : max c (x₀ - ε) < x₀ := max_lt hc.out (by linarith)
  filter_upwards [Ioo_mem_nhdsLT hc'] with x hx
  have hxc : c < x := (le_max_left _ _).trans_lt hx.1
  have hxε : x₀ - ε < x := (le_max_right _ _).trans_lt hx.1
  have hD : ∀ t ∈ Icc x x₀, HasDerivAt g (g' t) t := fun t ht => hball (by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope g g' hx.2
    (fun t ht => (hD t ht).continuousAt.continuousWithinAt)
    (fun t ht => hD t (Ioo_subset_Icc_self ht))
  have hneg : g' ξ < 0 := hsub ⟨hxc.trans hξ.1, hξ.2⟩
  rw [hξeq] at hneg
  have := (div_lt_iff₀ (sub_pos.mpr hx.2)).mp hneg
  linarith

/-- A critical point at which the derivative has positive derivative is not a local
maximum. -/
theorem sturmCount_not_isLocalMax (hg : ∀ᶠ x in 𝓝 x₀, HasDerivAt g (g' x) x)
    (hg' : HasDerivAt g' d x₀) (h0 : g' x₀ = 0) (hd : 0 < d) : ¬IsLocalMax g x₀ := by
  intro hmax
  obtain ⟨x, h1, h2⟩ := ((sturmCount_eventually_lt_right hg hg' h0 hd).and
    (nhdsWithin_le_nhds hmax)).exists
  exact absurd h2 (not_le.mpr h1)

/-- **Maximum principle.** Let `g ≤ 0` at both ends of `[a, b]`, and let `g'' > 0` at every
interior critical point where `g > 0`. Then `g ≤ 0` on `[a, b]`. -/
theorem sturmCount_nonpos_of_maxPrinciple {a b : ℝ} (hc : ContinuousOn g (Icc a b))
    (hg : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Ioo a b, HasDerivAt g' (g'' x) x)
    (ha : g a ≤ 0) (hb : g b ≤ 0) (hode : ∀ x ∈ Ioo a b, 0 < g x → g' x = 0 → 0 < g'' x) :
    ∀ x ∈ Icc a b, g x ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hy, hgy⟩ := hcon
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨y, hy⟩ hc
  have hpos : 0 < g x := hgy.trans_le (hmax hy)
  have hxa : a < x := lt_of_le_of_ne hx.1 fun h => by rw [← h] at hpos; linarith
  have hxb : x < b := lt_of_le_of_ne hx.2 fun h => by rw [h] at hpos; linarith
  have hmem : Ioo a b ∈ 𝓝 x := Ioo_mem_nhds hxa hxb
  have hloc : IsLocalMax g x := hmax.isLocalMax (Icc_mem_nhds hxa hxb)
  have hd0 := hloc.hasDerivAt_eq_zero (hg x ⟨hxa, hxb⟩)
  exact sturmCount_not_isLocalMax (Filter.mem_of_superset hmem fun t ht => hg t ht)
    (hg' x ⟨hxa, hxb⟩) hd0 (hode x ⟨hxa, hxb⟩ hpos hd0) hloc

/-- **Strict maximum principle.** Let `g < 0` at both ends of `[a, b]`, and let `g'' > 0` at
every interior critical point where `g ≥ 0`. Then `g < 0` on `[a, b]`. -/
theorem sturmCount_neg_of_maxPrinciple {a b : ℝ} (hc : ContinuousOn g (Icc a b))
    (hg : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Ioo a b, HasDerivAt g' (g'' x) x)
    (ha : g a < 0) (hb : g b < 0) (hode : ∀ x ∈ Ioo a b, 0 ≤ g x → g' x = 0 → 0 < g'' x) :
    ∀ x ∈ Icc a b, g x < 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hy, hgy⟩ := hcon
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨y, hy⟩ hc
  have hpos : 0 ≤ g x := hgy.trans (hmax hy)
  have hxa : a < x := lt_of_le_of_ne hx.1 fun h => by rw [← h] at hpos; linarith
  have hxb : x < b := lt_of_le_of_ne hx.2 fun h => by rw [h] at hpos; linarith
  have hmem : Ioo a b ∈ 𝓝 x := Ioo_mem_nhds hxa hxb
  have hloc : IsLocalMax g x := hmax.isLocalMax (Icc_mem_nhds hxa hxb)
  have hd0 := hloc.hasDerivAt_eq_zero (hg x ⟨hxa, hxb⟩)
  exact sturmCount_not_isLocalMax (Filter.mem_of_superset hmem fun t ht => hg t ht)
    (hg' x ⟨hxa, hxb⟩) hd0 (hode x ⟨hxa, hxb⟩ hpos hd0) hloc

/-- **At most one critical point.** If `g'' < 0` at every critical point of `g` in `(a, b)`,
then `g` has at most one critical point in `(a, b)`. -/
theorem sturmCount_deriv_zero_unique {a b : ℝ}
    (hg : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Ioo a b, HasDerivAt g' (g'' x) x)
    (hneg : ∀ x ∈ Ioo a b, g' x = 0 → g'' x < 0) {c₁ c₂ : ℝ} (h₁ : c₁ ∈ Ioo a b)
    (h₂ : c₂ ∈ Ioo a b) (e₁ : g' c₁ = 0) (e₂ : g' c₂ = 0) : c₁ = c₂ := by
  by_contra hne
  wlog hlt : c₁ < c₂ generalizing c₁ c₂
  · exact this h₂ h₁ e₂ e₁ (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
  have hN : ∀ x ∈ Ioo a b, ∀ᶠ t in 𝓝 x, HasDerivAt (fun t => -g t) (-g' t) t :=
    fun x hx => Filter.mem_of_superset (Ioo_mem_nhds hx.1 hx.2) fun t ht => (hg t ht).neg
  have hI : Icc c₁ c₂ ⊆ Ioo a b := Icc_subset_Ioo h₁.1 h₂.2
  have hcont : ContinuousOn g (Icc c₁ c₂) := fun t ht =>
    (hg t (hI ht)).continuousAt.continuousWithinAt
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hlt.le) hcont
  have r₁ := sturmCount_eventually_lt_right (hN c₁ h₁) (hg' c₁ h₁).neg (by simp [e₁])
    (by linarith [hneg c₁ h₁ e₁])
  have r₂ := sturmCount_eventually_lt_left (hN c₂ h₂) (hg' c₂ h₂).neg (by simp [e₂])
    (by linarith [hneg c₂ h₂ e₂])
  obtain ⟨t₁, ht₁, ht₁'⟩ := (r₁.and (Ioo_mem_nhdsGT hlt)).exists
  obtain ⟨t₂, ht₂, ht₂'⟩ := (r₂.and (Ioo_mem_nhdsLT hlt)).exists
  have hm₁ : m ≠ c₁ := fun h => by
    have : g m ≤ g t₁ := hmin (Ioo_subset_Icc_self ht₁')
    rw [h] at this; linarith
  have hm₂ : m ≠ c₂ := fun h => by
    have : g m ≤ g t₂ := hmin (Ioo_subset_Icc_self ht₂')
    rw [h] at this; linarith
  have hmo : m ∈ Ioo c₁ c₂ := ⟨lt_of_le_of_ne hm.1 (Ne.symm hm₁), lt_of_le_of_ne hm.2 hm₂⟩
  have hmab : m ∈ Ioo a b := hI (Ioo_subset_Icc_self hmo)
  have hloc : IsLocalMin g m := hmin.isLocalMin (Icc_mem_nhds hmo.1 hmo.2)
  have hd0 := hloc.hasDerivAt_eq_zero (hg m hmab)
  exact sturmCount_not_isLocalMax (hN m hmab) (hg' m hmab).neg (by simp [hd0])
    (by linarith [hneg m hmab hd0]) hloc.neg


/-- **Separation of zeros by a Wronskian.** Let `p q' - q p' > 0` on `[c, d]`, and let `c < d` be
consecutive zeros of `p`. Then `q` has exactly one zero in `(c, d)`. No differential equation
is needed: the sign of the Wronskian at `c` and `d` forces a sign change of `q`, and `q / p` is
strictly monotone on `(c, d)`. -/
theorem sturmCount_existsUnique_zero_between {p p' q q' : ℝ → ℝ} {c d : ℝ} (hcd : c < d)
    (hp : ∀ x ∈ Icc c d, HasDerivAt p (p' x) x) (hq : ∀ x ∈ Icc c d, HasDerivAt q (q' x) x)
    (hw : ∀ x ∈ Icc c d, 0 < p x * q' x - q x * p' x)
    (hc : p c = 0) (hd : p d = 0) (hne : ∀ x ∈ Ioo c d, p x ≠ 0) :
    ∃! e, e ∈ Ioo c d ∧ q e = 0 := by
  have hcI : c ∈ Icc c d := ⟨le_rfl, hcd.le⟩
  have hdI : d ∈ Icc c d := ⟨hcd.le, le_rfl⟩
  have hqc : ContinuousOn q (Icc c d) := fun x hx => (hq x hx).continuousAt.continuousWithinAt
  have hpc : ContinuousOn p (Ioo c d) := fun x hx =>
    (hp x (Ioo_subset_Icc_self hx)).continuousAt.continuousWithinAt
  have wc := hw c hcI
  have wd := hw d hdI
  rw [hc, zero_mul, zero_sub] at wc
  rw [hd, zero_mul, zero_sub] at wd
  have hex : ∃ e, e ∈ Ioo c d ∧ q e = 0 := by
    rcases pos_or_neg_of_ne_zero hpc hne with hpos | hneg
    · have h1 := nonneg_of_hasDerivAt_of_eq_zero_left hcd (hp c hcI) hc fun x hx => (hpos x hx).le
      have h2 := nonpos_of_hasDerivAt_of_eq_zero_right hcd (hp d hdI) hd fun x hx => (hpos x hx).le
      have hqc0 : q c < 0 := by nlinarith
      have hqd0 : 0 < q d := by nlinarith
      obtain ⟨e, he, he0⟩ := intermediate_value_Icc hcd.le hqc ⟨hqc0.le, hqd0.le⟩
      refine ⟨e, ⟨lt_of_le_of_ne he.1 ?_, lt_of_le_of_ne he.2 ?_⟩, he0⟩
      · rintro rfl; linarith
      · rintro rfl; linarith
    · have h1 := nonneg_of_hasDerivAt_of_eq_zero_left (u := fun x => -p x) hcd (hp c hcI).neg
        (by simp [hc]) fun x hx => (neg_pos.mpr (hneg x hx)).le
      have h2 := nonpos_of_hasDerivAt_of_eq_zero_right (u := fun x => -p x) hcd (hp d hdI).neg
        (by simp [hd]) fun x hx => (neg_pos.mpr (hneg x hx)).le
      have hqc0 : 0 < q c := by nlinarith
      have hqd0 : q d < 0 := by nlinarith
      obtain ⟨e, he, he0⟩ := intermediate_value_Icc' hcd.le hqc ⟨hqd0.le, hqc0.le⟩
      refine ⟨e, ⟨lt_of_le_of_ne he.1 ?_, lt_of_le_of_ne he.2 ?_⟩, he0⟩
      · rintro rfl; linarith
      · rintro rfl; linarith
  have key : ∀ y e, y ∈ Ioo c d → e ∈ Ioo c d → q y = 0 → q e = 0 → y < e → False := by
    intro y e hy he hy0 he0 hlt
    have hsub : Icc y e ⊆ Ioo c d := Icc_subset_Ioo hy.1 he.2
    have hD : ∀ x ∈ Icc y e, HasDerivAt (fun t => q t / p t)
        ((q' x * p x - q x * p' x) / p x ^ 2) x := fun x hx =>
      HasDerivAt.fun_div (hq x (Ioo_subset_Icc_self (hsub hx)))
          (hp x (Ioo_subset_Icc_self (hsub hx)))
        (hne x (hsub hx))
    obtain ⟨ξ, hξ, hξ0⟩ := exists_hasDerivAt_eq_zero hlt
      (fun x hx => (hD x hx).continuousAt.continuousWithinAt) (by simp [hy0, he0])
      (fun x hx => hD x (Ioo_subset_Icc_self hx))
    have hξI : ξ ∈ Icc c d := Ioo_subset_Icc_self (hsub (Ioo_subset_Icc_self hξ))
    have hpξ : p ξ ^ 2 ≠ 0 := pow_ne_zero 2 (hne ξ (hsub (Ioo_subset_Icc_self hξ)))
    rw [div_eq_zero_iff, or_iff_left hpξ] at hξ0
    have := hw ξ hξI
    linarith
  obtain ⟨e, he, he0⟩ := hex
  refine ⟨e, ⟨he, he0⟩, fun y ⟨hy, hy0⟩ => ?_⟩
  rcases lt_trichotomy y e with h | h | h
  · exact (key y e hy he hy0 he0 h).elim
  · exact h
  · exact (key e y he hy he0 hy0 h).elim


/-- **At most one zero.** If `p ≠ 0` on `(c, d)` and `p q' - q p' > 0` there, then `q` has at
most one zero in `(c, d)` (Rolle's theorem applied to `q / p`). -/
theorem sturmCount_zero_unique_of_wronskian {p p' q q' : ℝ → ℝ} {c d : ℝ}
    (hp : ∀ x ∈ Ioo c d, HasDerivAt p (p' x) x) (hq : ∀ x ∈ Ioo c d, HasDerivAt q (q' x) x)
    (hw : ∀ x ∈ Ioo c d, 0 < p x * q' x - q x * p' x) (hne : ∀ x ∈ Ioo c d, p x ≠ 0)
    {y e : ℝ} (hy : y ∈ Ioo c d) (he : e ∈ Ioo c d) (hy0 : q y = 0) (he0 : q e = 0) : y = e := by
  have key : ∀ y e, y ∈ Ioo c d → e ∈ Ioo c d → q y = 0 → q e = 0 → y < e → False := by
    intro y e hy he hy0 he0 hlt
    have hsub : Icc y e ⊆ Ioo c d := Icc_subset_Ioo hy.1 he.2
    have hD : ∀ x ∈ Icc y e, HasDerivAt (fun t => q t / p t)
        ((q' x * p x - q x * p' x) / p x ^ 2) x := fun x hx =>
      HasDerivAt.fun_div (hq x (hsub hx)) (hp x (hsub hx)) (hne x (hsub hx))
    obtain ⟨ξ, hξ, hξ0⟩ := exists_hasDerivAt_eq_zero hlt
      (fun x hx => (hD x hx).continuousAt.continuousWithinAt) (by simp [hy0, he0])
      (fun x hx => hD x (Ioo_subset_Icc_self hx))
    have hξI : ξ ∈ Ioo c d := hsub (Ioo_subset_Icc_self hξ)
    have hpξ : p ξ ^ 2 ≠ 0 := pow_ne_zero 2 (hne ξ hξI)
    rw [div_eq_zero_iff, or_iff_left hpξ] at hξ0
    have := hw ξ hξI
    linarith
  rcases lt_trichotomy y e with h | h | h
  · exact (key y e hy he hy0 he0 h).elim
  · exact h
  · exact (key e y he hy he0 hy0 h).elim

/-- **One zero next to a right end.** Let `p q' - q p' > 0` on `[c, d)`, `p c = 0`, `p ≠ 0` on
`(c, d)`, and let `q / p` be positive somewhere in `(c, d)`. Then `q` has exactly one zero in
`(c, d)`. -/
theorem sturmCount_existsUnique_zero_right {p p' q q' : ℝ → ℝ} {c d : ℝ}
    (hp : ∀ x ∈ Ico c d, HasDerivAt p (p' x) x) (hq : ∀ x ∈ Ico c d, HasDerivAt q (q' x) x)
    (hw : ∀ x ∈ Ico c d, 0 < p x * q' x - q x * p' x) (hc : p c = 0)
    (hne : ∀ x ∈ Ioo c d, p x ≠ 0) (hpos : ∃ y ∈ Ioo c d, 0 < q y / p y) :
    ∃! e, e ∈ Ioo c d ∧ q e = 0 := by
  obtain ⟨y, hy, hqy⟩ := hpos
  have hcd : c < d := hy.1.trans hy.2
  have hcI : c ∈ Ico c d := ⟨le_rfl, hcd⟩
  have hsub : Icc c y ⊆ Ico c d := fun x hx => ⟨hx.1, hx.2.trans_lt hy.2⟩
  have hqc : ContinuousOn q (Icc c y) := fun x hx =>
    (hq x (hsub hx)).continuousAt.continuousWithinAt
  have hpc : ContinuousOn p (Ioo c d) := fun x hx =>
    (hp x (Ioo_subset_Ico_self hx)).continuousAt.continuousWithinAt
  have wc := hw c hcI
  rw [hc, zero_mul, zero_sub] at wc
  have hex : ∃ e, e ∈ Ioo c d ∧ q e = 0 := by
    rcases pos_or_neg_of_ne_zero hpc hne with hP | hN
    · have h1 := nonneg_of_hasDerivAt_of_eq_zero_left hcd (hp c hcI) hc fun x hx => (hP x hx).le
      have hqc0 : q c < 0 := by nlinarith
      have hqy0 : 0 < q y := (div_pos_iff_of_pos_right (hP y hy)).mp hqy
      obtain ⟨e, he, he0⟩ := intermediate_value_Ioo hy.1.le hqc ⟨hqc0, hqy0⟩
      exact ⟨e, ⟨he.1, he.2.trans hy.2⟩, he0⟩
    · have h1 := nonneg_of_hasDerivAt_of_eq_zero_left (u := fun x => -p x) hcd (hp c hcI).neg
        (by simp [hc]) fun x hx => (neg_pos.mpr (hN x hx)).le
      have hqc0 : 0 < q c := by nlinarith
      have hqy0 : q y < 0 := by
        by_contra hle; push Not at hle
        have := div_nonpos_of_nonneg_of_nonpos hle (hN y hy).le
        linarith
      obtain ⟨e, he, he0⟩ := intermediate_value_Ioo' hy.1.le hqc ⟨hqy0, hqc0⟩
      exact ⟨e, ⟨he.1, he.2.trans hy.2⟩, he0⟩
  obtain ⟨e, he, he0⟩ := hex
  exact ⟨e, ⟨he, he0⟩, fun z ⟨hz, hz0⟩ => sturmCount_zero_unique_of_wronskian
    (fun x hx => hp x (Ioo_subset_Ico_self hx)) (fun x hx => hq x (Ioo_subset_Ico_self hx))
    (fun x hx => hw x (Ioo_subset_Ico_self hx)) hne hz he hz0 he0⟩

/-- **One zero next to a left end.** Let `p q' - q p' > 0` on `(c, d]`, `p d = 0`, `p ≠ 0` on
`(c, d)`, and let `q / p` be negative somewhere in `(c, d)`. Then `q` has exactly one zero in
`(c, d)`. -/
theorem sturmCount_existsUnique_zero_left {p p' q q' : ℝ → ℝ} {c d : ℝ}
    (hp : ∀ x ∈ Ioc c d, HasDerivAt p (p' x) x) (hq : ∀ x ∈ Ioc c d, HasDerivAt q (q' x) x)
    (hw : ∀ x ∈ Ioc c d, 0 < p x * q' x - q x * p' x) (hd : p d = 0)
    (hne : ∀ x ∈ Ioo c d, p x ≠ 0) (hneg : ∃ y ∈ Ioo c d, q y / p y < 0) :
    ∃! e, e ∈ Ioo c d ∧ q e = 0 := by
  obtain ⟨y, hy, hqy⟩ := hneg
  have hcd : c < d := hy.1.trans hy.2
  have hdI : d ∈ Ioc c d := ⟨hcd, le_rfl⟩
  have hsub : Icc y d ⊆ Ioc c d := fun x hx => ⟨hy.1.trans_le hx.1, hx.2⟩
  have hqc : ContinuousOn q (Icc y d) := fun x hx =>
    (hq x (hsub hx)).continuousAt.continuousWithinAt
  have hpc : ContinuousOn p (Ioo c d) := fun x hx =>
    (hp x (Ioo_subset_Ioc_self hx)).continuousAt.continuousWithinAt
  have wd := hw d hdI
  rw [hd, zero_mul, zero_sub] at wd
  have hex : ∃ e, e ∈ Ioo c d ∧ q e = 0 := by
    rcases pos_or_neg_of_ne_zero hpc hne with hP | hN
    · have h1 := nonpos_of_hasDerivAt_of_eq_zero_right hcd (hp d hdI) hd fun x hx => (hP x hx).le
      have hqd0 : 0 < q d := by nlinarith
      have hqy0 : q y < 0 := by
        by_contra hle; push Not at hle
        have := div_nonneg hle (hP y hy).le
        linarith
      obtain ⟨e, he, he0⟩ := intermediate_value_Ioo hy.2.le hqc ⟨hqy0, hqd0⟩
      exact ⟨e, ⟨hy.1.trans he.1, he.2⟩, he0⟩
    · have h1 := nonpos_of_hasDerivAt_of_eq_zero_right (u := fun x => -p x) hcd (hp d hdI).neg
        (by simp [hd]) fun x hx => (neg_pos.mpr (hN x hx)).le
      have hqd0 : q d < 0 := by nlinarith
      have hqy0 : 0 < q y := by
        have := hN y hy
        by_contra hle; push Not at hle
        have : 0 ≤ q y / p y := div_nonneg_of_nonpos hle this.le
        linarith
      obtain ⟨e, he, he0⟩ := intermediate_value_Ioo' hy.2.le hqc ⟨hqd0, hqy0⟩
      exact ⟨e, ⟨hy.1.trans he.1, he.2⟩, he0⟩
  obtain ⟨e, he, he0⟩ := hex
  exact ⟨e, ⟨he, he0⟩, fun z ⟨hz, hz0⟩ => sturmCount_zero_unique_of_wronskian
    (fun x hx => hp x (Ioo_subset_Ioc_self hx)) (fun x hx => hq x (Ioo_subset_Ioc_self hx))
    (fun x hx => hw x (Ioo_subset_Ioc_self hx)) hne hz he hz0 he0⟩

/-- **One zero in a zero-free interval.** If `p ≠ 0` and `p q' - q p' > 0` on `(c, d)` and
`q / p` takes both signs there, then `q` has exactly one zero in `(c, d)`. -/
theorem sturmCount_existsUnique_zero_of_signs {p p' q q' : ℝ → ℝ} {c d : ℝ}
    (hp : ∀ x ∈ Ioo c d, HasDerivAt p (p' x) x) (hq : ∀ x ∈ Ioo c d, HasDerivAt q (q' x) x)
    (hw : ∀ x ∈ Ioo c d, 0 < p x * q' x - q x * p' x) (hne : ∀ x ∈ Ioo c d, p x ≠ 0)
    (hneg : ∃ y ∈ Ioo c d, q y / p y < 0) (hpos : ∃ y ∈ Ioo c d, 0 < q y / p y) :
    ∃! e, e ∈ Ioo c d ∧ q e = 0 := by
  obtain ⟨y₁, hy₁, h₁⟩ := hneg
  obtain ⟨y₂, hy₂, h₂⟩ := hpos
  have hr : ContinuousOn (fun t => q t / p t) (uIcc y₁ y₂) := fun x hx =>
    have hx' : x ∈ Ioo c d := (ordConnected_Ioo.uIcc_subset hy₁ hy₂) hx
    ((HasDerivAt.fun_div (hq x hx') (hp x hx') (hne x hx')).continuousAt.continuousWithinAt)
  obtain ⟨e, he, he0⟩ := isPreconnected_uIcc.intermediate_value left_mem_uIcc right_mem_uIcc hr
    ⟨h₁.le, h₂.le⟩
  have he' : e ∈ Ioo c d := (ordConnected_Ioo.uIcc_subset hy₁ hy₂) he
  have hq0 : q e = 0 := by
    simpa [div_eq_zero_iff, hne e he'] using he0
  exact ⟨e, ⟨he', hq0⟩, fun z ⟨hz, hz0⟩ =>
    sturmCount_zero_unique_of_wronskian hp hq hw hne hz he' hz0 hq0⟩

/-- **Divergence at a right end.** If `r' ≥ c / (b - y)` on `[y₀, b)` with `c > 0`, then `r`
takes positive values in `(y₀, b)`. -/
theorem sturmCount_exists_pos_of_deriv_ge {r r' : ℝ → ℝ} {y₀ b c : ℝ} (hy₀ : y₀ < b)
    (hc : 0 < c) (hr : ∀ y ∈ Ico y₀ b, HasDerivAt r (r' y) y)
    (hge : ∀ y ∈ Ico y₀ b, c / (b - y) ≤ r' y) : ∃ y ∈ Ioo y₀ b, 0 < r y := by
  set F : ℝ → ℝ := fun y => r y + c * Real.log (b - y)
  have hF : ∀ y ∈ Ico y₀ b, HasDerivAt F (r' y - c / (b - y)) y := by
    intro y hy
    have hby : 0 < b - y := sub_pos.mpr hy.2
    have hl : HasDerivAt (fun t => Real.log (b - t)) (-1 / (b - y)) y := by
      exact HasDerivAt.log ((hasDerivAt_id y).const_sub b) hby.ne'
    have := (hr y hy).add (hl.const_mul c)
    convert this using 1
    ring
  have hmono : MonotoneOn F (Ico y₀ b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun y => r' y - c / (b - y))
      (convex_Ico y₀ b) (fun y hy => (hF y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hF y (interior_subset hy)).hasDerivWithinAt) fun y hy => ?_
    have := hge y (interior_subset hy)
    linarith
  -- choose `y` with `c log (b - y) < -F y₀`
  set δ := min ((b - y₀) / 2) (Real.exp (-(|F y₀| + 1) / c))
  have hδ : 0 < δ := lt_min (by linarith) (Real.exp_pos _)
  have hδb : δ < b - y₀ := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨b - δ, ⟨by linarith, by linarith⟩, ?_⟩
  have hFy := hmono ⟨le_rfl, hy₀⟩ ⟨by linarith, by linarith⟩ (show y₀ ≤ b - δ by linarith)
  simp only [F, sub_sub_cancel] at hFy
  have hlog : Real.log δ ≤ -(|F y₀| + 1) / c := by
    rw [← Real.log_exp (-(|F y₀| + 1) / c)]
    exact Real.log_le_log hδ (min_le_right _ _)
  have : c * Real.log δ ≤ -(|F y₀| + 1) := by
    have := mul_le_mul_of_nonneg_left hlog hc.le
    rwa [mul_div_cancel₀ _ hc.ne'] at this
  have hab := neg_abs_le (F y₀)
  simp only [F] at hab
  linarith

/-- **Divergence at a left end.** If `r' ≥ c / (y - a)` on `(a, y₀]` with `c > 0`, then `r`
takes negative values in `(a, y₀)`. -/
theorem sturmCount_exists_neg_of_deriv_ge {r r' : ℝ → ℝ} {a y₀ c : ℝ} (hy₀ : a < y₀)
    (hc : 0 < c) (hr : ∀ y ∈ Ioc a y₀, HasDerivAt r (r' y) y)
    (hge : ∀ y ∈ Ioc a y₀, c / (y - a) ≤ r' y) : ∃ y ∈ Ioo a y₀, r y < 0 := by
  obtain ⟨y, hy, hy0⟩ := sturmCount_exists_pos_of_deriv_ge (r := fun t => -r (-t))
    (r' := fun t => r' (-t)) (y₀ := -y₀) (b := -a) (by linarith) hc
    (fun t ht => by
      have h1 : HasDerivAt (fun t => r (-t)) (r' (-t) * (-1)) t :=
        HasDerivAt.comp t (hr (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩) (hasDerivAt_neg t)
      have h2 := h1.neg
      convert h2 using 1
      ring)
    (fun t ht => by
      have := hge (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
      rwa [show -t - a = -a - t by ring] at this)
  exact ⟨-y, ⟨by linarith [hy.2], by linarith [hy.1]⟩, by simpa using hy0⟩

/-- **Counting zeros over a partition.** Let `t₀ < t₁ < ⋯ < t_m`, let `P` hold at exactly one
point of each `(t_k, t_{k+1})` (`k < m`) and at none of the interior points `t_k`
(`0 < k < m`). Then `P` holds at exactly `m` points of `(t₀, t_m)`. -/
theorem sturmCount_ncard_of_partition {P : ℝ → Prop} {t : ℕ → ℝ} {m : ℕ}
    (ht : ∀ k < m, t k < t (k + 1)) (hu : ∀ k < m, ∃! x, x ∈ Ioo (t k) (t (k + 1)) ∧ P x)
    (he : ∀ k, 0 < k → k < m → ¬P (t k)) :
    {x | x ∈ Ioo (t 0) (t m) ∧ P x}.Finite ∧ {x | x ∈ Ioo (t 0) (t m) ∧ P x}.ncard = m := by
  classical
  have htmono : ∀ j k, j ≤ k → k ≤ m → t j ≤ t k := by
    intro j k hjk hkm
    induction k, hjk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hjk ih => exact (ih (by omega)).trans (ht k (by omega)).le
  let z : ℕ → ℝ := fun k => if h : k < m then (hu k h).exists.choose else 0
  have hz : ∀ k < m, z k ∈ Ioo (t k) (t (k + 1)) ∧ P (z k) := fun k hk => by
    simp only [z, hk, ↓reduceDIte]; exact (hu k hk).exists.choose_spec
  have hset : {x | x ∈ Ioo (t 0) (t m) ∧ P x} = z '' (Finset.range m : Set ℕ) := by
    ext x
    constructor
    · rintro ⟨hx, hPx⟩
      have hex : ∃ k, k ≤ m ∧ t k < x := ⟨0, Nat.zero_le _, hx.1⟩
      let k := Nat.findGreatest (fun k => t k < x) m
      have hk : t k < x := Nat.findGreatest_spec (P := fun k => t k < x) (Nat.zero_le m) hx.1
      have hkm : k ≤ m := Nat.findGreatest_le m
      have hkm' : k < m := lt_of_le_of_ne hkm fun h => by rw [h] at hk; linarith [hx.2]
      have hk1 : x ≤ t (k + 1) := by
        by_contra hlt
        exact Nat.findGreatest_is_greatest (P := fun k => t k < x) (Nat.lt_succ_self k)
          (by omega) (not_le.mp hlt)
      have hk1' : x < t (k + 1) := by
        refine lt_of_le_of_ne hk1 fun h => ?_
        rcases Nat.lt_or_ge (k + 1) m with h' | h'
        · exact he (k + 1) (Nat.succ_pos _) h' (h ▸ hPx)
        · have : k + 1 = m := by omega
          rw [this] at h; linarith [hx.2]
      refine ⟨k, by simpa using hkm', ?_⟩
      exact (hu k hkm').unique (hz k hkm') ⟨⟨hk, hk1'⟩, hPx⟩
    · rintro ⟨k, hk, rfl⟩
      have hk' : k < m := by simpa using hk
      obtain ⟨⟨h1, h2⟩, hP⟩ := hz k hk'
      exact ⟨⟨(htmono 0 k (Nat.zero_le _) hk'.le).trans_lt h1,
        h2.trans_le (htmono (k + 1) m hk' le_rfl)⟩, hP⟩
  have hinj : Set.InjOn z (Finset.range m : Set ℕ) := by
    intro j hj k hk hjk
    have hj' : j < m := by simpa using hj
    have hk' : k < m := by simpa using hk
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := (hz j hj').1.2.trans_le ((htmono (j + 1) k h hk'.le).trans (hz k hk').1.1.le)
      rw [hjk] at this; exact lt_irrefl _ this
    · have := (hz k hk').1.2.trans_le ((htmono (k + 1) j h hj'.le).trans (hz j hj').1.1.le)
      rw [hjk] at this; exact lt_irrefl _ this
  rw [hset]
  refine ⟨(Finset.finite_toSet _).image _, ?_⟩
  rw [hinj.ncard_image, Set.ncard_coe_finset, Finset.card_range]

/-- **Oscillation at `-∞`.** A function continuous on `(-∞, c)` that takes positive and
negative values arbitrarily far to the left has infinitely many zeros in `(-∞, c)`. -/
theorem sturmCount_infinite_zeros_atBot {f : ℝ → ℝ} {c : ℝ} (hf : ContinuousOn f (Iio c))
    (hpos : ∀ M, ∃ x < M, 0 < f x) (hneg : ∀ M, ∃ x < M, f x < 0) :
    {x : ℝ | x < c ∧ f x = 0}.Infinite := by
  intro hfin
  obtain ⟨m, hm⟩ := hfin.bddBelow
  set M := min m c - 1
  obtain ⟨x, hxM, hx⟩ := hpos M
  obtain ⟨y, hyM, hy⟩ := hneg M
  have hM : M < c := by simp only [M]; linarith [min_le_right m c]
  have hsub : uIcc y x ⊆ Iio c := fun t ht => by
    rcases ht with ⟨h1, h2⟩
    exact lt_of_le_of_lt h2 (max_lt (hyM.trans hM) (hxM.trans hM))
  obtain ⟨z, hz, hz0⟩ := isPreconnected_uIcc.intermediate_value left_mem_uIcc right_mem_uIcc
    (hf.mono hsub) ⟨hy.le, hx.le⟩
  have hzM : z < M := lt_of_le_of_lt hz.2 (max_lt hyM hxM)
  have := hm ⟨hzM.trans hM, hz0⟩
  simp only [M] at hzM
  linarith [min_le_left m c]

/-- **Oscillation at `+∞`.** A function continuous on `(c, ∞)` that takes positive and
negative values arbitrarily far to the right has infinitely many zeros in `(c, ∞)`. -/
theorem sturmCount_infinite_zeros_atTop {f : ℝ → ℝ} {c : ℝ} (hf : ContinuousOn f (Ioi c))
    (hpos : ∀ M, ∃ x > M, 0 < f x) (hneg : ∀ M, ∃ x > M, f x < 0) :
    {x : ℝ | c < x ∧ f x = 0}.Infinite := by
  intro hfin
  obtain ⟨m, hm⟩ := hfin.bddAbove
  set M := max m c + 1
  obtain ⟨x, hxM, hx⟩ := hpos M
  obtain ⟨y, hyM, hy⟩ := hneg M
  have hM : c < M := by simp only [M]; linarith [le_max_right m c]
  have hsub : uIcc y x ⊆ Ioi c := fun t ht => by
    rcases ht with ⟨h1, h2⟩
    exact lt_of_lt_of_le (lt_min (hM.trans hyM) (hM.trans hxM)) h1
  obtain ⟨z, hz, hz0⟩ := isPreconnected_uIcc.intermediate_value left_mem_uIcc right_mem_uIcc
    (hf.mono hsub) ⟨hy.le, hx.le⟩
  have hzM : M < z := lt_of_lt_of_le (lt_min hyM hxM) hz.1
  have := hm ⟨hM.trans hzM, hz0⟩
  simp only [M] at hzM
  linarith [le_max_left m c]

/-- **Rolle.** If `f` is differentiable on an order-connected set `s` and has infinitely many
zeros in `s`, then `f'` has infinitely many zeros in `s`. -/
theorem sturmCount_infinite_deriv_zeros {f f' : ℝ → ℝ} {s : Set ℝ} (hs : s.OrdConnected)
    (hf : ∀ x ∈ s, HasDerivAt f (f' x) x) (hinf : {x : ℝ | x ∈ s ∧ f x = 0}.Infinite) :
    {x : ℝ | x ∈ s ∧ f' x = 0}.Infinite := by
  intro hfin
  set n := hfin.toFinset.card
  obtain ⟨F, hFs, hFc⟩ := hinf.exists_subset_card_eq (n + 2)
  set e := F.orderEmbOfFin hFc
  have he : ∀ i, e i ∈ s ∧ f (e i) = 0 := fun i => hFs (F.orderEmbOfFin_mem hFc i)
  have hrolle : ∀ i : Fin (n + 1), ∃ c ∈ Ioo (e i.castSucc) (e i.succ), f' c = 0 := by
    intro i
    have hlt : e i.castSucc < e i.succ := e.strictMono Fin.castSucc_lt_succ
    have hI : Icc (e i.castSucc) (e i.succ) ⊆ s := hs.out (he _).1 (he _).1
    exact exists_hasDerivAt_eq_zero hlt
      (fun t ht => (hf t (hI ht)).continuousAt.continuousWithinAt)
      (by rw [(he _).2, (he _).2]) (fun t ht => hf t (hI (Ioo_subset_Icc_self ht)))
  choose c hc hc0 using hrolle
  have hmono : StrictMono c := by
    intro i j hij
    calc c i < e i.succ := (hc i).2
      _ ≤ e j.castSucc := e.monotone (Fin.succ_le_castSucc_iff.mpr hij)
      _ < c j := (hc j).1
  have hmem : ∀ i, c i ∈ hfin.toFinset := fun i => by
    rw [Set.Finite.mem_toFinset]
    have hI : Icc (e i.castSucc) (e i.succ) ⊆ s := hs.out (he _).1 (he _).1
    exact ⟨hI (Ioo_subset_Icc_self (hc i)), hc0 i⟩
  have := Finset.card_le_card_of_injOn c (s := Finset.univ) (fun i _ => hmem i)
    (hmono.injective.injOn)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  omega

end ODE
