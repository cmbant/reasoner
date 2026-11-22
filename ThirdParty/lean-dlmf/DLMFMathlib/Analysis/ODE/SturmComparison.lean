/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Sturm comparison and separation theorems

For real second-order equations in self-adjoint form `(p y')' + q y = 0` on an interval
`[a, b]` we prove the classical zero theorems of Sturm (Beals–Wong, Theorems 3.3.3, 3.3.4
and 3.3.6). A solution is described by two functions `y` and `y'` with
`HasDerivAt y (y' x) x` and `HasDerivAt (fun t => p t * y' t) (-(q x * y x)) x` on `[a, b]`;
no existence or uniqueness theory for the equation is used.

The tool is the Wronskian `W = p (u' v - u v')` of a solution `u` of the `q₁`-equation and a
solution `v` of the `q₂`-equation, whose derivative is `(q₂ - q₁) u v`.

## Main results

* `ODE.sturm_comparison`: if `q₁ ≤ q₂` on `(a, b)` and `u` has consecutive zeros `a < b`,
  then either `v` vanishes in `(a, b)` or `W(u, v)` vanishes identically on `[a, b]`.
* `ODE.sturm_comparison_strict`: if `q₁ < q₂` on `(a, b)`, then `v` vanishes in `(a, b)`.
* `ODE.sturm_separation`: for one equation and solutions with nonzero Wronskian, `v` does not
  vanish at the consecutive zeros `a`, `b` of `u`, and it vanishes in between.
* `ODE.eq_zero_of_eq_zero_of_eq_zero_of_nonpos`: if `p > 0` and `q ≤ 0`, a solution vanishing
  at `a` and at `b` vanishes on `[a, b]`.
-/

@[expose] public section

open Set Filter Topology

namespace ODE

variable {p q q₁ q₂ u u' v v' y y' : ℝ → ℝ} {a b : ℝ}

/-- The Wronskian `p (u' v - u v')` of the equations `(p y')' + q y = 0`. -/
def sturmWronskian (p u u' v v' : ℝ → ℝ) (x : ℝ) : ℝ :=
  p x * (u' x * v x - u x * v' x)

/-- At `x`, the function `(sturmWronskian p u u' v v')` has derivative `((q₂ x - q₁ x) * u x * v
x)`. -/
theorem hasDerivAt_sturmWronskian {x : ℝ}
    (hu : HasDerivAt u (u' x) x) (hpu : HasDerivAt (fun t => p t * u' t) (-(q₁ x * u x)) x)
    (hv : HasDerivAt v (v' x) x) (hpv : HasDerivAt (fun t => p t * v' t) (-(q₂ x * v x)) x) :
    HasDerivAt (sturmWronskian p u u' v v') ((q₂ x - q₁ x) * u x * v x) x := by
  have h := (hpu.mul hv).sub (hu.mul hpv)
  have hfun : sturmWronskian p u u' v v' = fun t => p t * u' t * v t - u t * (p t * v' t) := by
    funext t
    simp only [sturmWronskian]
    ring
  rw [hfun]
  convert h using 1
  ring

/-- At a left zero of a function that is nonnegative to the right, the derivative is
nonnegative. -/
theorem nonneg_of_hasDerivAt_of_eq_zero_left {d : ℝ} (hab : a < b) (hd : HasDerivAt u d a)
    (hua : u a = 0) (hpos : ∀ x ∈ Ioo a b, 0 ≤ u x) : 0 ≤ d := by
  have ht := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono a (show Ioi a ⊆ {a}ᶜ from fun t ht => ne_of_gt ht))
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT hab] with t ht
  rw [slope_def_field, hua, sub_zero]
  exact div_nonneg (hpos t ht) (sub_pos.mpr ht.1).le

/-- At a right zero of a function that is nonnegative to the left, the derivative is
nonpositive. -/
theorem nonpos_of_hasDerivAt_of_eq_zero_right {d : ℝ} (hab : a < b) (hd : HasDerivAt u d b)
    (hub : u b = 0) (hpos : ∀ x ∈ Ioo a b, 0 ≤ u x) : d ≤ 0 := by
  have ht := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono b (show Iio b ⊆ {b}ᶜ from fun t ht => ne_of_lt ht))
  refine le_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT hab] with t ht
  rw [slope_def_field, hub, sub_zero]
  exact div_nonpos_of_nonneg_of_nonpos (hpos t ht) (sub_neg.mpr ht.2).le

/-- A continuous function without zeros on `(a, b)` has constant sign there. -/
theorem pos_or_neg_of_ne_zero {f : ℝ → ℝ} (hf : ContinuousOn f (Ioo a b))
    (h0 : ∀ x ∈ Ioo a b, f x ≠ 0) :
    (∀ x ∈ Ioo a b, 0 < f x) ∨ ∀ x ∈ Ioo a b, f x < 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨x, hx, hfx⟩, ⟨y, hy, hfy⟩⟩ := hcon
  have hx' : f x < 0 := lt_of_le_of_ne hfx (h0 x hx)
  have hy' : 0 < f y := lt_of_le_of_ne hfy (h0 y hy).symm
  obtain ⟨z, hz, hfz⟩ := isPreconnected_Ioo.intermediate_value hx hy hf ⟨hx'.le, hy'.le⟩
  exact h0 z hz hfz

/-- The negative of a solution is a solution. -/
theorem neg_solution (hu : ∀ x ∈ Icc a b, HasDerivAt u (u' x) x)
    (hpu : ∀ x ∈ Icc a b, HasDerivAt (fun t => p t * u' t) (-(q x * u x)) x) :
    (∀ x ∈ Icc a b, HasDerivAt (fun t => -u t) (-u' x) x) ∧
      ∀ x ∈ Icc a b, HasDerivAt (fun t => p t * -u' t) (-(q x * -u x)) x := by
  refine ⟨fun x hx => (hu x hx).neg, fun x hx => ?_⟩
  have h := (hpu x hx).neg
  convert h using 1
  · funext t
    simp only [Pi.neg_apply]
    ring
  · ring

/-- Identity under the stated parameter and domain assumptions: `sturmWronskian p (fun t => -u t)
(fun t => -u' t) v v' x = -sturmWronskian p u u' v v' x`. -/
theorem sturmWronskian_neg_left (x : ℝ) :
    sturmWronskian p (fun t => -u t) (fun t => -u' t) v v' x =
      -sturmWronskian p u u' v v' x := by
  simp only [sturmWronskian]
  ring

/-- Identity under the stated parameter and domain assumptions: `sturmWronskian p u u' (fun t =>
-v t) (fun t => -v' t) x = -sturmWronskian p u u' v v' x`. -/
theorem sturmWronskian_neg_right (x : ℝ) :
    sturmWronskian p u u' (fun t => -v t) (fun t => -v' t) x =
      -sturmWronskian p u u' v v' x := by
  simp only [sturmWronskian]
  ring

/-- The core of the comparison theorem: for `u, v ≥ 0` on `(a, b)` the Wronskian vanishes. -/
theorem sturmWronskian_eq_zero_of_nonneg (hab : a < b)
    (hu : ∀ x ∈ Icc a b, HasDerivAt u (u' x) x)
    (hpu : ∀ x ∈ Icc a b, HasDerivAt (fun t => p t * u' t) (-(q₁ x * u x)) x)
    (hv : ∀ x ∈ Icc a b, HasDerivAt v (v' x) x)
    (hpv : ∀ x ∈ Icc a b, HasDerivAt (fun t => p t * v' t) (-(q₂ x * v x)) x)
    (hpa : 0 ≤ p a) (hpb : 0 ≤ p b) (hq : ∀ x ∈ Ioo a b, q₁ x ≤ q₂ x)
    (hua : u a = 0) (hub : u b = 0) (hupos : ∀ x ∈ Ioo a b, 0 ≤ u x)
    (hvpos : ∀ x ∈ Ioo a b, 0 ≤ v x) :
    ∀ x ∈ Icc a b, sturmWronskian p u u' v v' x = 0 := by
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  have hW : ∀ x ∈ Icc a b,
      HasDerivAt (sturmWronskian p u u' v v') ((q₂ x - q₁ x) * u x * v x) x := fun x hx =>
    hasDerivAt_sturmWronskian (hu x hx) (hpu x hx) (hv x hx) (hpv x hx)
  have hmono : MonotoneOn (sturmWronskian p u u' v v') (Icc a b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
      (f' := fun x => (q₂ x - q₁ x) * u x * v x)
      (fun x hx => (hW x hx).continuousAt.continuousWithinAt) (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Icc] at hx
      exact (hW x (Ioo_subset_Icc_self hx)).hasDerivWithinAt
    · rw [interior_Icc] at hx
      exact mul_nonneg (mul_nonneg (sub_nonneg.mpr (hq x hx)) (hupos x hx)) (hvpos x hx)
  have hva : 0 ≤ v a := by
    refine ge_of_tendsto ((hv a ha).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi a))) ?_
    filter_upwards [Ioo_mem_nhdsGT hab] with t ht using hvpos t ht
  have hvb : 0 ≤ v b := by
    refine ge_of_tendsto ((hv b hb).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio b))) ?_
    filter_upwards [Ioo_mem_nhdsLT hab] with t ht using hvpos t ht
  have hu'a := nonneg_of_hasDerivAt_of_eq_zero_left hab (hu a ha) hua hupos
  have hu'b := nonpos_of_hasDerivAt_of_eq_zero_right hab (hu b hb) hub hupos
  have hWa : 0 ≤ sturmWronskian p u u' v v' a := by
    simp only [sturmWronskian, hua, zero_mul, sub_zero]
    exact mul_nonneg hpa (mul_nonneg hu'a hva)
  have hWb : sturmWronskian p u u' v v' b ≤ 0 := by
    simp only [sturmWronskian, hub, zero_mul, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hpb (mul_nonpos_of_nonpos_of_nonneg hu'b hvb)
  intro x hx
  have h1 := hmono ha hx hx.1
  have h2 := hmono hx hb hx.2
  linarith

/-- **Sturm comparison theorem** (Beals–Wong, Theorem 3.3.4). Let `u` solve
`(p u')' + q₁ u = 0` and `v` solve `(p v')' + q₂ v = 0` on `[a, b]`, with `q₁ ≤ q₂` on
`(a, b)` and `p ≥ 0` at the endpoints. If `a < b` are consecutive zeros of `u`, then `v`
vanishes in `(a, b)` or the Wronskian `p (u' v - u v')` vanishes identically on `[a, b]`. -/
theorem sturm_comparison (hab : a < b)
    (hu : ∀ x ∈ Icc a b, HasDerivAt u (u' x) x)
    (hpu : ∀ x ∈ Icc a b, HasDerivAt (fun t => p t * u' t) (-(q₁ x * u x)) x)
    (hv : ∀ x ∈ Icc a b, HasDerivAt v (v' x) x)
    (hpv : ∀ x ∈ Icc a b, HasDerivAt (fun t => p t * v' t) (-(q₂ x * v x)) x)
    (hpa : 0 ≤ p a) (hpb : 0 ≤ p b) (hq : ∀ x ∈ Ioo a b, q₁ x ≤ q₂ x)
    (hua : u a = 0) (hub : u b = 0) (hu0 : ∀ x ∈ Ioo a b, u x ≠ 0) :
    (∃ x ∈ Ioo a b, v x = 0) ∨ ∀ x ∈ Icc a b, sturmWronskian p u u' v v' x = 0 := by
  by_cases hz : ∃ x ∈ Ioo a b, v x = 0
  · exact Or.inl hz
  right
  push Not at hz
  have hcont : ∀ {f f' : ℝ → ℝ}, (∀ x ∈ Icc a b, HasDerivAt f (f' x) x) →
      ContinuousOn f (Ioo a b) := fun hf x hx =>
    (hf x (Ioo_subset_Icc_self hx)).continuousAt.continuousWithinAt
  obtain ⟨hnu, hpnu⟩ := neg_solution hu hpu
  obtain ⟨hnv, hpnv⟩ := neg_solution hv hpv
  intro x hx
  rcases pos_or_neg_of_ne_zero (hcont hu) hu0 with hup | hun <;>
    rcases pos_or_neg_of_ne_zero (hcont hv) hz with hvp | hvn
  · exact sturmWronskian_eq_zero_of_nonneg hab hu hpu hv hpv hpa hpb hq hua hub
      (fun t ht => (hup t ht).le) (fun t ht => (hvp t ht).le) x hx
  · have h := sturmWronskian_eq_zero_of_nonneg hab hu hpu hnv hpnv hpa hpb hq hua hub
      (fun t ht => (hup t ht).le) (fun t ht => (neg_pos.mpr (hvn t ht)).le) x hx
    rw [sturmWronskian_neg_right] at h
    exact neg_eq_zero.mp h
  · have h := sturmWronskian_eq_zero_of_nonneg hab hnu hpnu hv hpv hpa hpb hq
      (by simp [hua]) (by simp [hub]) (fun t ht => (neg_pos.mpr (hun t ht)).le)
      (fun t ht => (hvp t ht).le) x hx
    rw [sturmWronskian_neg_left] at h
    exact neg_eq_zero.mp h
  · have h := sturmWronskian_eq_zero_of_nonneg hab hnu hpnu hnv hpnv hpa hpb hq
      (by simp [hua]) (by simp [hub]) (fun t ht => (neg_pos.mpr (hun t ht)).le)
      (fun t ht => (neg_pos.mpr (hvn t ht)).le) x hx
    rw [sturmWronskian_neg_right, sturmWronskian_neg_left, neg_neg] at h
    exact h

/-- **Sturm comparison theorem**, strict form: if `q₁ < q₂` on `(a, b)`, then every solution
of the `q₂`-equation vanishes between consecutive zeros `a < b` of a solution of the
`q₁`-equation. -/
theorem sturm_comparison_strict (hab : a < b)
    (hu : ∀ x ∈ Icc a b, HasDerivAt u (u' x) x)
    (hpu : ∀ x ∈ Icc a b, HasDerivAt (fun t => p t * u' t) (-(q₁ x * u x)) x)
    (hv : ∀ x ∈ Icc a b, HasDerivAt v (v' x) x)
    (hpv : ∀ x ∈ Icc a b, HasDerivAt (fun t => p t * v' t) (-(q₂ x * v x)) x)
    (hpa : 0 ≤ p a) (hpb : 0 ≤ p b) (hq : ∀ x ∈ Ioo a b, q₁ x < q₂ x)
    (hua : u a = 0) (hub : u b = 0) (hu0 : ∀ x ∈ Ioo a b, u x ≠ 0) :
    ∃ x ∈ Ioo a b, v x = 0 := by
  rcases sturm_comparison hab hu hpu hv hpv hpa hpb (fun x hx => (hq x hx).le) hua hub hu0
    with h | h
  · exact h
  have hm : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hd := hasDerivAt_sturmWronskian (hu _ (Ioo_subset_Icc_self hm))
    (hpu _ (Ioo_subset_Icc_self hm)) (hv _ (Ioo_subset_Icc_self hm))
    (hpv _ (Ioo_subset_Icc_self hm))
  have hloc : sturmWronskian p u u' v v' =ᶠ[𝓝 ((a + b) / 2)] fun _ => 0 := by
    filter_upwards [Ioo_mem_nhds hm.1 hm.2] with t ht using h t (Ioo_subset_Icc_self ht)
  have h0 := hd.unique ((hasDerivAt_const ((a + b) / 2) (0 : ℝ)).congr_of_eventuallyEq hloc)
  refine ⟨(a + b) / 2, hm, ?_⟩
  rcases mul_eq_zero.mp h0 with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (sub_ne_zero.mpr (hq _ hm).ne')
    · exact absurd h2 (hu0 _ hm)
  · exact h1

/-- For one equation the Wronskian of two solutions is constant. -/
theorem sturmWronskian_eq_left
    (hu : ∀ x ∈ Icc a b, HasDerivAt u (u' x) x)
    (hpu : ∀ x ∈ Icc a b, HasDerivAt (fun t => p t * u' t) (-(q x * u x)) x)
    (hv : ∀ x ∈ Icc a b, HasDerivAt v (v' x) x)
    (hpv : ∀ x ∈ Icc a b, HasDerivAt (fun t => p t * v' t) (-(q x * v x)) x) :
    ∀ x ∈ Icc a b, sturmWronskian p u u' v v' x = sturmWronskian p u u' v v' a := by
  have hW : ∀ x ∈ Icc a b, HasDerivAt (sturmWronskian p u u' v v') 0 x := fun x hx => by
    simpa using hasDerivAt_sturmWronskian (hu x hx) (hpu x hx) (hv x hx) (hpv x hx)
  exact constant_of_has_deriv_right_zero (fun x hx => (hW x hx).continuousAt.continuousWithinAt)
    fun x hx => (hW x (Ico_subset_Icc_self hx)).hasDerivWithinAt

/-- **Sturm separation theorem** (Beals–Wong, Theorem 3.3.3). Let `u` and `v` solve
`(p y')' + q y = 0` on `[a, b]` with a Wronskian that is somewhere nonzero, and let `p > 0`
at the endpoints. If `a < b` are consecutive zeros of `u`, then `v` does not vanish at `a`
or `b` and vanishes in `(a, b)`. -/
theorem sturm_separation (hab : a < b)
    (hu : ∀ x ∈ Icc a b, HasDerivAt u (u' x) x)
    (hpu : ∀ x ∈ Icc a b, HasDerivAt (fun t => p t * u' t) (-(q x * u x)) x)
    (hv : ∀ x ∈ Icc a b, HasDerivAt v (v' x) x)
    (hpv : ∀ x ∈ Icc a b, HasDerivAt (fun t => p t * v' t) (-(q x * v x)) x)
    (hpa : 0 ≤ p a) (hpb : 0 ≤ p b)
    (hua : u a = 0) (hub : u b = 0) (hu0 : ∀ x ∈ Ioo a b, u x ≠ 0)
    (hW : ∃ x₀ ∈ Icc a b, sturmWronskian p u u' v v' x₀ ≠ 0) :
    v a ≠ 0 ∧ v b ≠ 0 ∧ ∃ x ∈ Ioo a b, v x = 0 := by
  obtain ⟨x₀, hx₀, hW₀⟩ := hW
  have hconst := sturmWronskian_eq_left hu hpu hv hpv
  have hWa : sturmWronskian p u u' v v' a ≠ 0 := by rwa [← hconst x₀ hx₀]
  have hWb : sturmWronskian p u u' v v' b ≠ 0 := by
    rwa [hconst b (right_mem_Icc.mpr hab.le)]
  refine ⟨fun h => hWa ?_, fun h => hWb ?_, ?_⟩
  · simp [sturmWronskian, hua, h]
  · simp [sturmWronskian, hub, h]
  rcases sturm_comparison hab hu hpu hv hpv hpa hpb (fun _ _ => le_rfl) hua hub hu0 with h | h
  · exact h
  · exact absurd (h a (left_mem_Icc.mpr hab.le)) hWa

/-- **At most one zero** (Beals–Wong, Theorem 3.3.6). If `p > 0` and `q ≤ 0` on `(a, b)`, a
solution of `(p y')' + q y = 0` that vanishes at `a` and at `b` vanishes on `[a, b]`. -/
theorem eq_zero_of_eq_zero_of_eq_zero_of_nonpos (hab : a ≤ b)
    (hy : ∀ x ∈ Icc a b, HasDerivAt y (y' x) x)
    (hpy : ∀ x ∈ Icc a b, HasDerivAt (fun t => p t * y' t) (-(q x * y x)) x)
    (hp : ∀ x ∈ Ioo a b, 0 < p x) (hq : ∀ x ∈ Ioo a b, q x ≤ 0)
    (hya : y a = 0) (hyb : y b = 0) : ∀ x ∈ Icc a b, y x = 0 := by
  set F : ℝ → ℝ := fun t => y t * (p t * y' t) with hF
  have hFd : ∀ x ∈ Icc a b,
      HasDerivAt F (y' x * (p x * y' x) + y x * -(q x * y x)) x := fun x hx =>
    (hy x hx).mul (hpy x hx)
  have hmono : MonotoneOn F (Icc a b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
      (f' := fun x => y' x * (p x * y' x) + y x * -(q x * y x))
      (fun x hx => (hFd x hx).continuousAt.continuousWithinAt) (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Icc] at hx
      exact (hFd x (Ioo_subset_Icc_self hx)).hasDerivWithinAt
    · rw [interior_Icc] at hx
      have h1 := hp x hx
      have h2 := hq x hx
      nlinarith [sq_nonneg (y' x), sq_nonneg (y x), mul_nonneg h1.le (sq_nonneg (y' x)),
        mul_nonneg (neg_nonneg.mpr h2) (sq_nonneg (y x))]
  rcases hab.eq_or_lt with rfl | hlt
  · intro x hx
    rw [show x = a from le_antisymm hx.2 hx.1, hya]
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab
  have hFa : F a = 0 := by simp [hF, hya]
  have hFb : F b = 0 := by simp [hF, hyb]
  have hF0 : ∀ x ∈ Icc a b, F x = 0 := fun x hx => by
    have := hmono ha hx hx.1
    have := hmono hx hb hx.2
    linarith
  have hy'0 : ∀ x ∈ Ioo a b, y' x = 0 := by
    intro x hx
    have hloc : F =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht using hF0 t (Ioo_subset_Icc_self ht)
    have h0 := (hFd x (Ioo_subset_Icc_self hx)).unique
      ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hloc)
    have h1 := hp x hx
    have h2 := hq x hx
    have hsq : p x * y' x ^ 2 = 0 := by
      nlinarith [mul_nonneg h1.le (sq_nonneg (y' x)),
        mul_nonneg (neg_nonneg.mpr h2) (sq_nonneg (y x))]
    rcases mul_eq_zero.mp hsq with h | h
    · exact absurd h h1.ne'
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  intro x hx
  rcases hx.1.eq_or_lt with rfl | hax
  · exact hya
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope y y' hax
    (fun t ht => (hy t ⟨ht.1, ht.2.trans hx.2⟩).continuousAt.continuousWithinAt)
    (fun t ht => hy t ⟨ht.1.le, ht.2.le.trans hx.2⟩)
  rw [hy'0 c ⟨hc.1, hc.2.trans_le hx.2⟩, hya, sub_zero, eq_comm,
    div_eq_zero_iff] at hcd
  rcases hcd with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hax.ne'

end ODE
