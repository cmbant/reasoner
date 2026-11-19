/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ODE.SturmLiouville

/-!
# Sturm's oscillation theorem

For `u'' = (Q - μ₁) u` and `v'' = (Q - μ₂) v` with `μ₁ < μ₂`, the Wronskian
`W = u' v - u v'` satisfies `W' = (μ₂ - μ₁) u v`. If `u` has no zero in `(a, b)` and each end
of `[a, b]` is either a zero of `u` or a point where `W` vanishes, then `v` vanishes in
`(a, b)`. Counting over consecutive zeros, if `u`, `v` have proportional data at `0`, then `v`
has at least as many zeros in `(0, X)` as `u` has in `(0, X]`, and one more when
`u'(X) = v'(X) = 0`.

From this and the deformation argument of `DLMFMathlib/Analysis/ODE/SturmDeformation.lean` we
prove **Sturm's oscillation theorem** for the separated problems of
`DLMFMathlib/Analysis/ODE/SturmLiouville.lean` (`w'' = (V - h) w` on `[0, L]`, `V`
continuous and bounded, Dirichlet or Neumann conditions at each end): the eigenfunction of the
`k`-th eigenvalue has exactly `k` zeros in `(0, L)`. Every Dirichlet gap contains a Neumann
eigenvalue.

## Main definitions

* `basicSolutionZeroCount`: the number of zeros of the basic solution in `(0, X]`.

## Main results

* `ncard_basicSolution_zeros_eq_ncard_separatedSpectrum_inter_Iio`,
  `encard_basicSolution_zeros_eq_encard_separatedSpectrum_inter_Iio`: Sturm's oscillation
  theorem for the basic solution.
* `encard_zeros_eq_encard_separatedSpectrum_inter_Iio_of_isSturmLiouvilleSolution`: the same
  for an arbitrary nonzero eigenfunction.
* `basicSolutionZeroCount_eq_ncard_dirichlet_eigenvalues_le`: the zero count in `(0, L]`
  equals the number of Dirichlet eigenvalues `≤ h`, for every `h`.
* `basicSolutionZeroCount_eq_ncard_neumann_eigenvalues`: the zero count at a Neumann
  eigenvalue.
* `separatedSpectrum_true_eq`, `separatedSpectrum_false_eq`: the Dirichlet and Neumann spectra
  at `L` as zero sets of the basic solution and its derivative.
* `neg_one_pow_mul_basicSolution_pos_of_mem_separatedSpectrum_false`,
  `neg_one_pow_mul_deriv_basicSolution_pos_of_mem_separatedSpectrum_true`: signs at `L` of the
  `k`-th eigenfunction.
-/

@[expose] public section

open Set Filter Topology

namespace ODE

/-- A continuous function positive on `(a, b)` is nonnegative at `a`. -/
private lemma nonneg_left_of_pos_Ioo {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f) (hab : a < b)
    (h : ∀ x ∈ Ioo a b, 0 < f x) : 0 ≤ f a :=
  ge_of_tendsto (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (Filter.eventually_of_mem (Ioo_mem_nhdsGT hab) fun x hx => (h x hx).le)

/-- A continuous function positive on `(a, b)` is nonnegative at `b`. -/
private lemma nonneg_right_of_pos_Ioo {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f) (hab : a < b)
    (h : ∀ x ∈ Ioo a b, 0 < f x) : 0 ≤ f b :=
  ge_of_tendsto (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (Filter.eventually_of_mem (Ioo_mem_nhdsLT hab) fun x hx => (h x hx).le)

variable {Q u u' v v' : ℝ → ℝ} {μ₁ μ₂ a b : ℝ}

/-- **Core of the comparison.** With `μ₁ < μ₂`, `u, v > 0` on `(a, b)`, and at each end
either `u = 0` or `W = u' v - u v' = 0`, we get a contradiction: `W` increases strictly. -/
private lemma sturm_comparison_false (hμ : μ₁ < μ₂) (hab : a < b) (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : ∀ x, HasDerivAt u' ((Q x - μ₁) * u x) x) (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((Q x - μ₂) * v x) x) (hup : ∀ x ∈ Ioo a b, 0 < u x)
    (hvp : ∀ x ∈ Ioo a b, 0 < v x) (ha : u a = 0 ∨ u' a * v a - u a * v' a = 0)
    (hb : u b = 0 ∨ u' b * v b - u b * v' b = 0) : False := by
  set W : ℝ → ℝ := fun x => u' x * v x - u x * v' x
  have hW : ∀ x, HasDerivAt W ((μ₂ - μ₁) * (u x * v x)) x := fun x =>
    (((hu' x).mul (hv x)).sub ((hu x).mul (hv' x))).congr_deriv (by ring)
  have hmono : StrictMonoOn W (Icc a b) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc a b)
      (fun x _ => (hW x).continuousAt.continuousWithinAt) (fun x _ => (hW x).hasDerivWithinAt)
      fun x hx => by
        rw [interior_Icc] at hx
        have := hup x hx; have := hvp x hx
        have : 0 < μ₂ - μ₁ := by linarith
        positivity
  have hlt : W a < W b := hmono ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
  have hvc : Continuous v := continuous_iff_continuousAt.mpr fun x => (hv x).continuousAt
  have hWa : 0 ≤ W a := by
    rcases ha with h | h
    · have h1 := nonneg_of_hasDerivAt_of_eq_zero_left hab (hu a) h fun x hx => (hup x hx).le
      have h2 := nonneg_left_of_pos_Ioo hvc hab hvp
      simp only [W, h, zero_mul, sub_zero]; positivity
    · exact h.symm.le
  have hWb : W b ≤ 0 := by
    rcases hb with h | h
    · have h1 := nonpos_of_hasDerivAt_of_eq_zero_right hab (hu b) h fun x hx => (hup x hx).le
      have h2 := nonneg_right_of_pos_Ioo hvc hab hvp
      simp only [W, h, zero_mul, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg h1 h2
    · exact h.le
  linarith

/-- **Comparison in the parameter.** Let `μ₁ < μ₂`, `u'' = (Q - μ₁) u`, `v'' = (Q - μ₂) v`,
`u ≠ 0` on `(a, b)`, and at each end either `u = 0` or `u' v - u v' = 0`. Then `v` vanishes
somewhere in `(a, b)`. -/
private lemma sturm_comparison_exists_zero (hμ : μ₁ < μ₂) (hab : a < b)
    (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : ∀ x, HasDerivAt u' ((Q x - μ₁) * u x) x) (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((Q x - μ₂) * v x) x) (hu0 : ∀ x ∈ Ioo a b, u x ≠ 0)
    (ha : u a = 0 ∨ u' a * v a - u a * v' a = 0)
    (hb : u b = 0 ∨ u' b * v b - u b * v' b = 0) : ∃ x ∈ Ioo a b, v x = 0 := by
  by_contra hcon
  push Not at hcon
  have huc : Continuous u := continuous_iff_continuousAt.mpr fun x => (hu x).continuousAt
  have hvc : Continuous v := continuous_iff_continuousAt.mpr fun x => (hv x).continuousAt
  have sign : ∀ {f : ℝ → ℝ}, Continuous f → (∀ x ∈ Ioo a b, f x ≠ 0) →
      ∃ σ : ℝ, σ ≠ 0 ∧ ∀ x ∈ Ioo a b, 0 < σ * f x := by
    intro f hf h0
    rcases pos_or_neg_of_ne_zero hf.continuousOn h0 with h | h
    · exact ⟨1, one_ne_zero, fun x hx => by simpa using h x hx⟩
    · exact ⟨-1, by norm_num, fun x hx => by have := h x hx; linarith⟩
  obtain ⟨σ, hσ, hσu⟩ := sign huc hu0
  obtain ⟨τ, hτ, hτv⟩ := sign hvc hcon
  refine sturm_comparison_false (Q := Q) (u := fun x => σ * u x) (u' := fun x => σ * u' x)
    (v := fun x => τ * v x) (v' := fun x => τ * v' x) hμ hab (fun x => (hu x).const_mul σ)
    (fun x => ((hu' x).const_mul σ).congr_deriv (by ring)) (fun x => (hv x).const_mul τ)
    (fun x => ((hv' x).const_mul τ).congr_deriv (by ring)) hσu hτv ?_ ?_
  · rcases ha with h | h
    · left; simp [h]
    · right; linear_combination σ * τ * h
  · rcases hb with h | h
    · left; simp [h]
    · right; linear_combination σ * τ * h

/-- **Counting comparison.** Let `μ₁ < μ₂`, `u'' = (Q - μ₁) u`, `v'' = (Q - μ₂) v` with
`u' v - u v' = 0` at `0`, and `X > 0`. If `u` has finitely many zeros in `(0, X]`, then `v`
has at least as many zeros in `(0, X)` (one in each gap between consecutive zeros of `u`,
starting from `0`). -/
private lemma sturm_comparison_ncard_zeros_le (hμ : μ₁ < μ₂) {X : ℝ} (hX : 0 < X)
    (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : ∀ x, HasDerivAt u' ((Q x - μ₁) * u x) x) (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((Q x - μ₂) * v x) x) (hW0 : u' 0 * v 0 - u 0 * v' 0 = 0)
    (hfin : {x | x ∈ Ioc 0 X ∧ u x = 0}.Finite) (hfin' : {x | x ∈ Ioo 0 X ∧ v x = 0}.Finite) :
    {x | x ∈ Ioc 0 X ∧ u x = 0}.ncard + (if u' X = 0 ∧ v' X = 0 ∧ u X ≠ 0 then 1 else 0) ≤
      {x | x ∈ Ioo 0 X ∧ v x = 0}.ncard := by
  classical
  set Z := {x | x ∈ Ioc 0 X ∧ u x = 0} with hZ
  set F := hfin.toFinset
  have hF : ∀ x, x ∈ F ↔ x ∈ Z := fun x => hfin.mem_toFinset
  -- the previous zero (or `0`)
  set prev : ℝ → ℝ := fun z => (insert 0 (F.filter (· < z))).max' (Finset.insert_nonempty _ _)
  have hprev0 : ∀ z, 0 ≤ prev z := fun z => Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  have hprevlt : ∀ z ∈ Z, prev z < z := by
    intro z hz
    refine (Finset.max'_lt_iff _ _).mpr fun y hy => ?_
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hz.1.1
    · exact (Finset.mem_filter.mp hy).2
  have hprevmem : ∀ z, prev z = 0 ∨ prev z ∈ Z := by
    intro z
    rcases Finset.mem_insert.mp (Finset.max'_mem (insert 0 (F.filter (· < z)))
      (Finset.insert_nonempty _ _)) with h | h
    · exact Or.inl h
    · exact Or.inr ((hF _).mp (Finset.mem_filter.mp h).1)
  have hle_prev : ∀ z y, y ∈ Z → y < z → y ≤ prev z := fun z y hy hyz =>
    Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨(hF y).mpr hy, hyz⟩))
  have hgap : ∀ z ∈ Z, ∃ x ∈ Ioo (prev z) z, v x = 0 := by
    intro z hz
    refine sturm_comparison_exists_zero hμ (hprevlt z hz) hu hu' hv hv' (fun x hx h0 => ?_) ?_
      (Or.inl hz.2)
    · have hxZ : x ∈ Z := ⟨⟨(hprev0 z).trans_lt hx.1, hx.2.le.trans hz.1.2⟩, h0⟩
      exact absurd (hle_prev z x hxZ hx.2) (not_le.mpr hx.1)
    · rcases hprevmem z with h | h
      · right; rw [h]; exact hW0
      · left; exact h.2
  choose! φ hφ hφ0 using hgap
  have hφmem : ∀ z ∈ Z, φ z ∈ {x | x ∈ Ioo 0 X ∧ v x = 0} := fun z hz =>
    ⟨⟨(hprev0 z).trans_lt (hφ z hz).1, (hφ z hz).2.trans_le hz.1.2⟩, hφ0 z hz⟩
  have hφlt : ∀ z ∈ Z, ∀ z' ∈ Z, z < z' → φ z < φ z' := fun z hz z' hz' h =>
    ((hφ z hz).2.trans_le (hle_prev z' z hz h)).trans (hφ z' hz').1
  have hinj : InjOn φ Z := by
    intro z hz z' hz' he
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hφlt z hz z' hz' h).ne he
    · exact (hφlt z' hz' z hz h).ne he.symm
  split_ifs with hN
  · -- one more zero in the last gap, where `W(X) = 0`
    set m := (insert 0 F).max' (Finset.insert_nonempty _ _)
    have hm0 : 0 ≤ m := Finset.le_max' _ _ (Finset.mem_insert_self _ _)
    have hZm : ∀ z ∈ Z, z ≤ m := fun z hz =>
      Finset.le_max' _ _ (Finset.mem_insert_of_mem ((hF z).mpr hz))
    have hmmem : m = 0 ∨ m ∈ Z := by
      rcases Finset.mem_insert.mp (Finset.max'_mem (insert 0 F) (Finset.insert_nonempty _ _))
        with h | h
      · exact Or.inl h
      · exact Or.inr ((hF _).mp h)
    have hmX : m < X := by
      rcases hmmem with h | h
      · rw [h]; exact hX
      · exact lt_of_le_of_ne h.1.2 fun he => hN.2.2 (he ▸ h.2)
    obtain ⟨ψ, hψ, hψ0⟩ := sturm_comparison_exists_zero hμ hmX hu hu' hv hv'
      (fun x hx h0 => absurd (hZm x ⟨⟨hm0.trans_lt hx.1, hx.2.le⟩, h0⟩) (not_le.mpr hx.1))
      (by rcases hmmem with h | h
          · right; rw [h]; exact hW0
          · left; exact h.2)
      (Or.inr (by rw [hN.1, hN.2.1]; ring))
    have hXZ : X ∉ Z := fun h => hN.2.2 h.2
    set φ' : ℝ → ℝ := fun z => if z = X then ψ else φ z
    have key := Set.ncard_le_ncard_of_injOn φ' (s := insert X Z)
      (t := {x | x ∈ Ioo 0 X ∧ v x = 0}) ?_ ?_ hfin'
    · rwa [Set.ncard_insert_of_notMem hXZ hfin] at key
    · intro z hz
      rcases mem_insert_iff.mp hz with rfl | hz
      · simp only [φ', ↓reduceIte]
        exact ⟨⟨hm0.trans_lt hψ.1, hψ.2⟩, hψ0⟩
      · have hzX : z ≠ X := fun h => hXZ (h ▸ hz)
        simp only [φ', hzX, ↓reduceIte]
        exact hφmem z hz
    · have hφm : ∀ z ∈ Z, φ z < ψ := fun z hz => ((hφ z hz).2.trans_le (hZm z hz)).trans hψ.1
      intro z hz z' hz' he
      rcases mem_insert_iff.mp hz with rfl | hz <;> rcases mem_insert_iff.mp hz' with rfl | hz'
      · rfl
      · have hzX : z' ≠ z := fun h => hXZ (h ▸ hz')
        simp only [φ', hzX, ↓reduceIte] at he
        exact absurd he.symm (hφm z' hz').ne
      · have hzX : z ≠ z' := fun h => hXZ (h ▸ hz)
        simp only [φ', hzX, ↓reduceIte] at he
        exact absurd he (hφm z hz).ne
      · have h1 : z ≠ X := fun h => hXZ (h ▸ hz)
        have h2 : z' ≠ X := fun h => hXZ (h ▸ hz')
        simp only [φ', h1, h2, ↓reduceIte] at he
        exact hinj hz hz' he
  · simpa using Set.ncard_le_ncard_of_injOn φ hφmem hinj hfin'

/-! ### The oscillation theorem for separated boundary conditions -/

section Osc

variable {V : ℝ → ℝ} {B L : ℝ} {odd0 : Bool}

/-- The number of zeros of the basic solution `basicSolution V odd0 h` in `(0, X]`. -/
noncomputable def basicSolutionZeroCount (V : ℝ → ℝ) (odd0 : Bool) (h X : ℝ) : ℕ :=
  {x | x ∈ Ioc 0 X ∧ basicSolution V odd0 h x = 0}.ncard

/-- At `x`, the function `(basicSolution V odd0 h)` has derivative
`(deriv (basicSolution V odd0 h) x)`. -/
private lemma hasDerivAt_basicSolution (hV : Continuous V) (h x : ℝ) :
    HasDerivAt (basicSolution V odd0 h) (deriv (basicSolution V odd0 h) x) x :=
  (basicSolution_initial_and_isSol hV odd0 h).2.2.hasDerivAt x

/-- At `x`, the function `(deriv (basicSolution V odd0 h))` has derivative
`((V x - h) * basicSolution V odd0 h x)`. -/
private lemma hasDerivAt_deriv_basicSolution (hV : Continuous V) (h x : ℝ) :
    HasDerivAt (deriv (basicSolution V odd0 h)) ((V x - h) * basicSolution V odd0 h x) x :=
  (basicSolution_initial_and_isSol hV odd0 h).2.2.2 x

/-- Nonvanishing under the stated hypotheses: `deriv (basicSolution V odd0 h) x ≠ 0`. -/
private lemma deriv_basicSolution_ne_zero_of_basicSolution_eq_zero (hV : Continuous V) {h x : ℝ}
    (h0 : basicSolution V odd0 h x = 0) :
    deriv (basicSolution V odd0 h) x ≠ 0 := fun h1 =>
  basicSolution_ne_zero hV odd0 h
      (isSturmLiouvilleSolution_eq_zero_of_eq_zero_of_deriv_eq_zero hV
      (basicSolution_initial_and_isSol hV odd0 h).2.2 h0 h1)

/-- Formula under the stated hypotheses: `{x | x ∈ Ioc a b ∧ basicSolution V odd0 h x = 0}.Finite`.
-/
private lemma basicSolution_zeros_Ioc_finite (hV : Continuous V) (h a b : ℝ) :
    {x | x ∈ Ioc a b ∧ basicSolution V odd0 h x = 0}.Finite :=
  (isSturmLiouvilleSolution_zeros_Icc_finite hV (basicSolution_initial_and_isSol hV odd0 h).2.2
      (basicSolution_ne_zero hV odd0 h) a b).subset
    fun _ hx => ⟨Ioc_subset_Icc_self hx.1, hx.2⟩

/-- Formula under the stated hypotheses: `{x | x ∈ Ioo a b ∧ basicSolution V odd0 h x = 0}.Finite`.
-/
private lemma basicSolution_zeros_Ioo_finite (hV : Continuous V) (h a b : ℝ) :
    {x | x ∈ Ioo a b ∧ basicSolution V odd0 h x = 0}.Finite :=
  (basicSolution_zeros_Ioc_finite hV h a b).subset fun _ hx => ⟨Ioo_subset_Ioc_self hx.1, hx.2⟩

/-- Identity under the stated parameter and domain assumptions:
`deriv (basicSolution V odd0 h) 0 * basicSolution V odd0 h' 0 - basicSolution V odd0 h 0 * deriv
(basicSolution V odd0 h') 0 = 0`. -/
private lemma basicSolution_wronskian_zero_eq_zero (hV : Continuous V) (h h' : ℝ) :
    deriv (basicSolution V odd0 h) 0 * basicSolution V odd0 h' 0 - basicSolution V odd0 h 0 *
        deriv (basicSolution V odd0 h') 0
      = 0 := by
  rw [(basicSolution_initial_and_isSol hV odd0 h).1,
      (basicSolution_initial_and_isSol hV odd0 h).2.1,
      (basicSolution_initial_and_isSol hV odd0 h').1,
    (basicSolution_initial_and_isSol hV odd0 h').2.1]; ring

/-- Uniformly near `h₀`, the basic solution is positive on `(0, δ]`. -/
private lemma eventually_basicSolution_pos_Ioc (hV : Continuous V) (hB : ∀ x, |V x| ≤ B) (h₀ : ℝ) :
    ∃ δ > 0, ∀ᶠ h in 𝓝 h₀, ∀ x ∈ Ioc 0 δ, 0 < basicSolution V odd0 h x := by
  obtain ⟨c1, c2⟩ := continuous_uncurry_basicSolution hV hB odd0
  cases odd0
  · have h1 : (0 : ℝ) < Function.uncurry (basicSolution V false) (h₀, 0) := by
      simp [(basicSolution_initial_and_isSol hV false h₀).1, basicInitValue]
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
      (c1.continuousAt.eventually (lt_mem_nhds h1))
    refine ⟨ε / 2, by positivity, ?_⟩
    filter_upwards [Metric.ball_mem_nhds h₀ hε] with h hh x hx
    have := @hball (h, x) (by
      rw [Prod.dist_eq, max_lt_iff]
      refine ⟨hh, ?_⟩
      rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]; linarith [hx.2])
    simpa using this
  · have h1 : (0 : ℝ) < Function.uncurry (fun h x => deriv (basicSolution V true h) x) (h₀, 0) := by
      simp [(basicSolution_initial_and_isSol hV true h₀).2.1, basicInitSlope]
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
      (c2.continuousAt.eventually (lt_mem_nhds h1))
    refine ⟨ε / 2, by positivity, ?_⟩
    filter_upwards [Metric.ball_mem_nhds h₀ hε] with h hh x hx
    have hpos : ∀ t ∈ interior (Icc 0 x), 0 < deriv (basicSolution V true h) t := fun t ht => by
      rw [interior_Icc] at ht
      have := @hball (h, t) (by
        rw [Prod.dist_eq, max_lt_iff]
        refine ⟨hh, ?_⟩
        rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]; linarith [hx.2, ht.2])
      simpa using this
    have hm := strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 x)
      (fun t _ => (hasDerivAt_basicSolution hV h t).continuousAt.continuousWithinAt)
      (fun t _ => (hasDerivAt_basicSolution hV h t).hasDerivWithinAt) hpos
    have := hm (left_mem_Icc.2 hx.1.le) (right_mem_Icc.2 hx.1.le) hx.1
    simpa [(basicSolution_initial_and_isSol hV true h).1, basicInitValue] using this

/-- Below the potential, `y y'` is positive on `(0, ∞)`. -/
private lemma basicSolution_mul_deriv_pos_of_lt_neg (hV : Continuous V) (hB : ∀ x, |V x| ≤ B)
    {h : ℝ} (hh : h < -B) {x : ℝ}
    (hx : 0 < x) : 0 < basicSolution V odd0 h x * deriv (basicSolution V odd0 h) x := by
  set y := basicSolution V odd0 h
  have hE : ∀ t, HasDerivAt (fun t => y t * deriv y t)
      (deriv y t ^ 2 + (V t - h) * y t ^ 2) t := fun t =>
    ((hasDerivAt_basicSolution hV h t).mul
        (hasDerivAt_deriv_basicSolution hV h t)).congr_deriv (by ring)
  have hpos : ∀ t, 0 < deriv y t ^ 2 + (V t - h) * y t ^ 2 := fun t => by
    have hVt : 0 < V t - h := by linarith [neg_abs_le (V t), hB t]
    by_cases h0 : y t = 0
    · have := deriv_basicSolution_ne_zero_of_basicSolution_eq_zero hV h0
      have := pow_pos (abs_pos.2 this) 2
      rw [sq_abs] at this
      nlinarith [sq_nonneg (y t)]
    · have := pow_pos (abs_pos.2 h0) 2
      rw [sq_abs] at this
      nlinarith [sq_nonneg (deriv y t), mul_pos hVt this]
  have hm := strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 x)
    (fun t _ => (hE t).continuousAt.continuousWithinAt) (fun t _ => (hE t).hasDerivWithinAt)
    (fun t _ => hpos t)
  have := hm (left_mem_Icc.2 hx.le) (right_mem_Icc.2 hx.le) hx
  have h00 : y 0 * deriv y 0 = 0 := by
    simp only [y]; rw [(basicSolution_initial_and_isSol hV odd0 h).1,
        (basicSolution_initial_and_isSol hV odd0 h).2.1]
    cases odd0 <;> simp [basicInitValue, basicInitSlope]
  linarith

/-- **Local constancy of the zero count** in `(0, X]` while `X` is not a zero. -/
private lemma eventually_basicSolutionZeroCount_eq (hV : Continuous V) (hB : ∀ x, |V x| ≤ B)
    {h₀ X : ℝ} (hX : 0 < X)
    (hY : basicSolution V odd0 h₀ X ≠ 0) : ∀ᶠ h in 𝓝 h₀, basicSolutionZeroCount V odd0 h X =
        basicSolutionZeroCount V odd0 h₀ X := by
  obtain ⟨δ, hδ, hev⟩ := eventually_basicSolution_pos_Ioc (odd0 := odd0) hV hB h₀
  set δ' := min δ (X / 2)
  have hδ' : 0 < δ' := by positivity
  have hδ'X : δ' < X := (min_le_right _ _).trans_lt (by linarith)
  have hev' : ∀ᶠ h in 𝓝 h₀, ∀ x ∈ Ioc 0 δ', 0 < basicSolution V odd0 h x :=
    hev.mono fun h hh x hx => hh x ⟨hx.1, hx.2.trans (min_le_left _ _)⟩
  have key : ∀ h, (∀ x ∈ Ioc 0 δ', 0 < basicSolution V odd0 h x) →
      {x | x ∈ Ioc 0 X ∧ basicSolution V odd0 h x = 0} =
          {x | x ∈ Icc δ' X ∧ basicSolution V odd0 h x = 0} := by
    intro h hh
    ext x
    simp only [mem_ofPred_eq, mem_Ioc, mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨?_, h2⟩, h3⟩
      by_contra hlt
      have := hh x ⟨h1, (not_le.1 hlt).le⟩
      linarith
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨hδ'.trans_le h1, h2⟩, h3⟩
  obtain ⟨c1, c2⟩ := continuous_uncurry_basicSolution hV hB odd0
  have hst := SturmDeformation.eventually_ncard_eq (T := ℝ) (Y := basicSolution V odd0)
    (Y' := fun h x => deriv (basicSolution V odd0 h) x) (Λ := univ) (U := univ)
        isOpen_univ isOpen_univ
    (a := δ') (b := X) (subset_univ _) c1.continuousOn c2.continuousOn
    (fun t _ x _ => hasDerivAt_basicSolution hV t x)
        (fun t _ x _ h0 => deriv_basicSolution_ne_zero_of_basicSolution_eq_zero hV h0)
    (mem_univ h₀) (hev'.self_of_nhds δ' ⟨hδ', le_rfl⟩).ne' hY
  filter_upwards [hev', hst] with h hh hs
  simp only [basicSolutionZeroCount]
  rw [key h hh, key h₀ hev'.self_of_nhds, hs]

/-- A set meeting every `(-∞, c)` in a finite set is discrete. -/
private lemma exists_isolated_of_inter_Iio_finite {S : Set ℝ}
    (hfin : ∀ c, (S ∩ Iio c).Finite) (h₀ : ℝ) :
    ∃ ε > 0, ∀ h ∈ S, |h - h₀| < ε → h = h₀ := by
  set T : Set ℝ := (S ∩ Iio (h₀ + 1)) \ {h₀}
  have hT : IsOpen Tᶜ := ((hfin _).sdiff).isClosed.isOpen_compl
  have hmem : h₀ ∈ Tᶜ := fun h => h.2 rfl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hT h₀ hmem
  refine ⟨min ε 1, by positivity, fun h hS hh => ?_⟩
  by_contra hne
  have hlt : h < h₀ + 1 := by linarith [(abs_lt.1 hh).2, min_le_right ε 1]
  exact hball (show dist h h₀ < ε by
    rw [Real.dist_eq]; exact hh.trans_le (min_le_left _ _)) ⟨⟨hS, hlt⟩, hne⟩

/-- Identity under the stated parameter and domain assumptions: `S ∩ Iic h = S ∩ Iio h₀`. -/
private lemma inter_Iic_eq_inter_Iio_of_isolated_left {S : Set ℝ} {ε h₀ h : ℝ}
    (hiso : ∀ t ∈ S, |t - h₀| < ε → t = h₀)
    (hh : h ∈ Ioo (h₀ - ε) h₀) : S ∩ Iic h = S ∩ Iio h₀ := by
  ext t
  simp only [mem_inter_iff, mem_Iic, mem_Iio]
  constructor
  · rintro ⟨hS, ht⟩; exact ⟨hS, ht.trans_lt hh.2⟩
  · rintro ⟨hS, ht⟩
    refine ⟨hS, ?_⟩
    by_contra hlt
    have := hiso t hS (abs_lt.2 ⟨by linarith [hh.1], by linarith [hh.1, hh.2]⟩)
    linarith

/-- Identity under the stated parameter and domain assumptions: `S ∩ Iic h = S ∩ Iic h₀`. -/
private lemma inter_Iic_eq_inter_Iic_of_isolated_right {S : Set ℝ} {ε h₀ h : ℝ}
    (hiso : ∀ t ∈ S, |t - h₀| < ε → t = h₀)
    (hh : h ∈ Ico h₀ (h₀ + ε)) : S ∩ Iic h = S ∩ Iic h₀ := by
  ext t
  simp only [mem_inter_iff, mem_Iic]
  constructor
  · rintro ⟨hS, ht⟩
    refine ⟨hS, ?_⟩
    by_contra hlt
    have := hiso t hS (abs_lt.2 ⟨by linarith [hh.1, hh.2], by linarith [hh.2]⟩)
    linarith
  · rintro ⟨hS, ht⟩; exact ⟨hS, ht.trans hh.1⟩

/-- Identity under the stated parameter and domain assumptions: `S ∩ Iic h₀ = insert h₀ (S ∩ Iio
h₀)`. -/
private lemma inter_Iic_eq_insert_inter_Iio {S : Set ℝ} {h₀ : ℝ} (hS : h₀ ∈ S) :
    S ∩ Iic h₀ = insert h₀ (S ∩ Iio h₀) := by
  ext t
  simp only [mem_inter_iff, mem_Iic, mem_Iio, mem_insert_iff]
  constructor
  · rintro ⟨h1, h2⟩
    rcases h2.lt_or_eq with h | h
    · exact Or.inr ⟨h1, h⟩
    · exact Or.inl h
  · rintro (rfl | ⟨h1, h2⟩)
    · exact ⟨hS, le_rfl⟩
    · exact ⟨h1, h2.le⟩

/-- Identity under the stated parameter and domain assumptions: `(S ∩ Iic h₀).ncard = (S ∩ Iio
h₀).ncard + 1`. -/
private lemma ncard_inter_Iic_eq_ncard_inter_Iio_add_one {S : Set ℝ}
    (hfin : ∀ c, (S ∩ Iio c).Finite) {h₀ : ℝ} (hS : h₀ ∈ S) :
    (S ∩ Iic h₀).ncard = (S ∩ Iio h₀).ncard + 1 := by
  rw [inter_Iic_eq_insert_inter_Iio hS, Set.ncard_insert_of_notMem (by simp) (hfin _)]

/-- **The zero count near a zero at the end.** If `y(e, X) = 0`, then for some small `δ` and all
`h` near `e`, the zeros in `(0, X]` are those in `(0, X - δ]` plus exactly one more when
`y'(e, X) y(h, X) ≥ 0`, and no more when `y'(e, X) y(h, X) < 0`. -/
private lemma eventually_basicSolutionZeroCount_eq_near_zero_endpoint (hV : Continuous V)
    (hB : ∀ x, |V x| ≤ B) {e X : ℝ} (hX : 0 < X)
    (he : basicSolution V odd0 e X = 0) :
    ∃ δ, 0 < δ ∧ δ < X ∧ basicSolution V odd0 e (X - δ) ≠ 0 ∧ ∀ᶠ h in 𝓝 e,
      (0 ≤ deriv (basicSolution V odd0 e) X * basicSolution V odd0 h X →
        basicSolutionZeroCount V odd0 h X = basicSolutionZeroCount V odd0 h (X - δ) + 1) ∧
      (deriv (basicSolution V odd0 e) X * basicSolution V odd0 h X < 0 →
        basicSolutionZeroCount V odd0 h X = basicSolutionZeroCount V odd0 h (X - δ)) := by
  set s := deriv (basicSolution V odd0 e) X
  have hs : s ≠ 0 := deriv_basicSolution_ne_zero_of_basicSolution_eq_zero hV he
  obtain ⟨c1, c2⟩ := continuous_uncurry_basicSolution hV hB odd0
  have h1 : (0 : ℝ) < (fun p : ℝ × ℝ => s * deriv (basicSolution V odd0 p.1) p.2) (e, X) := by
    exact mul_self_pos.2 hs
  have hc : Continuous fun p : ℝ × ℝ => s * deriv (basicSolution V odd0 p.1) p.2 :=
    continuous_const.mul c2
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
    (hc.continuousAt.eventually (lt_mem_nhds h1))
  set δ := min (ε / 2) (X / 2)
  have hδ : 0 < δ := by positivity
  have hδX : δ < X := (min_le_right _ _).trans_lt (by linarith)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  -- strict monotonicity of `s y(h, ·)` on `[X - δ, X]`
  have hmono : ∀ h, dist h e < ε →
      StrictMonoOn (fun x => s * basicSolution V odd0 h x) (Icc (X - δ) X) :=
    fun h hh => strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
      (fun t _ => ((hasDerivAt_basicSolution hV h t).const_mul s).continuousAt.continuousWithinAt)
      (fun t _ => ((hasDerivAt_basicSolution hV h t).const_mul s).hasDerivWithinAt) fun t ht => by
        rw [interior_Icc] at ht
        have := @hball (h, t) (by
          rw [Prod.dist_eq, max_lt_iff]
          refine ⟨hh, ?_⟩
          rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])
        simpa using this
  have hXδ : X - δ ∈ Icc (X - δ) X := left_mem_Icc.2 (by linarith)
  have hXX : X ∈ Icc (X - δ) X := right_mem_Icc.2 (by linarith)
  have hneg : s * basicSolution V odd0 e (X - δ) < 0 := by
    have := hmono e (dist_self e ▸ hε) hXδ hXX (by linarith)
    simpa [he] using this
  refine ⟨δ, hδ, hδX, fun h0 => by simp [h0] at hneg, ?_⟩
  have hcont : Continuous fun h => s * basicSolution V odd0 h (X - δ) :=
    continuous_const.mul (continuous_basicSolution_param hV odd0 _).1
  filter_upwards [Metric.ball_mem_nhds e hε, hcont.continuousAt.eventually (gt_mem_nhds hneg)]
    with h hh hneg'
  have hm := hmono h hh
  have hfin := basicSolution_zeros_Ioc_finite (odd0 := odd0) hV h 0 (X - δ)
  constructor
  · intro hpos
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc (by linarith) (fun t ht =>
      ((hasDerivAt_basicSolution hV h t).const_mul s).continuousAt.continuousWithinAt)
      (show (0 : ℝ) ∈ Icc (s * basicSolution V odd0 h (X - δ)) (s * basicSolution V odd0 h X) from
        ⟨hneg'.le, hpos⟩)
    have hz1 : X - δ < z := by
      rcases hz.1.lt_or_eq with h' | h'
      · exact h'
      · simp only at hz0; rw [← h'] at hz0; linarith
    have hYz : basicSolution V odd0 h z = 0 := by
      simp only at hz0; rcases mul_eq_zero.1 hz0 with h' | h'
      · exact absurd h' hs
      · exact h'
    have heq : {x | x ∈ Ioc 0 X ∧ basicSolution V odd0 h x = 0} =
        insert z {x | x ∈ Ioc 0 (X - δ) ∧ basicSolution V odd0 h x = 0} := by
      ext x
      simp only [mem_ofPred_eq, mem_insert_iff, mem_Ioc]
      constructor
      · rintro ⟨⟨hx1, hx2⟩, hx3⟩
        by_cases hxl : x ≤ X - δ
        · exact Or.inr ⟨⟨hx1, hxl⟩, hx3⟩
        · left
          refine hm.injOn ⟨(not_le.1 hxl).le, hx2⟩ hz ?_
          simp only [hx3, hYz]
      · rintro (rfl | ⟨⟨hx1, hx2⟩, hx3⟩)
        · exact ⟨⟨by linarith, hz.2⟩, hYz⟩
        · exact ⟨⟨hx1, by linarith⟩, hx3⟩
    simp only [basicSolutionZeroCount]
    rw [heq, Set.ncard_insert_of_notMem (fun h' => by linarith [h'.1.2]) hfin]
  · intro hneg2
    have heq : {x | x ∈ Ioc 0 X ∧ basicSolution V odd0 h x = 0} =
        {x | x ∈ Ioc 0 (X - δ) ∧ basicSolution V odd0 h x = 0} := by
      ext x
      simp only [mem_ofPred_eq, mem_Ioc]
      constructor
      · rintro ⟨⟨hx1, hx2⟩, hx3⟩
        refine ⟨⟨hx1, ?_⟩, hx3⟩
        by_contra hxl
        have hxI : x ∈ Icc (X - δ) X := ⟨(not_le.1 hxl).le, hx2⟩
        have := hm.monotoneOn hxI hXX hx2
        simp only [hx3, mul_zero] at this
        linarith
      · rintro ⟨⟨hx1, hx2⟩, hx3⟩
        exact ⟨⟨hx1, by linarith⟩, hx3⟩
    simp only [basicSolutionZeroCount]
    rw [heq]

/-- Estimate under the stated parameter and domain assumptions:
`basicSolutionZeroCount V odd0 h X ≤ basicSolutionZeroCount V odd0 h X'`. -/
private lemma basicSolutionZeroCount_mono (hV : Continuous V) (h : ℝ) {X X' : ℝ} (hXX : X ≤ X') :
    basicSolutionZeroCount V odd0 h X ≤ basicSolutionZeroCount V odd0 h X' :=
  Set.ncard_le_ncard (fun _ hx => ⟨⟨hx.1.1, hx.1.2.trans hXX⟩, hx.2⟩)
      (basicSolution_zeros_Ioc_finite hV h 0 X')

/-- The zeros in `(0, X]` versus `(0, X)` when `X` is a zero. -/
private lemma basicSolutionZeroCount_eq_ncard_Ioo_add_one (hV : Continuous V) {h X : ℝ} (hX : 0 < X)
    (he : basicSolution V odd0 h X = 0) :
    basicSolutionZeroCount V odd0 h X =
        {x | x ∈ Ioo 0 X ∧ basicSolution V odd0 h x = 0}.ncard + 1 := by
  have heq : {x | x ∈ Ioc 0 X ∧ basicSolution V odd0 h x = 0} =
      insert X {x | x ∈ Ioo 0 X ∧ basicSolution V odd0 h x = 0} := by
    ext x
    simp only [mem_ofPred_eq, mem_insert_iff, mem_Ioc, mem_Ioo]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rcases h2.lt_or_eq with h' | h'
      · exact Or.inr ⟨⟨h1, h'⟩, h3⟩
      · exact Or.inl h'
    · rintro (rfl | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨⟨hX, le_rfl⟩, he⟩
      · exact ⟨⟨h1, h2.le⟩, h3⟩
  simp only [basicSolutionZeroCount]
  rw [heq, Set.ncard_insert_of_notMem (by simp) (basicSolution_zeros_Ioo_finite hV h 0 X)]

/-- Formula under the stated hypotheses:
`basicSolutionZeroCount V odd0 h X = {x | x ∈ Ioo 0 X ∧ basicSolution V odd0 h x = 0}.ncard`. -/
private lemma basicSolutionZeroCount_eq_ncard_Ioo {h X : ℝ} (he : basicSolution V odd0 h X ≠ 0) :
    basicSolutionZeroCount V odd0 h X = {x | x ∈ Ioo 0 X ∧ basicSolution V odd0 h x = 0}.ncard := by
  simp only [basicSolutionZeroCount]
  congr 1
  ext x
  simp only [mem_ofPred_eq, mem_Ioc, mem_Ioo]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, lt_of_le_of_ne h2 fun h' => he (h' ▸ h3)⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, h2.le⟩, h3⟩

/-- Monotonicity of the zero count in the parameter (Sturm comparison). -/
private lemma basicSolutionZeroCount_add_le_ncard_Ioo_of_lt (hV : Continuous V) {h₁ h₂ X : ℝ}
    (hh : h₁ < h₂) (hX : 0 < X) :
    basicSolutionZeroCount V odd0 h₁ X +
        (if deriv (basicSolution V odd0 h₁) X = 0 ∧ deriv (basicSolution V odd0 h₂) X = 0 ∧
        basicSolution V odd0 h₁ X ≠ 0 then 1 else 0) ≤
      {x | x ∈ Ioo 0 X ∧ basicSolution V odd0 h₂ x = 0}.ncard :=
  sturm_comparison_ncard_zeros_le hh hX (hasDerivAt_basicSolution hV h₁)
      (hasDerivAt_deriv_basicSolution hV h₁) (hasDerivAt_basicSolution hV h₂)
    (hasDerivAt_deriv_basicSolution hV h₂) (basicSolution_wronskian_zero_eq_zero hV h₁ h₂)
        (basicSolution_zeros_Ioc_finite hV h₁ 0 X)
    (basicSolution_zeros_Ioo_finite hV h₂ 0 X)

/-- **Sturm oscillation, Dirichlet condition at `L`.** The number of zeros of `y(h, ·)` in
`(0, L]` equals the number of Dirichlet eigenvalues `≤ h`. -/
theorem basicSolutionZeroCount_eq_ncard_dirichlet_eigenvalues_le (hV : Continuous V)
    (hB : ∀ x, |V x| ≤ B) (hL : 0 < L)
    (hfin : ∀ c, ({e | basicSolution V odd0 e L = 0} ∩ Iio c).Finite) (h : ℝ) :
    basicSolutionZeroCount V odd0 h L = ({e | basicSolution V odd0 e L = 0} ∩ Iic h).ncard := by
  set D := {e | basicSolution V odd0 e L = 0}
  set g : ℝ → ℤ := fun h => (basicSolutionZeroCount V odd0 h L : ℤ) - ((D ∩ Iic h).ncard : ℤ)
  have hloc : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro h₀
    obtain ⟨ε, hε, hiso⟩ := exists_isolated_of_inter_Iio_finite hfin h₀
    by_cases hD : h₀ ∈ D
    · obtain ⟨δ, hδ, hδL, hYδ, hev⟩ :=
          eventually_basicSolutionZeroCount_eq_near_zero_endpoint (odd0 := odd0) hV hB hL hD
      have hF := eventually_basicSolutionZeroCount_eq (odd0 := odd0) hV hB
          (by linarith : 0 < L - δ) hYδ
      have he0 := (hev.self_of_nhds).1
          (by rw [show basicSolution V odd0 h₀ L = 0 from hD, mul_zero])
      have hcD := ncard_inter_Iic_eq_ncard_inter_Iio_add_one hfin hD
      filter_upwards [hev, hF, Metric.ball_mem_nhds h₀ hε] with h hh hF' hball
      rw [Metric.mem_ball, Real.dist_eq] at hball
      rcases lt_trichotomy h h₀ with hlt | rfl | hgt
      · have h1 : basicSolutionZeroCount V odd0 h L ≤ basicSolutionZeroCount V odd0 h₀ L - 1 := by
          have := basicSolutionZeroCount_add_le_ncard_Ioo_of_lt (odd0 := odd0) hV hlt hL
          have := basicSolutionZeroCount_eq_ncard_Ioo_add_one hV hL hD
          omega
        have h2 : basicSolutionZeroCount V odd0 h (L - δ) ≤ basicSolutionZeroCount V odd0 h L :=
            basicSolutionZeroCount_mono hV h (by linarith)
        have hDl := inter_Iic_eq_inter_Iio_of_isolated_left hiso (h := h)
            ⟨by linarith [(abs_lt.1 hball).1], hlt⟩
        simp only [g]
        rw [hDl]
        omega
      · rfl
      · have h1 : basicSolutionZeroCount V odd0 h₀ L ≤ basicSolutionZeroCount V odd0 h L := by
          have := basicSolutionZeroCount_add_le_ncard_Ioo_of_lt (odd0 := odd0) hV hgt hL
          have := basicSolutionZeroCount_eq_ncard_Ioo (V := V) (odd0 := odd0) (h := h)
              (X := L) (fun h0 => by
            have := hiso h h0 hball; linarith)
          omega
        have h2 : basicSolutionZeroCount V odd0 h L ≤
            basicSolutionZeroCount V odd0 h (L - δ) + 1 := by
          by_cases hs : 0 ≤ deriv (basicSolution V odd0 h₀) L * basicSolution V odd0 h L
          · exact (hh.1 hs).le
          · exact (hh.2 (not_le.1 hs)).le.trans (Nat.le_succ _)
        have hDr := inter_Iic_eq_inter_Iic_of_isolated_right hiso (h := h)
            ⟨hgt.le, by linarith [(abs_lt.1 hball).2]⟩
        simp only [g]
        rw [hDr]
        omega
    · filter_upwards [eventually_basicSolutionZeroCount_eq (odd0 := odd0) hV hB hL hD,
          Metric.ball_mem_nhds h₀ hε]
        with h hF hball
      rw [Metric.mem_ball, Real.dist_eq] at hball
      have hDc : D ∩ Iic h = D ∩ Iic h₀ := by
        rcases lt_or_ge h h₀ with hlt | hge
        · rw [inter_Iic_eq_inter_Iio_of_isolated_left hiso ⟨by linarith [(abs_lt.1 hball).1], hlt⟩]
          ext t
          simp only [mem_inter_iff, mem_Iio, mem_Iic]
          exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.le⟩, fun ⟨h1, h2⟩ =>
            ⟨h1, lt_of_le_of_ne h2 fun h' => hD (h' ▸ h1)⟩⟩
        · exact inter_Iic_eq_inter_Iic_of_isolated_right hiso
              ⟨hge, by linarith [(abs_lt.1 hball).2]⟩
      simp only [g]
      rw [hF, hDc]
  have hlow : g (-B - 1) = 0 := by
    have h1 : basicSolutionZeroCount V odd0 (-B - 1) L = 0 := by
      simp only [basicSolutionZeroCount]
      rw [Set.ncard_eq_zero (basicSolution_zeros_Ioc_finite hV _ 0 L)]
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hx h0
      have := basicSolution_mul_deriv_pos_of_lt_neg (odd0 := odd0) hV hB
          (by linarith : -B - 1 < -B) hx.1
      rw [h0, zero_mul] at this
      exact lt_irrefl _ this
    have h2 : D ∩ Iic (-B - 1) = ∅ := by
      ext e
      simp only [mem_inter_iff, mem_Iic, mem_empty_iff_false, iff_false, not_and]
      intro hD he
      have := basicSolution_mul_deriv_pos_of_lt_neg (odd0 := odd0) hV hB (by linarith : e < -B) hL
      rw [show basicSolution V odd0 e L = 0 from hD, zero_mul] at this
      exact lt_irrefl _ this
    simp only [g, h1, h2, Set.ncard_empty]; rfl
  have := hloc.apply_eq_of_preconnectedSpace h (-B - 1)
  rw [hlow] at this
  simp only [g] at this
  omega

/-- Nonvanishing under the stated hypotheses: `basicSolution V odd0 h X ≠ 0`. -/
theorem basicSolution_ne_zero_of_deriv_eq_zero (hV : Continuous V) {h X : ℝ}
    (h1 : deriv (basicSolution V odd0 h) X = 0) :
    basicSolution V odd0 h X ≠ 0 := fun h0 =>
        deriv_basicSolution_ne_zero_of_basicSolution_eq_zero hV h0 h1

/-- **A Neumann eigenvalue in each Dirichlet gap.** Below each Dirichlet eigenvalue `d` and
above all smaller ones there is an `h` with `y'(h, L) = 0`. -/
private lemma exists_neumann_eigenvalue_in_dirichlet_gap (hV : Continuous V)
    (hB : ∀ x, |V x| ≤ B) (hL : 0 < L)
    (hfin : ∀ c, ({e | basicSolution V odd0 e L = 0} ∩ Iio c).Finite) {d : ℝ}
    (hd : basicSolution V odd0 d L = 0) :
    ∃ e, deriv (basicSolution V odd0 e) L = 0 ∧ e < d ∧
      ∀ d', basicSolution V odd0 d' L = 0 → d' < d → d' < e := by
  set D := {e | basicSolution V odd0 e L = 0}
  set φ : ℝ → ℝ := fun h => basicSolution V odd0 h L * deriv (basicSolution V odd0 h) L
  have hφc : Continuous φ :=
    (continuous_basicSolution_param hV odd0 L).1.mul (continuous_basicSolution_param hV odd0 L).2
  have hdc := fun h =>
      basicSolutionZeroCount_eq_ncard_dirichlet_eigenvalues_le (odd0 := odd0) hV hB hL hfin h
  -- sign of the derivative near an eigenvalue
  have hder : ∀ m, m ∈ D → ∀ᶠ h in 𝓝 m,
      0 < deriv (basicSolution V odd0 m) L * deriv (basicSolution V odd0 h) L := fun m hm => by
    have hc : Continuous fun h => deriv (basicSolution V odd0 m) L *
        deriv (basicSolution V odd0 h) L :=
      continuous_const.mul (continuous_basicSolution_param hV odd0 L).2
    exact hc.continuousAt.eventually
        (lt_mem_nhds (mul_self_pos.2 (deriv_basicSolution_ne_zero_of_basicSolution_eq_zero hV hm)))
  -- Step A: just below `d`
  obtain ⟨h2, h2d, h2c, h2φ⟩ : ∃ h2, h2 < d ∧ (∀ d' ∈ D, d' < d → d' < h2) ∧ φ h2 < 0 := by
    obtain ⟨ε, hε, hiso⟩ := exists_isolated_of_inter_Iio_finite hfin d
    obtain ⟨δ, hδ, hδL, hYδ, hev⟩ :=
        eventually_basicSolutionZeroCount_eq_near_zero_endpoint (odd0 := odd0) hV hB hL hd
    have hF := eventually_basicSolutionZeroCount_eq (odd0 := odd0) hV hB
        (by linarith : 0 < L - δ) hYδ
    have he0 := (hev.self_of_nhds).1 (by rw [hd, mul_zero])
    have hall := ((hev.and (hF.and (hder d hd))).filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsLT (show d - ε < d by linarith))
    obtain ⟨h, ⟨hb, hF', hs⟩, hh⟩ := hall.exists
    refine ⟨h, hh.2, fun d' hd' hlt => ?_, ?_⟩
    · by_contra hge
      have := hiso d' hd' (abs_lt.2 ⟨by linarith [hh.1], by linarith⟩)
      linarith
    · have hc1 := hdc h
      rw [inter_Iic_eq_inter_Iio_of_isolated_left hiso hh] at hc1
      have hc2 := hdc d
      rw [ncard_inter_Iic_eq_ncard_inter_Iio_add_one hfin hd] at hc2
      have hneg : deriv (basicSolution V odd0 d) L * basicSolution V odd0 h L < 0 := by
        by_contra hnn
        have := hb.1 (not_lt.1 hnn)
        omega
      simp only [φ]
      by_contra hφ
      have : 0 ≤ (deriv (basicSolution V odd0 d) L * basicSolution V odd0 h L) *
          (deriv (basicSolution V odd0 d) L * deriv (basicSolution V odd0 h) L) := by
        have := mul_nonneg (not_lt.1 hφ) (mul_self_nonneg (deriv (basicSolution V odd0 d) L))
        nlinarith
      nlinarith
  -- Step B: just above the previous eigenvalue (or far below)
  obtain ⟨h1, h12, h1c, h1φ⟩ : ∃ h1, h1 < h2 ∧ (∀ d' ∈ D, d' < d → d' < h1) ∧ 0 < φ h1 := by
    by_cases hne : (D ∩ Iio d).Nonempty
    · obtain ⟨m, ⟨hmD, hmd⟩, hmax⟩ := Set.exists_max_image (D ∩ Iio d) id (hfin d) hne
      have hm2 : m < h2 := h2c m hmD hmd
      obtain ⟨ε, hε, hiso⟩ := exists_isolated_of_inter_Iio_finite hfin m
      obtain ⟨δ, hδ, hδL, hYδ, hev⟩ :=
          eventually_basicSolutionZeroCount_eq_near_zero_endpoint (odd0 := odd0) hV hB hL hmD
      have hF := eventually_basicSolutionZeroCount_eq (odd0 := odd0) hV hB
          (by linarith : 0 < L - δ) hYδ
      have he0 := (hev.self_of_nhds).1
          (by rw [show basicSolution V odd0 m L = 0 from hmD, mul_zero])
      have hall := ((hev.and (hF.and (hder m hmD))).filter_mono nhdsWithin_le_nhds).and
        (Ioo_mem_nhdsGT (show m < min (m + ε) h2 from lt_min (by linarith) hm2))
      obtain ⟨h, ⟨hb, hF', hs⟩, hh⟩ := hall.exists
      have hh2 : h < h2 := hh.2.trans_le (min_le_right _ _)
      have hnD : basicSolution V odd0 h L ≠ 0 := fun h0 => by
        have := hmax h ⟨h0, hh2.trans h2d⟩
        simp only [id] at this
        linarith [hh.1]
      refine ⟨h, hh2, fun d' hd' hlt => (hmax d' ⟨hd', hlt⟩).trans_lt hh.1, ?_⟩
      have hc1 := hdc h
      rw [inter_Iic_eq_inter_Iic_of_isolated_right hiso ⟨hh.1.le, hh.2.trans_le (min_le_left _ _)⟩,
          ← hdc m] at hc1
      have hpos : 0 < deriv (basicSolution V odd0 m) L * basicSolution V odd0 h L := by
        rcases lt_trichotomy 0 (deriv (basicSolution V odd0 m) L * basicSolution V odd0 h L)
            with h' | h' | h'
        · exact h'
        · exact absurd (mul_eq_zero.1 h'.symm)
              (not_or.2 ⟨deriv_basicSolution_ne_zero_of_basicSolution_eq_zero hV hmD, hnD⟩)
        · have := hb.2 h'
          omega
      simp only [φ]
      have h3 := mul_pos hpos hs
      by_contra hφ
      have h4 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hφ)
        (mul_self_nonneg (deriv (basicSolution V odd0 m) L))
      have e : (deriv (basicSolution V odd0 m) L * basicSolution V odd0 h L) *
          (deriv (basicSolution V odd0 m) L * deriv (basicSolution V odd0 h) L) =
          (basicSolution V odd0 h L * deriv (basicSolution V odd0 h) L) *
            (deriv (basicSolution V odd0 m) L * deriv (basicSolution V odd0 m) L) := by ring
      linarith
    · refine ⟨min (-B - 1) (h2 - 1), (min_le_right _ _).trans_lt (by linarith),
        fun d' hd' hlt => absurd ⟨d', hd', hlt⟩ hne, ?_⟩
      exact basicSolution_mul_deriv_pos_of_lt_neg hV hB
          ((min_le_left _ _).trans_lt (by linarith)) hL
  -- Step C: intermediate values
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' h12.le hφc.continuousOn
    (show (0 : ℝ) ∈ Icc (φ h2) (φ h1) from ⟨h2φ.le, h1φ.le⟩)
  have hcd : c < d := hc.2.trans_lt h2d
  rcases mul_eq_zero.1 hc0 with h0 | h0
  · exact absurd (h1c c h0 hcd) (not_lt.2 hc.1)
  · exact ⟨c, h0, hcd, fun d' hd' hlt => (h1c d' hd' hlt).trans_le hc.1⟩

/-- **Sturm oscillation, Neumann condition at `L`.** At a Neumann eigenvalue `e`, the number
of zeros of `y(e, ·)` in `(0, L]` equals the number of Neumann eigenvalues `< e`. -/
theorem basicSolutionZeroCount_eq_ncard_neumann_eigenvalues (hV : Continuous V)
    (hB : ∀ x, |V x| ≤ B) (hL : 0 < L)
    (hfin : ∀ c, ({e | basicSolution V odd0 e L = 0} ∩ Iio c).Finite)
    (hfinN : ∀ c, ({e | deriv (basicSolution V odd0 e) L = 0} ∩ Iio c).Finite) {e : ℝ}
    (he : deriv (basicSolution V odd0 e) L = 0) :
    basicSolutionZeroCount V odd0 e L =
        ({e | deriv (basicSolution V odd0 e) L = 0} ∩ Iio e).ncard := by
  set D := {e | basicSolution V odd0 e L = 0}
  set Nn := {e | deriv (basicSolution V odd0 e) L = 0}
  have hstrict : ∀ e₁ e₂, e₁ ∈ Nn → e₂ ∈ Nn → e₁ < e₂ →
      basicSolutionZeroCount V odd0 e₁ L < basicSolutionZeroCount V odd0 e₂ L :=
          fun e₁ e₂ h₁ h₂ hlt => by
    have := basicSolutionZeroCount_add_le_ncard_Ioo_of_lt (odd0 := odd0) hV hlt hL
    have hc : deriv (basicSolution V odd0 e₁) L = 0 ∧ deriv (basicSolution V odd0 e₂) L = 0 ∧
        basicSolution V odd0 e₁ L ≠ 0 := ⟨h₁, h₂, basicSolution_ne_zero_of_deriv_eq_zero hV h₁⟩
    simp only [hc, ne_eq, not_false_eq_true, and_self, ↓reduceIte] at this
    rw [← basicSolutionZeroCount_eq_ncard_Ioo
        (basicSolution_ne_zero_of_deriv_eq_zero hV h₂)] at this
    omega
  apply le_antisymm
  · rw [basicSolutionZeroCount_eq_ncard_dirichlet_eigenvalues_le hV hB hL hfin e]
    choose! f hf using fun d (hd : d ∈ D) =>
        exists_neumann_eigenvalue_in_dirichlet_gap (odd0 := odd0) hV hB hL hfin hd
    refine Set.ncard_le_ncard_of_injOn f (fun d hd => ⟨(hf d hd.1).1, ?_⟩) ?_ (hfinN e)
    · exact (hf d hd.1).2.1.trans_le hd.2
    · intro d₁ hd₁ d₂ hd₂ heq
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have h1 := (hf d₂ hd₂.1).2.2 d₁ hd₁.1 hlt
        have h2 := (hf d₁ hd₁.1).2.1
        rw [heq] at h2; linarith
      · have h1 := (hf d₁ hd₁.1).2.2 d₂ hd₂.1 hlt
        have h2 := (hf d₂ hd₂.1).2.1
        rw [← heq] at h2; linarith
  · have := Set.ncard_le_ncard_of_injOn (s := Nn ∩ Iio e)
      (t := ((Finset.range (basicSolutionZeroCount V odd0 e L) : Finset ℕ) : Set ℕ))
          (fun e' => basicSolutionZeroCount V odd0 e' L)
      (fun e' he' => by
        simp only [Finset.coe_range, mem_Iio]
        exact hstrict e' e he'.1 he he'.2)
      (fun e₁ h₁ e₂ h₂ heq => by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact absurd heq (hstrict e₁ e₂ h₁.1 h₂.1 hlt).ne
        · exact absurd heq (hstrict e₂ e₁ h₂.1 h₁.1 hlt).ne')
      (Finset.finite_toSet _)
    rwa [Set.ncard_coe_finset, Finset.card_range] at this

/-- Identity under the stated parameter and domain assumptions:
`separatedSpectrum V L odd0 true = {e | basicSolution V odd0 e L = 0}`. -/
theorem separatedSpectrum_true_eq (hV : Continuous V) (odd0 : Bool) :
    separatedSpectrum V L odd0 true = {e | basicSolution V odd0 e L = 0} := by
  ext e; rw [mem_separatedSpectrum_iff hV]; simp [sturmCharacteristic]

/-- Identity under the stated parameter and domain assumptions:
`separatedSpectrum V L odd0 false = {e | deriv (basicSolution V odd0 e) L = 0}`. -/
theorem separatedSpectrum_false_eq (hV : Continuous V) (odd0 : Bool) :
    separatedSpectrum V L odd0 false = {e | deriv (basicSolution V odd0 e) L = 0} := by
  ext e; rw [mem_separatedSpectrum_iff hV]; simp [sturmCharacteristic]

/-- **Sturm's oscillation theorem** for the separated problem `w'' = (V - h) w` on `[0, L]`
(`V` continuous and bounded, any of the four combinations of Dirichlet/Neumann conditions at
`0` and `L`): at an eigenvalue `h` with exactly `k` smaller eigenvalues, the eigenfunction
`basicSolution V odd0 h` has exactly `k` zeros in `(0, L)`. -/
lemma ncard_basicSolution_zeros_eq_ncard_separatedSpectrum_inter_Iio (hV : Continuous V)
    (hB : ∀ x, |V x| ≤ B) (hL : 0 < L)
    (odd0 oddK : Bool) {h : ℝ} (hh : h ∈ separatedSpectrum V L odd0 oddK) :
    {x | x ∈ Ioo 0 L ∧ basicSolution V odd0 h x = 0}.ncard =
        (separatedSpectrum V L odd0 oddK ∩ Iio h).ncard := by
  have hfin := separatedSpectrum_inter_Iio_finite hV hB hL odd0 oddK
  have hfinD := separatedSpectrum_inter_Iio_finite hV hB hL odd0 true
  rw [separatedSpectrum_true_eq hV] at hfinD
  cases oddK
  · rw [separatedSpectrum_false_eq hV] at hh hfin ⊢
    rw [← basicSolutionZeroCount_eq_ncard_neumann_eigenvalues hV hB hL hfinD hfin hh,
        basicSolutionZeroCount_eq_ncard_Ioo (basicSolution_ne_zero_of_deriv_eq_zero hV hh)]
  · rw [separatedSpectrum_true_eq hV] at hh ⊢
    have h1 := basicSolutionZeroCount_eq_ncard_dirichlet_eigenvalues_le hV hB hL hfinD h
    rw [ncard_inter_Iic_eq_ncard_inter_Iio_add_one hfinD hh,
        basicSolutionZeroCount_eq_ncard_Ioo_add_one hV hL hh] at h1
    omega

/-- `encard` form of `ODE.ncard_basicSolution_zeros_eq_ncard_separatedSpectrum_inter_Iio`. -/
theorem encard_basicSolution_zeros_eq_encard_separatedSpectrum_inter_Iio (hV : Continuous V)
    (hB : ∀ x, |V x| ≤ B) (hL : 0 < L)
    (odd0 oddK : Bool) {h : ℝ} (hh : h ∈ separatedSpectrum V L odd0 oddK) :
    {x | x ∈ Ioo 0 L ∧ basicSolution V odd0 h x = 0}.encard =
        (separatedSpectrum V L odd0 oddK ∩ Iio h).encard := by
  rw [← (basicSolution_zeros_Ioo_finite hV h 0 L).cast_ncard_eq,
    ← (separatedSpectrum_inter_Iio_finite hV hB hL odd0 oddK h).cast_ncard_eq,
    ncard_basicSolution_zeros_eq_ncard_separatedSpectrum_inter_Iio hV hB hL odd0 oddK hh]

/-- **Sturm's oscillation theorem for an arbitrary eigenfunction**: a nonzero solution `w` of
`w'' = (V - h) w` satisfying the separated boundary conditions has as many zeros in `(0, L)`
as there are eigenvalues below `h`. -/
theorem encard_zeros_eq_encard_separatedSpectrum_inter_Iio_of_isSturmLiouvilleSolution
    (hV : Continuous V) (hB : ∀ x, |V x| ≤ B) (hL : 0 < L)
    (odd0 oddK : Bool) {h : ℝ} {w : ℝ → ℝ} (hw : IsSturmLiouvilleSolution V h w)
        (hbc : SatisfiesSeparatedBC L odd0 oddK w)
    (hne : w ≠ 0) :
    {x | x ∈ Ioo 0 L ∧ w x = 0}.encard = (separatedSpectrum V L odd0 oddK ∩ Iio h).encard := by
  have hh : h ∈ separatedSpectrum V L odd0 oddK := ⟨w, hw, hbc, hne⟩
  have heq := isSturmLiouvilleSolution_eq_mul_basicSolution hV hw hbc.1
  set c := if odd0 then deriv w 0 else w 0
  have hc : c ≠ 0 := fun h0 => hne (by rw [heq, h0]; funext x; simp)
  rw [← encard_basicSolution_zeros_eq_encard_separatedSpectrum_inter_Iio hV hB hL odd0 oddK hh]
  congr 1
  ext x
  simp only [mem_ofPred_eq]
  rw [heq]
  simp [hc]

/-- Around a simple zero `z`, `y'(z) y` is negative to the left and positive to the right. -/
private lemma exists_sign_deriv_mul_basicSolution_around_zero (hV : Continuous V) {h z : ℝ}
    (hz : basicSolution V odd0 h z = 0) :
    ∃ η > 0, (∀ x ∈ Ico (z - η) z, deriv (basicSolution V odd0 h) z *
        basicSolution V odd0 h x < 0) ∧
      ∀ x ∈ Ioc z (z + η), 0 < deriv (basicSolution V odd0 h) z * basicSolution V odd0 h x := by
  set s := deriv (basicSolution V odd0 h) z
  have hs : s ≠ 0 := deriv_basicSolution_ne_zero_of_basicSolution_eq_zero hV hz
  have hc : Continuous fun x => s * deriv (basicSolution V odd0 h) x :=
    continuous_const.mul (basicSolution_initial_and_isSol hV odd0 h).2.2.continuous_deriv
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
    (hc.continuousAt.eventually (lt_mem_nhds (show 0 < s * s from mul_self_pos.2 hs)))
  refine ⟨ε / 2, by positivity, ?_⟩
  have hm : StrictMonoOn (fun x => s * basicSolution V odd0 h x) (Icc (z - ε / 2) (z + ε / 2)) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
      (fun t _ => ((hasDerivAt_basicSolution hV h t).const_mul s).continuousAt.continuousWithinAt)
      (fun t _ => ((hasDerivAt_basicSolution hV h t).const_mul s).hasDerivWithinAt) fun t ht => by
        rw [interior_Icc] at ht
        exact hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])
  have hzI : z ∈ Icc (z - ε / 2) (z + ε / 2) := ⟨by linarith, by linarith⟩
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have := hm ⟨hx.1, by linarith [hx.2]⟩ hzI hx.2
    simpa [hz] using this
  · have := hm hzI ⟨by linarith [hx.1], hx.2⟩ hx.1
    simpa [hz] using this

/-- **The sign of the basic solution** at `X > 0` is `(-1)^N`, where `N` is the number of zeros
in `(0, X]`. -/
private lemma neg_one_pow_basicSolutionZeroCount_mul_basicSolution_pos (hV : Continuous V)
    (hB : ∀ x, |V x| ≤ B) (h : ℝ) :
    ∀ k : ℕ, ∀ X, 0 < X → basicSolutionZeroCount V odd0 h X = k → basicSolution V odd0 h X ≠ 0 →
      0 < (-1) ^ k * basicSolution V odd0 h X := by
  have hcY : Continuous (basicSolution V odd0 h) :=
      (basicSolution_initial_and_isSol hV odd0 h).2.2.continuous
  intro k
  induction k with
  | zero =>
    intro X hX hN hY
    obtain ⟨δ, hδ, hev⟩ := eventually_basicSolution_pos_Ioc (odd0 := odd0) hV hB h
    set t := min δ X
    have ht : 0 < basicSolution V odd0 h t := hev.self_of_nhds t ⟨by positivity, min_le_left _ _⟩
    rw [pow_zero, one_mul]
    by_contra hneg
    obtain ⟨w, hw, hw0⟩ := intermediate_value_Icc' (min_le_right δ X) hcY.continuousOn
      (show (0 : ℝ) ∈ Icc (basicSolution V odd0 h X) (basicSolution V odd0 h t)
          from ⟨not_lt.1 hneg, ht.le⟩)
    have hmem : w ∈ {x | x ∈ Ioc 0 X ∧ basicSolution V odd0 h x = 0} :=
      ⟨⟨(show 0 < t by positivity).trans_le hw.1, hw.2⟩, hw0⟩
    have := Set.ncard_pos (basicSolution_zeros_Ioc_finite hV h 0 X) |>.2 ⟨w, hmem⟩
    simp only [basicSolutionZeroCount] at hN
    omega
  | succ k ih =>
    intro X hX hN hY
    set Z := {x | x ∈ Ioc 0 X ∧ basicSolution V odd0 h x = 0}
    have hZf : Z.Finite := basicSolution_zeros_Ioc_finite hV h 0 X
    have hZn : Z.ncard = k + 1 := hN
    have hZne : Z.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨z, hzZ, hzmax⟩ := Set.exists_max_image Z id hZf hZne
    have hzX : z < X := lt_of_le_of_ne hzZ.1.2 fun h' => hY (h' ▸ hzZ.2)
    obtain ⟨ε, hε, hiso⟩ :=
        exists_isolated_of_inter_Iio_finite (S := Z) (fun c => hZf.subset inter_subset_left) z
    obtain ⟨η, hη, hl, hr⟩ :=
        exists_sign_deriv_mul_basicSolution_around_zero (odd0 := odd0) hV hzZ.2
    set s := deriv (basicSolution V odd0 h) z
    -- a point just left of `z`
    set X' := max (max (z - ε / 2) (z / 2)) (z - η)
    have hz0 := hzZ.1.1
    have hX'z : X' < z := max_lt (max_lt (by linarith) (by linarith)) (by linarith)
    have hX'0 : 0 < X' := lt_max_of_lt_left (lt_max_of_lt_right (by linarith))
    have hsX' : s * basicSolution V odd0 h X' < 0 := hl X' ⟨le_max_right _ _, hX'z⟩
    have hNX' : basicSolutionZeroCount V odd0 h X' = k := by
      have heq : Z = insert z {x | x ∈ Ioc 0 X' ∧ basicSolution V odd0 h x = 0} := by
        ext x
        simp only [Z, mem_ofPred_eq, mem_insert_iff, mem_Ioc]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          by_cases hx : x ≤ X'
          · exact Or.inr ⟨⟨h1, hx⟩, h3⟩
          · left
            have hxz : x ≤ z := hzmax x ⟨⟨h1, h2⟩, h3⟩
            refine hiso x ⟨⟨h1, h2⟩, h3⟩ (abs_lt.2 ⟨?_, by linarith⟩)
            have : z - ε / 2 ≤ X' := (le_max_left _ _).trans (le_max_left _ _)
            linarith [not_le.1 hx]
        · rintro (rfl | ⟨⟨h1, h2⟩, h3⟩)
          · exact hzZ
          · exact ⟨⟨h1, by linarith⟩, h3⟩
      have := hZn
      rw [heq, Set.ncard_insert_of_notMem (fun h' => by linarith [h'.1.2])
        (basicSolution_zeros_Ioc_finite hV h 0 X')] at this
      simp only [basicSolutionZeroCount]; omega
    have hYX' : basicSolution V odd0 h X' ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hsX'; exact lt_irrefl _ hsX'
    have hih := ih X' hX'0 hNX' hYX'
    -- the sign at `X`
    have hsX : 0 < s * basicSolution V odd0 h X := by
      set xp := min (z + η) X
      have hxp : 0 < s * basicSolution V odd0 h xp :=
          hr xp ⟨lt_min (by linarith) hzX, min_le_left _ _⟩
      by_contra hneg
      have hc : Continuous fun x => s * basicSolution V odd0 h x := continuous_const.mul hcY
      obtain ⟨w, hw, hw0⟩ := intermediate_value_Icc' (min_le_right (z + η) X) hc.continuousOn
        (show (0 : ℝ) ∈ Icc (s * basicSolution V odd0 h X) (s * basicSolution V odd0 h xp) from
          ⟨not_lt.1 hneg, hxp.le⟩)
      have hwz : z < w := (lt_min (by linarith) hzX).trans_le hw.1
      have hw0' : basicSolution V odd0 h w = 0 := by
        rcases mul_eq_zero.1 hw0 with h' | h'
        · exact absurd h' (deriv_basicSolution_ne_zero_of_basicSolution_eq_zero hV hzZ.2)
        · exact h'
      have := hzmax w ⟨⟨hz0.trans hwz, hw.2⟩, hw0'⟩
      simp only [id] at this
      linarith
    rcases neg_one_pow_eq_or ℝ k with hk | hk
    · rw [hk, one_mul] at hih
      rw [pow_succ, hk]
      nlinarith
    · rw [hk] at hih
      rw [pow_succ, hk]
      nlinarith

/-- At a Neumann eigenvalue `h` (condition `w'(L) = 0`) with `k` smaller eigenvalues, the
basic solution has sign `(-1)^k` at `L`. -/
theorem neg_one_pow_mul_basicSolution_pos_of_mem_separatedSpectrum_false (hV : Continuous V)
    (hB : ∀ x, |V x| ≤ B) (hL : 0 < L)
    (odd0 : Bool) {h : ℝ} (hh : h ∈ separatedSpectrum V L odd0 false) :
    0 < (-1) ^ (separatedSpectrum V L odd0 false ∩ Iio h).ncard * basicSolution V odd0 h L := by
  have hh' : deriv (basicSolution V odd0 h) L = 0 := by rwa [separatedSpectrum_false_eq hV] at hh
  have hY := basicSolution_ne_zero_of_deriv_eq_zero hV hh'
  refine neg_one_pow_basicSolutionZeroCount_mul_basicSolution_pos hV hB h _ L hL ?_ hY
  rw [basicSolutionZeroCount_eq_ncard_Ioo hY,
      ncard_basicSolution_zeros_eq_ncard_separatedSpectrum_inter_Iio hV hB hL odd0 false hh]

/-- Just left of a positive zero `z` there is a point `X'` with no zeros in `(X', z)`. -/
private lemma exists_left_point_basicSolutionZeroCount_eq_add_one (hV : Continuous V) {h z : ℝ}
    (hz0 : 0 < z) (hz : basicSolution V odd0 h z = 0) :
    ∃ X', 0 < X' ∧ X' < z ∧ deriv (basicSolution V odd0 h) z * basicSolution V odd0 h X' < 0 ∧
      basicSolutionZeroCount V odd0 h z = basicSolutionZeroCount V odd0 h X' + 1 := by
  set Z := {x | x ∈ Ioc 0 z ∧ basicSolution V odd0 h x = 0}
  have hZf : Z.Finite := basicSolution_zeros_Ioc_finite hV h 0 z
  have hzZ : z ∈ Z := ⟨⟨hz0, le_rfl⟩, hz⟩
  obtain ⟨ε, hε, hiso⟩ :=
      exists_isolated_of_inter_Iio_finite (S := Z) (fun c => hZf.subset inter_subset_left) z
  obtain ⟨η, hη, hl, -⟩ := exists_sign_deriv_mul_basicSolution_around_zero (odd0 := odd0) hV hz
  set X' := max (max (z - ε / 2) (z / 2)) (z - η)
  have hX'z : X' < z := max_lt (max_lt (by linarith) (by linarith)) (by linarith)
  have hX'0 : 0 < X' := lt_max_of_lt_left (lt_max_of_lt_right (by linarith))
  refine ⟨X', hX'0, hX'z, hl X' ⟨le_max_right _ _, hX'z⟩, ?_⟩
  have heq : Z = insert z {x | x ∈ Ioc 0 X' ∧ basicSolution V odd0 h x = 0} := by
    ext x
    simp only [Z, mem_ofPred_eq, mem_insert_iff, mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases hx : x ≤ X'
      · exact Or.inr ⟨⟨h1, hx⟩, h3⟩
      · left
        refine hiso x ⟨⟨h1, h2⟩, h3⟩ (abs_lt.2 ⟨?_, by linarith⟩)
        have : z - ε / 2 ≤ X' := (le_max_left _ _).trans (le_max_left _ _)
        linarith [not_le.1 hx]
    · rintro (rfl | ⟨⟨h1, h2⟩, h3⟩)
      · exact hzZ
      · exact ⟨⟨h1, by linarith⟩, h3⟩
  show Z.ncard = _
  rw [heq, Set.ncard_insert_of_notMem (fun h' => by linarith [h'.1.2])
    (basicSolution_zeros_Ioc_finite hV h 0 X')]
  rfl

/-- At a positive zero `X`, the derivative has sign `(-1)^N`, `N` the number of zeros in
`(0, X]` (including `X`). -/
private lemma neg_one_pow_basicSolutionZeroCount_mul_deriv_basicSolution_pos (hV : Continuous V)
    (hB : ∀ x, |V x| ≤ B) {h X : ℝ} (hX : 0 < X)
    (hz : basicSolution V odd0 h X = 0) : 0 < (-1) ^ basicSolutionZeroCount V odd0 h X *
        deriv (basicSolution V odd0 h) X := by
  obtain ⟨X', hX'0, -, hs, hN⟩ :=
      exists_left_point_basicSolutionZeroCount_eq_add_one (odd0 := odd0) hV hX hz
  have hY : basicSolution V odd0 h X' ≠ 0 := fun h0 => by rw [h0, mul_zero] at hs;
                                                          exact lt_irrefl _ hs
  have hih := neg_one_pow_basicSolutionZeroCount_mul_basicSolution_pos hV hB h _ X' hX'0 rfl hY
  rw [hN, pow_succ]
  rcases neg_one_pow_eq_or ℝ (basicSolutionZeroCount V odd0 h X') with hk | hk
  · rw [hk] at hih ⊢; nlinarith
  · rw [hk] at hih ⊢; nlinarith

/-- At a Dirichlet eigenvalue `h` (condition `w(L) = 0`) with `k` smaller eigenvalues,
`(-1)^(k+1) y'(h, L) > 0`. -/
theorem neg_one_pow_mul_deriv_basicSolution_pos_of_mem_separatedSpectrum_true (hV : Continuous V)
    (hB : ∀ x, |V x| ≤ B) (hL : 0 < L)
    (odd0 : Bool) {h : ℝ} (hh : h ∈ separatedSpectrum V L odd0 true) :
    0 < (-1) ^ ((separatedSpectrum V L odd0 true ∩ Iio h).ncard + 1) *
        deriv (basicSolution V odd0 h) L := by
  have hh' : basicSolution V odd0 h L = 0 := by rwa [separatedSpectrum_true_eq hV] at hh
  have := neg_one_pow_basicSolutionZeroCount_mul_deriv_basicSolution_pos hV hB hL hh'
  rwa [basicSolutionZeroCount_eq_ncard_Ioo_add_one hV hL hh',
      ncard_basicSolution_zeros_eq_ncard_separatedSpectrum_inter_Iio hV hB hL odd0 true hh] at this

end Osc

end ODE
