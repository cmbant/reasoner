module

public import FormalResearch.ModularBootstrap.Mixtures.O1Lower
public import FormalResearch.ModularBootstrap.Mixtures.O1
public import FormalResearch.ModularBootstrap.Mixtures.Duality

/-!
# Unconditional `pmix:o1` component comparison and `pmix:liminf`

`positive_mixtures.tex`, Corollary PM.7 (`pmix:o1`, `pmix:liminf`):

* `pmix_o1_feasible_of_Smax`: for every `M : MixtureData` and every `c > 0` with `12 * M.Smax ≤ c`,
  there exist `T > 0` and `g ∈ Ā_{w,mix}` feasible at `(c / 12, T)`, discharging the nonemptiness
  hypotheses of `pmix_o1_component_comparison` (`Mixtures/O1Lower.lean`) unconditionally.
* `pmix_o1_component_comparison_unconditional`: unconditionally for all `c > 0` with `12 * M.Smax ≤ c`,
  `min_i (M.Q i).T_weak (c - 12 * M.r i) ≤ M.toSource.T_weak c ≤ M.toSource.T_V c` and
  `min_i (M.Q i).T_V (c - 12 * M.r i) ≤ M.toSource.T_V c`.
* `pmix_o1_component_strict_gt`: if `12 * M.Smax ≤ c` and `∀ i, 12 * M.r i < c` and some component has
  `(M.Q i*).T_weak (c - 12 * M.r i*) > min_j (M.Q j).T_V (c - 12 * M.r j)`, then the strict
  comparison `min_j (M.Q j).T_V (c - 12 * M.r j) < M.toSource.T_V c` is strict.
* `pmix_liminf_of_component_c0`: `pmix:liminf` from single-component weak asymptotic lower bounds
  `(M.Q i).T_weak n ≥ T_*(n) + c₀*(i) - o(1)` (discharged from `ctu:c0` + `int:strict-weak`).

Each result is proved; `pmix_liminf_of_component_c0` is conditional on the component lower bounds `hcomp` (the identification `c0 i = c₀*(w, Q_i)`, via `ctu:c0` and `int:strict-weak`, is not formalised).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Duality FormalResearch.ModularBootstrap.FixedWeight

/-! ### 1. Unconditional nonemptiness and component comparisons -/

/-- For every `M : MixtureData` and every `c > 0` with `12 * M.Smax ≤ c`, the strict (and hence weak)
feasible threshold set of `M.toSource` at `c` is nonempty and `T_weak ≤ T_V`. -/
theorem pmix_o1_feasible_of_Smax (M : MixtureData) {c : ℝ} (hc0 : 0 < c) (hc : 12 * M.Smax ≤ c) :
    (∃ T : ℝ, 0 < T ∧ ∃ g, M.toSource.IsFeasible (c / 12) T g) ∧
    (∃ T : ℝ, 0 < T ∧ ∃ g, M.toSource.IsWeaklyFeasible (c / 12) T g) ∧
    M.toSource.T_weak c ≤ M.toSource.T_V c := by
  obtain ⟨β₀, hβ₀pos, hβ₀2, hβ₀t⟩ := exists_beta0 M.w one_pos
  have hS : SourceDualSetupCore M.toSource c β₀ 1 :=
    SourceDualSetupCore.of_mixture M hc0 hc hβ₀pos hβ₀2 hβ₀t one_pos
  obtain ⟨_, T, hT0, ⟨g, hg⟩, _⟩ := T_V_lt_top_of_core hS
  have hgw : M.toSource.IsWeaklyFeasible (c / 12) T g :=
    ⟨hg.1, by
      by_contra h0
      push Not at h0
      have hv0 : M.toSource.gVac (c / 12) g = 0 := by
        unfold ShiftSource.gVac
        have : (fun t => g t * M.toSource.cardyV (c / 12) t) =ᵐ[volume.restrict (Ioi 0)] 0 := by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          simp [h0 t (mem_Ioi.1 ht).le]
        rw [integral_congr_ae this]; simp
      linarith [hg.2.1], hg.2.1.le, hg.2.2⟩
  refine ⟨⟨T, hT0, g, hg⟩, ⟨T, hT0, g, hgw⟩, ?_⟩
  refine le_csInf ⟨T, hT0, g, hg⟩ fun T' ⟨hT'0, g', hg'⟩ => ?_
  refine csInf_le ⟨0, fun T'' hT'' => hT''.1.le⟩ ⟨hT'0, g', ?_⟩
  exact ⟨hg'.1, by
    by_contra h0
    push Not at h0
    have hv0 : M.toSource.gVac (c / 12) g' = 0 := by
      unfold ShiftSource.gVac
      have : (fun t => g' t * M.toSource.cardyV (c / 12) t) =ᵐ[volume.restrict (Ioi 0)] 0 := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        simp [h0 t (mem_Ioi.1 ht).le]
      rw [integral_congr_ae this]; simp
    linarith [hg'.2.1], hg'.2.1.le, hg'.2.2⟩

/-- **`pmix:o1`, unconditional component comparison**: for every `M : MixtureData` and every `c > 0`
with `12 * M.Smax ≤ c`:
- `min_i (M.Q i).T_weak (c - 12 * M.r i) ≤ M.toSource.T_weak c`,
- `M.toSource.T_weak c ≤ M.toSource.T_V c`, and
- `min_i (M.Q i).T_V (c - 12 * M.r i) ≤ M.toSource.T_V c`. -/
theorem pmix_o1_component_comparison_unconditional (M : MixtureData) {c : ℝ}
    (hc0 : 0 < c) (hc : 12 * M.Smax ≤ c) :
    Finset.univ.inf' ⟨⟨0, M.hs⟩, Finset.mem_univ _⟩ (fun i => (M.Q i).T_weak (c - 12 * M.r i)) ≤
      M.toSource.T_weak c ∧
    M.toSource.T_weak c ≤ M.toSource.T_V c ∧
    Finset.univ.inf' ⟨⟨0, M.hs⟩, Finset.mem_univ _⟩ (fun i => (M.Q i).T_V (c - 12 * M.r i)) ≤
      M.toSource.T_V c := by
  obtain ⟨hfs, hfw, hle⟩ := pmix_o1_feasible_of_Smax M hc0 hc
  obtain ⟨hw, hs⟩ := pmix_o1_component_comparison M hc
  exact ⟨hw hfw, hle, hs hfs⟩

/-! ### 2. Strict component inequality (Lean addition; not a clause of `pmix:o1`) -/

/-- **`pmix:o1` strict comparison**: for `M : MixtureData` with `12 * M.Smax ≤ c` and
`∀ i, 12 * M.r i < c`, if some component satisfies
`min_j (M.Q j).T_V (c - 12 * M.r j) < (M.Q i*).T_weak (c - 12 * M.r i*)`,
then `min_j (M.Q j).T_V (c - 12 * M.r j) < M.toSource.T_V c`. -/
theorem pmix_o1_component_strict_gt (M : MixtureData) {c : ℝ}
    (hc : 12 * M.Smax ≤ c) (hrc : ∀ i : Fin M.s, 12 * M.r i < c)
    {i_star : Fin M.s}
    (hstrict : Finset.univ.inf' ⟨⟨0, M.hs⟩, Finset.mem_univ _⟩
        (fun j => (M.Q j).T_V (c - 12 * M.r j)) <
      (M.Q i_star).T_weak (c - 12 * M.r i_star)) :
    Finset.univ.inf' ⟨⟨0, M.hs⟩, Finset.mem_univ _⟩
        (fun j => (M.Q j).T_V (c - 12 * M.r j)) <
      M.toSource.T_V c := by
  have hc0 : 0 < c := lt_of_le_of_lt (by have := M.hr i_star; positivity) (hrc i_star)
  set Tmin := Finset.univ.inf' ⟨⟨0, M.hs⟩, Finset.mem_univ _⟩
    (fun j => (M.Q j).T_V (c - 12 * M.r j))
  have hle : Tmin ≤ M.toSource.T_V c := (pmix_o1_component_comparison_unconditional M hc0 hc).2.2
  refine lt_of_le_of_ne hle ?_
  intro heq
  obtain ⟨i₀, hi₀⟩ := M.rebase_exists_zero
  have hrmin_eq : M.rmin = M.r i₀ := by
    have h1 : M.r i₀ - M.rmin = 0 := hi₀
    linarith
  have hc'_smax : M.rebase.Smax ≤ (c - 12 * M.rmin) / 12 := by
    refine Finset.sup'_le _ _ fun i _ => ?_
    have hri : M.rebase.r i = M.r i - M.rmin := rfl
    have hQi : M.rebase.Q i = M.Q i := rfl
    rw [hri, hQi]
    linarith [M.le_Smax i]
  have hAt' : (M.rebase.floorData i₀).At ((c - 12 * M.rmin) / 12) :=
    M.rebase.floorAt hi₀ (by linarith [hrc i₀]) hc'_smax
  obtain ⟨-, gs, ⟨htc', -, hvac', hnn', _, hne0, -⟩, -⟩ :=
    theorem_primal_floor hAt' isCompact_empty (empty_subset _)
  have hTV' : 0 < M.rebase.toSource.T_V (c - 12 * M.rmin) :=
    (M.rebase_T_V c).symm ▸ (lt_of_lt_of_le (by
      have h1 : ∀ j ∈ Finset.univ, 0 < (M.Q j).T_V (c - 12 * M.r j) := fun j _ =>
        T_V_pos (by linarith [hrc j]) (by linarith [M.le_Smax j])
      exact (Finset.lt_inf'_iff ⟨⟨0, M.hs⟩, Finset.mem_univ _⟩).2 h1) hle)
  rw [(theorem_E_b_compact_empty_src hAt' hTV').1, M.rebase_T_V, ← heq] at hnn'
  have hch' : (c - 12 * M.rmin) / 12 = c / 12 - M.rmin := M.rebase_charge c
  rw [hch'] at htc' hvac'
  have htc : TestClass M.toSource (c / 12) gs := M.rebase_testClass_iff.1 htc'
  have hvac : M.toSource.gVac (c / 12) gs = 0 := by rwa [M.rebase_gVac] at hvac'
  have hS : M.Smax ≤ c / 12 := by linarith
  have hcomp_tc : ∀ i : Fin M.s, FixedWeightProblem.T_V (M.Q i) (c - 12 * M.r i) = (M.Q i).T_V (c - 12 * M.r i) :=
    fun _ => rfl
  have hcomp_tc' := fun i => M.comp_testClass hS htc i
  have hcomp_vac_le : ∀ i : Fin M.s, (M.Q i).gVac ((c - 12 * M.r i) / 12) gs ≤ 0 := by
    intro i
    have hci_pos : 0 < c - 12 * M.r i := by linarith [hrc i]
    have hci_shift : 12 * (M.Q i).totalShift ≤ c - 12 * M.r i := by
      linarith [M.le_Smax i]
    have hTVi := T_V_pos hci_pos hci_shift
    have hEb := theorem_E_b_compact (M.Q i) hci_pos hci_shift isCompact_empty (empty_subset _) hTVi
    rw [constrainedThreshold_empty] at hEb
    obtain ⟨-, meas_i, hsupp_i⟩ := hEb.2.1.1
    have hTmin_le_i : Tmin ≤ (M.Q i).T_V (c - 12 * M.r i) :=
      Finset.inf'_le (fun j => (M.Q j).T_V (c - 12 * M.r j)) (Finset.mem_univ i)
    have hgs_nn_i : ∀ t : ℝ, (M.Q i).T_V (c - 12 * M.r i) ≤ t → 0 ≤ gs t := fun t ht =>
      hnn' t (Or.inr (hTmin_le_i.trans ht))
    have htci := hcomp_tc' i
    rw [show c / 12 - M.r i = (c - 12 * M.r i) / 12 by ring] at htci
    obtain ⟨-, hfw⟩ := lemma_fwX_one_sided_unconditional (M.Q i)
      (show (M.Q i).totalShift ≤ (c - 12 * M.r i) / 12 by linarith)
      (by linarith) meas_i htci hgs_nn_i
    rw [Duality.restrict_Ici_eq_self meas_i] at hfw
    have hae : ∀ᵐ t ∂meas_i.ν, (M.Q i).T_V (c - 12 * M.r i) ≤ t := by
      have hm : ∀ᵐ t ∂meas_i.ν, t ∉ (∅ ∪ Ici ((M.Q i).T_V (c - 12 * M.r i)))ᶜ :=
        measure_eq_zero_iff_ae_notMem.1 hsupp_i
      filter_upwards [hm] with t ht
      simpa using ht
    have hI0 : 0 ≤ ∫ t, gs t ∂meas_i.ν :=
      integral_nonneg_of_ae (hae.mono fun t ht => hgs_nn_i t ht)
    linarith
  have hsum : ∑ i : Fin M.s, M.d i * (M.Q i).gVac ((c - 12 * M.r i) / 12) gs = 0 := by
    have hg := M.gVac_eq hS htc
    rw [hvac] at hg
    refine (Finset.sum_congr rfl fun i _ => ?_).trans hg.symm
    rw [show (c - 12 * M.r i) / 12 = c / 12 - M.r i by ring]
  have hcomp_vac_eq : ∀ i : Fin M.s, (M.Q i).gVac ((c - 12 * M.r i) / 12) gs = 0 := by
    have hnp : ∀ i ∈ Finset.univ, M.d i * (M.Q i).gVac ((c - 12 * M.r i) / 12) gs ≤ 0 :=
      fun i _ => mul_nonpos_of_nonneg_of_nonpos (M.hd i).le (hcomp_vac_le i)
    have h0 := (Finset.sum_eq_zero_iff_of_nonpos hnp).1 hsum
    intro i
    exact (mul_eq_zero.1 (h0 i (Finset.mem_univ i))).resolve_left (M.hd i).ne'
  have htci_star := hcomp_tc' i_star
  rw [show c / 12 - M.r i_star = (c - 12 * M.r i_star) / 12 by ring] at htci_star
  have hweak_star : (M.Q i_star).IsWeaklyFeasible ((c - 12 * M.r i_star) / 12) Tmin gs :=
    ⟨htci_star, hne0, (hcomp_vac_eq i_star).ge, fun t ht => hnn' t (Or.inr ht)⟩
  have hTmin_pos : 0 < Tmin := by
    have h1 : ∀ j ∈ Finset.univ, 0 < (M.Q j).T_V (c - 12 * M.r j) := fun j _ =>
      T_V_pos (by linarith [hrc j]) (by linarith [M.le_Smax j])
    exact (Finset.lt_inf'_iff ⟨⟨0, M.hs⟩, Finset.mem_univ _⟩).2 h1
  have hTw_le : (M.Q i_star).T_weak (c - 12 * M.r i_star) ≤ Tmin :=
    csInf_le ⟨0, fun T hT => hT.1.le⟩ ⟨hTmin_pos, gs, hweak_star⟩
  linarith

/-! ### 3. `pmix:liminf` from single-component `c₀*` lower bounds -/

private lemma rpow_third_shift_tendsto_zero (a : ℝ) :
    Tendsto (fun c : ℝ => (c - a) ^ ((1 : ℝ) / 3) - c ^ ((1 : ℝ) / 3)) atTop (𝓝 0) := by
  have hpos : ∀ᶠ c : ℝ in atTop, 1 ≤ c ∧ |a| / c ≤ 1 / 2 := by
    filter_upwards [eventually_ge_atTop (max 1 (2 * |a|))] with c hc
    have h1 : 1 ≤ c := (le_max_left _ _).trans hc
    have h2 : 2 * |a| ≤ c := (le_max_right _ _).trans hc
    refine ⟨h1, ?_⟩
    rw [div_le_iff₀ (by linarith)]
    linarith
  refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
  have hbnd : ∀ᶠ c : ℝ in atTop,
      ‖(c - a) ^ ((1 : ℝ) / 3) - c ^ ((1 : ℝ) / 3)‖ ≤ 2 * |a| * c ^ (-(2 / 3 : ℝ)) := by
    filter_upwards [hpos] with c ⟨hc1, hac⟩
    have hc0 : 0 < c := by linarith
    have hhalf : c / 2 ≤ c - a := by
      have ha1 : a ≤ c / 2 := (le_abs_self a).trans (by rw [div_le_iff₀ hc0] at hac; linarith)
      linarith
    have hca0 : 0 < c - a := by linarith
    have hdiff := show (c - a) - c = -a by ring
    -- use mean value theorem on `x ↦ x^(1/3)` between `min c (c - a)` and `max c (c - a)`
    set lo := min c (c - a)
    set hi := max c (c - a)
    have hlo_pos : 0 < lo := lt_min hc0 hca0
    have hlo_ge : c / 2 ≤ lo := le_min (by linarith) hhalf
    have hderiv : ∀ x ∈ Icc lo hi,
        HasDerivAt (fun t : ℝ => t ^ ((1 : ℝ) / 3)) ((1 / 3 : ℝ) * x ^ (-(2 / 3 : ℝ))) x := by
      intro x hx
      have hx0 : x ≠ 0 := (lt_of_lt_of_le hlo_pos hx.1).ne'
      convert (Real.hasDerivAt_rpow_const (Or.inl hx0) (p := (1 : ℝ) / 3)) using 2
      norm_num
    have hderiv_le : ∀ x ∈ Icc lo hi,
        ‖(1 / 3 : ℝ) * x ^ (-(2 / 3 : ℝ))‖ ≤ 2 * c ^ (-(2 / 3 : ℝ)) := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hlo_pos hx.1
      rw [Real.norm_of_nonneg (by positivity)]
      have hpow : x ^ (-(2 / 3 : ℝ)) ≤ (c / 2) ^ (-(2 / 3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (hlo_ge.trans hx.1) (by norm_num)
      have h2 : (c / 2) ^ (-(2 / 3 : ℝ)) = 2 ^ ((2 : ℝ) / 3) * c ^ (-(2 / 3 : ℝ)) := by
        rw [div_eq_mul_inv, Real.mul_rpow hc0.le (by positivity), Real.inv_rpow (by norm_num),
          ← Real.rpow_neg (by norm_num), neg_neg, mul_comm]
      have h23 : (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 := by
        simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (2 : ℝ) / 3 ≤ 1)
      have h3 : (1 / 3 : ℝ) * (c / 2) ^ (-(2 / 3 : ℝ)) ≤ 2 * c ^ (-(2 / 3 : ℝ)) := by
        rw [h2]
        nlinarith [Real.rpow_nonneg hc0.le (-(2 / 3 : ℝ))]
      exact (mul_le_mul_of_nonneg_left hpow (by norm_num)).trans h3
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hderiv x hx).hasDerivWithinAt)
      (fun x hx => hderiv_le x hx)
      (convex_Icc lo hi)
      (⟨min_le_right _ _, le_max_right _ _⟩ : c - a ∈ Icc lo hi)
      (⟨min_le_left _ _, le_max_left _ _⟩ : c ∈ Icc lo hi)
    rw [norm_sub_rev (c ^ ((1 : ℝ) / 3)), norm_sub_rev c] at hmvt
    have hnorm : ‖(c - a) - c‖ = |a| := by rw [Real.norm_eq_abs, hdiff, abs_neg]
    rw [hnorm] at hmvt
    calc |((c - a) ^ ((1 : ℝ) / 3) - c ^ ((1 : ℝ) / 3))| =
          ‖(c - a) ^ ((1 : ℝ) / 3) - c ^ ((1 : ℝ) / 3)‖ := (Real.norm_eq_abs _).symm
      _ ≤ 2 * c ^ (-(2 / 3 : ℝ)) * |a| := hmvt
      _ = 2 * |a| * c ^ (-(2 / 3 : ℝ)) := by ring
  have hlim : Tendsto (fun c : ℝ => 2 * |a| * c ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul (2 * |a|)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => norm_nonneg _) hbnd

/-- **`pmix:liminf` (`pmix:o1`, eq. `pmix:liminf`)**: for a positive mixture `M : MixtureData`
whose components `(M.Q i)` satisfy weak asymptotic lower bounds
`T_weak(n_i) ≥ T_*(n_i) + c0 i - o(1)` as `n_i → ∞` (which holds from `ctu:c0` together with
`int:strict-weak`), both `T_{weak,mix}(c) - T_*(c)` and `T_mix(c) - T_*(c)` are eventually
`≥ min_i (c0 i - 12 ξ̄ r_i) - ε` for every `ε > 0`, and consequently
`min_i (c0 i - 12 ξ̄ r_i) ≤ liminf_{c → ∞} [T_{weak,mix}(c) - T_*(c)] ≤ liminf_{c → ∞} [T_mix(c) - T_*(c)]`. -/
theorem pmix_liminf_of_component_c0 (M : MixtureData) (c0 : Fin M.s → ℝ)
    (hcomp : ∀ i : Fin M.s, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℝ in atTop,
      TStar n + c0 i - ε ≤ (M.Q i).T_weak n) :
    let m0 := Finset.univ.inf' ⟨⟨0, M.hs⟩, Finset.mem_univ _⟩ (fun i => c0 i - 12 * xiBar * M.r i)
    (∀ ε : ℝ, 0 < ε → ∀ᶠ c : ℝ in atTop,
      m0 - ε ≤ M.toSource.T_weak c - TStar c ∧ M.toSource.T_weak c - TStar c ≤ M.toSource.T_V c - TStar c) ∧
    (m0 ≤ Filter.liminf (fun c : ℝ => M.toSource.T_weak c - TStar c) atTop ∧
      Filter.liminf (fun c : ℝ => M.toSource.T_weak c - TStar c) atTop ≤
        Filter.liminf (fun c : ℝ => M.toSource.T_V c - TStar c) atTop) := by
  intro m0
  have hcomp_c : ∀ i : Fin M.s, ∀ ε : ℝ, 0 < ε → ∀ᶠ c : ℝ in atTop,
      c0 i - 12 * xiBar * M.r i - ε ≤ (M.Q i).T_weak (c - 12 * M.r i) - TStar c := by
    intro i ε hε
    have hshift : Tendsto (fun c : ℝ => c - 12 * M.r i) atTop atTop :=
      tendsto_atTop_add_const_right atTop _ tendsto_id
    have h1 := hshift.eventually (hcomp i (ε / 2) (half_pos hε))
    have h2 : Tendsto (fun c : ℝ => TStar (c - 12 * M.r i) - TStar c) atTop
        (𝓝 (-12 * xiBar * M.r i)) := by
      have e : (fun c : ℝ => TStar (c - 12 * M.r i) - TStar c) =
          fun c : ℝ => -12 * xiBar * M.r i + Aopt * ((c - 12 * M.r i) ^ ((1 : ℝ) / 3) - c ^ ((1 : ℝ) / 3)) := by
        ext c; unfold TStar; ring
      rw [e]
      simpa using tendsto_const_nhds.add ((rpow_third_shift_tendsto_zero (12 * M.r i)).const_mul Aopt)
    have h3 := h2.eventually (lt_mem_nhds (show -12 * xiBar * M.r i - ε / 2 < -12 * xiBar * M.r i by linarith))
    filter_upwards [h1, h3] with c hc1 hc3
    linarith
  have hall : ∀ ε : ℝ, 0 < ε → ∀ᶠ c : ℝ in atTop,
      m0 - ε ≤ M.toSource.T_weak c - TStar c ∧ M.toSource.T_weak c - TStar c ≤ M.toSource.T_V c - TStar c := by
    intro ε hε
    have hfin : ∀ᶠ c : ℝ in atTop, ∀ i : Fin M.s,
        c0 i - 12 * xiBar * M.r i - ε ≤ (M.Q i).T_weak (c - 12 * M.r i) - TStar c :=
      eventually_all.2 fun i => hcomp_c i ε hε
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (12 * M.Smax), hfin]
      with c hc0 hcS hfi
    obtain ⟨hw_cmp, hle_wv, -⟩ := pmix_o1_component_comparison_unconditional M hc0 hcS
    have hneU : (Finset.univ : Finset (Fin M.s)).Nonempty := ⟨⟨0, M.hs⟩, Finset.mem_univ _⟩
    have hm0 : m0 - ε ≤ Finset.univ.inf' hneU
        (fun i => (M.Q i).T_weak (c - 12 * M.r i)) - TStar c := by
      have hex : ∃ i ∈ Finset.univ,
          Finset.univ.inf' hneU (fun j => (M.Q j).T_weak (c - 12 * M.r j)) =
            (M.Q i).T_weak (c - 12 * M.r i) :=
        Finset.exists_mem_eq_inf' hneU (fun j => (M.Q j).T_weak (c - 12 * M.r j))
      obtain ⟨i, _, hi⟩ := hex
      rw [hi]
      linarith [Finset.inf'_le (fun j => c0 j - 12 * xiBar * M.r j) (Finset.mem_univ i), hfi i]
    exact ⟨by linarith, by linarith⟩
  refine ⟨hall, ?_, ?_⟩
  · obtain ⟨c₁, D_m, D_p, _, _, hpm⟩ := M.pmix_o1_mixture
    have hbd_above : atTop.IsBoundedUnder (· ≤ ·) (fun c : ℝ => M.toSource.T_weak c - TStar c) :=
      ⟨D_p, eventually_atTop.2 ⟨c₁, fun c hc =>
        sub_le_iff_le_add'.2 ((hpm hc).2.1.trans (hpm hc).2.2)⟩⟩
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := Filter.le_liminf_of_le hbd_above.isCoboundedUnder_ge ((hall ε hε).mono fun _ hc => hc.1)
    linarith
  · obtain ⟨c₁, D_m, D_p, _, _, hpm⟩ := M.pmix_o1_mixture
    have hbd_below : atTop.IsBoundedUnder (· ≥ ·) (fun c : ℝ => M.toSource.T_weak c - TStar c) :=
      ⟨-D_m, eventually_atTop.2 ⟨c₁, fun c hc => by
        show -D_m ≤ M.toSource.T_weak c - TStar c
        exact le_sub_iff_add_le'.2 (by linarith [(hpm hc).1])⟩⟩
    have hbd_above_V : atTop.IsBoundedUnder (· ≤ ·) (fun c : ℝ => M.toSource.T_V c - TStar c) :=
      ⟨D_p, eventually_atTop.2 ⟨c₁, fun c hc => sub_le_iff_le_add'.2 (hpm hc).2.2⟩⟩
    exact Filter.liminf_le_liminf ((hall 1 one_pos).mono fun _ hc => hc.2)
      hbd_below hbd_above_V.isCoboundedUnder_ge

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_o1_feasible_of_Smax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_o1_feasible_of_Smax

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_o1_component_comparison_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_o1_component_comparison_unconditional

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_o1_component_strict_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_o1_component_strict_gt

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_liminf_of_component_c0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_liminf_of_component_c0

end FormalResearch.ModularBootstrap.Mixtures
