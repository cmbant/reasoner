module

public import FormalResearch.ModularBootstrap.Mixtures.CommonSource
public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWInterface

/-!
# `pmix:o1`, lower half, for positive mixtures: the component comparison

`positive_mixtures.tex`, Lemma PM.7 (`pmix:o1`), "Sharper mixture-only comparison": work in the un-rebased variable `n`
with `n ≥ 12 S_max`, so that every component has `a_i = a - r_i = n_i/12 ≥ S_i` and `V_i ≥ 0`.  If
`g ∈ \overline{\mathcal A}_{w,mix}` is weakly feasible at `T`, then since `d_i > 0` some index `i_*` has
`g_{vac,i_*} ≥ 0`, and `d_{i_*} V_{i_*} ≤ V_mix` gives `M_{i_*}[g] ≤ d_{i_*}^{-1} M_mix[g] < ∞`, so `g` is weakly feasible at `T`
for the single component `(w, Q_{i_*})` at `n_{i_*} = n - 12 r_{i_*}`.  Hence `T_mix ≥ T_weak,mix ≥ min_i T_{w,i}(n_i)`, and
the single-component weak bound of Theorem `W1'(1)` (`theoremFTLFW_W_of_YVFor`, proved for every `(w, Q)`) gives the lower
half of `pmix:o1` for every positive mixture with *no* rebasing and no use of `(W1)-(W4)`.

* `fixedWeight_weak_lower`: the weak bound `T ≥ T_*(c') - C` for every weakly feasible test of a fixed-weight problem
  (the intermediate form of `fixedWeightLowerBoundInput_of_problem`);
* `MixtureData.weak_component`, `MixtureData.strict_component`: the pigeonhole;
* `pmix_o1_lower_mixture`: every weakly feasible test function of the mixture at `(c/12, T)`, `c ≥ c₁`, has
  `T ≥ T_*(c) - D_-`; `pmix_o1_component_comparison`: the comparison `T_weak,mix ≥ min_i T_{w,i}(n - 12 r_i)`
  (and for the strict thresholds), `n ≥ 12 S_max`.

All results are proved unconditionally; the liminf bound with the constant `c_0^*` (`pmix:liminf`) is not covered
(it needs `ctu:c0`, `int:strict-weak`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight FormalResearch.ModularBootstrap.FixedWeightBand

/-- **The weak single-component lower bound** (Theorem `W1'(1)` in its weak form): for every fixed-weight problem there are
`c₂` and `C ≥ 0` with `T_*(c') - C ≤ T` for every weakly feasible test function at `(c'/12, T)`, `c' ≥ c₂`. -/
theorem fixedWeight_weak_lower (prob : FixedWeightProblem) :
    ∃ c₂ C : ℝ, 0 ≤ C ∧ ∀ {c' T : ℝ} {g : ℝ → ℝ}, c₂ ≤ c' →
      prob.IsWeaklyFeasible (c' / 12) T g → TStar c' - C ≤ T := by
  obtain ⟨Q⟩ := LemmaQData.nonempty prob
  obtain ⟨c₂, C, -, hC, hft⟩ := theoremFTLFW_W_of_YVFor Q Q.bvChoice_pos Q.bvChoice_le
    Q.yvInputForW_bvChoice
  refine ⟨c₂, C, hC, fun {c' T g} hc hg => ?_⟩
  have := hft hc hg
  unfold TStar
  simpa using this

namespace MixtureData

variable (M : MixtureData)

lemma comp_nonneg {a : ℝ} (ha : M.Smax ≤ a) (i : Fin M.s) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (M.Q i).cardyV (a - M.r i) t :=
  (M.Q i).cardyV_nonneg (by linarith [M.le_Smax i]) ht

/-- `d_i V_i ≤ V_mix` on `t ≥ 0`. -/
lemma comp_le_mix {a : ℝ} (ha : M.Smax ≤ a) (i : Fin M.s) {t : ℝ} (ht : 0 ≤ t) :
    M.d i * (M.Q i).cardyV (a - M.r i) t ≤ M.toSource.cardyV a t := by
  rw [M.toSource_cardyV]
  exact Finset.single_le_sum (f := fun j => M.d j * (M.Q j).cardyV (a - M.r j) t)
    (fun j _ => mul_nonneg (M.hd j).le (M.comp_nonneg ha j ht)) (Finset.mem_univ i)

/-- A mixture test function is a test function of every component at the shifted charge. -/
lemma comp_testClass {a : ℝ} (ha : M.Smax ≤ a) {g : ℝ → ℝ} (hg : TestClass M.toSource a g)
    (i : Fin M.s) : Crossing.TestClass (M.Q i) (a - M.r i) g := by
  refine ⟨hg.cont, hg.int_lift, hg.fourier_odd, ?_⟩
  refine (hg.int_cardy.const_mul (1 / M.d i)).mono' ?_
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  · exact ((hg.cont.abs.mono Ioi_subset_Ici_self).mul
      (continuous_cardyV (M.Q i) (a - M.r i)).continuousOn).aestronglyMeasurable measurableSet_Ioi
  · have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
    have hd := M.hd i
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (M.comp_nonneg ha i ht0))]
    have h1 := M.comp_le_mix ha i ht0
    have h2 : (M.Q i).cardyV (a - M.r i) t ≤ (1 / M.d i) * M.toSource.cardyV a t := by
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hd]
      linarith
    calc |g t| * (M.Q i).cardyV (a - M.r i) t
        ≤ |g t| * ((1 / M.d i) * M.toSource.cardyV a t) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = 1 / M.d i * (|g t| * M.toSource.cardyV a t) := by ring

/-- **`g_{vac,mix} = ∑_i d_i g_{vac,i}`** at `a_i = a - r_i`. -/
lemma gVac_eq {a : ℝ} (ha : M.Smax ≤ a) {g : ℝ → ℝ} (hg : TestClass M.toSource a g) :
    M.toSource.gVac a g = ∑ i, M.d i * (M.Q i).gVac (a - M.r i) g := by
  have hint : ∀ i : Fin M.s, IntegrableOn (fun t => g t * (M.Q i).cardyV (a - M.r i) t) (Ioi 0) := by
    intro i
    have h := (M.comp_testClass ha hg i).int_cardy
    refine h.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
    · exact ((hg.cont.mono Ioi_subset_Ici_self).mul
        (continuous_cardyV (M.Q i) (a - M.r i)).continuousOn).aestronglyMeasurable measurableSet_Ioi
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (M.comp_nonneg ha i (mem_Ioi.mp ht).le)]
  unfold ShiftSource.gVac FixedWeightProblem.gVac
  have hfun : (fun t => g t * M.toSource.cardyV a t) =
      fun t => ∑ i, M.d i * (g t * (M.Q i).cardyV (a - M.r i) t) := by
    ext t
    rw [M.toSource_cardyV, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hfun, integral_finsetSum _ (fun i _ => (hint i).const_mul _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]
  ring

/-- **Pigeonhole, weak form**: a weakly feasible mixture test function is weakly feasible for some component at the shifted
charge `a - r_i`. -/
theorem weak_component {a T : ℝ} (ha : M.Smax ≤ a) {g : ℝ → ℝ}
    (hg : M.toSource.IsWeaklyFeasible a T g) :
    ∃ i : Fin M.s, (M.Q i).IsWeaklyFeasible (a - M.r i) T g := by
  obtain ⟨hT, hne, hvac, hnn⟩ := hg
  have hg_eq := M.gVac_eq ha hT
  by_contra hcon
  push Not at hcon
  have hneg : ∀ i : Fin M.s, (M.Q i).gVac (a - M.r i) g < 0 := fun i => by
    by_contra h
    push Not at h
    exact hcon i ⟨M.comp_testClass ha hT i, hne, h, hnn⟩
  have : M.toSource.gVac a g < 0 := by
    rw [hg_eq]
    exact Finset.sum_neg (fun i _ => mul_neg_of_pos_of_neg (M.hd i) (hneg i))
      ⟨⟨0, M.hs⟩, Finset.mem_univ _⟩
  linarith

/-- **Pigeonhole, strict form**: a strictly feasible mixture test function is strictly feasible for some component. -/
theorem strict_component {a T : ℝ} (ha : M.Smax ≤ a) {g : ℝ → ℝ}
    (hg : M.toSource.IsFeasible a T g) :
    ∃ i : Fin M.s, (M.Q i).IsFeasible (a - M.r i) T g := by
  obtain ⟨hT, hvac, hnn⟩ := hg
  have hg_eq := M.gVac_eq ha hT
  by_contra hcon
  push Not at hcon
  have hneg : ∀ i : Fin M.s, (M.Q i).gVac (a - M.r i) g ≤ 0 := fun i => by
    by_contra h
    push Not at h
    exact hcon i ⟨M.comp_testClass ha hT i, h, hnn⟩
  have : M.toSource.gVac a g ≤ 0 := by
    rw [hg_eq]
    exact Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (M.hd i).le (hneg i)
  linarith

end MixtureData

/-- **`pmix:o1`, lower half, for every positive mixture** (`(H_{w,mix})`, un-rebased variable): there are `c₁ ≥ 12 S_max` and
`D_- ≥ 0` such that every weakly feasible test function of the mixture at `(c/12, T)` with `c ≥ c₁` has
`T ≥ T_*(c) - D_-`, `T_*(c) = ξ̄ c + A_opt c^{1/3}`.  (So `T_weak,mix(n) ≥ T_*(n) - D_-` whenever the weak set is
nonempty, in particular `T_mix ≥ T_weak,mix ≥ T_* - D_-`; see `pmix_o1_mixture`.) -/
theorem pmix_o1_lower_mixture (M : MixtureData) :
    ∃ c₁ D : ℝ, 0 ≤ D ∧ 12 * M.Smax ≤ c₁ ∧ ∀ {c T : ℝ} {g : ℝ → ℝ}, c₁ ≤ c →
      M.toSource.IsWeaklyFeasible (c / 12) T g → TStar c - D ≤ T := by
  have h : ∀ i : Fin M.s, ∃ c₂ C : ℝ, 0 ≤ C ∧ ∀ {c' T : ℝ} {g : ℝ → ℝ}, c₂ ≤ c' →
      (M.Q i).IsWeaklyFeasible (c' / 12) T g → TStar c' - C ≤ T := fun i => fixedWeight_weak_lower (M.Q i)
  choose c₂ C hC hlow using h
  have hA : 0 ≤ Aopt := by unfold Aopt; have := cStar_pos; positivity
  have hxb : 0 ≤ xiBar := by unfold xiBar; positivity
  have hterm : ∀ j : Fin M.s, 0 ≤ C j + 12 * xiBar * M.r j + Aopt * (12 * M.r j) ^ ((1 : ℝ) / 3) := fun j => by
    have := M.hr j
    have := Real.rpow_nonneg (by positivity : 0 ≤ 12 * M.r j) ((1 : ℝ) / 3)
    have := hC j
    positivity
  refine ⟨max (12 * M.Smax) (∑ i, (|c₂ i| + 12 * M.r i)),
    ∑ i, (C i + 12 * xiBar * M.r i + Aopt * (12 * M.r i) ^ ((1 : ℝ) / 3)),
    Finset.sum_nonneg fun j _ => hterm j, le_max_left _ _, fun {c T g} hc hg => ?_⟩
  have hS : M.Smax ≤ c / 12 := by
    have := (le_max_left _ _).trans hc
    linarith
  obtain ⟨i, hi⟩ := M.weak_component hS hg
  have hsum : |c₂ i| + 12 * M.r i ≤ c := by
    refine le_trans ?_ ((le_max_right _ _).trans hc)
    exact Finset.single_le_sum (f := fun j => |c₂ j| + 12 * M.r j)
      (fun j _ => by have := M.hr j; positivity) (Finset.mem_univ i)
  have hri := M.hr i
  have hci : c₂ i ≤ c - 12 * M.r i := by linarith [le_abs_self (c₂ i)]
  have hc0 : 0 ≤ c - 12 * M.r i := by linarith [abs_nonneg (c₂ i)]
  have e : (c - 12 * M.r i) / 12 = c / 12 - M.r i := by ring
  rw [← e] at hi
  have h1 := hlow i hci hi
  have hsub := Real.rpow_add_le_add_rpow hc0 (by positivity : 0 ≤ 12 * M.r i)
    (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 : ℝ) / 3 ≤ 1)
  rw [sub_add_cancel] at hsub
  have hD : C i + 12 * xiBar * M.r i + Aopt * (12 * M.r i) ^ ((1 : ℝ) / 3) ≤
      ∑ j, (C j + 12 * xiBar * M.r j + Aopt * (12 * M.r j) ^ ((1 : ℝ) / 3)) :=
    Finset.single_le_sum (f := fun j => C j + 12 * xiBar * M.r j + Aopt * (12 * M.r j) ^ ((1 : ℝ) / 3))
      (fun j _ => hterm j) (Finset.mem_univ i)
  have hA' := mul_le_mul_of_nonneg_left hsub hA
  unfold TStar at h1 ⊢
  nlinarith only [h1, hD, hA', hxb]

/-- **`pmix:o1`, component comparison** (strict and weak thresholds, un-rebased variable): for `c ≥ 12 S_max` and a nonempty
weak set, `min_i T_{w,i}(c - 12 r_i) ≤ T_weak,mix(c)`; for a nonempty strict set,
`min_i T_{V,i}(c - 12 r_i) ≤ T_mix(c)` (`T_{w,i}`, `T_{V,i}` the weak and strict thresholds of the single component
`(w, Q_i)` at `n_i = c - 12 r_i`). -/
theorem pmix_o1_component_comparison (M : MixtureData) {c : ℝ} (hc : 12 * M.Smax ≤ c) :
    ({T : ℝ | 0 < T ∧ ∃ g, M.toSource.IsWeaklyFeasible (c / 12) T g}.Nonempty →
      Finset.univ.inf' ⟨⟨0, M.hs⟩, Finset.mem_univ _⟩ (fun i => (M.Q i).T_weak (c - 12 * M.r i)) ≤
        M.toSource.T_weak c) ∧
    ({T : ℝ | 0 < T ∧ ∃ g, M.toSource.IsFeasible (c / 12) T g}.Nonempty →
      Finset.univ.inf' ⟨⟨0, M.hs⟩, Finset.mem_univ _⟩ (fun i => (M.Q i).T_V (c - 12 * M.r i)) ≤
        M.toSource.T_V c) := by
  have hS : M.Smax ≤ c / 12 := by linarith
  have e : ∀ i : Fin M.s, (c - 12 * M.r i) / 12 = c / 12 - M.r i := fun i => by ring
  constructor
  · intro hne
    refine le_csInf hne ?_
    rintro T ⟨hT0, g, hg⟩
    obtain ⟨i, hi⟩ := M.weak_component hS hg
    refine le_trans (Finset.inf'_le _ (Finset.mem_univ i)) ?_
    refine csInf_le ⟨0, fun T hT => hT.1.le⟩ ⟨hT0, g, ?_⟩
    rw [e i]
    exact hi
  · intro hne
    refine le_csInf hne ?_
    rintro T ⟨hT0, g, hg⟩
    obtain ⟨i, hi⟩ := M.strict_component hS hg
    refine le_trans (Finset.inf'_le _ (Finset.mem_univ i)) ?_
    refine csInf_le ⟨0, fun T hT => hT.1.le⟩ ⟨hT0, g, ?_⟩
    rw [e i]
    exact hi

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.fixedWeight_weak_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixedWeight_weak_lower

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_o1_lower_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_o1_lower_mixture

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_o1_component_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pmix_o1_component_comparison

end FormalResearch.ModularBootstrap.Mixtures
