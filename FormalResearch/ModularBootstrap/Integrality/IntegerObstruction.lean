module

public import FormalResearch.ModularBootstrap.Integrality.IntClosed
public import FormalResearch.ModularBootstrap.Duality.ConstrainedThreshold
public import FormalResearch.ModularBootstrap.Duality.Primal.Attainment

/-!
# Attainment of Integer Optima and Criterion for Equality (`int:obstr`(a), `integrality.tex`)

`CFT/modular_bootstrap/paper/integrality.tex`, Theorem INT-4 (`int:obstr`(a)) at every fixed
chiral weight `(w, Q)` (`prob : FixedWeightProblem`) with `c̃ > 0` and `c̃ ≥ 12 S`, for any
compact set `F ⊂ (0, ∞)` (possibly empty):

* `constrainedIntGaps`, `constrainedIntThreshold` (`T_ℤ`), `constrainedDeltaBest`,
  `constrainedDeltaBestInt` (`Δ_best^ℤ`): the supremal gap and dimension of locally finite
  integer-weighted crossing measures (`Integrality.IsIntegerCounting`) carried by `F ∪ [τ, ∞)`.
* `int_obstr_a`: whenever at least one integer-degeneracy crossing spectrum with positive
  terminal threshold exists, `T_ℤ` is attained by an integer counting crossing measure
  (`IsGreatest`), `0 < T_ℤ ≤ T_F < ∞`, `0 < T_V`, and
  `Δ_best^ℤ = Δ_best^ℝ` iff some attaining real crossing measure is integer-weighted
  (equivalently, `Δ_best^ℤ < Δ_best^ℝ` iff no attaining real crossing measure is integer-weighted).
* `int_obstr_a_primal`: by `theorem_primal` (`ds:primal`), at every fixed charge `c̃ > 0` with
  `12 S ≤ c̃`, every attaining real crossing measure is locally finite atomic, so
  `Δ_best^ℤ < Δ_best^ℝ` iff every attaining real crossing measure has an atom of non-integer
  weight.

Statements are in the paper's class **proved** (for `(H_w)`; the mixture/source cases wait for
PM-4 `pmix:duality`).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Integrality

open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality
open FormalResearch.ModularBootstrap.FixedWeight

section FixedWeight

variable (prob : FixedWeightProblem) (cTilde : ℝ) (F : Set ℝ)

/-- Gaps `τ > 0` at which a locally finite positive integer-weighted atomic crossing measure
carried by `F ∪ [τ, ∞)` exists. -/
def constrainedIntGaps : Set ℝ :=
  {τ : ℝ | 0 < τ ∧ ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
    meas.ν (F ∪ Ici τ)ᶜ = 0 ∧ IsIntegerCounting meas.ν}

/-- The supremal integer terminal threshold `T_ℤ` on `F ∪ [τ, ∞)`. -/
noncomputable def constrainedIntThreshold : ℝ :=
  sSup (constrainedIntGaps prob cTilde F)

/-- The constrained real optimal dimension `Δ_best^ℝ = c̃/12 + T_F`. -/
noncomputable def constrainedDeltaBest : ℝ :=
  cTilde / 12 + constrainedThreshold prob cTilde F

/-- The constrained integer optimal dimension `Δ_best^ℤ = c̃/12 + T_ℤ`. -/
noncomputable def constrainedDeltaBestInt : ℝ :=
  cTilde / 12 + constrainedIntThreshold prob cTilde F

@[simp] lemma constrainedDeltaBest_empty :
    constrainedDeltaBest prob cTilde ∅ = prob.Delta_best cTilde := by
  unfold constrainedDeltaBest FixedWeightProblem.Delta_best
  rw [constrainedThreshold_empty]

end FixedWeight

section Proofs

private lemma isIntegerCounting_singletons_of_isIntegerCounting {ν : Measure ℝ}
    (h : IsIntegerCounting ν) : ∀ x : ℝ, ∃ n : ℕ, ν {x} = n := by
  classical
  obtain ⟨S, d, -, -, rfl⟩ := h
  intro x
  by_cases hx : x ∈ S
  · refine ⟨d x, ?_⟩
    rw [Measure.sum_apply _ (measurableSet_singleton x)]
    have heq : (fun y : S => ((d y : ℝ≥0∞) • Measure.dirac (y : ℝ)) {x}) =
        fun y : S => if y = ⟨x, hx⟩ then (d x : ℝ≥0∞) else 0 := by
      funext y
      by_cases hy : y = ⟨x, hx⟩
      · subst hy; simp
      · have hne : (y : ℝ) ≠ x := fun h => hy (Subtype.ext h)
        simp [hy, Measure.dirac_apply' _ (measurableSet_singleton x), hne]
    rw [heq, tsum_ite_eq]
  · refine ⟨0, ?_⟩
    rw [Measure.sum_apply _ (measurableSet_singleton x)]
    have h0 : ∀ y : S, ((d y : ℝ≥0∞) • Measure.dirac (y : ℝ)) {x} = 0 := fun y => by
      have hne : (y : ℝ) ≠ x := fun h => hx (h ▸ y.2)
      simp [Measure.dirac_apply' _ (measurableSet_singleton x), hne]
    simp [h0]

private lemma support_eq_of_locallyFinite {ν : Measure ℝ} (hnonneg : ν (Iio 0) = 0)
    {Z : Set ℝ} (hZ : ∀ R : ℝ, (Z ∩ Icc 0 R).Finite) (hνZ : ν Zᶜ = 0) :
    ν.support = {x ∈ Z ∩ Ici 0 | 0 < ν {x}} := by
  set Z₀ : Set ℝ := Z ∩ Ici 0 with hZ₀
  have hνZ₀ : ν Z₀ᶜ = 0 := by
    have hsub : Z₀ᶜ = Zᶜ ∪ Iio 0 := by ext x; simp [Z₀]
    rw [hsub]
    exact measure_union_null hνZ hnonneg
  ext x
  constructor
  · intro hx
    have hxZ₀ : x ∈ Z₀ := by
      by_contra hxn
      set R : ℝ := |x| + 1 with hR
      have hfin : (Z₀ ∩ Icc 0 R).Finite := (hZ R).subset fun y hy => ⟨hy.1.1, hy.2⟩
      have hx_mem : x ∈ Ioo (-R) R := ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
      set U : Set ℝ := Ioo (-R) R ∩ (Z₀ ∩ Icc 0 R)ᶜ with hU
      have hUopen : IsOpen U := isOpen_Ioo.inter hfin.isClosed.isOpen_compl
      have hxU : x ∈ U := ⟨hx_mem, fun h => hxn h.1⟩
      have hU_sub : U ⊆ Z₀ᶜ := fun y hy hyZ => by
        apply hy.2
        refine ⟨hyZ, hyZ.2, ?_⟩
        exact hy.1.2.le
      have hνU : ν U = 0 := measure_mono_null hU_sub hνZ₀
      have hpos : 0 < ν U := (Measure.mem_support_iff_forall x).1 hx U (hUopen.mem_nhds hxU)
      exact absurd hνU hpos.ne'
    refine ⟨hxZ₀, ?_⟩
    by_contra hx0
    have hνx0 : ν {x} = 0 := nonpos_iff_eq_zero.1 (not_lt.1 hx0)
    set R : ℝ := |x| + 1 with hR
    have hfin : ((Z₀ ∩ Icc 0 R) \ {x}).Finite :=
      (hZ R).subset fun y hy => ⟨hy.1.1.1, hy.1.2⟩
    have hx_mem : x ∈ Ioo (-R) R := ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    set U : Set ℝ := Ioo (-R) R ∩ ((Z₀ ∩ Icc 0 R) \ {x})ᶜ with hU
    have hUopen : IsOpen U := isOpen_Ioo.inter hfin.isClosed.isOpen_compl
    have hxU : x ∈ U := ⟨hx_mem, fun h => h.2 rfl⟩
    have hU_sub : U ⊆ Z₀ᶜ ∪ {x} := fun y hy => by
      by_cases hyZ : y ∈ Z₀
      · right
        by_contra hyx
        apply hy.2
        refine ⟨⟨hyZ, hyZ.2, hy.1.2.le⟩, hyx⟩
      · left; exact hyZ
    have hνU : ν U = 0 := measure_mono_null hU_sub (measure_union_null hνZ₀ hνx0)
    have hpos : 0 < ν U := (Measure.mem_support_iff_forall x).1 hx U (hUopen.mem_nhds hxU)
    exact absurd hνU hpos.ne'
  · rintro ⟨-, hpos⟩
    exact (Measure.mem_support_iff_forall x).2 fun U hU =>
      lt_of_lt_of_le hpos (measure_mono (singleton_subset_iff.2 (mem_of_mem_nhds hU)))

private lemma isIntegerCounting_of_locallyFinite_singletons {ν : Measure ℝ}
    (hnonneg : ν (Iio 0) = 0) {Z : Set ℝ} (hZ : ∀ R : ℝ, (Z ∩ Icc 0 R).Finite)
    (hνZ : ν Zᶜ = 0) (hint : ∀ x ∈ ν.support, ∃ n : ℕ, ν {x} = n) :
    IsIntegerCounting ν := by
  classical
  have hsupp_eq := support_eq_of_locallyFinite hnonneg hZ hνZ
  have hSfin : ∀ K : Set ℝ, IsCompact K → (ν.support ∩ K).Finite := by
    intro K hK
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · simp
    obtain ⟨R, -, hRmax⟩ := hK.exists_isMaxOn hKne continuous_id.continuousOn
    refine (hZ (max R 0)).subset fun x hx => ?_
    have hxS := hsupp_eq ▸ hx.1
    exact ⟨hxS.1.1, hxS.1.2, (isMaxOn_iff.1 hRmax x hx.2).trans (le_max_left R 0)⟩
  have hcount : ν.support.Countable := by
    have hcov : ν.support = ⋃ n : ℕ, ν.support ∩ Icc (-(n : ℝ)) n := by
      ext x
      simp only [mem_iUnion, mem_inter_iff, mem_Icc]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_ge |x|
        refine ⟨n, hx, ?_, ?_⟩ <;> linarith [abs_le.1 hn]
      · rintro ⟨_, hx, -⟩; exact hx
    rw [hcov]
    exact countable_iUnion fun n => (hSfin _ isCompact_Icc).countable
  choose d hd using hint
  refine ⟨ν.support, fun x => if hx : x ∈ ν.support then d x hx else 0, hSfin, fun x hx => ?_, ?_⟩
  · simp only [hx, ↓reduceDIte]
    have hpos : 0 < ν {x} := (hsupp_eq ▸ hx).2
    rw [hd x hx] at hpos
    exact_mod_cast hpos
  · ext A hA
    have h1 : ν (A ∩ ν.support) = ν A := measure_inter_conull Measure.measure_compl_support
    have hcA : (A ∩ ν.support).Countable := hcount.mono inter_subset_right
    have h2 : ν (A ∩ ν.support) = ∑' x : ↥(A ∩ ν.support), ν {(x : ℝ)} := by
      have := measure_biUnion (μ := ν) hcA (f := fun y => ({y} : Set ℝ))
        (by intro a _ b _ hab; simp [Function.onFun, hab]) (fun _ _ => measurableSet_singleton _)
      rwa [Set.biUnion_of_singleton] at this
    rw [← h1, h2, Measure.sum_apply _ hA, tsum_subtype (A ∩ ν.support) (fun y => ν {y})]
    have h3 : ∀ x : ν.support,
        (((if hx : (x : ℝ) ∈ ν.support then d (x : ℝ) hx else 0 : ℕ) : ℝ≥0∞) •
          Measure.dirac (x : ℝ)) A =
        A.indicator (fun y => ν {y}) (x : ℝ) := by
      intro x
      simp only [x.2, ↓reduceDIte, ← hd x x.2]
      by_cases hxA : (x : ℝ) ∈ A <;> simp [Measure.dirac_apply' _ hA, hxA]
    rw [tsum_congr h3, tsum_subtype ν.support (fun y => A.indicator (fun y => ν {y}) y)]
    refine tsum_congr fun y => ?_
    rw [Set.indicator_indicator, inter_comm]

/-- **Theorem INT-4(a)** (`integrality.tex`, `int:obstr`(a)) at fixed weight `(w, Q)`:
whenever at least one integer-degeneracy crossing spectrum with positive terminal threshold on
`F ∪ [τ, ∞)` exists (`F ⊂ (0, ∞)` compact, possibly empty), the supremal integer gap `T_ℤ` is
attained by an integer-degeneracy crossing spectrum (`IsGreatest`), `0 < T_ℤ ≤ T_F < ∞`, `0 < T_V`,
and `Δ_best^ℤ = Δ_best^ℝ` iff some attaining real crossing measure is integer-weighted (equivalently,
`Δ_best^ℤ < Δ_best^ℝ` iff no attaining real crossing measure is integer-weighted). -/
theorem int_obstr_a (prob : FixedWeightProblem) {cTilde : ℝ} (hc_pos : 0 < cTilde)
    (hc : 12 * prob.totalShift ≤ cTilde) {F : Set ℝ} (hFc : IsCompact F) (hF : F ⊆ Ioi 0)
    (hneZ : (constrainedIntGaps prob cTilde F).Nonempty) :
    (0 < constrainedIntThreshold prob cTilde F ∧
      constrainedIntThreshold prob cTilde F ≤ constrainedThreshold prob cTilde F ∧
      0 < prob.T_V cTilde) ∧
    IsGreatest (constrainedIntGaps prob cTilde F) (constrainedIntThreshold prob cTilde F) ∧
    ((constrainedDeltaBestInt prob cTilde F = constrainedDeltaBest prob cTilde F) ↔
      ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
        meas.ν (F ∪ Ici (constrainedThreshold prob cTilde F))ᶜ = 0 ∧
        IsIntegerCounting meas.ν) ∧
    ((constrainedDeltaBestInt prob cTilde F < constrainedDeltaBest prob cTilde F) ↔
      ∀ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
        meas.ν (F ∪ Ici (constrainedThreshold prob cTilde F))ᶜ = 0 →
        ¬ IsIntegerCounting meas.ν) := by
  classical
  set TZ : ℝ := constrainedIntThreshold prob cTilde F with hTZ
  set TF : ℝ := constrainedThreshold prob cTilde F with hTF
  obtain ⟨τ₁, hτ₁, g₁, hg₁⟩ := exists_feasible_of_compact prob hc_pos hc hFc hF
  have hne : (constrainedGaps prob cTilde F).Nonempty := ⟨τ₁, hτ₁, g₁, hg₁⟩
  have hbdd : BddAbove (constrainedIntGaps prob cTilde F) := by
    refine ⟨TF, ?_⟩
    rintro τ ⟨-, meas, hν, -⟩
    exact le_constrainedThreshold_of_crossingMeasure prob hc_pos hc hne meas hν
  obtain ⟨τ₀, hτ₀_mem⟩ := id hneZ
  obtain ⟨hτ₀_pos, meas₀, hν₀, -⟩ := id hτ₀_mem
  have hTZ_pos : 0 < TZ := lt_of_lt_of_le hτ₀_pos (le_csSup hbdd hτ₀_mem)
  have hTZ_le_TF : TZ ≤ TF := by
    refine csSup_le hneZ ?_
    rintro τ ⟨-, meas, hν, -⟩
    exact le_constrainedThreshold_of_crossingMeasure prob hc_pos hc hne meas hν
  obtain ⟨m, hm, hFm⟩ := exists_pos_lower_bound hFc hF
  have hTV_pos : 0 < prob.T_V cTilde := by
    set T₀' : ℝ := min m τ₀
    have hT₀'pos : 0 < T₀' := lt_min hm hτ₀_pos
    have hgap0 : meas₀.ν (Iio T₀') = 0 := by
      refine measure_mono_null (fun t ht => ?_) hν₀
      intro hmem
      rcases hmem with htF | htτ
      · exact absurd ((min_le_left m τ₀).trans (hFm htF)) (not_le.2 ht)
      · exact absurd ((min_le_right m τ₀).trans (mem_Ici.1 htτ)) (not_le.2 ht)
    have hD1 := (Duality.proposition_D1 prob hc hc_pos hT₀'pos ⟨meas₀, hgap0⟩).2.1
    exact lt_of_lt_of_le hT₀'pos hD1
  -- Choose `T₀ < T_Z` with `F ⊆ [T₀, ∞)` and `β₀` for `DualSetupCore`.
  set T₀ : ℝ := min m (TZ / 2) with hT₀def
  have hT₀pos : 0 < T₀ := lt_min hm (half_pos hTZ_pos)
  have hT₀TZ : T₀ < TZ := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hTZ_pos)
  have hF0 : F ⊆ Ici T₀ := fun t ht => (min_le_left _ _).trans (hFm ht)
  obtain ⟨β₀, hβ₀, hβ₀2, hβ₀t⟩ := exists_beta0 prob.w hT₀pos
  let S : DualSetupCore prob cTilde β₀ T₀ := ⟨hc_pos, hc, hβ₀, hβ₀2, hβ₀t, hT₀pos⟩
  -- Decreasing sequence of supports `X_k = F ∪ [σ_k, ∞)` with `σ_k ↑ T_Z`.
  let σ : ℕ → ℝ := fun k => TZ - (TZ - T₀) / (k + 2)
  have hσ0 : ∀ k, T₀ ≤ σ k := fun k => by
    have : (TZ - T₀) / (k + 2) ≤ TZ - T₀ :=
      div_le_self (by linarith) (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    show T₀ ≤ TZ - (TZ - T₀) / (k + 2); linarith
  have hσlt : ∀ k, σ k < TZ := fun k => by
    have : 0 < (TZ - T₀) / (k + 2) :=
      div_pos (by linarith) (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    show TZ - (TZ - T₀) / (k + 2) < TZ; linarith
  have hσmono : Monotone σ := by
    refine monotone_nat_of_le_succ fun k => ?_
    show TZ - (TZ - T₀) / (k + 2) ≤ TZ - (TZ - T₀) / ((k + 1 : ℕ) + 2)
    have h1 : (TZ - T₀) / (((k + 1 : ℕ) : ℝ) + 2) ≤ (TZ - T₀) / (k + 2) := by
      refine div_le_div_of_nonneg_left (by linarith)
        (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) ?_
      push_cast; linarith
    linarith
  have hpick : ∀ k : ℕ, ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν (F ∪ Ici (σ k))ᶜ = 0 ∧ IsIntegerCounting meas.ν := fun k => by
    obtain ⟨τ, hτ_mem, hστ⟩ := (lt_csSup_iff hbdd hneZ).1 (hσlt k)
    obtain ⟨-, meas, hν, hint⟩ := hτ_mem
    refine ⟨meas, measure_mono_null (compl_subset_compl.2
      (union_subset_union_right F (Ici_subset_Ici.2 hστ.le))) hν, hint⟩
  choose meas hmsupp hmint using hpick
  let X : ℕ → Set ℝ := fun k => F ∪ Ici (σ k)
  have hXc : ∀ k, IsClosed (X k) := fun k => hFc.isClosed.union isClosed_Ici
  have hXa : Antitone X := fun j k hjk => union_subset_union_right F (Ici_subset_Ici.2 (hσmono hjk))
  have hX0 : X 0 ⊆ Ici T₀ := union_subset hF0 (Ici_subset_Ici.2 (hσ0 0))
  let 𝒰 : Ultrafilter ℕ := Ultrafilter.of atTop
  have h𝒰 : (𝒰 : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨meas', hlim, hsupp', -, -⟩ :=
    theorem_E_a_compactness prob S hXc hXa hX0 meas hmsupp 𝒰 h𝒰
  have hInter : (⋂ k, X k) = F ∪ Ici TZ := by
    refine Subset.antisymm (fun y hy => ?_) (fun y hy => mem_iInter.2 fun k => ?_)
    · by_cases hyF : y ∈ F
      · exact Or.inl hyF
      · refine Or.inr ?_
        have hall : ∀ k, σ k ≤ y := fun k => by
          rcases mem_iInter.1 hy k with h | h
          · exact absurd h hyF
          · exact h
        by_contra hlt0
        have hlt : y < TZ := by simpa using hlt0
        obtain ⟨k, hk⟩ := exists_nat_gt ((TZ - T₀) / (TZ - y))
        have hpos : 0 < TZ - y := by linarith
        have : (TZ - T₀) / (k + 2) < TZ - y := by
          rw [div_lt_iff₀ (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)]
          have := (div_lt_iff₀ hpos).mp hk
          nlinarith
        have h2 := hall k
        have : y < σ k := by show y < TZ - (TZ - T₀) / (k + 2); linarith
        linarith
    · rcases hy with hy | hy
      · exact Or.inl hy
      · exact Or.inr (le_trans (hσlt k).le hy)
  rw [hInter] at hsupp'
  have := meas'.isFiniteMeasureOnCompacts
  have hmeas'_int : IsIntegerCounting meas'.ν := isIntegerCounting_of_vagueLimit hmint hlim
  have hmemZ : TZ ∈ constrainedIntGaps prob cTilde F := ⟨hTZ_pos, meas', hsupp', hmeas'_int⟩
  have hGreatest : IsGreatest (constrainedIntGaps prob cTilde F) TZ :=
    ⟨hmemZ, fun τ hτ => le_csSup hbdd hτ⟩
  have hiff_eq : (constrainedDeltaBestInt prob cTilde F = constrainedDeltaBest prob cTilde F) ↔
      ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
        meas.ν (F ∪ Ici TF)ᶜ = 0 ∧ IsIntegerCounting meas.ν := by
    unfold constrainedDeltaBestInt constrainedDeltaBest
    rw [add_right_inj]
    constructor
    · intro heq
      rw [hTZ, heq, ← hTF] at hsupp'
      exact ⟨meas', hsupp', hmeas'_int⟩
    · rintro ⟨meas, hν, hint⟩
      have hTF_pos : 0 < TF := lt_of_lt_of_le hTZ_pos hTZ_le_TF
      have hle : TF ≤ TZ := le_csSup hbdd ⟨hTF_pos, meas, hν, hint⟩
      exact le_antisymm hTZ_le_TF hle
  have hiff_lt : (constrainedDeltaBestInt prob cTilde F < constrainedDeltaBest prob cTilde F) ↔
      ∀ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
        meas.ν (F ∪ Ici TF)ᶜ = 0 → ¬ IsIntegerCounting meas.ν := by
    have hle : constrainedDeltaBestInt prob cTilde F ≤ constrainedDeltaBest prob cTilde F := by
      unfold constrainedDeltaBestInt constrainedDeltaBest
      linarith
    rw [lt_iff_le_and_ne, and_iff_right hle, ne_eq, hiff_eq]
    push Not
    rfl
  exact ⟨⟨hTZ_pos, hTZ_le_TF, hTV_pos⟩, hGreatest, hiff_eq, hiff_lt⟩

/-- **Theorem INT-4(a), primal-atomicity form** (`integrality.tex`, `int:obstr`(a)):
at every fixed charge `c̃ > 0` with `12 S ≤ c̃`, every attaining real crossing measure on
`F ∪ [T_F, ∞)` is locally finite atomic, and `Δ_best^ℤ < Δ_best^ℝ` strictly iff every attaining
real crossing measure has at least one support point (atom) of non-integer weight. -/
theorem int_obstr_a_primal {prob : FixedWeightProblem} {cTilde : ℝ}
    (hc_pos : 0 < cTilde) (hc : 12 * prob.totalShift ≤ cTilde)
    {F : Set ℝ} (hFc : IsCompact F) (hF : F ⊆ Ioi 0)
    (hneZ : (constrainedIntGaps prob cTilde F).Nonempty) :
    (∀ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν (F ∪ Ici (constrainedThreshold prob cTilde F))ᶜ = 0 →
      ∃ Z : Set ℝ, (∀ R : ℝ, (Z ∩ Icc 0 R).Finite) ∧ meas.ν Zᶜ = 0) ∧
    ((constrainedDeltaBestInt prob cTilde F < constrainedDeltaBest prob cTilde F) ↔
      ∀ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
        meas.ν (F ∪ Ici (constrainedThreshold prob cTilde F))ᶜ = 0 →
        ∃ x ∈ meas.ν.support, ∀ n : ℕ, meas.ν {x} ≠ n) := by
  obtain ⟨-, -, -, hiff_lt⟩ := int_obstr_a prob hc_pos hc hFc hF hneZ
  obtain ⟨-, gs, -, -, hprim_loc, -⟩ := theorem_primal hc_pos hc hFc hF
  refine ⟨fun meas hν => (hprim_loc meas hν).1, ?_⟩
  rw [hiff_lt]
  refine forall₂_congr fun meas hν => ?_
  obtain ⟨Z, hZfin, hνZ⟩ := (hprim_loc meas hν).1
  constructor
  · intro hnot
    by_contra hcon
    push Not at hcon
    exact hnot (isIntegerCounting_of_locallyFinite_singletons meas.supp_nonneg hZfin hνZ hcon)
  · rintro ⟨x, -, hxne⟩ hint
    obtain ⟨n, hn⟩ := isIntegerCounting_singletons_of_isIntegerCounting hint x
    exact hxne n hn

end Proofs

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Integrality.int_obstr_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Integrality.int_obstr_a

/-- info: 'FormalResearch.ModularBootstrap.Integrality.int_obstr_a_primal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Integrality.int_obstr_a_primal

end FormalResearch.ModularBootstrap.Integrality
