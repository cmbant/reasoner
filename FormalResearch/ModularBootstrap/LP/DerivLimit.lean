module

public import FormalResearch.ModularBootstrap.LP.DerivLimitII
public import FormalResearch.ModularBootstrap.Duality.ConstrainedThreshold

/-!
# Theorem LP (`ds:LP`): the infinite-order derivative limit

`CFT/modular_bootstrap/paper/dual_spectrum.tex`, Theorem LP (line 221).  For `prob : FixedWeightProblem`
at `c̃ > 0`, `c̃ ≥ 12 S`, `a = c̃/12`:

* (i) (`ds_LP_i`) for a closed `X ⊂ [T₀, ∞)`, `T₀ > 0`: no finite odd-Laguerre test `g = e^{-2πt} p`,
  `p ∈ ⋃ O_N`, is nonnegative on `X` with `g_vac > 0` iff a crossing measure carried by `X` exists;
  the implication (b) ⇒ (a) holds for every `X` (`ds_LP_b_imp_a`).
* (ii) (`ds_LP_ii`) for closed `F ⊂ [T₀, ∞)` and `X_τ = F ∪ [τ, ∞)`: if `T₀ < T_F^{[∞]} < ∞` then
  `T_F^{[∞]} = max {τ > 0 : a crossing measure carried by X_τ exists}`.
* (iii) (`ds_LP_iii`) at every charge with `T_V > 0`: `T_V = inf_P T_P = lim_N T_∅^{[N]}
  = max {τ : a crossing measure at gap τ exists}`.

`T_F^{[N]}` (`thrN`) is the infimum of the `τ > 0` for which a finite odd-Laguerre test `p ∈ O_N` is
feasible on `F ∪ [τ, ∞)`, with values in `[0, ∞]` (`inf ∅ = ∞`), and `T_F^{[∞]} = inf_N T_F^{[N]}`.
No membership `e^{-2πt} O_N ⊂ Ā_w` is used: the exact pairing for crossing measures (`ds:cay`) and the
existing crossing measure at gap `T_V` (`theorem_E_b_compact`) give all the needed comparisons.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open scoped ENNReal
open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.Duality
  FormalResearch.ModularBootstrap.FixedWeight

namespace FormalResearch.ModularBootstrap.LP

variable (prob : FixedWeightProblem) (a : ℝ)

/-- `T_F^{[N]}`: the infimum of `τ > 0` such that a finite odd-Laguerre test `p ∈ O_N` is feasible on
`F ∪ [τ, ∞)` (`∞` if there is none). -/
noncomputable def thrN (F : Set ℝ) (N : ℕ) : ℝ≥0∞ :=
  ⨅ (τ : ℝ) (_ : 0 < τ ∧ ∃ p, OddFeasible prob a N (F ∪ Ici τ) p), ENNReal.ofReal τ

/-- `T_F^{[∞]} = inf_N T_F^{[N]}`. -/
noncomputable def thrInf (F : Set ℝ) : ℝ≥0∞ := ⨅ N : ℕ, thrN prob a F N

variable {prob a}

lemma thrN_le_of_feasible {F : Set ℝ} {N : ℕ} {τ : ℝ} (hτ : 0 < τ) {p : ℝ → ℝ}
    (hp : OddFeasible prob a N (F ∪ Ici τ) p) : thrN prob a F N ≤ ENNReal.ofReal τ :=
  iInf₂_le τ ⟨hτ, p, hp⟩

lemma thrInf_le_of_feasible {F : Set ℝ} {N : ℕ} {τ : ℝ} (hτ : 0 < τ) {p : ℝ → ℝ}
    (hp : OddFeasible prob a N (F ∪ Ici τ) p) : thrInf prob a F ≤ ENNReal.ofReal τ :=
  (iInf_le _ N).trans (thrN_le_of_feasible hτ hp)

lemma thrN_antitone (F : Set ℝ) : Antitone (thrN prob a F) := by
  intro M N hMN
  refine le_iInf₂ fun τ hτ => ?_
  obtain ⟨hτ0, p, hp⟩ := hτ
  exact thrN_le_of_feasible hτ0 (hp.mono_N hMN)

/-- A crossing measure carried by `F ∪ [τ, ∞)` forces `τ ≤ T_F^{[N]}` for every `N`. -/
lemma le_thrN_of_crossingMeasure (ha : prob.totalShift ≤ a) {F : Set ℝ} {τ : ℝ}
    (meas : AdmissibleCrossingMeasure prob a) (hν : meas.ν (F ∪ Ici τ)ᶜ = 0) (N : ℕ) :
    ENNReal.ofReal τ ≤ thrN prob a F N := by
  refine le_iInf₂ fun τ' hτ' => ?_
  obtain ⟨hτ'0, p, hp⟩ := hτ'
  by_contra hlt
  have hlt' : τ' < τ := by
    by_contra h; exact hlt (ENNReal.ofReal_le_ofReal (not_lt.1 h))
  have hsub : F ∪ Ici τ ⊆ F ∪ Ici τ' := union_subset_union_right F (Ici_subset_Ici.2 hlt'.le)
  exact not_oddFeasible_of_crossingMeasure ha meas hν N p (hp.mono_X hsub)

lemma not_oddFeasible_of_lt_thrInf {F : Set ℝ} {τ : ℝ} (hτ : 0 < τ)
    (h : ENNReal.ofReal τ < thrInf prob a F) (N : ℕ) (p : ℝ → ℝ) :
    ¬ OddFeasible prob a N (F ∪ Ici τ) p := fun hp =>
  absurd (thrInf_le_of_feasible hτ hp) (not_le.2 h)

/-! ### (i) -/

/-- **`ds:LP`(i)**: for a closed `X ⊂ [T₀, ∞)` with `T₀ > 0`, no finite odd-Laguerre test `g = e^{-2πt}p`
(`p ∈ ⋃ O_N`) is nonnegative on `X` with `g_vac > 0` iff a crossing measure carried by `X` exists. -/
theorem ds_LP_i (ha : prob.totalShift ≤ a) {T₀ : ℝ} (hT₀ : 0 < T₀) {X : Set ℝ} (hXc : IsClosed X)
    (hX : X ⊆ Ici T₀) :
    (∀ N p, ¬ OddFeasible prob a N X p) ↔
      ∃ meas : AdmissibleCrossingMeasure prob a, meas.ν Xᶜ = 0 :=
  ⟨exists_crossingMeasure_of_not_oddFeasible ha hT₀ hXc hX,
    fun ⟨meas, hν⟩ N p => not_oddFeasible_of_crossingMeasure ha meas hν N p⟩

/-- **`ds:LP`(i)**, the implication (b) ⇒ (a), for every `X`. -/
theorem ds_LP_b_imp_a (ha : prob.totalShift ≤ a) (meas : AdmissibleCrossingMeasure prob a)
    {X : Set ℝ} (hν : meas.ν Xᶜ = 0) : ∀ N p, ¬ OddFeasible prob a N X p :=
  fun N p => not_oddFeasible_of_crossingMeasure ha meas hν N p

/-! ### (ii) -/

/-- Decreasing-support compactness (`ds:E`(a)) fed by `ds:LP`(i): if no finite odd-Laguerre test is
feasible on `F ∪ [τ, ∞)` for every `τ ∈ [T₀, τ*)`, there is a crossing measure carried by
`F ∪ [τ*, ∞)`. -/
theorem exists_crossingMeasure_at_limit {cTilde : ℝ} (hc_pos : 0 < cTilde)
    (hc : 12 * prob.totalShift ≤ cTilde) {T₀ : ℝ} (hT₀ : 0 < T₀) {F : Set ℝ} (hFc : IsClosed F)
    (hF : F ⊆ Ici T₀) {τs : ℝ} (hτs : T₀ < τs)
    (hno : ∀ τ, T₀ ≤ τ → τ < τs → ∀ N p, ¬ OddFeasible prob (cTilde / 12) N (F ∪ Ici τ) p) :
    ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12), meas.ν (F ∪ Ici τs)ᶜ = 0 := by
  have ha : prob.totalShift ≤ cTilde / 12 := by linarith
  obtain ⟨β₀, hβ₀, hβ₀2, hβ₀t⟩ := FixedWeight.exists_beta0 prob.w hT₀
  have S : DualSetupCore prob cTilde β₀ T₀ := ⟨hc_pos, hc, hβ₀, hβ₀2, hβ₀t, hT₀⟩
  let τ : ℕ → ℝ := fun n => τs - (τs - T₀) / (n + 2)
  have hτ0 : ∀ n, T₀ ≤ τ n := fun n => by
    have : (τs - T₀) / (n + 2) ≤ τs - T₀ :=
      div_le_self (by linarith) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    show T₀ ≤ τs - (τs - T₀) / (n + 2); linarith
  have hτlt : ∀ n, τ n < τs := fun n => by
    have : 0 < (τs - T₀) / (n + 2) :=
      div_pos (by linarith) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    show τs - (τs - T₀) / (n + 2) < τs; linarith
  have hτmono : Monotone τ := by
    refine monotone_nat_of_le_succ fun n => ?_
    show τs - (τs - T₀) / (n + 2) ≤ τs - (τs - T₀) / ((n + 1 : ℕ) + 2)
    have h1 : (τs - T₀) / (((n + 1 : ℕ) : ℝ) + 2) ≤ (τs - T₀) / (n + 2) := by
      refine div_le_div_of_nonneg_left (by linarith)
        (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) ?_
      push_cast; linarith
    linarith
  let X : ℕ → Set ℝ := fun n => F ∪ Ici (τ n)
  have hXc : ∀ n, IsClosed (X n) := fun n => hFc.union isClosed_Ici
  have hXa : Antitone X := fun m n hmn => union_subset_union_right F (Ici_subset_Ici.2 (hτmono hmn))
  have hX0 : X 0 ⊆ Ici T₀ := union_subset hF (Ici_subset_Ici.2 (hτ0 0))
  have hns : ∀ n, NoSpanFeasible prob cTilde β₀ (X n) := fun n => by
    obtain ⟨meas, hν⟩ := exists_crossingMeasure_of_not_oddFeasible ha hT₀ (hXc n)
      (union_subset hF (Ici_subset_Ici.2 (hτ0 n))) (hno (τ n) (hτ0 n) (hτlt n))
    exact noSpanFeasible_of_crossingMeasure prob hc_pos hc hβ₀ hβ₀2 meas hν
  obtain ⟨meas, hν, -, -⟩ := theorem_E_a_decreasing prob S hXc hXa hX0 hns
  have hInter : (⋂ n, X n) = F ∪ Ici τs := by
    refine Subset.antisymm (fun y hy => ?_) (fun y hy => mem_iInter.2 fun n => ?_)
    · by_cases hyF : y ∈ F
      · exact Or.inl hyF
      · refine Or.inr ?_
        have hall : ∀ n, τ n ≤ y := fun n => by
          rcases mem_iInter.1 hy n with h | h
          · exact absurd h hyF
          · exact h
        by_contra hlt0
        have hlt : y < τs := by simpa using hlt0
        obtain ⟨n, hn⟩ := exists_nat_gt ((τs - T₀) / (τs - y))
        have hpos : 0 < τs - y := by linarith
        have : (τs - T₀) / (n + 2) < τs - y := by
          rw [div_lt_iff₀ (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)]
          have := (div_lt_iff₀ hpos).mp hn
          nlinarith
        have h2 := hall n
        have : y < τ n := by show y < τs - (τs - T₀) / (n + 2); linarith
        linarith
    · rcases hy with hy | hy
      · exact Or.inl hy
      · exact Or.inr (le_trans (hτlt n).le hy)
  exact ⟨meas, by rw [← hInter]; exact hν⟩

/-- **`ds:LP`(ii)**: for a closed `F ⊂ [T₀, ∞)`, `T₀ > 0`, `X_τ = F ∪ [τ, ∞)`, if
`T₀ < T_F^{[∞]} < ∞` then `T_F^{[∞]} = max {τ > 0 : a crossing measure carried by X_τ exists}`. -/
theorem ds_LP_ii {cTilde : ℝ} (hc_pos : 0 < cTilde) (hc : 12 * prob.totalShift ≤ cTilde)
    {T₀ : ℝ} (hT₀ : 0 < T₀) {F : Set ℝ} (hFc : IsClosed F) (hF : F ⊆ Ici T₀)
    (hlow : ENNReal.ofReal T₀ < thrInf prob (cTilde / 12) F)
    (hfin : thrInf prob (cTilde / 12) F < ⊤) :
    IsGreatest {τ : ℝ | 0 < τ ∧ ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν (F ∪ Ici τ)ᶜ = 0} (thrInf prob (cTilde / 12) F).toReal := by
  have ha : prob.totalShift ≤ cTilde / 12 := by linarith
  set τs := (thrInf prob (cTilde / 12) F).toReal with hτs
  have hofr : ENNReal.ofReal τs = thrInf prob (cTilde / 12) F := ENNReal.ofReal_toReal hfin.ne
  have hT₀τ : T₀ < τs := by
    have := hlow; rw [← hofr] at this
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hT₀.le).1 this
  refine ⟨⟨by linarith, ?_⟩, fun τ hτ => ?_⟩
  · refine exists_crossingMeasure_at_limit hc_pos hc hT₀ hFc hF hT₀τ fun τ h0 hlt N p => ?_
    refine not_oddFeasible_of_lt_thrInf (by linarith) ?_ N p
    rw [← hofr]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hlt
  · obtain ⟨hτ0, meas, hν⟩ := hτ
    have h1 : ENNReal.ofReal τ ≤ thrInf prob (cTilde / 12) F :=
      le_iInf fun N => le_thrN_of_crossingMeasure ha meas hν N
    rw [← hofr] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h1

/-! ### (iii) -/

/-- **`ds:LP`(iii)**: at every fixed weight `(w, Q)` with `c̃ > 0`, `c̃ ≥ 12 S` and `T_V(c̃) > 0`,
`T_V = T_∅^{[∞]} = lim_N T_∅^{[N]} = inf_P T_∅^{[2P+1]}`, and `T_V` is the maximal gap `τ` for which
a crossing measure carried by `[τ, ∞)` exists. -/
theorem ds_LP_iii {cTilde : ℝ} (hc_pos : 0 < cTilde) (hc : 12 * prob.totalShift ≤ cTilde)
    (hTV : 0 < prob.T_V cTilde) :
    thrInf prob (cTilde / 12) ∅ = ENNReal.ofReal (prob.T_V cTilde) ∧
    Tendsto (fun N => thrN prob (cTilde / 12) ∅ N) atTop (𝓝 (ENNReal.ofReal (prob.T_V cTilde))) ∧
    (⨅ P : ℕ, thrN prob (cTilde / 12) ∅ (2 * P + 1)) = ENNReal.ofReal (prob.T_V cTilde) ∧
    IsGreatest {τ : ℝ | 0 < τ ∧ ∃ meas : AdmissibleCrossingMeasure prob (cTilde / 12),
      meas.ν (Ici τ)ᶜ = 0} (prob.T_V cTilde) := by
  have ha : prob.totalShift ≤ cTilde / 12 := by linarith
  -- the crossing measure at gap `T_V`
  obtain ⟨-, hmax, -, -⟩ := theorem_E_b_compact prob hc_pos hc (F := ∅) isCompact_empty
    (empty_subset _) hTV
  rw [constrainedThreshold_empty] at hmax
  obtain ⟨-, meas, hmeas⟩ := hmax.1
  rw [empty_union] at hmeas
  have hge : ∀ N, ENNReal.ofReal (prob.T_V cTilde) ≤ thrN prob (cTilde / 12) ∅ N := fun N =>
    le_thrN_of_crossingMeasure ha meas (by rw [empty_union]; exact hmeas) N
  have hle : thrInf prob (cTilde / 12) ∅ ≤ ENNReal.ofReal (prob.T_V cTilde) := by
    by_contra hlt
    obtain ⟨τ, hτ0, hτ1, hτ2⟩ := ENNReal.lt_iff_exists_real_btwn.1 (not_le.1 hlt)
    have hTτ : prob.T_V cTilde < τ := (ENNReal.ofReal_lt_ofReal_iff'.1 hτ1).1
    have hτpos : 0 < τ := lt_trans hTV hTτ
    have hno := not_oddFeasible_of_lt_thrInf hτpos hτ2
    obtain ⟨m, hm⟩ := (ds_LP_i ha hτpos (X := ∅ ∪ Ici τ) (isClosed_empty.union isClosed_Ici)
      (by rw [empty_union])).1 hno
    rw [empty_union, compl_Ici] at hm
    have := (proposition_D1 prob hc hc_pos hτpos ⟨m, hm⟩).2.1
    linarith
  have heq : thrInf prob (cTilde / 12) ∅ = ENNReal.ofReal (prob.T_V cTilde) :=
    le_antisymm hle (le_iInf hge)
  refine ⟨heq, ?_, ?_, ?_⟩
  · rw [← heq]; exact tendsto_atTop_iInf (thrN_antitone ∅)
  · refine le_antisymm ?_ (le_iInf fun P => (hge _))
    rw [← heq]
    refine le_iInf fun N => (iInf_le _ N).trans ?_
    exact thrN_antitone ∅ (by omega)
  · refine ⟨⟨hTV, meas, by rw [← empty_union (Ici _)]; rw [empty_union]; exact hmeas⟩, ?_⟩
    rintro τ ⟨hτ0, m, hm⟩
    rw [compl_Ici] at hm
    exact (proposition_D1 prob hc hc_pos hτ0 ⟨m, hm⟩).2.1

/-- info: 'FormalResearch.ModularBootstrap.LP.ds_LP_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ds_LP_i

/-- info: 'FormalResearch.ModularBootstrap.LP.ds_LP_b_imp_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ds_LP_b_imp_a

/-- info: 'FormalResearch.ModularBootstrap.LP.ds_LP_ii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ds_LP_ii

/-- info: 'FormalResearch.ModularBootstrap.LP.ds_LP_iii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ds_LP_iii

end FormalResearch.ModularBootstrap.LP
