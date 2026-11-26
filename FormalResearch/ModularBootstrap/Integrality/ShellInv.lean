module

public import FormalResearch.ModularBootstrap.Integrality.ShellInvStep
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Shell atomisation: the recursion and its limit (`int:shell-inv`)

`CFT/modular_bootstrap/paper/integrality.tex`, Proposition INT-S, aggregated form.  Given the
stage-`j` step data for every stage (`AggStep`), the recursion
`Σ^{(j+1)} = Σ^{(j)} + σ_j`, `λ^{(j+1)} = λ^{(j)} - μ_j + Rp_j - Rm_j` preserves the invariants
(`exists_next`), and `ν_ℤ = ∑_j σ_j` is locally finite, integer atomic, obeys the envelope bound
`∫ e_γ dν_ℤ ≤ (9/4) C_γ ∫ e_{γ'} dν⁰` and `∫ K_α dν_ℤ = c_α`.  **Proved.**
-/

@[expose] public section

open MeasureTheory Set Finset Filter Topology
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.Integrality

set_option linter.unusedSectionVars false

/-- Dependent choice along a relation preserving a predicate. -/
lemma exists_seq {α : Type*} (P : ℕ → α → Prop) (R : ℕ → α → α → Prop) (a0 : α) (h0 : P 0 a0)
    (hs : ∀ j a, P j a → ∃ b, P (j + 1) b ∧ R j a b) :
    ∃ f : ℕ → α, f 0 = a0 ∧ ∀ j, P j (f j) ∧ R j (f j) (f (j + 1)) := by
  let g : (j : ℕ) → {a : α // P j a} := fun j =>
    Nat.rec ⟨a0, h0⟩ (fun j p => ⟨Classical.choose (hs j p.1 p.2),
      (Classical.choose_spec (hs j p.1 p.2)).1⟩) j
  refine ⟨fun j => (g j).1, rfl, fun j => ⟨(g j).2, ?_⟩⟩
  exact (Classical.choose_spec (hs j (g j).1 (g j).2)).2

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

namespace ShellSetup

lemma IsIntAtomicOn.measure_eq_zero {T A : Set X} {σ : Measure X} (hσ : IsIntAtomicOn T σ)
    (hA : MeasurableSet A) (hd : Disjoint A T) : σ A = 0 := by
  obtain ⟨ι, hι, x, d, hd', rfl⟩ := hσ
  have hx : ∀ i, x i ∉ A := fun i hxi => Set.disjoint_left.1 hd hxi (hd' i).2
  simp [Measure.dirac_apply' _ hA, hx]

variable (S : ShellSetup X) [SigmaFinite S.ν0]

lemma cm_le_nu0_of_le_one {a : ℝ} (ha : 0 ≤ a) (h1 : a ≤ 1) : S.cm a ≤ S.ν0 := by
  refine (S.cm_le_nu0 ha).trans ?_
  have := smul_coef_mono (c := ENNReal.ofReal a) (c' := 1)
    (by simpa using ENNReal.ofReal_le_ofReal h1) S.ν0
  simpa using this

/-- Stage `0`: `Σ⁰ = 0`, `λ⁰ = ν⁰`. -/
lemma inv_zero : S.Inv 0 0 S.ν0 := by
  refine ⟨⟨Empty, inferInstance, Empty.elim, Empty.elim, by simp, by simp⟩, ?_,
    meas_le_self_add _ _, ?_, ?_, ?_⟩
  · rw [S.Ω_zero]; simp
  · intro A _ _
    exact S.cm_le_nu0_of_le_one (by norm_num) (by norm_num) A
  · intro A _ _
    exact S.cm_le_nu0_of_le_one (by unfold cE; norm_num) (by unfold cE; norm_num) A
  · intro α
    simp [S.ν0_K α]

lemma shell_disjoint : Pairwise (Function.onFun Disjoint S.shell) := by
  intro i k hik
  wlog h : i < k generalizing i k
  · exact (this hik.symm (by omega)).symm
  refine Set.disjoint_left.2 fun x hx hx' => hx'.2 ?_
  exact S.Ω_mono (by omega) hx.1

lemma hinv_K {j : ℕ} {Sg lam : Measure X} (h : S.Inv j Sg lam) (α : S.I) :
    ∫ x, S.K α x ∂Sg + ∫ x, S.K α x ∂lam = S.c α := h.2.2.2.2.2 α

/-- Compact sets meet only finitely much of `∑ σ_j`. -/
lemma sum_lt_top_of_compact {σ : ℕ → Measure X}
    (hatom : ∀ j, IsIntAtomicOn (closure (S.Ω (j + 2)) \ S.Ω j) (σ j))
    {T : Set X} (hT : IsCompact T) : Measure.sum σ T < ∞ := by
  have hcov : T ⊆ ⋃ k, S.Ω k := by rw [S.Ω_cover]; exact subset_univ _
  obtain ⟨l, hl⟩ := hT.elim_directed_cover S.Ω S.Ω_open hcov S.Ω_mono.directed_le
  have hz : ∀ i, l ≤ i → σ i (S.Ω l) = 0 := fun i hi =>
    (hatom i).measure_eq_zero (S.measurableSet_Ω l)
      (Set.disjoint_left.2 fun x hx hx' => hx'.2 (S.Ω_mono hi hx))
  calc Measure.sum σ T ≤ Measure.sum σ (S.Ω l) := measure_mono hl
    _ = ∑' i, σ i (S.Ω l) := Measure.sum_apply _ (S.measurableSet_Ω l)
    _ = ∑ i ∈ range l, σ i (S.Ω l) :=
        tsum_eq_sum fun i hi => hz i (by simpa using hi)
    _ < ∞ := by
        refine ENNReal.sum_lt_top.2 fun i _ => ?_
        have := (hatom i).isFiniteMeasure
        exact measure_lt_top _ _

/-- The envelope bound `∫ e_γ d(∑ σ_j) ≤ (9/4) C_γ ∫ e_{γ'} dν⁰`. -/
lemma lintegral_sum_le {σ μ lam : ℕ → Measure X} {Sgj : ℕ → Measure X}
    (hinv : ∀ j, S.Inv j (Sgj j) (lam j))
    (hmu_le : ∀ j, μ j ≤ lam j)
    (hmu_supp : ∀ j, μ j (S.shell j ∪ S.shell (j + 1))ᶜ = 0)
    (hcomp : ∀ j γ, ∫⁻ x, ENNReal.ofReal (S.e γ x) ∂σ j ≤
      ENNReal.ofReal (S.C γ) * ∫⁻ x, ENNReal.ofReal (S.e (S.γ' γ) x) ∂μ j) (γ : S.Γ) :
    ∫⁻ x, ENNReal.ofReal (S.e γ x) ∂Measure.sum σ ≤
      ENNReal.ofReal (9 / 4 * S.C γ) * ∫⁻ x, ENNReal.ofReal (S.e (S.γ' γ) x) ∂S.ν0 := by
  set f : X → ℝ≥0∞ := fun x => ENNReal.ofReal (S.e (S.γ' γ) x) with hf
  set a : ℕ → ℝ≥0∞ := fun j => ∫⁻ x in S.shell j, f x ∂S.ν0 with ha
  have hstep : ∀ j, ∫⁻ x, f x ∂μ j ≤ ENNReal.ofReal (9 / 8) * (a j + a (j + 1)) := by
    intro j
    have hae : ∀ᵐ x ∂μ j, x ∈ S.shell j ∪ S.shell (j + 1) := by
      have := measure_eq_zero_iff_ae_notMem.1 (hmu_supp j)
      exact this.mono fun x hx => Set.notMem_compl_iff.1 hx
    have h1 : μ j = (μ j).restrict (S.shell j ∪ S.shell (j + 1)) :=
      (Measure.restrict_eq_self_of_ae_mem hae).symm
    have h2 : (μ j).restrict (S.shell j ∪ S.shell (j + 1)) ≤
        (ENNReal.ofReal (9 / 8) • S.ν0).restrict (S.shell j ∪ S.shell (j + 1)) :=
      Measure.restrict_mono subset_rfl ((hmu_le j).trans (S.lam_le_nu0 (hinv j)))
    calc ∫⁻ x, f x ∂μ j = ∫⁻ x, f x ∂(μ j).restrict (S.shell j ∪ S.shell (j + 1)) := by
          rw [← h1]
      _ ≤ ∫⁻ x, f x ∂(ENNReal.ofReal (9 / 8) • S.ν0).restrict (S.shell j ∪ S.shell (j + 1)) :=
          lintegral_mono' h2 le_rfl
      _ = ENNReal.ofReal (9 / 8) * ∫⁻ x in S.shell j ∪ S.shell (j + 1), f x ∂S.ν0 := by
          rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
      _ ≤ ENNReal.ofReal (9 / 8) * (a j + a (j + 1)) := by
          gcongr
          exact lintegral_union_le _ _ _
  have hA : ∑' j, a j ≤ ∫⁻ x, f x ∂S.ν0 := by
    have := lintegral_iUnion (μ := S.ν0) (f := f) (fun j => S.measurableSet_shell j)
      S.shell_disjoint
    rw [ha]
    rw [← this]
    exact setLIntegral_le_lintegral _ _
  have hA1 : ∑' j, a (j + 1) ≤ ∑' j, a j :=
    tsum_comp_le_tsum_of_injective (f := fun j => j + 1) (add_left_injective 1) a
  calc ∫⁻ x, ENNReal.ofReal (S.e γ x) ∂Measure.sum σ
      = ∑' j, ∫⁻ x, ENNReal.ofReal (S.e γ x) ∂σ j := lintegral_sum_measure _ _
    _ ≤ ∑' j, ENNReal.ofReal (S.C γ) * ∫⁻ x, f x ∂μ j := tsum_le_tsum fun j => hcomp j γ
    _ ≤ ∑' j, ENNReal.ofReal (S.C γ) * (ENNReal.ofReal (9 / 8) * (a j + a (j + 1))) :=
        tsum_le_tsum fun j => by gcongr; exact hstep j
    _ = ENNReal.ofReal (S.C γ) * (ENNReal.ofReal (9 / 8) * (∑' j, a j + ∑' j, a (j + 1))) := by
        rw [ENNReal.tsum_mul_left]
        congr 1
        rw [ENNReal.tsum_mul_left, tsum_add]
    _ ≤ ENNReal.ofReal (S.C γ) * (ENNReal.ofReal (9 / 8) * (2 * ∫⁻ x, f x ∂S.ν0)) := by
        gcongr
        calc ∑' j, a j + ∑' j, a (j + 1) ≤ ∑' j, a j + ∑' j, a j := by gcongr
          _ ≤ ∫⁻ x, f x ∂S.ν0 + ∫⁻ x, f x ∂S.ν0 := by gcongr
          _ = 2 * ∫⁻ x, f x ∂S.ν0 := (two_mul _).symm
    _ = ENNReal.ofReal (9 / 4 * S.C γ) * ∫⁻ x, f x ∂S.ν0 := by
        have h94 : ENNReal.ofReal (9 / 4 * S.C γ) =
            ENNReal.ofReal (9 / 8) * 2 * ENNReal.ofReal (S.C γ) := by
          rw [ENNReal.ofReal_mul (by norm_num),
            show (9 / 4 : ℝ) = 9 / 8 * 2 by norm_num, ENNReal.ofReal_mul (by norm_num)]
          simp
        rw [h94]; ring

/-- Integrability of the envelopes against `∑ σ_j`. -/
lemma integrable_e_sum {σ μ lam Sgj : ℕ → Measure X}
    (hinv : ∀ j, S.Inv j (Sgj j) (lam j))
    (hmu_le : ∀ j, μ j ≤ lam j)
    (hmu_supp : ∀ j, μ j (S.shell j ∪ S.shell (j + 1))ᶜ = 0)
    (hcomp : ∀ j γ, ∫⁻ x, ENNReal.ofReal (S.e γ x) ∂σ j ≤
      ENNReal.ofReal (S.C γ) * ∫⁻ x, ENNReal.ofReal (S.e (S.γ' γ) x) ∂μ j) (γ : S.Γ) :
    Integrable (S.e γ) (Measure.sum σ) := by
  refine ⟨(S.e_cont γ).aestronglyMeasurable, ?_⟩
  have h := S.lintegral_sum_le hinv hmu_le hmu_supp hcomp γ
  have hfin : ∫⁻ x, ENNReal.ofReal (S.e (S.γ' γ) x) ∂S.ν0 < ∞ := by
    have := (S.ν0_int (S.γ' γ)).hasFiniteIntegral
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => (S.e_pos _ x).le)] at this
    exact this
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => (S.e_pos _ x).le)]
  exact h.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)

/-- The tail integrals of a reserve vanish in the limit. -/
lemma tendsto_integral_lam {lam Sgj : ℕ → Measure X} (hinv : ∀ j, S.Inv j (Sgj j) (lam j))
    (α : S.I) : Tendsto (fun j => ∫ x, S.K α x ∂lam j) atTop (𝓝 0) := by
  have hKν : Integrable (S.K α) S.ν0 := S.integrable_K S.ν0_int α
  have hbound : ∀ j, ‖∫ x, S.K α x ∂lam j‖ ≤
      (9 / 8 : ℝ) * ∫ x in (S.Ω j)ᶜ, ‖S.K α x‖ ∂S.ν0 := by
    intro j
    have hlam0 := (hinv j).2.1
    have hae : ∀ᵐ x ∂lam j, x ∈ (S.Ω j)ᶜ :=
      (measure_eq_zero_iff_ae_notMem.1 hlam0).mono fun x hx => hx
    have h1 : lam j = (lam j).restrict (S.Ω j)ᶜ := (Measure.restrict_eq_self_of_ae_mem hae).symm
    have h2 : lam j ≤ ENNReal.ofReal (9 / 8) • S.ν0.restrict (S.Ω j)ᶜ := by
      rw [h1, ← Measure.restrict_smul]
      exact Measure.restrict_mono subset_rfl (S.lam_le_nu0 (hinv j))
    have hKint : Integrable (fun x => ‖S.K α x‖) (ENNReal.ofReal (9 / 8) • S.ν0.restrict (S.Ω j)ᶜ) :=
      (hKν.norm.restrict.smul_measure ENNReal.ofReal_ne_top)
    calc ‖∫ x, S.K α x ∂lam j‖ ≤ ∫ x, ‖S.K α x‖ ∂lam j := norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖S.K α x‖ ∂(ENNReal.ofReal (9 / 8) • S.ν0.restrict (S.Ω j)ᶜ) :=
          integral_mono_measure h2 (Filter.Eventually.of_forall fun x => norm_nonneg _) hKint
      _ = (9 / 8 : ℝ) * ∫ x in (S.Ω j)ᶜ, ‖S.K α x‖ ∂S.ν0 := by
          rw [integral_smul_measure, ENNReal.toReal_ofReal (by norm_num), smul_eq_mul]
  have hanti : Antitone fun j => (S.Ω j)ᶜ := fun i j hij => compl_subset_compl.2 (S.Ω_mono hij)
  have hlim := tendsto_setIntegral_of_antitone (μ := S.ν0) (f := fun x => ‖S.K α x‖)
    (fun j => (S.measurableSet_Ω j).compl) hanti ⟨0, hKν.norm.integrableOn⟩
  have hempty : (⋂ j, (S.Ω j)ᶜ) = ∅ := by
    rw [← compl_iUnion, S.Ω_cover, compl_univ]
  rw [hempty] at hlim
  simp only [Measure.restrict_empty, integral_zero_measure] at hlim
  refine squeeze_zero_norm hbound ?_
  simpa using hlim.const_mul (9 / 8 : ℝ)

/-- **Proposition INT-S, limit, aggregated form.**  If the stage-`j` invariants hold along a
sequence with step data `σ_j, μ_j`, then `ν_ℤ = ∑_j σ_j` is locally finite and satisfies the envelope
bound and the crossing equations. -/
theorem limit_of_seq {σ μ lam : ℕ → Measure X}
    (hatom : ∀ j, IsIntAtomicOn (closure (S.Ω (j + 2)) \ S.Ω j) (σ j))
    (hinv : ∀ j, S.Inv j (∑ i ∈ range j, σ i) (lam j))
    (hmu_le : ∀ j, μ j ≤ lam j)
    (hmu_supp : ∀ j, μ j (S.shell j ∪ S.shell (j + 1))ᶜ = 0)
    (hcomp : ∀ j γ, ∫⁻ x, ENNReal.ofReal (S.e γ x) ∂σ j ≤
      ENNReal.ofReal (S.C γ) * ∫⁻ x, ENNReal.ofReal (S.e (S.γ' γ) x) ∂μ j) :
    (∀ T : Set X, IsCompact T → Measure.sum σ T < ∞) ∧
    (∀ γ, ∫⁻ x, ENNReal.ofReal (S.e γ x) ∂Measure.sum σ ≤
      ENNReal.ofReal (9 / 4 * S.C γ) * ∫⁻ x, ENNReal.ofReal (S.e (S.γ' γ) x) ∂S.ν0) ∧
    (∀ γ, Integrable (S.e γ) (Measure.sum σ)) ∧
    (∀ α, ∫ x, S.K α x ∂Measure.sum σ = S.c α) := by
  have hint := S.integrable_e_sum hinv hmu_le hmu_supp hcomp
  refine ⟨fun T hT => S.sum_lt_top_of_compact hatom hT,
    fun γ => S.lintegral_sum_le hinv hmu_le hmu_supp hcomp γ, hint, fun α => ?_⟩
  have hKint : Integrable (S.K α) (Measure.sum σ) := S.integrable_K hint α
  have hsum := (hasSum_integral_measure hKint).tendsto_sum_nat
  have h1 : ∀ j, ∫ x, S.K α x ∂(∑ i ∈ range j, σ i) = ∑ i ∈ range j, ∫ x, S.K α x ∂σ i := by
    intro j
    exact integral_finsetSum_measure fun i _ => hKint.mono_measure (Measure.le_sum _ _)
  have hlim := hsum.add (S.tendsto_integral_lam hinv α)
  have hconst : Tendsto (fun j => ∑ i ∈ range j, ∫ x, S.K α x ∂σ i +
      ∫ x, S.K α x ∂lam j) atTop (𝓝 (S.c α)) := by
    refine tendsto_const_nhds.congr fun j => ?_
    rw [← h1 j]
    exact (S.hinv_K (hinv j) α).symm
  simpa using tendsto_nhds_unique hlim hconst

/-- **Proposition INT-S (`int:shell-inv`), aggregated form.**  Suppose that from every stage `j`
satisfying the invariants (i)-(iv) one aggregated step `AggStep` exists.  Then there are finite
positive integer-weighted atomic measures `σ_j` on `X ∩ (closure Ω_{j+2} \ Ω_j)` whose sum
`ν_ℤ` is locally finite, obeys `∫ e_γ dν_ℤ ≤ (9/4) C_γ ∫ e_{γ'} dν⁰` and `∫ K_α dν_ℤ = c_α`. -/
theorem shell_inv_agg
    (hstep : ∀ (j : ℕ) (Sg lam : Measure X), S.Inv j Sg lam →
      ∃ σ μ Rp Rm : Measure X, S.AggStep j lam σ μ Rp Rm) :
    ∃ σ : ℕ → Measure X,
      (∀ j, IsIntAtomicOn (closure (S.Ω (j + 2)) \ S.Ω j) (σ j)) ∧
      (∀ T : Set X, IsCompact T → Measure.sum σ T < ∞) ∧
      (∀ γ, ∫⁻ x, ENNReal.ofReal (S.e γ x) ∂Measure.sum σ ≤
        ENNReal.ofReal (9 / 4 * S.C γ) * ∫⁻ x, ENNReal.ofReal (S.e (S.γ' γ) x) ∂S.ν0) ∧
      (∀ γ, Integrable (S.e γ) (Measure.sum σ)) ∧
      (∀ α, ∫ x, S.K α x ∂Measure.sum σ = S.c α) := by
  obtain ⟨f, hf0, hf⟩ := exists_seq (fun j (p : Measure X × Measure X) => S.Inv j p.1 p.2)
    (fun j p q => ∃ σ μ Rp Rm : Measure X, S.AggStep j p.2 σ μ Rp Rm ∧ q.1 = p.1 + σ ∧
      q.2 + μ + Rm = p.2 + Rp) ((0 : Measure X), S.ν0) S.inv_zero (by
        intro j p hp
        obtain ⟨σ, μ, Rp, Rm, h⟩ := hstep j p.1 p.2 hp
        obtain ⟨lam', hl, hI⟩ := S.exists_next hp h
        exact ⟨(p.1 + σ, lam'), hI, σ, μ, Rp, Rm, h, rfl, hl⟩)
  choose σ μ Rp Rm hAgg hSg hLam using fun j => (hf j).2
  have hsum : ∀ j, (f j).1 = ∑ i ∈ range j, σ i := by
    intro j
    induction j with
    | zero => simp [hf0]
    | succ j ih => rw [hSg j, ih, sum_range_succ]
  refine ⟨σ, fun j => (hAgg j).atomic, ?_⟩
  exact S.limit_of_seq (lam := fun j => (f j).2) (μ := μ) (fun j => (hAgg j).atomic)
    (fun j => by have := (hf j).1; rwa [hsum j] at this) (fun j => (hAgg j).mu_le)
    (fun j => (hAgg j).mu_supp) (fun j => (hAgg j).comparison)

end ShellSetup

end FormalResearch.ModularBootstrap.Integrality
