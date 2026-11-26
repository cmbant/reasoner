module

public import FormalResearch.ModularBootstrap.Integrality.ShellInv

/-!
# Shell atomisation with cells (`int:shell-inv`, paper form)

`CellStep` is one step of Proposition INT-S as stated in the paper: a finite family of closed cells
`U_r ⊂ X ∩ (closure Ω_{k+1} \ Ω_{k-1})`, extracted measures `μ_r`, integer atomic measures `σ_r` with
`σ_r(U_r) = μ_r(U_r)`, and repairs `D_r = (σ_r + Rp_r) - (μ_r + Rm_r)` with exterior remainder
`Rp_r - Rm_r` of total variation `≤ 2^{-k-3} δ ρ_res` (here `k = j + 1`), balancing every `K_α` and
with the uniform cell comparison `e_γ(x) ≤ C_γ e_{γ'}(y)` on each cell.  `shell_inv` is the
Proposition: if every stage has such a step then `ν_ℤ = ∑_{j,r} σ_{j,r}` has the stated
properties.  **Proved.**
-/

@[expose] public section

open MeasureTheory Set Finset Filter Topology
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.Integrality

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

namespace ShellSetup

variable {S : ShellSetup X}

/-- One step of Proposition INT-S from stage `j` (paper stage `k = j + 1`), with cells. -/
structure CellStep (j : ℕ) (lam : Measure X) {ι : Type} [Fintype ι] (U : ι → Set X)
    (μ σ Rp Rm : ι → Measure X) : Prop where
  cell_closed : ∀ r, IsClosed (U r)
  cell_sub : ∀ r, U r ⊆ closure (S.Ω (j + 2)) \ S.Ω j
  sigma_atomic : ∀ r, IsIntAtomicOn (U r) (σ r)
  mu_supp : ∀ r, μ r (U r ∩ (S.shell j ∪ S.shell (j + 1)))ᶜ = 0
  mass : ∀ r, σ r (U r) = μ r (U r)
  mu_le : ∑ r, μ r ≤ lam
  shell_vanish : LEOn (S.shell j) lam (∑ r, μ r)
  shell_reserve : LEOn (S.shell (j + 1)) (∑ r, μ r + S.cm (5 / 8)) lam
  Rp_null : ∀ r, Rp r (S.Ω (j + 2)) = 0
  Rm_null : ∀ r, Rm r (S.Ω (j + 2)) = 0
  R_le : ∑ r, (Rp r + Rm r) ≤ S.cm ((1 / 2 : ℝ) ^ (j + 4))
  balance : ∀ r α, ∫ x, S.K α x ∂σ r + ∫ x, S.K α x ∂Rp r =
    ∫ x, S.K α x ∂μ r + ∫ x, S.K α x ∂Rm r
  comparison : ∀ r γ, ∀ x ∈ U r, ∀ y ∈ U r, S.e γ x ≤ S.C γ * S.e (S.γ' γ) y

lemma IsIntAtomicOn.sum' {T : Set X} {ι : Type} [Fintype ι] {σ : ι → Measure X}
    (h : ∀ r, IsIntAtomicOn T (σ r)) : IsIntAtomicOn T (∑ r, σ r) := by
  refine Finset.sum_induction σ (IsIntAtomicOn T) (fun a b ha hb => ha.add hb) ?_ fun r _ => h r
  exact ⟨Empty, inferInstance, Empty.elim, Empty.elim, by simp, by simp⟩

lemma lintegral_le_of_forall {σ : Measure X} {T : Set X} (hT : MeasurableSet T) (hσ : σ Tᶜ = 0)
    (hfin : σ T ≠ ∞) {f : X → ℝ≥0∞} (B : ℝ≥0∞) (hf : ∀ x ∈ T, f x * σ T ≤ B) :
    ∫⁻ x, f x ∂σ ≤ B := by
  by_cases h0 : σ T = 0
  · have : σ = 0 := by
      refine Measure.measure_univ_eq_zero.1 ?_
      rw [← union_compl_self T, measure_union_null h0 hσ]
    simp [this]
  · have hae : ∀ᵐ x ∂σ, x ∈ T := by
      have := measure_eq_zero_iff_ae_notMem.1 hσ
      exact this.mono fun x hx => Set.notMem_compl_iff.1 hx
    calc ∫⁻ x, f x ∂σ = ∫⁻ x in T, f x ∂σ := by rw [Measure.restrict_eq_self_of_ae_mem hae]
      _ ≤ ∫⁻ x in T, B / σ T ∂σ :=
          setLIntegral_mono' hT fun x hx => (ENNReal.le_div_iff_mul_le (Or.inl h0)
            (Or.inl hfin)).2 (hf x hx)
      _ = B / σ T * σ T := by rw [setLIntegral_const]
      _ = B := ENNReal.div_mul_cancel h0 hfin

lemma le_sum_measure {ι : Type} [Fintype ι] (μ : ι → Measure X) (r : ι) : μ r ≤ ∑ r', μ r' := by
  classical
  rw [← Finset.add_sum_erase _ _ (mem_univ r)]
  exact meas_le_self_add _ _

lemma CellStep.cell_comparison {j : ℕ} {lam : Measure X} {ι : Type} [Fintype ι] {U : ι → Set X}
    {μ σ Rp Rm : ι → Measure X} (h : S.CellStep j lam U μ σ Rp Rm) (r : ι) (γ : S.Γ) :
    ∫⁻ x, ENNReal.ofReal (S.e γ x) ∂σ r ≤
      ENNReal.ofReal (S.C γ) * ∫⁻ y, ENNReal.ofReal (S.e (S.γ' γ) y) ∂μ r := by
  have hUm : MeasurableSet (U r) := (h.cell_closed r).measurableSet
  have hσfin := (h.sigma_atomic r).isFiniteMeasure
  have hσU : σ r (U r)ᶜ = 0 :=
    (h.sigma_atomic r).measure_eq_zero hUm.compl disjoint_compl_left
  refine lintegral_le_of_forall hUm hσU (measure_ne_top _ _) _ ?_
  intro x hx
  rw [h.mass r]
  have hμU : μ r (U r)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 inter_subset_left) (h.mu_supp r)
  have hae : ∀ᵐ y ∂μ r, y ∈ U r :=
    (measure_eq_zero_iff_ae_notMem.1 hμU).mono fun y hy => Set.notMem_compl_iff.1 hy
  have hμuniv : μ r univ = μ r (U r) := by
    rw [← measure_add_measure_compl hUm, hμU, add_zero]
  have hmeas : Measurable fun y => ENNReal.ofReal (S.e (S.γ' γ) y) :=
    ENNReal.measurable_ofReal.comp (S.e_cont _).measurable
  calc ENNReal.ofReal (S.e γ x) * μ r (U r) = ∫⁻ y, ENNReal.ofReal (S.e γ x) ∂μ r := by
        rw [lintegral_const, hμuniv]
    _ ≤ ∫⁻ y, ENNReal.ofReal (S.C γ) * ENNReal.ofReal (S.e (S.γ' γ) y) ∂μ r :=
        lintegral_mono_ae (hae.mono fun y hy => by
          rw [← ENNReal.ofReal_mul (S.C_nonneg γ)]
          exact ENNReal.ofReal_le_ofReal (h.comparison r γ x hx y hy))
    _ = ENNReal.ofReal (S.C γ) * ∫⁻ y, ENNReal.ofReal (S.e (S.γ' γ) y) ∂μ r :=
        lintegral_const_mul _ hmeas

/-- A cell step gives an aggregated step. -/
lemma CellStep.toAgg [SigmaFinite S.ν0] {j : ℕ} {Sg lam : Measure X} (hI : S.Inv j Sg lam)
    {ι : Type} [Fintype ι] {U : ι → Set X} {μ σ Rp Rm : ι → Measure X}
    (h : S.CellStep j lam U μ σ Rp Rm) :
    S.AggStep j lam (∑ r, σ r) (∑ r, μ r) (∑ r, Rp r) (∑ r, Rm r) := by
  have hμfin : ∀ r, IsFiniteMeasure (μ r) := by
    intro r
    have hUm : MeasurableSet (U r) := (h.cell_closed r).measurableSet
    have hσfin := (h.sigma_atomic r).isFiniteMeasure
    have hμU : μ r (U r)ᶜ = 0 :=
      measure_mono_null (compl_subset_compl.2 inter_subset_left) (h.mu_supp r)
    refine ⟨?_⟩
    rw [← measure_add_measure_compl hUm, hμU, add_zero, ← h.mass r]
    exact measure_lt_top _ _
  have : IsFiniteMeasure (∑ r, μ r) := inferInstance
  have hRle : ∀ r, Rp r + Rm r ≤ S.cm ((1 / 2 : ℝ) ^ (j + 4)) := fun r =>
    (le_sum_measure (fun r => Rp r + Rm r) r).trans h.R_le
  have hint_lam := S.envInt_lam hI
  have hKi : ∀ (α : S.I) (ν : Measure X), (∀ γ, Integrable (S.e γ) ν) → Integrable (S.K α) ν :=
    fun α ν hν => S.integrable_K hν α
  refine ⟨IsIntAtomicOn.sum' fun r => (h.sigma_atomic r).mono (h.cell_sub r), h.mu_le,
    inferInstance, ?_, h.shell_vanish, h.shell_reserve, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [FunLike.coe_sum, Finset.sum_apply]
    exact Finset.sum_eq_zero fun r _ =>
      measure_mono_null (compl_subset_compl.2 inter_subset_right) (h.mu_supp r)
  · simp [h.Rp_null]
  · simp [h.Rm_null]
  · rw [← Finset.sum_add_distrib]; exact h.R_le
  · intro α
    have iσ : ∀ r, Integrable (S.K α) (σ r) := fun r => (h.sigma_atomic r).integrable (S.K_cont α)
    have iμ : ∀ r, Integrable (S.K α) (μ r) := fun r => hKi α _ fun γ =>
      (hint_lam γ).mono_measure ((le_sum_measure μ r).trans h.mu_le)
    have iRp : ∀ r, Integrable (S.K α) (Rp r) := fun r => hKi α _ fun γ =>
      (S.cm_integrable (S.ρ_int γ)).mono_measure ((meas_le_self_add _ _).trans (hRle r))
    have iRm : ∀ r, Integrable (S.K α) (Rm r) := fun r => hKi α _ fun γ =>
      (S.cm_integrable (S.ρ_int γ)).mono_measure ((meas_le_add_self _ _).trans (hRle r))
    rw [integral_finsetSum_measure fun r _ => iσ r, integral_finsetSum_measure fun r _ => iRp r,
      integral_finsetSum_measure fun r _ => iμ r, integral_finsetSum_measure fun r _ => iRm r,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => h.balance r α
  · intro γ
    rw [lintegral_finsetSum_measure, lintegral_finsetSum_measure, Finset.mul_sum]
    exact Finset.sum_le_sum fun r _ => h.cell_comparison r γ

variable (S) in
/-- **Proposition INT-S (`int:shell-inv`).**  If from every stage satisfying the invariants (i)-(iv)
one cell step exists, then there are finite positive integer-weighted atomic measures `σ_j`
(`= ∑_r σ_{j+1,r}` in the paper's indexing) on `X ∩ (closure Ω_{j+2} \ Ω_j)`, whose sum `ν_ℤ` is
locally finite, obeys the envelope bound `∫ e_γ dν_ℤ ≤ (9/4) C_γ ∫ e_{γ'} dν⁰` and satisfies the
crossing equations `∫ K_α dν_ℤ = c_α`. -/
theorem shell_inv [SigmaFinite S.ν0]
    (hcells : ∀ (j : ℕ) (Sg lam : Measure X), S.Inv j Sg lam →
      ∃ (ι : Type) (_ : Fintype ι) (U : ι → Set X) (μ σ Rp Rm : ι → Measure X),
        S.CellStep j lam U μ σ Rp Rm) :
    ∃ σ : ℕ → Measure X,
      (∀ j, IsIntAtomicOn (closure (S.Ω (j + 2)) \ S.Ω j) (σ j)) ∧
      (∀ T : Set X, IsCompact T → Measure.sum σ T < ∞) ∧
      (∀ γ, ∫⁻ x, ENNReal.ofReal (S.e γ x) ∂Measure.sum σ ≤
        ENNReal.ofReal (9 / 4 * S.C γ) * ∫⁻ x, ENNReal.ofReal (S.e (S.γ' γ) x) ∂S.ν0) ∧
      (∀ γ, Integrable (S.e γ) (Measure.sum σ)) ∧
      (∀ α, ∫ x, S.K α x ∂Measure.sum σ = S.c α) := by
  refine S.shell_inv_agg fun j Sg lam hI => ?_
  obtain ⟨ι, hι, U, μ, σ, Rp, Rm, h⟩ := hcells j Sg lam hI
  exact ⟨∑ r, σ r, ∑ r, μ r, ∑ r, Rp r, ∑ r, Rm r, h.toAgg hI⟩

end ShellSetup

/-- info: 'FormalResearch.ModularBootstrap.Integrality.ShellSetup.shell_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ShellSetup.shell_inv

end FormalResearch.ModularBootstrap.Integrality
