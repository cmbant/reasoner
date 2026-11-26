module

public import FormalResearch.ModularBootstrap.Integrality.ShellInvDefs

/-!
# One step of the shell-atomisation recursion (`int:shell-inv`)

`AggStep` records the output of one step of Proposition INT-S in aggregated form (sums over the
cells `r`): the integer atomic measure `σ`, the extracted measure `μ`, and the positive and negative
parts `Rp, Rm` of the exterior remainder `𝓡`.  The lemma `exists_next` shows that the new reserve
`λ' = λ - μ + Rp - Rm` exists and that the invariants pass from stage `j` to stage `j + 1`.
**Proved.**
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.Integrality

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

lemma smul_coef_mono {c c' : ℝ≥0∞} (h : c ≤ c') (μ : Measure X) : c • μ ≤ c' • μ := by
  refine Measure.le_iff'.2 fun A => ?_
  simp only [smul_apply, smul_eq_mul]
  exact mul_le_mul' h le_rfl

lemma meas_le_self_add (a b : Measure X) : a ≤ a + b :=
  Measure.le_iff'.2 fun A => by simp [add_apply]

lemma meas_le_add_self (a b : Measure X) : b ≤ a + b :=
  Measure.le_iff'.2 fun A => by simp [add_apply]

namespace ShellSetup

variable (S : ShellSetup X)

/-- One step of the recursion (aggregated over the cells), from stage `j` to stage `j+1`:
the paper's `μ_k = ∑_r μ_{k,r}`, `σ_k = ∑_r σ_{k,r}`, `𝓡_k = Rp - Rm`, `k = j + 1`. -/
structure AggStep (j : ℕ) (lam σ μ Rp Rm : Measure X) : Prop where
  atomic : IsIntAtomicOn (closure (S.Ω (j + 2)) \ S.Ω j) σ
  mu_le : μ ≤ lam
  mu_fin : IsFiniteMeasure μ
  mu_supp : μ (S.shell j ∪ S.shell (j + 1))ᶜ = 0
  shell_vanish : LEOn (S.shell j) lam μ
  shell_reserve : LEOn (S.shell (j + 1)) (μ + S.cm (5 / 8)) lam
  Rp_null : Rp (S.Ω (j + 2)) = 0
  Rm_null : Rm (S.Ω (j + 2)) = 0
  R_le : Rp + Rm ≤ S.cm ((1 / 2 : ℝ) ^ (j + 4))
  balance : ∀ α, ∫ x, S.K α x ∂σ + ∫ x, S.K α x ∂Rp = ∫ x, S.K α x ∂μ + ∫ x, S.K α x ∂Rm
  comparison : ∀ γ, ∫⁻ x, ENNReal.ofReal (S.e γ x) ∂σ ≤
    ENNReal.ofReal (S.C γ) * ∫⁻ x, ENNReal.ofReal (S.e (S.γ' γ) x) ∂μ

lemma lam_le_nu0 {j : ℕ} {Sg lam : Measure X} (h : S.Inv j Sg lam) :
    lam ≤ ENNReal.ofReal (9 / 8) • S.ν0 := by
  obtain ⟨-, -, h2, -⟩ := h
  refine h2.trans ?_
  have h3 : S.cm (theta j) ≤ ENNReal.ofReal (1 / 8) • S.ν0 :=
    (S.cm_le_nu0 (theta_nonneg j)).trans (smul_coef_mono (ENNReal.ofReal_le_ofReal (theta_le j)) _)
  calc S.ν0 + S.cm (theta j) ≤ S.ν0 + ENNReal.ofReal (1 / 8) • S.ν0 := by
        exact add_le_add le_rfl h3
    _ = ENNReal.ofReal (9 / 8) • S.ν0 := by
        have : ENNReal.ofReal (9 / 8) = 1 + ENNReal.ofReal (1 / 8) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
        rw [this, add_smul, one_smul]

lemma envInt_lam [SigmaFinite S.ν0] {j : ℕ} {Sg lam : Measure X} (h : S.Inv j Sg lam) (γ : S.Γ) :
    Integrable (S.e γ) lam :=
  ((S.ν0_int γ).smul_measure ENNReal.ofReal_ne_top).mono_measure (S.lam_le_nu0 h)

lemma ofReal_half_le {j : ℕ} : ((1 / 2 : ℝ) ^ (j + 4)) ≤ cE j := by
  unfold cE
  have : (1 / 2 : ℝ) ^ (j + 4) ≤ (1 / 2) ^ (j + 3) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h0 : (0 : ℝ) ≤ (1 / 2) ^ (j + 3) := by positivity
  linarith

/-- **Stage step.**  From the invariants at stage `j` and one aggregated step, the new reserve
`λ' = λ - μ + Rp - Rm` exists and the invariants hold at stage `j + 1`. -/
theorem exists_next [SigmaFinite S.ν0] {j : ℕ} {Sg lam σ μ Rp Rm : Measure X}
    (hI : S.Inv j Sg lam) (hs : S.AggStep j lam σ μ Rp Rm) :
    ∃ lam' : Measure X, lam' + μ + Rm = lam + Rp ∧ S.Inv (j + 1) (Sg + σ) lam' := by
  have hI' := hI
  obtain ⟨hSg, hlam0, hlamle, hshell, hE, hK⟩ := hI
  have : IsFiniteMeasure μ := hs.mu_fin
  set ε : ℝ := (1 / 2 : ℝ) ^ (j + 4) with hε
  have hε0 : 0 ≤ ε := pow_half_nonneg _
  have hRp : Rp ≤ S.cm ε := (meas_le_self_add _ _).trans hs.R_le
  have hRm : Rm ≤ S.cm ε := (meas_le_add_self _ _).trans hs.R_le
  have hlamfin : lam ≤ ENNReal.ofReal (9 / 8) • S.ν0 := S.lam_le_nu0 hI'
  have : SigmaFinite lam := by
    rw [ofReal_smul_eq] at hlamfin
    exact Measure.sigmaFinite_of_le _ hlamfin
  have : SigmaFinite Rp := Measure.sigmaFinite_of_le (S.cm ε) hRp
  have : SigmaFinite Rm := Measure.sigmaFinite_of_le (S.cm ε) hRm
  have hΩ1 : MeasurableSet (S.Ω (j + 1)) := S.measurableSet_Ω _
  have hΩ2 : MeasurableSet (S.Ω (j + 2)) := S.measurableSet_Ω _
  have hΩ12 : S.Ω (j + 1) ⊆ S.Ω (j + 2) := S.Ω_mono (by omega)
  have hshell_sub : S.shell j ∪ S.shell (j + 1) ⊆ S.Ω (j + 2) := by
    intro x hx
    rcases hx with hx | hx
    · exact hΩ12 hx.1
    · exact hx.1
  have hshell1 : S.shell (j + 1) ⊆ S.Ω (j + 2) := fun x hx => hx.1
  have hmuT : μ (S.Ω (j + 2))ᶜ = 0 :=
    measure_mono_null (show (S.Ω (j + 2))ᶜ ⊆ (S.shell j ∪ S.shell (j + 1))ᶜ from
      fun x hx hx' => hx (hshell_sub hx')) hs.mu_supp
  -- `μ + Rm ≤ lam + Rp`
  have hle : μ + Rm ≤ lam + Rp := by
    refine measure_le_of_split hΩ2 ?_ ?_
    · intro A hA hAT
      have h0 : Rm A = 0 := measure_mono_null hAT hs.Rm_null
      simp only [add_apply, h0, add_zero]
      exact (hs.mu_le A).trans le_self_add
    · intro A hA hAT
      have h0 : μ A = 0 := measure_mono_null hAT hmuT
      have hA' : A ⊆ (S.Ω (j + 1))ᶜ := fun x hx hx' => hAT hx (hΩ12 hx')
      have h1 := hE A hA hA'
      have h2 : Rm A ≤ S.cm (cE j) A := (hRm A).trans (S.cm_mono ofReal_half_le A)
      simp only [add_apply, h0, zero_add]
      exact (h2.trans h1).trans le_self_add
  obtain ⟨lam', hlam'⟩ := exists_add_of_measure_le hle
  have F1 : lam' + μ + Rm = lam + Rp := by rw [hlam']; ac_rfl
  have F1A : ∀ A, lam' A + μ A + Rm A = lam A + Rp A := by
    intro A
    have := congrArg (fun m : Measure X => m A) F1
    simpa [add_apply] using this
  refine ⟨lam', F1, ?_⟩
  have hlam'le : lam' ≤ lam + Rp :=
    calc lam' ≤ lam' + μ := meas_le_self_add _ _
      _ ≤ lam' + μ + Rm := meas_le_self_add _ _
      _ = lam + Rp := F1
  have hμΩ : μ (S.Ω (j + 1)) ≠ ∞ := measure_ne_top _ _
  -- `lam'` vanishes on `Ω_{j+1}`
  have hlam'0 : lam' (S.Ω (j + 1)) = 0 := by
    have hRp0 : Rp (S.Ω (j + 1)) = 0 := measure_mono_null hΩ12 hs.Rp_null
    have hRm0 : Rm (S.Ω (j + 1)) = 0 := measure_mono_null hΩ12 hs.Rm_null
    have hsub : S.Ω (j + 1) ⊆ S.Ω j ∪ S.shell j := by
      intro x hx
      by_cases h : x ∈ S.Ω j
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
    have hl1 : lam (S.Ω (j + 1)) ≤ μ (S.Ω (j + 1)) := by
      calc lam (S.Ω (j + 1)) ≤ lam (S.Ω j ∪ S.shell j) := measure_mono hsub
        _ ≤ lam (S.Ω j) + lam (S.shell j) := measure_union_le _ _
        _ = lam (S.shell j) := by rw [hlam0, zero_add]
        _ ≤ μ (S.shell j) := hs.shell_vanish _ (S.measurableSet_shell j) subset_rfl
        _ ≤ μ (S.Ω (j + 1)) := measure_mono (show S.shell j ⊆ S.Ω (j + 1) from fun x hx => hx.1)
    have h2 := F1A (S.Ω (j + 1))
    rw [hRp0, hRm0, add_zero, add_zero] at h2
    have h3 : lam' (S.Ω (j + 1)) + μ (S.Ω (j + 1)) ≤ 0 + μ (S.Ω (j + 1)) := by
      rw [h2, zero_add]; exact hl1
    exact nonpos_iff_eq_zero.1 ((ENNReal.add_le_add_iff_right hμΩ).1 h3)
  have hint_lam : ∀ γ, Integrable (S.e γ) lam := S.envInt_lam hI'
  have hint_Rp : ∀ γ, Integrable (S.e γ) Rp := fun γ => (S.cm_integrable (S.ρ_int γ)).mono_measure hRp
  have hint_Rm : ∀ γ, Integrable (S.e γ) Rm := fun γ => (S.cm_integrable (S.ρ_int γ)).mono_measure hRm
  have hint_mu : ∀ γ, Integrable (S.e γ) μ := fun γ => (hint_lam γ).mono_measure hs.mu_le
  have hint_lam' : ∀ γ, Integrable (S.e γ) lam' := fun γ =>
    ((hint_lam γ).add_measure (hint_Rp γ)).mono_measure hlam'le
  refine ⟨?_, hlam'0, ?_, ?_, ?_, ?_⟩
  · -- (i)
    exact (hSg.mono (closure_mono hΩ12)).add
      (hs.atomic.mono (show closure (S.Ω (j + 2)) \ S.Ω j ⊆ closure (S.Ω (j + 1 + 1)) from fun x hx => hx.1))
  · -- (ii)
    refine hlam'le.trans ?_
    calc lam + Rp ≤ (S.ν0 + S.cm (theta j)) + S.cm ε := add_le_add hlamle hRp
      _ = S.ν0 + S.cm (theta (j + 1)) := by
        rw [add_assoc, S.cm_add (theta_nonneg j) hε0, theta_succ]
  · -- (iii) shell
    intro A hA hAs
    have hRp0 : Rp A = 0 := measure_mono_null (hAs.trans hshell1) hs.Rp_null
    have hRm0 : Rm A = 0 := measure_mono_null (hAs.trans hshell1) hs.Rm_null
    have h1 := F1A A
    rw [hRp0, hRm0, add_zero, add_zero] at h1
    have h2 := hs.shell_reserve A hA hAs
    simp only [add_apply] at h2
    have hμA : μ A ≠ ∞ := measure_ne_top _ _
    refine (ENNReal.add_le_add_iff_right hμA).1 ?_
    rw [h1, add_comm]
    exact h2
  · -- (iii) tail
    have hT : MeasurableSet (S.Ω (j + 2))ᶜ := hΩ2.compl
    refine (leOn_iff hT).2 ?_
    refine measure_le_of_add_le_add_right (c := Rm.restrict (S.Ω (j + 2))ᶜ) ?_
    have hEj : (S.cm (cE j)).restrict (S.Ω (j + 2))ᶜ ≤ lam.restrict (S.Ω (j + 2))ᶜ :=
      (leOn_iff hT).1 fun A hA hAT => hE A hA (hAT.trans (compl_subset_compl.2 hΩ12))
    have hμ0 : μ.restrict (S.Ω (j + 2))ᶜ = 0 := Measure.restrict_eq_zero.2 hmuT
    have hF := congrArg (fun m : Measure X => m.restrict (S.Ω (j + 2))ᶜ) F1
    simp only [Measure.restrict_add, hμ0, add_zero] at hF
    have hcm : S.cm (cE (j + 1)) + S.cm ε = S.cm (cE j) := by
      rw [S.cm_add (by unfold cE; positivity) hε0, cE_succ]; congr 1; ring
    calc (S.cm (cE (j + 1))).restrict (S.Ω (j + 2))ᶜ + Rm.restrict (S.Ω (j + 2))ᶜ
        ≤ (S.cm (cE (j + 1))).restrict (S.Ω (j + 2))ᶜ + (S.cm ε).restrict (S.Ω (j + 2))ᶜ :=
          add_le_add le_rfl (Measure.restrict_mono subset_rfl hRm)
      _ = (S.cm (cE j)).restrict (S.Ω (j + 2))ᶜ := by rw [← Measure.restrict_add, hcm]
      _ ≤ lam.restrict (S.Ω (j + 2))ᶜ := hEj
      _ ≤ lam.restrict (S.Ω (j + 2))ᶜ + Rp.restrict (S.Ω (j + 2))ᶜ := meas_le_self_add _ _
      _ = lam'.restrict (S.Ω (j + 2))ᶜ + Rm.restrict (S.Ω (j + 2))ᶜ := hF.symm
  · -- (iv)
    intro α
    have hKi : ∀ ν : Measure X, (∀ γ, Integrable (S.e γ) ν) → Integrable (S.K α) ν :=
      fun ν hν => S.integrable_K hν α
    have iSg := hSg.integrable (S.K_cont α)
    have iσ := hs.atomic.integrable (S.K_cont α)
    have i1 := hKi _ hint_lam'
    have i2 := hKi _ hint_mu
    have i3 := hKi _ hint_Rm
    have i4 := hKi _ hint_lam
    have i5 := hKi _ hint_Rp
    have hF1 : ∫ x, S.K α x ∂(lam' + μ + Rm) = ∫ x, S.K α x ∂(lam + Rp) := by rw [F1]
    rw [integral_add_measure (i1.add_measure i2) i3, integral_add_measure i1 i2,
      integral_add_measure i4 i5] at hF1
    rw [integral_add_measure iSg iσ]
    have hb := hs.balance α
    have hk := hK α
    linarith

end ShellSetup

end FormalResearch.ModularBootstrap.Integrality
