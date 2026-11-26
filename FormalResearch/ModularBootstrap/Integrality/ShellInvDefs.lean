module

public import FormalResearch.ModularBootstrap.Integrality.MeasureAlg
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Topology.Compactness.Compact

/-!
# Shell-atomisation invariant: set-up and stage invariants (`int:shell-inv`)

`CFT/modular_bootstrap/paper/integrality.tex`, Proposition INT-S.  This file fixes the data
(open exhaustion `Ω`, test functions `K_α` with targets `c_α`, envelopes `e_γ`, reserve `ρ_res`,
the measure `ν⁰` and the constant `δ`) and the stage-`j` invariants (i)-(iv).  Stage `j` of this
file is stage `k - 1 = j` of the paper, so `shell j` is the paper's `S_{j+1}` and the tail
`(Ω (j+1))ᶜ` the paper's `E_{j+1}`.

Measures are compared by values on measurable sets; `cm a = ofReal (a δ) • ρ_res` is the reserve
`a δ ρ_res`.  **Proved** (definitions and first consequences).
-/

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.Integrality

lemma smul_measure_mono {X : Type*} [MeasurableSpace X] (c : ℝ≥0∞) {a b : Measure X} (h : a ≤ b) :
    c • a ≤ c • b := by
  refine Measure.le_iff'.2 fun A => ?_
  simp only [smul_apply, smul_eq_mul]
  exact mul_le_mul' le_rfl (h A)

/-- The data of Proposition INT-S (first paragraph) for a topological space `X`
(the closed set `X ⊂ ℝ^d` of the paper, as a type). -/
structure ShellSetup (X : Type*) [TopologicalSpace X] [MeasurableSpace X] where
  /-- the increasing exhaustion by open sets `Ω₀ ⊂ Ω₁ ⊂ ⋯` -/
  Ω : ℕ → Set X
  I : Type
  Γ : Type
  /-- test functions `K_α` and their targets `c_α` -/
  K : I → X → ℝ
  c : I → ℝ
  /-- envelopes `e_γ` -/
  e : Γ → X → ℝ
  /-- reserve measure and the starting measure `ν⁰` -/
  ρ : Measure X
  ν0 : Measure X
  δ : ℝ
  /-- the comparison data of the uniform cell comparison: `e_γ ≤ C_γ e_{γ'}` on a cell -/
  γ' : Γ → Γ
  C : Γ → ℝ
  Ω_open : ∀ k, IsOpen (Ω k)
  Ω_mono : Monotone Ω
  Ω_zero : Ω 0 = ∅
  Ω_cover : ⋃ k, Ω k = univ
  K_cont : ∀ α, Continuous (K α)
  e_cont : ∀ γ, Continuous (e γ)
  e_pos : ∀ γ x, 0 < e γ x
  K_dom : ∀ α, ∃ (s : Finset Γ) (a : Γ → ℝ), (∀ γ, 0 ≤ a γ) ∧
    ∀ x, |K α x| ≤ ∑ γ ∈ s, a γ * e γ x
  δ_pos : 0 < δ
  δ_le : δ ≤ 1
  ρ_int : ∀ γ, Integrable (e γ) ρ
  ν0_int : ∀ γ, Integrable (e γ) ν0
  ν0_K : ∀ α, ∫ x, K α x ∂ν0 = c α
  reserve_le : ENNReal.ofReal δ • ρ ≤ ν0
  C_nonneg : ∀ γ, 0 ≤ C γ

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

/-- `θ_k = ∑_{i=1}^k 2^{-i-3} = 1/8 - 2^{-k-3}`. -/
noncomputable def theta (j : ℕ) : ℝ := 1 / 8 - (1 / 2 : ℝ) ^ (j + 3)

/-- The tail coefficient `7/8 + 2^{-j-3}` of invariant (iii). -/
noncomputable def cE (j : ℕ) : ℝ := 7 / 8 + (1 / 2 : ℝ) ^ (j + 3)

namespace ShellSetup

variable (S : ShellSetup X)

/-- The reserve `a δ ρ_res`. -/
noncomputable def cm (a : ℝ) : Measure X := ENNReal.ofReal (a * S.δ) • S.ρ

/-- The shell `S_{j+1} = Ω_{j+1} \ Ω_j`. -/
def shell (j : ℕ) : Set X := S.Ω (j + 1) \ S.Ω j

/-- Comparison of two measures on the measurable subsets of `T`. -/
def LEOn (T : Set X) (a b : Measure X) : Prop :=
  ∀ A, MeasurableSet A → A ⊆ T → a A ≤ b A

/-- Finite positive integer-weighted atomic measures supported in `T`. -/
def IsIntAtomicOn (T : Set X) (σ : Measure X) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (x : ι → X) (d : ι → ℕ), (∀ i, 1 ≤ d i ∧ x i ∈ T) ∧
    σ = ∑ i, (d i : ℝ≥0∞) • Measure.dirac (x i)

/-- The stage-`j` invariants (i)-(iv) of Proposition INT-S, for `ν^{(j)} = Σ + lam`. -/
def Inv (j : ℕ) (Sg lam : Measure X) : Prop :=
  IsIntAtomicOn (closure (S.Ω (j + 1))) Sg ∧
  lam (S.Ω j) = 0 ∧
  lam ≤ S.ν0 + S.cm (theta j) ∧
  LEOn (S.shell j) (S.cm (5 / 8)) lam ∧
  LEOn (S.Ω (j + 1))ᶜ (S.cm (cE j)) lam ∧
  ∀ α, ∫ x, S.K α x ∂Sg + ∫ x, S.K α x ∂lam = S.c α

lemma IsIntAtomicOn.mono {T T' : Set X} (h : T ⊆ T') {σ : Measure X} (hσ : IsIntAtomicOn T σ) :
    IsIntAtomicOn T' σ := by
  obtain ⟨ι, hι, x, d, hd, rfl⟩ := hσ
  exact ⟨ι, hι, x, d, fun i => ⟨(hd i).1, h (hd i).2⟩, rfl⟩

lemma IsIntAtomicOn.add {T : Set X} {σ σ' : Measure X} (hσ : IsIntAtomicOn T σ)
    (hσ' : IsIntAtomicOn T σ') : IsIntAtomicOn T (σ + σ') := by
  obtain ⟨ι, hι, x, d, hd, rfl⟩ := hσ
  obtain ⟨ι', hι', x', d', hd', rfl⟩ := hσ'
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim x x', Sum.elim d d', ?_, ?_⟩
  · rintro (i | i)
    · exact hd i
    · exact hd' i
  · simp [Fintype.sum_sum_type]

lemma IsIntAtomicOn.integrable {T : Set X} {σ : Measure X} (hσ : IsIntAtomicOn T σ) {f : X → ℝ}
    (hf : Continuous f) : Integrable f σ := by
  obtain ⟨ι, hι, x, d, hd, rfl⟩ := hσ
  rw [integrable_finsetSum_measure]
  intro i _
  exact (integrable_dirac' hf.stronglyMeasurable (by simp)).smul_measure (by simp)

lemma IsIntAtomicOn.isFiniteMeasure {T : Set X} {σ : Measure X} (hσ : IsIntAtomicOn T σ) :
    IsFiniteMeasure σ := by
  obtain ⟨ι, hι, x, d, hd, rfl⟩ := hσ
  have : ∀ i, IsFiniteMeasure ((d i : ℝ≥0∞) • Measure.dirac (x i)) :=
    fun i => ⟨by simp⟩
  infer_instance

lemma measurableSet_Ω (k : ℕ) : MeasurableSet (S.Ω k) := (S.Ω_open k).measurableSet

lemma measurableSet_shell (j : ℕ) : MeasurableSet (S.shell j) :=
  (S.measurableSet_Ω _).diff (S.measurableSet_Ω _)

lemma theta_succ (j : ℕ) : theta (j + 1) = theta j + (1 / 2 : ℝ) ^ (j + 4) := by
  unfold _root_.FormalResearch.ModularBootstrap.Integrality.theta; ring

lemma cE_succ (j : ℕ) : cE (j + 1) = cE j - (1 / 2 : ℝ) ^ (j + 4) := by
  unfold cE; ring

lemma theta_nonneg (j : ℕ) : 0 ≤ theta j := by
  unfold _root_.FormalResearch.ModularBootstrap.Integrality.theta
  have : (1 / 2 : ℝ) ^ (j + 3) ≤ (1 / 2) ^ 3 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  norm_num at this ⊢; linarith

lemma theta_le (j : ℕ) : theta j ≤ 1 / 8 := by
  unfold _root_.FormalResearch.ModularBootstrap.Integrality.theta
  have : (0 : ℝ) < (1 / 2) ^ (j + 3) := by positivity
  linarith

lemma pow_half_nonneg (n : ℕ) : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity

lemma cm_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : S.cm a + S.cm b = S.cm (a + b) := by
  unfold cm
  rw [← add_smul, ← ENNReal.ofReal_add (mul_nonneg ha S.δ_pos.le) (mul_nonneg hb S.δ_pos.le),
    add_mul]

lemma cm_mono {a b : ℝ} (h : a ≤ b) : S.cm a ≤ S.cm b := by
  refine Measure.le_iff'.2 fun A => ?_
  simp only [cm, smul_apply, smul_eq_mul]
  gcongr
  exact S.δ_pos.le

lemma cm_apply (a : ℝ) (A : Set X) : S.cm a A = ENNReal.ofReal (a * S.δ) * S.ρ A := by
  simp [cm]

lemma cm_le_nu0 {a : ℝ} (ha : 0 ≤ a) : S.cm a ≤ ENNReal.ofReal a • S.ν0 := by
  have : S.cm a = ENNReal.ofReal a • (ENNReal.ofReal S.δ • S.ρ) := by
    unfold cm
    rw [smul_smul, ENNReal.ofReal_mul ha]
  rw [this]
  exact smul_measure_mono _ S.reserve_le

lemma cm_integrable {a : ℝ} {f : X → ℝ} (hf : Integrable f S.ρ) : Integrable f (S.cm a) :=
  hf.smul_measure ENNReal.ofReal_ne_top

lemma ofReal_smul_eq (a : ℝ) (μ : Measure X) :
    ENNReal.ofReal a • μ = (a.toNNReal : NNReal) • μ := by
  ext A _
  simp [ENNReal.ofReal]

instance sigmaFinite_cm (a : ℝ) [SigmaFinite S.ν0] : SigmaFinite (S.cm a) := by
  by_cases ha : 0 ≤ a
  · have h := S.cm_le_nu0 ha
    rw [ofReal_smul_eq] at h
    exact Measure.sigmaFinite_of_le _ h
  · have : S.cm a = 0 := by
      unfold cm
      rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (not_le.1 ha).le S.δ_pos.le),
        zero_smul]
    rw [this]; infer_instance

lemma rho_le_nu0 : S.ρ ≤ ENNReal.ofReal S.δ⁻¹ • S.ν0 := by
  have h := smul_measure_mono (ENNReal.ofReal S.δ⁻¹) S.reserve_le
  rwa [smul_smul, ← ENNReal.ofReal_mul (by have := S.δ_pos; positivity),
    inv_mul_cancel₀ S.δ_pos.ne', ENNReal.ofReal_one, one_smul] at h

instance sigmaFinite_rho [SigmaFinite S.ν0] : SigmaFinite S.ρ := by
  have h := S.rho_le_nu0
  rw [ofReal_smul_eq] at h
  exact Measure.sigmaFinite_of_le _ h

lemma integrable_K {ν : Measure X} (hν : ∀ γ, Integrable (S.e γ) ν) (α : S.I) :
    Integrable (S.K α) ν := by
  obtain ⟨s, a, ha, hbd⟩ := S.K_dom α
  have hint : Integrable (fun x => ∑ γ ∈ s, a γ * S.e γ x) ν :=
    integrable_finsetSum _ fun γ _ => (hν γ).const_mul (a γ)
  exact hint.mono' (S.K_cont α).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa using hbd x)

lemma integrable_e_of_le {ν ν' : Measure X} (h : ν ≤ ν') (hν' : ∀ γ, Integrable (S.e γ) ν')
    (γ : S.Γ) : Integrable (S.e γ) ν := (hν' γ).mono_measure h

lemma leOn_iff {T : Set X} (hT : MeasurableSet T) {a b : Measure X} :
    LEOn T a b ↔ a.restrict T ≤ b.restrict T := by
  constructor
  · intro h
    refine Measure.le_iff.2 fun A hA => ?_
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
    exact h _ (hA.inter hT) inter_subset_right
  · intro h A hA hAT
    have := Measure.le_iff.1 h A hA
    rwa [Measure.restrict_apply hA, Measure.restrict_apply hA, inter_eq_left.2 hAT] at this

end ShellSetup

end FormalResearch.ModularBootstrap.Integrality
