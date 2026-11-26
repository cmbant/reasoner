module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Cancellation and subtraction for `σ`-finite measures

Small measure-algebra facts for `int:shell-inv`: if `a + c ≤ b + c` with `c` `σ`-finite then
`a ≤ b`; if `c ≤ b` with `b` `σ`-finite then `b = c + κ` for a measure `κ`.  **Proved.**
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.Integrality

variable {X : Type*} [MeasurableSpace X]

/-- Cancellation of a `σ`-finite summand in an order relation between measures. -/
lemma measure_le_of_add_le_add_right {a b c : Measure X} [SigmaFinite c]
    (h : a + c ≤ b + c) : a ≤ b := by
  refine Measure.le_iff'.2 fun A => ?_
  have hA : ∀ n, a (A ∩ spanningSets c n) ≤ b (A ∩ spanningSets c n) := by
    intro n
    have h1 := h (A ∩ spanningSets c n)
    simp only [add_apply] at h1
    have hfin : c (A ∩ spanningSets c n) ≠ ∞ :=
      ne_top_of_le_ne_top (measure_spanningSets_lt_top c n).ne (measure_mono inter_subset_right)
    exact (ENNReal.add_le_add_iff_right hfin).1 h1
  have hU : A = ⋃ n, A ∩ spanningSets c n := by
    rw [← inter_iUnion, iUnion_spanningSets, inter_univ]
  have hmono : Monotone fun n => A ∩ spanningSets c n :=
    fun m n hmn => inter_subset_inter_right _ (monotone_spanningSets c hmn)
  calc a A = a (⋃ n, A ∩ spanningSets c n) := by rw [← hU]
    _ = ⨆ n, a (A ∩ spanningSets c n) := hmono.measure_iUnion
    _ ≤ ⨆ n, b (A ∩ spanningSets c n) := iSup_mono hA
    _ = b (⋃ n, A ∩ spanningSets c n) := hmono.measure_iUnion.symm
    _ = b A := by rw [← hU]

lemma measure_eq_of_add_eq_add_right {a b c : Measure X} [SigmaFinite c]
    (h : a + c = b + c) : a = b :=
  le_antisymm (measure_le_of_add_le_add_right h.le) (measure_le_of_add_le_add_right h.ge)

/-- **Subtraction** for `σ`-finite measures: `c ≤ b` gives `b = c + κ`. -/
lemma exists_add_of_measure_le {b c : Measure X} [SigmaFinite b] (h : c ≤ b) :
    ∃ κ : Measure X, b = c + κ := by
  have : SigmaFinite c := Measure.sigmaFinite_of_le b h
  have hac : c ≪ b := Measure.absolutelyContinuous_of_le h
  have hf : Measurable (c.rnDeriv b) := Measure.measurable_rnDeriv c b
  have hle : c.rnDeriv b ≤ᵐ[b] 1 := Measure.rnDeriv_le_one_of_le h
  refine ⟨b.withDensity (1 - c.rnDeriv b), ?_⟩
  have h1 : c = b.withDensity (c.rnDeriv b) := (Measure.withDensity_rnDeriv_eq c b hac).symm
  have h2 : c + b.withDensity (1 - c.rnDeriv b) = b.withDensity (c.rnDeriv b + (1 - c.rnDeriv b)) := by
    rw [withDensity_add_left hf, ← h1]
  rw [h2]
  conv_lhs => rw [← withDensity_one (μ := b)]
  refine withDensity_congr_ae ?_
  filter_upwards [hle] with x hx
  simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply]
  exact (add_tsub_cancel_of_le hx).symm

/-- Splitting criterion for `a ≤ b` along a measurable set. -/
lemma measure_le_of_split {a b : Measure X} {T : Set X} (hT : MeasurableSet T)
    (h1 : ∀ A, MeasurableSet A → A ⊆ T → a A ≤ b A)
    (h2 : ∀ A, MeasurableSet A → A ⊆ Tᶜ → a A ≤ b A) : a ≤ b := by
  refine Measure.le_iff.2 fun A hA => ?_
  rw [← measure_inter_add_sdiff A hT, ← measure_inter_add_sdiff A hT (μ := b)]
  exact add_le_add (h1 _ (hA.inter hT) inter_subset_right)
    (h2 _ (hA.diff hT) fun x hx => hx.2)

end FormalResearch.ModularBootstrap.Integrality
