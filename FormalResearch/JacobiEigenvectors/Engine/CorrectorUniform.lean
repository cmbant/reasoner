module

public import Mathlib
public import FormalResearch.Analysis.UniformTaylor
public import FormalResearch.JacobiEigenvectors.Engine.CorrectorLocal

/-!
# Paper J engine: defect bounds uniform in a compact parameter set

`localized_eng_corr` (`thm:eng-corr` on `[a, b]`) gives, for one symbol and one spectral parameter, constants
`C, δ` with `|defect| ≤ C |h|^{m+1}`.  The chain hypotheses `LadderData.Valid` need one constant for all
parameters `θ = (μ, X)` of a compact set.  `localized_eng_corr_uniform` supplies it from the pointwise
theorem and the joint regularity of the defect in `(θ, u, h)` (the `C^{m+1}` dependence on `h` with a
jointly continuous `(m+1)`-th derivative; in the paper this is the joint regularity of the chart data,
`lem:smo-budget` (e)), by `FormalResearch.Analysis.uniform_bigO_of_pointwise`.
-/

@[expose] public section

noncomputable section

open Set

namespace FormalResearch.JacobiEigenvectors.Engine

variable {K : ℕ} {a b η : ℝ} {pp qq : ℝ → ℝ → ℝ} {PiP PiM : ℝ → ℝ → M2}
  {g b_fn : ℕ → ℝ → ℝ} {c : ℕ → ℝ}

/-- Both defect components are `O(h^{m+1})` uniformly on `[a, b]` (the first clause of `thm:eng-corr`). -/
theorem localized_defect_UOOn (S : LocalCorrSetting K a b η pp qq PiP PiM)
    (C : LocalCorrectors K a b η pp PiP PiM qq g b_fn c) {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 2 * K + 1)
    (k : Fin 2) :
    UOOn (Icc a b) (m + 1) (fun u h => defectRow pp qq (Ahat g m) (Bhat b_fn m) PiP PiM u h k) := by
  obtain ⟨hodd, heven⟩ := localized_eng_corr S C hm1 hm
  rcases Nat.even_or_odd m with he | ho
  · obtain ⟨h0, h1⟩ := heven he
    fin_cases k
    · exact h0.mono (by omega)
    · exact h1
  · obtain ⟨h0, h1⟩ := hodd ho
    fin_cases k
    · exact h0
    · exact h1.mono (by omega)

/-- **`thm:eng-corr` with constants uniform in a compact parameter set.**  For a family of symbols,
ladders and correctors indexed by `θ ∈ S` (`S` compact), each satisfying the localised standing hypotheses
and corrector equations on `[a, b]`, and whose defect component `k` is `C^{m+1}` in `h` on `(-δ₀, δ₀)` with
`(θ, u, h) ↦ ∂_h^{m+1} defect` continuous on `S × [a, b] × [-δ₀/2, δ₀/2]`, one constant `C` and one `δ`
give `|defect| ≤ C |h|^{m+1}` for all `θ ∈ S`, `u ∈ [a, b]`, `|h| < δ`. -/
theorem localized_eng_corr_uniform {Θ : Type*} [TopologicalSpace Θ] {P : Set Θ} (hP : IsCompact P)
    {pp qq : Θ → ℝ → ℝ → ℝ} {PiP PiM : Θ → ℝ → ℝ → M2} {g b_fn : Θ → ℕ → ℝ → ℝ} {c : Θ → ℕ → ℝ}
    (hS : ∀ θ ∈ P, LocalCorrSetting K a b η (pp θ) (qq θ) (PiP θ) (PiM θ))
    (hC : ∀ θ ∈ P, LocalCorrectors K a b η (pp θ) (PiP θ) (PiM θ) (qq θ) (g θ) (b_fn θ) (c θ))
    {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 2 * K + 1) (k : Fin 2) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hreg : ∀ θ ∈ P, ∀ u ∈ Icc a b, ContDiffOn ℝ (m + 1)
      (fun h => defectRow (pp θ) (qq θ) (Ahat (g θ) m) (Bhat (b_fn θ) m) (PiP θ) (PiM θ) u h k)
      (Ioo (-δ₀) δ₀))
    (hcont : ContinuousOn (fun p : (Θ × ℝ) × ℝ => iteratedDeriv (m + 1)
      (fun h => defectRow (pp p.1.1) (qq p.1.1) (Ahat (g p.1.1) m) (Bhat (b_fn p.1.1) m)
        (PiP p.1.1) (PiM p.1.1) p.1.2 h k) p.2)
      ((P ×ˢ Icc a b) ×ˢ Icc (-(δ₀ / 2)) (δ₀ / 2))) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ θ ∈ P, ∀ u ∈ Icc a b, ∀ h, |h| < δ →
      |defectRow (pp θ) (qq θ) (Ahat (g θ) m) (Bhat (b_fn θ) m) (PiP θ) (PiM θ) u h k| ≤
        C * |h| ^ (m + 1) := by
  have hcpt : IsCompact (P ×ˢ Icc a b) := hP.prod isCompact_Icc
  obtain ⟨C, δ, hδ, hb⟩ := FormalResearch.Analysis.uniform_bigO_of_pointwise hcpt hδ₀
    (f := fun p h => defectRow (pp p.1) (qq p.1) (Ahat (g p.1) m) (Bhat (b_fn p.1) m)
      (PiP p.1) (PiM p.1) p.2 h k)
    (fun p hp => hreg p.1 hp.1 p.2 hp.2) hcont
    (fun p hp => by
      obtain ⟨C, δ, hδ, hb⟩ := localized_defect_UOOn (hS p.1 hp.1) (hC p.1 hp.1) hm1 hm k
      exact ⟨C, δ, hδ, fun h hh => hb p.2 hp.2 h hh⟩)
  exact ⟨C, δ, hδ, fun θ hθ u hu h hh => hb (θ, u) ⟨hθ, hu⟩ h hh⟩

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.localized_eng_corr_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.localized_eng_corr_uniform

end FormalResearch.JacobiEigenvectors.Engine
