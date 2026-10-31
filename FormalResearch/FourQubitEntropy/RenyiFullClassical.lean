import FormalResearch.FourQubitEntropy.RenyiFullSliver

/-!
# `thm:fqe-renyi-classical`: the classical relaxation at the two anchor orders

Paper E, `renyi_uncapped_covering.tex`, `sup_renyi.tex` (`sec:sup-renyi-classical-proof`).

`ClassicalRelaxation` is the statement of `thm:fqe-renyi-classical`: every triple with `P ≥ 1`, `F ≥ 0`
and (QK) satisfies one of

1. `F ≥ 3/20` or `20ε + 2F ≥ 1`: `E_{q_s} ≤ 5/3`, with equality only at the cluster triple `(c₁, c₂, c₂)`;
2. otherwise `E_{q_u} ≤ h_{q_u}`, with equality only for three HS spectra.

`classical_of_certificates` proves it from the six per-spectrum statements of `RenyiFullProps.lean`.
The high-`F` case `20ε + 2F ≥ 1` is unconditional (`cubic_envelope_le_five_thirds`).
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy

/-- **`thm:fqe-renyi-classical`**, with `q_s = 1587/1000` and `q_u = 8/5`. -/
def ClassicalRelaxation : Prop :=
  ∀ l₂ l₃ l₄ : Fin 4 → ℝ, RelaxTriple l₂ l₃ l₄ →
    ((3 / 20 ≤ Fm l₂ l₃ l₄ ∨ 1 ≤ 20 * (Pm l₂ l₃ l₄ - 1) + 2 * Fm l₂ l₃ l₄) →
        Em qS l₂ l₃ l₄ ≤ 5 / 3 ∧ (Em qS l₂ l₃ l₄ = 5 / 3 → IsClusterTriple l₂ l₃ l₄)) ∧
    (¬ (3 / 20 ≤ Fm l₂ l₃ l₄ ∨ 1 ≤ 20 * (Pm l₂ l₃ l₄ - 1) + 2 * Fm l₂ l₃ l₄) →
        Em qU l₂ l₃ l₄ ≤ hsq qU ∧ (Em qU l₂ l₃ l₄ = hsq qU → IsHsTriple l₂ l₃ l₄))

theorem qb_le_qS : PaperECritical.qb ≤ qS := by
  have := PaperECritical.qb_bounds
  unfold qS; linarith [this.2.1, this.2.2]

/-- **The sliver, any distinguished cut.** -/
theorem caseSliver (hDM : DetReduction) (hNU : NearUniformDual) (hSL : ClusterSliver)
    {l₂ l₃ l₄ : Fin 4 → ℝ} (R : RelaxTriple l₂ l₃ l₄)
    (hF : 11 / 25 ≤ Fm l₂ l₃ l₄) (hE : 20 * (Pm l₂ l₃ l₄ - 1) + 2 * Fm l₂ l₃ l₄ < 1)
    (hbig : 47 / 100 ≤ pur l₂ ∨ 47 / 100 ≤ pur l₃ ∨ 47 / 100 ≤ pur l₄) :
    Em qS l₂ l₃ l₄ < 5 / 3 := by
  rcases hbig with h | h | h
  · exact sliver_core hDM hNU hSL R hF hE h
  · have R' := R.rot
    have := sliver_core hDM hNU hSL R' (by rw [Fm_rot]; exact hF)
      (by rw [Fm_rot, Pm_rot]; exact hE) h
    rwa [Em_rot] at this
  · have R' := R.rot.rot
    have := sliver_core hDM hNU hSL R' (by rw [Fm_rot, Fm_rot]; exact hF)
      (by rw [Fm_rot, Fm_rot, Pm_rot, Pm_rot]; exact hE) h
    rwa [Em_rot, Em_rot] at this

/-- **`thm:fqe-renyi-classical`** from the six per-spectrum certificates. -/
theorem classical_of_certificates (hDM : DetReduction) (hHZ : HsSupporting) (hL : RationalDual)
    (hC : CappedCubic) (hNU : NearUniformDual) (hSL : ClusterSliver) : ClassicalRelaxation := by
  intro l₂ l₃ l₄ R
  refine ⟨fun hcase => ?_, fun hcase => ?_⟩
  · by_cases hHC : 1 ≤ 20 * (Pm l₂ l₃ l₄ - 1) + 2 * Fm l₂ l₃ l₄
    · exact cubic_envelope_le_five_thirds R.prob₂ R.prob₃ R.prob₄ qb_le_qS hHC
    · push Not at hHC
      have hF : 3 / 20 ≤ Fm l₂ l₃ l₄ := by
        rcases hcase with h | h
        · exact h
        · linarith
      have hlt : Em qS l₂ l₃ l₄ < 5 / 3 := by
        by_cases h1 : Fm l₂ l₃ l₄ ≤ 11 / 25
        · exact caseL hL R hF h1 hHC
        · push Not at h1
          have hε : Pm l₂ l₃ l₄ - 1 ≤ 1 / 100 := by linarith
          by_cases h2 : pur l₂ ≤ 47 / 100 ∧ pur l₃ ≤ 47 / 100 ∧ pur l₄ ≤ 47 / 100
          · exact caseC hC R h1.le hε h2.1 h2.2.1 h2.2.2
          · have : 47 / 100 ≤ pur l₂ ∨ 47 / 100 ≤ pur l₃ ∨ 47 / 100 ≤ pur l₄ := by
              by_contra hn
              push Not at hn
              exact h2 ⟨hn.1.le, hn.2.1.le, hn.2.2.le⟩
            exact caseSliver hDM hNU hSL R h1.le hHC this
      exact ⟨hlt.le, fun heq => absurd heq hlt.ne⟩
  · push Not at hcase
    exact caseHZ hHZ R hcase.1 hcase.2

end FormalResearch.FourQubitEntropy.RenyiFull
