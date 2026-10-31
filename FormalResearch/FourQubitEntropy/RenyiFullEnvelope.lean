import FormalResearch.FourQubitEntropy.RenyiFullClassical

/-!
# The Rényi envelope above one for triples and states: `cor:fqe-renyi-gw`, `q > 1`

Paper E, `cor:fqe-renyi-gw` (`spectral_corollaries.tex`) and the coverage table of
`renyi_proofs_appendix.tex`.

* `envelope_triple`: from `ClassicalRelaxation` and the order transfer (`renyi_order_transfer_all`),
  every triple of the relaxation and every `q > 1` satisfy `E_q ≤ max {h_q, 5/3}` with the equality
  clauses (three HS spectra when `h_q > 5/3`, the cluster triple when `h_q < 5/3`, either at
  `h_q = 5/3`, i.e. `q = q_*`).
* `meanRenyi_envelope`: for every unit four-qubit vector satisfying (QK) (taken as a hypothesis;
  `thm:fqe-quadratic-variance` is an exact-rational certificate not formalised here),
  `meanRenyi q ψ ≤ max {hsRenyi q, 5/3}` for every `q > 1`, with the spectral equality clauses.

The equality statement is spectral: equality at `h_q > 5/3` means three HS cut spectra.
The identification of states with HS cut spectra with the LU orbits of `M₄`, `conj M₄` is
`PaperECritical.moment_zeros`; the identification of the cluster triple with the cluster-to-Bell
family (`prop:fqe-two-flat-rigidity`, the (QF) step) is not formalised.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy

theorem Em_anti {l₂ l₃ l₄ : Fin 4 → ℝ} (h₂ : IsProb4 l₂) (h₃ : IsProb4 l₃) (h₄ : IsProb4 l₄)
    {q q' : ℝ} (hq : 1 < q') (hqq : q' ≤ q) : Em q l₂ l₃ l₄ ≤ Em q' l₂ l₃ l₄ := by
  have a2 := renyiSpec_anti hq hqq h₂.1 h₂.2
  have a3 := renyiSpec_anti hq hqq h₃.1 h₃.2
  have a4 := renyiSpec_anti hq hqq h₄.1 h₄.2
  unfold Em renyiE
  linarith

theorem hsq_strictAnti {q q' : ℝ} (h1 : 1 < q) (h : q < q') : hsq q' < hsq q := by
  rw [hsq_eq, hsq_eq]
  exact hsRenyi_strictAntiOn (Set.mem_Ioi.2 h1) (Set.mem_Ioi.2 (h1.trans h)) h

theorem hsq_qS_gt : 5 / 3 < hsq qS := by
  rw [hsq_eq]; unfold qS; exact hs_gt_at_1587

theorem hsq_qU_lt : hsq qU < 5 / 3 := by
  rw [hsq_eq]; unfold qU; exact hs_lt_at_eight_fifths

theorem qS_lt_qU : qS < qU := by unfold qS qU; norm_num

/-- **`cor:fqe-renyi-gw` for triples, `q > 1`** (from `ClassicalRelaxation`). -/
theorem envelope_triple (hCl : ClassicalRelaxation) {l₂ l₃ l₄ : Fin 4 → ℝ}
    (R : RelaxTriple l₂ l₃ l₄) {q : ℝ} (hq : 1 < q) :
    Em q l₂ l₃ l₄ ≤ max (hsq q) (5 / 3) ∧
    (5 / 3 < hsq q → Em q l₂ l₃ l₄ = hsq q → IsHsTriple l₂ l₃ l₄) ∧
    (hsq q < 5 / 3 → Em q l₂ l₃ l₄ = 5 / 3 → IsClusterTriple l₂ l₃ l₄) ∧
    (hsq q = 5 / 3 → Em q l₂ l₃ l₄ = 5 / 3 → IsHsTriple l₂ l₃ l₄ ∨ IsClusterTriple l₂ l₃ l₄) := by
  obtain ⟨hA, hB⟩ := hCl l₂ l₃ l₄ R
  have tr := fun {q1 : ℝ} (h : q < q1) =>
    renyi_order_transfer_all R.prob₂ R.prob₃ R.prob₄ hq h
  have hqS1 := qS_gt_one
  have hqU1 := qU_gt_one
  have hmax1 : hsq q ≤ max (hsq q) (5 / 3) := le_max_left _ _
  have hmax2 : 5 / 3 ≤ max (hsq q) (5 / 3) := le_max_right _ _
  by_cases hcase : 3 / 20 ≤ Fm l₂ l₃ l₄ ∨ 1 ≤ 20 * (Pm l₂ l₃ l₄ - 1) + 2 * Fm l₂ l₃ l₄
  · obtain ⟨hE1, hE2⟩ := hA hcase
    rcases lt_trichotomy q qS with hlt | heq | hgt
    · -- q < q_s
      have t := tr hlt
      have h1 : Em qS l₂ l₃ l₄ < hsq qS := lt_of_le_of_lt hE1 hsq_qS_gt
      have h2 : Em q l₂ l₃ l₄ < hsq q := t.2.1 (by exact h1)
      have h3 : 5 / 3 < hsq q := lt_trans hsq_qS_gt (hsq_strictAnti hq hlt)
      refine ⟨by linarith, fun _ h => absurd h h2.ne, fun h => absurd h (by linarith),
        fun h => absurd h (by linarith)⟩
    · subst heq
      have h3 : 5 / 3 < hsq qS := hsq_qS_gt
      refine ⟨by linarith, fun _ h => by linarith, fun h => absurd h (by linarith),
        fun h => absurd h (by linarith)⟩
    · have h1 : Em q l₂ l₃ l₄ ≤ Em qS l₂ l₃ l₄ := Em_anti R.prob₂ R.prob₃ R.prob₄ hqS1 hgt.le
      refine ⟨by linarith, fun h3 h => by linarith, fun _ h => hE2 (by linarith),
        fun _ h => Or.inr (hE2 (by linarith))⟩
  · obtain ⟨hE1, hE2⟩ := hB hcase
    rcases lt_trichotomy q qU with hlt | heq | hgt
    · have t := tr hlt
      have h1 : Em q l₂ l₃ l₄ ≤ hsq q := t.1 hE1
      refine ⟨by linarith, fun _ h => t.2.2 hE1 h, fun h h' => absurd h' (by linarith),
        fun h h' => Or.inl (t.2.2 hE1 (by show Em q l₂ l₃ l₄ = hsq q; linarith))⟩
    · subst heq
      have h3 : hsq qU < 5 / 3 := hsq_qU_lt
      refine ⟨by linarith, fun h => absurd h (by linarith), fun _ h => absurd h (by linarith),
        fun h => absurd h (by linarith)⟩
    · have h1 : Em q l₂ l₃ l₄ ≤ Em qU l₂ l₃ l₄ := Em_anti R.prob₂ R.prob₃ R.prob₄ hqU1 hgt.le
      have h2 : hsq q < hsq qU := hsq_strictAnti hqU1 hgt
      have h3 := hsq_qU_lt
      refine ⟨by linarith, fun h => absurd h (by linarith), fun _ h => absurd h (by linarith),
        fun h => absurd h (by linarith)⟩

end FormalResearch.FourQubitEntropy.RenyiFull
