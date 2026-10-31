import FormalResearch.FourQubitEntropy.RenyiFullState
import FormalResearch.FourQubitEntropy.PaperECriticalZeroOrbits
import FormalResearch.FourQubitEntropy.Tradeoff
import FormalResearch.FourQubitEntropy.CriticalOrbitPhi

/-!
# Equality classes of the Rényi envelope below the crossing, as local-unitary orbits

Paper E, `cor:fqe-renyi-gw`: for `q < q_*` the maximisers are exactly the two HS local-unitary orbits.
The spectral clause of `meanRenyi_envelope` (three HS cut spectra) is turned into an LU statement:
three HS cut spectra force `P = 1`, `F = 0`, hence (`PaperECritical.moment_zeros`) one of the five
zero orbits of `F`, and `P = 1` excludes the three Bell-pair products (purity `3/2`).

`meanRenyi_envelope_eq_hs`: for `1 < q` with `h_q > 5/3`, equality `E_q(ψ) = h_q` forces `ψ` to be
LU-equivalent to `M₄` or `conj M₄` (under `ClassicalRelaxation` and (QK)); conversely `M₄` attains it
(`meanRenyi_M4`).  The cluster clause for `q > q_*` is spectral only (the (QF) identification of
two-flat states with the cluster-to-Bell family is not formalised).
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy

theorem pur_cub_of_hsPerm {l : Fin 4 → ℝ} (h : IsHsPerm l) : pur l = 1 / 3 ∧ cub l = 5 / 36 := by
  obtain ⟨e, he⟩ := h
  have h2 := Equiv.sum_comp e (fun i => hsSpec i ^ 2)
  have h3 := Equiv.sum_comp e (fun i => hsSpec i ^ 3)
  have p2 : pur l = ∑ i, hsSpec i ^ 2 := by unfold pur; simp only [he]; exact h2
  have p3 : cub l = ∑ i, hsSpec i ^ 3 := by unfold cub; simp only [he]; exact h3
  rw [p2, p3]
  unfold hsSpec
  simp [Fin.sum_univ_four]
  norm_num

theorem hs_triple_LU {ψ : Psi} (hψ : normSqPsi ψ = 1)
    (h : IsHsTriple (cutSpec₂ ψ) (cutSpec₃ ψ) (cutSpec₄ ψ)) :
    LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ := by
  obtain ⟨h2, h3, h4⟩ := h
  obtain ⟨a2, b2⟩ := pur_cub_of_hsPerm h2
  obtain ⟨a3, b3⟩ := pur_cub_of_hsPerm h3
  obtain ⟨a4, b4⟩ := pur_cub_of_hsPerm h4
  have hP : purity ψ = 1 := by
    rw [← Pm_cutSpec]; unfold Pm; rw [a2, a3, a4]; norm_num
  have hF : sexticF ψ = 0 := by
    rw [← Fm_cutSpec ψ hψ]; unfold Fm Tm; rw [Pm_cutSpec, hP, b2, b3, b4]; norm_num
  rcases (PaperECritical.moment_zeros ψ hψ).1 hF with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    have := CO.purity_LUEquiv h
    rw [hP, bell2_vals.2.1] at this; norm_num at this
  · exfalso
    have := CO.purity_LUEquiv h
    rw [hP, bell13_vals.2.1] at this; norm_num at this
  · exfalso
    have := CO.purity_LUEquiv h
    rw [hP, bell14_vals.2.1] at this; norm_num at this

/-- **`cor:fqe-renyi-gw`, `q > 1`, equality below the crossing**: if `h_q > 5/3` and `E_q(ψ) = h_q`, then
`ψ` is LU-equivalent to `M₄` or `conj M₄`. -/
theorem meanRenyi_envelope_eq_hs (hCl : ClassicalRelaxation) (hQK : QuadraticVarianceBound)
    {ψ : Psi} (hψ : normSqPsi ψ = 1) {q : ℝ} (hq : 1 < q) (hgt : 5 / 3 < hsRenyi q)
    (heq : meanRenyi q ψ = hsRenyi q) : LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ :=
  hs_triple_LU hψ ((meanRenyi_envelope hCl hQK hψ hq).2.1 hgt heq)


/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.dual_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dual_bound

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.cubic_envelope_le_five_thirds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_envelope_le_five_thirds

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.caseL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms caseL

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.caseC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms caseC

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.sliver_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sliver_core

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.classical_of_certificates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms classical_of_certificates

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.envelope_triple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms envelope_triple

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.meanRenyi_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms meanRenyi_envelope

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.hs_triple_LU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hs_triple_LU

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.meanRenyi_envelope_eq_hs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms meanRenyi_envelope_eq_hs

end FormalResearch.FourQubitEntropy.RenyiFull
