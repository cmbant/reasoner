import FormalResearch.FourQubitEntropy.SevenQubitEigenCap497
import FormalResearch.FourQubitEntropy.SevenQubitSpectralPairCross

/-!
# `cor:seven-entropy-eigen-cap-497` for pure seven-qubit states, cross-cut inequality discharged

`SevenQubitEigenCap497.eigenCap_497` takes the spin-flip cross-cut inequality `SpinFlipCrossCut`
as a hypothesis.  `SevenQubitSpectralPair.cross_cut` proves it for every pure unit vector, so here
the hypothesis is removed.  The only remaining hypothesis is the SC-2 lower witness for
`E₃(ψ_{7/100})` (`hwit`), which is not formalized.
-/

open Real Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitConseq

open FormalResearch.FourQubitEntropy.SevenQubitIco

namespace EigCap

/-- The two `vSpec` definitions agree on a normalised spectrum (`∑ l = 1`). -/
theorem vSpec_eq_pair (l : Fin 8 → ℝ) (hl : ∑ i, l i = 1) :
    vSpec l = SevenQubitSpectralPair.vSpec l := by
  rw [SevenQubitSpectralPair.vSpec_eq l hl]
  simp only [vSpec, Fin.sum_univ_eight, Fin.rev]
  simp only [Fin.sum_univ_eight] at hl
  simp [Fin.val_zero]
  nlinarith [hl]

/-- The eigenvalue list of the cut matrix is the same in both developments. -/
theorem sortedSpec_eq_lam3 (m : Fin 7 → Bool) (ψ : BitString → ℂ) :
    sortedSpec (maskCut 3 4 m) ψ =
      SevenQubitSpectralPair.lam3 (SevenQubitSpectralPair.rhoS m ψ)
        (SevenQubitSpectralPair.rhoS_hermitian m ψ) := by
  funext i
  simp only [sortedSpec, SevenQubitSpectralPair.lam3, Matrix.IsHermitian.eigenvalues, specEquiv,
    Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

/-- The spin-flip cross-cut inequality holds for every pure unit vector. -/
theorem spinFlipCrossCut_of_unit (ψ : BitString → ℂ) (hψ : UnitVec ψ) : SpinFlipCrossCut ψ := by
  intro m hm
  have hmem : weight m = 3 := (Finset.mem_filter.1 hm).2
  have h := SevenQubitSpectralPair.cross_cut m hmem ψ hψ
  have hb := maskCut_bijective_three m hmem
  have hsum := sortedSpec_sum _ hb ψ hψ
  rw [vSpec_eq_pair _ hsum, sortedSpec_eq_lam3]
  exact h

/-- **`cor:seven-entropy-eigen-cap-497`, pure states.**  If `E₃(ψ) ≥ Eref` with
`Eref > (59307/20000) ln 2` (the SC-2 witness, hypothesis), then every eigenvalue of every
three-qubit marginal of the unit vector `ψ` is `< 497/1000`. -/
theorem eigenCap_497_pure (ψ : BitString → ℂ) (hψ : UnitVec ψ)
    {Eref : ℝ} (hwit : (59307 / 20000) * log 2 < Eref) (hE : Eref ≤ meanEntropy3 ψ) :
    ∀ m ∈ tripleMasks, ∀ x,
      (redMatPsi_isHermitian (maskCut 3 4 m) ψ).eigenvalues x < 497 / 1000 :=
  eigenCap_497 ψ hψ (spinFlipCrossCut_of_unit ψ hψ) hwit hE

end EigCap

end FormalResearch.FourQubitEntropy.SevenQubitConseq
