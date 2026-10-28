import FormalResearch.FourQubitEntropy.SevenQubitJointMajorant
import FormalResearch.FourQubitEntropy.SevenQubitCompetitorBand

/-!
# `thm:seven-entropy-global-maximum`: the final reduction (conditional)

Source: `ResearchNotes/QI/seven_qubit_entanglement/seven_qubit_entropy_certificate.tex`, proof of
`thm:seven-entropy-global-maximum` (`E₃(z) ≤ E_*`), which reads: it suffices to consider
`E₃(z) ≥ E_*`; `prop:seven-competitor-band` and `cor:seven-entropy-eigen-cap-497` put such a
state in the region `p₀ ≤ π₃ ≤ p_c`, `R_S ⪯ κ I` (`p₀ = 121/917`, `p_c = 8693/64000`,
`κ = 497/1000`); then `prop:seven-joint-entropy-target` and `thm:seven-entropy-localized-identity`
give `E₃(z) ≤ 𝒫₅(z) ≤ E_*`.

Entropies are in nats (`meanEntropy3`), so the paper's `E_* > 59307/20000` bits is
`E_* > (59307/20000) ln 2` here.

**This is a reduction, not a proof of the maximum.**

## Proved in Lean (this file, with `SevenQubitCompetitorBand`, `SevenQubitEigenCap497Pure`)

* `contender_region`: every unit vector with `E₃(ψ) ≥ E_*` lies in the contender region, namely
  `121/917 ≤ π₃ ≤ 8693/64000` (`competitor_purity_band`: the upper bound is proved from the averaged
  linear purity bound; the lower bound is `SevenPurityBound`) and every eigenvalue of every
  three-qubit marginal is `≤ 497/1000` (`eigenCap_497_pure`: proved, using the spin-flip cross-cut
  inequality of `SevenQubitSpectralPair*`).
* `seven_entropy_max_reduction`: the chaining `E₃ ≤ 𝒫₅ ≤ E_*`, with `𝒫₅` an arbitrary function.
* `seven_entropy_max_reduction_of_scalarMajorant`: the same with `𝒫₅ := jointP5 K h` the explicit
  joint functional of `SevenQubitJointMajorant`, so that `JointMajorantBound` is *proved* from the
  scalar hypothesis `ScalarMajorant` (the matrix part of `prop:seven-joint-entropy-target`).

## Hypotheses (explicit arguments, **not** proved here)

1. `SevenPurityBound`: `π₃ ≥ 121/917` for all unit vectors (computer certificate; not formalized).
2. The SC-2 witness `(59307/20000) ln 2 < E_*`.  In the paper `E_* = E₃(ψ_{x_*})` is the candidate
   value; here `E_*` is an arbitrary real, so this file does **not** show that `E_*` is attained.
3. `LocalizedBound P5 E_*`: `thm:seven-entropy-localized-identity` (verified-arithmetic certificate
   E7-1), in its consequence `𝒫₅(z) ≤ E_*` on the contender region.  The polynomial identity, the
   Gram matrices `C_b`, and the homogenization to five-copy moments are not formalized.
4. `JointMajorantBound P5`: the entropy inequality `E₃(z) ≤ 𝒫₅(z)` on the contender region
   (`prop:seven-joint-entropy-target`).  For the paper's `𝒫₅` it follows from the matrix part proved
   in `SevenQubitJointMajorant` plus the scalar majorant `H(λ,μ) ≥ (f(λ)+f(μ))/2` on
   `[0,497/1000]²` (lemma AH-6, an interval certificate; **not** formalized), see the second
   theorem.

Not formalized at all: that the explicit coefficients `h_{kl}` of the paper define a polynomial
satisfying AH-6; that the candidate states `φ_s` give `𝒫₅(φ_s) = E_*`; that `E_*` equals
`(39 f(c) + 8 f(a) + 6 f(d) + 3 f(b))/7` at the root `x_*`; attainment.
-/

open Real Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitConseq

namespace MaximumReduction

open FormalResearch.FourQubitEntropy.SevenQubitIco
open JointMajorant

/-- The contender region `p₀ ≤ π₃ ≤ p_c`, `R_S ⪯ κ I` (`p₀ = 121/917`, `p_c = 8693/64000`,
`κ = 497/1000`) of `eq:seven-entropy-compatible-bound`, for a unit vector `ψ`. -/
def ContenderRegion (ψ : BitString → ℂ) : Prop :=
  UnitVec ψ ∧ 121 / 917 ≤ meanPurity3 ψ ∧ meanPurity3 ψ ≤ 8693 / 64000 ∧
    ∀ m ∈ tripleMasks, ∀ x,
      (redMatPsi_isHermitian (maskCut 3 4 m) ψ).eigenvalues x ≤ 497 / 1000

/-- **Hypothesis `JointMajorantBound`** (`prop:seven-joint-entropy-target`, entropy part):
`E₃(z) ≤ 𝒫₅(z)` on the contender region. -/
def JointMajorantBound (P5 : (BitString → ℂ) → ℝ) : Prop :=
  ∀ ψ, ContenderRegion ψ → meanEntropy3 ψ ≤ P5 ψ

/-- **Hypothesis `LocalizedBound`** (`thm:seven-entropy-localized-identity`, consequence
`eq:seven-entropy-compatible-bound`, certificate E7-1): `𝒫₅(z) ≤ E_*` on the contender region. -/
def LocalizedBound (P5 : (BitString → ℂ) → ℝ) (Estar : ℝ) : Prop :=
  ∀ ψ, ContenderRegion ψ → P5 ψ ≤ Estar

/-- **Every contender lies in the region (proved, modulo `SevenPurityBound` and the SC-2 witness).**
A unit vector with `E₃(ψ) ≥ E_* > (59307/20000) ln 2` has `121/917 ≤ π₃ ≤ 8693/64000` and all
eigenvalues of all three-qubit marginals `≤ 497/1000`. -/
theorem contender_region (hPB : SevenPurityBound) {Estar : ℝ}
    (hwit : (59307 / 20000) * log 2 < Estar) (ψ : BitString → ℂ) (hψ : UnitVec ψ)
    (hE : Estar ≤ meanEntropy3 ψ) : ContenderRegion ψ := by
  obtain ⟨h1, h2⟩ := competitor_purity_band hPB ψ hψ hwit hE
  exact ⟨hψ, h1, h2.le, fun m hm x => (EigCap.eigenCap_497_pure ψ hψ hwit hE m hm x).le⟩

/-- **`thm:seven-entropy-global-maximum`, final reduction.**  Assume the sharp purity bound, the
SC-2 witness `(59307/20000) ln 2 < E_*`, the joint-majorant conclusion `E₃ ≤ 𝒫₅` and the
localized-identity conclusion `𝒫₅ ≤ E_*` on the contender region.  Then every unit vector has
`E₃(ψ) ≤ E_*`.  (Hypotheses are not proved here; see the module docstring.) -/
theorem seven_entropy_max_reduction (hPB : SevenPurityBound) {Estar : ℝ}
    (hwit : (59307 / 20000) * log 2 < Estar) {P5 : (BitString → ℂ) → ℝ}
    (hJ : JointMajorantBound P5) (hL : LocalizedBound P5 Estar)
    (ψ : BitString → ℂ) (hψ : UnitVec ψ) : meanEntropy3 ψ ≤ Estar := by
  by_cases hE : Estar ≤ meanEntropy3 ψ
  · have hR := contender_region hPB hwit ψ hψ hE
    exact (hJ ψ hR).trans (hL ψ hR)
  · exact (not_le.1 hE).le

/-- `JointMajorantBound` for the explicit functional `jointP5 K h` follows from the scalar
majorant `H ≥ (f ⊕ f)/2` on `[0,497/1000]²` (AH-6, hypothesis) by the matrix part proved in
`SevenQubitJointMajorant`. -/
theorem jointMajorantBound_of_scalarMajorant (K : Finset (ℕ × ℕ)) (h : ℕ → ℕ → ℝ)
    (hH : ScalarMajorant (polyH K h) (497 / 1000)) : JointMajorantBound (jointP5 K h) :=
  fun ψ hR => meanEntropy3_le_jointP5 K h _ hH ψ hR.2.2.2

/-- **Final reduction with the explicit joint functional.**  Same as `seven_entropy_max_reduction`
with `𝒫₅ = jointP5 K h` and `JointMajorantBound` replaced by its source, the scalar majorant
`ScalarMajorant (polyH K h) (497/1000)` (lemma AH-6, interval-certified, hypothesis).  The remaining
hypotheses are `SevenPurityBound`, the SC-2 witness and `LocalizedBound (jointP5 K h) E_*`
(the localized identity E7-1). -/
theorem seven_entropy_max_reduction_of_scalarMajorant (hPB : SevenPurityBound) {Estar : ℝ}
    (hwit : (59307 / 20000) * log 2 < Estar) (K : Finset (ℕ × ℕ)) (h : ℕ → ℕ → ℝ)
    (hH : ScalarMajorant (polyH K h) (497 / 1000)) (hL : LocalizedBound (jointP5 K h) Estar)
    (ψ : BitString → ℂ) (hψ : UnitVec ψ) : meanEntropy3 ψ ≤ Estar :=
  seven_entropy_max_reduction hPB hwit (jointMajorantBound_of_scalarMajorant K h hH) hL ψ hψ

end MaximumReduction

end FormalResearch.FourQubitEntropy.SevenQubitConseq
