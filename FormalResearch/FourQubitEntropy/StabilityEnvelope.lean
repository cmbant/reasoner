import FormalResearch.FourQubitEntropy.GeneralEnvelope
import FormalResearch.FourQubitEntropy.Stability

/-!
# Spectral stability with the general envelope, unconditionally

`thm:fqe-general-envelope` (`GeneralEnvelope.lean`, `envelope_weak`) gives
`(3/4) W₁ + τ - τ^{3/2} ≤ F` for every unit state. The `*_of_envelope` theorems of `Stability.lean` take that
inequality as a hypothesis `henv`; here it is discharged, so the paper's estimates (with the extra term
`(a/12)(τ - τ^{3/2})`) hold outright.
-/

namespace FormalResearch.FourQubitEntropy

/-- **Stability for a cubic majorant** (`eq:fqe-spectral-plus` with the general envelope), unconditional. -/
theorem majorant_stability_env {f : ℝ → ℝ} {a b c d : ℝ} (hM : Majorant f a b c d) (ha : 0 ≤ a)
    (hb : b + 17 * a / 12 ≤ 0) (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    ((-b - 17 * a / 12) / 2 + a / 16) * blochSq ψ
      + ((-b - 17 * a / 12) / 2) * Complex.normSq (spinFlipForm ψ)
      + a / 12 * (Complex.normSq (spinFlipForm ψ)
          - Complex.normSq (spinFlipForm ψ) * Real.sqrt (Complex.normSq (spinFlipForm ψ)))
    ≤ 3 * (meanSpec f M4 - meanSpec f ψ) :=
  majorant_stability_of_envelope hM ha hb ψ hψ (envelope_weak ψ hψ)

/-- **Von Neumann stability** (the paper's estimate in `spectral_proofs.tex`), unconditional: with
`δ = E(M₄) - E(ψ)` in bits,
`3 ln 2 · δ ≥ ((21 - 15 ln 3)/8) W₁ + ((9 - 6 ln 3)/4) τ - (3/2)(ln 3 - 1) τ^{3/2}`. -/
theorem entropy_stability_env (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    (21 - 15 * Real.log 3) / 8 * blochSq ψ
      + (9 - 6 * Real.log 3) / 4 * Complex.normSq (spinFlipForm ψ)
      - 3 / 2 * (Real.log 3 - 1)
          * (Complex.normSq (spinFlipForm ψ) * Real.sqrt (Complex.normSq (spinFlipForm ψ)))
    ≤ 3 * Real.log 2 * (meanEntropy M4 - meanEntropy ψ) :=
  entropy_stability_of_envelope ψ hψ (envelope_weak ψ hψ)

/-- **Tsallis stability** (`0 < q < 2`, `q ≠ 1`), unconditional. -/
theorem tsallis_stability_env {q : ℝ} (h0 : 0 < q) (h2 : q < 2) (h1 : q ≠ 1) (ψ : Psi)
    (hψ : normSqPsi ψ = 1) :
    ((-tsB q - 17 * tsA q / 12) / 2 + tsA q / 16) * blochSq ψ
      + ((-tsB q - 17 * tsA q / 12) / 2) * Complex.normSq (spinFlipForm ψ)
      + tsA q / 12 * (Complex.normSq (spinFlipForm ψ)
          - Complex.normSq (spinFlipForm ψ) * Real.sqrt (Complex.normSq (spinFlipForm ψ)))
    ≤ 3 * (tsallisCeiling q - meanTsallis q ψ) :=
  tsallis_stability_of_envelope h0 h2 h1 ψ hψ (envelope_weak ψ hψ)

/-- info: 'FormalResearch.FourQubitEntropy.general_envelope_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms general_envelope_unit

/-- info: 'FormalResearch.FourQubitEntropy.critical_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms critical_envelope

/-- info: 'FormalResearch.FourQubitEntropy.flipGradient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flipGradient

/-- info: 'FormalResearch.FourQubitEntropy.entropy_stability_env' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entropy_stability_env

/-- info: 'FormalResearch.FourQubitEntropy.tsallis_stability_env' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tsallis_stability_env

/-- info: 'FormalResearch.FourQubitEntropy.majorant_stability_env' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms majorant_stability_env

end FormalResearch.FourQubitEntropy
