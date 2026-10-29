import FormalResearch.FourQubitEntropy.Renyi

/-!
# Spectral stability from the polarization and spin-flip remainders

For a cubic majorant `h` with `a ≥ 0`, `α = -b - 17a/12 ≥ 0`, the gap identity (SF) of the paper
together with `2(P - 1) = W₁ + τ` and `F ≥ (3/4) n W₁` (`sexticF_ge`) gives

`3 (E_f(M₄) - E_f(ψ)) ≥ (α/2 + a/16) W₁ + (α/2) τ`,

where `W₁ = Σ_i |r_i|²` is the squared one-qubit polarization and `τ = |ψᵀ ε^{⊗4} ψ|²` the
spin-flip overlap. (The paper's finer form `(SF+)` also keeps the nonnegative residual norms of
`sextic_identity`; we drop them.)

Paper: `eq:fqe-spectral-plus` and the stability paragraphs of `spectral_proofs.tex`
("Tsallis stability", "Quantitative consequence for von Neumann entropy").

**What is proved here, and what the paper now states.** The paper's stability estimates use the general
envelope `F ≥ (3/4) W₁ + τ - τ^{3/2}` (`thm:fqe-general-envelope`, `sextic_identity.tex`), which is proved in
`GeneralEnvelope.lean` (`envelope_weak`) after this file; `StabilityEnvelope.lean` states the paper's
estimates unconditionally. They carry the extra term `(a/12)(τ - τ^{3/2}) ≥ 0`. The unconditional theorems below
(`majorant_stability`, `entropy_stability`, `entropy_stability_joint`, `tsallis_stability`) use only
`F ≥ (3/4) W₁` and are the `τ^{3/2}`-free corollaries (`τ - τ^{3/2} ≥ 0` for `τ ≤ 1`). The theorems
`*_of_envelope` at the end of the file are the paper's strengthened estimates with the general envelope
as an explicit hypothesis `henv`; they do not prove the envelope (`StabilityEnvelope.lean` does).
-/

open scoped ComplexConjugate Matrix ComplexOrder

namespace FormalResearch.FourQubitEntropy

open Real

/-- **Stability for a cubic majorant** (`τ^{3/2}`-free form). The paper's estimate adds the term
`(a/12)(τ - τ^{3/2})`, which needs the general envelope `thm:fqe-general-envelope` (`GeneralEnvelope.lean`; the unconditional
estimate is `majorant_stability_env` in `StabilityEnvelope.lean`);
see `majorant_stability_of_envelope` for that estimate conditional on the envelope. -/
theorem majorant_stability {f : ℝ → ℝ} {a b c d : ℝ} (hM : Majorant f a b c d) (ha : 0 ≤ a)
    (hb : b + 17 * a / 12 ≤ 0) (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    ((-b - 17 * a / 12) / 2 + a / 16) * blochSq ψ
      + ((-b - 17 * a / 12) / 2) * Complex.normSq (spinFlipForm ψ)
    ≤ 3 * (meanSpec f M4 - meanSpec f ψ) := by
  have g := majorant_gap hM ψ hψ
  have hpi := purity_identity_exact ψ
  have hFge := sexticF_ge ψ
  rw [hψ] at hpi hFge
  have hs := majorantSlack_nonneg hM ψ hψ
  have hα : 0 ≤ -b - 17 * a / 12 := by linarith
  have hP1 : purity ψ - 1 = (blochSq ψ + Complex.normSq (spinFlipForm ψ)) / 2 := by
    nlinarith
  rw [hP1] at g
  have k2 : 0 ≤ a / 12 * (sexticF ψ - 3 / 4 * (1 * blochSq ψ)) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- `b + 17a/12`, and `a`, as the coefficients of the von Neumann (Hermite) majorant. -/
theorem majorant_negMulLog : Majorant Real.negMulLog hermA hermB hermC hermD := by
  have key : ∀ x, 0 < x → hermCubic x - Real.negMulLog x = x * hermPhi x := fun x hx => by
    unfold hermCubic Real.negMulLog hermPhi; field_simp; ring
  refine ⟨fun x hx => negMulLog_le_hermCubic hx.1, ?_, ?_⟩
  · have := key (1 / 6) (by norm_num)
    rw [hermPhi_at_p, mul_zero] at this
    unfold cubicPoly; unfold hermCubic at this; linarith
  · have := key (1 / 2) (by norm_num)
    rw [hermPhi_at_q, mul_zero] at this
    unfold cubicPoly; unfold hermCubic at this; linarith

theorem meanEntropy_eq_meanSpec (ψ : Psi) :
    meanEntropy ψ = meanSpec Real.negMulLog ψ / Real.log 2 := by
  unfold meanEntropy meanSpec vnEntropy cutSum
  ring

/-- **Quantitative consequence for von Neumann entropy** (`τ^{3/2}`-free corollary). With
`δ = E(M₄) - E(ψ)` in bits, `3 ln 2 · δ ≥ ((21 - 15 ln 3)/8) W₁ + (15/4 - 3 ln 3) τ`.
The paper's estimate is stronger:
`3 ln 2 · δ ≥ ((21 - 15 ln 3)/8) W₁ + ((9 - 6 ln 3)/4) τ - (3/2)(ln 3 - 1) τ^{3/2}` (it adds
`(3/2)(ln 3 - 1)(τ - τ^{3/2}) ≥ 0`), from `thm:fqe-general-envelope` (`GeneralEnvelope.lean`; unconditionally `entropy_stability_env`);
`entropy_stability_of_envelope` proves it from the envelope as a hypothesis. -/
theorem entropy_stability (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    (21 - 15 * Real.log 3) / 8 * blochSq ψ
      + (15 / 4 - 3 * Real.log 3) * Complex.normSq (spinFlipForm ψ)
    ≤ 3 * Real.log 2 * (meanEntropy M4 - meanEntropy ψ) := by
  have l3b := log_three_lt
  have hA := hermA_pos
  have h := majorant_stability majorant_negMulLog hA.le
    (by unfold hermB hermA; linarith) ψ hψ
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e : 3 * Real.log 2 * (meanEntropy M4 - meanEntropy ψ)
      = 3 * (meanSpec Real.negMulLog M4 - meanSpec Real.negMulLog ψ) := by
    rw [meanEntropy_eq_meanSpec, meanEntropy_eq_meanSpec]
    field_simp
  rw [e]
  have c1 : (-hermB - 17 * hermA / 12) / 2 + hermA / 16 = (21 - 15 * Real.log 3) / 8 := by
    unfold hermA hermB; ring
  have c2 : (-hermB - 17 * hermA / 12) / 2 = 15 / 4 - 3 * Real.log 3 := by
    unfold hermA hermB; ring
  rw [c1, c2] at h
  exact h

/-- Both stability coefficients are positive. -/
theorem entropy_stability_coeffs_pos :
    0 < 21 - 15 * Real.log 3 ∧ 0 < 15 / 4 - 3 * Real.log 3 := by
  have := log_three_lt
  constructor <;> linarith

/-- The simpler joint estimate: `(15/4 - 3 ln 3)(W₁ + τ) ≤ 3 ln 2 · δ`, i.e.
`W₁ + τ ≤ 6 ln 2 / (15/2 - 6 ln 3) · δ`. -/
theorem entropy_stability_joint (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    (15 / 4 - 3 * Real.log 3) * (blochSq ψ + Complex.normSq (spinFlipForm ψ))
    ≤ 3 * Real.log 2 * (meanEntropy M4 - meanEntropy ψ) := by
  have h := entropy_stability ψ hψ
  have l3b := lt_log_three
  have hW := blochSq_nonneg ψ
  have : (15 / 4 - 3 * Real.log 3) * blochSq ψ ≤ (21 - 15 * Real.log 3) / 8 * blochSq ψ :=
    mul_le_mul_of_nonneg_right (by linarith) hW
  nlinarith

/-- **Tsallis stability** (`0 < q < 2`, `q ≠ 1`; `τ^{3/2}`-free corollary): with `a_q = tsA q` and
`α_q = -b_q - 17a_q/12`, both coefficients below are strictly positive and
`3 δ_q ≥ (α_q/2 + a_q/16) W₁ + (α_q/2) τ`, `δ_q = ceiling - mean Tsallis`. The paper's estimate adds
`(a_q/12)(τ - τ^{3/2}) ≥ 0` via `thm:fqe-general-envelope` (`GeneralEnvelope.lean`; unconditionally `tsallis_stability_env`);
see `tsallis_stability_of_envelope`. -/
theorem tsallis_stability {q : ℝ} (h0 : 0 < q) (h2 : q < 2) (h1 : q ≠ 1) (ψ : Psi)
    (hψ : normSqPsi ψ = 1) :
    0 < (-tsB q - 17 * tsA q / 12) / 2 + tsA q / 16 ∧ 0 < (-tsB q - 17 * tsA q / 12) / 2 ∧
    ((-tsB q - 17 * tsA q / 12) / 2 + tsA q / 16) * blochSq ψ
      + ((-tsB q - 17 * tsA q / 12) / 2) * Complex.normSq (spinFlipForm ψ)
    ≤ 3 * (tsallisCeiling q - meanTsallis q ψ) := by
  obtain ⟨-, ha⟩ := tsallis_hermite h0 h2 h1
  have hb := tsallis_coeff_neg h0 h2 h1
  refine ⟨by linarith, by linarith, ?_⟩
  have := majorant_stability (tsallis_majorant h0 h2 h1) ha.le hb.le ψ hψ
  rw [meanTsallis_eq_meanSpec q ψ hψ, tsallisCeiling_eq, ← meanSpec_M4]
  exact this

/-- At `q = 2` the mean Tsallis entropy is `1 - P/3`. -/
theorem meanTsallis_two (ψ : Psi) : meanTsallis 2 ψ = 1 - purity ψ / 3 := by
  unfold meanTsallis tsallisCut purity
  have e : ∀ {R : Mat4} (hR : R.IsHermitian), ∑ i, hR.eigenvalues i ^ (2 : ℝ)
      = (Matrix.trace (R * R)).re := by
    intro R hR
    simp only [Real.rpow_two]
    rw [sum_eigenvalues_pow hR 2, pow_two]
  rw [e, e, e]
  ring

/-- **Tsallis at `q = 2`** (`cor:fqe-tsallis`, sharpness paragraph). The ceiling `2/3` is valid
at `q = 2`, with gap `δ₂ = (W₁ + τ)/6`; equality holds iff `W₁ = 0` and `τ = 0` (all one-qubit
polarizations vanish and the spin-flip overlap vanishes), which is not an `M₄`-orbit
condition: the cluster state attains it. -/
theorem tsallis_two_gap (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    2 / 3 - meanTsallis 2 ψ = (blochSq ψ + Complex.normSq (spinFlipForm ψ)) / 6 := by
  rw [meanTsallis_two ψ]
  have := purity_identity_exact ψ
  rw [hψ] at this
  linarith

theorem tsallis_two_eq_iff (ψ : Psi) (hψ : normSqPsi ψ = 1) :
    meanTsallis 2 ψ = 2 / 3 ↔ blochSq ψ = 0 ∧ spinFlipForm ψ = 0 := by
  have h := tsallis_two_gap ψ hψ
  have hW := blochSq_nonneg ψ
  have hτ := Complex.normSq_nonneg (spinFlipForm ψ)
  constructor
  · intro heq
    rw [heq] at h
    have h1 : blochSq ψ + Complex.normSq (spinFlipForm ψ) = 0 := by linarith
    exact ⟨by linarith, Complex.normSq_eq_zero.1 (by linarith)⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2] at h
    simp at h
    linarith

/-- info: 'FormalResearch.FourQubitEntropy.majorant_stability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms majorant_stability

/-- info: 'FormalResearch.FourQubitEntropy.entropy_stability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entropy_stability

/-- info: 'FormalResearch.FourQubitEntropy.entropy_stability_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms entropy_stability_joint

/-- info: 'FormalResearch.FourQubitEntropy.tsallis_stability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tsallis_stability

/-- info: 'FormalResearch.FourQubitEntropy.tsallis_two_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tsallis_two_eq_iff

/-! ### The paper's strengthened estimates, conditional on the general envelope

`thm:fqe-general-envelope` gives, for unit `ψ` with `τ = |ψᵀ ε^{⊗4} ψ|²`,
`F ≥ (3/4) W₁ + τ - τ^{3/2}` (and more: a further `7τ W₁/(8(1+√τ))`); it is proved in
`GeneralEnvelope.lean`, which imports this file. The
theorems in this section take that weaker consequence as the hypothesis `henv`
(`τ^{3/2}` written `τ √τ`), and derive the paper's strengthened stability estimates, which differ from
the unconditional ones above by the added term `(a/12)(τ - τ^{3/2})`. They are conditional: nothing
here proves `henv`. -/

/-- **Stability for a cubic majorant, conditional on the general envelope.** If a unit `ψ` satisfies
`(3/4) W₁ + τ - τ √τ ≤ F` (`thm:fqe-general-envelope`, hypothesis `henv`), then the estimate of
`majorant_stability` gains the term `(a/12)(τ - τ^{3/2})`. -/
theorem majorant_stability_of_envelope {f : ℝ → ℝ} {a b c d : ℝ} (hM : Majorant f a b c d)
    (ha : 0 ≤ a) (hb : b + 17 * a / 12 ≤ 0) (ψ : Psi) (hψ : normSqPsi ψ = 1)
    (henv : 3 / 4 * blochSq ψ + Complex.normSq (spinFlipForm ψ)
        - Complex.normSq (spinFlipForm ψ) * Real.sqrt (Complex.normSq (spinFlipForm ψ))
      ≤ sexticF ψ) :
    ((-b - 17 * a / 12) / 2 + a / 16) * blochSq ψ
      + ((-b - 17 * a / 12) / 2) * Complex.normSq (spinFlipForm ψ)
      + a / 12 * (Complex.normSq (spinFlipForm ψ)
          - Complex.normSq (spinFlipForm ψ) * Real.sqrt (Complex.normSq (spinFlipForm ψ)))
    ≤ 3 * (meanSpec f M4 - meanSpec f ψ) := by
  have g := majorant_gap hM ψ hψ
  have hpi := purity_identity_exact ψ
  rw [hψ] at hpi
  have hs := majorantSlack_nonneg hM ψ hψ
  have hP1 : purity ψ - 1 = (blochSq ψ + Complex.normSq (spinFlipForm ψ)) / 2 := by
    nlinarith
  rw [hP1] at g
  have k2 : a / 12 * (Complex.normSq (spinFlipForm ψ)
        - Complex.normSq (spinFlipForm ψ) * Real.sqrt (Complex.normSq (spinFlipForm ψ)))
      ≤ a / 12 * (sexticF ψ - 3 / 4 * blochSq ψ) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith

/-- **Von Neumann stability, conditional on the general envelope** (the paper's estimate in
`spectral_proofs.tex`). With `δ = E(M₄) - E(ψ)` in bits and `henv` as in
`majorant_stability_of_envelope`,
`3 ln 2 · δ ≥ ((21 - 15 ln 3)/8) W₁ + ((9 - 6 ln 3)/4) τ - (3/2)(ln 3 - 1) τ^{3/2}`. -/
theorem entropy_stability_of_envelope (ψ : Psi) (hψ : normSqPsi ψ = 1)
    (henv : 3 / 4 * blochSq ψ + Complex.normSq (spinFlipForm ψ)
        - Complex.normSq (spinFlipForm ψ) * Real.sqrt (Complex.normSq (spinFlipForm ψ))
      ≤ sexticF ψ) :
    (21 - 15 * Real.log 3) / 8 * blochSq ψ
      + (9 - 6 * Real.log 3) / 4 * Complex.normSq (spinFlipForm ψ)
      - 3 / 2 * (Real.log 3 - 1)
          * (Complex.normSq (spinFlipForm ψ) * Real.sqrt (Complex.normSq (spinFlipForm ψ)))
    ≤ 3 * Real.log 2 * (meanEntropy M4 - meanEntropy ψ) := by
  have l3b := log_three_lt
  have hA := hermA_pos
  have h := majorant_stability_of_envelope majorant_negMulLog hA.le
    (by unfold hermB hermA; linarith) ψ hψ henv
  have e : 3 * Real.log 2 * (meanEntropy M4 - meanEntropy ψ)
      = 3 * (meanSpec Real.negMulLog M4 - meanSpec Real.negMulLog ψ) := by
    have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [meanEntropy_eq_meanSpec, meanEntropy_eq_meanSpec]
    field_simp
  rw [e]
  have c1 : (-hermB - 17 * hermA / 12) / 2 + hermA / 16 = (21 - 15 * Real.log 3) / 8 := by
    unfold hermA hermB; ring
  have c2 : (-hermB - 17 * hermA / 12) / 2 = 15 / 4 - 3 * Real.log 3 := by
    unfold hermA hermB; ring
  have c3 : hermA / 12 = 3 / 2 * (Real.log 3 - 1) := by unfold hermA; ring
  rw [c1, c2, c3] at h
  nlinarith

/-- **Tsallis stability, conditional on the general envelope** (`0 < q < 2`, `q ≠ 1`): the estimate of
`tsallis_stability` plus `(a_q/12)(τ - τ^{3/2})`, `a_q = tsA q`, from `henv`
(`(3/4) W₁ + τ - τ √τ ≤ F`, `thm:fqe-general-envelope`). -/
theorem tsallis_stability_of_envelope {q : ℝ} (h0 : 0 < q) (h2 : q < 2) (h1 : q ≠ 1) (ψ : Psi)
    (hψ : normSqPsi ψ = 1)
    (henv : 3 / 4 * blochSq ψ + Complex.normSq (spinFlipForm ψ)
        - Complex.normSq (spinFlipForm ψ) * Real.sqrt (Complex.normSq (spinFlipForm ψ))
      ≤ sexticF ψ) :
    ((-tsB q - 17 * tsA q / 12) / 2 + tsA q / 16) * blochSq ψ
      + ((-tsB q - 17 * tsA q / 12) / 2) * Complex.normSq (spinFlipForm ψ)
      + tsA q / 12 * (Complex.normSq (spinFlipForm ψ)
          - Complex.normSq (spinFlipForm ψ) * Real.sqrt (Complex.normSq (spinFlipForm ψ)))
    ≤ 3 * (tsallisCeiling q - meanTsallis q ψ) := by
  obtain ⟨-, ha⟩ := tsallis_hermite h0 h2 h1
  have hb := tsallis_coeff_neg h0 h2 h1
  have := majorant_stability_of_envelope (tsallis_majorant h0 h2 h1) ha.le hb.le ψ hψ henv
  rw [meanTsallis_eq_meanSpec q ψ hψ, tsallisCeiling_eq, ← meanSpec_M4]
  exact this

/-- info: 'FormalResearch.FourQubitEntropy.majorant_stability_of_envelope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms majorant_stability_of_envelope

/-- info: 'FormalResearch.FourQubitEntropy.entropy_stability_of_envelope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms entropy_stability_of_envelope

/-- info: 'FormalResearch.FourQubitEntropy.tsallis_stability_of_envelope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms tsallis_stability_of_envelope

end FormalResearch.FourQubitEntropy
