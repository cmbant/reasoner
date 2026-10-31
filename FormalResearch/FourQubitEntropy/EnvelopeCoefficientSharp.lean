import FormalResearch.FourQubitEntropy.Checks
import FormalResearch.FourQubitEntropy.GeneralEnvelope

/-!
# Optimality of the coefficient `7/8` in the general envelope

Paper: `thm:fqe-general-envelope` (sextic_identity.tex, section "The general envelope"), the remark
that the coefficient `7/8` of the added `W₁` term is optimal (check tag ESH,
`code/verify_envelope_coefficient_sharp.py`).

On the GHZ family `z = c|0000⟩ + s|1111⟩` (`c, s` real, `c² + s² = 1`), with `τ = 4c²s²`, one has
`W₁ = 4(1 - τ)` and `F = 3 + 3τ/2` (`ghz_tau`, `ghz_blochSq_unit`, `ghz_sexticF`, computed from the
definitions of `Statement.lean`), so the envelope inequality with `7/8` replaced by `C` leaves the
slack `(7/2 - 4C) τ + (1 + 4C) τ^{3/2}` (`ghz_slack`), negative for small `τ > 0` as soon as `C > 7/8`
(`general_envelope_coeff_sharp`).
-/

open scoped ComplexConjugate Matrix

namespace FormalResearch.FourQubitEntropy

/-- The GHZ family `c|0000⟩ + s|1111⟩`. -/
noncomputable def ghzState (c s : ℝ) : Psi := fun a b d e =>
  if a = 0 ∧ b = 0 ∧ d = 0 ∧ e = 0 then (c : ℂ) else
  if a = 1 ∧ b = 1 ∧ d = 1 ∧ e = 1 then (s : ℂ) else 0

theorem ghz_normSq (c s : ℝ) : normSqPsi (ghzState c s) = c ^ 2 + s ^ 2 := by
  simp [normSqPsi, ghzState, Fin.sum_univ_two, Complex.normSq_apply]
  ring

theorem ghz_spinFlipForm (c s : ℝ) : spinFlipForm (ghzState c s) = ((2 * c * s : ℝ) : ℂ) := by
  simp [spinFlipForm, sum4, sum2, lit, sgn, ghzState, RingOps.ofInt]
  ring

theorem ghz_purity (c s : ℝ) : purity (ghzState c s) = 3 * (c ^ 4 + s ^ 4) := by
  simp [purity, red12, red13, red14, ghzState, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
    Fintype.sum_prod_type]
  ring

theorem ghz_cubic (c s : ℝ) : cubicMoment (ghzState c s) = 3 * (c ^ 6 + s ^ 6) := by
  simp [cubicMoment, red12, red13, red14, ghzState, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
    Fintype.sum_prod_type]
  ring

theorem ghz_blochSq (c s : ℝ) : blochSq (ghzState c s) = 4 * (c ^ 2 - s ^ 2) ^ 2 := by
  simp [blochSq, expectation, actOn, ghzState, pauliX, pauliY, pauliZ, Fin.sum_univ_two,
    Fin.sum_univ_four]
  ring

/-- On the unit GHZ family, `F = 3 + 3τ/2` with `τ = 4c²s²`. -/
theorem ghz_sexticF {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    sexticF (ghzState c s) = 3 + 3 / 2 * (4 * c ^ 2 * s ^ 2) := by
  unfold sexticF
  rw [ghz_normSq, ghz_purity, ghz_cubic, h]
  have h4 : c ^ 4 + s ^ 4 = 1 - 2 * c ^ 2 * s ^ 2 := by nlinarith [h]
  have h6 : c ^ 6 + s ^ 6 = 1 - 3 * c ^ 2 * s ^ 2 := by
    have : c ^ 6 + s ^ 6 = (c ^ 2 + s ^ 2) ^ 3 - 3 * c ^ 2 * s ^ 2 * (c ^ 2 + s ^ 2) := by ring
    rw [this, h]; ring
  rw [h4, h6]; ring

/-- `τ = |ψᵀ ε^{⊗4} ψ|² = 4c²s²` on the GHZ family. -/
theorem ghz_tau (c s : ℝ) : Complex.normSq (spinFlipForm (ghzState c s)) = 4 * c ^ 2 * s ^ 2 := by
  rw [ghz_spinFlipForm, Complex.normSq_ofReal]; ring

/-- `W₁ = 4(1 - τ)` on the unit GHZ family. -/
theorem ghz_blochSq_unit {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    blochSq (ghzState c s) = 4 * (1 - 4 * c ^ 2 * s ^ 2) := by
  rw [ghz_blochSq]
  have : (c ^ 2 - s ^ 2) ^ 2 = (c ^ 2 + s ^ 2) ^ 2 - 4 * c ^ 2 * s ^ 2 := by ring
  rw [this, h]; ring

/-- The slack of the envelope with coefficient `C`, on the unit GHZ family with `r = √τ = 2cs ≥ 0`:
`F - (3/4 + C τ/(1+√τ)) W₁ - τ + τ^{3/2} = (7/2 - 4C) τ + (1 + 4C) τ^{3/2}`. -/
theorem ghz_slack {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) (hr : 0 ≤ 2 * c * s) (C : ℝ) :
    sexticF (ghzState c s)
        - ((3 / 4 + C * Complex.normSq (spinFlipForm (ghzState c s))
              / (1 + Real.sqrt (Complex.normSq (spinFlipForm (ghzState c s)))))
            * blochSq (ghzState c s)
          + Complex.normSq (spinFlipForm (ghzState c s))
          - Complex.normSq (spinFlipForm (ghzState c s))
            * Real.sqrt (Complex.normSq (spinFlipForm (ghzState c s))))
      = (7 / 2 - 4 * C) * (2 * c * s) ^ 2 + (1 + 4 * C) * (2 * c * s) ^ 3 := by
  have hτ : Complex.normSq (spinFlipForm (ghzState c s)) = (2 * c * s) ^ 2 := by
    rw [ghz_tau]; ring
  have hsq : Real.sqrt (Complex.normSq (spinFlipForm (ghzState c s))) = 2 * c * s := by
    rw [hτ]; exact Real.sqrt_sq hr
  rw [hsq, hτ, ghz_sexticF h, ghz_blochSq_unit h]
  have h1 : 0 < 1 + 2 * c * s := by linarith
  have e : (4 * c ^ 2 * s ^ 2) = (2 * c * s) ^ 2 := by ring
  rw [e]
  field_simp
  ring

/-- **`thm:fqe-general-envelope`, optimality of the coefficient `7/8` (check tag ESH).**
For every `C > 7/8` there is a unit four-qubit state (on the GHZ family `c|0000⟩ + s|1111⟩`, with small
`τ = 4c²s²`) violating the envelope inequality with `7/8` replaced by `C`:
`F < (3/4 + C τ/(1 + √τ)) W₁ + τ - τ^{3/2}`. Formalised with `F = sexticF`, `W₁ = blochSq` and
`τ = normSq (spinFlipForm ψ)`; the exact values `τ = 4c²s²`, `W₁ = 4(1-τ)`, `F = 3 + 3τ/2` on the
family are `ghz_tau`, `ghz_blochSq_unit`, `ghz_sexticF`; the companion statement that the coefficient
`7/8` itself is admissible is `general_envelope_unit`. -/
theorem general_envelope_coeff_sharp {C : ℝ} (hC : 7 / 8 < C) :
    ∃ ψ : Psi, normSqPsi ψ = 1 ∧
      sexticF ψ < (3 / 4 + C * Complex.normSq (spinFlipForm ψ)
              / (1 + Real.sqrt (Complex.normSq (spinFlipForm ψ)))) * blochSq ψ
          + Complex.normSq (spinFlipForm ψ)
          - Complex.normSq (spinFlipForm ψ) * Real.sqrt (Complex.normSq (spinFlipForm ψ)) := by
  -- `r = 2cs` with `r (1 + 4C) < 4C - 7/2`
  set r : ℝ := (4 * C - 7 / 2) / (2 * (1 + 4 * C)) with hr
  have hd : 0 < 1 + 4 * C := by linarith
  have hr0 : 0 < r := by rw [hr]; apply div_pos <;> linarith
  have hr1 : r < 1 := by
    rw [hr, div_lt_one (by linarith)]; linarith
  have hrr : r * (1 + 4 * C) < 4 * C - 7 / 2 := by
    rw [hr, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
  -- `c = (√(1+r) + √(1-r))/2`, `s = (√(1+r) - √(1-r))/2`
  set p := Real.sqrt (1 + r) with hp
  set m := Real.sqrt (1 - r) with hm
  have hp2 : p ^ 2 = 1 + r := Real.sq_sqrt (by linarith)
  have hm2 : m ^ 2 = 1 - r := Real.sq_sqrt (by linarith)
  have hpm : p * m ≥ 0 := by positivity
  have hcs : (p + m) ^ 2 / 4 + (p - m) ^ 2 / 4 = 1 := by nlinarith
  have hrcs : 2 * ((p + m) / 2) * ((p - m) / 2) = r := by nlinarith
  refine ⟨ghzState ((p + m) / 2) ((p - m) / 2), ?_, ?_⟩
  · rw [ghz_normSq]; nlinarith
  · have h1 : ((p + m) / 2) ^ 2 + ((p - m) / 2) ^ 2 = 1 := by nlinarith
    have := ghz_slack h1 (by rw [hrcs]; exact hr0.le) C
    rw [hrcs] at this
    have hneg : (7 / 2 - 4 * C) * r ^ 2 + (1 + 4 * C) * r ^ 3 < 0 := by
      have : r ^ 2 * ((1 + 4 * C) * r + (7 / 2 - 4 * C)) < 0 :=
        mul_neg_of_pos_of_neg (by positivity) (by nlinarith)
      nlinarith
    linarith

/-- **`thm:fqe-general-envelope`, the coefficient `7/8` is the largest admissible one.** For `C : ℝ`,
the envelope inequality `F ≥ (3/4 + C τ/(1+√τ)) W₁ + τ - τ^{3/2}` holds for every unit state if and only
if `C ≤ 7/8`. (`C ≤ 7/8` follows from `general_envelope_unit` and `W₁ ≥ 0`.) -/
theorem general_envelope_coeff_iff (C : ℝ) :
    (∀ ψ : Psi, normSqPsi ψ = 1 →
      (3 / 4 + C * Complex.normSq (spinFlipForm ψ)
              / (1 + Real.sqrt (Complex.normSq (spinFlipForm ψ)))) * blochSq ψ
          + Complex.normSq (spinFlipForm ψ)
          - Complex.normSq (spinFlipForm ψ) * Real.sqrt (Complex.normSq (spinFlipForm ψ))
        ≤ sexticF ψ) ↔ C ≤ 7 / 8 := by
  constructor
  · intro h
    by_contra hC
    push Not at hC
    obtain ⟨ψ, hψ, hlt⟩ := general_envelope_coeff_sharp hC
    exact absurd (h ψ hψ) (not_le.mpr hlt)
  · intro hC ψ hψ
    have h := general_envelope_unit ψ hψ
    have hW := blochSq_nonneg ψ
    have hτ := Complex.normSq_nonneg (spinFlipForm ψ)
    have hd : 0 < 1 + Real.sqrt (Complex.normSq (spinFlipForm ψ)) := by positivity
    have h1 : C * Complex.normSq (spinFlipForm ψ) / (1 + Real.sqrt (Complex.normSq (spinFlipForm ψ)))
        ≤ 7 * Complex.normSq (spinFlipForm ψ)
          / (8 * (1 + Real.sqrt (Complex.normSq (spinFlipForm ψ)))) := by
      rw [show 7 * Complex.normSq (spinFlipForm ψ)
          / (8 * (1 + Real.sqrt (Complex.normSq (spinFlipForm ψ))))
          = (7 / 8) * Complex.normSq (spinFlipForm ψ)
            / (1 + Real.sqrt (Complex.normSq (spinFlipForm ψ))) by field_simp]
      exact div_le_div_of_nonneg_right (by nlinarith) hd.le
    nlinarith [mul_le_mul_of_nonneg_right h1 hW]

end FormalResearch.FourQubitEntropy
