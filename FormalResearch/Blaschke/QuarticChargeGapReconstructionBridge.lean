import FormalResearch.Blaschke.QuarticChargeGapAlgebra

namespace FormalResearch.Blaschke

/-!
# Quartic charge-gap reconstruction bridge

This module matches the scalar factorization promoted in
`cmbant/QIprojects` at source commit
`9389c39c10dd15db6ac9a47087d0118142e70630`, specifically
`Blaschke/notes/quartic_charge_gap_closure_2026-09-09.md`.

It deliberately does **not** formalize the exact CAS reconstruction of the
raw charge invariants, the Bessel/Gram input, the Schur-domain input, Möbius
normalization, or the confluent-continuity argument.  Instead, the exact raw
reconstruction equality is an explicit hypothesis.  Lean then checks the
remaining scalar-prefactor sign, the already-formalized `F1/F2/F3` sign
chain, and the final unsquaring step.
-/

/-- The squared polynomial factor `G` in the reconstructed quartic
charge-gap prefactor. -/
def quarticG (t q : ℝ) : ℝ :=
  q ^ 2 * t - 2 * q * t ^ 2 - 2 * q + 3 * t

/-- The denominator factor `Delta` in the reconstructed quartic charge-gap
identity.  Here `x = Re s` and `y = Im s` are the normalized critical
coordinates from the source proof. -/
def quarticDelta (t x y : ℝ) : ℝ :=
  (1 - t ^ 2) ^ 2 - (1 - t) ^ 2 * x ^ 2 - (1 + t) ^ 2 * y ^ 2

/-- Scalar prefactor in the exact raw quartic squared-gap reconstruction.
The source identity is supplied only on its valid normalized simple-critical
locus; in the bridge theorem below that identity is kept as an explicit
hypothesis. -/
noncomputable def quarticRawPrefactor (t q x y : ℝ) : ℝ :=
  -(4 * t ^ 3 * (3 - q * t) ^ 2 * (quarticG t q) ^ 2 /
      (q ^ 6 * (1 + t) ^ 6 * (quarticLp t q) ^ 3 *
        (quarticDelta t x y) ^ 2))

/-- On the physical scalar domain, the reconstructed raw prefactor is
nonpositive.  The only sign-sensitive denominator factor is `L_+`; its
positivity was already formalized in `QuarticChargeGapAlgebra`. -/
theorem quarticRawPrefactor_nonpos
    {t q x y : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hq0 : 0 < q)
    (heps : 0 ≤ quarticEpsilon t q) :
    quarticRawPrefactor t q x y ≤ 0 := by
  have hLp : 0 < quarticLp t q := quarticLp_pos ht0 ht1 heps
  unfold quarticRawPrefactor
  apply neg_nonpos.mpr
  positivity

/-- Once the exact raw reconstruction equality is supplied, the physical
quartic sign conditions force the squared charge-gap defect to be
nonnegative.  This is the formal bridge from the source-side reconstruction
certificate to the existing Lean sign algebra. -/
theorem quartic_squared_defect_nonneg_of_raw_factorization
    {t q U V x y mu1 mu2 : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hq0 : 0 < q)
    (heps : 0 ≤ quarticEpsilon t q)
    (hU0 : 0 ≤ U) (hV0 : 0 ≤ V)
    (hUschur : U < (1 + q) ^ 2)
    (hconic : quarticCriticalConic t q U V)
    (hreconstruction :
      (mu1 ^ 2 + mu2 ^ 2 - (1 : ℝ) / 4) ^ 2 -
          4 * mu1 ^ 2 * mu2 ^ 2 =
        quarticRawPrefactor t q x y * quarticF1 t q U *
          quarticF2 t q U * quarticF3 t q U) :
    0 ≤ (mu1 ^ 2 + mu2 ^ 2 - (1 : ℝ) / 4) ^ 2 -
      4 * mu1 ^ 2 * mu2 ^ 2 := by
  have hpref : quarticRawPrefactor t q x y ≤ 0 :=
    quarticRawPrefactor_nonpos ht0 ht1 hq0 heps
  have h1 : quarticF1 t q U ≤ 0 := quarticF1_nonpos hU0 heps
  have h2 : 0 < quarticF2 t q U := quarticF2_pos ht0 ht1 hq0 hUschur
  have h3 : 0 ≤ quarticF3 t q U :=
    quarticF3_nonneg ht0 ht1 hq0 heps hV0 hconic
  rw [hreconstruction]
  have hprefF1 :
      0 ≤ quarticRawPrefactor t q x y * quarticF1 t q U :=
    mul_nonneg_of_nonpos_of_nonpos hpref h1
  exact mul_nonneg (mul_nonneg hprefF1 h2.le) h3

/-- Conditional simple-critical quartic charge gap matching the newly closed
source proof: the raw CAS reconstruction equality and analytic hypotheses are
visible assumptions, while all downstream scalar sign and unsquaring steps
are discharged in Lean. -/
theorem quartic_charge_gap_of_raw_factorization
    {t q U V x y mu1 mu2 : ℝ}
    (hmu2 : 0 ≤ mu2) (horder : mu2 ≤ mu1)
    (henergy : (5 : ℝ) / 4 ≤ 2 * (mu1 ^ 2 + mu2 ^ 2))
    (ht0 : 0 < t) (ht1 : t < 1) (hq0 : 0 < q)
    (heps : 0 ≤ quarticEpsilon t q)
    (hU0 : 0 ≤ U) (hV0 : 0 ≤ V)
    (hUschur : U < (1 + q) ^ 2)
    (hconic : quarticCriticalConic t q U V)
    (hreconstruction :
      (mu1 ^ 2 + mu2 ^ 2 - (1 : ℝ) / 4) ^ 2 -
          4 * mu1 ^ 2 * mu2 ^ 2 =
        quarticRawPrefactor t q x y * quarticF1 t q U *
          quarticF2 t q U * quarticF3 t q U) :
    (1 : ℝ) / 2 ≤ mu1 - mu2 := by
  apply quartic_charge_gap_of_energy_and_squared_defect hmu2 horder henergy
  exact quartic_squared_defect_nonneg_of_raw_factorization
    ht0 ht1 hq0 heps hU0 hV0 hUschur hconic hreconstruction

end FormalResearch.Blaschke
