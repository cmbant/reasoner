import Mathlib
import FormalResearch.Blaschke.CompositionBaseline

namespace FormalResearch.Blaschke

/-- The normalized quartic domain defect used in the v13 Blaschke--Virasoro
charge-gap calculation. -/
def quarticEpsilon (t q : ℝ) : ℝ := 2 * t - q * (1 + t ^ 2)

/-- First denominator polynomial in the normalized quartic critical chart. -/
def quarticLm (t q : ℝ) : ℝ :=
  t * (q + 3) ^ 2 - 4 * q * (t + 1) ^ 2

/-- Second denominator polynomial in the normalized quartic critical chart. -/
def quarticLp (t q : ℝ) : ℝ :=
  t * (q - 3) ^ 2 - 4 * q * (t - 1) ^ 2

/-- First sign-sensitive factor in the v13 quartic charge-gap reduction. Here
`U` is the square of the real part of the normalized numerator parameter `p`,
not the square of the real part of the critical parameter `s`. -/
def quarticF1 (t q U : ℝ) : ℝ :=
  -t ^ 2 * U - (1 + t) ^ 2 * quarticEpsilon t q

/-- Second sign-sensitive factor in the v13 quartic charge-gap reduction. -/
def quarticF2 (t q U : ℝ) : ℝ :=
  (1 + q) ^ 2 * (1 + t) ^ 2 - 4 * t * U

/-- Third sign-sensitive factor in the v13 quartic charge-gap reduction. -/
def quarticF3 (t q U : ℝ) : ℝ :=
  q * (1 + t) ^ 2 * (q - t ^ 2 - 2 * t) ^ 2 -
    t ^ 2 * (q - 3 * t) ^ 2 * U

/-- Polynomial form of the exact critical conic after using
`U = (Re p)^2` and `V = (Im p)^2`. Keeping the conic polynomial avoids
introducing divisions by chart denominators. -/
def quarticCriticalConic (t q U V : ℝ) : Prop :=
  t * (1 - t) ^ 2 * quarticLm t q * U +
      t * (1 + t) ^ 2 * quarticLp t q * V =
    4 * q * (1 - t ^ 2) ^ 2 * quarticEpsilon t q

/-- Exact re-expression of `L_-` in terms of the domain defect
`epsilon = 2t-q(1+t^2)`. -/
theorem quarticLm_epsilon_identity (t q : ℝ) :
    (1 + t ^ 2) ^ 2 * quarticLm t q =
      t * (1 - t) ^ 4 +
      quarticEpsilon t q *
        (4 * t ^ 4 + 2 * t ^ 3 + 4 * t ^ 2 + 2 * t + 4) +
      t * (quarticEpsilon t q) ^ 2 := by
  simp [quarticLm, quarticEpsilon]
  ring

/-- Exact re-expression of `L_+` in terms of the same domain defect. -/
theorem quarticLp_epsilon_identity (t q : ℝ) :
    (1 + t ^ 2) ^ 2 * quarticLp t q =
      t * (1 + t) ^ 4 +
      quarticEpsilon t q *
        (4 * t ^ 4 - 2 * t ^ 3 + 4 * t ^ 2 - 2 * t + 4) +
      t * (quarticEpsilon t q) ^ 2 := by
  simp [quarticLp, quarticEpsilon]
  ring

/-- Arithmetic identity behind the two-vector Gram/Bessel reduction. The
model-space Bessel inequality supplying nonnegativity is an external analytic
input, not hidden in this theorem. -/
theorem quartic_bessel_reduction_identity
    {t q : ℝ} (ht : t ≠ 0) :
    (1 - q ^ 2) - (q * t / 2 + q / (2 * t) - q ^ 2) =
      quarticEpsilon t q / (2 * t) := by
  simp [quarticEpsilon]
  field_simp [ht]
  ring

/-- On the physical quartic domain, `L_-` is strictly positive. -/
theorem quarticLm_pos
    {t q : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (heps : 0 ≤ quarticEpsilon t q) :
    0 < quarticLm t q := by
  have hbase : 0 < t * (1 - t) ^ 4 := by positivity
  have hcoef :
      0 < 4 * t ^ 4 + 2 * t ^ 3 + 4 * t ^ 2 + 2 * t + 4 := by
    positivity
  have hrhs :
      0 < t * (1 - t) ^ 4 +
          quarticEpsilon t q *
            (4 * t ^ 4 + 2 * t ^ 3 + 4 * t ^ 2 + 2 * t + 4) +
          t * (quarticEpsilon t q) ^ 2 := by
    have h1 :
        0 ≤ quarticEpsilon t q *
          (4 * t ^ 4 + 2 * t ^ 3 + 4 * t ^ 2 + 2 * t + 4) :=
      mul_nonneg heps hcoef.le
    have h2 : 0 ≤ t * (quarticEpsilon t q) ^ 2 := by positivity
    linarith
  have hlhs : 0 < (1 + t ^ 2) ^ 2 * quarticLm t q := by
    rw [quarticLm_epsilon_identity]
    exact hrhs
  by_contra h
  have hnonpos : quarticLm t q ≤ 0 := le_of_not_gt h
  have hfac : 0 ≤ (1 + t ^ 2) ^ 2 := by positivity
  have : (1 + t ^ 2) ^ 2 * quarticLm t q ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hfac hnonpos
  linarith

/-- On the same physical domain, `L_+` is strictly positive. -/
theorem quarticLp_pos
    {t q : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (heps : 0 ≤ quarticEpsilon t q) :
    0 < quarticLp t q := by
  have htwo : 0 < 2 - t := by linarith
  have hcoef :
      0 < 4 * t ^ 4 - 2 * t ^ 3 + 4 * t ^ 2 - 2 * t + 4 := by
    rw [show
      4 * t ^ 4 - 2 * t ^ 3 + 4 * t ^ 2 - 2 * t + 4 =
        4 * t ^ 4 + 2 * t ^ 2 * (2 - t) + 2 * (2 - t) by ring]
    positivity
  have hbase : 0 < t * (1 + t) ^ 4 := by positivity
  have hrhs :
      0 < t * (1 + t) ^ 4 +
          quarticEpsilon t q *
            (4 * t ^ 4 - 2 * t ^ 3 + 4 * t ^ 2 - 2 * t + 4) +
          t * (quarticEpsilon t q) ^ 2 := by
    have h1 :
        0 ≤ quarticEpsilon t q *
          (4 * t ^ 4 - 2 * t ^ 3 + 4 * t ^ 2 - 2 * t + 4) :=
      mul_nonneg heps hcoef.le
    have h2 : 0 ≤ t * (quarticEpsilon t q) ^ 2 := by positivity
    linarith
  have hlhs : 0 < (1 + t ^ 2) ^ 2 * quarticLp t q := by
    rw [quarticLp_epsilon_identity]
    exact hrhs
  by_contra h
  have hnonpos : quarticLp t q ≤ 0 := le_of_not_gt h
  have hfac : 0 ≤ (1 + t ^ 2) ^ 2 := by positivity
  have : (1 + t ^ 2) ^ 2 * quarticLp t q ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hfac hnonpos
  linarith

/-- The first factor has the required nonpositive sign. -/
theorem quarticF1_nonpos
    {t q U : ℝ} (hU : 0 ≤ U) (heps : 0 ≤ quarticEpsilon t q) :
    quarticF1 t q U ≤ 0 := by
  have h1 : 0 ≤ t ^ 2 * U := mul_nonneg (sq_nonneg t) hU
  have h2 : 0 ≤ (1 + t) ^ 2 * quarticEpsilon t q :=
    mul_nonneg (sq_nonneg (1 + t)) heps
  simp [quarticF1]
  linarith

/-- The Schur-ellipse consequence `U < (1+q)^2` gives strict positivity of the
second factor. -/
theorem quarticF2_pos
    {t q U : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hq0 : 0 < q)
    (hU : U < (1 + q) ^ 2) :
    0 < quarticF2 t q U := by
  have honeq : 0 < (1 + q) ^ 2 := by positivity
  have h4t : 4 * t < (1 + t) ^ 2 := by
    have hs : 0 < (1 - t) ^ 2 := by positivity
    nlinarith
  have hA : 4 * t * U < 4 * t * (1 + q) ^ 2 := by
    exact mul_lt_mul_of_pos_left hU (by positivity)
  have hB : 4 * t * (1 + q) ^ 2 < (1 + t) ^ 2 * (1 + q) ^ 2 := by
    exact mul_lt_mul_of_pos_right h4t honeq
  simp [quarticF2]
  nlinarith

/-- Exact denominator-free `F3` reduction on the quartic critical conic. -/
theorem quarticF3_conic_identity
    {t q U V : ℝ} (hconic : quarticCriticalConic t q U V) :
    (1 - t) ^ 2 * quarticLm t q * quarticF3 t q U =
      (1 + t) ^ 2 * quarticLp t q *
        (q * (1 - t) ^ 2 * (q + t ^ 2 - 2 * t) ^ 2 +
          t ^ 2 * (q - 3 * t) ^ 2 * V) := by
  have hpoly :
      (1 - t) ^ 2 * quarticLm t q * quarticF3 t q U =
        (1 + t) ^ 2 * quarticLp t q *
            (q * (1 - t) ^ 2 * (q + t ^ 2 - 2 * t) ^ 2 +
              t ^ 2 * (q - 3 * t) ^ 2 * V) -
          t * (q - 3 * t) ^ 2 *
            (t * (1 - t) ^ 2 * quarticLm t q * U +
              t * (1 + t) ^ 2 * quarticLp t q * V -
              4 * q * (1 - t ^ 2) ^ 2 * quarticEpsilon t q) := by
    simp [quarticLm, quarticLp, quarticF3, quarticEpsilon]
    ring
  rw [hpoly]
  have hc := hconic
  simp [quarticCriticalConic] at hc
  rw [hc]
  ring

/-- The third factor is nonnegative on the physical critical conic. -/
theorem quarticF3_nonneg
    {t q U V : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hq0 : 0 < q)
    (heps : 0 ≤ quarticEpsilon t q) (hV : 0 ≤ V)
    (hconic : quarticCriticalConic t q U V) :
    0 ≤ quarticF3 t q U := by
  have hLm := quarticLm_pos ht0 ht1 heps
  have hLp := quarticLp_pos ht0 ht1 heps
  have hid := quarticF3_conic_identity hconic
  have hbracket :
      0 ≤ q * (1 - t) ^ 2 * (q + t ^ 2 - 2 * t) ^ 2 +
        t ^ 2 * (q - 3 * t) ^ 2 * V := by
    positivity
  have hrhs :
      0 ≤ (1 + t) ^ 2 * quarticLp t q *
        (q * (1 - t) ^ 2 * (q + t ^ 2 - 2 * t) ^ 2 +
          t ^ 2 * (q - 3 * t) ^ 2 * V) := by
    positivity
  have hmul : 0 ≤ (1 - t) ^ 2 * quarticLm t q * quarticF3 t q U := by
    rw [hid]
    exact hrhs
  have hfac : 0 < (1 - t) ^ 2 * quarticLm t q := by positivity
  by_contra h
  have hneg : quarticF3 t q U < 0 := lt_of_not_ge h
  have hprodneg :
      (1 - t) ^ 2 * quarticLm t q * quarticF3 t q U < 0 :=
    mul_neg_of_pos_of_neg hfac hneg
  linarith

/-- Combined downstream sign certificate for the three factors. -/
theorem quartic_factor_product_nonneg
    {t q U V : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hq0 : 0 < q)
    (heps : 0 ≤ quarticEpsilon t q) (hU0 : 0 ≤ U) (hV0 : 0 ≤ V)
    (hUschur : U < (1 + q) ^ 2)
    (hconic : quarticCriticalConic t q U V) :
    0 ≤ (-quarticF1 t q U) * quarticF2 t q U * quarticF3 t q U := by
  have h1 := quarticF1_nonpos hU0 heps
  have h2 := quarticF2_pos ht0 ht1 hq0 hUschur
  have h3 := quarticF3_nonneg ht0 ht1 hq0 heps hV0 hconic
  have hm1 : 0 ≤ -quarticF1 t q U := neg_nonneg.mpr h1
  exact mul_nonneg (mul_nonneg hm1 h2.le) h3

/-- The squared charge-gap defect factors into the two squared sum/difference
gaps. -/
theorem chargeGap_squared_defect_factorization (mu1 mu2 : ℝ) :
    (mu1 ^ 2 + mu2 ^ 2 - (1 : ℝ) / 4) ^ 2 -
        4 * mu1 ^ 2 * mu2 ^ 2 =
      ((mu1 - mu2) ^ 2 - (1 : ℝ) / 4) *
        ((mu1 + mu2) ^ 2 - (1 : ℝ) / 4) := by
  ring

/-- Unsquaring lemma after the raw squared-defect calculation. The energy
lower bound `5/4 <= 2(mu1^2+mu2^2)` is the degree-four Gate-A input. -/
theorem quartic_charge_gap_of_energy_and_squared_defect
    {mu1 mu2 : ℝ} (hmu2 : 0 ≤ mu2) (horder : mu2 ≤ mu1)
    (henergy : (5 : ℝ) / 4 ≤ 2 * (mu1 ^ 2 + mu2 ^ 2))
    (hdefect :
      0 ≤ (mu1 ^ 2 + mu2 ^ 2 - (1 : ℝ) / 4) ^ 2 -
        4 * mu1 ^ 2 * mu2 ^ 2) :
    (1 : ℝ) / 2 ≤ mu1 - mu2 := by
  have hmu1 : 0 ≤ mu1 := le_trans hmu2 horder
  have hsum : (5 : ℝ) / 8 ≤ mu1 ^ 2 + mu2 ^ 2 := by linarith
  rw [chargeGap_squared_defect_factorization] at hdefect
  have hsecond : 0 < (mu1 + mu2) ^ 2 - (1 : ℝ) / 4 := by
    have hp : 0 ≤ mu1 * mu2 := mul_nonneg hmu1 hmu2
    nlinarith
  have hfirst : 0 ≤ (mu1 - mu2) ^ 2 - (1 : ℝ) / 4 := by
    by_contra h
    have hneg : (mu1 - mu2) ^ 2 - (1 : ℝ) / 4 < 0 := lt_of_not_ge h
    have hpneg :
        ((mu1 - mu2) ^ 2 - (1 : ℝ) / 4) *
          ((mu1 + mu2) ^ 2 - (1 : ℝ) / 4) < 0 :=
      mul_neg_of_neg_of_pos hneg hsecond
    linarith
  nlinarith

/-- Exact rational degree-four Gate-A baseline used by the unsquaring lemma. -/
theorem quartic_gateA_baseline : gateABaseline 4 = (5 : ℚ) / 4 := by
  norm_num [gateABaseline]

end FormalResearch.Blaschke
