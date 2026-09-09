import Mathlib

namespace FormalResearch.QID

/-!
# QI-D E6/F4 A2 phase-envelope quartic reduction

Source authority:
`cmbant/QIprojects:QI-D/code/certify_E6_A2_phase_envelope.py`, audited at
QIprojects main `acfb127df5cc5998fb91cd00ea6e5311d1462e39`.

T33 reduces the fixed-endpoint middle `A2` phase problem to

`H(u,v) = c0 + 2 Re(a*u + b*v + c*u*v)`.

After eliminating one phase, the remaining unit-circle defect is

`q(u) = (d - Re(a*u))^2 - |b + c*u|^2`,

with `d=(target-c0)/2`.  Under the tangent-half-angle parameter
`u=(1+i*t)/(1-i*t)`, this module checks the exact rational algebra:

* the `A2` phase map has determinant `3` and the displayed inverse;
* the trigonometric numerators and source `D`, `Rnum` formulas agree exactly;
* clearing the positive denominator `(1+t^2)^2` gives a quartic `Q(t)`;
* `q(t) >= 0` is equivalent to `Q(t) >= 0` for every finite rational `t`;
* the quartic coefficients and the separate `t=infinity` defect are exact;
* the source's positive equality regression and negative regression are exact.

The analytic maximization `max_v Re(z*v)=|z|`, the identification of the
coefficient tuple `(c0,a,b,c)` from genuine compact-F4 endpoints, and the
uniform positivity of the resulting quartics over that endpoint locus are not
proved here. In particular this module does **not** prove compact-E6
simultaneous Weyl convexity.
-/

abbrev E6A2Fin := Fin 2
abbrev E6A2Mat := Matrix E6A2Fin E6A2Fin ℚ

/-- Integer `A2` frequency map `(x,y) -> (2x-y,-x+2y)`. -/
def e6A2PhaseMap : E6A2Mat :=
  !![2, -1; -1, 2]

/-- Exact rational inverse of the `A2` phase map. -/
def e6A2PhaseMapInv : E6A2Mat :=
  !![2/3, 1/3; 1/3, 2/3]

/-- The phase map has determinant three and the displayed two-sided inverse. -/
theorem e6A2PhaseMap_certificate :
    e6A2PhaseMap.det = 3 ∧
      e6A2PhaseMap * e6A2PhaseMapInv = 1 ∧
      e6A2PhaseMapInv * e6A2PhaseMap = 1 := by
  native_decide

/-- Tangent-half-angle denominator. -/
def e6A2Den (t : ℚ) : ℚ := 1 + t^2

/-- Numerator of `cos(theta)=(1-t^2)/(1+t^2)`. -/
def e6A2CosNum (t : ℚ) : ℚ := 1 - t^2

/-- Numerator of `sin(theta)=2t/(1+t^2)`. -/
def e6A2SinNum (t : ℚ) : ℚ := 2*t

/-- Numerator of `Re(a e^{i theta})` for `a=ar+i ai`. -/
def e6A2AReNum (ar ai t : ℚ) : ℚ :=
  ar * e6A2CosNum t - ai * e6A2SinNum t

/-- Source numerator `D=(1+t^2)(d-Re(a e^{i theta}))`. -/
def e6A2D (ar ai d t : ℚ) : ℚ :=
  (d-ar) + 2*ai*t + (d+ar)*t^2

/-- Source numerator for `(1+t^2)|b+c e^{i theta}|^2`.
Here `b=br+i bi`, `c=cr+i ci`. -/
def e6A2Rnum (br bi cr ci t : ℚ) : ℚ :=
  (br^2 + bi^2 + cr^2 + ci^2) * (1+t^2)
    + 2*(br*cr + bi*ci)*(1-t^2)
    - 4*(br*ci - bi*cr)*t

/-- Exact real quartic obtained after clearing the tangent-half-angle denominator. -/
def e6A2Quartic (ar ai br bi cr ci d t : ℚ) : ℚ :=
  e6A2D ar ai d t ^ 2 - e6A2Den t * e6A2Rnum br bi cr ci t

/-- The tangent-half-angle denominator is strictly positive over `ℚ`. -/
theorem e6A2Den_pos (t : ℚ) : 0 < e6A2Den t := by
  unfold e6A2Den
  nlinarith [sq_nonneg t]

/-- Exact source identity for the first cleared numerator. -/
theorem e6A2D_from_trig_numerators (ar ai d t : ℚ) :
    e6A2D ar ai d t =
      d * e6A2Den t - e6A2AReNum ar ai t := by
  unfold e6A2D e6A2Den e6A2AReNum e6A2CosNum e6A2SinNum
  ring

/-- Rational unit-circle defect after the tangent-half-angle substitution. -/
def e6A2CircleDefect (ar ai br bi cr ci d t : ℚ) : ℚ :=
  (d - e6A2AReNum ar ai t / e6A2Den t)^2
    - e6A2Rnum br bi cr ci t / e6A2Den t

/-- Clearing `(1+t^2)^2` from the substituted circle defect gives exactly the
source quartic. -/
theorem e6A2CircleDefect_clear_denominators
    (ar ai br bi cr ci d t : ℚ) :
    e6A2Den t ^ 2 * e6A2CircleDefect ar ai br bi cr ci d t =
      e6A2Quartic ar ai br bi cr ci d t := by
  have h : (1 + t^2 : ℚ) ≠ 0 := by
    nlinarith [sq_nonneg t]
  field_simp [e6A2CircleDefect, e6A2Quartic, e6A2D, e6A2Den,
    e6A2AReNum, e6A2CosNum, e6A2SinNum, e6A2Rnum, h]
  <;> ring

/-- Because the cleared denominator is positive, finite-`t` nonnegativity of
the unit-circle defect is exactly quartic nonnegativity. -/
theorem e6A2CircleDefect_nonneg_iff_quartic_nonneg
    (ar ai br bi cr ci d t : ℚ) :
    0 ≤ e6A2CircleDefect ar ai br bi cr ci d t ↔
      0 ≤ e6A2Quartic ar ai br bi cr ci d t := by
  have hden : 0 < e6A2Den t ^ 2 := by
    have h := e6A2Den_pos t
    rw [pow_two]
    exact mul_pos h h
  have hclear := e6A2CircleDefect_clear_denominators ar ai br bi cr ci d t
  constructor
  · intro hq
    rw [← hclear]
    exact mul_nonneg (le_of_lt hden) hq
  · intro hQ
    have hprod : 0 ≤ e6A2Den t ^ 2 *
        e6A2CircleDefect ar ai br bi cr ci d t := by
      rw [hclear]
      exact hQ
    exact (mul_le_mul_left hden).mp (by simpa using hprod)

/-- Constant quartic coefficient. -/
def e6A2Q0 (ar ai br bi cr ci d : ℚ) : ℚ :=
  ar^2 - 2*ar*d - bi^2 - 2*bi*ci - br^2 - 2*br*cr - ci^2 - cr^2 + d^2

/-- Linear quartic coefficient. -/
def e6A2Q1 (ar ai br bi cr ci d : ℚ) : ℚ :=
  4*(-ai*ar + ai*d - bi*cr + br*ci)

/-- Quadratic quartic coefficient. -/
def e6A2Q2 (ar ai br bi cr ci d : ℚ) : ℚ :=
  2*(2*ai^2 - ar^2 - bi^2 - br^2 - ci^2 - cr^2 + d^2)

/-- Cubic quartic coefficient. -/
def e6A2Q3 (ar ai br bi cr ci d : ℚ) : ℚ :=
  4*(ai*ar + ai*d - bi*cr + br*ci)

/-- Quartic leading coefficient. -/
def e6A2Q4 (ar ai br bi cr ci d : ℚ) : ℚ :=
  ar^2 + 2*ar*d - bi^2 + 2*bi*ci - br^2 + 2*br*cr - ci^2 - cr^2 + d^2

/-- Exact coefficient expansion of the cleared defect. -/
theorem e6A2Quartic_coefficient_expansion
    (ar ai br bi cr ci d t : ℚ) :
    e6A2Quartic ar ai br bi cr ci d t =
      e6A2Q0 ar ai br bi cr ci d
      + e6A2Q1 ar ai br bi cr ci d * t
      + e6A2Q2 ar ai br bi cr ci d * t^2
      + e6A2Q3 ar ai br bi cr ci d * t^3
      + e6A2Q4 ar ai br bi cr ci d * t^4 := by
  unfold e6A2Quartic e6A2D e6A2Den e6A2Rnum
    e6A2Q0 e6A2Q1 e6A2Q2 e6A2Q3 e6A2Q4
  ring

/-- Separate `t=infinity` / `u=-1` defect from the source verifier. -/
def e6A2InfinityDefect (ar ai br bi cr ci d : ℚ) : ℚ :=
  (d+ar)^2 - ((br-cr)^2 + (bi-ci)^2)

/-- The infinity defect is exactly the quartic leading coefficient. -/
theorem e6A2Q4_eq_infinityDefect (ar ai br bi cr ci d : ℚ) :
    e6A2Q4 ar ai br bi cr ci d =
      e6A2InfinityDefect ar ai br bi cr ci d := by
  unfold e6A2Q4 e6A2InfinityDefect
  ring

/-- Source equality regression: `a=1/4`, `b=1/6`, `c=1/12`, `d=1/2`. -/
theorem e6A2EqualityRegression (t : ℚ) :
    e6A2Quartic (1/4) 0 (1/6) 0 (1/12) 0 (1/2) t =
      t^2 * (20*t^2 + 11) / 36 := by
  norm_num [e6A2Quartic, e6A2D, e6A2Den, e6A2Rnum]
  <;> ring

/-- The source equality regression is globally nonnegative for finite rational
`t`. -/
theorem e6A2EqualityRegression_nonneg (t : ℚ) :
    0 ≤ e6A2Quartic (1/4) 0 (1/6) 0 (1/12) 0 (1/2) t := by
  rw [e6A2EqualityRegression]
  positivity

/-- The source equality regression also has positive infinity defect `5/9`. -/
theorem e6A2EqualityRegression_infinity :
    e6A2InfinityDefect (1/4) 0 (1/6) 0 (1/12) 0 (1/2) = 5/9 := by
  norm_num [e6A2InfinityDefect]

/-- Source negative regression: lowering the target from `1` to `9/10` gives
`d=9/20` and a negative defect already at `t=0`. -/
theorem e6A2FailureRegression_at_zero :
    e6A2Quartic (1/4) 0 (1/6) 0 (1/12) 0 (9/20) 0 = -9/400 := by
  norm_num [e6A2Quartic, e6A2D, e6A2Den, e6A2Rnum]

/-- Therefore the lowered-target regression cannot be globally nonnegative. -/
theorem e6A2FailureRegression_negative :
    e6A2Quartic (1/4) 0 (1/6) 0 (1/12) 0 (9/20) 0 < 0 := by
  rw [e6A2FailureRegression_at_zero]
  norm_num

end FormalResearch.QID
