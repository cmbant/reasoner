module

public import FormalResearch.SignUncertainty.HankelLangerSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

open Finset Filter Topology
open scoped Real

/-!
# The Langer series identity for the Hankel chart (`lem:langer-chart`, (0), series part)

Continues `HankelLangerSeries` (coefficients `etaC j = η_D(2j+2)`). Proved here, all in Lean:

* `csc_hasSum`: for `0 < ‖z‖ < 1`, `π / sin (π z) - 1/z = ∑_{n≥0} 2(-1)^n z/((n+1)² - z²)`, from
  Mathlib's Mittag-Leffler expansion `cot_series_rep'` at `z/2` and `z`, the identity
  `cot b - cot 2b = 1/sin 2b`, and the even/odd splitting of the alternating sum.
* `eta_hasSum`: for `0 < ‖z‖ < 1`, `HasSum (fun j => 2 * etaC j * z^(2j+1)) (π/sin(πz) - 1/z)`,
  from the double series `etaH` (geometric in `n`, `etaC` in `j`) by swapping the sums.
* `langer_eta_identity`: the tsum form `π/sin(πz) - 1/z = 2 ∑' etaC j z^(2j+1)`.
* `Pser`, `Pser_hasDerivAt`: the power series `P(z) = ∑ etaC j/(j+1) z^(2j+2)` and its derivative
  on `‖z‖ < 1/2`.
* `langer_g_hasSum`, `langer_g_eq_tsum`, `langer_g_hasDerivAt`: for `‖z‖ < 1/8`,
  `log (tan (π z/2)/(π z/2)) = P(z)` (so `g 0 = 0`, as `Complex.log 0 = 0`), its HasSum form, and
  `HasDerivAt g (2 ∑' etaC j z^(2j+1)) z`. The restriction `‖z‖ < 1/8` is a proof device
  (the segment argument on `(0,2)` needs `‖2z‖ < 1/4`); the principal branch is used.

The argument that `u(z) = tan(πz/2)/(πz/2)` equals `exp P(z)`: `φ(t) = u(tz) exp(-P(tz))` has zero
derivative on `(0,2)` (because `u'/u = π/sin - 1/z = P'`), tends to `1` at `0⁺` (from
`tan_div_sub_one_norm_le`, `‖tan ζ/ζ - 1‖ ≤ ‖ζ‖²` for `‖ζ‖ ≤ 1/2`), hence `φ ≡ 1`.
-/

namespace FormalResearch.SignUncertainty

lemma pi_ne_zero_c : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero

/-- `sin (π z) ≠ 0` for `0 < ‖z‖ < 1`. -/
lemma sin_pi_mul_ne_zero {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    Complex.sin (π * z) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  have hzk : z = (k : ℂ) := by
    have h' : (π : ℂ) * (z - k) = 0 := by linear_combination hk
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact absurd h1 pi_ne_zero_c
    · exact sub_eq_zero.mp h1
  have h2 : ‖(k : ℂ)‖ < 1 := by rw [← hzk]; exact hz
  rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs] at h2
  have h3 : |k| < 1 := by exact_mod_cast h2
  have hk0 : k = 0 := Int.abs_lt_one_iff.mp h3
  exact hz0 (by rw [hzk, hk0]; simp)

/-- `sin (π (z/2)) ≠ 0` for `0 < ‖z‖ < 1`. -/
lemma sin_pi_half_ne_zero {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    Complex.sin (π * (z / 2)) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  have hzk : z = ((2 * k : ℤ) : ℂ) := by
    have h' : (π : ℂ) * (z - 2 * k) = 0 := by linear_combination 2 * hk
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact absurd h1 pi_ne_zero_c
    · push_cast; exact sub_eq_zero.mp h1
  have h2 : ‖((2 * k : ℤ) : ℂ)‖ < 1 := by rw [← hzk]; exact hz
  rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs] at h2
  have h3 : |2 * k| < 1 := by exact_mod_cast h2
  have hk0 : 2 * k = 0 := Int.abs_lt_one_iff.mp h3
  exact hz0 (by rw [hzk, show 2 * k = 0 from hk0]; simp)

/-- `cos (π (z/2)) ≠ 0` for `‖z‖ < 1`. -/
lemma cos_pi_half_ne_zero {z : ℂ} (hz : ‖z‖ < 1) :
    Complex.cos (π * (z / 2)) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp h
  have hzk : z = ((2 * k + 1 : ℤ) : ℂ) := by
    have h' : (π : ℂ) * (z - (2 * k + 1)) = 0 := by linear_combination 2 * hk
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact absurd h1 pi_ne_zero_c
    · push_cast; exact sub_eq_zero.mp h1
  have h2 : ‖((2 * k + 1 : ℤ) : ℂ)‖ < 1 := by rw [← hzk]; exact hz
  rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs] at h2
  have h3 : |2 * k + 1| < 1 := by exact_mod_cast h2
  have := Int.abs_lt_one_iff.mp h3
  omega

/-- Nonzero points of norm `< 1` are in the complement of the integers. -/
lemma mem_integerComplement_of_ne {x : ℂ} (hx0 : x ≠ 0) (hx : ‖x‖ < 1) :
    x ∈ Complex.integerComplement := by
  rw [Complex.integerComplement, Set.mem_compl_iff, Set.mem_range]
  rintro ⟨n, hn⟩
  rw [← hn] at hx hx0
  rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs] at hx
  have h3 : |n| < 1 := by exact_mod_cast hx
  have := Int.abs_lt_one_iff.mp h3
  subst this
  simp at hx0

/-- `z - (m+1)` and `z + (m+1)` are nonzero for `‖z‖ < 1`. -/
lemma sub_add_ne_of_norm {x : ℂ} (hx : ‖x‖ < 1) (m : ℕ) :
    x - ((m : ℂ) + 1) ≠ 0 ∧ x + ((m : ℂ) + 1) ≠ 0 := by
  have hc : (1 : ℝ) ≤ ‖(m : ℂ) + 1‖ := by
    have : (m : ℂ) + 1 = ((m + 1 : ℕ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_natCast]
    exact_mod_cast Nat.succ_pos m
  constructor
  · intro h
    have e : x = (m : ℂ) + 1 := sub_eq_zero.mp h
    rw [e] at hx; linarith
  · intro h
    have e : x = -((m : ℂ) + 1) := eq_neg_of_add_eq_zero_left h
    rw [e, norm_neg] at hx; linarith

/-- Closed form of the cotangent term `1/(x-c) + 1/(x+c) = 2x/(x²-c²)`. -/
lemma cotTerm_closed {x : ℂ} (m : ℕ) (h1 : x - ((m : ℂ) + 1) ≠ 0) (h2 : x + ((m : ℂ) + 1) ≠ 0) :
    cotTerm x m = 2 * x / (x ^ 2 - ((m : ℂ) + 1) ^ 2) := by
  have hd : x ^ 2 - ((m : ℂ) + 1) ^ 2 ≠ 0 := by
    rw [show x ^ 2 - ((m : ℂ) + 1) ^ 2 = (x - ((m : ℂ) + 1)) * (x + ((m : ℂ) + 1)) by ring]
    exact mul_ne_zero h1 h2
  unfold cotTerm
  rw [div_add_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) hd]
  ring

/-- `cot (b) - cot (2b) = 1/sin (2b)` when `sin b, cos b ≠ 0`. -/
lemma cot_sub_cot_double {b : ℂ} (hs : Complex.sin b ≠ 0) (hc : Complex.cos b ≠ 0) :
    Complex.cot b - Complex.cot (2 * b) = 1 / Complex.sin (2 * b) := by
  rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin, Complex.sin_two_mul,
    Complex.cos_two_mul]
  field_simp
  ring

/-- Half-argument cotangent term: `cotTerm (z/2) n = 2 · cotTerm z (2n+1)`. -/
lemma cotTerm_half {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    cotTerm (z / 2) n = 2 * cotTerm z (2 * n + 1) := by
  have hz2 : ‖z / 2‖ < 1 := by
    rw [norm_div]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]; linarith
  obtain ⟨a1, a2⟩ := sub_add_ne_of_norm hz2 n
  obtain ⟨b1, b2⟩ := sub_add_ne_of_norm hz (2 * n + 1)
  rw [cotTerm_closed n a1 a2, cotTerm_closed (2 * n + 1) b1 b2]
  have hd1 : (z / 2) ^ 2 - ((n : ℂ) + 1) ^ 2 ≠ 0 := by
    rw [show (z / 2) ^ 2 - ((n : ℂ) + 1) ^ 2 = (z / 2 - ((n : ℂ) + 1)) * (z / 2 + ((n : ℂ) + 1)) by ring]
    exact mul_ne_zero a1 a2
  have hd2 : z ^ 2 - (((2 * n + 1 : ℕ) : ℂ) + 1) ^ 2 ≠ 0 := by
    rw [show z ^ 2 - (((2 * n + 1 : ℕ) : ℂ) + 1) ^ 2 =
      (z - (((2 * n + 1 : ℕ) : ℂ) + 1)) * (z + (((2 * n + 1 : ℕ) : ℂ) + 1)) by ring]
    exact mul_ne_zero b1 b2
  have hcast : (((2 * n + 1 : ℕ) : ℂ)) = 2 * (n : ℂ) + 1 := by push_cast; ring
  rw [hcast]
  have hD : z ^ 2 - (2 * (n : ℂ) + 1 + 1) ^ 2 = 4 * ((z / 2) ^ 2 - ((n : ℂ) + 1) ^ 2) := by ring
  rw [hD]
  field_simp
  ring

/-- The partial-fraction expansion `π / sin (π z) - 1/z = ∑_{n≥0} 2(-1)^n z/((n+1)² - z²)`
for `0 < ‖z‖ < 1`. Derived from Mathlib's Mittag-Leffler expansion of `π cot` at `z/2` and `z`,
using `cot b - cot 2b = 1/sin 2b` and the even/odd splitting of the alternating sum. -/
lemma csc_hasSum {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => 2 * (-1 : ℂ) ^ n * z / (((n : ℂ) + 1) ^ 2 - z ^ 2))
      (π / Complex.sin (π * z) - 1 / z) := by
  have hzM : z ∈ Complex.integerComplement := mem_integerComplement_of_ne hz0 hz
  have hz2 : ‖z / 2‖ < 1 := by
    rw [norm_div]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]; linarith
  have hz2M : z / 2 ∈ Complex.integerComplement :=
    mem_integerComplement_of_ne (div_ne_zero hz0 two_ne_zero) hz2
  have hsum : Summable (fun n => cotTerm z n) := summable_cotTerm hzM
  have hE : Summable (fun k : ℕ => cotTerm z (2 * k + 1)) :=
    hsum.comp_injective (fun a b (h : 2 * a + 1 = 2 * b + 1) => by omega)
  have hO : Summable (fun k : ℕ => cotTerm z (2 * k)) :=
    hsum.comp_injective (fun a b (h : 2 * a = 2 * b) => by omega)
  set F : ℕ → ℂ := fun n => (-1 : ℂ) ^ n * cotTerm z n with hFdef
  have hF : Summable F := hsum.alternating
  have hFe : Summable (fun k : ℕ => F (2 * k)) :=
    hF.comp_injective (fun a b (h : 2 * a = 2 * b) => by omega)
  have hFo : Summable (fun k : ℕ => F (2 * k + 1)) :=
    hF.comp_injective (fun a b (h : 2 * a + 1 = 2 * b + 1) => by omega)
  have hsplitF : ∑' k, F (2 * k) + ∑' k, F (2 * k + 1) = ∑' n, F n :=
    tsum_even_add_odd (f := F) hFe hFo
  have e1 : ∑' k, F (2 * k) = ∑' k, cotTerm z (2 * k) := by
    congr 1; funext k; simp only [hFdef, pow_mul]; norm_num
  have e2 : ∑' k, F (2 * k + 1) = -∑' k, cotTerm z (2 * k + 1) := by
    rw [← tsum_neg]; congr 1; funext k; simp only [hFdef, pow_succ, pow_mul]; norm_num
  have hsplit : ∑' n, cotTerm z n = ∑' k, cotTerm z (2 * k) + ∑' k, cotTerm z (2 * k + 1) :=
    (tsum_even_add_odd (f := cotTerm z) hO hE).symm
  have hS1 : ∑' n, cotTerm (z / 2) n = 2 * ∑' k, cotTerm z (2 * k + 1) := by
    rw [← tsum_mul_left]; congr 1; funext n; exact cotTerm_half hz n
  have c1 : π * Complex.cot (π * (z / 2)) - 1 / (z / 2) = ∑' n, cotTerm (z / 2) n :=
    cot_series_rep' hz2M
  have c2 : π * Complex.cot (π * z) - 1 / z = ∑' n, cotTerm z n := cot_series_rep' hzM
  have hcsc : π / Complex.sin (π * z) =
      π * Complex.cot (π * (z / 2)) - π * Complex.cot (π * z) := by
    have hb := cot_sub_cot_double (b := π * (z / 2)) (sin_pi_half_ne_zero hz0 hz)
      (cos_pi_half_ne_zero hz)
    have h2b : 2 * (π * (z / 2)) = π * z := by ring
    rw [h2b] at hb
    rw [show π / Complex.sin (π * z) = π * (1 / Complex.sin (π * z)) by ring, ← hb]
    ring
  have hhalf : 1 / (z / 2) = 2 * (1 / z) := by rw [one_div_div]; ring
  have hdiff : π / Complex.sin (π * z) - 1 / z =
      ∑' n, cotTerm (z / 2) n - ∑' n, cotTerm z n := by
    rw [hcsc]
    linear_combination c1 - c2 + hhalf
  have hval : π / Complex.sin (π * z) - 1 / z = -∑' n, F n := by
    rw [hdiff, hS1]
    have hFsum : ∑' n, F n = ∑' k, cotTerm z (2 * k) - ∑' k, cotTerm z (2 * k + 1) := by
      rw [← hsplitF, e1, e2]; ring
    rw [hFsum, hsplit]
    ring
  have hfun : (fun n : ℕ => 2 * (-1 : ℂ) ^ n * z / (((n : ℂ) + 1) ^ 2 - z ^ 2)) =
      fun n => -F n := by
    funext n
    obtain ⟨a1, a2⟩ := sub_add_ne_of_norm hz n
    simp only [hFdef]
    rw [cotTerm_closed n a1 a2]
    have hne : ((n : ℂ) + 1) ^ 2 - z ^ 2 = -(z ^ 2 - ((n : ℂ) + 1) ^ 2) := by ring
    rw [hne, div_neg]
    ring
  rw [hfun, hval]
  exact hF.hasSum.neg

/-- The double-series term `2 (-1)^n z^(2j+1) / (n+1)^(2j+2)` (index `p = (n, j)`). -/
noncomputable def etaH (z : ℂ) (p : ℕ × ℕ) : ℂ :=
  2 * (-1 : ℂ) ^ p.1 * z ^ (2 * p.2 + 1) / (((p.1 : ℂ) + 1)) ^ (2 * p.2 + 2)

lemma norm_natsucc_cast_eq (n : ℕ) : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
  have : (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

lemma norm_etaH_le {z : ℂ} (p : ℕ × ℕ) :
    ‖etaH z p‖ ≤ 2 * (1 / ((p.1 : ℝ) + 1) ^ 2) * (‖z‖ * (‖z‖ ^ 2) ^ p.2) := by
  obtain ⟨n, j⟩ := p
  have hm : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hm0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hA : 0 ≤ ‖z‖ * (‖z‖ ^ 2) ^ j := by positivity
  have hpow : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ (2 * j + 2) :=
    pow_le_pow_right₀ hm (by omega)
  have h1 : 1 ≤ ((n : ℝ) + 1) ^ (2 * j + 2) / ((n : ℝ) + 1) ^ 2 :=
    (one_le_div (by positivity)).mpr hpow
  have hnorm : ‖etaH z (n, j)‖ = 2 * ‖z‖ ^ (2 * j + 1) / ((n : ℝ) + 1) ^ (2 * j + 2) := by
    unfold etaH
    simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, norm_natsucc_cast_eq]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]; ring
  rw [hnorm]
  have hz2 : ‖z‖ ^ (2 * j + 1) = ‖z‖ * (‖z‖ ^ 2) ^ j := by ring
  rw [hz2, div_le_iff₀ (by positivity)]
  have e : 2 * (1 / ((n : ℝ) + 1) ^ 2) * (‖z‖ * (‖z‖ ^ 2) ^ j) * ((n : ℝ) + 1) ^ (2 * j + 2)
      = 2 * (‖z‖ * (‖z‖ ^ 2) ^ j) * (((n : ℝ) + 1) ^ (2 * j + 2) / ((n : ℝ) + 1) ^ 2) := by ring
  rw [e]
  have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * (‖z‖ * (‖z‖ ^ 2) ^ j))
  linarith

lemma etaH_summable {z : ℂ} (hz : ‖z‖ < 1) : Summable (etaH z) := by
  have hz2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  have hA0 : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
    simpa using summable_inv_succ_pow 0
  have hB : Summable (fun j : ℕ => ‖z‖ * (‖z‖ ^ 2) ^ j) :=
    (summable_geometric_of_lt_one (sq_nonneg _) hz2).mul_left _
  have hprod := Summable.mul_of_nonneg (hA0.mul_left 2) hB
    (fun n => by dsimp only; positivity) (fun j => by dsimp only; positivity)
  exact Summable.of_norm_bounded hprod (fun p => norm_etaH_le p)

/-- Algebraic identity behind the geometric expansion of `etaH` (atoms `c, z, m`). -/
lemma etaH_geom_alg (c z m : ℂ) (j : ℕ) :
    c * z ^ (2 * j + 1) / m ^ (2 * j + 2) = c * z / m ^ 2 * (z ^ 2 / m ^ 2) ^ j := by
  rw [div_pow]
  rw [show z ^ (2 * j + 1) = z * (z ^ 2) ^ j by ring, show m ^ (2 * j + 2) = m ^ 2 * (m ^ 2) ^ j by ring]
  ring

/-- The `n`-fiber of `etaH`: a geometric series in `j`. -/
lemma etaH_fiber_n {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    HasSum (fun j : ℕ => etaH z (n, j))
      (2 * (-1 : ℂ) ^ n * z / (((n : ℂ) + 1) ^ 2 - z ^ 2)) := by
  have hm0 : ((n : ℂ) + 1) ≠ 0 := by
    intro h
    have : (n : ℝ) + 1 = 0 := by exact_mod_cast h
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hmn : 1 ≤ ‖(n : ℂ) + 1‖ := by
    rw [norm_natsucc_cast_eq]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hz2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  have hq : ‖z ^ 2 / ((n : ℂ) + 1) ^ 2‖ < 1 := by
    rw [norm_div, norm_pow, norm_pow, div_lt_one (by positivity)]
    have h2 : 1 ≤ ‖(n : ℂ) + 1‖ ^ 2 := by nlinarith
    nlinarith [norm_nonneg z]
  set q : ℂ := z ^ 2 / ((n : ℂ) + 1) ^ 2 with hqdef
  have hq1 : (1 : ℂ) - q ≠ 0 := by
    intro h
    have e := sub_eq_zero.mp h
    rw [← e] at hq
    simp at hq
  have hd : ((n : ℂ) + 1) ^ 2 - z ^ 2 ≠ 0 := by
    intro h
    have e : z ^ 2 = ((n : ℂ) + 1) ^ 2 := by linear_combination -h
    have h3 := congrArg norm e
    rw [norm_pow, norm_pow] at h3
    nlinarith [norm_nonneg z, norm_nonneg ((n : ℂ) + 1)]
  have hg := (hasSum_geometric_of_norm_lt_one hq).mul_left
    (2 * (-1 : ℂ) ^ n * z / ((n : ℂ) + 1) ^ 2)
  have hval : 2 * (-1 : ℂ) ^ n * z / ((n : ℂ) + 1) ^ 2 * (1 - q)⁻¹ =
      2 * (-1 : ℂ) ^ n * z / (((n : ℂ) + 1) ^ 2 - z ^ 2) := by
    rw [hqdef]
    field_simp
  have hfun : (fun j : ℕ => etaH z (n, j)) =
      fun j : ℕ => 2 * (-1 : ℂ) ^ n * z / ((n : ℂ) + 1) ^ 2 * q ^ j := by
    funext j
    unfold etaH
    rw [hqdef]
    exact etaH_geom_alg _ _ _ j
  rw [hfun]
  rw [← hval]
  exact hg

/-- The `j`-fiber of `etaH`: the Dirichlet eta value `etaC j` times `2 z^(2j+1)`. -/
lemma etaH_fiber_j (z : ℂ) (j : ℕ) :
    HasSum (fun n : ℕ => etaH z (n, j)) (2 * (etaC j : ℂ) * z ^ (2 * j + 1)) := by
  have h := Complex.hasSum_ofReal.mpr (etaC_hasSum j)
  have h2 := h.mul_left (2 * z ^ (2 * j + 1))
  have hfun : (fun n : ℕ => etaH z (n, j)) = fun n : ℕ =>
      2 * z ^ (2 * j + 1) * (((-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1) ^ (2 * j + 2)) : ℝ) : ℂ) := by
    funext n
    unfold etaH
    push_cast
    ring
  rw [hfun]
  convert h2 using 1
  ring

/-- Partial-fraction expansion of `π / sin (π z) - 1/z` as an eta series, for `0 < ‖z‖ < 1`. -/
lemma eta_hasSum {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    HasSum (fun j : ℕ => 2 * (etaC j : ℂ) * z ^ (2 * j + 1))
      (π / Complex.sin (π * z) - 1 / z) := by
  have hS := etaH_summable hz
  have T1 : HasSum (fun n : ℕ => 2 * (-1 : ℂ) ^ n * z / (((n : ℂ) + 1) ^ 2 - z ^ 2))
      (∑' p, etaH z p) :=
    hS.hasSum.prod_fiberwise (fun n => etaH_fiber_n hz n)
  have hsw : HasSum (fun p : ℕ × ℕ => etaH z p.swap) (∑' p, etaH z p) :=
    (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hS.hasSum
  have T2 : HasSum (fun j : ℕ => 2 * (etaC j : ℂ) * z ^ (2 * j + 1)) (∑' p, etaH z p) :=
    hsw.prod_fiberwise (fun j => etaH_fiber_j z j)
  have hv := (csc_hasSum hz0 hz).unique T1
  rw [hv]
  exact T2

/-- The coefficients `etaC j/(j+1)` of `g`'s power series. -/
noncomputable def langerc (j : ℕ) : ℝ := etaC j / ((j : ℝ) + 1)

/-- The power series `P(z) = ∑_j etaC j/(j+1) · z^(2j+2)`. -/
noncomputable def Pser (z : ℂ) : ℂ := ∑' j : ℕ, ((langerc j : ℝ) : ℂ) * z ^ (2 * j + 2)

lemma langerc_nonneg (j : ℕ) : 0 ≤ langerc j :=
  div_nonneg (etaC_pos j).le (by positivity)

lemma langerc_le_one (j : ℕ) : langerc j ≤ 1 := by
  unfold langerc
  rw [div_le_one (by positivity)]
  have h1 := etaC_lt_one j
  have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

lemma Pser_summable {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun j : ℕ => ((langerc j : ℝ) : ℂ) * z ^ (2 * j + 2)) := by
  have hz2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (sq_nonneg _) hz2).mul_left (‖z‖ ^ 2)) (fun j => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (langerc_nonneg j)]
  have e : ‖z‖ ^ (2 * j + 2) = ‖z‖ ^ 2 * (‖z‖ ^ 2) ^ j := by ring
  rw [e]
  have : 0 ≤ ‖z‖ ^ 2 * (‖z‖ ^ 2) ^ j := by positivity
  exact mul_le_of_le_one_left this (langerc_le_one j)

lemma Pser_zero : Pser 0 = 0 := by
  unfold Pser
  simp

lemma Pser_hasDerivAt {y : ℂ} (hy : ‖y‖ < 1 / 2) :
    HasDerivAt Pser (∑' j : ℕ, 2 * (etaC j : ℂ) * y ^ (2 * j + 1)) y := by
  have hu : Summable (fun j : ℕ => ((j : ℝ) + 1) * (1 / 4 : ℝ) ^ j) := by
    have h1 := (summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 4 : ℝ))
      (by norm_num)).add (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 4 : ℝ) < 1))
    exact h1.congr (fun j => by ring)
  have hd := hasDerivAt_tsum_of_isPreconnected (t := Metric.ball (0 : ℂ) (1 / 2))
    (y₀ := 0) (u := fun j : ℕ => ((j : ℝ) + 1) * (1 / 4 : ℝ) ^ j)
    (g := fun (j : ℕ) (w : ℂ) => ((langerc j : ℝ) : ℂ) * w ^ (2 * j + 2))
    (g' := fun (j : ℕ) (w : ℂ) => ((langerc j : ℝ) : ℂ) * (((2 * j + 2 : ℕ) : ℂ) * w ^ (2 * j + 2 - 1)))
    hu Metric.isOpen_ball (convex_ball _ _).isPreconnected
    (fun n w _ => (hasDerivAt_pow (2 * n + 2) w).const_mul _)
    (by
      intro n w hw
      have hw' : ‖w‖ < 1 / 2 := mem_ball_zero_iff.mp hw
      have hw2 : ‖w‖ ^ (2 * n + 2 - 1) ≤ (1 / 2 : ℝ) ^ (2 * n + 2 - 1) :=
        pow_le_pow_left₀ (norm_nonneg _) hw'.le _
      have key : ((2 * n + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (2 * n + 2 - 1)
          = ((n : ℝ) + 1) * (1 / 4 : ℝ) ^ n := by
        rw [show 2 * n + 2 - 1 = 2 * n + 1 by omega, pow_succ, pow_mul]
        push_cast
        norm_num
        ring
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (langerc_nonneg n), norm_pow, Complex.norm_natCast]
      have hA : (0 : ℝ) ≤ ((2 * n + 2 : ℕ) : ℝ) := by positivity
      calc langerc n * (((2 * n + 2 : ℕ) : ℝ) * ‖w‖ ^ (2 * n + 2 - 1))
          ≤ 1 * (((2 * n + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (2 * n + 2 - 1)) := by
            apply mul_le_mul (langerc_le_one n) (mul_le_mul_of_nonneg_left hw2 hA) (by positivity)
              (by norm_num)
        _ = ((n : ℝ) + 1) * (1 / 4 : ℝ) ^ n := by rw [one_mul, key])
    (by simp)
    (by
      have : (fun n : ℕ => ((langerc n : ℝ) : ℂ) * (0 : ℂ) ^ (2 * n + 2)) = fun _ => 0 := by
        funext n
        rw [zero_pow (by omega), mul_zero]
      show Summable (fun n : ℕ => ((langerc n : ℝ) : ℂ) * (0 : ℂ) ^ (2 * n + 2))
      rw [this]
      exact summable_zero)
    (mem_ball_zero_iff.mpr hy)
  have hval : (∑' j : ℕ, ((langerc j : ℝ) : ℂ) * (((2 * j + 2 : ℕ) : ℂ) * y ^ (2 * j + 2 - 1)))
      = ∑' j : ℕ, 2 * (etaC j : ℂ) * y ^ (2 * j + 1) := by
    congr 1
    funext j
    rw [show 2 * j + 2 - 1 = 2 * j + 1 by omega]
    unfold langerc
    push_cast
    have hj : ((j : ℂ) + 1) ≠ 0 := by
      intro h
      have : (j : ℝ) + 1 = 0 := by exact_mod_cast h
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    field_simp
  rw [← hval]
  exact hd

/-- `tan ζ / ζ - 1` is bounded by `‖ζ‖²` for `0 < ‖ζ‖ ≤ 1/2` (from the Taylor bounds of `sin`, `cos`). -/
lemma tan_div_sub_one_norm_le {ζ : ℂ} (hζ0 : ζ ≠ 0) (hζ : ‖ζ‖ ≤ 1 / 2) :
    ‖Complex.tan ζ / ζ - 1‖ ≤ ‖ζ‖ ^ 2 := by
  have hr0 : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
  have hr : 0 ≤ ‖ζ‖ := hr0.le
  have hζ1 : ‖ζ‖ ≤ 1 := by linarith
  have hsb := Complex.sin_bound hζ1
  have hcb := Complex.cos_bound hζ1
  -- lower bound for `‖cos ζ‖`
  have hcos_lb : 1 - ‖ζ‖ ^ 2 / 2 - ‖ζ‖ ^ 4 * (5 / 96) ≤ ‖Complex.cos ζ‖ := by
    have h1 : ‖(1 : ℂ)‖ - ‖ζ ^ 2 / 2‖ ≤ ‖(1 : ℂ) - ζ ^ 2 / 2‖ := norm_sub_norm_le _ _
    have h2 := norm_sub_norm_le ((1 : ℂ) - ζ ^ 2 / 2) (-(Complex.cos ζ - (1 - ζ ^ 2 / 2)))
    have e : (1 : ℂ) - ζ ^ 2 / 2 - -(Complex.cos ζ - (1 - ζ ^ 2 / 2)) = Complex.cos ζ := by ring
    rw [e, norm_neg] at h2
    have h3 : ‖ζ ^ 2 / 2‖ = ‖ζ‖ ^ 2 / 2 := by
      rw [norm_div, norm_pow]; simp
    rw [norm_one, h3] at h1
    linarith
  have hr2 : ‖ζ‖ ^ 2 ≤ 1 / 4 := by nlinarith
  have hr4 : ‖ζ‖ ^ 4 ≤ 1 / 16 := by nlinarith
  have hc0pos : 0 < 1 - ‖ζ‖ ^ 2 / 2 - ‖ζ‖ ^ 4 * (5 / 96) := by linarith
  have hcne : Complex.cos ζ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hcos_lb
    linarith
  have key : Complex.tan ζ / ζ - 1 = (Complex.sin ζ - ζ * Complex.cos ζ) / (ζ * Complex.cos ζ) := by
    rw [Complex.tan_eq_sin_div_cos]
    field_simp
  have hNeq : Complex.sin ζ - ζ * Complex.cos ζ =
      ζ ^ 3 / 3 + (Complex.sin ζ - (ζ - ζ ^ 3 / 6)) - ζ * (Complex.cos ζ - (1 - ζ ^ 2 / 2)) := by
    ring
  have hNn : ‖Complex.sin ζ - ζ * Complex.cos ζ‖ ≤
      ‖ζ‖ ^ 3 / 3 + ‖ζ‖ ^ 5 / 100 + ‖ζ‖ * (‖ζ‖ ^ 4 * (5 / 96)) := by
    rw [hNeq]
    have A := norm_sub_le (ζ ^ 3 / 3 + (Complex.sin ζ - (ζ - ζ ^ 3 / 6)))
      (ζ * (Complex.cos ζ - (1 - ζ ^ 2 / 2)))
    have B := norm_add_le (ζ ^ 3 / 3) (Complex.sin ζ - (ζ - ζ ^ 3 / 6))
    have C : ‖ζ * (Complex.cos ζ - (1 - ζ ^ 2 / 2))‖ ≤ ‖ζ‖ * (‖ζ‖ ^ 4 * (5 / 96)) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hcb (norm_nonneg _)
    have D : ‖ζ ^ 3 / 3‖ = ‖ζ‖ ^ 3 / 3 := by
      rw [norm_div, norm_pow]; simp
    linarith
  have hpoly : ‖ζ‖ ^ 3 / 3 + ‖ζ‖ ^ 5 / 100 + ‖ζ‖ * (‖ζ‖ ^ 4 * (5 / 96)) ≤
      ‖ζ‖ ^ 3 * (1 - ‖ζ‖ ^ 2 / 2 - ‖ζ‖ ^ 4 * (5 / 96)) := by
    have h4 : 1 / 3 + ‖ζ‖ ^ 2 / 100 + ‖ζ‖ ^ 2 * (5 / 96) ≤
        1 - ‖ζ‖ ^ 2 / 2 - ‖ζ‖ ^ 4 * (5 / 96) := by
      linarith
    have := mul_le_mul_of_nonneg_left h4 (pow_nonneg hr 3)
    nlinarith [this]
  rw [key, norm_div, norm_mul, div_le_iff₀ (mul_pos hr0 (lt_of_lt_of_le hc0pos hcos_lb))]
  calc ‖Complex.sin ζ - ζ * Complex.cos ζ‖
      ≤ ‖ζ‖ ^ 3 * (1 - ‖ζ‖ ^ 2 / 2 - ‖ζ‖ ^ 4 * (5 / 96)) := hNn.trans hpoly
    _ ≤ ‖ζ‖ ^ 3 * ‖Complex.cos ζ‖ := mul_le_mul_of_nonneg_left hcos_lb (by positivity)
    _ = ‖ζ‖ ^ 2 * (‖ζ‖ * ‖Complex.cos ζ‖) := by ring

/-- The function `u(z) = tan(π z/2)/(π z/2)` whose logarithm is `g`. -/
noncomputable def langerU (z : ℂ) : ℂ := Complex.tan (π * z / 2) / (π * z / 2)

/-- The derivative of `u`: `u'(z) = u(z) (π/sin(πz) - 1/z)` for `0 < ‖z‖ < 1/4`. -/
lemma langerU_hasDerivAt {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1 / 4) :
    HasDerivAt langerU (langerU z * (π / Complex.sin (π * z) - 1 / z)) z := by
  have hz1 : ‖z‖ < 1 := by linarith
  have hcos : Complex.cos (π * z / 2) ≠ 0 := by
    rw [mul_div_assoc]; exact cos_pi_half_ne_zero hz1
  have hsin : Complex.sin (π * z / 2) ≠ 0 := by
    rw [mul_div_assoc]; exact sin_pi_half_ne_zero hz0 hz1
  have hpz : π * z / 2 ≠ 0 := by
    exact div_ne_zero (mul_ne_zero pi_ne_zero_c hz0) two_ne_zero
  have hl : HasDerivAt (fun w : ℂ => π * w / 2) (π / 2) z := by
    simpa using ((hasDerivAt_id z).const_mul (π : ℂ)).div_const 2
  have ht := HasDerivAt.comp z (Complex.hasDerivAt_tan (x := π * z / 2) hcos) hl
  have hq := ht.div hl hpz
  have hval : (1 / Complex.cos (π * z / 2) ^ 2 * (π / 2) * (π * z / 2) -
      Complex.tan (π * z / 2) * (π / 2)) / (π * z / 2) ^ 2
      = langerU z * (π / Complex.sin (π * z) - 1 / z) := by
    unfold langerU
    have hsin2 : Complex.sin (π * z) = 2 * Complex.sin (π * z / 2) * Complex.cos (π * z / 2) := by
      rw [← Complex.sin_two_mul]; ring_nf
    rw [hsin2, Complex.tan_eq_sin_div_cos]
    field_simp
  have hfun : langerU = (Complex.tan ∘ fun w : ℂ => π * w / 2) / (fun w : ℂ => π * w / 2) := by
    funext w
    rfl
  rw [hfun]
  exact hq.congr_deriv hval

/-- `‖P(z)‖ ≤ 1/4` for `‖z‖ < 1/8`. -/
lemma Pser_norm_le {z : ℂ} (hz : ‖z‖ < 1 / 8) : ‖Pser z‖ ≤ 1 / 4 := by
  have hz1 : ‖z‖ < 1 := by linarith
  have hz2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  have hterm : ∀ j : ℕ, ‖((langerc j : ℝ) : ℂ) * z ^ (2 * j + 2)‖ ≤ ‖z‖ ^ 2 * (‖z‖ ^ 2) ^ j := by
    intro j
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (langerc_nonneg j)]
    have e : ‖z‖ ^ (2 * j + 2) = ‖z‖ ^ 2 * (‖z‖ ^ 2) ^ j := by ring
    rw [e]
    exact mul_le_of_le_one_left (by positivity) (langerc_le_one j)
  have hgeo : Summable (fun j : ℕ => ‖z‖ ^ 2 * (‖z‖ ^ 2) ^ j) :=
    (summable_geometric_of_lt_one (sq_nonneg _) hz2).mul_left _
  have hsn : Summable (fun j : ℕ => ‖((langerc j : ℝ) : ℂ) * z ^ (2 * j + 2)‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hterm hgeo
  have hz64 : ‖z‖ ^ 2 ≤ 1 / 64 := by nlinarith [norm_nonneg z]
  have h1 : (1 - ‖z‖ ^ 2)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
    linarith
  calc ‖Pser z‖ ≤ ∑' j : ℕ, ‖((langerc j : ℝ) : ℂ) * z ^ (2 * j + 2)‖ :=
        norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' j : ℕ, ‖z‖ ^ 2 * (‖z‖ ^ 2) ^ j := Summable.tsum_le_tsum hterm hsn hgeo
    _ = ‖z‖ ^ 2 * (1 - ‖z‖ ^ 2)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg _) hz2]
    _ ≤ 1 / 4 := by
        linarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖z‖)]

/-- The complex-variable function `w ↦ u(wz) exp(-P(wz))`. -/
noncomputable def phiC (z w : ℂ) : ℂ := langerU (w * z) * Complex.exp (-Pser (w * z))

/-- Along the segment `t ↦ t z` (real `t ∈ (0,2)`), `φ(t) = u(tz) exp(-P(tz))` is locally
constant: its derivative vanishes, because `u'/u = P'` by the partial-fraction identity. -/
lemma phiC_hasDerivAt {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1 / 8) {s : ℝ} (hs0 : 0 < s)
    (hs2 : s < 2) : HasDerivAt (fun t : ℝ => phiC z (t : ℂ)) 0 s := by
  have hsz : ‖(s : ℂ) * z‖ < 1 / 4 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    nlinarith [norm_nonneg z]
  have hy0 : (s : ℂ) * z ≠ 0 := mul_ne_zero (by exact_mod_cast hs0.ne') hz0
  have hY : HasDerivAt (fun w : ℂ => w * z) z (s : ℂ) := by
    simpa using (hasDerivAt_id (s : ℂ)).mul_const z
  have hU := HasDerivAt.comp (s : ℂ) (langerU_hasDerivAt hy0 hsz) hY
  have hP0 := HasDerivAt.comp (s : ℂ) (Pser_hasDerivAt (y := (s : ℂ) * z) (by linarith)) hY
  have hK := (eta_hasSum hy0 (by linarith)).tsum_eq
  rw [hK] at hP0
  have hE := hP0.neg.cexp
  have hprod := hU.mul hE
  have hfin : HasDerivAt (phiC z) 0 (s : ℂ) := by
    refine hprod.congr_deriv ?_
    simp only [Function.comp]
    ring
  exact HasDerivAt.comp_ofReal hfin

/-- `‖π (t z)/2‖ = π t ‖z‖/2` for real `t ≥ 0`. -/
lemma norm_pi_mul_half {z : ℂ} {t : ℝ} (ht : 0 ≤ t) :
    ‖π * ((t : ℂ) * z) / 2‖ = π * t * ‖z‖ / 2 := by
  rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le, abs_of_nonneg ht]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  ring

/-- `φ` is constant on `(0,2)` and tends to `1` at `0⁺`, so `φ(1) = 1`. -/
lemma phiC_one {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1 / 8) :
    langerU z * Complex.exp (-Pser z) = 1 := by
  have hc : ∀ s ∈ Set.Ioo (0 : ℝ) 2, phiC z (s : ℂ) = phiC z ((1 : ℝ) : ℂ) := by
    intro s hs
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (f := fun t : ℝ => phiC z (t : ℂ))
      (fun s hs => (phiC_hasDerivAt hz0 hz hs.1 hs.2).differentiableAt.differentiableWithinAt)
      (fun s hs => (phiC_hasDerivAt hz0 hz hs.1 hs.2).deriv) hs ⟨one_pos, one_lt_two⟩
  have hlim : Tendsto (fun t : ℝ => phiC z (t : ℂ)) (𝓝[>] 0) (𝓝 1) := by
    have hPc : Tendsto (fun t : ℝ => Pser ((t : ℂ) * z)) (𝓝 0) (𝓝 0) := by
      have h1 : ContinuousAt Pser 0 := (Pser_hasDerivAt (y := 0) (by norm_num)).continuousAt
      have h2 : Tendsto (fun t : ℝ => (t : ℂ) * z) (𝓝 0) (𝓝 0) := by
        have hc' : Continuous (fun t : ℝ => (t : ℂ) * z) :=
          (Complex.continuous_ofReal).mul continuous_const
        simpa using hc'.tendsto 0
      have h3 := h1.tendsto.comp h2
      rw [Pser_zero] at h3
      exact h3
    have hexp : Tendsto (fun t : ℝ => Complex.exp (-Pser ((t : ℂ) * z))) (𝓝[>] 0) (𝓝 1) := by
      have hPc' : Tendsto (fun t : ℝ => -Pser ((t : ℂ) * z)) (𝓝 0) (𝓝 0) := by
        simpa using hPc.neg
      have h5 : Tendsto (fun t : ℝ => Complex.exp (-Pser ((t : ℂ) * z))) (𝓝 0) (𝓝 (Complex.exp 0)) :=
        (Complex.continuous_exp.tendsto 0).comp hPc'
      have := tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi (0 : ℝ)) h5
      simpa using this
    have hu : Tendsto (fun t : ℝ => langerU ((t : ℂ) * z)) (𝓝[>] 0) (𝓝 1) := by
      have hbound : ∀ᶠ (t : ℝ) in 𝓝[>] (0 : ℝ), ‖langerU ((t : ℂ) * z) - 1‖ ≤ 4 * ‖z‖ ^ 2 * t ^ 2 := by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
        have ht0 : 0 < t := ht.1
        have ht1 : t < 1 := ht.2
        have hzt : ‖(t : ℂ) * z‖ < 1 / 8 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
          nlinarith [norm_nonneg z]
        have htz0 : (t : ℂ) * z ≠ 0 := mul_ne_zero (by exact_mod_cast ht0.ne') hz0
        have hζ0 : π * ((t : ℂ) * z) / 2 ≠ 0 :=
          div_ne_zero (mul_ne_zero pi_ne_zero_c htz0) two_ne_zero
        have hnorm := norm_pi_mul_half (z := z) ht0.le
        have hζn : ‖π * ((t : ℂ) * z) / 2‖ ≤ 1 / 2 := by
          rw [hnorm]
          have htz : t * ‖z‖ ≤ 1 / 8 := by nlinarith [norm_nonneg z]
          have h1 : π * (t * ‖z‖) ≤ 4 * (t * ‖z‖) :=
            mul_le_mul_of_nonneg_right Real.pi_le_four (by positivity)
          have e : π * t * ‖z‖ = π * (t * ‖z‖) := by ring
          linarith
        have key := tan_div_sub_one_norm_le hζ0 hζn
        unfold langerU
        refine key.trans ?_
        rw [hnorm]
        have h3 : π ^ 2 / 4 ≤ 4 := by nlinarith [Real.pi_le_four, Real.pi_pos]
        have h2 : (π * t * ‖z‖ / 2) ^ 2 = (π ^ 2 / 4) * (t ^ 2 * ‖z‖ ^ 2) := by ring
        rw [h2]
        nlinarith [mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ t ^ 2 * ‖z‖ ^ 2)]
      have hub : Tendsto (fun t : ℝ => 4 * ‖z‖ ^ 2 * t ^ 2) (𝓝[>] 0) (𝓝 0) := by
        have hc' : Continuous (fun t : ℝ => 4 * ‖z‖ ^ 2 * t ^ 2) := by fun_prop
        have := tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi (0 : ℝ)) (hc'.tendsto 0)
        simpa using this
      have hlim0 : Tendsto (fun t : ℝ => langerU ((t : ℂ) * z) - 1) (𝓝[>] 0) (𝓝 0) :=
        squeeze_zero_norm' hbound hub
      have := hlim0.add_const 1
      simpa using this
    have := hu.mul hexp
    rw [one_mul] at this
    exact this
  have hev : (fun t : ℝ => phiC z (t : ℂ)) =ᶠ[𝓝[>] 0] fun _ => phiC z ((1 : ℝ) : ℂ) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 by norm_num)] with t ht
    exact hc t ht
  have hconst_lim : Tendsto (fun t : ℝ => phiC z (t : ℂ)) (𝓝[>] 0)
      (𝓝 (phiC z ((1 : ℝ) : ℂ))) :=
    tendsto_const_nhds.congr' hev.symm
  have h1 : phiC z ((1 : ℝ) : ℂ) = 1 := tendsto_nhds_unique hconst_lim hlim
  simpa [phiC] using h1

/-- `u(z) = exp(P(z))` for `0 < ‖z‖ < 1/8`. -/
lemma langerU_eq_exp {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1 / 8) :
    langerU z = Complex.exp (Pser z) := by
  have h := phiC_one hz0 hz
  rw [Complex.exp_neg] at h
  field_simp at h
  exact h

/-- `log u(z) = P(z)` for `‖z‖ < 1/8` (with `log 0 = 0`). -/
lemma log_langerU_eq {z : ℂ} (hz : ‖z‖ < 1 / 8) : Complex.log (langerU z) = Pser z := by
  by_cases hz0 : z = 0
  · subst hz0
    simp [langerU, Pser_zero]
  · rw [langerU_eq_exp hz0 hz]
    have hP := Pser_norm_le hz
    have him := Complex.abs_im_le_norm (Pser z)
    have hab := abs_le.mp (le_trans him hP)
    apply Complex.log_exp
    · linarith [hab.1, Real.pi_gt_three]
    · linarith [hab.2, Real.pi_gt_three]

/-- **Series identity** (HasSum form is `eta_hasSum`): for `0 < ‖z‖ < 1`,
`π / sin (π z) - 1/z = 2 ∑_{j≥0} η_D(2j+2) z^(2j+1)`. -/
theorem langer_eta_identity {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    π / Complex.sin (π * z) - 1 / z = 2 * ∑' j : ℕ, (etaC j : ℂ) * z ^ (2 * j + 1) := by
  rw [← (eta_hasSum hz0 hz).tsum_eq, ← tsum_mul_left]
  congr 1
  funext j
  ring

/-- **Langer `g`, power series** (`‖z‖ < 1/8`; `g 0 = 0` since `Complex.log 0 = 0`):
`log (tan (π z/2) / (π z/2)) = ∑_{j≥0} η_D(2j+2)/(j+1) z^(2j+2)`, HasSum form. -/
theorem langer_g_hasSum {z : ℂ} (hz : ‖z‖ < 1 / 8) :
    HasSum (fun j : ℕ => ((etaC j / ((j : ℝ) + 1) : ℝ) : ℂ) * z ^ (2 * j + 2))
      (Complex.log (Complex.tan (π * z / 2) / (π * z / 2))) := by
  have e : Complex.log (Complex.tan (π * z / 2) / (π * z / 2)) = Pser z := log_langerU_eq hz
  rw [e]
  exact (Pser_summable (z := z) (by linarith)).hasSum

theorem langer_g_eq_tsum {z : ℂ} (hz : ‖z‖ < 1 / 8) :
    Complex.log (Complex.tan (π * z / 2) / (π * z / 2)) =
      ∑' j : ℕ, ((etaC j / ((j : ℝ) + 1) : ℝ) : ℂ) * z ^ (2 * j + 2) :=
  log_langerU_eq hz

/-- **Langer `g`, derivative** (`‖z‖ < 1/8`): `d/dz log (tan (π z/2)/(π z/2)) = 2 ∑ η_D(2j+2) z^(2j+1)`. -/
theorem langer_g_hasDerivAt {z : ℂ} (hz : ‖z‖ < 1 / 8) :
    HasDerivAt (fun w : ℂ => Complex.log (Complex.tan (π * w / 2) / (π * w / 2)))
      (2 * ∑' j : ℕ, (etaC j : ℂ) * z ^ (2 * j + 1)) z := by
  have hev : (fun w : ℂ => Complex.log (Complex.tan (π * w / 2) / (π * w / 2))) =ᶠ[𝓝 z] Pser := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz)] with w hw
    exact log_langerU_eq (mem_ball_zero_iff.mp hw)
  have h := (Pser_hasDerivAt (y := z) (by linarith)).congr_of_eventuallyEq hev
  have hv : (∑' j : ℕ, 2 * (etaC j : ℂ) * z ^ (2 * j + 1)) =
      2 * ∑' j : ℕ, (etaC j : ℂ) * z ^ (2 * j + 1) := by
    rw [← tsum_mul_left]
    congr 1
    funext j
    ring
  rw [hv] at h
  exact h

/-- info: 'FormalResearch.SignUncertainty.langer_eta_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langer_eta_identity

/-- info: 'FormalResearch.SignUncertainty.langer_g_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langer_g_hasSum

/-- info: 'FormalResearch.SignUncertainty.langer_g_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langer_g_hasDerivAt

/-- info: 'FormalResearch.SignUncertainty.eta_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eta_hasSum

end FormalResearch.SignUncertainty
