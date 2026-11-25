module

public import FormalResearch.SignUncertainty.HankelLangerIdentity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Mittag-Leffler series of `π/sin(π z)` off the real axis, and of `m'(t)` (support for `ct:outer` (2))

Generic.  **Proved.**  `csc_hasSum_im`: for `Im z ≠ 0`,
`π / sin(π z) - 1/z = ∑_{n≥0} 2 (-1)^n z / ((n+1)² - z²)` (the restriction `‖z‖ < 1` of `csc_hasSum` is dropped; the
proof is the same, with `Im z ≠ 0` giving all non-vanishing conditions).  `hasSum_mPrime`: for `t > 0`,
`1/t - π/sinh(πt) = ∑_{n≥0} 2 (-1)^n t / ((n+1)² + t²)`.
-/

@[expose] public section

open Finset Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty

lemma im_ne_zero_notMem_int {w : ℂ} (hw : w.im ≠ 0) (k : ℤ) : w ≠ (k : ℂ) := by
  intro h; apply hw; rw [h]; simp

lemma sin_pi_ne_zero_of_im {w : ℂ} (hw : w.im ≠ 0) : Complex.sin (π * w) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  apply im_ne_zero_notMem_int hw k
  have h' : (π : ℂ) * (w - k) = 0 := by linear_combination hk
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact absurd h1 pi_ne_zero_c
  · exact sub_eq_zero.mp h1

lemma cos_pi_ne_zero_of_im {w : ℂ} (hw : w.im ≠ 0) : Complex.cos (π * w) ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp h
  apply hw
  have := congrArg Complex.im hk
  simpa using this

lemma mem_integerComplement_of_im {x : ℂ} (hx : x.im ≠ 0) : x ∈ Complex.integerComplement := by
  rw [Complex.integerComplement, Set.mem_compl_iff, Set.mem_range]
  rintro ⟨n, hn⟩
  apply hx; rw [← hn]; simp

lemma sub_add_ne_of_im {x : ℂ} (hx : x.im ≠ 0) (m : ℕ) :
    x - ((m : ℂ) + 1) ≠ 0 ∧ x + ((m : ℂ) + 1) ≠ 0 := by
  constructor
  · intro h; apply hx; have := congrArg Complex.im h; simpa using this
  · intro h; apply hx; have := congrArg Complex.im h; simpa using this

lemma cotTerm_half_im {z : ℂ} (hz : z.im ≠ 0) (n : ℕ) :
    cotTerm (z / 2) n = 2 * cotTerm z (2 * n + 1) := by
  have hz2 : (z / 2).im ≠ 0 := by simpa using hz
  obtain ⟨a1, a2⟩ := sub_add_ne_of_im hz2 n
  obtain ⟨b1, b2⟩ := sub_add_ne_of_im hz (2 * n + 1)
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

lemma csc_hasSum_im {z : ℂ} (hz : z.im ≠ 0) :
    HasSum (fun n : ℕ => 2 * (-1 : ℂ) ^ n * z / (((n : ℂ) + 1) ^ 2 - z ^ 2))
      (π / Complex.sin (π * z) - 1 / z) := by
  have hz0 : z ≠ 0 := fun h => hz (by simp [h])
  have hz2 : (z / 2).im ≠ 0 := by simpa using hz
  have hzM : z ∈ Complex.integerComplement := mem_integerComplement_of_im hz
  have hz2M : z / 2 ∈ Complex.integerComplement := mem_integerComplement_of_im hz2
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
    rw [← tsum_mul_left]; congr 1; funext n; exact cotTerm_half_im hz n
  have c1 : π * Complex.cot (π * (z / 2)) - 1 / (z / 2) = ∑' n, cotTerm (z / 2) n :=
    cot_series_rep' hz2M
  have c2 : π * Complex.cot (π * z) - 1 / z = ∑' n, cotTerm z n := cot_series_rep' hzM
  have hcsc : π / Complex.sin (π * z) =
      π * Complex.cot (π * (z / 2)) - π * Complex.cot (π * z) := by
    have hb := cot_sub_cot_double (b := π * (z / 2)) (sin_pi_ne_zero_of_im hz2)
      (cos_pi_ne_zero_of_im hz2)
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
    obtain ⟨a1, a2⟩ := sub_add_ne_of_im hz n
    simp only [hFdef]
    rw [cotTerm_closed n a1 a2]
    have hne : ((n : ℂ) + 1) ^ 2 - z ^ 2 = -(z ^ 2 - ((n : ℂ) + 1) ^ 2) := by ring
    rw [hne, div_neg]
    ring
  rw [hfun, hval]
  exact hF.hasSum.neg

/-- `1/t - π/sinh(πt) = ∑_{n≥0} 2 (-1)^n t/((n+1)²+t²)` for `t > 0`. -/
theorem hasSum_mPrime {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => 2 * (-1 : ℝ) ^ n * t / (((n : ℝ) + 1) ^ 2 + t ^ 2))
      (1 / t - π / Real.sinh (π * t)) := by
  have hz : (Complex.I * (t : ℂ)).im ≠ 0 := by simpa using ht.ne'
  have h := csc_hasSum_im hz
  have hs : Real.sinh (π * t) ≠ 0 := by
    have h0 : 0 < π * t := by positivity
    exact (Real.sinh_pos_iff.mpr h0).ne'
  have hsC : (Real.sinh (π * t) : ℂ) ≠ 0 := by exact_mod_cast hs
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hsin : Complex.sin (π * (Complex.I * t)) = (Real.sinh (π * t) : ℂ) * Complex.I := by
    rw [show (π : ℂ) * (Complex.I * t) = ((π * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.sin_mul_I, ← Complex.ofReal_sinh]
  have hval : (π : ℂ) / Complex.sin (π * (Complex.I * t)) - 1 / (Complex.I * t) =
      Complex.I * ((1 / t - π / Real.sinh (π * t) : ℝ) : ℂ) := by
    rw [hsin]
    push_cast
    field_simp
    simp [Complex.I_sq]
  have h2 := h.mul_left (-Complex.I)
  have hfun : (fun n : ℕ => -Complex.I * (2 * (-1 : ℂ) ^ n * (Complex.I * t) /
      (((n : ℂ) + 1) ^ 2 - (Complex.I * t) ^ 2))) =
      fun n : ℕ => ((2 * (-1 : ℝ) ^ n * t / (((n : ℝ) + 1) ^ 2 + t ^ 2) : ℝ) : ℂ) := by
    funext n
    push_cast
    have : ((n : ℂ) + 1) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by
      have : ((n : ℝ) + 1) ^ 2 + t ^ 2 ≠ 0 := by positivity
      exact_mod_cast this
    have e : ((n : ℂ) + 1) ^ 2 - (Complex.I * t) ^ 2 = ((n : ℂ) + 1) ^ 2 + (t : ℂ) ^ 2 := by
      rw [mul_pow, Complex.I_sq]; ring
    rw [e]
    field_simp
    simp [Complex.I_sq]
  rw [hfun, hval] at h2
  have h3 : -Complex.I * (Complex.I * ((1 / t - π / Real.sinh (π * t) : ℝ) : ℂ)) =
      ((1 / t - π / Real.sinh (π * t) : ℝ) : ℂ) := by
    rw [← mul_assoc]; simp
  rw [h3] at h2
  exact Complex.hasSum_ofReal.mp h2

/-- info: 'FormalResearch.SignUncertainty.hasSum_mPrime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasSum_mPrime

end FormalResearch.SignUncertainty
