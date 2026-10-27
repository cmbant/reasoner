import Mathlib

/-!
# Pure-state Helstrom bound (generic finite-dimensional statement)

Namespace `FormalResearch.FrameFree.Helstrom`.  For unit vectors `a, b` of `ℂ^ι` and a two-outcome test
(effect) `0 ≤ E ≤ 1` the equal-prior error is `err E a b = ½(⟨a|E|a⟩ + ⟨b|(1-E)|b⟩)`.

* `pure_helstrom`: `½(1 - √(1 - |⟨a|b⟩|²)) ≤ err E a b` (Helstrom's bound for pure states; the value is
  attained, but only the lower bound is needed and proved).
* `quarter_le_err`: `|⟨a|b⟩|²/4 ≤ err E a b`.

The proof is elementary (no trace norm, no spectral theorem): the two Cauchy-Schwarz inequalities
`Re⟨a|E|b⟩² ≤ ⟨a|E|a⟩⟨b|E|b⟩` for `E` and for `1 - E` (`cs_re`), applied after aligning the phase of
`⟨a|b⟩`, give `(⟨b|E|b⟩ - ⟨a|E|a⟩)² ≤ 1 - |⟨a|b⟩|²` (`real_ineq`).
-/

open scoped ComplexConjugate Matrix BigOperators
open Matrix
open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace FormalResearch.FrameFree.Helstrom

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sesquilinear form `⟨v|M|w⟩` (conjugate-linear in `v`). -/
def qf (M : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ := star v ⬝ᵥ (M *ᵥ w)

/-- An effect (two-outcome test): `0 ≤ E ≤ 1`. -/
def IsEffect (E : Matrix ι ι ℂ) : Prop := E.PosSemidef ∧ (1 - E).PosSemidef

/-- Equal-prior error of the test with effect `E` ("`b`") against `a`: `½(⟨a|E|a⟩ + ⟨b|(1-E)|b⟩)`. -/
noncomputable def err (E : Matrix ι ι ℂ) (a b : ι → ℂ) : ℝ :=
  (qf E a a).re / 2 + (qf (1 - E) b b).re / 2

theorem qf_add_left (M : Matrix ι ι ℂ) (v v' w : ι → ℂ) : qf M (v + v') w = qf M v w + qf M v' w := by
  simp [qf, star_add, add_dotProduct]

theorem qf_add_right (M : Matrix ι ι ℂ) (v w w' : ι → ℂ) : qf M v (w + w') = qf M v w + qf M v w' := by
  simp [qf, Matrix.mulVec_add, dotProduct_add]

theorem qf_sub_left (M : Matrix ι ι ℂ) (v v' w : ι → ℂ) : qf M (v - v') w = qf M v w - qf M v' w := by
  simp [qf, star_sub, sub_dotProduct]

theorem qf_sub_right (M : Matrix ι ι ℂ) (v w w' : ι → ℂ) : qf M v (w - w') = qf M v w - qf M v w' := by
  simp [qf, Matrix.mulVec_sub, dotProduct_sub]

theorem qf_smul_left (M : Matrix ι ι ℂ) (c : ℂ) (v w : ι → ℂ) : qf M (c • v) w = conj c * qf M v w := by
  simp [qf, star_smul, smul_dotProduct]

theorem qf_smul_right (M : Matrix ι ι ℂ) (c : ℂ) (v w : ι → ℂ) : qf M v (c • w) = c * qf M v w := by
  simp [qf, Matrix.mulVec_smul, dotProduct_smul]

theorem qf_sub_matrix (M N : Matrix ι ι ℂ) (v w : ι → ℂ) : qf (M - N) v w = qf M v w - qf N v w := by
  simp [qf, Matrix.sub_mulVec, dotProduct_sub]

theorem qf_one (v w : ι → ℂ) : qf (1 : Matrix ι ι ℂ) v w = star v ⬝ᵥ w := by
  simp [qf]

/-- Hermitian symmetry. -/
theorem qf_symm {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (v w : ι → ℂ) :
    qf M w v = conj (qf M v w) := by
  unfold qf
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : conj (M j i) = M i j := by
    have := congrFun (congrFun hM i) j
    simpa [Matrix.conjTranspose_apply] using this
  have h' : (starRingEnd ℂ) (M i j) = M j i := by rw [← h]; simp
  simp only [Complex.star_def, Complex.conj_conj, h']
  ring

theorem qf_nonneg {M : Matrix ι ι ℂ} (hM : M.PosSemidef) (v : ι → ℂ) : 0 ≤ qf M v v :=
  hM.dotProduct_mulVec_nonneg v

theorem qf_re_nonneg {M : Matrix ι ι ℂ} (hM : M.PosSemidef) (v : ι → ℂ) : 0 ≤ (qf M v v).re :=
  (Complex.nonneg_iff.1 (qf_nonneg hM v)).1

/-- Cauchy-Schwarz for a positive semidefinite form, real part. -/
theorem cs_re {E : Matrix ι ι ℂ} (hE : E.PosSemidef) (a b : ι → ℂ) :
    (qf E a b).re ^ 2 ≤ (qf E a a).re * (qf E b b).re := by
  have hsym := qf_symm hE.1 a b
  have hre : (qf E b a).re = (qf E a b).re := by rw [hsym]; simp
  have key : ∀ t : ℝ, 0 ≤ (qf E b b).re * (t * t) + (-2 * (qf E a b).re) * t + (qf E a a).re := by
    intro t
    have h0 := qf_re_nonneg hE (a - (t : ℂ) • b)
    have e : qf E (a - (t : ℂ) • b) (a - (t : ℂ) • b)
        = qf E a a - (t : ℂ) * qf E a b - (t : ℂ) * qf E b a + ((t * t : ℝ) : ℂ) * qf E b b := by
      simp only [qf_sub_left, qf_sub_right, qf_smul_left, qf_smul_right, Complex.conj_ofReal]
      push_cast
      ring
    rw [e] at h0
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hre] at h0
    nlinarith [h0]
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith [this]

/-- The real inequality behind Helstrom's bound. -/
theorem real_ineq {x y c r : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hx1 : 0 ≤ 1 - x) (hy1 : 0 ≤ 1 - y)
    (hc : c ^ 2 ≤ x * y) (hc' : (r - c) ^ 2 ≤ (1 - x) * (1 - y)) :
    (y - x) ^ 2 ≤ 1 - r ^ 2 := by
  -- the four nonnegative numbers p, q, p', q'
  have hp : 0 ≤ x + y + 2 * c := by nlinarith [sq_nonneg (x - y), sq_nonneg (x + y + 2 * c), sq_nonneg (x + y - 2 * c)]
  have hp' : 0 ≤ x + y - 2 * c := by nlinarith [sq_nonneg (x - y), sq_nonneg (x + y + 2 * c), sq_nonneg (x + y - 2 * c)]
  have hq : 0 ≤ (1 - x) + (1 - y) + 2 * (r - c) := by
    nlinarith [sq_nonneg ((1 - x) - (1 - y)), sq_nonneg ((1 - x) + (1 - y) + 2 * (r - c)),
      sq_nonneg ((1 - x) + (1 - y) - 2 * (r - c))]
  have hq' : 0 ≤ (1 - x) + (1 - y) - 2 * (r - c) := by
    nlinarith [sq_nonneg ((1 - x) - (1 - y)), sq_nonneg ((1 - x) + (1 - y) + 2 * (r - c)),
      sq_nonneg ((1 - x) + (1 - y) - 2 * (r - c))]
  set p := x + y + 2 * c with hpdef
  set p' := x + y - 2 * c with hp'def
  set q := (1 - x) + (1 - y) + 2 * (r - c) with hqdef
  set q' := (1 - x) + (1 - y) - 2 * (r - c) with hq'def
  set A := y - x with hA
  have h1 : A ^ 2 ≤ p * p' := by rw [hA, hpdef, hp'def]; nlinarith [hc]
  have h2 : A ^ 2 ≤ q * q' := by rw [hA, hqdef, hq'def]; nlinarith [hc']
  have h3 : 2 * A ^ 2 ≤ p * q' + q * p' := by
    have hS : 0 ≤ p * q' := mul_nonneg hp hq'
    have hT : 0 ≤ q * p' := mul_nonneg hq hp'
    have hprod : (A ^ 2) * (A ^ 2) ≤ (p * q') * (q * p') := by
      have := mul_le_mul h1 h2 (sq_nonneg _) (mul_nonneg hp hp')
      calc (A ^ 2) * (A ^ 2) ≤ (p * p') * (q * q') := this
        _ = (p * q') * (q * p') := by ring
    by_contra hcon
    push Not at hcon
    nlinarith [sq_nonneg (p * q' - q * p'), mul_nonneg hS hT, sq_nonneg A]
  have h4 : 4 * A ^ 2 ≤ (p + q) * (p' + q') := by nlinarith [h1, h2, h3]
  have h5 : (p + q) * (p' + q') = 4 * (1 - r ^ 2) := by
    rw [hpdef, hp'def, hqdef, hq'def]; ring
  nlinarith [h4, h5]

/-- Phase alignment: some unimodular `λ` makes `⟨a|λ b⟩` real and nonnegative, equal to `|⟨a|b⟩|`. -/
theorem exists_phase (ω : ℂ) : ∃ l : ℂ, conj l * l = 1 ∧ l * ω = (‖ω‖ : ℂ) := by
  by_cases h : ω = 0
  · exact ⟨1, by simp, by simp [h]⟩
  · have hn : (‖ω‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 h)
    refine ⟨conj ω / (‖ω‖ : ℂ), ?_, ?_⟩
    · have e : ω * conj ω = ((‖ω‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [map_div₀, Complex.conj_ofReal, Complex.conj_conj]
      field_simp
      rw [e]; push_cast; ring
    · have e : ω * conj ω = ((‖ω‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      field_simp
      rw [mul_comm, e]; push_cast; ring

/-- Cauchy-Schwarz for unit vectors, in the form used here. -/
theorem normSq_le_one {a b : ι → ℂ} (ha : star a ⬝ᵥ a = 1) (hb : star b ⬝ᵥ b = 1) :
    Complex.normSq (star a ⬝ᵥ b) ≤ 1 := by
  obtain ⟨l, hl1, hl2⟩ := exists_phase (star a ⬝ᵥ b)
  have := cs_re (E := (1 : Matrix ι ι ℂ)) Matrix.PosSemidef.one a (l • b)
  have hbb : star (l • b) ⬝ᵥ (l • b) = 1 := by
    rw [star_smul, smul_dotProduct, dotProduct_smul, hb]; simp only [smul_eq_mul, mul_one]
    exact hl1
  rw [qf_one, qf_one, qf_one, ha, hbb, dotProduct_smul, smul_eq_mul, hl2] at this
  rw [Complex.normSq_eq_norm_sq]
  simpa using this

/-- **Helstrom's bound for pure states.**  For unit vectors `a, b` and every effect `E`,
`½(1 - √(1 - |⟨a|b⟩|²)) ≤ err E a b`. -/
theorem pure_helstrom {E : Matrix ι ι ℂ} (hE : IsEffect E) {a b : ι → ℂ}
    (ha : star a ⬝ᵥ a = 1) (hb : star b ⬝ᵥ b = 1) :
    (1 - Real.sqrt (1 - Complex.normSq (star a ⬝ᵥ b))) / 2 ≤ err E a b := by
  obtain ⟨l, hl1, hl2⟩ := exists_phase (star a ⬝ᵥ b)
  set r : ℝ := ‖star a ⬝ᵥ b‖ with hr
  set b' : ι → ℂ := l • b with hb'
  have hq1 : ∀ v w : ι → ℂ, qf (1 : Matrix ι ι ℂ) v w = star v ⬝ᵥ w := qf_one
  have hab' : qf (1 : Matrix ι ι ℂ) a b' = (r : ℂ) := by
    rw [hq1, hb', dotProduct_smul, smul_eq_mul]; exact hl2
  have hbb' : ∀ M : Matrix ι ι ℂ, qf M b' b' = qf M b b := by
    intro M
    rw [hb', qf_smul_left, qf_smul_right, ← mul_assoc, hl1, one_mul]
  have hb'1 : qf (1 : Matrix ι ι ℂ) b' b' = 1 := by rw [hbb', hq1]; exact hb
  have ha1 : qf (1 : Matrix ι ι ℂ) a a = 1 := by rw [hq1]; exact ha
  have hr0 : 0 ≤ r := norm_nonneg _
  have hEherm := hE.1.1
  -- Cauchy-Schwarz for E and 1 - E
  have c1 := cs_re hE.1 a b'
  have c2 := cs_re hE.2 a b'
  rw [qf_sub_matrix] at c2
  rw [qf_sub_matrix, qf_sub_matrix] at c2
  rw [hab', ha1, hb'1] at c2
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at c2
  have hx := qf_re_nonneg hE.1 a
  have hy := qf_re_nonneg hE.1 b'
  have hx1 := qf_re_nonneg hE.2 a
  have hy1 := qf_re_nonneg hE.2 b'
  rw [qf_sub_matrix, ha1] at hx1
  rw [qf_sub_matrix, hb'1] at hy1
  simp only [Complex.sub_re, Complex.one_re] at hx1 hy1
  have key := real_ineq hx hy hx1 hy1 c1 c2
  -- unfold the error
  have herr : err E a b = ((qf E a a).re + (1 - (qf E b' b').re)) / 2 := by
    have e : qf (1 - E) b b = 1 - qf E b' b' := by
      rw [qf_sub_matrix, hq1, hb, hbb']
    unfold err
    rw [e]
    simp only [Complex.sub_re, Complex.one_re]
    ring
  have hF : Complex.normSq (star a ⬝ᵥ b) = r ^ 2 := by
    rw [hr, Complex.normSq_eq_norm_sq]
  have hsq : (qf E b' b').re - (qf E a a).re ≤ Real.sqrt (1 - r ^ 2) := Real.le_sqrt_of_sq_le key
  rw [herr, hF]
  linarith

/-- The elementary consequence `|⟨a|b⟩|²/4 ≤ err E a b`. -/
theorem quarter_le_err {E : Matrix ι ι ℂ} (hE : IsEffect E) {a b : ι → ℂ}
    (ha : star a ⬝ᵥ a = 1) (hb : star b ⬝ᵥ b = 1) :
    Complex.normSq (star a ⬝ᵥ b) / 4 ≤ err E a b := by
  refine le_trans ?_ (pure_helstrom hE ha hb)
  set F := Complex.normSq (star a ⬝ᵥ b)
  have hF0 : 0 ≤ F := Complex.normSq_nonneg _
  have hF1 : F ≤ 1 := normSq_le_one ha hb
  have : Real.sqrt (1 - F) ≤ 1 - F / 2 := by
    apply Real.sqrt_le_iff.2
    constructor
    · linarith
    · nlinarith [sq_nonneg F]
  linarith

end FormalResearch.FrameFree.Helstrom
