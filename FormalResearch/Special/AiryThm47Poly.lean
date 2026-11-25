module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Polynomial growth on the negative axis (input to Theorem 4.7)

Elementary two-sided growth bounds for a real polynomial `T` of degree `d` at `x = -s`, `s → ∞`:
`|T(-s)| ≤ C s^d`, `s |T'(-s)| ≤ C s^d` for `s ≥ 1`, and `|T(-s)| ≥ c s^d` for `s ≥ S` when `T ≠ 0`.
All proved.
-/

@[expose] public section

open Polynomial Filter Topology

namespace FormalResearch.Special

lemma at47_poly_upper (T : ℝ[X]) {n : ℕ} (hn : T.natDegree ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 ≤ s → |T.eval (-s)| ≤ C * s ^ n := by
  refine ⟨∑ k ∈ Finset.range (T.natDegree + 1), |T.coeff k|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun s hs => ?_⟩
  rw [Polynomial.eval_eq_sum_range]
  calc |∑ k ∈ Finset.range (T.natDegree + 1), T.coeff k * (-s) ^ k|
      ≤ ∑ k ∈ Finset.range (T.natDegree + 1), |T.coeff k * (-s) ^ k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (T.natDegree + 1), |T.coeff k| * s ^ n := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
        rw [abs_mul, abs_pow, abs_neg, abs_of_nonneg (by linarith : 0 ≤ s)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hs hk') (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

lemma at47_poly_deriv_upper (T : ℝ[X]) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 ≤ s → s * |(derivative T).eval (-s)| ≤ C * s ^ T.natDegree := by
  rcases Nat.eq_zero_or_pos T.natDegree with h0 | hpos
  · have : derivative T = 0 := Polynomial.derivative_of_natDegree_zero h0
    exact ⟨0, le_rfl, fun s _ => by simp [this]⟩
  · obtain ⟨C, hC, h⟩ := at47_poly_upper (derivative T) (n := T.natDegree - 1) (by
      have := Polynomial.natDegree_derivative_le T; omega)
    refine ⟨C, hC, fun s hs => ?_⟩
    have := h s hs
    calc s * |(derivative T).eval (-s)| ≤ s * (C * s ^ (T.natDegree - 1)) := by gcongr
      _ = C * s ^ T.natDegree := by
        obtain ⟨k, hk⟩ : ∃ k, T.natDegree = k + 1 := ⟨T.natDegree - 1, by omega⟩
        rw [hk]; simp [pow_succ]; ring

lemma at47_poly_lower {T : ℝ[X]} (hT : T ≠ 0) :
    ∃ c S : ℝ, 0 < c ∧ 1 ≤ S ∧ ∀ s : ℝ, S ≤ s → c * s ^ T.natDegree ≤ |T.eval (-s)| := by
  have hne : (T.comp (-X)) ≠ 0 := by
    intro h
    have := Polynomial.comp_eq_zero_iff.mp h
    rcases this with h | ⟨h1, h2⟩
    · exact hT h
    · have := congrArg (fun q => q.coeff 1) h2; simp at this
  have hdeg : (T.comp (-X)).natDegree = T.natDegree := by
    rw [Polynomial.natDegree_comp]; simp
  have hlc : (T.comp (-X)).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hne
  have heq := Polynomial.isEquivalent_atTop_lead (T.comp (-X))
  have hlo := heq.isLittleO.def (c := 1 / 2) (by norm_num)
  have hev := hlo.and (Filter.eventually_ge_atTop (1 : ℝ))
  obtain ⟨S, hS⟩ := Filter.eventually_atTop.mp hev
  refine ⟨|(T.comp (-X)).leadingCoeff| / 2, max S 1, by positivity, le_max_right _ _, fun s hs => ?_⟩
  obtain ⟨h1, h2⟩ := hS s ((le_max_left _ _).trans hs)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Pi.sub_apply] at h1
  have hev' : (T.comp (-X)).eval s = T.eval (-s) := by simp
  simp only [hev', hdeg] at h1
  have hv : |(T.comp (-X)).leadingCoeff * s ^ T.natDegree| = |(T.comp (-X)).leadingCoeff| * s ^ T.natDegree := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ s ^ T.natDegree)]
  rw [hv] at h1
  have := abs_sub_abs_le_abs_sub ((T.comp (-X)).leadingCoeff * s ^ T.natDegree) (T.eval (-s))
  rw [hv, abs_sub_comm] at this
  linarith

/-- Lower growth bound for a nonzero complex polynomial: `c ‖z‖^d ≤ ‖p(z)‖` for `‖z‖ ≥ S`. -/
lemma at47_cpoly_lower {p : ℂ[X]} (hp : p ≠ 0) :
    ∃ c S : ℝ, 0 < c ∧ 1 ≤ S ∧ ∀ z : ℂ, S ≤ ‖z‖ → c * ‖z‖ ^ p.natDegree ≤ ‖p.eval z‖ := by
  set d := p.natDegree with hd
  set a : ℝ := ‖p.leadingCoeff‖ with ha
  have ha0 : 0 < a := norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)
  set B : ℝ := ∑ k ∈ Finset.range d, ‖p.coeff k‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨a / 2, max 1 (2 * B / a), by positivity, le_max_left _ _, fun z hz => ?_⟩
  have hr1 : 1 ≤ ‖z‖ := (le_max_left _ _).trans hz
  have hr2 : 2 * B / a ≤ ‖z‖ := (le_max_right _ _).trans hz
  set r := ‖z‖ with hr
  have hsum : p.eval z = ∑ k ∈ Finset.range d, p.coeff k * z ^ k + p.leadingCoeff * z ^ d := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ]; rfl
  have hlow : ‖∑ k ∈ Finset.range d, p.coeff k * z ^ k‖ ≤ B * r ^ (d - 1) := by
    calc ‖∑ k ∈ Finset.range d, p.coeff k * z ^ k‖ ≤ ∑ k ∈ Finset.range d, ‖p.coeff k * z ^ k‖ :=
          norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range d, ‖p.coeff k‖ * r ^ (d - 1) := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [norm_mul, norm_pow]
          have : k ≤ d - 1 := by have := Finset.mem_range.mp hk; omega
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr1 this) (norm_nonneg _)
      _ = _ := by rw [Finset.sum_mul]
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · rw [h0] at hB ⊢
    simp at hB
    have hz1 : ‖p.eval z‖ = a := by
      rw [hsum, h0]; simp [ha]
    rw [hz1]; simp; linarith
  · have hlead : ‖p.leadingCoeff * z ^ d‖ = a * r ^ d := by rw [norm_mul, norm_pow]
    have h1 : a * r ^ d - B * r ^ (d - 1) ≤ ‖p.eval z‖ := by
      rw [hsum]
      have := norm_sub_norm_le (p.leadingCoeff * z ^ d) (-(∑ k ∈ Finset.range d, p.coeff k * z ^ k))
      rw [norm_neg, sub_neg_eq_add, add_comm] at this
      linarith
    have h2 : B * r ^ (d - 1) ≤ a / 2 * r ^ d := by
      have hrd : r ^ d = r * r ^ (d - 1) := by
        rw [← pow_succ']; congr 1; omega
      have : 2 * B ≤ a * r := by rw [div_le_iff₀ ha0] at hr2; linarith
      rw [hrd]
      have hp0 : 0 ≤ r ^ (d - 1) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right this hp0]
    linarith

end FormalResearch.Special
