module

public import FormalResearch.Special.AiryThm47Poly
public import FormalResearch.Special.AiryThm47Nonintegrability

/-!
# Size bounds for `P`, `Q` on the negative axis (input to Theorem 4.7)

With `e := max (2 deg P - 1) (2 deg Q)` (so `at47_m P Q = e + 2`) and `Q ≠ 0`, for `s` large:
`Q(-s)² ≲ s^e`, `P(-s)² ≲ s^{e+1}`, `(s Q'(-s))² ≲ s^e`, `(s P'(-s))² ≲ s^{e+1}` and `Q(-s)² + P(-s)²/s ≳ s^e`.
All proved.
-/

@[expose] public section

open Polynomial

namespace FormalResearch.Special

/-- The exponent `e = max (2 deg P - 1) (2 deg Q)`; `at47_m P Q = e + 2`. -/
def at47_e (P Q : ℝ[X]) : ℕ := max (2 * P.natDegree - 1) (2 * Q.natDegree)

lemma at47_m_eq (P Q : ℝ[X]) : at47_m P Q = at47_e P Q + 2 := by
  unfold at47_m at47_e; omega

lemma at47_sq_le_of_abs {x C s : ℝ} {n k : ℕ} (hs : 1 ≤ s) (hn : 2 * n ≤ k) (h : |x| ≤ C * s ^ n) :
    x ^ 2 ≤ C ^ 2 * s ^ k := by
  rw [← sq_abs]
  have h0 := abs_nonneg x
  calc |x| ^ 2 ≤ (C * s ^ n) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = C ^ 2 * s ^ (2 * n) := by ring
    _ ≤ C ^ 2 * s ^ k := by gcongr

theorem at47_sizes (P Q : ℝ[X]) (hQ : Q ≠ 0) :
    ∃ C c S : ℝ, 0 < C ∧ 0 < c ∧ 1 ≤ S ∧ ∀ s : ℝ, S ≤ s →
      (Q.eval (-s)) ^ 2 ≤ C * s ^ (at47_e P Q) ∧
      (P.eval (-s)) ^ 2 ≤ C * s ^ (at47_e P Q + 1) ∧
      (s * (derivative Q).eval (-s)) ^ 2 ≤ C * s ^ (at47_e P Q) ∧
      (s * (derivative P).eval (-s)) ^ 2 ≤ C * s ^ (at47_e P Q + 1) ∧
      c * s ^ (at47_e P Q) ≤ (Q.eval (-s)) ^ 2 + (P.eval (-s)) ^ 2 / s := by
  obtain ⟨CQ, hCQ, hQu⟩ := at47_poly_upper Q le_rfl
  obtain ⟨CP, hCP, hPu⟩ := at47_poly_upper P le_rfl
  obtain ⟨CQ', hCQ', hQ'u⟩ := at47_poly_deriv_upper Q
  obtain ⟨CP', hCP', hP'u⟩ := at47_poly_deriv_upper P
  obtain ⟨cQ, SQ, hcQ, hSQ, hQl⟩ := at47_poly_lower hQ
  have he1 : 2 * Q.natDegree ≤ at47_e P Q := le_max_right _ _
  have he2 : 2 * P.natDegree ≤ at47_e P Q + 1 := by unfold at47_e; omega
  set C : ℝ := CQ ^ 2 + CP ^ 2 + CQ' ^ 2 + CP' ^ 2 + 1 with hC
  have hCpos : 0 < C := by positivity
  -- lower bound constant
  by_cases hcase : 2 * P.natDegree - 1 ≤ 2 * Q.natDegree
  · have he : at47_e P Q = 2 * Q.natDegree := by unfold at47_e; omega
    refine ⟨C, cQ ^ 2, SQ, hCpos, by positivity, hSQ, fun s hs => ?_⟩
    have hs1 : 1 ≤ s := hSQ.trans hs
    have hs0 : 0 < s := by linarith
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have := at47_sq_le_of_abs hs1 he1 (hQu s hs1)
      calc _ ≤ CQ ^ 2 * s ^ at47_e P Q := this
        _ ≤ _ := by gcongr; unfold C; linarith [sq_nonneg CP, sq_nonneg CQ', sq_nonneg CP']
    · have := at47_sq_le_of_abs hs1 he2 (hPu s hs1)
      calc _ ≤ CP ^ 2 * s ^ (at47_e P Q + 1) := this
        _ ≤ _ := by gcongr; unfold C; linarith [sq_nonneg CQ, sq_nonneg CQ', sq_nonneg CP']
    · have h := hQ'u s hs1
      have h' : |s * (derivative Q).eval (-s)| ≤ CQ' * s ^ Q.natDegree := by
        rw [abs_mul, abs_of_nonneg hs0.le]; exact h
      have := at47_sq_le_of_abs hs1 he1 h'
      calc _ ≤ CQ' ^ 2 * s ^ at47_e P Q := this
        _ ≤ _ := by gcongr; unfold C; linarith [sq_nonneg CP, sq_nonneg CQ, sq_nonneg CP']
    · have h := hP'u s hs1
      have h' : |s * (derivative P).eval (-s)| ≤ CP' * s ^ P.natDegree := by
        rw [abs_mul, abs_of_nonneg hs0.le]; exact h
      have := at47_sq_le_of_abs hs1 he2 h'
      calc _ ≤ CP' ^ 2 * s ^ (at47_e P Q + 1) := this
        _ ≤ _ := by gcongr; unfold C; linarith [sq_nonneg CP, sq_nonneg CQ, sq_nonneg CQ']
    · have h := hQl s hs
      have h2 : (cQ * s ^ Q.natDegree) ^ 2 ≤ |Q.eval (-s)| ^ 2 := pow_le_pow_left₀ (by positivity) h 2
      rw [sq_abs] at h2
      have : cQ ^ 2 * s ^ at47_e P Q = (cQ * s ^ Q.natDegree) ^ 2 := by rw [he]; ring
      rw [this]
      have : 0 ≤ (P.eval (-s)) ^ 2 / s := by positivity
      linarith
  · have he : at47_e P Q = 2 * P.natDegree - 1 := by unfold at47_e; omega
    have hdP : 1 ≤ P.natDegree := by omega
    have hP0 : P ≠ 0 := by rintro rfl; simp at hdP
    obtain ⟨cP, SP, hcP, hSP, hPl⟩ := at47_poly_lower hP0
    refine ⟨C, cP ^ 2, max SP SQ, hCpos, by positivity, hSP.trans (le_max_left _ _), fun s hs => ?_⟩
    have hs1 : 1 ≤ s := hSP.trans ((le_max_left _ _).trans hs)
    have hs0 : 0 < s := by linarith
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have := at47_sq_le_of_abs hs1 he1 (hQu s hs1)
      calc _ ≤ CQ ^ 2 * s ^ at47_e P Q := this
        _ ≤ _ := by gcongr; unfold C; linarith [sq_nonneg CP, sq_nonneg CQ', sq_nonneg CP']
    · have := at47_sq_le_of_abs hs1 he2 (hPu s hs1)
      calc _ ≤ CP ^ 2 * s ^ (at47_e P Q + 1) := this
        _ ≤ _ := by gcongr; unfold C; linarith [sq_nonneg CQ, sq_nonneg CQ', sq_nonneg CP']
    · have h := hQ'u s hs1
      have h' : |s * (derivative Q).eval (-s)| ≤ CQ' * s ^ Q.natDegree := by
        rw [abs_mul, abs_of_nonneg hs0.le]; exact h
      have := at47_sq_le_of_abs hs1 he1 h'
      calc _ ≤ CQ' ^ 2 * s ^ at47_e P Q := this
        _ ≤ _ := by gcongr; unfold C; linarith [sq_nonneg CP, sq_nonneg CQ, sq_nonneg CP']
    · have h := hP'u s hs1
      have h' : |s * (derivative P).eval (-s)| ≤ CP' * s ^ P.natDegree := by
        rw [abs_mul, abs_of_nonneg hs0.le]; exact h
      have := at47_sq_le_of_abs hs1 he2 h'
      calc _ ≤ CP' ^ 2 * s ^ (at47_e P Q + 1) := this
        _ ≤ _ := by gcongr; unfold C; linarith [sq_nonneg CP, sq_nonneg CQ, sq_nonneg CQ']
    · have h := hPl s ((le_max_left _ _).trans hs)
      have h2 : (cP * s ^ P.natDegree) ^ 2 ≤ |P.eval (-s)| ^ 2 := pow_le_pow_left₀ (by positivity) h 2
      rw [sq_abs] at h2
      have : cP ^ 2 * s ^ at47_e P Q = (cP * s ^ P.natDegree) ^ 2 / s := by
        rw [he]; obtain ⟨k, hk⟩ : ∃ k, P.natDegree = k + 1 := ⟨P.natDegree - 1, by omega⟩
        rw [hk]; field_simp
        have : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
        rw [this]; ring
      rw [this]
      have : 0 ≤ (Q.eval (-s)) ^ 2 := sq_nonneg _
      have h3 : (cP * s ^ P.natDegree) ^ 2 / s ≤ (P.eval (-s)) ^ 2 / s := by gcongr
      linarith

/-- info: 'FormalResearch.Special.at47_sizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.at47_sizes

end FormalResearch.Special
