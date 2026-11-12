module

public import FormalResearch.Wigner.SixJRecurrence
public import FormalResearch.Wigner.Rec3j
public import FormalResearch.Wigner.Rec3m

/-!
# The Wigner `3j` symbol and its recurrence in `j₁` (DLMF 34.3.15)

`threeJ` is Racah's formula (DLMF 34.2.4, 34.2.5).  `threeJ_recurrence` is DLMF 34.3.15, obtained
from the rational recurrence `racahSum3_recurrence` by absorbing the square roots, exactly as for
the `6j` symbol (`EW3_plus`, `EW3_minus`).
-/

@[expose] public section

namespace FormalResearch.Wigner

open Classical in
/-- `(-1)^x` for a rational `x` that is an integer, and `0` otherwise. -/
noncomputable def sgn (x : ℚ) : ℝ :=
  if h : ∃ n : ℤ, x = n then (-1 : ℝ) ^ h.choose else 0

/-- The Wigner `3j` symbol `(j₁ j₂ j₃; m₁ m₂ m₃)` by Racah's formula (DLMF 34.2.4, 34.2.5). -/
noncomputable def threeJ (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) : ℝ :=
  if m₁ + m₂ + m₃ = 0 then
    sgn (j₁ - j₂ - m₃) * Real.sqrt (triSq j₁ j₂ j₃) *
      Real.sqrt (fq (j₁ + m₁) * fq (j₁ - m₁) * fq (j₂ + m₂) * fq (j₂ - m₂) *
        fq (j₃ + m₃) * fq (j₃ - m₃)) * racahSum3 j₁ j₂ j₃ m₁ m₂
  else 0

lemma sgn_add_one (x : ℚ) : sgn (x + 1) = - sgn x := by
  unfold sgn
  by_cases h : ∃ n : ℤ, x = n
  · obtain ⟨n, rfl⟩ := h
    have h' : ∃ m : ℤ, ((n : ℚ) + 1) = m := ⟨n + 1, by push_cast; ring⟩
    rw [dif_pos h', dif_pos ⟨n, rfl⟩]
    have e1 : h'.choose = n + 1 := by exact_mod_cast h'.choose_spec.symm
    have e2 : (⟨n, rfl⟩ : ∃ m : ℤ, (n : ℚ) = m).choose = n := by
      exact_mod_cast (Exists.choose_spec (⟨n, rfl⟩ : ∃ m : ℤ, (n : ℚ) = m)).symm
    rw [e1, e2, zpow_add_one₀ (by norm_num)]; ring
  · have h' : ¬ ∃ m : ℤ, x + 1 = m := by
      rintro ⟨m, hm⟩; exact h ⟨m - 1, by push_cast; linarith⟩
    rw [dif_neg h', dif_neg h]; simp

lemma sgn_sub_one (x : ℚ) : sgn (x - 1) = - sgn x := by
  have := sgn_add_one (x - 1)
  rw [sub_add_cancel] at this
  linarith

lemma fq_nonneg (x : ℚ) : 0 ≤ fq x := by
  unfold fq; split_ifs <;> positivity

/-- DLMF 34.3.15's square root. -/
noncomputable def E3 (j₂ j₃ m₁ x : ℝ) : ℝ :=
  Real.sqrt ((x ^ 2 - (j₂ - j₃) ^ 2) * ((j₂ + j₃ + 1) ^ 2 - x ^ 2) * (x ^ 2 - m₁ ^ 2))


lemma fq_succ' {x y : ℚ} (h : IsNat x) (hxy : y = x + 1) : fq y = ((x : ℝ) + 1) * fq x := by
  subst hxy; exact fq_succ h

/-- `E₃(f+1) W(f+1) = ρ₊ W(f)` with `W(F) = Δ(F,j₂,j₃) √((F+m₁)!(F-m₁)!)`. -/
lemma EW3_plus {f j₂ j₃ m₁ : ℚ} (h : IsTri f j₂ j₃) (hp : IsTri (f + 1) j₂ j₃)
    (hm1 : IsNat (f + m₁)) (hm2 : IsNat (f - m₁)) :
    E3 j₂ j₃ m₁ ((f : ℝ) + 1) *
        (Real.sqrt (triSq (f + 1) j₂ j₃) * Real.sqrt (fq (f + 1 + m₁) * fq (f + 1 - m₁))) =
      (((f : ℝ) + 1 + j₂ - j₃) * ((f : ℝ) + 1 - j₂ + j₃) * ((f : ℝ) + 1 + m₁) *
        ((f : ℝ) + 1 - m₁)) *
        (Real.sqrt (triSq f j₂ j₃) * Real.sqrt (fq (f + m₁) * fq (f - m₁))) := by
  have hsq := triSq_succ_mul h hp
  have e1 : fq (f + 1 + m₁) = ((f : ℝ) + m₁ + 1) * fq (f + m₁) := by
    have := fq_succ' hm1 (y := f + 1 + m₁) (by ring)
    rw [this]; push_cast; ring
  have e2 : fq (f + 1 - m₁) = ((f : ℝ) - m₁ + 1) * fq (f - m₁) := by
    have := fq_succ' hm2 (y := f + 1 - m₁) (by ring)
    rw [this]; push_cast; ring
  have ha := hp.1.nonneg_real
  have hb := hp.2.1.nonneg_real
  have hu := hp.2.2.nonneg_real
  have hs := h.sum_nonneg
  have hm1' := hm1.nonneg_real
  have hm2' := hm2.nonneg_real
  push_cast at ha hb hu hs hm1' hm2'
  have hA := (triSq_pos hp).le
  have hA' := (triSq_pos h).le
  have hG := mul_nonneg (fq_nonneg (f + 1 + m₁)) (fq_nonneg (f + 1 - m₁))
  have hG' := mul_nonneg (fq_nonneg (f + m₁)) (fq_nonneg (f - m₁))
  have e : (((f : ℝ) + 1) ^ 2 - ((j₂ : ℝ) - j₃) ^ 2) *
      (((j₂ : ℝ) + j₃ + 1) ^ 2 - ((f : ℝ) + 1) ^ 2) * (((f : ℝ) + 1) ^ 2 - (m₁ : ℝ) ^ 2) =
      (((f : ℝ) + 1 + j₂ - j₃) * ((f : ℝ) + 1 - j₂ + j₃)) *
        (((j₂ : ℝ) + j₃ - f) * ((f : ℝ) + j₂ + j₃ + 2)) *
        (((f : ℝ) + 1 + m₁) * ((f : ℝ) + 1 - m₁)) := by ring
  have hP : (0 : ℝ) ≤ (((f : ℝ) + 1) ^ 2 - ((j₂ : ℝ) - j₃) ^ 2) *
      (((j₂ : ℝ) + j₃ + 1) ^ 2 - ((f : ℝ) + 1) ^ 2) * (((f : ℝ) + 1) ^ 2 - (m₁ : ℝ) ^ 2) := by
    rw [e]
    have : 0 ≤ ((j₂ : ℝ) + j₃ - f) := by linarith
    have : 0 ≤ (f : ℝ) + 1 + m₁ := by linarith
    have : 0 ≤ (f : ℝ) + 1 - m₁ := by linarith
    positivity
  have hρ : 0 ≤ ((f : ℝ) + 1 + j₂ - j₃) * ((f : ℝ) + 1 - j₂ + j₃) * ((f : ℝ) + 1 + m₁) *
      ((f : ℝ) + 1 - m₁) := by
    have : 0 ≤ (f : ℝ) + 1 + m₁ := by linarith
    have : 0 ≤ (f : ℝ) + 1 - m₁ := by linarith
    positivity
  apply sqrt_mul_sq_eq (Real.sqrt_nonneg _) hρ hA hG hA' hG'
  rw [Real.sq_sqrt hP, e, e1, e2]
  linear_combination
    (((f : ℝ) + 1 + j₂ - j₃) * ((f : ℝ) + 1 - j₂ + j₃) *
      (((f : ℝ) + 1 + m₁) * ((f : ℝ) + 1 - m₁)) * ((f : ℝ) + m₁ + 1) * ((f : ℝ) - m₁ + 1) *
      (fq (f + m₁) * fq (f - m₁))) * hsq

/-- `E₃(f) W(f-1) = ρ₋ W(f)`. -/
lemma EW3_minus {f j₂ j₃ m₁ : ℚ} (h : IsTri f j₂ j₃) (hm : IsTri (f - 1) j₂ j₃)
    (hm1 : IsNat (f - 1 + m₁)) (hm2 : IsNat (f - 1 - m₁)) :
    E3 j₂ j₃ m₁ (f : ℝ) *
        (Real.sqrt (triSq (f - 1) j₂ j₃) * Real.sqrt (fq (f - 1 + m₁) * fq (f - 1 - m₁))) =
      (((j₂ : ℝ) + j₃ + 1 - f) * ((f : ℝ) + j₂ + j₃ + 1)) *
        (Real.sqrt (triSq f j₂ j₃) * Real.sqrt (fq (f + m₁) * fq (f - m₁))) := by
  have hsq := triSq_pred_mul h hm
  have e1 : fq (f + m₁) = ((f : ℝ) + m₁) * fq (f - 1 + m₁) := by
    have := fq_succ' hm1 (y := f + m₁) (by ring)
    rw [this]; push_cast; ring
  have e2 : fq (f - m₁) = ((f : ℝ) - m₁) * fq (f - 1 - m₁) := by
    have := fq_succ' hm2 (y := f - m₁) (by ring)
    rw [this]; push_cast; ring
  have hp := h.1.nonneg_real
  have hq := h.2.1.nonneg_real
  have hr := hm.2.2.nonneg_real
  have hs := h.sum_nonneg
  have hm1' := hm1.nonneg_real
  have hm2' := hm2.nonneg_real
  push_cast at hp hq hr hs hm1' hm2'
  have hA := (triSq_pos hm).le
  have hA' := (triSq_pos h).le
  have hG := mul_nonneg (fq_nonneg (f - 1 + m₁)) (fq_nonneg (f - 1 - m₁))
  have hG' := mul_nonneg (fq_nonneg (f + m₁)) (fq_nonneg (f - m₁))
  have e : ((f : ℝ) ^ 2 - ((j₂ : ℝ) - j₃) ^ 2) * (((j₂ : ℝ) + j₃ + 1) ^ 2 - (f : ℝ) ^ 2) *
      ((f : ℝ) ^ 2 - (m₁ : ℝ) ^ 2) =
      (((f : ℝ) + j₂ - j₃) * ((f : ℝ) - j₂ + j₃)) *
        (((j₂ : ℝ) + j₃ + 1 - f) * ((j₂ : ℝ) + j₃ + 1 + f)) *
        (((f : ℝ) + m₁) * ((f : ℝ) - m₁)) := by ring
  have h1 : 0 ≤ (f : ℝ) + m₁ := by linarith
  have h2 : 0 ≤ (f : ℝ) - m₁ := by linarith
  have h3 : 0 ≤ (j₂ : ℝ) + j₃ + 1 - f := by linarith
  have h4 : 0 ≤ (j₂ : ℝ) + j₃ + 1 + f := by linarith
  have hP : (0 : ℝ) ≤ ((f : ℝ) ^ 2 - ((j₂ : ℝ) - j₃) ^ 2) *
      (((j₂ : ℝ) + j₃ + 1) ^ 2 - (f : ℝ) ^ 2) * ((f : ℝ) ^ 2 - (m₁ : ℝ) ^ 2) := by
    rw [e]; positivity
  have hρ : 0 ≤ ((j₂ : ℝ) + j₃ + 1 - f) * ((f : ℝ) + j₂ + j₃ + 1) := by
    have : 0 ≤ (f : ℝ) + j₂ + j₃ + 1 := by linarith
    positivity
  apply sqrt_mul_sq_eq (Real.sqrt_nonneg _) hρ hA hG hA' hG'
  rw [Real.sq_sqrt hP, e, e1, e2]
  linear_combination
    (((j₂ : ℝ) + j₃ + 1 - f) * ((j₂ : ℝ) + j₃ + 1 + f) *
      (((f : ℝ) + m₁) * ((f : ℝ) - m₁)) * (fq (f - 1 + m₁) * fq (f - 1 - m₁))) * hsq


lemma threeJ_factor {j₁ j₂ j₃ m₁ m₂ m₃ : ℚ} (hm : m₁ + m₂ + m₃ = 0) :
    threeJ j₁ j₂ j₃ m₁ m₂ m₃ =
      sgn (j₁ - j₂ - m₃) * (Real.sqrt (triSq j₁ j₂ j₃) *
        Real.sqrt (fq (j₁ + m₁) * fq (j₁ - m₁))) *
        Real.sqrt (fq (j₂ + m₂) * fq (j₂ - m₂) * fq (j₃ + m₃) * fq (j₃ - m₃)) *
        racahSum3 j₁ j₂ j₃ m₁ m₂ := by
  unfold threeJ
  rw [if_pos hm, show fq (j₁ + m₁) * fq (j₁ - m₁) * fq (j₂ + m₂) * fq (j₂ - m₂) *
      fq (j₃ + m₃) * fq (j₃ - m₃) = (fq (j₁ + m₁) * fq (j₁ - m₁)) *
      (fq (j₂ + m₂) * fq (j₂ - m₂) * fq (j₃ + m₃) * fq (j₃ - m₃)) by ring,
    Real.sqrt_mul (mul_nonneg (fq_nonneg _) (fq_nonneg _))]
  ring

/-- **DLMF 34.3.15** (three-term recurrence of the `3j` symbol in `j₁`) under the triangle and
projection conditions that DLMF assumes for the three symbols involved. -/
theorem threeJ_recurrence (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) (hm : m₁ + m₂ + m₃ = 0)
    (h : IsTri j₁ j₂ j₃) (hp : IsTri (j₁ + 1) j₂ j₃) (hmn : IsTri (j₁ - 1) j₂ j₃)
    (h1 : IsNat (j₁ + m₁)) (h2 : IsNat (j₁ - m₁)) (h3 : IsNat (j₁ - 1 + m₁))
    (h4 : IsNat (j₁ - 1 - m₁)) :
    (2 * (j₁ : ℝ) + 1) * ((((j₂ : ℝ) * (j₂ + 1) - j₃ * (j₃ + 1)) * m₁ -
        j₁ * (j₁ + 1) * ((m₃ : ℝ) - m₂))) * threeJ j₁ j₂ j₃ m₁ m₂ m₃ =
      ((j₁ : ℝ) + 1) * E3 j₂ j₃ m₁ (j₁ : ℝ) * threeJ (j₁ - 1) j₂ j₃ m₁ m₂ m₃
        + (j₁ : ℝ) * E3 j₂ j₃ m₁ ((j₁ : ℝ) + 1) * threeJ (j₁ + 1) j₂ j₃ m₁ m₂ m₃ := by
  have hrec := racahSum3_recurrence j₁ j₂ j₃ m₁ m₂
  have em3 : (m₃ : ℝ) = -(m₁ : ℝ) - m₂ := by
    have : (m₃ : ℚ) = -m₁ - m₂ := by linarith
    rw [this]; push_cast; ring
  have ep := EW3_plus h hp h1 h2
  have emn := EW3_minus h hmn h3 h4
  rw [threeJ_factor hm, threeJ_factor hm, threeJ_factor hm,
    show j₁ - 1 - j₂ - m₃ = (j₁ - j₂ - m₃) - 1 by ring,
    show j₁ + 1 - j₂ - m₃ = (j₁ - j₂ - m₃) + 1 by ring, sgn_sub_one, sgn_add_one]
  rw [em3]
  linear_combination
    (sgn (j₁ - j₂ - m₃) * Real.sqrt (fq (j₂ + m₂) * fq (j₂ - m₂) * fq (j₃ + m₃) * fq (j₃ - m₃)) *
      (Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (fq (j₁ + m₁) * fq (j₁ - m₁)))) * hrec
    + (((j₁ : ℝ) + 1) * sgn (j₁ - j₂ - m₃) *
      Real.sqrt (fq (j₂ + m₂) * fq (j₂ - m₂) * fq (j₃ + m₃) * fq (j₃ - m₃)) *
      racahSum3 (j₁ - 1) j₂ j₃ m₁ m₂) * emn
    + ((j₁ : ℝ) * sgn (j₁ - j₂ - m₃) *
      Real.sqrt (fq (j₂ + m₂) * fq (j₂ - m₂) * fq (j₃ + m₃) * fq (j₃ - m₃)) *
      racahSum3 (j₁ + 1) j₂ j₃ m₁ m₂) * ep


lemma sqrt_mul_sq_eq1 {E A A' ρ : ℝ} (hE : 0 ≤ E) (hρ : 0 ≤ ρ) (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (h : E ^ 2 * A = ρ ^ 2 * A') : E * Real.sqrt A = ρ * Real.sqrt A' := by
  have h1 : (E * Real.sqrt A) ^ 2 = (ρ * Real.sqrt A') ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hA']
    exact h
  exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp h1

/-- The `m`-dependent square root in the `3j` prefactor. -/
noncomputable def Rm (j₂ j₃ m₂ m₃ : ℚ) : ℝ :=
  Real.sqrt (fq (j₂ + m₂) * fq (j₂ - m₂) * fq (j₃ + m₃) * fq (j₃ - m₃))

lemma Rm_plus {j₂ j₃ m₂ m₃ : ℚ} (h1 : IsNat (j₂ + m₂)) (h2 : IsNat (j₂ - (m₂ + 1)))
    (h3 : IsNat (j₃ + (m₃ - 1))) (h4 : IsNat (j₃ - m₃)) :
    Real.sqrt (((j₂ : ℝ) - m₂) * ((j₂ : ℝ) + m₂ + 1) * ((j₃ : ℝ) - m₃ + 1) * ((j₃ : ℝ) + m₃)) *
        Rm j₂ j₃ (m₂ + 1) (m₃ - 1) =
      (((j₂ : ℝ) + m₂ + 1) * ((j₃ : ℝ) - m₃ + 1)) * Rm j₂ j₃ m₂ m₃ := by
  have f1 : fq (j₂ + (m₂ + 1)) = ((j₂ : ℝ) + m₂ + 1) * fq (j₂ + m₂) := by
    have := fq_succ' h1 (y := j₂ + (m₂ + 1)) (by ring)
    rw [this]; push_cast; ring
  have f2 : fq (j₂ - m₂) = ((j₂ : ℝ) - m₂) * fq (j₂ - (m₂ + 1)) := by
    have := fq_succ' h2 (y := j₂ - m₂) (by ring)
    rw [this]; push_cast; ring
  have f3 : fq (j₃ + m₃) = ((j₃ : ℝ) + m₃) * fq (j₃ + (m₃ - 1)) := by
    have := fq_succ' h3 (y := j₃ + m₃) (by ring)
    rw [this]; push_cast; ring
  have f4 : fq (j₃ - (m₃ - 1)) = ((j₃ : ℝ) - m₃ + 1) * fq (j₃ - m₃) := by
    have := fq_succ' h4 (y := j₃ - (m₃ - 1)) (by ring)
    rw [this]; push_cast; ring
  have a1 := h1.nonneg_real
  have a2 := h2.nonneg_real
  have a3 := h3.nonneg_real
  have a4 := h4.nonneg_real
  push_cast at a1 a2 a3 a4
  unfold Rm
  apply sqrt_mul_sq_eq1 (Real.sqrt_nonneg _) _ _ _ _
  · have : 0 ≤ (j₂ : ℝ) + m₂ + 1 := by linarith
    have : 0 ≤ (j₃ : ℝ) - m₃ + 1 := by linarith
    positivity
  · exact mul_nonneg (mul_nonneg (mul_nonneg (fq_nonneg _) (fq_nonneg _)) (fq_nonneg _))
      (fq_nonneg _)
  · exact mul_nonneg (mul_nonneg (mul_nonneg (fq_nonneg _) (fq_nonneg _)) (fq_nonneg _))
      (fq_nonneg _)
  · have hP : 0 ≤ ((j₂ : ℝ) - m₂) * ((j₂ : ℝ) + m₂ + 1) * ((j₃ : ℝ) - m₃ + 1) * ((j₃ : ℝ) + m₃) := by
      have : 0 ≤ (j₂ : ℝ) - m₂ := by linarith
      have : 0 ≤ (j₂ : ℝ) + m₂ + 1 := by linarith
      have : 0 ≤ (j₃ : ℝ) - m₃ + 1 := by linarith
      have : 0 ≤ (j₃ : ℝ) + m₃ := by linarith
      positivity
    rw [Real.sq_sqrt hP, f1, f4, f2, f3]
    ring

lemma Rm_minus {j₂ j₃ m₂ m₃ : ℚ} (h1 : IsNat (j₂ - m₂)) (h2 : IsNat (j₂ + (m₂ - 1)))
    (h3 : IsNat (j₃ + m₃)) (h4 : IsNat (j₃ - (m₃ + 1))) :
    Real.sqrt (((j₂ : ℝ) - m₂ + 1) * ((j₂ : ℝ) + m₂) * ((j₃ : ℝ) - m₃) * ((j₃ : ℝ) + m₃ + 1)) *
        Rm j₂ j₃ (m₂ - 1) (m₃ + 1) =
      (((j₂ : ℝ) - m₂ + 1) * ((j₃ : ℝ) + m₃ + 1)) * Rm j₂ j₃ m₂ m₃ := by
  have f1 : fq (j₂ + m₂) = ((j₂ : ℝ) + m₂) * fq (j₂ + (m₂ - 1)) := by
    have := fq_succ' h2 (y := j₂ + m₂) (by ring)
    rw [this]; push_cast; ring
  have f2 : fq (j₂ - (m₂ - 1)) = ((j₂ : ℝ) - m₂ + 1) * fq (j₂ - m₂) := by
    have := fq_succ' h1 (y := j₂ - (m₂ - 1)) (by ring)
    rw [this]; push_cast; ring
  have f3 : fq (j₃ + (m₃ + 1)) = ((j₃ : ℝ) + m₃ + 1) * fq (j₃ + m₃) := by
    have := fq_succ' h3 (y := j₃ + (m₃ + 1)) (by ring)
    rw [this]; push_cast; ring
  have f4 : fq (j₃ - m₃) = ((j₃ : ℝ) - m₃) * fq (j₃ - (m₃ + 1)) := by
    have := fq_succ' h4 (y := j₃ - m₃) (by ring)
    rw [this]; push_cast; ring
  have a1 := h1.nonneg_real
  have a2 := h2.nonneg_real
  have a3 := h3.nonneg_real
  have a4 := h4.nonneg_real
  push_cast at a1 a2 a3 a4
  unfold Rm
  apply sqrt_mul_sq_eq1 (Real.sqrt_nonneg _) _ _ _ _
  · have : 0 ≤ (j₂ : ℝ) - m₂ + 1 := by linarith
    have : 0 ≤ (j₃ : ℝ) + m₃ + 1 := by linarith
    positivity
  · exact mul_nonneg (mul_nonneg (mul_nonneg (fq_nonneg _) (fq_nonneg _)) (fq_nonneg _))
      (fq_nonneg _)
  · exact mul_nonneg (mul_nonneg (mul_nonneg (fq_nonneg _) (fq_nonneg _)) (fq_nonneg _))
      (fq_nonneg _)
  · have hP : 0 ≤ ((j₂ : ℝ) - m₂ + 1) * ((j₂ : ℝ) + m₂) * ((j₃ : ℝ) - m₃) * ((j₃ : ℝ) + m₃ + 1) := by
      have : 0 ≤ (j₂ : ℝ) - m₂ + 1 := by linarith
      have : 0 ≤ (j₂ : ℝ) + m₂ := by linarith
      have : 0 ≤ (j₃ : ℝ) - m₃ := by linarith
      have : 0 ≤ (j₃ : ℝ) + m₃ + 1 := by linarith
      positivity
    rw [Real.sq_sqrt hP, f2, f3, f1, f4]
    ring

/-- **DLMF 34.3.14** (three-term recurrence of the `3j` symbol in `m₂, m₃`), under the
projection conditions that DLMF assumes for the three symbols involved. -/
theorem threeJ_recurrence_m (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ) (hm : m₁ + m₂ + m₃ = 0)
    (a1 : IsNat (j₂ + m₂)) (a2 : IsNat (j₂ - (m₂ + 1))) (a3 : IsNat (j₃ + (m₃ - 1)))
    (a4 : IsNat (j₃ - m₃)) (b1 : IsNat (j₂ - m₂)) (b2 : IsNat (j₂ + (m₂ - 1)))
    (b3 : IsNat (j₃ + m₃)) (b4 : IsNat (j₃ - (m₃ + 1))) :
    (((j₁ : ℝ) * (j₁ + 1) - j₂ * (j₂ + 1) - j₃ * (j₃ + 1)) - 2 * (m₂ : ℝ) * m₃) *
        threeJ j₁ j₂ j₃ m₁ m₂ m₃ =
      Real.sqrt (((j₂ : ℝ) - m₂) * ((j₂ : ℝ) + m₂ + 1) * ((j₃ : ℝ) - m₃ + 1) * ((j₃ : ℝ) + m₃)) *
          threeJ j₁ j₂ j₃ m₁ (m₂ + 1) (m₃ - 1)
        + Real.sqrt (((j₂ : ℝ) - m₂ + 1) * ((j₂ : ℝ) + m₂) * ((j₃ : ℝ) - m₃) *
            ((j₃ : ℝ) + m₃ + 1)) * threeJ j₁ j₂ j₃ m₁ (m₂ - 1) (m₃ + 1) := by
  have hrec := racahSum3_m_recurrence j₁ j₂ j₃ m₁ m₂
  have em3 : (m₃ : ℝ) = -(m₁ : ℝ) - m₂ := by
    have : (m₃ : ℚ) = -m₁ - m₂ := by linarith
    rw [this]; push_cast; ring
  have ep := Rm_plus a1 a2 a3 a4
  have emn := Rm_minus b1 b2 b3 b4
  have hmp : m₁ + (m₂ + 1) + (m₃ - 1) = 0 := by linarith
  have hmm : m₁ + (m₂ - 1) + (m₃ + 1) = 0 := by linarith
  rw [threeJ_factor hm, threeJ_factor hmp, threeJ_factor hmm,
    show j₁ - j₂ - (m₃ - 1) = (j₁ - j₂ - m₃) + 1 by ring,
    show j₁ - j₂ - (m₃ + 1) = (j₁ - j₂ - m₃) - 1 by ring, sgn_add_one, sgn_sub_one]
  unfold Rm at ep emn
  have hrec' : (((j₁ : ℝ) * (j₁ + 1) - j₂ * (j₂ + 1) - j₃ * (j₃ + 1)) - 2 * (m₂ : ℝ) * m₃) *
        racahSum3 j₁ j₂ j₃ m₁ m₂ +
      ((j₂ : ℝ) + m₂ + 1) * ((j₃ : ℝ) - m₃ + 1) * racahSum3 j₁ j₂ j₃ m₁ (m₂ + 1) +
      ((j₂ : ℝ) - m₂ + 1) * ((j₃ : ℝ) + m₃ + 1) * racahSum3 j₁ j₂ j₃ m₁ (m₂ - 1) = 0 := by
    rw [em3]; linear_combination hrec
  linear_combination
    (sgn (j₁ - j₂ - m₃) * (Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (fq (j₁ + m₁) * fq (j₁ - m₁))) *
      Real.sqrt (fq (j₂ + m₂) * fq (j₂ - m₂) * fq (j₃ + m₃) * fq (j₃ - m₃))) * hrec'
    + (sgn (j₁ - j₂ - m₃) * (Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (fq (j₁ + m₁) * fq (j₁ - m₁))) *
      racahSum3 j₁ j₂ j₃ m₁ (m₂ + 1)) * ep
    + (sgn (j₁ - j₂ - m₃) * (Real.sqrt (triSq j₁ j₂ j₃) * Real.sqrt (fq (j₁ + m₁) * fq (j₁ - m₁))) *
      racahSum3 j₁ j₂ j₃ m₁ (m₂ - 1)) * emn

/-- info: 'FormalResearch.Wigner.threeJ_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threeJ_recurrence

/-- info: 'FormalResearch.Wigner.threeJ_recurrence_m' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threeJ_recurrence_m

end FormalResearch.Wigner
