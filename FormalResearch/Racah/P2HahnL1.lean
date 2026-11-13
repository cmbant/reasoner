module

public import FormalResearch.Racah.P2ThreeJHahn
public import FormalResearch.Wigner.SpecialValues

/-!
# The row `L = 1` of the `M = σ = 0` kernel (Weyl P2)

For `M = σ = 0` the rank recurrence is degenerate at `L = 0` (`L(L+1)x - Mσ = 0` and the coefficient of
`Φ_{L+1}` is `L R_{L+1}`), so the row `L = 1` is not determined by `L = 0` through it.  It is
evaluated here directly from Racah's formula, whose sum has two terms.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner

/-- `(1 j j; 0 m -m)` with `j+m = a`, `j-m = b` (naturals, `a+b ≥ 1`):
`(-1)^{1-b} (b-a)/√((a+b)(a+b+1)(a+b+2))`. -/
lemma racahSum3_one_zero (j m : ℚ) (a b : ℕ) (ha : j + m = a) (hb : j - m = b) :
    racahSum3 1 j j 0 m = ((b : ℝ) - a) * (ifa (a : ℚ) * ifa (b : ℚ)) := by
  unfold racahSum3
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range 2)]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, term3_eq, zero_add]
    have z : ∀ x : ℚ, x = 0 → ifa x = 1 := fun x hx => by rw [hx, ifa_zero]
    have o : ∀ x : ℚ, x = 1 → ifa x = 1 := fun x hx => by rw [hx, ifa_one]
    have hb1 : ifa (j - 1 - m + ((0 : ℕ) : ℚ)) = (b : ℝ) * ifa (b : ℚ) := by
      rw [show j - 1 - m + ((0 : ℕ) : ℚ) = (b : ℚ) - 1 by rw [← hb]; push_cast; ring, ifa_pred]
      simp
    have ha1 : ifa (j + m - ((1 : ℕ) : ℚ)) = (a : ℝ) * ifa (a : ℚ) := by
      rw [show j + m - ((1 : ℕ) : ℚ) = (a : ℚ) - 1 by rw [← ha]; push_cast; ring, ifa_pred]
      simp
    have e1 : ifa (j - 1 - m + ((1 : ℕ) : ℚ)) = ifa (b : ℚ) := by
      rw [show j - 1 - m + ((1 : ℕ) : ℚ) = (b : ℚ) by rw [← hb]; push_cast; ring]
    have e2 : ifa (j + m - ((0 : ℕ) : ℚ)) = ifa (a : ℚ) := by
      rw [show j + m - ((0 : ℕ) : ℚ) = (a : ℚ) by rw [← ha]; push_cast; ring]
    have v0 : ifa ((0 : ℕ) : ℚ) = 1 := z _ (by simp)
    have v1 : ifa (1 + j - j - ((0 : ℕ) : ℚ)) = 1 := o _ (by simp)
    have v2 : ifa (1 - 0 - ((0 : ℕ) : ℚ)) = 1 := o _ (by simp)
    have v3 : ifa (j - j + 0 + ((0 : ℕ) : ℚ)) = 1 := z _ (by simp)
    have v4 : ifa ((1 : ℕ) : ℚ) = 1 := o _ (by simp)
    have v5 : ifa (1 + j - j - ((1 : ℕ) : ℚ)) = 1 := z _ (by simp)
    have v6 : ifa (1 - 0 - ((1 : ℕ) : ℚ)) = 1 := z _ (by simp)
    have v7 : ifa (j - j + 0 + ((1 : ℕ) : ℚ)) = 1 := o _ (by simp)
    rw [hb1, ha1, e1, e2, v1, v2, v3, v4, v5, v6, v7, v0]
    ring
  · intro s hs
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hs
    show term3 1 j j 0 m (s : ℚ) ((-1 : ℝ) ^ s) = 0
    rw [term3_eq, ifa_eq_zero_of_neg (x := 1 + j - j - (s : ℚ)) (by
      have : (2 : ℚ) ≤ s := by exact_mod_cast not_lt.mp hlt
      linarith)]
    ring

/-- `(1 j j; 0 m -m)` with `j+m = a`, `j-m = b` (naturals, `a+b ≥ 1`):
`(-1)^{1-b} (b-a)/√((a+b)(a+b+1)(a+b+2))`. -/
lemma threeJ_one_zero (j m : ℚ) (a b : ℕ) (ha : j + m = a) (hb : j - m = b) (hab : 1 ≤ a + b) :
    threeJ 1 j j 0 m (-m) =
      (-1 : ℝ) ^ (1 - (b : ℤ)) * ((b : ℝ) - a) /
        Real.sqrt (((a + b : ℕ) : ℝ) * ((a + b : ℕ) + 1) * ((a + b : ℕ) + 2)) := by
  obtain ⟨t, ht⟩ : ∃ t, a + b = t + 1 := ⟨a + b - 1, by omega⟩
  unfold threeJ
  rw [ite_eq_left (by ring), racahSum3_one_zero j m a b ha hb]
  have hs : sgn (1 - j - -m) = (-1 : ℝ) ^ (1 - (b : ℤ)) := by
    rw [show (1 : ℚ) - j - -m = (((1 - (b : ℤ) : ℤ)) : ℚ) by push_cast; rw [← hb]; ring, sgn_intCast]
  have hT : triSq 1 j j = (t.factorial : ℝ) / ((t + 3).factorial : ℝ) := by
    rw [triSq_of_nat (p := 1) (q := 1) (r := t) (by ring) (by ring)
      (by have : (a : ℚ) + b = t + 1 := by exact_mod_cast ht
          linarith)]
    simp only [Nat.factorial_one, Nat.cast_one, one_mul]
    rw [show 1 + 1 + t + 1 = t + 3 by ring]
  have f1 : fq (1 + 0) = 1 := by
    rw [show (1 : ℚ) + 0 = ((1 : ℕ) : ℚ) by simp, fq_natCast]; simp
  have f2 : fq (1 - 0) = 1 := by
    rw [show (1 : ℚ) - 0 = ((1 : ℕ) : ℚ) by simp, fq_natCast]; simp
  have f3 : fq (j + m) = (a.factorial : ℝ) := by rw [ha, fq_natCast]
  have f4 : fq (j - m) = (b.factorial : ℝ) := by rw [hb, fq_natCast]
  have f5 : fq (j + -m) = (b.factorial : ℝ) := by rw [← sub_eq_add_neg, hb, fq_natCast]
  have f6 : fq (j - -m) = (a.factorial : ℝ) := by rw [sub_neg_eq_add, ha, fq_natCast]
  rw [hs, hT, f1, f2, f3, f4, f5, f6, ifa_natCast, ifa_natCast]
  have hA : (a.factorial : ℝ) ≠ 0 := by positivity
  have hB : (b.factorial : ℝ) ≠ 0 := by positivity
  have hsq : Real.sqrt (1 * 1 * (a.factorial : ℝ) * b.factorial * b.factorial * a.factorial) =
      (a.factorial : ℝ) * b.factorial := by
    rw [show (1 : ℝ) * 1 * (a.factorial : ℝ) * b.factorial * b.factorial * a.factorial =
      ((a.factorial : ℝ) * b.factorial) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  rw [hsq]
  have hab' : ((a + b : ℕ) : ℝ) = (t : ℝ) + 1 := by rw [ht]; push_cast; ring
  rw [hab']
  have hfac : ((t + 3).factorial : ℝ) = ((t : ℝ) + 3) * ((t : ℝ) + 2) * ((t : ℝ) + 1) *
      (t.factorial : ℝ) := by
    rw [show t + 3 = (t + 2) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have ht0 : (t.factorial : ℝ) ≠ 0 := by positivity
  rw [hfac]
  have hrad : (t.factorial : ℝ) / (((t : ℝ) + 3) * ((t : ℝ) + 2) * ((t : ℝ) + 1) * t.factorial) =
      1 / (((t : ℝ) + 1) * (((t : ℝ) + 1) + 1) * (((t : ℝ) + 1) + 2)) := by
    field_simp; ring
  rw [hrad, Real.sqrt_div (by norm_num), Real.sqrt_one]
  have hq : (0 : ℝ) < Real.sqrt (((t : ℝ) + 1) * (((t : ℝ) + 1) + 1) * (((t : ℝ) + 1) + 2)) :=
    Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- The row `L = 1` of the kernel `Φ^{0,0}`: `Φ_1(x_u) = (D-2u)/√(D(D+2))`, with `N = D+1`
and `u = j_++m_+ ∈ {0,…,D}` (`D ≥ 1`). -/
lemma Phi3j_L1_M0 (N μ : ℚ) (D u : ℕ) (hD : N - 1 = D) (hu : jPlus N 0 + mPlus 0 μ = u)
    (huD : u ≤ D) (hD1 : 1 ≤ D) :
    Phi3j 1 0 0 N μ = ((D : ℝ) - 2 * u) / Real.sqrt ((D : ℝ) * (D + 2)) := by
  have hj : jMinus N 0 = (D : ℚ) / 2 := by unfold jMinus; linarith
  have hj' : jPlus N 0 = (D : ℚ) / 2 := by unfold jPlus; linarith
  have hm1 : mMinus 0 μ = μ := by unfold mMinus; ring
  have hm2 : mPlus 0 μ = -μ := by unfold mPlus; ring
  have hμ : (D : ℚ) / 2 - μ = u := by rw [hj', hm2] at hu; linarith
  unfold Phi3j
  rw [hj, hj', hm1, hm2]
  have h3 := threeJ_one_zero ((D : ℚ) / 2) μ (D - u) u
    (by rw [Nat.cast_sub huD]; linarith) hμ (by omega)
  rw [h3]
  have hs : sgn (2 * 1 + (D : ℚ) / 2 + -μ) = (-1 : ℝ) ^ (2 + u) := by
    rw [show 2 * 1 + (D : ℚ) / 2 + -μ = ((2 + u : ℕ) : ℚ) by push_cast; rw [← hμ]; ring,
      sgn_natCast]
  rw [hs]
  have hNr : (N : ℝ) = (D : ℝ) + 1 := by
    have : N = (D : ℚ) + 1 := by linarith
    rw [this]; push_cast; ring
  have hDu : D - u + u = D := by omega
  rw [hDu, hNr]
  have hpm : (-1 : ℝ) ^ (2 + u) * (-1 : ℝ) ^ (1 - (u : ℤ)) = -1 := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
    norm_num
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD1
  have hsplit : Real.sqrt ((D : ℝ) * ((D : ℝ) + 1) * ((D : ℝ) + 2)) =
      Real.sqrt ((D : ℝ) + 1) * Real.sqrt ((D : ℝ) * (D + 2)) := by
    rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
  have hq1 : 0 < Real.sqrt ((D : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hq2 : 0 < Real.sqrt ((D : ℝ) * (D + 2)) := Real.sqrt_pos.mpr (by positivity)
  rw [Nat.cast_sub huD, hsplit]
  have e : (-1 : ℝ) ^ (2 + u) * Real.sqrt ((D : ℝ) + 1) *
      ((-1 : ℝ) ^ (1 - (u : ℤ)) * ((u : ℝ) - ((D : ℝ) - u)) /
        (Real.sqrt ((D : ℝ) + 1) * Real.sqrt ((D : ℝ) * (D + 2)))) =
      ((-1 : ℝ) ^ (2 + u) * (-1 : ℝ) ^ (1 - (u : ℤ))) * ((u : ℝ) - ((D : ℝ) - u)) *
        (Real.sqrt ((D : ℝ) + 1) / (Real.sqrt ((D : ℝ) + 1) * Real.sqrt ((D : ℝ) * (D + 2)))) := by
    ring
  rw [e, hpm]
  field_simp
  ring

end FormalResearch.Racah
