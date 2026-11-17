module

public import FormalResearch.Special.AiryCftQSampleZeros
public import FormalResearch.Special.AiryCft2ComboWeights

/-!
# Position data of the zeros of `N = P Ai + Q Ai'` for the sampling bound

Inputs for `AiryCftQNCSample`, all **proved** from the interlacing `airyNIdx_injOn` (`AiryCft2ComboZeros`) and the separation of the
roots of `Ai` (`AiryCftQSampleZeros`).  For a real zero `t ≤ -1` of `N` with index `n = airyNIdx t` (so `a_{n+1} < t`, and `t < a_n` if `n ≥ 1`) put
`x(t) = √(-t) ≥ 1`:

* `ncRoot_growth`: `(n+1)² ≤ x⁶`;
* `ncRoot_sep`: if `n₁ + 2 ≤ n₂` for two such zeros, `n₂ - n₁ - 1 ≤ (x₂ - x₁) x₂²` (the zeros of `N` need not be separated like those of `Ai` — two
  zeros can sit on both sides of a zero of `Ai` — but they are separated up to a shift of one index);
* `airyNIdx_eq_zero`: a zero `t > a_1` has index `0`; hence `airyNC_near_finite`: only finitely many zeros of `N` have `t > -1`.
-/

@[expose] public section

open Real

namespace FormalResearch.Special

lemma airyNC_realzero_airy_ne (P Q : ℝ) (hQ : Q ≠ 0) {t : ℝ} (h : airyNC P Q (t : ℂ) = 0) : airyAi t ≠ 0 := by
  intro h0
  have := airyNC_ne_zero_of_airy_zero P Q hQ (z := (t : ℂ)) (by rw [airyAiC_ofReal, h0]; simp)
  exact this h

lemma airyNIdx_eq_zero {t : ℝ} (ht : airyZero 1 < t) : airyNIdx t = 0 := by
  by_contra h
  exact airyNIdx_min (t := t) (j := 0) (by omega) ht

/-- The root `x = √(-t)` of a zero with index `n ≥ 1` lies above `ρ_n = √(-a_n)`. -/
lemma ncRoot_gt {P Q : ℝ} (hQ : Q ≠ 0) {t : ℝ} (h : airyNC P Q (t : ℂ) = 0) (hn : 1 ≤ airyNIdx t) :
    airyZeroRoot (airyNIdx t) < √(-t) := by
  have hA := airyNC_realzero_airy_ne P Q hQ h
  have h1 := (airyNIdx_gap hA (j := airyNIdx t) hn).1 le_rfl
  rw [airyZeroRoot]
  exact Real.sqrt_lt_sqrt (neg_nonneg.mpr (airyZero_nonpos _)) (by linarith)

/-- The root `x = √(-t)` of a zero with index `n` lies below `ρ_{n+1} = √(-a_{n+1})`. -/
lemma ncRoot_lt {t : ℝ} (ht : t ≤ 0) : airyZeroRoot (airyNIdx t + 1) > √(-t) := by
  have h1 := airyNIdx_spec t
  rw [airyZeroRoot]
  exact Real.sqrt_lt_sqrt (by linarith) (by linarith)

lemma ncRoot_ge_one {t : ℝ} (ht : t ≤ -1) : 1 ≤ √(-t) := by
  rw [show (1 : ℝ) = √1 by simp]
  exact Real.sqrt_le_sqrt (by linarith)

/-- **Growth**: `(n+1)² ≤ x⁶` for a zero `t ≤ -1` of index `n`. -/
lemma ncRoot_growth {P Q : ℝ} (hQ : Q ≠ 0) {t : ℝ} (h : airyNC P Q (t : ℂ) = 0) (ht : t ≤ -1) :
    ((airyNIdx t : ℝ) + 1) ^ 2 ≤ (√(-t)) ^ 6 := by
  have hx1 := ncRoot_ge_one ht
  rcases Nat.eq_zero_or_pos (airyNIdx t) with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero, zero_add, one_pow]
    exact one_le_pow₀ hx1
  · have hgt := ncRoot_gt hQ h hpos
    have h6 := airyZeroRoot_sixth_ge hpos
    have hρ0 := (airyZeroRoot_pos (airyNIdx t)).le
    have : airyZeroRoot (airyNIdx t) ^ 6 ≤ (√(-t)) ^ 6 := pow_le_pow_left₀ hρ0 hgt.le 6
    have hn1 : (1 : ℝ) ≤ airyNIdx t := by exact_mod_cast hpos
    nlinarith

/-- **Separation up to a shift of one index.** -/
lemma ncRoot_sep {P Q : ℝ} (hQ : Q ≠ 0) {t₁ t₂ : ℝ} (h₂ : airyNC P Q (t₂ : ℂ) = 0)
    (ht₁ : t₁ ≤ -1) (hn : airyNIdx t₁ + 2 ≤ airyNIdx t₂) :
    (airyNIdx t₂ : ℝ) - airyNIdx t₁ - 1 ≤ (√(-t₂) - √(-t₁)) * (√(-t₂)) ^ 2 := by
  set n := airyNIdx t₁ with hn1
  set m := airyNIdx t₂ with hm
  have hpos : 1 ≤ m := by omega
  have hgt := ncRoot_gt hQ h₂ hpos
  have hlt := ncRoot_lt (t := t₁) (by linarith)
  have hs := airyRoot_sep_lt (n := n) (m := m - 1) (by omega)
  rw [show m - 1 + 1 = m by omega] at hs
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub hpos]; simp
  rw [hcast] at hs
  have hρn : airyZeroRoot (n + 1) < airyZeroRoot m := airyZeroRoot_lt (by omega) (by omega)
  have hρm0 := (airyZeroRoot_pos m).le
  have hd : airyZeroRoot m - airyZeroRoot (n + 1) ≤ √(-t₂) - √(-t₁) := by linarith
  have hsq : airyZeroRoot m ^ 2 ≤ (√(-t₂)) ^ 2 := pow_le_pow_left₀ hρm0 hgt.le 2
  have hpos' : 0 ≤ airyZeroRoot m - airyZeroRoot (n + 1) := by linarith
  calc (m : ℝ) - n - 1 = ((m : ℝ) - 1) - n := by ring
    _ ≤ _ := hs
    _ ≤ (√(-t₂) - √(-t₁)) * (√(-t₂)) ^ 2 := mul_le_mul hd hsq (by positivity) (by linarith)

/-- Symmetric form of the separation, for two zeros `≤ -1`. -/
lemma ncRoot_sep_abs {P Q : ℝ} (hQ : Q ≠ 0) {t₁ t₂ : ℝ} (h₁ : airyNC P Q (t₁ : ℂ) = 0) (h₂ : airyNC P Q (t₂ : ℂ) = 0)
    (ht₁ : t₁ ≤ -1) (ht₂ : t₂ ≤ -1) :
    |(airyNIdx t₁ : ℝ) - airyNIdx t₂| - 1 ≤ |√(-t₁) - √(-t₂)| * (max (√(-t₁)) (√(-t₂))) ^ 2 := by
  have hnn : 0 ≤ |√(-t₁) - √(-t₂)| * (max (√(-t₁)) (√(-t₂))) ^ 2 := by positivity
  by_cases hn : airyNIdx t₁ + 2 ≤ airyNIdx t₂
  · have h := ncRoot_sep hQ h₂ ht₁ hn
    have hq : (airyNIdx t₁ : ℝ) + 2 ≤ airyNIdx t₂ := by exact_mod_cast hn
    have hc : √(-t₁) < √(-t₂) := by
      by_contra hcon
      push Not at hcon
      have : (√(-t₂) - √(-t₁)) * (√(-t₂)) ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      linarith
    rw [abs_sub_comm (√(-t₁)), abs_of_nonneg (by linarith : (0 : ℝ) ≤ √(-t₂) - √(-t₁)), max_eq_right hc.le,
      abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (airyNIdx t₂ : ℝ) - airyNIdx t₁)]
    linarith
  by_cases hn2 : airyNIdx t₂ + 2 ≤ airyNIdx t₁
  · have h := ncRoot_sep hQ h₁ ht₂ hn2
    have hq : (airyNIdx t₂ : ℝ) + 2 ≤ airyNIdx t₁ := by exact_mod_cast hn2
    have hc : √(-t₂) < √(-t₁) := by
      by_contra hcon
      push Not at hcon
      have : (√(-t₁) - √(-t₂)) * (√(-t₁)) ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      linarith
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ √(-t₁) - √(-t₂)), max_eq_left hc.le,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ (airyNIdx t₁ : ℝ) - airyNIdx t₂)]
    linarith
  · have h1 : (airyNIdx t₁ : ℝ) ≤ airyNIdx t₂ + 1 := by exact_mod_cast (by omega : airyNIdx t₁ ≤ airyNIdx t₂ + 1)
    have h2 : (airyNIdx t₂ : ℝ) ≤ airyNIdx t₁ + 1 := by exact_mod_cast (by omega : airyNIdx t₂ ≤ airyNIdx t₁ + 1)
    have : |(airyNIdx t₁ : ℝ) - airyNIdx t₂| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith

/-- Only finitely many zeros of `N` have `t > -1`. -/
theorem airyNC_near_finite (P Q : ℝ) (hQ : Q ≠ 0) :
    {z : {z : ℂ // airyNC P Q z = 0} | -1 < z.1.re}.Finite := by
  have hfin : ({0} : Set ℕ).Finite := Set.finite_singleton 0
  refine Set.Finite.of_injOn (f := fun z : {z : ℂ // airyNC P Q z = 0} => airyNIdx z.1.re) (t := {0}) ?_ ?_ hfin
  · intro z hz
    have : airyZero 1 < z.1.re := by
      have := airyZero_one.2
      have hz' : -1 < z.1.re := hz
      linarith
    exact airyNIdx_eq_zero this
  · intro z₁ hz₁ z₂ hz₂ h12
    have i1 := airyNC_zero_im P Q hQ z₁.2
    have i2 := airyNC_zero_im P Q hQ z₂.2
    have e1 : z₁.1 = (z₁.1.re : ℂ) := Complex.ext (by simp) (by simp [i1])
    have e2 : z₂.1 = (z₂.1.re : ℂ) := Complex.ext (by simp) (by simp [i2])
    have h1 : airyNC P Q (z₁.1.re : ℂ) = 0 := by rw [← e1]; exact z₁.2
    have h2 : airyNC P Q (z₂.1.re : ℂ) = 0 := by rw [← e2]; exact z₂.2
    have := airyNIdx_injOn P Q hQ h1 h2 h12
    apply Subtype.ext
    rw [e1, e2, this]

end FormalResearch.Special
