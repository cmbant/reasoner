module

public import FormalResearch.Special.RacahKappaHLeftCoef
public import FormalResearch.Special.RacahKappaLeftBand
public import FormalResearch.Special.DiscreteAiryLimitChains2HalfAiry

/-!
# The band comparison for the half-integer Racah chain

Twin of `RacahKappaLeftBand` for the shifted closed forms `hrAkH`, `hrCkH` (rank `t = k + ½`); declarations carry the suffix `H`.  The coefficient facts come from the real-rank versions of `RacahKappaHLeftCoef`.

**Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

lemma rlH_cancel (m0 X T : ℝ) (hm : 0 < m0) : m0 * (X / m0 * T) = X * T := by
  field_simp

lemma hrAkH_eq (P Q a b h : ℝ) (k : ℤ) : hrAkH P Q a b h k = hrAt P Q a b h ((k : ℝ) + 1 / 2) := rfl

lemma hrCkH_eq (P Q τ x a b h : ℝ) (k : ℤ) : hrCkH P Q τ x a b h k = hrCt P Q τ x a b h ((k : ℝ) + 1 / 2) := rfl

lemma hrAkH_succ (P Q a b h : ℝ) (k : ℤ) : hrAkH P Q a b h (k + 1) = hrAt P Q a b h (((k : ℝ) + 1 / 2) + 1) := by
  unfold hrAkH hrAt; push_cast; ring_nf

lemma hrCkH_succ (P Q τ x a b h : ℝ) (k : ℤ) : hrCkH P Q τ x a b h (k + 1) = hrCt P Q τ x a b h (((k : ℝ) + 1 / 2) + 1) := by
  unfold hrCkH hrCt; push_cast; ring_nf


/-- **The coefficient facts on the band** (constants depending on the data only). -/
lemma rl_coef_allH {P Q a b τ x qs : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hτ : τ ^ 2 = 1) (hs : 1 - x ^ 2 = rkS P Q x * qs ^ 2)
    (hspos : 0 < rkS P Q x) (hqs : 0 < qs) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2) :
    ∃ (K0 : ℕ) (h0 m0 B Λ0 : ℝ), 2 ≤ K0 ∧ 0 < h0 ∧ h0 ≤ 1 ∧ 0 < m0 ∧ 0 < B ∧ 0 ≤ Λ0 ∧ |a| ≤ K0 ∧ |b| ≤ K0 ∧
      ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ k : ℤ, (K0 : ℤ) ≤ k → ((k : ℝ) + 3) * h ≤ qs / 2 →
        (0 < hrAkH P Q a b h k ∧ hrAkH P Q a b h k ≤ 3 / 4 ∧ m0 ≤ 2 * hrAkH P Q a b h k - |hrCkH P Q τ x a b h k|) ∧
        (0 < hrAkH P Q a b h (k + 1) ∧ m0 ≤ 2 * hrAkH P Q a b h (k + 1) - |hrCkH P Q τ x a b h (k + 1)|) ∧
        hrCkH P Q τ x a b h k ^ 2 + hrAkH P Q a b h k ^ 2 ≤ B * hrAkH P Q a b h (k + 1) ^ 2 ∧
        2 * (1 + B) * (|hrAkH P Q a b h (k + 1) - hrAkH P Q a b h k| + |hrCkH P Q τ x a b h (k + 1) - hrCkH P Q τ x a b h k|) ≤
          m0 * (2 * (1 + B) * Λ0 / m0 * (1 / ((k : ℝ) + 1 / 2) ^ 2 + h)) ∧
        2 * (1 + B) * Λ0 / m0 * (1 / ((k : ℝ) + 1 / 2) ^ 2 + h) ≤ 1 / 2 := by
  set qm : ℝ := qs / 2 with hqm
  have hqm0 : 0 < qm := by rw [hqm]; positivity
  have hP1 : 0 < 1 - P * qm ^ 2 := by
    have : P * qm ^ 2 ≤ P * qs ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith only [hqs, hqm]) hP
    linarith
  have hQ1 : 0 < 1 - Q * qm ^ 2 := by
    have : Q * qm ^ 2 ≤ Q * qs ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith only [hqs, hqm]) hQ
    linarith
  set β : ℝ := a ^ 2 + b ^ 2 + 1 / 3 with hβdef
  have hβ0 : 0 < β := by rw [hβdef]; positivity
  set β0 : ℝ := Real.sqrt (P * Q) with hβ0def
  have hβ00 : 0 ≤ β0 := Real.sqrt_nonneg _
  set μ0 : ℝ := rkS P Q x * (qs ^ 2 - qm ^ 2) / 2 with hμ0
  have hμ0p : 0 < μ0 := by
    rw [hμ0]
    have : 0 < qs ^ 2 - qm ^ 2 := by rw [hqm]; nlinarith only [hqs]
    positivity
  set m0 : ℝ := μ0 / 2 with hm0
  have hm0p : 0 < m0 := by positivity
  set L : ℝ := (P + Q + 2 * P * Q * qm ^ 2) / (2 * Real.sqrt ((1 - P * qm ^ 2) * (1 - Q * qm ^ 2))) with hL
  have hL0 : 0 ≤ L := by positivity
  set Λ1 : ℝ := 3 / 2 * L * qm + 2 * β0 * qm with hΛ1
  have hΛ10 : 0 ≤ Λ1 := by positivity
  set Λ0 : ℝ := (β + 2 * |a * b|) + Λ1 with hΛ0
  have hΛ00 : 0 ≤ Λ0 := by positivity
  set B : ℝ := 45 / (4 * m0 ^ 2) with hB
  have hBp : 0 < B := by positivity
  set Ê : ℝ := 2 * (1 + B) * Λ0 / m0 with hÊ
  have hÊ0 : 0 ≤ Ê := by positivity
  set R : ℝ := 2 + |a| + |b| + 2 * β + 4 * (β + |a * b|) / μ0 + 4 * Ê with hR
  have hR2 : 2 ≤ R := by
    have : 0 ≤ 4 * (β + |a * b|) / μ0 := by positivity
    rw [hR]; linarith [abs_nonneg a, abs_nonneg b]
  set K0 : ℕ := ⌈R⌉₊ with hK0
  have hK0R : R ≤ (K0 : ℝ) := Nat.le_ceil R
  have hK02 : (2 : ℝ) ≤ (K0 : ℝ) := hR2.trans hK0R
  set h0 : ℝ := min 1 (min (μ0 / (4 * (β0 * (qm + (a ^ 2 + b ^ 2) / 2) + 1))) (1 / (4 * Ê + 1))) with hh0
  have hh0p : 0 < h0 := lt_min one_pos (lt_min (by positivity) (by positivity))
  have hh01 : h0 ≤ 1 := min_le_left _ _
  have hh0a : h0 ≤ μ0 / (4 * (β0 * (qm + (a ^ 2 + b ^ 2) / 2) + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hh0b : h0 ≤ 1 / (4 * Ê + 1) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨K0, h0, m0, B, Λ0, by exact_mod_cast (by exact_mod_cast hK02 : (2 : ℝ) ≤ K0), hh0p, hh01, hm0p, hBp, hΛ00,
    by rw [hR] at hK0R; linarith [abs_nonneg a, abs_nonneg b, abs_nonneg (a * b), (by positivity : 0 ≤ 4 * (β + |a * b|) / μ0)],
    by rw [hR] at hK0R; linarith [abs_nonneg a, abs_nonneg b, abs_nonneg (a * b), (by positivity : 0 ≤ 4 * (β + |a * b|) / μ0)], ?_⟩
  intro h hh hhh0 k hk hkq0
  have hkq : ((k : ℝ) + 3) * h ≤ qs / 2 := hkq0
  have hab1 : |a| ≤ (K0 : ℝ) := by
    rw [hR] at hK0R; linarith [abs_nonneg a, abs_nonneg b, abs_nonneg (a * b), (by positivity : 0 ≤ 4 * (β + |a * b|) / μ0)]
  have hab2 : |b| ≤ (K0 : ℝ) := by
    rw [hR] at hK0R; linarith [abs_nonneg a, abs_nonneg b, abs_nonneg (a * b), (by positivity : 0 ≤ 4 * (β + |a * b|) / μ0)]
  have hKβ : 2 * β ≤ (K0 : ℝ) := by
    rw [hR] at hK0R; linarith [abs_nonneg a, abs_nonneg b, abs_nonneg (a * b), (by positivity : 0 ≤ 4 * (β + |a * b|) / μ0), (by positivity : 0 ≤ 4 * Ê)]
  have hKβ2 : 4 * (β + |a * b|) / μ0 ≤ (K0 : ℝ) := by
    rw [hR] at hK0R; linarith [abs_nonneg a, abs_nonneg b, abs_nonneg (a * b), (by positivity : 0 ≤ 4 * Ê)]
  have hKÊ : 4 * Ê ≤ (K0 : ℝ) := by
    rw [hR] at hK0R; linarith [abs_nonneg a, abs_nonneg b, abs_nonneg (a * b), (by positivity : 0 ≤ 4 * (β + |a * b|) / μ0)]
  have hh0c : h * (β0 * (qm + (a ^ 2 + b ^ 2) / 2)) ≤ μ0 / 4 := by
    have hpos : 0 < 4 * (β0 * (qm + (a ^ 2 + b ^ 2) / 2) + 1) := by positivity
    have h1 : h ≤ μ0 / (4 * (β0 * (qm + (a ^ 2 + b ^ 2) / 2) + 1)) := hhh0.trans hh0a
    rw [le_div_iff₀ hpos] at h1
    have : 0 ≤ β0 * (qm + (a ^ 2 + b ^ 2) / 2) := by positivity
    nlinarith only [h1, this, hh]
  have hmarg : ∀ j : ℤ, (K0 : ℤ) ≤ j → ((j : ℝ) + 1) * h ≤ qs / 2 →
      (0 < hrAkH P Q a b h j ∧ hrAkH P Q a b h j ≤ 3 / 4 ∧ m0 ≤ 2 * hrAkH P Q a b h j - |hrCkH P Q τ x a b h j|) := by
    intro j hj hjq
    have hjR0 : (K0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hjR : (K0 : ℝ) ≤ (j : ℝ) + 1 / 2 := by linarith
    have hj1R : (1 : ℝ) ≤ (j : ℝ) := by linarith
    have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 / 2 := by linarith
    have hjpos : 0 < ((j : ℝ) + 1 / 2) := by linarith
    have hj2 : ((j : ℝ) + 1 / 2) ≤ ((j : ℝ) + 1 / 2) ^ 2 := by nlinarith only [hj1R]
    have hja : a ^ 2 ≤ ((j : ℝ) + 1 / 2) ^ 2 := by
      have : |a| ≤ ((j : ℝ) + 1 / 2) := hab1.trans hjR
      nlinarith only [sq_abs a, abs_nonneg a, this]
    have hjb : b ^ 2 ≤ ((j : ℝ) + 1 / 2) ^ 2 := by
      have : |b| ≤ ((j : ℝ) + 1 / 2) := hab2.trans hjR
      nlinarith only [sq_abs b, abs_nonneg b, this]
    have hβj : β / ((j : ℝ) + 1 / 2) ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith only [hKβ, hjR, hj2]
    have hβj' : (β + |a * b|) / ((j : ℝ) + 1 / 2) ^ 2 ≤ μ0 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      have : 4 * (β + |a * b|) ≤ μ0 * K0 := by
        rw [div_le_iff₀ hμ0p] at hKβ2; linarith
      nlinarith only [this, hjR, hj2, hμ0p]
    have hh1' : h ≤ 1 := hhh0.trans hh01
    obtain ⟨hm, hA⟩ := rl_marginT (a := a) (b := b) (τ := τ) (x := x) hP hQ hτ hs hspos hqs hα hβ hh hh1' hj1 hja hjb hβj (by linarith only [hjq])
    rw [← hqm, ← hβdef, ← hβ0def, ← hμ0] at hm
    have hsplit : (β + |a * b|) / ((j : ℝ) + 1 / 2) ^ 2 = β / ((j : ℝ) + 1 / 2) ^ 2 + |a * b| / ((j : ℝ) + 1 / 2) ^ 2 := by ring
    have hm2 : h * (β0 * qm + β0 * (a ^ 2 + b ^ 2) / 2) ≤ μ0 / 4 := by
      have : β0 * qm + β0 * (a ^ 2 + b ^ 2) / 2 = β0 * (qm + (a ^ 2 + b ^ 2) / 2) := by ring
      rw [this]; exact hh0c
    have hmm : m0 ≤ 2 * hrAkH P Q a b h j - |hrCkH P Q τ x a b h j| := by
      rw [hrAkH_eq, hrCkH_eq, hm0]; linarith only [hm, hsplit, hβj', hm2]
    refine ⟨?_, by rw [hrAkH_eq]; exact hA, hmm⟩
    have := abs_nonneg (hrCkH P Q τ x a b h j)
    linarith only [hmm, this, hm0p]
  have hkR0 : (K0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkR : (K0 : ℝ) ≤ (k : ℝ) + 1 / 2 := by linarith
  have hk1R : (2 : ℝ) ≤ ((k : ℝ) + 1 / 2) := hK02.trans hkR
  have hkpos : 0 < ((k : ℝ) + 1 / 2) := by linarith
  have h1 := hmarg k hk (by nlinarith only [hkq, hh])
  have h2 := hmarg (k + 1) (by omega) (by push_cast; nlinarith only [hkq, hh])
  refine ⟨h1, ⟨h2.1, h2.2.2⟩, ?_, ?_, ?_⟩
  · -- B bound
    have hCk := h1.2.2
    have hA1 := h1.2.1
    have hA0 := h1.1
    have hCle : |hrCkH P Q τ x a b h k| ≤ 3 / 2 := by linarith only [hCk, hA1, hm0p]
    have hCsq : hrCkH P Q τ x a b h k ^ 2 ≤ 9 / 4 := by
      have := sq_abs (hrCkH P Q τ x a b h k)
      nlinarith only [this, hCle, abs_nonneg (hrCkH P Q τ x a b h k)]
    have hA2 : hrAkH P Q a b h k ^ 2 ≤ 9 / 16 := by nlinarith only [hA1, hA0]
    have hAk1 : m0 / 2 ≤ hrAkH P Q a b h (k + 1) := by
      have := abs_nonneg (hrCkH P Q τ x a b h (k + 1)); linarith only [h2.2, this]
    have hAk1sq : m0 ^ 2 / 4 ≤ hrAkH P Q a b h (k + 1) ^ 2 := by nlinarith only [hAk1, hm0p]
    have : B * (m0 ^ 2 / 4) = 45 / 16 := by rw [hB]; field_simp; ring
    nlinarith only [hCsq, hA2, hAk1sq, this, hBp]
  · -- epsilon
    have hq : (((k : ℝ) + 1 / 2) + 1) * h ≤ qs / 2 := by nlinarith only [hkq, hh]
    have hkpos1 : (1 : ℝ) ≤ (k : ℝ) + 1 / 2 := by linarith
    have hja : a ^ 2 ≤ ((k : ℝ) + 1 / 2) ^ 2 := by
      have : |a| ≤ ((k : ℝ) + 1 / 2) := hab1.trans hkR
      nlinarith only [sq_abs a, abs_nonneg a, this]
    have hjb : b ^ 2 ≤ ((k : ℝ) + 1 / 2) ^ 2 := by
      have : |b| ≤ ((k : ℝ) + 1 / 2) := hab2.trans hkR
      nlinarith only [sq_abs b, abs_nonneg b, this]
    have hβj : β / ((k : ℝ) + 1 / 2) ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith only [hKβ, hkR, hk1R]
    have hi := rl_incrT (a := a) (b := b) (τ := τ) (x := x) hP hQ hτ hqs hP1 hQ1 hh (hhh0.trans hh01) hkpos1 hja hjb hβj hq
    rw [← hqm, ← hβdef, ← hβ0def, ← hL, ← hΛ1] at hi
    have hk2 : 0 ≤ 1 / ((k : ℝ) + 1 / 2) ^ 2 := by positivity
    have e1 : (β + 2 * |a * b|) / ((k : ℝ) + 1 / 2) ^ 2 + Λ1 * h ≤ Λ0 * (1 / ((k : ℝ) + 1 / 2) ^ 2 + h) := by
      have : (β + 2 * |a * b|) / ((k : ℝ) + 1 / 2) ^ 2 = (β + 2 * |a * b|) * (1 / ((k : ℝ) + 1 / 2) ^ 2) := by ring
      rw [this, hΛ0]
      nlinarith only [mul_nonneg hΛ10 hk2, mul_nonneg (add_nonneg hβ0.le (mul_nonneg two_pos.le (abs_nonneg (a * b)))) hh.le, hΛ10, hh, hk2]
    have hi' : |hrAkH P Q a b h (k + 1) - hrAkH P Q a b h k| + |hrCkH P Q τ x a b h (k + 1) - hrCkH P Q τ x a b h k| ≤
        (β + 2 * |a * b|) / ((k : ℝ) + 1 / 2) ^ 2 + Λ1 * h := by
      rw [hrAkH_succ, hrCkH_succ, hrAkH_eq, hrCkH_eq]; exact hi
    have hnn : 0 ≤ 2 * (1 + B) := by positivity
    calc 2 * (1 + B) * (|hrAkH P Q a b h (k + 1) - hrAkH P Q a b h k| + |hrCkH P Q τ x a b h (k + 1) - hrCkH P Q τ x a b h k|)
        ≤ 2 * (1 + B) * ((β + 2 * |a * b|) / ((k : ℝ) + 1 / 2) ^ 2 + Λ1 * h) := mul_le_mul_of_nonneg_left hi' hnn
      _ ≤ 2 * (1 + B) * (Λ0 * (1 / ((k : ℝ) + 1 / 2) ^ 2 + h)) := mul_le_mul_of_nonneg_left e1 hnn
      _ = m0 * (2 * (1 + B) * Λ0 / m0 * (1 / ((k : ℝ) + 1 / 2) ^ 2 + h)) :=
          by rw [← mul_assoc]; exact (rlH_cancel m0 (2 * (1 + B) * Λ0) (1 / ((k : ℝ) + 1 / 2) ^ 2 + h) hm0p).symm
  · obtain ⟨tk, htk⟩ : ∃ tk : ℝ, tk = (k : ℝ) + 1 / 2 := ⟨_, rfl⟩
    have hkpos' : 0 < tk := by rw [htk]; exact hkpos
    have hk1R' : 2 ≤ tk := by rw [htk]; exact hk1R
    have hKtk : (K0 : ℝ) ≤ tk := by rw [htk]; exact hkR
    rw [← htk]
    have h1k : 1 / tk ^ 2 ≤ 1 / tk := by
      apply one_div_le_one_div_of_le hkpos'; nlinarith only [hk1R']
    have hÊk : Ê * (1 / tk) ≤ 1 / 4 := by
      rw [← div_eq_mul_one_div, div_le_iff₀ hkpos']; linarith only [hKÊ, hKtk]
    have hÊh : Ê * h ≤ 1 / 4 := by
      have h1 : h ≤ 1 / (4 * Ê + 1) := hhh0.trans hh0b
      rw [le_div_iff₀ (by positivity)] at h1
      nlinarith only [h1, hÊ0, hh]
    have h3 := mul_le_mul_of_nonneg_left h1k hÊ0
    have h4 : Ê * (1 / tk ^ 2 + h) = Ê * (1 / tk ^ 2) + Ê * h := by ring
    linarith only [h3, h4, hÊk, hÊh]

/-- **The band comparison** for the closed-form Racah coefficients. -/
theorem rl_bandH {P Q a b τ x qs : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hτ : τ ^ 2 = 1) (hs : 1 - x ^ 2 = rkS P Q x * qs ^ 2)
    (hspos : 0 < rkS P Q x) (hqs : 0 < qs) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2) :
    ∃ (K0 : ℕ) (h0 Cb : ℝ), 2 ≤ K0 ∧ 0 < h0 ∧ h0 ≤ 1 ∧ 1 ≤ Cb ∧ |a| ≤ K0 ∧ |b| ≤ K0 ∧
      ∀ (h : ℝ) (Y : ℤ → ℝ), 0 < h → h ≤ h0 → ∀ k0 k1 : ℤ, (K0 : ℤ) ≤ k0 → k0 ≤ k1 → ((k1 : ℝ) + 3) * h ≤ qs / 2 →
        (∀ k ∈ Finset.Ico k0 k1, jac (hrAkH P Q a b h) (hrCkH P Q τ x a b h) Y k = 0) →
        Y k1 ^ 2 + Y (k1 - 1) ^ 2 ≤ Cb * (Y k0 ^ 2 + Y (k0 - 1) ^ 2) ∧
        Y k0 ^ 2 + Y (k0 - 1) ^ 2 ≤ Cb * (Y k1 ^ 2 + Y (k1 - 1) ^ 2) := by
  obtain ⟨K0, h0, m0, B, Λ0, hK02, hh0, hh01, hm0, hB, hΛ0, hKa, hKb, key⟩ :=
    rl_coef_allH (a := a) (b := b) (τ := τ) hP hQ hτ hs hspos hqs hα hβ
  set Ê : ℝ := 2 * (1 + B) * Λ0 / m0 with hÊ
  have hÊ0 : 0 ≤ Ê := by positivity
  set E0 : ℝ := Ê * (1 + qs / 2) with hE0
  refine ⟨K0, h0, max 1 (3 * Real.exp (2 * E0) / m0), by exact_mod_cast hK02, hh0, hh01, le_max_left _ _, hKa, hKb, ?_⟩
  intro h Y hh hhh0 k0 k1 hk0 hk01 hq hrow
  have hk0R : (2 : ℝ) ≤ (k0 : ℝ) + 1 / 2 := by
    have : (K0 : ℤ) ≤ k0 := hk0
    have h2 : (2 : ℝ) ≤ (K0 : ℝ) := by exact_mod_cast hK02
    have : (K0 : ℝ) ≤ (k0 : ℝ) := by exact_mod_cast hk0
    linarith
  have hk1R : (k0 : ℝ) ≤ (k1 : ℝ) := by exact_mod_cast hk01
  have hat : ∀ k ∈ Finset.Icc k0 k1, (K0 : ℤ) ≤ k ∧ ((k : ℝ) + 3) * h ≤ qs / 2 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    refine ⟨by omega, ?_⟩
    have : (k : ℝ) ≤ (k1 : ℝ) := by exact_mod_cast hk.2
    nlinarith only [this, hq, hh]
  have hatI : ∀ k ∈ Finset.Ico k0 k1, (K0 : ℤ) ≤ k ∧ ((k : ℝ) + 3) * h ≤ qs / 2 := fun k hk =>
    hat k (Finset.Ico_subset_Icc_self hk)
  have hcomp := rl_comp (a := hrAkH P Q a b h) (c := hrCkH P Q τ x a b h) (Y := Y)
    (ε := fun k => Ê * (1 / ((k : ℝ) + 1 / 2) ^ 2 + h)) (k0 := k0) (k1 := k1) (m0 := m0) (B := B) (E0 := E0) hm0 hk01 hrow
    (fun k hk => ⟨(key h hh hhh0 k (hat k hk).1 (hat k hk).2).1.1, (key h hh hhh0 k (hat k hk).1 (hat k hk).2).1.2.1⟩)
    (fun k hk => (key h hh hhh0 k (hat k hk).1 (hat k hk).2).1.2.2)
    (fun k hk => (key h hh hhh0 k (hatI k hk).1 (hatI k hk).2).2.2.1)
    (fun k hk => (key h hh hhh0 k (hatI k hk).1 (hatI k hk).2).2.2.2.1)
    (fun k hk => by
      have : 0 ≤ 1 / ((k : ℝ) + 1 / 2) ^ 2 + h := by positivity
      positivity)
    (fun k hk => (key h hh hhh0 k (hatI k hk).1 (hatI k hk).2).2.2.2.2)
    (by
      rw [kk_ico_range _ hk01]
      have e1 : ∀ i ∈ range (k1 - k0).toNat, Ê * (1 / ((((k0 + (i : ℤ) : ℤ) : ℝ) + 1 / 2)) ^ 2 + h) =
          Ê * (1 / ((k0 : ℝ) + 1 / 2 + (i : ℝ)) ^ 2) + Ê * h := by
        intro i _; push_cast; ring
      rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, ← Finset.mul_sum]
      have h1 := kl_sum_inv_sq_le_one hk0R (k1 - k0).toNat
      have h2 : ∑ i ∈ range (k1 - k0).toNat, Ê * h = ((k1 - k0).toNat : ℝ) * (Ê * h) := by simp
      rw [h2]
      have hn : ((k1 - k0).toNat : ℝ) ≤ (k1 : ℝ) := by
        have : ((k1 - k0).toNat : ℤ) ≤ k1 := by omega
        have h' : (((k1 - k0).toNat : ℤ) : ℝ) ≤ (k1 : ℝ) := by exact_mod_cast this
        exact_mod_cast h'
      have hnh : ((k1 - k0).toNat : ℝ) * h ≤ qs / 2 := by nlinarith only [hn, hq, hh]
      have h3 : ((k1 - k0).toNat : ℝ) * (Ê * h) ≤ Ê * (qs / 2) := by
        have : ((k1 - k0).toNat : ℝ) * (Ê * h) = Ê * (((k1 - k0).toNat : ℝ) * h) := by ring
        rw [this]; exact mul_le_mul_of_nonneg_left hnh hÊ0
      have h4 := mul_le_mul_of_nonneg_left h1 hÊ0
      rw [hE0]
      nlinarith only [h3, h4])
  refine ⟨hcomp.1.trans ?_, hcomp.2.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)


end FormalResearch.Special
