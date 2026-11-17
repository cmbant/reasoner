module

public import FormalResearch.Special.DiscreteAiryKappaBand3j

/-!
# Sharp `κ`: the band errors are `O(h + 1/k₀)` (plan K1, sharp constant, step 5)

The explicit error functions of the band mass (`kpEps`, `kpDub`, `kpRb`, `DiscreteAiryKappaTransport`, `DiscreteAiryKappaBandHahn`) are *affine* in
`(h, h², η̄, κ̄)` with coefficients bounded by `K₀ = 200/(x A⁹)` (`A ≤ 1`, `x ≤ 1`).  With `η̄_i = β₀/(k₀+i)²`, `κ̄_i = μ₀/(k₀+i)²`,
`Σ_{i<n} (k₀+i)^{-2} ≤ 2/k₀` and `(m+1) h ≤ 1`:

* `ksb_S_le`: `kb3S ≤ K₀ (h + 2(β₀+μ₀)/k₀)`;
* `ksb_eps_le`: each `kpEps ≤ K₀ (h + 2(β₀ + μ₀)/k₀)`;
* `ksb_Dub_le`, `ksb_Rb_le`: `kpDub, kpRb ≤ K₀ (h + β₀/k₀ + μ₀/k₀)`.

**Claim class: proved.**
-/

@[expose] public section

open Finset

namespace FormalResearch.Special

/-- `kpEps` is affine in `(h², η̄, κ̄)`. -/
lemma ksb_eps_eq {x h A ηb κb : ℝ} (hx : 0 < x) (hA : 0 < A) :
    kpEps x h A ηb κb = (80 / (x * A ^ 4) + 120 * x / A ^ 7) * h ^ 2 + 80 / (x * A ^ 2) * ηb + 80 / A ^ 2 * κb := by
  unfold kpEps
  field_simp
  ring

lemma ksb_eps_le {x h A ηb κb : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hA : 0 < A) (hA1 : A ≤ 1)
    (hη : 0 ≤ ηb) (hκ : 0 ≤ κb) :
    kpEps x h A ηb κb ≤ 200 / (x * A ^ 9) * (h ^ 2 + ηb + κb) := by
  rw [ksb_eps_eq hx hA]
  have hA9 : A ^ 4 ≥ A ^ 9 := pow_le_pow_of_le_one hA.le hA1 (by norm_num)
  have hA9' : A ^ 7 ≥ A ^ 9 := pow_le_pow_of_le_one hA.le hA1 (by norm_num)
  have hA9'' : A ^ 2 ≥ A ^ 9 := pow_le_pow_of_le_one hA.le hA1 (by norm_num)
  have hp9 : 0 < A ^ 9 := by positivity
  have c1 : 80 / (x * A ^ 4) ≤ 80 / (x * A ^ 9) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (mul_le_mul_of_nonneg_left hA9 hx.le)
  have c2 : 120 * x / A ^ 7 ≤ 120 / (x * A ^ 9) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : x * (x * A ^ 9) ≤ 1 * A ^ 7 := by nlinarith [mul_le_mul hx1 hx1 hx.le (by norm_num : (0 : ℝ) ≤ 1), hA9']
    nlinarith [this]
  have c3 : 80 / (x * A ^ 2) ≤ 200 / (x * A ^ 9) :=
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) (mul_le_mul_of_nonneg_left hA9'' hx.le)).trans
      (by apply div_le_div_of_nonneg_right (by norm_num) (by positivity))
  have c4 : 80 / A ^ 2 ≤ 200 / (x * A ^ 9) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hA9'' (by norm_num : (0 : ℝ) ≤ 80), mul_pos hx hp9, mul_le_mul_of_nonneg_left hx1 hp9.le]
  have c5 : (80 / (x * A ^ 4) + 120 * x / A ^ 7) ≤ 200 / (x * A ^ 9) := by
    have : 80 / (x * A ^ 9) + 120 / (x * A ^ 9) = 200 / (x * A ^ 9) := by ring
    linarith
  have hK : 0 ≤ 200 / (x * A ^ 9) := by positivity
  have t1 : (80 / (x * A ^ 4) + 120 * x / A ^ 7) * h ^ 2 ≤ 200 / (x * A ^ 9) * h ^ 2 :=
    mul_le_mul_of_nonneg_right c5 (sq_nonneg h)
  have t2 : 80 / (x * A ^ 2) * ηb ≤ 200 / (x * A ^ 9) * ηb := mul_le_mul_of_nonneg_right c3 hη
  have t3 : 80 / A ^ 2 * κb ≤ 200 / (x * A ^ 9) * κb := mul_le_mul_of_nonneg_right c4 hκ
  nlinarith [t1, t2, t3]

/-- `1/A^n ≤ 1/A^9` for `0 < A ≤ 1`, `n ≤ 9`. -/
lemma ksb_inv_pow {A : ℝ} (hA : 0 < A) (hA1 : A ≤ 1) {n : ℕ} (hn : n ≤ 9) : 1 / A ^ n ≤ 1 / A ^ 9 := by
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_of_le_one hA.le hA1 hn

/-- Affine bound: `c₁ h + c₂ h² + c₃ η + c₄ κ ≤ K (h + η + κ)` if `c₁ + c₂ ≤ K`, `c₃, c₄ ≤ K`, `0 ≤ h ≤ 1`. -/
lemma ksb_affine {c1 c2 c3 c4 h η κ K : ℝ} (hc2 : 0 ≤ c2) (hc12 : c1 + c2 ≤ K) (hc3 : c3 ≤ K) (hc4 : c4 ≤ K)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hη : 0 ≤ η) (hκ : 0 ≤ κ) :
    c1 * h + c2 * h ^ 2 + c3 * η + c4 * κ ≤ K * (h + η + κ) := by
  have h2 : h ^ 2 ≤ h := by nlinarith
  have t1 : c1 * h + c2 * h ^ 2 ≤ (c1 + c2) * h := by nlinarith [mul_le_mul_of_nonneg_left h2 hc2]
  have t2 : (c1 + c2) * h ≤ K * h := mul_le_mul_of_nonneg_right hc12 hh
  have t3 : c3 * η ≤ K * η := mul_le_mul_of_nonneg_right hc3 hη
  have t4 : c4 * κ ≤ K * κ := mul_le_mul_of_nonneg_right hc4 hκ
  nlinarith [t1, t2, t3, t4]

lemma ksb_Dub_eq {x h A ηb : ℝ} (hx : 0 < x) (hA : 0 < A) :
    kpDub x h A ηb = (2 / A ^ 4 + x / A ^ 4) * h + (2 / (x * A ^ 4) + x / (2 * A ^ 7)) * h ^ 2 + 2 / (x * A ^ 2) * ηb := by
  unfold kpDub
  field_simp
  ring

lemma ksb_Rb_eq {x h A ηb κb : ℝ} (hx : 0 < x) (hA : 0 < A) :
    kpRb x h A ηb κb = (1 / (2 * A ^ 2) + 2 / A ^ 5 + x / A ^ 5) * h + (4 / (x * A ^ 5) + 7 * x / (2 * A ^ 8)) * h ^ 2 +
      4 / (x * A ^ 3) * ηb + 2 / A ^ 3 * κb := by
  unfold kpRb
  rw [ksb_Dub_eq hx hA]
  field_simp
  ring

/-- Coefficient bound `c/(x^e A^n) ≤ c/(x A^9)`, packaged: for `0 < x, A ≤ 1`: `1/A^n ≤ 1/(x A^9)` and `x/A^n ≤ 1/(x A^9)` (`n ≤ 9`). -/
lemma ksb_coef_a {x A : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hA : 0 < A) (hA1 : A ≤ 1) {n : ℕ} (hn : n ≤ 9) :
    1 / A ^ n ≤ 1 / (x * A ^ 9) ∧ x / A ^ n ≤ 1 / (x * A ^ 9) ∧ 1 / (x * A ^ n) ≤ 1 / (x * A ^ 9) := by
  have h1 := ksb_inv_pow hA hA1 hn
  have hp : 0 < A ^ 9 := by positivity
  have e1 : 1 / A ^ 9 ≤ 1 / (x * A ^ 9) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hx1 hp.le]
  refine ⟨h1.trans e1, ?_, ?_⟩
  · calc x / A ^ n = x * (1 / A ^ n) := by ring
      _ ≤ 1 * (1 / A ^ 9) := mul_le_mul hx1 h1 (by positivity) (by norm_num)
      _ ≤ _ := by rw [one_mul]; exact e1
  · have : 1 / (x * A ^ n) = (1 / x) * (1 / A ^ n) := by field_simp
    rw [this]
    calc (1 / x) * (1 / A ^ n) ≤ (1 / x) * (1 / A ^ 9) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 / (x * A ^ 9) := by field_simp

lemma ksb_Dub_le {x h A ηb : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hA : 0 < A) (hA1 : A ≤ 1) (hh : 0 ≤ h) (hh1 : h ≤ 1) (hη : 0 ≤ ηb) :
    kpDub x h A ηb ≤ 200 / (x * A ^ 9) * (h + ηb) := by
  rw [ksb_Dub_eq hx hA]
  have a4 := ksb_coef_a hx hx1 hA hA1 (n := 4) (by norm_num)
  have a7 := ksb_coef_a hx hx1 hA hA1 (n := 7) (by norm_num)
  have a2 := ksb_coef_a hx hx1 hA hA1 (n := 2) (by norm_num)
  have e1 : 2 / A ^ 4 = 2 * (1 / A ^ 4) := by ring
  have e2 : 2 / (x * A ^ 4) = 2 * (1 / (x * A ^ 4)) := by ring
  have e3 : x / (2 * A ^ 7) = x / A ^ 7 / 2 := by ring
  have e4 : 2 / (x * A ^ 2) = 2 * (1 / (x * A ^ 2)) := by ring
  have hK : 200 / (x * A ^ 9) = 200 * (1 / (x * A ^ 9)) := by ring
  have hu : 0 ≤ 1 / (x * A ^ 9) := by positivity
  have key := ksb_affine (c1 := 2 / A ^ 4 + x / A ^ 4) (c2 := 2 / (x * A ^ 4) + x / (2 * A ^ 7)) (c3 := 2 / (x * A ^ 2)) (c4 := 0)
    (h := h) (η := ηb) (κ := 0) (K := 200 / (x * A ^ 9)) (by positivity) ?_ ?_ (by positivity) hh hh1 hη le_rfl
  · simpa using key
  · rw [e1, e2, e3, hK]; linarith [a4.1, a4.2.1, a4.2.2, a7.2.1, a7.1]
  · rw [e4, hK]; linarith [a2.2.2]

lemma ksb_Rb_le {x h A ηb κb : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hA : 0 < A) (hA1 : A ≤ 1) (hh : 0 ≤ h) (hh1 : h ≤ 1) (hη : 0 ≤ ηb)
    (hκ : 0 ≤ κb) : kpRb x h A ηb κb ≤ 200 / (x * A ^ 9) * (h + ηb + κb) := by
  rw [ksb_Rb_eq hx hA]
  have a5 := ksb_coef_a hx hx1 hA hA1 (n := 5) (by norm_num)
  have a8 := ksb_coef_a hx hx1 hA hA1 (n := 8) (by norm_num)
  have a2 := ksb_coef_a hx hx1 hA hA1 (n := 2) (by norm_num)
  have a3 := ksb_coef_a hx hx1 hA hA1 (n := 3) (by norm_num)
  have e1 : 1 / (2 * A ^ 2) = 1 / A ^ 2 / 2 := by ring
  have e2 : 2 / A ^ 5 = 2 * (1 / A ^ 5) := by ring
  have e3 : 4 / (x * A ^ 5) = 4 * (1 / (x * A ^ 5)) := by ring
  have e4 : 7 * x / (2 * A ^ 8) = 7 * (x / A ^ 8) / 2 := by ring
  have e5 : 4 / (x * A ^ 3) = 4 * (1 / (x * A ^ 3)) := by ring
  have e6 : 2 / A ^ 3 = 2 * (1 / A ^ 3) := by ring
  have hK : 200 / (x * A ^ 9) = 200 * (1 / (x * A ^ 9)) := by ring
  have hu : 0 ≤ 1 / (x * A ^ 9) := by positivity
  have key := ksb_affine (c1 := 1 / (2 * A ^ 2) + 2 / A ^ 5 + x / A ^ 5) (c2 := 4 / (x * A ^ 5) + 7 * x / (2 * A ^ 8))
    (c3 := 4 / (x * A ^ 3)) (c4 := 2 / A ^ 3) (h := h) (η := ηb) (κ := κb) (K := 200 / (x * A ^ 9)) (by positivity)
    ?_ ?_ ?_ hh hh1 hη hκ
  · exact key
  · rw [e1, e2, e3, e4, hK]; linarith [a2.1, a5.1, a5.2.1, a5.2.2, a8.2.1]
  · rw [e5, hK]; linarith [a3.2.2]
  · rw [e6, hK]; linarith [a3.1]

/-- `Σ_{i<n} 1/(k₀+i)² ≤ 2/k₀` for an integer `k₀ ≥ 1`. -/
lemma ksb_sum_inv_sq {k0 : ℤ} (hk0 : 1 ≤ k0) (n : ℕ) :
    ∑ i ∈ range n, 1 / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2 ≤ 2 / (k0 : ℝ) - 2 / ((k0 : ℝ) + n) := by
  have hk : (1 : ℝ) ≤ k0 := by exact_mod_cast hk0
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hpos : 0 < (k0 : ℝ) + n := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
    have e : (((k0 + (n : ℤ) : ℤ) : ℝ)) = (k0 : ℝ) + n := by push_cast; ring
    rw [e]
    have h1 : 1 / ((k0 : ℝ) + n) ^ 2 ≤ 2 / ((k0 : ℝ) + n) - 2 / ((k0 : ℝ) + ((n + 1 : ℕ) : ℝ)) := by
      have e2 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [e2, div_sub_div _ _ hpos.ne' (by linarith : (k0 : ℝ) + ((n : ℝ) + 1) ≠ 0), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hpos]
    have e3 : 2 / (k0 : ℝ) - 2 / ((k0 : ℝ) + n) + (2 / ((k0 : ℝ) + n) - 2 / ((k0 : ℝ) + ((n + 1 : ℕ) : ℝ))) =
        2 / (k0 : ℝ) - 2 / ((k0 : ℝ) + ((n + 1 : ℕ) : ℝ)) := by ring
    linarith [ih]

lemma ksb_sum_inv_sq' {k0 : ℤ} (hk0 : 1 ≤ k0) (n : ℕ) :
    ∑ i ∈ range n, 1 / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2 ≤ 2 / (k0 : ℝ) := by
  have := ksb_sum_inv_sq hk0 n
  have hk : (1 : ℝ) ≤ k0 := by exact_mod_cast hk0
  have : 0 ≤ 2 / ((k0 : ℝ) + n) := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; positivity
  linarith

/-- **`kb3S` is `O(h + 1/k₀)`**: `kb3S ≤ K (h + 2(3β + |Mσ|)/k₀)`, `K = 200/(x A⁹)`, if `(m+1)h ≤ 1`. -/
lemma ksb_S_le (M σ : ℤ) {x h A : ℝ} {k0 : ℤ} {m : ℕ} (hx : 0 < x) (hx1 : x ≤ 1) (hA : 0 < A) (hA1 : A ≤ 1) (hh : 0 ≤ h)
    (hk0 : 1 ≤ k0) (hmh : ((m : ℝ) + 1) * h ≤ 1) :
    kb3S M σ x h A k0 m ≤ 200 / (x * A ^ 9) * (h + 2 * (3 * kl_beta (M : ℝ) (σ : ℝ) + |(M : ℝ) * (σ : ℝ)|) / (k0 : ℝ)) := by
  unfold kb3S
  have hβ0 : 0 ≤ kl_beta (M : ℝ) (σ : ℝ) := by unfold kl_beta; positivity
  have hk : (1 : ℝ) ≤ k0 := by exact_mod_cast hk0
  set K : ℝ := 200 / (x * A ^ 9) with hK
  have hK0 : 0 ≤ K := by positivity
  have hterm : ∀ i ∈ range (m + 1), kpEps x h A (3 * kl_beta (M : ℝ) (σ : ℝ) / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2)
      (|(M : ℝ) * (σ : ℝ)| / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2) ≤
      K * (h ^ 2 + (3 * kl_beta (M : ℝ) (σ : ℝ) + |(M : ℝ) * (σ : ℝ)|) * (1 / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2)) := by
    intro i _
    refine (ksb_eps_le hx hx1 hA hA1 (by positivity) (by positivity)).trans ?_
    apply le_of_eq
    rw [← hK]; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum, nsmul_eq_mul]
  have hs := ksb_sum_inv_sq' hk0 (m + 1)
  have h2 : ((m + 1 : ℕ) : ℝ) * h ^ 2 ≤ h := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hmh hh, sq_nonneg h]
  have hc : 0 ≤ 3 * kl_beta (M : ℝ) (σ : ℝ) + |(M : ℝ) * (σ : ℝ)| := by positivity
  have h3 := mul_le_mul_of_nonneg_left hs hc
  apply mul_le_mul_of_nonneg_left _ hK0
  have e : 2 * (3 * kl_beta (M : ℝ) (σ : ℝ) + |(M : ℝ) * (σ : ℝ)|) / (k0 : ℝ) =
      (3 * kl_beta (M : ℝ) (σ : ℝ) + |(M : ℝ) * (σ : ℝ)|) * (2 / (k0 : ℝ)) := by ring
  rw [e]; linarith

/-- The band error scale `S_bd = K (h + 2(3β + |Mσ|)/k₀)`, `K = 200/(x A⁹)`. -/
noncomputable def ksbSbd (M σ : ℤ) (x h A : ℝ) (k0 : ℤ) : ℝ :=
  200 / (x * A ^ 9) * (h + 2 * (3 * kl_beta (M : ℝ) (σ : ℝ) + |(M : ℝ) * (σ : ℝ)|) / (k0 : ℝ))

/-- `e^s ≤ 1 + 2s` for `0 ≤ s ≤ 1/2`. -/
lemma ksb_exp_le {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) : Real.exp s ≤ 1 + 2 * s := by
  have h := Real.exp_bound_div_one_sub_of_interval h0 (by linarith : s < 1)
  have h2 : 1 / (1 - s) ≤ 1 + 2 * s := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  exact h.trans h2

lemma ksb_eps_nonneg {x h A ηb κb : ℝ} (hx : 0 < x) (hA : 0 < A) (hη : 0 ≤ ηb) (hκ : 0 ≤ κb) : 0 ≤ kpEps x h A ηb κb := by
  unfold kpEps; positivity

lemma ksb_S_nonneg (M σ : ℤ) {x h A : ℝ} {k0 : ℤ} {m : ℕ} (hx : 0 < x) (hA : 0 < A) : 0 ≤ kb3S M σ x h A k0 m := by
  unfold kb3S
  have hβ0 : 0 ≤ kl_beta (M : ℝ) (σ : ℝ) := by unfold kl_beta; positivity
  exact Finset.sum_nonneg fun i _ => ksb_eps_nonneg hx hA (by positivity) (by positivity)

/-- The error factor of the band mass: abstract form. -/
lemma ksb_mass_err {S Sb r τ A sv : ℝ} (hA0 : 0 < A) (hA1 : A ≤ 1) (hS0 : 0 ≤ S) (hSS : S ≤ Sb) (hSb : Sb ≤ 1 / 4)
    (hr0 : 0 ≤ r) (hr' : r ≤ Sb) (hτ0 : 0 ≤ τ) (hτ' : τ ≤ Sb) (hsv : 0 ≤ sv) :
    ((Real.exp (2 * S) - 1) * Real.exp S + 4 * (|r| + τ) * Real.exp S) * sv + (2 * τ / A + 32 / A ^ 3) * Real.exp S ≤
      18 * Sb * sv + 50 / A ^ 3 := by
  have hA3 : 0 < A ^ 3 := by positivity
  have heS : Real.exp S ≤ 1 + 2 * S := ksb_exp_le hS0 (by linarith)
  have he2S : Real.exp (2 * S) ≤ 1 + 4 * S := by
    have := ksb_exp_le (s := 2 * S) (by linarith) (by linarith)
    linarith
  have e1 : Real.exp S ≤ 3 / 2 := by linarith
  have hE1 : (Real.exp (2 * S) - 1) * Real.exp S + 4 * (|r| + τ) * Real.exp S ≤ 18 * Sb := by
    rw [abs_of_nonneg hr0]
    have t1 : (Real.exp (2 * S) - 1) * Real.exp S ≤ 4 * S * (3 / 2) :=
      mul_le_mul (by linarith) e1 (Real.exp_pos _).le (by linarith)
    have t2 : 4 * (r + τ) * Real.exp S ≤ 4 * (Sb + Sb) * (3 / 2) :=
      mul_le_mul (by linarith) e1 (Real.exp_pos _).le (by linarith)
    linarith
  have hE2 : (2 * τ / A + 32 / A ^ 3) * Real.exp S ≤ 50 / A ^ 3 := by
    have h1 : 2 * τ / A ≤ 1 / A ^ 3 := by
      rw [div_le_div_iff₀ hA0 hA3]
      have hA2 : A ^ 2 ≤ 1 := pow_le_one₀ hA0.le hA1
      nlinarith [mul_le_mul_of_nonneg_left hA2 hτ0]
    have : (2 * τ / A + 32 / A ^ 3) ≤ 33 / A ^ 3 := by
      have : 33 / A ^ 3 = 1 / A ^ 3 + 32 / A ^ 3 := by ring
      linarith
    calc (2 * τ / A + 32 / A ^ 3) * Real.exp S ≤ 33 / A ^ 3 * (3 / 2) :=
          mul_le_mul this e1 (Real.exp_pos _).le (by positivity)
      _ ≤ 50 / A ^ 3 := by
          rw [show 33 / A ^ 3 * (3 / 2) = (99 / 2) / A ^ 3 by ring]
          exact div_le_div_of_nonneg_right (by norm_num) hA3.le
  have := mul_le_mul_of_nonneg_right hE1 hsv
  linarith

/-- `K (h + η_B + κ_B) ≤ S_bd` for `η_B = 3β/k₀²`, `κ_B = |Mσ|/k₀²`. -/
lemma ksb_scale (M σ : ℤ) {x h A : ℝ} {k0 : ℤ} (hx : 0 < x) (hA : 0 < A) (hk0 : 1 ≤ k0) :
    200 / (x * A ^ 9) * (h + 3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2 + |(M : ℝ) * (σ : ℝ)| / (k0 : ℝ) ^ 2) ≤ ksbSbd M σ x h A k0 := by
  have hk : (1 : ℝ) ≤ k0 := by exact_mod_cast hk0
  have hk0p : 0 < (k0 : ℝ) := by linarith
  have hβ0 : 0 ≤ kl_beta (M : ℝ) (σ : ℝ) := by unfold kl_beta; positivity
  have hK0 : 0 < 200 / (x * A ^ 9) := by positivity
  unfold ksbSbd
  apply mul_le_mul_of_nonneg_left _ hK0.le
  have hηk : 3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2 ≤ 3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) := by
    apply div_le_div_of_nonneg_left (by positivity) hk0p; nlinarith
  have hκk : |(M : ℝ) * (σ : ℝ)| / (k0 : ℝ) ^ 2 ≤ |(M : ℝ) * (σ : ℝ)| / (k0 : ℝ) := by
    apply div_le_div_of_nonneg_left (by positivity) hk0p; nlinarith
  have e : 2 * (3 * kl_beta (M : ℝ) (σ : ℝ) + |(M : ℝ) * (σ : ℝ)|) / (k0 : ℝ) =
      3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) + |(M : ℝ) * (σ : ℝ)| / (k0 : ℝ) +
        (3 * kl_beta (M : ℝ) (σ : ℝ) + |(M : ℝ) * (σ : ℝ)|) / (k0 : ℝ) := by ring
  have : 0 ≤ (3 * kl_beta (M : ℝ) (σ : ℝ) + |(M : ℝ) * (σ : ℝ)|) / (k0 : ℝ) := by positivity
  linarith

/-- The one-site hypothesis of the band mass: each `kpEps ≤ S_bd`. -/
lemma ksb_eps_site (M σ : ℤ) {x h A : ℝ} {k0 : ℤ} (hx : 0 < x) (hx1 : x ≤ 1) (hA : 0 < A) (hA1 : A ≤ 1) (hh : 0 ≤ h)
    (hh1 : h ≤ 1) (hk0 : 1 ≤ k0) (i : ℕ) :
    kpEps x h A (3 * kl_beta (M : ℝ) (σ : ℝ) / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2)
      (|(M : ℝ) * (σ : ℝ)| / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2) ≤ ksbSbd M σ x h A k0 := by
  have hk : (1 : ℝ) ≤ k0 := by exact_mod_cast hk0
  have hk0p : 0 < (k0 : ℝ) := by linarith
  have hβ0 : 0 ≤ kl_beta (M : ℝ) (σ : ℝ) := by unfold kl_beta; positivity
  have hc0 : 0 ≤ 3 * kl_beta (M : ℝ) (σ : ℝ) + |(M : ℝ) * (σ : ℝ)| := by positivity
  have hK0 : 0 < 200 / (x * A ^ 9) := by positivity
  have hq : 1 / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2 ≤ 1 / (k0 : ℝ) := by
    have h1 : (k0 : ℝ) ≤ (((k0 + (i : ℤ) : ℤ) : ℝ)) := by push_cast; have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith
    have h2 : (k0 : ℝ) ≤ (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2 := by nlinarith
    exact one_div_le_one_div_of_le hk0p h2
  refine (ksb_eps_le hx hx1 hA hA1 (by positivity) (by positivity)).trans ?_
  have h2 : h ^ 2 ≤ h := by nlinarith
  have e : 3 * kl_beta (M : ℝ) (σ : ℝ) / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2 + |(M : ℝ) * (σ : ℝ)| / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2 =
      (3 * kl_beta (M : ℝ) (σ : ℝ) + |(M : ℝ) * (σ : ℝ)|) * (1 / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2) := by ring
  have h3 : (3 * kl_beta (M : ℝ) (σ : ℝ) + |(M : ℝ) * (σ : ℝ)|) * (1 / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2) ≤
      2 * (3 * kl_beta (M : ℝ) (σ : ℝ) + |(M : ℝ) * (σ : ℝ)|) / (k0 : ℝ) := by
    have := mul_le_mul_of_nonneg_left hq hc0
    have e2 : 2 * (3 * kl_beta (M : ℝ) (σ : ℝ) + |(M : ℝ) * (σ : ℝ)|) / (k0 : ℝ) =
        2 * ((3 * kl_beta (M : ℝ) (σ : ℝ) + |(M : ℝ) * (σ : ℝ)|) * (1 / (k0 : ℝ))) := by ring
    rw [e2]
    have : 0 ≤ (3 * kl_beta (M : ℝ) (σ : ℝ) + |(M : ℝ) * (σ : ℝ)|) * (1 / (k0 : ℝ)) := by positivity
    nlinarith
  unfold ksbSbd
  apply mul_le_mul_of_nonneg_left _ hK0.le
  rw [add_assoc, e]; linarith

/-- **The band mass and the transport of the actual `3j` chain, in clean form.**  Under the hypotheses of `hahn3j_band_mass`, with `h = 1/N`,
`(m+1) h ≤ 1` and `S_bd := ksbSbd ≤ 1/4`: `I_{k₀} ≥ 0`, `I_{k₀+i} ≤ (1 + 2S_bd) I_{k₀}`, `I_{k₀} ≤ (1 + 4S_bd) I_{k₀+i}` (`i ≤ m+1`) and
`|Σ_{i≤m} Ŷ_{k₀+i}² - I_{k₀} Σv| ≤ I_{k₀} (18 S_bd Σv + 50/A³)`, `Σv = Σ_{i≤m} P_{k₀+i}/2`. -/
theorem hahn3j_band_clean (M σ N : ℤ) (x : ℚ) (hN : 0 < N) (hx0 : (0 : ℝ) < x) (hx1 : (x : ℝ) < 1) {k0 : ℤ} (m : ℕ)
    {A : ℝ} (hk0 : 1 ≤ k0) (hβk : kl_beta (M : ℝ) (σ : ℝ) < (k0 : ℝ) ^ 2) (hA0 : 0 < A) (hA1 : A ≤ 1)
    (hband : ∀ j : ℤ, k0 - 1 ≤ j → j ≤ k0 + ((m + 1 : ℕ) : ℤ) →
      A ^ 2 ≤ (Real.sqrt (1 - (x : ℝ) ^ 2)) ^ 2 - kpU (1 / (N : ℝ)) j ^ 2)
    (hηB : 3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2 ≤ (x : ℝ) ^ 2)
    (hκB : |(M : ℝ) * (σ : ℝ)| / (k0 : ℝ) ^ 2 ≤ 1) (hmh : ((m : ℝ) + 1) * (1 / (N : ℝ)) ≤ 1)
    (hS : ksbSbd M σ (x : ℝ) (1 / (N : ℝ)) A k0 ≤ 1 / 4) :
    0 ≤ kermI (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (kpP (Real.sqrt (1 - (x : ℝ) ^ 2)) (1 / (N : ℝ))) (hahn3jY M σ N x) k0 ∧
    (∀ i : ℕ, i ≤ m + 1 →
      kermI (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (kpP (Real.sqrt (1 - (x : ℝ) ^ 2)) (1 / (N : ℝ))) (hahn3jY M σ N x)
          (k0 + (i : ℤ)) ≤
        (1 + 2 * ksbSbd M σ (x : ℝ) (1 / (N : ℝ)) A k0) *
          kermI (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (kpP (Real.sqrt (1 - (x : ℝ) ^ 2)) (1 / (N : ℝ))) (hahn3jY M σ N x) k0 ∧
      kermI (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (kpP (Real.sqrt (1 - (x : ℝ) ^ 2)) (1 / (N : ℝ))) (hahn3jY M σ N x) k0 ≤
        (1 + 4 * ksbSbd M σ (x : ℝ) (1 / (N : ℝ)) A k0) *
          kermI (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (kpP (Real.sqrt (1 - (x : ℝ) ^ 2)) (1 / (N : ℝ))) (hahn3jY M σ N x)
            (k0 + (i : ℤ))) ∧
    |∑ i ∈ range (m + 1), hahn3jY M σ N x (k0 + (i : ℤ)) ^ 2 -
        kermI (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (kpP (Real.sqrt (1 - (x : ℝ) ^ 2)) (1 / (N : ℝ))) (hahn3jY M σ N x) k0 *
          ∑ i ∈ range (m + 1), kpP (Real.sqrt (1 - (x : ℝ) ^ 2)) (1 / (N : ℝ)) (k0 + (i : ℤ)) / 2| ≤
      kermI (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (kpP (Real.sqrt (1 - (x : ℝ) ^ 2)) (1 / (N : ℝ))) (hahn3jY M σ N x) k0 *
        (18 * ksbSbd M σ (x : ℝ) (1 / (N : ℝ)) A k0 *
            ∑ i ∈ range (m + 1), kpP (Real.sqrt (1 - (x : ℝ) ^ 2)) (1 / (N : ℝ)) (k0 + (i : ℤ)) / 2 + 50 / A ^ 3) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hxr : (x : ℝ) ≤ 1 := hx1.le
  have hhpos : 0 < 1 / (N : ℝ) := by positivity
  have hmh1 : 1 / (N : ℝ) ≤ 1 := by
    have : (1 : ℝ) ≤ (m : ℝ) + 1 := by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
    nlinarith
  have hk : (1 : ℝ) ≤ k0 := by exact_mod_cast hk0
  have hε : ∀ i : ℕ, i < m + 1 → kpEps (x : ℝ) (1 / (N : ℝ)) A (3 * kl_beta (M : ℝ) (σ : ℝ) / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2)
      (|(M : ℝ) * (σ : ℝ)| / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2) ≤ 1 / 2 := fun i _ =>
    (ksb_eps_site M σ hx0 hxr hA0 hA1 hhpos.le hmh1 hk0 i).trans (by linarith)
  obtain ⟨hI0, htr, hmass⟩ := hahn3j_band_mass M σ N x hN hx0 hx1 m hk0 hβk hA0 hA1 hband hηB hκB hε
  have hS0 : 0 ≤ kb3S M σ (x : ℝ) (1 / (N : ℝ)) A k0 m := ksb_S_nonneg M σ hx0 hA0
  have hSS : kb3S M σ (x : ℝ) (1 / (N : ℝ)) A k0 m ≤ ksbSbd M σ (x : ℝ) (1 / (N : ℝ)) A k0 :=
    ksb_S_le M σ hx0 hxr hA0 hA1 hhpos.le hk0 hmh
  have heS : Real.exp (kb3S M σ (x : ℝ) (1 / (N : ℝ)) A k0 m) ≤ 1 + 2 * ksbSbd M σ (x : ℝ) (1 / (N : ℝ)) A k0 := by
    have := ksb_exp_le hS0 (by linarith)
    linarith
  have he2S : Real.exp (2 * kb3S M σ (x : ℝ) (1 / (N : ℝ)) A k0 m) ≤ 1 + 4 * ksbSbd M σ (x : ℝ) (1 / (N : ℝ)) A k0 := by
    have := ksb_exp_le (s := 2 * kb3S M σ (x : ℝ) (1 / (N : ℝ)) A k0 m) (by linarith) (by linarith)
    linarith
  refine ⟨hI0, fun i hi => ?_, ?_⟩
  · obtain ⟨t1, t2⟩ := htr i hi
    have hIi : 0 ≤ kermI (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (kpP (Real.sqrt (1 - (x : ℝ) ^ 2)) (1 / (N : ℝ)))
        (hahn3jY M σ N x) (k0 + (i : ℤ)) := by
      have h1 := le_trans hI0 t2
      exact (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).1 h1
    exact ⟨t1.trans (mul_le_mul_of_nonneg_right heS hI0), t2.trans (mul_le_mul_of_nonneg_right he2S hIi)⟩
  · have hηB0 : 0 ≤ 3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2 := by
      have : 0 ≤ kl_beta (M : ℝ) (σ : ℝ) := by unfold kl_beta; positivity
      positivity
    have hκB0 : 0 ≤ |(M : ℝ) * (σ : ℝ)| / (k0 : ℝ) ^ 2 := by positivity
    have hscale := ksb_scale M σ hx0 hA0 hk0 (x := (x : ℝ)) (h := 1 / (N : ℝ))
    have hr := ksb_Rb_le hx0 hxr hA0 hA1 hhpos.le hmh1 hηB0 hκB0
    have hτ := ksb_Dub_le hx0 hxr hA0 hA1 hhpos.le hmh1 hηB0
    have hr0 : 0 ≤ kpRb (x : ℝ) (1 / (N : ℝ)) A (3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2) (|(M : ℝ) * (σ : ℝ)| / (k0 : ℝ) ^ 2) := by
      rw [ksb_Rb_eq hx0 hA0]
      have : 0 ≤ kl_beta (M : ℝ) (σ : ℝ) := by unfold kl_beta; positivity
      positivity
    have hτ0 : 0 ≤ kpDub (x : ℝ) (1 / (N : ℝ)) A (3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2) := by
      rw [ksb_Dub_eq hx0 hA0]
      have : 0 ≤ kl_beta (M : ℝ) (σ : ℝ) := by unfold kl_beta; positivity
      positivity
    have hsv : 0 ≤ ∑ i ∈ range (m + 1), kpP (Real.sqrt (1 - (x : ℝ) ^ 2)) (1 / (N : ℝ)) (k0 + (i : ℤ)) / 2 := by
      apply Finset.sum_nonneg
      intro i hi
      have := kpP_pos hA0 (hband (k0 + (i : ℤ)) (by omega) (by have := Finset.mem_range.1 hi; omega))
      exact div_nonneg this.le (by norm_num)
    have hr' : kpRb (x : ℝ) (1 / (N : ℝ)) A (3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2) (|(M : ℝ) * (σ : ℝ)| / (k0 : ℝ) ^ 2) ≤
        ksbSbd M σ (x : ℝ) (1 / (N : ℝ)) A k0 := hr.trans hscale
    have hτ' : kpDub (x : ℝ) (1 / (N : ℝ)) A (3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2) ≤
        ksbSbd M σ (x : ℝ) (1 / (N : ℝ)) A k0 := by
      refine hτ.trans (le_trans ?_ hscale)
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hmain := ksb_mass_err hA0 hA1 hS0 hSS hS hr0 hr' hτ0 hτ' hsv
    refine le_trans hmass (mul_le_mul_of_nonneg_left hmain hI0)

/-- info: 'FormalResearch.Special.ksb_S_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksb_S_le

/-- info: 'FormalResearch.Special.hahn3j_band_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn3j_band_clean

end FormalResearch.Special
