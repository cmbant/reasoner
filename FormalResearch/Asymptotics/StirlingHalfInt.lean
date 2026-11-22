module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Half-Integer Gamma and Stirling Bounds

Half-integer factorial/Gamma Stirling bound `(TE.7)` from `CFT/common/two_edge_bootstrap.tex`:
* `gamma_add_half_le`: `Real.Gamma (k + 1 / 2) ≤ √(2 * π) * k ^ k * Real.exp (-k)` for `k ≥ 1`.
* `teb_stirling_bound`: `2 ^ (k + 1) * Real.Gamma (k + 1 / 2) * (π / (4 * ℓ * a)) ^ (k + 1 / 2) ≤ 4 * Real.exp (-k)`.
-/

@[expose] public section

open scoped Real Nat

namespace FormalResearch.Asymptotics

section StirlingHalfInt

private lemma gamma_add_half_eq_factorial (k : ℕ) :
    Real.Gamma ((k : ℝ) + 1 / 2) = ((2 * k)! : ℝ) / ((4 : ℝ) ^ k * ((k)! : ℝ)) * √π := by
  induction k with
  | zero =>
    rw [Nat.cast_zero, zero_add, mul_zero, Nat.factorial_zero, pow_zero, Nat.cast_one, mul_one,
      div_one, Real.Gamma_one_half_eq, one_mul]
  | succ k ih =>
    have hne : (k : ℝ) + 1 / 2 ≠ 0 := by positivity
    have heq : ((k + 1 : ℕ) : ℝ) + 1 / 2 = ((k : ℝ) + 1 / 2) + 1 := by push_cast; ring
    rw [heq, Real.Gamma_add_one hne, ih]
    have hfac : ((2 * (k + 1))! : ℝ) = (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) * ((2 * k)! : ℝ) := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    have hfac_k : ((k + 1)! : ℝ) = ((k : ℝ) + 1) * ((k)! : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfac, hfac_k, pow_succ]
    have hk_ne : ((k)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    field_simp
    ring

/-- Stirling upper bound for half-integers: `Γ(k + 1/2) ≤ √(2π) k^k e^{-k}` for all `k ≥ 1`. -/
theorem gamma_add_half_le {k : ℕ} (hk : 1 ≤ k) :
    Real.Gamma ((k : ℝ) + 1 / 2) ≤ √(2 * π) * (k : ℝ) ^ k * Real.exp (-(k : ℝ)) := by
  rw [gamma_add_half_eq_factorial]
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hst_k : ((k)! : ℝ) =
      Stirling.stirlingSeq k * (√(2 * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k) := by
    have hden : √(2 * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k ≠ 0 := by positivity
    rw [Stirling.stirlingSeq, div_mul_cancel₀ _ hden]
  have hst_2k : ((2 * k)! : ℝ) =
      Stirling.stirlingSeq (2 * k) * (√(2 * ((2 * k : ℕ) : ℝ)) * (((2 * k : ℕ) : ℝ) / Real.exp 1) ^ (2 * k)) := by
    have hden : √(2 * ((2 * k : ℕ) : ℝ)) * (((2 * k : ℕ) : ℝ) / Real.exp 1) ^ (2 * k) ≠ 0 := by
      positivity
    rw [Stirling.stirlingSeq, div_mul_cancel₀ _ hden]
  have hst_mono : Stirling.stirlingSeq (2 * k) ≤ Stirling.stirlingSeq k := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hm : m ≤ 2 * m + 1 := by omega
    have := Stirling.stirlingSeq'_antitone hm
    simpa [Function.comp_apply, show 2 * (m + 1) = (2 * m + 1) + 1 by ring] using this
  have hst_k_pos : 0 < Stirling.stirlingSeq k := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact Stirling.stirlingSeq'_pos m
  have h_ratio_eq : ((2 * k)! : ℝ) / ((4 : ℝ) ^ k * ((k)! : ℝ)) * √π =
      (Stirling.stirlingSeq (2 * k) / Stirling.stirlingSeq k) *
        (√(2 * π) * (k : ℝ) ^ k * Real.exp (-(k : ℝ))) := by
    rw [hst_2k, hst_k]
    have hsqrt_rel : √(2 * ((2 * k : ℕ) : ℝ)) / √(2 * (k : ℝ)) = √2 := by
      have : (2 * ((2 * k : ℕ) : ℝ)) = 2 * (2 * (k : ℝ)) := by push_cast; ring
      rw [this, Real.sqrt_mul zero_le_two, mul_div_cancel_right₀ _ (Real.sqrt_ne_zero'.mpr (by positivity))]
    have hexp_k : (Real.exp 1) ^ k = Real.exp (k : ℝ) := by
      rw [← Real.exp_nat_mul, mul_one]
    have hexp_2k : (Real.exp 1) ^ (2 * k) = Real.exp (2 * (k : ℝ)) := by
      rw [← Real.exp_nat_mul, mul_one]; push_cast; rfl
    have hexp_neg : Real.exp (-(k : ℝ)) = (Real.exp (k : ℝ))⁻¹ := Real.exp_neg _
    have hexp_2k_sq : Real.exp (2 * (k : ℝ)) = Real.exp (k : ℝ) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1
    have hk_pow : (k : ℝ) ^ (2 * k) = (k : ℝ) ^ k * (k : ℝ) ^ k := by
      rw [two_mul, pow_add]
    have h4_eq : (4 : ℝ) ^ k = (2 : ℝ) ^ (2 * k) := by
      rw [pow_mul]; norm_num
    have hsqrt_2pi : √(2 * π) = √2 * √π := Real.sqrt_mul zero_le_two π
    push_cast
    rw [div_pow, div_pow, mul_pow, hexp_k, hexp_2k, hexp_2k_sq, hk_pow, h4_eq, hexp_neg, hsqrt_2pi]
    have hsqrt_2k_eq : √(2 * (2 * (k : ℝ))) = √2 * √(2 * (k : ℝ)) :=
      Real.sqrt_mul zero_le_two (2 * (k : ℝ))
    rw [hsqrt_2k_eq]
    have hnz1 : √(2 * (k : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have hnz2 : Real.exp (k : ℝ) ≠ 0 := (Real.exp_pos _).ne'
    have hnz3 : (k : ℝ) ^ k ≠ 0 := pow_ne_zero _ hk_pos.ne'
    have hnz4 : (2 : ℝ) ^ (2 * k) ≠ 0 := by positivity
    have hnz5 : Stirling.stirlingSeq k ≠ 0 := hst_k_pos.ne'
    field_simp
  rw [h_ratio_eq]
  calc (Stirling.stirlingSeq (2 * k) / Stirling.stirlingSeq k) *
        (√(2 * π) * (k : ℝ) ^ k * Real.exp (-(k : ℝ)))
      ≤ 1 * (√(2 * π) * (k : ℝ) ^ k * Real.exp (-(k : ℝ))) := by
        gcongr
        exact (div_le_one hst_k_pos).mpr hst_mono
    _ = √(2 * π) * (k : ℝ) ^ k * Real.exp (-(k : ℝ)) := one_mul _

/-- Combined Stirling-arc bound `(TE.7)`:
`2 ^ (k + 1) * Γ(k + 1/2) * (π / (4 * ℓ * a)) ^ (k + 1/2) ≤ 4 * exp(-k)` for `k ≥ 1`, `ℓ * a ≥ (π / 2) * k`. -/
theorem teb_stirling_bound {k : ℕ} {ℓ a : ℝ} (hk : 1 ≤ k) (hℓ : 0 < ℓ) (ha : 0 < a)
    (hla : (π / 2) * (k : ℝ) ≤ ℓ * a) :
    (2 : ℝ) ^ (k + 1) * Real.Gamma ((k : ℝ) + 1 / 2) * (π / (4 * ℓ * a)) ^ ((k : ℝ) + 1 / 2) ≤
      4 * Real.exp (-(k : ℝ)) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have h_arg_le : π / (4 * ℓ * a) ≤ 1 / (2 * (k : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hpow_le : (π / (4 * ℓ * a)) ^ ((k : ℝ) + 1 / 2) ≤ (1 / (2 * (k : ℝ))) ^ ((k : ℝ) + 1 / 2) :=
    Real.rpow_le_rpow (by positivity) h_arg_le (by positivity)
  have hgam := gamma_add_half_le hk
  have hgam_nn : 0 ≤ Real.Gamma ((k : ℝ) + 1 / 2) := (Real.Gamma_pos_of_pos (by positivity)).le
  have h_id : (2 : ℝ) ^ (k + 1) * (√(2 * π) * (k : ℝ) ^ k * Real.exp (-(k : ℝ))) *
      (1 / (2 * (k : ℝ))) ^ ((k : ℝ) + 1 / 2) =
      2 * √π / √(k : ℝ) * Real.exp (-(k : ℝ)) := by
    rw [Real.rpow_add (by positivity : 0 < 1 / (2 * (k : ℝ))), Real.rpow_natCast,
      one_div_pow, mul_pow, one_div (2 * (k : ℝ)), Real.inv_rpow (by positivity),
      ← Real.sqrt_eq_rpow]
    simp_rw [Real.sqrt_mul zero_le_two]
    have hk_pow_ne : (k : ℝ) ^ k ≠ 0 := pow_ne_zero _ hk_pos.ne'
    have hk_sqrt_ne : √(k : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hk_pos).ne'
    have h2_pow_ne : (2 : ℝ) ^ k ≠ 0 := by positivity
    have h2_sqrt_sq : √2 * √2 = 2 := Real.mul_self_sqrt zero_le_two
    rw [pow_succ]
    field_simp
  have hsqrt_k_ge : 1 ≤ √(k : ℝ) := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hk)
  have h2sqrt_pi_le : 2 * √π ≤ 4 := by
    have : √π ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      nlinarith [Real.pi_lt_four]
    linarith
  calc (2 : ℝ) ^ (k + 1) * Real.Gamma ((k : ℝ) + 1 / 2) * (π / (4 * ℓ * a)) ^ ((k : ℝ) + 1 / 2)
      ≤ (2 : ℝ) ^ (k + 1) * (√(2 * π) * (k : ℝ) ^ k * Real.exp (-(k : ℝ))) *
          (1 / (2 * (k : ℝ))) ^ ((k : ℝ) + 1 / 2) := by
        gcongr
    _ = 2 * √π / √(k : ℝ) * Real.exp (-(k : ℝ)) := h_id
    _ ≤ 4 / 1 * Real.exp (-(k : ℝ)) := by gcongr
    _ = 4 * Real.exp (-(k : ℝ)) := by ring

end StirlingHalfInt

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.Asymptotics.gamma_add_half_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.gamma_add_half_le

/-- info: 'FormalResearch.Asymptotics.teb_stirling_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.teb_stirling_bound


end FormalResearch.Asymptotics
