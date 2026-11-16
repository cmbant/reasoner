module

public import FormalResearch.Complex.HadamardGeneral

/-!
# Growth of canonical products and of the Hadamard factorization (converse direction)

Hadamard's theorem (`Hadamard.hadamard`) turns a growth bound `‖f‖ ≤ C exp(C‖z‖^σ)` into the factorization
`f = c z^m e^P ∏ E_p(z/a_i)`.  This module proves the *converse* growth estimate (Boas, *Entire functions*, Thm 2.6.5 and
2.7.x; Titchmarsh 8.2; Conway XI.3): a canonical product whose zeros have a finite convergence exponent `s` has order `≤ s`.

* `Hadamard.norm_E_le_exp`: for `p ≤ s ≤ p + 1`, `s > 0`, there is `K` with `‖E_p(w)‖ ≤ exp(K ‖w‖^s)` for all `w ∈ ℂ`;
* `Hadamard.CanonData.of_summable_rpow`: `a_i ≠ 0`, `Σ ‖a_i‖^{-s} < ∞`, `s ≤ p + 1` give the hypothesis of the canonical
  product;
* **`Hadamard.norm_canonProd_le`**: `‖∏ E_p(z/a_i)‖ ≤ exp(K S ‖z‖^s)`, `S = Σ ‖a_i‖^{-s}`;
* **`Hadamard.growthBound_canonProd`**: `GrowthBound (canonProd p a) s`;
* **`Hadamard.growthBound_factorization`**: for `P` of degree `≤ p ≤ s ≤ p + 1`, `m : ℕ`, `c : ℂ`, the function
  `z ↦ c z^m e^{P(z)} ∏ E_p(z/a_i)` has `GrowthBound … s` (finite order `≤ s`).  Together with `Hadamard.hadamard` this gives the
  order/genus dictionary: for `p ≤ s ≤ p + 1` an entire function with `Σ ‖a_i‖^{-s} < ∞` and polynomial exponent of degree
  `≤ p` has growth `≤ s`, and conversely growth `σ < p + 1` forces the representation.

Proved here: all of the above.  **Not formalised:** lower bounds on canonical products (order *equal* to the convergence
exponent needs those, or Jensen on a product with infinitely many zeros), the limsup definition of order, and the
`s < p` (excess-genus) case of the estimate, which is false in general.
-/

@[expose] public section

open Complex Filter Topology Finset
open scoped BigOperators

namespace FormalResearch.Hadamard

/-- `1 + x ≤ exp (K x^s)` for `x ≥ 1`, with `K = log 2 + 1/s`. -/
lemma one_add_le_exp_rpow {x s : ℝ} (hx : 1 ≤ x) (hs : 0 < s) :
    1 + x ≤ Real.exp ((Real.log 2 + 1 / s) * x ^ s) := by
  have hx0 : 0 < x := by linarith
  have h1 : 1 + x ≤ 2 * x := by linarith
  have hxs : 1 ≤ x ^ s := Real.one_le_rpow hx hs.le
  have hl : Real.log x ≤ x ^ s / s := Real.log_le_rpow_div hx0.le hs
  have h2 : Real.log (2 * x) ≤ (Real.log 2 + 1 / s) * x ^ s := by
    rw [Real.log_mul (by norm_num) hx0.ne']
    have : Real.log 2 ≤ Real.log 2 * x ^ s := by
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      nlinarith
    calc Real.log 2 + Real.log x ≤ Real.log 2 * x ^ s + x ^ s / s := add_le_add this hl
      _ = _ := by ring
  calc 1 + x ≤ 2 * x := h1
    _ = Real.exp (Real.log (2 * x)) := (Real.exp_log (by positivity)).symm
    _ ≤ _ := Real.exp_le_exp.mpr h2

/-- **Elementary factors have order at most `s`** for `p ≤ s ≤ p + 1`, `s > 0`:
`‖E_p(w)‖ ≤ exp(K ‖w‖^s)` for all `w ∈ ℂ`, with `K = e^p + log 2 + 1/s + p`. -/
theorem norm_E_le_exp (p : ℕ) {s : ℝ} (hs : 0 < s) (hps : (p : ℝ) ≤ s) (hsp : s ≤ p + 1) (w : ℂ) :
    ‖E p w‖ ≤ Real.exp ((Real.exp p + Real.log 2 + 1 / s + p) * ‖w‖ ^ s) := by
  have hK0 : 0 ≤ Real.log 2 + 1 / s := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity
  rcases le_or_gt ‖w‖ 1 with hw | hw
  · have hE := E_sub_one_le p hw
    have h1 : ‖E p w‖ ≤ 1 + Real.exp p * ‖w‖ ^ (p + 1) := by
      have := norm_le_norm_add_norm_sub' (E p w) 1
      have h := norm_add_le (1 : ℂ) (E p w - 1)
      calc ‖E p w‖ = ‖1 + (E p w - 1)‖ := by ring_nf
        _ ≤ ‖(1 : ℂ)‖ + ‖E p w - 1‖ := h
        _ ≤ _ := by rw [norm_one]; linarith
    have h2 : ‖w‖ ^ (p + 1) ≤ ‖w‖ ^ s := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hw hs.le (by push_cast; exact hsp)
    have h3 : 1 + Real.exp p * ‖w‖ ^ (p + 1) ≤ Real.exp (Real.exp p * ‖w‖ ^ s) := by
      have := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (p : ℝ)).le
      linarith [Real.add_one_le_exp (Real.exp p * ‖w‖ ^ s)]
    refine h1.trans (h3.trans (Real.exp_le_exp.mpr ?_))
    have hx : 0 ≤ ‖w‖ ^ s := Real.rpow_nonneg (norm_nonneg _) _
    have : (0 : ℝ) ≤ Real.log 2 + 1 / s + p := by positivity
    nlinarith
  · have hS : ‖S p w‖ ≤ p * ‖w‖ ^ p := by
      unfold S
      calc ‖∑ k ∈ range p, w ^ (k + 1) / ((k : ℂ) + 1)‖
          ≤ ∑ k ∈ range p, ‖w ^ (k + 1) / ((k : ℂ) + 1)‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ range p, ‖w‖ ^ p := by
            refine sum_le_sum fun k hk => ?_
            have hk' : k + 1 ≤ p := Finset.mem_range.mp hk
            rw [norm_div, norm_pow]
            have h1 : (1 : ℝ) ≤ ‖((k : ℂ) + 1)‖ := by
              have : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
              rw [this, Complex.norm_natCast]; exact_mod_cast Nat.succ_pos k
            calc ‖w‖ ^ (k + 1) / ‖((k : ℂ) + 1)‖ ≤ ‖w‖ ^ (k + 1) / 1 :=
                  div_le_div_of_nonneg_left (by positivity) one_pos h1
              _ ≤ ‖w‖ ^ p := by rw [div_one]; exact pow_le_pow_right₀ hw.le hk'
        _ = p * ‖w‖ ^ p := by simp
    have hp : ‖w‖ ^ p ≤ ‖w‖ ^ s := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hw.le hps
    have hE : ‖E p w‖ ≤ (1 + ‖w‖) * Real.exp (p * ‖w‖ ^ p) := by
      unfold E
      rw [norm_mul, Complex.norm_exp]
      refine mul_le_mul ?_ ?_ (Real.exp_pos _).le (by positivity)
      · calc ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
          _ = 1 + ‖w‖ := by rw [norm_one]
      · exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hS)
    refine hE.trans ?_
    have h1 := one_add_le_exp_rpow hw.le hs
    calc (1 + ‖w‖) * Real.exp (p * ‖w‖ ^ p)
        ≤ Real.exp ((Real.log 2 + 1 / s) * ‖w‖ ^ s) * Real.exp (p * ‖w‖ ^ s) := by
          gcongr
      _ = Real.exp (((Real.log 2 + 1 / s) + p) * ‖w‖ ^ s) := by rw [← Real.exp_add]; ring_nf
      _ ≤ _ := by
          refine Real.exp_le_exp.mpr ?_
          have hx : 0 ≤ ‖w‖ ^ s := Real.rpow_nonneg (norm_nonneg _) _
          nlinarith [Real.exp_pos (p : ℝ)]

variable {ι : Type*}

/-- `Σ ‖a_i‖^{-s} < ∞` with `s ≤ p + 1` and no zero entry give the canonical-product hypothesis. -/
theorem CanonData.of_summable_rpow {p : ℕ} {s : ℝ} {a : ι → ℂ} (ha : ∀ i, a i ≠ 0) (hs0 : 0 < s)
    (hsp : s ≤ p + 1) (hs : Summable fun i => (‖a i‖ ^ s)⁻¹) : CanonData p a := by
  refine ⟨ha, ?_⟩
  refine Summable.of_norm_bounded_eventually hs ?_
  filter_upwards [hs.tendsto_cofinite_zero.eventually (gt_mem_nhds one_pos)] with i hi
  have hai : 0 < ‖a i‖ := norm_pos_iff.mpr (ha i)
  have h1 : 1 ≤ ‖a i‖ := by
    by_contra hlt
    push Not at hlt
    have : ‖a i‖ ^ s < 1 := Real.rpow_lt_one hai.le hlt hs0
    have := one_lt_inv_iff₀.mpr ⟨Real.rpow_pos_of_pos hai s, this⟩
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine inv_anti₀ (Real.rpow_pos_of_pos hai s) ?_
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le h1 (by push_cast; exact hsp)

/-- **Growth of a canonical product**: for `p ≤ s ≤ p + 1`, `s > 0`, `Σ ‖a_i‖^{-s} < ∞`,
`‖∏ E_p(z/a_i)‖ ≤ exp(K (Σ ‖a_i‖^{-s}) ‖z‖^s)`, `K = e^p + log 2 + 1/s + p`. -/
theorem norm_canonProd_le {p : ℕ} {s : ℝ} {a : ι → ℂ} (hD : CanonData p a) (hs0 : 0 < s)
    (hps : (p : ℝ) ≤ s) (hsp : s ≤ p + 1) (hs : Summable fun i => (‖a i‖ ^ s)⁻¹) (z : ℂ) :
    ‖canonProd p a z‖ ≤ Real.exp ((Real.exp p + Real.log 2 + 1 / s + p) * (∑' i, (‖a i‖ ^ s)⁻¹) * ‖z‖ ^ s) := by
  set K := Real.exp p + Real.log 2 + 1 / s + p with hK
  have hK0 : 0 ≤ K := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity
  have hpart : ∀ F : Finset ι, ‖∏ i ∈ F, E p (z / a i)‖ ≤
      Real.exp (K * (∑' i, (‖a i‖ ^ s)⁻¹) * ‖z‖ ^ s) := by
    intro F
    rw [norm_prod]
    calc ∏ i ∈ F, ‖E p (z / a i)‖ ≤ ∏ i ∈ F, Real.exp (K * ((‖a i‖ ^ s)⁻¹ * ‖z‖ ^ s)) := by
          gcongr with i hi
          refine (norm_E_le_exp p hs0 hps hsp _).trans (Real.exp_le_exp.mpr (le_of_eq ?_))
          rw [norm_div, Real.div_rpow (norm_nonneg _) (norm_nonneg _), hK]
          ring
      _ = Real.exp (K * (∑ i ∈ F, (‖a i‖ ^ s)⁻¹) * ‖z‖ ^ s) := by
          rw [← Real.exp_sum]; congr 1; rw [← mul_sum, ← sum_mul]; ring
      _ ≤ _ := by
          refine Real.exp_le_exp.mpr ?_
          have hx : 0 ≤ ‖z‖ ^ s := Real.rpow_nonneg (norm_nonneg _) _
          have := hs.sum_le_tsum F (fun i _ => by positivity)
          have h2 := mul_le_mul_of_nonneg_left this hK0
          exact mul_le_mul_of_nonneg_right h2 hx
  have ht := (canonProd_hasProd_at hD z)
  have hlim : Tendsto (fun F : Finset ι => ‖∏ i ∈ F, E p (z / a i)‖) atTop (𝓝 ‖canonProd p a z‖) :=
    (continuous_norm.tendsto _).comp ht
  exact le_of_tendsto hlim (Eventually.of_forall hpart)

/-- `canonProd p a` has growth of order at most `s` in the sense `GrowthBound`. -/
theorem growthBound_canonProd {p : ℕ} {s : ℝ} {a : ι → ℂ} (hD : CanonData p a) (hs0 : 0 < s)
    (hps : (p : ℝ) ≤ s) (hsp : s ≤ p + 1) (hs : Summable fun i => (‖a i‖ ^ s)⁻¹) :
    GrowthBound (canonProd p a) s := by
  set K := (Real.exp p + Real.log 2 + 1 / s + p) * (∑' i, (‖a i‖ ^ s)⁻¹) with hK
  refine ⟨max K 1, fun z => ?_⟩
  have hK0 : 0 ≤ K := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have h2 : 0 ≤ ∑' i, (‖a i‖ ^ s)⁻¹ := tsum_nonneg fun i => by positivity
    positivity
  refine (norm_canonProd_le hD hs0 hps hsp hs z).trans ?_
  have hx : 0 ≤ ‖z‖ ^ s := Real.rpow_nonneg (norm_nonneg _) _
  calc Real.exp (K * ‖z‖ ^ s) ≤ Real.exp (max K 1 * ‖z‖ ^ s) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hx)
    _ = 1 * Real.exp (max K 1 * ‖z‖ ^ s) := by ring
    _ ≤ _ := by
        gcongr
        exact le_max_right _ _

lemma pow_le_exp_rpow {x s : ℝ} (hx : 0 ≤ x) (hs : 0 < s) (m : ℕ) :
    x ^ m ≤ Real.exp (m / s * x ^ s) := by
  have hxs : 0 ≤ x ^ s := Real.rpow_nonneg hx _
  rcases le_or_gt x 1 with h | h
  · calc x ^ m ≤ 1 := pow_le_one₀ hx h
      _ ≤ _ := Real.one_le_exp (by positivity)
  · have hx0 : 0 < x := by linarith
    have hl : Real.log x ≤ x ^ s / s := Real.log_le_rpow_div hx0.le hs
    calc x ^ m = Real.exp (m * Real.log x) := by
          rw [← Real.log_pow, Real.exp_log (pow_pos hx0 m)]
      _ ≤ _ := Real.exp_le_exp.mpr (by
          have := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
          calc (m : ℝ) * Real.log x ≤ m * (x ^ s / s) := this
            _ = _ := by ring)

/-- `‖P(z)‖ ≤ B (1 + ‖z‖^s)` for a polynomial of degree `≤ p ≤ s`, `B = Σ ‖coeff_k‖`. -/
lemma norm_eval_le_rpow {p : ℕ} {s : ℝ} (hps : (p : ℝ) ≤ s) (P : Polynomial ℂ) (hP : P.natDegree ≤ p) (z : ℂ) :
    ‖P.eval z‖ ≤ (∑ k ∈ range (p + 1), ‖P.coeff k‖) * (1 + ‖z‖ ^ s) := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP)]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine sum_le_sum fun k hk => ?_
  have hk' : k ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rcases le_or_gt ‖z‖ 1 with h | h
  · have := pow_le_one₀ (norm_nonneg z) h (n := k)
    have : 0 ≤ ‖z‖ ^ s := Real.rpow_nonneg (norm_nonneg _) _
    linarith
  · have h1 : ‖z‖ ^ k ≤ ‖z‖ ^ p := pow_le_pow_right₀ h.le hk'
    have h2 : ‖z‖ ^ p ≤ ‖z‖ ^ s := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le h.le hps
    linarith

/-- **The Hadamard factorization has finite order** (converse of `Hadamard.hadamard`): for `p ≤ s ≤ p + 1`, `s > 0`,
`Σ ‖a_i‖^{-s} < ∞`, a polynomial `P` of degree `≤ p`, `c ∈ ℂ`, `m : ℕ`, the entire function
`z ↦ c z^m e^{P(z)} ∏ E_p(z/a_i)` satisfies `GrowthBound … s`. -/
theorem growthBound_factorization {p : ℕ} {s : ℝ} {a : ι → ℂ} (hD : CanonData p a) (hs0 : 0 < s)
    (hps : (p : ℝ) ≤ s) (hsp : s ≤ p + 1) (hs : Summable fun i => (‖a i‖ ^ s)⁻¹) (c : ℂ) (m : ℕ)
    (P : Polynomial ℂ) (hP : P.natDegree ≤ p) :
    GrowthBound (fun z => c * z ^ m * cexp (P.eval z) * canonProd p a z) s := by
  set B := ∑ k ∈ range (p + 1), ‖P.coeff k‖ with hB
  have hB0 : 0 ≤ B := sum_nonneg fun k _ => norm_nonneg _
  set K := (Real.exp p + Real.log 2 + 1 / s + p) * (∑' i, (‖a i‖ ^ s)⁻¹) with hK
  have hK0 : 0 ≤ K := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have h2 : 0 ≤ ∑' i, (‖a i‖ ^ s)⁻¹ := tsum_nonneg fun i => by positivity
    positivity
  refine ⟨max (‖c‖ * Real.exp B) (m / s + B + K), fun z => ?_⟩
  have hx : 0 ≤ ‖z‖ ^ s := Real.rpow_nonneg (norm_nonneg _) _
  have h1 := pow_le_exp_rpow (norm_nonneg z) hs0 m
  have h2 : ‖cexp (P.eval z)‖ ≤ Real.exp (B * (1 + ‖z‖ ^ s)) := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (norm_eval_le_rpow hps P hP z))
  have h3 := norm_canonProd_le hD hs0 hps hsp hs z
  rw [← hK] at h3
  have hf : ‖c * z ^ m * cexp (P.eval z) * canonProd p a z‖ ≤
      ‖c‖ * Real.exp B * Real.exp ((m / s + B + K) * ‖z‖ ^ s) := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow]
    have e : ‖c‖ * Real.exp B * Real.exp ((m / s + B + K) * ‖z‖ ^ s) =
        ‖c‖ * Real.exp (m / s * ‖z‖ ^ s) * Real.exp (B * (1 + ‖z‖ ^ s)) * Real.exp (K * ‖z‖ ^ s) := by
      have e2 : (m / s + B + K) * ‖z‖ ^ s = m / s * ‖z‖ ^ s + B * ‖z‖ ^ s + K * ‖z‖ ^ s := by ring
      rw [e2, Real.exp_add, Real.exp_add, mul_one_add B, Real.exp_add]
      ring
    rw [e]
    gcongr
  refine hf.trans ?_
  have hM1 : ‖c‖ * Real.exp B ≤ max (‖c‖ * Real.exp B) (m / s + B + K) := le_max_left _ _
  have hM2 : m / s + B + K ≤ max (‖c‖ * Real.exp B) (m / s + B + K) := le_max_right _ _
  gcongr

end FormalResearch.Hadamard

/-- info: 'FormalResearch.Hadamard.norm_E_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.norm_E_le_exp

/-- info: 'FormalResearch.Hadamard.CanonData.of_summable_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.CanonData.of_summable_rpow

/-- info: 'FormalResearch.Hadamard.norm_canonProd_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.norm_canonProd_le

/-- info: 'FormalResearch.Hadamard.growthBound_canonProd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.growthBound_canonProd

/-- info: 'FormalResearch.Hadamard.growthBound_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.growthBound_factorization

