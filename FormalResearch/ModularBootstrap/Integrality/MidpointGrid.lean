module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# The midpoint-cosine grid and Fejér quadrature (tools for `int:cheb`)

`CFT/modular_bootstrap/paper/integrality.tex`, proof of Lemma INT-M (`int:cheb`), first paragraph:
for `n ≥ M + 1` the midpoint angles `θ_j = (j + 1/2) π / n` (`j = 0, …, n - 1`) satisfy the discrete
orthogonality relations (`int:mid-orth`), and the Fejér-I quadrature weights

`λ_j = (2/n) (1 - 2 ∑_{k=1}^K cos(2kθ_j)/(4k²-1))`, `K = ⌊M/2⌋`,

integrate the Chebyshev polynomials `T_m` (`m ≤ M`) exactly and obey `λ_j ≥ 2/n²`
(`int:lam-lb`).  Everything here is **proved**.
-/

@[expose] public section

open Real Finset

namespace FormalResearch.ModularBootstrap.Integrality

/-- The midpoint angle `θ_j = (j + 1/2) π / n`. -/
noncomputable def midAngle (n j : ℕ) : ℝ := ((j : ℝ) + 1 / 2) * π / n

lemma midAngle_mul (n j r : ℕ) (hn : 0 < n) :
    (r : ℝ) * midAngle n j = ((2 * j + 1 : ℕ) : ℝ) * ((r : ℝ) * π / (2 * n)) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  unfold midAngle
  push_cast
  field_simp

/-- `∑_j cos(r θ_j) = 0` for `0 < r < 2n`. -/
lemma sum_cos_midAngle {n r : ℕ} (hn : 0 < n) (hr : 0 < r) (hr2 : r < 2 * n) :
    ∑ j ∈ range n, cos ((r : ℝ) * midAngle n j) = 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set s := (r : ℝ) * π / (2 * n) with hs
  have hspos : 0 < sin s := by
    apply sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [hs, div_lt_iff₀ (by positivity)]
      have : (r : ℝ) < 2 * n := by exact_mod_cast hr2
      nlinarith [pi_pos]
  have key : ∀ j : ℕ, 2 * sin s * cos ((r : ℝ) * midAngle n j) =
      sin (((j + 1 : ℕ) : ℝ) * (2 * s)) - sin ((j : ℝ) * (2 * s)) := by
    intro j
    have hθ : (r : ℝ) * midAngle n j = (2 * (j : ℝ) + 1) * s := by
      rw [midAngle_mul n j r hn, hs]; push_cast; ring
    rw [two_mul_sin_mul_cos, hθ]
    have h1 : s - (2 * (j : ℝ) + 1) * s = -((j : ℝ) * (2 * s)) := by ring
    have h2 : s + (2 * (j : ℝ) + 1) * s = ((j + 1 : ℕ) : ℝ) * (2 * s) := by push_cast; ring
    rw [h1, h2, sin_neg]; ring
  have hsum : 2 * sin s * ∑ j ∈ range n, cos ((r : ℝ) * midAngle n j) = 0 := by
    rw [mul_sum]
    simp_rw [key]
    rw [sum_range_sub (fun j : ℕ => sin ((j : ℝ) * (2 * s)))]
    have : (n : ℝ) * (2 * s) = r * π := by
      rw [hs]; field_simp
    rw [this, sin_nat_mul_pi]; simp
  have : 2 * sin s ≠ 0 := by positivity
  exact (mul_eq_zero.1 hsum).resolve_left this

/-- Integer-frequency form: `∑_j cos(r θ_j) = n [r = 0]` for `|r| < 2n`. -/
lemma sum_cos_midAngle_int {n : ℕ} (hn : 0 < n) {r : ℤ} (hr : r.natAbs < 2 * n) :
    ∑ j ∈ range n, cos ((r : ℝ) * midAngle n j) = if r = 0 then (n : ℝ) else 0 := by
  by_cases h0 : r = 0
  · subst h0; simp
  · simp only [h0, ↓reduceIte]
    obtain ⟨k, hk⟩ : ∃ k : ℕ, r = k ∨ r = -k := ⟨r.natAbs, Int.natAbs_eq r⟩
    have hk0 : 0 < k := by
      rcases hk with rfl | rfl <;> omega
    have hkn : k < 2 * n := by
      rcases hk with rfl | rfl <;> simpa using hr
    rcases hk with rfl | rfl
    · simpa using sum_cos_midAngle hn hk0 hkn
    · simp_rw [Int.cast_neg, Int.cast_natCast, neg_mul, cos_neg]
      exact sum_cos_midAngle hn hk0 hkn

/-- Orthogonality of the midpoint cosines (`int:mid-orth`). -/
lemma sum_cos_mul_cos {n a b : ℕ} (hn : 0 < n) (ha : a < n) (hb : b < n) :
    ∑ j ∈ range n, cos ((a : ℝ) * midAngle n j) * cos ((b : ℝ) * midAngle n j) =
      if a = b then (if a = 0 then (n : ℝ) else n / 2) else 0 := by
  have key : ∀ j : ℕ, cos ((a : ℝ) * midAngle n j) * cos ((b : ℝ) * midAngle n j) =
      (cos ((((a : ℤ) - b : ℤ) : ℝ) * midAngle n j) +
        cos ((((a : ℤ) + b : ℤ) : ℝ) * midAngle n j)) / 2 := by
    intro j
    have := two_mul_cos_mul_cos ((a : ℝ) * midAngle n j) ((b : ℝ) * midAngle n j)
    push_cast
    rw [← sub_mul, ← add_mul] at this
    linarith
  simp_rw [key]
  rw [← sum_div, sum_add_distrib, sum_cos_midAngle_int hn (by omega), sum_cos_midAngle_int hn (by omega)]
  by_cases hab : a = b
  · subst hab
    by_cases ha0 : a = 0
    · subst ha0; simp
    · simp [ha0]
  · have h1 : ((a : ℤ) - b) ≠ 0 := by omega
    have h2 : ((a : ℤ) + b) ≠ 0 ∨ (a = 0 ∧ b = 0) := by omega
    rcases h2 with h2 | ⟨rfl, rfl⟩
    · simp [h1, h2, hab]
    · exact absurd rfl hab

/-- Orthogonality of the midpoint sines (`int:mid-orth`). -/
lemma sum_sin_mul_sin {n a b : ℕ} (hn : 0 < n) (ha : a < n) (hb : b < n) (ha1 : 1 ≤ a)
    (hb1 : 1 ≤ b) :
    ∑ j ∈ range n, sin ((a : ℝ) * midAngle n j) * sin ((b : ℝ) * midAngle n j) =
      if a = b then (n : ℝ) / 2 else 0 := by
  have key : ∀ j : ℕ, sin ((a : ℝ) * midAngle n j) * sin ((b : ℝ) * midAngle n j) =
      (cos ((((a : ℤ) - b : ℤ) : ℝ) * midAngle n j) -
        cos ((((a : ℤ) + b : ℤ) : ℝ) * midAngle n j)) / 2 := by
    intro j
    have := two_mul_sin_mul_sin ((a : ℝ) * midAngle n j) ((b : ℝ) * midAngle n j)
    push_cast
    rw [← sub_mul, ← add_mul] at this
    linarith
  simp_rw [key]
  rw [← sum_div, sum_sub_distrib, sum_cos_midAngle_int hn (by omega),
    sum_cos_midAngle_int hn (by omega)]
  have h2 : ((a : ℤ) + b) ≠ 0 := by omega
  by_cases hab : a = b
  · subst hab; simp [h2]
  · have h1 : ((a : ℤ) - b) ≠ 0 := by omega
    simp [h1, h2, hab]

/-- The Fejér-I quadrature weight `λ_j = (2/n)(1 - 2 ∑_{k=1}^K cos(2kθ_j)/(4k² - 1))`. -/
noncomputable def fejerWeight (n K j : ℕ) : ℝ :=
  (2 / n) * (1 - 2 * ∑ k ∈ range K, cos (2 * ((k : ℝ) + 1) * midAngle n j) /
    (4 * ((k : ℝ) + 1) ^ 2 - 1))

/-- `2 ∑_{k=1}^K 1/(4k²-1) = 1 - 1/(2K+1)`. -/
lemma two_mul_sum_inv (K : ℕ) :
    2 * ∑ k ∈ range K, 1 / (4 * ((k : ℝ) + 1) ^ 2 - 1) = 1 - 1 / (2 * (K : ℝ) + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    have h1 : (2 * (K : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (2 * ((K : ℝ) + 1) + 1) ≠ 0 := by positivity
    have h3 : (4 * ((K : ℝ) + 1) ^ 2 - 1) = (2 * (K : ℝ) + 1) * (2 * ((K : ℝ) + 1) + 1) := by ring
    rw [h3]
    field_simp
    ring

/-- The Fejér weights satisfy `λ_j ≥ 2/(n(2K+1))` (`int:lam-lb`). -/
lemma fejerWeight_ge {n : ℕ} (hn : 0 < n) (K j : ℕ) :
    2 / ((n : ℝ) * (2 * K + 1)) ≤ fejerWeight n K j := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold fejerWeight
  have h1 : ∑ k ∈ range K, cos (2 * ((k : ℝ) + 1) * midAngle n j) / (4 * ((k : ℝ) + 1) ^ 2 - 1) ≤
      ∑ k ∈ range K, 1 / (4 * ((k : ℝ) + 1) ^ 2 - 1) := by
    refine sum_le_sum fun k _ => ?_
    have hpos : (0 : ℝ) < 4 * ((k : ℝ) + 1) ^ 2 - 1 := by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    exact div_le_div_of_nonneg_right (cos_le_one _) hpos.le
  have h2 := two_mul_sum_inv K
  have h3 : 2 / ((n : ℝ) * (2 * K + 1)) = (2 / n) * (1 / (2 * (K : ℝ) + 1)) := by
    field_simp
  rw [h3]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  linarith

lemma fejerWeight_ge_sq {n : ℕ} (hn : 0 < n) {M : ℕ} (hM : M + 1 ≤ n) (j : ℕ) :
    2 / (n : ℝ) ^ 2 ≤ fejerWeight n (M / 2) j := by
  refine le_trans ?_ (fejerWeight_ge hn (M / 2) j)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (2 * ((M / 2 : ℕ) : ℝ) + 1) ≤ n := by
    have : 2 * (M / 2) + 1 ≤ n := by omega
    exact_mod_cast this
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [h1]

/-- `∫_{-1}^1 T_m` : `2/(1 - m²)` for even `m`, `0` for odd `m`. -/
noncomputable def chebInt (m : ℕ) : ℝ := if m % 2 = 0 then 2 / (1 - (m : ℝ) ^ 2) else 0

/-- **Fejér-I quadrature is exact on `T_m`, `m ≤ M`** (`n ≥ M + 1`). -/
lemma fejerWeight_cos_sum {n M : ℕ} (hn : 0 < n) (hM : M + 1 ≤ n) {m : ℕ} (hm : m ≤ M) :
    ∑ j ∈ range n, fejerWeight n (M / 2) j * cos ((m : ℝ) * midAngle n j) = chebInt m := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  set K := M / 2 with hK
  have hexp : ∀ j : ℕ, fejerWeight n K j * cos ((m : ℝ) * midAngle n j) =
      (2 / n) * (cos ((m : ℝ) * midAngle n j) - 2 * ∑ k ∈ range K,
        (1 / (4 * ((k : ℝ) + 1) ^ 2 - 1)) *
          (cos ((((2 * (k + 1) : ℕ)) : ℝ) * midAngle n j) * cos ((m : ℝ) * midAngle n j))) := by
    intro j
    unfold fejerWeight
    have hs : (∑ k ∈ range K, cos (2 * ((k : ℝ) + 1) * midAngle n j) /
        (4 * ((k : ℝ) + 1) ^ 2 - 1)) * cos ((m : ℝ) * midAngle n j) =
        ∑ k ∈ range K, (1 / (4 * ((k : ℝ) + 1) ^ 2 - 1)) *
          (cos ((((2 * (k + 1) : ℕ)) : ℝ) * midAngle n j) * cos ((m : ℝ) * midAngle n j)) := by
      rw [sum_mul]
      exact sum_congr rfl fun k _ => by push_cast; ring
    calc _ = (2 / (n : ℝ)) * (cos ((m : ℝ) * midAngle n j) - 2 *
          ((∑ k ∈ range K, cos (2 * ((k : ℝ) + 1) * midAngle n j) /
        (4 * ((k : ℝ) + 1) ^ 2 - 1)) * cos ((m : ℝ) * midAngle n j))) := by ring
      _ = _ := by rw [hs]
  have hc0 : ∑ j ∈ range n, cos ((m : ℝ) * midAngle n j) = if m = 0 then (n : ℝ) else 0 := by
    by_cases hm0 : m = 0
    · subst hm0; simp
    · simp only [hm0, ↓reduceIte]
      exact sum_cos_midAngle hn (Nat.pos_of_ne_zero hm0) (by omega)
  have hcc : ∀ k ∈ range K, ∑ j ∈ range n, cos ((((2 * (k + 1) : ℕ)) : ℝ) * midAngle n j) *
      cos ((m : ℝ) * midAngle n j) = if 2 * (k + 1) = m then (n : ℝ) / 2 else 0 := by
    intro k hk
    have hk' := mem_range.1 hk
    rw [sum_cos_mul_cos hn (by omega) (by omega)]
    by_cases h : 2 * (k + 1) = m
    · simp [h]; omega
    · simp [h]
  have hswap : ∑ j ∈ range n, ∑ k ∈ range K, (1 / (4 * ((k : ℝ) + 1) ^ 2 - 1)) *
      (cos ((((2 * (k + 1) : ℕ)) : ℝ) * midAngle n j) * cos ((m : ℝ) * midAngle n j)) =
      ∑ k ∈ range K, (1 / (4 * ((k : ℝ) + 1) ^ 2 - 1)) *
        (if 2 * (k + 1) = m then (n : ℝ) / 2 else 0) := by
    rw [sum_comm]
    refine sum_congr rfl fun k hk => ?_
    rw [← mul_sum, hcc k hk]
  have htot : ∑ j ∈ range n, fejerWeight n K j * cos ((m : ℝ) * midAngle n j) =
      (2 / n) * ((if m = 0 then (n : ℝ) else 0) - 2 * ∑ k ∈ range K,
        (1 / (4 * ((k : ℝ) + 1) ^ 2 - 1)) * (if 2 * (k + 1) = m then (n : ℝ) / 2 else 0)) := by
    have e1 : ∀ X : ℕ → ℝ, ∑ j ∈ range n, (2 / (n : ℝ)) * X j =
        (2 / (n : ℝ)) * ∑ j ∈ range n, X j := fun X => (mul_sum _ _ _).symm
    have e2 : ∀ X : ℕ → ℝ, ∑ j ∈ range n, (2 : ℝ) * X j = 2 * ∑ j ∈ range n, X j :=
      fun X => (mul_sum _ _ _).symm
    simp_rw [hexp]
    rw [e1, sum_sub_distrib, e2, hswap, hc0]
  rw [htot]
  unfold chebInt
  by_cases hm0 : m = 0
  · subst hm0
    have : ∀ k ∈ range K, (1 / (4 * ((k : ℝ) + 1) ^ 2 - 1)) *
        (if 2 * (k + 1) = 0 then (n : ℝ) / 2 else 0) = 0 := by
      intro k _
      simp
    rw [sum_congr rfl this]
    simp
    field_simp
  · simp only [hm0, ↓reduceIte]
    by_cases hmeven : m % 2 = 0
    · obtain ⟨k0, hk0⟩ : ∃ k0, m = 2 * (k0 + 1) := ⟨m / 2 - 1, by omega⟩
      have hk0K : k0 < K := by omega
      subst hk0
      rw [sum_eq_single k0]
      · simp only [hmeven, ↓reduceIte]
        have hmv : ((2 * (k0 + 1) : ℕ) : ℝ) = 2 * ((k0 : ℝ) + 1) := by push_cast; ring
        rw [hmv]
        have hden : (4 * ((k0 : ℝ) + 1) ^ 2 - 1) ≠ 0 := by
          nlinarith [(Nat.cast_nonneg k0 : (0 : ℝ) ≤ k0)]
        have hd2 : (1 - (2 * ((k0 : ℝ) + 1)) ^ 2) = -(4 * ((k0 : ℝ) + 1) ^ 2 - 1) := by ring
        rw [hd2]
        field_simp
        ring
      · intro k _ hk
        have : ¬ (2 * (k + 1) = 2 * (k0 + 1)) := by omega
        simp [this]
      · intro h; exact absurd (mem_range.2 hk0K) h
    · have : ∀ k ∈ range K, (1 / (4 * ((k : ℝ) + 1) ^ 2 - 1)) *
          (if 2 * (k + 1) = m then (n : ℝ) / 2 else 0) = 0 := by
        intro k _
        have : ¬ (2 * (k + 1) = m) := by omega
        simp [this]
      rw [sum_congr rfl this, sum_const_zero]
      simp [hmeven]

/-- `∫_0^π sin(kθ) dθ = (1 - cos(kπ))/k` for `k ≠ 0`. -/
lemma integral_sin_mul_left {k : ℝ} (hk : k ≠ 0) :
    ∫ θ in (0 : ℝ)..π, sin (k * θ) = (1 - cos (k * π)) / k := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => sin x) hk, integral_sin]
  simp only [mul_zero, cos_zero, smul_eq_mul]
  field_simp

/-- Substitution `x = cos θ`. -/
lemma integral_comp_cos {g : ℝ → ℝ} (hg : Continuous g) :
    ∫ x in (-1 : ℝ)..1, g x = ∫ θ in (0 : ℝ)..π, g (cos θ) * sin θ := by
  have h := intervalIntegral.integral_comp_mul_deriv' (a := 0) (b := π) (f := cos)
    (f' := fun θ => -sin θ) (g := g) (fun x _ => hasDerivAt_cos x)
    (by fun_prop) hg.continuousOn
  simp only [cos_zero, cos_pi, Function.comp_apply] at h
  rw [intervalIntegral.integral_symm, ← h, ← intervalIntegral.integral_neg]
  simp only [mul_neg, neg_neg]

/-- `∫_0^π cos(mθ) sin θ dθ = ∫_{-1}^1 T_m`. -/
lemma integral_cos_mul_sin (m : ℕ) :
    ∫ θ in (0 : ℝ)..π, cos ((m : ℝ) * θ) * sin θ = chebInt m := by
  have hpt : ∀ θ : ℝ, cos ((m : ℝ) * θ) * sin θ =
      (sin (((m : ℝ) + 1) * θ) - sin (((m : ℝ) - 1) * θ)) / 2 := by
    intro θ
    have := two_mul_sin_mul_cos θ ((m : ℝ) * θ)
    have e1 : θ - (m : ℝ) * θ = -(((m : ℝ) - 1) * θ) := by ring
    have e2 : θ + (m : ℝ) * θ = ((m : ℝ) + 1) * θ := by ring
    rw [e1, e2, sin_neg] at this
    linarith
  simp_rw [hpt]
  have hi1 : IntervalIntegrable (fun θ : ℝ => sin (((m : ℝ) + 1) * θ)) MeasureTheory.volume 0 π :=
    (by fun_prop : Continuous fun θ : ℝ => sin (((m : ℝ) + 1) * θ)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun θ : ℝ => sin (((m : ℝ) - 1) * θ)) MeasureTheory.volume 0 π :=
    (by fun_prop : Continuous fun θ : ℝ => sin (((m : ℝ) - 1) * θ)).intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hi1 hi2,
    integral_sin_mul_left (by positivity)]
  have hc1 : cos (((m : ℝ) + 1) * π) = (-1) ^ (m + 1) := by
    have := cos_nat_mul_pi (m + 1); push_cast at this; exact this
  rw [hc1]
  unfold chebInt
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · simp
      norm_num
    · simp
  · have hne : ((m : ℝ) - 1) ≠ 0 := by
      have : (2 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    rw [integral_sin_mul_left hne]
    have hc2 : cos (((m : ℝ) - 1) * π) = (-1) ^ (m - 1) := by
      have := cos_nat_mul_pi (m - 1)
      rw [Nat.cast_sub (by omega)] at this
      push_cast at this; exact this
    rw [hc2]
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hd1 : ((m : ℝ) + 1) ≠ 0 := by positivity
    have hd3 : (1 - (m : ℝ) ^ 2) ≠ 0 := by nlinarith
    rcases Nat.even_or_odd m with he | ho
    · have hmod : m % 2 = 0 := Nat.even_iff.1 he
      have p1 : (-1 : ℝ) ^ (m + 1) = -1 := by rw [pow_succ, he.neg_one_pow]; ring
      have p2 : (-1 : ℝ) ^ (m - 1) = -1 := by
        obtain ⟨k, hk⟩ := he
        have : m - 1 = 2 * (k - 1) + 1 := by omega
        rw [this, pow_succ, pow_mul]; simp
      simp only [p1, p2, hmod, ↓reduceIte]
      field_simp
      ring
    · have hmod : m % 2 ≠ 0 := by
        have := Nat.odd_iff.1 ho; omega
      have p1 : (-1 : ℝ) ^ (m + 1) = 1 := by
        obtain ⟨k, hk⟩ := ho
        rw [hk, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]; simp
      have p2 : (-1 : ℝ) ^ (m - 1) = 1 := by
        obtain ⟨k, hk⟩ := ho
        have : m - 1 = 2 * k := by omega
        rw [this, pow_mul]; simp
      simp only [p1, p2, hmod, ↓reduceIte]
      ring

/-- **`∫_{-1}^1 T_m = chebInt m`.** -/
lemma integral_chebyshevT (m : ℕ) :
    ∫ x in (-1 : ℝ)..1, (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval x = chebInt m := by
  rw [integral_comp_cos (g := fun x => (Polynomial.Chebyshev.T ℝ (m : ℤ)).eval x)
    ((Polynomial.Chebyshev.T ℝ (m : ℤ)).continuous)]
  rw [← integral_cos_mul_sin m]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [Polynomial.Chebyshev.T_real_cos]
  simp

end FormalResearch.ModularBootstrap.Integrality
