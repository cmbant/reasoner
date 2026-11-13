module

public import FormalResearch.Wigner.WignerD
public import FormalResearch.Special.JacobiDef

/-!
# Wigner's small `d`-function and Jacobi polynomials

In the chamber `m' ≥ m`, `m' + m ≥ 0` (put `μ = m'-m`, `ν = m'+m`, `k = j-m'`, all natural numbers)

  `d^j_{m'm}(θ) = (-1)^μ √(k! (k+μ+ν)! / ((k+μ)! (k+ν)!)) · sin(θ/2)^μ cos(θ/2)^ν · P_k^{(μ,ν)}(cos θ)`

(Varshalovich 4.3.4(1) in this chamber; Wikipedia "Wigner D-matrix").  The proof first shows that
the one-sided definition `FormalResearch.Special.jacobi` (DLMF 18.5.7, powers of `(x-1)/2`) equals
the two-sided sum of DLMF 18.5.8 for natural `α = μ`, `β = ν`,

  `P_n^{(μ,ν)}(x) = ∑_s C(n+μ, n-s) C(n+ν, s) ((x-1)/2)^s ((x+1)/2)^{n-s}`,

by comparing coefficients of `((x-1)/2)^ℓ`: expanding `((x+1)/2)^{n-s} = (1 + (x-1)/2)^{n-s}`
binomially, the coefficient is `C(n+μ, n-ℓ) C(n+μ+ν+ℓ, ℓ)` by Vandermonde's identity, which is the
Pochhammer expression of `jacobiCoeff`.  The two-sided sum is then exactly Wigner's sum with
`(x-1)/2 = -sin²(θ/2)`, `(x+1)/2 = cos²(θ/2)`.
-/

@[expose] public section

namespace FormalResearch.Wigner

open Polynomial FormalResearch.Special

/-! ### DLMF 18.5.8 from DLMF 18.5.7 (natural parameters) -/

lemma ascPochhammer_eval_nat_succ (N k : ℕ) :
    (ascPochhammer ℝ k).eval ((N : ℝ) + 1) * (N.factorial : ℝ) = ((N + k).factorial : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, mul_assoc, mul_comm ((N : ℝ) + 1 + k), ← mul_assoc, ih,
      show N + (k + 1) = (N + k) + 1 by ring, Nat.factorial_succ]
    push_cast; ring

/-- The coefficient identity: the Pochhammer coefficient of `jacobiCoeff` is a product of binomials. -/
lemma jacobi_coeff_eq_choose (μ ν n ℓ : ℕ) (hℓ : ℓ ≤ n) :
    (ascPochhammer ℝ ℓ).eval ((n : ℝ) + μ + ν + 1) *
        (ascPochhammer ℝ (n - ℓ)).eval ((μ : ℝ) + ℓ + 1) /
      ((ℓ.factorial : ℝ) * ((n - ℓ).factorial : ℝ)) =
    (((n + μ).choose (n - ℓ) * (n + μ + ν + ℓ).choose ℓ : ℕ) : ℝ) := by
  have p1 : (ascPochhammer ℝ ℓ).eval ((n : ℝ) + μ + ν + 1) =
      ((n + μ + ν + ℓ).factorial : ℝ) / ((n + μ + ν).factorial : ℝ) := by
    rw [eq_div_iff (by positivity)]
    have := ascPochhammer_eval_nat_succ (n + μ + ν) ℓ
    push_cast at this
    exact this
  have p2 : (ascPochhammer ℝ (n - ℓ)).eval ((μ : ℝ) + ℓ + 1) =
      ((n + μ).factorial : ℝ) / ((μ + ℓ).factorial : ℝ) := by
    rw [eq_div_iff (by positivity)]
    have := ascPochhammer_eval_nat_succ (μ + ℓ) (n - ℓ)
    rw [show μ + ℓ + (n - ℓ) = n + μ by omega] at this
    push_cast at this
    exact this
  have c1 : (((n + μ).choose (n - ℓ) : ℕ) : ℝ) =
      ((n + μ).factorial : ℝ) / (((n - ℓ).factorial : ℝ) * ((μ + ℓ).factorial : ℝ)) := by
    rw [Nat.cast_choose ℝ (by omega : n - ℓ ≤ n + μ), show n + μ - (n - ℓ) = μ + ℓ by omega]
  have c2 : (((n + μ + ν + ℓ).choose ℓ : ℕ) : ℝ) =
      ((n + μ + ν + ℓ).factorial : ℝ) / ((ℓ.factorial : ℝ) * ((n + μ + ν).factorial : ℝ)) := by
    rw [Nat.cast_choose ℝ (by omega : ℓ ≤ n + μ + ν + ℓ), show n + μ + ν + ℓ - ℓ = n + μ + ν by omega]
  rw [Nat.cast_mul, c1, c2, p1, p2]
  have h1 : (0 : ℝ) < ℓ.factorial := by positivity
  have h2 : (0 : ℝ) < (n - ℓ).factorial := by positivity
  have h3 : (0 : ℝ) < (μ + ℓ).factorial := by positivity
  have h4 : (0 : ℝ) < (n + μ + ν).factorial := by positivity
  field_simp

/-- Vandermonde step: for `d ≤ n`,
`∑_{s ≤ d} C(n+μ, n-s) C(n+ν, s) C(n-s, d-s) = C(n+μ, n-d) C(n+μ+ν+d, d)`. -/
lemma jacobi_vandermonde_nat (μ ν n d : ℕ) (hd : d ≤ n) :
    ∑ s ∈ Finset.range (d + 1), (n + μ).choose (n - s) * (n + ν).choose s * (n - s).choose (d - s) =
      (n + μ).choose (n - d) * (n + μ + ν + d).choose d := by
  have step : ∀ s ∈ Finset.range (d + 1),
      (n + μ).choose (n - s) * (n + ν).choose s * (n - s).choose (d - s) =
        (n + μ).choose (n - d) * ((n + ν).choose s * (μ + d).choose (d - s)) := by
    intro s hs
    have hs' : s ≤ d := by simp at hs; omega
    have h1 : (n - s).choose (d - s) = (n - s).choose (n - d) :=
      Nat.choose_symm_of_eq_add (by omega)
    have h2 := Nat.choose_mul (n := n + μ) (k := n - s) (s := n - d) (by omega)
    rw [show n + μ - (n - d) = μ + d by omega, show n - s - (n - d) = d - s by omega] at h2
    rw [h1, mul_assoc, mul_comm ((n + ν).choose s), ← mul_assoc, h2]
    ring
  rw [Finset.sum_congr rfl step, ← Finset.mul_sum]
  congr 1
  rw [show n + μ + ν + d = (n + ν) + (μ + d) by ring, Nat.add_choose_eq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- The polynomial form of DLMF 18.5.8 in the variable `y = (x-1)/2`:
`∑_s C(n+μ,n-s) C(n+ν,s) y^s (1+y)^{n-s} = ∑_ℓ C(n+μ,n-ℓ) C(n+μ+ν+ℓ,ℓ) y^ℓ`. -/
lemma twoSided_poly (μ ν n : ℕ) :
    ∑ s ∈ Finset.range (n + 1),
        C (((n + μ).choose (n - s) * (n + ν).choose s : ℕ) : ℝ) * X ^ s * (1 + X) ^ (n - s) =
      ∑ ℓ ∈ Finset.range (n + 1),
        C (((n + μ).choose (n - ℓ) * (n + μ + ν + ℓ).choose ℓ : ℕ) : ℝ) * X ^ ℓ := by
  ext d
  simp only [finsetSum_coeff, mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_one_add_X_pow,
    coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  by_cases hd : d ≤ n
  · simp only [Finset.mem_range, show d < n + 1 by omega, ↓reduceIte]
    have hsub : ∑ s ∈ Finset.range (n + 1), (if s ≤ d then
          (((n + μ).choose (n - s) * (n + ν).choose s : ℕ) : ℝ) * (((n - s).choose (d - s) : ℕ) : ℝ)
          else 0) =
        ∑ s ∈ Finset.range (d + 1), (((n + μ).choose (n - s) * (n + ν).choose s *
          (n - s).choose (d - s) : ℕ) : ℝ) := by
      rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : d + 1 ≤ n + 1))]
      · refine Finset.sum_congr rfl fun s hs => ?_
        have : s ≤ d := by simp at hs; omega
        simp only [this, ↓reduceIte]; push_cast; ring
      · intro s _ hs
        have : ¬ s ≤ d := by simp at hs; omega
        simp [this]
    rw [hsub, ← Nat.cast_sum, jacobi_vandermonde_nat μ ν n d hd]
  · have hd' : d ∉ Finset.range (n + 1) := by simpa using hd
    simp only [hd', ↓reduceIte]
    apply Finset.sum_eq_zero
    intro s hs
    have hsn : s ≤ n := by simp at hs; omega
    by_cases hsd : s ≤ d
    · have : (n - s).choose (d - s) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [hsd, this]
    · simp [hsd]

/-- **DLMF 18.5.8** for natural parameters, from the one-sided DLMF 18.5.7 used in `jacobi`:
`P_n^{(μ,ν)}(x) = ∑_s C(n+μ,n-s) C(n+ν,s) ((x-1)/2)^s ((x+1)/2)^{n-s}`. -/
theorem jacobi_eval_nat_twoSided (μ ν n : ℕ) (x : ℝ) :
    (jacobi (μ : ℝ) (ν : ℝ) n).eval x =
      ∑ s ∈ Finset.range (n + 1), (((n + μ).choose (n - s) * (n + ν).choose s : ℕ) : ℝ) *
        ((x - 1) / 2) ^ s * ((x + 1) / 2) ^ (n - s) := by
  have h := congrArg (Polynomial.eval ((x - 1) / 2)) (twoSided_poly μ ν n)
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one] at h
  rw [show (1 : ℝ) + (x - 1) / 2 = (x + 1) / 2 by ring] at h
  rw [h, jacobi_eval]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have hℓ' : ℓ ≤ n := by simp at hℓ; omega
  rw [← jacobi_coeff_eq_choose μ ν n ℓ hℓ']
  unfold jacobiCoeff
  have : ((2 : ℝ) ^ ℓ) ≠ 0 := by positivity
  rw [div_pow]
  field_simp

/-! ### The Jacobi form of `d^j_{m'm}` -/

lemma wignerTerm_chamber {j m' m : ℚ} {μ ν k : ℕ} (hμ : m' - m = μ) (hν : m' + m = ν)
    (hk : j - m' = k) (θ : ℝ) {s : ℕ} (hs : s ≤ k) :
    wignerTerm j m' m θ s = (-1 : ℝ) ^ (μ + s) *
      (((k + ν - s).factorial : ℝ) * s.factorial * (μ + s).factorial * (k - s).factorial)⁻¹ *
      Real.cos (θ / 2) ^ (ν + 2 * (k - s)) * Real.sin (θ / 2) ^ (μ + 2 * s) := by
  have ha : j + m - s = ((k + ν - s : ℕ) : ℚ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; linarith
  have hc : m' - m + s = ((μ + s : ℕ) : ℚ) := by push_cast; linarith
  have hd : j - m' - s = ((k - s : ℕ) : ℚ) := by rw [Nat.cast_sub hs]; linarith
  unfold wignerTerm wignerMag
  rw [ha, hc, hd, Nat.floor_natCast, Nat.floor_natCast, Nat.floor_natCast, ifa_natCast,
    ifa_natCast, ifa_natCast, ifa_natCast, show k + ν - s + (k - s) = ν + 2 * (k - s) by omega,
    show s + (μ + s) = μ + 2 * s by omega]
  field_simp

/-- **Wigner `d`-function as a Jacobi polynomial** (Varshalovich 4.3.4, Wikipedia "Wigner
D-matrix"), in the chamber `m' ≥ m`, `m' + m ≥ 0`: with `μ = m'-m`, `ν = m'+m`, `k = j-m'` natural,
`d^j_{m'm}(θ) = (-1)^μ √(k!(k+μ+ν)!/((k+μ)!(k+ν)!)) sin(θ/2)^μ cos(θ/2)^ν P_k^{(μ,ν)}(cos θ)`. -/
theorem wignerSmallD_eq_jacobi {j m' m : ℚ} {μ ν k : ℕ} (hμ : m' - m = μ) (hν : m' + m = ν)
    (hk : j - m' = k) (θ : ℝ) :
    wignerSmallD j m' m θ = (-1 : ℝ) ^ μ *
      Real.sqrt ((k.factorial : ℝ) * (k + μ + ν).factorial /
        (((k + μ).factorial : ℝ) * (k + ν).factorial)) *
      Real.sin (θ / 2) ^ μ * Real.cos (θ / 2) ^ ν *
      (jacobi (μ : ℝ) (ν : ℝ) k).eval (Real.cos θ) := by
  have hfl : ⌊j - m'⌋₊ = k := by rw [hk, Nat.floor_natCast]
  have f1 : fq (j + m') = ((k + μ + ν).factorial : ℝ) := by
    rw [show j + m' = ((k + μ + ν : ℕ) : ℚ) by push_cast; linarith, fq_natCast]
  have f2 : fq (j - m') = (k.factorial : ℝ) := by rw [hk, fq_natCast]
  have f3 : fq (j + m) = ((k + ν).factorial : ℝ) := by
    rw [show j + m = ((k + ν : ℕ) : ℚ) by push_cast; linarith, fq_natCast]
  have f4 : fq (j - m) = ((k + μ).factorial : ℝ) := by
    rw [show j - m = ((k + μ : ℕ) : ℚ) by push_cast; linarith, fq_natCast]
  set F : ℝ := ((k + μ).factorial : ℝ) * ((k + ν).factorial : ℝ) with hF
  set Q : ℝ := (k.factorial : ℝ) * (k + μ + ν).factorial /
        (((k + μ).factorial : ℝ) * (k + ν).factorial) with hQ
  have hFpos : 0 < F := by positivity
  have hW : Real.sqrt (fq (j + m') * fq (j - m') * fq (j + m) * fq (j - m)) =
      F * Real.sqrt Q := by
    rw [f1, f2, f3, f4, show ((k + μ + ν).factorial : ℝ) * k.factorial * (k + ν).factorial *
        (k + μ).factorial = F ^ 2 * Q by
      rw [hF, hQ]; field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hFpos.le]
  have hc1 : (Real.cos θ - 1) / 2 = -(Real.sin (θ / 2)) ^ 2 := by
    have h : Real.cos θ = Real.cos (2 * (θ / 2)) := by ring_nf
    rw [h, Real.cos_two_mul, Real.sin_sq]; ring
  have hc2 : (Real.cos θ + 1) / 2 = Real.cos (θ / 2) ^ 2 := by
    have h : Real.cos θ = Real.cos (2 * (θ / 2)) := by ring_nf
    rw [h, Real.cos_two_mul]; ring
  have hterm : ∀ s ∈ Finset.range (k + 1), F * wignerTerm j m' m θ s =
      (-1 : ℝ) ^ μ * Real.sin (θ / 2) ^ μ * Real.cos (θ / 2) ^ ν *
        ((((k + μ).choose (k - s) * (k + ν).choose s : ℕ) : ℝ) *
          (-(Real.sin (θ / 2)) ^ 2) ^ s * (Real.cos (θ / 2) ^ 2) ^ (k - s)) := by
    intro s hs
    have hsk : s ≤ k := by simp at hs; omega
    have e3 : (-(Real.sin (θ / 2)) ^ 2) ^ s = (-1 : ℝ) ^ s * (Real.sin (θ / 2) ^ 2) ^ s := by
      rw [neg_pow]
    rw [wignerTerm_chamber hμ hν hk θ hsk, Nat.cast_mul,
      Nat.cast_choose ℝ (by omega : k - s ≤ k + μ), Nat.cast_choose ℝ (by omega : s ≤ k + ν),
      show k + μ - (k - s) = μ + s by omega, show k + ν - s = k + ν - s from rfl,
      pow_add (-1 : ℝ) μ s, pow_add (Real.cos (θ / 2)) ν, pow_mul, pow_add (Real.sin (θ / 2)) μ,
      pow_mul, e3]
    have h1 : (0 : ℝ) < ((k + ν - s).factorial : ℝ) := by positivity
    have h2 : (0 : ℝ) < (s.factorial : ℝ) := by positivity
    have h3 : (0 : ℝ) < ((μ + s).factorial : ℝ) := by positivity
    have h4 : (0 : ℝ) < ((k - s).factorial : ℝ) := by positivity
    rw [hF]
    field_simp
  rw [jacobi_eval_nat_twoSided, hc1, hc2]
  unfold wignerSmallD
  rw [finsum_wignerTerm_eq_sum, hfl, hW, mul_comm F, mul_assoc, Finset.mul_sum,
    Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  ring

/-! ### The other chambers -/

/-- The Jacobi form `√(k!(k+μ+ν)!/((k+μ)!(k+ν)!)) sin(θ/2)^μ cos(θ/2)^ν P_k^{(μ,ν)}(cos θ)` of the
Wigner `d`-function up to its sign. -/
noncomputable def wignerJacobiForm (μ ν k : ℕ) (θ : ℝ) : ℝ :=
  Real.sqrt ((k.factorial : ℝ) * (k + μ + ν).factorial /
        (((k + μ).factorial : ℝ) * (k + ν).factorial)) *
      Real.sin (θ / 2) ^ μ * Real.cos (θ / 2) ^ ν *
      (jacobi (μ : ℝ) (ν : ℝ) k).eval (Real.cos θ)

/-- Chamber `m' ≥ m`, `m' + m ≥ 0` (Varshalovich 4.3.4): `d = (-1)^μ · wignerJacobiForm`. -/
theorem wignerSmallD_chamber_A {j m' m : ℚ} {μ ν k : ℕ} (hμ : m' - m = μ) (hν : m' + m = ν)
    (hk : j - m' = k) (θ : ℝ) :
    wignerSmallD j m' m θ = (-1 : ℝ) ^ μ * wignerJacobiForm μ ν k θ := by
  rw [wignerSmallD_eq_jacobi hμ hν hk θ]
  unfold wignerJacobiForm
  ring

/-- Chamber `m' ≥ m`, `m' + m ≤ 0`, from chamber A by `d^j_{m'm} = d^j_{-m,-m'}`. -/
theorem wignerSmallD_chamber_B {j m' m : ℚ} {μ ν k : ℕ} (hμ : m' - m = μ) (hν : -(m' + m) = ν)
    (hk : j + m = k) (θ : ℝ) :
    wignerSmallD j m' m θ = (-1 : ℝ) ^ μ * wignerJacobiForm μ ν k θ := by
  rw [← wignerSmallD_neg j m' m θ]
  exact wignerSmallD_chamber_A (by linarith) (by linarith) (by linarith) θ

/-- Chamber `m' ≤ m`, `m' + m ≥ 0`, from chamber A by `d^j_{m'm} = (-1)^{m'-m} d^j_{mm'}`. -/
theorem wignerSmallD_chamber_C {j m' m : ℚ} {μ ν k : ℕ} (hμ : m - m' = μ) (hν : m + m' = ν)
    (hk : j - m = k) (θ : ℝ) :
    wignerSmallD j m' m θ = wignerJacobiForm μ ν k θ := by
  rw [wignerSmallD_swap, wignerSmallD_chamber_A hμ hν hk θ,
    show m' - m = -(μ : ℚ) by linarith, sgn_neg', sgn_natCast, ← mul_assoc,
    show (-1 : ℝ) ^ μ * (-1 : ℝ) ^ μ = 1 by rw [← mul_pow]; norm_num, one_mul]

/-- Chamber `m' ≤ m`, `m' + m ≤ 0`, from chamber B by `d^j_{m'm} = (-1)^{m'-m} d^j_{mm'}`. -/
theorem wignerSmallD_chamber_D {j m' m : ℚ} {μ ν k : ℕ} (hμ : m - m' = μ) (hν : -(m + m') = ν)
    (hk : j + m' = k) (θ : ℝ) :
    wignerSmallD j m' m θ = wignerJacobiForm μ ν k θ := by
  rw [wignerSmallD_swap, wignerSmallD_chamber_B hμ hν hk θ,
    show m' - m = -(μ : ℚ) by linarith, sgn_neg', sgn_natCast, ← mul_assoc,
    show (-1 : ℝ) ^ μ * (-1 : ℝ) ^ μ = 1 by rw [← mul_pow]; norm_num, one_mul]

/-- info: 'FormalResearch.Wigner.jacobi_eval_nat_twoSided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_eval_nat_twoSided

/-- info: 'FormalResearch.Wigner.wignerSmallD_eq_jacobi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_eq_jacobi

/-- info: 'FormalResearch.Wigner.wignerSmallD_chamber_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_chamber_A

/-- info: 'FormalResearch.Wigner.wignerSmallD_chamber_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_chamber_B

/-- info: 'FormalResearch.Wigner.wignerSmallD_chamber_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_chamber_C

/-- info: 'FormalResearch.Wigner.wignerSmallD_chamber_D' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wignerSmallD_chamber_D

end FormalResearch.Wigner
