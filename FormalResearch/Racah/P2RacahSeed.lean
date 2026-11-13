module

public import FormalResearch.Racah.P2RacahMidpoint
public import FormalResearch.Wigner.SpecialValues

/-!
# The positive stretched seed (Weyl P2, `lem:6jseed`): product lemmas
-/

@[expose] public section

namespace FormalResearch.Racah.SixJ

open FormalResearch.Wigner

lemma fact_ratio (u d : ℕ) :
    (((u + d).factorial : ℕ) : ℝ) = (u.factorial : ℝ) * ∏ k ∈ Finset.range d, ((u : ℝ) + 1 + k) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih, show u + (d + 1) = (u + d) + 1 by ring,
      Nat.factorial_succ]
    push_cast; ring

lemma pair_even (M : ℕ) : ∀ y : ℝ,
    ∏ j ∈ Finset.range (2 * M), (y + j) =
      ∏ k ∈ Finset.range M, ((y + k) * (y + (2 * M - 1 : ℝ) - k)) := by
  induction M with
  | zero => intro y; simp
  | succ M ih =>
    intro y
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ',
      Finset.prod_range_succ']
    have := ih (y + 1)
    have h2 : ∏ j ∈ Finset.range (2 * M), (y + ((j + 1 : ℕ) : ℝ)) =
        ∏ k ∈ Finset.range M, ((y + ((k + 1 : ℕ) : ℝ)) *
          (y + (2 * ((M + 1 : ℕ) : ℝ) - 1) - ((k + 1 : ℕ) : ℝ))) :=
      (Finset.prod_congr rfl (fun j _ => by push_cast; ring)).trans
        (this.trans (Finset.prod_congr rfl (fun k _ => by push_cast; ring)))
    rw [h2]
    have h3 : (y + ((2 * M + 1 : ℕ) : ℝ)) = (y + (2 * ((M + 1 : ℕ) : ℝ) - 1) - ((0 : ℕ) : ℝ)) := by
      push_cast; ring
    rw [h3]
    ring

lemma pair_odd (M : ℕ) : ∀ y : ℝ,
    ∏ j ∈ Finset.range (2 * M + 1), (y + j) =
      (y + M) * ∏ k ∈ Finset.range M, ((y + k) * (y + 2 * M - k)) := by
  induction M with
  | zero => intro y; simp
  | succ M ih =>
    intro y
    rw [show 2 * (M + 1) + 1 = 2 * M + 1 + 1 + 1 by ring, Finset.prod_range_succ,
      Finset.prod_range_succ', Finset.prod_range_succ' (fun k : ℕ =>
        (y + (k : ℝ)) * (y + 2 * ((M + 1 : ℕ) : ℝ) - (k : ℝ))) M]
    have := ih (y + 1)
    have h2 : ∏ j ∈ Finset.range (2 * M + 1), (y + ((j + 1 : ℕ) : ℝ)) =
        (y + ((M + 1 : ℕ) : ℝ)) * ∏ k ∈ Finset.range M, ((y + ((k + 1 : ℕ) : ℝ)) *
          (y + 2 * ((M + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ))) :=
      (Finset.prod_congr rfl (fun j _ => by push_cast; ring)).trans
        ((this.trans (by
          congr 1
          · push_cast; ring
          · exact Finset.prod_congr rfl (fun k _ => by push_cast; ring))))
    rw [h2]
    have h3 : (y + ((2 * M + 1 + 1 : ℕ) : ℝ)) = (y + 2 * ((M + 1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ)) := by
      push_cast; ring
    rw [h3]
    have h4 : (y + ((M + 1 : ℕ) : ℝ)) = (y + ((M + 1 : ℕ) : ℝ)) := rfl
    ring

/-- `𝔆_r(X) = ∏_{q=-(r-1)/2}^{(r-1)/2} (X+q)` (`eq:Ccentral6`), for `r ∈ ℕ` (`𝔆_0 = 1`). -/
noncomputable def cenProd (r : ℕ) (X : ℝ) : ℝ :=
  ∏ k ∈ Finset.range r, (X - ((r : ℝ) - 1) / 2 + k)

/-- `𝔇_m(X) = ∏_{q ∈ Q_m} ((2X)² - q²)`, where `Q_m = {m, m-1, …}` is the set of positive
numbers `m - k` (`k ∈ ℕ`): `{1,…,m}` for integer `m` and `{1/2, 3/2, …, m}` for half-integer `m`.
The set has `⌈m⌉` elements. -/
noncomputable def dProd (m : ℚ) (X : ℝ) : ℝ :=
  ∏ k ∈ Finset.range ⌈m⌉₊, ((2 * X) ^ 2 - ((m : ℝ) - k) ^ 2)

open Classical in
/-- `χ_m(A,B) = 1` for integer `m` and `4AB` for half-integer `m`. -/
noncomputable def chiM (m : ℚ) (A B : ℝ) : ℝ := if IsNat m then 1 else 4 * A * B

lemma cenProd_eq (r u : ℕ) (X : ℝ) (hX : X - ((r : ℝ) - 1) / 2 = u + 1) :
    cenProd r X = (((u + r).factorial : ℕ) : ℝ) / (u.factorial : ℝ) := by
  unfold cenProd
  rw [hX, fact_ratio u r]
  have : (u.factorial : ℝ) ≠ 0 := by positivity
  field_simp

open Classical in
lemma dProd_mul (m : ℚ) (μ u : ℕ) (hμ : (μ : ℚ) = 2 * m) (X : ℝ)
    (hX : 2 * X - (m : ℝ) = u + 1) :
    dProd m X * (if IsNat m then 2 * X else 1) =
      (((u + μ + 1).factorial : ℕ) : ℝ) / (u.factorial : ℝ) := by
  have hu : (u.factorial : ℝ) ≠ 0 := by positivity
  rcases Nat.even_or_odd' μ with ⟨M, hM | hM⟩
  · -- integer `m = M`
    have hmM : m = M := by
      have : ((2 * M : ℕ) : ℚ) = 2 * m := by rw [← hM]; exact hμ
      push_cast at this; linarith
    have hnat : IsNat m := ⟨M, hmM⟩
    rw [if_pos hnat]
    have hc : ⌈m⌉₊ = M := by rw [hmM, Nat.ceil_natCast]
    unfold dProd
    rw [hc, eq_div_iff hu, show u + μ + 1 = u + (2 * M + 1) by omega, fact_ratio u (2 * M + 1),
      pair_odd M ((u : ℝ) + 1)]
    have hm' : (m : ℝ) = M := by rw [hmM]; simp
    rw [hm'] at hX
    have e1 : (u : ℝ) + 1 + M = 2 * X := by linarith
    rw [e1]
    have : ∏ k ∈ Finset.range M, (((u : ℝ) + 1 + k) * ((u : ℝ) + 1 + 2 * M - k)) =
        ∏ k ∈ Finset.range M, ((2 * X) ^ 2 - ((M : ℝ) - k) ^ 2) := by
      refine Finset.prod_congr rfl fun k _ => ?_
      have : (u : ℝ) + 1 = 2 * X - M := by linarith
      rw [this]; ring
    rw [this, hm']
    ring
  · -- half-integer `m = M + 1/2`
    have hmM : m = M + 1 / 2 := by
      have : ((2 * M + 1 : ℕ) : ℚ) = 2 * m := by rw [← hM]; exact hμ
      push_cast at this; linarith
    have hnat : ¬ IsNat m := by
      rintro ⟨n, hn⟩
      have : (2 * n : ℚ) = 2 * M + 1 := by rw [← hn, hmM]; ring
      have : 2 * n = 2 * M + 1 := by exact_mod_cast this
      omega
    rw [if_neg hnat]
    have hc : ⌈m⌉₊ = M + 1 := by
      rw [Nat.ceil_eq_iff (by omega), hmM]
      constructor <;> push_cast <;> linarith
    unfold dProd
    rw [hc, mul_one, eq_div_iff hu, show u + μ + 1 = u + 2 * (M + 1) by omega,
      fact_ratio u (2 * (M + 1)), pair_even (M + 1) ((u : ℝ) + 1)]
    have hm' : (m : ℝ) = M + 1 / 2 := by rw [hmM]; push_cast; ring
    rw [hm'] at hX
    have : ∏ k ∈ Finset.range (M + 1), (((u : ℝ) + 1 + k) * ((u : ℝ) + 1 + (2 * ((M + 1 : ℕ) : ℝ) - 1) - k)) =
        ∏ k ∈ Finset.range (M + 1), ((2 * X) ^ 2 - (((M : ℝ) + 1 / 2) - k) ^ 2) := by
      refine Finset.prod_congr rfl fun k _ => ?_
      have : (u : ℝ) + 1 = 2 * X - (M + 1 / 2) := by linarith
      rw [this]; push_cast; ring
    rw [this, hm']
    ring

/-- `𝒮_m(A,B,C)` of `eq:6jseed`:
`Γ(2m+1)/(Γ(m+n+1)Γ(m-n+1)) · χ_m(A,B)/(𝔇_m(A)𝔇_m(B)) · 𝔆_{m-n}(A-B+C) 𝔆_{m-n}(-A+B+C)
· 𝔆_{m+n}(A+B-C) 𝔆_{m+n}(A+B+C)`.  The Gamma ratio is the binomial coefficient
`C(2m, m+n)` (for `m ± n ∈ ℕ`, `2m ∈ ℕ`). -/
noncomputable def seedS (m n : ℚ) (A B C : ℝ) : ℝ :=
  ((Nat.choose ⌊2 * m⌋₊ ⌊m + n⌋₊ : ℕ) : ℝ) * chiM m A B / (dProd m A * dProd m B) *
    cenProd ⌊m - n⌋₊ (A - B + C) * cenProd ⌊m - n⌋₊ (-A + B + C) *
    cenProd ⌊m + n⌋₊ (A + B - C) * cenProd ⌊m + n⌋₊ (A + B + C)

lemma ifa_zero' : ifa 0 = 1 := by simpa using ifa_natCast 0

/-- The Racah sum of the stretched `6j` `{a b c; b+m a+n m}` has the single term `t = a+b+c+m+n`. -/
lemma racahSum6_seed (a b c m n : ℚ) (α₁ α₃ e₂ r s N : ℕ) (hN : (N : ℚ) = a + b + c + m + n)
    (hs : m + n = s) (hα₃ : -a + b + c = α₃) (he₂ : c - (b + m) + (a + n) = e₂)
    (hα₁ : a + b - c = α₁) (hr : m - n = r) :
    racahSum6 a b c (b + m) (a + n) m =
      (-1 : ℝ) ^ N * (((N + 1).factorial : ℕ) : ℝ) *
        ((s.factorial : ℝ) * α₃.factorial * e₂.factorial * α₁.factorial * r.factorial)⁻¹ := by
  unfold racahSum6
  rw [finsum_eq_single _ N]
  · unfold term6
    rw [P7_vec]
    have a1 : (N : ℚ) - a - b - c = (s : ℚ) := by linarith
    have a2 : (N : ℚ) - a - (a + n) - m = (α₃ : ℚ) := by linarith
    have a3 : (N : ℚ) - (b + m) - b - m = (e₂ : ℚ) := by linarith
    have a4 : (N : ℚ) - (b + m) - (a + n) - c = 0 := by linarith
    have a5 : a + b + (b + m) + (a + n) - (N : ℚ) = (α₁ : ℚ) := by linarith
    have a6 : b + c + (a + n) + m - (N : ℚ) = 0 := by linarith
    have a7 : c + a + m + (b + m) - (N : ℚ) = (r : ℚ) := by linarith
    rw [a1, a2, a3, a4, a5, a6, a7, ifa_zero', ifa_natCast, ifa_natCast, ifa_natCast, ifa_natCast,
      ifa_natCast]
    simp only [mul_one]
    rw [mul_inv, mul_inv, mul_inv, mul_inv]
  · intro t ht
    unfold term6
    rw [P7_vec]
    rcases lt_or_gt_of_ne ht with hlt | hgt
    · have : ifa ((t : ℚ) - (b + m) - (a + n) - c) = 0 := by
        apply ifa_eq_zero_of_neg
        have : (t : ℚ) + 1 ≤ N := by exact_mod_cast hlt
        linarith
      rw [this]; simp
    · have : ifa (b + c + (a + n) + m - (t : ℚ)) = 0 := by
        apply ifa_eq_zero_of_neg
        have : (N : ℚ) + 1 ≤ t := by exact_mod_cast hgt
        linarith
      rw [this]; simp

lemma seed_alg (A B a1 a2 a3 e1 e2 e3 u0 v0 m0 r0 s0 n1 n2 n3 n4 : ℝ)
    (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (he1 : 0 < e1) (he2 : 0 < e2) (he3 : 0 < e3)
    (hu0 : 0 < u0) (hv0 : 0 < v0) (hm0 : 0 < m0) (hr0 : 0 < r0) (hs0 : 0 < s0) (hn1 : 0 < n1)
    (hn2 : 0 < n2) (hn3 : 0 < n3) (hn4 : 0 < n4) :
    4 * (A * B) * ((a1 * a2 * a3 / n1) * (u0 * r0 * s0 / n2) * (v0 * m0 / n3) * (e3 * e1 * e2 / n4)) *
        (n4 * (s0 * a3 * e2 * a1 * r0)⁻¹) ^ 2 =
      m0 / (r0 * s0) * (4 * A * B * u0 * v0 / (n2 * n3)) * (a2 / e2) * (e1 / a3) * (e3 / a1) *
        (n4 / n1) := by
  field_simp

open Classical in
lemma chi_dProd (m : ℚ) (μ u ν : ℕ) (hμ : (μ : ℚ) = 2 * m) (A B : ℝ) (hA0 : 0 < A) (hB0 : 0 < B)
    (hA : 2 * A - (m : ℝ) = u + 1) (hB : 2 * B - (m : ℝ) = ν + 1) :
    chiM m A B / (dProd m A * dProd m B) =
      4 * A * B * (u.factorial : ℝ) * ν.factorial /
        ((((u + μ + 1).factorial : ℕ) : ℝ) * (((ν + μ + 1).factorial : ℕ) : ℝ)) := by
  have hDA := dProd_mul m μ u hμ A hA
  have hDB := dProd_mul m μ ν hμ B hB
  have hu : (u.factorial : ℝ) ≠ 0 := by positivity
  have hv : (ν.factorial : ℝ) ≠ 0 := by positivity
  have hGu : (((u + μ + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hGv : (((ν + μ + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  rw [eq_div_iff hu] at hDA
  rw [eq_div_iff hv] at hDB
  by_cases hn : IsNat m
  · unfold chiM
    rw [if_pos hn]
    rw [if_pos hn] at hDA hDB
    have eA : dProd m A = (((u + μ + 1).factorial : ℕ) : ℝ) / u.factorial / (2 * A) := by
      field_simp; linarith
    have eB : dProd m B = (((ν + μ + 1).factorial : ℕ) : ℝ) / ν.factorial / (2 * B) := by
      field_simp; linarith
    rw [eA, eB]
    field_simp
    norm_num
  · unfold chiM
    rw [if_neg hn]
    rw [if_neg hn] at hDA hDB
    have eA : dProd m A = (((u + μ + 1).factorial : ℕ) : ℝ) / u.factorial := by
      field_simp; linarith
    have eB : dProd m B = (((ν + μ + 1).factorial : ℕ) : ℝ) / ν.factorial := by
      field_simp; linarith
    rw [eA, eB]
    field_simp

set_option maxHeartbeats 600000 in
/-- **`lem:6jseed`, nonnegativity and square** (exact stretched seed): for `f = m` (the lowest rank,
`m ≥ |n|`, integer or half-integer), at every physical point
`Φ_m ≥ 0` and `Φ_m² = 𝒮_m(A,B,C)`. -/
theorem Phi6_seed_sq (a b c m n : ℚ) (h1 : IsTri m (b + m) b) (h2 : IsTri m a (a + n))
    (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n)) :
    0 ≤ Phi6 a b c m m n ∧
      Phi6 a b c m m n ^ 2 = seedS m n (wA a n) (wB b m) (wC c) := by
  obtain ⟨⟨μ, hμ⟩, ⟨z, hz⟩, ⟨ν, hν⟩⟩ := h1
  obtain ⟨⟨r, hr⟩, ⟨s, hs⟩, ⟨u, hu⟩⟩ := h2
  obtain ⟨⟨α₂, hα₂⟩, ⟨α₃, hα₃⟩, ⟨α₁, hα₁⟩⟩ := h3
  obtain ⟨⟨e₁, he₁⟩, ⟨e₂, he₂⟩, ⟨e₃, he₃⟩⟩ := h4
  have hμrs : μ = r + s := by
    have : (μ : ℚ) = r + s := by linarith
    exact_mod_cast this
  have rel1 : e₁ = α₃ + r := by
    have : (e₁ : ℚ) = α₃ + r := by linarith
    exact_mod_cast this
  have rel2 : α₂ = e₂ + r := by
    have : (α₂ : ℚ) = e₂ + r := by linarith
    exact_mod_cast this
  have rel3 : e₃ = α₁ + s := by
    have : (e₃ : ℚ) = α₁ + s := by linarith
    exact_mod_cast this
  have hz0 : z = 0 := by
    have : (z : ℚ) = 0 := by linarith
    exact_mod_cast this
  have hN : ((α₁ + α₂ + α₃ + s : ℕ) : ℚ) = a + b + c + m + n := by push_cast; linarith
  have hseed := racahSum6_seed a b c m n α₁ α₃ e₂ r s (α₁ + α₂ + α₃ + s) hN (by linarith)
    (by linarith) he₂ (by linarith) (by linarith)
  -- the four triangle coefficients
  have T1 := triSq_of_nat (a := a) (b := b) (c := c) (p := α₁) (q := α₂) (r := α₃)
    (by linarith) (by linarith) (by linarith)
  have T2 := triSq_of_nat (a := a) (b := a + n) (c := m) (p := u) (q := r) (r := s)
    (by linarith) (by linarith) (by linarith)
  have T3 := triSq_of_nat (a := b + m) (b := b) (c := m) (p := ν) (q := μ) (r := 0)
    (by linarith) (by linarith) (by push_cast; ring)
  have T4 := triSq_of_nat (a := b + m) (b := a + n) (c := c) (p := e₃) (q := e₁) (r := e₂)
    (by linarith) (by linarith) (by linarith)
  have hn1 : u + r + s + 1 = u + μ + 1 := by omega
  have hn2 : ν + μ + 0 + 1 = ν + μ + 1 := by omega
  have hn3 : e₃ + e₁ + e₂ + 1 = α₁ + α₂ + α₃ + s + 1 := by omega
  rw [hn1] at T2
  rw [hn2] at T3
  rw [hn3] at T4
  simp only [Nat.factorial_zero, Nat.cast_one, mul_one] at T3
  -- positivity of A, B
  have hm0 : (0 : ℝ) ≤ m := by
    have : (0 : ℚ) ≤ μ := by positivity
    have : (0 : ℚ) ≤ m := by linarith
    exact_mod_cast this
  have hA : 0 < wA a n := by
    have hu' : (0 : ℚ) ≤ u := by positivity
    have : (0 : ℝ) ≤ u := by exact_mod_cast hu'
    have hu2 : (u : ℝ) = -m + a + (a + n) := by exact_mod_cast hu.symm
    unfold wA; linarith
  have hB : 0 < wB b m := by
    have hv' : (0 : ℚ) ≤ ν := by positivity
    have : (0 : ℝ) ≤ ν := by exact_mod_cast hv'
    have hv2 : (ν : ℝ) = -m + (b + m) + b := by exact_mod_cast hν.symm
    unfold wB; linarith
  -- the symbol
  have hPhi : Phi6 a b c m m n =
      2 * Real.sqrt (wA a n * wB b m) *
        (Real.sqrt (triSq a b c) * Real.sqrt (triSq a (a + n) m) * Real.sqrt (triSq (b + m) b m) *
          Real.sqrt (triSq (b + m) (a + n) c)) *
        ((((α₁ + α₂ + α₃ + s + 1).factorial : ℕ) : ℝ) *
          ((s.factorial : ℝ) * α₃.factorial * e₂.factorial * α₁.factorial * r.factorial)⁻¹) := by
    unfold Phi6 W6 sixJ
    rw [hseed]
    have e : a + b + c + m + n = ((α₁ + α₂ + α₃ + s : ℕ) : ℚ) := hN.symm
    rw [e, sgn_natCast]
    have hs2 : ((-1 : ℝ) ^ (α₁ + α₂ + α₃ + s)) * (-1) ^ (α₁ + α₂ + α₃ + s) = 1 := by
      rw [← mul_pow]; norm_num
    generalize ((-1 : ℝ) ^ (α₁ + α₂ + α₃ + s)) = w at hs2 ⊢
    linear_combination (2 * Real.sqrt (wA a n * wB b m) *
        (Real.sqrt (triSq a b c) * Real.sqrt (triSq a (a + n) m) * Real.sqrt (triSq (b + m) b m) *
          Real.sqrt (triSq (b + m) (a + n) c)) *
        ((((α₁ + α₂ + α₃ + s + 1).factorial : ℕ) : ℝ) *
          ((s.factorial : ℝ) * α₃.factorial * e₂.factorial * α₁.factorial * r.factorial)⁻¹)) * hs2
  have hρ : 0 ≤ ((((α₁ + α₂ + α₃ + s + 1).factorial : ℕ) : ℝ) *
          ((s.factorial : ℝ) * α₃.factorial * e₂.factorial * α₁.factorial * r.factorial)⁻¹) := by
    positivity
  have hX : 0 ≤ Real.sqrt (triSq a b c) * Real.sqrt (triSq a (a + n) m) *
      Real.sqrt (triSq (b + m) b m) * Real.sqrt (triSq (b + m) (a + n) c) := by positivity
  refine ⟨by rw [hPhi]; positivity, ?_⟩
  rw [hPhi]
  have hsq : (Real.sqrt (triSq a b c) * Real.sqrt (triSq a (a + n) m) * Real.sqrt (triSq (b + m) b m) *
      Real.sqrt (triSq (b + m) (a + n) c)) ^ 2 =
      triSq a b c * triSq a (a + n) m * triSq (b + m) b m * triSq (b + m) (a + n) c := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (triSq_nonneg _ _ _), Real.sq_sqrt (triSq_nonneg _ _ _),
      Real.sq_sqrt (triSq_nonneg _ _ _), Real.sq_sqrt (triSq_nonneg _ _ _)]
  have hAB : (2 * Real.sqrt (wA a n * wB b m)) ^ 2 = 4 * (wA a n * wB b m) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  rw [mul_pow, mul_pow, hsq, hAB, T1, T2, T3, T4]
  -- the seed `𝒮_m`
  have hμ' : (μ : ℚ) = 2 * m := by linarith
  have fm : ⌊2 * m⌋₊ = μ := by rw [← hμ', Nat.floor_natCast]
  have fs : ⌊m + n⌋₊ = s := by
    have : m + n = (s : ℚ) := by linarith
    rw [this, Nat.floor_natCast]
  have fr : ⌊m - n⌋₊ = r := by
    have : m - n = (r : ℚ) := by linarith
    rw [this, Nat.floor_natCast]
  have hch : ((μ.choose s : ℕ) : ℝ) = (μ.factorial : ℝ) / ((r.factorial : ℝ) * s.factorial) := by
    rw [hμrs, add_comm r s, Nat.cast_add_choose, mul_comm]
  have hr_ : (r : ℝ) = (m : ℝ) - n := by
    have : (r : ℚ) = m - n := by linarith
    exact_mod_cast this
  have hs_ : (s : ℝ) = (m : ℝ) + n := by
    have : (s : ℚ) = m + n := by linarith
    exact_mod_cast this
  have hu_ : (u : ℝ) = 2 * a + n - m := by
    have : (u : ℚ) = 2 * a + n - m := by linarith
    exact_mod_cast this
  have hν_ : (ν : ℝ) = 2 * b := by
    have : (ν : ℚ) = 2 * b := by linarith
    exact_mod_cast this
  have hα₁_ : (α₁ : ℝ) = a + b - c := by
    have : (α₁ : ℚ) = a + b - c := by linarith
    exact_mod_cast this
  have hα₂_ : (α₂ : ℝ) = c + a - b := by
    have : (α₂ : ℚ) = c + a - b := by linarith
    exact_mod_cast this
  have hα₃_ : (α₃ : ℝ) = c - a + b := by
    have : (α₃ : ℚ) = c - a + b := by linarith
    exact_mod_cast this
  have he₁_ : (e₁ : ℝ) = c + (b + m) - (a + n) := by
    have : (e₁ : ℚ) = c + (b + m) - (a + n) := by linarith
    exact_mod_cast this
  have he₂_ : (e₂ : ℝ) = c - (b + m) + (a + n) := by
    have : (e₂ : ℚ) = c - (b + m) + (a + n) := by linarith
    exact_mod_cast this
  have he₃_ : (e₃ : ℝ) = -c + (b + m) + (a + n) := by
    have : (e₃ : ℚ) = -c + (b + m) + (a + n) := by linarith
    exact_mod_cast this
  have c1 : cenProd r (wA a n - wB b m + wC c) =
      (α₂.factorial : ℝ) / (e₂.factorial : ℝ) := by
    rw [cenProd_eq r e₂ _ (by unfold wA wB wC; rw [hr_, he₂_]; linarith), ← rel2]
  have c2 : cenProd r (-wA a n + wB b m + wC c) =
      (e₁.factorial : ℝ) / (α₃.factorial : ℝ) := by
    rw [cenProd_eq r α₃ _ (by unfold wA wB wC; rw [hr_, hα₃_]; linarith), ← rel1]
  have c3 : cenProd s (wA a n + wB b m - wC c) =
      (e₃.factorial : ℝ) / (α₁.factorial : ℝ) := by
    rw [cenProd_eq s α₁ _ (by unfold wA wB wC; rw [hs_, hα₁_]; linarith), ← rel3]
  have c4 : cenProd s (wA a n + wB b m + wC c) =
      (((α₁ + α₂ + α₃ + s + 1).factorial : ℕ) : ℝ) /
        (((α₁ + α₂ + α₃ + 1).factorial : ℕ) : ℝ) := by
    rw [cenProd_eq s (α₁ + α₂ + α₃ + 1) _
      (by unfold wA wB wC; rw [hs_]; push_cast; rw [hα₁_, hα₂_, hα₃_]; linarith),
      show α₁ + α₂ + α₃ + 1 + s = α₁ + α₂ + α₃ + s + 1 by omega]
  have chi := chi_dProd m μ u ν hμ' (wA a n) (wB b m) hA hB
    (by unfold wA; rw [hu_]; linarith) (by unfold wB; rw [hν_]; linarith)
  have hS : seedS m n (wA a n) (wB b m) (wC c) =
      (μ.factorial : ℝ) / ((r.factorial : ℝ) * s.factorial) *
        (chiM m (wA a n) (wB b m) / (dProd m (wA a n) * dProd m (wB b m))) *
        cenProd r (wA a n - wB b m + wC c) * cenProd r (-wA a n + wB b m + wC c) *
        cenProd s (wA a n + wB b m - wC c) * cenProd s (wA a n + wB b m + wC c) := by
    unfold seedS
    rw [fm, fs, fr, hch]
    ring
  rw [hS, c1, c2, c3, c4, chi]
  exact seed_alg (wA a n) (wB b m) (α₁.factorial : ℝ) (α₂.factorial : ℝ)
    (α₃.factorial : ℝ) (e₁.factorial : ℝ) (e₂.factorial : ℝ) (e₃.factorial : ℝ) (u.factorial : ℝ)
    (ν.factorial : ℝ) (μ.factorial : ℝ) (r.factorial : ℝ) (s.factorial : ℝ)
    (((α₁ + α₂ + α₃ + 1).factorial : ℕ) : ℝ) (((u + μ + 1).factorial : ℕ) : ℝ)
    (((ν + μ + 1).factorial : ℕ) : ℝ) (((α₁ + α₂ + α₃ + s + 1).factorial : ℕ) : ℝ)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)

/-- **`lem:6jseed`** (Positive stretched seed), `eq:6jseedsign`: for `f = m` (the lowest rank; the
sector `m ≥ |n|`, `m ≥ 0` is implied by the triangle `(m, a, a+n)`), at every physical point
`Φ_m = √𝒮_m(A,B,C)` with the positive square root, for integer and half-integer spins alike.
Hypotheses: the four triads `(m, b+m, b)`, `(m, a, a+n)`, `(c, a, b)`, `(c, b+m, a+n)`.
Also `Φ_m² = 𝒮_m` is `Phi6_seed_sq`. -/
theorem Phi6_seed (a b c m n : ℚ) (h1 : IsTri m (b + m) b) (h2 : IsTri m a (a + n))
    (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n)) :
    Phi6 a b c m m n = Real.sqrt (seedS m n (wA a n) (wB b m) (wC c)) := by
  obtain ⟨h0, hsq⟩ := Phi6_seed_sq a b c m n h1 h2 h3 h4
  rw [← hsq]
  exact (Real.sqrt_sq h0).symm

/-- `eq:6jexceptionalseed`, first start: `Φ_0 = 1` (`m = n = 0`, `f = 0`), from DLMF 34.5.1. -/
theorem Phi6_exceptional_zero (a b c : ℚ) (h : IsTri c a b) : Phi6 a b c 0 0 0 = 1 := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩ := h
  have hN : ((p + q + r : ℕ) : ℚ) = c + a + b := by push_cast; linarith
  unfold Phi6
  rw [W6_eq_regge_form]
  simp only [add_zero]
  rw [sixJ_zero_left ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩ (p + q + r) hN]
  have e : a + b + c = ((p + q + r : ℕ) : ℚ) := by rw [hN]; ring
  rw [e, sgn_natCast]
  have hs2 : ((-1 : ℝ) ^ (p + q + r)) * (-1) ^ (p + q + r) = 1 := by
    rw [← mul_pow]; norm_num
  generalize ((-1 : ℝ) ^ (p + q + r)) = w at hs2 ⊢
  have ha : (0 : ℝ) ≤ 2 * a := by
    have : (0 : ℚ) ≤ p := by positivity
    have : (0 : ℚ) ≤ q := by positivity
    have : (0 : ℝ) ≤ 2 * a := by
      have : (0 : ℚ) ≤ 2 * a := by linarith
      exact_mod_cast this
    exact this
  have hb : (0 : ℝ) ≤ 2 * b := by
    have : (0 : ℚ) ≤ 2 * b := by
      have : (0 : ℚ) ≤ p := by positivity
      have : (0 : ℚ) ≤ r := by positivity
      linarith
    exact_mod_cast this
  unfold wA wB
  push_cast
  have e2 : ((2 * (a : ℝ) + 1) * (2 * (b : ℝ) + 1)) =
      (2 : ℝ) ^ 2 * (((a : ℝ) + (0 + 1) / 2) * ((b : ℝ) + (0 + 1) / 2)) := by ring
  have hXa : 0 < (a : ℝ) + (0 + 1) / 2 := by linarith
  have hXb : 0 < (b : ℝ) + (0 + 1) / 2 := by linarith
  rw [e2, Real.sqrt_mul (show (0 : ℝ) ≤ 2 ^ 2 by norm_num), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_mul hXa.le]
  have h1 := Real.sqrt_pos.mpr hXa
  have h2 := Real.sqrt_pos.mpr hXb
  field_simp
  linear_combination hs2

lemma eta_alg (X Y : ℝ) (hX : X ≠ 0) (hY : Y ≠ 0) :
    (1 - 1 ^ 2 / (4 * X ^ 2)) * (1 - 1 ^ 2 / (4 * Y ^ 2)) =
      ((2 * X - 1) * (2 * X + 1) * ((2 * Y - 1) * (2 * Y + 1))) / (4 * (X * Y)) ^ 2 := by
  field_simp
  ring

/-- `eq:6jexceptionalseed`, second start (`m = n = 0`, `f = 1`), from DLMF 34.5.7:
`Φ_1 = (x - 1/(8AB)) / √((1-1/4A²)(1-1/4B²))` (when `a, b ≥ 1/2`, so that `f = 1` is admissible). -/
theorem Phi6_exceptional_one (a b c : ℚ) (h : IsTri c a b) (ha : 1 ≤ 2 * a) (hb : 1 ≤ 2 * b) :
    Phi6 a b c 1 0 0 =
      (cosA (wA a 0) (wB b 0) (wC c) - 1 / (8 * wA a 0 * wB b 0)) / etaK (wA a 0) (wB b 0) 1 := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩ := h
  have hN : ((p + q + r : ℕ) : ℚ) = c + a + b := by push_cast; linarith
  have ha' : (1 : ℝ) ≤ 2 * a := by exact_mod_cast ha
  have hb' : (1 : ℝ) ≤ 2 * b := by exact_mod_cast hb
  unfold Phi6
  rw [W6_eq_regge_form]
  simp only [add_zero]
  rw [sixJ_one_left ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩ (p + q + r) hN ha hb]
  have e : a + b + c + 1 = ((p + q + r + 1 : ℕ) : ℚ) := by push_cast; linarith
  rw [e, sgn_natCast]
  have hs2 : ((-1 : ℝ) ^ (p + q + r + 1)) * (-1) ^ (p + q + r + 1) = 1 := by
    rw [← mul_pow]; norm_num
  generalize ((-1 : ℝ) ^ (p + q + r + 1)) = w at hs2 ⊢
  unfold wA wB wC cosA etaK
  push_cast
  set Sg : ℝ := ((a : ℝ) * (a + 1) + b * (b + 1) - c * (c + 1)) with hSg
  have hX : 0 < ((a : ℝ) + (0 + 1) / 2) * ((b : ℝ) + (0 + 1) / 2) := by
    have : 0 < (a : ℝ) + (0 + 1) / 2 := by linarith
    have : 0 < (b : ℝ) + (0 + 1) / 2 := by linarith
    positivity
  have hP' : 0 ≤ (2 * (a : ℝ)) * (2 * a + 2) * ((2 * (b : ℝ)) * (2 * b + 2)) := by
    have : 0 ≤ 2 * (a : ℝ) := by linarith
    have : 0 ≤ 2 * (b : ℝ) := by linarith
    positivity
  have hQ : (2 * (a : ℝ)) * (2 * a + 1) * (2 * a + 2) * ((2 * (b : ℝ)) * (2 * b + 1) * (2 * b + 2)) =
      ((2 * (a : ℝ)) * (2 * a + 2) * ((2 * (b : ℝ)) * (2 * b + 2))) *
        (2 ^ 2 * (((a : ℝ) + (0 + 1) / 2) * ((b : ℝ) + (0 + 1) / 2))) := by ring
  have hη : (1 - 1 ^ 2 / (4 * ((a : ℝ) + (0 + 1) / 2) ^ 2)) *
      (1 - 1 ^ 2 / (4 * ((b : ℝ) + (0 + 1) / 2) ^ 2)) =
      ((2 * (a : ℝ)) * (2 * a + 2) * ((2 * (b : ℝ)) * (2 * b + 2))) /
        (4 * (((a : ℝ) + (0 + 1) / 2) * ((b : ℝ) + (0 + 1) / 2))) ^ 2 := by
    have ha2 : (a : ℝ) + (0 + 1) / 2 ≠ 0 := by linarith
    have hb2 : (b : ℝ) + (0 + 1) / 2 ≠ 0 := by linarith
    rw [eta_alg _ _ ha2 hb2]
    congr 1
    ring
  rw [hη, hQ, Real.sqrt_div hP', Real.sqrt_sq (by positivity),
    Real.sqrt_mul hP', Real.sqrt_mul (show (0 : ℝ) ≤ 2 ^ 2 by norm_num),
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hsP : 0 < Real.sqrt ((2 * (a : ℝ)) * (2 * a + 2) * ((2 * (b : ℝ)) * (2 * b + 2))) := by
    apply Real.sqrt_pos.mpr
    have : 0 < 2 * (a : ℝ) := by linarith
    have : 0 < 2 * (b : ℝ) := by linarith
    positivity
  have hsAB := Real.sqrt_pos.mpr hX
  rw [Real.sqrt_mul (by linarith : (0 : ℝ) ≤ (a : ℝ) + (0 + 1) / 2)] at hsAB ⊢
  have hsa : 0 < Real.sqrt ((a : ℝ) + (0 + 1) / 2) := by
    apply Real.sqrt_pos.mpr; linarith
  have hsb : 0 < Real.sqrt ((b : ℝ) + (0 + 1) / 2) := by
    apply Real.sqrt_pos.mpr; linarith
  have ha2 : (a : ℝ) + (0 + 1) / 2 ≠ 0 := by linarith
  have hb2 : (b : ℝ) + (0 + 1) / 2 ≠ 0 := by linarith
  field_simp
  congr 1
  linear_combination (128 * Sg) * hs2 + 128 * hSg

/-- info: 'FormalResearch.Racah.SixJ.Phi6_exceptional_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_exceptional_one

/-- info: 'FormalResearch.Racah.SixJ.Phi6_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_seed

/-- info: 'FormalResearch.Racah.SixJ.Phi6_seed_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_seed_sq

/-- info: 'FormalResearch.Racah.SixJ.Phi6_exceptional_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_exceptional_zero

end FormalResearch.Racah.SixJ
