module

public import FormalResearch.Racah.P2ThreeJRec

/-!
# The one-term seed of the Regge-midpoint `3j` kernel (Weyl P2, `eq:3jseed`)

For the extremal rank `M = L`, Racah's sum has the single term `s = 0` and the kernel is a
central-factorial product:
`Φ_L^{L,σ}(x;h) = (-1)^{L-σ} √((2L)!/((L+σ)!(L-σ)!)) √(𝔠_{L+σ}(u₊,h) 𝔠_{L-σ}(u₋,h)) / √Π_L(h²)`,
`u_± = (1±x)/2`, `𝔠_r(u,h) = ∏_{q=-(r-1)/2}^{(r-1)/2} (u+qh)`, `Π_L(h²) = 𝔠_{2L+1}(1,h)`.

Dictionary: `Cprod r u h` is `𝔠_r(u,h)` for a natural number `r` (the product over
`k = 0, …, r-1` of `u + (k-(r-1)/2) h`); `Π_L(h²)` is `Cprod (2L+1) 1 h`.  To keep all
exponents natural numbers the labels enter through `p = L+σ` and `q = L-σ` (so `2L = p+q`); the
paper's sign `(-1)^{L-σ}` is `sgn (L-σ)` (`= (-1)^q`).  The lattice hypotheses are the natural
numbers `a = j_-+m_-` and `c = j_++m_+` (the other three projection combinations and the
triangle conditions are then automatic: `j_--m_- = c+q`, `j_+-m_+ = a+p`, `N-1-L = a+c`).  This
is the paper's statement exactly, on the physical lattice, with `h = 1/N`, `x = 2μ/N`.

The proof is direct from Racah's formula (the `s = 0` term).  It does not use
`threeJ_stretched`, which is the different one-term case `j₃ = j₁+j₂`.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner

/-- `𝔠_r(u,h) = ∏_{q=-(r-1)/2}^{(r-1)/2} (u+qh)`, written as a product over `k < r`. -/
noncomputable def Cprod (r : ℕ) (u h : ℝ) : ℝ :=
  ∏ k ∈ Finset.range r, (u + ((k : ℝ) - ((r : ℝ) - 1) / 2) * h)

lemma fact_mul_prod_asc (a r : ℕ) :
    (a.factorial : ℝ) * ∏ k ∈ Finset.range r, ((a : ℝ) + 1 + k) = ((a + r).factorial : ℝ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ih, show a + (r + 1) = (a + r) + 1 by ring,
      Nat.factorial_succ]
    push_cast; ring

/-- If the lowest factor of `𝔠_r(u,h)` is `(a+1)/N` and `h = 1/N`, then
`𝔠_r(u,h) = N^{-r} (a+r)!/a!`. -/
lemma Cprod_eq (r a : ℕ) (u h N : ℝ) (hN : N ≠ 0) (hh : h = 1 / N)
    (hu : u - ((r : ℝ) - 1) / 2 * h = ((a : ℝ) + 1) / N) :
    Cprod r u h = ((a + r).factorial : ℝ) / (a.factorial : ℝ) / N ^ r := by
  unfold Cprod
  have hf : ∀ k ∈ Finset.range r, (u + ((k : ℝ) - ((r : ℝ) - 1) / 2) * h) =
      ((a : ℝ) + 1 + k) / N := by
    intro k _
    have : u + ((k : ℝ) - ((r : ℝ) - 1) / 2) * h = (u - ((r : ℝ) - 1) / 2 * h) + k * h := by ring
    rw [this, hu, hh]; field_simp
  rw [Finset.prod_congr rfl hf, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range,
    ← fact_mul_prod_asc a r]
  have : (a.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- The three central-factorial products of `eq:3jseed` in closed form (`h = 1/N`, `x = 2μ/N`):
`𝔠_p(u₊,h) = N^{-p}(a+p)!/a!`, `𝔠_q(u₋,h) = N^{-q}(c+q)!/c!`,
`Π_L = 𝔠_{p+q+1}(1,h) = N^{-(p+q+1)}(a+c+p+q+1)!/(a+c)!`. -/
lemma seed_Cvalues (L σ N μ : ℚ) (p q a c : ℕ) (hp : L + σ = p) (hq : L - σ = q)
    (ha : jMinus N σ + mMinus L μ = a) (hc : jPlus N σ + mPlus L μ = c) :
    Cprod p ((1 + 2 * (μ : ℝ) / N) / 2) (1 / N) =
      ((a + p).factorial : ℝ) / (a.factorial : ℝ) / (N : ℝ) ^ p ∧
    Cprod q ((1 - 2 * (μ : ℝ) / N) / 2) (1 / N) =
      ((c + q).factorial : ℝ) / (c.factorial : ℝ) / (N : ℝ) ^ q ∧
    Cprod (p + q + 1) 1 (1 / N) =
      ((a + c + (p + q + 1)).factorial : ℝ) / ((a + c).factorial : ℝ) / (N : ℝ) ^ (p + q + 1) := by
  have hNq : N = (a : ℚ) + c + 1 + L := by
    unfold jMinus jPlus mMinus mPlus at *; linarith
  have hNpos : (0 : ℝ) < N := by
    have : (0 : ℚ) ≤ L := by linarith [(Nat.cast_nonneg p : (0 : ℚ) ≤ p), (Nat.cast_nonneg q : (0 : ℚ) ≤ q)]
    have : (0 : ℚ) < N := by
      rw [hNq]; have := (Nat.cast_nonneg a : (0 : ℚ) ≤ a); have := (Nat.cast_nonneg c : (0 : ℚ) ≤ c); linarith
    exact_mod_cast this
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hLq : L = ((p : ℚ) + q) / 2 := by linarith
  have hσq : σ = ((p : ℚ) - q) / 2 := by linarith
  have hμq : μ = ((a : ℚ) - c) / 2 + ((p : ℚ) - q) / 4 := by
    unfold jMinus jPlus mMinus mPlus at *; linarith
  have hNr : (N : ℝ) = (a : ℝ) + c + 1 + ((p : ℝ) + q) / 2 := by
    have h := hNq; rw [hLq] at h
    have := congrArg (Rat.cast : ℚ → ℝ) h
    push_cast at this
    linarith
  have hμr : (μ : ℝ) = ((a : ℝ) - c) / 2 + ((p : ℝ) - q) / 4 := by exact_mod_cast hμq
  have k1 : (N : ℝ) + 2 * μ = 2 * a + p + 1 := by rw [hNr, hμr]; ring
  have k2 : (N : ℝ) - 2 * μ = 2 * c + q + 1 := by rw [hNr, hμr]; ring
  have hCp : Cprod p ((1 + 2 * (μ : ℝ) / N) / 2) (1 / N) =
      ((a + p).factorial : ℝ) / (a.factorial : ℝ) / (N : ℝ) ^ p := by
    refine Cprod_eq p a _ _ (N : ℝ) hNne rfl ?_
    field_simp
    linear_combination k1
  have hCq : Cprod q ((1 - 2 * (μ : ℝ) / N) / 2) (1 / N) =
      ((c + q).factorial : ℝ) / (c.factorial : ℝ) / (N : ℝ) ^ q := by
    refine Cprod_eq q c _ _ (N : ℝ) hNne rfl ?_
    field_simp
    linear_combination k2
  have hCPi : Cprod (p + q + 1) 1 (1 / N) =
      ((a + c + (p + q + 1)).factorial : ℝ) / ((a + c).factorial : ℝ) / (N : ℝ) ^ (p + q + 1) := by
    refine Cprod_eq (p + q + 1) (a + c) 1 (1 / (N : ℝ)) (N : ℝ) hNne rfl ?_
    push_cast
    field_simp
    rw [hNr]; ring
  exact ⟨hCp, hCq, hCPi⟩

/-- **`eq:3jseed`** (one-term seed, `M = L`).  `p = L+σ`, `q = L-σ` and `a = j_-+m_-`,
`c = j_++m_+` are natural numbers (physical lattice); `x = 2μ/N`, `h = 1/N`. -/
theorem Phi3j_seed (L σ N μ : ℚ) (p q a c : ℕ) (hp : L + σ = p) (hq : L - σ = q)
    (ha : jMinus N σ + mMinus L μ = a) (hc : jPlus N σ + mPlus L μ = c) :
    Phi3j L L σ N μ =
      sgn (L - σ) * Real.sqrt (((p + q).factorial : ℝ) / ((p.factorial : ℝ) * q.factorial)) *
        Real.sqrt (Cprod p ((1 + 2 * (μ : ℝ) / N) / 2) (1 / N) *
          Cprod q ((1 - 2 * (μ : ℝ) / N) / 2) (1 / N)) /
        Real.sqrt (Cprod (p + q + 1) 1 (1 / N)) := by
  -- rational bookkeeping
  have e1 : L + jMinus N σ - jPlus N σ = q := by unfold jMinus jPlus; linarith
  have e2 : L - jMinus N σ + jPlus N σ = p := by unfold jMinus jPlus; linarith
  have e3 : -L + jMinus N σ + jPlus N σ = (a : ℚ) + c := by
    unfold jMinus jPlus mMinus mPlus at *; linarith
  have e4 : L + jMinus N σ + jPlus N σ + 1 = ((a + c + p + q + 1 : ℕ) : ℚ) := by
    unfold jMinus jPlus mMinus mPlus at *; push_cast; linarith
  have e5 : L + L = ((p + q : ℕ) : ℚ) := by push_cast; linarith
  have e6 : L - L = ((0 : ℕ) : ℚ) := by simp
  have e8 : jMinus N σ - mMinus L μ = ((c + q : ℕ) : ℚ) := by
    unfold jMinus jPlus mMinus mPlus at *; push_cast; linarith
  have e10 : jPlus N σ - mPlus L μ = ((a + p : ℕ) : ℚ) := by
    unfold jMinus jPlus mMinus mPlus at *; push_cast; linarith
  have hNq : N = (a : ℚ) + c + 1 + L := by
    unfold jMinus jPlus mMinus mPlus at *; linarith
  have hNpos : (0 : ℝ) < N := by
    have : (0 : ℚ) ≤ L := by linarith [(Nat.cast_nonneg p : (0 : ℚ) ≤ p), (Nat.cast_nonneg q : (0 : ℚ) ≤ q)]
    have : (0 : ℚ) < N := by
      rw [hNq]; have := (Nat.cast_nonneg a : (0 : ℚ) ≤ a); have := (Nat.cast_nonneg c : (0 : ℚ) ≤ c); linarith
    exact_mod_cast this
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  -- the magnitude `Z`
  have hm : L + mMinus L μ + mPlus L μ = 0 := by unfold mMinus mPlus; ring
  have hmsum : L + mMinus L μ + mPlus L μ = 0 := hm
  -- Racah sum
  have hsum : racahSum3 L (jMinus N σ) (jPlus N σ) L (mMinus L μ) =
      ((q.factorial : ℝ) * a.factorial * p.factorial * c.factorial)⁻¹ := by
    unfold racahSum3
    rw [finsum_eq_single _ 0]
    · unfold term3
      rw [P6_vec]
      rw [show L + jMinus N σ - jPlus N σ - ((0 : ℕ) : ℚ) = (q : ℚ) by push_cast; linarith,
        show L - L - ((0 : ℕ) : ℚ) = ((0 : ℕ) : ℚ) by simp,
        show jMinus N σ + mMinus L μ - ((0 : ℕ) : ℚ) = (a : ℚ) by push_cast; linarith,
        show jPlus N σ - jMinus N σ + L + ((0 : ℕ) : ℚ) = (p : ℚ) by
          unfold jMinus jPlus; push_cast; linarith,
        show jPlus N σ - L - mMinus L μ + ((0 : ℕ) : ℚ) = (c : ℚ) by
          unfold jMinus jPlus mMinus mPlus at *; push_cast; linarith]
      simp only [Nat.cast_zero, ifa_zero, ifa_natCast, pow_zero]
      field_simp
    · intro s hs
      unfold term3
      rw [P6_vec]
      have : ifa (L - L - (s : ℚ)) = 0 := by
        apply ifa_eq_zero_of_neg
        have : (1 : ℚ) ≤ s := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hs
        linarith
      rw [this]; simp
  -- the sign
  have hsg : sgn (2 * L + jPlus N σ + mPlus L μ) * sgn (L - jMinus N σ - mPlus L μ) =
      sgn (L - σ) := by
    have s1 : 2 * L + jPlus N σ + mPlus L μ = (((p + q + c : ℕ) : ℤ) : ℚ) := by
      push_cast; unfold jMinus jPlus mMinus mPlus at *; linarith
    have s2 : L - jMinus N σ - mPlus L μ = ((((p : ℤ) - c : ℤ)) : ℚ) := by
      push_cast; unfold jMinus jPlus mMinus mPlus at *; linarith
    have s3 : L - σ = ((q : ℤ) : ℚ) := by push_cast; linarith
    rw [s1, s2, s3, sgn_intCast, sgn_intCast, sgn_intCast, ← zpow_add₀ (by norm_num)]
    have : (((p + q + c : ℕ) : ℤ) + ((p : ℤ) - c)) = (q : ℤ) + 2 * (p : ℤ) := by push_cast; ring
    rw [this, neg_one_zpow_add_two_mul]
  -- unfold Φ and the 3j
  unfold Phi3j
  rw [threeJ_factor hm, hsum]
  have f1 : fq (L + L) = ((p + q).factorial : ℝ) := by rw [e5, fq_natCast]
  have f2 : fq (L - L) = 1 := by rw [e6, fq_natCast]; simp
  have f3 : fq (jMinus N σ + mMinus L μ) = (a.factorial : ℝ) := by rw [ha, fq_natCast]
  have f4 : fq (jMinus N σ - mMinus L μ) = ((c + q).factorial : ℝ) := by rw [e8, fq_natCast]
  have f5 : fq (jPlus N σ + mPlus L μ) = (c.factorial : ℝ) := by rw [hc, fq_natCast]
  have f6 : fq (jPlus N σ - mPlus L μ) = ((a + p).factorial : ℝ) := by rw [e10, fq_natCast]
  have tri : triSq L (jMinus N σ) (jPlus N σ) =
      (q.factorial : ℝ) * p.factorial * ((a + c).factorial : ℝ) /
        ((a + c + p + q + 1).factorial : ℝ) := by
    unfold triSq
    rw [e1, e2, show -L + jMinus N σ + jPlus N σ = ((a + c : ℕ) : ℚ) by push_cast; exact e3, e4,
      fq_natCast, fq_natCast, fq_natCast, ifa_natCast]
    field_simp
  rw [f1, f2, f3, f4, f5, f6, tri]
  obtain ⟨hCp, hCq, hCPi⟩ := seed_Cvalues L σ N μ p q a c hp hq ha hc
  rw [hCp, hCq, hCPi]
  have hidx : a + c + (p + q + 1) = a + c + p + q + 1 := by ring
  rw [hidx]
  have hAB : Real.sqrt (N : ℝ) *
      ((Real.sqrt ((q.factorial : ℝ) * p.factorial * ((a + c).factorial : ℝ) /
          ((a + c + p + q + 1).factorial : ℝ)) * Real.sqrt (((p + q).factorial : ℝ) * 1)) *
        Real.sqrt ((a.factorial : ℝ) * ((c + q).factorial : ℝ) * (c.factorial : ℝ) *
          ((a + p).factorial : ℝ)) *
        ((q.factorial : ℝ) * a.factorial * p.factorial * c.factorial)⁻¹) =
      Real.sqrt (((p + q).factorial : ℝ) / ((p.factorial : ℝ) * q.factorial)) *
        Real.sqrt (((a + p).factorial : ℝ) / (a.factorial : ℝ) / (N : ℝ) ^ p *
          (((c + q).factorial : ℝ) / (c.factorial : ℝ) / (N : ℝ) ^ q)) /
        Real.sqrt (((a + c + p + q + 1).factorial : ℝ) / ((a + c).factorial : ℝ) /
          (N : ℝ) ^ (p + q + 1)) := by
    have hpos : ∀ n : ℕ, (0 : ℝ) < (n.factorial : ℝ) := fun n => by positivity
    have h1 := hpos a
    have h2 := hpos c
    have h3 := hpos p
    have h4 := hpos q
    have h5 := hpos (a + c)
    have h6 := hpos (a + c + p + q + 1)
    have h7 := hpos (p + q)
    have h8 := hpos (a + p)
    have h9 := hpos (c + q)
    have hP : 0 < (N : ℝ) := hNpos
    apply (pow_left_inj₀ (by positivity) (by positivity) (two_ne_zero)).mp
    simp only [mul_pow, div_pow]
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    rw [pow_succ, pow_add]
    field_simp
    ring
  rw [← hsg]
  linear_combination (sgn (2 * L + jPlus N σ + mPlus L μ) * sgn (L - jMinus N σ - mPlus L μ)) * hAB

/-- info: 'FormalResearch.Racah.Phi3j_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_seed

/-! ### The central factorials are even in `h` and `Π_L` -/

lemma Cprod_zero (u h : ℝ) : Cprod 0 u h = 1 := by simp [Cprod]

lemma Cprod_one (u h : ℝ) : Cprod 1 u h = u := by simp [Cprod]

/-- Peeling the two extreme factors: `𝔠_{r+2}(u,h) = (u²-((r+1)h/2)²) 𝔠_r(u,h)`. -/
lemma Cprod_succ_succ (r : ℕ) (u h : ℝ) :
    Cprod (r + 2) u h = (u ^ 2 - (((r : ℝ) + 1) / 2 * h) ^ 2) * Cprod r u h := by
  unfold Cprod
  rw [Finset.prod_range_succ, Finset.prod_range_succ']
  have hf : ∀ k ∈ Finset.range r,
      (u + (((k + 1 : ℕ) : ℝ) - (((r + 2 : ℕ) : ℝ) - 1) / 2) * h) =
        (u + ((k : ℝ) - ((r : ℝ) - 1) / 2) * h) := by
    intro k _; push_cast; ring
  rw [Finset.prod_congr rfl hf]
  push_cast
  ring

/-- **`lem:centeredshift`-type evenness**: the central factorial `𝔠_r(u,h)` is exactly even in
`h` (the set of `q` values is symmetric). -/
lemma Cprod_neg (r : ℕ) (u h : ℝ) : Cprod r u (-h) = Cprod r u h := by
  unfold Cprod
  rw [← Finset.prod_range_reflect (fun k : ℕ => u + ((k : ℝ) - ((r : ℝ) - 1) / 2) * h) r]
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk' : k < r := Finset.mem_range.mp hk
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

/-- `eq:3jPiL`, integer `L = m`: `𝔠_{2m+1}(1,h) = ∏_{k=1}^{m} (1 - k²h²)`. -/
lemma Cprod_one_odd (m : ℕ) (h : ℝ) :
    Cprod (2 * m + 1) 1 h = ∏ k ∈ Finset.range m, (1 - (((k : ℝ) + 1) * h) ^ 2) := by
  induction m with
  | zero => simp [Cprod_one]
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, Cprod_succ_succ, ih,
      Finset.prod_range_succ, mul_comm]
    congr 1
    push_cast
    ring_nf

/-- `eq:3jPiL`, half-integer `L = m - 1/2`: `𝔠_{2m}(1,h) = ∏_{k=1}^{m} (1 - ((2k-1)h/2)²)`, i.e.
`∏_{q=1/2}^{L}(1-q²h²)`. -/
lemma Cprod_one_even (m : ℕ) (h : ℝ) :
    Cprod (2 * m) 1 h =
      ∏ k ∈ Finset.range m, (1 - ((((k : ℝ) + 1) - 1 / 2) * h) ^ 2) := by
  induction m with
  | zero => simp [Cprod_zero]
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m) + 2 by ring, Cprod_succ_succ, ih,
      Finset.prod_range_succ, mul_comm]
    congr 1
    push_cast
    ring_nf

/-- info: 'FormalResearch.Racah.Cprod_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cprod_neg

/-- info: 'FormalResearch.Racah.Cprod_one_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cprod_one_odd

/-- info: 'FormalResearch.Racah.Cprod_one_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cprod_one_even

end FormalResearch.Racah
