module

public import FormalResearch.Racah.P2RacahSystemSpec
public import FormalResearch.Racah.P2RacahSeed

/-!
# The stretched seed along the `c`-lattice: shift identity and positivity (Weyl P2, `lem:6jseed`,
`eq:physicalRacahweight`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `eq:6jseed`, `eq:physicalRacahweight`.

For the stretched seed `Φ_m(c)² = 𝒮_m(A,B,c+1/2)` (`Phi6_seed_sq`), the dependence on `c` is through
four central Pochhammer products `𝔆_r(X)`, and one lattice step multiplies each by an explicit linear
factor.  With `r₁ = m-n`, `r₂ = m+n`, `A = a+(n+1)/2`, `B = b+(m+1)/2` this gives, in the original
labels,

* `seedS_shift` / `Phi6_seed_step`:
  `Φ_m(c+1)² · D₁(c) = Φ_m(c)² · N₁(c)` with
  `N₁(c) = (a-b+c+1)(b+m-a-n+c+1)(a+b-c)(a+b+m+n+c+2)` (`seedN`),
  `D₁(c) = (a-b-m+n+c+1)(b-a+c+1)(a+b+m+n-c)(a+b+c+2)` (`seedD`);
* `Phi6_seed_pos`: `Φ_m(c) > 0` at every physical `c` (the positivity of `lem:6jseed` in the form used
  by `eq:physicalRacahweight`); `seedN_pos`, `seedD_pos`: the two products are positive when `c`
  and `c+1` are both physical.
-/

@[expose] public section

namespace FormalResearch.Racah.SixJ

open FormalResearch.Wigner

lemma prod_shift (b : ℝ) (r : ℕ) :
    (∏ k ∈ Finset.range r, (b + k)) * (b + r) = b * ∏ k ∈ Finset.range r, (b + 1 + k) := by
  have h1 := Finset.prod_range_succ (fun k : ℕ => b + (k : ℝ)) r
  have h2 := Finset.prod_range_succ' (fun k : ℕ => b + (k : ℝ)) r
  rw [h1] at h2
  rw [h2, mul_comm]
  simp only [Nat.cast_zero, add_zero]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  push_cast; ring

/-- One step up in the argument of `𝔆_r`: `𝔆_r(X+1)(X-(r-1)/2) = 𝔆_r(X)(X+(r+1)/2)`. -/
lemma cenProd_up (r : ℕ) (X : ℝ) :
    cenProd r (X + 1) * (X - ((r : ℝ) - 1) / 2) = cenProd r X * (X + ((r : ℝ) + 1) / 2) := by
  have := prod_shift (X - ((r : ℝ) - 1) / 2) r
  unfold cenProd
  have e1 : ∏ k ∈ Finset.range r, (X + 1 - ((r : ℝ) - 1) / 2 + k) =
      ∏ k ∈ Finset.range r, (X - ((r : ℝ) - 1) / 2 + 1 + k) :=
    Finset.prod_congr rfl fun k _ => by ring
  rw [e1, mul_comm, ← this]
  ring_nf

/-- One step down: `𝔆_r(X-1)(X+(r-1)/2) = 𝔆_r(X)(X-(r+1)/2)`. -/
lemma cenProd_down (r : ℕ) (X : ℝ) :
    cenProd r (X - 1) * (X + ((r : ℝ) - 1) / 2) = cenProd r X * (X - ((r : ℝ) + 1) / 2) := by
  have := prod_shift (X - ((r : ℝ) - 1) / 2 - 1) r
  unfold cenProd
  have e1 : ∏ k ∈ Finset.range r, (X - 1 - ((r : ℝ) - 1) / 2 + k) =
      ∏ k ∈ Finset.range r, (X - ((r : ℝ) - 1) / 2 - 1 + k) :=
    Finset.prod_congr rfl fun k _ => by ring
  have e2 : ∏ k ∈ Finset.range r, (X - ((r : ℝ) - 1) / 2 - 1 + 1 + k) =
      ∏ k ∈ Finset.range r, (X - ((r : ℝ) - 1) / 2 + k) :=
    Finset.prod_congr rfl fun k _ => by ring
  rw [e2] at this
  rw [e1]
  have e3 : X - ((r : ℝ) - 1) / 2 - 1 + r = X + ((r : ℝ) - 1) / 2 := by ring
  rw [e3] at this
  rw [this]; ring

/-- The four linear factors by which `𝒮_m(A,B,C+1)` exceeds `𝒮_m(A,B,C)` (numerator part) -/
noncomputable def shiftN (r₁ r₂ A B C : ℝ) : ℝ :=
  (A - B + C + (r₁ + 1) / 2) * (-A + B + C + (r₁ + 1) / 2) * (A + B - C - (r₂ + 1) / 2) *
    (A + B + C + (r₂ + 1) / 2)

/-- ... and the denominator part. -/
noncomputable def shiftD (r₁ r₂ A B C : ℝ) : ℝ :=
  (A - B + C - (r₁ - 1) / 2) * (-A + B + C - (r₁ - 1) / 2) * (A + B - C + (r₂ - 1) / 2) *
    (A + B + C - (r₂ - 1) / 2)

/-- `𝒮_m(A,B,C+1) D = 𝒮_m(A,B,C) N`: the lattice step of the seed (`eq:6jseed`), with
`r₁ = ⌊m-n⌋₊`, `r₂ = ⌊m+n⌋₊`. -/
theorem seedS_shift (m n : ℚ) (A B C : ℝ) :
    seedS m n A B (C + 1) * shiftD (⌊m - n⌋₊ : ℝ) (⌊m + n⌋₊ : ℝ) A B C =
      seedS m n A B C * shiftN (⌊m - n⌋₊ : ℝ) (⌊m + n⌋₊ : ℝ) A B C := by
  have u1 := cenProd_up ⌊m - n⌋₊ (A - B + C)
  have u2 := cenProd_up ⌊m - n⌋₊ (-A + B + C)
  have d3 := cenProd_down ⌊m + n⌋₊ (A + B - C)
  have u4 := cenProd_up ⌊m + n⌋₊ (A + B + C)
  have key : (cenProd ⌊m - n⌋₊ (A - B + C + 1) * (A - B + C - ((⌊m - n⌋₊ : ℝ) - 1) / 2)) *
      (cenProd ⌊m - n⌋₊ (-A + B + C + 1) * (-A + B + C - ((⌊m - n⌋₊ : ℝ) - 1) / 2)) *
      (cenProd ⌊m + n⌋₊ (A + B - C - 1) * (A + B - C + ((⌊m + n⌋₊ : ℝ) - 1) / 2)) *
      (cenProd ⌊m + n⌋₊ (A + B + C + 1) * (A + B + C - ((⌊m + n⌋₊ : ℝ) - 1) / 2)) =
      (cenProd ⌊m - n⌋₊ (A - B + C) * (A - B + C + ((⌊m - n⌋₊ : ℝ) + 1) / 2)) *
      (cenProd ⌊m - n⌋₊ (-A + B + C) * (-A + B + C + ((⌊m - n⌋₊ : ℝ) + 1) / 2)) *
      (cenProd ⌊m + n⌋₊ (A + B - C) * (A + B - C - ((⌊m + n⌋₊ : ℝ) + 1) / 2)) *
      (cenProd ⌊m + n⌋₊ (A + B + C) * (A + B + C + ((⌊m + n⌋₊ : ℝ) + 1) / 2)) := by
    rw [u1, u2, d3, u4]
  have e1 : A - B + (C + 1) = A - B + C + 1 := by ring
  have e2 : -A + B + (C + 1) = -A + B + C + 1 := by ring
  have e3 : A + B - (C + 1) = A + B - C - 1 := by ring
  have e4 : A + B + (C + 1) = A + B + C + 1 := by ring
  unfold seedS shiftN shiftD
  rw [e1, e2, e3, e4]
  linear_combination
    (((Nat.choose ⌊2 * m⌋₊ ⌊m + n⌋₊ : ℕ) : ℝ) * chiM m A B / (dProd m A * dProd m B)) * key

/-! ### Positivity on the physical lattice -/

lemma floor_isNat {x : ℚ} (h : IsNat x) : ((⌊x⌋₊ : ℕ) : ℝ) = (x : ℝ) := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.floor_natCast]; simp

/-- The three nonnegative combinations of a triad, as real inequalities. -/
lemma tri_nonneg {x y z : ℚ} (h : IsTri x y z) :
    0 ≤ (x : ℝ) + y - z ∧ 0 ≤ (x : ℝ) - y + z ∧ 0 ≤ -(x : ℝ) + y + z := by
  obtain ⟨h1, h2, h3⟩ := h
  have a1 := h1.nonneg_real
  have a2 := h2.nonneg_real
  have a3 := h3.nonneg_real
  push_cast at a1 a2 a3
  exact ⟨a1, a2, by linarith⟩

lemma cenProd_pos (r : ℕ) (X : ℝ) (h : 0 < X - ((r : ℝ) - 1) / 2) : 0 < cenProd r X := by
  unfold cenProd
  refine Finset.prod_pos fun k _ => ?_
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

lemma dProd_pos (m : ℚ) (X : ℝ) (hm : (m : ℝ) < 2 * X) : 0 < dProd m X := by
  unfold dProd
  refine Finset.prod_pos fun k hk => ?_
  have hk' : (k : ℚ) < m := Nat.lt_ceil.1 (Finset.mem_range.1 hk)
  have hk'' : (k : ℝ) < m := by exact_mod_cast hk'
  have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

/-- **`lem:6jseed`, positivity**: `𝒮_m(A,B,C) > 0` at every physical point, so that the stretched seed
`Φ_m(c) = √𝒮_m` is strictly positive on the whole lattice. -/
theorem seedS_pos (a b c m n : ℚ) (h1 : IsTri m (b + m) b) (h2 : IsTri m a (a + n))
    (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n)) :
    0 < seedS m n (wA a n) (wB b m) (wC c) := by
  obtain ⟨t1, t2, t3⟩ := tri_nonneg h1
  obtain ⟨s1, s2, s3⟩ := tri_nonneg h2
  obtain ⟨u1, u2, u3⟩ := tri_nonneg h3
  obtain ⟨v1, v2, v3⟩ := tri_nonneg h4
  push_cast at t1 t2 t3 s1 s2 s3 u1 u2 u3 v1 v2 v3
  have hmn : IsNat (m - n) := by
    obtain ⟨x, -, -⟩ := h2; obtain ⟨y, hy⟩ := x; exact ⟨y, by linarith⟩
  have hpn : IsNat (m + n) := by
    obtain ⟨-, x, -⟩ := h2; obtain ⟨y, hy⟩ := x; exact ⟨y, by linarith⟩
  have fm := floor_isNat hmn
  have fp := floor_isNat hpn
  push_cast at fm fp
  have hA : 0 < wA a n := by unfold wA; linarith
  have hB : 0 < wB b m := by unfold wB; linarith
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hc : 0 < ((Nat.choose ⌊2 * m⌋₊ ⌊m + n⌋₊ : ℕ) : ℝ) := by
    have : ⌊m + n⌋₊ ≤ ⌊2 * m⌋₊ := Nat.floor_le_floor (by linarith [(show (n : ℚ) ≤ m by
      have : (0 : ℝ) ≤ (m : ℝ) - n := by linarith
      exact_mod_cast (by linarith : (n : ℝ) ≤ m))])
    exact_mod_cast Nat.choose_pos this
  have hchi : 0 < chiM m (wA a n) (wB b m) := by
    unfold chiM; split_ifs
    · exact one_pos
    · have := mul_pos hA hB; linarith
  have hdA : 0 < dProd m (wA a n) := dProd_pos m _ (by unfold wA; linarith)
  have hdB : 0 < dProd m (wB b m) := dProd_pos m _ (by unfold wB; linarith)
  have c1 : 0 < cenProd ⌊m - n⌋₊ (wA a n - wB b m + wC c) :=
    cenProd_pos _ _ (by rw [fm]; unfold wA wB wC; linarith)
  have c2 : 0 < cenProd ⌊m - n⌋₊ (-wA a n + wB b m + wC c) :=
    cenProd_pos _ _ (by rw [fm]; unfold wA wB wC; linarith)
  have c3 : 0 < cenProd ⌊m + n⌋₊ (wA a n + wB b m - wC c) :=
    cenProd_pos _ _ (by rw [fp]; unfold wA wB wC; linarith)
  have c4 : 0 < cenProd ⌊m + n⌋₊ (wA a n + wB b m + wC c) :=
    cenProd_pos _ _ (by rw [fp]; unfold wA wB wC; linarith)
  unfold seedS
  exact mul_pos (mul_pos (mul_pos (mul_pos (div_pos (mul_pos hc hchi) (mul_pos hdA hdB)) c1) c2) c3) c4

/-! ### The lattice step of the seed in the original labels -/

/-- `N₁(c) = (a-b+c+1)(b+m-a-n+c+1)(a+b-c)(a+b+m+n+c+2)`. -/
noncomputable def seedN (a b m n c : ℝ) : ℝ :=
  (a - b + c + 1) * (b + m - a - n + c + 1) * (a + b - c) * (a + b + m + n + c + 2)

/-- `D₁(c) = (a-b-m+n+c+1)(b-a+c+1)(a+b+m+n-c)(a+b+c+2)`. -/
noncomputable def seedD (a b m n c : ℝ) : ℝ :=
  (a - b - m + n + c + 1) * (b - a + c + 1) * (a + b + m + n - c) * (a + b + c + 2)

/-- `E(c+1)² = N₁(c) D₁(c)` for the edge factor of `eq:Racahcedgefactor`. -/
theorem edgeA2_succ_eq (a b m n c : ℝ) :
    edgeA2 a b m n (c + 1) = seedN a b m n c * seedD a b m n c := by
  unfold edgeA2 seedN seedD; ring

/-- **The lattice step of the stretched seed**: if `c` and `c+1` are physical,
`Φ_m(c+1)² D₁(c) = Φ_m(c)² N₁(c)`. -/
theorem Phi6_seed_step (a b c m n : ℚ) (h1 : IsTri m (b + m) b) (h2 : IsTri m a (a + n))
    (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n))
    (h3' : IsTri (c + 1) a b) (h4' : IsTri (c + 1) (b + m) (a + n)) :
    Phi6 a b (c + 1) m m n ^ 2 * seedD a b m n c = Phi6 a b c m m n ^ 2 * seedN a b m n c := by
  have hmn : IsNat (m - n) := by
    obtain ⟨x, -, -⟩ := h2; obtain ⟨y, hy⟩ := x; exact ⟨y, by linarith⟩
  have hpn : IsNat (m + n) := by
    obtain ⟨-, x, -⟩ := h2; obtain ⟨y, hy⟩ := x; exact ⟨y, by linarith⟩
  have fm := floor_isNat hmn
  have fp := floor_isNat hpn
  push_cast at fm fp
  rw [(Phi6_seed_sq a b c m n h1 h2 h3 h4).2, (Phi6_seed_sq a b (c + 1) m n h1 h2 h3' h4').2]
  have hC : wC (c + 1) = wC c + 1 := by unfold wC; push_cast; ring
  rw [hC]
  have := seedS_shift m n (wA a n) (wB b m) (wC c)
  rw [fm, fp] at this
  have e1 : shiftN ((m : ℝ) - n) ((m : ℝ) + n) (wA a n) (wB b m) (wC c) =
      seedN a b m n c := by unfold shiftN seedN wA wB wC; ring
  have e2 : shiftD ((m : ℝ) - n) ((m : ℝ) + n) (wA a n) (wB b m) (wC c) =
      seedD a b m n c := by unfold shiftD seedD wA wB wC; ring
  rw [e1, e2] at this
  exact this

/-- `N₁(c) > 0` when `c` and `c+1` are physical. -/
theorem seedN_pos (a b c m n : ℚ) (h2 : IsTri m a (a + n))
    (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n))
    (h3' : IsTri (c + 1) a b) (h4' : IsTri (c + 1) (b + m) (a + n)) :
    0 < seedN a b m n c := by
  obtain ⟨s1, s2, s3⟩ := tri_nonneg h2
  obtain ⟨u1, u2, u3⟩ := tri_nonneg h3
  obtain ⟨v1, v2, v3⟩ := tri_nonneg h4
  obtain ⟨u1', u2', u3'⟩ := tri_nonneg h3'
  obtain ⟨v1', v2', v3'⟩ := tri_nonneg h4'
  push_cast at s1 s2 s3 u1 u2 u3 v1 v2 v3 u1' u2' u3' v1' v2' v3'
  unfold seedN
  refine mul_pos (mul_pos (mul_pos ?_ ?_) ?_) ?_ <;> linarith

/-- `D₁(c) > 0` when `c` and `c+1` are physical. -/
theorem seedD_pos (a b c m n : ℚ) (h2 : IsTri m a (a + n))
    (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n))
    (h3' : IsTri (c + 1) a b) (h4' : IsTri (c + 1) (b + m) (a + n)) :
    0 < seedD a b m n c := by
  obtain ⟨s1, s2, s3⟩ := tri_nonneg h2
  obtain ⟨u1, u2, u3⟩ := tri_nonneg h3
  obtain ⟨v1, v2, v3⟩ := tri_nonneg h4
  obtain ⟨u1', u2', u3'⟩ := tri_nonneg h3'
  obtain ⟨v1', v2', v3'⟩ := tri_nonneg h4'
  push_cast at s1 s2 s3 u1 u2 u3 v1 v2 v3 u1' u2' u3' v1' v2' v3'
  unfold seedD
  refine mul_pos (mul_pos (mul_pos ?_ ?_) ?_) ?_ <;> linarith

/-- `Φ_m(c) > 0` at every physical `c`. -/
theorem Phi6_seed_pos (a b c m n : ℚ) (h1 : IsTri m (b + m) b) (h2 : IsTri m a (a + n))
    (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n)) : 0 < Phi6 a b c m m n := by
  obtain ⟨h0, hsq⟩ := Phi6_seed_sq a b c m n h1 h2 h3 h4
  have hp := seedS_pos a b c m n h1 h2 h3 h4
  rcases h0.lt_or_eq with h | h
  · exact h
  · rw [← h] at hsq; simp at hsq; linarith

/-! ### The two off-diagonal ratios of the seed -/

lemma edgeA_succ_sq (a b c m n : ℚ) (h2 : IsTri m a (a + n))
    (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n))
    (h3' : IsTri (c + 1) a b) (h4' : IsTri (c + 1) (b + m) (a + n)) :
    edgeA a b m n ((c : ℝ) + 1) ^ 2 = seedN a b m n c * seedD a b m n c := by
  have hN := seedN_pos a b c m n h2 h3 h4 h3' h4'
  have hD := seedD_pos a b c m n h2 h3 h4 h3' h4'
  unfold edgeA
  rw [Real.sq_sqrt, edgeA2_succ_eq]
  rw [edgeA2_succ_eq]; exact (mul_pos hN hD).le

/-- **Upper ratio of the seed**: `a_c^+ Φ_m(c+1) = N₁(c)/((2c+1)(2c+2)) Φ_m(c)` for `c, c+1` physical. -/
theorem aPlus_mul_seed (a b c m n : ℚ) (h1 : IsTri m (b + m) b) (h2 : IsTri m a (a + n))
    (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n))
    (h3' : IsTri (c + 1) a b) (h4' : IsTri (c + 1) (b + m) (a + n)) :
    aPlus a b m n (c : ℝ) * Phi6 a b (c + 1) m m n =
      seedN a b m n c / ((2 * (c : ℝ) + 1) * (2 * (c : ℝ) + 2)) * Phi6 a b c m m n := by
  have hN := seedN_pos a b c m n h2 h3 h4 h3' h4'
  have hD := seedD_pos a b c m n h2 h3 h4 h3' h4'
  have hc0 : (0 : ℝ) ≤ c := by
    obtain ⟨u1, u2, -⟩ := tri_nonneg h3; linarith
  have P0 := Phi6_seed_pos a b c m n h1 h2 h3 h4
  have P1 := Phi6_seed_pos a b (c + 1) m n h1 h2 h3' h4'
  have step := Phi6_seed_step a b c m n h1 h2 h3 h4 h3' h4'
  have hE := edgeA_succ_sq a b c m n h2 h3 h4 h3' h4'
  have hden : 0 < 2 * (2 * (c : ℝ) + 1) * ((c : ℝ) + 1) := by positivity
  have hX : 0 ≤ aPlus a b m n (c : ℝ) * Phi6 a b (c + 1) m m n := by
    unfold aPlus
    exact mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hden.le) P1.le
  have hY : 0 ≤ seedN a b m n c / ((2 * (c : ℝ) + 1) * (2 * (c : ℝ) + 2)) * Phi6 a b c m m n := by
    positivity
  refine (sq_eq_sq₀ hX hY).1 ?_
  have e1 : aPlus a b m n (c : ℝ) ^ 2 = seedN a b m n c * seedD a b m n c /
      (2 * (2 * (c : ℝ) + 1) * ((c : ℝ) + 1)) ^ 2 := by
    unfold aPlus; rw [div_pow, hE]
  rw [mul_pow, e1]
  simp only [mul_pow, div_pow]
  have h2c : (2 * (c : ℝ) + 1) ≠ 0 := by positivity
  have h2c' : (2 * (c : ℝ) + 2) ≠ 0 := by positivity
  have h1c : ((c : ℝ) + 1) ≠ 0 := by positivity
  have hDne : seedD a b m n c ≠ 0 := hD.ne'
  have hP1 : Phi6 a b (c + 1) m m n ^ 2 =
      Phi6 a b c m m n ^ 2 * seedN a b m n c / seedD a b m n c := by
    rw [eq_div_iff hDne]; exact_mod_cast step
  rw [hP1]
  field_simp

/-- **Lower ratio of the seed**: `a_{c+1}^- Φ_m(c) = D₁(c)/((2c+2)(2c+3)) Φ_m(c+1)` for `c, c+1` physical. -/
theorem aMinus_mul_seed (a b c m n : ℚ) (h1 : IsTri m (b + m) b) (h2 : IsTri m a (a + n))
    (h3 : IsTri c a b) (h4 : IsTri c (b + m) (a + n))
    (h3' : IsTri (c + 1) a b) (h4' : IsTri (c + 1) (b + m) (a + n)) :
    aMinus a b m n ((c : ℝ) + 1) * Phi6 a b c m m n =
      seedD a b m n c / ((2 * (c : ℝ) + 2) * (2 * (c : ℝ) + 3)) * Phi6 a b (c + 1) m m n := by
  have hN := seedN_pos a b c m n h2 h3 h4 h3' h4'
  have hD := seedD_pos a b c m n h2 h3 h4 h3' h4'
  have hc0 : (0 : ℝ) ≤ c := by
    obtain ⟨u1, u2, -⟩ := tri_nonneg h3; linarith
  have P0 := Phi6_seed_pos a b c m n h1 h2 h3 h4
  have P1 := Phi6_seed_pos a b (c + 1) m n h1 h2 h3' h4'
  have step := Phi6_seed_step a b c m n h1 h2 h3 h4 h3' h4'
  have hE := edgeA_succ_sq a b c m n h2 h3 h4 h3' h4'
  have hden : 0 < 2 * (2 * ((c : ℝ) + 1) + 1) * ((c : ℝ) + 1) := by positivity
  have hX : 0 ≤ aMinus a b m n ((c : ℝ) + 1) * Phi6 a b c m m n := by
    unfold aMinus
    exact mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hden.le) P0.le
  have hY : 0 ≤ seedD a b m n c / ((2 * (c : ℝ) + 2) * (2 * (c : ℝ) + 3)) * Phi6 a b (c + 1) m m n := by
    positivity
  refine (sq_eq_sq₀ hX hY).1 ?_
  have e1 : aMinus a b m n ((c : ℝ) + 1) ^ 2 = seedN a b m n c * seedD a b m n c /
      (2 * (2 * ((c : ℝ) + 1) + 1) * ((c : ℝ) + 1)) ^ 2 := by
    unfold aMinus; rw [div_pow, hE]
  rw [mul_pow, e1]
  simp only [mul_pow, div_pow]
  have h2c : (2 * (c : ℝ) + 3) ≠ 0 := by positivity
  have h2c' : (2 * (c : ℝ) + 2) ≠ 0 := by positivity
  have h1c : ((c : ℝ) + 1) ≠ 0 := by positivity
  have hNne : seedN a b m n c ≠ 0 := hN.ne'
  have hP0 : Phi6 a b c m m n ^ 2 =
      Phi6 a b (c + 1) m m n ^ 2 * seedD a b m n c / seedN a b m n c := by
    rw [eq_div_iff hNne]; exact_mod_cast step.symm
  rw [hP0]
  field_simp
  ring

/-- info: 'FormalResearch.Racah.SixJ.Phi6_seed_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_seed_step

/-- info: 'FormalResearch.Racah.SixJ.Phi6_seed_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_seed_pos

/-- info: 'FormalResearch.Racah.SixJ.aPlus_mul_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aPlus_mul_seed

/-- info: 'FormalResearch.Racah.SixJ.aMinus_mul_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aMinus_mul_seed

end FormalResearch.Racah.SixJ
