module

public import FormalResearch.Racah.P2ThreeJRecAll

/-!
# The Regge-midpoint `3j` kernel: exact rank and magnetic recurrences (Weyl P2)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, sections *Variables and the exact even
theorem* and *Exact finite-difference equation and the first correction*.

## Dictionary (paper symbol -> Lean symbol)

All labels are rational numbers (so integer and half-integer spins are treated uniformly); the
real numbers `h = 1/N`, `x = 2μ/N` are the casts.

| paper | Lean |
|---|---|
| `L, M, σ`, `N = 2ℓ+1`, `μ` | `L M σ N μ : ℚ` |
| `j_∓ = (N-1∓σ)/2` | `jMinus N σ`, `jPlus N σ` |
| `m_- = μ - M/2`, `m_+ = -μ - M/2` | `mMinus M μ`, `mPlus M μ` |
| `Φ_L^{M,σ}(x;h) = (-1)^{2L+j_++m_+} √N (L j_- j_+; M m_- m_+)` | `Phi3j L M σ N μ` |
| `Φ_L^{M,σ}(x;1/N)` as a function of `x` (`μ = N x/2`) | `PhiX L M σ N x` |
| `R_k = √((k²-M²)(k²-σ²))` | `Rk M σ k` |
| `a_k^{(N)} = a_k^{(0)} √(1-k²/N²)`, `a_k^{(0)} = R_k/k` | `aRank M σ N k` |
| `a_h(y)` of `eq:ah3` | `aMid M σ N y` (with `h = 1/N`) |

`sgn` is the zero-extended sign of the library (`(-1)^n` for integer `n`, `0` otherwise); the
exponent `2L+j_++m_+` is an integer in every case the paper treats, so on the paper's domain
`Phi3j` is exactly `(-1)^{2L+j_++m_+} √N (3j)`.  Off that domain `Phi3j` is `0` (the paper's
convention that the kernel vanishes off the physical lattice).

## Results

* `Phi3j_rank_recurrence`: `eq:3jrank`, exactly the paper's statement, at every admissible rank
  `L` (including the end rows `L = L_0` and `L = N-1`, where the missing neighbour is `0`).
* `Phi3j_rank_jacobi`: `eq:rankJacobiForm` (`obs:rankJacobi`), the same after division by `L(L+1)`.
* `PhiX_midpoint_diff`: `eq:3jdiff`, the exact finite-difference equation, at every point `x`
  of the physical lattice (including the two boundary rows, where `a_h(x±h) = 0` removes the
  missing neighbour).
* `aMid_*`: the algebra of `a_h` (evenness in `h`, the boundary zeros used in `thm:3jspectral`).

The rank recurrence is DLMF 34.3.15 (`threeJ_recurrence`) and the magnetic one is DLMF 34.3.14
(`threeJ_recurrence_m`), here in the all-rows forms `threeJ_recurrence_all`,
`threeJ_recurrence_m_all` (`P2ThreeJRecAll.lean`); this file only does the change of variables.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner

/-- `j_- = (N-1-σ)/2`. -/
def jMinus (N σ : ℚ) : ℚ := (N - 1 - σ) / 2
/-- `j_+ = (N-1+σ)/2`. -/
def jPlus (N σ : ℚ) : ℚ := (N - 1 + σ) / 2
/-- `m_- = μ - M/2`. -/
def mMinus (M μ : ℚ) : ℚ := μ - M / 2
/-- `m_+ = -μ - M/2`. -/
def mPlus (M μ : ℚ) : ℚ := -μ - M / 2

/-- The Regge-midpoint kernel `Φ_L^{M,σ}` of `eq:3jPhi`, as a function of the rational
magnetic parameter `μ` (so `x = 2μ/N`, `h = 1/N`). -/
noncomputable def Phi3j (L M σ N μ : ℚ) : ℝ :=
  sgn (2 * L + jPlus N σ + mPlus M μ) * Real.sqrt (N : ℝ) *
    threeJ L (jMinus N σ) (jPlus N σ) M (mMinus M μ) (mPlus M μ)

/-- `Φ_L^{M,σ}(x; 1/N)` as a function of the midpoint coordinate `x = 2μ/N`. -/
noncomputable def PhiX (L M σ N x : ℚ) : ℝ := Phi3j L M σ N (N * x / 2)

/-- `R_k = √((k²-M²)(k²-σ²))`. -/
noncomputable def Rk (M σ k : ℚ) : ℝ :=
  Real.sqrt (((k : ℝ) ^ 2 - (M : ℝ) ^ 2) * ((k : ℝ) ^ 2 - (σ : ℝ) ^ 2))

/-- `a_k^{(N)} = (R_k/k) √(1-k²/N²)` (`eq:rankJacobiFactor` and `eq:rankDefectFactor`). -/
noncomputable def aRank (M σ N k : ℚ) : ℝ :=
  Rk M σ k / (k : ℝ) * Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)

/-- `a_h(y)` of `eq:ah3` with `h = 1/N`. -/
noncomputable def aMid (M σ N : ℚ) (y : ℝ) : ℝ :=
  Real.sqrt (((1 - y) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) - M) ^ 2) *
    ((1 + y) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) + M) ^ 2))

/-! ### The rank recurrence -/

lemma E3_rank {L M σ N : ℚ} (hN : 0 < N) (hLN : L ≤ N) (hL0 : 0 ≤ L) :
    E3 (jMinus N σ : ℝ) (jPlus N σ : ℝ) (M : ℝ) (L : ℝ) =
      (N : ℝ) * (Rk M σ L * Real.sqrt (1 - (L : ℝ) ^ 2 / (N : ℝ) ^ 2)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hLr : (L : ℝ) ≤ N := by exact_mod_cast hLN
  have hL0r : (0 : ℝ) ≤ L := by exact_mod_cast hL0
  have hd : ((jMinus N σ : ℚ) : ℝ) - ((jPlus N σ : ℚ) : ℝ) = -(σ : ℝ) := by
    unfold jMinus jPlus; push_cast; ring
  have hs : ((jMinus N σ : ℚ) : ℝ) + ((jPlus N σ : ℚ) : ℝ) + 1 = N := by
    unfold jMinus jPlus; push_cast; ring
  unfold E3 Rk
  rw [hd, hs]
  have hB : (0 : ℝ) ≤ 1 - (L : ℝ) ^ 2 / (N : ℝ) ^ 2 := by
    rw [sub_nonneg, div_le_one (by positivity)]
    nlinarith
  have e : (((L : ℝ) ^ 2 - (-(σ : ℝ)) ^ 2) * ((N : ℝ) ^ 2 - (L : ℝ) ^ 2) *
      ((L : ℝ) ^ 2 - (M : ℝ) ^ 2)) =
      ((N : ℝ) ^ 2 * (1 - (L : ℝ) ^ 2 / (N : ℝ) ^ 2)) *
        (((L : ℝ) ^ 2 - (M : ℝ) ^ 2) * ((L : ℝ) ^ 2 - (σ : ℝ) ^ 2)) := by
    field_simp
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hNr.le]
  ring

/-- **`eq:3jrank`** (exact rank recurrence of the Regge-midpoint kernel), with `h = 1/N`,
`x` the midpoint coordinate and `R_k = √((k²-M²)(k²-σ²))`:
`(2L+1)[L(L+1)x - Mσ] Φ_L = (L+1) R_L √(1-L²h²) Φ_{L-1} + L R_{L+1} √(1-(L+1)²h²) Φ_{L+1}`.
The hypotheses say only that `L` is an admissible rank for the pair `(j_-, j_+)` (triangle
conditions) and for the projection `M` (`L ± M` natural numbers).  This is the paper's identity
verbatim, **at every rank row**: the end rows (`L = L_0`, where `R_{L_0}=0`, and `L = N-1`, where
`1-(L+1)²h²=0`) are included, with the out-of-range neighbour equal to `0`
(`threeJ_recurrence_all`). -/
theorem Phi3j_rank_recurrence (L M σ N x : ℚ) (hN : 0 < N)
    (hT : IsTri L (jMinus N σ) (jPlus N σ)) (h1 : IsNat (L + M)) (h2 : IsNat (L - M)) :
    (2 * (L : ℝ) + 1) * ((L : ℝ) * (L + 1) * (x : ℝ) - (M : ℝ) * σ) * PhiX L M σ N x =
      ((L : ℝ) + 1) * (Rk M σ L * Real.sqrt (1 - (L : ℝ) ^ 2 / (N : ℝ) ^ 2)) *
          PhiX (L - 1) M σ N x
        + (L : ℝ) * (Rk M σ (L + 1) * Real.sqrt (1 - ((L : ℝ) + 1) ^ 2 / (N : ℝ) ^ 2)) *
          PhiX (L + 1) M σ N x := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  set μ : ℚ := N * x / 2 with hμ
  have hm : M + mMinus M μ + mPlus M μ = 0 := by unfold mMinus mPlus; ring
  have hrec := threeJ_recurrence_all L (jMinus N σ) (jPlus N σ) M (mMinus M μ) (mPlus M μ) hm
    hT h1 h2
  have hLN : L ≤ N := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := hT
    unfold jMinus jPlus at hc
    have : (0 : ℚ) ≤ a := Nat.cast_nonneg a
    have : (0 : ℚ) ≤ b := Nat.cast_nonneg b
    have : (0 : ℚ) ≤ c := Nat.cast_nonneg c
    linarith
  have hLN1 : L + 1 ≤ N := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := hT
    unfold jMinus jPlus at hc
    have : (0 : ℚ) ≤ a := Nat.cast_nonneg a
    have : (0 : ℚ) ≤ b := Nat.cast_nonneg b
    have : (0 : ℚ) ≤ c := Nat.cast_nonneg c
    linarith
  have hL0 : 0 ≤ L := by
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    have : (0 : ℚ) ≤ a := Nat.cast_nonneg a
    have : (0 : ℚ) ≤ b := Nat.cast_nonneg b
    linarith
  have e0 := E3_rank (M := M) (σ := σ) hN hLN hL0
  have e1 := E3_rank (M := M) (σ := σ) hN hLN1 (by linarith)
  push_cast at e1
  have sp : sgn (2 * (L + 1) + jPlus N σ + mPlus M μ) = sgn (2 * L + jPlus N σ + mPlus M μ) := by
    have := sgn_add_int (2 * L + jPlus N σ + mPlus M μ) 2
    rw [show 2 * (L + 1) + jPlus N σ + mPlus M μ = 2 * L + jPlus N σ + mPlus M μ + ((2 : ℤ) : ℚ) by
      push_cast; ring, this]; norm_num
  have sm : sgn (2 * (L - 1) + jPlus N σ + mPlus M μ) = sgn (2 * L + jPlus N σ + mPlus M μ) := by
    have := sgn_add_int (2 * L + jPlus N σ + mPlus M μ) (-2)
    rw [show 2 * (L - 1) + jPlus N σ + mPlus M μ = 2 * L + jPlus N σ + mPlus M μ + ((-2 : ℤ) : ℚ) by
      push_cast; ring, this]; norm_num
  have hK : ((jMinus N σ : ℚ) : ℝ) * (((jMinus N σ : ℚ) : ℝ) + 1) -
      ((jPlus N σ : ℚ) : ℝ) * (((jPlus N σ : ℚ) : ℝ) + 1) = -(σ : ℝ) * N := by
    unfold jMinus jPlus; push_cast; ring
  have hmd : ((mPlus M μ : ℚ) : ℝ) - ((mMinus M μ : ℚ) : ℝ) = -(N : ℝ) * x := by
    unfold mMinus mPlus; rw [hμ]; push_cast; ring
  rw [hK, hmd, e0, e1] at hrec
  unfold PhiX
  rw [← hμ]
  unfold Phi3j
  rw [sp, sm]
  have hs := sgn_mul_self_of_int (x := 2 * L + jPlus N σ + mPlus M μ)
  set s0 := sgn (2 * L + jPlus N σ + mPlus M μ)
  set r := Real.sqrt (N : ℝ)
  have hrN : r ≠ 0 := by
    have : (0 : ℝ) < r := Real.sqrt_pos.mpr (by exact_mod_cast hN)
    exact this.ne'
  have key := congrArg (fun t => t * (s0 * r) / (N : ℝ)) hrec
  field_simp at key ⊢
  linear_combination key

/-- **`eq:rankJacobiForm`** (`obs:rankJacobi`): the exact three-term Jacobi form of the rank
recurrence,
`a_{L+1}^{(N)} Φ_{L+1} + a_L^{(N)} Φ_{L-1} = b_L^{(0)}(x) Φ_L` with
`b_L^{(0)}(x) = (2L+1)(x - Mσ/(L(L+1)))`, for `L > 0`; it is `Phi3j_rank_recurrence` divided by
`L(L+1)`.  Same hypotheses (all rank rows). -/
theorem Phi3j_rank_jacobi (L M σ N x : ℚ) (hN : 0 < N) (hL : 0 < L)
    (hT : IsTri L (jMinus N σ) (jPlus N σ)) (h1 : IsNat (L + M)) (h2 : IsNat (L - M)) :
    aRank M σ N (L + 1) * PhiX (L + 1) M σ N x + aRank M σ N L * PhiX (L - 1) M σ N x =
      (2 * (L : ℝ) + 1) * ((x : ℝ) - (M : ℝ) * σ / ((L : ℝ) * (L + 1))) * PhiX L M σ N x := by
  have := Phi3j_rank_recurrence L M σ N x hN hT h1 h2
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  unfold aRank
  push_cast at this ⊢
  generalize Real.sqrt (1 - ((L : ℝ) + 1) ^ 2 / (N : ℝ) ^ 2) = s1 at this ⊢
  generalize Real.sqrt (1 - (L : ℝ) ^ 2 / (N : ℝ) ^ 2) = s0 at this ⊢
  generalize Rk M σ (L + 1) = r1 at this ⊢
  generalize Rk M σ L = r0 at this ⊢
  field_simp
  linear_combination (-1 : ℝ) * this

/-! ### The algebra of `a_h` -/

/-- `a_h(y)` is even in `h`: it only involves `h²`.  (With `h = 1/N`, `h ↦ -h` is `N ↦ -N`.) -/
lemma aMid_neg_N (M σ : ℚ) (N : ℚ) (y : ℝ) : aMid M σ (-N) y = aMid M σ N y := by
  unfold aMid; push_cast; congr 2 <;> ring

/-- The first factor of `a_h(y)` vanishes at `y = 1 - (1+|σ-M|) h`, i.e. `y = x_max + h` for the
top lattice point `x_max = 1 - (1+|M-σ|)h` of `eq:physicalgrid` (here `d = |M-σ|`,
`x_max + h = 1 - d h`... recorded as the exact zero of the factor `(1-y)² - h²(σ-M)²`). -/
lemma aMid_zero_top (M σ N : ℚ) (hN : N ≠ 0) :
    aMid M σ N (1 - |(σ : ℝ) - M| / N) = 0 := by
  unfold aMid
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have : (1 - (1 - |(σ : ℝ) - M| / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) - M) ^ 2 = 0 := by
    rw [show (1 - (1 - |(σ : ℝ) - M| / N)) = |(σ : ℝ) - M| / N by ring, div_pow, sq_abs]
    field_simp
    ring
  rw [this, zero_mul, Real.sqrt_zero]

/-- The second factor `(1+y)² - h²(σ+M)²` vanishes at `y = -1 + |σ+M| h`
(`x_min - h` with `x_min = -1 + (1+|M+σ|)h`). -/
lemma aMid_zero_bottom (M σ N : ℚ) (hN : N ≠ 0) :
    aMid M σ N (-1 + |(σ : ℝ) + M| / N) = 0 := by
  unfold aMid
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have : (1 + (-1 + |(σ : ℝ) + M| / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) + M) ^ 2 = 0 := by
    rw [show (1 + (-1 + |(σ : ℝ) + M| / N)) = |(σ : ℝ) + M| / N by ring, div_pow, sq_abs]
    field_simp
    ring
  rw [this, mul_zero, Real.sqrt_zero]

lemma aMid_sq {M σ N : ℚ} {y : ℝ}
    (h : 0 ≤ ((1 - y) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) - M) ^ 2) *
      ((1 + y) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) + M) ^ 2)) :
    aMid M σ N y ^ 2 = ((1 - y) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) - M) ^ 2) *
      ((1 + y) ^ 2 - (1 / (N : ℝ)) ^ 2 * ((σ : ℝ) + M) ^ 2) := Real.sq_sqrt h

/-! ### The magnetic (finite-difference) recurrence -/

/-- **`eq:3jdiff`** (exact finite-difference equation of the Regge-midpoint kernel), with
`h = 1/N`:
`a_h(x+h) Φ(x+2h) + a_h(x-h) Φ(x-2h) - 2(1-x²) Φ(x) + 2h²[2L(L+1) - M² - σ² + 1] Φ(x) = 0`.
The four `IsNat` hypotheses say that `x` itself lies on the physical lattice
(`j_±±m_± ∈ ℕ`); the neighbours `x ± 2h` need not (if one is off the lattice its coefficient
`a_h(x±h)` is `0` and the kernel there is `0`).  The statement is the paper's verbatim. -/
theorem PhiX_midpoint_diff (L M σ N x : ℚ) (hN : 0 < N)
    (a1 : IsNat (jMinus N σ + mMinus M (N * x / 2)))
    (a4 : IsNat (jPlus N σ - mPlus M (N * x / 2)))
    (b1 : IsNat (jMinus N σ - mMinus M (N * x / 2)))
    (b3 : IsNat (jPlus N σ + mPlus M (N * x / 2))) :
    aMid M σ N ((x : ℝ) + 1 / N) * PhiX L M σ N (x + 2 / N)
      + aMid M σ N ((x : ℝ) - 1 / N) * PhiX L M σ N (x - 2 / N)
      - 2 * (1 - (x : ℝ) ^ 2) * PhiX L M σ N x
      + 2 * (1 / (N : ℝ)) ^ 2 * (2 * (L : ℝ) * (L + 1) - (M : ℝ) ^ 2 - (σ : ℝ) ^ 2 + 1) *
          PhiX L M σ N x = 0 := by
  have hNq : N ≠ 0 := hN.ne'
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hNq
  set μ : ℚ := N * x / 2 with hμ
  have hm : M + mMinus M μ + mPlus M μ = 0 := by unfold mMinus mPlus; ring
  have hrec := threeJ_recurrence_m_all L (jMinus N σ) (jPlus N σ) M (mMinus M μ) (mPlus M μ) hm
    a1 a4 b1 b3
  -- the two shifted arguments
  have ep : N * (x + 2 / N) / 2 = μ + 1 := by rw [hμ]; field_simp
  have em : N * (x - 2 / N) / 2 = μ - 1 := by rw [hμ]; field_simp
  have hmm1 : mMinus M (μ + 1) = mMinus M μ + 1 := by unfold mMinus; ring
  have hmm2 : mMinus M (μ - 1) = mMinus M μ - 1 := by unfold mMinus; ring
  have hmp1 : mPlus M (μ + 1) = mPlus M μ - 1 := by unfold mPlus; ring
  have hmp2 : mPlus M (μ - 1) = mPlus M μ + 1 := by unfold mPlus; ring
  have sP : sgn (2 * L + jPlus N σ + (mPlus M μ - 1)) = - sgn (2 * L + jPlus N σ + mPlus M μ) := by
    rw [show 2 * L + jPlus N σ + (mPlus M μ - 1) = (2 * L + jPlus N σ + mPlus M μ) - 1 by ring,
      sgn_sub_one]
  have sM : sgn (2 * L + jPlus N σ + (mPlus M μ + 1)) = - sgn (2 * L + jPlus N σ + mPlus M μ) := by
    rw [show 2 * L + jPlus N σ + (mPlus M μ + 1) = (2 * L + jPlus N σ + mPlus M μ) + 1 by ring,
      sgn_add_one]
  have hPp : PhiX L M σ N (x + 2 / N) = - (sgn (2 * L + jPlus N σ + mPlus M μ) *
      Real.sqrt (N : ℝ) * threeJ L (jMinus N σ) (jPlus N σ) M (mMinus M μ + 1)
        (mPlus M μ - 1)) := by
    unfold PhiX Phi3j
    rw [ep, hmm1, hmp1, sP]; ring
  have hPm : PhiX L M σ N (x - 2 / N) = - (sgn (2 * L + jPlus N σ + mPlus M μ) *
      Real.sqrt (N : ℝ) * threeJ L (jMinus N σ) (jPlus N σ) M (mMinus M μ - 1)
        (mPlus M μ + 1)) := by
    unfold PhiX Phi3j
    rw [em, hmm2, hmp2, sM]; ring
  have hP0 : PhiX L M σ N x = sgn (2 * L + jPlus N σ + mPlus M μ) * Real.sqrt (N : ℝ) *
      threeJ L (jMinus N σ) (jPlus N σ) M (mMinus M μ) (mPlus M μ) := by
    unfold PhiX Phi3j; rw [← hμ]
  -- the square roots
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have cP : Real.sqrt ((((jMinus N σ : ℚ) : ℝ) - ((mMinus M μ : ℚ) : ℝ)) *
        (((jMinus N σ : ℚ) : ℝ) + ((mMinus M μ : ℚ) : ℝ) + 1) *
        (((jPlus N σ : ℚ) : ℝ) - ((mPlus M μ : ℚ) : ℝ) + 1) *
        (((jPlus N σ : ℚ) : ℝ) + ((mPlus M μ : ℚ) : ℝ))) =
      ((N : ℝ) ^ 2 / 4) * aMid M σ N ((x : ℝ) + 1 / N) := by
    unfold aMid
    have e : (((jMinus N σ : ℚ) : ℝ) - ((mMinus M μ : ℚ) : ℝ)) *
        (((jMinus N σ : ℚ) : ℝ) + ((mMinus M μ : ℚ) : ℝ) + 1) *
        (((jPlus N σ : ℚ) : ℝ) - ((mPlus M μ : ℚ) : ℝ) + 1) *
        (((jPlus N σ : ℚ) : ℝ) + ((mPlus M μ : ℚ) : ℝ)) =
        ((N : ℝ) ^ 2 / 4) ^ 2 * (((1 - ((x : ℝ) + 1 / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 *
          ((σ : ℝ) - M) ^ 2) * ((1 + ((x : ℝ) + 1 / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 *
          ((σ : ℝ) + M) ^ 2)) := by
      unfold jMinus jPlus mMinus mPlus; rw [hμ]; push_cast
      field_simp
      ring
    rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have cM : Real.sqrt ((((jMinus N σ : ℚ) : ℝ) - ((mMinus M μ : ℚ) : ℝ) + 1) *
        (((jMinus N σ : ℚ) : ℝ) + ((mMinus M μ : ℚ) : ℝ)) *
        (((jPlus N σ : ℚ) : ℝ) - ((mPlus M μ : ℚ) : ℝ)) *
        (((jPlus N σ : ℚ) : ℝ) + ((mPlus M μ : ℚ) : ℝ) + 1)) =
      ((N : ℝ) ^ 2 / 4) * aMid M σ N ((x : ℝ) - 1 / N) := by
    unfold aMid
    have e : (((jMinus N σ : ℚ) : ℝ) - ((mMinus M μ : ℚ) : ℝ) + 1) *
        (((jMinus N σ : ℚ) : ℝ) + ((mMinus M μ : ℚ) : ℝ)) *
        (((jPlus N σ : ℚ) : ℝ) - ((mPlus M μ : ℚ) : ℝ)) *
        (((jPlus N σ : ℚ) : ℝ) + ((mPlus M μ : ℚ) : ℝ) + 1) =
        ((N : ℝ) ^ 2 / 4) ^ 2 * (((1 - ((x : ℝ) - 1 / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 *
          ((σ : ℝ) - M) ^ 2) * ((1 + ((x : ℝ) - 1 / N)) ^ 2 - (1 / (N : ℝ)) ^ 2 *
          ((σ : ℝ) + M) ^ 2)) := by
      unfold jMinus jPlus mMinus mPlus; rw [hμ]; push_cast
      field_simp
      ring
    rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hc : (((L : ℝ) * (L + 1) - ((jMinus N σ : ℚ) : ℝ) * (((jMinus N σ : ℚ) : ℝ) + 1) -
      ((jPlus N σ : ℚ) : ℝ) * (((jPlus N σ : ℚ) : ℝ) + 1)) -
      2 * ((mMinus M μ : ℚ) : ℝ) * ((mPlus M μ : ℚ) : ℝ)) =
      -((N : ℝ) ^ 2 / 2) * (1 - (x : ℝ) ^ 2) +
        (1 / 2) * (2 * (L : ℝ) * (L + 1) - (M : ℝ) ^ 2 - (σ : ℝ) ^ 2 + 1) := by
    unfold jMinus jPlus mMinus mPlus; rw [hμ]; push_cast; ring
  rw [hc, cP, cM] at hrec
  rw [hPp, hPm, hP0]
  generalize sgn (2 * L + jPlus N σ + mPlus M μ) * Real.sqrt (N : ℝ) = w
  generalize threeJ L (jMinus N σ) (jPlus N σ) M (mMinus M μ + 1) (mPlus M μ - 1) = Tp at hrec ⊢
  generalize threeJ L (jMinus N σ) (jPlus N σ) M (mMinus M μ - 1) (mPlus M μ + 1) = Tm at hrec ⊢
  generalize threeJ L (jMinus N σ) (jPlus N σ) M (mMinus M μ) (mPlus M μ) = T0 at hrec ⊢
  generalize aMid M σ N ((x : ℝ) + 1 / N) = ap at hrec ⊢
  generalize aMid M σ N ((x : ℝ) - 1 / N) = am at hrec ⊢
  have h2 : ap * -(w * Tp) + am * -(w * Tm) - 2 * (1 - (x : ℝ) ^ 2) * (w * T0)
      + 2 * (1 / (N : ℝ)) ^ 2 * (2 * (L : ℝ) * (L + 1) - (M : ℝ) ^ 2 - (σ : ℝ) ^ 2 + 1) *
          (w * T0) =
      (4 / (N : ℝ) ^ 2 * w) *
        ((-((N : ℝ) ^ 2 / 2) * (1 - (x : ℝ) ^ 2) +
            1 / 2 * (2 * (L : ℝ) * (L + 1) - (M : ℝ) ^ 2 - (σ : ℝ) ^ 2 + 1)) * T0 -
          ((N : ℝ) ^ 2 / 4 * ap * Tp + (N : ℝ) ^ 2 / 4 * am * Tm)) := by
    field_simp
    ring
  rw [h2, sub_eq_zero.mpr hrec, mul_zero]

/-- info: 'FormalResearch.Racah.Phi3j_rank_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_rank_recurrence

/-- info: 'FormalResearch.Racah.Phi3j_rank_jacobi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_rank_jacobi

/-- info: 'FormalResearch.Racah.PhiX_midpoint_diff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhiX_midpoint_diff

end FormalResearch.Racah
