module

public import FormalResearch.Wigner.ThreeJOrthL
public import FormalResearch.Wigner.Stretched3j

/-!
# The norm of the `3j` orthogonality relation at the top rank `L = j₂ + j₃`

For `L = j₂ + j₃` the symbol is the stretched one-term value `threeJ_stretched` (DLMF 34.3.6), and
`(2L+1) ∑_m tt L m² = 1` is the Chu--Vandermonde identity
`∑_k C(2j₂,k) C(2j₃,J+M-k) = C(2j₂+2j₃, J+M)`.
-/

@[expose] public section

namespace FormalResearch.Wigner

open Nat

/-- The squared stretched symbol: `tt² = P! Q!/(u+v+1)! · C(u,k) C(v,P-k)` at `m = j₂ - k`, for
`u = 2j₂`, `v = 2j₃`, `P = J+M`, `Q = J-M`, `k ≤ P`. -/
lemma tt_top_sq {j₂ j₃ M : ℚ} {u v P Q : ℕ} (hu : 2 * j₂ = u) (hv : 2 * j₃ = v)
    (hP : j₂ + j₃ + M = P) (hQ : j₂ + j₃ - M = Q) {k : ℕ} (hk : k ≤ P) :
    tt j₂ j₃ M (j₂ + j₃) (j₂ - k) ^ 2 =
      (((P)! : ℝ) * (Q)! / ((u + v + 1)! : ℝ)) * ((u.choose k : ℝ) * (v.choose (P - k) : ℝ)) := by
  have hPQ : P + Q = u + v := by
    have : ((P + Q : ℕ) : ℚ) = ((u + v : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  by_cases hkk : k ≤ u ∧ P - k ≤ v
  · obtain ⟨hku, hkv⟩ := hkk
    -- naturals A B C D
    obtain ⟨C, hC⟩ : ∃ C : ℕ, C = v - (P - k) := ⟨_, rfl⟩
    obtain ⟨A, hA⟩ : ∃ A : ℕ, A = u - k := ⟨_, rfl⟩
    have hAk : A + k = u := by omega
    have hCD : C + (P - k) = v := by omega
    have hAC : A + C = Q := by omega
    have hAq : (A : ℚ) = j₂ + (j₂ - k) := by
      have : ((A + k : ℕ) : ℚ) = u := by exact_mod_cast hAk
      push_cast at this; linarith
    have hDq : ((P - k : ℕ) : ℚ) = P - k := by push_cast [Nat.cast_sub hk]; ring
    have hCq : (C : ℚ) = j₃ + (-M - (j₂ - k)) := by
      have : ((C + (P - k) : ℕ) : ℚ) = v := by exact_mod_cast hCD
      push_cast [Nat.cast_sub hk] at this; linarith
    have hm : (j₂ - k) + (-M - (j₂ - k)) + M = 0 := by ring
    have e : tt j₂ j₃ M (j₂ + j₃) (j₂ - k) =
        threeJ j₂ j₃ (j₂ + j₃) (j₂ - k) (-M - (j₂ - k)) M := by
      unfold tt
      rw [threeJ_cyc' j₂ j₃ (j₂ + j₃) (j₂ - k) (-M - (j₂ - k)) M]
    have hs := threeJ_stretched (j₁ := j₂) (j₂ := j₃) (m₁ := j₂ - k) (m₂ := -M - (j₂ - k))
      (m₃ := M) (A := A) (B := k) (C := C) (D := P - k) hm
      (by linarith) (by ring) (by linarith) (by linarith)
    rw [e, hs]
    have hsg : sgn (j₂ - j₃ - M) * sgn (j₂ - j₃ - M) = 1 := by
      apply sgn_mul_self_of_int
      refine ⟨(A : ℤ) - ((P - k : ℕ) : ℤ), ?_⟩
      push_cast
      rw [hAq, hDq]
      ring_nf
      linarith
    rw [mul_pow, sq (sgn _), hsg, one_mul, Real.sq_sqrt (by positivity)]
    have f1 : (u.choose k : ℝ) * (k ! : ℝ) * (A ! : ℝ) = (u ! : ℝ) := by
      have := Nat.choose_mul_factorial_mul_factorial (n := u) (k := k) hku
      rw [show u - k = A by omega] at this
      exact_mod_cast this
    have f2 : (v.choose (P - k) : ℝ) * ((P - k) ! : ℝ) * (C ! : ℝ) = (v ! : ℝ) := by
      have := Nat.choose_mul_factorial_mul_factorial (n := v) (k := P - k) hkv
      rw [show v - (P - k) = C by omega] at this
      exact_mod_cast this
    have s1 : A + k = u := hAk
    have s2 : C + (P - k) = v := hCD
    have s3 : k + (P - k) = P := by omega
    have s4 : A + C = Q := hAC
    have s5 : A + k + C + (P - k) + 1 = u + v + 1 := by omega
    rw [s5, s1, s2, s3, s4]
    have hAf : (A ! : ℝ) ≠ 0 := by positivity
    have hkf : (k ! : ℝ) ≠ 0 := by positivity
    have hCf : (C ! : ℝ) ≠ 0 := by positivity
    have hDf : ((P - k) ! : ℝ) ≠ 0 := by positivity
    have hu1 : ((u + v + 1)! : ℝ) ≠ 0 := by positivity
    have c1 : (u.choose k : ℝ) = (u ! : ℝ) / ((k ! : ℝ) * (A ! : ℝ)) := by
      field_simp; linarith [f1]
    have c2 : (v.choose (P - k) : ℝ) = (v ! : ℝ) / (((P - k) ! : ℝ) * (C ! : ℝ)) := by
      field_simp; linarith [f2]
    rw [c1, c2]
    field_simp
  · -- not admissible: both sides vanish
    have hz : tt j₂ j₃ M (j₂ + j₃) (j₂ - k) = 0 := by
      apply tt_eq_zero_of_not_madm
      rintro ⟨⟨a, ha⟩, -, ⟨c, hc⟩, ⟨d, hd⟩⟩
      apply hkk
      have hu' : (u : ℚ) = 2 * j₂ := hu.symm
      have h1 : ((k : ℕ) : ℚ) ≤ u := by
        have : (0 : ℚ) ≤ a := by positivity
        linarith
      have h2 : ((P - k : ℕ) : ℚ) ≤ v := by
        have hDq : ((P - k : ℕ) : ℚ) = P - k := by push_cast [Nat.cast_sub hk]; ring
        have : (0 : ℚ) ≤ c := by positivity
        have hv' : (v : ℚ) = 2 * j₃ := hv.symm
        rw [hDq]; linarith
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    rw [hz]
    have : (u.choose k : ℝ) * (v.choose (P - k) : ℝ) = 0 := by
      by_cases h1 : k ≤ u
      · have h2 : v < P - k := by omega
        rw [Nat.choose_eq_zero_of_lt h2]; simp
      · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    rw [this]; ring

/-- The norm at the top rank: `(2J+1) ∑ₘ tt J m² = 1`, `J = j₂ + j₃`. -/
theorem tt_norm_top (j₂ j₃ M : ℚ) (h : LAdm j₂ j₃ M (j₂ + j₃)) :
    (2 * ((j₂ + j₃ : ℚ) : ℝ) + 1) * TOA j₂ j₃ M (j₂ + j₃) (j₂ + j₃) = 1 := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, -⟩, ⟨P, hP⟩, ⟨Q, hQ⟩⟩ := h
  have hu : 2 * j₂ = ((a : ℕ) : ℚ) := by linarith
  have hv : 2 * j₃ = ((b : ℕ) : ℚ) := by linarith
  have hP' : j₂ + j₃ + M = P := hP
  have hQ' : j₂ + j₃ - M = Q := hQ
  have hPQ : P + Q = a + b := by
    have : ((P + Q : ℕ) : ℚ) = ((a + b : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  -- the support is `k ≤ P`
  have hsupp : (Function.support fun k : ℕ =>
      tt j₂ j₃ M (j₂ + j₃) (j₂ - k) * tt j₂ j₃ M (j₂ + j₃) (j₂ - k)) ⊆
        ↑(Finset.range (P + 1)) := by
    intro k hk
    simp only [Function.mem_support, ne_eq] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hk
    have : tt j₂ j₃ M (j₂ + j₃) (j₂ - k) = 0 := by
      apply tt_eq_zero_of_not_madm
      rintro ⟨-, -, -, ⟨d, hd⟩⟩
      have : (P : ℚ) + 1 ≤ k := by exact_mod_cast not_lt.mp hlt
      have : (0 : ℚ) ≤ d := by positivity
      linarith
    rw [this]; ring
  have hsum : TOA j₂ j₃ M (j₂ + j₃) (j₂ + j₃) =
      ∑ k ∈ Finset.range (P + 1), tt j₂ j₃ M (j₂ + j₃) (j₂ - k) ^ 2 := by
    unfold TOA msum
    rw [finsum_eq_sum_of_support_subset _ hsupp]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsum]
  have hterm : ∀ k ∈ Finset.range (P + 1), tt j₂ j₃ M (j₂ + j₃) (j₂ - k) ^ 2 =
      (((P)! : ℝ) * (Q)! / ((a + b + 1)! : ℝ)) * ((a.choose k : ℝ) * (b.choose (P - k) : ℝ)) := by
    intro k hk
    exact tt_top_sq hu hv hP' hQ' (by simpa [Nat.lt_succ_iff] using hk)
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hV : ∑ k ∈ Finset.range (P + 1), (a.choose k : ℝ) * (b.choose (P - k) : ℝ) =
      ((a + b).choose P : ℝ) := by
    have := Nat.add_choose_eq a b P
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at this
    exact_mod_cast this.symm
  rw [hV]
  have hch : ((a + b).choose P : ℝ) * (P ! : ℝ) * (Q ! : ℝ) = ((a + b)! : ℝ) := by
    have := Nat.choose_mul_factorial_mul_factorial (n := a + b) (k := P) (by omega)
    rw [show a + b - P = Q by omega] at this
    exact_mod_cast this
  have hP0 : (P ! : ℝ) ≠ 0 := by positivity
  have hQ0 : (Q ! : ℝ) ≠ 0 := by positivity
  have hab : ((a + b + 1)! : ℝ) = ((a : ℝ) + b + 1) * ((a + b)! : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hab0 : ((a + b)! : ℝ) ≠ 0 := by positivity
  have hcast : (2 * ((j₂ + j₃ : ℚ) : ℝ) + 1) = (a : ℝ) + b + 1 := by
    have : (2 * (j₂ + j₃) + 1 : ℚ) = ((a + b + 1 : ℕ) : ℚ) := by push_cast; linarith
    have h2 : ((2 * (j₂ + j₃) + 1 : ℚ) : ℝ) = (((a + b + 1 : ℕ) : ℚ) : ℝ) := by rw [this]
    push_cast at h2 ⊢
    linarith
  rw [hcast, hab]
  have hpos : (0 : ℝ) < (a : ℝ) + b + 1 := by positivity
  have hch' : ((a + b).choose P : ℝ) = ((a + b)! : ℝ) / ((P ! : ℝ) * (Q ! : ℝ)) := by
    field_simp; linarith [hch]
  rw [hch']
  field_simp

/-- info: 'FormalResearch.Wigner.tt_norm_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tt_norm_top

end FormalResearch.Wigner
