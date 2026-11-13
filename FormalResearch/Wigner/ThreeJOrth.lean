module

public import FormalResearch.Wigner.ThreeJOrthTop
public import FormalResearch.Wigner.Special3j

/-!
# Orthogonality of the Wigner `3j` symbol in the rank (DLMF 34.3.17)

For fixed `j₂ j₃` and fixed projection `M` of the first spin,
`∑_{m₂+m₃=-M} (L j₂ j₃; M m₂ m₃)(L' j₂ j₃; M m₂ m₃) = δ_{LL'}/(2L+1)`
(`threeJ_orthogonality`), the sum over the lattice `m₂ = j₂ - k`, `k ∈ ℕ` (the symbol is zero outside
the admissible range).  The off-diagonal part is the Green identity for the symmetric recurrence in
`m₂` (`ThreeJOrthM`); the norm is propagated from the stretched top rank `L = j₂ + j₃` down the
rank lattice by the summed rank recurrence (`ThreeJOrthL`, `ThreeJOrthTop`), the rank `L = 0`
being a direct computation.
-/

@[expose] public section

namespace FormalResearch.Wigner

lemma LAdm.succ {j₂ j₃ M L : ℚ} (h : LAdm j₂ j₃ M L) {n : ℕ} (hn : -L + j₂ + j₃ = ((n + 1 : ℕ) : ℚ)) :
    LAdm j₂ j₃ M (L + 1) := by
  obtain ⟨⟨⟨p1, hp1⟩, ⟨p2, hp2⟩, -⟩, ⟨q1, hq1⟩, ⟨q2, hq2⟩⟩ := h
  refine ⟨⟨⟨p1 + 1, ?_⟩, ⟨p2 + 1, ?_⟩, ⟨n, ?_⟩⟩, ⟨q1 + 1, ?_⟩, ⟨q2 + 1, ?_⟩⟩ <;>
    push_cast at hn ⊢ <;> linarith

/-- The norm at rank `L = 0`: `∑ₘ tt 0 m² = 1`. -/
theorem tt_norm_zero (j₂ j₃ M : ℚ) (h : LAdm j₂ j₃ M 0) :
    (2 * ((0 : ℚ) : ℝ) + 1) * TOA j₂ j₃ M 0 0 = 1 := by
  obtain ⟨⟨⟨p1, hp1⟩, ⟨p2, hp2⟩, ⟨n, hn⟩⟩, ⟨q1, hq1⟩, ⟨q2, hq2⟩⟩ := h
  have e23 : j₂ = j₃ := by
    have : (0 : ℚ) ≤ p1 := by positivity
    have : (0 : ℚ) ≤ p2 := by positivity
    linarith
  have eM : M = 0 := by
    have : (0 : ℚ) ≤ q1 := by positivity
    have : (0 : ℚ) ≤ q2 := by positivity
    linarith
  subst e23 eM
  have hn' : 2 * j₂ = n := by linarith
  have hsupp : (Function.support fun k : ℕ =>
      tt j₂ j₂ 0 0 (j₂ - k) * tt j₂ j₂ 0 0 (j₂ - k)) ⊆ ↑(Finset.range (n + 1)) := by
    intro k hk
    simp only [Function.mem_support, ne_eq] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hk
    have : tt j₂ j₂ 0 0 (j₂ - k) = 0 := by
      apply tt_eq_zero_of_not_madm
      rintro ⟨⟨a, ha⟩, -⟩
      have : (n : ℚ) + 1 ≤ k := by exact_mod_cast not_lt.mp hlt
      have : (0 : ℚ) ≤ a := by positivity
      linarith
    rw [this]; ring
  have hterm : ∀ k ∈ Finset.range (n + 1),
      tt j₂ j₂ 0 0 (j₂ - k) * tt j₂ j₂ 0 0 (j₂ - k) = 1 / ((n : ℝ) + 1) := by
    intro k hk
    have hkn : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
    have ha : IsNat (j₂ + (j₂ - k)) := ⟨n - k, by push_cast [Nat.cast_sub hkn]; linarith⟩
    have hb : IsNat (j₂ - (j₂ - k)) := ⟨k, by ring⟩
    have e : tt j₂ j₂ 0 0 (j₂ - k) = threeJ j₂ j₂ 0 (j₂ - k) (-(j₂ - k)) 0 := by
      unfold tt
      rw [← threeJ_cyc' j₂ j₂ 0 (j₂ - k) (-(j₂ - k)) 0]
      simp
    rw [e, threeJ_zero_right ha hb]
    have hsg : sgn (j₂ - (j₂ - k)) * sgn (j₂ - (j₂ - k)) = 1 := by
      apply sgn_mul_self_of_int
      exact ⟨k, by push_cast; ring⟩
    have hj : (2 * (j₂ : ℝ) + 1) = (n : ℝ) + 1 := by
      have : (2 * j₂ + 1 : ℚ) = n + 1 := by linarith
      exact_mod_cast this
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [hj]
    have := Real.mul_self_sqrt hpos.le
    have hs0 : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr hpos
    calc sgn (j₂ - (j₂ - k)) / Real.sqrt ((n : ℝ) + 1) *
          (sgn (j₂ - (j₂ - k)) / Real.sqrt ((n : ℝ) + 1))
        = (sgn (j₂ - (j₂ - k)) * sgn (j₂ - (j₂ - k))) /
            (Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)) := by
          field_simp
      _ = 1 / ((n : ℝ) + 1) := by rw [hsg, this]
  have hsum : TOA j₂ j₂ 0 0 0 = ∑ k ∈ Finset.range (n + 1), 1 / ((n : ℝ) + 1) := by
    unfold TOA msum
    rw [finsum_eq_sum_of_support_subset _ hsupp]
    exact Finset.sum_congr rfl hterm
  rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  push_cast
  field_simp
  norm_num

/-- **Norm of the `3j` orthogonality relation**: `(2L+1) ∑ₘ tt L m² = 1` for admissible `L`. -/
theorem tt_norm (j₂ j₃ M L : ℚ) (h : LAdm j₂ j₃ M L) :
    (2 * (L : ℝ) + 1) * TOA j₂ j₃ M L L = 1 := by
  obtain ⟨n, hn⟩ := h.1.2.2
  induction n generalizing L with
  | zero =>
    have hL : L = j₂ + j₃ := by push_cast at hn; linarith
    subst hL
    have := tt_norm_top j₂ j₃ M h
    push_cast at this ⊢
    exact this
  | succ n ih =>
    by_cases hL0 : L = 0
    · subst hL0; exact tt_norm_zero j₂ j₃ M h
    have hpos : 0 < L := lt_of_le_of_ne h.nonneg (Ne.symm hL0)
    have h1 := h.succ hn
    have ih' := ih (L + 1) h1 (by push_cast at hn ⊢; linarith)
    have hr := tt_norm_ratio j₂ j₃ M L hpos h h1
    push_cast at ih' hr
    linarith

/-- **DLMF 34.3.17 (orthogonality of the `3j` symbol in the rank).**  For fixed `j₂ j₃` and fixed
projection `M` of the first spin, and admissible ranks `L, L'` (`(L j₂ j₃)` and `(L' j₂ j₃)`
triangles with integral sum, `L ± M`, `L' ± M` natural numbers),
`∑_{m₂+m₃=-M} (L j₂ j₃; M m₂ m₃)(L' j₂ j₃; M m₂ m₃) = δ_{LL'}/(2L+1)`.
The sum is over the lattice `m₂ = j₂ - k`, `k ∈ ℕ`, which contains every `m₂` with `j₂ - m₂ ∈ ℕ`;
the symbol is zero outside the admissible range, so the `finsum` is the finite sum over the
admissible `m₂`. -/
theorem threeJ_orthogonality (j₂ j₃ M L L' : ℚ)
    (hT : IsTri L j₂ j₃) (h1 : IsNat (L + M)) (h2 : IsNat (L - M))
    (hT' : IsTri L' j₂ j₃) (h1' : IsNat (L' + M)) (h2' : IsNat (L' - M)) :
    ∑ᶠ k : ℕ, threeJ L j₂ j₃ M (j₂ - k) (-M - (j₂ - k)) *
        threeJ L' j₂ j₃ M (j₂ - k) (-M - (j₂ - k)) =
      if L = L' then 1 / (2 * (L : ℝ) + 1) else 0 := by
  have hL : LAdm j₂ j₃ M L := ⟨hT, h1, h2⟩
  have hL' : LAdm j₂ j₃ M L' := ⟨hT', h1', h2'⟩
  have hOA : ∑ᶠ k : ℕ, threeJ L j₂ j₃ M (j₂ - k) (-M - (j₂ - k)) *
        threeJ L' j₂ j₃ M (j₂ - k) (-M - (j₂ - k)) = TOA j₂ j₃ M L L' := rfl
  rw [hOA]
  split_ifs with he
  · subst he
    have := tt_norm j₂ j₃ M L hL
    have hpos : (0 : ℝ) < 2 * (L : ℝ) + 1 := by
      have : (0 : ℝ) ≤ L := by exact_mod_cast hL.nonneg
      linarith
    field_simp
    linarith
  · apply tt_orth_offdiag
    intro h
    have n1 : (0 : ℝ) ≤ L := by exact_mod_cast hL.nonneg
    have n2 : (0 : ℝ) ≤ L' := by exact_mod_cast hL'.nonneg
    have h0 : ((L : ℝ) - L') * ((L : ℝ) + L' + 1) = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h3 | h3
    · exact he (by exact_mod_cast (by linarith : (L : ℝ) = L'))
    · linarith

/-- info: 'FormalResearch.Wigner.tt_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tt_norm

/-- info: 'FormalResearch.Wigner.threeJ_orthogonality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threeJ_orthogonality

end FormalResearch.Wigner
