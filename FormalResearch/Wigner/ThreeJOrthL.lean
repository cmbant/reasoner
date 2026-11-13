module

public import FormalResearch.Wigner.ThreeJOrthM

/-!
# The rank recurrence of the `3j` symbol and the norm ratio (DLMF 34.3.17)

`tt_rec_L` is DLMF 34.3.15 in the rank `L` for every rational `L` and `m` (no admissibility of the
neighbours).  Summing it over the projection `m` against `tt L'` and using the off-diagonal
orthogonality `tt_orth_offdiag` (which kills the neighbouring overlaps) gives the norm ratio
`(2L+3) ∑_m tt (L+1)² = (2L+1) ∑_m tt L²` for `L > 0` (`tt_norm_ratio`), as for classical orthogonal
polynomials.  The only coefficient `m` appears in is linear: `2(2L+1)L(L+1) m`.
-/

@[expose] public section

namespace FormalResearch.Wigner

open FormalResearch.Racah

/-- Admissibility of the rank `L` for fixed `j₂, j₃, M`. -/
def LAdm (j₂ j₃ M L : ℚ) : Prop := IsTri L j₂ j₃ ∧ IsNat (L + M) ∧ IsNat (L - M)

lemma tt_eq_zero_of_not_ladm {j₂ j₃ M : ℚ} (L m : ℚ) (h : ¬ LAdm j₂ j₃ M L) :
    tt j₂ j₃ M L m = 0 := by
  apply threeJ_eq_zero_of_racah
  apply racahSum3_zero_of_not_isNat _ _ _ _ _ (-M - m) (by ring)
  unfold LAdm at h
  by_contra hcon
  push Not at hcon
  exact h ⟨⟨hcon.1, hcon.2.1, hcon.2.2.1⟩, hcon.2.2.2.1, hcon.2.2.2.2.1⟩

lemma E3_eq_zero_of_factor {j₂ j₃ M x : ℝ}
    (h : x ^ 2 - (j₂ - j₃) ^ 2 = 0 ∨ (j₂ + j₃ + 1) ^ 2 - x ^ 2 = 0 ∨ x ^ 2 - M ^ 2 = 0) :
    E3 j₂ j₃ M x = 0 := by
  unfold E3
  have : (x ^ 2 - (j₂ - j₃) ^ 2) * ((j₂ + j₃ + 1) ^ 2 - x ^ 2) * (x ^ 2 - M ^ 2) = 0 := by
    rcases h with h | h | h <;> rw [h] <;> ring
  rw [this, Real.sqrt_zero]

/-- The lower neighbour of an inadmissible rank is admissible only if `E₃(L) = 0`. -/
lemma E3_down {j₂ j₃ M L : ℚ} (h : ¬ LAdm j₂ j₃ M L) (hn : LAdm j₂ j₃ M (L - 1)) :
    E3 (j₂ : ℝ) (j₃ : ℝ) (M : ℝ) (L : ℝ) = 0 := by
  obtain ⟨⟨n1, n2, n3⟩, n4, n5⟩ := hn
  have c1 : IsNat (L + j₂ - j₃) := by convert tj_isNat_add_one n1 using 1; ring
  have c2 : IsNat (L - j₂ + j₃) := by convert tj_isNat_add_one n2 using 1; ring
  have c4 : IsNat (L + M) := by convert tj_isNat_add_one n4 using 1; ring
  have c5 : IsNat (L - M) := by convert tj_isNat_add_one n5 using 1; ring
  by_cases c3 : IsNat (-L + j₂ + j₃)
  · exact absurd ⟨⟨c1, c2, c3⟩, c4, c5⟩ h
  · apply E3_eq_zero_of_factor; right; left
    have := tj_succ_zero (y := -L + j₂ + j₃) (by convert n3 using 1; ring) c3
    have h' : L = j₂ + j₃ + 1 := by linarith
    have : (L : ℝ) = j₂ + j₃ + 1 := by exact_mod_cast h'
    rw [this]; ring

/-- The upper neighbour of an inadmissible rank is admissible only if `E₃(L+1) = 0`. -/
lemma E3_up {j₂ j₃ M L : ℚ} (h : ¬ LAdm j₂ j₃ M L) (hn : LAdm j₂ j₃ M (L + 1)) :
    E3 (j₂ : ℝ) (j₃ : ℝ) (M : ℝ) ((L : ℝ) + 1) = 0 := by
  obtain ⟨⟨n1, n2, n3⟩, n4, n5⟩ := hn
  have c3 : IsNat (-L + j₂ + j₃) := by convert tj_isNat_add_one n3 using 1; ring
  by_cases c1 : IsNat (L + j₂ - j₃)
  · by_cases c2 : IsNat (L - j₂ + j₃)
    · by_cases c4 : IsNat (L + M)
      · by_cases c5 : IsNat (L - M)
        · exact absurd ⟨⟨c1, c2, c3⟩, c4, c5⟩ h
        · apply E3_eq_zero_of_factor; right; right
          have := tj_succ_zero (y := L - M) (by convert n5 using 1; ring) c5
          have h' : L + 1 = M := by linarith
          have : (L : ℝ) + 1 = M := by exact_mod_cast h'
          rw [this]; ring
      · apply E3_eq_zero_of_factor; right; right
        have := tj_succ_zero (y := L + M) (by convert n4 using 1; ring) c4
        have h' : L + 1 = -M := by linarith
        have : (L : ℝ) + 1 = -M := by exact_mod_cast h'
        rw [this]; ring
    · apply E3_eq_zero_of_factor; left
      have := tj_succ_zero (y := L - j₂ + j₃) (by convert n2 using 1; ring) c2
      have h' : L + 1 = j₂ - j₃ := by linarith
      have : (L : ℝ) + 1 = j₂ - j₃ := by exact_mod_cast h'
      rw [this]; ring
  · apply E3_eq_zero_of_factor; left
    have := tj_succ_zero (y := L + j₂ - j₃) (by convert n1 using 1; ring) c1
    have h' : L + 1 = j₃ - j₂ := by linarith
    have : (L : ℝ) + 1 = j₃ - j₂ := by exact_mod_cast h'
    rw [this]; ring

/-- **DLMF 34.3.15** for `tt`, for every rational `L` and `m`. -/
theorem tt_rec_L (j₂ j₃ M L m : ℚ) :
    (2 * (L : ℝ) + 1) * ((((j₂ : ℝ) * (j₂ + 1) - j₃ * (j₃ + 1)) * M -
        L * (L + 1) * ((((-M - m : ℚ)) : ℝ) - m))) * tt j₂ j₃ M L m =
      ((L : ℝ) + 1) * E3 j₂ j₃ M (L : ℝ) * tt j₂ j₃ M (L - 1) m
        + (L : ℝ) * E3 j₂ j₃ M ((L : ℝ) + 1) * tt j₂ j₃ M (L + 1) m := by
  by_cases hc : LAdm j₂ j₃ M L
  · obtain ⟨h, h1, h2⟩ := hc
    have e := threeJ_recurrence_all L j₂ j₃ M m (-M - m) (by ring) h h1 h2
    exact e
  · have z0 : tt j₂ j₃ M L m = 0 := tt_eq_zero_of_not_ladm L m hc
    have z1 : E3 j₂ j₃ M ((L : ℝ) + 1) * tt j₂ j₃ M (L + 1) m = 0 := by
      by_cases hu : LAdm j₂ j₃ M (L + 1)
      · rw [E3_up hc hu]; ring
      · rw [tt_eq_zero_of_not_ladm (L + 1) m hu]; ring
    have z2 : E3 j₂ j₃ M (L : ℝ) * tt j₂ j₃ M (L - 1) m = 0 := by
      by_cases hd : LAdm j₂ j₃ M (L - 1)
      · rw [E3_down hc hd]; ring
      · rw [tt_eq_zero_of_not_ladm (L - 1) m hd]; ring
    rw [z0]
    linear_combination -((L : ℝ) + 1) * z2 - (L : ℝ) * z1

/-! ### Summation over the projection -/

/-- `∑ₘ tt L m · tt L' m`. -/
noncomputable def TOA (j₂ j₃ M L L' : ℚ) : ℝ :=
  msum j₂ (fun m => tt j₂ j₃ M L m * tt j₂ j₃ M L' m)

/-- `∑ₘ m · tt L m · tt L' m`. -/
noncomputable def TOB (j₂ j₃ M L L' : ℚ) : ℝ :=
  msum j₂ (fun m => (m : ℝ) * (tt j₂ j₃ M L m * tt j₂ j₃ M L' m))

lemma TOA_symm (j₂ j₃ M L L' : ℚ) : TOA j₂ j₃ M L L' = TOA j₂ j₃ M L' L := by
  unfold TOA; apply msum_congr; intro x; ring

lemma TOB_symm (j₂ j₃ M L L' : ℚ) : TOB j₂ j₃ M L L' = TOB j₂ j₃ M L' L := by
  unfold TOB; apply msum_congr; intro x; ring

/-- The recurrence in `L`, summed over `m` against `tt L'`. -/
lemma tt_sum_relation (j₂ j₃ M L L' : ℚ) :
    ((2 * (L : ℝ) + 1) * (((j₂ : ℝ) * (j₂ + 1) - j₃ * (j₃ + 1)) * M + L * (L + 1) * M)) *
        TOA j₂ j₃ M L L' + (2 * (2 * (L : ℝ) + 1) * L * (L + 1)) * TOB j₂ j₃ M L L' =
      ((L : ℝ) + 1) * E3 j₂ j₃ M (L : ℝ) * TOA j₂ j₃ M (L - 1) L' +
        (L : ℝ) * E3 j₂ j₃ M ((L : ℝ) + 1) * TOA j₂ j₃ M (L + 1) L' := by
  have hz : ∀ (ρ : ℚ) (x : ℚ), x < -j₂ → tt j₂ j₃ M ρ x * tt j₂ j₃ M L' x = 0 := by
    intro ρ x hx; rw [tt_neg_m j₂ j₃ M ρ hx]; ring
  have hz2 : ∀ (ρ : ℚ) (x : ℚ), x < -j₂ → (x : ℝ) * (tt j₂ j₃ M ρ x * tt j₂ j₃ M L' x) = 0 := by
    intro ρ x hx; rw [hz ρ x hx]; ring
  have h := msum_congr (a := j₂)
    (f := fun x : ℚ => ((2 * (L : ℝ) + 1) * (((j₂ : ℝ) * (j₂ + 1) - j₃ * (j₃ + 1)) * M +
          L * (L + 1) * M)) * (tt j₂ j₃ M L x * tt j₂ j₃ M L' x) +
        (2 * (2 * (L : ℝ) + 1) * L * (L + 1)) * ((x : ℝ) * (tt j₂ j₃ M L x * tt j₂ j₃ M L' x)))
    (g := fun x : ℚ => (((L : ℝ) + 1) * E3 j₂ j₃ M (L : ℝ)) *
        (tt j₂ j₃ M (L - 1) x * tt j₂ j₃ M L' x) +
      ((L : ℝ) * E3 j₂ j₃ M ((L : ℝ) + 1)) * (tt j₂ j₃ M (L + 1) x * tt j₂ j₃ M L' x))
    (by
      intro x
      have := tt_rec_L j₂ j₃ M L x
      push_cast at this
      linear_combination (tt j₂ j₃ M L' x) * this)
  rw [msum_comb (fun x hx => by simp [hz L x hx]) (hz2 L), msum_comb (hz (L - 1)) (hz (L + 1))]
    at h
  unfold TOA TOB
  linear_combination h

lemma E3_ne_zero_of_adm {j₂ j₃ M L : ℚ} (h : LAdm j₂ j₃ M L) (h' : LAdm j₂ j₃ M (L + 1)) :
    E3 (j₂ : ℝ) (j₃ : ℝ) (M : ℝ) ((L : ℝ) + 1) ≠ 0 := by
  obtain ⟨⟨⟨p1, hp1⟩, ⟨p2, hp2⟩, ⟨p3, hp3⟩⟩, ⟨q1, hq1⟩, ⟨q2, hq2⟩⟩ := h
  obtain ⟨⟨⟨-, -⟩, -, ⟨p3', hp3'⟩⟩, -, -⟩ := h'
  have e1 : (L : ℝ) + j₂ - j₃ = p1 := by exact_mod_cast hp1
  have e2 : (L : ℝ) - j₂ + j₃ = p2 := by exact_mod_cast hp2
  have e3 : -((L : ℝ) + 1) + j₂ + j₃ = p3' := by
    exact_mod_cast (by linarith : -(L + 1) + j₂ + j₃ = p3')
  have f1 : (L : ℝ) + M = q1 := by exact_mod_cast hq1
  have f2 : (L : ℝ) - M = q2 := by exact_mod_cast hq2
  have n1 : (0 : ℝ) ≤ p1 := by positivity
  have n2 : (0 : ℝ) ≤ p2 := by positivity
  have n3 : (0 : ℝ) ≤ p3' := by positivity
  have m1 : (0 : ℝ) ≤ q1 := by positivity
  have m2 : (0 : ℝ) ≤ q2 := by positivity
  unfold E3
  apply (Real.sqrt_pos.mpr _).ne'
  have g1 : 0 < ((L : ℝ) + 1) ^ 2 - ((j₂ : ℝ) - j₃) ^ 2 := by
    have : ((L : ℝ) + 1) ^ 2 - ((j₂ : ℝ) - j₃) ^ 2 =
        ((L : ℝ) + 1 + j₂ - j₃) * ((L : ℝ) + 1 - j₂ + j₃) := by ring
    rw [this]; apply mul_pos <;> linarith
  have g2 : 0 < ((j₂ : ℝ) + j₃ + 1) ^ 2 - ((L : ℝ) + 1) ^ 2 := by
    have : ((j₂ : ℝ) + j₃ + 1) ^ 2 - ((L : ℝ) + 1) ^ 2 =
        ((j₂ : ℝ) + j₃ + 1 - (L + 1)) * ((j₂ : ℝ) + j₃ + 1 + (L + 1)) := by ring
    rw [this]; apply mul_pos <;> linarith
  have g3 : 0 < ((L : ℝ) + 1) ^ 2 - (M : ℝ) ^ 2 := by
    have : ((L : ℝ) + 1) ^ 2 - (M : ℝ) ^ 2 = ((L : ℝ) + 1 + M) * ((L : ℝ) + 1 - M) := by ring
    rw [this]; apply mul_pos <;> linarith
  positivity

lemma LAdm.nonneg {j₂ j₃ M L : ℚ} (h : LAdm j₂ j₃ M L) : 0 ≤ L := by
  obtain ⟨⟨⟨n, hn⟩, ⟨m, hm⟩, -⟩, -⟩ := h
  have : (0 : ℚ) ≤ n + m := by positivity
  linarith

/-- **Norm ratio**: for `L > 0` and `L`, `L+1` admissible,
`(2L+3) ∑ₘ tt(L+1)² = (2L+1) ∑ₘ tt L²`. -/
theorem tt_norm_ratio (j₂ j₃ M L : ℚ) (hL : 0 < L) (h : LAdm j₂ j₃ M L)
    (h' : LAdm j₂ j₃ M (L + 1)) :
    (2 * (L : ℝ) + 3) * TOA j₂ j₃ M (L + 1) (L + 1) = (2 * (L : ℝ) + 1) * TOA j₂ j₃ M L L := by
  have hF := E3_ne_zero_of_adm h h'
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have o1 : TOA j₂ j₃ M L (L + 1) = 0 := tt_orth_offdiag j₂ j₃ M L (L + 1) (by
    push_cast; intro h; nlinarith)
  have o2 : TOA j₂ j₃ M (L - 1) (L + 1) = 0 := tt_orth_offdiag j₂ j₃ M (L - 1) (L + 1) (by
    push_cast; intro h; nlinarith)
  have o3 : TOA j₂ j₃ M (L + 1 + 1) L = 0 := tt_orth_offdiag j₂ j₃ M (L + 1 + 1) L (by
    push_cast; intro h; nlinarith)
  have o4 : TOA j₂ j₃ M (L + 1) L = 0 := by rw [TOA_symm, o1]
  have h1 := tt_sum_relation j₂ j₃ M L (L + 1)
  have h2 := tt_sum_relation j₂ j₃ M (L + 1) L
  rw [o1, o2] at h1
  rw [o3, o4, add_sub_cancel_right, TOB_symm j₂ j₃ M (L + 1) L] at h2
  push_cast at h1 h2 hF
  have hne : (L : ℝ) * ((L : ℝ) + 2) * E3 j₂ j₃ M ((L : ℝ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hne
  linear_combination (-(2 * (L : ℝ) + 3) * ((L : ℝ) + 2)) * h1 +
    ((L : ℝ) * (2 * L + 1)) * h2

/-- info: 'FormalResearch.Wigner.tt_rec_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tt_rec_L

/-- info: 'FormalResearch.Wigner.tt_norm_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tt_norm_ratio

end FormalResearch.Wigner
