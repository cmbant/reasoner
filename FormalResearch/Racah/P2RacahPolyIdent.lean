module

public import FormalResearch.Racah.P2RacahPolyMain

/-!
# The physical ratio is the terminating Racah polynomial (Weyl P2, `eq:physicalRacahExplicit`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, subsection *Explicit physical Racah-polynomial
realization*.  Canonical sector `|n| ≤ m`.  With the standard terminating Racah polynomial
`Q^R_r(y) = ₄F₃(-r, r+2m+1, -y, y+2c_min+1; m-n+1, m+n+c_min+c_max+2, -D; 1)` (`racahPoly` with the
parameters `α = m-n`, `β = m+n`, `γ = -D-1`, `δ = c_min+c_max+1` of `eq:physicalRacahParameters`) we
prove, for `0 ≤ r, y ≤ D`,

`Φ_{m+r}(c_min+y)/Φ_m(c_min+y) = [Φ_{m+r}(c_min)/Φ_m(c_min)] · Q^R_r(y)`   (`ppR_eq_racahPoly`),

i.e. `eq:physicalRacahExplicit` after multiplying by the orthonormalising factor
`√((2(m+r)+1)/(2m+1))` (`physR_eq`).  The proof is the uniqueness of the solution of the three-term
difference equation (`ppR_row` for the left side, `racahPoly_diff` for the right) with the given value
at `y = 0` (the lower end has `D(0) = 0` and `B(y) ≠ 0` for `y < D`).
-/

@[expose] public section

namespace FormalResearch.Racah.SixJ

open FormalResearch.Wigner FormalResearch.Racah.RacahPoly

/-- The physical Racah parameters `α, β, γ, δ` (`eq:physicalRacahParameters`) packaged as the
polynomial `Q^R_r(y) = ₄F₃(-r, r+2m+1, -y, y+2c_min+1; m-n+1, m+n+c_min+c_max+2, -D; 1)`. -/
noncomputable def physQ (a b m n : ℚ) (D : ℕ) (r : ℕ) (y : ℝ) : ℝ :=
  racahPoly ((m : ℝ) - n) ((m : ℝ) + n) (-(D : ℝ) - 1)
    ((cMin a b m n : ℝ) + (cMax a b m n : ℝ) + 1) r y

lemma phys_D_real {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) :
    (D : ℝ) = (cMax a b m n : ℝ) - (cMin a b m n : ℝ) := by
  exact_mod_cast h.dim

lemma physQ_diff {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (hcan : |n| ≤ m) (r : ℕ)
    (hr : r ≤ D) (y : ℕ) :
    physRacahB a b m n D y * (physQ a b m n D r (y + 1) - physQ a b m n D r y) +
        physRacahD a b m n D y * (physQ a b m n D r ((y : ℝ) - 1) - physQ a b m n D r y) =
      (r : ℝ) * (r + 2 * m + 1) * physQ a b m n D r y := by
  have hD := phys_D_real h
  have hmn := abs_le.1 hcan
  have hc0 : (0 : ℝ) ≤ (cMin a b m n : ℝ) := by exact_mod_cast cMin_nonneg a b m n
  have hDn : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ (m : ℝ) - n := by
    have : (n : ℝ) ≤ m := by exact_mod_cast hmn.2
    linarith
  have hm1 : (0 : ℝ) ≤ (m : ℝ) + n := by
    have : (-m : ℝ) ≤ n := by exact_mod_cast hmn.1
    linarith
  have hy : (0 : ℝ) ≤ y := Nat.cast_nonneg _
  have := racahPoly_diff ((m : ℝ) - n) ((m : ℝ) + n) (-(D : ℝ) - 1)
    ((cMin a b m n : ℝ) + (cMax a b m n : ℝ) + 1) r (y : ℝ)
    (by
      intro hy0
      have : (0 : ℝ) < y := lt_of_le_of_ne hy (Ne.symm hy0)
      intro e0; linarith)
    (by intro e0; linarith)
    (by intro e0; linarith)
    (fun i _ => by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
    (fun i _ => by
      have : (0 : ℝ) ≤ (cMax a b m n : ℝ) := by linarith
      linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
    (fun i hi => by
      have : (i : ℝ) + 1 ≤ D := by exact_mod_cast (show i + 1 ≤ D by omega)
      linarith)
  have e : (r : ℝ) * (r + ((m : ℝ) - n) + ((m : ℝ) + n) + 1) = (r : ℝ) * (r + 2 * m + 1) := by ring
  rw [e] at this
  simpa [racahL, physQ, physRacahB, physRacahD] using this

lemma physRacahB_ne {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (hcan : |n| ≤ m) (y : ℕ)
    (hy : y < D) : physRacahB a b m n D (y : ℝ) ≠ 0 := by
  have hm := mem_rank h hcan 0 (Nat.zero_le _)
  simp only [Nat.cast_zero, add_zero] at hm
  have hc := mem_lattice h y hy.le
  have hc' := mem_lattice h (y + 1) hy
  push_cast at hc'
  have hN := seedN_pos a b (cMin a b m n + y) m n hm.2 hc.1 hc.2
    (by simpa [add_assoc] using hc'.1) (by simpa [add_assoc] using hc'.2)
  rw [physRacahB_eq h hcan]
  have h0 : (0 : ℝ) ≤ (cMin a b m n : ℝ) := by exact_mod_cast cMin_nonneg a b m n
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg _
  have hN' : 0 < seedN a b m n ((cMin a b m n : ℝ) + y) := by
    have := hN; push_cast at this; exact this
  have : 0 < (2 * ((cMin a b m n : ℝ) + y) + 1) * (2 * ((cMin a b m n : ℝ) + y) + 2) := by
    apply mul_pos <;> linarith
  exact div_ne_zero (neg_ne_zero.2 hN'.ne') this.ne'

/-- **`eq:physicalRacahExplicit`, unnormalised form.**  In the canonical sector, for `0 ≤ r, y ≤ D`,
`Φ_{m+r}(c_min+y)/Φ_m(c_min+y) = [Φ_{m+r}(c_min)/Φ_m(c_min)] · Q^R_r(y)` with `Q^R_r` the terminating
Racah polynomial `₄F₃(-r, r+2m+1, -y, y+2c_min+1; m-n+1, m+n+c_min+c_max+2, -D; 1)`
(`eq:physicalRacah4F3`, `eq:physicalRacahParameters`).  Literal. -/
theorem ppR_eq_racahPoly {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (hcan : |n| ≤ m)
    (r y : ℕ) (hr : r ≤ D) (hy : y ≤ D) :
    ppR a b m n r y = ppR a b m n r 0 * physQ a b m n D r (y : ℝ) := by
  set e : ℕ → ℝ := fun k => ppR a b m n r k - ppR a b m n r 0 * physQ a b m n D r (k : ℝ) with he
  have hrec : ∀ k : ℕ, k ≤ D →
      physRacahB a b m n D k * (e (k + 1) - e k) +
        physRacahD a b m n D k * (e (k - 1) - e k) = (r : ℝ) * (r + 2 * m + 1) * e k := by
    intro k hk
    have h1 := ppR_row h hcan r k hr hk
    have h2 := physQ_diff h hcan r hr k
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      simp only [Nat.cast_zero, physRacahD_zero, zero_mul, add_zero] at h1 h2 ⊢
      simp only [he]
      push_cast at h1 h2 ⊢
      rw [zero_add] at h2
      linear_combination h1 - ppR a b m n r 0 * h2
    · have hk1 : (((k - 1 : ℕ)) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub hpos]; simp
      simp only [he]
      rw [hk1]
      push_cast at h1 h2 ⊢
      linear_combination h1 - ppR a b m n r 0 * h2
  have e0 : e 0 = 0 := by
    simp only [he, Nat.cast_zero, racahPoly_zero, physQ, mul_one, sub_self]
  have key : ∀ k : ℕ, k ≤ D → e k = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0]; exact e0
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have hj := ih j (by omega) (by omega)
        have hjm : e (j - 1) = 0 := by
          rcases Nat.eq_zero_or_pos j with h0 | hp
          · rw [h0]; exact e0
          · exact ih (j - 1) (by omega) (by omega)
        have := hrec j (by omega)
        rw [hj, hjm] at this
        have hB := physRacahB_ne h hcan j (by omega)
        have : physRacahB a b m n D j * e (j + 1) = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hB
  have := key y hy
  simp only [he] at this
  linarith

/-- info: 'FormalResearch.Racah.SixJ.ppR_eq_racahPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppR_eq_racahPoly

end FormalResearch.Racah.SixJ
