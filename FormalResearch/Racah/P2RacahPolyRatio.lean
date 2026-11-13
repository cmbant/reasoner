module

public import FormalResearch.Racah.P2RacahPolyShift
public import FormalResearch.Racah.P2RacahPolyDiff

/-!
# The seed ratios are the Racah coefficients (Weyl P2, `eq:physicalRacahParameters`,
`eq:RacahGroundTransform`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, subsection *Explicit physical Racah-polynomial
realization*.  Fix the canonical sector `|n| ≤ m` (so `f_0 = m`, `c_max = a+b`) and the physical Racah
parameters `α = m-n`, `β = m+n`, `γ = -D-1`, `δ = c_min+c_max+1` (`D = c_max - c_min`).  This file
proves that the two off-diagonal coefficients of the ground-state transform
`Φ_m^{-1}(H_R - m(m+1))Φ_m` are the standard Racah coefficients:

* `offPlus`: `a_c^+ Φ_m(c+1) = -B(y) Φ_m(c)`,
* `offMinus`: `a_c^- Φ_m(c-1) = -D(y) Φ_m(c)`,

at every `c = c_min + y`, `0 ≤ y ≤ D` (zero at the two ends on both sides), where `B`, `D` are
`RacahPoly.racahB`, `RacahPoly.racahD`.  They come from `aPlus_mul_seed`, `aMinus_mul_seed`
(`P2RacahPolyShift`) and the algebraic identities `racahB_alg`, `racahD_alg`:
`B(y) = -N₁(c)/((2c+1)(2c+2))`, `D(y+1) = -D₁(c)/((2c+2)(2c+3))`.
-/

@[expose] public section

namespace FormalResearch.Racah.SixJ

open FormalResearch.Wigner FormalResearch.Racah.RacahPoly

/-! ### Algebra: the Racah coefficients in the labels `a, b, m, n` -/

lemma racahB_alg (a b m n y cmin α β γ δ : ℝ) (hc : cmin = a - b ∨ cmin = b + m - a - n)
    (hα : α = m - n) (hβ : β = m + n) (hγ : γ = -(a + b - cmin) - 1) (hδ : δ = cmin + (a + b) + 1) :
    racahB α β γ δ y =
      -seedN a b m n (cmin + y) / ((2 * (cmin + y) + 1) * (2 * (cmin + y) + 2)) := by
  subst hα hβ hγ hδ
  unfold racahB seedN
  have e : (2 * y + (-(a + b - cmin) - 1) + (cmin + (a + b) + 1) + 1) *
      (2 * y + (-(a + b - cmin) - 1) + (cmin + (a + b) + 1) + 2) =
      (2 * (cmin + y) + 1) * (2 * (cmin + y) + 2) := by ring
  rw [e]
  congr 1
  rcases hc with rfl | rfl <;> ring

lemma racahD_alg (a b m n y cmin α β γ δ : ℝ) (hc : cmin = a - b ∨ cmin = b + m - a - n)
    (hα : α = m - n) (hβ : β = m + n) (hγ : γ = -(a + b - cmin) - 1) (hδ : δ = cmin + (a + b) + 1) :
    racahD α β γ δ (y + 1) =
      -seedD a b m n (cmin + y) / ((2 * (cmin + y) + 2) * (2 * (cmin + y) + 3)) := by
  subst hα hβ hγ hδ
  unfold racahD seedD
  have e : (2 * (y + 1) + (-(a + b - cmin) - 1) + (cmin + (a + b) + 1)) *
      (2 * (y + 1) + (-(a + b - cmin) - 1) + (cmin + (a + b) + 1) + 1) =
      (2 * (cmin + y) + 2) * (2 * (cmin + y) + 3) := by ring
  rw [e]
  congr 1
  rcases hc with rfl | rfl <;> ring

/-! ### The canonical sector -/

lemma cMax_eq_of_canonical {a b m n : ℚ} (hcan : |n| ≤ m) : cMax a b m n = a + b := by
  have := (abs_le.1 hcan).1
  unfold cMax
  exact min_eq_left (by linarith)

lemma cMin_cases_of_canonical (a b m n : ℚ) (hcan : |n| ≤ m) :
    cMin a b m n = a - b ∨ cMin a b m n = b + m - a - n := by
  have h1 := (abs_le.1 hcan)
  have hmn : |m - n| = m - n := abs_of_nonneg (by linarith [h1.2])
  rw [cMin_centered, hmn]
  rcases abs_cases ((a + (n + 1) / 2) - (b + (m + 1) / 2)) with ⟨h, h'⟩ | ⟨h, h'⟩
  · left; rw [h]; linarith
  · right; rw [h]; linarith

lemma fMin_eq_of_canonical {m n : ℚ} (hcan : |n| ≤ m) : fMin m n = m := by
  have h0 : 0 ≤ m := le_trans (abs_nonneg _) hcan
  unfold fMin
  rw [abs_of_nonneg h0]
  exact max_eq_left hcan

/-! ### The physical Racah coefficients -/

/-- `B(y)` of the physical Racah parameters `α = m-n`, `β = m+n`, `γ = -D-1`,
`δ = c_min+c_max+1` (`eq:physicalRacahParameters`). -/
noncomputable def physRacahB (a b m n : ℚ) (D : ℕ) (y : ℝ) : ℝ :=
  racahB ((m : ℝ) - n) ((m : ℝ) + n) (-(D : ℝ) - 1) ((cMin a b m n : ℝ) + (cMax a b m n : ℝ) + 1) y

/-- `D(y)` of the physical Racah parameters. -/
noncomputable def physRacahD (a b m n : ℚ) (D : ℕ) (y : ℝ) : ℝ :=
  racahD ((m : ℝ) - n) ((m : ℝ) + n) (-(D : ℝ) - 1) ((cMin a b m n : ℝ) + (cMax a b m n : ℝ) + 1) y

lemma phys_params {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (hcan : |n| ≤ m) :
    ((cMin a b m n : ℝ) = a - b ∨ (cMin a b m n : ℝ) = b + m - a - n) ∧
    (-(D : ℝ) - 1 = -((a : ℝ) + b - (cMin a b m n : ℝ)) - 1) ∧
    ((cMin a b m n : ℝ) + (cMax a b m n : ℝ) + 1 = (cMin a b m n : ℝ) + ((a : ℝ) + b) + 1) := by
  have hmax := cMax_eq_of_canonical (a := a) (b := b) hcan
  have hD : (D : ℚ) = a + b - cMin a b m n := by rw [h.dim, hmax]
  have hD' : (D : ℝ) = (a : ℝ) + b - (cMin a b m n : ℝ) := by exact_mod_cast hD
  refine ⟨?_, by rw [hD'], by rw [hmax]; push_cast; ring⟩
  rcases cMin_cases_of_canonical a b m n hcan with h1 | h1
  · left; rw [h1]; push_cast; ring
  · right; rw [h1]; push_cast; ring

theorem physRacahB_eq {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (hcan : |n| ≤ m) (y : ℝ) :
    physRacahB a b m n D y =
      -seedN a b m n ((cMin a b m n : ℝ) + y) /
        ((2 * ((cMin a b m n : ℝ) + y) + 1) * (2 * ((cMin a b m n : ℝ) + y) + 2)) := by
  obtain ⟨h1, h2, h3⟩ := phys_params h hcan
  exact racahB_alg a b m n y (cMin a b m n : ℝ) _ _ _ _ h1 rfl rfl h2 h3

theorem physRacahD_eq {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (hcan : |n| ≤ m) (y : ℝ) :
    physRacahD a b m n D (y + 1) =
      -seedD a b m n ((cMin a b m n : ℝ) + y) /
        ((2 * ((cMin a b m n : ℝ) + y) + 2) * (2 * ((cMin a b m n : ℝ) + y) + 3)) := by
  obtain ⟨h1, h2, h3⟩ := phys_params h hcan
  exact racahD_alg a b m n y (cMin a b m n : ℝ) _ _ _ _ h1 rfl rfl h2 h3

lemma physRacahD_zero (a b m n : ℚ) (D : ℕ) : physRacahD a b m n D 0 = 0 := by
  simp [physRacahD, racahD]

lemma physRacahB_top (a b m n : ℚ) (D : ℕ) : physRacahB a b m n D (D : ℝ) = 0 := by
  unfold physRacahB racahB
  have : (D : ℝ) + (-(D : ℝ) - 1) + 1 = 0 := by ring
  rw [this]; simp

/-! ### The off-diagonal coefficients of the ground-state transform -/

lemma mem_lattice {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (y : ℕ) (hy : y ≤ D) :
    cMin a b m n + (y : ℚ) ∈ physC a b m n := by
  have := cPt_mem h ⟨y, by omega⟩
  simpa [cPt] using this

lemma mem_rank {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (hcan : |n| ≤ m) (r : ℕ)
    (hr : r ≤ D) : m + (r : ℚ) ∈ physF a b m n := by
  have := fPt_mem h ⟨r, by omega⟩
  simpa [fPt, fMin_eq_of_canonical hcan] using this

/-- **Upper ratio of the seed**: `a_c^+ Φ_m(c+1) = -B(y) Φ_m(c)` at `c = c_min + y`, `0 ≤ y ≤ D`. -/
theorem offPlus {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (hcan : |n| ≤ m) (y : ℕ)
    (hy : y ≤ D) :
    aPlus a b m n ((cMin a b m n + y : ℚ) : ℝ) * Phi6 a b (cMin a b m n + y + 1) m m n =
      -physRacahB a b m n D (y : ℝ) * Phi6 a b (cMin a b m n + y) m m n := by
  rcases hy.lt_or_eq with hlt | heq
  · have hm := mem_rank h hcan 0 (Nat.zero_le _)
    simp only [Nat.cast_zero, add_zero] at hm
    have hc := mem_lattice h y hy
    have hc' := mem_lattice h (y + 1) (by omega)
    push_cast at hc'
    have := aPlus_mul_seed a b (cMin a b m n + y) m n hm.1 hm.2 hc.1 hc.2 (by simpa [add_assoc] using hc'.1)
      (by simpa [add_assoc] using hc'.2)
    rw [this, physRacahB_eq h hcan]
    push_cast
    ring
  · have hz : aPlus a b m n ((cMin a b m n + y : ℚ) : ℝ) = 0 := by
      have hc : cMin a b m n + (y : ℚ) = cMax a b m n := by
        rw [heq, h.dim]; ring
      rw [hc]; unfold aPlus; rw [edgeA_cMax_succ]; simp
    have hB : physRacahB a b m n D (y : ℝ) = 0 := by rw [heq]; exact physRacahB_top a b m n D
    rw [hz, hB]; ring

/-- **Lower ratio of the seed**: `a_c^- Φ_m(c-1) = -D(y) Φ_m(c)` at `c = c_min + y`, `0 ≤ y ≤ D`. -/
theorem offMinus {a b m n : ℚ} {D : ℕ} (h : RacahSystem a b m n D) (hcan : |n| ≤ m) (y : ℕ)
    (hy : y ≤ D) :
    aMinus a b m n ((cMin a b m n + y : ℚ) : ℝ) * Phi6 a b (cMin a b m n + y - 1) m m n =
      -physRacahD a b m n D (y : ℝ) * Phi6 a b (cMin a b m n + y) m m n := by
  rcases Nat.eq_zero_or_pos y with h0 | hpos
  · subst h0
    have hz : aMinus a b m n ((cMin a b m n + ((0 : ℕ) : ℚ) : ℚ) : ℝ) = 0 := by
      simp only [Nat.cast_zero, add_zero]
      unfold aMinus; rw [edgeA_cMin]; simp
    rw [hz]; simp [physRacahD_zero]
  · obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    have hm := mem_rank h hcan 0 (Nat.zero_le _)
    simp only [Nat.cast_zero, add_zero] at hm
    have hc := mem_lattice h y' (by omega)
    have hc' := mem_lattice h (y' + 1) hy
    push_cast at hc' ⊢
    have := aMinus_mul_seed a b (cMin a b m n + y') m n hm.1 hm.2 hc.1 hc.2
      (by simpa [add_assoc] using hc'.1) (by simpa [add_assoc] using hc'.2)
    have e1 : cMin a b m n + (y' + 1) - 1 = cMin a b m n + y' := by ring
    have e2 : cMin a b m n + (y' + 1) = cMin a b m n + y' + 1 := by ring
    rw [e1, e2]
    have e3 : (cMin a b m n : ℝ) + ((y' : ℝ) + 1) = (cMin a b m n : ℝ) + y' + 1 := by ring
    rw [e3, physRacahD_eq h hcan]
    push_cast at this ⊢
    rw [this]
    ring

/-- info: 'FormalResearch.Racah.SixJ.offPlus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms offPlus

/-- info: 'FormalResearch.Racah.SixJ.offMinus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms offMinus

end FormalResearch.Racah.SixJ
