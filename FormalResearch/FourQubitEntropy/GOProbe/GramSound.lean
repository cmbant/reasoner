module

public import Mathlib

/-!
# GO certificate probe: soundness of the compact Gram positivity test

`eq:fqe-compact-gram-test` of `global_overlap_certificate.tex`: if `G - A Aᵀ/s²` is diagonally dominant then
`G` is positive semidefinite.  This file proves the real-analysis half (`quad_nonneg_of_dd`); the integer half
(that `gramOK` implies its hypotheses, via the rounding bound `|H - g (AAᵀ)/s²| ≤ 1/2` for
`H = (g·dot + s²/2) / s²`) is the remaining obligation (see the probe report).  Claim class: proved.
-/

@[expose] public section


open Finset

namespace FormalResearch.FourQubitEntropy.GOProbe

/-- A symmetric real matrix with `∑_{j ≠ i} |E_ij| ≤ E_ii` has nonnegative quadratic form. -/
theorem quad_nonneg_of_dd {m : ℕ} (E : Fin m → Fin m → ℝ) (hsym : ∀ i j, E i j = E j i)
    (hdd : ∀ i, ∑ j, (if i = j then (0 : ℝ) else |E i j|) ≤ E i i) (x : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * E i j * x j := by
  set g : Fin m → Fin m → ℝ := fun i j => if i = j then 0 else |E i j| with hg
  have hgs : ∀ i j, g i j = g j i := by
    intro i j
    simp only [hg]
    by_cases h : i = j
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), hsym]
  have hg0 : ∀ i j, 0 ≤ g i j := by
    intro i j; simp only [hg]; split_ifs <;> positivity
  -- pointwise bound
  have hpt : ∀ i j, (if i = j then E i i * (x i) ^ 2 else 0) - g i j * ((x i) ^ 2 + (x j) ^ 2) / 2
      ≤ x i * E i j * x j := by
    intro i j
    by_cases h : i = j
    · subst h
      have h0 : g i i = 0 := by simp [hg]
      rw [if_pos rfl, h0]
      apply le_of_eq
      ring
    · simp only [hg, if_neg h]
      have h2 : |E i j * (x i * x j)| ≤ |E i j| * ((x i) ^ 2 + (x j) ^ 2) / 2 := by
        rw [abs_mul]
        have h4 : |x i * x j| ≤ ((x i) ^ 2 + (x j) ^ 2) / 2 := by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x i + x j), sq_nonneg (x i - x j)]
        calc |E i j| * |x i * x j| ≤ |E i j| * (((x i) ^ 2 + (x j) ^ 2) / 2) :=
              mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
          _ = _ := by ring
      have h3 := neg_abs_le (E i j * (x i * x j))
      have h5 : x i * E i j * x j = E i j * (x i * x j) := by ring
      rw [h5]
      linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
    Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hpt i j
  refine le_trans ?_ hsum
  have hd : ∑ i : Fin m, ∑ j : Fin m, (if i = j then E i i * (x i) ^ 2 else 0)
      = ∑ i, E i i * (x i) ^ 2 := by
    simp [Finset.sum_ite_eq]
  have hswap : ∑ i : Fin m, ∑ j : Fin m, g i j * (x j) ^ 2
      = ∑ i : Fin m, ∑ j : Fin m, g i j * (x i) ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hgs]
  have hS : ∑ i : Fin m, ∑ j : Fin m, g i j * (x i) ^ 2 = ∑ i : Fin m, (∑ j, g i j) * (x i) ^ 2 := by
    simp [Finset.sum_mul]
  have hq : ∑ i : Fin m, ∑ j : Fin m, g i j * ((x i) ^ 2 + (x j) ^ 2) / 2
      = (∑ i : Fin m, ∑ j : Fin m, g i j * (x i) ^ 2) / 2
        + (∑ i : Fin m, ∑ j : Fin m, g i j * (x j) ^ 2) / 2 := by
    have e : ∀ i j, g i j * ((x i) ^ 2 + (x j) ^ 2) / 2
        = g i j * (x i) ^ 2 / 2 + g i j * (x j) ^ 2 / 2 := fun i j => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.sum_div]
  have hgoal : ∑ i : Fin m, ∑ j : Fin m,
      ((if i = j then E i i * (x i) ^ 2 else 0) - g i j * ((x i) ^ 2 + (x j) ^ 2) / 2)
      = ∑ i : Fin m, E i i * (x i) ^ 2 - ∑ i : Fin m, ∑ j : Fin m, g i j * ((x i) ^ 2 + (x j) ^ 2) / 2 := by
    rw [← hd, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_sub_distrib]
  rw [hgoal, hq, hswap, hS]
  have key : 0 ≤ ∑ i : Fin m, (E i i * (x i) ^ 2 - (∑ j, g i j) * (x i) ^ 2) :=
    Finset.sum_nonneg fun i _ => by
      have := mul_nonneg (sub_nonneg.2 (hdd i)) (sq_nonneg (x i))
      nlinarith [this]
  rw [Finset.sum_sub_distrib] at key
  linarith


/-! ### Rounding and the compact Gram test -/

/-- `H = (g d + s/2) / s` satisfies `|s H - g d| ≤ s/2` (for even `s > 0`). -/
theorem round_err (g d s : ℤ) (hs : 0 < s) (h2 : (2 : ℤ) ∣ s) :
    |s * ((g * d + s / 2) / s) - g * d| ≤ s / 2 := by
  obtain ⟨t, rfl⟩ := h2
  have ht : 2 * t / 2 = t := by omega
  have hdiv := Int.emod_add_mul_ediv (g * d + t) (2 * t)
  have h0 := Int.emod_nonneg (g * d + t) (ne_of_gt hs)
  have h1 := Int.emod_lt_of_pos (g * d + t) hs
  rw [ht]
  rw [abs_le]
  constructor <;> nlinarith

/-- Real form of the rounding bound: `|H - g d / s| ≤ 1/2`. -/
theorem round_err_real (g d s : ℤ) (hs : 0 < s) (h2 : (2 : ℤ) ∣ s) :
    |(((g * d + s / 2) / s : ℤ) : ℝ) - ((g * d : ℤ) : ℝ) / (s : ℝ)| ≤ 1 / 2 := by
  have h := round_err g d s hs h2
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have h' : |(s : ℝ) * (((g * d + s / 2) / s : ℤ) : ℝ) - ((g * d : ℤ) : ℝ)| ≤ (s : ℝ) / 2 := by
    obtain ⟨t, rfl⟩ := h2
    have ht : (2 * t) / 2 = t := by omega
    rw [ht] at h
    have h3 : ((|2 * t * ((g * d + t) / (2 * t)) - g * d| : ℤ) : ℝ) ≤ ((t : ℤ) : ℝ) := by
      exact_mod_cast h
    have h4 : (((g * d + t) / (2 * t) : ℤ) : ℝ) = (((g * d + 2 * t / 2) / (2 * t) : ℤ) : ℝ) := by
      rw [ht]
    rw [← h4]
    push_cast at h3 ⊢
    linarith
  have e : (((g * d + s / 2) / s : ℤ) : ℝ) - ((g * d : ℤ) : ℝ) / (s : ℝ)
      = ((s : ℝ) * (((g * d + s / 2) / s : ℤ) : ℝ) - ((g * d : ℤ) : ℝ)) / (s : ℝ) := by
    field_simp
  rw [e, abs_div, abs_of_pos hsR, div_le_iff₀ hsR]
  linarith


/-- The real Gram form of an integer factor is positive semidefinite. -/
theorem gram_form_nonneg {m r : ℕ} (A : Fin m → Fin r → ℤ) (x : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * (((∑ k, A i k * A j k : ℤ) : ℝ)) * x j := by
  have h1 : ∑ i : Fin m, ∑ j : Fin m, x i * (((∑ k, A i k * A j k : ℤ) : ℝ)) * x j
      = ∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin r, x i * (A i k : ℝ) * (x j * (A j k : ℝ)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h2 : ∑ k : Fin r, (∑ i : Fin m, x i * (A i k : ℝ)) ^ 2
      = ∑ k : Fin r, ∑ i : Fin m, ∑ j : Fin m, x i * (A i k : ℝ) * (x j * (A j k : ℝ)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sq, Finset.sum_mul_sum]
  have : ∑ i : Fin m, ∑ j : Fin m, x i * (((∑ k, A i k * A j k : ℤ) : ℝ)) * x j
      = ∑ k : Fin r, (∑ i : Fin m, x i * (A i k : ℝ)) ^ 2 := by
    rw [h1, h2]
    calc ∑ i : Fin m, ∑ j : Fin m, ∑ k : Fin r, x i * (A i k : ℝ) * (x j * (A j k : ℝ))
        = ∑ i : Fin m, ∑ k : Fin r, ∑ j : Fin m, x i * (A i k : ℝ) * (x j * (A j k : ℝ)) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k : Fin r, ∑ i : Fin m, ∑ j : Fin m, x i * (A i k : ℝ) * (x j * (A j k : ℝ)) :=
          Finset.sum_comm
  rw [this]
  exact Finset.sum_nonneg fun k _ => sq_nonneg _


theorem sum_ite_ne {m : ℕ} (i : Fin m) (c : ℝ) :
    ∑ j : Fin m, (if i = j then (0 : ℝ) else c) = (m : ℝ) * c - c := by
  have : ∀ j : Fin m, (if i = j then (0 : ℝ) else c) = c - (if i = j then c else 0) := by
    intro j; split_ifs <;> ring
  simp only [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Decomposition of the Gram matrix: `G = AAᵀ/s + E` with `E` symmetric and diagonally dominant. -/
theorem gram_decomp {m r : ℕ} (A : Fin m → Fin r → ℤ) (R C : Fin m → Fin m → ℤ)
    (hR : ∀ i j, R i j = R j i) (hC : ∀ i j, C i j = C j i)
    (grid s cd : ℤ) (hg : 0 < grid) (hs : 0 < s) (h2 : (2 : ℤ) ∣ s) (hcd : 0 < cd)
    (hdd : ∀ i, (m : ℤ) * cd <
      2 * ((cd * R i i + C i i) - ∑ j, if i = j then 0 else |cd * R i j + C i j|)) :
    ∃ E : Fin m → Fin m → ℝ, (∀ i j, E i j = E j i) ∧
      (∀ i, ∑ j, (if i = j then (0 : ℝ) else |E i j|) ≤ E i i) ∧
      ∀ i j, (((((grid * (∑ k, A i k * A j k) + s / 2) / s + R i j : ℤ) : ℝ)
        + (C i j : ℝ) / cd) / grid) = ((∑ k, A i k * A j k : ℤ) : ℝ) / s + E i j := by
  classical
  set dot : Fin m → Fin m → ℤ := fun i j => ∑ k, A i k * A j k with hdot
  have hdots : ∀ i j, dot i j = dot j i := fun i j => by
    simp only [hdot]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hgR : (0 : ℝ) < grid := by exact_mod_cast hg
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hcdR : (0 : ℝ) < cd := by exact_mod_cast hcd
  set G : Fin m → Fin m → ℝ := fun i j =>
    ((((grid * dot i j + s / 2) / s + R i j : ℤ) : ℝ) + (C i j : ℝ) / cd) / grid with hG
  set P : Fin m → Fin m → ℝ := fun i j => ((dot i j : ℤ) : ℝ) / s with hP
  set E : Fin m → Fin m → ℝ := fun i j => G i j - P i j with hE
  set ε : Fin m → Fin m → ℝ := fun i j =>
    (((grid * dot i j + s / 2) / s : ℤ) : ℝ) - ((grid * dot i j : ℤ) : ℝ) / s with hε
  have hεb : ∀ i j, |ε i j| ≤ 1 / 2 := fun i j => round_err_real grid (dot i j) s hs h2
  have hEij : ∀ i j, E i j = (ε i j + (R i j : ℝ) + (C i j : ℝ) / cd) / grid := by
    intro i j
    simp only [hE, hG, hP, hε]
    push_cast
    field_simp
    ring
  have hEs : ∀ i j, E i j = E j i := by
    intro i j
    rw [hEij, hEij]
    have : ε i j = ε j i := by simp only [hε, hdots i j]
    rw [this, hR i j, hC i j]
  -- diagonal dominance of `E`
  have hdd' : ∀ i, ∑ j, (if i = j then (0 : ℝ) else |E i j|) ≤ E i i := by
    intro i
    set u : Fin m → ℝ := fun j => |((cd * R i j + C i j : ℤ) : ℝ)| / cd with hu
    have hpt : ∀ j, (if i = j then (0 : ℝ) else |E i j|)
        ≤ (if i = j then (0 : ℝ) else 1 / 2 / grid) + (if i = j then (0 : ℝ) else u j / grid) := by
      intro j
      by_cases hij : i = j
      · simp [hij]
      · simp only [if_neg hij]
        rw [hEij, abs_div, abs_of_pos hgR, ← add_div]
        apply div_le_div_of_nonneg_right _ hgR.le
        have e1 : (R i j : ℝ) + (C i j : ℝ) / cd = ((cd * R i j + C i j : ℤ) : ℝ) / cd := by
          push_cast; field_simp
        have e2 : |(R i j : ℝ) + (C i j : ℝ) / cd| = u j := by
          rw [e1, abs_div, abs_of_pos hcdR]
        have h3 : |ε i j + (R i j : ℝ) + (C i j : ℝ) / cd|
            ≤ |ε i j| + |(R i j : ℝ) + (C i j : ℝ) / cd| := by
          rw [add_assoc]; exact abs_add_le _ _
        rw [e2] at h3
        linarith [hεb i j]
    refine le_trans (Finset.sum_le_sum fun j _ => hpt j) ?_
    rw [Finset.sum_add_distrib]
    have hA : ∑ j : Fin m, (if i = j then (0 : ℝ) else 1 / 2 / grid) = ((m : ℝ) * (1 / 2 / grid) - 1 / 2 / grid) :=
      sum_ite_ne i _
    have hB : ∑ j : Fin m, (if i = j then (0 : ℝ) else u j / grid)
        = (∑ j : Fin m, (if i = j then (0 : ℝ) else |((cd * R i j + C i j : ℤ) : ℝ)|)) / cd / grid := by
      rw [Finset.sum_div, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i = j <;> simp [hij, hu, div_div]
    rw [hA, hB, hEij]
    have hh := hdd i
    have hh' : (m : ℝ) * cd < 2 * (((cd * R i i + C i i : ℤ) : ℝ)
        - ∑ j : Fin m, (if i = j then (0 : ℝ) else |((cd * R i j + C i j : ℤ) : ℝ)|)) := by
      have := (Int.cast_lt (R := ℝ)).2 hh
      push_cast at this ⊢
      simpa [Int.cast_sum, apply_ite Int.cast, Int.cast_abs] using this
    have hεi := (abs_le.1 (hεb i i)).1
    set S : ℝ := ∑ j : Fin m, (if i = j then (0 : ℝ) else |((cd * R i j + C i j : ℤ) : ℝ)|) with hS
    have hDi : ((cd * R i i + C i i : ℤ) : ℝ) = cd * R i i + C i i := by push_cast; ring
    -- goal: (m * (1/2/grid) - 1/2/grid) + S / cd / grid ≤ (ε + R + C/cd) / grid
    rw [← sub_nonneg]
    have key : 0 ≤ ((ε i i + (R i i : ℝ) + (C i i : ℝ) / cd) - ((m : ℝ) * (1 / 2) - 1 / 2 + S / cd)) / grid := by
      apply div_nonneg _ hgR.le
      have hq : (m : ℝ) / 2 < ((cd * R i i + C i i : ℤ) - S) / cd := by
        rw [lt_div_iff₀ hcdR]; push_cast at hh' ⊢; linarith
      have hq' : ((((cd * R i i + C i i : ℤ) : ℝ) - S) / cd) = (R i i : ℝ) + (C i i : ℝ) / cd - S / cd := by
        rw [hDi]; field_simp
      rw [hq'] at hq
      linarith
    convert key using 1
    field_simp
  exact ⟨E, hEs, hdd', fun i j => by simp only [hE, hG, hP]; ring⟩

/-- **Soundness of the compact Gram test** (`eq:fqe-compact-gram-test`), matrix level.  For an integer factor
`A`, integer symmetric `R` (= `Δ`) and `C`, and `G_ij = (H_ij + R_ij + C_ij/cd)/grid` with
`H_ij = ⌊(grid (AAᵀ)_ij + s/2)/s⌋`, the integer test `m cd < 2 (D_ii - ∑_{j≠i} |D_ij|)`,
`D = cd R + C`, makes `G` positive semidefinite. -/
theorem gram_psd {m r : ℕ} (A : Fin m → Fin r → ℤ) (R C : Fin m → Fin m → ℤ)
    (hR : ∀ i j, R i j = R j i) (hC : ∀ i j, C i j = C j i)
    (grid s cd : ℤ) (hg : 0 < grid) (hs : 0 < s) (h2 : (2 : ℤ) ∣ s) (hcd : 0 < cd)
    (hdd : ∀ i, (m : ℤ) * cd <
      2 * ((cd * R i i + C i i) - ∑ j, if i = j then 0 else |cd * R i j + C i j|))
    (x : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * (((((grid * (∑ k, A i k * A j k) + s / 2) / s + R i j : ℤ) : ℝ)
        + (C i j : ℝ) / cd) / grid) * x j := by
  obtain ⟨E, hEs, hdd', hG⟩ := gram_decomp A R C hR hC grid s cd hg hs h2 hcd hdd
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hEq := quad_nonneg_of_dd E hEs hdd' x
  have hPq : 0 ≤ ∑ i, ∑ j, x i * (((∑ k, A i k * A j k : ℤ) : ℝ) / s) * x j := by
    have := gram_form_nonneg A x
    have h' : ∑ i : Fin m, ∑ j : Fin m, x i * (((∑ k, A i k * A j k : ℤ) : ℝ) / s) * x j
        = (∑ i : Fin m, ∑ j : Fin m, x i * (((∑ k, A i k * A j k : ℤ) : ℝ)) * x j) / s := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h']
    exact div_nonneg this hsR.le
  calc (0 : ℝ) ≤ (∑ i, ∑ j, x i * (((∑ k, A i k * A j k : ℤ) : ℝ) / s) * x j)
        + ∑ i, ∑ j, x i * E i j * x j := add_nonneg hPq hEq
    _ = _ := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hG i j]; ring

/-- Diagonally dominant symmetric `E` against a matrix `Q` with `|Q_ij + Q_ji| ≤ Q_ii + Q_jj`, `Q_ii ≥ 0`. -/
theorem dd_nonneg {m : ℕ} (E Q : Fin m → Fin m → ℝ) (hsym : ∀ i j, E i j = E j i)
    (hdd : ∀ i, ∑ j, (if i = j then (0 : ℝ) else |E i j|) ≤ E i i)
    (hQd : ∀ i, 0 ≤ Q i i) (hQ : ∀ i j, |Q i j + Q j i| ≤ Q i i + Q j j) :
    0 ≤ ∑ i, ∑ j, E i j * Q i j := by
  set g : Fin m → Fin m → ℝ := fun i j => if i = j then 0 else |E i j| with hg
  have hgs : ∀ i j, g i j = g j i := by
    intro i j
    simp only [hg]
    by_cases h : i = j
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), hsym]
  have hpt : ∀ i j, (if i = j then 2 * E i i * Q i i else 0) - g i j * (Q i i + Q j j)
      ≤ E i j * (Q i j + Q j i) := by
    intro i j
    by_cases h : i = j
    · subst h
      have h0 : g i i = 0 := by simp [hg]
      rw [if_pos rfl, h0]
      apply le_of_eq
      ring
    · simp only [hg, if_neg h]
      have h2 : |E i j * (Q i j + Q j i)| ≤ |E i j| * (Q i i + Q j j) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hQ i j) (abs_nonneg _)
      have h3 := neg_abs_le (E i j * (Q i j + Q j i))
      linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
    Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hpt i j
  have hd : ∑ i : Fin m, ∑ j : Fin m, (if i = j then 2 * E i i * Q i i else 0)
      = ∑ i, 2 * E i i * Q i i := by
    simp [Finset.sum_ite_eq]
  have hswap : ∑ i : Fin m, ∑ j : Fin m, g i j * Q j j = ∑ i : Fin m, ∑ j : Fin m, g i j * Q i i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hgs]
  have hS : ∑ i : Fin m, ∑ j : Fin m, g i j * Q i i = ∑ i : Fin m, (∑ j, g i j) * Q i i := by
    simp [Finset.sum_mul]
  have hq : ∑ i : Fin m, ∑ j : Fin m, g i j * (Q i i + Q j j)
      = (∑ i : Fin m, ∑ j : Fin m, g i j * Q i i) + ∑ i : Fin m, ∑ j : Fin m, g i j * Q j j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hE2 : ∑ i : Fin m, ∑ j : Fin m, E i j * (Q i j + Q j i)
      = 2 * ∑ i : Fin m, ∑ j : Fin m, E i j * Q i j := by
    have : ∑ i : Fin m, ∑ j : Fin m, E i j * Q j i = ∑ i : Fin m, ∑ j : Fin m, E i j * Q i j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hsym j i]
    simp only [mul_add, Finset.sum_add_distrib, this]
    ring
  have hlhs : ∑ i : Fin m, ∑ j : Fin m,
      ((if i = j then 2 * E i i * Q i i else 0) - g i j * (Q i i + Q j j))
      = ∑ i, 2 * E i i * Q i i - ∑ i : Fin m, ∑ j : Fin m, g i j * (Q i i + Q j j) := by
    rw [← hd, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_sub_distrib]
  rw [hlhs, hq, hswap, hS, hE2] at hsum
  have key : 0 ≤ ∑ i : Fin m, (2 * E i i * Q i i - 2 * ((∑ j, g i j) * Q i i)) :=
    Finset.sum_nonneg fun i _ => by
      have := mul_nonneg (sub_nonneg.2 (hdd i)) (hQd i)
      simp only [hg]
      nlinarith [this]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at key
  linarith

/-- The inner product `∑ G_ij B(u_i, u_j)` of a Gram matrix passing the compact test with a Gram family of a
positive semidefinite bilinear form is nonnegative. -/
theorem inner_nonneg {V : Type*} [AddCommGroup V] [Module ℝ V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hB : ∀ v, 0 ≤ B v v) {m r : ℕ} (u : Fin m → V) (A : Fin m → Fin r → ℤ) (R C : Fin m → Fin m → ℤ)
    (hR : ∀ i j, R i j = R j i) (hC : ∀ i j, C i j = C j i)
    (grid s cd : ℤ) (hg : 0 < grid) (hs : 0 < s) (h2 : (2 : ℤ) ∣ s) (hcd : 0 < cd)
    (hdd : ∀ i, (m : ℤ) * cd <
      2 * ((cd * R i i + C i i) - ∑ j, if i = j then 0 else |cd * R i j + C i j|)) :
    0 ≤ ∑ i, ∑ j, (((((grid * (∑ k, A i k * A j k) + s / 2) / s + R i j : ℤ) : ℝ)
        + (C i j : ℝ) / cd) / grid) * B (u i) (u j) := by
  obtain ⟨E, hEs, hdd', hG⟩ := gram_decomp A R C hR hC grid s cd hg hs h2 hcd hdd
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hEq : 0 ≤ ∑ i, ∑ j, E i j * B (u i) (u j) := by
    apply dd_nonneg E (fun i j => B (u i) (u j)) hEs hdd' (fun i => hB _)
    intro i j
    have h1 := hB (u i + u j)
    have h2 := hB (u i - u j)
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at h1 h2
    rw [abs_le]
    constructor <;> linarith
  have hPq : 0 ≤ ∑ i, ∑ j, (((∑ k, A i k * A j k : ℤ) : ℝ) / s) * B (u i) (u j) := by
    have e1 : ∀ k : Fin r, B (∑ i, (A i k : ℝ) • u i) (∑ j, (A j k : ℝ) • u j)
        = ∑ i : Fin m, ∑ j : Fin m, (A i k : ℝ) * (A j k : ℝ) * B (u i) (u j) := by
      intro k
      have f1 : ∀ w, B (∑ i, (A i k : ℝ) • u i) w = ∑ i, (A i k : ℝ) * B (u i) w := by
        intro w
        simp [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
      have f2 : ∀ v, B v (∑ j, (A j k : ℝ) • u j) = ∑ j, (A j k : ℝ) * B v (u j) := by
        intro v
        simp [map_sum, map_smul]
      rw [f1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [f2, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∑ k : Fin r, ∑ i : Fin m, ∑ j : Fin m, (A i k : ℝ) * (A j k : ℝ) * B (u i) (u j)
        = ∑ i : Fin m, ∑ j : Fin m, ((∑ k, A i k * A j k : ℤ) : ℝ) * B (u i) (u j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      rw [Finset.sum_mul]
    have h' : ∑ i : Fin m, ∑ j : Fin m, (((∑ k, A i k * A j k : ℤ) : ℝ) / s) * B (u i) (u j)
        = (∑ k : Fin r, B (∑ i, (A i k : ℝ) • u i) (∑ j, (A j k : ℝ) • u j)) / s := by
      simp only [e1]
      rw [e2, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h']
    exact div_nonneg (Finset.sum_nonneg fun k _ => hB _) hsR.le
  calc (0 : ℝ) ≤ (∑ i, ∑ j, (((∑ k, A i k * A j k : ℤ) : ℝ) / s) * B (u i) (u j))
        + ∑ i, ∑ j, E i j * B (u i) (u j) := add_nonneg hPq hEq
    _ = _ := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hG i j]; ring

end FormalResearch.FourQubitEntropy.GOProbe
