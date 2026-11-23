module

public import FormalResearch.ModularBootstrap.Upper.Holes.HoleLimit

/-!
# Geometry of the `j = 4` hole of the reference comb

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Step (3), "The other seven hole pairs":
"the gaps in `H` are `ℓ_n(1+O(1/n))`, so if `x - χ_{k₀} ≥ 0` the hole sites `k₀ + j` lie at distance
`≥ (j-½)ℓ_n(1-C/n)` from `x` and the sites `k₀ - j` at distance `≥ jℓ_n(1-C/n)` (symmetrically if
`x < χ_{k₀}`)".

For `x` in the reference cell `[χ_n, χ_{n+1})` with `n ≥ 20` and `ℓ = ℓ_n`, the hole `H = {n-3, …, n+4}` is
`k₀` together with four near indices and three far indices:

* layout `A` (`x - χ_n ≤ ℓ/2`): `k₀ = n`, near `n + 1 + i`, far `n - 1 - i`;
* layout `B` (`χ_{n+1} - x ≤ ℓ/2`): `k₀ = n + 1`, near `n - i`, far `n + 2 + i`.

`hole_geometry_A`, `hole_geometry_B`: near sites are at distance `≥ (1 - 200/n)(i + ½)ℓ` and far sites at
distance `≥ (1 - 200/n)(i + 1)ℓ`; `hole_gap_bounds`: all gaps of the hole are `(1 ± 20/n)ℓ`.
All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set

namespace FormalResearch.ModularBootstrap.Upper.Holes

open FormalResearch.ModularBootstrap.Upper.Comb

/-- The gaps of the hole are `(1 ± 20/n) ℓ_n`, and `ℓ_n > 0`. -/
theorem hole_gap_bounds {c' : ℝ} (hc' : 0 < c') {n : ℕ} (hn : 20 ≤ n) :
    0 < siteGap c' n ∧ ∀ m ∈ Finset.Icc (n - 4 + 1) (n + 4),
      (1 - 20 / (n : ℝ)) * siteGap c' n ≤ siteGap c' m ∧
        siteGap c' m ≤ (1 + 20 / (n : ℝ)) * siteGap c' n := by
  obtain ⟨hℓ, -, -, hgap⟩ := quantile_linearization_K5 hc' (j := 4) (n := n) (by norm_num)
    (by omega)
  refine ⟨hℓ, fun m hm => ?_⟩
  have h := hgap m hm
  have h20 : (4 : ℝ) * ((4 : ℕ) + 1) = 20 := by norm_num
  rw [h20] at h
  have := abs_le.mp h
  constructor <;> nlinarith [this.1, this.2]

private lemma chi_window {c' : ℝ} (hc' : 0 < c') {n : ℕ} (hn : 20 ≤ n) {b : ℝ}
    (hb1 : (n : ℝ) - 4 - 1 / 2 ≤ b) (hb2 : b ≤ (n : ℝ) + 4 + 1) :
    |chiQuantile c' b - chiQuantile c' n - (b - n) * siteGap c' n| ≤ 100 / (n : ℝ) * siteGap c' n := by
  obtain ⟨-, -, hchi, -⟩ := quantile_linearization_K5 hc' (j := 4) (n := n) (by norm_num) (by omega)
  have := hchi b ⟨hb1, hb2⟩
  have h100 : (4 : ℝ) * (((4 : ℕ) : ℝ) + 1) ^ 2 = 100 := by norm_num
  rw [h100] at this
  exact this

private lemma step_aux {n : ℝ} {ℓ a : ℝ} (hn : 0 < n) (hℓ : 0 < ℓ) (ha : 1 / 2 ≤ a) :
    100 / n * ℓ ≤ 200 / n * a * ℓ := by
  have h1 : 0 ≤ 1 / n := by positivity
  have : 100 / n = 100 * (1 / n) := by ring
  have h2 : 200 / n * a = 200 * (1 / n) * a := by ring
  have h3 : 100 * (1 / n) ≤ 200 * (1 / n) * a := by nlinarith
  rw [this, h2]
  exact mul_le_mul_of_nonneg_right h3 hℓ.le

private lemma step_aux' {n : ℝ} {ℓ a : ℝ} (hn : 0 < n) (hℓ : 0 < ℓ) (ha : 1 ≤ a) :
    100 / n * ℓ ≤ 200 / n * a * ℓ := step_aux hn hℓ (by linarith)

/-- Layout `A`: `0 ≤ x - χ_n ≤ ℓ/2`.  The near sites `n + 1 + i` are at distance `≥ (1 - 200/n)(i+½)ℓ`
and the far sites `n - 1 - i` at distance `≥ (1 - 200/n)(i+1)ℓ`. -/
theorem hole_geometry_A {c' x : ℝ} (hc' : 0 < c') {n : ℕ} (hn : 400 ≤ n)
    (hx0 : chiQuantile c' n ≤ x) (hxA : x - chiQuantile c' n ≤ siteGap c' n / 2) :
    (∀ i : ℕ, i < 4 → (1 - 200 / (n : ℝ)) * (((i : ℝ) + 1 / 2) * siteGap c' n) ≤
        |x - chiQuantile c' ((n + 1 + i : ℕ) : ℝ)|) ∧
      ∀ i : ℕ, i < 3 → (1 - 200 / (n : ℝ)) * (((i : ℝ) + 1) * siteGap c' n) ≤
        |x - chiQuantile c' ((n - 1 - i : ℕ) : ℝ)| := by
  obtain ⟨hℓ, -⟩ := hole_gap_bounds hc' (by omega : 20 ≤ n)
  have hnr : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnr20 : (400 : ℝ) ≤ n := by exact_mod_cast hn
  have h100 : 100 / (n : ℝ) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hnr (by norm_num)]; linarith
  have h100ℓ : 100 / (n : ℝ) * siteGap c' n ≤ 1 / 4 * siteGap c' n :=
    mul_le_mul_of_nonneg_right h100 hℓ.le
  constructor
  · intro i hi
    have hir : (i : ℝ) ≤ 3 := by exact_mod_cast (by omega : i ≤ 3)
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hb := chi_window hc' (by omega : 20 ≤ n) (b := (((n + 1 + i : ℕ)) : ℝ)) (by push_cast; linarith)
      (by push_cast; linarith)
    have hcast : (((n + 1 + i : ℕ)) : ℝ) - n = (i : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hb
    have hstep := step_aux hnr hℓ (a := (i : ℝ) + 1 / 2) (by linarith)
    have hl := (abs_le.mp hb).1
    have : x - chiQuantile c' ((n + 1 + i : ℕ) : ℝ) ≤ 0 := by nlinarith
    rw [abs_of_nonpos this]
    nlinarith
  · intro i hi
    have hir : (i : ℝ) ≤ 2 := by exact_mod_cast (by omega : i ≤ 2)
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hcast : (((n - 1 - i : ℕ)) : ℝ) = (n : ℝ) - 1 - i := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    have hb := chi_window hc' (by omega : 20 ≤ n) (b := (((n - 1 - i : ℕ)) : ℝ)) (by rw [hcast]; linarith)
      (by rw [hcast]; linarith)
    rw [hcast] at hb ⊢
    have hstep := step_aux' hnr hℓ (a := (i : ℝ) + 1) (by linarith)
    have hl := (abs_le.mp hb).2
    have : 0 ≤ x - chiQuantile c' ((n : ℝ) - 1 - i) := by nlinarith
    rw [abs_of_nonneg this]
    nlinarith

/-- Layout `B`: `0 < χ_{n+1} - x ≤ ℓ/2`.  The near sites `n - i` are at distance `≥ (1 - 200/n)(i+½)ℓ`
and the far sites `n + 2 + i` at distance `≥ (1 - 200/n)(i+1)ℓ`. -/
theorem hole_geometry_B {c' x : ℝ} (hc' : 0 < c') {n : ℕ} (hn : 400 ≤ n)
    (hx1 : x ≤ chiQuantile c' ((n + 1 : ℕ) : ℝ))
    (hxB : chiQuantile c' ((n + 1 : ℕ) : ℝ) - x ≤ siteGap c' n / 2) :
    (∀ i : ℕ, i < 4 → (1 - 200 / (n : ℝ)) * (((i : ℝ) + 1 / 2) * siteGap c' n) ≤
        |x - chiQuantile c' ((n - i : ℕ) : ℝ)|) ∧
      ∀ i : ℕ, i < 3 → (1 - 200 / (n : ℝ)) * (((i : ℝ) + 1) * siteGap c' n) ≤
        |x - chiQuantile c' ((n + 2 + i : ℕ) : ℝ)| := by
  obtain ⟨hℓ, -⟩ := hole_gap_bounds hc' (by omega : 20 ≤ n)
  have hnr : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnr20 : (400 : ℝ) ≤ n := by exact_mod_cast hn
  have h100 : 100 / (n : ℝ) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hnr (by norm_num)]; linarith
  have h100ℓ : 100 / (n : ℝ) * siteGap c' n ≤ 1 / 4 * siteGap c' n :=
    mul_le_mul_of_nonneg_right h100 hℓ.le
  have hgap : siteGap c' n = chiQuantile c' ((n + 1 : ℕ) : ℝ) - chiQuantile c' (n : ℝ) := by
    unfold siteGap; push_cast; ring
  constructor
  · intro i hi
    have hir : (i : ℝ) ≤ 3 := by exact_mod_cast (by omega : i ≤ 3)
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hcast : (((n - i : ℕ)) : ℝ) = (n : ℝ) - i := by
      rw [Nat.cast_sub (by omega)]
    have hb := chi_window hc' (by omega : 20 ≤ n) (b := (((n - i : ℕ)) : ℝ)) (by rw [hcast]; linarith)
      (by rw [hcast]; linarith)
    rw [hcast] at hb ⊢
    have hb' : (n - i - n : ℝ) = -i := by ring
    rw [hb'] at hb
    have hstep := step_aux hnr hℓ (a := (i : ℝ) + 1 / 2) (by linarith)
    have hl := (abs_le.mp hb).2
    have : 0 ≤ x - chiQuantile c' ((n : ℝ) - i) := by nlinarith
    rw [abs_of_nonneg this]
    nlinarith
  · intro i hi
    have hir : (i : ℝ) ≤ 2 := by exact_mod_cast (by omega : i ≤ 2)
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hb := chi_window hc' (by omega : 20 ≤ n) (b := (((n + 2 + i : ℕ)) : ℝ)) (by push_cast; linarith)
      (by push_cast; linarith)
    have hcast : (((n + 2 + i : ℕ)) : ℝ) - n = (i : ℝ) + 2 := by push_cast; ring
    rw [hcast] at hb
    have hstep := step_aux' hnr hℓ (a := (i : ℝ) + 1) (by linarith)
    have hl := (abs_le.mp hb).1
    have : x - chiQuantile c' ((n + 2 + i : ℕ) : ℝ) ≤ 0 := by nlinarith
    rw [abs_of_nonpos this]
    nlinarith

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.hole_gap_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.hole_gap_bounds

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.hole_geometry_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.hole_geometry_A

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.hole_geometry_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.hole_geometry_B

end FormalResearch.ModularBootstrap.Upper.Holes
