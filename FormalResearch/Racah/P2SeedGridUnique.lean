module

public import FormalResearch.Racah.P2SeedLogAllOrderPhys

/-!
# Uniqueness of expansion coefficients on the physical `3j` grid (Weyl P2, `app:3j-allorder`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `app:3j-allorder`.  Support for the link
`P2SeedMultiplierLink`.

The expansions `HasUniformExpansionOn (phys3jGrid M σ)` only constrain the amplitude at the lattice
points `x = 2μ/N`, `N → ∞`, so uniqueness of the coefficient functions is not the pointwise
uniqueness of `HasUniformExpansion.eq_of_tendsto` (for a fixed `x` the grid is usually empty).  This
file proves it for *continuous* coefficients, in the extremal chamber `α = M-σ`, `β = M+σ` natural:

* `exists_grid_point`: **the physical lattice is dense and unbounded**: for every `x ∈ (-1,1)`,
  `δ > 0` and `N₀` there are `(N, μ)` with `N ≥ N₀`, `SpecAdm M σ N`, `Lat4 M σ N μ` and
  `|2μ/N - x| < δ` (explicitly `N = j+1+M`, `2μ = 2a-j+σ`, `a = ⌊j(1+x)/2⌋`, so that
  `j_-+m_- = a`, `j_++m_+ = j-a`).
* `grid_coeff_unique`: two continuous-on-`(-1,1)` coefficient families that both give uniform
  expansions of the same function on the grid (for every compact `K ⊆ (-1,1)`) agree on `(-1,1)`.

All proved; no hypotheses beyond `α, β ∈ ℕ`.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Asymptotics FormalResearch.Wigner Finset Filter Topology Set

section Grid

variable {M σ : ℚ} {α β : ℕ}

/-- `max |M| |σ| = M` in the extremal chamber. -/
theorem max_abs_eq_of_chamber (hα : M - σ = α) (hβ : M + σ = β) : max |M| |σ| = M := by
  have hα0 : (0 : ℚ) ≤ α := Nat.cast_nonneg α
  have hβ0 : (0 : ℚ) ≤ β := Nat.cast_nonneg β
  rw [abs_of_nonneg (by linarith : (0 : ℚ) ≤ M)]
  exact max_eq_left (abs_le.mpr ⟨by linarith, by linarith⟩)

/-- **The physical lattice is dense in `x` and unbounded in `N`.**  For `x ∈ (-1,1)`, `δ > 0` and
`N₀`, there is an admissible `N ≥ N₀` and a lattice point `μ` with `|2μ/N - x| < δ`
(extremal chamber, `α = M-σ`, `β = M+σ` natural). -/
theorem exists_grid_point (hα : M - σ = α) (hβ : M + σ = β) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    {δ : ℝ} (hδ : 0 < δ) (N₀ : ℝ) :
    ∃ N μ : ℚ, SpecAdm M σ N ∧ Lat4 M σ N μ ∧ N₀ ≤ (N : ℝ) ∧ |2 * (μ : ℝ) / N - x| < δ := by
  have hα0 : (0 : ℚ) ≤ α := Nat.cast_nonneg α
  have hβ0 : (0 : ℚ) ≤ β := Nat.cast_nonneg β
  have hM0 : (0 : ℚ) ≤ M := by linarith
  have hM0' : (0 : ℝ) ≤ M := by exact_mod_cast hM0
  set B : ℝ := 3 + |(σ : ℝ)| + (M : ℝ) with hB
  obtain ⟨j, hj⟩ := exists_nat_gt (max (B / δ) N₀)
  have hj1 : B / δ < j := lt_of_le_of_lt (le_max_left _ _) hj
  have hj2 : N₀ < j := lt_of_le_of_lt (le_max_right _ _) hj
  set a : ℕ := ⌊(j : ℝ) * (1 + x) / 2⌋₊ with ha
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hx1 : 0 < 1 + x := by linarith [hx.1]
  have hx2 : 0 < 1 - x := by linarith [hx.2]
  have hnn : 0 ≤ (j : ℝ) * (1 + x) / 2 := by positivity
  have ha1 : (a : ℝ) ≤ (j : ℝ) * (1 + x) / 2 := Nat.floor_le hnn
  have ha2 : (j : ℝ) * (1 + x) / 2 < a + 1 := Nat.lt_floor_add_one _
  have haj : a ≤ j := by
    have : (a : ℝ) ≤ j := by nlinarith
    exact_mod_cast this
  obtain ⟨c, hc⟩ : ∃ c : ℕ, j = a + c := ⟨j - a, by omega⟩
  have hcq : (c : ℚ) = j - a := by
    have : ((a + c : ℕ) : ℚ) = j := by rw [← hc]
    push_cast at this; linarith
  have hcr : (c : ℝ) = j - a := by
    have : ((a + c : ℕ) : ℝ) = j := by rw [← hc]
    push_cast at this; linarith
  refine ⟨(j : ℚ) + 1 + M, ((a : ℚ) - c + σ) / 2, ?_, ?_, ?_, ?_⟩
  · -- SpecAdm
    have hmax := max_abs_eq_of_chamber hα hβ
    unfold SpecAdm IsTri IsNat
    rw [hmax]
    refine ⟨⟨⟨α, ?_⟩, ⟨β, ?_⟩, ⟨j, ?_⟩⟩, ⟨α + β, ?_⟩, ⟨0, ?_⟩⟩ <;>
      first
      | (unfold jMinus jPlus; linarith)
      | (push_cast; linarith)
  · unfold Lat4 IsNat jMinus jPlus mMinus mPlus
    refine ⟨⟨a, ?_⟩, ⟨a + β, ?_⟩, ⟨c + α, ?_⟩, ⟨c, ?_⟩⟩ <;> push_cast <;> linarith
  · have : (N₀ : ℝ) ≤ j := hj2.le
    have e : (((j : ℚ) + 1 + M : ℚ) : ℝ) = j + 1 + M := by push_cast; ring
    rw [e]; linarith
  · have e : (((j : ℚ) + 1 + M : ℚ) : ℝ) = j + 1 + M := by push_cast; ring
    have e2 : ((((a : ℚ) - c + σ) / 2 : ℚ) : ℝ) = ((a : ℝ) - c + σ) / 2 := by push_cast; ring
    rw [e, e2]
    have hNpos : 0 < (j : ℝ) + 1 + M := by positivity
    have hacos : (a : ℝ) - c = 2 * a - j := by rw [hcr]; ring
    have hlow : (j : ℝ) * x - 2 < 2 * a - j := by nlinarith
    have hup : 2 * (a : ℝ) - j ≤ j * x := by nlinarith
    have hs : -|(σ : ℝ)| ≤ σ ∧ σ ≤ |(σ : ℝ)| := ⟨neg_abs_le _, le_abs_self _⟩
    have hxa : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
    have hxM : -(M : ℝ) - 1 ≤ x * (1 + M) ∧ x * (1 + M) ≤ M + 1 := by
      have h1M : 0 ≤ 1 + (M : ℝ) := by linarith
      have := (abs_le.1 (show |x * (1 + (M : ℝ))| ≤ 1 + M by
        rw [abs_mul, abs_of_nonneg h1M]; exact mul_le_of_le_one_left h1M hxa))
      constructor <;> linarith [this.1, this.2]
    have key : |2 * (((a : ℝ) - c + σ) / 2) - x * ((j : ℝ) + 1 + M)| ≤ B := by
      rw [abs_le]
      have e3 : 2 * (((a : ℝ) - c + σ) / 2) - x * ((j : ℝ) + 1 + M) =
          ((2 * a - j : ℝ) - j * x) + σ - x * (1 + M) := by rw [hacos]; ring
      rw [e3]
      constructor <;> nlinarith [hs.1, hs.2, hxM.1, hxM.2]
    have hdiv : 2 * (((a : ℝ) - c + σ) / 2) / ((j : ℝ) + 1 + M) - x =
        (2 * (((a : ℝ) - c + σ) / 2) - x * ((j : ℝ) + 1 + M)) / ((j : ℝ) + 1 + M) := by
      field_simp
    rw [hdiv, abs_div, abs_of_pos hNpos, div_lt_iff₀ hNpos]
    have hBj : B < δ * j := by
      have := (div_lt_iff₀ hδ).1 hj1
      linarith
    nlinarith [abs_nonneg (2 * (((a : ℝ) - c + σ) / 2) - x * ((j : ℝ) + 1 + M)), hj0, hM0']

/-- `eps3j (N, μ) = 1/N²`. -/
private lemma eps3j_apply (q : ℚ × ℚ) : eps3j q = 1 / (q.1 : ℝ) ^ 2 := rfl

/-- **Uniqueness of continuous coefficients on the physical grid.**  Let `g : ℚ × ℚ → ℝ` be a function
of the lattice index `(N, μ)` and `a, b : ℕ → ℝ → ℝ` two families of coefficient functions, continuous
on `(-1,1)`, such that for every compact `K ⊆ (-1,1)` and every `R`, `g(N,μ) = ∑_{r<R} N^{-2r} a_r(x)
+ O(N^{-2R})` (uniformly in the lattice points with `x = 2μ/N ∈ K`, `N → ∞`), and the same for `b`.
Then `a_r = b_r` on `(-1,1)` for all `r` (extremal chamber `α = M-σ`, `β = M+σ` natural). -/
theorem grid_coeff_unique (hα : M - σ = α) (hβ : M + σ = β) (g : ℚ × ℚ → ℝ) (a b : ℕ → ℝ → ℝ)
    (ha : ∀ r, ContinuousOn (a r) (Ioo (-1 : ℝ) 1)) (hb : ∀ r, ContinuousOn (b r) (Ioo (-1 : ℝ) 1))
    (h1 : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo (-1 : ℝ) 1 → ∀ R : ℕ, ∃ C : ℝ, ∀ᶠ i in atN,
      ∀ z ∈ K, (z, i) ∈ phys3jGrid M σ →
        |g i - ∑ r ∈ range R, eps3j i ^ r * a r z| ≤ C * |eps3j i| ^ R)
    (h2 : ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo (-1 : ℝ) 1 → ∀ R : ℕ, ∃ C : ℝ, ∀ᶠ i in atN,
      ∀ z ∈ K, (z, i) ∈ phys3jGrid M σ →
        |g i - ∑ r ∈ range R, eps3j i ^ r * b r z| ≤ C * |eps3j i| ^ R) :
    ∀ r : ℕ, ∀ x ∈ Ioo (-1 : ℝ) 1, a r x = b r x := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro x hx
  by_contra hne
  have hd : 0 < |a r x - b r x| := abs_pos.2 (sub_ne_zero.2 hne)
  set d := |a r x - b r x| with hdd
  have hcont : ContinuousAt (fun z => a r z - b r z) x :=
    ((ha r).sub (hb r)).continuousAt (Ioo_mem_nhds hx.1 hx.2)
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.continuousAt_iff.1 hcont (d / 2) (by positivity)
  set δ : ℝ := min (δ₀ / 2) (min ((1 - x) / 2) ((1 + x) / 2)) with hδ
  have hx1 : 0 < 1 + x := by linarith [hx.1]
  have hx2 : 0 < 1 - x := by linarith [hx.2]
  have hδpos : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hδ1 : δ ≤ δ₀ / 2 := min_le_left _ _
  have hδ2 : δ ≤ (1 - x) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ (1 + x) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set K : Set ℝ := Icc (x - δ) (x + δ) with hK
  have hKc : IsCompact K := isCompact_Icc
  have hKI : K ⊆ Ioo (-1 : ℝ) 1 := fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩
  obtain ⟨C1, hC1⟩ := h1 K hKc hKI (r + 1)
  obtain ⟨C2, hC2⟩ := h2 K hKc hKI (r + 1)
  have hev := hC1.and hC2
  rw [atN, Filter.eventually_comap] at hev
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 hev
  set T : ℝ := |C1 + C2| with hT
  obtain ⟨N, μ, hA, hlat, hN, hclose⟩ :=
    exists_grid_point hα hβ hx hδpos (max N1 (max 1 (2 * T / d + 1)))
  have hN1' : N1 ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have hN2 : 1 ≤ (N : ℝ) := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN3 : 2 * T / d + 1 ≤ (N : ℝ) := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  set z : ℝ := 2 * (μ : ℝ) / N with hz
  have hzK : z ∈ K := by
    have := abs_lt.1 hclose
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hmem : (z, ((N, μ) : ℚ × ℚ)) ∈ phys3jGrid M σ := ⟨hA, hlat, rfl⟩
  obtain ⟨hb1, hb2⟩ := hN1 (N : ℝ) hN1' (N, μ) rfl
  have e1 := hb1 z hzK hmem
  have e2 := hb2 z hzK hmem
  have hzI := hKI hzK
  have hsum : ∑ s ∈ range r, eps3j (N, μ) ^ s * a s z = ∑ s ∈ range r, eps3j (N, μ) ^ s * b s z :=
    sum_congr rfl fun s hs => by rw [ih s (mem_range.1 hs) z hzI]
  have hNpos : 0 < (N : ℝ) := by linarith
  have hε : 0 < eps3j (N, μ) := by rw [eps3j_apply]; positivity
  have hεabs : |eps3j (N, μ)| = eps3j (N, μ) := abs_of_pos hε
  rw [sum_range_succ, hsum, hεabs] at e1
  rw [sum_range_succ, hεabs] at e2
  set ε := eps3j (N, μ) with hεdef
  set S0 := ∑ s ∈ range r, ε ^ s * b s z with hS0
  have hdiff : |ε ^ r * (a r z - b r z)| ≤ (C1 + C2) * ε ^ (r + 1) := by
    have e3 : ε ^ r * (a r z - b r z) =
        (g (N, μ) - (S0 + ε ^ r * b r z)) - (g (N, μ) - (S0 + ε ^ r * a r z)) := by ring
    rw [e3]
    calc _ ≤ |g (N, μ) - (S0 + ε ^ r * b r z)| + |g (N, μ) - (S0 + ε ^ r * a r z)| := abs_sub _ _
      _ ≤ C2 * ε ^ (r + 1) + C1 * ε ^ (r + 1) := add_le_add e2 e1
      _ = _ := by ring
  have hεr : 0 < ε ^ r := pow_pos hε r
  have hc : |a r z - b r z| ≤ T * ε := by
    rw [abs_mul, abs_of_pos hεr, pow_succ] at hdiff
    have h5 : ε ^ r * |a r z - b r z| ≤ ε ^ r * (T * ε) := by
      calc ε ^ r * |a r z - b r z| ≤ (C1 + C2) * (ε ^ r * ε) := hdiff
        _ ≤ T * (ε ^ r * ε) := by
            have : 0 ≤ ε ^ r * ε := by positivity
            exact mul_le_mul_of_nonneg_right (le_abs_self _) this
        _ = ε ^ r * (T * ε) := by ring
    exact le_of_mul_le_mul_left h5 hεr
  have hTε : T * ε < d / 2 := by
    have hT0 : 0 ≤ T := abs_nonneg _
    have hεN : ε ≤ 1 / (N : ℝ) := by
      rw [hεdef, eps3j_apply]
      simp only
      rw [div_le_div_iff₀ (by positivity) hNpos]
      nlinarith
    have h6 : T * ε ≤ T / N := by
      calc T * ε ≤ T * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_left hεN hT0
        _ = T / N := by ring
    have h7 : T / N < d / 2 := by
      rw [div_lt_div_iff₀ hNpos (by norm_num)]
      have : 2 * T / d < N := by linarith
      rw [div_lt_iff₀ hd] at this
      linarith
    linarith
  have hclose' : |(a r z - b r z) - (a r x - b r x)| < d / 2 := by
    have h := hδ₀' (x := z) (by rw [Real.dist_eq]; linarith)
    rw [Real.dist_eq] at h
    exact h
  have : d ≤ |a r z - b r z| + |(a r z - b r z) - (a r x - b r x)| := by
    rw [hdd]
    calc |a r x - b r x| = |(a r z - b r z) - ((a r z - b r z) - (a r x - b r x))| := by ring_nf
      _ ≤ _ := abs_sub _ _
  linarith

end Grid

/-- info: 'FormalResearch.Racah.exists_grid_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.exists_grid_point

/-- info: 'FormalResearch.Racah.grid_coeff_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.grid_coeff_unique

end FormalResearch.Racah
