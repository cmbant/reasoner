module

public import FormalResearch.Special.LatticeVarTail

/-!
# Geometric tails over a phase lattice with a general rate

`lem:latticesum` (o) gives at most `c(a'-a) + 2` levels in `[a,a']`; hence
`∑_{x∈S} e^{-γ|x|} ≤ 2(c + 2)/(1 - e^{-γ})` for every `γ > 0` (`sum_exp_rate_le`).  This is the version of
`sum_exp_tail_two_sided` (`LatticeVarTail`, rate `2π`, with a cutoff `y₀`) for an arbitrary rate; it is used in
`thm:tracecore` with `γ = πσ` (`∑_r e^{-πσ|x_r|} ≤ C ϰ log L`).
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set

/-- One-sided geometric tail of rate `γ` over a finite set with at most `N₁` points in every unit window of `u`. -/
lemma sum_rate_one_side (S : Finset ℝ) (u : ℝ → ℝ) {N1 X γ : ℝ} (hγ : 0 < γ)
    (hbd : ∀ x ∈ S, u x ≤ X)
    (hcard : ∀ a : ℝ, ((S.filter fun x => a ≤ u x ∧ u x ≤ a + 1).card : ℝ) ≤ N1) :
    ∑ x ∈ S.filter (fun x => 0 ≤ u x), Real.exp (-γ * u x) ≤ N1 / (1 - Real.exp (-γ)) := by
  set T := S.filter (fun x => 0 ≤ u x) with hT
  set K : ℕ := ⌊X⌋₊ + 1 with hK
  set r : ℝ := Real.exp (-γ) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hN : 0 ≤ N1 := le_trans (Nat.cast_nonneg _) (hcard 0)
  have hmaps : ∀ x ∈ T, ⌊u x⌋₊ ∈ Finset.range K := by
    intro x hx
    rw [hT, Finset.mem_filter] at hx
    rw [Finset.mem_range, hK]
    have := Nat.floor_le_floor (hbd x hx.1)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ k ∈ Finset.range K,
      ∑ x ∈ T with ⌊u x⌋₊ = k, Real.exp (-γ * u x) ≤ N1 * r ^ k := by
    intro k _
    have hfib_sub : (T.filter fun x => ⌊u x⌋₊ = k) ⊆ S.filter fun x => (k : ℝ) ≤ u x ∧ u x ≤ k + 1 := by
      intro x hx
      rw [Finset.mem_filter, hT, Finset.mem_filter] at hx
      obtain ⟨⟨hxS, hxy⟩, hxk⟩ := hx
      rw [Nat.floor_eq_iff hxy] at hxk
      rw [Finset.mem_filter]
      exact ⟨hxS, hxk.1, hxk.2.le⟩
    have hterm : ∀ x ∈ (T.filter fun x => ⌊u x⌋₊ = k), Real.exp (-γ * u x) ≤ r ^ k := by
      intro x hx
      rw [Finset.mem_filter, hT, Finset.mem_filter] at hx
      obtain ⟨⟨hxS, hxy⟩, hxk⟩ := hx
      rw [Nat.floor_eq_iff hxy] at hxk
      have hrk : r ^ k = Real.exp (-γ * k) := by
        rw [hr, ← Real.exp_nat_mul]; congr 1; ring
      rw [hrk]
      apply Real.exp_le_exp.2
      nlinarith [hxk.1]
    calc ∑ x ∈ T with ⌊u x⌋₊ = k, Real.exp (-γ * u x)
        ≤ ∑ _x ∈ (T.filter fun x => ⌊u x⌋₊ = k), r ^ k := Finset.sum_le_sum hterm
      _ = ((T.filter fun x => ⌊u x⌋₊ = k).card : ℝ) * r ^ k := by simp
      _ ≤ N1 * r ^ k := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact le_trans (by exact_mod_cast Finset.card_le_card hfib_sub) (hcard k)
  refine (Finset.sum_le_sum hfib).trans ?_
  rw [← Finset.mul_sum]
  have hg : ∑ k ∈ Finset.range K, r ^ k ≤ 1 / (1 - r) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := K) hr0.le hr1
    rw [← Finset.range_eq_Ico] at this
    simpa using this
  calc N1 * ∑ k ∈ Finset.range K, r ^ k ≤ N1 * (1 / (1 - r)) := mul_le_mul_of_nonneg_left hg hN
    _ = N1 / (1 - r) := by ring

/-- **Two-sided geometric tail of rate `γ`**: `∑_{x∈S} e^{-γ|x|} ≤ 2(c+2)/(1 - e^{-γ})` when every window `[a,a']`
holds at most `c(a'-a)+2` levels. -/
theorem sum_exp_rate_le (S : Finset ℝ) {X c γ : ℝ} (hγ : 0 < γ) (hc0 : 0 ≤ c)
    (hS : ∀ x ∈ S, x ∈ Icc (-X) X)
    (hc : ∀ a a' : ℝ, -X ≤ a → a ≤ a' → a' ≤ X →
      ((S.filter fun x => x ∈ Icc a a').card : ℝ) ≤ c * (a' - a) + 2) :
    ∑ x ∈ S, Real.exp (-γ * |x|) ≤ 2 * ((c + 2) / (1 - Real.exp (-γ))) := by
  have hcl := window_card_clip S hc0 hS hc
  have hpos := sum_rate_one_side S (fun x => x) (N1 := c + 2) (X := X) hγ
    (fun x hx => (hS x hx).2)
    (fun a => by
      have e : (S.filter fun x => a ≤ x ∧ x ≤ a + 1) = S.filter fun x => x ∈ Icc a (a + 1) := by
        ext x; simp [Finset.mem_filter, mem_Icc]
      rw [e]
      have := hcl a (a + 1) (by linarith)
      linarith)
  have hneg := sum_rate_one_side S (fun x => -x) (N1 := c + 2) (X := X) hγ
    (fun x hx => by have := (hS x hx).1; linarith)
    (fun a => by
      have e : (S.filter fun x => a ≤ -x ∧ -x ≤ a + 1) = S.filter fun x => x ∈ Icc (-a - 1) (-a) := by
        ext x; simp only [Finset.mem_filter, mem_Icc]
        constructor <;> rintro ⟨h, h1, h2⟩ <;> exact ⟨h, by linarith, by linarith⟩
      rw [e]
      have := hcl (-a - 1) (-a) (by linarith)
      linarith)
  rw [Finset.sum_filter] at hpos hneg
  have hle : ∑ x ∈ S, Real.exp (-γ * |x|) ≤
      ∑ x ∈ S, ((if 0 ≤ x then Real.exp (-γ * x) else 0) +
        (if 0 ≤ -x then Real.exp (-γ * -x) else 0)) := by
    apply Finset.sum_le_sum
    intro x _
    have h0 : 0 ≤ (if 0 ≤ x then Real.exp (-γ * x) else 0) := by split_ifs <;> positivity
    have h1 : 0 ≤ (if 0 ≤ -x then Real.exp (-γ * -x) else 0) := by split_ifs <;> positivity
    by_cases h : 0 ≤ x
    · have e : (if 0 ≤ x then Real.exp (-γ * x) else 0) = Real.exp (-γ * x) := by simp [h]
      rw [abs_of_nonneg h]; linarith
    · have h' : 0 ≤ -x := by linarith [not_le.mp h]
      have e : (if 0 ≤ -x then Real.exp (-γ * -x) else 0) = Real.exp (-γ * -x) := by simp [h']
      rw [abs_of_neg (not_le.mp h)]; linarith
  rw [Finset.sum_add_distrib] at hle
  linarith

/-- info: 'FormalResearch.Special.Lattice.sum_exp_rate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sum_exp_rate_le

end FormalResearch.Special.Lattice
