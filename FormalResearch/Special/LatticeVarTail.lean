module

public import FormalResearch.Special.LatticeVar

/-!
# `lem:varcore` (ii): the tail of the variance sum

For levels `S ⊂ [-X, X]` with at most `N₁` levels in every unit interval,
`∑_{x ∈ S, |x| ≥ y₀} e^{-2π|x|} ≤ 4 N₁ e^{-2π y₀}`; with `N₁ = 2ϰ log L/π + 2` from
`latticesum_gamma` (o) and `λ(1-λ) ≤ e^{-2π|x|} + ε_λ` this is `lem:varcore` (ii) of
`Weyl/free_fermion/paper/parts/constants.tex`.
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex Barnes MeasureTheory

/-- One-sided geometric tail over a finite set with at most `N₁` points in every unit window of `u`. -/
lemma sum_tail_one_side (S : Finset ℝ) (u : ℝ → ℝ) {N1 y0 X : ℝ} (hy0 : 0 ≤ y0) (hX : 0 ≤ X)
    (hbd : ∀ x ∈ S, u x ≤ X)
    (hcard : ∀ a : ℝ, ((S.filter fun x => a ≤ u x ∧ u x ≤ a + 1).card : ℝ) ≤ N1) :
    ∑ x ∈ S.filter (fun x => y0 ≤ u x), Real.exp (-(2 * Real.pi) * u x) ≤
      2 * N1 * Real.exp (-(2 * Real.pi) * y0) := by
  have hpi := Real.pi_pos
  set T := S.filter (fun x => y0 ≤ u x) with hT
  set K : ℕ := ⌊X⌋₊ + 1 with hK
  set r : ℝ := Real.exp (-(2 * Real.pi)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r ≤ 1 / 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h3 : Real.exp (-(2 * Real.pi)) ≤ Real.exp (-1) :=
      Real.exp_le_exp.2 (by linarith [Real.pi_gt_three])
    have h4 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
    rw [hr]
    calc Real.exp (-(2 * Real.pi)) ≤ (Real.exp 1)⁻¹ := h4 ▸ h3
      _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) h2
  have hN : 0 ≤ N1 := le_trans (Nat.cast_nonneg _) (hcard 0)
  have hmaps : ∀ x ∈ T, ⌊u x - y0⌋₊ ∈ Finset.range K := by
    intro x hx
    rw [hT, Finset.mem_filter] at hx
    rw [Finset.mem_range, hK]
    have h1 : u x - y0 ≤ X := by linarith [hbd x hx.1]
    have := Nat.floor_le_floor h1
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ k ∈ Finset.range K,
      ∑ x ∈ T with ⌊u x - y0⌋₊ = k, Real.exp (-(2 * Real.pi) * u x) ≤
        N1 * (Real.exp (-(2 * Real.pi) * y0) * r ^ k) := by
    intro k _
    set a : ℝ := y0 + k with ha
    have hfib_sub : (T.filter fun x => ⌊u x - y0⌋₊ = k) ⊆ S.filter fun x => a ≤ u x ∧ u x ≤ a + 1 := by
      intro x hx
      rw [Finset.mem_filter, hT, Finset.mem_filter] at hx
      obtain ⟨⟨hxS, hxy⟩, hxk⟩ := hx
      rw [Nat.floor_eq_iff (by linarith)] at hxk
      rw [Finset.mem_filter]
      refine ⟨hxS, by linarith [hxk.1], by linarith [hxk.2]⟩
    have hterm : ∀ x ∈ (T.filter fun x => ⌊u x - y0⌋₊ = k),
        Real.exp (-(2 * Real.pi) * u x) ≤ Real.exp (-(2 * Real.pi) * y0) * r ^ k := by
      intro x hx
      rw [Finset.mem_filter, hT, Finset.mem_filter] at hx
      obtain ⟨⟨hxS, hxy⟩, hxk⟩ := hx
      rw [Nat.floor_eq_iff (by linarith)] at hxk
      have hrk : r ^ k = Real.exp (-(2 * Real.pi) * k) := by
        rw [hr, ← Real.exp_nat_mul]; congr 1; ring
      rw [hrk, ← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith [hxk.1]
    calc ∑ x ∈ T with ⌊u x - y0⌋₊ = k, Real.exp (-(2 * Real.pi) * u x)
        ≤ ∑ _x ∈ (T.filter fun x => ⌊u x - y0⌋₊ = k), Real.exp (-(2 * Real.pi) * y0) * r ^ k :=
          Finset.sum_le_sum hterm
      _ = ((T.filter fun x => ⌊u x - y0⌋₊ = k).card : ℝ) *
            (Real.exp (-(2 * Real.pi) * y0) * r ^ k) := by simp
      _ ≤ N1 * (Real.exp (-(2 * Real.pi) * y0) * r ^ k) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact le_trans (by exact_mod_cast Finset.card_le_card hfib_sub) (hcard a)
  refine (Finset.sum_le_sum hfib).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hg : ∑ k ∈ Finset.range K, r ^ k ≤ 2 := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := K) hr0 (by linarith)
    rw [← Finset.range_eq_Ico] at this
    refine this.trans ?_
    rw [pow_zero, div_le_iff₀ (by linarith)]
    linarith
  have hE := (Real.exp_pos (-(2 * Real.pi) * y0)).le
  calc N1 * (Real.exp (-(2 * Real.pi) * y0) * ∑ k ∈ Finset.range K, r ^ k)
      ≤ N1 * (Real.exp (-(2 * Real.pi) * y0) * 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg hE) hN
    _ = 2 * N1 * Real.exp (-(2 * Real.pi) * y0) := by ring

/-- A window count valid inside `[-X, X]` extends to every interval, by clipping. -/
lemma window_card_clip (S : Finset ℝ) {X c : ℝ} (hc0 : 0 ≤ c) (hS : ∀ x ∈ S, x ∈ Icc (-X) X)
    (hc : ∀ a a' : ℝ, -X ≤ a → a ≤ a' → a' ≤ X →
      ((S.filter fun x => x ∈ Icc a a').card : ℝ) ≤ c * (a' - a) + 2)
    (a a' : ℝ) (haa : a ≤ a') :
    ((S.filter fun x => x ∈ Icc a a').card : ℝ) ≤ c * (a' - a) + 2 := by
  by_cases hne : max a (-X) ≤ min a' X
  · have hsub : (S.filter fun x => x ∈ Icc a a') =
        (S.filter fun x => x ∈ Icc (max a (-X)) (min a' X)) := by
      ext x
      simp only [Finset.mem_filter, mem_Icc, max_le_iff, le_min_iff]
      constructor
      · rintro ⟨hx, h1, h2⟩
        have := hS x hx
        exact ⟨hx, ⟨h1, this.1⟩, h2, this.2⟩
      · rintro ⟨hx, ⟨h1, _⟩, h2, _⟩
        exact ⟨hx, h1, h2⟩
    rw [hsub]
    refine (hc _ _ (le_max_right _ _) hne (min_le_right _ _)).trans ?_
    have : min a' X - max a (-X) ≤ a' - a := by
      have := min_le_left a' X; have := le_max_left a (-X); linarith
    nlinarith
  · have hemp : (S.filter fun x => x ∈ Icc a a') = ∅ := by
      ext x
      simp only [Finset.mem_filter, mem_Icc, Finset.notMem_empty, iff_false, not_and]
      intro hx h1 h2
      apply hne
      have := hS x hx
      exact max_le_iff.2 ⟨h1, this.1⟩ |>.trans (le_trans (by linarith [this.1, this.2])
        (le_min_iff.2 ⟨h2, this.2⟩))
    rw [hemp]; simp
    nlinarith

/-- Two-sided tail: `∑_{|x| ≥ y₀} e^{-2π|x|} ≤ 4 (c + 2) e^{-2π y₀}` when every unit window holds at most
`c + 2` levels. -/
theorem sum_exp_tail_two_sided (S : Finset ℝ) {X c y0 : ℝ} (hc0 : 0 ≤ c) (hy0 : 0 ≤ y0) (hX : 0 ≤ X)
    (hS : ∀ x ∈ S, x ∈ Icc (-X) X)
    (hc : ∀ a a' : ℝ, -X ≤ a → a ≤ a' → a' ≤ X →
      ((S.filter fun x => x ∈ Icc a a').card : ℝ) ≤ c * (a' - a) + 2) :
    ∑ x ∈ S.filter (fun x => y0 ≤ |x|), Real.exp (-(2 * Real.pi) * |x|) ≤
      4 * (c + 2) * Real.exp (-(2 * Real.pi) * y0) := by
  have hcl := window_card_clip S hc0 hS hc
  have hpos := sum_tail_one_side S (fun x => x) (N1 := c + 2) (y0 := y0) (X := X) hy0 hX
    (fun x hx => (hS x hx).2)
    (fun a => by
      have e : (S.filter fun x => a ≤ x ∧ x ≤ a + 1) = S.filter fun x => x ∈ Icc a (a + 1) := by
        ext x; simp [Finset.mem_filter, mem_Icc]
      rw [e]
      have := hcl a (a + 1) (by linarith)
      linarith)
  have hneg := sum_tail_one_side S (fun x => -x) (N1 := c + 2) (y0 := y0) (X := X) hy0 hX
    (fun x hx => by have := (hS x hx).1; linarith)
    (fun a => by
      have e : (S.filter fun x => a ≤ -x ∧ -x ≤ a + 1) = S.filter fun x => x ∈ Icc (-a - 1) (-a) := by
        ext x; simp only [Finset.mem_filter, mem_Icc]
        constructor <;> rintro ⟨h, h1, h2⟩ <;> exact ⟨h, by linarith, by linarith⟩
      rw [e]
      have := hcl (-a - 1) (-a) (by linarith)
      linarith)
  rw [Finset.sum_filter] at hpos hneg ⊢
  have hle : ∑ x ∈ S, (if y0 ≤ |x| then Real.exp (-(2 * Real.pi) * |x|) else 0) ≤
      ∑ x ∈ S, ((if y0 ≤ x then Real.exp (-(2 * Real.pi) * x) else 0) +
        (if y0 ≤ -x then Real.exp (-(2 * Real.pi) * -x) else 0)) := by
    apply Finset.sum_le_sum
    intro x _
    by_cases h : y0 ≤ |x|
    · rw [ite_eq_left h]
      rcases le_abs'.1 h with h1 | h1
      · have : y0 ≤ -x := by linarith
        rw [ite_eq_left this]
        have h0 : 0 ≤ (if y0 ≤ x then Real.exp (-(2 * Real.pi) * x) else 0) := by
          split_ifs <;> positivity
        rw [abs_of_nonpos (by linarith)]
        linarith [show Real.exp (-(2 * Real.pi) * -x) = Real.exp (-(2 * Real.pi) * -x) from rfl]
      · rw [ite_eq_left h1, abs_of_nonneg (by linarith)]
        have h0 : 0 ≤ (if y0 ≤ -x then Real.exp (-(2 * Real.pi) * -x) else 0) := by
          split_ifs <;> positivity
        linarith
    · rw [ite_eq_right h]
      have h0 : 0 ≤ (if y0 ≤ x then Real.exp (-(2 * Real.pi) * x) else 0) := by
        split_ifs <;> positivity
      have h1 : 0 ≤ (if y0 ≤ -x then Real.exp (-(2 * Real.pi) * -x) else 0) := by
        split_ifs <;> positivity
      linarith
  rw [Finset.sum_add_distrib] at hle
  have e1 : ∑ x ∈ S, (if y0 ≤ x then Real.exp (-(2 * Real.pi) * x) else 0) ≤
      2 * (c + 2) * Real.exp (-(2 * Real.pi) * y0) := hpos
  have e2 : ∑ x ∈ S, (if y0 ≤ -x then Real.exp (-(2 * Real.pi) * -x) else 0) ≤
      2 * (c + 2) * Real.exp (-(2 * Real.pi) * y0) := hneg
  linarith

lemma wR_two_mul_le (x : ℝ) : wR (2 * x) ≤ Real.exp (-(2 * Real.pi) * |x|) := by
  have hpi := Real.pi_pos
  unfold wR
  have e : Real.pi * (2 * x) / 2 = Real.pi * x := by ring
  rw [e, ← Real.cosh_abs, show |Real.pi * x| = Real.pi * |x| by rw [abs_mul, abs_of_pos hpi]]
  have hE0 := Real.exp_pos (Real.pi * |x|)
  have hc : Real.exp (Real.pi * |x|) / 2 ≤ Real.cosh (Real.pi * |x|) := by
    rw [Real.cosh_eq]; linarith [(Real.exp_pos (-(Real.pi * |x|))).le]
  have hE : Real.exp (-(2 * Real.pi) * |x|) = (Real.exp (Real.pi * |x|) ^ 2)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; push_cast; ring
  rw [hE, one_div]
  apply inv_anti₀ (by positivity)
  have := pow_le_pow_left₀ (by positivity) hc 2
  nlinarith

/-- **`lem:varcore` (ii)** for the Gamma phase: for every `y₀ ≥ 0`,
`∑_{|x_r| ≥ y₀} λ_r(1-λ_r) ≤ 4(2ϰ log L/π + 2) e^{-2π y₀} + (4ϰ X log L/π + 2) ε_λ`. -/
theorem varcore_tail_gamma (nc : ℕ) (hnc : 1 ≤ nc) {b cs b1 Fm Fp : ℝ}
    (hb : 0 < b) (hcs0 : 0 < cs) (hcs : cs < 1 / 2) (hb1 : 0 < b1)
    (hb1b : b1 < b) (hb1δ : b1 < nc * (1 / 4)) (hFm : 0 < Fm) (hFmp : Fm ≤ Fp) :
    ∃ L0 : ℝ, 1 < L0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ F : Fin nc → ℝ, (∀ i, Fm ≤ F i ∧ F i ≤ Fp) →
      ∀ (X θ0 : ℝ), L ^ (cs / 2) ≤ X → X ≤ L ^ cs →
      ∀ Θ : ℝ → ℝ, ContinuousOn Θ (Icc (-X) X) → StrictMonoOn Θ (Icc (-X) X) →
      (∀ s ∈ Icc (-X) X, |Θ s - gammaG nc (lsum nc L F) θ0 s| ≤ L ^ (-b)) →
      ∀ S : Finset ℝ, (∀ x, x ∈ S ↔ x ∈ Icc (-X) X ∧ ∃ n : ℤ, Θ x = n * Real.pi) →
      ∀ (lam : ℝ → ℝ) (epl y0 : ℝ), 0 ≤ epl → 0 ≤ y0 →
        (∀ x ∈ S, 0 ≤ lam x ∧ lam x ≤ 1 ∧ |lam x - nuR (2 * Real.pi * x)| ≤ epl) →
        ∑ x ∈ S.filter (fun x => y0 ≤ |x|), lam x * (1 - lam x) ≤
          4 * (2 * nc * Real.log L / Real.pi + 2) * Real.exp (-(2 * Real.pi) * y0) +
            (4 * nc * X * Real.log L / Real.pi + 2) * epl := by
  have hb1δ' : b1 < nc * min (1 / 4 : ℝ) (1 / 4) := by rwa [min_self]
  obtain ⟨C, L0, hC, hL0, H⟩ := latticesum_gamma nc hnc (b := b) (cs := cs) (δ := 1 / 4)
    (κ := 2 * Real.pi) (b1 := b1) (Fm := Fm) (Fp := Fp) hb hcs0 hcs (by norm_num)
    (by positivity) hb1 hb1b hb1δ' hFm hFmp
  refine ⟨L0, hL0, ?_⟩
  intro L hL F hF X θ0 hX hXu Θ hΘc hΘm hΘG S hS lam epl y0 hε hy0 hlam
  obtain ⟨ho, -⟩ := H L hL F hF X θ0 hX hXu Θ hΘc hΘm hΘG S hS
  have hL1 : 1 < L := lt_of_lt_of_le hL0 hL
  have hXpos : 0 < X := lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hX
  have hmem : ∀ x ∈ S, x ∈ Icc (-X) X := fun x hx => ((hS x).1 hx).1
  have hncpos : (0 : ℝ) < nc := by exact_mod_cast hnc
  have hlogpos : 0 ≤ Real.log L := Real.log_nonneg hL1.le
  have hc0 : 0 ≤ 2 * (nc : ℝ) * Real.log L / Real.pi := by positivity
  have hexp := sum_exp_tail_two_sided S (c := 2 * nc * Real.log L / Real.pi) hc0 hy0 hXpos.le hmem
    ho.1
  have hcard : (S.card : ℝ) ≤ 4 * nc * X * Real.log L / Real.pi + 2 := by
    have h := ho.1 (-X) X (le_refl _) (by linarith) (le_refl _)
    have hfil : S.filter (fun x => x ∈ Icc (-X) X) = S := Finset.filter_true_of_mem hmem
    rw [hfil] at h
    calc (S.card : ℝ) ≤ _ := h
      _ = 4 * nc * X * Real.log L / Real.pi + 2 := by ring
  have hpt : ∀ x ∈ S.filter (fun x => y0 ≤ |x|),
      lam x * (1 - lam x) ≤ Real.exp (-(2 * Real.pi) * |x|) + epl := by
    intro x hx
    obtain ⟨h0, h1, h2⟩ := hlam x (Finset.mem_filter.1 hx).1
    have := (abs_le.1 ((lipschitz_var h0 h1 (nuR_mem _).1 (nuR_mem _).2).trans h2)).2
    rw [nuR_mul_one_sub x] at this
    linarith [wR_two_mul_le x]
  calc ∑ x ∈ S.filter (fun x => y0 ≤ |x|), lam x * (1 - lam x)
      ≤ ∑ x ∈ S.filter (fun x => y0 ≤ |x|), (Real.exp (-(2 * Real.pi) * |x|) + epl) :=
        Finset.sum_le_sum hpt
    _ = ∑ x ∈ S.filter (fun x => y0 ≤ |x|), Real.exp (-(2 * Real.pi) * |x|) +
          (S.filter (fun x => y0 ≤ |x|)).card * epl := by
        rw [Finset.sum_add_distrib]; simp
    _ ≤ 4 * (2 * nc * Real.log L / Real.pi + 2) * Real.exp (-(2 * Real.pi) * y0) +
          (4 * nc * X * Real.log L / Real.pi + 2) * epl := by
        have hc' : ((S.filter (fun x => y0 ≤ |x|)).card : ℝ) ≤ S.card := by
          exact_mod_cast Finset.card_filter_le _ _
        have := mul_le_mul_of_nonneg_right (hc'.trans hcard) hε
        linarith

/-- info: 'FormalResearch.Special.Lattice.varcore_tail_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms varcore_tail_gamma

end FormalResearch.Special.Lattice

