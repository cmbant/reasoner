module

public import FormalResearch.ModularBootstrap.Upper.Holes.HolePairs

/-!
# The product over the hole of a modified comb

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Step (3), the displayed lower bound of
`∏_{k∈H} ρ_k` through the pair `k₀` (nearest site to `x`) and the seven other pairs of the `j = 4` hole
`H = {n-3, …, n+4}`.

* `holeSet_caseA`, `holeSet_caseB`: the two layouts of the hole around `k₀ = n` (`x ≥ χ_n`) and `k₀ = n+1`:
  `k₀` together with four "near" indices (at distance `≥ (i + ½)ℓ`, `i = 0..3`) and three "far" indices
  (at distance `≥ (i + 1)ℓ`, `i = 0..2`).
* `prod_hole_decomp`: `∏_{k∈H} L(k) = L(k₀) · ∏_{i<4} L(near i) · ∏_{i<3} L(far i)`.
* `holeProduct_lower`: the product `∏_{k ∈ T} ρ_k` over any subset `T ⊆ H` (the modified pairs of the hole)
  is at least `L₀ (1-δ)⁷ (16647192576/23591176505) (1 - (7/4)(θ-1))` as soon as the pair `k₀` has `ρ ≥ L₀`
  (`0 ≤ L₀ ≤ 1`) and the near/far pairs have `ρ ≥ (1-δ)(1 + θ/(16a²))⁻¹` (`a = i+½`, resp. `i+1`).
* `otherPair_factor_lower`: such a bound for one pair from the geometry of the hole
  (`|x-χ_k| ≥ (1-2γ) a ℓ`, `ε⁰_k ≤ (1+γ)ℓ/4`, `|f_x(χ'_k) - f_x(χ_k)| ≤ s`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Holes

open FormalResearch.ModularBootstrap.Upper.Comb

/-! ### 1. The layout of the hole -/

lemma prod_hole_decomp {S : Finset ℕ} {k0 : ℕ} {kN kF : ℕ → ℕ}
    (hS : S = insert k0 (Finset.image kN (Finset.range 4) ∪ Finset.image kF (Finset.range 3)))
    (h0N : ∀ i, i < 4 → kN i ≠ k0) (h0F : ∀ i, i < 3 → kF i ≠ k0)
    (hNF : ∀ i, i < 4 → ∀ j, j < 3 → kN i ≠ kF j)
    (hNi : ∀ i, i < 4 → ∀ j, j < 4 → kN i = kN j → i = j)
    (hFi : ∀ i, i < 3 → ∀ j, j < 3 → kF i = kF j → i = j) (L : ℕ → ℝ) :
    ∏ k ∈ S, L k = L k0 * ((∏ i ∈ Finset.range 4, L (kN i)) * ∏ i ∈ Finset.range 3, L (kF i)) := by
  subst hS
  have hnot : k0 ∉ Finset.image kN (Finset.range 4) ∪ Finset.image kF (Finset.range 3) := by
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, not_or, not_exists, not_and]
    exact ⟨fun i hi h => h0N i hi h, fun i hi h => h0F i hi h⟩
  have hdisj : Disjoint (Finset.image kN (Finset.range 4)) (Finset.image kF (Finset.range 3)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_image, Finset.mem_range] at hk1 hk2
    obtain ⟨i, hi, rfl⟩ := hk1
    obtain ⟨j, hj, hij⟩ := hk2
    exact hNF i hi j hj hij.symm
  rw [Finset.prod_insert hnot, Finset.prod_union hdisj,
    Finset.prod_image (fun i hi j hj h => hNi i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) h),
    Finset.prod_image (fun i hi j hj h => hFi i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) h)]

/-- Layout `A`: `k₀ = n`, near indices `n + 1 + i`, far indices `n - 1 - i`. -/
lemma holeSet_caseA {n : ℕ} (hn : 4 ≤ n) :
    holeSet n 4 = insert n (Finset.image (fun i => n + 1 + i) (Finset.range 4) ∪
      Finset.image (fun i => n - 1 - i) (Finset.range 3)) := by
  ext k
  simp only [holeSet, Finset.mem_Icc, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
    Finset.mem_range]
  constructor
  · intro h
    by_cases h1 : k = n
    · exact Or.inl h1
    · by_cases h2 : n < k
      · exact Or.inr (Or.inl ⟨k - n - 1, by omega, by omega⟩)
      · exact Or.inr (Or.inr ⟨n - 1 - k, by omega, by omega⟩)
  · rintro (h | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · constructor <;> omega
    · omega
    · omega

/-- Layout `B`: `k₀ = n + 1`, near indices `n - i`, far indices `n + 2 + i`. -/
lemma holeSet_caseB {n : ℕ} (hn : 4 ≤ n) :
    holeSet n 4 = insert (n + 1) (Finset.image (fun i => n - i) (Finset.range 4) ∪
      Finset.image (fun i => n + 2 + i) (Finset.range 3)) := by
  ext k
  simp only [holeSet, Finset.mem_Icc, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
    Finset.mem_range]
  constructor
  · intro h
    by_cases h1 : k = n + 1
    · exact Or.inl h1
    · by_cases h2 : k ≤ n
      · exact Or.inr (Or.inl ⟨n - k, by omega, by omega⟩)
      · exact Or.inr (Or.inr ⟨k - n - 2, by omega, by omega⟩)
  · rintro (h | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) <;> omega

/-- The product over the hole in layout `A`. -/
lemma prod_holeSet_caseA {n : ℕ} (hn : 4 ≤ n) (L : ℕ → ℝ) :
    ∏ k ∈ holeSet n 4, L k =
      L n * ((∏ i ∈ Finset.range 4, L (n + 1 + i)) * ∏ i ∈ Finset.range 3, L (n - 1 - i)) :=
  prod_hole_decomp (kN := fun i => n + 1 + i) (kF := fun i => n - 1 - i) (holeSet_caseA hn)
    (by intro i hi; omega) (by intro i hi; omega) (by intro i hi j hj; omega)
    (by intro i hi j hj; omega) (by intro i hi j hj; omega) L

/-- The product over the hole in layout `B`. -/
lemma prod_holeSet_caseB {n : ℕ} (hn : 4 ≤ n) (L : ℕ → ℝ) :
    ∏ k ∈ holeSet n 4, L k =
      L (n + 1) * ((∏ i ∈ Finset.range 4, L (n - i)) * ∏ i ∈ Finset.range 3, L (n + 2 + i)) :=
  prod_hole_decomp (kN := fun i => n - i) (kF := fun i => n + 2 + i) (holeSet_caseB hn)
    (by intro i hi; omega) (by intro i hi; omega) (by intro i hi j hj; omega)
    (by intro i hi j hj; omega) (by intro i hi j hj; omega) L

/-! ### 2. Products over a subset of the hole -/

lemma prod_hole_le_prod_subset {T H : Finset ℕ} (hT : T ⊆ H) (ρ L : ℕ → ℝ)
    (hL0 : ∀ k ∈ H, 0 ≤ L k) (hL1 : ∀ k ∈ H, L k ≤ 1) (hρ : ∀ k ∈ T, L k ≤ ρ k) :
    ∏ k ∈ H, L k ≤ ∏ k ∈ T, ρ k := by
  have hsd := Finset.prod_sdiff hT (f := L)
  have h1 : ∏ k ∈ H \ T, L k ≤ 1 :=
    Finset.prod_le_one₀ (fun k hk => hL0 k (Finset.mem_sdiff.mp hk).1)
      (fun k hk => hL1 k (Finset.mem_sdiff.mp hk).1)
  have h2 : 0 ≤ ∏ k ∈ T, L k := Finset.prod_nonneg fun k hk => hL0 k (hT hk)
  have h3 : ∏ k ∈ T, L k ≤ ∏ k ∈ T, ρ k :=
    Finset.prod_le_prod₀ (fun k hk => hL0 k (hT hk)) hρ
  rw [← hsd]
  calc (∏ k ∈ H \ T, L k) * ∏ k ∈ T, L k ≤ 1 * ∏ k ∈ T, L k :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = ∏ k ∈ T, L k := one_mul _
    _ ≤ _ := h3

/-! ### 3. The product over the modified pairs of the hole -/

/-- **The hole product** (`rem:thmU` Step (3), "The pair at `k₀`" and "The other seven hole pairs"):
if the hole `H` is `k₀` together with four near indices `kN i` and three far indices `kF i`, and the
modified pairs `T ⊆ H` satisfy `ρ_{k₀} ≥ b₀` (`0 ≤ b₀ ≤ 1`), `ρ_{kN i} ≥ (1-δ)(1+θ/(16(i+½)²))⁻¹` and
`ρ_{kF i} ≥ (1-δ)(1+θ/(16(i+1)²))⁻¹`, with `1 ≤ θ ≤ 8/7` and `0 ≤ δ ≤ 1`, then
`∏_{k∈T} ρ_k ≥ b₀ (1-δ)⁷ (16647192576/23591176505)(1 - (7/4)(θ-1))`.  The pairs of `H` outside `T`
are unmodified (`ρ = 1`) and are covered because every lower bound is at most `1`. -/
theorem holeProduct_lower {H T : Finset ℕ} {k0 : ℕ} {kN kF : ℕ → ℕ}
    (hS : H = insert k0 (Finset.image kN (Finset.range 4) ∪ Finset.image kF (Finset.range 3)))
    (h0N : ∀ i, i < 4 → kN i ≠ k0) (h0F : ∀ i, i < 3 → kF i ≠ k0)
    (hNF : ∀ i, i < 4 → ∀ j, j < 3 → kN i ≠ kF j)
    (hNi : ∀ i, i < 4 → ∀ j, j < 4 → kN i = kN j → i = j)
    (hFi : ∀ i, i < 3 → ∀ j, j < 3 → kF i = kF j → i = j)
    (hT : T ⊆ H) (ρ : ℕ → ℝ) (hρ0 : ∀ k ∈ T, 0 ≤ ρ k)
    {θ δ b0 : ℝ} (hθ : 1 ≤ θ) (hθ2 : θ ≤ 8 / 7) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hb0 : 0 ≤ b0) (hb01 : b0 ≤ 1)
    (h0 : k0 ∈ T → b0 ≤ ρ k0)
    (hN : ∀ i : ℕ, i < 4 → kN i ∈ T →
      (1 - δ) * (1 + θ / (16 * ((i : ℝ) + 1 / 2) ^ 2))⁻¹ ≤ ρ (kN i))
    (hF : ∀ i : ℕ, i < 3 → kF i ∈ T →
      (1 - δ) * (1 + θ / (16 * ((i : ℝ) + 1) ^ 2))⁻¹ ≤ ρ (kF i)) :
    b0 * ((1 - δ) ^ 7 * holeProdConst * (1 - 7 / 4 * (θ - 1))) ≤ ∏ k ∈ T, ρ k := by
  classical
  set L : ℕ → ℝ := fun k => if k ∈ T then min 1 (ρ k) else 1 with hL
  have hL0 : ∀ k ∈ H, 0 ≤ L k := fun k _ => by
    by_cases hk : k ∈ T
    · simp only [hL, hk, ite_true]; exact le_min zero_le_one (hρ0 k hk)
    · simp [hL, hk]
  have hL1 : ∀ k ∈ H, L k ≤ 1 := fun k _ => by
    by_cases hk : k ∈ T
    · simp only [hL, hk, ite_true]; exact min_le_left _ _
    · simp [hL, hk]
  have hLρ : ∀ k ∈ T, L k ≤ ρ k := fun k hk => by
    simp only [hL, hk, ite_true]; exact min_le_right _ _
  have hle := prod_hole_le_prod_subset hT ρ L hL0 hL1 hLρ
  have hLb : ∀ k (b : ℝ), b ≤ 1 → (k ∈ T → b ≤ ρ k) → b ≤ L k := fun k b hb1 hk => by
    by_cases hkT : k ∈ T
    · simp only [hL, hkT, ite_true]; exact le_min hb1 (hk hkT)
    · simp [hL, hkT, hb1]
  have hδ' : 0 ≤ 1 - δ := by linarith
  have hbN : ∀ i : ℕ, (1 - δ) * (1 + θ / (16 * ((i : ℝ) + 1 / 2) ^ 2))⁻¹ ≤ 1 := fun i => by
    have h1 : 1 ≤ 1 + θ / (16 * ((i : ℝ) + 1 / 2) ^ 2) := by
      have : 0 ≤ θ / (16 * ((i : ℝ) + 1 / 2) ^ 2) := by
        apply div_nonneg (by linarith); positivity
      linarith
    have h2 : (1 + θ / (16 * ((i : ℝ) + 1 / 2) ^ 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    calc _ ≤ 1 * 1 := mul_le_mul (by linarith) h2 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hbF : ∀ i : ℕ, (1 - δ) * (1 + θ / (16 * ((i : ℝ) + 1) ^ 2))⁻¹ ≤ 1 := fun i => by
    have h1 : 1 ≤ 1 + θ / (16 * ((i : ℝ) + 1) ^ 2) := by
      have : 0 ≤ θ / (16 * ((i : ℝ) + 1) ^ 2) := by
        apply div_nonneg (by linarith); positivity
      linarith
    have h2 : (1 + θ / (16 * ((i : ℝ) + 1) ^ 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    calc _ ≤ 1 * 1 := mul_le_mul (by linarith) h2 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hseven := holeSeven_prod hθ (by linarith) hδ0 hδ1 (fun i => L (kN i)) (fun i => L (kF i))
    (fun i hi => hLb _ _ (hbN i) (hN i hi)) (fun i hi => hLb _ _ (hbF i) (hF i hi))
  have hdec : ∏ k ∈ H, L k =
      L k0 * ((∏ i ∈ Finset.range 4, L (kN i)) * ∏ i ∈ Finset.range 3, L (kF i)) :=
    prod_hole_decomp hS h0N h0F hNF hNi hFi L
  have hLk0 : b0 ≤ L k0 := hLb k0 b0 hb01 h0
  have hval : 0 ≤ (1 - δ) ^ 7 * holeProdConst * (1 - 7 / 4 * (θ - 1)) := by
    have := holeProdConst_pos
    have h3 : 0 ≤ 1 - 7 / 4 * (θ - 1) := by linarith
    positivity
  calc b0 * ((1 - δ) ^ 7 * holeProdConst * (1 - 7 / 4 * (θ - 1)))
      ≤ L k0 * ((∏ i ∈ Finset.range 4, L (kN i)) * ∏ i ∈ Finset.range 3, L (kF i)) :=
        mul_le_mul hLk0 hseven hval (hb0.trans hLk0)
    _ = ∏ k ∈ H, L k := hdec.symm
    _ ≤ ∏ k ∈ T, ρ k := hle

/-! ### 4. The pair factors in the form used by the hole product -/

/-- **One of the seven other pairs** (`rem:thmU` Step (3)): the pair `(χ', ε')` against the reference pair
`(χ, ε₀)` with `|f_x(χ') - f_x(χ)| ≤ s`, `ε₀ ≤ e₁` and `16 a² ε₀² ≤ θ (x-χ)²` (the geometry of the hole: the
site is at distance `≥ a ℓ(1-2γ)` and the reference height is `≤ (1+γ)ℓ/4`) has
`q'/q⁰ ≥ (1-δ)(1 + θ/(16a²))⁻¹` whenever `1 - δ ≤ e^{-2s}/(1 + 8 e₁²)`. -/
theorem otherPair_factor_lower {χ χ' ε' ε₀ x s e1 δ θ a : ℝ} (hχ : xiStar ≤ χ) (hχ' : 0 ≤ χ')
    (hx : xiStar ≤ x) (hne : x ≠ χ) (hne' : χ' ≠ x) (hε' : 0 ≤ ε' ∧ ε' ≤ 1 / 2)
    (hε₀ : 0 ≤ ε₀ ∧ ε₀ ≤ 1 / 16) (hs : |realLogT x χ' - realLogT x χ| ≤ s) (hε₀e : ε₀ ≤ e1)
    (hδ1 : δ ≤ 1) (hδ : 1 - δ ≤ Real.exp (-2 * s) / (1 + 8 * e1 ^ 2)) (ha : 0 < a)
    (hgeom : 16 * a ^ 2 * ε₀ ^ 2 ≤ θ * (x - χ) ^ 2) :
    (1 - δ) * (1 + θ / (16 * a ^ 2))⁻¹ ≤ blaschkePairQ χ' ε' x / blaschkePairQ χ ε₀ x := by
  have h := pairQ_ratio_other_lower hχ hχ' hx hne hne' hε' hε₀
  refine le_trans ?_ h
  have hd : 0 < (x - χ) ^ 2 := by
    have : x - χ ≠ 0 := sub_ne_zero.mpr hne
    positivity
  set u : ℝ := ε₀ ^ 2 / (x - χ) ^ 2 with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ θ / (16 * a ^ 2) := by
    rw [hu, div_le_div_iff₀ hd (by positivity)]
    nlinarith
  have hE1 : 0 < 1 + 8 * e1 ^ 2 := by positivity
  have h8 : 1 + 8 * ε₀ ^ 2 ≤ 1 + 8 * e1 ^ 2 := by
    have : ε₀ ^ 2 ≤ e1 ^ 2 := pow_le_pow_left₀ hε₀.1 hε₀e 2
    linarith
  have hexp : Real.exp (-2 * s) ≤ Real.exp (-2 * |realLogT x χ' - realLogT x χ|) :=
    Real.exp_le_exp.mpr (by linarith)
  have h8pos : 0 < 1 + 8 * ε₀ ^ 2 := by positivity
  have hu1pos : 0 < 1 + u := by linarith
  have hθ0 : 0 ≤ θ := by
    by_contra hneg
    push Not at hneg
    have h1 : 0 ≤ 16 * a ^ 2 * ε₀ ^ 2 := by positivity
    nlinarith
  have hθ1 : 0 ≤ θ / (16 * a ^ 2) := by positivity
  have hden : (1 + u) * (1 + 8 * ε₀ ^ 2) ≤ (1 + θ / (16 * a ^ 2)) * (1 + 8 * e1 ^ 2) :=
    mul_le_mul (by linarith) h8 h8pos.le (by linarith)
  have hpos : 0 < (1 + u) * (1 + 8 * ε₀ ^ 2) := by positivity
  have hδ0' : 0 ≤ 1 - δ := by linarith
  calc (1 - δ) * (1 + θ / (16 * a ^ 2))⁻¹
      ≤ (Real.exp (-2 * s) / (1 + 8 * e1 ^ 2)) * (1 + θ / (16 * a ^ 2))⁻¹ := by
        apply mul_le_mul_of_nonneg_right hδ (by
          have : 0 < 1 + θ / (16 * a ^ 2) := by linarith
          positivity)
    _ = Real.exp (-2 * s) / ((1 + θ / (16 * a ^ 2)) * (1 + 8 * e1 ^ 2)) := by
        rw [div_mul_eq_mul_div, inv_eq_one_div, mul_one_div, div_div, mul_comm]
    _ ≤ Real.exp (-2 * s) / ((1 + u) * (1 + 8 * ε₀ ^ 2)) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le hpos hden
    _ ≤ Real.exp (-2 * |realLogT x χ' - realLogT x χ|) / ((1 + u) * (1 + 8 * ε₀ ^ 2)) :=
        div_le_div_of_nonneg_right hexp hpos.le

/-- **The pair at `k₀`** (`rem:thmU` Step (3)): with `ε' = ηℓ`, `ε⁰ = ℓ/4`, `χ' = χ + Δ`,
all displacements and widths `≤ w ≤ 1/16`, and `Δ = 0` or `η² ≤ 1/32`,
`q'/q⁰ ≥ (1 - 16w) · min(1, 16η²) · (1 - 32Δ²/ℓ²)`. -/
theorem pairK0_factor_lower {χ Δ η ℓ x w : ℝ} (hχ : xiStar ≤ χ) (hχ' : xiStar ≤ χ + Δ)
    (hx : xiStar ≤ x) (hw0 : 0 < w) (hw : w ≤ 1 / 16) (ha' : |x - (χ + Δ)| ≤ w) (ha : |x - χ| ≤ w)
    (hη : 0 ≤ η) (hℓ : 0 < ℓ) (hηℓ : η * ℓ ≤ w) (hℓw : 1 / 4 * ℓ ≤ w) (hcase : Δ = 0 ∨ η ^ 2 ≤ 1 / 32) :
    (1 - 16 * w) * (min 1 (16 * η ^ 2) * (1 - 32 * Δ ^ 2 / ℓ ^ 2)) ≤
      blaschkePairQ (χ + Δ) (η * ℓ) x / blaschkePairQ χ (1 / 4 * ℓ) x := by
  have h := pairQ_ratio_lower hχ hχ' hx hw0 hw ha' ha ⟨mul_nonneg hη hℓ.le, hηℓ⟩
    ⟨by positivity, hℓw⟩
  have hR := R_lower (t := x - χ) (Δ := Δ) (η := η) hℓ hcase
  have hform : ((x - (χ + Δ)) ^ 2 + (η * ℓ) ^ 2) / ((x - χ) ^ 2 + (1 / 4 * ℓ) ^ 2) =
      ((x - χ - Δ) ^ 2 + η ^ 2 * ℓ ^ 2) / ((x - χ) ^ 2 + ℓ ^ 2 / 16) := by
    congr 1 <;> ring
  rw [hform] at h
  refine le_trans ?_ h
  exact mul_le_mul_of_nonneg_left hR (by linarith)

/-! ### 5. Positivity of a pair and the exponential of `Σ_H log ρ_k` -/

/-- A pair `(χ, ε)` with `0 ≤ ε ≤ 1/8` and either `χ ≠ x` or `ε > 0` has `q > 0` at `x > 0`. -/
theorem blaschkePairQ_pos_of {χ ε x : ℝ} (hχ : 0 ≤ χ) (hx : 0 < x) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 8)
    (h : χ ≠ x ∨ 0 < ε) : 0 < blaschkePairQ χ ε x := by
  rcases h with hne | hε
  · exact (two_realLogT_le_log_blaschkePairQ hχ hx hne hε0 (by linarith)).1
  · obtain ⟨hlo, hhi⟩ := sinSq_bounds hε0 hε1
    have hpi := Real.pi_pos
    have hpi4 := Real.pi_lt_d2
    have hs0 : 0 < (π * ε / 2) ^ 2 := by positivity
    have hs1 : (π * ε / 2) ^ 2 ≤ 1 / 16 := by
      have h1 : π * ε / 2 ≤ 1 / 4 := by nlinarith
      have h2 : 0 ≤ π * ε / 2 := by positivity
      nlinarith
    have hS0 : 0 < Real.sin (π * ε / 2) ^ 2 := by nlinarith
    have hS1 : Real.sin (π * ε / 2) ^ 2 < 1 := by linarith
    rw [blaschkePairQ_eq_pairFac]
    exact mul_pos (pairFac_pos hS1 (by positivity)) (pairFac_pos hS1 (by positivity))

/-- `exp (Σ_{k∈T} (log a_k - log b_k)) = ∏_{k∈T} a_k / b_k` for positive `a_k, b_k`. -/
theorem exp_sum_log_sub {T : Finset ℕ} (a b : ℕ → ℝ) (ha : ∀ k ∈ T, 0 < a k) (hb : ∀ k ∈ T, 0 < b k) :
    Real.exp (∑ k ∈ T, (Real.log (a k) - Real.log (b k))) = ∏ k ∈ T, (a k / b k) := by
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [Real.exp_sub, Real.exp_log (ha k hk), Real.exp_log (hb k hk)]

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.holeProduct_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.holeProduct_lower

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.otherPair_factor_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.otherPair_factor_lower

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.pairK0_factor_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.pairK0_factor_lower

end FormalResearch.ModularBootstrap.Upper.Holes
