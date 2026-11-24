module

public import Mathlib.Analysis.PSeries
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Sums of Lorentzians over separated points (`fw:e3.2a`, block sum)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, "Uniform product comparison": "summing the
right-hand side over all sites in the fixed boosted block costs at most `C Σ_{j∈ℤ}(1+j²)^{-1} = O(1)`".

* `sum_inv_quad_le`: if the points `p k` (`k ∈ S ⊆ ℕ`) satisfy `p j - p k ≥ δ (j - k)` for `k ≤ j` in `S`, then
  for every `u` and `D > 0`, `Σ_{k ∈ S} 1 / (1 + ((u - p k)/D)²) ≤ 2 + 4 (D/δ)²`, with no dependence on
  the number of points or on `u`.

All results are proved unconditionally.
-/

@[expose] public section

open Finset

namespace FormalResearch.ModularBootstrap.Upper.Bump

/-- One-sided version: an injective integer rank `ι` with `d k ≥ δ ι k`. -/
lemma sum_inv_quad_le_aux {T : Finset ℕ} {ι : ℕ → ℕ} {d : ℕ → ℝ} {δ D : ℝ} (hδ : 0 < δ)
    (hD : 0 < D) (hinj : Set.InjOn ι (T : Set ℕ)) (hd : ∀ k ∈ T, δ * (ι k : ℝ) ≤ d k) :
    ∑ k ∈ T, 1 / (1 + (d k / D) ^ 2) ≤ 1 + 2 * (D / δ) ^ 2 := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not T (fun k => ι k = 0)
    (fun k => 1 / (1 + (d k / D) ^ 2))
  rw [← hsplit]
  have hterm : ∀ k, 1 / (1 + (d k / D) ^ 2) ≤ 1 := fun k => by
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg (d k / D)]
  have h0 : ∑ k ∈ T.filter (fun k => ι k = 0), 1 / (1 + (d k / D) ^ 2) ≤ 1 := by
    have hcard : (T.filter (fun k => ι k = 0)).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun a ha b hb => ?_
      rw [Finset.mem_filter] at ha hb
      exact hinj ha.1 hb.1 (ha.2.trans hb.2.symm)
    calc ∑ k ∈ T.filter (fun k => ι k = 0), 1 / (1 + (d k / D) ^ 2)
        ≤ ∑ _k ∈ T.filter (fun k => ι k = 0), (1 : ℝ) := Finset.sum_le_sum fun k _ => hterm k
      _ = ((T.filter (fun k => ι k = 0)).card : ℝ) := by simp
      _ ≤ 1 := by exact_mod_cast hcard
  have h1 : ∑ k ∈ T.filter (fun k => ¬ ι k = 0), 1 / (1 + (d k / D) ^ 2) ≤ 2 * (D / δ) ^ 2 := by
    set T1 := T.filter (fun k => ¬ ι k = 0) with hT1
    have hpt : ∀ k ∈ T1, 1 / (1 + (d k / D) ^ 2) ≤ (D / δ) ^ 2 * (((ι k : ℝ) ^ 2)⁻¹) := by
      intro k hk
      rw [hT1, Finset.mem_filter] at hk
      have hιpos : (0 : ℝ) < ι k := by exact_mod_cast Nat.pos_of_ne_zero hk.2
      have hdk : δ * (ι k : ℝ) ≤ d k := hd k hk.1
      have hdpos : 0 < d k := lt_of_lt_of_le (by positivity) hdk
      have hz : (δ * (ι k : ℝ) / D) ^ 2 ≤ (d k / D) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        exact div_le_div_of_nonneg_right hdk hD.le
      have hzpos : 0 < (δ * (ι k : ℝ) / D) ^ 2 := by positivity
      calc 1 / (1 + (d k / D) ^ 2) ≤ 1 / (δ * (ι k : ℝ) / D) ^ 2 := by
            apply one_div_le_one_div_of_le hzpos
            linarith
        _ = (D / δ) ^ 2 * (((ι k : ℝ) ^ 2)⁻¹) := by
            field_simp
    have himg : T1.image ι ⊆ Finset.Ioo 0 (T.sup ι + 1) := by
      intro j hj
      rw [Finset.mem_image] at hj
      obtain ⟨k, hk, rfl⟩ := hj
      rw [hT1, Finset.mem_filter] at hk
      rw [Finset.mem_Ioo]
      exact ⟨Nat.pos_of_ne_zero hk.2, Nat.lt_succ_of_le (Finset.le_sup (f := ι) hk.1)⟩
    have hinj1 : ∀ x ∈ T1, ∀ y ∈ T1, ι x = ι y → x = y := fun x hx y hy hxy =>
      hinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy
    calc ∑ k ∈ T1, 1 / (1 + (d k / D) ^ 2)
        ≤ ∑ k ∈ T1, (D / δ) ^ 2 * (((ι k : ℝ) ^ 2)⁻¹) := Finset.sum_le_sum hpt
      _ = (D / δ) ^ 2 * ∑ k ∈ T1, (((ι k : ℝ) ^ 2)⁻¹) := by rw [← Finset.mul_sum]
      _ = (D / δ) ^ 2 * ∑ j ∈ T1.image ι, (((j : ℝ) ^ 2)⁻¹) := by
          rw [Finset.sum_image hinj1]
      _ ≤ (D / δ) ^ 2 * ∑ j ∈ Finset.Ioo 0 (T.sup ι + 1), (((j : ℝ) ^ 2)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg himg fun j _ _ => by positivity
      _ ≤ (D / δ) ^ 2 * 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := sum_Ioo_inv_sq_le (α := ℝ) 0 (T.sup ι + 1)
          simpa using this
      _ = 2 * (D / δ) ^ 2 := by ring
  linarith

/-- **Block sum.**  If `p j - p k ≥ δ (j - k)` for `k ≤ j` in `S`, then for every `u`,
`Σ_{k ∈ S} 1 / (1 + ((u - p k)/D)²) ≤ 2 + 4 (D/δ)²`. -/
theorem sum_inv_quad_le {S : Finset ℕ} {p : ℕ → ℝ} {δ D : ℝ} (hδ : 0 < δ) (hD : 0 < D)
    (hsp : ∀ k ∈ S, ∀ j ∈ S, k ≤ j → δ * ((j : ℝ) - k) ≤ p j - p k) (u : ℝ) :
    ∑ k ∈ S, 1 / (1 + ((u - p k) / D) ^ 2) ≤ 2 + 4 * (D / δ) ^ 2 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not S (fun k => u < p k)]
  have hsq : ∀ k, 1 / (1 + ((u - p k) / D) ^ 2) = 1 / (1 + ((p k - u) / D) ^ 2) := fun k => by
    congr 2
    rw [← neg_sub, neg_div, neg_sq]
  have hP : ∑ k ∈ S.filter (fun k => u < p k), 1 / (1 + ((u - p k) / D) ^ 2) ≤
      1 + 2 * (D / δ) ^ 2 := by
    rcases (S.filter (fun k => u < p k)).eq_empty_or_nonempty with he | hne
    · rw [he]; simp; positivity
    set T := S.filter (fun k => u < p k) with hT
    set m := T.min' hne with hm
    have hmT : m ∈ T := Finset.min'_mem T hne
    simp_rw [hsq]
    refine sum_inv_quad_le_aux (ι := fun k => k - m) (d := fun k => p k - u) hδ hD ?_ ?_
    · intro a ha b hb hab
      have ha' := Finset.min'_le T a ha
      have hb' := Finset.min'_le T b hb
      simp only at hab
      omega
    · intro k hk
      have hkm : m ≤ k := Finset.min'_le T k hk
      have hkS : k ∈ S := (Finset.mem_filter.mp hk).1
      have hmS : m ∈ S := (Finset.mem_filter.mp hmT).1
      have hmu : u < p m := (Finset.mem_filter.mp hmT).2
      have := hsp m hmS k hkS hkm
      rw [Nat.cast_sub hkm]
      linarith
  have hM : ∑ k ∈ S.filter (fun k => ¬ u < p k), 1 / (1 + ((u - p k) / D) ^ 2) ≤
      1 + 2 * (D / δ) ^ 2 := by
    rcases (S.filter (fun k => ¬ u < p k)).eq_empty_or_nonempty with he | hne
    · rw [he]; simp; positivity
    set T := S.filter (fun k => ¬ u < p k) with hT
    set M := T.max' hne with hMdef
    have hMT : M ∈ T := Finset.max'_mem T hne
    refine sum_inv_quad_le_aux (ι := fun k => M - k) (d := fun k => u - p k) hδ hD ?_ ?_
    · intro a ha b hb hab
      have ha' := Finset.le_max' T a ha
      have hb' := Finset.le_max' T b hb
      simp only at hab
      omega
    · intro k hk
      have hkM : k ≤ M := Finset.le_max' T k hk
      have hkS : k ∈ S := (Finset.mem_filter.mp hk).1
      have hMS : M ∈ S := (Finset.mem_filter.mp hMT).1
      have hMu : p M ≤ u := not_lt.mp (Finset.mem_filter.mp hMT).2
      have := hsp k hkS M hMS hkM
      rw [Nat.cast_sub hkM]
      linarith
  linarith

/-- info: 'FormalResearch.ModularBootstrap.Upper.Bump.sum_inv_quad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sum_inv_quad_le

end FormalResearch.ModularBootstrap.Upper.Bump
