module

public import FormalResearch.Special.DiscreteAiryKappaRiemann
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Sharp `κ`: the geometry of the band (plan K1, sharp constant, step 8)

* `ksg_sv`: for `q_{k₀+m+1} < q_*`, `Σ_{i≤m} P_{k₀+i}/2 ≤ (π/2) N` and `(π/2) N (1 - a) ≤ Σ_{i≤m} P_{k₀+i}/2`, with `N = 1/h` and
  `a = q_{k₀-1}/q_* + √(1 - (q_{k₀+m}/q_*)²)` (Jordan inequalities for `arcsin`, with `kr_sum_bounds`);
* `ksg_index`: the band indices `k₀ = ⌈η/h⌉`, `b = ⌊q_A/h - ½⌋`, `q_A = √(q_*² - A²)`.

**Claim class: proved.**
-/

@[expose] public section

open Finset

namespace FormalResearch.Special

/-- Jordan: `arcsin z ≤ (π/2) z` on `[0,1]`. -/
lemma ksg_arcsin_le {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) : Real.arcsin z ≤ Real.pi / 2 * z := by
  have hy0 : 0 ≤ Real.arcsin z := Real.arcsin_nonneg.2 h0
  have hy1 : Real.arcsin z ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two z
  have := Real.mul_le_sin hy0 hy1
  rw [Real.sin_arcsin (by linarith) h1] at this
  have hπ := Real.pi_pos
  have h2 : Real.arcsin z * (2 / Real.pi) ≤ z := by linarith
  rw [mul_div_assoc', div_le_iff₀ hπ] at h2
  nlinarith

/-- Jordan: `π/2 - arcsin w ≤ (π/2) √(1 - w²)` on `[0,1]`. -/
lemma ksg_arccos_le {w : ℝ} (h0 : 0 ≤ w) (_h1 : w ≤ 1) : Real.pi / 2 - Real.arcsin w ≤ Real.pi / 2 * √(1 - w ^ 2) := by
  have hy0 : 0 ≤ Real.arccos w := Real.arccos_nonneg w
  have hy1 : Real.arccos w ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.2 h0
  have := Real.mul_le_sin hy0 hy1
  rw [Real.sin_arccos] at this
  have hπ := Real.pi_pos
  have h2 : Real.arccos w * (2 / Real.pi) ≤ √(1 - w ^ 2) := by linarith
  rw [mul_div_assoc', div_le_iff₀ hπ] at h2
  rw [Real.arccos_eq_pi_div_two_sub_arcsin] at h2
  nlinarith

/-- **The band sum of the profile**: `(π/2)N(1 - a) ≤ Σ P/2 ≤ (π/2)N` (lattice `q_k = (k + θ) h`, `θ > 0`). -/
theorem ksg_sv_g {θ qs h : ℝ} (hθ : 0 < θ) {k0 : ℤ} (m : ℕ) (hq : 0 < qs) (hh : 0 < h) (hk0 : 1 ≤ k0)
    (hend : kpUg θ h (k0 + (m : ℤ) + 1) < qs) :
    ∑ i ∈ range (m + 1), kpPg θ qs h (k0 + (i : ℤ)) / 2 ≤ Real.pi / 2 * (1 / h) ∧
    Real.pi / 2 * (1 / h) * (1 - (kpUg θ h (k0 - 1) / qs + √(1 - (kpUg θ h (k0 + (m : ℤ)) / qs) ^ 2))) ≤
      ∑ i ∈ range (m + 1), kpPg θ qs h (k0 + (i : ℤ)) / 2 := by
  obtain ⟨hlo, hhi⟩ := kr_sum_bounds_g hθ (qs := qs) (h := h) (k0 := k0) m hq hh hk0 hend
  have hk' : (1 : ℝ) ≤ k0 := by exact_mod_cast hk0
  have hsum : ∑ i ∈ range (m + 1), kpPg θ qs h (k0 + (i : ℤ)) / 2 = ∑ i ∈ range (m + 1), 1 / kpαg θ qs h (k0 + (i : ℤ)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold kpPg
    ring
  rw [hsum]
  have hπ := Real.pi_pos
  have hU0 : ∀ j : ℤ, 1 ≤ j → 0 < kpUg θ h j := fun j hj => by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    unfold kpUg; exact mul_pos (by linarith) hh
  have hUm : kpUg θ h (k0 + (m : ℤ)) < qs := by
    have : kpUg θ h (k0 + (m : ℤ)) ≤ kpUg θ h (k0 + (m : ℤ) + 1) := by unfold kpUg; push_cast; nlinarith
    linarith
  have hUm0 : 0 < kpUg θ h (k0 + (m : ℤ)) := hU0 _ (by omega)
  have hU1 : 0 ≤ kpUg θ h (k0 - 1) := by unfold kpUg; push_cast; nlinarith
  have hU1q : kpUg θ h (k0 - 1) ≤ kpUg θ h (k0 + (m : ℤ)) := by unfold kpUg; push_cast; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; nlinarith
  have e1 : 1 / h * (h * ∑ i ∈ range (m + 1), 1 / kpαg θ qs h (k0 + (i : ℤ))) = ∑ i ∈ range (m + 1), 1 / kpαg θ qs h (k0 + (i : ℤ)) := by
    field_simp
  constructor
  · have hA0 : 0 ≤ Real.arcsin (kpUg θ h k0 / qs) := Real.arcsin_nonneg.2 (by have := hU0 k0 hk0; positivity)
    have hA1 : Real.arcsin (kpUg θ h (k0 + (m : ℤ) + 1) / qs) ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
    have : h * ∑ i ∈ range (m + 1), 1 / kpαg θ qs h (k0 + (i : ℤ)) ≤ Real.pi / 2 := by linarith
    rw [← e1]
    exact mul_le_mul_of_nonneg_left this (by positivity) |>.trans (by rw [mul_comm])
  · have hw0 : 0 ≤ kpUg θ h (k0 + (m : ℤ)) / qs := by positivity
    have hw1 : kpUg θ h (k0 + (m : ℤ)) / qs ≤ 1 := by rw [div_le_one hq]; exact hUm.le
    have hz0 : 0 ≤ kpUg θ h (k0 - 1) / qs := by positivity
    have hz1 : kpUg θ h (k0 - 1) / qs ≤ 1 := by rw [div_le_one hq]; linarith
    have j1 := ksg_arccos_le hw0 hw1
    have j2 := ksg_arcsin_le hz0 hz1
    have key : Real.pi / 2 * (1 - (kpUg θ h (k0 - 1) / qs + √(1 - (kpUg θ h (k0 + (m : ℤ)) / qs) ^ 2))) ≤
        h * ∑ i ∈ range (m + 1), 1 / kpαg θ qs h (k0 + (i : ℤ)) := by nlinarith
    rw [← e1]
    have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 1 / h)
    calc Real.pi / 2 * (1 / h) * (1 - (kpUg θ h (k0 - 1) / qs + √(1 - (kpUg θ h (k0 + (m : ℤ)) / qs) ^ 2))) =
        1 / h * (Real.pi / 2 * (1 - (kpUg θ h (k0 - 1) / qs + √(1 - (kpUg θ h (k0 + (m : ℤ)) / qs) ^ 2)))) := by ring
      _ ≤ _ := this

/-- info: 'FormalResearch.Special.ksg_sv_g' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksg_sv_g

/-- **The band sum of the profile**: `(π/2)N(1 - a) ≤ Σ P/2 ≤ (π/2)N`. -/
theorem ksg_sv {qs h : ℝ} {k0 : ℤ} (m : ℕ) (hq : 0 < qs) (hh : 0 < h) (hk0 : 1 ≤ k0)
    (hend : kpU h (k0 + (m : ℤ) + 1) < qs) :
    ∑ i ∈ range (m + 1), kpP qs h (k0 + (i : ℤ)) / 2 ≤ Real.pi / 2 * (1 / h) ∧
    Real.pi / 2 * (1 / h) * (1 - (kpU h (k0 - 1) / qs + √(1 - (kpU h (k0 + (m : ℤ)) / qs) ^ 2))) ≤
      ∑ i ∈ range (m + 1), kpP qs h (k0 + (i : ℤ)) / 2 := ksg_sv_g (θ := 1 / 2) (by norm_num) m hq hh hk0 hend

/-- **The band indices**: for `h > 0`, `η > 0`, `qA > 0` with `η + 4h ≤ qA` there are integers `1 ≤ k₀`, `k₀ + 1 ≤ b` with
`η ≤ k₀ h < η + h` and `q_b ≤ qA < q_b + h` (`q_j = (j + ½)h`). -/
lemma ksg_index {h η qA : ℝ} (hh : 0 < h) (hη : 0 < η) (hgap : η + 4 * h ≤ qA) :
    ∃ k0 b : ℤ, 1 ≤ k0 ∧ k0 + 1 ≤ b ∧ η ≤ (k0 : ℝ) * h ∧ (k0 : ℝ) * h < η + h ∧ kpU h b ≤ qA ∧ qA < kpU h b + h := by
  set k0 : ℤ := ⌈η / h⌉ with hk0
  set b : ℤ := ⌊qA / h - 1 / 2⌋ with hb
  have h1 : η / h ≤ (k0 : ℝ) := Int.le_ceil _
  have h2 : (k0 : ℝ) < η / h + 1 := Int.ceil_lt_add_one _
  have h3 : (b : ℝ) ≤ qA / h - 1 / 2 := Int.floor_le _
  have h4 : qA / h - 1 / 2 < (b : ℝ) + 1 := Int.lt_floor_add_one _
  have hη' : 0 < η / h := by positivity
  have e1 : η ≤ (k0 : ℝ) * h := by
    have := mul_le_mul_of_nonneg_right h1 hh.le
    rwa [div_mul_cancel₀ _ hh.ne'] at this
  have e2 : (k0 : ℝ) * h < η + h := by
    have := mul_lt_mul_of_pos_right h2 hh
    rw [add_mul, div_mul_cancel₀ _ hh.ne'] at this
    linarith
  have hk1 : 1 ≤ k0 := by
    have : (0 : ℝ) < k0 := lt_of_lt_of_le hη' h1
    have : (0 : ℤ) < k0 := by exact_mod_cast this
    omega
  have e3 : kpU h b ≤ qA := by
    unfold kpU
    have := mul_le_mul_of_nonneg_right h3 hh.le
    have e : (qA / h - 1 / 2) * h = qA - h / 2 := by field_simp
    nlinarith
  have e4 : qA < kpU h b + h := by
    unfold kpU
    have := mul_lt_mul_of_pos_right h4 hh
    have e : (qA / h - 1 / 2) * h = qA - h / 2 := by field_simp
    nlinarith
  have hkb : k0 + 1 ≤ b := by
    have hlt : (k0 : ℝ) + 3 < (b : ℝ) + 3 / 2 := by
      by_contra hc
      have hc' : (b : ℝ) + 3 / 2 ≤ (k0 : ℝ) + 3 := not_lt.1 hc
      have := mul_le_mul_of_nonneg_right hc' hh.le
      unfold kpU at e4
      nlinarith
    have : (k0 : ℝ) + 1 ≤ b := by linarith
    exact_mod_cast this
  exact ⟨k0, b, hk1, hkb, e1, e2, e3, e4⟩

/-- info: 'FormalResearch.Special.ksg_sv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksg_sv

end FormalResearch.Special
