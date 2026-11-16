module

public import FormalResearch.Special.DiscreteAiryOscPair
public import FormalResearch.Special.DiscreteAiryLimitDefect

/-!
# From exact-coefficient parametrix defects to the hypotheses `DaoPair`

`dao_defect_perturb`: if `a0, c0` are the exact smooth coefficients with row defect `|jac a0 c0 y_k| ≤ K₀ w_k`, and `a, c` are
the actual coefficients with `|a - a0|, |c - c0| ≤ E₆` on the rows, then `|jac a c y_k| ≤ (K₀ + E₆ P (2 C_n + 1)) w_k`
whenever `|y_j| ≤ P w_j` and the weight is locally constant (`w_{k±1} ≤ C_n w_k`).

`dao_pair_of_defects` assembles the structure `DaoPair` (the hypotheses of `dao_decomposition`) from: the lattice gaps/size, the
amplitude bounds `g_min ≤ g ≤ g_max`, the lower bound `a ≥ c_a`, the exact defects of `g Ai` and `g Bi` with respect to
`(a0, c0)`, the coefficient perturbation `E₆`, and the weight neighbour constants `C_n`, with
`K = K₀ + 450 g_max E₆ (2 C_n + 1)`.

`dao_airyWt_nbr`, `dao_airyBiWt_nbr`: the neighbour constants `C_n = (6/5) e^{c₂ √(1+M)}` from `|X_k| ≤ M δ⁻²`, `|ΔX| ≤ c₂ δ ≤ 1`.

**Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- Perturbation of a row defect in the coefficients. -/
lemma dao_defect_perturb {a c a0 c0 y : ℤ → ℝ} {k : ℤ} {w0 w1 w2 w3 E6 P Cn K0 : ℝ}
    (hE : 0 ≤ E6) (hP : 0 ≤ P)
    (ha1 : |a (k + 1) - a0 (k + 1)| ≤ E6) (ha2 : |a k - a0 k| ≤ E6) (hc : |c k - c0 k| ≤ E6)
    (hy1 : |y (k + 1)| ≤ P * w1) (hy2 : |y (k - 1)| ≤ P * w2) (hy3 : |y k| ≤ P * w0)
    (hw1 : w1 ≤ Cn * w3) (hw2 : w2 ≤ Cn * w3) (hw0 : w0 = w3)
    (h0 : |jac a0 c0 y k| ≤ K0 * w3) : |jac a c y k| ≤ (K0 + E6 * P * (2 * Cn + 1)) * w3 := by
  have hp := dal_jac_perturb a0 a c0 c y k
  have e : |jac a c y k| ≤ |jac a0 c0 y k| + |jac a0 c0 y k - jac a c y k| := by
    have := abs_sub_abs_le_abs_sub (jac a c y k) (jac a0 c0 y k)
    rw [abs_sub_comm] at this
    have h2 := abs_sub_comm (jac a c y k) (jac a0 c0 y k)
    linarith
  have t1 : |a0 (k + 1) - a (k + 1)| * |y (k + 1)| ≤ E6 * (P * (Cn * w3)) := by
    rw [abs_sub_comm]
    exact mul_le_mul ha1 (hy1.trans (mul_le_mul_of_nonneg_left hw1 hP)) (abs_nonneg _) hE
  have t2 : |a0 k - a k| * |y (k - 1)| ≤ E6 * (P * (Cn * w3)) := by
    rw [abs_sub_comm]
    exact mul_le_mul ha2 (hy2.trans (mul_le_mul_of_nonneg_left hw2 hP)) (abs_nonneg _) hE
  have t3 : |c0 k - c k| * |y k| ≤ E6 * (P * w3) := by
    rw [abs_sub_comm]
    exact mul_le_mul hc (hy3.trans (by rw [hw0])) (abs_nonneg _) hE
  nlinarith [t1, t2, t3]

/-- `|g Ai(X)| ≤ 25 g_max airyWt X` for `0 ≤ g ≤ g_max`. -/
lemma dao_phi_abs_gen {g X gmax : ℝ} (hg0 : 0 ≤ g) (hg2 : g ≤ gmax) :
    |g * airyAi X| ≤ 25 * gmax * airyWt X := by
  have := (apx_airy_global X).1
  rw [abs_mul, abs_of_nonneg hg0]
  calc g * |airyAi X| ≤ gmax * (25 * airyWt X) := mul_le_mul hg2 this (abs_nonneg _) (hg0.trans hg2)
    _ = _ := by ring

/-- `|g Bi(X)| ≤ 450 g_max airyBiWt X` for `0 ≤ g ≤ g_max`. -/
lemma dao_psi_abs_gen {g X gmax : ℝ} (hg0 : 0 ≤ g) (hg2 : g ≤ gmax) :
    |g * airyBi X| ≤ 450 * gmax * airyBiWt X := by
  have := (apx_airyBi_global X).1
  rw [abs_mul, abs_of_nonneg hg0]
  calc g * |airyBi X| ≤ gmax * (450 * airyBiWt X) := mul_le_mul hg2 this (abs_nonneg _) (hg0.trans hg2)
    _ = _ := by ring

/-- Neighbour constant for `airyWt` (cf. `dal_airyWt_nbr`). -/
lemma dao_airyBiWt_nbr {X X' c2 B δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc2 : 0 ≤ c2) (hc2δ : c2 * δ ≤ 1)
    (hX : |X| ≤ B / δ ^ 2) (hB : 0 ≤ B) (hd : |X' - X| ≤ c2 * δ) :
    airyBiWt X' ≤ 6 / 5 * Real.exp (c2 * √(1 + B)) * airyBiWt X := by
  refine airyBiWt_le_of_close (hd.trans hc2δ) ?_
  have h1 : |X' - X| * √(1 + |X|) ≤ c2 * δ * √(1 + B / δ ^ 2) :=
    mul_le_mul hd (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _) (by positivity)
  refine h1.trans ?_
  have h2 : δ * √(1 + B / δ ^ 2) = √(δ ^ 2 + B) := by
    have : (δ ^ 2 + B) = δ ^ 2 * (1 + B / δ ^ 2) := by field_simp
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hδ.le]
  have h3 : √(δ ^ 2 + B) ≤ √(1 + B) := Real.sqrt_le_sqrt (by nlinarith)
  calc c2 * δ * √(1 + B / δ ^ 2) = c2 * (δ * √(1 + B / δ ^ 2)) := by ring
    _ = c2 * √(δ ^ 2 + B) := by rw [h2]
    _ ≤ c2 * √(1 + B) := mul_le_mul_of_nonneg_left h3 hc2

/-- **Assembly of `DaoPair`.**  `a0, c0` the exact smooth coefficients (with the exact defects `K₀ δ⁶ w` of `g Ai`, `g Bi`),
`a, c` the actual ones within `E δ⁶` on the rows. -/
theorem dao_pair_of_defects {X g a c a0 c0 : ℤ → ℝ} {J N : ℤ} {δ c1 c2 gmin gmax ca K0 E M : ℝ}
    (hJN : J ≤ N) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc1 : 0 < c1) (hc2δ : c2 * δ ≤ 1) (hM : 0 ≤ M) (hc2 : 0 ≤ c2)
    (hgap : ∀ k ∈ Icc J N, c1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ)
    (hXabs : ∀ k ∈ Icc J (N + 1), |X k| ≤ M / δ ^ 2)
    (hgmin : 0 < gmin) (hgb : ∀ k ∈ Icc J (N + 1), gmin ≤ g k ∧ g k ≤ gmax)
    (hca : 0 < ca) (halow : ∀ k ∈ Icc (J + 1) (N + 1), ca ≤ a k) (hK0 : 0 ≤ K0) (hE : 0 ≤ E)
    (ha : ∀ k ∈ Icc (J + 1) (N + 1), |a k - a0 k| ≤ E * δ ^ 6)
    (hc : ∀ k ∈ Icc (J + 1) N, |c k - c0 k| ≤ E * δ ^ 6)
    (hdA : ∀ k ∈ Icc (J + 1) N, |jac a0 c0 (daoPhi g X) k| ≤ K0 * δ ^ 6 * airyWt (X k))
    (hdB : ∀ k ∈ Icc (J + 1) N, |jac a0 c0 (daoPsi g X) k| ≤ K0 * δ ^ 6 * airyBiWt (X k)) :
    DaoPair X g a c J N δ c1 c2 gmin gmax ca
      (K0 + E * (450 * gmax * (2 * (6 / 5 * Real.exp (c2 * √(1 + M))) + 1))) M := by
  have h6 : 0 < δ ^ 6 := by positivity
  set Cn : ℝ := 6 / 5 * Real.exp (c2 * √(1 + M)) with hCn
  have hCn0 : 0 ≤ Cn := by positivity
  have hgmax : 0 < gmax := by
    have := hgb J (by rw [mem_Icc]; omega)
    linarith [this.1, this.2]
  have hP : 0 ≤ 450 * gmax := by positivity
  have hEδ : 0 ≤ E * δ ^ 6 := by positivity
  have hgbk : ∀ k, J ≤ k → k ≤ N + 1 → 0 ≤ g k ∧ g k ≤ gmax := fun k h1 h2 => by
    have := hgb k (by rw [mem_Icc]; omega)
    exact ⟨by linarith [this.1], this.2⟩
  have hnbr : ∀ k ∈ Icc (J + 1) N,
      airyWt (X (k + 1)) ≤ Cn * airyWt (X k) ∧ airyWt (X (k - 1)) ≤ Cn * airyWt (X k) ∧
      airyBiWt (X (k + 1)) ≤ Cn * airyBiWt (X k) ∧ airyBiWt (X (k - 1)) ≤ Cn * airyBiWt (X k) := by
    intro k hk
    rw [mem_Icc] at hk
    have hk0 := hXabs k (by rw [mem_Icc]; omega)
    have g1 := hgap k (by rw [mem_Icc]; omega)
    have g2 := hgap (k - 1) (by rw [mem_Icc]; omega)
    rw [show k - 1 + 1 = k by ring] at g2
    have d1 : |X (k + 1) - X k| ≤ c2 * δ := by
      rw [abs_le]; constructor <;> nlinarith [g1.1, g1.2, hc1, hδ]
    have d2 : |X (k - 1) - X k| ≤ c2 * δ := by
      rw [abs_le]; constructor <;> nlinarith [g2.1, g2.2, hc1, hδ]
    exact ⟨dal_airyWt_nbr hδ hδ1 hc2 hc2δ hk0 hM d1, dal_airyWt_nbr hδ hδ1 hc2 hc2δ hk0 hM d2,
      dao_airyBiWt_nbr hδ hδ1 hc2 hc2δ hk0 hM d1, dao_airyBiWt_nbr hδ hδ1 hc2 hc2δ hk0 hM d2⟩
  refine ⟨hδ, hδ1, hc1, hc2δ, hgap, hXabs, hgmin, hgb, hca, halow, by positivity, fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨n1, n2, -, -⟩ := hnbr k hk
    rw [mem_Icc] at hk
    have b1 := hgbk (k + 1) (by omega) (by omega)
    have b2 := hgbk (k - 1) (by omega) (by omega)
    have b3 := hgbk k (by omega) (by omega)
    have := dao_defect_perturb (a := a) (c := c) (a0 := a0) (c0 := c0) (y := daoPhi g X) (k := k)
      (w0 := airyWt (X k)) (w1 := airyWt (X (k + 1))) (w2 := airyWt (X (k - 1))) (w3 := airyWt (X k))
      (E6 := E * δ ^ 6) (P := 450 * gmax) (Cn := Cn) (K0 := K0 * δ ^ 6) hEδ hP
      (ha (k + 1) (by rw [mem_Icc]; omega)) (ha k (by rw [mem_Icc]; omega)) (hc k (by rw [mem_Icc]; omega))
      ?_ ?_ ?_ n1 n2 rfl (hdA k (by rw [mem_Icc]; omega))
    · calc _ ≤ _ := this
        _ = _ := by ring
    · exact (dao_phi_abs_gen b1.1 b1.2).trans (mul_le_mul_of_nonneg_right (by linarith) (airyWt_pos _).le)
    · exact (dao_phi_abs_gen b2.1 b2.2).trans (mul_le_mul_of_nonneg_right (by linarith) (airyWt_pos _).le)
    · exact (dao_phi_abs_gen b3.1 b3.2).trans (mul_le_mul_of_nonneg_right (by linarith) (airyWt_pos _).le)
  · obtain ⟨-, -, n1, n2⟩ := hnbr k hk
    rw [mem_Icc] at hk
    have b1 := hgbk (k + 1) (by omega) (by omega)
    have b2 := hgbk (k - 1) (by omega) (by omega)
    have b3 := hgbk k (by omega) (by omega)
    have := dao_defect_perturb (a := a) (c := c) (a0 := a0) (c0 := c0) (y := daoPsi g X) (k := k)
      (w0 := airyBiWt (X k)) (w1 := airyBiWt (X (k + 1))) (w2 := airyBiWt (X (k - 1))) (w3 := airyBiWt (X k))
      (E6 := E * δ ^ 6) (P := 450 * gmax) (Cn := Cn) (K0 := K0 * δ ^ 6) hEδ hP
      (ha (k + 1) (by rw [mem_Icc]; omega)) (ha k (by rw [mem_Icc]; omega)) (hc k (by rw [mem_Icc]; omega))
      (dao_psi_abs_gen b1.1 b1.2) (dao_psi_abs_gen b2.1 b2.2) (dao_psi_abs_gen b3.1 b3.2) n1 n2 rfl
      (hdB k (by rw [mem_Icc]; omega))
    calc _ ≤ _ := this
      _ = _ := by ring

/-- info: 'FormalResearch.Special.dao_pair_of_defects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dao_pair_of_defects

end FormalResearch.Special
