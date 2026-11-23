module

public import FormalResearch.ModularBootstrap.Upper.Holes.HoleComparison

/-!
# Hole pairs of a modified comb: the discriminant lemma, the pair factor, and the finite product

Sources: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Step (3), bullets "The pair at `k_0`" and
"The other seven hole pairs"; `CFT/modular_bootstrap/paper/comb_estimates.tex`, Lemma K1(b), (F3).

* `R_lower_zero`, `R_lower_shift`: `R(t) = ((t-Δ)² + η²ℓ²)/(t² + ℓ²/16) ≥ min(1, 16η²)` if `Δ = 0`, and
  `R(t) ≥ 16η²(1-θ)`, `θ = 32Δ²/ℓ²`, if `η² ≤ 1/32` (the discriminant argument of the paper).
* `pairQ_pair_ratio_lower`: `ρ_{k_0} = q'_{k_0}/q⁰_{k_0} ≥ (1 - 16 w) (a'² + ε'²)/(a⁰² + ε⁰²)` for a pair whose
  displacement and width are `≤ w ≤ 1/16` (`a' = x - χ'`, `a⁰ = x - χ`; the paper's `(1 - Cλ)R(t)`).
* `pairQ_ratio_other_lower`: the other hole pairs, `ρ_k ≥ e^{-2|f_x(χ'_k) - f_x(χ_k)|}/[(1 + ε⁰²/(x-χ_k)²)(1 + 8ε⁰²)]`.
* `holeProdConst`, `holeProd_eq`, `cFl_gt`: the exact rational product of the seven other pairs,
  `∏_{j=1}^4(1 + 1/(16(j-½)²))^{-1} ∏_{j=1}^3 (1 + 1/(16 j²))^{-1} = 16647192576/23591176505`
  (`= 0.70565…`, replacing the Euler products `π/(2 sinh(π/2))` of the paper), and
  `c_fl := (7/10)·16647192576/23591176505 > 0.493`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Holes

open FormalResearch.ModularBootstrap.Upper.Comb

/-! ### 1. The discriminant lemma `R(t)` -/

/-- `Δ = 0`: `R(t) ≥ min(1, 16η²)`. -/
theorem R_lower_zero {t η ℓ : ℝ} (hℓ : 0 < ℓ) :
    min 1 (16 * η ^ 2) ≤ (t ^ 2 + η ^ 2 * ℓ ^ 2) / (t ^ 2 + ℓ ^ 2 / 16) := by
  have hden : 0 < t ^ 2 + ℓ ^ 2 / 16 := by positivity
  rw [le_div_iff₀ hden]
  by_cases h : 16 * η ^ 2 ≤ 1
  · rw [min_eq_right h]
    nlinarith [sq_nonneg t, sq_nonneg η]
  · push Not at h
    rw [min_eq_left h.le]
    nlinarith [sq_nonneg t, sq_nonneg ℓ]

/-- The discriminant argument: for `η² ≤ 1/32` and `θ = 32Δ²/ℓ²`,
`R(t) ≥ 16η²(1 - θ)` for every `t`. -/
theorem R_lower_shift {t Δ η ℓ : ℝ} (hℓ : 0 < ℓ) (hη : η ^ 2 ≤ 1 / 32) :
    16 * η ^ 2 * (1 - 32 * Δ ^ 2 / ℓ ^ 2) ≤
      ((t - Δ) ^ 2 + η ^ 2 * ℓ ^ 2) / (t ^ 2 + ℓ ^ 2 / 16) := by
  have hden : 0 < t ^ 2 + ℓ ^ 2 / 16 := by positivity
  rw [le_div_iff₀ hden]
  set θ : ℝ := 32 * Δ ^ 2 / ℓ ^ 2 with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hΔ : Δ ^ 2 = θ * ℓ ^ 2 / 32 := by
    rw [hθ]; field_simp
  set m : ℝ := 16 * η ^ 2 * (1 - θ) with hm
  have hm_le : m ≤ 16 * η ^ 2 := by
    rw [hm]; nlinarith [sq_nonneg η]
  have hm_half : m ≤ 1 / 2 := by linarith
  have ha : 1 / 2 ≤ 1 - m := by linarith
  -- (1 - m) · Q = ((1 - m) t - Δ)² + ((1 - m) η² ℓ² θ - m Δ²)
  have hQ : (1 - m) * ((t - Δ) ^ 2 + η ^ 2 * ℓ ^ 2 - m * (t ^ 2 + ℓ ^ 2 / 16)) =
      ((1 - m) * t - Δ) ^ 2 + ((1 - m) * (η ^ 2 * ℓ ^ 2 * θ) - m * Δ ^ 2) := by
    have h16 : m * (ℓ ^ 2 / 16) = η ^ 2 * ℓ ^ 2 * (1 - θ) := by rw [hm]; ring
    have : (t - Δ) ^ 2 + η ^ 2 * ℓ ^ 2 - m * (t ^ 2 + ℓ ^ 2 / 16) =
        (1 - m) * t ^ 2 - 2 * Δ * t + Δ ^ 2 + η ^ 2 * ℓ ^ 2 * θ := by
      have : m * (t ^ 2 + ℓ ^ 2 / 16) = m * t ^ 2 + η ^ 2 * ℓ ^ 2 * (1 - θ) := by
        rw [mul_add, h16]
      rw [this]; ring
    rw [this]; ring
  have hbr : 0 ≤ (1 - m) * (η ^ 2 * ℓ ^ 2 * θ) - m * Δ ^ 2 := by
    have h1 : m * Δ ^ 2 ≤ 16 * η ^ 2 * Δ ^ 2 := mul_le_mul_of_nonneg_right hm_le (sq_nonneg Δ)
    have h2 : 16 * η ^ 2 * Δ ^ 2 = (1 / 2) * (η ^ 2 * ℓ ^ 2 * θ) := by rw [hΔ]; ring
    have h3 : (1 / 2) * (η ^ 2 * ℓ ^ 2 * θ) ≤ (1 - m) * (η ^ 2 * ℓ ^ 2 * θ) :=
      mul_le_mul_of_nonneg_right ha (by positivity)
    linarith
  have hQ0 : 0 ≤ (t - Δ) ^ 2 + η ^ 2 * ℓ ^ 2 - m * (t ^ 2 + ℓ ^ 2 / 16) := by
    have hpos : 0 < 1 - m := by linarith
    have : 0 ≤ (1 - m) * ((t - Δ) ^ 2 + η ^ 2 * ℓ ^ 2 - m * (t ^ 2 + ℓ ^ 2 / 16)) := by
      rw [hQ]; positivity
    exact nonneg_of_mul_nonneg_right this hpos
  linarith

/-- Combined form: `R(t) ≥ min(1, 16η²)(1 - θ)` when `Δ = 0` or `η² ≤ 1/32`. -/
theorem R_lower {t Δ η ℓ : ℝ} (hℓ : 0 < ℓ) (h : Δ = 0 ∨ η ^ 2 ≤ 1 / 32) :
    min 1 (16 * η ^ 2) * (1 - 32 * Δ ^ 2 / ℓ ^ 2) ≤
      ((t - Δ) ^ 2 + η ^ 2 * ℓ ^ 2) / (t ^ 2 + ℓ ^ 2 / 16) := by
  rcases h with h | h
  · subst h
    simpa using R_lower_zero (t := t) (η := η) hℓ
  · have : min 1 (16 * η ^ 2) = 16 * η ^ 2 := min_eq_right (by linarith)
    rw [this]
    exact R_lower_shift hℓ h

/-! ### 2. The exact rational product of the seven other hole pairs -/

/-- The exact value of the finite product replacing the Euler products of the paper. -/
noncomputable def holeProdConst : ℝ := 16647192576 / 23591176505

theorem holeProd_eq :
    (∏ i ∈ Finset.range 4, (1 + 1 / (16 * ((i : ℝ) + 1 / 2) ^ 2))⁻¹) *
        ∏ i ∈ Finset.range 3, (1 + 1 / (16 * ((i : ℝ) + 1) ^ 2))⁻¹ = holeProdConst := by
  unfold holeProdConst
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num

theorem holeProdConst_pos : 0 < holeProdConst := by unfold holeProdConst; norm_num

theorem holeProdConst_gt : (7056 / 10000 : ℝ) < holeProdConst := by
  unfold holeProdConst; norm_num

/-- `c_fl := μ₄-lower · (product of the seven other hole pairs)`, with `μ₄ > 7/10`
(`muHole_four_quarter_gt`). Only `c_fl > 0` is used downstream; in fact `c_fl > 0.493`. -/
noncomputable def cFl : ℝ := (7 / 10) * holeProdConst

theorem cFl_pos : 0 < cFl := by unfold cFl; have := holeProdConst_pos; positivity

theorem cFl_gt : (493 / 1000 : ℝ) < cFl := by
  unfold cFl; have := holeProdConst_gt; nlinarith

/-! ### 3. Elementary hyperbolic bounds -/

lemma cosh_sq_le_inv {z : ℝ} (hz : z ^ 2 < 1) : Real.cosh z ^ 2 ≤ 1 / (1 - z ^ 2) := by
  have h1 := Real.cosh_le_exp_half_sq z
  have hc0 := (Real.cosh_pos z).le
  have h2 : Real.cosh z ^ 2 ≤ Real.exp (z ^ 2) := by
    calc Real.cosh z ^ 2 ≤ Real.exp (z ^ 2 / 2) ^ 2 := by gcongr
      _ = Real.exp (z ^ 2) := by rw [sq, ← Real.exp_add]; ring_nf
  have h3 : 1 - z ^ 2 ≤ Real.exp (-(z ^ 2)) := by linarith [Real.add_one_le_exp (-(z ^ 2))]
  have h4 : Real.exp (z ^ 2) * Real.exp (-(z ^ 2)) = 1 := by rw [← Real.exp_add]; simp
  rw [le_div_iff₀ (by linarith)]
  calc Real.cosh z ^ 2 * (1 - z ^ 2) ≤ Real.exp (z ^ 2) * Real.exp (-(z ^ 2)) :=
        mul_le_mul h2 h3 (by linarith) (Real.exp_pos _).le
    _ = 1 := h4

lemma sinh_sq_le {z : ℝ} (hz : z ^ 2 < 1) : Real.sinh z ^ 2 ≤ z ^ 2 / (1 - z ^ 2) := by
  have h1 := cosh_sq_le_inv hz
  have h2 := Real.cosh_sq_sub_sinh_sq z
  have hpos : 0 < 1 - z ^ 2 := by linarith
  have h3 : Real.sinh z ^ 2 ≤ 1 / (1 - z ^ 2) - 1 := by linarith
  calc Real.sinh z ^ 2 ≤ 1 / (1 - z ^ 2) - 1 := h3
    _ = z ^ 2 / (1 - z ^ 2) := by field_simp; ring

lemma sq_le_sinh_sq (z : ℝ) : z ^ 2 ≤ Real.sinh z ^ 2 := by
  have h : |z| ≤ Real.sinh |z| := Real.self_le_sinh_iff.mpr (abs_nonneg z)
  calc z ^ 2 = |z| ^ 2 := (sq_abs z).symm
    _ ≤ Real.sinh |z| ^ 2 := by gcongr
    _ = Real.sinh z ^ 2 := by
        rcases abs_cases z with ⟨h1, _⟩ | ⟨h1, _⟩
        · rw [h1]
        · rw [h1, Real.sinh_neg]; ring

/-- `sin²(πε/2)` against `(πε/2)²` for `0 ≤ ε ≤ 1/8`. -/
lemma sinSq_bounds {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 8) :
    (π * ε / 2) ^ 2 * (1 - (π * ε / 2) ^ 2 / 2) ≤ Real.sin (π * ε / 2) ^ 2 ∧
      Real.sin (π * ε / 2) ^ 2 ≤ (π * ε / 2) ^ 2 := by
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_d2
  set s : ℝ := π * ε / 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := by rw [hs]; nlinarith
  have hsin0 : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs0 (by linarith [Real.pi_gt_three])
  have hsin_le : Real.sin s ≤ s := Real.sin_le hs0
  refine ⟨?_, by nlinarith⟩
  rcases eq_or_lt_of_le hs0 with h | h
  · rw [← h]; simp
  · have hlow := Real.sin_gt_sub_cube h
    have hlow' : s * (1 - s ^ 2 / 4) ≤ Real.sin s := by nlinarith [pow_nonneg hs0 3]
    have hpos : 0 ≤ s * (1 - s ^ 2 / 4) := by
      apply mul_nonneg hs0; nlinarith
    have : (s * (1 - s ^ 2 / 4)) ^ 2 ≤ Real.sin s ^ 2 := by gcongr
    nlinarith [sq_nonneg (s ^ 2 / 4), sq_nonneg s]

/-- The single pair factor `(sinh² z + S²)/(cosh² z - S²)`. -/
noncomputable def pairFac (z S2 : ℝ) : ℝ := (Real.sinh z ^ 2 + S2) / (Real.cosh z ^ 2 - S2)

lemma blaschkePairQ_eq_pairFac (χ ε x : ℝ) :
    blaschkePairQ χ ε x = pairFac (π * (x - χ) / 2) (Real.sin (π * ε / 2) ^ 2) *
      pairFac (π * (x + χ) / 2) (Real.sin (π * ε / 2) ^ 2) := by
  rw [blaschkePairQ_eq]; rfl

lemma cosh_sq_sub_pos {z S2 : ℝ} (hS : S2 < 1) : 0 < Real.cosh z ^ 2 - S2 := by
  have := Real.one_le_cosh z
  nlinarith

lemma pairFac_pos {z S2 : ℝ} (hS : S2 < 1) (h : 0 < Real.sinh z ^ 2 + S2) : 0 < pairFac z S2 :=
  div_pos h (cosh_sq_sub_pos hS)

/-- Minus factor, lower bound: `(z² + s²)(1 - s²/2 - z²) ≤ F(z, sin²(πε/2))`. -/
lemma pairFac_lower_minus {z ε : ℝ} (hz : z ^ 2 ≤ 1 / 4) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 8) :
    (z ^ 2 + (π * ε / 2) ^ 2) * (1 - (π * ε / 2) ^ 2 / 2 - z ^ 2) ≤
      pairFac z (Real.sin (π * ε / 2) ^ 2) := by
  obtain ⟨hSl, hSu⟩ := sinSq_bounds h0 h1
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_d2
  set s2 : ℝ := (π * ε / 2) ^ 2 with hs2
  set S2 : ℝ := Real.sin (π * ε / 2) ^ 2 with hS2
  have hs2_0 : 0 ≤ s2 := sq_nonneg _
  have hs2_small : s2 ≤ 1 / 4 := by
    rw [hs2]
    have : π * ε / 2 ≤ 1 / 2 := by nlinarith
    nlinarith [mul_nonneg hpi.le h0]
  have hS0 : 0 ≤ S2 := sq_nonneg _
  have hS1 : S2 < 1 := by linarith
  have hz1 : z ^ 2 < 1 := by linarith
  have hch := cosh_sq_le_inv hz1
  have hcpos : 0 < Real.cosh z ^ 2 := by positivity
  have hch1 : 1 - z ^ 2 ≤ 1 / Real.cosh z ^ 2 := by
    rw [le_div_iff₀ hcpos]
    have := hch
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - z ^ 2)] at this
    linarith
  have hstep1 : (z ^ 2 + S2) / Real.cosh z ^ 2 ≤ pairFac z S2 := by
    unfold pairFac
    exact div_le_div₀ (by nlinarith [sq_nonneg (Real.sinh z)]) (by nlinarith [sq_le_sinh_sq z])
      (cosh_sq_sub_pos hS1) (by linarith)
  have hstep2 : (z ^ 2 + S2) * (1 - z ^ 2) ≤ (z ^ 2 + S2) / Real.cosh z ^ 2 := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hch1 (by positivity)
  have hz0 : 0 ≤ z ^ 2 := sq_nonneg z
  have hA : (z ^ 2 + s2) * (1 - s2 / 2) ≤ z ^ 2 + S2 := by nlinarith
  have hA0 : 0 ≤ z ^ 2 + s2 := by positivity
  have hB : (z ^ 2 + s2) * (1 - s2 / 2 - z ^ 2) ≤ (z ^ 2 + S2) * (1 - z ^ 2) := by
    have h1' : (z ^ 2 + s2) * (1 - s2 / 2) * (1 - z ^ 2) ≤ (z ^ 2 + S2) * (1 - z ^ 2) :=
      mul_le_mul_of_nonneg_right hA (by linarith)
    have h2' : (z ^ 2 + s2) * (1 - s2 / 2 - z ^ 2) ≤ (z ^ 2 + s2) * (1 - s2 / 2) * (1 - z ^ 2) := by
      nlinarith [mul_nonneg hA0 (mul_nonneg hs2_0 hz0)]
    linarith
  exact hB.trans (hstep2.trans hstep1)

/-- Minus factor, upper bound: `F(z, sin²(πε/2)) ≤ (z² + s²)/((1 - z²)(1 - s²))`. -/
lemma pairFac_upper_minus {z ε : ℝ} (hz : z ^ 2 ≤ 1 / 4) (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 8) :
    pairFac z (Real.sin (π * ε / 2) ^ 2) ≤
      (z ^ 2 + (π * ε / 2) ^ 2) / ((1 - z ^ 2) * (1 - (π * ε / 2) ^ 2)) := by
  obtain ⟨hSl, hSu⟩ := sinSq_bounds h0 h1
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_d2
  set s2 : ℝ := (π * ε / 2) ^ 2 with hs2
  set S2 : ℝ := Real.sin (π * ε / 2) ^ 2 with hS2
  have hs2_0 : 0 ≤ s2 := sq_nonneg _
  have hs2_small : s2 ≤ 1 / 4 := by
    rw [hs2]
    have : π * ε / 2 ≤ 1 / 2 := by nlinarith
    nlinarith [mul_nonneg hpi.le h0]
  have hz1 : z ^ 2 < 1 := by linarith
  have hz0 : 0 ≤ z ^ 2 := sq_nonneg z
  have hpos1 : 0 < 1 - z ^ 2 := by linarith
  have hpos2 : 0 < 1 - s2 := by linarith
  have hsh := sinh_sq_le hz1
  have hnum : Real.sinh z ^ 2 + S2 ≤ (z ^ 2 + s2) / (1 - z ^ 2) := by
    have : z ^ 2 / (1 - z ^ 2) + s2 ≤ (z ^ 2 + s2) / (1 - z ^ 2) := by
      rw [div_add' _ _ _ hpos1.ne', div_le_div_iff_of_pos_right hpos1]
      nlinarith
    linarith
  have hden : 1 - s2 ≤ Real.cosh z ^ 2 - S2 := by
    have := Real.one_le_cosh z
    nlinarith
  unfold pairFac
  have := div_le_div₀ (by positivity) hnum hpos2 hden
  calc _ ≤ ((z ^ 2 + s2) / (1 - z ^ 2)) / (1 - s2) := this
    _ = _ := by rw [div_div]

/-- Plus factor (`sinh² z ≥ 1`): between `tanh² z` and `tanh² z · (1 + S²)/(1 - S²)`. -/
lemma pairFac_ge_tanhSq {z S2 : ℝ} (hS0 : 0 ≤ S2) (hS : S2 < 1) :
    Real.sinh z ^ 2 / Real.cosh z ^ 2 ≤ pairFac z S2 := by
  unfold pairFac
  rw [div_le_div_iff₀ (by positivity) (cosh_sq_sub_pos hS)]
  nlinarith [mul_nonneg hS0 (sq_nonneg (Real.sinh z)), mul_nonneg hS0 (sq_nonneg (Real.cosh z))]

lemma pairFac_le_tanhSq_mul {z S2 : ℝ} (hsh : 1 ≤ Real.sinh z ^ 2) (hS0 : 0 ≤ S2)
    (hS : S2 ≤ 1 / 2) :
    pairFac z S2 ≤ Real.sinh z ^ 2 / Real.cosh z ^ 2 * ((1 + S2) / (1 - S2)) := by
  have hc : Real.cosh z ^ 2 = 1 + Real.sinh z ^ 2 := by linarith [Real.cosh_sq_sub_sinh_sq z]
  have hcpos : 0 < Real.cosh z ^ 2 := by positivity
  unfold pairFac
  rw [div_mul_div_comm, div_le_div_iff₀ (cosh_sq_sub_pos (by linarith)) (by nlinarith)]
  rw [hc]
  generalize Real.sinh z ^ 2 = sh at hsh ⊢
  nlinarith [mul_nonneg hS0 (by nlinarith : 0 ≤ 2 * sh ^ 2 - 1 + S2)]

/-- General upper bound `F(z, S²) ≤ F(z, 0)·(1 + S²/sinh² z)/(1 - S²)` (`sinh z ≠ 0`). -/
lemma pairFac_le_mul {z S2 : ℝ} (hsh : 0 < Real.sinh z ^ 2) (hS0 : 0 ≤ S2) (hS : S2 < 1) :
    pairFac z S2 ≤ Real.sinh z ^ 2 / Real.cosh z ^ 2 * ((1 + S2 / Real.sinh z ^ 2) / (1 - S2)) := by
  have hc1 : 1 ≤ Real.cosh z ^ 2 := by have := Real.one_le_cosh z; nlinarith
  have hcpos : 0 < Real.cosh z ^ 2 := by linarith
  have h1S : 0 < 1 - S2 := by linarith
  have heq : Real.sinh z ^ 2 / Real.cosh z ^ 2 * ((1 + S2 / Real.sinh z ^ 2) / (1 - S2)) =
      (Real.sinh z ^ 2 + S2) / (Real.cosh z ^ 2 * (1 - S2)) := by
    have hne : Real.sinh z ^ 2 ≠ 0 := hsh.ne'
    generalize Real.sinh z ^ 2 = A at hsh hne ⊢
    generalize Real.cosh z ^ 2 = B at hc1 hcpos ⊢
    field_simp
  rw [heq]
  unfold pairFac
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

/-! ### 4. The other hole pairs -/

/-- `|combH a - combH b| ≤ π |a - b|` for `a, b ≥ ξ_*` (`𝔥'(z) = π/sinh(πz) ≤ π`). -/
lemma abs_combH_sub_le {a b : ℝ} (ha : xiStar ≤ a) (hb : xiStar ≤ b) :
    |combH a - combH b| ≤ π * |a - b| := by
  have hpi := Real.pi_pos
  have hy : ∀ y ∈ Set.uIcc a b, xiStar ≤ y := fun y hy => by
    rcases Set.mem_uIcc.mp hy with h | h
    · exact ha.trans h.1
    · exact hb.trans h.1
  have hderiv : ∀ y ∈ Set.uIcc a b, HasDerivWithinAt combH (combHDeriv y) (Set.uIcc a b) y :=
    fun y hyy => (hasDerivAt_combH (xiStar_pos.trans_le (hy y hyy))).hasDerivWithinAt
  have hbound : ∀ y ∈ Set.uIcc a b, ‖combHDeriv y‖ ≤ π := fun y hyy => by
    have hy1 : 1 ≤ Real.sinh (π * y) := by
      rw [← sinh_pi_mul_xiStar]
      exact Real.sinh_le_sinh.mpr (by nlinarith [hy y hyy])
    have hpos : 0 < combHDeriv y := by
      unfold combHDeriv; exact div_pos hpi (by linarith)
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    unfold combHDeriv
    exact div_le_self hpi.le hy1
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_uIcc a b) Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs, abs_sub_comm] using this

/-- `e^{2 f_x(χ)} = T_χ(x)²`, the pair modulus at zero width. -/
lemma exp_two_realLogT_eq {χ x : ℝ} (hχ : 0 ≤ χ) (hx : 0 < x) (hne : χ ≠ x) :
    Real.exp (2 * realLogT x χ) = blaschkePairQ χ 0 x := by
  have hT := norm_blaschkeT_real_pos hχ hx hne
  rw [blaschkePairQ_zero_eps_eq_norm_sq, show 2 * realLogT x χ = realLogT x χ + realLogT x χ by ring,
    Real.exp_add]
  unfold realLogT
  rw [Real.exp_log hT]; ring

lemma one_add_div_le {s2 e : ℝ} (hs2 : 0 ≤ s2) (h : s2 ≤ (π / 2) ^ 2 * e) (he0 : 0 ≤ e) (he : e ≤ 1 / 256) :
    (1 + s2) / (1 - s2) ^ 2 ≤ 1 + 8 * e := by
  have hpi4 := Real.pi_lt_d2
  have hpi := Real.pi_pos
  have hk : (π / 2) ^ 2 ≤ 2.5 := by nlinarith
  have hs : s2 ≤ 2.5 * e := by nlinarith
  have hs' : s2 ≤ 1 / 100 := by nlinarith
  have hpos : 0 < (1 - s2) ^ 2 := by nlinarith
  rw [div_le_iff₀ hpos]
  nlinarith [mul_nonneg hs2 he0, mul_nonneg hs2 hs2]

lemma mul_div_aux (a b E s : ℝ) (hs : 1 - s ≠ 0) :
    a * ((1 + E) / (1 - s)) * (b * ((1 + s) / (1 - s))) = a * b * ((1 + E) * ((1 + s) / (1 - s) ^ 2)) := by
  field_simp

/-- The pair modulus is at most `T_χ(x)²` times `(1 + ε²/(x-χ)²)(1 + 8ε²)` (for `ε ≤ 1/16`,
`x, χ ≥ ξ_*`, `x ≠ χ`). -/
theorem blaschkePairQ_le_mul {χ ε x : ℝ} (hχ : xiStar ≤ χ) (hx : xiStar ≤ x) (hne : x ≠ χ)
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 16) :
    blaschkePairQ χ ε x ≤
      blaschkePairQ χ 0 x * ((1 + ε ^ 2 / (x - χ) ^ 2) * (1 + 8 * ε ^ 2)) := by
  have hpi := Real.pi_pos
  obtain ⟨hSl, hSu⟩ := sinSq_bounds h0 (by linarith : ε ≤ 1 / 8)
  set s2 : ℝ := (π * ε / 2) ^ 2 with hs2
  set S2 : ℝ := Real.sin (π * ε / 2) ^ 2 with hS2
  have hs2e : s2 = (π / 2) ^ 2 * ε ^ 2 := by rw [hs2]; ring
  have hs2_0 : 0 ≤ s2 := sq_nonneg _
  have hS0 : 0 ≤ S2 := sq_nonneg _
  have hs2_small : s2 ≤ 1 / 100 := by
    have hpi4 := Real.pi_lt_d2
    have : π * ε / 2 ≤ 1 / 10 := by nlinarith
    rw [hs2]; nlinarith [mul_nonneg hpi.le h0]
  have hS1 : S2 < 1 := by linarith
  have hd : x - χ ≠ 0 := sub_ne_zero.mpr hne
  have hzm : π * (x - χ) / 2 ≠ 0 := by positivity
  have hshm : 0 < Real.sinh (π * (x - χ) / 2) ^ 2 := by
    have := sq_le_sinh_sq (π * (x - χ) / 2)
    have : 0 < (π * (x - χ) / 2) ^ 2 := by positivity
    linarith [sq_le_sinh_sq (π * (x - χ) / 2)]
  have hshp : 1 ≤ Real.sinh (π * (x + χ) / 2) ^ 2 := by
    have h1' : 1 ≤ Real.sinh (π * (x + χ) / 2) := by
      rw [← sinh_pi_mul_xiStar]
      exact Real.sinh_le_sinh.mpr (by nlinarith)
    nlinarith
  rw [blaschkePairQ_eq_pairFac, blaschkePairQ_eq_pairFac]
  have h0S : Real.sin (π * 0 / 2) ^ 2 = 0 := by simp
  rw [h0S]
  have hm := pairFac_le_mul hshm hS0 hS1
  have hp := pairFac_le_tanhSq_mul hshp hS0 (by linarith)
  have hF0m : pairFac (π * (x - χ) / 2) 0 = Real.sinh (π * (x - χ) / 2) ^ 2 /
      Real.cosh (π * (x - χ) / 2) ^ 2 := by unfold pairFac; simp
  have hF0p : pairFac (π * (x + χ) / 2) 0 = Real.sinh (π * (x + χ) / 2) ^ 2 /
      Real.cosh (π * (x + χ) / 2) ^ 2 := by unfold pairFac; simp
  rw [hF0m, hF0p]
  have hqm : 0 ≤ Real.sinh (π * (x - χ) / 2) ^ 2 / Real.cosh (π * (x - χ) / 2) ^ 2 := by positivity
  have hqp : 0 ≤ Real.sinh (π * (x + χ) / 2) ^ 2 / Real.cosh (π * (x + χ) / 2) ^ 2 := by positivity
  -- minus factor
  have hratiom : (1 + S2 / Real.sinh (π * (x - χ) / 2) ^ 2) / (1 - S2) ≤
      (1 + ε ^ 2 / (x - χ) ^ 2) / (1 - s2) := by
    have hq : S2 / Real.sinh (π * (x - χ) / 2) ^ 2 ≤ ε ^ 2 / (x - χ) ^ 2 := by
      have hz2 : 0 < (π * (x - χ) / 2) ^ 2 := by positivity
      calc S2 / Real.sinh (π * (x - χ) / 2) ^ 2 ≤ s2 / (π * (x - χ) / 2) ^ 2 := by
            apply div_le_div₀ hs2_0 hSu hz2 (sq_le_sinh_sq _)
        _ = ε ^ 2 / (x - χ) ^ 2 := by rw [hs2]; field_simp
    have hnum : 1 + S2 / Real.sinh (π * (x - χ) / 2) ^ 2 ≤ 1 + ε ^ 2 / (x - χ) ^ 2 := by linarith
    exact div_le_div₀ (by positivity) hnum (by linarith) (by linarith)
  -- plus factor
  have hratiop : (1 + S2) / (1 - S2) ≤ (1 + s2) / (1 - s2) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hm' : pairFac (π * (x - χ) / 2) S2 ≤ Real.sinh (π * (x - χ) / 2) ^ 2 /
      Real.cosh (π * (x - χ) / 2) ^ 2 * ((1 + ε ^ 2 / (x - χ) ^ 2) / (1 - s2)) :=
    hm.trans (mul_le_mul_of_nonneg_left hratiom hqm)
  have hp' : pairFac (π * (x + χ) / 2) S2 ≤ Real.sinh (π * (x + χ) / 2) ^ 2 /
      Real.cosh (π * (x + χ) / 2) ^ 2 * ((1 + s2) / (1 - s2)) :=
    hp.trans (mul_le_mul_of_nonneg_left hratiop hqp)
  have hposm : 0 ≤ pairFac (π * (x - χ) / 2) S2 := (pairFac_pos hS1 (by positivity)).le
  have hprod := mul_le_mul hm' hp' (pairFac_pos hS1 (by positivity)).le (by
    have : 0 ≤ (1 + ε ^ 2 / (x - χ) ^ 2) / (1 - s2) := by
      apply div_nonneg (by positivity) (by linarith)
    positivity)
  have hk : (1 + s2) / (1 - s2) ^ 2 ≤ 1 + 8 * ε ^ 2 := by
    apply one_add_div_le hs2_0 (by rw [hs2e]) (by positivity) (by nlinarith)
  have heq := mul_div_aux (Real.sinh (π * (x - χ) / 2) ^ 2 / Real.cosh (π * (x - χ) / 2) ^ 2)
    (Real.sinh (π * (x + χ) / 2) ^ 2 / Real.cosh (π * (x + χ) / 2) ^ 2) (ε ^ 2 / (x - χ) ^ 2) s2
    (by linarith : 1 - s2 ≠ 0)
  refine hprod.trans (heq.le.trans ?_)
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hqm hqp)
  exact mul_le_mul_of_nonneg_left hk (by positivity)

/-- The other hole pairs (`rem:thmU` Step (3), last bullet): the modified pair `q'_k ≥ T_{χ'_k}(x)²`
against the reference pair `q⁰_k ≤ T_{χ_k}(x)²(1 + ε⁰²/(x-χ_k)²)(1 + 8ε⁰²)`. -/
theorem pairQ_ratio_other_lower {χ χ' ε' ε₀ x : ℝ} (hχ : xiStar ≤ χ) (hχ' : 0 ≤ χ')
    (hx : xiStar ≤ x) (hne : x ≠ χ) (hne' : χ' ≠ x) (hε' : 0 ≤ ε' ∧ ε' ≤ 1 / 2)
    (hε₀ : 0 ≤ ε₀ ∧ ε₀ ≤ 1 / 16) :
    Real.exp (-2 * |realLogT x χ' - realLogT x χ|) /
        ((1 + ε₀ ^ 2 / (x - χ) ^ 2) * (1 + 8 * ε₀ ^ 2)) ≤
      blaschkePairQ χ' ε' x / blaschkePairQ χ ε₀ x := by
  have hx0 : 0 < x := xiStar_pos.trans_le hx
  have hχ0 : 0 ≤ χ := xiStar_pos.le.trans hχ
  obtain ⟨hQ'pos, hQ'⟩ := two_realLogT_le_log_blaschkePairQ hχ' hx0 hne' hε'.1 hε'.2
  obtain ⟨hQpos, -⟩ := two_realLogT_le_log_blaschkePairQ hχ0 hx0 hne.symm hε₀.1
    (by linarith [hε₀.2])
  have hQ'e : Real.exp (2 * realLogT x χ') ≤ blaschkePairQ χ' ε' x := by
    calc Real.exp (2 * realLogT x χ') ≤ Real.exp (Real.log (blaschkePairQ χ' ε' x)) :=
          Real.exp_le_exp.mpr hQ'
      _ = _ := Real.exp_log hQ'pos
  have hQ0 := exp_two_realLogT_eq hχ0 hx0 hne.symm
  have hup := blaschkePairQ_le_mul hχ hx hne hε₀.1 hε₀.2
  rw [← hQ0] at hup
  have hM : 0 < (1 + ε₀ ^ 2 / (x - χ) ^ 2) * (1 + 8 * ε₀ ^ 2) := by positivity
  have h1 : Real.exp (2 * realLogT x χ') /
      (Real.exp (2 * realLogT x χ) * ((1 + ε₀ ^ 2 / (x - χ) ^ 2) * (1 + 8 * ε₀ ^ 2))) ≤
      blaschkePairQ χ' ε' x / blaschkePairQ χ ε₀ x :=
    div_le_div₀ hQ'pos.le hQ'e hQpos hup
  refine le_trans ?_ h1
  have hexp : Real.exp (-2 * |realLogT x χ' - realLogT x χ|) ≤
      Real.exp (2 * realLogT x χ') / Real.exp (2 * realLogT x χ) := by
    rw [← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    have := neg_abs_le (realLogT x χ' - realLogT x χ)
    linarith
  calc Real.exp (-2 * |realLogT x χ' - realLogT x χ|) /
        ((1 + ε₀ ^ 2 / (x - χ) ^ 2) * (1 + 8 * ε₀ ^ 2)) ≤
      (Real.exp (2 * realLogT x χ') / Real.exp (2 * realLogT x χ)) /
        ((1 + ε₀ ^ 2 / (x - χ) ^ 2) * (1 + 8 * ε₀ ^ 2)) :=
        div_le_div_of_nonneg_right hexp hM.le
    _ = _ := by rw [div_div]

/-! ### 5. The pair at `k₀` -/

lemma tanhSq_eq_exp_combH {y : ℝ} (hy : 0 < y) :
    Real.sinh (π * y / 2) ^ 2 / Real.cosh (π * y / 2) ^ 2 = Real.exp (2 * combH y) := by
  have hpos : 0 < Real.tanh (π * y / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by positivity [Real.pi_pos])) (Real.cosh_pos _)
  unfold combH
  rw [show 2 * Real.log (Real.tanh (π * y / 2)) =
      Real.log (Real.tanh (π * y / 2)) + Real.log (Real.tanh (π * y / 2)) by ring, Real.exp_add,
    Real.exp_log hpos, Real.tanh_eq_sinh_div_cosh, ← sq, div_pow]

lemma ratio_alg (z' s' z s : ℝ) (hu : 0 < z ^ 2 + s ^ 2) (h2 : 0 < 1 - z ^ 2) (h3 : 0 < 1 - s ^ 2) :
    ((z' ^ 2 + s' ^ 2) / (z ^ 2 + s ^ 2)) *
        ((1 - (s' ^ 2 / 2 + z' ^ 2)) * (1 - z ^ 2) * (1 - s ^ 2)) =
      ((z' ^ 2 + s' ^ 2) * (1 - s' ^ 2 / 2 - z' ^ 2)) /
        ((z ^ 2 + s ^ 2) / ((1 - z ^ 2) * (1 - s ^ 2))) := by
  field_simp
  ring

lemma one_sub_mul_ge {a b P : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hb1 : b ≤ 1) (hP : 1 - a ≤ P) :
    1 - a - b ≤ P * (1 - b) := by
  have h1 : (1 - a) * (1 - b) ≤ P * (1 - b) := mul_le_mul_of_nonneg_right hP (by linarith)
  nlinarith [mul_nonneg ha hb]

/-- Basic size bounds used by both factors of a pair of small displacement and width. -/
lemma pair_small_bounds {a ε w : ℝ} (ha : |a| ≤ w) (hε : 0 ≤ ε ∧ ε ≤ w) :
    (π * a / 2) ^ 2 ≤ 5 / 2 * w ^ 2 ∧ (π * ε / 2) ^ 2 ≤ 5 / 2 * w ^ 2 := by
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_d2
  have hkk : (π / 2) ^ 2 ≤ 5 / 2 := by nlinarith
  have hd : a ^ 2 ≤ w ^ 2 := by
    have := sq_abs a; nlinarith [abs_nonneg a]
  have he : ε ^ 2 ≤ w ^ 2 := by nlinarith [hε.1, hε.2]
  constructor
  · calc (π * a / 2) ^ 2 = (π / 2) ^ 2 * a ^ 2 := by ring
      _ ≤ 5 / 2 * w ^ 2 := by nlinarith [sq_nonneg a]
  · calc (π * ε / 2) ^ 2 = (π / 2) ^ 2 * ε ^ 2 := by ring
      _ ≤ 5 / 2 * w ^ 2 := by nlinarith [sq_nonneg ε]

/-- Ratio of the minus factors. -/
lemma minusFactor_ratio_lower {χ χ' ε' ε₀ x w : ℝ} (hw0 : 0 < w) (hw : w ≤ 1 / 16)
    (ha' : |x - χ'| ≤ w) (ha : |x - χ| ≤ w) (hε' : 0 ≤ ε' ∧ ε' ≤ w) (hε₀ : 0 < ε₀ ∧ ε₀ ≤ w) :
    ∃ c1 c2 c3 : ℝ, 0 ≤ c1 ∧ 0 ≤ c2 ∧ 0 ≤ c3 ∧ c1 ≤ 15 / 4 * w ^ 2 ∧ c2 ≤ 5 / 2 * w ^ 2 ∧
      c3 ≤ 5 / 2 * w ^ 2 ∧
      ((x - χ') ^ 2 + ε' ^ 2) / ((x - χ) ^ 2 + ε₀ ^ 2) * ((1 - c1) * (1 - c2) * (1 - c3)) ≤
        pairFac (π * (x - χ') / 2) (Real.sin (π * ε' / 2) ^ 2) /
          pairFac (π * (x - χ) / 2) (Real.sin (π * ε₀ / 2) ^ 2) := by
  have hpi := Real.pi_pos
  have hε₀0 := hε₀.1
  have hw2 : w ^ 2 ≤ w / 16 := by nlinarith
  obtain ⟨hz'2, hs'2⟩ := pair_small_bounds ha' hε'
  obtain ⟨hz2, hs2⟩ := pair_small_bounds ha ⟨hε₀0.le, hε₀.2⟩
  have hz'q : (π * (x - χ') / 2) ^ 2 ≤ 1 / 4 := by linarith only [hz'2, hw2, hw]
  have hzq : (π * (x - χ) / 2) ^ 2 ≤ 1 / 4 := by linarith only [hz2, hw2, hw]
  have hFm' := pairFac_lower_minus hz'q hε'.1 (by linarith only [hε'.2, hw] : ε' ≤ 1 / 8)
  have hFmu := pairFac_upper_minus hzq hε₀0.le (by linarith only [hε₀.2, hw] : ε₀ ≤ 1 / 8)
  obtain ⟨hSl, hSu⟩ := sinSq_bounds hε₀0.le (by linarith only [hε₀.2, hw] : ε₀ ≤ 1 / 8)
  obtain ⟨hSl', hSu'⟩ := sinSq_bounds hε'.1 (by linarith only [hε'.2, hw] : ε' ≤ 1 / 8)
  have hs2pos : 0 < (π * ε₀ / 2) ^ 2 := by positivity
  have hS2pos : 0 < Real.sin (π * ε₀ / 2) ^ 2 := by
    have : (π * ε₀ / 2) ^ 2 * (1 - (π * ε₀ / 2) ^ 2 / 2) > 0 := by
      apply mul_pos hs2pos; linarith only [hs2, hw2, hw]
    linarith only [this, hSl]
  have hS1 : Real.sin (π * ε₀ / 2) ^ 2 < 1 := by linarith only [hSu, hs2, hw2, hw]
  have hS1' : Real.sin (π * ε' / 2) ^ 2 < 1 := by linarith only [hSu', hs'2, hw2, hw]
  have hFm_pos : 0 < pairFac (π * (x - χ) / 2) (Real.sin (π * ε₀ / 2) ^ 2) :=
    pairFac_pos hS1 (by positivity)
  have hFm'0 : 0 ≤ pairFac (π * (x - χ') / 2) (Real.sin (π * ε' / 2) ^ 2) := by
    unfold pairFac
    exact div_nonneg (by positivity) (cosh_sq_sub_pos hS1').le
  refine ⟨(π * ε' / 2) ^ 2 / 2 + (π * (x - χ') / 2) ^ 2, (π * (x - χ) / 2) ^ 2,
    (π * ε₀ / 2) ^ 2, by positivity, by positivity, by positivity, ?_, hz2, hs2, ?_⟩
  · linarith only [hs'2, hz'2]
  · have hu0 : 0 < (x - χ) ^ 2 + ε₀ ^ 2 := by positivity
    have hR0 : ((π * (x - χ') / 2) ^ 2 + (π * ε' / 2) ^ 2) /
        ((π * (x - χ) / 2) ^ 2 + (π * ε₀ / 2) ^ 2) =
        ((x - χ') ^ 2 + ε' ^ 2) / ((x - χ) ^ 2 + ε₀ ^ 2) := by
      have : (π / 2) ^ 2 ≠ 0 := by positivity
      field_simp
    have hdiv := div_le_div₀ hFm'0 hFm' hFm_pos hFmu
    rw [← hR0]
    have hc2' : 0 < 1 - (π * (x - χ) / 2) ^ 2 := by linarith only [hz2, hw2, hw]
    have hc3' : 0 < 1 - (π * ε₀ / 2) ^ 2 := by linarith only [hs2, hw2, hw]
    have hu : 0 < (π * (x - χ) / 2) ^ 2 + (π * ε₀ / 2) ^ 2 := by positivity
    exact le_trans (le_of_eq (ratio_alg _ _ _ _ hu hc2' hc3')) hdiv

lemma frac_aux1 {c S : ℝ} (hS0 : 0 ≤ S) (hSc : S ≤ c) :
    (1 - c) / (1 + c) ≤ (1 - S) / (1 + S) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma frac_aux2 {c : ℝ} (h0 : 0 ≤ c) : 1 - 2 * c ≤ (1 - c) / (1 + c) := by
  rw [le_div_iff₀ (by linarith)]
  nlinarith [sq_nonneg c]

/-- Ratio of the plus factors. -/
lemma plusFactor_ratio_lower {χ χ' ε' ε₀ x w : ℝ} (hχ : xiStar ≤ χ) (hχ' : xiStar ≤ χ')
    (hx : xiStar ≤ x) (hw0 : 0 < w) (hw : w ≤ 1 / 16) (ha' : |x - χ'| ≤ w) (ha : |x - χ| ≤ w)
    (hε' : 0 ≤ ε' ∧ ε' ≤ w) (hε₀ : 0 < ε₀ ∧ ε₀ ≤ w) :
    ∃ c4 c5 : ℝ, 0 ≤ c4 ∧ 0 ≤ c5 ∧ c4 ≤ 63 / 5 * w ∧ c5 ≤ 5 * w ^ 2 ∧
      (1 - c4) * (1 - c5) ≤
        pairFac (π * (x + χ') / 2) (Real.sin (π * ε' / 2) ^ 2) /
          pairFac (π * (x + χ) / 2) (Real.sin (π * ε₀ / 2) ^ 2) := by
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_lt_d2
  have hε₀0 := hε₀.1
  have hw2 : w ^ 2 ≤ w / 16 := by nlinarith
  obtain ⟨hz'2, hs'2⟩ := pair_small_bounds ha' hε'
  obtain ⟨hz2, hs2⟩ := pair_small_bounds ha ⟨hε₀0.le, hε₀.2⟩
  obtain ⟨hSl, hSu⟩ := sinSq_bounds hε₀0.le (by linarith only [hε₀.2, hw] : ε₀ ≤ 1 / 8)
  obtain ⟨hSl', hSu'⟩ := sinSq_bounds hε'.1 (by linarith only [hε'.2, hw] : ε' ≤ 1 / 8)
  have hs2pos : 0 < (π * ε₀ / 2) ^ 2 := by positivity
  have hS2pos : 0 < Real.sin (π * ε₀ / 2) ^ 2 := by
    have : (π * ε₀ / 2) ^ 2 * (1 - (π * ε₀ / 2) ^ 2 / 2) > 0 := by
      apply mul_pos hs2pos; linarith only [hs2, hw2, hw]
    linarith only [this, hSl]
  have hS1 : Real.sin (π * ε₀ / 2) ^ 2 < 1 := by linarith only [hSu, hs2, hw2, hw]
  have hS1' : Real.sin (π * ε' / 2) ^ 2 < 1 := by linarith only [hSu', hs'2, hw2, hw]
  have hshp : 1 ≤ Real.sinh (π * (x + χ) / 2) ^ 2 := by
    have h1' : 1 ≤ Real.sinh (π * (x + χ) / 2) := by
      rw [← sinh_pi_mul_xiStar]
      exact Real.sinh_le_sinh.mpr (by nlinarith)
    nlinarith
  have hS0 : 0 ≤ Real.sin (π * ε₀ / 2) ^ 2 := sq_nonneg _
  have hS0' : 0 ≤ Real.sin (π * ε' / 2) ^ 2 := sq_nonneg _
  have hFp' := pairFac_ge_tanhSq (z := π * (x + χ') / 2) hS0' hS1'
  have hFpu := pairFac_le_tanhSq_mul hshp hS0 (by linarith only [hSu, hs2, hw2, hw])
  have hFp_pos : 0 < pairFac (π * (x + χ) / 2) (Real.sin (π * ε₀ / 2) ^ 2) :=
    pairFac_pos hS1 (by positivity)
  have hxχ : 0 < x + χ := by linarith [xiStar_pos]
  have hxχ' : 0 < x + χ' := by linarith [xiStar_pos]
  have htp' := tanhSq_eq_exp_combH hxχ'
  have htp := tanhSq_eq_exp_combH hxχ
  have hcomb := abs_combH_sub_le (a := x + χ') (b := x + χ) (by linarith) (by linarith)
  have hΔ : |χ' - χ| ≤ 2 * w := by
    have : χ' - χ = (x - χ) - (x - χ') := by ring
    rw [this]
    calc |(x - χ) - (x - χ')| ≤ |x - χ| + |x - χ'| := abs_sub _ _
      _ ≤ 2 * w := by linarith
  have hπΔ : π * |χ' - χ| ≤ 3.15 * (2 * w) := mul_le_mul hpi4.le hΔ (abs_nonneg _) (by norm_num)
  refine ⟨2 * π * |χ' - χ|, 2 * (π * ε₀ / 2) ^ 2, by positivity, by positivity, ?_, ?_, ?_⟩
  · linarith only [hπΔ]
  · linarith only [hs2, hw2, hw]
  · obtain ⟨c4, hc4⟩ : ∃ c4 : ℝ, c4 = 2 * π * |χ' - χ| := ⟨_, rfl⟩
    obtain ⟨c3, hc3⟩ : ∃ c3 : ℝ, c3 = (π * ε₀ / 2) ^ 2 := ⟨_, rfl⟩
    rw [← hc4, ← hc3]
    have hc4_1 : c4 ≤ 63 / 5 * w := by
      rw [hc4]; linarith only [hπΔ]
    have hc3_1 : c3 ≤ 5 / 2 * w ^ 2 := by rw [hc3]; exact hs2
    have hc3_0 : 0 ≤ c3 := by rw [hc3]; positivity
    have hexp : 1 - c4 ≤ Real.exp (2 * combH (x + χ')) / Real.exp (2 * combH (x + χ)) := by
      rw [← Real.exp_sub]
      have h1 := Real.add_one_le_exp (2 * combH (x + χ') - 2 * combH (x + χ))
      have h2 := (abs_le.mp hcomb).1
      have h3 : |(x + χ') - (x + χ)| = |χ' - χ| := by congr 1; ring
      rw [h3] at h2
      rw [hc4]
      linarith
    have hS2s : Real.sin (π * ε₀ / 2) ^ 2 ≤ c3 := by rw [hc3]; exact hSu
    have hratio_S : (1 - c3) / (1 + c3) ≤
        (1 - Real.sin (π * ε₀ / 2) ^ 2) / (1 + Real.sin (π * ε₀ / 2) ^ 2) :=
      frac_aux1 hS0 hS2s
    have hc5' : 1 - 2 * c3 ≤ (1 - c3) / (1 + c3) := frac_aux2 hc3_0
    set Sa := Real.sin (π * ε₀ / 2) ^ 2 with hSa
    have hupp : pairFac (π * (x + χ) / 2) Sa ≤
        Real.exp (2 * combH (x + χ)) * ((1 + Sa) / (1 - Sa)) := by
      rw [← htp]; exact hFpu
    have hlow : Real.exp (2 * combH (x + χ')) ≤
        pairFac (π * (x + χ') / 2) (Real.sin (π * ε' / 2) ^ 2) := by rw [← htp']; exact hFp'
    have hE : 0 < Real.exp (2 * combH (x + χ)) := Real.exp_pos _
    have hdiv := div_le_div₀ (le_trans (Real.exp_pos _).le hlow) hlow hFp_pos hupp
    refine le_trans ?_ hdiv
    have hq : Real.exp (2 * combH (x + χ')) /
        (Real.exp (2 * combH (x + χ)) * ((1 + Sa) / (1 - Sa))) =
        (Real.exp (2 * combH (x + χ')) / Real.exp (2 * combH (x + χ))) * ((1 - Sa) / (1 + Sa)) := by
      have : 1 - Sa ≠ 0 := by linarith
      have : 1 + Sa ≠ 0 := by linarith
      field_simp
    rw [hq]
    have h1 : 1 - 2 * c3 ≤ (1 - Sa) / (1 + Sa) := hc5'.trans hratio_S
    have hc4' : 0 ≤ 1 - c4 := by linarith only [hc4_1, hw]
    exact mul_le_mul hexp h1 (by linarith only [hc3_1, hw2, hw]) (le_trans hc4' hexp)

/-- **The pair at `k₀`** (`rem:thmU` Step (3), "The pair at `k₀`"): for a modified pair `(χ', ε')` against the
reference pair `(χ, ε⁰)` at a point `x` with all displacements and widths `≤ w ≤ 1/16`,
`q'/q⁰ ≥ (1 - 16w) ((x-χ')² + ε'²)/((x-χ)² + ε⁰²)`. -/
theorem pairQ_ratio_lower {χ χ' ε' ε₀ x w : ℝ} (hχ : xiStar ≤ χ) (hχ' : xiStar ≤ χ')
    (hx : xiStar ≤ x) (hw0 : 0 < w) (hw : w ≤ 1 / 16) (ha' : |x - χ'| ≤ w) (ha : |x - χ| ≤ w)
    (hε' : 0 ≤ ε' ∧ ε' ≤ w) (hε₀ : 0 < ε₀ ∧ ε₀ ≤ w) :
    (1 - 16 * w) * (((x - χ') ^ 2 + ε' ^ 2) / ((x - χ) ^ 2 + ε₀ ^ 2)) ≤
      blaschkePairQ χ' ε' x / blaschkePairQ χ ε₀ x := by
  obtain ⟨c1, c2, c3, hc1_0, hc2_0, hc3_0, hc1_1, hc2_1, hc3_1, hmin⟩ :=
    minusFactor_ratio_lower (χ := χ) (χ' := χ') (ε' := ε') (ε₀ := ε₀) hw0 hw ha' ha hε' hε₀
  obtain ⟨c4, c5, hc4_0, hc5_0, hc4_1, hc5_1, hFp⟩ :=
    plusFactor_ratio_lower hχ hχ' hx hw0 hw ha' ha hε' hε₀
  have hw2 : w ^ 2 ≤ w / 16 := by nlinarith
  have hQ : blaschkePairQ χ' ε' x / blaschkePairQ χ ε₀ x =
      (pairFac (π * (x - χ') / 2) (Real.sin (π * ε' / 2) ^ 2) /
          pairFac (π * (x - χ) / 2) (Real.sin (π * ε₀ / 2) ^ 2)) *
        (pairFac (π * (x + χ') / 2) (Real.sin (π * ε' / 2) ^ 2) /
          pairFac (π * (x + χ) / 2) (Real.sin (π * ε₀ / 2) ^ 2)) := by
    rw [blaschkePairQ_eq_pairFac, blaschkePairQ_eq_pairFac, mul_div_mul_comm]
  rw [hQ]
  have hR0nn : 0 ≤ ((x - χ') ^ 2 + ε' ^ 2) / ((x - χ) ^ 2 + ε₀ ^ 2) := by
    have := hε₀.1; positivity
  have hP1 : 0 ≤ (1 - c1) * (1 - c2) * (1 - c3) := by
    apply mul_nonneg (mul_nonneg _ _) _ <;> linarith only [hc1_1, hc2_1, hc3_1, hw2, hw]
  have hP2 : 0 ≤ (1 - c4) * (1 - c5) := by
    apply mul_nonneg <;> linarith only [hc4_1, hc5_1, hw2, hw]
  have hcomb2 := mul_le_mul hmin hFp hP2 (le_trans (mul_nonneg hR0nn hP1) hmin)
  refine le_trans ?_ hcomb2
  have hq1 : 1 - c1 ≤ 1 - c1 := le_rfl
  have hq2 := one_sub_mul_ge hc1_0 hc2_0 (by linarith only [hc2_1, hw2, hw]) hq1
  have hq3 := one_sub_mul_ge (by linarith : 0 ≤ c1 + c2) hc3_0 (by linarith only [hc3_1, hw2, hw])
    (show 1 - (c1 + c2) ≤ (1 - c1) * (1 - c2) by linarith)
  have hq4 := one_sub_mul_ge (by linarith : 0 ≤ c1 + c2 + c3) hc4_0 (by linarith only [hc4_1, hw])
    (show 1 - (c1 + c2 + c3) ≤ (1 - c1) * (1 - c2) * (1 - c3) by linarith)
  have hq5 := one_sub_mul_ge (by linarith : 0 ≤ c1 + c2 + c3 + c4) hc5_0
    (by linarith only [hc5_1, hw2, hw])
    (show 1 - (c1 + c2 + c3 + c4) ≤ (1 - c1) * (1 - c2) * (1 - c3) * (1 - c4) by linarith)
  have hsum : c1 + c2 + c3 + c4 + c5 ≤ 16 * w := by
    linarith only [hc1_1, hc2_1, hc3_1, hc4_1, hc5_1, hw2, hw, hw0]
  have hprod : 1 - 16 * w ≤ (1 - c1) * (1 - c2) * (1 - c3) * ((1 - c4) * (1 - c5)) := by
    have : (1 - c1) * (1 - c2) * (1 - c3) * ((1 - c4) * (1 - c5)) =
        (1 - c1) * (1 - c2) * (1 - c3) * (1 - c4) * (1 - c5) := by ring
    rw [this]; linarith
  calc (1 - 16 * w) * (((x - χ') ^ 2 + ε' ^ 2) / ((x - χ) ^ 2 + ε₀ ^ 2)) =
      (((x - χ') ^ 2 + ε' ^ 2) / ((x - χ) ^ 2 + ε₀ ^ 2)) * (1 - 16 * w) := by ring
    _ ≤ (((x - χ') ^ 2 + ε' ^ 2) / ((x - χ) ^ 2 + ε₀ ^ 2)) *
        ((1 - c1) * (1 - c2) * (1 - c3) * ((1 - c4) * (1 - c5))) :=
        mul_le_mul_of_nonneg_left hprod hR0nn
    _ = ((x - χ') ^ 2 + ε' ^ 2) / ((x - χ) ^ 2 + ε₀ ^ 2) *
          ((1 - c1) * (1 - c2) * (1 - c3)) * ((1 - c4) * (1 - c5)) := by ring

/-! ### 6. The finite product of the seven other pairs -/

lemma inv_one_add_mul_ge {c θ : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1 / 4) (hθ : 1 ≤ θ) :
    (1 + c)⁻¹ * (1 - (θ - 1) / 4) ≤ (1 + θ * c)⁻¹ := by
  have h1 : 0 < 1 + c := by linarith
  have h2 : 0 < 1 + θ * c := by nlinarith
  rw [inv_mul_eq_div, ← one_div, div_le_div_iff₀ h1 h2]
  have h3 : 0 ≤ 1 / 4 + θ * c / 4 - c := by nlinarith
  nlinarith [mul_nonneg (by linarith : 0 ≤ θ - 1) h3]

/-- **The seven other hole pairs, finite product**: if the four "near" factors are at least
`(1-δ)(1 + θ/(16 (i+½)²))⁻¹` and the three "far" factors at least `(1-δ)(1 + θ/(16 (i+1)²))⁻¹`
(`θ ≥ 1`), then the product is at least `(1-δ)⁷ · (16647192576/23591176505) · (1 - (7/4)(θ-1))`. -/
theorem holeSeven_prod {θ δ : ℝ} (hθ : 1 ≤ θ) (hθ2 : θ ≤ 2) (_hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (gN gF : ℕ → ℝ)
    (hN : ∀ i : ℕ, i < 4 → (1 - δ) * (1 + θ / (16 * ((i : ℝ) + 1 / 2) ^ 2))⁻¹ ≤ gN i)
    (hF : ∀ i : ℕ, i < 3 → (1 - δ) * (1 + θ / (16 * ((i : ℝ) + 1) ^ 2))⁻¹ ≤ gF i) :
    (1 - δ) ^ 7 * holeProdConst * (1 - 7 / 4 * (θ - 1)) ≤
      (∏ i ∈ Finset.range 4, gN i) * ∏ i ∈ Finset.range 3, gF i := by
  set q : ℝ := 1 - (θ - 1) / 4 with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  have hδ' : 0 ≤ 1 - δ := by linarith
  have hlowN : ∀ i ∈ Finset.range 4, (1 - δ) * ((1 + 1 / (16 * ((i : ℝ) + 1 / 2) ^ 2))⁻¹ * q) ≤ gN i := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    refine le_trans ?_ (hN i hi')
    apply mul_le_mul_of_nonneg_left _ hδ'
    have hc0 : 0 ≤ 1 / (16 * ((i : ℝ) + 1 / 2) ^ 2) := by positivity
    have hc1 : 1 / (16 * ((i : ℝ) + 1 / 2) ^ 2) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Nat.cast_nonneg (α := ℝ) i]
    have := inv_one_add_mul_ge hc0 hc1 hθ
    rw [← hq] at this
    calc _ ≤ (1 + θ * (1 / (16 * ((i : ℝ) + 1 / 2) ^ 2)))⁻¹ := this
      _ = _ := by rw [mul_one_div]
  have hlowF : ∀ i ∈ Finset.range 3, (1 - δ) * ((1 + 1 / (16 * ((i : ℝ) + 1) ^ 2))⁻¹ * q) ≤ gF i := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    refine le_trans ?_ (hF i hi')
    apply mul_le_mul_of_nonneg_left _ hδ'
    have hc0 : 0 ≤ 1 / (16 * ((i : ℝ) + 1) ^ 2) := by positivity
    have hc1 : 1 / (16 * ((i : ℝ) + 1) ^ 2) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Nat.cast_nonneg (α := ℝ) i]
    have := inv_one_add_mul_ge hc0 hc1 hθ
    rw [← hq] at this
    calc _ ≤ (1 + θ * (1 / (16 * ((i : ℝ) + 1) ^ 2)))⁻¹ := this
      _ = _ := by rw [mul_one_div]
  have hnnN : ∀ i ∈ Finset.range 4,
      0 ≤ (1 - δ) * ((1 + 1 / (16 * ((i : ℝ) + 1 / 2) ^ 2))⁻¹ * q) := fun i _ =>
    mul_nonneg hδ' (mul_nonneg (by positivity) hq0.le)
  have hnnF : ∀ i ∈ Finset.range 3,
      0 ≤ (1 - δ) * ((1 + 1 / (16 * ((i : ℝ) + 1) ^ 2))⁻¹ * q) := fun i _ =>
    mul_nonneg hδ' (mul_nonneg (by positivity) hq0.le)
  have hpN := Finset.prod_le_prod₀ hnnN hlowN
  have hpF := Finset.prod_le_prod₀ hnnF hlowF
  have hexpN : ∏ i ∈ Finset.range 4, (1 - δ) * ((1 + 1 / (16 * ((i : ℝ) + 1 / 2) ^ 2))⁻¹ * q) =
      ((1 - δ) * q) ^ 4 * ∏ i ∈ Finset.range 4, (1 + 1 / (16 * ((i : ℝ) + 1 / 2) ^ 2))⁻¹ := by
    simp only [← mul_assoc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [mul_pow]; ring
  have hexpF : ∏ i ∈ Finset.range 3, (1 - δ) * ((1 + 1 / (16 * ((i : ℝ) + 1) ^ 2))⁻¹ * q) =
      ((1 - δ) * q) ^ 3 * ∏ i ∈ Finset.range 3, (1 + 1 / (16 * ((i : ℝ) + 1) ^ 2))⁻¹ := by
    simp only [← mul_assoc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [mul_pow]; ring
  have hmain : ((1 - δ) * q) ^ 7 * holeProdConst ≤
      (∏ i ∈ Finset.range 4, gN i) * ∏ i ∈ Finset.range 3, gF i := by
    rw [← holeProd_eq]
    calc ((1 - δ) * q) ^ 7 * ((∏ i ∈ Finset.range 4, (1 + 1 / (16 * ((i : ℝ) + 1 / 2) ^ 2))⁻¹) *
          ∏ i ∈ Finset.range 3, (1 + 1 / (16 * ((i : ℝ) + 1) ^ 2))⁻¹)
        = (((1 - δ) * q) ^ 4 * ∏ i ∈ Finset.range 4, (1 + 1 / (16 * ((i : ℝ) + 1 / 2) ^ 2))⁻¹) *
          (((1 - δ) * q) ^ 3 * ∏ i ∈ Finset.range 3, (1 + 1 / (16 * ((i : ℝ) + 1) ^ 2))⁻¹) := by ring
      _ ≤ _ := by
        rw [← hexpN, ← hexpF]
        exact mul_le_mul hpN hpF (Finset.prod_nonneg hnnF)
          (Finset.prod_nonneg fun i hi => le_trans (hnnN i hi) (hlowN i hi))
  have hbern : 1 - 7 / 4 * (θ - 1) ≤ q ^ 7 := by
    have := one_add_mul_le_pow (a := -((θ - 1) / 4)) (by linarith) 7
    rw [hq]
    nlinarith
  calc (1 - δ) ^ 7 * holeProdConst * (1 - 7 / 4 * (θ - 1)) ≤
      (1 - δ) ^ 7 * holeProdConst * q ^ 7 := by
        apply mul_le_mul_of_nonneg_left hbern
        have := holeProdConst_pos; positivity
    _ = ((1 - δ) * q) ^ 7 * holeProdConst := by rw [mul_pow]; ring
    _ ≤ _ := hmain

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.R_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.R_lower

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.holeProd_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.holeProd_eq

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.cFl_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.cFl_pos

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.cFl_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.cFl_gt

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.pairQ_ratio_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.pairQ_ratio_lower

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.pairQ_ratio_other_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.pairQ_ratio_other_lower

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.holeSeven_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.holeSeven_prod

end FormalResearch.ModularBootstrap.Upper.Holes
