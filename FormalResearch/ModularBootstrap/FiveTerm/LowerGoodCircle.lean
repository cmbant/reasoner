module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerMainDefs
public import FormalResearch.Special.AiryGoodCircles
public import FormalResearch.Special.AiryCftZeros

/-!
# Positive-measure good Airy circles in `[r₀, (3/2) r₀]` (`cts:rosc-uncond` (1))

Constructs a measurable subset `lowerGoodSet r₀ ⊆ [r₀, (3/2) r₀]` of radii `r` such that:
* `volume.real (lowerGoodSet r₀) ≥ r₀ / 16` for `r₀ ≥ 10` (`lowerGoodSet_measure`);
* for every `r ∈ lowerGoodSet r₀`, `R = r²` satisfies `LowerGoodCircle N R` (`lowerGood_circle_of_phase`),
  i.e. `‖Ai(u)‖² ≥ (1/(25π)) (1 + R)^{-1/2} e(u)` on `‖u‖ = R` and `n ≤ N ↔ |a_n| < R`.

The condition defining `lowerGoodSet r₀` is `∃ m : ℕ, |2 / 3 * r ^ 3 - (π / 4 + m * π)| ≤ 1 / 4`.
On each interval `[π/4 + mπ - 1/4, π/4 + mπ + 1/4]` inside `[2/3 r₀³, 2/3 ((3/2) r₀)³]`,
`r ↦ 2/3 r³` has derivative `2 r² ≤ 9 r₀² / 2`, so each interval has length `≥ 1 / (9 r₀²)`,
and there are at least `r₀³` disjoint such intervals for `r₀ ≥ 10`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special

/-! ### Cosine lower bound near good phases -/

/-- Extension of `airyNorm_cos_good` to a `1/4`-neighbourhood of `π/4 + mπ` (when `12 ≤ ‖ξ‖`). -/
lemma lowerGood_cos_good {ξ : ℂ} (hre : 0 ≤ ξ.re) (m : ℕ)
    (hm : |‖ξ‖ - (π / 4 + m * π)| ≤ 1 / 4) (h12 : 12 ≤ ‖ξ‖) :
    Real.exp |ξ.im| / 4 ≤ ‖Complex.cos (ξ - (π / 4 : ℂ))‖ := by
  set w : ℂ := ξ - (π / 4 : ℂ) with hw
  have hwr : w.re = ξ.re - π / 4 := by simp [hw]
  have hwi : w.im = ξ.im := by simp [hw]
  by_cases hy : 1 ≤ |ξ.im|
  · have := airyNorm_cos_ge_of_abs_im_ge (w := w) (by rw [hwi]; exact hy)
    rwa [hwi] at this
  replace hy := not_le.mp hy
  have hre' : (Complex.cos w).re = Real.cos w.re * Real.cosh w.im := airyRe_cos_eq w
  have hcosh := airyCosh_ge_half_exp_abs ξ.im
  set d : ℝ := ‖ξ‖ - ξ.re with hd
  have hd0 : 0 ≤ d := by
    have := Complex.re_le_norm ξ; linarith
  have hsq : d * (‖ξ‖ + ξ.re) = ξ.im ^ 2 := by
    have := sq_norm_eq ξ
    rw [hd]; nlinarith
  have hy2 : ξ.im ^ 2 < 1 := by
    have : |ξ.im| ^ 2 < 1 := by nlinarith [abs_nonneg ξ.im]
    rwa [sq_abs] at this
  have hd12 : d ≤ 1 / 12 := by
    have hsum : 12 ≤ ‖ξ‖ + ξ.re := by linarith
    nlinarith
  set δ : ℝ := (‖ξ‖ - (π / 4 + m * π)) - d with hδ
  have hδ_abs : |δ| ≤ 1 / 3 := by
    calc |δ| ≤ |‖ξ‖ - (π / 4 + m * π)| + |d| := abs_sub _ _
      _ ≤ 1 / 4 + 1 / 12 := by rw [abs_of_nonneg hd0]; linarith
      _ = 1 / 3 := by norm_num
  have hx : w.re = m * π + δ := by rw [hwr, hδ, hd]; ring
  have hcos : |Real.cos w.re| = Real.cos δ := by
    rw [hx, Real.cos_add, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi, zero_mul, sub_zero]
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have hδ2 := abs_le.mp hδ_abs
    exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hδ2.1, Real.pi_gt_three], by linarith [hδ2.2, Real.pi_gt_three]⟩)
  have hc12 : 1 / 2 ≤ Real.cos δ := by
    have := Real.one_sub_sq_div_two_le_cos (x := δ)
    have hδ2 : δ ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hδ_abs 2
    linarith
  have hre2 : ‖Complex.cos w‖ ≥ |(Complex.cos w).re| := Complex.abs_re_le_norm _
  rw [hre', abs_mul, hcos, abs_of_pos (Real.cosh_pos _), hwi] at hre2
  have hep := Real.exp_pos |ξ.im|
  nlinarith

/-- Lower bound near the negative axis when `|2/3 ‖q‖³ - (π/4 + mπ)| ≤ 1/4` and `3 ≤ ‖q‖`. -/
theorem lowerGood_airyAiC_neg_sq_ge {q : ℂ} (hq : NegSector q) (m : ℕ)
    (hm : |2 / 3 * ‖q‖ ^ 3 - (π / 4 + m * π)| ≤ 1 / 4) (h3 : 3 ≤ ‖q‖) :
    airyEnv (-(q ^ 2)) / (25 * π * ‖q‖) ≤ ‖airyAiC (-(q ^ 2))‖ ^ 2 := by
  have hq0 : 0 < ‖q‖ := by linarith
  set ξ : ℂ := (2 / 3 : ℂ) * q ^ 3 with hξ
  have hnξ : ‖ξ‖ = 2 / 3 * ‖q‖ ^ 3 := by
    rw [hξ, norm_mul, norm_pow]; norm_num
  have hq27 : (27 : ℝ) ≤ ‖q‖ ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) h3 3]
  have hξ12 : 12 ≤ ‖ξ‖ := by rw [hnξ]; linarith
  have hξre : 0 ≤ ξ.re := by
    have h1 := hq.re_sq_ge
    have h0 := hq.re_nonneg
    have : ξ.re = 2 / 3 * (q.re * (q.re ^ 2 - 3 * q.im ^ 2)) := by
      rw [hξ]; simp [Complex.mul_re, re_cube]; ring
    rw [this]
    have : 0 ≤ q.re * (q.re ^ 2 - 3 * q.im ^ 2) := mul_nonneg h0 (by linarith)
    positivity
  have hcos := lowerGood_cos_good hξre m (by rw [hnξ]; exact hm) hξ12
  set Y := |ξ.im| with hY
  have hmain := airyAiC_neg_complex hq hq0
  set M : ℂ := (1 / (π : ℂ)) * ((π : ℂ) / q) ^ (1 / 2 : ℂ) * Complex.cos (ξ - (π / 4 : ℂ)) with hM
  have hτ : ‖((π : ℂ) / q) ^ (1 / 2 : ℂ)‖ = √(π / ‖q‖) := by
    rw [norm_cpow_half, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hMn : ‖M‖ = √(π / ‖q‖) / π * ‖Complex.cos (ξ - (π / 4 : ℂ))‖ := by
    rw [hM, norm_mul, norm_mul, hτ, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    ring
  set A : ℝ := √(π / ‖q‖) / π with hA
  have hApos : 0 < A := by positivity
  have herr : 6 / 5 * Real.exp Y * A / ‖q‖ ^ 3 ≤ 1 / 20 * (A * Real.exp Y) := by
    rw [div_le_iff₀ (by positivity)]
    have := Real.exp_pos Y
    nlinarith [mul_pos hApos this]
  have hlow : 1 / 5 * (A * Real.exp Y) ≤ ‖airyAiC (-(q ^ 2))‖ := by
    have h1 : ‖M‖ - ‖airyAiC (-(q ^ 2)) - M‖ ≤ ‖airyAiC (-(q ^ 2))‖ := by
      have := norm_sub_norm_le M (M - airyAiC (-(q ^ 2)))
      rw [norm_sub_rev M (airyAiC (-(q ^ 2)))] at this
      simpa using this
    have h2 : A * (Real.exp Y / 4) ≤ ‖M‖ := by
      rw [hMn]; exact mul_le_mul_of_nonneg_left hcos hApos.le
    have : ‖airyAiC (-(q ^ 2)) - M‖ ≤ 1 / 20 * (A * Real.exp Y) := hmain.trans herr
    nlinarith
  rw [airyEnv_neg_sq hq]
  have hEY : Real.exp (2 * Y) = Real.exp Y ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have hsq : (1 / 5 * (A * Real.exp Y)) ^ 2 ≤ ‖airyAiC (-(q ^ 2))‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlow 2
  refine le_trans (le_of_eq ?_) hsq
  have hAsq : A ^ 2 = 1 / (π * ‖q‖) := by
    rw [hA, div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  rw [hEY, mul_pow, mul_pow, hAsq]
  field_simp
  ring

/-- If `10 ≤ r` and `|2/3 r³ - (π/4 + mπ)| ≤ 1/4`, then `R = r²` satisfies `LowerGoodCircle N R`
for some `N : ℕ`. -/
theorem lowerGood_circle_of_phase {r : ℝ} (hr10 : 10 ≤ r) (m : ℕ)
    (hm : |2 / 3 * r ^ 3 - (π / 4 + m * π)| ≤ 1 / 4) :
    ∃ N : ℕ, LowerGoodCircle N (r ^ 2) := by
  have hrpos : 0 < r := by linarith
  have hRpos : 0 < r ^ 2 := by positivity
  have hs3 : 3 ≤ r := by linarith
  have hR10 : 10 ≤ r ^ 2 := by nlinarith
  have hpi := Real.pi_pos
  have hlow : ∀ u : ℂ, ‖u‖ = r ^ 2 →
      1 / (25 * π) * (1 + r ^ 2) ^ (-(1 / 2 : ℝ)) * airyEnv u ≤ ‖airyAiC u‖ ^ 2 := by
    intro u hu
    have hw : (1 + r ^ 2) ^ (-(1 / 2 : ℝ)) ≤ 1 / r := by
      have := airyOnePlus_rpow_le hRpos
      rwa [Real.sqrt_sq hrpos.le] at this
    have henv := airyEnv_pos u
    by_cases hcase : -(‖u‖ / 2) ≤ u.re
    · have hz : 0 < ‖u‖ := by rw [hu]; exact hRpos
      have hR32 : (r ^ 2) ^ (3 / 2 : ℝ) = r ^ 3 := by
        rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hrpos.le]
        norm_num
      have hη : 5 / 48 / ((1 / 2 : ℝ) ^ 3 * √(1 / 2 : ℝ) * ‖u‖ ^ (3 / 2 : ℝ)) ≤ 1 / 2 := by
        rw [hu, hR32]
        have h7 : (7 / 10 : ℝ) ≤ √(1 / 2 : ℝ) := Real.le_sqrt_of_sq_le (by norm_num)
        have hden : (7 / 80 : ℝ) * r ^ 3 ≤ (1 / 2 : ℝ) ^ 3 * √(1 / 2 : ℝ) * r ^ 3 := by
          have := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h7 (by norm_num : (0 : ℝ) ≤ (1 / 2) ^ 3))
            (by positivity : 0 ≤ r ^ 3)
          nlinarith
        rw [div_le_iff₀ (by positivity)]
        have hr3 : (1000 : ℝ) ≤ r ^ 3 := by nlinarith
        nlinarith
      have hsec := airyAiC_sq_ge_sector (z := u) (s := 1 / 2) (by norm_num) hz (by nlinarith) hη
      rw [hu, Real.sqrt_sq hrpos.le] at hsec
      refine le_trans ?_ hsec
      have h1 : 1 / (25 * π) * (1 + r ^ 2) ^ (-(1 / 2 : ℝ)) ≤ 1 / (16 * π * r) := by
        calc 1 / (25 * π) * (1 + r ^ 2) ^ (-(1 / 2 : ℝ))
            ≤ 1 / (25 * π) * (1 / r) := by gcongr
          _ ≤ 1 / (16 * π * r) := by
            rw [one_div_mul_one_div, one_div_le_one_div (by positivity) (by positivity)]
            nlinarith
      calc 1 / (25 * π) * (1 + r ^ 2) ^ (-(1 / 2 : ℝ)) * airyEnv u
          ≤ 1 / (16 * π * r) * airyEnv u := by gcongr
        _ = airyEnv u / (16 * π * r) := by ring
    · have hlt : u.re < -(‖u‖ / 2) := not_le.mp hcase
      set q : ℂ := (-u) ^ (1 / 2 : ℂ) with hqdef
      have hq : NegSector q := NegSector_of_re_lt hlt
      have hq2 : q ^ 2 = -u := cpow_half_sq _
      have hqn : ‖q‖ ^ 2 = r ^ 2 := by rw [hqdef, norm_cpow_half_sq, norm_neg, hu]
      have hqs : ‖q‖ = r := by
        have := congrArg Real.sqrt hqn
        rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hrpos.le] at this
      have hneg := lowerGood_airyAiC_neg_sq_ge hq m (by rw [hqs]; exact hm) (by rw [hqs]; exact hs3)
      have e : -(q ^ 2) = u := by rw [hq2, neg_neg]
      rw [e, hqs] at hneg
      refine le_trans ?_ hneg
      calc 1 / (25 * π) * (1 + r ^ 2) ^ (-(1 / 2 : ℝ)) * airyEnv u
          ≤ 1 / (25 * π) * (1 / r) * airyEnv u := by gcongr
        _ = airyEnv u / (25 * π * r) := by field_simp
  have hgood_ai : ∀ u : ℂ, ‖u‖ = r ^ 2 → airyAiC u ≠ 0 := by
    intro u hu h0
    have h1 := hlow u hu
    rw [h0, norm_zero] at h1
    have h2 : 0 < 1 / (25 * π) * (1 + r ^ 2) ^ (-(1 / 2 : ℝ)) * airyEnv u := by
      have := airyEnv_pos u
      have := Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 1 + r ^ 2) (-(1 / 2 : ℝ))
      positivity
    linarith
  obtain ⟨N, hN, _⟩ := airy_circleData hRpos hgood_ai
  refine ⟨N, hlow, fun n hn => ?_⟩
  rw [hN n hn, abs_of_neg (airyZero_neg n)]

/-! ### Measure of the good-radius set in `[r₀, (3/2) r₀]` -/

/-- The set of good radii `r ∈ [r₀, (3/2) r₀]` satisfying `|2/3 r³ - (π/4 + mπ)| ≤ 1/4` for some `m : ℕ`. -/
def lowerGoodSet (r₀ : ℝ) : Set ℝ :=
  {r ∈ Icc r₀ (3 / 2 * r₀) | ∃ m : ℕ, |2 / 3 * r ^ 3 - (π / 4 + m * π)| ≤ 1 / 4}

lemma lowerGoodSet_measurable (r₀ : ℝ) : MeasurableSet (lowerGoodSet r₀) := by
  have h1 : MeasurableSet (Icc r₀ (3 / 2 * r₀)) := measurableSet_Icc
  have h2 : MeasurableSet (⋃ m : ℕ, {r : ℝ | |2 / 3 * r ^ 3 - (π / 4 + m * π)| ≤ 1 / 4}) :=
    MeasurableSet.iUnion fun m =>
      isClosed_le (Continuous.abs (by fun_prop)) continuous_const |>.measurableSet
  have heq : lowerGoodSet r₀ =
      Icc r₀ (3 / 2 * r₀) ∩ ⋃ m : ℕ, {r : ℝ | |2 / 3 * r ^ 3 - (π / 4 + m * π)| ≤ 1 / 4} := by
    ext r; simp [lowerGoodSet]
  rw [heq]
  exact h1.inter h2

lemma lowerGoodSet_finite_measure (r₀ : ℝ) : volume (lowerGoodSet r₀) ≠ ⊤ := by
  have hsub : lowerGoodSet r₀ ⊆ Icc r₀ (3 / 2 * r₀) := fun _ hr => hr.1
  exact ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    (measure_mono hsub)

/-- For `r₀ ≥ 10`, `lowerGoodSet r₀` has Lebesgue measure at least `r₀ / 36`. -/
theorem lowerGoodSet_measure {r₀ : ℝ} (hr₀ : 10 ≤ r₀) :
    r₀ / 36 ≤ volume.real (lowerGoodSet r₀) := by
  have hr₀_pos : 0 < r₀ := by linarith
  have hpi := Real.pi_pos
  have hpi_lt : π < 3.15 := Real.pi_lt_d2
  let M₀ : ℕ := ⌈(2 / 3 * r₀ ^ 3 - π / 4 + 1 / 4) / π⌉₊
  let K : ℕ := ⌊r₀ ^ 3 / 3⌋₊
  have hK_ge : r₀ ^ 3 / 3 - 1 < (K : ℝ) := by
    have := Nat.lt_floor_add_one (r₀ ^ 3 / 3)
    linarith
  have hK_le : (K : ℝ) ≤ r₀ ^ 3 / 3 := Nat.floor_le (by positivity)
  have hr₀3 : (1000 : ℝ) ≤ r₀ ^ 3 := by
    have : (10 : ℝ) ^ 3 ≤ r₀ ^ 3 := pow_le_pow_left₀ (by norm_num) hr₀ 3
    linarith
  have hK_pos : 0 < K := by
    have : (1 : ℝ) < (K : ℝ) := by linarith
    exact_mod_cast (by linarith : (0 : ℝ) < K)
  let Φ : ℝ → ℝ := fun r => 2 / 3 * r ^ 3
  have hΦ_mono : StrictMonoOn Φ (Ici 0) := by
    intro a ha b hb hab
    dsimp [Φ]
    have ha0 : 0 ≤ a := ha
    exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hab ha0 three_ne_zero) (by norm_num)
  have hM₀_lb : 2 / 3 * r₀ ^ 3 ≤ π / 4 + (M₀ : ℝ) * π - 1 / 4 := by
    have h1 := Nat.le_ceil ((2 / 3 * r₀ ^ 3 - π / 4 + 1 / 4) / π)
    have h2 : (2 / 3 * r₀ ^ 3 - π / 4 + 1 / 4) ≤ (M₀ : ℝ) * π := by
      rwa [div_le_iff₀ hpi] at h1
    linarith
  have hM₀_ub : (M₀ : ℝ) * π < 2 / 3 * r₀ ^ 3 - π / 4 + 1 / 4 + π := by
    have harg : 0 ≤ (2 / 3 * r₀ ^ 3 - π / 4 + 1 / 4) / π := by
      apply div_nonneg _ hpi.le
      nlinarith [Real.pi_lt_d2]
    have h1 := Nat.ceil_lt_add_one harg
    have h2 := mul_lt_mul_of_pos_right h1 hpi
    rw [add_mul, div_mul_cancel₀ _ hpi.ne', one_mul] at h2
    exact h2
  -- For `j ∈ range K`, let `m = M₀ + j`, and `I_j = [a_j, b_j]` where `Φ(a_j) = π/4 + mπ - 1/4`, `Φ(b_j) = π/4 + mπ + 1/4`.
  let a : ℕ → ℝ := fun j => (3 / 2 * (π / 4 + ((M₀ + j : ℕ) : ℝ) * π - 1 / 4)) ^ (1 / 3 : ℝ)
  let b : ℕ → ℝ := fun j => (3 / 2 * (π / 4 + ((M₀ + j : ℕ) : ℝ) * π + 1 / 4)) ^ (1 / 3 : ℝ)
  have hΦ_a : ∀ j, 0 ≤ a j ∧ Φ (a j) = π / 4 + ((M₀ + j : ℕ) : ℝ) * π - 1 / 4 := fun j => by
    have harg : 0 ≤ 3 / 2 * (π / 4 + ((M₀ + j : ℕ) : ℝ) * π - 1 / 4) := by
      have hle : (M₀ : ℝ) ≤ (M₀ + j : ℕ) := by exact_mod_cast Nat.le_add_right M₀ j
      have : 0 ≤ (M₀ : ℝ) * π := mul_nonneg (Nat.cast_nonneg _) hpi.le
      nlinarith [Real.pi_gt_three]
    refine ⟨Real.rpow_nonneg harg _, ?_⟩
    dsimp [Φ, a]
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul harg]
    norm_num; ring
  have hΦ_b : ∀ j, 0 ≤ b j ∧ Φ (b j) = π / 4 + ((M₀ + j : ℕ) : ℝ) * π + 1 / 4 := fun j => by
    have harg : 0 ≤ 3 / 2 * (π / 4 + ((M₀ + j : ℕ) : ℝ) * π + 1 / 4) := by positivity
    refine ⟨Real.rpow_nonneg harg _, ?_⟩
    dsimp [Φ, b]
    rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul harg]
    norm_num; ring
  have h_in_Icc : ∀ j ∈ Finset.range K, Icc (a j) (b j) ⊆ lowerGoodSet r₀ := by
    intro j hj r hr
    rw [Finset.mem_range] at hj
    have hj_lt : (j : ℝ) < r₀ ^ 3 / 3 := (by exact_mod_cast hj : (j : ℝ) < K).trans_le hK_le
    have hle_M : (M₀ : ℝ) ≤ (M₀ + j : ℕ) := by exact_mod_cast Nat.le_add_right M₀ j
    have hΦ_r0 : Φ r₀ ≤ Φ (a j) := by
      rw [(hΦ_a j).2]
      have : (M₀ : ℝ) * π ≤ ((M₀ + j : ℕ) : ℝ) * π := mul_le_mul_of_nonneg_right hle_M hpi.le
      dsimp [Φ]; linarith
    have hΦ_r1 : Φ (b j) ≤ Φ (3 / 2 * r₀) := by
      rw [(hΦ_b j).2]
      have hm_eq : ((M₀ + j : ℕ) : ℝ) = (M₀ : ℝ) + j := by push_cast; ring
      rw [hm_eq, add_mul]
      have h1 : (j : ℝ) * π ≤ (r₀ ^ 3 / 3) * 3.15 := by nlinarith
      dsimp [Φ]
      nlinarith
    have hr0_le_a : r₀ ≤ a j :=
      (hΦ_mono.le_iff_le hr₀_pos.le (hΦ_a j).1).mp hΦ_r0
    have hb_le_r1 : b j ≤ 3 / 2 * r₀ :=
      (hΦ_mono.le_iff_le (hΦ_b j).1 (by linarith : (0 : ℝ) ≤ 3 / 2 * r₀)).mp hΦ_r1
    refine ⟨⟨hr0_le_a.trans hr.1, hr.2.trans hb_le_r1⟩, M₀ + j, ?_⟩
    have hr0_nn : 0 ≤ r := by linarith [hr0_le_a.trans hr.1]
    have h1 : Φ (a j) ≤ Φ r := hΦ_mono.monotoneOn (hΦ_a j).1 hr0_nn hr.1
    have h2 : Φ r ≤ Φ (b j) := hΦ_mono.monotoneOn hr0_nn (hΦ_b j).1 hr.2
    rw [(hΦ_a j).2] at h1
    rw [(hΦ_b j).2] at h2
    dsimp [Φ] at h1 h2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h_disj : Set.PairwiseDisjoint (Finset.range K : Set ℕ) (fun j => Icc (a j) (b j)) := by
    intro i _ j _ hij
    rw [Function.onFun, Set.disjoint_iff]
    intro r ⟨hri, hrj⟩
    have hr_nn : 0 ≤ r := (hΦ_a i).1.trans hri.1
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have hbi : Φ r ≤ Φ (b i) := hΦ_mono.monotoneOn hr_nn (hΦ_b i).1 hri.2
      have haj : Φ (a j) ≤ Φ r := hΦ_mono.monotoneOn (hΦ_a j).1 hr_nn hrj.1
      rw [(hΦ_b i).2] at hbi
      rw [(hΦ_a j).2] at haj
      have hij1 : ((M₀ + i : ℕ) : ℝ) + 1 ≤ ((M₀ + j : ℕ) : ℝ) := by
        exact_mod_cast (by omega : M₀ + i + 1 ≤ M₀ + j)
      nlinarith [Real.pi_gt_three]
    · have hbj : Φ r ≤ Φ (b j) := hΦ_mono.monotoneOn hr_nn (hΦ_b j).1 hrj.2
      have hai : Φ (a i) ≤ Φ r := hΦ_mono.monotoneOn (hΦ_a i).1 hr_nn hri.1
      rw [(hΦ_b j).2] at hbj
      rw [(hΦ_a i).2] at hai
      have hji1 : ((M₀ + j : ℕ) : ℝ) + 1 ≤ ((M₀ + i : ℕ) : ℝ) := by
        exact_mod_cast (by omega : M₀ + j + 1 ≤ M₀ + i)
      nlinarith [Real.pi_gt_three]
  have h_len : ∀ j ∈ Finset.range K, 1 / (9 * r₀ ^ 2) ≤ b j - a j := by
    intro j hj
    have hsub := h_in_Icc j hj
    have hj_lt : (j : ℝ) < r₀ ^ 3 / 3 := by
      rw [Finset.mem_range] at hj
      exact (by exact_mod_cast hj : (j : ℝ) < K).trans_le hK_le
    have hle_M : (M₀ : ℝ) ≤ (M₀ + j : ℕ) := by exact_mod_cast Nat.le_add_right M₀ j
    have ha_le_b : a j ≤ b j := by
      refine (hΦ_mono.le_iff_le (hΦ_a j).1 (hΦ_b j).1).mp ?_
      rw [(hΦ_a j).2, (hΦ_b j).2]; linarith
    have hb_le : b j ≤ 3 / 2 * r₀ := (hsub ⟨ha_le_b, le_rfl⟩).1.2
    have ha_nn : 0 ≤ a j := (hΦ_a j).1
    have hdiff : Φ (b j) - Φ (a j) = 1 / 2 := by
      rw [(hΦ_b j).2, (hΦ_a j).2]; ring
    have hfac : Φ (b j) - Φ (a j) = 2 / 3 * (b j - a j) * (b j ^ 2 + b j * a j + a j ^ 2) := by
      dsimp [Φ]; ring
    have hquad : b j ^ 2 + b j * a j + a j ^ 2 ≤ 27 / 4 * r₀ ^ 2 := by
      nlinarith
    have hdiff_le : 1 / 2 ≤ 9 / 2 * r₀ ^ 2 * (b j - a j) := by
      have hba : 0 ≤ b j - a j := sub_nonneg.mpr ha_le_b
      calc 1 / 2 = 2 / 3 * (b j - a j) * (b j ^ 2 + b j * a j + a j ^ 2) := by rw [← hfac, hdiff]
        _ ≤ 2 / 3 * (b j - a j) * (27 / 4 * r₀ ^ 2) := by gcongr
        _ = 9 / 2 * r₀ ^ 2 * (b j - a j) := by ring
    rw [div_le_iff₀ (by positivity)]
    linarith
  -- Sum the measures of the disjoint intervals `Icc (a j) (b j)` inside `lowerGoodSet r₀`
  have hUnion_sub : (⋃ j ∈ Finset.range K, Icc (a j) (b j)) ⊆ lowerGoodSet r₀ :=
    Set.iUnion₂_subset h_in_Icc
  have hmeas_sum : (∑ j ∈ Finset.range K, volume (Icc (a j) (b j))) ≤ volume (lowerGoodSet r₀) := by
    rw [← MeasureTheory.measure_biUnion_finset h_disj (fun _ _ => measurableSet_Icc)]
    exact measure_mono hUnion_sub
  have hreal_sum : (∑ j ∈ Finset.range K, (b j - a j)) ≤ volume.real (lowerGoodSet r₀) := by
    have h_toReal : ∀ j ∈ Finset.range K, (volume (Icc (a j) (b j))).toReal = b j - a j := fun j hj => by
      rw [Real.volume_Icc, ENNReal.toReal_ofReal]
      have ha_le_b : a j ≤ b j := (hΦ_mono.le_iff_le (hΦ_a j).1 (hΦ_b j).1).mp (by
        rw [(hΦ_a j).2, (hΦ_b j).2]; linarith)
      linarith
    have hfin : ∑ j ∈ Finset.range K, volume (Icc (a j) (b j)) ≠ ⊤ := by
      rw [ENNReal.sum_ne_top]
      intro j _
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    have hle := ENNReal.toReal_mono (lowerGoodSet_finite_measure r₀) hmeas_sum
    rw [ENNReal.toReal_sum (fun j _ => by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)] at hle
    calc ∑ j ∈ Finset.range K, (b j - a j)
        = ∑ j ∈ Finset.range K, (volume (Icc (a j) (b j))).toReal :=
          Finset.sum_congr rfl fun j hj => (h_toReal j hj).symm
      _ ≤ volume.real (lowerGoodSet r₀) := hle
  have hsum_lb : (K : ℝ) * (1 / (9 * r₀ ^ 2)) ≤ ∑ j ∈ Finset.range K, (b j - a j) := by
    calc (K : ℝ) * (1 / (9 * r₀ ^ 2))
        = ∑ _ ∈ Finset.range K, (1 / (9 * r₀ ^ 2)) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.range K, (b j - a j) := Finset.sum_le_sum h_len
  have hK_bd : r₀ / 36 ≤ (K : ℝ) * (1 / (9 * r₀ ^ 2)) := by
    have : 9 / 36 * r₀ ^ 3 ≤ (K : ℝ) := by linarith
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    nlinarith
  exact hK_bd.trans (hsum_lb.trans hreal_sum)

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.lowerGood_circle_of_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.lowerGood_circle_of_phase

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.lowerGoodSet_measure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.lowerGoodSet_measure
