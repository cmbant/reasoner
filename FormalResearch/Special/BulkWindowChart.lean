module

public import FormalResearch.Special.BulkIndexSteps
public import FormalResearch.Special.BulkWindowAiry
public import FormalResearch.Special.BulkWindowZeros
public import FormalResearch.Special.DiscreteLgHahnMatch
public import FormalResearch.Special.RacahKappaCompose

/-!
# Bulk window, part 4: chart arithmetic for the Airy window of the `3j` chain

Elementary lemmas between the Airy-window data (`RkWinAtG`) and the abstract node count `BwnWin` (`BulkWindowCount`):

* `bwn_phase_bounds`: `0 ≤ Φ(q) ≤ (π/2)(q_* - q)`, `Φ = bkPhase 1 0 1 x q_*`.
* `bwn_chart_X`: with `Z = -ζ > 0` and `(2/3) Z^{3/2} = Φ`, the lattice variable `X = h^{-2/3} ζ` satisfies `-X > 0`,
  `(2/3)(-X)^{3/2} = Φ/h`: **the Airy phase of the window is exactly the Bohr-Sommerfeld phase** `Φ(q)/h`.
* `bwn_sign_all`: `(-1)^{#zeros of Ai in (x,0]} Ai(x) > 0` at every real `x` with `Ai x ≠ 0`.
* `bwn_exp_small`: `C e^{-ξ₀/δ³} ≤ δ^n` for small `δ` (the exponentially small `μ`).
* `bwn_Ai_lower`: `|Ai(-v)| ≥ δ/25` at a non-resonant `v ≥ 4`, `v δ² ≤ 1` (from the DLMF 9.7.9 bound `airyAi_neg_asymptotic`).
* `bwn_vbounds`: `c₂ δ √v ≤ 1/4` and `v δ² ≤ 1` from `(2/3) v^{3/2} ≤ (π/2) ρ/δ³`, `200 c₂³ ρ ≤ 1`, `ρ ≤ 1/4`.

**Claim class: proved.**  **Not formalised:** nothing beyond the statements (all constants are non-optimal).
-/

@[expose] public section

open Finset Set FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special


/-- `0 ≤ Φ(q) ≤ (π/2)(q_* - q)` for `0 ≤ q ≤ q_*`. -/
lemma bwn_phase_bounds {x q : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hq : 0 ≤ q) (hqs : q ≤ √(1 - x ^ 2)) :
    0 ≤ bkPhase 1 0 1 x (√(1 - x ^ 2)) q ∧ bkPhase 1 0 1 x (√(1 - x ^ 2)) q ≤ π / 2 * (√(1 - x ^ 2) - q) := by
  have hcont := bix_f_contOn hx0 hx1
  have hI : IntervalIntegrable (fun t => Real.arccos (hrU 1 0 1 x t)) MeasureTheory.volume q (√(1 - x ^ 2)) := by
    apply ContinuousOn.intervalIntegrable
    apply hcont.mono
    intro t ht
    rw [Set.mem_uIcc] at ht
    rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  have h1 : 0 < 1 - x ^ 2 := by nlinarith
  have hqs0 : 0 ≤ √(1 - x ^ 2) := Real.sqrt_nonneg _
  have hb : ∀ t ∈ Set.Icc q (√(1 - x ^ 2)), 0 ≤ Real.arccos (hrU 1 0 1 x t) ∧ Real.arccos (hrU 1 0 1 x t) ≤ π / 2 := by
    intro t ht
    refine ⟨Real.arccos_nonneg _, ?_⟩
    rw [bix_hrU]
    apply Real.arccos_le_pi_div_two.2
    have hq2 : √(1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt h1.le
    have : t ^ 2 ≤ 1 - x ^ 2 := by rw [← hq2]; exact pow_le_pow_left₀ (hq.trans ht.1) ht.2 2
    have : 0 ≤ √(1 - t ^ 2) := Real.sqrt_nonneg _
    positivity
  unfold bkPhase
  constructor
  · exact intervalIntegral.integral_nonneg hqs (fun t ht => (hb t ht).1)
  · have := intervalIntegral.integral_mono_on hqs hI (intervalIntegrable_const (c := π / 2)) (fun t ht => (hb t ht).2)
    simp at this; linarith


/-- The Langer lattice variable at a lattice site of the chart: `X = h^{-2/3} ζ < 0` and `(2/3)(-X)^{3/2} = Φ/h`. -/
lemma bwn_chart_X {Z h Φ : ℝ} (hZ : 0 < Z) (hh : 0 < h) (hΦ : 2 / 3 * Z ^ (3 / 2 : ℝ) = Φ) :
    0 < h ^ (-(2 / 3) : ℝ) * Z ∧ 2 / 3 * (h ^ (-(2 / 3) : ℝ) * Z) ^ (3 / 2 : ℝ) = Φ / h := by
  have hhp : 0 < h ^ (-(2 / 3) : ℝ) := Real.rpow_pos_of_pos hh _
  refine ⟨by positivity, ?_⟩
  have e2 : (h ^ (-(2 / 3) : ℝ) * Z) ^ (3 / 2 : ℝ) = h⁻¹ * Z ^ (3 / 2 : ℝ) := by
    rw [Real.mul_rpow hhp.le hZ.le, ← Real.rpow_mul hh.le, ← Real.rpow_neg_one]; norm_num
  rw [e2, ← hΦ]; field_simp

/-- The sign formula for `Ai` at every real point. -/
theorem bwn_sign_all (x : ℝ) (hne : airyAi x ≠ 0) : 0 < (-1 : ℝ) ^ (airyZeroCount x) * airyAi x := by
  rcases le_or_gt x 0 with hx | hx
  · exact bwn_sign hx hne
  · rw [bwn_count_zero (by linarith)]
    simpa using airyAi_pos hx.le

/-- Superpolynomial smallness: `C e^{-ξ₀/δ³} ≤ δ^n` for small `δ`. -/
lemma bwn_exp_small {C ξ0 : ℝ} (hC : 0 < C) (hξ : 0 < ξ0) (n : ℕ) (hn : 1 ≤ n) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → C * Real.exp (-ξ0 / δ ^ 3) ≤ δ ^ n := by
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  refine ⟨min 1 (ξ0 ^ n / (C * n.factorial)), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  intro δ hδ hδ0
  have hδ1 : δ ≤ 1 := hδ0.trans (min_le_left _ _)
  have hδ2 : δ ≤ ξ0 ^ n / (C * n.factorial) := hδ0.trans (min_le_right _ _)
  have hy : 0 ≤ ξ0 / δ ^ 3 := by positivity
  have h1 := Real.pow_div_factorial_le_exp (ξ0 / δ ^ 3) hy n
  have hexp : Real.exp (-ξ0 / δ ^ 3) = (Real.exp (ξ0 / δ ^ 3))⁻¹ := by rw [← Real.exp_neg]; ring_nf
  rw [hexp]
  have hp : 0 < (ξ0 / δ ^ 3) ^ n / n.factorial := by positivity
  have h2 : (Real.exp (ξ0 / δ ^ 3))⁻¹ ≤ ((ξ0 / δ ^ 3) ^ n / n.factorial)⁻¹ := inv_anti₀ hp h1
  have h3 : ((ξ0 / δ ^ 3) ^ n / n.factorial)⁻¹ = n.factorial * δ ^ (3 * n) / ξ0 ^ n := by
    rw [div_pow, ← pow_mul]; field_simp
  rw [h3] at h2
  have h4 : C * (n.factorial * δ ^ (3 * n) / ξ0 ^ n) ≤ δ ^ n := by
    have hδp : 0 < δ := hδ
    have hξn : 0 < ξ0 ^ n := by positivity
    rw [show C * (n.factorial * δ ^ (3 * n) / ξ0 ^ n) = (C * n.factorial / ξ0 ^ n) * δ ^ (3 * n) by ring]
    have hle : δ ^ (3 * n) ≤ δ ^ n * δ ^ n := by
      rw [← pow_add]; exact pow_le_pow_of_le_one hδp.le hδ1 (by omega)
    have hδn : δ ^ n ≤ 1 := pow_le_one₀ hδp.le hδ1
    have hcoef : C * n.factorial / ξ0 ^ n * δ ^ n ≤ 1 := by
      have : C * n.factorial / ξ0 ^ n * δ ^ n ≤ C * n.factorial / ξ0 ^ n * δ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_of_le_one hδp.le hδ1 (by omega)
      refine this.trans ?_
      rw [div_mul_eq_mul_div, div_le_one hξn]
      have : C * n.factorial * δ ≤ ξ0 ^ n := by
        have := mul_le_mul_of_nonneg_left hδ2 (by positivity : (0:ℝ) ≤ C * n.factorial)
        rw [mul_div_cancel₀ _ (by positivity)] at this
        exact this
      exact this
    calc C * n.factorial / ξ0 ^ n * δ ^ (3 * n) ≤ C * n.factorial / ξ0 ^ n * (δ ^ n * δ ^ n) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (C * n.factorial / ξ0 ^ n * δ ^ n) * δ ^ n := by ring
      _ ≤ 1 * δ ^ n := mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = δ ^ n := one_mul _
  calc C * (Real.exp (ξ0 / δ ^ 3))⁻¹ ≤ C * (n.factorial * δ ^ (3 * n) / ξ0 ^ n) := mul_le_mul_of_nonneg_left h2 hC.le
    _ ≤ δ ^ n := h4


/-- Lower bound for `|Ai(-v)|` at a large non-resonant `v` (`v ≥ 4`, `|cos(ξ - π/4)| > 1/10`) with `v δ² ≤ 1`: `|Ai(-v)| ≥ δ/25`. -/
lemma bwn_Ai_lower {v δ : ℝ} (hv4 : 4 ≤ v) (hvδ : v * δ ^ 2 ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hcos : 1 / 10 < |Real.cos (2 / 3 * v ^ (3 / 2 : ℝ) - π / 4)|) : δ / 25 ≤ |airyAi (-v)| := by
  have hv : 0 < v := by linarith
  have h1 := airyAi_neg_asymptotic hv
  set t : ℝ := v ^ (-(1 / 4) : ℝ) with ht
  have htp : 0 < t := Real.rpow_pos_of_pos hv _
  have hv32 : (8 : ℝ) ≤ v ^ (3 / 2 : ℝ) := by
    have : (4 : ℝ) ^ (3 / 2 : ℝ) ≤ v ^ (3 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hv4 (by norm_num)
    have e : (4 : ℝ) ^ (3 / 2 : ℝ) = 8 := by
      rw [← sqrt_cube_eq_rpow (by norm_num : (0 : ℝ) < 4)]
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num
    linarith
  have h74 : v ^ (-(7 / 4) : ℝ) = t * (v ^ (3 / 2 : ℝ))⁻¹ := by
    rw [ht, ← Real.rpow_neg hv.le, ← Real.rpow_add hv]; norm_num
  have hinv : (v ^ (3 / 2 : ℝ))⁻¹ ≤ 1 / 8 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hv32
  have hsq : √π < 1.78 := by
    rw [Real.sqrt_lt' (by norm_num)]
    have := Real.pi_lt_d2; norm_num; linarith
  have hsp : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have h2 : |1 / √π * t * Real.cos (2 / 3 * v ^ (3 / 2 : ℝ) - π / 4)| ≤ |airyAi (-v)| + 1 / 8 * (t * (v ^ (3 / 2 : ℝ))⁻¹) := by
    have := abs_sub_abs_le_abs_sub (1 / √π * t * Real.cos (2 / 3 * v ^ (3 / 2 : ℝ) - π / 4)) (airyAi (-v))
    rw [abs_sub_comm] at this
    rw [h74] at h1
    linarith
  have h3 : |1 / √π * t * Real.cos (2 / 3 * v ^ (3 / 2 : ℝ) - π / 4)| = 1 / √π * t * |Real.cos (2 / 3 * v ^ (3 / 2 : ℝ) - π / 4)| := by
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / √π), abs_of_pos htp]
  rw [h3] at h2
  have h4 : t * (1 / 25) ≤ |airyAi (-v)| := by
    have e1 : 1 / 17.8 ≤ 1 / √π * (1 / 10) * 1 := by
      have : 1 / 1.78 * (1 / 10) ≤ 1 / √π * (1 / 10) := by
        have : 1 / 1.78 ≤ 1 / √π := one_div_le_one_div_of_le hsp hsq.le
        nlinarith
      norm_num at this ⊢; linarith
    have e2 : 1 / √π * (1 / 10) * t ≤ 1 / √π * t * |Real.cos (2 / 3 * v ^ (3 / 2 : ℝ) - π / 4)| := by
      have : 0 ≤ 1 / √π * t := by positivity
      nlinarith
    have e3 : 1 / 8 * (t * (v ^ (3 / 2 : ℝ))⁻¹) ≤ t / 64 := by
      have := mul_le_mul_of_nonneg_left hinv htp.le
      nlinarith
    nlinarith
  have hs : (v ^ (1 / 4 : ℝ)) * δ ≤ 1 := by
    set s := v ^ (1 / 4 : ℝ) with hs
    have hsp' : 0 < s := Real.rpow_pos_of_pos hv _
    have hs4 : s ^ 4 = v := by
      rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hv.le]; norm_num
    by_contra hlt
    push Not at hlt
    have : 1 < (s * δ) ^ 4 := one_lt_pow₀ hlt (by norm_num)
    rw [mul_pow, hs4] at this
    have : v * δ ^ 4 ≤ 1 := by nlinarith [pow_le_one₀ hδ.le hδ1 (n := 2), sq_nonneg δ]
    linarith
  have hts : t = (v ^ (1 / 4 : ℝ))⁻¹ := by rw [ht, Real.rpow_neg hv.le]
  have hδt : δ ≤ t := by
    rw [hts, ← one_div, le_div_iff₀ (Real.rpow_pos_of_pos hv _)]
    linarith [mul_comm δ (v ^ (1 / 4 : ℝ))]
  nlinarith


/-- Size of `δ √v` on the window: from `(2/3) v^{3/2} ≤ (π/2) ρ/δ³`. -/
lemma bwn_vbounds {v δ ρ c2 : ℝ} (hv : 0 < v) (hδ : 0 < δ) (hc2 : 0 < c2) (hρ4 : ρ ≤ 1 / 4) (hρ : 0 ≤ ρ)
    (hρc : 200 * c2 ^ 3 * ρ ≤ 1) (hξ : 2 / 3 * v ^ (3 / 2 : ℝ) ≤ π / 2 * ρ / δ ^ 3) :
    c2 * δ * √v ≤ 1 / 4 ∧ v * δ ^ 2 ≤ 1 := by
  have hp := Real.pi_lt_d2
  have hw3 : (δ * √v) ^ 3 ≤ 3 * π / 4 * ρ := by
    have e : v ^ (3 / 2 : ℝ) = (√v) ^ 3 := (sqrt_cube_eq_rpow hv).symm
    rw [e] at hξ
    rw [le_div_iff₀ (by positivity)] at hξ
    rw [mul_pow]; nlinarith
  have hw0 : 0 ≤ δ * √v := by positivity
  have hw1 : δ * √v ≤ 1 := by
    by_contra h; push Not at h
    have := one_lt_pow₀ h (by norm_num : (3 : ℕ) ≠ 0)
    nlinarith
  refine ⟨?_, ?_⟩
  · by_contra h; push Not at h
    have h' : 1 / 4 < c2 * (δ * √v) := by linarith [mul_assoc c2 δ (√v)]
    have : (1 / 4 : ℝ) ^ 3 < (c2 * (δ * √v)) ^ 3 := pow_lt_pow_left₀ h' (by norm_num) (by norm_num)
    rw [mul_pow] at this
    have h3 : c2 ^ 3 * (δ * √v) ^ 3 ≤ c2 ^ 3 * (3 * π / 4 * ρ) := mul_le_mul_of_nonneg_left hw3 (by positivity)
    have h4 : c2 ^ 3 * ρ ≤ 1 / 200 := by linarith
    have h5 : c2 ^ 3 * (3 * π / 4 * ρ) = 3 * π / 4 * (c2 ^ 3 * ρ) := by ring
    have h6 : 3 * π / 4 * (c2 ^ 3 * ρ) ≤ 3 * π / 4 * (1 / 200) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    norm_num at this ⊢
    nlinarith [Real.pi_pos]
  · have : v * δ ^ 2 = (δ * √v) ^ 2 := by rw [mul_pow, Real.sq_sqrt hv.le]; ring
    rw [this]; nlinarith


end FormalResearch.Special
