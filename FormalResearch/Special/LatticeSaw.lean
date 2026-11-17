module

public import FormalResearch.Special.LatticeContour
public import Mathlib.NumberTheory.ZetaValues

/-!
# The sawtooth antiderivative `H` and its Fourier series

`sawH y = ({y}² - {y} + 1/6)/2 = B₂({y})/2` is continuous, `1`-periodic, with
`sawH' y = {y} - 1/2` off `ℤ`, and (Mathlib's Bernoulli Fourier series for `k = 2`)
`sawH y = ∑_{n≥1} cos(2πny)/(2π²n²)`, absolutely convergent.

In the proof of `lem:latticesum` (i) the paper expands the sawtooth `{y} - ½` itself, whose partial sums
are only bounded; here we integrate by parts once and expand `sawH` instead.  This is what makes
all interchanges of sum and integral absolutely convergent.
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex MeasureTheory intervalIntegral

/-- `B₂({y})/2`, the periodic antiderivative of `{y} - ½`. -/
noncomputable def sawH (y : ℝ) : ℝ := ((Int.fract y) ^ 2 - Int.fract y + 1 / 6) / 2

lemma hasSum_sawH (y : ℝ) :
    HasSum (fun n : ℕ => Real.cos (2 * Real.pi * n * y) / (2 * Real.pi ^ 2 * (n : ℝ) ^ 2)) (sawH y) := by
  have hx : Int.fract y ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg y, (Int.fract_lt_one y).le⟩
  have h := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hx
  have h2 := h.mul_left (1 / (2 * Real.pi ^ 2))
  have hB : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * 1))).eval (Int.fract y) =
      (Int.fract y) ^ 2 - Int.fract y + 6⁻¹ := bernoulliFun_two (Int.fract y)
  rw [hB] at h2
  have e1 : ∀ n : ℕ, Real.cos (2 * Real.pi * n * Int.fract y) = Real.cos (2 * Real.pi * n * y) := by
    intro n
    have : 2 * Real.pi * n * y = 2 * Real.pi * n * Int.fract y + ((n * ⌊y⌋ : ℤ) : ℝ) * (2 * Real.pi) := by
      have : y = Int.fract y + ⌊y⌋ := by rw [Int.fract_add_floor]
      push_cast
      conv_lhs => rw [this]
      ring
    rw [this, Real.cos_add_int_mul_two_pi]
  have e2 : sawH y = 1 / (2 * Real.pi ^ 2) * ((-1 : ℝ) ^ (1 + 1) * (2 * Real.pi) ^ (2 * 1) / 2 /
      ((2 * 1).factorial : ℝ) * ((Int.fract y) ^ 2 - Int.fract y + 6⁻¹)) := by
    unfold sawH
    have := Real.pi_pos
    simp [Nat.factorial]
    field_simp
  rw [e2]
  convert h2 using 1
  ext n
  rw [e1]
  have : (2 * Real.pi ^ 2 * (n : ℝ) ^ 2) = (2 * Real.pi ^ 2) * (n : ℝ) ^ 2 := rfl
  by_cases hn : n = 0
  · simp [hn]
  · have := Real.pi_pos
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
    ring

lemma summable_sawH_terms : Summable (fun n : ℕ => 1 / (2 * Real.pi ^ 2) * (1 / (n : ℝ) ^ 2)) :=
  (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left _

lemma continuous_sawH : Continuous sawH := by
  have hfun : sawH = fun y => ∑' n : ℕ, Real.cos (2 * Real.pi * n * y) / (2 * Real.pi ^ 2 * (n : ℝ) ^ 2) := by
    ext y; exact (hasSum_sawH y).tsum_eq.symm
  rw [hfun]
  refine continuous_tsum (fun n => by fun_prop) summable_sawH_terms (fun n y => ?_)
  rw [Real.norm_eq_abs, abs_div]
  by_cases hn : n = 0
  · simp [hn]
  · have hp := Real.pi_pos
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [abs_of_pos (by positivity : 0 < 2 * Real.pi ^ 2 * (n : ℝ) ^ 2)]
    calc |Real.cos (2 * Real.pi * n * y)| / (2 * Real.pi ^ 2 * (n : ℝ) ^ 2)
        ≤ 1 / (2 * Real.pi ^ 2 * (n : ℝ) ^ 2) :=
          div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)
      _ = 1 / (2 * Real.pi ^ 2) * (1 / (n : ℝ) ^ 2) := by field_simp

lemma hasDerivAt_sawH {y : ℝ} (hy : ∀ n : ℤ, y ≠ n) :
    HasDerivAt sawH (Int.fract y - 1 / 2) y := by
  set n : ℤ := ⌊y⌋ with hn
  have h1 : (n : ℝ) < y := lt_of_le_of_ne (Int.floor_le y) (fun h => hy n h.symm)
  have h2 : y < n + 1 := Int.lt_floor_add_one y
  have hev : sawH =ᶠ[𝓝 y] fun z => (((z - n) ^ 2 - (z - n) + 1 / 6) / 2) := by
    filter_upwards [Ioo_mem_nhds h1 h2] with z hz
    have : Int.fract z = z - n := by
      rw [Int.fract, show ⌊z⌋ = n from by rw [Int.floor_eq_iff]; exact ⟨hz.1.le, hz.2⟩]
    unfold sawH; rw [this]
  have hd : HasDerivAt (fun z : ℝ => (((z - n) ^ 2 - (z - n) + 1 / 6) / 2)) ((2 * (y - n) - 1) / 2) y := by
    have h0 := (((hasDerivAt_id' y).sub_const (n : ℝ)).pow 2).sub
      ((hasDerivAt_id' y).sub_const (n : ℝ)) |>.add_const (1 / 6 : ℝ) |>.div_const 2
    refine h0.congr_deriv ?_
    push_cast
    ring
  refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [Int.fract]; ring

lemma CalPhase.ofReal_eq {τ0 : ℂ → ℂ} {X y0 m M K : ℝ} (h : CalPhase τ0 X y0 m M K) (x : ℝ) :
    τ0 (x : ℂ) = ((realPhase τ0 x : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [realPhase]
  · simpa using h.real x

end FormalResearch.Special.Lattice
