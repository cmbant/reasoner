module

public import FormalResearch.Special.DiscreteAiryKappaProfile
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The Riemann sum `h Σ 1/α_k` of the Hahn profile (plan K1, step K-2)

For `q_k = (k+½)h`, `α_k = √(q_*² - q_k²)`: with `F(q) = arcsin(q/q_*)` (`F' = 1/√(q_*² - q²)`, increasing), the mean value theorem gives
`h/α(a) ≤ F(a+h) - F(a) ≤ h/α(a+h)` for `0 ≤ a`, `a + h < q_*`, and telescoping gives, for the sites `k₀, …, k₀+m`,

`arcsin(q_{k₀+m}/q_*) - arcsin(q_{k₀-1}/q_*) ≤ h Σ_{i≤m} 1/α_{k₀+i} ≤ arcsin(q_{k₀+m+1}/q_*) - arcsin(q_{k₀}/q_*)` (`kr_sum_bounds`).

Together with `kp_hahn_band_mass` this gives the band mass `Σ Ŷ² = (I/h)(Θ_b - Θ_a)(1 + o(1))`, `Θ = arcsin(q/q_*)`: the origin of
`π` in `|κ|² ≈ 2 N^{1/3}` (`Θ_b - Θ_a → π/2`, `I = 2/π`).  **Claim class: proved.**
-/

@[expose] public section

open Finset Set

namespace FormalResearch.Special

/-- **Mean value bound for `F = arcsin(·/q_*)`**: for `0 ≤ a < b < q_*`,
`(b - a)/√(q_*² - a²) ≤ F(b) - F(a) ≤ (b - a)/√(q_*² - b²)`. -/
lemma kr_arcsin_mvt {qs a b : ℝ} (hq : 0 < qs) (ha : 0 ≤ a) (hab : a < b) (hb : b < qs) :
    (b - a) / Real.sqrt (qs ^ 2 - a ^ 2) ≤ Real.arcsin (b / qs) - Real.arcsin (a / qs) ∧
      Real.arcsin (b / qs) - Real.arcsin (a / qs) ≤ (b - a) / Real.sqrt (qs ^ 2 - b ^ 2) := by
  have hder : ∀ x ∈ Set.Ioo a b, HasDerivAt (fun x => Real.arcsin (x / qs)) (1 / Real.sqrt (qs ^ 2 - x ^ 2)) x := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hxq : x < qs := by linarith [hx.2]
    have h1 : x / qs ≠ -1 := by
      have : 0 < x / qs := by positivity
      linarith
    have h2 : x / qs ≠ 1 := by
      have : x / qs < 1 := by rw [div_lt_one hq]; exact hxq
      exact this.ne
    have hd := (Real.hasDerivAt_arcsin h1 h2).comp x ((hasDerivAt_id x).div_const qs)
    have e : 1 / Real.sqrt (1 - (x / qs) ^ 2) * (1 / qs) = 1 / Real.sqrt (qs ^ 2 - x ^ 2) := by
      have hpos : 0 < qs ^ 2 - x ^ 2 := by nlinarith
      have : Real.sqrt (1 - (x / qs) ^ 2) = Real.sqrt (qs ^ 2 - x ^ 2) / qs := by
        rw [show 1 - (x / qs) ^ 2 = (qs ^ 2 - x ^ 2) / qs ^ 2 by field_simp, Real.sqrt_div hpos.le, Real.sqrt_sq hq.le]
      rw [this]
      have : 0 < Real.sqrt (qs ^ 2 - x ^ 2) := Real.sqrt_pos.2 hpos
      field_simp
    have hd2 : HasDerivAt (fun x => Real.arcsin (x / qs)) (1 / Real.sqrt (1 - (x / qs) ^ 2) * (1 / qs)) x := by
      simpa [Function.comp_def, one_div] using hd
    rw [e] at hd2
    exact hd2
  have hcont : ContinuousOn (fun x => Real.arcsin (x / qs)) (Set.Icc a b) := by
    exact (Real.continuous_arcsin.comp (continuous_id.div_const qs)).continuousOn
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope (fun x => Real.arcsin (x / qs))
    (fun x => 1 / Real.sqrt (qs ^ 2 - x ^ 2)) hab hcont hder
  have hba : 0 < b - a := by linarith
  have hξq : ξ < qs := by linarith [hξ.2]
  have hξ0 : 0 < ξ := by linarith [hξ.1]
  have hdiff : Real.arcsin (b / qs) - Real.arcsin (a / qs) = (b - a) / Real.sqrt (qs ^ 2 - ξ ^ 2) := by
    have := hξe
    field_simp at this ⊢
    nlinarith [this]
  rw [hdiff]
  have hpa : 0 < Real.sqrt (qs ^ 2 - a ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hpb : 0 < Real.sqrt (qs ^ 2 - b ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hpξ : 0 < Real.sqrt (qs ^ 2 - ξ ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  constructor
  · apply div_le_div_of_nonneg_left hba.le hpξ
    exact Real.sqrt_le_sqrt (by nlinarith [hξ.1])
  · apply div_le_div_of_nonneg_left hba.le hpb
    exact Real.sqrt_le_sqrt (by nlinarith [hξ.2])

/-- The lattice position `q_k = (k + θ) h` (`θ = ½`: `kpU`, integer-rank chains; `θ = 1`: half-integer chains), the profile radius `α_k = √(q_*² - q_k²)` and the Ermakov profile `P_k = 2/α_k` on it. -/
noncomputable def kpUg (θ h : ℝ) (k : ℤ) : ℝ := ((k : ℝ) + θ) * h

/-- `α_k = √(q_*² - q_k²)` on the lattice `q_k = (k + θ) h`. -/
noncomputable def kpαg (θ qs h : ℝ) (k : ℤ) : ℝ := Real.sqrt (qs ^ 2 - kpUg θ h k ^ 2)

/-- `P_k = 2/α_k` on the lattice `q_k = (k + θ) h`. -/
noncomputable def kpPg (θ qs h : ℝ) (k : ℤ) : ℝ := 2 / kpαg θ qs h k

/-- **Riemann sums of `1/α`** (see the module docstring): for `k₀ ≥ 1`, `h > 0`, `q_{k₀+m+1} < q_*`,
`q_k = (k+θ)h`, `arcsin(q_{k₀+m}/q_*) - arcsin(q_{k₀-1}/q_*) ≤ h Σ_{i≤m} 1/α_{k₀+i} ≤ arcsin(q_{k₀+m+1}/q_*) - arcsin(q_{k₀}/q_*)`. -/
theorem kr_sum_bounds_g {θ qs h : ℝ} (hθ : 0 < θ) {k0 : ℤ} (m : ℕ) (hq : 0 < qs) (hh : 0 < h) (hk0 : 1 ≤ k0)
    (hend : kpUg θ h (k0 + (m : ℤ) + 1) < qs) :
    Real.arcsin (kpUg θ h (k0 + (m : ℤ)) / qs) - Real.arcsin (kpUg θ h (k0 - 1) / qs) ≤
        h * ∑ i ∈ range (m + 1), 1 / kpαg θ qs h (k0 + (i : ℤ)) ∧
      h * ∑ i ∈ range (m + 1), 1 / kpαg θ qs h (k0 + (i : ℤ)) ≤
        Real.arcsin (kpUg θ h (k0 + (m : ℤ) + 1) / qs) - Real.arcsin (kpUg θ h k0 / qs) := by
  have hk' : (1 : ℝ) ≤ k0 := by exact_mod_cast hk0
  have hU : ∀ i : ℕ, i ≤ m + 1 → 0 < kpUg θ h (k0 + (i : ℤ) - 1) ∧ kpUg θ h (k0 + (i : ℤ)) < qs := by
    intro i hi
    refine ⟨?_, ?_⟩
    · unfold kpUg; push_cast
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      exact mul_pos (by linarith) hh
    · have : kpUg θ h (k0 + (i : ℤ)) ≤ kpUg θ h (k0 + (m : ℤ) + 1) := by
        unfold kpUg; push_cast
        have : (i : ℝ) ≤ m + 1 := by exact_mod_cast hi
        nlinarith
      linarith
  have hstep : ∀ i : ℕ, i ≤ m →
      h / kpαg θ qs h (k0 + (i : ℤ)) ≤ Real.arcsin (kpUg θ h (k0 + (i : ℤ) + 1) / qs) - Real.arcsin (kpUg θ h (k0 + (i : ℤ)) / qs) ∧
      Real.arcsin (kpUg θ h (k0 + (i : ℤ)) / qs) - Real.arcsin (kpUg θ h (k0 + (i : ℤ) - 1) / qs) ≤ h / kpαg θ qs h (k0 + (i : ℤ)) := by
    intro i hi
    have hUi := hU i (by omega)
    have hUi1 := hU (i + 1) (by omega)
    have hsucc : kpUg θ h (k0 + ((i + 1 : ℕ) : ℤ) - 1) = kpUg θ h (k0 + (i : ℤ)) := by unfold kpUg; push_cast; ring
    rw [hsucc] at hUi1
    have h1 : kpUg θ h (k0 + (i : ℤ) + 1) = kpUg θ h (k0 + (i : ℤ)) + h := by unfold kpUg; push_cast; ring
    have h2 : kpUg θ h (k0 + (i : ℤ) - 1) = kpUg θ h (k0 + (i : ℤ)) - h := by unfold kpUg; push_cast; ring
    have hlt1 : kpUg θ h (k0 + (i : ℤ) + 1) < qs := by
      have := hU (i + 1) (by omega)
      have e : kpUg θ h (k0 + ((i + 1 : ℕ) : ℤ)) = kpUg θ h (k0 + (i : ℤ) + 1) := by unfold kpUg; push_cast; ring
      rw [e] at this; exact this.2
    have hUk : 0 < kpUg θ h (k0 + (i : ℤ)) := by rw [h2] at hUi; linarith [hUi.1]
    have hUm : 0 < kpUg θ h (k0 + (i : ℤ) - 1) := hUi.1
    have hlk : kpUg θ h (k0 + (i : ℤ)) < qs := hUi.2
    have hαk : kpαg θ qs h (k0 + (i : ℤ)) = Real.sqrt (qs ^ 2 - kpUg θ h (k0 + (i : ℤ)) ^ 2) := rfl
    constructor
    · have := (kr_arcsin_mvt (qs := qs) (a := kpUg θ h (k0 + (i : ℤ))) (b := kpUg θ h (k0 + (i : ℤ) + 1)) hq hUk.le
        (by rw [h1]; linarith) hlt1).1
      rw [h1, add_sub_cancel_left] at this
      rw [hαk, h1]; exact this
    · have := (kr_arcsin_mvt (qs := qs) (a := kpUg θ h (k0 + (i : ℤ) - 1)) (b := kpUg θ h (k0 + (i : ℤ))) hq hUm.le
        (by rw [h2]; linarith) hlk).2
      rw [hαk]
      rw [h2] at this ⊢
      rwa [sub_sub_cancel] at this
  have hsum : h * ∑ i ∈ range (m + 1), 1 / kpαg θ qs h (k0 + (i : ℤ)) = ∑ i ∈ range (m + 1), h / kpαg θ qs h (k0 + (i : ℤ)) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  have e1 : ∑ i ∈ range (m + 1), (Real.arcsin (kpUg θ h (k0 + (i : ℤ) + 1) / qs) - Real.arcsin (kpUg θ h (k0 + (i : ℤ)) / qs)) =
      Real.arcsin (kpUg θ h (k0 + (m : ℤ) + 1) / qs) - Real.arcsin (kpUg θ h k0 / qs) := by
    have := Finset.sum_range_sub (fun i : ℕ => Real.arcsin (kpUg θ h (k0 + (i : ℤ)) / qs)) (m + 1)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] at this
    simpa [add_assoc] using this
  have e2 : ∑ i ∈ range (m + 1), (Real.arcsin (kpUg θ h (k0 + (i : ℤ)) / qs) - Real.arcsin (kpUg θ h (k0 + (i : ℤ) - 1) / qs)) =
      Real.arcsin (kpUg θ h (k0 + (m : ℤ)) / qs) - Real.arcsin (kpUg θ h (k0 - 1) / qs) := by
    set g : ℕ → ℝ := fun i => Real.arcsin (kpUg θ h (k0 + (i : ℤ) - 1) / qs) with hg
    have e : ∀ i : ℕ, Real.arcsin (kpUg θ h (k0 + (i : ℤ)) / qs) = g (i + 1) := by
      intro i; rw [hg]; simp only []; congr 2; unfold kpUg; push_cast; ring
    have key : ∀ i : ℕ, Real.arcsin (kpUg θ h (k0 + (i : ℤ)) / qs) - Real.arcsin (kpUg θ h (k0 + (i : ℤ) - 1) / qs) = g (i + 1) - g i := by
      intro i; rw [e i]
    simp only [key]
    rw [Finset.sum_range_sub g (m + 1), e m]
    simp [hg]
  constructor
  · rw [← e2]; exact Finset.sum_le_sum fun i hi => (hstep i (by have := Finset.mem_range.1 hi; omega)).2
  · rw [← e1]; exact Finset.sum_le_sum fun i hi => (hstep i (by have := Finset.mem_range.1 hi; omega)).1

/-- info: 'FormalResearch.Special.kr_sum_bounds_g' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kr_sum_bounds_g

/-- **Riemann sums of `1/α`** (see the module docstring): for `k₀ ≥ 1`, `h > 0`, `q_{k₀+m+1} < q_*`,
`arcsin(q_{k₀+m}/q_*) - arcsin(q_{k₀-1}/q_*) ≤ h Σ_{i≤m} 1/α_{k₀+i} ≤ arcsin(q_{k₀+m+1}/q_*) - arcsin(q_{k₀}/q_*)`. -/
theorem kr_sum_bounds {qs h : ℝ} {k0 : ℤ} (m : ℕ) (hq : 0 < qs) (hh : 0 < h) (hk0 : 1 ≤ k0)
    (hend : kpU h (k0 + (m : ℤ) + 1) < qs) :
    Real.arcsin (kpU h (k0 + (m : ℤ)) / qs) - Real.arcsin (kpU h (k0 - 1) / qs) ≤
        h * ∑ i ∈ range (m + 1), 1 / kpα qs h (k0 + (i : ℤ)) ∧
      h * ∑ i ∈ range (m + 1), 1 / kpα qs h (k0 + (i : ℤ)) ≤
        Real.arcsin (kpU h (k0 + (m : ℤ) + 1) / qs) - Real.arcsin (kpU h k0 / qs) := kr_sum_bounds_g (θ := 1 / 2) (by norm_num) m hq hh hk0 hend

/-- info: 'FormalResearch.Special.kr_sum_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kr_sum_bounds

end FormalResearch.Special
