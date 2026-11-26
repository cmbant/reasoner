module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasMoments
public import FormalResearch.SignUncertainty.CtBoasTent

/-!
# `ct:boas`: the lower cut `L_min = L(ξ(-c^{4/7}))` and the node grid

`constant_terms_lower.tex`, `ct:boas` Step 3 and `ct:dyadic` (4): `ctLv0 c = log(π² ξ(-v₀))`, `v₀ = c^{4/7}`, is the lower limit of the
Boas integral.  On the Langer chart `v'(L) = K g(L)` (`ctVprime`, `K = c^{2/3}κ`, `0.998 L ≤ g ≤ 1.0025 L`), `L_min ≍ c^{-2/21}`:

* `ctLv0_facts`: for `c ≥ c₀`, `0 < L_min`, `e^{L_min} - 1 ≤ 5·10⁻⁴`, `v'(L_min) = c^{4/7}` and `κ₀ c^{-2/21} ≤ (5/6)L_min`;
* `exists_tentNode_min`: the minimal node `J` of the grid `x_k = tentNode a` with `b ≤ x_J` has `x_{J-1} < b` and
  `J ≤ 37 log(1/a) + 36 b + 3`.

**Proved**, unconditional.
-/

@[expose] public section

open Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- **`L_min ≍ c^{-2/21}`**. -/
theorem ctLv0_facts : ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ c₀ : ℝ, 1 ≤ c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
    0 < ctLv0 c ∧ Real.exp (ctLv0 c) - 1 ≤ 5e-4 ∧ ctVprime c (ctLv0 c) = c ^ (4 / 7 : ℝ) ∧
      κ₀ * c ^ (-(2 / 21) : ℝ) ≤ 5 / 6 * ctLv0 c := by
  have hκ := langerKappa_pos
  have hev : ∀ᶠ c : ℝ in atTop, (langerKappa * 4.94e-4)⁻¹ ≤ c ^ (2 / 21 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 21)).eventually_ge_atTop _
  obtain ⟨c₁, hc₁⟩ := eventually_atTop.1 hev
  refine ⟨5 / (6 * 1.0025 * langerKappa), by positivity, max 1 c₁, le_max_left _ _, fun c hc => ?_⟩
  have hc1 : 1 ≤ c := (le_max_left _ _).trans hc
  have hc0 : 0 < c := by linarith
  have hcc : (langerKappa * 4.94e-4)⁻¹ ≤ c ^ (2 / 21 : ℝ) := hc₁ c ((le_max_right _ _).trans hc)
  have hr0 : 0 < c ^ (4 / 7 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have e1 : c ^ (4 / 7 : ℝ) = c ^ (2 / 3 : ℝ) * c ^ (-(2 / 21) : ℝ) := by
    rw [← Real.rpow_add hc0]; norm_num
  have hneg : 0 < c ^ (-(2 / 21) : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hpos : 0 < c ^ (2 / 21 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hmul : c ^ (-(2 / 21) : ℝ) * c ^ (2 / 21 : ℝ) = 1 := by
    rw [← Real.rpow_add hc0]; norm_num
  have hr : c ^ (4 / 7 : ℝ) ≤ langerRadius c := by
    have h1 : c ^ (-(2 / 21) : ℝ) ≤ langerKappa * 4.94e-4 := by
      have h2 := mul_le_mul_of_nonneg_left hcc hneg.le
      have h3 : c ^ (-(2 / 21) : ℝ) * (langerKappa * 4.94e-4)⁻¹ ≤ 1 := by rw [hmul] at h2; exact h2
      rw [← div_eq_mul_inv, div_le_one (by positivity)] at h3
      exact h3
    have : langerRadius c = c ^ (2 / 3 : ℝ) * (langerKappa * 4.94e-4) := by
      unfold langerRadius langerScale; ring
    rw [this, e1]
    exact mul_le_mul_of_nonneg_left h1 (Real.rpow_pos_of_pos hc0 _).le
  obtain ⟨h0, h1, h2⟩ := hankel_band_edge hc0 hr0 hr
  have hL : ctLv0 c = Real.log (π ^ 2 * hankelXi c (-(c ^ (4 / 7 : ℝ)))) := rfl
  rw [← hL] at h0 h1 h2
  refine ⟨h0, h1, h2, ?_⟩
  have hb := (ctVprime_bounds hc0 h0.le h1).2
  rw [h2] at hb
  have hK : langerScale c = c ^ (2 / 3 : ℝ) * langerKappa := rfl
  rw [hK, e1] at hb
  have h23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have : c ^ (-(2 / 21) : ℝ) ≤ 1.0025 * langerKappa * ctLv0 c := by
    have : c ^ (2 / 3 : ℝ) * c ^ (-(2 / 21) : ℝ) ≤ c ^ (2 / 3 : ℝ) * (1.0025 * langerKappa * ctLv0 c) := by
      calc _ ≤ 1.0025 * (c ^ (2 / 3 : ℝ) * langerKappa) * ctLv0 c := hb
        _ = _ := by ring
    exact le_of_mul_le_mul_left this h23
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- **The minimal grid index**: for `0 < a ≤ 1 < b` there is `J ≥ 1` with `b ≤ x_J`, `x_{J-1} < b` and
`J ≤ 37 log(1/a) + 36 b + 3`. -/
theorem exists_tentNode_min {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hab : a < b) :
    ∃ J : ℕ, 1 ≤ J ∧ b ≤ tentNode a J ∧ tentNode a (J - 1) < b ∧ (J : ℝ) ≤ 37 * Real.log (1 / a) + 36 * b + 3 := by
  classical
  obtain ⟨J0, -, hJ0, hJ0b⟩ := exists_tentNode_ge ha ha1 (by linarith : 0 ≤ b)
  have hex : ∃ J : ℕ, b ≤ tentNode a J := ⟨J0, hJ0⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_, ?_⟩
  · by_contra h
    have h0 : Nat.find hex = 0 := by omega
    have := Nat.find_spec hex
    rw [h0] at this
    simp [tentNode] at this
    linarith
  · have h1 : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0] at this
      simp [tentNode] at this
      linarith
    have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    exact not_le.1 this
  · have : Nat.find hex ≤ J0 := Nat.find_min' hex hJ0
    have : (Nat.find hex : ℝ) ≤ J0 := by exact_mod_cast this
    linarith

end FormalResearch.SignUncertainty
