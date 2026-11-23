module

public import Mathlib

/-!
# Energy bound for the Bessel recurrence system

If `a, b` satisfy `a' = (ν/x) a - b` and `b' = a - ((ν+1)/x) b` for `x ≥ x₀ > 0` (the pair
`J_ν, J_{ν+1}`, DLMF 10.6.2) with `ν ≥ -1/2`, then `x (a² + b²)` is bounded for `x ≥ max x₀ (2ν+1)`.
The Lyapunov function is `L = x (a² + b²) - (2ν+1) a b`, with `L' = (2ν+1) a b / x`.
-/

@[expose] public section

open Set

namespace FormalResearch.Special

theorem bessel_energy_bound {ν : ℝ} (hν : -1 / 2 ≤ ν) {a b : ℝ → ℝ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (ha : ∀ x ≥ x₀, HasDerivAt a (ν / x * a x - b x) x)
    (hb : ∀ x ≥ x₀, HasDerivAt b (a x - (ν + 1) / x * b x) x) :
    ∃ C : ℝ, ∀ x ≥ max x₀ (2 * ν + 1), x * (a x ^ 2 + b x ^ 2) ≤ C := by
  set κ : ℝ := 2 * ν + 1 with hκ
  have hκ0 : 0 ≤ κ := by linarith
  set x₁ : ℝ := max x₀ κ with hx₁
  have hx₁0 : 0 < x₁ := lt_of_lt_of_le hx₀ (le_max_left _ _)
  set L : ℝ → ℝ := fun x => x * (a x ^ 2 + b x ^ 2) - κ * (a x * b x) with hL
  set M : ℝ → ℝ := fun x => L x * Real.exp (κ / x) with hM
  have hLd : ∀ x ≥ x₀, HasDerivAt L (κ * (a x * b x) / x) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hx₀ hx
    have h1 := ((hasDerivAt_id x).mul (((ha x hx).pow 2).add ((hb x hx).pow 2))).sub
      (((ha x hx).mul (hb x hx)).const_mul κ)
    refine h1.congr_deriv ?_
    simp only [id, Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat]
    field_simp
    simp only [hκ]
    ring
  have hMd : ∀ x ≥ x₀, HasDerivAt M (Real.exp (κ / x) * (κ * (a x * b x) / x - κ * L x / x ^ 2)) x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hx₀ hx
    have h2 := ((hasDerivAt_const x κ).div (hasDerivAt_id x) hx0.ne').exp
    have h3 := (hLd x hx).mul h2
    refine h3.congr_deriv ?_
    simp only [id, Pi.div_apply]
    field_simp
    simp only [hL]
    ring
  have hab : ∀ x, 2 * |a x * b x| ≤ a x ^ 2 + b x ^ 2 := fun x => by
    rw [abs_mul]; nlinarith [sq_nonneg (|a x| - |b x|), sq_abs (a x), sq_abs (b x)]
  have hLge : ∀ x ≥ x₁, x * (a x ^ 2 + b x ^ 2) ≤ 2 * L x := by
    intro x hx
    have hxκ : κ ≤ x := le_trans (le_max_right _ _) hx
    have := hab x
    have h1 : κ * (a x * b x) ≤ κ * |a x * b x| := mul_le_mul_of_nonneg_left (le_abs_self _) hκ0
    have h2 : κ * |a x * b x| ≤ x * |a x * b x| := mul_le_mul_of_nonneg_right hxκ (abs_nonneg _)
    simp only [hL]
    nlinarith [sq_nonneg (a x), sq_nonneg (b x)]
  have hMnonpos : ∀ x ≥ x₁, Real.exp (κ / x) * (κ * (a x * b x) / x - κ * L x / x ^ 2) ≤ 0 := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hx₁0 hx
    have hxκ : κ ≤ x := le_trans (le_max_right _ _) hx
    refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ?_
    have h1 := hLge x hx
    have h2 := hab x
    have h3 : a x * b x ≤ |a x * b x| := le_abs_self _
    rw [sub_nonpos, div_le_div_iff₀ hx0 (by positivity)]
    have : κ * (a x * b x) * x ^ 2 ≤ κ * L x * x := by
      have : x * (a x * b x) ≤ L x := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this hκ0, hx0]
    nlinarith
  have hanti : AntitoneOn M (Ici x₁) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici x₁) ?_ ?_ ?_
    · exact fun x hx => (hMd x (le_trans (le_max_left _ _) hx)).continuousAt.continuousWithinAt
    · exact fun x hx => (hMd x (le_trans (le_max_left _ _)
        (interior_subset hx))).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : x₁ ≤ x := le_of_lt hx
      rw [(hMd x (le_trans (le_max_left _ _) hx')).deriv]
      exact hMnonpos x hx'
  have hL1 : 0 ≤ L x₁ := by
    have := hLge x₁ le_rfl
    nlinarith [sq_nonneg (a x₁), sq_nonneg (b x₁)]
  refine ⟨2 * M x₁, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le hx₁0 hx
  have hMx : M x ≤ M x₁ := hanti Set.self_mem_Ici hx hx
  have hexp : 1 ≤ Real.exp (κ / x) := Real.one_le_exp (by positivity)
  have hLx : L x ≤ M x := by
    have : 0 ≤ L x := by
      have := hLge x hx
      nlinarith [sq_nonneg (a x), sq_nonneg (b x)]
    simp only [hM]
    nlinarith
  linarith [hLge x hx]

/-- info: 'FormalResearch.Special.bessel_energy_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bessel_energy_bound

end FormalResearch.Special
