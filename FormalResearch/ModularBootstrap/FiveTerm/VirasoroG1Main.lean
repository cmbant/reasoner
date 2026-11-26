module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroAmpIntegral
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG1Jet

/-!
# `g₁ = 3 + 6/π - 16√2 ξ_*` (FIVE-0, `ctu:jets` / `cts:piece4` for `g₁`)

Assembly: the slope of `Re h̄_a` at the edge point `0` is `d = 2 ∫₀^∞ a'(τ)/sinh(πτ) dτ`
(`hbarA_slope`, `slope_ibp`), evaluated as the sum of the `x_T b_T` Cauchy integral (`xb_cauchy_identity`) and the
five elementary integrals; with `g1Out_of_slope` this gives `g1Out = g1Vir`, hence `comb_minimum_virasoro` in the
form `IsLeast … c0Star`.  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

lemma xA_even (t : ℝ) : xA (-t) = xA t := by
  unfold xA
  rw [xT_even, mul_neg, Real.cosh_neg]

lemma vA_even (t : ℝ) : vA (-t) = vA t := by
  unfold vA
  have e : π * (-t) / 2 = -(π * t / 2) := by ring
  rw [vT_odd, e, mul_neg, Real.cosh_neg, Real.sinh_neg, neg_sq, mul_neg, neg_div_neg_eq]

lemma integral_xA_vA_Ioi : ∫ t in Ioi (0 : ℝ), (xA t + vA t) = π - √2 := by
  obtain ⟨-, -, h⟩ := xb_cauchy_identity
  have hev : ∀ t : ℝ, (fun s => xA s + vA s) |t| = xA t + vA t := by
    intro t
    rcases abs_cases t with ⟨e, _⟩ | ⟨e, _⟩
    · simp only [e]
    · simp only [e, xA_even, vA_even]
  have := integral_comp_abs (f := fun s => xA s + vA s)
  simp only [hev] at this
  linarith

/-- `∫₀^∞ a'(τ)/sinh(πτ) dτ = 11π/16 + 3/4 - √2/8 - 2√2 arsinh 1`, and the integrand is integrable. -/
lemma aD_integral :
    IntegrableOn (fun t : ℝ => aD t / Real.sinh (π * t)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), aD t / Real.sinh (π * t) =
        11 * π / 16 + 3 / 4 - √2 / 8 - 2 * √2 * Real.arsinh 1 := by
  obtain ⟨hxi, hvi, -⟩ := xb_cauchy_identity
  obtain ⟨iS, vS⟩ := int_sech
  obtain ⟨iH, vH⟩ := int_half
  obtain ⟨iQ, vQ⟩ := int_sqrt
  obtain ⟨i4, v4⟩ := int_g4
  obtain ⟨i5, v5⟩ := int_g5
  have iXV : IntegrableOn (fun t => xA t + vA t) (Ioi 0) := (hxi.add hvi).integrableOn
  have iP : IntegrableOn (fun t => (1 / 8) * (xA t + vA t)) (Ioi 0) := iXV.const_mul _
  have iR : IntegrableOn (fun t => (1 / 2) * (π / Real.cosh (π * t)) + π / (1 + Real.cosh (π * t)) -
        2 * (π / √(Real.cosh (π * t) * (1 + Real.cosh (π * t)))) + (5 / 8) * g4 t + (3 / 8) * g5 t)
      (Ioi 0) :=
    ((((iS.const_mul (1 / 2)).add iH).sub (iQ.const_mul 2)).add (i4.const_mul (5 / 8))).add (i5.const_mul (3 / 8))
  have heq : ∀ t ∈ Ioi (0 : ℝ), aD t / Real.sinh (π * t) = (1 / 8) * (xA t + vA t) +
      ((1 / 2) * (π / Real.cosh (π * t)) + π / (1 + Real.cosh (π * t)) -
        2 * (π / √(Real.cosh (π * t) * (1 + Real.cosh (π * t)))) + (5 / 8) * g4 t + (3 / 8) * g5 t) := by
    intro t ht
    rw [aD_div (ne_of_gt ht)]; ring
  have hI : IntegrableOn (fun t : ℝ => aD t / Real.sinh (π * t)) (Ioi 0) :=
    (iP.add iR).congr_fun (fun t ht => (heq t ht).symm) measurableSet_Ioi
  refine ⟨hI, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_add iP iR]
  have e1 : ∫ t in Ioi (0 : ℝ), (1 / 8) * (xA t + vA t) = (1 / 8) * (π - √2) := by
    rw [integral_const_mul, integral_xA_vA_Ioi]
  have e2 : ∫ t in Ioi (0 : ℝ), ((1 / 2) * (π / Real.cosh (π * t)) + π / (1 + Real.cosh (π * t)) -
        2 * (π / √(Real.cosh (π * t) * (1 + Real.cosh (π * t)))) + (5 / 8) * g4 t + (3 / 8) * g5 t) =
      (1 / 2) * (π / 2) + 1 - 2 * (√2 * Real.arsinh 1) + (5 / 8) * (π / 2 - 1) + (3 / 8) * 1 := by
    have j1 : IntegrableOn (fun t : ℝ => (1 / 2) * (π / Real.cosh (π * t))) (Ioi 0) := iS.const_mul _
    have j12 : IntegrableOn (fun t : ℝ => (1 / 2) * (π / Real.cosh (π * t)) + π / (1 + Real.cosh (π * t)))
        (Ioi 0) := j1.add iH
    have j3 : IntegrableOn (fun t : ℝ => 2 * (π / √(Real.cosh (π * t) * (1 + Real.cosh (π * t))))) (Ioi 0) :=
      iQ.const_mul _
    have j123 : IntegrableOn (fun t : ℝ => (1 / 2) * (π / Real.cosh (π * t)) + π / (1 + Real.cosh (π * t)) -
        2 * (π / √(Real.cosh (π * t) * (1 + Real.cosh (π * t))))) (Ioi 0) := j12.sub j3
    have j4 : IntegrableOn (fun t : ℝ => (5 / 8) * g4 t) (Ioi 0) := i4.const_mul _
    have j1234 : IntegrableOn (fun t : ℝ => (1 / 2) * (π / Real.cosh (π * t)) + π / (1 + Real.cosh (π * t)) -
        2 * (π / √(Real.cosh (π * t) * (1 + Real.cosh (π * t)))) + (5 / 8) * g4 t) (Ioi 0) := j123.add j4
    have j5 : IntegrableOn (fun t : ℝ => (3 / 8) * g5 t) (Ioi 0) := i5.const_mul _
    have h1 := integral_add j1234 j5
    have h2 := integral_add j123 j4
    have h3 := integral_sub j12 j3
    have h4 := integral_add j1 iH
    beta_reduce at h1 h2 h3 h4
    rw [h1, h2, h3, h4]
    rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, vS, vH, vQ, v4, v5]
  rw [e1, e2]
  ring

/-- **`g₁ = g1Vir`**: the first odd jet of the Virasoro outer function. -/
theorem g1Out_eq_g1Vir : g1Out = g1Vir := by
  have hpi := Real.pi_pos
  obtain ⟨hint, hval⟩ := aD_integral
  have hslope := hbarA_slope amp_aAmp
  have hibp := slope_ibp amp_aAmp (fun t _ => hasDerivAt_aAmp t) hint
  rw [hibp, hval] at hslope
  rw [g1Out_of_slope hslope]
  unfold g1Vir xiStar
  field_simp
  ring

/-- **The exact minimum of the comb functional with the closed-form constant**:
`min 𝒥 = c₀* = α_tip g₁`. -/
theorem comb_minimum_virasoro_c0Star :
    IsLeast {x : ℝ | ∃ (F : ℂ → ℂ) (c1 : ℝ), HAdm F c1 ∧ combJ Wslit Kedge F = x} c0Star := by
  rw [c0Star_eq_c0StarOf, ← g1Out_eq_g1Vir]
  exact comb_minimum_virasoro

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.g1Out_eq_g1Vir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.g1Out_eq_g1Vir

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.comb_minimum_virasoro_c0Star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.comb_minimum_virasoro_c0Star

end FormalResearch.ModularBootstrap.FiveTerm
