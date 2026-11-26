module

public import FormalResearch.ModularBootstrap.FiveTerm.HalfDiscCauchyEdge
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Cauchy identity on the half-disc (FIVE-0; `ctu:common-functional` (1), contour step)

Source: `CFT/modular_bootstrap/paper/constant_term_universality.tex`, Lemma ctu.2a, proof of (1):
Cauchy's theorem for `(H(z) - 1)/z²` on `Ω` indented around `0, 1, ±i`, divided by `i`, in the variable
`ψ = 2 arctan y`.

`halfDisc_cauchy_identity`: for `H` in the class `CauchyClass H h₁` (holomorphic on `Ω`, real-symmetric,
`H = 1 + h₁ z + O(z²)` at `0`, `|H| = O(|1+z²|^{-(1-ε)})`), with
`B_H(y) := H(iy) + e^{iψ} (2y²/(1+y²)) H(e^{-iψ})` (`e^{iψ} = wPt y`, `ψ = 2 arctan y`),

`∫_0^1 (Re B_H(y) - 1)/y² dy = 1 + (π/2) h₁`,

the integrand being integrable on `(0,1)`.  This is the identity
`-α_tip F'(0) - α_C = α_tip g_1 - α_C ∫ [Re B_H - 1]/y² dy` of the paper (with `h₁ = F'(0) + g_1`,
`α_C π/2 = α_tip`) behind the defect identity `ctu:common-defect`.

Proof: `strip_edge_cauchy` for `Ψ_H` (edge integrals agree), real symmetry to reduce to half lines,
`y = tanh(π τ/4)` to reach `(0,1)`, and the explicit integrals `∫ 2(1-y²)/(1+y²)² = 1`,
`∫ 2/(1+y²) = π/2`.  All results are proved unconditionally.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- `B_H(y) = H(iy) + e^{iψ} (2y²/(1+y²)) H(e^{-iψ})` (`ctu:common-functional`). -/
noncomputable def edgeSum (H : ℂ → ℂ) (y : ℝ) : ℂ :=
  H (Complex.I * (y : ℂ)) +
    wPt y * ((2 * y ^ 2 / (1 + y ^ 2) : ℝ) : ℂ) * H (starRingEnd ℂ (wPt y))

section

variable {H : ℂ → ℂ} {h1 : ℝ}

/-- The slit integrand `Re(H(iy) - 1)/y²`. -/
noncomputable def slitInt (H : ℂ → ℂ) (y : ℝ) : ℝ := (H (Complex.I * (y : ℂ)) - 1).re / y ^ 2

/-- The edge integrand after the substitution (without the `-c - h₁` terms). -/
noncomputable def edgeInt (H : ℂ → ℂ) (h1 : ℝ) (y : ℝ) : ℝ :=
  2 / (1 + y ^ 2) * ((wPt y * H (starRingEnd ℂ (wPt y))).re - (1 - y ^ 2) / (1 + y ^ 2) - h1)

lemma edgeSum_re_sub_one {y : ℝ} (hy : y ≠ 0) :
    ((edgeSum H y).re - 1) / y ^ 2 =
      slitInt H y + edgeInt H h1 y + (2 * ((1 - y ^ 2) / (1 + y ^ 2) + h1)) / (1 + y ^ 2) := by
  have h2 : (1 + y ^ 2 : ℝ) ≠ 0 := by positivity
  have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
  have e1 : (wPt y * ((2 * y ^ 2 / (1 + y ^ 2) : ℝ) : ℂ) * H (starRingEnd ℂ (wPt y))).re =
      2 * y ^ 2 / (1 + y ^ 2) * (wPt y * H (starRingEnd ℂ (wPt y))).re := by
    have : wPt y * ((2 * y ^ 2 / (1 + y ^ 2) : ℝ) : ℂ) * H (starRingEnd ℂ (wPt y)) =
        ((2 * y ^ 2 / (1 + y ^ 2) : ℝ) : ℂ) * (wPt y * H (starRingEnd ℂ (wPt y))) := by ring
    rw [this, Complex.re_ofReal_mul]
  unfold edgeSum slitInt edgeInt
  rw [Complex.add_re, e1]
  simp only [Complex.sub_re, Complex.one_re]
  field_simp
  ring

lemma conj_edge_left (τ : ℝ) : starRingEnd ℂ ((τ : ℂ) * Complex.I) = ((-τ : ℝ) : ℂ) * Complex.I := by
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I]

lemma conj_edge_right (τ : ℝ) :
    starRingEnd ℂ (1 + (τ : ℂ) * Complex.I) = 1 + ((-τ : ℝ) : ℂ) * Complex.I := by
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I]

lemma deriv_factor_nonneg (τ : ℝ) : 0 ≤ π / 4 * (1 - Real.tanh (π * τ / 4) ^ 2) := by
  have := Real.tanh_lt_one (π * τ / 4)
  have := Real.neg_one_lt_tanh (π * τ / 4)
  have := Real.pi_pos
  have h3 : 0 ≤ 1 - Real.tanh (π * τ / 4) ^ 2 := by nlinarith
  positivity

lemma integral_edge_explicit :
    ∫ y in Ioo (0 : ℝ) 1, 2 * ((1 - y ^ 2) / (1 + y ^ 2)) / (1 + y ^ 2) = 1 := by
  have hcont : Continuous fun y : ℝ => 2 * ((1 - y ^ 2) / (1 + y ^ 2)) / (1 + y ^ 2) := by
    have h1 : Continuous fun y : ℝ => (1 - y ^ 2) / (1 + y ^ 2) :=
      Continuous.div (by fun_prop) (by fun_prop) (fun y => by positivity)
    exact Continuous.div (continuous_const.mul h1) (by fun_prop) (fun y => by positivity)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => 2 * y / (1 + y ^ 2))
    (fun y _ => ?_) (hcont.intervalIntegrable _ _)]
  · norm_num
  · have h : (1 + y ^ 2 : ℝ) ≠ 0 := by positivity
    have := ((hasDerivAt_id y).const_mul (2 : ℝ)).div ((hasDerivAt_pow 2 y).const_add 1) h
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring

lemma integral_one_div_explicit : ∫ y in Ioo (0 : ℝ) 1, 2 / (1 + y ^ 2) = π / 2 := by
  have hcont : Continuous fun y : ℝ => 2 / (1 + y ^ 2) := by
    refine Continuous.div (by fun_prop) (by fun_prop) (fun y => by positivity)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have : ∀ y : ℝ, 2 / (1 + y ^ 2) = 2 * (1 / (1 + y ^ 2)) := fun y => by ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, integral_one_div_one_add_sq]
  simp [Real.arctan_one]
  ring

/-- **The Cauchy identity on the half-disc.**  For `H` in the Cauchy class, the function
`(Re B_H(y) - 1)/y²` is integrable on `(0,1)` and `∫_0^1 (Re B_H - 1)/y² dy = 1 + (π/2) h₁`. -/
theorem halfDisc_cauchy_identity (hH : CauchyClass H h1) :
    IntegrableOn (fun y : ℝ => ((edgeSum H y).re - 1) / y ^ 2) (Ioo (0 : ℝ) 1) ∧
    ∫ y in Ioo (0 : ℝ) 1, ((edgeSum H y).re - 1) / y ^ 2 = 1 + π / 2 * h1 := by
  obtain ⟨K, ε', hε', hb⟩ := cauchyPsi_decay hH
  obtain ⟨IL, IR, heq⟩ := strip_edge_cauchy (cauchyPsi_differentiableOn hH) hε'
    (cauchyPsi_continuousOn hH) hb
  set gL : ℝ → ℂ := fun τ => cauchyPsi H h1 ((τ : ℂ) * Complex.I) with hgL
  set gR : ℝ → ℂ := fun τ => cauchyPsi H h1 (1 + (τ : ℂ) * Complex.I) with hgR
  have hsymL : ∀ τ : ℝ, 0 < τ → gL (-τ) = starRingEnd ℂ (gL τ) := by
    intro τ hτ
    have := cauchyPsi_conj hH (edge_left_mem hτ.ne')
    rw [conj_edge_left] at this
    exact this
  have hsymR : ∀ τ : ℝ, 0 < τ → gR (-τ) = starRingEnd ℂ (gR τ) := by
    intro τ hτ
    have := cauchyPsi_conj hH (edge_right_mem hτ.ne')
    rw [conj_edge_right] at this
    exact this
  have E1 := integral_eq_two_re IL hsymL
  have E2 := integral_eq_two_re IR hsymR
  have hab : ∫ τ in Ioi (0 : ℝ), (gL τ).re = ∫ τ in Ioi (0 : ℝ), (gR τ).re := by
    have h := heq
    simp only [hgL, hgR] at E1 E2
    rw [E1, E2] at h
    have := Complex.ofReal_injective h
    linarith
  -- left edge
  have aL : ∀ τ ∈ Ioi (0 : ℝ), (gL τ).re =
      -(π / 4 * (1 - Real.tanh (π * τ / 4) ^ 2) * slitInt H (Real.tanh (π * τ / 4))) := by
    intro τ _
    simp only [hgL]
    rw [re_cauchyPsi_left]
    unfold slitInt
    simp only [Complex.sub_re, Complex.one_re]
    rw [div_neg]
    ring
  have IL' : IntegrableOn (fun τ : ℝ => π / 4 * (1 - Real.tanh (π * τ / 4) ^ 2) *
      slitInt H (Real.tanh (π * τ / 4))) (Ioi (0 : ℝ)) := by
    have h1 : IntegrableOn (fun τ : ℝ => (gL τ).re) (Ioi (0 : ℝ)) := IL.re.integrableOn
    have h2 := h1.neg
    refine h2.congr_fun (fun τ hτ => ?_) measurableSet_Ioi
    simp only [Pi.neg_apply]
    rw [aL τ hτ, neg_neg]
  have hLint : IntegrableOn (slitInt H) (Ioo (0 : ℝ) 1) := (integrableOn_Ioo_iff_Ioi _).2 IL'
  have hLval : ∫ τ in Ioi (0 : ℝ), (gL τ).re = -∫ y in Ioo (0 : ℝ) 1, slitInt H y := by
    rw [integral_Ioo_eq_Ioi, ← integral_neg]
    exact setIntegral_congr_fun measurableSet_Ioi (fun τ hτ => aL τ hτ)
  -- right edge
  have aR : ∀ τ ∈ Ioi (0 : ℝ), (gR τ).re =
      π / 4 * (1 - Real.tanh (π * τ / 4) ^ 2) * edgeInt H h1 (Real.tanh (π * τ / 4)) := by
    intro τ hτ
    simp only [hgR]
    rw [re_cauchyPsi_right, re_conj_mul_eq hH (ne_of_gt hτ)]
    unfold edgeInt
    ring
  have IR' : IntegrableOn (fun τ : ℝ => π / 4 * (1 - Real.tanh (π * τ / 4) ^ 2) *
      edgeInt H h1 (Real.tanh (π * τ / 4))) (Ioi (0 : ℝ)) := by
    have h1' : IntegrableOn (fun τ : ℝ => (gR τ).re) (Ioi (0 : ℝ)) := IR.re.integrableOn
    exact h1'.congr_fun (fun τ hτ => aR τ hτ) measurableSet_Ioi
  have hRint : IntegrableOn (edgeInt H h1) (Ioo (0 : ℝ) 1) := (integrableOn_Ioo_iff_Ioi _).2 IR'
  have hRval : ∫ τ in Ioi (0 : ℝ), (gR τ).re = ∫ y in Ioo (0 : ℝ) 1, edgeInt H h1 y := by
    rw [integral_Ioo_eq_Ioi]
    exact setIntegral_congr_fun measurableSet_Ioi (fun τ hτ => aR τ hτ)
  have hzero : (∫ y in Ioo (0 : ℝ) 1, slitInt H y) + ∫ y in Ioo (0 : ℝ) 1, edgeInt H h1 y = 0 := by
    have : -∫ y in Ioo (0 : ℝ) 1, slitInt H y = ∫ y in Ioo (0 : ℝ) 1, edgeInt H h1 y := by
      rw [← hLval, ← hRval]; exact hab
    linarith
  -- the explicit remainder
  set e : ℝ → ℝ := fun y => 2 * ((1 - y ^ 2) / (1 + y ^ 2)) / (1 + y ^ 2) + h1 * (2 / (1 + y ^ 2)) with he
  have he_cont : Continuous e := by
    have h1' : Continuous fun y : ℝ => (1 - y ^ 2) / (1 + y ^ 2) :=
      Continuous.div (by fun_prop) (by fun_prop) (fun y => by positivity)
    refine Continuous.add (Continuous.div (continuous_const.mul h1') (by fun_prop) (fun y => by positivity)) ?_
    exact continuous_const.mul (Continuous.div (by fun_prop) (by fun_prop) (fun y => by positivity))
  have he_int : IntegrableOn e (Ioo (0 : ℝ) 1) :=
    he_cont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have he_val : ∫ y in Ioo (0 : ℝ) 1, e y = 1 + π / 2 * h1 := by
    have i1 : IntegrableOn (fun y : ℝ => 2 * ((1 - y ^ 2) / (1 + y ^ 2)) / (1 + y ^ 2)) (Ioo (0 : ℝ) 1) := by
      refine (Continuous.integrableOn_Icc ?_).mono_set Ioo_subset_Icc_self
      have h1' : Continuous fun y : ℝ => (1 - y ^ 2) / (1 + y ^ 2) :=
        Continuous.div (by fun_prop) (by fun_prop) (fun y => by positivity)
      exact Continuous.div (continuous_const.mul h1') (by fun_prop) (fun y => by positivity)
    have i2 : IntegrableOn (fun y : ℝ => h1 * (2 / (1 + y ^ 2))) (Ioo (0 : ℝ) 1) := by
      refine (Continuous.integrableOn_Icc ?_).mono_set Ioo_subset_Icc_self
      exact continuous_const.mul (Continuous.div (by fun_prop) (by fun_prop) (fun y => by positivity))
    rw [he, integral_add i1 i2, integral_edge_explicit, integral_const_mul, integral_one_div_explicit]
    ring
  have hpt : ∀ y ∈ Ioo (0 : ℝ) 1, ((edgeSum H y).re - 1) / y ^ 2 = slitInt H y + edgeInt H h1 y + e y := by
    intro y hy
    rw [edgeSum_re_sub_one (h1 := h1) hy.1.ne', he]
    ring
  have hint : IntegrableOn (fun y : ℝ => ((edgeSum H y).re - 1) / y ^ 2) (Ioo (0 : ℝ) 1) := by
    have := (hLint.add hRint).add he_int
    exact this.congr_fun (fun y hy => (hpt y hy).symm) measurableSet_Ioo
  refine ⟨hint, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioo (fun y hy => hpt y hy),
    integral_add (f := fun y => slitInt H y + edgeInt H h1 y) (g := e) (hLint.add hRint) he_int,
    integral_add (f := slitInt H) (g := edgeInt H h1) hLint hRint, hzero, he_val]
  ring

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.halfDisc_cauchy_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.halfDisc_cauchy_identity
