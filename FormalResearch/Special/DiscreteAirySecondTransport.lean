module

public import FormalResearch.Special.LangerHadamard
public import Mathlib

/-!
# Second-order Airy parametrix, part 14: the regular solution of the singular transport equation (Q1, abstract part)

Olver's transport equation for the second-order amplitude `q₁` is `2 W q₁' + W' q₁ = f` with `W` vanishing simply at the turn
`c`.  This module proves the **existence of a `C^m` solution on a ball `B(c, ρ)`** from `W ∈ C^{m+2}`, `f ∈ C^{m+1}`
(`W(c) = 0`, `ω := dslope W c > 0`, `m ≥ 1`), by the explicit formula
`q₁ = ω^{-1/2} u`, `u(q) = F(c) + (q - c) · h(q)`, `h = hadInt (√t/2) (dslope F c) c`, `F = f ω^{-1/2}`, i.e.
`u(q) = ∫₀¹ F(c + t(q-c)) dt/(2√t)` rewritten so that only continuous weights appear (and the existing Hadamard calculus
`LangerHadamard`, `contDiffOn_hadInt`, applies).  The `q₁`-equation is then checked by one fundamental-theorem identity
(`tr_ftc`: `3 h + 2 (q-c) h' = dslope F c`).

**Claim class: proved.**  This is the formalisation of Olver's `B₀`-analysis step of `lem:airy2-olver` (the analytic solution
`B = ∫₀¹ ψ(ζ y²) dy` of `2ζ B_ζ + B = ψ`).  The concrete `W`, `f` of the paper are in `DiscreteAirySecondQ1`.
-/

@[expose] public section

open Set Metric

namespace FormalResearch.Special

/-- **The fundamental-theorem identity** `3 h + 2 (q-c) h' = H(q)` for `h = hadInt (√t/2) H`, `h' = hadInt (t √t/2) H'`. -/
lemma tr_ftc {H : ℝ → ℝ} {c ρ q : ℝ} (hH : ContDiffOn ℝ 1 H (ball c ρ)) (hq : q ∈ ball c ρ) :
    3 * hadInt (fun t => √t / 2) H c q + 2 * (q - c) * hadInt (fun t => t * (√t / 2)) (deriv H) c q = H q := by
  have hK' : ContinuousOn (deriv H) (ball c ρ) := hH.continuousOn_deriv_of_isOpen isOpen_ball le_rfl
  have hKc : ContinuousOn H (ball c ρ) := hH.continuousOn
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, c + t * (q - c) ∈ ball c ρ := fun t ht => hadInt_mem_ball hq ht
  have hcH : ContinuousOn (fun t : ℝ => H (c + t * (q - c))) (Icc 0 1) :=
    hKc.comp (by fun_prop) hmem
  have hcH' : ContinuousOn (fun t : ℝ => deriv H (c + t * (q - c))) (Icc 0 1) :=
    hK'.comp (by fun_prop) hmem
  have hsq : ContinuousOn (fun t : ℝ => √t) (Icc 0 1) := Real.continuous_sqrt.continuousOn
  set φ' : ℝ → ℝ := fun t => 3 / 2 * √t * H (c + t * (q - c)) +
    t * √t * ((q - c) * deriv H (c + t * (q - c))) with hφ'
  have hcφ' : ContinuousOn φ' (Icc 0 1) := by
    refine ContinuousOn.add ((continuousOn_const.mul hsq).mul hcH) ?_
    exact (continuousOn_id.mul hsq).mul (continuousOn_const.mul hcH')
  have hcφ : ContinuousOn (fun t : ℝ => t * √t * H (c + t * (q - c))) (Icc 0 1) :=
    ((continuousOn_id.mul hsq).mul hcH)
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun t : ℝ => t * √t * H (c + t * (q - c))) (φ' t) t := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hHd : DifferentiableAt ℝ H (c + t * (q - c)) :=
      (hH.differentiableOn one_ne_zero).differentiableAt
        (isOpen_ball.mem_nhds (hmem t ⟨ht.1.le, ht.2.le⟩))
    have h1 : HasDerivAt (fun t : ℝ => c + t * (q - c)) (q - c) t := by
      simpa using ((hasDerivAt_id t).mul_const (q - c)).const_add c
    have h2 := hHd.hasDerivAt.comp t h1
    have h3 : HasDerivAt (fun t : ℝ => t * √t) (1 * √t + t * (1 / (2 * √t))) t :=
      (hasDerivAt_id' t).mul (Real.hasDerivAt_sqrt ht0.ne')
    have h4 := h3.mul h2
    refine h4.congr_deriv ?_
    have hs : 0 < √t := Real.sqrt_pos.2 ht0
    simp only [hφ', Function.comp_apply]
    field_simp
    rw [Real.sq_sqrt ht0.le]
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (zero_le_one' ℝ) hcφ hderiv
    (hcφ'.intervalIntegrable_of_Icc zero_le_one)
  have e1 : (1 : ℝ) * √1 * H (c + 1 * (q - c)) = H q := by simp
  have e0 : (0 : ℝ) * √0 * H (c + 0 * (q - c)) = 0 := by simp
  simp only [e1, e0, sub_zero] at hint
  rw [← hint]
  unfold hadInt
  have i1 : IntervalIntegrable (fun t : ℝ => √t / 2 * H (c + t * (q - c))) MeasureTheory.volume 0 1 :=
    (((hsq.div_const 2).mul hcH)).intervalIntegrable_of_Icc zero_le_one
  have i2 : IntervalIntegrable (fun t : ℝ => t * (√t / 2) * deriv H (c + t * (q - c))) MeasureTheory.volume 0 1 :=
    ((((continuousOn_id.mul (hsq.div_const 2))).mul hcH')).intervalIntegrable_of_Icc zero_le_one
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (i1.const_mul 3) (i2.const_mul (2 * (q - c)))]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  simp only [hφ']
  ring

/-- The algebra of the integrating factor `ω^{-1/2}`. -/
lemma tr_alg {s ωv ω' x u u' f : ℝ} (hs : 0 < s) (hωv : s ^ 2 = ωv) (key : s * (2 * x * u' + u) = f) :
    2 * (x * ωv) * (-(ω' / (2 * s)) / s ^ 2 * u + s⁻¹ * u') + (ωv + x * ω') * (s⁻¹ * u) = f := by
  subst hωv
  rw [← key]
  field_simp
  ring

/-- **Q1 (abstract): the regular solution of `2 W q₁' + W' q₁ = f` on a ball around the simple zero `c` of `W`.** -/
theorem transport_regular_solution {c ρ : ℝ} (m : ℕ) (hm : 1 ≤ m) {W f : ℝ → ℝ}
    (hW : ContDiffOn ℝ (m + 2 : ℕ) W (ball c ρ)) (hf : ContDiffOn ℝ (m + 1 : ℕ) f (ball c ρ))
    (hW0 : W c = 0) (hω : ∀ q ∈ ball c ρ, 0 < dslope W c q) :
    ∃ q1 : ℝ → ℝ, ContDiffOn ℝ m q1 (ball c ρ) ∧
      ∀ q ∈ ball c ρ, 2 * W q * deriv q1 q + deriv W q * q1 q = f q := by
  set ω : ℝ → ℝ := dslope W c with hωdef
  have hω1 : ContDiffOn ℝ (m + 1 : ℕ) ω (ball c ρ) := contDiffOn_dslope (m + 1) hW
  have hsq : ContDiffOn ℝ (m + 1 : ℕ) (fun q => √(ω q)) (ball c ρ) := hω1.sqrt (fun q hq => (hω q hq).ne')
  have hS : ContDiffOn ℝ (m + 1 : ℕ) (fun q => (√(ω q))⁻¹) (ball c ρ) :=
    hsq.inv (fun q hq => (Real.sqrt_pos.2 (hω q hq)).ne')
  have hF : ContDiffOn ℝ (m + 1 : ℕ) (fun q => f q * (√(ω q))⁻¹) (ball c ρ) := hf.mul hS
  have hH : ContDiffOn ℝ m (dslope (fun q => f q * (√(ω q))⁻¹) c) (ball c ρ) := contDiffOn_dslope m hF
  have hH1 : ContDiffOn ℝ 1 (dslope (fun q => f q * (√(ω q))⁻¹) c) (ball c ρ) :=
    hH.of_le (by exact_mod_cast hm)
  have hwc : Continuous (fun t : ℝ => √t / 2) := Real.continuous_sqrt.div_const 2
  set H := dslope (fun q => f q * (√(ω q))⁻¹) c with hHdef
  set hh : ℝ → ℝ := hadInt (fun t => √t / 2) H c with hhdef
  have hhC : ContDiffOn ℝ m hh (ball c ρ) := contDiffOn_hadInt m _ H hwc hH
  set u : ℝ → ℝ := fun q => f c * (√(ω c))⁻¹ + (q - c) * hh q with hudef
  have huC : ContDiffOn ℝ m u (ball c ρ) :=
    contDiffOn_const.add ((contDiffOn_id.sub contDiffOn_const).mul hhC)
  refine ⟨fun q => (√(ω q))⁻¹ * u q, ?_, ?_⟩
  · exact (hS.of_le (by exact_mod_cast Nat.le_succ m)).mul huC
  intro q hq
  have hωq := hω q hq
  have hs : 0 < √(ω q) := Real.sqrt_pos.2 hωq
  have hωd : HasDerivAt ω (deriv ω q) q :=
    ((hω1.differentiableOn (by exact_mod_cast Nat.succ_ne_zero m)).differentiableAt
      (isOpen_ball.mem_nhds hq)).hasDerivAt
  have hSd : HasDerivAt (fun q => (√(ω q))⁻¹) (-(deriv ω q / (2 * √(ω q))) / √(ω q) ^ 2) q :=
    (hωd.sqrt hωq.ne').inv hs.ne'
  have hhd : HasDerivAt hh (hadInt (fun t => t * (√t / 2)) (deriv H) c q) q :=
    hasDerivAt_hadInt hwc hH1 hq
  have hud : HasDerivAt u (hh q + (q - c) * hadInt (fun t => t * (√t / 2)) (deriv H) c q) q := by
    have := (((hasDerivAt_id q).sub_const c).mul hhd).const_add (f c * (√(ω c))⁻¹)
    refine this.congr_deriv ?_
    simp
  have hq1d : HasDerivAt (fun q => (√(ω q))⁻¹ * u q) _ q := hSd.mul hud
  -- `W = (q - c) ω`
  have hWeq : ∀ x ∈ ball c ρ, W x = (x - c) * ω x := fun x hx => by
    have := sub_smul_dslope W c x
    rw [hW0, sub_zero, smul_eq_mul] at this
    exact this.symm
  have hWd : HasDerivAt W (ω q + (q - c) * deriv ω q) q := by
    have h1 := ((hasDerivAt_id q).sub_const c).mul hωd
    refine (h1.congr_deriv (by simp)).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds hq] with x hx
    exact hWeq x hx
  -- the `u` identity: `2 (q-c) u' + u = F q`
  have hFq : f q * (√(ω q))⁻¹ = f c * (√(ω c))⁻¹ + (q - c) * H q := by
    have := sub_smul_dslope (fun q => f q * (√(ω q))⁻¹) c q
    rw [smul_eq_mul] at this
    linarith
  have hft := tr_ftc hH1 hq
  have huid : 2 * (q - c) * (hh q + (q - c) * hadInt (fun t => t * (√t / 2)) (deriv H) c q) + u q =
      f q * (√(ω q))⁻¹ := by
    rw [hFq]
    simp only [hudef]
    rw [← hft]
    ring
  rw [hq1d.deriv, hWd.deriv, hWeq q hq]
  have hs2 : √(ω q) ^ 2 = ω q := Real.sq_sqrt hωq.le
  have key : √(ω q) * (2 * (q - c) * (hh q + (q - c) * hadInt (fun t => t * (√t / 2)) (deriv H) c q) + u q) =
      f q := by
    rw [huid]; field_simp
  exact tr_alg hs hs2 key

/-- info: 'FormalResearch.Special.transport_regular_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.transport_regular_solution

end FormalResearch.Special
