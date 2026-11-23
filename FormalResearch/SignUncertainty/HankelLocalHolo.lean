module

public import FormalResearch.SignUncertainty.HankelLocalDensity

/-!
# The local density `(fρ₀)_loc` is entire in `ℓ = log(π² ξ)` (`gt:7.7c` (a))

`hankelLocal c f ℓ = ∫_{|τ|≤1/3} J(σ_* + iτ) dτ`, `σ_* = 1/10`.  Since `J(ℓ, ζ) = J(0, ζ) e^{c ζ ℓ}` with `J(0, ·)`
continuous on the segment, differentiation under the integral gives `Differentiable ℂ (hankelLocal c f)`.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `(fρ₀)_loc` in the variable `ℓ = log(π² ξ)`: `∫_{|τ|≤1/3} J_ξ(1/10 + iτ) dτ`. -/
noncomputable def hankelLocal (c : ℝ) (f : ℝ → ℝ) (ℓ : ℂ) : ℂ :=
  ∫ τ in (-(1 / 3 : ℝ))..(1 / 3), hankelJ c f ℓ (((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)

lemma hankelJ_ell (c : ℝ) (f : ℝ → ℝ) (ℓ ζ : ℂ) :
    hankelJ c f ℓ ζ = hankelJ c f 0 ζ * Complex.exp ((c : ℂ) * ζ * ℓ) := by
  unfold hankelJ hankelLocPhi
  have : Complex.exp ((c : ℂ) * (SSer etaC ζ + ζ * ℓ)) =
      Complex.exp ((c : ℂ) * (SSer etaC ζ + ζ * 0)) * Complex.exp ((c : ℂ) * ζ * ℓ) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [this]; ring

theorem hankelLocal_differentiable {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    Differentiable ℂ (hankelLocal c f) := by
  intro ℓ0
  set z : ℝ → ℂ := fun τ => ((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I with hz
  have hzcont : Continuous z := by fun_prop
  have hzn : ∀ τ ∈ Icc (-(1 / 3 : ℝ)) (1 / 3), ‖z τ‖ < 1 := fun τ hτ =>
    norm_line_lt (σ := 1 / 10) (τ := τ) (by rw [abs_of_pos (by norm_num)]; norm_num) (abs_le.2 hτ)
  have hzU : MapsTo z (Icc (-(1 / 3 : ℝ)) (1 / 3)) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1 ∧ ‖ζ‖ < 1} := by
    intro τ hτ
    refine ⟨by simp [hz], by simp [hz]; norm_num, hzn τ hτ⟩
  have hJcont : ∀ ℓ : ℂ, ContinuousOn (fun τ : ℝ => hankelJ c f ℓ (z τ)) (Icc (-(1 / 3 : ℝ)) (1 / 3)) :=
    fun ℓ => ((hankelJ_differentiableOn hc hf ℓ).continuousOn).comp hzcont.continuousOn hzU
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hJcont 0)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨by norm_num, by norm_num⟩)
  have hmeas : ∀ ℓ : ℂ, AEStronglyMeasurable (fun τ : ℝ => hankelJ c f ℓ (z τ))
      (volume.restrict (Ι (-(1 / 3 : ℝ)) (1 / 3))) := fun ℓ =>
    ((hJcont ℓ).mono (by rw [uIoc_of_le (by norm_num)]; exact Ioc_subset_Icc_self)).aestronglyMeasurable
      (by rw [uIoc_of_le (by norm_num)]; exact measurableSet_Ioc)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := -(1 / 3 : ℝ)) (b := 1 / 3)
    (F := fun (ℓ : ℂ) (τ : ℝ) => hankelJ c f ℓ (z τ))
    (F' := fun (ℓ : ℂ) (τ : ℝ) => hankelJ c f ℓ (z τ) * ((c : ℂ) * z τ))
    (x₀ := ℓ0) (s := Metric.ball ℓ0 1) (bound := fun _ => C * Real.exp (c * (‖ℓ0‖ + 1)) * c)
    (Metric.ball_mem_nhds _ one_pos) (Eventually.of_forall hmeas)
    ((hJcont ℓ0).intervalIntegrable_of_Icc (by norm_num))
    (by
      have hcz : Continuous (fun τ : ℝ => (c : ℂ) * z τ) := continuous_const.mul hzcont
      exact (hmeas ℓ0).mul hcz.aestronglyMeasurable)
    (Eventually.of_forall fun t ht ℓ hℓ => by
      rw [uIoc_of_le (by norm_num)] at ht
      have ht' : t ∈ Icc (-(1 / 3 : ℝ)) (1 / 3) := Ioc_subset_Icc_self ht
      rw [hankelJ_ell, mul_assoc, norm_mul, norm_mul, norm_mul]
      have h1 : ‖hankelJ c f 0 (z t)‖ ≤ C := hC t ht'
      have h2 : ‖z t‖ ≤ 1 := (hzn t ht').le
      have h3 : ‖Complex.exp ((c : ℂ) * z t * ℓ)‖ ≤ Real.exp (c * (‖ℓ0‖ + 1)) := by
        rw [Complex.norm_exp]
        refine Real.exp_le_exp.2 ((Complex.re_le_norm _).trans ?_)
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
        have hℓ' : ‖ℓ‖ ≤ ‖ℓ0‖ + 1 := by
          have := norm_le_insert' ℓ ℓ0
          have := Metric.mem_ball.1 hℓ
          rw [dist_eq_norm] at this
          linarith [norm_sub_rev ℓ ℓ0, norm_le_norm_add_norm_sub' ℓ ℓ0]
        have : ‖z t‖ * ‖ℓ‖ ≤ 1 * (‖ℓ0‖ + 1) := mul_le_mul h2 hℓ' (norm_nonneg _) (by norm_num)
        nlinarith
      have h4 : ‖(c : ℂ)‖ = c := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      rw [h4]
      have h5 : ‖Complex.exp ((c : ℂ) * z t * ℓ)‖ * (c * ‖z t‖) ≤ Real.exp (c * (‖ℓ0‖ + 1)) * c := by
        gcongr
        nlinarith
      calc ‖hankelJ c f 0 (z t)‖ * (‖Complex.exp ((c : ℂ) * z t * ℓ)‖ * (c * ‖z t‖))
          ≤ C * (Real.exp (c * (‖ℓ0‖ + 1)) * c) := by gcongr
        _ = _ := by ring)
    (by exact intervalIntegrable_const)
    (Eventually.of_forall fun t ht ℓ hℓ => by
      rw [show (fun ℓ : ℂ => hankelJ c f ℓ (z t)) = fun ℓ => hankelJ c f 0 (z t) * Complex.exp ((c : ℂ) * z t * ℓ) from
        funext fun ℓ => hankelJ_ell c f ℓ (z t)]
      have h1 : HasDerivAt (fun ℓ : ℂ => Complex.exp ((c : ℂ) * z t * ℓ)) (Complex.exp ((c : ℂ) * z t * ℓ) * ((c : ℂ) * z t)) ℓ := by
        simpa using ((hasDerivAt_id ℓ).const_mul ((c : ℂ) * z t)).cexp
      have := h1.const_mul (hankelJ c f 0 (z t))
      convert this using 1
      rw [hankelJ_ell]; ring)
  exact key.2.differentiableAt

/-- info: 'FormalResearch.SignUncertainty.hankelLocal_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelLocal_differentiable

end FormalResearch.SignUncertainty
