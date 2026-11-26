module

public import FormalResearch.ModularBootstrap.LP.Continuation

/-!
# The exponential tilt `ν = e^{2πt} μ` and the transfer of odd moments to the crossing identity

Shared by `LP.PositiveRay` (`dsl:positive-ray`) and `LP.DerivLimit` (`ds:LP`).  A measure `μ`
on `[0, ∞)` with `∫ e^{ε t} dμ < ∞` and prescribed odd moments `∫ P_k dμ` gives
`ν = e^{2πt} μ`, whose Laplace transform is finite at `s_θ` for `θ` small (`LapFin` of `Cayley`),
and `∫ ψ_k dν = c_k ∫ P_k dμ` (`integral_lagPsi_expTilt`).  Combined with `ds:cay`
(`ds_cay_iff`) the equality of odd moments with a second tilted measure is the crossing identity on
`(s_θ, 1/s_θ)` (`tilt_crossing`); `ds:cont` (`ds_cont`) then spreads it to all `β > 0`.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.LP

/-- `e^{2πt} dμ`. -/
noncomputable def expTilt (μ : Measure ℝ) : Measure ℝ :=
  μ.withDensity (fun s => ENNReal.ofReal (Real.exp (2 * π * s)))

lemma measurable_tiltDensity : Measurable (fun s : ℝ => ENNReal.ofReal (Real.exp (2 * π * s))) :=
  ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun s : ℝ => Real.exp (2 * π * s)).measurable

lemma tiltDensity_lt_top (μ : Measure ℝ) :
    ∀ᵐ s ∂μ, ENNReal.ofReal (Real.exp (2 * π * s)) < ∞ :=
  Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

lemma expTilt_ac (μ : Measure ℝ) : expTilt μ ≪ μ := withDensity_absolutelyContinuous _ _

lemma expTilt_apply_eq_zero {μ : Measure ℝ} {A : Set ℝ} (h : μ A = 0) : expTilt μ A = 0 :=
  expTilt_ac μ h

lemma integral_expTilt (μ : Measure ℝ) (g : ℝ → ℝ) :
    ∫ s, g s ∂expTilt μ = ∫ s, Real.exp (2 * π * s) * g s ∂μ := by
  unfold expTilt
  rw [integral_withDensity_eq_integral_toReal_smul measurable_tiltDensity (tiltDensity_lt_top μ)]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]

lemma integrable_expTilt_iff (μ : Measure ℝ) (g : ℝ → ℝ) :
    Integrable g (expTilt μ) ↔ Integrable (fun s => Real.exp (2 * π * s) * g s) μ := by
  unfold expTilt
  rw [integrable_withDensity_iff_integrable_smul' measurable_tiltDensity (tiltDensity_lt_top μ)]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]

/-- `ψ_k e^{2πt} = L_k(4πt)`, a nonzero multiple of `P_k(t)`. -/
lemma exp_mul_lagPsi (w : ℝ) (k : ℕ) (s : ℝ) :
    Real.exp (2 * π * s) * lagPsi w k s =
      ((4 * π) ^ k / ((-1) ^ k * (k.factorial : ℝ))) * lagP w k s := by
  have hpi := Real.pi_pos
  have hk : ((-1 : ℝ) ^ k * (k.factorial : ℝ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)
  unfold lagPsi
  rw [← mul_assoc, ← Real.exp_add, show 2 * π * s + -2 * π * s = 0 by ring, Real.exp_zero, one_mul,
    lagP_eq]
  have h4 : (4 * π) ^ k ≠ 0 := by positivity
  field_simp

lemma integral_lagPsi_expTilt (w : ℝ) (k : ℕ) (μ : Measure ℝ) :
    ∫ s, lagPsi w k s ∂expTilt μ = ((4 * π) ^ k / ((-1) ^ k * (k.factorial : ℝ))) *
      ∫ s, lagP w k s ∂μ := by
  rw [integral_expTilt]
  simp_rw [exp_mul_lagPsi]
  rw [integral_const_mul]

/-- `∫ Ξ_β dν = Z(β) - β^{-w} Z(1/β)` in terms of `lapZ`. -/
lemma integral_xiW_lapZ {w β : ℝ} {ν : Measure ℝ} (h1 : LapFin ν β) (h2 : LapFin ν (1 / β)) :
    ∫ t, xiW w β t ∂ν = lapZ ν β - β ^ (-w) * lapZ ν (1 / β) := by
  have e : (fun t : ℝ => Real.exp (-2 * π * t / β)) = fun t => Real.exp (-2 * π * (1 / β) * t) := by
    funext t; congr 1; ring
  have h2' : Integrable (fun t : ℝ => Real.exp (-2 * π * t / β)) ν := by rw [e]; exact h2
  rw [integral_xiW h1 h2']
  unfold lapZ
  rw [e]

/-- Finiteness of the tilted Laplace transform at `s_θ`, from an exponential moment. -/
lemma lapFin_expTilt_sTheta {μ : Measure ℝ} (hμ : μ (Iio 0) = 0) {ε θ : ℝ} (hθε : 2 * π * (1 - sTheta θ) ≤ ε)
    (hexp : Integrable (fun s => Real.exp (ε * s)) μ) : LapFin (expTilt μ) (sTheta θ) := by
  have hae : ∀ᵐ t ∂μ, 0 ≤ t := by
    have : ∀ᵐ t ∂μ, t ∉ Iio 0 := measure_eq_zero_iff_ae_notMem.1 hμ
    filter_upwards [this] with t ht using not_lt.1 ht
  unfold LapFin
  rw [integrable_expTilt_iff]
  refine Integrable.mono' hexp (by fun_prop : Continuous fun t : ℝ =>
    Real.exp (2 * π * t) * Real.exp (-2 * π * sTheta θ * t)).aestronglyMeasurable ?_
  filter_upwards [hae] with t ht
  rw [← Real.exp_add, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.2
  nlinarith only [hθε, ht]

/-- **Crossing identity from odd moments** (`ds:cay` through the tilt): if `μ, μ'` are measures on
`[0, ∞)` with exponential moments `e^{ε t}` and `∫ P_k dμ = ∫ P_k dμ'` for all odd `k`, then there is
`θ ∈ (0, 1)` with `LapFin` of both tilts at `s_θ` and `∫ Ξ_β d(e^{2πt}μ) = ∫ Ξ_β d(e^{2πt}μ')` for
`β ∈ (s_θ, 1/s_θ)`. -/
theorem tilt_crossing {w : ℝ} (hw : 0 < w) {μ μ' : Measure ℝ} (hμ : μ (Iio 0) = 0)
    (hμ' : μ' (Iio 0) = 0) {ε : ℝ} (hε : 0 < ε)
    (hexp : Integrable (fun s => Real.exp (ε * s)) μ)
    (hexp' : Integrable (fun s => Real.exp (ε * s)) μ')
    (hodd : ∀ k, Odd k → ∫ s, lagP w k s ∂μ = ∫ s, lagP w k s ∂μ') :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ LapFin (expTilt μ) (sTheta θ) ∧ LapFin (expTilt μ') (sTheta θ) ∧
      ∀ β, sTheta θ < β → β < 1 / sTheta θ →
        ∫ t, xiW w β t ∂expTilt μ = ∫ t, xiW w β t ∂expTilt μ' := by
  have hpi := Real.pi_pos
  set θ : ℝ := min (1 / 2) (ε / (4 * π)) with hθ
  have hθ0 : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθ1 : θ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hθε : 2 * π * (1 - sTheta θ) ≤ ε := by
    have h1 : 1 - sTheta θ = 2 * θ / (1 + θ) := by unfold sTheta; field_simp; ring
    have h2 : 1 - sTheta θ ≤ 2 * θ := by
      rw [h1, div_le_iff₀ (by linarith)]; nlinarith only [hθ0]
    have h3 : θ ≤ ε / (4 * π) := min_le_right _ _
    have h4 : θ * (4 * π) ≤ ε := by rwa [le_div_iff₀ (by positivity)] at h3
    nlinarith only [h2, h4, hpi]
  have hf := lapFin_expTilt_sTheta hμ hθε hexp
  have hf' := lapFin_expTilt_sTheta hμ' hθε hexp'
  refine ⟨θ, hθ0, hθ1, hf, hf', ?_⟩
  have := (ds_cay_iff hw hθ0 hθ1 (expTilt_apply_eq_zero hμ) (expTilt_apply_eq_zero hμ') hf hf').2 ?_
  · exact this
  · intro k hk
    rw [integral_lagPsi_expTilt, integral_lagPsi_expTilt, hodd k hk]

end FormalResearch.ModularBootstrap.LP
