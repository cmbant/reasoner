module

public import FormalResearch.SignUncertainty.HankelLangerPsiReal

/-!
# Pointwise transport `(b)` of `gt:7.7p`

For real `ũ = x` in the Langer disc, `ξ(x) = (1 + Re w)/π²` with `w = y⁻¹(x/K)`, `K = c^{2/3} κ`, and
`ξ'(x) = Re (dw/dy) / (π² K)`.  For `c ≥ 5000` and the normalised `f`:
`|Ψ̃(x) + c ξ'(x) (ρ₀ f)(cξ(x))| ≤ 2 I₀ c^{1/3} e^{-c/40000} =: r_∞` (`hankel_transport_pointwise`), from the split
`(ρ₀ f)(cξ) = (2πξ)⁻¹((fρ₀)_loc + tail)` and the tail bound `(T)`.  Lean exponent versus paper: `1/40000`
(`2·10⁻³` in the paper); only positivity of the exponent is used downstream.
-/

@[expose] public section

open Complex Set Filter Topology Metric
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `K = c^{2/3} κ`, the scale between `ũ` and `y`. -/
noncomputable def langerScale (c : ℝ) : ℝ := c ^ (2 / 3 : ℝ) * langerKappa

lemma langerScale_pos {c : ℝ} (hc : 0 < c) : 0 < langerScale c :=
  mul_pos (Real.rpow_pos_of_pos hc _) langerKappa_pos

/-- `ξ(ũ)` for real `ũ`. -/
noncomputable def hankelXi (c x : ℝ) : ℝ :=
  (1 + (chartYinv etaC (((x / langerScale c : ℝ)) : ℂ)).re) / π ^ 2

/-- `ξ'(ũ)` for real `ũ`. -/
noncomputable def hankelXiD (c x : ℝ) : ℝ :=
  (deriv (chartYinv etaC) (((x / langerScale c : ℝ)) : ℂ)).re / (π ^ 2 * langerScale c)

/-- The real chart value `w = y⁻¹(x/K)` is real with `|w| ≤ 5·10⁻⁴`. -/
lemma chartYinv_real_point {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : |x| ≤ langerScale c * 4.94e-4) :
    chartYinv etaC (((x / langerScale c : ℝ)) : ℂ) = (((chartYinv etaC (((x / langerScale c : ℝ)) : ℂ)).re : ℝ) : ℂ) ∧
      |(chartYinv etaC (((x / langerScale c : ℝ)) : ℂ)).re| ≤ 5e-4 := by
  have hK0 := langerScale_pos hc
  set yr : ℝ := x / langerScale c with hyr
  have hyr_le : |yr| ≤ 4.94e-4 := by
    rw [hyr, abs_div, abs_of_pos hK0, div_le_iff₀ hK0]; linarith
  have hyn : ‖(yr : ℂ)‖ ≤ 4.94e-4 := by simpa using hyr_le
  have hw := chartYinv_conj langerEta_etaC (y := (yr : ℂ)) (hyn.trans (by norm_num))
  rw [Complex.conj_ofReal] at hw
  set w := chartYinv etaC (yr : ℂ) with hwdef
  have hwim : w.im = 0 := by
    have := congrArg Complex.im hw
    simp at this; linarith
  refine ⟨Complex.ext (by simp) (by simp [hwim]), ?_⟩
  have hwn := norm_chartYinv_le langerEta_etaC hyn
  have := Complex.abs_re_le_norm w
  linarith

lemma langer_pref_le {c : ℝ} (hc : 0 < c) : c ^ (1 / 3 : ℝ) / (2 * π * langerKappa) ≤ c ^ (1 / 3 : ℝ) * 0.27 := by
  have hmu := langerMu_sq_ge
  have : 1 / (2 * π * langerKappa) ≤ 0.27 := by
    unfold langerKappa
    have hpi := Real.pi_pos
    have e : 1 / (2 * π * (12 * langerMu ^ 2 / π ^ 2)) = π / (24 * langerMu ^ 2) := by field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_lt_d2]
  have hk0 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  calc c ^ (1 / 3 : ℝ) / (2 * π * langerKappa) = c ^ (1 / 3 : ℝ) * (1 / (2 * π * langerKappa)) := by ring
    _ ≤ _ := by gcongr

lemma langer_pref_eq {c : ℝ} (hc : 0 < c) :
    c ^ (1 / 3 : ℝ) / (2 * π * langerKappa) = c / (2 * π * langerScale c) := by
  unfold langerScale
  have h1 : c = c ^ (1 / 3 : ℝ) * c ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_add hc]; norm_num
  have hκ := langerKappa_pos
  have hc2 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (-(2 * π * langerKappa)) * h1

theorem hankel_transport_pointwise {c ε : ℝ} (hc : 5000 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) {x : ℝ}
    (hx : |x| ≤ langerScale c * 4.94e-4) :
    |(hankelPsi c f (x : ℂ)).re + c * hankelXiD c x * (hankelRho0 c (c * hankelXi c x) * f (c * hankelXi c x))| ≤
      2 * hankelTailI0 * c ^ (1 / 3 : ℝ) * Real.exp (-(c / 40000)) := by
  have hc0 : 0 < c := by linarith
  have hK0 := langerScale_pos hc0
  obtain ⟨hwc, hwre⟩ := chartYinv_real_point hc0 hx
  set yr : ℝ := x / langerScale c with hyr
  have hyr_le : |yr| ≤ 4.94e-4 := by
    rw [hyr, abs_div, abs_of_pos hK0, div_le_iff₀ hK0]; linarith
  have hyn : ‖(yr : ℂ)‖ ≤ 4.94e-4 := by simpa using hyr_le
  set wr : ℝ := (chartYinv etaC (yr : ℂ)).re with hwr
  have h1pos : 0 < 1 + wr := by linarith [abs_le.1 hwre]
  set ξ : ℝ := hankelXi c x with hξdef
  have hξ : ξ = (1 + wr) / π ^ 2 := rfl
  have hξpos : 0 < ξ := by rw [hξ]; positivity
  have hpiξ : π ^ 2 * ξ = 1 + wr := by rw [hξ]; field_simp
  have hℓ : hankelEll ξ = Complex.log (1 + (wr : ℂ)) := by
    unfold hankelEll
    congr 1
    have : ((π : ℂ) ^ 2 * (ξ : ℂ)) = ((π ^ 2 * ξ : ℝ) : ℂ) := by push_cast; ring
    rw [this, hpiξ]; push_cast; ring
  have hsplit := hankel_rho0_split hc hf hε hM hξpos
  have htail := hankel_tail_le hc hf hε hM hξpos (by
    rw [hpiξ]
    have := Real.log_le_sub_one_of_pos h1pos
    linarith [abs_le.1 hwre])
  -- the derivative is real
  set D := deriv (chartYinv etaC) (yr : ℂ) with hD
  have hDc : starRingEnd ℂ D = D := deriv_chartYinv_real hyr_le
  have hDre : D = ((D.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
    have := congrArg Complex.im hDc
    simp at this; linarith
  have hDn := norm_deriv_chartYinv_le hyn
  -- Ψ in the real chart
  have hK : langerScale c = c ^ (2 / 3 : ℝ) * langerKappa := rfl
  have hΨ : hankelPsi c f (x : ℂ) = -(((c / (2 * π * langerScale c) : ℝ)) : ℂ) * D / (1 + (wr : ℂ)) *
      hankelLocal c f (Complex.log (1 + (wr : ℂ))) := by
    show hankelPsiY c f ((x : ℂ) / ((c ^ (2 / 3 : ℝ) * langerKappa : ℝ) : ℂ)) = _
    have hyc : (x : ℂ) / ((c ^ (2 / 3 : ℝ) * langerKappa : ℝ) : ℂ) = (yr : ℂ) := by
      rw [hyr, ← hK]; push_cast; rfl
    rw [hyc]
    unfold hankelPsiY
    rw [langer_pref_eq hc0, hwc]
  have hΨim : (hankelPsi c f (x : ℂ)).im = 0 := by
    have := hankelPsi_real hc0 f (x := x) (by rw [← hK]; exact hx)
    exact this
  -- the combination
  have hcomb : (hankelPsi c f (x : ℂ)) + (((c * hankelXiD c x * (hankelRho0 c (c * ξ) * f (c * ξ)) : ℝ)) : ℂ) =
      (((c / (2 * π * langerScale c) : ℝ)) : ℂ) * D / (1 + (wr : ℂ)) * hankelTail c f ξ := by
    have e1 : (((c * hankelXiD c x * (hankelRho0 c (c * ξ) * f (c * ξ)) : ℝ)) : ℂ) =
        (c : ℂ) * (((hankelXiD c x : ℝ)) : ℂ) * (((hankelRho0 c (c * ξ) * f (c * ξ) : ℝ)) : ℂ) := by push_cast; ring
    rw [e1, hsplit, hΨ, hℓ]
    have hXD : (((hankelXiD c x : ℝ)) : ℂ) = D / (((π ^ 2 * langerScale c : ℝ)) : ℂ) := by
      unfold hankelXiD
      rw [← hyr, ← hD]
      conv_rhs => rw [hDre]
      push_cast; ring
    rw [hXD, hξ]
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hK0c : (langerScale c : ℂ) ≠ 0 := by exact_mod_cast hK0.ne'
    have h1w : (1 + (wr : ℂ)) ≠ 0 := by exact_mod_cast h1pos.ne'
    push_cast
    field_simp
    ring
  have hI0 : 0 ≤ hankelTailI0 := by
    unfold hankelTailI0; exact MeasureTheory.integral_nonneg fun τ => by positivity
  have hP0 : 0 ≤ c / (2 * π * langerScale c) := by positivity
  have hPle : c / (2 * π * langerScale c) ≤ c ^ (1 / 3 : ℝ) * 0.27 := by
    rw [← langer_pref_eq hc0]; exact langer_pref_le hc0
  have hre : (hankelPsi c f (x : ℂ)).re + c * hankelXiD c x * (hankelRho0 c (c * ξ) * f (c * ξ)) =
      ((hankelPsi c f (x : ℂ)) + (((c * hankelXiD c x * (hankelRho0 c (c * ξ) * f (c * ξ)) : ℝ)) : ℂ)).re := by
    simp
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [hcomb, norm_mul, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hP0]
  have h1w : 0.9995 ≤ ‖1 + (wr : ℂ)‖ := by
    have : ‖1 + (wr : ℂ)‖ = 1 + wr := by
      rw [show (1 + (wr : ℂ)) = ((1 + wr : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos h1pos]
    rw [this]; linarith [abs_le.1 hwre]
  have hk0 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hD0 := norm_nonneg D
  have ht0 := norm_nonneg (hankelTail c f ξ)
  calc c / (2 * π * langerScale c) * ‖D‖ / ‖1 + (wr : ℂ)‖ * ‖hankelTail c f ξ‖
      ≤ (c ^ (1 / 3 : ℝ) * 0.27) * (1 / 0.996) / 0.9995 *
        (6 * hankelTailI0 * Real.exp (-(c / 40000))) := by
        gcongr
    _ ≤ 2 * hankelTailI0 * c ^ (1 / 3 : ℝ) * Real.exp (-(c / 40000)) := by
        have he : 0 ≤ Real.exp (-(c / 40000)) := (Real.exp_pos _).le
        have : (0.27 * (1 / 0.996) / 0.9995 * 6 : ℝ) ≤ 2 := by norm_num
        have hp := mul_nonneg (mul_nonneg hI0 hk0.le) he
        have e1 : (c ^ (1 / 3 : ℝ) * 0.27) * (1 / 0.996) / 0.9995 * (6 * hankelTailI0 * Real.exp (-(c / 40000))) =
            (0.27 * (1 / 0.996) / 0.9995 * 6 : ℝ) * (hankelTailI0 * c ^ (1 / 3 : ℝ) * Real.exp (-(c / 40000))) := by ring
        rw [e1]
        nlinarith [hp]

/-- info: 'FormalResearch.SignUncertainty.hankel_transport_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_transport_pointwise

end FormalResearch.SignUncertainty
