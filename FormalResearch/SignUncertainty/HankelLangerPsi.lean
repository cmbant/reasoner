module

public import FormalResearch.SignUncertainty.HankelChartInverse
public import FormalResearch.SignUncertainty.HankelLocalEnvelope
public import FormalResearch.SignUncertainty.HankelTail
public import FormalResearch.SignUncertainty.RadialRigidity

/-!
# The Langer-disc density `Ψ̃` (`gt:7.7c` (a), (c); `gt:7.7p` (a))

`ũ = c^{2/3} κ y`, `κ = 12μ²/π² = β₁/π²` (`langerKappa`, `hankelBeta1_eq`), `y = y(w)`, `w = π²ξ - 1`
(`chartYinv`).  `Ψ̃(ũ) = -c ξ'(ũ) (fρ₀)_loc(cξ(ũ))` with `(fρ₀)_loc(cξ) = (2πξ)⁻¹ hankelLocal c f (log π²ξ)`.

Lean disc versus the paper: the chart disc is `‖y‖ ≤ ρ_y := 4.94·10⁻⁴` (the paper's `|ũ| ≤ A_c²` is `‖y‖ ≤ w₀/2 =
π² r₀ / 2 ≤ 4.935·10⁻⁴`), so `R_dom(c) = c^{2/3} κ ρ_y`; only `R_dom → ∞` is used downstream.
-/

@[expose] public section

open Complex Set Filter Topology Metric
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `κ = 12 μ² / π² = (3/π²)^{1/3}`. -/
noncomputable def langerKappa : ℝ := 12 * langerMu ^ 2 / π ^ 2

lemma langerKappa_pos : 0 < langerKappa := by
  unfold langerKappa; have := langerMu_pos; positivity

lemma hankelBeta1_eq : hankelBeta1 = 12 * langerMu ^ 2 := by
  have h3 : hankelBeta1 ^ 3 = (12 * langerMu ^ 2) ^ 3 := by
    have e1 : hankelBeta1 ^ 3 = (π ^ 2 * √3) ^ 2 := by
      unfold hankelBeta1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [e1]
    have e2 : (12 * langerMu ^ 2) ^ 3 = 1728 * (langerMu ^ 3) ^ 2 := by ring
    rw [e2, langerMu_cube]
    have : (√3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    rw [mul_pow, this]; ring
  exact (pow_left_inj₀ hankelBeta1_pos.le (by have := langerMu_pos; positivity) (by norm_num)).1 h3

lemma hankelBeta1_eq_kappa : hankelBeta1 = langerKappa * π ^ 2 := by
  rw [hankelBeta1_eq]; unfold langerKappa; field_simp

/-- Saddle data at a chart point `y`: the point `u` with `ũ(u) = c^{2/3} κ y`, `ζ_+ = u^{1/2}`,
`-g(ζ_+) = log π²ξ`, `1 + w = π² ξ`, off the cut. -/
lemma chart_saddle_data {η : ℕ → ℝ} (h : LangerEta η) {c : ℝ} (hc : 0 < c) {y : ℂ} (hy : ‖y‖ ≤ 4.94e-4)
    (hcut : ¬ ((((c ^ (2 / 3 : ℝ) * langerKappa : ℝ) : ℂ) * y).im = 0 ∧
      (((c ^ (2 / 3 : ℝ) * langerKappa : ℝ) : ℂ) * y).re ≤ 0)) :
    ∃ u : ℂ, u ∈ slitPlane ∧ ‖u‖ ≤ 0.035 ^ 2 ∧
      langerUtilde η c u = ((c ^ (2 / 3 : ℝ) * langerKappa : ℝ) : ℂ) * y ∧
      -(gSer η (saddleRoot u)) = Complex.log (1 + chartYinv η y) := by
  obtain ⟨hw, hY⟩ := chartYinv_spec η (exists_chartY_small h hy)
  have hwn : ‖chartYinv η y‖ ≤ 1e-3 := (mem_ball_zero_iff.1 hw).le
  set w := chartYinv η y with hwdef
  have hv := chartVofW_mem hwn
  obtain ⟨hu, hK⟩ := chartKinv_spec h hv
  set u := chartKinv η (chartVofW w) with hudef
  have hun : ‖u‖ ≤ 0.035 ^ 2 := (mem_ball_zero_iff.1 hu).le
  have hyM : ((π ^ 2 / 12 : ℝ) : ℂ) * chartM η u = y := by
    rw [← hY]; unfold chartY chartXi; rfl
  have hM : chartM η u = ((12 / π ^ 2 : ℝ) : ℂ) * y := by
    rw [← hyM, ← mul_assoc]
    have : ((12 / π ^ 2 : ℝ) : ℂ) * ((π ^ 2 / 12 : ℝ) : ℂ) = 1 := by
      have : (π : ℝ) ≠ 0 := Real.pi_ne_zero
      rw [← Complex.ofReal_mul]; field_simp; simp
    rw [this, one_mul]
  refine ⟨u, ?_, hun, ?_, ?_⟩
  · by_contra hns
    rw [Complex.mem_slitPlane_iff] at hns
    push Not at hns
    obtain ⟨hre, him⟩ := hns
    apply hcut
    have hconj : (starRingEnd ℂ) u = u := by
      apply Complex.ext <;> simp [him]
    have hMr := chartM_conj h hun
    rw [hconj] at hMr
    have hMim : (chartM η u).im = 0 := by
      have := congrArg Complex.im hMr
      simp at this; linarith
    have hx := norm_psW_aE_sub_one_u h hun
    have hG : ‖(1 + (psW (aE η) u - 1)) ^ ((2 / 3 : ℝ) : ℂ) - 1‖ ≤ 2 / 3 * 8.95e-4 / (1 - 8.95e-4) :=
      norm_one_add_cpow_sub_one_le (α := 2 / 3) (by norm_num) (by norm_num) (hx.trans (by norm_num)) (by norm_num)
    have hGre : 0 < ((psW (aE η) u) ^ ((2 / 3 : ℝ) : ℂ)).re := by
      have e : (1 + (psW (aE η) u - 1)) = psW (aE η) u := by ring
      rw [e] at hG
      have h1 := Complex.abs_re_le_norm (psW (aE η) u ^ ((2 / 3 : ℝ) : ℂ) - 1)
      have h2 := abs_le.1 (h1.trans (hG.trans (by norm_num : (2 / 3 * 8.95e-4 / (1 - 8.95e-4) : ℝ) ≤ 1 / 2)))
      simp only [Complex.sub_re, Complex.one_re] at h2
      linarith [h2.1]
    have hMre : (chartM η u).re ≤ 0 := by
      have e : chartM η u = u * (psW (aE η) u) ^ ((2 / 3 : ℝ) : ℂ) := rfl
      rw [e, Complex.mul_re, him]
      simp only [zero_mul, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg hre hGre.le
    have hyim : y.im = 0 := by
      rw [← hyM, Complex.im_ofReal_mul, hMim, mul_zero]
    have hyre : y.re ≤ 0 := by
      have := congrArg Complex.re hyM
      rw [Complex.re_ofReal_mul] at this
      rw [← this]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hMre
    refine ⟨?_, ?_⟩
    · rw [Complex.im_ofReal_mul, hyim, mul_zero]
    · rw [Complex.re_ofReal_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (Real.rpow_nonneg hc.le _) langerKappa_pos.le) hyre
  · unfold langerUtilde
    rw [hM, ← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    unfold langerKappa
    have : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    field_simp
  · rw [gSer_eq_chartK, saddleRoot_sq, hK]
    unfold chartVofW
    rw [← mul_assoc]
    have : ((π ^ 2 / 12 : ℝ) : ℂ) * ((12 / π ^ 2 : ℝ) : ℂ) = 1 := by
      have : (π : ℝ) ≠ 0 := Real.pi_ne_zero
      rw [← Complex.ofReal_mul]; field_simp; simp
    rw [this]; ring

lemma langerMu_sq_ge : 1 / 2 ≤ langerMu ^ 2 := by
  by_contra hlt
  push Not at hlt
  have h3 : (langerMu ^ 2) ^ 3 < (1 / 2) ^ 3 :=
    pow_lt_pow_left₀ hlt (by have := langerMu_pos; positivity) (by norm_num)
  have e : (langerMu ^ 2) ^ 3 = (π ^ 2 / 24) ^ 2 := by rw [← langerMu_cube]; ring
  rw [e] at h3
  have : (9 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
  nlinarith

/-- `ξ' ` in the `y`-variable: `Ψ̃` as a function of `y = ũ/(c^{2/3} κ)`:
`Ψ̃ = -(c^{1/3}/(2πκ)) (dw/dy)/(1+w) · hankelLocal c f (log(1+w))`, `w = y⁻¹(y)`. -/
noncomputable def hankelPsiY (c : ℝ) (f : ℝ → ℝ) (y : ℂ) : ℂ :=
  -((c ^ (1 / 3 : ℝ) / (2 * π * langerKappa) : ℝ) : ℂ) * deriv (chartYinv etaC) y /
    (1 + chartYinv etaC y) * hankelLocal c f (Complex.log (1 + chartYinv etaC y))

/-- The Langer-disc density `Ψ̃(ũ) = -c ξ'(ũ) (fρ₀)_loc(cξ(ũ))`. -/
noncomputable def hankelPsi (c : ℝ) (f : ℝ → ℝ) (u : ℂ) : ℂ :=
  hankelPsiY c f (u / ((c ^ (2 / 3 : ℝ) * langerKappa : ℝ) : ℂ))

lemma norm_deriv_chartYinv_le {y : ℂ} (hy : ‖y‖ ≤ 4.94e-4) :
    ‖deriv (chartYinv etaC) y‖ ≤ 1 / 0.996 := by
  obtain ⟨hw, hY⟩ := chartYinv_spec etaC (exists_chartY_small langerEta_etaC hy)
  have hd := (analyticAt_chartYinv langerEta_etaC (mem_ball_zero_iff.1 hw)).2
  rw [hY] at hd
  rw [hd.deriv, norm_inv]
  have h4 := norm_chartYD_add_one_le langerEta_etaC (mem_ball_zero_iff.1 hw).le
  have : 0.996 ≤ ‖chartYD etaC (chartYinv etaC y)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(chartYD etaC (chartYinv etaC y) + 1) + 1 + (-1))
    have h5 := norm_sub_norm_le (chartYD etaC (chartYinv etaC y) + 1) (1 : ℂ)
    have e : ‖chartYD etaC (chartYinv etaC y) + 1‖ ≤ 4e-3 := h4
    have h6 := norm_add_le (chartYD etaC (chartYinv etaC y)) 1
    have h7 : (1 : ℝ) ≤ ‖chartYD etaC (chartYinv etaC y)‖ + 4e-3 := by
      have := norm_sub_norm_le (1 : ℂ) (-(chartYD etaC (chartYinv etaC y)))
      rw [norm_neg, norm_one] at this
      have e2 : (1 : ℂ) - -(chartYD etaC (chartYinv etaC y)) = chartYD etaC (chartYinv etaC y) + 1 := by ring
      rw [e2] at this; linarith
    linarith
  rw [one_div]
  exact inv_anti₀ (by norm_num) this

/-- **Envelope `(e71)` for `Ψ̃`** (`gt:7.7c` (c), `gt:7.7p` (a)), for the normalised `f` and `c ≥ 2`, on the
disc `‖ũ‖ ≤ c^{2/3} κ · 4.94·10⁻⁴` off the cut.  Absolute constant `60` (paper: `C₀`). -/
theorem hankelPsi_envelope {c ε : ℝ} (hc : 2 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) {u : ℂ}
    (hu : ‖u‖ ≤ c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4) (hcut : ¬ (u.im = 0 ∧ u.re ≤ 0)) :
    ‖hankelPsi c f u‖ ≤ 60 * ‖Complex.exp (-(4 / 3 : ℂ) * u ^ (3 / 2 : ℂ))‖ * (u ^ (1 / 2 : ℂ)).re ^ (-(1 / 2 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  set K : ℝ := c ^ (2 / 3 : ℝ) * langerKappa with hK
  have hK0 : 0 < K := mul_pos (Real.rpow_pos_of_pos hc0 _) langerKappa_pos
  set y : ℂ := u / (K : ℂ) with hy
  have hKne : (K : ℂ) ≠ 0 := by exact_mod_cast hK0.ne'
  have huy : (K : ℂ) * y = u := by rw [hy]; field_simp
  have hyn : ‖y‖ ≤ 4.94e-4 := by
    rw [hy, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK0, div_le_iff₀ hK0]
    linarith
  obtain ⟨q, hq, hqn, hqu, hqg⟩ := chart_saddle_data langerEta_etaC hc0 hyn (by rw [huy]; exact hcut)
  rw [huy] at hqu
  have henv := hankel_local_density_envelope hc hf hε hM hq hqn
  rw [hqu] at henv
  have hloc : ‖hankelLocal c f (Complex.log (1 + chartYinv etaC y))‖ ≤
      200 * (c ^ (1 / 3 : ℝ))⁻¹ * (Real.sqrt (u ^ (1 / 2 : ℂ)).re)⁻¹ *
        ‖Complex.exp (-(4 / 3 : ℂ) * u ^ (3 / 2 : ℂ))‖ := by
    rw [← hqg]; exact henv
  have hwn := norm_chartYinv_le langerEta_etaC hyn
  have h1w : 0.9995 ≤ ‖1 + chartYinv etaC y‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(chartYinv etaC y))
    rw [norm_neg, norm_one, sub_neg_eq_add] at this; linarith
  have hder := norm_deriv_chartYinv_le hyn
  have hk0 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hmu := langerMu_sq_ge
  have hpref : c ^ (1 / 3 : ℝ) / (2 * π * langerKappa) ≤ c ^ (1 / 3 : ℝ) * 0.27 := by
    have : 1 / (2 * π * langerKappa) ≤ 0.27 := by
      unfold langerKappa
      have hpi := Real.pi_pos
      have e : 1 / (2 * π * (12 * langerMu ^ 2 / π ^ 2)) = π / (24 * langerMu ^ 2) := by field_simp; ring
      rw [e, div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_lt_d2]
    calc c ^ (1 / 3 : ℝ) / (2 * π * langerKappa) = c ^ (1 / 3 : ℝ) * (1 / (2 * π * langerKappa)) := by ring
      _ ≤ _ := by gcongr
  have hRpos : 0 < (u ^ (1 / 2 : ℂ)).re := by
    have hus : u ∈ slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      by_contra hn; push Not at hn
      exact hcut ⟨hn.2, hn.1⟩
    exact re_saddleRoot_pos hus
  have hsq : (Real.sqrt (u ^ (1 / 2 : ℂ)).re)⁻¹ = (u ^ (1 / 2 : ℂ)).re ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hRpos.le]
  rw [hsq] at hloc
  have hE0 : 0 ≤ ‖Complex.exp (-(4 / 3 : ℂ) * u ^ (3 / 2 : ℂ))‖ := norm_nonneg _
  have hR0 : 0 ≤ (u ^ (1 / 2 : ℂ)).re ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hRpos.le _
  have hnorm : ‖hankelPsi c f u‖ = (c ^ (1 / 3 : ℝ) / (2 * π * langerKappa)) *
      ‖deriv (chartYinv etaC) y‖ / ‖1 + chartYinv etaC y‖ *
      ‖hankelLocal c f (Complex.log (1 + chartYinv etaC y))‖ := by
    show ‖hankelPsiY c f y‖ = _
    unfold hankelPsiY
    rw [norm_mul, norm_div, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by have := langerKappa_pos; positivity)]
  rw [hnorm]
  have hL0 := norm_nonneg (hankelLocal c f (Complex.log (1 + chartYinv etaC y)))
  have hD0 := norm_nonneg (deriv (chartYinv etaC) y)
  have hpref0 : 0 ≤ c ^ (1 / 3 : ℝ) / (2 * π * langerKappa) := by
    have := langerKappa_pos; positivity
  have hcc : c ^ (1 / 3 : ℝ) * (c ^ (1 / 3 : ℝ))⁻¹ = 1 := mul_inv_cancel₀ hk0.ne'
  calc (c ^ (1 / 3 : ℝ) / (2 * π * langerKappa)) * ‖deriv (chartYinv etaC) y‖ / ‖1 + chartYinv etaC y‖ *
        ‖hankelLocal c f (Complex.log (1 + chartYinv etaC y))‖
      ≤ (c ^ (1 / 3 : ℝ) * 0.27) * (1 / 0.996) / 0.9995 *
        (200 * (c ^ (1 / 3 : ℝ))⁻¹ * (u ^ (1 / 2 : ℂ)).re ^ (-(1 / 2 : ℝ)) *
          ‖Complex.exp (-(4 / 3 : ℂ) * u ^ (3 / 2 : ℂ))‖) := by
        gcongr
    _ = (0.27 * 200 / 0.996 / 0.9995) * (c ^ (1 / 3 : ℝ) * (c ^ (1 / 3 : ℝ))⁻¹) *
        ‖Complex.exp (-(4 / 3 : ℂ) * u ^ (3 / 2 : ℂ))‖ * (u ^ (1 / 2 : ℂ)).re ^ (-(1 / 2 : ℝ)) := by ring
    _ ≤ 60 * ‖Complex.exp (-(4 / 3 : ℂ) * u ^ (3 / 2 : ℂ))‖ * (u ^ (1 / 2 : ℂ)).re ^ (-(1 / 2 : ℝ)) := by
        rw [hcc]
        have : (0.27 * 200 / 0.996 / 0.9995 : ℝ) * 1 ≤ 60 := by norm_num
        gcongr

/-- info: 'FormalResearch.SignUncertainty.hankelPsi_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelPsi_envelope

end FormalResearch.SignUncertainty
