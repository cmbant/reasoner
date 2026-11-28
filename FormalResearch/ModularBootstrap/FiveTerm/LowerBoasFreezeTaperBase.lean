module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasFreezeCoord

/-!
# Shifted Taper Coordinates and Chart Matching (`ctl:freeze`)

Establishes:
* `virasoroPsiEps_re_c2`: Cauchy `C^2` bounds for `w ↦ Re(ψ_ε(w))` on `|w| ≤ r_ψ / 2`.
* `lowerTaper_zeta_eq`: exact identity between `lowerTaper virasoroPhi virasoroUhat c' R (c' x(ζ)^2 / 3)`
  and the explicit taper `taperWζ c' R ζ` (`1 - lowerW6 R (taperV c' ζ)` for `ζ ≤ zetaR c' R`, `1` beyond).
* `zetaR_bounds`: upper/lower bounds on `-(virasoroPhi c' (-R)).re`, `vOfZeta (zetaMin c' / 2)`, and `zetaR c' R`.
-/

@[expose] public section

open Real Complex MeasureTheory Filter Topology Set Metric
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.TipFront
open FormalResearch.ModularBootstrap.Contour

noncomputable section

/-! ### 1. Exact `v ↔ ζ` Langer relation and Cauchy `C^2` bound for `ψ_ε` -/

/-- `ζ(v) = (2 / (3π)) v^{3/2}` inverse to `v(ζ) = (3πζ / 2)^{2/3}`. -/
def zetaOfV (v : ℝ) : ℝ := (2 / (3 * π)) * v ^ (3 / 2 : ℝ)

/-- `v(ζ) = (3πζ / 2)^{2/3}`. -/
def vOfZeta (ζ : ℝ) : ℝ := (3 * π * ζ / 2) ^ (2 / 3 : ℝ)

/-- Upper taper edge in `ζ`: `ζ_R = (2 / (3π)) (-Re φ_c(-R))^{3/2}`. -/
def zetaR (c' R : ℝ) : ℝ := zetaOfV (-(virasoroPhi c' (-R)).re)

/-- Shifted taper argument `v(ζ) = -û_c(-v_0(ζ))` for `ζ > 0`. -/
def taperV (c' ζ : ℝ) : ℝ := -virasoroUhat c' (-vOfZeta ζ)

/-- Piecewise taper formula in `ζ`. -/
def taperWζ (c' R ζ : ℝ) : ℝ :=
  if ζ ≤ zetaR c' R then 1 - lowerW6 R (taperV c' ζ) else 1

/-- Tapered leading density `P(ζ) = w̃_R(ζ) P_0(ζ)`. -/
def lowerPζ (c' R ζ : ℝ) : ℝ :=
  lowerTaper virasoroPhi virasoroUhat c' R (c' * xOfZeta c' ζ ^ 2 / 3) * lowerP0 c' ζ

lemma vOfZeta_pos {ζ : ℝ} (hζ : 0 < ζ) : 0 < vOfZeta ζ := by
  unfold vOfZeta; positivity

lemma zetaOfV_pos {v : ℝ} (hv : 0 < v) : 0 < zetaOfV v := by
  unfold zetaOfV; positivity

lemma vOfZeta_zetaOfV {v : ℝ} (hv : 0 ≤ v) : vOfZeta (zetaOfV v) = v := by
  unfold vOfZeta zetaOfV
  have hpi := Real.pi_pos
  have heq : 3 * π * (2 / (3 * π) * v ^ (3 / 2 : ℝ)) / 2 = v ^ (3 / 2 : ℝ) := by
    field_simp [hpi.ne']
  rw [heq, ← Real.rpow_mul hv]
  norm_num

lemma zetaOfV_vOfZeta {ζ : ℝ} (hζ : 0 ≤ ζ) : zetaOfV (vOfZeta ζ) = ζ := by
  unfold zetaOfV vOfZeta
  have hpi := Real.pi_pos
  rw [← Real.rpow_mul (by positivity : 0 ≤ 3 * π * ζ / 2)]
  norm_num

lemma zetaOfV_le_iff {v₁ v₂ : ℝ} (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) :
    zetaOfV v₁ ≤ zetaOfV v₂ ↔ v₁ ≤ v₂ := by
  unfold zetaOfV
  have hc : (0 : ℝ) < 2 / (3 * π) := by positivity
  rw [mul_le_mul_iff_right₀ hc]
  exact Real.rpow_le_rpow_iff hv₁ hv₂ (by norm_num)

lemma vOfZeta_mono {ζ₁ ζ₂ : ℝ} (hζ₁ : 0 ≤ ζ₁) (h : ζ₁ ≤ ζ₂) : vOfZeta ζ₁ ≤ vOfZeta ζ₂ := by
  unfold vOfZeta
  have hpi := Real.pi_pos
  exact Real.rpow_le_rpow (by positivity) (by gcongr) (by norm_num)

lemma vOfZeta_derivs {ζ : ℝ} (hζ : 0 < ζ) :
    let v1 : ℝ → ℝ := fun t => (2 / 3 : ℝ) * vOfZeta t / t
    let v2 : ℝ → ℝ := fun t => -(2 / 9 : ℝ) * vOfZeta t / t ^ 2
    HasDerivAt vOfZeta (v1 ζ) ζ ∧ HasDerivAt v1 (v2 ζ) ζ := by
  intro v1 v2
  have hpi := Real.pi_pos
  have hlin : ∀ t, HasDerivAt (fun u : ℝ => 3 * π * u / 2) (3 * π / 2) t := fun t =>
    (((hasDerivAt_id t).const_mul (3 * π)).div_const 2).congr_deriv (by ring)
  have hd_v : ∀ {t : ℝ}, 0 < t → HasDerivAt vOfZeta (v1 t) t := fun {t} ht => by
    have hpos : 0 < 3 * π * t / 2 := by positivity
    have hp := (Real.hasDerivAt_rpow_const (p := (2 / 3 : ℝ)) (Or.inl hpos.ne')).comp t (hlin t)
    refine hp.congr_deriv ?_
    have hpow : (3 * π * t / 2) ^ ((2 / 3 : ℝ) - 1) * (3 * π * t / 2) =
        (3 * π * t / 2) ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_add_one hpos.ne']; ring_nf
    dsimp [v1, vOfZeta]
    have h1 : (2 / 3 : ℝ) * (3 * π * t / 2) ^ ((2 / 3 : ℝ) - 1) * (3 * π / 2) * t =
        (2 / 3 : ℝ) * ((3 * π * t / 2) ^ ((2 / 3 : ℝ) - 1) * (3 * π * t / 2)) := by ring
    rw [eq_div_iff ht.ne', h1, hpow]
  have hd_v1 : HasDerivAt v1 (v2 ζ) ζ := by
    have hd_num := (hd_v hζ).const_mul (2 / 3 : ℝ)
    have hd_q := hd_num.div (hasDerivAt_id ζ) hζ.ne'
    refine hd_q.congr_deriv ?_
    dsimp [v2, v1]
    field_simp [hζ.ne']; ring
  exact ⟨hd_v hζ, hd_v1⟩

lemma virasoroPsiEps_re_c2 {ε w : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 4)
    (hw : |w| ≤ chartParams.r_ψ / 2) :
    let ψR : ℝ → ℝ := fun t => (virasoroPsiEps ε (t : ℂ)).re
    let ψ1 : ℝ → ℝ := fun t => (deriv (virasoroPsiEps ε) (t : ℂ)).re
    let ψ2 : ℝ → ℝ := fun t => (deriv (deriv (virasoroPsiEps ε)) (t : ℂ)).re
    HasDerivAt ψR (ψ1 w) w ∧ HasDerivAt ψ1 (ψ2 w) w ∧
    |ψR w| ≤ chartParams.M_ψ ∧ |ψ1 w| ≤ chartParams.M_ψ ∧
    |ψ2 w| ≤ 2 * chartParams.M_ψ / chartParams.r_ψ := by
  intro ψR ψ1 ψ2
  obtain ⟨hf_diff, _, hf_bd, _, _⟩ := chartParams.hψ_spec ε hε0 hε1
  have hr_pos : 0 < chartParams.r_ψ := chartParams.hrψ_pos
  have hr2_pos : 0 < chartParams.r_ψ / 2 := half_pos hr_pos
  have hw_ball : (w : ℂ) ∈ ball (0 : ℂ) chartParams.ρ_ψ := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact hw.trans_lt (by linarith [chartParams.hrψ_lt])
  have hw_cb : (w : ℂ) ∈ closedBall (0 : ℂ) chartParams.r_ψ := by
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact hw.trans (by linarith)
  have hf_an : AnalyticOnNhd ℂ (virasoroPsiEps ε) (ball 0 chartParams.ρ_ψ) :=
    hf_diff.analyticOnNhd isOpen_ball
  have hg_an : AnalyticOnNhd ℂ (deriv (virasoroPsiEps ε)) (ball 0 chartParams.ρ_ψ) := hf_an.deriv
  have hd_f : HasDerivAt (virasoroPsiEps ε) (deriv (virasoroPsiEps ε) (w : ℂ)) (w : ℂ) :=
    (hf_diff.differentiableAt (isOpen_ball.mem_nhds hw_ball)).hasDerivAt
  have hd_g : HasDerivAt (deriv (virasoroPsiEps ε)) (deriv (deriv (virasoroPsiEps ε)) (w : ℂ)) (w : ℂ) :=
    (hg_an (w : ℂ) hw_ball).differentiableAt.hasDerivAt
  have hd_ψR : HasDerivAt ψR (ψ1 w) w := by
    have h1 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt w hd_f.comp_ofReal
    exact h1.congr_deriv (by simp [ψ1])
  have hd_ψ1 : HasDerivAt ψ1 (ψ2 w) w := by
    have h1 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt w hd_g.comp_ofReal
    exact h1.congr_deriv (by simp [ψ2])
  have hbd0 : |ψR w| ≤ chartParams.M_ψ :=
    (Complex.abs_re_le_norm _).trans (hf_bd _ hw_cb).1
  have hbd1 : |ψ1 w| ≤ chartParams.M_ψ :=
    (Complex.abs_re_le_norm _).trans (hf_bd _ hw_cb).2
  have hcb_sub : closedBall (w : ℂ) (chartParams.r_ψ / 2) ⊆ closedBall (0 : ℂ) chartParams.r_ψ := by
    intro z hz
    rw [mem_closedBall] at hz
    rw [mem_closedBall_zero_iff]
    have hwn : ‖(w : ℂ)‖ ≤ chartParams.r_ψ / 2 := by
      simpa [Complex.norm_real, Real.norm_eq_abs] using hw
    calc ‖z‖ = ‖(z - (w : ℂ)) + (w : ℂ)‖ := by ring_nf
      _ ≤ ‖z - (w : ℂ)‖ + ‖(w : ℂ)‖ := norm_add_le _ _
      _ = dist z (w : ℂ) + ‖(w : ℂ)‖ := by rw [dist_eq_norm]
      _ ≤ chartParams.r_ψ / 2 + chartParams.r_ψ / 2 := add_le_add hz hwn
      _ = chartParams.r_ψ := by ring
  have hcl : DiffContOnCl ℂ (deriv (virasoroPsiEps ε)) (ball (w : ℂ) (chartParams.r_ψ / 2)) :=
    (hg_an.differentiableOn.mono (closure_ball_subset_closedBall.trans
      (hcb_sub.trans (closedBall_subset_ball chartParams.hrψ_lt)))).diffContOnCl
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 hr2_pos hcl
    fun z hz => (hf_bd z (hcb_sub (sphere_subset_closedBall hz))).2
  rw [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul, pow_one,
    div_div_eq_mul_div] at hcauchy
  have hbd2 : |ψ2 w| ≤ 2 * chartParams.M_ψ / chartParams.r_ψ :=
    (Complex.abs_re_le_norm _).trans (by linarith only [hcauchy,
      show 2 * chartParams.M_ψ / chartParams.r_ψ = chartParams.M_ψ * 2 / chartParams.r_ψ by ring])
  exact ⟨hd_ψR, hd_ψ1, hbd0, hbd1, hbd2⟩

/-! ### 2. Chart window constants and `lowerTaper` coordinate match -/

lemma virasoroChart_pack :
    ∃ cc C_phi : ℝ, 0 ≤ C_phi ∧ ∀ c : ℝ, cc ≤ c →
      (∀ x : ℝ, |x| ≤ lowerRmax virasoroC1 c → (virasoroPhi c (x : ℂ)).im = 0) ∧
      (∀ u : ℂ, ‖u‖ ≤ lowerRmax virasoroC1 c →
        ‖virasoroPhi c u - u‖ ≤ C_phi * c ^ (-(1 / 3 : ℝ))) ∧
      (∀ x : ℝ, |x| ≤ lowerRmax virasoroC1 c →
        virasoroUhat c (virasoroPhi c (x : ℂ)).re = x) := by
  obtain ⟨cc, C_phi, hC_nn, hspec⟩ := virasoroChart_holds
  refine ⟨cc, C_phi, hC_nn, fun c hc => ?_⟩
  obtain ⟨_, him, hdiff, hinv, _⟩ := hspec c hc
  exact ⟨him, fun u hu => (hdiff u hu).1, hinv⟩

/-- Large-`c'` threshold above which all taper coordinate and positivity hypotheses hold cleanly. -/
def taperC0 : ℝ :=
  let C_phi := Classical.choose (Classical.choose_spec virasoroChart_pack)
  let cc := Classical.choose virasoroChart_pack
  max (max 10000 cc)
    (max (4 * (C_phi + 1) / virasoroC1 ^ 2 + 1)
      (max ((4 / virasoroC1 ^ 2 + 1) ^ 11 + 1)
        (max ((4 * betaTip * (chartParams.M_ψ + 1) + 1) ^ 2)
          (2 * (chartParams.M_ψ + 1) + 4 * chartParams.M_ψ / chartParams.r_ψ + 1))))

lemma taperC0_ge : 10000 ≤ taperC0 := by
  unfold taperC0; exact le_max_of_le_left (le_max_left _ _)

lemma taperC0_cc {c' : ℝ} (hc' : taperC0 ≤ c') : Classical.choose virasoroChart_pack ≤ c' := by
  unfold taperC0 at hc'
  exact (le_max_of_le_left (le_max_right _ _)).trans hc'

lemma taperC0_phi {c' : ℝ} (hc' : taperC0 ≤ c') :
    4 * (Classical.choose (Classical.choose_spec virasoroChart_pack) + 1) / virasoroC1 ^ 2 + 1 ≤ c' := by
  unfold taperC0 at hc'
  exact (le_max_left _ _).trans ((le_max_right _ _).trans hc')

lemma taperC0_pow11 {c' : ℝ} (hc' : taperC0 ≤ c') :
    (4 / virasoroC1 ^ 2 + 1) ^ 11 + 1 ≤ c' := by
  unfold taperC0 at hc'
  exact (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc'))

lemma taperC0_beta {c' : ℝ} (hc' : taperC0 ≤ c') :
    (4 * betaTip * (chartParams.M_ψ + 1) + 1) ^ 2 ≤ c' := by
  unfold taperC0 at hc'
  exact (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc')))

lemma taperC0_psi {c' : ℝ} (hc' : taperC0 ≤ c') :
    2 * (chartParams.M_ψ + 1) + 4 * chartParams.M_ψ / chartParams.r_ψ + 1 ≤ c' := by
  unfold taperC0 at hc'
  exact (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc')))

lemma taper_R_phi_bounds {c' R : ℝ} (hc' : taperC0 ≤ c')
    (hR : LowerRadiusRange virasoroC1 c' R) :
    let uR := (virasoroPhi c' (-R)).re
    (virasoroPhi c' (-R)).im = 0 ∧
    |uR - (-R)| ≤ R / 4 ∧
    R / 2 ≤ -uR ∧ -uR ≤ 5 * R / 4 ∧
    -(5 * virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ)) ≤ uR ∧ uR < 0 ∧
    -(virasoroAC c' ^ 2) ≤ uR ∧
    virasoroUhat c' uR = -R := by
  intro uR
  let C_phi := Classical.choose (Classical.choose_spec virasoroChart_pack)
  have hpack := Classical.choose_spec (Classical.choose_spec virasoroChart_pack)
  have hC_nn : 0 ≤ C_phi := hpack.1
  have hcc : Classical.choose virasoroChart_pack ≤ c' := taperC0_cc hc'
  have hc0 : 0 < c' := by linarith [taperC0_ge]
  have hc23_pos : 0 < c' ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hR_min : virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R := hR.1
  have hR_max : R ≤ 4 * virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) := hR.2
  have hR_pos : 0 < R := lt_of_lt_of_le (mul_pos (pow_pos virasoroC1_pos 2) hc23_pos) hR_min
  have hmR : |-R| ≤ lowerRmax virasoroC1 c' := by
    rw [abs_neg, abs_of_pos hR_pos]; exact hR_max
  obtain ⟨him, hdiff, hinv⟩ := hpack.2 c' hcc
  have hu_im : (virasoroPhi c' (-R : ℂ)).im = 0 := by
    have := him (-R) hmR
    simpa only [Complex.ofReal_neg] using this
  have hu_norm : ‖((-R : ℝ) : ℂ)‖ ≤ lowerRmax virasoroC1 c' := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hmR
  have hu_diff : |uR - (-R)| ≤ C_phi * c' ^ (-(1 / 3 : ℝ)) := by
    have h := (Complex.abs_re_le_norm (virasoroPhi c' ((-R : ℝ) : ℂ) - ((-R : ℝ) : ℂ))).trans
      (hdiff _ hu_norm)
    change |(virasoroPhi c' ((-R : ℝ) : ℂ)).re - (-R)| ≤ C_phi * c' ^ (-(1 / 3 : ℝ)) at h
    simpa only [Complex.ofReal_neg, uR] using h
  have hCphi_le : C_phi * c' ^ (-(1 / 3 : ℝ)) ≤ virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) / 4 := by
    have h4 : 4 * (C_phi + 1) / virasoroC1 ^ 2 ≤ c' := by
      have := taperC0_phi hc'; linarith only [this]
    have h4' : C_phi ≤ virasoroC1 ^ 2 * c' / 4 := by
      rw [div_le_iff₀ (pow_pos virasoroC1_pos 2)] at h4
      nlinarith only [h4, hC_nn]
    calc C_phi * c' ^ (-(1 / 3 : ℝ))
        ≤ (virasoroC1 ^ 2 * c' / 4) * c' ^ (-(1 / 3 : ℝ)) := by gcongr
      _ = virasoroC1 ^ 2 / 4 * (c' * c' ^ (-(1 / 3 : ℝ))) := by ring
      _ = virasoroC1 ^ 2 / 4 * c' ^ (2 / 3 : ℝ) := by
          congr 1
          conv_lhs => lhs; rw [← Real.rpow_one c']
          rw [← Real.rpow_add hc0]; norm_num
      _ = virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) / 4 := by ring
  have hdiff_le : |uR - (-R)| ≤ virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) / 4 := hu_diff.trans hCphi_le
  have h14R : |uR - (-R)| ≤ R / 4 := hdiff_le.trans (by linarith only [hR_min])
  have hlo : R / 2 ≤ -uR := by linarith only [(abs_le.mp h14R).2, hR_pos]
  have hhi : -uR ≤ 5 * R / 4 := by linarith only [(abs_le.mp h14R).1, hR_pos]
  have h5 : -(5 * virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ)) ≤ uR := by
    linarith only [hhi, hR_max]
  have hneg : uR < 0 := by linarith only [hlo, hR_pos]
  have hAC : -(virasoroAC c' ^ 2) ≤ uR := by
    have hA2 : virasoroAC c' ^ 2 = 2 * virasoroBV ^ 2 * c' ^ (2 / 3 : ℝ) := virasoroAC_sq c' hc0.le
    have h5bv : 5 * virasoroC1 ^ 2 ≤ 2 * virasoroBV ^ 2 := by
      have hbv := virasoroC1_small.trans virasoroBVChoice_le
      have hsq : (10 * virasoroC1) ^ 2 ≤ virasoroBV ^ 2 :=
        pow_le_pow_left₀ (by linarith only [virasoroC1_pos]) hbv 2
      nlinarith only [hsq, virasoroBV_pos]
    rw [hA2]
    nlinarith only [h5, h5bv, hc23_pos]
  have hu_inv : virasoroUhat c' uR = -R := by
    have h1 := hinv (-R) hmR
    simpa only [Complex.ofReal_neg, uR] using h1
  exact ⟨hu_im, h14R, hlo, hhi, h5, hneg, hAC, hu_inv⟩

private lemma virasoroDelta_xOfZeta_eq {c' ζ : ℝ} (hc0 : 0 < c') (hζ : 0 < ζ)
    (hv : vOfZeta ζ ≤ 5 * virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ)) :
    virasoroDeltaChart c' (-vOfZeta ζ) = c' * xOfZeta c' ζ ^ 2 / 3 := by
  have hv_pos : 0 < vOfZeta ζ := vOfZeta_pos hζ
  obtain ⟨hx_gt, hcum_eq, _⟩ := xOfZeta_spec hc0 hζ
  set x := xOfZeta c' ζ
  have hx_pos : 0 < x := xiStar_pos.trans hx_gt
  obtain ⟨htau, _, hx'_gt⟩ := lowerLangerPhase_band hc0 (u := -vOfZeta ζ)
    (by linarith only [hv]) (by linarith only [hv_pos])
  set x' := √(3 * virasoroDeltaChart c' (-vOfZeta ζ) / c')
  have htau_eq : tauPhase x' = tauPhase x := by
    rw [htau, neg_neg]
    have hβ := betaTip_pos
    have hc23 : 0 < c' ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    unfold vOfZeta tauPhase
    have hk_pos := kTip_pos
    have hpi := Real.pi_pos
    have hβ_eq : betaTip = (3 * π * kTip / 2) ^ (2 / 3 : ℝ) := by
      unfold betaTip KTip; congr 1; ring
    have hmul : betaTip * c' ^ (2 / 3 : ℝ) = (3 * π * kTip / 2 * c') ^ (2 / 3 : ℝ) := by
      rw [hβ_eq]
      exact (@Real.mul_rpow (3 * π * kTip / 2) c' (2 / 3 : ℝ) (by positivity) hc0.le).symm
    rw [hmul, ← Real.div_rpow (by positivity) (by positivity)]
    congr 1
    calc (3 * π * ζ / 2) / (3 * π * kTip / 2 * c')
        = (ζ / c') / kTip := by field_simp [hk_pos.ne', hc0.ne', hpi.ne']
      _ = cumulN x / kTip := by
          congr 1; rw [div_eq_iff hc0.ne']; linarith only [hcum_eq]
  have hx'_eq : x' = x := tauPhase_strictMonoOn.injOn hx'_gt.le hx_gt.le htau_eq
  have hΔ_nn : 0 ≤ 3 * virasoroDeltaChart c' (-vOfZeta ζ) / c' := by
    by_contra h
    have h0 : x' = 0 := by dsimp [x']; exact Real.sqrt_eq_zero_of_nonpos (le_of_not_ge h)
    linarith only [h0, hx'_gt, xiStar_pos]
  have hsq : 3 * virasoroDeltaChart c' (-vOfZeta ζ) / c' = x ^ 2 := by
    calc 3 * virasoroDeltaChart c' (-vOfZeta ζ) / c' = x' ^ 2 := (Real.sq_sqrt hΔ_nn).symm
      _ = x ^ 2 := by rw [hx'_eq]
  field_simp [hc0.ne'] at hsq ⊢
  linarith only [hsq]

lemma lowerTaper_zeta_eq {c' R ζ : ℝ} (hc' : taperC0 ≤ c')
    (hR : LowerRadiusRange virasoroC1 c' R) (hζ : 0 < ζ) :
    lowerTaper virasoroPhi virasoroUhat c' R (c' * xOfZeta c' ζ ^ 2 / 3) = taperWζ c' R ζ := by
  have hc0 : 0 < c' := by linarith [taperC0_ge]
  obtain ⟨hx_gt, _, _⟩ := xOfZeta_spec hc0 hζ
  have ht_lo : virasoroDeltaChart c' 0 ≤ c' * xOfZeta c' ζ ^ 2 / 3 := by
    rw [virasoroDeltaChart_zero]
    have hx_sq : xiStar ^ 2 < xOfZeta c' ζ ^ 2 := sq_lt_sq' (by linarith [xiStar_pos]) hx_gt
    unfold xiBar
    nlinarith only [hx_sq, hc0]
  obtain ⟨_, _, _, _, h5_uR, hneg_uR, hAC_uR, _⟩ := taper_R_phi_bounds hc' hR
  set uR := (virasoroPhi c' (-R)).re
  set ζR := zetaR c' R
  have hζR_pos : 0 < ζR := zetaOfV_pos (by linarith only [hneg_uR])
  have hv_ζR : vOfZeta ζR = -uR := vOfZeta_zetaOfV (by linarith only [hneg_uR])
  have hΔ_ζR : virasoroDeltaChart c' uR = c' * xOfZeta c' ζR ^ 2 / 3 := by
    have h1 := virasoroDelta_xOfZeta_eq hc0 hζR_pos (by rw [hv_ζR]; linarith only [h5_uR])
    rwa [hv_ζR, neg_neg] at h1
  unfold lowerTaper taperWζ
  by_cases hle : ζ ≤ ζR
  · have hv_le : vOfZeta ζ ≤ -uR := by
      have h1 : zetaOfV (vOfZeta ζ) ≤ zetaOfV (-uR) := by rwa [zetaOfV_vOfZeta hζ.le]
      exact (zetaOfV_le_iff (vOfZeta_pos hζ).le (by linarith only [hneg_uR])).mp h1
    have hv5 : vOfZeta ζ ≤ 5 * virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) := hv_le.trans (by linarith only [h5_uR])
    have hΔ_ζ := virasoroDelta_xOfZeta_eq hc0 hζ hv5
    have ht_hi : c' * xOfZeta c' ζ ^ 2 / 3 ≤ virasoroDeltaChart c' (virasoroPhi c' ((-R : ℝ) : ℂ)).re := by
      have hsub : c' * xOfZeta c' ζ ^ 2 / 3 ≤ virasoroDeltaChart c' uR := by
        rw [hΔ_ζR]
        rcases hle.eq_or_lt with rfl | hlt
        · exact le_rfl
        · have hx_lt := xOfZeta_strictMono hc0 (Set.mem_Ioi.mpr hζ) (Set.mem_Ioi.mpr hζR_pos) hlt
          have hx_pos : 0 < xOfZeta c' ζ := xiStar_pos.trans hx_gt
          have hx_sq : xOfZeta c' ζ ^ 2 < xOfZeta c' ζR ^ 2 := sq_lt_sq' (by linarith) hx_lt
          nlinarith only [hx_sq, hc0]
      simpa only [uR, Complex.ofReal_neg] using hsub
    have hmem_v : |-vOfZeta ζ| ≤ virasoroAC c' ^ 2 := by
      rw [abs_neg, abs_of_pos (vOfZeta_pos hζ)]
      exact hv_le.trans (by linarith only [hAC_uR])
    have hu_eq : virasoroUChart c' ((c' * xOfZeta c' ζ ^ 2 / 3) / c') = -vOfZeta ζ := by
      rw [← hΔ_ζ]
      exact virasoroUChart_deltaChart hc0 hmem_v
    have hcond : virasoroDeltaChart c' 0 ≤ c' * xOfZeta c' ζ ^ 2 / 3 ∧
        c' * xOfZeta c' ζ ^ 2 / 3 ≤ virasoroDeltaChart c' (virasoroPhi c' ((-R : ℝ) : ℂ)).re := ⟨ht_lo, ht_hi⟩
    split_ifs
    rw [hu_eq]; unfold lowerWR taperV lowerW6
    congr 3; rw [neg_neg, neg_div, neg_pow]; norm_num
  · have hlt : ζR < ζ := lt_of_not_ge hle
    have hx_lt := xOfZeta_strictMono hc0 (Set.mem_Ioi.mpr hζR_pos) (Set.mem_Ioi.mpr hζ) hlt
    have hxR_pos : 0 < xOfZeta c' ζR := xiStar_pos.trans (xOfZeta_spec hc0 hζR_pos).1
    have ht_gt : virasoroDeltaChart c' (virasoroPhi c' ((-R : ℝ) : ℂ)).re < c' * xOfZeta c' ζ ^ 2 / 3 := by
      have hsub : virasoroDeltaChart c' uR < c' * xOfZeta c' ζ ^ 2 / 3 := by
        rw [hΔ_ζR]
        have hx_sq : xOfZeta c' ζR ^ 2 < xOfZeta c' ζ ^ 2 := sq_lt_sq' (by linarith) hx_lt
        nlinarith only [hx_sq, hc0]
      simpa only [uR, Complex.ofReal_neg] using hsub
    have hcond : ¬(virasoroDeltaChart c' 0 ≤ c' * xOfZeta c' ζ ^ 2 / 3 ∧
        c' * xOfZeta c' ζ ^ 2 / 3 ≤ virasoroDeltaChart c' (virasoroPhi c' ((-R : ℝ) : ℂ)).re) :=
      fun h => hlt.not_ge (by linarith only [h.2, ht_gt])
    split_ifs; rfl

lemma zetaR_bounds {c' R : ℝ} (hc' : taperC0 ≤ c') (hR : LowerRadiusRange virasoroC1 c' R) :
    let uR := (virasoroPhi c' (-R)).re
    R / 2 ≤ -uR ∧ -uR ≤ 5 * R / 4 ∧
    (1 / 2 : ℝ) * c' ^ (4 / 7 : ℝ) ≤ vOfZeta (zetaMin c' / 2) ∧
    2 * zetaMin c' ≤ zetaR c' R ∧
    10 ≤ zetaMin c' ∧
    zetaR c' R ≤ (2 / (3 * π)) * (5 * virasoroC1 ^ 2) ^ (3 / 2 : ℝ) * c' := by
  have hc0 : 0 < c' := by linarith [taperC0_ge]
  obtain ⟨_, _, hlo_uR, hhi_uR, h5_uR, hneg_uR, _, _⟩ := taper_R_phi_bounds hc' hR
  have hc23 : 0 < c' ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hc47 : 0 < c' ^ (4 / 7 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hv_zmin : (1 / 2 : ℝ) * c' ^ (4 / 7 : ℝ) ≤ vOfZeta (zetaMin c' / 2) := by
    unfold vOfZeta zetaMin
    have hpi := Real.pi_pos
    have h1 : 3 * π * (2 / (3 * π) * c' ^ (6 / 7 : ℝ) / 2) / 2 = (1 / 2 : ℝ) * c' ^ (6 / 7 : ℝ) := by
      field_simp [hpi.ne']
    rw [h1, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hc0.le _),
      ← Real.rpow_mul hc0.le, show (6 / 7 : ℝ) * (2 / 3 : ℝ) = 4 / 7 by norm_num]
    have h2 : (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ (2 / 3 : ℝ) := by
      calc (1 / 2 : ℝ) = (1 / 2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (1 / 2 : ℝ) ^ (2 / 3 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
    gcongr
  have hzmin_ge : 10 ≤ zetaMin c' := by
    unfold zetaMin
    have h128 : (2 : ℝ) ^ (7 : ℕ) ≤ c' := by linarith [taperC0_ge]
    have h67 : (64 : ℝ) ≤ c' ^ (6 / 7 : ℝ) := by
      have h1 := Real.rpow_le_rpow (by positivity) h128 (by norm_num : (0 : ℝ) ≤ 6 / 7)
      rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two] at h1
      norm_num at h1; exact h1
    have hpi4 : π < 4 := Real.pi_lt_four
    have hden : 3 * π < 12 := by linarith
    have hfrac : 2 / (3 * π) ≥ 2 / 12 := by gcongr
    nlinarith only [hfrac, h67]
  have hζR_hi : zetaR c' R ≤ (2 / (3 * π)) * (5 * virasoroC1 ^ 2) ^ (3 / 2 : ℝ) * c' := by
    unfold zetaR zetaOfV
    have hnn : 0 ≤ -(virasoroPhi c' (-R)).re := by linarith only [hneg_uR]
    calc 2 / (3 * π) * (-(virasoroPhi c' (-R)).re) ^ (3 / 2 : ℝ)
        ≤ 2 / (3 * π) * (5 * virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) := by
          gcongr; linarith only [h5_uR]
      _ = 2 / (3 * π) * ((5 * virasoroC1 ^ 2) ^ (3 / 2 : ℝ) * (c' ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ)) := by
          rw [Real.mul_rpow (by positivity) hc23.le]
      _ = 2 / (3 * π) * (5 * virasoroC1 ^ 2) ^ (3 / 2 : ℝ) * c' := by
          rw [← Real.rpow_mul hc0.le]; norm_num; ring
  have hζR_lo : 2 * zetaMin c' ≤ zetaR c' R := by
    have h11 : (4 / virasoroC1 ^ 2 + 1) ^ 11 + 1 ≤ c' := taperC0_pow11 hc'
    have h11' : (4 / virasoroC1 ^ 2 + 1) ^ (11 : ℝ) ≤ c' := by
      rw [show (11 : ℝ) = ((11 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; linarith only [h11]
    have hc_pow : (4 / virasoroC1 ^ 2 + 1) ^ (21 / 2 : ℝ) ≤ c' := by
      have hle : (4 / virasoroC1 ^ 2 + 1) ^ (21 / 2 : ℝ) ≤ (4 / virasoroC1 ^ 2 + 1) ^ (11 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [virasoroC1_pos, show (0 : ℝ) ≤ 4 / virasoroC1 ^ 2 by positivity])
          (by norm_num)
      exact hle.trans h11'
    have hc221 : 4 / virasoroC1 ^ 2 ≤ c' ^ (2 / 21 : ℝ) := by
      have h_pow := Real.rpow_le_rpow (by positivity) hc_pow (by norm_num : (0 : ℝ) ≤ 2 / 21)
      rw [← Real.rpow_mul (by positivity)] at h_pow
      norm_num at h_pow
      exact (by linarith only [virasoroC1_pos] : 4 / virasoroC1 ^ 2 ≤ 4 / virasoroC1 ^ 2 + 1).trans h_pow
    have h4v : 4 * c' ^ (4 / 7 : ℝ) ≤ virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hc221 (pow_pos virasoroC1_pos 2).le
      rw [mul_div_cancel₀ _ (pow_pos virasoroC1_pos 2).ne'] at hmul
      have hmul2 := mul_le_mul_of_nonneg_right hmul hc47.le
      rw [mul_assoc, ← Real.rpow_add hc0, show (2 / 21 : ℝ) + 4 / 7 = 2 / 3 by norm_num] at hmul2
      exact hmul2
    have h2v : 2 ^ (2 / 3 : ℝ) * c' ^ (4 / 7 : ℝ) ≤ -((virasoroPhi c' (-R)).re) := by
      have h2le : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 := by
        calc (2 : ℝ) ^ (2 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      have hR_min : virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R := hR.1
      calc (2 : ℝ) ^ (2 / 3 : ℝ) * c' ^ (4 / 7 : ℝ) ≤ 2 * c' ^ (4 / 7 : ℝ) := by gcongr
        _ ≤ virasoroC1 ^ 2 * c' ^ (2 / 3 : ℝ) / 2 := by linarith only [h4v]
        _ ≤ R / 2 := by linarith only [hR_min]
        _ ≤ -(virasoroPhi c' (-R)).re := hlo_uR
    have hzeq : 2 * zetaMin c' = zetaOfV (2 ^ (2 / 3 : ℝ) * c' ^ (4 / 7 : ℝ)) := by
      unfold zetaMin zetaOfV
      rw [Real.mul_rpow (by positivity) hc47.le, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_mul hc0.le]
      norm_num; ring
    rw [hzeq]
    exact (zetaOfV_le_iff (by positivity) (by linarith only [hneg_uR])).mpr h2v
  exact ⟨hlo_uR, hhi_uR, hv_zmin, hζR_lo, hzmin_ge, hζR_hi⟩

end

end FormalResearch.ModularBootstrap.FiveTerm
