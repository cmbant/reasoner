module

public import FormalResearch.ModularBootstrap.TipFront.ComplexMajorant
public import FormalResearch.ModularBootstrap.TipFront.ConcreteBlowup
public import FormalResearch.ModularBootstrap.Blowup.TipMap
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Virasoro Langer Chart and Tip Comparability (`lower_o1_two_edge.tex`, Proposition P Step 2)

Constructs the concrete Virasoro Langer chart `virasoroUInf`, its analytic local inverse
`virasoroXiInf`, and the `c'`-scaled chart maps `virasoroUChart`, `virasoroXiChart`,
`virasoroDeltaChart`, and `virasoroBChart` from `TipFront.lemmaGPotentialInput_virasoro`.

Main definitions and theorems:
* `virasoroUInf`, `virasoroXiInf`, `virasoroBV`, `virasoroAC`: the Virasoro Langer chart, its
  local inverse, and the concrete bootstrap radius `b_V > 0`, `A_{c'}^2 = 2 b_V^2 c'^{2/3}`.
* `virasoroUChart`, `virasoroDeltaChart`, `virasoroBChart`: `c'`-rescaled chart maps.
* `virasoro_chart_potential_eq`: exact potential identity
  `c' * (majorant2D (virasoroBChart c' u) + (tipL (virasoroBChart c' u)).re) = -(4/3) Re(u^{3/2})`
  on `closedBall 0 (virasoroAC c' ^ 2) \ (-∞, 0]`, giving `exp(...) = airyEnv u`.
* `virasoro_tip_comparability`: uniform comparability of `((-ζ)^{1/2}).re` and `tipDist ζ`
  with `(u^{1/2}).re` and `√‖u‖ * (u^{1/2}).re` up to the cut `(-∞, 0]`.
* `virasoro_deltaChart_inversion`: chart inversion for Step 5 of Theorem `FT-L.FW`
  (`Δ(a₁ + K c'^{-1/3}) ≥ ξ̄ c' + A_opt c'^{1/3} - c_* K - C_inv c'^{-1/3}`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.ConcreteBootstrap

open FormalResearch.Special
open PoissonJensen

/-! ### Section 1: `b(ξ) = √(3ξ)` and `u_∞(ξ)` near `ξ̄` -/

/-- Local complex branch `b(ξ) = (3 ξ)^{1/2}` near `ξ̄ = ξ_*^2 / 3`. -/
noncomputable def virasoroBOfXi (ξ : ℂ) : ℂ :=
  ((3 : ℂ) * ξ) ^ (1 / 2 : ℂ)

lemma virasoroBOfXi_xiBar : virasoroBOfXi (xiBar : ℂ) = (xiStar : ℂ) := by
  unfold virasoroBOfXi xiBar
  have h3 : (3 : ℂ) * ((xiStar ^ 2 / 3 : ℝ) : ℂ) = ((xiStar ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h3, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cpow (sq_nonneg xiStar), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq xiStar_pos.le]

lemma virasoroBOfXi_ofReal {ξ : ℝ} (hξ : 0 ≤ ξ) :
    virasoroBOfXi (ξ : ℂ) = (Real.sqrt (3 * ξ) : ℂ) := by
  unfold virasoroBOfXi
  rw [show (3 : ℂ) * (ξ : ℂ) = ((3 * ξ : ℝ) : ℂ) by push_cast; ring,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow]

lemma virasoroBOfXi_sq {ξ : ℂ} : virasoroBOfXi ξ ^ 2 = (3 : ℂ) * ξ := by
  unfold virasoroBOfXi
  exact cpow_half_sq _

lemma virasoroBOfXi_conj {ξ : ℂ} (hre : 0 < ξ.re) :
    virasoroBOfXi (starRingEnd ℂ ξ) = starRingEnd ℂ (virasoroBOfXi ξ) := by
  unfold virasoroBOfXi
  have h3re : 0 < ((3 : ℂ) * ξ).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    positivity
  have harg : ((3 : ℂ) * ξ).arg ≠ π := by
    intro h
    rw [Complex.arg_eq_pi_iff] at h
    linarith [h3re, h.1]
  have hcp := congr_arg (starRingEnd ℂ) (Complex.cpow_conj ((3 : ℂ) * ξ) (1 / 2 : ℂ) harg)
  simp only [Complex.conj_conj, map_mul, map_div₀, map_one, map_ofNat] at hcp
  exact hcp.symm

lemma virasoroBOfXi_analyticAt {ξ : ℂ} (hre : 0 < ξ.re) :
    AnalyticAt ℂ virasoroBOfXi ξ := by
  unfold virasoroBOfXi
  have h3re : 0 < ((3 : ℂ) * ξ).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    positivity
  exact (analyticAt_const.mul analyticAt_id).cpow analyticAt_const
    (Complex.mem_slitPlane_iff.mpr (Or.inl h3re))

lemma virasoroBOfXi_hasDerivAt_xiBar :
    HasDerivAt virasoroBOfXi (3 / (2 * (xiStar : ℂ))) (xiBar : ℂ) := by
  unfold virasoroBOfXi
  have h3xi : ((3 : ℂ) * (xiBar : ℂ)) = ((xiStar ^ 2 : ℝ) : ℂ) := by
    unfold xiBar; push_cast; ring
  have h3re : 0 < ((3 : ℂ) * (xiBar : ℂ)).re := by
    rw [h3xi, Complex.ofReal_re]; exact sq_pos_of_pos xiStar_pos
  have hsp : (3 : ℂ) * (xiBar : ℂ) ∈ slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl h3re)
  have hlin : HasDerivAt (fun ξ : ℂ => (3 : ℂ) * ξ) 3 (xiBar : ℂ) := by
    simpa using (hasDerivAt_id (xiBar : ℂ)).const_mul (3 : ℂ)
  have hcp := HasDerivAt.cpow_const hlin hsp (c := (1 / 2 : ℂ))
  have hpow : ((3 : ℂ) * (xiBar : ℂ)) ^ (1 / 2 - 1 : ℂ) = ((xiStar : ℂ))⁻¹ := by
    rw [h3xi, show (1 / 2 - 1 : ℂ) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow (sq_nonneg xiStar), Real.rpow_neg (sq_nonneg xiStar),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq xiStar_pos.le]
    push_cast; rfl
  refine hcp.congr_deriv ?_
  rw [hpow]
  ring

/-- The infinite-`c'` Langer chart `u_∞(ξ) = β (ξ_* - b(ξ)) A(b(ξ) - ξ_*)^{2/3}`
constructed from `TipFront.lemmaGPotentialInput_virasoro`. -/
noncomputable def virasoroUInf (ξ : ℂ) : ℂ :=
  let pg := TipFront.lemmaGPotentialInput_virasoro
  let b := virasoroBOfXi ξ
  (betaTip : ℂ) * ((xiStar : ℂ) - b) * (pg.A (b - (xiStar : ℂ))) ^ (2 / 3 : ℂ)

lemma virasoroUInf_xiBar : virasoroUInf (xiBar : ℂ) = 0 := by
  unfold virasoroUInf
  dsimp only
  rw [virasoroBOfXi_xiBar, sub_self, mul_zero, zero_mul]

lemma virasoroUInf_hasDerivAt_xiBar :
    HasDerivAt virasoroUInf (-(1 / (cStar : ℂ))) (xiBar : ℂ) := by
  let pg := TipFront.lemmaGPotentialInput_virasoro
  let f : ℂ → ℂ := fun ξ => (betaTip : ℂ) * ((xiStar : ℂ) - virasoroBOfXi ξ)
  let g : ℂ → ℂ := fun ξ => (pg.A (virasoroBOfXi ξ - (xiStar : ℂ))) ^ (2 / 3 : ℂ)
  have hf_at : f (xiBar : ℂ) = 0 := by dsimp [f]; rw [virasoroBOfXi_xiBar, sub_self, mul_zero]
  have hg_at : g (xiBar : ℂ) = 1 := by
    dsimp [g]; rw [virasoroBOfXi_xiBar, sub_self, pg.hA_0, Complex.one_cpow]
  have hf_deriv : HasDerivAt f (-(betaTip : ℂ) * (3 / (2 * (xiStar : ℂ)))) (xiBar : ℂ) := by
    have h1 := ((hasDerivAt_const (xiBar : ℂ) (xiStar : ℂ)).sub virasoroBOfXi_hasDerivAt_xiBar).const_mul (betaTip : ℂ)
    refine h1.congr_deriv ?_
    ring
  have hg_diff : DifferentiableAt ℂ g (xiBar : ℂ) := by
    have hA_an : AnalyticAt ℂ pg.A 0 := pg.hA_an 0 (mem_ball_self pg.hr_A_pos)
    have hcomp : AnalyticAt ℂ (fun ξ => pg.A (virasoroBOfXi ξ - (xiStar : ℂ))) (xiBar : ℂ) := by
      refine hA_an.comp_of_eq (AnalyticAt.sub (virasoroBOfXi_analyticAt ?_) analyticAt_const) ?_
      · rw [Complex.ofReal_re]; unfold xiBar; positivity [xiStar_pos]
      · rw [virasoroBOfXi_xiBar, sub_self]
    have hsp : pg.A (virasoroBOfXi (xiBar : ℂ) - (xiStar : ℂ)) ∈ slitPlane := by
      rw [virasoroBOfXi_xiBar, sub_self, pg.hA_0]
      exact Complex.one_mem_slitPlane
    exact (AnalyticAt.cpow hcomp analyticAt_const hsp).differentiableAt
  have hmul : HasDerivAt (fun ξ => f ξ * g ξ)
      ((-(betaTip : ℂ) * (3 / (2 * (xiStar : ℂ)))) * 1 + 0 * deriv g (xiBar : ℂ)) (xiBar : ℂ) := by
    have hm := HasDerivAt.mul hf_deriv hg_diff.hasDerivAt
    rw [hf_at, hg_at] at hm
    exact hm
  refine hmul.congr_deriv ?_
  have hc_eq : (betaTip : ℂ) * (3 / (2 * (xiStar : ℂ))) = 1 / (cStar : ℂ) := by
    unfold cStar
    have hxi : (xiStar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr xiStar_pos.ne'
    have hbt : (betaTip : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr betaTip_pos.ne'
    push_cast; field_simp
  rw [zero_mul, add_zero, mul_one, ← hc_eq]
  ring

/-! ### Section 2: Analytic neighborhood and local inverse `virasoroXiInf` -/

structure LangerChartCore where
  r_xi : ℝ
  r_u : ℝ
  hr_xi_pos : 0 < r_xi
  hr_xi_half : r_xi ≤ xiBar / 2
  hr_u_pos : 0 < r_u
  huInf_an : AnalyticOnNhd ℂ virasoroUInf (ball (xiBar : ℂ) r_xi)
  huInf_real_pos : ∀ ξ : ℂ, ξ ∈ ball (xiBar : ℂ) r_xi →
    0 < ξ.re ∧
    ‖virasoroBOfXi ξ - (xiStar : ℂ)‖ < TipFront.lemmaGPotentialInput_virasoro.r_A / 2 ∧
    0 < (TipFront.lemmaGPotentialInput_virasoro.A (virasoroBOfXi ξ - (xiStar : ℂ))).re
  huInf_inj : InjOn virasoroUInf (ball (xiBar : ℂ) r_xi)
  xiInf : ℂ → ℂ
  hxiInf_an : AnalyticOnNhd ℂ xiInf (ball (0 : ℂ) r_u)
  hxiInf_zero : xiInf 0 = (xiBar : ℂ)
  hxiInf_deriv : deriv xiInf 0 = -(cStar : ℂ)
  hxiInf_mem : ∀ u ∈ ball (0 : ℂ) r_u, xiInf u ∈ ball (xiBar : ℂ) r_xi
  hxiInf_right : ∀ u ∈ ball (0 : ℂ) r_u, virasoroUInf (xiInf u) = u
  hxiInf_left : ∀ ξ ∈ ball (xiBar : ℂ) r_xi, xiInf (virasoroUInf ξ) = ξ

lemma langerChartCore_exists : Nonempty LangerChartCore := by
  let pg := TipFront.lemmaGPotentialInput_virasoro
  have hxiBar_pos : 0 < xiBar := by unfold xiBar; positivity [xiStar_pos]
  have hcont_b : ContinuousAt virasoroBOfXi (xiBar : ℂ) :=
    (virasoroBOfXi_analyticAt (by simpa using hxiBar_pos)).continuousAt
  have hev_re : ∀ᶠ ξ in 𝓝 (xiBar : ℂ), 0 < ξ.re :=
    Complex.continuous_re.continuousAt.eventually (Ioi_mem_nhds hxiBar_pos)
  have hev_ball : ∀ᶠ ξ in 𝓝 (xiBar : ℂ), ‖virasoroBOfXi ξ - (xiStar : ℂ)‖ < pg.r_A / 2 := by
    have hc : ContinuousAt (fun ξ => ‖virasoroBOfXi ξ - (xiStar : ℂ)‖) (xiBar : ℂ) :=
      (hcont_b.sub continuousAt_const).norm
    rw [ContinuousAt, virasoroBOfXi_xiBar, sub_self, norm_zero] at hc
    exact hc (Iio_mem_nhds (half_pos pg.hr_A_pos))
  have hev_Are : ∀ᶠ ξ in 𝓝 (xiBar : ℂ),
      0 < (pg.A (virasoroBOfXi ξ - (xiStar : ℂ))).re := by
    have hA_cont : ContinuousAt pg.A 0 := (pg.hA_an 0 (mem_ball_self pg.hr_A_pos)).continuousAt
    have hc : ContinuousAt (fun ξ => (pg.A (virasoroBOfXi ξ - (xiStar : ℂ))).re) (xiBar : ℂ) :=
      Complex.continuous_re.continuousAt.comp (hA_cont.comp_of_eq (hcont_b.sub continuousAt_const)
        (by rw [virasoroBOfXi_xiBar, sub_self]))
    rw [ContinuousAt, virasoroBOfXi_xiBar, sub_self, pg.hA_0, Complex.one_re] at hc
    exact hc (Ioi_mem_nhds one_pos)
  obtain ⟨r₁, hr₁_pos, hb₁⟩ := Metric.eventually_nhds_iff_ball.mp (hev_re.and (hev_ball.and hev_Are))
  let r_xi0 : ℝ := min r₁ (xiBar / 2)
  have hr_xi0_pos : 0 < r_xi0 := lt_min hr₁_pos (half_pos hxiBar_pos)
  have huInf_an0 : AnalyticOnNhd ℂ virasoroUInf (ball (xiBar : ℂ) r_xi0) := fun ξ hξ => by
    have hξ₁ : ξ ∈ ball (xiBar : ℂ) r₁ := ball_subset_ball (min_le_left _ _) hξ
    obtain ⟨hre, hball, hAre⟩ := hb₁ ξ hξ₁
    have hA_an : AnalyticAt ℂ pg.A (virasoroBOfXi ξ - (xiStar : ℂ)) :=
      pg.hA_an _ (mem_ball_zero_iff.mpr (hball.trans (half_lt_self pg.hr_A_pos)))
    have hsub_an : AnalyticAt ℂ (fun w => virasoroBOfXi w - (xiStar : ℂ)) ξ :=
      AnalyticAt.sub (virasoroBOfXi_analyticAt hre) analyticAt_const
    have hcomp : AnalyticAt ℂ (fun w => pg.A (virasoroBOfXi w - (xiStar : ℂ))) ξ :=
      hA_an.comp_of_eq hsub_an rfl
    have hpow : AnalyticAt ℂ (fun w => (pg.A (virasoroBOfXi w - (xiStar : ℂ))) ^ (2 / 3 : ℂ)) ξ :=
      AnalyticAt.cpow hcomp analyticAt_const (Complex.mem_slitPlane_iff.mpr (Or.inl hAre))
    have hlin : AnalyticAt ℂ (fun w => (betaTip : ℂ) * ((xiStar : ℂ) - virasoroBOfXi w)) ξ :=
      analyticAt_const.mul (analyticAt_const.sub (virasoroBOfXi_analyticAt hre))
    exact AnalyticAt.mul hlin hpow
  have hd0_eq : deriv virasoroUInf (xiBar : ℂ) = -(1 / (cStar : ℂ)) :=
    virasoroUInf_hasDerivAt_xiBar.deriv
  have hd_ne : deriv virasoroUInf (xiBar : ℂ) ≠ 0 := by
    rw [hd0_eq]
    exact neg_ne_zero.mpr (one_div_ne_zero (Complex.ofReal_ne_zero.mpr cStar_pos.ne'))
  have huInf_an_xiBar : AnalyticAt ℂ virasoroUInf (xiBar : ℂ) :=
    huInf_an0 (xiBar : ℂ) (mem_ball_self hr_xi0_pos)
  have hstrict := huInf_an_xiBar.hasStrictDerivAt
  let xiInf : ℂ → ℂ := hstrict.localInverse virasoroUInf (deriv virasoroUInf (xiBar : ℂ)) (xiBar : ℂ) hd_ne
  have hxiInf_an0 : AnalyticAt ℂ xiInf 0 := by
    have hinv := huInf_an_xiBar.analyticAt_localInverse hd_ne
    rw [virasoroUInf_xiBar] at hinv
    exact hinv
  obtain ⟨r_inv, hr_inv_pos, hr_inv_an⟩ := hxiInf_an0.exists_ball_analyticOnNhd
  have hright := hstrict.eventually_right_inverse hd_ne
  rw [virasoroUInf_xiBar] at hright
  have hleft := hstrict.eventually_left_inverse hd_ne
  have hxiInf_zero : xiInf 0 = (xiBar : ℂ) := by
    have h0 := hleft.self_of_nhds
    rw [virasoroUInf_xiBar] at h0
    exact h0
  have hcont_xi : ContinuousAt xiInf 0 := hxiInf_an0.continuousAt
  rw [ContinuousAt, hxiInf_zero] at hcont_xi
  obtain ⟨r_xi_l, hr_xi_l_pos, hb_left⟩ := Metric.eventually_nhds_iff_ball.mp hleft
  let r_xi : ℝ := min r_xi0 r_xi_l
  have hr_xi_pos : 0 < r_xi := lt_min hr_xi0_pos hr_xi_l_pos
  have huInf_inj : InjOn virasoroUInf (ball (xiBar : ℂ) r_xi) := by
    intro ξ₁ h₁ ξ₂ h₂ heq
    have hl₁ := hb_left ξ₁ (ball_subset_ball (min_le_right _ _) h₁)
    have hl₂ := hb_left ξ₂ (ball_subset_ball (min_le_right _ _) h₂)
    rw [← hl₁, ← hl₂, heq]
  have hev_u : ∀ᶠ u in 𝓝 (0 : ℂ),
      u ∈ ball (0 : ℂ) r_inv ∧ xiInf u ∈ ball (xiBar : ℂ) r_xi ∧ virasoroUInf (xiInf u) = u :=
    Filter.Eventually.and (Metric.ball_mem_nhds 0 hr_inv_pos)
      (Filter.Eventually.and (hcont_xi.eventually (Metric.ball_mem_nhds (xiBar : ℂ) hr_xi_pos))
        hright)
  obtain ⟨r_u, hr_u_pos, hb_u⟩ := Metric.eventually_nhds_iff_ball.mp hev_u
  have hxiInf_deriv : deriv xiInf 0 = -(cStar : ℂ) := by
    have hd := (hstrict.to_localInverse hd_ne).hasDerivAt
    rw [virasoroUInf_xiBar] at hd
    rw [hd.deriv, hd0_eq]
    have hc : (cStar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr cStar_pos.ne'
    field_simp
  exact ⟨{
    r_xi := r_xi
    r_u := r_u
    hr_xi_pos := hr_xi_pos
    hr_xi_half := (min_le_left _ _).trans (min_le_right _ _)
    hr_u_pos := hr_u_pos
    huInf_an := huInf_an0.mono (ball_subset_ball (min_le_left _ _))
    huInf_real_pos := fun ξ hξ => hb₁ ξ (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hξ)
    huInf_inj := huInf_inj
    xiInf := xiInf
    hxiInf_an := fun u hu => hr_inv_an u (hb_u u hu).1
    hxiInf_zero := hxiInf_zero
    hxiInf_deriv := hxiInf_deriv
    hxiInf_mem := fun u hu => (hb_u u hu).2.1
    hxiInf_right := fun u hu => (hb_u u hu).2.2
    hxiInf_left := fun ξ hξ => hb_left ξ (ball_subset_ball (min_le_right _ _) hξ)
  }⟩

noncomputable def langerCore : LangerChartCore :=
  Classical.choice langerChartCore_exists

/-- Analytic local inverse `ξ_∞(w)` of `virasoroUInf` on `ball 0 virasoroRUInf`. -/
noncomputable def virasoroXiInf : ℂ → ℂ := langerCore.xiInf

/-- Radius of the `w`-disc for `virasoroXiInf`. -/
noncomputable def virasoroRUInf : ℝ := langerCore.r_u

/-- Radius of the `ξ`-disc around `ξ̄` for `virasoroUInf`. -/
noncomputable def virasoroRXiInf : ℝ := langerCore.r_xi

lemma virasoroRUInf_pos : 0 < virasoroRUInf := langerCore.hr_u_pos
lemma virasoroRXiInf_pos : 0 < virasoroRXiInf := langerCore.hr_xi_pos
lemma virasoroRXiInf_le_half : virasoroRXiInf ≤ xiBar / 2 := langerCore.hr_xi_half

lemma virasoroXiInf_an : AnalyticOnNhd ℂ virasoroXiInf (ball (0 : ℂ) virasoroRUInf) :=
  langerCore.hxiInf_an

lemma virasoroUInf_an : AnalyticOnNhd ℂ virasoroUInf (ball (xiBar : ℂ) virasoroRXiInf) :=
  langerCore.huInf_an

lemma virasoroXiInf_zero : virasoroXiInf 0 = (xiBar : ℂ) := langerCore.hxiInf_zero
lemma virasoroXiInf_deriv_zero : deriv virasoroXiInf 0 = -(cStar : ℂ) := langerCore.hxiInf_deriv

lemma virasoroXiInf_mem {w : ℂ} (hw : w ∈ ball (0 : ℂ) virasoroRUInf) :
    virasoroXiInf w ∈ ball (xiBar : ℂ) virasoroRXiInf :=
  langerCore.hxiInf_mem w hw

lemma virasoroUInf_xiInf {w : ℂ} (hw : w ∈ ball (0 : ℂ) virasoroRUInf) :
    virasoroUInf (virasoroXiInf w) = w :=
  langerCore.hxiInf_right w hw

lemma virasoroXiInf_uInf {ξ : ℂ} (hξ : ξ ∈ ball (xiBar : ℂ) virasoroRXiInf) :
    virasoroXiInf (virasoroUInf ξ) = ξ :=
  langerCore.hxiInf_left ξ hξ

lemma virasoroUInf_conj {ξ : ℂ} (hξ : ξ ∈ ball (xiBar : ℂ) virasoroRXiInf) :
    virasoroUInf (starRingEnd ℂ ξ) = starRingEnd ℂ (virasoroUInf ξ) := by
  let pg := TipFront.lemmaGPotentialInput_virasoro
  have hξ_conj : starRingEnd ℂ ξ ∈ ball (xiBar : ℂ) virasoroRXiInf := by
    rw [mem_ball, dist_eq_norm, show (xiBar : ℂ) = starRingEnd ℂ (xiBar : ℂ) by simp,
      ← map_sub, Complex.norm_conj]
    rwa [mem_ball, dist_eq_norm] at hξ
  obtain ⟨hre, hball, hAre⟩ := langerCore.huInf_real_pos ξ hξ
  have hA_conj : ∀ z ∈ ball (0 : ℂ) pg.r_A, pg.A (starRingEnd ℂ z) = starRingEnd ℂ (pg.A z) := by
    let g : ℂ → ℂ := fun z => starRingEnd ℂ (pg.A (starRingEnd ℂ z))
    have hg_diff : DifferentiableOn ℂ g (ball (0 : ℂ) pg.r_A) := fun z hz => by
      have hz_c : starRingEnd ℂ z ∈ ball (0 : ℂ) pg.r_A := by
        simpa [mem_ball, dist_zero_right, Complex.norm_conj] using hz
      have hd := (pg.hA_an _ hz_c).differentiableAt.conj_conj
      change DifferentiableWithinAt ℂ (fun w => starRingEnd ℂ (pg.A (starRingEnd ℂ w)))
        (ball (0 : ℂ) pg.r_A) z
      rw [Complex.conj_conj] at hd
      have heq_fn : (fun w => starRingEnd ℂ (pg.A (starRingEnd ℂ w))) =
          (starRingEnd ℂ ∘ pg.A ∘ starRingEnd ℂ) := rfl
      rw [heq_fn]
      exact hd.differentiableWithinAt
    have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), pg.A z = g z := by
      rw [Filter.frequently_iff]
      intro U hU
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU
      obtain ⟨V, hV, hVU⟩ := hU
      obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.mem_nhds_iff.mp hV
      let x : ℝ := min (δ / 2) (pg.r_A / 2)
      have hx_pos : 0 < x := lt_min (half_pos hδ_pos) (half_pos pg.hr_A_pos)
      refine ⟨(x : ℂ), hVU ⟨hδ_ball ?_, Complex.ofReal_ne_zero.mpr hx_pos.ne'⟩, ?_⟩
      · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos]
        exact (min_le_left _ _).trans_lt (half_lt_self hδ_pos)
      · dsimp [g]
        rw [Complex.conj_ofReal]
        exact (Complex.conj_eq_iff_im.mpr (pg.hA_real x
          (by rw [abs_of_pos hx_pos]; exact (min_le_right _ _).trans_lt (half_lt_self pg.hr_A_pos)))).symm
    have heq := pg.hA_an.eqOn_of_preconnected_of_frequently_eq
      (hg_diff.analyticOnNhd isOpen_ball) (convex_ball (0 : ℂ) pg.r_A).isPreconnected
      (mem_ball_self pg.hr_A_pos) hfreq
    intro z hz
    have heq_z := congr_arg (starRingEnd ℂ) (heq hz)
    dsimp [g] at heq_z
    rw [Complex.conj_conj] at heq_z
    exact heq_z.symm
  have hb_conj := virasoroBOfXi_conj hre
  have hsub_mem : virasoroBOfXi ξ - (xiStar : ℂ) ∈ ball (0 : ℂ) pg.r_A :=
    mem_ball_zero_iff.mpr (hball.trans (half_lt_self pg.hr_A_pos))
  have hA_eq : pg.A (virasoroBOfXi (starRingEnd ℂ ξ) - (xiStar : ℂ)) =
      starRingEnd ℂ (pg.A (virasoroBOfXi ξ - (xiStar : ℂ))) := by
    rw [hb_conj, show starRingEnd ℂ (virasoroBOfXi ξ) - (xiStar : ℂ) =
      starRingEnd ℂ (virasoroBOfXi ξ - (xiStar : ℂ)) by simp]
    exact hA_conj _ hsub_mem
  have hargA : (pg.A (virasoroBOfXi ξ - (xiStar : ℂ))).arg ≠ π := by
    intro h
    rw [Complex.arg_eq_pi_iff] at h
    linarith [hAre, h.1]
  have hcp := congr_arg (starRingEnd ℂ)
    (Complex.cpow_conj (pg.A (virasoroBOfXi ξ - (xiStar : ℂ))) (2 / 3 : ℂ) hargA)
  simp only [Complex.conj_conj, map_div₀, map_ofNat] at hcp
  unfold virasoroUInf
  dsimp only
  dsimp only [pg] at hA_eq hcp
  rw [hA_eq, hb_conj, ← hcp, ← Complex.conj_ofReal xiStar,
    ← Complex.conj_ofReal betaTip, ← map_sub, ← map_mul, ← map_mul]
  simp only [Complex.conj_ofReal]

lemma virasoroXiInf_conj {w : ℂ} (hw : w ∈ ball (0 : ℂ) virasoroRUInf) :
    virasoroXiInf (starRingEnd ℂ w) = starRingEnd ℂ (virasoroXiInf w) := by
  have hw_conj : starRingEnd ℂ w ∈ ball (0 : ℂ) virasoroRUInf := by
    simpa [mem_ball, dist_zero_right, Complex.norm_conj] using hw
  have h1 : virasoroXiInf w ∈ ball (xiBar : ℂ) virasoroRXiInf := virasoroXiInf_mem hw
  have h2 : virasoroXiInf (starRingEnd ℂ w) ∈ ball (xiBar : ℂ) virasoroRXiInf := virasoroXiInf_mem hw_conj
  have h3 : starRingEnd ℂ (virasoroXiInf w) ∈ ball (xiBar : ℂ) virasoroRXiInf := by
    rw [mem_ball, dist_eq_norm, show (xiBar : ℂ) = starRingEnd ℂ (xiBar : ℂ) by simp,
      ← map_sub, Complex.norm_conj]
    rwa [mem_ball, dist_eq_norm] at h1
  apply langerCore.huInf_inj h2 h3
  rw [virasoroUInf_xiInf hw_conj, virasoroUInf_conj h1, virasoroUInf_xiInf hw]

lemma virasoroXiInf_ofReal_im {x : ℝ} (hx : |x| < virasoroRUInf) :
    (virasoroXiInf (x : ℂ)).im = 0 := by
  have hx_ball : (x : ℂ) ∈ ball (0 : ℂ) virasoroRUInf := by
    simpa [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using hx
  have h := virasoroXiInf_conj hx_ball
  rw [Complex.conj_ofReal] at h
  have him := congrArg Complex.im h.symm
  rw [Complex.conj_im] at him
  linarith

lemma virasoroUInf_ofReal_im' {ξ : ℝ} (hξ : |ξ - xiBar| < virasoroRXiInf) :
    (virasoroUInf (ξ : ℂ)).im = 0 := by
  have hξ_ball : (ξ : ℂ) ∈ ball (xiBar : ℂ) virasoroRXiInf := by
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hξ
  have h := virasoroUInf_conj hξ_ball
  rw [Complex.conj_ofReal] at h
  have him := congrArg Complex.im h.symm
  rw [Complex.conj_im] at him
  linarith

/-! ### Section 3: Quadratic Taylor helper, selecting `b_V`, and tip comparability -/

private lemma analytic_quadratic_remainder {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (ball z₀ r)) :
    ∃ C ≥ 0, ∀ z ∈ closedBall z₀ (r / 2),
      ‖f z - f z₀ - deriv f z₀ * (z - z₀)‖ ≤ C * ‖z - z₀‖ ^ 2 := by
  let g₁ : ℂ → ℂ := dslope f z₀
  have hg₁_an : AnalyticOnNhd ℂ g₁ (ball z₀ r) :=
    ((differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hr))).mpr
      hf.differentiableOn).analyticOnNhd isOpen_ball
  let g₂ : ℂ → ℂ := dslope g₁ z₀
  have hg₂_an : AnalyticOnNhd ℂ g₂ (ball z₀ r) :=
    ((differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self hr))).mpr
      hg₁_an.differentiableOn).analyticOnNhd isOpen_ball
  obtain ⟨M, hM⟩ := (isCompact_closedBall z₀ (r / 2)).exists_bound_of_continuousOn
    (hg₂_an.continuousOn.mono (closedBall_subset_ball (half_lt_self hr)))
  refine ⟨max M 0, le_max_right _ _, fun z hz => ?_⟩
  have h1 := sub_smul_dslope f z₀ z
  have h2 := sub_smul_dslope g₁ z₀ z
  have hg1_at : g₁ z₀ = deriv f z₀ := dslope_same f z₀
  rw [hg1_at, smul_eq_mul] at h2
  rw [smul_eq_mul] at h1
  have hid : f z - f z₀ - deriv f z₀ * (z - z₀) = (z - z₀) ^ 2 * g₂ z := by
    calc f z - f z₀ - deriv f z₀ * (z - z₀)
        = (z - z₀) * (g₁ z - deriv f z₀) := by rw [← h1]; ring
      _ = (z - z₀) * ((z - z₀) * g₂ z) := by rw [h2]
      _ = (z - z₀) ^ 2 * g₂ z := by ring
  rw [hid, norm_mul, norm_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right ((hM z hz).trans (le_max_left _ _)) (sq_nonneg _)

private lemma cpow_half_of_sq_and_re_pos {z w : ℂ} (hsq : w ^ 2 = z) (hre : 0 < w.re) :
    z ^ (1 / 2 : ℂ) = w := by
  have h1 : (z ^ (1 / 2 : ℂ)) ^ 2 = w ^ 2 := by rw [cpow_half_sq, hsq]
  have hfac : (z ^ (1 / 2 : ℂ) - w) * (z ^ (1 / 2 : ℂ) + w) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp hfac with hsub | hadd
  · exact sub_eq_zero.mp hsub
  · exfalso
    have hsum_re : (z ^ (1 / 2 : ℂ) + w).re = 0 := by rw [hadd, Complex.zero_re]
    have hre1 : 0 ≤ (z ^ (1 / 2 : ℂ)).re := cpow_half_re_nonneg z
    rw [Complex.add_re] at hsum_re
    linarith

structure VirasoroChartParams where
  b_V : ℝ
  hbV_pos : 0 < b_V
  r_xi0 : ℝ
  hr_xi0_pos : 0 < r_xi0
  hr_xi0_le : r_xi0 ≤ virasoroRXiInf / 2
  h2bV2_lt : 2 * b_V ^ 2 < virasoroRUInf / 2
  C_b : ℝ
  hCb_pos : 0 < C_b
  hCb_bd : ∀ w ∈ closedBall (0 : ℂ) (2 * b_V ^ 2),
    ‖virasoroBOfXi (virasoroXiInf w) - (xiStar : ℂ)‖ ≤ C_b * ‖w‖
  C_xi : ℝ
  hCxi_nn : 0 ≤ C_xi
  hxi_err : ∀ w ∈ closedBall (0 : ℂ) (2 * b_V ^ 2),
    ‖virasoroXiInf w - ((xiBar : ℂ) - (cStar : ℂ) * w)‖ ≤ C_xi * ‖w‖ ^ 2
  M_u : ℝ
  hMu_nn : 0 ≤ M_u
  hu_err : ∀ ξ ∈ closedBall (xiBar : ℂ) r_xi0,
    ‖virasoroUInf ξ - ((1 / (cStar : ℂ)) * ((xiBar : ℂ) - ξ))‖ ≤ M_u * ‖ξ - (xiBar : ℂ)‖ ^ 2
  h_strictAnti_xi : ∀ x : ℝ, x ∈ Icc (-(2 * b_V ^ 2)) (2 * b_V ^ 2) →
    deriv (fun t : ℝ => (virasoroXiInf (t : ℂ)).re) x ≤ -cStar / 2
  h_strictAnti_u : ∀ ξ : ℝ, ξ ∈ Icc (xiBar - r_xi0) (xiBar + r_xi0) →
    deriv (fun t : ℝ => (virasoroUInf (t : ℂ)).re) ξ ≤ -1 / (2 * cStar)
  h_u_range : ∀ x : ℝ, x ∈ Icc (-(2 * b_V ^ 2)) (2 * b_V ^ 2) →
    |(virasoroXiInf (x : ℂ)).re - xiBar| ≤ r_xi0
  h_b_range : ∀ w ∈ closedBall (0 : ℂ) (2 * b_V ^ 2),
    ‖virasoroBOfXi (virasoroXiInf w) - (xiStar : ℂ)‖ ≤
      min (TipFront.lemmaGPotentialInput_virasoro.r_A / 2) (min 0.05 (xiStar / 4))
  h_b_T1 : ∀ w ∈ closedBall (0 : ℂ) (2 * b_V ^ 2),
    ‖virasoroBOfXi (virasoroXiInf w) - (xiStar : ℂ)‖ ≤
      min (TipFront.lemmaGPotentialInput_virasoro.r_A / 2) 0.1
  ρ₁_tip : ℝ
  C_T1_tip : ℝ
  ψ_tip : ℂ → ℂ
  ρ₃_tip : ℝ
  C_W_tip : ℝ
  hρ₁_tip_pos : 0 < ρ₁_tip
  hCT1_tip_nn : 0 ≤ C_T1_tip
  hρ₃_tip_pos : 0 < ρ₃_tip
  hCW_tip_nn : 0 ≤ C_W_tip
  hT1_tip : ∀ {c' : ℝ} {ζ : ℂ}, 0 < c' → ¬ (ζ.im = 0 ∧ 0 ≤ ζ.re) →
    tipEps c' * ‖ζ‖ ≤ ρ₁_tip →
    let ε := tipEps c'
    let v := I * ((√ε : ℝ) : ℂ) * (-ζ) ^ (1 / 2 : ℂ)
    let z_b := (sigmaStar : ℂ) + ψ_tip v
    ‖v‖ = √(ε * ‖ζ‖) ∧
    0 < z_b.im ∧
    ‖z_b - (sigmaStar : ℂ)‖ ≤ 0.1 ∧
    slitBoundaryMapC z_b = bScale c' ζ ∧
    (∀ w : ℂ, 0 < w.im → slitBoundaryMapC w = bScale c' ζ → w = z_b) ∧
    |z_b.im - √(ε / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re| ≤
      C_T1_tip * √(ε * ‖ζ‖) * (√(ε / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re) ∧
    |‖z_b - (sigmaStar : ℂ)‖ - √(ε * ‖ζ‖ / slitQ)| ≤
      C_T1_tip * √(ε * ‖ζ‖) * √(ε * ‖ζ‖ / slitQ) ∧
    |z_b.im * ‖z_b - (sigmaStar : ℂ)‖ - (ε / slitQ) * tipDist ζ| ≤
      C_T1_tip * √(ε * ‖ζ‖) * ((ε / slitQ) * tipDist ζ)
  hT3_tip : ∀ {c' : ℝ} {ζ : ℂ}, 39 ≤ c' → tipEps c' * ‖ζ‖ ≤ ρ₃_tip →
    let b := bScale c' ζ
    ‖W_C c' b - (kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖ ≤
      C_W_tip * (tipEps c' * (1 + ‖ζ‖) + 1 / c') *
        ‖(kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖
  C_dxi : ℝ
  hCdxi_pos : 0 < C_dxi
  hdxi_bd : ∀ w ∈ closedBall (0 : ℂ) (2 * b_V ^ 2), ‖deriv virasoroXiInf w‖ ≤ C_dxi
  h_b_tip_cap : ∀ w ∈ closedBall (0 : ℂ) (2 * b_V ^ 2),
    ‖virasoroBOfXi (virasoroXiInf w) - (xiStar : ℂ)‖ ≤
      min ρ₁_tip (min ρ₃_tip (min (1 / (4 * (C_T1_tip + 1) ^ 2)) (1 / (6 * (C_W_tip + 1)))))
  c_tip_lo : ℝ
  c_tip_hi : ℝ
  hc_tip_lo_pos : 0 < c_tip_lo
  hc_tip_hi_pos : 0 < c_tip_hi
  r_open_cap : ℝ
  hr_open_cap_gt : 2 * b_V ^ 2 < r_open_cap
  hr_open_cap_lt_u : r_open_cap < virasoroRUInf
  h_tip_comp : ∀ w ∈ ball (0 : ℂ) r_open_cap, ¬ (w.im = 0 ∧ w.re ≤ 0) →
    let mz := (xiStar : ℂ) - virasoroBOfXi (virasoroXiInf w)
    c_tip_lo * (w ^ (1 / 2 : ℂ)).re ≤ (mz ^ (1 / 2 : ℂ)).re ∧
    (mz ^ (1 / 2 : ℂ)).re ≤ c_tip_hi * (w ^ (1 / 2 : ℂ)).re ∧
    c_tip_lo * ‖w‖ ≤ ‖mz‖ ∧ ‖mz‖ ≤ c_tip_hi * ‖w‖
  hbOfW_real : ∀ x : ℝ, |x| < r_open_cap → (virasoroBOfXi (virasoroXiInf (x : ℂ))).im = 0 ∧
    0 < (virasoroBOfXi (virasoroXiInf (x : ℂ))).re ∧
    |((virasoroBOfXi (virasoroXiInf (x : ℂ))).re - xiStar)| <
      TipFront.lemmaGPotentialInput_virasoro.r_A ∧
    0 < (TipFront.lemmaGPotentialInput_virasoro.A
      (virasoroBOfXi (virasoroXiInf (x : ℂ)) - (xiStar : ℂ))).re

lemma virasoroChartParams_exists : Nonempty VirasoroChartParams := by
  let pg := TipFront.lemmaGPotentialInput_virasoro
  obtain ⟨ρ₁_tip, C_T1_tip, ψ_tip, hρ₁_tip_pos, hCT1_tip_nn, _, _, _, _, hT1_tip⟩ := lemma_T1
  obtain ⟨ρ₃_tip, C_W_tip, hρ₃_tip_pos, hCW_tip_nn, hT3_tip⟩ :=
    lemma_T3_W_bound ComplexBessel.besselI0Asymptotic
  obtain ⟨M_dxi, hMdxi⟩ := (isCompact_closedBall (0 : ℂ) (virasoroRUInf / 2)).exists_bound_of_continuousOn
    (virasoroXiInf_an.deriv.continuousOn.mono (closedBall_subset_ball (half_lt_self virasoroRUInf_pos)))
  let C_dxi : ℝ := max M_dxi 1
  have hCdxi_pos : 0 < C_dxi := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let bOfW : ℂ → ℂ := fun w => virasoroBOfXi (virasoroXiInf w)
  have hbOfW_an : AnalyticOnNhd ℂ bOfW (ball (0 : ℂ) virasoroRUInf) := fun w hw => by
    have hmem := virasoroXiInf_mem hw
    have hre := (langerCore.huInf_real_pos _ hmem).1
    exact (virasoroBOfXi_analyticAt hre).comp_of_eq (virasoroXiInf_an w hw) rfl
  have hbOfW_0 : bOfW 0 = (xiStar : ℂ) := by
    dsimp [bOfW]; rw [virasoroXiInf_zero, virasoroBOfXi_xiBar]
  have hbOfW_deriv0 : deriv bOfW 0 = -(1 / (betaTip : ℂ)) := by
    have h1 : HasDerivAt virasoroXiInf (-(cStar : ℂ)) 0 := by
      rw [← virasoroXiInf_deriv_zero]
      exact (virasoroXiInf_an 0 (mem_ball_self virasoroRUInf_pos)).differentiableAt.hasDerivAt
    have h2 : HasDerivAt virasoroBOfXi (3 / (2 * (xiStar : ℂ))) (xiBar : ℂ) :=
      virasoroBOfXi_hasDerivAt_xiBar
    have hcomp : HasDerivAt bOfW ((3 / (2 * (xiStar : ℂ))) * (-(cStar : ℂ))) 0 :=
      h2.comp_of_eq 0 h1 virasoroXiInf_zero.symm
    rw [hcomp.deriv]
    unfold cStar
    have hxi : (xiStar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr xiStar_pos.ne'
    have hbt : (betaTip : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr betaTip_pos.ne'
    push_cast; field_simp
  -- Quadratic remainders
  obtain ⟨C_xi, hCxi_nn, hRxi_bd⟩ := analytic_quadratic_remainder virasoroRUInf_pos virasoroXiInf_an
  obtain ⟨M_u, hMu_nn, hRu_bd⟩ := analytic_quadratic_remainder virasoroRXiInf_pos virasoroUInf_an
  have hRxi_bd' : ∀ w ∈ closedBall (0 : ℂ) (virasoroRUInf / 2),
      ‖virasoroXiInf w - ((xiBar : ℂ) - (cStar : ℂ) * w)‖ ≤ C_xi * ‖w‖ ^ 2 := by
    intro w hw
    have h := hRxi_bd w hw
    rw [virasoroXiInf_zero, virasoroXiInf_deriv_zero, sub_zero] at h
    refine le_trans (le_of_eq ?_) h
    congr 1; ring
  have hRu_bd' : ∀ ξ ∈ closedBall (xiBar : ℂ) (virasoroRXiInf / 2),
      ‖virasoroUInf ξ - ((1 / (cStar : ℂ)) * ((xiBar : ℂ) - ξ))‖ ≤ M_u * ‖ξ - (xiBar : ℂ)‖ ^ 2 := by
    intro ξ hξ
    have h := hRu_bd ξ hξ
    rw [virasoroUInf_xiBar, virasoroUInf_hasDerivAt_xiBar.deriv, sub_zero] at h
    refine le_trans (le_of_eq ?_) h
    congr 1; ring
  -- `bOfW` Lipschitz bound on `closedBall 0 (virasoroRUInf / 2)`
  obtain ⟨M_b0, hMb0⟩ := (isCompact_closedBall (0 : ℂ) (virasoroRUInf / 2)).exists_bound_of_continuousOn
    (hbOfW_an.deriv.continuousOn.mono (closedBall_subset_ball (half_lt_self virasoroRUInf_pos)))
  let C_b : ℝ := max M_b0 1
  have hCb_pos : 0 < C_b := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbOfW_lip : ∀ w ∈ closedBall (0 : ℂ) (virasoroRUInf / 2),
      ‖bOfW w - (xiStar : ℂ)‖ ≤ C_b * ‖w‖ := fun w hw => by
    have hmvt := (convex_closedBall (0 : ℂ) (virasoroRUInf / 2)).norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hbOfW_an z (closedBall_subset_ball (half_lt_self virasoroRUInf_pos) hz)).differentiableAt)
      (fun z hz => (hMb0 z hz).trans (le_max_left M_b0 1))
      (mem_closedBall_self (half_pos virasoroRUInf_pos).le) hw
    rw [hbOfW_0, sub_zero] at hmvt
    exact hmvt
  -- Derivative bounds on `xiInf` and `uInf` near `0` and `xiBar`
  have hcont_dxi : ContinuousAt (fun x : ℝ => (deriv virasoroXiInf (x : ℂ)).re) 0 := by
    have h1 : ContinuousAt (deriv virasoroXiInf) ((0 : ℝ) : ℂ) :=
      (virasoroXiInf_an.deriv 0 (mem_ball_self virasoroRUInf_pos)).continuousAt
    exact Complex.continuous_re.continuousAt.comp
      (ContinuousAt.comp h1 (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))))
  have hdxi0 : (deriv virasoroXiInf (0 : ℂ)).re = -cStar := by
    rw [virasoroXiInf_deriv_zero, Complex.neg_re, Complex.ofReal_re]
  have hev_dxi : ∀ᶠ x : ℝ in 𝓝 0, (deriv virasoroXiInf (x : ℂ)).re ≤ -cStar / 2 := by
    refine hcont_dxi.eventually (Iic_mem_nhds ?_)
    have hval : (deriv virasoroXiInf ((0 : ℝ) : ℂ)).re = -cStar := by
      rw [Complex.ofReal_zero]; exact hdxi0
    change (deriv virasoroXiInf ((0 : ℝ) : ℂ)).re < -cStar / 2
    rw [hval]
    linarith [cStar_pos]
  obtain ⟨r_dxi, hr_dxi_pos, hb_dxi⟩ := Metric.eventually_nhds_iff_ball.mp hev_dxi
  have hcont_du : ContinuousAt (fun ξ : ℝ => (deriv virasoroUInf (ξ : ℂ)).re) xiBar := by
    have h1 : ContinuousAt (deriv virasoroUInf) (xiBar : ℂ) :=
      (virasoroUInf_an.deriv (xiBar : ℂ) (mem_ball_self virasoroRXiInf_pos)).continuousAt
    exact Complex.continuous_re.continuousAt.comp
      (ContinuousAt.comp h1 (Complex.continuous_ofReal.continuousAt (x := xiBar)))
  have hdu0 : (deriv virasoroUInf (xiBar : ℂ)).re = -1 / cStar := by
    rw [virasoroUInf_hasDerivAt_xiBar.deriv, Complex.neg_re]
    simp [neg_div]
  have hev_du : ∀ᶠ ξ : ℝ in 𝓝 xiBar, (deriv virasoroUInf (ξ : ℂ)).re ≤ -1 / (2 * cStar) := by
    refine hcont_du.eventually (Iic_mem_nhds ?_)
    change (deriv virasoroUInf (xiBar : ℂ)).re < -1 / (2 * cStar)
    rw [hdu0]
    have hc := cStar_pos
    rw [neg_div, neg_div, neg_lt_neg_iff]
    exact div_lt_div_of_pos_left one_pos hc (by linarith)
  obtain ⟨r_du, hr_du_pos, hb_du⟩ := Metric.eventually_nhds_iff_ball.mp hev_du
  let r_xi0 : ℝ := min (virasoroRXiInf / 2) (r_du / 2)
  have hr_xi0_pos : 0 < r_xi0 := lt_min (half_pos virasoroRXiInf_pos) (half_pos hr_du_pos)
  -- `Q_mz(w) = betaTip * dslope (xiStar - bOfW) 0 w` and `h_mz(w) = Q_mz(w)^{1/2}` for tip comparability
  let F_mz : ℂ → ℂ := fun w => (xiStar : ℂ) - bOfW w
  have hFmz_an : AnalyticOnNhd ℂ F_mz (ball (0 : ℂ) virasoroRUInf) := fun w hw =>
    analyticAt_const.sub (hbOfW_an w hw)
  have hFmz_0 : F_mz 0 = 0 := by dsimp [F_mz]; rw [hbOfW_0, sub_self]
  have hFmz_d0 : deriv F_mz 0 = (1 / (betaTip : ℂ)) := by
    have h1 : HasDerivAt bOfW (-(1 / (betaTip : ℂ))) 0 := by
      rw [← hbOfW_deriv0]
      exact (hbOfW_an 0 (mem_ball_self virasoroRUInf_pos)).differentiableAt.hasDerivAt
    have hd := (hasDerivAt_const (0 : ℂ) (xiStar : ℂ)).sub h1
    have hfn : F_mz = (fun _ : ℂ => (xiStar : ℂ)) - bOfW := rfl
    rw [hfn, hd.deriv]
    ring
  let Q_mz : ℂ → ℂ := fun w => (betaTip : ℂ) * dslope F_mz 0 w
  have hQmz_an : AnalyticOnNhd ℂ Q_mz (ball (0 : ℂ) virasoroRUInf) := fun w hw =>
    analyticAt_const.mul
      (((differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self virasoroRUInf_pos))).mpr
        hFmz_an.differentiableOn).analyticOnNhd isOpen_ball w hw)
  have hQmz_0 : Q_mz 0 = 1 := by
    dsimp [Q_mz]
    rw [dslope_same, hFmz_d0]
    have hbt : (betaTip : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr betaTip_pos.ne'
    field_simp
  have hev_Q : ∀ᶠ w in 𝓝 (0 : ℂ),
      0 < (Q_mz w).re ∧ (1 / 2 : ℝ) ≤ ‖Q_mz w‖ ∧ ‖Q_mz w‖ ≤ 3 / 2 := by
    have hre := Complex.continuous_re.continuousAt.comp
      (hQmz_an 0 (mem_ball_self virasoroRUInf_pos)).continuousAt
    change Tendsto (fun w => (Q_mz w).re) (𝓝 0) (𝓝 (Q_mz 0).re) at hre
    rw [hQmz_0, Complex.one_re] at hre
    have hnorm := (hQmz_an 0 (mem_ball_self virasoroRUInf_pos)).continuousAt.norm
    rw [ContinuousAt, hQmz_0, norm_one] at hnorm
    exact (hre.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))).and
      ((hnorm.eventually (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).and
        (hnorm.eventually (Iic_mem_nhds (by norm_num : (1 : ℝ) < 3 / 2))))
  obtain ⟨r_Q, hr_Q_pos, hb_Q⟩ := Metric.eventually_nhds_iff_ball.mp hev_Q
  let r_Q1 : ℝ := min (virasoroRUInf / 2) (r_Q / 2)
  have hr_Q1_pos : 0 < r_Q1 := lt_min (half_pos virasoroRUInf_pos) (half_pos hr_Q_pos)
  let h_mz : ℂ → ℂ := fun w => (Q_mz w) ^ (1 / 2 : ℂ)
  have hhmz_an : AnalyticOnNhd ℂ h_mz (ball (0 : ℂ) r_Q1) := fun w hw => by
    have hw_u : w ∈ ball (0 : ℂ) virasoroRUInf :=
      ball_subset_ball ((min_le_left _ _).trans (half_lt_self virasoroRUInf_pos).le) hw
    have hw_Q : w ∈ ball (0 : ℂ) r_Q :=
      ball_subset_ball ((min_le_right _ _).trans (half_lt_self hr_Q_pos).le) hw
    exact (hQmz_an w hw_u).cpow analyticAt_const (Complex.mem_slitPlane_iff.mpr (Or.inl (hb_Q w hw_Q).1))
  have hhmz_0 : h_mz 0 = 1 := by dsimp [h_mz]; rw [hQmz_0, Complex.one_cpow]
  have hev_h : ∀ᶠ w in 𝓝 (0 : ℂ), (1 / 2 : ℝ) ≤ (h_mz w).re ∧ (h_mz w).re ≤ 3 / 2 := by
    have hre := Complex.continuous_re.continuousAt.comp
      (hhmz_an 0 (mem_ball_self hr_Q1_pos)).continuousAt
    change Tendsto (fun w => (h_mz w).re) (𝓝 0) (𝓝 (h_mz 0).re) at hre
    rw [hhmz_0, Complex.one_re] at hre
    exact (hre.eventually (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).and
      (hre.eventually (Iic_mem_nhds (by norm_num : (1 : ℝ) < 3 / 2)))
  obtain ⟨r_h, hr_h_pos, hb_h⟩ := Metric.eventually_nhds_iff_ball.mp hev_h
  let r_h1 : ℝ := min (r_Q1 / 2) (r_h / 2)
  have hr_h1_pos : 0 < r_h1 := lt_min (half_pos hr_Q1_pos) (half_pos hr_h_pos)
  obtain ⟨M_h0, hMh0⟩ := (isCompact_closedBall (0 : ℂ) r_h1).exists_bound_of_continuousOn
    (hhmz_an.deriv.continuousOn.mono
      (closedBall_subset_ball ((min_le_left _ _).trans_lt (half_lt_self hr_Q1_pos))))
  let M_h : ℝ := max M_h0 1
  have hMh_pos : 0 < M_h := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  -- Choose `b_V > 0` small enough for all constraints
  have h_b_lim : ContinuousAt (fun x : ℝ => |(virasoroXiInf (x : ℂ)).re - xiBar|) 0 := by
    have hc : ContinuousAt virasoroXiInf ((0 : ℝ) : ℂ) :=
      (virasoroXiInf_an 0 (mem_ball_self virasoroRUInf_pos)).continuousAt
    have hre : ContinuousAt (fun x : ℝ => (virasoroXiInf (x : ℂ)).re) 0 :=
      Complex.continuous_re.continuousAt.comp
        (ContinuousAt.comp hc (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ))))
    exact (hre.sub continuousAt_const).abs
  have h_b_lim_val : |(virasoroXiInf ((0 : ℝ) : ℂ)).re - xiBar| < r_xi0 := by
    rw [Complex.ofReal_zero, virasoroXiInf_zero, Complex.ofReal_re, sub_self, abs_zero]
    exact hr_xi0_pos
  obtain ⟨r_xr, hr_xr_pos, hb_xr⟩ := Metric.eventually_nhds_iff_ball.mp
    (h_b_lim.eventually (Iic_mem_nhds h_b_lim_val))
  let δ_tip : ℝ := min ρ₁_tip (min ρ₃_tip (min (1 / (4 * (C_T1_tip + 1) ^ 2)) (1 / (6 * (C_W_tip + 1)))))
  have hδ_tip_pos : 0 < δ_tip := by positivity
  let δ_b_min : ℝ := min δ_tip (min (pg.r_A / 2) (min 0.05 (xiStar / 4)))
  have hδ_b_min_pos : 0 < δ_b_min := by
    have := pg.hr_A_pos; have := xiStar_pos; positivity
  let R_cap : ℝ := min (virasoroRUInf / 4) (min (r_dxi / 2) (min (r_xr / 2)
    (min r_h1 (min (δ_b_min / C_b) (1 / (8 * M_h))))))
  have hR_cap_pos : 0 < R_cap :=
    lt_min (by positivity [virasoroRUInf_pos]) (lt_min (half_pos hr_dxi_pos)
      (lt_min (half_pos hr_xr_pos) (lt_min hr_h1_pos (lt_min (div_pos hδ_b_min_pos hCb_pos)
        (by positivity)))))
  let b_V : ℝ := √(R_cap / 4)
  have hbV_pos : 0 < b_V := Real.sqrt_pos.mpr (by linarith)
  have h2bV2_eq : 2 * b_V ^ 2 = R_cap / 2 := by
    dsimp [b_V]; rw [Real.sq_sqrt (by linarith)]; ring
  have h2bV2_lt_Rcap : 2 * b_V ^ 2 < R_cap := by rw [h2bV2_eq]; linarith
  have hRcap_lt_u : R_cap < virasoroRUInf :=
    (min_le_left _ _).trans_lt (by linarith [virasoroRUInf_pos])
  have h2bV2_lt_u : 2 * b_V ^ 2 < virasoroRUInf / 2 :=
    h2bV2_lt_Rcap.trans_le ((min_le_left _ _).trans (by linarith [virasoroRUInf_pos]))
  have h2bV2_le_dxi : 2 * b_V ^ 2 ≤ r_dxi / 2 :=
    h2bV2_lt_Rcap.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h2bV2_le_xr : 2 * b_V ^ 2 ≤ r_xr / 2 :=
    h2bV2_lt_Rcap.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hRcap_le_rh1 : R_cap ≤ r_h1 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h2bV2_le_rh1 : 2 * b_V ^ 2 ≤ r_h1 := h2bV2_lt_Rcap.le.trans hRcap_le_rh1
  have h2bV2_le_Cb : 2 * b_V ^ 2 ≤ δ_b_min / C_b :=
    h2bV2_lt_Rcap.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))))
  have hRcap_le_Mh : R_cap ≤ 1 / (8 * M_h) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  have hcl_sub_u1 : closedBall (0 : ℂ) (2 * b_V ^ 2) ⊆ closedBall (0 : ℂ) (virasoroRUInf / 2) :=
    closedBall_subset_closedBall h2bV2_lt_u.le
  -- Real derivatives on intervals
  have h_strictAnti_xi : ∀ x ∈ Icc (-(2 * b_V ^ 2)) (2 * b_V ^ 2),
      deriv (fun t : ℝ => (virasoroXiInf (t : ℂ)).re) x ≤ -cStar / 2 := by
    intro x hx
    have hx_ball : x ∈ ball (0 : ℝ) r_dxi := by
      rw [mem_ball_zero_iff, Real.norm_eq_abs]
      exact (abs_le.mpr hx).trans_lt (h2bV2_le_dxi.trans_lt (half_lt_self hr_dxi_pos))
    have hx_u : (x : ℂ) ∈ ball (0 : ℂ) virasoroRUInf := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact (abs_le.mpr hx).trans_lt (h2bV2_lt_u.trans (half_lt_self virasoroRUInf_pos))
    have h_d : HasDerivAt virasoroXiInf (deriv virasoroXiInf (x : ℂ)) (x : ℂ) :=
      (virasoroXiInf_an (x : ℂ) hx_u).differentiableAt.hasDerivAt
    have h_d_real : HasDerivAt (fun t : ℝ => (virasoroXiInf (t : ℂ)).re)
        (deriv virasoroXiInf (x : ℂ)).re x := by
      simpa only [Function.comp_def, Complex.reCLM_apply, one_mul] using
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h_d.comp_ofReal
    rw [h_d_real.deriv]
    exact hb_dxi x hx_ball
  have h_strictAnti_u : ∀ ξ : ℝ, ξ ∈ Icc (xiBar - r_xi0) (xiBar + r_xi0) →
      deriv (fun t : ℝ => (virasoroUInf (t : ℂ)).re) ξ ≤ -1 / (2 * cStar) := by
    intro ξ hξ
    have hξ_ball : ξ ∈ ball xiBar r_du := by
      rw [mem_ball, Real.dist_eq]
      have h1 : |ξ - xiBar| ≤ r_xi0 := abs_le.mpr ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
      exact h1.trans_lt ((min_le_right _ _).trans_lt (half_lt_self hr_du_pos))
    have hξ_u : (ξ : ℂ) ∈ ball (xiBar : ℂ) virasoroRXiInf := by
      rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |ξ - xiBar| ≤ r_xi0 := abs_le.mpr ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
      exact h1.trans_lt ((min_le_left _ _).trans_lt (half_lt_self virasoroRXiInf_pos))
    have h_d : HasDerivAt virasoroUInf (deriv virasoroUInf (ξ : ℂ)) (ξ : ℂ) :=
      (virasoroUInf_an (ξ : ℂ) hξ_u).differentiableAt.hasDerivAt
    have h_d_real : HasDerivAt (fun t : ℝ => (virasoroUInf (t : ℂ)).re)
        (deriv virasoroUInf (ξ : ℂ)).re ξ := by
      simpa only [Function.comp_def, Complex.reCLM_apply, one_mul] using
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt ξ h_d.comp_ofReal
    rw [h_d_real.deriv]
    exact hb_du ξ hξ_ball
  have h_u_range : ∀ x : ℝ, x ∈ Icc (-(2 * b_V ^ 2)) (2 * b_V ^ 2) →
      |(virasoroXiInf (x : ℂ)).re - xiBar| ≤ r_xi0 := fun x hx => by
    have hx_ball : x ∈ ball (0 : ℝ) r_xr := by
      rw [mem_ball_zero_iff, Real.norm_eq_abs]
      exact (abs_le.mpr hx).trans_lt (h2bV2_le_xr.trans_lt (half_lt_self hr_xr_pos))
    exact hb_xr x hx_ball
  have h_b_range : ∀ w ∈ closedBall (0 : ℂ) (2 * b_V ^ 2),
      ‖bOfW w - (xiStar : ℂ)‖ ≤ min (pg.r_A / 2) (min 0.05 (xiStar / 4)) := fun w hw => by
    have h_b_range_pt : ‖bOfW w - (xiStar : ℂ)‖ ≤ δ_b_min := by
      have hw_norm : ‖w‖ ≤ 2 * b_V ^ 2 := by simpa [mem_closedBall, dist_zero_right] using hw
      calc ‖bOfW w - (xiStar : ℂ)‖ ≤ C_b * ‖w‖ := hbOfW_lip w (hcl_sub_u1 hw)
        _ ≤ C_b * (2 * b_V ^ 2) := mul_le_mul_of_nonneg_left hw_norm hCb_pos.le
        _ ≤ C_b * (δ_b_min / C_b) := mul_le_mul_of_nonneg_left h2bV2_le_Cb hCb_pos.le
        _ = δ_b_min := mul_div_cancel₀ _ hCb_pos.ne'
    exact h_b_range_pt.trans (min_le_right _ _)
  have h_b_tip_cap : ∀ w ∈ closedBall (0 : ℂ) (2 * b_V ^ 2),
      ‖bOfW w - (xiStar : ℂ)‖ ≤ δ_tip := fun w hw => by
    have hw_norm : ‖w‖ ≤ 2 * b_V ^ 2 := by simpa [mem_closedBall, dist_zero_right] using hw
    have h1 : ‖bOfW w - (xiStar : ℂ)‖ ≤ δ_b_min := by
      calc ‖bOfW w - (xiStar : ℂ)‖ ≤ C_b * ‖w‖ := hbOfW_lip w (hcl_sub_u1 hw)
        _ ≤ C_b * (2 * b_V ^ 2) := mul_le_mul_of_nonneg_left hw_norm hCb_pos.le
        _ ≤ C_b * (δ_b_min / C_b) := mul_le_mul_of_nonneg_left h2bV2_le_Cb hCb_pos.le
        _ = δ_b_min := mul_div_cancel₀ _ hCb_pos.ne'
    exact h1.trans (min_le_left _ _)
  have h_b_T1 : ∀ w ∈ closedBall (0 : ℂ) (2 * b_V ^ 2),
      ‖bOfW w - (xiStar : ℂ)‖ ≤ min (pg.r_A / 2) 0.1 := fun w hw => by
    refine (h_b_range w hw).trans (min_le_min le_rfl ?_)
    exact (min_le_left _ _).trans (by norm_num)
  -- Tip comparability constants
  let c_tip_lo : ℝ := min (1 / (4 * √betaTip)) (1 / (2 * betaTip))
  let c_tip_hi : ℝ := max (7 / (4 * √betaTip)) (3 / (2 * betaTip))
  have hc_tip_lo_pos : 0 < c_tip_lo := by have := betaTip_pos; positivity
  have hc_tip_hi_pos : 0 < c_tip_hi := lt_of_lt_of_le (by have := betaTip_pos; positivity) (le_max_left _ _)
  have h_tip_comp : ∀ w ∈ ball (0 : ℂ) R_cap, ¬ (w.im = 0 ∧ w.re ≤ 0) →
      let mz := (xiStar : ℂ) - bOfW w
      c_tip_lo * (w ^ (1 / 2 : ℂ)).re ≤ (mz ^ (1 / 2 : ℂ)).re ∧
      (mz ^ (1 / 2 : ℂ)).re ≤ c_tip_hi * (w ^ (1 / 2 : ℂ)).re ∧
      c_tip_lo * ‖w‖ ≤ ‖mz‖ ∧ ‖mz‖ ≤ c_tip_hi * ‖w‖ := by
    intro w hw hcut mz
    have hw_rh1 : w ∈ closedBall (0 : ℂ) r_h1 :=
      closedBall_subset_closedBall hRcap_le_rh1 (ball_subset_closedBall hw)
    have hw_rh : w ∈ ball (0 : ℂ) r_h :=
      closedBall_subset_ball ((min_le_right _ _).trans_lt (half_lt_self hr_h_pos)) hw_rh1
    have hw_rQ1 : w ∈ ball (0 : ℂ) r_Q1 :=
      closedBall_subset_ball ((min_le_left _ _).trans_lt (half_lt_self hr_Q1_pos)) hw_rh1
    have hw_rQ : w ∈ ball (0 : ℂ) r_Q :=
      ball_subset_ball ((min_le_right _ _).trans (half_lt_self hr_Q_pos).le) hw_rQ1
    have hw_ru : w ∈ ball (0 : ℂ) virasoroRUInf :=
      ball_subset_ball ((min_le_left _ _).trans (half_lt_self virasoroRUInf_pos).le) hw_rQ1
    have hQ_props := hb_Q w hw_rQ
    have hh_props := hb_h w hw_rh
    have hmz_eq : mz = (1 / (betaTip : ℂ)) * w * Q_mz w := by
      dsimp [mz, Q_mz]
      have hds := sub_smul_dslope F_mz 0 w
      rw [sub_zero, hFmz_0, sub_zero, smul_eq_mul] at hds
      have hbt : (betaTip : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr betaTip_pos.ne'
      calc F_mz w = w * dslope F_mz 0 w := hds.symm
        _ = (1 / (betaTip : ℂ)) * w * ((betaTip : ℂ) * dslope F_mz 0 w) := by field_simp
    have hnorm_mz : ‖mz‖ = (1 / betaTip) * ‖w‖ * ‖Q_mz w‖ := by
      rw [hmz_eq, norm_mul, norm_mul,
        show (1 / (betaTip : ℂ)) = ((1 / betaTip : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr betaTip_pos)]
    have hnorm_lo : c_tip_lo * ‖w‖ ≤ ‖mz‖ := by
      rw [hnorm_mz]
      calc c_tip_lo * ‖w‖ ≤ (1 / (2 * betaTip)) * ‖w‖ :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
        _ = (1 / betaTip) * ‖w‖ * (1 / 2) := by ring
        _ ≤ (1 / betaTip) * ‖w‖ * ‖Q_mz w‖ :=
            mul_le_mul_of_nonneg_left hQ_props.2.1 (by positivity [betaTip_pos])
    have hnorm_hi : ‖mz‖ ≤ c_tip_hi * ‖w‖ := by
      rw [hnorm_mz]
      calc (1 / betaTip) * ‖w‖ * ‖Q_mz w‖ ≤ (1 / betaTip) * ‖w‖ * (3 / 2) :=
            mul_le_mul_of_nonneg_left hQ_props.2.2 (by positivity [betaTip_pos])
        _ = (3 / (2 * betaTip)) * ‖w‖ := by ring
        _ ≤ c_tip_hi * ‖w‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    have hh_re_im : ∀ x : ℝ, |(x : ℝ)| ≤ r_h1 → (h_mz (x : ℂ)).im = 0 := by
      intro x hx
      have hr1_lt_Q1 : r_h1 < r_Q1 := (min_le_left _ _).trans_lt (half_lt_self hr_Q1_pos)
      have hx_u : (x : ℂ) ∈ ball (0 : ℂ) virasoroRUInf := by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        exact hx.trans_lt (hr1_lt_Q1.trans_le ((min_le_left _ _).trans (half_lt_self virasoroRUInf_pos).le))
      have h_b_conj : bOfW (starRingEnd ℂ (x : ℂ)) = starRingEnd ℂ (bOfW (x : ℂ)) := by
        dsimp [bOfW]
        have hx_xi := virasoroXiInf_mem hx_u
        rw [virasoroXiInf_conj hx_u, virasoroBOfXi_conj (langerCore.huInf_real_pos _ hx_xi).1]
      have hb_x_im : (bOfW (x : ℂ)).im = 0 := by
        have h1 := h_b_conj
        rw [Complex.conj_ofReal] at h1
        have him := congrArg Complex.im h1.symm
        rw [Complex.conj_im] at him
        linarith
      have hF_x_im : (F_mz (x : ℂ)).im = 0 := by
        dsimp [F_mz]; simp [hb_x_im]
      have hQ_x_im : (Q_mz (x : ℂ)).im = 0 := by
        by_cases hx0 : x = 0
        · subst hx0; simp [hQmz_0]
        · dsimp [Q_mz]
          rw [dslope_of_ne _ (Complex.ofReal_ne_zero.mpr hx0), slope_def_field, hFmz_0, sub_zero,
            sub_zero]
          have h1 : F_mz (x : ℂ) = ((F_mz (x : ℂ)).re : ℂ) := Complex.ext rfl hF_x_im
          rw [h1, ← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.ofReal_im]
      have hx_rQ : (x : ℂ) ∈ ball (0 : ℂ) r_Q := by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        exact hx.trans_lt (hr1_lt_Q1.trans_le ((min_le_right _ _).trans (half_lt_self hr_Q_pos).le))
      have hQ_x_pos : 0 < (Q_mz (x : ℂ)).re := (hb_Q _ hx_rQ).1
      have hQ_eq : Q_mz (x : ℂ) = ((Q_mz (x : ℂ)).re : ℂ) := Complex.ext rfl hQ_x_im
      dsimp [h_mz]
      rw [hQ_eq, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_cpow hQ_x_pos.le, Complex.ofReal_im]
    have hw_re_cb : (w.re : ℂ) ∈ closedBall (0 : ℂ) r_h1 := by
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm w).trans (mem_closedBall_zero_iff.mp hw_rh1)
    have hmvt_h := (convex_closedBall (0 : ℂ) r_h1).norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hhmz_an z (closedBall_subset_ball
        ((min_le_left _ _).trans_lt (half_lt_self hr_Q1_pos)) hz)).differentiableAt)
      (fun z hz => (hMh0 z hz).trans (le_max_left M_h0 0)) hw_re_cb hw_rh1
    have hw_sub_re : ‖w - (w.re : ℂ)‖ = |w.im| := by
      have : w - (w.re : ℂ) = (w.im : ℂ) * Complex.I := by apply Complex.ext <;> simp
      rw [this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    have hh_im_le : |(h_mz w).im| ≤ M_h * |w.im| := by
      have him0 : (h_mz (w.re : ℂ)).im = 0 :=
        hh_re_im w.re ((Complex.abs_re_le_norm w).trans (mem_closedBall_zero_iff.mp hw_rh1))
      calc |(h_mz w).im| = |(h_mz w - h_mz (w.re : ℂ)).im| := by rw [Complex.sub_im, him0, sub_zero]
        _ ≤ ‖h_mz w - h_mz (w.re : ℂ)‖ := Complex.abs_im_le_norm _
        _ ≤ max M_h0 0 * ‖w - (w.re : ℂ)‖ := hmvt_h
        _ ≤ M_h * |w.im| := by
            rw [hw_sub_re]
            exact mul_le_mul_of_nonneg_right (max_le_max_left _ (by norm_num)) (abs_nonneg _)
    let s : ℂ := w ^ (1 / 2 : ℂ)
    let a : ℝ := s.re
    let b : ℝ := s.im
    have ha_nn : 0 ≤ a := cpow_half_re_nonneg w
    have ha_pos : 0 < a := by
      rcases ha_nn.eq_or_lt with ha0 | ha_lt
      · exfalso
        apply hcut
        have him_w : w.im = 2 * a * b := (airySqrtRe_mul_im w).symm
        have hre_w : w.re = a ^ 2 - b ^ 2 := (airySqrtRe_sq_sub w).symm
        rw [← ha0] at him_w hre_w
        exact ⟨by linarith, by nlinarith [sq_nonneg b]⟩
      · exact ha_lt
    have hw_im_eq : w.im = 2 * a * b := (airySqrtRe_mul_im w).symm
    have hb_sq_le : b ^ 2 ≤ ‖w‖ := by
      have hadd : a ^ 2 + b ^ 2 = ‖w‖ := airySqrtRe_sq_add w
      linarith [sq_nonneg a]
    have hbw_im_le : |b * (h_mz w).im| ≤ 2 * M_h * ‖w‖ * a := by
      rw [hw_im_eq, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos ha_pos] at hh_im_le
      rw [abs_mul]
      calc |b| * |(h_mz w).im|
          ≤ |b| * (M_h * (2 * a * |b|)) := mul_le_mul_of_nonneg_left hh_im_le (abs_nonneg b)
        _ = 2 * M_h * (|b| ^ 2) * a := by ring
        _ = 2 * M_h * (b ^ 2) * a := by rw [sq_abs]
        _ ≤ 2 * M_h * ‖w‖ * a := by gcongr
    have hw_norm_Rcap : ‖w‖ ≤ R_cap := (mem_ball_zero_iff.mp hw).le
    have h2Mh_le : 2 * M_h * ‖w‖ ≤ 1 / 4 := by
      calc 2 * M_h * ‖w‖ ≤ 2 * M_h * R_cap := mul_le_mul_of_nonneg_left hw_norm_Rcap (by positivity)
        _ ≤ 2 * M_h * (1 / (8 * M_h)) := mul_le_mul_of_nonneg_left hRcap_le_Mh (by positivity)
        _ = 1 / 4 := by field_simp [hMh_pos.ne']; ring
    let p : ℂ := ((1 / √betaTip : ℝ) : ℂ) * s * h_mz w
    have hp_sq : p ^ 2 = mz := by
      dsimp [p, s, h_mz]
      rw [mul_pow, mul_pow, cpow_half_sq, cpow_half_sq,
        ← Complex.ofReal_pow, div_pow, one_pow, Real.sq_sqrt betaTip_pos.le]
      rw [hmz_eq]; push_cast; ring
    have hp_re_eq : p.re = (1 / √betaTip) * (a * (h_mz w).re - b * (h_mz w).im) := by
      dsimp [p, a, b]
      rw [mul_assoc, Complex.re_ofReal_mul, Complex.mul_re]
    have hp_re_lo : (1 / (4 * √betaTip)) * a ≤ p.re := by
      have h1 : (1 / 2 : ℝ) * a ≤ a * (h_mz w).re := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hh_props.1 ha_pos.le
      have h2 : b * (h_mz w).im ≤ (1 / 4 : ℝ) * a :=
        (le_abs_self _).trans (hbw_im_le.trans (mul_le_mul_of_nonneg_right h2Mh_le ha_pos.le))
      rw [hp_re_eq]
      calc (1 / (4 * √betaTip)) * a = (1 / √betaTip) * ((1 / 4 : ℝ) * a) := by ring
        _ ≤ (1 / √betaTip) * (a * (h_mz w).re - b * (h_mz w).im) := by
            gcongr; linarith
    have hp_re_hi : p.re ≤ (7 / (4 * √betaTip)) * a := by
      have h1 : a * (h_mz w).re ≤ (3 / 2 : ℝ) * a := by
        rw [mul_comm a]; exact mul_le_mul_of_nonneg_right hh_props.2 ha_pos.le
      have h2 : -(b * (h_mz w).im) ≤ (1 / 4 : ℝ) * a :=
        (neg_le_abs _).trans (hbw_im_le.trans (mul_le_mul_of_nonneg_right h2Mh_le ha_pos.le))
      rw [hp_re_eq]
      calc (1 / √betaTip) * (a * (h_mz w).re - b * (h_mz w).im)
          ≤ (1 / √betaTip) * ((7 / 4 : ℝ) * a) := by gcongr; linarith
        _ = (7 / (4 * √betaTip)) * a := by ring
    have hp_re_pos : 0 < p.re := lt_of_lt_of_le (by positivity [betaTip_pos]) hp_re_lo
    have hmz_half : mz ^ (1 / 2 : ℂ) = p := cpow_half_of_sq_and_re_pos hp_sq hp_re_pos
    refine ⟨?_, ?_, hnorm_lo, hnorm_hi⟩
    · rw [hmz_half]
      exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) ha_pos.le) hp_re_lo
    · rw [hmz_half]
      exact hp_re_hi.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ha_pos.le)
  have hbOfW_real : ∀ x : ℝ, |x| < R_cap → (bOfW (x : ℂ)).im = 0 ∧
      0 < (bOfW (x : ℂ)).re ∧
      |(bOfW (x : ℂ)).re - xiStar| < pg.r_A ∧
      0 < (pg.A (bOfW (x : ℂ) - (xiStar : ℂ))).re := by
    intro x hx
    have hx_u : (x : ℂ) ∈ ball (0 : ℂ) virasoroRUInf := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact hx.trans hRcap_lt_u
    have hx_xi := virasoroXiInf_mem hx_u
    have h_b_conj : bOfW (starRingEnd ℂ (x : ℂ)) = starRingEnd ℂ (bOfW (x : ℂ)) := by
      dsimp [bOfW]
      rw [virasoroXiInf_conj hx_u, virasoroBOfXi_conj (langerCore.huInf_real_pos _ hx_xi).1]
    have hb_im : (bOfW (x : ℂ)).im = 0 := by
      have h1 := h_b_conj; rw [Complex.conj_ofReal] at h1
      have him := congrArg Complex.im h1.symm; rw [Complex.conj_im] at him; linarith
    have hprops := langerCore.huInf_real_pos _ hx_xi
    have hsub_abs : |(bOfW (x : ℂ)).re - xiStar| < pg.r_A := by
      have h1 : ‖bOfW (x : ℂ) - (xiStar : ℂ)‖ < pg.r_A / 2 := hprops.2.1
      have h2 : |(bOfW (x : ℂ)).re - xiStar| ≤ ‖bOfW (x : ℂ) - (xiStar : ℂ)‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (bOfW (x : ℂ) - (xiStar : ℂ))
      exact h2.trans_lt (h1.trans (half_lt_self pg.hr_A_pos))
    have hb_re_pos : 0 < (bOfW (x : ℂ)).re := by
      have h1 : ‖bOfW (x : ℂ) - (xiStar : ℂ)‖ ≤ C_b * |x| := by
        have hx_u1 : (x : ℂ) ∈ closedBall (0 : ℂ) (virasoroRUInf / 2) := by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
          exact hx.le.trans ((min_le_left _ _).trans (by linarith [virasoroRUInf_pos]))
        simpa [Complex.norm_real, Real.norm_eq_abs] using hbOfW_lip (x : ℂ) hx_u1
      have h2 : C_b * |x| ≤ δ_b_min := by
        have hx_cb : |x| ≤ δ_b_min / C_b := hx.le.trans ((min_le_right _ _).trans
          ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
        calc C_b * |x| ≤ C_b * (δ_b_min / C_b) := mul_le_mul_of_nonneg_left hx_cb hCb_pos.le
          _ = δ_b_min := mul_div_cancel₀ _ hCb_pos.ne'
      have h3 : |(bOfW (x : ℂ)).re - xiStar| ≤ xiStar / 4 := by
        have hre := Complex.abs_re_le_norm (bOfW (x : ℂ) - (xiStar : ℂ))
        simp only [Complex.sub_re, Complex.ofReal_re] at hre
        exact hre.trans (h1.trans (h2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
      linarith [(abs_le.mp h3).1, xiStar_pos]
    exact ⟨hb_im, hb_re_pos, hsub_abs, hprops.2.2⟩
  exact ⟨{
    b_V := b_V
    hbV_pos := hbV_pos
    r_xi0 := r_xi0
    hr_xi0_pos := hr_xi0_pos
    hr_xi0_le := min_le_left _ _
    h2bV2_lt := h2bV2_lt_u
    C_b := C_b
    hCb_pos := hCb_pos
    hCb_bd := fun w hw => hbOfW_lip w (hcl_sub_u1 hw)
    C_xi := C_xi
    hCxi_nn := hCxi_nn
    hxi_err := fun w hw => hRxi_bd' w (hcl_sub_u1 hw)
    M_u := M_u
    hMu_nn := hMu_nn
    hu_err := fun ξ hξ => hRu_bd' ξ (closedBall_subset_closedBall (min_le_left _ _) hξ)
    h_strictAnti_xi := h_strictAnti_xi
    h_strictAnti_u := h_strictAnti_u
    h_u_range := h_u_range
    h_b_range := h_b_range
    h_b_T1 := h_b_T1
    ρ₁_tip := ρ₁_tip
    C_T1_tip := C_T1_tip
    ψ_tip := ψ_tip
    ρ₃_tip := ρ₃_tip
    C_W_tip := C_W_tip
    hρ₁_tip_pos := hρ₁_tip_pos
    hCT1_tip_nn := hCT1_tip_nn
    hρ₃_tip_pos := hρ₃_tip_pos
    hCW_tip_nn := hCW_tip_nn
    hT1_tip := hT1_tip
    hT3_tip := hT3_tip
    C_dxi := C_dxi
    hCdxi_pos := hCdxi_pos
    hdxi_bd := fun w hw => (hMdxi w (hcl_sub_u1 hw)).trans (le_max_left M_dxi 1)
    h_b_tip_cap := h_b_tip_cap
    c_tip_lo := c_tip_lo
    c_tip_hi := c_tip_hi
    hc_tip_lo_pos := hc_tip_lo_pos
    hc_tip_hi_pos := hc_tip_hi_pos
    r_open_cap := R_cap
    hr_open_cap_gt := h2bV2_lt_Rcap
    hr_open_cap_lt_u := hRcap_lt_u
    h_tip_comp := h_tip_comp
    hbOfW_real := hbOfW_real
  }⟩

noncomputable def chartParams : VirasoroChartParams :=
  Classical.choice virasoroChartParams_exists

noncomputable def virasoroCTipLo : ℝ := chartParams.c_tip_lo
noncomputable def virasoroCTipHi : ℝ := chartParams.c_tip_hi
noncomputable def virasoroCXi : ℝ := chartParams.C_xi

lemma virasoroCTipLo_pos : 0 < virasoroCTipLo := chartParams.hc_tip_lo_pos
lemma virasoroCTipHi_pos : 0 < virasoroCTipHi := chartParams.hc_tip_hi_pos
lemma virasoroCXi_nn : 0 ≤ virasoroCXi := chartParams.hCxi_nn

/-! ### Section 4: `c'`-scaled chart maps and main chart theorems -/

/-- Bootstrap scale parameter `b_V > 0` for Virasoro (`lower_o1_two_edge.tex`, §J2). -/
noncomputable def virasoroBV : ℝ := chartParams.b_V

lemma virasoroBV_pos : 0 < virasoroBV := chartParams.hbV_pos

/-- Chart radius `A_{c'} = √2 b_V c'^{1/3}`, so `A_{c'}^2 = 2 b_V^2 c'^{2/3}`. -/
noncomputable def virasoroAC (c' : ℝ) : ℝ := √2 * virasoroBV * c' ^ (1 / 3 : ℝ)

lemma virasoroAC_sq (c' : ℝ) (hc' : 0 ≤ c') :
    virasoroAC c' ^ 2 = 2 * virasoroBV ^ 2 * c' ^ (2 / 3 : ℝ) := by
  unfold virasoroAC
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), ← Real.rpow_natCast (c' ^ (1 / 3 : ℝ)) 2,
    ← Real.rpow_mul hc']
  norm_num

lemma virasoroAC_pos {c' : ℝ} (hc' : 0 < c') : 0 < virasoroAC c' := by
  unfold virasoroAC; have := virasoroBV_pos; positivity

/-- Real-valued Langer chart `ũ(ξ) = c'^{2/3} Re u_∞(ξ)` on the chart interval `[ξ̄ - r_0, ξ̄ + r_0]`. -/
noncomputable def virasoroUChart (c' ξ : ℝ) : ℝ :=
  c' ^ (2 / 3 : ℝ) * (virasoroUInf (ξ : ℂ)).re

/-- Complex inverse Langer chart `ξ_{c'}(u) = ξ_∞(u c'^{-2/3})`. -/
noncomputable def virasoroXiChartC (c' : ℝ) (u : ℂ) : ℂ :=
  virasoroXiInf (u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ))

/-- Real inverse Langer chart `Δ(u) = c' Re ξ_{c'}(u)`. -/
noncomputable def virasoroDeltaChart (c' u : ℝ) : ℝ :=
  c' * (virasoroXiChartC c' (u : ℂ)).re

/-- Complex energy threshold map `Δ_ℂ(u) = c' ξ_{c'}(u)`. -/
noncomputable def virasoroDeltaChartC (c' : ℝ) (u : ℂ) : ℂ :=
  (c' : ℂ) * virasoroXiChartC c' u

/-- Complex `b`-coordinate map `b(u) = √(3 ξ_{c'}(u))`. -/
noncomputable def virasoroBChart (c' : ℝ) (u : ℂ) : ℂ :=
  virasoroBOfXi (virasoroXiChartC c' u)

/-- Half-width `r_0 > 0` of the real chart interval around `ξ̄`. -/
noncomputable def virasoroChartR0 : ℝ := chartParams.r_xi0

lemma virasoroChartR0_pos : 0 < virasoroChartR0 := chartParams.hr_xi0_pos

lemma virasoro_u_mem_ball {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) (virasoroAC c' ^ 2)) :
    u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) ∈ closedBall (0 : ℂ) (2 * virasoroBV ^ 2) := by
  rw [mem_closedBall_zero_iff] at hu ⊢
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hc'.le _)]
  have h1 : virasoroAC c' ^ 2 * c' ^ (-(2 / 3 : ℝ)) = 2 * virasoroBV ^ 2 := by
    rw [virasoroAC_sq c' hc'.le, mul_assoc, ← Real.rpow_add hc', add_neg_cancel, Real.rpow_zero,
      mul_one]
  calc ‖u‖ * c' ^ (-(2 / 3 : ℝ))
      ≤ virasoroAC c' ^ 2 * c' ^ (-(2 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_right hu (Real.rpow_nonneg hc'.le _)
    _ = 2 * virasoroBV ^ 2 := h1

lemma virasoro_u_mem_open_ball {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) (virasoroAC c' ^ 2)) :
    u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) ∈ ball (0 : ℂ) virasoroRUInf :=
  (closedBall_subset_ball (chartParams.h2bV2_lt.trans (half_lt_self virasoroRUInf_pos)))
    (virasoro_u_mem_ball hc' hu)

/-- Analyticity of `virasoroXiChartC c'` on `ball 0 (virasoroRUInf * c'^{2/3})`
(which contains `closedBall 0 (virasoroAC c' ^ 2)`). -/
lemma virasoroXiChartC_analyticOnNhd {c' : ℝ} (hc' : 0 < c') :
    AnalyticOnNhd ℂ (virasoroXiChartC c') (ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ))) := by
  intro u hu
  have hw : u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) ∈ ball (0 : ℂ) virasoroRUInf := by
    rw [mem_ball_zero_iff] at hu ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hc'.le _)]
    have hmul : virasoroRUInf * c' ^ (2 / 3 : ℝ) * c' ^ (-(2 / 3 : ℝ)) = virasoroRUInf := by
      rw [mul_assoc, ← Real.rpow_add hc', add_neg_cancel, Real.rpow_zero, mul_one]
    calc ‖u‖ * c' ^ (-(2 / 3 : ℝ))
        < (virasoroRUInf * c' ^ (2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) :=
          mul_lt_mul_of_pos_right hu (Real.rpow_pos_of_pos hc' _)
      _ = virasoroRUInf := hmul
  have hmul_an : AnalyticAt ℂ (fun z : ℂ => z * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) u :=
    AnalyticAt.mul analyticAt_id analyticAt_const
  exact (virasoroXiInf_an _ hw).comp_of_eq hmul_an rfl

lemma virasoroDeltaChartC_analyticOnNhd {c' : ℝ} (hc' : 0 < c') :
    AnalyticOnNhd ℂ (virasoroDeltaChartC c') (ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ))) :=
  fun u hu => analyticAt_const.mul (virasoroXiChartC_analyticOnNhd hc' u hu)

lemma virasoroBChart_analyticOnNhd {c' : ℝ} (hc' : 0 < c') :
    AnalyticOnNhd ℂ (virasoroBChart c') (ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ))) := by
  intro u hu
  have hw : u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) ∈ ball (0 : ℂ) virasoroRUInf := by
    rw [mem_ball_zero_iff] at hu ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hc'.le _)]
    have hmul : virasoroRUInf * c' ^ (2 / 3 : ℝ) * c' ^ (-(2 / 3 : ℝ)) = virasoroRUInf := by
      rw [mul_assoc, ← Real.rpow_add hc', add_neg_cancel, Real.rpow_zero, mul_one]
    calc ‖u‖ * c' ^ (-(2 / 3 : ℝ))
        < (virasoroRUInf * c' ^ (2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) :=
          mul_lt_mul_of_pos_right hu (Real.rpow_pos_of_pos hc' _)
      _ = virasoroRUInf := hmul
  have hmem := virasoroXiInf_mem hw
  have hre := (langerCore.huInf_real_pos _ hmem).1
  exact (virasoroBOfXi_analyticAt hre).comp_of_eq (virasoroXiChartC_analyticOnNhd hc' u hu) rfl

lemma virasoroAC_sq_lt_domain {c' : ℝ} (hc' : 0 < c') :
    virasoroAC c' ^ 2 < virasoroRUInf * c' ^ (2 / 3 : ℝ) := by
  rw [virasoroAC_sq c' hc'.le]
  have h1 : 2 * virasoroBV ^ 2 < virasoroRUInf :=
    chartParams.h2bV2_lt.trans (half_lt_self virasoroRUInf_pos)
  exact mul_lt_mul_of_pos_right h1 (Real.rpow_pos_of_pos hc' _)

lemma virasoroDeltaChartC_ofReal {c' : ℝ} (hc' : 0 < c') {u : ℝ}
    (hu : |u| ≤ virasoroAC c' ^ 2) :
    virasoroDeltaChartC c' (u : ℂ) = (virasoroDeltaChart c' u : ℂ) := by
  unfold virasoroDeltaChart virasoroDeltaChartC virasoroXiChartC
  have hw : ((u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) =
      (((u * c' ^ (-(2 / 3 : ℝ)) : ℝ)) : ℂ) := by push_cast; rfl
  have hmem : |u * c' ^ (-(2 / 3 : ℝ))| < virasoroRUInf := by
    have hball := virasoro_u_mem_open_ball hc' (u := (u : ℂ))
      (by simpa [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hu)
    rwa [hw, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs] at hball
  have him := virasoroXiInf_ofReal_im hmem
  rw [hw]
  refine Complex.ext ?_ ?_
  · rw [Complex.re_ofReal_mul, Complex.ofReal_re]
  · rw [Complex.im_ofReal_mul, him, mul_zero, Complex.ofReal_im]

lemma virasoroBChart_ofReal {c' : ℝ} (hc' : 0 < c') {u : ℝ}
    (hu : |u| ≤ virasoroAC c' ^ 2) :
    (virasoroBChart c' (u : ℂ)).im = 0 ∧
    0 < (virasoroBChart c' (u : ℂ)).re ∧
    virasoroBChart c' (u : ℂ) = (Real.sqrt (3 * virasoroDeltaChart c' u / c') : ℂ) ∧
    (c' : ℂ) * virasoroBChart c' (u : ℂ) ^ 2 / 3 = (virasoroDeltaChart c' u : ℂ) := by
  have hmem_open := virasoro_u_mem_open_ball hc' (u := (u : ℂ))
    (by simpa [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hu)
  have hxi_mem := virasoroXiInf_mem hmem_open
  have hxi_re_pos : 0 < (virasoroXiChartC c' (u : ℂ)).re :=
    (langerCore.huInf_real_pos _ hxi_mem).1
  have hxi_im : (virasoroXiChartC c' (u : ℂ)).im = 0 := by
    unfold virasoroXiChartC
    have hw : ((u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) =
        (((u * c' ^ (-(2 / 3 : ℝ)) : ℝ)) : ℂ) := by push_cast; rfl
    rw [hw]
    apply virasoroXiInf_ofReal_im
    rwa [hw, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs] at hmem_open
  have hxi_eq : virasoroXiChartC c' (u : ℂ) = ((virasoroDeltaChart c' u / c' : ℝ) : ℂ) := by
    unfold virasoroDeltaChart
    rw [mul_div_cancel_left₀ _ hc'.ne']
    exact Complex.ext rfl hxi_im
  have hdiv_pos : 0 < virasoroDeltaChart c' u / c' := by
    unfold virasoroDeltaChart
    rwa [mul_div_cancel_left₀ _ hc'.ne']
  have hb_eq : virasoroBChart c' (u : ℂ) = (Real.sqrt (3 * virasoroDeltaChart c' u / c') : ℂ) := by
    unfold virasoroBChart
    rw [hxi_eq, virasoroBOfXi_ofReal hdiv_pos.le]
    congr 1; ring
  have hpos3 : 0 < 3 * virasoroDeltaChart c' u / c' := by
    rw [mul_div_assoc]; exact mul_pos (by norm_num) hdiv_pos
  refine ⟨?_, ?_, hb_eq, ?_⟩
  · rw [hb_eq, Complex.ofReal_im]
  · rw [hb_eq, Complex.ofReal_re]
    exact Real.sqrt_pos.mpr hpos3
  · rw [hb_eq, ← Complex.ofReal_pow, Real.sq_sqrt hpos3.le]
    push_cast; field_simp [hc'.ne']

lemma virasoroDeltaChart_pos {c' : ℝ} (hc' : 0 < c') {u : ℝ} (hu : |u| ≤ virasoroAC c' ^ 2) :
    0 < virasoroDeltaChart c' u := by
  have hmem := virasoro_u_mem_open_ball hc' (u := (u : ℂ))
    (by simpa [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hu)
  have hre := (langerCore.huInf_real_pos _ (virasoroXiInf_mem hmem)).1
  unfold virasoroDeltaChart virasoroXiChartC
  exact mul_pos hc' hre

lemma virasoroDeltaChart_hasDerivAt {c' u : ℝ} (hc' : 0 < c')
    (hu : |u| ≤ virasoroAC c' ^ 2) :
    HasDerivAt (virasoroDeltaChart c')
      (c' ^ (1 / 3 : ℝ) * (deriv virasoroXiInf ((u * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re) u := by
  let x : ℝ := u * c' ^ (-(2 / 3 : ℝ))
  have hu_open : (x : ℂ) ∈ ball (0 : ℂ) virasoroRUInf := by
    have h1 := virasoro_u_mem_open_ball hc' (u := (u : ℂ))
      (by simpa [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hu)
    rwa [show (u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) = (x : ℂ) by dsimp [x]; push_cast; rfl] at h1
  have hd_xi : HasDerivAt (fun t : ℝ => virasoroXiInf (t : ℂ))
      (deriv virasoroXiInf (x : ℂ)) x := by
    simpa using ((virasoroXiInf_an _ hu_open).differentiableAt.hasDerivAt).comp_ofReal
  have hd_lin : HasDerivAt (fun t : ℝ => t * c' ^ (-(2 / 3 : ℝ))) (c' ^ (-(2 / 3 : ℝ))) u := by
    simpa using (hasDerivAt_id u).mul_const (c' ^ (-(2 / 3 : ℝ)))
  have hd_comp : HasDerivAt (fun t : ℝ => virasoroXiInf ((t * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ))
      ((c' ^ (-(2 / 3 : ℝ))) • deriv virasoroXiInf (x : ℂ)) u := by
    show HasDerivAt ((fun t : ℝ => virasoroXiInf (t : ℂ)) ∘ (fun t : ℝ => t * c' ^ (-(2 / 3 : ℝ))))
      ((c' ^ (-(2 / 3 : ℝ))) • deriv virasoroXiInf (x : ℂ)) u
    exact hd_xi.scomp u hd_lin
  have hd_re : HasDerivAt (fun t : ℝ => (virasoroXiInf ((t * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re)
      (((c' ^ (-(2 / 3 : ℝ))) • deriv virasoroXiInf (x : ℂ)).re) u :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hd_comp
  have hd_mul := hd_re.const_mul c'
  have hfun : (fun t : ℝ => c' * (virasoroXiInf ((t * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re) =
      virasoroDeltaChart c' := by
    ext t; unfold virasoroDeltaChart virasoroXiChartC; push_cast; rfl
  rw [hfun] at hd_mul
  refine hd_mul.congr_deriv ?_
  have hrw : (((c' ^ (-(2 / 3 : ℝ))) • deriv virasoroXiInf (x : ℂ))).re =
      c' ^ (-(2 / 3 : ℝ)) * (deriv virasoroXiInf (x : ℂ)).re := by
    rw [Complex.real_smul, Complex.re_ofReal_mul]
  rw [hrw, ← mul_assoc, ← Real.rpow_one_add' hc'.le (by norm_num : (1 : ℝ) + -(2 / 3 : ℝ) ≠ 0)]
  norm_num
  left
  dsimp [x]; push_cast; rfl

lemma virasoroDeltaChart_deriv_le {c' u : ℝ} (hc' : 0 < c')
    (hu : u ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2)) :
    deriv (virasoroDeltaChart c') u ≤ -(cStar / 2) * c' ^ (1 / 3 : ℝ) := by
  have hu_abs : |u| ≤ virasoroAC c' ^ 2 := abs_le.mpr hu
  have hhd := virasoroDeltaChart_hasDerivAt hc' hu_abs
  rw [hhd.deriv]
  set x : ℝ := u * c' ^ (-(2 / 3 : ℝ))
  have hx_mem : x ∈ Icc (-(2 * chartParams.b_V ^ 2)) (2 * chartParams.b_V ^ 2) := by
    have hxb : (x : ℂ) ∈ closedBall (0 : ℂ) (2 * virasoroBV ^ 2) := by
      have h1 := virasoro_u_mem_ball hc' (u := (u : ℂ))
        (by simpa [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hu_abs)
      rwa [show (u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) = (x : ℂ) by dsimp [x]; push_cast; rfl] at h1
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] at hxb
    unfold virasoroBV at hxb
    exact abs_le.mp hxb
  have hx_open : (x : ℂ) ∈ ball (0 : ℂ) virasoroRUInf :=
    closedBall_subset_ball (chartParams.h2bV2_lt.trans (half_lt_self virasoroRUInf_pos))
      (by simpa [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using abs_le.mpr hx_mem)
  have hhd_x : HasDerivAt (fun t : ℝ => (virasoroXiInf (t : ℂ)).re)
      (deriv virasoroXiInf (x : ℂ)).re x := by
    have h1 : HasDerivAt (fun t : ℝ => virasoroXiInf (t : ℂ)) (deriv virasoroXiInf (x : ℂ)) x := by
      simpa using ((virasoroXiInf_an (x : ℂ) hx_open).differentiableAt.hasDerivAt).comp_ofReal
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h1
  have hbd := chartParams.h_strictAnti_xi x hx_mem
  rw [hhd_x.deriv] at hbd
  calc c' ^ (1 / 3 : ℝ) * (deriv virasoroXiInf (x : ℂ)).re
      ≤ c' ^ (1 / 3 : ℝ) * (-cStar / 2) :=
        mul_le_mul_of_nonneg_left hbd (Real.rpow_nonneg hc'.le _)
    _ = -(cStar / 2) * c' ^ (1 / 3 : ℝ) := by ring

lemma virasoroDeltaChart_strictAnti {c' : ℝ} (hc' : 0 < c') :
    StrictAntiOn (virasoroDeltaChart c') (Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
  · exact ContinuousOn.congr (fun u hu =>
      (virasoroDeltaChart_hasDerivAt hc' (abs_le.mpr hu)).continuousAt.continuousWithinAt)
      (fun u _ => rfl)
  · intro u hu
    have hmem : u ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) := interior_subset hu
    have hbd := virasoroDeltaChart_deriv_le hc' hmem
    have hneg : -(cStar / 2) * c' ^ (1 / 3 : ℝ) < 0 := by
      have := cStar_pos
      have : 0 < c' ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc' _
      linarith [mul_pos (half_pos cStar_pos) this]
    exact lt_of_le_of_lt hbd hneg

lemma virasoroDeltaChart_zero {c' : ℝ} : virasoroDeltaChart c' 0 = xiBar * c' := by
  unfold virasoroDeltaChart virasoroXiChartC
  simp [virasoroXiInf_zero, mul_comm]

lemma virasoroUChart_xiBar {c' : ℝ} : virasoroUChart c' xiBar = 0 := by
  unfold virasoroUChart
  simp [virasoroUInf_xiBar]

lemma virasoroUChart_strictAnti {c' : ℝ} (hc' : 0 < c') :
    StrictAntiOn (virasoroUChart c') (Icc (xiBar - virasoroChartR0) (xiBar + virasoroChartR0)) := by
  have hd : ∀ ξ ∈ Icc (xiBar - virasoroChartR0) (xiBar + virasoroChartR0),
      HasDerivAt (virasoroUChart c')
        (c' ^ (2 / 3 : ℝ) * (deriv virasoroUInf (ξ : ℂ)).re) ξ := fun ξ hξ => by
    have hξ_open : (ξ : ℂ) ∈ ball (xiBar : ℂ) virasoroRXiInf := by
      rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |ξ - xiBar| ≤ virasoroChartR0 := abs_le.mpr ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
      exact h1.trans_lt (chartParams.hr_xi0_le.trans_lt (half_lt_self virasoroRXiInf_pos))
    have h1 : HasDerivAt (fun t : ℝ => virasoroUInf (t : ℂ)) (deriv virasoroUInf (ξ : ℂ)) ξ := by
      simpa using ((virasoroUInf_an (ξ : ℂ) hξ_open).differentiableAt.hasDerivAt).comp_ofReal
    have h2 : HasDerivAt (fun t : ℝ => (virasoroUInf (t : ℂ)).re)
        (deriv virasoroUInf (ξ : ℂ)).re ξ :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt ξ h1
    exact h2.const_mul (c' ^ (2 / 3 : ℝ))
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (fun ξ hξ => (hd ξ hξ).continuousAt.continuousWithinAt) ?_
  intro ξ hξ
  have hmem : ξ ∈ Icc (xiBar - virasoroChartR0) (xiBar + virasoroChartR0) := interior_subset hξ
  rw [(hd ξ hmem).deriv]
  have hre_deriv : (deriv virasoroUInf (ξ : ℂ)).re ≤ -1 / (2 * cStar) := by
    have hξ_open : (ξ : ℂ) ∈ ball (xiBar : ℂ) virasoroRXiInf := by
      rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |ξ - xiBar| ≤ virasoroChartR0 := abs_le.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
      exact h1.trans_lt (chartParams.hr_xi0_le.trans_lt (half_lt_self virasoroRXiInf_pos))
    have h1 : HasDerivAt (fun t : ℝ => virasoroUInf (t : ℂ)) (deriv virasoroUInf (ξ : ℂ)) ξ := by
      simpa using ((virasoroUInf_an (ξ : ℂ) hξ_open).differentiableAt.hasDerivAt).comp_ofReal
    have h2 : HasDerivAt (fun t : ℝ => (virasoroUInf (t : ℂ)).re)
        (deriv virasoroUInf (ξ : ℂ)).re ξ :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt ξ h1
    rw [← h2.deriv]
    exact chartParams.h_strictAnti_u ξ hmem
  have hneg : (deriv virasoroUInf (ξ : ℂ)).re < 0 :=
    hre_deriv.trans_lt (div_neg_of_neg_of_pos (by norm_num) (by positivity [cStar_pos]))
  exact mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos hc' _) hneg

lemma virasoroDeltaChart_div_mem {c' u : ℝ} (hc' : 0 < c')
    (hu : |u| ≤ virasoroAC c' ^ 2) :
    virasoroDeltaChart c' u / c' ∈ Icc (xiBar - virasoroChartR0) (xiBar + virasoroChartR0) := by
  set x : ℝ := u * c' ^ (-(2 / 3 : ℝ))
  have hx_mem : x ∈ Icc (-(2 * chartParams.b_V ^ 2)) (2 * chartParams.b_V ^ 2) := by
    have h1 := virasoro_u_mem_ball hc' (u := (u : ℂ))
      (by simpa [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hu)
    rw [show (u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) = (x : ℂ) by dsimp [x]; push_cast; rfl,
      mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] at h1
    unfold virasoroBV at h1
    exact abs_le.mp h1
  have hrange := chartParams.h_u_range x hx_mem
  have heq : virasoroDeltaChart c' u / c' = (virasoroXiInf (x : ℂ)).re := by
    unfold virasoroDeltaChart virasoroXiChartC
    rw [mul_div_cancel_left₀ _ hc'.ne',
      show (u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) = (x : ℂ) by dsimp [x]; push_cast; rfl]
  rw [heq]
  unfold virasoroChartR0
  exact ⟨by linarith [(abs_le.mp hrange).1], by linarith [(abs_le.mp hrange).2]⟩

lemma virasoroUChart_deltaChart {c' u : ℝ} (hc' : 0 < c')
    (hu : |u| ≤ virasoroAC c' ^ 2) :
    virasoroUChart c' (virasoroDeltaChart c' u / c') = u := by
  have hu_open : (u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) ∈ ball (0 : ℂ) virasoroRUInf :=
    virasoro_u_mem_open_ball hc' (u := (u : ℂ))
      (by simpa [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hu)
  have hxi_im : (virasoroXiChartC c' (u : ℂ)).im = 0 := by
    unfold virasoroXiChartC
    have hmul : (u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) =
        ((u * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) := by push_cast; rfl
    rw [hmul]
    apply virasoroXiInf_ofReal_im
    rwa [hmul, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs] at hu_open
  have hxi_eq : ((virasoroDeltaChart c' u / c' : ℝ) : ℂ) = virasoroXiChartC c' (u : ℂ) := by
    unfold virasoroDeltaChart
    rw [mul_div_cancel_left₀ _ hc'.ne']
    exact Complex.ext rfl hxi_im.symm
  unfold virasoroUChart
  rw [hxi_eq]
  unfold virasoroXiChartC
  rw [virasoroUInf_xiInf hu_open, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, mul_left_comm,
    ← Real.rpow_add hc', show (2 / 3 : ℝ) + -(2 / 3 : ℝ) = 0 by norm_num,
    Real.rpow_zero, mul_one]

lemma virasoroDeltaChart_uChart {c' ξ : ℝ} (hc' : 0 < c')
    (hlo : virasoroDeltaChart c' (virasoroAC c' ^ 2) / c' ≤ ξ)
    (hhi : ξ ≤ virasoroDeltaChart c' (-(virasoroAC c' ^ 2)) / c') :
    virasoroDeltaChart c' (virasoroUChart c' ξ) = c' * ξ := by
  have hmem_lo := virasoroDeltaChart_div_mem hc' (by rw [abs_of_nonneg (sq_nonneg _)])
  have hmem_hi := virasoroDeltaChart_div_mem hc'
    (by rw [abs_neg, abs_of_nonneg (sq_nonneg _)])
  have hξ_mem : ξ ∈ Icc (xiBar - virasoroChartR0) (xiBar + virasoroChartR0) :=
    ⟨hmem_lo.1.trans hlo, hhi.trans hmem_hi.2⟩
  have hξ_open : (ξ : ℂ) ∈ ball (xiBar : ℂ) virasoroRXiInf := by
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |ξ - xiBar| ≤ virasoroChartR0 := abs_le.mpr ⟨by linarith [hξ_mem.1], by linarith [hξ_mem.2]⟩
    exact h1.trans_lt (chartParams.hr_xi0_le.trans_lt (half_lt_self virasoroRXiInf_pos))
  have hu_im : (virasoroUInf (ξ : ℂ)).im = 0 := by
    apply virasoroUInf_ofReal_im'
    rwa [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hξ_open
  have huc_eq : ((virasoroUChart c' ξ * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) = virasoroUInf (ξ : ℂ) := by
    unfold virasoroUChart
    refine Complex.ext ?_ hu_im.symm
    simp only [Complex.ofReal_re]
    rw [mul_right_comm, ← Real.rpow_add hc',
      show (2 / 3 : ℝ) + -(2 / 3 : ℝ) = 0 by norm_num, Real.rpow_zero, one_mul]
  unfold virasoroDeltaChart virasoroXiChartC
  have hmul : ((virasoroUChart c' ξ : ℝ) : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) =
      virasoroUInf (ξ : ℂ) := by
    calc ((virasoroUChart c' ξ : ℝ) : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)
        = ((virasoroUChart c' ξ * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) := by push_cast; rfl
      _ = virasoroUInf (ξ : ℂ) := huc_eq
  rw [hmul, virasoroXiInf_uInf hξ_open, Complex.ofReal_re]

lemma virasoro_deltaChart_err {c' u : ℝ} (hc' : 0 < c')
    (hu : |u| ≤ virasoroAC c' ^ 2) :
    |virasoroDeltaChart c' u - (xiBar * c' - cStar * c' ^ (1 / 3 : ℝ) * u)| ≤
      chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * u ^ 2 := by
  have hw_ball : (u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) ∈ closedBall (0 : ℂ) (2 * virasoroBV ^ 2) :=
    virasoro_u_mem_ball hc' (by simpa [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hu)
  have herr := chartParams.hxi_err _ hw_ball
  have hre : ‖(virasoroXiChartC c' (u : ℂ) - ((xiBar : ℂ) - (cStar : ℂ) * ((u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)))).re‖ ≤
      ‖virasoroXiChartC c' (u : ℂ) - ((xiBar : ℂ) - (cStar : ℂ) * ((u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)))‖ :=
    Complex.abs_re_le_norm _
  have hre_lhs : |virasoroDeltaChart c' u / c' - (xiBar - cStar * (u * c' ^ (-(2 / 3 : ℝ))))| ≤
      chartParams.C_xi * (|u| * c' ^ (-(2 / 3 : ℝ))) ^ 2 := by
    have hnorm_w : ‖(u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)‖ = |u| * c' ^ (-(2 / 3 : ℝ)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg hc'.le _)]
    rw [hnorm_w] at herr
    have hlhs : (virasoroXiChartC c' (u : ℂ) -
        ((xiBar : ℂ) - (cStar : ℂ) * ((u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)))).re =
        virasoroDeltaChart c' u / c' - (xiBar - cStar * (u * c' ^ (-(2 / 3 : ℝ)))) := by
      unfold virasoroDeltaChart virasoroXiChartC
      rw [mul_div_cancel_left₀ _ hc'.ne']
      simp [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [Real.norm_eq_abs, hlhs] at hre
    exact hre.trans herr
  have hmul := mul_le_mul_of_nonneg_left hre_lhs hc'.le
  rw [← abs_of_pos hc', ← abs_mul, abs_of_pos hc'] at hmul
  have hdiff : c' * (virasoroDeltaChart c' u / c' - (xiBar - cStar * (u * c' ^ (-(2 / 3 : ℝ))))) =
      virasoroDeltaChart c' u - (xiBar * c' - cStar * c' ^ (1 / 3 : ℝ) * u) := by
    have hcr : c' * c' ^ (-(2 / 3 : ℝ)) = c' ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_one_add' hc'.le (by norm_num : (1 : ℝ) + -(2 / 3 : ℝ) ≠ 0)]
      norm_num
    calc c' * (virasoroDeltaChart c' u / c' - (xiBar - cStar * (u * c' ^ (-(2 / 3 : ℝ)))))
        = virasoroDeltaChart c' u - (xiBar * c' - cStar * (c' * c' ^ (-(2 / 3 : ℝ))) * u) := by
          field_simp [hc'.ne']
      _ = virasoroDeltaChart c' u - (xiBar * c' - cStar * c' ^ (1 / 3 : ℝ) * u) := by rw [hcr]
  have hrhs : c' * (chartParams.C_xi * (|u| * c' ^ (-(2 / 3 : ℝ))) ^ 2) =
      chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * u ^ 2 := by
    have hcr2 : c' * (c' ^ (-(2 / 3 : ℝ))) ^ 2 = c' ^ (-(1 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast (c' ^ (-(2 / 3 : ℝ))) 2, ← Real.rpow_mul hc'.le,
        ← Real.rpow_one_add' hc'.le (by norm_num : (1 : ℝ) + (-(2 / 3 : ℝ) * (2 : ℕ)) ≠ 0)]
      norm_num
    calc c' * (chartParams.C_xi * (|u| * c' ^ (-(2 / 3 : ℝ))) ^ 2)
        = chartParams.C_xi * (c' * (c' ^ (-(2 / 3 : ℝ))) ^ 2) * (|u| ^ 2) := by ring
      _ = chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * u ^ 2 := by rw [hcr2, sq_abs]
  rwa [hdiff, hrhs] at hmul

/-- Chart inversion for Step 5 of Theorem `FT-L.FW` (`lower_o1_two_edge.tex`, `wone:ftlfw`). -/
lemma virasoro_deltaChart_inversion {c' u : ℝ} (hc' : 0 < c') (hu : |u| ≤ virasoroAC c' ^ 2) :
    virasoroDeltaChart c' u ≥ xiBar * c' - cStar * c' ^ (1 / 3 : ℝ) * u -
      chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * u ^ 2 := by
  have herr := (abs_le.mp (virasoro_deltaChart_err hc' hu)).1
  linarith

/-- Lower bound `b(u) ≥ xiStar / 2 > 0` on the entire chart disc (used in `LemmaQ` for `(B1)`). -/
lemma virasoro_deltaChart_b_min {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) (virasoroAC c' ^ 2)) :
    ‖virasoroBChart c' u - (xiStar : ℂ)‖ ≤
      min (TipFront.lemmaGPotentialInput_virasoro.r_A / 2) (min 0.05 (xiStar / 4)) := by
  unfold virasoroBChart virasoroXiChartC
  exact chartParams.h_b_range _ (virasoro_u_mem_ball hc' hu)

/-- Uniform smallness `tipEps c' * ‖ζ‖ = ‖b(u) - xiStar‖ ≤ δ_tip` for `lemma_T1` / `lemma_T3_W_bound`. -/
lemma virasoro_deltaChart_tip_cap {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) (virasoroAC c' ^ 2)) :
    ‖virasoroBChart c' u - (xiStar : ℂ)‖ ≤
      min chartParams.ρ₁_tip (min chartParams.ρ₃_tip
        (min (1 / (4 * (chartParams.C_T1_tip + 1) ^ 2)) (1 / (6 * (chartParams.C_W_tip + 1))))) := by
  unfold virasoroBChart virasoroXiChartC
  exact chartParams.h_b_tip_cap _ (virasoro_u_mem_ball hc' hu)

/-- Exposed `lemma_T1` with the exact `ρ₁_tip`, `C_T1_tip`, `ψ_tip` witnesses of `chartParams`. -/
lemma virasoro_lemma_T1 {c' : ℝ} {ζ : ℂ} (hc' : 0 < c')
    (hcut : ¬ (ζ.im = 0 ∧ 0 ≤ ζ.re)) (hζ : tipEps c' * ‖ζ‖ ≤ chartParams.ρ₁_tip) :
    let ε := tipEps c'
    let v := I * ((√ε : ℝ) : ℂ) * (-ζ) ^ (1 / 2 : ℂ)
    let z_b := (sigmaStar : ℂ) + chartParams.ψ_tip v
    ‖v‖ = √(ε * ‖ζ‖) ∧
    0 < z_b.im ∧
    ‖z_b - (sigmaStar : ℂ)‖ ≤ 0.1 ∧
    slitBoundaryMapC z_b = bScale c' ζ ∧
    (∀ w : ℂ, 0 < w.im → slitBoundaryMapC w = bScale c' ζ → w = z_b) ∧
    |z_b.im - √(ε / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re| ≤
      chartParams.C_T1_tip * √(ε * ‖ζ‖) * (√(ε / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re) ∧
    |‖z_b - (sigmaStar : ℂ)‖ - √(ε * ‖ζ‖ / slitQ)| ≤
      chartParams.C_T1_tip * √(ε * ‖ζ‖) * √(ε * ‖ζ‖ / slitQ) ∧
    |z_b.im * ‖z_b - (sigmaStar : ℂ)‖ - (ε / slitQ) * tipDist ζ| ≤
      chartParams.C_T1_tip * √(ε * ‖ζ‖) * ((ε / slitQ) * tipDist ζ) :=
  chartParams.hT1_tip hc' hcut hζ

/-- Exposed `lemma_T3_W_bound` with the exact `ρ₃_tip`, `C_W_tip` witnesses of `chartParams`. -/
lemma virasoro_lemma_T3_W {c' : ℝ} {ζ : ℂ} (hc' : 39 ≤ c')
    (hζ : tipEps c' * ‖ζ‖ ≤ chartParams.ρ₃_tip) :
    let b := bScale c' ζ
    ‖W_C c' b - (kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖ ≤
      chartParams.C_W_tip * (tipEps c' * (1 + ‖ζ‖) + 1 / c') *
        ‖(kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖ :=
  chartParams.hT3_tip hc' hζ

/-- Complex derivative bound `‖deriv (virasoroDeltaChartC c') u‖ ≤ chartParams.C_dxi * c'^(1/3)` on the chart disc. -/
lemma virasoroDeltaChartC_deriv_bound {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) (virasoroAC c' ^ 2)) :
    ‖deriv (virasoroDeltaChartC c') u‖ ≤ chartParams.C_dxi * c' ^ (1 / 3 : ℝ) := by
  let s : ℝ := c' ^ (-(2 / 3 : ℝ))
  let w : ℂ := u * (s : ℂ)
  have hw_mem : w ∈ ball (0 : ℂ) virasoroRUInf := virasoro_u_mem_open_ball hc' hu
  have hw_cl : w ∈ closedBall (0 : ℂ) (2 * virasoroBV ^ 2) := virasoro_u_mem_ball hc' hu
  have hd_xi : HasDerivAt virasoroXiInf (deriv virasoroXiInf w) w :=
    (virasoroXiInf_an w hw_mem).differentiableAt.hasDerivAt
  have hd_lin : HasDerivAt (fun z : ℂ => z * (s : ℂ)) (s : ℂ) u := by
    simpa using (hasDerivAt_id u).mul_const (s : ℂ)
  have hd_comp : HasDerivAt (virasoroDeltaChartC c')
      ((c' : ℂ) * (deriv virasoroXiInf w * (s : ℂ))) u := by
    have h1 := (hd_xi.comp u hd_lin).const_mul (c' : ℂ)
    exact h1.congr_of_eventuallyEq (Eventually.of_forall fun z => rfl)
  rw [hd_comp.deriv]
  have hnorm_s : ‖(s : ℂ)‖ = s := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hc'.le _)]
  have hnorm_c : ‖(c' : ℂ)‖ = c' := by
    rw [Complex.norm_real, Real.norm_of_nonneg hc'.le]
  have hc_pow : c' * s = c' ^ (1 / 3 : ℝ) := by
    dsimp [s]
    rw [← Real.rpow_one_add' hc'.le (by norm_num : (1 : ℝ) + -(2 / 3 : ℝ) ≠ 0)]
    norm_num
  rw [norm_mul, norm_mul, hnorm_c, hnorm_s]
  have hdxi_bd : ‖deriv virasoroXiInf w‖ ≤ chartParams.C_dxi :=
    chartParams.hdxi_bd w hw_cl
  calc c' * (‖deriv virasoroXiInf w‖ * s)
      = ‖deriv virasoroXiInf w‖ * (c' * s) := by ring
    _ ≤ chartParams.C_dxi * c' ^ (1 / 3 : ℝ) := by
        rw [hc_pow]
        exact mul_le_mul_of_nonneg_right hdxi_bd (Real.rpow_nonneg hc'.le _)

/-- Exact Proposition P Step 2 potential identity on `closedBall 0 (virasoroAC c'^2) \ (-∞, 0]`:
`c' * (majorant2D (virasoroBChart c' u) + (tipL (virasoroBChart c' u)).re) = -(4/3) * Re(u^{3/2})`. -/
theorem virasoro_chart_potential_eq {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) (virasoroAC c' ^ 2)) (hcut : ¬ (u.im = 0 ∧ u.re ≤ 0)) :
    c' * (PoissonJensen.majorant2D (virasoroBChart c' u) +
      (tipL (virasoroBChart c' u)).re) = -(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re := by
  let pg := TipFront.lemmaGPotentialInput_virasoro
  let R := chartParams.r_open_cap
  have hR_pos : 0 < R := lt_trans
    (by have := chartParams.hbV_pos; positivity) chartParams.hr_open_cap_gt
  let Ω : Set ℂ := {w : ℂ | w ∈ ball (0 : ℂ) R ∧ ¬ (w.im = 0 ∧ w.re ≤ 0)}
  have hΩ_open : IsOpen Ω := by
    have hclosed : IsClosed {w : ℂ | w.im = 0 ∧ w.re ≤ 0} :=
      (isClosed_singleton.preimage Complex.continuous_im).inter
        (isClosed_Iic.preimage Complex.continuous_re)
    exact isOpen_ball.sdiff hclosed
  let x₀ : ℂ := ((R / 2 : ℝ) : ℂ)
  have hx₀_mem : x₀ ∈ Ω := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hR_pos)]
      exact half_lt_self hR_pos
    · rintro ⟨_, hre⟩
      simp only [x₀, Complex.ofReal_re] at hre
      linarith [half_pos hR_pos]
  have hΩ_pre : IsPreconnected Ω := by
    have hpc : IsPathConnected Ω := by
      refine ⟨x₀, hx₀_mem, fun w hw => ⟨⟨⟨fun t : unitInterval =>
        ((1 - (t : ℝ)) : ℂ) * x₀ + ((t : ℝ) : ℂ) * w, by continuity⟩, by simp, by simp⟩, ?_⟩⟩
      intro t
      have ht0 : 0 ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      let z : ℂ := ((1 - (t : ℝ)) : ℂ) * x₀ + ((t : ℝ) : ℂ) * w
      change z ∈ Ω
      have hz_ball : z ∈ ball (0 : ℂ) R := by
        rw [mem_ball_zero_iff]
        have hw_norm : ‖w‖ < R := mem_ball_zero_iff.mp hw.1
        have hx₀_norm : ‖x₀‖ = R / 2 := by
          dsimp [x₀]
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hR_pos)]
        have hstep : ‖z‖ ≤ (1 - (t : ℝ)) * (R / 2) + (t : ℝ) * ‖w‖ := by
          calc ‖z‖ ≤ ‖((1 - (t : ℝ)) : ℂ) * x₀‖ + ‖((t : ℝ) : ℂ) * w‖ := norm_add_le _ _
            _ = (1 - (t : ℝ)) * (R / 2) + (t : ℝ) * ‖w‖ := by
                rw [norm_mul, norm_mul, hx₀_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
                  Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
                  abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht0]
        rcases eq_or_lt_of_le ht1 with h1 | h1
        · rw [h1, sub_self, zero_mul, zero_add, one_mul] at hstep
          exact hstep.trans_lt hw_norm
        · have hlt : (1 - (t : ℝ)) * (R / 2) < (1 - (t : ℝ)) * R :=
            mul_lt_mul_of_pos_left (half_lt_self hR_pos) (sub_pos.mpr h1)
          have hle : (t : ℝ) * ‖w‖ ≤ (t : ℝ) * R :=
            mul_le_mul_of_nonneg_left hw_norm.le ht0
          linarith
      refine ⟨hz_ball, ?_⟩
      rintro ⟨hz_im, hz_re⟩
      have hzim : z.im = (t : ℝ) * w.im := by
        simp [z, x₀, Complex.add_im, Complex.ofReal_im]
      have hzre : z.re = (1 - (t : ℝ)) * (R / 2) + (t : ℝ) * w.re := by
        simp [z, x₀, Complex.add_re, Complex.ofReal_re]
      rw [hzim] at hz_im
      rcases mul_eq_zero.mp hz_im with ht0_eq | hw_im0
      · rw [ht0_eq] at hzre; linarith [half_pos hR_pos]
      · have hw_re_pos : 0 < w.re := by
          by_contra hle
          exact hw.2 ⟨hw_im0, not_lt.mp hle⟩
        have : 0 < z.re := by
          rw [hzre]
          have h1 : 0 ≤ (1 - (t : ℝ)) * (R / 2) := mul_nonneg (sub_nonneg.mpr ht1) (half_pos hR_pos).le
          rcases eq_or_lt_of_le ht0 with ht_z | ht_p
          · rw [← ht_z]; linarith [half_pos hR_pos]
          · linarith [mul_pos ht_p hw_re_pos]
        linarith
    exact hpc.isConnected.isPreconnected
  let bOfW : ℂ → ℂ := fun w => virasoroBOfXi (virasoroXiInf w)
  let f₁ : ℂ → ℂ := fun w => (KTip : ℂ) * ((xiStar : ℂ) - bOfW w) ^ (3 / 2 : ℂ) *
    pg.A (bOfW w - (xiStar : ℂ))
  let f₂ : ℂ → ℂ := fun w => ((4 / 3 : ℝ) : ℂ) * w ^ (3 / 2 : ℂ)
  have hf_slit : ∀ z : ℂ, 0 < (z ^ (1 / 2 : ℂ)).re → z ∈ slitPlane := fun z hre => by
    rw [Complex.mem_slitPlane_iff]
    by_contra hns
    push Not at hns
    rcases eq_or_lt_of_le hns.1 with hz0 | hz_neg
    · have hz_zero : z = 0 := Complex.ext hz0 hns.2
      rw [hz_zero, Complex.zero_cpow (by norm_num : (1 / 2 : ℂ) ≠ 0), Complex.zero_re] at hre
      exact lt_irrefl 0 hre
    · have hne : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz_neg; exact lt_irrefl 0 hz_neg
      have harg : z.arg = π := Complex.arg_eq_pi_iff.mpr ⟨hz_neg, hns.2⟩
      have hcpow : (z ^ (1 / 2 : ℂ)).re = Real.exp (Real.log ‖z‖ * (1 / 2)) * Real.cos (π / 2) := by
        rw [Complex.cpow_def_of_ne_zero hne]
        have heq : Complex.log z * (1 / 2 : ℂ) =
            ((Real.log ‖z‖ * (1 / 2) : ℝ) : ℂ) + ((π / 2 : ℝ) : ℂ) * Complex.I := by
          refine Complex.ext ?_ ?_
          · simp [Complex.log_re]
          · simp [Complex.log_im, harg]; ring
        rw [heq, Complex.exp_add_mul_I, Complex.mul_re, ← Complex.ofReal_exp,
          ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_re, Complex.ofReal_im,
          Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Real.cos_pi_div_two]
        ring
      rw [Real.cos_pi_div_two, mul_zero] at hcpow
      linarith
  have hf₁_an : AnalyticOnNhd ℂ f₁ Ω := fun w hw => by
    have hw_u : w ∈ ball (0 : ℂ) virasoroRUInf := ball_subset_ball chartParams.hr_open_cap_lt_u.le hw.1
    have hbOfW_w : AnalyticAt ℂ bOfW w := by
      have hre := (langerCore.huInf_real_pos _ (virasoroXiInf_mem hw_u)).1
      exact (virasoroBOfXi_analyticAt hre).comp_of_eq (virasoroXiInf_an w hw_u) rfl
    have hcomp := chartParams.h_tip_comp w hw.1 hw.2
    have hm_pos : 0 < (((xiStar : ℂ) - bOfW w) ^ (1 / 2 : ℂ)).re :=
      lt_of_lt_of_le (mul_pos chartParams.hc_tip_lo_pos
        (by
          by_contra hle
          have hw_re_nn : 0 ≤ (w ^ (1 / 2 : ℂ)).re := cpow_half_re_nonneg w
          have hw_re0 : (w ^ (1 / 2 : ℂ)).re = 0 := le_antisymm (not_lt.mp hle) hw_re_nn
          have him : w.im = 2 * (w ^ (1 / 2 : ℂ)).re * (w ^ (1 / 2 : ℂ)).im := (airySqrtRe_mul_im w).symm
          have hre_w : w.re = (w ^ (1 / 2 : ℂ)).re ^ 2 - (w ^ (1 / 2 : ℂ)).im ^ 2 :=
            (airySqrtRe_sq_sub w).symm
          rw [hw_re0] at him hre_w
          exact hw.2 ⟨by linarith, by nlinarith [sq_nonneg (w ^ (1 / 2 : ℂ)).im]⟩)) hcomp.1
    have hpow_an : AnalyticAt ℂ (fun z => ((xiStar : ℂ) - bOfW z) ^ (3 / 2 : ℂ)) w :=
      (analyticAt_const.sub hbOfW_w).cpow analyticAt_const (hf_slit _ hm_pos)
    have hsub_ball : bOfW w - (xiStar : ℂ) ∈ ball (0 : ℂ) pg.r_A := by
      rw [mem_ball_zero_iff]
      exact (langerCore.huInf_real_pos _ (virasoroXiInf_mem hw_u)).2.1.trans (half_lt_self pg.hr_A_pos)
    have hA_an : AnalyticAt ℂ (fun z => pg.A (bOfW z - (xiStar : ℂ))) w :=
      (pg.hA_an _ hsub_ball).comp_of_eq (AnalyticAt.sub hbOfW_w analyticAt_const) rfl
    exact (analyticAt_const.mul hpow_an).mul hA_an
  have hf₂_an : AnalyticOnNhd ℂ f₂ Ω := fun w hw => by
    have hw_slit : w ∈ slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      by_contra hns; push Not at hns; exact hw.2 ⟨hns.2, hns.1⟩
    exact analyticAt_const.mul (analyticAt_id.cpow analyticAt_const hw_slit)
  have hfreq : ∃ᶠ w in 𝓝[≠] x₀, f₁ w = f₂ w := by
    rw [Filter.frequently_iff]
    intro U hU
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.mem_nhds_iff.mp hV
    let t : ℝ := R / 2 + min (δ / 2) (R / 4)
    have ht_pos : 0 < t := by positivity
    have ht_lt : t < R := by
      have : min (δ / 2) (R / 4) ≤ R / 4 := min_le_right _ _
      dsimp [t]; linarith
    have ht_ne : (t : ℂ) ≠ x₀ := by
      intro h
      have := congrArg Complex.re h
      simp [t, x₀] at this
      linarith [lt_min (half_pos hδ_pos) (by positivity : 0 < R / 4)]
    have ht_memV : (t : ℂ) ∈ V := by
      apply hδ_ball
      rw [mem_ball, dist_eq_norm]
      have hsub : (t : ℂ) - x₀ = ((min (δ / 2) (R / 4) : ℝ) : ℂ) := by
        simp [t, x₀]
      rw [hsub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (lt_min (half_pos hδ_pos) (by positivity))]
      exact (min_le_left _ _).trans_lt (half_lt_self hδ_pos)
    refine ⟨(t : ℂ), hVU ⟨ht_memV, ht_ne⟩, ?_⟩
    have ht_abs : |t| < R := by rw [abs_of_pos ht_pos]; exact ht_lt
    obtain ⟨hb_im, _, hb_sub_abs, hA_re_pos⟩ := chartParams.hbOfW_real t ht_abs
    have ht_u : (t : ℂ) ∈ ball (0 : ℂ) virasoroRUInf := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact ht_abs.trans chartParams.hr_open_cap_lt_u
    have hA_im : (pg.A (bOfW (t : ℂ) - (xiStar : ℂ))).im = 0 := by
      have hsub_eq : bOfW (t : ℂ) - (xiStar : ℂ) = (((bOfW (t : ℂ)).re - xiStar : ℝ) : ℂ) := by
        refine Complex.ext ?_ ?_
        · simp [Complex.sub_re]
        · simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
          exact hb_im
      rw [hsub_eq]
      exact pg.hA_real _ hb_sub_abs
    have hu_eq : virasoroUInf (virasoroXiInf (t : ℂ)) = (t : ℂ) := virasoroUInf_xiInf ht_u
    let r_mz : ℝ := xiStar - (bOfW (t : ℂ)).re
    let r_A : ℝ := (pg.A (bOfW (t : ℂ) - (xiStar : ℂ))).re
    have hmz_eq_r : (xiStar : ℂ) - bOfW (t : ℂ) = (r_mz : ℂ) := by
      refine Complex.ext (by simp [r_mz]) ?_
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub]
      rw [hb_im, neg_zero]
    have hA_eq_r : pg.A (bOfW (t : ℂ) - (xiStar : ℂ)) = (r_A : ℂ) := Complex.ext rfl hA_im
    have hu_real : t = betaTip * r_mz * r_A ^ (2 / 3 : ℝ) := by
      have hre := congrArg Complex.re hu_eq
      dsimp [virasoroUInf] at hre
      change ((betaTip : ℂ) * ((xiStar : ℂ) - bOfW (t : ℂ)) *
        pg.A (bOfW (t : ℂ) - (xiStar : ℂ)) ^ (2 / 3 : ℂ)).re = (t : ℂ).re at hre
      rw [Complex.ofReal_re, hmz_eq_r, hA_eq_r, show (2 / 3 : ℂ) = ((2 / 3 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_cpow hA_re_pos.le, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
        Complex.ofReal_re] at hre
      exact hre.symm
    have hrmz_pos : 0 < r_mz := by
      have h1 : 0 < betaTip * r_mz * r_A ^ (2 / 3 : ℝ) := hu_real ▸ ht_pos
      have h2 : 0 < betaTip * r_A ^ (2 / 3 : ℝ) := mul_pos betaTip_pos (Real.rpow_pos_of_pos hA_re_pos _)
      nlinarith
    have hpow_real : (4 / 3 : ℝ) * t ^ (3 / 2 : ℝ) = KTip * r_mz ^ (3 / 2 : ℝ) * r_A := by
      rw [hu_real, Real.mul_rpow (mul_nonneg betaTip_pos.le hrmz_pos.le) (Real.rpow_nonneg hA_re_pos.le _),
        Real.mul_rpow betaTip_pos.le hrmz_pos.le, ← Real.rpow_mul hA_re_pos.le,
        show (2 / 3 : ℝ) * (3 / 2 : ℝ) = 1 by norm_num, Real.rpow_one]
      calc (4 / 3 : ℝ) * (betaTip ^ (3 / 2 : ℝ) * r_mz ^ (3 / 2 : ℝ) * r_A)
          = ((4 / 3 : ℝ) * betaTip ^ (3 / 2 : ℝ)) * r_mz ^ (3 / 2 : ℝ) * r_A := by ring
        _ = KTip * r_mz ^ (3 / 2 : ℝ) * r_A := by rw [four_thirds_betaTip_rpow]
    dsimp [f₁, f₂]
    rw [hmz_eq_r, hA_eq_r, show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hrmz_pos.le, ← Complex.ofReal_cpow ht_pos.le]
    exact_mod_cast hpow_real.symm
  have heqOn := hf₁_an.eqOn_of_preconnected_of_frequently_eq hf₂_an hΩ_pre hx₀_mem hfreq
  -- Apply `heqOn` at `w = u * c'^{-(2/3)}`
  let w : ℂ := u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)
  have hc'_neg23 : 0 < c' ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hc' _
  have hw_ball : w ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    have h1 := virasoro_u_mem_ball hc' hu
    rw [mem_closedBall_zero_iff] at h1
    unfold virasoroBV at h1
    exact h1.trans_lt chartParams.hr_open_cap_gt
  have hw_cut : ¬ (w.im = 0 ∧ w.re ≤ 0) := by
    intro ⟨him, hre⟩
    apply hcut
    have hw_im' : w.im = u.im * c' ^ (-(2 / 3 : ℝ)) := by
      simp [w, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    have hw_re' : w.re = u.re * c' ^ (-(2 / 3 : ℝ)) := by
      simp [w, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [hw_im'] at him
    rw [hw_re'] at hre
    exact ⟨(mul_eq_zero.mp him).resolve_right hc'_neg23.ne',
      nonpos_of_mul_nonpos_left hre hc'_neg23⟩
  have hfw := heqOn ⟨hw_ball, hw_cut⟩
  have hb_mem : virasoroBChart c' u ∈ ball (xiStar : ℂ) pg.r_A := by
    rw [mem_ball, dist_eq_norm]
    have hb1 := virasoro_deltaChart_b_min hc' hu
    exact hb1.trans_lt ((min_le_left _ _).trans_lt (half_lt_self pg.hr_A_pos))
  have hb_cut : ¬ ((virasoroBChart c' u).im = 0 ∧ xiStar ≤ (virasoroBChart c' u).re) := by
    intro ⟨him, hre⟩
    have hm_nonpos : ((xiStar : ℂ) - bOfW w).re ≤ 0 := by
      dsimp [bOfW]
      change xiStar - (virasoroBChart c' u).re ≤ 0
      linarith
    have hm_im : ((xiStar : ℂ) - bOfW w).im = 0 := by
      dsimp [bOfW]
      change 0 - (virasoroBChart c' u).im = 0
      rw [him, sub_zero]
    have hzero : (((xiStar : ℂ) - bOfW w) ^ (1 / 2 : ℂ)).re = 0 := by
      let z := (xiStar : ℂ) - bOfW w
      rcases eq_or_lt_of_le hm_nonpos with hz0 | hz_neg
      · have hz_zero : z = 0 := Complex.ext hz0 hm_im
        rw [show (xiStar : ℂ) - bOfW w = z from rfl, hz_zero,
          Complex.zero_cpow (by norm_num : (1 / 2 : ℂ) ≠ 0), Complex.zero_re]
      · have hne : z ≠ 0 := fun h => by
          dsimp [z] at h
          rw [h, Complex.zero_re] at hz_neg
          exact lt_irrefl 0 hz_neg
        have harg : z.arg = π := Complex.arg_eq_pi_iff.mpr ⟨hz_neg, hm_im⟩
        rw [Complex.cpow_def_of_ne_zero hne]
        have heq : Complex.log z * (1 / 2 : ℂ) =
            ((Real.log ‖z‖ * (1 / 2) : ℝ) : ℂ) + ((π / 2 : ℝ) : ℂ) * Complex.I := by
          refine Complex.ext ?_ ?_
          · simp [Complex.log_re]
          · simp [Complex.log_im, harg]; ring
        rw [heq, Complex.exp_add_mul_I, Complex.mul_re, ← Complex.ofReal_exp,
          ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_re, Complex.ofReal_im,
          Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Real.cos_pi_div_two]
        ring
    have hcomp := chartParams.h_tip_comp w hw_ball hw_cut
    have hw_re_pos : 0 < (w ^ (1 / 2 : ℂ)).re := by
      by_contra hle
      have hw_re0 : (w ^ (1 / 2 : ℂ)).re = 0 := le_antisymm (not_lt.mp hle) (cpow_half_re_nonneg w)
      have him_w : w.im = 2 * (w ^ (1 / 2 : ℂ)).re * (w ^ (1 / 2 : ℂ)).im := (airySqrtRe_mul_im w).symm
      have hre_w : w.re = (w ^ (1 / 2 : ℂ)).re ^ 2 - (w ^ (1 / 2 : ℂ)).im ^ 2 :=
        (airySqrtRe_sq_sub w).symm
      rw [hw_re0] at him_w hre_w
      exact hw_cut ⟨by linarith, by nlinarith [sq_nonneg (w ^ (1 / 2 : ℂ)).im]⟩
    linarith [mul_pos chartParams.hc_tip_lo_pos hw_re_pos, hcomp.1]
  have hpot := pg.U_add_L_near_tip (virasoroBChart c' u) hb_mem hb_cut
  rw [TipFront.lemmaGPotentialInput_virasoro_U] at hpot
  have hpot_eq : PoissonJensen.majorant2D (virasoroBChart c' u) + (tipL (virasoroBChart c' u)).re =
      -(f₁ w).re := by
    rw [hpot]
    dsimp [f₁, bOfW]
    change (-KTip * ((xiStar : ℂ) - virasoroBChart c' u) ^ (3 / 2 : ℂ) *
      pg.A (virasoroBChart c' u - (xiStar : ℂ))).re =
      -(((KTip : ℂ) * ((xiStar : ℂ) - virasoroBChart c' u) ^ (3 / 2 : ℂ) *
        pg.A (virasoroBChart c' u - (xiStar : ℂ))).re)
    rw [← Complex.neg_re]
    congr 1; ring
  have hw_cpow : w ^ (3 / 2 : ℂ) = ((c'⁻¹ : ℝ) : ℂ) * u ^ (3 / 2 : ℂ) := by
    dsimp [w]
    rw [mul_comm u, ofReal_mul_cpow hc'_neg23 u (3 / 2 : ℂ),
      show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hc'_neg23.le, ← Real.rpow_mul hc'.le,
      show -(2 / 3 : ℝ) * (3 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have hf₂_re : (f₂ w).re = (4 / 3 : ℝ) * c'⁻¹ * (u ^ (3 / 2 : ℂ)).re := by
    dsimp [f₂]
    rw [hw_cpow, show ((4 / 3 : ℝ) : ℂ) * (((c'⁻¹ : ℝ) : ℂ) * u ^ (3 / 2 : ℂ)) =
      (((4 / 3 * c'⁻¹ : ℝ) : ℂ) * u ^ (3 / 2 : ℂ)) by push_cast; ring, Complex.re_ofReal_mul]
  rw [hpot_eq, congrArg Complex.re hfw, hf₂_re]
  field_simp [hc'.ne']

/-- Uniform tip comparability on the chart disc (`lower_o1_two_edge.tex`, `ft:PP` / Lemma Q):
relating `((-ζ)^{1/2}).re` and `tipDist ζ` (at `ζ = c'^{2/3} (virasoroBChart c' u - xiStar)`)
with `(u^{1/2}).re` and `√‖u‖ * (u^{1/2}).re`. -/
lemma virasoro_tip_comparability {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) (virasoroAC c' ^ 2)) (hcut : ¬ (u.im = 0 ∧ u.re ≤ 0)) :
    let ζ : ℂ := ((tipEps c')⁻¹ : ℝ) * (virasoroBChart c' u - (xiStar : ℂ))
    chartParams.c_tip_lo * (u ^ (1 / 2 : ℂ)).re ≤ ((-ζ) ^ (1 / 2 : ℂ)).re ∧
    ((-ζ) ^ (1 / 2 : ℂ)).re ≤ chartParams.c_tip_hi * (u ^ (1 / 2 : ℂ)).re ∧
    chartParams.c_tip_lo * ‖u‖ ≤ ‖ζ‖ ∧
    ‖ζ‖ ≤ chartParams.c_tip_hi * ‖u‖ ∧
    chartParams.c_tip_lo ^ (3 / 2 : ℝ) * √‖u‖ * (u ^ (1 / 2 : ℂ)).re ≤ tipDist ζ := by
  let w : ℂ := u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)
  have hc'_neg23 : 0 < c' ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hc' _
  have hc'_neg13 : 0 < c' ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc' _
  have hw_ball : w ∈ ball (0 : ℂ) chartParams.r_open_cap := by
    rw [mem_ball_zero_iff]
    have h1 := virasoro_u_mem_ball hc' hu
    rw [mem_closedBall_zero_iff] at h1
    unfold virasoroBV at h1
    exact h1.trans_lt chartParams.hr_open_cap_gt
  have hw_cut : ¬ (w.im = 0 ∧ w.re ≤ 0) := by
    intro ⟨him, hre⟩
    apply hcut
    have hw_im' : w.im = u.im * c' ^ (-(2 / 3 : ℝ)) := by
      simp [w, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    have hw_re' : w.re = u.re * c' ^ (-(2 / 3 : ℝ)) := by
      simp [w, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [hw_im'] at him
    rw [hw_re'] at hre
    exact ⟨(mul_eq_zero.mp him).resolve_right hc'_neg23.ne',
      nonpos_of_mul_nonpos_left hre hc'_neg23⟩
  have hcomp := chartParams.h_tip_comp w hw_ball hw_cut
  let mz : ℂ := (xiStar : ℂ) - virasoroBOfXi (virasoroXiInf w)
  let ζ : ℂ := ((tipEps c')⁻¹ : ℝ) * (virasoroBChart c' u - (xiStar : ℂ))
  have hζ_neg : -ζ = ((c' ^ (2 / 3 : ℝ) : ℝ) : ℂ) * mz := by
    have heps : (tipEps c')⁻¹ = c' ^ (2 / 3 : ℝ) := by
      unfold tipEps
      rw [Real.rpow_neg hc'.le, inv_inv]
    dsimp [ζ, mz]
    unfold virasoroBChart virasoroXiChartC
    rw [heps]
    ring
  have hc'23 : 0 < c' ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc' _
  have hsqrt_scale : c' ^ (1 / 3 : ℝ) * (w ^ (1 / 2 : ℂ)).re = (u ^ (1 / 2 : ℂ)).re := by
    dsimp [w]
    rw [mul_comm u, ofReal_mul_cpow hc'_neg23 u (1 / 2 : ℂ),
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hc'_neg23.le, ← Real.rpow_mul hc'.le,
      show -(2 / 3 : ℝ) * (1 / 2 : ℝ) = -(1 / 3 : ℝ) by norm_num,
      Complex.re_ofReal_mul, ← mul_assoc, ← Real.rpow_add hc',
      add_neg_cancel, Real.rpow_zero, one_mul]
  have hmz_scale : ((-ζ) ^ (1 / 2 : ℂ)).re = c' ^ (1 / 3 : ℝ) * (mz ^ (1 / 2 : ℂ)).re := by
    rw [hζ_neg, ofReal_mul_cpow hc'23 mz (1 / 2 : ℂ),
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hc'23.le, ← Real.rpow_mul hc'.le,
      show (2 / 3 : ℝ) * (1 / 2 : ℝ) = 1 / 3 by norm_num,
      Complex.re_ofReal_mul]
  have hnorm_w : ‖w‖ = c' ^ (-(2 / 3 : ℝ)) * ‖u‖ := by
    dsimp [w]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc'_neg23.le, mul_comm]
  have hnorm_ζ : ‖ζ‖ = c' ^ (2 / 3 : ℝ) * ‖mz‖ := by
    rw [← norm_neg ζ, hζ_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc'23.le]
  have hlo1 : chartParams.c_tip_lo * (u ^ (1 / 2 : ℂ)).re ≤ ((-ζ) ^ (1 / 2 : ℂ)).re := by
    rw [hmz_scale, ← hsqrt_scale]
    calc chartParams.c_tip_lo * (c' ^ (1 / 3 : ℝ) * (w ^ (1 / 2 : ℂ)).re)
        = c' ^ (1 / 3 : ℝ) * (chartParams.c_tip_lo * (w ^ (1 / 2 : ℂ)).re) := by ring
      _ ≤ c' ^ (1 / 3 : ℝ) * (mz ^ (1 / 2 : ℂ)).re :=
          mul_le_mul_of_nonneg_left hcomp.1 (Real.rpow_nonneg hc'.le _)
  have hhi1 : ((-ζ) ^ (1 / 2 : ℂ)).re ≤ chartParams.c_tip_hi * (u ^ (1 / 2 : ℂ)).re := by
    rw [hmz_scale, ← hsqrt_scale]
    calc c' ^ (1 / 3 : ℝ) * (mz ^ (1 / 2 : ℂ)).re
        ≤ c' ^ (1 / 3 : ℝ) * (chartParams.c_tip_hi * (w ^ (1 / 2 : ℂ)).re) :=
          mul_le_mul_of_nonneg_left hcomp.2.1 (Real.rpow_nonneg hc'.le _)
      _ = chartParams.c_tip_hi * (c' ^ (1 / 3 : ℝ) * (w ^ (1 / 2 : ℂ)).re) := by ring
  have hcr_pow : c' ^ (2 / 3 : ℝ) * c' ^ (-(2 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add hc', add_neg_cancel, Real.rpow_zero]
  have hnorm_lo : chartParams.c_tip_lo * ‖u‖ ≤ ‖ζ‖ := by
    rw [hnorm_ζ]
    have hmul := mul_le_mul_of_nonneg_left hcomp.2.2.1 hc'23.le
    rw [hnorm_w] at hmul
    calc chartParams.c_tip_lo * ‖u‖
        = (c' ^ (2 / 3 : ℝ) * c' ^ (-(2 / 3 : ℝ))) * (chartParams.c_tip_lo * ‖u‖) := by
          rw [hcr_pow, one_mul]
      _ = c' ^ (2 / 3 : ℝ) * (chartParams.c_tip_lo * (c' ^ (-(2 / 3 : ℝ)) * ‖u‖)) := by ring
      _ ≤ c' ^ (2 / 3 : ℝ) * ‖mz‖ := hmul
  have hnorm_hi : ‖ζ‖ ≤ chartParams.c_tip_hi * ‖u‖ := by
    rw [hnorm_ζ]
    have hmul := mul_le_mul_of_nonneg_left hcomp.2.2.2 hc'23.le
    rw [hnorm_w] at hmul
    calc c' ^ (2 / 3 : ℝ) * ‖mz‖
        ≤ c' ^ (2 / 3 : ℝ) * (chartParams.c_tip_hi * (c' ^ (-(2 / 3 : ℝ)) * ‖u‖)) := hmul
      _ = (c' ^ (2 / 3 : ℝ) * c' ^ (-(2 / 3 : ℝ))) * (chartParams.c_tip_hi * ‖u‖) := by ring
      _ = chartParams.c_tip_hi * ‖u‖ := by rw [hcr_pow, one_mul]
  have hdist : chartParams.c_tip_lo ^ (3 / 2 : ℝ) * √‖u‖ * (u ^ (1 / 2 : ℂ)).re ≤ tipDist ζ := by
    unfold tipDist
    have h1 : √(chartParams.c_tip_lo * ‖u‖) * (chartParams.c_tip_lo * (u ^ (1 / 2 : ℂ)).re) ≤
        √‖ζ‖ * ((-ζ) ^ (1 / 2 : ℂ)).re := by
      gcongr
      exact mul_nonneg chartParams.hc_tip_lo_pos.le (cpow_half_re_nonneg u)
    have h2 : √(chartParams.c_tip_lo * ‖u‖) * (chartParams.c_tip_lo * (u ^ (1 / 2 : ℂ)).re) =
        chartParams.c_tip_lo ^ (3 / 2 : ℝ) * √‖u‖ * (u ^ (1 / 2 : ℂ)).re := by
      rw [Real.sqrt_mul chartParams.hc_tip_lo_pos.le, Real.sqrt_eq_rpow]
      have : chartParams.c_tip_lo ^ (1 / 2 : ℝ) * chartParams.c_tip_lo =
          chartParams.c_tip_lo ^ (3 / 2 : ℝ) := by
        conv_lhs => rhs; rw [← Real.rpow_one chartParams.c_tip_lo]
        rw [← Real.rpow_add chartParams.hc_tip_lo_pos]
        norm_num
      calc chartParams.c_tip_lo ^ (1 / 2 : ℝ) * √‖u‖ * (chartParams.c_tip_lo * (u ^ (1 / 2 : ℂ)).re)
          = (chartParams.c_tip_lo ^ (1 / 2 : ℝ) * chartParams.c_tip_lo) * √‖u‖ * (u ^ (1 / 2 : ℂ)).re := by
            ring
        _ = chartParams.c_tip_lo ^ (3 / 2 : ℝ) * √‖u‖ * (u ^ (1 / 2 : ℂ)).re := by rw [this]
    exact h2.symm.trans_le h1
  exact ⟨hlo1, hhi1, hnorm_lo, hnorm_hi, hdist⟩

end FormalResearch.ModularBootstrap.ConcreteBootstrap
