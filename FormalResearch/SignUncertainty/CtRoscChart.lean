module

public import Mathlib
public import FormalResearch.SignUncertainty.CtDyadicEta
public import FormalResearch.SignUncertainty.CtChartPsiAnalytic
public import FormalResearch.SignUncertainty.HankelLangerPsiReal
public import FormalResearch.SignUncertainty.CtBandTop

/-!
# `f_c = Ψ̃(φ_c) φ_c'` as a holomorphic, real-symmetric function on a disc (`(ct:rosc)`, proof)

`constant_terms_lower.tex`, `ct:dyadic` (3), proof of `(ct:rosc)`: "`H = W_6 f_c` is holomorphic on `D_R^+` and real on `ℝ`".  In Lean the complex
chart `φ_c = ctPhiC c₁ ε c` is holomorphic on a disc of radius `> R_max = 4c₁²c^{2/3}` and `Ψ̃ = hankelPsi c f` on the Langer disc
`‖ũ‖ ≤ langerRadius c`; for `c₁` small `φ_c` maps `‖u‖ ≤ R_max` into that disc, hence (compactness) a slightly larger disc.

* `holo_reflect`: a function holomorphic on `ball 0 r` and real on `(-r, r)` is conjugation-symmetric (identity theorem).
* `ctFcC_holo`: `ctFcC c₁ ε c f` is holomorphic on `ball 0 ρ`, `ρ > R_max`, and real-symmetric there.

All proved.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- **Reflection principle on a disc**: `G` holomorphic on `ball 0 r` and real on the real segment satisfies `G(z̄) = conj G(z)`. -/
lemma holo_reflect {G : ℂ → ℂ} {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (hG : DifferentiableOn ℂ G (ball 0 r))
    (hreal : ∀ x : ℝ, |x| < r' → (G x).im = 0) :
    ∀ z ∈ ball (0 : ℂ) r, G ((starRingEnd ℂ) z) = (starRingEnd ℂ) (G z) := by
  set G2 : ℂ → ℂ := fun w => (starRingEnd ℂ) (G ((starRingEnd ℂ) w)) with hG2
  have hconj : ∀ w ∈ ball (0 : ℂ) r, (starRingEnd ℂ) w ∈ ball (0 : ℂ) r := fun w hw => by
    rwa [mem_ball_zero_iff, Complex.norm_conj, ← mem_ball_zero_iff]
  have hG2d : DifferentiableOn ℂ G2 (ball 0 r) := by
    intro w hw
    have := ((hG _ (hconj w hw)).differentiableAt (isOpen_ball.mem_nhds (hconj w hw))).conj_conj
    simp only [Complex.conj_conj] at this
    exact this.differentiableWithinAt
  have han : AnalyticOnNhd ℂ G (ball 0 r) := hG.analyticOnNhd isOpen_ball
  have han2 : AnalyticOnNhd ℂ G2 (ball 0 r) := hG2d.analyticOnNhd isOpen_ball
  have hz0 : (0 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_self hr
  have heq : EqOn G G2 (ball 0 r) := by
    refine han.eqOn_of_preconnected_of_frequently_eq han2 (convex_ball _ _).isPreconnected hz0 ?_
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), G (t : ℂ) = G2 (t : ℂ) := by
      have h0 : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), |t| < min r r' := by
        have := (continuous_abs.tendsto (0 : ℝ)).eventually
          (gt_mem_nhds (by simpa using lt_min hr hr' : |(0 : ℝ)| < min r r'))
        simpa using this
      filter_upwards [mem_nhdsWithin_of_mem_nhds h0] with t ht
      have h1 := hreal t (lt_of_lt_of_le ht (min_le_right _ _))
      simp only [hG2, Complex.conj_ofReal]
      exact ((Complex.conj_eq_iff_im.2 h1).symm)
    have htend : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa using ht
    by_contra hcon
    have h1 := Filter.not_frequently.mp hcon
    have h2 := htend.eventually h1
    obtain ⟨t, ht1, ht2⟩ := (hev.and h2).exists
    exact ht2 ht1
  intro z hz
  have := heq hz
  simp only [hG2] at this
  rw [this, Complex.conj_conj]


/-- The derivative of a holomorphic function that is real on a real interval is real there. -/
lemma deriv_im_eq_zero_of_real {Φ : ℂ → ℂ} {r : ℝ} (hd : DifferentiableOn ℂ Φ (ball 0 r))
    (hreal : ∀ x : ℝ, |x| < r → (Φ x).im = 0) {x : ℝ} (hx : |x| < r) : (deriv Φ (x : ℂ)).im = 0 := by
  have hxb : (x : ℂ) ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hx
  have hda : HasDerivAt Φ (deriv Φ (x : ℂ)) (x : ℂ) :=
    ((hd _ hxb).differentiableAt (isOpen_ball.mem_nhds hxb)).hasDerivAt
  have h1 : HasDerivAt (fun t : ℝ => (Φ (t : ℂ)).re) (deriv Φ (x : ℂ)).re x := hda.real_of_complex
  have hev : ∀ᶠ t : ℝ in 𝓝 x, |t| < r :=
    (continuous_abs.tendsto x).eventually (gt_mem_nhds hx)
  have h2 : HasDerivAt (fun t : ℝ => Φ (t : ℂ)) (deriv Φ (x : ℂ)) x := hda.comp_ofReal
  have h3 : HasDerivAt (fun t : ℝ => ((Φ (t : ℂ)).re : ℂ)) (((deriv Φ (x : ℂ)).re : ℝ) : ℂ) x :=
    h1.ofReal_comp
  have h4 : (fun t : ℝ => ((Φ (t : ℂ)).re : ℂ)) =ᶠ[𝓝 x] (fun t : ℝ => Φ (t : ℂ)) := by
    filter_upwards [hev] with t ht
    exact Complex.ext (by simp) (by simpa using (hreal t ht).symm)
  have h5 := (h3.congr_of_eventuallyEq h4.symm)
  have := h2.unique h5
  have := congrArg Complex.im this
  simpa using this


/-- **`f_c` is holomorphic on a disc `> R_max` and real-symmetric** (`ct:dyadic` (3), proof of `(ct:rosc)`): for `c₁ ≤ 1/900` and `c` large,
`ctFcC c₁ ε c f = Ψ̃(φ_c) φ_c'` is holomorphic on `ball 0 ρ` for some `ρ > R_max`, `φ_c` maps that disc into the Langer disc, and
`f_c(ū) = conj f_c(u)`. -/
lemma ctFcC_holo {c₁ ε c C : ℝ} {f : ℝ → ℝ} (hc₁ : 0 < c₁) (hs : c₁ ≤ 1 / 900)
    (hbody : CtChartBody c₁ ε c C) (hc : 3e6 ≤ c) (hcC : C * c ^ (-(1 / 3 : ℝ)) < 1)
    (hf : IsHankelEigenfn c ε f) :
    ∃ ρ : ℝ, ctRmax c₁ c < ρ ∧ DifferentiableOn ℂ (ctFcC c₁ ε c f) (ball 0 ρ) ∧
      (∀ u ∈ ball (0 : ℂ) ρ, ‖ctPhiC c₁ ε c u‖ < langerRadius c) ∧
      (∀ u ∈ ball (0 : ℂ) ρ, ctFcC c₁ ε c f ((starRingEnd ℂ) u) = (starRingEnd ℂ) (ctFcC c₁ ε c f u)) := by
  obtain ⟨hex, hdom, him, hcl⟩ := hbody
  obtain ⟨⟨ρ0, hρ0, hd0⟩, -⟩ := ctPhiC_spec hex
  have hc0 : 0 < c := by linarith
  have hRm : 0 < ctRmax c₁ c := ctRmax_pos hc₁ hc0
  set Rm := ctRmax c₁ c with hRmdef
  set A := langerRadius c with hAdef
  set Φ := ctPhiC c₁ ε c with hΦ
  have hA : Rm + C * c ^ (-(1 / 3 : ℝ)) < A := by
    have h1 := hankelBand_radius_ge_one hc
    have hp : 0 ≤ c ^ (2 / 3 : ℝ) := Real.rpow_nonneg hc0.le _
    have h2 : Rm ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by
      rw [hRmdef]; unfold ctRmax
      have : 4 * c₁ ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by nlinarith
      nlinarith
    linarith
  have hcont : ContinuousOn Φ (ball 0 ρ0) := hd0.continuousOn
  set U : Set ℂ := ball 0 ρ0 ∩ Φ ⁻¹' (ball 0 A) with hU
  have hUo : IsOpen U := hcont.isOpen_inter_preimage isOpen_ball isOpen_ball
  have hKU : closedBall (0 : ℂ) Rm ⊆ U := by
    intro u hu
    have hu' : ‖u‖ ≤ Rm := mem_closedBall_zero_iff.1 hu
    refine ⟨by rw [mem_ball_zero_iff]; linarith, ?_⟩
    rw [mem_preimage, mem_ball_zero_iff]
    have := (hcl u hu').1
    calc ‖Φ u‖ = ‖u + (Φ u - u)‖ := by ring_nf
      _ ≤ ‖u‖ + ‖Φ u - u‖ := norm_add_le _ _
      _ < A := by linarith
  obtain ⟨δ, hδ, hth⟩ := (isCompact_closedBall (0 : ℂ) Rm).exists_thickening_subset_open hUo hKU
  rw [thickening_closedBall hδ hRm.le] at hth
  refine ⟨δ + Rm, by linarith, ?_, fun u hu => ?_, ?_⟩
  · have hsub : ball (0 : ℂ) (δ + Rm) ⊆ ball 0 ρ0 := fun u hu => (hth hu).1
    have hΨ : DifferentiableOn ℂ (hankelPsi c f) (closedBall 0 A) := by
      rw [hAdef, langerRadius_eq]; exact (analyticOnNhd_hankelPsi hc0 hf).differentiableOn
    have h1 : DifferentiableOn ℂ (fun u => hankelPsi c f (Φ u)) (ball 0 (δ + Rm)) :=
      hΨ.comp (hd0.mono hsub) (fun u hu => by simpa [mem_closedBall_zero_iff] using (le_of_lt (by simpa [mem_preimage, mem_ball_zero_iff] using (hth hu).2 : ‖Φ u‖ < A)))
    have h2 : DifferentiableOn ℂ (deriv Φ) (ball 0 (δ + Rm)) :=
      ((hd0.deriv isOpen_ball)).mono hsub
    exact h1.mul h2
  · simpa [mem_preimage, mem_ball_zero_iff] using (hth hu).2
  · have hd1 : DifferentiableOn ℂ (ctFcC c₁ ε c f) (ball 0 (δ + Rm)) := by
      have hsub : ball (0 : ℂ) (δ + Rm) ⊆ ball 0 ρ0 := fun u hu => (hth hu).1
      have hΨ : DifferentiableOn ℂ (hankelPsi c f) (closedBall 0 A) := by
        rw [hAdef, langerRadius_eq]; exact (analyticOnNhd_hankelPsi hc0 hf).differentiableOn
      exact (hΨ.comp (hd0.mono hsub) (fun u hu => by simpa [mem_closedBall_zero_iff] using (le_of_lt (by simpa [mem_preimage, mem_ball_zero_iff] using (hth hu).2 : ‖Φ u‖ < A)))).mul
        ((hd0.deriv isOpen_ball).mono hsub)
    refine holo_reflect (by linarith) hRm hd1 (fun x hx => ?_)
    have hxR : |x| ≤ Rm := hx.le
    have hΦim : (Φ (x : ℂ)).im = 0 := him x hxR
    have hΦA : ‖Φ (x : ℂ)‖ < A := by
      have hxb : ‖(x : ℂ)‖ ≤ Rm := by rwa [Complex.norm_real, Real.norm_eq_abs]
      have := (hcl (x : ℂ) hxb).1
      calc ‖Φ (x : ℂ)‖ = ‖(x : ℂ) + (Φ (x : ℂ) - x)‖ := by ring_nf
        _ ≤ ‖(x : ℂ)‖ + ‖Φ (x : ℂ) - x‖ := norm_add_le _ _
        _ < A := by linarith
    have hre : (Φ (x : ℂ)) = (((Φ (x : ℂ)).re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using hΦim)
    have hΨim : (hankelPsi c f (Φ (x : ℂ))).im = 0 := by
      rw [hre]
      refine hankelPsi_real hc0 f (x := (Φ (x : ℂ)).re) ?_
      have : |(Φ (x : ℂ)).re| ≤ ‖Φ (x : ℂ)‖ := Complex.abs_re_le_norm _
      have h2 : A = c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := langerRadius_eq c
      linarith
    have hdim : (deriv Φ (x : ℂ)).im = 0 :=
      deriv_im_eq_zero_of_real (r := Rm) (hd0.mono (ball_subset_ball (by linarith))) (fun y hy => him y hy.le) hx
    have e : (ctFcC c₁ ε c f (x : ℂ)).im = (hankelPsi c f (Φ (x : ℂ)) * deriv Φ (x : ℂ)).im := rfl
    rw [e, Complex.mul_im, hΨim, hdim]; ring


/-- **The complex chart does not depend on `c₁`** (identity theorem): for `c₁ ≤ c₁'` both charts agree on a disc of radius `> R_max(c₁)`.
Needs the window `PsiWin ε ρW MW` (to produce an accumulation point of `û`-images of the real window) with `8c₁² ≤ ρW/2` and `MW < 2c₁²c`. -/
lemma ctPhiC_agree {c₁ c₁' ε c C C' ρW MW : ℝ} (hc : 0 < c) (hc₁ : 0 < c₁) (hle : c₁ ≤ c₁')
    (hb : CtChartBody c₁ ε c C) (hb' : CtChartBody c₁' ε c C') (hW : PsiWin ε ρW MW)
    (hν : 8 * c₁ ^ 2 ≤ ρW / 2) (hMc : MW < 2 * c₁ ^ 2 * c) :
    ∃ ρ : ℝ, ctRmax c₁ c < ρ ∧ EqOn (ctPhiC c₁ ε c) (ctPhiC c₁' ε c) (ball 0 ρ) := by
  have hR := ctRmax_pos hc₁ hc
  set R := ctRmax c₁ c with hRdef
  have hmono : R ≤ ctRmax c₁' c := by
    rw [hRdef]; unfold ctRmax
    have : c₁ ^ 2 ≤ c₁' ^ 2 := pow_le_pow_left₀ hc₁.le hle 2
    have h2 : 0 ≤ c ^ (2 / 3 : ℝ) := Real.rpow_nonneg hc.le _
    nlinarith [mul_le_mul_of_nonneg_right this h2]
  have h₁ := ctPhiC_spec hb.1
  have h₂ : IsCtChartExt c₁ ε c (ctPhiC c₁' ε c) := by
    obtain ⟨⟨ρ', hρ', hd'⟩, hleft⟩ := ctPhiC_spec hb'.1
    exact ⟨⟨ρ', lt_of_le_of_lt hmono hρ', hd'⟩, fun w hw hw0 hwR => hleft w hw hw0 (hwR.trans hmono)⟩
  have hμR : ctMu c * R ≤ 8 * c₁ ^ 2 := ctMu_mul_ctRmax_le hc
  have hw0 : -R / 2 < 0 := by linarith
  have hwρ : -ρW < ctMu c * (-R / 2) := by
    have : ctMu c * (-R / 2) = -(ctMu c * R) / 2 := by ring
    rw [this]; linarith [hW.1]
  have hcont : ContinuousAt (ctUhat ε c) (-R / 2) := (ctUhat_hasDerivAt hW hc hw0 hwρ).continuousAt
  have hz0 : |ctUhat ε c (-R / 2)| < R := by
    have h1 := abs_ctUhat_sub_le hW hc hw0 hwρ
    have h3 : ctLam c * MW < R / 2 := by
      have hlc := ctLam_le_rpow_neg hc
      have : ctLam c * MW ≤ c ^ (-(1 / 3 : ℝ)) * MW := mul_le_mul_of_nonneg_right hlc hW.2.1
      have hcc : c ^ (-(1 / 3 : ℝ)) * c ^ (1 : ℝ) = c ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_add hc]; norm_num
      have hpos : 0 < c ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc _
      have e1 : R / 2 = 2 * c₁ ^ 2 * c ^ (2 / 3 : ℝ) := by rw [hRdef]; unfold ctRmax; ring
      rw [e1, ← hcc, Real.rpow_one]
      nlinarith [mul_lt_mul_of_pos_left hMc hpos]
    have := abs_le.mp h1
    rw [abs_lt]
    constructor <;> nlinarith [this.1, this.2]
  exact ctChartExt_unique hc hc₁ hb.2.1 hcont hz0 h₁ h₂

/-- info: 'FormalResearch.SignUncertainty.ctFcC_holo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctFcC_holo

/-- info: 'FormalResearch.SignUncertainty.ctPhiC_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctPhiC_agree

/-- info: 'FormalResearch.SignUncertainty.holo_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms holo_reflect

end FormalResearch.SignUncertainty
