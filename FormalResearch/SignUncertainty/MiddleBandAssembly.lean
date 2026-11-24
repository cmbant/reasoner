module

public import FormalResearch.SignUncertainty.MiddleBandInner
public import FormalResearch.SignUncertainty.MiddleBandRefOuter

/-!
# GT.2a: assembly of the middle transfer

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `cegt:GT2a`.

Helper facts on the normal-form map `t = Re τ` used by the change of variables `v = w₁(u) = t(εu)/ε`.

Status: proved, conditional on `O4NormalForm L τ`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `t' ≥ 0` on `|θ| < 0.2`. -/
lemma trF_deriv_nonneg {L : ℝ} {τ : ℂ → ℂ} (h : O4NormalForm L τ) (hL0 : 0 < L) (hL2 : L ≤ 0.002) {θ : ℝ}
    (hθ : |θ| < 0.2) : 0 ≤ trF τ 1 θ := by
  have hmono := h.strictMonoOn hL0 hL2
  have hmem : θ ∈ Icc (-0.2 : ℝ) 0.2 := by rw [abs_lt] at hθ; exact ⟨hθ.1.le, hθ.2.le⟩
  have hd : HasDerivAt (trF τ 0) (trF τ 1 θ) θ := trF_hasDerivAt h 0 (by linarith)
  have hint : θ ∈ interior (Icc (-0.2 : ℝ) 0.2) := by rw [interior_Icc]; rw [abs_lt] at hθ; exact hθ
  have hmo : MonotoneOn (trF τ 0) (Icc (-0.2 : ℝ) 0.2) := by
    intro a ha b hb hab
    exact (hmono.monotoneOn (by simpa [trF] using ha) (by simpa [trF] using hb) hab)
  have h1 := hmo.derivWithin_nonneg (x := θ)
  have h2 : derivWithin (trF τ 0) (Icc (-0.2 : ℝ) 0.2) θ = trF τ 1 θ :=
    (hd.hasDerivWithinAt).derivWithin (uniqueDiffOn_Icc (by norm_num) θ hmem)
  rwa [h2] at h1

/-- `τ` is real on the real axis. -/
lemma tau_real_eq {L : ℝ} {τ : ℂ → ℂ} (h : O4NormalForm L τ) {θ : ℝ} (hθ : |θ| < 0.22) :
    τ (θ : ℂ) = ((trF τ 0 θ : ℝ) : ℂ) := by
  have := h.real θ hθ
  have him : (τ (θ : ℂ)).im = 0 := by
    have h2 := congrArg Complex.im this
    simp at h2
    linarith
  apply Complex.ext
  · simp [trF]
  · simp [him]

/-- The phase identity `c Φ(t(θ)) = c α̃ θ - c π² θ³/36` for `|θ| < 0.22`. -/
lemma phase_id {L : ℝ} {τ : ℂ → ℂ} (h : O4NormalForm L τ) (hL0 : 0 < L) (hL2 : L ≤ 0.002) {θ : ℝ} (hθ : |θ| < 0.22) (c : ℝ) :
    c * edgePhi L (trF τ 0 θ) = c * edgeAlphaTilde L * θ - c * (Real.pi ^ 2 / 36) * θ ^ 3 := by
  have hm : (θ : ℂ) ∈ Metric.ball (0 : ℂ) 0.22 := by simpa [Complex.norm_real] using hθ
  have hp := h.phase (θ : ℂ) hm
  rw [tau_real_eq h hθ] at hp
  have hlt : |trF τ 0 θ| < 1 := by
    have := h.norm_lt (θ : ℂ) hm
    rw [tau_real_eq h hθ, Complex.norm_real, Real.norm_eq_abs] at this
    linarith
  rw [edgePhiC_ofReal L hlt] at hp
  unfold o4PhiMod at hp
  have hr : edgePhi L (trF τ 0 θ) = edgeAlphaTilde L * θ - Real.pi ^ 2 / 36 * θ ^ 3 := by
    apply Complex.ofReal_injective
    rw [hp]; push_cast; ring
  rw [hr]; ring

/-- `ε^{-1} * (ε^{5/2} / c²) = ε^{15/2}` when `c ε³ = 1`. -/
lemma eps_rpow_arith {c ε : ℝ} (hε : 0 < ε) (hc : c * ε ^ 3 = 1) :
    ε⁻¹ * (ε ^ (5 / 2 : ℝ) / c ^ 2) = ε ^ (15 / 2 : ℝ) := by
  have hc' : c = (ε ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hc
  have h1 : ε ^ (15 / 2 : ℝ) = ε ^ (5 / 2 : ℝ) * ε ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hε]; norm_num
  rw [h1, hc']
  field_simp

/-- **Main outer piece in the variable `v`.** -/
theorem main_outer_v {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) (AW : ℝ) (hAW : 0 ≤ AW) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L c ε : ℝ} {W W1 W2 W3 : ℝ → ℂ}, 0 < L → L ≤ 0.002 → 2 ≤ c → 0 < ε → ε ≤ 0.16 →
      c * ε ^ 3 = 1 →
      (∀ s, s ≠ 0 → HasDerivAt W (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s) →
      (∀ s, 1 / 2 ≤ |s| → ‖W s‖ ≤ AW * |s| ^ (-(5 / 2 : ℝ)) ∧ ‖W1 s‖ ≤ AW * |s| ^ (-(7 / 2 : ℝ)) ∧
        ‖W2 s‖ ≤ AW * |s| ^ (-(9 / 2 : ℝ)) ∧ ‖W3 s‖ ≤ AW * |s| ^ (-(11 / 2 : ℝ))) →
      ‖∫ v : ℝ, ((1 - ϑ (ε * v / 0.08) : ℝ) : ℂ) * (outerK c (ε * v) *
          Complex.exp (Complex.I * ((c * edgePhi L (ε * v) : ℝ) : ℂ)) * W v)‖ ≤ C * ε ^ (15 / 2 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := main_outer_bound hϑ AW hAW
  refine ⟨C, hC0, ?_⟩
  intro L c ε W W1 W2 W3 hL0 hL2 hc hε hε16 hcε hWd hWb
  have hb := hC hL0 hL2 hc hε hε16 hWd hWb
  set f : ℝ → ℂ := fun τ => (((1 - ϑ (τ / 0.08) : ℝ) : ℂ) * outerK c τ * W (τ / ε)) *
    Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) with hf
  have hpt : ∀ v : ℝ, ((1 - ϑ (ε * v / 0.08) : ℝ) : ℂ) * (outerK c (ε * v) *
          Complex.exp (Complex.I * ((c * edgePhi L (ε * v) : ℝ) : ℂ)) * W v) = f (ε * v) := by
    intro v
    simp only [hf]
    rw [show ε * v / ε = v by field_simp]
    ring
  simp_rw [hpt]
  rw [Measure.integral_comp_mul_left f ε, norm_smul, Real.norm_eq_abs, abs_abs, abs_inv, abs_of_pos hε]
  calc ε⁻¹ * ‖∫ τ, f τ‖ ≤ ε⁻¹ * (C * ε ^ (5 / 2 : ℝ) / c ^ 2) := by gcongr
    _ = C * (ε⁻¹ * (ε ^ (5 / 2 : ℝ) / c ^ 2)) := by ring
    _ = C * ε ^ (15 / 2 : ℝ) := by rw [eps_rpow_arith hε hcε]

/-- `tauCut = ϑ(t(εu)/0.08)` for `ε|u| ≤ 0.19`. -/
lemma tauCut_eq_of_le {ϑ : ℝ → ℝ} {τ : ℂ → ℂ} {ε u : ℝ} (hε : 0 < ε) (h : ε * |u| ≤ 0.19) :
    tauCut ϑ τ ε u = ϑ (trF τ 0 (ε * u) / 0.08) :=
  tauCut_of_lt (by rw [abs_mul, abs_of_pos hε]; linarith)

/-- **Change of variables `v = w₁(u) = t(εu)/ε`** for the inner main piece, for an arbitrary integrand `G`. -/
theorem inner_cov {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) {L : ℝ} {τ : ℂ → ℂ} (h : O4NormalForm L τ) (hL0 : 0 < L)
    (hL2 : L ≤ 0.002) {ε : ℝ} (hε : 0 < ε) (G : ℝ → ℂ) :
    (Integrable (fun v : ℝ => ((ϑ (ε * v / 0.08) : ℝ) : ℂ) * G v) ↔
      Integrable (fun u : ℝ => ((tauCut ϑ τ ε u : ℝ) : ℂ) * ((trF τ 1 (ε * u) : ℝ) : ℂ) * G (trF τ 0 (ε * u) / ε))) ∧
    ∫ v : ℝ, ((ϑ (ε * v / 0.08) : ℝ) : ℂ) * G v =
      ∫ u : ℝ, ((tauCut ϑ τ ε u : ℝ) : ℂ) * ((trF τ 1 (ε * u) : ℝ) : ℂ) * G (trF τ 0 (ε * u) / ε) := by
  obtain ⟨Z1, Z2, -, -, hZ⟩ := tauCut_isCut hϑ
  have hzero := (hZ h hL0 hL2 hε).2.2
  set s : Set ℝ := Icc (-0.19 / ε) (0.19 / ε) with hs
  set f : ℝ → ℝ := fun u => trF τ 0 (ε * u) / ε with hf
  set f' : ℝ → ℝ := fun u => trF τ 1 (ε * u) with hf'
  have hms : MeasurableSet s := measurableSet_Icc
  have hsm : ∀ u ∈ s, |ε * u| ≤ 0.19 := by
    intro u hu
    rw [hs] at hu
    obtain ⟨h1, h2⟩ := hu
    rw [le_div_iff₀ hε] at h2
    rw [div_le_iff₀ hε] at h1
    rw [abs_le]; constructor <;> nlinarith
  have hder : ∀ u ∈ s, HasDerivWithinAt f (f' u) s u := by
    intro u hu
    have hu' := hsm u hu
    have h1 := hasDerivAt_dilate (trF_hasDerivAt h 0 (show |ε * u| < 0.22 by linarith))
    have h2 := h1.div_const ε
    have : (ε • trF τ 1 (ε * u)) / ε = f' u := by
      simp only [hf', smul_eq_mul]; field_simp
    exact (this ▸ h2).hasDerivWithinAt
  have hmono := h.strictMonoOn hL0 hL2
  have hinj : InjOn f s := by
    intro a ha b hb hab
    have ha' := hsm a ha
    have hb' := hsm b hb
    have hab' : trF τ 0 (ε * a) = trF τ 0 (ε * b) := by
      have := hab
      simp only [hf] at this
      field_simp at this
      exact this
    have hmem : ∀ x : ℝ, |ε * x| ≤ 0.19 → ε * x ∈ Icc (-0.2 : ℝ) 0.2 := fun x hx => by
      rw [abs_le] at hx; exact ⟨by linarith, by linarith⟩
    have := hmono.injOn (hmem a ha') (hmem b hb') (by simpa [trF] using hab')
    exact mul_left_cancel₀ hε.ne' this
  -- support of the `v`-integrand lies in the image
  have hA : ∀ v, v ∉ f '' s → ((ϑ (ε * v / 0.08) : ℝ) : ℂ) * G v = 0 := by
    intro v hv
    have : ϑ (ε * v / 0.08) = 0 := by
      by_contra hne
      apply hv
      have hlt : |ε * v| < 0.16 := by
        by_contra hge
        apply hne
        apply hϑ.zero
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 0.08), le_div_iff₀ (by norm_num)]
        linarith [not_lt.1 hge]
      -- intermediate value theorem for `t` on `[-0.19, 0.19]`
      have hcont : ContinuousOn (trF τ 0) (Icc (-0.19 : ℝ) 0.19) := fun x hx =>
        (trF_hasDerivAt h 0 (show |x| < 0.22 by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])).continuousAt.continuousWithinAt
      have hlo : trF τ 0 (-0.19) ≤ -(0.16 : ℝ) := by
        have := (trF_abs_bounds h hL0 hL2 (θ := -0.19) (by norm_num [abs_neg])).1
        have h2 : |trF τ 0 (-0.19)| ≥ 0.989 * 0.19 := by
          rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 0.19)] at this; exact this
        have h3 : trF τ 0 (-0.19) < 0 := by
          have := hmono (a := -0.19) (b := 0) (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)
          simpa [trF, h.zero] using this
        rw [abs_of_neg h3] at h2; linarith
      have hhi : (0.16 : ℝ) ≤ trF τ 0 0.19 := by
        have := (trF_abs_bounds h hL0 hL2 (θ := 0.19) (by norm_num)).1
        have h3 : 0 < trF τ 0 0.19 := by
          have := hmono (a := 0) (b := 0.19) (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)
          simpa [trF, h.zero] using this
        rw [abs_of_pos h3] at this; norm_num at this ⊢; linarith
      have hivt := intermediate_value_Icc (by norm_num : (-0.19 : ℝ) ≤ 0.19) hcont
      have hv' : ε * v ∈ Icc (trF τ 0 (-0.19)) (trF τ 0 0.19) := by
        rw [abs_lt] at hlt; constructor <;> linarith [hlt.1, hlt.2]
      obtain ⟨θ, hθ, hθv⟩ := hivt hv'
      refine ⟨θ / ε, ?_, ?_⟩
      · rw [hs]; constructor
        · rw [div_le_div_iff_of_pos_right hε]; exact hθ.1
        · rw [div_le_div_iff_of_pos_right hε]; exact hθ.2
      · simp only [hf]
        rw [mul_div_cancel₀ _ hε.ne', hθv]
        field_simp
    simp [this]
  -- equality of integrands on `s`
  have hpt : ∀ u ∈ s, |f' u| • (((ϑ (ε * f u / 0.08) : ℝ) : ℂ) * G (f u)) =
      ((tauCut ϑ τ ε u : ℝ) : ℂ) * ((trF τ 1 (ε * u) : ℝ) : ℂ) * G (trF τ 0 (ε * u) / ε) := by
    intro u hu
    have hu' := hsm u hu
    have hnn := trF_deriv_nonneg h hL0 hL2 (θ := ε * u) (by linarith)
    have hu2 : ε * |u| ≤ 0.19 := by rw [← abs_of_pos hε, ← abs_mul]; exact hu'
    rw [tauCut_eq_of_le hε hu2, Complex.real_smul, abs_of_nonneg (by simpa [hf'] using hnn)]
    have : ε * f u = trF τ 0 (ε * u) := by simp only [hf]; field_simp
    rw [this]
    simp only [hf']
    ring
  have hzs : ∀ u, u ∉ s → ((tauCut ϑ τ ε u : ℝ) : ℂ) * ((trF τ 1 (ε * u) : ℝ) : ℂ) * G (trF τ 0 (ε * u) / ε) = 0 := by
    intro u hu
    have : tauCut ϑ τ ε u = 0 := by
      apply hzero
      by_contra hlt
      apply hu
      rw [not_le] at hlt
      have hεu : |ε * u| < 0.18 := by rw [abs_mul, abs_of_pos hε]; exact hlt
      obtain ⟨ha, hb⟩ := abs_lt.mp hεu
      rw [hs]; constructor
      · rw [div_le_iff₀ hε]; nlinarith
      · rw [le_div_iff₀ hε]; nlinarith
    simp [this]
  have hcov := integral_image_eq_integral_abs_deriv_smul hms hder hinj (fun v : ℝ => ((ϑ (ε * v / 0.08) : ℝ) : ℂ) * G v)
  have hicov := integrableOn_image_iff_integrableOn_abs_deriv_smul hms hder hinj (fun v : ℝ => ((ϑ (ε * v / 0.08) : ℝ) : ℂ) * G v)
  constructor
  · have e1 : Integrable (fun v : ℝ => ((ϑ (ε * v / 0.08) : ℝ) : ℂ) * G v) ↔
        IntegrableOn (fun v : ℝ => ((ϑ (ε * v / 0.08) : ℝ) : ℂ) * G v) (f '' s) :=
      (integrableOn_iff_integrable_of_support_subset (fun v hv => by
        by_contra hn; exact hv (hA v hn))).symm
    have e2 : Integrable (fun u : ℝ => ((tauCut ϑ τ ε u : ℝ) : ℂ) * ((trF τ 1 (ε * u) : ℝ) : ℂ) * G (trF τ 0 (ε * u) / ε)) ↔
        IntegrableOn (fun u : ℝ => ((tauCut ϑ τ ε u : ℝ) : ℂ) * ((trF τ 1 (ε * u) : ℝ) : ℂ) * G (trF τ 0 (ε * u) / ε)) s :=
      (integrableOn_iff_integrable_of_support_subset (fun u hu => by
        by_contra hn; exact hu (hzs u hn))).symm
    rw [e1, e2, hicov]
    exact integrableOn_congr_fun (fun u hu => hpt u hu) hms
  · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hA, hcov,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero hzs]
    exact setIntegral_congr_fun hms (fun u hu => hpt u hu)

/-- Continuity and integrability of a symbol with the `GT.1` bounds. -/
lemma symbol_cont_int {AW : ℝ} (hAW : 1 ≤ AW) {W W1 W2 W3 : ℝ → ℂ}
    (hWd : ∀ s, s ≠ 0 → HasDerivAt W (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s)
    (hWb : ∀ s, 1 / 2 ≤ |s| → ‖W s‖ ≤ AW * |s| ^ (-(5 / 2 : ℝ)))
    (hW0 : ‖W 0‖ ≤ AW)
    (hSm : ∀ s : ℝ, 0 < |s| → |s| ≤ 9 → ‖W s - W 0‖ ≤ AW * |s| ^ (1 / 2 : ℝ)) :
    Continuous W ∧ Integrable W := by
  have hcont : Continuous W := by
    rw [continuous_iff_continuousAt]
    intro s
    by_cases hs : s = 0
    · subst hs
      rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
      have hb : Tendsto (fun x : ℝ => AW * |x| ^ (1 / 2 : ℝ)) (𝓝 0) (𝓝 0) := by
        have : Continuous (fun x : ℝ => AW * |x| ^ (1 / 2 : ℝ)) :=
          continuous_const.mul ((Real.continuous_rpow_const (by norm_num)).comp continuous_abs)
        have h0 := this.tendsto 0
        simpa using h0
      refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ hb
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds (by simp : |(0 : ℝ)| < 9)] with x hx
      by_cases hx0 : x = 0
      · subst hx0; simp
      · exact hSm x (abs_pos.mpr hx0) (le_of_lt hx)
    · exact (hWd s hs).1.continuousAt
  refine ⟨hcont, ?_⟩
  set M : ℝ := (3 : ℝ) ^ (5 / 2 : ℝ) with hM
  have hM0 : 0 < M := by positivity
  have hM3 : M * (3 : ℝ) ^ (-(5 / 2 : ℝ)) = 1 := by
    rw [hM, ← Real.rpow_add (by norm_num)]; norm_num
  have hdom : Integrable (fun x : ℝ => (2 * AW * M) * (1 + ‖x‖) ^ (-(5 / 2 : ℝ))) :=
    (integrable_one_add_norm (E := ℝ) (r := 5 / 2) (by simp; norm_num)).const_mul _
  refine hdom.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  have hq : 0 < (1 + ‖u‖) ^ (-(5 / 2 : ℝ)) := by positivity
  rw [Real.norm_eq_abs] at hq ⊢
  by_cases hu : 1 / 2 ≤ |u|
  · have hu0 : 0 < |u| := by linarith
    have h1 : (3 : ℝ) ^ (-(5 / 2 : ℝ)) * |u| ^ (-(5 / 2 : ℝ)) ≤ (1 + |u|) ^ (-(5 / 2 : ℝ)) := by
      rw [← Real.mul_rpow (by norm_num) hu0.le]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
    have h2 : |u| ^ (-(5 / 2 : ℝ)) ≤ M * (1 + |u|) ^ (-(5 / 2 : ℝ)) := by
      have := mul_le_mul_of_nonneg_left h1 hM0.le
      rw [← mul_assoc, hM3, one_mul] at this
      exact this
    calc ‖W u‖ ≤ AW * |u| ^ (-(5 / 2 : ℝ)) := hWb u hu
      _ ≤ AW * (M * (1 + |u|) ^ (-(5 / 2 : ℝ))) := by gcongr
      _ ≤ 2 * AW * M * (1 + |u|) ^ (-(5 / 2 : ℝ)) := by nlinarith [mul_pos hM0 hq]
  · rw [not_le] at hu
    have hW : ‖W u‖ ≤ 2 * AW := by
      by_cases hu0 : u = 0
      · subst hu0; linarith
      · have := hSm u (abs_pos.mpr hu0) (by linarith)
        have h1 : |u| ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one (abs_nonneg _) (by linarith) (by norm_num)
        have h2 : ‖W u‖ ≤ ‖W 0‖ + ‖W u - W 0‖ := norm_le_insert' _ _
        nlinarith
    have h1 : (3 : ℝ) ^ (-(5 / 2 : ℝ)) ≤ (1 + |u|) ^ (-(5 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
    have h2 : 1 ≤ M * (1 + |u|) ^ (-(5 / 2 : ℝ)) := by
      have := mul_le_mul_of_nonneg_left h1 hM0.le
      rw [hM3] at this; exact this
    calc ‖W u‖ ≤ 2 * AW := hW
      _ ≤ 2 * AW * (M * (1 + |u|) ^ (-(5 / 2 : ℝ))) := by nlinarith
      _ = _ := by ring

/-- Parameter bookkeeping: with `c ε³ = 1`, `L = π² ε² S`, `S ≥ 100`, `0 < L ≤ 0.002` and `a₀ = c ε α̃(L)`:
`a₀ = κ₀ π² S`, `u₀² = 12 κ₀ S` etc. -/
lemma param_facts {L c ε S : ℝ} (hL0 : 0 < L) (hL2 : L ≤ 0.002) (hε : 0 < ε) (hcε : c * ε ^ 3 = 1)
    (hS : L = Real.pi ^ 2 * ε ^ 2 * S) (hS100 : 100 ≤ S) :
    c * ε * edgeAlphaTilde L = edgeKappa0 L * Real.pi ^ 2 * S ∧ 1 < edgeKappa0 L ∧ edgeKappa0 L ≤ 1 + L / 4 ∧
    ε ^ 2 ≤ L ∧ ε ≤ 0.0015 ∧ 1 / c ≤ L := by
  obtain ⟨hk1, hk2⟩ := edgeKappa0_bounds hL0 hL2
  have hπ : (9.8 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_d2]
  have hε2 : 0 < ε ^ 2 := by positivity
  have hα : edgeAlphaTilde L = edgeKappa0 L * L := by
    unfold edgeKappa0; field_simp
  have hcε2 : c * ε = (ε ^ 2)⁻¹ := by
    field_simp; nlinarith [hcε]
  have h1 : c * ε * edgeAlphaTilde L = edgeKappa0 L * Real.pi ^ 2 * S := by
    rw [hα, hcε2, hS]; field_simp
  have hε2L : ε ^ 2 ≤ L := by
    rw [hS]; nlinarith [mul_pos hε2 (by linarith : (0 : ℝ) < S)]
  have hε15 : ε ≤ 0.0015 := by
    have : ε ^ 2 * (9.8 * 100) ≤ 0.002 := by
      calc ε ^ 2 * (9.8 * 100) ≤ ε ^ 2 * (Real.pi ^ 2 * S) := by gcongr
        _ = L := by rw [hS]; ring
        _ ≤ 0.002 := hL2
    nlinarith [sq_nonneg (ε - 0.0015)]
  have hcinv : 1 / c = ε ^ 3 := by
    rw [eq_inv_of_mul_eq_one_left hcε]; simp
  refine ⟨h1, hk1, hk2, hε2L, hε15, ?_⟩
  rw [hcinv, hS]
  have : ε ^ 3 ≤ ε ^ 2 * 1 := by nlinarith
  nlinarith [mul_pos hε2 (by linarith : (0 : ℝ) < S)]

lemma rpow_three_halves_le {S u0 : ℝ} (hS : 0 < S) (hu : 0 < u0) (h : S ≤ u0 ^ 2) : S ^ (3 / 2 : ℝ) ≤ u0 ^ 3 := by
  have h1 : (S ^ (3 / 2 : ℝ)) ^ 2 = S ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hS.le]; norm_num
  have h2 : S ^ 3 ≤ (u0 ^ 3) ^ 2 := by
    calc S ^ 3 ≤ (u0 ^ 2) ^ 3 := by gcongr
      _ = (u0 ^ 3) ^ 2 := by ring
  by_contra hcon
  rw [not_le] at hcon
  have : (u0 ^ 3) ^ 2 < (S ^ (3 / 2 : ℝ)) ^ 2 := by
    have : 0 ≤ u0 ^ 3 := by positivity
    nlinarith
  linarith

set_option maxHeartbeats 1600000 in
/-- **The inner difference integral** for the middle transfer. -/
theorem inner_osc_bound {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) (AW : ℝ) (hAW : 1 ≤ AW) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L c ε S : ℝ} {τ : ℂ → ℂ} {W W1 W2 W3 : ℝ → ℂ}, O4NormalForm L τ → 0 < L → L ≤ 0.002 →
      2 ≤ c → 0 < ε → c * ε ^ 3 = 1 → L = Real.pi ^ 2 * ε ^ 2 * S → 100 ≤ S →
      (∀ s, s ≠ 0 → HasDerivAt W (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s) →
      (∀ s, 1 / 2 ≤ |s| → ‖W s‖ ≤ AW * |s| ^ (-(5 / 2 : ℝ)) ∧ ‖W1 s‖ ≤ AW * |s| ^ (-(7 / 2 : ℝ)) ∧
        ‖W2 s‖ ≤ AW * |s| ^ (-(9 / 2 : ℝ)) ∧ ‖W3 s‖ ≤ AW * |s| ^ (-(11 / 2 : ℝ))) →
      ‖W 0‖ ≤ AW →
      (∀ s : ℝ, 0 < |s| → |s| ≤ 9 → ‖W s - W 0‖ ≤ AW * |s| ^ (1 / 2 : ℝ) ∧ ‖W1 s‖ ≤ AW * |s| ^ (-(1 / 2) : ℝ) ∧
        ‖W2 s‖ ≤ AW * |s| ^ (-(3 / 2) : ℝ) ∧ ‖W3 s‖ ≤ AW * |s| ^ (-(5 / 2) : ℝ)) →
      ‖oscInt (c * ε * edgeAlphaTilde L) (fun u => ((tauCut ϑ τ ε u : ℝ) : ℂ) * innerDiff c ε τ W u)‖ ≤
        C * (S ^ (-(3 / 2 : ℝ)) * L) := by
  obtain ⟨Z1, Z2, hZ1, hZ2, hZ⟩ := tauCut_isCut hϑ
  obtain ⟨C3, hC3, hI⟩ := inner_integral_bound hϑ (Z0 := 1) zero_le_one hZ1 hZ2
  obtain ⟨CL, hCL, hLarge⟩ := innerDiff_largeZone AW hAW
  obtain ⟨Cs, hCs, hSmall⟩ := innerDiff_small AW hAW
  refine ⟨C3 * (3 * CL + 2 * Cs), by positivity, ?_⟩
  intro L c ε S τ W W1 W2 W3 h hL0 hL2 hc hε hcε hS hS100 hWd hWb hW0 hSm
  obtain ⟨hpf1, hk1, hk2, hε2L, hε15, hcL⟩ := param_facts hL0 hL2 hε hcε hS hS100
  have hπ : (9.8 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_d2]
  have hπ' : Real.pi ^ 2 ≤ 9.93 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hSpos : 0 < S := by linarith
  set κ : ℝ := edgeKappa0 L with hκ
  set u0 : ℝ := Real.sqrt (12 * κ * S) with hu0
  have hu0sq : u0 ^ 2 = 12 * κ * S := Real.sq_sqrt (by positivity)
  have hu0pos : 0 < u0 := Real.sqrt_pos.mpr (by positivity)
  have hu34 : 34 ≤ u0 := by
    by_contra hcon; rw [not_le] at hcon
    nlinarith
  have hεu2 : ε ^ 2 * u0 ^ 2 = 12 * κ * L / Real.pi ^ 2 := by
    rw [hu0sq]; rw [hS]; field_simp
  have hεu : ε * u0 ≤ 0.05 := by
    by_contra hcon; rw [not_le] at hcon
    have h1 : (0.05 : ℝ) ^ 2 < (ε * u0) ^ 2 := by gcongr
    have h2 : (ε * u0) ^ 2 = 12 * κ * L / Real.pi ^ 2 := by rw [mul_pow]; exact hεu2
    rw [h2, lt_div_iff₀ (by positivity)] at h1
    nlinarith
  have hLle : L ≤ ε ^ 2 * u0 ^ 2 := by
    rw [hεu2, le_div_iff₀ (by positivity)]
    nlinarith
  have hεu2L : ε ^ 2 * u0 ^ 2 ≤ 2 * L := by
    rw [hεu2, div_le_iff₀ (by positivity)]
    nlinarith
  have hε5 : ε ≤ 0.05 := by linarith
  have hpa : Real.pi ^ 2 * u0 ^ 2 / 12 = c * ε * edgeAlphaTilde L := by
    rw [hpf1, hu0sq]; ring
  obtain ⟨hζ, hζ1, hζ0⟩ := hZ h hL0 hL2 hε
  obtain ⟨hlz⟩ := (⟨hLarge h hL0 hL2 hc hε hcL hWd hWb⟩ : Nonempty _)
  obtain ⟨hsm0, hsm⟩ := hSmall h hL0 hL2 hc hε hε5 hcL hWd hW0 hSm
  have hCsL : 0 ≤ Cs * (L + ε ^ 2) := by positivity
  have key := hI (ζ := tauCut ϑ τ ε) (u0 := u0) (ε := ε) (L := L) (G := CL) (G0 := Cs * (L + ε ^ 2))
    (g := innerDiff c ε τ W) (g0 := innerDiff c ε τ W 0) hζ hζ1 hζ0 hu34 hε hL0.le hCL hCsL hεu hLle hlz rfl hsm0
    (fun u hu0' hu3 => innerDiff_contDiffAt h hL0 hL2 hc hε hWd (abs_pos.mp hu0') (by
      rw [abs_mul, abs_of_pos hε]; nlinarith [abs_nonneg u]))
    (fun u hu0' hu3 => (hsm u hu0' hu3).1) (fun u hu0' hu3 => (hsm u hu0' hu3).2.1)
    (fun u hu0' hu3 => (hsm u hu0' hu3).2.2)
  rw [hpa] at key
  refine key.trans ?_
  have hinv : 1 / u0 ^ 3 ≤ S ^ (-(3 / 2 : ℝ)) := by
    have h1 : S ^ (3 / 2 : ℝ) ≤ u0 ^ 3 :=
      rpow_three_halves_le hSpos hu0pos (by rw [hu0sq]; nlinarith [mul_pos (by linarith : 0 < κ - 1) hSpos])
    rw [Real.rpow_neg hSpos.le, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) h1
  have hA : CL * (L + ε ^ 2 * u0 ^ 2) + Cs * (L + ε ^ 2) ≤ (3 * CL + 2 * Cs) * L := by
    nlinarith [mul_nonneg hCL (by linarith : 0 ≤ 3 * L - (L + ε ^ 2 * u0 ^ 2)),
      mul_nonneg hCs (by linarith : 0 ≤ 2 * L - (L + ε ^ 2))]
  calc C3 * (CL * (L + ε ^ 2 * u0 ^ 2) + Cs * (L + ε ^ 2)) * (1 / u0 ^ 3)
      ≤ C3 * ((3 * CL + 2 * Cs) * L) * S ^ (-(3 / 2 : ℝ)) := by gcongr
    _ = C3 * (3 * CL + 2 * Cs) * (S ^ (-(3 / 2 : ℝ)) * L) := by ring

set_option maxHeartbeats 3200000 in
/-- **GT.2a, abstract middle transfer.**  For a symbol `W` with the `GT.1` bounds and the edge phase of `O.4`
(`c ε³ = 1`, `L = π² ε² S`, `S ≥ 100`, `0 < L ≤ 0.002`):
`|∫ k_c(εv) e^{icΦ(εv;L)} W(v) dv - ∫ W(u) e^{i((a₀ + ε/2)u - π²u³/36)} du| ≤ C (S^{-3/2} L + ε^{15/2})`, `a₀ = c ε α̃(L) = κ₀ π² S`. -/
theorem middle_transfer_abstract {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) (AW : ℝ) (hAW : 1 ≤ AW) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L c ε S : ℝ} {τ : ℂ → ℂ} {W W1 W2 W3 : ℝ → ℂ}, O4NormalForm L τ → 0 < L → L ≤ 0.002 →
      2 ≤ c → 0 < ε → c * ε ^ 3 = 1 → L = Real.pi ^ 2 * ε ^ 2 * S → 100 ≤ S →
      (∀ s, s ≠ 0 → HasDerivAt W (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s) →
      (∀ s, 1 / 2 ≤ |s| → ‖W s‖ ≤ AW * |s| ^ (-(5 / 2 : ℝ)) ∧ ‖W1 s‖ ≤ AW * |s| ^ (-(7 / 2 : ℝ)) ∧
        ‖W2 s‖ ≤ AW * |s| ^ (-(9 / 2 : ℝ)) ∧ ‖W3 s‖ ≤ AW * |s| ^ (-(11 / 2 : ℝ))) →
      ‖W 0‖ ≤ AW →
      (∀ s : ℝ, 0 < |s| → |s| ≤ 9 → ‖W s - W 0‖ ≤ AW * |s| ^ (1 / 2 : ℝ) ∧ ‖W1 s‖ ≤ AW * |s| ^ (-(1 / 2) : ℝ) ∧
        ‖W2 s‖ ≤ AW * |s| ^ (-(3 / 2) : ℝ) ∧ ‖W3 s‖ ≤ AW * |s| ^ (-(5 / 2) : ℝ)) →
      Integrable (fun v : ℝ => outerK c (ε * v) * Complex.exp (Complex.I * ((c * edgePhi L (ε * v) : ℝ) : ℂ)) * W v) →
      ‖(∫ v : ℝ, outerK c (ε * v) * Complex.exp (Complex.I * ((c * edgePhi L (ε * v) : ℝ) : ℂ)) * W v) -
        ∫ u : ℝ, W u * Complex.exp (Complex.I * (((c * ε * edgeAlphaTilde L + ε / 2) * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ))‖ ≤
        C * (S ^ (-(3 / 2 : ℝ)) * L + ε ^ (15 / 2 : ℝ)) := by
  obtain ⟨Co, hCo, hO⟩ := main_outer_v hϑ AW (by linarith)
  obtain ⟨Cr, hCr, hR⟩ := ref_outer_bound hϑ AW (by linarith)
  obtain ⟨Ci, hCi, hIn⟩ := inner_osc_bound hϑ AW hAW
  obtain ⟨Z1, Z2, hZ1, hZ2, hZ⟩ := tauCut_isCut hϑ
  refine ⟨max (Co + Cr) Ci, le_max_of_le_left (by positivity), ?_⟩
  intro L c ε S τ W W1 W2 W3 h hL0 hL2 hc hε hcε hS hS100 hWd hWb hW0 hSm hGint
  obtain ⟨hpf1, hk1, hk2, hε2L, hε15, hcL⟩ := param_facts hL0 hL2 hε hcε hS hS100
  obtain ⟨hWc, hWi⟩ := symbol_cont_int hAW hWd (fun s hs => (hWb s hs).1) hW0 (fun s h1 h2 => (hSm s h1 h2).1)
  obtain ⟨hζ, hζ1, hζ0⟩ := hZ h hL0 hL2 hε
  set a0 : ℝ := c * ε * edgeAlphaTilde L with ha0
  set ζ : ℝ → ℝ := tauCut ϑ τ ε with hζdef
  set E : ℝ → ℂ := fun u => Complex.exp (Complex.I * ((a0 * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ)) with hE
  set e2 : ℝ → ℂ := fun u => Complex.exp (Complex.I * ((ε * u : ℝ) : ℂ) / 2) with he2
  set G : ℝ → ℂ := fun v => outerK c (ε * v) * Complex.exp (Complex.I * ((c * edgePhi L (ε * v) : ℝ) : ℂ)) * W v with hG
  have hEc : Continuous E := by rw [hE]; fun_prop
  have hEn : ∀ u, ‖E u‖ = 1 := fun u => by
    rw [hE]; simp only []
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  have he2c : Continuous e2 := by rw [he2]; fun_prop
  have he2n : ∀ u, ‖e2 u‖ = 1 := fun u => by
    rw [he2]; simp only []
    have : Complex.I * ((ε * u : ℝ) : ℂ) / 2 = ((ε * u / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this]; exact Complex.norm_exp_ofReal_mul_I _
  have hζc : Continuous ζ := hζ.contDiff.continuous
  have hζn : ∀ u, ‖((ζ u : ℝ) : ℂ)‖ ≤ 1 := fun u => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hζ.bound0 u
  -- the products with `W`
  have hbdd : ∀ B : ℝ → ℂ, Continuous B → (∀ u, ‖B u‖ ≤ 1) → Integrable (fun u => B u * W u) :=
    fun B hB hB1 => hWi.bdd_mul hB.aestronglyMeasurable (Eventually.of_forall hB1)
  have hT2int : Integrable (fun u => ((ζ u : ℝ) : ℂ) * (e2 u * W u) * E u) := by
    have := hbdd (fun u => ((ζ u : ℝ) : ℂ) * e2 u * E u) (by fun_prop) (fun u => by
      rw [norm_mul, norm_mul, he2n, hEn]; simpa using hζn u)
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only []; ring
  have hE2 : ∀ u, e2 u * E u = Complex.exp (Complex.I * (((a0 + ε / 2) * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ)) := by
    intro u
    rw [he2, hE]; simp only []
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  -- the reference integral splits
  have hRint : Integrable (fun u => W u * Complex.exp (Complex.I * (((a0 + ε / 2) * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ))) := by
    have := hbdd (fun u => Complex.exp (Complex.I * (((a0 + ε / 2) * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ))) (by fun_prop) (fun u => by
      rw [mul_comm, Complex.norm_exp_ofReal_mul_I])
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only []; ring
  set T3 : ℝ → ℂ := fun u => (((1 - ζ u : ℝ) : ℂ) * W u) *
    Complex.exp (Complex.I * (((a0 + ε / 2) * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ)) with hT3
  have hRsplit : ∀ u, W u * Complex.exp (Complex.I * (((a0 + ε / 2) * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ)) =
      ((ζ u : ℝ) : ℂ) * (e2 u * W u) * E u + T3 u := by
    intro u
    rw [hT3]; simp only []
    rw [← hE2 u]; push_cast; ring
  have hT3int : Integrable T3 := by
    have : T3 = fun u => W u * Complex.exp (Complex.I * (((a0 + ε / 2) * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ)) -
        ((ζ u : ℝ) : ℂ) * (e2 u * W u) * E u := by
      funext u; rw [hRsplit u]; ring
    rw [this]; exact hRint.sub hT2int
  have hRint_eq : (∫ u : ℝ, W u * Complex.exp (Complex.I * (((a0 + ε / 2) * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ))) =
      (∫ u, ((ζ u : ℝ) : ℂ) * (e2 u * W u) * E u) + ∫ u, T3 u := by
    rw [← integral_add hT2int hT3int]
    exact integral_congr_ae (Eventually.of_forall fun u => hRsplit u)
  -- the main integral splits (outer / inner)
  have hϑc : Continuous fun v : ℝ => ((ϑ (ε * v / 0.08) : ℝ) : ℂ) := by
    have := hϑ.contDiff.continuous
    fun_prop
  have hϑn : ∀ v : ℝ, ‖((ϑ (ε * v / 0.08) : ℝ) : ℂ)‖ ≤ 1 := fun v => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hϑ.range _).1]; exact (hϑ.range _).2
  have h1ϑc : Continuous fun v : ℝ => ((1 - ϑ (ε * v / 0.08) : ℝ) : ℂ) := by
    have := hϑ.contDiff.continuous
    fun_prop
  have h1ϑn : ∀ v : ℝ, ‖((1 - ϑ (ε * v / 0.08) : ℝ) : ℂ)‖ ≤ 1 := fun v => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [(hϑ.range (ε * v / 0.08)).2])]
    linarith [(hϑ.range (ε * v / 0.08)).1]
  have hOint : Integrable (fun v : ℝ => ((1 - ϑ (ε * v / 0.08) : ℝ) : ℂ) * G v) :=
    hGint.bdd_mul h1ϑc.aestronglyMeasurable (Eventually.of_forall h1ϑn)
  have hIint : Integrable (fun v : ℝ => ((ϑ (ε * v / 0.08) : ℝ) : ℂ) * G v) :=
    hGint.bdd_mul hϑc.aestronglyMeasurable (Eventually.of_forall hϑn)
  have hGsplit : (∫ v, G v) = (∫ v, ((1 - ϑ (ε * v / 0.08) : ℝ) : ℂ) * G v) + ∫ v, ((ϑ (ε * v / 0.08) : ℝ) : ℂ) * G v := by
    rw [← integral_add hOint hIint]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only []; push_cast; ring
  obtain ⟨hcovI, hcov⟩ := inner_cov hϑ h hL0 hL2 hε G
  -- pointwise identity in the variable `u`
  have hpt : ∀ u : ℝ, ((ζ u : ℝ) : ℂ) * ((trF τ 1 (ε * u) : ℝ) : ℂ) * G (trF τ 0 (ε * u) / ε) =
      ((ζ u : ℝ) : ℂ) * innerDiff c ε τ W u * E u + ((ζ u : ℝ) : ℂ) * (e2 u * W u) * E u := by
    intro u
    by_cases hu : ε * |u| < 0.18
    · have hθ : |ε * u| < 0.22 := by rw [abs_mul, abs_of_pos hε]; linarith
      have hph := phase_id h hL0 hL2 hθ c
      have hcube : c * (Real.pi ^ 2 / 36) * (ε * u) ^ 3 = Real.pi ^ 2 / 36 * u ^ 3 := by
        have : c * (ε * u) ^ 3 = u ^ 3 := by
          calc c * (ε * u) ^ 3 = (c * ε ^ 3) * u ^ 3 := by ring
            _ = u ^ 3 := by rw [hcε, one_mul]
        calc c * (Real.pi ^ 2 / 36) * (ε * u) ^ 3 = Real.pi ^ 2 / 36 * (c * (ε * u) ^ 3) := by ring
          _ = _ := by rw [this]
      have hphase : c * edgePhi L (trF τ 0 (ε * u)) = a0 * u - Real.pi ^ 2 / 36 * u ^ 3 := by
        rw [hph, ← hcube, ha0]; ring
      have hεw : ε * (trF τ 0 (ε * u) / ε) = trF τ 0 (ε * u) := mul_div_cancel₀ _ hε.ne'
      simp only [hG, hεw, hphase, innerDiff, hE, he2]
      ring
    · have : ζ u = 0 := hζ0 u (not_lt.1 hu)
      simp [this]
  have hinnerEq : (∫ v, ((ϑ (ε * v / 0.08) : ℝ) : ℂ) * G v) =
      (∫ u, ((ζ u : ℝ) : ℂ) * innerDiff c ε τ W u * E u) + ∫ u, ((ζ u : ℝ) : ℂ) * (e2 u * W u) * E u := by
    rw [hcov]
    have hsumint : Integrable (fun u => ((ζ u : ℝ) : ℂ) * innerDiff c ε τ W u * E u +
        ((ζ u : ℝ) : ℂ) * (e2 u * W u) * E u) := by
      have := hcovI.1 hIint
      refine this.congr (Eventually.of_forall fun u => ?_)
      exact hpt u
    have hT1int : Integrable (fun u => ((ζ u : ℝ) : ℂ) * innerDiff c ε τ W u * E u) := by
      have := hsumint.sub hT2int
      refine this.congr (Eventually.of_forall fun u => ?_)
      simp only [Pi.sub_apply]; ring
    rw [← integral_add hT1int hT2int]
    exact integral_congr_ae (Eventually.of_forall fun u => hpt u)
  -- the three bounds
  have hb1 := hO hL0 hL2 hc hε (by linarith) hcε hWd (fun s hs => hWb s hs)
  have hb2 := hIn h hL0 hL2 hc hε hcε hS hS100 hWd hWb hW0 hSm
  have hb3 := hR h hL0 hL2 hε (by linarith) (by
    have hae : (a0 + ε / 2) * ε ^ 2 = edgeKappa0 L * L + ε ^ 3 / 2 := by
      have h1 : a0 * ε ^ 2 = edgeAlphaTilde L := by
        rw [ha0]
        calc c * ε * edgeAlphaTilde L * ε ^ 2 = (c * ε ^ 3) * edgeAlphaTilde L := by ring
          _ = _ := by rw [hcε, one_mul]
      have h2 : edgeAlphaTilde L = edgeKappa0 L * L := by unfold edgeKappa0; field_simp
      rw [add_mul, h1, h2]; ring
    rw [hae]
    have : ε ^ 3 ≤ 0.0015 ^ 3 := by gcongr
    nlinarith) hWd (fun s hs => ⟨(hWb s hs).1, (hWb s hs).2.1, (hWb s hs).2.2.1⟩)
  have hfinal : (∫ v, G v) - ∫ u, W u * Complex.exp (Complex.I * (((a0 + ε / 2) * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ)) =
      (∫ v, ((1 - ϑ (ε * v / 0.08) : ℝ) : ℂ) * G v) + oscInt a0 (fun u => ((ζ u : ℝ) : ℂ) * innerDiff c ε τ W u) -
        ∫ u, T3 u := by
    rw [hGsplit, hinnerEq, hRint_eq]
    unfold oscInt
    ring
  rw [hfinal]
  have hEpos : 0 ≤ ε ^ (15 / 2 : ℝ) := by positivity
  have hX : 0 ≤ S ^ (-(3 / 2 : ℝ)) * L := by have : 0 < S := by linarith
                                             positivity
  calc ‖(∫ v, ((1 - ϑ (ε * v / 0.08) : ℝ) : ℂ) * G v) + oscInt a0 (fun u => ((ζ u : ℝ) : ℂ) * innerDiff c ε τ W u) - ∫ u, T3 u‖
      ≤ ‖∫ v, ((1 - ϑ (ε * v / 0.08) : ℝ) : ℂ) * G v‖ + ‖oscInt a0 (fun u => ((ζ u : ℝ) : ℂ) * innerDiff c ε τ W u)‖ +
        ‖∫ u, T3 u‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ Co * ε ^ (15 / 2 : ℝ) + Ci * (S ^ (-(3 / 2 : ℝ)) * L) + Cr * ε ^ (15 / 2 : ℝ) := by
        gcongr
    _ ≤ max (Co + Cr) Ci * (S ^ (-(3 / 2 : ℝ)) * L + ε ^ (15 / 2 : ℝ)) := by
        have h1 : Co + Cr ≤ max (Co + Cr) Ci := le_max_left _ _
        have h2 : Ci ≤ max (Co + Cr) Ci := le_max_right _ _
        nlinarith [mul_le_mul_of_nonneg_right h1 hEpos, mul_le_mul_of_nonneg_right h2 hX]

/-- info: 'FormalResearch.SignUncertainty.trF_deriv_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trF_deriv_nonneg

/-- info: 'FormalResearch.SignUncertainty.phase_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms phase_id

/-- info: 'FormalResearch.SignUncertainty.main_outer_v' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms main_outer_v

/-- info: 'FormalResearch.SignUncertainty.inner_cov' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inner_cov

/-- info: 'FormalResearch.SignUncertainty.symbol_cont_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms symbol_cont_int

/-- info: 'FormalResearch.SignUncertainty.param_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms param_facts

/-- info: 'FormalResearch.SignUncertainty.inner_osc_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inner_osc_bound

/-- info: 'FormalResearch.SignUncertainty.middle_transfer_abstract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms middle_transfer_abstract

end FormalResearch.SignUncertainty
