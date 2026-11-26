module

public import FormalResearch.SignUncertainty.CtSdAssemble
public import FormalResearch.SignUncertainty.CtChartPsi
public import FormalResearch.SignUncertainty.CtChartBounds
public import FormalResearch.SignUncertainty.CtOuterBandFinal

/-!
# The chart on a polydisc and at real parameters (`ct:cfu` Step 3, concrete data)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 2/3.  **Proved.**
All chart facts of `CtChart*` (germs at `(0,0)`) hold on one polydisc `‖s‖, ‖β‖ < ρ`; for real `(s,β)` the chart `T(s;β)`
and its derivative are real.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real

namespace FormalResearch.SignUncertainty.CtSd

open FormalResearch.SignUncertainty.CtChart

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- All chart facts on the polydisc `‖s‖, ‖β‖ < ρ`. -/
def ChartReg (ε : ℝ) (ϑ : ℂ → ℂ) (ρ : ℝ) : Prop :=
  ∀ s β : ℂ, ‖s‖ < ρ → ‖β‖ < ρ →
      PhiC (Tf (s, β)) β = -(aC β * s + s ^ 3 / 3) ∧
      HasDerivAt (fun s' : ℂ => Tf (s', β)) (Tsd (s ^ 2, β)) s ∧
      Tf (conj2 (s, β)) = starRingEnd ℂ (Tf (s, β)) ∧
      muf (s ^ 2, β) * Complex.exp (Complex.I * Xph ϑ (s, β)) = 1 + (s ^ 2 - ysF β) * Qeps ϑ (s, β) ∧
      thOdd ε (Tf (s, β)) - s * psiHat ϑ β = s * (s ^ 2 - ysF β) * htil ϑ (s ^ 2, β) ∧
      Tf (s, β) ^ 2 = Zf (s ^ 2, β) ∧
      DifferentiableAt ℂ (Qeps ϑ) (s, β) ∧ ContinuousAt (dyF (Qeps ϑ)) (s, β) ∧
      1 / (2 * CtCfu.d0) ≤ (Tsd (s ^ 2, β)).re ∧ ‖Tsd (s ^ 2, β)‖ ≤ 2 / CtCfu.d0

/-- All chart facts on one polydisc. -/
theorem chart_region {ε : ℝ} {ϑ : ℂ → ℂ} (hA : AnalyticAt ℂ ϑ 0)
    (hϑ : ∀ᶠ τ in 𝓝 (0 : ℂ), thOdd ε τ = τ * ϑ (τ ^ 2)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ChartReg ε ϑ ρ := by
  have h1 := chart_identity
  have h2 := hasDerivAt_Tf
  have h3 := Tf_conj
  have h4 := amp_decomp ϑ
  have h5 := theta_T_decomp hA hϑ
  have h6 := Tf_sq
  have h7 := ev_diff (contDiffAt_Qeps hA)
  have h8 : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), ContinuousAt (dyF (Qeps ϑ)) p :=
    (ev_cd1 (contDiffAt_dyF (contDiffAt_Qeps hA))).mono fun y hy => hy.continuousAt
  have hc0 : Tsd ((0 : ℂ) ^ 2, (0 : ℂ)) = ((1 / CtCfu.d0 : ℝ) : ℂ) := by
    have := Tsd_zero
    simpa using this
  have hcn : ContinuousAt (fun p : ℂ × ℂ => Tsd (p.1 ^ 2, p.2)) (0, 0) :=
    (contDiffAt_comp_sq contDiffAt_Tsd).continuousAt
  have h9 : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), 1 / (2 * CtCfu.d0) ≤ (Tsd (p.1 ^ 2, p.2)).re := by
    have hc : ContinuousAt (fun p : ℂ × ℂ => (Tsd (p.1 ^ 2, p.2)).re) (0, 0) :=
      Complex.continuous_re.continuousAt.comp hcn
    have h0 : (Tsd ((0 : ℂ) ^ 2, (0 : ℂ))).re = 1 / CtCfu.d0 := by
      rw [hc0]; simp
    have hpos : 1 / (2 * CtCfu.d0) < (Tsd ((0 : ℂ) ^ 2, (0 : ℂ))).re := by
      rw [h0]
      have := CtCfu.d0_pos
      rw [show 1 / (2 * CtCfu.d0) = (1 / CtCfu.d0) / 2 by field_simp]
      have : 0 < 1 / CtCfu.d0 := one_div_pos.2 this
      linarith
    exact (hc.eventually (lt_mem_nhds hpos)).mono fun p hp => hp.le
  have h10 : ∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), ‖Tsd (p.1 ^ 2, p.2)‖ ≤ 2 / CtCfu.d0 := by
    have hn : ContinuousAt (fun p : ℂ × ℂ => ‖Tsd (p.1 ^ 2, p.2)‖) (0, 0) := hcn.norm
    have h0 : ‖Tsd ((0 : ℂ) ^ 2, (0 : ℂ))‖ = 1 / CtCfu.d0 := by
      rw [hc0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.2 CtCfu.d0_pos)]
    have hlt : ‖Tsd ((0 : ℂ) ^ 2, (0 : ℂ))‖ < 2 / CtCfu.d0 := by
      rw [h0]
      have := CtCfu.d0_pos
      rw [div_lt_div_iff₀ this this]; nlinarith
    exact (hn.eventually (gt_mem_nhds hlt)).mono fun p hp => hp.le
  obtain ⟨ρ, hρ, hall⟩ := Metric.eventually_nhds_iff.mp
    (h1.and (h2.and (h3.and (h4.and (h5.and (h6.and (h7.and (h8.and (h9.and h10)))))))))
  refine ⟨ρ, hρ, fun s β hs hβ => ?_⟩
  have hmem : dist ((s, β) : ℂ × ℂ) ((0 : ℂ), (0 : ℂ)) < ρ := by
    rw [Prod.dist_eq, dist_zero_right, dist_zero_right]; exact max_lt hs hβ
  exact hall hmem

/-- The real chart `T(s;β) = Re Tf(s,β)` and its derivative. -/
noncomputable def Treal (β s : ℝ) : ℝ := (Tf ((s : ℂ), (β : ℂ))).re

noncomputable def T1real (β s : ℝ) : ℝ := (Tsd (((s : ℝ) : ℂ) ^ 2, (β : ℂ))).re

lemma conj2_real (s β : ℝ) : conj2 ((s : ℂ), (β : ℂ)) = ((s : ℂ), (β : ℂ)) := by
  simp [conj2]

lemma Tf_real_eq {s β : ℝ} (h : Tf (conj2 ((s : ℂ), (β : ℂ))) = starRingEnd ℂ (Tf ((s : ℂ), (β : ℂ)))) :
    Tf ((s : ℂ), (β : ℂ)) = ((Treal β s : ℝ) : ℂ) := by
  rw [conj2_real] at h
  apply Complex.ext
  · simp [Treal]
  · have := Complex.conj_eq_iff_im.1 h.symm
    simpa [Treal] using this

/-- The real chart is differentiable with derivative `Re Tsd` (which equals `Tsd`). -/
theorem Treal_deriv {ρ : ℝ} {β : ℝ}
    (hd : ∀ s : ℂ, ‖s‖ < ρ → HasDerivAt (fun s' : ℂ => Tf (s', (β : ℂ))) (Tsd (s ^ 2, (β : ℂ))) s)
    (hc : ∀ s : ℂ, ‖s‖ < ρ → Tf (conj2 (s, (β : ℂ))) = starRingEnd ℂ (Tf (s, (β : ℂ)))) {s : ℝ} (hs : |s| < ρ) :
    HasDerivAt (Treal β) (T1real β s) s ∧ Tsd (((s : ℝ) : ℂ) ^ 2, (β : ℂ)) = ((T1real β s : ℝ) : ℂ) := by
  have hmem : ‖(s : ℂ)‖ < ρ := by simpa using hs
  have h1 : HasDerivAt (Treal β) (T1real β s) s := by
    have := (hd (s : ℂ) hmem).real_of_complex
    exact this
  refine ⟨h1, ?_⟩
  have h2 : HasDerivAt (fun x : ℝ => ((Treal β x : ℝ) : ℂ)) ((T1real β s : ℝ) : ℂ) s := h1.ofReal_comp
  have h3 : HasDerivAt (fun x : ℝ => Tf ((x : ℂ), (β : ℂ))) (Tsd (((s : ℝ) : ℂ) ^ 2, (β : ℂ))) s :=
    (hd (s : ℂ) hmem).comp_ofReal
  have h4 : (fun x : ℝ => ((Treal β x : ℝ) : ℂ)) =ᶠ[𝓝 s] fun x : ℝ => Tf ((x : ℂ), (β : ℂ)) := by
    have hopen : ∀ᶠ x in 𝓝 s, |x| < ρ := (isOpen_lt continuous_abs continuous_const).mem_nhds hs
    filter_upwards [hopen] with x hx
    exact (Tf_real_eq (hc (x : ℂ) (by simpa using hx))).symm
  exact (h3.congr_of_eventuallyEq h4).unique h2

/-- The real phase `ϕ_L(τ) = ∫₀^τ m - L τ` (`= phaseP τ₀` for `L = m(τ₀)`). -/
noncomputable def phaseL (L τ : ℝ) : ℝ := (∫ u in (0 : ℝ)..τ, hankelEdgeM u) - L * τ

lemma phaseL_deriv (L : ℝ) {τ : ℝ} (hτ : 0 < τ) : HasDerivAt (phaseL L) (hankelEdgeM τ - L) τ := by
  have hc : ContinuousOn hankelEdgeM (Ici 0) := hankelEdgeM_continuousOn
  have hint : IntervalIntegrable hankelEdgeM volume 0 τ :=
    (hc.mono (fun x hx => by rw [uIcc_of_le hτ.le] at hx; exact hx.1)).intervalIntegrable
  have h1 : HasDerivAt (fun τ => ∫ u in (0 : ℝ)..τ, hankelEdgeM u) (hankelEdgeM τ) τ := by
    refine intervalIntegral.integral_hasDerivAt_right hint ?_ ?_
    · exact (hc.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi τ hτ
    · exact hc.continuousAt (Ici_mem_nhds hτ)
  exact h1.sub ((hasDerivAt_id τ).const_mul L) |>.congr_deriv (by simp)

lemma phaseL_eq_phaseP (τ0 τ : ℝ) : phaseL (hankelEdgeM τ0) τ = CtOsc.phaseP τ0 τ := rfl

/-- The pulled-back phase: `ϕ_L(T(s;β)) = a s + s³/3`. -/
lemma phase_pull {β s : ℝ}
    (hid : PhiC (Tf ((s : ℂ), (β : ℂ))) (β : ℂ) = -(aC (β : ℂ) * (s : ℂ) + (s : ℂ) ^ 3 / 3))
    (hconj : Tf (conj2 ((s : ℂ), (β : ℂ))) = starRingEnd ℂ (Tf ((s : ℂ), (β : ℂ))))
    (haC : aC (β : ℂ) = ((CtCfu.AF β : ℝ) : ℂ)) (hT0 : 0 ≤ Treal β s) (hT2 : Treal β s ^ 2 < CtCfu.rr) :
    phaseL (CtCfu.NF β) (Treal β s) = CtCfu.AF β * s + s ^ 3 / 3 := by
  have hT := Tf_real_eq hconj
  rw [hT] at hid
  unfold PhiC at hid
  rw [LC_ofReal, haC, show ((Treal β s : ℝ) : ℂ) ^ 2 = (((Treal β s) ^ 2 : ℝ) : ℂ) by push_cast; rfl, pC_ofReal] at hid
  have hid' : Treal β s * (CtCfu.NF β - Treal β s ^ 2 * CtCfu.ntil (Treal β s ^ 2)) = -(CtCfu.AF β * s + s ^ 3 / 3) := by
    exact_mod_cast hid
  unfold phaseL
  rw [CtCfu.integral_hankelEdgeM_eq hT0 hT2]
  linarith [hid']

lemma csq_ofReal {x : ℝ} (hx : 0 < x) : csq (x : ℂ) = ((Real.sqrt x : ℝ) : ℂ) := by
  unfold csq
  rw [← Complex.ofReal_log hx.le, show ((Real.log x : ℝ) : ℂ) / 2 = ((Real.log x / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
  congr 2
  ring

lemma csr_ofReal {s : ℝ} (hs : 0 ≤ s) : csr (s : ℂ) = ((Real.sqrt s : ℝ) : ℂ) := by
  have := csr_mul_ofReal hs (zero_le_one : (0 : ℝ) ≤ 1)
  have h1 : csr ((1 : ℝ) : ℂ) = 1 := by
    unfold csr; simp
  rw [h1, mul_one, mul_one] at this
  exact this

lemma mPrime_eq_kfun {T : ℝ} (hT : 0 < T) (hT2 : T ^ 2 < CtCfu.rr) :
    CtOuter.mPrime T = T * CtCfu.kfun (T ^ 2) := by
  rw [CtOuter.mPrime_eq_hankelEdgeM' hT]
  exact CtCfu.hankelEdgeM'_eq hT hT2

lemma mPrime_pos {T : ℝ} (hT : 0 < T) : 0 < CtOuter.mPrime T := by
  obtain ⟨C0, hC0, hM⟩ := CtOsc.mdata_hankel
  have := hM.m1_pos hT
  rwa [CtOsc.iteratedDeriv_one_m hT] at this

/-- The pulled-back amplitude at a real point. -/
theorem amp_pull {ε c β s psi a T T1 : ℝ} {ϑ : ℂ → ℂ}
    (hc : 0 < c) (hs : 0 < s)
    (hT : Tf ((s : ℂ), (β : ℂ)) = (T : ℂ)) (hTpos : 0 < T) (hT2 : T ^ 2 < CtCfu.rr) (hTh : T < 1 / 2)
    (hT1 : Tsd (((s : ℝ) : ℂ) ^ 2, (β : ℂ)) = (T1 : ℂ))
    (hsq : Tf ((s : ℂ), (β : ℂ)) ^ 2 = Zf (((s : ℝ) : ℂ) ^ 2, (β : ℂ)))
    (hamp : muf (((s : ℝ) : ℂ) ^ 2, (β : ℂ)) * Complex.exp (Complex.I * Xph ϑ ((s : ℂ), (β : ℂ))) =
      1 + (((s : ℝ) : ℂ) ^ 2 - ysF (β : ℂ)) * Qeps ϑ ((s : ℂ), (β : ℂ)))
    (hth : thOdd ε (Tf ((s : ℂ), (β : ℂ))) - (s : ℂ) * psiHat ϑ (β : ℂ) =
      (s : ℂ) * (((s : ℝ) : ℂ) ^ 2 - ysF (β : ℂ)) * htil ϑ (((s : ℝ) : ℂ) ^ 2, (β : ℂ)))
    (hys : ysF (β : ℂ) = -(a : ℂ)) (hpsi : psiHat ϑ (β : ℂ) = (psi : ℂ)) :
    ((Real.sqrt (π * c / 12) : ℝ) : ℂ) * CtOsc.outerAmp ε c T * (T1 : ℂ) =
      ((Real.sqrt c / Real.sqrt π : ℝ) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ)) * csr (s : ℂ) *
        gAmp a psi (fun z => Qeps ϑ (z, (β : ℂ)))
          (fun z => Complex.exp (-(FormalResearch.Asymptotics.binetDiff c (Complex.I * Tf (z, (β : ℂ)))))) (s : ℂ) := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hmp := mPrime_pos hTpos
  have hmk := mPrime_eq_kfun hTpos hT2
  have hk : 0 < CtCfu.kfun (T ^ 2) := by
    rw [hmk] at hmp
    exact pos_of_mul_pos_right hmp hTpos.le |>.trans_le le_rfl
  set x : ℝ := T * CtCfu.kfun (T ^ 2) / (2 * s) with hxdef
  have hx : 0 < x := by positivity
  -- `muf` at the real point
  have hUf : Uf (((s : ℝ) : ℂ) ^ 2, (β : ℂ)) = ((T / s : ℝ) : ℂ) := by
    have h : (s : ℂ) * Uf (((s : ℝ) : ℂ) ^ 2, (β : ℂ)) = (T : ℂ) := by
      rw [← hT]; rfl
    push_cast
    field_simp
    linear_combination h
  have hZ : Zf (((s : ℝ) : ℂ) ^ 2, (β : ℂ)) = ((T ^ 2 : ℝ) : ℂ) := by
    rw [← hsq, hT]; push_cast; ring
  have hmuf : muf (((s : ℝ) : ℂ) ^ 2, (β : ℂ)) = ((Real.sqrt x : ℝ) : ℂ) * (T1 : ℂ) := by
    unfold muf
    rw [hUf, hZ, kC_ofReal]
    have : ((T / s : ℝ) : ℂ) * ((CtCfu.kfun (T ^ 2) : ℝ) : ℂ) / 2 = (x : ℂ) := by
      rw [hxdef]; push_cast; field_simp
    rw [this, csq_ofReal hx, hT1]
  -- the phase
  have hθ : thOdd ε (Tf ((s : ℂ), (β : ℂ))) = ((CtOuter.outerTheta ε T : ℝ) : ℂ) := by
    rw [hT]; exact thOdd_real ε (by rw [abs_of_pos hTpos]; exact hTh)
  have hθ2 : ((CtOuter.outerTheta ε T : ℝ) : ℂ) = (s : ℂ) * (psi : ℂ) + Xph ϑ ((s : ℂ), (β : ℂ)) := by
    rw [← hθ]
    have : Xph ϑ ((s : ℂ), (β : ℂ)) = (s : ℂ) * (((s : ℝ) : ℂ) ^ 2 - ysF (β : ℂ)) * htil ϑ (((s : ℝ) : ℂ) ^ 2, (β : ℂ)) := rfl
    rw [this]
    rw [hpsi] at hth
    linear_combination hth
  have hexpθ : Complex.exp (Complex.I * ((CtOuter.outerTheta ε T : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (psi : ℂ) * (s : ℂ)) * Complex.exp (Complex.I * Xph ϑ ((s : ℂ), (β : ℂ))) := by
    rw [← Complex.exp_add, hθ2]; congr 1; ring
  -- the real prefactor
  have hpre : Real.sqrt (π * c / 12) * Real.sqrt (6 / π ^ 2 * (T * CtCfu.kfun (T ^ 2))) =
      Real.sqrt c / Real.sqrt π * Real.sqrt s * Real.sqrt x := by
    have hπ := Real.pi_pos
    have e1 : T * CtCfu.kfun (T ^ 2) = 2 * s * x := by rw [hxdef]; field_simp
    rw [e1, ← Real.sqrt_mul (by positivity)]
    have e2 : π * c / 12 * (6 / π ^ 2 * (2 * s * x)) = c * s * x / π := by field_simp; ring
    rw [e2, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    ring
  unfold CtOsc.outerAmp CtOsc.ampExp CtOsc.sqf
  rw [CtOsc.iteratedDeriv_one_m hTpos, hmk, show gAmp a psi = gAmp a psi from rfl]
  unfold gAmp
  simp only []
  rw [hT, csr_ofReal hs.le]
  have hbracket : (1 + ((s : ℂ) ^ 2 + (a : ℂ)) * Qeps ϑ ((s : ℂ), (β : ℂ))) =
      muf (((s : ℝ) : ℂ) ^ 2, (β : ℂ)) * Complex.exp (Complex.I * Xph ϑ ((s : ℂ), (β : ℂ))) := by
    rw [hamp, hys]; ring
  rw [hbracket, hmuf]
  have hexp1 : Complex.exp (Complex.I * ((π / 4 + CtOuter.outerTheta ε T : ℝ) : ℂ) -
      FormalResearch.Asymptotics.binetDiff c (Complex.I * (T : ℂ))) =
      Complex.exp (Complex.I * (π / 4 : ℝ)) * Complex.exp (Complex.I * ((CtOuter.outerTheta ε T : ℝ) : ℂ)) *
        Complex.exp (-(FormalResearch.Asymptotics.binetDiff c (Complex.I * (T : ℂ)))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [hexp1, hexpθ]
  have hpreC : ((Real.sqrt (π * c / 12) : ℝ) : ℂ) * ((Real.sqrt (6 / π ^ 2 * (T * CtCfu.kfun (T ^ 2))) : ℝ) : ℂ) =
      ((Real.sqrt c / Real.sqrt π : ℝ) : ℂ) * ((Real.sqrt s : ℝ) : ℂ) * ((Real.sqrt x : ℝ) : ℂ) := by
    exact_mod_cast hpre
  linear_combination (Complex.exp (Complex.I * (π / 4 : ℝ)) * (Complex.exp (Complex.I * (psi : ℂ) * (s : ℂ)) *
      Complex.exp (Complex.I * Xph ϑ ((s : ℂ), (β : ℂ)))) *
      Complex.exp (-(FormalResearch.Asymptotics.binetDiff c (Complex.I * (T : ℂ)))) * (T1 : ℂ)) * hpreC

end FormalResearch.SignUncertainty.CtSd
