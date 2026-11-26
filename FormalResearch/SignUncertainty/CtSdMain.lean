module

public import FormalResearch.SignUncertainty.CtSdFinal
public import FormalResearch.SignUncertainty.CtChartQ0

/-!
# `(ct:K-airy)`, concrete form (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` (1), `(ct:K-airy)`.  **Proved.**
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real Interval

set_option linter.unusedSectionVars false

namespace FormalResearch.SignUncertainty.CtSd

open FormalResearch.SignUncertainty.CtChart FormalResearch.Special

lemma abs_re_le_of_norm {z : ℂ} {x : ℝ} (h : ‖z‖ ≤ x) : |z.re| ≤ x := (Complex.abs_re_le_norm z).trans h

lemma chain_exists {rr Uh Cm1 Cm2 : ℝ}
    (hmA : ∀ (U R R₀ : ℝ) (hU : -1 ≤ U) (hR : 0 ≤ R) (hRR : R < R₀), MomOK Cm1 U (chainA hR hRR))
    (hmB : ∀ (v R R₀ : ℝ) (hv : 0 < v) (hvk : kap ≤ v ^ 2) (hR : (1 + Real.sqrt 3) * v ≤ R) (hRR : R < R₀)
      (h3 : 3 * v < R₀), MomOK Cm2 (-(v ^ 2) / kap) (chainB hv hR hRR h3))
    (hCm1 : 0 ≤ Cm1) (hCm2 : 0 ≤ Cm2) (hrr : 0 < rr) (hKU16 : kap * |Uh| ≤ (rr ^ 2) ^ 2 / 16) :
    ∃ ch : Chain3 (2 * rr ^ 2) (((rr ^ 2 : ℝ) : ℂ) * d6), MomOK (Cm1 + Cm2) Uh ch := by
  have hR0 : 0 < rr ^ 2 := by positivity
  have hRR : rr ^ 2 < 2 * rr ^ 2 := by linarith
  have hk := kap_pos
  by_cases hU1 : -1 ≤ Uh
  · exact ⟨chainA hR0.le hRR, momOK_mono (hmA Uh (rr ^ 2) (2 * rr ^ 2) hU1 hR0.le hRR) (by linarith)⟩
  · push_neg at hU1
    have hneg : Uh < 0 := by linarith
    have hpos : 0 < -(kap * Uh) := by nlinarith
    set v : ℝ := Real.sqrt (-(kap * Uh)) with hvdef
    have hv2 : v ^ 2 = -(kap * Uh) := Real.sq_sqrt hpos.le
    have hv0 : 0 < v := Real.sqrt_pos.2 hpos
    have hvk : kap ≤ v ^ 2 := by rw [hv2]; nlinarith
    have hvR : v ≤ rr ^ 2 / 4 := by
      have h1 : v ^ 2 ≤ (rr ^ 2 / 4) ^ 2 := by
        rw [hv2]
        have : kap * |Uh| = -(kap * Uh) := by rw [abs_of_neg hneg]; ring
        nlinarith
      exact (abs_le_of_sq_le_sq' h1 (by positivity)).2
    have hs3 := sqrt3_bounds
    have hR : (1 + Real.sqrt 3) * v ≤ rr ^ 2 := by nlinarith
    have h3 : 3 * v < 2 * rr ^ 2 := by nlinarith
    refine ⟨chainB hv0 hR hRR h3, momOK_mono (C := Cm2) ?_ (by linarith)⟩
    have e : Uh = -(v ^ 2) / kap := by rw [hv2]; field_simp
    rw [e]
    exact hmB v (rr ^ 2) (2 * rr ^ 2) hv0 hvk hR hRR h3

lemma hU_aux {lam s1 Uh rr : ℝ} (hlam : 0 < lam) (hs1 : 0 < s1) (hrr2 : rr ^ 2 = s1 / lam)
    (hKU16 : kap * |Uh| ≤ (rr ^ 2) ^ 2 / 16) (hk1 : 1 ≤ kap) : lam * Real.sqrt |Uh| ≤ s1 := by
  have h1 : (lam * Real.sqrt |Uh|) ^ 2 ≤ s1 ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
    have h0 : |Uh| ≤ kap * |Uh| := by nlinarith [abs_nonneg Uh]
    have h2 : |Uh| ≤ (s1 ^ 2 / 16) / lam ^ 2 := by
      have e : (rr ^ 2) ^ 2 / 16 = (s1 ^ 2 / 16) / lam ^ 2 := by rw [hrr2]; field_simp
      linarith
    rw [le_div_iff₀ (by positivity)] at h2
    nlinarith [sq_nonneg s1]
  exact (abs_le_of_sq_le_sq' h1 hs1.le).2

lemma htail_aux {rr Uh : ℝ} (hR0 : 0 < rr ^ 2) (hKU16 : kap * |Uh| ≤ (rr ^ 2) ^ 2 / 16) (hk1 : 1 ≤ kap) :
    ∀ t, rr ^ 2 < t → -(t ^ 3 / 6) ≤ nu * Uh * t := by
  intro t ht
  have ht0 : 0 < t := lt_trans hR0 ht
  have hnu := nu_le_one
  have hnu0 := nu_pos
  have h1 : -|Uh| ≤ nu * Uh := by
    have := neg_abs_le Uh
    have h2 : nu * (-|Uh|) ≤ nu * Uh := mul_le_mul_of_nonneg_left this hnu0.le
    nlinarith [abs_nonneg Uh]
  have h3 : |Uh| ≤ t ^ 2 / 16 := by
    have : |Uh| ≤ kap * |Uh| := by nlinarith [abs_nonneg Uh]
    have h4 : (rr ^ 2) ^ 2 ≤ t ^ 2 := by nlinarith
    linarith
  have h5 : -(|Uh| * t) ≤ nu * Uh * t := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h3 ht0.le, pow_pos ht0 3]

set_option maxHeartbeats 16000000 in
theorem cfu_K_airy_beta {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ th : ℝ → ℝ, AnalyticAt ℝ th 0 ∧ (∀ᶠ τ in 𝓝 (0 : ℝ), CtOuter.outerTheta ε τ = τ * th (τ ^ 2)) ∧
    ∃ s1 β0 c0 hh CK : ℝ, 0 < s1 ∧ 0 < β0 ∧ 2 ≤ c0 ∧ 0 ≤ CK ∧
      ∀ {c lam β : ℝ}, c0 ≤ c → 0 < lam → c * lam ^ 3 = 1 → |β| < β0 →
        ∃ Itot : ℂ, Tendsto (fun b : ℝ => ∫ τ in (0 : ℝ)..b, Bfun ε c τ *
            Complex.exp (Complex.I * c * (phaseL (CtCfu.NF β) τ : ℂ))) atTop (𝓝 Itot) ∧
          |(-Itot.re) - KMain lam (th β / CtCfu.dF β) q0c hh (Uhat lam (CtCfu.AF β) (th β / CtCfu.dF β))| ≤
            CK * lam ^ 4 * (1 + |Uhat lam (CtCfu.AF β) (th β / CtCfu.dF β)|) ^ (1 / 2 : ℝ) := by
  obtain ⟨th, hthA, hth, hth0, hth1⟩ := CtCfu.theta_hat hε
  refine ⟨th, hthA, hth, ?_⟩
  have hε' : ε = -1 ∨ ε = 1 := hε.symm
  obtain ⟨ϑ, hA, hϑ⟩ := CtChart.exists_vartheta ε
  have hconj := CtChart.vartheta_conj hA hϑ hth
  obtain ⟨ρ, hρ, hreg⟩ := chart_region hA hϑ
  -- the real constant `h̃(0,0)`
  have hhr := htil_zero_real hA hconj
  set hh : ℝ := (htil ϑ (0, 0)).re with hhdef
  have hhh : htil ϑ (0, 0) = (hh : ℂ) := (Complex.conj_eq_iff_re.1 hhr).symm
  have hQg : Qgeo (0, 0) = ((q0c : ℝ) : ℂ) := CtChart.Qgeo_zero_paper
  have hd0 := CtCfu.d0_pos
  set Cβ : ℝ := 4 / CtCfu.d0 ^ 2 with hCβ
  obtain ⟨ρ1, CQ, CE, CB, hρ1, hρ1ρ, hρ11, hCQ, hCE, hCB, hSd⟩ := sdAmp_real hA hreg hρ (Cβ := Cβ) (by positivity)
  obtain ⟨C0, CA, hC0, hCA, hTail⟩ := tailBd_real hε'
  obtain ⟨K, r, hK, hr, hLip⟩ := exists_Tf_lip
  obtain ⟨Cm1, hCm1, hmA⟩ := chainA_momOK
  obtain ⟨Cm2, hCm2, hmB⟩ := chainB_momOK
  obtain ⟨δ1, hδ1, hAFl⟩ := exists_AF_lower
  obtain ⟨δ2, Cψ, hδ2, hCψ, hpsib⟩ := exists_psi_bound hthA
  have hev12 := (aC_ofReal).and (psiHat_ofReal hA hthA hϑ hth)
  obtain ⟨δ3, hδ3, hev3⟩ := Metric.eventually_nhds_iff.mp hev12
  -- the scale `s1`
  set s1 : ℝ := min (min (ρ1 / 4) (r / 4)) (min (1 / (8 * K + 8)) 1) with hs1def
  have hs10 : 0 < s1 := lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) one_pos)
  have hs1a : s1 ≤ ρ1 / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hs1b : s1 ≤ r / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hs1c : s1 ≤ 1 / (8 * K + 8) := (min_le_right _ _).trans (min_le_left _ _)
  have hs11 : s1 ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  -- smallness of `a`
  have hAFc : ContinuousAt CtCfu.AF 0 := CtCfu.contDiffAt_AF.continuousAt
  have hev4 : ∀ᶠ β in 𝓝 (0 : ℝ), |CtCfu.AF β| < s1 ^ 2 / 32 := by
    have := (continuous_abs.continuousAt.comp hAFc).eventually
      (gt_mem_nhds (show (abs ∘ CtCfu.AF) 0 < s1 ^ 2 / 32 by simp [CtCfu.AF_zero]; positivity))
    exact this
  obtain ⟨δ4, hδ4, h4⟩ := Metric.eventually_nhds_iff.mp hev4
  set β0 : ℝ := min (min (min δ1 δ2) (min δ3 δ4)) (min ρ1 r) with hβ0def
  have hβ0 : 0 < β0 := lt_min (lt_min (lt_min hδ1 hδ2) (lt_min hδ3 hδ4)) (lt_min hρ1 hr)
  -- the large parameter
  set c0 : ℝ := max (max 2 (1 / s1 ^ 3)) (32 * Cψ / s1 ^ 2 + 1) with hc0def
  have hc0 : 2 ≤ c0 := (le_max_left _ _).trans (le_max_left _ _)
  -- error constants
  set K1 : ℝ := 2 / CtCfu.d0 with hK1def
  have hK1 : 0 < K1 := by positivity
  set γ : ℝ := min 1 ((15 / 16) * s1 ^ 2 / K1) with hγdef
  have hγ : 0 < γ := lt_min one_pos (div_pos (mul_pos (by norm_num) (pow_pos hs10 2)) hK1)
  set τs : ℝ := (1 / (2 * CtCfu.d0)) * s1 with hτsdef
  have hτs : 0 < τs := by positivity
  set Cqq : ℝ := CQ * (1 + s1 ^ 2) + ‖Complex.I * (hh : ℂ)‖ * s1 with hCqq
  have hCqq0 : 0 ≤ Cqq := by positivity
  set Cm : ℝ := Cm1 + Cm2 with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  obtain ⟨C6e, hC6e0, hC6e⟩ := exp_le_lam6 (δ := 29 * s1 ^ 3 / 96) (by positivity)
  obtain ⟨C6a, hC6a0, hC6a⟩ := exp_le_lam6 (δ := s1 ^ 3 / 12) (by positivity)
  set Cend : ℝ := Cqq * C6e * Real.sqrt s1 with hCend
  have hCend0 : 0 ≤ Cend := by positivity
  set Cb0 : ℝ := CB * (1 + CE * (3 * s1)) * Real.exp (Cψ * (3 * s1)) with hCb0
  have hCb00 : 0 ≤ Cb0 := by positivity
  set CP : ℝ := 1 + Cψ * |q0c| + 3 / 2 * |hh| with hCP
  have hCP0 : 0 ≤ CP := by positivity
  set Sd : ℝ := sdC CQ CE CB Cm s1 Cend (3 * s1) ‖Complex.I * (hh : ℂ)‖ Cψ with hSd'
  have hSd0 : 0 ≤ Sd := by
    rw [hSd']; unfold sdC
    have := kap_pos
    positivity
  set CKa : ℝ := (1 / √π) * (Sd + CP * 144 * C6a + |q0c| * 288 * C6a) with hCKa
  set CKb : ℝ := (1 / √π) * ((16 * (2 * Cb0) + 1024 * (2 * Cb0)) * C6a + 320000 * (2 * Cb0) / s1 ^ 4) with hCKb
  set CKc : ℝ := Real.sqrt (π / 12) * CA * (4 * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) / γ ^ 2) *
    ((2 / 9) * τs ^ (-9 / 2 : ℝ) + (2 / 3) * τs ^ (-3 / 2 : ℝ)) with hCKc
  have hCKa0 : 0 ≤ CKa := by rw [hCKa]; positivity
  have hCKb0 : 0 ≤ CKb := by rw [hCKb]; positivity
  have hCKc0 : 0 ≤ CKc := by rw [hCKc]; positivity
  refine ⟨s1, β0, c0, hh, CKa + CKb + CKc, hs10, hβ0, hc0, by positivity, ?_⟩
  intro c lam β hcc hlam hlc hβ
  have hc2 : 2 ≤ c := hc0.trans hcc
  have hcpos : 0 < c := by linarith
  have hcs : 1 / s1 ^ 3 ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hcc
  have hcψ : 32 * Cψ / s1 ^ 2 + 1 ≤ c := (le_max_right _ _).trans hcc
  have hc' : c = 1 / lam ^ 3 := by
    have : 0 < lam ^ 3 := by positivity
    field_simp; linarith
  have hlam1 : lam ≤ 1 := by
    by_contra h
    push_neg at h
    have h1 : 1 < lam ^ 3 := one_lt_pow₀ h (by norm_num)
    have h2 := mul_le_mul_of_nonneg_left h1.le hcpos.le
    linarith only [h2, hlc, hc2]
  have hlams1 : lam ≤ s1 := by
    by_contra h
    push_neg at h
    have h1 : s1 ^ 3 < lam ^ 3 := pow_lt_pow_left₀ h hs10.le (by norm_num)
    have h2 : 1 ≤ c * s1 ^ 3 := by
      have := (div_le_iff₀ (pow_pos hs10 3)).1 hcs
      exact this
    have h3 := mul_lt_mul_of_pos_left h1 hcpos
    linarith only [h3, h2, hlc]
  -- smallness of `β`
  have hβδ1 : |β| < δ1 := hβ.trans_le (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hβδ2 : |β| < δ2 := hβ.trans_le (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hβδ3 : |β| < δ3 := hβ.trans_le (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_left _ _))
  have hβδ4 : |β| < δ4 := hβ.trans_le (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_right _ _))
  have hβρ1 : |β| < ρ1 := hβ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hβr : |β| < r := hβ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hβρ : |β| < ρ := hβρ1.trans_le hρ1ρ
  have hβa : |β| ≤ Cβ * |CtCfu.AF β| := hAFl β hβδ1
  have ha32 : |CtCfu.AF β| ≤ s1 ^ 2 / 32 := (h4 (by simpa using hβδ4)).le
  have hpsiB : |th β / CtCfu.dF β| ≤ Cψ := hpsib β hβδ2
  obtain ⟨haC, hpsi⟩ := hev3 (y := β) (by simpa using hβδ3)
  set a : ℝ := CtCfu.AF β with ha
  set psi : ℝ := th β / CtCfu.dF β with hpsidef
  have hψ : lam ^ 3 * |psi| ≤ s1 ^ 2 / 32 := by
    have h1 : Cψ ≤ c * (s1 ^ 2 / 32) := by
      have := (div_le_iff₀ (pow_pos hs10 2)).1 (show 32 * Cψ / s1 ^ 2 ≤ c by linarith)
      linarith
    calc lam ^ 3 * |psi| ≤ lam ^ 3 * Cψ := mul_le_mul_of_nonneg_left hpsiB (by positivity)
      _ ≤ lam ^ 3 * (c * (s1 ^ 2 / 32)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = s1 ^ 2 / 32 := by rw [← mul_assoc, show lam ^ 3 * c = 1 by linarith]; ring
  -- the scales
  set rr : ℝ := Real.sqrt (s1 / lam) with hrrdef
  have hrr2 : rr ^ 2 = s1 / lam := Real.sq_sqrt (by positivity)
  have hrr : 0 < rr := Real.sqrt_pos.2 (by positivity)
  have hR0 : 0 < rr ^ 2 := by positivity
  have hR1 : 1 ≤ rr ^ 2 := by rw [hrr2, le_div_iff₀ hlam]; linarith
  have hrr1 : 1 ≤ rr := by
    by_contra h
    push_neg at h
    have := mul_lt_mul'' h h hrr.le hrr.le
    nlinarith only [this, hR1]
  have hsR : s1 = lam * rr ^ 2 := by rw [hrr2]; field_simp
  have hR3 : (rr ^ 2) ^ 3 = s1 ^ 3 * c := by rw [hrr2, hc']; field_simp
  set Uh : ℝ := Uhat lam a psi with hUhdef
  set Ua : ℝ := a / (kap * lam ^ 2) with hUadef
  have hk := kap_pos
  have hk1 := kap_ge_one
  have hUa : a = kap * Ua * lam ^ 2 := by rw [hUadef]; field_simp
  have hUh : kap * Uh * lam ^ 2 = a + lam ^ 3 * psi := by rw [hUhdef]; unfold Uhat; field_simp
  have key : ∀ x : ℝ, kap * |x| * lam ^ 2 ≤ s1 ^ 2 / 16 → kap * |x| ≤ (rr ^ 2) ^ 2 / 16 := by
    intro x hx
    have e : (rr ^ 2) ^ 2 / 16 = (s1 ^ 2 / 16) / lam ^ 2 := by rw [hrr2]; field_simp
    rw [e, le_div_iff₀ (by positivity)]
    exact hx
  have hseg16 : kap * |Ua| ≤ (rr ^ 2) ^ 2 / 16 := by
    apply key
    have : kap * |Ua| * lam ^ 2 = |a| := by
      rw [hUadef, abs_div, abs_of_pos (by positivity : 0 < kap * lam ^ 2)]; field_simp
    rw [this]; linarith only [ha32, sq_nonneg s1]
  have hKU16 : kap * |Uh| ≤ (rr ^ 2) ^ 2 / 16 := by
    apply key
    have : kap * |Uh| * lam ^ 2 = |a + lam ^ 3 * psi| := by
      rw [hUhdef]; unfold Uhat
      rw [abs_div, abs_of_pos (by positivity : 0 < kap * lam ^ 2)]; field_simp
    rw [this]
    calc |a + lam ^ 3 * psi| ≤ |a| + |lam ^ 3 * psi| := abs_add_le _ _
      _ ≤ s1 ^ 2 / 16 := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < lam ^ 3)]; linarith only [ha32, hψ, sq_nonneg s1]
  have hkUR : kap * |Uh| ≤ (rr ^ 2) ^ 2 := by linarith only [hKU16, sq_nonneg (rr ^ 2)]
  -- normalisations
  have hsq : Real.sqrt c * (lam * Real.sqrt lam) = 1 := by
    have h1 : lam * Real.sqrt lam = Real.sqrt (lam ^ 3) := by
      rw [show lam ^ 3 = lam ^ 2 * lam by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hlam.le]
    rw [h1, ← Real.sqrt_mul hcpos.le, hlc, Real.sqrt_one]
  have hNc : Ncc c * ((lam * Real.sqrt lam : ℝ) : ℂ) =
      ((1 / √π : ℝ) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ)) := by
    unfold Ncc
    have : (Real.sqrt c / Real.sqrt π) * (lam * Real.sqrt lam) = 1 / √π := by
      rw [div_mul_eq_mul_div, mul_comm (Real.sqrt c), mul_assoc]
      field_simp
      linarith [hsq]
    calc ((Real.sqrt c / Real.sqrt π : ℝ) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ)) * ((lam * Real.sqrt lam : ℝ) : ℂ)
        = (((Real.sqrt c / Real.sqrt π) * (lam * Real.sqrt lam) : ℝ) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ)) := by
          push_cast; ring
      _ = _ := by rw [this]
  -- the chain and its moments
  have hRR : rr ^ 2 < 2 * rr ^ 2 := by linarith
  obtain ⟨ch, hm⟩ := chain_exists hmA hmB hCm1 hCm2 hrr hKU16
  have hU := hU_aux hlam hs10 hrr2 hKU16 hk1
  have htail := htail_aux hR0 hKU16 hk1
  have hCU : 0 ≤ s1 := hs10.le
  -- the pull-back
  have hs1ρ : 2 * s1 < ρ := by linarith only [hs1a, hρ1ρ, hρ1]
  have hTb : ∀ s ∈ Icc (0 : ℝ) (2 * s1), |Treal β s| < 1 / 4 := by
    intro s hs
    have hsr : ‖(s : ℂ)‖ < r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; linarith only [hs.2, hs1b, hr]
    have hβr' : ‖(β : ℂ)‖ < r := by simpa using hβr
    have h1 := hLip (s : ℂ) (β : ℂ) hsr hβr'
    have h2 : |Treal β s| ≤ ‖Tf ((s : ℂ), (β : ℂ))‖ := Complex.abs_re_le_norm _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1] at h1
    have h3 : K * s ≤ K * (2 * s1) := mul_le_mul_of_nonneg_left hs.2 hK
    have h5 : s1 * (8 * K + 8) ≤ 1 := (le_div_iff₀ (by positivity)).1 hs1c
    linarith only [h1, h2, h3, h5, hs10]
  have pb := pullBack_real hreg (by linarith only [hc2]) hs1ρ hβρ hTb haC hpsi
  have hs1I : s1 ∈ Icc (0 : ℝ) (2 * s1) := ⟨hs10.le, by linarith only [hs10]⟩
  have hpos := T_pos_of_deriv pb.hT pb.hT1 pb.hT0 s1 ⟨hs10, by linarith only [hs10]⟩
  have hregs1 := hreg ((s1 : ℝ) : ℂ) (β : ℂ) (by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs10.le]; linarith only [hs1a, hρ1ρ, hρ1])
    (by simpa using hβρ)
  have hT1K : T1real β s1 ≤ K1 := by
    have := hregs1.2.2.2.2.2.2.2.2.2
    exact (Complex.re_le_norm _).trans this
  have ha16 : |a| ≤ s1 ^ 2 / 16 := by linarith only [ha32, sq_nonneg s1]
  obtain ⟨B1, B2, tb⟩ := hTail hc2 hs10 (by linarith only [hs10] : s1 < 2 * s1) hK1 pb.hT pb.hϕT hpos
    (pb.hT1 s1 hs1I) hT1K ha16
  have hτ1 : τs ≤ Treal β s1 := by
    have := T_lower (δ := 1 / (2 * CtCfu.d0)) pb.hT (fun s hs => by
      have hh := hreg (s : ℂ) (β : ℂ) (by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; linarith only [hs.2, hs1a, hρ1ρ, hρ1])
        (by simpa using hβρ)
      exact hh.2.2.2.2.2.2.2.2.1) pb.hT0 hs1I
    rw [hτsdef]; exact this
  -- the amplitude data
  have h3ρ1 : 3 * s1 ≤ ρ1 := by linarith only [hs1a, hρ1]
  have ha1 : |a| ≤ 1 := by nlinarith only [ha32, hs11, hs10]
  obtain ⟨amp0, hEd⟩ := hSd (c := c) (lam := lam) (ρ0 := 3 * s1) (β := β) (a := a) hc2 hlam hlc
    (by linarith only [hs10]) h3ρ1 hβρ1 hβa ha1
  rw [hQg, hhh] at amp0
  have hne : ∀ s ∈ Ioo (s1 / 2) (2 * s1), a + s ^ 2 ≠ 0 := by
    intro s hs
    have h1 : s1 / 2 < s := hs.1
    have h2 : (s1 / 2) ^ 2 < s ^ 2 := pow_lt_pow_left₀ h1 (by positivity) (by norm_num)
    have h3 := (abs_le.1 ha32).1
    have : 0 < a + s ^ 2 := by nlinarith only [h2, h3, sq_nonneg s1]
    exact this.ne'
  -- the endpoint term
  have hn1 : ‖csr (((rr ^ 2 : ℝ) : ℂ) * d6)‖ = rr := by
    rw [norm_csr, norm_mul, Complex.norm_real, norm_d6, mul_one, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg rr),
      Real.sqrt_sq hrr.le]
  have hz : ‖(lam : ℂ) * (((rr ^ 2 : ℝ) : ℂ) * d6)‖ = s1 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, norm_d6, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hlam, abs_of_nonneg (sq_nonneg rr), ← hsR]
  have hzb : (lam : ℂ) * (((rr ^ 2 : ℝ) : ℂ) * d6) ∈ ball (0 : ℂ) (3 * s1) := by
    rw [mem_ball, dist_zero_right, hz]; linarith only [hs10]
  have hQq : ‖Qeps ϑ ((lam : ℂ) * (((rr ^ 2 : ℝ) : ℂ) * d6), (β : ℂ)) - ((q0c : ℝ) : ℂ)‖ ≤ Cqq := by
    have h1 := amp0.hQ1 _ hzb
    have e : Qeps ϑ ((lam : ℂ) * (((rr ^ 2 : ℝ) : ℂ) * d6), (β : ℂ)) - ((q0c : ℝ) : ℂ) =
        (Qeps ϑ ((lam : ℂ) * (((rr ^ 2 : ℝ) : ℂ) * d6), (β : ℂ)) - ((q0c : ℝ) : ℂ) -
          Complex.I * (hh : ℂ) * ((lam : ℂ) * (((rr ^ 2 : ℝ) : ℂ) * d6))) +
        Complex.I * (hh : ℂ) * ((lam : ℂ) * (((rr ^ 2 : ℝ) : ℂ) * d6)) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul (Complex.I * (hh : ℂ)), hz]
    rw [hz] at h1
    have ha' : ‖(a : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact ha1
    have : CQ * (‖(a : ℂ)‖ + s1 ^ 2) ≤ CQ * (1 + s1 ^ 2) := mul_le_mul_of_nonneg_left (by linarith only [ha']) hCQ
    rw [hCqq]
    linarith only [h1, this]
  have hseg0 : segPt (rr ^ 2) 0 = ((rr ^ 2 : ℝ) : ℂ) * d6 := by simp [segPt]
  have hIm := im_PhU_segPt (R := rr ^ 2) (t := 0) hR0.le le_rfl zero_le_one (U := Uh) hKU16
  rw [hseg0] at hIm
  have hexp : Real.exp (-(PhU Uh (((rr ^ 2 : ℝ) : ℂ) * d6)).im) ≤ C6e * lam ^ 6 := by
    have e : rr ^ 2 / 2 * (29 * (rr ^ 2) ^ 2 / 48) * (1 - 0) = (29 * s1 ^ 3 / 96) * c := by
      have : rr ^ 2 / 2 * (29 * (rr ^ 2) ^ 2 / 48) * (1 - 0) = 29 * (rr ^ 2) ^ 3 / 96 := by ring
      rw [this, hR3]; ring
    rw [e] at hIm
    exact (Real.exp_le_exp.2 (by linarith only [hIm])).trans (hC6e hlam hlc)
  have hrl : rr * lam ≤ Real.sqrt s1 := by
    have h1 : (rr * lam) ^ 2 ≤ s1 := by
      rw [mul_pow, hrr2]
      have : s1 / lam * lam ^ 2 = s1 * lam := by field_simp
      rw [this]; nlinarith only [hlam1, hs10]
    calc rr * lam = Real.sqrt ((rr * lam) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt s1 := Real.sqrt_le_sqrt h1
  have hend : lam ^ 2 * (‖csr (((rr ^ 2 : ℝ) : ℂ) * d6)‖ *
      ‖(fun z => Qeps ϑ (z, (β : ℂ))) ((lam : ℂ) * (((rr ^ 2 : ℝ) : ℂ) * d6)) - ((q0c : ℝ) : ℂ)‖ *
      Real.exp (-(PhU Uh (((rr ^ 2 : ℝ) : ℂ) * d6)).im)) ≤ Cend * lam ^ 4 := by
    rw [hn1]
    have hl4 : lam ^ 7 ≤ lam ^ 4 := pow_le_pow_of_le_one hlam.le hlam1 (by norm_num)
    have s1' : lam ^ 2 * (rr * ‖Qeps ϑ ((lam : ℂ) * (((rr ^ 2 : ℝ) : ℂ) * d6), (β : ℂ)) - ((q0c : ℝ) : ℂ)‖ *
        Real.exp (-(PhU Uh (((rr ^ 2 : ℝ) : ℂ) * d6)).im)) ≤ lam ^ 2 * (rr * Cqq * (C6e * lam ^ 6)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hQq hrr.le) hexp (Real.exp_pos _).le (by positivity)
    refine s1'.trans ?_
    have e : lam ^ 2 * (rr * Cqq * (C6e * lam ^ 6)) = Cqq * C6e * ((rr * lam) * lam ^ 7) := by ring
    rw [e, hCend]
    have : (rr * lam) * lam ^ 7 ≤ Real.sqrt s1 * lam ^ 4 :=
      mul_le_mul hrl hl4 (by positivity) (Real.sqrt_nonneg _)
    calc Cqq * C6e * ((rr * lam) * lam ^ 7) ≤ Cqq * C6e * (Real.sqrt s1 * lam ^ 4) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = Cqq * C6e * Real.sqrt s1 * lam ^ 4 := by ring
  have hR₀ : lam * (2 * rr ^ 2) ≤ 3 * s1 := by rw [hrr2]; field_simp; linarith only [hs10]
  obtain ⟨Itot, hI, hb⟩ := outer_assembly (c := c) (lam := lam) (s1 := s1) (s1' := 2 * s1) (rr := rr) (a := a)
    (Ua := Ua) (Uh := Uh) (psi := psi) (q0 := q0c) (hh := hh) (L := CtCfu.NF β) (R₀ := 2 * rr ^ 2) (Nc := Ncc c)
    (N1 := ((1 / √π : ℝ) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ)))
    hcpos hlam hlam1 hlc hs10 (by linarith only [hs10]) hrr hR1 hsR hUa hUh hseg16 rfl hNc hRR hR₀ ch amp0 hEd hm
    hCm0 hCU hU hCend0 hend htail hkUR pb tb hne
  refine ⟨Itot, hI, ?_⟩
  have hX := one_le_rpow_half Uh
  set X : ℝ := (1 + |Uh|) ^ (1 / 2 : ℝ) with hXdef
  have hl4 : lam ^ 6 ≤ lam ^ 4 := pow_le_pow_of_le_one hlam.le hlam1 (by norm_num)
  have hl8 : lam ^ 8 ≤ lam ^ 4 := pow_le_pow_of_le_one hlam.le hlam1 (by norm_num)
  have hEb : Real.exp (-((rr ^ 2) ^ 3 / 12)) ≤ C6a * lam ^ 4 := by
    have h := hC6a hlam hlc
    have e : -((rr ^ 2) ^ 3 / 12) = -(s1 ^ 3 / 12 * c) := by rw [hR3]; ring
    rw [e]
    exact h.trans (mul_le_mul_of_nonneg_left hl4 hC6a0)
  have hE4b : Real.exp (-((rr ^ 2) ^ 3 / 4)) ≤ C6a * lam ^ 4 := by
    refine le_trans (Real.exp_le_exp.2 ?_) hEb
    have : 0 ≤ (rr ^ 2) ^ 3 := by positivity
    linarith only [this]
  have hE0 := (Real.exp_pos (-((rr ^ 2) ^ 3 / 12))).le
  have hE40 := (Real.exp_pos (-((rr ^ 2) ^ 3 / 4))).le
  have hCg : 2 * (CB * (1 + CE * (3 * s1)) * Real.exp (|psi| * (3 * s1))) ≤ 2 * Cb0 := by
    rw [hCb0]
    have : Real.exp (|psi| * (3 * s1)) ≤ Real.exp (Cψ * (3 * s1)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hpsiB (by positivity))
    have h0 : 0 ≤ CB * (1 + CE * (3 * s1)) := by positivity
    linarith only [mul_le_mul_of_nonneg_left this h0]
  have hCg0 : 0 ≤ 2 * (CB * (1 + CE * (3 * s1)) * Real.exp (|psi| * (3 * s1))) := by positivity
  have hrr9 : 1 / rr ^ 9 ≤ lam ^ 4 / s1 ^ 4 := by
    have h8 : (s1 / lam) ^ 4 ≤ rr ^ 9 := by
      have : (s1 / lam) ^ 4 = rr ^ 8 := by rw [← hrr2]; ring
      rw [this]
      calc rr ^ 8 = rr ^ 8 * 1 := by ring
        _ ≤ rr ^ 8 * rr := mul_le_mul_of_nonneg_left hrr1 (by positivity)
        _ = rr ^ 9 := by ring
    calc 1 / rr ^ 9 ≤ 1 / (s1 / lam) ^ 4 := one_div_le_one_div_of_le (by positivity) h8
      _ = lam ^ 4 / s1 ^ 4 := by field_simp
  have hrr3 : 1 / rr ^ 3 ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ hrr1
  have hrr9' : 1 / rr ^ 9 ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ hrr1
  have hsqc : Real.sqrt c * lam ^ 2 ≤ 1 := by
    have h1 : (Real.sqrt c * lam ^ 2) ^ 2 ≤ 1 := by
      rw [mul_pow, Real.sq_sqrt hcpos.le]
      have : c * (lam ^ 2) ^ 2 = lam := by
        have : c * lam ^ 3 = 1 := hlc
        calc c * (lam ^ 2) ^ 2 = (c * lam ^ 3) * lam := by ring
          _ = lam := by rw [this]; ring
      rw [this]; exact hlam1
    exact (abs_le_of_sq_le_sq' (by rw [one_pow]; exact h1) zero_le_one).2
  have hlc6 : 1 / c ^ 2 = lam ^ 6 := by
    rw [hc']; field_simp
  have key : ∀ A B C : ℝ, A ≤ CKa * lam ^ 4 * X → B ≤ CKb * lam ^ 4 → C ≤ CKc * lam ^ 4 →
      A + B + C ≤ (CKa + CKb + CKc) * lam ^ 4 * X := by
    intro A B C hA hB hC
    have hl40 : 0 ≤ lam ^ 4 := by positivity
    have h2 : CKb * lam ^ 4 ≤ CKb * lam ^ 4 * X := le_mul_of_one_le_right (by positivity) hX
    have h3 : CKc * lam ^ 4 ≤ CKc * lam ^ 4 * X := le_mul_of_one_le_right (by positivity) hX
    nlinarith only [hA, hB, hC, h2, h3]
  have hl40 : 0 ≤ lam ^ 4 := by positivity
  have hX0 : 0 ≤ X := by linarith only [hX]
  have hπ : 0 ≤ 1 / √π := by positivity
  apply le_trans hb
  apply key
  · -- the steepest-descent error
    have hsd : sdC CQ CE CB Cm s1 Cend (3 * s1) ‖Complex.I * (hh : ℂ)‖ ‖(psi : ℂ)‖ ≤ Sd :=
      sdC_mono hCQ hCE hCB hCm0 hCU (by positivity) (norm_nonneg _) (norm_nonneg _)
        (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hpsiB)
    have hP : |1 + lam ^ 3 * (-psi * q0c - 3 / 2 * hh)| ≤ CP := by
      have h3 : lam ^ 3 ≤ 1 := pow_le_one₀ hlam.le hlam1
      have h4 : |-psi * q0c - 3 / 2 * hh| ≤ Cψ * |q0c| + 3 / 2 * |hh| := by
        calc |-psi * q0c - 3 / 2 * hh| ≤ |-psi * q0c| + |3 / 2 * hh| := abs_sub _ _
          _ = |psi| * |q0c| + 3 / 2 * |hh| := by
            rw [abs_mul, abs_neg, abs_mul]; norm_num
          _ ≤ Cψ * |q0c| + 3 / 2 * |hh| := by
            have := mul_le_mul_of_nonneg_right hpsiB (abs_nonneg q0c); linarith only [this]
      calc |1 + lam ^ 3 * (-psi * q0c - 3 / 2 * hh)| ≤ |(1 : ℝ)| + |lam ^ 3 * (-psi * q0c - 3 / 2 * hh)| := abs_add_le _ _
        _ = 1 + lam ^ 3 * |-psi * q0c - 3 / 2 * hh| := by
          rw [abs_one, abs_mul, abs_of_pos (by positivity : 0 < lam ^ 3)]
        _ ≤ 1 + 1 * (Cψ * |q0c| + 3 / 2 * |hh|) := by
          have := mul_le_mul h3 h4 (abs_nonneg _) zero_le_one
          linarith only [this]
        _ = CP := by rw [hCP]; ring
    have hl2 : lam ^ 2 ≤ 1 := pow_le_one₀ hlam.le hlam1
    have t1 : sdC CQ CE CB Cm s1 Cend (3 * s1) ‖Complex.I * (hh : ℂ)‖ ‖(psi : ℂ)‖ * lam ^ 4 * X ≤ Sd * lam ^ 4 * X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsd hl40) hX0
    have t2 : |1 + lam ^ 3 * (-psi * q0c - 3 / 2 * hh)| * (144 * Real.exp (-((rr ^ 2) ^ 3 / 12))) ≤
        CP * (144 * (C6a * lam ^ 4)) :=
      mul_le_mul hP (mul_le_mul_of_nonneg_left hEb (by norm_num)) (by positivity) hCP0
    have t3 : lam ^ 2 * |q0c| * (288 * Real.exp (-((rr ^ 2) ^ 3 / 12))) ≤ |q0c| * (288 * (C6a * lam ^ 4)) := by
      have h1 : 288 * Real.exp (-((rr ^ 2) ^ 3 / 12)) ≤ 288 * (C6a * lam ^ 4) :=
        mul_le_mul_of_nonneg_left hEb (by norm_num)
      calc lam ^ 2 * |q0c| * (288 * Real.exp (-((rr ^ 2) ^ 3 / 12))) ≤ 1 * |q0c| * (288 * Real.exp (-((rr ^ 2) ^ 3 / 12))) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl2 (abs_nonneg _)) (by positivity)
        _ ≤ |q0c| * (288 * (C6a * lam ^ 4)) := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have hAX : lam ^ 4 ≤ lam ^ 4 * X := le_mul_of_one_le_right hl40 hX
    have inner : sdC CQ CE CB Cm s1 Cend (3 * s1) ‖Complex.I * (hh : ℂ)‖ ‖(psi : ℂ)‖ * lam ^ 4 * X +
        |1 + lam ^ 3 * (-psi * q0c - 3 / 2 * hh)| * (144 * Real.exp (-((rr ^ 2) ^ 3 / 12))) +
        lam ^ 2 * |q0c| * (288 * Real.exp (-((rr ^ 2) ^ 3 / 12))) ≤
        (Sd + CP * 144 * C6a + |q0c| * 288 * C6a) * lam ^ 4 * X := by
      have u2 : CP * (144 * (C6a * lam ^ 4)) ≤ CP * 144 * C6a * (lam ^ 4 * X) := by
        have := mul_le_mul_of_nonneg_left hAX (by positivity : 0 ≤ CP * 144 * C6a)
        linarith only [this]
      have u3 : |q0c| * (288 * (C6a * lam ^ 4)) ≤ |q0c| * 288 * C6a * (lam ^ 4 * X) := by
        have := mul_le_mul_of_nonneg_left hAX (by positivity : 0 ≤ |q0c| * 288 * C6a)
        linarith only [this]
      nlinarith only [t1, t2, t3, u2, u3]
    rw [hCKa]
    calc _ ≤ (1 / √π) * ((Sd + CP * 144 * C6a + |q0c| * 288 * C6a) * lam ^ 4 * X) :=
          mul_le_mul_of_nonneg_left inner hπ
      _ = _ := by ring
  · -- the cutoff term
    generalize hCgdef : 2 * (CB * (1 + CE * (3 * s1)) * Real.exp (|psi| * (3 * s1))) = Cg at hCg hCg0 ⊢
    have hb1 : 16 * Cg / rr ^ 3 ≤ 16 * Cg := by
      rw [show 16 * Cg / rr ^ 3 = 16 * Cg * (1 / rr ^ 3) by ring]
      exact mul_le_of_le_one_right (mul_nonneg (by norm_num) hCg0) hrr3
    have hb2 : 1024 * Cg / rr ^ 9 ≤ 1024 * Cg := by
      rw [show 1024 * Cg / rr ^ 9 = 1024 * Cg * (1 / rr ^ 9) by ring]
      exact mul_le_of_le_one_right (mul_nonneg (by norm_num) hCg0) hrr9'
    have hb3 : 320000 * Cg / rr ^ 9 ≤ 320000 * Cg * (lam ^ 4 / s1 ^ 4) := by
      rw [show 320000 * Cg / rr ^ 9 = 320000 * Cg * (1 / rr ^ 9) by ring]
      exact mul_le_mul_of_nonneg_left hrr9 (mul_nonneg (by norm_num) hCg0)
    have hb4 : (16 * Cg / rr ^ 3 + 1024 * Cg / rr ^ 9) * Real.exp (-((rr ^ 2) ^ 3 / 4)) ≤
        (16 * Cg + 1024 * Cg) * (C6a * lam ^ 4) :=
      mul_le_mul (add_le_add hb1 hb2) hE4b hE40 (by positivity)
    have hb5 : (16 * Cg + 1024 * Cg) * (C6a * lam ^ 4) ≤ (16 * (2 * Cb0) + 1024 * (2 * Cb0)) * (C6a * lam ^ 4) :=
      mul_le_mul_of_nonneg_right (by linarith only [hCg]) (by positivity)
    have hb6 : 320000 * Cg * (lam ^ 4 / s1 ^ 4) ≤ 320000 * (2 * Cb0) / s1 ^ 4 * lam ^ 4 := by
      have : 320000 * Cg * (lam ^ 4 / s1 ^ 4) = 320000 * Cg / s1 ^ 4 * lam ^ 4 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith only [hCg]) (by positivity)) hl40
    rw [hCKb]
    calc _ ≤ (1 / √π) * ((16 * (2 * Cb0) + 1024 * (2 * Cb0)) * (C6a * lam ^ 4) + 320000 * (2 * Cb0) / s1 ^ 4 * lam ^ 4) :=
          mul_le_mul_of_nonneg_left (by linarith only [hb3, hb4, hb5, hb6]) hπ
      _ = _ := by ring
  · -- the tail term
    have hT := hτ1
    have hKB : 0 ≤ Real.sqrt (π * c / 12) * CA := by positivity
    have hV : (2 / 9) * (Treal β s1) ^ (-9 / 2 : ℝ) + (2 / 3) * (Treal β s1) ^ (-3 / 2 : ℝ) ≤
        (2 / 9) * τs ^ (-9 / 2 : ℝ) + (2 / 3) * τs ^ (-3 / 2 : ℝ) := by
      have e1 : (Treal β s1) ^ (-9 / 2 : ℝ) ≤ τs ^ (-9 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hτs hT (by norm_num)
      have e2 : (Treal β s1) ^ (-3 / 2 : ℝ) ≤ τs ^ (-3 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hτs hT (by norm_num)
      linarith only [e1, e2]
    have hsc : Real.sqrt (π * c / 12) = Real.sqrt (π / 12) * Real.sqrt c := by
      rw [show π * c / 12 = π / 12 * c by ring, Real.sqrt_mul (by positivity)]
    set W : ℝ := 4 * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) / γ ^ 2 with hW
    have hW0 : 0 ≤ W := by rw [hW]; positivity
    set V : ℝ := (2 / 9) * τs ^ (-9 / 2 : ℝ) + (2 / 3) * τs ^ (-3 / 2 : ℝ) with hVdef
    have hV0 : 0 ≤ V := by rw [hVdef]; positivity
    have hlhs : 4 * (Real.sqrt (π * c / 12) * CA) * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) / γ ^ 2 =
        Real.sqrt (π * c / 12) * CA * W := by rw [hW]; ring
    rw [hlhs, hlc6, hsc]
    have hmain : (Real.sqrt (π / 12) * Real.sqrt c * CA * W) *
        ((2 / 9) * (Treal β s1) ^ (-9 / 2 : ℝ) + (2 / 3) * (Treal β s1) ^ (-3 / 2 : ℝ)) ≤
        (Real.sqrt (π / 12) * Real.sqrt c * CA * W) * V :=
      mul_le_mul_of_nonneg_left hV (by positivity)
    have hfin : lam ^ 6 * ((Real.sqrt (π / 12) * Real.sqrt c * CA * W) * V) ≤ CKc * lam ^ 4 := by
      have e : lam ^ 6 * ((Real.sqrt (π / 12) * Real.sqrt c * CA * W) * V) =
          (Real.sqrt c * lam ^ 2) * (CKc * lam ^ 4) := by rw [hCKc]; ring
      rw [e]
      calc (Real.sqrt c * lam ^ 2) * (CKc * lam ^ 4) ≤ 1 * (CKc * lam ^ 4) :=
            mul_le_mul_of_nonneg_right hsqc (by positivity)
        _ = _ := one_mul _
    exact le_trans (mul_le_mul_of_nonneg_left hmain (by positivity)) hfin

/-- info: 'FormalResearch.SignUncertainty.CtSd.cfu_K_airy_beta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cfu_K_airy_beta

end FormalResearch.SignUncertainty.CtSd
