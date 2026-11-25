module

public import FormalResearch.SignUncertainty.CtOuterBandGlue

/-!
# `ct:cfu` (2): the outer-band asymptotics of `K_ε`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` (2), `(ct:K-outer)`, Step 4.  **Proved** for
`μ₀ ≥ M₀` (a fixed large constant).

`K_ε(ξ;c) = -√(πc/12) Re ∫₀^∞ A_ε(τ) e^{-icΦ(τ;L)} dτ` with `Φ(τ;L) = Lτ - ∫₀^τ m`, `A_ε = √(6m'/π²) e^{i(π/4+θ_ε)} e^{-B_c(iτ)}`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOsc

open CtOuter

/-- `ϕ_{τ₀}(τ) = ∫₀^τ m - m(τ₀) τ = -Φ(τ; m(τ₀))`. -/
noncomputable def phaseP (τ0 τ : ℝ) : ℝ := (∫ u in (0 : ℝ)..τ, hankelEdgeM u) - hankelEdgeM τ0 * τ

lemma hasDerivAt_phaseP (τ0 : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (phaseP τ0) (hankelEdgeM τ - hankelEdgeM τ0) τ := by
  have hc : ContinuousOn hankelEdgeM (Ici 0) := hankelEdgeM_continuousOn
  have hint : IntervalIntegrable hankelEdgeM volume 0 τ :=
    (hc.mono (fun x hx => by rw [uIcc_of_le hτ.le] at hx; exact hx.1)).intervalIntegrable
  have h1 : HasDerivAt (fun τ => ∫ u in (0 : ℝ)..τ, hankelEdgeM u) (hankelEdgeM τ) τ := by
    refine intervalIntegral.integral_hasDerivAt_right hint ?_ ?_
    · exact (hc.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi τ hτ
    · exact hc.continuousAt (Ici_mem_nhds hτ)
  exact h1.sub ((hasDerivAt_id τ).const_mul (hankelEdgeM τ0)) |>.congr_deriv (by simp)

lemma exp_pi_div_two : Complex.exp ((π : ℂ) / 2 * Complex.I) = Complex.I := by
  rw [Complex.exp_mul_I]
  have h1 : Complex.cos ((π : ℂ) / 2) = 0 := by
    have := Complex.cos_pi_div_two; simpa using this
  have h2 : Complex.sin ((π : ℂ) / 2) = 1 := by
    have := Complex.sin_pi_div_two; simpa using this
  rw [h1, h2]; ring

/-- Algebra of the leading term: `√(πc/12) · e^{iπ/4}√(2π/(c m')) A(τ₀) e^{icϕ(τ₀)} = i e^{-B} e^{iY}`. -/
lemma lead_alg {ε c τ0 : ℝ} (hc : 0 < c) (hm : 0 < iteratedDeriv 1 hankelEdgeM τ0) :
    ((Real.sqrt (π * c / 12) : ℝ) : ℂ) *
      (Complex.exp ((π : ℂ) / 4 * Complex.I) * ((Real.sqrt (2 * π / (c * iteratedDeriv 1 hankelEdgeM τ0)) : ℝ) : ℂ) *
        outerAmp ε c τ0 * Complex.exp (Complex.I * c * (phaseP τ0 τ0 : ℂ))) =
      Complex.I * Complex.exp (-(FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ0 : ℂ)))) *
        Complex.exp (Complex.I * ((CtOuter.outerTheta ε τ0 + c * phaseP τ0 τ0 : ℝ) : ℂ)) := by
  have hpi := Real.pi_pos
  set m1v := iteratedDeriv 1 hankelEdgeM τ0 with hm1v
  have hs : Real.sqrt (π * c / 12) * Real.sqrt (2 * π / (c * m1v)) * sqf (iteratedDeriv 1 hankelEdgeM) τ0 = 1 := by
    unfold sqf
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    have : π * c / 12 * (2 * π / (c * m1v)) * (6 / π ^ 2 * m1v) = 1 := by field_simp; ring
    rw [this, Real.sqrt_one]
  unfold outerAmp ampExp
  set β0 := FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ0 : ℂ)) with hβ0
  have e1 : Complex.exp ((π : ℂ) / 4 * Complex.I) * Complex.exp (Complex.I * ((π / 4 + CtOuter.outerTheta ε τ0 : ℝ) : ℂ) - β0) *
      Complex.exp (Complex.I * c * (phaseP τ0 τ0 : ℂ)) =
      Complex.I * Complex.exp (-β0) * Complex.exp (Complex.I * ((CtOuter.outerTheta ε τ0 + c * phaseP τ0 τ0 : ℝ) : ℂ)) := by
    calc _ = Complex.exp ((π : ℂ) / 4 * Complex.I + (Complex.I * ((π / 4 + CtOuter.outerTheta ε τ0 : ℝ) : ℂ) - β0) +
          Complex.I * c * (phaseP τ0 τ0 : ℂ)) := by rw [Complex.exp_add, Complex.exp_add]
      _ = Complex.exp ((π : ℂ) / 2 * Complex.I + -β0 + Complex.I * ((CtOuter.outerTheta ε τ0 + c * phaseP τ0 τ0 : ℝ) : ℂ)) := by
          congr 1; push_cast; ring
      _ = _ := by rw [Complex.exp_add, Complex.exp_add, exp_pi_div_two]
  have hcast : ((Real.sqrt (π * c / 12) : ℝ) : ℂ) * ((Real.sqrt (2 * π / (c * m1v)) : ℝ) : ℂ) *
      ((sqf (iteratedDeriv 1 hankelEdgeM) τ0 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hs]; simp
  calc _ = (((Real.sqrt (π * c / 12) : ℝ) : ℂ) * ((Real.sqrt (2 * π / (c * m1v)) : ℝ) : ℂ) *
        ((sqf (iteratedDeriv 1 hankelEdgeM) τ0 : ℝ) : ℂ)) *
        (Complex.exp ((π : ℂ) / 4 * Complex.I) * Complex.exp (Complex.I * ((π / 4 + CtOuter.outerTheta ε τ0 : ℝ) : ℂ) - β0) *
          Complex.exp (Complex.I * c * (phaseP τ0 τ0 : ℂ))) := by ring
    _ = _ := by rw [hcast, one_mul, e1]

lemma re_I_exp (Y : ℝ) : (Complex.I * Complex.exp (Complex.I * (Y : ℂ))).re = -Real.sin Y := by
  rw [mul_comm Complex.I (Y : ℂ), Complex.exp_mul_I]
  simp [Complex.sin_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_im, Complex.cos_ofReal_re]

lemma re_lead_close {β0 : ℂ} (hβ : ‖β0‖ ≤ 1) (Y : ℝ) :
    |(Complex.I * Complex.exp (-β0) * Complex.exp (Complex.I * (Y : ℂ))).re + Real.sin Y| ≤ 2 * ‖β0‖ := by
  have h1 : (Complex.I * Complex.exp (Complex.I * (Y : ℂ))).re = -Real.sin Y := re_I_exp Y
  have e : (Complex.I * Complex.exp (-β0) * Complex.exp (Complex.I * (Y : ℂ))).re + Real.sin Y =
      (Complex.I * Complex.exp (Complex.I * (Y : ℂ)) * (Complex.exp (-β0) - 1)).re := by
    have : Complex.I * Complex.exp (-β0) * Complex.exp (Complex.I * (Y : ℂ)) =
        Complex.I * Complex.exp (Complex.I * (Y : ℂ)) * (Complex.exp (-β0) - 1) +
          Complex.I * Complex.exp (Complex.I * (Y : ℂ)) := by ring
    rw [this, Complex.add_re, h1]; ring
  rw [e]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
  have hn : ‖Complex.exp (Complex.I * (Y : ℂ))‖ = 1 := by
    rw [show Complex.I * (Y : ℂ) = ((Y : ℂ)) * Complex.I by ring, Complex.norm_exp_ofReal_mul_I]
  rw [hn, one_mul]
  have := Complex.norm_exp_sub_one_le (x := -β0) (by rwa [norm_neg])
  rwa [norm_neg] at this

/-- **`ct:cfu` (2)**, in terms of the saddle `τ₀` (`m(τ₀) = L`): for `c ≥ 2` and `c · min(1, τ₀³) ≥ M₀` the improper
integral `I = ∫₀^∞ A_ε e^{-icΦ}` exists and `K = -√(πc/12) Re I = -sin(cΦ(τ₀) - θ_ε(τ₀)) + O(1/(c min(1,τ₀³)))`,
where `Φ(τ₀) = -phaseP τ₀ τ₀ = L τ₀ - ∫₀^{τ₀} m`. -/
theorem ct_cfu_outer_tau {ε : ℝ} (hε : ε = -1 ∨ ε = 1) :
    ∃ M0 K : ℝ, 0 < M0 ∧ 0 ≤ K ∧ ∀ {c τ0 : ℝ}, 2 ≤ c → 0 < τ0 → M0 ≤ c * min 1 (τ0 ^ 3) →
      ∃ I : ℂ, Tendsto (fun T : ℝ => ∫ τ in (0 : ℝ)..T,
          outerAmp ε c τ * Complex.exp (Complex.I * c * (phaseP τ0 τ : ℂ))) atTop (𝓝 I) ∧
        |(-Real.sqrt (π * c / 12) * I.re) -
            (-Real.sin (c * (-phaseP τ0 τ0) - CtOuter.outerTheta ε τ0))| ≤ K / (c * min 1 (τ0 ^ 3)) := by
  obtain ⟨C0, hC0, hMd⟩ := mdata_hankel
  obtain ⟨CA, hCA, hAmp⟩ := outerAmp_ampBd hε
  obtain ⟨M0, K', hM0, hK', H⟩ := outer_band C0 CA hC0 hCA
  have hpi := Real.pi_pos
  refine ⟨M0, Real.sqrt (π / 12) * K' + 1 / 3, hM0, by positivity, fun {c τ0} hc2 hτ0 hlarge => ?_⟩
  have hc : 0 < c := by linarith
  obtain ⟨A1, A2, hA⟩ := hAmp c hc2
  obtain ⟨I, hI, hIb⟩ := H hMd hA hτ0 hc (fun τ hτ => hasDerivAt_phaseP τ0 hτ) hlarge
  refine ⟨I, hI, ?_⟩
  have hm1 : 0 < iteratedDeriv 1 hankelEdgeM τ0 := by
    rw [iteratedDeriv_one_m hτ0]; exact (mPrime_bounds hτ0).1.trans_lt' (by positivity) |>.trans_le le_rfl
  set lead := Complex.exp ((π : ℂ) / 4 * Complex.I) *
      ((Real.sqrt (2 * π / (c * iteratedDeriv 1 hankelEdgeM τ0)) : ℝ) : ℂ) * outerAmp ε c τ0 *
        Complex.exp (Complex.I * c * (phaseP τ0 τ0 : ℂ)) with hlead
  set s : ℝ := Real.sqrt (π * c / 12) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  set β0 := FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ0 : ℂ)) with hβ0
  have hβn : ‖β0‖ ≤ 1 / (6 * c) := Asymptotics.binetDiff_norm_le_left hc (by simp)
  have hβ1 : ‖β0‖ ≤ 1 := hβn.trans (by rw [div_le_one (by positivity)]; linarith)
  have hkey := lead_alg (ε := ε) hc hm1
  set Y : ℝ := CtOuter.outerTheta ε τ0 + c * phaseP τ0 τ0 with hY
  have hclose := re_lead_close hβ1 Y
  -- Re (s * lead) ≈ -sin Y
  have hre1 : |((s : ℂ) * lead).re + Real.sin Y| ≤ 2 * ‖β0‖ := by rw [hlead, hs, hkey]; exact hclose
  have hre2 : |s * I.re - ((s : ℂ) * lead).re| ≤ s * (K' / (c * Real.sqrt c * min 1 (τ0 ^ 3))) := by
    have h1 : s * I.re - ((s : ℂ) * lead).re = ((s : ℂ) * (I - lead)).re := by
      rw [mul_sub, Complex.sub_re]; simp
    rw [h1]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    exact mul_le_mul_of_nonneg_left hIb hs0.le
  have hX : c * (-phaseP τ0 τ0) - CtOuter.outerTheta ε τ0 = -Y := by rw [hY]; ring
  rw [hX, Real.sin_neg]
  have hmin0 : 0 < min 1 (τ0 ^ 3) := lt_min one_pos (pow_pos hτ0 3)
  have hmin1 : min 1 (τ0 ^ 3) ≤ 1 := min_le_left _ _
  have e1 : (-s * I.re) - (-(-Real.sin Y)) = -(s * I.re - (-Real.sin Y)) := by ring
  rw [show -s * I.re = -(s * I.re) by ring, show -(-Real.sin Y) = Real.sin Y by ring]
  have h3 : |-(s * I.re) - Real.sin Y| = |s * I.re + Real.sin Y| := by
    rw [show -(s * I.re) - Real.sin Y = -(s * I.re + Real.sin Y) by ring, abs_neg]
  rw [h3]
  have h4 : |s * I.re + Real.sin Y| ≤ |s * I.re - ((s : ℂ) * lead).re| + |((s : ℂ) * lead).re + Real.sin Y| := by
    have := abs_add_le (s * I.re - ((s : ℂ) * lead).re) (((s : ℂ) * lead).re + Real.sin Y)
    rwa [show s * I.re - ((s : ℂ) * lead).re + (((s : ℂ) * lead).re + Real.sin Y) = s * I.re + Real.sin Y by ring] at this
  refine h4.trans ?_
  -- the two error terms
  have t1 : s * (K' / (c * Real.sqrt c * min 1 (τ0 ^ 3))) = Real.sqrt (π / 12) * K' / (c * min 1 (τ0 ^ 3)) := by
    have hsc : s = Real.sqrt (π / 12) * Real.sqrt c := by
      rw [hs, ← Real.sqrt_mul (by positivity)]; congr 1; ring
    have hsq : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
    rw [hsc]; field_simp
  have t2 : 2 * ‖β0‖ ≤ 1 / 3 / (c * min 1 (τ0 ^ 3)) := by
    have : 2 * ‖β0‖ ≤ 1 / (3 * c) := by
      calc 2 * ‖β0‖ ≤ 2 * (1 / (6 * c)) := by linarith
        _ = 1 / (3 * c) := by field_simp; ring
    refine this.trans ?_
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hc hmin0]
  calc _ ≤ Real.sqrt (π / 12) * K' / (c * min 1 (τ0 ^ 3)) + 1 / 3 / (c * min 1 (τ0 ^ 3)) := by
        linarith [hre2, hre1, t1, t2]
    _ = _ := by ring

/-- `m(τ) ≤ C₀ τ²` (from `m' ≤ C₀ τ` and `m(0) = 0`). -/
lemma m_le_sq {C0 : ℝ} {m1 m2 m3 : ℝ → ℝ} (hM : MData C0 hankelEdgeM m1 m2 m3) {τ : ℝ} (hτ : 0 < τ) :
    hankelEdgeM τ ≤ C0 * τ ^ 2 := by
  have hcont : ContinuousOn (fun u => C0 * u ^ 2 - hankelEdgeM u) (Ici 0) :=
    (continuousOn_const.mul (continuousOn_id.pow 2)).sub hankelEdgeM_continuousOn
  have hmono : MonotoneOn (fun u => C0 * u ^ 2 - hankelEdgeM u) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont ?_ ?_
    · rw [interior_Ici]
      intro u hu
      have hu' : 0 < u := hu
      exact (((hasDerivAt_pow 2 u).const_mul C0).sub (hM.d0 u hu')).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro u hu
      have hu' : 0 < u := hu
      rw [((((hasDerivAt_pow 2 u).const_mul C0).fun_sub (hM.d0 u hu'))).deriv]
      have h1 := hM.hi u hu'
      have h2 : C0 * (u / (1 + u ^ 2)) ≤ C0 * u := mul_le_mul_of_nonneg_left
        (div_le_self hu'.le (by nlinarith [sq_nonneg u])) hM.C0nn
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      nlinarith [mul_nonneg hM.C0nn hu'.le]
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hτ.le) hτ.le
  simp only [hankelEdgeM_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero] at this
  linarith

/-- **`ct:cfu` (2)** in the paper's variables: `L = log(π²ξ) > 0`, `μ₀ = c min(1, L^{3/2})`. -/
theorem ct_cfu_outer {ε : ℝ} (hε : ε = -1 ∨ ε = 1) :
    ∃ M K : ℝ, 0 < M ∧ 0 ≤ K ∧ ∀ {c L : ℝ}, 2 ≤ c → 0 < L → M ≤ c * min 1 (L * Real.sqrt L) →
      ∃ τ0 : ℝ, 0 < τ0 ∧ hankelEdgeM τ0 = L ∧ ∃ I : ℂ,
        Tendsto (fun T : ℝ => ∫ τ in (0 : ℝ)..T,
          outerAmp ε c τ * Complex.exp (Complex.I * c * (phaseP τ0 τ : ℂ))) atTop (𝓝 I) ∧
        |(-Real.sqrt (π * c / 12) * I.re) -
            (-Real.sin (c * (-phaseP τ0 τ0) - CtOuter.outerTheta ε τ0))| ≤ K / (c * min 1 (L * Real.sqrt L)) := by
  obtain ⟨C0, hC0, hMd⟩ := mdata_hankel
  obtain ⟨M0, K, hM0, hK, H⟩ := ct_cfu_outer_tau hε
  set κ : ℝ := max 1 (C0 * Real.sqrt C0) with hκ
  have hκ1 : 1 ≤ κ := le_max_left _ _
  refine ⟨M0 * κ, K * κ, by positivity, by positivity, fun {c L} hc2 hL hlarge => ?_⟩
  have hc : 0 < c := by linarith
  obtain ⟨τ0, hτ0, hmτ⟩ := hankelEdgeM_exists_root hL.le
  have hτ0p : 0 < τ0 := by
    rcases hτ0.eq_or_lt with h | h
    · rw [← h, hankelEdgeM_zero] at hmτ; linarith
    · exact h
  have hLle : L ≤ C0 * τ0 ^ 2 := by rw [← hmτ]; exact m_le_sq hMd hτ0p
  have hsq : L * Real.sqrt L ≤ (C0 * Real.sqrt C0) * τ0 ^ 3 := by
    have h1 : Real.sqrt L ≤ Real.sqrt C0 * τ0 := by
      calc Real.sqrt L ≤ Real.sqrt (C0 * τ0 ^ 2) := Real.sqrt_le_sqrt hLle
        _ = Real.sqrt C0 * τ0 := by rw [Real.sqrt_mul hC0.le, Real.sqrt_sq hτ0p.le]
    calc L * Real.sqrt L ≤ (C0 * τ0 ^ 2) * (Real.sqrt C0 * τ0) :=
          mul_le_mul hLle h1 (Real.sqrt_nonneg _) (by positivity)
      _ = (C0 * Real.sqrt C0) * τ0 ^ 3 := by ring
  have hmin : min 1 (L * Real.sqrt L) ≤ κ * min 1 (τ0 ^ 3) := by
    rcases le_total 1 (τ0 ^ 3) with h | h
    · rw [min_eq_left h, mul_one]; exact (min_le_left _ _).trans hκ1
    · rw [min_eq_right h]
      refine (min_le_right _ _).trans (hsq.trans ?_)
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hτ0p.le 3)
  have hmL : 0 < min 1 (L * Real.sqrt L) := lt_min one_pos (by positivity)
  have hm0 : 0 < min 1 (τ0 ^ 3) := lt_min one_pos (pow_pos hτ0p 3)
  have hκ0 : 0 < κ := by linarith
  have hbig : M0 ≤ c * min 1 (τ0 ^ 3) := by
    have h1 : c * min 1 (L * Real.sqrt L) ≤ c * (κ * min 1 (τ0 ^ 3)) := mul_le_mul_of_nonneg_left hmin hc.le
    have h2 : M0 * κ ≤ c * (κ * min 1 (τ0 ^ 3)) := hlarge.trans h1
    have h3 : M0 * κ ≤ (c * min 1 (τ0 ^ 3)) * κ := by linarith
    exact le_of_mul_le_mul_right h3 hκ0
  obtain ⟨I, hI, hb⟩ := H hc2 hτ0p hbig
  refine ⟨τ0, hτ0p, hmτ, I, hI, hb.trans ?_⟩
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_left hmin (by positivity : (0 : ℝ) ≤ K * c)
  nlinarith [this]

/-- info: 'FormalResearch.SignUncertainty.CtOsc.ct_cfu_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_cfu_outer

/-- info: 'FormalResearch.SignUncertainty.CtOsc.ct_cfu_outer_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_cfu_outer_tau

end FormalResearch.SignUncertainty.CtOsc
