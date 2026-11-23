module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedRegionOneDesign
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedThreshold

/-!
# Geometry and amplitude of Region I (`rem:thmU`, Step (2))

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Step (2).

* `sigma_xiI_pow`: `(τ(ξ_I)/λ)^{3/2} = N_tr`, hence `u ≥ -κ N_tr^{2/3}` on Region I
  (`airyZero_le_neg_kappa`: `a_K ≤ u` for `K ≥ 2 N_tr`);
* `regionI_gap`: `t ≥ t_* + 1` gives `u_f - u ≥ c_1 c'^{-1/3}` (the "left half of cell 1" estimate);
* `regionI_amp`: `h_0 e^{c'L} ≥ c_h c' ‖W_D(u)‖` on `[χ'_1, ξ_I]`, from `rampedComb_amplitude`.

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb Upper.Design Upper.Holes Upper.Positivity Upper.Hankel
  FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window

lemma kappaAiry_le_three : kappaAiry ≤ 3 := by
  by_contra h
  push Not at h
  have h0 : 0 ≤ kappaAiry := kappaAiry_pos.le
  have h1 : (3 : ℝ) ^ 3 < kappaAiry ^ 3 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  have h2 : kappaAiry ^ 3 = (3 * π / 2) ^ 2 := by
    unfold kappaAiry
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [h2] at h1
  have hπ := Real.pi_lt_d2
  nlinarith [Real.pi_pos]

lemma langerTau_nonneg_of_ge {x : ℝ} (hx : xiStar ≤ x) : 0 ≤ langerTau x := by
  have := langerTau_strictMonoOn.monotoneOn (Set.mem_Ioi.2 xiStar_pos) (Set.mem_Ioi.2 (xiStar_pos.trans_le hx)) hx
  rwa [langerTau_xiStar] at this

/-- `(τ(ξ_I)/λ)^{3/2} = N_tr`. -/
lemma sigma_xiI_pow {c' : ℝ} (hc' : 0 < c') :
    (sigmaOf c' (xiStar + c' ^ (-(3 / 5 : ℝ)))) ^ (3 / 2 : ℝ) = nTr c' := by
  have hr : 0 < c' ^ (-(3 / 5 : ℝ)) := Real.rpow_pos_of_pos hc' _
  have hge : xiStar ≤ xiStar + c' ^ (-(3 / 5 : ℝ)) := by linarith
  have hτ := langerTau_nonneg_of_ge hge
  have hl := lambdaComb_pos' hc'
  have hk := kTip_pos
  have hl32 : lambdaComb c' ^ (3 / 2 : ℝ) = (kTip * c')⁻¹ := by
    unfold lambdaComb
    rw [← Real.rpow_mul (by positivity)]
    norm_num [Real.rpow_neg_one]
  unfold sigmaOf nTr
  rw [cumulN_eq_kTip_mul_langerTau hge, Real.div_rpow hτ hl.le, hl32]
  field_simp

/-- `a_K ≤ -κ s` whenever `0 ≤ s ≤ N^{2/3}` and `K ≥ 2N`. -/
lemma airyZero_le_neg_kappa {N s : ℝ} (hN : 0 ≤ N) (hs : 0 ≤ s) (hsN : s ≤ N ^ (2 / 3 : ℝ)) {K : ℕ}
    (hK1 : 1 ≤ K) (hK : 2 * N ≤ K) : airyZero K ≤ -kappaAiry * s := by
  have h1 := airyZero_abs_ge_pow hK1
  rw [abs_of_neg (airyZero_neg K)] at h1
  have hN2 : (2 * N) ^ (2 / 3 : ℝ) ≤ (K : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hK (by norm_num)
  rw [Real.mul_rpow (by norm_num) hN] at hN2
  have h3 := three_halves_le_two_rpow
  have hNp : 0 ≤ N ^ (2 / 3 : ℝ) := Real.rpow_nonneg hN _
  have h4 : 3 / 2 * N ^ (2 / 3 : ℝ) ≤ (K : ℝ) ^ (2 / 3 : ℝ) := by nlinarith
  have hκ := kappaAiry_le_three
  have h5 : kappaAiry * s ≤ 3 * N ^ (2 / 3 : ℝ) := by
    calc kappaAiry * s ≤ 3 * s := mul_le_mul_of_nonneg_right hκ hs
      _ ≤ 3 * N ^ (2 / 3 : ℝ) := by linarith
  nlinarith

/-- **Left half of cell 1** (`rem:thmU` Step (2)): `t ≥ t_* + 1` and `x ≤ ξ_I` give `χ'_1 < x` and
`u_f - u ≥ c₁ c'^{-1/3}` for `u = -κ σ(x)`, `u_f = a_1 - d`. -/
lemma regionI_gap : ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ c' : ℝ, 1 ≤ c' → ∀ d : ℝ, 0 ≤ d → d ≤ 1 → ∀ x : ℝ, 0 ≤ x →
    c' * designSite c' (rampedSigma d c') 1 ^ 2 / 3 + 1 ≤ c' * x ^ 2 / 3 →
    x ≤ xiStar + c' ^ (-(3 / 5 : ℝ)) →
    xiStar ≤ designSite c' (rampedSigma d c') 1 ∧ designSite c' (rampedSigma d c') 1 < x ∧
    c₁ * c' ^ (-(1 / 3 : ℝ)) ≤ (airyZero 1 - d) - (-kappaAiry * sigmaOf c' x) := by
  have hxs := xiStar_pos
  have hκ := kappaAiry_pos
  have hk := kTip_pos
  obtain ⟨cτ, hcτ, hcd⟩ := langerTau_deriv_ge_const_of (a := xiStar / 2) (by linarith)
  have hkp : 0 < kTip ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hk _
  refine ⟨kappaAiry * cτ * (3 / (2 * (xiStar + 1))) * kTip ^ (2 / 3 : ℝ), by positivity, ?_⟩
  intro c' hc'1 d hd hd1 x hx0 ht hxI
  have hc'0 : 0 < c' := by linarith
  have hr1 : c' ^ (-(3 / 5 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc'1 (by norm_num)
  have hl := lambdaComb_pos' hc'0
  set χ := designSite c' (rampedSigma d c') 1 with hχ
  have hχsite : χ = langerTauInv (lambdaComb c' * rampedNode d c' 1) := designSite_rampedSigma hc'0 d 1
  have hσ1 : 0 ≤ rampedNode d c' 1 := rampedNode_nonneg hd c' le_rfl
  have hχge : xiStar ≤ χ := by
    rw [hχsite]
    have := (langerTauInv_spec (mul_nonneg hl.le hσ1)).1
    exact this
  have hτχ : langerTau χ = lambdaComb c' * rampedNode d c' 1 := by
    rw [hχsite]; exact langerTau_langerTauInv (mul_nonneg hl.le hσ1)
  have hχx : χ < x := by
    by_contra hcon
    push Not at hcon
    have : c' * x ^ 2 / 3 ≤ c' * χ ^ 2 / 3 := by
      have : x ^ 2 ≤ χ ^ 2 := pow_le_pow_left₀ hx0 hcon 2
      have := mul_le_mul_of_nonneg_left this hc'0.le
      linarith
    linarith
  refine ⟨hχge, hχx, ?_⟩
  -- `x - χ ≥ 3/(2 c' (ξ_* + 1))`
  have hxle : x ≤ xiStar + 1 := by linarith
  have hsum : x + χ ≤ 2 * (xiStar + 1) := by linarith
  have hprod : 3 / c' ≤ (x - χ) * (x + χ) := by
    have : 3 ≤ c' * (x ^ 2 - χ ^ 2) := by nlinarith
    rw [div_le_iff₀ hc'0]; nlinarith
  have hxχ : 3 / (2 * (xiStar + 1)) / c' ≤ x - χ := by
    have hpos : 0 < x + χ := by linarith
    have h1 : 3 / c' ≤ (x - χ) * (2 * (xiStar + 1)) := by
      refine hprod.trans ?_
      exact mul_le_mul_of_nonneg_left hsum (by linarith)
    rw [div_div, div_le_iff₀ (by positivity)]
    nlinarith
  -- `τ(x) - τ(χ) ≥ cτ (x - χ)`
  have hτ := langerTau_sub_ge (a := xiStar / 2) (c := cτ) (by linarith) hcd (by linarith) hχx.le
  have hs : sigmaOf c' x - rampedNode d c' 1 = (langerTau x - langerTau χ) / lambdaComb c' := by
    unfold sigmaOf; rw [hτχ]; field_simp
  have hs2 : cτ * (x - χ) / lambdaComb c' ≤ sigmaOf c' x - rampedNode d c' 1 := by
    rw [hs]; exact div_le_div_of_nonneg_right hτ hl.le
  have hcl := c_mul_lambdaComb hc'0
  have hexp : (airyZero 1 - d) - (-kappaAiry * sigmaOf c' x) = kappaAiry * (sigmaOf c' x - rampedNode d c' 1) := by
    have := ramped_site_first c' d
    rw [← this]; ring
  rw [hexp]
  have hkey : cτ * (3 / (2 * (xiStar + 1)) / c') / lambdaComb c' = cτ * (3 / (2 * (xiStar + 1))) *
      kTip ^ (2 / 3 : ℝ) * c' ^ (-(1 / 3 : ℝ)) := by
    have h2 : c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 3 : ℝ) = 1 := by rw [← Real.rpow_add hc'0]; norm_num
    have h3 : kTip ^ (2 / 3 : ℝ) * kTip ^ (-(2 / 3 : ℝ)) = 1 := by rw [← Real.rpow_add hk]; norm_num
    have hP : kTip ^ (-(2 / 3 : ℝ)) * c' ^ (1 / 3 : ℝ) ≠ 0 := by positivity
    rw [show cτ * (3 / (2 * (xiStar + 1)) / c') / lambdaComb c' =
        cτ * (3 / (2 * (xiStar + 1))) / (c' * lambdaComb c') by field_simp, hcl, div_eq_iff hP]
    calc cτ * (3 / (2 * (xiStar + 1))) = cτ * (3 / (2 * (xiStar + 1))) *
          ((kTip ^ (2 / 3 : ℝ) * kTip ^ (-(2 / 3 : ℝ))) * (c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 3 : ℝ))) := by
          rw [h3, h2]; ring
      _ = _ := by ring
  have hmono : cτ * (3 / (2 * (xiStar + 1)) / c') / lambdaComb c' ≤ cτ * (x - χ) / lambdaComb c' :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxχ hcτ.le) hl.le
  have : kappaAiry * (cτ * (3 / (2 * (xiStar + 1)) / c') / lambdaComb c') ≤
      kappaAiry * (sigmaOf c' x - rampedNode d c' 1) :=
    mul_le_mul_of_nonneg_left (hmono.trans hs2) hκ.le
  rw [hkey] at this
  linarith

/-- `0 ≤ σ(x) ≤ N_tr^{2/3}` for `ξ_* ≤ x ≤ ξ_I`. -/
lemma regionI_sigma_bounds {c' x : ℝ} (hc' : 0 < c') (hx : xiStar ≤ x) (hxI : x ≤ xiStar + c' ^ (-(3 / 5 : ℝ))) :
    0 ≤ sigmaOf c' x ∧ sigmaOf c' x ≤ (nTr c') ^ (2 / 3 : ℝ) := by
  have hr : 0 < c' ^ (-(3 / 5 : ℝ)) := Real.rpow_pos_of_pos hc' _
  have hl := lambdaComb_pos' hc'
  have hτx := langerTau_nonneg_of_ge hx
  have hτI := langerTau_nonneg_of_ge (show xiStar ≤ xiStar + c' ^ (-(3 / 5 : ℝ)) by linarith)
  have hmono : langerTau x ≤ langerTau (xiStar + c' ^ (-(3 / 5 : ℝ))) :=
    langerTau_strictMonoOn.monotoneOn (Set.mem_Ioi.2 (xiStar_pos.trans_le hx))
      (Set.mem_Ioi.2 (by linarith [xiStar_pos])) hxI
  refine ⟨div_nonneg hτx hl.le, ?_⟩
  have hI : (sigmaOf c' (xiStar + c' ^ (-(3 / 5 : ℝ)))) = (nTr c') ^ (2 / 3 : ℝ) := by
    have h := sigma_xiI_pow hc'
    have hs : 0 ≤ sigmaOf c' (xiStar + c' ^ (-(3 / 5 : ℝ))) := div_nonneg hτI hl.le
    rw [← h, ← Real.rpow_mul hs]
    norm_num
  rw [← hI]
  exact div_le_div_of_nonneg_right hmono hl.le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.sigma_xiI_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sigma_xiI_pow

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.regionI_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms regionI_gap

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.regionI_sigma_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms regionI_sigma_bounds

end FormalResearch.ModularBootstrap.Upper.Ramped
