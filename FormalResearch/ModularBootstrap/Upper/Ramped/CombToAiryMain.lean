module

public import FormalResearch.ModularBootstrap.Upper.Ramped.CombToAiry
public import FormalResearch.ModularBootstrap.Upper.Ramped.CombToAiryCont

/-!
# Proposition 1.2(2) (`rem:P1.2`) on the whole window, including the real zeros

`combToAiry_nonsite` gives the logarithmic identity off the sites `χ'_k`.  Both sides of the multiplicative form
`‖B_D(x)‖ e^{c'L(x)} = λ^{-3/2} e^{-(3/2)𝒦_*(x)} C_* κ ‖W_D(-κτ(x)/λ)‖ · e^{O(λ)}` are continuous in `x`
(`CombToAiryCont`), so the two-sided bound extends to the countable set of sites (`combToAiry_mult`).  The
logarithmic form at every `x` with `B_D(x) ≠ 0` (`combToAiry_log`), its `c'^{-2/3}` version
(`combToAiry_log_rate`) and the amplitude form of the Langer-window consumers (`combToAiry_amplitude`) follow.
-/

@[expose] public section

open Filter Topology Set Finset MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Window

/-- The left side `‖B_D(x)‖ e^{c'L(x)}`. -/
noncomputable def combAmp (c' : ℝ) (σ η : ℕ → ℝ) (x : ℝ) : ℝ :=
  ‖combBD c' σ η (x : ℂ)‖ * Real.exp (c' * slitL x)

/-- The Airy side `λ^{-3/2} e^{-(3/2)𝒦_*(x)} C_* κ ‖W_D(-κτ(x)/λ)‖`. -/
noncomputable def airyAmp (c' : ℝ) (σ η : ℕ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-(3 / 2) * Real.log (lambdaComb c') - 3 / 2 * langerK x xiStar) *
    (CStar * kappaAiry * ‖designAiryW σ η (-kappaAiry * sigmaOf c' x)‖)

lemma width_bound_large (Csh csep : ℝ) :
    ∃ N : ℝ, ∀ {c' : ℝ}, N ≤ c' → ∀ {σ η : ℕ → ℝ}, CombDesignHyp Csh csep σ η →
      ∀ k : ℕ, 2 ≤ k → |widthE c' η k| ≤ 1 / 8 := by
  obtain ⟨Cg, hCg, hgev⟩ := siteGap_le_unif
  obtain ⟨N, hN⟩ := eventually_atTop.1 hgev
  refine ⟨max N 1, fun {c'} hc' σ η h k hk => ?_⟩
  have hc'0 : 0 < c' := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hc')
  have hk1 : 1 ≤ k := by omega
  obtain ⟨hη0, hη1⟩ := h.height k hk
  have hℓ1 := (hN c' ((le_max_left _ _).trans hc') k hk1).2
  have hℓ0 : 0 ≤ siteGap c' k := Design.siteGap_nonneg hc'0 hk1
  rw [abs_of_nonneg (widthE_nonneg hc'0 hk hη0)]
  have := mul_le_mul_of_nonneg_right hη1 hℓ0
  unfold widthE
  linarith

lemma norm_combBD_pos {Csh csep : ℝ} {c' : ℝ} (hc' : 0 < c') {σ η : ℕ → ℝ}
    (h : CombDesignHyp Csh csep σ η) (hw : ∀ k : ℕ, 2 ≤ k → |widthE c' η k| ≤ 1 / 8) {x : ℝ}
    (hx : 0 < x) (hxk : ∀ k : ℕ, 1 ≤ k → x ≠ siteX c' σ k) : 0 < ‖combBD c' σ η (x : ℂ)‖ := by
  have hy0 : ∀ k : ℕ, 1 ≤ k → 0 ≤ siteX c' σ k := fun k hk =>
    xiStar_pos.le.trans (xiStar_le_siteX hc' (h.nonneg k hk))
  obtain ⟨hlog, _, hB⟩ := combBD_real hc' h hw x
  have hT : 0 < ‖blaschkeT (siteX c' σ 1 : ℂ) (x : ℂ)‖ :=
    Design.norm_blaschkeT_ofReal_pos hx.le (hy0 1 le_rfl) (hxk 1 le_rfl)
  have hq : ∀ m : ℕ, 0 < qPair c' σ η (m + 2) x := fun m => by
    have hε0 : 0 ≤ widthE c' η (m + 2) :=
      widthE_nonneg hc' (by omega) (h.height (m + 2) (by omega)).1
    have hε := (abs_le.1 (hw (m + 2) (by omega))).2
    exact Design.blaschkePairQ_pos (hy0 (m + 2) (by omega)) hx.le (hxk (m + 2) (by omega)) hε0
      (by linarith)
  rw [hB, ← Real.rexp_tsum_eq_tprod hq hlog]
  exact mul_pos hT (Real.exp_pos _)

lemma continuous_slitL : Continuous slitL := by
  unfold slitL; fun_prop

lemma continuousOn_combAmp {Csh csep : ℝ} {c' : ℝ} (hc' : 0 < c') {σ η : ℕ → ℝ}
    (h : CombDesignHyp Csh csep σ η) (hw : ∀ k : ℕ, 2 ≤ k → |widthE c' η k| ≤ 1 / 8) :
    ContinuousOn (combAmp c' σ η) (langerX (1 / 2)) := by
  intro x hx
  have hE : Continuous fun z : ℝ => Real.exp (c' * slitL z) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_slitL)
  exact ((continuousAt_normComb hc' h hw x).mul hE.continuousAt).continuousWithinAt

lemma continuousOn_airyAmp {Csh csep : ℝ} {c' : ℝ} {σ η : ℕ → ℝ}
    (h : CombDesignHyp Csh csep σ η) :
    ContinuousOn (airyAmp c' σ η) (langerX (1 / 2)) := by
  intro x hx
  have hxpos : 0 < x := by have := xiStar_pos; linarith [hx.1]
  have hK := continuousAt_langerK_xiStar hxpos
  have hW := continuousAt_normAiryW h c' hxpos
  have h1 : ContinuousAt (fun z : ℝ => Real.exp (-(3 / 2) * Real.log (lambdaComb c') -
      3 / 2 * langerK z xiStar)) x :=
    (Real.continuous_exp.continuousAt).comp (continuousAt_const.sub (hK.const_mul _))
  exact (h1.mul (hW.const_mul _)).continuousWithinAt

/-- **Proposition 1.2(2), multiplicative form, on all of `[ξ_*/2, ξ_* + 1/2]`.** -/
theorem combToAiry_mult (Csh csep : ℝ) (hcsep : 0 < csep) :
    ∃ C c0 : ℝ, 0 < C ∧ 0 < c0 ∧ ∀ {c' : ℝ}, c0 ≤ c' → ∀ {σ η : ℕ → ℝ},
      CombDesignHyp Csh csep σ η → ∀ x ∈ langerX (1 / 2),
      Real.exp (-(C * lambdaComb c')) * airyAmp c' σ η x ≤ combAmp c' σ η x ∧
      combAmp c' σ η x ≤ Real.exp (C * lambdaComb c') * airyAmp c' σ η x := by
  obtain ⟨C, c0, hC, hc0, H⟩ := combToAiry_nonsite Csh csep hcsep
  obtain ⟨N, hN⟩ := width_bound_large Csh csep
  refine ⟨C, max c0 (max N 1), hC, lt_of_lt_of_le hc0 (le_max_left _ _), ?_⟩
  intro c' hc' σ η h
  have hc'0 : 0 < c' := lt_of_lt_of_le one_pos ((le_max_right _ _).trans ((le_max_right _ _).trans hc'))
  have hw := hN ((le_max_left _ _).trans ((le_max_right _ _).trans hc')) h
  have hcc := continuousOn_combAmp hc'0 h hw
  have hca := continuousOn_airyAmp (c' := c') h
  have hup : ContinuousOn (fun x => Real.exp (C * lambdaComb c') * airyAmp c' σ η x) (langerX (1 / 2)) :=
    continuousOn_const.mul hca
  have hlo : ContinuousOn (fun x => Real.exp (-(C * lambdaComb c')) * airyAmp c' σ η x) (langerX (1 / 2)) :=
    continuousOn_const.mul hca
  have hab : xiStar / 2 < xiStar + 1 / 2 := by have := xiStar_pos; linarith
  have key : ∀ x ∈ langerX (1 / 2), x ∉ Set.range (siteX c' σ) →
      Real.exp (-(C * lambdaComb c')) * airyAmp c' σ η x ≤ combAmp c' σ η x ∧
      combAmp c' σ η x ≤ Real.exp (C * lambdaComb c') * airyAmp c' σ η x := by
    intro x hx hxS
    have hxk : ∀ k : ℕ, 1 ≤ k → x ≠ siteX c' σ k := fun k _ hk => hxS ⟨k, hk.symm⟩
    have hxpos : 0 < x := by have := xiStar_pos; linarith [hx.1]
    obtain ⟨hWpos, hlog⟩ := H ((le_max_left _ _).trans hc') h x hx hxk
    have hBpos := norm_combBD_pos hc'0 h hw hxpos hxk
    have hCW : 0 < CStar * kappaAiry * ‖designAiryW σ η (-kappaAiry * sigmaOf c' x)‖ :=
      mul_pos (mul_pos CStar_pos kappaAiry_pos) hWpos
    have hAeq : airyAmp c' σ η x = Real.exp (-(3 / 2) * Real.log (lambdaComb c') -
        3 / 2 * langerK x xiStar + Real.log (CStar * kappaAiry * ‖designAiryW σ η (-kappaAiry * sigmaOf c' x)‖)) := by
      unfold airyAmp
      rw [Real.exp_add, Real.exp_log hCW]
    have hBeq : combAmp c' σ η x = Real.exp (Real.log ‖combBD c' σ η (x : ℂ)‖ + c' * slitL x) := by
      unfold combAmp
      rw [Real.exp_add, Real.exp_log hBpos]
    obtain ⟨h1, h2⟩ := abs_le.1 hlog
    rw [hAeq, hBeq, ← Real.exp_add, ← Real.exp_add]
    constructor
    · apply Real.exp_le_exp.2; linarith
    · apply Real.exp_le_exp.2; linarith
  have hcount : (Set.range (siteX c' σ)).Countable := Set.countable_range _
  intro x hx
  exact ⟨le_of_forall_notMem_countable hab hcount hlo hcc (fun y hy hyS => (key y hy hyS).1) x hx,
    le_of_forall_notMem_countable hab hcount hcc hup (fun y hy hyS => (key y hy hyS).2) x hx⟩

/-- **Proposition 1.2(2), logarithmic form at every `x` with `B_D(x) ≠ 0`** (the real zeros of `B_D` are the sites
`χ'_k` of height `0`; for `η_k > 0` the statement holds at the sites too). -/
theorem combToAiry_log (Csh csep : ℝ) (hcsep : 0 < csep) :
    ∃ C c0 : ℝ, 0 < C ∧ 0 < c0 ∧ ∀ {c' : ℝ}, c0 ≤ c' → ∀ {σ η : ℕ → ℝ},
      CombDesignHyp Csh csep σ η → ∀ x ∈ langerX (1 / 2), ‖combBD c' σ η (x : ℂ)‖ ≠ 0 →
      0 < ‖designAiryW σ η (-kappaAiry * sigmaOf c' x)‖ ∧
      |Real.log ‖combBD c' σ η (x : ℂ)‖ + c' * slitL x -
        (-(3 / 2) * Real.log (lambdaComb c') - 3 / 2 * langerK x xiStar +
          Real.log (CStar * kappaAiry * ‖designAiryW σ η (-kappaAiry * sigmaOf c' x)‖))| ≤
        C * lambdaComb c' := by
  obtain ⟨C, c0, hC, hc0, H⟩ := combToAiry_mult Csh csep hcsep
  refine ⟨C, c0, hC, hc0, fun {c'} hc' σ η h x hx hB => ?_⟩
  obtain ⟨h1, h2⟩ := H hc' h x hx
  have hBpos : 0 < ‖combBD c' σ η (x : ℂ)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hB)
  have hFpos : 0 < combAmp c' σ η x := mul_pos hBpos (Real.exp_pos _)
  have hApos : 0 < airyAmp c' σ η x := by
    have := mul_pos hFpos (Real.exp_pos (-(C * lambdaComb c')))
    have h3 : Real.exp (-(C * lambdaComb c')) * combAmp c' σ η x ≤ airyAmp c' σ η x := by
      have := Real.exp_pos (-(C * lambdaComb c'))
      have h4 := Real.exp_pos (C * lambdaComb c')
      have h5 : combAmp c' σ η x * Real.exp (-(C * lambdaComb c')) ≤
          Real.exp (C * lambdaComb c') * airyAmp c' σ η x * Real.exp (-(C * lambdaComb c')) :=
        mul_le_mul_of_nonneg_right h2 this.le
      have h6 : Real.exp (C * lambdaComb c') * Real.exp (-(C * lambdaComb c')) = 1 := by
        rw [← Real.exp_add]; simp
      have h7 : Real.exp (C * lambdaComb c') * airyAmp c' σ η x * Real.exp (-(C * lambdaComb c')) =
          airyAmp c' σ η x := by
        calc _ = (Real.exp (C * lambdaComb c') * Real.exp (-(C * lambdaComb c'))) * airyAmp c' σ η x := by ring
          _ = _ := by rw [h6, one_mul]
      rw [h7] at h5; linarith
    exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) hFpos) h3
  have hWpos : 0 < ‖designAiryW σ η (-kappaAiry * sigmaOf c' x)‖ := by
    by_contra hcon
    have h0 : ‖designAiryW σ η (-kappaAiry * sigmaOf c' x)‖ = 0 :=
      le_antisymm (not_lt.1 hcon) (norm_nonneg _)
    have : airyAmp c' σ η x = 0 := by unfold airyAmp; rw [h0]; ring
    linarith
  refine ⟨hWpos, ?_⟩
  have hCW : 0 < CStar * kappaAiry * ‖designAiryW σ η (-kappaAiry * sigmaOf c' x)‖ :=
    mul_pos (mul_pos CStar_pos kappaAiry_pos) hWpos
  have hAlog : Real.log (airyAmp c' σ η x) = -(3 / 2) * Real.log (lambdaComb c') -
      3 / 2 * langerK x xiStar +
        Real.log (CStar * kappaAiry * ‖designAiryW σ η (-kappaAiry * sigmaOf c' x)‖) := by
    unfold airyAmp
    rw [Real.log_mul (Real.exp_pos _).ne' hCW.ne', Real.log_exp]
  have hFlog : Real.log (combAmp c' σ η x) =
      Real.log ‖combBD c' σ η (x : ℂ)‖ + c' * slitL x := by
    unfold combAmp
    rw [Real.log_mul hBpos.ne' (Real.exp_pos _).ne', Real.log_exp]
  have e1 := Real.log_le_log (mul_pos (Real.exp_pos _) hApos) h1
  have e2 := Real.log_le_log hFpos h2
  rw [Real.log_mul (Real.exp_pos _).ne' hApos.ne', Real.log_exp] at e1
  rw [Real.log_mul (Real.exp_pos _).ne' hApos.ne', Real.log_exp] at e2
  rw [← hAlog, ← hFlog]
  exact abs_le.2 ⟨by linarith, by linarith⟩

lemma lambdaComb_eq_mul {c' : ℝ} (hc' : 0 < c') :
    lambdaComb c' = kTip ^ (-(2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) := by
  unfold lambdaComb
  exact Real.mul_rpow kTip_pos.le hc'.le

/-- `rem:P1.2`(2) as stated: the error is `C c'^{-2/3}`. -/
theorem combToAiry_log_rate (Csh csep : ℝ) (hcsep : 0 < csep) :
    ∃ C c0 : ℝ, 0 < C ∧ 0 < c0 ∧ ∀ {c' : ℝ}, c0 ≤ c' → ∀ {σ η : ℕ → ℝ},
      CombDesignHyp Csh csep σ η → ∀ x ∈ langerX (1 / 2), ‖combBD c' σ η (x : ℂ)‖ ≠ 0 →
      0 < ‖designAiryW σ η (-kappaAiry * sigmaOf c' x)‖ ∧
      |Real.log ‖combBD c' σ η (x : ℂ)‖ + c' * slitL x -
        (-(3 / 2) * Real.log (lambdaComb c') - 3 / 2 * langerK x xiStar +
          Real.log (CStar * kappaAiry * ‖designAiryW σ η (-kappaAiry * sigmaOf c' x)‖))| ≤
        C * c' ^ (-(2 / 3 : ℝ)) := by
  obtain ⟨C, c0, hC, hc0, H⟩ := combToAiry_log Csh csep hcsep
  have hk : 0 < kTip ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos kTip_pos _
  refine ⟨C * kTip ^ (-(2 / 3 : ℝ)), c0, mul_pos hC hk, hc0, fun {c'} hc' σ η h x hx hB => ?_⟩
  obtain ⟨hW, hb⟩ := H hc' h x hx hB
  refine ⟨hW, hb.trans (le_of_eq ?_)⟩
  rw [lambdaComb_eq_mul (lt_of_lt_of_le hc0 hc')]; ring

lemma ref_amp_eq (c' x : ℝ) (hc' : 0 < c') :
    (2 * Real.sqrt 2 / (π * lambdaComb c')) ^ (3 / 2 : ℝ) *
        Real.exp (-(3 / 2) * (langerK x xiStar + Real.log (2 * Real.sqrt 2 / π))) =
      Real.exp (-(3 / 2) * Real.log (lambdaComb c') - 3 / 2 * langerK x xiStar) := by
  have hl := lamPos hc'
  have ha : 0 < 2 * Real.sqrt 2 / π := by positivity
  have h1 : (2 * Real.sqrt 2 / (π * lambdaComb c')) = (2 * Real.sqrt 2 / π) / lambdaComb c' := by
    field_simp
  rw [h1, Real.div_rpow ha.le hl.le, Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hl,
    ← Real.exp_sub, ← Real.exp_add]
  congr 1
  ring

/-- **Amplitude form** (`n2_ramped_comb.tex`, Step 2 / Step 5): with `K_s(x) = 𝒦_*(x) + log(2√2/π)`,
`‖B_D(x)‖ e^{c'L(x)} = (2√2/(πλ))^{3/2} e^{-(3/2)K_s(x)} C_* κ ‖W_D(-κτ(x)/λ)‖ exp(O(c'^{-2/3}))`
uniformly on `[ξ_*/2, ξ_* + 1/2]`, including the real zeros. -/
theorem combToAiry_amplitude (Csh csep : ℝ) (hcsep : 0 < csep) :
    ∃ C c0 : ℝ, 0 < C ∧ 0 < c0 ∧ ∀ {c' : ℝ}, c0 ≤ c' → ∀ {σ η : ℕ → ℝ},
      CombDesignHyp Csh csep σ η → ∀ x ∈ langerX (1 / 2),
      Real.exp (-(C * c' ^ (-(2 / 3 : ℝ)))) *
          ((2 * Real.sqrt 2 / (π * lambdaComb c')) ^ (3 / 2 : ℝ) *
            Real.exp (-(3 / 2) * (langerK x xiStar + Real.log (2 * Real.sqrt 2 / π))) *
            (CStar * kappaAiry * ‖designAiryW σ η (-kappaAiry * sigmaOf c' x)‖)) ≤
        ‖combBD c' σ η (x : ℂ)‖ * Real.exp (c' * slitL x) ∧
      ‖combBD c' σ η (x : ℂ)‖ * Real.exp (c' * slitL x) ≤
        Real.exp (C * c' ^ (-(2 / 3 : ℝ))) *
          ((2 * Real.sqrt 2 / (π * lambdaComb c')) ^ (3 / 2 : ℝ) *
            Real.exp (-(3 / 2) * (langerK x xiStar + Real.log (2 * Real.sqrt 2 / π))) *
            (CStar * kappaAiry * ‖designAiryW σ η (-kappaAiry * sigmaOf c' x)‖)) := by
  obtain ⟨C, c0, hC, hc0, H⟩ := combToAiry_mult Csh csep hcsep
  have hk : 0 < kTip ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos kTip_pos _
  refine ⟨C * kTip ^ (-(2 / 3 : ℝ)), c0, mul_pos hC hk, hc0, fun {c'} hc' σ η h x hx => ?_⟩
  have hc'0 : 0 < c' := lt_of_lt_of_le hc0 hc'
  obtain ⟨h1, h2⟩ := H hc' h x hx
  have hr := ref_amp_eq c' x hc'0
  have hexp : C * kTip ^ (-(2 / 3 : ℝ)) * c' ^ (-(2 / 3 : ℝ)) = C * lambdaComb c' := by
    rw [lambdaComb_eq_mul hc'0]; ring
  rw [hexp, hr]
  unfold airyAmp at h1 h2
  unfold combAmp at h1 h2
  exact ⟨h1, h2⟩

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.combToAiry_mult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combToAiry_mult

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.combToAiry_log_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combToAiry_log_rate

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.combToAiry_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combToAiry_amplitude

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.combToAiry_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combToAiry_log

end FormalResearch.ModularBootstrap.Upper.Ramped
