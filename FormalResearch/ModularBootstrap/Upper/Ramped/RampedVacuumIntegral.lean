module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedVacuumBands
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedVacuumCore

/-!
# The Langer window of the vacuum integral of the ramped comb (`rem:thmU` Step (5))

* `integral_comp_sq_Icc`: the substitution `t = c'x²/3` on a compact interval;
* `rampedWindow_part`: given the Airy-window package of `W_D` (`rampedW_package`), the window part of the vacuum
  integral is `∫_{x ∈ [ξ_*/2, ξ_*+1/2]} h₀ V ≤ FK_c C_* (-d/2 + (C_E + T) c'^{-1/3})` for `d ∈ [0, d_0]`, with `T`
  depending only on the Airy constant `C_w`: the pointwise inequality `rampedWindow_pointwise` is integrated in
  the Langer variable `σ = τ(x)/λ` and `window_core` is applied with `A = -σ(ξ_*/2) ≍ 1/λ`, `b = σ(ξ_*+1/2) ≍ 1/λ`,
  `E₁ = c₁λ`, `E₂ = c₂ c'^{-2/3}`; the truncation tails and the weight error are all `O(λ^{1/2}) = O(c'^{-1/3})`.

All results are proved unconditionally.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open Real Filter Topology Set MeasureTheory
open scoped Real
open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Window
  FormalResearch.ModularBootstrap.Upper.Window.Cardy FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Window.Tail
  FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Holes

/-- The substitution `t = c' x²/3` on a compact interval. -/
lemma integral_comp_sq_Icc {c' : ℝ} (hc' : 0 ≤ c') {F : ℝ → ℝ} (hF : ContinuousOn F (Ici 0)) {a b : ℝ} :
    ∫ t in (c' * a ^ 2 / 3)..(c' * b ^ 2 / 3), F t = ∫ x in a..b, (2 * c' * x / 3) * F (c' * x ^ 2 / 3) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => c' * x ^ 2 / 3) (2 * c' * x / 3) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
    have h2 := (h1.const_mul c').div_const 3
    convert h2 using 1
    ring
  have himg : (fun x : ℝ => c' * x ^ 2 / 3) '' uIcc a b ⊆ Ici 0 := by
    rintro _ ⟨x, _, rfl⟩
    exact mem_Ici.mpr (by positivity)
  have := intervalIntegral.integral_comp_mul_deriv'' (a := a) (b := b) (f := fun x : ℝ => c' * x ^ 2 / 3)
    (f' := fun x => 2 * c' * x / 3) (g := F) (by fun_prop) (fun x _ => (hd x).hasDerivWithinAt)
    (by fun_prop) (hF.mono himg)
  rw [← this]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [Function.comp_apply]
  ring

lemma sqrt_lam_eq {c' : ℝ} (hc' : 0 < c') :
    lambdaComb c' ^ (1 / 2 : ℝ) = kTip ^ (-(1 / 3 : ℝ)) * c' ^ (-(1 / 3 : ℝ)) := by
  have hk := kTip_pos
  unfold lambdaComb
  rw [← Real.rpow_mul (by positivity), Real.mul_rpow hk.le hc'.le]
  norm_num

lemma lam_rpow_scale {l : ℝ} (hl : 0 < l) {x : ℝ} (hx : 0 < x) :
    (x / l) ^ (-(1 / 2 : ℝ)) = x ^ (-(1 / 2 : ℝ)) * l ^ (1 / 2 : ℝ) := by
  rw [Real.div_rpow hx.le hl.le, Real.rpow_neg hl.le, div_inv_eq_mul]

lemma lam_mul_rpow_scale {l : ℝ} (hl : 0 < l) {x : ℝ} (hx : 0 < x) :
    l * (x / l) ^ (1 / 2 : ℝ) = x ^ (1 / 2 : ℝ) * l ^ (1 / 2 : ℝ) := by
  have hs : l ^ (1 / 2 : ℝ) * l ^ (1 / 2 : ℝ) = l := by
    rw [← Real.rpow_add hl]; norm_num
  have hs0 : 0 < l ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hl _
  rw [Real.div_rpow hx.le hl.le]
  nth_rewrite 1 [← hs]
  field_simp

lemma langerTau_xiStar_half_neg : langerTau (xiStar / 2) < 0 := by
  have hxs := xiStar_pos
  have h := langerTau_strictMonoOn (show xiStar / 2 ∈ Ioi (0 : ℝ) from by simp only [mem_Ioi]; linarith)
    (show xiStar ∈ Ioi (0 : ℝ) from hxs) (by linarith)
  rwa [langerTau_xiStar] at h

lemma langerTau_xiStar_add_half_pos : 0 < langerTau (xiStar + 1 / 2) :=
  langerTau_pos_of_gt (by linarith)


/-- **The Langer window** (`rem:thmU` Step (5)): given the Airy-window package for `W_D` (the bound
`‖W_D(u)‖ ≤ C_w (1 + |u|)^{-3/2}`, continuity and integrability of `Re W_D`, and the profile bound
`∫ Re W_D ≤ -d/2 + C_E c'^{-1/3}`), the window part of the vacuum integral satisfies
`∫_{x ∈ [ξ_*/2, ξ_*+1/2]} h₀ V ≤ FK_c C_* (-d/2 + (C_E + T) c'^{-1/3})`, `T` depending on `C_w` only. -/
theorem rampedWindow_part (Cw : ℝ) (hCw : 0 < Cw) : ∃ T : ℝ, 0 < T ∧ ∀ (P : RampedParams) (CE : ℝ),
    (∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ 1 →
      (∀ u : ℝ, ‖designAiryW (rampedNode d c') (rampedEta P c') u‖ ≤ Cw * (1 + |u|) ^ (-(3 / 2 : ℝ))) ∧
      Continuous (fun u : ℝ => (designAiryW (rampedNode d c') (rampedEta P c') u).re) ∧
      Integrable (fun u : ℝ => (designAiryW (rampedNode d c') (rampedEta P c') u).re) ∧
      (∫ u : ℝ, (designAiryW (rampedNode d c') (rampedEta P c') u).re) ≤
        -d / 2 + CE * c' ^ (-(1 / 3 : ℝ))) →
    (∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ 1 → ContinuousOn (rampedF P d c') (Ici 0)) →
    ∀ᶠ c' : ℝ in atTop, ∀ d : ℝ, 0 ≤ d → d ≤ rampedD0 →
      (∫ t in (c' * (xiStar / 2) ^ 2 / 3)..(c' * (xiStar + 1 / 2) ^ 2 / 3), rampedF P d c' t) ≤
        FKc 1 1 c' * CStar * (-d / 2 + (CE + T) * c' ^ (-(1 / 3 : ℝ))) := by
  obtain ⟨c1, c2, hc1, hc2, hpt⟩ := rampedWindow_pointwise
  have hκ := kappaAiry_pos
  have hk := kTip_pos
  have hxs := xiStar_pos
  have hCs := CStar_pos
  obtain ⟨a0, ha0def⟩ : ∃ a0 : ℝ, a0 = -langerTau (xiStar / 2) := ⟨_, rfl⟩
  obtain ⟨b0, hb0def⟩ : ∃ b0 : ℝ, b0 = langerTau (xiStar + 1 / 2) := ⟨_, rfl⟩
  have ha0 : 0 < a0 := by rw [ha0def]; linarith [langerTau_xiStar_half_neg]
  have hb0 : 0 < b0 := by rw [hb0def]; exact langerTau_xiStar_add_half_pos
  obtain ⟨J, hJdef⟩ : ∃ J : ℝ, J = ∫ u : ℝ, (1 + |u|) ^ (-(3 / 2 : ℝ)) := ⟨_, rfl⟩
  have hJint : Integrable (fun u : ℝ => (1 + |u|) ^ (-(3 / 2 : ℝ))) := by
    have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2) (by simp; norm_num)
    simpa only [Real.norm_eq_abs] using this
  have hJ0 : 0 ≤ J := by rw [hJdef]; exact integral_nonneg fun u => by positivity
  obtain ⟨S1, hS1⟩ : ∃ S1 : ℝ, S1 = (2 * Cw / kappaAiry) * ((kappaAiry * b0) ^ (-(1 / 2 : ℝ)) +
      (kappaAiry * a0) ^ (-(1 / 2 : ℝ))) + 2 * c1 * Cw * kappaAiry ^ (-(3 / 2 : ℝ)) *
      (a0 ^ (1 / 2 : ℝ) + b0 ^ (1 / 2 : ℝ)) := ⟨_, rfl⟩
  have hS10 : 0 ≤ S1 := by rw [hS1]; positivity
  refine ⟨kappaAiry * S1 * kTip ^ (-(1 / 3 : ℝ)) + c2 * Cw * J + 1, by positivity, fun P CE hW hFc => ?_⟩
  filter_upwards [hpt P, hW, hFc, eventually_ge_atTop (1 : ℝ)] with c' hp hw hF hc1' d hd0 hdD
  have hc'0 : 0 < c' := by linarith
  have hd1 : d ≤ 1 := hdD.trans rampedD0_le_one
  obtain ⟨hbd, hcont, hint, hI⟩ := hw d hd0 hd1
  have hFc' := hF d hd0 hd1
  have hl := lamPos hc'0
  set l : ℝ := lambdaComb c' with hldef
  set w : ℝ → ℝ := fun u => (designAiryW (rampedNode d c') (rampedEta P c') u).re with hwdef
  have hbd' : ∀ u, |w u| ≤ Cw * (1 + |u|) ^ (-(3 / 2 : ℝ)) := fun u =>
    (Complex.abs_re_le_norm _).trans (hbd u)
  have hab : xiStar / 2 ≤ xiStar + 1 / 2 := by linarith
  have hstep1 := integral_comp_sq_Icc hc'0.le hFc' (a := xiStar / 2) (b := xiStar + 1 / 2)
  -- the weight function
  set g : ℝ → ℝ := fun σ => w (-kappaAiry * σ) + |w (-kappaAiry * σ)| *
      (c1 * l * |σ| + c2 * c' ^ (-(2 / 3 : ℝ))) with hgdef
  have hwc : Continuous fun σ : ℝ => w (-kappaAiry * σ) := hcont.comp (by fun_prop)
  have hgc : Continuous g := hwc.add (hwc.abs.mul (by fun_prop))
  have hgx : ∀ x : ℝ, rampedWFun P d c' (sigmaOf c' x) + |rampedWFun P d c' (sigmaOf c' x)| *
      (c1 * lambdaComb c' * |sigmaOf c' x| + c2 * c' ^ (-(2 / 3 : ℝ))) = g (sigmaOf c' x) :=
    fun x => rfl
  have hsub : uIcc (xiStar / 2) (xiStar + 1 / 2) ⊆ Ioi 0 := by
    rw [uIcc_of_le hab]
    intro x hx
    exact mem_Ioi.mpr (by linarith [hx.1])
  have hsd : ∀ x ∈ uIcc (xiStar / 2) (xiStar + 1 / 2),
      HasDerivAt (sigmaOf c') (deriv langerTau x / l) x := fun x hx => by
    exact (hasDerivAt_langerTau_pos (hsub hx)).div_const l
  have hsc : ContinuousOn (sigmaOf c') (uIcc (xiStar / 2) (xiStar + 1 / 2)) :=
    fun x hx => (hsd x hx).continuousAt.continuousWithinAt
  have hdc : ContinuousOn (fun x => deriv langerTau x / l) (uIcc (xiStar / 2) (xiStar + 1 / 2)) :=
    (continuousOn_deriv_langerTau.mono hsub).div_const l
  have hstep3 := intervalIntegral.integral_comp_mul_deriv' hsd hdc hgc.continuousOn
  have hs1 : sigmaOf c' (xiStar / 2) = -(a0 / l) := by
    unfold sigmaOf
    rw [ha0def]; ring
  have hs2 : sigmaOf c' (xiStar + 1 / 2) = b0 / l := by
    unfold sigmaOf
    rw [hb0def]
  rw [hs1, hs2] at hstep3
  -- monotonicity
  have hlc : ContinuousOn (fun x : ℝ => (2 * c' * x / 3) * rampedF P d c' (c' * x ^ 2 / 3))
      (uIcc (xiStar / 2) (xiStar + 1 / 2)) := by
    refine ContinuousOn.mul (by fun_prop) (hFc'.comp (by fun_prop) fun x _ => ?_)
    exact mem_Ici.mpr (by positivity)
  have hrc : ContinuousOn (fun x : ℝ => FKc 1 1 c' * (CStar * kappaAiry) *
      (g (sigmaOf c' x) * (deriv langerTau x / l))) (uIcc (xiStar / 2) (xiStar + 1 / 2)) :=
    continuousOn_const.mul ((hgc.comp_continuousOn hsc).mul hdc)
  have hmono := intervalIntegral.integral_mono_on hab (hlc.intervalIntegrable (μ := volume)) (hrc.intervalIntegrable (μ := volume))
    (fun x hx => by
      have := hp d hd0 hdD x hx
      rw [hgx x] at this
      calc (2 * c' * x / 3) * rampedF P d c' (c' * x ^ 2 / 3)
          ≤ FKc 1 1 c' * (CStar * kappaAiry) * (deriv langerTau x / lambdaComb c') * g (sigmaOf c' x) := this
        _ = FKc 1 1 c' * (CStar * kappaAiry) * (g (sigmaOf c' x) * (deriv langerTau x / l)) := by
            ring)
  rw [intervalIntegral.integral_const_mul] at hmono
  have hconv : (∫ x in (xiStar / 2)..(xiStar + 1 / 2), g (sigmaOf c' x) * (deriv langerTau x / l)) =
      ∫ σ in (-(a0 / l))..(b0 / l), g σ := hstep3
  rw [hconv] at hmono
  rw [hstep1]
  refine hmono.trans ?_
  -- the core estimate
  have hFK := FKc_pos (q := 1) one_pos 1 hc'0
  have hcore := window_core (w := w) hcont hint hCw.le hκ (E1 := c1 * l) (E2 := c2 * c' ^ (-(2 / 3 : ℝ)))
    (A := a0 / l) (b := b0 / l) (by positivity) (by positivity) (by positivity) (by positivity) hbd'
  have e1 : (kappaAiry * (b0 / l)) ^ (-(1 / 2 : ℝ)) = (kappaAiry * b0) ^ (-(1 / 2 : ℝ)) * l ^ (1 / 2 : ℝ) := by
    rw [← mul_div_assoc]; exact lam_rpow_scale hl (mul_pos hκ hb0)
  have e2 : (kappaAiry * (a0 / l)) ^ (-(1 / 2 : ℝ)) = (kappaAiry * a0) ^ (-(1 / 2 : ℝ)) * l ^ (1 / 2 : ℝ) := by
    rw [← mul_div_assoc]; exact lam_rpow_scale hl (mul_pos hκ ha0)
  have e3 := lam_mul_rpow_scale hl ha0
  have e4 := lam_mul_rpow_scale hl hb0
  have e5 : 2 * (c1 * l) * Cw * kappaAiry ^ (-(3 / 2 : ℝ)) * ((a0 / l) ^ (1 / 2 : ℝ) + (b0 / l) ^ (1 / 2 : ℝ)) =
      2 * c1 * Cw * kappaAiry ^ (-(3 / 2 : ℝ)) * (a0 ^ (1 / 2 : ℝ) * l ^ (1 / 2 : ℝ) +
        b0 ^ (1 / 2 : ℝ) * l ^ (1 / 2 : ℝ)) := by
    rw [← e3, ← e4]; ring
  rw [e1, e2, e5] at hcore
  have hs : l ^ (1 / 2 : ℝ) = kTip ^ (-(1 / 3 : ℝ)) * c' ^ (-(1 / 3 : ℝ)) := sqrt_lam_eq hc'0
  have hr : 0 < c' ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hc'0 _
  have h23 : c' ^ (-(2 / 3 : ℝ)) ≤ c' ^ (-(1 / 3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hc1' (by norm_num)
  have h23' : 0 ≤ c' ^ (-(2 / 3 : ℝ)) := (Real.rpow_pos_of_pos hc'0 _).le
  have hIa : (∫ u, |w u|) ≤ Cw * J := by
    rw [hJdef, ← integral_const_mul]
    exact integral_mono hint.abs (hJint.const_mul Cw) hbd'
  have hIa0 : 0 ≤ ∫ u, |w u| := integral_nonneg fun u => abs_nonneg _
  have hk3 : 0 < kTip ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hk _
  -- assemble: κ ∫g ≤ I_w + κ s S1 + c2 c'^{-2/3} I_a
  have hmain : kappaAiry * ((kappaAiry)⁻¹ * (∫ u, w u) +
      (2 * Cw / kappaAiry) * ((kappaAiry * b0) ^ (-(1 / 2 : ℝ)) * l ^ (1 / 2 : ℝ) +
        (kappaAiry * a0) ^ (-(1 / 2 : ℝ)) * l ^ (1 / 2 : ℝ)) +
      2 * c1 * Cw * kappaAiry ^ (-(3 / 2 : ℝ)) * (a0 ^ (1 / 2 : ℝ) * l ^ (1 / 2 : ℝ) +
        b0 ^ (1 / 2 : ℝ) * l ^ (1 / 2 : ℝ)) +
      c2 * c' ^ (-(2 / 3 : ℝ)) / kappaAiry * ∫ u, |w u|) =
      (∫ u, w u) + kappaAiry * S1 * l ^ (1 / 2 : ℝ) + c2 * c' ^ (-(2 / 3 : ℝ)) * ∫ u, |w u| := by
    rw [hS1]
    field_simp
    ring
  have hbound : (∫ u, w u) + kappaAiry * S1 * l ^ (1 / 2 : ℝ) + c2 * c' ^ (-(2 / 3 : ℝ)) * ∫ u, |w u| ≤
      -d / 2 + (CE + (kappaAiry * S1 * kTip ^ (-(1 / 3 : ℝ)) + c2 * Cw * J + 1)) * c' ^ (-(1 / 3 : ℝ)) := by
    rw [hs]
    have h1 : c2 * c' ^ (-(2 / 3 : ℝ)) * ∫ u, |w u| ≤ c2 * c' ^ (-(1 / 3 : ℝ)) * (Cw * J) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h23 hc2.le) hIa hIa0 (by positivity)
    linarith only [hI, h1, hr]
  have hκg := mul_le_mul_of_nonneg_left hcore hκ.le
  rw [hmain] at hκg
  have hK0 : 0 ≤ FKc 1 1 c' * CStar := by positivity
  calc FKc 1 1 c' * (CStar * kappaAiry) * _ = FKc 1 1 c' * CStar * (kappaAiry * _) := by ring
    _ ≤ FKc 1 1 c' * CStar * (-d / 2 + (CE + (kappaAiry * S1 * kTip ^ (-(1 / 3 : ℝ)) + c2 * Cw * J + 1)) *
          c' ^ (-(1 / 3 : ℝ))) := mul_le_mul_of_nonneg_left (hκg.trans hbound) hK0

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.rampedWindow_part' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rampedWindow_part

end FormalResearch.ModularBootstrap.Upper.Ramped
