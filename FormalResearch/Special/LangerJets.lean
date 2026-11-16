module

public import FormalResearch.Special.LangerPhi

@[expose] public section

open Filter Topology Set

namespace FormalResearch.Special

private lemma deriv_sub_one_fun (u : ℝ → ℝ) : deriv (fun q => u q - 1) = deriv u := by
  funext q; exact deriv_sub_const _

/-- **Jets of `F = Φ(u - 1)` at a point where `u = 1`** (P3 A:1152): with `u₁ = u'(c)`, `u₂ = u''(c)/2`,
`u₃ = u'''(c)/6` the Taylor coefficients, `F₁ = 2u₁`, `F₂ = 2u₂ - u₁²/3`,
`F₃ = 2u₃ - (2/3)u₁u₂ + (4/45)u₁³` (the Taylor coefficients `F''/2`, `F'''/6` of `F`).
Stated here with derivatives: `F'' = 2u'' - (2/3)u'²`, `F''' = 2u''' - 2u'u'' + (8/15)u'³`. -/
theorem langerF_jets {u : ℝ → ℝ} {c : ℝ} (hu : ContDiffAt ℝ 3 u c) (h1 : u c = 1) :
    deriv (fun q => langerPhi (u q - 1)) c = 2 * deriv u c ∧
    deriv (deriv (fun q => langerPhi (u q - 1))) c =
      2 * deriv (deriv u) c - 2 / 3 * deriv u c ^ 2 ∧
    deriv (deriv (deriv (fun q => langerPhi (u q - 1)))) c =
      2 * deriv (deriv (deriv u)) c - 2 * deriv u c * deriv (deriv u) c
        + 8 / 15 * deriv u c ^ 3 := by
  set v : ℝ → ℝ := fun q => u q - 1 with hv
  have hvc : ContDiffAt ℝ 3 v c := hu.sub contDiffAt_const
  have hv0 : v c = 0 := by simp [hv, h1]
  have hdv : deriv v = deriv u := deriv_sub_one_fun u
  -- smoothness of `v`, `v'`, `v''` near `c`
  have hv3 : ∀ᶠ y in 𝓝 c, ContDiffAt ℝ 3 v y := hvc.eventually (by simp)
  have hv1c : ContDiffAt ℝ 2 (deriv v) c := hvc.derivWithin (m := 2) (by norm_num)
  have hv2c : ContDiffAt ℝ 1 (deriv (deriv v)) c := hv1c.derivWithin (m := 1) (by norm_num)
  have hv1 : ∀ᶠ y in 𝓝 c, ContDiffAt ℝ 2 (deriv v) y := hv3.mono fun y hy =>
    hy.derivWithin (m := 2) (by norm_num)
  have hvd : ∀ᶠ y in 𝓝 c, DifferentiableAt ℝ v y := hv3.mono fun y hy => hy.differentiableAt (by simp)
  have hv1d : ∀ᶠ y in 𝓝 c, DifferentiableAt ℝ (deriv v) y :=
    hv1.mono fun y hy => hy.differentiableAt (by simp)
  have hv2d : DifferentiableAt ℝ (deriv (deriv v)) c := hv2c.differentiableAt (by simp)
  have hv1dc : DifferentiableAt ℝ (deriv v) c := hv1c.differentiableAt (by simp)
  have hvdc : DifferentiableAt ℝ v c := hvc.differentiableAt (by simp)
  -- analyticity of `Φ` and derivatives along `v y`
  have hΦ : ∀ᶠ y in 𝓝 c, AnalyticAt ℝ langerPhi (v y) := by
    have hcont : ContinuousAt v c := hvc.continuousAt
    have := hcont.tendsto
    rw [hv0] at this
    exact this.eventually langerPhi_eventually_analytic
  -- first derivative
  have E1 : ∀ᶠ y in 𝓝 c, HasDerivAt (fun q => langerPhi (v q)) (deriv langerPhi (v y) * deriv v y) y := by
    filter_upwards [hΦ, hvd] with y hy hyd
    exact HasDerivAt.comp y hy.differentiableAt.hasDerivAt hyd.hasDerivAt
  have E1' : deriv (fun q => langerPhi (v q)) =ᶠ[𝓝 c] fun y => deriv langerPhi (v y) * deriv v y :=
    E1.mono fun y hy => hy.deriv
  have E2 : ∀ᶠ y in 𝓝 c, HasDerivAt (fun y => deriv langerPhi (v y) * deriv v y)
      (deriv (deriv langerPhi) (v y) * deriv v y * deriv v y + deriv langerPhi (v y) * deriv (deriv v) y) y := by
    filter_upwards [hΦ, hvd, hv1d] with y hy hyd hy1d
    have h1' : HasDerivAt (fun y => deriv langerPhi (v y))
        (deriv (deriv langerPhi) (v y) * deriv v y) y :=
      HasDerivAt.comp y hy.deriv.differentiableAt.hasDerivAt hyd.hasDerivAt
    exact (h1'.mul hy1d.hasDerivAt)
  have hFdef : (fun q => langerPhi (u q - 1)) = fun q => langerPhi (v q) := rfl
  rw [hFdef]
  have p1 : deriv (fun q => langerPhi (v q)) c = 2 * deriv u c := by
    rw [E1'.self_of_nhds]
    simp only [hv0, deriv_langerPhi_zero, hdv]
  have p2 : deriv (deriv (fun q => langerPhi (v q))) c =
      2 * deriv (deriv u) c - 2 / 3 * deriv u c ^ 2 := by
    rw [E1'.deriv_eq, E2.self_of_nhds.deriv]
    simp only [hv0, deriv_langerPhi_zero, deriv2_langerPhi_zero, hdv]
    ring
  have E3 : deriv (deriv (fun q => langerPhi (v q))) =ᶠ[𝓝 c] fun y =>
      deriv (deriv langerPhi) (v y) * deriv v y * deriv v y
        + deriv langerPhi (v y) * deriv (deriv v) y :=
    E1'.deriv.trans (E2.mono fun y hy => hy.deriv)
  have hΦc : AnalyticAt ℝ langerPhi (v c) := by rw [hv0]; exact analyticAt_langerPhi
  have h2c : HasDerivAt (fun y => deriv (deriv langerPhi) (v y))
      (deriv (deriv (deriv langerPhi)) (v c) * deriv v c) c :=
    HasDerivAt.comp c hΦc.deriv.deriv.differentiableAt.hasDerivAt hvdc.hasDerivAt
  have h1c : HasDerivAt (fun y => deriv langerPhi (v y))
      (deriv (deriv langerPhi) (v c) * deriv v c) c :=
    HasDerivAt.comp c hΦc.deriv.differentiableAt.hasDerivAt hvdc.hasDerivAt
  have hg2 := ((h2c.mul hv1dc.hasDerivAt).mul hv1dc.hasDerivAt).add
    (h1c.mul hv2d.hasDerivAt)
  have p3 : deriv (deriv (deriv (fun q => langerPhi (v q)))) c =
      2 * deriv (deriv (deriv u)) c - 2 * deriv u c * deriv (deriv u) c
        + 8 / 15 * deriv u c ^ 3 := by
    have hg2' : HasDerivAt (fun y => deriv (deriv langerPhi) (v y) * deriv v y * deriv v y
        + deriv langerPhi (v y) * deriv (deriv v) y) _ c := hg2
    rw [E3.deriv_eq, hg2'.deriv]
    simp only [Pi.mul_apply, hv0, deriv_langerPhi_zero, deriv2_langerPhi_zero, deriv3_langerPhi_zero, hdv]
    ring
  exact ⟨p1, p2, p3⟩

/-- info: 'FormalResearch.Special.langerF_jets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langerF_jets

end FormalResearch.Special
