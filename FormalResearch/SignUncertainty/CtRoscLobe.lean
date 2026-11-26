module

public import Mathlib
public import FormalResearch.SignUncertainty.HankelTransportMass
public import FormalResearch.SignUncertainty.HankelBandChart
public import FormalResearch.SignUncertainty.DeepLobeMass

/-!
# `ct:dyadic` (4), mass identity and the lobe (pieces `T2`, `T3` of `CtRoscBook`)

`constant_terms_lower.tex`, `ct:dyadic` (4): `∫_{-R}^R f_c du = ∫_{-R'}^{φ(R)} Ψ̃ dx`, the mass identity `∫_0^∞ dm = ε f(0)` (`gt:7.7p` (c), `(ct:gvac-def)`) and the
exponentially small lobe `ξ < ξ(x)`, `x ≥ 0` of `dm` (`lem:radial-compactness`, `deep_lobe_mass_thm`).  In the Hankel variable `Δ = cξ`:

* `hankelXi_pos_side`: on the positive side of the Langer chart `π²ξ(x) - 1 ≤ -x/(2K)`, `K = langerScale c` (the mirror of `hankelXi_w_bounds`);
* `deep_lobe_at`, `psi_abs_tail`: `∫_{Ioc 0 (cξ(x))} |f| ρ₀ ≤ 8(e^{-5 (k x)^{3/2}} + e^{-c/25})` and the same bound for `∫_{x₁}^{x₂} |Re Ψ̃|` up to `(x₂ - x₁) r_∞`,
  `k = 1/(2κπ²)` (`langerLobeK`);
* `ct_mass_split`: `ε f(0) = ∫_{cξ(a)}^{cξ(-r)} ρ₀ f + ∫_{Δ > cξ(-r)} ρ₀ f + O(lobe)`; `ct_psi_mass`: `∫_{-r}^a Re Ψ̃ = ∫_{cξ(a)}^{cξ(-r)} ρ₀ f + O((r+a) r_∞)`.

All proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

namespace FormalResearch.SignUncertainty

/-- `k = 1/(2κπ²)`: `c ξ(x) ≤ c/π² - (k x) c^{1/3}` for `0 ≤ x ≤ A`. -/
noncomputable def langerLobeK : ℝ := 1 / (2 * langerKappa * π ^ 2)

lemma langerLobeK_pos : 0 < langerLobeK := by
  unfold langerLobeK; have := langerKappa_pos; positivity

/-- **The positive side of the Langer chart**: for `0 ≤ x ≤ A`, `π²ξ(x) - 1 ≤ -x/(2K)`. -/
lemma hankelXi_pos_side {c x : ℝ} (hc : 0 < c) (hx : |x| ≤ langerRadius c) (hx0 : 0 ≤ x) :
    Real.pi ^ 2 * hankelXi c x - 1 ≤ -x / (2 * langerScale c) := by
  have hK := langerScale_pos hc
  have hx' : |x| ≤ langerScale c * 4.94e-4 := hx
  obtain ⟨hreal, hre⟩ := chartYinv_real_point hc hx'
  set y : ℝ := x / langerScale c with hy
  set w : ℝ := (chartYinv etaC (y : ℂ)).re with hw
  have hyn : ‖(y : ℂ)‖ ≤ 4.94e-4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, hy, abs_div, abs_of_pos hK, div_le_iff₀ hK]; linarith
  obtain ⟨hmem, hspec⟩ := chartYinv_spec etaC (exists_chartY_small langerEta_etaC hyn)
  rw [hreal] at hspec
  have hwn : ‖(w : ℂ)‖ ≤ 1e-3 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; linarith [(abs_le.mp hre).1, (abs_le.mp hre).2]
  have h := norm_chartY_add_le langerEta_etaC hwn
  rw [hspec, ← Complex.ofReal_add, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs] at h
  have hy0 : 0 ≤ y := div_nonneg hx0 hK.le
  have hab := abs_le.mp h
  have hxi : Real.pi ^ 2 * hankelXi c x - 1 = w := by
    unfold hankelXi
    have : Real.pi ^ 2 ≠ 0 := by positivity
    rw [← hy, ← hw]; field_simp; ring
  rw [hxi]
  have hwnp : w ≤ 0 := by
    by_contra hneg
    push Not at hneg
    rw [abs_of_pos hneg] at hab
    linarith [hab.1, hab.2]
  rw [abs_of_nonpos hwnp] at hab
  have : w ≤ -y / 2 := by linarith [hab.1, hab.2]
  calc w ≤ -y / 2 := this
    _ = -x / (2 * langerScale c) := by rw [hy]; field_simp

/-- **The lobe at `x ≥ 0`** (`deep_lobe_mass_thm` at the scale `k x`): for `0 ≤ x ≤ A` with `k x ≥ 1`,
`∫_{(0, cξ(x)]} |f| ρ₀ ≤ 8(e^{-5 (k x)^{3/2}} + e^{-c/25})` (`M[f] = 1`). -/
lemma deep_lobe_at {c ε : ℝ} (hc : 3e6 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) {x : ℝ} (hx0 : 0 ≤ x) (hxA : x ≤ langerRadius c)
    (hk : 1 ≤ langerLobeK * x) :
    ∫ u in Ioc (0 : ℝ) (c * hankelXi c x), |f u| * hankelRho0 c u ≤
      8 * (Real.exp (-5 * (langerLobeK * x) ^ (3 / 2 : ℝ)) + Real.exp (-(1 / 25) * c)) := by
  have hc0 : 0 < c := by linarith
  have hxa : |x| ≤ langerRadius c := abs_le.2 ⟨by linarith, hxA⟩
  have hK := langerScale_pos hc0
  have hside := hankelXi_pos_side hc0 hxa hx0
  have hU : c * hankelXi c x ≤ c / π ^ 2 - (langerLobeK * x) * c ^ (1 / 3 : ℝ) := by
    have hpi : 0 < π ^ 2 := by positivity
    have h1 : hankelXi c x ≤ 1 / π ^ 2 + (-x / (2 * langerScale c)) / π ^ 2 := by
      rw [← add_div]
      rw [le_div_iff₀ hpi]; linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hc0.le
    have e : c * (1 / π ^ 2 + (-x / (2 * langerScale c)) / π ^ 2) =
        c / π ^ 2 - (langerLobeK * x) * c ^ (1 / 3 : ℝ) := by
      unfold langerLobeK langerScale
      have h3 : c = c ^ (1 / 3 : ℝ) * c ^ (2 / 3 : ℝ) := by rw [← Real.rpow_add hc0]; norm_num
      have hκ := langerKappa_pos
      have hc23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
      have hc13 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
      field_simp
      linear_combination (-x) * h3
    linarith
  have hdeep := deep_lobe_mass_thm (by linarith : 56 ≤ c) hf hε (R := langerLobeK * x) hk
  rw [hM] at hdeep
  have hint := abs_mul_rho0_integrableOn hc0 hf.int
  have hmono : ∫ u in Ioc (0 : ℝ) (c * hankelXi c x), |f u| * hankelRho0 c u ≤
      ∫ u in Ioo (0 : ℝ) (c / π ^ 2 - (langerLobeK * x) * c ^ (1 / 3 : ℝ)), |f u| * hankelRho0 c u := by
    rw [integral_Ioc_eq_integral_Ioo]
    refine setIntegral_mono_set (hint.mono_set (fun u hu => hu.1)) ?_
      (Filter.Eventually.of_forall fun u hu => ⟨hu.1, lt_of_lt_of_le hu.2 hU⟩)
    exact ae_restrict_of_forall_mem measurableSet_Ioo fun u hu =>
      mul_nonneg (abs_nonneg _) (hankelRho0_nonneg hc0 (le_of_lt hu.1))
  refine hmono.trans (hdeep.trans ?_)
  rw [mul_one]

/-- **`∫_{x₁}^{x₂} |Re Ψ̃|` beyond the lobe scale** (`x₁ ≥ 1/k`): `≤ 8(e^{-5 (k x₁)^{3/2}} + e^{-c/25}) + (x₂ - x₁) r_∞`. -/
lemma psi_abs_tail {c ε : ℝ} (hc : 3e6 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) {x₁ x₂ : ℝ} (h1 : 0 ≤ x₁) (h12 : x₁ ≤ x₂)
    (h2 : x₂ ≤ langerRadius c) (hk : 1 ≤ langerLobeK * x₁) :
    ∫ x in x₁..x₂, |hankelPsiR c f x| ≤
      8 * (Real.exp (-5 * (langerLobeK * x₁) ^ (3 / 2 : ℝ)) + Real.exp (-(1 / 25) * c)) +
        (x₂ - x₁) * hankelRinf c := by
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have ha1 : |x₁| ≤ langerRadius c := abs_le.2 ⟨by linarith [langerRadius_pos hc0], by linarith⟩
  have ha2 : |x₂| ≤ langerRadius c := abs_le.2 ⟨by linarith [langerRadius_pos hc0], h2⟩
  have hG := hankel_transport_G hc5 hf hε hM (G := fun v => |v|) continuous_abs hankelG_abs
    (fun l v hl => by rw [abs_mul, abs_of_nonneg hl]) ha1 ha2 h12
  beta_reduce at hG
  rw [abs_le] at hG
  have hmono := hankel_phi_anti hc0 ha1 ha2 h12
  have hp0 : 0 < c * hankelXi c x₂ := mul_pos hc0 (hankelXi_pos hc0 ha2)
  have hle : ∫ u in (c * hankelXi c x₂)..(c * hankelXi c x₁), hankelRho0 c u * |f u| ≤
      ∫ u in Ioc (0 : ℝ) (c * hankelXi c x₁), |f u| * hankelRho0 c u := by
    rw [intervalIntegral.integral_of_le hmono]
    have hint := (hankel_gA_int hc0 hf).mono_set (fun u (hu : u ∈ Ioc 0 (c * hankelXi c x₁)) => hu.1)
    have hint' : IntegrableOn (fun u => |f u| * hankelRho0 c u) (Ioc 0 (c * hankelXi c x₁)) := by
      simpa only [mul_comm] using hint
    calc ∫ u in Ioc (c * hankelXi c x₂) (c * hankelXi c x₁), hankelRho0 c u * |f u|
        ≤ ∫ u in Ioc 0 (c * hankelXi c x₁), hankelRho0 c u * |f u| := by
          refine setIntegral_mono_set hint ?_ (Filter.Eventually.of_forall fun u hu => ⟨hp0.trans hu.1, hu.2⟩)
          exact ae_restrict_of_forall_mem measurableSet_Ioc fun u hu =>
            mul_nonneg (hankelRho0_nonneg hc0 hu.1.le) (abs_nonneg _)
      _ = _ := by simp only [mul_comm]
  have hlobe := deep_lobe_at hc hf hε hM h1 (h12.trans h2) hk
  linarith [hG.1, hG.2]

/-- **Mass identity on the window** (`gt:7.7p` (c), `(ct:gvac-def)`): for `0 ≤ a ≤ A`, `k a ≥ 1`, `0 < r ≤ A`,
`|ε f(0) - ∫_{cξ(a)}^{cξ(-r)} ρ₀ f - ∫_{Δ > cξ(-r)} ρ₀ f| ≤ 8(e^{-5 (k a)^{3/2}} + e^{-c/25})`. -/
lemma ct_mass_split {c ε : ℝ} (hc : 3e6 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) {a r : ℝ} (ha0 : 0 ≤ a) (haA : a ≤ langerRadius c)
    (hr0 : 0 ≤ r) (hrA : r ≤ langerRadius c) (hk : 1 ≤ langerLobeK * a) :
    |ε * f 0 - (∫ u in (c * hankelXi c a)..(c * hankelXi c (-r)), hankelRho0 c u * f u) -
        ∫ u in Ioi (c * hankelXi c (-r)), hankelRho0 c u * f u| ≤
      8 * (Real.exp (-5 * (langerLobeK * a) ^ (3 / 2 : ℝ)) + Real.exp (-(1 / 25) * c)) := by
  have hc0 : 0 < c := by linarith
  have haa : |a| ≤ langerRadius c := abs_le.2 ⟨by linarith [langerRadius_pos hc0], haA⟩
  have hra : |-r| ≤ langerRadius c := by rw [abs_neg, abs_of_nonneg hr0]; exact hrA
  have hmono := hankel_phi_anti hc0 hra haa (by linarith)
  have hmono' : c * hankelXi c a ≤ c * hankelXi c (-r) := hankel_phi_anti hc0 hra haa (by linarith)
  have hp0 : 0 < c * hankelXi c a := mul_pos hc0 (hankelXi_pos hc0 haa)
  have hgF := hankel_gF_int hf
  have hsplit := hankel_split3 hgF hp0.le hmono'
  rw [hankel_gF_integral hc0 hf] at hsplit
  have hlobe := deep_lobe_at hc hf hε hM ha0 haA hk
  have habs : |∫ u in Ioc (0 : ℝ) (c * hankelXi c a), hankelRho0 c u * f u| ≤
      ∫ u in Ioc (0 : ℝ) (c * hankelXi c a), |f u| * hankelRho0 c u := by
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    simp only [abs_mul, abs_of_nonneg (hankelRho0_nonneg hc0 hu.1.le), mul_comm]
  have e : ε * f 0 - (∫ u in (c * hankelXi c a)..(c * hankelXi c (-r)), hankelRho0 c u * f u) -
      ∫ u in Ioi (c * hankelXi c (-r)), hankelRho0 c u * f u =
        ∫ u in Ioc (0 : ℝ) (c * hankelXi c a), hankelRho0 c u * f u := by linarith
  rw [e]
  exact habs.trans hlobe

/-- **`∫_{-r}^a Re Ψ̃` in the Hankel variable** (`hankel_transport_G`, `G = id`): `|∫_{-r}^a Re Ψ̃ - ∫_{cξ(a)}^{cξ(-r)} ρ₀ f| ≤ (a + r) r_∞`. -/
lemma ct_psi_mass {c ε : ℝ} (hc : 3e6 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) {a r : ℝ} (ha : |a| ≤ langerRadius c)
    (hr : |-r| ≤ langerRadius c) (har : -r ≤ a) :
    |(∫ x in (-r)..a, hankelPsiR c f x) - ∫ u in (c * hankelXi c a)..(c * hankelXi c (-r)), hankelRho0 c u * f u| ≤
      (a - -r) * hankelRinf c := by
  have hG := hankel_transport_G (by linarith : (5000 : ℝ) ≤ c) hf hε hM (G := fun v => v) continuous_id
    (fun s t => le_rfl) (fun l v hl => rfl) hr ha har
  simpa using hG

/-- info: 'FormalResearch.SignUncertainty.ct_mass_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_mass_split

/-- info: 'FormalResearch.SignUncertainty.psi_abs_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms psi_abs_tail

/-- info: 'FormalResearch.SignUncertainty.deep_lobe_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deep_lobe_at

end FormalResearch.SignUncertainty
