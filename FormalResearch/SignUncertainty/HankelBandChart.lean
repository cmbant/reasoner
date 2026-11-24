module

public import FormalResearch.SignUncertainty.HankelTransportInt

/-!
# Chart comparison for the band `[T, Δ(-R)]` (`teb:MS3`, M5-S5)

`hankelBandU c ξ = c^{2/3} κ Re y(π²ξ - 1)` is the Langer variable `ũ` as a function of `ξ`.  With
`w = π²ξ - 1`:

* `hankelBandU_le`: `ũ(ξ) ≤ -K w/2` for `0 ≤ w ≤ 10⁻³`, `K = langerScale c`, from `‖y(w) + w‖ ≤ 1.9·10⁻³ ‖w‖`
  (`norm_chartY_add_le`);
* `hankelXi_w_bounds`: for `x ≤ 0` in the Langer disc, `0 ≤ π² ξ(x) - 1 ≤ min(5·10⁻⁴, -2x/K)`;
* `hankelBand_mu_band`, `hankelBand_mu_below`: the bounds on `μ(ξ) = log(π² ξ)` used for the stationary
  points `τ₀` on the band `[ξ(u_T), ξ(-R)]` and below the threshold `ξ(u_T)`.
-/

@[expose] public section

open Complex Set Filter Topology Metric
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `ũ(ξ) = K Re y(π² ξ - 1)`, `K = c^{2/3} κ`. -/
noncomputable def hankelBandU (c ξ : ℝ) : ℝ :=
  langerScale c * (chartY etaC (((Real.pi ^ 2 * ξ - 1 : ℝ)) : ℂ)).re

theorem hankelBandU_le {c : ℝ} (hc : 0 < c) {ξ : ℝ} (h0 : 0 ≤ Real.pi ^ 2 * ξ - 1)
    (h1 : Real.pi ^ 2 * ξ - 1 ≤ 1e-3) :
    hankelBandU c ξ ≤ -(langerScale c * (Real.pi ^ 2 * ξ - 1) / 2) := by
  set w : ℝ := Real.pi ^ 2 * ξ - 1 with hw
  have hK := langerScale_pos hc
  have hn : ‖(w : ℂ)‖ ≤ 1e-3 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have h := norm_chartY_add_le langerEta_etaC hn
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0] at h
  have hre := Complex.abs_re_le_norm (chartY etaC (w : ℂ) + (w : ℂ))
  have h2 : |(chartY etaC (w : ℂ)).re + w| ≤ 1.9e-3 * w := by
    have : (chartY etaC (w : ℂ) + (w : ℂ)).re = (chartY etaC (w : ℂ)).re + w := by simp
    rw [this] at hre
    exact hre.trans h
  have h3 := (abs_le.mp h2).2
  unfold hankelBandU
  have h4 : (chartY etaC (w : ℂ)).re ≤ -(w / 2) := by linarith
  nlinarith

theorem hankelXi_w_bounds {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : |x| ≤ langerRadius c) (hx0 : x ≤ 0) :
    0 ≤ Real.pi ^ 2 * hankelXi c x - 1 ∧ Real.pi ^ 2 * hankelXi c x - 1 ≤ 5e-4 ∧
      Real.pi ^ 2 * hankelXi c x - 1 ≤ -2 * x / langerScale c := by
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
  have hy0 : y ≤ 0 := by rw [hy]; exact div_nonpos_of_nonpos_of_nonneg hx0 hK.le
  have hab := abs_le.mp h
  have hwabs := abs_le.mp hre
  have hxi : Real.pi ^ 2 * hankelXi c x - 1 = w := by
    unfold hankelXi
    have : Real.pi ^ 2 ≠ 0 := by positivity
    rw [← hy, ← hw]; field_simp; ring
  rw [hxi]
  have hwnn : 0 ≤ w := by
    by_contra hneg
    push Not at hneg
    rw [abs_of_neg hneg] at hab
    linarith [hab.1, hab.2]
  rw [abs_of_nonneg hwnn] at hab
  refine ⟨hwnn, hwabs.2, ?_⟩
  have : w ≤ -2 * y := by linarith [hab.1, hab.2]
  calc w ≤ -2 * y := this
    _ = -2 * x / langerScale c := by rw [hy]; ring

/-- On the band `ξ(u_T) ≤ ξ ≤ ξ(-R)`: `0 ≤ μ ≤ 5·10⁻⁴` and `μ ≤ 2 (-ũ(ξ)) / K`, `μ = log π²ξ`. -/
theorem hankelBand_mu_band {c u_T R ξ : ℝ} (hc : 0 < c) (hu0 : u_T ≤ 0) (hu : |u_T| ≤ langerRadius c)
    (hR0 : 0 ≤ R) (hR : R ≤ langerRadius c)
    (hξ : ξ ∈ Icc (hankelXi c u_T) (hankelXi c (-R))) :
    0 ≤ Real.log (Real.pi ^ 2 * ξ) ∧ Real.log (Real.pi ^ 2 * ξ) ≤ 5e-4 ∧
      Real.log (Real.pi ^ 2 * ξ) ≤ 2 * (-hankelBandU c ξ) / langerScale c := by
  have hK := langerScale_pos hc
  have hT := hankelXi_w_bounds hc hu hu0
  have hRb := hankelXi_w_bounds hc (x := -R) (by rw [abs_neg, abs_of_nonneg hR0]; exact hR) (by linarith)
  have hpi : 0 < Real.pi ^ 2 := by positivity
  have hw0 : 0 ≤ Real.pi ^ 2 * ξ - 1 := by nlinarith [hξ.1, hT.1]
  have hw1 : Real.pi ^ 2 * ξ - 1 ≤ 5e-4 := by nlinarith [hξ.2, hRb.2.1]
  have hpos : 0 < Real.pi ^ 2 * ξ := by linarith
  have hmu : Real.log (Real.pi ^ 2 * ξ) ≤ Real.pi ^ 2 * ξ - 1 := Real.log_le_sub_one_of_pos hpos
  refine ⟨Real.log_nonneg (by linarith), hmu.trans hw1, ?_⟩
  have hU := hankelBandU_le hc hw0 (by linarith)
  have : Real.pi ^ 2 * ξ - 1 ≤ 2 * (-hankelBandU c ξ) / langerScale c := by
    rw [le_div_iff₀ hK]; nlinarith
  exact hmu.trans this

/-- Below the threshold: `μ(ξ) ≤ -2 u_T / K` for `0 < ξ < ξ(u_T)`. -/
theorem hankelBand_mu_below {c u_T ξ : ℝ} (hc : 0 < c) (hu0 : u_T ≤ 0) (hu : |u_T| ≤ langerRadius c)
    (hξ0 : 0 < ξ) (hξ : ξ < hankelXi c u_T) :
    Real.log (Real.pi ^ 2 * ξ) ≤ -2 * u_T / langerScale c := by
  have hT := hankelXi_w_bounds hc hu hu0
  have hpi : 0 < Real.pi ^ 2 := by positivity
  have hpos : 0 < Real.pi ^ 2 * ξ := by positivity
  have hmu := Real.log_le_sub_one_of_pos hpos
  have : Real.pi ^ 2 * ξ - 1 ≤ Real.pi ^ 2 * hankelXi c u_T - 1 := by nlinarith
  linarith [hT.2.2]

/-- info: 'FormalResearch.SignUncertainty.hankelBandU_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBandU_le

/-- info: 'FormalResearch.SignUncertainty.hankelXi_w_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelXi_w_bounds

/-- info: 'FormalResearch.SignUncertainty.hankelBand_mu_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBand_mu_band

/-- info: 'FormalResearch.SignUncertainty.hankelBand_mu_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBand_mu_below

end FormalResearch.SignUncertainty
