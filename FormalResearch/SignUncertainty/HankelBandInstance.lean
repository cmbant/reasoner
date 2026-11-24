module

public import FormalResearch.SignUncertainty.HankelBandParams
public import FormalResearch.SignUncertainty.HankelBandMeasure

/-!
# The Hankel `BandReductionInstance` (`teb:mellin`, `u1cl:rep`; M5-S5)

For `c ≥ 3·10⁶`, `ε = ±1`, `f ∈ 𝒜_c^ε` with `M[f] = 1`, a level `-3 ≤ u_T ≤ 0` and `f ≥ 0` on
`[c ξ(u_T), ∞)`, `hankelBandInstance` is the `BandReductionInstance hankelBandParams` with:

* `W̃ = hankelWtS` (closed-strip form of `e^{-cℋ} M̃_f(c(1-ζ))`; `M = 1/2`);
* `dm = c (fρ₀)(cξ) dξ` split into `hankelDmPos`, `hankelDmNeg`, threshold `T = ξ(u_T)`;
* `E_sub = ∅`, `K_edge = K₀(iτ, ξ)⁻¹ = a_0(τ) e^{-icΦ(τ; log π²ξ)}`, `a_2 = 1`, `R_0 = 0`;
* `ν(τ) = τ`, `μ(ξ) = log π²ξ` (`0` for `ξ ≤ 0`), `m(τ) = log((πτ/2)/tanh(πτ/2))`;
* `ũ = hankelBandU c`, `Δ = hankelXi c`, `R = b² c^{2/3}`, `τ_0 = m⁻¹ ∘ μ`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.ModularBootstrap.StripBand FormalResearch.CohnElkies

/-- `μ(ξ) = log π²ξ` for `ξ > 0`, `0` otherwise. -/
noncomputable def hankelBandMu (ξ : ℝ) : ℝ := if 0 < ξ then Real.log (Real.pi ^ 2 * ξ) else 0

/-- The stationary point `τ_0 = m⁻¹(μ)` (`0` when `μ ≤ 0`). -/
noncomputable def hankelBandTau0 (ξ : ℝ) : ℝ :=
  if h : 0 < hankelBandMu ξ then Classical.choose (hankelEdgeM_exists_root h.le) else 0

lemma hankelBandTau0_nonneg (ξ : ℝ) : 0 ≤ hankelBandTau0 ξ := by
  unfold hankelBandTau0
  split_ifs with h
  · exact (Classical.choose_spec (hankelEdgeM_exists_root h.le)).1
  · exact le_rfl

lemma hankelBandTau0_root {ξ : ℝ} (h : 0 < hankelBandMu ξ) :
    hankelEdgeM (hankelBandTau0 ξ) = hankelBandMu ξ := by
  unfold hankelBandTau0
  rw [dif_pos h]
  exact (Classical.choose_spec (hankelEdgeM_exists_root h.le)).2

lemma hankelBandTau0_zero {ξ : ℝ} (h : hankelBandMu ξ ≤ 0) : hankelBandTau0 ξ = 0 := by
  unfold hankelBandTau0
  rw [dif_neg (not_lt.mpr h)]

lemma hankelBandTau0_sq_le {ξ : ℝ} (h0 : 0 ≤ hankelBandMu ξ) (h : hankelBandMu ξ < 3 / 16) :
    hankelBandTau0 ξ ^ 2 ≤ 16 / 3 * hankelBandMu ξ := by
  rcases h0.eq_or_lt with h1 | h1
  · rw [hankelBandTau0_zero h1.symm.le, ← h1]; norm_num
  · exact hankelEdgeM_sq_le (hankelBandTau0_nonneg ξ) (hankelBandTau0_root h1) h

lemma hankelBand_langerScale_ge {c : ℝ} (hc : 3e6 ≤ c) : 1e4 ≤ langerScale c := by
  have h1 := hankel_rpow23_ge hc
  have hk := hankelLangerKappa_bounds
  unfold langerScale
  nlinarith [mul_le_mul h1 hk.1 (by norm_num) (by linarith)]

/-- `(A_0 c^{-1/3})² = 32 / K`. -/
lemma hankelBand_A0_sq {c : ℝ} (hc : 0 < c) :
    (hankelBandParams.A_0 * c ^ (-(1 / 3 : ℝ))) ^ 2 = 32 / langerScale c := by
  have hk := langerKappa_pos
  have hc23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have e : (c ^ (-(1 / 3 : ℝ))) ^ 2 = (c ^ (2 / 3 : ℝ))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le, ← Real.rpow_neg hc.le]; norm_num
  show (Real.sqrt (32 / langerKappa) * c ^ (-(1 / 3 : ℝ))) ^ 2 = _
  rw [mul_pow, Real.sq_sqrt (by positivity), e]
  unfold langerScale
  field_simp

/-- Below the threshold: `τ_0 ≤ A_0 c^{-1/3}`. -/
theorem hankelBandTau0_below {c u_T ξ : ℝ} (hc : 3e6 ≤ c) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T)
    (hξ : ξ < hankelXi c u_T) : hankelBandTau0 ξ ≤ hankelBandParams.A_0 * c ^ (-(1 / 3 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hB : 0 ≤ hankelBandParams.A_0 * c ^ (-(1 / 3 : ℝ)) :=
    mul_nonneg hankelBandParams.hA_0.le (Real.rpow_nonneg hc0.le _)
  rcases le_or_gt (hankelBandMu ξ) 0 with h0 | h0
  · rw [hankelBandTau0_zero h0]; exact hB
  · have hξ0 : 0 < ξ := by
      by_contra hneg
      unfold hankelBandMu at h0
      rw [if_neg hneg] at h0
      exact lt_irrefl _ h0
    have hu : |u_T| ≤ langerRadius c := by
      rw [abs_of_nonpos hu0]; linarith [(hankel_radius_ge hc).1]
    have hmu := hankelBand_mu_below hc0 hu0 hu hξ0 hξ
    have hK := hankelBand_langerScale_ge hc
    have hmu' : hankelBandMu ξ = Real.log (Real.pi ^ 2 * ξ) := by unfold hankelBandMu; rw [if_pos hξ0]
    have hμ6 : hankelBandMu ξ ≤ 6 / langerScale c := by
      rw [hmu']
      refine hmu.trans ?_
      rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
    have hμsmall : hankelBandMu ξ < 3 / 16 := by
      refine lt_of_le_of_lt hμ6 ?_
      rw [div_lt_iff₀ (by linarith)]; nlinarith
    have hsq := hankelBandTau0_sq_le h0.le hμsmall
    have hfin : hankelBandTau0 ξ ^ 2 ≤ (hankelBandParams.A_0 * c ^ (-(1 / 3 : ℝ))) ^ 2 := by
      rw [hankelBand_A0_sq hc0]
      have : 16 / 3 * hankelBandMu ξ ≤ 32 / langerScale c := by
        have : 16 / 3 * hankelBandMu ξ ≤ 16 / 3 * (6 / langerScale c) := by linarith
        refine this.trans ?_
        rw [← sub_nonneg]
        have : 32 / langerScale c - 16 / 3 * (6 / langerScale c) = 0 := by field_simp; norm_num
        linarith
      linarith
    by_contra hlt
    push Not at hlt
    have := pow_lt_pow_left₀ hlt hB (two_ne_zero)
    linarith

/-- On the band: `τ_0² ≤ C_τ c^{-2/3} (-ũ)` and `0 ≤ -ũ`. -/
theorem hankelBandTau0_band {c u_T R ξ : ℝ} (hc : 3e6 ≤ c) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T)
    (hR0 : 0 ≤ R) (hR : R ≤ langerRadius c)
    (hξ : ξ ∈ Icc (hankelXi c u_T) (hankelXi c (-R))) :
    hankelBandTau0 ξ ^ 2 ≤ hankelBandParams.C_τ * c ^ (-(2 / 3 : ℝ)) * (-hankelBandU c ξ) := by
  have hc0 : 0 < c := by linarith
  have hu : |u_T| ≤ langerRadius c := by
    rw [abs_of_nonpos hu0]; linarith [(hankel_radius_ge hc).1]
  obtain ⟨hm0, hm1, hm2⟩ := hankelBand_mu_band hc0 hu0 hu hR0 hR hξ
  have hT := hankelXi_w_bounds hc0 hu hu0
  have hpi : 0 < Real.pi ^ 2 := by positivity
  have hξ0 : 0 < ξ := by
    have : 0 ≤ Real.pi ^ 2 * hankelXi c u_T - 1 := hT.1
    nlinarith [hξ.1]
  have hmu' : hankelBandMu ξ = Real.log (Real.pi ^ 2 * ξ) := by unfold hankelBandMu; rw [if_pos hξ0]
  rw [← hmu'] at hm0 hm1 hm2
  have hw0 : 0 ≤ Real.pi ^ 2 * ξ - 1 := by nlinarith [hξ.1, hT.1]
  have hU := hankelBandU_le hc0 hw0 (by
    have hRb := hankelXi_w_bounds hc0 (x := -R) (by rw [abs_neg, abs_of_nonneg hR0]; exact hR) (by linarith)
    nlinarith [hξ.2, hRb.2.1])
  have hK := hankelBand_langerScale_ge hc
  have hUnn : 0 ≤ -hankelBandU c ξ := by nlinarith
  have hsq := hankelBandTau0_sq_le hm0 (by linarith)
  have hc23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hneg : c ^ (-(2 / 3 : ℝ)) = (c ^ (2 / 3 : ℝ))⁻¹ := Real.rpow_neg hc0.le _
  have hk := langerKappa_pos
  have hKdef : langerScale c = c ^ (2 / 3 : ℝ) * langerKappa := rfl
  show _ ≤ 11 / langerKappa * c ^ (-(2 / 3 : ℝ)) * _
  rw [hneg]
  have h1 : 16 / 3 * hankelBandMu ξ ≤ 16 / 3 * (2 * (-hankelBandU c ξ) / langerScale c) := by linarith
  refine hsq.trans (h1.trans ?_)
  rw [hKdef]
  have hq : 0 ≤ -hankelBandU c ξ / (c ^ (2 / 3 : ℝ) * langerKappa) := div_nonneg hUnn (by positivity)
  have e1 : 16 / 3 * (2 * -hankelBandU c ξ / (c ^ (2 / 3 : ℝ) * langerKappa)) =
      32 / 3 * (-hankelBandU c ξ / (c ^ (2 / 3 : ℝ) * langerKappa)) := by ring
  have e2 : 11 / langerKappa * (c ^ (2 / 3 : ℝ))⁻¹ * -hankelBandU c ξ =
      11 * (-hankelBandU c ξ / (c ^ (2 / 3 : ℝ) * langerKappa)) := by field_simp
  rw [e1, e2]
  nlinarith

/-- info: 'FormalResearch.SignUncertainty.hankelBandTau0_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBandTau0_below

/-- info: 'FormalResearch.SignUncertainty.hankelBandTau0_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBandTau0_band

end FormalResearch.SignUncertainty
