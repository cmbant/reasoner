module

public import FormalResearch.ModularBootstrap.Upper.Rigidity.SpectrumCorollary

/-!
# Barycentre assertion of Corollary `sr:cor` (`spectral_rigidity.tex`)

Proves the Cardy-normalised cluster barycentre convergence of Corollary `sr:cor`:
for fixed `i` and small radius `r > 0`, letting `𝒞_i(r) = {t > 0 : |u(t) - a_{i+1}| ≤ r}`,
define the Cardy-normalised moment and barycentre
`clusterBarycentre prob c ν B = (∫_{u ∈ B, t > 0} t / (2π V(c/12, t)) dν(t)) / (clusterWeight prob c ν B).toReal`.

* `cluster_barycentre_bound`: quantitative sandwich
  `|(t̄_i(r) - ξ̄ c) / c^{1/3} - c_* |a_{i+1}|| ≤ c_* r + c^{-2/3} (|a_{i+1}| + r)² / (3 β²)`.
* `cluster_barycentre_tendsto`: for every `ρ > 0` there exists `r₀ > 0` such that for `0 < r ≤ r₀`
  (isolated around `a_{i+1}`), eventually `|(t̄_i(r) - ξ̄ c_j) / c_j^{1/3} - c_* |a_{i+1}|| ≤ ρ`.
* `cluster_barycentre_diff_tendsto`, `crossing_barycentre_diff_tendsto`:
  `(t̄_2 - t̄_1) c_j^{-1/3} → (|a_2| / |a_1| - 1) A_opt` (`= c_* (|a_2| - |a_1|)`)
  for any `S : CrossingSequence prob` with `SigmaConclusion S.μS`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal Real

namespace FormalResearch.ModularBootstrap.Upper.Rigidity

open FormalResearch.ModularBootstrap Crossing FixedWeight TipFront FormalResearch.Special

/-- First moment of `t` against the Cardy-normalised cluster weight `1 / (2π V(c/12, t))`
on `{t > 0 : uAiry c t ∈ B}`. -/
noncomputable def clusterMoment (prob : FixedWeightProblem) (c : ℝ) (ν : Measure ℝ)
    (B : Set ℝ) : ℝ :=
  ∫ t in uAiry c ⁻¹' B ∩ Ioi 0, t / (2 * π * prob.cardyV (c / 12) t) ∂ν

/-- Cardy-normalised cluster barycentre `t̄_B` of `{t > 0 : uAiry c t ∈ B}`. -/
noncomputable def clusterBarycentre (prob : FixedWeightProblem) (c : ℝ) (ν : Measure ℝ)
    (B : Set ℝ) : ℝ :=
  clusterMoment prob c ν B / (clusterWeight prob c ν B).toReal

private lemma measurableSet_clusterSet (c : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    MeasurableSet (uAiry c ⁻¹' B ∩ Ioi 0) :=
  ((continuous_uAiry c).measurable hB).inter measurableSet_Ioi

private lemma continuousOn_cardyInvWeight (prob : FixedWeightProblem) {c : ℝ}
    (ha : prob.totalShift ≤ c / 12) :
    ContinuousOn (fun t => 1 / (2 * π * prob.cardyV (c / 12) t)) (Ioi 0) := by
  refine continuousOn_const.div (ContinuousOn.mul continuousOn_const
    ((continuous_cardyV prob (c / 12)).continuousOn.mono Ioi_subset_Ici_self)) ?_
  intro t ht
  exact (mul_pos (by positivity) (prob.cardyV_pos ha ht)).ne'

private lemma clusterWeight_lt_top_of_Icc (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c)
    (ha : prob.totalShift ≤ c / 12) (ν : Measure ℝ)
    [IsLocallyFiniteMeasure (spectralMeasure prob c ν)] (a r : ℝ) :
    clusterWeight prob c ν (Icc (a - r) (a + r)) ≠ ∞ := by
  let M := |a| + |r|
  have hBM : ∀ u ∈ Icc (a - r) (a + r), |u| ≤ M := fun u hu => by
    have h1 : |u - a| ≤ |r| := abs_le.2 ⟨by linarith [hu.1, le_abs_self r], by linarith [hu.2, le_abs_self r]⟩
    have := abs_sub_abs_le_abs_sub u a
    linarith [h1]
  let A : ℝ := cStar * c ^ ((1 : ℝ) / 3) * (1 + M * epsAiry c / (betaTip * xiStar))
  have hK : 0 < cStar * c ^ ((1 : ℝ) / 3) := mul_pos cStar_pos (Real.rpow_pos_of_pos hc _)
  have he_nn : 0 ≤ M * epsAiry c / (betaTip * xiStar) :=
    div_nonneg (mul_nonneg (by dsimp [M]; positivity) (epsAiry_pos hc).le)
      (mul_pos betaTip_pos xiStar_pos).le
  have hA0 : 0 ≤ A := mul_nonneg hK.le (by linarith)
  have hWu := clusterWeight_le hc ha ν measurableSet_Icc hA0 fun t _ ht => by
    have hbd := (abs_le.mp (jAiry_bounds hc (hBM _ ht))).2
    dsimp [A]; linarith
  have hμfin : spectralMeasure prob c ν (Icc (a - r) (a + r)) < ∞ := isCompact_Icc.measure_lt_top
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμfin.ne) hWu

private lemma clusterWeight_integrableOn_of_Icc (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c)
    (ha : prob.totalShift ≤ c / 12) (ν : Measure ℝ)
    [IsLocallyFiniteMeasure (spectralMeasure prob c ν)] (a r : ℝ) :
    IntegrableOn (fun t => 1 / (2 * π * prob.cardyV (c / 12) t))
      (uAiry c ⁻¹' Icc (a - r) (a + r) ∩ Ioi 0) ν ∧
    (clusterWeight prob c ν (Icc (a - r) (a + r))).toReal =
      ∫ t in uAiry c ⁻¹' Icc (a - r) (a + r) ∩ Ioi 0,
        1 / (2 * π * prob.cardyV (c / 12) t) ∂ν := by
  let E := uAiry c ⁻¹' Icc (a - r) (a + r) ∩ Ioi (0 : ℝ)
  have hEm : MeasurableSet E := measurableSet_clusterSet c measurableSet_Icc
  let w : ℝ → ℝ := fun t => 1 / (2 * π * prob.cardyV (c / 12) t)
  have hw_cont : ContinuousOn w (Ioi 0) := continuousOn_cardyInvWeight prob ha
  have hw_meas : AEStronglyMeasurable w (ν.restrict E) :=
    (hw_cont.mono inter_subset_right).aestronglyMeasurable hEm
  have hw_nn : ∀ t ∈ E, 0 ≤ w t := fun t ht => by
    dsimp [w]; exact one_div_nonneg.mpr (mul_pos (by positivity) (prob.cardyV_pos ha ht.2)).le
  have hfin_lt : (∫⁻ t in E, ‖w t‖ₑ ∂ν) < ∞ := by
    have heq : (∫⁻ t in E, ‖w t‖ₑ ∂ν) = clusterWeight prob c ν (Icc (a - r) (a + r)) := by
      unfold clusterWeight
      refine setLIntegral_congr_fun hEm fun t ht => ?_
      rw [Real.eNorm_eq_ofReal_abs, abs_of_nonneg (hw_nn t ht)]
    rw [heq]
    exact lt_top_iff_ne_top.mpr (clusterWeight_lt_top_of_Icc prob hc ha ν a r)
  have hint : IntegrableOn w E ν := ⟨hw_meas, hfin_lt⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem hEm hw_nn) hw_meas]
  rfl

/-- Quantitative barycentre bound on an arbitrary separated interval `[a_i - r, a_i + r]`:
if `clusterWeight > 0`, then `(t̄_i - ξ̄ c) / c^{1/3}` lies within
`c_* r + c^{-2/3} (|a_i| + r)² / (3 β²)` of `c_* |a_i|`. -/
theorem cluster_barycentre_bound {prob : FixedWeightProblem} {c : ℝ} (hc : 0 < c)
    (ha : prob.totalShift ≤ c / 12) (ν : Measure ℝ)
    [IsLocallyFiniteMeasure (spectralMeasure prob c ν)]
    (i : ℕ) {r : ℝ} (_hr : 0 < r)
    (hW_pos : 0 < (clusterWeight prob c ν (Icc (airyNode i - r) (airyNode i + r))).toReal) :
    |(clusterBarycentre prob c ν (Icc (airyNode i - r) (airyNode i + r)) - xiBar * c) /
        c ^ ((1 : ℝ) / 3) - cStar * abs (airyNode i)| ≤
      cStar * r + epsAiry c * (|airyNode i| + r) ^ 2 / (3 * betaTip ^ 2) := by
  let B := Icc (airyNode i - r) (airyNode i + r)
  let E := uAiry c ⁻¹' B ∩ Ioi (0 : ℝ)
  have hEm : MeasurableSet E := measurableSet_clusterSet c measurableSet_Icc
  let w : ℝ → ℝ := fun t => 1 / (2 * π * prob.cardyV (c / 12) t)
  obtain ⟨hw_int, hw_eq⟩ := clusterWeight_integrableOn_of_Icc prob hc ha ν (airyNode i) r
  let η : ℝ := cStar * r + epsAiry c * (|airyNode i| + r) ^ 2 / (3 * betaTip ^ 2)
  let L : ℝ := xiBar * c + (cStar * |airyNode i| - η) * c ^ ((1 : ℝ) / 3)
  let U : ℝ := xiBar * c + (cStar * |airyNode i| + η) * c ^ ((1 : ℝ) / 3)
  have hcp : 0 < c ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc _
  have hpos_in_E : ∀ t ∈ E, L ≤ t ∧ t ≤ U := by
    intro t ht
    have hu : |uAiry c t - airyNode i| ≤ r := abs_le.2 ⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩
    have hcp_bd := cluster_position hc ht.2.le hu
    have hneg_abs : -airyNode i = |airyNode i| := (abs_of_neg (airyNode_neg i)).symm
    rw [hneg_abs] at hcp_bd
    obtain ⟨hlo, hhi⟩ := abs_le.mp hcp_bd
    have hm1 := mul_le_mul_of_nonneg_right hlo hcp.le
    have hm2 := mul_le_mul_of_nonneg_right hhi hcp.le
    rw [sub_mul, div_mul_cancel₀ _ hcp.ne'] at hm1 hm2
    have heq_l : L = xiBar * c + cStar * |airyNode i| * c ^ ((1 : ℝ) / 3) - η * c ^ ((1 : ℝ) / 3) := by
      dsimp [L]; ring
    have heq_u : U = xiBar * c + cStar * |airyNode i| * c ^ ((1 : ℝ) / 3) + η * c ^ ((1 : ℝ) / 3) := by
      dsimp [U]; ring
    constructor <;> [rw [heq_l]; rw [heq_u]] <;> linarith only [hm1, hm2]
  let Mt : ℝ := max |L| |U|
  have hM_int : IntegrableOn (fun t => t * w t) E ν := by
    have hcont : ContinuousOn (fun t : ℝ => t * w t) (Ioi 0) :=
      continuousOn_id.mul (continuousOn_cardyInvWeight prob ha)
    refine (hw_int.const_mul Mt).mono' ((hcont.mono inter_subset_right).aestronglyMeasurable hEm) ?_
    filter_upwards [ae_restrict_mem hEm] with t ht
    have ht_le : |t| ≤ Mt := by
      have ⟨hL, hU⟩ := hpos_in_E t ht
      have hL' : -Mt ≤ L := by
        have h1 : |L| ≤ Mt := le_max_left _ _
        linarith [neg_abs_le L]
      have hU' : U ≤ Mt := (le_abs_self U).trans (le_max_right _ _)
      exact abs_le.mpr ⟨hL'.trans hL, hU.trans hU'⟩
    have hw_nn : 0 ≤ w t :=
      one_div_nonneg.mpr (mul_pos (by positivity) (prob.cardyV_pos ha ht.2)).le
    have hMt_nn : 0 ≤ Mt := (abs_nonneg L).trans (le_max_left _ _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw_nn]
    exact mul_le_mul_of_nonneg_right ht_le hw_nn
  have hw_nn : ∀ t ∈ E, 0 ≤ w t := fun t ht =>
    one_div_nonneg.mpr (mul_pos (by positivity) (prob.cardyV_pos ha ht.2)).le
  have hmoment_eq : clusterMoment prob c ν B = ∫ t in E, t * w t ∂ν := by
    unfold clusterMoment; refine setIntegral_congr_fun hEm fun t _ => ?_; dsimp [w]; ring
  have hlo_int : L * (clusterWeight prob c ν B).toReal ≤ clusterMoment prob c ν B := by
    rw [hw_eq, hmoment_eq, ← integral_const_mul]
    refine setIntegral_mono_on (hw_int.const_mul L) hM_int hEm fun t ht => ?_
    exact mul_le_mul_of_nonneg_right (hpos_in_E t ht).1 (hw_nn t ht)
  have hhi_int : clusterMoment prob c ν B ≤ U * (clusterWeight prob c ν B).toReal := by
    rw [hw_eq, hmoment_eq, ← integral_const_mul]
    refine setIntegral_mono_on hM_int (hw_int.const_mul U) hEm fun t ht => ?_
    exact mul_le_mul_of_nonneg_right (hpos_in_E t ht).2 (hw_nn t ht)
  have hbar_lo : L ≤ clusterBarycentre prob c ν B := by
    rw [clusterBarycentre, le_div_iff₀ hW_pos]; exact hlo_int
  have hbar_hi : clusterBarycentre prob c ν B ≤ U := by
    rw [clusterBarycentre, div_le_iff₀ hW_pos]; exact hhi_int
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ hcp]; dsimp [L, η] at hbar_lo; linarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hcp]; dsimp [U, η] at hbar_hi; linarith

/-- **Barycentre position limit (`sr:cor`)**: for every `i` and `ρ > 0` there is `r₀ > 0` such that
for `0 < r ≤ r₀`, eventually `(t̄_i(r) - ξ̄ c_j) / c_j^{1/3}` stays within `ρ` of `c_* |a_{i+1}|`. -/
theorem cluster_barycentre_tendsto {prob : FixedWeightProblem} {c : ℕ → ℝ} {ν : ℕ → Measure ℝ}
    (hct : Tendsto c atTop atTop) (hcpos : ∀ j, 0 < c j)
    (hshift : ∀ j, prob.totalShift ≤ c j / 12)
    [∀ j, IsLocallyFiniteMeasure (spectralMeasure prob (c j) (ν j))]
    (hν : IsVagueLimit atTop (fun j => spectralMeasure prob (c j) (ν j)) airyMeasure)
    (i : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      (∀ k, k ≠ i → 2 * r ≤ |airyNode k - airyNode i|) →
      ∀ᶠ j in atTop,
        |(clusterBarycentre prob (c j) (ν j) (Icc (airyNode i - r) (airyNode i + r)) -
            xiBar * c j) / (c j) ^ ((1 : ℝ) / 3) - cStar * abs (airyNode i)| ≤ ρ := by
  refine ⟨ρ / (2 * cStar), div_pos hρ (mul_pos two_pos cStar_pos), fun r hr hr0 hsep => ?_⟩
  have hcr : cStar * r ≤ ρ / 2 := by
    have hm := mul_le_mul_of_nonneg_left hr0 cStar_pos.le
    rwa [show cStar * (ρ / (2 * cStar)) = ρ / 2 by field_simp [cStar_pos.ne']] at hm
  have hQpos : 0 < (|airyNode i| + r) ^ 2 / (3 * betaTip ^ 2) + 1 := by positivity
  have hev_eps := (tendsto_epsAiry hct).eventually
    (gt_mem_nhds (div_pos (half_pos hρ) hQpos))
  have hmass := cluster_mass_tendsto hct hcpos hshift hν i hr hsep
  have hlim_pos : 0 < cStar * airyNodeWeight i := mul_pos cStar_pos (airyNodeWeight_pos i)
  have hev_W : ∀ᶠ j in atTop,
      0 < (clusterWeight prob (c j) (ν j) (Icc (airyNode i - r) (airyNode i + r))).toReal := by
    filter_upwards [hmass.eventually (lt_mem_nhds hlim_pos), hct.eventually (eventually_gt_atTop 0)]
      with j hj hcj
    have hcp : 0 < (c j) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hcj _
    have h_pos : 0 < (clusterWeight prob (c j) (ν j) (Icc (airyNode i - r) (airyNode i + r))).toReal /
        (c j) ^ ((1 : ℝ) / 3) := hj
    rwa [div_pos_iff_of_pos_right hcp] at h_pos
  filter_upwards [hev_eps, hev_W] with j heps hW
  have hbd := cluster_barycentre_bound (hcpos j) (hshift j) (ν j) i hr hW
  have heps_j := epsAiry_pos (hcpos j)
  have h2 : epsAiry (c j) * ((|airyNode i| + r) ^ 2 / (3 * betaTip ^ 2) + 1) < ρ / 2 := by
    rwa [lt_div_iff₀ hQpos] at heps
  have h2' : epsAiry (c j) * ((|airyNode i| + r) ^ 2 / (3 * betaTip ^ 2)) ≤
      epsAiry (c j) * ((|airyNode i| + r) ^ 2 / (3 * betaTip ^ 2) + 1) := by
    have : (|airyNode i| + r) ^ 2 / (3 * betaTip ^ 2) ≤ (|airyNode i| + r) ^ 2 / (3 * betaTip ^ 2) + 1 := by
      linarith
    exact mul_le_mul_of_nonneg_left this heps_j.le
  rw [← mul_div_assoc] at h2'
  linarith only [hbd, hcr, h2, h2']

/-- **Barycentre separation limit (`sr:cor`)**:
for any `ρ > 0`, sufficiently small `r > 0`, and large `j`, the difference of the first two
cluster barycentres satisfies
`|(t̄_2(r) - t̄_1(r)) / c_j^{1/3} - (|a_2| / |a_1| - 1) A_opt| ≤ ρ`.
In the Airy parameters of `spectral_rigidity.tex`, `(|a_2| / |a_1| - 1) A_opt = c_* (|a_2| - |a_1|)`. -/
theorem cluster_barycentre_diff_tendsto {prob : FixedWeightProblem} {c : ℕ → ℝ}
    {ν : ℕ → Measure ℝ} (hct : Tendsto c atTop atTop) (hcpos : ∀ j, 0 < c j)
    (hshift : ∀ j, prob.totalShift ≤ c j / 12)
    [∀ j, IsLocallyFiniteMeasure (spectralMeasure prob (c j) (ν j))]
    (hν : IsVagueLimit atTop (fun j => spectralMeasure prob (c j) (ν j)) airyMeasure)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ᶠ j in atTop,
        |(clusterBarycentre prob (c j) (ν j) (Icc (airyNode 1 - r) (airyNode 1 + r)) -
            clusterBarycentre prob (c j) (ν j) (Icc (airyNode 0 - r) (airyNode 0 + r))) /
            (c j) ^ ((1 : ℝ) / 3) - (|airyZero 2| / |airyZero 1| - 1) * Aopt| ≤ ρ := by
  obtain ⟨r₀_0, hr₀0_pos, h0⟩ := cluster_barycentre_tendsto hct hcpos hshift hν 0 (half_pos hρ)
  obtain ⟨r₀_1, hr₀1_pos, h1⟩ := cluster_barycentre_tendsto hct hcpos hshift hν 1 (half_pos hρ)
  let r_sep : ℝ := min ((airyZero 1 - airyZero 2) / 4) ((airyZero 2 - airyZero 3) / 4)
  have hr_sep_pos : 0 < r_sep := by
    have h12 : airyZero 2 < airyZero 1 := airyZero_strictAnti (by norm_num)
    have h23 : airyZero 3 < airyZero 2 := airyZero_strictAnti (by norm_num)
    dsimp [r_sep]; exact lt_min (by linarith) (by linarith)
  refine ⟨min r_sep (min r₀_0 r₀_1), lt_min hr_sep_pos (lt_min hr₀0_pos hr₀1_pos), fun r hr hr0 => ?_⟩
  have hr_sep : r ≤ r_sep := hr0.trans (min_le_left _ _)
  have hr0_le : r ≤ r₀_0 := hr0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr1_le : r ≤ r₀_1 := hr0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsep0 : ∀ k, k ≠ 0 → 2 * r ≤ |airyNode k - airyNode 0| := by
    intro k hk
    have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk
    have hanti : airyNode k ≤ airyNode 1 := airyNode_strictAnti.antitone hk1
    have hlt0 : airyNode k < airyNode 0 := lt_of_le_of_lt hanti (airyNode_strictAnti (by norm_num))
    rw [abs_of_neg (sub_neg.mpr hlt0)]
    have hgap : (airyNode 0 - airyNode 1 : ℝ) = airyZero 1 - airyZero 2 := rfl
    have hr12 : r ≤ (airyZero 1 - airyZero 2) / 4 := hr_sep.trans (min_le_left _ _)
    linarith
  have hsep1 : ∀ k, k ≠ 1 → 2 * r ≤ |airyNode k - airyNode 1| := by
    intro k hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · have hk0 : k = 0 := by omega
      subst hk0
      have hpos : 0 < airyNode 0 - airyNode 1 := sub_pos.mpr (airyNode_strictAnti (by norm_num))
      rw [abs_of_pos hpos]
      have hgap : (airyNode 0 - airyNode 1 : ℝ) = airyZero 1 - airyZero 2 := rfl
      have hr12 : r ≤ (airyZero 1 - airyZero 2) / 4 := hr_sep.trans (min_le_left _ _)
      linarith
    · have hk2 : 2 ≤ k := hgt
      have hanti : airyNode k ≤ airyNode 2 := airyNode_strictAnti.antitone hk2
      have hlt1 : airyNode k < airyNode 1 := lt_of_le_of_lt hanti (airyNode_strictAnti (by norm_num))
      rw [abs_of_neg (sub_neg.mpr hlt1)]
      have hn1 : airyNode 1 = airyZero 2 := rfl
      have hn2 : airyNode 2 = airyZero 3 := rfl
      have hr23 : r ≤ (airyZero 2 - airyZero 3) / 4 := hr_sep.trans (min_le_right _ _)
      linarith
  have hid : (|airyZero 2| / |airyZero 1| - 1) * Aopt = cStar * |airyNode 1| - cStar * |airyNode 0| := by
    have ha1_ne : |airyZero 1| ≠ 0 := (abs_pos.mpr (airyZero_neg 1).ne).ne'
    have hn0 : airyNode 0 = airyZero 1 := rfl
    have hn1 : airyNode 1 = airyZero 2 := rfl
    unfold Aopt
    rw [hn0, hn1]
    field_simp [ha1_ne]
  filter_upwards [h0 r hr hr0_le hsep0, h1 r hr hr1_le hsep1] with j hj0 hj1
  have hsub :
      (clusterBarycentre prob (c j) (ν j) (Icc (airyNode 1 - r) (airyNode 1 + r)) -
          clusterBarycentre prob (c j) (ν j) (Icc (airyNode 0 - r) (airyNode 0 + r))) /
          (c j) ^ ((1 : ℝ) / 3) - (|airyZero 2| / |airyZero 1| - 1) * Aopt =
        ((clusterBarycentre prob (c j) (ν j) (Icc (airyNode 1 - r) (airyNode 1 + r)) -
            xiBar * c j) / (c j) ^ ((1 : ℝ) / 3) - cStar * |airyNode 1|) -
        ((clusterBarycentre prob (c j) (ν j) (Icc (airyNode 0 - r) (airyNode 0 + r)) -
            xiBar * c j) / (c j) ^ ((1 : ℝ) / 3) - cStar * |airyNode 0|) := by
    rw [hid]; ring
  rw [hsub]
  exact (abs_sub _ _).trans (add_le_add hj1 hj0 |>.trans_eq (add_halves ρ))

/-- **Corollary `sr:cor` barycentre assertion for crossing sequences**:
for any crossing sequence `S` satisfying `SigmaConclusion S.μS`,
`(t̄_2(r) - t̄_1(r)) / c_j^{1/3} → (|a_2| / |a_1| - 1) A_opt`. -/
theorem crossing_barycentre_diff_tendsto {prob : FixedWeightProblem} (S : CrossingSequence prob)
    (hσ : SigmaConclusion S.μS) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ᶠ j in atTop,
        |(clusterBarycentre prob (S.c j) (S.meas j).ν (Icc (airyNode 1 - r) (airyNode 1 + r)) -
            clusterBarycentre prob (S.c j) (S.meas j).ν (Icc (airyNode 0 - r) (airyNode 0 + r))) /
            (S.c j) ^ ((1 : ℝ) / 3) - (|airyZero 2| / |airyZero 1| - 1) * Aopt| ≤ ρ := by
  have : ∀ j, IsLocallyFiniteMeasure (spectralMeasure prob (S.c j) (S.meas j).ν) :=
    S.isLocallyFinite
  exact cluster_barycentre_diff_tendsto S.tendsto_c S.c_pos S.shift_le hσ.2.2.2.1 hρ

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.cluster_barycentre_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cluster_barycentre_tendsto

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.crossing_barycentre_diff_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms crossing_barycentre_diff_tendsto

end FormalResearch.ModularBootstrap.Upper.Rigidity
