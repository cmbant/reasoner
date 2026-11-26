module

public import FormalResearch.ModularBootstrap.FiveTerm.RegulariserDefect

/-!
# Regularised minimisers `F_ε = m_ε F_*` and `𝒥[F_ε] - α_tip g₁ ≤ 25 α_C ε²`
(FIVE-0; `ctu:common-functional` (3), eq. `ctu:J-quad`)

Source: `CFT/modular_bootstrap/paper/constant_term_universality.tex`, Lemma ctu.2a (3).

For an outer-function datum `G` (`OuterDatum W K g₁ G`) and `ε ∈ (0,1)` (the paper takes `ε ∈ (0, 1/2)`),
`F_ε = m_ε · (1+z²)/G`:

* `HAdm (m_ε F) (-(ε/2) + c₁)` for every `F ∈ HAdm F c₁` (`mEps_hAdm_mul`): `m_ε` is bounded with `‖m_ε‖² ≤ 2/ε`
  on `closure Ω ∖ {1}`, holomorphic, real-symmetric, with jet `1 - (ε/2) z`;
* `comb_regularisation`: `F_ε ∈ HAdm` with `F_ε'(0) = -g₁ - ε/2` and
  `α_tip g₁ ≤ 𝒥[F_ε] ≤ α_tip g₁ + 25 α_C ε²`, the constant `25 α_C` being absolute (independent of `(W, K, G)`).

Not proved here: the smoothness of `F_ε` across `z = 1` and the sharp two-sided `D_ε - 1 ≍ y^{5/2}(ε+y)^{-1/2}`
(not needed for `ctu:J-quad`).  All results proved unconditionally.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

section

variable {F G : ℂ → ℂ} {c1 g1 ε : ℝ} {W : ℝ → ℝ} {K : ℝ → ℂ}

/-- Multiplying an admissible `F` by a bounded holomorphic real-symmetric multiplier with a jet. -/
lemma HAdm.mul_bdd {m : ℂ → ℂ} {m1 M : ℝ} (hF : HAdm F c1)
    (hmd : DifferentiableOn ℂ m halfDisc) (hmc : ContinuousOn m (closure halfDisc \ {1}))
    (hmconj : ∀ z ∈ halfDisc, m (starRingEnd ℂ z) = starRingEnd ℂ (m z))
    (hmj : ∃ C r : ℝ, 0 < r ∧ ∀ z ∈ closure halfDisc, ‖z‖ < r → ‖m z - 1 - m1 * z‖ ≤ C * ‖z‖ ^ 2)
    (hmb : ∀ z ∈ closure halfDisc, z ≠ 1 → ‖m z‖ ≤ M) :
    HAdm (fun z => m z * F z) (m1 + c1) where
  diff := hmd.mul hF.diff
  cont := by
    refine ContinuousOn.mul (hmc.mono ?_) hF.cont
    intro z hz
    refine ⟨hz.1, ?_⟩
    intro h
    exact hz.2 (by rw [mem_singPts_iff]; right; right; simpa using h)
  conj z hz := by simp only [hmconj z hz, hF.conj z hz, map_mul]
  jet := by
    obtain ⟨C, r, hr, h⟩ := jet_mul hmj hF.jet
    exact ⟨C, r, hr, h⟩
  near_one := by
    obtain ⟨C, r, hr, h⟩ := hF.near_one
    refine ⟨|M| * |C|, r, hr, fun z hz hz1 hzr => ?_⟩
    have hm := hmb z hz hz1
    have hh := h z hz hz1 hzr
    calc ‖m z * F z‖ * ‖z - 1‖ ^ (1 / 2 : ℝ) = ‖m z‖ * (‖F z‖ * ‖z - 1‖ ^ (1 / 2 : ℝ)) := by
          rw [norm_mul]; ring
      _ ≤ |M| * |C| := by
          apply mul_le_mul (le_trans hm (le_abs_self _)) (le_trans hh (le_abs_self _))
          · positivity
          · exact abs_nonneg _
  near_I := by
    obtain ⟨C, r, a, hr, ha, h⟩ := hF.near_I
    refine ⟨|M| * |C|, min r 1, a, lt_min hr one_pos, ha, fun z hz h1 h2 hzr => ?_⟩
    have hzr' : ‖z - Complex.I‖ < r ∨ ‖z + Complex.I‖ < r := by
      rcases hzr with h3 | h3
      · exact Or.inl (lt_of_lt_of_le h3 (min_le_left _ _))
      · exact Or.inr (lt_of_lt_of_le h3 (min_le_left _ _))
    have hz1 : z ≠ 1 := by
      intro hz1
      rw [hz1] at hzr
      have e1 : 1 ≤ ‖(1 : ℂ) - Complex.I‖ := by
        have := Complex.abs_re_le_norm ((1 : ℂ) - Complex.I); simpa using this
      have e2 : 1 ≤ ‖(1 : ℂ) + Complex.I‖ := by
        have := Complex.abs_re_le_norm ((1 : ℂ) + Complex.I); simpa using this
      rcases hzr with h3 | h3
      · linarith [lt_of_lt_of_le h3 (min_le_right _ _)]
      · linarith [lt_of_lt_of_le h3 (min_le_right _ _)]
    have hm := hmb z hz hz1
    have hh := h z hz h1 h2 hzr'
    calc ‖m z * F z‖ = ‖m z‖ * ‖F z‖ := norm_mul _ _
      _ ≤ |M| * (|C| * ‖1 + z ^ 2‖ ^ a) := by
          apply mul_le_mul (le_trans hm (le_abs_self _))
          · calc ‖F z‖ ≤ C * ‖1 + z ^ 2‖ ^ a := hh
              _ ≤ |C| * ‖1 + z ^ 2‖ ^ a := by
                  gcongr; exact le_abs_self _
          · exact norm_nonneg _
          · exact abs_nonneg _
      _ = |M| * |C| * ‖1 + z ^ 2‖ ^ a := by ring

/-- `m_ε F ∈ H_adm` for every `F ∈ H_adm`. -/
theorem mEps_hAdm_mul (hF : HAdm F c1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    HAdm (fun z => mEps ε z * F z) (-(ε / 2) + c1) := by
  refine HAdm.mul_bdd (M := 1 + 2 / ε) hF ?_ (continuousOn_mEps hε0 hε1)
    (fun z hz => mEps_conj hz hε0 hε1) ?_ ?_
  · exact (differentiableOn_mEps_ball hε0 hε1).mono (fun z hz => by
      simpa using hz.1)
  · obtain ⟨C, r, hr, h⟩ := mEps_jet hε0 hε1
    exact ⟨C, r, hr, fun z _ hz => h z hz⟩
  · intro z hz hz1
    have h := norm_mEps_sq_le hz hz1 hε0 hε1
    nlinarith only [h, sq_nonneg (‖mEps ε z‖ - 1 / 2)]

/-- `defectInt` only depends on the values at `iy` and `e^{-iψ}`. -/
lemma defectInt_congr {H1 H2 : ℂ → ℂ} {y : ℝ}
    (h1 : H1 (Complex.I * (y : ℂ)) = H2 (Complex.I * (y : ℂ)))
    (h2 : H1 (starRingEnd ℂ (wPt y)) = H2 (starRingEnd ℂ (wPt y))) :
    defectInt H1 y = defectInt H2 y := by
  have hes : edgeSum H1 y = edgeSum H2 y := by unfold edgeSum; rw [h1, h2]
  unfold defectInt defectNum
  rw [hes, h1]

/-- **`ctu:J-quad`** (with the absolute constant `25 α_C`): the regularised minimisers
`F_ε = m_ε (1+z²)/G` are admissible with `F_ε'(0) = -g₁ - ε/2` and
`α_tip g₁ ≤ 𝒥[F_ε] ≤ α_tip g₁ + 25 α_C ε²`. -/
theorem comb_regularisation (hG : OuterDatum W K g1 G) (hε0 : 0 < ε) (hε1 : ε < 1) :
    HAdm (fun z => mEps ε z * fStar G z) (-g1 - ε / 2) ∧
    alphaTip * g1 ≤ combJ W K (fun z => mEps ε z * fStar G z) ∧
    combJ W K (fun z => mEps ε z * fStar G z) ≤ alphaTip * g1 + 25 * alphaC * ε ^ 2 := by
  have hF : HAdm (fun z => mEps ε z * fStar G z) (-(ε / 2) + -g1) :=
    mEps_hAdm_mul (fStar_hAdm hG) hε0 hε1
  have hc : -(ε / 2) + -g1 = -g1 - ε / 2 := by ring
  rw [hc] at hF
  refine ⟨hF, comb_lower_bound hF hG, ?_⟩
  obtain ⟨_, h⟩ := comb_defect_identity hF hG
  rw [h]
  have hHc := hF.mul_datum hG
  have hint := defectInt_integrable hHc
  have hpt : ∀ y ∈ Ioo (0 : ℝ) 1,
      defectInt (fun z => (fun z => mEps ε z * fStar G z) z * G z) y ≤ 25 * ε ^ 2 := by
    intro y hy
    obtain ⟨hy0, hy1⟩ := hy
    have hfG : ∀ z ∈ closure halfDisc \ singPts,
        (fun z => mEps ε z * fStar G z) z * G z = mEps ε z * (1 + z ^ 2) := by
      intro z hz
      show mEps ε z * fStar G z * G z = _
      unfold fStar
      rw [mul_assoc, div_mul_cancel₀ _ (hG.ne_zero z hz)]
    rw [defectInt_congr (H2 := fun z => mEps ε z * (1 + z ^ 2))
      (hfG _ (I_mul_mem_cont hy0 hy1)) (hfG _ (wbar_mem_cont hy0 hy1))]
    exact defectInt_reg_le hy0 hy1 hε0 hε1
  have hI : ∫ y in Ioo (0 : ℝ) 1, defectInt (fun z => (fun z => mEps ε z * fStar G z) z * G z) y ≤
      25 * ε ^ 2 := by
    calc _ ≤ ∫ _y in Ioo (0 : ℝ) 1, 25 * ε ^ 2 :=
          setIntegral_mono_on hint (integrableOn_const (by simp)) measurableSet_Ioo hpt
      _ = 25 * ε ^ 2 := by simp
  nlinarith only [hI, alphaC_pos]

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.comb_regularisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.comb_regularisation
