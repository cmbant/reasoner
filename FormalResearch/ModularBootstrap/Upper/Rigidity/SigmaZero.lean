module

public import FormalResearch.ModularBootstrap.Upper.Rigidity.Families
public import FormalResearch.ModularBootstrap.Upper.Rigidity.Dictionary

/-!
# Theorem `Σ₀` (`spectral_rigidity.tex`, `sr:Sigma0`)

Under (Gap) `liminf (τ_j - T_*)/c_j'^{1/3} ≥ 0`, and given Property `sr:P` for the same-site
designs (`DesignPropertyP`, `SameSiteFamily`):

* (a) `τ_j = T_* + o(c_j'^{1/3})`, i.e. `u(τ_j) → a₁` (`sigma_zero_a`, `theorem_sigma_zero_a`);
* (b) for every `ρ > 0`, `liminf_j μ_j([a₁ - ρ, a₁ + ρ]) ≥ 1/Ai'(a₁)²` (`sigma_zero_b`).

The proof of (a) is the first step of the proof of (b): a design with `f = 1`, `d > 0` and
`V_𝔇 < 0` forces an atom of `μ_j` above `u_f - o(1)` (so (a) does not need the upper bound of
Theorem C15 that the TeX proof quotes).  Proof of (b): `∫ Ψ_j dμ_j = ∫ Ψ_j du ≤ V + o(1) < 0`, the
atoms below `θ_j` contribute nonnegatively, the sliver `[θ_j, s_j] ⊆ [a₁ - d - η, a₁ + ι]` carries
the negative part, on which `-W ≤ (d + ι) G(a₁)(1 + C(d + η + ι))`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace FormalResearch.ModularBootstrap.Upper.Rigidity

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.FixedWeight

/-- `Σ₀(a)` at the level of `u(τ_j)`: `liminf_j u(τ_j) ≥ a₁` (the matching `limsup` is (Gap)). -/
theorem liminf_s_ge (S : SpectralData) {𝒟 : Set Window} (hP : DesignPropertyP S.μ 𝒟)
    (F : SameSiteFamily 𝒟) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ j in atTop, airyZero 1 - δ ≤ S.s j := by
  intro δ hδ
  have hr := designRadius_pos
  set d : ℝ := min δ designRadius / 2 with hd
  have hd0 : 0 < d := by rw [hd]; exact div_pos (lt_min hδ hr) two_pos
  have hdδ : d < δ := by
    rw [hd]; have := min_le_left δ designRadius; linarith [lt_min hδ hr]
  have hdr : d < designRadius := by
    rw [hd]; have := min_le_right δ designRadius; linarith [lt_min hδ hr]
  obtain ⟨k, hk⟩ := (F.E_small.eventually (gt_mem_nhds (half_pos hd0))).exists
  have habs : |d| < designRadius := by rw [abs_of_pos hd0]; exact hdr
  obtain ⟨T⟩ := hP _ (F.mem k d habs)
  have hV : (F.win k d).V < 0 := by
    have h1 := F.V_le_of_nonneg k hd0.le
    have h2 := F.Rt_ge k
    nlinarith
  set v : ℝ := -(F.win k d).V with hv
  have hv0 : 0 < v := by rw [hv]; linarith
  have huF : (F.win k d).uF = airyNode 0 - d := F.uF_eq k d
  have h1 : ∀ᶠ j in atTop, airyNode 0 - δ < T.θ j := by
    have := T.theta_tendsto
    rw [huF] at this
    exact this.eventually (lt_mem_nhds (by linarith))
  have h2 := T.limsup_le (v / 2) (half_pos hv0)
  filter_upwards [h1, h2] with j hj1 hj2
  by_contra hcon
  push Not at hcon
  have hcon' : S.s j < airyNode 0 - δ := by rw [airyNode_zero]; exact hcon
  have hnn : 0 ≤ ∫ u, T.Ψ j u ∂(S.μ j) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [S.ae_le j] with u hu
    exact T.nonneg j u (by linarith)
  have := T.crossing j
  linarith

/-- The key sliver estimate of `Σ₀(b)`: for a same-site design `(k, d)` with `V < 0`, parameters
`η, ι > 0` and `δ ∈ (0, 1)`, eventually
`(1 - δ)(-V) ≤ (1 + δ) M_W μ_j([a₁ - d - η, a₁ + ι])`, `M_W = (d + ι) G_k(a₁)(1 + C(d + η + ι))`. -/
theorem sliver_estimate (S : SpectralData) {𝒟 : Set Window} (hP : DesignPropertyP S.μ 𝒟)
    (F : SameSiteFamily 𝒟) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ k u, |u - airyNode 0| ≤ 1 →
      F.G k u ≤ F.G k (airyNode 0) * (1 + C * |u - airyNode 0|))
    (k : ℕ) {d η ι δ : ℝ} (hd : 0 < d) (hdr : d < designRadius) (hη : 0 < η) (hι : 0 < ι)
    (hιr : ι ≤ designRadius) (hsmall : d + η + ι ≤ 1) (hδ : 0 < δ) (hV : (F.win k d).V < 0) :
    ∀ᶠ j in atTop, (1 - δ) * (-(F.win k d).V) ≤ (1 + δ) *
      ((d + ι) * F.G k (airyNode 0) * (1 + C * (d + η + ι))) *
        (S.μ j (Icc (airyNode 0 - d - η) (airyNode 0 + ι))).toReal := by
  have habs : |d| < designRadius := by rw [abs_of_pos hd]; exact hdr
  obtain ⟨T⟩ := hP _ (F.mem k d habs)
  set v : ℝ := -(F.win k d).V with hv
  have hv0 : 0 < v := by rw [hv]; linarith
  set Mw : ℝ := (d + ι) * F.G k (airyNode 0) * (1 + C * (d + η + ι)) with hMw
  have hG0 : 0 < F.G k (airyNode 0) := F.G_pos k _ (by linarith [designRadius_pos])
  have hMw0 : 0 < Mw := by rw [hMw]; positivity
  have huF : (F.win k d).uF = airyNode 0 - d := F.uF_eq k d
  set K : Set ℝ := Icc (airyNode 0 - d - 1) (airyNode 0 + 1) with hK
  have hKc : IsCompact K := isCompact_Icc
  have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.1 T.window_limit) K hKc
  have e1 : ∀ᶠ j in atTop, airyNode 0 - d - η < T.θ j := by
    have := T.theta_tendsto
    rw [huF] at this
    exact this.eventually (lt_mem_nhds (by linarith))
  have e2 := S.ae_le_of_gap hι
  have e3 := T.limsup_le (δ * v) (by positivity)
  have e4 : ∀ᶠ j in atTop, ∀ x ∈ K, dist ((F.win k d).W x) (T.Ψ j x) < δ * Mw :=
    Metric.tendstoUniformlyOn_iff.1 hunif (δ * Mw) (by positivity)
  filter_upwards [e1, e2, e3, e4] with j hj1 hj2 hj3 hj4
  set Sset : Set ℝ := Icc (airyNode 0 - d - η) (airyNode 0 + ι) with hSset
  have hfin : S.μ j Sset < ∞ := isCompact_Icc.measure_lt_top
  have hlow : ∀ u ∈ Sset, -((1 + δ) * Mw) ≤ T.Ψ j u := by
    intro u hu
    have huK : u ∈ K := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h4 := hj4 u huK
    rw [Real.dist_eq] at h4
    have h5 := (abs_lt.mp h4).2
    -- lower bound for W on the sliver
    have hW : -Mw ≤ (F.win k d).W u := by
      rw [F.W_eq]
      by_cases hu1 : u ≤ airyNode 0 - d
      · have hG : 0 ≤ F.G k u := F.G_nonneg k (by linarith [hu.2])
        have : 0 ≤ F.G k u * (airyNode 0 - d - u) := mul_nonneg hG (by linarith)
        linarith
      · push Not at hu1
        have hG : 0 ≤ F.G k u := F.G_nonneg k (by linarith [hu.2])
        have hau : |u - airyNode 0| ≤ d + η + ι := by
          rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
        have hbound := hC k u (hau.trans hsmall)
        have h6 : F.G k u ≤ F.G k (airyNode 0) * (1 + C * (d + η + ι)) := by
          refine hbound.trans ?_
          have : C * |u - airyNode 0| ≤ C * (d + η + ι) := mul_le_mul_of_nonneg_left hau hC0
          exact mul_le_mul_of_nonneg_left (by linarith) hG0.le
        have h7 : F.G k u * (u - (airyNode 0 - d)) ≤ Mw := by
          rw [hMw]
          have h8 : u - (airyNode 0 - d) ≤ d + ι := by linarith [hu.2]
          have h9 : 0 ≤ u - (airyNode 0 - d) := by linarith
          calc F.G k u * (u - (airyNode 0 - d))
              ≤ (F.G k (airyNode 0) * (1 + C * (d + η + ι))) * (d + ι) :=
                mul_le_mul h6 h8 h9 (by positivity)
            _ = (d + ι) * F.G k (airyNode 0) * (1 + C * (d + η + ι)) := by ring
        nlinarith
    have hΨ : (F.win k d).W u - δ * Mw < T.Ψ j u := by linarith
    linarith
  have hoff : ∀ᵐ u ∂(S.μ j), u ∉ Sset → 0 ≤ T.Ψ j u := by
    filter_upwards [hj2] with u hu hnot
    have hlt : u < airyNode 0 - d - η := by
      by_contra hge
      push Not at hge
      exact hnot ⟨hge, hu⟩
    exact T.nonneg j u (by linarith)
  have hmain := const_mul_measure_le_integral (T.integrable_mu j) measurableSet_Icc hfin hlow hoff
  rw [T.crossing j] at hmain
  have : -((1 + δ) * Mw) * (S.μ j Sset).toReal ≤ -(1 - δ) * v := by
    have : (F.win k d).V = -v := by rw [hv]; ring
    linarith
  nlinarith

/-- The arithmetic of the choice of parameters in `Σ₀(b)`. -/
lemma final_arith {r δ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hδ : δ = (1 - r) / 17) :
    r * ((1 + δ) ^ 2 * (1 + 3 * δ)) ≤ (1 - δ) ^ 2 := by
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ < 1 / 17 := by rw [hδ]; linarith
  have h1 : (1 + δ) ^ 2 * (1 + 3 * δ) ≤ 1 + 6 * δ := by nlinarith [mul_pos hδ0 hδ0, mul_pos (mul_pos hδ0 hδ0) hδ0]
  have h2 : r * ((1 + δ) ^ 2 * (1 + 3 * δ)) ≤ r * (1 + 6 * δ) := mul_le_mul_of_nonneg_left h1 hr0.le
  have h3 : r * (1 + 6 * δ) ≤ 1 - 2 * δ := by
    have : r = 1 - 17 * δ := by rw [hδ]; ring
    rw [this]; nlinarith
  nlinarith

/-- **`Σ₀(b)`, eventual form**: for every `ρ > 0` and `b < 1/Ai'(a₁)²`, eventually
`μ_j([a₁ - ρ, a₁ + ρ]) ≥ b`. -/
theorem sigma_zero_b_eventually (S : SpectralData) {𝒟 : Set Window}
    (hP : DesignPropertyP S.μ 𝒟) (F : SameSiteFamily 𝒟) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ b : ℝ, b < airyNodeWeight 0 →
      ∀ᶠ j in atTop, ENNReal.ofReal b ≤ S.μ j (Icc (airyZero 1 - ρ) (airyZero 1 + ρ)) := by
  have hw0 := airyNodeWeight_pos 0
  have hr := designRadius_pos
  intro b hb
  by_cases hb0 : b ≤ 0
  · exact Eventually.of_forall fun j => by rw [ENNReal.ofReal_of_nonpos hb0]; exact bot_le
  push Not at hb0
  set w₀ := airyNodeWeight 0 with hw₀
  set r : ℝ := b / w₀ with hrdef
  have hr0 : 0 < r := div_pos hb0 hw0
  have hr1 : r < 1 := by rw [hrdef, div_lt_one hw0]; exact hb
  obtain ⟨C, hC0, hC⟩ := F.G_upper
  set δ : ℝ := (1 - r) / 17 with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hδ1 : δ < 1 / 17 := by rw [hδdef]; linarith
  set d : ℝ := min (min (designRadius / 2) (ρ / 4)) (min (δ / (C + 1)) (1 / 4)) with hddef
  have hd0 : 0 < d := by
    rw [hddef]; refine lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by norm_num))
  have hd1 : d ≤ designRadius / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hd2 : d ≤ ρ / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hd3 : d ≤ δ / (C + 1) := (min_le_right _ _).trans (min_le_left _ _)
  have hd4 : d ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hCd : C * d ≤ δ := by
    have h1 : d * (C + 1) ≤ δ := by rwa [le_div_iff₀ (by positivity)] at hd3
    nlinarith
  have hdr : d < designRadius := by linarith
  set η : ℝ := δ * d with hηdef
  have hη0 : 0 < η := by positivity
  have hsmall : d + η + η ≤ 1 := by
    have : η ≤ d := by rw [hηdef]; nlinarith
    linarith
  have hηr : η ≤ designRadius := by
    have : η ≤ d := by rw [hηdef]; nlinarith
    linarith
  obtain ⟨k, hk⟩ := (F.E_small.eventually (gt_mem_nhds (show 0 < δ * d / 2 by positivity))).exists
  have hRt := F.Rt_ge k
  have hVle := F.V_le_of_nonneg k hd0.le
  have hv : (1 - δ) * d * F.Rt k ≤ -(F.win k d).V := by
    have : δ * d / 2 ≤ δ * d * F.Rt k := by nlinarith [mul_pos hδ0 hd0]
    nlinarith
  have hVneg : (F.win k d).V < 0 := by
    have : 0 < (1 - δ) * d * F.Rt k := by
      have := F.Rt_pos k
      have : 0 < 1 - δ := by linarith
      positivity
    linarith
  have hkey := sliver_estimate S hP F hC0 hC k hd0 hdr hη0 hη0 hηr hsmall hδ0 hVneg
  filter_upwards [hkey] with j hj
  set m' := (S.μ j (Icc (airyNode 0 - d - η) (airyNode 0 + η))).toReal with hm'
  have hsub : Icc (airyNode 0 - d - η) (airyNode 0 + η) ⊆ Icc (airyZero 1 - ρ) (airyZero 1 + ρ) := by
    rw [← airyNode_zero]
    intro u hu
    have hηd : η ≤ d := by rw [hηdef]; nlinarith
    refine ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hfin : S.μ j (Icc (airyZero 1 - ρ) (airyZero 1 + ρ)) < ∞ := isCompact_Icc.measure_lt_top
  have hmono : m' ≤ (S.μ j (Icc (airyZero 1 - ρ) (airyZero 1 + ρ))).toReal :=
    ENNReal.toReal_mono hfin.ne (measure_mono hsub)
  -- G(a₁) = Rt / w₀
  have hG : F.G k (airyNode 0) = F.Rt k / w₀ := by
    unfold SameSiteFamily.Rt; rw [← hw₀]; field_simp
  have hMw : (d + η) * F.G k (airyNode 0) * (1 + C * (d + η + η)) ≤
      d * (1 + δ) * (F.Rt k / w₀) * (1 + 3 * δ) := by
    rw [hG]
    have hRt0 := F.Rt_pos k
    have h1 : 1 + C * (d + η + η) ≤ 1 + 3 * δ := by
      have : C * (d + η + η) = C * d * (1 + 2 * δ) := by rw [hηdef]; ring
      rw [this]
      have : C * d * (1 + 2 * δ) ≤ δ * (1 + 2 * δ) :=
        mul_le_mul_of_nonneg_right hCd (by positivity)
      nlinarith
    have h2 : d + η = d * (1 + δ) := by rw [hηdef]; ring
    have h3 : 0 ≤ (d + η) * (F.Rt k / w₀) := by positivity
    calc (d + η) * (F.Rt k / w₀) * (1 + C * (d + η + η))
        ≤ (d + η) * (F.Rt k / w₀) * (1 + 3 * δ) := mul_le_mul_of_nonneg_left h1 h3
      _ = d * (1 + δ) * (F.Rt k / w₀) * (1 + 3 * δ) := by rw [h2]
  -- conclude `b ≤ m`
  have hMwpos : 0 < (d + η) * F.G k (airyNode 0) * (1 + C * (d + η + η)) := by
    have hG0 : 0 < F.G k (airyNode 0) := F.G_pos k _ (by linarith [designRadius_pos])
    positivity
  have hfin_arith := final_arith hr0 hr1 hδdef
  have hb_le : b ≤ m' := by
    have h1 : b * ((1 + δ) * ((d + η) * F.G k (airyNode 0) * (1 + C * (d + η + η)))) ≤
        (1 - δ) * (-(F.win k d).V) := by
      have hb' : b = r * w₀ := by rw [hrdef]; field_simp
      have h2 : b * ((1 + δ) * ((d + η) * F.G k (airyNode 0) * (1 + C * (d + η + η)))) ≤
          b * ((1 + δ) * (d * (1 + δ) * (F.Rt k / w₀) * (1 + 3 * δ))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMw (by positivity)) hb0.le
      have h3 : b * ((1 + δ) * (d * (1 + δ) * (F.Rt k / w₀) * (1 + 3 * δ))) =
          r * ((1 + δ) ^ 2 * (1 + 3 * δ)) * (d * F.Rt k) := by
        rw [hb']; field_simp
      have h4 : (1 - δ) * ((1 - δ) * d * F.Rt k) ≤ (1 - δ) * (-(F.win k d).V) :=
        mul_le_mul_of_nonneg_left hv (by linarith)
      have h5 : r * ((1 + δ) ^ 2 * (1 + 3 * δ)) * (d * F.Rt k) ≤ (1 - δ) ^ 2 * (d * F.Rt k) :=
        mul_le_mul_of_nonneg_right hfin_arith (by positivity)
      calc b * ((1 + δ) * ((d + η) * F.G k (airyNode 0) * (1 + C * (d + η + η))))
          ≤ b * ((1 + δ) * (d * (1 + δ) * (F.Rt k / w₀) * (1 + 3 * δ))) := h2
        _ = r * ((1 + δ) ^ 2 * (1 + 3 * δ)) * (d * F.Rt k) := h3
        _ ≤ (1 - δ) ^ 2 * (d * F.Rt k) := h5
        _ = (1 - δ) * ((1 - δ) * d * F.Rt k) := by ring
        _ ≤ (1 - δ) * (-(F.win k d).V) := h4
    have h6 : (1 - δ) * (-(F.win k d).V) ≤ (1 + δ) *
        ((d + η) * F.G k (airyNode 0) * (1 + C * (d + η + η))) * m' := hj
    have h7 : b * ((1 + δ) * ((d + η) * F.G k (airyNode 0) * (1 + C * (d + η + η)))) ≤
        m' * ((1 + δ) * ((d + η) * F.G k (airyNode 0) * (1 + C * (d + η + η)))) :=
      calc b * ((1 + δ) * ((d + η) * F.G k (airyNode 0) * (1 + C * (d + η + η))))
          ≤ (1 - δ) * (-(F.win k d).V) := h1
        _ ≤ _ := h6
        _ = _ := by ring
    have hpos : 0 < (1 + δ) * ((d + η) * F.G k (airyNode 0) * (1 + C * (d + η + η))) := by positivity
    exact le_of_mul_le_mul_right h7 hpos
  exact ENNReal.ofReal_le_of_le_toReal (hb_le.trans hmono)

/-- **Theorem `Σ₀(b)`** (`sr:Sigma0`(b)): for every `ρ > 0`,
`liminf_j μ_j([a₁ - ρ, a₁ + ρ]) ≥ 1/Ai'(a₁)²`. -/
theorem sigma_zero_b (S : SpectralData) {𝒟 : Set Window} (hP : DesignPropertyP S.μ 𝒟)
    (F : SameSiteFamily 𝒟) {ρ : ℝ} (hρ : 0 < ρ) :
    ENNReal.ofReal (airyNodeWeight 0) ≤
      liminf (fun j => S.μ j (Icc (airyZero 1 - ρ) (airyZero 1 + ρ))) atTop := by
  have hw0 := airyNodeWeight_pos 0
  have claim := sigma_zero_b_eventually S hP F hρ
  by_contra hcon
  push Not at hcon
  obtain ⟨b, hb0, hb1, hb2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hcon
  have hbw : b < airyNodeWeight 0 := (ENNReal.ofReal_lt_ofReal_iff hw0).1 hb2
  have hle : ENNReal.ofReal b ≤ liminf (fun j => S.μ j (Icc (airyZero 1 - ρ) (airyZero 1 + ρ))) atTop :=
    le_liminf_of_le (by isBoundedDefault) (claim b hbw)
  exact absurd hb1 (not_lt.mpr hle)

/-- The spectral data of a sequence `(c_j, τ_j, μ_j)` with (Gap): `μ_j` is supported on
`u ≤ u(τ_j)`, where `u = uAiry c_j` is the Airy variable. -/
noncomputable def SpectralData.ofGap {c τ : ℕ → ℝ} (hc : Tendsto c atTop atTop)
    (hgap : GapCondition c τ) (μ : ℕ → Measure ℝ) [∀ j, IsLocallyFiniteMeasure (μ j)]
    (hsupp : ∀ j, μ j (Ioi (uAiry (c j) (τ j))) = 0) : SpectralData where
  μ := μ
  s := fun j => uAiry (c j) (τ j)
  locFin := inferInstance
  supp := hsupp
  gap := eventually_uAiry_le_of_gap hc hgap

/-- **Theorem `Σ₀(a)`** (`sr:Sigma0`(a)) in the variables of the paper: for spectra with (Gap),
`τ_j = T_*(c_j) + o(c_j^{1/3})` and `u(τ_j) → a₁`, where `μ_j` is the spectral measure of the
spectrum with first level `τ_j` (`μ_j` lives on `u ≤ u(τ_j)`). -/
theorem theorem_sigma_zero_a {c τ : ℕ → ℝ} (hc : Tendsto c atTop atTop) (hgap : GapCondition c τ)
    (μ : ℕ → Measure ℝ) [∀ j, IsLocallyFiniteMeasure (μ j)]
    (hsupp : ∀ j, μ j (Ioi (uAiry (c j) (τ j))) = 0) {𝒟 : Set Window}
    (hP : DesignPropertyP μ 𝒟) (F : SameSiteFamily 𝒟) :
    (∀ δ : ℝ, 0 < δ → ∀ᶠ j in atTop,
        |τ j - TStar (c j)| ≤ δ * (c j) ^ ((1 : ℝ) / 3)) ∧
      Tendsto (fun j => uAiry (c j) (τ j)) atTop (𝓝 (airyZero 1)) := by
  let S := SpectralData.ofGap hc hgap μ hsupp
  have hge := liminf_s_ge S hP F
  have hup := eventually_le_of_uAiry_ge hc hge
  have hcpos : ∀ᶠ j in atTop, 0 < c j := hc.eventually_gt_atTop 0
  refine ⟨fun δ hδ => ?_, ?_⟩
  · filter_upwards [hup δ hδ, hgap δ hδ, hcpos] with j h1 h2 h3
    rw [abs_le]
    constructor <;> linarith
  · refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
    · filter_upwards [hge ((airyZero 1 - a) / 2) (by linarith)] with j hj
      have hj' : airyZero 1 - (airyZero 1 - a) / 2 ≤ uAiry (c j) (τ j) := hj
      linarith
    · filter_upwards [S.gap ((a - airyZero 1) / 2) (by linarith)] with j hj
      have hj' : uAiry (c j) (τ j) ≤ airyZero 1 + (a - airyZero 1) / 2 := hj
      linarith

/-- **Theorem `Σ₀(b)`** (`sr:Sigma0`(b)) in the variables of the paper. -/
theorem theorem_sigma_zero_b {c τ : ℕ → ℝ} (hc : Tendsto c atTop atTop) (hgap : GapCondition c τ)
    (μ : ℕ → Measure ℝ) [∀ j, IsLocallyFiniteMeasure (μ j)]
    (hsupp : ∀ j, μ j (Ioi (uAiry (c j) (τ j))) = 0) {𝒟 : Set Window}
    (hP : DesignPropertyP μ 𝒟) (F : SameSiteFamily 𝒟) {ρ : ℝ} (hρ : 0 < ρ) :
    ENNReal.ofReal (1 / (airyAi' (airyZero 1)) ^ 2) ≤
      liminf (fun j => μ j (Icc (airyZero 1 - ρ) (airyZero 1 + ρ))) atTop :=
  sigma_zero_b (SpectralData.ofGap hc hgap μ hsupp) hP F hρ

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.liminf_s_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.liminf_s_ge

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.sliver_estimate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.sliver_estimate

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.sigma_zero_b_eventually' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.sigma_zero_b_eventually

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.sigma_zero_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.sigma_zero_b

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.theorem_sigma_zero_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.theorem_sigma_zero_a

/-- info: 'FormalResearch.ModularBootstrap.Upper.Rigidity.theorem_sigma_zero_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Rigidity.theorem_sigma_zero_b

end FormalResearch.ModularBootstrap.Upper.Rigidity
