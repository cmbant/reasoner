module

public import FormalResearch.ModularBootstrap.FiveTerm.StripOuterGen

/-!
# The boundary extension of the strip Schwarz integral (FIVE-0 slice 1; `cts:involution` (1))

Generalisation of Paper I's `CtOuterBoundary` (specific to `uR`) to an amplitude `a` with `Amp a`
(`StripOuterGen`).  `hbarA a ζ = lim_{ξ → ζ, ξ ∈ S} genH a ξ` is the continuous extension of `genH a` to
`closedStrip`; it is real-symmetric, invariant under `ζ ↦ 1 - ζ`, and `Re hbarA a (i y) = Re hbarA a (1 + i y) = a y`.
All proved unconditionally.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.ModularBootstrap.FiveTerm.StripOuter

/-- Local edge data at every real `y₀`. -/
lemma exists_edge_dataA {a : ℝ → ℝ} (ha : Amp a) (y₀ : ℝ) :
    ∃ δ > 0, ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball (Complex.I * (y₀ : ℂ)) δ) ∧
      (∀ ζ ∈ strip, ζ ∈ ball (Complex.I * (y₀ : ℂ)) δ → genH a ζ = H ζ) ∧ (H (Complex.I * (y₀ : ℂ))).re = a y₀ := by
  obtain ⟨R, hR, v, hv, hvu⟩ := ha.loc y₀
  have hδ : 0 < min (1 / 2 : ℝ) (R / 2) := lt_min (by norm_num) (by positivity)
  have h2 : min (1 / 2 : ℝ) (R / 2) ≤ 1 / 2 := min_le_left _ _
  have hδR : min (1 / 2 : ℝ) (R / 2) < R := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  exact ⟨min (1 / 2 : ℝ) (R / 2), hδ, contHA a v y₀ (min (1 / 2 : ℝ) (R / 2)),
    differentiableOn_contHA ha hδ h2 hδR hv,
    fun ζ hζ hb => genH_eq_contHA ha h2 hδR hv hvu hζ hb,
    re_contHA_center hδ h2 hδR hv hvu⟩

noncomputable def hbarA (a : ℝ → ℝ) (ζ : ℂ) : ℂ := limUnder (𝓝[strip] ζ) (genH a)

section

variable {a : ℝ → ℝ}

lemma tendsto_of_local {y₀ δ : ℝ} {H : ℂ → ℂ} {ζ' : ℂ} (hH : DifferentiableOn ℂ H (ball (Complex.I * (y₀ : ℂ)) δ))
    (heq : ∀ ζ ∈ strip, ζ ∈ ball (Complex.I * (y₀ : ℂ)) δ → genH a ζ = H ζ)
    (hζ' : ζ' ∈ ball (Complex.I * (y₀ : ℂ)) δ) : Tendsto (genH a) (𝓝[strip] ζ') (𝓝 (H ζ')) := by
  have hc : ContinuousAt H ζ' := hH.continuousOn.continuousAt (isOpen_ball.mem_nhds hζ')
  have h1 : Tendsto H (𝓝[strip] ζ') (𝓝 (H ζ')) := hc.tendsto.mono_left nhdsWithin_le_nhds
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_ball.mem_nhds hζ')] with ζ hs hb
  exact (heq ζ hs hb).symm

lemma tendsto_oneSub_aux (ha : Amp a) {ζ : ℂ} {L : ℂ} (h : Tendsto (genH a) (𝓝[strip] (1 - ζ)) (𝓝 L)) :
    Tendsto (genH a) (𝓝[strip] ζ) (𝓝 L) := by
  have hmap : Tendsto (fun z : ℂ => 1 - z) (𝓝[strip] ζ) (𝓝[strip] (1 - ζ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_const.sub continuous_id).tendsto ζ).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact ⟨by simp; exact hz.2, by simp; exact hz.1⟩
  have := h.comp hmap
  refine this.congr (fun z => ?_)
  simp [Function.comp, genH_one_sub ha]

lemma tendsto_conj_aux (ha : Amp a) {ζ : ℂ} {L : ℂ} (h : Tendsto (genH a) (𝓝[strip] ζ) (𝓝 L)) :
    Tendsto (genH a) (𝓝[strip] (starRingEnd ℂ ζ)) (𝓝 (starRingEnd ℂ L)) := by
  have hmap : Tendsto (fun z : ℂ => starRingEnd ℂ z) (𝓝[strip] (starRingEnd ℂ ζ)) (𝓝[strip] ζ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun z : ℂ => starRingEnd ℂ z) (𝓝 (starRingEnd ℂ ζ)) (𝓝 ζ) := by
        have := (Complex.continuous_conj.tendsto (starRingEnd ℂ ζ))
        simpa using this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact ⟨by simpa using hz.1, by simpa using hz.2⟩
  have h2 := (Complex.continuous_conj.tendsto L).comp (h.comp hmap)
  refine h2.congr (fun z => ?_)
  simp only [Function.comp]
  rw [← genH_conj ha, Complex.conj_conj]

lemma tendsto_closedStrip (ha : Amp a) {ζ : ℂ} (hζ : ζ ∈ closedStrip) : ∃ L, Tendsto (genH a) (𝓝[strip] ζ) (𝓝 L) := by
  rcases hζ.1.eq_or_lt with h0 | h0
  · -- left edge
    have hζe : ζ = Complex.I * (ζ.im : ℂ) := by
      apply Complex.ext <;> simp [← h0]
    obtain ⟨δ, hδ, H, hH, heq, _⟩ := exists_edge_dataA ha ζ.im
    refine ⟨H ζ, tendsto_of_local hH heq ?_⟩
    rw [← hζe]; exact mem_ball_self hδ
  rcases hζ.2.eq_or_lt with h1 | h1
  · -- right edge: reflect
    have hmem : (1 - ζ) ∈ closedStrip := ⟨by simp [h1], by simp [h1]⟩
    have hre : (1 - ζ).re = 0 := by simp [h1]
    have hζe : 1 - ζ = Complex.I * ((1 - ζ).im : ℂ) := by
      apply Complex.ext <;> simp [hre]
    obtain ⟨δ, hδ, H, hH, heq, _⟩ := exists_edge_dataA ha (1 - ζ).im
    refine ⟨H (1 - ζ), tendsto_oneSub_aux ha (tendsto_of_local hH heq ?_)⟩
    rw [← hζe]; exact mem_ball_self hδ
  · -- interior
    have hs : ζ ∈ strip := ⟨h0, h1⟩
    refine ⟨genH a ζ, ?_⟩
    have hc : ContinuousAt (genH a) ζ := (differentiableOn_genH ha).continuousOn.continuousAt (isOpen_strip.mem_nhds hs)
    exact hc.tendsto.mono_left nhdsWithin_le_nhds

lemma hbarA_tendsto (ha : Amp a) {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    Tendsto (genH a) (𝓝[strip] ζ) (𝓝 (hbarA a ζ)) := by
  have := neBot_nhdsWithin_strip hζ
  obtain ⟨L, hL⟩ := tendsto_closedStrip ha hζ
  have : hbarA a ζ = L := hL.limUnder_eq
  rw [this]; exact hL

lemma hbarA_of_mem_strip (ha : Amp a) {ζ : ℂ} (hζ : ζ ∈ strip) : hbarA a ζ = genH a ζ := by
  have := neBot_nhdsWithin_strip (strip_subset_closedStrip hζ)
  have hc : ContinuousAt (genH a) ζ := (differentiableOn_genH ha).continuousOn.continuousAt (isOpen_strip.mem_nhds hζ)
  exact (hc.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq

lemma hbarA_eq_local {y₀ δ : ℝ} {H : ℂ → ℂ} {ζ' : ℂ}
    (hH : DifferentiableOn ℂ H (ball (Complex.I * (y₀ : ℂ)) δ))
    (heq : ∀ ζ ∈ strip, ζ ∈ ball (Complex.I * (y₀ : ℂ)) δ → genH a ζ = H ζ)
    (hζ' : ζ' ∈ ball (Complex.I * (y₀ : ℂ)) δ) (hcl : ζ' ∈ closedStrip) : hbarA a ζ' = H ζ' := by
  have := neBot_nhdsWithin_strip hcl
  exact (tendsto_of_local hH heq hζ').limUnder_eq

lemma hbarA_oneSub (ha : Amp a) {ζ : ℂ} (hζ : ζ ∈ closedStrip) : hbarA a (1 - ζ) = hbarA a ζ := by
  have hmem : (1 - ζ) ∈ closedStrip := ⟨by simp; exact hζ.2, by simp; exact hζ.1⟩
  have := neBot_nhdsWithin_strip hζ
  have h := tendsto_oneSub_aux ha (ζ := ζ) (hbarA_tendsto ha hmem)
  exact (h.limUnder_eq).symm

lemma hbarA_conj (ha : Amp a) {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    hbarA a (starRingEnd ℂ ζ) = starRingEnd ℂ (hbarA a ζ) := by
  have hmem : starRingEnd ℂ ζ ∈ closedStrip := ⟨by simpa using hζ.1, by simpa using hζ.2⟩
  have := neBot_nhdsWithin_strip hmem
  exact (tendsto_conj_aux ha (hbarA_tendsto ha hζ)).limUnder_eq

lemma re_hbarA_left (ha : Amp a) (y : ℝ) : (hbarA a (Complex.I * (y : ℂ))).re = a y := by
  obtain ⟨δ, hδ, H, hH, heq, hre⟩ := exists_edge_dataA ha y
  have hcl : Complex.I * (y : ℂ) ∈ closedStrip := ⟨by simp, by simp⟩
  rw [hbarA_eq_local hH heq (mem_ball_self hδ) hcl]
  exact hre

lemma re_hbarA_right (ha : Amp a) (y : ℝ) : (hbarA a (1 + Complex.I * (y : ℂ))).re = a y := by
  have hcl : (1 + Complex.I * (y : ℂ)) ∈ closedStrip := ⟨by simp, by simp⟩
  have h := hbarA_oneSub ha hcl
  have e : 1 - (1 + Complex.I * (y : ℂ)) = Complex.I * ((-y : ℝ) : ℂ) := by push_cast; ring
  rw [e] at h
  rw [← h, re_hbarA_left ha, ha.even]

lemma continuousOn_hbarA_left (ha : Amp a) {ζ : ℂ} (hζ : ζ ∈ closedStrip) (h0 : ζ.re = 0) :
    ContinuousWithinAt (hbarA a) closedStrip ζ := by
  have hζe : ζ = Complex.I * (ζ.im : ℂ) := by
    apply Complex.ext <;> simp [h0]
  obtain ⟨δ, hδ, H, hH, heq, _⟩ := exists_edge_dataA ha ζ.im
  have hb : ζ ∈ ball (Complex.I * (ζ.im : ℂ)) δ := by rw [← hζe]; exact mem_ball_self hδ
  have hc : ContinuousWithinAt H closedStrip ζ :=
    (hH.continuousOn.continuousAt (isOpen_ball.mem_nhds hb)).continuousWithinAt
  refine hc.congr_of_eventuallyEq ?_ (hbarA_eq_local hH heq hb hζ)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_ball.mem_nhds hb)] with ξ hcl hbl
  exact hbarA_eq_local hH heq hbl hcl

/-- **`ct:outer` (1), continuity.** `hbarA a` is continuous on the closed strip. -/
theorem continuousOn_hbarA (ha : Amp a) : ContinuousOn (hbarA a) closedStrip := by
  intro ζ hζ
  rcases hζ.1.eq_or_lt with h0 | h0
  · exact continuousOn_hbarA_left ha hζ h0.symm
  rcases hζ.2.eq_or_lt with h1 | h1
  · -- right edge
    have hmem : (1 - ζ) ∈ closedStrip := ⟨by simp [h1], by simp [h1]⟩
    have hre : (1 - ζ).re = 0 := by simp [h1]
    have hc := continuousOn_hbarA_left ha hmem hre
    have hmaps : MapsTo (fun z : ℂ => 1 - z) closedStrip closedStrip :=
      fun z hz => ⟨by simp; exact hz.2, by simp; exact hz.1⟩
    have hcomp : ContinuousWithinAt (fun z : ℂ => hbarA a (1 - z)) closedStrip ζ :=
      hc.comp (by fun_prop : Continuous fun z : ℂ => 1 - z).continuousWithinAt hmaps
    refine hcomp.congr (fun z hz => ?_) ?_
    · exact (hbarA_oneSub ha hz).symm
    · exact (hbarA_oneSub ha hζ).symm
  · have hs : ζ ∈ strip := ⟨h0, h1⟩
    have hc : ContinuousAt (genH a) ζ := (differentiableOn_genH ha).continuousOn.continuousAt (isOpen_strip.mem_nhds hs)
    have : hbarA a =ᶠ[𝓝 ζ] genH a := by
      filter_upwards [isOpen_strip.mem_nhds hs] with z hz using hbarA_of_mem_strip ha hz
    exact (hc.congr this.symm).continuousWithinAt


end

end FormalResearch.ModularBootstrap.FiveTerm.StripOuter
