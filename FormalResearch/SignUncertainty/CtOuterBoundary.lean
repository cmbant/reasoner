module

public import FormalResearch.SignUncertainty.CtOuterEdge

/-!
# The continuous boundary extension of `h` (`ct:outer` (1))

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:outer` (1) ("continuous on `\overline S`",
boundary real part `Re h(it) = Re h(1 + it) = u_r(t)`).  **Proved.**

`outerHbar ζ = lim_{ξ → ζ, ξ ∈ S} h(ξ)` (`limUnder`) is the continuous extension of `h` to the closed strip
`closedStrip = {0 ≤ Re ζ ≤ 1}` (`= closure strip`).  The local holomorphic continuation across the edge
(`CtOuterEdge`) shows the limits exist, that `outerHbar` is continuous on `closedStrip`, and the boundary real part
`Re outerHbar(i y) = Re outerHbar(1 + i y) = u_r(y)` (`re_outerHbar_left`, `re_outerHbar_right`).  Real
symmetry, `h(1 - ζ) = h(ζ)` and the decay `Re h ≤ -2 log(1 + |Im ζ|) + C` pass to `outerHbar`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- The closed strip `0 ≤ Re ζ ≤ 1`. -/
def closedStrip : Set ℂ := {ζ | 0 ≤ ζ.re ∧ ζ.re ≤ 1}

lemma strip_subset_closedStrip : strip ⊆ closedStrip := fun _ h => ⟨h.1.le, h.2.le⟩

lemma isClosed_closedStrip : IsClosed closedStrip :=
  (isClosed_le continuous_const Complex.continuous_re).inter (isClosed_le Complex.continuous_re continuous_const)

lemma closure_strip_eq : closure strip = closedStrip := by
  have h : strip = Complex.re ⁻¹' Ioo (0 : ℝ) 1 := rfl
  have h2 := Complex.isOpenMap_re.preimage_closure_eq_closure_preimage Complex.continuous_re (Ioo (0 : ℝ) 1)
  rw [h, ← h2, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  rfl

/-- Local edge data at every real `y₀`: a ball `B(i y₀, δ)` and a holomorphic `H` on it with `h = H` on
`S ∩ B(i y₀, δ)` and `Re H(i y₀) = u_r(y₀)`. -/
lemma exists_edge_data (y₀ : ℝ) :
    ∃ δ > 0, ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball (Complex.I * (y₀ : ℂ)) δ) ∧
      (∀ ζ ∈ strip, ζ ∈ ball (Complex.I * (y₀ : ℂ)) δ → outerH ζ = H ζ) ∧ (H (Complex.I * (y₀ : ℂ))).re = uR y₀ := by
  obtain ⟨r, hr, v, hv, hvu⟩ := exists_holo_uR y₀
  have hδ : 0 < min (1 / 2 : ℝ) (r / 2) := lt_min (by norm_num) (by positivity)
  have h2 : min (1 / 2 : ℝ) (r / 2) ≤ 1 / 2 := min_le_left _ _
  have hδR : min (1 / 2 : ℝ) (r / 2) < r := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  exact ⟨min (1 / 2 : ℝ) (r / 2), hδ, contH v y₀ (min (1 / 2 : ℝ) (r / 2)),
    differentiableOn_contH hδ h2 hδR hv,
    fun ζ hζ hb => outerH_eq_contH h2 hδR hv hvu hζ hb,
    re_contH_center hδ h2 hδR hv hvu⟩

/-- The boundary extension of `h` to the closed strip. -/
noncomputable def outerHbar (ζ : ℂ) : ℂ := limUnder (𝓝[strip] ζ) outerH

lemma neBot_nhdsWithin_strip {ζ : ℂ} (hζ : ζ ∈ closedStrip) : NeBot (𝓝[strip] ζ) :=
  mem_closure_iff_nhdsWithin_neBot.mp (by rw [closure_strip_eq]; exact hζ)

lemma tendsto_of_local {y₀ δ : ℝ} {H : ℂ → ℂ} {ζ' : ℂ} (hH : DifferentiableOn ℂ H (ball (Complex.I * (y₀ : ℂ)) δ))
    (heq : ∀ ζ ∈ strip, ζ ∈ ball (Complex.I * (y₀ : ℂ)) δ → outerH ζ = H ζ)
    (hζ' : ζ' ∈ ball (Complex.I * (y₀ : ℂ)) δ) : Tendsto outerH (𝓝[strip] ζ') (𝓝 (H ζ')) := by
  have hc : ContinuousAt H ζ' := hH.continuousOn.continuousAt (isOpen_ball.mem_nhds hζ')
  have h1 : Tendsto H (𝓝[strip] ζ') (𝓝 (H ζ')) := hc.tendsto.mono_left nhdsWithin_le_nhds
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_ball.mem_nhds hζ')] with ζ hs hb
  exact (heq ζ hs hb).symm

lemma tendsto_oneSub_aux {ζ : ℂ} {L : ℂ} (h : Tendsto outerH (𝓝[strip] (1 - ζ)) (𝓝 L)) :
    Tendsto outerH (𝓝[strip] ζ) (𝓝 L) := by
  have hmap : Tendsto (fun z : ℂ => 1 - z) (𝓝[strip] ζ) (𝓝[strip] (1 - ζ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_const.sub continuous_id).tendsto ζ).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact ⟨by simp; exact hz.2, by simp; exact hz.1⟩
  have := h.comp hmap
  refine this.congr (fun z => ?_)
  simp [Function.comp, outerH_one_sub]

lemma tendsto_conj_aux {ζ : ℂ} {L : ℂ} (h : Tendsto outerH (𝓝[strip] ζ) (𝓝 L)) :
    Tendsto outerH (𝓝[strip] (starRingEnd ℂ ζ)) (𝓝 (starRingEnd ℂ L)) := by
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
  rw [← outerH_conj, Complex.conj_conj]

lemma tendsto_closedStrip {ζ : ℂ} (hζ : ζ ∈ closedStrip) : ∃ L, Tendsto outerH (𝓝[strip] ζ) (𝓝 L) := by
  rcases hζ.1.eq_or_lt with h0 | h0
  · -- left edge
    have hζe : ζ = Complex.I * (ζ.im : ℂ) := by
      apply Complex.ext <;> simp [← h0]
    obtain ⟨δ, hδ, H, hH, heq, _⟩ := exists_edge_data ζ.im
    refine ⟨H ζ, tendsto_of_local hH heq ?_⟩
    rw [← hζe]; exact mem_ball_self hδ
  rcases hζ.2.eq_or_lt with h1 | h1
  · -- right edge: reflect
    have hmem : (1 - ζ) ∈ closedStrip := ⟨by simp [h1], by simp [h1]⟩
    have hre : (1 - ζ).re = 0 := by simp [h1]
    have hζe : 1 - ζ = Complex.I * ((1 - ζ).im : ℂ) := by
      apply Complex.ext <;> simp [hre]
    obtain ⟨δ, hδ, H, hH, heq, _⟩ := exists_edge_data (1 - ζ).im
    refine ⟨H (1 - ζ), tendsto_oneSub_aux (tendsto_of_local hH heq ?_)⟩
    rw [← hζe]; exact mem_ball_self hδ
  · -- interior
    have hs : ζ ∈ strip := ⟨h0, h1⟩
    refine ⟨outerH ζ, ?_⟩
    have hc : ContinuousAt outerH ζ := differentiableOn_outerH.continuousOn.continuousAt (isOpen_strip.mem_nhds hs)
    exact hc.tendsto.mono_left nhdsWithin_le_nhds

lemma outerHbar_tendsto {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    Tendsto outerH (𝓝[strip] ζ) (𝓝 (outerHbar ζ)) := by
  have := neBot_nhdsWithin_strip hζ
  obtain ⟨L, hL⟩ := tendsto_closedStrip hζ
  have : outerHbar ζ = L := hL.limUnder_eq
  rw [this]; exact hL

lemma outerHbar_of_mem_strip {ζ : ℂ} (hζ : ζ ∈ strip) : outerHbar ζ = outerH ζ := by
  have := neBot_nhdsWithin_strip (strip_subset_closedStrip hζ)
  have hc : ContinuousAt outerH ζ := differentiableOn_outerH.continuousOn.continuousAt (isOpen_strip.mem_nhds hζ)
  exact (hc.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq

lemma outerHbar_eq_local {y₀ δ : ℝ} {H : ℂ → ℂ} {ζ' : ℂ}
    (hH : DifferentiableOn ℂ H (ball (Complex.I * (y₀ : ℂ)) δ))
    (heq : ∀ ζ ∈ strip, ζ ∈ ball (Complex.I * (y₀ : ℂ)) δ → outerH ζ = H ζ)
    (hζ' : ζ' ∈ ball (Complex.I * (y₀ : ℂ)) δ) (hcl : ζ' ∈ closedStrip) : outerHbar ζ' = H ζ' := by
  have := neBot_nhdsWithin_strip hcl
  exact (tendsto_of_local hH heq hζ').limUnder_eq

lemma outerHbar_oneSub {ζ : ℂ} (hζ : ζ ∈ closedStrip) : outerHbar (1 - ζ) = outerHbar ζ := by
  have hmem : (1 - ζ) ∈ closedStrip := ⟨by simp; exact hζ.2, by simp; exact hζ.1⟩
  have := neBot_nhdsWithin_strip hζ
  have h := tendsto_oneSub_aux (ζ := ζ) (outerHbar_tendsto hmem)
  exact (h.limUnder_eq).symm

lemma outerHbar_conj {ζ : ℂ} (hζ : ζ ∈ closedStrip) :
    outerHbar (starRingEnd ℂ ζ) = starRingEnd ℂ (outerHbar ζ) := by
  have hmem : starRingEnd ℂ ζ ∈ closedStrip := ⟨by simpa using hζ.1, by simpa using hζ.2⟩
  have := neBot_nhdsWithin_strip hmem
  exact (tendsto_conj_aux (outerHbar_tendsto hζ)).limUnder_eq

lemma re_outerHbar_left (y : ℝ) : (outerHbar (Complex.I * (y : ℂ))).re = uR y := by
  obtain ⟨δ, hδ, H, hH, heq, hre⟩ := exists_edge_data y
  have hcl : Complex.I * (y : ℂ) ∈ closedStrip := ⟨by simp, by simp⟩
  rw [outerHbar_eq_local hH heq (mem_ball_self hδ) hcl]
  exact hre

lemma re_outerHbar_right (y : ℝ) : (outerHbar (1 + Complex.I * (y : ℂ))).re = uR y := by
  have hcl : (1 + Complex.I * (y : ℂ)) ∈ closedStrip := ⟨by simp, by simp⟩
  have h := outerHbar_oneSub hcl
  have e : 1 - (1 + Complex.I * (y : ℂ)) = Complex.I * ((-y : ℝ) : ℂ) := by push_cast; ring
  rw [e] at h
  rw [← h, re_outerHbar_left, uR_neg]

lemma continuousOn_outerHbar_left {ζ : ℂ} (hζ : ζ ∈ closedStrip) (h0 : ζ.re = 0) :
    ContinuousWithinAt outerHbar closedStrip ζ := by
  have hζe : ζ = Complex.I * (ζ.im : ℂ) := by
    apply Complex.ext <;> simp [h0]
  obtain ⟨δ, hδ, H, hH, heq, _⟩ := exists_edge_data ζ.im
  have hb : ζ ∈ ball (Complex.I * (ζ.im : ℂ)) δ := by rw [← hζe]; exact mem_ball_self hδ
  have hc : ContinuousWithinAt H closedStrip ζ :=
    (hH.continuousOn.continuousAt (isOpen_ball.mem_nhds hb)).continuousWithinAt
  refine hc.congr_of_eventuallyEq ?_ (outerHbar_eq_local hH heq hb hζ)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_ball.mem_nhds hb)] with ξ hcl hbl
  exact outerHbar_eq_local hH heq hbl hcl

/-- **`ct:outer` (1), continuity.** `outerHbar` is continuous on the closed strip. -/
theorem continuousOn_outerHbar : ContinuousOn outerHbar closedStrip := by
  intro ζ hζ
  rcases hζ.1.eq_or_lt with h0 | h0
  · exact continuousOn_outerHbar_left hζ h0.symm
  rcases hζ.2.eq_or_lt with h1 | h1
  · -- right edge
    have hmem : (1 - ζ) ∈ closedStrip := ⟨by simp [h1], by simp [h1]⟩
    have hre : (1 - ζ).re = 0 := by simp [h1]
    have hc := continuousOn_outerHbar_left hmem hre
    have hmaps : MapsTo (fun z : ℂ => 1 - z) closedStrip closedStrip :=
      fun z hz => ⟨by simp; exact hz.2, by simp; exact hz.1⟩
    have hcomp : ContinuousWithinAt (fun z : ℂ => outerHbar (1 - z)) closedStrip ζ :=
      hc.comp (by fun_prop : Continuous fun z : ℂ => 1 - z).continuousWithinAt hmaps
    refine hcomp.congr (fun z hz => ?_) ?_
    · exact (outerHbar_oneSub hz).symm
    · exact (outerHbar_oneSub hζ).symm
  · have hs : ζ ∈ strip := ⟨h0, h1⟩
    have hc : ContinuousAt outerH ζ := differentiableOn_outerH.continuousOn.continuousAt (isOpen_strip.mem_nhds hs)
    have : outerHbar =ᶠ[𝓝 ζ] outerH := by
      filter_upwards [isOpen_strip.mem_nhds hs] with z hz using outerHbar_of_mem_strip hz
    exact (hc.congr this.symm).continuousWithinAt

/-- Decay of the real part on the closed strip. -/
theorem re_outerHbar_bound : ∃ C : ℝ, ∀ ζ ∈ closedStrip, (outerHbar ζ).re ≤ -2 * Real.log (1 + |ζ.im|) + C := by
  obtain ⟨C, hC⟩ := re_outerH_bound
  refine ⟨C, fun ζ hζ => ?_⟩
  have := neBot_nhdsWithin_strip hζ
  have hf : Tendsto (fun ξ => (outerH ξ).re) (𝓝[strip] ζ) (𝓝 (outerHbar ζ).re) :=
    (Complex.continuous_re.tendsto _).comp (outerHbar_tendsto hζ)
  have hg : Tendsto (fun ξ : ℂ => -2 * Real.log (1 + |ξ.im|) + C) (𝓝[strip] ζ)
      (𝓝 (-2 * Real.log (1 + |ζ.im|) + C)) := by
    have : Continuous fun ξ : ℂ => -2 * Real.log (1 + |ξ.im|) + C := by
      refine Continuous.add (Continuous.mul continuous_const (Continuous.log ?_ ?_)) continuous_const
      · fun_prop
      · intro ξ; positivity
    exact (this.tendsto ζ).mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto hf hg ?_
  filter_upwards [self_mem_nhdsWithin] with ξ hξ using hC ξ hξ

end FormalResearch.SignUncertainty.CtOuter
