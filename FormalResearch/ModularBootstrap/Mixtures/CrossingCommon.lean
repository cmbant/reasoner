module

public import FormalResearch.ModularBootstrap.Mixtures.CrossingPort

/-!
# `CrossingBounds` for the common source class

`positive_mixtures.tex`, Lemma PM.3 (a), the input step: "the standing-source argument after `ds:source-floor`
verifies the hypotheses of `fw:crossing`".  At a charge with the floor (`FloorData.At a`) the three facts bundled in
`CrossingBounds src a` follow from the sandwich `d_λ V_{Q_0} ≤ V ≤ ‖λ‖_TV K_a`:

* `V ≥ 0` (`FloorData.At.nonneg_V`);
* `ρ_src ≤ ‖λ‖_TV ρ_{Q ≡ 1}`, then the upper bound of the fixed-weight `rhoDensity_le_cardyWeight` for `Q ≡ 1`;
* `ρ_src ≥ d_λ ρ_{Q_0}` on `t > 0`, then the large-`t` lower bound of the fixed-weight
  `rhoDensity_ge_cardyWeight_large` for `Q_0`.

The reduced densities `V/t^{w-1}` are compared on `t > 0` and extended to `t = 0` by continuity.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight

private lemma le_of_pos_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ t : ℝ, 0 < t → f t ≤ g t) {t : ℝ} (ht : 0 ≤ t) : f t ≤ g t := by
  rcases ht.eq_or_lt with rfl | htp
  · have h1 : Tendsto (fun s => g s - f s) (𝓝[>] 0) (𝓝 (g 0 - f 0)) :=
      (hg.sub hf).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : 0 ≤ g 0 - f 0 := by
      refine ge_of_tendsto h1 ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      linarith [h s hs]
    linarith
  · exact h t htp

lemma rho_eq (S : ShiftSource) (a t : ℝ) :
    S.rhoDensity a t = (((S.w - 1).factorial : ℝ) / (2 * π) ^ S.w * (2 * π)) * S.cardyVReduced a t := by
  unfold ShiftSource.rhoDensity; ring

namespace FloorData.At

variable {src : ShiftSource} {F : FloorData src} {a : ℝ}

/-- The reduced Cardy weight of `Q ≡ 1` at the weight of the source (`V/t^{w-1} = K^{(w)}_a/t^{w-1}`). -/
noncomputable abbrev unitSource (src : ShiftSource) : ShiftSource :=
  ShiftSource.ofProblem (trivialProductProblem src.w src.hw)

/-- The reduced weight is dominated: `V_red ≤ ‖λ‖_TV K_red` on `t ≥ 0`. -/
lemma red_le (h : F.At a) {t : ℝ} (ht : 0 ≤ t) :
    src.cardyVReduced a t ≤ src.tv * (unitSource src).cardyVReduced a t := by
  refine le_of_pos_le (g := fun s => src.tv * (unitSource src).cardyVReduced a s)
    (src.continuous_cardyVReduced a)
    (continuous_const.mul ((unitSource src).continuous_cardyVReduced a)) (fun s hs => ?_) ht
  have h1 := h.upper hs.le
  have e1 := src.cardyV_eq_pow_mul_reduced a s
  have e2 : kernelK src.w a s = s ^ (src.w - 1) * (unitSource src).cardyVReduced a s := by
    have := (unitSource src).cardyV_eq_pow_mul_reduced a s
    rwa [unitSource, ofProblem_cardyV, trivial_cardyV] at this
  rw [e1, e2] at h1
  have hp : 0 < s ^ (src.w - 1) := pow_pos hs _
  refine le_of_mul_le_mul_left ?_ hp
  linarith

/-- The reduced weight dominates the floor: `d_λ V_{Q_0, red} ≤ V_red` on `t > 0`. -/
lemma red_ge (h : F.At a) {t : ℝ} (ht : 0 < t) :
    F.d * (ShiftSource.ofProblem F.prob).cardyVReduced a t ≤ src.cardyVReduced a t := by
  have h1 := h.lower ht
  have e1 := src.cardyV_eq_pow_mul_reduced a t
  have e2 : F.prob.cardyV a t = t ^ (src.w - 1) * (ShiftSource.ofProblem F.prob).cardyVReduced a t :=
    (ShiftSource.ofProblem F.prob).cardyV_eq_pow_mul_reduced a t
  rw [e1, e2] at h1
  have hp : 0 < t ^ (src.w - 1) := pow_pos ht _
  refine le_of_mul_le_mul_left ?_ hp
  linarith

/-- **`CrossingBounds` from the floor** (`Lemma PM.3 (a)`, input of `fw:crossing`). -/
theorem crossingBounds (h : F.At a) : CrossingBounds src a where
  pos := h.pos
  nonneg t ht := h.nonneg_V ht
  rho_le := by
    obtain ⟨C, hC, hle⟩ := (trivialProductProblem src.w src.hw).rhoDensity_le_cardyWeight (a := a)
      (by rw [trivialProductProblem_totalShift]; exact h.pos.le) h.pos
    refine ⟨src.tv * C, mul_pos h.tv_pos hC, fun t ht => ?_⟩
    have h1 := h.red_le ht
    have h2 := hle t ht
    have hκ : 0 ≤ ((src.w - 1).factorial : ℝ) / (2 * π) ^ src.w * (2 * π) := by positivity
    have e1 : src.rhoDensity a t =
        (((src.w - 1).factorial : ℝ) / (2 * π) ^ src.w * (2 * π)) * src.cardyVReduced a t :=
      rho_eq src a t
    have e2 : (trivialProductProblem src.w src.hw).rhoDensity a t =
        (((src.w - 1).factorial : ℝ) / (2 * π) ^ src.w * (2 * π)) *
          (unitSource src).cardyVReduced a t := by
      exact rho_eq (unitSource src) a t
    rw [e2] at h2
    calc src.rhoDensity a t
        = (((src.w - 1).factorial : ℝ) / (2 * π) ^ src.w * (2 * π)) * src.cardyVReduced a t := e1
      _ ≤ (((src.w - 1).factorial : ℝ) / (2 * π) ^ src.w * (2 * π)) *
            (src.tv * (unitSource src).cardyVReduced a t) := mul_le_mul_of_nonneg_left h1 hκ
      _ = src.tv * ((((src.w - 1).factorial : ℝ) / (2 * π) ^ src.w * (2 * π)) *
            (unitSource src).cardyVReduced a t) := by ring
      _ ≤ src.tv * (C * cardyWeight (-((src.w - 1 : ℝ) / 2 + 1 / 4))
            (2 * Real.sqrt 2 * π * Real.sqrt a) t) := mul_le_mul_of_nonneg_left h2 src.tv_nonneg
      _ = src.tv * C * cardyWeight (-((src.w - 1 : ℝ) / 2 + 1 / 4))
            (2 * Real.sqrt 2 * π * Real.sqrt a) t := by ring
  rho_ge := by
    obtain ⟨c, T₀, hc, hT₀, hge⟩ := F.prob.rhoDensity_ge_cardyWeight_large h.prob_shift h.pos
    refine ⟨F.d * c, T₀, mul_pos F.hd hc, hT₀, fun t ht => ?_⟩
    have htp : 0 < t := lt_of_lt_of_le (by linarith) ht
    have h1 := h.red_ge htp
    have h2 := hge t ht
    have hκ : 0 ≤ ((src.w - 1).factorial : ℝ) / (2 * π) ^ src.w * (2 * π) := by positivity
    have e1 : src.rhoDensity a t =
        (((src.w - 1).factorial : ℝ) / (2 * π) ^ src.w * (2 * π)) * src.cardyVReduced a t :=
      rho_eq src a t
    have e2 : F.prob.rhoDensity a t =
        (((src.w - 1).factorial : ℝ) / (2 * π) ^ src.w * (2 * π)) *
          (ShiftSource.ofProblem F.prob).cardyVReduced a t := by
      exact rho_eq (ShiftSource.ofProblem F.prob) a t
    rw [e2] at h2
    calc F.d * c * cardyWeight (-((src.w - 1 : ℝ) / 2 + 1 / 4))
          (2 * Real.sqrt 2 * π * Real.sqrt a) t
        = F.d * (c * cardyWeight (-((src.w - 1 : ℝ) / 2 + 1 / 4))
          (2 * Real.sqrt 2 * π * Real.sqrt a) t) := by ring
      _ ≤ F.d * ((((src.w - 1).factorial : ℝ) / (2 * π) ^ src.w * (2 * π)) *
            (ShiftSource.ofProblem F.prob).cardyVReduced a t) :=
          mul_le_mul_of_nonneg_left h2 F.hd.le
      _ = (((src.w - 1).factorial : ℝ) / (2 * π) ^ src.w * (2 * π)) *
            (F.d * (ShiftSource.ofProblem F.prob).cardyVReduced a t) := by ring
      _ ≤ (((src.w - 1).factorial : ℝ) / (2 * π) ^ src.w * (2 * π)) * src.cardyVReduced a t :=
          mul_le_mul_of_nonneg_left h1 hκ
      _ = src.rhoDensity a t := e1.symm

end FloorData.At

end FormalResearch.ModularBootstrap.Mixtures
