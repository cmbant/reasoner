module

public import FormalResearch.ModularBootstrap.FiveTerm.StripCoord

/-!
# The Cauchy class on the half-disc and the decay of `Ψ_H` (FIVE-0 tool)

Source: `CFT/modular_bootstrap/paper/constant_term_universality.tex`, Lemma ctu.2a (`ctu:common-functional`),
proof of (1): "Applying Cauchy's theorem to `(H(z) - 1)/z²` on `Ω` indented by radius-`δ` arcs around
`0, 1, ±i`".  Here the indentation is replaced by the strip coordinate `z = tan(π s/4)` (`StripCoord`),
in which the four singular points are the two edge points `s = 0, 1` and the two strip ends, and the
contour step is Cauchy's theorem on a strip (`StripCauchy.strip_edge_cauchy`).

`CauchyClass H h₁` collects what the paper's admissible class gives for `H = F G`:

* `H` holomorphic on `Ω`, continuous on `closure Ω ∖ {i, -i, 1}`, `H(z̄) = conj H(z)`;
* `H(z) = 1 + h₁ z + O(|z|²)` as `z → 0` in `closure Ω` (so `H 0 = 1`);
* `‖H z‖ ‖1 + z²‖^{1-ε} ≤ C` on `closure Ω ∖ {i, -i, 1}`, i.e. `|H| = O(|1+z²|^{-(1-ε)})` (this includes
  boundedness near `z = 1` and the endpoint growth at `±i`; in the paper
  `|H| = O(|1+z²|^{a_∞-1}(1+|log|1+z²||)^{w-1/2})` with `a_∞ > 1/2`, and a log power is absorbed by a smaller
  power margin).  The values at the three singular points are not constrained.

`cauchyPsi H h₁ s = (π/4)(1+z²)(H z - 1 - h₁ z)/z²` with `z = tan(π s/4)` is then holomorphic on the open
strip, continuous on the closed strip off `{0, 1}`, and decays like `e^{-(επ/2)|Im s|}`
(`cauchyPsi_decay`).  All results are proved unconditionally.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

lemma isOpen_halfDisc : IsOpen halfDisc :=
  (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const Complex.continuous_re)

/-- The class of `H = F G`: holomorphic on `Ω`, continuous on the closure off `{i, -i, 1}`, real-symmetric,
with the jet `1 + h₁ z + O(z²)` at `0` and the endpoint growth `O(|1+z²|^{-(1-ε)})` on `Ω`. -/
structure CauchyClass (H : ℂ → ℂ) (h1 : ℝ) : Prop where
  diff : DifferentiableOn ℂ H halfDisc
  cont : ContinuousOn H (closure halfDisc \ {Complex.I, -Complex.I, 1})
  conj : ∀ z ∈ halfDisc, H (starRingEnd ℂ z) = starRingEnd ℂ (H z)
  jet : ∃ C r : ℝ, 0 < r ∧ ∀ z ∈ closure halfDisc, ‖z‖ < r → ‖H z - 1 - h1 * z‖ ≤ C * ‖z‖ ^ 2
  growth : ∃ C ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ z ∈ closure halfDisc, z ≠ Complex.I → z ≠ -Complex.I → z ≠ 1 →
    ‖H z‖ * ‖1 + z ^ 2‖ ^ (1 - ε) ≤ C

lemma halfDisc_ne_special {z : ℂ} (hz : z ∈ halfDisc) : z ≠ Complex.I ∧ z ≠ -Complex.I ∧ z ≠ 1 := by
  have h1 := hz.1
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> rw [h] at h1 <;> simp at h1

/-- The strip-coordinate integrand `Ψ_H(s) = (π/4) (1+z²)(H z - 1 - h₁ z)/z²`, `z = tan(π s/4)`. -/
noncomputable def cauchyPsi (H : ℂ → ℂ) (h1 : ℝ) (s : ℂ) : ℂ :=
  ((π / 4 : ℝ) : ℂ) * ((1 + sTan s ^ 2) * (H (sTan s) - 1 - h1 * sTan s) / sTan s ^ 2)

section

variable {H : ℂ → ℂ} {h1 : ℝ}

lemma sTan_ne_zero_strip {s : ℂ} (hs : s ∈ unitStrip) : sTan s ≠ 0 := by
  intro h
  have := (sTan_mem_halfDisc hs).2
  rw [h] at this
  simp at this

lemma cauchyPsi_differentiableOn (hH : CauchyClass H h1) :
    DifferentiableOn ℂ (cauchyPsi H h1) unitStrip := by
  intro s hs
  have hcl := unitStrip_subset_cl hs
  have hz := sTan_mem_halfDisc hs
  have h1' : DifferentiableAt ℂ sTan s := differentiableAt_sTan hcl
  have h2 : DifferentiableAt ℂ H (sTan s) := hH.diff.differentiableAt (isOpen_halfDisc.mem_nhds hz)
  have h3 : DifferentiableAt ℂ (fun s => H (sTan s)) s := h2.comp s h1'
  have hne : sTan s ^ 2 ≠ 0 := pow_ne_zero 2 (sTan_ne_zero_strip hs)
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold cauchyPsi
  refine (differentiableAt_const _).mul ?_
  refine DifferentiableAt.div ?_ (h1'.pow 2) hne
  exact ((differentiableAt_const _).add (h1'.pow 2)).mul ((h3.sub (differentiableAt_const _)).sub
    ((differentiableAt_const _).mul h1'))

lemma cauchyPsi_continuousOn (hH : CauchyClass H h1) :
    ContinuousOn (cauchyPsi H h1) (unitStripCl \ {0, 1}) := by
  have hmaps : ∀ s ∈ unitStripCl \ {0, 1}, sTan s ∈ closure halfDisc \ {Complex.I, -Complex.I, 1} := by
    intro s hs
    refine ⟨sTan_mem_closure hs.1, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    have h0 : s ≠ 1 := fun h => hs.2 (Or.inr h)
    exact ⟨sTan_ne_I s hs.1, sTan_ne_neg_I s hs.1, fun h => h0 ((sTan_eq_one_iff hs.1).1 h)⟩
  have hT : ContinuousOn sTan (unitStripCl \ {0, 1}) := continuousOn_sTan.mono Set.sdiff_subset
  have hHT : ContinuousOn (fun s => H (sTan s)) (unitStripCl \ {0, 1}) := hH.cont.comp hT hmaps
  have hne : ∀ s ∈ unitStripCl \ {0, 1}, sTan s ^ 2 ≠ 0 := by
    intro s hs
    have h0 : s ≠ 0 := fun h => hs.2 (Or.inl h)
    exact pow_ne_zero 2 (fun h => h0 ((sTan_eq_zero_iff hs.1).1 h))
  unfold cauchyPsi
  refine continuousOn_const.mul ?_
  refine ContinuousOn.div ?_ (hT.pow 2) hne
  exact (continuousOn_const.add (hT.pow 2)).mul ((hHT.sub continuousOn_const).sub (continuousOn_const.mul hT))

lemma mul_norm_le {t m C ε E : ℝ} (ht : 0 < t) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hE : 0 < E)
    (htE : t ≤ 4 * E) (hC : m * t ^ (1 - ε) ≤ C) :
    t * m ≤ max C 0 * (4 * E ^ ε) := by
  have h1 : t = t ^ (1 - ε) * t ^ ε := by
    rw [← Real.rpow_add ht]; simp
  have h2 : t ^ ε ≤ (4 * E) ^ ε := Real.rpow_le_rpow ht.le htE hε0.le
  have h3 : (4 * E) ^ ε = 4 ^ ε * E ^ ε := Real.mul_rpow (by norm_num) hE.le
  have h4 : (4 : ℝ) ^ ε ≤ 4 := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 4 by norm_num) hε1
    simpa using this
  have h5 : 0 ≤ E ^ ε := Real.rpow_nonneg hE.le _
  have h6 : 0 ≤ t ^ ε := Real.rpow_nonneg ht.le _
  calc t * m = (m * t ^ (1 - ε)) * t ^ ε := by
        conv_lhs => rw [h1]
        ring
    _ ≤ max C 0 * t ^ ε := by
        apply mul_le_mul (le_trans hC (le_max_left _ _)) le_rfl h6 (le_max_right _ _)
    _ ≤ max C 0 * (4 * E ^ ε) := by
        apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
        calc t ^ ε ≤ (4 * E) ^ ε := h2
          _ = 4 ^ ε * E ^ ε := h3
          _ ≤ 4 * E ^ ε := by nlinarith only [h4, h5]

/-- `Ψ_H` decays exponentially along the strip. -/
lemma cauchyPsi_decay (hH : CauchyClass H h1) :
    ∃ K ε' : ℝ, 0 < ε' ∧ ∀ s ∈ unitStrip, ‖cauchyPsi H h1 s‖ ≤ K * Real.exp (-(ε' * |s.im|)) := by
  obtain ⟨C₁, r, hr, hjet0⟩ := hH.jet
  obtain ⟨Cg, ε, hε0, hε1, hgr0⟩ := hH.growth
  have hjet : ∀ z ∈ halfDisc, ‖z‖ < r → ‖H z - 1 - h1 * z‖ ≤ C₁ * ‖z‖ ^ 2 :=
    fun z hz hzr => hjet0 z (subset_closure hz) hzr
  have hgr : ∀ z ∈ halfDisc, ‖H z‖ * ‖1 + z ^ 2‖ ^ (1 - ε) ≤ Cg := fun z hz =>
    hgr0 z (subset_closure hz) (halfDisc_ne_special hz).1 (halfDisc_ne_special hz).2.1
      (halfDisc_ne_special hz).2.2
  refine ⟨Real.pi * max C₁ 0 + Real.pi / (r ^ 2) * (max Cg 0 + 1 + |h1|), ε * π / 2, by positivity, ?_⟩
  intro s hs
  have hcl := unitStrip_subset_cl hs
  have hz := sTan_mem_halfDisc hs
  set z := sTan s with hzdef
  set τ := s.im with hτ
  set E := Real.exp (-(π * |τ| / 2)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by
    rw [hE]; apply Real.exp_le_one_iff.mpr; have := Real.pi_pos; have := abs_nonneg τ; nlinarith
  set t := ‖1 + z ^ 2‖ with ht
  have htE : t ≤ 4 * E := norm_one_add_sTan_sq_le hcl
  have htpos : 0 < t := by
    rw [ht, norm_one_add_sTan_sq hcl]
    have := cos_ne_zero_of_cl hcl
    positivity
  have hzne : z ≠ 0 := sTan_ne_zero_strip hs
  have hz2 : 0 < ‖z‖ ^ 2 := by positivity
  set A := Real.exp (-(ε * π / 2 * |τ|)) with hA
  have hEA : E ^ ε = A := by
    rw [hE, hA, ← Real.exp_mul]; congr 1; ring
  have hEleA : E ≤ A := by
    rw [← hEA]
    calc E = E ^ (1 : ℝ) := (Real.rpow_one E).symm
      _ ≤ E ^ ε := Real.rpow_le_rpow_of_exponent_ge hEpos hE1 hε1
  have hnorm : ‖cauchyPsi H h1 s‖ = π / 4 * (t * ‖H z - 1 - h1 * z‖ / ‖z‖ ^ 2) := by
    unfold cauchyPsi
    rw [norm_mul, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hAnn : 0 ≤ A := Real.exp_nonneg _
  rw [hnorm]
  by_cases hzr : ‖z‖ < r
  · have h1' := hjet z hz hzr
    have : t * ‖H z - 1 - h1 * z‖ / ‖z‖ ^ 2 ≤ t * max C₁ 0 := by
      rw [div_le_iff₀ hz2]
      calc t * ‖H z - 1 - h1 * z‖ ≤ t * (max C₁ 0 * ‖z‖ ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ htpos.le
            exact le_trans h1' (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        _ = t * max C₁ 0 * ‖z‖ ^ 2 := by ring
    have h4 : t * max C₁ 0 ≤ 4 * A * max C₁ 0 := by
      apply mul_le_mul_of_nonneg_right _ (le_max_right _ _)
      linarith
    have hpi := Real.pi_pos
    have hC0 := le_max_right C₁ 0
    have hK : π / 4 * (t * ‖H z - 1 - h1 * z‖ / ‖z‖ ^ 2) ≤ π * max C₁ 0 * A := by
      calc π / 4 * (t * ‖H z - 1 - h1 * z‖ / ‖z‖ ^ 2) ≤ π / 4 * (4 * A * max C₁ 0) := by
            apply mul_le_mul_of_nonneg_left (le_trans this h4) (by positivity)
        _ = π * max C₁ 0 * A := by ring
    have hK2 : 0 ≤ π / r ^ 2 * (max Cg 0 + 1 + |h1|) * A := by positivity
    calc _ ≤ π * max C₁ 0 * A := hK
      _ ≤ (π * max C₁ 0 + π / r ^ 2 * (max Cg 0 + 1 + |h1|)) * A := by nlinarith only [hK2, hAnn]
  · push Not at hzr
    have hzlt : ‖z‖ < 1 := hz.1
    have hnum : ‖H z - 1 - h1 * z‖ ≤ ‖H z‖ + 1 + |h1| := by
      calc ‖H z - 1 - h1 * z‖ ≤ ‖H z - 1‖ + ‖(h1 : ℂ) * z‖ := norm_sub_le _ _
        _ ≤ (‖H z‖ + ‖(1 : ℂ)‖) + ‖(h1 : ℂ) * z‖ := by gcongr; exact norm_sub_le _ _
        _ = ‖H z‖ + 1 + |h1| * ‖z‖ := by
            rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ‖H z‖ + 1 + |h1| := by nlinarith only [abs_nonneg h1, hzlt, norm_nonneg z]
    have hG := mul_norm_le htpos hε0 hε1 hEpos htE (hgr z hz)
    have hr2 : r ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith only [hzr, hr]
    have hfrac : t * ‖H z - 1 - h1 * z‖ / ‖z‖ ^ 2 ≤ t * (‖H z‖ + 1 + |h1|) / r ^ 2 := by
      calc t * ‖H z - 1 - h1 * z‖ / ‖z‖ ^ 2 ≤ t * (‖H z‖ + 1 + |h1|) / ‖z‖ ^ 2 := by
            apply div_le_div_of_nonneg_right _ hz2.le
            exact mul_le_mul_of_nonneg_left hnum htpos.le
        _ ≤ t * (‖H z‖ + 1 + |h1|) / r ^ 2 := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity) hr2
    have hpi := Real.pi_pos
    have hexp : t * (‖H z‖ + 1 + |h1|) ≤ 4 * (max Cg 0 + 1 + |h1|) * A := by
      have e1 : t * (‖H z‖ + 1 + |h1|) = t * ‖H z‖ + t * (1 + |h1|) := by ring
      have e2 : t * ‖H z‖ ≤ max Cg 0 * (4 * A) := by rw [← hEA]; exact hG
      have e3 : t * (1 + |h1|) ≤ 4 * A * (1 + |h1|) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      rw [e1]
      nlinarith only [e2, e3]
    calc π / 4 * (t * ‖H z - 1 - h1 * z‖ / ‖z‖ ^ 2)
        ≤ π / 4 * (t * (‖H z‖ + 1 + |h1|) / r ^ 2) := by gcongr
      _ ≤ π / 4 * (4 * (max Cg 0 + 1 + |h1|) * A / r ^ 2) := by
          gcongr
      _ = π / r ^ 2 * (max Cg 0 + 1 + |h1|) * A := by field_simp
      _ ≤ (π * max C₁ 0 + π / r ^ 2 * (max Cg 0 + 1 + |h1|)) * A := by
          have : 0 ≤ π * max C₁ 0 := by positivity
          nlinarith only [this, hAnn]

end

end FormalResearch.ModularBootstrap.FiveTerm
