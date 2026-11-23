module

public import FormalResearch.ModularBootstrap.Upper.Membership.CombDecay
public import FormalResearch.ModularBootstrap.Upper.Holes.BandLobe

/-!
# The reference comb satisfies (i) and (iii) of Lemma `K7`

Final sentence of the proof of `cmb:K7` (`comb_estimates.tex`): for `B^{(f)}`, hypotheses (i)-(iii)
are `K1(a)`, `K3` and `K6(a)`.  Here (i) and (iii) are verified for `refComb c' f η₀`
(`f ≥ 1`, `η₀ ∈ [0, 1/4]`, all sufficiently large `c'`): evenness and reality on `ℝ` (the comb is a
product of the factors `blaschkeT`, even in `b`, with conjugate-paired zeros), `K1(a)`
(`refComb_K1a`: `|B| ≤ 1` on `|Im b| ≤ 1/2`, `|B| = 1` on `|Im b| = 1/2`, holomorphy on `|Im b| < 7/8`),
and `K6(a)` (`band_upper_K6a_bdd`).  This is the non-vacuity of `InnerCombHyp`.
Hypothesis (ii) (`K3`, the phase `Φ₁` with `|Φ₁^{(i)}| ≤ M`) and `SaddleTailBound` are not used here.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Membership

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Holes

lemma refComb_neg (c' : ℝ) (f : ℕ) (η₀ : ℝ) (b : ℂ) :
    refComb c' f η₀ (-b) = refComb c' f η₀ b := by
  unfold refComb
  simp only [blaschkeT_neg_b]

lemma refComb_conj (c' : ℝ) (f : ℕ) (η₀ : ℝ) (b : ℂ) :
    starRingEnd ℂ (refComb c' f η₀ b) = refComb c' f η₀ (starRingEnd ℂ b) := by
  have hge : Topology.IsClosedEmbedding (starRingEnd ℂ) := Complex.conjLIE.toHomeomorph.isClosedEmbedding
  unfold refComb
  rw [map_mul, Topology.IsClosedEmbedding.map_tprod _ hge, ← blaschkeT_conj,
    Complex.conj_ofReal]
  congr 1
  refine tprod_congr fun m => ?_
  rw [map_mul, ← blaschkeT_conj, ← blaschkeT_conj]
  simp only [map_add, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [mul_comm]
  congr 2 <;> ring_nf

/-- **(i) and (iii) of Lemma `K7` for the reference comb `B^{(f)}`** (eventually in `c'`). -/
theorem refComb_innerCombHyp {f : ℕ} (hf : 1 ≤ f) {η₀ : ℝ} (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1 / 4) :
    ∀ᶠ c' in atTop, InnerCombHyp c' (refComb c' f η₀) := by
  filter_upwards [refComb_K1a f hf h0 h1, band_upper_K6a_bdd hf h0 h1] with c' hK1 hK6
  obtain ⟨hb, he, -, hd⟩ := hK1
  obtain ⟨M, -, hM⟩ := hK6
  refine ⟨fun r => ?_, fun r => ?_, hd, fun b hb' => hb hb', fun v => ?_, ⟨M, fun x hx => ?_⟩⟩
  · simpa using refComb_neg c' f η₀ (r : ℂ)
  · have := refComb_conj c' f η₀ (r : ℂ)
    rw [Complex.conj_ofReal] at this
    exact Complex.conj_eq_iff_im.mp this
  · exact he (by simp)
  · have := hM x hx
    unfold slitL at this
    rw [abs_of_nonneg hx] at this
    exact this

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.refComb_innerCombHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refComb_innerCombHyp

end FormalResearch.ModularBootstrap.Upper.Membership
