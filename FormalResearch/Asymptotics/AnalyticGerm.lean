module

public import FormalResearch.Asymptotics.UniformExpansion
public import FormalResearch.Asymptotics.TaylorUniform

/-!
# Uniform expansions from a smooth or analytic germ

The bridge between a jointly smooth function `G (z, t)` and `HasUniformExpansion`: if
`G : E × ℝ → F` is `C^∞` (in particular real analytic) on an open set `U ⊇ K ×ˢ {0}` with `K`
compact, `ε → 0` along `l`, and `f z i = G (z, ε i)` eventually along `l`, uniformly in `z ∈ K`,
then `f` has the uniform expansion `∑ r, ε i ^ r • taylorCoeff G r z` on `K`.

The identity `f z i = G (z, ε i)` may be required only at the points of a set `S ⊆ E × ι`
(for instance a lattice on which `z` is tied to the index), see
`hasUniformExpansionOn_of_contDiffOn`; the general statement is
`hasExpansionAlong_of_contDiffOn`, for an arbitrary filter `L ≤ 𝓟 K ×ˢ l`.

Since the coefficients are `taylorCoeff`s they are analytic in `z` when `G` is
(`analyticOnNhd_taylorCoeff`), and by `HasUniformExpansion.eq_of_tendsto` any uniform expansion of
`f` has these coefficients when `ε` is eventually nonzero.
-/

@[expose] public section

open Asymptotics Filter Topology
open scoped ContDiff

namespace FormalResearch.Asymptotics

variable {E ι F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Bridge, general filter.**  `G` is `C^∞` on an open `U ⊇ K ×ˢ {0}` (`K` compact), `ε → 0`
along `l`, and `f z i = G (z, ε i)` eventually along a filter `L ≤ 𝓟 K ×ˢ l`.  Then `f` has the
expansion with the Taylor coefficients of `G` in its last variable along `L`. -/
theorem hasExpansionAlong_of_contDiffOn {G : E × ℝ → F} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) {K : Set E} (hK : IsCompact K)
    (hKU : K ×ˢ ({0} : Set ℝ) ⊆ U) {f : E → ι → F} {ε : ι → ℝ} {l : Filter ι}
    (hε : Tendsto ε l (𝓝 0)) {L : Filter (E × ι)} (hL : L ≤ 𝓟 K ×ˢ l)
    (hf : ∀ᶠ p in L, f p.1 p.2 = G (p.1, ε p.2)) :
    HasExpansionAlong L f (taylorCoeff fun z t => G (z, t)) ε := by
  intro R
  obtain ⟨ρ, hρ, C, hC⟩ := taylor_uniform hU hG hK hKU R
  have h1 : ∀ᶠ p in L, p.1 ∈ K := tendsto_principal.1 (tendsto_fst.mono_left hL)
  have h2 : ∀ᶠ p in L, |ε p.2| ≤ ρ := by
    have : Tendsto (fun p : E × ι => ε p.2) L (𝓝 0) := hε.comp (tendsto_snd.mono_left hL)
    filter_upwards [this.eventually (Metric.closedBall_mem_nhds (0 : ℝ) hρ)] with p hp
    simpa using hp
  refine IsBigO.of_bound C ?_
  filter_upwards [hf, h1, h2] with p hp hp1 hp2
  rw [hp, norm_pow, Real.norm_eq_abs]
  exact hC p.1 hp1 (ε p.2) hp2

/-- **Bridge with the identity at the points of `S`.**  As `hasExpansionAlong_of_contDiffOn`,
for the expansion `HasUniformExpansionOn S`, where `f z i = G (z, ε i)` is only required for
`(z, i) ∈ S` with `z ∈ K`, and only eventually in `i`. -/
theorem hasUniformExpansionOn_of_contDiffOn {G : E × ℝ → F} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) {K : Set E} (hK : IsCompact K)
    (hKU : K ×ˢ ({0} : Set ℝ) ⊆ U) {f : E → ι → F} {ε : ι → ℝ} {l : Filter ι}
    (hε : Tendsto ε l (𝓝 0)) (S : Set (E × ι))
    (hf : ∀ᶠ i in l, ∀ z, (z, i) ∈ S → z ∈ K → f z i = G (z, ε i)) :
    HasUniformExpansionOn S f (taylorCoeff fun z t => G (z, t)) ε l K := by
  refine hasExpansionAlong_of_contDiffOn hU hG hK hKU hε inf_le_right ?_
  have hS : ∀ᶠ p in 𝓟 S ⊓ 𝓟 K ×ˢ l, p ∈ S :=
    tendsto_principal.1 (tendsto_id.mono_left inf_le_left)
  have hK' : ∀ᶠ p in 𝓟 S ⊓ 𝓟 K ×ˢ l, p.1 ∈ K :=
    tendsto_principal.1 (tendsto_fst.mono_left inf_le_right)
  have hl : ∀ᶠ p in 𝓟 S ⊓ 𝓟 K ×ˢ l, ∀ z, (z, p.2) ∈ S → z ∈ K → f z p.2 = G (z, ε p.2) :=
    (tendsto_snd.mono_left (inf_le_right : 𝓟 S ⊓ 𝓟 K ×ˢ l ≤ 𝓟 K ×ˢ l)).eventually hf
  filter_upwards [hS, hK', hl] with p hp hp1 hp2
  exact hp2 p.1 hp hp1

/-- **Bridge, `C^∞` germ, uniform on `K`.** -/
theorem hasUniformExpansion_of_contDiffOn {G : E × ℝ → F} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) {K : Set E} (hK : IsCompact K)
    (hKU : K ×ˢ ({0} : Set ℝ) ⊆ U) {f : E → ι → F} {ε : ι → ℝ} {l : Filter ι}
    (hε : Tendsto ε l (𝓝 0)) (hf : ∀ᶠ i in l, ∀ z ∈ K, f z i = G (z, ε i)) :
    HasUniformExpansion f (taylorCoeff fun z t => G (z, t)) ε l K :=
  hasExpansionAlong_of_contDiffOn hU hG hK hKU hε le_rfl (eventually_principal_prod_iff.2 hf)

/-- **Bridge, analytic germ, uniform on `K`**: `G` real analytic on an open `U ⊇ K ×ˢ {0}`. -/
theorem hasUniformExpansion_of_analytic {G : E × ℝ → F} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : AnalyticOnNhd ℝ G U) {K : Set E} (hK : IsCompact K)
    (hKU : K ×ˢ ({0} : Set ℝ) ⊆ U) {f : E → ι → F} {ε : ι → ℝ} {l : Filter ι}
    (hε : Tendsto ε l (𝓝 0)) (hf : ∀ᶠ i in l, ∀ z ∈ K, f z i = G (z, ε i)) :
    HasUniformExpansion f (taylorCoeff fun z t => G (z, t)) ε l K :=
  hasUniformExpansion_of_contDiffOn hU (hG.contDiffOn hU.uniqueDiffOn) hK hKU hε hf

/-- **Bridge, analytic germ, identity at the points of `S`.** -/
theorem hasUniformExpansionOn_of_analytic {G : E × ℝ → F} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : AnalyticOnNhd ℝ G U) {K : Set E} (hK : IsCompact K)
    (hKU : K ×ˢ ({0} : Set ℝ) ⊆ U) {f : E → ι → F} {ε : ι → ℝ} {l : Filter ι}
    (hε : Tendsto ε l (𝓝 0)) (S : Set (E × ι))
    (hf : ∀ᶠ i in l, ∀ z, (z, i) ∈ S → z ∈ K → f z i = G (z, ε i)) :
    HasUniformExpansionOn S f (taylorCoeff fun z t => G (z, t)) ε l K :=
  hasUniformExpansionOn_of_contDiffOn hU (hG.contDiffOn hU.uniqueDiffOn) hK hKU hε S hf

/-- **Bridge, globally smooth germ.** -/
theorem hasUniformExpansion_of_contDiff {G : E × ℝ → F} (hG : ContDiff ℝ ∞ G) {K : Set E}
    (hK : IsCompact K) {f : E → ι → F} {ε : ι → ℝ} {l : Filter ι} (hε : Tendsto ε l (𝓝 0))
    (hf : ∀ᶠ i in l, ∀ z ∈ K, f z i = G (z, ε i)) :
    HasUniformExpansion f (taylorCoeff fun z t => G (z, t)) ε l K :=
  hasUniformExpansion_of_contDiffOn isOpen_univ hG.contDiffOn hK (Set.subset_univ _) hε hf

/-- **Identification of the coefficients.**  Any uniform expansion of a function that equals a
smooth germ `G (z, ε i)` has the Taylor coefficients of `G` as coefficients, pointwise on `K`
(`ε → 0` and `ε ≠ 0` eventually along a nontrivial `l`). -/
theorem HasUniformExpansion.eq_taylorCoeff {G : E × ℝ → F} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) {K : Set E} (hK : IsCompact K)
    (hKU : K ×ˢ ({0} : Set ℝ) ⊆ U) {f : E → ι → F} {ε : ι → ℝ} {l : Filter ι} [l.NeBot]
    (hε : Tendsto ε l (𝓝 0)) (hε0 : ∀ᶠ i in l, ε i ≠ 0)
    (hf : ∀ᶠ i in l, ∀ z ∈ K, f z i = G (z, ε i)) {a : ℕ → E → F}
    (ha : HasUniformExpansion f a ε l K) {z : E} (hz : z ∈ K) (r : ℕ) :
    a r z = taylorCoeff (fun z t => G (z, t)) r z :=
  ha.eq_of_tendsto (hasUniformExpansion_of_contDiffOn hU hG hK hKU hε hf) hε hε0 hz r

/-- info: 'FormalResearch.Asymptotics.hasUniformExpansion_of_analytic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasUniformExpansion_of_analytic

/-- info: 'FormalResearch.Asymptotics.hasUniformExpansionOn_of_analytic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasUniformExpansionOn_of_analytic

/-- info: 'FormalResearch.Asymptotics.hasUniformExpansion_of_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasUniformExpansion_of_contDiff

/-- info: 'FormalResearch.Asymptotics.HasUniformExpansion.eq_taylorCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasUniformExpansion.eq_taylorCoeff

end FormalResearch.Asymptotics
