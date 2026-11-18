module

public import Mathlib

/-!
# Paper J, Layer 2 (L2.G4 (d)): uniformity in the parameter for the fold

Auxiliary compactness lemmas for `GeomSoft`.  Let `K` be compact, `f : Par -> R -> R` jointly continuous on `K x [0, L]` and
`uc : Par -> R` the *unique* maximiser of `f mu` on `[0, L]` for `mu in K`.  Then (the parameter space is only a topological space,
so every statement is by compactness of `K x [0, L]` and closed-graph / tube arguments, not sequences or uniform continuity):

* `uc_continuousOn`: `uc` is continuous on `K` (the graph of the argmax is closed);
* `uc_margin`: `uc` stays a fixed distance from `0` and `L` (this uses `uc mu in (0, L)`);
* `gap_unif`: for each `eps > 0` there is `gamma > 0` with `f mu u + gamma <= f mu (uc mu)` whenever `|u - uc mu| >= eps`;
* `tube_pos`: if `Phi` is continuous on `K x [a, b]` and `c < Phi mu (uc mu)`, then `c < Phi mu u` for `|u - uc mu| < rho`, uniformly.

Differences from the paper: the paper says "by compactness and continuity" (finding F-loc); these are the statements used.
Not formalised: nothing.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA.SoftUnif

open Set Filter Topology

variable {Par : Type*} [TopologicalSpace Par]

/-- A closed condition on a compact set cuts out a compact set (the ambient space need not be Hausdorff). -/
lemma isCompact_preimage {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {s : Set α} (hs : IsCompact s)
    {ψ : α → β} (hψ : ContinuousOn ψ s) {t : Set β} (ht : IsClosed t) : IsCompact (ψ ⁻¹' t ∩ s) := by
  obtain ⟨u, hu, hEq⟩ := continuousOn_iff_isClosed.1 hψ t ht
  rw [hEq]
  exact hs.inter_left hu

/-- The argmax `uc` is continuous on `K`. -/
lemma uc_continuousOn {L : ℝ} {K : Set Par} {f : Par → ℝ → ℝ} {uc : Par → ℝ}
    (hcont : ContinuousOn (fun p : Par × ℝ => f p.1 p.2) (K ×ˢ Icc 0 L))
    (hmem : ∀ μ ∈ K, uc μ ∈ Icc 0 L) (hmax : ∀ μ ∈ K, ∀ u ∈ Icc 0 L, f μ u ≤ f μ (uc μ))
    (huniq : ∀ μ ∈ K, ∀ u ∈ Icc 0 L, f μ (uc μ) ≤ f μ u → u = uc μ) : ContinuousOn uc K := by
  intro μ0 hμ0
  show Tendsto uc (𝓝[K] μ0) (𝓝 (uc μ0))
  refine isCompact_Icc.tendsto_nhds_of_unique_mapClusterPt (s := Icc 0 L) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with μ hμ using hmem μ hμ
  intro x hx hclu
  by_contra hne
  have hlt : f μ0 x < f μ0 (uc μ0) := by
    by_contra hnlt
    exact hne (huniq μ0 hμ0 x hx (not_lt.1 hnlt))
  set v := uc μ0 with hv
  have hvI : v ∈ Icc 0 L := hmem μ0 hμ0
  have hmaps : Set.MapsTo (fun p : Par × ℝ => (p.1, v)) (K ×ˢ Icc 0 L) (K ×ˢ Icc 0 L) :=
    fun p hp => ⟨hp.1, hvI⟩
  have hΔ : ContinuousOn (fun p : Par × ℝ => f p.1 v - f p.1 p.2) (K ×ˢ Icc 0 L) :=
    (hcont.comp (Continuous.prodMk continuous_fst continuous_const).continuousOn hmaps).sub hcont
  have hpos : (0 : ℝ) < f μ0 v - f μ0 x := by linarith
  have hev : ∀ᶠ p in 𝓝[K ×ˢ Icc 0 L] (μ0, x), 0 < f p.1 v - f p.1 p.2 :=
    Filter.Tendsto.eventually_const_lt (by linarith) (hΔ.continuousWithinAt ⟨hμ0, hx⟩)
  rw [nhdsWithin_prod_eq] at hev
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := Filter.eventually_prod_iff.1 hev
  have hpb' : ∀ᶠ y in 𝓝 x, y ∈ Icc 0 L → pb y := eventually_nhdsWithin_iff.1 hpb
  have hfreq := (mapClusterPt_iff_frequently.1 hclu) _ hpb'
  have hKev : ∀ᶠ μ in 𝓝[K] μ0, pa μ ∧ μ ∈ K := hpa.and self_mem_nhdsWithin
  obtain ⟨μ, hμ, hμa, hμK⟩ := (hfreq.and_eventually hKev).exists
  have := hab hμa (hμ (hmem μ hμK))
  have := hmax μ hμK v hvI
  linarith

/-- `uc` stays away from the ends. -/
lemma uc_margin {L : ℝ} {K : Set Par} {uc : Par → ℝ} (hK : IsCompact K) (huc : ContinuousOn uc K)
    (hint : ∀ μ ∈ K, uc μ ∈ Ioo 0 L) : ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ μ ∈ K, ρ0 ≤ uc μ ∧ uc μ ≤ L - ρ0 := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun μ hμ => by simp at hμ⟩
  have hc : ContinuousOn (fun μ => min (uc μ) (L - uc μ)) K := (continuous_min (α := ℝ)).comp_continuousOn (huc.prodMk (continuousOn_const.sub huc))
  obtain ⟨μ0, hμ0, hmin⟩ := hK.exists_isMinOn hne hc
  have h0 := hint μ0 hμ0
  refine ⟨min (uc μ0) (L - uc μ0), lt_min h0.1 (by linarith [h0.2]), fun μ hμ => ?_⟩
  have := isMinOn_iff.1 hmin μ hμ
  exact ⟨le_trans this (min_le_left _ _), by linarith [min_le_right (uc μ) (L - uc μ)]⟩

/-- Uniform gap away from the maximiser. -/
lemma gap_unif {L : ℝ} {K : Set Par} {f : Par → ℝ → ℝ} {uc : Par → ℝ} (hK : IsCompact K)
    (hcont : ContinuousOn (fun p : Par × ℝ => f p.1 p.2) (K ×ˢ Icc 0 L))
    (huc : ContinuousOn uc K) (hmem : ∀ μ ∈ K, uc μ ∈ Icc 0 L)
    (huniq : ∀ μ ∈ K, ∀ u ∈ Icc 0 L, f μ (uc μ) ≤ f μ u → u = uc μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ μ ∈ K, ∀ u ∈ Icc 0 L, ε ≤ |u - uc μ| → f μ u + γ ≤ f μ (uc μ) := by
  set s : Set (Par × ℝ) := K ×ˢ Icc 0 L with hs
  have hsc : IsCompact s := hK.prod isCompact_Icc
  have hmaps : Set.MapsTo (fun p : Par × ℝ => p.1) s K := fun p hp => hp.1
  have hψ : ContinuousOn (fun p : Par × ℝ => |p.2 - uc p.1|) s :=
    (continuous_snd.continuousOn.sub (huc.comp continuous_fst.continuousOn hmaps)).abs
  have hZ := isCompact_preimage hsc hψ (isClosed_Ici (a := ε))
  set Z := (fun p : Par × ℝ => |p.2 - uc p.1|) ⁻¹' Ici ε ∩ s with hZdef
  rcases Z.eq_empty_or_nonempty with hZe | hZne
  · refine ⟨1, one_pos, fun μ hμ u hu hεu => ?_⟩
    have : (μ, u) ∈ Z := ⟨hεu, hμ, hu⟩
    rw [hZe] at this
    exact absurd this (notMem_empty _)
  have hmapsU : Set.MapsTo (fun p : Par × ℝ => (p.1, uc p.1)) s s := fun p hp => ⟨hp.1, hmem p.1 hp.1⟩
  have hgraph : ContinuousOn (fun p : Par × ℝ => (p.1, uc p.1)) s :=
    continuous_fst.continuousOn.prodMk (huc.comp continuous_fst.continuousOn hmaps)
  have hD : ContinuousOn (fun p : Par × ℝ => f p.1 (uc p.1) - f p.1 p.2) s :=
    (hcont.comp hgraph hmapsU).sub hcont
  obtain ⟨p0, hp0, hmin⟩ := hZ.exists_isMinOn hZne (hD.mono inter_subset_right)
  have hDpos : ∀ p ∈ Z, 0 < f p.1 (uc p.1) - f p.1 p.2 := by
    intro p hp
    by_contra hle
    have h1 : f p.1 (uc p.1) ≤ f p.1 p.2 := by linarith [not_lt.1 hle]
    have := huniq p.1 hp.2.1 p.2 hp.2.2 h1
    have h2 : ε ≤ |p.2 - uc p.1| := hp.1
    rw [this, sub_self, abs_zero] at h2
    linarith
  refine ⟨f p0.1 (uc p0.1) - f p0.1 p0.2, hDpos p0 hp0, fun μ hμ u hu hεu => ?_⟩
  have hmem' : (μ, u) ∈ Z := ⟨hεu, hμ, hu⟩
  have := isMinOn_iff.1 hmin _ hmem'
  linarith

/-- Tube lemma along the graph of `uc`. -/
lemma tube_pos {a b : ℝ} {K : Set Par} {uc : Par → ℝ} {Φ : Par × ℝ → ℝ} (hK : IsCompact K)
    (huc : ContinuousOn uc K) (hΦ : ContinuousOn Φ (K ×ˢ Icc a b)) {c : ℝ}
    (hg : ∀ μ ∈ K, uc μ ∈ Icc a b ∧ c < Φ (μ, uc μ)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ μ ∈ K, ∀ u ∈ Icc a b, |u - uc μ| < ρ → c < Φ (μ, u) := by
  set s : Set (Par × ℝ) := K ×ˢ Icc a b with hs
  have hsc : IsCompact s := hK.prod isCompact_Icc
  have hmaps : Set.MapsTo (fun p : Par × ℝ => p.1) s K := fun p hp => hp.1
  have hψ : ContinuousOn (fun p : Par × ℝ => |p.2 - uc p.1|) s :=
    (continuous_snd.continuousOn.sub (huc.comp continuous_fst.continuousOn hmaps)).abs
  have hC := isCompact_preimage hsc hΦ (isClosed_Iic (a := c))
  set C := Φ ⁻¹' Iic c ∩ s with hCdef
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · refine ⟨1, one_pos, fun μ hμ u hu _ => ?_⟩
    by_contra hle
    have : (μ, u) ∈ C := ⟨not_lt.1 hle, hμ, hu⟩
    rw [hCe] at this
    exact absurd this (notMem_empty _)
  obtain ⟨p0, hp0, hmin⟩ := hC.exists_isMinOn hCne (hψ.mono inter_subset_right)
  have hρpos : 0 < |p0.2 - uc p0.1| := by
    rcases (abs_nonneg (p0.2 - uc p0.1)).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : p0.2 = uc p0.1 := by
        have := abs_eq_zero.1 h.symm
        linarith
      have h1 : Φ p0 ≤ c := hp0.1
      have h2 := (hg p0.1 hp0.2.1).2
      have : p0 = (p0.1, uc p0.1) := Prod.ext rfl h0
      rw [this] at h1
      linarith
  refine ⟨|p0.2 - uc p0.1|, hρpos, fun μ hμ u hu hlt => ?_⟩
  by_contra hle
  have hmem' : (μ, u) ∈ C := ⟨not_lt.1 hle, hμ, hu⟩
  have := isMinOn_iff.1 hmin _ hmem'
  linarith

end FormalResearch.JacobiEigenvectors.TheoremA.SoftUnif
