module

public import Mathlib

/-!
# Listing the zeros of an entire function with multiplicity (Hadamard factorization, interface)

`Hadamard.Listing f a` says that the family `a : ι → ℂ` lists the **nonzero** zeros of `f` with multiplicity:
no entry is `0`, every fibre `a ⁻¹' {w}` is finite and, for `w ≠ 0`, has exactly `analyticOrderNatAt f w` elements.
Any enumeration (a function `ℕ → ℂ`, a finite family, the canonical `Hadamard.ZeroIdx f`, ...) can be used.

Main results, for `f` entire with `f 0 ≠ 0` (**proved**):
* `Hadamard.exists_listing`: a listing exists (`ι = Hadamard.ZeroIdx f`);
* `Hadamard.Listing.f_a`: `f (a i) = 0`; `Hadamard.Listing.finite_idx`: finitely many `i` with `‖a i‖ ≤ R`;
* `Hadamard.Listing.prod_idx` / `sum_idx`: for `S ⊆ ℂ` with `{i | a i ∈ S}` finite,
  `∏_{i : a i ∈ S} F (a i) = ∏ᶠ u, F u ^ ord_S(u)` (and the additive version), in particular
  `Hadamard.Listing.card_idx_eq_finsum_divisor`: the number of `i` with `a i ∈ S` is `Σᶠ divisor f S`, the quantity in
  Mathlib's Jensen formula.
-/

@[expose] public section

open Complex Filter Topology Finset Metric
open scoped BigOperators Classical

namespace FormalResearch.Hadamard

variable {ι : Type*}

/-- `a : ι → ℂ` lists the nonzero zeros of `f` with multiplicity. -/
structure Listing (f : ℂ → ℂ) (a : ι → ℂ) : Prop where
  ne_zero : ∀ i, a i ≠ 0
  finite_fibre : ∀ w, (a ⁻¹' {w}).Finite
  ncard_fibre : ∀ w, w ≠ 0 → (a ⁻¹' {w}).ncard = analyticOrderNatAt f w

/-- The canonical index type: pairs `(w, k)` with `w ≠ 0` and `k < ord_w f`. -/
abbrev ZeroIdx (f : ℂ → ℂ) : Type := {q : ℂ × ℕ // q.1 ≠ 0 ∧ q.2 < analyticOrderNatAt f q.1}

/-- The canonical listing `(w, k) ↦ w`. -/
def ZeroIdx.a (f : ℂ → ℂ) (q : ZeroIdx f) : ℂ := q.1.1

section entire

variable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
include hf h0

lemma order_ne_top (w : ℂ) : analyticOrderAt f w ≠ ⊤ := by
  have han : AnalyticOnNhd ℂ f Set.univ := fun w _ => hf.analyticAt w
  refine han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ 0)
    (Set.mem_univ w) ?_
  rw [Ne, analyticOrderAt_eq_top]
  intro hev
  exact h0 hev.self_of_nhds

lemma ordNat_pos_iff (w : ℂ) : 0 < analyticOrderNatAt f w ↔ f w = 0 := by
  have hne := order_ne_top hf h0 w
  have han : AnalyticAt ℂ f w := hf.analyticAt w
  have h0' : analyticOrderAt f w = 0 ↔ f w ≠ 0 := by
    rw [analyticOrderAt_eq_zero]; simp [han]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  have hnat : analyticOrderNatAt f w = n := by
    rw [analyticOrderNatAt, ← hn]; simp
  rw [hnat]
  constructor
  · intro hp
    by_contra hw
    have := h0'.mpr hw
    rw [← hn] at this
    simp at this; omega
  · intro hw
    by_contra hn0
    have : n = 0 := by omega
    have : analyticOrderAt f w = 0 := by rw [← hn, this]; simp
    exact (h0'.mp this) hw

lemma divisor_apply_entire (S : Set ℂ) (u : ℂ) :
    MeromorphicOn.divisor f S u = if u ∈ S then (analyticOrderNatAt f u : ℤ) else 0 := by
  have han : AnalyticOnNhd ℂ f S := fun w _ => hf.analyticAt w
  split_ifs with hu
  · rw [MeromorphicOn.AnalyticOnNhd.divisor_apply han hu]
    have hne := order_ne_top hf h0 u
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hn]
    have : analyticOrderNatAt f u = n := by rw [analyticOrderNatAt, ← hn]; simp
    rw [this]; simp
  · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu

lemma zeros_finite (R : ℝ) : {w : ℂ | ‖w‖ ≤ R ∧ f w = 0}.Finite := by
  have hfin := (MeromorphicOn.divisor f (closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)
  refine hfin.subset ?_
  rintro w ⟨hw, hz⟩
  have hw' : w ∈ closedBall (0 : ℂ) R := by simpa using hw
  rw [Function.mem_support, divisor_apply_entire hf h0]
  simp only [hw', ↓reduceIte]
  have := (ordNat_pos_iff hf h0 w).mpr hz
  exact_mod_cast this.ne'

variable {a : ι → ℂ} (L : Listing f a)
include L

lemma Listing.f_a (i : ι) : f (a i) = 0 := by
  have hpos : 0 < (a ⁻¹' {a i}).ncard :=
    (Set.ncard_pos (L.finite_fibre _)).mpr ⟨i, rfl⟩
  rw [L.ncard_fibre _ (L.ne_zero i)] at hpos
  exact (ordNat_pos_iff hf h0 _).mp hpos

lemma Listing.finite_idx (R : ℝ) : {i | ‖a i‖ ≤ R}.Finite := by
  have : {i | ‖a i‖ ≤ R} ⊆ ⋃ w ∈ {w : ℂ | ‖w‖ ≤ R ∧ f w = 0}, a ⁻¹' {w} := by
    intro i hi
    simp only [Set.mem_iUnion]
    exact ⟨a i, ⟨hi, L.f_a hf h0 i⟩, rfl⟩
  exact ((zeros_finite hf h0 R).biUnion fun w _ => L.finite_fibre w).subset this

/-- Grouping a product over the listing by values. -/
@[to_additive]
lemma Listing.prod_idx {M : Type*} [CommMonoid M] (S : Set ℂ) (hT : {i | a i ∈ S}.Finite)
    (F : ℂ → M) :
    ∏ i ∈ hT.toFinset, F (a i)
      = ∏ᶠ u, F u ^ (if u ∈ S then analyticOrderNatAt f u else 0) := by
  classical
  rw [Finset.prod_comp F a]
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hT.toFinset.image a)]
  · refine Finset.prod_congr rfl fun u hu => ?_
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    have hiS : a i ∈ S := hT.mem_toFinset.mp hi
    simp only [hiS, ↓reduceIte]
    congr 1
    rw [← L.ncard_fibre _ (L.ne_zero i)]
    rw [Set.ncard_eq_toFinset_card _ (L.finite_fibre _)]
    congr 1
    ext j
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_singleton_iff]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨by rw [h]; exact hiS, h⟩
  · intro u hu
    by_contra hnot
    rw [Function.mem_mulSupport] at hu
    apply hu
    by_cases huS : u ∈ S
    · by_cases hord : analyticOrderNatAt f u = 0
      · simp [huS, hord]
      · exfalso
        apply hnot
        have hz : f u = 0 := (ordNat_pos_iff hf h0 u).mp (Nat.pos_of_ne_zero hord)
        have hu0 : u ≠ 0 := by rintro rfl; exact h0 hz
        have hpos : 0 < (a ⁻¹' {u}).ncard := by
          rw [L.ncard_fibre u hu0]; exact Nat.pos_of_ne_zero hord
        obtain ⟨j, hj⟩ := (Set.ncard_pos (L.finite_fibre u)).mp hpos
        have hjT : j ∈ hT.toFinset := by
          simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
          have : a j = u := hj
          rw [this]; exact huS
        exact Finset.mem_image.mpr ⟨j, hjT, hj⟩
    · simp [huS]

/-- The number of `i` with `a i ∈ S` is `Σᶠ divisor f S`, the quantity bounded by Jensen's inequality. -/
lemma Listing.ncard_idx_eq_finsum_divisor (S : Set ℂ) (hT : {i | a i ∈ S}.Finite) :
    (Set.ncard {i | a i ∈ S} : ℤ) = ∑ᶠ u, MeromorphicOn.divisor f S u := by
  rw [Set.ncard_eq_toFinset_card _ hT]
  have h := Listing.sum_idx (M := ℤ) hf h0 L S hT (fun _ => (1 : ℤ))
  have hc : (hT.toFinset.card : ℤ) = ∑ i ∈ hT.toFinset, (1 : ℤ) := by simp
  rw [hc, h]
  refine finsum_congr fun u => ?_
  rw [divisor_apply_entire hf h0]
  by_cases hu : u ∈ S <;> simp [hu]

end entire

lemma exists_listing (f : ℂ → ℂ) :
    Listing f (ZeroIdx.a f) := by
  refine ⟨fun q => q.2.1, fun w => ?_, fun w hw => ?_⟩
  · by_cases hw0 : w = 0
    · have : ZeroIdx.a f ⁻¹' {w} = ∅ := by
        ext q; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false]
        intro h; exact q.2.1 (h.trans hw0)
      rw [this]; exact Set.finite_empty
    · have : ZeroIdx.a f ⁻¹' {w} = Set.range (fun k : Fin (analyticOrderNatAt f w) =>
          (⟨(w, (k : ℕ)), hw0, k.2⟩ : ZeroIdx f)) := by
        ext q
        constructor
        · intro h
          have hq : q.1.1 = w := h
          refine ⟨⟨q.1.2, ?_⟩, ?_⟩
          · have := q.2.2; rw [hq] at this; exact this
          · apply Subtype.ext; exact Prod.ext hq.symm rfl
        · rintro ⟨k, rfl⟩; rfl
      rw [this]; exact Set.finite_range _
  · have : ZeroIdx.a f ⁻¹' {w} = Set.range (fun k : Fin (analyticOrderNatAt f w) =>
        (⟨(w, (k : ℕ)), hw, k.2⟩ : ZeroIdx f)) := by
      ext q
      constructor
      · intro h
        have hq : q.1.1 = w := h
        refine ⟨⟨q.1.2, ?_⟩, ?_⟩
        · have := q.2.2; rw [hq] at this; exact this
        · apply Subtype.ext; exact Prod.ext hq.symm rfl
      · rintro ⟨k, rfl⟩; rfl
    rw [this, Set.ncard_range_of_injective]
    · simp
    · intro k l hkl
      have := congrArg (fun q : ZeroIdx f => q.1.2) hkl
      exact Fin.ext this

end FormalResearch.Hadamard

/-- info: 'FormalResearch.Hadamard.exists_listing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.exists_listing

/-- info: 'FormalResearch.Hadamard.Listing.ncard_idx_eq_finsum_divisor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.Listing.ncard_idx_eq_finsum_divisor

/-- info: 'FormalResearch.Hadamard.Listing.prod_idx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.Listing.prod_idx
