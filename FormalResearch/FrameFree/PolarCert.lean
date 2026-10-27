import FormalResearch.FrameFree.WeylUpper

open scoped ComplexConjugate Matrix
open FormalResearch.FourQubitEntropy FormalResearch.FrameFree.WeylUpper

/-!
# `PolarExtremeHyp`: what is actually needed, and the exact remaining statement

`WeylUpper.lean` proves the Weyl-vertex upper bound (R7) from `PolarExtremeHyp`, the polar form of the
facet classification of `conv W(D₄) ⊂ M₄(ℝ)`.  This file isolates the *primal* form of what is missing and
shows that it is strictly what the paper uses (`QI-A`, `thm:D4hadamard`):

* `hadM A B = A ∘ B` (entrywise product);
* `QSet = {M | ∀ e ∈ ExtN, ⟨e, M⟩ ≤ 1}` (the polytope cut out by the candidate facets);
* `FacetComplete : QSet ⊆ conv W(D₄)` (the facets of `conv W(D₄)` are among `ExtN`);
* `D4Hull : ∀ realised A B, A ∘ B ∈ conv W(D₄)` (`thm:D4hadamard`, realised form).

Proved here, with no new hypotheses:
`hadM_mem_Q` (realised `A ∘ B` lies in `QSet`, from the facet inequalities of `WeylUpper`),
`facetComplete_to_hull : FacetComplete → D4Hull`,
`hull_to_re : D4Hull → HadamardWeylBoundRe` (a convex combination and the triangle inequality, no polar
duality at all), `polar_to_facetComplete : PolarExtremeHyp → FacetComplete` (Hahn–Banach), and the final
theorems of `WeylUpper` from `FacetComplete` (or from `D4Hull`) alone.
-/

namespace FormalResearch.FrameFree.PolarCert

abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ

/-- The `192` vertices of `conv W(D₄)`, as matrices. -/
def Wset : Set M4 := (fun w => wmat w) '' (weylSet : Set SP)

/-- The entrywise (Hadamard) product. -/
def hadM (A B : M4) : M4 := Matrix.of fun i j => A i j * B i j

theorem pair_comm (N M : M4) : pair N M = pair M N := by
  unfold pair
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pair_hadM (N A B : M4) : pair N (hadM A B) = tri N A B := by
  unfold pair tri hadM
  simp only [Matrix.of_apply]

/-- The polytope cut out by the candidate facet normals. -/
def QSet : Set M4 := {M | ∀ e ∈ ExtN, pair e M ≤ 1}

theorem hadM_mem_Q {A B : M4} (hA : Real4 A) (hB : Real4 B) : hadM A B ∈ QSet := by
  intro e he
  rw [pair_hadM]
  exact tri_le_one_of_ext he hA hB

/-- **Facet completeness** of `ExtN` (primal form of `PolarExtremeHyp`): every matrix satisfying all
candidate facet inequalities lies in `conv W(D₄)`. -/
def FacetComplete : Prop := QSet ⊆ convexHull ℝ Wset

/-- **`thm:D4hadamard`, realised form**: `A ∘ B ∈ conv W(D₄)` for local-rotation matrices. -/
def D4Hull : Prop := ∀ A B : M4, Real4 A → Real4 B → hadM A B ∈ convexHull ℝ Wset

theorem facetComplete_to_hull (h : FacetComplete) : D4Hull :=
  fun _ _ hA hB => h (hadM_mem_Q hA hB)

/-- The complex bilinear form `M ↦ ∑ xᵢ Mᵢⱼ yⱼ` as a real-linear map. -/
def bil (x y : Fin 4 → ℂ) : M4 →ₗ[ℝ] ℂ where
  toFun M := ∑ i, ∑ j, x i * (M i j : ℂ) * y j
  map_add' M N := by
    simp only [Matrix.add_apply, Complex.ofReal_add, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c M := by
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply, Complex.real_smul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

theorem bil_hadM (x y : Fin 4 → ℂ) (A B : M4) : bil x y (hadM A B) = hadPair x y A B := by
  simp only [bil, hadM, hadPair, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
  push_cast
  rfl

theorem bil_wmat (x y : Fin 4 → ℂ) (w : SP) : bil x y (wmat w) = weylPair x y w := by
  simp only [bil, LinearMap.coe_mk, AddHom.coe_mk, weylPair]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (w.1 i)]
  · simp [wmat]
  · intro j _ hj
    simp [wmat, Ne.symm hj]
  · simp

/-- **`D4Hull` implies the Hadamard bound** (convex combination plus triangle inequality). -/
theorem hull_to_re (h : D4Hull) : HadamardWeylBoundRe := by
  intro x y A B hA hB
  obtain ⟨w0, hw0, hmax⟩ := Finset.exists_max_image weylSet (fun w => ‖weylPair x y w‖)
    ⟨_, one_mem_weylSet⟩
  refine ⟨w0, hw0, ?_⟩
  set m := ‖weylPair x y w0‖ with hm
  have hconv : Convex ℝ ((bil x y) ⁻¹' (Metric.closedBall (0 : ℂ) m)) :=
    (convex_closedBall (0 : ℂ) m).linear_preimage (bil x y)
  have hsub : Wset ⊆ (bil x y) ⁻¹' (Metric.closedBall (0 : ℂ) m) := by
    rintro _ ⟨w, hw, rfl⟩
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, bil_wmat]
    exact hmax w hw
  have := convexHull_min hsub hconv (h A B hA hB)
  simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, bil_hadM] at this
  exact this

theorem hadamard_of_facetComplete (h : FacetComplete) : HadamardWeylBoundRe :=
  hull_to_re (facetComplete_to_hull h)

/-- **`thm:weyl`, upper bound, from facet completeness only.** -/
theorem rotOverlap_conj_le_FKmag_of_facetComplete (h : FacetComplete) (d : Fin 4 → ℂ) :
    rotOverlap (psiMag d) (Psi.conj (psiMag d)) ≤ FKmag d :=
  rotOverlap_conj_le_FKmag (hadamard_of_facetComplete h) d

/-- **`thm:weyl`, one-vector form, from `D4Hull` (= `thm:D4hadamard`) only.** -/
theorem rotOverlap_conj_eq_FKmag_of_hull (h : D4Hull) (d : Fin 4 → ℂ) :
    rotOverlap (psiMag d) (Psi.conj (psiMag d)) = FKmag d :=
  rotOverlap_conj_eq_FKmag (hull_to_re h) d


/-! ### Duality: `PolarExtremeHyp` implies `FacetComplete` -/

instance : LocallyConvexSpace ℝ M4 :=
  inferInstanceAs (LocallyConvexSpace ℝ (Fin 4 → Fin 4 → ℝ))

theorem single_smul (i j : Fin 4) (M : M4) : Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : ℝ) := by
  ext a b
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [Matrix.single_apply, Matrix.smul_apply, Matrix.single_apply]
    by_cases h1 : i = a <;> by_cases h2 : j = b <;> simp_all [eq_comm]

theorem strongDual_eq_pair (f : StrongDual ℝ M4) (M : M4) :
    f M = pair (Matrix.of fun i j => f (Matrix.single i j (1 : ℝ))) M := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  simp only [map_sum, single_smul, map_smul, smul_eq_mul, pair, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_pair_separation {s : Set M4} (hs : Convex ℝ s) (hc : IsClosed s) {x : M4} (hx : x ∉ s) :
    ∃ N : M4, ∃ u : ℝ, (∀ a ∈ s, pair N a < u) ∧ u < pair N x := by
  obtain ⟨f, u, h1, h2⟩ := geometric_hahn_banach_closed_point hs hc hx
  refine ⟨Matrix.of fun i j => f (Matrix.single i j (1 : ℝ)), u, fun a ha => ?_, ?_⟩
  · rw [← strongDual_eq_pair]; exact h1 a ha
  · rw [← strongDual_eq_pair]; exact h2


theorem pair_comb (a b : ℝ) (N1 N2 M : M4) :
    pair (a • N1 + b • N2) M = a * pair N1 M + b * pair N2 M := by
  unfold pair
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem Wset_finite : Wset.Finite := (Finset.finite_toSet weylSet).image _

theorem isClosed_hull : IsClosed (convexHull ℝ Wset) := Wset_finite.isClosed_convexHull ℝ

theorem negI_mem : ((1 : Equiv.Perm (Fin 4)), fun _ : Fin 4 => true) ∈ weylSet := by decide +kernel

theorem pair_wmat_one (N : M4) : pair N (wmat (1, fun _ => false)) = ∑ i, N i i := by
  unfold pair wmat
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [sg]
  · intro j _ hj; simp [Ne.symm hj]
  · simp

theorem pair_wmat_neg (N : M4) : pair N (wmat (1, fun _ => true)) = - ∑ i, N i i := by
  unfold pair wmat
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [sg]
  · intro j _ hj; simp [Ne.symm hj]
  · simp

/-- **The polar form implies the primal form**: `PolarExtremeHyp → FacetComplete` (Hahn–Banach). -/
theorem polar_to_facetComplete (hyp : PolarExtremeHyp) : FacetComplete := by
  intro M hM
  by_contra hnot
  obtain ⟨N, u, h1, h2⟩ := exists_pair_separation (convex_convexHull ℝ Wset) isClosed_hull hnot
  have hmem : ∀ w ∈ weylSet, pair N (wmat w) < u := fun w hw =>
    h1 _ (subset_convexHull ℝ Wset ⟨w, hw, rfl⟩)
  have hu : 0 < u := by
    have a := hmem _ one_mem_weylSet
    have b := hmem _ negI_mem
    rw [pair_wmat_one] at a
    rw [pair_wmat_neg] at b
    linarith
  have hpol : ∀ w ∈ weylSet, pair (u⁻¹ • N) (wmat w) ≤ 1 := by
    intro w hw
    rw [pair_smul, inv_mul_le_iff₀ hu]
    linarith [hmem w hw]
  have hN := hyp _ hpol
  have hconv : Convex ℝ {X : M4 | pair X M ≤ 1} := by
    intro X1 hX1 X2 hX2 a b ha hb hab
    change pair X1 M ≤ 1 at hX1
    change pair X2 M ≤ 1 at hX2
    show pair (a • X1 + b • X2) M ≤ 1
    rw [pair_comb]
    nlinarith
  have hle := convexHull_min (fun e he => by
    show pair e M ≤ 1
    exact hM e he) hconv hN
  change pair (u⁻¹ • N) M ≤ 1 at hle
  rw [pair_smul, inv_mul_le_iff₀ hu] at hle
  have hc := pair_comm N M
  linarith

theorem rotOverlap_conj_le_FKmag_of_polar' (hyp : PolarExtremeHyp) (d : Fin 4 → ℂ) :
    rotOverlap (psiMag d) (Psi.conj (psiMag d)) ≤ FKmag d :=
  rotOverlap_conj_le_FKmag_of_facetComplete (polar_to_facetComplete hyp) d


/-! ### The converse: `FacetComplete → PolarExtremeHyp` (so the two forms are equivalent) -/

/-- The `±1` vector attached to a Boolean vector. -/
def sgnVec (b : Fin 4 → Bool) : Fin 4 → ℝ := fun i => if b i then -1 else 1

theorem exists_sgnVec_of_isSign {t : Fin 4 → ℝ} (h : IsSign t) : ∃ b, t = sgnVec b := by
  refine ⟨fun i => decide (t i = -1), ?_⟩
  funext i
  rcases h i with h1 | h1
  · simp [sgnVec, h1]
  · simp [sgnVec, h1]

theorem isSign_sgnVec (b : Fin 4 → Bool) : IsSign (sgnVec b) := by
  intro i; unfold sgnVec; split_ifs <;> simp

theorem ExtN_finite : ExtN.Finite := by
  let f : ((Fin 4 × (Fin 4 → Bool)) ⊕ (Fin 4 × (Fin 4 → Bool))) ⊕
      (((Fin 4 → Bool) × (Fin 4 → Bool)) ⊕ (SP × SP)) → M4 := fun x =>
    match x with
    | Sum.inl (Sum.inl (i, b)) => rowN i (sgnVec b)
    | Sum.inl (Sum.inr (j, b)) => colN j (sgnVec b)
    | Sum.inr (Sum.inl (b, b')) => parN (sgnVec b) (sgnVec b')
    | Sum.inr (Sum.inr (g, h)) => wmat g * Fmat * wmat h
  refine (Set.finite_range f).subset ?_
  rintro N (⟨i, t, ht, rfl⟩ | ⟨j, s, hs, rfl⟩ | ⟨s, t, hs, ht, hp, rfl⟩ | ⟨g, hg, h, hh, rfl⟩)
  · obtain ⟨b, rfl⟩ := exists_sgnVec_of_isSign ht; exact ⟨Sum.inl (Sum.inl (i, b)), rfl⟩
  · obtain ⟨b, rfl⟩ := exists_sgnVec_of_isSign hs; exact ⟨Sum.inl (Sum.inr (j, b)), rfl⟩
  · obtain ⟨b, rfl⟩ := exists_sgnVec_of_isSign hs
    obtain ⟨b', rfl⟩ := exists_sgnVec_of_isSign ht
    exact ⟨Sum.inr (Sum.inl (b, b')), rfl⟩
  · exact ⟨Sum.inr (Sum.inr (g, h)), rfl⟩

theorem isClosed_hullExt : IsClosed (convexHull ℝ ExtN) := ExtN_finite.isClosed_convexHull ℝ

theorem rowN_mem (i : Fin 4) (b : Fin 4 → Bool) : rowN i (sgnVec b) ∈ ExtN :=
  Or.inl ⟨i, _, isSign_sgnVec b, rfl⟩

theorem pair_rowN (M : M4) (i : Fin 4) (t : Fin 4 → ℝ) : pair (rowN i t) M = ∑ b, t b * M i b := by
  unfold pair rowN
  rw [Finset.sum_eq_single i]
  · simp
  · intro a _ ha; simp [ha]
  · simp

/-- **Equivalence**: `FacetComplete` implies the polar form. -/
theorem facetComplete_to_polar (h : FacetComplete) : PolarExtremeHyp := by
  intro N hN
  by_contra hnot
  obtain ⟨M, u, h1, h2⟩ := exists_pair_separation (convex_convexHull ℝ ExtN) isClosed_hullExt hnot
  have hmem : ∀ e ∈ ExtN, pair M e < u := fun e he => h1 _ (subset_convexHull ℝ ExtN he)
  have hu : 0 < u := by
    have a := hmem _ (rowN_mem 0 (fun _ => false))
    have b := hmem _ (rowN_mem 0 (fun _ => true))
    rw [pair_comm, pair_rowN] at a b
    simp only [sgnVec, Bool.false_eq_true, ↓reduceIte, Fin.sum_univ_four] at a b
    linarith
  have hQ : u⁻¹ • M ∈ QSet := by
    intro e he
    rw [pair_comm, pair_smul, inv_mul_le_iff₀ hu, mul_one]
    exact (hmem e he).le
  have hM := h hQ
  have hconv : Convex ℝ {X : M4 | pair N X ≤ 1} := by
    intro X1 hX1 X2 hX2 a b ha hb hab
    change pair N X1 ≤ 1 at hX1
    change pair N X2 ≤ 1 at hX2
    show pair N (a • X1 + b • X2) ≤ 1
    rw [pair_comm, pair_comb, pair_comm X1, pair_comm X2]
    nlinarith
  have hle := convexHull_min (fun w hw => by
    obtain ⟨w', hw', rfl⟩ := hw
    exact hN w' hw') hconv hM
  change pair N (u⁻¹ • M) ≤ 1 at hle
  rw [pair_comm, pair_smul, inv_mul_le_iff₀ hu] at hle
  linarith

theorem polar_iff_facetComplete : PolarExtremeHyp ↔ FacetComplete :=
  ⟨polar_to_facetComplete, facetComplete_to_polar⟩

end FormalResearch.FrameFree.PolarCert
