module

public import Mathlib

/-!
# Bordered-distance inertia

Weyl/P5 `prop:inertia`: for `m` points of a Euclidean space whose affine span has dimension `d`,
the bordered squared-distance matrix `[[0, 1ᵀ],[1, D]]` has inertia `(1, d+1, m-d-1)`.
The headline `p5a_bordered_distance_inertia` states this as an orthogonal decomposition of
`ℝ × ℝ^m` into a positive line, a negative definite subspace of dimension `d+1` and the radical
of dimension `m-d-1` (Mathlib has no signature API).  The proof follows the paper: the coordinates
`β = α + ∑ |Pᵢ|² zᵢ`, `s = ∑ zᵢ`, `y = ∑ zᵢ Pᵢ` turn the form into `2βs - 2|y|²`
(`p5a_borderedForm_coordinate_identity`), the radical is `β = s = y = 0`, whose dimension is
`m - (d+1)` by the rank of `z ↦ (s, y)`, and `u = (1, e₀)` (form value `2`) splits off the
positive line, its orthogonal complement being negative definite modulo the radical.
Not formalised: the explicit sign of the coefficient `c` in `adj(M) = c v vᵀ` at a planar wall
point (a consequence in the paper).
-/

@[expose] public section

namespace FormalResearch.EuclTet

/-- The quadratic form of the bordered squared-distance matrix, written without a matrix
representation. -/
noncomputable def p5a_borderedForm {m d : ℕ} (p : Fin m → EuclideanSpace ℝ (Fin d))
    (α : ℝ) (z : Fin m → ℝ) : ℝ :=
  2 * α * (∑ i, z i) + ∑ i, ∑ j, z i * z j * ‖p i - p j‖ ^ 2

/-- The symmetric bilinear form obtained by polarizing `p5a_borderedForm`. -/
noncomputable def p5a_borderedBilin {m d : ℕ}
    (p : Fin m → EuclideanSpace ℝ (Fin d))
    (x y : ℝ × (Fin m → ℝ)) : ℝ :=
  (p5a_borderedForm p (x.1 + y.1) (x.2 + y.2) -
    p5a_borderedForm p x.1 x.2 - p5a_borderedForm p y.1 y.2) / 2

/-- The coordinate identity used in the proof of Weyl/P5 `prop:inertia`.
This is the algebraic reduction only; no affine-rank or inertia conclusion is asserted. -/
theorem p5a_borderedForm_coordinate_identity {m d : ℕ}
    (p : Fin m → EuclideanSpace ℝ (Fin d)) (α : ℝ) (z : Fin m → ℝ) :
    p5a_borderedForm p α z =
      2 * (α + ∑ i, ‖p i‖ ^ 2 * z i) * (∑ i, z i) -
        2 * ‖∑ i, z i • p i‖ ^ 2 := by
  classical
  have hnorm : ‖∑ i, z i • p i‖ ^ 2 =
      ∑ i, ∑ j, z i * z j * inner ℝ (p i) (p j) := by
    calc
      ‖∑ i, z i • p i‖ ^ 2 = inner ℝ (∑ i, z i • p i) (∑ i, z i • p i) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = ∑ i, ∑ j, z i * z j * inner ℝ (p i) (p j) := by
        simp only [inner_sum, sum_inner, inner_smul_left, inner_smul_right]
        simp only [Finset.mul_sum]
        simp [real_inner_comm]
        ring_nf
  have hswap (f : Fin m → ℝ) :
      (∑ i, ∑ j, z i * z j * f i) = ∑ i, ∑ j, z i * z j * f j := by
    calc
      (∑ i, ∑ j, z i * z j * f i) = ∑ j, ∑ i, z i * z j * f i := by
        rw [Finset.sum_comm]
      _ = ∑ j, ∑ i, z j * z i * f i := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ i, ∑ j, z i * z j * f j := rfl
  have hcoef (f : Fin m → Fin m → ℝ) :
      (∑ i, ∑ j, f i j) * 2 = ∑ i, ∑ j, f i j * 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_mul]
  have hcoef' (f : Fin m → Fin m → ℝ) :
      2 * (∑ i, ∑ j, f i j) = ∑ i, ∑ j, 2 * f i j := by
    calc
      2 * (∑ i, ∑ j, f i j) = (∑ i, ∑ j, f i j) * 2 := by ring
      _ = ∑ i, ∑ j, f i j * 2 := hcoef f
      _ = ∑ i, ∑ j, 2 * f i j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
  unfold p5a_borderedForm
  simp_rw [norm_sub_sq_real]
  rw [hnorm]
  ring_nf
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hswap (fun i => ‖p i‖ ^ 2)]
  simp [mul_comm, mul_left_comm, mul_assoc]
  rw [hcoef' (fun i j => z i * (z j * inner ℝ (p i) (p j)))]
  ring_nf

/-! ### Coordinates and the polarized form -/

/-- The coordinate `β = α + ∑ |Pᵢ|² zᵢ`. -/
noncomputable def p5a_bcoord {m n : ℕ} (p : Fin m → EuclideanSpace ℝ (Fin n))
    (w : ℝ × (Fin m → ℝ)) : ℝ := w.1 + ∑ i, ‖p i‖ ^ 2 * w.2 i

/-- The coordinate `s = ∑ zᵢ`. -/
def p5a_s {m : ℕ} (w : ℝ × (Fin m → ℝ)) : ℝ := ∑ i, w.2 i

/-- The coordinate `y = ∑ zᵢ Pᵢ`. -/
noncomputable def p5a_y {m n : ℕ} (p : Fin m → EuclideanSpace ℝ (Fin n))
    (w : ℝ × (Fin m → ℝ)) : EuclideanSpace ℝ (Fin n) := ∑ i, w.2 i • p i

section coords
variable {m n : ℕ} (p : Fin m → EuclideanSpace ℝ (Fin n))

lemma p5a_bcoord_add (x x' : ℝ × (Fin m → ℝ)) :
    p5a_bcoord p (x + x') = p5a_bcoord p x + p5a_bcoord p x' := by
  simp only [p5a_bcoord, Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

lemma p5a_s_add (x x' : ℝ × (Fin m → ℝ)) : p5a_s (x + x') = p5a_s x + p5a_s x' := by
  simp [p5a_s, Finset.sum_add_distrib]

lemma p5a_y_add (x x' : ℝ × (Fin m → ℝ)) : p5a_y p (x + x') = p5a_y p x + p5a_y p x' := by
  simp [p5a_y, add_smul, Finset.sum_add_distrib]

lemma p5a_form_eq (w : ℝ × (Fin m → ℝ)) :
    p5a_borderedForm p w.1 w.2 = 2 * p5a_bcoord p w * p5a_s w - 2 * ‖p5a_y p w‖ ^ 2 := by
  rw [p5a_borderedForm_coordinate_identity]; rfl

/-- The polarized form in the coordinates `(β, s, y)`. -/
lemma p5a_bilin_eq (x x' : ℝ × (Fin m → ℝ)) :
    p5a_borderedBilin p x x' =
      p5a_bcoord p x * p5a_s x' + p5a_bcoord p x' * p5a_s x -
        2 * inner ℝ (p5a_y p x) (p5a_y p x') := by
  unfold p5a_borderedBilin
  have h := p5a_form_eq p (x + x')
  rw [p5a_bcoord_add, p5a_s_add, p5a_y_add, norm_add_sq_real] at h
  have h1 := p5a_form_eq p x
  have h2 := p5a_form_eq p x'
  simp only [Prod.fst_add, Prod.snd_add] at h
  rw [h, h1, h2]
  ring

lemma p5a_bilin_comm (x x' : ℝ × (Fin m → ℝ)) :
    p5a_borderedBilin p x x' = p5a_borderedBilin p x' x := by
  rw [p5a_bilin_eq, p5a_bilin_eq, real_inner_comm]; ring

lemma p5a_bcoord_smul (c : ℝ) (x : ℝ × (Fin m → ℝ)) :
    p5a_bcoord p (c • x) = c * p5a_bcoord p x := by
  simp [p5a_bcoord, mul_add, Finset.mul_sum, mul_left_comm]

lemma p5a_s_smul (c : ℝ) (x : ℝ × (Fin m → ℝ)) : p5a_s (c • x) = c * p5a_s x := by
  simp [p5a_s, Finset.mul_sum]

lemma p5a_y_smul (c : ℝ) (x : ℝ × (Fin m → ℝ)) : p5a_y p (c • x) = c • p5a_y p x := by
  simp [p5a_y, Finset.smul_sum, smul_smul]

lemma p5a_bilin_smul_left (c : ℝ) (x x' : ℝ × (Fin m → ℝ)) :
    p5a_borderedBilin p (c • x) x' = c * p5a_borderedBilin p x x' := by
  rw [p5a_bilin_eq, p5a_bilin_eq, p5a_bcoord_smul, p5a_s_smul, p5a_y_smul, inner_smul_left]
  simp; ring

end coords

/-- info: 'FormalResearch.EuclTet.p5a_borderedForm_coordinate_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms p5a_borderedForm_coordinate_identity


/-! ### Rank of the coordinate map and the radical -/

section rank
variable {m n : ℕ} (p : Fin m → EuclideanSpace ℝ (Fin n))

/-- The linear map `z ↦ (∑ zᵢ, ∑ zᵢ Pᵢ)`. -/
noncomputable def p5a_Psi : (Fin m → ℝ) →ₗ[ℝ] ℝ × EuclideanSpace ℝ (Fin n) where
  toFun z := (∑ i, z i, ∑ i, z i • p i)
  map_add' z z' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c z := by
    refine Prod.ext ?_ ?_
    · simp [Finset.mul_sum]
    · simp [Finset.smul_sum, smul_smul]

/-- The embedding `z ↦ (-∑ |Pᵢ|² zᵢ, z)` of the radical candidates. -/
noncomputable def p5a_iota : (Fin m → ℝ) →ₗ[ℝ] ℝ × (Fin m → ℝ) where
  toFun z := (-∑ i, ‖p i‖ ^ 2 * z i, z)
  map_add' z z' := by simp [mul_add, Finset.sum_add_distrib]; ring
  map_smul' c z := by
    ext
    · simp [Finset.mul_sum, mul_left_comm]
    · simp

lemma p5a_iota_injective : Function.Injective (p5a_iota p) := by
  intro z z' h
  exact congrArg Prod.snd h

/-- The radical of the bordered form. -/
noncomputable def p5a_V0 : Submodule ℝ (ℝ × (Fin m → ℝ)) :=
  (LinearMap.ker (p5a_Psi p)).map (p5a_iota p)

lemma p5a_mem_V0 (w : ℝ × (Fin m → ℝ)) :
    w ∈ p5a_V0 p ↔ p5a_bcoord p w = 0 ∧ p5a_s w = 0 ∧ p5a_y p w = 0 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have h1 : ∑ i, z i = 0 := congrArg Prod.fst hz
    have h2 : ∑ i, z i • p i = 0 := congrArg Prod.snd hz
    refine ⟨?_, h1, h2⟩
    simp [p5a_bcoord, p5a_iota]
  · rintro ⟨h0, h1, h2⟩
    refine ⟨w.2, ?_, ?_⟩
    · exact Prod.ext h1 h2
    · apply Prod.ext
      · simp only [p5a_iota, LinearMap.coe_mk, AddHom.coe_mk]
        unfold p5a_bcoord at h0; linarith
      · rfl

lemma p5a_V0_radical {x : ℝ × (Fin m → ℝ)} (hx : x ∈ p5a_V0 p) (w : ℝ × (Fin m → ℝ)) :
    p5a_borderedBilin p x w = 0 := by
  obtain ⟨h0, h1, h2⟩ := (p5a_mem_V0 p x).1 hx
  rw [p5a_bilin_eq, h0, h1, h2]; simp

lemma p5a_finrank_V0 : Module.finrank ℝ (p5a_V0 p) = Module.finrank ℝ (LinearMap.ker (p5a_Psi p)) :=
  (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (p5a_iota_injective p) _)).symm

/-- The range of `Ψ` splits as the line through `(1, P_{i₀})` and the direction. -/
lemma p5a_range_Psi (i0 : Fin m) :
    LinearMap.range (p5a_Psi p) =
      (ℝ ∙ ((1 : ℝ), p i0)) ⊔
        (vectorSpan ℝ (Set.range p)).map (LinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin n))) := by
  classical
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    have hmem : ∑ i, z i • p i - (∑ i, z i) • p i0 ∈ vectorSpan ℝ (Set.range p) := by
      rw [mem_vectorSpan_iff_eq_weightedVSub]
      refine ⟨Finset.univ, fun i => z i - (if i = i0 then ∑ j, z j else 0), ?_, ?_⟩
      · simp [Finset.sum_sub_distrib]
      · rw [Finset.weightedVSub_eq_linear_combination]
        · simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
        · simp [Finset.sum_sub_distrib]
    refine Submodule.mem_sup.2 ⟨(∑ i, z i) • ((1 : ℝ), p i0), Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self _), (0, ∑ i, z i • p i - (∑ i, z i) • p i0),
      ⟨_, hmem, rfl⟩, ?_⟩
    ext <;> simp [p5a_Psi]
  · refine sup_le ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨Pi.single i0 1, by simp [p5a_Psi]⟩
    · rintro _ ⟨v, hv, rfl⟩
      replace hv : v ∈ vectorSpan ℝ (Set.range p) := hv
      rw [mem_vectorSpan_iff_eq_weightedVSub] at hv
      obtain ⟨s, w, hw, rfl⟩ := hv
      refine ⟨fun i => if i ∈ s then w i else 0, ?_⟩
      have hs : ∑ i, (if i ∈ s then w i else 0) = 0 := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]; exact hw
      refine Prod.ext ?_ ?_
      · simpa [p5a_Psi] using hs
      · simp [p5a_Psi, Finset.weightedVSub_eq_linear_combination _ hw, Prod.snd_sum]

lemma p5a_finrank_range {d : ℕ} (hd : Module.finrank ℝ (vectorSpan ℝ (Set.range p)) = d)
    (i0 : Fin m) : Module.finrank ℝ (LinearMap.range (p5a_Psi p)) = d + 1 := by
  rw [p5a_range_Psi p i0]
  have hdisj : Disjoint (ℝ ∙ ((1 : ℝ), p i0))
      ((vectorSpan ℝ (Set.range p)).map (LinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin n)))) := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    obtain ⟨v, _, hv⟩ := hx'
    have : c = 0 := by simpa using (congrArg Prod.fst hv).symm
    simp [this]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (ℝ ∙ ((1 : ℝ), p i0))
    ((vectorSpan ℝ (Set.range p)).map (LinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin n))))
  rw [hdisj.eq_bot, finrank_bot, finrank_span_singleton (by simp)] at h
  have hm : Module.finrank ℝ
      ((vectorSpan ℝ (Set.range p)).map (LinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin n)))) = d := by
    rw [← hd]
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
      (LinearMap.inr_injective) _)).symm
  omega

end rank

/-! ### The inertia theorem -/

section main
variable {m n : ℕ} (p : Fin m → EuclideanSpace ℝ (Fin n))

/-- The vector `u = (1, e₀)`, on which the form equals `2`. -/
noncomputable def p5a_u (i0 : Fin m) : ℝ × (Fin m → ℝ) := (1, Pi.single i0 1)

lemma p5a_bcoord_u (i0 : Fin m) : p5a_bcoord p (p5a_u i0) = 1 + ‖p i0‖ ^ 2 := by
  simp [p5a_bcoord, p5a_u, Pi.single_apply]

lemma p5a_s_u (i0 : Fin m) : p5a_s (p5a_u i0 : ℝ × (Fin m → ℝ)) = 1 := by
  simp [p5a_s, p5a_u]

lemma p5a_y_u (i0 : Fin m) : p5a_y p (p5a_u i0) = p i0 := by
  simp [p5a_y, p5a_u, Pi.single_apply]

/-- The linear functional `w ↦ B(u, w)`. -/
noncomputable def p5a_f (i0 : Fin m) : (ℝ × (Fin m → ℝ)) →ₗ[ℝ] ℝ where
  toFun w := p5a_borderedBilin p (p5a_u i0) w
  map_add' x x' := by
    simp only [p5a_bilin_eq, p5a_bcoord_add, p5a_s_add, p5a_y_add, inner_add_right]; ring
  map_smul' c x := by
    simp only [p5a_bilin_eq, p5a_bcoord_smul, p5a_s_smul, p5a_y_smul, inner_smul_right,
      RingHom.id_apply, smul_eq_mul]; ring

lemma p5a_f_apply (i0 : Fin m) (w : ℝ × (Fin m → ℝ)) :
    p5a_f p i0 w = p5a_borderedBilin p (p5a_u i0) w := rfl

lemma p5a_f_u (i0 : Fin m) : p5a_f p i0 (p5a_u i0) = 2 := by
  rw [p5a_f_apply, p5a_bilin_eq, p5a_bcoord_u, p5a_s_u, p5a_y_u, real_inner_self_eq_norm_sq]; ring

lemma p5a_f_one (i0 : Fin m) : p5a_f p i0 ((1 : ℝ), (0 : Fin m → ℝ)) = 1 := by
  rw [p5a_f_apply, p5a_bilin_eq, p5a_s_u]
  simp [p5a_bcoord, p5a_s, p5a_y]

lemma p5a_finrank_ker_f (i0 : Fin m) :
    Module.finrank ℝ (LinearMap.ker (p5a_f p i0)) = m := by
  have h := LinearMap.finrank_range_add_finrank_ker (p5a_f p i0)
  have hr : LinearMap.range (p5a_f p i0) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨c • ((1 : ℝ), (0 : Fin m → ℝ)), by rw [map_smul, p5a_f_one]; simp⟩
  have h1 : Module.finrank ℝ ℝ = 1 := Module.finrank_self ℝ
  rw [hr, finrank_top, Module.finrank_prod, Module.finrank_fin_fun] at h
  omega

lemma p5a_neg_on_hyperplane (i0 : Fin m) (w : ℝ × (Fin m → ℝ))
    (hw : p5a_f p i0 w = 0) (hw0 : w ∉ p5a_V0 p) : p5a_borderedBilin p w w < 0 := by
  have hf : p5a_borderedBilin p (p5a_u i0) w = 0 := hw
  rw [p5a_bilin_eq, p5a_bcoord_u, p5a_s_u, p5a_y_u] at hf
  have hB : p5a_borderedBilin p w w =
      -2 * p5a_s w ^ 2 - 2 * ‖p5a_y p w - p5a_s w • p i0‖ ^ 2 := by
    rw [p5a_bilin_eq, real_inner_self_eq_norm_sq, norm_sub_sq_real, inner_smul_right, norm_smul,
      mul_pow, Real.norm_eq_abs, sq_abs]
    have : p5a_bcoord p w = 2 * inner ℝ (p i0) (p5a_y p w) - (1 + ‖p i0‖ ^ 2) * p5a_s w := by
      linarith
    rw [this, real_inner_comm (p5a_y p w) (p i0)]
    ring
  by_contra hcon
  push Not at hcon
  have h1 : p5a_s w = 0 := by
    nlinarith [sq_nonneg (p5a_s w), sq_nonneg ‖p5a_y p w - p5a_s w • p i0‖]
  have h2 : ‖p5a_y p w - p5a_s w • p i0‖ = 0 := by
    have : ‖p5a_y p w - p5a_s w • p i0‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg (p5a_s w), sq_nonneg ‖p5a_y p w - p5a_s w • p i0‖]
    exact (pow_eq_zero_iff two_ne_zero).1 this
  rw [h1, zero_smul, sub_zero, norm_eq_zero] at h2
  apply hw0
  refine (p5a_mem_V0 p w).2 ⟨?_, h1, h2⟩
  rw [h1, h2] at hf
  simp at hf
  exact hf

end main

/-- **Bordered-distance inertia** (Weyl/P5 `prop:inertia`, eq. `eq:generalinertia`).

Let `P₁,…,P_m` (`m ≥ 1`) be points of a Euclidean space `ℝⁿ` whose affine span has dimension
`d`, and let `p5a_borderedBilin p` be the symmetric bilinear form of the bordered matrix
`M_m = [[0, 1ᵀ],[1, D]]`, `D_ij = |P_i - P_j|²`, on `ℝ × ℝ^m` (so that
`p5a_borderedForm p α z = (α,z)ᵀ M_m (α,z)`).  Then `ℝ × ℝ^m` is the direct sum of three
subspaces, pairwise orthogonal for the form: `V₊` of dimension `1` on which the form is positive
definite, `V₋` of dimension `d+1` on which it is negative definite, and `V₀`, the radical, of
dimension `m-d-1` (the form vanishes against everything).  By Sylvester's law this is the
statement that `M_m` has `1` positive, `d+1` negative and `m-d-1` zero eigenvalues; the Lean
statement is the decomposition itself, since Mathlib has no inertia-count API.  The hypothesis
`0 < m` is needed (for `m = 0` the claim is false) and is automatic for a nonempty configuration.
The planar `(1,3,1)` and collinear `(1,2,2)` four-point statements are the instances `m = 4`,
`d = 2` and `d = 1` (no separate Lean statement; the sign of `c` in `adj(M) = c v vᵀ` is not
formalised here). -/
theorem p5a_bordered_distance_inertia
    {m n d : ℕ} (p : Fin m → EuclideanSpace ℝ (Fin n)) (hm : 0 < m)
    (h_affine_rank : Module.finrank ℝ (affineSpan ℝ (Set.range p)).direction = d) :
    ∃ (Vpos Vneg Vrad : Submodule ℝ (ℝ × (Fin m → ℝ))),
      Module.finrank ℝ Vpos = 1 ∧
      Module.finrank ℝ Vneg = d + 1 ∧
      Module.finrank ℝ Vrad = m - d - 1 ∧
      IsCompl Vpos (Vneg ⊔ Vrad) ∧ Disjoint Vneg Vrad ∧
      (∀ x ∈ Vpos, x ≠ 0 → 0 < p5a_borderedBilin p x x) ∧
      (∀ x ∈ Vneg, x ≠ 0 → p5a_borderedBilin p x x < 0) ∧
      (∀ x ∈ Vrad, ∀ y, p5a_borderedBilin p x y = 0) ∧
      (∀ x ∈ Vpos, ∀ y ∈ Vneg, p5a_borderedBilin p x y = 0) ∧
      (∀ x ∈ Vpos, ∀ y ∈ Vrad, p5a_borderedBilin p x y = 0) ∧
      (∀ x ∈ Vneg, ∀ y ∈ Vrad, p5a_borderedBilin p x y = 0) := by
  classical
  set i0 : Fin m := ⟨0, hm⟩ with hi0
  have hd : Module.finrank ℝ (vectorSpan ℝ (Set.range p)) = d := by
    rw [← direction_affineSpan]; exact h_affine_rank
  have hrange := p5a_finrank_range p hd i0
  have hker := LinearMap.finrank_range_add_finrank_ker (p5a_Psi p)
  rw [hrange, Module.finrank_fin_fun] at hker
  have hV0 : Module.finrank ℝ (p5a_V0 p) = m - d - 1 := by
    rw [p5a_finrank_V0]; omega
  set H := LinearMap.ker (p5a_f p i0) with hH
  have hV0H : p5a_V0 p ≤ H := by
    intro x hx
    show p5a_f p i0 x = 0
    rw [p5a_f_apply, p5a_bilin_comm]
    exact p5a_V0_radical p hx _
  obtain ⟨C0, hC0⟩ := Submodule.exists_isCompl (p5a_V0 p)
  set C := C0 ⊓ H with hC
  have hsup : p5a_V0 p ⊔ C = H := by
    rw [hC, ← sup_inf_assoc_of_le _ hV0H, hC0.sup_eq_top, top_inf_eq]
  have hdisj : Disjoint (p5a_V0 p) C := hC0.disjoint.mono_right inf_le_left
  have hCdim : Module.finrank ℝ C = d + 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (p5a_V0 p) C
    rw [hsup, hdisj.eq_bot, finrank_bot, p5a_finrank_ker_f p i0, hV0] at h
    omega
  have hu0 : p5a_u i0 ≠ 0 := fun h => by
    have := congrArg Prod.fst h
    simp [p5a_u] at this
  have hfC : ∀ w ∈ C, p5a_f p i0 w = 0 := fun w hw => hw.2
  refine ⟨ℝ ∙ p5a_u i0, C, p5a_V0 p, finrank_span_singleton hu0, hCdim, hV0, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [sup_comm, hsup]
    refine ⟨?_, ?_⟩
    · rw [Submodule.disjoint_def]
      intro x hx hxH
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      have : c * 2 = 0 := by
        have := hxH
        simp only [hH, LinearMap.mem_ker, map_smul, p5a_f_u, smul_eq_mul] at this
        exact this
      have hc : c = 0 := by linarith
      simp [hc]
    · rw [codisjoint_iff, eq_top_iff]
      intro w _
      have hw : w = (p5a_f p i0 w / 2) • p5a_u i0 + (w - (p5a_f p i0 w / 2) • p5a_u i0) := by
        abel
      rw [hw]
      refine Submodule.add_mem_sup (Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self _)) ?_
      simp only [hH, LinearMap.mem_ker, map_sub, map_smul, p5a_f_u, smul_eq_mul]
      ring
  · exact hdisj.symm
  · rintro x hx hx0
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    have hc : c ≠ 0 := fun h => hx0 (by simp [h])
    have h2 : p5a_borderedBilin p (p5a_u i0) (p5a_u i0) = 2 := p5a_f_u p i0
    have : p5a_borderedBilin p (c • p5a_u i0) (c • p5a_u i0) = c * (c * 2) := by
      rw [p5a_bilin_smul_left, p5a_bilin_comm, p5a_bilin_smul_left, p5a_bilin_comm, h2]
    rw [this]; nlinarith [sq_pos_of_ne_zero hc]
  · rintro x hx hx0
    apply p5a_neg_on_hyperplane p i0 x (hfC x hx)
    intro hx'
    exact hx0 (by simpa using hdisj.le_bot ⟨hx', hx⟩)
  · exact fun x hx y => p5a_V0_radical p hx y
  · rintro x hx y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [p5a_bilin_smul_left]
    have := hfC y hy
    rw [p5a_f_apply] at this
    rw [this, mul_zero]
  · rintro x hx y hy
    rw [p5a_bilin_comm]; exact p5a_V0_radical p hy x
  · rintro x hx y hy
    rw [p5a_bilin_comm]; exact p5a_V0_radical p hy x

/-- info: 'FormalResearch.EuclTet.p5a_bordered_distance_inertia' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms p5a_bordered_distance_inertia

end FormalResearch.EuclTet
