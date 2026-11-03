module

public import FormalResearch.GurvitsBarnum.Contraction
public import FormalResearch.GurvitsBarnum.Witness
public import FormalResearch.GurvitsBarnum.Separation

/-!
# The Gurvits–Barnum separable ball

Source: L. Gurvits and H. Barnum, *Largest separable balls around the maximally mixed bipartite
quantum state*, Phys. Rev. A 66, 062311 (2002), Sec. III.

Headlines (all for finite index types `ι`, `κ`):

* `GurvitsBarnum.contractionBound_of_isPositiveMap`: a positive unital map satisfies the Frobenius
  contraction bound `‖⟨u, φ(X) w⟩‖ ≤ c ‖u‖ ‖w‖` whenever `∑ ‖X i j‖² ≤ c²` (plan lemma L3 together with
  the double-sum Cauchy–Schwarz inequality).
* `GurvitsBarnum.gurvits_barnum`: if `Δ` is Hermitian with `∑ ‖Δ p q‖² ≤ 1` (Hilbert–Schmidt norm at
  most `1`), then `1 + Δ` is separable.
* `GurvitsBarnum.isSeparable_of_sum_norm_sq_sub_smul_one_le`: the scaled form, a Hermitian `Y` within
  Hilbert–Schmidt distance `c` of `c • 1` is separable.  This is the Gurvits–Barnum step in the PPT
  three-qubit paper (a residual within Hilbert–Schmidt distance `c` of `c I`).
* `GurvitsBarnum.sum_norm_sq_le_trace_sq_of_blockPositive`: every Hermitian block-positive `W` obeys
  `∑ ‖W p q‖² ≤ (Re tr W)²`, i.e. `‖W‖₂ ≤ tr W`.
-/

@[expose] public section


namespace FormalResearch.GurvitsBarnum

open Matrix ComplexOrder

noncomputable section

section CS

variable {κ : Type*} [Fintype κ]

/-- Double-sum Cauchy–Schwarz: `‖⟨u, X w⟩‖ ≤ (∑ ‖X i j‖²)^{1/2} ‖u‖ ‖w‖`, in the form with a bound
`c` on the Frobenius norm. -/
theorem norm_dot_mulVec_le_of_sum_norm_sq_le (X : Matrix κ κ ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hX : ∑ i, ∑ j, ‖X i j‖ ^ 2 ≤ c ^ 2) (u w : κ → ℂ) :
    ‖star u ⬝ᵥ (X *ᵥ w)‖ ≤
      c * ‖(WithLp.toLp 2 u : EuclideanSpace ℂ κ)‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ κ)‖ := by
  have hnu : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ κ)‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have hnw : ‖(WithLp.toLp 2 w : EuclideanSpace ℂ κ)‖ ^ 2 = ∑ i, ‖w i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  set a : κ × κ → ℝ := fun p => ‖X p.1 p.2‖ with ha
  set b : κ × κ → ℝ := fun p => ‖u p.1‖ * ‖w p.2‖ with hb
  have h1 : ‖star u ⬝ᵥ (X *ᵥ w)‖ ≤ ∑ p : κ × κ, a p * b p := by
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, Fintype.sum_prod_type]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    simp only [ha, hb, norm_mul, norm_star]
    rw [← mul_assoc, ← mul_assoc]
    apply le_of_eq
    ring
  have h2 : (∑ p : κ × κ, a p * b p) ^ 2 ≤ (∑ p, a p ^ 2) * (∑ p, b p ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : ∑ p : κ × κ, a p ^ 2 ≤ c ^ 2 := by
    simpa only [ha, Fintype.sum_prod_type] using hX
  have h4 : ∑ p : κ × κ, b p ^ 2 =
      ‖(WithLp.toLp 2 u : EuclideanSpace ℂ κ)‖ ^ 2 * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ κ)‖ ^ 2 := by
    rw [hnu, hnw, Finset.sum_mul_sum, Fintype.sum_prod_type]
    simp only [hb, mul_pow]
  have h5 : (∑ p : κ × κ, a p * b p) ^ 2 ≤
      (c * ‖(WithLp.toLp 2 u : EuclideanSpace ℂ κ)‖ * ‖(WithLp.toLp 2 w : EuclideanSpace ℂ κ)‖) ^ 2 := by
    calc (∑ p : κ × κ, a p * b p) ^ 2 ≤ (∑ p, a p ^ 2) * (∑ p, b p ^ 2) := h2
      _ ≤ c ^ 2 * (∑ p, b p ^ 2) :=
          mul_le_mul_of_nonneg_right h3 (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ = _ := by rw [h4]; ring
  have h6 := abs_le_of_sq_le_sq h5 (by positivity)
  exact h1.trans ((le_abs_self _).trans h6)

end CS

section Main

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **Contraction bound for positive unital maps** (Gurvits–Barnum, PRA 66, 062311 (2002), Sec. III;
plan lemma L3 and the double-sum Cauchy–Schwarz step).  A positive unital linear map
`φ : M_κ → M_μ` satisfies `‖⟨u, φ(X) w⟩‖ ≤ c ‖u‖ ‖w‖` whenever `∑ ‖X i j‖² ≤ c²`. -/
theorem contractionBound_of_isPositiveMap {μ : Type*} [Fintype μ] [DecidableEq μ]
    {φ : Matrix κ κ ℂ →ₗ[ℂ] Matrix μ μ ℂ} (hφ : IsPositiveMap φ) (h1 : φ 1 = 1) :
    BlockBound.ContractionBound φ := by
  intro X c hc hX u w
  have hu : BlockBound.vnorm u = ‖(WithLp.toLp 2 u : EuclideanSpace ℂ μ)‖ := by
    rw [BlockBound.vnorm, EuclideanSpace.norm_eq]
  have hw : BlockBound.vnorm w = ‖(WithLp.toLp 2 w : EuclideanSpace ℂ μ)‖ := by
    rw [BlockBound.vnorm, EuclideanSpace.norm_eq]
  rw [hu, hw]
  exact hφ.norm_dot_le_of_norm_dot_le h1 hc
    (fun u' w' => norm_dot_mulVec_le_of_sum_norm_sq_le X hc hX u' w') u w

/-- **Witness inequality** (Gurvits–Barnum, PRA 66, 062311 (2002), Sec. III, inequality (K)).  A
Hermitian block-positive `W` satisfies `∑ ‖W p q‖² ≤ (Re tr W)²`, i.e. `‖W‖₂ ≤ tr W`. -/
theorem sum_norm_sq_le_trace_sq_of_blockPositive
    {W : Matrix (ι × κ) (ι × κ) ℂ} (hWh : W.IsHermitian) (hW : IsBlockPositive W) :
    ∑ p, ∑ q, ‖W p q‖ ^ 2 ≤ ((trace W).re) ^ 2 :=
  Witness.sum_norm_sq_le_trace_sq
    (fun _ hφ h1 => contractionBound_of_isPositiveMap hφ h1) hWh hW

/-- **The Gurvits–Barnum separable ball** (Gurvits–Barnum, PRA 66, 062311 (2002), Thm. 1; plan
lemmas D2 and L6).  If `Δ` is Hermitian with Hilbert–Schmidt norm `‖Δ‖₂ ≤ 1`, then `1 + Δ` is
separable. -/
theorem gurvits_barnum {Δ : Matrix (ι × κ) (ι × κ) ℂ} (hΔh : Δ.IsHermitian)
    (hΔ : ∑ p, ∑ q, ‖Δ p q‖ ^ 2 ≤ 1) : IsSeparable (1 + Δ) := by
  by_contra hns
  have h1 : (1 + Δ).IsHermitian := Matrix.isHermitian_one.add hΔh
  obtain ⟨W, hWh, hW, hlt⟩ := exists_blockPositive_separating h1 hns
  have := Witness.trace_mul_one_add_nonneg
    (fun _ hφ h1 => contractionBound_of_isPositiveMap hφ h1) hWh hW hΔh hΔ
  linarith

/-- **Scaled Gurvits–Barnum ball** (Gurvits–Barnum, PRA 66, 062311 (2002), Thm. 1).  For `c > 0`, a
Hermitian `Y` within Hilbert–Schmidt distance `c` of `c • 1` is separable.  This is the form used in
the PPT three-qubit paper's Gurvits–Barnum step (a residual within Hilbert–Schmidt distance `c` of
`c I`). -/
theorem isSeparable_of_sum_norm_sq_sub_smul_one_le {c : ℝ} (hc : 0 < c)
    {Y : Matrix (ι × κ) (ι × κ) ℂ} (hY : Y.IsHermitian)
    (hd : ∑ p, ∑ q, ‖(Y - c • (1 : Matrix (ι × κ) (ι × κ) ℂ)) p q‖ ^ 2 ≤ c ^ 2) :
    IsSeparable Y := by
  set Δ : Matrix (ι × κ) (ι × κ) ℂ := c⁻¹ • (Y - c • 1) with hΔdef
  have hΔh : Δ.IsHermitian := by
    have h1 : (Y - c • (1 : Matrix (ι × κ) (ι × κ) ℂ)).IsHermitian := by
      refine hY.sub ?_
      unfold Matrix.IsHermitian
      rw [conjTranspose_smul, conjTranspose_one]
      simp
    unfold Matrix.IsHermitian at h1 ⊢
    rw [hΔdef, conjTranspose_smul, h1]
    simp
  have hΔ : ∑ p, ∑ q, ‖Δ p q‖ ^ 2 ≤ 1 := by
    have hc2 : 0 < c ^ 2 := by positivity
    simp only [hΔdef, Matrix.smul_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc,
      mul_pow, ← Finset.mul_sum, inv_pow]
    rw [inv_mul_le_iff₀ hc2]
    simpa using hd
  have hsep := (gurvits_barnum hΔh hΔ).smul_nonneg hc.le
  have : Y = c • (1 + Δ) := by
    rw [hΔdef, smul_add, smul_smul, mul_inv_cancel₀ hc.ne', one_smul, add_sub_cancel]
  rwa [this]

end Main

end

end FormalResearch.GurvitsBarnum

/-- info: 'FormalResearch.GurvitsBarnum.contractionBound_of_isPositiveMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.GurvitsBarnum.contractionBound_of_isPositiveMap

/-- info: 'FormalResearch.GurvitsBarnum.sum_norm_sq_le_trace_sq_of_blockPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.GurvitsBarnum.sum_norm_sq_le_trace_sq_of_blockPositive

/-- info: 'FormalResearch.GurvitsBarnum.gurvits_barnum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.GurvitsBarnum.gurvits_barnum

/-- info: 'FormalResearch.GurvitsBarnum.isSeparable_of_sum_norm_sq_sub_smul_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.GurvitsBarnum.isSeparable_of_sum_norm_sq_sub_smul_one_le
