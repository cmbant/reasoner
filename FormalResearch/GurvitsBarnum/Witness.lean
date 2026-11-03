module

public import Mathlib
public import FormalResearch.GurvitsBarnum.Basic
public import FormalResearch.GurvitsBarnum.BlockBound

/-!
# Gurvits–Barnum separable ball: witnesses are non-negative on the ball

Source: L. Gurvits and H. Barnum, *Largest separable balls around the maximally mixed bipartite
quantum state*, Phys. Rev. A 66, 062311 (2002), Sec. III; plan lemma L6 (module M7).

For a Hermitian block-positive `W` on `ι × κ` and Hermitian `Δ` with `∑ ‖Δ p q‖² ≤ 1` we prove
`0 ≤ Re tr (W (1 + Δ))` (`trace_mul_one_add_nonneg`), assuming as a hypothesis the contraction bound
(plan lemma L3, Russo–Dye) for positive unital maps.  The proof normalises `φ_W + ε` to a unital
map `S φ Sᴴ` with `S = (yᴴ)⁻¹`, where `φ_{W+ε}(1) = yᴴ y`, applies `BlockBound.idTensor_one_add_posSemidef`
and the identity `⟨ω, (id ⊗ φ_W)(Y) ω⟩ = tr (W Y)`, and lets `ε → 0`.  The corollary
`sum_norm_sq_le_trace_sq` is the inequality `‖W‖₂ ≤ tr W` (plan inequality (K)).
-/

@[expose] public section


set_option linter.unusedSectionVars false

namespace FormalResearch.GurvitsBarnum

open Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Witness

variable {ι κ μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ]

/-! ### Congruence of `id ⊗ φ` -/

theorem kron_mul_mul_apply (A C : Matrix μ μ ℂ) (M : Matrix (ι × μ) (ι × μ) ℂ)
    (i j : ι) (i' j' : μ) :
    (((1 : Matrix ι ι ℂ) ⊗ₖ A) * M * ((1 : Matrix ι ι ℂ) ⊗ₖ C)) (i, i') (j, j')
      = (A * matBlock M i j * C) i' j' := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, kronecker_apply, one_apply, matBlock_apply,
    ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- Congruence: if `φ' X = S * φ X * R` for all `X` then
`(id ⊗ φ') Y = (1 ⊗ S) * (id ⊗ φ) Y * (1 ⊗ R)`. -/
theorem idTensor_congr (φ φ' : Matrix κ κ ℂ →ₗ[ℂ] Matrix μ μ ℂ) (S R : Matrix μ μ ℂ)
    (h : ∀ X, φ' X = S * φ X * R) (Y : Matrix (ι × κ) (ι × κ) ℂ) :
    idTensor φ' Y = ((1 : Matrix ι ι ℂ) ⊗ₖ S) * idTensor φ Y * ((1 : Matrix ι ι ℂ) ⊗ₖ R) := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  rw [kron_mul_mul_apply, idTensor_apply, h]
  rfl

/-! ### Positive definite matrices have a unital congruence -/

theorem exists_unital_congr {T : Matrix ι ι ℂ} (hT : T.PosDef) :
    ∃ B S : Matrix ι ι ℂ, T = Bᴴ * B ∧ Bᴴ * S = 1 ∧ S * Bᴴ = 1 := by
  obtain ⟨y, hy, hyT⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hT.isStrictlyPositive
  lift y to (Matrix ι ι ℂ)ˣ using hy
  refine ⟨y, ((y⁻¹ : (Matrix ι ι ℂ)ˣ) : Matrix ι ι ℂ)ᴴ, hyT, ?_, ?_⟩
  · rw [← conjTranspose_mul, Units.inv_mul, conjTranspose_one]
  · rw [← conjTranspose_mul, Units.mul_inv, conjTranspose_one]

/-! ### The `ε`-shifted witness -/

theorem choiMap_conjTranspose {W : Matrix (ι × κ) (ι × κ) ℂ} (hW : W.IsHermitian)
    (X : Matrix κ κ ℂ) : choiMap W Xᴴ = (choiMap W X)ᴴ := by
  ext i j
  simp only [conjTranspose_apply, choiMap_apply, star_sum, star_mul']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hW.apply]

theorem posSemidef_smul_one {ν : Type*} [Fintype ν] [DecidableEq ν] (ε : ℝ) (hε : 0 ≤ ε) :
    ((ε : ℂ) • (1 : Matrix ν ν ℂ)).PosSemidef :=
  Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr hε)

/-- If `0 ≤ a + ε b` for all `ε > 0` then `0 ≤ a`. -/
theorem nonneg_of_forall_pos_add (a b : ℝ) (h : ∀ ε : ℝ, 0 < ε → 0 ≤ a + ε * b) : 0 ≤ a := by
  by_contra ha
  have hc : 0 < -a := by linarith
  have hb : 0 < |b| + 1 := by positivity
  have hε : 0 < -a / (2 * (|b| + 1)) := div_pos hc (by positivity)
  have := h _ hε
  have h3 : -a / (2 * (|b| + 1)) * b ≤ -a / 2 := by
    calc -a / (2 * (|b| + 1)) * b ≤ -a / (2 * (|b| + 1)) * (|b| + 1) :=
          mul_le_mul_of_nonneg_left ((le_abs_self b).trans (by linarith)) hε.le
      _ = -a / 2 := by field_simp
  linarith

/-! ### Headline -/

/-- **L6 (K-form).** (Gurvits–Barnum, PRA 66, 062311, Sec. III; plan lemma L6, `(**)`.)
Assume the contraction bound for positive unital maps `Matrix κ κ ℂ →ₗ Matrix ι ι ℂ` (plan lemma L3,
Russo–Dye; a hypothesis here).  If `W` is Hermitian and block-positive and `Δ` is Hermitian with
`∑ ‖Δ p q‖² ≤ 1`, then `0 ≤ Re tr (W (1 + Δ))`. -/
theorem trace_mul_one_add_nonneg
    (hcontr : ∀ (φ : Matrix κ κ ℂ →ₗ[ℂ] Matrix ι ι ℂ), (∀ P, P.PosSemidef → (φ P).PosSemidef) →
      φ 1 = 1 → BlockBound.ContractionBound φ)
    {W : Matrix (ι × κ) (ι × κ) ℂ} (hWh : W.IsHermitian) (hW : IsBlockPositive W)
    {Δ : Matrix (ι × κ) (ι × κ) ℂ} (hΔh : Δ.IsHermitian) (hΔ : ∑ p, ∑ q, ‖Δ p q‖ ^ 2 ≤ 1) :
    0 ≤ (trace (W * (1 + Δ))).re := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · have : IsEmpty (ι × κ) := inferInstance
    simp [Matrix.trace]
  have key : ∀ ε : ℝ, 0 < ε →
      0 ≤ (trace ((W + (ε : ℂ) • (1 : Matrix (ι × κ) (ι × κ) ℂ)) * (1 + Δ))).re := by
    intro ε hε
    have hεP := posSemidef_smul_one (ν := ι × κ) ε hε.le
    have hWεh : (W + (ε : ℂ) • (1 : Matrix (ι × κ) (ι × κ) ℂ)).IsHermitian :=
      hWh.add hεP.isHermitian
    have hWε : IsBlockPositive (W + (ε : ℂ) • (1 : Matrix (ι × κ) (ι × κ) ℂ)) :=
      hW.add (IsBlockPositive.of_posSemidef hεP)
    set Wε := W + (ε : ℂ) • (1 : Matrix (ι × κ) (ι × κ) ℂ) with hWεdef
    have hpos : ∀ P : Matrix κ κ ℂ, P.PosSemidef → (choiMap Wε P).PosSemidef :=
      fun P hP => choiMap_posSemidef hWεh hWε hP
    -- `T = φ_{Wε}(1)` is positive definite
    have hT : (choiMap Wε 1).PosDef := by
      rw [hWεdef, choiMap_one_add_smul_one]
      have h0 : (choiMap W 1).PosSemidef := choiMap_posSemidef hWh hW Matrix.PosSemidef.one
      have hc : (0 : ℂ) < (ε : ℂ) * (Fintype.card κ : ℂ) := by
        have : 0 < Fintype.card κ := Fintype.card_pos
        have h' : (0 : ℝ) < ε * (Fintype.card κ : ℝ) := by positivity
        exact_mod_cast h'
      exact Matrix.PosDef.posSemidef_add h0 ((Matrix.PosDef.one (n := ι) (R := ℂ)).smul hc)
    obtain ⟨B, S, hTB, hBS, hSB⟩ := exists_unital_congr hT
    -- the normalised map
    let φ' : Matrix κ κ ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
      (LinearMap.mulLeft ℂ S ∘ₗ LinearMap.mulRight ℂ Sᴴ) ∘ₗ choiMap Wε
    have hφ'X : ∀ X, φ' X = S * choiMap Wε X * Sᴴ := by
      intro X; simp [φ', Matrix.mul_assoc]
    have hSBt : Sᴴ * B = 1 := by
      have := congrArg conjTranspose hBS
      simpa [conjTranspose_mul] using this
    have hBSt : B * Sᴴ = 1 := by
      have := congrArg conjTranspose hSB
      simpa [conjTranspose_mul] using this
    have hφ'pos : ∀ P, P.PosSemidef → (φ' P).PosSemidef := by
      intro P hP
      rw [hφ'X]
      exact (hpos P hP).mul_mul_conjTranspose_same S
    have hφ'1 : φ' 1 = 1 := by
      rw [hφ'X, hTB]
      calc S * (Bᴴ * B) * Sᴴ = (S * Bᴴ) * (B * Sᴴ) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hSB, hBSt, Matrix.mul_one]
    have hφ'h : ∀ X, φ' Xᴴ = (φ' X)ᴴ := by
      intro X
      rw [hφ'X, hφ'X, choiMap_conjTranspose hWεh, conjTranspose_mul, conjTranspose_mul,
        conjTranspose_conjTranspose, Matrix.mul_assoc]
    have hPSD := BlockBound.idTensor_one_add_posSemidef φ' hφ'h hφ'1
      (hcontr φ' hφ'pos hφ'1) Δ hΔh hΔ
    -- transfer back
    have hback : ∀ X, choiMap Wε X = Bᴴ * φ' X * B := by
      intro X
      rw [hφ'X]
      calc choiMap Wε X = (Bᴴ * S) * choiMap Wε X * (Sᴴ * B) := by rw [hBS, hSBt]; simp
        _ = Bᴴ * (S * choiMap Wε X * Sᴴ) * B := by simp only [Matrix.mul_assoc]
    have hcongr : idTensor (choiMap Wε) (1 + Δ)
        = ((1 : Matrix ι ι ℂ) ⊗ₖ B)ᴴ * idTensor φ' (1 + Δ) * ((1 : Matrix ι ι ℂ) ⊗ₖ B) := by
      rw [conjTranspose_kronecker, conjTranspose_one]
      exact idTensor_congr φ' (choiMap Wε) Bᴴ B hback _
    have hPSD2 : (idTensor (choiMap Wε) (1 + Δ)).PosSemidef := by
      rw [hcongr]
      exact hPSD.conjTranspose_mul_mul_same _
    have h3 := hPSD2.dotProduct_mulVec_nonneg (omega ι)
    rw [star_omega_idTensor_choiMap] at h3
    exact (Complex.nonneg_iff.mp h3).1
  refine nonneg_of_forall_pos_add _ (trace (1 + Δ)).re fun ε hε => ?_
  have := key ε hε
  rwa [add_mul, Matrix.smul_mul, one_mul, trace_add, trace_smul, Complex.add_re, smul_eq_mul,
    Complex.re_ofReal_mul] at this

/-- `0 ≤ Re tr W` for a Hermitian block-positive `W`, under the same contraction hypothesis. -/
theorem trace_re_nonneg_of_blockPositive
    (hcontr : ∀ (φ : Matrix κ κ ℂ →ₗ[ℂ] Matrix ι ι ℂ), (∀ P, P.PosSemidef → (φ P).PosSemidef) →
      φ 1 = 1 → BlockBound.ContractionBound φ)
    {W : Matrix (ι × κ) (ι × κ) ℂ} (hWh : W.IsHermitian) (hW : IsBlockPositive W) :
    0 ≤ (trace W).re := by
  have := trace_mul_one_add_nonneg hcontr hWh hW (Δ := 0) Matrix.isHermitian_zero (by simp)
  simpa using this

/-- **Inequality (K).** (Gurvits–Barnum, PRA 66, 062311, Sec. III; plan lemma L6 and inequality `(K)`.)
Under the contraction hypothesis, a Hermitian block-positive `W` satisfies
`∑ ‖W p q‖² ≤ (Re tr W)²`, i.e. `‖W‖₂ ≤ tr W`. -/
theorem sum_norm_sq_le_trace_sq
    (hcontr : ∀ (φ : Matrix κ κ ℂ →ₗ[ℂ] Matrix ι ι ℂ), (∀ P, P.PosSemidef → (φ P).PosSemidef) →
      φ 1 = 1 → BlockBound.ContractionBound φ)
    {W : Matrix (ι × κ) (ι × κ) ℂ} (hWh : W.IsHermitian) (hW : IsBlockPositive W) :
    ∑ p, ∑ q, ‖W p q‖ ^ 2 ≤ ((trace W).re) ^ 2 := by
  set N : ℝ := ∑ p, ∑ q, ‖W p q‖ ^ 2 with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have htr0 := trace_re_nonneg_of_blockPositive hcontr hWh hW
  rcases hN0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  set r : ℝ := Real.sqrt N with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hpos
  have hr2 : r ^ 2 = N := Real.sq_sqrt hN0
  set c : ℝ := -(1 / r) with hc
  have hΔh : ((c : ℂ) • W).IsHermitian := by
    rw [IsHermitian, conjTranspose_smul, hWh.eq, Complex.star_def, Complex.conj_ofReal]
  have hΔ : ∑ p, ∑ q, ‖((c : ℂ) • W) p q‖ ^ 2 ≤ 1 := by
    simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, ← Finset.mul_sum]
    rw [← hN, hc, neg_sq, div_pow, one_pow, ← hr2]
    field_simp
    exact le_refl _
  have h := trace_mul_one_add_nonneg hcontr hWh hW hΔh hΔ
  have hWW : trace (W * W) = ((N : ℝ) : ℂ) := by
    simp only [trace, diag, Matrix.mul_apply, hN, Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [← hWh.apply q p, ← Complex.conj_mul']
    rw [Complex.star_def, mul_comm]
  rw [mul_add, mul_one, Matrix.mul_smul, trace_add, trace_smul, hWW, Complex.add_re,
    smul_eq_mul, Complex.re_ofReal_mul, Complex.ofReal_re, hc] at h
  have h4 : r ≤ (trace W).re := by
    have h5 : N * (1 / r) = r := by rw [← hr2]; field_simp
    linarith
  rw [← hr2]
  exact pow_le_pow_left₀ hr0.le h4 2

end Witness

end

end FormalResearch.GurvitsBarnum

/-- info: 'FormalResearch.GurvitsBarnum.Witness.trace_mul_one_add_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.GurvitsBarnum.Witness.trace_mul_one_add_nonneg

/-- info: 'FormalResearch.GurvitsBarnum.Witness.sum_norm_sq_le_trace_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.GurvitsBarnum.Witness.sum_norm_sq_le_trace_sq

/-- info: 'FormalResearch.GurvitsBarnum.Witness.trace_re_nonneg_of_blockPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.GurvitsBarnum.Witness.trace_re_nonneg_of_blockPositive
