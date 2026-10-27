import Mathlib
import FormalResearch.FrameFree.Foundations
import FormalResearch.FrameFree.Zariski
import FormalResearch.FrameFree.TwirlsBicommutant

/-!
# Schur--Weyl duality for qubits with sharing patterns (Paper P, `thm:onecopy`, `thm:copythreshold`)

Namespace `FormalResearch.FrameFree.Twirls`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate
open FormalResearch.FrameFree.NQubit (Op1 SU2)

namespace FormalResearch.FrameFree.Twirls

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Operators on the qubits indexed by `ι`, in the product basis. -/
abbrev OpS (ι : Type*) := Matrix (ι → Fin 2) (ι → Fin 2) ℂ

/-- The local operator `⊗_i v_{π i}` (slot `i` carries the frame of its block `π i`). -/
noncomputable def tensOp (π : ι → κ) (v : κ → Op1) : OpS ι :=
  Matrix.of fun x y => ∏ i, v (π i) (x i) (y i)

/-- The slot-permutation operator `(P_σ ψ)(x) = ψ(x ∘ σ)`. -/
def permOp (σ : Equiv.Perm ι) : OpS ι := Matrix.of fun x y => if y = x ∘ σ then 1 else 0

theorem comp_inv_comp {α : Type*} (z : ι → α) (σ : Equiv.Perm ι) : (z ∘ ⇑(σ⁻¹)) ∘ ⇑σ = z := by
  ext i; simp

theorem comp_comp_inv {α : Type*} (z : ι → α) (σ : Equiv.Perm ι) : (z ∘ ⇑σ) ∘ ⇑(σ⁻¹) = z := by
  ext i; simp

theorem eq_comp_iff (σ : Equiv.Perm ι) (z y : ι → Fin 2) : z = y ∘ ⇑σ ↔ y = z ∘ ⇑(σ⁻¹) := by
  constructor
  · intro h; rw [h, comp_comp_inv]
  · intro h; rw [h, comp_inv_comp]

theorem mul_permOp_apply (A : OpS ι) (σ : Equiv.Perm ι) (x z : ι → Fin 2) :
    (A * permOp σ) x z = A x (z ∘ ⇑(σ⁻¹)) := by
  simp only [Matrix.mul_apply, permOp, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (z ∘ ⇑(σ⁻¹))]
  · rw [if_pos ((eq_comp_iff σ z _).2 rfl)]
  · intro y _ hy
    rw [if_neg]
    intro h; exact hy ((eq_comp_iff σ z y).1 h)
  · simp

theorem permOp_mul_apply (A : OpS ι) (σ : Equiv.Perm ι) (x z : ι → Fin 2) :
    (permOp σ * A) x z = A (x ∘ ⇑σ) z := by
  simp only [Matrix.mul_apply, permOp, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  simp

theorem permOp_mul (σ τ : Equiv.Perm ι) : permOp σ * permOp τ = permOp (σ * τ) := by
  ext x z
  rw [permOp_mul_apply]
  simp only [permOp, Matrix.of_apply]
  rfl

theorem permOp_one : permOp (1 : Equiv.Perm ι) = 1 := by
  ext x z
  simp [permOp, Matrix.one_apply, eq_comm]

theorem permOp_conjTranspose (σ : Equiv.Perm ι) : (permOp σ)ᴴ = permOp σ⁻¹ := by
  ext x z
  simp only [Matrix.conjTranspose_apply, permOp, Matrix.of_apply]
  by_cases h : x = z ∘ ⇑σ
  · rw [if_pos h, if_pos ((eq_comp_iff σ⁻¹ z x).2 (by rw [inv_inv]; exact h))]; simp
  · rw [if_neg h, if_neg (fun h' => h ((eq_comp_iff σ⁻¹ z x).1 h' |>.trans (by rw [inv_inv])))]; simp

theorem tensOp_commute (π : ι → κ) (v : κ → Op1) (σ : Equiv.Perm ι) (hσ : ∀ i, π (σ i) = π i) :
    tensOp π v * permOp σ = permOp σ * tensOp π v := by
  ext x z
  rw [mul_permOp_apply, permOp_mul_apply]
  simp only [tensOp, Matrix.of_apply]
  rw [← Equiv.prod_comp σ]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [hσ]

/-! ### Two functions with the same fibre counts differ by a permutation -/

theorem exists_perm_of_card_fiber_eq {β : Type*} [DecidableEq β] (f f' : ι → β)
    (h : ∀ b, (Finset.univ.filter fun i => f' i = b).card = (Finset.univ.filter fun i => f i = b).card) :
    ∃ σ : Equiv.Perm ι, ∀ i, f' i = f (σ i) := by
  have e : ∀ b, {i // f' i = b} ≃ {i // f i = b} := fun b =>
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]; exact h b)
  refine ⟨(Equiv.sigmaFiberEquiv f').symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv f)), fun i => ?_⟩
  simp only [Equiv.trans_apply, Equiv.sigmaCongrRight_apply, Equiv.sigmaFiberEquiv_apply]
  exact (e (f' i) ⟨i, rfl⟩).2.symm

/-- The *type* of a pair of basis words: the multiset of `(block, bra letter, ket letter)` over slots,
as a monomial exponent. -/
noncomputable def typ (π : ι → κ) (x y : ι → Fin 2) : (κ × Fin 2 × Fin 2) →₀ ℕ :=
  ∑ i, Finsupp.single (π i, x i, y i) 1

theorem typ_apply (π : ι → κ) (x y : ι → Fin 2) (b : κ × Fin 2 × Fin 2) :
    typ π x y b = (Finset.univ.filter fun i => (π i, x i, y i) = b).card := by
  simp [typ, Finsupp.finset_sum_apply, Finsupp.single_apply, Finset.sum_boole]

theorem exists_perm_of_typ_eq (π : ι → κ) {x y x' y' : ι → Fin 2} (h : typ π x' y' = typ π x y) :
    ∃ σ : Equiv.Perm ι, (∀ i, π (σ i) = π i) ∧ x' = x ∘ ⇑σ ∧ y' = y ∘ ⇑σ := by
  obtain ⟨σ, hσ⟩ := exists_perm_of_card_fiber_eq (fun i => (π i, x i, y i))
    (fun i => (π i, x' i, y' i)) (fun b => by rw [← typ_apply, ← typ_apply, h])
  refine ⟨σ, fun i => (congrArg Prod.fst (hσ i)).symm, ?_, ?_⟩
  · funext i; exact congrArg (fun q => q.2.1) (hσ i)
  · funext i; exact congrArg (fun q => q.2.2) (hσ i)

/-! ### The polynomial attached to a linear functional -/

section Poly

/-- Coefficients `f(E_{xy})` of a linear functional on `OpS ι`. -/
def coefF (f : OpS ι →ₗ[ℂ] ℂ) (x y : ι → Fin 2) : ℂ := f (Matrix.single x y (1 : ℂ))

theorem lin_apply (f : OpS ι →ₗ[ℂ] ℂ) (M : OpS ι) :
    f M = ∑ x, ∑ y, coefF f x y * M x y := by
  have hs : ∀ x y, Matrix.single x y (M x y) = M x y • Matrix.single x y (1 : ℂ) := by
    intro x y; rw [Matrix.smul_single]; simp
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  simp only [hs, map_sum, map_smul, smul_eq_mul, coefF]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => mul_comm _ _

/-- The polynomial in the entries of the frames, `v ↦ f(⊗ v_{π i})`. -/
noncomputable def polyF (π : ι → κ) (f : OpS ι →ₗ[ℂ] ℂ) : MvPolynomial (κ × Fin 2 × Fin 2) ℂ :=
  ∑ x, ∑ y, MvPolynomial.monomial (typ π x y) (coefF f x y)

theorem eval_monomial_typ (π : ι → κ) (w : κ × Fin 2 × Fin 2 → ℂ) (x y : ι → Fin 2) (c : ℂ) :
    MvPolynomial.eval w (MvPolynomial.monomial (typ π x y) c) = c * ∏ i, w (π i, x i, y i) := by
  rw [MvPolynomial.eval_monomial, typ, ← Finsupp.prod_finsetSum_index (fun _ => pow_zero _)
    (fun _ _ _ => pow_add _ _ _)]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finsupp.prod_single_index (h := fun n e => w n ^ e) (pow_zero _), pow_one]

theorem eval_polyF (π : ι → κ) (f : OpS ι →ₗ[ℂ] ℂ) (v : κ → Op1) :
    MvPolynomial.eval (fun q => v q.1 q.2.1 q.2.2) (polyF π f) = f (tensOp π v) := by
  rw [lin_apply, polyF]
  simp only [map_sum, eval_monomial_typ, tensOp, Matrix.of_apply]

theorem tensOp_smul (π : ι → κ) (s : κ → ℂ) (v : κ → Op1) :
    tensOp π (fun b => s b • v b) = (∏ i, s (π i)) • tensOp π v := by
  ext x y
  simp [tensOp, Finset.prod_mul_distrib]

/-- The product of the block determinants, as a polynomial in the frame entries. -/
noncomputable def detPoly (κ : Type*) [Fintype κ] : MvPolynomial (κ × Fin 2 × Fin 2) ℂ :=
  ∏ b : κ, (MvPolynomial.X (b, 0, 0) * MvPolynomial.X (b, 1, 1)
    - MvPolynomial.X (b, 0, 1) * MvPolynomial.X (b, 1, 0))

theorem eval_detPoly (w : κ × Fin 2 × Fin 2 → ℂ) :
    MvPolynomial.eval w (detPoly κ) =
      ∏ b : κ, (Matrix.of fun i j : Fin 2 => w (b, i, j)).det := by
  simp [detPoly, Matrix.det_fin_two]

theorem detPoly_ne_zero : detPoly κ ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval fun q : κ × Fin 2 × Fin 2 => if q.2.1 = q.2.2 then (1 : ℂ) else 0) h
  rw [eval_detPoly] at this
  have h1 : (Matrix.of fun i j : Fin 2 => if i = j then (1 : ℂ) else 0) = 1 := by
    ext i j; simp [Matrix.one_apply]
  simp [h1] at this

/-- A functional killing all `SU(2)^κ` frames has zero polynomial (Zariski density, homogeneity). -/
theorem polyF_eq_zero (π : ι → κ) (f : OpS ι →ₗ[ℂ] ℂ)
    (h0 : ∀ u : κ → Op1, (∀ b, SU2 (u b)) → f (tensOp π u) = 0) : polyF π f = 0 := by
  have hSL : ∀ v : κ → Op1, (∀ b, (v b).det = 1) → f (tensOp π v) = 0 := by
    intro v hv
    rw [← eval_polyF]
    exact FormalResearch.FrameFree.Zariski.mvPolynomial_vanish_SL2 (polyF π f)
      (fun u hu => by rw [eval_polyF]; exact h0 u hu) v hv
  have hGL : ∀ v : κ → Op1, (∀ b, (v b).det ≠ 0) → f (tensOp π v) = 0 := by
    intro v hv
    choose s hs using fun b => IsAlgClosed.exists_pow_nat_eq ((v b).det) (two_pos)
    have hs0 : ∀ b, s b ≠ 0 := fun b h => hv b (by rw [← hs b, h]; simp)
    have hdet : ∀ b, ((s b)⁻¹ • v b).det = 1 := fun b => by
      rw [Matrix.det_smul, Fintype.card_fin, ← hs b, ← mul_pow, inv_mul_cancel₀ (hs0 b), one_pow]
    have hv' : v = fun b => s b • ((s b)⁻¹ • v b) := by
      funext b; rw [smul_smul, mul_inv_cancel₀ (hs0 b), one_smul]
    have := hSL (fun b => (s b)⁻¹ • v b) hdet
    conv_lhs => rw [hv', tensOp_smul, map_smul, this, smul_zero]
  have hp : polyF π f * detPoly κ = 0 := by
    refine MvPolynomial.funext fun w => ?_
    rw [map_mul, map_zero, eval_detPoly]
    by_cases hd : ∏ b : κ, (Matrix.of fun i j : Fin 2 => w (b, i, j)).det = 0
    · rw [hd, mul_zero]
    · have hv := hGL (fun b => Matrix.of fun i j : Fin 2 => w (b, i, j))
        (fun b => (Finset.prod_ne_zero_iff.1 hd) b (Finset.mem_univ b))
      rw [← eval_polyF] at hv
      rw [show w = fun q => (fun b : κ => Matrix.of fun i j : Fin 2 => w (b, i, j)) q.1 q.2.1 q.2.2 from
        by funext q; rfl, hv, zero_mul]
  exact (mul_eq_zero.1 hp).resolve_right detPoly_ne_zero

theorem coeff_polyF (π : ι → κ) (f : OpS ι →ₗ[ℂ] ℂ) (m : (κ × Fin 2 × Fin 2) →₀ ℕ) :
    (polyF π f).coeff m =
      ∑ q : (ι → Fin 2) × (ι → Fin 2), if typ π q.1 q.2 = m then coefF f q.1 q.2 else 0 := by
  rw [polyF, MvPolynomial.coeff_sum, Fintype.sum_prod_type' (f := fun x y =>
    if typ π x y = m then coefF f x y else 0)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [MvPolynomial.coeff_sum]
  exact Finset.sum_congr rfl fun y _ => MvPolynomial.coeff_monomial _ _ _

/-- The span of the `SU(2)^κ` frame operators `⊗_i u_{π i}`. -/
def frameSpan (π : ι → κ) : Submodule ℂ (OpS ι) :=
  Submodule.span ℂ {M | ∃ u : κ → Op1, (∀ b, SU2 (u b)) ∧ M = tensOp π u}

/-- A block-permutation invariant matrix pairs to zero with every functional killing the frame
span... (the key step of polarisation). -/
theorem apply_eq_zero_of_comm (π : ι → κ) (f : OpS ι →ₗ[ℂ] ℂ)
    (hf : ∀ u : κ → Op1, (∀ b, SU2 (u b)) → f (tensOp π u) = 0) (Y : OpS ι)
    (hY : ∀ σ : Equiv.Perm ι, (∀ i, π (σ i) = π i) → Y * permOp σ = permOp σ * Y) : f Y = 0 := by
  have hp := polyF_eq_zero π f hf
  have hYinv : ∀ (x y : ι → Fin 2) (σ : Equiv.Perm ι), (∀ i, π (σ i) = π i) →
      Y (x ∘ ⇑σ) (y ∘ ⇑σ) = Y x y := by
    intro x y σ hσ
    have h := congrFun (congrFun (hY σ hσ) x) (y ∘ ⇑σ)
    rw [mul_permOp_apply, permOp_mul_apply, comp_comp_inv] at h
    exact h.symm
  have hcoef : ∀ m, ∑ q : (ι → Fin 2) × (ι → Fin 2),
      (if typ π q.1 q.2 = m then coefF f q.1 q.2 else 0) = 0 := fun m => by
    rw [← coeff_polyF, hp]; simp
  rw [lin_apply, ← Fintype.sum_prod_type' (f := fun x y => coefF f x y * Y x y)]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
    (t := Finset.univ.image fun q : (ι → Fin 2) × (ι → Fin 2) => typ π q.1 q.2)
    (g := fun q => typ π q.1 q.2) (fun q _ => Finset.mem_image_of_mem _ (Finset.mem_univ q))]
  refine Finset.sum_eq_zero fun m hm => ?_
  obtain ⟨q0, _, rfl⟩ := Finset.mem_image.1 hm
  have : ∀ q ∈ Finset.univ.filter (fun q : (ι → Fin 2) × (ι → Fin 2) => typ π q.1 q.2 = typ π q0.1 q0.2),
      coefF f q.1 q.2 * Y q.1 q.2 = coefF f q.1 q.2 * Y q0.1 q0.2 := by
    intro q hq
    obtain ⟨σ, hσ, h1, h2⟩ := exists_perm_of_typ_eq π (Finset.mem_filter.1 hq).2
    rw [h1, h2, hYinv _ _ σ hσ]
  rw [Finset.sum_congr rfl this, ← Finset.sum_mul, Finset.sum_filter, hcoef, zero_mul]

/-- **Polarisation** (`span{g^{⊗m}}` = block-permutation commutant): a matrix commuting with all
block-preserving slot permutations is a linear combination of `SU(2)^κ` frame operators. -/
theorem mem_frameSpan_of_comm (π : ι → κ) (Y : OpS ι)
    (hY : ∀ σ : Equiv.Perm ι, (∀ i, π (σ i) = π i) → Y * permOp σ = permOp σ * Y) :
    Y ∈ frameSpan π := by
  by_contra hn
  obtain ⟨f, hfY, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have hker : ∀ M ∈ frameSpan π, f M = 0 := fun M hM => by
    have := Submodule.mem_map_of_mem (f := f) hM
    rw [hmap] at this; simpa using this
  exact hfY (apply_eq_zero_of_comm π f
    (fun u hu => hker _ (Submodule.subset_span ⟨u, hu, rfl⟩)) Y hY)

end Poly

/-! ### Schur--Weyl duality -/

section SchurWeyl

variable (π : ι → κ)

/-- The span of the block-preserving slot permutation operators. -/
def blockPermSpan : Submodule ℂ (OpS ι) :=
  Submodule.span ℂ {M | ∃ σ : Equiv.Perm ι, (∀ i, π (σ i) = π i) ∧ M = permOp σ}

theorem permOp_mem_blockPermSpan (σ : Equiv.Perm ι) (hσ : ∀ i, π (σ i) = π i) :
    permOp σ ∈ blockPermSpan π :=
  Submodule.subset_span ⟨σ, hσ, rfl⟩

theorem one_mem_blockPermSpan : (1 : OpS ι) ∈ blockPermSpan π := by
  rw [← permOp_one]; exact permOp_mem_blockPermSpan π 1 (fun _ => rfl)

theorem mul_mem_blockPermSpan {a b : OpS ι} (ha : a ∈ blockPermSpan π) (hb : b ∈ blockPermSpan π) :
    a * b ∈ blockPermSpan π := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, hσ, rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨τ, hτ, rfl⟩ := hy
      rw [permOp_mul]
      exact permOp_mem_blockPermSpan π _ (fun i => by rw [Equiv.Perm.mul_apply, hσ, hτ])
    | zero => rw [Matrix.mul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [Matrix.mul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ c hy
  | zero => rw [Matrix.zero_mul]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [Matrix.add_mul]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ c hy

theorem conjTranspose_mem_blockPermSpan {a : OpS ι} (ha : a ∈ blockPermSpan π) :
    aᴴ ∈ blockPermSpan π := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, hσ, rfl⟩ := hx
    rw [permOp_conjTranspose]
    refine permOp_mem_blockPermSpan π _ (fun i => ?_)
    have := hσ (σ⁻¹ i)
    have e : σ (σ⁻¹ i) = i := by simp
    rw [e] at this
    exact this.symm
  | zero => rw [Matrix.conjTranspose_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [Matrix.conjTranspose_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [Matrix.conjTranspose_smul]; exact Submodule.smul_mem _ _ hy

/-- The algebra generated by the block-preserving slot permutations (their span). -/
def blockPermAlg : Subalgebra ℂ (OpS ι) :=
  (blockPermSpan π).toSubalgebra (one_mem_blockPermSpan π) fun _ _ => mul_mem_blockPermSpan π

theorem mem_blockPermAlg {a : OpS ι} : a ∈ blockPermAlg π ↔ a ∈ blockPermSpan π := Iff.rfl

/-- Elements of the permutation span commute with every frame operator `⊗ v_{π i}`. -/
theorem tensOp_commute_of_mem (v : κ → Op1) {a : OpS ι} (ha : a ∈ blockPermSpan π) :
    tensOp π v * a = a * tensOp π v := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, hσ, rfl⟩ := hx
    exact tensOp_commute π v σ hσ
  | zero => simp
  | add y z _ _ hy hz => rw [Matrix.mul_add, Matrix.add_mul, hy, hz]
  | smul c y _ hy => rw [Matrix.mul_smul, Matrix.smul_mul, hy]

/-- **Schur--Weyl duality for qubits with sharing pattern `π`.**  An operator `X` on the qubits `ι`
commutes with `⊗_i u_{π i}` for all `u : κ → SU(2)` iff `X` is a linear combination of slot
permutations preserving the blocks of `π`. -/
theorem commutant_eq_blockPermSpan (X : OpS ι) :
    (∀ u : κ → Op1, (∀ b, SU2 (u b)) → X * tensOp π u = tensOp π u * X) ↔ X ∈ blockPermSpan π := by
  constructor
  · intro hX
    refine bicommutant_mem (blockPermAlg π) (fun b hb => conjTranspose_mem_blockPermSpan π hb) X ?_
    intro Y hY
    have hYσ : ∀ σ : Equiv.Perm ι, (∀ i, π (σ i) = π i) → Y * permOp σ = permOp σ * Y :=
      fun σ hσ => hY _ (permOp_mem_blockPermSpan π σ hσ)
    have key : ∀ Y' ∈ frameSpan π, Y' * X = X * Y' := by
      intro Y' hY'
      induction hY' using Submodule.span_induction with
      | mem M hM =>
        obtain ⟨u, hu, rfl⟩ := hM
        exact (hX u hu).symm
      | zero => simp
      | add y z _ _ hy hz => rw [Matrix.add_mul, Matrix.mul_add, hy, hz]
      | smul c y _ hy => rw [Matrix.smul_mul, Matrix.mul_smul, hy]
    exact key Y (mem_frameSpan_of_comm π Y hYσ)
  · intro hX u _
    exact (tensOp_commute_of_mem π u hX).symm

end SchurWeyl

end FormalResearch.FrameFree.Twirls
