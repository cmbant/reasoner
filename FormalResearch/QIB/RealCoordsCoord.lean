import Mathlib
import FormalResearch.QIB.BlockRealCore
import FormalResearch.QIB.RealCoordsStructure

/-!
# Pure vectors in an isotypic sector (coordinate lemmas)

Namespace `FormalResearch.QIB`.  Claim class: **proved** (no hypothesis, no new axiom).

Let `C ⊆ M_ι(ℂ)` have isotypic coordinates `W` (`M ∈ C ↔ ∃ Y, M = W (⊕ I_{a_l} ⊗ Y_l) Wᴴ`).  A vector
supported on sector `l` is an `a_l × b_l` matrix `Φ` (`lift l Φ`).

* `isMinInv_cyc`: if `Φ = v mᵀ` is a nonzero pure tensor, `C f` is a *minimal* `C`-invariant subspace
  (`f = W (lift l Φ)`).
* `pure_of_comm`: if `P` is a projection in the commutant `C'` with `P C' P` commutative and `P f = f`
  for a vector `f` supported on sector `l`, then its coordinate matrix `Φ` is a pure tensor `v mᵀ`.
  (The `a_l × a_l` carrier operators `⊕ M ⊗ 1` lie in `C'`; the relation
  `(u†u)(w†w) u = (u†u)(w†u) w` for two columns `u, w` of `Φ` follows from commutativity.)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate
open scoped Kronecker ComplexOrder

namespace FormalResearch.QIB

section Coord

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {A B : Λ → Type*}
  [∀ l, Fintype (A l)] [∀ l, DecidableEq (A l)] [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `⊕_l M_l ⊗ 1` (the carrier-side operators, the commutant of `blockOp`). -/
noncomputable def carrOp (B : Λ → Type*) [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]
    (M : ∀ l, Matrix (A l) (A l) ℂ) : Matrix (Idx A B) (Idx A B) ℂ :=
  Matrix.blockDiagonal' fun l => M l ⊗ₖ (1 : Matrix (B l) (B l) ℂ)

theorem carrOp_mul_blockOp (M : ∀ l, Matrix (A l) (A l) ℂ) (X : ∀ l, Matrix (B l) (B l) ℂ) :
    carrOp B M * blockOp A X = blockOp A X * carrOp B M := by
  unfold carrOp blockOp
  rw [← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
  congr 1; funext l
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.one_mul, Matrix.mul_one]

theorem carrOp_mulVec_apply (M : ∀ l, Matrix (A l) (A l) ℂ) (w : Idx A B → ℂ) (l : Λ) (α : A l)
    (b : B l) :
    (carrOp B M *ᵥ w) ⟨l, (α, b)⟩ = ∑ β, M l α β * w ⟨l, (β, b)⟩ := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single l]
  · unfold carrOp
    simp only [Matrix.blockDiagonal'_apply_eq, Matrix.kronecker_apply, Matrix.one_apply, mul_ite,
      mul_one, mul_zero, ite_mul, zero_mul]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.sum_ite_eq Finset.univ b]
    simp
  · intro l' _ hl'
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b' _ => ?_
    unfold carrOp
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hl'), zero_mul]
  · simp

variable (l : Λ)

/-- A vector supported on sector `l`, from its `a_l × b_l` coordinate matrix. -/
def lift (Φ : Matrix (A l) (B l) ℂ) : Idx A B → ℂ := fun i =>
  if h : i.1 = l then Φ (h ▸ i.2.1) (h ▸ i.2.2) else 0

variable {l}

theorem lift_same (Φ : Matrix (A l) (B l) ℂ) (α : A l) (b : B l) :
    lift l Φ ⟨l, (α, b)⟩ = Φ α b := by
  simp [lift]

theorem lift_ne (Φ : Matrix (A l) (B l) ℂ) {l' : Λ} (h : l' ≠ l) (p : A l' × B l') :
    lift l Φ ⟨l', p⟩ = 0 := by
  simp [lift, h]

theorem eq_lift_of_supp (x : Idx A B → ℂ) (h : ∀ l' ≠ l, ∀ p, x ⟨l', p⟩ = 0) :
    x = lift l (Matrix.of fun α b => x ⟨l, (α, b)⟩) := by
  funext ⟨l', α, b⟩
  by_cases hl : l' = l
  · subst hl
    rw [lift_same]; rfl
  · rw [lift_ne _ hl, h l' hl]

theorem lift_injective {Φ Ψ : Matrix (A l) (B l) ℂ} (h : lift l Φ = lift l Ψ) : Φ = Ψ := by
  ext α b
  have := congrFun h ⟨l, (α, b)⟩
  rwa [lift_same, lift_same] at this

theorem lift_add (Φ Ψ : Matrix (A l) (B l) ℂ) : lift l (Φ + Ψ) = lift l Φ + lift l Ψ := by
  funext ⟨l', α, b⟩
  by_cases hl : l' = l
  · subst hl; simp [lift_same]
  · simp [lift_ne _ hl]

theorem lift_smul (c : ℂ) (Φ : Matrix (A l) (B l) ℂ) : lift l (c • Φ) = c • lift l Φ := by
  funext ⟨l', α, b⟩
  by_cases hl : l' = l
  · subst hl; simp [lift_same]
  · simp [lift_ne _ hl]

theorem lift_zero : lift l (0 : Matrix (A l) (B l) ℂ) = 0 := by
  funext ⟨l', α, b⟩
  by_cases hl : l' = l
  · subst hl; simp [lift_same]
  · simp [lift_ne _ hl]

theorem blockOp_mulVec_lift (X : ∀ l, Matrix (B l) (B l) ℂ) (Φ : Matrix (A l) (B l) ℂ) :
    blockOp A X *ᵥ lift l Φ = lift l (Φ * (X l)ᵀ) := by
  funext ⟨l', α, b⟩
  rw [blockOp_mulVec_apply]
  by_cases hl : l' = l
  · subst hl
    rw [lift_same]
    simp only [Matrix.mulVec, dotProduct, slice, lift_same, Matrix.mul_apply, Matrix.transpose_apply]
    refine Finset.sum_congr rfl fun b' _ => ?_
    ring
  · rw [lift_ne _ hl]
    have : slice (lift l Φ) l' α = 0 := by
      funext b'; exact lift_ne _ hl _
    rw [this]; simp

theorem carrOp_mulVec_lift (M : ∀ l, Matrix (A l) (A l) ℂ) (Φ : Matrix (A l) (B l) ℂ) :
    carrOp B M *ᵥ lift l Φ = lift l (M l * Φ) := by
  funext ⟨l', α, b⟩
  rw [carrOp_mulVec_apply]
  by_cases hl : l' = l
  · subst hl
    rw [lift_same, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [lift_same]
  · rw [lift_ne _ hl]
    refine Finset.sum_eq_zero fun β _ => ?_
    rw [lift_ne _ hl, mul_zero]

end Coord


section Cyc

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {A B : Λ → Type*}
  [∀ l, Fintype (A l)] [∀ l, DecidableEq (A l)] [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `C f`, the cyclic `C`-submodule generated by `f`. -/
def cycSub (C : Subalgebra ℂ (Matrix ι ι ℂ)) (f : ι → ℂ) : Submodule ℂ (ι → ℂ) where
  carrier := {v | ∃ c ∈ C, v = c *ᵥ f}
  add_mem' := by
    rintro _ _ ⟨c1, h1, rfl⟩ ⟨c2, h2, rfl⟩
    exact ⟨c1 + c2, add_mem h1 h2, by rw [Matrix.add_mulVec]⟩
  zero_mem' := ⟨0, zero_mem _, by simp⟩
  smul_mem' := by
    rintro c _ ⟨c', h, rfl⟩
    exact ⟨c • c', Subalgebra.smul_mem _ h c, by rw [Matrix.smul_mulVec]⟩

theorem mem_cycSub_self (C : Subalgebra ℂ (Matrix ι ι ℂ)) (f : ι → ℂ) : f ∈ cycSub C f :=
  ⟨1, one_mem _, by simp⟩

theorem cycSub_inv (C : Subalgebra ℂ (Matrix ι ι ℂ)) (f : ι → ℂ) :
    Inv (C : Set (Matrix ι ι ℂ)) (cycSub C f) := by
  rintro c hc _ ⟨c', hc', rfl⟩
  exact ⟨c * c', mul_mem hc hc', by rw [Matrix.mulVec_mulVec]⟩

theorem vecMulVec_mulVec_eq {κ : Type*} [Fintype κ] {μ : Type*} (u : μ → ℂ) (v w : κ → ℂ) :
    Matrix.vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec, Matrix.of_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

section WCoord

variable {W : Matrix ι (Idx A B) ℂ}

theorem coord_back (hW2 : W * Wᴴ = 1) (x : ι → ℂ) : x = W *ᵥ (Wᴴ *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, hW2, Matrix.one_mulVec]

theorem coord_conj_mulVec (hW1 : Wᴴ * W = 1) (X : Matrix (Idx A B) (Idx A B) ℂ) (x : ι → ℂ) :
    Wᴴ *ᵥ ((W * X * Wᴴ) *ᵥ x) = X *ᵥ (Wᴴ *ᵥ x) := by
  have : Wᴴ * (W * X * Wᴴ) = X * Wᴴ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hW1, Matrix.one_mul]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, this]

theorem isMinInv_cyc {C : Subalgebra ℂ (Matrix ι ι ℂ)} (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1)
    (hCW : ∀ M, M ∈ C ↔ ∃ Y : ∀ l, Matrix (B l) (B l) ℂ, M = W * blockOp A Y * Wᴴ)
    {f : ι → ℂ} {l : Λ} {v : A l → ℂ} {m : B l → ℂ} (hv : v ≠ 0) (hm : m ≠ 0)
    (hf : Wᴴ *ᵥ f = lift l (Matrix.vecMulVec v m)) : IsMinInv C (cycSub C f) := by
  have hΦ : ∀ y : B l → ℂ, y ≠ 0 → lift l (Matrix.vecMulVec v y) ≠ 0 := by
    intro y hy h
    obtain ⟨α, hα⟩ := Function.ne_iff.1 hv
    obtain ⟨b, hb⟩ := Function.ne_iff.1 hy
    have := congrFun h ⟨l, (α, b)⟩
    rw [lift_same] at this
    simp only [Matrix.vecMulVec_apply, Pi.zero_apply] at this
    exact mul_ne_zero hα hb (by simpa using this)
  refine ⟨?_, cycSub_inv C f, ?_⟩
  · intro h
    have hf0 : f ∈ (⊥ : Submodule ℂ (ι → ℂ)) := h ▸ mem_cycSub_self C f
    have : f = 0 := by simpa using hf0
    apply hΦ m hm
    rw [← hf, this, Matrix.mulVec_zero]
  · intro S' hle hinv
    by_cases hS : S' = ⊥
    · exact Or.inl hS
    right
    obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    obtain ⟨c, hc, rfl⟩ := hle hsS
    obtain ⟨Y, rfl⟩ := (hCW c).1 hc
    have h1 : Wᴴ *ᵥ ((W * blockOp A Y * Wᴴ) *ᵥ f) =
        lift l (Matrix.vecMulVec v (Y l *ᵥ m)) := by
      rw [coord_conj_mulVec hW1, hf, blockOp_mulVec_lift, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
    have hw : Y l *ᵥ m ≠ 0 := by
      intro h0
      apply hs0
      rw [coord_back hW2 ((W * blockOp A Y * Wᴴ) *ᵥ f), h1, h0]
      have : Matrix.vecMulVec v (0 : B l → ℂ) = 0 := by
        ext i j; simp [Matrix.vecMulVec_apply]
      rw [this, lift_zero, Matrix.mulVec_zero]
    set w : B l → ℂ := Y l *ᵥ m with hwdef
    have hd : star w ⬝ᵥ w ≠ 0 := fun h => hw (dotProduct_star_self_eq_zero.1 h)
    let M0 : Matrix (B l) (B l) ℂ := (star w ⬝ᵥ w)⁻¹ • Matrix.vecMulVec m (star w)
    have hM0 : M0 *ᵥ w = m := by
      show ((star w ⬝ᵥ w)⁻¹ • Matrix.vecMulVec m (star w)) *ᵥ w = m
      rw [Matrix.smul_mulVec, vecMulVec_mulVec_eq, smul_smul, inv_mul_cancel₀ hd, one_smul]
    let X0 : ∀ l', Matrix (B l') (B l') ℂ := Function.update (fun l' => 0) l M0
    have hX0 : X0 l = M0 := by simp [X0]
    have hc' : W * blockOp A X0 * Wᴴ ∈ C := (hCW _).2 ⟨X0, rfl⟩
    have h2 : (W * blockOp A X0 * Wᴴ) *ᵥ ((W * blockOp A Y * Wᴴ) *ᵥ f) = f := by
      rw [coord_back hW2 ((W * blockOp A X0 * Wᴴ) *ᵥ ((W * blockOp A Y * Wᴴ) *ᵥ f)),
        coord_conj_mulVec hW1, h1, blockOp_mulVec_lift, hX0, Matrix.vecMulVec_mul,
        Matrix.vecMul_transpose, hM0, ← hf, ← coord_back hW2]
    have hfS : f ∈ S' := by
      rw [← h2]; exact hinv _ hc' _ hsS
    refine le_antisymm hle ?_
    intro x hx
    obtain ⟨c'', hc'', rfl⟩ := hx
    exact hinv _ hc'' _ hfS

end WCoord

section Pure

variable {W : Matrix ι (Idx A B) ℂ} {l : Λ}

/-- The `a_l × b_l` matrix with column `b0` equal to `x` and all other columns zero. -/
def colEmb (b0 : B l) (x : A l → ℂ) : Matrix (A l) (B l) ℂ :=
  Matrix.vecMulVec x (Pi.single b0 1)

/-- The embedding `x ↦ W (lift (x ⊗ e_{b0}))` of the carrier `ℂ^{a_l}` into `ℂ^ι`. -/
noncomputable def Lc (W : Matrix ι (Idx A B) ℂ) (b0 : B l) (x : A l → ℂ) : ι → ℂ :=
  W *ᵥ lift l (colEmb b0 x)

/-- `W (⊕ M ⊗ 1) Wᴴ`, with `M` on sector `l` and zero elsewhere (lies in `C'`). -/
noncomputable def Dl (W : Matrix ι (Idx A B) ℂ) (l : Λ) (M : Matrix (A l) (A l) ℂ) : Matrix ι ι ℂ :=
  W * carrOp B (Function.update (fun l' => (0 : Matrix (A l') (A l') ℂ)) l M) * Wᴴ

theorem sandwich_mulVec (hW1 : Wᴴ * W = 1) (X : Matrix (Idx A B) (Idx A B) ℂ) (y : Idx A B → ℂ) :
    (W * X * Wᴴ) *ᵥ (W *ᵥ y) = W *ᵥ (X *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  simp only [Matrix.mul_assoc, hW1, Matrix.mul_one]

theorem Lc_smul (b0 : B l) (c : ℂ) (x : A l → ℂ) : Lc W b0 (c • x) = c • Lc W b0 x := by
  unfold Lc
  have : colEmb b0 (c • x) = c • colEmb b0 x := by
    ext α b; simp [colEmb, Matrix.vecMulVec_apply, mul_assoc]
  rw [this, lift_smul, Matrix.mulVec_smul]

theorem Lc_inj (hW1 : Wᴴ * W = 1) (b0 : B l) {x y : A l → ℂ} (h : Lc W b0 x = Lc W b0 y) :
    x = y := by
  unfold Lc at h
  have h1 := congrArg (fun z => Wᴴ *ᵥ z) h
  simp only [Matrix.mulVec_mulVec, hW1, Matrix.one_mulVec] at h1
  have h2 := lift_injective h1
  funext α
  have := congrFun (congrFun h2 α) b0
  simpa [colEmb, Matrix.vecMulVec_apply] using this

theorem Dl_mulVec_Lc (hW1 : Wᴴ * W = 1) (b0 : B l) (M : Matrix (A l) (A l) ℂ) (x : A l → ℂ) :
    Dl (B := B) W l M *ᵥ Lc W b0 x = Lc W b0 (M *ᵥ x) := by
  unfold Dl Lc
  rw [sandwich_mulVec hW1, carrOp_mulVec_lift, Function.update_self]
  unfold colEmb
  rw [Matrix.mul_vecMulVec]

theorem Dl_mem_comm {C : Subalgebra ℂ (Matrix ι ι ℂ)} (hW1 : Wᴴ * W = 1)
    (hCW : ∀ M, M ∈ C ↔ ∃ Y : ∀ l, Matrix (B l) (B l) ℂ, M = W * blockOp A Y * Wᴴ)
    (M : Matrix (A l) (A l) ℂ) : Dl (B := B) W l M ∈ comm C := by
  rw [mem_comm]
  intro c hc
  obtain ⟨Y, rfl⟩ := (hCW c).1 hc
  unfold Dl
  rw [sandwich_mul hW1, sandwich_mul hW1, carrOp_mul_blockOp]

theorem unit_mul_col (b0 b : B l) (Φ : Matrix (A l) (B l) ℂ) :
    Φ * (Matrix.of fun i j : B l => if i = b0 ∧ j = b then (1 : ℂ) else 0)ᵀ =
      colEmb b0 (fun α => Φ α b) := by
  ext α b'
  by_cases h : b' = b0
  · subst h
    simp [Matrix.mul_apply, colEmb, Matrix.vecMulVec_apply]
  · simp [Matrix.mul_apply, colEmb, Matrix.vecMulVec_apply, h]

/-- **Purity.**  Let `P ∈ C'` be such that `P C' P` is commutative, and `f` a vector with `P f = f`
supported on sector `l`, with coordinate matrix `Φ`.  Then `Φ = v mᵀ` is a pure tensor. -/
theorem pure_of_comm {C : Subalgebra ℂ (Matrix ι ι ℂ)} (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1)
    (hCW : ∀ M, M ∈ C ↔ ∃ Y : ∀ l, Matrix (B l) (B l) ℂ, M = W * blockOp A Y * Wᴴ)
    {P : Matrix ι ι ℂ} (hP : P ∈ comm C)
    (hcomm : ∀ Z₁ ∈ comm C, ∀ Z₂ ∈ comm C,
      (P * Z₁ * P) * (P * Z₂ * P) = (P * Z₂ * P) * (P * Z₁ * P))
    {f : ι → ℂ} {Φ : Matrix (A l) (B l) ℂ} (hPf : P *ᵥ f = f)
    (hf : Wᴴ *ᵥ f = lift l Φ) (hf0 : f ≠ 0) :
    ∃ (v : A l → ℂ) (m : B l → ℂ), v ≠ 0 ∧ m ≠ 0 ∧ Φ = Matrix.vecMulVec v m := by
  have hΦ0 : Φ ≠ 0 := by
    intro h; apply hf0
    rw [coord_back hW2 f, hf, h, lift_zero, Matrix.mulVec_zero]
  obtain ⟨α1, b1, h1⟩ : ∃ α b, Φ α b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hΦ0 (by ext α b; exact hcon α b)
  have hf' : f = W *ᵥ lift l Φ := by rw [← hf]; exact coord_back hW2 f
  let col : B l → (A l → ℂ) := fun b α => Φ α b
  have hfix : ∀ b, P *ᵥ Lc W b1 (col b) = Lc W b1 (col b) := by
    intro b
    let Y : ∀ l', Matrix (B l') (B l') ℂ := Function.update (fun l' => (0 : Matrix (B l') (B l') ℂ)) l
      (Matrix.of fun i j : B l => if i = b1 ∧ j = b then (1 : ℂ) else 0)
    have hc : W * blockOp A Y * Wᴴ ∈ C := (hCW _).2 ⟨Y, rfl⟩
    have hcb : (W * blockOp A Y * Wᴴ) *ᵥ f = Lc W b1 (col b) := by
      rw [hf', sandwich_mulVec hW1, blockOp_mulVec_lift]
      unfold Lc
      have hY : Y l = Matrix.of fun i j : B l => if i = b1 ∧ j = b then (1 : ℂ) else 0 := by
        simp [Y]
      rw [hY, unit_mul_col]
    rw [← hcb, Matrix.mulVec_mulVec, ← (mem_comm.1 hP _ hc), ← Matrix.mulVec_mulVec, hPf]
  have hprod : ∀ (X Y : Matrix ι ι ℂ) (x : ι → ℂ), (X * Y) *ᵥ x = X *ᵥ (Y *ᵥ x) :=
    fun X Y x => (Matrix.mulVec_mulVec x X Y).symm
  have hPZP : ∀ (M : Matrix (A l) (A l) ℂ) (x : A l → ℂ), P *ᵥ Lc W b1 x = Lc W b1 x →
      P *ᵥ Lc W b1 (M *ᵥ x) = Lc W b1 (M *ᵥ x) →
      (P * Dl (B := B) W l M * P) *ᵥ Lc W b1 x = Lc W b1 (M *ᵥ x) := by
    intro M x hx hMx
    rw [hprod, hprod, hx, Dl_mulVec_Lc hW1, hMx]
  have hsm : ∀ (c : ℂ) (x : A l → ℂ), P *ᵥ Lc W b1 x = Lc W b1 x →
      P *ᵥ Lc W b1 (c • x) = Lc W b1 (c • x) := by
    intro c x hx
    rw [Lc_smul, Matrix.mulVec_smul, hx]
  have key : ∀ u w : A l → ℂ, P *ᵥ Lc W b1 u = Lc W b1 u → P *ᵥ Lc W b1 w = Lc W b1 w →
      (star u ⬝ᵥ u) • (star w ⬝ᵥ w) • u = (star w ⬝ᵥ u) • (star u ⬝ᵥ u) • w := by
    intro u w hu hw
    have e2u : Matrix.vecMulVec w (star u) *ᵥ u = (star u ⬝ᵥ u) • w := vecMulVec_mulVec_eq _ _ _
    have e1w : Matrix.vecMulVec u (star w) *ᵥ w = (star w ⬝ᵥ w) • u := vecMulVec_mulVec_eq _ _ _
    have e1u : Matrix.vecMulVec u (star w) *ᵥ u = (star w ⬝ᵥ u) • u := vecMulVec_mulVec_eq _ _ _
    have hL := hcomm _ (Dl_mem_comm hW1 hCW (Matrix.vecMulVec u (star w)))
      _ (Dl_mem_comm hW1 hCW (Matrix.vecMulVec w (star u)))
    have hL2 := congrArg (fun Z => Z *ᵥ Lc W b1 u) hL
    have fx2 : P *ᵥ Lc W b1 (Matrix.vecMulVec w (star u) *ᵥ u) =
        Lc W b1 (Matrix.vecMulVec w (star u) *ᵥ u) := by rw [e2u]; exact hsm _ _ hw
    have fx1 : P *ᵥ Lc W b1 (Matrix.vecMulVec u (star w) *ᵥ u) =
        Lc W b1 (Matrix.vecMulVec u (star w) *ᵥ u) := by rw [e1u]; exact hsm _ _ hu
    have fx12 : P *ᵥ Lc W b1 (Matrix.vecMulVec u (star w) *ᵥ (Matrix.vecMulVec w (star u) *ᵥ u)) =
        Lc W b1 (Matrix.vecMulVec u (star w) *ᵥ (Matrix.vecMulVec w (star u) *ᵥ u)) := by
      rw [e2u, Matrix.mulVec_smul, e1w]; exact hsm _ _ (hsm _ _ hu)
    have fx21 : P *ᵥ Lc W b1 (Matrix.vecMulVec w (star u) *ᵥ (Matrix.vecMulVec u (star w) *ᵥ u)) =
        Lc W b1 (Matrix.vecMulVec w (star u) *ᵥ (Matrix.vecMulVec u (star w) *ᵥ u)) := by
      rw [e1u, Matrix.mulVec_smul, e2u]; exact hsm _ _ (hsm _ _ hw)
    rw [hprod (P * Dl (B := B) W l _ * P), hprod (P * Dl (B := B) W l _ * P),
      hPZP _ u hu fx2, hPZP _ _ fx2 fx12, hPZP _ u hu fx1, hPZP _ _ fx1 fx21] at hL2
    have h3 := Lc_inj hW1 b1 hL2
    rw [e2u, Matrix.mulVec_smul, e1w, e1u, Matrix.mulVec_smul, e2u] at h3
    rw [h3, smul_comm]
  have hw0 : col b1 ≠ 0 := by
    intro h
    apply h1
    have := congrFun h α1
    simpa [col] using this
  have hww : star (col b1) ⬝ᵥ col b1 ≠ 0 := fun h => hw0 (dotProduct_star_self_eq_zero.1 h)
  have hΦeq : Φ = Matrix.vecMulVec (col b1)
      (fun b => (star (col b1) ⬝ᵥ col b1)⁻¹ * (star (col b1) ⬝ᵥ col b)) := by
    ext α b
    rw [Matrix.vecMulVec_apply]
    have hb := key (col b) (col b1) (hfix b) (hfix b1)
    by_cases hu : star (col b) ⬝ᵥ col b = 0
    · have h0 : col b = 0 := dotProduct_star_self_eq_zero.1 hu
      have h00 : Φ α b = 0 := by simpa [col] using congrFun h0 α
      rw [h00, h0]; simp
    · have h' : (star (col b1) ⬝ᵥ col b1) • col b = (star (col b1) ⬝ᵥ col b) • col b1 := by
        apply smul_right_injective _ hu
        simp only
        rw [hb, smul_comm]
      have := congrFun h' α
      simp only [Pi.smul_apply, smul_eq_mul] at this
      have h2 : Φ α b = col b α := rfl
      rw [h2]
      field_simp
      linear_combination this
  refine ⟨col b1, _, hw0, ?_, hΦeq⟩
  intro hm
  apply hΦ0
  rw [hΦeq, hm]
  ext; simp [Matrix.vecMulVec_apply]

end Pure

end Cyc

end FormalResearch.QIB
