import Mathlib
import FormalResearch.FrameFree.OddWordsCopies

/-!
# Compressed odd words on `k` copies (Paper P, `prop:oddwords` (i), (ii))

Namespace `FormalResearch.FrameFree.OddWords`.  Claim class: **proved**.

Setting: slots `α × γ` (spin, copy), block pattern `P : α × γ → κ` preserved by every copy permutation
(`hP`; the paper's words are `P = copyPattern γ id`), `Π = symmetrizer α γ`.

* `Acal P`: the complex span of the compressed words `Π P_σ Π`, `σ` block-preserving (`𝒜_k`);
* `oddK P`: the real span of the compressed odd words `Π (i (P_σ - P_σ⁻¹)) Π`
  (the paper's `(i/2)(W - W⁻¹)` up to the real factor `2`);
* `ThetaOddK A`: `⟨(Θψ)^{⊗k}|A|(Θψ)^{⊗k}⟩ = -⟨ψ^{⊗k}|A|ψ^{⊗k}⟩` for every `ψ`.

`oddK_odd` is the "if" half of `prop:oddwords` (i): every element of `oddK P` is Hermitian and `Θ`-odd
(the full equivalence is `OddWordsOddIff.prop_oddwords_i`, which adds the polarization of `OddWordsPolar`).
`exists_odd_of_noncomm` is the "if" half of (ii): if `𝒜_k` is noncommutative then there is a nonzero
Hermitian `Θ`-odd element of `𝒜_k` (the "only if" half and the dimension count are R4, not formalised).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Matrix ComplexConjugate

namespace FormalResearch.FrameFree.OddWords

open FormalResearch.FrameFree.Twirls

variable {α γ κ : Type*} [Fintype α] [DecidableEq α] [Fintype γ] [DecidableEq γ] [Fintype κ]
  [DecidableEq κ] (P : α × γ → κ)

/-- The compressed word `Π P_σ Π`. -/
noncomputable def cWord (s : Equiv.Perm (α × γ)) : OpS (α × γ) :=
  symmetrizer α γ * permOp s * symmetrizer α γ

/-- `𝒜_k`: the complex span of the compressed block-preserving words. -/
noncomputable def Acal : Submodule ℂ (OpS (α × γ)) :=
  Submodule.span ℂ {M | ∃ s : Equiv.Perm (α × γ), (∀ q, P (s q) = P q) ∧ M = cWord s}

/-- Compression `M ↦ Π (i M) Π`, real-linear. -/
noncomputable def compI (α γ : Type*) [Fintype α] [DecidableEq α] [Fintype γ] [DecidableEq γ] :
    OpS (α × γ) →ₗ[ℝ] OpS (α × γ) where
  toFun M := symmetrizer α γ * (Complex.I • M) * symmetrizer α γ
  map_add' M N := by simp [Matrix.mul_add, Matrix.add_mul, smul_add]
  map_smul' r M := by
    simp only [RingHom.id_apply]
    rw [smul_comm Complex.I r M, Matrix.mul_smul, Matrix.smul_mul]

/-- The real span of the compressed odd words `Π (i (P_σ - P_σ⁻¹)) Π`. -/
noncomputable def oddK : Submodule ℝ (OpS (α × γ)) := (sSkew P).map (compI α γ)

/-- `Θ`-oddness on the product vectors `ψ^{⊗k}`. -/
def ThetaOddK (A : OpS (α × γ)) : Prop :=
  ∀ ψ : (α → Fin 2) → ℂ, ev A (kronVec γ (thetaN ψ)) = - ev A (kronVec γ ψ)

theorem oddK_eq_span :
    oddK P = Submodule.span ℝ {M | ∃ s : Equiv.Perm (α × γ), (∀ q, P (s q) = P q) ∧
      M = symmetrizer α γ * (Complex.I • (permOp s - permOp s⁻¹)) * symmetrizer α γ} := by
  rw [oddK, sSkew, Submodule.map_span]
  congr 1
  ext M
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩; exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩; exact ⟨_, ⟨s, hs, rfl⟩, rfl⟩

theorem conjTranspose_of_map_conj {X : OpS (α × γ)} (h : X.map conj = X) : Xᴴ = Xᵀ := by
  ext x y
  have := congrFun (congrFun h y) x
  simp only [Matrix.map_apply] at this
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Complex.star_def, this]

theorem symmetrizer_conjTranspose (hP : ∀ (c : Equiv.Perm γ) q, P (copyPerm (α := α) c q) = P q) :
    (symmetrizer α γ)ᴴ = symmetrizer α γ := by
  have h1 : (symmetrizer α γ).map conj = symmetrizer α γ :=
    rPerm_map_conj (symmetrizer_mem hP)
  rw [conjTranspose_of_map_conj h1, symmetrizer_transpose]

variable {P}

theorem ev_cmp (hP : ∀ (c : Equiv.Perm γ) q, P (copyPerm (α := α) c q) = P q) (M : OpS (α × γ))
    (v : (α × γ → Fin 2) → ℂ) :
    ev (symmetrizer α γ * M * symmetrizer α γ) v = ev M (symmetrizer α γ *ᵥ v) := by
  unfold ev
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← symmetrizer_conjTranspose P hP, ← Matrix.star_mulVec]
  simp only [symmetrizer_conjTranspose P hP]

theorem odd_gen_herm (hP : ∀ (c : Equiv.Perm γ) q, P (copyPerm (α := α) c q) = P q)
    (s : Equiv.Perm (α × γ)) :
    (symmetrizer α γ * (Complex.I • (permOp s - permOp s⁻¹)) * symmetrizer α γ)ᴴ =
      symmetrizer α γ * (Complex.I • (permOp s - permOp s⁻¹)) * symmetrizer α γ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, symmetrizer_conjTranspose P hP,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, permOp_conjTranspose, permOp_conjTranspose,
    inv_inv, Matrix.mul_assoc]
  congr 2
  rw [Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub]

theorem odd_gen_theta (hP : ∀ (c : Equiv.Perm γ) q, P (copyPerm (α := α) c q) = P q)
    (s : Equiv.Perm (α × γ)) :
    ThetaOddK (symmetrizer α γ * (Complex.I • (permOp s - permOp s⁻¹)) * symmetrizer α γ) := by
  intro ψ
  rw [ev_cmp hP, ev_cmp hP, symmetrizer_mulVec_kronVec, symmetrizer_mulVec_kronVec,
    ← thetaN_kronVec, ev_smul, ev_smul, ev_sub, ev_sub, ev_permOp_thetaN, ev_permOp_thetaN]
  have h1 : ev (permOp s⁻¹) (kronVec γ ψ) = conj (ev (permOp s) (kronVec γ ψ)) := by
    rw [conj_ev, permOp_conjTranspose]
  rw [h1, Complex.conj_conj]
  ring

theorem real_smul_eq' (r : ℝ) (X : OpS (α × γ)) : r • X = (r : ℂ) • X := by
  ext x y; simp [Complex.real_smul]

theorem ThetaOddK.add {A B : OpS (α × γ)} (hA : ThetaOddK A) (hB : ThetaOddK B) : ThetaOddK (A + B) := by
  intro ψ; rw [ev_add, ev_add, hA ψ, hB ψ]; ring

theorem ThetaOddK.real_smul {A : OpS (α × γ)} (hA : ThetaOddK A) (r : ℝ) : ThetaOddK (r • A) := by
  intro ψ; rw [real_smul_eq', ev_smul, ev_smul, hA ψ]; ring

theorem ThetaOddK.zero : ThetaOddK (0 : OpS (α × γ)) := by
  intro ψ; rw [ev_zero, ev_zero]; ring

/-- **Paper P, `prop:oddwords` (i), "if" half.**  Every real combination of compressed odd words is
Hermitian and `Θ`-odd on the product vectors `ψ^{⊗k}`. -/
theorem oddK_odd (hP : ∀ (c : Equiv.Perm γ) q, P (copyPerm (α := α) c q) = P q) {A : OpS (α × γ)}
    (hA : A ∈ oddK P) : Aᴴ = A ∧ ThetaOddK A := by
  rw [oddK_eq_span] at hA
  induction hA using Submodule.span_induction with
  | mem M hM =>
    obtain ⟨s, -, rfl⟩ := hM
    exact ⟨odd_gen_herm hP s, odd_gen_theta hP s⟩
  | zero => exact ⟨by simp, ThetaOddK.zero⟩
  | add x y _ _ hx hy => exact ⟨by rw [Matrix.conjTranspose_add, hx.1, hy.1], hx.2.add hy.2⟩
  | smul r x _ hx =>
    exact ⟨by rw [Matrix.conjTranspose_smul, star_trivial, hx.1], hx.2.real_smul r⟩

theorem cmp_mem_Acal {Y : OpS (α × γ)} (hY : Y ∈ rPerm P) :
    symmetrizer α γ * Y * symmetrizer α γ ∈ Acal P := by
  induction hY using Submodule.span_induction with
  | mem M hM =>
    obtain ⟨s, hs, rfl⟩ := hM
    exact Submodule.subset_span ⟨s, hs, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [real_smul_eq', Matrix.mul_smul, Matrix.smul_mul]
    exact Submodule.smul_mem _ _ hx

/-- Real compressions are symmetric unless there is a nonzero Hermitian `Θ`-odd element. -/
theorem cmp_symm_of_no_odd (hP : ∀ (c : Equiv.Perm γ) q, P (copyPerm (α := α) c q) = P q)
    (hno : ∀ A ∈ Acal P, Aᴴ = A → ThetaOddK A → A = 0) {Y : OpS (α × γ)} (hY : Y ∈ rPerm P) :
    (symmetrizer α γ * Y * symmetrizer α γ)ᵀ = symmetrizer α γ * Y * symmetrizer α γ := by
  have hW : compI α γ (Y - Yᵀ) ∈ oddK P := Submodule.mem_map_of_mem (rPerm_sub_transpose hY)
  have hWo := oddK_odd hP hW
  have hWe : compI α γ (Y - Yᵀ) = Complex.I •
      (symmetrizer α γ * Y * symmetrizer α γ - symmetrizer α γ * Yᵀ * symmetrizer α γ) := by
    show symmetrizer α γ * (Complex.I • (Y - Yᵀ)) * symmetrizer α γ = _
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
  have hWA : compI α γ (Y - Yᵀ) ∈ Acal P := by
    rw [hWe]
    exact Submodule.smul_mem _ _ (sub_mem (cmp_mem_Acal hY) (cmp_mem_Acal (rPerm_transpose hY)))
  have h0 := hno _ hWA hWo.1 hWo.2
  rw [hWe] at h0
  have h1 : symmetrizer α γ * Y * symmetrizer α γ - symmetrizer α γ * Yᵀ * symmetrizer α γ = 0 := by
    have := smul_eq_zero.1 h0
    exact this.resolve_left Complex.I_ne_zero
  rw [Matrix.transpose_mul, Matrix.transpose_mul, symmetrizer_transpose]
  simp only [Matrix.mul_assoc] at h1 ⊢
  exact (sub_eq_zero.1 h1).symm

theorem Acal_comm_of_no_odd (hP : ∀ (c : Equiv.Perm γ) q, P (copyPerm (α := α) c q) = P q)
    (hno : ∀ A ∈ Acal P, Aᴴ = A → ThetaOddK A → A = 0) {A B : OpS (α × γ)} (hA : A ∈ Acal P)
    (hB : B ∈ Acal P) : A * B = B * A := by
  have hsym : ∀ s : Equiv.Perm (α × γ), (∀ q, P (s q) = P q) → (cWord s)ᵀ = cWord s := fun s hs =>
    cmp_symm_of_no_odd hP hno (Submodule.subset_span ⟨s, hs, rfl⟩)
  have hgen : ∀ s t : Equiv.Perm (α × γ), (∀ q, P (s q) = P q) → (∀ q, P (t q) = P q) →
      cWord s * cWord t = cWord t * cWord s := by
    intro s t hs ht
    have hY : permOp s * (symmetrizer α γ * symmetrizer α γ) * permOp t ∈ rPerm P :=
      rPerm_mul (rPerm_mul (Submodule.subset_span ⟨s, hs, rfl⟩)
        (rPerm_mul (symmetrizer_mem hP) (symmetrizer_mem hP))) (Submodule.subset_span ⟨t, ht, rfl⟩)
    have h1 := cmp_symm_of_no_odd hP hno hY
    have e : cWord s * cWord t =
        symmetrizer α γ * (permOp s * (symmetrizer α γ * symmetrizer α γ) * permOp t) *
          symmetrizer α γ := by
      simp only [cWord, Matrix.mul_assoc]
    rw [← e] at h1
    calc cWord s * cWord t = (cWord s * cWord t)ᵀ := h1.symm
      _ = cWord t * cWord s := by rw [Matrix.transpose_mul, hsym s hs, hsym t ht]
  induction hA using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨s, hs, rfl⟩ := ha
    induction hB using Submodule.span_induction with
    | mem b hb => obtain ⟨t, ht, rfl⟩ := hb; exact hgen s t hs ht
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul, hx, hy]
    | smul c x _ hx => rw [Matrix.mul_smul, Matrix.smul_mul, hx]
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.mul_add, hx, hy]
  | smul c x _ hx => rw [Matrix.smul_mul, Matrix.mul_smul, hx]

/-- **Paper P, `prop:oddwords` (ii), "if" half.**  If `𝒜_k` is noncommutative, there is a nonzero
Hermitian `Θ`-odd element of `𝒜_k` (a nonzero odd invariant). -/
theorem exists_odd_of_noncomm (hP : ∀ (c : Equiv.Perm γ) q, P (copyPerm (α := α) c q) = P q)
    (h : ∃ A ∈ Acal P, ∃ B ∈ Acal P, A * B ≠ B * A) :
    ∃ A ∈ Acal P, Aᴴ = A ∧ ThetaOddK A ∧ A ≠ 0 := by
  by_contra hno
  push Not at hno
  obtain ⟨A, hA, B, hB, hne⟩ := h
  exact hne (Acal_comm_of_no_odd hP (fun A hA h1 h2 => hno A hA h1 h2) hA hB)

end FormalResearch.FrameFree.OddWords
