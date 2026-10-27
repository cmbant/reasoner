import Mathlib
import FormalResearch.FrameFree.Foundations
import FormalResearch.FrameFree.OneCopy
import FormalResearch.FrameFree.TwirlsTwirl

/-!
# Odd invariants of one copy (Paper P, `prop:oddwords` (iii))

Namespace `FormalResearch.FrameFree.Twirls`.  Claim class: **proved**.

`thetaOdd_iff_mem_oddSpan`: for a sharing pattern `π` (`π` constant = common frame), a Hermitian `A`
commuting with `K_π` (equivalently `A ∈ blockPermSpan π`, `commutant_eq_blockPermSpan`) satisfies
`⟨Θψ|A Θψ⟩ = -⟨ψ|Aψ⟩` for all `ψ` iff `A` is a real combination of the odd words `i (P_σ - P_σ⁻¹)`,
`σ` block-preserving.  Route: split `A = X₁ + i X₂` with `X_j` in the real span of the permutations
(`exists_real_split`), `Θ` acts as complex conjugation on real permutation combinations
(`realPerm_theta`), so oddness kills the symmetric part `X₁` (`quad_zero`) and `X₂` is real antisymmetric
(`realPerm_sub_transpose`).  Not formalised: `(i)`, `(ii)` (compressed symmetric-subspace algebras) and the
real-type multiplicity-space dimension count `∑_j C(g_j, 2)` of `(iii)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate
open FormalResearch.FrameFree.NQubit (Ψ Θ)

namespace FormalResearch.FrameFree.Twirls

section Odd

variable {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The odd word `i (P_σ - P_σ⁻¹)` as a matrix. -/
noncomputable def oddMat (σ : Equiv.Perm (Fin n)) : OpS (Fin n) :=
  Complex.I • (permOp σ - permOp σ⁻¹)

/-- Real span of the block-preserving slot permutations. -/
noncomputable def realPerm (π : Fin n → κ) : Submodule ℝ (OpS (Fin n)) :=
  Submodule.span ℝ {M | ∃ σ : Equiv.Perm (Fin n), (∀ i, π (σ i) = π i) ∧ M = permOp σ}

/-- Real span of the odd words of block-preserving permutations. -/
noncomputable def oddSpan (π : Fin n → κ) : Submodule ℝ (OpS (Fin n)) :=
  Submodule.span ℝ {M | ∃ σ : Equiv.Perm (Fin n), (∀ i, π (σ i) = π i) ∧ M = oddMat σ}

theorem permOp_mulVec (σ : Equiv.Perm (Fin n)) (ψ : Ψ n) :
    permOp σ *ᵥ ψ = OneCopy.permN σ ψ := by
  funext x
  simp [permOp, Matrix.mulVec, dotProduct, OneCopy.permN]

theorem oddMat_mulVec (σ : Equiv.Perm (Fin n)) (ψ : Ψ n) :
    oddMat σ *ᵥ ψ = OneCopy.oddOp σ ψ := by
  rw [oddMat, OneCopy.oddOp, Matrix.smul_mulVec, Matrix.sub_mulVec, permOp_mulVec, permOp_mulVec]

theorem permOp_transpose (σ : Equiv.Perm (Fin n)) : (permOp σ)ᵀ = permOp σ⁻¹ := by
  ext x y
  have h := congrFun (congrFun (permOp_conjTranspose σ) x) y
  have h2 := congrFun (congrFun (permOp_map_conj σ) y) x
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def] at h h2
  simp only [Matrix.transpose_apply]
  rw [← h, h2]

theorem inv_block (π : Fin n → κ) (σ : Equiv.Perm (Fin n)) (hσ : ∀ i, π (σ i) = π i) (i : Fin n) :
    π (σ⁻¹ i) = π i := by
  have := hσ (σ⁻¹ i)
  simpa using this.symm

theorem real_smul_eq (r : ℝ) (X : OpS (Fin n)) : r • X = (r : ℂ) • X := by
  ext x y; simp [Complex.real_smul]

theorem ip_mulVec_sum (M : OpS (Fin n)) (ψ : Ψ n) :
    NQubit.ip ψ (M *ᵥ ψ) = ∑ x, ∑ y, conj (ψ x) * (M x y * ψ y) := by
  simp [NQubit.ip, Matrix.mulVec, dotProduct, Finset.mul_sum]

theorem conj_ip_mulVec (M : OpS (Fin n)) (ψ : Ψ n) :
    conj (NQubit.ip ψ (M *ᵥ ψ)) = NQubit.ip ψ (Mᴴ *ᵥ ψ) := by
  rw [ip_mulVec_sum, ip_mulVec_sum, map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [map_mul, Complex.conj_conj, Matrix.conjTranspose_apply, Complex.star_def]
  ring

theorem ip_mulVec_add (M N : OpS (Fin n)) (ψ : Ψ n) :
    NQubit.ip ψ ((M + N) *ᵥ ψ) = NQubit.ip ψ (M *ᵥ ψ) + NQubit.ip ψ (N *ᵥ ψ) := by
  simp only [ip_mulVec_sum, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem ip_mulVec_smul (c : ℂ) (M : OpS (Fin n)) (ψ : Ψ n) :
    NQubit.ip ψ ((c • M) *ᵥ ψ) = c * NQubit.ip ψ (M *ᵥ ψ) := by
  simp only [ip_mulVec_sum, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem ip_mulVec_sub (M N : OpS (Fin n)) (ψ : Ψ n) :
    NQubit.ip ψ ((M - N) *ᵥ ψ) = NQubit.ip ψ (M *ᵥ ψ) - NQubit.ip ψ (N *ᵥ ψ) := by
  simp only [ip_mulVec_sum, Matrix.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem ip_mulVec_zero (ψ : Ψ n) : NQubit.ip ψ ((0 : OpS (Fin n)) *ᵥ ψ) = 0 := by
  rw [Matrix.zero_mulVec]; simp [NQubit.ip]

/-- `⟨Θψ|P_σ Θψ⟩ = conj ⟨ψ|P_σ ψ⟩`. -/
theorem ip_theta_permOp (σ : Equiv.Perm (Fin n)) (ψ : Ψ n) :
    NQubit.ip (Θ ψ) (permOp σ *ᵥ Θ ψ) = conj (NQubit.ip ψ (permOp σ *ᵥ ψ)) := by
  rw [permOp_mulVec, permOp_mulVec, ← OneCopy.Θ_permN, NQubit.ip_Θ_Θ]

/-- `Θ`-odd observables, in matrix form. -/
def ThetaOdd (A : OpS (Fin n)) : Prop :=
  ∀ ψ : Ψ n, NQubit.ip (Θ ψ) (A *ᵥ Θ ψ) = - NQubit.ip ψ (A *ᵥ ψ)


/-- Real span of `P_σ - P_σ⁻¹` over block-preserving `σ`. -/
noncomputable def skewSpan (π : Fin n → κ) : Submodule ℝ (OpS (Fin n)) :=
  Submodule.span ℝ {M | ∃ σ : Equiv.Perm (Fin n), (∀ i, π (σ i) = π i) ∧ M = permOp σ - permOp σ⁻¹}

section RealPerm
variable (π : Fin n → κ)

theorem realPerm_map_conj {X : OpS (Fin n)} (hX : X ∈ realPerm π) : X.map conj = X := by
  induction hX using Submodule.span_induction with
  | mem x hx => obtain ⟨σ, -, rfl⟩ := hx; exact permOp_map_conj σ
  | zero => ext x y; simp
  | add x y _ _ hx hy =>
    ext a b
    have h1 := congrFun (congrFun hx a) b
    have h2 := congrFun (congrFun hy a) b
    simp only [Matrix.map_apply, Matrix.add_apply, map_add] at h1 h2 ⊢
    rw [h1, h2]
  | smul r x _ hx =>
    ext a b
    have h1 := congrFun (congrFun hx a) b
    simp only [Matrix.map_apply] at h1
    simp only [Matrix.map_apply, Matrix.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, h1]

theorem realPerm_transpose {X : OpS (Fin n)} (hX : X ∈ realPerm π) : Xᵀ ∈ realPerm π := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, hσ, rfl⟩ := hx
    rw [permOp_transpose]
    exact Submodule.subset_span ⟨σ⁻¹, inv_block π σ hσ, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.transpose_add]; exact add_mem hx hy
  | smul r x _ hx => rw [Matrix.transpose_smul]; exact Submodule.smul_mem _ r hx

theorem realPerm_theta {X : OpS (Fin n)} (hX : X ∈ realPerm π) (ψ : Ψ n) :
    NQubit.ip (Θ ψ) (X *ᵥ Θ ψ) = conj (NQubit.ip ψ (X *ᵥ ψ)) := by
  induction hX using Submodule.span_induction with
  | mem x hx => obtain ⟨σ, -, rfl⟩ := hx; exact ip_theta_permOp σ ψ
  | zero => rw [ip_mulVec_zero, ip_mulVec_zero]; simp
  | add x y _ _ hx hy => rw [ip_mulVec_add, ip_mulVec_add, hx, hy, map_add]
  | smul r x _ hx =>
    rw [real_smul_eq, ip_mulVec_smul, ip_mulVec_smul, hx, map_mul, Complex.conj_ofReal]

theorem realPerm_sub_transpose {X : OpS (Fin n)} (hX : X ∈ realPerm π) : X - Xᵀ ∈ skewSpan π := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, hσ, rfl⟩ := hx
    rw [permOp_transpose]
    exact Submodule.subset_span ⟨σ, hσ, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    have : x + y - (x + y)ᵀ = (x - xᵀ) + (y - yᵀ) := by rw [Matrix.transpose_add]; abel
    rw [this]; exact add_mem hx hy
  | smul r x _ hx =>
    have : r • x - (r • x)ᵀ = r • (x - xᵀ) := by rw [Matrix.transpose_smul, smul_sub]
    rw [this]; exact Submodule.smul_mem _ r hx

theorem I_smul_mem_oddSpan {X : OpS (Fin n)} (hX : X ∈ skewSpan π) :
    Complex.I • X ∈ oddSpan π := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, hσ, rfl⟩ := hx
    exact Submodule.subset_span ⟨σ, hσ, rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ r hx

theorem exists_real_split {A : OpS (Fin n)} (hA : A ∈ blockPermSpan π) :
    ∃ X1 ∈ realPerm π, ∃ X2 ∈ realPerm π, A = X1 + Complex.I • X2 := by
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, hσ, rfl⟩ := hx
    exact ⟨permOp σ, Submodule.subset_span ⟨σ, hσ, rfl⟩, 0, zero_mem _, by simp⟩
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a1, ha1, a2, ha2, rfl⟩ := hx
    obtain ⟨b1, hb1, b2, hb2, rfl⟩ := hy
    refine ⟨a1 + b1, add_mem ha1 hb1, a2 + b2, add_mem ha2 hb2, ?_⟩
    rw [smul_add]; abel
  | smul c x _ hx =>
    obtain ⟨a1, ha1, a2, ha2, rfl⟩ := hx
    refine ⟨c.re • a1 - c.im • a2, sub_mem (Submodule.smul_mem _ _ ha1) (Submodule.smul_mem _ _ ha2),
      c.im • a1 + c.re • a2, add_mem (Submodule.smul_mem _ _ ha1) (Submodule.smul_mem _ _ ha2), ?_⟩
    ext a b
    have key : c * (a1 a b + Complex.I * a2 a b)
        = c.re • a1 a b - c.im • a2 a b + Complex.I * (c.im • a1 a b + c.re • a2 a b) := by
      simp only [Complex.real_smul]
      apply Complex.ext <;> simp <;> ring
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul, Complex.real_smul]
    simp only [Complex.real_smul] at key
    linear_combination key

end RealPerm


theorem conjTranspose_of_real {X : OpS (Fin n)} (h : X.map conj = X) : Xᴴ = Xᵀ := by
  ext x y
  have := congrFun (congrFun h y) x
  simp only [Matrix.map_apply] at this
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Complex.star_def, this]

theorem real_sep {U V W Z : OpS (Fin n)} (hU : U.map conj = U) (hV : V.map conj = V)
    (hW : W.map conj = W) (hZ : Z.map conj = Z) (h : U + Complex.I • V = W + Complex.I • Z) :
    U = W ∧ V = Z := by
  have key : ∀ a b : ℂ, conj a = a → conj b = b → ∀ c d : ℂ, conj c = c → conj d = d →
      a + Complex.I * b = c + Complex.I * d → a = c ∧ b = d := by
    intro a b ha hb c d hc hd hab
    have ha' := Complex.conj_eq_iff_im.1 ha
    have hb' := Complex.conj_eq_iff_im.1 hb
    have hc' := Complex.conj_eq_iff_im.1 hc
    have hd' := Complex.conj_eq_iff_im.1 hd
    have h1 := congrArg Complex.re hab
    have h2 := congrArg Complex.im hab
    simp [ha', hb', hc', hd'] at h1 h2
    exact ⟨Complex.ext h1 (by simp [ha', hc']), Complex.ext h2 (by simp [hb', hd'])⟩
  have ent : ∀ (M : OpS (Fin n)), M.map conj = M → ∀ a b, conj (M a b) = M a b :=
    fun M hM a b => by simpa using congrFun (congrFun hM a) b
  constructor <;> ext a b <;>
  · have := key _ _ (ent U hU a b) (ent V hV a b) _ _ (ent W hW a b) (ent Z hZ a b)
      (by simpa using congrFun (congrFun h a) b)
    simp [this]

theorem quad_zero {X : OpS (Fin n)} (hX : Xᵀ = X) (h : ∀ ψ : Ψ n, NQubit.ip ψ (X *ᵥ ψ) = 0) :
    X = 0 := by
  ext x y
  have hs : X y x = X x y := by simpa using congrFun (congrFun hX x) y
  have hxx : ∀ z, X z z = 0 := by
    intro z
    have := h (fun w => if w = z then 1 else 0)
    simpa [ip_mulVec_sum] using this
  by_cases hxy : x = y
  · subst hxy; simpa using hxx x
  · have := h (fun w => (if w = x then 1 else 0) + (if w = y then 1 else 0))
    simp only [ip_mulVec_sum] at this
    simp [mul_add, add_mul, Finset.sum_add_distrib, hxx, hs] at this
    simpa using this

theorem thetaOdd_oddMat (σ : Equiv.Perm (Fin n)) : ThetaOdd (oddMat σ) := by
  intro ψ
  have hb : NQubit.ip ψ (permOp σ⁻¹ *ᵥ ψ) = conj (NQubit.ip ψ (permOp σ *ᵥ ψ)) := by
    rw [conj_ip_mulVec, permOp_conjTranspose]
  have hb' : NQubit.ip (Θ ψ) (permOp σ⁻¹ *ᵥ Θ ψ) = conj (NQubit.ip ψ (permOp σ⁻¹ *ᵥ ψ)) :=
    ip_theta_permOp _ _
  rw [oddMat, ip_mulVec_smul, ip_mulVec_smul, ip_mulVec_sub, ip_mulVec_sub, ip_theta_permOp, hb',
    hb, Complex.conj_conj]
  ring

theorem ThetaOdd.zero : ThetaOdd (0 : OpS (Fin n)) := by
  intro ψ; rw [ip_mulVec_zero, ip_mulVec_zero]; simp

theorem ThetaOdd.add {A B : OpS (Fin n)} (hA : ThetaOdd A) (hB : ThetaOdd B) : ThetaOdd (A + B) := by
  intro ψ
  rw [ip_mulVec_add, ip_mulVec_add, hA ψ, hB ψ]
  ring

theorem ThetaOdd.real_smul {A : OpS (Fin n)} (hA : ThetaOdd A) (r : ℝ) : ThetaOdd (r • A) := by
  intro ψ
  rw [real_smul_eq, ip_mulVec_smul, ip_mulVec_smul, hA ψ]
  ring

/-- `prop:oddwords` (iii), easy direction: real combinations of odd words are `Θ`-odd. -/
theorem thetaOdd_of_mem_oddSpan (π : Fin n → κ) {A : OpS (Fin n)} (hA : A ∈ oddSpan π) :
    ThetaOdd A := by
  induction hA using Submodule.span_induction with
  | mem x hx => obtain ⟨σ, -, rfl⟩ := hx; exact thetaOdd_oddMat σ
  | zero => exact ThetaOdd.zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul r x _ hx => exact hx.real_smul r


theorem ip_mulVec_neg (M : OpS (Fin n)) (ψ : Ψ n) :
    NQubit.ip ψ ((-M) *ᵥ ψ) = - NQubit.ip ψ (M *ᵥ ψ) := by
  have := ip_mulVec_smul (-1) M ψ
  simpa using this

/-- **`prop:oddwords` (iii)** (proved).  For one copy with sharing pattern `π` (block frames
`u_{π i}`; `π` constant is the common frame), a Hermitian observable `A` commuting with `K_π`
(Schur-Weyl: `A` in the span of the block-preserving slot permutations) is `Θ`-odd,
`⟨Θψ|A Θψ⟩ = -⟨ψ|Aψ⟩` for all `ψ`, iff `A` is a real combination of the odd words
`i (P_σ - P_σ⁻¹)`, `σ` block-preserving. -/
theorem thetaOdd_iff_mem_oddSpan (π : Fin n → κ) {A : OpS (Fin n)} (hA : A ∈ blockPermSpan π)
    (hH : Aᴴ = A) : ThetaOdd A ↔ A ∈ oddSpan π := by
  refine ⟨fun hT => ?_, thetaOdd_of_mem_oddSpan π⟩
  obtain ⟨X1, h1, X2, h2, rfl⟩ := exists_real_split π hA
  have c1 := realPerm_map_conj π h1
  have c2 := realPerm_map_conj π h2
  have t1 : (X1ᵀ).map conj = X1ᵀ := by
    have := congrArg Matrix.transpose c1; simpa [Matrix.transpose_map] using this
  have t2 : ((-X2)ᵀ).map conj = (-X2)ᵀ := by
    have := congrArg Matrix.transpose c2; ext a b
    have e := congrFun (congrFun c2 b) a
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.neg_apply, map_neg] at e ⊢
    rw [e]
  have hH' : X1ᵀ + Complex.I • (-X2)ᵀ = X1 + Complex.I • X2 := by
    rw [← hH, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, conjTranspose_of_real c1,
      conjTranspose_of_real c2, Complex.star_def, Complex.conj_I, Matrix.transpose_neg]
    simp only [neg_smul, smul_neg]
  obtain ⟨e1, e2⟩ := real_sep t1 t2 c1 c2 hH'
  -- e1 : X1ᵀ = X1, e2 : (-X2)ᵀ = X2
  have e2' : X2ᵀ = -X2 := by
    have := congrArg Neg.neg e2
    rw [Matrix.transpose_neg, neg_neg] at this
    exact this
  have hX1 : X1 = 0 := by
    refine quad_zero e1 fun ψ => ?_
    have hθ := hT ψ
    rw [ip_mulVec_add, ip_mulVec_add, ip_mulVec_smul, ip_mulVec_smul,
      realPerm_theta π h1, realPerm_theta π h2] at hθ
    have ca : conj (NQubit.ip ψ (X1 *ᵥ ψ)) = NQubit.ip ψ (X1 *ᵥ ψ) := by
      rw [conj_ip_mulVec, conjTranspose_of_real c1, e1]
    have cb : conj (NQubit.ip ψ (X2 *ᵥ ψ)) = - NQubit.ip ψ (X2 *ᵥ ψ) := by
      rw [conj_ip_mulVec, conjTranspose_of_real c2, e2', ip_mulVec_neg]
    rw [ca, cb] at hθ
    have : (2 : ℂ) * NQubit.ip ψ (X1 *ᵥ ψ) = 0 := by linear_combination hθ
    simpa using this
  subst hX1
  have hsk : X2 ∈ skewSpan π := by
    have h := realPerm_sub_transpose π h2
    have := Submodule.smul_mem _ (1 / 2 : ℝ) h
    rw [e2'] at this
    have e : (1 / 2 : ℝ) • (X2 - -X2) = X2 := by
      rw [real_smul_eq, sub_neg_eq_add, ← two_smul ℂ X2, smul_smul]
      norm_num
    rwa [e] at this
  simpa using I_smul_mem_oddSpan π hsk

end Odd
end FormalResearch.FrameFree.Twirls
