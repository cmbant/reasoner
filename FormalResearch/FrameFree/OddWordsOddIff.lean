import Mathlib
import FormalResearch.FrameFree.OddWordsCompressed
import FormalResearch.FrameFree.OddWordsPolar

/-!
# `prop:oddwords` (i): Hermitian `Θ`-odd elements of `𝒜_k` are the real combinations of compressed odd words

Namespace `FormalResearch.FrameFree.OddWords`.  Claim class: **proved**.

`prop_oddwords_i`: for `A` in `Acal P` (the paper's `𝒜_k`, the span of compressed words) with `P` a block
pattern preserved by the copy permutations, `A` is Hermitian and `Θ`-odd on all `ψ^{⊗k}` iff
`A ∈ oddK P`, the real span of the compressed odd words `Π (i (P_σ - P_σ⁻¹)) Π`.

Route: `A = Z₁ + i Z₂` with `Z_j = Π Y_j Π` real (`Y_j` real permutation combinations);
Hermiticity makes `Z₁` symmetric and `Z₂` antisymmetric; `Θ` acts as complex conjugation on `ev Z_j`
(`ev_permOp_thetaN`), so oddness forces `⟨ψ^{⊗k}|Z₁|ψ^{⊗k}⟩ = 0` for all `ψ`, hence `Z₁ = 0` by the
polarization `eq_zero_of_ev_kronVec`; and `i Z₂ = ½ Π (i (Y₂ - Y₂ᵀ)) Π ∈ oddK`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Matrix ComplexConjugate

namespace FormalResearch.FrameFree.OddWords

open FormalResearch.FrameFree.Twirls

variable {α γ κ : Type*} [Fintype α] [DecidableEq α] [Fintype γ] [DecidableEq γ] [Fintype κ]
  [DecidableEq κ] {P : α × γ → κ}

theorem copyPerm_mul (c d : Equiv.Perm γ) :
    copyPerm (α := α) (c * d) = copyPerm c * copyPerm d := by
  ext q <;> simp [copyPerm]

theorem permOp_copyPerm_mul_symmetrizer (c : Equiv.Perm γ) :
    permOp (copyPerm (α := α) c) * symmetrizer α γ = symmetrizer α γ := by
  rw [symmetrizer, Matrix.mul_smul, Matrix.mul_sum]
  congr 1
  simp only [permOp_mul, ← copyPerm_mul]
  exact Equiv.sum_comp (Equiv.mulLeft c) (fun e => permOp (copyPerm (α := α) e))

theorem symmetrizer_mul_permOp_copyPerm (c : Equiv.Perm γ) :
    symmetrizer α γ * permOp (copyPerm (α := α) c) = symmetrizer α γ := by
  rw [symmetrizer, Matrix.smul_mul, Matrix.sum_mul]
  congr 1
  simp only [permOp_mul, ← copyPerm_mul]
  exact Equiv.sum_comp (Equiv.mulRight c) (fun e => permOp (copyPerm (α := α) e))

theorem row_inv_of {B : OpS (α × γ)} {c : Equiv.Perm γ}
    (hB : permOp (copyPerm (α := α) c) * B = B) (x z : α × γ → Fin 2) :
    B (x ∘ ⇑(copyPerm (α := α) c)) z = B x z := by
  have := permOp_mul_apply B (copyPerm (α := α) c) x z
  rw [hB] at this
  exact this.symm

theorem col_inv_of {B : OpS (α × γ)} {c : Equiv.Perm γ}
    (hB : B * permOp (copyPerm (α := α) c⁻¹) = B) (x z : α × γ → Fin 2) :
    B x (z ∘ ⇑(copyPerm (α := α) c)) = B x z := by
  have h : z ∘ ⇑(copyPerm (α := α) c) = z ∘ ⇑((copyPerm (α := α) c⁻¹)⁻¹) := by
    rw [← copyPerm_inv, inv_inv]
  have := mul_permOp_apply B (copyPerm (α := α) c⁻¹) x z
  rw [hB] at this
  rw [h]
  exact this.symm

theorem cmp_row_inv (Y : OpS (α × γ)) (x z : α × γ → Fin 2) (c : Equiv.Perm γ) :
    (symmetrizer α γ * Y * symmetrizer α γ) (x ∘ ⇑(copyPerm (α := α) c)) z =
      (symmetrizer α γ * Y * symmetrizer α γ) x z :=
  row_inv_of (by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, permOp_copyPerm_mul_symmetrizer]) x z

theorem cmp_col_inv (Y : OpS (α × γ)) (x z : α × γ → Fin 2) (c : Equiv.Perm γ) :
    (symmetrizer α γ * Y * symmetrizer α γ) x (z ∘ ⇑(copyPerm (α := α) c)) =
      (symmetrizer α γ * Y * symmetrizer α γ) x z :=
  col_inv_of (by rw [Matrix.mul_assoc, symmetrizer_mul_permOp_copyPerm]) x z

theorem rPerm_thetaN {X : OpS (α × γ)} (hX : X ∈ rPerm P) (v : (α × γ → Fin 2) → ℂ) :
    ev X (thetaN v) = conj (ev X v) := by
  induction hX using Submodule.span_induction with
  | mem x hx => obtain ⟨σ, -, rfl⟩ := hx; exact ev_permOp_thetaN σ v
  | zero => rw [ev_zero, ev_zero]; simp
  | add x y _ _ hx hy => rw [ev_add, ev_add, hx, hy, map_add]
  | smul r x _ hx => rw [real_smul_eq', ev_smul, ev_smul, hx, map_mul, Complex.conj_ofReal]

theorem real_sep' {U V W Z : OpS (α × γ)} (hU : U.map conj = U) (hV : V.map conj = V)
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
  have ent : ∀ (M : OpS (α × γ)), M.map conj = M → ∀ a b, conj (M a b) = M a b :=
    fun M hM a b => by simpa using congrFun (congrFun hM a) b
  constructor <;> ext a b <;>
  · have := key _ _ (ent U hU a b) (ent V hV a b) _ _ (ent W hW a b) (ent Z hZ a b)
      (by simpa using congrFun (congrFun h a) b)
    simp [this]

theorem exists_real_split_cmp {A : OpS (α × γ)} (hA : A ∈ Acal P) :
    ∃ Y1 ∈ rPerm P, ∃ Y2 ∈ rPerm P, A = symmetrizer α γ * Y1 * symmetrizer α γ +
      Complex.I • (symmetrizer α γ * Y2 * symmetrizer α γ) := by
  induction hA using Submodule.span_induction with
  | mem M hM =>
    obtain ⟨s, hs, rfl⟩ := hM
    exact ⟨permOp s, Submodule.subset_span ⟨s, hs, rfl⟩, 0, zero_mem _, by simp [cWord]⟩
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a1, ha1, a2, ha2, rfl⟩ := hx
    obtain ⟨b1, hb1, b2, hb2, rfl⟩ := hy
    refine ⟨a1 + b1, add_mem ha1 hb1, a2 + b2, add_mem ha2 hb2, ?_⟩
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_mul, smul_add]; abel
  | smul c x _ hx =>
    obtain ⟨a1, ha1, a2, ha2, rfl⟩ := hx
    refine ⟨c.re • a1 - c.im • a2, sub_mem (Submodule.smul_mem _ _ ha1) (Submodule.smul_mem _ _ ha2),
      c.im • a1 + c.re • a2, add_mem (Submodule.smul_mem _ _ ha1) (Submodule.smul_mem _ _ ha2), ?_⟩
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, real_smul_eq', smul_sub, smul_add, smul_smul]
    ext a b
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    apply Complex.ext <;> simp <;> ring

theorem cmp_mem_rPerm (hP : ∀ (c : Equiv.Perm γ) q, P (copyPerm (α := α) c q) = P q) {Y : OpS (α × γ)}
    (hY : Y ∈ rPerm P) : symmetrizer α γ * Y * symmetrizer α γ ∈ rPerm P :=
  rPerm_mul (rPerm_mul (symmetrizer_mem hP) hY) (symmetrizer_mem hP)

theorem ev_neg_of (A : OpS (α × γ)) (v : (α × γ → Fin 2) → ℂ) : ev (-A) v = - ev A v := by
  have := ev_sub 0 A v
  rw [ev_zero, zero_sub] at this
  rw [zero_sub] at this
  exact this

theorem oddK_of_odd (hP : ∀ (c : Equiv.Perm γ) q, P (copyPerm (α := α) c q) = P q) {A : OpS (α × γ)}
    (hA : A ∈ Acal P) (hH : Aᴴ = A) (hT : ThetaOddK A) : A ∈ oddK P := by
  obtain ⟨Y1, h1, Y2, h2, rfl⟩ := exists_real_split_cmp hA
  set Z1 := symmetrizer α γ * Y1 * symmetrizer α γ with hZ1
  set Z2 := symmetrizer α γ * Y2 * symmetrizer α γ with hZ2
  have hm1 : Z1 ∈ rPerm P := cmp_mem_rPerm hP h1
  have hm2 : Z2 ∈ rPerm P := cmp_mem_rPerm hP h2
  have hr1 : Z1.map conj = Z1 := rPerm_map_conj hm1
  have hr2 : Z2.map conj = Z2 := rPerm_map_conj hm2
  -- Hermiticity splits into symmetry of `Z₁` and antisymmetry of `Z₂`
  have hH' : Z1ᵀ + Complex.I • (-Z2ᵀ) = Z1 + Complex.I • Z2 := by
    rw [← hH, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, conjTranspose_of_map_conj hr1,
      conjTranspose_of_map_conj hr2, Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg]
  have hn : (-Z2ᵀ).map conj = -Z2ᵀ := by
    ext a b
    have := congrFun (congrFun hr2 b) a
    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply, map_neg] at this ⊢
    rw [this]
  have hsep := real_sep' (by rw [Matrix.transpose_map, hr1]) hn hr1 hr2 hH'
  have hs1 : Z1ᵀ = Z1 := hsep.1
  have hs2 : -Z2ᵀ = Z2 := hsep.2
  -- `Θ`-oddness kills `Z₁`
  have hZ1zero : Z1 = 0 := by
    refine eq_zero_of_ev_kronVec Z1 (fun x y c => cmp_row_inv Y1 x y c) (fun x y c => cmp_col_inv Y1 x y c) ?_
    intro ψ
    have hψ := hT ψ
    rw [← thetaN_kronVec, ev_add, ev_add, ev_smul, ev_smul, rPerm_thetaN hm1, rPerm_thetaN hm2] at hψ
    have e1 : conj (ev Z1 (kronVec γ ψ)) = ev Z1 (kronVec γ ψ) := by
      rw [conj_ev, conjTranspose_of_map_conj hr1, hs1]
    have e2 : conj (ev Z2 (kronVec γ ψ)) = - ev Z2 (kronVec γ ψ) := by
      rw [conj_ev, conjTranspose_of_map_conj hr2, neg_eq_iff_eq_neg.1 hs2, ev_neg_of]
    rw [e1, e2] at hψ
    linear_combination hψ / 2
  rw [hZ1zero, zero_add]
  -- the remaining part is `i Z₂ = ½ Π (i (Y₂ - Y₂ᵀ)) Π`
  have hmem : compI α γ (Y2 - Y2ᵀ) ∈ oddK P := Submodule.mem_map_of_mem (rPerm_sub_transpose h2)
  have hexp : compI α γ (Y2 - Y2ᵀ) = Complex.I • (Z2 - Z2ᵀ) := by
    show symmetrizer α γ * (Complex.I • (Y2 - Y2ᵀ)) * symmetrizer α γ = _
    rw [hZ2, Matrix.transpose_mul, Matrix.transpose_mul, symmetrizer_transpose, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
  have hfin : Complex.I • Z2 = (1 / 2 : ℝ) • compI α γ (Y2 - Y2ᵀ) := by
    rw [hexp, real_smul_eq']
    have h3 : Z2 - Z2ᵀ = (2 : ℂ) • Z2 := by
      rw [neg_eq_iff_eq_neg.1 hs2, sub_neg_eq_add, two_smul]
    rw [h3, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  rw [hfin]
  exact Submodule.smul_mem _ _ hmem

theorem oddK_le_Acal {A : OpS (α × γ)} (hA : A ∈ oddK P) : A ∈ Acal P := by
  obtain ⟨Y, hY, rfl⟩ := Submodule.mem_map.1 hA
  have h := cmp_mem_Acal (sSkew_le_rPerm hY)
  have e : compI α γ Y = Complex.I • (symmetrizer α γ * Y * symmetrizer α γ) := by
    show symmetrizer α γ * (Complex.I • Y) * symmetrizer α γ = _
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e]
  exact Submodule.smul_mem _ _ h

/-- **Paper P, `prop:oddwords` (i).**  An element `A` of `𝒜_k` (the span of the compressed words) is
Hermitian and `Θ`-odd on all product vectors `ψ^{⊗k}`, i.e.
`⟨(Θψ)^{⊗k}|A|(Θψ)^{⊗k}⟩ = -⟨ψ^{⊗k}|A|ψ^{⊗k}⟩`, if and only if it is a real combination of the compressed
odd words `Π (i (P_σ - P_σ⁻¹)) Π` (the paper's `(i/2)(W - W⁻¹)` up to the real factor `2`). -/
theorem prop_oddwords_i (hP : ∀ (c : Equiv.Perm γ) q, P (copyPerm (α := α) c q) = P q)
    {A : OpS (α × γ)} : (A ∈ Acal P ∧ Aᴴ = A ∧ ThetaOddK A) ↔ A ∈ oddK P :=
  ⟨fun h => oddK_of_odd hP h.1 h.2.1 h.2.2, fun h => ⟨oddK_le_Acal h, oddK_odd hP h⟩⟩

/-- The paper's words: spins `α`, copies `γ`, one frame per spin (`P q = q.1`). -/
theorem prop_oddwords_i_spins {A : OpS (α × γ)} :
    (A ∈ Acal (fun q : α × γ => q.1) ∧ Aᴴ = A ∧ ThetaOddK A) ↔ A ∈ oddK (fun q : α × γ => q.1) :=
  prop_oddwords_i (fun _ _ => rfl)

/-- `prop:oddwords` (ii), "if" half, for the paper's words. -/
theorem exists_odd_of_noncomm_spins
    (h : ∃ A ∈ Acal (fun q : α × γ => q.1), ∃ B ∈ Acal (fun q : α × γ => q.1), A * B ≠ B * A) :
    ∃ A ∈ Acal (fun q : α × γ => q.1), Aᴴ = A ∧ ThetaOddK A ∧ A ≠ 0 :=
  exists_odd_of_noncomm (fun _ _ => rfl) h

end FormalResearch.FrameFree.OddWords
