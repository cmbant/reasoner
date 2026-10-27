import Mathlib
import FormalResearch.QIB.BlockRealFrame
import FormalResearch.QIB.RealCoordsStructure

/-!
# Weight projectors of the frame commutant are multiplicity-free

Namespace `FormalResearch.QIB`.  Claim class: **proved** (no hypothesis, no new axiom).

Let `C = frameAlg n k` be the commutant of the frame group `{⊗_a u_a^{⊗k}}` on `Copies n k` and
`D = comm C`.  For `m : Fin n → ℕ`, `weightProj m` is the diagonal projector onto the basis vectors
with exactly `m a` ones in block `a` (a weight space of the diagonal torus of `SU(2)^n`).

* `frameAlg_star`, `frameAlg_conj`: `C` is closed under `ᴴ` and under entrywise conjugation (real-spanned);
* `weightProj_mem_comm`: `weightProj m ∈ D` (block permutations preserve weights);
* `exists_block_involution`: two configurations of equal block weights are exchanged by a
  block-preserving involution (Gelfand's trick: the orbitals of `S_k^n` on a weight space are symmetric);
* `weightProj_sym`: every `P Z P`, `Z ∈ D`, is a *symmetric* matrix;
* `weightProj_comm`: hence `P D P` is commutative (`(PZP)(PZ'P)` is again of the form `P Z'' P`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate

namespace FormalResearch.QIB

open FormalResearch.FrameFree.Twirls (OpS permOp permOp_mul permOp_one mul_permOp_apply permOp_mul_apply)
open FormalResearch.FrameFree.Helstrom (Copies)

section Weights

variable {n k : ℕ}

/-- The commutant algebra of the frame group. -/
noncomputable def frameAlg (n k : ℕ) : Subalgebra ℂ (Matrix (Copies n k) (Copies n k) ℂ) :=
  Subalgebra.centralizer ℂ (frameGroup n k)

theorem mem_frameAlg {X : Matrix (Copies n k) (Copies n k) ℂ} :
    X ∈ frameAlg n k ↔ ∀ g ∈ frameGroup n k, g * X = X * g := by
  unfold frameAlg
  rw [Subalgebra.mem_centralizer_iff]

theorem frameAlg_star : ∀ c ∈ frameAlg n k, cᴴ ∈ frameAlg n k := by
  intro c hc
  rw [mem_frameAlg] at hc ⊢
  intro g hg
  have h2 := congrArg Matrix.conjTranspose (hc gᴴ (frameGroup_star_closed n k g hg))
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose] at h2
  exact h2.symm

theorem map_conj_mem_span {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Set (Matrix ι ι ℂ))
    (hreal : ∀ p ∈ S, p.map conj = p) {X : Matrix ι ι ℂ} (hX : X ∈ Submodule.span ℂ S) :
    X.map conj ∈ Submodule.span ℂ S := by
  induction hX using Submodule.span_induction with
  | mem x hx => rw [hreal x hx]; exact Submodule.subset_span hx
  | zero => simpa using Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Matrix.map_add _ (by simp)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have : (c • x).map conj = (conj c) • x.map conj := by ext i j; simp
    rw [this]; exact Submodule.smul_mem _ _ hx

theorem frameAlg_conj : ∀ c ∈ frameAlg n k, c.map conj ∈ frameAlg n k := by
  obtain ⟨hSC, hCS, hreal, -⟩ := frame_real_data n k
  intro c hc
  have h1 : c ∈ commSub (frameGroup n k) := hc
  have h2 := map_conj_mem_span (frameS n k) hreal (hCS c h1)
  have h3 : Submodule.span ℂ (frameS n k) ≤ commSub (frameGroup n k) := Submodule.span_le.2 hSC
  exact h3 h2

theorem mem_frameAlg_of_span {X : Matrix (Copies n k) (Copies n k) ℂ}
    (hX : X ∈ Submodule.span ℂ (frameS n k)) : X ∈ frameAlg n k := by
  obtain ⟨hSC, -, -, -⟩ := frame_real_data n k
  have h3 : Submodule.span ℂ (frameS n k) ≤ commSub (frameGroup n k) := Submodule.span_le.2 hSC
  exact h3 hX

theorem frameS_mem_frameAlg {p : Matrix (Copies n k) (Copies n k) ℂ} (hp : p ∈ frameS n k) :
    p ∈ frameAlg n k :=
  mem_frameAlg_of_span (Submodule.subset_span hp)

theorem mem_span_frameS {X : Matrix (Copies n k) (Copies n k) ℂ} (hX : X ∈ frameAlg n k) :
    X ∈ Submodule.span ℂ (frameS n k) := by
  obtain ⟨-, hCS, -, -⟩ := frame_real_data n k
  exact hCS X hX

/-- Number of ones in block `a` of a copy configuration. -/
def wtc (x : Copies n k) (a : Fin n) : ℕ := (Finset.univ.filter fun c : Fin k => x c a = 1).card

theorem wtc_perm (σ : Equiv.Perm (Fin n × Fin k)) (hσ : ∀ i, (σ i).1 = i.1)
    (x y : Copies n k)
    (hxy : (FormalResearch.QIB.slotEquiv n k).symm y =
      (FormalResearch.QIB.slotEquiv n k).symm x ∘ σ) : wtc y = wtc x := by
  funext a
  unfold wtc
  have hy : ∀ c, y c a = x (σ (a, c)).2 a := by
    intro c
    have := congrFun hxy (a, c)
    simp [FormalResearch.QIB.slotEquiv, Function.comp] at this
    rw [hσ] at this
    exact this
  have hσ' : ∀ c, σ (a, c) = (a, (σ (a, c)).2) := fun c => Prod.ext (hσ _) rfl
  have hinv : ∀ c, (σ.symm (a, c)).1 = a := by
    intro c
    have := hσ (σ.symm (a, c))
    simpa using this.symm
  have hσ'' : ∀ c, σ (a, (σ.symm (a, c)).2) = (a, c) := by
    intro c
    have h1 : σ.symm (a, c) = (a, (σ.symm (a, c)).2) := Prod.ext (hinv c) rfl
    conv_lhs => rw [← h1]
    simp
  refine Finset.card_nbij' (fun c => (σ (a, c)).2) (fun c => (σ.symm (a, c)).2) ?_ ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rw [← hy]; exact hc
  · intro c hc
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rw [hy, hσ'']
    exact hc
  · intro c _
    show (σ.symm (a, (σ (a, c)).2)).2 = c
    rw [← hσ' c]; simp
  · intro c _
    show (σ (a, (σ.symm (a, c)).2)).2 = c
    rw [hσ'']

/-- The weight projector. -/
noncomputable def weightProj (m : Fin n → ℕ) : Matrix (Copies n k) (Copies n k) ℂ :=
  Matrix.diagonal fun x => if wtc x = m then 1 else 0

theorem weightProj_map_conj (m : Fin n → ℕ) : (weightProj (k := k) m).map conj = weightProj m := by
  ext x y
  by_cases h : x = y
  · subst h; by_cases h' : wtc x = m <;> simp [weightProj, h']
  · simp [weightProj, Matrix.diagonal_apply_ne _ h]

theorem weightProj_conjTranspose (m : Fin n → ℕ) : (weightProj (k := k) m)ᴴ = weightProj m := by
  unfold weightProj
  rw [Matrix.diagonal_conjTranspose]
  congr 1; funext x
  by_cases h' : wtc x = m <;> simp [h']

theorem weightProj_idem (m : Fin n → ℕ) :
    weightProj (k := k) m * weightProj m = weightProj m := by
  unfold weightProj
  rw [Matrix.diagonal_mul_diagonal]
  congr 1; funext x
  by_cases h' : wtc x = m <;> simp [h']

theorem weightProj_comm_frameS (m : Fin n → ℕ) {p : Matrix (Copies n k) (Copies n k) ℂ}
    (hp : p ∈ frameS n k) : weightProj m * p = p * weightProj m := by
  obtain ⟨σ, hσ, rfl⟩ := hp
  ext x y
  unfold weightProj
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : slotAlg n k (permOp σ) x y = 0
  · rw [h]; simp
  · have h1 : (FormalResearch.QIB.slotEquiv n k).symm y =
        (FormalResearch.QIB.slotEquiv n k).symm x ∘ σ := by
      by_contra hne
      apply h
      simp [slotAlg_apply, permOp, hne]
    have := wtc_perm σ hσ x y h1
    rw [this]; ring

theorem weightProj_mem_comm (m : Fin n → ℕ) : weightProj m ∈ Subalgebra.centralizer ℂ
    ((frameAlg n k : Subalgebra ℂ _) : Set (Matrix (Copies n k) (Copies n k) ℂ)) := by
  rw [Subalgebra.mem_centralizer_iff]
  intro c hc
  have hc' : c ∈ Submodule.span ℂ (frameS n k) := mem_span_frameS hc
  clear hc
  induction hc' using Submodule.span_induction with
  | mem x hx => exact (weightProj_comm_frameS m hx).symm
  | zero => simp
  | add x y _ _ ihx ihy => rw [Matrix.add_mul, Matrix.mul_add, ihx, ihy]
  | smul a x _ ih => rw [Matrix.smul_mul, Matrix.mul_smul, ih]

/-- The commutant `D = C'` of the frame commutant. -/
noncomputable abbrev frameDual (n k : ℕ) : Subalgebra ℂ (Matrix (Copies n k) (Copies n k) ℂ) :=
  Subalgebra.centralizer ℂ ((frameAlg n k : Subalgebra ℂ _) : Set (Matrix (Copies n k) (Copies n k) ℂ))

theorem exists_involution_fin (f g : Fin k → Fin 2)
    (h : (Finset.univ.filter fun c => f c = 1).card = (Finset.univ.filter fun c => g c = 1).card) :
    ∃ π : Equiv.Perm (Fin k), π * π = 1 ∧ f ∘ π = g := by
  classical
  set A : Finset (Fin k) := Finset.univ.filter fun c => f c = 1 with hA
  set B : Finset (Fin k) := Finset.univ.filter fun c => g c = 1 with hB
  have hcard : (A \ B).card = (B \ A).card := Finset.card_sdiff_comm h
  let e : {c // c ∈ A \ B} ≃ {c // c ∈ B \ A} := Finset.equivOfCardEq hcard
  let F : Fin k → Fin k := fun c =>
    if hc : c ∈ A \ B then ((e ⟨c, hc⟩ : {c // c ∈ B \ A}) : Fin k)
    else if hc' : c ∈ B \ A then ((e.symm ⟨c, hc'⟩ : {c // c ∈ A \ B}) : Fin k) else c
  have hF1 : ∀ c (hc : c ∈ A \ B), F c = ((e ⟨c, hc⟩ : {c // c ∈ B \ A}) : Fin k) := by
    intro c hc; simp only [F, dif_pos hc]
  have hF2 : ∀ c (hc : c ∈ B \ A), F c = ((e.symm ⟨c, hc⟩ : {c // c ∈ A \ B}) : Fin k) := by
    intro c hc
    have : c ∉ A \ B := by
      intro h'; exact (Finset.mem_sdiff.1 hc).2 (Finset.mem_sdiff.1 h').1
    simp only [F, dif_neg this, dif_pos hc]
  have hF3 : ∀ c, c ∉ A \ B → c ∉ B \ A → F c = c := by
    intro c h1 h2; simp only [F, dif_neg h1, dif_neg h2]
  have hinv : Function.Involutive F := by
    intro c
    by_cases h1 : c ∈ A \ B
    · have h2 := (e ⟨c, h1⟩).2
      rw [hF1 c h1, hF2 _ h2]
      simp
    · by_cases h2 : c ∈ B \ A
      · have h3 := (e.symm ⟨c, h2⟩).2
        rw [hF2 c h2, hF1 _ h3]
        simp
      · rw [hF3 c h1 h2, hF3 c h1 h2]
  refine ⟨Function.Involutive.toPerm F hinv, ?_, ?_⟩
  · exact Equiv.ext fun c => hinv c
  · funext c
    show f (F c) = g c
    have hfA : ∀ c, c ∈ A ↔ f c = 1 := fun c => by simp [hA]
    have hgB : ∀ c, c ∈ B ↔ g c = 1 := fun c => by simp [hB]
    have f01 : ∀ c, f c = 1 ∨ f c = 0 := fun c => by
      have := (f c).isLt
      rcases (f c) with ⟨v, hv⟩
      interval_cases v <;> simp
    have g01 : ∀ c, g c = 1 ∨ g c = 0 := fun c => by
      have := (g c).isLt
      rcases (g c) with ⟨v, hv⟩
      interval_cases v <;> simp
    by_cases h1 : c ∈ A \ B
    · have h2 := (e ⟨c, h1⟩).2
      rw [hF1 c h1]
      have hb := (Finset.mem_sdiff.1 h1).2
      have ha2 := (Finset.mem_sdiff.1 h2).2
      rw [hfA] at ha2
      rw [hgB] at hb
      rcases f01 ((e ⟨c, h1⟩ : {c // c ∈ B \ A}) : Fin k) with h | h
      · exact absurd h ha2
      · rcases g01 c with h' | h'
        · exact absurd h' hb
        · rw [h, h']
    · by_cases h2 : c ∈ B \ A
      · have h3 := (e.symm ⟨c, h2⟩).2
        rw [hF2 c h2]
        have hb := (Finset.mem_sdiff.1 h2).1
        rw [hgB] at hb
        have ha3 := (Finset.mem_sdiff.1 h3).1
        rw [hfA] at ha3
        rw [ha3, hb]
      · rw [hF3 c h1 h2]
        have : c ∈ A ↔ c ∈ B := by
          constructor
          · intro ha
            by_contra hb
            exact h1 (Finset.mem_sdiff.2 ⟨ha, hb⟩)
          · intro hb
            by_contra ha
            exact h2 (Finset.mem_sdiff.2 ⟨hb, ha⟩)
        rw [hfA, hgB] at this
        rcases f01 c with h | h <;> rcases g01 c with h' | h'
        · rw [h, h']
        · rw [h] at this; exact absurd (this.1 rfl) (by rw [h']; decide)
        · rw [h'] at this; exact absurd (this.2 rfl) (by rw [h]; decide)
        · rw [h, h']

theorem exists_block_involution (x y : Fin n × Fin k → Fin 2)
    (h : ∀ a, (Finset.univ.filter fun c : Fin k => x (a, c) = 1).card =
      (Finset.univ.filter fun c : Fin k => y (a, c) = 1).card) :
    ∃ σ : Equiv.Perm (Fin n × Fin k), (∀ i, (σ i).1 = i.1) ∧ σ * σ = 1 ∧ x ∘ σ = y := by
  choose π hπ1 hπ2 using fun a => exists_involution_fin (fun c => x (a, c)) (fun c => y (a, c)) (h a)
  have hinv : Function.Involutive (fun p : Fin n × Fin k => (p.1, π p.1 p.2)) := by
    intro p
    have := congrFun (congrArg (fun q : Equiv.Perm (Fin k) => (q : Fin k → Fin k)) (hπ1 p.1)) p.2
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id_eq] at this
    simp [this]
  refine ⟨Function.Involutive.toPerm _ hinv, fun i => rfl, ?_, ?_⟩
  · exact Equiv.ext fun p => hinv p
  · funext p
    have := congrFun (hπ2 p.1) p.2
    simpa using this

theorem Z_swap {m : Fin n → ℕ} {Z : Matrix (Copies n k) (Copies n k) ℂ} (hZ : Z ∈ frameDual n k)
    (x y : Copies n k) (hw : wtc x = wtc y) : Z y x = Z x y := by
  obtain ⟨σ, hσ, hσ2, hxy⟩ := exists_block_involution (slotEquiv n k |>.symm x) ((slotEquiv n k).symm y)
    (fun a => by
      have := congrFun hw a
      exact this)
  have hp : slotAlg n k (permOp σ) ∈ frameS n k := ⟨σ, hσ, rfl⟩
  have hcomm : slotAlg n k (permOp σ) * Z = Z * slotAlg n k (permOp σ) :=
    (Subalgebra.mem_centralizer_iff ℂ).1 hZ _ (frameS_mem_frameAlg hp)
  have h2 := congrArg (slotAlg n k).symm hcomm
  rw [map_mul, map_mul, AlgEquiv.symm_apply_apply] at h2
  have h3 := congrFun (congrFun h2 ((slotEquiv n k).symm x)) ((slotEquiv n k).symm x)
  rw [permOp_mul_apply, mul_permOp_apply] at h3
  have hσinv : σ⁻¹ = σ := by
    rw [inv_eq_iff_mul_eq_one]; exact hσ2
  rw [hσinv, hxy] at h3
  have e1 : Z y x = (slotAlg n k).symm Z ((slotEquiv n k).symm y) ((slotEquiv n k).symm x) := by
    conv_lhs => rw [← (slotAlg n k).apply_symm_apply Z]
    rfl
  have e2 : Z x y = (slotAlg n k).symm Z ((slotEquiv n k).symm x) ((slotEquiv n k).symm y) := by
    conv_lhs => rw [← (slotAlg n k).apply_symm_apply Z]
    rfl
  rw [e1, e2, h3]

theorem weightProj_mem_frameDual (m : Fin n → ℕ) : weightProj (k := k) m ∈ frameDual n k :=
  weightProj_mem_comm m

theorem weightProj_mul_apply (m : Fin n → ℕ) (Z : Matrix (Copies n k) (Copies n k) ℂ) (x y : Copies n k) :
    ((weightProj m * Z * weightProj m : Matrix (Copies n k) (Copies n k) ℂ)) x y =
      (if wtc x = m then 1 else 0) * Z x y * (if wtc y = m then 1 else 0) := by
  unfold weightProj
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- **Every `P Z P`, `Z ∈ C'`, is a symmetric matrix** (Gelfand's trick). -/
theorem weightProj_sym (m : Fin n → ℕ) {Z : Matrix (Copies n k) (Copies n k) ℂ}
    (hZ : Z ∈ frameDual n k) : (weightProj m * Z * weightProj m)ᵀ = weightProj m * Z * weightProj m := by
  ext x y
  rw [Matrix.transpose_apply, weightProj_mul_apply, weightProj_mul_apply]
  by_cases hx : wtc x = m
  · by_cases hy : wtc y = m
    · rw [Z_swap (m := m) hZ x y (hx.trans hy.symm)]; ring
    · simp [hy]
  · simp [hx]

/-- **`P C' P` is commutative.** -/
theorem weightProj_comm (m : Fin n → ℕ) {Z₁ Z₂ : Matrix (Copies n k) (Copies n k) ℂ}
    (h₁ : Z₁ ∈ frameDual n k) (h₂ : Z₂ ∈ frameDual n k) :
    (weightProj m * Z₁ * weightProj m) * (weightProj m * Z₂ * weightProj m) =
      (weightProj m * Z₂ * weightProj m) * (weightProj m * Z₁ * weightProj m) := by
  set P : Matrix (Copies n k) (Copies n k) ℂ := weightProj m with hP
  have hPD : P ∈ frameDual n k := weightProj_mem_frameDual m
  have hPP : P * P = P := weightProj_idem m
  have hs1 := weightProj_sym m h₁
  have hs2 := weightProj_sym m h₂
  have hprod : (P * Z₁ * P) * (P * Z₂ * P) = P * (Z₁ * P * Z₂) * P := by
    calc (P * Z₁ * P) * (P * Z₂ * P) = P * Z₁ * (P * P) * Z₂ * P := by simp only [Matrix.mul_assoc]
      _ = P * (Z₁ * P * Z₂) * P := by rw [hPP]; simp only [Matrix.mul_assoc]
  have hs3 : ((P * Z₁ * P) * (P * Z₂ * P))ᵀ = (P * Z₁ * P) * (P * Z₂ * P) := by
    rw [hprod]
    exact weightProj_sym m (mul_mem (mul_mem h₁ hPD) h₂)
  rw [Matrix.transpose_mul, hs1, hs2] at hs3
  exact hs3.symm

end Weights

end FormalResearch.QIB
