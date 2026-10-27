import FormalResearch.FrameFree.XiInvUnconditional

/-!
# The paper's `ψ₊`: `F_C = F_K = 1/2` and `ξ_inv = log 2` (Paper P, `eq:psiplus`)

Namespace `FormalResearch.PsiPlusPaper` (outside `FormalResearch.FrameFree`, whose `ip` for `Psi` would shadow `NQubit.ip`).  Claim class: **proved**.

`FrameFree.PsiPlusKramers.psiPlus = FrameFree.Sharing.psiEx (π/4)` is the Choi probe of `√SWAP`; it is the paper's
`ψ₊ = (s₁₂ s₃₄ + i s₁₃ s₂₄)/√2` (`s_{ij}` the singlet of spins `i, j`) only after exchanging spins `2` and `4`
and up to a global phase.  This file makes that identification, so that the results proved for `psiPlus`
transfer to the paper's state.

* `psiPlusPaper : Ψ 4`: the paper's `ψ₊`, written out in the product basis from `eps` (`s(a,b) = ε_{ab}/√2`).
* `permΨ σ ψ = ψ ∘ (· ∘ σ)`: the action of a qubit permutation on `Ψ n`.
* Invariance under qubit permutations (`σ`) and global phases (`|c| = 1`) of `F_K(ψ, Θψ)`
  (`FKΘ_perm`, `FKΘ_smul`), of `F_C(ψ,Θψ)` (`FCΘ_perm`, `FCΘ_smul`) and of `Helstrom.Pe k` (`Pe_perm`, `Pe_smul`),
  and `Θ (permΨ σ ψ) = permΨ σ (Θ ψ)`.
* `psiPlusPaper_eq : psiPlusPaper = (-i) • permΨ (swap 1 3) psiPlus` (exchange of spins `2` and `4`).
* `psiPlusPaper_kramers : F_C = F_K = 1/2` and `psiPlusPaper_xi_inv : HasXiInv psiPlusPaper (log 2)`.

Depends only on `FrameFree.PsiPlusKramers.psiPlus`, `FrameFree.PsiPlusKramers.psiplus_kramers` and `FrameFree.XiInv.psiplus_xi_inv'`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped ComplexConjugate Matrix BigOperators Real ComplexOrder
open Matrix FormalResearch.FrameFree.NQubit FormalResearch.FrameFree.Helstrom
open FormalResearch.FrameFree.Sharing (eq_four)

namespace FormalResearch.PsiPlusPaper

/-! ### Qubit permutations and phases -/

section Perm

variable {n : ℕ}

/-- `x ↦ x ∘ σ` on computational basis labels. -/
def pw (σ : Equiv.Perm (Fin n)) : (Fin n → Fin 2) ≃ (Fin n → Fin 2) where
  toFun x := x ∘ σ
  invFun x := x ∘ σ.symm
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

/-- The action of a permutation of the qubits on `Ψ n`: `(permΨ σ ψ)(x) = ψ(x ∘ σ)`. -/
def permΨ (σ : Equiv.Perm (Fin n)) (ψ : Ψ n) : Ψ n := fun x => ψ (pw σ x)

theorem permΨ_inv_perm (σ : Equiv.Perm (Fin n)) (ψ : Ψ n) : permΨ σ⁻¹ (permΨ σ ψ) = ψ := by
  funext x
  simp [permΨ, pw, Function.comp_def]

theorem nsq_perm (σ : Equiv.Perm (Fin n)) (ψ : Ψ n) : nsq (permΨ σ ψ) = nsq ψ :=
  (pw σ).sum_comp (fun y => Complex.normSq (ψ y))

theorem ip_perm (σ : Equiv.Perm (Fin n)) (φ ψ : Ψ n) : ip (permΨ σ φ) (permΨ σ ψ) = ip φ ψ :=
  (pw σ).sum_comp (fun y => conj (φ y) * ψ y)

theorem rot_perm (σ : Equiv.Perm (Fin n)) (u : Fin n → Op1) (ψ : Ψ n) :
    rot u (permΨ σ ψ) = permΨ σ (rot (u ∘ σ) ψ) := by
  funext x
  simp only [rot, permΨ]
  rw [← (pw σ).sum_comp (fun z => (∏ j, (u ∘ σ) j ((pw σ x) j) (z j)) * ψ z)]
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  exact (Equiv.prod_comp σ (fun i => u i (x i) (y i))).symm

theorem Θ_perm (σ : Equiv.Perm (Fin n)) (ψ : Ψ n) : Θ (permΨ σ ψ) = permΨ σ (Θ ψ) := by
  rw [Θ_eq_rot, Θ_eq_rot]
  exact rot_perm σ (fun _ => eps) (cj ψ)

theorem rot_smul (u : Fin n → Op1) (c : ℂ) (ψ : Ψ n) : rot u (c • ψ) = c • rot u ψ := by
  funext x
  simp [rot, Finset.mul_sum, mul_left_comm]

theorem ip_smul_left (c : ℂ) (φ ψ : Ψ n) : ip (c • φ) ψ = conj c * ip φ ψ := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [mul_assoc]

theorem ip_smul_right (c : ℂ) (φ ψ : Ψ n) : ip φ (c • ψ) = c * ip φ ψ := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [mul_left_comm]

theorem nsq_smul (c : ℂ) (φ : Ψ n) : nsq (c • φ) = Complex.normSq c * nsq φ := by
  unfold nsq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [Complex.normSq_mul]

theorem Θ_smul (c : ℂ) (ψ : Ψ n) : Θ (c • ψ) = conj c • Θ ψ := by
  funext x
  simp [Θ, Finset.mul_sum, mul_left_comm]

/-- Reindexing `∃ u` by a qubit permutation. -/
theorem exists_comp_perm (σ : Equiv.Perm (Fin n)) (p : Op1 → Prop) (f : (Fin n → Op1) → Prop) :
    (∃ u : Fin n → Op1, (∀ i, p (u i)) ∧ f (u ∘ σ)) ↔ ∃ u : Fin n → Op1, (∀ i, p (u i)) ∧ f u := by
  constructor
  · rintro ⟨u, hu, hf⟩
    exact ⟨u ∘ σ, fun i => hu (σ i), hf⟩
  · rintro ⟨u, hu, hf⟩
    refine ⟨u ∘ σ.symm, fun i => hu _, ?_⟩
    have : (u ∘ σ.symm) ∘ σ = u := by funext i; simp
    rw [this]; exact hf

/-! #### `F_K` -/

theorem rotSet_perm (σ : Equiv.Perm (Fin n)) (ψ φ : Ψ n) :
    rotSet (permΨ σ ψ) (permΨ σ φ) = rotSet ψ φ := by
  ext r
  simp only [rotSet, Set.mem_ofPred_eq, rot_perm, ip_perm]
  exact exists_comp_perm σ SU2 (fun u => r = Complex.normSq (ip ψ (rot u φ)))

theorem rotSet_smul {c d : ℂ} (hc : Complex.normSq c = 1) (hd : Complex.normSq d = 1) (ψ φ : Ψ n) :
    rotSet (c • ψ) (d • φ) = rotSet ψ φ := by
  ext r
  simp only [rotSet, Set.mem_ofPred_eq, rot_smul, ip_smul_left, ip_smul_right, Complex.normSq_mul,
    Complex.normSq_conj, hc, hd, one_mul]

theorem FKΘ_perm (σ : Equiv.Perm (Fin n)) (ψ : Ψ n) : FKΘ (permΨ σ ψ) = FKΘ ψ := by
  unfold FKΘ FK
  rw [Θ_perm, rotSet_perm]

theorem FKΘ_smul {c : ℂ} (hc : Complex.normSq c = 1) (ψ : Ψ n) : FKΘ (c • ψ) = FKΘ ψ := by
  unfold FKΘ FK
  rw [Θ_smul, rotSet_smul hc (by rw [Complex.normSq_conj]; exact hc)]

/-! #### `F_C` -/

theorem FCset_perm (σ : Equiv.Perm (Fin n)) (ψ φ : Ψ n) :
    FrameFree.Ceilings.FCset (permΨ σ ψ) (permΨ σ φ) = FrameFree.Ceilings.FCset ψ φ := by
  ext r
  simp only [FrameFree.Ceilings.FCset, Set.mem_ofPred_eq, rot_perm, ip_perm, nsq_perm]
  exact exists_comp_perm σ (fun a => a.det = 1)
    (fun g => nsq (rot g φ) ≠ 0 ∧ r = Complex.normSq (ip ψ (rot g φ)) / nsq (rot g φ))

theorem FCset_smul {c d : ℂ} (hc : Complex.normSq c = 1) (hd : Complex.normSq d = 1) (ψ φ : Ψ n) :
    FrameFree.Ceilings.FCset (c • ψ) (d • φ) = FrameFree.Ceilings.FCset ψ φ := by
  ext r
  simp only [FrameFree.Ceilings.FCset, Set.mem_ofPred_eq, rot_smul, ip_smul_left, ip_smul_right, nsq_smul,
    Complex.normSq_mul, Complex.normSq_conj, hc, hd, one_mul]

theorem FCΘ_perm (σ : Equiv.Perm (Fin n)) (ψ : Ψ n) :
    FrameFree.Ceilings.FCΘ (permΨ σ ψ) = FrameFree.Ceilings.FCΘ ψ := by
  unfold FrameFree.Ceilings.FCΘ FrameFree.Ceilings.FC
  rw [Θ_perm, FCset_perm]

theorem FCΘ_smul {c : ℂ} (hc : Complex.normSq c = 1) (ψ : Ψ n) :
    FrameFree.Ceilings.FCΘ (c • ψ) = FrameFree.Ceilings.FCΘ ψ := by
  unfold FrameFree.Ceilings.FCΘ FrameFree.Ceilings.FC
  rw [Θ_smul, FCset_smul hc (by rw [Complex.normSq_conj]; exact hc)]

end Perm

/-! ### `P_e(k)` -/

section PeInv

variable {n : ℕ}

/-- `x ↦ (j ↦ x j ∘ σ)` on the basis of `k` copies. -/
def pB (σ : Equiv.Perm (Fin n)) (k : ℕ) : Copies n k ≃ Copies n k where
  toFun x := fun j => x j ∘ σ
  invFun x := fun j => x j ∘ σ.symm
  left_inv x := by funext j i; simp
  right_inv x := by funext j i; simp

theorem copies_perm (σ : Equiv.Perm (Fin n)) (k : ℕ) (ψ : Ψ n) :
    copies k (permΨ σ ψ) = copies k ψ ∘ pB σ k := rfl

theorem copies_smul (k : ℕ) (c : ℂ) (φ : Ψ n) : copies k (c • φ) = c ^ k • copies k φ := by
  funext i
  simp [copies, Finset.prod_mul_distrib]

theorem rotK_submatrix (σ : Equiv.Perm (Fin n)) (k : ℕ) (u : Fin n → Op1) :
    (rotK k u).submatrix (pB σ k) (pB σ k) = rotK k (u ∘ σ.symm) := by
  ext x y
  simp only [Matrix.submatrix_apply, rotK, kron]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Equiv.prod_comp σ (fun i => (u ∘ σ.symm) i (x j i) (y j i))]
  simp [pB]

theorem submatrix_one_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ ι) (E : Matrix ι ι ℂ) :
    (1 - E).submatrix e e = 1 - E.submatrix e e := by
  ext i j
  simp [Matrix.one_apply]

theorem isInvEffect_submatrix (σ : Equiv.Perm (Fin n)) (k : ℕ)
    {E : Matrix (Copies n k) (Copies n k) ℂ} (hE : IsInvEffect k E) :
    IsInvEffect k (E.submatrix (pB σ k) (pB σ k)) := by
  refine ⟨⟨hE.1.1.submatrix _, ?_⟩, fun u hu => ?_⟩
  · have := hE.1.2.submatrix (pB σ k)
    rwa [submatrix_one_sub] at this
  · have hu' : ∀ i, SU2 ((u ∘ σ) i) := fun i => hu (σ i)
    have h1 : rotK k u = (rotK k (u ∘ σ)).submatrix (pB σ k) (pB σ k) := by
      rw [rotK_submatrix]
      congr 1; funext i; simp
    rw [h1, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hE.2 (u ∘ σ) hu']

theorem qf_submatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ ι) (M : Matrix ι ι ℂ)
    (v w : ι → ℂ) : qf (M.submatrix e e) v w = qf M (v ∘ e.symm) (w ∘ e.symm) := by
  unfold qf
  rw [Matrix.submatrix_mulVec_equiv]
  simp only [dotProduct, Pi.star_apply, Function.comp_apply]
  exact Fintype.sum_equiv e _ _ (fun i => by simp)

theorem err_submatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ ι) (E : Matrix ι ι ℂ)
    (v w : ι → ℂ) : err (E.submatrix e e) v w = err E (v ∘ e.symm) (w ∘ e.symm) := by
  unfold err
  rw [← submatrix_one_sub, qf_submatrix, qf_submatrix]

theorem Pe_le_err {k : ℕ} {ψ : Ψ n} {E : Matrix (Copies n k) (Copies n k) ℂ} (hE : IsInvEffect k E) :
    Pe k ψ ≤ err E (copies k ψ) (copies k (Θ ψ)) :=
  csInf_le ⟨0, by rintro r ⟨E, hE, rfl⟩; exact err_nonneg hE.1 _ _⟩ ⟨E, hE, rfl⟩

theorem Pe_le_perm (k : ℕ) (σ : Equiv.Perm (Fin n)) (ψ : Ψ n) : Pe k ψ ≤ Pe k (permΨ σ ψ) := by
  refine le_csInf ⟨_, 0, isInvEffect_zero k, rfl⟩ ?_
  rintro r ⟨E, hE, rfl⟩
  rw [Θ_perm, copies_perm, copies_perm]
  have hE' : IsInvEffect k (E.submatrix (pB σ.symm k) (pB σ.symm k)) := isInvEffect_submatrix σ.symm k hE
  have h := Pe_le_err (ψ := ψ) hE'
  refine h.trans (le_of_eq ?_)
  have := err_submatrix (pB σ.symm k) E (copies k ψ) (copies k (Θ ψ))
  rw [this]
  rfl

/-- `P_e(k)` is invariant under permutations of the qubits. -/
theorem Pe_perm (k : ℕ) (σ : Equiv.Perm (Fin n)) (ψ : Ψ n) : Pe k (permΨ σ ψ) = Pe k ψ := by
  refine le_antisymm ?_ (Pe_le_perm k σ ψ)
  have := Pe_le_perm k σ⁻¹ (permΨ σ ψ)
  rwa [permΨ_inv_perm] at this

theorem err_smul {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Matrix ι ι ℂ) {l m : ℂ}
    (hl : Complex.normSq l = 1) (hm : Complex.normSq m = 1) (a b : ι → ℂ) :
    err E (l • a) (m • b) = err E a b := by
  have key : ∀ (M : Matrix ι ι ℂ) (c : ℂ) (v : ι → ℂ), Complex.normSq c = 1 →
      qf M (c • v) (c • v) = qf M v v := by
    intro M c v hc
    rw [qf_smul_left, qf_smul_right, ← mul_assoc, ← Complex.normSq_eq_conj_mul_self, hc]
    simp
  unfold err
  rw [key _ _ _ hl, key _ _ _ hm]

/-- `P_e(k)` is invariant under global phases. -/
theorem Pe_smul (k : ℕ) {c : ℂ} (hc : Complex.normSq c = 1) (ψ : Ψ n) : Pe k (c • ψ) = Pe k ψ := by
  have hck : Complex.normSq (c ^ k) = 1 := by rw [map_pow, hc, one_pow]
  have hck' : Complex.normSq (conj c ^ k) = 1 := by rw [map_pow, Complex.normSq_conj, hc, one_pow]
  unfold Pe
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq, Θ_smul, copies_smul, err_smul _ hck hck']

theorem Pe_smul_perm (k : ℕ) {c : ℂ} (hc : Complex.normSq c = 1) (σ : Equiv.Perm (Fin n)) (ψ : Ψ n) :
    Pe k (c • permΨ σ ψ) = Pe k ψ := by
  rw [Pe_smul k hc, Pe_perm]

end PeInv

/-! ### The paper's `ψ₊` -/

/-- The singlet amplitude `s(a,b) = ε_{ab}/√2`, `s = (|01⟩ - |10⟩)/√2`. -/
noncomputable def sing (a b : Fin 2) : ℂ := eps a b / (Real.sqrt 2 : ℂ)

/-- **The paper's `ψ₊`** (Paper P, `eq:psiplus`): `ψ₊ = (s₁₂ s₃₄ + i s₁₃ s₂₄)/√2`, written in the product
basis `x = (x₁,x₂,x₃,x₄)`. -/
noncomputable def psiPlusPaper : Ψ 4 := fun x =>
  (1 / (Real.sqrt 2 : ℂ)) *
    (sing (x 0) (x 1) * sing (x 2) (x 3) + Complex.I * (sing (x 0) (x 2) * sing (x 1) (x 3)))

/-- Explicit amplitudes of `psiPlus = ψ_{U_{π/4}}`:
`ψ(x) = (√2/4)(ε_{x₁x₃} ε_{x₂x₄} - i ε_{x₂x₃} ε_{x₁x₄})`, i.e. `(s₁₃ s₂₄ - i s₂₃ s₁₄)/√2`. -/
theorem psiPlus_apply (x : Fin 4 → Fin 2) :
    FrameFree.PsiPlusKramers.psiPlus x =
      ((Real.sqrt 2 : ℂ) / 4) *
        (eps (x 0) (x 2) * eps (x 1) (x 3) - Complex.I * (eps (x 1) (x 2) * eps (x 0) (x 3))) := by
  rw [eq_four x]
  generalize x 0 = a
  generalize x 1 = b
  generalize x 2 = c
  generalize x 3 = d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [FrameFree.PsiPlusKramers.psiPlus, FrameFree.Sharing.psiEx, FrameFree.Sharing.choi, FrameFree.Sharing.ofMat, FrameFree.Sharing.Uex, FrameFree.Sharing.Ug,
      FrameFree.Sharing.Sw, FrameFree.Sharing.EE, eps, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Real.cos_pi_div_four] <;> ring

theorem eps_antisymm (a b : Fin 2) : eps b a = - eps a b := by
  fin_cases a <;> fin_cases b <;> simp [eps]

/-- **The identification.**  The paper's `ψ₊` is `psiPlus` after exchanging spins `2` and `4`, times the
global phase `-i`. -/
theorem psiPlusPaper_eq :
    psiPlusPaper = (-Complex.I) • permΨ (Equiv.swap (1 : Fin 4) 3) FrameFree.PsiPlusKramers.psiPlus := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have : (Real.sqrt 2) ≠ 0 := by positivity
    exact_mod_cast this
  funext x
  rw [Pi.smul_apply, smul_eq_mul]
  show _ = _ * FrameFree.PsiPlusKramers.psiPlus (x ∘ Equiv.swap (1 : Fin 4) 3)
  rw [psiPlus_apply]
  have e0 : (x ∘ Equiv.swap (1 : Fin 4) 3) 0 = x 0 := by simp [Equiv.swap_apply_of_ne_of_ne]
  have e1 : (x ∘ Equiv.swap (1 : Fin 4) 3) 1 = x 3 := by simp
  have e2 : (x ∘ Equiv.swap (1 : Fin 4) 3) 2 = x 2 := by simp [Equiv.swap_apply_of_ne_of_ne]
  have e3 : (x ∘ Equiv.swap (1 : Fin 4) 3) 3 = x 1 := by simp
  rw [e0, e1, e2, e3, eps_antisymm (x 1) (x 3), eps_antisymm (x 2) (x 3)]
  simp only [psiPlusPaper, sing]
  have h4 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = 4 := by
    calc ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) ^ 2 := by ring
      _ = 4 := by rw [h2]; norm_num
  field_simp
  generalize eps (x 0) (x 1) = A
  generalize eps (x 2) (x 3) = B
  generalize eps (x 0) (x 2) = C
  generalize eps (x 1) (x 3) = D
  linear_combination (Complex.I * (-(C * D) + Complex.I * (A * B))) * h4 + 4 * (A * B) * Complex.I_sq

theorem normSq_neg_I : Complex.normSq (-Complex.I) = 1 := by simp

theorem nsq_psiPlusPaper : nsq psiPlusPaper = 1 := by
  rw [psiPlusPaper_eq, nsq_smul, nsq_perm, FrameFree.Sharing.nsq_psiEx, normSq_neg_I, one_mul]

/-- **`thm:psipluskramers` for the paper's `ψ₊`**: `F_C(ψ₊) = F_K(ψ₊) = 1/2`. -/
theorem psiPlusPaper_kramers : FrameFree.Ceilings.FCΘ psiPlusPaper = 1 / 2 ∧ FKΘ psiPlusPaper = 1 / 2 := by
  rw [psiPlusPaper_eq, FCΘ_smul normSq_neg_I, FKΘ_smul normSq_neg_I, FCΘ_perm, FKΘ_perm]
  exact FrameFree.PsiPlusKramers.psiplus_kramers

theorem psiPlusPaper_calibrated : FrameFree.Ceilings.FCΘ psiPlusPaper = FKΘ psiPlusPaper := by
  rw [psiPlusPaper_kramers.1, psiPlusPaper_kramers.2]

theorem psiPlusPaper_CK : CK psiPlusPaper = Real.log 2 := by
  unfold CK
  rw [psiPlusPaper_kramers.2, Real.log_div (by norm_num) (by norm_num)]
  simp

theorem Pe_psiPlusPaper (k : ℕ) : Pe k psiPlusPaper = Pe k FrameFree.PsiPlusKramers.psiPlus := by
  rw [psiPlusPaper_eq, Pe_smul_perm k normSq_neg_I]

/-- **`ξ_inv(ψ₊) = log 2` for the paper's `ψ₊`.** -/
theorem psiPlusPaper_xi_inv : FrameFree.XiInv.HasXiInv psiPlusPaper (Real.log 2) := by
  have h := FrameFree.XiInv.psiplus_xi_inv'
  unfold FrameFree.XiInv.HasXiInv at h ⊢
  simp only [Pe_psiPlusPaper]
  exact h

end FormalResearch.PsiPlusPaper
