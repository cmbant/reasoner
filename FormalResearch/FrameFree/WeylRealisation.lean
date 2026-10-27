import FormalResearch.FourQubitEntropy.Classify

/-!
# Realising signed permutations by local rotations, and the easy direction of the Weyl-vertex formula

A *magic-diagonal* state `psiMag d` has cut matrix `B diag(d) Bᵀ` (`B = magicB`).  Local rotations
`a ⊗ b ⊗ c ⊗ e` with `a,b,c,e ∈ SU(2)` act on magic coordinates as `X ↦ P X Qᵀ`, where
`P = Bᴴ (a ⊗ b) B` and `Q = Bᴴ (c ⊗ e) B` are real.  We prove

* `ip_psiMag`, `conj_psiMag`, `M4_eq_psiMag`;
* `exists_su2_realise`: every signed permutation matrix `D_t Π_σ` of determinant `1` is of the form
  `Bᴴ (a ⊗ b) B` with `a, b ∈ SU(2)`;
* `weyl_le_rotOverlap`: for `w = (σ, s) ∈ W(D₄)` (`s k = ±1`, `∏ s = 1`, `(w d')_k = s_k d'_{σ k}`),
  `|∑ conj(d_k) s_k d'_{σ k}|² ≤ rotOverlap (psiMag d) (psiMag d')`.

Everything is a proof (no numerics, no `native_decide`).
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FrameFree

open FormalResearch.FourQubitEntropy

/-- The index type of a magic basis (and of a cut matrix). -/
abbrev Pair := Fin 2 × Fin 2

/-- `(a,b) ↦ 2a+b`, the order `(0,0),(0,1),(1,0),(1,1)` of the columns of `magicB`. -/
def pairEquiv : Pair ≃ Fin 4 := finProdFinEquiv

/-- The Hermitian pairing `⟨ψ|φ⟩`. -/
noncomputable def ip (ψ φ : Psi) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ e, conj (ψ a b c e) * φ a b c e

/-- `SU(2)`. -/
def SU2 (a : Op1) : Prop := aᴴ * a = 1 ∧ a.det = 1

/-- The vector with cut matrix `B diag(d) Bᵀ`, `d` indexed by `Pair`. -/
noncomputable def psiMagP (d : Pair → ℂ) : Psi :=
  ofZmat (magicB * Matrix.diagonal d * magicBᵀ)

/-- The magic-diagonal state of `d : Fin 4 → ℂ` (coordinate `k` ↔ magic vector `pairEquiv.symm k`). -/
noncomputable def psiMag (d : Fin 4 → ℂ) : Psi := psiMagP (fun p => d (pairEquiv p))

/-- The Frobenius pairing of two matrices. -/
noncomputable def fro (A B : Mat4) : ℂ := ∑ i, ∑ j, conj (A i j) * B i j

theorem ip_eq_fro (ψ φ : Psi) : ip ψ φ = fro (zmat ψ) (zmat φ) := by
  simp [ip, fro, zmat, Fintype.sum_prod_type]

theorem fro_eq_trace (A B : Mat4) : fro A B = Matrix.trace (Aᴴ * B) := by
  simp only [fro, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Finset.sum_comm

theorem bT_conjB : magicBᵀ * magicB.map star = 1 := unitary_transpose_mul magicB_unitary

/-- Magic coordinates are an isometry for the Frobenius pairing. -/
theorem fro_magic (X Y : Mat4) :
    fro (magicB * X * magicBᵀ) (magicB * Y * magicBᵀ) = fro X Y := by
  rw [fro_eq_trace, fro_eq_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    transpose_conjTranspose]
  have h1 : (magicB.map star * (Xᴴ * magicBᴴ)) * (magicB * Y * magicBᵀ) =
      magicB.map star * (Xᴴ * Y) * magicBᵀ := by
    calc (magicB.map star * (Xᴴ * magicBᴴ)) * (magicB * Y * magicBᵀ)
        = magicB.map star * (Xᴴ * (magicBᴴ * magicB) * Y) * magicBᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [magicB_unitary]; simp only [Matrix.mul_one]
  rw [h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, bT_conjB, Matrix.one_mul]

theorem ip_psiMagP (d d' : Pair → ℂ) :
    ip (psiMagP d) (psiMagP d') = ∑ k, conj (d k) * d' k := by
  rw [ip_eq_fro]
  unfold psiMagP
  rw [zmat_ofZmat, zmat_ofZmat, fro_magic]
  simp only [fro, Matrix.diagonal_apply]
  simp [apply_ite]

theorem ip_psiMag (d d' : Fin 4 → ℂ) :
    ip (psiMag d) (psiMag d') = ∑ k, conj (d k) * d' k := by
  unfold psiMag
  rw [ip_psiMagP]
  exact Equiv.sum_comp pairEquiv (fun k => conj (d k) * d' k)


/-! ### Signed permutation matrices and their realisation -/

/-- The signed permutation matrix `D_t Π_σ`: row `i` has the single entry `t i` in column `σ i`. -/
def sp (σ : Equiv.Perm Pair) (t : Pair → ℤ) : Matrix Pair Pair ℝ :=
  Matrix.of fun i j => if σ i = j then (t i : ℝ) else 0

/-- A real matrix viewed as a complex one. -/
noncomputable def cmat (M : Matrix Pair Pair ℝ) : Mat4 := M.map Complex.ofReal

theorem cmat_mul (M N : Matrix Pair Pair ℝ) : cmat (M * N) = cmat M * cmat N := by
  unfold cmat; exact Matrix.map_mul (f := Complex.ofRealHom)

theorem cmat_one : cmat 1 = 1 := by
  ext i j; by_cases h : i = j <;> simp [cmat, Matrix.one_apply, h]

theorem sp_mul (σ σ' : Equiv.Perm Pair) (t t' : Pair → ℤ) :
    sp σ t * sp σ' t' = sp (σ' * σ) (fun i => t i * t' (σ i)) := by
  ext i j
  simp [sp, Matrix.mul_apply, ite_mul]
  rw [Finset.sum_eq_single (σ i)]
  · by_cases h : σ' (σ i) = j <;> simp [h]
  · intro l _ hl; simp [Ne.symm hl]
  · simp

theorem sp_one (t : Pair → ℤ) (ht : ∀ k, t k = 1) : sp 1 t = 1 := by
  ext i j; simp [sp, Matrix.one_apply, ht]

theorem SU2.mul {a a' : Op1} (h : SU2 a) (h' : SU2 a') : SU2 (a * a') := by
  refine ⟨?_, by rw [Matrix.det_mul, h.2, h'.2, one_mul]⟩
  rw [Matrix.conjTranspose_mul]
  calc a'ᴴ * aᴴ * (a * a') = a'ᴴ * (aᴴ * a) * a' := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h.1, Matrix.mul_one, h'.1]

theorem SU2.one : SU2 1 := ⟨by simp, by simp⟩

/-- `M` is realised by local `SU(2) ⊗ SU(2)` rotations: `(a ⊗ b) B = B M`, i.e. `Bᴴ (a ⊗ b) B = M`. -/
def RealSet (M : Matrix Pair Pair ℝ) : Prop :=
  ∃ a b : Op1, SU2 a ∧ SU2 b ∧ kron a b * magicB = magicB * cmat M

theorem RealSet.one : RealSet 1 :=
  ⟨1, 1, SU2.one, SU2.one, by rw [kron_one, cmat_one]; simp⟩

theorem RealSet.mul {M N : Matrix Pair Pair ℝ} (hM : RealSet M) (hN : RealSet N) :
    RealSet (M * N) := by
  obtain ⟨a, b, ha, hb, h⟩ := hM
  obtain ⟨a', b', ha', hb', h'⟩ := hN
  refine ⟨a * a', b * b', ha.mul ha', hb.mul hb', ?_⟩
  rw [← kron_mul, cmat_mul, Matrix.mul_assoc, h', ← Matrix.mul_assoc, h, Matrix.mul_assoc]

theorem RealSet.congr {M N : Matrix Pair Pair ℝ} (h : M = N) (hM : RealSet M) : RealSet N := h ▸ hM

theorem RealSet.bHb {M : Matrix Pair Pair ℝ} (h : RealSet M) :
    ∃ a b : Op1, SU2 a ∧ SU2 b ∧ magicBᴴ * kron a b * magicB = cmat M := by
  obtain ⟨a, b, ha, hb, h⟩ := h
  refine ⟨a, b, ha, hb, ?_⟩
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, magicB_unitary, Matrix.one_mul]

/-! ### Six rotations by a quarter turn in a coordinate plane of magic coordinates -/

noncomputable def sA1 : Op1 := !![-rt, -(Complex.I * rt); -(Complex.I * rt), -rt]
noncomputable def sA1' : Op1 := !![-rt, Complex.I * rt; Complex.I * rt, -rt]
noncomputable def sA2 : Op1 := !![-rt, -rt; rt, -rt]
noncomputable def sA2' : Op1 := !![-rt, rt; -rt, -rt]
noncomputable def sDp : Op1 := !![-rt - Complex.I * rt, 0; 0, -rt + Complex.I * rt]
noncomputable def sDm : Op1 := !![-rt + Complex.I * rt, 0; 0, -rt - Complex.I * rt]

theorem rt_sq : rt ^ 2 = 1 / 2 := by rw [pow_two]; exact rt_mul_rt

macro "su2_tac" : tactic => `(tactic| (
  have hrt2 : rt ^ 2 = 1 / 2 := rt_sq
  have hrt4 : rt ^ 4 = 1 / 4 := by rw [show rt ^ 4 = (rt ^ 2) ^ 2 by ring, hrt2]; norm_num
  have hrt3 : rt ^ 3 = rt / 2 := by rw [show rt ^ 3 = rt * rt ^ 2 by ring, hrt2]; ring
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [show Complex.I ^ 3 = Complex.I * Complex.I ^ 2 by ring, Complex.I_sq]; ring
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, rt_conj,
      Matrix.one_apply] <;>
    (try ring_nf) <;> (try simp only [Complex.I_sq, hI3, hrt2, hrt3, hrt4]) <;> (try ring_nf)
  · simp [Matrix.det_fin_two]
    (try ring_nf) <;> (try simp only [Complex.I_sq, hI3, hrt2, hrt3, hrt4]) <;> (try ring_nf) <;> (try simp)))

theorem su2_sA1 : SU2 sA1 := by unfold sA1; su2_tac
theorem su2_sA1' : SU2 sA1' := by unfold sA1'; su2_tac
theorem su2_sA2 : SU2 sA2 := by unfold sA2; su2_tac
theorem su2_sA2' : SU2 sA2' := by unfold sA2'; su2_tac
theorem su2_sDp : SU2 sDp := by unfold sDp; su2_tac
theorem su2_sDm : SU2 sDm := by unfold sDm; su2_tac

/-- `flipAt u` has a single sign `-1`, at `u`. -/
def flipAt (u : Pair) : Pair → ℤ := fun k => if k = u then -1 else 1

macro "gen_tac" : tactic => `(tactic| (
  have hrt2 : rt ^ 2 = 1 / 2 := rt_sq
  have hrt4 : rt ^ 4 = 1 / 4 := by rw [show rt ^ 4 = (rt ^ 2) ^ 2 by ring, hrt2]; norm_num
  have hrt3 : rt ^ 3 = rt / 2 := by rw [show rt ^ 3 = rt * rt ^ 2 by ring, hrt2]; ring
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [show Complex.I ^ 3 = Complex.I * Complex.I ^ 2 by ring, Complex.I_sq]; ring
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [kron, magicB, cmat, sp, flipAt, sA1, sA1', sA2, sA2', sDp, sDm, Equiv.swap_apply_def, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply] <;>
  (try ring_nf) <;> (try simp only [Complex.I_sq, hI3, hrt2, hrt3, hrt4]) <;> (try ring_nf) <;> (try simp)))

theorem gen01 : RealSet (sp (Equiv.swap (0, 0) (0, 1)) (flipAt (0, 0))) :=
  ⟨sA1, sA1, su2_sA1, su2_sA1, by gen_tac⟩
theorem gen02 : RealSet (sp (Equiv.swap (0, 0) (1, 0)) (flipAt (0, 0))) :=
  ⟨sA2, sA2', su2_sA2, su2_sA2', by gen_tac⟩
theorem gen03 : RealSet (sp (Equiv.swap (0, 0) (1, 1)) (flipAt (0, 0))) :=
  ⟨sDp, sDp, su2_sDp, su2_sDp, by gen_tac⟩
theorem gen12 : RealSet (sp (Equiv.swap (0, 1) (1, 0)) (flipAt (0, 1))) :=
  ⟨sDm, sDp, su2_sDm, su2_sDp, by gen_tac⟩
theorem gen13 : RealSet (sp (Equiv.swap (0, 1) (1, 1)) (flipAt (0, 1))) :=
  ⟨sA2, sA2, su2_sA2, su2_sA2, by gen_tac⟩
theorem gen23 : RealSet (sp (Equiv.swap (1, 0) (1, 1)) (flipAt (1, 0))) :=
  ⟨sA1', sA1, su2_sA1', su2_sA1, by gen_tac⟩

/-! ### Generating all signed permutations of determinant one -/

theorem gens (x y : Pair) (h : (pairEquiv x).val < (pairEquiv y).val) :
    RealSet (sp (Equiv.swap x y) (flipAt x)) := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;>
    first
    | (exfalso; revert h; decide)
    | exact gen01 | exact gen02 | exact gen03 | exact gen12 | exact gen13 | exact gen23

/-- `-1` at two places. -/
def dd2 (x y : Pair) : Pair → ℤ := fun k => if k = x ∨ k = y then -1 else 1

theorem dd2_realset (x y : Pair) (hxy : x ≠ y) (h : (pairEquiv x).val < (pairEquiv y).val) :
    RealSet (sp 1 (dd2 x y)) := by
  have := (gens x y h).mul (gens x y h)
  rw [sp_mul, Equiv.swap_mul_self] at this
  refine RealSet.congr ?_ this
  congr 1
  funext k
  by_cases hx : k = x
  · subst hx; simp [flipAt, dd2, Equiv.swap_apply_left, hxy.symm]
  · by_cases hy : k = y
    · subst hy; simp [flipAt, dd2, Equiv.swap_apply_right, hx]
    · simp [flipAt, dd2, Equiv.swap_apply_of_ne_of_ne hx hy, hx, hy]

theorem sp_one_mul (A B : Pair → ℤ) (hA : RealSet (sp 1 A)) (hB : RealSet (sp 1 B)) :
    RealSet (sp 1 (fun k => A k * B k)) := by
  have := hA.mul hB
  rw [sp_mul] at this
  simpa using this

theorem base (t : Pair → ℤ) (ht : ∀ k, t k = 1 ∨ t k = -1) (hp : ∏ k, t k = 1) :
    RealSet (sp 1 t) := by
  have hprod : ∏ k, t k = t (0, 0) * t (0, 1) * t (1, 0) * t (1, 1) := by
    simp [Fintype.prod_prod_type, Fin.prod_univ_two, mul_assoc]
  rw [hprod] at hp
  have key : ∀ t' : Pair → ℤ, (∀ i j, t (i, j) = t' (i, j)) → RealSet (sp 1 t') →
      RealSet (sp 1 t) := by
    intro t' h h'
    have : t = t' := by funext ⟨i, j⟩; exact h i j
    rw [this]; exact h'
  have d01 := dd2_realset (0, 0) (0, 1) (by decide) (by decide)
  have d02 := dd2_realset (0, 0) (1, 0) (by decide) (by decide)
  have d03 := dd2_realset (0, 0) (1, 1) (by decide) (by decide)
  have d12 := dd2_realset (0, 1) (1, 0) (by decide) (by decide)
  have d13 := dd2_realset (0, 1) (1, 1) (by decide) (by decide)
  have d23 := dd2_realset (1, 0) (1, 1) (by decide) (by decide)
  have d0123 := sp_one_mul _ _ d01 d23
  have d1 : RealSet (sp 1 (fun _ => 1)) := by
    rw [sp_one _ (fun _ => rfl)]; exact RealSet.one
  rcases ht (0, 0) with h00 | h00 <;> rcases ht (0, 1) with h01 | h01 <;>
  rcases ht (1, 0) with h10 | h10 <;> rcases ht (1, 1) with h11 | h11 <;>
  rw [h00, h01, h10, h11] at hp <;> norm_num at hp <;>
  first
  | (refine key _ (fun i j => ?_) d1; fin_cases i <;> fin_cases j <;> simp [dd2, h00, h01, h10, h11]; done)
  | (refine key _ (fun i j => ?_) d01; fin_cases i <;> fin_cases j <;> simp [dd2, h00, h01, h10, h11]; done)
  | (refine key _ (fun i j => ?_) d02; fin_cases i <;> fin_cases j <;> simp [dd2, h00, h01, h10, h11]; done)
  | (refine key _ (fun i j => ?_) d03; fin_cases i <;> fin_cases j <;> simp [dd2, h00, h01, h10, h11]; done)
  | (refine key _ (fun i j => ?_) d12; fin_cases i <;> fin_cases j <;> simp [dd2, h00, h01, h10, h11]; done)
  | (refine key _ (fun i j => ?_) d13; fin_cases i <;> fin_cases j <;> simp [dd2, h00, h01, h10, h11]; done)
  | (refine key _ (fun i j => ?_) d23; fin_cases i <;> fin_cases j <;> simp [dd2, h00, h01, h10, h11]; done)
  | (refine key _ (fun i j => ?_) d0123; fin_cases i <;> fin_cases j <;> simp [dd2, h00, h01, h10, h11]; done)

/-- The set of `(σ, t)` realised. -/
def Good (σ : Equiv.Perm Pair) : Prop :=
  ∀ t : Pair → ℤ, (∀ k, t k = 1 ∨ t k = -1) →
    (∏ k, t k) * ((Equiv.Perm.sign σ : ℤˣ) : ℤ) = 1 → RealSet (sp σ t)

theorem good_step (u v : Pair) (huv : u ≠ v) (h : (pairEquiv u).val < (pairEquiv v).val)
    (g : Equiv.Perm Pair) (hg : Good g) : Good (Equiv.swap u v * g) := by
  intro t ht hdet
  set t1 := flipAt u with ht1
  have ht1pm : ∀ k, t1 k = 1 ∨ t1 k = -1 := by
    intro k; simp only [ht1, flipAt]; split_ifs <;> simp
  have ht1sq : ∀ k, t1 k * t1 k = 1 := by
    intro k; rcases ht1pm k with h | h <;> rw [h] <;> norm_num
  have hprod1 : ∏ k, t1 k = -1 := by
    simp [ht1, flipAt, Finset.prod_ite_eq']
  have hprodg : ∏ i, t1 (g i) = -1 := by
    rw [Equiv.prod_comp g t1, hprod1]
  set t2 : Pair → ℤ := fun i => t i * t1 (g i) with ht2
  have ht2pm : ∀ k, t2 k = 1 ∨ t2 k = -1 := by
    intro k
    rcases ht k with h | h <;> rcases ht1pm (g k) with h' | h' <;> simp [ht2, h, h']
  have hp2 : ∏ k, t2 k = - ∏ k, t k := by
    simp only [ht2, Finset.prod_mul_distrib, hprodg]; ring
  have hs : ((Equiv.Perm.sign (Equiv.swap u v * g) : ℤˣ) : ℤ) = - ((Equiv.Perm.sign g : ℤˣ) : ℤ) := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap huv]; simp
  have hdet2 : (∏ k, t2 k) * ((Equiv.Perm.sign g : ℤˣ) : ℤ) = 1 := by
    rw [hs] at hdet; rw [hp2]; linarith
  have e : sp (Equiv.swap u v * g) t = sp g t2 * sp (Equiv.swap u v) t1 := by
    rw [sp_mul]
    congr 1
    funext i
    have := ht1sq (g i)
    simp only [ht2]; linear_combination (t i) * this.symm
  rw [e]
  exact (hg t2 ht2pm hdet2).mul (gens u v h)

theorem good_all (σ : Equiv.Perm Pair) : Good σ := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
    intro t ht hdet
    apply base t ht
    simpa using hdet
  | swap_mul f x y hxy ih =>
    rcases lt_or_gt_of_ne (show (pairEquiv x).val ≠ (pairEquiv y).val from
      fun h => hxy (pairEquiv.injective (Fin.ext h))) with h | h
    · exact good_step x y hxy h f ih
    · rw [Equiv.swap_comm]
      exact good_step y x hxy.symm h f ih

/-- **Realisation.** Every signed permutation matrix `D_t Π_σ` of determinant `1`
(`det = (∏ t) · sign σ`) is `Bᴴ (a ⊗ b) B` for some `a, b ∈ SU(2)`. -/
theorem exists_su2_realise (σ : Equiv.Perm Pair) (t : Pair → ℤ) (ht : ∀ k, t k = 1 ∨ t k = -1)
    (hdet : (∏ k, t k) * ((Equiv.Perm.sign σ : ℤˣ) : ℤ) = 1) :
    ∃ a b : Op1, SU2 a ∧ SU2 b ∧ magicBᴴ * kron a b * magicB = (sp σ t).map Complex.ofReal :=
  (good_all σ t ht hdet).bHb

/-! ### Overlaps of magic-diagonal states under local rotations -/

theorem zmat_local_psiMagP (d' : Pair → ℂ) (a b c e : Op1) (P Q : Matrix Pair Pair ℝ)
    (hP : kron a b * magicB = magicB * cmat P) (hQ : kron c e * magicB = magicB * cmat Q) :
    zmat (localApply a b c e (psiMagP d')) =
      magicB * (cmat P * Matrix.diagonal d' * (cmat Q)ᵀ) * magicBᵀ := by
  rw [zmat_localApply]
  unfold psiMagP; rw [zmat_ofZmat]
  have hK1 : kron a b = magicB * cmat P * magicBᴴ := by
    calc kron a b = kron a b * (magicB * magicBᴴ) := by rw [magicB_unitary', Matrix.mul_one]
      _ = (kron a b * magicB) * magicBᴴ := by rw [Matrix.mul_assoc]
      _ = _ := by rw [hP]
  have hK2 : kron c e = magicB * cmat Q * magicBᴴ := by
    calc kron c e = kron c e * (magicB * magicBᴴ) := by rw [magicB_unitary', Matrix.mul_one]
      _ = (kron c e * magicB) * magicBᴴ := by rw [Matrix.mul_assoc]
      _ = _ := by rw [hQ]
  have hBHT : (magicBᴴ)ᵀ = magicB.map star := by ext i j; simp [Matrix.conjTranspose_apply]
  have hBB : ∀ M : Mat4, magicBᴴ * (magicB * M) = M := by
    intro M; rw [← Matrix.mul_assoc, magicB_unitary, Matrix.one_mul]
  have hB2 : ∀ M : Mat4, magicBᵀ * (magicB.map star * M) = M := by
    intro M; rw [← Matrix.mul_assoc, bT_conjB, Matrix.one_mul]
  rw [hK1, hK2, Matrix.transpose_mul, Matrix.transpose_mul, hBHT]
  simp only [Matrix.mul_assoc, hBB, hB2]

theorem ip_local (d d' : Pair → ℂ) (a b c e : Op1) (P Q : Matrix Pair Pair ℝ)
    (hP : kron a b * magicB = magicB * cmat P) (hQ : kron c e * magicB = magicB * cmat Q) :
    ip (psiMagP d) (localApply a b c e (psiMagP d')) =
      ∑ k, conj (d k) * ∑ l, (P k l : ℂ) * (Q k l : ℂ) * d' l := by
  have hY : ∀ k, (cmat P * Matrix.diagonal d' * (cmat Q)ᵀ) k k =
      ∑ l, (P k l : ℂ) * (Q k l : ℂ) * d' l := by
    intro k
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, cmat, Matrix.map_apply, Matrix.transpose_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [ip_eq_fro, zmat_local_psiMagP d' a b c e P Q hP hQ]
  unfold psiMagP
  rw [zmat_ofZmat, fro_magic]
  simp only [fro, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · simp [hY k]
  · intro j _ hj; simp [hj.symm]
  · simp


/-! ### The rotation overlap and the easy direction of the Weyl-vertex formula -/

theorem ip_self (ψ : Psi) : ip ψ ψ = (normSqPsi ψ : ℂ) := by
  unfold ip normSqPsi
  push_cast
  simp only [Complex.normSq_eq_conj_mul_self]

theorem fro_unitary (K C : Mat4) (hK : Kᴴ * K = 1) (hC : Cᴴ * C = 1) (A B : Mat4) :
    fro (K * A * Cᵀ) (K * B * Cᵀ) = fro A B := by
  rw [fro_eq_trace, fro_eq_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    transpose_conjTranspose]
  have h1 : (C.map star * (Aᴴ * Kᴴ)) * (K * B * Cᵀ) = C.map star * (Aᴴ * B) * Cᵀ := by
    calc (C.map star * (Aᴴ * Kᴴ)) * (K * B * Cᵀ)
        = C.map star * (Aᴴ * (Kᴴ * K) * B) * Cᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hK]; simp only [Matrix.mul_one]
  rw [h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, unitary_transpose_mul hC, Matrix.one_mul]

theorem ip_localApply (a b c e : Op1) (ha : aᴴ * a = 1) (hb : bᴴ * b = 1) (hc : cᴴ * c = 1)
    (he : eᴴ * e = 1) (ψ φ : Psi) :
    ip (localApply a b c e ψ) (localApply a b c e φ) = ip ψ φ := by
  rw [ip_eq_fro, ip_eq_fro, zmat_localApply, zmat_localApply]
  exact fro_unitary _ _ (kron_unitary ha hb) (kron_unitary hc he) _ _

theorem normSqPsi_localApply (a b c e : Op1) (ha : aᴴ * a = 1) (hb : bᴴ * b = 1) (hc : cᴴ * c = 1)
    (he : eᴴ * e = 1) (φ : Psi) : normSqPsi (localApply a b c e φ) = normSqPsi φ := by
  have := ip_localApply a b c e ha hb hc he φ φ
  rw [ip_self, ip_self] at this
  exact_mod_cast this

theorem cs_complex {ι : Type*} [Fintype ι] (x y : ι → ℂ) :
    Complex.normSq (∑ i, conj (x i) * y i) ≤
      (∑ i, Complex.normSq (x i)) * (∑ i, Complex.normSq (y i)) := by
  have h1 : ‖∑ i, conj (x i) * y i‖ ≤ ∑ i, ‖x i‖ * ‖y i‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => by simp))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖x i‖) (fun i => ‖y i‖)
  simp only [Complex.normSq_eq_norm_sq]
  calc ‖∑ i, conj (x i) * y i‖ ^ 2 ≤ (∑ i, ‖x i‖ * ‖y i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem normSq_ip_le (ψ φ : Psi) :
    Complex.normSq (ip ψ φ) ≤ normSqPsi ψ * normSqPsi φ := by
  have h := cs_complex (fun x : Pair × Pair => zmat ψ x.1 x.2) (fun x : Pair × Pair => zmat φ x.1 x.2)
  have e1 : ip ψ φ = ∑ x : Pair × Pair, conj (zmat ψ x.1 x.2) * zmat φ x.1 x.2 := by
    rw [ip_eq_fro]; simp [fro, Fintype.sum_prod_type]
  have e2 : ∀ χ : Psi, normSqPsi χ = ∑ x : Pair × Pair, Complex.normSq (zmat χ x.1 x.2) := by
    intro χ; simp [normSqPsi, zmat, Fintype.sum_prod_type]
  rw [e1, e2 ψ, e2 φ]; exact h

/-- The best overlap of `ψ` with a local `SU(2)^{⊗4}` rotation of `φ`. -/
noncomputable def rotOverlap (ψ φ : Psi) : ℝ :=
  sSup {x : ℝ | ∃ a b c e : Op1, SU2 a ∧ SU2 b ∧ SU2 c ∧ SU2 e ∧
    x = Complex.normSq (ip ψ (localApply a b c e φ))}

theorem rotOverlap_bddAbove (ψ φ : Psi) :
    BddAbove {x : ℝ | ∃ a b c e : Op1, SU2 a ∧ SU2 b ∧ SU2 c ∧ SU2 e ∧
      x = Complex.normSq (ip ψ (localApply a b c e φ))} := by
  refine ⟨normSqPsi ψ * normSqPsi φ, ?_⟩
  rintro x ⟨a, b, c, e, ha, hb, hc, he, rfl⟩
  calc _ ≤ normSqPsi ψ * normSqPsi (localApply a b c e φ) := normSq_ip_le _ _
    _ = _ := by rw [normSqPsi_localApply a b c e ha.1 hb.1 hc.1 he.1]

theorem le_rotOverlap {ψ φ : Psi} {a b c e : Op1} (ha : SU2 a) (hb : SU2 b) (hc : SU2 c)
    (he : SU2 e) : Complex.normSq (ip ψ (localApply a b c e φ)) ≤ rotOverlap ψ φ :=
  le_csSup (rotOverlap_bddAbove ψ φ) ⟨a, b, c, e, ha, hb, hc, he, rfl⟩

theorem weylP_exists (σ : Equiv.Perm Pair) (s : Pair → ℤ) (hs : ∀ k, s k = 1 ∨ s k = -1)
    (hp : ∏ k, s k = 1) (d d' : Pair → ℂ) :
    ∃ a b c e : Op1, SU2 a ∧ SU2 b ∧ SU2 c ∧ SU2 e ∧
      ip (psiMagP d) (localApply a b c e (psiMagP d')) = ∑ k, conj (d k) * (s k : ℂ) * d' (σ k) := by
  set ε : ℤ := ((Equiv.Perm.sign σ : ℤˣ) : ℤ) with hε
  have hεpm : ε = 1 ∨ ε = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · left; simp [hε, h]
    · right; simp [hε, h]
  have hεε : ε * ε = 1 := by rcases hεpm with h | h <;> rw [h] <;> norm_num
  set τ : Pair → ℤ := fun k => if k = (0, 0) then ε else 1 with hτ
  have hτpm : ∀ k, τ k = 1 ∨ τ k = -1 := by
    intro k; simp only [hτ]; split_ifs
    · exact hεpm
    · left; rfl
  have hττ : ∀ k, τ k * τ k = 1 := by
    intro k; rcases hτpm k with h | h <;> rw [h] <;> norm_num
  have hτprod : ∏ k, τ k = ε := by simp [hτ, Finset.prod_ite_eq']
  have hdetQ : (∏ k, τ k) * ((Equiv.Perm.sign σ : ℤˣ) : ℤ) = 1 := by rw [hτprod]; exact hεε
  have hpm : ∀ k, τ k * s k = 1 ∨ τ k * s k = -1 := by
    intro k
    rcases hτpm k with h | h <;> rcases hs k with h' | h' <;> simp [h, h']
  have hdetP : (∏ k, (τ k * s k)) * ((Equiv.Perm.sign σ : ℤˣ) : ℤ) = 1 := by
    rw [Finset.prod_mul_distrib, hτprod, hp, mul_one]; exact hεε
  obtain ⟨a, b, ha, hb, hab⟩ := good_all σ (fun k => τ k * s k) hpm hdetP
  obtain ⟨c, e, hc, he, hce⟩ := good_all σ τ hτpm hdetQ
  refine ⟨a, b, c, e, ha, hb, hc, he, ?_⟩
  rw [ip_local d d' a b c e _ _ hab hce]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h' : ((τ k : ℤ) : ℂ) * (τ k : ℂ) = 1 := by exact_mod_cast hττ k
  rw [mul_assoc]
  congr 1
  rw [Finset.sum_eq_single (σ k)]
  · simp only [sp, Matrix.of_apply, ite_true]
    push_cast
    linear_combination ((s k : ℂ) * d' (σ k)) * h'
  · intro l _ hl; simp [sp, Ne.symm hl]
  · simp

/-- **Weyl-vertex lower bound (easy direction).**  Let `w = (σ, s)` be an element of `W(D₄)`:
`σ ∈ Sym(4)`, `s k = ±1`, `∏ s k = 1`, acting by `(w d')_k = s_k d'_{σ k}`.  Then
`|⟨ψ_d | w d'⟩|² ≤ rotOverlap ψ_d ψ_{d'}` (coordinate `k : Fin 4` ↔ magic vector `pairEquiv.symm k`,
i.e. `0,1,2,3 ↔ (0,0),(0,1),(1,0),(1,1)`). -/
theorem weyl_le_rotOverlap (σ : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤ)
    (hs : ∀ k, s k = 1 ∨ s k = -1) (hprod : ∏ k, s k = 1) (d d' : Fin 4 → ℂ) :
    Complex.normSq (∑ k, conj (d k) * (s k : ℂ) * d' (σ k)) ≤
      rotOverlap (psiMag d) (psiMag d') := by
  set σP : Equiv.Perm Pair := pairEquiv.trans (σ.trans pairEquiv.symm) with hσP
  obtain ⟨a, b, c, e, ha, hb, hc, he, h⟩ := weylP_exists σP (fun k => s (pairEquiv k))
    (fun k => hs _) (by rw [Equiv.prod_comp pairEquiv s]; exact hprod)
    (fun p => d (pairEquiv p)) (fun p => d' (pairEquiv p))
  have hsum : ∑ k : Pair, conj (d (pairEquiv k)) * (s (pairEquiv k) : ℂ) * d' (pairEquiv (σP k)) =
      ∑ k, conj (d k) * (s k : ℂ) * d' (σ k) := by
    rw [← Equiv.sum_comp pairEquiv (fun k => conj (d k) * (s k : ℂ) * d' (σ k))]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [σP]
  calc Complex.normSq (∑ k, conj (d k) * (s k : ℂ) * d' (σ k))
      = Complex.normSq (ip (psiMag d) (localApply a b c e (psiMag d'))) := by
        unfold psiMag; rw [h]; simp only [hσP] at hsum ⊢; rw [hsum]
    _ ≤ _ := le_rotOverlap ha hb hc he

/-- `psiMag` commutes with complex conjugation of the state. -/
theorem conj_magicB (i k : Pair) :
    conj (magicB i k) = (if k.2 = 1 then -1 else 1) * magicB i k := by
  obtain ⟨i1, i2⟩ := i
  obtain ⟨k1, k2⟩ := k
  fin_cases i1 <;> fin_cases i2 <;> fin_cases k1 <;> fin_cases k2 <;> simp [magicB, rt_conj]

theorem psiMagP_apply (d : Pair → ℂ) (a b c e : Fin 2) :
    psiMagP d a b c e = ∑ x, magicB (a, b) x * d x * magicB (c, e) x := by
  simp only [psiMagP, ofZmat, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp

theorem conj_psiMagP (d : Pair → ℂ) :
    Psi.conj (psiMagP d) = psiMagP (fun k => conj (d k)) := by
  funext a b c e
  show conj (psiMagP d a b c e) = psiMagP (fun k => conj (d k)) a b c e
  rw [psiMagP_apply, psiMagP_apply, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_mul, conj_magicB, conj_magicB]
  split_ifs <;> ring

theorem conj_psiMag (d : Fin 4 → ℂ) :
    Psi.conj (psiMag d) = psiMag (fun k => conj (d k)) := by
  unfold psiMag; exact conj_psiMagP _

/-- Corollary: overlap of a magic-diagonal state with its own complex conjugate. -/
theorem weyl_le_rotOverlap_conj (σ : Equiv.Perm (Fin 4)) (s : Fin 4 → ℤ)
    (hs : ∀ k, s k = 1 ∨ s k = -1) (hprod : ∏ k, s k = 1) (d : Fin 4 → ℂ) :
    Complex.normSq (∑ k, (s k : ℂ) * d k * d (σ k)) ≤
      rotOverlap (psiMag d) (Psi.conj (psiMag d)) := by
  rw [conj_psiMag]
  have := weyl_le_rotOverlap σ s hs hprod d (fun k => conj (d k))
  refine le_trans (le_of_eq ?_) this
  rw [← Complex.normSq_conj]
  congr 1
  simp only [map_sum, map_mul, Complex.conj_conj, map_intCast]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ### The maximiser `M₄` -/

theorem Xtarget_diag (ε : ℂ) :
    Xtarget ε = Matrix.diagonal (fun p => if p = sing then ε else rt6) := by
  ext i j
  by_cases hij : i = j
  · subst hij; by_cases hi : i = sing <;> simp [Xtarget, Pm_apply, Matrix.one_apply, hi]
  · have : ¬ (i = sing ∧ j = sing) := fun h => hij (h.1.trans h.2.symm)
    simp [Xtarget, Pm_apply, Matrix.one_apply, hij, Matrix.diagonal_apply, this]

/-- `M₄ = ψ_d` with `d = (1/√6, 1/√6, i/√2, 1/√6)`. -/
theorem M4_eq_psiMag : M4 = psiMag ![rt6, rt6, Complex.I * rt, rt6] := by
  have hd : (fun p : Pair => if p = sing then Complex.I * rt else rt6) =
      fun p => ![rt6, rt6, Complex.I * rt, rt6] (pairEquiv p) := by
    funext ⟨p1, p2⟩
    fin_cases p1 <;> fin_cases p2 <;> simp [sing] <;> rfl
  calc M4 = ofZmat (zmat M4) := rfl
    _ = ofZmat (magicB * Matrix.diagonal (fun p : Pair => if p = sing then Complex.I * rt else rt6) *
          magicBᵀ) := by rw [zmat_M4, Xtarget_diag]
    _ = psiMag _ := by unfold psiMag psiMagP; rw [hd]


/-! ### Determinant of the signed permutation matrices -/

theorem det_sp (σ : Equiv.Perm Pair) (t : Pair → ℤ) :
    (sp σ t).det = ((Equiv.Perm.sign σ : ℤˣ) : ℝ) * ∏ k, (t k : ℝ) := by
  have : sp σ t = Matrix.diagonal (fun i => (t i : ℝ)) *
      (σ.toPEquiv.toMatrix : Matrix Pair Pair ℝ) := by
    ext i j; simp [sp, Matrix.diagonal_mul, PEquiv.toMatrix_apply]
  rw [this, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permutation]; ring

/-- Realisation, stated with the determinant of the real matrix: every signed permutation matrix
`sp σ t` (entries `t k = ±1`) of determinant `1` is `Bᴴ (a ⊗ b) B` with `a, b ∈ SU(2)`. -/
theorem exists_su2_realise_det (σ : Equiv.Perm Pair) (t : Pair → ℤ) (ht : ∀ k, t k = 1 ∨ t k = -1)
    (hdet : (sp σ t).det = 1) :
    ∃ a b : Op1, SU2 a ∧ SU2 b ∧ magicBᴴ * kron a b * magicB = (sp σ t).map Complex.ofReal := by
  apply exists_su2_realise σ t ht
  rw [det_sp] at hdet
  have : (((∏ k, t k) * ((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℤ) : ℝ) = 1 := by
    push_cast; rw [mul_comm]; exact hdet
  exact_mod_cast this


end FormalResearch.FrameFree
