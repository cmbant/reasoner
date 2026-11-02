import FormalResearch.FourQubitEntropy.QVBlock.Assembly

/-!
# Integer-certificate form of the top theorem

`quad_eq_zero_of_int_certificate`: the hypotheses of `quad_eq_zero_of_certificate` stated over `ℤ`
(each is a decidable equation or `≠ 0` between explicit integer matrices), and the conclusion over
any field of characteristic `0`, for the integer matrix `K = ∑_k ⊗_q X k q` mapped into `𝕜`.
The inverse of `C` is given as `Cinv` with `Cinv C = C Cinv = D • 1`, `D ≠ 0`.
-/

open scoped Matrix BigOperators

namespace FormalResearch.FourQubitEntropy.QVBlock

set_option linter.unusedSectionVars false

section
variable {R S : Type*} [CommRing R] [CommRing S]
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

theorem kronPi_map (f : R →+* S) {m n : Q → Type*} (X : ∀ q, Matrix (m q) (n q) R) :
    (kronPi X).map f = kronPi (fun q => (X q).map f) := by
  ext a b
  simp [map_prod]

variable {J : Type*} [Fintype J] [DecidableEq J] (dim : J → ℕ) {mult : J → ℕ}

theorem blk_map (f : R →+* S) (X : ∀ j, Matrix (Fin (mult j)) (Fin (mult j)) R) :
    (blk dim X).map f = blk dim (fun j => (X j).map f) := by
  ext ⟨j, k, μ⟩ ⟨j', k', μ'⟩
  by_cases h : j = j'
  · subst h
    simp only [Matrix.map_apply, blk_same]
    split_ifs <;> simp
  · simp [Matrix.map_apply, blk_ne dim _ h]

theorem slotPerm_map (f : R →+* S) {σ : Type*} [Fintype σ] [DecidableEq σ] {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    (slotPerm R π : Matrix (Fin n → σ) (Fin n → σ) R).map f = slotPerm S π := by
  ext a c
  change f (if a = slotAct π c then 1 else 0) = if a = slotAct π c then 1 else 0
  split_ifs <;> simp

theorem map_int_smul_one {𝕜 : Type*} [Field 𝕜] {a : Type*} [Fintype a] [DecidableEq a]
    (M : Matrix a a ℤ) (r : ℤ) (h : M = r • 1) :
    M.map (Int.castRingHom 𝕜) = (r : 𝕜) • (1 : Matrix a a 𝕜) := by
  subst h
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem sum_kronPi_map (f : R →+* S) {κ : Type*} [Fintype κ] {m : Q → Type*}
    [∀ q, Fintype (m q)] (Y : κ → ∀ q, Matrix (m q) (m q) R) :
    (∑ k, kronPi (Y k)).map f = ∑ k, kronPi (fun q => (Y k q).map f) := by
  ext a b
  simp [Matrix.sum_apply, Matrix.map_apply, map_sum, kronPi_apply, map_prod]

theorem det_submatrix_map_ne_zero {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {m : Type*} [Fintype m]
    [DecidableEq m] {k : ℕ} (A : Matrix m (Fin k) ℤ) (piv : Fin k → m)
    (h : (A.submatrix piv id).det ≠ 0) :
    ((A.map (Int.castRingHom 𝕜)).submatrix piv id).det ≠ 0 := by
  rw [Matrix.submatrix_map]
  intro h0
  apply h
  have := RingHom.map_det (Int.castRingHom 𝕜) (A.submatrix piv id)
  rw [RingHom.mapMatrix_apply, h0] at this
  exact RingHom.injective_int _ (this.trans (map_zero _).symm)

end

section
variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {n : ℕ}
variable {J : Type*} [Fintype J] [DecidableEq J] (dim : J → ℕ) {mult : J → ℕ}
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- **Top theorem, integer certificate form.** -/
theorem quad_eq_zero_of_int_certificate (hdim : ∀ j, 0 < dim j)
    (C : Matrix (Idx dim mult) (Fin n → σ) ℤ) (Cinv : Matrix (Fin n → σ) (Idx dim mult) ℤ)
    (D : ℤ) (hD : D ≠ 0) (hCi : Cinv * C = D • 1) (hiC : C * Cinv = D • 1)
    {ι : Type*} (gens : ι → Equiv.Perm (Fin n)) (w : Equiv.Perm (Fin n) → List ι)
    (hw : ∀ g, ((w g).map gens).prod = g)
    (ρ0 : ι → ∀ j, Matrix (Fin (mult j)) (Fin (mult j)) ℤ)
    (hρ0 : ∀ i, C * slotPerm ℤ (gens i) = blk dim (ρ0 i) * C)
    {κ : Type*} [Fintype κ] (X : κ → Q → Matrix (Fin n → σ) (Fin n → σ) ℤ)
    (Xh : κ → Q → ∀ j, Matrix (Fin (mult j)) (Fin (mult j)) ℤ)
    (hX : ∀ k q, C * X k q = blk dim (Xh k q) * C)
    (nn : (Q → J) → ℕ)
    (V W : ∀ p : Q → J, Matrix (∀ q, Fin (mult (p q))) (Fin (nn p)) ℤ)
    (hV : ∀ p i, kronPi (fun q => ρ0 i (p q)) * V p = V p)
    (hW : ∀ p i, (kronPi (fun q => ρ0 i (p q)))ᵀ * W p = W p)
    (pivV pivW : ∀ p : Q → J, Fin (nn p) → (∀ q, Fin (mult (p q))))
    (hdetV : ∀ p, ((V p).submatrix (pivV p) id).det ≠ 0)
    (hdetW : ∀ p, ((W p).submatrix (pivW p) id).det ≠ 0)
    (hchar : ∀ p, (Fintype.card (Equiv.Perm (Fin n)) : ℤ) * nn p =
      ∑ g : Equiv.Perm (Fin n), ∏ q, (((w g).map (fun i => ρ0 i (p q))).prod).trace)
    (hcheck : ∀ p, (W p)ᵀ * (∑ k, kronPi (fun q => Xh k q (p q))) * V p = 0)
    (z' z : (Q → σ) → 𝕜) :
    copyPower z' n ⬝ᵥ (((∑ k, kronPi (X k)).map (Int.cast : ℤ → 𝕜)) *ᵥ copyPower z n) = 0 := by
  let f : ℤ →+* 𝕜 := Int.castRingHom 𝕜
  have hf : ∀ x : ℤ, f x = (x : 𝕜) := fun x => rfl
  have hD' : (D : 𝕜) ≠ 0 := by exact_mod_cast hD
  have hinv1 : ((D : 𝕜)⁻¹ • Cinv.map f) * C.map f = 1 := by
    rw [Matrix.smul_mul, ← Matrix.map_mul, map_int_smul_one _ D hCi, smul_smul, inv_mul_cancel₀ hD', one_smul]
  have hinv2 : C.map f * ((D : 𝕜)⁻¹ • Cinv.map f) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.map_mul, map_int_smul_one _ D hiC, smul_smul, inv_mul_cancel₀ hD', one_smul]
  have hρ0' : ∀ i, C.map f * slotPerm 𝕜 (gens i) =
      blk dim (fun j => (ρ0 i j).map f) * C.map f := by
    intro i
    have h1 := congrArg (fun A => A.map f) (hρ0 i)
    exact (congrArg (fun A => C.map f * A) (slotPerm_map f (gens i)).symm).trans
      (Matrix.map_mul.symm.trans (h1.trans (Matrix.map_mul.trans
        (congrArg (fun A => A * C.map f) (blk_map dim f _)))))
  have hX' : ∀ k q, C.map f * (X k q).map f =
      blk dim (fun j => (Xh k q j).map f) * C.map f := by
    intro k q
    have h1 := congrArg (fun A => A.map f) (hX k q)
    exact Matrix.map_mul.symm.trans (h1.trans (Matrix.map_mul.trans
        (congrArg (fun A => A * C.map f) (blk_map dim f _))))
  have hkron : ∀ (p : Q → J) (Y : ∀ q, Matrix (Fin (mult (p q))) (Fin (mult (p q))) ℤ),
      kronPi (fun q => (Y q).map f) = (kronPi Y).map f := fun p Y => (kronPi_map f Y).symm
  have hV' : ∀ p i, kronPi (fun q => (fun j => (ρ0 i j).map f) (p q)) * (V p).map f
      = (V p).map f := by
    intro p i
    rw [hkron p (fun q => ρ0 i (p q)), ← Matrix.map_mul, hV p i]
  have hW' : ∀ p i, (kronPi (fun q => (fun j => (ρ0 i j).map f) (p q)))ᵀ * (W p).map f
      = (W p).map f := by
    intro p i
    rw [hkron p (fun q => ρ0 i (p q)), ← Matrix.transpose_map, ← Matrix.map_mul, hW p i]
  have hchar' : ∀ p, (Fintype.card (Equiv.Perm (Fin n)) : 𝕜) * nn p =
      ∑ g : Equiv.Perm (Fin n), ∏ q,
        (((w g).map (fun i => (fun j => (ρ0 i j).map f) (p q))).prod).trace := by
    intro p
    have h1 := congrArg (fun x : ℤ => (x : 𝕜)) (hchar p)
    simp only [Int.cast_mul, Int.cast_natCast, Int.cast_sum, Int.cast_prod] at h1
    rw [h1]
    refine Finset.sum_congr rfl (fun g _ => Finset.prod_congr rfl (fun q _ => ?_))
    have hl : ∀ l : List ι, (l.map (fun i => (ρ0 i (p q)).map f)).prod =
        ((l.map (fun i => ρ0 i (p q))).prod).map f := by
      intro l
      induction l with
      | nil => ext i j; simp [Matrix.one_apply, Matrix.map_apply]
      | cons a t ih => simp only [List.map_cons, List.prod_cons, ih, Matrix.map_mul]
    rw [hl]
    simp [Matrix.trace, Matrix.map_apply]
  have hcheck' : ∀ p, ((W p).map f)ᵀ * (∑ k, kronPi (fun q => (fun j => (Xh k q j).map f) (p q)))
      * (V p).map f = 0 := by
    intro p
    have h1 := congrArg (fun A => A.map f) (hcheck p)
    simp only [Matrix.map_mul, Matrix.transpose_map] at h1
    have hS' : (∑ k, kronPi (fun q => Xh k q (p q))).map f =
        ∑ k, kronPi (fun q => (Xh k q (p q)).map f) :=
      sum_kronPi_map f (fun k q => Xh k q (p q))
    rw [hS'] at h1
    simpa using h1
  have key := quad_eq_zero_of_certificate dim hdim (C.map f) ((D : 𝕜)⁻¹ • Cinv.map f) hinv1 hinv2
    gens w hw (fun i j => (ρ0 i j).map f) hρ0'
    (fun k q => (X k q).map f) (fun k q j => (Xh k q j).map f) hX' nn
    (fun p => (V p).map f) (fun p => (W p).map f) hV' hW'
    pivV pivW (fun p => det_submatrix_map_ne_zero _ _ (hdetV p))
    (fun p => det_submatrix_map_ne_zero _ _ (hdetW p)) hchar' hcheck' z' z
  have hS2 : (∑ k, kronPi (X k)).map (Int.cast : ℤ → 𝕜) =
      ∑ k, kronPi (fun q => (X k q).map f) := sum_kronPi_map f X
  rw [hS2]
  exact key

end

end FormalResearch.FourQubitEntropy.QVBlock
