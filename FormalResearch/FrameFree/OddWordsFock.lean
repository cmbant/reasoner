import Mathlib

/-!
# Total-spin ladder operators on `(ℂ²)^{⊗n}`, real matrix form (Paper P, `prop:oddwords` (iii))

Namespace `FormalResearch.FrameFree.OddWords`.  Claim class: **proved**.

On the computational basis `Cube n = Fin n → Fin 2` (real matrices), `Lm = Σ_i σ_i^-` is the total
spin lowering operator (it flips one `0` to `1`), `Rm = Lmᵀ` the raising operator and
`Hm = Σ_i σ_i^z = diag (n - 2 |x|)`.  Local operators `E i a` (the 2×2 matrix `a` on site `i`) commute
across sites and multiply within a site, which gives `[Rm, Lm] = Hm` (`Rm_mul_Lm_sub`) and
`[Hm, Lm] = -2 Lm` (`Hm_mul_Lm_sub`).  `Lm x y` is the indicator that `x` is `y` with one more `1`
(`Lm_apply`); the slot permutation matrices commute with `Lm` (`rperm_mul_Lm`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Matrix

namespace FormalResearch.FrameFree.OddWords

/-- The computational basis of `n` qubits. -/
abbrev Cube (n : ℕ) := Fin n → Fin 2

variable {n : ℕ}

/-- Hamming weight. -/
def wt (x : Cube n) : ℕ := ∑ i, (x i : ℕ)

/-- Product operator `⊗_i v_i` on real matrices. -/
def rtens (v : Fin n → Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Cube n) (Cube n) ℝ :=
  Matrix.of fun x y => ∏ i, v i (x i) (y i)

theorem rtens_mul (u v : Fin n → Matrix (Fin 2) (Fin 2) ℝ) :
    rtens u * rtens v = rtens (fun i => u i * v i) := by
  ext x z
  simp only [Matrix.mul_apply, rtens, Matrix.of_apply]
  simp_rw [← Finset.prod_mul_distrib]
  have := Finset.sum_prod_piFinset (Finset.univ : Finset (Fin 2))
    (fun i b => u i (x i) b * v i b (z i))
  simpa [Fintype.piFinset_univ] using this

theorem rtens_transpose (v : Fin n → Matrix (Fin 2) (Fin 2) ℝ) :
    (rtens v)ᵀ = rtens (fun i => (v i)ᵀ) := by
  ext x y; simp [rtens]

/-- The 2×2 matrix `a` on site `i`, identity elsewhere. -/
def E (i : Fin n) (a : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Cube n) (Cube n) ℝ :=
  rtens (Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) i a)

theorem E_apply (i : Fin n) (a : Matrix (Fin 2) (Fin 2) ℝ) (x y : Cube n) :
    E i a x y = a (x i) (y i) * ∏ j ∈ univ.erase i, (if x j = y j then (1 : ℝ) else 0) := by
  have h : ∀ j, Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) i a j (x j) (y j)
      = Function.update (fun j => (1 : Matrix (Fin 2) (Fin 2) ℝ) (x j) (y j)) i (a (x i) (y i)) j := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  simp only [E, rtens, Matrix.of_apply, h]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
  congr 1
  refine Finset.prod_congr (by ext; simp) fun j _ => ?_
  simp [Matrix.one_apply]

theorem E_mul_same (i : Fin n) (a b : Matrix (Fin 2) (Fin 2) ℝ) : E i a * E i b = E i (a * b) := by
  rw [E, E, E, rtens_mul]
  congr 1; funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

theorem E_comm {i j : Fin n} (hij : i ≠ j) (a b : Matrix (Fin 2) (Fin 2) ℝ) :
    E i a * E j b = E j b * E i a := by
  rw [E, E, rtens_mul, rtens_mul]
  congr 1; funext k
  by_cases hi : k = i
  · rw [hi, Function.update_self, Function.update_of_ne hij]; simp
  · by_cases hj : k = j
    · rw [hj, Function.update_self, Function.update_of_ne hij.symm]; simp
    · simp [Function.update_of_ne hi, Function.update_of_ne hj]

theorem E_sub (i : Fin n) (a b : Matrix (Fin 2) (Fin 2) ℝ) : E i (a - b) = E i a - E i b := by
  ext x y; simp [E_apply, sub_mul]

theorem E_smul (i : Fin n) (c : ℝ) (a : Matrix (Fin 2) (Fin 2) ℝ) : E i (c • a) = c • E i a := by
  ext x y; simp [E_apply, mul_assoc]

theorem E_transpose (i : Fin n) (a : Matrix (Fin 2) (Fin 2) ℝ) : (E i a)ᵀ = E i aᵀ := by
  rw [E, E, rtens_transpose]
  congr 1; funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

/-- Local lowering `|0⟩ ↦ |1⟩`. -/
def sM : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun a b => if a = 1 ∧ b = 0 then 1 else 0

/-- Local `σ^z`. -/
def zM : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun a b => if a = b then (if a = 0 then 1 else -1) else 0

/-- Total lowering operator. -/
def Lm (n : ℕ) : Matrix (Cube n) (Cube n) ℝ := ∑ i : Fin n, E i sM

/-- Total `σ^z`. -/
def Hm (n : ℕ) : Matrix (Cube n) (Cube n) ℝ := ∑ i : Fin n, E i zM

theorem Lm_transpose : (Lm n)ᵀ = ∑ i : Fin n, E i sMᵀ := by
  rw [Lm, Matrix.transpose_sum]; simp [E_transpose]

theorem sMt_mul_sM_sub : sMᵀ * sM - sM * sMᵀ = zM := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [sM, zM, Matrix.mul_apply, Fin.sum_univ_two]

theorem zM_mul_sM_sub : zM * sM - sM * zM = (-2 : ℝ) • sM := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [sM, zM, Matrix.mul_apply] <;> norm_num

/-- `[Rm, Lm] = Hm`. -/
theorem Rm_mul_Lm_sub : (Lm n)ᵀ * Lm n - Lm n * (Lm n)ᵀ = Hm n := by
  rw [Lm_transpose, Lm, Hm, Finset.sum_mul_sum, Finset.sum_mul_sum]
  have h : ∑ i : Fin n, ∑ j : Fin n, E i sM * E j sMᵀ = ∑ i : Fin n, ∑ j : Fin n, E j sM * E i sMᵀ :=
    Finset.sum_comm
  rw [h, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · rw [E_mul_same, E_mul_same, ← E_sub, sMt_mul_sM_sub]
  · intro j _ hj
    rw [E_comm hj, sub_self]
  · simp

/-- `[Hm, Lm] = -2 Lm`. -/
theorem Hm_mul_Lm_sub : Hm n * Lm n - Lm n * Hm n = (-2 : ℝ) • Lm n := by
  rw [Lm, Hm, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.smul_sum]
  have h : ∑ i : Fin n, ∑ j : Fin n, E i sM * E j zM = ∑ i : Fin n, ∑ j : Fin n, E j sM * E i zM :=
    Finset.sum_comm
  rw [h, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · rw [E_mul_same, E_mul_same, ← E_sub, zM_mul_sM_sub, E_smul]
  · intro j _ hj
    rw [E_comm hj, sub_self]
  · simp

/-- Entries of `Lm`: the number of sites `i` with `x i = 1` and `y = x` with site `i` reset to `0`. -/
theorem Lm_apply (x y : Cube n) :
    Lm n x y = ∑ i : Fin n, if x i = 1 ∧ y = Function.update x i 0 then (1 : ℝ) else 0 := by
  rw [Lm, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [E_apply, Finset.prod_boole]
  by_cases h : x i = 1 ∧ y = Function.update x i 0
  · obtain ⟨h1, h2⟩ := h
    have h3 : y i = 0 := by rw [h2]; simp
    have h4 : ∀ j ∈ univ.erase i, x j = y j := by
      intro j hj; rw [h2, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have e : sM (x i) (y i) = 1 := by simp [sM, h1, h3]
    rw [if_pos h4, e, if_pos ⟨h1, h2⟩, one_mul]
  · rw [if_neg h]
    by_cases h1 : x i = 1 ∧ y i = 0
    · have : ¬ ∀ j ∈ univ.erase i, x j = y j := by
        intro h4; apply h; refine ⟨h1.1, funext fun j => ?_⟩
        by_cases hj : j = i
        · subst hj; simpa using h1.2
        · rw [Function.update_of_ne hj]; exact (h4 j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩)).symm
      rw [if_neg this, mul_zero]
    · have e : sM (x i) (y i) = 0 := by simp only [sM, Matrix.of_apply]; exact if_neg h1
      rw [e, zero_mul]

theorem wt_le (x : Cube n) : wt x ≤ n := by
  calc wt x = ∑ i, (x i : ℕ) := rfl
    _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => by have := (x i).2; omega
    _ = n := by simp

theorem Hm_eq_diagonal : Hm n = Matrix.diagonal (fun x : Cube n => (n : ℝ) - 2 * (wt x : ℝ)) := by
  ext x y
  rw [Hm, Matrix.sum_apply, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    have : ∀ i ∈ (Finset.univ : Finset (Fin n)), E i zM x x = 1 - 2 * ((x i : ℕ) : ℝ) := by
      intro i _
      rw [E_apply]
      simp only [if_true, Finset.prod_const_one, mul_one]
      generalize x i = a
      fin_cases a <;> simp [zM] <;> norm_num
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [wt]
  · rw [if_neg hxy]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [E_apply]
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
      by_contra h; push Not at h; exact hxy (funext h)
    by_cases hji : j = i
    · subst hji
      have : zM (x j) (y j) = 0 := by simp [zM, hj]
      rw [this, zero_mul]
    · rw [Finset.prod_eq_zero (i := j) (Finset.mem_erase.2 ⟨hji, Finset.mem_univ _⟩)
        (by simp [hj]), mul_zero]

/-- The real slot-permutation matrix `(P_σ ψ)(x) = ψ(x ∘ σ)`. -/
def rperm (σ : Equiv.Perm (Fin n)) : Matrix (Cube n) (Cube n) ℝ :=
  Matrix.of fun x y => if y = x ∘ σ then 1 else 0

theorem rperm_mul_apply (σ : Equiv.Perm (Fin n)) (A : Matrix (Cube n) (Cube n) ℝ) (x z : Cube n) :
    (rperm σ * A) x z = A (x ∘ σ) z := by
  simp [rperm, Matrix.mul_apply]

theorem mul_rperm_apply (σ : Equiv.Perm (Fin n)) (A : Matrix (Cube n) (Cube n) ℝ) (x z : Cube n) :
    (A * rperm σ) x z = A x (z ∘ ⇑(σ⁻¹)) := by
  simp only [rperm, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (z ∘ ⇑(σ⁻¹))]
  · have : z = (z ∘ ⇑(σ⁻¹)) ∘ ⇑σ := by ext i; simp
    rw [if_pos this]
  · intro y _ hy
    rw [if_neg]
    intro h; apply hy; rw [h]; ext i; simp
  · simp

theorem Lm_perm (σ : Equiv.Perm (Fin n)) (x z : Cube n) :
    Lm n (x ∘ σ) z = Lm n x (z ∘ ⇑(σ⁻¹)) := by
  rw [Lm_apply, Lm_apply,
    ← Equiv.sum_comp σ (fun j => if x j = 1 ∧ z ∘ ⇑(σ⁻¹) = Function.update x j 0 then (1 : ℝ) else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : (z = Function.update (x ∘ σ) i 0) ↔ (z ∘ ⇑(σ⁻¹) = Function.update x (σ i) 0) := by
    constructor
    · intro h; subst h
      funext k
      by_cases hk : k = σ i
      · simp [Function.update_apply, hk]
      · have : ¬ (i = σ.symm k) := fun h' => hk (by rw [h']; simp)
        have this' : ¬ (σ.symm k = i) := fun h' => this h'.symm
        simp [Function.update_apply, hk, this, this']
    · intro h; funext m
      have := congrFun h (σ m)
      have h' : σ⁻¹ (σ m) = m := by simp
      simp only [Function.comp_apply, h'] at this
      rw [this]
      by_cases hm : m = i
      · subst hm; simp
      · have : σ m ≠ σ i := fun h'' => hm (σ.injective h'')
        simp [Function.update_apply, this, hm]
  simp only [Function.comp_apply, e]

/-- The slot permutations commute with the total lowering operator. -/
theorem rperm_mul_Lm (σ : Equiv.Perm (Fin n)) : rperm σ * Lm n = Lm n * rperm σ := by
  ext x z
  rw [rperm_mul_apply, mul_rperm_apply, Lm_perm]

end FormalResearch.FrameFree.OddWords
