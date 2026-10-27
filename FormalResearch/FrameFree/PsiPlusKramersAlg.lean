import FormalResearch.FrameFree.Sharing

/-!
# `ψ₊`: matrix identities for the Kramers bound

With `V = 1 + i SWAP` (`Vg`, so `V Vᴴ = 2`), `Y` the Pauli matrix, `M₀ = (n·σ) Y` for a real vector
`n = (p,q,r)`, and `Ω = Y ⊗ M₀` (`Ω Ωᴴ = |n|²`), this file proves the algebra behind the bound
`F_C(ψ₊) ≤ 1/2` (`PsiPlusKramersCore`), for the exchange gate `√SWAP`:

* `exists_gauge`: for every `E` there is a real `n ≠ 0` with `K = E M₀` symmetric (rank--nullity);
* `Vg_Y_K_Vg`: `V (Y ⊗ K) V = (1+i)(Y ⊗ K + i K ⊗ Y)` for symmetric `K` (a rank-two matrix);
* `N_formula`: hence `N = Z Ω V = (A ⊗ B) V (Y ⊗ K) V` has two product terms, `Z = (A ⊗ B) V (1 ⊗ E)`;
* `Wm_flat`: the realigned matrix `W_{(c,a),(d,b)} = T_{(a,b),(c,d)}` of `T = Vᴴ Ωᴴ V` is flat,
  `W Wᴴ = 4 |n|² · 1`.
-/

open scoped Matrix ComplexConjugate Kronecker
open FormalResearch.FrameFree FormalResearch.FrameFree.Sharing FormalResearch.FrameFree.NQubit

namespace FormalResearch.FrameFree.PsiPlusKramers

theorem I_pow_four : Complex.I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
theorem I_pow_five : Complex.I ^ 5 = Complex.I := by rw [pow_succ, I_pow_four]; ring
theorem I_pow_six : Complex.I ^ 6 = -1 := by rw [pow_succ, I_pow_five, Complex.I_mul_I]
theorem I_pow_seven : Complex.I ^ 7 = -Complex.I := by rw [pow_succ, I_pow_six]; ring
theorem I_pow_eight : Complex.I ^ 8 = 1 := by rw [pow_succ, I_pow_seven]; simp

/-- `V = 1 + i SWAP`. -/
noncomputable def Vg : Mat4 := Ug 1 Complex.I

/-- Pauli `Y`. -/
def Yp : Op1 := !![0, -Complex.I; Complex.I, 0]

/-- `M₀ = (n·σ) Y` for the real vector `n = (p,q,r)`. -/
def M0 (p q r : ℝ) : Op1 :=
  !![(q : ℂ) + Complex.I * p, -Complex.I * r; -Complex.I * r, (q : ℂ) - Complex.I * p]

theorem Vg_conjT : Vgᴴ = Ug 1 (-Complex.I) := by
  rw [Vg, Ug_conjT]; simp

theorem Vg_mul_Vg_conjT : Vg * Vgᴴ = (2 : ℂ) • (1 : Mat4) := by
  rw [Vg_conjT]
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Vg, Ug, Sw, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply] <;> ring_nf <;> norm_num

theorem Yp_mul_conjT : Yp * Ypᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Yp, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

theorem M0_mul_conjT (p q r : ℝ) : M0 p q r * (M0 p q r)ᴴ = ((p ^ 2 + q ^ 2 + r ^ 2 : ℝ) : ℂ) • (1 : Op1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    <;> ring_nf <;> simp <;> ring_nf


theorem Vg_Y_K_Vg (a b d : ℂ) :
    Vg * (Yp ⊗ₖ !![a, b; b, d]) * Vg =
      (1 + Complex.I) • (Yp ⊗ₖ !![a, b; b, d] + Complex.I • (!![a, b; b, d] ⊗ₖ Yp)) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Vg, Ug, Sw, Yp, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, Matrix.kroneckerMap_apply] <;>
    ring_nf


/-- `T = V† Ω† V`, `Ω = Y ⊗ M₀`. -/
noncomputable def Tm (p q r : ℝ) : Mat4 := Vgᴴ * (Yp ⊗ₖ M0 p q r)ᴴ * Vg

/-- The realigned matrix `W_{(c,a),(d,b)} = T_{(a,b),(c,d)}`. -/
noncomputable def Wm (p q r : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun ca db => Tm p q r (ca.2, db.2) (ca.1, db.1)

theorem Wm_flat (p q r : ℝ) :
    Wm p q r * (Wm p q r)ᴴ = ((4 * (p ^ 2 + q ^ 2 + r ^ 2) : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext ⟨c, a⟩ ⟨c', a'⟩
  fin_cases c <;> fin_cases a <;> fin_cases c' <;> fin_cases a' <;>
    simp [Wm, Tm, Vg, Ug, Sw, Yp, M0, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, Matrix.kroneckerMap_apply,
      Matrix.conjTranspose_apply] <;> ring_nf <;>
    simp only [Complex.I_sq, I_pow_four, I_pow_five, I_pow_six, I_pow_seven, I_pow_eight] <;>
    ring_nf

/-- A nonzero real solution of one complex linear equation in three real unknowns
(rank--nullity: `dim_ℝ ℂ = 2 < 3`). -/
theorem exists_real_kernel (c₁ c₂ c₃ : ℂ) :
    ∃ p q r : ℝ, 0 < p ^ 2 + q ^ 2 + r ^ 2 ∧ (p : ℂ) * c₁ + q * c₂ + r * c₃ = 0 := by
  let f : (Fin 3 → ℝ) →ₗ[ℝ] ℂ :=
    { toFun := fun v => ((v 0 : ℝ) : ℂ) * c₁ + ((v 1 : ℝ) : ℂ) * c₂ + ((v 2 : ℝ) : ℂ) * c₃
      map_add' := by intro v w; simp only [Pi.add_apply, Complex.ofReal_add]; ring
      map_smul' := by intro a v; simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
        RingHom.id_apply, Complex.real_smul]; ring }
  have hk : LinearMap.ker f ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp [Complex.finrank_real_complex])
  obtain ⟨v, hv, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  refine ⟨v 0, v 1, v 2, ?_, hv⟩
  by_contra hcon
  apply hne
  have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have h2 : v 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  funext i; fin_cases i <;> simpa


/-- `Ω = Y ⊗ M₀`. -/
def Om (p q r : ℝ) : Mat4 := Yp ⊗ₖ M0 p q r

theorem Om_mul_conjT (p q r : ℝ) :
    Om p q r * (Om p q r)ᴴ = ((p ^ 2 + q ^ 2 + r ^ 2 : ℝ) : ℂ) • (1 : Mat4) := by
  unfold Om
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Yp_mul_conjT, M0_mul_conjT,
    Matrix.kronecker_smul, Matrix.one_kronecker_one]

/-- `Z = (A ⊗ B) V (1 ⊗ E)`. -/
noncomputable def Zm (A B E : Op1) : Mat4 := (A ⊗ₖ B) * Vg * ((1 : Op1) ⊗ₖ E)

/-- The gauge: a real `n ≠ 0` with `E (n·σ) Y` symmetric. -/
theorem exists_gauge (E : Op1) :
    ∃ p q r : ℝ, 0 < p ^ 2 + q ^ 2 + r ^ 2 ∧ (E * M0 p q r) 0 1 = (E * M0 p q r) 1 0 := by
  obtain ⟨p, q, r, hpos, h⟩ := exists_real_kernel (-Complex.I * (E 0 1 + E 1 0)) (E 0 1 - E 1 0)
    (-Complex.I * (E 0 0 - E 1 1))
  refine ⟨p, q, r, hpos, ?_⟩
  simp only [Matrix.mul_apply, Fin.sum_univ_two, M0]
  simp
  linear_combination h

theorem N_formula (A B E : Op1) (p q r : ℝ) (hK : (E * M0 p q r) 0 1 = (E * M0 p q r) 1 0) :
    Zm A B E * Om p q r * Vg =
      (1 + Complex.I) • ((A * Yp) ⊗ₖ (B * (E * M0 p q r)) +
        Complex.I • ((A * (E * M0 p q r)) ⊗ₖ (B * Yp))) := by
  set K := E * M0 p q r with hKdef
  have hKe : K = !![K 0 0, K 0 1; K 0 1, K 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hK]
  have h1 : Zm A B E * Om p q r * Vg = (A ⊗ₖ B) * (Vg * (Yp ⊗ₖ K) * Vg) := by
    have : ((1 : Op1) ⊗ₖ E) * Om p q r = Yp ⊗ₖ K := by
      unfold Om
      rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
    unfold Zm
    calc (A ⊗ₖ B) * Vg * ((1 : Op1) ⊗ₖ E) * Om p q r * Vg
        = (A ⊗ₖ B) * (Vg * (((1 : Op1) ⊗ₖ E) * Om p q r) * Vg) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [this]
  rw [h1, hKe, Vg_Y_K_Vg, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_smul,
    ← hKe, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

end FormalResearch.FrameFree.PsiPlusKramers
