import FormalResearch.FrameFree.PsiPlusKramersAlg
import FormalResearch.FrameFree.PsiPlusKramersRK2

/-!
# `ψ₊`: the core Kramers inequality

For arbitrary `2 × 2` matrices `A, B, E` and `Z = (A ⊗ B) V (1 ⊗ E)`, `V = 1 + i SWAP`:
`|tr(V Z)|² ≤ 4 ‖Z‖²_F` (`core_ineq`).  This is the filter inequality `F_C(ψ₊) ≤ 1/2` for the Choi
state of `√SWAP`, after the three-filter reduction of `PsiPlusKramers`.

Proof.  Choose a real `n ≠ 0` with `K = E (n·σ) Y` symmetric (`exists_gauge`).  With `Ω = Y ⊗ (n·σ)Y`
and `N = Z Ω V`, `N = (A ⊗ B)(V (Y ⊗ K) V)` has two product terms (`N_formula`), while
`tr(T N) = 2|n|² tr(V Z)` and `‖N‖² = 2|n|² ‖Z‖²` for `T = Vᴴ Ωᴴ V` (`trace_TN`, `trace_NN`).  The
realignment of `T` is flat, `W Wᴴ = 4|n|²` (`Wm_flat`), so the rank-two Cauchy--Schwarz inequality
`rk2` gives `|tr(T N)|² ≤ 8|n|² ‖N‖²`, i.e. `|tr(V Z)|² ≤ 4‖Z‖²`.
-/

open scoped Matrix ComplexConjugate Kronecker
open FormalResearch.FrameFree FormalResearch.FrameFree.Sharing FormalResearch.FrameFree.NQubit

namespace FormalResearch.FrameFree.PsiPlusKramers

theorem trace_TN (p q r : ℝ) (Z : Mat4) :
    Matrix.trace (Tm p q r * (Z * Om p q r * Vg)) =
      (2 * ((p ^ 2 + q ^ 2 + r ^ 2 : ℝ) : ℂ)) * Matrix.trace (Vg * Z) := by
  unfold Tm
  have h2 : Matrix.trace (Om p q r * ((Om p q r)ᴴ * (Vg * Z))) =
      ((p ^ 2 + q ^ 2 + r ^ 2 : ℝ) : ℂ) * Matrix.trace (Vg * Z) := by
    rw [← Matrix.mul_assoc, Om_mul_conjT, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul]
    rfl
  calc Matrix.trace (Vgᴴ * (Yp ⊗ₖ M0 p q r)ᴴ * Vg * (Z * Om p q r * Vg))
      = Matrix.trace (Vgᴴ * ((Om p q r)ᴴ * Vg * Z * Om p q r * Vg)) := by
        unfold Om; simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((Om p q r)ᴴ * Vg * Z * Om p q r * (Vg * Vgᴴ)) := by
        rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    _ = 2 * Matrix.trace ((Om p q r)ᴴ * (Vg * Z) * Om p q r) := by
        rw [Vg_mul_Vg_conjT, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul]
        simp only [Matrix.mul_assoc, smul_eq_mul]
    _ = 2 * Matrix.trace (Om p q r * ((Om p q r)ᴴ * (Vg * Z))) := by
        rw [Matrix.trace_mul_comm]
    _ = _ := by rw [h2]; ring

theorem trace_NN (p q r : ℝ) (Z : Mat4) :
    Matrix.trace ((Z * Om p q r * Vg)ᴴ * (Z * Om p q r * Vg)) =
      (2 * ((p ^ 2 + q ^ 2 + r ^ 2 : ℝ) : ℂ)) * Matrix.trace (Zᴴ * Z) := by
  have h2 : Matrix.trace (Om p q r * ((Om p q r)ᴴ * (Zᴴ * Z))) =
      ((p ^ 2 + q ^ 2 + r ^ 2 : ℝ) : ℂ) * Matrix.trace (Zᴴ * Z) := by
    rw [← Matrix.mul_assoc, Om_mul_conjT, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul]
    rfl
  calc Matrix.trace ((Z * Om p q r * Vg)ᴴ * (Z * Om p q r * Vg))
      = Matrix.trace (Vgᴴ * ((Om p q r)ᴴ * Zᴴ * Z * Om p q r * Vg)) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Matrix.trace ((Om p q r)ᴴ * Zᴴ * Z * Om p q r * (Vg * Vgᴴ)) := by
        rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    _ = 2 * Matrix.trace ((Om p q r)ᴴ * (Zᴴ * Z) * Om p q r) := by
        rw [Vg_mul_Vg_conjT, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul]
        simp only [Matrix.mul_assoc, smul_eq_mul]
    _ = 2 * Matrix.trace (Om p q r * ((Om p q r)ᴴ * (Zᴴ * Z))) := by
        rw [Matrix.trace_mul_comm]
    _ = _ := by rw [h2]; ring

/-- Realignment `T_{(a,b),(c,d)} ↦ W_{(c,a),(d,b)}`. -/
def realign (T : Mat4) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun ca db => T (ca.2, db.2) (ca.1, db.1)

theorem Wm_eq (p q r : ℝ) : Wm p q r = realign (Tm p q r) := rfl

theorem trace_realign (T N : Mat4) (x₁ x₂ y₁ y₂ : Fin 2 × Fin 2 → ℂ)
    (hN : ∀ c d a b, N (c, d) (a, b) = x₁ (c, a) * y₁ (d, b) + x₂ (c, a) * y₂ (d, b)) :
    Matrix.trace (T * N) = ∑ i, ∑ j, x₁ i * realign T i j * y₁ j +
      ∑ i, ∑ j, x₂ i * realign T i j * y₂ j := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, hN, realign, Matrix.of_apply]
  ring

theorem trace_NN_re (N : Mat4) (x₁ x₂ y₁ y₂ : Fin 2 × Fin 2 → ℂ)
    (hN : ∀ c d a b, N (c, d) (a, b) = x₁ (c, a) * y₁ (d, b) + x₂ (c, a) * y₂ (d, b)) :
    (Matrix.trace (Nᴴ * N)).re = ∑ i, ∑ j, Complex.normSq (x₁ i * y₁ j + x₂ i * y₂ j) := by
  have h : Matrix.trace (Nᴴ * N) =
      ((∑ x : Fin 2 × Fin 2, ∑ y : Fin 2 × Fin 2, Complex.normSq (N y x) : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.star_def, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
  rw [h, Complex.ofReal_re]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, hN]
  ring

/-- **Core inequality** (`F_C(ψ₊) ≤ 1/2`, matrix form): for all `2 × 2` matrices `A, B, E` and
`Z = (A ⊗ B) V (1 ⊗ E)`, `|tr(V Z)|² ≤ 4 ‖Z‖²_F`. -/
theorem core_ineq (A B E : Op1) :
    Complex.normSq (Matrix.trace (Vg * Zm A B E)) ≤
      4 * (Matrix.trace ((Zm A B E)ᴴ * Zm A B E)).re := by
  obtain ⟨p, q, r, hs, hK⟩ := exists_gauge E
  set s : ℝ := p ^ 2 + q ^ 2 + r ^ 2 with hsdef
  set Z := Zm A B E with hZ
  set K := E * M0 p q r with hKdef
  set x₁ : Fin 2 × Fin 2 → ℂ := fun ca => (1 + Complex.I) * (A * Yp) ca.1 ca.2 with hx₁
  set y₁ : Fin 2 × Fin 2 → ℂ := fun db => (B * K) db.1 db.2 with hy₁
  set x₂ : Fin 2 × Fin 2 → ℂ := fun ca => (1 + Complex.I) * Complex.I * (A * K) ca.1 ca.2 with hx₂
  set y₂ : Fin 2 × Fin 2 → ℂ := fun db => (B * Yp) db.1 db.2 with hy₂
  have hN : ∀ c d a b, (Z * Om p q r * Vg) (c, d) (a, b) =
      x₁ (c, a) * y₁ (d, b) + x₂ (c, a) * y₂ (d, b) := by
    intro c d a b
    rw [hZ, N_formula A B E p q r hK]
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.kroneckerMap_apply, smul_eq_mul, hx₁, hy₁,
      hx₂, hy₂]
    ring
  have h1 := rk2 (realign (Tm p q r)) (4 * s) (by rw [← Wm_eq]; exact_mod_cast Wm_flat p q r)
    x₁ x₂ y₁ y₂
  rw [← trace_realign (Tm p q r) _ x₁ x₂ y₁ y₂ hN, trace_TN, ← trace_NN_re _ x₁ x₂ y₁ y₂ hN,
    trace_NN, Complex.normSq_mul] at h1
  have e1 : Complex.normSq (2 * ((s : ℝ) : ℂ)) = 4 * s ^ 2 := by
    rw [show (2 * ((s : ℝ) : ℂ)) = ((2 * s : ℝ) : ℂ) by push_cast; ring, Complex.normSq_ofReal]; ring
  have e2 : ((2 * ((s : ℝ) : ℂ)) * Matrix.trace (Zᴴ * Z)).re = 2 * s * (Matrix.trace (Zᴴ * Z)).re := by
    rw [show (2 * ((s : ℝ) : ℂ)) = ((2 * s : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
  rw [e1, e2] at h1
  have hs2 : 0 < s ^ 2 := by positivity
  nlinarith

end FormalResearch.FrameFree.PsiPlusKramers
