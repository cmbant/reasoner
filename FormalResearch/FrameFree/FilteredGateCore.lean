import FormalResearch.FrameFree.FilteredGateGauge
import FormalResearch.FrameFree.FilteredGateRk2H


/-!
# Filtered-gate law: the core inequality for `sin 4c_k ≥ 0`

`core_good`: for `W` unitary and `c` with `sin 4c_k ≥ 0`,
`|Tr[U (A⊗B) U (W⊗C)]|² ≤ 2 (1 + δ) ‖(A⊗B) U (W⊗C)‖_F²`.  Gauge `W ⊗ C = det W (ς ⊗ K) Φ`, rank-two
form `(A⊗B) U (ς⊗K) U = A ς ⊗ B m + A m' ⊗ B ς`, then the rank-two Cauchy--Schwarz `rk2H` with the
pair bound `pair_le` for `T = U† Φ U`.
-/

open scoped Matrix Kronecker ComplexConjugate
open Finset Complex

namespace FormalResearch.FrameFree.FTG

/-- The matrix with entries `e (a, b)`. -/
def Mx (e : Fin 2 × Fin 2 → ℂ) : M2 := Matrix.of fun a b => e (a, b)

theorem tr_Mx (e₁ e₂ : Fin 2 × Fin 2 → ℂ) :
    (Mx e₂ * (Mx e₁)ᴴ).trace = ∑ i, conj (e₁ i) * e₂ i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Mx,
    Matrix.of_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Complex.star_def]
  ring

theorem tr_Mx_self (e : Fin 2 × Fin 2 → ℂ) :
    (Mx e * (Mx e)ᴴ).trace = ((nrm2 e : ℝ) : ℂ) := by
  rw [tr_Mx]
  simp only [nrm2, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]

theorem trace_realign' (T N : M4) (x₁ x₂ y₁ y₂ : Fin 2 × Fin 2 → ℂ)
    (hN : ∀ c d a b, N (c, d) (a, b) = x₁ (c, a) * y₁ (d, b) + x₂ (c, a) * y₂ (d, b)) :
    Matrix.trace (T * N) = ∑ i, ∑ j, x₁ i * rlg T i j * y₁ j +
      ∑ i, ∑ j, x₂ i * rlg T i j * y₂ j := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, hN, rlg, Matrix.of_apply]
  ring

theorem trace_NN_re' (N : M4) (x₁ x₂ y₁ y₂ : Fin 2 × Fin 2 → ℂ)
    (hN : ∀ c d a b, N (c, d) (a, b) = x₁ (c, a) * y₁ (d, b) + x₂ (c, a) * y₂ (d, b)) :
    fro2 N = ∑ i, ∑ j, Complex.normSq (x₁ i * y₁ j + x₂ i * y₂ j) := by
  have h : Matrix.trace (Nᴴ * N) =
      ((∑ x : Fin 2 × Fin 2, ∑ y : Fin 2 × Fin 2, Complex.normSq (N y x) : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.star_def, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
  unfold fro2
  rw [h, Complex.ofReal_re]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, hN]
  ring

/-- **Filtered-gate law for good `c`** (`sin 4c_k ≥ 0` for all `k`). -/
theorem core_good (c : Fin 3 → ℝ) (hgood : ∀ k, 0 ≤ Real.sin (4 * c k)) (A B C W : M2)
    (hW : Wᴴ * W = 1) :
    ‖(Ug c * kr A B * Ug c * kr W C).trace‖ ^ 2 ≤
      2 * (1 + dl c) * fro2 (kr A B * Ug c * kr W C) := by
  obtain ⟨n, hn, hsym⟩ := exists_unit_gauge C W
  set K : M2 := C * nh n * sig 2 * Wᵀ with hK
  set φ : M2 := Wb W * sig 2 with hφ
  obtain ⟨hφ1, hφ2⟩ := phi_unit W hW
  set Φ : M4 := kr φ (φ * nh n) with hΦ
  have hΦu : Φ * Φᴴ = 1 := kr_unitary _ _ hφ1 (Phi_unitary φ hφ1 n hn)
  have hG : kr W C = W.det • (kr (sig 2) K * Φ) := kr_W_C W C hW n hn
  have hD := det_unit W hW
  set T := Tg c φ n with hT
  have hTe : T = (Ug c)ᴴ * Φ * Ug c := rfl
  -- the rank-two form of `S = U (ς ⊗ K) U`
  set a : ℂ := (K 0 0 + K 1 1) / 2
  set b : ℂ := K 0 1
  set d : ℂ := (K 0 0 - K 1 1) / 2
  have hKs : K = Ksym a b d := K_sym K hsym
  set m : M2 := Ksym (a * (Real.cos (2 * c 1) : ℂ)) (b * (Real.cos (2 * c 2) : ℂ))
    (d * (Real.cos (2 * c 0) : ℂ)) with hm
  set m' : M2 := Ksym (-(Complex.I * a * (Real.sin (2 * c 1) : ℂ)))
    (-(Complex.I * b * (Real.sin (2 * c 2) : ℂ)))
    (-(Complex.I * d * (Real.sin (2 * c 0) : ℂ))) with hm'
  have hS : Ug c * kr (sig 2) K * Ug c = kr (sig 2) m + kr m' (sig 2) := by
    rw [hKs]; exact S_gauge c a b d
  set x₁ : Fin 2 × Fin 2 → ℂ := fun i => (A * sig 2) i.1 i.2
  set y₁ : Fin 2 × Fin 2 → ℂ := fun i => (B * m) i.1 i.2
  set x₂ : Fin 2 × Fin 2 → ℂ := fun i => (A * m') i.1 i.2
  set y₂ : Fin 2 × Fin 2 → ℂ := fun i => (B * sig 2) i.1 i.2
  have hFS : kr A B * (Ug c * kr (sig 2) K * Ug c) = kr (A * sig 2) (B * m) + kr (A * m') (B * sig 2) := by
    rw [hS, Matrix.mul_add, kr_mul, kr_mul]
  have hN : ∀ c' d' a' b', (kr A B * (Ug c * kr (sig 2) K * Ug c)) (c', d') (a', b') =
      x₁ (c', a') * y₁ (d', b') + x₂ (c', a') * y₂ (d', b') := by
    intro c' d' a' b'
    rw [hFS]
    simp [kr_apply, x₁, y₁, x₂, y₂]
  have htr := tr_reduce c (kr A B) (kr (sig 2) K) Φ (kr W C) W.det hG
  have hfro := fro2_reduce c (kr A B) (kr (sig 2) K) Φ (kr W C) W.det hG hΦu hD
  have hpair : ∀ e₁ e₂ : Fin 2 × Fin 2 → ℂ, nrm2 e₁ = 1 → nrm2 e₂ = 1 →
      ∑ i, conj (e₁ i) * e₂ i = 0 → qg (rlg T) e₁ + qg (rlg T) e₂ ≤ 2 + 2 * dl c := by
    intro e₁ e₂ h1 h2 ho
    have t11 := tr_Mx_self e₁
    have t22 := tr_Mx_self e₂
    have t21 := tr_Mx e₁ e₂
    have t12 := tr_Mx e₂ e₁
    rw [h1] at t11
    rw [h2] at t22
    rw [ho] at t21
    have ho' : ∑ i, conj (e₂ i) * e₁ i = 0 := by
      have := congrArg conj ho
      simpa [map_sum, mul_comm] using this
    rw [ho'] at t12
    have := pair_le c hgood φ hφ1 hφ2 n hn (Mx e₁) (Mx e₂) (by simpa using t11) (by simpa using t22)
      (by simpa using t12) (by simpa using t21)
    exact this
  have h1 := rk2H (rlg T) (2 + 2 * dl c) (by decide) (by linarith [dl_nonneg c]) hpair x₁ x₂ y₁ y₂
  rw [← trace_realign' T _ x₁ x₂ y₁ y₂ hN, ← trace_NN_re' _ x₁ x₂ y₁ y₂ hN] at h1
  rw [htr, hfro]
  rw [← hTe, Complex.sq_norm, Complex.normSq_mul]
  have hD1 : Complex.normSq W.det = 1 := by
    have h := hD
    rw [Complex.mul_conj] at h
    exact_mod_cast h
  rw [hD1, one_mul]
  linarith [h1]

end FormalResearch.FrameFree.FTG
