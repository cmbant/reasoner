import FormalResearch.FourQubitEntropy.EnvelopePermCore

/-!
# The permanent bound for `Θ = O D`, `D = κ I + (1-κ) s sᵀ`

Real `3 × 3` algebra for the equality case of `prop:fqe-critical-envelope`
(`sextic_identity.tex`, "The permanent bound" and "Equality").

* `main_Os`: for an orthogonal `O` with `det O = -1`, a unit `s` and `0 < κ ≤ 1`,
  `perm(O D) ≥ -(2 + 3κ² + 4κ³)/9`, and equality forces `O` to be a signed cyclic permutation matrix
  with sign product `-1` and (`κ < 1`) `s_i² = 1/3`. The proof is the paper's Cauchy–Schwarz /
  Maclaurin argument, with `D^{1/2}` and the cubic-form pairing of `EnvelopePermCore.lean`.
* `perm_of_signedCyclic`: conversely `perm(O D) = -(2 + 3κ² + 4κ³)/9` for every signed cyclic `O` and
  every `s ∈ {±1}³/√3` (`CubeDiag`).
-/

namespace FormalResearch.FourQubitEntropy
open Matrix

/-- `D = κ I + (1-κ) s sᵀ` -/
noncomputable def Dmat (κ : ℝ) (s : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  κ • (1 : Matrix (Fin 3) (Fin 3) ℝ) + (1 - κ) • Matrix.vecMulVec s s

theorem main_Os (O : Matrix (Fin 3) (Fin 3) ℝ) (s : Fin 3 → ℝ) (κ : ℝ)
    (hO : O * Oᵀ = 1) (hs : s ⬝ᵥ s = 1) (hdet : O.det = -1) (hk0 : 0 < κ) (hk1 : κ ≤ 1) :
    -pmax κ ≤ perm3 (O * Dmat κ s) ∧
      (perm3 (O * Dmat κ s) = -pmax κ → IsSignedCyclic O ∧ (κ < 1 → ∀ i, s i ^ 2 = 1 / 3)) := by
  have hO' : Oᵀ * O = 1 := mul_eq_one_comm.1 hO
  set l := Real.sqrt κ with hl
  have hl0 : 0 < l := Real.sqrt_pos.2 hk0
  have hl2 : l ^ 2 = κ := Real.sq_sqrt hk0.le
  set S : Matrix (Fin 3) (Fin 3) ℝ := l • (1 : Matrix (Fin 3) (Fin 3) ℝ) + (1 - l) • Matrix.vecMulVec s s with hS
  have hSS : S * S = Dmat κ s := by
    rw [hS, sc_mul _ _ _ _ s hs]
    unfold Dmat
    congr 2
    · rw [← hl2]; ring
    · rw [← hl2]; ring
  have hSt : Sᵀ = S := sc_transpose _ _ s
  set X := O * S with hX
  have hXY : X * Sᵀ = O * Dmat κ s := by rw [hX, hSt, Matrix.mul_assoc, hSS]
  have hXX : X * Xᵀ = κ • (1 : Matrix (Fin 3) (Fin 3) ℝ) + (1 - κ) • Matrix.vecMulVec (O.mulVec s) (O.mulVec s) := by
    rw [hX, Matrix.transpose_mul, hSt, Matrix.mul_assoc, ← Matrix.mul_assoc S, hSS, ← Matrix.mul_assoc]
    unfold Dmat
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_vecMulVec, Matrix.add_mul,
      Matrix.smul_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, hO]
  have hr : (O.mulVec s) ⬝ᵥ (O.mulVec s) = 1 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hO',
      Matrix.vecMul_one]
    exact hs
  have hr' : (O.mulVec s) 0 ^ 2 + (O.mulVec s) 1 ^ 2 + (O.mulVec s) 2 ^ 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_three, sq] using hr
  have hs' : s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_three, sq] using hs
  have pX := perm_rank1_le hk0.le hk1 (O.mulVec s) hr'
  have pY := perm_rank1_le hk0.le hk1 s hs'
  have hnn := perm3_sq_sum_nonneg X S
  have hSS' : S * Sᵀ = Dmat κ s := by rw [hSt, hSS]
  rw [hXX, hSS', hXY] at hnn
  have pY' : perm3 (Dmat κ s) ≤ pmax κ := pY
  refine ⟨by linarith, fun heq => ?_⟩
  have hzero : perm3 (X * Xᵀ) + perm3 (S * Sᵀ) + 2 * perm3 (X * Sᵀ) = 0 := by
    rw [hXX, hSS', hXY]
    have : perm3 (κ • (1 : Matrix (Fin 3) (Fin 3) ℝ) + (1 - κ) • Matrix.vecMulVec (O.mulVec s) (O.mulVec s)) = pmax κ := by
      linarith
    have h2 : perm3 (Dmat κ s) = pmax κ := by linarith
    linarith
  have hD : perm3 (Dmat κ s) = pmax κ := by linarith
  have hcf := cf_add_eq_zero X S hzero
  -- the inverse of S
  set Si : Matrix (Fin 3) (Fin 3) ℝ := l⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℝ) + (1 - l⁻¹) • Matrix.vecMulVec s s with hSi
  have hSSi : S * Si = 1 := by
    rw [hS, hSi, sc_mul _ _ _ _ s hs]
    have e1 : l * l⁻¹ = 1 := mul_inv_cancel₀ hl0.ne'
    have e2 : l * (1 - l⁻¹) + l⁻¹ * (1 - l) + (1 - l) * (1 - l⁻¹) = 0 := by
      field_simp; ring
    rw [e1, e2]; simp
  have hcub : ∀ y : Fin 3 → ℝ, (O.mulVec y) 0 * (O.mulVec y) 1 * (O.mulVec y) 2 = -(y 0 * y 1 * y 2) := by
    intro y
    have hx := cprod_eval X (Si.mulVec y)
    have hx2 := cprod_eval S (Si.mulVec y)
    have e1 : X.mulVec (Si.mulVec y) = O.mulVec y := by
      rw [hX, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec y S Si, hSSi, Matrix.one_mulVec]
    have e2 : S.mulVec (Si.mulVec y) = y := by
      rw [Matrix.mulVec_mulVec y S Si, hSSi, Matrix.one_mulVec]
    rw [e1] at hx
    rw [e2] at hx2
    have hsum : ∑ i, (cf X i + cf S i) * cmon (Si.mulVec y) i = 0 := by
      simp [hcf]
    simp only [add_mul, Finset.sum_add_distrib] at hsum
    linarith
  refine ⟨signedCyclic_of_cubic O hO hdet hcub, fun hlt => ?_⟩
  exact perm_rank1_eq hk0 hlt s hs' (by unfold Dmat at hD; exact hD.ge)

def CubeDiag (s : Fin 3 → ℝ) : Prop := ∀ i, s i * Real.sqrt 3 = 1 ∨ s i * Real.sqrt 3 = -1

theorem CubeDiag.sq {s : Fin 3 → ℝ} (h : CubeDiag s) (i : Fin 3) : s i ^ 2 = 1 / 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have : (s i * Real.sqrt 3) ^ 2 = 1 := by
    rcases h i with h | h <;> rw [h] <;> norm_num
  have h' : s i ^ 2 * 3 = 1 := by rw [mul_pow, h3] at this; exact this
  linarith

theorem perm3_signed_mul (O M : Matrix (Fin 3) (Fin 3) ℝ) (σ : Fin 3 → ℝ) (k : Fin 3)
    (hO : ∀ i j, O i j = if i = j + k then σ j else 0) :
    perm3 (O * M) = σ 0 * σ 1 * σ 2 * perm3 M := by
  fin_cases k <;> simp [perm3, Matrix.mul_apply, Fin.sum_univ_three, hO] <;> ring

theorem perm3_Dmat_cube (κ : ℝ) (s : Fin 3 → ℝ) (h : ∀ i, s i ^ 2 = 1 / 3) :
    perm3 (Dmat κ s) = pmax κ := by
  unfold Dmat pmax
  rw [perm3_scalar_rank1, h 0, h 1, h 2]
  ring

theorem perm_of_signedCyclic (κ : ℝ) (O : Matrix (Fin 3) (Fin 3) ℝ) (s : Fin 3 → ℝ)
    (hO : IsSignedCyclic O) (hs : CubeDiag s) : perm3 (O * Dmat κ s) = -pmax κ := by
  obtain ⟨k, σ, -, hσ, hk⟩ := hO
  rw [perm3_signed_mul O _ σ k hk, hσ, perm3_Dmat_cube κ s hs.sq]
  ring


end FormalResearch.FourQubitEntropy
