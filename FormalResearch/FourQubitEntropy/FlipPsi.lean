import FormalResearch.FourQubitEntropy.Bridge
import FormalResearch.FourQubitEntropy.Purity

/-!
# The spin flip `ψ ↦ ε^{⊗4} ψ̄` and the spin-flip pencil `ψ + ρ ψ̃`

`flipPsi ψ = ψ̃` is the antiunitary involution of `sextic_identity.tex`
(`thm:fqe-general-envelope`, "spin-flip split"). Every statement here is an elementary identity of
coordinates. For every `ψ`, with `s = ψᵀ ε^{⊗4} ψ = spinFlipForm ψ`, `n = ‖ψ‖²` and real `ρ`:

* `flipPsi_flipPsi`: `ψ̃̃ = ψ`; additivity, real homogeneity, conjugate homogeneity;
* `normSqPsi_pencil`: `‖ψ + ρ ψ̃‖² = (1 + ρ²) n + 2ρ Re s`;
* `spinFlipForm_pencil`: `s(ψ + ρ ψ̃) = s + ρ² s̄ + 2ρ n`;
* `expectation_pencil`, `blochSq_pencil`: the Bloch vectors of `ψ + ρ ψ̃` are `(1 - ρ²)` times
  those of `ψ` (the flip reverses Bloch vectors and `⟨ψ̃|σ|ψ⟩ = 0`), so
  `W₁(ψ + ρ ψ̃) = (1 - ρ²)² W₁(ψ)`;
* real homogeneity of `n`, `W₁`, `F`.

No `native_decide`; kernel/`ring` only.
-/

open scoped ComplexConjugate
open scoped FormalResearch.FourQubitEntropy.GenericOps

namespace FormalResearch.FourQubitEntropy

@[simp] theorem sgn_zero : sgn 0 = 1 := by simp [sgn]
@[simp] theorem sgn_one : sgn 1 = -1 := by simp [sgn]

/-- The spin flip `ψ̃ = ε^{⊗4} ψ̄` (`ε = [[0,1],[-1,0]]`). -/
noncomputable def flipPsi (ψ : Psi) : Psi := fun a b c d => ztil ψ.conj a b c d

theorem flipPsi_apply (ψ : Psi) (a b c d : Fin 2) :
    flipPsi ψ a b c d = ((sgn a * sgn b * sgn c * sgn d : ℤ) : ℂ)
      * conj (ψ (1 - a) (1 - b) (1 - c) (1 - d)) := by
  simp [flipPsi, ztil, Psi.conj]

theorem flipPsi_flipPsi (ψ : Psi) : flipPsi (flipPsi ψ) = ψ := by
  funext a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [flipPsi_apply] <;> ring_nf <;> simp

theorem flipPsi_add (ψ φ : Psi) : flipPsi (ψ + φ) = flipPsi ψ + flipPsi φ := by
  funext a b c d
  simp [flipPsi_apply, mul_add]

theorem flipPsi_smul_real (r : ℝ) (ψ : Psi) : flipPsi (r • ψ) = r • flipPsi ψ := by
  funext a b c d
  simp only [flipPsi_apply, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
  ring

theorem flipPsi_neg (ψ : Psi) : flipPsi (-ψ) = -flipPsi ψ := by
  funext a b c d
  simp [flipPsi_apply]


/-! ### The pencil `ψ + ρ ψ̃` -/

theorem normSqPsi_pencil (ψ : Psi) (ρ : ℝ) :
    normSqPsi (ψ + ρ • flipPsi ψ)
      = (1 + ρ ^ 2) * normSqPsi ψ + 2 * ρ * (spinFlipForm ψ).re := by
  simp only [normSqPsi, spinFlipForm, sum4, sum2, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply,
    Complex.real_smul, flipPsi_apply, Complex.normSq_apply, toAdd_complex, toMul_complex, lit_complex]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, sgn]
  ring

theorem spinFlipForm_pencil (ψ : Psi) (ρ : ℝ) :
    spinFlipForm (ψ + ρ • flipPsi ψ)
      = spinFlipForm ψ + ρ ^ 2 * conj (spinFlipForm ψ) + 2 * ρ * normSqPsi ψ := by
  simp only [normSqPsi, spinFlipForm, sum4, sum2, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply,
    Complex.real_smul, flipPsi_apply, toAdd_complex, toMul_complex, lit_complex,
    map_add, map_mul, Complex.conj_conj, Complex.conj_ofReal, map_intCast]
  simp only [Complex.normSq_eq_conj_mul_self, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_add]
  simp [sgn]
  ring


theorem expectation_pencil (i : Fin 4) (σ : Matrix (Fin 2) (Fin 2) ℂ)
    (hσ : σ = pauliX ∨ σ = pauliY ∨ σ = pauliZ) (ψ : Psi) (ρ : ℝ) :
    expectation i σ (ψ + ρ • flipPsi ψ) = ((1 - ρ ^ 2 : ℝ) : ℂ) * expectation i σ ψ := by
  rcases hσ with rfl | rfl | rfl <;> fin_cases i <;>
  · simp only [expectation, actOn, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply,
      Complex.real_smul, flipPsi_apply, map_add, map_mul, Complex.conj_conj, Complex.conj_ofReal,
      map_intCast, pauliX, pauliY, pauliZ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    simp [sgn]
    ring


theorem blochSq_pencil (ψ : Psi) (ρ : ℝ) :
    blochSq (ψ + ρ • flipPsi ψ) = (1 - ρ ^ 2) ^ 2 * blochSq ψ := by
  unfold blochSq
  simp only [expectation_pencil _ _ (Or.inl rfl) ψ ρ,
    expectation_pencil _ _ (Or.inr (Or.inl rfl)) ψ ρ,
    expectation_pencil _ _ (Or.inr (Or.inr rfl)) ψ ρ, Complex.re_ofReal_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ### Real homogeneity -/

theorem normSqPsi_smul (c : ℝ) (ψ : Psi) : normSqPsi (c • ψ) = c ^ 2 * normSqPsi ψ := by
  simp only [normSqPsi, Pi.smul_apply, Complex.real_smul, Complex.normSq_mul,
    Complex.normSq_ofReal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d _ => ?_
  ring

theorem expectation_smul (i : Fin 4) (σ : Matrix (Fin 2) (Fin 2) ℂ) (c : ℝ) (ψ : Psi) :
    expectation i σ (c • ψ) = ((c ^ 2 : ℝ) : ℂ) * expectation i σ ψ := by
  fin_cases i <;>
  · simp only [expectation, actOn, Fin.sum_univ_two, Pi.smul_apply, Complex.real_smul, map_mul,
      Complex.conj_ofReal]
    push_cast
    ring

theorem blochSq_smul (c : ℝ) (ψ : Psi) : blochSq (c • ψ) = c ^ 4 * blochSq ψ := by
  unfold blochSq
  simp only [expectation_smul, Complex.re_ofReal_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem red12_smul (c : ℝ) (ψ : Psi) : red12 (c • ψ) = ((c ^ 2 : ℝ) : ℂ) • red12 ψ := by
  ext i j
  simp only [red12, Matrix.of_apply, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  push_cast
  ring

theorem red13_smul (c : ℝ) (ψ : Psi) : red13 (c • ψ) = ((c ^ 2 : ℝ) : ℂ) • red13 ψ := by
  ext i j
  simp only [red13, Matrix.of_apply, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  push_cast
  ring

theorem red14_smul (c : ℝ) (ψ : Psi) : red14 (c • ψ) = ((c ^ 2 : ℝ) : ℂ) • red14 ψ := by
  ext i j
  simp only [red14, Matrix.of_apply, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  push_cast
  ring

theorem purity_smul (c : ℝ) (ψ : Psi) : purity (c • ψ) = c ^ 4 * purity ψ := by
  unfold purity
  rw [red12_smul, red13_smul, red14_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, smul_eq_mul]
  simp only [Complex.re_ofReal_mul, ← Complex.ofReal_mul]
  ring

theorem cubicMoment_smul (c : ℝ) (ψ : Psi) : cubicMoment (c • ψ) = c ^ 6 * cubicMoment ψ := by
  unfold cubicMoment
  rw [red12_smul, red13_smul, red14_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, smul_eq_mul]
  simp only [Complex.re_ofReal_mul, ← Complex.ofReal_mul]
  ring

theorem sexticF_smul (c : ℝ) (ψ : Psi) : sexticF (c • ψ) = c ^ 6 * sexticF ψ := by
  unfold sexticF
  rw [normSqPsi_smul, purity_smul, cubicMoment_smul]
  ring


/-! ### Complex scalars: a global phase changes nothing, and `s` scales by `c²` -/

theorem real_smul_eq (r : ℝ) (ψ : Psi) : r • ψ = (r : ℂ) • ψ := by
  funext a b c d; simp [Complex.real_smul]

theorem normSqPsi_smulC (c : ℂ) (ψ : Psi) : normSqPsi (c • ψ) = Complex.normSq c * normSqPsi ψ := by
  simp only [normSqPsi, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Finset.mul_sum]

theorem expectation_smulC (i : Fin 4) (σ : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) (ψ : Psi) :
    expectation i σ (c • ψ) = ((Complex.normSq c : ℝ) : ℂ) * expectation i σ ψ := by
  rw [Complex.normSq_eq_conj_mul_self]
  fin_cases i <;>
  · simp only [expectation, actOn, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, map_mul]
    ring

theorem blochSq_smulC (c : ℂ) (ψ : Psi) :
    blochSq (c • ψ) = Complex.normSq c ^ 2 * blochSq ψ := by
  unfold blochSq
  simp only [expectation_smulC, Complex.re_ofReal_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem red12_smulC (c : ℂ) (ψ : Psi) : red12 (c • ψ) = ((Complex.normSq c : ℝ) : ℂ) • red12 ψ := by
  ext i j
  simp only [red12, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, map_mul, Matrix.smul_apply,
    Finset.mul_sum, Complex.normSq_eq_conj_mul_self]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem red13_smulC (c : ℂ) (ψ : Psi) : red13 (c • ψ) = ((Complex.normSq c : ℝ) : ℂ) • red13 ψ := by
  ext i j
  simp only [red13, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, map_mul, Matrix.smul_apply,
    Finset.mul_sum, Complex.normSq_eq_conj_mul_self]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem red14_smulC (c : ℂ) (ψ : Psi) : red14 (c • ψ) = ((Complex.normSq c : ℝ) : ℂ) • red14 ψ := by
  ext i j
  simp only [red14, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, map_mul, Matrix.smul_apply,
    Finset.mul_sum, Complex.normSq_eq_conj_mul_self]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem sexticF_smulC (c : ℂ) (ψ : Psi) : sexticF (c • ψ) = Complex.normSq c ^ 3 * sexticF ψ := by
  unfold sexticF purity cubicMoment
  rw [normSqPsi_smulC, red12_smulC, red13_smulC, red14_smulC]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, smul_eq_mul]
  simp only [Complex.re_ofReal_mul, ← Complex.ofReal_mul]
  ring

theorem Hval_smulC_aux (c : ℂ) (ψ : Psi) :
    4 * sexticF (c • ψ) - 3 * (normSqPsi (c • ψ) * blochSq (c • ψ))
      = Complex.normSq c ^ 3 * (4 * sexticF ψ - 3 * (normSqPsi ψ * blochSq ψ)) := by
  rw [sexticF_smulC, normSqPsi_smulC, blochSq_smulC]
  ring

theorem spinFlipForm_smulC (c : ℂ) (ψ : Psi) : spinFlipForm (c • ψ) = c ^ 2 * spinFlipForm ψ := by
  simp only [spinFlipForm, sum4, sum2, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, toAdd_complex,
    toMul_complex, lit_complex]
  ring

theorem flipPsi_smulC (c : ℂ) (ψ : Psi) : flipPsi (c • ψ) = (conj c) • flipPsi ψ := by
  funext a b c' d
  simp only [flipPsi_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

end FormalResearch.FourQubitEntropy
