import FormalResearch.FourQubitEntropy.Statement
import FormalResearch.FourQubitEntropy.Defect

/-!
# Generic expressions at `ℂ` are the Mathlib quantities

For `w = conj ψ`, the generic expressions of `Generic.lean` evaluated in `ℂ` are the quantities of
`Statement.lean`.
-/

open scoped ComplexConjugate
open scoped FormalResearch.FourQubitEntropy.GenericOps

namespace FormalResearch.FourQubitEntropy

/-- The conjugate vector. -/
def Psi.conj (ψ : Psi) : Psi := fun a b c d => (starRingEnd ℂ) (ψ a b c d)

section Simp

open GenericOps

@[simp] theorem toAdd_complex (a b : ℂ) :
    @HAdd.hAdd ℂ ℂ ℂ (@instHAdd ℂ toAdd) a b = a + b := rfl
@[simp] theorem toMul_complex (a b : ℂ) :
    @HMul.hMul ℂ ℂ ℂ (@instHMul ℂ toMul) a b = a * b := rfl
@[simp] theorem toNeg_complex (a : ℂ) : @Neg.neg ℂ toNeg a = -a := rfl
@[simp] theorem toSub_complex (a b : ℂ) :
    @HSub.hSub ℂ ℂ ℂ (@instHSub ℂ toSub) a b = a - b := sub_eq_add_neg a b |>.symm ▸ rfl
@[simp] theorem lit_complex (k : ℤ) : (lit k : ℂ) = (k : ℂ) := rfl

end Simp

theorem normG_eq (ψ : Psi) : normG ψ ψ.conj = (normSqPsi ψ : ℂ) := by
  simp [normG, sum4, sum2, normSqPsi, Fin.sum_univ_two, Psi.conj, Complex.mul_conj]


theorem tr2_eq (X : Mat4) :
    tr2 (fun a b a' b' => X (a, b) (a', b')) = Matrix.trace (X * X) := by
  simp [tr2, sum2, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem tr3_eq (X : Mat4) :
    tr3 (fun a b a' b' => X (a, b) (a', b')) = Matrix.trace (X * X * X) := by
  simp [tr3, sum2, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

theorem marg12_eq (ψ : Psi) (a b a' b' : Fin 2) :
    marg12 ψ ψ.conj a b a' b' = red12 ψ (a, b) (a', b') := by
  simp [marg12, red12, sum2, Psi.conj, Fin.sum_univ_two]

theorem marg13_eq (ψ : Psi) (a b a' b' : Fin 2) :
    marg13 ψ ψ.conj a b a' b' = red13 ψ (a, b) (a', b') := by
  simp [marg13, red13, sum2, Psi.conj, Fin.sum_univ_two]

theorem marg14_eq (ψ : Psi) (a b a' b' : Fin 2) :
    marg14 ψ ψ.conj a b a' b' = red14 ψ (a, b) (a', b') := by
  simp [marg14, red14, sum2, Psi.conj, Fin.sum_univ_two]

theorem red12_herm (ψ : Psi) : (red12 ψ).IsHermitian := by
  ext i j
  simp [red12, mul_comm]

theorem red13_herm (ψ : Psi) : (red13 ψ).IsHermitian := by
  ext i j
  simp [red13, mul_comm]

theorem red14_herm (ψ : Psi) : (red14 ψ).IsHermitian := by
  ext i j
  simp [red14, mul_comm]

/-- Traces of powers of a Hermitian matrix are real. -/
theorem trace_sq_real {X : Mat4} (hX : X.IsHermitian) :
    Matrix.trace (X * X) = ((Matrix.trace (X * X)).re : ℂ) := by
  have h : star (Matrix.trace (X * X)) = Matrix.trace (X * X) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hX.eq]
  exact (Complex.conj_eq_iff_re.mp h).symm

theorem trace_cube_real {X : Mat4} (hX : X.IsHermitian) :
    Matrix.trace (X * X * X) = ((Matrix.trace (X * X * X)).re : ℂ) := by
  have h : star (Matrix.trace (X * X * X)) = Matrix.trace (X * X * X) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hX.eq,
      Matrix.mul_assoc]
  exact (Complex.conj_eq_iff_re.mp h).symm

theorem tr2_marg12 (ψ : Psi) : tr2 (marg12 ψ ψ.conj) = Matrix.trace (red12 ψ * red12 ψ) := by
  rw [← tr2_eq]; congr; funext a b a' b'; exact marg12_eq ψ a b a' b'
theorem tr2_marg13 (ψ : Psi) : tr2 (marg13 ψ ψ.conj) = Matrix.trace (red13 ψ * red13 ψ) := by
  rw [← tr2_eq]; congr; funext a b a' b'; exact marg13_eq ψ a b a' b'
theorem tr2_marg14 (ψ : Psi) : tr2 (marg14 ψ ψ.conj) = Matrix.trace (red14 ψ * red14 ψ) := by
  rw [← tr2_eq]; congr; funext a b a' b'; exact marg14_eq ψ a b a' b'
theorem tr3_marg12 (ψ : Psi) :
    tr3 (marg12 ψ ψ.conj) = Matrix.trace (red12 ψ * red12 ψ * red12 ψ) := by
  rw [← tr3_eq]; congr; funext a b a' b'; exact marg12_eq ψ a b a' b'
theorem tr3_marg13 (ψ : Psi) :
    tr3 (marg13 ψ ψ.conj) = Matrix.trace (red13 ψ * red13 ψ * red13 ψ) := by
  rw [← tr3_eq]; congr; funext a b a' b'; exact marg13_eq ψ a b a' b'
theorem tr3_marg14 (ψ : Psi) :
    tr3 (marg14 ψ ψ.conj) = Matrix.trace (red14 ψ * red14 ψ * red14 ψ) := by
  rw [← tr3_eq]; congr; funext a b a' b'; exact marg14_eq ψ a b a' b'

theorem Fgen_eq (ψ : Psi) : Fgen ψ ψ.conj = (sexticF ψ : ℂ) := by
  simp only [Fgen, normG_eq, tr2_marg12, tr2_marg13, tr2_marg14, tr3_marg12, tr3_marg13,
    tr3_marg14, sexticF, purity, cubicMoment]
  rw [trace_sq_real (red12_herm ψ), trace_sq_real (red13_herm ψ), trace_sq_real (red14_herm ψ),
    trace_cube_real (red12_herm ψ), trace_cube_real (red13_herm ψ), trace_cube_real (red14_herm ψ)]
  push_cast
  simp
  ring


/-! ### Bloch vectors -/

theorem siteSwap_conj (i : Fin 4) (ψ : Psi) : siteSwap i ψ.conj = Psi.conj (siteSwap i ψ) := by
  fin_cases i <;> rfl

/-- The one-qubit reduced matrix of qubit `i`. -/
noncomputable def rhoSite (i : Fin 4) (ψ : Psi) (a a' : Fin 2) : ℂ :=
  rho0 (siteSwap i ψ) (Psi.conj (siteSwap i ψ)) a a'

theorem rhoSite_conj (i : Fin 4) (ψ : Psi) (a a' : Fin 2) :
    (starRingEnd ℂ) (rhoSite i ψ a a') = rhoSite i ψ a' a := by
  simp [rhoSite, rho0, sum2, Psi.conj, Fin.sum_univ_two, mul_comm]

theorem expectation_eq (i : Fin 4) (σ : Matrix (Fin 2) (Fin 2) ℂ) (ψ : Psi) :
    expectation i σ ψ = ∑ a, ∑ t, σ a t * rhoSite i ψ t a := by
  fin_cases i <;>
  simp [expectation, actOn, rhoSite, rho0, siteSwap, sum2, Psi.conj, Fin.sum_univ_two] <;> ring

theorem normG_siteSwap (i : Fin 4) (ψ : Psi) :
    normG (siteSwap i ψ) (Psi.conj (siteSwap i ψ)) = normG ψ ψ.conj := by
  fin_cases i <;>
  simp [normG, sum4, sum2, siteSwap, Psi.conj, Fin.sum_univ_two] <;> ring

theorem normG_rho (i : Fin 4) (ψ : Psi) :
    normG ψ ψ.conj = rhoSite i ψ 0 0 + rhoSite i ψ 1 1 := by
  rw [← normG_siteSwap i]
  simp [normG, sum4, sum2, rhoSite, rho0]

theorem bloch_aux (r : Fin 2 → Fin 2 → ℂ) (h : ∀ a a', (starRingEnd ℂ) (r a a') = r a' a) :
    ((((r 1 0 + r 0 1).re ^ 2 + (-Complex.I * r 1 0 + Complex.I * r 0 1).re ^ 2
      + (r 0 0 - r 1 1).re ^ 2 : ℝ) : ℂ))
      = 2 * (r 0 0 * r 0 0 + r 0 1 * r 1 0 + (r 1 0 * r 0 1 + r 1 1 * r 1 1))
        - (r 0 0 + r 1 1) * (r 0 0 + r 1 1) := by
  have h00 := Complex.conj_eq_iff_re.mp (h 0 0)
  have h11 := Complex.conj_eq_iff_re.mp (h 1 1)
  have h10 : r 1 0 = (starRingEnd ℂ) (r 0 1) := (h 0 1).symm
  rw [h10, ← h00, ← h11]
  generalize r 0 1 = x
  generalize (r 0 0).re = p
  generalize (r 1 1).re = q
  apply Complex.ext <;> simp [Complex.ext_iff, pow_two] <;> ring

theorem bloch_site (i : Fin 4) (ψ : Psi) :
    (((expectation i pauliX ψ).re ^ 2 + (expectation i pauliY ψ).re ^ 2
      + (expectation i pauliZ ψ).re ^ 2 : ℝ) : ℂ)
      = lit 2 * trRho2 (siteSwap i ψ) (siteSwap i ψ.conj) - normG ψ ψ.conj * normG ψ ψ.conj := by
  rw [normG_rho i ψ, siteSwap_conj]
  have := bloch_aux (rhoSite i ψ) (rhoSite_conj i ψ)
  simp only [expectation_eq, Fin.sum_univ_two, pauliX, pauliY, pauliZ]
  simp [trRho2, sum2, rhoSite] at this ⊢
  linear_combination this


theorem W1gen_eq (ψ : Psi) : W1gen ψ ψ.conj = (blochSq ψ : ℂ) := by
  have h0 : (((expectation 0 pauliX ψ).re ^ 2 + (expectation 0 pauliY ψ).re ^ 2
      + (expectation 0 pauliZ ψ).re ^ 2 : ℝ) : ℂ)
      = lit 2 * trRho2 ψ ψ.conj - normG ψ ψ.conj * normG ψ ψ.conj := bloch_site 0 ψ
  have h1 := bloch_site 1 ψ
  have h2 := bloch_site 2 ψ
  have h3 := bloch_site 3 ψ
  simp only [blochSq, Fin.sum_univ_four, W1gen]
  push_cast
  push_cast at h0 h1 h2 h3
  linear_combination -(h0 + h1 + h2 + h3)

/-! ### The residual norms are nonnegative -/

/-- A nonnegative real number, viewed in `ℂ`. -/
def NonnegReal (c : ℂ) : Prop := ∃ r : ℝ, 0 ≤ r ∧ c = r

theorem NonnegReal.add {a b : ℂ} (ha : NonnegReal a) (hb : NonnegReal b) : NonnegReal (a + b) := by
  obtain ⟨r, hr, rfl⟩ := ha
  obtain ⟨s, hs, rfl⟩ := hb
  exact ⟨r + s, add_nonneg hr hs, by push_cast; rfl⟩

theorem NonnegReal.natMul {a : ℂ} (ha : NonnegReal a) (n : ℕ) : NonnegReal ((n : ℂ) * a) := by
  obtain ⟨r, hr, rfl⟩ := ha
  exact ⟨n * r, mul_nonneg n.cast_nonneg hr, by push_cast; rfl⟩

theorem NonnegReal.mul_conj (x : ℂ) : NonnegReal (x * (starRingEnd ℂ) x) :=
  ⟨Complex.normSq x, Complex.normSq_nonneg x, Complex.mul_conj x⟩

theorem NonnegReal.sum2 {f : Fin 2 → ℂ} (h : ∀ i, NonnegReal (f i)) :
    NonnegReal (FormalResearch.FourQubitEntropy.sum2 f) := by
  simp only [FormalResearch.FourQubitEntropy.sum2, toAdd_complex]
  exact (h 0).add (h 1)

theorem opsHom_conj : OpsHom (starRingEnd ℂ) where
  map_zero := map_zero _
  map_one := map_one _
  map_add := map_add _
  map_mul := map_mul _
  map_neg := map_neg _
  map_ofInt k := by simp [RingOps.ofInt]

theorem State.map_conj (z : State ℂ) :
    (State.map (starRingEnd ℂ) z) = fun a b c d => (starRingEnd ℂ) (z a b c d) := rfl

theorem resTensor_conj (ψ : Psi) (x y t o1 o2 o3 : Fin 2) :
    resTensor ψ.conj ψ x y t o1 o2 o3
      = (starRingEnd ℂ) (resTensor ψ ψ.conj x y t o1 o2 o3) := by
  have h := opsHom_conj.resTensor ψ ψ.conj x y t o1 o2 o3
  rw [h]
  have e1 : State.map (starRingEnd ℂ) ψ = ψ.conj := rfl
  have e2 : State.map (starRingEnd ℂ) ψ.conj = ψ := by
    funext a b c d; simp [State.map, Psi.conj]
  rw [e1, e2]

theorem pairVec_conj (i j : Fin 4) (ψ : Psi) (a b c d : Fin 2) :
    pairVec i j ψ.conj ψ a b c d = (starRingEnd ℂ) (pairVec i j ψ ψ.conj a b c d) := by
  have h := opsHom_conj.pairVec ψ ψ.conj i j a b c d
  rw [h]
  have e1 : State.map (starRingEnd ℂ) ψ = ψ.conj := rfl
  have e2 : State.map (starRingEnd ℂ) ψ.conj = ψ := by
    funext a b c d; simp [State.map, Psi.conj]
  rw [e1, e2]

theorem NonnegReal.sum4 {f : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ} (h : ∀ a b c d, NonnegReal (f a b c d)) :
    NonnegReal (FormalResearch.FourQubitEntropy.sum4 f) :=
  NonnegReal.sum2 fun a => NonnegReal.sum2 fun b => NonnegReal.sum2 fun c =>
    NonnegReal.sum2 fun d => h a b c d

theorem pairNorm_nonneg (i j : Fin 4) (ψ : Psi) : NonnegReal (pairNorm i j ψ ψ.conj) := by
  refine NonnegReal.sum4 fun a b c d => ?_
  simp only [pairVec_conj]
  exact NonnegReal.mul_conj _

theorem pairSum_nonneg (ψ : Psi) : NonnegReal (pairSum ψ ψ.conj) := by
  simp only [pairSum, toAdd_complex]
  exact (((((pairNorm_nonneg 0 1 ψ).add (pairNorm_nonneg 0 2 ψ)).add (pairNorm_nonneg 0 3 ψ)).add
    (pairNorm_nonneg 1 2 ψ)).add (pairNorm_nonneg 1 3 ψ)).add (pairNorm_nonneg 2 3 ψ)

theorem resNorm0_nonneg (ψ : Psi) : NonnegReal (resNorm0 ψ ψ.conj) := by
  have slot : ∀ x y t : Fin 2, NonnegReal (resSlot ψ ψ.conj x y t) := by
    intro x y t
    refine NonnegReal.sum2 fun o1 => NonnegReal.sum2 fun o2 => NonnegReal.sum2 fun o3 => ?_
    simp only [resTensor_conj]
    exact NonnegReal.mul_conj _
  have h3 : (lit 3 : ℂ) = ((3 : ℕ) : ℂ) := by
    show ((3 : ℤ) : ℂ) = ((3 : ℕ) : ℂ)
    norm_num
  simp only [resNorm0, toAdd_complex, toMul_complex, h3]
  exact (((slot 0 0 0).add ((slot 0 0 1).natMul 3)).add ((slot 0 1 1).natMul 3)).add (slot 1 1 1)

end FormalResearch.FourQubitEntropy
