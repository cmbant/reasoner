import FormalResearch.FrameFree.ConverseM4

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped ComplexConjugate Matrix BigOperators
open Matrix FormalResearch.FrameFree.NQubit FormalResearch.FrameFree.Helstrom

/-!
# Three-qubit vectors with vanishing hyperdeterminant are locally-unitarily real

Namespace `FormalResearch.FrameFree.Converse`.  `Ach3 β` : there are `v ∈ SU(2)³` and `|c| = 1` with
`rot v (Θ β) = c β` (the branch criterion of `achiralBranch_of_branch`).

* `Ach3.of_rot`, `Ach3.of_real`, `Ach3.smul`, `Ach3.of_support` : invariance under `SU(2)³`, real vectors, scaling, and the
  four-point support `{000, 001, 010, 100}` (diagonal `SU(2)` phases make the four coefficients real).
* `disc3R`, `disc3` : the Cayley hyperdeterminant `B² - 4AC` of a three-qubit vector, `det(x N₀ + y N₁) = A x² + B xy + C y²`
  for the slices `N_b = β(b,·,·)`.
* `Ach3.of_disc` : `disc3 β = 0 → Ach3 β`.  Proof: the kernel `u` of `[[2A, B], [B, 2C]]` (singular because
  `disc3 β = 0`) is a *double root* of the quadratic form, so `X = Σ u_b N_b` is singular and its mixed determinant with the
  orthogonal slice vanishes; a kernel vector `k` of `X` and a left null vector `r` of `(X k^⊥, Y k)` give three
  `SU(2)` frames in which `β` is supported on `{000, 001, 010, 100}`.
* `exists_root_disc` : the quartic `z ↦ disc3 (z p + q)` has a root in `ℙ¹` (fundamental theorem of algebra).
-/

namespace FormalResearch.FrameFree.Converse

open Polynomial

/-- A three-qubit vector is *achiral* (locally-unitarily real): `v Θβ = c β` for some `v ∈ SU(2)³`, `|c| = 1`. -/
def Ach3 (β : Ψ 3) : Prop :=
  ∃ v : Fin 3 → Op1, (∀ i, SU2 (v i)) ∧ ∃ c : ℂ, ‖c‖ = 1 ∧ rot v (Θ β) = c • β

theorem Ach3.of_rot {β : Ψ 3} {R : Fin 3 → Op1} (hR : ∀ i, SU2 (R i)) (h : Ach3 (rot R β)) :
    Ach3 β := by
  obtain ⟨v, hv, c, hc, h⟩ := h
  refine ⟨fun i => (R i)ᴴ * v i * R i,
    fun i => SU2_mul (SU2_mul (SU2_adjoint (hR i)) (hv i)) (hR i), c, hc, ?_⟩
  rw [Θ_rot R hR, rot_comp] at h
  have := congrArg (rot (fun i => (R i)ᴴ)) h
  simp only [rot_comp, rot_smul'] at this
  have e : (fun i => (R i)ᴴ * R i) = fun _ => (1 : Op1) := funext fun i => (hR i).1
  rw [e, rot_one] at this
  simpa only [mul_assoc] using this

theorem Ach3.of_real {β r : Ψ 3} (hr : cj r = r) {z : ℂ} (hz : z ≠ 0) (h : β = z • r) : Ach3 β := by
  refine ⟨fun _ => epsᴴ, fun _ => SU2_adjoint SU2_eps, conj z / z, ?_, ?_⟩
  · rw [norm_div, Complex.norm_conj]; exact div_self (by simpa using hz)
  · rw [Θ_eq_rot, rot_comp]
    have e' : (fun i : Fin 3 => (fun _ : Fin 3 => epsᴴ) i * (fun _ : Fin 3 => eps) i) =
        fun _ => (1 : Op1) := funext fun _ => SU2_eps.1
    rw [e', rot_one, h, cj_smul', hr, smul_smul, div_mul_cancel₀ _ hz]

theorem Ach3.smul {β : Ψ 3} (h : Ach3 β) {z : ℂ} (hz : z ≠ 0) : Ach3 (z • β) := by
  obtain ⟨v, hv, c, hc, h⟩ := h
  refine ⟨v, hv, conj z * c / z, ?_, ?_⟩
  · rw [norm_div, norm_mul, Complex.norm_conj, hc, mul_one]; exact div_self (by simpa using hz)
  · rw [Θ_smul', rot_smul', h, smul_smul, smul_smul, div_mul_cancel₀ _ hz]

/-! ### The four-point support `{000, 001, 010, 100}` -/

/-- The diagonal `SU(2)` element `diag(e^{it}, e^{-it})`. -/
noncomputable def Dg (t : ℝ) : Op1 :=
  Matrix.diagonal ![Complex.exp (t * Complex.I), Complex.exp (-(t * Complex.I))]

theorem conj_exp_I (t : ℝ) : conj (Complex.exp (t * Complex.I)) = Complex.exp (-(t * Complex.I)) := by
  rw [← Complex.exp_conj]; congr 1; simp

theorem SU2_Dg (t : ℝ) : SU2 (Dg t) := by
  have h1 : Complex.exp (-(t * Complex.I)) * Complex.exp (t * Complex.I) = 1 := by
    rw [← Complex.exp_add]; simp
  have h2 : Complex.exp (t * Complex.I) * Complex.exp (-(t * Complex.I)) = 1 := by
    rw [mul_comm]; exact h1
  have h3 : conj (Complex.exp (-(t * Complex.I))) = Complex.exp (t * Complex.I) := by
    have := congrArg conj (conj_exp_I t)
    rw [Complex.conj_conj] at this
    exact this.symm
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Dg, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
        conj_exp_I, h3, h1, h2]
  · simp [Dg, Matrix.det_fin_two, h2]

theorem exp_mul_polar (g : ℂ) (s α : ℝ) (h : s + Complex.arg g = α) :
    Complex.exp (s * Complex.I) * g = Complex.exp (α * Complex.I) * (‖g‖ : ℂ) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I g]
  rw [← h]
  push_cast
  rw [add_mul, Complex.exp_add]
  ring

theorem rot_Dg (θ : Fin 3 → ℝ) (γ : Ψ 3) (a b c : Fin 2) :
    rot (fun i => Dg (θ i)) γ ![a, b, c] =
      ![Complex.exp (θ 0 * Complex.I), Complex.exp (-(θ 0 * Complex.I))] a *
      ![Complex.exp (θ 1 * Complex.I), Complex.exp (-(θ 1 * Complex.I))] b *
      ![Complex.exp (θ 2 * Complex.I), Complex.exp (-(θ 2 * Complex.I))] c * γ ![a, b, c] := by
  have := rot_diagonal (fun i => ![Complex.exp (θ i * Complex.I), Complex.exp (-(θ i * Complex.I))]) γ
    ![a, b, c]
  simp only [Fin.prod_univ_three] at this
  exact this

theorem Ach3.of_support {γ : Ψ 3} (h011 : γ ![0, 1, 1] = 0) (h101 : γ ![1, 0, 1] = 0)
    (h110 : γ ![1, 1, 0] = 0) (h111 : γ ![1, 1, 1] = 0) : Ach3 γ := by
  set φ0 := Complex.arg (γ ![0, 0, 0]) with hφ0
  set φ1 := Complex.arg (γ ![0, 0, 1]) with hφ1
  set φ2 := Complex.arg (γ ![0, 1, 0]) with hφ2
  set φ3 := Complex.arg (γ ![1, 0, 0]) with hφ3
  set θ : Fin 3 → ℝ := ![(φ3 - φ0) / 2, (φ2 - φ0) / 2, (φ1 - φ0) / 2] with hθ
  set α : ℝ := φ0 + (φ3 - φ0) / 2 + (φ2 - φ0) / 2 + (φ1 - φ0) / 2 with hα
  have hrot : rot (fun i => Dg (θ i)) γ =
      Complex.exp (α * Complex.I) • (fun x => ((‖γ x‖ : ℝ) : ℂ)) := by
    funext x
    obtain ⟨a, b, c, rfl⟩ : ∃ a b c : Fin 2, x = ![a, b, c] := ⟨x 0, x 1, x 2, RealRep3.vec3 x⟩
    have e0 : θ 0 = (φ3 - φ0) / 2 := rfl
    have e1 : θ 1 = (φ2 - φ0) / 2 := rfl
    have e2 : θ 2 = (φ1 - φ0) / 2 := rfl
    revert a b c
    simp only [Fin.forall_fin_two]
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩ <;>
      rw [rot_Dg] <;>
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    · have h := exp_mul_polar (γ ![0, 0, 0]) (θ 0 + θ 1 + θ 2) α (by rw [e0, e1, e2, hα]; ring)
      rw [← h, ← Complex.exp_add, ← Complex.exp_add]
      congr 2; push_cast; ring
    · have h := exp_mul_polar (γ ![0, 0, 1]) (θ 0 + θ 1 - θ 2) α (by rw [e0, e1, e2, hα]; ring)
      rw [← h, ← Complex.exp_add, ← Complex.exp_add]
      congr 2; push_cast; ring
    · have h := exp_mul_polar (γ ![0, 1, 0]) (θ 0 - θ 1 + θ 2) α (by rw [e0, e1, e2, hα]; ring)
      rw [← h, ← Complex.exp_add, ← Complex.exp_add]
      congr 2; push_cast; ring
    · simp [h011]
    · have h := exp_mul_polar (γ ![1, 0, 0]) (-θ 0 + θ 1 + θ 2) α (by rw [e0, e1, e2, hα]; ring)
      rw [← h, ← Complex.exp_add, ← Complex.exp_add]
      congr 2; push_cast; ring
    · simp [h101]
    · simp [h110]
    · simp [h111]
  refine Ach3.of_rot (R := fun i => Dg (θ i)) (fun i => SU2_Dg _) ?_
  refine Ach3.of_real (r := fun x => ((‖γ x‖ : ℝ) : ℂ)) ?_ (Complex.exp_ne_zero _) hrot
  funext x
  simp [cj]

/-! ### The hyperdeterminant -/

section Disc

variable {R : Type*} [CommRing R]

/-- `det (x N₀ + y N₁) = A x² + B x y + C y²` for the slices `N_b = β(b,·,·)`: the coefficient `A = det N₀`. -/
def dA (β : (Fin 3 → Fin 2) → R) : R := β ![0, 0, 0] * β ![0, 1, 1] - β ![0, 0, 1] * β ![0, 1, 0]

/-- The coefficient `C = det N₁`. -/
def dC (β : (Fin 3 → Fin 2) → R) : R := β ![1, 0, 0] * β ![1, 1, 1] - β ![1, 0, 1] * β ![1, 1, 0]

/-- The mixed coefficient `B`. -/
def dB (β : (Fin 3 → Fin 2) → R) : R :=
  β ![0, 0, 0] * β ![1, 1, 1] + β ![0, 1, 1] * β ![1, 0, 0] - β ![0, 0, 1] * β ![1, 1, 0] -
    β ![0, 1, 0] * β ![1, 0, 1]

/-- The Cayley hyperdeterminant (three-tangle up to a factor) `B² - 4AC`. -/
def disc3R (β : (Fin 3 → Fin 2) → R) : R := dB β ^ 2 - 4 * dA β * dC β

end Disc

/-! ### Linear algebra on `ℂ²` -/

/-- A unit vector of `ℂ²`. -/
def U2 (g : Fin 2 → ℂ) : Prop := conj (g 0) * g 0 + conj (g 1) * g 1 = 1

/-- The `SU(2)` matrix with second row `g` (its first row is `![conj (g 1), -conj (g 0)]`). -/
def Sm (g : Fin 2 → ℂ) : Op1 := !![conj (g 1), -conj (g 0); g 0, g 1]

/-- The first row of `Sm g`, orthogonal to `g`. -/
def perp (g : Fin 2 → ℂ) : Fin 2 → ℂ := ![conj (g 1), -conj (g 0)]

theorem SU2_Sm {g : Fin 2 → ℂ} (hg : U2 g) : SU2 (Sm g) := by
  have hg : conj (g 0) * g 0 + conj (g 1) * g 1 = 1 := hg
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Sm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
      first | exact hg | linear_combination hg | ring
  · rw [Matrix.det_fin_two]
    simp only [Sm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    linear_combination hg

/-- A singular `2 × 2` matrix has a unit kernel vector. -/
theorem exists_unit_ker (Z : Matrix (Fin 2) (Fin 2) ℂ) (h : Z.det = 0) :
    ∃ g : Fin 2 → ℂ, U2 g ∧ Z *ᵥ g = 0 := by
  obtain ⟨v, hv, hZ⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  set n : ℝ := Complex.normSq (v 0) + Complex.normSq (v 1) with hn
  have hnpos : 0 < n := by
    by_contra hle
    apply hv
    have h0 : Complex.normSq (v 0) = 0 := by
      nlinarith [Complex.normSq_nonneg (v 0), Complex.normSq_nonneg (v 1)]
    have h1 : Complex.normSq (v 1) = 0 := by
      nlinarith [Complex.normSq_nonneg (v 0), Complex.normSq_nonneg (v 1)]
    funext i
    fin_cases i
    · simpa using Complex.normSq_eq_zero.1 h0
    · simpa using Complex.normSq_eq_zero.1 h1
  have hc : ((Real.sqrt n)⁻¹ : ℝ) ^ 2 * n = 1 := by
    rw [inv_pow, Real.sq_sqrt hnpos.le]; exact inv_mul_cancel₀ hnpos.ne'
  have hcC : (((Real.sqrt n)⁻¹ : ℝ) : ℂ) ^ 2 * ((Complex.normSq (v 0) : ℝ) + (Complex.normSq (v 1) : ℝ)) = 1 := by
    exact_mod_cast hc
  refine ⟨(((Real.sqrt n)⁻¹ : ℝ) : ℂ) • v, ?_, ?_⟩
  · simp only [U2, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self] at hcC
    linear_combination hcC
  · rw [Matrix.mulVec_smul, hZ, smul_zero]

/-- The algebraic heart of the frame construction: if `X k = 0` and `X`, `Y` have vanishing determinant and
mixed determinant, the vectors `X k^⊥` and `Y k` are parallel. -/
theorem frame_alg (x00 x01 x10 x11 y00 y01 y10 y11 k0 k1 : ℂ) (hX : x00 * x11 - x01 * x10 = 0)
    (hD : x00 * y11 + y00 * x11 - x01 * y10 - y01 * x10 = 0) (hk0 : x00 * k0 + x01 * k1 = 0)
    (hk1 : x10 * k0 + x11 * k1 = 0) :
    (x00 * conj k1 - x01 * conj k0) * (y10 * k0 + y11 * k1)
      - (x10 * conj k1 - x11 * conj k0) * (y00 * k0 + y01 * k1) = 0 := by
  linear_combination (conj k1 * k1 + k0 * conj k0) * (hX + hD)
    - (((x00 + y00) * conj k1 - (x01 + y01) * conj k0)) * hk1
    + (((x10 + y10) * conj k1 - (x11 + y11) * conj k0)) * hk0

/-- The contraction `X_u(c, d) = Σ_b u_b β(b, c, d)` of the first qubit with the vector `u`. -/
def Mu (β : Ψ 3) (u : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun c d => u 0 * β ![0, c, d] + u 1 * β ![1, c, d]

/-- **A three-qubit vector with vanishing hyperdeterminant is achiral.** -/
theorem Ach3.of_disc {β : Ψ 3} (hd : disc3R β = 0) : Ach3 β := by
  have hS : (!![2 * dA β, dB β; dB β, 2 * dC β] : Matrix (Fin 2) (Fin 2) ℂ).det = 0 := by
    rw [Matrix.det_fin_two]
    simp only [disc3R] at hd
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    linear_combination (-1 : ℂ) * hd
  obtain ⟨u, hu, hSu⟩ := exists_unit_ker _ hS
  have G0 : 2 * dA β * u 0 + dB β * u 1 = 0 := by
    have := congrFun hSu 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have G1 : dB β * u 0 + 2 * dC β * u 1 = 0 := by
    have := congrFun hSu 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  simp only [dA, dB, dC] at G0 G1
  have hX : Mu β u 0 0 * Mu β u 1 1 - Mu β u 0 1 * Mu β u 1 0 = 0 := by
    simp only [Mu, Matrix.of_apply]
    linear_combination (u 0 / 2) * G0 + (u 1 / 2) * G1
  have hD : Mu β u 0 0 * Mu β (perp u) 1 1 + Mu β (perp u) 0 0 * Mu β u 1 1
      - Mu β u 0 1 * Mu β (perp u) 1 0 - Mu β (perp u) 0 1 * Mu β u 1 0 = 0 := by
    simp only [Mu, Matrix.of_apply]
    linear_combination (perp u 0) * G0 + (perp u 1) * G1
  obtain ⟨k, hk, hXk⟩ := exists_unit_ker (Mu β u) (by rw [Matrix.det_fin_two]; exact hX)
  have e1 : Mu β u 0 0 * k 0 + Mu β u 0 1 * k 1 = 0 := by
    have := congrFun hXk 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have e2 : Mu β u 1 0 * k 0 + Mu β u 1 1 * k 1 = 0 := by
    have := congrFun hXk 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hZ : (!![Mu β u 0 0 * conj (k 1) - Mu β u 0 1 * conj (k 0),
        Mu β u 1 0 * conj (k 1) - Mu β u 1 1 * conj (k 0);
      Mu β (perp u) 0 0 * k 0 + Mu β (perp u) 0 1 * k 1,
        Mu β (perp u) 1 0 * k 0 + Mu β (perp u) 1 1 * k 1] : Matrix (Fin 2) (Fin 2) ℂ).det = 0 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    exact frame_alg _ _ _ _ _ _ _ _ _ _ hX hD e1 e2
  obtain ⟨r, hr, hZr⟩ := exists_unit_ker _ hZ
  have f0 : (Mu β u 0 0 * conj (k 1) - Mu β u 0 1 * conj (k 0)) * r 0 +
      (Mu β u 1 0 * conj (k 1) - Mu β u 1 1 * conj (k 0)) * r 1 = 0 := by
    have := congrFun hZr 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have f1 : (Mu β (perp u) 0 0 * k 0 + Mu β (perp u) 0 1 * k 1) * r 0 +
      (Mu β (perp u) 1 0 * k 0 + Mu β (perp u) 1 1 * k 1) * r 1 = 0 := by
    have := congrFun hZr 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  simp only [Mu, perp, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e1 e2 f0 f1
  have hR : ∀ i, SU2 (![Sm u, Sm r, Sm k] i) := by
    intro i
    fin_cases i
    · exact SU2_Sm hu
    · exact SU2_Sm hr
    · exact SU2_Sm hk
  apply Ach3.of_rot hR
  apply Ach3.of_support
  · rw [RealRep3.rot3_apply]
    simp only [Fin.sum_univ_two, Sm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    linear_combination f1
  · rw [RealRep3.rot3_apply]
    simp only [Fin.sum_univ_two, Sm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    linear_combination (conj (r 1)) * e1 + (-conj (r 0)) * e2
  · rw [RealRep3.rot3_apply]
    simp only [Fin.sum_univ_two, Sm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    linear_combination f0
  · rw [RealRep3.rot3_apply]
    simp only [Fin.sum_univ_two, Sm, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    linear_combination (r 0) * e1 + (r 1) * e2

/-! ### The quartic has a root in `ℙ¹` -/

theorem exists_root_disc (p q : Ψ 3) :
    ∃ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) ∧ disc3R (fun x => s * p x + t * q x) = 0 := by
  by_cases h4 : disc3R p = 0
  · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
    simpa using h4
  · let n : (Fin 3 → Fin 2) → ℂ[X] := fun x => C (p x) * X + C (q x)
    let P : ℂ[X] := disc3R n
    have hP : ∀ z : ℂ, P.eval z = disc3R (fun x => z * p x + q x) := by
      intro z
      simp [P, n, disc3R, dA, dB, dC]
      ring
    have hdeg : P.natDegree ≤ 4 := by
      simp only [P, n, disc3R, dA, dB, dC]
      compute_degree
    have hcoeff : P.coeff 4 = disc3R p := by
      simp only [P, n, disc3R, dA, dB, dC]
      compute_degree!
    have hdeg4 : P.natDegree = 4 :=
      natDegree_eq_of_le_of_coeff_ne_zero hdeg (by rw [hcoeff]; exact h4)
    have hpos : 0 < P.degree := by
      rw [degree_eq_natDegree (by intro h0; rw [h0] at hdeg4; simp at hdeg4), hdeg4]
      exact_mod_cast (by norm_num : 0 < 4)
    obtain ⟨z, hz⟩ := Complex.exists_root hpos
    refine ⟨z, 1, Or.inr one_ne_zero, ?_⟩
    have := hP z
    rw [IsRoot.def] at hz
    rw [hz] at this
    simpa using this.symm

end FormalResearch.FrameFree.Converse
