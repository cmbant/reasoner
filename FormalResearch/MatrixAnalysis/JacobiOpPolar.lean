module

public import FormalResearch.MatrixAnalysis.Spectral.FanHoffmanPolar

/-!
# Jacobi operator package: polar repair

Paper J, `lem:thb-polar` (`thmB.tex`), operator norm.

* `jop_polar_repair`: abstract form for linear maps of a finite-dimensional real inner product space.
  The nearest-factor estimate is `fanHoffman_polarFactor` verbatim (a restatement, nothing new); the
  `2ε` estimate is the triangle inequality.
* `jop_polar_repair_matrix`: the form for real `n × n` matrices (`n` any finite type): derives
  injectivity of `G` from `‖G - U‖ < 1`, defines `Q = jop_polarMatrix G` as the matrix of the library's
  polar factor, and proves `Qᵀ Q = 1`, `Qᵀ G` positive semidefinite (so `Q` is the polar factor),
  `‖G - Q‖ ≤ ‖G - U‖`, `‖Q - U‖ ≤ 2‖G - U‖`.  The new content is this bridge; the estimates are
  Fan–Hoffman.

The Frobenius-norm form is in `JacobiOpFrobenius`.  Not formalised: an explicit functional-calculus
formula `G (GᵀG)^{-1/2}` with the continuous functional calculus of `Matrix` (the library's
`Polar.polarFactor` is `T ∘ (T^*T)^{-1/2}` for the positive root `Polar.polarRoot`).
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis

open FormalResearch.Racah

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Paper J's operator-norm polar repair, expressed for the library's `Racah.Polar.polarFactor`.
The nearest-factor bound restates `fanHoffman_polarFactor`. -/
theorem jop_polar_repair (T U : V →ₗ[ℝ] V) (hT : Function.Injective T)
    (hU : ∀ x, ‖U x‖ = ‖x‖) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ x, ‖(T - U) x‖ ≤ ε * ‖x‖) :
    (∀ x, ‖(T - Polar.polarFactor T hT) x‖ ≤ ε * ‖x‖) ∧
    (∀ x, ‖(Polar.polarFactor T hT - U) x‖ ≤ 2 * ε * ‖x‖) := by
  refine ⟨FormalResearch.MatrixAnalysis.Spectral.fanHoffman_polarFactor T hT U hU hε h, ?_⟩
  intro x
  have h1 := FormalResearch.MatrixAnalysis.Spectral.fanHoffman_polarFactor T hT U hU hε h x
  calc ‖(Polar.polarFactor T hT - U) x‖
      = ‖(Polar.polarFactor T hT x - T x) + (T x - U x)‖ := by congr 1; simp
    _ ≤ ‖(Polar.polarFactor T hT - T) x‖ + ‖(T - U) x‖ := norm_add_le _ _
    _ ≤ ε * ‖x‖ + ε * ‖x‖ := add_le_add (by
      have heq : (Polar.polarFactor T hT - T) x = -((T - Polar.polarFactor T hT) x) := by
        simp [sub_eq_add_neg, add_comm]
      rw [heq, norm_neg]
      exact h1) (h x)
    _ = 2 * ε * ‖x‖ := by ring

/-- info: 'FormalResearch.MatrixAnalysis.jop_polar_repair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.jop_polar_repair

section MatrixForm

open Matrix
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma jop_norm_apply_le (M : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    ‖toEuclideanLin M x‖ ≤ ‖M‖ * ‖x‖ :=
  l2_opNorm_mulVec M x

lemma jop_norm_le_of_apply (M : Matrix n n ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : EuclideanSpace ℝ n, ‖toEuclideanLin M x‖ ≤ C * ‖x‖) : ‖M‖ ≤ C := by
  rw [l2_opNorm_def]
  exact ContinuousLinearMap.opNorm_le_bound _ hC h

lemma jop_inner_orth {U : Matrix n n ℝ} (hU : Uᵀ * U = 1) (x y : EuclideanSpace ℝ n) :
    inner ℝ (toEuclideanLin U x) (toEuclideanLin U y) = inner ℝ x y := by
  have hU' : Uᴴ * U = 1 := by simpa using hU
  rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    ← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, hU', Matrix.toLpLin_one, LinearMap.id_apply]

lemma jop_norm_orth {U : Matrix n n ℝ} (hU : Uᵀ * U = 1) (x : EuclideanSpace ℝ n) :
    ‖toEuclideanLin U x‖ = ‖x‖ := by
  have h := jop_inner_orth hU x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- A real matrix within operator-norm distance `< 1` of an orthogonal matrix is injective. -/
lemma jop_injective_of_close {G U : Matrix n n ℝ} (hU : Uᵀ * U = 1) (hGU : ‖G - U‖ < 1) :
    Function.Injective (toEuclideanLin G) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 := jop_norm_apply_le (G - U) x
  have h2 : toEuclideanLin (G - U) x = - toEuclideanLin U x := by
    rw [map_sub, LinearMap.sub_apply, hx]; simp
  rw [h2, norm_neg, jop_norm_orth hU] at h1
  have : (1 - ‖G - U‖) * ‖x‖ ≤ 0 := by linarith
  have h3 : ‖x‖ ≤ 0 := by
    by_contra hc
    rw [not_le] at hc
    nlinarith
  exact norm_le_zero_iff.mp h3

/-- The polar factor of an injective real matrix, as a matrix: the matrix of `Polar.polarFactor` of
`toEuclideanLin G`.  It is `G (GᵀG)^{-1/2}` (`Polar.polarFactor` is defined as `T ∘ (T^*T)^{-1/2}`). -/
noncomputable def jop_polarMatrix (G : Matrix n n ℝ) (h : Function.Injective (toEuclideanLin G)) :
    Matrix n n ℝ :=
  (toEuclideanLin (m := n) (n := n) (𝕜 := ℝ)).symm (Polar.polarFactor (toEuclideanLin G) h)

lemma jop_toEuclideanLin_polarMatrix (G : Matrix n n ℝ) (h : Function.Injective (toEuclideanLin G)) :
    toEuclideanLin (jop_polarMatrix G h) = Polar.polarFactor (toEuclideanLin G) h := by
  simp [jop_polarMatrix]

/-- The polar factor of a matrix is orthogonal. -/
theorem jop_polarMatrix_orth (G : Matrix n n ℝ) (h : Function.Injective (toEuclideanLin G)) :
    (jop_polarMatrix G h)ᵀ * jop_polarMatrix G h = 1 := by
  apply (toEuclideanLin (m := n) (n := n) (𝕜 := ℝ)).injective
  have hadj : toEuclideanLin (jop_polarMatrix G h)ᵀ =
      LinearMap.adjoint (toEuclideanLin (jop_polarMatrix G h)) := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]; simp
  have hmul : ∀ A B : Matrix n n ℝ,
      toEuclideanLin (A * B) = toEuclideanLin A ∘ₗ toEuclideanLin B := fun A B =>
    Matrix.toLpLin_mul_same (p := 2) A B
  rw [hmul, hadj]
  ext x : 1
  apply ext_inner_left ℝ
  intro y
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, jop_toEuclideanLin_polarMatrix,
    Polar.inner_polarFactor]
  simp

lemma jop_adjoint_polarFactor (G : Matrix n n ℝ) (h : Function.Injective (toEuclideanLin G))
    (y : EuclideanSpace ℝ n) :
    LinearMap.adjoint (Polar.polarFactor (toEuclideanLin G) h) (Polar.polarFactor (toEuclideanLin G) h y)
      = y := by
  apply ext_inner_left ℝ
  intro x
  rw [LinearMap.adjoint_inner_right, Polar.inner_polarFactor]

/-- `Qᵀ G` is positive semidefinite: it is the positive root `(GᵀG)^{1/2}`. -/
theorem jop_polarMatrix_posSemidef (G : Matrix n n ℝ) (h : Function.Injective (toEuclideanLin G)) :
    ((jop_polarMatrix G h)ᵀ * G).PosSemidef := by
  rw [← Matrix.isPositive_toEuclideanLin_iff]
  have hadj : toEuclideanLin (jop_polarMatrix G h)ᵀ =
      LinearMap.adjoint (toEuclideanLin (jop_polarMatrix G h)) := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]; simp
  have heq : toEuclideanLin ((jop_polarMatrix G h)ᵀ * G) = Polar.polarRoot (toEuclideanLin G) := by
    have hmul : ∀ A B : Matrix n n ℝ,
        toEuclideanLin (A * B) = toEuclideanLin A ∘ₗ toEuclideanLin B := fun A B =>
      Matrix.toLpLin_mul_same (p := 2) A B
    rw [hmul, hadj]
    ext x : 1
    rw [LinearMap.comp_apply, ← Polar.polarFactor_root (toEuclideanLin G) h x]
    rw [jop_toEuclideanLin_polarMatrix]
    exact jop_adjoint_polarFactor G h _
  rw [heq]
  exact Polar.polarRoot_pos _

/-- **Polar repair** (Paper J `lem:thb-polar`, operator norm, matrix form).  If `U` is an orthogonal
real matrix and `‖G - U‖ < 1` (spectral norm), the polar factor `Q = G (GᵀG)^{-1/2}` of `G`
(`jop_polarMatrix`; invertibility of `G` is derived) is orthogonal, `Qᵀ G` is positive semidefinite
(this characterises `Q` as the polar factor), `‖G - Q‖ ≤ ‖G - U‖` and `‖Q - U‖ ≤ 2 ‖G - U‖`.

New here: the bridge between `Matrix` and `toEuclideanLin`, the derivation of injectivity, and the
orthogonality and positivity statements for the matrix `Q`.  The two norm bounds are
`fanHoffman_polarFactor` and the triangle inequality, through `jop_polar_repair`.
The Frobenius form is `jop_polar_repair_frobenius` (`JacobiOpFrobenius`). -/
theorem jop_polar_repair_matrix (G U : Matrix n n ℝ) (hU : Uᵀ * U = 1) (hGU : ‖G - U‖ < 1) :
    (jop_polarMatrix G (jop_injective_of_close hU hGU))ᵀ *
        jop_polarMatrix G (jop_injective_of_close hU hGU) = 1 ∧
      ((jop_polarMatrix G (jop_injective_of_close hU hGU))ᵀ * G).PosSemidef ∧
      ‖G - jop_polarMatrix G (jop_injective_of_close hU hGU)‖ ≤ ‖G - U‖ ∧
      ‖jop_polarMatrix G (jop_injective_of_close hU hGU) - U‖ ≤ 2 * ‖G - U‖ := by
  have hinj := jop_injective_of_close hU hGU
  have hrep := jop_polar_repair (toEuclideanLin G) (toEuclideanLin U) hinj
    (jop_norm_orth hU) (norm_nonneg (G - U))
    (fun x => by rw [← map_sub]; exact jop_norm_apply_le (G - U) x)
  refine ⟨jop_polarMatrix_orth G hinj, jop_polarMatrix_posSemidef G hinj, ?_, ?_⟩
  · refine jop_norm_le_of_apply _ (norm_nonneg _) fun x => ?_
    rw [map_sub, jop_toEuclideanLin_polarMatrix]
    exact hrep.1 x
  · refine jop_norm_le_of_apply _ (by positivity) fun x => ?_
    rw [map_sub, jop_toEuclideanLin_polarMatrix]
    exact hrep.2 x

/-- info: 'FormalResearch.MatrixAnalysis.jop_polar_repair_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.jop_polar_repair_matrix

end MatrixForm

end FormalResearch.MatrixAnalysis
