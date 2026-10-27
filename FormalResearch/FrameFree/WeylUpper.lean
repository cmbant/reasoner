import FormalResearch.FrameFree.WeylRealisation
import FormalResearch.FrameFree.WeylVertex

open scoped ComplexConjugate Matrix Kronecker
open FormalResearch.FourQubitEntropy

/-!
# The Weyl-vertex upper bound (R7, `thm:weyl` of Paper P), reduced to one polytope input

**Target.**  For `d : Fin 4 → ℂ`: `rotOverlap (psiMag d) (Psi.conj (psiMag d)) ≤ FKmag d`
(the lower bound `≥` is `WeylVertex`).  Maths source: `QI-A/paper/finite_copy_quantum_memory.tex`
(`thm:D4hadamard`, `cor:D4weylvertex`, `lem:fourprodvol`), which uses the polar description of
`conv W(D₄)` of Brandman–Fowler–Lins–Spitkovsky–Zobin (BFLSZ), Thm 7.1.

**Status: conditional.  The upper bound is proved from exactly one hypothesis, `PolarExtremeHyp`.**
It is NOT an unconditional theorem.  `PolarExtremeHyp` is a pure polytope statement (the polar of
`conv W(D₄) ⊂ M₄(ℝ)` is the convex hull of the explicit normals `ExtN`); it is not proved here.

## Proved here (no unproved placeholders, no new axioms; `propext`, `Classical.choice`, `Quot.sound` only)

* **Step 1, reduction to real matrices.**  `exists_real_rep`: for `a, b ∈ SU(2)` the local rotation
  `kron a b` is, in the magic basis, a real matrix `P ∈ SO(4)` (`magic_real`, via `E4 = ε⊗ε` and
  `ε ā ε = -a`).  `ip_local_real4`, `FKmag2_le_rotOverlap`, `rotOverlap_le_FKmag2`: the rotation
  overlap equals `FKmag2 d d' = max_w |⟨d, w d'⟩|²` as soon as `HadamardWeylBoundRe` holds, i.e.
  `Σ x_i (A∘B)_ij y_j ≤ max_w |weylPair x y w|` for realised `A, B`.
* **All facet inequalities for realised matrices** (`tri N A B = Σ N_ij A_ij B_ij ≤ 1`, `ExtN`):
  rows and columns (`tri_rowN_le`, `tri_colN_le`, Cauchy–Schwarz), opposite-parity rank-one
  normals (`tri_parN_le`, via `trace_le_two` for improper orthogonal matrices), and the whole
  `W(D₄) × W(D₄)` orbit of the exceptional normal `Fmat` (`tri_orbit_le`), which rests on the
  quaternion identity `tri_Fmat`, Fischer's four-product bound `fourprodvol` (Laplace expansion,
  Lagrange identity, AM-GM), the sandwich identity `tri_wmat` and the reflection trick `Dm`.
  `tri_le_one_of_ext`, `tri_le_one_of_hull`: hence `tri N A B ≤ 1` on `conv ExtN`.
* **Polar step.**  `polar_to_re : PolarExtremeHyp → HadamardWeylBoundRe` (phase trick, `ε → 0`,
  no Hahn-Banach).  Final theorems: `rotOverlap_conj_le_FKmag_of_polar`,
  `rotOverlap_conj_eq_FKmag_of_polar`, `rotOverlap_eq_FKmag2_of_polar`, all taking `hyp : PolarExtremeHyp`.

## Not proved here, and why

* `PolarExtremeHyp` (BFLSZ Thm 7.1).  Its content is facet-completeness of a 16-dimensional
  polytope with 192 vertices (about 9.5k facets in `W(D₄) × W(D₄)` orbits).  Mathlib has no
  Minkowski-Weyl / polytope duality and there is no cheap finite exact certificate.
* The `SO(4)` form `HadamardWeylBound` is stated but not derived: surjectivity `SU(2)² → SO(4)` is
  not formalised, so only the form `HadamardWeylBoundRe` (matrices realised by `SU(2)` pairs) is used;
  this suffices for `rotOverlap`.
* No mathematical error was found in the paper's argument.
-/

namespace FormalResearch.FrameFree.WeylUpper

/-- The entries of `a ∈ SU(2)`: `ā₀₀ = a₁₁`, `ā₁₀ = -a₀₁`. -/
theorem su2_entries {a : Op1} (h : SU2 a) : conj (a 0 0) = a 1 1 ∧ conj (a 1 0) = - a 0 1 := by
  have hadj : aᴴ = a.adjugate := by
    have h1 : a * a.adjugate = 1 := by rw [Matrix.mul_adjugate, h.2]; simp
    calc aᴴ = aᴴ * (a * a.adjugate) := by rw [h1, Matrix.mul_one]
      _ = (aᴴ * a) * a.adjugate := by rw [Matrix.mul_assoc]
      _ = a.adjugate := by rw [h.1, Matrix.one_mul]
  have e1 := congrFun (congrFun hadj 0) 0
  have e2 := congrFun (congrFun hadj 0) 1
  simp [Matrix.conjTranspose_apply, Matrix.adjugate_fin_two] at e1 e2
  exact ⟨e1, by simpa using e2⟩

theorem eps_conj_eps {a : Op1} (h : SU2 a) : eps2 * a.map conj * eps2 = -a := by
  obtain ⟨h1, h2⟩ := su2_entries h
  have h1' : conj (a 1 1) = a 0 0 := by rw [← h1, Complex.conj_conj]
  have h2' : conj (a 0 1) = - a 1 0 := by
    have := congrArg conj h2
    rw [Complex.conj_conj, map_neg] at this
    linear_combination this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eps2, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, h1, h2, h1', h2']

theorem E4_conj_kron {a b : Op1} (ha : SU2 a) (hb : SU2 b) :
    E4 * (kron a b).map conj * E4 = kron a b := by
  have hk : (kron a b).map conj = (a.map conj) ⊗ₖ (b.map conj) := by
    ext ⟨i1, i2⟩ ⟨j1, j2⟩; simp [kron, Matrix.kroneckerMap_apply]
  unfold E4 kron at *
  rw [hk, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, eps_conj_eps ha, eps_conj_eps hb]
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp [Matrix.kroneckerMap_apply]

theorem E4_mul_magicB : E4 * magicB = magicB.map conj := by
  calc E4 * magicB = (magicB.map conj * magicBᵀ) * (E4 * magicB) := by
        rw [magicBbar_mul, Matrix.one_mul]
    _ = magicB.map conj * (magicBᵀ * E4 * magicB) := by simp only [Matrix.mul_assoc]
    _ = magicB.map conj := by rw [magicB_E4, Matrix.mul_one]

theorem E4_conjTranspose : E4ᴴ = E4 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [E4, kron, eps2, Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply]

theorem magicBT_eq : magicBᵀ = magicBᴴ * E4 := by
  have h := congrArg Matrix.conjTranspose E4_mul_magicB
  rw [Matrix.conjTranspose_mul, E4_conjTranspose] at h
  rw [h]
  ext i j; simp [Matrix.conjTranspose_apply]

/-- For `a, b ∈ SU(2)` the matrix `Bᴴ (a ⊗ b) B` of the rotation in magic coordinates is real. -/
theorem magic_real {a b : Op1} (ha : SU2 a) (hb : SU2 b) :
    (magicBᴴ * kron a b * magicB).map conj = magicBᴴ * kron a b * magicB := by
  have h1 : (magicBᴴ).map conj = magicBᴴ * E4 := by rw [← magicBT_eq]; ext i j; simp [Matrix.conjTranspose_apply]
  rw [Matrix.map_mul (f := starRingEnd ℂ), Matrix.map_mul (f := starRingEnd ℂ), h1, ← E4_mul_magicB]
  calc magicBᴴ * E4 * (kron a b).map conj * (E4 * magicB)
      = magicBᴴ * (E4 * (kron a b).map conj * E4) * magicB := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [E4_conj_kron ha hb]

theorem cmat_injective : Function.Injective cmat :=
  Matrix.map_injective Complex.ofReal_injective

theorem cmat_transpose (P : Matrix Pair Pair ℝ) : cmat Pᵀ = (cmat P)ᴴ := by
  ext i j; simp [cmat, Matrix.conjTranspose_apply]

theorem det_cmat (P : Matrix Pair Pair ℝ) : (cmat P).det = (P.det : ℂ) := by
  have := RingHom.map_det Complex.ofRealHom P
  exact this.symm

theorem det_kron {a b : Op1} (ha : SU2 a) (hb : SU2 b) : (kron a b).det = 1 := by
  unfold kron
  rw [Matrix.det_kronecker, ha.2, hb.2]; simp

/-- **Local `SU(2)` rotations are real `SO(4)` rotations in magic coordinates.** -/
theorem exists_real_rep {a b : Op1} (ha : SU2 a) (hb : SU2 b) :
    ∃ P : Matrix Pair Pair ℝ, kron a b * magicB = magicB * cmat P ∧ Pᵀ * P = 1 ∧ P.det = 1 := by
  set M : Mat4 := magicBᴴ * kron a b * magicB with hM
  have hreal := magic_real ha hb
  set P : Matrix Pair Pair ℝ := Matrix.of fun i j => (M i j).re with hP
  have hPM : cmat P = M := by
    ext i j
    have him : (M i j).im = 0 := by
      have := congrFun (congrFun hreal i) j
      simpa [Matrix.map_apply, Complex.conj_eq_iff_im] using this
    apply Complex.ext <;> simp [cmat, hP, him]
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [hPM, hM]
    calc kron a b * magicB = (magicB * magicBᴴ) * kron a b * magicB := by
          rw [magicB_unitary', Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  · apply cmat_injective
    rw [cmat_one, cmat_mul, cmat_transpose, hPM, hM]
    have hK := kron_unitary ha.1 hb.1
    calc (magicBᴴ * kron a b * magicB)ᴴ * (magicBᴴ * kron a b * magicB)
        = magicBᴴ * (kron a b)ᴴ * (magicB * magicBᴴ) * kron a b * magicB := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = magicBᴴ * ((kron a b)ᴴ * kron a b) * magicB := by
          rw [magicB_unitary']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hK, Matrix.mul_one, magicB_unitary]
  · have h1 : (P.det : ℂ) = 1 := by
      rw [← det_cmat, hPM, hM, Matrix.det_mul, Matrix.det_mul, det_kron ha hb, mul_one,
        ← Matrix.det_mul, magicB_unitary]
      simp
    exact_mod_cast h1

/-! ### Reduction to a statement about pairs of `SO(4)` matrices -/

/-- `SO(4)` as real `4×4` matrices (indexed by `Fin 4`). -/
def SO4 (A : Matrix (Fin 4) (Fin 4) ℝ) : Prop := Aᵀ * A = 1 ∧ A.det = 1

/-- Reindexing `Pair → Fin 4`. -/
def reidx (P : Matrix Pair Pair ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  P.submatrix pairEquiv.symm pairEquiv.symm

theorem reidx_SO4 {P : Matrix Pair Pair ℝ} (h1 : Pᵀ * P = 1) (h2 : P.det = 1) : SO4 (reidx P) := by
  refine ⟨?_, ?_⟩
  · have : (reidx P)ᵀ * reidx P = (Pᵀ * P).submatrix pairEquiv.symm pairEquiv.symm := by
      unfold reidx
      rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
    rw [this, h1]
    ext i j; simp [Matrix.one_apply]
  · unfold reidx
    rw [Matrix.det_submatrix_equiv_self, h2]

/-- The Hadamard pairing `∑ᵢⱼ xᵢ (A∘B)ᵢⱼ yⱼ`. -/
def hadPair (x y : Fin 4 → ℂ) (A B : Matrix (Fin 4) (Fin 4) ℝ) : ℂ :=
  ∑ i, ∑ j, x i * ((A i j : ℂ) * (B i j : ℂ)) * y j

/-- The Weyl-vertex pairing `∑ₖ xₖ (±1)ₖ y_{σ k}` for `w = (σ, e) ∈ W(D₄)`. -/
def weylPair (x y : Fin 4 → ℂ) (w : SP) : ℂ := ∑ k, x k * (sg (w.2 k) : ℂ) * y (w.1 k)

/-- The determinant of the `4×4` matrix with columns `x 0, …, x 3`, by Laplace expansion along the
row pair `{0,1}`: `∑_{I} ± U_I W_{Iᶜ}` (`U_I`, `W_I` the `2×2` minors of the first and last two rows). -/
def lap (x : Fin 4 → Fin 4 → ℝ) : ℝ :=
  (x 0 0 * x 1 1 - x 1 0 * x 0 1) * (x 2 2 * x 3 3 - x 3 2 * x 2 3)
  - (x 0 0 * x 2 1 - x 2 0 * x 0 1) * (x 1 2 * x 3 3 - x 3 2 * x 1 3)
  + (x 0 0 * x 3 1 - x 3 0 * x 0 1) * (x 1 2 * x 2 3 - x 2 2 * x 1 3)
  + (x 1 0 * x 2 1 - x 2 0 * x 1 1) * (x 0 2 * x 3 3 - x 3 2 * x 0 3)
  - (x 1 0 * x 3 1 - x 3 0 * x 1 1) * (x 0 2 * x 2 3 - x 2 2 * x 0 3)
  + (x 2 0 * x 3 1 - x 3 0 * x 2 1) * (x 0 2 * x 1 3 - x 1 2 * x 0 3)

theorem lap_eq_det (x : Fin 4 → Fin 4 → ℝ) : lap x = (Matrix.of fun k j => x j k).det := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, lap]
  simp [Matrix.det_fin_three, Fin.succAbove, Matrix.submatrix]
  ring

theorem amgm4 (r : Fin 4 → ℝ) (hr : ∀ j, 0 ≤ r j) :
    r 0 * r 1 * r 2 * r 3 ≤ ((r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 + r 3 ^ 2) / 4) ^ 2 := by
  have h01 : r 0 * r 1 ≤ (r 0 ^ 2 + r 1 ^ 2) / 2 := by nlinarith [sq_nonneg (r 0 - r 1)]
  have h23 : r 2 * r 3 ≤ (r 2 ^ 2 + r 3 ^ 2) / 2 := by nlinarith [sq_nonneg (r 2 - r 3)]
  have p01 : 0 ≤ r 0 * r 1 := mul_nonneg (hr 0) (hr 1)
  have p23 : 0 ≤ r 2 * r 3 := mul_nonneg (hr 2) (hr 3)
  calc r 0 * r 1 * r 2 * r 3 = (r 0 * r 1) * (r 2 * r 3) := by ring
    _ ≤ ((r 0 ^ 2 + r 1 ^ 2) / 2) * ((r 2 ^ 2 + r 3 ^ 2) / 2) :=
        mul_le_mul h01 h23 p23 (by positivity)
    _ ≤ _ := by nlinarith [sq_nonneg ((r 0 ^ 2 + r 1 ^ 2) / 2 - (r 2 ^ 2 + r 3 ^ 2) / 2)]

/-- `|Re ∏ u_j| ≤ (Σ|u_j|²/4)²`. -/
theorem abs_re_prod_le (u : Fin 4 → ℂ) :
    |(∏ j, u j).re| ≤ ((‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 + ‖u 2‖ ^ 2 + ‖u 3‖ ^ 2) / 4) ^ 2 := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_prod, Fin.prod_univ_four]
  exact amgm4 (fun j => ‖u j‖) (fun j => norm_nonneg _)

/-- Lagrange: the sum of squares of the `2×2` minors of a `2×4` matrix is `det(UUᵀ) ≤ (tr/2)²`. -/
theorem minors_sq_le (r1 r2 : Fin 4 → ℝ) :
    (r1 0 * r2 1 - r1 1 * r2 0) ^ 2 + (r1 0 * r2 2 - r1 2 * r2 0) ^ 2 + (r1 0 * r2 3 - r1 3 * r2 0) ^ 2
    + (r1 1 * r2 2 - r1 2 * r2 1) ^ 2 + (r1 1 * r2 3 - r1 3 * r2 1) ^ 2
    + (r1 2 * r2 3 - r1 3 * r2 2) ^ 2 ≤
    (((r1 0 ^ 2 + r1 1 ^ 2 + r1 2 ^ 2 + r1 3 ^ 2) + (r2 0 ^ 2 + r2 1 ^ 2 + r2 2 ^ 2 + r2 3 ^ 2)) / 2) ^ 2 := by
  nlinarith [sq_nonneg (r1 0 * r2 0 + r1 1 * r2 1 + r1 2 * r2 2 + r1 3 * r2 3),
    sq_nonneg ((r1 0 ^ 2 + r1 1 ^ 2 + r1 2 ^ 2 + r1 3 ^ 2) - (r2 0 ^ 2 + r2 1 ^ 2 + r2 2 ^ 2 + r2 3 ^ 2))]

theorem abs_lap_le (x : Fin 4 → Fin 4 → ℝ) :
    |lap x| ≤ ((x 0 0 ^ 2 + x 0 1 ^ 2 + x 1 0 ^ 2 + x 1 1 ^ 2 + x 2 0 ^ 2 + x 2 1 ^ 2 + x 3 0 ^ 2 + x 3 1 ^ 2) / 2) *
      ((x 0 2 ^ 2 + x 0 3 ^ 2 + x 1 2 ^ 2 + x 1 3 ^ 2 + x 2 2 ^ 2 + x 2 3 ^ 2 + x 3 2 ^ 2 + x 3 3 ^ 2) / 2) := by
  set sU := (x 0 0 ^ 2 + x 0 1 ^ 2 + x 1 0 ^ 2 + x 1 1 ^ 2 + x 2 0 ^ 2 + x 2 1 ^ 2 + x 3 0 ^ 2 + x 3 1 ^ 2) with hsU
  set sW := (x 0 2 ^ 2 + x 0 3 ^ 2 + x 1 2 ^ 2 + x 1 3 ^ 2 + x 2 2 ^ 2 + x 2 3 ^ 2 + x 3 2 ^ 2 + x 3 3 ^ 2) with hsW
  have hU := minors_sq_le (fun j => x j 0) (fun j => x j 1)
  have hW := minors_sq_le (fun j => x j 2) (fun j => x j 3)
  have hsU0 : 0 ≤ sU := by positivity
  have hsW0 : 0 ≤ sW := by positivity
  -- Cauchy–Schwarz on the six terms
  set a : Fin 6 → ℝ := ![x 0 0 * x 1 1 - x 1 0 * x 0 1, x 0 0 * x 2 1 - x 2 0 * x 0 1,
    x 0 0 * x 3 1 - x 3 0 * x 0 1, x 1 0 * x 2 1 - x 2 0 * x 1 1, x 1 0 * x 3 1 - x 3 0 * x 1 1,
    x 2 0 * x 3 1 - x 3 0 * x 2 1] with ha
  set b : Fin 6 → ℝ := ![x 2 2 * x 3 3 - x 3 2 * x 2 3, -(x 1 2 * x 3 3 - x 3 2 * x 1 3),
    x 1 2 * x 2 3 - x 2 2 * x 1 3, x 0 2 * x 3 3 - x 3 2 * x 0 3, -(x 0 2 * x 2 3 - x 2 2 * x 0 3),
    x 0 2 * x 1 3 - x 1 2 * x 0 3] with hb
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have hlap : lap x = ∑ i, a i * b i := by
    simp [lap, ha, hb, Fin.sum_univ_succ]; ring
  have hsa : ∑ i, a i ^ 2 ≤ (sU / 2) ^ 2 := by
    have e1 : ∑ i, a i ^ 2 = (x 0 0 * x 1 1 - x 1 0 * x 0 1) ^ 2 + (x 0 0 * x 2 1 - x 2 0 * x 0 1) ^ 2
        + (x 0 0 * x 3 1 - x 3 0 * x 0 1) ^ 2 + (x 1 0 * x 2 1 - x 2 0 * x 1 1) ^ 2
        + (x 1 0 * x 3 1 - x 3 0 * x 1 1) ^ 2 + (x 2 0 * x 3 1 - x 3 0 * x 2 1) ^ 2 := by
      simp [ha, Fin.sum_univ_succ]; ring
    rw [e1]
    refine hU.trans (le_of_eq ?_)
    simp only [hsU]; ring
  have hsb : ∑ i, b i ^ 2 ≤ (sW / 2) ^ 2 := by
    have e1 : ∑ i, b i ^ 2 = (x 0 2 * x 1 3 - x 1 2 * x 0 3) ^ 2 + (x 0 2 * x 2 3 - x 2 2 * x 0 3) ^ 2
        + (x 0 2 * x 3 3 - x 3 2 * x 0 3) ^ 2 + (x 1 2 * x 2 3 - x 2 2 * x 1 3) ^ 2
        + (x 1 2 * x 3 3 - x 3 2 * x 1 3) ^ 2 + (x 2 2 * x 3 3 - x 3 2 * x 2 3) ^ 2 := by
      simp [hb, Fin.sum_univ_succ]; ring
    rw [e1]
    refine hW.trans (le_of_eq ?_)
    simp only [hsW]; ring
  have : (lap x) ^ 2 ≤ ((sU / 2) * (sW / 2)) ^ 2 := by
    rw [hlap, mul_pow]
    exact hcs.trans (mul_le_mul hsa hsb (by positivity) (by positivity))
  exact abs_le_of_sq_le_sq' this (by positivity) |> fun h => abs_le.2 h

theorem norm_mk_sq (a b : ℝ) : ‖(⟨a, b⟩ : ℂ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_mk]; ring

/-- **Four products plus four-volume** (`QI-A`, `lem:fourprodvol`), signed form: for four unit vectors
`x j = (u_j, v_j) ∈ ℂ² ≅ ℝ⁴`, `-Re(∏u_j + ∏v_j) + ½ det[x_0,…,x_3] ≤ 1`. -/
theorem fourprodvol (x : Fin 4 → Fin 4 → ℝ) (hn : ∀ j, x j 0 ^ 2 + x j 1 ^ 2 + x j 2 ^ 2 + x j 3 ^ 2 = 1) :
    -((∏ j, (⟨x j 0, x j 1⟩ : ℂ)).re + (∏ j, (⟨x j 2, x j 3⟩ : ℂ)).re) + (1 / 2) * lap x ≤ 1 := by
  have h1 := abs_re_prod_le (fun j => (⟨x j 0, x j 1⟩ : ℂ))
  have h2 := abs_re_prod_le (fun j => (⟨x j 2, x j 3⟩ : ℂ))
  have h3 := abs_lap_le x
  simp only [norm_mk_sq] at h1 h2
  have e0 := hn 0
  have e1 := hn 1
  have e2 := hn 2
  have e3 := hn 3
  set s := x 0 0 ^ 2 + x 0 1 ^ 2 + x 1 0 ^ 2 + x 1 1 ^ 2 + x 2 0 ^ 2 + x 2 1 ^ 2 + x 3 0 ^ 2 + x 3 1 ^ 2 with hs
  have hW : x 0 2 ^ 2 + x 0 3 ^ 2 + x 1 2 ^ 2 + x 1 3 ^ 2 + x 2 2 ^ 2 + x 2 3 ^ 2 + x 3 2 ^ 2 + x 3 3 ^ 2 = 4 - s := by
    rw [hs]; linarith
  rw [hW] at h3
  have h1' : |(∏ j, (⟨x j 0, x j 1⟩ : ℂ)).re| ≤ (s / 4) ^ 2 := by
    refine h1.trans (le_of_eq ?_); rw [hs]; ring
  have h2' : |(∏ j, (⟨x j 2, x j 3⟩ : ℂ)).re| ≤ ((4 - s) / 4) ^ 2 := by
    refine h2.trans (le_of_eq ?_); congr 1; linarith
  have a1 := neg_abs_le (∏ j, (⟨x j 0, x j 1⟩ : ℂ)).re
  have a2 := neg_abs_le (∏ j, (⟨x j 2, x j 3⟩ : ℂ)).re
  have a3 := le_abs_self (lap x)
  have key : (s / 4) ^ 2 + ((4 - s) / 4) ^ 2 + (1 / 2) * ((s / 2) * ((4 - s) / 2)) = 1 := by ring
  generalize (∏ j, (⟨x j 0, x j 1⟩ : ℂ)).re = r1 at *
  generalize (∏ j, (⟨x j 2, x j 3⟩ : ℂ)).re = r2 at *
  generalize lap x = L at *
  generalize s = t at *
  linarith [a1, a2, a3]



/-- The `SU(2)` matrix of the real 4-vector `q`. -/
noncomputable def ofQ (q : Fin 4 → ℝ) : Op1 :=
  !![(q 0 : ℂ) + (q 1 : ℂ) * Complex.I, -(q 2 : ℂ) + (q 3 : ℂ) * Complex.I;
     (q 2 : ℂ) + (q 3 : ℂ) * Complex.I, (q 0 : ℂ) - (q 1 : ℂ) * Complex.I]

/-- The real `SO(4)` matrix of the pair of real 4-vectors `(q,p)`. -/
def Pq (q p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
!![
  p 0*q 0 - p 1*q 1 + p 2*q 2 - p 3*q 3, -p 0*q 3 + p 1*q 2 + p 2*q 1 - p 3*q 0, p 0*q 2 + p 1*q 3 - p 2*q 0 - p 3*q 1, -p 0*q 1 - p 1*q 0 - p 2*q 3 - p 3*q 2;
  p 0*q 3 + p 1*q 2 + p 2*q 1 + p 3*q 0, p 0*q 0 + p 1*q 1 - p 2*q 2 - p 3*q 3, p 0*q 1 - p 1*q 0 - p 2*q 3 + p 3*q 2, p 0*q 2 - p 1*q 3 + p 2*q 0 - p 3*q 1;
  -p 0*q 2 + p 1*q 3 + p 2*q 0 - p 3*q 1, -p 0*q 1 + p 1*q 0 - p 2*q 3 + p 3*q 2, p 0*q 0 + p 1*q 1 + p 2*q 2 + p 3*q 3, p 0*q 3 + p 1*q 2 - p 2*q 1 - p 3*q 0;
  p 0*q 1 + p 1*q 0 - p 2*q 3 - p 3*q 2, -p 0*q 2 - p 1*q 3 - p 2*q 0 - p 3*q 1, -p 0*q 3 + p 1*q 2 - p 2*q 1 + p 3*q 0, p 0*q 0 - p 1*q 1 - p 2*q 2 + p 3*q 3]

def PqP (q p : Fin 4 → ℝ) : Matrix Pair Pair ℝ := Matrix.of fun i j => Pq q p (pairEquiv i) (pairEquiv j)

theorem pairEquiv_00 : pairEquiv ((0 : Fin 2), (0 : Fin 2)) = 0 := rfl
theorem pairEquiv_01 : pairEquiv ((0 : Fin 2), (1 : Fin 2)) = 1 := rfl
theorem pairEquiv_10 : pairEquiv ((1 : Fin 2), (0 : Fin 2)) = 2 := rfl
theorem pairEquiv_11 : pairEquiv ((1 : Fin 2), (1 : Fin 2)) = 3 := rfl

set_option maxHeartbeats 4000000 in
theorem magic_ofQ (q p : Fin 4 → ℝ) :
    kron (ofQ q) (ofQ p) * magicB = magicB * cmat (PqP q p) := by
  have hrt2 : rt ^ 2 = 1 / 2 := rt_sq
  have hrt4 : rt ^ 4 = 1 / 4 := by rw [show rt ^ 4 = (rt ^ 2) ^ 2 by ring, hrt2]; norm_num
  have hrt3 : rt ^ 3 = rt / 2 := by rw [show rt ^ 3 = rt * rt ^ 2 by ring, hrt2]; ring
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [show Complex.I ^ 3 = Complex.I * Complex.I ^ 2 by ring, Complex.I_sq]; ring
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [kron, magicB, cmat, PqP, Pq, ofQ, pairEquiv_00, pairEquiv_01, pairEquiv_10, pairEquiv_11, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply] <;>
  (try ring_nf) <;> (try simp only [Complex.I_sq, hI3, hrt2, hrt3, hrt4]) <;> (try ring_nf)


/-- The trilinear pairing `∑ᵢⱼ Nᵢⱼ Aᵢⱼ Bᵢⱼ = ⟨N, A∘B⟩`. -/
def tri (N A B : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := ∑ i, ∑ j, N i j * (A i j * B i j)

/-- The exceptional facet normal `F` of `conv W(D₄)` (Brandman–Fowler–Lins–Spitkovsky–Zobin, Thm 7.1). -/
noncomputable def Fmat : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1/2, 1/2, 0, -1/4; 1/2, -1/2, 0, -1/4; -1/4, -1/4, -1/4, 0; 0, 0, 0, 1/4]

/-- The four unit vectors of `fourprodvol` attached to `(q,p,w,z)`. -/
def Xvec (q p w z : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![p 0, p 3, p 2, -p 1], ![-q 3, q 0, q 1, q 2], ![w 0, w 3, -w 2, w 1], ![z 3, -z 0, z 1, z 2]]

theorem tri_Fmat (q p w z : Fin 4 → ℝ) :
    tri Fmat (Pq q p) (Pq w z) =
      -((∏ j, (⟨Xvec q p w z j 0, Xvec q p w z j 1⟩ : ℂ)).re +
        (∏ j, (⟨Xvec q p w z j 2, Xvec q p w z j 3⟩ : ℂ)).re) + (1 / 2) * lap (Xvec q p w z) := by
  simp [tri, Fmat, Pq, Xvec, lap, Fin.prod_univ_four, Fin.sum_univ_four, Complex.mul_re, Complex.mul_im]
  ring

/-- **The exceptional facet for the identity orbit element**: `⟨F, A∘B⟩ ≤ 1` for the matrices of unit
quaternion pairs. -/
theorem tri_Fmat_le (q p w z : Fin 4 → ℝ) (hq : ∑ i, q i ^ 2 = 1) (hp : ∑ i, p i ^ 2 = 1)
    (hw : ∑ i, w i ^ 2 = 1) (hz : ∑ i, z i ^ 2 = 1) : tri Fmat (Pq q p) (Pq w z) ≤ 1 := by
  rw [tri_Fmat]
  refine fourprodvol _ ?_
  simp only [Fin.sum_univ_four] at hq hp hw hz
  intro j
  fin_cases j <;> simp [Xvec] <;> linarith






/-- The signed permutation matrix of `w = (σ, e)`: row `i` has the entry `(-1)^{e i}` in column `σ i`. -/
def wmat (w : SP) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => if w.1 i = j then (sg (w.2 i) : ℝ) else 0

theorem wmat_mul (w w' : SP) :
    wmat w * wmat w' = wmat (w'.1 * w.1, fun i => xor (w.2 i) (w'.2 (w.1 i))) := by
  ext i j
  simp only [wmat, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (w.1 i)]
  · by_cases h : w'.1 (w.1 i) = j
    · simp [h, sg_xor]
    · simp [h]
  · intro k _ hk; simp [Ne.symm hk]
  · simp

theorem wmat_transpose (w : SP) :
    (wmat w)ᵀ = wmat (w.1⁻¹, fun k => w.2 (w.1⁻¹ k)) := by
  ext k i
  simp only [wmat, Matrix.transpose_apply, Matrix.of_apply]
  by_cases h : w.1 i = k
  · have : w.1⁻¹ k = i := by rw [← h]; simp
    show (if w.1 i = k then (sg (w.2 i) : ℝ) else 0) = if w.1⁻¹ k = i then (sg (w.2 (w.1⁻¹ k)) : ℝ) else 0
    rw [if_pos h, if_pos this, this]
  · have : ¬ w.1⁻¹ k = i := by
      intro hh; apply h; rw [← hh]; simp
    show (if w.1 i = k then (sg (w.2 i) : ℝ) else 0) = if w.1⁻¹ k = i then (sg (w.2 (w.1⁻¹ k)) : ℝ) else 0
    rw [if_neg h, if_neg this]

theorem det_wmat (w : SP) : (wmat w).det = ((Equiv.Perm.sign w.1 : ℤˣ) : ℝ) * ∏ k, (sg (w.2 k) : ℝ) := by
  have : wmat w = Matrix.diagonal (fun i => (sg (w.2 i) : ℝ)) *
      (w.1.toPEquiv.toMatrix : Matrix (Fin 4) (Fin 4) ℝ) := by
    ext i j; simp [wmat, Matrix.diagonal_mul, PEquiv.toMatrix_apply]
  rw [this, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permutation]; ring

theorem wmat_entry (g h : SP) (N : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    (wmat g * N * wmat h) i j = (sg (g.2 i) : ℝ) * (sg (h.2 (h.1⁻¹ j)) : ℝ) * N (g.1 i) (h.1⁻¹ j) := by
  simp only [Matrix.mul_apply, wmat, Matrix.of_apply]
  have h1 : ∀ l, ∑ k, (if g.1 i = k then (sg (g.2 i) : ℝ) else 0) * N k l = (sg (g.2 i) : ℝ) * N (g.1 i) l := by
    intro l
    rw [Finset.sum_eq_single (g.1 i)]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · simp
  simp only [h1]
  rw [Finset.sum_eq_single (h.1⁻¹ j)]
  · simp
    ring
  · intro l _ hl
    have : ¬ h.1 l = j := by
      intro hh; apply hl; rw [← hh]; simp
    simp [this]
  · simp

theorem wmat_sandwich (g h : SP) (A : Matrix (Fin 4) (Fin 4) ℝ) (k l : Fin 4) :
    ((wmat g)ᵀ * A * (wmat h)ᵀ) k l =
      (sg (g.2 (g.1⁻¹ k)) : ℝ) * (sg (h.2 l) : ℝ) * A (g.1⁻¹ k) (h.1 l) := by
  rw [wmat_transpose, wmat_transpose, wmat_entry]
  simp

/-- The sandwich identity: `⟨gNh, A∘B⟩ = ⟨N, A'∘B'⟩` with `A' = gᵀ A hᵀ`, `B' = |g|ᵀ B |h|ᵀ`. -/
theorem tri_wmat (g h : SP) (N A B : Matrix (Fin 4) (Fin 4) ℝ) :
    tri (wmat g * N * wmat h) A B =
      tri N ((wmat g)ᵀ * A * (wmat h)ᵀ) ((wmat (g.1, fun _ => false))ᵀ * B * (wmat (h.1, fun _ => false))ᵀ) := by
  unfold tri
  simp only [wmat_entry, wmat_sandwich]
  rw [← Equiv.sum_comp g.1.symm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Equiv.sum_comp h.1]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [sg]




/-! ### Realizable matrices -/

/-- A `4×4` real matrix indexed by `Fin 4` as a matrix indexed by `Pair`. -/
def toPair (M : Matrix (Fin 4) (Fin 4) ℝ) : Matrix Pair Pair ℝ := M.submatrix pairEquiv pairEquiv

/-- `M` is the magic-coordinate matrix of a local rotation `a ⊗ b`, `a, b ∈ SU(2)`
(every `SO(4)` matrix is of this form, but only the easy inclusion is used here). -/
def Real4 (M : Matrix (Fin 4) (Fin 4) ℝ) : Prop := RealSet (toPair M)

theorem toPair_mul (M N : Matrix (Fin 4) (Fin 4) ℝ) : toPair (M * N) = toPair M * toPair N := by
  unfold toPair; rw [Matrix.submatrix_mul_equiv]

theorem Real4.mul {M N : Matrix (Fin 4) (Fin 4) ℝ} (hM : Real4 M) (hN : Real4 N) : Real4 (M * N) := by
  unfold Real4; rw [toPair_mul]; exact RealSet.mul hM hN

theorem realSet_of_bHb {M : Matrix Pair Pair ℝ} {a b : Op1} (ha : SU2 a) (hb : SU2 b)
    (h : magicBᴴ * kron a b * magicB = cmat M) : RealSet M := by
  refine ⟨a, b, ha, hb, ?_⟩
  rw [← h]
  calc kron a b * magicB = (magicB * magicBᴴ) * kron a b * magicB := by
        rw [magicB_unitary', Matrix.one_mul]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem real4_wmat (w : SP) (hdet : (wmat w).det = 1) : Real4 (wmat w) := by
  set σP : Equiv.Perm Pair := pairEquiv.trans (w.1.trans pairEquiv.symm) with hσP
  set t : Pair → ℤ := fun p => sg (w.2 (pairEquiv p)) with ht
  have hE : toPair (wmat w) = sp σP t := by
    ext i j
    simp only [toPair, wmat, sp, Matrix.submatrix_apply, Matrix.of_apply, hσP, ht]
    by_cases h : w.1 (pairEquiv i) = pairEquiv j
    · have : (pairEquiv.trans (w.1.trans pairEquiv.symm)) i = j := by
        simp [h]
      rw [if_pos h, if_pos this]
    · have : ¬ (pairEquiv.trans (w.1.trans pairEquiv.symm)) i = j := by
        intro hh; apply h; simpa using congrArg pairEquiv hh
      rw [if_neg h, if_neg this]
  have hdetP : (sp σP t).det = 1 := by
    rw [← hE]; unfold toPair; rw [Matrix.det_submatrix_equiv_self]; exact hdet
  have htpm : ∀ k, t k = 1 ∨ t k = -1 := by
    intro k; simp only [ht]; cases w.2 (pairEquiv k) <;> simp [sg]
  obtain ⟨a, b, ha, hb, h⟩ := exists_su2_realise_det σP t htpm hdetP
  unfold Real4; rw [hE]
  exact realSet_of_bHb ha hb h

/-! ### Conjugation by the swap reflection `D = diag(1,1,-1,1)` -/

/-- The swap of the two qubits of a pair. -/
def S2 : Mat4 := Matrix.of fun i j => if i = (j.2, j.1) then 1 else 0

/-- The reflection `diag(1,1,-1,1)` (swap in magic coordinates). -/
def Dm : Matrix (Fin 4) (Fin 4) ℝ := wmat (1, fun i => decide (i = 2))

theorem S2_kron (a b : Op1) : S2 * kron a b * S2 = kron b a := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [S2, kron, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Matrix.kroneckerMap_apply] <;> ring

theorem S2_S2 : S2 * S2 = 1 := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [S2, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply]

theorem S2_magicB : S2 * magicB = magicB * cmat (toPair Dm) := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [S2, magicB, cmat, toPair, Dm, wmat, sg, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      pairEquiv_00, pairEquiv_01, pairEquiv_10, pairEquiv_11]

theorem Dm_mul_Dm : Dm * Dm = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Dm, wmat, sg, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem real4_conj_Dm {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : Real4 M) : Real4 (Dm * M * Dm) := by
  obtain ⟨a, b, ha, hb, h⟩ := hM
  refine ⟨b, a, hb, ha, ?_⟩
  rw [toPair_mul, toPair_mul, cmat_mul, cmat_mul]
  calc kron b a * magicB = (S2 * kron a b * S2) * magicB := by rw [S2_kron]
    _ = S2 * kron a b * (S2 * magicB) := by simp only [Matrix.mul_assoc]
    _ = S2 * (kron a b * magicB) * cmat (toPair Dm) := by rw [S2_magicB]; simp only [Matrix.mul_assoc]
    _ = (S2 * magicB) * cmat (toPair M) * cmat (toPair Dm) := by rw [h]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [S2_magicB]; simp only [Matrix.mul_assoc]


/-! ### Realizable matrices are `SO(4)` matrices of unit quaternion pairs -/

/-- The unit quaternion of `a ∈ SU(2)`. -/
def qOf (a : Op1) : Fin 4 → ℝ := ![(a 0 0).re, (a 0 0).im, (a 1 0).re, (a 1 0).im]

theorem su2_ofQ {a : Op1} (h : SU2 a) :
    a = ofQ (qOf a) ∧ ∑ i, qOf a i ^ 2 = 1 := by
  obtain ⟨h1, h2⟩ := su2_entries h
  have r11 : (a 1 1).re = (a 0 0).re := by rw [← h1]; simp
  have i11 : (a 1 1).im = -(a 0 0).im := by rw [← h1]; simp
  have r01 : (a 0 1).re = -(a 1 0).re := by
    have := congrArg Complex.re h2; simp at this; linarith
  have i01 : (a 0 1).im = (a 1 0).im := by
    have := congrArg Complex.im h2; simp at this; linarith
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [ofQ, qOf, r11, i11, r01, i01]
  · have h00 := congrFun (congrFun h.1 0) 0
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] at h00
    simp only [Fin.sum_univ_four, qOf]
    simp
    have e1 : (starRingEnd ℂ) (a 0 0) * a 0 0 + (starRingEnd ℂ) (a 1 0) * a 1 0 = 1 := h00
    have := congrArg Complex.re e1
    simp [Complex.mul_re] at this
    linarith

theorem Pq_eq_of_real {M : Matrix (Fin 4) (Fin 4) ℝ} {a b : Op1} (ha : SU2 a) (hb : SU2 b)
    (h : kron a b * magicB = magicB * cmat (toPair M)) :
    ∃ q p : Fin 4 → ℝ, ∑ i, q i ^ 2 = 1 ∧ ∑ i, p i ^ 2 = 1 ∧ M = Pq q p := by
  obtain ⟨ha1, ha2⟩ := su2_ofQ ha
  obtain ⟨hb1, hb2⟩ := su2_ofQ hb
  refine ⟨qOf a, qOf b, ha2, hb2, ?_⟩
  have h2 := magic_ofQ (qOf a) (qOf b)
  rw [← ha1, ← hb1, h] at h2
  have h3 : cmat (toPair M) = cmat (PqP (qOf a) (qOf b)) := by
    have := congrArg (fun X => magicBᴴ * X) h2
    simpa [← Matrix.mul_assoc, magicB_unitary] using this
  have h4 := cmat_injective h3
  ext i j
  have := congrFun (congrFun h4 (pairEquiv.symm i)) (pairEquiv.symm j)
  simpa [toPair, PqP] using this

theorem Real4.exists_Pq {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : Real4 M) :
    ∃ q p : Fin 4 → ℝ, ∑ i, q i ^ 2 = 1 ∧ ∑ i, p i ^ 2 = 1 ∧ M = Pq q p := by
  obtain ⟨a, b, ha, hb, h⟩ := hM
  exact Pq_eq_of_real ha hb h

theorem Real4.so4 {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : Real4 M) : SO4 M := by
  obtain ⟨a, b, ha, hb, h⟩ := hM
  obtain ⟨P, hP, hP1, hP2⟩ := exists_real_rep ha hb
  have h3 : cmat P = cmat (toPair M) := by
    have := congrArg (fun X => magicBᴴ * X) (hP.symm.trans h)
    simpa [← Matrix.mul_assoc, magicB_unitary] using this
  have h4 := cmat_injective h3
  have : M = reidx P := by
    ext i j; rw [h4]; simp [reidx, toPair]
  rw [this]; exact reidx_SO4 hP1 hP2


/-! ### The rank-one facets -/

/-- A `±1` vector. -/
def IsSign (t : Fin 4 → ℝ) : Prop := ∀ i, t i = 1 ∨ t i = -1

theorem IsSign.sq {t : Fin 4 → ℝ} (h : IsSign t) (i : Fin 4) : t i ^ 2 = 1 := by
  rcases h i with h | h <;> rw [h] <;> norm_num

/-- The row facet normal `e_i tᵀ`. -/
def rowN (i : Fin 4) (t : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun a b => if a = i then t b else 0

/-- The column facet normal `s e_jᵀ`. -/
def colN (j : Fin 4) (s : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun a b => if b = j then s a else 0

/-- The remaining rank-one facet normal `½ s tᵀ`. -/
noncomputable def parN (s t : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun a b => (1 / 2) * s a * t b

theorem SO4.rows {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : SO4 A) (i : Fin 4) : ∑ b, A i b ^ 2 = 1 := by
  have h : A * Aᵀ = 1 := mul_eq_one_comm.mp hA.1
  have := congrFun (congrFun h i) i
  simpa [Matrix.mul_apply, sq] using this

theorem SO4.cols {A : Matrix (Fin 4) (Fin 4) ℝ} (hA : SO4 A) (j : Fin 4) : ∑ a, A a j ^ 2 = 1 := by
  have := congrFun (congrFun hA.1 j) j
  simpa [Matrix.mul_apply, sq] using this

theorem cs_le_one (f g : Fin 4 → ℝ) (hf : ∑ i, f i ^ 2 = 1) (hg : ∑ i, g i ^ 2 = 1) :
    ∑ i, f i * g i ≤ 1 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  rw [hf, hg] at h
  nlinarith [h]

theorem tri_rowN_le {A B : Matrix (Fin 4) (Fin 4) ℝ} (hA : SO4 A) (hB : SO4 B) (i : Fin 4)
    {t : Fin 4 → ℝ} (ht : IsSign t) : tri (rowN i t) A B ≤ 1 := by
  have : tri (rowN i t) A B = ∑ b, A i b * (t b * B i b) := by
    unfold tri
    rw [Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun b _ => ?_
      simp [rowN]; ring
    · intro a _ ha; simp [rowN, ha]
    · simp
  rw [this]
  refine cs_le_one _ _ (hA.rows i) ?_
  have := hB.rows i
  rw [← this]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_pow, ht.sq, one_mul]

theorem tri_colN_le {A B : Matrix (Fin 4) (Fin 4) ℝ} (hA : SO4 A) (hB : SO4 B) (j : Fin 4)
    {s : Fin 4 → ℝ} (hs : IsSign s) : tri (colN j s) A B ≤ 1 := by
  have : tri (colN j s) A B = ∑ a, A a j * (s a * B a j) := by
    unfold tri
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single j]
    · simp [colN]; ring
    · intro b _ hb; simp [colN, hb]
    · simp
  rw [this]
  refine cs_le_one _ _ (hA.cols j) ?_
  have := hB.cols j
  rw [← this]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_pow, hs.sq, one_mul]

/-- An improper orthogonal `4×4` matrix has trace at most `2`. -/
theorem trace_le_two {R : Matrix (Fin 4) (Fin 4) ℝ} (h1 : Rᵀ * R = 1) (h2 : R.det = -1) :
    R.trace ≤ 2 := by
  have h1' : R * Rᵀ = 1 := mul_eq_one_comm.mp h1
  have hdet : (1 + R).det = 0 := by
    have e : 1 + R = R * (1 + Rᵀ) := by
      rw [Matrix.mul_add, Matrix.mul_one, h1', add_comm]
    have e3 : (1 + Rᵀ).det = (1 + R).det := by
      rw [← Matrix.det_transpose (1 + R)]; simp [Matrix.transpose_add]
    have e2 : (1 + R).det = -(1 + R).det := by
      calc (1 + R).det = (R * (1 + Rᵀ)).det := by rw [← e]
        _ = R.det * (1 + Rᵀ).det := Matrix.det_mul _ _
        _ = -(1 + R).det := by rw [h2, e3]; ring
    linarith
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hRv : ∀ i, ∑ j, R i j * v j = - v i := by
    intro i
    have := congrFun hv i
    rw [Matrix.add_mulVec, Matrix.one_mulVec] at this
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    linarith
  have hc : 0 < ∑ j, v j ^ 2 := by
    by_contra hle
    push Not at hle
    apply hv0
    funext j
    have h0 : ∑ j, v j ^ 2 = 0 := le_antisymm hle (Finset.sum_nonneg fun j _ => sq_nonneg _)
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (v j))).mp h0 j (Finset.mem_univ j)
    simpa using this
  set c := ∑ j, v j ^ 2 with hcdef
  have hrow : ∀ i, 4 * v i ^ 2 ≤ (∑ j, (R i j - if i = j then 1 else 0) ^ 2) * c := by
    intro i
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => R i j - if i = j then 1 else 0) v
    have e : ∑ j, (R i j - if i = j then 1 else 0) * v j = -2 * v i := by
      simp only [sub_mul, Finset.sum_sub_distrib, hRv i]
      simp [ite_mul]
      ring
    rw [e] at cs
    nlinarith [cs]
  have hsum : 4 * c ≤ (∑ i, ∑ j, (R i j - if i = j then 1 else 0) ^ 2) * c := by
    calc 4 * c = ∑ i, 4 * v i ^ 2 := by rw [hcdef, Finset.mul_sum]
      _ ≤ ∑ i, (∑ j, (R i j - if i = j then 1 else 0) ^ 2) * c := Finset.sum_le_sum fun i _ => hrow i
      _ = _ := by rw [Finset.sum_mul]
  have hge : 4 ≤ ∑ i, ∑ j, (R i j - if i = j then 1 else 0) ^ 2 := by
    by_contra hlt
    push Not at hlt
    nlinarith
  have hsq : ∑ i, ∑ j, R i j ^ 2 = 4 := by
    rw [Finset.sum_comm]
    have : ∀ j, ∑ i, R i j ^ 2 = 1 := by
      intro j
      have := congrFun (congrFun h1 j) j
      simpa [Matrix.mul_apply, sq] using this
    simp [this]
  have hX : ∑ i, ∑ j, (R i j - if i = j then 1 else 0) ^ 2 = 8 - 2 * R.trace := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, hsq]
    simp [Matrix.trace, Matrix.diag, ← Finset.mul_sum]
    ring
  linarith

theorem tri_parN_le {A B : Matrix (Fin 4) (Fin 4) ℝ} (hA : SO4 A) (hB : SO4 B)
    {s t : Fin 4 → ℝ} (hs : IsSign s) (ht : IsSign t) (hpar : (∏ i, s i) * (∏ i, t i) = -1) :
    tri (parN s t) A B ≤ 1 := by
  set Ds : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal s with hDs
  set Dt : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal t with hDt
  have hDsDs : Ds * Ds = 1 := by
    rw [hDs, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.one_apply, ← sq, hs.sq]
    · simp [Matrix.diagonal_apply, Matrix.one_apply, h]
  have hDtDt : Dt * Dt = 1 := by
    rw [hDt, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.one_apply, ← sq, ht.sq]
    · simp [Matrix.diagonal_apply, Matrix.one_apply, h]
  have hDsT : Dsᵀ = Ds := Matrix.diagonal_transpose _
  have hDtT : Dtᵀ = Dt := Matrix.diagonal_transpose _
  set R : Matrix (Fin 4) (Fin 4) ℝ := Dt * Aᵀ * Ds * B with hR
  have hAAt : A * Aᵀ = 1 := mul_eq_one_comm.mp hA.1
  have hRR : Rᵀ * R = 1 := by
    have : Rᵀ = Bᵀ * Ds * A * Dt := by
      rw [hR]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hDsT, hDtT, Matrix.mul_assoc]
    calc Rᵀ * R = Bᵀ * (Ds * (A * (Dt * Dt) * Aᵀ) * Ds) * B := by
          rw [this, hR]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hDtDt, Matrix.mul_one, hAAt, Matrix.mul_one, hDsDs, Matrix.mul_one, hB.1]
  have hdetR : R.det = -1 := by
    rw [hR, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, hDs, hDt, Matrix.det_diagonal,
      Matrix.det_diagonal, Matrix.det_transpose, hA.2, hB.2]
    linarith
  have htr := trace_le_two hRR hdetR
  have hR1 : Dt * Aᵀ * Ds = Matrix.of fun i j => t i * A j i * s j := by
    ext i j; simp [hDt, hDs, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have htrR : R.trace = ∑ i, ∑ j, t i * A j i * s j * B j i := by
    simp only [hR, hR1, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  have e : tri (parN s t) A B = (1 / 2) * R.trace := by
    rw [htrR, Finset.mul_sum]
    unfold tri parN
    simp only [Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]; linarith


/-! ### The exceptional facets: propagation along the `W × W` orbit -/

/-- Signed permutation matrices. -/
def SPm (M : Matrix (Fin 4) (Fin 4) ℝ) : Prop := ∃ w : SP, M = wmat w

theorem SPm.wmat (w : SP) : SPm (wmat w) := ⟨w, rfl⟩

theorem SPm.mul {M N : Matrix (Fin 4) (Fin 4) ℝ} (hM : SPm M) (hN : SPm N) : SPm (M * N) := by
  obtain ⟨w, rfl⟩ := hM
  obtain ⟨w', rfl⟩ := hN
  exact ⟨_, wmat_mul w w'⟩

theorem SPm.transpose {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : SPm M) : SPm Mᵀ := by
  obtain ⟨w, rfl⟩ := hM
  exact ⟨_, wmat_transpose w⟩

theorem SPm.real4 {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : SPm M) (hd : M.det = 1) : Real4 M := by
  obtain ⟨w, rfl⟩ := hM
  exact real4_wmat w hd

theorem SPm_Dm : SPm Dm := ⟨_, rfl⟩

theorem det_Dm : Dm.det = -1 := by
  rw [Dm, det_wmat]
  simp [Fin.prod_univ_four, sg]

theorem Dm_mul_apply (X : Matrix (Fin 4) (Fin 4) ℝ) (k l : Fin 4) :
    (Dm * X) k l = (if k = 2 then -1 else 1) * X k l := by
  fin_cases k <;> simp [Dm, wmat, sg, Matrix.mul_apply, Fin.sum_univ_four]

theorem mul_Dm_apply (X : Matrix (Fin 4) (Fin 4) ℝ) (k l : Fin 4) :
    (X * Dm) k l = X k l * (if l = 2 then -1 else 1) := by
  fin_cases l <;> simp [Dm, wmat, sg, Matrix.mul_apply, Fin.sum_univ_four]

theorem tri_Dm_left (N X Y : Matrix (Fin 4) (Fin 4) ℝ) : tri N (Dm * X) (Dm * Y) = tri N X Y := by
  unfold tri
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [Dm_mul_apply, Dm_mul_apply]
  split_ifs <;> ring

theorem tri_Dm_right (N X Y : Matrix (Fin 4) (Fin 4) ℝ) : tri N (X * Dm) (Y * Dm) = tri N X Y := by
  unfold tri
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_Dm_apply, mul_Dm_apply]
  split_ifs <;> ring

theorem real4_pair_sandwich {A B G1 G2 H1 H2 : Matrix (Fin 4) (Fin 4) ℝ} (hA : Real4 A) (hB : Real4 B)
    (hG1 : SPm G1) (hG2 : SPm G2) (hH1 : SPm H1) (hH2 : SPm H2)
    (hdG : G1.det = G2.det) (hdH : H1.det = H2.det)
    (hG1d : G1.det = 1 ∨ G1.det = -1) (hH1d : H1.det = 1 ∨ H1.det = -1) :
    ∃ A'' B'' : Matrix (Fin 4) (Fin 4) ℝ, Real4 A'' ∧ Real4 B'' ∧
      ∀ N, tri N (G1 * A * H1) (G2 * B * H2) = tri N A'' B'' := by
  have hD : SPm Dm := SPm_Dm
  rcases hG1d with hg | hg <;> rcases hH1d with hh | hh
  · refine ⟨G1 * A * H1, G2 * B * H2, ?_, ?_, fun N => rfl⟩
    · exact ((hG1.real4 hg).mul hA).mul (hH1.real4 hh)
    · exact ((hG2.real4 (hdG ▸ hg)).mul hB).mul (hH2.real4 (hdH ▸ hh))
  · -- `H` improper: reflect on the right
    refine ⟨G1 * A * (H1 * Dm), G2 * B * (H2 * Dm), ?_, ?_, fun N => ?_⟩
    · refine ((hG1.real4 hg).mul hA).mul ((hH1.mul hD).real4 ?_)
      rw [Matrix.det_mul, hh, det_Dm]; norm_num
    · refine ((hG2.real4 (hdG ▸ hg)).mul hB).mul ((hH2.mul hD).real4 ?_)
      rw [Matrix.det_mul, ← hdH, hh, det_Dm]; norm_num
    · rw [← Matrix.mul_assoc _ _ Dm, ← Matrix.mul_assoc _ _ Dm, tri_Dm_right]
  · -- `G` improper: reflect on the left
    refine ⟨Dm * G1 * A * H1, Dm * G2 * B * H2, ?_, ?_, fun N => ?_⟩
    · refine (((hD.mul hG1).real4 ?_).mul hA).mul (hH1.real4 hh)
      rw [Matrix.det_mul, hg, det_Dm]; norm_num
    · refine (((hD.mul hG2).real4 ?_).mul hB).mul (hH2.real4 (hdH ▸ hh))
      rw [Matrix.det_mul, ← hdG, hg, det_Dm]; norm_num
    · have e1 : Dm * G1 * A * H1 = Dm * (G1 * A * H1) := by simp only [Matrix.mul_assoc]
      have e2 : Dm * G2 * B * H2 = Dm * (G2 * B * H2) := by simp only [Matrix.mul_assoc]
      rw [e1, e2, tri_Dm_left]
  · -- both improper: conjugate `A` by the swap reflection
    have hh2 : H2.det = -1 := hdH ▸ hh
    have hg2 : G2.det = -1 := hdG ▸ hg
    refine ⟨(G1 * Dm) * (Dm * A * Dm) * (Dm * H1), (G2 * Dm) * (Dm * B * Dm) * (Dm * H2), ?_, ?_, fun N => ?_⟩
    · refine (((hG1.mul hD).real4 ?_).mul (real4_conj_Dm hA)).mul ((hD.mul hH1).real4 ?_)
      · rw [Matrix.det_mul, hg, det_Dm]; norm_num
      · rw [Matrix.det_mul, hh, det_Dm]; norm_num
    · refine (((hG2.mul hD).real4 ?_).mul (real4_conj_Dm hB)).mul ((hD.mul hH2).real4 ?_)
      · rw [Matrix.det_mul, hg2, det_Dm]; norm_num
      · rw [Matrix.det_mul, hh2, det_Dm]; norm_num
    · have e : ∀ (G X H : Matrix (Fin 4) (Fin 4) ℝ), (G * Dm) * (Dm * X * Dm) * (Dm * H) = G * X * H := by
        intro G X H
        calc (G * Dm) * (Dm * X * Dm) * (Dm * H) = G * (Dm * Dm) * X * (Dm * Dm) * H := by
              simp only [Matrix.mul_assoc]
          _ = G * X * H := by rw [Dm_mul_Dm]; simp
      rw [e, e]

/-- **The exceptional facets over the whole `W(D₄) × W(D₄)` orbit.** -/
theorem tri_orbit_le {g h : SP} (hg : g ∈ weylSet) (hh : h ∈ weylSet)
    {A B : Matrix (Fin 4) (Fin 4) ℝ} (hA : Real4 A) (hB : Real4 B) :
    tri (wmat g * Fmat * wmat h) A B ≤ 1 := by
  have hpg : ∏ k, sg (g.2 k) = 1 := by
    unfold weylSet at hg; rw [Finset.mem_filter] at hg; exact hg.2
  have hph : ∏ k, sg (h.2 k) = 1 := by
    unfold weylSet at hh; rw [Finset.mem_filter] at hh; exact hh.2
  have hpgR : ∏ k, (sg (g.2 k) : ℝ) = 1 := by exact_mod_cast hpg
  have hphR : ∏ k, (sg (h.2 k) : ℝ) = 1 := by exact_mod_cast hph
  have hp0 : ∀ w : SP, ∏ k : Fin 4, (sg ((w.1, fun _ : Fin 4 => false).2 k) : ℝ) = 1 := by
    intro w; simp [sg]
  have sgn : ∀ w : SP, ((Equiv.Perm.sign w.1 : ℤˣ) : ℝ) = 1 ∨ ((Equiv.Perm.sign w.1 : ℤˣ) : ℝ) = -1 := by
    intro w
    rcases Int.units_eq_one_or (Equiv.Perm.sign w.1) with h | h <;> simp [h]
  rw [tri_wmat]
  obtain ⟨A'', B'', hA'', hB'', heq⟩ := real4_pair_sandwich (A := A) (B := B)
    (G1 := (wmat g)ᵀ) (G2 := (wmat (g.1, fun _ : Fin 4 => false))ᵀ)
    (H1 := (wmat h)ᵀ) (H2 := (wmat (h.1, fun _ : Fin 4 => false))ᵀ) hA hB
    (SPm.transpose (SPm.wmat g)) (SPm.transpose (SPm.wmat _))
    (SPm.transpose (SPm.wmat h)) (SPm.transpose (SPm.wmat _))
    (by rw [Matrix.det_transpose, Matrix.det_transpose, det_wmat, det_wmat, hpgR, hp0])
    (by rw [Matrix.det_transpose, Matrix.det_transpose, det_wmat, det_wmat, hphR, hp0])
    (by rw [Matrix.det_transpose, det_wmat, hpgR, mul_one]; exact sgn g)
    (by rw [Matrix.det_transpose, det_wmat, hphR, mul_one]; exact sgn h)
  rw [heq]
  obtain ⟨q, p, hq, hp, rfl⟩ := hA''.exists_Pq
  obtain ⟨w, z, hw, hz, rfl⟩ := hB''.exists_Pq
  exact tri_Fmat_le q p w z hq hp hw hz


/-! ### The polar of `conv W(D₄)` and the Hadamard bound -/

/-- The pairing `⟨N, M⟩`. -/
def pair (N M : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := ∑ i, ∑ j, N i j * M i j

/-- The candidate extreme points of the polar of `conv W(D₄)`: the signed row and column normals, the
`½ s tᵀ` normals of opposite parity, and the `W(D₄) × W(D₄)` orbit of the exceptional normal `F`
(Brandman–Fowler–Lins–Spitkovsky–Zobin, Thm 7.1). -/
def ExtN : Set (Matrix (Fin 4) (Fin 4) ℝ) :=
  {N | (∃ i t, IsSign t ∧ N = rowN i t) ∨ (∃ j s, IsSign s ∧ N = colN j s) ∨
    (∃ s t, IsSign s ∧ IsSign t ∧ (∏ i, s i) * (∏ i, t i) = -1 ∧ N = parN s t) ∨
    (∃ g ∈ weylSet, ∃ h ∈ weylSet, N = wmat g * Fmat * wmat h)}

/-- **Facets.** Every candidate normal satisfies `⟨N, A∘B⟩ ≤ 1` for `A, B` local-rotation matrices. -/
theorem tri_le_one_of_ext {N : Matrix (Fin 4) (Fin 4) ℝ} (hN : N ∈ ExtN) {A B : Matrix (Fin 4) (Fin 4) ℝ}
    (hA : Real4 A) (hB : Real4 B) : tri N A B ≤ 1 := by
  rcases hN with ⟨i, t, ht, rfl⟩ | ⟨j, s, hs, rfl⟩ | ⟨s, t, hs, ht, hp, rfl⟩ | ⟨g, hg, h, hh, rfl⟩
  · exact tri_rowN_le hA.so4 hB.so4 i ht
  · exact tri_colN_le hA.so4 hB.so4 j hs
  · exact tri_parN_le hA.so4 hB.so4 hs ht hp
  · exact tri_orbit_le hg hh hA hB

theorem tri_comb (a b : ℝ) (N1 N2 A B : Matrix (Fin 4) (Fin 4) ℝ) :
    tri (a • N1 + b • N2) A B = a * tri N1 A B + b * tri N2 A B := by
  unfold tri
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem tri_le_one_of_hull {N : Matrix (Fin 4) (Fin 4) ℝ} (hN : N ∈ convexHull ℝ ExtN)
    {A B : Matrix (Fin 4) (Fin 4) ℝ} (hA : Real4 A) (hB : Real4 B) : tri N A B ≤ 1 := by
  have hconv : Convex ℝ {N : Matrix (Fin 4) (Fin 4) ℝ | tri N A B ≤ 1} := by
    intro N1 h1 N2 h2 a b ha hb hab
    change tri N1 A B ≤ 1 at h1
    change tri N2 A B ≤ 1 at h2
    show tri (a • N1 + b • N2) A B ≤ 1
    rw [tri_comb]
    nlinarith
  exact convexHull_min (fun N hN => tri_le_one_of_ext hN hA hB) hconv hN

/-- **The polar-extreme-point input** (Brandman–Fowler–Lins–Spitkovsky–Zobin, Thm 7.1, as recalled in
`QI-A`, §`D4 Hadamard`): every real `4×4` matrix `N` with `⟨N, w⟩ ≤ 1` for all `w ∈ W(D₄)` lies in the
convex hull of `ExtN`.  Equivalently `conv W(D₄) = {M : ⟨N,M⟩ ≤ 1 ∀ N ∈ ExtN}`.  Not proved here. -/
def PolarExtremeHyp : Prop :=
  ∀ N : Matrix (Fin 4) (Fin 4) ℝ, (∀ w ∈ weylSet, pair N (wmat w) ≤ 1) → N ∈ convexHull ℝ ExtN

theorem tri_smul (a : ℝ) (N A B : Matrix (Fin 4) (Fin 4) ℝ) : tri (a • N) A B = a * tri N A B := by
  unfold tri
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem pair_smul (a : ℝ) (N M : Matrix (Fin 4) (Fin 4) ℝ) : pair (a • N) M = a * pair N M := by
  unfold pair
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring


/-! ### The Hadamard bound and the Weyl-vertex upper bound -/

/-- **The real-matrix inequality behind the upper bound** (`QI-A`, `thm:D4hadamard`, in the form used by
`cor:D4weylvertex`): for `A, B ∈ SO(4)` and complex vectors `x, y`, the Hadamard pairing
`xᵀ (A∘B) y` is dominated in modulus by its largest value over the `192` even signed permutations. -/
def HadamardWeylBound : Prop :=
  ∀ (x y : Fin 4 → ℂ) (A B : Matrix (Fin 4) (Fin 4) ℝ), SO4 A → SO4 B →
    ∃ w ∈ weylSet, ‖hadPair x y A B‖ ≤ ‖weylPair x y w‖

/-- The same statement for the matrices `A, B` that are actually realised by local `SU(2)` rotations
(`Real4`); this is all that the physical upper bound needs, and it is implied by `HadamardWeylBound`
because `Real4 A → SO4 A`. -/
def HadamardWeylBoundRe : Prop :=
  ∀ (x y : Fin 4 → ℂ) (A B : Matrix (Fin 4) (Fin 4) ℝ), Real4 A → Real4 B →
    ∃ w ∈ weylSet, ‖hadPair x y A B‖ ≤ ‖weylPair x y w‖

theorem HadamardWeylBound.re (H : HadamardWeylBound) : HadamardWeylBoundRe :=
  fun x y A B hA hB => H x y A B hA.so4 hB.so4

theorem ip_local_real4 (d d' : Fin 4 → ℂ) {a b c e : Op1} (ha : SU2 a) (hb : SU2 b) (hc : SU2 c)
    (he : SU2 e) :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℝ, Real4 A ∧ Real4 B ∧
      ip (psiMag d) (localApply a b c e (psiMag d')) = hadPair (fun k => conj (d k)) d' A B := by
  obtain ⟨P, hP, hP1, hP2⟩ := exists_real_rep ha hb
  obtain ⟨Q, hQ, hQ1, hQ2⟩ := exists_real_rep hc he
  have hrP : toPair (reidx P) = P := by ext i j; simp [toPair, reidx]
  have hrQ : toPair (reidx Q) = Q := by ext i j; simp [toPair, reidx]
  refine ⟨reidx P, reidx Q, ⟨a, b, ha, hb, by rw [hrP]; exact hP⟩,
    ⟨c, e, hc, he, by rw [hrQ]; exact hQ⟩, ?_⟩
  unfold psiMag
  rw [ip_local _ _ a b c e P Q hP hQ]
  unfold hadPair
  rw [← Equiv.sum_comp pairEquiv.symm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, ← Equiv.sum_comp pairEquiv.symm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Equiv.apply_symm_apply, reidx, Matrix.submatrix_apply]
  ring

/-- The two-vector Weyl-vertex value `max_{w ∈ W(D₄)} |⟨d, w d'⟩|²`. -/
noncomputable def FKmag2 (d d' : Fin 4 → ℂ) : ℝ :=
  weylSet.sup' ⟨_, one_mem_weylSet⟩ fun w =>
    Complex.normSq (weylPair (fun k => conj (d k)) d' w)

theorem le_FKmag2 (d d' : Fin 4 → ℂ) {w : SP} (hw : w ∈ weylSet) :
    Complex.normSq (weylPair (fun k => conj (d k)) d' w) ≤ FKmag2 d d' :=
  Finset.le_sup' (fun w => Complex.normSq (weylPair (fun k => conj (d k)) d' w)) hw

/-- The easy direction of the two-vector Weyl-vertex formula (from `WeylRealisation.lean`). -/
theorem FKmag2_le_rotOverlap (d d' : Fin 4 → ℂ) :
    FKmag2 d d' ≤ rotOverlap (psiMag d) (psiMag d') := by
  unfold FKmag2
  refine Finset.sup'_le _ _ fun w hw => ?_
  have hw' := hw
  unfold weylSet at hw'
  rw [Finset.mem_filter] at hw'
  have hs : ∀ k, sg (w.2 k) = 1 ∨ sg (w.2 k) = -1 := by
    intro k; cases h : w.2 k <;> simp [sg]
  exact weyl_le_rotOverlap w.1 (fun k => sg (w.2 k)) hs hw'.2 d d'

theorem FKmag2_conj (d : Fin 4 → ℂ) : FKmag2 d (fun k => conj (d k)) = FKmag d := by
  unfold FKmag2 FKmag
  refine Finset.sup'_congr _ rfl fun w _ => ?_
  rw [← Complex.normSq_conj]
  congr 1
  simp only [weylPair, weylVal, map_sum, map_mul, Complex.conj_conj, map_intCast]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Upper bound, conditional on the real-matrix inequality.** -/
theorem rotOverlap_le_FKmag2 (H : HadamardWeylBoundRe) (d d' : Fin 4 → ℂ) :
    rotOverlap (psiMag d) (psiMag d') ≤ FKmag2 d d' := by
  unfold rotOverlap
  refine csSup_le ⟨_, 1, 1, 1, 1, SU2.one, SU2.one, SU2.one, SU2.one, rfl⟩ ?_
  rintro x ⟨a, b, c, e, ha, hb, hc, he, rfl⟩
  obtain ⟨A, B, hA, hB, hip⟩ := ip_local_real4 d d' ha hb hc he
  obtain ⟨w, hw, hle⟩ := H (fun k => conj (d k)) d' A B hA hB
  rw [hip]
  refine le_trans ?_ (le_FKmag2 d d' hw)
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

/-- **Weyl-vertex formula (two-vector form), conditional on `HadamardWeylBoundRe`.** -/
theorem rotOverlap_eq_FKmag2 (H : HadamardWeylBoundRe) (d d' : Fin 4 → ℂ) :
    rotOverlap (psiMag d) (psiMag d') = FKmag2 d d' :=
  le_antisymm (rotOverlap_le_FKmag2 H d d') (FKmag2_le_rotOverlap d d')

/-- **`thm:weyl` upper bound (conditional on `HadamardWeylBoundRe`)**: the rotation overlap of `ψ_d`
with its time reverse is at most `FKmag d`. -/
theorem rotOverlap_conj_le_FKmag (H : HadamardWeylBoundRe) (d : Fin 4 → ℂ) :
    rotOverlap (psiMag d) (Psi.conj (psiMag d)) ≤ FKmag d := by
  rw [conj_psiMag, ← FKmag2_conj]
  exact rotOverlap_le_FKmag2 H d _

/-- **`thm:weyl` (one-vector form), conditional on `HadamardWeylBoundRe`**:
`F_K(ψ_d) = FKmag d`. -/
theorem rotOverlap_conj_eq_FKmag (H : HadamardWeylBoundRe) (d : Fin 4 → ℂ) :
    rotOverlap (psiMag d) (Psi.conj (psiMag d)) = FKmag d := by
  rw [conj_psiMag, ← FKmag2_conj]
  exact rotOverlap_eq_FKmag2 H d _

/-! ### From the polar-extreme-point input to the Hadamard bound -/

theorem exists_phase (z : ℂ) : ∃ c : ℂ, ‖c‖ = 1 ∧ (c * z).re = ‖z‖ := by
  by_cases hz : z = 0
  · exact ⟨1, by simp, by simp [hz]⟩
  · have hn : (‖z‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hz
    refine ⟨conj z / (‖z‖ : ℂ), ?_, ?_⟩
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, norm_norm, div_self hn]
    · have : conj z / (‖z‖ : ℂ) * z = (‖z‖ : ℂ) := by
        have h2 : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hn
        rw [div_mul_eq_mul_div, mul_comm, Complex.mul_conj', div_eq_iff h2]
        push_cast; ring
      rw [this]; simp

/-- **The upper bound from the polar input.**  `PolarExtremeHyp` (a statement about the polytope
`conv W(D₄)` only) implies the Hadamard bound for the realised matrices. -/
theorem polar_to_re (hyp : PolarExtremeHyp) : HadamardWeylBoundRe := by
  intro x y A B hA hB
  obtain ⟨w0, hw0, hmax⟩ := Finset.exists_max_image weylSet (fun w => ‖weylPair x y w‖)
    ⟨_, one_mem_weylSet⟩
  refine ⟨w0, hw0, ?_⟩
  obtain ⟨c, hc, hcz⟩ := exists_phase (hadPair x y A B)
  set N : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i j => (c * x i * y j).re with hN
  have h1 : tri N A B = ‖hadPair x y A B‖ := by
    rw [← hcz]
    unfold tri hadPair
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : c * (x i * ((A i j : ℂ) * (B i j : ℂ)) * y j) = (c * x i * y j) * ((A i j * B i j : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.re_mul_ofReal]
    simp only [hN, Matrix.of_apply]
  have h2 : ∀ w : SP, pair N (wmat w) = (c * weylPair x y w).re := by
    intro w
    unfold pair weylPair
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single (w.1 i)]
    · have : c * (x i * (sg (w.2 i) : ℂ) * y (w.1 i)) = (c * x i * y (w.1 i)) * ((sg (w.2 i) : ℝ) : ℂ) := by
        push_cast; ring
      rw [this, Complex.re_mul_ofReal]
      simp [wmat, hN]
    · intro j _ hj
      simp [wmat, Ne.symm hj]
    · simp
  have h3 : ∀ w ∈ weylSet, pair N (wmat w) ≤ ‖weylPair x y w0‖ := by
    intro w hw
    rw [h2]
    calc (c * weylPair x y w).re ≤ ‖c * weylPair x y w‖ := Complex.re_le_norm _
      _ = ‖weylPair x y w‖ := by rw [norm_mul, hc, one_mul]
      _ ≤ _ := hmax w hw
  set m := ‖weylPair x y w0‖ with hm
  have hm0 : 0 ≤ m := norm_nonneg _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have ht : 0 < m + ε := by linarith
  have hpol : ∀ w ∈ weylSet, pair ((m + ε)⁻¹ • N) (wmat w) ≤ 1 := by
    intro w hw
    rw [pair_smul]
    have := h3 w hw
    calc (m + ε)⁻¹ * pair N (wmat w) ≤ (m + ε)⁻¹ * m :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.mpr ht.le)
      _ ≤ 1 := by
          rw [inv_mul_le_iff₀ ht]; linarith
  have := tri_le_one_of_hull (hyp _ hpol) hA hB
  rw [tri_smul, h1] at this
  rw [inv_mul_le_iff₀ ht] at this
  linarith

/-- **The Weyl-vertex upper bound, conditional on the polar-extreme-point input only.** -/
theorem rotOverlap_conj_le_FKmag_of_polar (hyp : PolarExtremeHyp) (d : Fin 4 → ℂ) :
    rotOverlap (psiMag d) (Psi.conj (psiMag d)) ≤ FKmag d :=
  rotOverlap_conj_le_FKmag (polar_to_re hyp) d

/-- **`thm:weyl`, one-vector form, conditional on the polar-extreme-point input only.** -/
theorem rotOverlap_conj_eq_FKmag_of_polar (hyp : PolarExtremeHyp) (d : Fin 4 → ℂ) :
    rotOverlap (psiMag d) (Psi.conj (psiMag d)) = FKmag d :=
  rotOverlap_conj_eq_FKmag (polar_to_re hyp) d

/-- **`thm:weyl`, two-vector form, conditional on the polar-extreme-point input only.** -/
theorem rotOverlap_eq_FKmag2_of_polar (hyp : PolarExtremeHyp) (d d' : Fin 4 → ℂ) :
    rotOverlap (psiMag d) (psiMag d') = FKmag2 d d' :=
  rotOverlap_eq_FKmag2 (polar_to_re hyp) d d'

end FormalResearch.FrameFree.WeylUpper
