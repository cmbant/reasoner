module

/-
NormalCompletion.lean

Normal completions of 3 × 3 matrices (Kaliuzhnyi-Verbovetskyi, Spitkovsky and Woerdeman, "Matrices with
normal defect one", Oper. Matrices 3 (2009), Thm 2.4 and Cor 2.11): if `Bᴴ B - B Bᴴ = x xᴴ - y yᴴ`
and `B` is not normal, there are `z ∈ ℂ` and `|ν| = 1` with `ν (B - z)ᴴ x = (B - z) y`, so that the
4 × 4 matrix `[[B, ν x], [yᴴ, z]]` is normal.

The proof follows the paper in an eigenbasis of `Bᴴ B - B Bᴴ = diag(d, -d, 0)`, written out for n = 3
with explicit formulas for `ν` and `z` (`ksw3_coord`).
-/
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

open Matrix ComplexConjugate

noncomputable section

namespace MathLab

/-- `p ζ̄ + q ζ = c` is solvable when `|p|² - |q|² = Δ ≠ 0`. -/
theorem exists_solve_conj (p q c : ℂ) (Δ : ℝ) (hΔ : p * conj p - q * conj q = Δ) (hΔ0 : Δ ≠ 0) :
    ∃ ζ : ℂ, p * conj ζ + q * ζ = c := by
  have hΔ0' : (Δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hΔ0
  refine ⟨(p * conj c - conj q * c) / Δ, ?_⟩
  simp only [map_div₀, map_sub, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  field_simp
  linear_combination c * hΔ

theorem eq_zero_of_mul_conj_eq_zero {w : ℂ} (h : w * conj w = 0) : w = 0 := by
  rcases mul_eq_zero.1 h with h | h
  · exact h
  · exact (map_eq_zero (starRingEnd ℂ)).1 h

/-- The coordinate form: in an eigenbasis of the self-commutator. -/
theorem ksw3_coord (A : Matrix (Fin 3) (Fin 3) ℂ) (x y : Fin 3 → ℂ) (d : ℝ) (hd : 0 < d)
    (hA : Aᴴ * A - A * Aᴴ = diagonal ![(d : ℂ), -(d : ℂ), 0])
    (hxy : vecMulVec x (star x) - vecMulVec y (star y) = diagonal ![(d : ℂ), -(d : ℂ), 0]) :
    ∃ z ν : ℂ, ‖ν‖ = 1 ∧
      ν • ((Aᴴ - star z • (1 : Matrix (Fin 3) (Fin 3) ℂ)) *ᵥ x) = (A - z • 1) *ᵥ y := by
  have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.ne'
  -- (a) trace (A [Aᴴ, A]) = 0 gives a₀₀ = a₁₁
  have htr1 : trace (A * (Aᴴ * A - A * Aᴴ)) = 0 := by
    have h := trace_mul_comm (A * Aᴴ) A
    rw [mul_assoc] at h
    rw [mul_sub, trace_sub, h, sub_self]
  rw [hA] at htr1
  simp only [trace, Fin.sum_univ_three, mul_diagonal, diag_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, mul_zero,
    add_zero] at htr1
  have ha : A 1 1 = A 0 0 := by
    have : (A 0 0 - A 1 1) * d = 0 := by linear_combination htr1
    have := (mul_eq_zero.1 this).resolve_right hd0
    linear_combination -this
  -- (b) trace ([Aᴴ, A] (A Aᴴ + Aᴴ A)) = 0
  have htr2 : trace ((Aᴴ * A - A * Aᴴ) * (A * Aᴴ + Aᴴ * A)) = 0 := by
    have c1 : trace (Aᴴ * A * (A * Aᴴ)) = trace (A * Aᴴ * (Aᴴ * A)) := trace_mul_comm _ _
    have c2 : trace (Aᴴ * A * (Aᴴ * A)) = trace (A * Aᴴ * (A * Aᴴ)) := by
      have := trace_mul_comm Aᴴ (A * (Aᴴ * A))
      simpa only [mul_assoc] using this
    rw [sub_mul, mul_add, mul_add, trace_sub, trace_add, trace_add, c1, c2]
    ring
  rw [hA] at htr2
  -- entries
  have hE : ∀ i j, (Aᴴ * A - A * Aᴴ) i j = diagonal ![(d : ℂ), -(d : ℂ), 0] i j := fun i j => by
    rw [hA]
  have hX : ∀ i j, (vecMulVec x (star x) - vecMulVec y (star y)) i j =
      diagonal ![(d : ℂ), -(d : ℂ), 0] i j := fun i j => by rw [hxy]
  have e22 := hE 2 2
  have e01 := hE 0 1
  have X00 := hX 0 0
  have X11 := hX 1 1
  have X22 := hX 2 2
  have X01 := hX 0 1
  have X02 := hX 0 2
  simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_three,
    diagonal_apply, vecMulVec_apply, Pi.star_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, ite_true, ite_false,
    Fin.reduceEq, RCLike.star_def] at e22 e01 X00 X11 X22 X01 X02
  simp only [trace, diag_apply, Matrix.add_apply, Matrix.mul_apply, conjTranspose_apply,
    Fin.sum_univ_three, diagonal_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, ite_true, ite_false,
    Fin.reduceEq, RCLike.star_def, zero_mul, add_zero, zero_add] at htr2
  rw [ha] at e01 htr2
  -- the relations among the off-diagonal entries (Lemma 2.7 of the paper)
  have t2 : A 0 2 * conj (A 0 2) + A 2 0 * conj (A 2 0) - A 1 2 * conj (A 1 2)
      - A 2 1 * conj (A 2 1) = 0 := by
    have : (d : ℂ) * (A 0 2 * conj (A 0 2) + A 2 0 * conj (A 2 0) - A 1 2 * conj (A 1 2)
      - A 2 1 * conj (A 2 1)) = 0 := by linear_combination htr2
    exact (mul_eq_zero.1 this).resolve_left hd0
  have hn1 : A 0 2 * conj (A 0 2) = A 2 1 * conj (A 2 1) := by linear_combination (t2 + e22) / 2
  have hn2 : A 2 0 * conj (A 2 0) = A 1 2 * conj (A 1 2) := by linear_combination (t2 - e22) / 2
  have h3 : conj (A 2 0) * A 2 1 = A 0 2 * conj (A 1 2) := by linear_combination e01
  have h3c : A 2 0 * conj (A 2 1) = conj (A 0 2) * A 1 2 := by
    have := congrArg conj h3
    simpa only [map_mul, Complex.conj_conj] using this
  -- the vectors: x₂ = y₂ = 0, |x₀|² - |x₁|² = d, |y₀| = |x₁|, |y₁| = |x₀|
  have X02c : conj (x 0) * x 2 - conj (y 0) * y 2 = 0 := by
    have := congrArg conj X02
    simpa only [map_sub, map_mul, Complex.conj_conj, map_zero] using this
  have X01c : conj (x 0) * x 1 - conj (y 0) * y 1 = 0 := by
    have := congrArg conj X01
    simpa only [map_sub, map_mul, Complex.conj_conj, map_zero] using this
  have hx2 : x 2 = 0 := by
    have : (d : ℂ) * (x 2 * conj (x 2)) = 0 := by
      linear_combination (conj (x 0) * x 2) * X02 + (y 0 * conj (y 2)) * X02c
        - (y 0 * conj (y 0)) * X22 - (x 2 * conj (x 2)) * X00
    exact eq_zero_of_mul_conj_eq_zero ((mul_eq_zero.1 this).resolve_left hd0)
  have hy2 : y 2 = 0 := by
    rw [hx2] at X22
    exact eq_zero_of_mul_conj_eq_zero (by linear_combination -X22)
  have hm0 : y 0 * conj (y 0) = x 0 * conj (x 0) - d := by linear_combination -X00
  have hm1 : y 1 * conj (y 1) = x 1 * conj (x 1) + d := by linear_combination -X11
  have hprod : x 0 * conj (x 0) * (x 1 * conj (x 1)) = y 0 * conj (y 0) * (y 1 * conj (y 1)) := by
    linear_combination (conj (x 0) * x 1) * X01 + (y 0 * conj (y 1)) * X01c
  rw [hm0, hm1] at hprod
  have hn01 : x 0 * conj (x 0) - x 1 * conj (x 1) = d := by
    have : (d : ℂ) * (x 0 * conj (x 0) - x 1 * conj (x 1) - d) = 0 := by linear_combination -hprod
    linear_combination (mul_eq_zero.1 this).resolve_left hd0
  have hy0n : y 0 * conj (y 0) = x 1 * conj (x 1) := by linear_combination hm0 + hn01
  have hy1n : y 1 * conj (y 1) = x 0 * conj (x 0) := by linear_combination hm1 - hn01
  have hx0 : x 0 ≠ 0 := by
    intro h0
    rw [h0] at hn01
    have h1 : ((Complex.normSq (x 1) : ℝ) : ℂ) = ((-d : ℝ) : ℂ) := by
      rw [← Complex.mul_conj]
      push_cast
      linear_combination -hn01
    have := Complex.ofReal_injective h1
    linarith [Complex.normSq_nonneg (x 1)]
  have hx0c : conj (x 0) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 hx0
  -- the phase ω with y = ω (x̄₁, x̄₀, 0)
  set ω : ℂ := y 1 / conj (x 0) with hω
  have hy1 : y 1 = ω * conj (x 0) := by rw [hω, div_mul_cancel₀ _ hx0c]
  have hωω : ω * conj ω = 1 := by
    rw [hω, map_div₀, Complex.conj_conj, div_mul_div_comm, hy1n, mul_comm (conj (x 0)) (x 0)]
    exact div_self (mul_ne_zero hx0 hx0c)
  have hy0 : y 0 = ω * conj (x 1) := by
    have h1 : x 0 * (conj (x 1) - y 0 * conj ω) = 0 := by
      have : conj (y 1) = conj ω * x 0 := by
        rw [hy1, map_mul, Complex.conj_conj]
      rw [this] at X01
      linear_combination X01
    have h2 := (mul_eq_zero.1 h1).resolve_left hx0
    linear_combination -(ω * h2) - y 0 * hωω
  -- the scalars of the third component
  set R : ℂ := conj (A 0 2) * x 0 + conj (A 1 2) * x 1 with hR
  set S : ℂ := A 2 0 * y 0 + A 2 1 * y 1 with hS
  have hRS : R * conj R = S * conj S := by
    rw [hR, hS, hy0, hy1]
    simp only [map_add, map_mul, Complex.conj_conj]
    linear_combination
      (-(A 2 0 * conj (A 2 0) * (conj (x 1) * x 1) + A 2 0 * conj (A 2 1) * (conj (x 1) * x 0)
        + A 2 1 * conj (A 2 0) * (conj (x 0) * x 1) + A 2 1 * conj (A 2 1) * (conj (x 0) * x 0)))
        * hωω + (x 0 * conj (x 0)) * hn1 - (x 0 * conj (x 1)) * h3c - (x 1 * conj (x 0)) * h3
        - (x 1 * conj (x 1)) * hn2
  -- choose ν with ν R = S and |ν| = 1
  obtain ⟨ν, hν, hνR⟩ : ∃ ν : ℂ, ν * conj ν = 1 ∧ ν * R = S := by
    by_cases hR0 : R = 0
    · refine ⟨1, by simp, ?_⟩
      rw [hR0, map_zero, mul_zero] at hRS
      rw [hR0, mul_zero, eq_zero_of_mul_conj_eq_zero hRS.symm]
    · have hRc : conj R ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 hR0
      refine ⟨S / R, ?_, div_mul_cancel₀ _ hR0⟩
      rw [map_div₀, div_mul_div_comm, ← hRS]
      exact div_self (mul_ne_zero hR0 hRc)
  -- λ = ν ω̄ and the real-linear equation for ζ = a₀₀ - z
  set lam : ℂ := ν * conj ω with hlam
  have hll : lam * conj lam = 1 := by
    rw [hlam, map_mul, Complex.conj_conj]
    linear_combination (conj ω * ω) * hν + hωω
  have hνlam : ν = lam * ω := by
    rw [hlam]
    linear_combination -(ν * hωω)
  obtain ⟨ζ, hζ⟩ := exists_solve_conj (lam * x 0) (-conj (x 1))
    (A 0 1 * conj (x 0) - lam * conj (A 1 0) * x 1) d
    (by
      simp only [map_mul, map_neg, Complex.conj_conj]
      linear_combination (x 0 * conj (x 0)) * hll + hn01)
    hd.ne'
  have hζc : conj lam * conj (x 0) * ζ + (-x 1) * conj ζ =
      conj (A 0 1) * x 0 - conj lam * A 1 0 * conj (x 1) := by
    have := congrArg conj hζ
    simpa only [map_add, map_sub, map_mul, map_neg, Complex.conj_conj] using this
  refine ⟨A 0 0 - ζ, ν, ?_, ?_⟩
  · have h1 : ((‖ν‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, hν]
      simp
    have h2 : ‖ν‖ ^ 2 = 1 := Complex.ofReal_injective h1
    nlinarith [norm_nonneg ν]
  · ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, mulVec, dotProduct, Fin.sum_univ_three,
        Matrix.sub_apply, conjTranspose_apply, Matrix.smul_apply, one_apply, ite_true, ite_false,
        Fin.reduceEq, smul_eq_mul, mul_one, mul_zero, sub_zero, hx2, hy2, RCLike.star_def, map_sub,
        add_zero]
      rw [hνlam, hy0, hy1]
      linear_combination ω * hζ
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, mulVec, dotProduct, Fin.sum_univ_three,
        Matrix.sub_apply, conjTranspose_apply, Matrix.smul_apply, one_apply, ite_true, ite_false,
        Fin.reduceEq, smul_eq_mul, mul_one, mul_zero, sub_zero, hx2, hy2, RCLike.star_def, map_sub,
        add_zero]
      rw [hνlam, hy0, hy1, ha]
      linear_combination ω * (-lam * hζc + (conj (x 0) * ζ + A 1 0 * conj (x 1)) * hll)
    · simp only [Fin.reduceFinMk, Fin.isValue, Pi.smul_apply, mulVec, dotProduct, Fin.sum_univ_three,
        Matrix.sub_apply, conjTranspose_apply, Matrix.smul_apply, one_apply, ite_true, ite_false,
        Fin.reduceEq, smul_eq_mul, mul_one, mul_zero, sub_zero, hx2, hy2, RCLike.star_def,
        add_zero]
      linear_combination hνR

/-- A traceless, singular, nonzero Hermitian 3 × 3 matrix is unitarily `diag(d, -d, 0)` with `d > 0`. -/
theorem exists_unitary_diag3 (D : Matrix (Fin 3) (Fin 3) ℂ) (hH : D.IsHermitian) (htr : D.trace = 0)
    (hdet : D.det = 0) (hD0 : D ≠ 0) :
    ∃ (U : Matrix (Fin 3) (Fin 3) ℂ) (d : ℝ), 0 < d ∧ Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      Uᴴ * D * U = diagonal ![(d : ℂ), -(d : ℂ), 0] := by
  set μ := hH.eigenvalues with hμ
  set W : Matrix (Fin 3) (Fin 3) ℂ := (hH.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℂ) with hW
  have hWW : Wᴴ * W = 1 := Matrix.mem_unitaryGroup_iff'.1 hH.eigenvectorUnitary.2
  have hWW' : W * Wᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hH.eigenvectorUnitary.2
  have hdiag : Wᴴ * D * W = diagonal (fun i => (μ i : ℂ)) := by
    have := hH.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    simpa [hW, hμ, Function.comp_def, Matrix.star_eq_conjTranspose] using this
  have hsum : ∑ i, μ i = 0 := by
    have := hH.trace_eq_sum_eigenvalues
    rw [htr] at this
    have h2 : ((∑ i, μ i : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum, Complex.ofReal_zero, hμ]
      exact this.symm
    exact Complex.ofReal_injective h2
  -- a zero eigenvalue
  obtain ⟨r, hr⟩ : ∃ r, μ r = 0 := by
    have := hH.det_eq_prod_eigenvalues
    rw [hdet] at this
    have h0 : ∏ i, (μ i : ℂ) = 0 := this.symm
    obtain ⟨r, -, hr⟩ := Finset.prod_eq_zero_iff.1 h0
    exact ⟨r, by exact_mod_cast hr⟩
  -- D ≠ 0 gives a positive and a negative eigenvalue
  have hne : ∃ i, μ i ≠ 0 := by
    by_contra h
    push Not at h
    apply hD0
    have : diagonal (fun i => (μ i : ℂ)) = 0 := by
      ext i j
      simp [diagonal_apply, h]
    calc D = W * (Wᴴ * D * W) * Wᴴ := by
            simp only [← mul_assoc, hWW', one_mul]; rw [mul_assoc, hWW', mul_one]
      _ = 0 := by rw [hdiag, this, mul_zero, zero_mul]
  obtain ⟨p, hp⟩ : ∃ p, 0 < μ p := by
    by_contra h
    push Not at h
    obtain ⟨i, hi⟩ := hne
    have := (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => h j)).1 hsum i (Finset.mem_univ _)
    exact hi this
  obtain ⟨q, hq⟩ : ∃ q, μ q < 0 := by
    by_contra h
    push Not at h
    obtain ⟨i, hi⟩ := hne
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h j)).1 hsum i (Finset.mem_univ _)
    exact hi this
  have hpq : p ≠ q := fun h => by rw [h] at hp; linarith
  have hpr : p ≠ r := fun h => by rw [h] at hp; linarith
  have hqr : q ≠ r := fun h => by rw [h] at hq; linarith
  have huniv : (Finset.univ : Finset (Fin 3)) = {p, q, r} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simp [hpq, hpr]),
      Finset.card_insert_of_notMem (by simp [hqr]), Finset.card_singleton]
    rfl
  have hqp : μ q = -μ p := by
    rw [huniv, Finset.sum_insert (by simp [hpq, hpr]), Finset.sum_insert (by simp [hqr]),
      Finset.sum_singleton, hr] at hsum
    linarith
  -- reorder the eigenbasis as (p, q, r)
  have hqp' : q ≠ p := hpq.symm
  have hrp : r ≠ p := hpr.symm
  have hrq : r ≠ q := hqr.symm
  have hinj : Function.Injective ![p, q, r] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  set τ : Fin 3 ≃ Fin 3 := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj) with hτ
  have hτv : ∀ i, τ i = ![p, q, r] i := fun i => rfl
  have h2 : Wᴴ.submatrix τ id * W.submatrix id τ = (Wᴴ * W).submatrix τ τ := by
    ext i j
    simp [Matrix.mul_apply]
  have h3 : Wᴴ.submatrix τ id * D * W.submatrix id τ = (Wᴴ * D * W).submatrix τ τ := by
    ext i j
    simp [Matrix.mul_apply]
  refine ⟨W.submatrix id τ, μ p, hp, ?_, ?_, ?_⟩
  · rw [conjTranspose_submatrix, h2, hWW, submatrix_one_equiv]
  · rw [mul_eq_one_comm, conjTranspose_submatrix, h2, hWW, submatrix_one_equiv]
  · rw [conjTranspose_submatrix, h3, hdiag, submatrix_diagonal_equiv]
    congr 1
    funext i
    fin_cases i <;> simp [hτv, hqp, hr]

/-- `(M v)(M v)ᴴ = M (v vᴴ) Mᴴ`. -/
theorem vecMulVec_mulVec_star {m n : Type*} [Fintype n] (M : Matrix m n ℂ) (v : n → ℂ) :
    vecMulVec (M *ᵥ v) (star (M *ᵥ v)) = M * vecMulVec v (star v) * Mᴴ := by
  ext i j
  simp only [vecMulVec_apply, mulVec, dotProduct, Pi.star_apply, Matrix.mul_apply,
    conjTranspose_apply, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **Normal completion of a 3 × 3 matrix** (KSW 2009, Thm 2.4 and Cor 2.11): if
`Bᴴ B - B Bᴴ = x xᴴ - y yᴴ ≠ 0`, there are `z` and a unimodular `ν` with `ν (B - z)ᴴ x = (B - z) y`. -/
theorem normal_completion_three (B : Matrix (Fin 3) (Fin 3) ℂ) (x y : Fin 3 → ℂ)
    (hD : Bᴴ * B - B * Bᴴ = vecMulVec x (star x) - vecMulVec y (star y))
    (hD0 : Bᴴ * B - B * Bᴴ ≠ 0) :
    ∃ z ν : ℂ, ‖ν‖ = 1 ∧
      ν • ((Bᴴ - star z • (1 : Matrix (Fin 3) (Fin 3) ℂ)) *ᵥ x) = (B - z • 1) *ᵥ y := by
  have hH : (Bᴴ * B - B * Bᴴ).IsHermitian := by
    rw [IsHermitian, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose]
  have htr : (Bᴴ * B - B * Bᴴ).trace = 0 := by rw [trace_sub, trace_mul_comm, sub_self]
  have hdet : (Bᴴ * B - B * Bᴴ).det = 0 := by
    rw [hD, det_fin_three]
    simp only [Matrix.sub_apply, vecMulVec_apply, Pi.star_apply]
    ring
  obtain ⟨U, d, hd, hUU, hUU', hdiag⟩ := exists_unitary_diag3 _ hH htr hdet hD0
  have hAH : (Uᴴ * B * U)ᴴ = Uᴴ * Bᴴ * U := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, mul_assoc]
  have hcomm : (Uᴴ * B * U)ᴴ * (Uᴴ * B * U) - (Uᴴ * B * U) * (Uᴴ * B * U)ᴴ =
      diagonal ![(d : ℂ), -(d : ℂ), 0] := by
    rw [← hdiag, hAH]
    calc Uᴴ * Bᴴ * U * (Uᴴ * B * U) - Uᴴ * B * U * (Uᴴ * Bᴴ * U)
        = Uᴴ * Bᴴ * (U * Uᴴ) * B * U - Uᴴ * B * (U * Uᴴ) * Bᴴ * U := by
          simp only [mul_assoc]
      _ = Uᴴ * (Bᴴ * B - B * Bᴴ) * U := by
          rw [hUU', mul_one, mul_one]
          simp only [mul_sub, sub_mul, mul_assoc]
  have hxy : vecMulVec (Uᴴ *ᵥ x) (star (Uᴴ *ᵥ x)) - vecMulVec (Uᴴ *ᵥ y) (star (Uᴴ *ᵥ y)) =
      diagonal ![(d : ℂ), -(d : ℂ), 0] := by
    rw [vecMulVec_mulVec_star, vecMulVec_mulVec_star, conjTranspose_conjTranspose, ← sub_mul,
      ← mul_sub, ← hD, hdiag]
  obtain ⟨z, ν, hν, h⟩ := ksw3_coord _ _ _ d hd hcomm hxy
  refine ⟨z, ν, hν, ?_⟩
  have key := congrArg (U *ᵥ ·) h
  simp only [mulVec_smul, mulVec_mulVec, ← mul_assoc] at key
  have e1 : U * ((Uᴴ * B * U)ᴴ - star z • (1 : Matrix (Fin 3) (Fin 3) ℂ)) * Uᴴ =
      Bᴴ - star z • 1 := by
    rw [hAH]
    calc U * (Uᴴ * Bᴴ * U - star z • (1 : Matrix (Fin 3) (Fin 3) ℂ)) * Uᴴ
        = (U * Uᴴ) * Bᴴ * (U * Uᴴ) - star z • (U * Uᴴ) := by
          simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, mul_assoc]
      _ = Bᴴ - star z • 1 := by rw [hUU', one_mul, mul_one]
  have e2 : U * (Uᴴ * B * U - z • (1 : Matrix (Fin 3) (Fin 3) ℂ)) * Uᴴ = B - z • 1 := by
    calc U * (Uᴴ * B * U - z • (1 : Matrix (Fin 3) (Fin 3) ℂ)) * Uᴴ
        = (U * Uᴴ) * B * (U * Uᴴ) - z • (U * Uᴴ) := by
          simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, mul_assoc]
      _ = B - z • 1 := by rw [hUU', one_mul, mul_one]
  rwa [e1, e2] at key

section Bordered

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The bordered matrix `[[B, x], [yᴴ, z]]`. -/
def bordered (B : Matrix n n ℂ) (x y : n → ℂ) (z : ℂ) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ :=
  fromBlocks B (replicateCol Unit x) (replicateRow Unit (star y)) (of fun _ _ => z)

/-- **The bordered matrix is normal** (KSW 2009, Lemma 2.5) when `Bᴴ B - B Bᴴ = x xᴴ - y yᴴ` and
`(B - z)ᴴ x = (B - z) y`. -/
theorem bordered_normal (B : Matrix n n ℂ) (x y : n → ℂ) (z : ℂ)
    (h1 : Bᴴ * B - B * Bᴴ = vecMulVec x (star x) - vecMulVec y (star y))
    (h2 : (Bᴴ - star z • (1 : Matrix n n ℂ)) *ᵥ x = (B - z • 1) *ᵥ y) :
    (bordered B x y z)ᴴ * bordered B x y z = bordered B x y z * (bordered B x y z)ᴴ := by
  have htr : ∑ k, star (x k) * x k = ∑ k, star (y k) * y k := by
    have := congrArg trace h1
    rw [trace_sub, trace_mul_comm, sub_self, trace_sub] at this
    simp only [trace, diag_apply, vecMulVec_apply, Pi.star_apply] at this
    have h := sub_eq_zero.1 this.symm
    simpa only [mul_comm] using h
  ext a b
  rcases a with i | ⟨⟩ <;> rcases b with j | ⟨⟩
  · have := congrFun (congrFun h1 i) j
    simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, vecMulVec_apply,
      Pi.star_apply] at this
    simp only [bordered, Matrix.mul_apply, Fintype.sum_sum_type, conjTranspose_apply,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, 
      replicateCol_apply, replicateRow_apply, Pi.star_apply, star_star, Finset.univ_unique,
      Finset.sum_singleton]
    linear_combination this
  · have := congrFun h2 i
    simp only [mulVec, dotProduct, Matrix.sub_apply, conjTranspose_apply, Matrix.smul_apply,
      one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, sub_mul, Finset.sum_sub_distrib,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at this
    simp only [bordered, Matrix.mul_apply, Fintype.sum_sum_type, conjTranspose_apply,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      replicateCol_apply, replicateRow_apply, Pi.star_apply, star_star, Finset.univ_unique,
      Finset.sum_singleton, of_apply]
    linear_combination this
  · have := congrArg star (congrFun h2 j)
    simp only [mulVec, dotProduct, Matrix.sub_apply, conjTranspose_apply, Matrix.smul_apply,
      one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, sub_mul, Finset.sum_sub_distrib,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      star_sub, star_sum, star_mul', star_star] at this
    simp only [bordered, Matrix.mul_apply, Fintype.sum_sum_type, conjTranspose_apply,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      replicateCol_apply, replicateRow_apply, Pi.star_apply, Finset.univ_unique,
      Finset.sum_singleton, of_apply]
    have e1 : ∑ a, star (x a) * B a j = ∑ a, B a j * star (x a) :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have e2 : ∑ a, star (y a) * star (B j a) = ∑ a, star (B j a) * star (y a) :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [e1, e2]
    linear_combination this
  · simp only [bordered, Matrix.mul_apply, Fintype.sum_sum_type, conjTranspose_apply,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      replicateCol_apply, replicateRow_apply, Pi.star_apply, star_star, Finset.univ_unique,
      Finset.sum_singleton, of_apply]
    linear_combination htr

omit [Fintype n] [DecidableEq n] in
theorem bordered_toBlocks₁₁ (B : Matrix n n ℂ) (x y : n → ℂ) (z : ℂ) :
    (bordered B x y z).toBlocks₁₁ = B := by
  simp [bordered]

omit [DecidableEq n] in
theorem bordered_mul_conjTranspose_toBlocks₁₁ (B : Matrix n n ℂ) (x y : n → ℂ) (z : ℂ) :
    (bordered B x y z * (bordered B x y z)ᴴ).toBlocks₁₁ = B * Bᴴ + vecMulVec x (star x) := by
  ext i j
  simp only [bordered, toBlocks₁₁, of_apply, Matrix.mul_apply, Fintype.sum_sum_type,
    conjTranspose_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, replicateCol_apply,
    Finset.univ_unique, Finset.sum_singleton, Matrix.add_apply, vecMulVec_apply, Pi.star_apply]

end Bordered

/-- **A normal dilation with the right corner**: for `Bᴴ B - B Bᴴ = x xᴴ - y yᴴ` there is a normal
`N` on `ℂ³ ⊕ ℂ` with corner `B` and `B Bᴴ + x xᴴ - (N Nᴴ)₁₁` a rank-one positive matrix `w wᴴ`. -/
theorem exists_normal_dilation (B : Matrix (Fin 3) (Fin 3) ℂ) (x y : Fin 3 → ℂ)
    (hD : Bᴴ * B - B * Bᴴ = vecMulVec x (star x) - vecMulVec y (star y)) :
    ∃ (N : Matrix (Fin 3 ⊕ Unit) (Fin 3 ⊕ Unit) ℂ) (w : Fin 3 → ℂ), Nᴴ * N = N * Nᴴ ∧
      N.toBlocks₁₁ = B ∧ B * Bᴴ + vecMulVec x (star x) - (N * Nᴴ).toBlocks₁₁ = vecMulVec w (star w) := by
  by_cases hD0 : Bᴴ * B - B * Bᴴ = 0
  · refine ⟨fromBlocks B 0 0 0, x, ?_, by simp, ?_⟩
    · rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
      simp only [conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero]
      rw [sub_eq_zero.1 hD0]
    · rw [fromBlocks_conjTranspose, fromBlocks_multiply]
      simp
  · obtain ⟨z, ν, hν, h⟩ := normal_completion_three B x y hD hD0
    have hνν : ν * star ν = 1 := by
      rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hν]
      simp
    have hvx : vecMulVec (ν • x) (star (ν • x)) = vecMulVec x (star x) := by
      ext i j
      simp only [vecMulVec_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_mul']
      linear_combination (x i * star (x j)) * hνν
    refine ⟨bordered B (ν • x) y z, 0, bordered_normal B (ν • x) y z ?_ ?_,
      bordered_toBlocks₁₁ B _ y z, ?_⟩
    · rw [hvx, hD]
    · rw [mulVec_smul, h]
    · rw [bordered_mul_conjTranspose_toBlocks₁₁, hvx]
      ext i j
      simp

end MathLab

end

end -- public section

#print axioms MathLab.ksw3_coord
#print axioms MathLab.normal_completion_three
#print axioms MathLab.exists_normal_dilation
