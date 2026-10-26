import FormalResearch.FourQubitEntropy.SevenQubitIcoCert

/-!
# Spectra of the reduced matrices of the seven-qubit icosahedral family

For every three-qubit cut (35 of them) this proves the spectrum of the reduced matrix
`ρ_S` of `icosahedralState alpha beta`, derived from the state tensor (`thm:ico`, item 4 of
`icosahedral_state.tex`):

* cuts avoiding the special site `0`: eigenvalues `4α²` (six times) and `3α²+β²` (twice);
* cuts containing it: `8α²` (once), `4α²` (five times) and `α²+β²` (twice).

The spectra are stated as `∑ g(eigenvalue)` for every function `g`, i.e. as multisets. The proof
writes `ρ_S` as a polynomial in an integer matrix `T` whose cube relation `T(T-s)(T-2s) = 0`
(`s = 1` resp. `4`) and trace data are checked in the kernel for every cut, then derives the
spectrum from the spectral theorem of `T`. Nothing here uses the numerical values at the
icosahedral parameter.
-/

open Matrix Polynomial Unitary

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

/-! ### Spectrum of a polynomial in a matrix with three eigenvalues `0, s, 2s` -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_eigenvalues_poly (T ρ : Matrix ι ι ℂ) (hT : T.IsHermitian) (hρ : ρ.IsHermitian)
    (c0 c1 c2 : ℝ) (hρeq : ρ = (c0 : ℂ) • (1 : Matrix ι ι ℂ) + (c1 : ℂ) • T + (c2 : ℂ) • (T * T))
    (g : ℝ → ℝ) :
    ∑ i, g (hρ.eigenvalues i) = ∑ i, g (c0 + c1 * hT.eigenvalues i + c2 * hT.eigenvalues i ^ 2) := by
  set Φ := conjStarAlgAut ℂ _ hT.eigenvectorUnitary with hΦ
  set D : Matrix ι ι ℂ := diagonal (RCLike.ofReal ∘ hT.eigenvalues) with hD
  have hTD : T = Φ D := hT.spectral_theorem
  set d : ι → ℝ := fun i => c0 + c1 * hT.eigenvalues i + c2 * hT.eigenvalues i ^ 2 with hd
  have hρD : ρ = Φ (diagonal (fun i => (d i : ℂ))) := by
    have : (diagonal (fun i => (d i : ℂ)) : Matrix ι ι ℂ) =
        (c0 : ℂ) • (1 : Matrix ι ι ℂ) + (c1 : ℂ) • D + (c2 : ℂ) • (D * D) := by
      ext i j
      by_cases h : i = j
      · subst h; simp [hD, hd, diagonal_apply_eq, pow_two]
      · simp [hD, hd, h, diagonal_apply_ne, Matrix.one_apply_ne]
    rw [this, map_add, map_add, map_smul, map_smul, map_smul, map_one, map_mul, ← hTD]
    exact hρeq
  have hch : ρ.charpoly = ∏ i, (X - C ((d i : ℝ) : ℂ)) := by
    rw [hρD, conjStarAlgAut_apply, charpoly_mul_comm, ← mul_assoc]
    simp [charpoly_diagonal]
  have hroots := hρ.roots_charpoly_eq_eigenvalues
  have hroots' : ρ.charpoly.roots = Multiset.map (fun i => ((d i : ℝ) : ℂ)) Finset.univ.val := by
    rw [hch, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hm := hroots.symm.trans hroots'
  have h3 := congrArg (fun m : Multiset ℂ => (m.map (fun z : ℂ => g z.re)).sum) hm
  simp only [Multiset.map_map] at h3
  have e1 : ((fun z : ℂ => g z.re) ∘ (RCLike.ofReal ∘ hρ.eigenvalues)) =
      fun i => g (hρ.eigenvalues i) := by
    funext i; simp
  have e2 : ((fun z : ℂ => g z.re) ∘ (fun i => ((d i : ℝ) : ℂ))) = fun i => g (d i) := by
    funext i; simp
  rw [e1, e2] at h3
  exact h3


theorem three_valued_sum {ι : Type*} [Fintype ι] (t : ι → ℝ) (s : ℝ) (hs : s ≠ 0)
    (ht : ∀ i, t i = 0 ∨ t i = s ∨ t i = 2 * s) (q : ℝ → ℝ) (n1 n2 : ℝ)
    (h1 : ∑ i, t i = s * (n1 + 2 * n2)) (h2 : ∑ i, t i ^ 2 = s ^ 2 * (n1 + 4 * n2)) :
    ∑ i, q (t i) = Fintype.card ι * q 0 + n1 * (q s - q 0) + n2 * (q (2 * s) - q 0) := by
  have hpt : ∀ i, q (t i) = q 0 + (q s - q 0) * (t i * (2 * s - t i) / s ^ 2) +
      (q (2 * s) - q 0) * (t i * (t i - s) / (2 * s ^ 2)) := by
    intro i
    rcases ht i with h | h | h <;> rw [h] <;> field_simp <;> ring
  have e1 : ∑ i, t i * (2 * s - t i) / s ^ 2 = n1 := by
    have : ∑ i, t i * (2 * s - t i) = 2 * s * ∑ i, t i - ∑ i, t i ^ 2 := by
      simp only [mul_sub, Finset.sum_sub_distrib, pow_two]
      rw [Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl; intros; ring
    rw [← Finset.sum_div, this, h1, h2]; field_simp; ring
  have e2 : ∑ i, t i * (t i - s) / (2 * s ^ 2) = n2 := by
    have : ∑ i, t i * (t i - s) = ∑ i, t i ^ 2 - s * ∑ i, t i := by
      simp only [mul_sub, Finset.sum_sub_distrib, pow_two]
      rw [Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl; intros; ring
    rw [← Finset.sum_div, this, h1, h2]; field_simp; ring
  simp only [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, e1, e2, Finset.sum_const, nsmul_eq_mul]
  simp
  ring

theorem spectrum_three_valued (T ρ : Matrix ι ι ℂ) (hT : T.IsHermitian) (hρ : ρ.IsHermitian)
    (s : ℝ) (hs : s ≠ 0)
    (h3 : T * (T - (s : ℂ) • (1 : Matrix ι ι ℂ)) * (T - ((2 * s : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) = 0)
    (c0 c1 c2 : ℝ)
    (hρeq : ρ = (c0 : ℂ) • (1 : Matrix ι ι ℂ) + (c1 : ℂ) • T + (c2 : ℂ) • (T * T)) (n1 n2 : ℝ)
    (htr1 : T.trace = ((s * (n1 + 2 * n2) : ℝ) : ℂ))
    (htr2 : (T * T).trace = ((s ^ 2 * (n1 + 4 * n2) : ℝ) : ℂ)) (g : ℝ → ℝ) :
    ∑ i, g (hρ.eigenvalues i) =
      Fintype.card ι * g c0 + n1 * (g (c0 + c1 * s + c2 * s ^ 2) - g c0) +
        n2 * (g (c0 + c1 * (2 * s) + c2 * (2 * s) ^ 2) - g c0) := by
  rw [sum_eigenvalues_poly T ρ hT hρ c0 c1 c2 hρeq g]
  set Φ := conjStarAlgAut ℂ _ hT.eigenvectorUnitary with hΦ
  set D : Matrix ι ι ℂ := diagonal (RCLike.ofReal ∘ hT.eigenvalues) with hD
  have hTD : T = Φ D := hT.spectral_theorem
  have htrΦ : ∀ X : Matrix ι ι ℂ, (Φ X).trace = X.trace := by
    intro X
    have h1 : star (hT.eigenvectorUnitary : Matrix ι ι ℂ) * hT.eigenvectorUnitary = 1 :=
      Unitary.coe_star_mul_self hT.eigenvectorUnitary
    rw [hΦ, conjStarAlgAut_apply, mul_assoc, Matrix.trace_mul_comm, mul_assoc X, h1,
      mul_one]
  have ht : ∀ i, hT.eigenvalues i = 0 ∨ hT.eigenvalues i = s ∨ hT.eigenvalues i = 2 * s := by
    intro i
    have h0 : Φ (D * (D - (s : ℂ) • 1) * (D - ((2 * s : ℝ) : ℂ) • 1)) = 0 := by
      rw [map_mul, map_mul, map_sub, map_sub, map_smul, map_smul, map_one, ← hTD]; exact h3
    have h0' := (map_eq_zero_iff Φ (EmbeddingLike.injective Φ)).1 h0
    have e : D * (D - (s : ℂ) • (1 : Matrix ι ι ℂ)) * (D - ((2 * s : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) =
        diagonal (fun i => ((hT.eigenvalues i : ℝ) : ℂ) * (((hT.eigenvalues i : ℝ) : ℂ) - s) *
          (((hT.eigenvalues i : ℝ) : ℂ) - ((2 * s : ℝ) : ℂ))) := by
      rw [Matrix.smul_one_eq_diagonal, Matrix.smul_one_eq_diagonal, hD, diagonal_sub,
        diagonal_sub, diagonal_mul_diagonal, diagonal_mul_diagonal]
      rfl
    rw [e] at h0'
    have := congrFun (congrFun h0' i) i
    simp only [diagonal_apply_eq, Matrix.zero_apply] at this
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · left; exact_mod_cast h
      · right; left; have := sub_eq_zero.1 h; exact_mod_cast this
    · right; right; have := sub_eq_zero.1 h; exact_mod_cast this
  have h1 : ∑ i, hT.eigenvalues i = s * (n1 + 2 * n2) := by
    have := hT.trace_eq_sum_eigenvalues
    rw [htr1] at this
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum]
    exact this.symm
  have h2 : ∑ i, hT.eigenvalues i ^ 2 = s ^ 2 * (n1 + 4 * n2) := by
    have e : (T * T).trace = ∑ i, ((hT.eigenvalues i : ℝ) : ℂ) ^ 2 := by
      have hTT : T * T = Φ (D * D) := by rw [map_mul, ← hTD]
      rw [hTT, htrΦ]
      simp [hD, Matrix.trace, pow_two]
    rw [htr2] at e
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum]
    simpa using e.symm
  have := three_valued_sum hT.eigenvalues s hs ht (fun t => g (c0 + c1 * t + c2 * t ^ 2)) n1 n2 h1 h2
  simpa using this


end Generic



/-! ### The reduced matrices as complex Hermitian matrices -/

/-- The reduced density matrix of a three-qubit cut, as a complex matrix. -/
noncomputable def redMat (cut : Cut 3 4) (alpha beta : ℝ) : Matrix Triple Triple ℂ :=
  Matrix.of fun a b => ((entry cut alpha beta a b : ℝ) : ℂ)

theorem entry_symm {k l : ℕ} (cut : Cut k l) (alpha beta : ℝ) (a b : Fin k → Bool) :
    entry cut alpha beta a b = entry cut alpha beta b a := by
  unfold entry
  exact Finset.sum_congr rfl fun r _ => mul_comm _ _

theorem redMat_isHermitian (cut : Cut 3 4) (alpha beta : ℝ) : (redMat cut alpha beta).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, redMat, entry_symm cut alpha beta i j]

/-- Von Neumann entropy (in nats) of the reduced state of a three-qubit cut. -/
noncomputable def cutEntropy (cut : Cut 3 4) (alpha beta : ℝ) : ℝ :=
  ∑ i, Real.negMulLog ((redMat_isHermitian cut alpha beta).eigenvalues i)

/-- The integer-to-complex matrix map. -/
abbrev castHom : Matrix Triple Triple ℤ →+* Matrix Triple Triple ℂ := (Int.castRingHom ℂ).mapMatrix

theorem ofNat_mat (n : ℕ) [n.AtLeastTwo] :
    (((OfNat.ofNat n : ℝ)) : ℂ) • (1 : Matrix Triple Triple ℂ) =
      (OfNat.ofNat n : Matrix Triple Triple ℂ) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.ofNat_apply]; rfl
  · simp [Matrix.ofNat_apply, h]

theorem ofNat_mul_mat (n : ℕ) [n.AtLeastTwo] (X : Matrix Triple Triple ℂ) :
    (OfNat.ofNat n : Matrix Triple Triple ℂ) * X = (((OfNat.ofNat n : ℝ)) : ℂ) • X := by
  rw [← ofNat_mat n, smul_mul_assoc, one_mul]

theorem castHom_trace (M : Matrix Triple Triple ℤ) : (castHom M).trace = ((M.trace : ℤ) : ℂ) := by
  simp [Matrix.trace, castHom, RingHom.mapMatrix_apply]

theorem castHom_isHermitian (M : Matrix Triple Triple ℤ) (h : M.transpose = M) :
    (castHom M).IsHermitian := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.transpose_apply] at this
  simp [Matrix.conjTranspose_apply, castHom, RingHom.mapMatrix_apply, this]

theorem gram_symm {k l : ℕ} (cut : Cut k l) (f : BitString → ℤ) (a b : Fin k → Bool) :
    gram cut f f a b = gram cut f f b a := by
  unfold gram
  exact Finset.sum_congr rfl fun r _ => mul_comm _ _

theorem matP_transpose (cut : Cut 3 4) : (matP cut).transpose = matP cut := by
  ext i j; exact gram_symm cut alphaCoefficient j i

theorem matR_transpose (cut : Cut 3 4) : (matR cut).transpose = matR cut := by
  ext i j; exact gram_symm cut betaCoefficient j i

theorem matT_transpose (cut : Cut 3 4) : (matT cut).transpose = matT cut := by
  simp [matT, Matrix.transpose_add, Matrix.transpose_sub, matP_transpose, matR_transpose]
  exact (Commute.ofNat_right _ _).eq

theorem redMat_eq (cut : Cut 3 4) (alpha beta : ℝ) :
    redMat cut alpha beta = ((alpha ^ 2 : ℝ) : ℂ) • castHom (matP cut) +
      ((alpha * beta : ℝ) : ℂ) • castHom (matQ cut) + ((beta ^ 2 : ℝ) : ℂ) • castHom (matR cut) := by
  ext a b
  simp only [redMat, Matrix.of_apply, entry_expand, Matrix.add_apply, Matrix.smul_apply,
    castHom, RingHom.mapMatrix_apply, Matrix.map_apply, matP, matQ, matR, smul_eq_mul]
  push_cast
  simp only [eq_intCast]

/-! ### Spectrum on a cut avoiding the special site -/

theorem spectrum_avoiding (cut : Cut 3 4) (h : AvoidCert cut) (alpha beta : ℝ) (g : ℝ → ℝ) :
    ∑ i, g ((redMat_isHermitian cut alpha beta).eigenvalues i) =
      6 * g (4 * alpha ^ 2) + 2 * g (3 * alpha ^ 2 + beta ^ 2) := by
  obtain ⟨hQ, hRR, hP, htr⟩ := h
  have hQc : castHom (matQ cut) = 0 := by rw [hQ, map_zero]
  have hRc : castHom (matR cut) * castHom (matR cut) = castHom (matR cut) := by
    rw [← map_mul, hRR]
  have hPc : castHom (matP cut) = 4 - castHom (matR cut) := by rw [hP, map_sub, map_ofNat]
  have h4 := ofNat_mat 4
  have h2 := ofNat_mat 2
  have hρ : redMat cut alpha beta = ((4 * alpha ^ 2 : ℝ) : ℂ) • (1 : Matrix Triple Triple ℂ) +
      ((beta ^ 2 - alpha ^ 2 : ℝ) : ℂ) • castHom (matR cut) +
        ((0 : ℝ) : ℂ) • (castHom (matR cut) * castHom (matR cut)) := by
    rw [redMat_eq, hQc, hPc, ← h4]
    simp only [smul_zero, add_zero, smul_sub, Complex.ofReal_zero, zero_smul]
    push_cast
    module
  have hT := castHom_isHermitian (matR cut) (matR_transpose cut)
  have hcube : castHom (matR cut) * (castHom (matR cut) - ((1 : ℝ) : ℂ) • (1 : Matrix Triple Triple ℂ)) *
      (castHom (matR cut) - ((2 * 1 : ℝ) : ℂ) • (1 : Matrix Triple Triple ℂ)) = 0 := by
    have e2 : ((2 * 1 : ℝ) : ℂ) • (1 : Matrix Triple Triple ℂ) = (2 : Matrix Triple Triple ℂ) := by
      rw [← h2]; norm_num
    rw [e2, Complex.ofReal_one, one_smul]
    have : castHom (matR cut) * (castHom (matR cut) - 1) = 0 := by
      rw [mul_sub, mul_one, hRc, sub_self]
    rw [this, zero_mul]
  have key := spectrum_three_valued (castHom (matR cut)) (redMat cut alpha beta) hT
    (redMat_isHermitian cut alpha beta) 1 one_ne_zero hcube (4 * alpha ^ 2) (beta ^ 2 - alpha ^ 2) 0 hρ
    2 0 (by rw [castHom_trace, htr]; norm_num) (by rw [hRc, castHom_trace, htr]; norm_num) g
  simp at key
  rw [key, show 4 * alpha ^ 2 + (beta ^ 2 - alpha ^ 2) = 3 * alpha ^ 2 + beta ^ 2 by ring]
  ring


/-! ### Spectrum on a cut containing the special site -/

theorem spectrum_containing (cut : Cut 3 4) (h : ContainCert cut) (alpha beta : ℝ) (g : ℝ → ℝ) :
    ∑ i, g ((redMat_isHermitian cut alpha beta).eigenvalues i) =
      5 * g (4 * alpha ^ 2) + g (8 * alpha ^ 2) + 2 * g (alpha ^ 2 + beta ^ 2) := by
  obtain ⟨hQ, hcube, h32, htr1, htr2⟩ := h
  set Tc := castHom (matT cut) with hTc
  set Rc := castHom (matR cut) with hRcdef
  have hQc : castHom (matQ cut) = 0 := by rw [hQ, map_zero]
  have h4 := ofNat_mat 4
  have h8 := ofNat_mat 8
  -- `T = P - 4 + 11 R`
  have hT_def : Tc = castHom (matP cut) - ((4 : ℝ) : ℂ) • 1 + ((11 : ℝ) : ℂ) • Rc := by
    have : Tc = castHom (matP cut) - 4 + (11 : ℤ) • Rc := by
      simp only [hTc, hRcdef, matT, map_add, map_sub, map_ofNat, map_zsmul]
    rw [this, ← h4, ← Int.cast_smul_eq_zsmul ℂ]
    push_cast
    rfl
  -- `32 R = T² - 4 T`
  have hR32 : ((32 : ℝ) : ℂ) • Rc = Tc * Tc - ((4 : ℝ) : ℂ) • Tc := by
    have := congrArg castHom h32
    simp only [map_mul, map_sub, map_ofNat] at this
    rw [← hTc, ← hRcdef, ofNat_mul_mat, ofNat_mul_mat] at this
    exact this
  have hPc : castHom (matP cut) = Tc + ((4 : ℝ) : ℂ) • 1 - ((11 : ℝ) : ℂ) • Rc := by
    rw [hT_def]; abel
  have hRc : Rc = ((1 / 32 : ℝ) : ℂ) • (Tc * Tc - ((4 : ℝ) : ℂ) • Tc) := by
    rw [← hR32, smul_smul]
    push_cast
    norm_num
  have hρ : redMat cut alpha beta = ((4 * alpha ^ 2 : ℝ) : ℂ) • (1 : Matrix Triple Triple ℂ) +
      ((alpha ^ 2 - (beta ^ 2 - 11 * alpha ^ 2) / 8 : ℝ) : ℂ) • Tc +
        (((beta ^ 2 - 11 * alpha ^ 2) / 32 : ℝ) : ℂ) • (Tc * Tc) := by
    rw [redMat_eq, hQc, hPc, ← hRcdef, hRc]
    push_cast
    module
  have hT : Tc.IsHermitian := castHom_isHermitian (matT cut) (matT_transpose cut)
  have hcube' : Tc * (Tc - ((4 : ℝ) : ℂ) • (1 : Matrix Triple Triple ℂ)) *
      (Tc - ((2 * 4 : ℝ) : ℂ) • (1 : Matrix Triple Triple ℂ)) = 0 := by
    have e8 : ((2 * 4 : ℝ) : ℂ) • (1 : Matrix Triple Triple ℂ) = (8 : Matrix Triple Triple ℂ) := by
      rw [← h8]; norm_num
    rw [e8, h4, hTc, ← map_ofNat castHom 4, ← map_ofNat castHom 8, ← map_sub, ← map_sub, ← map_mul,
      ← map_mul, hcube, map_zero]
  have key := spectrum_three_valued Tc (redMat cut alpha beta) hT (redMat_isHermitian cut alpha beta)
    4 (by norm_num) hcube' (4 * alpha ^ 2) (alpha ^ 2 - (beta ^ 2 - 11 * alpha ^ 2) / 8)
    ((beta ^ 2 - 11 * alpha ^ 2) / 32) hρ 1 2
    (by rw [hTc, castHom_trace, htr1]; push_cast; norm_num)
    (by rw [hTc, ← map_mul, castHom_trace, htr2]; push_cast; norm_num) g
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at key
  rw [key, show 4 * alpha ^ 2 + (alpha ^ 2 - (beta ^ 2 - 11 * alpha ^ 2) / 8) * 4 +
      (beta ^ 2 - 11 * alpha ^ 2) / 32 * 4 ^ 2 = 8 * alpha ^ 2 by ring,
    show 4 * alpha ^ 2 + (alpha ^ 2 - (beta ^ 2 - 11 * alpha ^ 2) / 8) * (2 * 4) +
      (beta ^ 2 - 11 * alpha ^ 2) / 32 * (2 * 4) ^ 2 = alpha ^ 2 + beta ^ 2 by ring]
  push_cast
  ring


/-! ### Every three-qubit cut -/

/-- The spectrum of the reduced matrix of every three-qubit cut: for each function `g`,
`∑ g(eigenvalue)` is `6 g(4α²) + 2 g(3α²+β²)` on cuts avoiding the special site `0`, and
`g(8α²) + 5 g(4α²) + 2 g(α²+β²)` on those containing it. -/
theorem tripleCut_spectrum (m : Fin 7 → Bool) (hm : weight m = 3) (alpha beta : ℝ) (g : ℝ → ℝ) :
    ∑ i, g ((redMat_isHermitian (maskCut 3 4 m) alpha beta).eigenvalues i) =
      if m 0 = true then 5 * g (4 * alpha ^ 2) + g (8 * alpha ^ 2) + 2 * g (alpha ^ 2 + beta ^ 2)
      else 6 * g (4 * alpha ^ 2) + 2 * g (3 * alpha ^ 2 + beta ^ 2) := by
  obtain ⟨hc, ha⟩ := cuts_cert m hm
  by_cases h : m 0 = true
  · simp only [h, ↓reduceIte]; exact spectrum_containing _ (hc h) alpha beta g
  · simp only [h]; exact spectrum_avoiding _ (ha h) alpha beta g

theorem tripleCut_entropy (m : Fin 7 → Bool) (hm : weight m = 3) (alpha beta : ℝ) :
    cutEntropy (maskCut 3 4 m) alpha beta =
      if m 0 = true then
        5 * Real.negMulLog (4 * alpha ^ 2) + Real.negMulLog (8 * alpha ^ 2) +
          2 * Real.negMulLog (alpha ^ 2 + beta ^ 2)
      else 6 * Real.negMulLog (4 * alpha ^ 2) + 2 * Real.negMulLog (3 * alpha ^ 2 + beta ^ 2) :=
  tripleCut_spectrum m hm alpha beta Real.negMulLog

/-- Mean von Neumann entropy (nats) over the 35 three-qubit cuts. -/
noncomputable def meanTripleEntropy (alpha beta : ℝ) : ℝ :=
  (∑ m ∈ tripleMasks, cutEntropy (maskCut 3 4 m) alpha beta) / 35

theorem meanTripleEntropy_eq (alpha beta : ℝ) :
    meanTripleEntropy alpha beta =
      (195 * Real.negMulLog (4 * alpha ^ 2) + 40 * Real.negMulLog (3 * alpha ^ 2 + beta ^ 2) +
        15 * Real.negMulLog (8 * alpha ^ 2) + 30 * Real.negMulLog (alpha ^ 2 + beta ^ 2)) / 35 := by
  unfold meanTripleEntropy
  have hs : ∀ m ∈ tripleMasks, cutEntropy (maskCut 3 4 m) alpha beta =
      if m 0 = true then
        5 * Real.negMulLog (4 * alpha ^ 2) + Real.negMulLog (8 * alpha ^ 2) +
          2 * Real.negMulLog (alpha ^ 2 + beta ^ 2)
      else 6 * Real.negMulLog (4 * alpha ^ 2) + 2 * Real.negMulLog (3 * alpha ^ 2 + beta ^ 2) :=
    fun m hm => tripleCut_entropy m (Finset.mem_filter.1 hm).2 alpha beta
  rw [Finset.sum_congr rfl hs, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    tripleMasks_containing_card, tripleMasks_avoiding_card]
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-- On the family `α² = (1-2x)/30`, `β² = x`, with `u = (1-2x)/30`. -/
theorem meanTripleEntropy_family (x alpha beta : ℝ) (hα : alpha ^ 2 = u x) (hβ : beta ^ 2 = x) :
    meanTripleEntropy alpha beta =
      (195 * Real.negMulLog (4 * u x) + 40 * Real.negMulLog (3 * u x + x) +
        15 * Real.negMulLog (8 * u x) + 30 * Real.negMulLog (u x + x)) / 35 := by
  rw [meanTripleEntropy_eq, hα, hβ]

end FormalResearch.FourQubitEntropy.SevenQubitIco
