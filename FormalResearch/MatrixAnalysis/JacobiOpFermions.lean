module

public import FormalResearch.MatrixAnalysis.JacobiOpPolar
public import FormalResearch.MatrixAnalysis.JacobiOpSchur
public import FormalResearch.MatrixAnalysis.Spectral.WeylMatrix

/-!
# Jacobi operator package: free-fermion correlation matrices

Paper J, Corollary `cor:fermions` (`main_results.tex`) with the proof of `thmB.tex`, "Free-fermion
correlation matrices".  All statements are for an orthogonal `U` (the paper's `U_h`) and a real
matrix `G` with `‖G - U‖ ≤ ε` (spectral norm, `ε` the paper's `C_m h^m` or `2 C_m h^m`), a diagonal
occupation `F = diag f`, `0 ≤ f ≤ 1`, and a coordinate projection.

* `jop_fermion_compression_bound`: `‖P (G F Gᵀ - U F Uᵀ) P‖ ≤ ε (‖G‖ + 1) ≤ 3ε` for `P = diag p`,
  `p_i ∈ [0,1]` (a coordinate projection is `p_i ∈ {0,1}`), when `ε ≤ 1`.  The transpose norms are
  derived (`‖Mᵀ‖ = ‖M‖`).
* `jop_fermion_polar_bound`: the same with the polar factor `Q` of `G` (`jop_polarMatrix`) in place of `G`,
  with `4ε`; this uses `‖Q - U‖ ≤ 2ε` (`jop_polar_repair_matrix`).
* `jop_fermion_eigenvalue_bound`: the `k`-th eigenvalues (decreasing: `eigenvalues₀`) of the principal
  submatrices on the rows `f : m → n` of `P` of `U F Uᵀ` and `G F Gᵀ` differ by at most `3ε` (Weyl).
* `jop_entanglement_energy_bound`: the logarithmic estimate `8ε/τ` (mean value theorem), and its
  combination with the eigenvalue bound, `jop_fermion_energy_bound`.

Not formalised: the identification of `U`, `G` with the Jacobi eigenvector matrix and its approximant (the
input `‖G - U‖ ≤ C_m h^m` is Theorem B of Paper J); the entropy remark `rem:thb-entropy`.
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis

open Matrix

section Energy

/-- The entanglement energy `x ↦ log ((1 - x) / x)` is `(8 / (3 τ))`-Lipschitz on `[τ/2, 1 - τ/2]`
for `0 < τ ≤ 1/2`. -/
lemma jop_energy_lipschitz {τ x y : ℝ} (hτ : 0 < τ) (hτ2 : τ ≤ 1 / 2)
    (hx : x ∈ Set.Icc (τ / 2) (1 - τ / 2)) (hy : y ∈ Set.Icc (τ / 2) (1 - τ / 2)) :
    |Real.log ((1 - y) / y) - Real.log ((1 - x) / x)| ≤ 8 / (3 * τ) * |y - x| := by
  set s : Set ℝ := Set.Icc (τ / 2) (1 - τ / 2) with hs
  have hpos : ∀ z ∈ s, 0 < z ∧ 0 < 1 - z := fun z hz =>
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
  set g : ℝ → ℝ := fun z => Real.log (1 - z) - Real.log z with hg
  have hlog : ∀ z ∈ s, Real.log ((1 - z) / z) = g z := fun z hz => by
    obtain ⟨h1, h2⟩ := hpos z hz
    simp only [hg]; rw [Real.log_div h2.ne' h1.ne']
  have hderiv : ∀ z ∈ s, HasDerivAt g (-(1 - z)⁻¹ - z⁻¹) z := fun z hz => by
    obtain ⟨h1, h2⟩ := hpos z hz
    have a : HasDerivAt (fun z : ℝ => 1 - z) (-1) z := by simpa using (hasDerivAt_id z).const_sub 1
    have b := (a.log h2.ne')
    have c := Real.hasDerivAt_log h1.ne'
    have := b.sub c
    convert this using 1
    field_simp
  have hbound : ∀ z ∈ s, ‖deriv g z‖ ≤ 8 / (3 * τ) := fun z hz => by
    obtain ⟨h1, h2⟩ := hpos z hz
    rw [(hderiv z hz).deriv, Real.norm_eq_abs]
    have : -(1 - z)⁻¹ - z⁻¹ = -(1 / (z * (1 - z))) := by field_simp; ring
    rw [this, abs_neg, abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    have hz1 : τ / 2 ≤ z := hz.1
    have hz2 : z ≤ 1 - τ / 2 := hz.2
    nlinarith [mul_nonneg (sub_nonneg.2 hz1) (sub_nonneg.2 hz2)]
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := g) (s := s) (C := 8 / (3 * τ))
    (fun z hz => (hderiv z hz).differentiableAt) hbound (convex_Icc _ _) hx hy
  rw [hlog x hx, hlog y hy]
  simpa [Real.norm_eq_abs] using key

/-- **Entanglement-energy estimate** (Paper J `cor:fermions`).  If `6ε ≤ τ ≤ 1/2`, `ν ∈ [τ, 1 - τ]`
and `|ν - ν̂| ≤ 3ε` then `|log((1-ν)/ν) - log((1-ν̂)/ν̂)| ≤ 8ε/τ`: the mean value theorem on `[τ/2, 1 - τ/2]`
with the Lipschitz constant `8/(3τ)` (`jop_energy_lipschitz`) and `d = 3ε`, as in the paper's proof of `cor:fermions`. -/
theorem jop_entanglement_energy_bound {τ ε ν ν' : ℝ} (hε : 0 ≤ ε) (hτ : 6 * ε ≤ τ) (hτ2 : τ ≤ 1 / 2)
    (hτ0 : 0 < τ) (hν : ν ∈ Set.Icc τ (1 - τ)) (hνν : |ν - ν'| ≤ 3 * ε) :
    |Real.log ((1 - ν) / ν) - Real.log ((1 - ν') / ν')| ≤ 8 * ε / τ := by
  have h3 := abs_le.1 hνν
  have hx : ν ∈ Set.Icc (τ / 2) (1 - τ / 2) := ⟨by linarith [hν.1], by linarith [hν.2]⟩
  have hy : ν' ∈ Set.Icc (τ / 2) (1 - τ / 2) :=
    ⟨by linarith [hν.1, h3.1, h3.2], by linarith [hν.2, h3.1, h3.2]⟩
  have := jop_energy_lipschitz hτ0 hτ2 hy hx
  calc _ ≤ 8 / (3 * τ) * |ν - ν'| := this
    _ ≤ 8 / (3 * τ) * (3 * ε) := by gcongr
    _ = 8 * ε / τ := by field_simp

end Energy

section Algebra

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma jop_norm_orth_le {U : Matrix n n ℝ} (hU : Uᵀ * U = 1) : ‖U‖ ≤ 1 :=
  jop_norm_le_of_apply U zero_le_one fun x => by rw [jop_norm_orth hU, one_mul]

lemma jop_norm_transpose (M : Matrix n n ℝ) : ‖Mᵀ‖ = ‖M‖ := by
  simpa using l2_opNorm_conjTranspose M

lemma jop_norm_G_le {G U : Matrix n n ℝ} (hU : Uᵀ * U = 1) {ε : ℝ} (hGU : ‖G - U‖ ≤ ε) :
    ‖G‖ ≤ 1 + ε := by
  have h := norm_le_insert' G U
  linarith [jop_norm_orth_le hU]

/-- **Product perturbation** `G F Gᵀ - U F Uᵀ = (G - U) F Gᵀ + U F (G - U)ᵀ` and its norm bound
`ε (‖G‖ + 1)`; the transpose norms are derived, only `‖G - U‖ ≤ ε`, `U` orthogonal and
`F = diag f` with `0 ≤ f ≤ 1` are assumed. -/
theorem jop_fermion_product_bound (G U : Matrix n n ℝ) (f : n → ℝ) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1)
    (hU : Uᵀ * U = 1) {ε : ℝ} (hGU : ‖G - U‖ ≤ ε) :
    ‖G * diagonal f * Gᵀ - U * diagonal f * Uᵀ‖ ≤ ε * (‖G‖ + 1) := by
  have hF : ‖(diagonal f : Matrix n n ℝ)‖ ≤ 1 :=
    jop_norm_diagonal_le f zero_le_one fun i => by rw [abs_of_nonneg (hf i).1]; exact (hf i).2
  have hid : G * diagonal f * Gᵀ - U * diagonal f * Uᵀ =
      (G - U) * diagonal f * Gᵀ + U * diagonal f * (G - U)ᵀ := by
    simp only [Matrix.transpose_sub]; noncomm_ring
  have hε : 0 ≤ ε := (norm_nonneg _).trans hGU
  have hT : ‖(G - U)ᵀ‖ ≤ ε := by rwa [jop_norm_transpose]
  have h1 : ‖(G - U) * diagonal f * Gᵀ‖ ≤ ε * 1 * ‖G‖ := by
    calc _ ≤ ‖(G - U) * diagonal f‖ * ‖Gᵀ‖ := l2_opNorm_mul _ _
      _ ≤ (‖G - U‖ * ‖(diagonal f : Matrix n n ℝ)‖) * ‖Gᵀ‖ := by
        gcongr; exact l2_opNorm_mul _ _
      _ ≤ ε * 1 * ‖G‖ := by rw [jop_norm_transpose]; gcongr
  have h2 : ‖U * diagonal f * (G - U)ᵀ‖ ≤ 1 * 1 * ε := by
    calc _ ≤ ‖U * diagonal f‖ * ‖(G - U)ᵀ‖ := l2_opNorm_mul _ _
      _ ≤ (‖U‖ * ‖(diagonal f : Matrix n n ℝ)‖) * ‖(G - U)ᵀ‖ := by
        gcongr; exact l2_opNorm_mul _ _
      _ ≤ 1 * 1 * ε := by gcongr; exact jop_norm_orth_le hU
  rw [hid]
  calc _ ≤ ‖(G - U) * diagonal f * Gᵀ‖ + ‖U * diagonal f * (G - U)ᵀ‖ := norm_add_le _ _
    _ ≤ ε * (‖G‖ + 1) := by nlinarith

lemma jop_norm_diagonal_01_le (p : n → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    ‖(diagonal p : Matrix n n ℝ)‖ ≤ 1 :=
  jop_norm_diagonal_le p zero_le_one fun i => by rw [abs_of_nonneg (hp i).1]; exact (hp i).2

lemma jop_compress_le (p : n → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (M : Matrix n n ℝ) :
    ‖diagonal p * M * diagonal p‖ ≤ ‖M‖ := by
  have hP := jop_norm_diagonal_01_le p hp
  calc _ ≤ ‖diagonal p * M‖ * ‖(diagonal p : Matrix n n ℝ)‖ := l2_opNorm_mul _ _
    _ ≤ (‖(diagonal p : Matrix n n ℝ)‖ * ‖M‖) * ‖(diagonal p : Matrix n n ℝ)‖ := by
      gcongr; exact l2_opNorm_mul _ _
    _ ≤ 1 * ‖M‖ * 1 := by gcongr
    _ = ‖M‖ := by ring

/-- **Free-fermion compression bound** (Paper J `cor:fermions`, eq. (fermions)).  For `U` orthogonal,
`‖G - U‖ ≤ ε ≤ 1`, `F = diag f` with `0 ≤ f ≤ 1` and `P = diag p` with `p_i ∈ [0,1]` (a coordinate
projection has `p_i ∈ {0,1}`):
`‖P (G F Gᵀ - U F Uᵀ) P‖ ≤ ε (‖G‖ + 1) ≤ 3ε`. -/
theorem jop_fermion_compression_bound (G U : Matrix n n ℝ) (f p : n → ℝ)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hU : Uᵀ * U = 1)
    {ε : ℝ} (hGU : ‖G - U‖ ≤ ε) (hε1 : ε ≤ 1) :
    ‖diagonal p * (G * diagonal f * Gᵀ - U * diagonal f * Uᵀ) * diagonal p‖ ≤ ε * (‖G‖ + 1) ∧
      ε * (‖G‖ + 1) ≤ 3 * ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hGU
  refine ⟨(jop_compress_le p hp _).trans (jop_fermion_product_bound G U f hf hU hGU), ?_⟩
  have := jop_norm_G_le hU hGU
  nlinarith

/-- **Free-fermion compression bound for the polar factor** (Paper J `cor:fermions`, second clause):
with `Q` the polar factor of `G` (`jop_polarMatrix`) and `‖G - U‖ ≤ ε < 1`,
`‖P (Q F Qᵀ - U F Uᵀ) P‖ ≤ 4ε`. -/
theorem jop_fermion_polar_bound (G U : Matrix n n ℝ) (f p : n → ℝ)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hU : Uᵀ * U = 1)
    {ε : ℝ} (hGU : ‖G - U‖ ≤ ε) (hε1 : ε < 1) :
    ‖diagonal p * (jop_polarMatrix G (jop_injective_of_close hU (hGU.trans_lt hε1)) *
        diagonal f * (jop_polarMatrix G (jop_injective_of_close hU (hGU.trans_lt hε1)))ᵀ -
        U * diagonal f * Uᵀ) * diagonal p‖ ≤ 4 * ε := by
  have hlt := hGU.trans_lt hε1
  obtain ⟨hQ, -, -, hQU⟩ := jop_polar_repair_matrix G U hU hlt
  have hQU' : ‖jop_polarMatrix G (jop_injective_of_close hU hlt) - U‖ ≤ 2 * ε := by linarith
  have h := jop_fermion_product_bound (jop_polarMatrix G (jop_injective_of_close hU hlt)) U f hf hU hQU'
  have hQn := jop_norm_orth_le hQ
  refine (jop_compress_le p hp _).trans (h.trans ?_)
  have : 0 ≤ ε := (norm_nonneg _).trans hGU
  nlinarith

lemma jop_isHermitian_sandwich (G : Matrix n n ℝ) (f : n → ℝ) :
    (G * diagonal f * Gᵀ).IsHermitian := by
  have hd : (diagonal f : Matrix n n ℝ).IsHermitian := by
    simp [Matrix.IsHermitian]
  simpa using Matrix.isHermitian_mul_mul_conjTranspose G hd

/-- Principal submatrices do not increase the spectral norm. -/
lemma jop_norm_submatrix_le {m : Type*} [Fintype m] [DecidableEq m] (e : m → n)
    (he : Function.Injective e) (M : Matrix n n ℝ) : ‖M.submatrix e e‖ ≤ ‖M‖ := by
  set J : Matrix n m ℝ := Spectral.embedMatrix (𝕜 := ℝ) e
  have hJ : Jᴴ * J = 1 := Spectral.embedMatrix_conjTranspose_mul e he
  have hJn : ‖J‖ ≤ 1 := by
    have h := l2_opNorm_conjTranspose_mul_self J
    rw [hJ] at h
    have h1 : ‖(1 : Matrix m m ℝ)‖ ≤ 1 := by
      have := jop_norm_diagonal_le (fun _ : m => (1 : ℝ)) zero_le_one fun _ => by simp
      simpa using this
    nlinarith [norm_nonneg J]
  rw [← Spectral.embedMatrix_conj e M]
  calc ‖Jᴴ * M * J‖ ≤ ‖Jᴴ * M‖ * ‖J‖ := l2_opNorm_mul _ _
    _ ≤ (‖Jᴴ‖ * ‖M‖) * ‖J‖ := by gcongr; exact l2_opNorm_mul _ _
    _ ≤ 1 * ‖M‖ * 1 := by rw [l2_opNorm_conjTranspose]; gcongr
    _ = ‖M‖ := by ring

/-- **Eigenvalue comparison** (Paper J `cor:fermions`).  For `‖G - U‖ ≤ ε ≤ 1` the `k`-th eigenvalues
(decreasing order, `eigenvalues₀`) of the compressions `U F Uᵀ` and `G F Gᵀ` to the coordinates
`e : m → n` (a coordinate projection `P`, viewed on its range) differ by at most `3ε`. -/
theorem jop_fermion_eigenvalue_bound {m : Type*} [Fintype m] [DecidableEq m] (e : m → n)
    (he : Function.Injective e) (G U : Matrix n n ℝ) (f : n → ℝ) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1)
    (hU : Uᵀ * U = 1) {ε : ℝ} (hGU : ‖G - U‖ ≤ ε) (hε1 : ε ≤ 1) (k : Fin (Fintype.card m)) :
    |((jop_isHermitian_sandwich U f).submatrix e).eigenvalues₀ k -
        ((jop_isHermitian_sandwich G f).submatrix e).eigenvalues₀ k| ≤ 3 * ε := by
  have h := Spectral.herm_abs_eigenvalues₀_sub_le_norm ((jop_isHermitian_sandwich U f).submatrix e)
    ((jop_isHermitian_sandwich G f).submatrix e) k
  refine h.trans ?_
  have hsub : (U * diagonal f * Uᵀ).submatrix e e - (G * diagonal f * Gᵀ).submatrix e e =
      (-(G * diagonal f * Gᵀ - U * diagonal f * Uᵀ)).submatrix e e := by
    ext i j; simp
  rw [hsub]
  refine (jop_norm_submatrix_le e he _).trans ?_
  rw [norm_neg]
  exact (jop_fermion_product_bound G U f hf hU hGU).trans
    (by have := jop_norm_G_le hU hGU; have : 0 ≤ ε := (norm_nonneg _).trans hGU; nlinarith)

/-- **Free-fermion entanglement energies** (Paper J `cor:fermions`, last clause).  With `ν_k`, `ν̂_k` the
`k`-th eigenvalues of the compressions of `U F Uᵀ` and `G F Gᵀ` to the coordinates `e`, `‖G - U‖ ≤ ε`,
`0 < τ ≤ 1/2` and `6ε ≤ τ`: `|ν_k - ν̂_k| ≤ 3ε`, and if `ν_k ∈ [τ, 1 - τ]` the energies
`log ((1-ν)/ν)` differ by at most `8ε/τ`. -/
theorem jop_fermion_energy_bound {m : Type*} [Fintype m] [DecidableEq m] (e : m → n)
    (he : Function.Injective e) (G U : Matrix n n ℝ) (f : n → ℝ) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1)
    (hU : Uᵀ * U = 1) {ε τ : ℝ} (hGU : ‖G - U‖ ≤ ε) (hτ0 : 0 < τ) (hτ : 6 * ε ≤ τ)
    (hτ2 : τ ≤ 1 / 2) (k : Fin (Fintype.card m)) :
    |((jop_isHermitian_sandwich U f).submatrix e).eigenvalues₀ k -
        ((jop_isHermitian_sandwich G f).submatrix e).eigenvalues₀ k| ≤ 3 * ε ∧
      (((jop_isHermitian_sandwich U f).submatrix e).eigenvalues₀ k ∈ Set.Icc τ (1 - τ) →
        |Real.log ((1 - ((jop_isHermitian_sandwich U f).submatrix e).eigenvalues₀ k) /
              ((jop_isHermitian_sandwich U f).submatrix e).eigenvalues₀ k) -
          Real.log ((1 - ((jop_isHermitian_sandwich G f).submatrix e).eigenvalues₀ k) /
              ((jop_isHermitian_sandwich G f).submatrix e).eigenvalues₀ k)| ≤ 8 * ε / τ) := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hGU
  have h := jop_fermion_eigenvalue_bound e he G U f hf hU hGU (by linarith) k
  exact ⟨h, fun hν => jop_entanglement_energy_bound hε hτ hτ2 hτ0 hν h⟩

end Algebra

/-- info: 'FormalResearch.MatrixAnalysis.jop_entanglement_energy_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.jop_entanglement_energy_bound

/-- info: 'FormalResearch.MatrixAnalysis.jop_fermion_product_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.jop_fermion_product_bound

/-- info: 'FormalResearch.MatrixAnalysis.jop_fermion_compression_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.jop_fermion_compression_bound

/-- info: 'FormalResearch.MatrixAnalysis.jop_fermion_polar_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.jop_fermion_polar_bound

/-- info: 'FormalResearch.MatrixAnalysis.jop_fermion_eigenvalue_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.jop_fermion_eigenvalue_bound

/-- info: 'FormalResearch.MatrixAnalysis.jop_fermion_energy_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.jop_fermion_energy_bound


end FormalResearch.MatrixAnalysis
