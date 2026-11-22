module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbStableWeyl
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbStableMult

/-!
# Paper J, Theorem B, L3.D steps 1-3: the core of `cor:thb-stable` (pointwise, over `ℂ`)

Source: Paper J `thmB.tex`, Corollary `cor:thb-stable`, proof (after Bhatia--Davis--McIntosh, 1983): Weyl, the Schur
multiplier `f_gamma`, unit columns, the phase `Δ`.

Claim class: **proved** (no hypothesis beyond the stated ones, no new axiom).

## Proved here (axiom-pinned)

* `thb_stable_core`: let `J, J'` be Hermitian with unitary eigenvector matrices `U, U'` (`J U = U diag X`,
  `J' U' = U' diag X'`), `|X_j - X'_k| ≥ γ/2` for `j ≠ k`, `|X_k - X'_k| ≤ γ/4`, `‖J - J'‖ ≤ ε`, and `η := c_f ε/γ ≤ 1/2`.
  Then `V = U^* U'` has non-zero diagonal and the diagonal unitary `Δ_k = |V_kk|/V_kk` satisfies `‖U' Δ - U‖ ≤ 2 η`.
  Steps: `sylvester_entry` (`Λ V - V Λ' = E`), `offdiag_eq_hadamard` (`V - diag V = (f_γ(X_j - X'_k) E_jk)`), `offdiag_norm_le`
  (`‖V - diag V‖ ≤ η`, from `ThbStableMult.thb_multiplier_bound`), `diag_sq_lower` (`|V_kk|² ≥ 1 - η²`), the phase estimate
  `‖VΔ - 1‖ ≤ 2η`.
* `thbEig_eq_of_eigSystem`: an antitone eigenvalue list of a unitary diagonalisation is `thbEig`
  (Mathlib's sorted list), through the characteristic polynomial; `exists_eigSystem_thbEig`: a Hermitian matrix has a
  unitary eigenvector matrix with the eigenvalues `thbEig` in this order.
* `thb_stable_pointwise`: with `8 ε ≤ γ` and consecutive gaps `X_i - X_{i+1} ≥ γ` the data `|X_j - X'_k| ≥ γ/2` and
  `|X_k - X'_k| ≤ γ/4` come from Weyl's inequality (`ThbStableWeyl.lean`), the perturbed eigenvalues are simple
  (`StrictAnti X'`), and the conclusion of `thb_stable_core` holds.
* `thbCf`: the absolute constant `c_f` (from `ThbStableMult.thb_multiplier_bound`); `norm_cplx`: the complexification of a
  real matrix has the same `L²` operator norm.

## Differences from the paper

* `c_f` is the constant of `ThbStableMult` (existence; not computed).  The conditions `8 ε ≤ γ` and `η ≤ 1/2` are those of
  the paper's choice of `h'_m`.
* The statement is pointwise (one matrix pair); the family statement with `h'_m(K)` is `ThbStable.lean`.

## Not formalised

The Jacobi gauge `Δ = I` (`ThbStableGauge.lean`) and the family statement (`ThbStable.lean`).
-/

@[expose] public section

open MeasureTheory Complex Matrix
open scoped Matrix.Norms.L2Operator

namespace FormalResearch.JacobiEigenvectors.TheoremB

section Complexification

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- the complexification of a real matrix -/
abbrev cplx (A : Matrix n n ℝ) : Matrix n n ℂ := A.map (fun x => (x : ℂ))

lemma cplx_mulVec_re_im (A : Matrix n n ℝ) (z : n → ℂ) (i : n) :
    ((cplx A) *ᵥ z) i = (((A *ᵥ fun j => (z j).re) i : ℝ) : ℂ) +
      (((A *ᵥ fun j => (z j).im) i : ℝ) : ℂ) * Complex.I := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.ofReal_sum]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  conv_lhs => rw [← Complex.re_add_im (z j)]
  ring

lemma norm_cplx_le (A : Matrix n n ℝ) : ‖cplx A‖ ≤ ‖A‖ := by
  rw [Matrix.l2_opNorm_def, ContinuousLinearMap.opNorm_le_iff (norm_nonneg _)]
  intro z
  have hz : ‖z‖ ^ 2 = ‖(WithLp.toLp 2 (fun j => (z j).re) : EuclideanSpace ℝ n)‖ ^ 2 +
      ‖(WithLp.toLp 2 (fun j => (z j).im) : EuclideanSpace ℝ n)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  have himg : ‖((toEuclideanLin (𝕜 := ℂ) (m := n) (n := n)).trans LinearMap.toContinuousLinearMap (cplx A)) z‖ ^ 2 =
      ‖(WithLp.toLp 2 (A *ᵥ fun j => (z j).re) : EuclideanSpace ℝ n)‖ ^ 2 +
      ‖(WithLp.toLp 2 (A *ᵥ fun j => (z j).im) : EuclideanSpace ℝ n)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := cplx_mulVec_re_im A z i
    have e : ((toEuclideanLin (𝕜 := ℂ) (m := n) (n := n)).trans LinearMap.toContinuousLinearMap (cplx A) z).ofLp i
        = (cplx A *ᵥ z.ofLp) i := rfl
    rw [e, this]
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hr := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 (fun j => (z j).re))
  have hi := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 (fun j => (z j).im))
  have hAn : 0 ≤ ‖A‖ := norm_nonneg _
  have h1 : ‖(WithLp.toLp 2 (A *ᵥ fun j => (z j).re) : EuclideanSpace ℝ n)‖ ^ 2 ≤
      ‖A‖ ^ 2 * ‖(WithLp.toLp 2 (fun j => (z j).re) : EuclideanSpace ℝ n)‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hr 2
  have h2 : ‖(WithLp.toLp 2 (A *ᵥ fun j => (z j).im) : EuclideanSpace ℝ n)‖ ^ 2 ≤
      ‖A‖ ^ 2 * ‖(WithLp.toLp 2 (fun j => (z j).im) : EuclideanSpace ℝ n)‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hi 2
  have h3 : ‖((toEuclideanLin (𝕜 := ℂ) (m := n) (n := n)).trans LinearMap.toContinuousLinearMap (cplx A)) z‖ ^ 2 ≤
      (‖A‖ * ‖z‖) ^ 2 := by
    rw [himg, mul_pow, hz]; nlinarith
  exact le_of_sq_le_sq (by simpa using h3) (mul_nonneg hAn (norm_nonneg _))


lemma cplx_mulVec_ofReal (A : Matrix n n ℝ) (x : n → ℝ) (i : n) :
    ((cplx A) *ᵥ fun j => ((x j : ℝ) : ℂ)) i = (((A *ᵥ x) i : ℝ) : ℂ) := by
  simp [Matrix.mulVec, dotProduct]

lemma norm_le_norm_cplx (A : Matrix n n ℝ) : ‖A‖ ≤ ‖cplx A‖ := by
  rw [Matrix.l2_opNorm_def, ContinuousLinearMap.opNorm_le_iff (norm_nonneg _)]
  intro x
  have h : ‖(WithLp.toLp 2 (cplx A *ᵥ fun j => ((x j : ℝ) : ℂ)) : EuclideanSpace ℂ n)‖ ≤
      ‖cplx A‖ * ‖(WithLp.toLp 2 (fun j => ((x j : ℝ) : ℂ)) : EuclideanSpace ℂ n)‖ :=
    Matrix.l2_opNorm_mulVec (cplx A) (WithLp.toLp 2 (fun j => ((x j : ℝ) : ℂ)))
  have e1 : ‖(WithLp.toLp 2 (fun j => ((x j : ℝ) : ℂ)) : EuclideanSpace ℂ n)‖ = ‖x‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp
  have e2 : ‖(WithLp.toLp 2 (cplx A *ᵥ fun j => ((x j : ℝ) : ℂ)) : EuclideanSpace ℂ n)‖ =
      ‖((toEuclideanLin (𝕜 := ℝ) (m := n) (n := n)).trans LinearMap.toContinuousLinearMap A) x‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : ((toEuclideanLin (𝕜 := ℝ) (m := n) (n := n)).trans LinearMap.toContinuousLinearMap A x).ofLp i
        = (A *ᵥ x.ofLp) i := rfl
    rw [e]
    have := cplx_mulVec_ofReal A x.ofLp i
    simp only [WithLp.ofLp_toLp]
    rw [this]
    simp
  rw [e1, e2] at h
  exact h

lemma norm_cplx (A : Matrix n n ℝ) : ‖cplx A‖ = ‖A‖ :=
  le_antisymm (norm_cplx_le A) (norm_le_norm_cplx A)


end Complexification

variable {N : ℕ}


/-- shorthand -/
abbrev CMat (N : ℕ) := Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ

/-- a unitary has operator norm one -/
lemma norm_unitary_eq_one {U : CMat N} (hU : Uᴴ * U = 1) : ‖U‖ = 1 := by
  have hU' : U ∈ Matrix.unitaryGroup (Fin (N + 1)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    exact mul_eq_one_comm.1 hU
  exact CStarRing.norm_of_mem_unitary hU'

lemma norm_conjTranspose_unitary {U : CMat N} (hU : Uᴴ * U = 1) : ‖Uᴴ‖ = 1 := by
  rw [Matrix.l2_opNorm_conjTranspose]; exact norm_unitary_eq_one hU

/-- `‖M e_k‖₂ ≤ ‖M‖` in the form `Σ_j ‖M j k‖² ≤ ‖M‖²`. -/
lemma sum_sq_col_le (M : CMat N) (k : Fin (N + 1)) :
    ∑ j, ‖M j k‖ ^ 2 ≤ ‖M‖ ^ 2 := by
  have h := Matrix.l2_opNorm_mulVec M (WithLp.toLp 2 (Pi.single k (1:ℂ)))
  have e1 : ‖(WithLp.toLp 2 (Pi.single k (1:ℂ)) : EuclideanSpace ℂ (Fin (N + 1)))‖ = 1 := by
    simp [EuclideanSpace.norm_eq]
  rw [e1, mul_one] at h
  have e2 : ‖(WithLp.toLp 2 (M *ᵥ Pi.single k (1:ℂ)) : EuclideanSpace ℂ (Fin (N + 1)))‖ ^ 2 =
      ∑ j, ‖M j k‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.mulVec_single_one]
  rw [← e2]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2


open ThbMult in
/-- The Sylvester identity `Λ V - V Λ' = E` entrywise: `(X_j - X'_k) V_jk = E_jk`. -/
lemma sylvester_entry {J J' U U' : CMat N} {X X' : Fin (N + 1) → ℝ}
    (hJ : J.IsHermitian) (hU : Uᴴ * U = 1)
    (hX : J * U = U * diagonal (fun k => (X k : ℂ)))
    (hX' : J' * U' = U' * diagonal (fun k => (X' k : ℂ))) (j k : Fin (N + 1)) :
    (Uᴴ * (J - J') * U') j k = ((X j - X' k : ℝ) : ℂ) * (Uᴴ * U') j k := by
  have h1 : Uᴴ * J = diagonal (fun k => (X k : ℂ)) * Uᴴ := by
    have := congrArg Matrix.conjTranspose hX
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ.eq, Matrix.diagonal_conjTranspose] at this
    have hs : (star fun k => (X k : ℂ)) = fun k => (X k : ℂ) := by funext k; simp
    rw [hs] at this
    exact this
  have h2 : Uᴴ * (J - J') * U' = diagonal (fun k => (X k : ℂ)) * (Uᴴ * U') -
      (Uᴴ * U') * diagonal (fun k => (X' k : ℂ)) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, h1, Matrix.mul_assoc Uᴴ J' U', hX',
      ← Matrix.mul_assoc, Matrix.mul_assoc]
  rw [h2, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  push_cast
  ring

lemma V_unitary {U U' : CMat N} (hU : Uᴴ * U = 1) (hU' : U'ᴴ * U' = 1) :
    (Uᴴ * U')ᴴ * (Uᴴ * U') = 1 := by
  have hUU : U * Uᴴ = 1 := mul_eq_one_comm.1 hU
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc U'ᴴ * U * (Uᴴ * U') = U'ᴴ * (U * Uᴴ) * U' := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hUU, Matrix.mul_one, hU']

open ThbMult in
/-- `V - diag V = (f_gamma(X_j - X'_k) E_jk)`. -/
lemma offdiag_eq_hadamard {J J' U U' : CMat N} {X X' : Fin (N + 1) → ℝ} {γ : ℝ}
    (hJ : J.IsHermitian) (hU : Uᴴ * U = 1)
    (hX : J * U = U * diagonal (fun k => (X k : ℂ)))
    (hX' : J' * U' = U' * diagonal (fun k => (X' k : ℂ))) (hγ : 0 < γ)
    (hsep : ∀ j k, j ≠ k → γ / 2 ≤ |X j - X' k|) (hdiag : ∀ k, |X k - X' k| ≤ γ / 4) :
    (Uᴴ * U') - diagonal (fun k => (Uᴴ * U') k k) =
      Matrix.of fun j k => fG γ (X j - X' k) * (Uᴴ * (J - J') * U') j k := by
  ext j k
  simp only [Matrix.sub_apply, Matrix.of_apply, Matrix.diagonal_apply]
  rw [sylvester_entry hJ hU hX hX' j k]
  by_cases hjk : j = k
  · subst hjk
    rw [fG_of_small hγ (hdiag j)]
    simp
  · simp only [hjk, ↓reduceIte]
    rw [fG_of_large hγ (hsep j k hjk)]
    have hne : ((X j - X' k : ℝ) : ℂ) ≠ 0 := by
      have := hsep j k hjk
      have h0 : X j - X' k ≠ 0 := by
        intro h; rw [h] at this; simp at this; linarith
      exact_mod_cast h0
    simp only [sub_zero]
    field_simp


/-- The absolute constant `c_f` of the Fourier--Schur multiplier `f_gamma` (`thb_multiplier_bound`). -/
noncomputable def thbCf : ℝ := Classical.choose ThbMult.thb_multiplier_bound

lemma thbCf_nonneg : 0 ≤ thbCf := (Classical.choose_spec ThbMult.thb_multiplier_bound).1

lemma thbCf_spec {γ : ℝ} (hγ : 0 < γ) {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ)
    (E : Matrix (Fin n) (Fin m) ℂ) :
    ‖Matrix.of fun j k => ThbMult.fG γ (x j - y k) * E j k‖ ≤ thbCf / γ * ‖E‖ :=
  (Classical.choose_spec ThbMult.thb_multiplier_bound).2 γ hγ x y E

/-- Each column of a unitary has squared norm `1`. -/
lemma sum_sq_col_unitary {V : CMat N} (hV : Vᴴ * V = 1) (k : Fin (N + 1)) :
    ∑ j, ‖V j k‖ ^ 2 = 1 := by
  have h := congrFun (congrFun hV k) k
  rw [Matrix.mul_apply] at h
  simp only [Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have h2 : ∑ j, ((‖V j k‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; rfl
  exact_mod_cast (by rw [← Complex.ofReal_sum] at h2; exact_mod_cast h2)

/-- Diagonal lower bound: `‖V_kk‖² ≥ 1 - η²` for a unitary `V` with `‖V - diag V‖ ≤ η`. -/
lemma diag_sq_lower {V : CMat N} (hV : Vᴴ * V = 1) {η : ℝ}
    (hM : ‖V - diagonal (fun k => V k k)‖ ≤ η) (k : Fin (N + 1)) :
    1 - η ^ 2 ≤ ‖V k k‖ ^ 2 := by
  set M := V - diagonal (fun k => V k k) with hMdef
  have h1 := sum_sq_col_unitary hV k
  have h2 := sum_sq_col_le M k
  have hMn : 0 ≤ ‖M‖ := norm_nonneg _
  have h3 : ∑ j, ‖V j k‖ ^ 2 = ∑ j, ‖M j k‖ ^ 2 + ‖V k k‖ ^ 2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k), ← Finset.sum_erase_add (Finset.univ) (fun j => ‖M j k‖ ^ 2) (Finset.mem_univ k)]
    have : ∑ j ∈ Finset.univ.erase k, ‖V j k‖ ^ 2 = ∑ j ∈ Finset.univ.erase k, ‖M j k‖ ^ 2 := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk : j ≠ k := Finset.ne_of_mem_erase hj
      simp [hMdef, Matrix.diagonal_apply, hjk]
    rw [this]
    simp [hMdef]
  have : ‖M‖ ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hMn hM 2
  linarith


open ThbMult in
/-- **The Schur-multiplier step**: `‖V - diag V‖ ≤ c_f ε / γ`. -/
lemma offdiag_norm_le {J J' U U' : CMat N} {X X' : Fin (N + 1) → ℝ} {γ ε : ℝ}
    (hJ : J.IsHermitian) (hU : Uᴴ * U = 1) (hU' : U'ᴴ * U' = 1)
    (hX : J * U = U * diagonal (fun k => (X k : ℂ)))
    (hX' : J' * U' = U' * diagonal (fun k => (X' k : ℂ))) (hγ : 0 < γ)
    (hsep : ∀ j k, j ≠ k → γ / 2 ≤ |X j - X' k|) (hdiag : ∀ k, |X k - X' k| ≤ γ / 4)
    (hε : ‖J - J'‖ ≤ ε) :
    ‖(Uᴴ * U') - diagonal (fun k => (Uᴴ * U') k k)‖ ≤ thbCf / γ * ε := by
  rw [offdiag_eq_hadamard hJ hU hX hX' hγ hsep hdiag]
  refine (thbCf_spec hγ X X' _).trans ?_
  have hE : ‖Uᴴ * (J - J') * U'‖ ≤ ε := by
    calc ‖Uᴴ * (J - J') * U'‖ ≤ ‖Uᴴ * (J - J')‖ * ‖U'‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖Uᴴ‖ * ‖J - J'‖) * ‖U'‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
      _ = ‖J - J'‖ := by rw [norm_conjTranspose_unitary hU, norm_unitary_eq_one hU']; ring
      _ ≤ ε := hε
  have : 0 ≤ thbCf / γ := div_nonneg thbCf_nonneg hγ.le
  exact mul_le_mul_of_nonneg_left hE this

open ThbMult in
/-- **Core of `cor:thb-stable`** (Paper J, `thmB.tex`, proof of `cor:thb-stable`, steps 2--3).
Let `J, J'` be Hermitian with unitary eigenvector matrices `U, U'` (`J U = U diag X`, `J' U' = U' diag X'`),
`|X_j - X'_k| >= γ/2` for `j ≠ k` and `|X_k - X'_k| <= γ/4`, `‖J - J'‖ <= ε`, and `η := c_f ε / γ <= 1/2`.  Then the
diagonal unitary `Δ_k = |V_kk| / V_kk`, `V = U^* U'`, satisfies `‖U' Δ - U‖ <= 2 η`. -/
theorem thb_stable_core {J J' U U' : CMat N} {X X' : Fin (N + 1) → ℝ} {γ ε : ℝ}
    (hJ : J.IsHermitian) (hU : Uᴴ * U = 1) (hU' : U'ᴴ * U' = 1)
    (hX : J * U = U * diagonal (fun k => (X k : ℂ)))
    (hX' : J' * U' = U' * diagonal (fun k => (X' k : ℂ))) (hγ : 0 < γ)
    (hsep : ∀ j k, j ≠ k → γ / 2 ≤ |X j - X' k|) (hdiag : ∀ k, |X k - X' k| ≤ γ / 4)
    (hε : ‖J - J'‖ ≤ ε) (hη : thbCf / γ * ε ≤ 1 / 2) :
    (∀ k, (Uᴴ * U') k k ≠ 0) ∧
    ‖U' * diagonal (fun k => ((‖(Uᴴ * U') k k‖ : ℝ) : ℂ) / (Uᴴ * U') k k) - U‖ ≤ 2 * (thbCf / γ * ε) := by
  set V := Uᴴ * U' with hVdef
  set η := thbCf / γ * ε with hηdef
  have hη0 : 0 ≤ η := by
    have : 0 ≤ ε := (norm_nonneg _).trans hε
    exact mul_nonneg (div_nonneg thbCf_nonneg hγ.le) this
  have hVu : Vᴴ * V = 1 := V_unitary hU hU'
  have hM : ‖V - diagonal (fun k => V k k)‖ ≤ η := offdiag_norm_le hJ hU hU' hX hX' hγ hsep hdiag hε
  have hlow := diag_sq_lower hVu hM
  have hVne : ∀ k, V k k ≠ 0 := by
    intro k h0
    have := hlow k
    rw [h0] at this
    simp at this
    rw [abs_of_nonneg hη0] at this
    nlinarith
  refine ⟨hVne, ?_⟩
  -- the phase
  set Δ : Fin (N + 1) → ℂ := fun k => ((‖V k k‖ : ℝ) : ℂ) / V k k with hΔ
  have hΔn : ∀ k, ‖Δ k‖ = 1 := by
    intro k
    have : ‖V k k‖ ≠ 0 := norm_ne_zero_iff.2 (hVne k)
    simp [hΔ, norm_div, this]
  have hΔdiag : ‖(diagonal Δ : CMat N)‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => (hΔn k).le
  have hVk1 : ∀ k, ‖V k k‖ ≤ 1 := by
    intro k
    have h1 := sum_sq_col_unitary hVu k
    have h2 : ‖V k k‖ ^ 2 ≤ ∑ j, ‖V j k‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖V j k‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ k)
    nlinarith [norm_nonneg (V k k)]
  have hVk2 : ∀ k, 1 - η ≤ ‖V k k‖ := by
    intro k
    by_contra hcon
    push Not at hcon
    have h1 : ‖V k k‖ ^ 2 < (1 - η) ^ 2 := by
      have := norm_nonneg (V k k)
      nlinarith
    have := hlow k
    nlinarith
  -- W = V Δ - 1
  have hW : V * diagonal Δ - 1 = (V - diagonal (fun k => V k k)) * diagonal Δ +
      diagonal (fun k => ((‖V k k‖ : ℝ) : ℂ) - 1) := by
    have e1 : V * diagonal Δ = (V - diagonal (fun k => V k k)) * diagonal Δ +
        diagonal (fun k => ((‖V k k‖ : ℝ) : ℂ)) := by
      rw [Matrix.sub_mul, Matrix.diagonal_mul_diagonal]
      have : (fun k => V k k * Δ k) = fun k => ((‖V k k‖ : ℝ) : ℂ) := by
        funext k; simp only [hΔ]; field_simp [hVne k]
      rw [this]; abel
    rw [e1, ← Matrix.diagonal_one]
    have : (diagonal fun k => ((‖V k k‖ : ℝ) : ℂ)) - (diagonal fun _ : Fin (N + 1) => (1 : ℂ)) =
        diagonal (fun k => ((‖V k k‖ : ℝ) : ℂ) - 1) := by
      rw [← Matrix.diagonal_sub]
    rw [add_sub_assoc, this]
  have hD : ‖(diagonal (fun k => ((‖V k k‖ : ℝ) : ℂ) - 1) : CMat N)‖ ≤ η := by
    rw [Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg hη0).2 fun k => ?_
    have : ((‖V k k‖ : ℝ) : ℂ) - 1 = ((‖V k k‖ - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hVk1 k, hVk2 k]
  have hWn : ‖V * diagonal Δ - 1‖ ≤ 2 * η := by
    rw [hW]
    refine (norm_add_le _ _).trans ?_
    have : ‖(V - diagonal (fun k => V k k)) * diagonal Δ‖ ≤ η :=
      (Matrix.l2_opNorm_mul _ _).trans (by
        calc ‖V - diagonal (fun k => V k k)‖ * ‖(diagonal Δ : CMat N)‖
            ≤ η * 1 := mul_le_mul hM hΔdiag (norm_nonneg _) hη0
          _ = η := mul_one η)
    linarith
  -- U' Δ - U = U (V Δ - 1)
  have hUU : U * Uᴴ = 1 := mul_eq_one_comm.1 hU
  have hkey : U' * diagonal Δ - U = U * (V * diagonal Δ - 1) := by
    rw [Matrix.mul_sub, Matrix.mul_one, hVdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU,
      Matrix.one_mul]
  rw [hkey]
  calc ‖U * (V * diagonal Δ - 1)‖ ≤ ‖U‖ * ‖V * diagonal Δ - 1‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ 1 * (2 * η) := by rw [norm_unitary_eq_one hU]; exact mul_le_mul_of_nonneg_left hWn zero_le_one
    _ = 2 * η := one_mul _


section Sorting
open Polynomial


lemma charpoly_eq_of_eigSystem {J U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} (hU : Uᴴ * U = 1)
    {X : Fin (N + 1) → ℝ} (hX : J * U = U * diagonal (fun k => (X k : ℂ))) :
    J.charpoly = ∏ k, (Polynomial.X - Polynomial.C (X k : ℂ)) := by
  have hUU : U * Uᴴ = 1 := mul_eq_one_comm.1 hU
  have hJ : J = U * (diagonal (fun k => (X k : ℂ)) * Uᴴ) := by
    rw [← Matrix.mul_assoc, ← hX, Matrix.mul_assoc, hUU, Matrix.mul_one]
  rw [hJ, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hU, Matrix.mul_one, Matrix.charpoly_diagonal]

/-- An antitone eigenvalue listing of a unitary diagonalisation is Mathlib's sorted list `eigenvalues₀`. -/
theorem thbEig_eq_of_eigSystem {J U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} (hJ : J.IsHermitian)
    (hU : Uᴴ * U = 1) {X : Fin (N + 1) → ℝ}
    (hX : J * U = U * diagonal (fun k => (X k : ℂ))) (hA : Antitone X) (k : Fin (N + 1)) :
    X k = thbEig hJ k := by
  have hc := charpoly_eq_of_eigSystem hU hX
  have hroots : J.charpoly.roots = Multiset.map (RCLike.ofReal ∘ X) Finset.univ.val := by
    rw [hc, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have h1 := hJ.sort_roots_charpoly_eq_eigenvalues₀
  rw [hroots] at h1
  have h2 : List.ofFn X = List.ofFn hJ.eigenvalues₀ := by
    rw [← h1]
    simp_rw [Fin.univ_val_map, Multiset.map_coe, List.map_ofFn, Function.comp_def, RCLike.ofReal_re,
      Multiset.coe_sort]
    symm
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hA.sortedGE_ofFn
  have h3 := congrArg (fun l => l[k.val]?) h2
  simp only [List.getElem?_ofFn] at h3
  unfold thbEig
  simp [k.isLt] at h3
  exact h3


end Sorting


/-- Every Hermitian matrix has a unitary eigenvector matrix with the eigenvalues in decreasing order `thbEig`. -/
theorem exists_eigSystem_thbEig {A : CMat N} (hA : A.IsHermitian) :
    ∃ W : CMat N, Wᴴ * W = 1 ∧ A * W = W * diagonal (fun k => (thbEig hA k : ℂ)) := by
  set e : Fin (Fintype.card (Fin (N + 1))) ≃ Fin (N + 1) := Fintype.equivOfCardEq (Fintype.card_fin _) with he
  set σ : Fin (N + 1) → Fin (N + 1) := fun k => e (Fin.cast (Fintype.card_fin (N + 1)).symm k) with hσ
  have hσinj : Function.Injective σ := by
    intro a b h
    have := e.injective h
    exact (Fin.cast_injective _) this
  have hval : ∀ k, hA.eigenvalues (σ k) = thbEig hA k := by
    intro k
    simp [Matrix.IsHermitian.eigenvalues, hσ, thbEig, he]
  set U : CMat N := (hA.eigenvectorUnitary : CMat N) with hU
  have hUU : Uᴴ * U = 1 := by
    have := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose] at this
  have hAU : A * U = U * diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
    have h := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at h
    simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] at h
    have hUU' : U * Uᴴ = 1 := mul_eq_one_comm.1 hUU
    calc A * U = U * (Uᴴ * A * U) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU', Matrix.one_mul]
      _ = _ := by rw [h]; rfl
  refine ⟨U.submatrix id σ, ?_, ?_⟩
  · ext k l
    have := congrFun (congrFun hUU (σ k)) (σ l)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id,
      Matrix.one_apply] at this ⊢
    rw [this]
    simp [hσinj.eq_iff]
  · ext i k
    have := congrFun (congrFun hAU i) (σ k)
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.diagonal_apply] at this ⊢
    rw [this]
    simp [hval k]


/-- Weyl + gaps: the data `hsep`, `hdiag` of `thb_stable_core`, and simplicity of the perturbed spectrum. -/
theorem thb_stable_pointwise {J J' U U' : CMat N} {X X' : Fin (N + 1) → ℝ} {γ ε : ℝ}
    (hJ : J.IsHermitian) (hJ' : J'.IsHermitian) (hU : Uᴴ * U = 1) (hU' : U'ᴴ * U' = 1)
    (hX : J * U = U * diagonal (fun k => (X k : ℂ)))
    (hX' : J' * U' = U' * diagonal (fun k => (X' k : ℂ))) (hXa : Antitone X) (hXa' : Antitone X')
    (hγ : 0 < γ) (hcons : ∀ i j : Fin (N + 1), (j : ℕ) = (i : ℕ) + 1 → γ ≤ X i - X j)
    (hε : ‖J - J'‖ ≤ ε) (h8 : 8 * ε ≤ γ) (hη : thbCf / γ * ε ≤ 1 / 2) :
    StrictAnti X' ∧ (∀ k, (Uᴴ * U') k k ≠ 0) ∧
      ‖U' * diagonal (fun k => ((‖(Uᴴ * U') k k‖ : ℝ) : ℂ) / (Uᴴ * U') k k) - U‖ ≤
        2 * (thbCf / γ * ε) := by
  have hXe : ∀ k, X k = thbEig hJ k := thbEig_eq_of_eigSystem hJ hU hX hXa
  have hXe' : ∀ k, X' k = thbEig hJ' k := thbEig_eq_of_eigSystem hJ' hU' hX' hXa'
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have hcons' : ∀ (i : ℕ) (hi : i + 1 < N + 1),
      γ ≤ thbEig hJ ⟨i, by omega⟩ - thbEig hJ ⟨i + 1, hi⟩ := by
    intro i hi
    rw [← hXe, ← hXe]
    exact hcons ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl
  have hgap : ∀ j k : Fin (N + 1), j ≠ k → γ ≤ |thbEig hJ j - thbEig hJ k| := by
    intro j k hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · have := thb_gap_of_consecutive hJ hcons' h
      rw [abs_of_nonneg (by linarith [thbEig_antitone hJ h.le])]
      exact this
    · have := thb_gap_of_consecutive hJ hcons' h
      rw [abs_sub_comm, abs_of_nonneg (by linarith [thbEig_antitone hJ h.le])]
      exact this
  have hsep : ∀ j k, j ≠ k → γ / 2 ≤ |X j - X' k| := by
    intro j k hjk
    rw [hXe, hXe']
    have := thb_weyl_separated hJ hJ' (hgap j k hjk)
    linarith
  have hdiag : ∀ k, |X k - X' k| ≤ γ / 4 := by
    intro k
    rw [hXe, hXe']
    have := thb_weyl_abs_sub_le hJ hJ' k
    linarith
  refine ⟨?_, thb_stable_core hJ hU hU' hX hX' hγ hsep hdiag hε hη⟩
  intro i j hij
  refine lt_of_le_of_ne (hXa' hij.le) ?_
  rw [hXe', hXe']
  intro h
  exact thb_weyl_ne_of_gap hJ hJ' (hgap i j hij.ne) (by linarith) h.symm


end FormalResearch.JacobiEigenvectors.TheoremB

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.thb_stable_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.thb_stable_core

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.thb_stable_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.thb_stable_pointwise

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.thbEig_eq_of_eigSystem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.thbEig_eq_of_eigSystem

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.exists_eigSystem_thbEig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.exists_eigSystem_thbEig

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.norm_cplx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.norm_cplx
