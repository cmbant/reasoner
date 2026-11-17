module

public import FormalResearch.Jacobi.Interlacing

/-!
# Sturm oscillation for irreducible Jacobi matrices (Weyl P5, Theorem SP / (SP.1))

For a real symmetric Jacobi matrix `J = J_n` with nonzero off-diagonals `a_0, …, a_{n-2}`:

* `jacobi_cauchy_interlacing` : the eigenvalues of the leading `m × m` block strictly interlace those
  of the `(m+1) × (m+1)` block, and both spectra are simple (all eigenvalues are listed as strictly
  increasing `Fin`-families);
* `jacobi_oscillation` : **(SP.1)** if `λ` is an eigenvalue of `J_{m+1}` with exactly `k` eigenvalues
  strictly below it (the `k`-th eigenvalue in ascending order, 0-indexed) and `v` is an eigenvector,
  then both end components are nonzero and
  `sgn (v_m / v_0) = (-1)^{m-k} ∏_{j<m} sgn a_j`
  (stated multiplicatively as `0 < (-1)^{m-k} (∏ a_j) v_m v_0`, and in sign form as
  `jacobi_oscillation_sign`).

Source: `Weyl/P5/notes/dirichlet_block_audit.md`, Theorem SP, eq. (SP.1) (PR 250, head `cfad461d2`),
and its proof ("write `P_j` for the leading `j × j` principal matrix ... `u_j/u_0 = P_j(λ_k)/∏ a_i`;
strict Jacobi interlacing ...").  Claim class: proved (from the recurrence; no Cauchy interlacing
theorem is used).

Not formalised: the physical instantiation (SP.2: the Racah matrix has `sgn U_{a_0 d} =
(-1)^{z_0+d-d_0}` by R0(d), hence the `d`-independent sign of the second endpoint row); that is an
input about the `6j` symbols, not a statement about generic Jacobi matrices.  Also not formalised: the
nodal (sign-change count) form of Sturm oscillation, and the identification of `k` (here
`#{eigenvalues < λ}`, via `Set.ncard`) with the index in Mathlib's sorted
`Matrix.IsHermitian.eigenvalues₀`.
-/

@[expose] public section

namespace FormalResearch.Jacobi

open Polynomial Finset Matrix

section Spectrum

variable {b a : ℕ → ℝ}

theorem rootSeq_eval_eq_zero_iff {p : ℝ[X]} {m : ℕ} {θ : ℕ → ℝ} (h : RootSeq p m θ) (x : ℝ) :
    p.eval x = 0 ↔ ∃ i, i < m ∧ θ i = x := by
  rw [h, eval_prod, prod_eq_zero_iff]
  simp only [mem_range, eval_sub, eval_X, eval_C, sub_eq_zero]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, h.symm⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, h.symm⟩

/-- **Cauchy interlacing for Jacobi matrices with nonzero links.**  The spectra of `J_m` and
`J_{m+1}` are simple, and `θ_0 < μ_0 < θ_1 < ⋯ < μ_{m-1} < θ_m`. -/
theorem jacobi_cauchy_interlacing (m : ℕ) (ha : ∀ j, j < m → a j ≠ 0) :
    ∃ (μ : Fin m → ℝ) (θ : Fin (m + 1) → ℝ),
      (∀ k : Fin m, θ k.castSucc < μ k ∧ μ k < θ k.succ) ∧
      (∀ x, IsEigenval (jacobiMatrix m b a) x ↔ ∃ i, μ i = x) ∧
      (∀ x, IsEigenval (jacobiMatrix (m + 1) b a) x ↔ ∃ i, θ i = x) := by
  obtain ⟨μ, θ, hμ, hθ, hI⟩ := jacP_interlacing b a m ha
  refine ⟨fun i => μ i, fun i => θ i, fun k => hI k k.2, ?_, ?_⟩
  · intro x
    rw [jacobi_isEigenval_iff (fun j hj => ha j (by omega)), rootSeq_eval_eq_zero_iff hμ]
    exact ⟨fun ⟨i, hi, h⟩ => ⟨⟨i, hi⟩, h⟩, fun ⟨i, h⟩ => ⟨i, i.2, h⟩⟩
  · intro x
    rw [jacobi_isEigenval_iff (fun j hj => ha j (by omega)), rootSeq_eval_eq_zero_iff hθ]
    exact ⟨fun ⟨i, hi, h⟩ => ⟨⟨i, hi⟩, h⟩, fun ⟨i, h⟩ => ⟨i, i.2, h⟩⟩

/-- **(SP.1), multiplicative form.**  Let `λ` be an eigenvalue of `J_{m+1}` (nonzero links) having
exactly `k` eigenvalues strictly below it, and `v` an eigenvector.  Then `v_0 ≠ 0`, `v_m ≠ 0` and
`(-1)^{m-k} (∏_{j<m} a_j) v_m v_0 > 0`. -/
theorem jacobi_oscillation (m : ℕ) (ha : ∀ j, j < m → a j ≠ 0) {lam : ℝ} {k : ℕ}
    (hk : {x : ℝ | IsEigenval (jacobiMatrix (m + 1) b a) x ∧ x < lam}.ncard = k)
    {v : Fin (m + 1) → ℝ} (hv0 : v ≠ 0) (hv : jacobiMatrix (m + 1) b a *ᵥ v = lam • v) :
    v 0 ≠ 0 ∧ v (Fin.last m) ≠ 0 ∧
      0 < (-1 : ℝ) ^ (m - k) * (∏ j ∈ range m, a j) * (v (Fin.last m) * v 0) := by
  obtain ⟨μ, θ, hμ, hθ, hI⟩ := jacP_interlacing b a m ha
  have haN : ∀ j, j + 1 < m + 1 → a j ≠ 0 := fun j hj => ha j (by omega)
  have hroot : (jacP b a (m + 1)).eval lam = 0 := eval_jacP_eq_zero_of_eigen haN hv hv0
  obtain ⟨k0, hk0, hθk0⟩ := (rootSeq_eval_eq_zero_iff hθ lam).mp hroot
  -- the eigenvalues below `λ = θ_{k0}` are `θ_0, …, θ_{k0 - 1}`
  have hset : {x : ℝ | IsEigenval (jacobiMatrix (m + 1) b a) x ∧ x < lam} =
      ↑((range k0).image θ) := by
    ext x
    simp only [Set.mem_ofPred_eq, coe_image, coe_range, Set.mem_image, Set.mem_Iio]
    rw [jacobi_isEigenval_iff haN, rootSeq_eval_eq_zero_iff hθ]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hlt⟩
      refine ⟨i, ?_, rfl⟩
      by_contra hge
      have := hI.theta_mono (by omega : k0 ≤ i) (by omega)
      linarith
    · rintro ⟨i, hi, rfl⟩
      refine ⟨⟨i, by omega, rfl⟩, ?_⟩
      rw [← hθk0]
      exact hI.theta_strictMono hi (by omega)
  have hinj : Set.InjOn θ (range k0 : Finset ℕ) := by
    intro i hi j hj hij
    have hi' := mem_range.mp (mem_coe.mp hi)
    have hj' := mem_range.mp (mem_coe.mp hj)
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hI.theta_strictMono hlt (by omega); linarith
    · have := hI.theta_strictMono hlt (by omega); linarith
  have hkk : k0 = k := by
    rw [hset, Set.ncard_coe_finset, card_image_of_injOn hinj, card_range] at hk
    exact hk
  subst hkk
  -- sign of `P_m(λ)`
  have hsign := hI.sign_prod (by omega : k0 ≤ m)
  have hPm : (jacP b a m).eval lam = ∏ i ∈ range m, (θ k0 - μ i) := by
    rw [hμ, eval_prod, hθk0]; simp
  rw [← hPm] at hsign
  -- the recurrence identity at `j = m`
  have hprod := eigen_prod_eq (m + 1) b a (extVec v) lam (eigenvec_row hv) m (by omega)
  rw [extVec_of_lt v (by omega : m < m + 1), extVec_of_lt v (by omega : 0 < m + 1)] at hprod
  have hf : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := rfl
  have h00 : (⟨0, by omega⟩ : Fin (m + 1)) = 0 := rfl
  rw [hf, h00] at hprod
  have h0 : v 0 ≠ 0 := by
    have := eigenvec_zero_ne haN hv hv0
    rwa [extVec_of_lt v (by omega : 0 < m + 1)] at this
  have hP : ∏ i ∈ range m, a i ≠ 0 := prod_ne_zero_of_links haN (by omega)
  have hPmne : (jacP b a m).eval lam ≠ 0 := by
    intro h; rw [h] at hsign; simp at hsign
  refine ⟨h0, ?_, ?_⟩
  · intro h
    rw [h, zero_mul] at hprod
    exact mul_ne_zero h0 hPmne hprod.symm
  · have : (-1 : ℝ) ^ (m - k0) * (∏ j ∈ range m, a j) * (v (Fin.last m) * v 0) =
        v 0 ^ 2 * ((-1 : ℝ) ^ (m - k0) * (jacP b a m).eval lam) := by
      have e : v (Fin.last m) * ∏ i ∈ range m, a i = v 0 * (jacP b a m).eval lam := hprod
      linear_combination ((-1 : ℝ) ^ (m - k0) * v 0) * e
    rw [this]
    exact mul_pos (by positivity) hsign

theorem signType_aux : ∀ c p z w : SignType, c * p * (z * w) = 1 → z * w = c * p := by
  decide +revert

/-- **(SP.1), sign form**: `sgn (v_m / v_0) = (-1)^{m-k} ∏_{j<m} sgn a_j`. -/
theorem jacobi_oscillation_sign (m : ℕ) (ha : ∀ j, j < m → a j ≠ 0) {lam : ℝ} {k : ℕ}
    (hk : {x : ℝ | IsEigenval (jacobiMatrix (m + 1) b a) x ∧ x < lam}.ncard = k)
    {v : Fin (m + 1) → ℝ} (hv0 : v ≠ 0) (hv : jacobiMatrix (m + 1) b a *ᵥ v = lam • v) :
    SignType.sign (v (Fin.last m) / v 0) =
      (-1 : SignType) ^ (m - k) * ∏ j ∈ range m, SignType.sign (a j) := by
  obtain ⟨h0, hl, hpos⟩ := jacobi_oscillation m ha hk hv0 hv
  have h1 : SignType.sign ((-1 : ℝ) ^ (m - k) * (∏ j ∈ range m, a j) * (v (Fin.last m) * v 0)) = 1 :=
    sign_eq_one_iff.mpr hpos
  have hprodsign : SignType.sign (∏ j ∈ range m, a j) = ∏ j ∈ range m, SignType.sign (a j) :=
    map_prod (signHom (α := ℝ)) a (range m)
  rw [sign_mul, sign_mul, sign_mul, sign_pow, hprodsign] at h1
  have hneg : SignType.sign (-1 : ℝ) = -1 := sign_neg (by norm_num)
  rw [hneg] at h1
  have hdiv : SignType.sign (v (Fin.last m) / v 0) =
      SignType.sign (v (Fin.last m)) * SignType.sign (v 0) := by
    rw [div_eq_mul_inv, sign_mul]
    congr 1
    rcases lt_or_gt_of_ne h0 with h | h
    · rw [sign_neg h, sign_neg (inv_lt_zero.mpr h)]
    · rw [sign_pos h, sign_pos (inv_pos.mpr h)]
  rw [hdiv]
  exact signType_aux _ _ _ _ h1

end Spectrum

/-- info: 'FormalResearch.Jacobi.jacobi_cauchy_interlacing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_cauchy_interlacing

/-- info: 'FormalResearch.Jacobi.jacobi_oscillation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_oscillation

/-- info: 'FormalResearch.Jacobi.jacobi_oscillation_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_oscillation_sign

end FormalResearch.Jacobi
