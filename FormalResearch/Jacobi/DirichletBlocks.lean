module

public import FormalResearch.Jacobi.CombesThomas

/-!
# Theorem DB.1/DB.2: resolvent decay across spectrally separated Dirichlet blocks

Source: `Weyl/P5/notes/dirichlet_block_audit.md`, Theorem DB.1 (eqs. (DB.1), (DB.2)) (PR 250, head
`cfad461d2`), and `m7_review_and_open_gates.md` §C.

Let `H` be a real symmetric matrix with at most two nonzero off-diagonal entries per row, each of
modulus at most `M > 0` (a Jacobi matrix; `LocalBound H M`), `H u = λ u`.  For a block `I` (any finite
set of sites) with Dirichlet restriction `H_I` such that every eigenvalue `μ` of `H_I` satisfies
`|μ - λ| ≥ Δ > 0`, and any function `d : ι → ℕ` that vanishes at the *sources* (sites of `I` with a
nonzero bond to a site outside `I`) and is `1`-Lipschitz along bonds inside `I` (e.g. the lattice
distance to the set of sources), with `μ_I = log(1 + Δ/(4M))`:

* `dirichlet_coercive` : spectral separation `|μ - λ| ≥ Δ` for the eigenvalues of a symmetric `A`
  gives the coercive bound `Δ² ‖x‖² ≤ ‖(A - λ)x‖²` (spectral theorem).
* `db1` : **(DB.1)** `∑_{j∈I} e^{2 μ_I d(j)} u_j² ≤ (4/Δ²) ∑_{j∈I} f_j²`, with the boundary forcing
  `f_j = -∑_{k∉I} H_{jk} u_k` (for a Jacobi matrix `f_l = -H_{l,l-1}u_{l-1}`,
  `f_r += -H_{r,r+1}u_{r+1}`, exactly the note's forcing, including the singleton case).
* `db2` : **(DB.2)** for a family of pairwise disjoint blocks with gaps `Δ_I ≥ Δ_0`,
  `∑_I ∑_{j∈I} e^{2 μ_0 d_I(j)} u_j² ≤ 16 M² ‖u‖² / Δ_0²`, `μ_0 = log(1 + Δ_0/(4M))`.
* `jacobi_db1` / `jacobi_db2` : the Jacobi-matrix instances (`jacobiMatrix n b a`).

Claim class: proved.  The note's case of an interval without source (`u|_I = 0`) is the case `d`
arbitrary, `f = 0` of `db1`.  Not formalised: DB.3/DB.4 (the Racah corollary: `T`-dependent choice of
`Δ_0`, `L_T`, and the exact Racah spectrum bounds `M ≤ 5`, `n ≤ 5T/2`), which need the physical
`6j` input; the generic Frobenius form is `db3` below.
-/

@[expose] public section

namespace FormalResearch.Jacobi

open Matrix Finset Real

section Spectral

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Spectral separation implies coercivity of `A - λ` for a real symmetric matrix `A`. -/
theorem dirichlet_coercive {A : Matrix κ κ ℝ} (hA : A.IsHermitian) {lam Δ : ℝ} (hΔ : 0 ≤ Δ)
    (h : ∀ μ, IsEigenval A μ → Δ ≤ |μ - lam|) (x : κ → ℝ) :
    Δ ^ 2 * ∑ i, x i ^ 2 ≤ ∑ i, ((A *ᵥ x) i - lam * x i) ^ 2 := by
  set b := hA.eigenvectorBasis with hb
  have hAsymm : Aᵀ = A := by simpa using hA.eq
  -- coordinates
  have hcoord : ∀ j, inner ℝ (b j) (WithLp.toLp 2 (A *ᵥ x - lam • x)) =
      (hA.eigenvalues j - lam) * inner ℝ (b j) (WithLp.toLp 2 x) := by
    intro j
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    have e1 : (A *ᵥ x) ⬝ᵥ (b j).ofLp = (hA.eigenvalues j • (b j).ofLp) ⬝ᵥ x := by
      rw [dotProduct_comm, dotProduct_mulVec, ← hA.mulVec_eigenvectorBasis j]
      rw [← vecMul_transpose, hAsymm]
    simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [e1, smul_dotProduct, smul_eq_mul, dotProduct_comm x ((b j).ofLp)]
    ring
  have hP1 := b.sum_sq_norm_inner_right (WithLp.toLp 2 (A *ᵥ x - lam • x))
  have hP2 := b.sum_sq_norm_inner_right (WithLp.toLp 2 x)
  have hn1 : ‖(WithLp.toLp 2 (A *ᵥ x - lam • x) : EuclideanSpace ℝ κ)‖ ^ 2 =
      ∑ i, ((A *ᵥ x) i - lam * x i) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (sum_nonneg fun i _ => by positivity)]
    simp
  have hn2 : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ κ)‖ ^ 2 = ∑ i, x i ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (sum_nonneg fun i _ => by positivity)]
    simp
  rw [← hn1, ← hn2, ← hP1, ← hP2, mul_sum]
  refine sum_le_sum fun j _ => ?_
  rw [hcoord j, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, mul_pow]
  have hj : Δ ≤ |hA.eigenvalues j - lam| := by
    apply h
    refine ⟨(b j).ofLp, ?_, hA.mulVec_eigenvectorBasis j⟩
    intro h0
    have := b.norm_eq_one j
    have h1 : (b j) = 0 := by ext i; simpa using congrFun h0 i
    rw [h1] at this; simp at this
  have : Δ ^ 2 ≤ (hA.eigenvalues j - lam) ^ 2 := by
    rw [← sq_abs (hA.eigenvalues j - lam)]
    exact pow_le_pow_left₀ hΔ hj 2
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

end Spectral

section Blocks

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℝ} {M : ℝ}

/-- The Dirichlet restriction of a `LocalBound` matrix to a block is `LocalBound`. -/
theorem LocalBound.submatrix (hH : LocalBound H M) (I : Finset ι) :
    LocalBound (H.submatrix (fun i : I => (i : ι)) (fun i : I => (i : ι))) M where
  symm i j := hH.symm i j
  bound i j hij := hH.bound i j (fun h => hij (Subtype.ext h))
  deg i := by
    refine le_trans (card_le_card_of_injOn (fun j : I => (j : ι)) ?_ ?_) (hH.deg i)
    · intro j hj
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hj ⊢
      exact ⟨fun h => hj.1 (Subtype.ext h), hj.2⟩
    · intro x _ y _ h; exact Subtype.ext h

/-- **Theorem DB.1** (eq. (DB.1)).  See the module docstring. -/
theorem db1 (hH : LocalBound H M) (hM : 0 < M) {lam : ℝ} {u : ι → ℝ} (hu : H *ᵥ u = lam • u)
    (I : Finset ι) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ μ, IsEigenval (H.submatrix (fun i : I => (i : ι)) (fun i : I => (i : ι))) μ →
      Δ ≤ |μ - lam|)
    (d : ι → ℕ) (hd0 : ∀ j ∈ I, (∃ k ∈ Iᶜ, H j k ≠ 0) → d j = 0)
    (hlip : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → H i j ≠ 0 → |(d i : ℝ) - d j| ≤ 1) :
    ∑ j ∈ I, exp (2 * log (1 + Δ / (4 * M)) * d j) * u j ^ 2 ≤
      4 / Δ ^ 2 * ∑ j ∈ I, (∑ k ∈ Iᶜ, H j k * u k) ^ 2 := by
  set μ := log (1 + Δ / (4 * M)) with hμdef
  have hpos : 0 < Δ / (4 * M) := by positivity
  have hμ : 0 < μ := Real.log_pos (by linarith)
  have hexp : exp μ - 1 = Δ / (4 * M) := by
    rw [hμdef, exp_log (by linarith)]; ring
  set A : Matrix I I ℝ := H.submatrix (fun i : I => (i : ι)) (fun i : I => (i : ι)) with hAdef
  have hAsymm : A.IsHermitian := by
    ext i j
    simp [hAdef, Matrix.conjTranspose_apply, hH.symm i j]
  have hcoer := dirichlet_coercive hAsymm hΔ.le hgap
  have hloc := hH.submatrix I
  have hμΔ : 2 * M * (exp μ - 1) ≤ Δ / 2 := by
    rw [hexp]; apply le_of_eq; field_simp; norm_num
  -- the weighted estimate on the block
  have key := weighted_resolvent (A := A) hloc hM.le (lam := lam) (Δ := Δ) (μ := μ) hΔ hμ.le
    hμΔ hcoer
    (φ := fun j : I => μ * d j) (fun i j hij hAij => by
      have := hlip i i.2 j j.2 (fun h => hij (Subtype.ext h)) hAij
      calc |μ * (d i : ℝ) - μ * d j| = μ * |(d i : ℝ) - d j| := by
            rw [← mul_sub, abs_mul, abs_of_pos hμ]
        _ ≤ μ * 1 := mul_le_mul_of_nonneg_left this hμ.le
        _ = μ := mul_one μ)
    (u := fun j : I => u j) (f := fun j : I => -∑ k ∈ Iᶜ, H j k * u k) (by
      intro i
      have h1 := congrFun hu i
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
      rw [← sum_add_sum_compl I (fun k => H i k * u k)] at h1
      have h2 : ∑ j : I, A i j * u j = ∑ k ∈ I, H i k * u k :=
        Finset.sum_coe_sort I (fun k => H i k * u k)
      simp only [mulVec, dotProduct, hAdef, Matrix.submatrix_apply] at h2 ⊢
      linarith)
  have hl : ∑ j : I, exp (2 * (μ * d j)) * u j ^ 2 = ∑ j ∈ I, exp (2 * μ * d j) * u j ^ 2 := by
    rw [← Finset.sum_coe_sort I]
    exact sum_congr rfl fun j _ => by ring_nf
  have hr : ∑ j : I, exp (2 * (μ * d j)) * (-∑ k ∈ Iᶜ, H j k * u k) ^ 2 =
      ∑ j ∈ I, (∑ k ∈ Iᶜ, H j k * u k) ^ 2 := by
    rw [← Finset.sum_coe_sort I (fun j => (∑ k ∈ Iᶜ, H j k * u k) ^ 2)]
    refine sum_congr rfl fun j _ => ?_
    by_cases hf : ∑ k ∈ Iᶜ, H j k * u k = 0
    · simp [hf]
    · have : ∃ k ∈ Iᶜ, H j k ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hf (sum_eq_zero fun k hk => by rw [hcon k hk, zero_mul])
      have hd := hd0 j j.2 this
      simp [hd]
  rw [hl, hr] at key
  exact key

/-- info: 'FormalResearch.Jacobi.db1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms db1

end Blocks

end FormalResearch.Jacobi
