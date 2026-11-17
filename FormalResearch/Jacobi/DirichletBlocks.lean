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
* `jacobiMatrix_localBound` (module `CombesThomas`) : `jacobiMatrix n b a` is `LocalBound`, so
  `db1`, `db2` apply to Jacobi matrices; `jacobi_db1` (module `DirichletIntervals`) is the interval form.

Claim class: proved.  The note's case of an interval without source (`u|_I = 0`) is the case `d`
arbitrary, `f = 0` of `db1`.  Not formalised: DB.3/DB.4 (the Racah corollary: `T`-dependent choice of
`Δ_0`, `L_T`, and the exact Racah spectrum bounds `M ≤ 5`, `n ≤ 5T/2`), which need the physical
`6j` input; the generic Frobenius form is `FormalResearch.Jacobi.db3` (module `DirichletIntervals`),
and the interval form with the lattice distance to the sources is `jacobi_db1` there.  The explicit
two-term form of the Jacobi forcing (`f_l = -H_{l,l-1}u_{l-1}`, `f_r += -H_{r,r+1}u_{r+1}`) is the
statement `f_j = -∑_{k∉I} H_{jk}u_k` read off from the tridiagonal structure; this reading is not
re-proved as a separate lemma.
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

/-- The forcing from outside a block is small: for a pairwise disjoint family of blocks,
`∑_I ∑_{j∈I} (∑_{k∉I} H_{jk} u_k)² ≤ 4 M² ∑ u²` (each exterior site feeds at most two blocks). -/
theorem forcing_sum_le (hH : LocalBound H M) {α : Type*} [Fintype α] (I : α → Finset ι)
    (hdisj : ∀ a b, a ≠ b → Disjoint (I a) (I b)) (u : ι → ℝ) :
    ∑ a, ∑ j ∈ I a, (∑ k ∈ (I a)ᶜ, H j k * u k) ^ 2 ≤ 4 * M ^ 2 * ∑ k, u k ^ 2 := by
  classical
  set N : ι → Finset ι := fun j => univ.filter fun k => k ≠ j ∧ H j k ≠ 0 with hN
  have hM0 : ∀ j, ∀ k, k ≠ j → H j k ≠ 0 → |H j k| ≤ M := fun j k hk _ =>
    hH.bound j k (Ne.symm hk)
  -- pointwise bound
  have hpt : ∀ a, ∀ j ∈ I a, (∑ k ∈ (I a)ᶜ, H j k * u k) ^ 2 ≤ 2 * M ^ 2 * ∑ k ∈ N j, u k ^ 2 := by
    intro a j hj
    set T := (I a)ᶜ.filter fun k => H j k ≠ 0 with hT
    have hTsub : T ⊆ N j := by
      intro k hk
      simp only [hT, mem_filter, mem_compl] at hk
      simp only [hN, mem_filter, mem_univ, true_and]
      exact ⟨fun h => hk.1 (h ▸ hj), hk.2⟩
    have hsum : ∑ k ∈ (I a)ᶜ, H j k * u k = ∑ k ∈ T, H j k * u k := by
      rw [hT, sum_filter_of_ne]
      intro k _ hk h0
      exact hk (by rw [h0, zero_mul])
    have hcard : T.card ≤ 2 := (card_le_card hTsub).trans (hH.deg j)
    rw [hsum]
    calc (∑ k ∈ T, H j k * u k) ^ 2 ≤ T.card * ∑ k ∈ T, (H j k * u k) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ 2 * ∑ k ∈ T, M ^ 2 * u k ^ 2 := by
          apply mul_le_mul (by exact_mod_cast hcard) _ (sum_nonneg fun _ _ => sq_nonneg _)
            (by norm_num)
          refine sum_le_sum fun k hk => ?_
          have hk' : k ≠ j ∧ H j k ≠ 0 := by simpa [hN] using hTsub hk
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right (sq_le_sq' (abs_le.mp (hM0 j k hk'.1 hk'.2)).1
            (abs_le.mp (hM0 j k hk'.1 hk'.2)).2) (sq_nonneg _)
      _ ≤ 2 * M ^ 2 * ∑ k ∈ N j, u k ^ 2 := by
          rw [← mul_sum, ← mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact sum_le_sum_of_subset_of_nonneg hTsub fun _ _ _ => sq_nonneg _
  -- sum over the blocks
  have hnbr : ∑ j, ∑ k ∈ N j, u k ^ 2 ≤ 2 * ∑ k, u k ^ 2 := by
    have e1 : ∀ j, ∑ k ∈ N j, u k ^ 2 = ∑ k, if k ≠ j ∧ H j k ≠ 0 then u k ^ 2 else 0 := by
      intro j; rw [hN]; simp only; rw [sum_filter]
    simp only [e1]
    rw [sum_comm]
    calc ∑ k, ∑ j, (if k ≠ j ∧ H j k ≠ 0 then u k ^ 2 else 0)
        = ∑ k, ((univ.filter fun j => j ≠ k ∧ H k j ≠ 0).card : ℝ) * u k ^ 2 := by
          refine sum_congr rfl fun k _ => ?_
          rw [← sum_filter, sum_const, nsmul_eq_mul]
          congr 3
          ext j
          simp only [mem_filter, mem_univ, true_and]
          rw [hH.symm k j]
          exact ⟨fun h => ⟨Ne.symm h.1, h.2⟩, fun h => ⟨Ne.symm h.1, h.2⟩⟩
      _ ≤ ∑ k, 2 * u k ^ 2 := sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_right (by exact_mod_cast hH.deg k) (sq_nonneg _)
      _ = 2 * ∑ k, u k ^ 2 := by rw [mul_sum]
  calc ∑ a, ∑ j ∈ I a, (∑ k ∈ (I a)ᶜ, H j k * u k) ^ 2
      ≤ ∑ a, ∑ j ∈ I a, 2 * M ^ 2 * ∑ k ∈ N j, u k ^ 2 :=
        sum_le_sum fun a _ => sum_le_sum fun j hj => hpt a j hj
    _ = ∑ j ∈ univ.biUnion I, 2 * M ^ 2 * ∑ k ∈ N j, u k ^ 2 := by
        rw [sum_biUnion]
        intro a _ b _ hab
        exact hdisj a b hab
    _ ≤ ∑ j, 2 * M ^ 2 * ∑ k ∈ N j, u k ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _ =>
          mul_nonneg (by positivity) (sum_nonneg fun _ _ => sq_nonneg _)
    _ = 2 * M ^ 2 * ∑ j, ∑ k ∈ N j, u k ^ 2 := by rw [mul_sum]
    _ ≤ 2 * M ^ 2 * (2 * ∑ k, u k ^ 2) := mul_le_mul_of_nonneg_left hnbr (by positivity)
    _ = 4 * M ^ 2 * ∑ k, u k ^ 2 := by ring

/-- **Theorem DB.2** (eq. (DB.2)).  For a finite family of pairwise disjoint blocks `I_a`, each with
Dirichlet gap `Δ_a ≥ Δ₀ > 0` and admissible distance `d_a`, and a unit (or any) eigenvector `u`,
`∑_a ∑_{j∈I_a} e^{2 μ₀ d_a(j)} u_j² ≤ (16 M² / Δ₀²) ∑ u²`, `μ₀ = log(1 + Δ₀/(4M))`. -/
theorem db2 (hH : LocalBound H M) (hM : 0 < M) {lam : ℝ} {u : ι → ℝ} (hu : H *ᵥ u = lam • u)
    {α : Type*} [Fintype α] (I : α → Finset ι)
    (hdisj : ∀ a b, a ≠ b → Disjoint (I a) (I b)) {Δ₀ : ℝ} (hΔ₀ : 0 < Δ₀) (Δ : α → ℝ)
    (hΔ : ∀ a, Δ₀ ≤ Δ a)
    (hgap : ∀ a μ, IsEigenval (H.submatrix (fun i : I a => (i : ι)) (fun i : I a => (i : ι))) μ →
      Δ a ≤ |μ - lam|)
    (d : α → ι → ℕ) (hd0 : ∀ a, ∀ j ∈ I a, (∃ k ∈ (I a)ᶜ, H j k ≠ 0) → d a j = 0)
    (hlip : ∀ a, ∀ i ∈ I a, ∀ j ∈ I a, i ≠ j → H i j ≠ 0 → |(d a i : ℝ) - d a j| ≤ 1) :
    ∑ a, ∑ j ∈ I a, exp (2 * log (1 + Δ₀ / (4 * M)) * d a j) * u j ^ 2 ≤
      16 * M ^ 2 / Δ₀ ^ 2 * ∑ k, u k ^ 2 := by
  have hμ : ∀ a, log (1 + Δ₀ / (4 * M)) ≤ log (1 + Δ a / (4 * M)) := fun a =>
    Real.log_le_log (by positivity) (by gcongr; exact hΔ a)
  have hblock : ∀ a, ∑ j ∈ I a, exp (2 * log (1 + Δ₀ / (4 * M)) * d a j) * u j ^ 2 ≤
      4 / Δ₀ ^ 2 * ∑ j ∈ I a, (∑ k ∈ (I a)ᶜ, H j k * u k) ^ 2 := by
    intro a
    have hΔa : 0 < Δ a := lt_of_lt_of_le hΔ₀ (hΔ a)
    calc ∑ j ∈ I a, exp (2 * log (1 + Δ₀ / (4 * M)) * d a j) * u j ^ 2
        ≤ ∑ j ∈ I a, exp (2 * log (1 + Δ a / (4 * M)) * d a j) * u j ^ 2 := by
          refine sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          apply exp_le_exp.mpr
          have := hμ a
          have h0 : (0 : ℝ) ≤ d a j := Nat.cast_nonneg _
          nlinarith
      _ ≤ 4 / Δ a ^ 2 * ∑ j ∈ I a, (∑ k ∈ (I a)ᶜ, H j k * u k) ^ 2 :=
          db1 hH hM hu (I a) hΔa (hgap a) (d a) (hd0 a) (hlip a)
      _ ≤ 4 / Δ₀ ^ 2 * ∑ j ∈ I a, (∑ k ∈ (I a)ᶜ, H j k * u k) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun _ _ => sq_nonneg _)
          gcongr; exact hΔ a
  calc ∑ a, ∑ j ∈ I a, exp (2 * log (1 + Δ₀ / (4 * M)) * d a j) * u j ^ 2
      ≤ ∑ a, 4 / Δ₀ ^ 2 * ∑ j ∈ I a, (∑ k ∈ (I a)ᶜ, H j k * u k) ^ 2 := sum_le_sum fun a _ => hblock a
    _ = 4 / Δ₀ ^ 2 * ∑ a, ∑ j ∈ I a, (∑ k ∈ (I a)ᶜ, H j k * u k) ^ 2 := by rw [mul_sum]
    _ ≤ 4 / Δ₀ ^ 2 * (4 * M ^ 2 * ∑ k, u k ^ 2) :=
        mul_le_mul_of_nonneg_left (forcing_sum_le hH I hdisj u) (by positivity)
    _ = 16 * M ^ 2 / Δ₀ ^ 2 * ∑ k, u k ^ 2 := by ring

/-- info: 'FormalResearch.Jacobi.db2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms db2

end Blocks

end FormalResearch.Jacobi
