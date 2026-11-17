module

public import FormalResearch.Jacobi.DirichletBlocks
public import FormalResearch.MatrixAnalysis.MaskedFrobenius

/-!
# DB.1/DB.2 for consecutive intervals of a Jacobi matrix; the Frobenius deletion bound (DB.3)

Source: `Weyl/P5/notes/dirichlet_block_audit.md`, Theorem DB.1, Corollary DB.2 (eq. (DB.3)) (PR 250,
head `cfad461d2`).  Specialisation of `FormalResearch.Jacobi.db1` to an interval `I = [l, r]` of
`jacobiMatrix n b a` with the lattice distance to the sources:

* `intervalDist` : `d_I(j) = min(j - l, r - j)` if both endpoints are sources, `j - l` (resp. `r - j`)
  if only the left (right) one is, `0` if there is none (then the forcing vanishes and `u|_I = 0`);
  `l` is a *source* iff `l > 0` and `a_{l-1} ≠ 0`, `r` iff `r + 1 < n` and `a_r ≠ 0`
  (physical endpoints and zero bonds are not sources);
* the forcing is `∑_{k∉I} J_{jk} u_k`, which for an interval is the note's `f(l) = H_{l,l-1}u_{l-1}`,
  `f(r) += H_{r,r+1}u_{r+1}` up to sign (at a singleton both terms add); this identification is read
  off from the tridiagonal structure, not proved as a separate lemma;
* `jacobi_db1` : **(DB.1)** for the Jacobi matrix on one interval;
* `db3` : **(DB.3), generic Frobenius form.**  For a matrix `U` whose columns are eigenvectors of `H`
  with unit norm, and for every column a disjoint family of blocks with gaps `Δ ≥ Δ₀` and
  admissible distances, the mask `K_{jc} = 1[j ∈ some block of column c, d(j) ≥ L]` satisfies
  `‖K ∘ U‖_F² ≤ (#columns) (16 M²/Δ₀²) e^{-2 μ₀ L}`.

Claim class: proved.  Not formalised: DB.4 (the explicit Racah parameter choice `Δ₀ = T^{-r}`,
`L_T`), which needs the exact Racah spectrum `M ≤ 5`, `n ≤ 5T/2` and the identification of the Wigner
`6j` matrix with `U`; here `U`, `M`, `Δ₀`, `L` are free parameters.
-/

@[expose] public section

namespace FormalResearch.Jacobi

open Matrix Finset Real FormalResearch.MatrixAnalysis

section Interval

variable {n : ℕ} {b a : ℕ → ℝ}

/-- Lattice distance to the sources of the interval `[l, r]` (see the module docstring); the
source flags are passed as propositions. -/
def intervalDist (l r : ℕ) (sl sr : Prop) [Decidable sl] [Decidable sr] (j : ℕ) : ℕ :=
  if sl ∧ sr then min (j - l) (r - j) else if sl then j - l else if sr then r - j else 0

theorem jacobi_offdiag_ne {i j : Fin n} (hij : i ≠ j) (h : jacobiMatrix n b a i j ≠ 0) :
    (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i := by
  by_contra hcon
  push Not at hcon
  apply h
  simp [jacobiMatrix, hij, hcon.1, hcon.2]

theorem abs_natCast_sub_le {x y : ℕ} (h1 : x ≤ y + 1) (h2 : y ≤ x + 1) : |(x : ℝ) - y| ≤ 1 := by
  rw [abs_le]
  constructor
  · have : (y : ℝ) ≤ x + 1 := by exact_mod_cast h2
    linarith
  · have : (x : ℝ) ≤ y + 1 := by exact_mod_cast h1
    linarith

/-- **Theorem DB.1 for a Jacobi matrix on an interval `[l, r]`.**  `I = [l, r]`, the sources are the
endpoints joined by a nonzero bond to a site outside `I`, `d` is `intervalDist`, `μ_I = log (1 + Δ/(4M))`:
`∑_{j∈I} e^{2 μ_I d(j)} u_j² ≤ (4/Δ²) ∑_{j∈I} f_j²` with `f_j = ∑_{k∉I} J_{jk} u_k`. -/
theorem jacobi_db1 {M : ℝ} (hM : 0 < M) (hMa : ∀ j, j + 1 < n → |a j| ≤ M) {lam : ℝ}
    {u : Fin n → ℝ} (hu : jacobiMatrix n b a *ᵥ u = lam • u) (l r : Fin n) (hlr : l ≤ r)
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ μ, IsEigenval ((jacobiMatrix n b a).submatrix
      (fun i : Finset.Icc l r => (i : Fin n)) (fun i : Finset.Icc l r => (i : Fin n))) μ →
        Δ ≤ |μ - lam|) :
    ∑ j ∈ Finset.Icc l r, exp (2 * log (1 + Δ / (4 * M)) *
        (intervalDist l r (∃ k ∈ (Finset.Icc l r)ᶜ, jacobiMatrix n b a l k ≠ 0)
          (∃ k ∈ (Finset.Icc l r)ᶜ, jacobiMatrix n b a r k ≠ 0) j : ℕ)) * u j ^ 2 ≤
      4 / Δ ^ 2 * ∑ j ∈ Finset.Icc l r,
        (∑ k ∈ (Finset.Icc l r)ᶜ, jacobiMatrix n b a j k * u k) ^ 2 := by
  classical
  set J := jacobiMatrix n b a with hJ
  set I := Finset.Icc l r with hI
  set sl : Prop := ∃ k ∈ Iᶜ, J l k ≠ 0 with hsl
  set sr : Prop := ∃ k ∈ Iᶜ, J r k ≠ 0 with hsr
  refine db1 (jacobiMatrix_localBound n b a hM.le hMa) hM hu I hΔ hgap
    (fun j => intervalDist l r sl sr j) ?_ ?_
  · intro j hj ⟨k, hk, hjk⟩
    have hjI := Finset.mem_Icc.mp hj
    have hkI : ¬ (l ≤ k ∧ k ≤ r) := by simpa [hI] using hk
    have hne : j ≠ k := fun h => hkI (h ▸ hjI)
    rcases jacobi_offdiag_ne hne hjk with h | h
    · -- `k = j + 1 ∉ I`, so `j = r`
      have hjr : (j : ℕ) = r := by
        have := hjI.2; have := hjI.1
        by_contra hjr
        apply hkI
        constructor <;> (try (simp only [Fin.le_def] at *)) <;> omega
      have hsr' : sr := ⟨k, hk, by rw [show r = j from Fin.ext hjr.symm]; exact hjk⟩
      by_cases hsl' : sl <;> simp [intervalDist, hsl', hsr', hjr]
    · have hjl : (j : ℕ) = l := by
        have := hjI.2; have := hjI.1
        by_contra hjl
        apply hkI
        constructor <;> (try (simp only [Fin.le_def] at *)) <;> omega
      have hsl' : sl := ⟨k, hk, by rw [show l = j from Fin.ext hjl.symm]; exact hjk⟩
      by_cases hsr' : sr <;> simp [intervalDist, hsl', hsr', hjl]
  · intro i hi j hj hij hJij
    have hi' := Finset.mem_Icc.mp hi
    have hj' := Finset.mem_Icc.mp hj
    simp only [Fin.le_def] at hi' hj'
    have hadj := jacobi_offdiag_ne hij hJij
    unfold intervalDist
    by_cases hsl' : sl <;> by_cases hsr' : sr <;> simp only [hsl', hsr', and_self, and_true,
      and_false, ite_true, ite_false] <;>
      exact abs_natCast_sub_le (by omega) (by omega)

end Interval

section Frobenius

variable {ι κ α : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype α] {H : Matrix ι ι ℝ}
  {M : ℝ}

/-- **(DB.3), generic Frobenius form.**  Let the columns of `U` be unit eigenvectors of the
`LocalBound` matrix `H` (eigenvalue `lam c`), and for every column let `I c a` be a pairwise
disjoint family of blocks with Dirichlet gaps `Δ c a ≥ Δ₀ > 0` and admissible distances `d c a`.
For the (moving, disconnected) mask `K_{jc} = ∃ a, j ∈ I c a ∧ L ≤ d c a j`,
`‖K ∘ U‖_F² ≤ (#columns) · (16 M²/Δ₀²) · e^{-2 μ₀ L}`, `μ₀ = log(1 + Δ₀/(4M))`. -/
theorem db3 (hH : LocalBound H M) (hM : 0 < M) (U : Matrix ι κ ℝ) (lam : κ → ℝ)
    (hU : ∀ c, H *ᵥ (fun j => U j c) = lam c • (fun j => U j c))
    (hunit : ∀ c, ∑ j, U j c ^ 2 = 1) (I : κ → α → Finset ι)
    (hdisj : ∀ c a b, a ≠ b → Disjoint (I c a) (I c b)) {Δ₀ : ℝ} (hΔ₀ : 0 < Δ₀)
    (Δ : κ → α → ℝ) (hΔ : ∀ c a, Δ₀ ≤ Δ c a)
    (hgap : ∀ c a μ, IsEigenval (H.submatrix (fun i : I c a => (i : ι)) (fun i : I c a => (i : ι)))
      μ → Δ c a ≤ |μ - lam c|)
    (d : κ → α → ι → ℕ) (hd0 : ∀ c a, ∀ j ∈ I c a, (∃ k ∈ (I c a)ᶜ, H j k ≠ 0) → d c a j = 0)
    (hlip : ∀ c a, ∀ i ∈ I c a, ∀ j ∈ I c a, i ≠ j → H i j ≠ 0 → |(d c a i : ℝ) - d c a j| ≤ 1)
    (L : ℕ) [∀ j c, Decidable (∃ a, j ∈ I c a ∧ L ≤ d c a j)] :
    frobSq (maskMul (fun j c => ∃ a, j ∈ I c a ∧ L ≤ d c a j) U) ≤
      Fintype.card κ * (16 * M ^ 2 / Δ₀ ^ 2 * exp (-(2 * log (1 + Δ₀ / (4 * M)) * L))) := by
  classical
  set μ₀ := log (1 + Δ₀ / (4 * M)) with hμ₀
  have hμ0 : 0 < μ₀ := Real.log_pos (by have : 0 < Δ₀ / (4 * M) := by positivity
                                        linarith)
  -- per-column bound
  have hcol : ∀ c, ∑ j, (maskMul (fun j c => ∃ a, j ∈ I c a ∧ L ≤ d c a j) U) j c ^ 2 ≤
      16 * M ^ 2 / Δ₀ ^ 2 * exp (-(2 * μ₀ * L)) := by
    intro c
    have h2 := db2 hH hM (hU c) (I c) (hdisj c) hΔ₀ (Δ c) (hΔ c) (hgap c) (d c) (hd0 c) (hlip c)
    rw [hunit c, mul_one] at h2
    have h3 : ∑ j, (maskMul (fun j c => ∃ a, j ∈ I c a ∧ L ≤ d c a j) U) j c ^ 2 ≤
        exp (-(2 * μ₀ * L)) * ∑ a, ∑ j ∈ I c a, exp (2 * μ₀ * d c a j) * U j c ^ 2 := by
      calc ∑ j, (maskMul (fun j c => ∃ a, j ∈ I c a ∧ L ≤ d c a j) U) j c ^ 2
          ≤ ∑ j, ∑ a, (if j ∈ I c a ∧ L ≤ d c a j then exp (-(2 * μ₀ * L)) *
              (exp (2 * μ₀ * d c a j) * U j c ^ 2) else 0) := by
            refine sum_le_sum fun j _ => ?_
            by_cases hK : ∃ a, j ∈ I c a ∧ L ≤ d c a j
            · obtain ⟨a, ha⟩ := hK
              have e : maskMul (fun j c => ∃ a, j ∈ I c a ∧ L ≤ d c a j) U j c = U j c := by
                have hK' : ∃ a, j ∈ I c a ∧ L ≤ d c a j := ⟨a, ha⟩
                simp only [maskMul, Matrix.of_apply, hK', ite_true]
              rw [e]
              refine le_trans ?_ (single_le_sum (f := fun a => if j ∈ I c a ∧ L ≤ d c a j then
                exp (-(2 * μ₀ * L)) * (exp (2 * μ₀ * d c a j) * U j c ^ 2) else 0)
                (fun a _ => by split_ifs <;> positivity) (mem_univ a))
              simp only [ha, and_self, ite_true]
              have : (1 : ℝ) ≤ exp (-(2 * μ₀ * L)) * exp (2 * μ₀ * d c a j) := by
                rw [← exp_add]
                apply one_le_exp
                have : (L : ℝ) ≤ d c a j := by exact_mod_cast ha.2
                nlinarith
              nlinarith [sq_nonneg (U j c)]
            · have e : maskMul (fun j c => ∃ a, j ∈ I c a ∧ L ≤ d c a j) U j c = 0 := by
                simp only [maskMul, Matrix.of_apply, hK, ite_false]
              rw [e]
              calc (0 : ℝ) ^ 2 = 0 := by norm_num
                _ ≤ _ := sum_nonneg fun a _ => by split_ifs <;> positivity
        _ = ∑ a, ∑ j, (if j ∈ I c a ∧ L ≤ d c a j then exp (-(2 * μ₀ * L)) *
              (exp (2 * μ₀ * d c a j) * U j c ^ 2) else 0) := sum_comm
        _ ≤ ∑ a, ∑ j ∈ I c a, exp (-(2 * μ₀ * L)) * (exp (2 * μ₀ * d c a j) * U j c ^ 2) := by
            refine sum_le_sum fun a _ => ?_
            rw [← sum_filter]
            exact sum_le_sum_of_subset_of_nonneg (fun j hj => by
              simp only [mem_filter, mem_univ, true_and] at hj; exact hj.1)
              (fun j _ _ => by positivity)
        _ = _ := by rw [mul_sum]; exact sum_congr rfl fun a _ => by rw [mul_sum]
    calc _ ≤ _ := h3
      _ ≤ exp (-(2 * μ₀ * L)) * (16 * M ^ 2 / Δ₀ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (exp_pos _).le
      _ = _ := by ring
  unfold frobSq
  rw [sum_comm]
  calc ∑ c, ∑ j, (maskMul (fun j c => ∃ a, j ∈ I c a ∧ L ≤ d c a j) U) j c ^ 2
      ≤ ∑ c : κ, 16 * M ^ 2 / Δ₀ ^ 2 * exp (-(2 * μ₀ * L)) := sum_le_sum fun c _ => hcol c
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]

/-- info: 'FormalResearch.Jacobi.jacobi_db1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacobi_db1

/-- info: 'FormalResearch.Jacobi.db3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms db3

end Frobenius

end FormalResearch.Jacobi
