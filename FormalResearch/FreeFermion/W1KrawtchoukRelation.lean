module

public import FormalResearch.FreeFermion.W1Krawtchouk
public import FormalResearch.FreeFermion.W1TridiagRelation

/-!
# The Krawtchouk chain satisfies the tridiagonal relation (Weyl W1, `prop:bisp`(i))

Source: `Weyl/free_fermion/paper/parts/model.tex`, Proposition `prop:bisp`(i): "By self-duality
(... in this eigenbasis `X` is tridiagonal with nonzero links, as one checks by differentiating the
generating function) `(X, Y)` is a Leonard pair".

`krawtchouk_tdRel`: for `0 < p < 1`, `q = 1 - p`, `X = diag(n/N)` and `Y` the Krawtchouk chain,
`[Y,[Y,X]] - X/N² = ((p-q)/N²) Y - p/N²` (that is `tdRel X Y 0 (1/N²) = ((p-q)/N²) Y - (p/N²)`),
a one-line identity of coefficients (`W1TridiagRelation.tdRel_triChain`).  Together with the
spectrum `{k/N}` (`krawY_hasEigenvalue_iff`) it gives the duality by
`W1LeonardDual.tridiag_dual_of_relation` (the factor `(y_i-y_j)² - 1/N²` is nonzero for
`|i-j| ≥ 2`) without the generating function (`krawtchouk_dual_irreducible_of_relation`); the
existing proof in `W1Krawtchouk` is unchanged.  The spectrum itself still comes from the generating
function there.
-/

@[expose] public section

namespace FormalResearch.FreeFermion

open Matrix

section Relation

variable (p : ℝ) (N : ℕ)

/-- The Krawtchouk links as a function on `ℤ`, zero for `n < 0`. -/
noncomputable def krawAZ (n : ℤ) : ℝ := if n < 0 then 0 else krawA p N n.toNat

/-- The Krawtchouk diagonal as a function on `ℤ`. -/
noncomputable def krawBZ (n : ℤ) : ℝ := krawB p N n.toNat

theorem krawChain_eq_triChain : krawChain p N = triChain N (krawAZ p N) (krawBZ p N) := by
  ext i j
  by_cases h1 : i = j
  · subst h1
    rw [triChain_diag]
    simp [krawChain, krawBZ]
  · by_cases h2 : (j : ℕ) = i + 1
    · rw [triChain_succ N _ _ h2]
      simp [krawChain, h1, h2, krawAZ]
    · by_cases h3 : (i : ℕ) = j + 1
      · rw [triChain_pred N _ _ h3]
        simp only [krawChain, Matrix.of_apply, eq_false h1, eq_false h2, eq_true h3, ↓reduceIte,
          krawAZ]
        simp
      · rw [triChain_far N _ _ h1 h2 h3]
        simp [krawChain, h1, h2, h3]

variable {p N}

theorem krawAZ_neg_one : krawAZ p N (-1) = 0 := by simp [krawAZ]

theorem krawAZ_top : krawAZ p N N = 0 := by
  simp [krawAZ, krawA]

theorem krawAZ_sq (hp : 0 < p) (hp1 : p < 1) (n : ℤ) (h1 : -1 ≤ n) (h2 : n ≤ N) :
    krawAZ p N n ^ 2 = p * (1 - p) * ((n + 1) * (N - n)) / (N : ℝ) ^ 2 := by
  rcases h1.eq_or_lt with rfl | h
  · simp [krawAZ]
  · have h0 : 0 ≤ n := by omega
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := Int.eq_ofNat_of_zero_le h0
    have hm : (m : ℝ) ≤ N := by exact_mod_cast (show m ≤ N by omega)
    have hnn : 0 ≤ p * (1 - p) * (((m : ℝ) + 1) * ((N : ℝ) - m)) := by
      have : 0 ≤ ((m : ℝ) + 1) * ((N : ℝ) - m) :=
        mul_nonneg (by positivity) (by linarith)
      have : 0 ≤ p * (1 - p) := mul_nonneg hp.le (by linarith)
      positivity
    simp only [krawAZ, Int.natCast_nonneg, not_lt.mpr, ↓reduceIte, Int.toNat_natCast, krawA]
    rw [div_pow, Real.sq_sqrt hnn]
    push_cast
    ring

theorem krawtchouk_tdRel (hp : 0 < p) (hp1 : p < 1) (hN : 0 < N) :
    tdRel (Matrix.toLin' (Matrix.diagonal fun i : Fin (N + 1) => ((i : ℤ) : ℝ) / N))
        (Matrix.toLin' (krawChain p N)) ((0 : ℝ) : ℝ) ((1 / (N : ℝ) ^ 2 : ℝ) : ℝ) =
      (0 : ℝ) • (Matrix.toLin' (krawChain p N) * Matrix.toLin' (krawChain p N)) +
        (((p - (1 - p)) / (N : ℝ) ^ 2 : ℝ) : ℝ) • Matrix.toLin' (krawChain p N) +
        ((-p / (N : ℝ) ^ 2 : ℝ) : ℝ) • (1 : Module.End ℝ (Fin (N + 1) → ℝ)) := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  rw [krawChain_eq_triChain]
  refine tdRel_triChain N (krawAZ p N) (krawBZ p N) (fun n : ℤ => (n : ℝ) / N) krawAZ_neg_one
    krawAZ_top 0 (1 / (N : ℝ) ^ 2) 0 ((p - (1 - p)) / (N : ℝ) ^ 2) (-p / (N : ℝ) ^ 2) ?_ ?_ ?_
  · intro n
    push_cast
    ring
  · intro n
    by_cases hn : n < 0
    · simp [krawAZ, hn]
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := Int.eq_ofNat_of_zero_le (by omega)
      have : ((((m : ℤ) + 1 : ℤ) : ℝ) / N - ((m : ℤ) : ℝ) / N) *
          (krawBZ p N m - krawBZ p N ((m : ℤ) + 1)) -
          0 * ((((m : ℤ) + 1 : ℤ) : ℝ) / N + ((m : ℤ) : ℝ) / N) -
          0 * (krawBZ p N m + krawBZ p N ((m : ℤ) + 1)) - (p - (1 - p)) / (N : ℝ) ^ 2 = 0 := by
        simp only [krawBZ, Int.toNat_natCast]
        rw [show (((m : ℤ) + 1).toNat) = m + 1 by omega]
        simp only [krawB]
        push_cast
        field_simp
        ring
      rw [this, mul_zero]
  · intro n h0 hn
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := Int.eq_ofNat_of_zero_le h0
    have e1 := krawAZ_sq (N := N) hp hp1 (m : ℤ) (by omega) hn
    have e2 := krawAZ_sq (N := N) hp hp1 ((m : ℤ) - 1) (by omega) (by omega)
    rw [e1, e2]
    simp only [krawBZ, Int.toNat_natCast, krawB]
    push_cast
    field_simp
    ring

/-- **Duality of the Krawtchouk chain from the tridiagonal relation** (an alternative to
`W1Krawtchouk.krawX_irreducible`, which uses the generating function): `X = diag(n/N)` is
irreducible tridiagonal in the eigenbasis of `Y`. -/
theorem krawtchouk_dual_irreducible_of_relation (hp : 0 < p) (hp1 : p < 1) (hN : 0 < N) :
    IsIrreducibleTridiag (LinearMap.toMatrixAlgEquiv (krawBasis p N hp hp1 hN) (krawX N)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmono : Function.Injective (fun n : Fin (N + 1) => ((n : ℕ) : ℝ) / N) := by
    intro a b hab
    have : ((a : ℕ) : ℝ) = b := by
      have := hab; field_simp at this; exact this
    exact Fin.ext (by exact_mod_cast this)
  have hX : Matrix.toLin' (Matrix.diagonal fun i : Fin (N + 1) => ((i : ℤ) : ℝ) / N) = krawX N := by
    simp [krawX]
  have hrel := krawtchouk_tdRel hp hp1 hN
  rw [hX] at hrel
  have hrel' : tdRel (krawX N) (krawY p N) (RCLike.ofReal (0 : ℝ) : ℝ)
      (RCLike.ofReal (1 / (N : ℝ) ^ 2) : ℝ) =
      (RCLike.ofReal (0 : ℝ) : ℝ) • (krawY p N * krawY p N) +
        (RCLike.ofReal ((p - (1 - p)) / (N : ℝ) ^ 2) : ℝ) • krawY p N +
        (RCLike.ofReal (-p / (N : ℝ) ^ 2) : ℝ) • (1 : Module.End ℝ (Fin (N + 1) → ℝ)) := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq, krawY] using hrel
  refine tridiag_dual_of_relation (Pi.basisFun ℝ (Fin (N + 1))) (krawBasis p N hp hp1 hN)
    (krawX N) (krawY p N) (fun n => ((n : ℕ) : ℝ) / N) (fun n => ((n : ℕ) : ℝ) / N) hmono
    (krawX_basis_e N) (krawY_basis p N hp hp1 hN)
    (by rw [krawY_matrix_e]; exact krawChain_irreducible p N hp hp1 hN) 0 (1 / (N : ℝ) ^ 2) 0
    ((p - (1 - p)) / (N : ℝ) ^ 2) (-p / (N : ℝ) ^ 2) hrel' ?_
  intro i j hij h1 h2
  simp only [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at h1 h2
  have hfar : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i := by omega
  have hN2 : (N : ℝ) ^ 2 ≠ 0 := by positivity
  have hd : (2 : ℝ) ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
    rcases hfar with h | h
    · have : ((i : ℕ) : ℝ) + 2 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · have : ((j : ℕ) : ℝ) + 2 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
  have hd2 : (4 : ℝ) ≤ (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ^ 2 := by
    nlinarith [sq_abs (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)), abs_nonneg (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ))]
  have hey : (((i : ℕ) : ℝ) / N - ((j : ℕ) : ℝ) / N) ^ 2 - 0 * (((i : ℕ) : ℝ) / N + ((j : ℕ) : ℝ) / N) -
      1 / (N : ℝ) ^ 2 = ((((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ^ 2 - 1) / (N : ℝ) ^ 2 := by
    field_simp
    ring
  rw [hey]
  exact div_ne_zero (by linarith) hN2

/-- info: 'FormalResearch.FreeFermion.krawtchouk_tdRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms krawtchouk_tdRel

/-- info: 'FormalResearch.FreeFermion.krawtchouk_dual_irreducible_of_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms krawtchouk_dual_irreducible_of_relation

end Relation

end FormalResearch.FreeFermion
