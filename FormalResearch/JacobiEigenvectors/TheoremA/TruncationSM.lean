module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Setting.JacobiFamily

/-!
# Paper J, Layer 2: finite smooth jets and weighted hard edges (`lem:smo-SM`)

Source: Paper J `app_thmA.tex`, "The eigenvalue rule from the real charts", lemma `lem:smo-SM` ("Finite smooth jets and weighted
hard edges", \label{lem:smo-SM}), with the setting of `main_results.tex` (def:symbols, eq:symbols, eq:remainders) and the truncated
family `tilde J_h` of `thmA.tex` / `app_thmA.tex` (`truncFamily` of `TheoremA/Statements.lean`, restated locally as `truncSM`, see below).
Plan item L2.S4 of `PLAN.md`.  Namespace `FormalResearch.JacobiEigenvectors.TheoremA`.

## Statement formalised: `smo_SM`

For a set `Kset` of parameters (round 5: the constants `C', h_0` are uniform in `mu in Kset`, as in the paper; the hypotheses are uniform too), `F : SymbolFamily Par`,
`J = F.jacobiMat mu N` (the matrix `J_h` with `E_n = s_n(L-s_n) G_h(s_n)`, `B_n = B_h(u_n)`), and `truncSM F M` (`tilde J_h^{[M]}`: the jets
`G_j, B_j` with `j <= M`, samples of the polynomials, no remainder).  Hypotheses: `G_0 >= g_* > 0` on `[0,L]`; the remainders at the lattice nodes,
`|G_h(s_n) - sum_{j<=M} h^j G_j(s_n)| <= C h^{M+1}` for `0 <= n < N`, and `|B_h(u_n) - sum_{j<=M} h^j B_j(u_n)| <= C h^{M+1}` for `0 <= n <= N`
(the paper's `||r||_inf + ||q||_inf <= C h^{M+1}` over lattice points); and the **added** boundedness `|G_j| <= K_j` on `[0,L]`, `j <= M` (see
"Differences").  Conclusions, for some `C'`, `h_0` and all `N` with `h = L/(N+1) <= h_0`:

* (a) the bonds of `J` and of `tilde J` are positive;
* (b) `||J - tilde J||_op <= C' h^{M+1}`, stated in the form `sum_i ((J - tilde J) x)_i^2 <= (C' h^{M+1})^2 sum_i x_i^2` for all `x`
  (this is the definition of the operator norm, `sup_{||x||=1} ||(J - tilde J) x||`);
* (c) every ordered eigenvalue of `J` and the same-index eigenvalue of `tilde J` (`IsEigenSystem`: decreasing order, orthogonal eigenvector
  matrix) differ by at most `C' h^{M+1}`.

The proof: (a) divides out the hard-edge factor, `E_n = s_n(L-s_n)(T_n + r_n)` with `T_n` the truncated symbol, `T_n >= g_*/2` by the jet bounds
(`smo_jet_trunc`), and `sqrt` is perturbed (`smo_sqrt_perturb`); (b) the difference is tridiagonal with entries `O(h^{M+1})` (`smo_band_l2`:
a Schur-type estimate `||D||_2 <= 3 max |D_ij|` for tridiagonal `D`); (c) Weyl's inequality, which Mathlib does not state for matrices, is proved from the
min-max argument on the two eigen-bases (`smo_weyl_core`, `smo_weyl_abs`, with `smo_kernel_exists` giving the test vector and `smo_quad_eig` the spectral
expansion of the Rayleigh quotient).

## Differences from the paper

* **Added hypothesis `hGbdd` (boundedness of the jets `G_j`, `j <= M`, on `[0,L]`, uniformly in `mu in Kset`).**  The paper states the lemma for "real `G_j, B_j`", but the claim
  "the truncated factor is `>= g_*/2`" needs `sup |sum_{1<=j<=M} h^j G_j(s_n)| -> 0`, i.e. bounded jets.  Without it the lemma is false: with
  `G_0 = 1`, `M = 1`, `B_j = 0`, `r = q = 0`, and `G_1(s) = -c/(s - L/2)` (`c > 1`, `G_1(L/2) = 0`), at every `N` with `N+1` even the node
  `s = L/2 + h` has `E = s(L-s)(1 - c) < 0`, so the bond is not positive for infinitely many arbitrarily small `h`.  Under `(D_M)` the jets are `C^r([0,L])`,
  so `hGbdd` holds in the application.  Only the `G_j` need bounds; the diagonal jets `B_j` enter only through the remainder hypothesis.
* **Remainders only at lattice nodes**, with one constant `C` for `E` and `B` (the paper's `||r||_inf + ||q||_inf <= C h^{M+1}`); the paper's `J_h`
  uses `E_n = s_n(L-s_n) G_h(s_n)` and the remainder is `G_h - sum`, as here (`G_h` is the full symbol `F.Gh`).
* **`truncSM`** is the same family as `TheoremA.truncFamily` (`Statements.lean`), restated so that this module does not import the statement freeze
  (its import chain was mid-rebuild); the two are equal by `rfl` after unfolding.
* **Operator norm** in the `l^2` form (b); the eigenvalue claim (c) is for *all* eigen-systems `IsEigenSystem`, so no existence theorem is needed.
* **Constants.** `C' = 3(C_0 + C_a + 1)` with `C_0 = max(C,0)`, `C_a = L C_0/(2 sqrt(g_*/2))`, and `h_0` depend only on `g_*`, `C`, `L`, `M` and the
  bounds `K_j` of `hGbdd`; they are chosen before `N`.
* The paper's "all integer powers of `h` allowed" is read as: the expansion is in `h^j`, `0 <= j <= M`, with no parity assumption.

## Not formalised

* The use of `(D_M)` itself (only the displayed hypotheses are used); round 5: the statement was made uniform in `mu in Kset` (constants before `mu`), as `EigClose` needs it.
* The parity-frozen family and the application to `J_h` (`app_thmA` after the lemma) are not part of this module.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Matrix
open FormalResearch.JacobiEigenvectors.Setting




variable {N : ℕ}

lemma smo_mul_transpose_eq_one {U : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hU : Uᵀ * U = 1) : U * Uᵀ = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq (Fin (N+1)) (Fin (N+1)) ℝ rfl).mp hU

lemma smo_dot_U {U : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hU : Uᵀ * U = 1) (y z : Fin (N+1) → ℝ) :
    (U *ᵥ y) ⬝ᵥ (U *ᵥ z) = y ⬝ᵥ z := by
  have h1 : (U *ᵥ y) ᵥ* U = Uᵀ *ᵥ (U *ᵥ y) := by
    rw [← Matrix.vecMul_transpose Uᵀ, Matrix.transpose_transpose]
  rw [dotProduct_mulVec, h1, mulVec_mulVec, hU, one_mulVec]

lemma smo_quad_eig {A U : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} {X : Fin (N+1) → ℝ}
    (hU : Uᵀ * U = 1) (heig : A * U = U * Matrix.diagonal X) (x : Fin (N+1) → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = ∑ j, X j * (Uᵀ *ᵥ x) j ^ 2 := by
  have hUU := smo_mul_transpose_eq_one hU
  set y := Uᵀ *ᵥ x with hy
  have hx : x = U *ᵥ y := by
    rw [hy, mulVec_mulVec, hUU, one_mulVec]
  have hAx : A *ᵥ x = U *ᵥ (Matrix.diagonal X *ᵥ y) := by
    rw [hx, mulVec_mulVec, heig, ← mulVec_mulVec]
  rw [hAx]
  conv_lhs => rw [hx]
  rw [smo_dot_U hU]
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma smo_norm_sq_eig {U : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hU : Uᵀ * U = 1) (x : Fin (N+1) → ℝ) :
    x ⬝ᵥ x = ∑ j, (Uᵀ *ᵥ x) j ^ 2 := by
  have hUU := smo_mul_transpose_eq_one hU
  set y := Uᵀ *ᵥ x with hy
  have hx : x = U *ᵥ y := by
    rw [hy, mulVec_mulVec, hUU, one_mulVec]
  conv_lhs => rw [hx]
  rw [smo_dot_U hU]
  simp only [dotProduct]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma smo_kernel_exists (U V : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (k : Fin (N+1)) :
    ∃ x : Fin (N+1) → ℝ, x ≠ 0 ∧ (∀ j, k < j → (Uᵀ *ᵥ x) j = 0) ∧ (∀ j, j < k → (Vᵀ *ᵥ x) j = 0) := by
  classical
  let R : Matrix (Fin (N+1)) (Fin (N+1)) ℝ := Matrix.of fun j l =>
    if j = k then 0 else if k < j then U l j else if j < k then V l j else 0
  have hdet : R.det = 0 := Matrix.det_eq_zero_of_row_eq_zero k (fun l => by simp [R])
  obtain ⟨v, hv, hRv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv, ?_, ?_⟩
  · intro j hj
    have hj' := congrFun hRv j
    have hne : j ≠ k := ne_of_gt hj
    simp [Matrix.mulVec, dotProduct, R, hne, hj] at hj' ⊢
    exact hj'
  · intro j hj
    have hj' := congrFun hRv j
    have hne : j ≠ k := ne_of_lt hj
    have hnot : ¬ k < j := not_lt.mpr hj.le
    simp [Matrix.mulVec, dotProduct, R, hne, hnot, hj] at hj' ⊢
    exact hj'

lemma smo_weyl_core {A B U V : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} {X Y : Fin (N+1) → ℝ}
    (hA : IsEigenSystem A X U) (hB : IsEigenSystem B Y V) (K : ℝ)
    (hK : ∀ x : Fin (N+1) → ℝ, |x ⬝ᵥ ((A - B) *ᵥ x)| ≤ K * (x ⬝ᵥ x)) (k : Fin (N+1)) :
    X k ≤ Y k + K := by
  obtain ⟨x, hx0, hP, hQ⟩ := smo_kernel_exists U V k
  have hxx : 0 < x ⬝ᵥ x := by
    have hz := dotProduct_self_eq_zero (v := x)
    exact lt_of_le_of_ne (by simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i))
      (fun h => hx0 (hz.mp h.symm))
  have hAq := smo_quad_eig hA.orth hA.eig x
  have hBq := smo_quad_eig hB.orth hB.eig x
  have hnU := smo_norm_sq_eig hA.orth x
  have hnV := smo_norm_sq_eig hB.orth x
  have hLA : X k * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
    rw [hAq, hnU, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hkj : k < j
    · rw [hP j hkj]; simp
    · have hjk : j ≤ k := not_lt.mp hkj
      have h1 : X k ≤ X j := hA.anti.antitone hjk
      have h2 : 0 ≤ (Uᵀ *ᵥ x) j ^ 2 := sq_nonneg _
      nlinarith
  have hUB : x ⬝ᵥ (B *ᵥ x) ≤ Y k * (x ⬝ᵥ x) := by
    rw [hBq, hnV, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hjk : j < k
    · rw [hQ j hjk]; simp
    · have hkj : k ≤ j := not_lt.mp hjk
      have h1 : Y j ≤ Y k := hB.anti.antitone hkj
      have h2 : 0 ≤ (Vᵀ *ᵥ x) j ^ 2 := sq_nonneg _
      nlinarith
  have hdecomp : x ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (B *ᵥ x) + x ⬝ᵥ ((A - B) *ᵥ x) := by
    rw [sub_mulVec, dotProduct_sub]; ring
  have hb := (abs_le.mp (hK x)).2
  by_contra hcon
  rw [not_le] at hcon
  have := mul_lt_mul_of_pos_right hcon hxx
  nlinarith

lemma smo_weyl_abs {A B U V : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} {X Y : Fin (N+1) → ℝ}
    (hA : IsEigenSystem A X U) (hB : IsEigenSystem B Y V) (K : ℝ)
    (hK : ∀ x : Fin (N+1) → ℝ, |x ⬝ᵥ ((A - B) *ᵥ x)| ≤ K * (x ⬝ᵥ x)) (k : Fin (N+1)) :
    |X k - Y k| ≤ K := by
  have h1 := smo_weyl_core hA hB K hK k
  have hK' : ∀ x : Fin (N+1) → ℝ, |x ⬝ᵥ ((B - A) *ᵥ x)| ≤ K * (x ⬝ᵥ x) := by
    intro x
    rw [← neg_sub, Matrix.neg_mulVec, dotProduct_neg, abs_neg]
    exact hK x
  have h2 := smo_weyl_core hB hA K hK' k
  rw [abs_le]
  constructor <;> linarith


lemma smo_band_card (c : Fin (N+1)) :
    (Finset.univ.filter (fun t : Fin (N+1) => (c:ℕ) ≤ (t:ℕ) + 1 ∧ (t:ℕ) ≤ (c:ℕ) + 1)).card ≤ 3 := by
  have hsub : (Finset.univ.filter (fun t : Fin (N+1) => (c:ℕ) ≤ (t:ℕ) + 1 ∧ (t:ℕ) ≤ (c:ℕ) + 1)).image
      Fin.val ⊆ ({(c:ℕ) - 1, (c:ℕ), (c:ℕ) + 1} : Finset ℕ) := by
    intro a ha
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨t, ⟨h1, h2⟩, rfl⟩ := ha
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  calc (Finset.univ.filter (fun t : Fin (N+1) => (c:ℕ) ≤ (t:ℕ) + 1 ∧ (t:ℕ) ≤ (c:ℕ) + 1)).card
      = ((Finset.univ.filter (fun t : Fin (N+1) => (c:ℕ) ≤ (t:ℕ) + 1 ∧ (t:ℕ) ≤ (c:ℕ) + 1)).image
          Fin.val).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ ({(c:ℕ) - 1, (c:ℕ), (c:ℕ) + 1} : Finset ℕ).card := Finset.card_le_card hsub
    _ ≤ 3 := Finset.card_le_three

lemma smo_band_l2 (D : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (δ : ℝ)
    (hD0 : ∀ i j : Fin (N+1), ¬((i:ℕ) ≤ (j:ℕ) + 1 ∧ (j:ℕ) ≤ (i:ℕ) + 1) → D i j = 0)
    (hD1 : ∀ i j : Fin (N+1), |D i j| ≤ δ) (x : Fin (N+1) → ℝ) :
    ∑ i, (D *ᵥ x) i ^ 2 ≤ (3 * δ) ^ 2 * ∑ j, x j ^ 2 := by
  classical
  set adj : Fin (N+1) → Fin (N+1) → Prop := fun i j => (i:ℕ) ≤ (j:ℕ) + 1 ∧ (j:ℕ) ≤ (i:ℕ) + 1 with hadj
  have hδ2 : ∀ i j, (D i j) ^ 2 ≤ δ ^ 2 := by
    intro i j
    have h := hD1 i j
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hrow : ∀ i : Fin (N+1), (D *ᵥ x) i ^ 2 ≤
      3 * ∑ j ∈ Finset.univ.filter (fun j => adj i j), δ ^ 2 * x j ^ 2 := by
    intro i
    have hmv : (D *ᵥ x) i = ∑ j ∈ Finset.univ.filter (fun j => adj i j), D i j * x j := by
      rw [Matrix.mulVec, dotProduct, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hp : adj i j
      · simp [hp]
      · simp [hp, hD0 i j hp]
    rw [hmv]
    have hc : ((Finset.univ.filter (fun j => adj i j)).card : ℝ) ≤ 3 := by
      have := smo_band_card (N := N) i
      exact_mod_cast this
    calc (∑ j ∈ Finset.univ.filter (fun j => adj i j), D i j * x j) ^ 2
        ≤ ((Finset.univ.filter (fun j => adj i j)).card : ℝ) *
            ∑ j ∈ Finset.univ.filter (fun j => adj i j), (D i j * x j) ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ 3 * ∑ j ∈ Finset.univ.filter (fun j => adj i j), δ ^ 2 * x j ^ 2 := by
          apply mul_le_mul hc _ (Finset.sum_nonneg fun j _ => sq_nonneg _) (by norm_num)
          refine Finset.sum_le_sum fun j _ => ?_
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right (hδ2 i j) (sq_nonneg _)
  have hswap : ∑ i : Fin (N+1), ∑ j ∈ Finset.univ.filter (fun j => adj i j), x j ^ 2
      = ∑ j : Fin (N+1), ((Finset.univ.filter (fun i => adj i j)).card : ℝ) * x j ^ 2 := by
    have h1 : ∀ i : Fin (N+1), ∑ j ∈ Finset.univ.filter (fun j => adj i j), x j ^ 2
        = ∑ j : Fin (N+1), (if adj i j then x j ^ 2 else (0:ℝ)) := fun i => Finset.sum_filter _ _
    simp only [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard : ∀ j : Fin (N+1), ((Finset.univ.filter (fun i => adj i j)).card : ℝ) ≤ 3 := by
    intro j
    have hfeq : Finset.univ.filter (fun i => adj i j) =
        Finset.univ.filter (fun t : Fin (N+1) => (j:ℕ) ≤ (t:ℕ) + 1 ∧ (t:ℕ) ≤ (j:ℕ) + 1) := by
      refine Finset.filter_congr fun i _ => ?_
      simp only [hadj]
      exact and_comm
    rw [hfeq]
    exact_mod_cast smo_band_card (N := N) j
  calc ∑ i, (D *ᵥ x) i ^ 2
      ≤ ∑ i, 3 * ∑ j ∈ Finset.univ.filter (fun j => adj i j), δ ^ 2 * x j ^ 2 :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = 3 * δ ^ 2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => adj i j), x j ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum]
        ring
    _ = 3 * δ ^ 2 * ∑ j : Fin (N+1), ((Finset.univ.filter (fun i => adj i j)).card : ℝ) * x j ^ 2 := by
        rw [hswap]
    _ ≤ 3 * δ ^ 2 * ∑ j : Fin (N+1), 3 * x j ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_right (hcard j) (sq_nonneg _)
    _ = (3 * δ) ^ 2 * ∑ j, x j ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring


lemma smo_quad_of_l2 (D : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (K : ℝ) (hK : 0 < K)
    (hD : ∀ x : Fin (N+1) → ℝ, ∑ i, (D *ᵥ x) i ^ 2 ≤ K ^ 2 * ∑ i, x i ^ 2) (x : Fin (N+1) → ℝ) :
    |x ⬝ᵥ (D *ᵥ x)| ≤ K * (x ⬝ᵥ x) := by
  set y := D *ᵥ x with hy
  have hterm : ∀ i, 2 * K * |x i * y i| ≤ K ^ 2 * x i ^ 2 + y i ^ 2 := by
    intro i
    rcases abs_cases (x i * y i) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
      nlinarith [sq_nonneg (K * x i - y i), sq_nonneg (K * x i + y i)]
  have h1 : ∑ i, 2 * K * |x i * y i| ≤ ∑ i, (K ^ 2 * x i ^ 2 + y i ^ 2) :=
    Finset.sum_le_sum fun i _ => hterm i
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
  have hy2 : ∑ i, y i ^ 2 ≤ K ^ 2 * ∑ i, x i ^ 2 := hD x
  have hA : ∑ i, |x i * y i| ≤ K * ∑ i, x i ^ 2 := by
    have h2 : 2 * K * ∑ i, |x i * y i| ≤ 2 * K * (K * ∑ i, x i ^ 2) := by nlinarith [h1, hy2]
    exact le_of_mul_le_mul_left h2 (by positivity)
  have hxy : |x ⬝ᵥ y| ≤ ∑ i, |x i * y i| := by
    unfold dotProduct
    exact Finset.abs_sum_le_sum_abs _ _
  have hxx : x ⬝ᵥ x = ∑ i, x i ^ 2 := by
    unfold dotProduct
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hxx]
  exact le_trans hxy hA


/-- Perturbation of a square root: if `p > 0`, `p <= L^2/4`, `T >= g/2`, `G >= 0` and `|G - T| <= R`, then
`|sqrt(pG) - sqrt(pT)| <= L R / (2 sqrt(g/2))`. -/
lemma smo_sqrt_perturb (p T G L g R : ℝ) (hL : 0 ≤ L) (hp : 0 < p) (hpL : p ≤ L ^ 2 / 4) (hg : 0 < g) (hT : g / 2 ≤ T)
    (hG : 0 ≤ G) (hGT : |G - T| ≤ R) :
    |Real.sqrt (p * G) - Real.sqrt (p * T)| ≤ L * R / (2 * Real.sqrt (g / 2)) := by
  have hTpos : 0 < T := by linarith
  have hR0 : 0 ≤ R := le_trans (abs_nonneg _) hGT
  have ha : 0 ≤ Real.sqrt (p * G) := Real.sqrt_nonneg _
  have hb : 0 < Real.sqrt (p * T) := Real.sqrt_pos.mpr (mul_pos hp hTpos)
  have hab : (Real.sqrt (p * G) - Real.sqrt (p * T)) * (Real.sqrt (p * G) + Real.sqrt (p * T))
      = p * (G - T) := by
    have h1 : Real.sqrt (p * G) ^ 2 = p * G := Real.sq_sqrt (mul_nonneg hp.le hG)
    have h2 : Real.sqrt (p * T) ^ 2 = p * T := Real.sq_sqrt (mul_nonneg hp.le hTpos.le)
    linear_combination h1 - h2
  have hq : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have hqL : Real.sqrt p ≤ L / 2 := by
    have h1 : p ≤ (L / 2) ^ 2 := by nlinarith
    calc Real.sqrt p ≤ Real.sqrt ((L / 2) ^ 2) := Real.sqrt_le_sqrt h1
      _ = L / 2 := Real.sqrt_sq (by nlinarith)
  have hc : 0 < Real.sqrt (g / 2) := Real.sqrt_pos.mpr (by linarith)
  have hlb : Real.sqrt p * Real.sqrt (g / 2) ≤ Real.sqrt (p * T) := by
    rw [← Real.sqrt_mul hp.le]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hT hp.le)
  have hmain : |Real.sqrt (p * G) - Real.sqrt (p * T)| * Real.sqrt (p * T) ≤ p * R := by
    have h1 : |Real.sqrt (p * G) - Real.sqrt (p * T)| * (Real.sqrt (p * G) + Real.sqrt (p * T))
        = p * |G - T| := by
      rw [← abs_of_nonneg (show 0 ≤ Real.sqrt (p * G) + Real.sqrt (p * T) by linarith), ← abs_mul, hab,
        abs_mul, abs_of_pos hp]
    have h2 : |Real.sqrt (p * G) - Real.sqrt (p * T)| * Real.sqrt (p * T)
        ≤ |Real.sqrt (p * G) - Real.sqrt (p * T)| * (Real.sqrt (p * G) + Real.sqrt (p * T)) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    rw [h1] at h2
    nlinarith
  have h2 : |Real.sqrt (p * G) - Real.sqrt (p * T)| * (Real.sqrt p * Real.sqrt (g / 2)) ≤ p * R :=
    le_trans (mul_le_mul_of_nonneg_left hlb (abs_nonneg _)) hmain
  have hpp : p = Real.sqrt p * Real.sqrt p := (Real.mul_self_sqrt hp.le).symm
  have h3 : |Real.sqrt (p * G) - Real.sqrt (p * T)| * Real.sqrt (g / 2) ≤ Real.sqrt p * R := by
    have h4 : (|Real.sqrt (p * G) - Real.sqrt (p * T)| * Real.sqrt (g / 2)) * Real.sqrt p
        ≤ (Real.sqrt p * R) * Real.sqrt p := by
      nlinarith [h2, hpp]
    exact le_of_mul_le_mul_right h4 hq
  have h5 : Real.sqrt p * R ≤ L / 2 * R := mul_le_mul_of_nonneg_right hqL hR0
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- Truncation bound on the symbol: for `0 < h <= 1` and `s` in `[0, L]`, `|sum_{j<=M} h^j G_j(s) - G_0(s)| <= h * KG`,
where `KG` bounds the jets `G_1, ..., G_M` on `[0, L]`. -/
lemma smo_jet_trunc (f : ℕ → ℝ → ℝ) (M : ℕ) (Kf : ℕ → ℝ) (L : ℝ) (h : ℝ) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hKf : ∀ j ≤ M, ∀ s ∈ Set.Icc 0 L, |f j s| ≤ Kf j) (s : ℝ) (hs : s ∈ Set.Icc 0 L) :
    |∑ j ∈ Finset.range (M + 1), h ^ j * f j s - f 0 s| ≤ h * ∑ j ∈ Finset.range (M + 1), |Kf j| := by
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul]
  have hcancel : ∑ j ∈ Finset.range M, h ^ (j + 1) * f (j + 1) s + f 0 s - f 0 s
      = ∑ j ∈ Finset.range M, h ^ (j + 1) * f (j + 1) s := by ring
  rw [hcancel]
  calc |∑ j ∈ Finset.range M, h ^ (j + 1) * f (j + 1) s|
      ≤ ∑ j ∈ Finset.range M, |h ^ (j + 1) * f (j + 1) s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range M, h * |Kf (j + 1)| := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjM : j + 1 ≤ M := by
          have := Finset.mem_range.mp hj
          omega
        rw [abs_mul, abs_of_pos (pow_pos hh0 _)]
        have hpow : h ^ (j + 1) ≤ h := pow_le_of_le_one hh0.le hh1 (Nat.succ_ne_zero j)
        exact mul_le_mul hpow (le_trans (hKf (j + 1) hjM s hs) (le_abs_self _)) (abs_nonneg _) hh0.le
    _ ≤ h * ∑ j ∈ Finset.range (M + 1), |Kf j| := by
        rw [← Finset.mul_sum, Finset.sum_range_succ' (fun j => |Kf j|)]
        apply mul_le_mul_of_nonneg_left _ hh0.le
        linarith [abs_nonneg (Kf 0)]


/-- The truncated family `tilde J_h^{[M]}` of eq:l2-tilde (jets completed by zero beyond `M`, no remainder).  The same family as
`TheoremA.truncFamily` of `Statements.lean`, restated here so that this module does not depend on the statement freeze. -/
def truncSM {Par : Type*} (F : SymbolFamily Par) (M : ℕ) : SymbolFamily Par where
  L := F.L
  L_pos := F.L_pos
  Gh := fun μ h s => ∑ j ∈ Finset.range (M + 1), h ^ j * F.G j μ s
  Bh := fun μ h u => ∑ j ∈ Finset.range (M + 1), h ^ j * F.B j μ u
  G := fun j μ s => if j ≤ M then F.G j μ s else 0
  B := fun j μ s => if j ≤ M then F.B j μ s else 0


/-- **lem:smo-SM** (finite smooth jets and weighted hard edges), for one parameter `mu`; see the module docstring for the
exact form.  `J = F.jacobiMat mu N` is `J_h` with the symbols `E_n = s_n(L-s_n) G_h(s_n)`, `B_n = B_h(u_n)`; `truncSM F M`
is `tilde J_h^{[M]}` (jets completed by zero, `r = q = 0`).  Conclusions, for all `N` with `h = L/(N+1) <= h_0`:
(a) the bonds of `J` and of `tilde J` are positive; (b) `||J - tilde J||_op <= C' h^{M+1}` (in the form `sum_i ((J-tilde J)x)_i^2 <= (C' h^{M+1})^2 sum_i x_i^2`);
(c) every ordered eigenvalue of `J` and of `tilde J` (`IsEigenSystem`, decreasing order) changes by at most `C' h^{M+1}`. -/
theorem smo_SM {Par : Type*} (F : SymbolFamily Par) (Kset : Set Par) (M : ℕ) (gstar : ℝ) (hgstar : 0 < gstar)
    (hG0 : ∀ μ ∈ Kset, ∀ s ∈ Set.Icc 0 F.L, gstar ≤ F.G 0 μ s)
    (hGbdd : ∀ j ≤ M, ∃ K : ℝ, ∀ μ ∈ Kset, ∀ s ∈ Set.Icc 0 F.L, |F.G j μ s| ≤ K)
    (C : ℝ)
    (hrG : ∀ μ ∈ Kset, ∀ N : ℕ, ∀ n : ℤ, 0 ≤ n → n < N →
      |F.Gh μ (F.step N) (sNode (F.step N) n) -
        ∑ j ∈ Finset.range (M + 1), F.step N ^ j * F.G j μ (sNode (F.step N) n)| ≤ C * F.step N ^ (M + 1))
    (hrB : ∀ μ ∈ Kset, ∀ N : ℕ, ∀ n : ℤ, 0 ≤ n → n ≤ N →
      |F.Bh μ (F.step N) (uNode (F.step N) n) -
        ∑ j ∈ Finset.range (M + 1), F.step N ^ j * F.B j μ (uNode (F.step N) n)| ≤ C * F.step N ^ (M + 1)) :
    ∃ C' h0 : ℝ, 0 < C' ∧ 0 < h0 ∧ ∀ μ ∈ Kset, ∀ N : ℕ, F.step N ≤ h0 →
      (∀ n : ℤ, 0 ≤ n → n < N → 0 < F.bondA μ N n ∧ 0 < (truncSM F M).bondA μ N n) ∧
      (∀ x : Fin (N + 1) → ℝ,
        ∑ i, ((F.jacobiMat μ N - (truncSM F M).jacobiMat μ N) *ᵥ x) i ^ 2 ≤
          (C' * F.step N ^ (M + 1)) ^ 2 * ∑ i, x i ^ 2) ∧
      (∀ (X X' : Fin (N + 1) → ℝ) (U U' : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
        IsEigenSystem (F.jacobiMat μ N) X U → IsEigenSystem ((truncSM F M).jacobiMat μ N) X' U' →
        ∀ k : Fin (N + 1), |X k - X' k| ≤ C' * F.step N ^ (M + 1)) := by
  classical
  choose! Kf hKf using hGbdd
  have hL : 0 < F.L := F.L_pos
  set KG : ℝ := ∑ j ∈ Finset.range (M + 1), |Kf j| with hKG
  have hKG0 : 0 ≤ KG := Finset.sum_nonneg fun j _ => abs_nonneg _
  set C0 : ℝ := max C 0 with hC0
  have hC0nn : 0 ≤ C0 := le_max_right _ _
  have hCC0 : C ≤ C0 := le_max_left _ _
  set Ca : ℝ := F.L * C0 / (2 * Real.sqrt (gstar / 2)) with hCa
  have hCa0 : 0 ≤ Ca := by
    rw [hCa]
    exact div_nonneg (mul_nonneg hL.le hC0nn) (by positivity)
  set K0 : ℝ := C0 + Ca + 1 with hK0
  have hK0pos : 0 < K0 := by rw [hK0]; linarith
  set C' : ℝ := 3 * K0 with hC'
  have hC'pos : 0 < C' := by rw [hC']; linarith
  set h0 : ℝ := min (min 1 (gstar / (2 * (KG + 1)))) (gstar / (4 * (C0 + 1))) with hh0
  have hh0pos : 0 < h0 :=
    lt_min (lt_min one_pos (div_pos hgstar (by linarith))) (div_pos hgstar (by linarith))
  refine ⟨C', h0, hC'pos, hh0pos, ?_⟩
  intro μ hμ N hN
  have hh1' : F.step N ≤ 1 := le_trans hN (le_trans (min_le_left _ _) (min_le_left _ _))
  have hhKG' : F.step N ≤ gstar / (2 * (KG + 1)) :=
    le_trans hN (le_trans (min_le_left _ _) (min_le_right _ _))
  have hhC0' : F.step N ≤ gstar / (4 * (C0 + 1)) := le_trans hN (min_le_right _ _)
  have hhpos : 0 < F.step N := FormalResearch.JB.stepSize_pos hL N
  have hLh : F.L = F.step N * ((N : ℝ) + 1) := by
    unfold SymbolFamily.step FormalResearch.JB.stepSize
    have : (0:ℝ) < (N:ℝ) + 1 := by positivity
    field_simp
  set h := F.step N with hh
  have hhKG : h * KG ≤ gstar / 2 := by
    have h2 := (le_div_iff₀ (by linarith : (0:ℝ) < 2 * (KG + 1))).mp hhKG'
    nlinarith
  have hhC0 : C0 * h ≤ gstar / 4 := by
    have h2 := (le_div_iff₀ (by linarith : (0:ℝ) < 4 * (C0 + 1))).mp hhC0'
    nlinarith
  have hpowle : h ^ (M + 1) ≤ h := pow_le_of_le_one hhpos.le hh1' (Nat.succ_ne_zero M)
  have hpow0 : 0 ≤ h ^ (M + 1) := pow_nonneg hhpos.le _
  have hC0pow : C0 * h ^ (M + 1) ≤ gstar / 4 :=
    le_trans (mul_le_mul_of_nonneg_left hpowle hC0nn) hhC0
  -- nodes
  have hnode : ∀ n : ℤ, 0 ≤ n → n < N → 0 < sNode h n ∧ sNode h n < F.L := by
    intro n hn0 hnN
    have hn' : (n : ℝ) + 1 ≤ (N : ℝ) := by
      have : n + 1 ≤ (N : ℤ) := by omega
      exact_mod_cast this
    have hn0' : (0 : ℝ) ≤ n := by exact_mod_cast hn0
    constructor
    · unfold sNode
      exact mul_pos (by linarith) hhpos
    · unfold sNode
      rw [hLh]
      nlinarith
  have hpos_p : ∀ n : ℤ, 0 ≤ n → n < N → 0 < sNode h n * (F.L - sNode h n) := fun n h1 h2 =>
    mul_pos (hnode n h1 h2).1 (by linarith [(hnode n h1 h2).2])
  have hpL : ∀ n : ℤ, 0 ≤ n → n < N → sNode h n * (F.L - sNode h n) ≤ F.L ^ 2 / 4 := fun n _ _ => by
    nlinarith [sq_nonneg (F.L / 2 - sNode h n)]
  have hsrange : ∀ n : ℤ, 0 ≤ n → n < N → sNode h n ∈ Set.Icc 0 F.L := fun n h1 h2 =>
    ⟨(hnode n h1 h2).1.le, (hnode n h1 h2).2.le⟩
  -- truncated symbol
  have hTlow : ∀ n : ℤ, 0 ≤ n → n < N →
      gstar / 2 ≤ ∑ j ∈ Finset.range (M + 1), h ^ j * F.G j μ (sNode h n) := by
    intro n h1 h2
    have hb := smo_jet_trunc (fun j s => F.G j μ s) M Kf F.L h hhpos hh1'
      (fun j hj s hs => hKf j hj μ hμ s hs) (sNode h n) (hsrange n h1 h2)
    have hbd : |∑ j ∈ Finset.range (M + 1), h ^ j * F.G j μ (sNode h n) - F.G 0 μ (sNode h n)| ≤ gstar / 2 :=
      le_trans hb hhKG
    have hG := hG0 μ hμ (sNode h n) (hsrange n h1 h2)
    linarith [(abs_le.mp hbd).1]
  -- full symbol
  have hGfull : ∀ n : ℤ, 0 ≤ n → n < N →
      |F.Gh μ h (sNode h n) - ∑ j ∈ Finset.range (M + 1), h ^ j * F.G j μ (sNode h n)| ≤ C0 * h ^ (M + 1) := by
    intro n h1 h2
    calc |F.Gh μ h (sNode h n) - ∑ j ∈ Finset.range (M + 1), h ^ j * F.G j μ (sNode h n)|
        ≤ C * h ^ (M + 1) := hrG μ hμ N n h1 h2
      _ ≤ C0 * h ^ (M + 1) := mul_le_mul_of_nonneg_right hCC0 hpow0
  have hGlow : ∀ n : ℤ, 0 ≤ n → n < N → gstar / 4 ≤ F.Gh μ h (sNode h n) := by
    intro n h1 h2
    have hT := hTlow n h1 h2
    have hd := (abs_le.mp (hGfull n h1 h2)).1
    linarith [hC0pow]
  have hGnn : ∀ n : ℤ, 0 ≤ n → n < N → 0 ≤ F.Gh μ h (sNode h n) := fun n h1 h2 => by
    linarith [hGlow n h1 h2]
  -- entries and bonds
  have hEF : ∀ n : ℤ, F.entryE μ N n = sNode h n * (F.L - sNode h n) * F.Gh μ h (sNode h n) :=
    fun n => rfl
  have hETr : ∀ n : ℤ, (truncSM F M).entryE μ N n =
      sNode h n * (F.L - sNode h n) * ∑ j ∈ Finset.range (M + 1), h ^ j * F.G j μ (sNode h n) :=
    fun n => rfl
  have hBA : ∀ n : ℤ, 0 ≤ n → n < N → F.bondA μ N n = Real.sqrt (F.entryE μ N n) := fun n h1 h2 => by
    unfold SymbolFamily.bondA
    simp [h1, h2]
  have hBAt : ∀ n : ℤ, 0 ≤ n → n < N →
      (truncSM F M).bondA μ N n = Real.sqrt ((truncSM F M).entryE μ N n) := fun n h1 h2 => by
    unfold SymbolFamily.bondA
    simp [h1, h2]
  have hbond : ∀ n : ℤ, 0 ≤ n → n < N →
      |F.bondA μ N n - (truncSM F M).bondA μ N n| ≤ Ca * h ^ (M + 1) := by
    intro n h1 h2
    rw [hBA n h1 h2, hBAt n h1 h2, hEF n, hETr n]
    have key := smo_sqrt_perturb (sNode h n * (F.L - sNode h n))
      (∑ j ∈ Finset.range (M + 1), h ^ j * F.G j μ (sNode h n)) (F.Gh μ h (sNode h n)) F.L gstar
      (C0 * h ^ (M + 1)) hL.le (hpos_p n h1 h2) (hpL n h1 h2) hgstar (hTlow n h1 h2) (hGnn n h1 h2)
      (hGfull n h1 h2)
    calc _ ≤ F.L * (C0 * h ^ (M + 1)) / (2 * Real.sqrt (gstar / 2)) := key
      _ = Ca * h ^ (M + 1) := by rw [hCa]; ring
  have hEpos : ∀ n : ℤ, 0 ≤ n → n < N → 0 < F.entryE μ N n := fun n h1 h2 => by
    rw [hEF n]
    exact mul_pos (hpos_p n h1 h2) (by linarith [hGlow n h1 h2])
  have hEtpos : ∀ n : ℤ, 0 ≤ n → n < N → 0 < (truncSM F M).entryE μ N n := fun n h1 h2 => by
    rw [hETr n]
    exact mul_pos (hpos_p n h1 h2) (by linarith [hTlow n h1 h2])
  -- the difference matrix
  have hDentry : ∀ i j : Fin (N + 1), (F.jacobiMat μ N - (truncSM F M).jacobiMat μ N) i j =
      if i = j then (F.entryB μ N ((i : ℕ) : ℤ) - (truncSM F M).entryB μ N ((i : ℕ) : ℤ))
      else if (j : ℕ) = (i : ℕ) + 1 then
        (F.bondA μ N ((i : ℕ) : ℤ) - (truncSM F M).bondA μ N ((i : ℕ) : ℤ))
      else if (i : ℕ) = (j : ℕ) + 1 then
        (F.bondA μ N ((j : ℕ) : ℤ) - (truncSM F M).bondA μ N ((j : ℕ) : ℤ))
      else 0 := by
    intro i j
    simp only [Matrix.sub_apply, SymbolFamily.jacobiMat, Matrix.of_apply]
    split_ifs <;> ring
  have hDzero : ∀ i j : Fin (N + 1),
      ¬((i : ℕ) ≤ (j : ℕ) + 1 ∧ (j : ℕ) ≤ (i : ℕ) + 1) →
        (F.jacobiMat μ N - (truncSM F M).jacobiMat μ N) i j = 0 := by
    intro i j hadj
    rw [hDentry]
    split_ifs with h1 h2 h3
    · exfalso; apply hadj; subst h1; omega
    · exfalso; apply hadj; omega
    · exfalso; apply hadj; omega
    · rfl
  have hDbound : ∀ i j : Fin (N + 1),
      |(F.jacobiMat μ N - (truncSM F M).jacobiMat μ N) i j| ≤ K0 * h ^ (M + 1) := by
    intro i j
    have hK0h : 0 ≤ K0 * h ^ (M + 1) := mul_nonneg hK0pos.le hpow0
    rw [hDentry]
    split_ifs with h1 h2 h3
    · subst h1
      have hi : ((i : ℕ) : ℤ) ≤ (N : ℤ) := by have := i.isLt; omega
      have hd := hrB μ hμ N ((i : ℕ) : ℤ) (by positivity) hi
      change |F.Bh μ h (uNode h ((i : ℕ) : ℤ)) -
        ∑ j ∈ Finset.range (M + 1), h ^ j * F.B j μ (uNode h ((i : ℕ) : ℤ))| ≤ K0 * h ^ (M + 1)
      calc _ ≤ C * h ^ (M + 1) := hd
        _ ≤ C0 * h ^ (M + 1) := mul_le_mul_of_nonneg_right hCC0 hpow0
        _ ≤ K0 * h ^ (M + 1) := mul_le_mul_of_nonneg_right (by linarith) hpow0
    · have hi : ((i : ℕ) : ℤ) < (N : ℤ) := by have := j.isLt; omega
      have hb := hbond ((i : ℕ) : ℤ) (by positivity) hi
      calc _ ≤ Ca * h ^ (M + 1) := hb
        _ ≤ K0 * h ^ (M + 1) := mul_le_mul_of_nonneg_right (by linarith) hpow0
    · have hi : ((j : ℕ) : ℤ) < (N : ℤ) := by have := i.isLt; omega
      have hb := hbond ((j : ℕ) : ℤ) (by positivity) hi
      calc _ ≤ Ca * h ^ (M + 1) := hb
        _ ≤ K0 * h ^ (M + 1) := mul_le_mul_of_nonneg_right (by linarith) hpow0
    · simpa using hK0h
  -- the ell-2 bound and the eigenvalue bound
  have hl2 : ∀ x : Fin (N + 1) → ℝ,
      ∑ i, ((F.jacobiMat μ N - (truncSM F M).jacobiMat μ N) *ᵥ x) i ^ 2 ≤
        (C' * h ^ (M + 1)) ^ 2 * ∑ i, x i ^ 2 := by
    intro x
    have hb := smo_band_l2 (F.jacobiMat μ N - (truncSM F M).jacobiMat μ N) (K0 * h ^ (M + 1))
      hDzero hDbound x
    calc _ ≤ (3 * (K0 * h ^ (M + 1))) ^ 2 * ∑ i, x i ^ 2 := hb
      _ = (C' * h ^ (M + 1)) ^ 2 * ∑ i, x i ^ 2 := by rw [hC']; ring
  refine ⟨?_, hl2, ?_⟩
  · intro n h1 h2
    refine ⟨?_, ?_⟩
    · rw [hBA n h1 h2]
      exact Real.sqrt_pos.mpr (hEpos n h1 h2)
    · rw [hBAt n h1 h2]
      exact Real.sqrt_pos.mpr (hEtpos n h1 h2)
  · intro X X' U U' hA hB k
    have hK : ∀ x : Fin (N + 1) → ℝ,
        |x ⬝ᵥ ((F.jacobiMat μ N - (truncSM F M).jacobiMat μ N) *ᵥ x)| ≤ (C' * h ^ (M + 1)) * (x ⬝ᵥ x) :=
      fun x => smo_quad_of_l2 (F.jacobiMat μ N - (truncSM F M).jacobiMat μ N) (C' * h ^ (M + 1))
        (mul_pos hC'pos (pow_pos hhpos _)) hl2 x
    exact smo_weyl_abs hA hB (C' * h ^ (M + 1)) hK k

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.smo_SM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.smo_SM

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.smo_weyl_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.smo_weyl_abs

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.smo_band_l2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.smo_band_l2

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.smo_quad_of_l2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.smo_quad_of_l2

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.smo_sqrt_perturb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.smo_sqrt_perturb

end FormalResearch.JacobiEigenvectors.TheoremA

end
