module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftItem1
public import FormalResearch.JacobiEigenvectors.Setting.EigenSystem
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkNormalisation

/-!
# Paper J, Layer 2 (L2.C7): the routine algebra of `prop:tha-W2` (2), (3) (chain steps E1, E2, E5, E7)

Source: `app_thmA.tex` "The soft edges: proof of Proposition prop:tha-W2", Step 4 (first paragraph: `psi^L = kappa psi^R` and `Psi = psi^L/||psi^L||`), the "mirror statement" used throughout (item (1) for `psi^R`),
and `Charts/SoftParabolicCylinder.lean` (`SoftMirror`).

## Proved here (all axiom-pinned)

* **E1** (the recurrence, general `A, Q : Z -> R`): `rec_fwd_unique` (a solution of the recurrence on rows `0 <= n < R` with `A_n != 0` is determined by `f_0`), `rec_bwd_unique` (a solution on rows `1 <= m <= R'` with `A_{m-1} != 0` and
  `g_{R'} = 0 = g_{R'+1}` vanishes), `eig_eq_normalised` (an eigen-system column with `Psi_0 > 0` is `psi/||psi||` for every solution `psi` of rows `0 <= n < N` with `psi_0 > 0`, if `0 < a_n` for `n < N`), and `eig_eq_kappa_mul`
  (`psi^L = kappa psi^R` on `0..N` for the eigen column and a solution `psi^R` of rows `1..N`, `psi^R_N != 0`), and the combination `psiL_eq_kappa_psiR` with the mirror transport (`psi^R_n := psi'_{N-n}`, `psi'` seeded for the mirror family).
* **E2** (mirror transport; `uNode_mirror`, `bondA_mirror`, `diagQ_mirror`, `lop_mirror` are those of `BulkNormalisation.lean`): `jacSol_mirror` (`JacSol (mirrorFamily F) mu N X R psi'` implies the recurrence of `F` for `n -> psi'(N - n)` on
  `N - R < m <= N`), `bandHi_mirror` (`X_s^+` of the mirror family is that of the family), and, for `SoftMirror CL CR`, `Zof_mirror` (`Z_R(N - n) = -Z_L(n)`), `aOf_mirror` (`a_R = a_L`).

* **E5, E7** (abstract `l^2` lemmas, independent of the charts): `abs_sum_mul_le_sqrt`, `sqrt_sum_add_le` (Minkowski), `abs_sqrt_sub_le`, `glueKappa_sub_le` (`|hat kappa - kappa| <= ||a - kappa b|| / ||b||`, Step 4 (b)),
  `normalised_error` (`|psi/||psi|| - psi^/||psi^||| <= (2 + 2 C sqrt Cs) eps V/||psi^||` from `|psi - psi^| <= eps V`, `|psi^| <= C V`, `sum V^2 <= Cs ||psi^||^2`, `eps sqrt Cs <= 1/2`, Step 4 (e)).

## Not formalised

The rest of the chain E3--E9 of `PLAN.md` (L2.C7): envelopes on `Omega`, mass bounds (`PropThaWin`, `PropThaM`), tails, normalisation, quantisation, counting.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts
  FormalResearch.JacobiEigenvectors.Engine
open scoped Matrix

/-! ### E1: the recurrence -/

lemma Lop_sub_smul (A Q f r : ℤ → ℝ) (c : ℝ) (n : ℤ) :
    Lop A Q (fun k => f k - c * r k) n = Lop A Q f n - c * Lop A Q r n := by
  unfold Lop; ring

lemma Lop_smul' (A Q f : ℤ → ℝ) (c : ℝ) (n : ℤ) : Lop A Q (fun k => c * f k) n = c * Lop A Q f n := by
  unfold Lop; ring

/-- forward uniqueness: with `A (-1) = 0`, a solution of `Lop A Q f n = 0` for `0 <= n < R` and `A n != 0` is determined by `f 0`. -/
theorem rec_fwd_unique (A Q f g : ℤ → ℝ) (R : ℤ) (hA : ∀ n : ℤ, 0 ≤ n → n < R → A n ≠ 0) (hA0 : A (-1) = 0)
    (hf : ∀ n : ℤ, 0 ≤ n → n < R → Lop A Q f n = 0) (hg : ∀ n : ℤ, 0 ≤ n → n < R → Lop A Q g n = 0) (h0 : f 0 = g 0) :
    ∀ n : ℤ, 0 ≤ n → n ≤ R → f n = g n := by
  have key : ∀ k : ℕ, 1 ≤ k → (k : ℤ) ≤ R → f k = g k ∧ f ((k : ℤ) - 1) = g ((k : ℤ) - 1) := by
    intro k hk1
    induction k, hk1 using Nat.le_induction with
    | base =>
      intro hR
      have hAk := hA 0 le_rfl (by omega)
      have e1 := hf 0 le_rfl (by omega)
      have e2 := hg 0 le_rfl (by omega)
      unfold Lop at e1 e2
      have hm1 : ((0 : ℤ) - 1) = -1 := by norm_num
      rw [hm1, hA0] at e1 e2
      refine ⟨?_, by simpa using h0⟩
      simp only [Nat.cast_one]
      have h1 : A 0 * f 1 = Q 0 * f 0 := by
        have : (0 : ℤ) + 1 = 1 := by norm_num
        rw [this] at e1; linarith
      have h2 : A 0 * g 1 = Q 0 * g 0 := by
        have : (0 : ℤ) + 1 = 1 := by norm_num
        rw [this] at e2; linarith
      have : A 0 * f 1 = A 0 * g 1 := by rw [h1, h2, h0]
      exact mul_left_cancel₀ hAk this
    | succ k hk ih =>
      intro hR
      obtain ⟨ihk, ihk1⟩ := ih (by omega)
      have hAk := hA k (by omega) (by omega)
      have e1 := hf k (by omega) (by omega)
      have e2 := hg k (by omega) (by omega)
      unfold Lop at e1 e2
      have hnew : f ((k : ℤ) + 1) = g ((k : ℤ) + 1) := by
        have : A k * f ((k : ℤ) + 1) = A k * g ((k : ℤ) + 1) := by
          rw [ihk1] at e1
          rw [ihk] at e1
          linarith
        exact mul_left_cancel₀ hAk this
      refine ⟨by push_cast; exact hnew, by push_cast; simpa using ihk⟩
  intro n hn0 hnR
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn0
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using h0
  · exact (key k hk hnR).1

/-- backward uniqueness: if `A T = 0`, `g T = 0`, `A (m-1) != 0` and `Lop A Q g m = 0` for `1 <= m <= T`, then `g m = 0` for `0 <= m <= T`. -/
theorem rec_bwd_unique (A Q g : ℤ → ℝ) (T : ℕ) (hAT : A T = 0) (hgT : g T = 0)
    (hA : ∀ m : ℤ, 1 ≤ m → m ≤ T → A (m - 1) ≠ 0) (hg : ∀ m : ℤ, 1 ≤ m → m ≤ T → Lop A Q g m = 0) :
    ∀ m : ℤ, 0 ≤ m → m ≤ T → g m = 0 := by
  have key : ∀ j : ℕ, j ≤ T → g ((T : ℤ) - j) = 0 ∧ A ((T : ℤ) - j) * g ((T : ℤ) - j + 1) = 0 := by
    intro j
    induction j with
    | zero => intro _; simp [hgT, hAT]
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hrow := hg ((T : ℤ) - j) (by omega) (by omega)
      have hAm := hA ((T : ℤ) - j) (by omega) (by omega)
      unfold Lop at hrow
      rw [h1] at hrow
      have : A ((T : ℤ) - j - 1) * g ((T : ℤ) - j - 1) = 0 := by
        have e : A ((T : ℤ) - j) * g ((T : ℤ) - j + 1) = 0 := h2
        linarith
      have hz : g ((T : ℤ) - j - 1) = 0 := by
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hAm
        · exact h
      have e1 : ((T : ℤ) - ((j + 1 : ℕ) : ℤ)) = (T : ℤ) - j - 1 := by push_cast; ring
      have e3 : (T : ℤ) - j - 1 + 1 = (T : ℤ) - j := by ring
      rw [e1, e3, h1]
      exact ⟨hz, by ring⟩
  intro m hm0 hmT
  have := (key (T - m.toNat) (by omega)).1
  have e : (T : ℤ) - ((T - m.toNat : ℕ) : ℤ) = m := by omega
  rwa [e] at this

/-- `psi^L = kappa psi^R` at an eigenvalue (E1): `f` solves the recurrence on all rows `0 <= n <= N` (an eigen column), `r` on the rows `1 <= m <= N`, `A N = 0`, `A n != 0` for `0 <= n < N`, `r N != 0`; then `f = (f N / r N) r` on `0..N`. -/
theorem eig_eq_kappa_mul (A Q f r : ℤ → ℝ) (N : ℕ) (hAN : A N = 0) (hA : ∀ n : ℤ, 0 ≤ n → n < N → A n ≠ 0)
    (hf : ∀ n : ℤ, 0 ≤ n → n ≤ N → Lop A Q f n = 0) (hr : ∀ m : ℤ, 1 ≤ m → m ≤ N → Lop A Q r m = 0) (hrN : r N ≠ 0) :
    ∀ n : ℤ, 0 ≤ n → n ≤ N → f n = f N / r N * r n := by
  have hz := rec_bwd_unique A Q (fun k => f k - f N / r N * r k) N hAN (by simp [hrN])
    (fun m hm1 hmN => hA (m - 1) (by omega) (by omega))
    (fun m hm1 hmN => by rw [Lop_sub_smul, hf m (by omega) hmN, hr m hm1 hmN]; ring)
  intro n hn0 hnN
  have : f n - f N / r N * r n = 0 := hz n hn0 hnN
  linarith

/-- **E1: the eigen column is the normalised exact solution.**  If `0 < a_n` for `0 <= n < N` and `psi` solves the recurrence on the rows `0 <= n < N` with `psi_0 > 0`, then the column of an eigen-system is
`psi / ||psi||` on `0..N` (the gauge `(Psi_k)_0 > 0`). -/
theorem eig_eq_normalised {Par : Type*} (F : SymbolFamily Par) (μ : Par) (N : ℕ)
    (hpos : ∀ n : ℤ, 0 ≤ n → n < N → 0 < F.bondA μ N n) (Xs : Fin (N + 1) → ℝ)
    (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hE : IsEigenSystem (F.jacobiMat μ N) Xs Um) (k : Fin (N + 1))
    (ψ : ℤ → ℝ) (hψ : JacSol F μ N (Xs k) N ψ) (hψ0 : 0 < ψ 0) :
    ∀ n ∈ rowsOf N, eigVec Um k n = ψ n / Real.sqrt (∑ n ∈ rowsOf N, ψ n ^ 2) := by
  have hJ := eigVec_JacSol F μ N Xs Um hE k
  have hA0 : F.bondA μ N (-1) = 0 := by
    unfold SymbolFamily.bondA
    rw [if_neg (by omega)]
  have hP0 : 0 < eigVec Um k 0 := by
    unfold eigVec
    rw [dif_pos ⟨le_rfl, by omega⟩]
    exact hE.pos k
  set c : ℝ := eigVec Um k 0 / ψ 0 with hc
  have hcpos : 0 < c := div_pos hP0 hψ0
  have hcs : ∀ n : ℤ, 0 ≤ n → n ≤ N → eigVec Um k n = c * ψ n := by
    intro n hn0 hnN
    refine rec_fwd_unique (F.bondA μ N) (F.diagQ μ N (Xs k)) (eigVec Um k) (fun n => c * ψ n) N
      (fun n h0 hN => (hpos n h0 hN).ne') hA0 (fun n h0 hN => hJ n h0 (by omega))
      (fun n h0 hN => by rw [Lop_smul', hψ n h0 hN, mul_zero]) ?_ n hn0 hnN
    simp only [hc]
    field_simp
  -- the column has unit norm
  have hnorm : ∑ n ∈ rowsOf N, eigVec Um k n ^ 2 = 1 := by
    have h1 : (Umᵀ * Um) k k = 1 := by rw [hE.orth]; simp
    rw [Matrix.mul_apply] at h1
    simp only [Matrix.transpose_apply] at h1
    rw [← h1]
    unfold rowsOf
    refine Finset.sum_bij (fun n hn => (⟨n.toNat, by have := (Finset.mem_Icc.mp hn).2; omega⟩ : Fin (N + 1))) ?_ ?_ ?_ ?_
    · intros; exact Finset.mem_univ _
    · intro a ha b hb hab
      have h := Fin.mk.inj_iff.mp hab
      have := Finset.mem_Icc.mp ha
      have := Finset.mem_Icc.mp hb
      omega
    · intro j _
      exact ⟨(j.val : ℤ), Finset.mem_Icc.mpr ⟨by positivity, by omega⟩, by ext; simp⟩
    · intro n hn
      unfold eigVec
      rw [dif_pos (Finset.mem_Icc.mp hn)]
      ring
  have hsq : ∑ n ∈ rowsOf N, ψ n ^ 2 = 1 / c ^ 2 := by
    have : ∑ n ∈ rowsOf N, eigVec Um k n ^ 2 = c ^ 2 * ∑ n ∈ rowsOf N, ψ n ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      have := Finset.mem_Icc.mp hn
      rw [hcs n this.1 this.2]; ring
    rw [hnorm] at this
    field_simp
    linarith
  intro n hn
  have hn' := Finset.mem_Icc.mp hn
  rw [hsq, hcs n hn'.1 hn'.2]
  have : Real.sqrt (1 / c ^ 2) = 1 / c := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_sq hcpos.le]
  rw [this]
  field_simp

/-! ### E2: mirror transport -/

section Mirror

variable {Par : Type*} (F : SymbolFamily Par)

/-- **Mirror transport of the recurrence**: if `psi'` solves the recurrence of the mirror family on the rows `0 <= n < R`, then `m -> psi'(N - m)` solves that of `F` on the rows `N - R < m <= N`. -/
theorem jacSol_mirror (μ : Par) (N : ℕ) (X : ℝ) (R : ℤ) (ψ' : ℤ → ℝ) (h : JacSol (mirrorFamily F) μ N X R ψ') :
    ∀ m : ℤ, (N : ℤ) - R < m → m ≤ N → Lop (F.bondA μ N) (F.diagQ μ N X) (fun n => ψ' ((N : ℤ) - n)) m = 0 := by
  intro m hm1 hm2
  have h1 := h ((N : ℤ) - m) (by omega) (by omega)
  unfold Lop at h1 ⊢
  rw [bondA_mirror, bondA_mirror, diagQ_mirror] at h1
  have e1 : (N : ℤ) - 1 - ((N : ℤ) - m) = m - 1 := by ring
  have e2 : (N : ℤ) - 1 - ((N : ℤ) - m - 1) = m := by ring
  have e3 : (N : ℤ) - ((N : ℤ) - m) = m := by ring
  have e4 : (N : ℤ) - ((N : ℤ) - m + 1) = m - 1 := by ring
  have e5 : (N : ℤ) - ((N : ℤ) - m - 1) = m + 1 := by ring
  rw [e1, e2, e3] at h1
  show F.bondA μ N m * ψ' ((N : ℤ) - (m + 1)) + F.bondA μ N (m - 1) * ψ' ((N : ℤ) - (m - 1)) - F.diagQ μ N X m * ψ' ((N : ℤ) - m) = 0
  have e6 : (N : ℤ) - (m + 1) = (N : ℤ) - m - 1 := by ring
  have e7 : (N : ℤ) - (m - 1) = (N : ℤ) - m + 1 := by ring
  rw [e6, e7]
  linarith

/-- `X_s^+` of the mirror family is that of the family. -/
theorem bandHi_mirror (μ : Par) : (mirrorFamily F).bandHi μ = F.bandHi μ := by
  unfold SymbolFamily.bandHi Xsp
  have hL : (mirrorFamily F).L = F.L := rfl
  rw [hL]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨F.L - u, ⟨by linarith [hu.2], by linarith [hu.1]⟩, ?_⟩
    show fPlus F.L (F.G 0 μ) (F.B 0 μ) (F.L - u) = fPlus F.L (fun s => F.G 0 μ (F.L - s)) (fun s => F.B 0 μ (F.L - s)) u
    unfold fPlus E0
    have : F.L - (F.L - u) = u := by ring
    rw [this]
    simp only [this]
    ring_nf
  · rintro ⟨u, hu, rfl⟩
    refine ⟨F.L - u, ⟨by linarith [hu.2], by linarith [hu.1]⟩, ?_⟩
    show fPlus F.L (fun s => F.G 0 μ (F.L - s)) (fun s => F.B 0 μ (F.L - s)) (F.L - u) = fPlus F.L (F.G 0 μ) (F.B 0 μ) u
    unfold fPlus E0
    have : F.L - (F.L - u) = u := by ring
    simp only [this]
    ring_nf

end Mirror

section MirrorChart

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  {CL : SoftEdgeChart F P m q U V Lm} {CR : SoftEdgeChart (mirrorFamily F) P m q U V Lm}

/-- `a_R = a_L` for a mirror pair of charts (`mu in P`). -/
theorem aOf_mirror (hM : SoftMirror CL CR) {μ : Par} (hμ : μ ∈ P) (X : ℝ) (N : ℕ) : CR.aOf μ X N = CL.aOf μ X N := by
  obtain ⟨-, -, hmu, -⟩ := hM
  unfold SoftEdgeCore.aOf
  rw [bandHi_mirror, show (mirrorFamily F).step N = F.step N from rfl]
  have : (fun r α' => CR.muS r μ α') = fun r α' => CL.muS r μ α' := by
    funext r α'
    exact hmu r μ hμ α'
  rw [this]

/-- `Z_R(N - n) = -Z_L(n)` for a mirror pair of charts (`mu in P`). -/
theorem Zof_mirror (hM : SoftMirror CL CR) {μ : Par} (hμ : μ ∈ P) (X : ℝ) (N : ℕ) (n : ℤ) :
    CR.Zof μ X N ((N : ℤ) - n) = -CL.Zof μ X N n := by
  obtain ⟨huc, hz, -⟩ := hM
  unfold SoftEdgeCore.Zof
  rw [bandHi_mirror, show (mirrorFamily F).step N = F.step N from rfl, uNode_mirror F.L (F.step N) N n (step_mul_succ F N), huc μ hμ]
  have : F.L - uNode (F.step N) n - (F.L - CL.uc μ) = -(uNode (F.step N) n - CL.uc μ) := by ring
  rw [this, hz μ hμ, neg_div]

end MirrorChart

/-- **E1 + E2: `psi^L = kappa psi^R` at an eigenvalue.**  Let `psi^L` solve the recurrence of `F` on the rows `0 <= n < N` with `psi^L_0 > 0`, `psi'` solve that of the mirror family on the rows `0 <= n < N` with `psi'_0 != 0`
(`psi^R_n := psi'_{N-n}`), and `X_k = X` an eigenvalue (`0 < a_n`, `n < N`).  Then `psi^L_n = (psi^L_N / psi^R_N) psi^R_n` on `0..N`, and the column is `Psi_n = psi^L_n / ||psi^L||`. -/
theorem psiL_eq_kappa_psiR {Par : Type*} (F : SymbolFamily Par) (μ : Par) (N : ℕ)
    (hpos : ∀ n : ℤ, 0 ≤ n → n < N → 0 < F.bondA μ N n) (Xs : Fin (N + 1) → ℝ)
    (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hE : IsEigenSystem (F.jacobiMat μ N) Xs Um) (k : Fin (N + 1))
    (ψL : ℤ → ℝ) (hψL : JacSol F μ N (Xs k) N ψL) (hψL0 : 0 < ψL 0)
    (ψ' : ℤ → ℝ) (hψ' : JacSol (mirrorFamily F) μ N (Xs k) N ψ') (hψ'0 : ψ' 0 ≠ 0) :
    (∀ n ∈ rowsOf N, ψL n = ψL N / ψ' 0 * ψ' ((N : ℤ) - n)) ∧
      ∀ n ∈ rowsOf N, eigVec Um k n = ψL n / Real.sqrt (∑ n ∈ rowsOf N, ψL n ^ 2) := by
  have hnorm := eig_eq_normalised F μ N hpos Xs Um hE k ψL hψL hψL0
  have hJ := eigVec_JacSol F μ N Xs Um hE k
  have hA0N : F.bondA μ N N = 0 := by
    unfold SymbolFamily.bondA
    rw [if_neg (by omega)]
  have hr := jacSol_mirror F μ N (Xs k) N ψ' hψ'
  have hk := eig_eq_kappa_mul (F.bondA μ N) (F.diagQ μ N (Xs k)) (eigVec Um k) (fun n => ψ' ((N : ℤ) - n)) N hA0N
    (fun n h0 hN => (hpos n h0 hN).ne') (fun n h0 hN => hJ n h0 (by omega))
    (fun m hm1 hmN => hr m (by omega) hmN) (by simpa using hψ'0)
  refine ⟨?_, hnorm⟩
  have hS : 0 < Real.sqrt (∑ n ∈ rowsOf N, ψL n ^ 2) := by
    apply Real.sqrt_pos.mpr
    apply Finset.sum_pos' (fun n _ => sq_nonneg _)
    exact ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, by positivity⟩
  have hL : ∀ n ∈ rowsOf N, ψL n = Real.sqrt (∑ n ∈ rowsOf N, ψL n ^ 2) * eigVec Um k n := by
    intro n hn
    rw [hnorm n hn]
    field_simp
  have hN0 : (N : ℤ) ∈ rowsOf N := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  intro n hn
  have hn' := Finset.mem_Icc.mp hn
  have h1 := hk n hn'.1 hn'.2
  have h2 := hk N (by omega) le_rfl
  beta_reduce at h1 h2
  rw [sub_self] at h1
  rw [hL n hn, hL N hN0, h1]
  field_simp

/-! ### E5, E7: the algebra of matching and normalisation (abstract `l^2` lemmas) -/

section L2Algebra

/-- Cauchy--Schwarz in the form `|sum u v| <= sqrt(sum u^2) sqrt(sum v^2)`. -/
lemma abs_sum_mul_le_sqrt (S : Finset ℤ) (u v : ℤ → ℝ) :
    |∑ n ∈ S, u n * v n| ≤ Real.sqrt (∑ n ∈ S, u n ^ 2) * Real.sqrt (∑ n ∈ S, v n ^ 2) := by
  rw [← Real.sqrt_mul (Finset.sum_nonneg (fun n _ => sq_nonneg _))]
  apply Real.abs_le_sqrt
  exact Finset.sum_mul_sq_le_sq_mul_sq S u v

/-- Minkowski in `l^2`: `sqrt(sum (a+b)^2) <= sqrt(sum a^2) + sqrt(sum b^2)`. -/
lemma sqrt_sum_add_le (S : Finset ℤ) (a b : ℤ → ℝ) :
    Real.sqrt (∑ n ∈ S, (a n + b n) ^ 2) ≤ Real.sqrt (∑ n ∈ S, a n ^ 2) + Real.sqrt (∑ n ∈ S, b n ^ 2) := by
  have ha : 0 ≤ ∑ n ∈ S, a n ^ 2 := Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hb : 0 ≤ ∑ n ∈ S, b n ^ 2 := Finset.sum_nonneg (fun n _ => sq_nonneg _)
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hcs := abs_sum_mul_le_sqrt S a b
  have e : ∑ n ∈ S, (a n + b n) ^ 2 = ∑ n ∈ S, a n ^ 2 + 2 * ∑ n ∈ S, a n * b n + ∑ n ∈ S, b n ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  have h1 := le_abs_self (∑ n ∈ S, a n * b n)
  have h2 := Real.sq_sqrt ha
  have h3 := Real.sq_sqrt hb
  rw [e]
  nlinarith [h1, hcs, h2, h3]

/-- reverse Minkowski: `|sqrt(sum a^2) - sqrt(sum b^2)| <= sqrt(sum (a-b)^2)`. -/
lemma abs_sqrt_sub_le (S : Finset ℤ) (a b : ℤ → ℝ) :
    |Real.sqrt (∑ n ∈ S, a n ^ 2) - Real.sqrt (∑ n ∈ S, b n ^ 2)| ≤ Real.sqrt (∑ n ∈ S, (a n - b n) ^ 2) := by
  rw [abs_le]
  have h1 := sqrt_sum_add_le S (fun n => a n - b n) b
  have h2 := sqrt_sum_add_le S (fun n => b n - a n) a
  simp only [sub_add_cancel] at h1 h2
  have e : ∑ n ∈ S, (b n - a n) ^ 2 = ∑ n ∈ S, (a n - b n) ^ 2 := Finset.sum_congr rfl (fun n _ => by ring)
  rw [e] at h2
  constructor <;> linarith

/-- **E5 (matching, Cauchy--Schwarz)**: `hat kappa - kappa = sum (a - kappa b) b / sum b^2` and `|hat kappa - kappa| <= sqrt(sum (a - kappa b)^2) / sqrt(sum b^2)`
(app_thmA Step 4 (b)). -/
lemma glueKappa_sub_le (a b : ℤ → ℝ) (Ω : Finset ℤ) (κ : ℝ) (hb : 0 < ∑ n ∈ Ω, b n ^ 2) :
    |glueKappa a b Ω - κ| ≤ Real.sqrt (∑ n ∈ Ω, (a n - κ * b n) ^ 2) / Real.sqrt (∑ n ∈ Ω, b n ^ 2) := by
  have e : glueKappa a b Ω - κ = (∑ n ∈ Ω, (a n - κ * b n) * b n) / ∑ n ∈ Ω, b n ^ 2 := by
    unfold glueKappa
    field_simp
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [e, abs_div, abs_of_pos hb]
  have hs : 0 < Real.sqrt (∑ n ∈ Ω, b n ^ 2) := Real.sqrt_pos.mpr hb
  have h := abs_sum_mul_le_sqrt Ω (fun n => a n - κ * b n) b
  rw [div_le_div_iff₀ hb hs]
  have h2 := Real.sq_sqrt hb.le
  nlinarith [h, h2, Real.sqrt_nonneg (∑ n ∈ Ω, (a n - κ * b n) ^ 2)]

/-- **E7 (normalisation, app_thmA Step 4 (e))**: if `|psi - psi^| <= eps V`, `|psi^| <= C V`, `sum V^2 <= Cs sum psi^^2` and `eps sqrt Cs <= 1/2`, then the normalised vectors differ by
`(2 + 2 C sqrt Cs) eps V / ||psi^||`. -/
theorem normalised_error (S : Finset ℤ) (ψ ψh V : ℤ → ℝ) (ε C Cs : ℝ) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hCs : 0 ≤ Cs)
    (hNpos : 0 < ∑ n ∈ S, ψh n ^ 2) (hV : ∀ n ∈ S, 0 ≤ V n)
    (herr : ∀ n ∈ S, |ψ n - ψh n| ≤ ε * V n) (henv : ∀ n ∈ S, |ψh n| ≤ C * V n)
    (hsum : ∑ n ∈ S, V n ^ 2 ≤ Cs * ∑ n ∈ S, ψh n ^ 2) (hsmall : ε * Real.sqrt Cs ≤ 1 / 2) :
    ∀ n ∈ S, |ψ n / Real.sqrt (∑ n ∈ S, ψ n ^ 2) - ψh n / Real.sqrt (∑ n ∈ S, ψh n ^ 2)|
      ≤ (2 + 2 * C * Real.sqrt Cs) * ε * V n / Real.sqrt (∑ n ∈ S, ψh n ^ 2) := by
  intro n hn
  set N := Real.sqrt (∑ n ∈ S, ψh n ^ 2) with hN
  set M := Real.sqrt (∑ n ∈ S, ψ n ^ 2) with hM
  have hNp : 0 < N := Real.sqrt_pos.mpr hNpos
  have hsC : 0 ≤ Real.sqrt Cs := Real.sqrt_nonneg _
  -- (1) the `l^2` distance
  have hD : Real.sqrt (∑ n ∈ S, (ψ n - ψh n) ^ 2) ≤ ε * Real.sqrt Cs * N := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc ∑ n ∈ S, (ψ n - ψh n) ^ 2 ≤ ∑ n ∈ S, ε ^ 2 * V n ^ 2 := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          have := herr n hn
          have h0 := abs_nonneg (ψ n - ψh n)
          calc (ψ n - ψh n) ^ 2 = |ψ n - ψh n| ^ 2 := (sq_abs _).symm
            _ ≤ (ε * V n) ^ 2 := pow_le_pow_left₀ h0 this 2
            _ = _ := by ring
      _ = ε ^ 2 * ∑ n ∈ S, V n ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ε ^ 2 * (Cs * ∑ n ∈ S, ψh n ^ 2) := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = (ε * Real.sqrt Cs * N) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hCs, hN, Real.sq_sqrt hNpos.le]; ring
  have hMN := abs_sqrt_sub_le S ψ ψh
  rw [← hM, ← hN] at hMN
  have hMN' : |M - N| ≤ ε * Real.sqrt Cs * N := hMN.trans hD
  have hM2 : N / 2 ≤ M := by
    have := (abs_le.mp hMN').1
    nlinarith [mul_le_mul_of_nonneg_right hsmall hNp.le]
  have hMp : 0 < M := by linarith
  have hVn := hV n hn
  have h1 := herr n hn
  have h2 := henv n hn
  have key : ψ n / M - ψh n / N = (ψ n - ψh n) / M + ψh n * (N - M) / (M * N) := by
    field_simp
    ring
  rw [key]
  refine (abs_add_le _ _).trans ?_
  have t1 : |(ψ n - ψh n) / M| ≤ 2 * ε * V n / N := by
    rw [abs_div, abs_of_pos hMp, div_le_div_iff₀ hMp hNp]
    nlinarith [h1, abs_nonneg (ψ n - ψh n), hVn, hε]
  have t2 : |ψh n * (N - M) / (M * N)| ≤ 2 * C * Real.sqrt Cs * ε * V n / N := by
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hMp hNp), div_le_div_iff₀ (mul_pos hMp hNp) hNp, abs_sub_comm]
    have e1 : |ψh n| * |M - N| ≤ (C * V n) * (ε * Real.sqrt Cs * N) :=
      mul_le_mul h2 hMN' (abs_nonneg _) (by positivity)
    have e2 : 0 ≤ (C * V n) * (ε * Real.sqrt Cs * N) := by positivity
    calc |ψh n| * |M - N| * N ≤ (C * V n) * (ε * Real.sqrt Cs * N) * N := mul_le_mul_of_nonneg_right e1 hNp.le
      _ ≤ (C * V n) * (ε * Real.sqrt Cs * N) * (2 * M) := by
          apply mul_le_mul_of_nonneg_left (by linarith) e2
      _ = 2 * C * Real.sqrt Cs * ε * V n * (M * N) := by ring
  calc _ ≤ 2 * ε * V n / N + 2 * C * Real.sqrt Cs * ε * V n / N := add_le_add t1 t2
    _ = _ := by field_simp

end L2Algebra

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.eig_eq_normalised' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eig_eq_normalised

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.eig_eq_kappa_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eig_eq_kappa_mul

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.jacSol_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jacSol_mirror

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bandHi_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bandHi_mirror

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.psiL_eq_kappa_psiR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms psiL_eq_kappa_psiR

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.normalised_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normalised_error

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.glueKappa_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms glueKappa_sub_le

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.aOf_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aOf_mirror

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.Zof_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Zof_mirror

end FormalResearch.JacobiEigenvectors.TheoremA

end
