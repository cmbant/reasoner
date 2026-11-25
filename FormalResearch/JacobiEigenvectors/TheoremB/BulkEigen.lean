module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.BulkWindow

/-!
# Paper J, Theorem B, L3.1 bulk, input (ii)-(iii): the matching of the two comparison profiles at an eigenvalue

Source: Paper J `app_thmB.tex`, proof of `prop:tha-splice` (a): `eq:tha-spl1` and `eq:tha-spl3`, "the scalar `kappa-hat` is a sum over the
whole window"; `app_thmA.tex` Step 2.

## Proved here

* `kappa_core`: the least-squares scalar `kappa_h = sum a b / sum b^2` of two sequences on a finite window differs from any `kappa_e`
  by at most `(E2/D)^{1/2}`, where `E2` bounds `sum (a - kappa_e b)^2` and `D = sum b^2` (Cauchy--Schwarz).
* `window_sum_reflect`: the reflection `n |-> N - n` of a window sum of an arbitrary sequence.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset

/-- **Least-squares scalar** (`kappa-hat`): if `sum_W (a - kappa_e b)^2 <= E2` and `D = sum_W b^2 > 0`, then
`(sum_W a b / D - kappa_e)^2 <= E2 / D`. -/
theorem kappa_core {ι : Type*} [DecidableEq ι] (W : Finset ι) (a b : ι → ℝ) (κe E2 : ℝ)
    (hD : 0 < ∑ n ∈ W, b n ^ 2) (hE : ∑ n ∈ W, (a n - κe * b n) ^ 2 ≤ E2) :
    ((∑ n ∈ W, a n * b n) / (∑ n ∈ W, b n ^ 2) - κe) ^ 2 ≤ E2 / (∑ n ∈ W, b n ^ 2) := by
  set D := ∑ n ∈ W, b n ^ 2 with hDdef
  have hsum : ∑ n ∈ W, (a n - κe * b n) * b n = (∑ n ∈ W, a n * b n) - κe * D := by
    rw [hDdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq W (fun n => a n - κe * b n) b
  have e1 : (∑ n ∈ W, a n * b n) / D - κe = (∑ n ∈ W, (a n - κe * b n) * b n) / D := by
    rw [hsum]
    field_simp
  rw [e1, div_pow]
  have hD2 : 0 < D ^ 2 := by positivity
  rw [div_le_div_iff₀ hD2 hD]
  have h1 : (∑ n ∈ W, (a n - κe * b n) * b n) ^ 2 ≤ E2 * D := by
    calc (∑ n ∈ W, (a n - κe * b n) * b n) ^ 2 ≤ (∑ n ∈ W, (a n - κe * b n) ^ 2) * D := hcs
      _ ≤ E2 * D := mul_le_mul_of_nonneg_right hE hD.le
  nlinarith [h1]

/-- **Reflection of a window sum**: for `hLs`-type reflection `n |-> N - n` (here as a bijection of `Finset`s given by the caller). -/
theorem sum_reflect_window (W W' : Finset ℤ) (N : ℕ) (f : ℤ → ℝ)
    (hW : ∀ n ∈ W, (N : ℤ) - n ∈ W') (hW' : ∀ j ∈ W', (N : ℤ) - j ∈ W) :
    ∑ n ∈ W, f ((N : ℤ) - n) = ∑ j ∈ W', f j := by
  refine Finset.sum_nbij' (fun n : ℤ => (N : ℤ) - n) (fun j : ℤ => (N : ℤ) - j) hW hW' ?_ ?_ ?_
  · intro n _; ring
  · intro j _; ring
  · intro n _; rfl

open FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine

/-- The reflected eigenvector `i |-> v (N - i)` solves the recurrence of the mirror family on all rows `0..N`. -/
theorem eigen_mirror_jacSol {Par : Type*} (F : SymbolFamily Par) (μ : Par) (N : ℕ) (X : ℝ) (v : ℤ → ℝ)
    (hJ : JacSol F μ N X ((N : ℤ) + 1) v) :
    JacSol (mirrorFamily F) μ N X ((N : ℤ) + 1) (fun i => v ((N : ℤ) - i)) := by
  intro n hn0 hnN
  exact lop_mirror F μ N X v (fun j h0 h1 => hJ j h0 h1) n hn0 hnN

/-- **The last component of a unit eigenvector is nonzero** when the bonds `0 <= n < N` are positive. -/
theorem eigen_last_ne_zero {Par : Type*} (F : SymbolFamily Par) (μ : Par) (N : ℕ) (X : ℝ)
    (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hE : IsEigenSystem (F.jacobiMat μ N) Xs Um)
    (k : Fin (N + 1)) (hk : Xs k = X)
    (hbond : ∀ n : ℤ, 0 ≤ n → n < N → 0 < F.bondA μ N n) : eigVec Um k N ≠ 0 := by
  intro hz
  obtain ⟨hJ, -, hsum⟩ := eigen_col_facts F μ N Xs Um hE k
  rw [hk] at hJ
  have hmir := eigen_mirror_jacSol F μ N X (eigVec Um k) hJ
  have hA : ∀ n : ℤ, 0 ≤ n → n < (N : ℤ) → (mirrorFamily F).bondA μ N n ≠ 0 := by
    intro n hn0 hnN
    rw [bondA_mirror]
    exact (hbond _ (by omega) (by omega)).ne'
  have h0 : (fun i : ℤ => eigVec Um k ((N : ℤ) - i)) 0 = 0 := by
    simp only [sub_zero]
    exact hz
  have hseed := seed_zero_eq_zero (jacSol_mono hmir (by omega : (N : ℤ) ≤ (N : ℤ) + 1)) hA h0
  have hall : ∀ n ∈ rowsOf N, eigVec Um k n = 0 := by
    intro n hn
    unfold rowsOf at hn
    rw [Finset.mem_Icc] at hn
    have h1 := hseed ((N : ℤ) - n).toNat (by omega)
    have e : (((N : ℤ) - n).toNat : ℤ) = (N : ℤ) - n := Int.toNat_of_nonneg (by omega)
    rw [e] at h1
    simpa using h1
  have hzero : ∑ n ∈ rowsOf N, eigVec Um k n ^ 2 = 0 :=
    Finset.sum_eq_zero fun n hn => by rw [hall n hn]; ring
  rw [hsum] at hzero
  exact one_ne_zero hzero

/-- **Exact left profile at an eigenvalue.** If `psi` is the normalised eigenvector `v` scaled to the seed `psihat^L_0`, then it is within
`Cc h^m envL` of `psihat^L` on the rows `0..NR` of the left chain (from the comparison bound `BulkSolutionBound`). -/
theorem eigen_left_profile {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (p : Par × ℝ) (X : ℝ) (N : ℕ)
    (Cc : ℝ)
    (hB : ∀ ψ : ℤ → ℝ, JacSol G p N X (C.chain p X N).NR ψ → ψ 0 = C.psiHatL p X N 0 →
      ∀ k ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR, |ψ k - C.psiHatL p X N k| ≤ Cc * (G.step N) ^ m * C.envL p X N k)
    (v : ℤ → ℝ) (hJ : JacSol G p N X ((N : ℤ) + 1) v) (hv0 : v 0 ≠ 0) (hNR : (C.chain p X N).NR ≤ (N : ℤ) + 1) :
    ∀ k ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR,
      |(C.psiHatL p X N 0 / v 0) * v k - C.psiHatL p X N k| ≤ Cc * (G.step N) ^ m * C.envL p X N k := by
  have hs : JacSol G p N X (C.chain p X N).NR (fun k => (C.psiHatL p X N 0 / v 0) * v k) :=
    jacSol_smul (jacSol_mono hJ hNR) _
  have hval : (fun k => (C.psiHatL p X N 0 / v 0) * v k) 0 = C.psiHatL p X N 0 := by
    simp only
    field_simp
  exact hB (fun k => (C.psiHatL p X N 0 / v 0) * v k) hs hval

/-- **Exact right profile at an eigenvalue** (mirror chart): `beta v(N-j)`, `beta = psihat^R_0 / v_N`, is within `Cc h^m envR` of
`psihat^R_j` on the rows `0..NR` of the right chart. -/
theorem eigen_right_profile {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart (mirrorFamily G) P Jlo Jhi m U V) (p : Par × ℝ) (X : ℝ) (N : ℕ)
    (Cc : ℝ)
    (hB : ∀ ψ : ℤ → ℝ, JacSol (mirrorFamily G) p N X (C.chain p X N).NR ψ → ψ 0 = C.psiHatL p X N 0 →
      ∀ k ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR, |ψ k - C.psiHatL p X N k| ≤ Cc * (G.step N) ^ m * C.envL p X N k)
    (v : ℤ → ℝ) (hJ : JacSol G p N X ((N : ℤ) + 1) v) (hvN : v N ≠ 0) (hNR : (C.chain p X N).NR ≤ (N : ℤ) + 1) :
    ∀ j ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR,
      |(C.psiHatL p X N 0 / v N) * v ((N : ℤ) - j) - C.psiHatL p X N j| ≤ Cc * (G.step N) ^ m * C.envL p X N j := by
  have hmir := eigen_mirror_jacSol G p N X v hJ
  have hs : JacSol (mirrorFamily G) p N X (C.chain p X N).NR
      (fun j => (C.psiHatL p X N 0 / v N) * v ((N : ℤ) - j)) :=
    jacSol_smul (jacSol_mono hmir (by omega)) _
  have hval : (fun j => (C.psiHatL p X N 0 / v N) * v ((N : ℤ) - j)) 0 = C.psiHatL p X N 0 := by
    simp only [sub_zero]
    field_simp
  intro j hj
  exact hB (fun j => (C.psiHatL p X N 0 / v N) * v ((N : ℤ) - j)) hs hval j hj

/-- The last row of a chart is at most `N` (its node lies below `c < L`). -/
theorem chart_NR_le {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (p : Par × ℝ) (hp : p ∈ P)
    (X : ℝ) (hX : X ∈ Set.Icc Jlo Jhi) (N : ℕ) (hN : C.N0 ≤ N) (hst : 0 < G.step N)
    (hLs : G.step N * ((N : ℝ) + 1) = G.L) : (C.chain p X N).NR ≤ (N : ℤ) := by
  obtain ⟨-, -, -, hcNR, -⟩ := C.shape p hp X hX N hN
  have hcL : C.c < G.L := by linarith [C.consts_pos.2.2.2.1, C.consts_pos.2.2.1]
  by_contra hcon
  push Not at hcon
  have h1 : (N : ℝ) + 1 ≤ ((C.chain p X N).NR : ℝ) := by exact_mod_cast hcon
  unfold uNode at hcNR
  nlinarith [mul_le_mul_of_nonneg_right h1 hst.le]

/-- The window of a chart lies in the rows `0..NR`. -/
theorem window_sub_rows {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (p : Par × ℝ) (hp : p ∈ P)
    (X : ℝ) (hX : X ∈ Set.Icc Jlo Jhi) (N : ℕ) (hN : C.N0 ≤ N) (hst : 0 < G.step N) :
    ∀ n ∈ bulkWindow C N, n ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR := by
  intro n hn
  unfold bulkWindow at hn
  rw [Finset.mem_filter] at hn
  obtain ⟨hr, -, hc⟩ := hn
  unfold rowsOf at hr
  rw [Finset.mem_Icc] at hr
  exact Finset.mem_Icc.mpr ⟨hr.1, le_NR_of C p hp X hX N hN hst n hc⟩

/-- **Envelope sum over the window** (left chart): bounded by the whole-row sum of `envL^2`. -/
theorem env_window_le {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (p : Par × ℝ) (hp : p ∈ P)
    (X : ℝ) (hX : X ∈ Set.Icc Jlo Jhi) (N : ℕ) (hN : C.N0 ≤ N) (hst : 0 < G.step N) :
    ∑ n ∈ bulkWindow C N, (C.envL p X N n) ^ 2 ≤
      ∑ j ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR, (C.envL p X N j) ^ 2 :=
  Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => window_sub_rows C p hp X hX N hN hst n hn)
    (fun j _ _ => sq_nonneg _)

/-- **Envelope sum over the mirrored window** (right chart on the left window `n |-> N - n`). -/
theorem env_mirror_window_le {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : BulkWeberChart Fz P Jlo Jhi m U V) (CR : BulkWeberChart (mirrorFamily Fz) P Jlo Jhi m U V)
    (hcoup : CR.c = Fz.L - CL.c' ∧ CR.c' = Fz.L - CL.c) (p : Par × ℝ) (hp : p ∈ P) (X : ℝ) (hX : X ∈ Set.Icc Jlo Jhi)
    (N : ℕ) (hN : CR.N0 ≤ N) (hst : 0 < Fz.step N) (hLs : Fz.step N * ((N : ℝ) + 1) = Fz.L) :
    ∑ n ∈ bulkWindow CL N, (CR.envL p X N ((N : ℤ) - n)) ^ 2 ≤
      ∑ j ∈ Finset.Icc (0 : ℤ) (CR.chain p X N).NR, (CR.envL p X N j) ^ 2 := by
  have hms : ∑ n ∈ bulkWindow CL N, (CR.envL p X N ((N : ℤ) - n)) ^ 2 =
      ∑ j ∈ bulkWindow CR N, (CR.envL p X N j) ^ 2 := by
    apply sum_reflect_window (bulkWindow CL N) (bulkWindow CR N) N (fun j => (CR.envL p X N j) ^ 2)
    · intro n hn
      unfold bulkWindow at hn ⊢
      rw [Finset.mem_filter] at hn ⊢
      obtain ⟨hr, h1, h2⟩ := hn
      unfold rowsOf at hr ⊢
      rw [Finset.mem_Icc] at hr ⊢
      have hms' : (mirrorFamily Fz).step N = Fz.step N := rfl
      rw [hms', uNode_mirror Fz.L (Fz.step N) N n hLs]
      exact ⟨⟨by omega, by omega⟩, by linarith [hcoup.1, hcoup.2], by linarith [hcoup.1, hcoup.2]⟩
    · intro j hj
      unfold bulkWindow at hj ⊢
      rw [Finset.mem_filter] at hj ⊢
      obtain ⟨hr, h1, h2⟩ := hj
      unfold rowsOf at hr ⊢
      rw [Finset.mem_Icc] at hr ⊢
      have hms' : (mirrorFamily Fz).step N = Fz.step N := rfl
      rw [hms'] at h1 h2
      rw [uNode_mirror Fz.L (Fz.step N) N j hLs]
      exact ⟨⟨by omega, by omega⟩, by linarith [hcoup.1, hcoup.2], by linarith [hcoup.1, hcoup.2]⟩
  rw [hms]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun j hj => by
      unfold bulkWindow at hj
      rw [Finset.mem_filter] at hj
      exact window_sub_rows CR p hp X hX N hN hst j (by unfold bulkWindow; exact Finset.mem_filter.mpr hj))
    (fun j _ _ => sq_nonneg _)

/-- **The `kappa-hat` estimate at an eigenvalue** (algebra): if `|kappa-hat| <= Kk` and `(kappa-hat - kappa_e)^2 <= C2 h^(2m) (1 + kappa_e^2)`
with `(C2+1) h^m <= 1/2`, then `|kappa_e| <= 2 Kk + 1` and `|kappa-hat - kappa_e| <= (C2+1) h^m (2 + 2 Kk)`. -/
theorem kappa_e_bound (κh κe Kk C2 hm : ℝ) (hC2 : 0 ≤ C2) (hm0 : 0 ≤ hm) (hKk : |κh| ≤ Kk)
    (hsmall : (C2 + 1) * hm ≤ 1 / 2) (hdiff : (κh - κe) ^ 2 ≤ C2 * hm ^ 2 * (1 + κe ^ 2)) :
    |κe| ≤ 2 * Kk + 1 ∧ |κh - κe| ≤ (C2 + 1) * hm * (2 + 2 * Kk) := by
  set δ := (C2 + 1) * hm with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hsq : (κh - κe) ^ 2 ≤ (δ * (1 + |κe|)) ^ 2 := by
    have h1 : C2 * hm ^ 2 * (1 + κe ^ 2) ≤ δ ^ 2 * (1 + |κe|) ^ 2 := by
      have e : κe ^ 2 = |κe| ^ 2 := (sq_abs κe).symm
      have hb : C2 * hm ^ 2 ≤ δ ^ 2 := by
        rw [hδ]; nlinarith [sq_nonneg hm, mul_nonneg hC2 (sq_nonneg hm)]
      have h2 : 1 + κe ^ 2 ≤ (1 + |κe|) ^ 2 := by
        rw [e]; nlinarith [abs_nonneg κe]
      calc C2 * hm ^ 2 * (1 + κe ^ 2) ≤ δ ^ 2 * (1 + κe ^ 2) :=
            mul_le_mul_of_nonneg_right hb (by positivity)
        _ ≤ δ ^ 2 * (1 + |κe|) ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    rw [mul_pow]
    exact hdiff.trans h1
  have hab : |κh - κe| ≤ δ * (1 + |κe|) := by
    have := abs_le_of_sq_le_sq' hsq (by positivity)
    exact abs_le.mpr this
  have htri : |κe| ≤ |κh| + |κh - κe| := by
    have := abs_sub_abs_le_abs_sub κe κh
    have e : |κh - κe| = |κe - κh| := abs_sub_comm _ _
    have h3 : |κe| ≤ |κh| + |κh - κe| := by
      calc |κe| = |κh + (κe - κh)| := by ring_nf
        _ ≤ |κh| + |κe - κh| := abs_add_le _ _
        _ = |κh| + |κh - κe| := by rw [e]
    exact h3
  have hδ2 : δ ≤ 1 / 2 := hsmall
  have ht : |κe| ≤ 2 * Kk + 1 := by
    have h4 : |κe| ≤ Kk + δ * (1 + |κe|) := by linarith [hKk, htri, hab]
    nlinarith [abs_nonneg κe, hδ2]
  refine ⟨ht, ?_⟩
  calc |κh - κe| ≤ δ * (1 + |κe|) := hab
    _ ≤ δ * (1 + (2 * Kk + 1)) := mul_le_mul_of_nonneg_left (by linarith) hδ0
    _ = (C2 + 1) * hm * (2 + 2 * Kk) := by rw [hδ]; ring

/-- The window constant is positive. -/
theorem windowConst_pos {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (CA : ℝ) (hCA0 : 0 ≤ CA) :
    0 < windowConst C CA := by
  obtain ⟨hc'L, hcc'L, -, -, -, hcM, -, -, -, -⟩ := C.consts_pos
  unfold windowConst
  have hD : 0 < C.c - C.c' := by linarith
  have hK : 0 < (CA + 1) * ((C.cs.KA + C.cs.KB) * C.cs.Kw + 1) * (C.CM + 1) := by
    have h1 := mul_nonneg (add_nonneg C.cs.KA_nonneg C.cs.KB_nonneg) C.cs.Kw_nonneg
    have h2 : 0 < C.CM + 1 := by linarith [C.consts_pos.2.2.2.2.2.2.1]
    have h3 : 0 < CA + 1 := by linarith
    have h4 : 0 < (C.cs.KA + C.cs.KB) * C.cs.Kw + 1 := by linarith
    positivity
  apply div_pos
  · exact mul_pos hD (pow_pos C.cs.cm_pos 2)
  · positivity

/-- The mirror of a left-window row is a right-window row (`hcoup`). -/
theorem mirror_mem_window {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : BulkWeberChart Fz P Jlo Jhi m U V) (CR : BulkWeberChart (mirrorFamily Fz) P Jlo Jhi m U V)
    (hcoup : CR.c = Fz.L - CL.c' ∧ CR.c' = Fz.L - CL.c) (N : ℕ) (hLs : Fz.step N * ((N : ℝ) + 1) = Fz.L)
    (n : ℤ) (hn : n ∈ bulkWindow CL N) : (N : ℤ) - n ∈ bulkWindow CR N := by
  unfold bulkWindow at hn ⊢
  rw [Finset.mem_filter] at hn ⊢
  obtain ⟨hr, h1, h2⟩ := hn
  unfold rowsOf at hr ⊢
  rw [Finset.mem_Icc] at hr ⊢
  have hms' : (mirrorFamily Fz).step N = Fz.step N := rfl
  rw [hms', uNode_mirror Fz.L (Fz.step N) N n hLs]
  exact ⟨⟨by omega, by omega⟩, by linarith [hcoup.1, hcoup.2], by linarith [hcoup.1, hcoup.2]⟩

/-- Envelope sums with the `h^{1/2}` factor moved to `1/sqrt h` (for `h <= 1`). -/
theorem env_sum_inv (S E Cs Cm h : ℝ) (hS : S ≤ E * (Cs / Real.sqrt h + Cm ^ 2 * Real.sqrt h))
    (hE : 0 ≤ E) (hCm : 0 ≤ Cm) (h0 : 0 < h) (h1 : h ≤ 1) : S ≤ E * (Cs + Cm ^ 2) / Real.sqrt h := by
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.mpr h0
  have hsq : Real.sqrt h ≤ 1 / Real.sqrt h := by
    rw [le_div_iff₀ hs]
    nlinarith [Real.sq_sqrt h0.le]
  have : E * (Cs / Real.sqrt h + Cm ^ 2 * Real.sqrt h) ≤ E * (Cs + Cm ^ 2) / Real.sqrt h := by
    have e : E * (Cs + Cm ^ 2) / Real.sqrt h = E * Cs / Real.sqrt h + E * Cm ^ 2 * (1 / Real.sqrt h) := by
      ring
    rw [e]
    have h2 : E * Cm ^ 2 * Real.sqrt h ≤ E * Cm ^ 2 * (1 / Real.sqrt h) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have e2 : E * (Cs / Real.sqrt h + Cm ^ 2 * Real.sqrt h) = E * Cs / Real.sqrt h + E * Cm ^ 2 * Real.sqrt h := by
      ring
    rw [e2]
    linarith
  linarith

/-- **Arithmetic of the matching at an eigenvalue**: the three ingredients (the exact-profile error, the kappa estimate, the
envelope bounds) combine to `|psihat^L - kappa-hat psihat^R| <= (A / c_M) h^m M`. -/
theorem matching_arith (pL pR κe κh xn yn Mn hm qq cM CcL CcR Kk D1 kL kM kKg : ℝ)
    (hm0 : 0 ≤ hm) (hq0 : 0 ≤ qq) (hCcL : 0 ≤ CcL) (hCcR : 0 ≤ CcR) (hKk : 0 ≤ Kk) (hD1 : 0 ≤ D1)
    (hkL : 0 ≤ kL) (hkM : 0 ≤ kM) (hkKg : 0 ≤ kKg) (hcM : 0 < cM)
    (hF1 : |pL - κe * pR| ≤ CcL * hm * xn + |κe| * (CcR * hm * yn))
    (hF2 : |κh - κe| ≤ D1 * hm * (2 + 2 * Kk))
    (hF3 : |κe| ≤ 2 * Kk + 1)
    (hxn0 : 0 ≤ xn) (hyn0 : 0 ≤ yn)
    (hx : xn ≤ kL * qq) (hy : yn ≤ kM * qq) (hpR : |pR| ≤ kKg * yn) (hMn : cM * qq ≤ Mn) :
    |pL - κh * pR| ≤ (CcL * kL + (2 * Kk + 1) * CcR * kM + D1 * (2 + 2 * Kk) * kKg * kM) / cM * hm * Mn := by
  have hpR' : |pR| ≤ kKg * kM * qq := hpR.trans (by nlinarith [mul_le_mul_of_nonneg_left hy hkKg])
  have e1 : |pL - κh * pR| ≤ |pL - κe * pR| + |κh - κe| * |pR| := by
    have h := abs_sub (pL - κe * pR) ((κh - κe) * pR)
    rw [abs_mul] at h
    have e : pL - κh * pR = (pL - κe * pR) - (κh - κe) * pR := by ring
    rw [e]
    exact h
  have e2 : |pL - κe * pR| ≤ CcL * hm * kL * qq + (2 * Kk + 1) * (CcR * hm * kM * qq) := by
    refine hF1.trans ?_
    have a1 : CcL * hm * xn ≤ CcL * hm * (kL * qq) :=
      mul_le_mul_of_nonneg_left hx (mul_nonneg hCcL hm0)
    have a2 : |κe| * (CcR * hm * yn) ≤ (2 * Kk + 1) * (CcR * hm * (kM * qq)) := by
      apply mul_le_mul hF3 _ (by positivity) (by linarith)
      exact mul_le_mul_of_nonneg_left hy (mul_nonneg hCcR hm0)
    nlinarith [a1, a2]
  have e3 : |κh - κe| * |pR| ≤ D1 * hm * (2 + 2 * Kk) * (kKg * kM * qq) :=
    mul_le_mul hF2 hpR' (abs_nonneg _) (by positivity)
  have hA0 : 0 ≤ CcL * kL + (2 * Kk + 1) * CcR * kM + D1 * (2 + 2 * Kk) * kKg * kM := by positivity
  have hT : |pL - κh * pR| ≤ hm * qq * (CcL * kL + (2 * Kk + 1) * CcR * kM + D1 * (2 + 2 * Kk) * kKg * kM) := by
    nlinarith [e1, e2, e3]
  have hqq : qq ≤ Mn / cM := (le_div_iff₀ hcM).mpr (by linarith [hMn])
  calc |pL - κh * pR| ≤ hm * qq * (CcL * kL + (2 * Kk + 1) * CcR * kM + D1 * (2 + 2 * Kk) * kKg * kM) := hT
    _ ≤ hm * (Mn / cM) * (CcL * kL + (2 * Kk + 1) * CcR * kM + D1 * (2 + 2 * Kk) * kKg * kM) := by
        apply mul_le_mul_of_nonneg_right _ hA0
        exact mul_le_mul_of_nonneg_left hqq hm0
    _ = (CcL * kL + (2 * Kk + 1) * CcR * kM + D1 * (2 + 2 * Kk) * kKg * kM) / cM * hm * Mn := by
        field_simp

/-- **Clause (ii) of `prop:tha-splice` (a), bulk, at an eigenvalue** (matching of the comparison profiles on the window):
`|psihat^L_n - kappa-hat psihat^R_n| <= Cm h^m M_n` for `X = Xs k` an eigenvalue and `n` in the window `Omega`, for `h <= h1`. -/
theorem bulk_matching_eig {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : BulkWeberChart Fz P Jlo Jhi m U V) (CR : BulkWeberChart (mirrorFamily Fz) P Jlo Jhi m U V)
    (hm : 1 ≤ m) (hcoup : CR.c = Fz.L - CL.c' ∧ CR.c' = Fz.L - CL.c) (r : ℕ) (hr : StdAssump Fz P (m / 2) r) :
    ∃ Cm h1 : ℝ, 0 < h1 ∧ ∀ p ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
        ∀ k : Fin (N + 1), Xs k = X → ∀ n ∈ bulkWindow CL N,
          |CL.psiHatL p X N n - bulkKappa CL CR p X N * bulkSeqR CR p X N n| ≤
            Cm * Fz.step N ^ m * (CL.chain p X N).M n := by
  have hr0 := hr
  obtain ⟨hPc, hEK, hH⟩ := hr0
  obtain ⟨CA, hCA0, hCA⟩ := bondA_bound_of_EK Fz P (m / 2) r hPc hEK
  obtain ⟨hbh, hbhpos, hbpos⟩ := bondA_pos_small Fz P (m / 2) r hPc hEK hH
  have hBL' := bulkSolutionBound_of_one_le CL hm
  have hBR' := bulkSolutionBound_of_one_le CR hm
  unfold BulkSolutionBound at hBL' hBR'
  obtain ⟨CcL, h0L, hh0L, hBL⟩ := hBL'
  obtain ⟨CcR, h0R, hh0R, hBR⟩ := hBR'
  obtain ⟨Cc0, h0k, cN, CN, cκ, Cκ, hh0k, hcN, hcκ, hκall⟩ := bulk_conj1 CL CR hm hcoup r hr
  have hcLD : 0 < CL.c - CL.c' := by linarith [CL.consts_pos.2.1]
  have hCRD : CR.c - CR.c' = CL.c - CL.c' := by rw [hcoup.1, hcoup.2]; ring
  have hσL : 0 < CL.σ := CL.consts_pos.2.2.1
  have hσR : 0 < CR.σ := CR.consts_pos.2.2.1
  have hcM : 0 < CL.cM := CL.consts_pos.2.2.2.2.2.1
  have hCMLpos : 0 < CL.CM := lt_of_lt_of_le hcM (CL.consts_pos.2.2.2.2.2.2.1)
  have hCsLpos : 0 ≤ CL.Csum := CL.consts_pos.2.2.2.2.2.2.2.2.1
  have hCsRpos : 0 ≤ CR.Csum := CR.consts_pos.2.2.2.2.2.2.2.2.1
  -- standard constants of the two charts (`chart_side_facts`)
  obtain ⟨KgL, hKgL⟩ : ∃ x : ℝ, x = (CL.cs.KA + CL.cs.KB) * CL.cs.Kw + 1 := ⟨_, rfl⟩
  obtain ⟨CEL, hCEL⟩ : ∃ x : ℝ, x = |CL.cs.CE| + 1 := ⟨_, rfl⟩
  obtain ⟨CML, hCML⟩ : ∃ x : ℝ, x = CL.CM + 1 := ⟨_, rfl⟩
  obtain ⟨CsL, hCsL⟩ : ∃ x : ℝ, x = CL.Csum + 1 := ⟨_, rfl⟩
  obtain ⟨KgR, hKgR⟩ : ∃ x : ℝ, x = (CR.cs.KA + CR.cs.KB) * CR.cs.Kw + 1 := ⟨_, rfl⟩
  obtain ⟨CER, hCER⟩ : ∃ x : ℝ, x = |CR.cs.CE| + 1 := ⟨_, rfl⟩
  obtain ⟨CMR, hCMR⟩ : ∃ x : ℝ, x = CR.CM + 1 := ⟨_, rfl⟩
  obtain ⟨CsR, hCsR⟩ : ∃ x : ℝ, x = CR.Csum + 1 := ⟨_, rfl⟩
  obtain ⟨CAg, hCAg⟩ : ∃ x : ℝ, x = CA + 1 := ⟨_, rfl⟩
  have hKgL0 : 0 < KgL := by
    have := mul_nonneg (add_nonneg CL.cs.KA_nonneg CL.cs.KB_nonneg) CL.cs.Kw_nonneg
    rw [hKgL]; linarith
  have hKgR0 : 0 < KgR := by
    have := mul_nonneg (add_nonneg CR.cs.KA_nonneg CR.cs.KB_nonneg) CR.cs.Kw_nonneg
    rw [hKgR]; linarith
  have hCEL0 : 0 < CEL := by rw [hCEL]; linarith [abs_nonneg CL.cs.CE]
  have hCER0 : 0 < CER := by rw [hCER]; linarith [abs_nonneg CR.cs.CE]
  have hCML0 : 0 < CML := by rw [hCML]; linarith
  have hCMR0 : 0 < CMR := by rw [hCMR]; linarith [CR.consts_pos.2.2.2.2.2.2.1, CR.consts_pos.2.2.2.2.2.1]
  have hCsL0 : 0 ≤ CsL := by rw [hCsL]; linarith
  have hCsR0 : 0 ≤ CsR := by rw [hCsR]; linarith
  have hCAg0 : 0 < CAg := by rw [hCAg]; linarith
  have hKgCL : (CL.cs.KA + CL.cs.KB) * CL.cs.Kw ≤ KgL := by rw [hKgL]; linarith
  have hKgCR : (CR.cs.KA + CR.cs.KB) * CR.cs.Kw ≤ KgR := by rw [hKgR]; linarith
  have hCEgCL : CL.cs.CE ≤ CEL := by rw [hCEL]; linarith [le_abs_self CL.cs.CE]
  have hCEgCR : CR.cs.CE ≤ CER := by rw [hCER]; linarith [le_abs_self CR.cs.CE]
  have hCMgCL : CL.CM ≤ CML := by rw [hCML]; linarith
  have hCMgCR : CR.CM ≤ CMR := by rw [hCMR]; linarith
  have hCsgCL : CL.Csum ≤ CsL := by rw [hCsL]; linarith
  have hCsgCR : CR.Csum ≤ CsR := by rw [hCsR]; linarith
  have hcW : 0 < windowConst CR CA := windowConst_pos CR CA hCA0
  obtain ⟨C1, hC1⟩ : ∃ x : ℝ, x = CEL ^ 2 * (CsL + CML ^ 2) + CER ^ 2 * (CsR + CMR ^ 2) := ⟨_, rfl⟩
  have hC10 : 0 ≤ C1 := by rw [hC1]; positivity
  obtain ⟨Cc, hCc⟩ : ∃ x : ℝ, x = |CcL| + |CcR| := ⟨_, rfl⟩
  have hCc0 : 0 ≤ Cc := by rw [hCc]; positivity
  obtain ⟨C2, hC2⟩ : ∃ x : ℝ, x = 2 * C1 * Cc ^ 2 / windowConst CR CA := ⟨_, rfl⟩
  have hC20 : 0 ≤ C2 := by rw [hC2]; exact div_nonneg (by positivity) hcW.le
  -- the admissible step
  obtain ⟨h1, hh1⟩ : ∃ x : ℝ, x = min (min (min (min h0L h0R) (min h0k hbh)) (min 1 (1 / (2 * (C2 + 1)))))
      (min (min CL.σ CR.σ) ((CL.c - CL.c') / 6)) := ⟨_, rfl⟩
  have hh1pos : 0 < h1 := by
    rw [hh1]
    have hd : 0 < 1 / (2 * (C2 + 1)) := by apply div_pos one_pos; linarith
    exact lt_min (lt_min (lt_min (lt_min hh0L hh0R) (lt_min hh0k hbhpos)) (lt_min one_pos hd))
      (lt_min (lt_min hσL hσR) (by linarith))
  have hh1L : h1 ≤ h0L := by rw [hh1]; exact (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hh1R : h1 ≤ h0R := by rw [hh1]; exact (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hh1k : h1 ≤ h0k := by rw [hh1]; exact (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hh1b : h1 ≤ hbh := by rw [hh1]; exact (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hh1one : h1 ≤ 1 := by rw [hh1]; exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hh1D : h1 ≤ 1 / (2 * (C2 + 1)) := by rw [hh1]; exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hh1σL : h1 ≤ CL.σ := by rw [hh1]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hh1σR : h1 ≤ CR.σ := by rw [hh1]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hh1W : h1 ≤ (CL.c - CL.c') / 6 := by rw [hh1]; exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨(|CcL| * CML + (2 * Cκ + 1) * |CcR| * CMR + (C2 + 1) * (2 + 2 * Cκ) * KgR * CMR) / CL.cM, h1, hh1pos, ?_⟩
  intro p hp X hX N hN hstep Xs Um hE k hk n hn
  have hN1 : CL.N0 ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : CR.N0 ≤ N := le_trans (le_max_right _ _) hN
  have hst : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hLs : Fz.step N * ((N : ℝ) + 1) = Fz.L := step_mul_succ Fz N
  have hsle1 : Fz.step N ≤ 1 := hstep.trans hh1one
  have hsL : Fz.step N ≤ h0L := hstep.trans hh1L
  have hsR : Fz.step N ≤ h0R := hstep.trans hh1R
  have hsk : Fz.step N ≤ h0k := hstep.trans hh1k
  have hsb : Fz.step N ≤ hbh := hstep.trans hh1b
  have hsd : Fz.step N ≤ 1 / (2 * (C2 + 1)) := hstep.trans hh1D
  have hsσL : Fz.step N ≤ CL.σ := hstep.trans hh1σL
  have hsσR : Fz.step N ≤ CR.σ := hstep.trans hh1σR
  have hsdW : Fz.step N ≤ (CL.c - CL.c') / 6 := hstep.trans hh1W
  have hhcL : Fz.step N ≤ CL.c - CL.c' := by linarith
  have hhcR : Fz.step N ≤ CR.c - CR.c' := by rw [hCRD]; exact hhcL
  have hsdWR : Fz.step N ≤ (CR.c - CR.c') / 6 := by rw [hCRD]; exact hsdW
  -- the eigenvector: its recurrence, positivity of the first entry and nonvanishing of the last
  obtain ⟨hJ0, hv0pos, -⟩ := eigen_col_facts Fz p N Xs Um hE k
  rw [hk] at hJ0
  have hv0 : eigVec Um k 0 ≠ 0 := hv0pos.ne'
  have hvN : eigVec Um k N ≠ 0 :=
    eigen_last_ne_zero Fz p N X Xs Um hE k hk (fun n h0 h1 => hbpos p hp N hsb n h0 h1)
  have hNRL : (CL.chain p X N).NR ≤ (N : ℤ) + 1 := (chart_NR_le CL p hp X hX N hN1 hst hLs).trans (by omega)
  have hNRR : (CR.chain p X N).NR ≤ (N : ℤ) + 1 := (chart_NR_le CR p hp X hX N hN2 hst hLs).trans (by omega)
  have hψL0 : 0 < CL.psiHatL p X N 0 := by
    unfold BulkWeberChart.psiHatL
    rw [psiHat_one_eq]
    exact CL.seed_pos p hp X hX N hN1
  have hψR0 : 0 < CR.psiHatL p X N 0 := by
    unfold BulkWeberChart.psiHatL
    rw [psiHat_one_eq]
    exact CR.seed_pos p hp X hX N hN2
  -- bond bounds, chart facts, envelope sums
  have hAL0 : ∀ j : ℤ, 0 ≤ j → j ≤ (CL.chain p X N).NR - 1 → |(CL.chain p X N).A j| ≤ CA := by
    intro j h0 h1
    rw [CL.A_bond p hp X hX N hN1 j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]
    exact hCA p hp N j
  have hAR0 : ∀ j : ℤ, 0 ≤ j → j ≤ (CR.chain p X N).NR - 1 → |(CR.chain p X N).A j| ≤ CA := by
    intro j h0 h1
    rw [CR.A_bond p hp X hX N hN2 j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), bondA_mirror]
    exact hCA p hp N _
  have hAL : ∀ j : ℤ, 0 ≤ j → j ≤ (CL.chain p X N).NR - 1 → |(CL.chain p X N).A j| ≤ CAg :=
    fun j h0 h1 => (hAL0 j h0 h1).trans (by rw [hCAg]; linarith)
  have hAR : ∀ j : ℤ, 0 ≤ j → j ≤ (CR.chain p X N).NR - 1 → |(CR.chain p X N).A j| ≤ CAg :=
    fun j h0 h1 => (hAR0 j h0 h1).trans (by rw [hCAg]; linarith)
  obtain ⟨LA, LB, LC, LD, -⟩ := chart_side_facts CL p hp X hX N hN1 hhcL KgL CEL CML CL.cs.cm CsL CAg hKgL0 hCEL0
    hCML0 CL.cs.cm_pos hCAg0 hKgCL hCEgCL hCMgCL le_rfl hCsgCL hAL
  obtain ⟨RA, RB, RC, RD, -⟩ := chart_side_facts CR p hp X hX N hN2 hhcR KgR CER CMR CR.cs.cm CsR CAg hKgR0 hCER0
    hCMR0 CR.cs.cm_pos hCAg0 hKgCR hCEgCR hCMgCR le_rfl hCsgCR hAR
  have hSL : ∑ n ∈ bulkWindow CL N, (CL.envL p X N n) ^ 2 ≤ C1 / Real.sqrt (Fz.step N) := by
    have h1' := env_window_le CL p hp X hX N hN1 hst
    have h2 := env_sum_inv _ (CEL ^ 2) CsL CML (Fz.step N) LC (by positivity) hCML0.le hst hsle1
    refine h1'.trans (h2.trans ?_)
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    rw [hC1]
    have : 0 ≤ CER ^ 2 * (CsR + CMR ^ 2) := by positivity
    linarith
  have hSR : ∑ n ∈ bulkWindow CL N, (CR.envL p X N ((N : ℤ) - n)) ^ 2 ≤ C1 / Real.sqrt (Fz.step N) := by
    have h1' := env_mirror_window_le CL CR hcoup p hp X hX N hN2 hst hLs
    have h2 := env_sum_inv _ (CER ^ 2) CsR CMR (Fz.step N) RC (by positivity) hCMR0.le hst hsle1
    refine h1'.trans (h2.trans ?_)
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    rw [hC1]
    have : 0 ≤ CEL ^ 2 * (CsL + CML ^ 2) := by positivity
    linarith
  -- the window lower bound of the right chart, transported to the left window
  have hWR := window_sum_lower CR CA hCA0 p hp X hX N hN2 hsdWR hsσR hAR0
  have hDeq := window_mirror_sum CL CR hcoup p X N hLs
  have hDlow : windowConst CR CA / Real.sqrt (Fz.step N) ≤ ∑ n ∈ bulkWindow CL N, (bulkSeqR CR p X N n) ^ 2 :=
    hWR.trans_eq hDeq.symm
  have hDpos : 0 < ∑ n ∈ bulkWindow CL N, (bulkSeqR CR p X N n) ^ 2 :=
    lt_of_lt_of_le (div_pos hcW (Real.sqrt_pos.mpr hst)) hDlow
  -- the exact profiles, with the constants |Cc| (nonnegative envelopes)
  have hB' : ∀ ψ : ℤ → ℝ, JacSol Fz p N X (CL.chain p X N).NR ψ → ψ 0 = CL.psiHatL p X N 0 →
      ∀ k ∈ Finset.Icc (0 : ℤ) (CL.chain p X N).NR,
        |ψ k - CL.psiHatL p X N k| ≤ |CcL| * Fz.step N ^ m * CL.envL p X N k := by
    intro ψ hψ hψ0 k hk
    have hk' := Finset.mem_Icc.mp hk
    refine (hBL p hp X hX N hN1 hsL ψ hψ hψ0 k hk).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hst.le _))
      (LB k hk'.1 hk'.2).1
  have hB'R : ∀ ψ : ℤ → ℝ, JacSol (mirrorFamily Fz) p N X (CR.chain p X N).NR ψ → ψ 0 = CR.psiHatL p X N 0 →
      ∀ k ∈ Finset.Icc (0 : ℤ) (CR.chain p X N).NR,
        |ψ k - CR.psiHatL p X N k| ≤ |CcR| * Fz.step N ^ m * CR.envL p X N k := by
    intro ψ hψ hψ0 k hk
    have hk' := Finset.mem_Icc.mp hk
    refine (hBR p hp X hX N hN2 hsR ψ hψ hψ0 k hk).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hst.le _))
      (RB k hk'.1 hk'.2).1
  have hLp := eigen_left_profile CL p X N |CcL| hB' (eigVec Um k) hJ0 hv0 hNRL
  have hRp := eigen_right_profile CR p X N |CcR| hB'R (eigVec Um k) hJ0 hvN hNRR
  set α := CL.psiHatL p X N 0 / eigVec Um k 0 with hα
  set β := CR.psiHatL p X N 0 / eigVec Um k N with hβ
  have hβne : β ≠ 0 := div_ne_zero hψR0.ne' hvN
  set κe := α / β with hκe
  have hκβ : κe * β = α := div_mul_cancel₀ α hβne
  set hm := Fz.step N ^ m with hhm
  have hm0 : 0 ≤ hm := pow_nonneg hst.le _
  have hqq0 : 0 ≤ Fz.step N ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hst.le _
  -- the pointwise error of the exact-profile identity on the window
  have hF1 : ∀ n ∈ bulkWindow CL N, |CL.psiHatL p X N n - κe * CR.psiHatL p X N ((N : ℤ) - n)| ≤
      |CcL| * hm * CL.envL p X N n + |κe| * (|CcR| * hm * CR.envL p X N ((N : ℤ) - n)) := by
    intro n hn
    have hnL := window_sub_rows CL p hp X hX N hN1 hst n hn
    have hjR := window_sub_rows CR p hp X hX N hN2 hst ((N : ℤ) - n) (mirror_mem_window CL CR hcoup N hLs n hn)
    have eL := hLp n hnL
    have eR := hRp ((N : ℤ) - n) hjR
    rw [show (N : ℤ) - ((N : ℤ) - n) = n by ring] at eR
    rw [abs_sub_comm] at eL eR
    have key : CL.psiHatL p X N n - κe * CR.psiHatL p X N ((N : ℤ) - n) =
        (CL.psiHatL p X N n - α * eigVec Um k n) - κe * (CR.psiHatL p X N ((N : ℤ) - n) - β * eigVec Um k n) := by
      rw [← hκβ]; ring
    rw [key]
    calc _ ≤ |CL.psiHatL p X N n - α * eigVec Um k n| +
          |κe * (CR.psiHatL p X N ((N : ℤ) - n) - β * eigVec Um k n)| := abs_sub _ _
      _ = |CL.psiHatL p X N n - α * eigVec Um k n| +
          |κe| * |CR.psiHatL p X N ((N : ℤ) - n) - β * eigVec Um k n| := by rw [abs_mul]
      _ ≤ _ := add_le_add eL (mul_le_mul_of_nonneg_left eR (abs_nonneg _))
  -- the sum of squares over the window
  have hE2 : ∑ n ∈ bulkWindow CL N, (CL.psiHatL p X N n - κe * bulkSeqR CR p X N n) ^ 2 ≤
      2 * hm ^ 2 * Cc ^ 2 * (1 + |κe| ^ 2) * C1 / Real.sqrt (Fz.step N) := by
    have per : ∀ n ∈ bulkWindow CL N, (CL.psiHatL p X N n - κe * bulkSeqR CR p X N n) ^ 2 ≤
        2 * (|CcL| * hm) ^ 2 * (CL.envL p X N n) ^ 2 +
          2 * (|κe| ^ 2 * (|CcR| * hm) ^ 2) * (CR.envL p X N ((N : ℤ) - n)) ^ 2 := by
      intro n hn
      have hb := hF1 n hn
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hb 2
      rw [sq_abs] at hsq
      set P := |CcL| * hm * CL.envL p X N n with hP
      set Q := |κe| * (|CcR| * hm * CR.envL p X N ((N : ℤ) - n)) with hQ
      have hPQ : (P + Q) ^ 2 ≤ 2 * P ^ 2 + 2 * Q ^ 2 := by
        have h := sq_nonneg (P - Q)
        have e : (P + Q) ^ 2 + (P - Q) ^ 2 = 2 * P ^ 2 + 2 * Q ^ 2 := by ring
        linarith
      have hPe : P ^ 2 = (|CcL| * hm) ^ 2 * (CL.envL p X N n) ^ 2 := by rw [hP]; ring
      have hQe : Q ^ 2 = |κe| ^ 2 * (|CcR| * hm) ^ 2 * (CR.envL p X N ((N : ℤ) - n)) ^ 2 := by rw [hQ]; ring
      calc (CL.psiHatL p X N n - κe * bulkSeqR CR p X N n) ^ 2 ≤ (P + Q) ^ 2 := hsq
        _ ≤ 2 * P ^ 2 + 2 * Q ^ 2 := hPQ
        _ = 2 * (|CcL| * hm) ^ 2 * (CL.envL p X N n) ^ 2 +
            2 * (|κe| ^ 2 * (|CcR| * hm) ^ 2) * (CR.envL p X N ((N : ℤ) - n)) ^ 2 := by
          rw [hPe, hQe]; ring
    have ha0 : 0 ≤ 2 * (|CcL| * hm) ^ 2 := by positivity
    have hb0 : 0 ≤ 2 * (|κe| ^ 2 * (|CcR| * hm) ^ 2) := by positivity
    have hsplit : ∑ n ∈ bulkWindow CL N, (2 * (|CcL| * hm) ^ 2 * (CL.envL p X N n) ^ 2 +
        2 * (|κe| ^ 2 * (|CcR| * hm) ^ 2) * (CR.envL p X N ((N : ℤ) - n)) ^ 2) =
        2 * (|CcL| * hm) ^ 2 * ∑ n ∈ bulkWindow CL N, (CL.envL p X N n) ^ 2 +
          2 * (|κe| ^ 2 * (|CcR| * hm) ^ 2) * ∑ n ∈ bulkWindow CL N, (CR.envL p X N ((N : ℤ) - n)) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    have hcL2 : |CcL| ^ 2 ≤ Cc ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (by rw [hCc]; linarith [abs_nonneg CcR]) 2
    have hcR2 : |CcR| ^ 2 ≤ Cc ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (by rw [hCc]; linarith [abs_nonneg CcL]) 2
    have hcoef : 2 * (|CcL| * hm) ^ 2 + 2 * (|κe| ^ 2 * (|CcR| * hm) ^ 2) ≤ 2 * hm ^ 2 * Cc ^ 2 * (1 + |κe| ^ 2) := by
      have e1 : 2 * (|CcL| * hm) ^ 2 ≤ 2 * hm ^ 2 * Cc ^ 2 := by
        have := mul_le_mul_of_nonneg_left hcL2 (sq_nonneg hm)
        have e : 2 * (|CcL| * hm) ^ 2 = 2 * (hm ^ 2 * |CcL| ^ 2) := by ring
        have e' : 2 * hm ^ 2 * Cc ^ 2 = 2 * (hm ^ 2 * Cc ^ 2) := by ring
        rw [e, e']
        exact mul_le_mul_of_nonneg_left this (by norm_num)
      have e2 : 2 * (|κe| ^ 2 * (|CcR| * hm) ^ 2) ≤ 2 * hm ^ 2 * Cc ^ 2 * |κe| ^ 2 := by
        have := mul_le_mul_of_nonneg_left hcR2 (mul_nonneg (sq_nonneg hm) (sq_nonneg |κe|))
        have e : 2 * (|κe| ^ 2 * (|CcR| * hm) ^ 2) = 2 * (hm ^ 2 * |κe| ^ 2 * |CcR| ^ 2) := by ring
        have e' : 2 * hm ^ 2 * Cc ^ 2 * |κe| ^ 2 = 2 * (hm ^ 2 * |κe| ^ 2 * Cc ^ 2) := by ring
        rw [e, e']
        exact mul_le_mul_of_nonneg_left (by linarith [this]) (by norm_num)
      have e3 : 2 * hm ^ 2 * Cc ^ 2 * (1 + |κe| ^ 2) = 2 * hm ^ 2 * Cc ^ 2 + 2 * hm ^ 2 * Cc ^ 2 * |κe| ^ 2 := by
        ring
      linarith [e1, e2, e3]
    have hSsum : ∑ n ∈ bulkWindow CL N, (CL.psiHatL p X N n - κe * bulkSeqR CR p X N n) ^ 2 ≤
        (2 * (|CcL| * hm) ^ 2 + 2 * (|κe| ^ 2 * (|CcR| * hm) ^ 2)) * (C1 / Real.sqrt (Fz.step N)) := by
      refine (Finset.sum_le_sum per).trans ?_
      rw [hsplit]
      have h1 := mul_le_mul_of_nonneg_left hSL ha0
      have h2 := mul_le_mul_of_nonneg_left hSR hb0
      have e : (2 * (|CcL| * hm) ^ 2 + 2 * (|κe| ^ 2 * (|CcR| * hm) ^ 2)) * (C1 / Real.sqrt (Fz.step N)) =
          2 * (|CcL| * hm) ^ 2 * (C1 / Real.sqrt (Fz.step N)) +
            2 * (|κe| ^ 2 * (|CcR| * hm) ^ 2) * (C1 / Real.sqrt (Fz.step N)) := by ring
      rw [e]
      linarith [h1, h2]
    refine hSsum.trans ?_
    have hsq0 : 0 ≤ Real.sqrt (Fz.step N) := Real.sqrt_nonneg _
    calc (2 * (|CcL| * hm) ^ 2 + 2 * (|κe| ^ 2 * (|CcR| * hm) ^ 2)) * (C1 / Real.sqrt (Fz.step N))
        ≤ (2 * hm ^ 2 * Cc ^ 2 * (1 + |κe| ^ 2)) * (C1 / Real.sqrt (Fz.step N)) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = 2 * hm ^ 2 * Cc ^ 2 * (1 + |κe| ^ 2) * C1 / Real.sqrt (Fz.step N) := by ring
  -- the least-squares scalar (kappa_core)
  have hkc : (bulkKappa CL CR p X N - κe) ^ 2 ≤
      (2 * hm ^ 2 * Cc ^ 2 * (1 + |κe| ^ 2) * C1 / Real.sqrt (Fz.step N)) /
        (∑ n ∈ bulkWindow CL N, (bulkSeqR CR p X N n) ^ 2) :=
    kappa_core (bulkWindow CL N) (fun n => CL.psiHatL p X N n) (fun n => bulkSeqR CR p X N n) κe _ hDpos hE2
  have hEb : (2 * hm ^ 2 * Cc ^ 2 * (1 + |κe| ^ 2) * C1 / Real.sqrt (Fz.step N)) /
        (∑ n ∈ bulkWindow CL N, (bulkSeqR CR p X N n) ^ 2) ≤
      C2 * hm ^ 2 * (1 + |κe| ^ 2) := by
    have hpos : 0 < windowConst CR CA / Real.sqrt (Fz.step N) := div_pos hcW (Real.sqrt_pos.mpr hst)
    have h1 := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * hm ^ 2 * Cc ^ 2 * (1 + |κe| ^ 2) * C1 /
      Real.sqrt (Fz.step N)) hpos hDlow
    have e : (2 * hm ^ 2 * Cc ^ 2 * (1 + |κe| ^ 2) * C1 / Real.sqrt (Fz.step N)) /
        (windowConst CR CA / Real.sqrt (Fz.step N)) = C2 * hm ^ 2 * (1 + |κe| ^ 2) := by
      rw [hC2]
      have hs : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hst
      field_simp
    rw [e] at h1
    exact h1
  have hdiffκ : (bulkKappa CL CR p X N - κe) ^ 2 ≤ C2 * hm ^ 2 * (1 + κe ^ 2) := by
    have h := hkc.trans hEb
    rw [sq_abs] at h
    exact h
  have hκbound : |bulkKappa CL CR p X N| ≤ Cκ := (hκall p hp X hX N hN hsk).2.2.2.1
  have hC2small : (C2 + 1) * hm ≤ 1 / 2 := by
    have hmle : hm ≤ Fz.step N := pow_le_of_le_one hst.le hsle1 (by omega)
    have h1 := mul_le_mul_of_nonneg_left hsd (by linarith : (0 : ℝ) ≤ C2 + 1)
    have e : (C2 + 1) * (1 / (2 * (C2 + 1))) = 1 / 2 := by field_simp
    have h2 := mul_le_mul_of_nonneg_left hmle (by linarith : (0 : ℝ) ≤ C2 + 1)
    linarith
  obtain ⟨hκe2, hκdiff⟩ := kappa_e_bound (bulkKappa CL CR p X N) κe Cκ C2 hm hC20 hm0 hκbound hC2small hdiffκ
  have hκCκ0 : 0 ≤ Cκ := (abs_nonneg _).trans hκbound
  -- the final estimate at the window point n
  have hnL := window_sub_rows CL p hp X hX N hN1 hst n hn
  have hjR := window_sub_rows CR p hp X hX N hN2 hst ((N : ℤ) - n) (mirror_mem_window CL CR hcoup N hLs n hn)
  have hcn : CL.c' ≤ uNode (Fz.step N) n := by
    have h := hn
    unfold bulkWindow at h
    exact (Finset.mem_filter.mp h).2.1
  have hcjR : CR.c' ≤ uNode (Fz.step N) ((N : ℤ) - n) := by
    have h := mirror_mem_window CL CR hcoup N hLs n hn
    unfold bulkWindow at h
    exact (Finset.mem_filter.mp h).2.1
  have hnL' := Finset.mem_Icc.mp hnL
  have hjR' := Finset.mem_Icc.mp hjR
  have hxn0 := (LB n hnL'.1 hnL'.2).1
  have hyn0 := (RB ((N : ℤ) - n) hjR'.1 hjR'.2).1
  have hx := LD n hnL'.1 hnL'.2 hcn
  have hy := RD ((N : ℤ) - n) hjR'.1 hjR'.2 hcjR
  have hpR := RA ((N : ℤ) - n) hjR'.1 hjR'.2
  have hMn := (CL.M_osc p hp X hX N hN1 n hnL hcn).1
  have hfin := matching_arith (CL.psiHatL p X N n) (CR.psiHatL p X N ((N : ℤ) - n)) κe (bulkKappa CL CR p X N)
    (CL.envL p X N n) (CR.envL p X N ((N : ℤ) - n)) ((CL.chain p X N).M n) hm (Fz.step N ^ ((1 : ℝ) / 4))
    CL.cM |CcL| |CcR| Cκ (C2 + 1) CML CMR KgR hm0 hqq0 (abs_nonneg _) (abs_nonneg _) hκCκ0 (by linarith)
    hCML0.le hCMR0.le hKgR0.le hcM (hF1 n hn) hκdiff hκe2 hxn0 hyn0 hx hy hpR hMn
  exact hfin

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.kappa_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.kappa_core

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.sum_reflect_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.sum_reflect_window

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.kappa_e_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.kappa_e_bound

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.matching_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.matching_arith

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.env_sum_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.env_sum_inv

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.eigen_mirror_jacSol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.eigen_mirror_jacSol

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.eigen_last_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.eigen_last_ne_zero

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.eigen_left_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.eigen_left_profile

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.eigen_right_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.eigen_right_profile

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.chart_NR_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.chart_NR_le

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.window_sub_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.window_sub_rows

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.env_window_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.env_window_le

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.env_mirror_window_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.env_mirror_window_le

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.windowConst_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.windowConst_pos

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.mirror_mem_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.mirror_mem_window

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.bulk_matching_eig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.bulk_matching_eig

end FormalResearch.JacobiEigenvectors.TheoremB
