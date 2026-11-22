module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.Statements
public import FormalResearch.JacobiEigenvectors.Engine.Green

/-!
# Paper J, Layer 2 (L2.C5): counting zeros in windows (lem:tha-count)

Source: Paper J, `app_thmA.tex`, Lemma `lem:tha-count` ("Counting zeros in windows") and its proof: Green's identity
`D'(X) = sum_n p_n q_n`, the sign `D' = kappa' sum q_n^2` at a zero, and the alternation of the sign of `D'` between consecutive
zeros.  The statement is `TheoremA.PropThaCount` of `TheoremA/Statements.lean` (frozen; the hypotheses `1 <= N` and
`0 < bondA` are those of the corrected freeze).

## Main result

* `propThaCount` : `PropThaCount F μ N` for every family `F`, parameter `μ` and `N` (the statement is an implication in its
  hypotheses; no further hypothesis is needed).

## Proof outline (as formalised)

1. `pZ`, `qZ`: the `ℤ`-indexed versions of the solutions `pSol` (`p_0 = 1`, forward) and `qSol` (`q_N = 1`, backward).
   `pZ`, `qZ` satisfy the Jacobi row equations on `[0, N-1]` (resp. `[1, N]`) for the bonds `F.bondA μ N` and the diagonal
   `X - F.entryB μ N`; `F.bondA μ N` vanishes at `-1` and `N` (`Setting.SymbolFamily.bondA`), so the Green lemma
   `Engine.green_hasDerivAt` applies to `casD = cas bondA pZ qZ 0`.
2. `Sder X := sum_{i in [0,N]} pZ X i * qZ X i` is the derivative of `casD` (`HasDerivAt` everywhere).
3. At a zero of `casD`, `pZ X i = pZ X N * qZ X i` on `[0, N]` (the Casoratian is constant in `n`, the bonds are positive, and a
   downward induction on the row equations).  Hence `Sder X = pZ X N * sum qZ^2` with `sum qZ^2 >= qZ N^2 = 1`, so
   `sign Sder X = sign (pZ X N)` at a zero.
4. Real analysis of a `C^1`-everywhere function `f` with simple zeros: a positive derivative at a zero means `f > 0` on the right
   and `f < 0` on the left (`local_sign`); between two zeros `a < b` with `f' a > 0` there is a zero `c in (a, b]` with
   `f > 0` on `(a, c)` and `f' c <= 0` (`exists_first_zero`).
5. Uniqueness per window: two zeros in one window `w_k` have `e * Sder > 0` for the window sign `e = sigma' (-1)^k` (hypothesis
   (iii)), and `exists_first_zero` applied to `e * casD` yields a zero `c` between them in `w_k` with `e * Sder c <= 0`, a contradiction.
6. Existence per window: the IVT between preimages of `pi h k` and `pi h (k+1)` (hypothesis (ii)) gives a zero `X`; by (i) it lies in some
   window `w_j`, and since `Phi X` lies in `[pi h k, pi h (k+1)]` and `eps < pi h / 4`, `j = k`.

## Differences from the paper

None in the statement (it is the frozen `PropThaCount`).  The paper's windows are indexed by `k` without a range; the frozen statement
uses `k : ℕ` (consistent with the application, where the windows are the ones with `k >= 0`); the proof does not use this.  The
paper's continuity of `Phi` is not used (monotonicity suffices with the IVT on `D`).

## Not formalised

Nothing of lem:tha-count is left out.  The application of the lemma (checking (i)--(iii) for the eigenvalue windows, app_thmA
Step 5--6) is outside this file.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Filter Topology FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Engine

section Solutions

variable {Par : Type*} (F : SymbolFamily Par) (μ : Par) (N : ℕ)

/-- The `ℤ`-indexed forward solution `p_n(X) = pSol (n.toNat)`; the value at `n < 0` is irrelevant (it is multiplied by the hard edge). -/
def pZ (X : ℝ) (n : ℤ) : ℝ := pSol F μ N X n.toNat

/-- The `ℤ`-indexed backward solution `q_n(X) = qSol (N - n)`; `q_N = 1`. -/
def qZ (X : ℝ) (n : ℤ) : ℝ := qSol F μ N X (N - n).toNat

/-- `Sder X = sum_{i in [0,N]} p_i q_i`, the derivative of `casD` (Green). -/
def Sder (X : ℝ) : ℝ := ∑ i ∈ Icc (0 : ℤ) N, pZ F μ N X i * qZ F μ N X i

variable {F μ N}

lemma pZ_zero (X : ℝ) : pZ F μ N X 0 = 1 := by
  simp [pZ, pSol]

lemma pZ_one (X : ℝ) : pZ F μ N X 1 = (X - F.entryB μ N 0) / F.bondA μ N 0 := by
  simp [pZ, pSol]

lemma qZ_N (X : ℝ) : qZ F μ N X N = 1 := by
  simp [qZ, qSol]

lemma qZ_N_sub_one (X : ℝ) : qZ F μ N X ((N : ℤ) - 1) = (X - F.entryB μ N N) / F.bondA μ N ((N : ℤ) - 1) := by
  have h : (N : ℤ) - ((N : ℤ) - 1) = 1 := by ring
  simp only [qZ, h]
  simp [qSol]

/-- The forward recurrence `pSol (k+2)` in `ℤ`-indexed form, for `0 <= n`. -/
lemma pZ_succ_succ (X : ℝ) (n : ℤ) (hn : 0 ≤ n) :
    pZ F μ N X (n + 2) = ((X - F.entryB μ N (n + 1)) * pZ F μ N X (n + 1) - F.bondA μ N n * pZ F μ N X n) /
      F.bondA μ N (n + 1) := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  have e2 : ((k : ℤ) + 2).toNat = k + 2 := by omega
  have e1 : ((k : ℤ) + 1).toNat = k + 1 := by omega
  have e0 : ((k : ℤ)).toNat = k := by omega
  simp only [pZ, e2, e1, e0]
  rw [pSol]

/-- The backward recurrence in `ℤ`-indexed form: for `1 <= i <= N - 1`,
`A_{i-1} q_{i-1} = (X - B_i) q_i - A_i q_{i+1}`. -/
lemma qZ_rec (hpos : ∀ n : ℤ, 0 ≤ n → n < (N : ℤ) → 0 < F.bondA μ N n) (X : ℝ) (i : ℤ) (hi1 : 1 ≤ i)
    (hi2 : i ≤ (N : ℤ) - 1) :
    F.bondA μ N (i - 1) * qZ F μ N X (i - 1) =
      (X - F.entryB μ N i) * qZ F μ N X i - F.bondA μ N i * qZ F μ N X (i + 1) := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ, (s : ℤ) = (N : ℤ) - i - 1 := ⟨((N : ℤ) - i - 1).toNat, by omega⟩
  have e2 : ((N : ℤ) - (i - 1)).toNat = s + 2 := by omega
  have e1 : ((N : ℤ) - i).toNat = s + 1 := by omega
  have e0 : ((N : ℤ) - (i + 1)).toNat = s := by omega
  have hsN : (N : ℤ) - (s : ℤ) - 1 = i := by omega
  have hsN2 : (N : ℤ) - (s : ℤ) - 2 = i - 1 := by omega
  have hrec : qSol F μ N X (s + 2) =
      ((X - F.entryB μ N ((N : ℤ) - s - 1)) * qSol F μ N X (s + 1) -
        F.bondA μ N ((N : ℤ) - s - 1) * qSol F μ N X s) / F.bondA μ N ((N : ℤ) - s - 2) := by
    rw [qSol]
  rw [hsN, hsN2] at hrec
  have hne : F.bondA μ N (i - 1) ≠ 0 := (hpos (i - 1) (by omega) (by omega)).ne'
  simp only [qZ, e2, e1, e0]
  rw [hrec]
  field_simp


/-- Row equation of the forward solution: for `0 <= n <= N-1`, `A_n p_{n+1} + A_{n-1} p_{n-1} = (X - B_n) p_n`. -/
lemma pZ_rec (hpos : ∀ n : ℤ, 0 ≤ n → n < (N : ℤ) → 0 < F.bondA μ N n) (hN : 1 ≤ N) (X : ℝ) (n : ℤ)
    (hn0 : 0 ≤ n) (hn1 : n ≤ (N : ℤ) - 1) :
    F.bondA μ N n * pZ F μ N X (n + 1) + F.bondA μ N (n - 1) * pZ F μ N X (n - 1) =
      (X - F.entryB μ N n) * pZ F μ N X n := by
  rcases (show n = 0 ∨ 1 ≤ n by omega) with h | h
  · subst h
    have hb : F.bondA μ N (0 - 1) = 0 := by simp [SymbolFamily.bondA]
    have hne : F.bondA μ N 0 ≠ 0 := (hpos 0 le_rfl (by omega)).ne'
    rw [hb, zero_mul, zero_add, pZ_one, pZ_zero, mul_div_cancel₀ _ hne]
    ring
  · obtain ⟨k, rfl⟩ : ∃ k : ℤ, n = k + 1 := ⟨n - 1, by ring⟩
    have hk0 : 0 ≤ k := by omega
    have hne : F.bondA μ N (k + 1) ≠ 0 := (hpos (k + 1) (by omega) (by omega)).ne'
    rw [show k + 1 - 1 = k by ring, show k + 1 + 1 = k + 2 by ring, pZ_succ_succ X k hk0]
    field_simp
    ring

/-- The `p`-row equation in the form of `Engine.Lop`. -/
lemma Lop_pZ (hpos : ∀ n : ℤ, 0 ≤ n → n < (N : ℤ) → 0 < F.bondA μ N n) (hN : 1 ≤ N) (X : ℝ) (i : ℤ)
    (hi0 : 0 ≤ i) (hi1 : i ≤ (N : ℤ) - 1) :
    Lop (F.bondA μ N) (fun n => X - F.entryB μ N n) (pZ F μ N X) i = 0 := by
  have := pZ_rec hpos hN X i hi0 hi1
  simp only [Lop]
  linarith

/-- The backward row equation, for `1 <= i <= N` (`qZ_N` and the hard edge `bondA N = 0` at the last row). -/
lemma Lop_qZ (hpos : ∀ n : ℤ, 0 ≤ n → n < (N : ℤ) → 0 < F.bondA μ N n) (hN : 1 ≤ N) (X : ℝ) (i : ℤ)
    (hi1 : 1 ≤ i) (hi2 : i ≤ (N : ℤ)) :
    Lop (F.bondA μ N) (fun n => X - F.entryB μ N n) (qZ F μ N X) i = 0 := by
  simp only [Lop]
  rcases (show i ≤ (N : ℤ) - 1 ∨ i = N by omega) with h | h
  · have := qZ_rec hpos X i hi1 h
    linarith
  · subst h
    have hbN : F.bondA μ N (N : ℤ) = 0 := by simp [SymbolFamily.bondA]
    have hne : F.bondA μ N ((N : ℤ) - 1) ≠ 0 := (hpos ((N : ℤ) - 1) (by omega) (by omega)).ne'
    rw [hbN, zero_mul, zero_add, qZ_N_sub_one, qZ_N, mul_div_cancel₀ _ hne]
    ring

/-- The Casoratian at the bond `0` is `casD`. -/
lemma casD_eq_cas (X : ℝ) :
    casD F μ N X = cas (F.bondA μ N) (pZ F μ N X) (qZ F μ N X) 0 := by
  have h1 : pZ F μ N X (0 + 1) = pSol F μ N X 1 := by simp [pZ]
  have h2 : qZ F μ N X 0 = qSol F μ N X N := by simp [qZ]
  have h3 : qZ F μ N X (0 + 1) = qSol F μ N X (N - 1) := by
    simp only [qZ]
    congr 1
    omega
  have h0' : pSol F μ N X 0 = 1 := by simp [pSol]
  unfold casD cas
  rw [h1, h2, h3, pZ_zero, h0']

lemma differentiable_pSol (n : ℕ) :
    Differentiable ℝ (fun Z => pSol F μ N Z n) ∧ Differentiable ℝ (fun Z => pSol F μ N Z (n + 1)) := by
  induction n with
  | zero =>
    constructor
    · have e : (fun Z => pSol F μ N Z 0) = fun _ => (1 : ℝ) := funext fun Z => by simp [pSol]
      rw [e]
      exact differentiable_const _
    · have e : (fun Z => pSol F μ N Z (0 + 1)) = fun Z => (Z - F.entryB μ N 0) / F.bondA μ N 0 :=
        funext fun Z => by simp [pSol]
      rw [e]
      exact (differentiable_id.sub_const _).div_const _
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have e : (fun Z => pSol F μ N Z (n + 1 + 1)) = fun Z =>
        ((Z - F.entryB μ N ((n : ℤ) + 1)) * pSol F μ N Z (n + 1) - F.bondA μ N n * pSol F μ N Z n) /
          F.bondA μ N ((n : ℤ) + 1) :=
      funext fun Z => by rw [pSol]
    rw [e]
    exact (((differentiable_id.sub_const _).mul ih.2).sub (ih.1.const_mul _)).div_const _

lemma hasDerivAt_pZ (i : ℤ) (X : ℝ) : HasDerivAt (fun Z => pZ F μ N Z i) (deriv (fun Z => pZ F μ N Z i) X) X := by
  have hd : Differentiable ℝ (fun Z => pZ F μ N Z i) := (differentiable_pSol i.toNat).1
  exact (hd X).hasDerivAt

/-- Green's identity (lem:tha-count): `D = casD` has derivative `sum_{i in [0,N]} p_i q_i` at every energy. -/
lemma hasDerivAt_casD (hpos : ∀ n : ℤ, 0 ≤ n → n < (N : ℤ) → 0 < F.bondA μ N n) (hN : 1 ≤ N) (X : ℝ) :
    HasDerivAt (fun Y => casD F μ N Y) (Sder F μ N X) X := by
  have hA1 : F.bondA μ N (-1) = 0 := by simp [SymbolFamily.bondA]
  have hAN : F.bondA μ N N = 0 := by simp [SymbolFamily.bondA]
  have key := green_hasDerivAt (F.bondA μ N) (F.entryB μ N) (N : ℤ) (by exact_mod_cast hN) hA1 hAN
    (fun Y => pZ F μ N Y) (fun Y => qZ F μ N Y) (fun Y i => deriv (fun Z => pZ F μ N Z i) Y)
    (fun Y => pZ_zero Y) (fun Y i hi => Lop_pZ hpos hN Y i (mem_Icc.1 hi).1 (mem_Icc.1 hi).2)
    (fun Y i hi => Lop_qZ hpos hN Y i (mem_Icc.1 hi).1 (mem_Icc.1 hi).2)
    (fun Y => qZ_N Y) (fun Y i => hasDerivAt_pZ i Y) X
  have hfun : (fun Y => casD F μ N Y) = fun Y => cas (F.bondA μ N) (pZ F μ N Y) (qZ F μ N Y) 0 :=
    funext fun Y => casD_eq_cas Y
  rw [hfun]
  exact key

/-- At a zero of `casD`, `p_i = p_N q_i` on `[0, N]` (proportionality of the two solutions). -/
lemma zero_prop (hpos : ∀ n : ℤ, 0 ≤ n → n < (N : ℤ) → 0 < F.bondA μ N n) (hN : 1 ≤ N) {X : ℝ}
    (h0 : casD F μ N X = 0) : ∀ i ∈ Icc (0 : ℤ) N, pZ F μ N X i = pZ F μ N X N * qZ F μ N X i := by
  have hA1 : F.bondA μ N (-1) = 0 := by simp [SymbolFamily.bondA]
  have hc := green_cas_const (F.bondA μ N) (F.entryB μ N) X (N : ℤ) (pZ F μ N X) (qZ F μ N X)
    (fun i hi => Lop_pZ hpos hN X i (mem_Icc.1 hi).1 (mem_Icc.1 hi).2)
    (fun i hi => Lop_qZ hpos hN X i (mem_Icc.1 hi).1 (mem_Icc.1 hi).2)
  have hcas0 : cas (F.bondA μ N) (pZ F μ N X) (qZ F μ N X) 0 = 0 := by
    rw [← casD_eq_cas]
    exact h0
  have hcasN1 : cas (F.bondA μ N) (pZ F μ N X) (qZ F μ N X) ((N : ℤ) - 1) = 0 :=
    (hc ((N : ℤ) - 1) (mem_Icc.2 ⟨by omega, le_rfl⟩)).trans hcas0
  have hne : F.bondA μ N ((N : ℤ) - 1) ≠ 0 := (hpos ((N : ℤ) - 1) (by omega) (by omega)).ne'
  have hNm : (N : ℤ) - 1 + 1 = N := by ring
  unfold cas at hcasN1
  rw [hNm, qZ_N] at hcasN1
  have hlast : pZ F μ N X (N : ℤ) * qZ F μ N X ((N : ℤ) - 1) - pZ F μ N X ((N : ℤ) - 1) = 0 := by
    rcases mul_eq_zero.1 hcasN1 with h | h
    · exact absurd h hne
    · linarith
  obtain ⟨d, hd⟩ : ∃ d : ℤ → ℝ, ∀ i, d i = pZ F μ N X i - pZ F μ N X N * qZ F μ N X i :=
    ⟨_, fun i => rfl⟩
  have hdN : d N = 0 := by rw [hd, qZ_N]; ring
  have hdN1 : d ((N : ℤ) - 1) = 0 := by rw [hd]; linarith
  have hrow : ∀ i : ℤ, 1 ≤ i → i ≤ (N : ℤ) - 1 →
      F.bondA μ N i * d (i + 1) + F.bondA μ N (i - 1) * d (i - 1) - (X - F.entryB μ N i) * d i = 0 := by
    intro i hi1 hi2
    have h1 := Lop_pZ hpos hN X i (by omega) hi2
    have h2 := Lop_qZ hpos hN X i hi1 (by omega)
    simp only [Lop] at h1 h2
    rw [hd, hd, hd]
    linear_combination h1 - pZ F μ N X N * h2
  have hind : ∀ m : ℕ, (m : ℤ) + 1 ≤ N → d ((N : ℤ) - 1 - m) = 0 ∧ d ((N : ℤ) - m) = 0 := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨by simpa using hdN1, by simpa using hdN⟩
    | succ m ih =>
      intro hm
      push_cast at hm
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hr := hrow ((N : ℤ) - 1 - m) (by omega) (by omega)
      have e1 : (N : ℤ) - 1 - m + 1 = N - m := by ring
      rw [e1, ih2, ih1] at hr
      have hne' : F.bondA μ N ((N : ℤ) - 1 - m - 1) ≠ 0 :=
        (hpos _ (by omega) (by omega)).ne'
      have hd' : d ((N : ℤ) - 1 - m - 1) = 0 := by
        have : F.bondA μ N ((N : ℤ) - 1 - m - 1) * d ((N : ℤ) - 1 - m - 1) = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hne'
        · exact h
      refine ⟨?_, ?_⟩
      · push_cast
        rw [show (N : ℤ) - 1 - (m + 1) = (N : ℤ) - 1 - m - 1 by ring]
        exact hd'
      · push_cast
        rw [show (N : ℤ) - (m + 1) = (N : ℤ) - 1 - m by ring]
        exact ih1
  intro i hi
  have hi' := mem_Icc.1 hi
  rcases (show i = N ∨ i ≤ (N : ℤ) - 1 by omega) with h | h
  · subst h
    rw [qZ_N, mul_one]
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = (N : ℤ) - 1 - i := ⟨((N : ℤ) - 1 - i).toNat, by omega⟩
    have := (hind m (by omega)).1
    rw [show (N : ℤ) - 1 - m = i by omega, hd] at this
    linarith

/-- `Sder` at a zero of `casD`: `Sder = p_N * sum q_i^2`. -/
lemma Sder_zero (hpos : ∀ n : ℤ, 0 ≤ n → n < (N : ℤ) → 0 < F.bondA μ N n) (hN : 1 ≤ N) {X : ℝ}
    (h0 : casD F μ N X = 0) : Sder F μ N X = pZ F μ N X N * ∑ i ∈ Icc (0 : ℤ) N, qZ F μ N X i ^ 2 := by
  unfold Sder
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [zero_prop hpos hN h0 i hi]
  ring

lemma sum_qZ_sq_pos (hN : 1 ≤ N) (X : ℝ) : 0 < ∑ i ∈ Icc (0 : ℤ) N, qZ F μ N X i ^ 2 := by
  have hmem : (N : ℤ) ∈ Icc (0 : ℤ) N := mem_Icc.2 ⟨by omega, le_rfl⟩
  have h := Finset.single_le_sum (f := fun i => qZ F μ N X i ^ 2) (fun i _ => sq_nonneg _) hmem
  have hq : qZ F μ N X N ^ 2 = 1 := by rw [qZ_N]; norm_num
  have h' : qZ F μ N X N ^ 2 ≤ ∑ i ∈ Icc (0 : ℤ) N, qZ F μ N X i ^ 2 := h
  linarith

end Solutions

/-! ### Real analysis of a function with a derivative everywhere -/

/-- A positive derivative at a zero: the function is positive on the right and negative on the left, near the zero. -/
lemma count_local_sign {f : ℝ → ℝ} {f' a : ℝ} (hf : HasDerivAt f f' a) (ha : f a = 0) (hpos : 0 < f') :
    ∃ δ > 0, (∀ t, a < t → t < a + δ → 0 < f t) ∧ (∀ t, a - δ < t → t < a → f t < 0) := by
  have hs : Tendsto (slope f a) (𝓝[≠] a) (𝓝 f') := hasDerivAt_iff_tendsto_slope.1 hf
  have h1 : ∀ᶠ t in 𝓝[≠] a, 0 < slope f a t := hs.eventually (lt_mem_nhds hpos)
  have h2 : ∀ᶠ t in 𝓝 a, t ≠ a → 0 < slope f a t := eventually_nhdsWithin_iff.1 h1
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 h2
  have key : ∀ t, a < t ∨ t < a → |t - a| < δ → 0 < f t / (t - a) := by
    intro t ht htd
    have hta : t ≠ a := by
      rcases ht with h | h
      · exact h.ne'
      · exact h.ne
    have := hball (y := t) (by rw [Real.dist_eq]; exact htd) hta
    rwa [slope_def_field, ha, sub_zero] at this
  refine ⟨δ, hδ, fun t h1 h2 => ?_, fun t h1 h2 => ?_⟩
  · have h := key t (Or.inl h1) (by rw [abs_lt]; constructor <;> linarith)
    rcases div_pos_iff.1 h with ⟨h3, _⟩ | ⟨_, h4⟩
    · exact h3
    · linarith
  · have h := key t (Or.inr h2) (by rw [abs_lt]; constructor <;> linarith)
    rcases div_pos_iff.1 h with ⟨_, h4⟩ | ⟨h3, _⟩
    · linarith
    · exact h3

/-- Between two zeros `a < b` of a function with a derivative everywhere, if the derivative at `a` is positive, there is a
zero `c` in `(a, b]` with `f > 0` on `(a, c)` and `f' c <= 0`. -/
lemma count_first_zero {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) {a b : ℝ} (hab : a < b) (ha : f a = 0)
    (hb : f b = 0) (hpos : 0 < f' a) : ∃ c, a < c ∧ c ≤ b ∧ f c = 0 ∧ f' c ≤ 0 := by
  obtain ⟨δ, hδ, hright, -⟩ := count_local_sign (hf a) ha hpos
  have hcont : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  obtain ⟨δ', hδ'pos, hδ'le, hδ'half⟩ : ∃ δ' : ℝ, 0 < δ' ∧ δ' ≤ δ ∧ δ' ≤ (b - a) / 2 :=
    ⟨min δ ((b - a) / 2), lt_min hδ (by linarith), min_le_left _ _, min_le_right _ _⟩
  set Z : Set ℝ := Set.Icc (a + δ') b ∩ {t | f t ≤ 0} with hZdef
  have hZc : IsClosed Z := isClosed_Icc.inter (isClosed_le hcont continuous_const)
  have hZne : Z.Nonempty := ⟨b, ⟨⟨by linarith, le_rfl⟩, le_of_eq hb⟩⟩
  have hZb : BddBelow Z := ⟨a + δ', fun t ht => ht.1.1⟩
  have hcmem : sInf Z ∈ Z := hZc.csInf_mem hZne hZb
  have hc1 : a + δ' ≤ sInf Z := hcmem.1.1
  have hc2 : sInf Z ≤ b := hcmem.1.2
  have hfc : f (sInf Z) ≤ 0 := hcmem.2
  have hac : a < sInf Z := by linarith
  have hpos_int : ∀ t, a < t → t < sInf Z → 0 < f t := by
    intro t ht1 ht2
    by_cases ht : t < a + δ'
    · exact hright t ht1 (by linarith)
    · have ht' : a + δ' ≤ t := not_lt.1 ht
      by_contra hneg
      have hneg' : f t ≤ 0 := not_lt.1 hneg
      have htZ : t ∈ Z := ⟨⟨ht', by linarith⟩, hneg'⟩
      have := csInf_le hZb htZ
      linarith
  have hfc0 : f (sInf Z) = 0 := by
    by_contra hne
    have hlt : f (sInf Z) < 0 := lt_of_le_of_ne hfc hne
    have hev : ∀ᶠ t in 𝓝 (sInf Z), f t < 0 := (hf (sInf Z)).continuousAt.eventually (gt_mem_nhds hlt)
    obtain ⟨η, hη, hηball⟩ := Metric.eventually_nhds_iff.1 hev
    have hm0 : 0 < min (η / 2) ((sInf Z - a) / 2) := lt_min (by linarith) (by linarith)
    have hm1 : min (η / 2) ((sInf Z - a) / 2) ≤ η / 2 := min_le_left _ _
    have hm2 : min (η / 2) ((sInf Z - a) / 2) ≤ (sInf Z - a) / 2 := min_le_right _ _
    have h1 := hpos_int (sInf Z - min (η / 2) ((sInf Z - a) / 2)) (by linarith) (by linarith)
    have h2 := hηball (y := sInf Z - min (η / 2) ((sInf Z - a) / 2))
      (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    linarith
  have hfc' : f' (sInf Z) ≤ 0 := by
    by_contra hgt
    have hgt' : 0 < f' (sInf Z) := not_le.1 hgt
    obtain ⟨δc, hδc, -, hleft⟩ := count_local_sign (hf (sInf Z)) hfc0 hgt'
    have hm0 : 0 < min (δc / 2) ((sInf Z - a) / 2) := lt_min (by linarith) (by linarith)
    have hm1 : min (δc / 2) ((sInf Z - a) / 2) ≤ δc / 2 := min_le_left _ _
    have hm2 : min (δc / 2) ((sInf Z - a) / 2) ≤ (sInf Z - a) / 2 := min_le_right _ _
    have h1 := hpos_int (sInf Z - min (δc / 2) ((sInf Z - a) / 2)) (by linarith) (by linarith)
    have h2 := hleft (sInf Z - min (δc / 2) ((sInf Z - a) / 2)) (by linarith) (by linarith)
    linarith
  exact ⟨sInf Z, hac, hc2, hfc0, hfc'⟩

/-- Sign of `f` between a window point and the monotone image: a point `t` of `uIcc x y` has `Phi t` in `uIcc (Phi x) (Phi y)`. -/
lemma count_mem_uIcc_image {Φ : ℝ → ℝ} {I : Set ℝ} (hmono : StrictMonoOn Φ I ∨ StrictAntiOn Φ I) {x y t : ℝ}
    (hx : x ∈ I) (hy : y ∈ I) (ht : t ∈ Set.uIcc x y) (htI : t ∈ I) : Φ t ∈ Set.uIcc (Φ x) (Φ y) := by
  rcases hmono with h | h
  · rcases Set.mem_uIcc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Set.mem_uIcc.2 (Or.inl ⟨h.monotoneOn hx htI h1, h.monotoneOn htI hy h2⟩)
    · exact Set.mem_uIcc.2 (Or.inr ⟨h.monotoneOn hy htI h1, h.monotoneOn htI hx h2⟩)
  · rcases Set.mem_uIcc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Set.mem_uIcc.2 (Or.inr ⟨h.antitoneOn htI hy h2, h.antitoneOn hx htI h1⟩)
    · exact Set.mem_uIcc.2 (Or.inl ⟨h.antitoneOn htI hx h2, h.antitoneOn hy htI h1⟩)

/-- Sign of a real number as a product: `sign x = sign s` with `s = 1 ∨ s = -1` gives `0 < s * x`. -/
lemma count_pos_of_sign_eq {x s : ℝ} (hs : s = 1 ∨ s = -1) (h : SignType.sign x = SignType.sign s) :
    0 < s * x := by
  rcases hs with rfl | rfl
  · have h1 : SignType.sign x = 1 := by rw [h]; simp
    have := sign_eq_one_iff.1 h1
    linarith
  · have h1 : SignType.sign x = -1 := by rw [h]; simp
    have := sign_eq_neg_one_iff.1 h1
    linarith

/-- The index argument of the existence part: a window point `Phi X` in `[H k, H (k+1)]` and a window centre `H (j + 1/2)`
within `eps < H/4` force `j = k`. -/
lemma count_window_index {H ε Φv : ℝ} {j k : ℕ} (hH : 0 < H) (hε : ε < H / 4) (hΦ1 : H * k ≤ Φv)
    (hΦ2 : Φv ≤ H * (k + 1)) (hj : |Φv - H * ((j : ℝ) + 1 / 2)| ≤ ε) : j = k := by
  obtain ⟨hj1, hj2⟩ := abs_le.1 hj
  rcases lt_trichotomy j k with h | h | h
  · exfalso
    have h' : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
    have := mul_le_mul_of_nonneg_left (show (j : ℝ) + 1 / 2 ≤ (k : ℝ) - 1 / 2 by linarith) hH.le
    nlinarith
  · exact h
  · exfalso
    have h' : (k : ℝ) + 1 ≤ j := by exact_mod_cast h
    have := mul_le_mul_of_nonneg_left (show (k : ℝ) + 3 / 2 ≤ (j : ℝ) + 1 / 2 by linarith) hH.le
    nlinarith

/-! ### The counting lemma -/

/-- **lem:tha-count** (`PropThaCount`, proved): for every family, parameter and `N`, the zeros of `casD` in an interval `I` on which
`Phi` is continuous and strictly monotone are simple, at most one lies in each window `w_k`, and each window whose bracketing
interval lies in `Phi(I)` contains exactly one.  The hypotheses (i)--(iii) are those of the frozen statement. -/
theorem propThaCount (F : SymbolFamily Par) (μ : Par) (N : ℕ) : PropThaCount F μ N := by
  intro hN hpos I Φ ε hI _hΦc hmono hε0 hε1 hwin hsgn hsgn'
  obtain ⟨σ, hσ, hsg⟩ := hsgn
  obtain ⟨σ', hσ', hsg'⟩ := hsgn'
  have hH : 0 < Real.pi * F.step N := by
    have := Real.pi_pos
    linarith
  have hD : ∀ X, HasDerivAt (fun Y => casD F μ N Y) (Sder F μ N X) X := hasDerivAt_casD hpos hN
  have hDcont : Continuous (fun Y => casD F μ N Y) :=
    continuous_iff_continuousAt.2 fun X => (hD X).continuousAt
  -- the sign of the derivative at a zero of a window
  have hEpos : ∀ X ∈ I, ∀ k : ℕ, casD F μ N X = 0 →
      |Φ X - Real.pi * F.step N * ((k : ℝ) + 1 / 2)| ≤ ε → 0 < (σ' * (-1) ^ k) * Sder F μ N X := by
    intro X hX k h0 hwk
    have hκ : ∀ n : ℕ, n ≤ N → pSol F μ N X n = pZ F μ N X N * qSol F μ N X (N - n) := by
      intro n hn
      have h := zero_prop hpos hN h0 (n : ℤ) (mem_Icc.2 ⟨by omega, by omega⟩)
      have e1 : pZ F μ N X (n : ℤ) = pSol F μ N X n := by simp [pZ]
      have e2 : qZ F μ N X (n : ℤ) = qSol F μ N X (N - n) := by
        simp only [qZ]
        congr 1
        omega
      rw [← e1, h, e2]
    have hsgn_eq := hsg' X hX k h0 hwk (pZ F μ N X N) hκ
    have he : σ' * (-1) ^ k = 1 ∨ σ' * (-1) ^ k = -1 := by
      rcases hσ' with h1 | h1 <;> rcases neg_one_pow_eq_or ℝ k with h2 | h2 <;> simp [h1, h2]
    have hpe := count_pos_of_sign_eq he hsgn_eq
    rw [Sder_zero hpos hN h0, ← mul_assoc]
    exact mul_pos hpe (sum_qZ_sq_pos hN X)
  -- betweenness inside a window
  have hwin_between : ∀ (k : ℕ) (a b t : ℝ), a ∈ I → b ∈ I → t ∈ Set.Icc a b → t ∈ I →
      |Φ a - Real.pi * F.step N * ((k : ℝ) + 1 / 2)| ≤ ε → |Φ b - Real.pi * F.step N * ((k : ℝ) + 1 / 2)| ≤ ε →
      |Φ t - Real.pi * F.step N * ((k : ℝ) + 1 / 2)| ≤ ε := by
    intro k a b t ha hb ht htI hwa hwb
    obtain ⟨hta, htb⟩ := ht
    have hu : Φ t ∈ Set.uIcc (Φ a) (Φ b) :=
      count_mem_uIcc_image hmono ha hb (Set.mem_uIcc.2 (Or.inl ⟨hta, htb⟩)) htI
    obtain ⟨ha1, ha2⟩ := abs_le.1 hwa
    obtain ⟨hb1, hb2⟩ := abs_le.1 hwb
    rcases Set.mem_uIcc.1 hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact abs_le.2 ⟨by linarith, by linarith⟩
    · exact abs_le.2 ⟨by linarith, by linarith⟩
  -- uniqueness of the zero in a window, for `a < b`
  have uniq_aux : ∀ (k : ℕ) (a b : ℝ), a ∈ I → b ∈ I → casD F μ N a = 0 → casD F μ N b = 0 →
      |Φ a - Real.pi * F.step N * ((k : ℝ) + 1 / 2)| ≤ ε →
      |Φ b - Real.pi * F.step N * ((k : ℝ) + 1 / 2)| ≤ ε → a < b → False := by
    intro k a b ha hb hza hzb hwa hwb hab
    have hsub : Set.Icc a b ⊆ I := hI.out ha hb
    obtain ⟨e, he⟩ : ∃ e : ℝ, e = σ' * (-1) ^ k := ⟨_, rfl⟩
    have hea : 0 < e * Sder F μ N a := by
      rw [he]
      exact hEpos a ha k hza hwa
    obtain ⟨c, hac, hcb, hfc, hfc'⟩ :=
      count_first_zero (f := fun x => e * casD F μ N x) (f' := fun x => e * Sder F μ N x)
        (fun x => (hD x).const_mul e) hab (by simp [hza]) (by simp [hzb]) hea
    have hcmem : c ∈ Set.Icc a b := ⟨hac.le, hcb⟩
    have hcI : c ∈ I := hsub hcmem
    have he0 : e ≠ 0 := by
      rintro rfl
      simp at hea
    have hzc : casD F μ N c = 0 := by
      have h' : e * casD F μ N c = 0 := hfc
      exact (mul_eq_zero.1 h').resolve_left he0
    have hwc := hwin_between k a b c ha hb hcmem hcI hwa hwb
    have hpc := hEpos c hcI k hzc hwc
    rw [← he] at hpc
    have hfc'' : e * Sder F μ N c ≤ 0 := hfc'
    linarith
  refine ⟨?_, ?_⟩
  · -- at most one zero in each window
    intro k X hX X' hX' hz hz' hwX hwX'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact uniq_aux k X X' hX hX' hz hz' hwX hwX' hlt
    · exact uniq_aux k X' X hX' hX hz' hz hwX' hwX hlt
  · -- exactly one zero in each window whose bracketing interval lies in `Phi(I)`
    intro k hsubk
    have hkle : Real.pi * F.step N * (k : ℝ) ≤ Real.pi * F.step N * ((k : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hH.le
    obtain ⟨xa, hxa, hxa'⟩ := hsubk ⟨le_rfl, hkle⟩
    obtain ⟨xb, hxb, hxb'⟩ := hsubk ⟨hkle, le_rfl⟩
    have hDa := hsg xa hxa k hxa'
    have hDb := hsg xb hxb (k + 1) (by rw [hxb', Nat.cast_succ])
    have hs : σ * (-1) ^ k = 1 ∨ σ * (-1) ^ k = -1 := by
      rcases hσ with h1 | h1 <;> rcases neg_one_pow_eq_or ℝ k with h2 | h2 <;> simp [h1, h2]
    have hsb : σ * (-1) ^ (k + 1) = -(σ * (-1) ^ k) := by ring
    rw [hsb] at hDb
    have hs' : -(σ * (-1) ^ k) = 1 ∨ -(σ * (-1) ^ k) = -1 := by
      rcases hs with h | h
      · right
        linarith
      · left
        linarith
    have hpa := count_pos_of_sign_eq hs hDa
    have hpb := count_pos_of_sign_eq hs' hDb
    have hss : (σ * (-1) ^ k) * (σ * (-1) ^ k) = 1 := by
      rcases hs with h | h <;> rw [h] <;> norm_num
    have hprod : casD F μ N xa * casD F μ N xb < 0 := by
      have e1 : (σ * (-1) ^ k * casD F μ N xa) * (-(σ * (-1) ^ k) * casD F μ N xb) =
          -(casD F μ N xa * casD F μ N xb) := by
        linear_combination (-(casD F μ N xa * casD F μ N xb)) * hss
      linarith [mul_pos hpa hpb]
    -- intermediate value theorem for `casD` between `xa` and `xb`
    have hsubI : Set.uIcc xa xb ⊆ I := hI.uIcc_subset hxa hxb
    have hcontU : ContinuousOn (fun Y => casD F μ N Y) (Set.uIcc xa xb) := hDcont.continuousOn
    have h0mem : (0 : ℝ) ∈ Set.uIcc (casD F μ N xa) (casD F μ N xb) := by
      have : (casD F μ N xa ≤ 0 ∧ 0 ≤ casD F μ N xb) ∨ (casD F μ N xb ≤ 0 ∧ 0 ≤ casD F μ N xa) := by
        rcases le_total (casD F μ N xa) 0 with h1 | h1 <;> rcases le_total (casD F μ N xb) 0 with h2 | h2 <;>
          first
          | exact Or.inl ⟨h1, h2⟩
          | exact Or.inr ⟨h2, h1⟩
          | nlinarith
      exact Set.mem_uIcc.2 this
    obtain ⟨X, hXu, hXz⟩ := intermediate_value_uIcc hcontU h0mem
    have hXI : X ∈ I := hsubI hXu
    have hΦu : Φ X ∈ Set.uIcc (Φ xa) (Φ xb) := count_mem_uIcc_image hmono hxa hxb hXu hXI
    rw [hxa', hxb', Set.uIcc_of_le hkle] at hΦu
    obtain ⟨hΦ1, hΦ2⟩ := hΦu
    obtain ⟨j, hj⟩ := hwin X hXI hXz
    have hjk : j = k := count_window_index (H := Real.pi * F.step N) hH hε1 hΦ1 hΦ2 hj
    refine ⟨X, hXI, hXz, ?_⟩
    rw [hjk] at hj
    exact hj

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.propThaCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.propThaCount


end FormalResearch.JacobiEigenvectors.TheoremA

end
