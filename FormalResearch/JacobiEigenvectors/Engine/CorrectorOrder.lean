module

public import Mathlib

/-!
# Paper J engine, L1.2 (part 1): uniform orders in `h`, polynomial expansions and the parity lift

Source: bookkeeping for `thm:eng-corr` (`engine.tex`, "Every order"; proof in `app_engine.tex`, "Proof of Theorem
`thm:eng-corr`").  Namespace `FormalResearch.JacobiEigenvectors.Engine`.  No paper statement is formalised here: this file is the order
calculus that makes the paper's finitely many Taylor expansions in `h` an algebraic induction.

## Content
* `UO n f`: `f(u,h) = O(h^n)` as `h → 0`, **uniformly in `u ∈ ℝ`** (`∃ C δ>0, ∀ u, |h|<δ → |f u h| ≤ C |h|^n`),
  with the usual calculus (`UO.add`, `UO.mul`, `UO.mono`, ...).
* `PApprox N f`: `f` has a *uniform polynomial expansion of order `N` in `h`*: there are a degree bound `D`, a bound
  `C` and polynomials `p(u) ∈ ℝ[X]` of degree `≤ D` with all coefficients bounded by `C` such that
  `f(u,h) - p(u)(h) = O(h^N)` uniformly.  The coefficients are *not* prescribed (they are the Taylor coefficients of the
  paper).  `PApprox N` is closed under sums, products and `h`-monomials (`PApprox.add`, `PApprox.mul`, ...).
* `poly_vanish`: a polynomial that is `O(|h|^n)` near `0` has vanishing coefficients below `n`.
* `PApprox.peel`: if `f` has a `PApprox (n+1)` expansion and `f = O(h^n)` then `f - h^n a = O(h^{n+1})` for a bounded
  `a` (the order-`n` coefficient); `PApprox.lift` (**parity lift**): if moreover `f(u,-h) = σ f(u,h)` with
  `σ (-1)^n = -1` then `f = O(h^{n+1})`; `PApprox.exists_coeff`: if `σ (-1)^n = +1` and `f` has a `PApprox (n+2)`
  expansion and `f = O(h^n)` then `f = h^n a + O(h^{n+2})` for a bounded `a`.  These are the statements the paper
  uses as "an even `C^{2k+2}` function of `h` whose Taylor coefficients below `h^{2k+2}` vanish is `O(h^{2k+2})`".
* `BSmooth N g`: `g : ℝ → ℝ` is `N` times differentiable with all derivatives of order `≤ N` bounded on `ℝ`; the
  Taylor lemma `BSmooth.taylor` and `BSmooth.papprox_shift` (`h ↦ g(u + c h)` has a `PApprox N` expansion).

## Differences from the paper
The paper works on an interval `I_u` with sup norms over `I_u`; here every uniformity is over **all `u ∈ ℝ`** (data are
globally defined with globally bounded derivatives).  This matches the global form of the algebraic identities already
required by `SymplecticLadder` (see the docstring of `Defect`).  A localised version needs a thickening of `I_u` by `δ`
at every shift; it is not formalised.

Not formalised: `UO`, `PApprox` for functions of several parameters (the parameter `μ` of `prop:eng-corr1` is not carried).
-/

@[expose] public section

open Finset Polynomial

namespace FormalResearch.JacobiEigenvectors.Engine

/-! ### Uniform big-O -/

/-- `UO n f`: `f(u,h) = O(h^n)` as `h → 0`, uniformly in `u ∈ ℝ`. -/
def UO (n : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ C δ : ℝ, 0 < δ ∧ ∀ u h : ℝ, |h| < δ → |f u h| ≤ C * |h| ^ n

/-- A normalised form of `UO`: nonnegative constant, `δ ≤ 1`. -/
lemma UO.norm {n : ℕ} {f : ℝ → ℝ → ℝ} (hf : UO n f) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ δ ≤ 1 ∧ ∀ u h : ℝ, |h| < δ → |f u h| ≤ C * |h| ^ n := by
  obtain ⟨C, δ, hδ, H⟩ := hf
  refine ⟨|C|, min δ 1, abs_nonneg _, lt_min hδ one_pos, min_le_right _ _, fun u h hh => ?_⟩
  have h1 : |h| < δ := lt_of_lt_of_le hh (min_le_left _ _)
  calc |f u h| ≤ C * |h| ^ n := H u h h1
    _ ≤ |C| * |h| ^ n := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)

lemma UO.of_norm {n : ℕ} {f : ℝ → ℝ → ℝ} {C δ : ℝ} (hδ : 0 < δ)
    (H : ∀ u h : ℝ, |h| < δ → |f u h| ≤ C * |h| ^ n) : UO n f := ⟨C, δ, hδ, H⟩

lemma UO.mono {n m : ℕ} {f : ℝ → ℝ → ℝ} (hnm : n ≤ m) (hf : UO m f) : UO n f := by
  obtain ⟨C, δ, hC, hδ, hδ1, H⟩ := hf.norm
  refine ⟨C, δ, hδ, fun u h hh => ?_⟩
  have h1 : |h| ≤ 1 := (hh.trans_le hδ1).le
  calc |f u h| ≤ C * |h| ^ m := H u h hh
    _ ≤ C * |h| ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (abs_nonneg h) h1 hnm) hC

lemma UO.zero (n : ℕ) : UO n (fun _ _ => 0) := ⟨0, 1, one_pos, fun u h _ => by simp⟩

lemma UO.add {n : ℕ} {f g : ℝ → ℝ → ℝ} (hf : UO n f) (hg : UO n g) : UO n (fun u h => f u h + g u h) := by
  obtain ⟨C, δ, hC, hδ, _, H⟩ := hf.norm
  obtain ⟨C', δ', hC', hδ', _, H'⟩ := hg.norm
  refine ⟨C + C', min δ δ', lt_min hδ hδ', fun u h hh => ?_⟩
  have a := H u h (lt_of_lt_of_le hh (min_le_left _ _))
  have b := H' u h (lt_of_lt_of_le hh (min_le_right _ _))
  calc |f u h + g u h| ≤ |f u h| + |g u h| := abs_add_le _ _
    _ ≤ C * |h| ^ n + C' * |h| ^ n := add_le_add a b
    _ = (C + C') * |h| ^ n := by ring

lemma UO.neg {n : ℕ} {f : ℝ → ℝ → ℝ} (hf : UO n f) : UO n (fun u h => -f u h) := by
  obtain ⟨C, δ, hδ, H⟩ := hf
  exact ⟨C, δ, hδ, fun u h hh => by simpa using H u h hh⟩

lemma UO.sub {n : ℕ} {f g : ℝ → ℝ → ℝ} (hf : UO n f) (hg : UO n g) : UO n (fun u h => f u h - g u h) := by
  have := hf.add hg.neg
  simpa [sub_eq_add_neg] using this

lemma UO.const_mul {n : ℕ} {f : ℝ → ℝ → ℝ} (c : ℝ) (hf : UO n f) : UO n (fun u h => c * f u h) := by
  obtain ⟨C, δ, hδ, H⟩ := hf
  refine ⟨|c| * C, δ, hδ, fun u h hh => ?_⟩
  calc |c * f u h| = |c| * |f u h| := abs_mul _ _
    _ ≤ |c| * (C * |h| ^ n) := mul_le_mul_of_nonneg_left (H u h hh) (abs_nonneg c)
    _ = |c| * C * |h| ^ n := by ring

lemma UO.mul {n m : ℕ} {f g : ℝ → ℝ → ℝ} (hf : UO n f) (hg : UO m g) :
    UO (n + m) (fun u h => f u h * g u h) := by
  obtain ⟨C, δ, hC, hδ, _, H⟩ := hf.norm
  obtain ⟨C', δ', hC', hδ', _, H'⟩ := hg.norm
  refine ⟨C * C', min δ δ', lt_min hδ hδ', fun u h hh => ?_⟩
  have a := H u h (lt_of_lt_of_le hh (min_le_left _ _))
  have b := H' u h (lt_of_lt_of_le hh (min_le_right _ _))
  calc |f u h * g u h| = |f u h| * |g u h| := abs_mul _ _
    _ ≤ (C * |h| ^ n) * (C' * |h| ^ m) := mul_le_mul a b (abs_nonneg _) (by positivity)
    _ = C * C' * |h| ^ (n + m) := by ring

/-- `UO 0 f`: `f` is uniformly bounded for small `h`. -/
lemma UO.mul_left {n : ℕ} {f g : ℝ → ℝ → ℝ} (hf : UO 0 f) (hg : UO n g) :
    UO n (fun u h => f u h * g u h) := by
  simpa using hf.mul hg

lemma UO.mul_right {n : ℕ} {f g : ℝ → ℝ → ℝ} (hf : UO n f) (hg : UO 0 g) :
    UO n (fun u h => f u h * g u h) := by
  simpa using hf.mul hg

lemma UO.congr {n : ℕ} {f g : ℝ → ℝ → ℝ} (hf : UO n f) (hfg : ∀ u h, f u h = g u h) : UO n g := by
  have : f = g := funext fun u => funext fun h => hfg u h
  rw [← this]; exact hf

lemma UO.sum {ι : Type*} (s : Finset ι) {n : ℕ} {f : ι → ℝ → ℝ → ℝ} (hf : ∀ i ∈ s, UO n (f i)) :
    UO n (fun u h => ∑ i ∈ s, f i u h) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using UO.zero n
  | insert a s ha ih =>
    have h1 := hf a (mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (mem_insert_of_mem hi))
    have := h1.add h2
    refine this.congr fun u h => ?_
    rw [Finset.sum_insert ha]

/-- A function bounded by a constant (independent of `h`) is `UO 0`. -/
lemma UO.of_bdd {f : ℝ → ℝ → ℝ} {C : ℝ} (H : ∀ u h, |f u h| ≤ C) : UO 0 f :=
  ⟨C, 1, one_pos, fun u h _ => by simpa using H u h⟩

/-- The monomial `h^j` is `UO j`. -/
lemma UO.hpow (j : ℕ) : UO j (fun _ h => h ^ j) :=
  ⟨1, 1, one_pos, fun u h _ => by simp [abs_pow]⟩

/-- `h^j * f` is `UO (n+j)` if `f` is `UO n`. -/
lemma UO.hpow_mul {n : ℕ} (j : ℕ) {f : ℝ → ℝ → ℝ} (hf : UO n f) :
    UO (j + n) (fun u h => h ^ j * f u h) := (UO.hpow j).mul hf

/-- If `|a| ≤ C t` for all small `t > 0` then `a = 0`. -/
lemma eq_zero_of_le_mul_small {a C δ : ℝ} (hδ : 0 < δ) (H : ∀ t : ℝ, 0 < t → t < δ → |a| ≤ C * t) : a = 0 := by
  by_contra ha
  have hpos : 0 < |a| := abs_pos.mpr ha
  set t := min (δ / 2) (|a| / (2 * (|C| + 1))) with ht
  have h1 : 0 < t := lt_min (by positivity) (by positivity)
  have h2 : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have h3 := H t h1 h2
  have h4 : t ≤ |a| / (2 * (|C| + 1)) := min_le_right _ _
  have h5 : C * t ≤ |C| * t := mul_le_mul_of_nonneg_right (le_abs_self C) h1.le
  have h6 : |C| * t ≤ |C| * (|a| / (2 * (|C| + 1))) := mul_le_mul_of_nonneg_left h4 (abs_nonneg C)
  have h7 : |C| * (|a| / (2 * (|C| + 1))) < |a| := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg C]
  linarith

/-! ### Polynomial expansions -/

/-- `PApprox N f`: a uniform polynomial expansion of order `N` in `h` (coefficients unspecified, uniformly bounded,
uniformly bounded degree). -/
def PApprox (N : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ (D : ℕ) (C : ℝ) (p : ℝ → Polynomial ℝ), (∀ u, (p u).natDegree ≤ D) ∧ (∀ u n, |(p u).coeff n| ≤ C) ∧
    UO N (fun u h => f u h - (p u).eval h)

lemma eval_abs_le {p : Polynomial ℝ} {D : ℕ} {C : ℝ} (hD : p.natDegree ≤ D) (hC : ∀ n, |p.coeff n| ≤ C)
    {h : ℝ} (hh : |h| ≤ 1) : |p.eval h| ≤ (D + 1) * C := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hD)]
  calc |∑ i ∈ range (D + 1), p.coeff i * h ^ i| ≤ ∑ i ∈ range (D + 1), |p.coeff i * h ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range (D + 1), C := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_pow]
        calc |p.coeff i| * |h| ^ i ≤ C * 1 :=
              mul_le_mul (hC i) (pow_le_one₀ (abs_nonneg h) hh) (by positivity)
                ((abs_nonneg _).trans (hC 0))
          _ = C := mul_one C
    _ = (D + 1) * C := by simp

lemma PApprox.bdd {N : ℕ} {f : ℝ → ℝ → ℝ} (hf : PApprox N f) : UO 0 f := by
  obtain ⟨D, C, p, hD, hC, hr⟩ := hf
  obtain ⟨C', δ, hC', hδ, hδ1, H⟩ := hr.norm
  refine ⟨(D + 1) * C + C', δ, hδ, fun u h hh => ?_⟩
  have h1 : |h| ≤ 1 := (hh.trans_le hδ1).le
  have a := H u h hh
  have b := eval_abs_le (hD u) (hC u) h1
  have c : |h| ^ N ≤ 1 := pow_le_one₀ (abs_nonneg h) h1
  have d : f u h = (f u h - (p u).eval h) + (p u).eval h := by ring
  calc |f u h| = |(f u h - (p u).eval h) + (p u).eval h| := by rw [← d]
    _ ≤ |f u h - (p u).eval h| + |(p u).eval h| := abs_add_le _ _
    _ ≤ C' * |h| ^ N + (D + 1) * C := add_le_add a b
    _ ≤ C' * 1 + (D + 1) * C := by gcongr
    _ = ((D + 1) * C + C') * |h| ^ 0 := by simp; ring

lemma PApprox.mono {N M : ℕ} {f : ℝ → ℝ → ℝ} (hNM : M ≤ N) (hf : PApprox N f) : PApprox M f := by
  obtain ⟨D, C, p, hD, hC, hr⟩ := hf
  exact ⟨D, C, p, hD, hC, hr.mono hNM⟩

lemma PApprox.of_UO {N : ℕ} {f : ℝ → ℝ → ℝ} (hf : UO N f) : PApprox N f := by
  refine ⟨0, 0, fun _ => 0, fun _ => by simp, fun _ _ => by simp, ?_⟩
  simpa using hf

lemma PApprox.congr {N : ℕ} {f g : ℝ → ℝ → ℝ} (hf : PApprox N f) (hfg : ∀ u h, f u h = g u h) : PApprox N g := by
  have : f = g := funext fun u => funext fun h => hfg u h
  rw [← this]; exact hf

lemma PApprox.add {N : ℕ} {f g : ℝ → ℝ → ℝ} (hf : PApprox N f) (hg : PApprox N g) :
    PApprox N (fun u h => f u h + g u h) := by
  obtain ⟨D, C, p, hD, hC, hr⟩ := hf
  obtain ⟨D', C', q, hD', hC', hr'⟩ := hg
  refine ⟨max D D', C + C', fun u => p u + q u, fun u => ?_, fun u n => ?_, ?_⟩
  · exact (natDegree_add_le _ _).trans (max_le_max (hD u) (hD' u))
  · rw [coeff_add]
    exact (abs_add_le _ _).trans (add_le_add (hC u n) (hC' u n))
  · refine (hr.add hr').congr fun u h => ?_
    simp only [eval_add]; ring

lemma PApprox.neg {N : ℕ} {f : ℝ → ℝ → ℝ} (hf : PApprox N f) : PApprox N (fun u h => -f u h) := by
  obtain ⟨D, C, p, hD, hC, hr⟩ := hf
  refine ⟨D, C, fun u => -p u, fun u => ?_, fun u n => ?_, ?_⟩
  · simpa using hD u
  · simpa using hC u n
  · refine hr.neg.congr fun u h => ?_
    simp only [eval_neg]; ring

lemma PApprox.sub {N : ℕ} {f g : ℝ → ℝ → ℝ} (hf : PApprox N f) (hg : PApprox N g) :
    PApprox N (fun u h => f u h - g u h) := by
  have := hf.add hg.neg
  simpa [sub_eq_add_neg] using this

lemma coeff_mul_abs_le {p q : Polynomial ℝ} {D D' : ℕ} {C C' : ℝ} (hD : p.natDegree ≤ D) (hD' : q.natDegree ≤ D')
    (hC : ∀ n, |p.coeff n| ≤ C) (hC' : ∀ n, |q.coeff n| ≤ C') (n : ℕ) :
    |(p * q).coeff n| ≤ (D + D' + 1) * (C * C') := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hC0' : 0 ≤ C' := (abs_nonneg _).trans (hC' 0)
  by_cases hn : n ≤ D + D'
  · rw [coeff_mul]
    calc |∑ x ∈ antidiagonal n, p.coeff x.1 * q.coeff x.2|
        ≤ ∑ x ∈ antidiagonal n, |p.coeff x.1 * q.coeff x.2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ antidiagonal n, C * C' := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hC _) (hC' _) (abs_nonneg _) hC0
      _ = (n + 1) * (C * C') := by simp [Finset.Nat.card_antidiagonal]
      _ ≤ (D + D' + 1) * (C * C') := by
          have : (n : ℝ) + 1 ≤ D + D' + 1 := by exact_mod_cast Nat.succ_le_succ hn
          exact mul_le_mul_of_nonneg_right this (mul_nonneg hC0 hC0')
  · have : (p * q).natDegree < n := by
      have := natDegree_mul_le (p := p) (q := q)
      omega
    rw [coeff_eq_zero_of_natDegree_lt this]
    simp only [abs_zero]
    positivity

lemma PApprox.mul {N : ℕ} {f g : ℝ → ℝ → ℝ} (hf : PApprox N f) (hg : PApprox N g) :
    PApprox N (fun u h => f u h * g u h) := by
  obtain ⟨D, C, p, hD, hC, hr⟩ := hf
  obtain ⟨D', C', q, hD', hC', hr'⟩ := hg
  refine ⟨D + D', (D + D' + 1) * (C * C'), fun u => p u * q u, fun u => ?_, fun u n => ?_, ?_⟩
  · exact (natDegree_mul_le).trans (add_le_add (hD u) (hD' u))
  · exact coeff_mul_abs_le (hD u) (hD' u) (hC u) (hC' u) n
  · -- f g - P Q = (f-P)(g-Q) + (f-P) Q + P (g-Q)
    have hQ : UO 0 (fun u h => (q u).eval h) := by
      obtain ⟨C₀, δ, hC₀, hδ, hδ1, H⟩ := (UO.of_bdd (f := fun _ _ => (0:ℝ)) (C := 0) (fun _ _ => by simp)).norm
      refine ⟨(D' + 1) * C', 1, one_pos, fun u h hh => ?_⟩
      simpa using eval_abs_le (hD' u) (hC' u) hh.le
    have hP : UO 0 (fun u h => (p u).eval h) := by
      refine ⟨(D + 1) * C, 1, one_pos, fun u h hh => ?_⟩
      simpa using eval_abs_le (hD u) (hC u) hh.le
    have t1 : UO N (fun u h => (f u h - (p u).eval h) * (g u h - (q u).eval h)) := by
      have := hr.mul hr'
      have := UO.mono (show N ≤ N + N by omega) this
      exact this
    have t2 : UO N (fun u h => (f u h - (p u).eval h) * (q u).eval h) := by
      simpa using hr.mul hQ
    have t3 : UO N (fun u h => (p u).eval h * (g u h - (q u).eval h)) := by
      simpa using hP.mul hr'
    refine ((t1.add t2).add t3).congr fun u h => ?_
    simp only [eval_mul]; ring

/-- A bounded function of `u` alone (no `h`-dependence). -/
lemma PApprox.of_fun {N : ℕ} (c : ℝ → ℝ) {C : ℝ} (hC : ∀ u, |c u| ≤ C) : PApprox N (fun u _ => c u) := by
  refine ⟨0, C, fun u => Polynomial.C (c u), fun u => by simp, fun u n => ?_, ?_⟩
  · rw [coeff_C]; split_ifs
    · exact hC u
    · simpa using (abs_nonneg _).trans (hC u)
  · refine (UO.zero N).congr fun u h => ?_
    simp

lemma PApprox.const {N : ℕ} (c : ℝ) : PApprox N (fun _ _ => c) :=
  PApprox.of_fun (fun _ => c) (C := |c|) (fun _ => le_rfl)

/-- The monomial `h^j`. -/
lemma PApprox.hpow {N : ℕ} (j : ℕ) : PApprox N (fun _ h => h ^ j) := by
  refine ⟨j, 1, fun _ => X ^ j, fun _ => by simp, fun _ n => ?_, ?_⟩
  · rw [coeff_X_pow]; split_ifs <;> simp
  · refine (UO.zero N).congr fun u h => ?_
    simp

lemma PApprox.hpow_mul {N : ℕ} (j : ℕ) {f : ℝ → ℝ → ℝ} (hf : PApprox N f) :
    PApprox N (fun u h => h ^ j * f u h) := (PApprox.hpow j).mul hf

lemma PApprox.sum {ι : Type*} (s : Finset ι) {N : ℕ} {f : ι → ℝ → ℝ → ℝ} (hf : ∀ i ∈ s, PApprox N (f i)) :
    PApprox N (fun u h => ∑ i ∈ s, f i u h) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PApprox.const (N := N) 0
  | insert a s ha ih =>
    have h1 := hf a (mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (mem_insert_of_mem hi))
    refine (h1.add h2).congr fun u h => ?_
    rw [Finset.sum_insert ha]

/-- Build `PApprox` from explicit bounded coefficients `a n` (`n < D`). -/
lemma PApprox.of_coeffs {N : ℕ} {f : ℝ → ℝ → ℝ} (D : ℕ) (a : ℕ → ℝ → ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ n < D, ∀ u, |a n u| ≤ C)
    (hr : UO N (fun u h => f u h - ∑ n ∈ range D, a n u * h ^ n)) : PApprox N f := by
  refine ⟨D, C, fun u => ∑ n ∈ range D, Polynomial.C (a n u) * X ^ n, fun u => ?_, fun u m => ?_, ?_⟩
  · refine (natDegree_sum_le_of_forall_le _ _ (n := D) fun n hn => ?_).trans (by simp)
    refine (natDegree_C_mul_X_pow_le _ _).trans ?_
    exact (Finset.mem_range.mp hn).le
  · rw [finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    split_ifs with h1
    · exact hC m (Finset.mem_range.mp h1) u
    · simpa using hC0
  · refine hr.congr fun u h => ?_
    simp [eval_finsetSum]

/-! ### Uniqueness of coefficients, peeling and the parity lift -/

/-- A polynomial that is `O(|h|^n)` near `0` (at `h ≠ 0`) has vanishing coefficients below `n`. -/
lemma poly_vanish {n : ℕ} : ∀ (p : Polynomial ℝ) (C δ : ℝ), 0 < δ →
    (∀ h : ℝ, 0 < |h| → |h| < δ → |p.eval h| ≤ C * |h| ^ n) → ∀ j < n, p.coeff j = 0 := by
  induction n with
  | zero => intro p C δ _ _ j hj; omega
  | succ n ih =>
    intro p C δ hδ H j hj
    -- coefficient 0
    have h0 : p.coeff 0 = 0 := by
      have e : p.coeff 0 = p.eval 0 := by simp [Polynomial.coeff_zero_eq_eval_zero]
      have h1 : Filter.Tendsto (fun h : ℝ => |p.eval h|) (nhdsWithin 0 {0}ᶜ) (nhds |p.eval 0|) :=
        (((p.continuous.abs).tendsto 0)).mono_left nhdsWithin_le_nhds
      have h2 : Filter.Tendsto (fun h : ℝ => C * |h| ^ (n + 1)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
        have : Filter.Tendsto (fun h : ℝ => C * |h| ^ (n + 1)) (nhds 0) (nhds (C * |(0:ℝ)| ^ (n + 1))) :=
          ((continuous_const.mul ((continuous_abs).pow (n + 1))).tendsto 0)
        simpa using this.mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ h : ℝ in nhdsWithin 0 {0}ᶜ, |p.eval h| ≤ C * |h| ^ (n + 1) := by
        have hb : Metric.ball (0:ℝ) δ ∈ nhds (0:ℝ) := Metric.ball_mem_nhds 0 hδ
        have hb' : Metric.ball (0:ℝ) δ ∈ nhdsWithin (0:ℝ) {0}ᶜ := mem_nhdsWithin_of_mem_nhds hb
        filter_upwards [hb', self_mem_nhdsWithin] with h hh hne
        have hne' : h ≠ 0 := hne
        exact H h (abs_pos.mpr hne') (by simpa [Metric.mem_ball, dist_zero_right] using hh)
      have := le_of_tendsto_of_tendsto h1 h2 hev
      have h3 : |p.eval 0| = 0 := le_antisymm this (abs_nonneg _)
      rw [e]; exact abs_eq_zero.mp h3
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact h0
    · obtain ⟨q, hq⟩ : X ∣ p := Polynomial.X_dvd_iff.mpr h0
      have hq' : ∀ h : ℝ, 0 < |h| → |h| < δ → |q.eval h| ≤ C * |h| ^ n := by
        intro h hpos hlt
        have := H h hpos hlt
        rw [hq] at this
        simp only [eval_mul, eval_X, abs_mul] at this
        have hh : 0 < |h| := hpos
        rw [pow_succ] at this
        nlinarith [this, hh]
      have := ih q C δ hδ hq' (j - 1) (by omega)
      rw [hq]
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simpa [coeff_X_mul] using this

lemma eval_sub_coeff_abs_le {q : Polynomial ℝ} {D : ℕ} {C : ℝ} (hD : q.natDegree ≤ D) (hC : ∀ n, |q.coeff n| ≤ C)
    {h : ℝ} (hh : |h| ≤ 1) : |q.eval h - q.coeff 0| ≤ (D + 1) * C * |h| := by
  have e : q.eval h = h * q.divX.eval h + q.coeff 0 := by
    have := congrArg (Polynomial.eval h) (Polynomial.divX_mul_X_add q)
    simp only [eval_add, eval_mul, eval_X, eval_C] at this
    linarith
  have hdiv : q.divX.natDegree ≤ D := (Polynomial.natDegree_divX_le).trans hD
  have hc : ∀ n, |q.divX.coeff n| ≤ C := fun n => by rw [Polynomial.coeff_divX]; exact hC _
  have := eval_abs_le hdiv hc hh
  calc |q.eval h - q.coeff 0| = |h * q.divX.eval h| := by rw [e]; ring_nf
    _ = |h| * |q.divX.eval h| := abs_mul _ _
    _ ≤ |h| * ((D + 1) * C) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = (D + 1) * C * |h| := by ring

/-- **Peeling.** If `f` has a `PApprox (n+1)` expansion and `f = O(h^n)`, then `f - h^n a = O(h^{n+1})` for a bounded
function `a` (the order-`n` coefficient). -/
lemma PApprox.peel {n : ℕ} {f : ℝ → ℝ → ℝ} (hf : PApprox (n + 1) f) (h0 : UO n f) :
    ∃ a : ℝ → ℝ, (∃ C, ∀ u, |a u| ≤ C) ∧ UO (n + 1) (fun u h => f u h - h ^ n * a u) := by
  obtain ⟨D, C, p, hD, hC, hr⟩ := hf
  obtain ⟨C1, δ1, hC1, hδ1, hδ11, H1⟩ := hr.norm
  obtain ⟨C2, δ2, hC2, hδ2, hδ21, H2⟩ := h0.norm
  -- the polynomial is O(h^n)
  have hvan : ∀ u, ∀ j < n, (p u).coeff j = 0 := by
    intro u
    refine poly_vanish (p u) (C1 + C2) (min δ1 δ2) (lt_min hδ1 hδ2) ?_
    intro h hpos hlt
    have hh1 : |h| < δ1 := lt_of_lt_of_le hlt (min_le_left _ _)
    have hh2 : |h| < δ2 := lt_of_lt_of_le hlt (min_le_right _ _)
    have hle1 : |h| ≤ 1 := (hh1.trans_le hδ11).le
    have a1 := H1 u h hh1
    have a2 := H2 u h hh2
    have hpow : |h| ^ (n + 1) ≤ |h| ^ n := pow_le_pow_of_le_one (abs_nonneg h) hle1 (Nat.le_succ n)
    have : (p u).eval h = f u h - (f u h - (p u).eval h) := by ring
    calc |(p u).eval h| = |f u h - (f u h - (p u).eval h)| := by rw [← this]
      _ ≤ |f u h| + |f u h - (p u).eval h| := abs_sub _ _
      _ ≤ C2 * |h| ^ n + C1 * |h| ^ (n + 1) := add_le_add a2 a1
      _ ≤ C2 * |h| ^ n + C1 * |h| ^ n := by gcongr
      _ = (C1 + C2) * |h| ^ n := by ring
  -- factor p u = X^n * q u
  have hdvd : ∀ u, ∃ q : Polynomial ℝ, p u = X ^ n * q := fun u =>
    (Polynomial.X_pow_dvd_iff.mpr (hvan u))
  choose q hq using hdvd
  have hqD : ∀ u, (q u).natDegree ≤ D := by
    intro u
    by_cases hz : q u = 0
    · simp [hz]
    · have h1 := hD u
      rw [hq u, natDegree_X_pow_mul n hz] at h1
      omega
  have hqC : ∀ u m, |(q u).coeff m| ≤ C := by
    intro u m
    have := hC u (m + n)
    rwa [hq u, coeff_X_pow_mul] at this
  refine ⟨fun u => (q u).coeff 0, ⟨C, fun u => hqC u 0⟩, ?_⟩
  refine ⟨C1 + (D + 1) * C, min δ1 1, lt_min hδ1 one_pos, fun u h hh => ?_⟩
  have hh1 : |h| < δ1 := lt_of_lt_of_le hh (min_le_left _ _)
  have hle1 : |h| ≤ 1 := (lt_of_lt_of_le hh (min_le_right _ _)).le
  have a1 := H1 u h hh1
  have a2 := eval_sub_coeff_abs_le (hqD u) (hqC u) hle1
  have e : f u h - h ^ n * (q u).coeff 0 =
      (f u h - (p u).eval h) + h ^ n * ((q u).eval h - (q u).coeff 0) := by
    rw [hq u]; simp only [eval_mul, eval_pow, eval_X]; ring
  have hn0 : 0 ≤ |h| ^ n := by positivity
  calc |f u h - h ^ n * (q u).coeff 0|
      = |(f u h - (p u).eval h) + h ^ n * ((q u).eval h - (q u).coeff 0)| := by rw [e]
    _ ≤ |f u h - (p u).eval h| + |h ^ n * ((q u).eval h - (q u).coeff 0)| := abs_add_le _ _
    _ ≤ C1 * |h| ^ (n + 1) + |h| ^ n * ((D + 1) * C * |h|) := by
        refine add_le_add (by simpa using a1) ?_
        rw [abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_left a2 hn0
    _ = (C1 + (D + 1) * C) * |h| ^ (n + 1) := by ring

/-- **Parity lift.** If `f` has a `PApprox (n+1)` expansion, `f = O(h^n)` and `f(u,-h) = σ f(u,h)` with
`σ (-1)^n = -1`, then `f = O(h^{n+1})`.  (`σ = 1`, `n` odd: an even function vanishing to odd order `n` vanishes to
order `n+1`; `σ = -1`, `n` even: the same for an odd function.) -/
lemma PApprox.lift {n : ℕ} {σ δ0 : ℝ} (hσ : σ * (-1) ^ n = -1) {f : ℝ → ℝ → ℝ} (hf : PApprox (n + 1) f)
    (h0 : UO n f) (hδ0 : 0 < δ0) (hpar : ∀ u h, |h| < δ0 → f u (-h) = σ * f u h) : UO (n + 1) f := by
  obtain ⟨a, ⟨Ca, hCa⟩, hr⟩ := hf.peel h0
  obtain ⟨C1, δ1, hC1, hδ1, hδ11, H1⟩ := hr.norm
  have hσ2 : σ ^ 2 = 1 := by
    have : (σ * (-1) ^ n) ^ 2 = 1 := by rw [hσ]; norm_num
    have h2 : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    nlinarith [this, h2, sq_nonneg σ]
  have hneg : (-1 : ℝ) ^ n = -σ := by
    calc (-1 : ℝ) ^ n = σ ^ 2 * (-1) ^ n := by rw [hσ2, one_mul]
      _ = σ * (σ * (-1) ^ n) := by ring
      _ = -σ := by rw [hσ]; ring
  have hzero : ∀ u, a u = 0 := by
    intro u
    refine eq_zero_of_le_mul_small (C := C1) (δ := min δ1 δ0) (lt_min hδ1 hδ0) fun t ht htδ => ?_
    have htδ1 : t < δ1 := lt_of_lt_of_le htδ (min_le_left _ _)
    have htδ0 : t < δ0 := lt_of_lt_of_le htδ (min_le_right _ _)
    have a1 := H1 u t (by rw [abs_of_pos ht]; exact htδ1)
    have a2 := H1 u (-t) (by rw [abs_neg, abs_of_pos ht]; exact htδ1)
    rw [abs_neg, abs_of_pos ht] at a2
    rw [abs_of_pos ht] at a1
    have key : (f u (-t) - (-t) ^ n * a u) = σ * (f u t - t ^ n * a u) + 2 * σ * t ^ n * a u := by
      rw [hpar u t (by rw [abs_of_pos ht]; exact htδ0)]
      have : (-t) ^ n = (-1) ^ n * t ^ n := by rw [neg_eq_neg_one_mul, mul_pow]
      rw [this, hneg]; ring
    have h1 : |2 * σ * t ^ n * a u| ≤ 2 * C1 * t ^ (n + 1) := by
      have e : 2 * σ * t ^ n * a u = (f u (-t) - (-t) ^ n * a u) - σ * (f u t - t ^ n * a u) := by
        rw [key]; ring
      rw [e]
      have hσabs : |σ| = 1 := by
        have : |σ| ^ 2 = 1 := by rw [sq_abs]; exact hσ2
        nlinarith [abs_nonneg σ]
      calc |(f u (-t) - (-t) ^ n * a u) - σ * (f u t - t ^ n * a u)|
          ≤ |f u (-t) - (-t) ^ n * a u| + |σ * (f u t - t ^ n * a u)| := abs_sub _ _
        _ = |f u (-t) - (-t) ^ n * a u| + |f u t - t ^ n * a u| := by rw [abs_mul, hσabs, one_mul]
        _ ≤ C1 * t ^ (n + 1) + C1 * t ^ (n + 1) := add_le_add (by simpa using a2) (by simpa using a1)
        _ = 2 * C1 * t ^ (n + 1) := by ring
    have hσabs : |σ| = 1 := by
      have : |σ| ^ 2 = 1 := by rw [sq_abs]; exact hσ2
      nlinarith [abs_nonneg σ]
    have h2 : |2 * σ * t ^ n * a u| = 2 * t ^ n * |a u| := by
      rw [abs_mul, abs_mul, abs_mul, hσabs, abs_pow, abs_of_pos ht]; norm_num
    rw [h2] at h1
    have htn : 0 < t ^ n := pow_pos ht n
    have : t ^ n * (2 * |a u|) ≤ t ^ n * (2 * C1 * t) := by
      calc t ^ n * (2 * |a u|) = 2 * t ^ n * |a u| := by ring
        _ ≤ 2 * C1 * t ^ (n + 1) := h1
        _ = t ^ n * (2 * C1 * t) := by ring
    have := le_of_mul_le_mul_left this htn
    linarith
  refine hr.congr fun u h => ?_
  simp [hzero u]

/-- **Existence of the order-`n` coefficient.** If `f` has a `PApprox (n+2)` expansion, `f = O(h^n)` and
`f(u,-h) = σ f(u,h)` with `σ (-1)^n = +1`, then `f = h^n a + O(h^{n+2})` for a bounded `a`. -/
lemma PApprox.exists_coeff {n : ℕ} {σ δ0 : ℝ} (hσ : σ * (-1) ^ n = 1) {f : ℝ → ℝ → ℝ} (hf : PApprox (n + 2) f)
    (h0 : UO n f) (hδ0 : 0 < δ0) (hpar : ∀ u h, |h| < δ0 → f u (-h) = σ * f u h) :
    ∃ a : ℝ → ℝ, (∃ C, ∀ u, |a u| ≤ C) ∧ UO (n + 2) (fun u h => f u h - h ^ n * a u) := by
  obtain ⟨a, ⟨Ca, hCa⟩, hr⟩ := (hf.mono (Nat.le_succ (n + 1))).peel h0
  refine ⟨a, ⟨Ca, hCa⟩, ?_⟩
  have hσ2 : σ ^ 2 = 1 := by
    have : (σ * (-1) ^ n) ^ 2 = 1 := by rw [hσ]; norm_num
    have h2 : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    nlinarith [this, h2, sq_nonneg σ]
  have hneg : (-1 : ℝ) ^ n = σ := by
    calc (-1 : ℝ) ^ n = σ ^ 2 * (-1) ^ n := by rw [hσ2, one_mul]
      _ = σ * (σ * (-1) ^ n) := by ring
      _ = σ := by rw [hσ]; ring
  have h1 : PApprox (n + 2) (fun u h => f u h - h ^ n * a u) :=
    hf.sub ((PApprox.hpow_mul n (PApprox.of_fun a hCa)).congr fun u h => rfl)
  refine PApprox.lift (n := n + 1) (σ := σ) (δ0 := δ0) ?_ h1 hr hδ0 ?_
  · rw [pow_succ]; nlinarith [hσ]
  · intro u h hh
    simp only [hpar u h hh]
    have : (-h) ^ n = (-1) ^ n * h ^ n := by rw [neg_eq_neg_one_mul, mul_pow]
    rw [this, hneg]; ring

/-! ### Bounded smooth functions and Taylor expansions -/

/-- `BSmooth N g`: `g : ℝ → ℝ` is `N` times differentiable and `g, g', …, g^{(N)}` are bounded on `ℝ`
(defined recursively through `deriv`). -/
def BSmooth : ℕ → (ℝ → ℝ) → Prop
  | 0, g => ∃ C, ∀ x, |g x| ≤ C
  | N + 1, g => (∃ C, ∀ x, |g x| ≤ C) ∧ Differentiable ℝ g ∧ BSmooth N (deriv g)

lemma BSmooth.bdd : ∀ {N : ℕ} {g : ℝ → ℝ}, BSmooth N g → ∃ C, ∀ x, |g x| ≤ C
  | 0, _, h => h
  | _ + 1, _, h => h.1

lemma BSmooth.d {N : ℕ} {g : ℝ → ℝ} (h : BSmooth (N + 1) g) : BSmooth N (deriv g) := h.2.2

lemma BSmooth.diff {N : ℕ} {g : ℝ → ℝ} (h : BSmooth (N + 1) g) : Differentiable ℝ g := h.2.1

lemma BSmooth.mono : ∀ {N M : ℕ} {g : ℝ → ℝ}, M ≤ N → BSmooth N g → BSmooth M g
  | N, 0, g, _, h => h.bdd
  | 0, M + 1, g, hM, _ => absurd hM (by omega)
  | N + 1, M + 1, g, hM, h => ⟨h.1, h.2.1, BSmooth.mono (by omega) h.2.2⟩

lemma BSmooth.iter_bdd : ∀ {N : ℕ} {g : ℝ → ℝ}, BSmooth N g →
    ∃ C, 0 ≤ C ∧ ∀ n ≤ N, ∀ x, |deriv^[n] g x| ≤ C
  | 0, g, h => by
      obtain ⟨C, hC⟩ := h
      refine ⟨|C|, abs_nonneg _, fun n hn x => ?_⟩
      have : n = 0 := by omega
      subst this
      exact (hC x).trans (le_abs_self C)
  | N + 1, g, h => by
      obtain ⟨C0, hC0⟩ := h.bdd
      obtain ⟨C1, hC1, H1⟩ := BSmooth.iter_bdd h.d
      refine ⟨max |C0| C1, le_max_of_le_left (abs_nonneg _), fun n hn x => ?_⟩
      rcases n with _ | n
      · exact ((hC0 x).trans (le_abs_self C0)).trans (le_max_left _ _)
      · rw [Function.iterate_succ_apply]
        exact (H1 n (by omega) _).trans (le_max_right _ _)

/-- The Taylor polynomial of `g` at `u`, order `N`, evaluated at the increment `t`. -/
noncomputable def tay (g : ℝ → ℝ) (N : ℕ) (u t : ℝ) : ℝ := ∑ n ∈ range N, deriv^[n] g u / (n.factorial : ℝ) * t ^ n

lemma tay_hasDerivAt (g : ℝ → ℝ) (N : ℕ) (u s : ℝ) :
    HasDerivAt (fun s => tay g (N + 1) u s) (tay (deriv g) N u s) s := by
  unfold tay
  have h : ∀ n ∈ range (N + 1), HasDerivAt (fun s : ℝ => deriv^[n] g u / (n.factorial : ℝ) * s ^ n)
      (deriv^[n] g u / (n.factorial : ℝ) * ((n : ℝ) * s ^ (n - 1))) s :=
    fun n _ => (hasDerivAt_pow n s).const_mul _
  have h2 := HasDerivAt.fun_sum h
  convert h2 using 1
  rw [Finset.sum_range_succ']
  have z : deriv^[0] g u / ((Nat.factorial 0 : ℕ) : ℝ) * (((0 : ℕ) : ℝ) * s ^ (0 - 1)) = 0 := by simp
  rw [z, add_zero]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Function.iterate_succ_apply, Nat.factorial_succ]
  push_cast
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Taylor's formula with a uniform remainder** for `BSmooth N` functions. -/
lemma BSmooth.taylor : ∀ {N : ℕ} {g : ℝ → ℝ}, BSmooth N g →
    ∃ C, 0 ≤ C ∧ ∀ u t, |g (u + t) - tay g N u t| ≤ C * |t| ^ N
  | 0, g, h => by
      obtain ⟨C, hC⟩ := h
      refine ⟨|C|, abs_nonneg _, fun u t => ?_⟩
      simpa [tay] using (hC (u + t)).trans (le_abs_self C)
  | N + 1, g, h => by
      obtain ⟨C, hC0, hC⟩ := BSmooth.taylor h.d
      refine ⟨C, hC0, fun u t => ?_⟩
      have hd := h.diff
      set ψ : ℝ → ℝ := fun s => g (u + s) - tay g (N + 1) u s with hψ
      have hψd : ∀ s, HasDerivAt ψ (deriv g (u + s) - tay (deriv g) N u s) s := by
        intro s
        have h1 : HasDerivAt (fun s => g (u + s)) (deriv g (u + s)) s :=
          (hd (u + s)).hasDerivAt.comp_const_add u s
        exact h1.sub (tay_hasDerivAt g N u s)
      have hbound : ∀ s ∈ Metric.closedBall (0 : ℝ) |t|, ‖deriv ψ s‖ ≤ C * |t| ^ N := by
        intro s hs
        rw [(hψd s).deriv, Real.norm_eq_abs]
        have hs' : |s| ≤ |t| := by simpa [Metric.mem_closedBall, dist_zero_right] using hs
        calc |deriv g (u + s) - tay (deriv g) N u s| ≤ C * |s| ^ N := hC u s
          _ ≤ C * |t| ^ N := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hs' N) hC0
      have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := ψ) (s := Metric.closedBall (0 : ℝ) |t|)
        (fun s _ => (hψd s).differentiableAt) hbound (convex_closedBall _ _)
        (Metric.mem_closedBall_self (abs_nonneg t))
        (show t ∈ Metric.closedBall (0 : ℝ) |t| by simp [Metric.mem_closedBall, dist_zero_right])
      have h0 : ψ 0 = 0 := by
        simp [hψ, tay, Finset.sum_range_succ', zero_pow]
      simp only [Real.norm_eq_abs, h0, sub_zero, sub_zero] at hmv
      calc |g (u + t) - tay g (N + 1) u t| = |ψ t| := rfl
        _ ≤ C * |t| ^ N * |t| := hmv
        _ = C * |t| ^ (N + 1) := by ring

/-- First-order Taylor bound: `|g(u+t) - g(u) - t g'(u)| ≤ C t²` for `BSmooth 2` functions. -/
lemma BSmooth.order1 {g : ℝ → ℝ} (hg : BSmooth 2 g) :
    ∃ C, 0 ≤ C ∧ ∀ u t, |g (u + t) - g u - t * deriv g u| ≤ C * t ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := hg.taylor
  refine ⟨C, hC0, fun u t => ?_⟩
  have := hC u t
  have e : tay g 2 u t = g u + t * deriv g u := by
    simp [tay, Finset.sum_range_succ]
    ring
  rw [e, sq_abs] at this
  have e2 : g (u + t) - g u - t * deriv g u = g (u + t) - (g u + t * deriv g u) := by ring
  rw [e2]; simpa [sq_abs] using this

/-- **Shifts have polynomial expansions.** `h ↦ g(u + c h)` has a `PApprox N` expansion for `g` in `BSmooth N`. -/
lemma BSmooth.papprox_shift {N : ℕ} {g : ℝ → ℝ} (hg : BSmooth N g) (c : ℝ) :
    PApprox N (fun u h => g (u + c * h)) := by
  obtain ⟨Cd, hCd0, hCd⟩ := hg.iter_bdd
  obtain ⟨Ct, hCt0, hCt⟩ := hg.taylor
  refine PApprox.of_coeffs (C := (1 + |c|) ^ N * Cd) N (fun n u => c ^ n * (deriv^[n] g u / (n.factorial : ℝ)))
    (by positivity) (fun n hn u => ?_) ⟨Ct * |c| ^ N, 1, one_pos, fun u h _ => ?_⟩
  · have h1 := hCd n hn.le u
    have hf : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
    have h2 : |deriv^[n] g u / (n.factorial : ℝ)| ≤ Cd := by
      rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < n.factorial)]
      calc |deriv^[n] g u| / n.factorial ≤ |deriv^[n] g u| / 1 :=
            div_le_div_of_nonneg_left (abs_nonneg _) one_pos hf
        _ ≤ Cd := by simpa using h1
    have h3 : |c| ^ n ≤ (1 + |c|) ^ N := by
      calc |c| ^ n ≤ (1 + |c|) ^ n := pow_le_pow_left₀ (abs_nonneg _) (by linarith) n
        _ ≤ (1 + |c|) ^ N := pow_le_pow_right₀ (by linarith [abs_nonneg c]) hn.le
    rw [abs_mul, abs_pow]
    exact mul_le_mul h3 h2 (abs_nonneg _) (by positivity)
  · have := hCt u (c * h)
    have e : ∑ n ∈ range N, c ^ n * (deriv^[n] g u / (n.factorial : ℝ)) * h ^ n = tay g N u (c * h) := by
      unfold tay
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [mul_pow]; ring
    show |g (u + c * h) - ∑ n ∈ range N, c ^ n * (deriv^[n] g u / (n.factorial : ℝ)) * h ^ n| ≤ _
    rw [e]
    calc |g (u + c * h) - tay g N u (c * h)| ≤ Ct * |c * h| ^ N := this
      _ = Ct * |c| ^ N * |h| ^ N := by rw [abs_mul, mul_pow]; ring

/-! ### Further order calculus -/

/-- Order one: `f - f(·,0) = O(h)` for `f` with a `PApprox 1` expansion. -/
lemma PApprox.order1 {f : ℝ → ℝ → ℝ} (hf : PApprox 1 f) : UO 1 (fun u h => f u h - f u 0) := by
  obtain ⟨D, C, p, hD, hC, hr⟩ := hf
  obtain ⟨C1, δ1, hC1, hδ1, hδ11, H1⟩ := hr.norm
  refine ⟨C1 + (D + 1) * C, δ1, hδ1, fun u h hh => ?_⟩
  have hle1 : |h| ≤ 1 := (hh.trans_le hδ11).le
  have a1 := H1 u h hh
  have a0 : f u 0 = (p u).coeff 0 := by
    have := H1 u 0 (by simpa using hδ1)
    simp at this
    rw [Polynomial.coeff_zero_eq_eval_zero]
    linarith
  have a2 := eval_sub_coeff_abs_le (hD u) (hC u) hle1
  have e : f u h - f u 0 = (f u h - (p u).eval h) + ((p u).eval h - (p u).coeff 0) := by
    rw [a0]; ring
  calc |f u h - f u 0| = |(f u h - (p u).eval h) + ((p u).eval h - (p u).coeff 0)| := by rw [e]
    _ ≤ |f u h - (p u).eval h| + |(p u).eval h - (p u).coeff 0| := abs_add_le _ _
    _ ≤ C1 * |h| ^ 1 + (D + 1) * C * |h| := add_le_add a1 a2
    _ = (C1 + (D + 1) * C) * |h| ^ 1 := by ring

/-- Composition with the shift `u ↦ u + c h` preserves `UO` (the bound is uniform in `u`). -/
lemma UO.shift {n : ℕ} {f : ℝ → ℝ → ℝ} (hf : UO n f) (c : ℝ) : UO n (fun u h => f (u + c * h) h) := by
  obtain ⟨C, δ, hδ, H⟩ := hf
  exact ⟨C, δ, hδ, fun u h hh => H _ _ hh⟩

/-- A function that is `O(h^n)` for `h ≠ 0` and vanishes at `h = 0` is `UO n` (`n ≥ 1`). -/
lemma UO.of_punct {n : ℕ} (hn : 1 ≤ n) {f : ℝ → ℝ → ℝ} {C δ : ℝ} (hδ : 0 < δ)
    (H : ∀ u h : ℝ, 0 < |h| → |h| < δ → |f u h| ≤ C * |h| ^ n) (h0 : ∀ u, f u 0 = 0) : UO n f := by
  refine ⟨C, δ, hδ, fun u h hh => ?_⟩
  by_cases hz : h = 0
  · subst hz; simp [h0 u, zero_pow (by omega : n ≠ 0)]
  · exact H u h (abs_pos.mpr hz) hh

/-- Division by a uniformly nonvanishing factor. -/
lemma UO.div_of_lower {n : ℕ} {A f : ℝ → ℝ → ℝ} (hA : ∃ m δ : ℝ, 0 < m ∧ 0 < δ ∧ ∀ u h, |h| < δ → m ≤ |A u h|)
    (hf : UO n (fun u h => A u h * f u h)) : UO n f := by
  obtain ⟨m, δ, hm, hδ, hAm⟩ := hA
  obtain ⟨C, δ', hC, hδ', _, H⟩ := hf.norm
  refine ⟨C / m, min δ δ', lt_min hδ hδ', fun u h hh => ?_⟩
  have h1 := hAm u h (lt_of_lt_of_le hh (min_le_left _ _))
  have h2 := H u h (lt_of_lt_of_le hh (min_le_right _ _))
  rw [abs_mul] at h2
  have : m * |f u h| ≤ C * |h| ^ n :=
    calc m * |f u h| ≤ |A u h| * |f u h| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ _ := h2
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]
  linarith

/-- `UO` is insensitive to changing a function for large `|h|`. -/
lemma UO.congr_loc {n : ℕ} {f g : ℝ → ℝ → ℝ} (hf : UO n f) {δ0 : ℝ} (hδ0 : 0 < δ0)
    (hfg : ∀ u h, |h| < δ0 → f u h = g u h) : UO n g := by
  obtain ⟨C, δ, hδ, H⟩ := hf
  refine ⟨C, min δ δ0, lt_min hδ hδ0, fun u h hh => ?_⟩
  rw [← hfg u h (lt_of_lt_of_le hh (min_le_right _ _))]
  exact H u h (lt_of_lt_of_le hh (min_le_left _ _))

lemma PApprox.congr_loc {N : ℕ} {f g : ℝ → ℝ → ℝ} (hf : PApprox N f) {δ0 : ℝ} (hδ0 : 0 < δ0)
    (hfg : ∀ u h, |h| < δ0 → f u h = g u h) : PApprox N g := by
  obtain ⟨D, C, p, hD, hC, hr⟩ := hf
  exact ⟨D, C, p, hD, hC, hr.congr_loc hδ0 fun u h hh => by rw [hfg u h hh]⟩

/-- `UO` for a sum of a bounded-coefficient monomial family is used through `PApprox.bdd`; this packages the
frequent step "`PApprox` function is bounded". -/
lemma PApprox.bdd' {N : ℕ} {f : ℝ → ℝ → ℝ} (hf : PApprox N f) : ∃ C δ : ℝ, 0 < δ ∧ ∀ u h, |h| < δ → |f u h| ≤ C := by
  obtain ⟨C, δ, hδ, H⟩ := hf.bdd
  exact ⟨C, δ, hδ, fun u h hh => by simpa using H u h hh⟩

lemma BSmooth.papprox_shift' {N : ℕ} {g : ℝ → ℝ} (hg : BSmooth N g) (c : ℝ) {σ : ℝ → ℝ → ℝ}
    (hσ : ∀ u h, σ u h = u + c * h) : PApprox N (fun u h => g (σ u h)) :=
  (hg.papprox_shift c).congr fun u h => by rw [hσ]

/-- `h ↦ g(u + c h) - g(u) - c h g'(u)` is `O(h²)`, uniformly in `u`. -/
lemma BSmooth.uo_shift_order1 {g : ℝ → ℝ} (hg : BSmooth 2 g) (c : ℝ) {σ : ℝ → ℝ → ℝ}
    (hσ : ∀ u h, σ u h = u + c * h) :
    UO 2 (fun u h => g (σ u h) - g u - (c * h) * deriv g u) := by
  obtain ⟨C, hC0, hC⟩ := hg.order1
  refine ⟨C * c ^ 2, 1, one_pos, fun u h _ => ?_⟩
  show |g (σ u h) - g u - c * h * deriv g u| ≤ _
  rw [hσ]
  calc |g (u + c * h) - g u - c * h * deriv g u| ≤ C * (c * h) ^ 2 := hC u (c * h)
    _ = C * c ^ 2 * |h| ^ 2 := by rw [mul_pow, ← sq_abs h]; ring

lemma PApprox.of_bdd_fun {N : ℕ} {c : ℝ → ℝ} (hc : ∃ C, ∀ x, |c x| ≤ C) : PApprox N (fun u _ => c u) := by
  obtain ⟨C, hC⟩ := hc
  exact PApprox.of_fun c hC

lemma UO0_of_fun {c : ℝ → ℝ} (hc : ∃ C, ∀ x, |c x| ≤ C) : UO 0 (fun u _ => c u) := by
  obtain ⟨C, hC⟩ := hc
  exact UO.of_bdd (fun u h => hC u)

-- Axiom pins for the headline statements (checked at build time).
/-- info: 'FormalResearch.JacobiEigenvectors.Engine.poly_vanish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.poly_vanish

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.PApprox.peel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.PApprox.peel

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.PApprox.lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.PApprox.lift

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.PApprox.exists_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.PApprox.exists_coeff

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.BSmooth.taylor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.BSmooth.taylor

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.BSmooth.papprox_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.BSmooth.papprox_shift

/-- info: 'FormalResearch.JacobiEigenvectors.Engine.PApprox.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Engine.PApprox.mul


end FormalResearch.JacobiEigenvectors.Engine

end
