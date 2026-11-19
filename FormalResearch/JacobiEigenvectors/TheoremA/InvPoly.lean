module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.InvBounded
public import FormalResearch.JacobiEigenvectors.TheoremA.InvAlg

/-!
# Paper J, Layer 2: bounded-derivative polynomial-valued functions (L2.E, support for `InvCoeffs`)

Source: Paper J `thmA.tex`, proof of `cor:eigen` (b)(iii).

## Proved here

`PB I m C N p`: the coefficients of degree `<= N` of the polynomial-valued function `p` are `BD I m C`.  Closure under sums, products (`PB.mul_exists`), powers, `X^j *`, constants `C(f)`,
and `PB.Qp_exists`: for `BD` data `c_{jk}`, `a_r` the coefficient functions of `Qp M (c y) K0 (Dp M (a y))` are `BD` with a constant depending on `(M, m, K0, N, C_1, C_2)` only.

## Differences from the paper

The paper's `C^{M+1-r}` bounds are by compactness; here they are explicit.

## Not formalised

Nothing.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA.InvBD

open Set Polynomial Finset

variable {I : Set ℝ}

lemma BD.nonneg (hI : I.Nonempty) {m : ℕ} {C : ℝ} {g : ℝ → ℝ} (h : BD I m C g) : 0 ≤ C := by
  obtain ⟨y, hy⟩ := hI
  exact (abs_nonneg _).trans (h.bound y hy)

lemma BD.finset_sum {ι : Type*} (s : Finset ι) (m : ℕ) (C : ι → ℝ) (f : ι → ℝ → ℝ) (h : ∀ i ∈ s, BD I m (C i) (f i)) :
    BD I m (∑ i ∈ s, C i) (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (BD.const (I := I) m 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Polynomial-valued functions whose coefficients up to degree `N` are `BD`. -/
def PB (I : Set ℝ) (m : ℕ) (C : ℝ) (N : ℕ) (p : ℝ → ℝ[X]) : Prop := ∀ n ≤ N, BD I m C (fun y => (p y).coeff n)

lemma PB.add {m : ℕ} {C1 C2 : ℝ} {N : ℕ} {p q : ℝ → ℝ[X]} (hp : PB I m C1 N p) (hq : PB I m C2 N q) :
    PB I m (C1 + C2) N (fun y => p y + q y) := fun n hn => by
  simpa [coeff_add] using (hp n hn).add (hq n hn)

lemma PB.const_zero (hI : I.Nonempty) (m : ℕ) (N : ℕ) : PB I m 0 N (fun _ => 0) := fun n _ => by
  simpa using (BD.const (I := I) m 0)

lemma PB.finset_sum {ι : Type*} (s : Finset ι) {m N : ℕ} (hI : I.Nonempty) (C : ι → ℝ) (p : ι → ℝ → ℝ[X])
    (h : ∀ i ∈ s, PB I m (C i) N (p i)) : PB I m (∑ i ∈ s, C i) N (fun y => ∑ i ∈ s, p i y) := fun n hn => by
  have := BD.finset_sum s m C (fun i y => (p i y).coeff n) (fun i hi => h i hi n hn)
  simpa [finsetSum_coeff] using this

lemma PB.mono_C {m N : ℕ} {C C' : ℝ} {p : ℝ → ℝ[X]} (hC : C ≤ C') (h : PB I m C N p) : PB I m C' N p :=
  fun n hn => (h n hn).mono_C hC

lemma PB.mono_m {m N : ℕ} {C : ℝ} {p : ℝ → ℝ[X]} (h : PB I (m + 1) C N p) : PB I m C N p :=
  fun n hn => (h n hn).mono_m

lemma PB.mono_le {m m' N : ℕ} (hmm : m ≤ m') {C : ℝ} {p : ℝ → ℝ[X]} (h : PB I m' C N p) : PB I m C N p :=
  fun n hn => (h n hn).mono_le hmm

lemma PB.Cmul (hI : I.Nonempty) {m : ℕ} {C : ℝ} {f : ℝ → ℝ} (hf : BD I m C f) (N : ℕ) : PB I m C N (fun y => Polynomial.C (f y)) := by
  intro n hn
  rcases n with _ | n
  · simpa using hf
  · simpa [coeff_C] using (BD.const (I := I) m 0).mono_C (by simpa using hf.nonneg hI)

lemma PB.X_pow_mul (hI : I.Nonempty) {m N : ℕ} {C : ℝ} {p : ℝ → ℝ[X]} (hp : PB I m C N p) (j : ℕ) :
    PB I m C N (fun y => X ^ j * p y) := by
  intro n hn
  have h0 : 0 ≤ C := (hp 0 (Nat.zero_le _)).nonneg hI
  simp only [coeff_X_pow_mul']
  by_cases hjn : j ≤ n
  · simp only [hjn, if_true]
    exact hp (n - j) (by omega)
  · simp only [hjn, if_false]
    exact (BD.const (I := I) m 0).mono_C (by simpa using h0)

lemma PB.mul_exists (hI : I.Nonempty) (m N : ℕ) (C1 C2 : ℝ) :
    ∃ C3 : ℝ, ∀ p q : ℝ → ℝ[X], PB I m C1 N p → PB I m C2 N q → PB I m C3 N (fun y => p y * q y) := by
  obtain ⟨Cm, hCm⟩ := BD.mul_exists (I := I) m C1 C2
  refine ⟨(N + 1 : ℕ) * |Cm|, fun p q hp hq n hn => ?_⟩
  have := BD.finset_sum (I := I) (antidiagonal n) m (fun _ => Cm) (fun ij y => (p y).coeff ij.1 * (q y).coeff ij.2)
    (fun ij hij => hCm _ _ (hp ij.1 (by have := Finset.HasAntidiagonal.mem_antidiagonal.1 hij; omega))
      (hq ij.2 (by have := Finset.HasAntidiagonal.mem_antidiagonal.1 hij; omega)))
  simp only [coeff_mul]
  refine this.mono_C ?_
  rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
  have h1 : ((n + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hn
  calc ((n + 1 : ℕ) : ℝ) * Cm ≤ ((n + 1 : ℕ) : ℝ) * |Cm| := mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    _ ≤ ((N + 1 : ℕ) : ℝ) * |Cm| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

lemma PB.pow_exists (hI : I.Nonempty) (m N : ℕ) (C1 : ℝ) (k : ℕ) :
    ∃ C : ℝ, ∀ p : ℝ → ℝ[X], PB I m C1 N p → PB I m C N (fun y => (p y) ^ k) := by
  induction k with
  | zero =>
    refine ⟨1, fun p _ n hn => ?_⟩
    simp only [pow_zero, coeff_one]
    rcases n with _ | n
    · simpa using (BD.const (I := I) m 1)
    · simpa using (BD.const (I := I) m 0).mono_C (by norm_num)
  | succ k ih =>
    obtain ⟨Ck, hCk⟩ := ih
    obtain ⟨C3, h3⟩ := PB.mul_exists hI m N Ck C1
    exact ⟨C3, fun p hp => by simpa [pow_succ] using h3 _ p (hCk p hp) hp⟩

lemma PB.Dp (hI : I.Nonempty) (M m N : ℕ) (C2 : ℝ) (a : ℕ → ℝ → ℝ) (ha : ∀ r, 1 ≤ r → r ≤ M → BD I m C2 (a r)) :
    PB I m (M * C2) N (fun y => InvAlg.Dp M (fun r => a r y)) := by
  have h : (fun y => InvAlg.Dp M (fun r => a r y)) = fun y => ∑ r ∈ range M, X ^ (r + 1) * Polynomial.C (a (r + 1) y) := by
    funext y
    simp only [InvAlg.Dp, mul_comm]
  rw [h]
  have := PB.finset_sum (I := I) (range M) (m := m) (N := N) hI (fun _ => C2) (fun r y => X ^ (r + 1) * Polynomial.C (a (r + 1) y))
    (fun r hr => PB.X_pow_mul hI (PB.Cmul hI (ha (r + 1) (by omega) (by have := Finset.mem_range.1 hr; omega)) N) (r + 1))
  simpa using this

lemma PB.Qp_exists (hI : I.Nonempty) (M m K0 N : ℕ) (C1 C2 : ℝ) :
    ∃ C3 : ℝ, ∀ (c : ℕ → ℕ → ℝ → ℝ) (a : ℕ → ℝ → ℝ), (∀ j ≤ M, ∀ k ≤ K0, k ≤ M - j → BD I m C1 (c j k)) →
      (∀ r, 1 ≤ r → r ≤ M → BD I m C2 (a r)) →
      PB I m C3 N (fun y => InvAlg.Qp M (fun j k => c j k y) K0 (InvAlg.Dp M (fun r => a r y))) := by
  have hpow : ∀ k, ∃ Cp, ∀ p : ℝ → ℝ[X], PB I m (M * C2) N p → PB I m Cp N (fun y => (p y) ^ k) :=
    fun k => PB.pow_exists hI m N (M * C2) k
  choose Cp hCp using hpow
  have hmul : ∀ k, ∃ Cm, ∀ p q : ℝ → ℝ[X], PB I m C1 N p → PB I m (Cp k) N q → PB I m Cm N (fun y => p y * q y) :=
    fun k => PB.mul_exists hI m N C1 (Cp k)
  choose Cm hCm using hmul
  refine ⟨∑ j ∈ range (M + 1), ∑ k ∈ range (M - j + 1), |Cm k|, fun c a hc ha => ?_⟩
  unfold InvAlg.Qp
  refine PB.finset_sum (range (M + 1)) hI _ _ (fun j hj => ?_)
  refine PB.X_pow_mul hI ?_ j
  refine PB.finset_sum (range (M - j + 1)) hI _ _ (fun k hk => ?_)
  by_cases hkK : k ≤ K0
  · simp only [hkK, if_true]
    have hjM : j ≤ M := by have := Finset.mem_range.1 hj; omega
    have hkj : k ≤ M - j := by have := Finset.mem_range.1 hk; omega
    have h1 : PB I m C1 N (fun y => Polynomial.C (c j k y)) := PB.Cmul hI (hc j hjM k hkK hkj) N
    have h2 := hCp k _ (PB.Dp hI M m N C2 a ha)
    exact (hCm k _ _ h1 h2).mono_C (le_abs_self _)
  · simp only [hkK, if_false]
    exact (PB.const_zero hI m N).mono_C (abs_nonneg _)

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.InvBD.PB.Qp_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.InvBD.PB.Qp_exists

end FormalResearch.JacobiEigenvectors.TheoremA.InvBD
