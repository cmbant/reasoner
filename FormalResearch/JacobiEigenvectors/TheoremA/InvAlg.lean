module

public import Mathlib

/-!
# Paper J, Layer 2: the coefficient recursion of `InvCoeffs` as polynomial algebra (L2.E)

Source: Paper J `thmA.tex`, proof of `cor:eigen` (b)(iii): "the coefficient of `h^r` in `F_M(sum_s h^s x_s, h) = y` gives `x_1 = -S_1(x_0)/S_0'(x_0)` and `x_2 = ...`".

## Proved here

For reals `c j k` (the Taylor coefficients `S_j^{(k)}(x_0)/k!`) and `c 0 1 != 0`:

* `Dp M a = sum_{r=1}^M a_r X^r`, `Qp M c K0 D = sum_{j <= M} X^j sum_{k <= M-j, k <= K0} c_{jk} D^k` (the Taylor polynomial of `sum_j h^j S_j(x_0 + delta)`).
* `Qp_step`, `Qp_trunc`: adding `e X^n` to `D` changes the coefficients `0..n` of `Qp` by `c_{01} e` at `n` only; truncating `k <= K0` does not change the coefficients `<= K0`.
* `st`: the stage sequences `a_n = -coeff_n(Qp(D_{n-1}))/c_{01}`; **`Qp_vanish`**: the coefficients `1..n` of `Qp M c M (Dp (st n))` vanish.
* `st_one`, `st_two`: `x_1 = -c_{10}/c_{01}`, `x_2 = -(c_{20} + c_{11} x_1 + c_{02} x_1^2)/c_{01}` (the stated formulas of `InvCoeffs`).
* `tail_eval`: a polynomial with bounded coefficients, constant term `c`, vanishing coefficients `1..M` satisfies `|p(h) - c| <= (N0 + 1) Cq h^{M+1}` for `0 < h <= 1`; `natDegree_Qp_le`.

## Differences from the paper

The recursion is organised by `Polynomial.coeff`, so no multinomial bookkeeping is needed; the paper writes the coefficient of `h^r` explicitly for `r <= 2` only.

## Not formalised

Nothing: pure algebra.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA.InvAlg

open Polynomial Finset

variable (M : ℕ) (c : ℕ → ℕ → ℝ)

/-- `delta(h) = sum_{r = 1}^M a_r h^r`. -/
def Dp (a : ℕ → ℝ) : ℝ[X] := ∑ r ∈ range M, C (a (r + 1)) * X ^ (r + 1)

/-- `sum_{j <= M} h^j sum_{k <= M - j, k <= K0} c_{jk} delta^k` (the Taylor polynomial of `sum_j h^j S_j(x_0 + delta)`). -/
def Qp (K0 : ℕ) (D : ℝ[X]) : ℝ[X] :=
  ∑ j ∈ range (M + 1), X ^ j * ∑ k ∈ range (M - j + 1), if k ≤ K0 then C (c j k) * D ^ k else 0

lemma X_dvd_Dp (a : ℕ → ℝ) : (X : ℝ[X]) ∣ Dp M a :=
  Finset.dvd_sum fun r _ => dvd_mul_of_dvd_right (dvd_pow_self X (Nat.succ_ne_zero r)) _

lemma Dp_update (a : ℕ → ℝ) {n : ℕ} (hn1 : 1 ≤ n) (hnM : n ≤ M) (v : ℝ) :
    Dp M (fun r => if r = n then v else a r) = Dp M a + C (v - a n) * X ^ n := by
  unfold Dp
  have h1 : ∀ r ∈ range M, C ((fun r => if r = n then v else a r) (r + 1)) * (X : ℝ[X]) ^ (r + 1) =
      C (a (r + 1)) * X ^ (r + 1) + (if r = n - 1 then C (v - a n) * X ^ n else 0) := by
    intro r hr
    by_cases h : r + 1 = n
    · subst h
      have h' : r = r + 1 - 1 := by omega
      simp only [ite_true, h'.symm, C_sub]
      ring
    · have h' : r ≠ n - 1 := by omega
      simp [h, h']
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_ite_eq']
  rw [ite_eq_left_iff.2 (fun h => absurd (Finset.mem_range.2 (by omega)) h)]

lemma Qp_trunc {D : ℝ[X]} (hD : (X : ℝ[X]) ∣ D) {K0 K0' n : ℕ} (hK : K0 ≤ K0') (hn : n ≤ K0) :
    (Qp M c K0' D).coeff n = (Qp M c K0 D).coeff n := by
  obtain ⟨D1, rfl⟩ := hD
  unfold Qp
  simp only [finsetSum_coeff]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [coeff_X_pow_mul', coeff_X_pow_mul']
  split_ifs with hjn
  · simp only [finsetSum_coeff]
    refine Finset.sum_congr rfl fun k hk => ?_
    by_cases h1 : k ≤ K0
    · simp [h1, h1.trans hK]
    · by_cases h2 : k ≤ K0'
      · simp only [h1, h2, ite_true, ite_false, coeff_zero]
        rw [mul_pow, ← mul_assoc, mul_comm (C (c j k)), mul_assoc, coeff_X_pow_mul']
        rw [ite_eq_right_iff.2 (fun h => absurd h (by omega))]
      · simp [h1, h2]
  · rfl

lemma X_dvd_pow_sub {D : ℝ[X]} (hD : (X : ℝ[X]) ∣ D) {n : ℕ} (hn : 1 ≤ n) (e : ℝ) {k : ℕ} (hk : 2 ≤ k) :
    (X : ℝ[X]) ^ (n + 1) ∣ (D + C e * X ^ n) ^ k - D ^ k := by
  have hD' : (X : ℝ[X]) ∣ D + C e * X ^ n :=
    dvd_add hD (dvd_mul_of_dvd_right (dvd_pow_self X (by omega)) _)
  have hgeom := Commute.geom_sum₂_mul (Commute.all (D + C e * X ^ n) D) k
  have hsub : D + C e * X ^ n - D = C e * X ^ n := by ring
  rw [hsub] at hgeom
  rw [← hgeom]
  have hX : (X : ℝ[X]) ∣ ∑ i ∈ range k, (D + C e * X ^ n) ^ i * D ^ (k - 1 - i) := by
    refine Finset.dvd_sum fun i hi => ?_
    by_cases h0 : i = 0
    · subst h0
      simp only [pow_zero, one_mul]
      exact dvd_pow hD (by omega)
    · exact dvd_mul_of_dvd_left (dvd_pow hD' h0) _
  obtain ⟨R, hR⟩ := hX
  rw [hR]
  exact ⟨C e * R, by ring⟩

lemma Qp_step {D : ℝ[X]} (hD : (X : ℝ[X]) ∣ D) {K0 n : ℕ} (hn : 1 ≤ n) (hK0 : 1 ≤ K0) (hM : 1 ≤ M) (e : ℝ) {m : ℕ} (hm : m ≤ n) :
    (Qp M c K0 (D + C e * X ^ n)).coeff m = (Qp M c K0 D).coeff m + if m = n then c 0 1 * e else 0 := by
  set D' := D + C e * X ^ n with hD'
  have hXn : (X : ℝ[X]) ^ n ∣ D' - D := ⟨C e, by rw [hD']; ring⟩
  -- the special term
  let sp : ℕ → ℕ → ℝ[X] := fun j k => if j = 0 ∧ k = 1 then C (c 0 1 * e) * X ^ n else 0
  have hterm : ∀ j ∈ range (M + 1), ∀ k ∈ range (M - j + 1),
      (X : ℝ[X]) ^ (n + 1) ∣ X ^ j * (if k ≤ K0 then C (c j k) * D' ^ k else 0) - X ^ j * (if k ≤ K0 then C (c j k) * D ^ k else 0) - sp j k := by
    intro j hj k hk
    by_cases hkK : k ≤ K0
    · simp only [hkK, ite_true]
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · interval_cases k
        · simp [sp]
        · by_cases hj0 : j = 0
          · subst hj0
            have : (X : ℝ[X]) ^ 0 * (C (c 0 1) * D' ^ 1) - X ^ 0 * (C (c 0 1) * D ^ 1) - sp 0 1 = 0 := by
              simp only [sp, pow_zero, one_mul, pow_one, and_self, ite_true, hD', C_mul]; ring
            rw [this]; exact dvd_zero _
          · have : sp j 1 = 0 := by simp [sp, hj0]
            rw [this, sub_zero]
            have h1 : (X : ℝ[X]) ^ (n + 1) ∣ X ^ j * (C (c j 1) * (D' - D)) := by
              have : (X : ℝ[X]) ^ (n + 1) ∣ X ^ j * X ^ n := by
                rw [← pow_add]; exact pow_dvd_pow _ (by omega)
              exact dvd_trans this (mul_dvd_mul_left _ (dvd_mul_of_dvd_right hXn _))
            have e1 : (X : ℝ[X]) ^ j * (C (c j 1) * D' ^ 1) - X ^ j * (C (c j 1) * D ^ 1) = X ^ j * (C (c j 1) * (D' - D)) := by ring
            rw [e1]; exact h1
      · have hdv := X_dvd_pow_sub hD hn e hk2
        have : sp j k = 0 := by
          have : k ≠ 1 := by omega
          simp [sp, this]
        rw [this, sub_zero]
        have e1 : (X : ℝ[X]) ^ j * (C (c j k) * D' ^ k) - X ^ j * (C (c j k) * D ^ k) = X ^ j * (C (c j k) * (D' ^ k - D ^ k)) := by ring
        rw [e1]
        exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hdv _) _
    · have : sp j k = 0 := by
        have : k ≠ 1 := by omega
        simp [sp, this]
      simp [hkK, this]
  have hsum : (X : ℝ[X]) ^ (n + 1) ∣ Qp M c K0 D' - Qp M c K0 D - C (c 0 1 * e) * X ^ n := by
    have hsp : ∑ j ∈ range (M + 1), ∑ k ∈ range (M - j + 1), sp j k = C (c 0 1 * e) * X ^ n := by
      rw [Finset.sum_eq_single 0]
      · rw [Finset.sum_eq_single 1]
        · simp [sp]
        · intro b _ hb; simp [sp, hb]
        · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
      · intro b _ hb; simp [sp, hb]
      · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
    have h2 : Qp M c K0 D' - Qp M c K0 D - C (c 0 1 * e) * X ^ n =
        ∑ j ∈ range (M + 1), ∑ k ∈ range (M - j + 1), (X ^ j * (if k ≤ K0 then C (c j k) * D' ^ k else 0) -
          X ^ j * (if k ≤ K0 then C (c j k) * D ^ k else 0) - sp j k) := by
      simp only [Finset.sum_sub_distrib, hsp]
      unfold Qp
      simp only [Finset.mul_sum, Finset.sum_sub_distrib]
    rw [h2]
    exact Finset.dvd_sum fun j hj => Finset.dvd_sum fun k hk => hterm j hj k hk
  have hc := (X_pow_dvd_iff.1 hsum) m (by omega)
  rw [coeff_sub, coeff_sub, coeff_C_mul_X_pow] at hc
  linarith

/-- The stage sequences: `st n r = a_r` for `1 <= r <= n` (the coefficients `x_r` of the expansion), `0` for `r > n`. -/
def st (X0 : ℝ) : ℕ → ℕ → ℝ
  | 0 => fun r => if r = 0 then X0 else 0
  | n + 1 => fun r => if r = n + 1 then -((Qp M c (n + 1) (Dp M (st X0 n))).coeff (n + 1)) / c 0 1 else st X0 n r

lemma st_gt (X0 : ℝ) : ∀ n r : ℕ, n < r → st M c X0 n r = 0
  | 0, r, h => by simp [st, show r ≠ 0 by omega]
  | n + 1, r, h => by
    simp only [st, show r ≠ n + 1 by omega, ite_false]
    exact st_gt X0 n r (by omega)

lemma st_succ_self (X0 : ℝ) (n : ℕ) :
    st M c X0 (n + 1) (n + 1) = -((Qp M c (n + 1) (Dp M (st M c X0 n))).coeff (n + 1)) / c 0 1 := by
  simp [st]

lemma st_succ_of_ne (X0 : ℝ) {n r : ℕ} (h : r ≠ n + 1) : st M c X0 (n + 1) r = st M c X0 n r := by
  simp [st, h]

lemma st_stable (X0 : ℝ) {r : ℕ} : ∀ n : ℕ, r ≤ n → st M c X0 n r = st M c X0 r r := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih => rw [st_succ_of_ne M c X0 (by omega), ih]

lemma Dp_st_succ (X0 : ℝ) {n : ℕ} (hn : n + 1 ≤ M) :
    Dp M (st M c X0 (n + 1)) = Dp M (st M c X0 n) +
      C (-((Qp M c (n + 1) (Dp M (st M c X0 n))).coeff (n + 1)) / c 0 1) * X ^ (n + 1) := by
  have h := Dp_update M (st M c X0 n) (n := n + 1) (by omega) hn (-((Qp M c (n + 1) (Dp M (st M c X0 n))).coeff (n + 1)) / c 0 1)
  have e : st M c X0 (n + 1) = fun r => if r = n + 1 then -((Qp M c (n + 1) (Dp M (st M c X0 n))).coeff (n + 1)) / c 0 1 else st M c X0 n r := by
    funext r; rfl
  rw [e, h, st_gt M c X0 n (n + 1) (by omega), sub_zero]

/-- **The coefficient identity**: the first `n` coefficients of the Taylor polynomial vanish. -/
lemma Qp_vanish (X0 : ℝ) (hM : 1 ≤ M) (hc : c 0 1 ≠ 0) :
    ∀ n : ℕ, n ≤ M → ∀ m : ℕ, 1 ≤ m → m ≤ n → (Qp M c M (Dp M (st M c X0 n))).coeff m = 0 := by
  intro n
  induction n with
  | zero => intro _ m h1 h2; omega
  | succ n ih =>
    intro hn m hm1 hmn
    have hn' : n ≤ M := by omega
    rw [Dp_st_succ M c X0 hn]
    rw [Qp_step M c (X_dvd_Dp M _) (by omega) (by omega) hM _ hmn]
    by_cases hmn' : m = n + 1
    · subst hmn'
      rw [ite_eq_left rfl, Qp_trunc M c (X_dvd_Dp M _) (K0 := n + 1) (K0' := M) hn le_rfl]
      field_simp
      ring
    · rw [ite_eq_right hmn', add_zero]
      exact ih hn' m hm1 (by omega)

lemma eval_Dp (a : ℕ → ℝ) (h : ℝ) : (Dp M a).eval h = ∑ r ∈ range M, a (r + 1) * h ^ (r + 1) := by
  simp [Dp, eval_finsetSum]

lemma eval_Qp (K0 : ℕ) (D : ℝ[X]) (h : ℝ) :
    (Qp M c K0 D).eval h = ∑ j ∈ range (M + 1), h ^ j * ∑ k ∈ range (M - j + 1), if k ≤ K0 then c j k * (D.eval h) ^ k else 0 := by
  unfold Qp
  simp only [eval_finsetSum, eval_mul, eval_pow, eval_X]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

lemma Qp_coeff_zero {D : ℝ[X]} (hD : (X : ℝ[X]) ∣ D) (K0 : ℕ) : (Qp M c K0 D).coeff 0 = c 0 0 := by
  rw [coeff_zero_eq_eval_zero, eval_Qp]
  have hD0 : D.eval 0 = 0 := by
    obtain ⟨D1, rfl⟩ := hD; simp
  rw [hD0, Finset.sum_eq_single 0]
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro k _ hk
      simp [zero_pow hk]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  · intro j _ hj
    simp [hj]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

lemma Qp_zero (K0 : ℕ) : Qp M c K0 0 = ∑ j ∈ range (M + 1), X ^ j * C (c j 0) := by
  unfold Qp
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [zero_pow hk]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

lemma Dp_zero_stage (X0 : ℝ) : Dp M (st M c X0 0) = 0 := by
  unfold Dp
  exact Finset.sum_eq_zero fun r _ => by simp [st]

/-- `x_1 = - S_1(x_0)/S_0'(x_0)` (`c j 0 = S_j(x_0)`, `c 0 1 = S_0'(x_0)`). -/
lemma st_one (X0 : ℝ) (hM : 1 ≤ M) : st M c X0 1 1 = -(c 1 0) / c 0 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, st_succ_self, Dp_zero_stage, Qp_zero, finsetSum_coeff]
  congr 2
  rw [Finset.sum_eq_single 1]
  · simp [coeff_X_pow, coeff_C]
  · intro j _ hj
    rw [coeff_X_pow_mul']
    split_ifs with h
    · have : j = 0 := by omega
      subst this
      simp [coeff_C]
    · rfl
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

lemma Dp_one_stage (X0 : ℝ) (hM : 1 ≤ M) : Dp M (st M c X0 1) = C (st M c X0 1 1) * X := by
  have h := Dp_st_succ M c X0 (n := 0) hM
  rw [Dp_zero_stage, zero_add] at h
  rw [show (1 : ℕ) = 0 + 1 from rfl, h, st_succ_self, pow_one, Dp_zero_stage]
  simp

lemma coeff_Qp_inner (a : ℝ) (K0 j e : ℕ) :
    (∑ k ∈ range (M - j + 1), if k ≤ K0 then C (c j k) * (C a * (X : ℝ[X])) ^ k else 0).coeff e =
      if e ≤ M - j ∧ e ≤ K0 then c j e * a ^ e else 0 := by
  rw [finsetSum_coeff]
  have h1 : ∀ k ∈ range (M - j + 1), (if k ≤ K0 then C (c j k) * (C a * (X : ℝ[X])) ^ k else 0).coeff e =
      if e = k ∧ k ≤ K0 then c j k * a ^ k else 0 := by
    intro k _
    by_cases hk : k ≤ K0
    · simp only [hk, ite_true, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow, and_true]
    · simp [hk]
  rw [Finset.sum_congr rfl h1]
  by_cases he : e ≤ M - j ∧ e ≤ K0
  · rw [Finset.sum_eq_single e]
    · rw [ite_eq_left ⟨rfl, he.2⟩, ite_eq_left he]
    · intro k _ hk; simp [Ne.symm hk]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  · rw [ite_eq_right he]
    refine Finset.sum_eq_zero fun k hk => ?_
    by_cases hke : e = k
    · subst hke
      rw [Finset.mem_range] at hk
      have : ¬ (e ≤ K0) := fun h => he ⟨by omega, h⟩
      simp [this]
    · simp [hke]

lemma coeff_Qp_two (a : ℝ) (hM : 2 ≤ M) :
    (Qp M c 2 (C a * X)).coeff 2 = c 2 0 + c 1 1 * a + c 0 2 * a ^ 2 := by
  unfold Qp
  rw [finsetSum_coeff]
  have h1 : ∀ j ∈ range (M + 1), (X ^ j * ∑ k ∈ range (M - j + 1), if k ≤ 2 then C (c j k) * (C a * (X : ℝ[X])) ^ k else 0).coeff 2 =
      if j ≤ 2 then (if 2 - j ≤ M - j ∧ 2 - j ≤ 2 then c j (2 - j) * a ^ (2 - j) else 0) else 0 := by
    intro j _
    rw [coeff_X_pow_mul', coeff_Qp_inner]
  rw [Finset.sum_congr rfl h1]
  rw [← Finset.sum_subset (s₁ := range 3) (s₂ := range (M + 1)) (fun j hj => Finset.mem_range.2 (by have := Finset.mem_range.1 hj; omega))]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp [show 2 ≤ M - 0 from by omega, show 1 ≤ M - 1 from by omega, show 0 ≤ M - 2 from by omega, hM]
    ring
  · intro j _ hj
    have : ¬ j ≤ 2 := by have := Finset.mem_range.not.1 hj; omega
    simp [this]

lemma st_two (X0 : ℝ) (hM : 2 ≤ M) :
    st M c X0 2 2 = -(c 2 0 + c 1 1 * st M c X0 1 1 + c 0 2 * st M c X0 1 1 ^ 2) / c 0 1 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, st_succ_self, Dp_one_stage M c X0 (by omega), coeff_Qp_two M c _ hM]

lemma natDegree_Dp_le (a : ℕ → ℝ) : (Dp M a).natDegree ≤ M := by
  unfold Dp
  refine natDegree_sum_le_of_forall_le _ _ fun r hr => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (Finset.mem_range.1 hr)

lemma natDegree_Qp_le (hM : 1 ≤ M) {K0 : ℕ} {D : ℝ[X]} (hD : D.natDegree ≤ M) : (Qp M c K0 D).natDegree ≤ M * M := by
  unfold Qp
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  have hjM : j ≤ M := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  refine (natDegree_mul_le.trans ?_)
  rw [natDegree_X_pow]
  have h1 : (∑ k ∈ range (M - j + 1), if k ≤ K0 then C (c j k) * D ^ k else 0).natDegree ≤ (M - j) * M := by
    refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    have hkj : k ≤ M - j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    split_ifs
    · refine (natDegree_C_mul_le _ _).trans ?_
      exact (natDegree_pow_le.trans (Nat.mul_le_mul hkj hD))
    · simp
  have h2 : j ≤ j * M := Nat.le_mul_of_pos_right j hM
  have h3 : j + (M - j) * M ≤ M * M := by
    have : (M - j) * M + j * M = M * M := by rw [← Nat.add_mul, Nat.sub_add_cancel hjM]
    omega
  omega

/-- A polynomial with vanishing coefficients `1..M` and bounded coefficients is within `(N0 + 1) Cq h^{M+1}` of its constant term. -/
lemma tail_eval {Q : ℝ[X]} {N0 M : ℕ} {c00 Cq h : ℝ} (hdeg : Q.natDegree ≤ N0) (h0 : Q.coeff 0 = c00)
    (hvan : ∀ n, 1 ≤ n → n ≤ M → Q.coeff n = 0) (hbd : ∀ n ≤ N0, |Q.coeff n| ≤ Cq) (hh : 0 < h) (hh1 : h ≤ 1) :
    |Q.eval h - c00| ≤ (N0 + 1) * Cq * h ^ (M + 1) := by
  have hCq : 0 ≤ Cq := (abs_nonneg _).trans (hbd 0 (Nat.zero_le _))
  rw [eval_eq_sum_range' (n := N0 + 1) (by omega)]
  have hsplit : ∀ n ∈ range (N0 + 1), Q.coeff n * h ^ n = (if n = 0 then c00 else 0) + (if M < n then Q.coeff n * h ^ n else 0) := by
    intro n _
    by_cases hn0 : n = 0
    · subst hn0; simp [h0]
    · by_cases hMn : M < n
      · simp [hn0, hMn]
      · simp [hn0, hMn, hvan n (by omega) (by omega)]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq' (range (N0 + 1)) 0,
    ite_eq_left (Finset.mem_range.2 (by omega)), add_sub_cancel_left]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ n ∈ range (N0 + 1), |if M < n then Q.coeff n * h ^ n else 0| ≤ ∑ n ∈ range (N0 + 1), Cq * h ^ (M + 1) := by
        refine Finset.sum_le_sum fun n hn => ?_
        by_cases hMn : M < n
        · simp only [hMn, if_true, abs_mul, abs_pow, abs_of_pos hh]
          refine mul_le_mul (hbd n (by have := Finset.mem_range.1 hn; omega)) (pow_le_pow_of_le_one hh.le hh1 (by omega)) (by positivity) hCq
        · simp [hMn]; positivity
    _ = (N0 + 1) * Cq * h ^ (M + 1) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.InvAlg.Qp_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.InvAlg.Qp_step

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.InvAlg.Qp_vanish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.InvAlg.Qp_vanish

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.InvAlg.st_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.InvAlg.st_one

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.InvAlg.st_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.InvAlg.st_two

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.InvAlg.tail_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.InvAlg.tail_eval

end FormalResearch.JacobiEigenvectors.TheoremA.InvAlg
