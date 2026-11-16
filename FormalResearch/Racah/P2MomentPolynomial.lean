module

public import Mathlib

/-!
# The moment polynomial `π_s` (Weyl P2, `lem:momentpolynomial`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `lem:momentpolynomial` (appendix
`app:localgeneral`, the key lemma of the neighboring-moment reduction `eq:3jneighbormomentidentity`
of `prop:localcalculus`).  With `λ_k = k(k+1)`:

> for every integer `s ≥ 1` there is a unique polynomial `π_s` of degree `s` with
> `π_s(λ_k) + π_s(λ_{k+1}) = 2 (k+1)^{2s}` (`eq:3jpimoment`), and `π_s(0) = 0`.

What is formalised (over any field `K` of characteristic zero, exact algebra, no asymptotics):

* `momentMap`, the linear map `T[p](y) = p(y² - y) + p(y² + y)` of the paper's proof;
  `momentMap_surjective_even`: `T` maps `K[z]` **onto** the even polynomials of `K[y]`, and
  `momentMap_injective`: injectively (so it is a bijection onto them; the paper's proof states
  invertibility only from `{deg ≤ s}` into `{even, deg ≤ 2s}`);
* `momentPoly_exists_unique`: the statement of the lemma, pointwise in `k : K`
  (equivalently as a polynomial identity in `k`), with **uniqueness among all polynomials** (no degree
  assumption is needed: the degree `s` and monicity are consequences, `natDegree_momentPoly`,
  `monic_momentPoly`), and `momentPoly_eval_zero` (`π_s(0) = 0`, `s ≥ 1`);
* `momentPoly_one`, `momentPoly_two`: `π_1 = z`, `π_2 = z(z-1)`, as stated after the lemma.

Not formalised: the operators `𝒩_s` and the identity `eq:3jneighbormomentidentity`, which are in
`P2LocalCalculus`.
-/

@[expose] public section

namespace FormalResearch.Racah.LocalCalculus

open Polynomial

section Moment

variable {K : Type*} [Field K]

/-- `T[p](y) = p(y² - y) + p(y² + y)` (the linear map of the proof of `lem:momentpolynomial`);
with `y = k+1` it is `p(λ_k) + p(λ_{k+1})`. -/
noncomputable def momentMap (p : K[X]) : K[X] := p.comp (X ^ 2 - X) + p.comp (X ^ 2 + X)

theorem momentMap_add (p q : K[X]) : momentMap (p + q) = momentMap p + momentMap q := by
  simp only [momentMap, add_comp]; ring

theorem momentMap_sub (p q : K[X]) : momentMap (p - q) = momentMap p - momentMap q := by
  simp only [momentMap, sub_comp]; ring

theorem momentMap_C_mul (c : K) (p : K[X]) : momentMap (C c * p) = C c * momentMap p := by
  simp only [momentMap, mul_comp, C_comp]; ring

theorem eval_momentMap (p : K[X]) (y : K) :
    (momentMap p).eval y = p.eval (y ^ 2 - y) + p.eval (y ^ 2 + y) := by
  simp [momentMap, eval_comp]

private theorem natDegree_sq_sub_X : (X ^ 2 - X : K[X]).natDegree = 2 := by
  have : (X ^ 2 - X : K[X]) = X ^ 2 + C (-1) * X := by simp [sub_eq_add_neg]
  rw [this]; compute_degree!

private theorem natDegree_sq_add_X : (X ^ 2 + X : K[X]).natDegree = 2 := by
  compute_degree!

private theorem leadingCoeff_sq_sub_X : (X ^ 2 - X : K[X]).leadingCoeff = 1 := by
  have : (X ^ 2 - X : K[X]).Monic := by
    apply Polynomial.monic_X_pow_sub; simp
  exact this

private theorem leadingCoeff_sq_add_X : (X ^ 2 + X : K[X]).leadingCoeff = 1 := by
  have : (X ^ 2 + X : K[X]).Monic := by
    apply Polynomial.monic_X_pow_add; simp
  exact this

theorem natDegree_momentMap_le (p : K[X]) : (momentMap p).natDegree ≤ 2 * p.natDegree := by
  unfold momentMap
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · rw [natDegree_comp, natDegree_sq_sub_X]; omega
  · rw [natDegree_comp, natDegree_sq_add_X]; omega

/-- The top coefficient of `T[p]` is `2 · lc(p)`. -/
theorem coeff_momentMap_top (p : K[X]) :
    (momentMap p).coeff (2 * p.natDegree) = 2 * p.leadingCoeff := by
  have h1 := coeff_comp_degree_mul_degree (p := p) (q := (X ^ 2 - X : K[X]))
    (by rw [natDegree_sq_sub_X]; norm_num)
  have h2 := coeff_comp_degree_mul_degree (p := p) (q := (X ^ 2 + X : K[X]))
    (by rw [natDegree_sq_add_X]; norm_num)
  rw [natDegree_sq_sub_X, leadingCoeff_sq_sub_X, one_pow, mul_one] at h1
  rw [natDegree_sq_add_X, leadingCoeff_sq_add_X, one_pow, mul_one] at h2
  simp only [momentMap, coeff_add]
  rw [mul_comm 2 p.natDegree, h1, h2]; ring

/-- `T` is injective. -/
theorem momentMap_injective [CharZero K] : Function.Injective (momentMap (K := K)) := by
  intro p q hpq
  by_contra hne
  have hd : p - q ≠ 0 := sub_ne_zero.mpr hne
  have h0 : momentMap (p - q) = 0 := by rw [momentMap_sub, hpq, sub_self]
  have := coeff_momentMap_top (p - q)
  rw [h0] at this
  have hlc : (p - q).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hd
  have h2 : (2 : K) * (p - q).leadingCoeff = 0 := by simpa using this.symm
  rcases mul_eq_zero.mp h2 with h | h
  · exact two_ne_zero h
  · exact hlc h

private theorem coeff_comp_neg_X (p : K[X]) (n : ℕ) :
    (p.comp (-X)).coeff n = (-1) ^ n * p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial m a =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, neg_pow, coeff_C_mul]
    have : ((-1 : K[X]) ^ m) = C ((-1 : K) ^ m) := by simp
    rw [this, coeff_C_mul, coeff_C_mul, coeff_X_pow]
    split_ifs with h
    · subst h; ring
    · simp

/-- Evenness in the variable `y`: all odd coefficients vanish. -/
def IsEvenPoly (f : K[X]) : Prop := ∀ n, Odd n → f.coeff n = 0

theorem momentMap_comp_neg (p : K[X]) : (momentMap p).comp (-X) = momentMap p := by
  simp only [momentMap, add_comp, comp_assoc, sub_comp, add_comp, X_pow_comp, X_comp]
  rw [add_comm]; congr 2 <;> ring

theorem isEvenPoly_momentMap [CharZero K] (p : K[X]) : IsEvenPoly (momentMap p) := by
  intro n hn
  have h := congrArg (fun f => f.coeff n) (momentMap_comp_neg p)
  simp only [coeff_comp_neg_X, hn.neg_one_pow] at h
  have : (2 : K) * (momentMap p).coeff n = 0 := by linear_combination -h
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

/-- Every even polynomial of degree `≤ 2n` is `T[p]` for some `p` of degree `≤ n`. -/
theorem exists_momentMap_eq [CharZero K] :
    ∀ (n : ℕ) (f : K[X]), IsEvenPoly f → f.natDegree ≤ 2 * n →
      ∃ p : K[X], p.natDegree ≤ n ∧ momentMap p = f := by
  intro n
  induction n with
  | zero =>
    intro f _ hf
    have hf0 : f = C (f.coeff 0) := eq_C_of_natDegree_le_zero (by omega)
    refine ⟨C (f.coeff 0 / 2), by simp, ?_⟩
    rw [hf0]
    simp only [momentMap, C_comp, coeff_C_zero]
    rw [← C_add]; congr 1; ring
  | succ n ih =>
    intro f hev hf
    set c := f.coeff (2 * (n + 1)) with hc
    set p0 : K[X] := C (c / 2) * X ^ (n + 1) with hp0
    have hp0deg : p0.natDegree = n + 1 ∨ c = 0 := by
      by_cases h : c = 0
      · exact Or.inr h
      · left; rw [hp0, natDegree_C_mul_X_pow _ _ (by simpa using h)]
    have hp0le : p0.natDegree ≤ n + 1 := by
      rw [hp0]; exact natDegree_C_mul_X_pow_le _ _
    have hTtop : (momentMap p0).coeff (2 * (n + 1)) = c := by
      by_cases h : c = 0
      · have : p0 = 0 := by simp [hp0, h]
        rw [this, h]; simp [momentMap]
      · have hn : p0.natDegree = n + 1 := hp0deg.resolve_right h
        have := coeff_momentMap_top p0
        rw [hn] at this
        rw [this, hp0, leadingCoeff_C_mul_X_pow]; ring
    set g := f - momentMap p0 with hg
    have hgev : IsEvenPoly g := by
      intro m hm
      rw [hg, coeff_sub, hev m hm, isEvenPoly_momentMap p0 m hm, sub_zero]
    have hgdeg : g.natDegree ≤ 2 * n := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      have hTle := natDegree_momentMap_le p0
      by_cases h1 : N = 2 * n + 1
      · exact hgev N ⟨n, by omega⟩
      by_cases h2 : N = 2 * n + 2
      · rw [hg, coeff_sub, show N = 2 * (n + 1) by omega, hTtop, ← hc, sub_self]
      · have h3 : 2 * (n + 1) < N := by omega
        rw [hg, coeff_sub]
        have a1 : f.coeff N = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
        have a2 : (momentMap p0).coeff N = 0 :=
          coeff_eq_zero_of_natDegree_lt (by omega)
        rw [a1, a2, sub_zero]
    obtain ⟨q, hq, hqg⟩ := ih g hgev hgdeg
    refine ⟨q + p0, ?_, ?_⟩
    · exact (natDegree_add_le _ _).trans (max_le (by omega) hp0le)
    · rw [momentMap_add, hqg, hg]; ring

/-- `T` is a bijection from `K[z]` onto the even polynomials of `K[y]`. -/
theorem momentMap_bijective_even [CharZero K] (f : K[X]) (hf : IsEvenPoly f) :
    ∃! p : K[X], momentMap p = f := by
  obtain ⟨p, -, hp⟩ := exists_momentMap_eq f.natDegree f hf (by omega)
  exact ⟨p, hp, fun q hq => momentMap_injective (hq.trans hp.symm)⟩

theorem momentMap_ne_zero [CharZero K] {p : K[X]} (hp : p ≠ 0) : momentMap p ≠ 0 := by
  intro h
  have := coeff_momentMap_top p
  rw [h, coeff_zero] at this
  have hl : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  rcases mul_eq_zero.mp this.symm with h2 | h2
  · exact two_ne_zero h2
  · exact hl h2

theorem natDegree_momentMap [CharZero K] {p : K[X]} (hp : p ≠ 0) :
    (momentMap p).natDegree = 2 * p.natDegree := by
  refine le_antisymm (natDegree_momentMap_le p) ?_
  apply le_natDegree_of_ne_zero
  rw [coeff_momentMap_top]
  exact mul_ne_zero two_ne_zero (leadingCoeff_ne_zero.mpr hp)

/-- The two-sided statement as a polynomial identity in `y = k + 1`. -/
theorem momentMap_eq_iff (π : K[X]) (s : ℕ) [CharZero K] :
    momentMap π = C 2 * X ^ (2 * s) ↔
      ∀ k : K, π.eval (k * (k + 1)) + π.eval ((k + 1) * (k + 2)) = 2 * (k + 1) ^ (2 * s) := by
  constructor
  · intro h k
    have := congrArg (eval (k + 1)) h
    rw [eval_momentMap] at this
    simp only [eval_mul, eval_C, eval_pow, eval_X] at this
    have e1 : (k + 1) ^ 2 - (k + 1) = k * (k + 1) := by ring
    have e2 : (k + 1) ^ 2 + (k + 1) = (k + 1) * (k + 2) := by ring
    rwa [e1, e2] at this
  · intro h
    apply Polynomial.funext
    intro y
    rw [eval_momentMap]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    have := h (y - 1)
    have e1 : (y - 1) * (y - 1 + 1) = y ^ 2 - y := by ring
    have e2 : (y - 1 + 1) * (y - 1 + 2) = y ^ 2 + y := by ring
    rwa [e1, e2, sub_add_cancel] at this

/-- **`lem:momentpolynomial`** (`eq:3jpimoment`).  For every `s`, there is exactly one polynomial `π`
with `π(λ_k) + π(λ_{k+1}) = 2 (k+1)^{2s}` for all `k` (`λ_k = k(k+1)`); uniqueness holds among all
polynomials.  Its degree is `s` and it is monic (`natDegree_momentPoly`, `monic_momentPoly`),
and `π(0) = 0` for `s ≥ 1` (`momentPoly_eval_zero`). -/
theorem momentPoly_exists_unique [CharZero K] (s : ℕ) :
    ∃! π : K[X], ∀ k : K, π.eval (k * (k + 1)) + π.eval ((k + 1) * (k + 2)) = 2 * (k + 1) ^ (2 * s) := by
  have hev : IsEvenPoly (C 2 * X ^ (2 * s) : K[X]) := by
    intro n hn
    rw [coeff_C_mul, coeff_X_pow]
    split_ifs with h
    · exact absurd (h ▸ hn) (by simp)
    · simp
  obtain ⟨π, hπ, huniq⟩ := momentMap_bijective_even _ hev
  exact ⟨π, (momentMap_eq_iff π s).mp hπ, fun q hq => huniq q ((momentMap_eq_iff q s).mpr hq)⟩

/-- The moment polynomial `π_s`. -/
noncomputable def momentPoly (K : Type*) [Field K] [CharZero K] (s : ℕ) : K[X] :=
  (momentPoly_exists_unique (K := K) s).choose

theorem momentPoly_spec [CharZero K] (s : ℕ) (k : K) :
    (momentPoly K s).eval (k * (k + 1)) + (momentPoly K s).eval ((k + 1) * (k + 2)) =
      2 * (k + 1) ^ (2 * s) :=
  (momentPoly_exists_unique (K := K) s).choose_spec.1 k

theorem momentPoly_unique [CharZero K] {s : ℕ} {π : K[X]}
    (h : ∀ k : K, π.eval (k * (k + 1)) + π.eval ((k + 1) * (k + 2)) = 2 * (k + 1) ^ (2 * s)) :
    π = momentPoly K s :=
  (momentPoly_exists_unique (K := K) s).choose_spec.2 π h

theorem momentMap_momentPoly [CharZero K] (s : ℕ) :
    momentMap (momentPoly K s) = C 2 * X ^ (2 * s) :=
  (momentMap_eq_iff _ s).mpr (momentPoly_spec s)

/-- The same identity one step down (`k ↦ k - 1`): `π_s(λ_{k-1}) + π_s(λ_k) = 2 k^{2s}`. -/
theorem momentPoly_spec_pred [CharZero K] (s : ℕ) (k : K) :
    (momentPoly K s).eval ((k - 1) * k) + (momentPoly K s).eval (k * (k + 1)) = 2 * k ^ (2 * s) := by
  have := momentPoly_spec (K := K) s (k - 1)
  have e1 : (k - 1) * (k - 1 + 1) = k * (k - 1) := by ring
  have e2 : (k - 1 + 1) * (k - 1 + 2) = k * (k + 1) := by ring
  rw [e1, e2, sub_add_cancel] at this
  rw [mul_comm (k - 1) k] at *
  exact this

theorem momentPoly_ne_zero [CharZero K] (s : ℕ) : momentPoly K s ≠ 0 := by
  intro h
  have := momentMap_momentPoly (K := K) s
  rw [h] at this
  simp [momentMap] at this

theorem natDegree_momentPoly [CharZero K] (s : ℕ) : (momentPoly K s).natDegree = s := by
  have hne := momentPoly_ne_zero (K := K) s
  have := natDegree_momentMap hne
  rw [momentMap_momentPoly, natDegree_C_mul_X_pow _ _ two_ne_zero] at this
  omega

theorem monic_momentPoly [CharZero K] (s : ℕ) : (momentPoly K s).Monic := by
  have hne := momentPoly_ne_zero (K := K) s
  have := coeff_momentMap_top (momentPoly K s)
  rw [momentMap_momentPoly, natDegree_momentPoly, coeff_C_mul, coeff_X_pow_self] at this
  have h2 : (2 : K) * (momentPoly K s).leadingCoeff = 2 * 1 := this.symm
  exact mul_left_cancel₀ two_ne_zero h2

/-- `π_s(0) = 0` for `s ≥ 1` (`y = 0` in the proof of `lem:momentpolynomial`). -/
theorem momentPoly_eval_zero [CharZero K] {s : ℕ} (hs : 1 ≤ s) : (momentPoly K s).eval 0 = 0 := by
  have := momentPoly_spec (K := K) s (-1)
  have h0 : (2 * ((-1 : K) + 1) ^ (2 * s)) = 0 := by
    rw [show ((-1 : K) + 1) = 0 by ring, zero_pow (by omega)]; ring
  rw [h0] at this
  have e1 : ((-1 : K) * (-1 + 1)) = 0 := by ring
  have e2 : ((-1 + 1 : K) * (-1 + 2)) = 0 := by ring
  rw [e1, e2] at this
  have : 2 * (momentPoly K s).eval 0 = 0 := by rw [two_mul]; exact this
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

/-- `π_1 = z` (stated after `lem:momentpolynomial`). -/
theorem momentPoly_one [CharZero K] : momentPoly K 1 = X := by
  symm; apply momentPoly_unique
  intro k; simp; ring

/-- `π_2 = z (z - 1)` (stated after `lem:momentpolynomial`). -/
theorem momentPoly_two [CharZero K] : momentPoly K 2 = X * (X - 1) := by
  symm; apply momentPoly_unique
  intro k; simp; ring

end Moment

end FormalResearch.Racah.LocalCalculus

/-- info: 'FormalResearch.Racah.LocalCalculus.momentMap_bijective_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.momentMap_bijective_even

/-- info: 'FormalResearch.Racah.LocalCalculus.momentPoly_exists_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.momentPoly_exists_unique

/-- info: 'FormalResearch.Racah.LocalCalculus.momentPoly_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.momentPoly_unique

/-- info: 'FormalResearch.Racah.LocalCalculus.natDegree_momentPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.natDegree_momentPoly

/-- info: 'FormalResearch.Racah.LocalCalculus.monic_momentPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.monic_momentPoly

/-- info: 'FormalResearch.Racah.LocalCalculus.momentPoly_eval_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.momentPoly_eval_zero

/-- info: 'FormalResearch.Racah.LocalCalculus.momentPoly_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.momentPoly_one

/-- info: 'FormalResearch.Racah.LocalCalculus.momentPoly_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.momentPoly_two
