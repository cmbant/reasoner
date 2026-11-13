module

public import FormalResearch.Racah.P2HahnRec

/-!
# Exact finite part of the beta--binomial polar realization (Weyl P2)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `sec:polartransmutation` and Appendix
`app:beta-polar` (`eq:BernsteinHahnJacobi`, `eq:singularvaluesgeneral`, `eq:physicalsingularvalues`).

## What is proved (finite, exact, independent of `L²` and of the Jacobi limit)

* `bernstein_moment`: `∑_u b_u^D(t) (-u)_k = (-D)_k t^k`, the identity used in the appendix.
* `bernstein_hahn_jacobi`: `eq:BernsteinHahnJacobi` for `0 ≤ n ≤ D`,
  `∑_{u=0}^D b_u^D(t) Q_n(u;α,β,D) = ∑_{k=0}^n (-n)_k (n+α+β+1)_k/((α+1)_k k!) t^k`; the right side is the
  terminating `₂F₁(-n, n+α+β+1; α+1; t) = (n!/(α+1)_n) P_n^{(α,β)}(1-2t)` (Mathlib has no Jacobi
  polynomials, so the identification with `P_n^{(α,β)}` is the classical hypergeometric representation,
  taken as the definition of the Jacobi side).
* `singularSq_physical`: `eq:physicalsingularvalues`: with `α+β = 2M`, `D = N-M-1`,
  `s_n² = D^{\underline n}/(D+α+β+2)_n = ∏_{r=M+1}^{M+n} (N-r)/(N+r)`.
* `singularSq_pos`: all `s_n` are positive for `n ≤ D` (`eq:singularvaluesgeneral`).

Not covered: the `L²(dν_H)` statements (the singular-pair relation `T_D J_n = s_n H_n`, the polar
unitary `𝖴_D`, the gauges `𝖦_c, 𝖦_d` and `eq:SNpolar`), which involve the beta integrals and the
continuum Wigner `d`-functions.
-/

@[expose] public section

namespace FormalResearch.Racah

open Polynomial

/-- Bernstein basis `b_u^D(t) = C(D,u) t^u (1-t)^{D-u}`. -/
noncomputable def bern (D u : ℕ) (t : ℝ) : ℝ := (D.choose u : ℝ) * t ^ u * (1 - t) ^ (D - u)

/-- `∑_u b_u^D(t) C(u,k) = C(D,k) t^k`. -/
lemma bern_binom (D k : ℕ) (t : ℝ) :
    ∑ u ∈ Finset.range (D + 1), bern D u t * (u.choose k : ℝ) = (D.choose k : ℝ) * t ^ k := by
  rcases lt_or_ge D k with hk | hk
  · have h1 : D.choose k = 0 := Nat.choose_eq_zero_of_lt hk
    rw [h1]
    simp only [Nat.cast_zero, zero_mul]
    refine Finset.sum_eq_zero fun u hu => ?_
    have : u < k := by simp only [Finset.mem_range] at hu; omega
    rw [Nat.choose_eq_zero_of_lt this]; simp
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [show k + m + 1 = k + (m + 1) by ring, Finset.sum_range_add]
    have h0 : ∑ x ∈ Finset.range k, bern (k + m) x t * ((x.choose k : ℕ) : ℝ) = 0 := by
      refine Finset.sum_eq_zero fun u hu => ?_
      have : u < k := by simpa using hu
      rw [Nat.choose_eq_zero_of_lt this]; simp
    rw [h0, zero_add]
    have hterm : ∀ v ∈ Finset.range (m + 1),
        bern (k + m) (k + v) t * (((k + v).choose k : ℕ) : ℝ) =
          ((k + m).choose k : ℝ) * t ^ k * ((m.choose v : ℝ) * t ^ v * (1 - t) ^ (m - v)) := by
      intro v hv
      have hvm : v ≤ m := by simpa [Nat.lt_succ_iff] using hv
      unfold bern
      have hc := Nat.choose_mul (n := k + m) (k := k + v) (s := k) (by omega)
      have e1 : k + m - k = m := by omega
      have e2 : k + v - k = v := by omega
      rw [e1, e2] at hc
      have hc' : (((k + m).choose (k + v) : ℕ) : ℝ) * (((k + v).choose k : ℕ) : ℝ) =
          (((k + m).choose k : ℕ) : ℝ) * ((m.choose v : ℕ) : ℝ) := by exact_mod_cast hc
      have e3 : k + m - (k + v) = m - v := by omega
      rw [e3, pow_add]
      calc ((k + m).choose (k + v) : ℝ) * (t ^ k * t ^ v) * (1 - t) ^ (m - v) *
            (((k + v).choose k : ℕ) : ℝ)
          = ((((k + m).choose (k + v) : ℕ) : ℝ) * (((k + v).choose k : ℕ) : ℝ)) *
              (t ^ k * t ^ v) * (1 - t) ^ (m - v) := by ring
        _ = _ := by rw [hc']; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hb : ∑ v ∈ Finset.range (m + 1), (m.choose v : ℝ) * t ^ v * (1 - t) ^ (m - v) = 1 := by
      have h := add_pow t (1 - t) m
      rw [add_sub_cancel, one_pow] at h
      calc ∑ v ∈ Finset.range (m + 1), (m.choose v : ℝ) * t ^ v * (1 - t) ^ (m - v)
          = ∑ v ∈ Finset.range (m + 1), t ^ v * (1 - t) ^ (m - v) * (m.choose v : ℝ) :=
            Finset.sum_congr rfl fun v _ => by ring
        _ = 1 := h.symm
    rw [hb]; ring

/-- The Bernstein moment identity `∑_u b_u^D(t) (-u)_k = (-D)_k t^k`. -/
theorem bernstein_moment (D k : ℕ) (t : ℝ) :
    ∑ u ∈ Finset.range (D + 1), bern D u t * (ascPochhammer ℝ k).eval (-(u : ℝ)) =
      (ascPochhammer ℝ k).eval (-(D : ℝ)) * t ^ k := by
  have key : ∀ x : ℕ, (ascPochhammer ℝ k).eval (-(x : ℝ)) =
      (-1 : ℝ) ^ k * (k.factorial : ℝ) * (x.choose k : ℝ) := by
    intro x
    rw [ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose]
    push_cast; ring
  simp only [key]
  have := bern_binom D k t
  calc ∑ u ∈ Finset.range (D + 1),
        bern D u t * ((-1 : ℝ) ^ k * (k.factorial : ℝ) * (u.choose k : ℝ))
      = (-1 : ℝ) ^ k * (k.factorial : ℝ) *
          ∑ u ∈ Finset.range (D + 1), bern D u t * (u.choose k : ℝ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun u _ => ?_; ring
    _ = _ := by rw [this]; ring

/-- **`eq:BernsteinHahnJacobi`**: for `n ≤ D`,
`∑_u b_u^D(t) Q_n(u;α,β,D) = ∑_{k=0}^n (-n)_k (n+α+β+1)_k/((α+1)_k k!) t^k`
(the terminating `₂F₁` of `(n!/(α+1)_n) P_n^{(α,β)}(1-2t)`). -/
theorem bernstein_hahn_jacobi (α β D n : ℕ) (hn : n ≤ D) (t : ℝ) :
    ∑ u ∈ Finset.range (D + 1), bern D u t * hahnQ α β D n u =
      ∑ k ∈ Finset.range (n + 1),
        (ascPochhammer ℝ k).eval (-(n : ℝ)) * (ascPochhammer ℝ k).eval ((n : ℝ) + α + β + 1) /
          ((ascPochhammer ℝ k).eval ((α : ℝ) + 1) * (k.factorial : ℝ)) * t ^ k := by
  have h1 : ∀ u, bern D u t * hahnQ α β D n u =
      ∑ k ∈ Finset.range (n + 1), hc α β D n k * (bern D u t * (ascPochhammer ℝ k).eval (-(u : ℝ))) := by
    intro u
    rw [hahnQ_eq_hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := by simp only [Finset.mem_range] at hk; omega
  rw [← Finset.mul_sum, bernstein_moment]
  unfold hc
  have hD := D_ne D k (by omega)
  have hA := (al_pos α k).ne'
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- `s_n² = D^{\\underline n}/(D+α+β+2)_n` (`eq:singularvaluesgeneral`). -/
noncomputable def singularSq (α β D n : ℕ) : ℝ :=
  (descPochhammer ℝ n).eval (D : ℝ) / (ascPochhammer ℝ n).eval ((D : ℝ) + α + β + 2)

lemma ascPoch_eval_prod (n : ℕ) (x : ℝ) :
    (ascPochhammer ℝ n).eval x = ∏ j ∈ Finset.range n, (x + j) := by
  induction n with
  | zero => simp
  | succ n ih => rw [ascPochhammer_succ_eval, ih, Finset.prod_range_succ]

/-- **`eq:physicalsingularvalues`**: for `α+β = 2M` and `D = N-M-1`,
`s_{L-M}² = ∏_{r=M+1}^{L} (N-r)/(N+r)`, `L = M+n` (`r = M+k+1`, `0 ≤ k < n`). -/
theorem singularSq_physical (α β D n : ℕ) (M N : ℝ) (hM : (α : ℝ) + β = 2 * M)
    (hN : N = (D : ℝ) + M + 1) :
    singularSq α β D n = ∏ k ∈ Finset.range n, ((N - (M + k + 1)) / (N + (M + k + 1))) := by
  unfold singularSq
  rw [descPochhammer_eval_eq_prod_range, ascPoch_eval_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have e1 : (D : ℝ) - k = N - (M + k + 1) := by rw [hN]; ring
  have e2 : (D : ℝ) + α + β + 2 + k = N + (M + k + 1) := by
    have : (α : ℝ) + β = 2 * M := hM
    rw [hN]; linarith
  rw [e1, e2]

/-- All singular values are positive for `n ≤ D`. -/
theorem singularSq_pos (α β D n : ℕ) (hn : n ≤ D) : 0 < singularSq α β D n := by
  unfold singularSq
  rw [descPochhammer_eval_eq_prod_range, ascPoch_eval_prod]
  apply div_pos
  · apply Finset.prod_pos
    intro k hk
    have : k < n := by simpa using hk
    have : (k : ℝ) + 1 ≤ D := by exact_mod_cast (by omega : k + 1 ≤ D)
    linarith
  · apply Finset.prod_pos
    intro k _
    positivity

/-- info: 'FormalResearch.Racah.bernstein_hahn_jacobi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bernstein_hahn_jacobi

/-- info: 'FormalResearch.Racah.singularSq_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms singularSq_physical

/-- info: 'FormalResearch.Racah.singularSq_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms singularSq_pos

end FormalResearch.Racah
