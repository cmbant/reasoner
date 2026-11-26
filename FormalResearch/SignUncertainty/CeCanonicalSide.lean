module

public import FormalResearch.SignUncertainty.HbZeroEnum
public import FormalResearch.SignUncertainty.ShellLaplaceZeros

/-!
# Side clauses of `thm:ce-canonical-iff` (`ce_canonical_iff.tex`)

* `ShellHBData.S_zero`, `ShellHBData.tm_eq_hbNode`: the prescribed sites are the top `m` zeros of
  `N = P Ai + Q Ai'`, so `t_m = D.tm` for the zero enumeration `t`.
* `hbNodeWeight_pos`, `hbTauN_lt_tm`: for `m ≥ 2` the node weights `ω_n` of `eq:hb-node-bound` are positive
  (`gt:1.0pp`, `airyPQ_zero_weight_pos`) and so `τ_N < t_m` (`τ_N` is a positive-weight average of
  `t_m > t_{m+1}, …, t_{m+e}`).
-/

@[expose] public section

open Complex Polynomial Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

lemma nodeZero_iff (D : ShellHBData) (x : ℝ) :
    airyPQN D.P D.Q (x : ℂ) = 0 ↔ at47_Nf D.P D.Q x = 0 := by
  rw [airyPQN_ofReal, Complex.ofReal_eq_zero]
  rfl

/-- Every prescribed site is a zero of `N` (`G · ∏(z - s) = ±N²` at `z = s`). -/
lemma ShellHBData.S_zero (D : ShellHBData) {s : ℝ} (hs : s ∈ D.S) : airyPQN D.P D.Q (s : ℂ) = 0 := by
  have h := D.G_prod_eq (s : ℂ)
  have hpr : at47_pr D.S (s : ℂ) = 0 := by
    unfold at47_pr
    exact Finset.prod_eq_zero hs (sub_self _)
  rw [hpr, mul_zero] at h
  have hc : (((-1 : ℝ) ^ D.S.card : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact pow_ne_zero _ (by norm_num)
  have h2 : airyPQN D.P D.Q (s : ℂ) ^ 2 = 0 := by
    rcases mul_eq_zero.1 h.symm with h1 | h1
    · exact absurd h1 hc
    · exact h1
  exact pow_eq_zero_iff (two_ne_zero) |>.1 h2

/-- The prescribed sites are the top `m` zeros: `t_m = D.tm` for the zero enumeration `t`. -/
theorem ShellHBData.tm_eq_hbNode (D : ShellHBData) {t : ℕ → ℝ} (ht : IsHbZeroEnum D.P D.Q t) :
    D.tm = hbNode t D.S.card := by
  obtain ⟨j, hj⟩ := (ht.2 D.tm).1 ((nodeZero_iff D D.tm).1 (D.S_zero D.tm_mem))
  have hS : D.S = (Finset.range (j + 1)).image t := by
    ext x
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := (ht.2 x).1 ((nodeZero_iff D x).1 (D.S_zero hx))
      refine ⟨i, ?_, hi⟩
      have h1 : t j ≤ t i := by rw [hj, hi]; exact D.tm_min x hx
      by_contra hij
      exact absurd (ht.1 (by omega : j < i)) (not_lt.mpr h1)
    · rintro ⟨i, hi, rfl⟩
      by_contra hxS
      have h1 := D.S_top (t i) ((nodeZero_iff D _).2 ((ht.2 _).2 ⟨i, rfl⟩)) hxS D.tm D.tm_mem
      have h2 : t j ≤ t i := ht.1.antitone (by omega)
      linarith
  have hcard : D.S.card = j + 1 := by
    rw [hS, Finset.card_image_of_injective _ ht.1.injective, Finset.card_range]
  unfold hbNode
  rw [hcard]
  simpa using hj.symm

lemma ShellHBData.Q_ne_zero_of_two_le (D : ShellHBData) (hm : 2 ≤ D.S.card) : D.Q ≠ 0 := by
  rcases D.m_eq with ⟨_, h1⟩ | ⟨h, _⟩
  · omega
  · exact h

/-- `eq:hb-node-bound`: the node weights `ω_n`, `n ∈ T_0 = {m, …, m + ⌊m/2⌋}`, are positive. -/
theorem hbNodeWeight_pos (D : ShellHBData) {t : ℕ → ℝ} (ht : IsHbZeroEnum D.P D.Q t) (hm : 2 ≤ D.S.card)
    {n : ℕ} (hn : n ∈ Finset.Icc D.S.card (D.S.card + D.S.card / 2)) :
    0 < hbNodeWeight D.P D.Q t (Finset.Icc D.S.card (D.S.card + D.S.card / 2)) n := by
  have hQ := D.Q_ne_zero_of_two_le hm
  unfold hbNodeWeight
  have hz : airyPQN D.P D.Q (hbNode t n : ℂ) = 0 :=
    (nodeZero_iff D _).2 ((ht.2 _).2 ⟨n - 1, rfl⟩)
  have hD := (airyPQ_zero_weight_pos D.hHB hQ hz).1
  refine div_pos hD (Finset.prod_pos fun k hk => ?_)
  have hk' := Finset.mem_erase.1 hk
  have hn1 := (Finset.mem_Icc.1 hn).1
  have hk1 := (Finset.mem_Icc.1 hk'.2).1
  have hne : hbNode t n ≠ hbNode t k := by
    unfold hbNode
    intro h
    have := ht.1.injective h
    omega
  have h0 : hbNode t n - hbNode t k ≠ 0 := sub_ne_zero.2 hne
  positivity

/-- `eq:hb-node-bound`: `τ_N < t_m` for `m ≥ 2` (with `t_{m+e} < τ_N`, `lem:airy-node-square`, this is
`τ_N ∈ (t_{m+e}, t_m)`). -/
theorem hbTauN_lt_tm (D : ShellHBData) {t : ℕ → ℝ} (ht : IsHbZeroEnum D.P D.Q t) (hm : 2 ≤ D.S.card) :
    hbTauN D t < D.tm := by
  unfold hbTauN hbNodeSquareBound
  set T := Finset.Icc D.S.card (D.S.card + D.S.card / 2) with hT
  have hw : ∀ n ∈ T, 0 < hbNodeWeight D.P D.Q t T n := fun n hn => hbNodeWeight_pos D ht hm hn
  have hmT : D.S.card ∈ T := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hm1T : D.S.card + 1 ∈ T := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hsum : 0 < ∑ n ∈ T, hbNodeWeight D.P D.Q t T n := Finset.sum_pos hw ⟨_, hmT⟩
  rw [div_lt_iff₀ hsum, Finset.mul_sum]
  refine Finset.sum_lt_sum (fun n hn => ?_) ⟨D.S.card + 1, hm1T, ?_⟩
  · have hn1 := (Finset.mem_Icc.1 hn).1
    have h : hbNode t n ≤ D.tm := by
      rw [D.tm_eq_hbNode ht]
      unfold hbNode
      exact ht.1.antitone (by omega)
    nlinarith [hw n hn]
  · have h : hbNode t (D.S.card + 1) < D.tm := by
      rw [D.tm_eq_hbNode ht]
      unfold hbNode
      exact ht.1 (by omega)
    nlinarith [hw _ hm1T]

/-- info: 'FormalResearch.SignUncertainty.ShellHBData.tm_eq_hbNode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ShellHBData.tm_eq_hbNode

/-- info: 'FormalResearch.SignUncertainty.hbNodeWeight_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hbNodeWeight_pos

/-- info: 'FormalResearch.SignUncertainty.hbTauN_lt_tm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hbTauN_lt_tm

end FormalResearch.SignUncertainty
