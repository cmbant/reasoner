module

public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityApprox
public import FormalResearch.ModularBootstrap.TwoLevel.WindowOptimumLimit

/-!
# Ideal windows through the Clark nodes (`virasoro_two_level.tex`, `gt:2.6`)

* `IdealDatum.win_airyZero`, `win_nonneg_of_le`, `win_pos`: sign of `Re F_δ`, including the removable values at the
  Airy zeros `a_j` (`F_δ(a_j) E_j(a_j)² = Ai'(a_j)² N_δ(a_j)` with `E_j = ∏_{k ≠ j}(· - a_k)`);
* `IdealDatum.win_succ`: the splitting identity `F_{K+1}(u)(u - a_{K+1})² = F_K(u)(u - s_{K+1})²`;
* `clarkDatum α p q m K`: the datum with zeros `p, q`, sites `z_k` (`3 ≤ k ≤ K`) except `a_m` at `k = m`
  (so that the `m`-th pair is ideal), with `clarkDatum_adm` (admissibility for `TwoZeroApprox`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty
open FormalResearch.ModularBootstrap.Upper.Rigidity

lemma airyAi'_airyZero_ne {j : ℕ} (hj : 1 ≤ j) : airyAi' (airyZero j) ≠ 0 := by
  have := airyAi'_airyNode_ne (j - 1)
  unfold airyNode at this
  rwa [Nat.sub_add_cancel hj] at this

lemma clarkNode_neg_of_two_le (α : ℝ) {n : ℕ} (hn : 2 ≤ n) : clarkNode α n < 0 := by
  rcases hn.eq_or_lt with rfl | h
  · exact clarkNode_two_lt_zero α
  · exact (clarkNode_lt_of_lt (n := 2) (m := n) (by norm_num) h α).trans (clarkNode_two_lt_zero α)

lemma windowDr_succ (K : ℕ) (x : ℝ) : windowDr (K + 1) x = windowDr K x * (x - airyZero (K + 1)) := by
  unfold windowDr
  rw [Finset.prod_Icc_succ_top (by omega)]

namespace IdealDatum

variable (δ : IdealDatum)

lemma continuous_Nr : Continuous δ.Nr := by
  unfold Nr; fun_prop

lemma windowDr_eq_zero_iff {x : ℝ} : windowDr δ.K x = 0 ↔ ∃ j ∈ Finset.Icc 1 δ.K, x = airyZero j := by
  unfold windowDr
  rw [Finset.prod_eq_zero_iff]
  refine exists_congr fun j => and_congr_right fun _ => ?_
  exact sub_eq_zero

lemma prod_erase_ne {j : ℕ} (hj : j ∈ Finset.Icc 1 δ.K) :
    ∏ k ∈ (Finset.Icc 1 δ.K).erase j, (airyZero j - airyZero k) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun k hk => ?_
  obtain ⟨hkj, hk'⟩ := Finset.mem_erase.mp hk
  have hj1 := (Finset.mem_Icc.mp hj).1
  have hk1 := (Finset.mem_Icc.mp hk').1
  intro h
  exact hkj (airyZero_inj hk1 hj1 (sub_eq_zero.mp h).symm)

/-- The removable value of `Re F_δ` at an Airy zero `a_j`, `j ≤ K`. -/
lemma win_airyZero {j : ℕ} (hj : j ∈ Finset.Icc 1 δ.K) :
    δ.win (airyZero j) * (∏ k ∈ (Finset.Icc 1 δ.K).erase j, (airyZero j - airyZero k)) ^ 2 =
      airyAi' (airyZero j) ^ 2 * δ.Nr (airyZero j) := by
  set a := airyZero j with ha
  set E : ℝ → ℝ := fun x => ∏ k ∈ (Finset.Icc 1 δ.K).erase j, (x - airyZero k) with hE
  set B : ℝ → ℝ := dslope airyAi a with hB
  have hBc : Continuous B := by
    rw [← continuousOn_univ]
    exact (continuousOn_dslope Filter.univ_mem).2
      ⟨differentiable_airyAi.continuous.continuousOn, differentiable_airyAi.differentiableAt⟩
  have hAi : ∀ x, airyAi x = (x - a) * B x := by
    intro x
    have := sub_smul_dslope airyAi a x
    rw [show airyAi a = 0 from airyAi_airyZero j, sub_zero, smul_eq_mul] at this
    exact this.symm
  have hD : ∀ x, windowDr δ.K x = (x - a) * E x := by
    intro x; unfold windowDr; rw [← Finset.mul_prod_erase _ _ hj]
  have hid : ∀ x, x ≠ a → δ.win x * E x ^ 2 = B x ^ 2 * δ.Nr x := by
    intro x hx
    have h := δ.win_spec x
    rw [hD, hAi x] at h
    have hx' : (x - a) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hx)
    apply mul_left_cancel₀ hx'
    linear_combination h
  have hEc : Continuous E := by rw [hE]; fun_prop
  have hext : (fun x => δ.win x * E x ^ 2) = fun x => B x ^ 2 * δ.Nr x :=
    Continuous.ext_on (dense_compl_singleton a) (δ.continuous_win.mul (hEc.pow 2))
      ((hBc.pow 2).mul δ.continuous_Nr) (fun x hx => hid x hx)
  have := congrFun hext a
  simp only [hB, dslope_same, deriv_airyAi] at this
  exact this

lemma win_nonneg_of_le {x : ℝ} (hx : x ≤ δ.q) (hqp : δ.q < δ.p) : 0 ≤ δ.win x := by
  have hNr : 0 ≤ δ.Nr x := by
    unfold Nr
    refine mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)) ?_
    exact Finset.prod_nonneg fun k _ => sq_nonneg _
  by_cases hD : windowDr δ.K x = 0
  · obtain ⟨j, hj, rfl⟩ := (δ.windowDr_eq_zero_iff).1 hD
    have h := δ.win_airyZero hj
    have hE := δ.prod_erase_ne hj
    have hE2 : 0 < (∏ k ∈ (Finset.Icc 1 δ.K).erase j, (airyZero j - airyZero k)) ^ 2 := by positivity
    have : 0 ≤ δ.win (airyZero j) * (∏ k ∈ (Finset.Icc 1 δ.K).erase j, (airyZero j - airyZero k)) ^ 2 := by
      rw [h]; positivity
    exact nonneg_of_mul_nonneg_left this hE2
  · have h := δ.win_spec x
    have hD2 : 0 < windowDr δ.K x ^ 2 := by positivity
    have : 0 ≤ δ.win x * windowDr δ.K x ^ 2 := by rw [h]; positivity
    exact nonneg_of_mul_nonneg_left this hD2

lemma win_pos {x : ℝ} (hNr : 0 < δ.Nr x) (hAi : airyAi x = 0 → ∃ j ∈ Finset.Icc 1 δ.K, x = airyZero j) :
    0 < δ.win x := by
  by_cases hD : windowDr δ.K x = 0
  · obtain ⟨j, hj, rfl⟩ := (δ.windowDr_eq_zero_iff).1 hD
    have h := δ.win_airyZero hj
    have hE := δ.prod_erase_ne hj
    have hE2 : 0 < (∏ k ∈ (Finset.Icc 1 δ.K).erase j, (airyZero j - airyZero k)) ^ 2 := by positivity
    have h1 := airyAi'_airyZero_ne (Finset.mem_Icc.mp hj).1
    have : 0 < δ.win (airyZero j) * (∏ k ∈ (Finset.Icc 1 δ.K).erase j, (airyZero j - airyZero k)) ^ 2 := by
      rw [h]; positivity
    exact pos_of_mul_pos_left this hE2.le
  · have h := δ.win_spec x
    have hD2 : 0 < windowDr δ.K x ^ 2 := by positivity
    have hA : airyAi x ≠ 0 := fun h0 => hD ((δ.windowDr_eq_zero_iff).2 (hAi h0))
    have : 0 < δ.win x * windowDr δ.K x ^ 2 := by rw [h]; positivity
    exact pos_of_mul_pos_left this hD2.le

end IdealDatum

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.IdealDatum.win_airyZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IdealDatum.win_airyZero

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.IdealDatum.win_nonneg_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IdealDatum.win_nonneg_of_le

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.IdealDatum.win_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IdealDatum.win_pos

end FormalResearch.ModularBootstrap.TwoLevel
