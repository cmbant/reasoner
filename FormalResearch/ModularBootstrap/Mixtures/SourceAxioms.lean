module

public import FormalResearch.ModularBootstrap.Mixtures.ShiftAsymptotics
public import FormalResearch.ModularBootstrap.Mixtures.CommonSource

/-!
# The axioms `(W1)`-`(W4)` for an atomic source: the structure `SourceAxioms`

`SourceAxioms src c'` is the exact analogue of `WeightAxioms.FixedWeightAxioms prob c'` with the Cardy weight, test
class, norm, strict/weak feasibility and complex continuation of the source `src` (`ShiftSource`) in place of those of a
`FixedWeightProblem`; `SourceUniformAxioms src` is the `c'`-uniform version (`FixedWeightUniformAxioms`).

The fixed-weight case is the special case `ShiftSource.ofProblem prob`
(`FixedWeightAxioms.toSourceAxioms`, `FixedWeightUniformAxioms.toSourceUniformAxioms`): the new structure
specialises to the old one, so downstream packages (the lower chain, Proposition P, Lemma Q ...) can be re-run against
`SourceAxioms` and recover the old statements for products.  The proof of the axioms for a *common source*
(`pmix_weight_c`) is in `Mixtures/WeightAxioms.lean`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.WeightAxioms FormalResearch.ModularBootstrap.Bessel
  FormalResearch.ModularBootstrap.ComplexBessel

/-- Fixed-weight axioms `(W1)-(W4)` (`lower_o1_two_edge.tex` §J1) for a source at the parameter `c' > 0`
(`a = c'/12`); the fields are those of `FixedWeightAxioms`. -/
structure SourceAxioms (src : ShiftSource) (c' : ℝ) where
  hc'_pos : 0 < c'
  ha_shift : src.ShiftLE (c' / 12)
  C_1 : ℝ
  hC1_pos : 0 < C_1
  C_e : ℝ
  hCe_pos : 0 < C_e
  p_e : ℝ
  hp_e_nn : 0 ≤ p_e
  c_low : ℝ
  hc_low_pos : 0 < c_low
  p_0 : ℝ
  hp_0_nn : 0 ≤ p_0
  C_K : ℝ
  hCK_pos : 0 < C_K
  p_K : ℝ
  hp_K_nn : 0 ≤ p_K
  c_band : ℝ
  hc_band_pos : 0 < c_band
  C_up : ℝ
  hCup_pos : 0 < C_up
  p_u : ℝ
  hp_u_nn : 0 ≤ p_u
  r_1 : ℝ
  hr1_pos : 0 < r_1
  hr1_le : r_1 ≤ xiStar / 2
  Q_star : ℂ → ℂ
  c_Q : ℝ
  C_Q : ℝ
  hcQ_pos : 0 < c_Q
  hcQ_le : c_Q ≤ C_Q
  C_V : ℝ
  hCV_nn : 0 ≤ C_V
  /-- `(W1)` norm bound. -/
  w1_sup : ∀ {g : ℝ → ℝ}, TestClass src (c' / 12) g →
    ∀ {t : ℝ}, 0 ≤ t → |g t| ≤ C_1 * src.cardyNorm (c' / 12) g
  /-- `(W1)` strip continuation. -/
  w1_strip : ∀ {g : ℝ → ℝ}, TestClass src (c' / 12) g →
    ∃ G : ℂ → ℂ,
      ContinuousOn G {b : ℂ | |b.im| ≤ 1 / 2} ∧
      DifferentiableOn ℂ G {b : ℂ | |b.im| < 1 / 2} ∧
      (∀ x : ℝ, G (x : ℂ) = (g (c' * x ^ 2 / 3) : ℂ)) ∧
      ∀ {b : ℂ}, |b.im| ≤ 1 / 2 → ‖G b‖ ≤ C_e * c' ^ p_e * src.cardyNorm (c' / 12) g
  /-- `(W2)` strict positivity. -/
  w2_pos : ∀ {t : ℝ}, 0 < t → 0 < src.cardyV (c' / 12) t
  /-- `(W2)` small-`t` floor. -/
  w2_floor : ∀ {t : ℝ}, 0 < t → t ≤ 4 / c' → c_low * t ^ p_0 ≤ src.cardyV (c' / 12) t
  /-- `(W2)` lower comparison on `[4/c', ∞)`. -/
  w2_ker_le : ∀ {t : ℝ}, 4 / c' ≤ t →
    kernelK src.w (c' / 12) t ≤ C_K * c' ^ p_K * src.cardyV (c' / 12) t
  /-- `(W2)` band comparison on `[ξ̄ c', ∞)`. -/
  w2_band : ∀ {t : ℝ}, xiBar * c' ≤ t →
    c_band * kernelK src.w (c' / 12) t ≤ src.cardyV (c' / 12) t
  /-- `(W2)` upper comparison on `(0, ξ̄ c']`. -/
  w2_up : ∀ {t : ℝ}, 0 < t → t ≤ xiBar * c' →
    src.cardyV (c' / 12) t ≤ C_up * (1 + c' ^ p_u) * kernelK src.w (c' / 12) t
  /-- `(W3)` `Q_*` holomorphic on `Re b > 0`. -/
  w3_Q_holo : DifferentiableOn ℂ Q_star {b : ℂ | 0 < b.re}
  /-- `(W3)` zero-free on the disc. -/
  w3_Q_ne_zero : ∀ {b : ℂ}, b ∈ Metric.closedBall (xiStar : ℂ) r_1 → Q_star b ≠ 0
  /-- `(W3)` real and bounded above and below on `[ξ_*/2, ∞)`. -/
  w3_Q_real_bounds : ∀ {x : ℝ}, xiStar / 2 ≤ x →
    (Q_star (x : ℂ)).im = 0 ∧ c_Q ≤ (Q_star (x : ℂ)).re ∧ (Q_star (x : ℂ)).re ≤ C_Q
  /-- `(W3)` real Cardy asymptote. -/
  w3_real_asymp : ∀ {x : ℝ}, xiStar / 2 ≤ x →
    |src.cardyV (c' / 12) (c' * x ^ 2 / 3) /
        ((2 * x) ^ (src.w - 1) * besselAs (c' * (2 * Real.pi * x / 3))) -
      (Q_star (x : ℂ)).re| ≤ C_V / c'
  /-- `(W3)` entire complex continuation of `V`. -/
  w3_complex_holo : Differentiable ℂ (fun b : ℂ => src.cardyVC (c' / 12) ((c' : ℂ) * b ^ 2 / 3)) ∧
    ∀ x : ℝ, src.cardyVC (c' / 12) (x : ℂ) = (src.cardyV (c' / 12) x : ℂ)
  /-- `(W3)` complex-disc asymptote. -/
  w3_complex_asymp : ∀ {b : ℂ}, b ∈ Metric.closedBall (xiStar : ℂ) r_1 →
    ‖src.cardyVC (c' / 12) ((c' : ℂ) * b ^ 2 / 3) /
        ((2 * b) ^ (src.w - 1) * asC ((c' : ℂ) * tipL b)) -
      Q_star b‖ ≤ C_V / c'
  /-- `(W4)` vacuum sign. -/
  w4_vac : ∀ {T : ℝ} {g : ℝ → ℝ}, src.IsWeaklyFeasible (c' / 12) T g →
    ∫ t in Ioi (0 : ℝ), g t * src.cardyV (c' / 12) t ≤ 0

/-- Uniform-in-`c'` version of `SourceAxioms`. -/
structure SourceUniformAxioms (src : ShiftSource) where
  c₀ : ℝ
  hc₀_pos : 0 < c₀
  C_1 : ℝ
  hC1_pos : 0 < C_1
  C_e : ℝ
  hCe_pos : 0 < C_e
  p_e : ℝ
  hp_e_nn : 0 ≤ p_e
  c_low : ℝ
  hc_low_pos : 0 < c_low
  p_0 : ℝ
  hp_0_nn : 0 ≤ p_0
  C_K : ℝ
  hCK_pos : 0 < C_K
  p_K : ℝ
  hp_K_nn : 0 ≤ p_K
  c_band : ℝ
  hc_band_pos : 0 < c_band
  C_up : ℝ
  hCup_pos : 0 < C_up
  p_u : ℝ
  hp_u_nn : 0 ≤ p_u
  r_1 : ℝ
  hr1_pos : 0 < r_1
  hr1_le : r_1 ≤ xiStar / 2
  Q_star : ℂ → ℂ
  c_Q : ℝ
  C_Q : ℝ
  hcQ_pos : 0 < c_Q
  hcQ_le : c_Q ≤ C_Q
  C_V : ℝ
  hCV_nn : 0 ≤ C_V
  axioms_at : ∀ {c' : ℝ}, c₀ ≤ c' → SourceAxioms src c'
  uniform_C_1 : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (axioms_at hc').C_1 = C_1
  uniform_C_e : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (axioms_at hc').C_e = C_e
  uniform_p_e : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (axioms_at hc').p_e = p_e
  uniform_c_low : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (axioms_at hc').c_low = c_low
  uniform_p_0 : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (axioms_at hc').p_0 = p_0
  uniform_C_K : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (axioms_at hc').C_K = C_K
  uniform_p_K : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (axioms_at hc').p_K = p_K
  uniform_c_band : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (axioms_at hc').c_band = c_band
  uniform_C_up : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (axioms_at hc').C_up = C_up
  uniform_p_u : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (axioms_at hc').p_u = p_u
  uniform_r_1 : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (axioms_at hc').r_1 = r_1
  uniform_Q_star : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (axioms_at hc').Q_star = Q_star
  uniform_c_Q : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (axioms_at hc').c_Q = c_Q
  uniform_C_Q : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (axioms_at hc').C_Q = C_Q
  uniform_C_V : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (axioms_at hc').C_V = C_V

/-! ### The fixed-weight axioms are the special case of products -/

/-- **Bridge**: `FixedWeightAxioms prob c'` gives `SourceAxioms (ofProblem prob) c'` (same constants). -/
noncomputable def _root_.FormalResearch.ModularBootstrap.WeightAxioms.FixedWeightAxioms.toSourceAxioms
    {prob : FixedWeightProblem} {c' : ℝ} (W : FixedWeightAxioms prob c') :
    SourceAxioms (ShiftSource.ofProblem prob) c' where
  hc'_pos := W.hc'_pos
  ha_shift := (ofProblem_shiftLE_iff prob).mpr W.ha_shift
  C_1 := W.C_1
  hC1_pos := W.hC1_pos
  C_e := W.C_e
  hCe_pos := W.hCe_pos
  p_e := W.p_e
  hp_e_nn := W.hp_e_nn
  c_low := W.c_low
  hc_low_pos := W.hc_low_pos
  p_0 := W.p_0
  hp_0_nn := W.hp_0_nn
  C_K := W.C_K
  hCK_pos := W.hCK_pos
  p_K := W.p_K
  hp_K_nn := W.hp_K_nn
  c_band := W.c_band
  hc_band_pos := W.hc_band_pos
  C_up := W.C_up
  hCup_pos := W.hCup_pos
  p_u := W.p_u
  hp_u_nn := W.hp_u_nn
  r_1 := W.r_1
  hr1_pos := W.hr1_pos
  hr1_le := W.hr1_le
  Q_star := W.Q_star
  c_Q := W.c_Q
  C_Q := W.C_Q
  hcQ_pos := W.hcQ_pos
  hcQ_le := W.hcQ_le
  C_V := W.C_V
  hCV_nn := W.hCV_nn
  w1_sup := fun {g} hg {t} ht => W.w1_sup ((ofProblem_testClass_iff prob).mp hg) ht
  w1_strip := fun {g} hg => W.w1_strip ((ofProblem_testClass_iff prob).mp hg)
  w2_pos := fun {t} ht => W.w2_pos ht
  w2_floor := fun {t} ht h4 => W.w2_floor ht h4
  w2_ker_le := fun {t} ht => W.w2_ker_le ht
  w2_band := fun {t} ht => W.w2_band ht
  w2_up := fun {t} ht h => W.w2_up ht h
  w3_Q_holo := W.w3_Q_holo
  w3_Q_ne_zero := fun {b} hb => W.w3_Q_ne_zero hb
  w3_Q_real_bounds := fun {x} hx => W.w3_Q_real_bounds hx
  w3_real_asymp := fun {x} hx => W.w3_real_asymp hx
  w3_complex_holo := by
    have h : ∀ b : ℂ, (ShiftSource.ofProblem prob).cardyVC (c' / 12) ((c' : ℂ) * b ^ 2 / 3) =
        cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) := fun b => ofProblem_cardyVC prob _ _
    refine ⟨?_, fun x => ?_⟩
    · simpa only [h] using W.w3_complex_holo.1
    · rw [ofProblem_cardyVC]; exact W.w3_complex_holo.2 x
  w3_complex_asymp := fun {b} hb => by
    rw [ofProblem_cardyVC]; exact W.w3_complex_asymp hb
  w4_vac := fun {T g} hg => W.w4_vac ((ofProblem_isWeaklyFeasible_iff prob).mp hg)

/-- Uniform bridge: `FixedWeightUniformAxioms prob` gives `SourceUniformAxioms (ofProblem prob)`. -/
noncomputable def _root_.FormalResearch.ModularBootstrap.WeightAxioms.FixedWeightUniformAxioms.toSourceUniformAxioms
    {prob : FixedWeightProblem} (U : FixedWeightUniformAxioms prob) :
    SourceUniformAxioms (ShiftSource.ofProblem prob) where
  c₀ := U.c₀
  hc₀_pos := lt_of_lt_of_le (by linarith [le_max_left (1 : ℝ) (24 * prob.totalShift)]) U.hc₀_ge
  C_1 := U.C_1
  hC1_pos := U.hC1_pos
  C_e := U.C_e
  hCe_pos := U.hCe_pos
  p_e := U.p_e
  hp_e_nn := U.hp_e_nn
  c_low := U.c_low
  hc_low_pos := U.hc_low_pos
  p_0 := U.p_0
  hp_0_nn := U.hp_0_nn
  C_K := U.C_K
  hCK_pos := U.hCK_pos
  p_K := U.p_K
  hp_K_nn := U.hp_K_nn
  c_band := U.c_band
  hc_band_pos := U.hc_band_pos
  C_up := U.C_up
  hCup_pos := U.hCup_pos
  p_u := U.p_u
  hp_u_nn := U.hp_u_nn
  r_1 := U.r_1
  hr1_pos := U.hr1_pos
  hr1_le := U.hr1_le
  Q_star := U.Q_star
  c_Q := U.c_Q
  C_Q := U.C_Q
  hcQ_pos := U.hcQ_pos
  hcQ_le := U.hcQ_le
  C_V := U.C_V
  hCV_nn := U.hCV_nn
  axioms_at hc' := (U.axioms_at hc').toSourceAxioms
  uniform_C_1 hc' := U.uniform_C_1 hc'
  uniform_C_e hc' := U.uniform_C_e hc'
  uniform_p_e hc' := U.uniform_p_e hc'
  uniform_c_low hc' := U.uniform_c_low hc'
  uniform_p_0 hc' := U.uniform_p_0 hc'
  uniform_C_K hc' := U.uniform_C_K hc'
  uniform_p_K hc' := U.uniform_p_K hc'
  uniform_c_band hc' := U.uniform_c_band hc'
  uniform_C_up hc' := U.uniform_C_up hc'
  uniform_p_u hc' := U.uniform_p_u hc'
  uniform_r_1 hc' := U.uniform_r_1 hc'
  uniform_Q_star hc' := U.uniform_Q_star hc'
  uniform_c_Q hc' := U.uniform_c_Q hc'
  uniform_C_Q hc' := U.uniform_C_Q hc'
  uniform_C_V hc' := U.uniform_C_V hc'

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.FixedWeightUniformAxioms.toSourceUniformAxioms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FixedWeightUniformAxioms.toSourceUniformAxioms

end FormalResearch.ModularBootstrap.Mixtures
