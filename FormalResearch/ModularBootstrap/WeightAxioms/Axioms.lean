module

public import FormalResearch.ModularBootstrap.WeightAxioms.HankelContinuation
public import FormalResearch.ModularBootstrap.FixedWeight.CrossingMeasure
public import FormalResearch.ModularBootstrap.Bessel.VCorollaries

/-!
# Fixed-Weight Axioms (W1)–(W4), Proposition P (P0)–(P3), and Lemma 4 for Every `(w, Q)`

Formalises the fixed-weight axioms `(W1)–(W4)` of `lower_o1_two_edge.tex` §J1 (`vlo:secJ1`) and
`(P0)–(P3)` of Proposition P (`ft:PP`) at general chiral weight `w ≥ 1` and null-state product
`Q(q) = ∏_{l=1}^m (1 - q^{μ_l})`, and proves them **unconditionally** for every
`prob : FixedWeightProblem` for all `c' ≥ c₀` (`c₀ ≥ max 1 (24 S)`):

* `FixedWeightAxioms prob c'`: Lean structure encoding `(W1)–(W4)` at fixed `c'` (`a = c'/12`).
* `FixedWeightUniformAxioms prob`: `c'`-independent constants/exponents + `c₀ ≥ max 1 (24 S)` such
  that `FixedWeightAxioms prob c'` holds for all `c' ≥ c₀`.
* `PropositionPAxioms prob c'` and `FixedWeightUniformP prob`: the Proposition P clauses
  `(P0)–(P3)` (`ft:PP`), proved unconditionally from `FixedWeightAxioms` /
  `FixedWeightUniformAxioms` (`FixedWeightAxioms.toPropositionPAxioms`, `uniformP_of_uniformAxioms`).
* `fixedWeightAxioms_of_problem`: unconditional verification of `FixedWeightUniformAxioms prob` for
  every `prob : FixedWeightProblem` with `p_0 = prob.m + prob.w - 1`, `p_K = 2 * prob.m`,
  `p_e = prob.m`, `p_u = 0`, `r_1 = 1 / 10 ≤ xiStar / 2`, and `Q_* (b) = Q(e^{-4π b})`.
* `lemma4_summary`: unified summary of Lemma 4 `(a)–(f)` (`n1:L4`).
* Concrete instances `virasoro_fixedWeightAxioms`, `n1SuperVirasoro_fixedWeightAxioms`, and
  `trivialProduct_fixedWeightAxioms`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.WeightAxioms

open Crossing Bessel ComplexBessel

/-! ### Section 1: Fixed-weight axioms `(W1)–(W4)` (`lower_o1_two_edge.tex` §J1) -/

/-- Fixed-weight axioms `(W1)–(W4)` of `lower_o1_two_edge.tex` §J1 (`vlo:secJ1`) at a single
parameter `c' > 0` (`a = c' / 12`) for `prob : FixedWeightProblem`. -/
structure FixedWeightAxioms (prob : FixedWeightProblem) (c' : ℝ) where
  hc'_pos : 0 < c'
  ha_shift : prob.totalShift ≤ c' / 12
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
  /-- `(W1)` norm bound: `‖g‖_∞ ≤ C₁ M[g]` for `g ∈ \overline{\mathcal A}_w`. -/
  w1_sup : ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
    ∀ {t : ℝ}, 0 ≤ t → |g t| ≤ C_1 * prob.cardyNorm (c' / 12) g
  /-- `(W1)` strip continuation: `G(b) = g(c' b² / 3)` extends holomorphically to `|Im b| < 1/2`
  and continuously to `|Im b| ≤ 1/2`, bounded by `C_e c'^{p_e} M[g]`. -/
  w1_strip : ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
    ∃ G : ℂ → ℂ,
      ContinuousOn G {b : ℂ | |b.im| ≤ 1 / 2} ∧
      DifferentiableOn ℂ G {b : ℂ | |b.im| < 1 / 2} ∧
      (∀ x : ℝ, G (x : ℂ) = (g (c' * x ^ 2 / 3) : ℂ)) ∧
      ∀ {b : ℂ}, |b.im| ≤ 1 / 2 → ‖G b‖ ≤ C_e * c' ^ p_e * prob.cardyNorm (c' / 12) g
  /-- `(W2)` strict positivity on `(0, ∞)`. -/
  w2_pos : ∀ {t : ℝ}, 0 < t → 0 < prob.cardyV (c' / 12) t
  /-- `(W2)` small-`t` floor: `c_low t^{p_0} ≤ V(t)` on `(0, 4/c']`. -/
  w2_floor : ∀ {t : ℝ}, 0 < t → t ≤ 4 / c' → c_low * t ^ p_0 ≤ prob.cardyV (c' / 12) t
  /-- `(W2)` lower comparison on `[4/c', ∞)`: `K_a^{(w)}(t) ≤ C_K c'^{p_K} V(t)`. -/
  w2_ker_le : ∀ {t : ℝ}, 4 / c' ≤ t →
    kernelK prob.w (c' / 12) t ≤ C_K * c' ^ p_K * prob.cardyV (c' / 12) t
  /-- `(W2)` band lower comparison on `[xiBar * c', ∞)`: `c_band K_a^{(w)}(t) ≤ V(t)`. -/
  w2_band : ∀ {t : ℝ}, xiBar * c' ≤ t →
    c_band * kernelK prob.w (c' / 12) t ≤ prob.cardyV (c' / 12) t
  /-- `(W2)` upper comparison on `(0, xiBar * c']`: `V(t) ≤ C_up (1 + c'^{p_u}) K_a^{(w)}(t)`. -/
  w2_up : ∀ {t : ℝ}, 0 < t → t ≤ xiBar * c' →
    prob.cardyV (c' / 12) t ≤ C_up * (1 + c' ^ p_u) * kernelK prob.w (c' / 12) t
  /-- `(W3)` `Q_*` is holomorphic on `Re b > 0` (in fact entire here). -/
  w3_Q_holo : DifferentiableOn ℂ Q_star {b : ℂ | 0 < b.re}
  /-- `(W3)` `Q_*` is zero-free on the closed disc `|b - ξ_*| ≤ r₁`. -/
  w3_Q_ne_zero : ∀ {b : ℂ}, b ∈ Metric.closedBall (xiStar : ℂ) r_1 → Q_star b ≠ 0
  /-- `(W3)` `Q_*` is real and uniformly in `[c_Q, C_Q]` on `[ξ_*/2, ∞)`. -/
  w3_Q_real_bounds : ∀ {x : ℝ}, xiStar / 2 ≤ x →
    (Q_star (x : ℂ)).im = 0 ∧ c_Q ≤ (Q_star (x : ℂ)).re ∧ (Q_star (x : ℂ)).re ≤ C_Q
  /-- `(W3)` uniform real Cardy asymptote on `[ξ_*/2, ∞)`. -/
  w3_real_asymp : ∀ {x : ℝ}, xiStar / 2 ≤ x →
    |prob.cardyV (c' / 12) (c' * x ^ 2 / 3) /
        ((2 * x) ^ (prob.w - 1) * besselAs (c' * (2 * Real.pi * x / 3))) -
      (Q_star (x : ℂ)).re| ≤ C_V / c'
  /-- `(W3)` entire complex continuation of `V`, agreeing with `V` on `ℝ`. -/
  w3_complex_holo : Differentiable ℂ (fun b : ℂ => cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3)) ∧
    ∀ x : ℝ, cardyVC prob (c' / 12) (x : ℂ) = (prob.cardyV (c' / 12) x : ℂ)
  /-- `(W3)` complex-disc lobe asymptote on `|b - ξ_*| ≤ r₁`. -/
  w3_complex_asymp : ∀ {b : ℂ}, b ∈ Metric.closedBall (xiStar : ℂ) r_1 →
    ‖cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) /
        ((2 * b) ^ (prob.w - 1) * asC ((c' : ℂ) * tipL b)) -
      Q_star b‖ ≤ C_V / c'
  /-- `(W4)` vacuum sign: every weakly feasible `g` satisfies `∫₀^∞ g(t) V(t) dt ≤ 0`. -/
  w4_vac : ∀ {T : ℝ} {g : ℝ → ℝ}, prob.IsWeaklyFeasible (c' / 12) T g →
    ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c' / 12) t ≤ 0

/-- Uniform-in-`c'` version of `FixedWeightAxioms`: all structural constants, exponents,
disc radius `r₁`, and `Q_*` are independent of `c'` for `c' ≥ c₀`. -/
structure FixedWeightUniformAxioms (prob : FixedWeightProblem) where
  c₀ : ℝ
  hc₀_ge : max 1 (24 * prob.totalShift) ≤ c₀
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
  axioms_at : ∀ {c' : ℝ}, c₀ ≤ c' → FixedWeightAxioms prob c'
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

/-! ### Section 2: Proposition P `(P0)–(P3)` (`ft:PP`) and implication `(W1)–(W4) ⇒ (P0)–(P3)` -/

/-- Proposition P hypotheses `(P0)–(P3)` of `lower_o1_two_edge.tex` (`ft:PP`, ll. 251–262) at
parameter `c' > 0`, with vacuum tolerance `η_vac` and lobe-error bound `η_V`. -/
structure PropositionPAxioms (prob : FixedWeightProblem) (c' : ℝ) where
  hc'_pos : 0 < c'
  C_e : ℝ
  hCe_pos : 0 < C_e
  p_e : ℝ
  hp_e_nn : 0 ≤ p_e
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
  η_V : ℝ
  hηV_nn : 0 ≤ η_V
  η_vac : ℝ
  hηvac_nn : 0 ≤ η_vac
  /-- `(P0)` strip continuation and edge bound. -/
  p0_strip : ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
    ∃ G : ℂ → ℂ,
      ContinuousOn G {b : ℂ | |b.im| ≤ 1 / 2} ∧
      DifferentiableOn ℂ G {b : ℂ | |b.im| < 1 / 2} ∧
      (∀ x : ℝ, G (x : ℂ) = (g (c' * x ^ 2 / 3) : ℂ)) ∧
      ∀ {b : ℂ}, |b.im| ≤ 1 / 2 → ‖G b‖ ≤ C_e * c' ^ p_e * prob.cardyNorm (c' / 12) g
  /-- `(P1)` positivity and comparison with `K_a^{(w)}` on `[xiBar * c', ∞)` and `(0, xiBar * c']`. -/
  p1_pos : ∀ {t : ℝ}, 0 < t → 0 < prob.cardyV (c' / 12) t
  p1_band : ∀ {t : ℝ}, xiBar * c' ≤ t →
    c_band * kernelK prob.w (c' / 12) t ≤ prob.cardyV (c' / 12) t
  p1_up : ∀ {t : ℝ}, 0 < t → t ≤ xiBar * c' →
    prob.cardyV (c' / 12) t ≤ C_up * (1 + c' ^ p_u) * kernelK prob.w (c' / 12) t
  /-- `(P2)` holomorphic complex-disc lobe asymptote on `|b - ξ_*| ≤ r₁`. -/
  p2_Q_holo : DifferentiableOn ℂ Q_star {b : ℂ | 0 < b.re}
  p2_Q_ne_zero : ∀ {b : ℂ}, b ∈ Metric.closedBall (xiStar : ℂ) r_1 → Q_star b ≠ 0
  p2_Q_real_pos : ∀ {x : ℝ}, xiStar / 2 ≤ x →
    (Q_star (x : ℂ)).im = 0 ∧ 0 < (Q_star (x : ℂ)).re
  p2_V_holo : Differentiable ℂ (fun b : ℂ => cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3))
  p2_V_ofReal : ∀ x : ℝ, cardyVC prob (c' / 12) (x : ℂ) = (prob.cardyV (c' / 12) x : ℂ)
  p2_disc_asymp : ∀ {b : ℂ}, b ∈ Metric.closedBall (xiStar : ℂ) r_1 →
    ‖cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) /
        ((2 * b) ^ (prob.w - 1) * asC ((c' : ℂ) * tipL b)) -
      Q_star b‖ ≤ η_V
  /-- `(P3)` vacuum sign with tolerance `η_vac`: `∫₀^∞ g(t) V(t) dt ≤ η_vac * M[g]`. -/
  p3_vac : ∀ {T : ℝ} {g : ℝ → ℝ}, prob.IsWeaklyFeasible (c' / 12) T g →
    ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c' / 12) t ≤ η_vac * prob.cardyNorm (c' / 12) g

/-- Uniform asymptotic Proposition P family with `η_V(c') → 0` and `η_vac(c') = 0` (`ft:PP`, l. 267). -/
structure FixedWeightUniformP (prob : FixedWeightProblem) where
  c₀ : ℝ
  hc₀_pos : 0 < c₀
  pAt : ∀ {c' : ℝ}, c₀ ≤ c' → PropositionPAxioms prob c'
  disc_err_tendsto_zero :
    Tendsto (fun c' : ℝ => if h : c₀ ≤ c' then (pAt h).η_V else 0) atTop (𝓝 0)
  vac_err_zero : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (pAt hc').η_vac = 0

/-- **`(W1)–(W4) ⇒ (P0)–(P3)` (`ft:PP`, l. 267)**: every instance satisfying `FixedWeightAxioms`
satisfies `PropositionPAxioms` with `η_V = C_V / c'` and `η_vac = 0`. -/
noncomputable def FixedWeightAxioms.toPropositionPAxioms {prob : FixedWeightProblem} {c' : ℝ}
    (W : FixedWeightAxioms prob c') : PropositionPAxioms prob c' where
  hc'_pos := W.hc'_pos
  C_e := W.C_e
  hCe_pos := W.hCe_pos
  p_e := W.p_e
  hp_e_nn := W.hp_e_nn
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
  η_V := W.C_V / c'
  hηV_nn := div_nonneg W.hCV_nn W.hc'_pos.le
  η_vac := 0
  hηvac_nn := le_rfl
  p0_strip := W.w1_strip
  p1_pos := W.w2_pos
  p1_band := W.w2_band
  p1_up := W.w2_up
  p2_Q_holo := W.w3_Q_holo
  p2_Q_ne_zero := W.w3_Q_ne_zero
  p2_Q_real_pos := fun hx => by
    obtain ⟨him, hlo, _⟩ := W.w3_Q_real_bounds hx
    exact ⟨him, lt_of_lt_of_le W.hcQ_pos hlo⟩
  p2_V_holo := W.w3_complex_holo.1
  p2_V_ofReal := W.w3_complex_holo.2
  p2_disc_asymp := W.w3_complex_asymp
  p3_vac := fun hfeas => by
    rw [zero_mul]
    exact W.w4_vac hfeas

/-- Uniform-`c'` implication from `FixedWeightUniformAxioms` to `FixedWeightUniformP`. -/
noncomputable def uniformP_of_uniformAxioms {prob : FixedWeightProblem}
    (U : FixedWeightUniformAxioms prob) : FixedWeightUniformP prob where
  c₀ := U.c₀
  hc₀_pos := lt_of_lt_of_le (by linarith [le_max_left (1 : ℝ) (24 * prob.totalShift)]) U.hc₀_ge
  pAt hc' := (U.axioms_at hc').toPropositionPAxioms
  disc_err_tendsto_zero := by
    have htend : Tendsto (fun c' : ℝ => U.C_V / c') atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine htend.congr' ((eventually_ge_atTop U.c₀).mono fun c' hc' => ?_)
    dsimp only [FixedWeightAxioms.toPropositionPAxioms]
    rw [dite_eq_left_of_eq_true (eq_true hc'), U.uniform_C_V hc']
  vac_err_zero _ := rfl

/-! ### Section 3: Small-`t` polynomial floor and proof of `(W1)–(W4)` for every `(w, Q)` -/

/-- **Lemma 4(b) polynomial floor (`n1:L4`)**: for every `c' ≥ 12 S` and every `t > 0`,
`c_low * t^{m + w - 1} ≤ V(t)` with explicit `c_low > 0`. -/
lemma cardyV_small_t_floor (prob : FixedWeightProblem) :
    ∃ c_low : ℝ, 0 < c_low ∧
      ∀ {a t : ℝ}, prob.totalShift ≤ a → 0 < t →
        c_low * t ^ ((prob.m + prob.w - 1 : ℕ) : ℝ) ≤ prob.cardyV a t := by
  have hw := prob.hw
  let c_low : ℝ :=
    (∏ l : Fin prob.m, prob.μ l) * (4 * Real.pi ^ 2) ^ prob.m * (2 * Real.pi) ^ (prob.w - 1) /
      (((prob.w - 1 + prob.m)! : ℕ) : ℝ)
  have hprod_pos : 0 < ∏ l : Fin prob.m, prob.μ l :=
    Finset.prod_pos fun l _ => prob.hμ l
  have hc_pos : 0 < c_low := by
    dsimp [c_low]
    exact div_pos (mul_pos (mul_pos hprod_pos (pow_pos (by positivity) _)) (pow_pos (by positivity) _))
      (by exact_mod_cast Nat.factorial_pos _)
  refine ⟨c_low, hc_pos, fun {a t} ha ht => ?_⟩
  have hpeano := cardyV_ge_peano_kernel prob ha ht.le
  have hS_ge0 : ((((prob.w - 1 + prob.m)! : ℕ) : ℝ))⁻¹ ≤
      besselS (prob.w - 1 + prob.m) (4 * Real.pi ^ 2 * (a - prob.totalShift) * t) := by
    unfold besselS
    have hu_nn : 0 ≤ 4 * Real.pi ^ 2 * (a - prob.totalShift) * t :=
      mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr ha)) ht.le
    have hsum := summable_besselTerm (prob.w - 1 + prob.m) hu_nn
    have hterm0 : besselTerm (prob.w - 1 + prob.m) (4 * Real.pi ^ 2 * (a - prob.totalShift) * t) 0 =
        ((((prob.w - 1 + prob.m)! : ℕ) : ℝ))⁻¹ := by
      unfold besselTerm
      simp
    rw [← hterm0]
    exact hsum.le_tsum 0 fun j _ => by unfold besselTerm; positivity
  have hexp_eq : (prob.m + prob.w - 1 : ℕ) = prob.m + (prob.w - 1) := by omega
  have ht_pow : t ^ ((prob.m + prob.w - 1 : ℕ) : ℝ) = t ^ prob.m * t ^ (prob.w - 1) := by
    rw [Real.rpow_natCast, hexp_eq, pow_add]
  have hlow_le : c_low * t ^ ((prob.m + prob.w - 1 : ℕ) : ℝ) ≤
      (∏ l : Fin prob.m, prob.μ l) * (4 * Real.pi ^ 2 * t) ^ prob.m * (2 * Real.pi * t) ^ (prob.w - 1) *
        besselS (prob.w - 1 + prob.m) (4 * Real.pi ^ 2 * (a - prob.totalShift) * t) := by
    calc c_low * t ^ ((prob.m + prob.w - 1 : ℕ) : ℝ)
        = (∏ l : Fin prob.m, prob.μ l) * (4 * Real.pi ^ 2 * t) ^ prob.m * (2 * Real.pi * t) ^ (prob.w - 1) *
            ((((prob.w - 1 + prob.m)! : ℕ) : ℝ))⁻¹ := by
          dsimp [c_low]
          rw [ht_pow, mul_pow, mul_pow, div_eq_mul_inv]
          ring
      _ ≤ (∏ l : Fin prob.m, prob.μ l) * (4 * Real.pi ^ 2 * t) ^ prob.m * (2 * Real.pi * t) ^ (prob.w - 1) *
            besselS (prob.w - 1 + prob.m) (4 * Real.pi ^ 2 * (a - prob.totalShift) * t) := by
          gcongr
  exact hlow_le.trans hpeano

/-- Helper constructing a `FixedWeightUniformAxioms` witness once `p_K` and `ker_le` are given. -/
private noncomputable def mkUniformAxioms {prob : FixedWeightProblem}
    (c₀ : ℝ) (hc₀_ge : max 1 (24 * prob.totalShift) ≤ c₀)
    (C_1 : ℝ) (hC1_pos : 0 < C_1)
    (hwin : ∀ {a : ℝ} {g : ℝ → ℝ}, prob.totalShift ≤ a → TestClass prob a g →
      ∀ {t : ℝ}, 0 ≤ t → |g t| ≤ C_1 * prob.cardyNorm a g)
    (C_e : ℝ) (hCe_pos : 0 < C_e)
    (hstrip : ∀ {c' : ℝ} {g : ℝ → ℝ}, c₀ ≤ c' → TestClass prob (c' / 12) g →
      ∀ {b : ℂ}, |b.im| ≤ 1 / 2 →
        ‖hankelContinuationW prob.w c' g b‖ ≤ C_e * c' ^ (prob.m : ℝ) * prob.cardyNorm (c' / 12) g)
    (hcont : ∀ {c' : ℝ} {g : ℝ → ℝ}, c₀ ≤ c' → TestClass prob (c' / 12) g →
      ContinuousOn (hankelContinuationW prob.w c' g) {b : ℂ | |b.im| ≤ 1 / 2})
    (hdiff : ∀ {c' : ℝ} {g : ℝ → ℝ}, c₀ ≤ c' → TestClass prob (c' / 12) g →
      DifferentiableOn ℂ (hankelContinuationW prob.w c' g) {b : ℂ | |b.im| < 1 / 2})
    (c_low : ℝ) (hc_low_pos : 0 < c_low)
    (hfloor : ∀ {a t : ℝ}, prob.totalShift ≤ a → 0 < t →
      c_low * t ^ ((prob.m + prob.w - 1 : ℕ) : ℝ) ≤ prob.cardyV a t)
    (C_K p_K : ℝ) (hCK_pos : 0 < C_K) (hpK_nn : 0 ≤ p_K)
    (hker : ∀ {c' t : ℝ}, c₀ ≤ c' → 4 / c' ≤ t →
      kernelK prob.w (c' / 12) t ≤ C_K * c' ^ p_K * prob.cardyV (c' / 12) t)
    (c_band : ℝ) (hc_band_pos : 0 < c_band)
    (hband : ∀ {c' t : ℝ}, c₀ ≤ c' → xiBar * c' ≤ t →
      c_band * kernelK prob.w (c' / 12) t ≤ prob.cardyV (c' / 12) t)
    (C_V : ℝ) (hCV_nn : 0 ≤ C_V)
    (hreal : ∀ {c' x : ℝ}, max 1 (24 * prob.totalShift) ≤ c' → xiStar / 2 ≤ x →
      |prob.cardyV (c' / 12) (c' * x ^ 2 / 3) /
          ((2 * x) ^ (prob.w - 1) * besselAs (c' * (2 * Real.pi * x / 3))) -
        prob.nullPoly (Real.exp (-4 * Real.pi * x))| ≤ C_V / c')
    (hcmplx : ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {b : ℂ},
      (xiStar / 2 : ℝ) ≤ b.re → |b.im| ≤ b.re → ‖b‖ ≤ (3 / 2 : ℝ) * xiStar →
      ‖cardyErrC prob c' b‖ ≤ C_V / c') :
    FixedWeightUniformAxioms prob where
  c₀ := c₀
  hc₀_ge := hc₀_ge
  C_1 := C_1
  hC1_pos := hC1_pos
  C_e := C_e
  hCe_pos := hCe_pos
  p_e := prob.m
  hp_e_nn := Nat.cast_nonneg _
  c_low := c_low
  hc_low_pos := hc_low_pos
  p_0 := (prob.m + prob.w - 1 : ℕ)
  hp_0_nn := Nat.cast_nonneg _
  C_K := C_K
  hCK_pos := hCK_pos
  p_K := p_K
  hp_K_nn := hpK_nn
  c_band := c_band
  hc_band_pos := hc_band_pos
  C_up := 1
  hCup_pos := one_pos
  p_u := 0
  hp_u_nn := le_rfl
  r_1 := 1 / 10
  hr1_pos := by norm_num
  hr1_le := by linarith [one_fifth_le_xiStar]
  Q_star := nullPolyExpC prob
  c_Q := prob.nullPoly (Real.exp (-4 * Real.pi * (xiStar / 2)))
  C_Q := 1
  hcQ_pos := (nullPoly_exp_bounds prob (half_pos xiStar_pos)).1
  hcQ_le := (nullPoly_exp_bounds prob (half_pos xiStar_pos)).2 le_rfl |>.2
  C_V := C_V
  hCV_nn := hCV_nn
  axioms_at {c'} hc' :=
    have hcm : max 1 (24 * prob.totalShift) ≤ c' := hc₀_ge.trans hc'
    have hc'_pos : 0 < c' :=
      lt_of_lt_of_le (by linarith [le_max_left (1 : ℝ) (24 * prob.totalShift)]) hcm
    have ha_shift : prob.totalShift ≤ c' / 12 := by
      linarith [(le_max_right (1 : ℝ) (24 * prob.totalShift)).trans hcm, prob.totalShift_nonneg]
    { hc'_pos := hc'_pos
      ha_shift := ha_shift
      C_1 := C_1
      hC1_pos := hC1_pos
      C_e := C_e
      hCe_pos := hCe_pos
      p_e := prob.m
      hp_e_nn := Nat.cast_nonneg _
      c_low := c_low
      hc_low_pos := hc_low_pos
      p_0 := (prob.m + prob.w - 1 : ℕ)
      hp_0_nn := Nat.cast_nonneg _
      C_K := C_K
      hCK_pos := hCK_pos
      p_K := p_K
      hp_K_nn := hpK_nn
      c_band := c_band
      hc_band_pos := hc_band_pos
      C_up := 1
      hCup_pos := one_pos
      p_u := 0
      hp_u_nn := le_rfl
      r_1 := 1 / 10
      hr1_pos := by norm_num
      hr1_le := by linarith [one_fifth_le_xiStar]
      Q_star := nullPolyExpC prob
      c_Q := prob.nullPoly (Real.exp (-4 * Real.pi * (xiStar / 2)))
      C_Q := 1
      hcQ_pos := (nullPoly_exp_bounds prob (half_pos xiStar_pos)).1
      hcQ_le := (nullPoly_exp_bounds prob (half_pos xiStar_pos)).2 le_rfl |>.2
      C_V := C_V
      hCV_nn := hCV_nn
      w1_sup := fun {g} hg {t} ht => hwin ha_shift hg ht
      w1_strip := fun {g} hg =>
        ⟨hankelContinuationW prob.w c' _,
          hcont hc' hg,
          hdiff hc' hg,
          fun x => hankelContinuationW_ofReal prob.hw hc'_pos hg.cont hg.int_lift hg.fourier_odd x,
          fun {b} hb => hstrip hc' hg hb⟩
      w2_pos := fun {t} ht => prob.cardyV_pos ha_shift ht
      w2_floor := fun {t} ht _ => hfloor ha_shift ht
      w2_ker_le := fun {t} ht => hker hc' ht
      w2_band := fun {t} ht => hband hc' ht
      w2_up := fun {t} ht _ => by
        have hle := cardyV_le_kernelK prob ha_shift ht.le
        have hK_nn : 0 ≤ kernelK prob.w (c' / 12) t := kernelK_nonneg (by linarith) ht.le
        calc prob.cardyV (c' / 12) t ≤ 1 * kernelK prob.w (c' / 12) t := by linarith
          _ ≤ 1 * (1 + c' ^ (0 : ℝ)) * kernelK prob.w (c' / 12) t := by
            rw [Real.rpow_zero]; linarith
      w3_Q_holo := (nullPolyExpC_entire prob).differentiableOn
      w3_Q_ne_zero := fun {b} hb => by
        have hdist : ‖b - (xiStar : ℂ)‖ ≤ 1 / 10 := by
          simpa [Complex.dist_eq] using mem_closedBall.mp hb
        have hre_sub : |b.re - xiStar| ≤ ‖b - (xiStar : ℂ)‖ := by
          simpa [Complex.sub_re] using Complex.abs_re_le_norm (b - (xiStar : ℂ))
        have hb_re : 0 < b.re := by
          have := (abs_le.mp (hre_sub.trans hdist)).1
          linarith [one_fifth_le_xiStar]
        exact nullPolyExpC_ne_zero prob hb_re
      w3_Q_real_bounds := fun {x} hx => by
        rw [nullPolyExpC_ofReal]
        have hbd := (nullPoly_exp_bounds prob (half_pos xiStar_pos)).2 hx
        exact ⟨Complex.ofReal_im _, hbd.1, hbd.2⟩
      w3_real_asymp := fun {x} hx => by
        rw [nullPolyExpC_ofReal, Complex.ofReal_re]
        exact hreal hcm hx
      w3_complex_holo :=
        ⟨(cardyVC_entire prob (c' / 12)).comp (by fun_prop), fun x => cardyVC_ofReal prob (c' / 12) x⟩
      w3_complex_asymp := fun {b} hb => by
        have hdist : ‖b - (xiStar : ℂ)‖ ≤ 1 / 10 := by
          simpa [Complex.dist_eq] using mem_closedBall.mp hb
        have hre_sub : |b.re - xiStar| ≤ ‖b - (xiStar : ℂ)‖ := by
          simpa [Complex.sub_re] using Complex.abs_re_le_norm (b - (xiStar : ℂ))
        have him_sub : |b.im| ≤ ‖b - (xiStar : ℂ)‖ := by
          simpa [Complex.sub_im] using Complex.abs_im_le_norm (b - (xiStar : ℂ))
        have hb_re : xiStar / 2 ≤ b.re := by
          have := (abs_le.mp (hre_sub.trans hdist)).1
          linarith [one_fifth_le_xiStar]
        have hb_im : |b.im| ≤ b.re := by
          have := him_sub.trans hdist
          linarith [one_fifth_le_xiStar]
        have hb_norm : ‖b‖ ≤ (3 / 2 : ℝ) * xiStar := by
          have hxi : ‖(xiStar : ℂ)‖ = xiStar := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos xiStar_pos]
          calc ‖b‖ = ‖(b - (xiStar : ℂ)) + (xiStar : ℂ)‖ := by ring_nf
            _ ≤ ‖b - (xiStar : ℂ)‖ + ‖(xiStar : ℂ)‖ := norm_add_le _ _
            _ ≤ 1 / 10 + xiStar := add_le_add hdist hxi.le
            _ ≤ (3 / 2 : ℝ) * xiStar := by linarith [one_fifth_le_xiStar]
        exact hcmplx hc' hb_re hb_im hb_norm
      w4_vac := fun {T g} hfeas => by
        have hvac : 0 ≤ -2 * Real.pi * ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c' / 12) t :=
          hfeas.2.2.1
        nlinarith [Real.pi_pos] }
  uniform_C_1 _ := rfl
  uniform_C_e _ := rfl
  uniform_p_e _ := rfl
  uniform_c_low _ := rfl
  uniform_p_0 _ := rfl
  uniform_C_K _ := rfl
  uniform_p_K _ := rfl
  uniform_c_band _ := rfl
  uniform_C_up _ := rfl
  uniform_p_u _ := rfl
  uniform_r_1 _ := rfl
  uniform_Q_star _ := rfl
  uniform_c_Q _ := rfl
  uniform_C_Q _ := rfl
  uniform_C_V _ := rfl

/-- **Main fixed-weight theorem (`lower_o1_two_edge.tex` §J1, `n1_super_virasoro.tex` Lemma 4)**:
every `prob : FixedWeightProblem` satisfies `FixedWeightAxioms prob c'` uniformly for all
`c' ≥ c₀` (`c₀ ≥ max 1 (24 S)`), with `p₀ = m + w - 1`, `p_K = 2m`, `p_e = m`, `p_u = 0`,
`r₁ = 1 / 10`, and `Q_*(b) = Q(e^{-4π b})`. -/
theorem fixedWeightAxioms_of_problem (prob : FixedWeightProblem) :
    Nonempty (FixedWeightUniformAxioms prob) := by
  obtain ⟨C_int, C_1, hCint_pos, hC1_pos, hwin⟩ := testClass_window_bounds prob
  obtain ⟨C_e, c₁, hCe_pos, hc1_ge, hstrip⟩ := hankelContinuationW_strip_bound prob
  obtain ⟨c₂, hc2_ge, hcont⟩ := continuousOn_hankelContinuationW prob
  obtain ⟨c₃, hc3_ge, hdiff⟩ := differentiableOn_hankelContinuationW prob
  obtain ⟨c_low, hc_low_pos, hfloor⟩ := cardyV_small_t_floor prob
  obtain ⟨C_K, c₄, hCK_pos, hc4_ge, hker⟩ := kernelK_le_mul_cardyV_n1 prob
  obtain ⟨c_band, c₅, hc_band_pos, hc5_ge, hband⟩ := cardyV_ge_band_mul_kernelK prob
  obtain ⟨C_r, hCr_nn, hreal⟩ := cardyV_asymptotic_real prob (x₀ := xiStar / 2) (half_pos xiStar_pos)
  obtain ⟨C_c, c₆, hCc_nn, hc6_ge, hcmplx⟩ :=
    cardyErrC_bound_on_box prob (m₀ := xiStar / 2) (M₀ := (3 / 2 : ℝ) * xiStar)
      (half_pos xiStar_pos) (mul_nonneg (by positivity) xiStar_pos.le)
  let c₀ : ℝ := max c₁ (max c₂ (max c₃ (max c₄ (max c₅ c₆))))
  have hc₀_ge : max 1 (24 * prob.totalShift) ≤ c₀ := hc1_ge.trans (le_max_left _ _)
  let C_V : ℝ := max C_r C_c
  have hCV_nn : 0 ≤ C_V := le_trans hCr_nn (le_max_left _ _)
  exact ⟨mkUniformAxioms
    c₀ hc₀_ge C_1 hC1_pos (fun {a g} ha hg {t} ht => (hwin ha hg).2 ht)
    C_e hCe_pos
    (fun {c' g} hc' hg {b} hb => (hstrip ((le_max_left _ _).trans hc') hg hb).1)
    (fun {c' g} hc' hg => hcont ((le_max_left _ _).trans ((le_max_right _ _).trans hc')) hg)
    (fun {c' g} hc' hg => hdiff ((le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans hc'))) hg)
    c_low hc_low_pos hfloor
    C_K (2 * prob.m : ℕ) hCK_pos (Nat.cast_nonneg _)
    (fun {c' t} hc' ht => by
      have h1 := (hker ((le_max_left _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans ((le_max_right _ _).trans hc')))) ht).1
      simpa [Real.rpow_natCast] using h1)
    c_band hc_band_pos
    (fun {c' t} hc' ht => hband ((le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc'))))) ht)
    C_V hCV_nn
    (fun {c' x} hcm hx => (hreal hcm hx).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (by linarith [(le_max_left (1 : ℝ) _).trans hcm])))
    (fun {c'} hc' {b} hb1 hb2 hb3 => (hcmplx ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc'))))) hb1 hb2 hb3).trans
      (div_le_div_of_nonneg_right (le_max_right _ _)
        (lt_of_lt_of_le (by linarith [le_max_left (1 : ℝ) (24 * prob.totalShift)]) (hc₀_ge.trans hc')).le))⟩

/-- Sharper kernel-comparison variant with `p_K = prob.m` (using `kernelK_le_mul_cardyV_gen`,
improving the paper's `2m` exponent at `[4/c', ∞)`). -/
theorem fixedWeightAxioms_of_problem_sharp_pK (prob : FixedWeightProblem) :
    ∃ U : FixedWeightUniformAxioms prob, U.p_K = prob.m := by
  obtain ⟨C_int, C_1, hCint_pos, hC1_pos, hwin⟩ := testClass_window_bounds prob
  obtain ⟨C_e, c₁, hCe_pos, hc1_ge, hstrip⟩ := hankelContinuationW_strip_bound prob
  obtain ⟨c₂, hc2_ge, hcont⟩ := continuousOn_hankelContinuationW prob
  obtain ⟨c₃, hc3_ge, hdiff⟩ := differentiableOn_hankelContinuationW prob
  obtain ⟨c_low, hc_low_pos, hfloor⟩ := cardyV_small_t_floor prob
  obtain ⟨C_K, c₄, hCK_pos, hc4_ge, hker⟩ := kernelK_le_mul_cardyV_gen prob
  obtain ⟨c_band, c₅, hc_band_pos, hc5_ge, hband⟩ := cardyV_ge_band_mul_kernelK prob
  obtain ⟨C_r, hCr_nn, hreal⟩ := cardyV_asymptotic_real prob (x₀ := xiStar / 2) (half_pos xiStar_pos)
  obtain ⟨C_c, c₆, hCc_nn, hc6_ge, hcmplx⟩ :=
    cardyErrC_bound_on_box prob (m₀ := xiStar / 2) (M₀ := (3 / 2 : ℝ) * xiStar)
      (half_pos xiStar_pos) (mul_nonneg (by positivity) xiStar_pos.le)
  let c₀ : ℝ := max c₁ (max c₂ (max c₃ (max c₄ (max c₅ c₆))))
  have hc₀_ge : max 1 (24 * prob.totalShift) ≤ c₀ := hc1_ge.trans (le_max_left _ _)
  let C_V : ℝ := max C_r C_c
  have hCV_nn : 0 ≤ C_V := le_trans hCr_nn (le_max_left _ _)
  refine ⟨mkUniformAxioms
    c₀ hc₀_ge C_1 hC1_pos (fun {a g} ha hg {t} ht => (hwin ha hg).2 ht)
    C_e hCe_pos
    (fun {c' g} hc' hg {b} hb => (hstrip ((le_max_left _ _).trans hc') hg hb).1)
    (fun {c' g} hc' hg => hcont ((le_max_left _ _).trans ((le_max_right _ _).trans hc')) hg)
    (fun {c' g} hc' hg => hdiff ((le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans hc'))) hg)
    c_low hc_low_pos hfloor
    C_K prob.m hCK_pos (Nat.cast_nonneg _)
    (fun {c' t} hc' ht => hker ((le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hc')))) ht)
    c_band hc_band_pos
    (fun {c' t} hc' ht => hband ((le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc'))))) ht)
    C_V hCV_nn
    (fun {c' x} hcm hx => (hreal hcm hx).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (by linarith [(le_max_left (1 : ℝ) _).trans hcm])))
    (fun {c'} hc' {b} hb1 hb2 hb3 => (hcmplx ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hc'))))) hb1 hb2 hb3).trans
      (div_le_div_of_nonneg_right (le_max_right _ _)
        (lt_of_lt_of_le (by linarith [le_max_left (1 : ℝ) (24 * prob.totalShift)]) (hc₀_ge.trans hc')).le)), rfl⟩

/-- **Unified Lemma 4 (`n1:L4`, parts (a)–(f))**: packages the strip continuation & bound (a),
positivity, Peano floor, and log-convexity (b), comparison (c), sub-Cardy upper bound (d),
threshold window bounds (e), and real/complex asymptotics + Cauchy derivative estimates on
`|b - ξ_*| ≤ 0.1` (f) for every `prob : FixedWeightProblem`. -/
theorem lemma4_summary (prob : FixedWeightProblem) :
    (Nonempty (FixedWeightUniformAxioms prob)) ∧
    (∀ {a : ℝ}, prob.totalShift ≤ a →
      ConvexOn ℝ univ (fun s : ℝ => Real.log (prob.cardyV a (Real.exp s)))) ∧
    (∀ {a t : ℝ}, prob.totalShift ≤ a → 0 ≤ t →
      prob.cardyV a t ≤ (∏ l : Fin prob.m, prob.μ l) * (4 * Real.pi ^ 2 * t) ^ prob.m *
        kernelK prob.w a t) ∧
    (∃ δ : ℝ, 0 < δ ∧ ∃ C c₀ : ℝ, 0 ≤ C ∧ max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ n : ℕ, ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ {c' : ℝ}, c₀ ≤ c' → ∀ x ∈ Set.Icc (0.2 : ℝ) 0.4,
        ‖iteratedDeriv n (cardyErrC prob c') (x : ℂ)‖ ≤ Cn / c') := by
  refine ⟨fixedWeightAxioms_of_problem prob,
    fun ha => cardyV_log_convex prob ha,
    fun ha ht => cardyV_le_pow_mul_kernelK prob ha ht, ?_⟩
  obtain ⟨δ, hδ_pos, C, c₀, hC_nn, hc₀_ge, _, hderiv⟩ :=
    cardyComplexExpansion prob (Set.Icc (0.2 : ℝ) 0.4) isCompact_Icc (fun x hx => lt_of_lt_of_le (by norm_num) hx.1)
  exact ⟨δ, hδ_pos, C, c₀, hC_nn, hc₀_ge, hderiv⟩

/-! ### Section 4: Named instances (Virasoro, `N=1` super-Virasoro, and `U(1)`/`Q = 1`) -/

/-- Spinless Virasoro (`w = 1`, `Q(q) = (1 - q)²`) satisfies `FixedWeightUniformAxioms`
and `FixedWeightUniformP`. -/
theorem virasoro_fixedWeightAxioms :
    Nonempty (FixedWeightUniformAxioms virasoroProblem) ∧
    Nonempty (FixedWeightUniformP virasoroProblem) := by
  obtain ⟨U⟩ := fixedWeightAxioms_of_problem virasoroProblem
  exact ⟨⟨U⟩, ⟨uniformP_of_uniformAxioms U⟩⟩

/-- `N = 1` NS–NS super-Virasoro (`w = 1`, `Q(q) = (1 - q^{1/2})²`) satisfies
`FixedWeightUniformAxioms` and `FixedWeightUniformP`. -/
theorem n1SuperVirasoro_fixedWeightAxioms :
    Nonempty (FixedWeightUniformAxioms n1SuperVirasoroProblem) ∧
    Nonempty (FixedWeightUniformP n1SuperVirasoroProblem) := by
  obtain ⟨U⟩ := fixedWeightAxioms_of_problem n1SuperVirasoroProblem
  exact ⟨⟨U⟩, ⟨uniformP_of_uniformAxioms U⟩⟩

/-- Pure weight-`w` problem with `Q ≡ 1` (`m = 0`) satisfies `FixedWeightUniformAxioms`
and `FixedWeightUniformP` for every integer weight `w ≥ 1`. -/
theorem trivialProduct_fixedWeightAxioms (w : ℕ) (hw : 1 ≤ w) :
    Nonempty (FixedWeightUniformAxioms (FixedWeight.trivialProductProblem w hw)) ∧
    Nonempty (FixedWeightUniformP (FixedWeight.trivialProductProblem w hw)) := by
  obtain ⟨U⟩ := fixedWeightAxioms_of_problem (FixedWeight.trivialProductProblem w hw)
  exact ⟨⟨U⟩, ⟨uniformP_of_uniformAxioms U⟩⟩

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.FixedWeightAxioms.toPropositionPAxioms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FixedWeightAxioms.toPropositionPAxioms

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.fixedWeightAxioms_of_problem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixedWeightAxioms_of_problem

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.fixedWeightAxioms_of_problem_sharp_pK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fixedWeightAxioms_of_problem_sharp_pK

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.lemma4_summary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma4_summary

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.virasoro_fixedWeightAxioms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoro_fixedWeightAxioms

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.n1SuperVirasoro_fixedWeightAxioms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms n1SuperVirasoro_fixedWeightAxioms

/-- info: 'FormalResearch.ModularBootstrap.WeightAxioms.trivialProduct_fixedWeightAxioms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trivialProduct_fixedWeightAxioms

end FormalResearch.ModularBootstrap.WeightAxioms
