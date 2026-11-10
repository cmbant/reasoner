module

public import FormalResearch.PPTThreeQubit.WClass
public import FormalResearch.PPTThreeQubit.Coexistence
public import FormalResearch.PPTThreeQubit.RankProfile

/-!
# The mixed `W` class: the constructed fully-PPT states (`thm:ppt3-w-class`)

Source: `QI/hidden_entanglement/ppt_three_qubit/w_class_decompositions.tex`, `thm:ppt3-w-class`,
using the definition and the atoms of `WClass.lean`.

All operators of the library are unnormalised, and membership in the cone `IsWClass` is the statement
for the normalised state (divide by the trace).  Writing `surfXw A V G W E O` for the coefficient
matrix with diagonal `(A, V, W, E, O)` and `vw` entry `G` in the basis `(u, v, w, e, o)`, the
sandwich `B surfXw B†` is `wForm`; the two decomposition lemmas of the proof are
* `isWClass_wForm_nonpos`: `G = -μ ≤ 0`, diagonal remainder `(A - μ, V - μ, W - μ, E, O)` with
  `A - μ ≤ E + (V - μ)/4` (subtract `μ ([u] + [w - v])`, then the diagonal case `isWClass_wForm_diag`);
* `isWClass_wForm_pos`: `V > 0`, `A ≤ E`, `G² ≤ VW`, `G² ≤ VO` (subtract `A([u] + [e])` and
  `V([v + (G/V)w] + (G/V)²[o])`).

Covered: `ρ_t` for every `0 < t ≤ 12` (the PPT window is inside), `σ_6`, `ρ_{τ,a}` for
`1/√3 < τ < 1` and `a > 0` (the cases `E ≥ 1` and `E < 1` of the proof), the phase-coexistence line
`σ(t)` for `-1/200 ≤ t ≤ 1`, and their images under the diagonal local filters and mixtures with
biseparable noise.
The full-rank state `ρ̃` is in `WClassTilde.lean`.  Not covered: general (non-diagonal) local filters.
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix

noncomputable section

/-- `B_1 X B_1†` for the coefficient matrix `surfXw A V G W E O`. -/
def wForm (A V G W E O : ℝ) : Matrix (Fin 8) (Fin 8) ℂ :=
  Bs 1 * surfXw A V G W E O * (Bs 1)ᴴ

theorem wForm_eq (A V G W E O : ℝ) :
    wForm A V G W E O =
      (A : ℂ) • vecMulVec (uVec 1) (star (uVec 1)) + (W : ℂ) • vecMulVec wVec (star wVec) +
      (V : ℂ) • vecMulVec vVec (star vVec) +
      (G : ℂ) • (vecMulVec wVec (star vVec) + vecMulVec vVec (star wVec)) +
      (E : ℂ) • vecMulVec eVec (star eVec) + (O : ℂ) • vecMulVec oVec (star oVec) :=
  Bs_surfXw_Bs 1 A V G W E O

theorem isWClass_v : IsWClass (vecMulVec vVec (star vVec)) := isWClass_rankOne hyperdet_vVec
theorem isWClass_w : IsWClass (vecMulVec wVec (star wVec)) := isWClass_rankOne hyperdet_wVec
theorem isWClass_e : IsWClass (vecMulVec eVec (star eVec)) := isWClass_rankOne hyperdet_eVec
theorem isWClass_o : IsWClass (vecMulVec oVec (star oVec)) := isWClass_rankOne hyperdet_oVec

/-- A diagonal coefficient matrix with nonnegative weights and `A ≤ E + V/4`. -/
theorem isWClass_wForm_diag {A V W E O : ℝ} (hA : 0 ≤ A) (hV : 0 ≤ V) (hW : 0 ≤ W) (hE : 0 ≤ E)
    (hO : 0 ≤ O) (h : A ≤ E + V / 4) : IsWClass (wForm A V 0 W E O) := by
  rw [wForm_eq]
  by_cases hAE : A ≤ E
  · have key : (A : ℂ) • vecMulVec (uVec 1) (star (uVec 1)) + (W : ℂ) • vecMulVec wVec (star wVec) +
        (V : ℂ) • vecMulVec vVec (star vVec) +
        (((0 : ℝ)) : ℂ) • (vecMulVec wVec (star vVec) + vecMulVec vVec (star wVec)) +
        (E : ℂ) • vecMulVec eVec (star eVec) + (O : ℂ) • vecMulVec oVec (star oVec) =
        (A : ℂ) • (vecMulVec (uVec 1) (star (uVec 1)) + vecMulVec eVec (star eVec)) +
          ((V : ℂ) • vecMulVec vVec (star vVec) + (W : ℂ) • vecMulVec wVec (star wVec)) +
          ((E - A : ℝ) : ℂ) • vecMulVec eVec (star eVec) + (O : ℂ) • vecMulVec oVec (star oVec) := by
      push_cast
      module
    rw [key]
    exact ((((isWClass_u_e.smul hA).add ((isWClass_v.smul hV).add (isWClass_w.smul hW))).add
      (isWClass_e.smul (by linarith))).add (isWClass_o.smul hO))
  · replace hAE := not_le.mp hAE
    have key : (A : ℂ) • vecMulVec (uVec 1) (star (uVec 1)) + (W : ℂ) • vecMulVec wVec (star wVec) +
        (V : ℂ) • vecMulVec vVec (star vVec) +
        (((0 : ℝ)) : ℂ) • (vecMulVec wVec (star vVec) + vecMulVec vVec (star wVec)) +
        (E : ℂ) • vecMulVec eVec (star eVec) + (O : ℂ) • vecMulVec oVec (star oVec) =
        (E : ℂ) • (vecMulVec (uVec 1) (star (uVec 1)) + vecMulVec eVec (star eVec)) +
          ((A - E : ℝ) : ℂ) • (vecMulVec (uVec 1) (star (uVec 1)) +
            (4 : ℂ) • vecMulVec vVec (star vVec)) +
          ((V - 4 * (A - E) : ℝ) : ℂ) • vecMulVec vVec (star vVec) +
          (W : ℂ) • vecMulVec wVec (star wVec) + (O : ℂ) • vecMulVec oVec (star oVec) := by
      push_cast
      module
    rw [key]
    exact ((((isWClass_u_e.smul hE).add (isWClass_u_v.smul (by linarith))).add
      (isWClass_v.smul (by linarith))).add (isWClass_w.smul hW)).add (isWClass_o.smul hO)

/-- Negative cross term `G = -μ`: subtract `μ([u] + [w - v])` (`P([u + i(w - v)])`) and apply the
diagonal case to the remainder `(A - μ, V - μ, W - μ, E, O)`. -/
theorem isWClass_wForm_nonpos {A V W E O μ : ℝ} (hμ : 0 ≤ μ) (hA : μ ≤ A) (hV : μ ≤ V) (hW : μ ≤ W)
    (hE : 0 ≤ E) (hO : 0 ≤ O) (h : A - μ ≤ E + (V - μ) / 4) : IsWClass (wForm A V (-μ) W E O) := by
  have key : wForm A V (-μ) W E O =
      (μ : ℂ) • (vecMulVec (uVec 1) (star (uVec 1)) + vecMulVec (wVec - vVec) (star (wVec - vVec))) +
        wForm (A - μ) (V - μ) 0 (W - μ) E O := by
    rw [wForm_eq, wForm_eq, vecMulVec_sub_star]
    push_cast
    module
  rw [key]
  exact (isWClass_u_wv.smul hμ).add
    (isWClass_wForm_diag (by linarith) (by linarith) (by linarith) hE hO h)

theorem vecMulVec_vbw (b : ℝ) :
    vecMulVec (vVec + (b : ℂ) • wVec) (star (vVec + (b : ℂ) • wVec)) =
      vecMulVec vVec (star vVec) + ((b ^ 2 : ℝ) : ℂ) • vecMulVec wVec (star wVec) +
        (b : ℂ) • (vecMulVec wVec (star vVec) + vecMulVec vVec (star wVec)) := by
  ext i j
  simp only [vecMulVec_apply, Pi.add_apply, Pi.smul_apply, Pi.star_apply, star_add, star_smul,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

/-- Cross term `G = V b` with `V > 0`: `A([u] + [e]) + V([v + b w] + b²[o])` plus nonnegative
diagonal remainders (`W - V b²`, `E - A`, `O - V b²`). -/
theorem isWClass_wForm_pos' {A V W E O b : ℝ} (hA : 0 ≤ A) (hV : 0 ≤ V) (hAE : A ≤ E)
    (hW : V * b ^ 2 ≤ W) (hO : V * b ^ 2 ≤ O) : IsWClass (wForm A V (V * b) W E O) := by
  have key : wForm A V (V * b) W E O =
      (A : ℂ) • (vecMulVec (uVec 1) (star (uVec 1)) + vecMulVec eVec (star eVec)) +
        (V : ℂ) • (vecMulVec (vVec + (b : ℂ) • wVec) (star (vVec + (b : ℂ) • wVec)) +
          ((b ^ 2 : ℝ) : ℂ) • vecMulVec oVec (star oVec)) +
        ((W - V * b ^ 2 : ℝ) : ℂ) • vecMulVec wVec (star wVec) +
        ((E - A : ℝ) : ℂ) • vecMulVec eVec (star eVec) +
        ((O - V * b ^ 2 : ℝ) : ℂ) • vecMulVec oVec (star oVec) := by
    rw [wForm_eq, vecMulVec_vbw]
    push_cast
    module
  rw [key]
  exact ((((isWClass_u_e.smul hA).add ((isWClass_v_bw b).smul hV)).add (isWClass_w.smul (by linarith))).add
    (isWClass_e.smul (by linarith))).add (isWClass_o.smul (by linarith))

/-- `isWClass_wForm_pos'` in terms of the cross entry `G`. -/
theorem isWClass_wForm_pos {A V G W E O : ℝ} (hA : 0 ≤ A) (hV : 0 < V) (hAE : A ≤ E)
    (hW : G ^ 2 ≤ V * W) (hO : G ^ 2 ≤ V * O) : IsWClass (wForm A V G W E O) := by
  obtain ⟨b, rfl⟩ : ∃ b, G = V * b := ⟨G / V, by field_simp⟩
  refine isWClass_wForm_pos' hA hV.le hAE ?_ ?_
  · refine le_of_mul_le_mul_left ?_ hV
    nlinarith
  · refine le_of_mul_le_mul_left ?_ hV
    nlinarith

/-! ### The first family and `σ_6` -/

theorem Xt_eq_surfXw (t : ℝ) (ht : 0 < t) :
    Xt t = surfXw (t / (7 * (t + 3))) (3 * t / (7 * (t + 3))) 0 (3 / (7 * (t + 3)))
      (3 / (7 * (t + 3))) (1 / (7 * (t + 3))) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xt, surfXw, diagonal_apply]

/-- **`thm:ppt3-w-class`, the first family.**  `ρ_t` lies in the mixed `W` class for `0 < t ≤ 12`,
in particular throughout the PPT interval `[t_-, t_+]`. -/
theorem isWClass_rhoT {t : ℝ} (ht : 0 < t) (h12 : t ≤ 12) : IsWClass (rhoT t) := by
  have hN : 0 < 7 * (t + 3) := by positivity
  have : rhoT t = wForm (t / (7 * (t + 3))) (3 * t / (7 * (t + 3))) 0 (3 / (7 * (t + 3)))
      (3 / (7 * (t + 3))) (1 / (7 * (t + 3))) := by
    rw [wForm, ← Xt_eq_surfXw t ht]; rfl
  rw [this]
  refine isWClass_wForm_diag (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) ?_
  have h : 3 / (7 * (t + 3)) + 3 * t / (7 * (t + 3)) / 4 - t / (7 * (t + 3)) =
      (12 - t) / (4 * (7 * (t + 3))) := by
    field_simp; ring
  have := div_nonneg (sub_nonneg.2 h12) (by positivity : 0 ≤ 4 * (7 * (t + 3)))
  linarith

/-- `ρ_t` is in the mixed `W` class on the whole PPT interval. -/
theorem isWClass_rhoT_window {t : ℝ} (h1 : tMinus ≤ t) (h2 : t ≤ tPlus) : IsWClass (rhoT t) := by
  have h3 := three_lt_tMinus
  have hp := tPlus_facts t (by linarith) h2
  exact isWClass_rhoT (by linarith) (by nlinarith)

theorem X6_eq_surfXw :
    X6 = surfXw (sigma6A / sigma6N) (sigma6B / sigma6N) 0 (3 / sigma6N) (3 / sigma6N)
      (1 / sigma6N) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [X6, surfXw, diagonal_apply]

/-- **`thm:ppt3-w-class`, the extreme state `σ_6`.** -/
theorem isWClass_sigma6 : IsWClass sigma6 := by
  obtain ⟨hN, hA, hB⟩ := sigma6_pos
  have h1 := tMinus_lt_ten_thirds
  have : sigma6 = wForm (sigma6A / sigma6N) (sigma6B / sigma6N) 0 (3 / sigma6N) (3 / sigma6N)
      (1 / sigma6N) := by
    rw [sigma6, wForm, ← X6_eq_surfXw]
  rw [this]
  refine isWClass_wForm_diag (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) ?_
  have h : 3 / sigma6N + sigma6B / sigma6N / 4 - sigma6A / sigma6N =
      (3 + sigma6B / 4 - sigma6A) / sigma6N := by
    field_simp
  have h2 : 0 ≤ 3 + sigma6B / 4 - sigma6A := by
    simp only [sigma6A, sigma6B]; linarith
  have := div_nonneg h2 hN.le
  linarith

/-! ### The surface -/

/-- `O V - G² = 2E - 1` (`eq:ppt3-w-budget`). -/
theorem qO_mul_qV_sub {Q : ℝ} (hQ : 1 < Q) : qO Q * qV Q - qG Q ^ 2 = 2 * qE Q - 1 := by
  have hQ0 : Q ≠ 0 := by positivity
  have hN : Q ^ 2 - 1 ≠ 0 := by nlinarith
  unfold qO qV qG qE qk
  field_simp
  ring

/-- **`thm:ppt3-w-class`, the surface at `a = 1`, in the coordinate `Q`.**  The two cases of the proof
are `E ≥ 1` (`isWClass_wForm_pos`) and `E < 1` (`isWClass_wForm_nonpos`, `μ = -G`). -/
theorem isWClass_rhoQ {Q : ℝ} (hQ : 1 < Q) (h3 : 3 < Q ^ 2) (hk : qk Q < 0) :
    IsWClass (rhoQ Q) := by
  have hQ0 : 0 < Q := by linarith
  have hN : 0 < Q ^ 2 - 1 := by nlinarith
  have hfac : qk Q = (Q ^ 2 - 2 * Q - 1) * (Q ^ 2 + 2 * Q - 1) := by unfold qk; ring
  have hlt : Q ^ 2 - 2 * Q - 1 < 0 := by
    by_contra hc
    have hc := not_lt.mp hc
    have : 0 ≤ (Q ^ 2 - 2 * Q - 1) * (Q ^ 2 + 2 * Q - 1) := mul_nonneg hc (by nlinarith)
    linarith
  have hk' : Q ^ 4 - 6 * Q ^ 2 + 1 < 0 := by unfold qk at hk; exact hk
  have hQ6 : Q ^ 2 < 6 := by nlinarith [sq_nonneg Q]
  have hV : 0 < qV Q := by
    unfold qV
    have : 0 < Q * (Q ^ 2 - 1) * (6 - Q ^ 2) := mul_pos (mul_pos hQ0 hN) (by linarith)
    linarith
  rw [rhoQ_eq_sandwich]
  show IsWClass (wForm 1 (qV Q) (qG Q) (qT Q) (qE Q) (qO Q))
  by_cases hE : 1 ≤ qE Q
  · refine isWClass_wForm_pos zero_le_one hV hE ?_ ?_
    · have h := qT_mul_qV_sub hQ0
      nlinarith [mul_pos (sub_pos.2 h3) (neg_pos.2 hk)]
    · have h := qO_mul_qV_sub hQ
      nlinarith
  · have hE := not_le.mp hE
    have h5 : 5 < Q ^ 2 := by
      by_contra hc
      have hc := not_lt.mp hc
      have hE' : qE Q = -qk Q / 4 := rfl
      have : 0 < (Q ^ 2 - 1) * (Q ^ 2 - 5) := by nlinarith
      nlinarith
    have hG : qG Q ≤ 0 := by
      unfold qG
      have : 0 ≤ Q * (Q ^ 2 - 5) := mul_nonneg hQ0.le (by linarith)
      nlinarith
    have hμA : -qG Q ≤ 1 := by
      unfold qG
      nlinarith [mul_neg_of_pos_of_neg (by linarith : 0 < Q + 2) hlt]
    have hμV : -qG Q ≤ qV Q := by
      have : qV Q + qG Q = -Q * qk Q / 2 := by unfold qV qG qk; ring
      nlinarith [mul_pos hQ0 (neg_pos.2 hk)]
    have hμW : -qG Q ≤ qT Q := by
      have : qT Q + qG Q = -qk Q / (2 * Q) := by unfold qT qG qk; field_simp; ring
      have h2 : 0 ≤ -qk Q / (2 * Q) := div_nonneg (by linarith) (by positivity)
      linarith
    have hE0 : 0 ≤ qE Q := by unfold qE; linarith
    have hO0 : 0 ≤ qO Q := qO_nonneg hQ hk.le
    have hc : 0 ≤ qE Q - 1 - qG Q := by
      have : qE Q - 1 - qG Q = (Q ^ 2 - 5) * (-(Q ^ 2 - 2 * Q - 1)) / 4 := by
        unfold qE qG qk; ring
      rw [this]
      have : 0 ≤ (Q ^ 2 - 5) * (-(Q ^ 2 - 2 * Q - 1)) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
    have := isWClass_wForm_nonpos (A := 1) (V := qV Q) (W := qT Q) (E := qE Q) (O := qO Q)
      (μ := -qG Q) (by linarith) hμA hμV hμW hE0 hO0 (by linarith)
    rwa [neg_neg] at this

/-- **`thm:ppt3-w-class`, the surface.**  `ρ_{τ,a} = ρ(1, τ, a)` is in the mixed `W` class for every
`1/√3 < τ < 1` and `a > 0` (the filter law `rhoSurface_filter` reduces to `a = 1`; diagonal local
filters preserve the class). -/
theorem isWClass_rhoSurface {τ : ℝ} (a : ℝ) (h1 : 1 / Real.sqrt 3 < τ) (h2 : τ < 1) (ha : 0 < a) :
    IsWClass (rhoSurface 1 τ a) := by
  obtain ⟨Q, hQ, h3, hk, hr⟩ := window_Q h1 h2
  have hτ0 : 0 < τ := lt_trans (by positivity) h1
  have hl : (Real.sqrt a⁻¹) ^ 2 = a⁻¹ := Real.sq_sqrt (inv_nonneg.mpr ha.le)
  have hf := rhoSurface_filter one_pos hτ0 h2 ha hl
  rw [mul_one] at hf
  have h0 := isWClass_rhoQ hQ h3 hk
  rw [← hr] at h0
  rw [hf]
  exact (h0.filterDiag (Real.sqrt a⁻¹)).smul ha.le

/-- **`thm:ppt3-w-class`, the rational member `σ` of `cor:ppt3-extreme5`.** -/
theorem isWClass_sigma5 : IsWClass sigma5 := by
  rw [sigma5_eq_orbit]
  exact (isWClass_rhoSurface 2 window_48_55 (by norm_num) (by norm_num)).smul (by norm_num)

/-! ### The phase-coexistence line -/

theorem Xline_neg_eq : Xline (-1 / 200) =
    surfXw (213211157 / 2436000000) (413586193 / 2436000000) (-(10930399 / 348000000))
      (28362199 / 348000000) (1361527 / 24360000) (551683 / 24360000) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xline, Xd, XBS, surfXw] <;> norm_num

/-- **`thm:ppt3-w-class`, the phase-coexistence line.**  `σ(t) = (1-t)σ_∂ + tσ_BS` is in the mixed
`W` class for `-1/200 ≤ t ≤ 1`: biseparable for `t ≥ 0`, and at `t = -1/200` the coefficient matrix has
`(v, w)` entry `-μ`, `μ = 10930399/348000000`, and the remainder is diagonal with
`A - μ - E = 7/31250 ≤ (V - μ)/4` (`isWClass_wForm_nonpos`); the interval follows by convexity. -/
theorem isWClass_sigmaLine {t : ℝ} (h1 : -1 / 200 ≤ t) (h2 : t ≤ 1) : IsWClass (sigmaLine t) := by
  by_cases h0 : 0 ≤ t
  · exact (ppt3_exposed_transition.2.1 t h0 h2).isWClass
  · have h0 := not_le.mp h0
    -- `σ(t)` is a convex combination of `σ(-1/200)` and `σ(0) = σ_∂`
    have hend : IsWClass (sigmaLine (-1 / 200)) := by
      rw [sigmaLine_eq, Xline_neg_eq]
      exact isWClass_wForm_nonpos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
    have hD : IsWClass (sigmaLine 0) := (ppt3_exposed_transition.2.1 0 le_rfl (by norm_num)).isWClass
    -- `σ(t) = λ σ(-1/200) + (1-λ) σ(0)` with `λ = -200 t ∈ (0, 1]`
    have hcomb : sigmaLine t = ((-200 * t : ℝ) : ℂ) • sigmaLine (-1 / 200) +
        ((1 + 200 * t : ℝ) : ℂ) • sigmaLine 0 := by
      ext i j
      simp only [sigmaLine, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [hcomb]
    exact (hend.smul (by linarith)).add (hD.smul (by linarith))

/-- **`thm:ppt3-w-class`** (explicit states other than `ρ̃`).  Each constructed state lies in the mixed
`W` class; where it is GME (the stated ranges) it lies in `W ∖ BS`.  `ρ_t`, `ρ_{τ,a}` are fully PPT
there (`ppt3_family_ppt`, `ppt3_orbit_ppt`); `σ_6` and the line are covered by
`isWClass_sigma6`, `isWClass_sigmaLine`. -/
theorem ppt3_w_class :
    (∀ t : ℝ, tMinus ≤ t → t ≤ tPlus →
      IsPPT3 (rhoT t) ∧ IsGME (rhoT t) ∧ IsWClass (rhoT t)) ∧
    IsWClass sigma6 ∧
    (∀ (τ a : ℝ), 1 / Real.sqrt 3 < τ → τ < 1 → 0 < a →
      IsPPT3 (rhoSurface 1 τ a) ∧ IsGME (rhoSurface 1 τ a) ∧ IsWClass (rhoSurface 1 τ a)) ∧
    (∀ t : ℝ, -1 / 200 ≤ t → t ≤ 1 → IsWClass (sigmaLine t)) ∧
    (∀ t : ℝ, -1 / 200 ≤ t → t < 0 → IsWClass (sigmaLine t) ∧ IsGME (sigmaLine t)) :=
  ⟨fun t h1 h2 => ⟨ppt3_family_ppt t h1 h2, ppt3_family_gme_of_tMinus_le t h1,
      isWClass_rhoT_window h1 h2⟩,
    isWClass_sigma6,
    fun τ a h1 h2 ha => ⟨(ppt3_orbit_ppt a h1 h2 ha).2, ppt3_orbit_gme a h1 h2 ha,
      isWClass_rhoSurface a h1 h2 ha⟩,
    fun _ h1 h2 => isWClass_sigmaLine h1 h2,
    fun t h1 h2 => ⟨isWClass_sigmaLine h1 (by linarith), ppt3_exposed_transition.2.2 t h1 h2⟩⟩

end

/-- info: 'FormalResearch.PPTThreeQubit.isWClass_wForm_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isWClass_wForm_diag

/-- info: 'FormalResearch.PPTThreeQubit.isWClass_wForm_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isWClass_wForm_nonpos

/-- info: 'FormalResearch.PPTThreeQubit.isWClass_wForm_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isWClass_wForm_pos

/-- info: 'FormalResearch.PPTThreeQubit.isWClass_rhoT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isWClass_rhoT

/-- info: 'FormalResearch.PPTThreeQubit.isWClass_sigma6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isWClass_sigma6

/-- info: 'FormalResearch.PPTThreeQubit.isWClass_rhoQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isWClass_rhoQ

/-- info: 'FormalResearch.PPTThreeQubit.isWClass_rhoSurface' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isWClass_rhoSurface

/-- info: 'FormalResearch.PPTThreeQubit.isWClass_sigma5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isWClass_sigma5

/-- info: 'FormalResearch.PPTThreeQubit.isWClass_sigmaLine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isWClass_sigmaLine

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_w_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppt3_w_class

end FormalResearch.PPTThreeQubit
