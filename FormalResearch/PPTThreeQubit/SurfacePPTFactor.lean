module

public import FormalResearch.PPTThreeQubit.FamilyPPT
public import FormalResearch.PPTThreeQubit.Surface

/-!
# The rank-five surface at `α = A = 1`: the `LDL*` factorization of `ρ_τ^{T_A}`

Source: `ResearchNotes/QI/finite_copy_invariant_inference/ppt_three_qubit/rank_five_surface.tex`,
proof of `thm:ppt3-orbit`, "Rank and PPT" (`eq:ppt3-surface-simpledet`,
`eq:ppt3-surface-minors`).

In the coordinate `Q = τ + √(1+τ²)` the weights of `ρ_τ = ρ(1, τ, 1)` are rational in `Q`
(with `k = Q⁴ - 6Q² + 1 = -4Q²κ`):
`τ = (Q²-1)/(2Q)`, `O = -k/(2Q(Q²-1))`, `E = -k/4`, `G = Q(5-Q²)/2`, `V = Q(Q²-1)(6-Q²)/2`.
`rhoQ Q` is the operator with these weights.  This file proves, for every real `Q ≠ 0, ±1`,
the entrywise identity `ρ_Q^{T_A} = ∑ₖ dₖ |lₖ⟩⟨lₖ|` with five columns (three on the even parity
block `(000,011,101,110)`, two on the odd block `(001,010,100,111)`) and the pivots
`dpivQ` (`ptA_rhoQ_eq`); the pivots are the ratios of consecutive leading minors of
`eq:ppt3-surface-minors` (`1, E, (Q²-3)(Q⁴+3)κ²/(4τ²)`) and the zero fourth even pivot is the
singularity of the even block.  The positivity consequences are in `SurfacePPT.lean`.
-/

@[expose] public section


namespace FormalResearch.PPTThreeQubit

open Matrix

noncomputable section

/-- `k(Q) = Q⁴ - 6Q² + 1` (`= -4Q²κ`, negative exactly for `1 < Q < 1 + √2`). -/
def qk (Q : ℝ) : ℝ := Q ^ 4 - 6 * Q ^ 2 + 1

/-- `τ = (Q² - 1)/(2Q)`. -/
def qT (Q : ℝ) : ℝ := (Q ^ 2 - 1) / (2 * Q)
/-- `O = κ/τ = -k/(2Q(Q²-1))`. -/
def qO (Q : ℝ) : ℝ := -qk Q / (2 * Q * (Q ^ 2 - 1))
/-- `E = κ Q² = -k/4`. -/
def qE (Q : ℝ) : ℝ := -qk Q / 4
/-- `G = (E-1)/τ = Q(5-Q²)/2`. -/
def qG (Q : ℝ) : ℝ := Q * (5 - Q ^ 2) / 2
/-- `V = (E² - 2κE + κ)/(τκ) = Q(Q²-1)(6-Q²)/2`. -/
def qV (Q : ℝ) : ℝ := Q * (Q ^ 2 - 1) * (6 - Q ^ 2) / 2

/-- `ρ_τ = ρ(1, τ, 1)` written with the weights in the coordinate `Q`
(`eq:ppt3-rho-surface`, `α = A = 1`). -/
def rhoQ (Q : ℝ) : Matrix (Fin 8) (Fin 8) ℂ :=
  vecMulVec (uVec 1) (star (uVec 1)) + (qT Q : ℂ) • vecMulVec wVec (star wVec) +
    (qV Q : ℂ) • vecMulVec vVec (star vVec) +
    (qG Q : ℂ) • (vecMulVec wVec (star vVec) + vecMulVec vVec (star wVec)) +
    (qE Q : ℂ) • vecMulVec eVec (star eVec) + (qO Q : ℂ) • vecMulVec oVec (star oVec)

theorem rhoQ_apply (Q : ℝ) (i j : Fin 8) :
    rhoQ Q i j = uVec 1 i * star (uVec 1 j) + (qT Q : ℂ) * (wVec i * star (wVec j)) +
      (qV Q : ℂ) * (vVec i * star (vVec j)) +
      (qG Q : ℂ) * (wVec i * star (vVec j) + vVec i * star (wVec j)) +
      (qE Q : ℂ) * (eVec i * star (eVec j)) + (qO Q : ℂ) * (oVec i * star (oVec j)) := by
  simp only [rhoQ, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul]

/-- The columns `l_k` of the factor: `k = 0,1,2` on the even block, `k = 3,4` on the odd block. -/
def lq (Q : ℝ) : Fin 5 → Fin 8 → ℂ := ![
  ![1, 0, 0, -1, 0, cw ((Q ^ 4 - 4 * Q ^ 2 + 1) / (Q * (Q ^ 2 - 1))) (qk Q / (2 * Q * (Q ^ 2 - 1))),
    cw ((Q ^ 2 - 1) / (2 * Q)) (-qk Q / (2 * Q * (Q ^ 2 - 1))), 0],
  ![0, 0, 0, 1, 0, cw (2 * (Q ^ 2 - 2) / (Q * (Q ^ 2 - 1))) (-2 / (Q * (Q ^ 2 - 1))),
    cw (2 / Q) (2 / (Q * (Q ^ 2 - 1))), 0],
  ![0, 0, 0, 0, 0, 1, cw (-4 * Q ^ 2 / (Q ^ 4 + 3)) ((Q ^ 2 - 3) * (Q ^ 2 + 1) / (Q ^ 4 + 3)), 0],
  ![0, 1, cw ((Q ^ 4 - 4 * Q ^ 2 + 1) / (2 * Q ^ 2)) (qk Q / (4 * Q ^ 2)),
    0, cw (-(Q ^ 2 - 1) / (2 * Q)) 0, 0, 0,
    cw ((Q ^ 2 - 1) ^ 2 * (Q ^ 2 - 5) / (8 * Q)) ((Q ^ 2 - 1) * qk Q / (8 * Q))],
  ![0, 0, 1, 0, cw (-2 * Q / (3 * (Q ^ 2 - 1))) (2 * Q / (3 * (Q ^ 2 - 1))), 0, 0,
    cw (Q * (Q ^ 2 - 3) / 3) (Q * (Q ^ 2 + 3) / 6)]]

/-- The pivots: ratios of consecutive leading minors (`eq:ppt3-surface-minors`). -/
def dpivQ (Q : ℝ) : Fin 5 → ℝ := ![1, -qk Q / 4,
  -((Q ^ 2 - 3) * (Q ^ 4 + 3) * qk Q) / (4 * Q ^ 2 * (Q ^ 2 - 1) ^ 2),
  2 * Q / (Q ^ 2 - 1), -3 * (Q ^ 2 - 1) * qk Q / (8 * Q ^ 3)]


set_option maxHeartbeats 8000000 in
/-- Entrywise form of the `LDL*` factorization of `ρ_Q^{T_A}`. -/
theorem ptA_rhoQ_entry (Q : ℝ) (hQ : Q ≠ 0) (hQ1 : Q ^ 2 - 1 ≠ 0) (i j : Fin 8) :
    ptA (rhoQ Q) i j = ∑ k, (dpivQ Q k : ℂ) * lq Q k i * star (lq Q k j) := by
  have h2 : ω ^ 2 = -1 - ω := by linear_combination ω_sq_add_ω_add_one
  have hQ' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ
  have hQ1' : (Q : ℂ) ^ 2 - 1 ≠ 0 := by exact_mod_cast hQ1
  have hQ4 : (Q : ℂ) ^ 4 + 3 ≠ 0 := by
    have : Q ^ 4 + 3 ≠ 0 := by positivity
    exact_mod_cast this
  simp only [ptA, of_apply, rhoQ_apply]
  fin_cases i <;> fin_cases j <;>
    simp [uVec, vVec, wVec, eVec, oVec, Fin.sum_univ_five, lq, dpivQ, qT, qV, qG, qE, qO, qk,
      conj_cw, conj_ω, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
  all_goals
    try simp only [cw]
    try push_cast
    try field_simp
    try ring_nf
    try simp only [ω_cube, ω_pow4, ω_pow5, ω_pow6, h2]
    try ring_nf

end
end FormalResearch.PPTThreeQubit
