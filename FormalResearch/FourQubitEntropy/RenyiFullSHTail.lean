module

public import FormalResearch.FourQubitEntropy.RenyiFullSHSmall
public import FormalResearch.FourQubitEntropy.RenyiFullSHPoly

/-!
# Small-head dual: the small tail `0 ≤ u ≤ 1/4`

Paper E, `lem:fqe-small-head-dual`, "Small tail".  With `h(u) = H_q(u,1-u)`, `A_q` increasing
(`bqA_strictMonoOn`; the paper's concavity is replaced by a finer staircase of node values
`sh_node_0`, …, `sh_node_6`, `RenyiFullSHNodes.lean`) and the deficit (SHD), `Λ_θ ≤ shQ a u ≤ 8023/4800` on each interval.
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.RenyiFull

theorem pur_sh (u δ : ℝ) :
    pur ![(1 - u + δ) / 2, (1 - u - δ) / 2, u / 2, u / 2] = 1 / 2 - u + u ^ 2 + δ ^ 2 / 2 := by
  unfold pur; simp [Fin.sum_univ_four]; ring

theorem cub_sh (u δ : ℝ) :
    cub ![(1 - u + δ) / 2, (1 - u - δ) / 2, u / 2, u / 2] =
      1 / 4 - 3 / 4 * u + 3 / 4 * u ^ 2 + 3 / 4 * (1 - u) * δ ^ 2 := by
  unfold cub; simp [Fin.sum_univ_four]; ring

/-- `A_q ≥ 0`-type bound for small `u`: `H_q(u,1-u) ≤ 4u(1-u)` for `0 < u ≤ 1/100`. -/
theorem binH_small {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1 / 100) : binH qBQ u ≤ 4 * u * (1 - u) := by
  have hq := qS_gt_one
  have hr : 0 < qS - 1 := by linarith
  have hL := log_two_pos'
  have hLb := log2_bounds.1
  have hrL : 0 < (qS - 1) * Real.log 2 := mul_pos hr hL
  have hb := binH_mul_eq hu0 (by linarith)
  have hqs : qS = 1587 / 1000 := rfl
  have hB : 1 - qS * u ≤ (1 - u) ^ qS := by
    have := one_add_mul_self_le_rpow_one_add (s := -u) (p := qS) (by linarith) hq.le
    have e : (1 : ℝ) + -u = 1 - u := by ring
    rw [e] at this
    linarith
  have hqu : qS * u ≤ 1 / 50 := by rw [hqs]; nlinarith
  have hpos : 0 < 1 - qS * u := by linarith
  have hS : 1 - qS * u ≤ (1 - u) ^ qS + u ^ qS := by
    have := Real.rpow_nonneg hu0.le qS
    linarith
  have hlog : Real.log (1 - qS * u) ≤ Real.log ((1 - u) ^ qS + u ^ qS) := Real.log_le_log hpos hS
  have hnl := neg_log_one_sub_le (z := qS * u) (by positivity) (by linarith)
  have hfrac : (qS * u) ^ 2 / (2 * (1 - qS * u)) ≤ (qS * u) ^ 2 / (2 * (49 / 50)) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by linarith)
  have hfrac2 : (qS * u) ^ 2 / (2 * (49 / 50)) = (qS * u) ^ 2 * (25 / 49) := by ring
  by_contra h
  push Not at h
  have h1 := mul_lt_mul_of_pos_right h hrL
  have h2 : 4 * u * (1 - u) * ((qS - 1) * (693147 / 1000000)) ≤ 4 * u * (1 - u) * ((qS - 1) * Real.log 2) := by
    apply mul_le_mul_of_nonneg_left _ (by nlinarith)
    exact mul_le_mul_of_nonneg_left hLb.le hr.le
  rw [hb] at h1
  have h3 : -Real.log ((1 - u) ^ qS + u ^ qS) ≤ qS * u + (qS * u) ^ 2 * (25 / 49) := by linarith
  rw [hqs] at h3 h2 h1
  nlinarith [mul_pos hu0 hu0]

/-- One step of the small tail: `Λ ≤ shQ a u` if `h(u) ≤ 4d - a d(1-2u)²`. -/
theorem sh_tail_step {u δ a : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1 / 4) (hδ0 : 0 ≤ δ) (hδu : δ ≤ u)
    (hh : binH qBQ u ≤ 4 * u * (1 - u) - a * (u * (1 - u) * (1 - 2 * u) ^ 2)) :
    Lam qS aL bL gL ![(1 - u + δ) / 2, (1 - u - δ) / 2, u / 2, u / 2] ≤ shQ a u := by
  have hS := sh_deficit hu0 hu1 hδ0 hδu
  unfold Lam
  rw [pur_sh, cub_sh]
  unfold shQ aL bL gL
  have hv0 : 0 ≤ δ ^ 2 := sq_nonneg δ
  have hv1 : δ ^ 2 ≤ u ^ 2 := by nlinarith
  have hc : 0 ≤ 3 / 200 + 37 / 50 * u - 159 / 100 * u ^ 2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hv1 hc
  have h2 : 0 ≤ (δ ^ 2) ^ 2 := by positivity
  nlinarith [h1, h2, hS, hh]


theorem sh_interval {u δ a lo : ℝ} (hlo0 : 0 < lo) (hlo : lo < 1 / 2) (ha : a ≤ bqA lo) (h1 : lo ≤ u)
    (hu1 : u ≤ 1 / 4) (hδ0 : 0 ≤ δ) (hδu : δ ≤ u) (hq : shQ a u ≤ 8023 / 4800) :
    Lam qS aL bL gL ![(1 - u + δ) / 2, (1 - u - δ) / 2, u / 2, u / 2] ≤ 8023 / 4800 := by
  have hu0 : 0 < u := hlo0.trans_le h1
  have hh := binary_quartic_bound hlo0 hlo ha h1 (by linarith)
  exact (sh_tail_step hu0 hu1 hδ0 hδu hh).trans hq

/-- **Small tail**: `Λ_θ ≤ 8023/4800` on `((1-u+δ)/2, (1-u-δ)/2, u/2, u/2)`, `0 ≤ δ ≤ u ≤ 1/4`. -/
theorem sh_small_tail {u δ : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 4) (hδ0 : 0 ≤ δ) (hδu : δ ≤ u) :
    Lam qS aL bL gL ![(1 - u + δ) / 2, (1 - u - δ) / 2, u / 2, u / 2] ≤ 8023 / 4800 := by
  rcases hu0.eq_or_lt with h | hpos
  · subst h
    have hδ : δ = 0 := le_antisymm hδu hδ0
    subst hδ
    have e : (![(1 - 0 + 0) / 2, (1 - 0 - 0) / 2, 0 / 2, 0 / 2] : Fin 4 → ℝ) = c1 := by
      unfold c1; ext i; fin_cases i <;> simp <;> norm_num
    rw [e, Lam_c1 (by unfold qS; norm_num) (by unfold qS; norm_num)]
    unfold aL bL gL; norm_num
  · have hs : ∀ (a lo : ℝ), 0 < lo → lo < 1 / 2 → a ≤ bqA lo → lo ≤ u → shQ a u ≤ 8023 / 4800 →
        Lam qS aL bL gL ![(1 - u + δ) / 2, (1 - u - δ) / 2, u / 2, u / 2] ≤ 8023 / 4800 :=
      fun a lo h0 h1 ha h2 hq => sh_interval h0 h1 ha h2 hu1 hδ0 hδu hq
    by_cases c0 : u ≤ 1 / 100
    · exact (sh_tail_step hpos hu1 hδ0 hδu (a := 0) (by simpa using binH_small hpos c0)).trans
        ((shQ_le_0 hu0 c0))
    by_cases c1' : u ≤ 3 / 100
    · exact hs _ _ (by norm_num) (by norm_num) sh_node_0 (by linarith) (shQ_le_1 (by linarith) c1')
    by_cases c2 : u ≤ 1 / 20
    · exact hs _ _ (by norm_num) (by norm_num) sh_node_1 (by linarith) (shQ_le_2 (by linarith) c2)
    by_cases c3 : u ≤ 2 / 25
    · exact hs _ _ (by norm_num) (by norm_num) sh_node_2 (by linarith) (shQ_le_3 (by linarith) c3)
    by_cases c4 : u ≤ 13 / 100
    · exact hs _ _ (by norm_num) (by norm_num) sh_node_3 (by linarith) (shQ_le_4 (by linarith) c4)
    by_cases c5 : u ≤ 39 / 200
    · exact hs _ _ (by norm_num) (by norm_num) sh_node_4 (by linarith) (shQ_le_5 (by linarith) c5)
    by_cases c6 : u ≤ 47 / 200
    · exact hs _ _ (by norm_num) (by norm_num) sh_node_5 (by linarith) (shQ_le_6 (by linarith) c6)
    · exact hs _ _ (by norm_num) (by norm_num) sh_node_6 (by linarith) (shQ_le_7 (by linarith) hu1)

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.sh_small_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sh_small_tail

end FormalResearch.FourQubitEntropy.RenyiFull
