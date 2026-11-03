module

public import FormalResearch.FourQubitEntropy.RenyiFullSHBin

/-!
# Small-head dual: `D_q(z) ≥ c z` on `[0, 1/9]`

Paper E, `lem:fqe-small-head-dual`: the paper uses `D_q(z) ≥ D_q'(0) z + D_q''(0) z²/2` (Taylor, `D_q''' > 0`).
Here `D_q` is concave on `[0, 1/9]` (because `D_q'' = G/(rL)` increases, `bqG_strictMonoOn`, and `G(1/3) ≤ 0`),
so `D_q(z) ≥ 9 D_q(1/9) z`; and `D_q(1/9) = 1 - H_q(1/3, 2/3)`.
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.RenyiFull

theorem le_rpow_qS {x b : ℝ} (hb : 0 < b) (hx : 0 < x) (h : b ^ 1000 ≤ x ^ 1587) : b ≤ x ^ qS := by
  have := le_rpow_of_pow_le hb hx (m := 1587) (n := 1000) (by norm_num) h
  have e : qS = ((1587 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) := by unfold qS; norm_num
  rw [e]; exact this

theorem rpow_qS_le {x b : ℝ} (hb : 0 < b) (hx : 0 ≤ x) (h : x ^ 1587 ≤ b ^ 1000) : x ^ qS ≤ b := by
  have := rpow_le_of_le_pow hb hx (m := 1587) (n := 1000) (by norm_num) h
  have e : qS = ((1587 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) := by unfold qS; norm_num
  rw [e]; exact this

theorem le_rpow_qS_Q {x b : ℚ} (hb : 0 < b) (hx : 0 < x) (h : b ^ 1000 ≤ x ^ 1587) :
    ((b : ℚ) : ℝ) ≤ ((x : ℚ) : ℝ) ^ qS :=
  le_rpow_qS (by exact_mod_cast hb) (by exact_mod_cast hx) (by exact_mod_cast h)

theorem rpow_qS_le_Q {x b : ℚ} (hb : 0 < b) (hx : 0 ≤ x) (h : x ^ 1587 ≤ b ^ 1000) :
    ((x : ℚ) : ℝ) ^ qS ≤ ((b : ℚ) : ℝ) :=
  rpow_qS_le (by exact_mod_cast hb) (by exact_mod_cast hx) (by exact_mod_cast h)

theorem two_rpow_qS_ge : (3 : ℝ) ≤ 2 ^ qS := by
  have := le_rpow_qS_Q (b := 3) (x := 2) (by norm_num) (by norm_num) (by decide +kernel)
  simpa using this

theorem bqx_third : 1 / 2 ≤ bqx qS (1 / 3) := by
  have h2 := two_rpow_qS_ge
  have e1 : (1 + 1 / 3 : ℝ) = 2 * (1 - 1 / 3) := by norm_num
  have hp : 0 < ((1 : ℝ) - 1 / 3) ^ qS := Real.rpow_pos_of_pos (by norm_num) _
  unfold bqx
  rw [e1, Real.mul_rpow (by norm_num) (by norm_num)]
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith

theorem bqG_third_nonpos : bqG qS (1 / 3) ≤ 0 := by
  have hx := bqx_third
  have hx1 : bqx qS (1 / 3) ≤ 1 := by
    unfold bqx
    have h1 : 0 < ((1 : ℝ) + 1 / 3) ^ qS := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : 0 < ((1 : ℝ) - 1 / 3) ^ qS := Real.rpow_pos_of_pos (by norm_num) _
    rw [div_le_one (by linarith)]; linarith
  unfold bqG
  set x := bqx qS (1 / 3)
  have hq : qS = 1587 / 1000 := rfl
  rw [hq]
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  nlinarith


/-- `D_q'' ≤ 0` on `(0, 1/9]`. -/
theorem bqD_second_nonpos {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1 / 9) :
    deriv (deriv (bqD qBQ)) v ≤ 0 := by
  have hv1' : v < 1 := by linarith
  rw [deriv2_bqD hv0 hv1']
  have hc : 0 < (qBQ - 1) * Real.log 2 := mul_pos qBQ_sub_one_pos log_two_pos'
  have hs0 : 0 < Real.sqrt v := Real.sqrt_pos.2 hv0
  have hs3 : Real.sqrt v ≤ 1 / 3 := by
    rw [show (1 / 3 : ℝ) = Real.sqrt ((1 / 3) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hG : bqG qBQ (Real.sqrt v) ≤ bqG qBQ (1 / 3) := by
    rcases hs3.eq_or_lt with h | h
    · rw [h]
    · exact (bqG_strictMonoOn ⟨hs0, by linarith⟩ ⟨by norm_num, by norm_num⟩ h).le
  have := bqG_third_nonpos
  rw [show qBQ = qS from rfl] at hG ⊢
  have hc' : 0 < (qS - 1) * Real.log 2 := hc
  exact div_nonpos_of_nonpos_of_nonneg (hG.trans this) hc'.le

theorem bqD_concaveOn : ConcaveOn ℝ (Set.Icc (0 : ℝ) (1 / 9)) (bqD qBQ) := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc 0 (1 / 9))
  · exact bqD_continuousOn.mono (fun x hx => ⟨hx.1, by linarith [hx.2]⟩)
  · intro v hv
    rw [interior_Icc] at hv
    exact ((hasDerivAt_bqD hv.1 (by linarith [hv.2])).differentiableAt).differentiableWithinAt
  · rw [interior_Icc]
    have hd : ∀ v ∈ Set.Ioo (0 : ℝ) (1 / 9), HasDerivAt (deriv (bqD qBQ))
        (deriv (deriv (bqD qBQ)) v) v := by
      intro v hv
      have h1 := hasDerivAt_bqD1 (q := qBQ) hv.1 (by linarith [hv.2] : v < 1)
      have h2 := h1.congr_of_eventuallyEq (deriv_bqD_eventually hv.1 (by linarith [hv.2] : v < 1))
      rw [deriv2_bqD hv.1 (by linarith [hv.2] : v < 1)]
      exact h2
    apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 (1 / 9))
    · intro v hv; exact (hd v hv).continuousAt.continuousWithinAt
    · intro v hv
      rw [interior_Ioo] at hv
      exact (hd v hv).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Ioo] at hv
      exact bqD_second_nonpos hv.1 hv.2.le

/-- Chord bound `D_q(z) ≥ 9 D_q(1/9) z` on `[0, 1/9]`. -/
theorem bqD_chord {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 9) :
    9 * bqD qBQ (1 / 9) * z ≤ bqD qBQ z := by
  have h := bqD_concaveOn.2 (show (1 / 9 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 9) from ⟨by norm_num, le_rfl⟩)
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 9) from ⟨le_rfl, by norm_num⟩)
    (show 0 ≤ 9 * z by linarith) (show 0 ≤ 1 - 9 * z by linarith) (by ring)
  simp only [smul_eq_mul, bqD_zero, mul_zero, add_zero] at h
  have e : 9 * z * (1 / 9) = z := by ring
  rw [e] at h
  linarith

end FormalResearch.FourQubitEntropy.RenyiFull
