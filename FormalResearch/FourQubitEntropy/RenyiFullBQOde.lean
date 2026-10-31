import Mathlib

/-!
# Binary quartic lemma: the hyperbolic coordinate `x(s)` and its Riccati equation

Paper E, `lem:fqe-binary-quartic` (`renyi_binary_quartic.tex`), real-variable proof.  With `s = tanh φ`
and `x = tanh(qφ)` one has `x(s) = ((1+s)^q - (1-s)^q)/((1+s)^q + (1-s)^q)`; this file proves
`x' = q(1-x²)/(1-s²)` and `s < x < 1` for `0 < s < 1`, `q > 1`.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

/-- `x(s) = ((1+s)^q - (1-s)^q)/((1+s)^q + (1-s)^q) = tanh(q artanh s)`. -/
noncomputable def bqx (q s : ℝ) : ℝ :=
  ((1 + s) ^ q - (1 - s) ^ q) / ((1 + s) ^ q + (1 - s) ^ q)

theorem bq_denom_pos {s : ℝ} (hs : |s| < 1) (q : ℝ) : 0 < (1 + s) ^ q + (1 - s) ^ q := by
  have h1 := abs_lt.1 hs
  have a : 0 < (1 + s) ^ q := Real.rpow_pos_of_pos (by linarith) q
  have b : 0 < (1 - s) ^ q := Real.rpow_pos_of_pos (by linarith) q
  linarith

theorem bqx_zero (q : ℝ) : bqx q 0 = 0 := by simp [bqx]

/-- The Riccati equation `x' = q (1 - x²)/(1 - s²)`. -/
theorem hasDerivAt_bqx {q s : ℝ} (hs : |s| < 1) :
    HasDerivAt (bqx q) (q * (1 - bqx q s ^ 2) / (1 - s ^ 2)) s := by
  have h1 := abs_lt.1 hs
  have hp : (0 : ℝ) < 1 + s := by linarith
  have hm : (0 : ℝ) < 1 - s := by linarith
  have ha : HasDerivAt (fun s : ℝ => (1 + s) ^ q) (q * (1 + s) ^ q / (1 + s)) s := by
    have := ((hasDerivAt_id s).const_add 1).rpow_const (p := q) (Or.inl hp.ne')
    refine this.congr_deriv ?_
    simp only [id]
    rw [Real.rpow_sub_one hp.ne']
    ring
  have hb : HasDerivAt (fun s : ℝ => (1 - s) ^ q) (-(q * (1 - s) ^ q / (1 - s))) s := by
    have := ((hasDerivAt_id s).const_sub 1).rpow_const (p := q) (Or.inl hm.ne')
    refine this.congr_deriv ?_
    simp only [id]
    rw [Real.rpow_sub_one hm.ne']
    ring
  have hden := bq_denom_pos hs q
  have := (ha.sub hb).div (ha.add hb) hden.ne'
  unfold bqx
  refine this.congr_deriv ?_
  simp only [Pi.add_apply, Pi.sub_apply]
  set a := (1 + s) ^ q
  set b := (1 - s) ^ q
  have ha0 : 0 < a := Real.rpow_pos_of_pos hp q
  have hb0 : 0 < b := Real.rpow_pos_of_pos hm q
  have h2 : (1 : ℝ) - s ^ 2 = (1 + s) * (1 - s) := by ring
  rw [h2]
  field_simp
  ring

theorem bqx_gt {q s : ℝ} (hq : 1 < q) (hs0 : 0 < s) (hs1 : s < 1) : s < bqx q s := by
  have hp : (0 : ℝ) < 1 + s := by linarith
  have hm : (0 : ℝ) < 1 - s := by linarith
  have hlt : (1 - s) ^ (q - 1) < (1 + s) ^ (q - 1) :=
    Real.rpow_lt_rpow hm.le (by linarith) (by linarith)
  have e1 : (1 + s) ^ q = (1 + s) ^ (q - 1) * (1 + s) := by
    rw [← Real.rpow_add_one hp.ne']; ring_nf
  have e2 : (1 - s) ^ q = (1 - s) ^ (q - 1) * (1 - s) := by
    rw [← Real.rpow_add_one hm.ne']; ring_nf
  have hden := bq_denom_pos (s := s) (by rw [abs_lt]; constructor <;> linarith) q
  unfold bqx
  rw [lt_div_iff₀ hden]
  rw [e1, e2]
  nlinarith [mul_pos (mul_pos hp hm) (sub_pos.2 hlt), Real.rpow_pos_of_pos hm (q - 1)]

theorem bqx_lt_one {q s : ℝ} (hs : |s| < 1) : bqx q s < 1 := by
  have h1 := abs_lt.1 hs
  have hden := bq_denom_pos hs q
  have b : 0 < (1 - s) ^ q := Real.rpow_pos_of_pos (by linarith) q
  unfold bqx
  rw [div_lt_one hden]
  linarith


/-! ### The rational upper bound `U = P/Q` -/

/-- `15 P`. -/
noncomputable def bqPn (q s : ℝ) : ℝ := q * s * (15 + (q ^ 2 + 6 * q - 25) * s ^ 2 + (q - 2) * (q - 4) * s ^ 4)

/-- `15 Q`. -/
noncomputable def bqQn (q s : ℝ) : ℝ :=
  15 + 6 * (q ^ 2 + q - 5) * s ^ 2 + (2 * q ^ 3 - 6 * q ^ 2 - 8 * q + 15) * s ^ 4

/-- `U = P/Q`. -/
noncomputable def bqU (q s : ℝ) : ℝ := bqPn q s / bqQn q s

/-- The derivative of `bqPn` in `s`. -/
noncomputable def bqPn' (q s : ℝ) : ℝ :=
  q * (15 + 3 * (q ^ 2 + 6 * q - 25) * s ^ 2 + 5 * (q - 2) * (q - 4) * s ^ 4)

/-- The derivative of `bqQn` in `s`. -/
noncomputable def bqQn' (q s : ℝ) : ℝ :=
  12 * (q ^ 2 + q - 5) * s + 4 * (2 * q ^ 3 - 6 * q ^ 2 - 8 * q + 15) * s ^ 3

/-- The constant `κ(q) = q(q²-1)(2-q)(3-q)(4-q)(5-q)` of the Riccati residual. -/
noncomputable def bqKap (q : ℝ) : ℝ := q * (q ^ 2 - 1) * (2 - q) * (3 - q) * (4 - q) * (5 - q)

theorem bqKap_pos {q : ℝ} (h1 : 1 < q) (h2 : q < 2) : 0 < bqKap q := by
  unfold bqKap
  have a1 : 0 < q := by linarith
  have a2 : 0 < q ^ 2 - 1 := by nlinarith
  have a3 : 0 < 2 - q := by linarith
  have a4 : 0 < 3 - q := by linarith
  have a5 : 0 < 4 - q := by linarith
  have a6 : 0 < 5 - q := by linarith
  positivity

theorem bqQn_pos {q s : ℝ} (h1 : 1 < q) (h2 : q < 2) (hs : |s| < 1) : 0 < bqQn q s := by
  have hs2 : s ^ 2 < 1 := by
    have := abs_lt.1 hs
    nlinarith
  have hs0 : 0 ≤ s ^ 2 := sq_nonneg s
  have hc : 2 * q ^ 3 - 6 * q ^ 2 - 8 * q + 15 < 15 := by nlinarith
  have hq : 0 < 2 * q * (q ^ 2 - 1) := by nlinarith
  have hpos : 0 < 15 - (2 * q ^ 3 - 6 * q ^ 2 - 8 * q + 15) * s ^ 2 := by
    rcases le_or_gt (2 * q ^ 3 - 6 * q ^ 2 - 8 * q + 15) 0 with h | h
    · nlinarith
    · nlinarith
  have key : bqQn q s = (1 - s ^ 2) * (15 - (2 * q ^ 3 - 6 * q ^ 2 - 8 * q + 15) * s ^ 2)
      + 2 * q * (q ^ 2 - 1) * s ^ 2 := by unfold bqQn; ring
  rw [key]
  have := mul_pos (sub_pos.2 hs2) hpos
  nlinarith [mul_nonneg hq.le hs0]

/-- `Q - P = (1-s)² W / 15` with `W ≥ 3`: hence `U < 1` for `0 ≤ s < 1`. -/
theorem bqU_lt_one {q s : ℝ} (h1 : 1 < q) (h2 : q < 2) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    bqU q s < 1 := by
  have hQ := bqQn_pos h1 h2 (s := s) (by rw [abs_lt]; constructor <;> linarith)
  unfold bqU
  rw [div_lt_one hQ]
  have key : bqQn q s - bqPn q s = (1 - s) ^ 2 * (15 + 15 * (2 - q) * s +
      (6 * (q - 2) ^ 2 - 9) * s ^ 2 - q * (q - 2) * (q - 4) * s ^ 3) := by
    unfold bqQn bqPn; ring
  have hc1 : q * (q - 2) * (q - 4) ≤ 3 := by nlinarith [mul_pos (sub_pos.2 h1) (sub_pos.2 h2)]
  have hc0 : 0 ≤ q * (q - 2) * (q - 4) := by
    have : 0 ≤ (2 - q) * (4 - q) := by nlinarith
    nlinarith
  have hW : 3 ≤ 15 + 15 * (2 - q) * s + (6 * (q - 2) ^ 2 - 9) * s ^ 2 - q * (q - 2) * (q - 4) * s ^ 3 := by
    have e1 : 0 ≤ 15 * (2 - q) * s := by
      have : 0 ≤ 2 - q := by linarith
      positivity
    have e2 : (6 * (q - 2) ^ 2 - 9) * s ^ 2 ≥ -9 := by
      have : s ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (q - 2), sq_nonneg s]
    have e3 : q * (q - 2) * (q - 4) * s ^ 3 ≤ 3 := by
      have : s ^ 3 ≤ 1 := by
        calc s ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ hs0 hs1.le 3
          _ = 1 := by norm_num
      have h3 : 0 ≤ s ^ 3 := by positivity
      nlinarith
    linarith
  have hpos : 0 < (1 - s) ^ 2 := by
    have : 0 < 1 - s := by linarith
    positivity
  nlinarith


theorem hasDerivAt_bqPn (q s : ℝ) : HasDerivAt (bqPn q) (bqPn' q s) s := by
  have h : HasDerivAt (bqPn q) (deriv (bqPn q) s) s :=
    (by unfold bqPn; fun_prop : DifferentiableAt ℝ (bqPn q) s).hasDerivAt
  refine h.congr_deriv ?_
  unfold bqPn bqPn'
  simp (disch := fun_prop)
  ring

theorem hasDerivAt_bqQn (q s : ℝ) : HasDerivAt (bqQn q) (bqQn' q s) s := by
  have h : HasDerivAt (bqQn q) (deriv (bqQn q) s) s :=
    (by unfold bqQn; fun_prop : DifferentiableAt ℝ (bqQn q) s).hasDerivAt
  refine h.congr_deriv ?_
  unfold bqQn bqQn'
  simp (disch := fun_prop)
  ring

/-- The derivative of `U`. -/
noncomputable def bqU' (q s : ℝ) : ℝ :=
  (bqPn' q s * bqQn q s - bqPn q s * bqQn' q s) / bqQn q s ^ 2

theorem hasDerivAt_bqU {q s : ℝ} (h1 : 1 < q) (h2 : q < 2) (hs : |s| < 1) :
    HasDerivAt (bqU q) (bqU' q s) s :=
  (hasDerivAt_bqPn q s).div (hasDerivAt_bqQn q s) (bqQn_pos h1 h2 hs).ne'

/-- The Riccati residual of `U`: `(1-s²)U' - q(1-U²) = κ s⁶ (1-s²)² / Q²` (here with `Q = bqQn`). -/
theorem bqU_residual {q s : ℝ} (h1 : 1 < q) (h2 : q < 2) (hs : |s| < 1) :
    (1 - s ^ 2) * bqU' q s - q * (1 - bqU q s ^ 2) =
      bqKap q * s ^ 6 * (1 - s ^ 2) ^ 2 / bqQn q s ^ 2 := by
  have hQ := (bqQn_pos h1 h2 hs).ne'
  unfold bqU' bqU
  field_simp
  unfold bqPn' bqQn' bqPn bqQn bqKap
  ring


theorem bqU_nonneg {q s : ℝ} (h1 : 1 < q) (h2 : q < 2) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    0 ≤ bqU q s := by
  have hQ := bqQn_pos h1 h2 (s := s) (by rw [abs_lt]; constructor <;> linarith)
  unfold bqU bqPn
  apply div_nonneg _ hQ.le
  have : 0 ≤ 15 + (q ^ 2 + 6 * q - 25) * s ^ 2 + (q - 2) * (q - 4) * s ^ 4 := by
    have hy0 : 0 ≤ s ^ 2 := sq_nonneg s
    have hy1 : s ^ 2 ≤ 1 := by nlinarith
    have hy4 : s ^ 4 = (s ^ 2) ^ 2 := by ring
    have e : 15 + (q ^ 2 + 6 * q - 25) * s ^ 2 + (q - 2) * (q - 4) * s ^ 4 =
        (1 - s ^ 2) * (15 + (q ^ 2 + 6 * q - 10) * s ^ 2) + (2 * q ^ 2 - 2) * (s ^ 2) ^ 2 := by
      rw [hy4]; ring
    rw [e]
    have a : 0 ≤ 15 + (q ^ 2 + 6 * q - 10) * s ^ 2 := by nlinarith
    have b : 0 ≤ 2 * q ^ 2 - 2 := by nlinarith
    have := mul_nonneg (sub_nonneg.2 hy1) a
    nlinarith [mul_nonneg b (sq_nonneg (s ^ 2))]
  have : 0 ≤ q := by linarith
  positivity

/-- The comparison `x ≤ U` (BQ-2): monotonicity of `Ψ = ln((1+U)/(1-U)) - q ln((1+s)/(1-s))`. -/
theorem bqx_le_bqU {q s : ℝ} (h1 : 1 < q) (h2 : q < 2) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    bqx q s ≤ bqU q s := by
  set Ψ : ℝ → ℝ := fun s => Real.log (1 + bqU q s) - Real.log (1 - bqU q s)
    - q * (Real.log (1 + s) - Real.log (1 - s)) with hΨ
  have hU1 : ∀ s : ℝ, 0 ≤ s → s < 1 → bqU q s < 1 := fun s a b => bqU_lt_one h1 h2 a b
  have hder : ∀ s : ℝ, 0 ≤ s → s < 1 →
      HasDerivAt Ψ (bqU' q s / (1 + bqU q s) + bqU' q s / (1 - bqU q s)
        - q * (1 / (1 + s) + 1 / (1 - s))) s := by
    intro s a b
    have hs : |s| < 1 := by rw [abs_lt]; constructor <;> linarith
    have hU := hasDerivAt_bqU h1 h2 hs
    have hu0 := bqU_nonneg h1 h2 a b
    have hu1 := hU1 s a b
    have e1 : HasDerivAt (fun s => Real.log (1 + bqU q s)) (bqU' q s / (1 + bqU q s)) s :=
      (hU.const_add 1).log (by linarith)
    have e2 : HasDerivAt (fun s => Real.log (1 - bqU q s)) (-bqU' q s / (1 - bqU q s)) s :=
      (hU.const_sub 1).log (by linarith)
    have e3 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + s)) s := by
      have := ((hasDerivAt_id s).const_add 1).log (by simp; linarith)
      simpa using this
    have e4 : HasDerivAt (fun s : ℝ => Real.log (1 - s)) (-1 / (1 - s)) s := by
      have := ((hasDerivAt_id s).const_sub 1).log (by simp; linarith)
      simpa using this
    have := ((e1.sub e2).sub ((e3.sub e4).const_mul q))
    refine this.congr_deriv ?_
    have : (1 - s) ≠ 0 := by linarith
    field_simp
    ring
  have hmono : MonotoneOn Ψ (Set.Ico 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
      (f' := fun s => bqU' q s / (1 + bqU q s) + bqU' q s / (1 - bqU q s)
        - q * (1 / (1 + s) + 1 / (1 - s)))
    · intro s hs
      exact (hder s hs.1 hs.2).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ico] at hs
      exact (hder s hs.1.le hs.2).hasDerivWithinAt
    · intro s hs
      rw [interior_Ico] at hs
      obtain ⟨hs0', hs1'⟩ := hs
      have hs : |s| < 1 := by rw [abs_lt]; constructor <;> linarith
      have hu0 := bqU_nonneg h1 h2 hs0'.le hs1'
      have hu1 := hU1 s hs0'.le hs1'
      have hres := bqU_residual h1 h2 hs
      have hQ := bqQn_pos h1 h2 hs
      have hκ := bqKap_pos h1 h2
      have e : bqU' q s / (1 + bqU q s) + bqU' q s / (1 - bqU q s)
          - q * (1 / (1 + s) + 1 / (1 - s)) =
          2 * ((1 - s ^ 2) * bqU' q s - q * (1 - bqU q s ^ 2)) /
            ((1 - bqU q s ^ 2) * (1 - s ^ 2)) := by
        have : (1 + s) ≠ 0 := by linarith
        have : (1 - s) ≠ 0 := by linarith
        have : (1 + bqU q s) ≠ 0 := by linarith
        have : (1 - bqU q s) ≠ 0 := by linarith
        have : 1 - bqU q s ^ 2 ≠ 0 := by nlinarith
        have : 1 - s ^ 2 ≠ 0 := by nlinarith
        field_simp
        ring
      rw [e, hres]
      have : 0 < 1 - bqU q s ^ 2 := by nlinarith
      have : 0 < 1 - s ^ 2 := by nlinarith
      positivity
  have hΨ0 : Ψ 0 = 0 := by
    simp [hΨ, bqU, bqPn]
  have hge : 0 ≤ Ψ s := by
    have := hmono (Set.mem_Ico.2 ⟨le_rfl, by norm_num⟩) (Set.mem_Ico.2 ⟨hs0, hs1⟩) hs0
    linarith
  -- unfold: log((1+U) b) ≥ log((1-U) a)
  have hu0 := bqU_nonneg h1 h2 hs0 hs1
  have hu1 := hU1 s hs0 hs1
  have hp : (0 : ℝ) < 1 + s := by linarith
  have hm : (0 : ℝ) < 1 - s := by linarith
  have ha : 0 < (1 + s) ^ q := Real.rpow_pos_of_pos hp q
  have hb : 0 < (1 - s) ^ q := Real.rpow_pos_of_pos hm q
  have hlog : Real.log ((1 - bqU q s) * (1 + s) ^ q) ≤ Real.log ((1 + bqU q s) * (1 - s) ^ q) := by
    rw [Real.log_mul (by linarith) ha.ne', Real.log_mul (by linarith) hb.ne',
      Real.log_rpow hp, Real.log_rpow hm]
    simp only [hΨ] at hge
    linarith
  have hle := (Real.log_le_log_iff (mul_pos (by linarith) ha) (mul_pos (by linarith) hb)).1 hlog
  have hden := bq_denom_pos (s := s) (by rw [abs_lt]; constructor <;> linarith) q
  unfold bqx
  rw [div_le_iff₀ hden]
  nlinarith

end FormalResearch.FourQubitEntropy.RenyiFull
