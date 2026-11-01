import FormalResearch.FourQubitEntropy.RenyiFullLHKappa

/-!
# Elementary logarithm estimates for the large-head dual

`artanh_enc`: for `0 ≤ y < 1`, the partial sums `S_N(y) = Σ_{k<N} 2 y^{2k+1}/(2k+1)` of the series of
`Λ(y) = ln(1+y) - ln(1-y) = ln((1+y)/(1-y))` are lower bounds and `S_N + 2 y^{2N+1}/((2N+1)(1-y²))` is an
upper bound.  With `N = 1` this is the paper's `|E| ≤ 2|y|³/(3(1-y²))`; with larger `N` it gives
the rational enclosures of the constants.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open Finset

/-- Partial sum `Σ_{k<N} 2 y^{2k+1}/(2k+1)`. -/
noncomputable def artS (N : ℕ) (y : ℝ) : ℝ := ∑ k ∈ range N, 2 * (1 / (2 * (k : ℝ) + 1)) * y ^ (2 * k + 1)

/-- Tail bound used with `artS`. -/
noncomputable def artT (N : ℕ) (y : ℝ) : ℝ := 2 * y ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - y ^ 2))

theorem artanh_enc {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (N : ℕ) :
    artS N y ≤ Real.log (1 + y) - Real.log (1 - y) ∧
      Real.log (1 + y) - Real.log (1 - y) ≤ artS N y + artT N y := by
  have habs : |y| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  set f : ℕ → ℝ := fun k => 2 * (1 / (2 * (k : ℝ) + 1)) * y ^ (2 * k + 1) with hf
  have hf0 : ∀ k, 0 ≤ f k := fun k => by simp only [hf]; positivity
  constructor
  · exact sum_le_hasSum (range N) (fun k _ => hf0 k) hs
  · -- tail
    have htail := (hasSum_nat_add_iff' N).2 hs
    have hy2 : y ^ 2 < 1 := by nlinarith
    have hgeo : HasSum (fun k : ℕ => 2 * y ^ (2 * N + 1) / (2 * (N : ℝ) + 1) * (y ^ 2) ^ k)
        (2 * y ^ (2 * N + 1) / (2 * (N : ℝ) + 1) * (1 - y ^ 2)⁻¹) :=
      (hasSum_geometric_of_lt_one (by positivity) hy2).mul_left _
    have hle : ∀ k : ℕ, f (k + N) ≤ 2 * y ^ (2 * N + 1) / (2 * (N : ℝ) + 1) * (y ^ 2) ^ k := by
      intro k
      simp only [hf]
      have e : y ^ (2 * (k + N) + 1) = y ^ (2 * N + 1) * (y ^ 2) ^ k := by
        rw [← pow_mul]; rw [← pow_add]; congr 1; ring
      rw [e]
      have h1 : 1 / (2 * ((k + N : ℕ) : ℝ) + 1) ≤ 1 / (2 * (N : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        push_cast; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
      have h2 : 0 ≤ y ^ (2 * N + 1) * (y ^ 2) ^ k := by positivity
      calc 2 * (1 / (2 * ((k + N : ℕ) : ℝ) + 1)) * (y ^ (2 * N + 1) * (y ^ 2) ^ k)
          ≤ 2 * (1 / (2 * (N : ℝ) + 1)) * (y ^ (2 * N + 1) * (y ^ 2) ^ k) := by
            apply mul_le_mul_of_nonneg_right _ h2; linarith
        _ = 2 * y ^ (2 * N + 1) / (2 * (N : ℝ) + 1) * (y ^ 2) ^ k := by ring
    have := hasSum_le hle htail hgeo
    have e2 : 2 * y ^ (2 * N + 1) / (2 * (N : ℝ) + 1) * (1 - y ^ 2)⁻¹ =
        2 * y ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - y ^ 2)) := by
      field_simp
    unfold artS artT
    simp only [hf] at this
    linarith


theorem log_enc_ge {Z y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (hZ : Z = (1 + y) / (1 - y)) (N : ℕ) :
    artS N y ≤ Real.log Z := by
  have := (artanh_enc hy0 hy1 N).1
  rw [hZ, Real.log_div (by linarith) (by linarith)]
  exact this

theorem log_enc_le {Z y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (hZ : Z = (1 + y) / (1 - y)) (N : ℕ) :
    Real.log Z ≤ artS N y + artT N y := by
  have := (artanh_enc hy0 hy1 N).2
  rw [hZ, Real.log_div (by linarith) (by linarith)]
  exact this

theorem neglog_enc_ge {Z y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (hZ : Z = (1 - y) / (1 + y)) (N : ℕ) :
    artS N y ≤ -Real.log Z := by
  have := (artanh_enc hy0 hy1 N).1
  rw [hZ, Real.log_div (by linarith) (by linarith)]
  linarith

theorem neglog_enc_le {Z y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (hZ : Z = (1 - y) / (1 + y)) (N : ℕ) :
    -Real.log Z ≤ artS N y + artT N y := by
  have := (artanh_enc hy0 hy1 N).2
  rw [hZ, Real.log_div (by linarith) (by linarith)]
  linarith

theorem artS_one (y : ℝ) : artS 1 y = 2 * y := by
  unfold artS
  simp

theorem artT_one (y : ℝ) : artT 1 y = 2 * y ^ 3 / (3 * (1 - y ^ 2)) := by
  unfold artT
  norm_num

/-- The two-term bound `|Λ(y) - 2y| ≤ 2|y|³/(3(1-y²))` for `|y| < 1`. -/
theorem lam_two_term {y : ℝ} (hy : |y| < 1) :
    |Real.log (1 + y) - Real.log (1 - y) - 2 * y| ≤ 2 * |y| ^ 3 / (3 * (1 - y ^ 2)) := by
  have hy1 := abs_lt.1 hy
  rcases le_total 0 y with h | h
  · have := artanh_enc h hy1.2 1
    rw [artS_one, artT_one] at this
    rw [abs_of_nonneg h, abs_le]
    constructor
    · have : 0 ≤ 2 * y ^ 3 / (3 * (1 - y ^ 2)) := by
        apply div_nonneg (by positivity)
        nlinarith
      linarith [this]
    · linarith [this.2]
  · have h' : 0 ≤ -y := by linarith
    have := artanh_enc h' (by linarith) 1
    rw [artS_one, artT_one] at this
    have e1 : 1 + -y = 1 - y := by ring
    have e2 : 1 - -y = 1 + y := by ring
    rw [e1, e2] at this
    rw [abs_of_nonpos h, abs_le]
    have h3 : 0 ≤ 2 * (-y) ^ 3 / (3 * (1 - (-y) ^ 2)) := by
      apply div_nonneg (by positivity)
      nlinarith
    have e4 : (-y) ^ 2 = y ^ 2 := by ring
    rw [e4] at this h3
    constructor
    · linarith [this.1, this.2]
    · linarith [this.1, this.2]

end FormalResearch.FourQubitEntropy.RenyiFull
