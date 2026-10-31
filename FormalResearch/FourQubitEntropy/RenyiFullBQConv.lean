import FormalResearch.FourQubitEntropy.RenyiFullBQSign

/-!
# Binary quartic lemma at `q_s`: `G' > 0` and `f''' > 0`

`G'' > 0` on `(0,1)` (`bqG2_pos`) makes `G'` strictly increasing; `G'(0+) = 0` follows from
`x = U - O(s⁷)` (`bqU_sub_x_le`) and the exact cancellation `N₁(s,U)·Q³ = s⁵(q-1)(1-s²)² NN(s)`
(`bqNN`, certified by `ring`), which replaces the analyticity argument of the paper.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open Filter Topology

/-- The difference quotient of `N₁` in its last argument. -/
noncomputable def bqK1 (q s u d : ℝ) : ℝ :=
  2 * d ^ 2 * q ^ 2 * s ^ 2 - 6 * d * q ^ 2 * s ^ 2 * u + 9 * d * q * s ^ 3 - 3 * d * q * s
    + 6 * q ^ 2 * s ^ 2 * u ^ 2 - 2 * q ^ 2 * s ^ 2 - 18 * q * s ^ 3 * u + 6 * q * s * u
    + 15 * s ^ 4 - 10 * s ^ 2 + 3

theorem bqN1_sub (q s u d : ℝ) : bqN1 q s (u - d) = bqN1 q s u - d * bqK1 q s u d := by
  unfold bqN1 bqK1; ring

theorem bqN1_U {s : ℝ} (hs : |s| < 1) :
    bqN1 (1587 / 1000) s (bqU (1587 / 1000) s) =
      s ^ 5 * (1587 / 1000 - 1) * (1 - s ^ 2) ^ 2 * bqNN s / bqQn (1587 / 1000) s ^ 3 := by
  have hQ := (bqQn_pos (q := 1587 / 1000) (by norm_num) (by norm_num) hs).ne'
  unfold bqU bqN1
  field_simp
  unfold bqPn bqQn bqNN
  ring

/-- The cancelled leading part of `G'`. -/
noncomputable def bqT1 (s : ℝ) : ℝ :=
  1587 / 1000 * (1587 / 1000 - 1) * s * bqNN s / (4 * (1 - s ^ 2) * bqQn (1587 / 1000) s ^ 3)

/-- The coefficient of the error `Δ/s⁴`. -/
noncomputable def bqA1 (s : ℝ) : ℝ :=
  -(1587 / 1000 * bqK1 (1587 / 1000) s (bqU (1587 / 1000) s)
    (bqU (1587 / 1000) s - bqx (1587 / 1000) s)) / (4 * (1 - s ^ 2) ^ 3)

theorem bqG1_decomp {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    bqG1 (1587 / 1000) s = bqT1 s + bqA1 s *
      ((bqU (1587 / 1000) s - bqx (1587 / 1000) s) / s ^ 4) := by
  have hs : |s| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hQ := (bqQn_pos (q := 1587 / 1000) (by norm_num) (by norm_num) hs).ne'
  have h2 : 1 - s ^ 2 ≠ 0 := by nlinarith
  have hx : bqx (1587 / 1000) s = bqU (1587 / 1000) s - (bqU (1587 / 1000) s - bqx (1587 / 1000) s) := by ring
  unfold bqG1
  rw [hx, bqN1_sub, bqN1_U hs]
  unfold bqT1 bqA1
  have : s ≠ 0 := hs0.ne'
  field_simp
  ring

theorem bqU_continuousAt : ContinuousAt (bqU (1587 / 1000)) 0 := by
  unfold bqU bqPn bqQn
  apply ContinuousAt.div (by fun_prop) (by fun_prop)
  norm_num

theorem bqx_continuousAt : ContinuousAt (bqx (1587 / 1000)) 0 :=
  (hasDerivAt_bqx (q := 1587 / 1000) (s := 0) (by norm_num)).continuousAt

theorem bqT1_tendsto : Tendsto bqT1 (𝓝[>] 0) (𝓝 0) := by
  have hc : ContinuousAt bqT1 0 := by
    unfold bqT1 bqNN bqQn
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    norm_num
  have h0 : bqT1 0 = 0 := by simp [bqT1]
  have := hc.tendsto
  rw [h0] at this
  exact this.mono_left nhdsWithin_le_nhds

theorem bqA1_continuousAt : ContinuousAt bqA1 0 := by
  have hU := bqU_continuousAt
  have hx := bqx_continuousAt
  unfold bqA1 bqK1
  apply ContinuousAt.div (by fun_prop) (by fun_prop)
  norm_num

theorem bqDelta_tendsto : Tendsto (fun s => (bqU (1587 / 1000) s - bqx (1587 / 1000) s) / s ^ 4)
    (𝓝[>] 0) (𝓝 0) := by
  have hup : Tendsto (fun s : ℝ => s ^ 3 / 70) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun s : ℝ => s ^ 3 / 70) (𝓝 0) (𝓝 (0 ^ 3 / 70)) :=
      (by fun_prop : Continuous (fun s : ℝ => s ^ 3 / 70)).continuousAt.tendsto
    simpa using this.mono_left nhdsWithin_le_nhds
  have hI : Set.Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [hI] with s hs
    have h4 : 0 < s ^ 4 := by have := hs.1; positivity
    have := bqx_le_bqU (q := 1587 / 1000) (by norm_num) (by norm_num) hs.1.le (by linarith [hs.2])
    exact div_nonneg (by linarith) h4.le
  · filter_upwards [hI] with s hs
    have h4 : 0 < s ^ 4 := by have := hs.1; positivity
    have := bqU_sub_x_le hs.1.le hs.2.le
    rw [div_le_iff₀ h4]
    have e : s ^ 3 / 70 * s ^ 4 = s ^ 7 / 70 := by ring
    rw [e]; exact this

theorem bqG1_tendsto : Tendsto (bqG1 (1587 / 1000)) (𝓝[>] 0) (𝓝 0) := by
  have h1 := bqT1_tendsto
  have h2 : Tendsto bqA1 (𝓝[>] 0) (𝓝 (bqA1 0)) :=
    bqA1_continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h3 := h1.add (h2.mul bqDelta_tendsto)
  simp only [mul_zero, add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
  exact (bqG1_decomp hs.1 (by linarith [hs.2])).symm

/-- `G'` is strictly increasing on `(0,1)`. -/
theorem bqG1_strictMonoOn : StrictMonoOn (bqG1 (1587 / 1000)) (Set.Ioo 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
  · intro s hs
    exact (hasDerivAt_bqG1 hs.1 hs.2).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioo] at hs
    rw [(hasDerivAt_bqG1 hs.1 hs.2).deriv]
    exact bqG2_pos hs.1 hs.2

/-- `G'(s) > 0` for `0 < s < 1` (that is `D_q''' > 0`), `q = q_s`. -/
theorem bqG1_pos {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : 0 < bqG1 (1587 / 1000) s := by
  have key : ∀ t : ℝ, 0 < t → t < 1 → 0 ≤ bqG1 (1587 / 1000) t := by
    intro t ht0 ht1
    refine le_of_tendsto bqG1_tendsto ?_
    filter_upwards [Ioo_mem_nhdsGT ht0] with u hu
    exact (bqG1_strictMonoOn ⟨hu.1, hu.2.trans ht1⟩ ⟨ht0, ht1⟩ hu.2).le
  have h := bqG1_strictMonoOn (a := s / 2) (b := s) ⟨by linarith, by linarith⟩ ⟨hs0, hs1⟩ (by linarith)
  have := key (s / 2) (by linarith) (by linarith)
  linarith

end FormalResearch.FourQubitEntropy.RenyiFull
