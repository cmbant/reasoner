import FormalResearch.FourQubitEntropy.CriticalOrbitH
import FormalResearch.FourQubitEntropy.CriticalOrbitIdentity
import FormalResearch.FourQubitEntropy.CriticalOrbitReal

/-!
# Critical-orbit stability: the symmetry reduction and `Q ≥ 3/2 - 2Φ`

`Rel v u` says that `u` is obtained from `v` by the symmetries of `critical_orbit_stability.tex`
(`H₊`, `H₋`, coordinate swaps, sign flips, unit phase): same norm, the twelve cut probabilities are
permuted, and every overlap with a representative of `𝓗` of `u` is an overlap of `v`.
`normalize` brings a unit vector to the normal form `v₀ = r > 0`, `Im v_j ≥ 0`, `p₀` the largest of
the twelve probabilities; `Q_lower` is the first inequality of `eq:fqe-critical-fidelity`
(`Q ≥ 3/2 - 2Φ` for `Φ ≤ 1/2`), by the real inequality `core_real`.
-/

set_option linter.unusedSimpArgs false

namespace FormalResearch.FourQubitEntropy.CO
open PaperECritical

/-- `u` is obtained from `v` by the symmetries of the critical-orbit proof. -/
def Rel (v u : V) : Prop :=
  Nv u = Nv v ∧ (∃ σ : Equiv.Perm (Fin 12), ∀ k, pr u k = pr v (σ k)) ∧
    ∀ a, ∃ b, Aq a u = Aq b v ∧ Cq a u = Cq b v

theorem Rel.refl (v : V) : Rel v v := ⟨rfl, ⟨1, fun _ => rfl⟩, fun a => ⟨a, rfl, rfl⟩⟩

theorem Rel.trans {v u w : V} (h1 : Rel v u) (h2 : Rel u w) : Rel v w := by
  obtain ⟨hN1, ⟨σ1, hp1⟩, hq1⟩ := h1
  obtain ⟨hN2, ⟨σ2, hp2⟩, hq2⟩ := h2
  refine ⟨hN2.trans hN1, ⟨σ2.trans σ1, fun k => ?_⟩, fun a => ?_⟩
  · rw [hp2, hp1]; rfl
  · obtain ⟨b, hb1, hb2⟩ := hq2 a
    obtain ⟨c, hc1, hc2⟩ := hq1 b
    exact ⟨c, hb1.trans hc1, hb2.trans hc2⟩

theorem Rel.Qv_eq {v u : V} (h : Rel v u) : Qv u = Qv v := by
  obtain ⟨hN, ⟨σ, hp⟩, -⟩ := h
  exact Qv_of_perm σ hN hp

theorem Rel.qH_le {v u : V} (h : Rel v u) {Φ : ℝ} (hΦ : ∀ a, qH a v ≤ Φ) (a : Fin 32) :
    qH a u ≤ Φ := by
  obtain ⟨-, -, hq⟩ := h
  obtain ⟨b, hb1, hb2⟩ := hq a
  have := hΦ b
  unfold qH at *
  rw [hb1, hb2]; exact this

theorem Nv_wp (v : V) : Nv (wp v) = Nv v := by
  simp [Nv, Fintype.sum_prod_type, Fin.sum_univ_two, wp, Complex.normSq_apply]; ring

theorem Nv_wm (v : V) : Nv (wm v) = Nv v := by
  simp [Nv, Fintype.sum_prod_type, Fin.sum_univ_two, wm, Complex.normSq_apply]; ring

theorem Nv_swap (a b : Fin 2 × Fin 2) (v : V) : Nv (swapV a b v) = Nv v := by
  unfold Nv swapV
  exact Equiv.sum_comp (Equiv.swap a b) (fun p => Complex.normSq (v p))

theorem Nv_flip (j : Fin 2 × Fin 2) (v : V) : Nv (flipV j v) = Nv v := by
  unfold Nv flipV
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> simp

theorem rel_wp (v : V) : Rel v (wp v) :=
  ⟨Nv_wp v, ⟨Equiv.ofBijective ![4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11] (by decide),
    fun k => pr_wp v k⟩, fun a => ⟨_, close_wp v a⟩⟩

theorem rel_wm (v : V) : Rel v (wm v) :=
  ⟨Nv_wm v, ⟨Equiv.ofBijective ![8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3] (by decide),
    fun k => pr_wm v k⟩, fun a => ⟨_, close_wm v a⟩⟩

theorem rel_swap1 (v : V) : Rel v (swapV (0, 0) (0, 1) v) :=
  ⟨Nv_swap _ _ v, ⟨Equiv.ofBijective ![1, 0, 2, 3, 5, 4, 6, 7, 9, 8, 10, 11] (by decide),
    fun k => pr_swap1 v k⟩, fun a => ⟨_, close_swap1 v a⟩⟩

theorem rel_swap2 (v : V) : Rel v (swapV (0, 0) (1, 0) v) :=
  ⟨Nv_swap _ _ v, ⟨Equiv.ofBijective ![2, 1, 0, 3, 4, 7, 6, 5, 10, 9, 8, 11] (by decide),
    fun k => pr_swap2 v k⟩, fun a => ⟨_, close_swap2 v a⟩⟩

theorem rel_swap3 (v : V) : Rel v (swapV (0, 0) (1, 1) v) :=
  ⟨Nv_swap _ _ v, ⟨Equiv.ofBijective ![3, 1, 2, 0, 7, 5, 6, 4, 11, 9, 10, 8] (by decide),
    fun k => pr_swap3 v k⟩, fun a => ⟨_, close_swap3 v a⟩⟩

theorem rel_flip1 (v : V) : Rel v (flipV (0, 1) v) :=
  ⟨Nv_flip _ v, ⟨Equiv.ofBijective ![0, 1, 2, 3, 11, 10, 9, 8, 7, 6, 5, 4] (by decide),
    fun k => pr_flip1 v k⟩, fun a => ⟨_, close_flip1 v a⟩⟩

theorem rel_flip2 (v : V) : Rel v (flipV (1, 0) v) :=
  ⟨Nv_flip _ v, ⟨Equiv.ofBijective ![0, 1, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7] (by decide),
    fun k => pr_flip2 v k⟩, fun a => ⟨_, close_flip2 v a⟩⟩

theorem rel_flip3 (v : V) : Rel v (flipV (1, 1) v) :=
  ⟨Nv_flip _ v, ⟨Equiv.ofBijective ![0, 1, 2, 3, 9, 8, 11, 10, 5, 4, 7, 6] (by decide),
    fun k => pr_flip3 v k⟩, fun a => ⟨_, close_flip3 v a⟩⟩

theorem rel_smul {c : ℂ} (hc : Complex.normSq c = 1) (v : V) : Rel v (smulV c v) :=
  ⟨by rw [Nv_smul, hc, one_mul], ⟨1, fun k => by simp [pr_smul, hc]⟩,
    fun a => ⟨a, Aq_smul hc v a, Cq_smul hc v a⟩⟩


/-- Every cut probability is attained at coordinate `0` after a symmetry. -/
theorem exists_front (v : V) (k : Fin 12) : ∃ w, Rel v w ∧ pr w 0 = pr v k := by
  fin_cases k
  · exact ⟨v, Rel.refl v, rfl⟩
  · exact ⟨_, rel_swap1 v, by rw [pr_swap1]; rfl⟩
  · exact ⟨_, rel_swap2 v, by rw [pr_swap2]; rfl⟩
  · exact ⟨_, rel_swap3 v, by rw [pr_swap3]; rfl⟩
  · exact ⟨_, rel_wp v, by rw [pr_wp]; rfl⟩
  · exact ⟨_, (rel_wp v).trans (rel_swap1 _), by rw [pr_swap1, pr_wp]; rfl⟩
  · exact ⟨_, (rel_wp v).trans (rel_swap2 _), by rw [pr_swap2, pr_wp]; rfl⟩
  · exact ⟨_, (rel_wp v).trans (rel_swap3 _), by rw [pr_swap3, pr_wp]; rfl⟩
  · exact ⟨_, rel_wm v, by rw [pr_wm]; rfl⟩
  · exact ⟨_, (rel_wm v).trans (rel_swap1 _), by rw [pr_swap1, pr_wm]; rfl⟩
  · exact ⟨_, (rel_wm v).trans (rel_swap2 _), by rw [pr_swap2, pr_wm]; rfl⟩
  · exact ⟨_, (rel_wm v).trans (rel_swap3 _), by rw [pr_swap3, pr_wm]; rfl⟩

theorem pr_zero (v : V) : pr v 0 = Complex.normSq (v (0, 0)) := rfl

/-- Make the imaginary part of one coordinate nonnegative by a sign flip. -/
theorem flip_nonneg (j : Fin 2 × Fin 2) (hrel : ∀ v, Rel v (flipV j v)) (v : V) :
    ∃ u, Rel v u ∧ 0 ≤ (u j).im ∧ ∀ p, p ≠ j → u p = v p := by
  by_cases h : 0 ≤ (v j).im
  · exact ⟨v, Rel.refl v, h, fun _ _ => rfl⟩
  · refine ⟨flipV j v, hrel v, ?_, fun p hp => by simp [flipV, hp]⟩
    simp [flipV]; linarith [not_le.mp h]

/-- The normal form of the symmetry reduction: `u₀ = r > 0`, `Im u_j ≥ 0`, and `p₀` is the largest
of the twelve cut probabilities. -/
theorem normalize (v : V) (hN : Nv v = 1) :
    ∃ u, Rel v u ∧ 0 < (u (0, 0)).re ∧ (u (0, 0)).im = 0 ∧ 0 ≤ (u (0, 1)).im ∧
      0 ≤ (u (1, 0)).im ∧ 0 ≤ (u (1, 1)).im ∧ ∀ k, pr u k ≤ pr u 0 := by
  obtain ⟨k, hk⟩ := Finite.exists_max (pr v)
  obtain ⟨w, hw, hw0⟩ := exists_front v k
  have hmax : ∀ m, pr w m ≤ pr w 0 := by
    obtain ⟨-, ⟨σ, hσ⟩, -⟩ := hw
    intro m; rw [hσ, hw0]; exact hk _
  have hNw : Nv w = 1 := hw.1.trans hN
  -- the leading coordinate is nonzero
  have hz : w (0, 0) ≠ 0 := by
    intro h0
    have a0 : pr w 0 = 0 := by rw [pr_zero, h0]; simp
    have a1 : pr w 1 ≤ 0 := a0 ▸ hmax 1
    have a2 : pr w 2 ≤ 0 := a0 ▸ hmax 2
    have a3 : pr w 3 ≤ 0 := a0 ▸ hmax 3
    have b1 : 0 ≤ pr w 1 := Complex.normSq_nonneg _
    have b2 : 0 ≤ pr w 2 := Complex.normSq_nonneg _
    have b3 : 0 ≤ pr w 3 := Complex.normSq_nonneg _
    have := Nv_eq_pr w
    linarith
  set z := w (0, 0) with hzdef
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  set c : ℂ := (starRingEnd ℂ) z / (‖z‖ : ℂ) with hc
  have hcn : Complex.normSq c = 1 := by
    rw [hc, map_div₀, Complex.normSq_conj, Complex.normSq_ofReal]
    have : Complex.normSq z = ‖z‖ * ‖z‖ := by
      rw [Complex.normSq_eq_norm_sq]; ring
    rw [this]; field_simp
  have hcz : c * z = (‖z‖ : ℂ) := by
    rw [hc, div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hzn.ne'
    push_cast; field_simp
  set u1 := smulV c w with hu1
  have h1 : Rel v u1 := hw.trans (rel_smul hcn w)
  have hu10 : u1 (0, 0) = (‖z‖ : ℂ) := by
    show c * w (0, 0) = _
    rw [← hzdef]; exact hcz
  obtain ⟨u2, h2, h2j, h2p⟩ := flip_nonneg (0, 1) rel_flip1 u1
  obtain ⟨u3, h3, h3j, h3p⟩ := flip_nonneg (1, 0) rel_flip2 u2
  obtain ⟨u4, h4, h4j, h4p⟩ := flip_nonneg (1, 1) rel_flip3 u3
  have e4 : u4 (0, 0) = u1 (0, 0) := by
    rw [h4p _ (by decide), h3p _ (by decide), h2p _ (by decide)]
  have e41 : u4 (0, 1) = u3 (0, 1) := h4p _ (by decide)
  have e31 : u3 (0, 1) = u2 (0, 1) := h3p _ (by decide)
  have e40 : u4 (1, 0) = u3 (1, 0) := h4p _ (by decide)
  refine ⟨u4, h1.trans (h2.trans (h3.trans h4)), ?_, ?_, ?_, ?_, h4j, ?_⟩
  · rw [e4, hu10]; simpa using hzn
  · rw [e4, hu10]; simp
  · rw [e41, e31]; exact h2j
  · rw [e40]; exact h3j
  · obtain ⟨-, ⟨σ, hσ⟩, -⟩ := h2.trans (h3.trans h4)
    have hp1 : ∀ m, pr u1 m = pr w m := fun m => by simp [hu1, pr_smul, hcn]
    intro m
    rw [hσ m, hp1]
    calc pr w (σ m) ≤ pr w 0 := hmax _
      _ = pr u1 0 := (hp1 0).symm
      _ = pr u4 0 := by rw [pr_zero, pr_zero, e4]


/-- The eight rows `½ (1, ε₁, ε₂, ε₃)` of `H₊`, `H₋` (up to sign), for a vector with real `u₀`. -/
theorem pr_row (u : V) (hu0 : (u (0, 0)).im = 0) (s1 s2 s3 : ℝ) (h1 : s1 ^ 2 = 1) (h2 : s2 ^ 2 = 1)
    (h3 : s3 ^ 2 = 1) : ∃ k, pr u k * 4 =
      ((u (0, 0)).re + s1 * (u (0, 1)).re + s2 * (u (1, 0)).re + s3 * (u (1, 1)).re) ^ 2 +
      (s1 * (u (0, 1)).im + s2 * (u (1, 0)).im + s3 * (u (1, 1)).im) ^ 2 := by
  rcases eq_or_eq_neg_of_sq_eq_sq s1 1 (by simpa using h1) with rfl | rfl <;>
  rcases eq_or_eq_neg_of_sq_eq_sq s2 1 (by simpa using h2) with rfl | rfl <;>
  rcases eq_or_eq_neg_of_sq_eq_sq s3 1 (by simpa using h3) with rfl | rfl
  · -- s = (1, 1, 1)
    exact ⟨6, by simp [pr, wp, wm, Complex.normSq_apply, hu0]; ring⟩
  · -- s = (1, 1, -1)
    exact ⟨11, by simp [pr, wp, wm, Complex.normSq_apply, hu0]; ring⟩
  · -- s = (1, -1, 1)
    exact ⟨10, by simp [pr, wp, wm, Complex.normSq_apply, hu0]; ring⟩
  · -- s = (1, -1, -1)
    exact ⟨7, by simp [pr, wp, wm, Complex.normSq_apply, hu0]; ring⟩
  · -- s = (-1, 1, 1)
    exact ⟨9, by simp [pr, wp, wm, Complex.normSq_apply, hu0]; ring⟩
  · -- s = (-1, 1, -1)
    exact ⟨4, by simp [pr, wp, wm, Complex.normSq_apply, hu0]; ring⟩
  · -- s = (-1, -1, 1)
    exact ⟨5, by simp [pr, wp, wm, Complex.normSq_apply, hu0]; ring⟩
  · -- s = (-1, -1, -1)
    exact ⟨8, by simp [pr, wp, wm, Complex.normSq_apply, hu0]; ring⟩

/-- `Q ≥ 3/2 - 2 Φ` for a unit critical vector whose overlaps with `𝓗` are bounded by `Φ ≤ 1/2`
(first inequality of `eq:fqe-critical-fidelity` in `critical_orbit_stability.tex`). -/
theorem Q_lower (v : V) (hN : Nv v = 1) {Φ : ℝ} (hΦ : ∀ a, qH a v ≤ Φ) (hΦ2 : Φ ≤ 1 / 2) :
    3 / 2 - 2 * Φ ≤ Qv v := by
  obtain ⟨u, hu, hr, hu0, hy1, hy2, hy3, hmax⟩ := normalize v hN
  have hNu : Nv u = 1 := hu.1.trans hN
  have hq0 := hu.qH_le hΦ 0
  have hQ := hu.Qv_eq
  set r := (u (0, 0)).re with hrdef
  set x1 := (u (0, 1)).re
  set x2 := (u (1, 0)).re
  set x3 := (u (1, 1)).re
  set y1 := (u (0, 1)).im
  set y2 := (u (1, 0)).im
  set y3 := (u (1, 1)).im
  have hp0 : Complex.normSq (u (0, 0)) = r ^ 2 := by rw [Complex.normSq_apply, hu0]; ring
  have hN' : r ^ 2 + (x1 ^ 2 + y1 ^ 2) + (x2 ^ 2 + y2 ^ 2) + (x3 ^ 2 + y3 ^ 2) = 1 := by
    have := Nv_eq_pr u
    simp only [pr_zero, Matrix.cons_val_zero] at this
    have e1 : pr u 1 = x1 ^ 2 + y1 ^ 2 := by simp [pr, Complex.normSq_apply, x1, y1]; ring
    have e2 : pr u 2 = x2 ^ 2 + y2 ^ 2 := by simp [pr, Complex.normSq_apply, x2, y2]; ring
    have e3 : pr u 3 = x3 ^ 2 + y3 ^ 2 := by simp [pr, Complex.normSq_apply, x3, y3]; ring
    rw [hp0] at this
    linarith
  have hp : ∀ j : Fin 12, j = 1 ∨ j = 2 ∨ j = 3 → pr u j ≤ r ^ 2 := by
    intro j _; have := hmax j; rw [pr_zero, hp0] at this; exact this
  have e1 : pr u 1 = x1 ^ 2 + y1 ^ 2 := by simp [pr, Complex.normSq_apply, x1, y1]; ring
  have e2 : pr u 2 = x2 ^ 2 + y2 ^ 2 := by simp [pr, Complex.normSq_apply, x2, y2]; ring
  have e3 : pr u 3 = x3 ^ 2 + y3 ^ 2 := by simp [pr, Complex.normSq_apply, x3, y3]; ring
  have hl : ∀ s1 s2 s3 : ℝ, s1 ^ 2 = 1 → s2 ^ 2 = 1 → s3 ^ 2 = 1 →
      (r + s1 * x1 + s2 * x2 + s3 * x3) ^ 2 + (s1 * y1 + s2 * y2 + s3 * y3) ^ 2 ≤ 4 * r ^ 2 := by
    intro s1 s2 s3 h1 h2 h3
    obtain ⟨k, hk⟩ := pr_row u hu0 s1 s2 s3 h1 h2 h3
    have := hmax k
    rw [pr_zero, hp0] at this
    linarith
  have hqe : qH 0 u = (3 * r ^ 2 + (x1 + x2 + x3) ^ 2 + (y1 + y2 + y3) ^ 2 +
      2 * Real.sqrt 3 * (r * (y1 + y2 + y3))) / 6 := by
    simp [qH, Aq, Cq, Sx, Sy, coord, epsOf, idxI, Fin.sum_univ_four, hp0, hu0, x1, x2, x3, y1, y2, y3,
      hrdef]
  have h3 : 0 ≤ (x1 + x2 + x3) ^ 2 := sq_nonneg _
  have hqz : r ^ 2 / 2 + (y1 + y2 + y3) ^ 2 / 6 + Real.sqrt 3 * r * (y1 + y2 + y3) / 3 ≤ 1 / 2 := by
    linarith
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have key := core_real hs3 (Real.sqrt_pos.mpr (by norm_num)) hr hy1 hy2 hy3 hN'
    (hp 1 (by simp) |>.trans' (le_of_eq e1.symm)) (hp 2 (by simp) |>.trans' (le_of_eq e2.symm))
    (hp 3 (by simp) |>.trans' (le_of_eq e3.symm)) hl hqz
  have hQ3 := Qv_three_term u
  rw [hNu] at hQ3
  have him : (u (0, 0)).im ^ 2 = 0 := by rw [hu0]; ring
  have hD1 : Complex.normSq (u (0, 0)) + Complex.normSq (u (0, 1)) - Complex.normSq (u (1, 0)) -
      Complex.normSq (u (1, 1)) = 2 * (r ^ 2 + x1 ^ 2 + y1 ^ 2) - 1 := by
    simp only [Complex.normSq_apply, x1, x2, x3, y1, y2, y3] at hN' hp0 ⊢
    linear_combination (-1) * hN' + him
  have hD2 : Complex.normSq (u (0, 0)) + Complex.normSq (u (1, 0)) - Complex.normSq (u (0, 1)) -
      Complex.normSq (u (1, 1)) = 2 * (r ^ 2 + x2 ^ 2 + y2 ^ 2) - 1 := by
    simp only [Complex.normSq_apply, x1, x2, x3, y1, y2, y3] at hN' hp0 ⊢
    linear_combination (-1) * hN' + him
  have hD3 : Complex.normSq (u (0, 0)) + Complex.normSq (u (1, 1)) - Complex.normSq (u (0, 1)) -
      Complex.normSq (u (1, 0)) = 2 * (r ^ 2 + x3 ^ 2 + y3 ^ 2) - 1 := by
    simp only [Complex.normSq_apply, x1, x2, x3, y1, y2, y3] at hN' hp0 ⊢
    linear_combination (-1) * hN' + him
  have hQ' : Qv u = 1 / 2 + 18 * ((2 * (r ^ 2 + x1 ^ 2 + y1 ^ 2) - 1) * (r ^ 2 * x1 ^ 2 - (x2 * x3 + y2 * y3) ^ 2) +
        (2 * (r ^ 2 + x2 ^ 2 + y2 ^ 2) - 1) * (r ^ 2 * x2 ^ 2 - (x1 * x3 + y1 * y3) ^ 2) +
        (2 * (r ^ 2 + x3 ^ 2 + y3 ^ 2) - 1) * (r ^ 2 * x3 ^ 2 - (x1 * x2 + y1 * y2) ^ 2)) := by
    rw [hQ3, hD1, hD2, hD3]
    simp only [hu0, mul_zero, add_zero]
    ring
  linarith [hQ, hQ', key, hqe, hq0, h3]

end FormalResearch.FourQubitEntropy.CO
