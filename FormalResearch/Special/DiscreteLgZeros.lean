module

public import FormalResearch.Special.DiscreteLgBulk

/-!
# Discrete Liouville-Green: sign changes of a bulk solution sit within `O(h)` in phase of the zeros of `cos(Θ/h - φ₀)`

From `|Y_k - R w_k cos x_k| ≤ ε R w_k` (`x_k = Θ(q_k)/h - φ₀`, `ε = C h` in `dlg_bulk`):

* `dlg_sign`: `|cos x_k| > ε` forces `Y_k` to have the sign of `cos x_k`;
* `dlg_zero_localisation`: a sign change `Y_k Y_{k+1} ≤ 0` across a bond with `x_k ≤ x_{k+1}` forces a zero `(2j+1)π/2` of the cosine in
  `[x_k - (π/2) ε, x_{k+1} + (π/2) ε]`.  In the variable `q` the zeros are the points `Θ(q_j)/h = φ₀ + (2j+1)π/2` (Bohr-Sommerfeld lattice), and the bound
  says that the discrete zero bonds are the bonds containing them up to `O(h)` in the phase, i.e. `O(h²)` in `q`.

**Claim class: proved.**  **Not formalised:** the converse and the counting of sign changes are the abstract `bix_count` (`BulkIndexCount`); not formalised here: the conversion
of the phase window into a window in `q` (needs a lower bound `θ ≥ θ_min > 0`).
-/

@[expose] public section

namespace FormalResearch.Special

lemma dlg_sign {Y R w x ε : ℝ} (hRw : 0 < R * w) (hY : |Y - R * w * Real.cos x| ≤ ε * (R * w)) (hc : ε < |Real.cos x|) :
    0 < Y * Real.cos x := by
  have hε : 0 ≤ ε := by
    by_contra h; push Not at h
    have := (abs_nonneg _).trans hY
    nlinarith
  have hcpos : 0 < |Real.cos x| := lt_of_le_of_lt hε hc
  have e : Y * Real.cos x = R * w * |Real.cos x| ^ 2 + (Y - R * w * Real.cos x) * Real.cos x := by
    rw [sq_abs]; ring
  have h1 : |(Y - R * w * Real.cos x) * Real.cos x| ≤ ε * (R * w) * |Real.cos x| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right hY (abs_nonneg _)
  have h2 := neg_abs_le ((Y - R * w * Real.cos x) * Real.cos x)
  have h3 : 0 < R * w * |Real.cos x| * (|Real.cos x| - ε) := mul_pos (mul_pos hRw hcpos) (sub_pos.2 hc)
  rw [e]
  nlinarith

/-- A point where `|cos x| ≤ ε` is within `(π/2) ε` of a zero `(2j+1)π/2` of the cosine. -/
lemma dlg_near_zero {x ε : ℝ} (hε : |Real.cos x| ≤ ε) : ∃ j : ℤ, |x - (2 * j + 1) * Real.pi / 2| ≤ Real.pi / 2 * ε := by
  set j : ℤ := ⌊x / Real.pi⌋ with hj
  set y : ℝ := x - Real.pi / 2 - j * Real.pi with hy
  have hpi := Real.pi_pos
  have h1 : (j : ℝ) ≤ x / Real.pi := Int.floor_le _
  have h2 : x / Real.pi < j + 1 := Int.lt_floor_add_one _
  have h1' : (j : ℝ) * Real.pi ≤ x := (le_div_iff₀ hpi).1 h1
  have h2' : x < (j + 1) * Real.pi := (div_lt_iff₀ hpi).1 h2
  have hy1 : -(Real.pi / 2) ≤ y := by rw [hy]; linarith
  have hy2 : y ≤ Real.pi / 2 := by rw [hy]; nlinarith
  have hya : |y| ≤ Real.pi / 2 := abs_le.2 ⟨hy1, hy2⟩
  have hcos : |Real.cos x| = |Real.sin y| := by
    have h0 : Real.cos x = -Real.sin (x - Real.pi / 2) := by rw [Real.sin_sub_pi_div_two]; ring
    have hs : Real.sin (x - Real.pi / 2) = (-1) ^ j * Real.sin y := by
      have : x - Real.pi / 2 = y + j * Real.pi := by rw [hy]; ring
      rw [this, Real.sin_add_int_mul_pi]
    rw [h0, abs_neg, hs, abs_mul]
    simp
  have hsin : |Real.sin y| = Real.sin |y| := by
    rcases le_total 0 y with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith))]
    · have hs := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : 0 ≤ -y) (by linarith : -y ≤ Real.pi)
      rw [Real.sin_neg] at hs
      rw [abs_of_nonpos h, Real.sin_neg, abs_of_nonpos (by linarith)]
  have hJ : 2 / Real.pi * |y| ≤ Real.sin |y| := Real.mul_le_sin (abs_nonneg y) hya
  refine ⟨j, ?_⟩
  have e : x - (2 * j + 1) * Real.pi / 2 = y := by rw [hy]; ring
  rw [e]
  rw [hcos, hsin] at hε
  have : 2 / Real.pi * |y| ≤ ε := hJ.trans hε
  rw [div_mul_eq_mul_div, div_le_iff₀ hpi] at this
  nlinarith

/-- **Zero localisation**: see the module docstring. -/
theorem dlg_zero_localisation {Y0 Y1 R w0 w1 x0 x1 ε : ℝ} (hR0 : 0 < R * w0) (hR1 : 0 < R * w1) (hε : 0 ≤ ε)
    (h0 : |Y0 - R * w0 * Real.cos x0| ≤ ε * (R * w0)) (h1 : |Y1 - R * w1 * Real.cos x1| ≤ ε * (R * w1))
    (hch : Y0 * Y1 ≤ 0) (hx : x0 ≤ x1) :
    ∃ j : ℤ, x0 - Real.pi / 2 * ε ≤ (2 * j + 1) * Real.pi / 2 ∧ (2 * j + 1) * Real.pi / 2 ≤ x1 + Real.pi / 2 * ε := by
  have hpi := Real.pi_pos
  by_cases hA : |Real.cos x0| ≤ ε
  · obtain ⟨j, hj⟩ := dlg_near_zero hA
    rw [abs_le] at hj
    exact ⟨j, by linarith [hj.1, hj.2], by linarith [hj.1, hj.2]⟩
  by_cases hB : |Real.cos x1| ≤ ε
  · obtain ⟨j, hj⟩ := dlg_near_zero hB
    rw [abs_le] at hj
    exact ⟨j, by linarith [hj.1, hj.2], by linarith [hj.1, hj.2]⟩
  push Not at hA hB
  have s0 := dlg_sign hR0 h0 hA
  have s1 := dlg_sign hR1 h1 hB
  have hneg : Real.cos x0 * Real.cos x1 < 0 := by
    by_contra hcon
    push Not at hcon
    have h4 : 0 < (Y0 * Real.cos x0) * (Y1 * Real.cos x1) := mul_pos s0 s1
    have e : (Y0 * Real.cos x0) * (Y1 * Real.cos x1) = (Y0 * Y1) * (Real.cos x0 * Real.cos x1) := by ring
    rw [e] at h4
    nlinarith [mul_nonneg (neg_nonneg.2 hch) hcon]
  have hcont : ContinuousOn Real.cos (Set.Icc x0 x1) := Real.continuous_cos.continuousOn
  have hzero : ∃ z ∈ Set.Icc x0 x1, Real.cos z = 0 := by
    rcases lt_or_gt_of_ne (show Real.cos x0 ≠ 0 from fun h => by rw [h] at hneg; simp at hneg) with hn | hp
    · have hp1 : 0 < Real.cos x1 := by
        by_contra hc; push Not at hc
        nlinarith [mul_nonneg_of_nonpos_of_nonpos hn.le hc]
      exact intermediate_value_Icc hx hcont ⟨hn.le, hp1.le⟩
    · have hn1 : Real.cos x1 < 0 := by
        by_contra hc; push Not at hc
        nlinarith [mul_nonneg hp.le hc]
      exact intermediate_value_Icc' hx hcont ⟨hn1.le, hp.le⟩
  obtain ⟨z, hz, hz0⟩ := hzero
  obtain ⟨j, hj⟩ := Real.cos_eq_zero_iff.1 hz0
  refine ⟨j, ?_, ?_⟩
  · rw [← hj]; nlinarith [hz.1, mul_nonneg hpi.le hε]
  · rw [← hj]; nlinarith [hz.2, mul_nonneg hpi.le hε]

/-- The lattice phase is increasing when `θ > 0` (`Θ' = θ`): `P_k ≤ P_{k+1}` for sites in the convex set `U`. -/
lemma dlg_phase_mono {A θ w Θ : ℝ → ℝ} {U : Set ℝ} {lo hi M : ℝ} (D : DlgData A θ w Θ U lo hi M)
    (hθ : ∀ t ∈ U, 0 < θ t) {q0 h : ℝ} (hh : 0 < h) {k : ℤ} (hk : dlgQ q0 h k ∈ U) (hk1 : dlgQ q0 h (k + 1) ∈ U) :
    dlgP Θ q0 h k ≤ dlgP Θ q0 h (k + 1) := by
  have hmono : StrictMonoOn Θ U := by
    refine strictMonoOn_of_deriv_pos D.convex ?_ ?_
    · exact fun t ht => (D.Θd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [D.isOpen.interior_eq] at ht
      rw [(D.Θd t ht).deriv]; exact hθ t ht
  unfold dlgP
  rw [dlgQ_succ] at hk1 ⊢
  exact div_le_div_of_nonneg_right (hmono.monotoneOn hk hk1 (by linarith)) hh.le

/-- **Zero bonds of a bulk solution.**  If `|Y_k - R w_k cos(P_k - φ₀)| ≤ ε R w_k` at the sites `k, k+1` (`R > 0`, `w > 0`, `ε = C h` in `dlg_bulk`) and `Y`
changes sign across the bond `(k, k+1)`, then some zero `(2j+1)π/2` of the cosine lies in `[P_k - φ₀ - (π/2)ε, P_{k+1} - φ₀ + (π/2)ε]`. -/
theorem dlg_bulk_zero_bond {A θ w Θ : ℝ → ℝ} {U : Set ℝ} {lo hi M : ℝ} (D : DlgData A θ w Θ U lo hi M)
    (hθ : ∀ t ∈ U, 0 < θ t) {q0 h ε R φ0 : ℝ} (hh : 0 < h) (hε : 0 ≤ ε) (hR : 0 < R) {Y : ℤ → ℝ} {k : ℤ}
    (hk : dlgQ q0 h k ∈ U) (hk1 : dlgQ q0 h (k + 1) ∈ U)
    (h0 : |Y k - R * w (dlgQ q0 h k) * Real.cos (dlgP Θ q0 h k - φ0)| ≤ ε * (R * w (dlgQ q0 h k)))
    (h1 : |Y (k + 1) - R * w (dlgQ q0 h (k + 1)) * Real.cos (dlgP Θ q0 h (k + 1) - φ0)| ≤
      ε * (R * w (dlgQ q0 h (k + 1))))
    (hch : Y k * Y (k + 1) ≤ 0) :
    ∃ j : ℤ, dlgP Θ q0 h k - φ0 - Real.pi / 2 * ε ≤ (2 * j + 1) * Real.pi / 2 ∧
      (2 * j + 1) * Real.pi / 2 ≤ dlgP Θ q0 h (k + 1) - φ0 + Real.pi / 2 * ε := by
  have hw0 : 0 < w (dlgQ q0 h k) := D.lo_pos.trans_le (D.wb _ hk).1
  have hw1 : 0 < w (dlgQ q0 h (k + 1)) := D.lo_pos.trans_le (D.wb _ hk1).1
  exact dlg_zero_localisation (mul_pos hR hw0) (mul_pos hR hw1) hε h0 h1 hch
    (by linarith [dlg_phase_mono D hθ hh hk hk1])

/-- info: 'FormalResearch.Special.dlg_zero_localisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dlg_zero_localisation

/-- info: 'FormalResearch.Special.dlg_bulk_zero_bond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dlg_bulk_zero_bond

end FormalResearch.Special
