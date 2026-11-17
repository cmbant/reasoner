module

public import FormalResearch.Special.AiryClarkMid

/-!
# The zeros of `Ai'` far on the negative axis

Two statements in the variable `y` with `-y` the zero (DLMF 9.9.18, 9.9.19 for the phase `(n - 3/4)π`
of the `n`-th zero `a'_n`, i.e. `k = n - 1` below):

* `airyAi'_zero_location`: for `y ≥ 4`, a zero `-y` of `Ai'` has `|(2/3)y^(3/2) - (k+1/4)π| ≤ 1.12 y^(-3/2)`
  for an integer `k`.  This is `airyAi'_zero_location_r` (`AiryPruferAsym`) restated in `y = r²`; nothing new
  beyond the change of variable.
* `airyAi'_zero_window_existsUnique`: for every integer `k ≥ 2` exactly one `y > 0` has `Ai'(-y) = 0` and
  `|(2/3)y^(3/2) - (k+1/4)π| < π/3`.  Existence is the Prüfer-gap zero of `airyAi'_existsUnique_zero_gap`
  (`AiryClarkMid`) with its `0.14` phase bound; uniqueness within the window is new: Rolle in the radius
  variable plus the nonvanishing of `Ai` on the window (from `AiryAsymNeg`).

Numerical check (mpmath, 40 digits, zeros `a'_n`, `n = 3..1500` and `n = 10^4, 10^5, 10^6`, `y ≥ 4`): the
scaled error `y^(3/2) |(2/3)y^(3/2) - (n - 3/4)π|` rises from `0.14449` (`n = 3`) to `0.1458333333`, its
maximum, which is `7/48` to the digits shown (the DLMF 9.9.18 coefficient `-7/48`); the proved constant `1.12`
is much weaker.  This is a numerical observation, not part of the formal statements.

Not formalised here: the sharp constant `7/48` and the next asymptotic term, and the matching of the integer
`k` with the ordered zeros `a'_1 > a'_2 > ...`; only the gap bracket `a_{n+1} < b < a_n` (`k = n`) is
available in `AiryClarkMid`.
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.Special

/-- In a derivative phase window, `Ai` is nonzero; this is the Rolle obstruction. -/
lemma aizd_airyAi_ne_zero_window {r : ℝ} {k : ℤ} (hk : 2 ≤ k)
    (hw : |2 / 3 * r ^ 3 - (k + 1 / 4) * π| ≤ π / 3) :
    airyAi (-(r ^ 2)) ≠ 0 := by
  have hkp : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hw' := abs_le.mp hw
  have hr : 2 ≤ r := by
    by_contra h
    have hrlt : r < 2 := lt_of_not_ge h
    have hr0 : 0 ≤ r := by
      by_contra hn
      have hrneg : r < 0 := lt_of_not_ge hn
      have hc : 2 / 3 * r ^ 3 - (k + 1 / 4) * π < -π / 3 := by
        have hcube : r ^ 3 < 0 := by
          nlinarith [mul_pos (mul_pos (neg_pos.mpr hrneg) (neg_pos.mpr hrneg))
            (neg_pos.mpr hrneg)]
        nlinarith [Real.pi_gt_three]
      linarith [hw'.1]
    have hc : r ^ 3 < 8 := by
      have hfac : 0 < 4 + 2 * r + r ^ 2 := by positivity
      nlinarith [mul_pos (by linarith : 0 < 2 - r) hfac]
    have hlow : 2 / 3 * r ^ 3 - (k + 1 / 4) * π < -π / 3 := by
      nlinarith [hc, hkp, Real.pi_gt_three]
    linarith [hw'.1]
  have hphase : 2 / 3 * r ^ 3 - π / 4 =
      (2 / 3 * r ^ 3 - (k + 1 / 4) * π) + k * π := by ring
  have hcos : 1 / 2 ≤ |Real.cos (2 / 3 * r ^ 3 - π / 4)| := by
    rw [hphase, Real.cos_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
    exact half_le_abs_cos (by simpa [abs_sub_comm] using hw)
  have hsign := airyAi_neg_sq_mul_cos_pos (by linarith : 1 ≤ r) hcos
  intro hz
  rw [hz, zero_mul] at hsign
  exact (not_lt_of_ge (by norm_num : (0 : ℝ) ≤ 0)) hsign

lemma aizd_hasDerivAt_radius (r : ℝ) :
    HasDerivAt (fun x : ℝ => airyAi' (-(x ^ 2)))
      (2 * r ^ 3 * airyAi (-(r ^ 2))) r := by
  have harg : HasDerivAt (fun x : ℝ => -(x ^ 2)) (-(2 * r)) r := by
    exact (hasDerivAt_pow 2 r).neg.congr_deriv (by simp)
  have h := (hasDerivAt_airyAi' (-(r ^ 2))).comp r harg
  convert h using 1
  · rfl
  · ring

lemma aizd_continuous_radius :
    Continuous (fun r : ℝ => airyAi' (-(r ^ 2))) := by
  exact continuous_iff_continuousAt.mpr fun r => (aizd_hasDerivAt_radius r).continuousAt

/-- Every zero `-y` of `Ai'` with `y ≥ 4` has the explicit DLMF 9.9.19-scale location. -/
theorem airyAi'_zero_location {y : ℝ} (hy : 4 ≤ y) (hz : airyAi' (-y) = 0) :
    ∃ k : ℤ, |2 / 3 * y ^ (3 / 2 : ℝ) - (k + 1 / 4) * π| ≤
      1.12 * y ^ (-(3 / 2 : ℝ)) := by
  have hy0 : 0 < y := by linarith
  have hr : 2 ≤ √y := by
    rw [show (2 : ℝ) = √(2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  obtain ⟨k, hk⟩ := airyAi'_zero_location_r hr
    (by rw [Real.sq_sqrt hy0.le]; exact hz)
  refine ⟨k, ?_⟩
  rw [← sqrt_cube_eq_rpow hy0, Real.rpow_neg hy0.le, ← sqrt_cube_eq_rpow hy0]
  convert hk using 1
  field_simp

/-- For each integer `k ≥ 2`, exactly one positive `y` lies in its `Ai'` phase window. -/
theorem airyAi'_zero_window_existsUnique {k : ℤ} (hk : 2 ≤ k) :
    ∃! y : ℝ, 0 < y ∧
      |2 / 3 * y ^ (3 / 2 : ℝ) - (k + 1 / 4) * π| < π / 3 ∧ airyAi' (-y) = 0 := by
  have hn : 2 ≤ k.toNat := by omega
  have hkeq : (k.toNat : ℤ) = k := by omega
  obtain ⟨b, hb, _⟩ := airyAi'_existsUnique_zero_gap (n := k.toNat) (by omega)
  rcases hb with ⟨hb1, hb2, hbz⟩
  have hbneg : b < 0 := hb2.trans (airyZero_neg k.toNat)
  let r := √(-b)
  have hr0 : 0 < r := Real.sqrt_pos.mpr (neg_pos.mpr hbneg)
  have hrsq : r ^ 2 = -b := Real.sq_sqrt (neg_nonneg.mpr hbneg.le)
  have hphase := airyAi'_zero_phase_of_gap (n := k.toNat) hn hb1 hb2 hbz
  have hphase' : |2 / 3 * r ^ 3 - ((k : ℝ) + 1 / 4) * π| ≤ 0.14 := by
    have hkeqR : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast hkeq
    simpa [r, hkeqR] using hphase.2.2.2
  have hwindow : |2 / 3 * r ^ 3 - (k + 1 / 4) * π| < π / 3 := by
    have hpi : (0.14 : ℝ) < π / 3 := by nlinarith [Real.pi_gt_three]
    exact (hphase'.trans_lt hpi)
  have hpow : ((-b) : ℝ) ^ (3 / 2 : ℝ) = r ^ 3 := by
    change ((-b) : ℝ) ^ (3 / 2 : ℝ) = (√(-b)) ^ 3
    rw [← sqrt_cube_eq_rpow (neg_pos.mpr hbneg)]
  refine ⟨-b, ⟨neg_pos.mpr hbneg, ?_, ?_⟩, ?_⟩
  · rw [hpow]; exact hwindow
  · rw [neg_neg]; exact hbz
  · intro y hy
    have hy0 : 0 < y := hy.1
    have hyphase : |2 / 3 * (√y) ^ 3 - (k + 1 / 4) * π| < π / 3 := by
      have hpow' : y ^ (3 / 2 : ℝ) = (√y) ^ 3 := by
        rw [← sqrt_cube_eq_rpow hy0]
      have hwin := hy.2.1
      rw [hpow'] at hwin
      exact hwin
    have hr1 : 0 < √y := Real.sqrt_pos.mpr hy0
    have hz1 : airyAi' (-((√y) ^ 2)) = 0 := by
      rw [Real.sq_sqrt hy0.le]
      exact hy.2.2
    have hr2 : 0 < r := hr0
    have hphaseR : |2 / 3 * r ^ 3 - (k + 1 / 4) * π| < π / 3 := hwindow
    have hzR : airyAi' (-(r ^ 2)) = 0 := by
      rw [hrsq]
      simpa using hbz
    have hne : ∀ x : ℝ, 0 < x →
        |2 / 3 * x ^ 3 - (k + 1 / 4) * π| ≤ π / 3 →
        airyAi (-(x ^ 2)) ≠ 0 := by
      intro x hx hxw
      exact aizd_airyAi_ne_zero_window hk hxw
    have hnot : √y = r := by
      by_contra hneq
      rcases lt_or_gt_of_ne hneq with hlt | hgt
      · obtain ⟨c, hc, hcz⟩ := exists_hasDerivAt_eq_zero hlt
          aizd_continuous_radius.continuousOn (hz1.trans hzR.symm)
          (fun x _ => aizd_hasDerivAt_radius x)
        have hcpos : 0 < c := hr1.trans hc.1
        have hcwindow : |2 / 3 * c ^ 3 - (k + 1 / 4) * π| ≤ π / 3 := by
          have hyphase' := hyphase.le
          have hphaseR' := hphaseR.le
          rw [abs_le] at hyphase' hphaseR'
          rw [abs_le]
          constructor <;> nlinarith [pow_lt_pow_left₀ hc.1 hr1.le (by norm_num : 3 ≠ 0),
            pow_lt_pow_left₀ hc.2 (hr1.trans hc.1).le (by norm_num : 3 ≠ 0), hyphase', hphaseR']
        have hcAi := hne c hcpos hcwindow
        have hcne : 2 * c ^ 3 * airyAi (-(c ^ 2)) ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 (ne_of_gt hcpos))) hcAi
        exact hcne hcz
      · obtain ⟨c, hc, hcz⟩ := exists_hasDerivAt_eq_zero hgt
          aizd_continuous_radius.continuousOn (hzR.trans hz1.symm)
          (fun x _ => aizd_hasDerivAt_radius x)
        have hcpos : 0 < c := hr2.trans hc.1
        have hcwindow : |2 / 3 * c ^ 3 - (k + 1 / 4) * π| ≤ π / 3 := by
          have hyphase' := hyphase.le
          have hphaseR' := hphaseR.le
          rw [abs_le] at hyphase' hphaseR'
          rw [abs_le]
          constructor <;> nlinarith [pow_lt_pow_left₀ hc.1 hr2.le (by norm_num : 3 ≠ 0),
            pow_lt_pow_left₀ hc.2 (hr2.trans hc.1).le (by norm_num : 3 ≠ 0), hyphase', hphaseR']
        have hcAi := hne c hcpos hcwindow
        have hcne : 2 * c ^ 3 * airyAi (-(c ^ 2)) ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 (ne_of_gt hcpos))) hcAi
        exact hcne hcz
    have : y = -b := by
      have := congrArg (fun x : ℝ => x ^ 2) hnot
      rw [Real.sq_sqrt hy0.le, hrsq] at this
      linarith
    exact this

/-- info: 'FormalResearch.Special.airyAi'_zero_location' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi'_zero_location

/-- info: 'FormalResearch.Special.airyAi'_zero_window_existsUnique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi'_zero_window_existsUnique

end FormalResearch.Special
