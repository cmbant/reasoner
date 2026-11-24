module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroDict
public import FormalResearch.ModularBootstrap.Upper.Positivity.DesignReal
public import FormalResearch.ModularBootstrap.Upper.Window.TailGeometry

/-!
# The strip factor `T_{χ(p)}` in window coordinates (`upper_transfer.tex`, `ut:T2`, Region I)

With `x = ξ_* + λσ` and `χ(p) = ξ_* + λσ_p`, `σ_p = -p/κ`, the factor `T_{χ(p)}(x) = tanh(πλ(σ-σ_p)/2)
tanh(π ξ_* + πλ(σ+σ_p)/2)` equals `(πλ/(2√2))(σ - σ_p)(1 + O(λ))`:

* `tanh_sub_self_le`: `|tanh a - a| ≤ |a|³`;
* `blaschkeT_window_bound`: `|T_{χ(p)}(x) - (πλ/(2√2))(σ - σ_p)| ≤ C λ² |σ - σ_p|` for `0 < λ ≤ λ₀`,
  `|σ|, |σ_p| ≤ S` (the multiplicative `1 + O(λ)` form without dividing by `σ - σ_p`);
* `twoZeroT_window_bound`: the same at `λ = lambdaComb c'`, for large `c'` and for the design's `σ_p = -p/κ`,
  uniformly on the set where `|σ_p| ≤ S`; `-(πλ/(2√2κ))(u - p)` with `u = -κσ`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Window.Tail

/-- `|tanh a - a| ≤ |a|³`. -/
lemma tanh_sub_self_le (a : ℝ) : |Real.tanh a - a| ≤ |a| ^ 3 := by
  have hnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ t - Real.tanh t ∧ t - Real.tanh t ≤ t ^ 3 := by
    intro t ht
    have h1 : Real.tanh t ≤ t := tanh_le_self' ht
    refine ⟨by linarith, ?_⟩
    have hd : ∀ y : ℝ, HasDerivAt (fun s : ℝ => s ^ 3 / 3 + Real.tanh s - s)
        (y ^ 2 + (Real.cosh y)⁻¹ ^ 2 - 1) y := fun y => by
      have ht_d : HasDerivAt Real.tanh ((Real.cosh y)⁻¹ ^ 2) y := by
        rw [show Real.tanh = fun s => Real.sinh s / Real.cosh s from funext Real.tanh_eq_sinh_div_cosh]
        refine ((Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) (Real.cosh_pos y).ne').congr_deriv ?_
        field_simp [(Real.cosh_pos y).ne']
        linarith [Real.cosh_sq_sub_sinh_sq y]
      have h3 : HasDerivAt (fun s : ℝ => s ^ 3 / 3) (y ^ 2) y := by
        simpa using ((hasDerivAt_pow 3 y).div_const 3)
      exact (h3.add ht_d).sub (hasDerivAt_id y)
    have hmono : MonotoneOn (fun s : ℝ => s ^ 3 / 3 + Real.tanh s - s) (Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
        (fun y _ => (hd y).continuousAt.continuousWithinAt)
        (fun y _ => (hd y).differentiableAt.differentiableWithinAt) (fun y hy => ?_)
      rw [(hd y).deriv]
      have hy' : 0 < y := by simpa using hy
      have hth : Real.tanh y ≤ y := tanh_le_self' hy'.le
      have hth0 : 0 ≤ Real.tanh y := by
        rw [Real.tanh_eq_sinh_div_cosh]
        exact div_nonneg (Real.sinh_nonneg_iff.mpr hy'.le) (Real.cosh_pos y).le
      have hid : Real.tanh y ^ 2 + (Real.cosh y)⁻¹ ^ 2 = 1 := by
        rw [Real.tanh_eq_sinh_div_cosh]
        field_simp [(Real.cosh_pos y).ne']
        linarith [Real.cosh_sq_sub_sinh_sq y]
      nlinarith
    have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    simp only [Real.tanh_zero, zero_pow (by norm_num : 3 ≠ 0), zero_div, add_zero, sub_zero] at this
    linarith
  rcases le_total 0 a with ha | ha
  · obtain ⟨h1, h2⟩ := hnn a ha
    rw [abs_of_nonneg ha, abs_sub_comm, abs_of_nonneg h1]; exact h2
  · obtain ⟨h1, h2⟩ := hnn (-a) (neg_nonneg.2 ha)
    rw [Real.tanh_neg] at h1 h2
    rw [abs_of_nonpos ha, abs_of_nonneg (by linarith : 0 ≤ Real.tanh a - a)]
    nlinarith

/-- `T_{χ(p)}(x)` in window coordinates: for `0 < λ ≤ λ₀` and `|σ|, |σ_p| ≤ S`,
`|T_{ξ_*+λσ_p}(ξ_*+λσ) - (πλ/(2√2))(σ - σ_p)| ≤ C λ² |σ - σ_p|`. -/
theorem blaschkeT_window_bound (S : ℝ) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ l : ℝ, 0 < l → l ≤ l₀ → ∀ σ σp : ℝ, |σ| ≤ S → |σp| ≤ S →
      ‖blaschkeT ((xiStar + l * σp : ℝ) : ℂ) ((xiStar + l * σ : ℝ) : ℂ) -
          ((π * l / (2 * Real.sqrt 2) * (σ - σp) : ℝ) : ℂ)‖ ≤ C * l ^ 2 * |σ - σp| := by
  have hξ := xiStar_pos
  have hpi := Real.pi_pos
  refine ⟨π ^ 2 * S * (1 + π * S) / 2, by positivity, min 1 (xiStar / (2 * (S + 1))),
    lt_min one_pos (by positivity), fun l hl hl0 σ σp hσ hσp => ?_⟩
  have hl1 : l ≤ 1 := hl0.trans (min_le_left _ _)
  have hl2 : l ≤ xiStar / (2 * (S + 1)) := hl0.trans (min_le_right _ _)
  have hlS : l * S ≤ xiStar / 2 := by
    have : l * (2 * (S + 1)) ≤ xiStar := by rwa [le_div_iff₀ (by positivity)] at hl2
    nlinarith
  rw [blaschkeT_ofReal_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  set a : ℝ := π * ((xiStar + l * σ) - (xiStar + l * σp)) / 2 with ha
  set b : ℝ := π * ((xiStar + l * σ) + (xiStar + l * σp)) / 2 with hb
  have hδ : |σ - σp| ≤ 2 * S := by
    calc |σ - σp| ≤ |σ| + |σp| := abs_sub _ _
      _ ≤ 2 * S := by linarith
  have ha_eq : a = π * l * (σ - σp) / 2 := by rw [ha]; ring
  have hb_eq : b = π * xiStar + π * l * (σ + σp) / 2 := by rw [hb]; ring
  have habs : |a| = π * l * |σ - σp| / 2 := by
    rw [ha_eq, abs_div, abs_mul, abs_mul, abs_of_pos hpi, abs_of_pos hl]; norm_num
  have haS : |a| ≤ π * l * S := by
    rw [habs]; nlinarith [mul_le_mul_of_nonneg_left hδ (mul_pos hpi hl).le]
  have hbe : |b - π * xiStar| ≤ π * l * S := by
    rw [hb_eq]
    have : π * xiStar + π * l * (σ + σp) / 2 - π * xiStar = π * l * ((σ + σp) / 2) := by ring
    rw [this, abs_mul, abs_of_pos (mul_pos hpi hl)]
    refine mul_le_mul_of_nonneg_left ?_ (mul_pos hpi hl).le
    rw [abs_div]
    have := abs_add_le σ σp
    norm_num
    linarith
  have hbpos : 0 < b := by
    have := (abs_le.1 hbe).1
    nlinarith
  have hT0 : Real.tanh (π * xiStar) = 1 / Real.sqrt 2 := tanh_pi_xiStar
  have hkey : Real.tanh a * Real.tanh b - π * l / (2 * Real.sqrt 2) * (σ - σp) =
      (Real.tanh a - a) * Real.tanh b + a * (Real.tanh b - Real.tanh (π * xiStar)) := by
    rw [hT0, ha_eq]
    have : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    ring
  have e1 : |(Real.tanh a - a) * Real.tanh b| ≤ |a| * (π * l * S) ^ 2 := by
    rw [abs_mul]
    calc |Real.tanh a - a| * |Real.tanh b| ≤ |a| ^ 3 * 1 :=
          mul_le_mul (tanh_sub_self_le a) (Real.abs_tanh_lt_one b).le (abs_nonneg _) (by positivity)
      _ = |a| * |a| ^ 2 := by ring
      _ ≤ |a| * (π * l * S) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact pow_le_pow_left₀ (abs_nonneg _) haS 2
  have e2 : |Real.tanh b - Real.tanh (π * xiStar)| ≤ π * l * S := by
    have hπx : 0 < π * xiStar := by positivity
    rcases le_total (π * xiStar) b with h | h
    · have h1 := tanh_sub_le' hπx.le h
      have h2 := tanh_mono_real h
      rw [abs_of_nonneg (by linarith)]
      exact h1.trans ((le_abs_self _).trans hbe)
    · have h1 := tanh_sub_le' hbpos.le h
      have h2 := tanh_mono_real h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      exact h1.trans ((le_abs_self _).trans (by rwa [abs_sub_comm] at hbe))
  rw [hkey]
  have e3 : |a * (Real.tanh b - Real.tanh (π * xiStar))| ≤ |a| * (π * l * S) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left e2 (abs_nonneg _)
  have hplS : π * l * S ≤ π * S := by nlinarith [mul_nonneg hpi.le hS]
  calc _ ≤ |(Real.tanh a - a) * Real.tanh b| + |a * (Real.tanh b - Real.tanh (π * xiStar))| :=
        abs_add_le _ _
    _ ≤ |a| * (π * l * S) ^ 2 + |a| * (π * l * S) := add_le_add e1 e3
    _ = |a| * (π * l * S) * (1 + π * l * S) := by ring
    _ ≤ |a| * (π * l * S) * (1 + π * S) := by
        refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = π ^ 2 * S * (1 + π * S) / 2 * l ^ 2 * |σ - σp| := by rw [habs]; ring

/-- The design's `T_{χ(p)}` factor in window coordinates, at `λ = lambdaComb c'`, for large `c'`:
`|T_{χ(p)}(ξ_* + λσ) - (πλ/(2√2))(σ - σ_p)| ≤ C λ² |σ - σ_p|`, `σ_p = -p/κ`. -/
theorem twoZeroT_window_bound (S : ℝ) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ c' : ℝ in atTop, ∀ σ p : ℝ, |σ| ≤ S → |p / kappaAiry| ≤ S →
      ‖blaschkeT ((xiStar + lambdaComb c' * (-p / kappaAiry) : ℝ) : ℂ) ((xiStar + lambdaComb c' * σ : ℝ) : ℂ) -
          ((π * lambdaComb c' / (2 * Real.sqrt 2) * (σ - (-p / kappaAiry)) : ℝ) : ℂ)‖ ≤
        C * lambdaComb c' ^ 2 * |σ - (-p / kappaAiry)| := by
  obtain ⟨C, hC, l₀, hl₀, h⟩ := blaschkeT_window_bound S hS
  refine ⟨C, hC, ?_⟩
  filter_upwards [tendsto_lambdaComb_atTop.eventually (Iic_mem_nhds hl₀), eventually_gt_atTop (0 : ℝ)]
    with c' hc' hc0 σ p hσ hp
  have hlam : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hc0) _
  refine h _ hlam hc' σ (-p / kappaAiry) hσ ?_
  rwa [neg_div, abs_neg]

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.blaschkeT_window_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms blaschkeT_window_bound

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroT_window_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroT_window_bound

end FormalResearch.ModularBootstrap.TwoLevel
