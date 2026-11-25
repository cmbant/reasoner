module

public import FormalResearch.SignUncertainty.StripAdmissLift
public import FormalResearch.SignUncertainty.StripAdmissOsc
public import FormalResearch.CohnElkies.OuterWeightedBound
public import FormalResearch.CohnElkies.AirySeedFloors
public import FormalResearch.CohnElkies.MellinLiftIntegrals
public import FormalResearch.CohnElkies.PieceCPhase

/-!
# `uct:admiss`, the logarithmic tail `(uct:gen-tail)`

Source: `CFT/sign_uncertainty/paper/mellin_airy_toolkit.tex`, proof of Lemma T.8 (`uct:admiss`) (2): with `g = p_c · W̃(i·)`, `p_c(τ) = (1 - iτ)^{-1/2} e^{B_c(iτ)}`
(`outerK`), the vertical representation at `σ = 0` reads `(f ρ₀)(cξ) = (2πξ)⁻¹ ∫ g(τ) e^{ic Φ_Ph(τ; L)} dτ`, `L = log π²ξ`, and the oscillatory tail lemma
`osc_tail` (`StripAdmissOsc`) with the phase facts `Φ_Ph' ≥ L/2` on `|τ| ≤ τ_*(L)`, `|Φ_Ph''| ≤ 2`, `|Φ_Ph'''| ≤ π²/3` gives `L^{-1-α}`.

* `StripEdge0`: hypothesis (M3) for the edge trace `g_0(τ) = W̃(iτ)` (the edge `ζ = 1` enters only part (3) of `uct:admiss`, not formalised here);
* `oscData_mul`: `p_c · g_0` satisfies the amplitude hypotheses of `osc_tail`;
* `admiss_tail`: `|(f ρ₀)(cξ)| ≤ C' ξ⁻¹ L^{-1-α}` for `L ≥ 4`.

Status: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- The edge trace `g_0(τ) = W̃(iτ)`. -/
noncomputable def stripEdge0 (W : ℂ → ℂ) (τ : ℝ) : ℂ := W ((τ : ℂ) * Complex.I)

/-- Hypothesis (M3) of `uct:admiss` for the edge trace `g_0 = W̃(i ·)`: `C²` off `0`, `|∂^j(g_0 - g_0(0))| ≤ C |τ|^{α-j}` for `0 < |τ| ≤ 1`,
and `|∂^j g_0| ≤ C (1+|τ|)^{-2}` for `|τ| ≥ 1/2` (`j = 0, 1, 2`). -/
structure StripEdge0 (α : ℝ) (W : ℂ → ℂ) : Prop where
  c2 : ContDiffOn ℝ 2 (stripEdge0 W) {τ : ℝ | τ ≠ 0}
  near : ∃ C : ℝ, ∀ τ : ℝ, τ ≠ 0 → |τ| ≤ 1 →
    ‖stripEdge0 W τ - stripEdge0 W 0‖ ≤ C * |τ| ^ α ∧ ‖deriv (stripEdge0 W) τ‖ ≤ C * |τ| ^ (α - 1) ∧
      ‖deriv (deriv (stripEdge0 W)) τ‖ ≤ C * |τ| ^ (α - 2)
  far : ∃ C : ℝ, ∀ τ : ℝ, 1 / 2 ≤ |τ| →
    ‖stripEdge0 W τ‖ ≤ C * (1 + |τ|) ^ (-(2 : ℝ)) ∧ ‖deriv (stripEdge0 W) τ‖ ≤ C * (1 + |τ|) ^ (-(2 : ℝ)) ∧
      ‖deriv (deriv (stripEdge0 W)) τ‖ ≤ C * (1 + |τ|) ^ (-(2 : ℝ))

lemma rpow_quarter_le (τ : ℝ) : (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) ≤ 2 * (1 + |τ|) ^ (-(1 / 2 : ℝ)) := by
  have hs : 0 < 1 + |τ| := by positivity
  have h1 : (1 + |τ|) ^ 2 * 2⁻¹ ≤ 1 + τ ^ 2 := by nlinarith [sq_abs τ, sq_nonneg (|τ| - 1)]
  have h2 : (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) ≤ ((1 + |τ|) ^ 2 * 2⁻¹) ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
  have h3 : ((1 + |τ|) ^ 2 * 2⁻¹) ^ (-(1 / 4 : ℝ)) = (1 + |τ|) ^ (-(1 / 2 : ℝ)) * 2 ^ (1 / 4 : ℝ) := by
    rw [Real.mul_rpow (by positivity) (by norm_num), Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    norm_num
  have h4 : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
    calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  rw [h3] at h2
  calc _ ≤ _ := h2
    _ ≤ (1 + |τ|) ^ (-(1 / 2 : ℝ)) * 2 := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := mul_comm _ _

section mul

variable {α : ℝ} {k g0 : ℝ → ℂ}

lemma hasDerivAt_mul_amp (hk : ContDiff ℝ 2 k) {τ : ℝ} (h1 : HasDerivAt g0 (deriv g0 τ) τ)
    (h2 : HasDerivAt (deriv g0) (deriv (deriv g0) τ) τ) :
    HasDerivAt (fun x => k x * g0 x) (deriv k τ * g0 τ + k τ * deriv g0 τ) τ ∧
      HasDerivAt (fun x => deriv k x * g0 x + k x * deriv g0 x)
        (deriv (deriv k) τ * g0 τ + 2 * (deriv k τ * deriv g0 τ) + k τ * deriv (deriv g0) τ) τ := by
  have hk1 : ContDiff ℝ 1 (deriv k) := hk.iterate_deriv' 1 1
  have hkd : HasDerivAt k (deriv k τ) τ := ((hk.differentiable (by norm_num)) τ).hasDerivAt
  have hkd2 : HasDerivAt (deriv k) (deriv (deriv k) τ) τ := ((hk1.differentiable one_ne_zero) τ).hasDerivAt
  refine ⟨hkd.mul h1, ?_⟩
  refine ((hkd2.mul h1).add (hkd.mul h2)).congr_deriv ?_
  ring

/-- The product `k · g0` satisfies the amplitude hypotheses of `osc_tail`. -/
theorem oscData_mul (hα0 : 0 < α) (hα1 : α < 1) {Ck C0 : ℝ} (hCk : 0 ≤ Ck) (hC0 : 0 ≤ C0)
    (hk : ContDiff ℝ 2 k) (hk0 : k 0 = 1)
    (hkb : ∀ τ : ℝ, ‖k τ‖ ≤ Ck * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) ∧ ‖deriv k τ‖ ≤ Ck * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) ∧
      ‖deriv (deriv k) τ‖ ≤ Ck * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)))
    (hg0c : Continuous g0) (hg0 : ContDiffOn ℝ 2 g0 {τ : ℝ | τ ≠ 0})
    (hnear : ∀ τ : ℝ, τ ≠ 0 → |τ| ≤ 1 → ‖g0 τ - g0 0‖ ≤ C0 * |τ| ^ α ∧ ‖deriv g0 τ‖ ≤ C0 * |τ| ^ (α - 1) ∧
      ‖deriv (deriv g0) τ‖ ≤ C0 * |τ| ^ (α - 2))
    (hfar : ∀ τ : ℝ, 1 / 2 ≤ |τ| → ‖g0 τ‖ ≤ C0 * (1 + |τ|) ^ (-(2 : ℝ)) ∧
      ‖deriv g0 τ‖ ≤ C0 * (1 + |τ|) ^ (-(2 : ℝ)) ∧ ‖deriv (deriv g0) τ‖ ≤ C0 * (1 + |τ|) ^ (-(2 : ℝ))) :
    OscData α (fun τ => k τ * g0 τ) (Ck * (12 * C0 + 3 * ‖g0 0‖)) := by
  have hd1 : ∀ x : ℝ, x ≠ 0 → HasDerivAt g0 (deriv g0 x) x := fun x hx =>
    ((hg0.contDiffAt (isOpen_ne.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
  have hd2 : ∀ x : ℝ, x ≠ 0 → HasDerivAt (deriv g0) (deriv (deriv g0) x) x := fun x hx => by
    have h1 : ContDiffOn ℝ 1 (deriv g0) {τ : ℝ | τ ≠ 0} := hg0.deriv_of_isOpen isOpen_ne (by norm_num)
    exact ((h1.contDiffAt (isOpen_ne.mem_nhds hx)).differentiableAt one_ne_zero).hasDerivAt
  have hker : ∀ τ : ℝ, (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) ≤ 1 := fun τ =>
    Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg τ]) (by norm_num)
  have hker2 : ∀ τ : ℝ, (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) ≤ 2 * (1 + |τ|) ^ (-(1 / 2 : ℝ)) := rpow_quarter_le
  set a0 : ℝ := ‖g0 0‖ with ha0
  have ha00 : 0 ≤ a0 := norm_nonneg _
  have hCg0 : 0 ≤ Ck * (12 * C0 + 3 * a0) := by positivity
  -- derivative formulas off `0`
  have hderiv : ∀ τ : ℝ, τ ≠ 0 →
      deriv (fun x => k x * g0 x) τ = deriv k τ * g0 τ + k τ * deriv g0 τ ∧
      deriv (deriv (fun x => k x * g0 x)) τ =
        deriv (deriv k) τ * g0 τ + 2 * (deriv k τ * deriv g0 τ) + k τ * deriv (deriv g0) τ := by
    intro τ hτ
    have hA := (hasDerivAt_mul_amp hk (hd1 τ hτ) (hd2 τ hτ)).1
    refine ⟨hA.deriv, ?_⟩
    have hev : deriv (fun x => k x * g0 x) =ᶠ[𝓝 τ] fun x => deriv k x * g0 x + k x * deriv g0 x := by
      filter_upwards [isOpen_ne.mem_nhds hτ] with x hx
      exact (hasDerivAt_mul_amp hk (hd1 x hx) (hd2 x hx)).1.deriv
    rw [hev.deriv_eq]
    exact (hasDerivAt_mul_amp hk (hd1 τ hτ) (hd2 τ hτ)).2.deriv
  have hlip : ∀ τ : ℝ, ‖k τ - 1‖ ≤ Ck * |τ| := by
    intro τ
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := k) (C := Ck) (s := Set.univ) (x := 0) (y := τ)
      (fun x _ => (hk.differentiable (by norm_num)) x) (fun x _ => (hkb x).2.1.trans
        (mul_le_of_le_one_right hCk (hker x))) convex_univ trivial trivial
    rw [hk0, sub_zero, Real.norm_eq_abs] at this
    exact this
  refine ⟨hk.continuous.mul hg0c, hk.contDiffOn.mul hg0, ?_, ?_⟩
  · intro τ hτ h1
    obtain ⟨n0, n1, n2⟩ := hnear τ hτ h1
    obtain ⟨d1, d2⟩ := hderiv τ hτ
    have hτ0 : 0 < |τ| := abs_pos.mpr hτ
    have hp1 : |τ| ≤ |τ| ^ α := by
      calc |τ| = |τ| ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ |τ| ^ α := Real.rpow_le_rpow_of_exponent_ge hτ0 h1 hα1.le
    have hpα : |τ| ^ α ≤ 1 := Real.rpow_le_one (abs_nonneg _) h1 hα0.le
    have hq1 : 1 ≤ |τ| ^ (α - 1) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hτ0 h1 (by linarith)
    have hq12 : |τ| ^ (α - 1) ≤ |τ| ^ (α - 2) := Real.rpow_le_rpow_of_exponent_ge hτ0 h1 (by linarith)
    have hq2 : 1 ≤ |τ| ^ (α - 2) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hτ0 h1 (by linarith)
    have hq0 : 0 ≤ |τ| ^ (α - 1) := by positivity
    have hq20 : 0 ≤ |τ| ^ (α - 2) := by positivity
    have hpα0 : 0 ≤ |τ| ^ α := by positivity
    have kk := hkb τ
    have kb0 : ‖k τ‖ ≤ Ck := kk.1.trans (mul_le_of_le_one_right hCk (hker τ))
    have kb1 : ‖deriv k τ‖ ≤ Ck := kk.2.1.trans (mul_le_of_le_one_right hCk (hker τ))
    have kb2 : ‖deriv (deriv k) τ‖ ≤ Ck := kk.2.2.trans (mul_le_of_le_one_right hCk (hker τ))
    have g0b : ‖g0 τ‖ ≤ a0 + C0 := by
      calc ‖g0 τ‖ = ‖g0 0 + (g0 τ - g0 0)‖ := by rw [add_sub_cancel]
        _ ≤ ‖g0 0‖ + ‖g0 τ - g0 0‖ := norm_add_le _ _
        _ ≤ a0 + C0 * |τ| ^ α := by linarith
        _ ≤ a0 + C0 := by nlinarith
    refine ⟨?_, ?_, ?_⟩
    · show ‖k τ * g0 τ - k 0 * g0 0‖ ≤ _
      rw [hk0, one_mul]
      have e : k τ * g0 τ - g0 0 = k τ * (g0 τ - g0 0) + (k τ - 1) * g0 0 := by ring
      rw [e]
      calc _ ≤ ‖k τ * (g0 τ - g0 0)‖ + ‖(k τ - 1) * g0 0‖ := norm_add_le _ _
        _ ≤ Ck * (C0 * |τ| ^ α) + (Ck * |τ|) * a0 := by
          rw [norm_mul, norm_mul]
          exact add_le_add (mul_le_mul kb0 n0 (norm_nonneg _) hCk) (mul_le_mul (hlip τ) le_rfl (norm_nonneg _) (by positivity))
        _ ≤ Ck * (C0 * |τ| ^ α) + (Ck * |τ| ^ α) * a0 := by gcongr
        _ ≤ _ := by nlinarith [mul_nonneg hCk hpα0, mul_nonneg hCk ha00, mul_nonneg (mul_nonneg hCk hC0) hpα0,
            mul_nonneg (mul_nonneg hCk ha00) hpα0]
    · show ‖deriv (fun x => k x * g0 x) τ‖ ≤ _
      rw [d1]
      calc _ ≤ ‖deriv k τ * g0 τ‖ + ‖k τ * deriv g0 τ‖ := norm_add_le _ _
        _ ≤ Ck * (a0 + C0) + Ck * (C0 * |τ| ^ (α - 1)) := by
          rw [norm_mul, norm_mul]
          exact add_le_add (mul_le_mul kb1 g0b (norm_nonneg _) hCk) (mul_le_mul kb0 n1 (norm_nonneg _) hCk)
        _ ≤ _ := by
          have h1' : Ck * (a0 + C0) ≤ Ck * (a0 + C0) * |τ| ^ (α - 1) := le_mul_of_one_le_right (by positivity) hq1
          nlinarith [mul_nonneg hCk hC0, mul_nonneg hCk ha00, mul_nonneg (mul_nonneg hCk hC0) hq0,
            mul_nonneg (mul_nonneg hCk ha00) hq0]
    · show ‖deriv (deriv (fun x => k x * g0 x)) τ‖ ≤ _
      rw [d2]
      calc _ ≤ ‖deriv (deriv k) τ * g0 τ‖ + ‖2 * (deriv k τ * deriv g0 τ)‖ + ‖k τ * deriv (deriv g0) τ‖ :=
            (norm_add₃_le)
        _ ≤ Ck * (a0 + C0) + 2 * (Ck * (C0 * |τ| ^ (α - 1))) + Ck * (C0 * |τ| ^ (α - 2)) := by
          rw [norm_mul, norm_mul, norm_mul, norm_mul]
          have : ‖(2 : ℂ)‖ = 2 := by simp
          rw [this]
          refine add_le_add (add_le_add (mul_le_mul kb2 g0b (norm_nonneg _) hCk) ?_) (mul_le_mul kb0 n2 (norm_nonneg _) hCk)
          exact mul_le_mul_of_nonneg_left (mul_le_mul kb1 n1 (norm_nonneg _) hCk) (by norm_num)
        _ ≤ _ := by
          have h1' : Ck * (a0 + C0) ≤ Ck * (a0 + C0) * |τ| ^ (α - 2) := le_mul_of_one_le_right (by positivity) hq2
          have h2' : Ck * (C0 * |τ| ^ (α - 1)) ≤ Ck * (C0 * |τ| ^ (α - 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq12 hC0) hCk
          nlinarith [mul_nonneg hCk hC0, mul_nonneg hCk ha00, mul_nonneg (mul_nonneg hCk hC0) hq20,
            mul_nonneg (mul_nonneg hCk ha00) hq20]
  · intro τ hτ
    have hτ0 : τ ≠ 0 := by
      intro h; rw [h] at hτ; simp at hτ; linarith
    obtain ⟨d1, d2⟩ := hderiv τ hτ0
    obtain ⟨f0, f1, f2⟩ := hfar τ hτ
    have kk := hkb τ
    have hw : (1 + |τ|) ^ (-(5 / 2 : ℝ)) = (1 + |τ|) ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add (by positivity)]; norm_num
    set w1 : ℝ := (1 + |τ|) ^ (-(1 / 2 : ℝ)) with hw1
    set w2 : ℝ := (1 + |τ|) ^ (-(2 : ℝ)) with hw2
    have hw10 : 0 ≤ w1 := by positivity
    have hw20 : 0 ≤ w2 := by positivity
    have kb : ∀ x : ℝ, x ≤ Ck * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) → x ≤ 2 * Ck * w1 := fun x hx =>
      hx.trans (by nlinarith [mul_le_mul_of_nonneg_left (hker2 τ) hCk])
    have kb0 := kb _ kk.1
    have kb1 := kb _ kk.2.1
    have kb2 := kb _ kk.2.2
    have P : ∀ {u v : ℝ} {x y : ℂ}, ‖x‖ ≤ 2 * Ck * w1 → ‖y‖ ≤ C0 * w2 → ‖x * y‖ ≤ 2 * Ck * C0 * (w1 * w2) := by
      intro u v x y hx hy
      rw [norm_mul]
      calc ‖x‖ * ‖y‖ ≤ (2 * Ck * w1) * (C0 * w2) := mul_le_mul hx hy (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have P0 := P (u := 0) (v := 0) kb0 f0
    have P1a := P (u := 0) (v := 0) kb1 f0
    have P1b := P (u := 0) (v := 0) kb0 f1
    have P2a := P (u := 0) (v := 0) kb2 f0
    have P2b := P (u := 0) (v := 0) kb1 f1
    have P2c := P (u := 0) (v := 0) kb0 f2
    have hM : 0 ≤ 2 * Ck * C0 * (w1 * w2) := by positivity
    have hgoal : (1 + |τ|) ^ (-(5 / 2 : ℝ)) = w1 * w2 := hw
    refine ⟨?_, ?_, ?_⟩
    · show ‖k τ * g0 τ‖ ≤ _
      rw [hgoal]
      nlinarith [mul_nonneg (mul_nonneg hCk hC0) (mul_nonneg hw10 hw20), mul_nonneg (mul_nonneg hCk ha00) (mul_nonneg hw10 hw20)]
    · show ‖deriv (fun x => k x * g0 x) τ‖ ≤ _
      rw [d1, hgoal]
      refine (norm_add_le _ _).trans ?_
      nlinarith [mul_nonneg (mul_nonneg hCk hC0) (mul_nonneg hw10 hw20), mul_nonneg (mul_nonneg hCk ha00) (mul_nonneg hw10 hw20)]
    · show ‖deriv (deriv (fun x => k x * g0 x)) τ‖ ≤ _
      rw [d2, hgoal]
      refine (norm_add₃_le).trans ?_
      have : ‖(2 : ℂ) * (deriv k τ * deriv g0 τ)‖ ≤ 2 * (2 * Ck * C0 * (w1 * w2)) := by
        rw [norm_mul]
        have h2 : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h2]
        exact mul_le_mul_of_nonneg_left P2b (by norm_num)
      linarith [mul_nonneg (mul_nonneg hCk hC0) (mul_nonneg hw10 hw20), mul_nonneg (mul_nonneg hCk ha00) (mul_nonneg hw10 hw20)]

end mul

/-! ### The kernel and the phase on the imaginary axis -/

lemma outerK_zero' (c : ℝ) : outerK c 0 = 1 := by simp [outerK, FormalResearch.Asymptotics.binetDiff]

/-- `K₀(iτ, ξ) = k_c(τ) e^{i c Φ_Ph(τ; L)}`, `L = log π²ξ`. -/
lemma mellinK0_imag_outer (c ξ τ : ℝ) (hξ : 0 < ξ) :
    mellinK0 c ((τ : ℂ) * Complex.I) ξ =
      outerK c τ * Complex.exp (Complex.I * ((c * edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ : ℝ) : ℂ)) := by
  rw [mellinK0_imag_eq c ξ τ hξ, ← outerK_eq, edgePhi_eq_cubic_add_ceHth]
  have hmul : (τ : ℂ) * Complex.I = Complex.I * (τ : ℂ) := mul_comm _ _
  rw [hmul]
  unfold edgeR
  push_cast
  ring_nf

lemma edgePhi_contDiff' (L : ℝ) : ContDiff ℝ 3 (edgePhi L) := by
  rw [show edgePhi L = fun τ => L * τ - Real.pi ^ 2 / 36 * τ ^ 3 + edgeR τ from funext (edgePhi_eq_cubic_add_ceHth L)]
  exact (((contDiff_const.mul contDiff_id).sub (contDiff_const.mul (contDiff_id.pow 3))).add edgeR_contDiff)

/-- The phase `ψ = c Φ_Ph(·; L)`: `C³`, and the three bounds of `osc_tail` with `λ = cL/2` (for `L ≥ 4`). -/
lemma edge_phase_osc {c L : ℝ} (hc : 0 < c) (hL : 4 ≤ L) :
    ContDiff ℝ 3 (fun τ => c * edgePhi L τ) ∧
      (∀ τ : ℝ, |τ| ≤ tauStar L → c * L / 2 ≤ deriv (fun τ => c * edgePhi L τ) τ) ∧
      (∀ τ : ℝ, |deriv (deriv (fun τ => c * edgePhi L τ)) τ| ≤ c * L / 2) ∧
      (∀ τ : ℝ, |deriv (deriv (deriv (fun τ => c * edgePhi L τ))) τ| ≤ 2 * (c * L / 2)) := by
  have hL0 : 0 < L := by linarith
  have hcd : ContDiff ℝ 3 (fun τ => c * edgePhi L τ) := contDiff_const.mul (edgePhi_contDiff' L)
  have h1 : deriv (fun τ => c * edgePhi L τ) = fun τ => c * edgePhiDeriv L τ :=
    funext fun τ => ((hasDerivAt_edgePhi L τ).const_mul c).deriv
  have h2 : deriv (deriv (fun τ => c * edgePhi L τ)) = fun τ => c * edgePhiDeriv2 τ := by
    rw [h1]; exact funext fun τ => ((hasDerivAt_edgePhiDeriv L τ).const_mul c).deriv
  have hb2 : ∀ τ : ℝ, |edgePhiDeriv2 τ| ≤ 2 := by
    intro τ
    by_cases hτ : τ = 0
    · subst hτ; simp [edgePhiDeriv2]
    · have := edgePhiDeriv2_abs_le hτ
      have hτ0 : 0 < |τ| := abs_pos.mpr hτ
      rcases le_total |τ| 1 with h | h
      · have hπ2 : Real.pi ^ 2 ≤ 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
        calc |edgePhiDeriv2 τ| ≤ Real.pi ^ 2 / 6 * |τ| := this.trans (min_le_left _ _)
          _ ≤ Real.pi ^ 2 / 6 * 1 := mul_le_mul_of_nonneg_left h (by positivity)
          _ ≤ 2 := by linarith
      · calc |edgePhiDeriv2 τ| ≤ |τ|⁻¹ := this.trans (min_le_right _ _)
          _ ≤ 1 := inv_le_one_of_one_le₀ h
          _ ≤ 2 := by norm_num
  have hb3 : ∀ τ : ℝ, τ ≠ 0 → |c * edgePhiDeriv3 τ| ≤ 2 * (c * L / 2) := by
    intro τ hτ
    rw [abs_mul, abs_of_pos hc]
    have := edgePhiDeriv3_abs_le hτ
    have hπ : Real.pi ^ 2 / 3 ≤ 4 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    nlinarith
  refine ⟨hcd, ?_, ?_, ?_⟩
  · intro τ hτ
    rw [h1]
    have := edgePhiDeriv_ge hL0 hτ
    nlinarith
  · intro τ
    rw [h2]
    show |c * edgePhiDeriv2 τ| ≤ _
    rw [abs_mul, abs_of_pos hc]
    have := hb2 τ
    nlinarith
  · intro τ
    have hd2 : ContDiff ℝ 1 (deriv (deriv (fun τ => c * edgePhi L τ))) := hcd.iterate_deriv' 1 2
    have hd3 : Continuous (deriv (deriv (deriv (fun τ => c * edgePhi L τ)))) := hd2.continuous_deriv le_rfl
    have hS : IsClosed {τ : ℝ | |deriv (deriv (deriv (fun τ => c * edgePhi L τ))) τ| ≤ 2 * (c * L / 2)} :=
      isClosed_le hd3.abs continuous_const
    have hsub : ({0}ᶜ : Set ℝ) ⊆ {τ : ℝ | |deriv (deriv (deriv (fun τ => c * edgePhi L τ))) τ| ≤ 2 * (c * L / 2)} := by
      intro x hx
      have hx0 : x ≠ 0 := hx
      show |deriv (deriv (deriv (fun τ => c * edgePhi L τ))) x| ≤ _
      rw [h2]
      have : deriv (fun τ => c * edgePhiDeriv2 τ) x = c * edgePhiDeriv3 x :=
        ((hasDerivAt_edgePhiDeriv2_of_ne hx0).const_mul c).deriv
      rw [this]
      exact hb3 x hx0
    have := closure_minimal hsub hS
    rw [(dense_compl_singleton (0 : ℝ)).closure_eq] at this
    exact this (Set.mem_univ τ)

/-! ### Elementary bounds in `L` -/

lemma tauStar_eq {L : ℝ} (hL : 1 < L) : tauStar L = Real.exp ((L - 1) / 2) / Real.pi := by
  simp [tauStar, not_le.mpr hL]

lemma one_le_tauStar {L : ℝ} (hL : 4 ≤ L) : 1 ≤ tauStar L := by
  rw [tauStar_eq (by linarith), le_div_iff₀ Real.pi_pos, one_mul]
  have h1 : Real.exp (3 / 2) ≤ Real.exp ((L - 1) / 2) := Real.exp_le_exp.mpr (by linarith)
  have h2 := Real.quadratic_le_exp_of_nonneg (x := 3 / 2) (by norm_num)
  nlinarith [Real.pi_lt_d2]

lemma exp_quarter_ge {L : ℝ} (hL : 0 ≤ L) : L ^ 2 ≤ 32 * Real.exp (L / 4) := by
  have := Real.quadratic_le_exp_of_nonneg (x := L / 4) (by positivity)
  nlinarith [sq_nonneg L]

lemma rpow_one_add_le {L α : ℝ} (hL : 1 ≤ L) (hα1 : α ≤ 1) : L ^ (1 + α) ≤ L ^ 2 := by
  have : L ^ (1 + α) ≤ L ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  simpa using this

lemma tauStar_rpow_le {L α : ℝ} (hL : 4 ≤ L) (hα1 : α ≤ 1) :
    tauStar L ^ (-(1 / 2 : ℝ)) ≤ (32 * Real.pi ^ (1 / 2 : ℝ) * Real.exp (1 / 4)) * L ^ (-(1 + α)) := by
  have hL0 : 0 < L := by linarith
  rw [tauStar_eq (by linarith), Real.div_rpow (Real.exp_pos _).le Real.pi_pos.le, ← Real.exp_mul,
    Real.rpow_neg Real.pi_pos.le, div_inv_eq_mul]
  have h1 : L ^ (1 + α) ≤ 32 * Real.exp (L / 4) :=
    (rpow_one_add_le (by linarith) hα1).trans (exp_quarter_ge hL0.le)
  have h2 : Real.exp ((L - 1) / 2 * (-(1 / 2))) = Real.exp (1 / 4) * (Real.exp (L / 4))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]; congr 1; ring
  rw [h2, Real.rpow_neg hL0.le]
  have h3 : (Real.exp (L / 4))⁻¹ ≤ 32 * (L ^ (1 + α))⁻¹ := by
    rw [← one_div, ← one_div, mul_one_div, div_le_div_iff₀ (Real.exp_pos _) (Real.rpow_pos_of_pos hL0 _)]
    linarith
  have h4 : 0 ≤ Real.pi ^ (1 / 2 : ℝ) := by positivity
  have h5 : 0 ≤ Real.exp (1 / 4) := (Real.exp_pos _).le
  calc Real.exp (1 / 4) * (Real.exp (L / 4))⁻¹ * Real.pi ^ (1 / 2 : ℝ)
      ≤ Real.exp (1 / 4) * (32 * (L ^ (1 + α))⁻¹) * Real.pi ^ (1 / 2 : ℝ) := by gcongr
    _ = _ := by ring

lemma rpow_div_lam {c L α : ℝ} (hc : 0 < c) (hL : 0 < L) :
    L ^ (1 - α) / (c * L / 2) ^ 2 = 4 / c ^ 2 * L ^ (-(1 + α)) := by
  have : L ^ (1 - α) = L ^ (-(1 + α)) * L ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL]; congr 1; push_cast; ring
  rw [this]
  field_simp
  norm_num

/-- **`(uct:gen-tail)`** (`uct:admiss` (2), second half): for `c ≥ 2`, `0 < α < 1`, `W̃` satisfying (M1) and (M3) on the edge `Re ζ = 0`,
there is `C'` with `|(f ρ₀)(cξ)| ≤ C' ξ⁻¹ L^{-1-α}` for every `ξ = e^L/π²`, `L ≥ 4`. -/
theorem admiss_tail {c α : ℝ} {W : ℂ → ℂ} (hc : 2 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) (hW : StripM1 W)
    (hE : StripEdge0 α W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 4 ≤ L →
      |hankelRho0 c (c * (Real.exp L / Real.pi ^ 2)) * admissLift c W (c * (Real.exp L / Real.pi ^ 2))| ≤
        C * (Real.exp L / Real.pi ^ 2)⁻¹ * L ^ (-(1 + α)) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨CK, hCK, hKb⟩ := outerK_bounds
  obtain ⟨hk, hkb⟩ := hKb hc
  obtain ⟨C1, hC1⟩ := hE.near
  obtain ⟨C2, hC2⟩ := hE.far
  set C0 : ℝ := max |C1| |C2| with hC0
  have hC00 : 0 ≤ C0 := le_max_of_le_left (abs_nonneg _)
  have hg0c : Continuous (stripEdge0 W) := by
    have : Continuous fun τ : ℝ => (τ : ℂ) * Complex.I := by fun_prop
    exact hW.cont.comp_continuous this fun τ => by simp
  have hOsc := oscData_mul hα0 hα1 hCK.le hC00 hk (outerK_zero' c)
    (fun τ => ⟨by simpa using hkb 0 (by norm_num) τ,
      by simpa [iteratedDeriv_one] using hkb 1 (by norm_num) τ,
      by simpa [iteratedDeriv_succ, iteratedDeriv_one] using hkb 2 (by norm_num) τ⟩)
    hg0c hE.c2
    (fun τ hτ h1 => by
      obtain ⟨a, b, d⟩ := hC1 τ hτ h1
      have hp : ∀ r : ℝ, 0 ≤ r → C1 * r ≤ C0 * r := fun r hr =>
        mul_le_mul_of_nonneg_right ((le_abs_self C1).trans (le_max_left _ _)) hr
      exact ⟨a.trans (hp _ (by positivity)), b.trans (hp _ (by positivity)), d.trans (hp _ (by positivity))⟩)
    (fun τ hτ => by
      obtain ⟨a, b, d⟩ := hC2 τ hτ
      have hp : ∀ r : ℝ, 0 ≤ r → C2 * r ≤ C0 * r := fun r hr =>
        mul_le_mul_of_nonneg_right ((le_abs_self C2).trans (le_max_right _ _)) hr
      exact ⟨a.trans (hp _ (by positivity)), b.trans (hp _ (by positivity)), d.trans (hp _ (by positivity))⟩)
  obtain ⟨K, hK0, hK⟩ := osc_tail hα0 hα1 hOsc
  set M1 : ℝ := 32 * Real.pi ^ (1 / 2 : ℝ) * Real.exp (1 / 4) with hM1
  have hM10 : 0 ≤ M1 := by positivity
  refine ⟨K * (M1 + 1 + 4 / c ^ 2) / (2 * Real.pi), by positivity, fun L hL => ?_⟩
  have hL0 : 0 < L := by linarith
  set ξ : ℝ := Real.exp L / Real.pi ^ 2 with hξ
  have hξ0 : 0 < ξ := by positivity
  have hlog : Real.log (Real.pi ^ 2 * ξ) = L := by
    rw [hξ, mul_div_cancel₀ _ (by positivity), Real.log_exp]
  obtain ⟨hψ, hp1, hp2, hp3⟩ := edge_phase_osc hc0 hL
  have hT1 := one_le_tauStar hL
  have hos := hK hψ hT1 hL (by positivity : 0 < c * L / 2) hp1 (fun τ _ => hp2 τ) (fun τ _ => hp3 τ)
  have hv := admiss_vert_rep (c := c) (W := W) (by linarith) hW (σ := 0) le_rfl one_pos hξ0
  have hint : (∫ τ : ℝ, mellinK0 c (((0 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) ξ * W (((0 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)) =
      ∫ τ : ℝ, outerK c τ * stripEdge0 W τ * Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ)) := by
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only [Complex.ofReal_zero, zero_add]
    rw [mellinK0_imag_outer c ξ τ hξ0, hlog]
    unfold stripEdge0
    ring
  rw [hint] at hv
  have hnorm : |hankelRho0 c (c * ξ) * admissLift c W (c * ξ)| =
      1 / (2 * Real.pi * ξ) * ‖∫ τ : ℝ, outerK c τ * stripEdge0 W τ * Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ))‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  rw [hnorm]
  have hT := tauStar_rpow_le (α := α) hL hα1.le
  have hlam := rpow_div_lam (α := α) hc0 hL0
  have hL1α : 0 ≤ L ^ (-(1 + α)) := by positivity
  have hb : K * (tauStar L ^ (-(1 / 2 : ℝ)) + L ^ (-(1 + α)) + L ^ (1 - α) / (c * L / 2) ^ 2) ≤
      K * (M1 + 1 + 4 / c ^ 2) * L ^ (-(1 + α)) := by
    rw [hlam]
    have : tauStar L ^ (-(1 / 2 : ℝ)) + L ^ (-(1 + α)) + 4 / c ^ 2 * L ^ (-(1 + α)) ≤
        (M1 + 1 + 4 / c ^ 2) * L ^ (-(1 + α)) := by nlinarith
    calc K * (tauStar L ^ (-(1 / 2 : ℝ)) + L ^ (-(1 + α)) + 4 / c ^ 2 * L ^ (-(1 + α)))
        ≤ K * ((M1 + 1 + 4 / c ^ 2) * L ^ (-(1 + α))) := mul_le_mul_of_nonneg_left this hK0
      _ = _ := by ring
  have hpos : 0 ≤ 1 / (2 * Real.pi * ξ) := by positivity
  calc 1 / (2 * Real.pi * ξ) * ‖∫ τ : ℝ, outerK c τ * stripEdge0 W τ * Complex.exp (Complex.I * ((c * edgePhi L τ : ℝ) : ℂ))‖
      ≤ 1 / (2 * Real.pi * ξ) * (K * (M1 + 1 + 4 / c ^ 2) * L ^ (-(1 + α))) :=
        mul_le_mul_of_nonneg_left (hos.trans hb) hpos
    _ = _ := by
        field_simp

end FormalResearch.SignUncertainty
