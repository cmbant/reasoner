module

public import Mathlib

/-!
# Weber-type solutions: the energy identity and the forbidden region

Abstract analysis for a solution `f` of the Weber-type equation `f'' = (x² - L) f` (`L > 0`) with the decay and mass data of an
`L²`-normalised Hermite function (`WeberData`).  With `E = f'² + (L - x²) f²` one has `E' = -2x f²`; hence `E` is nonincreasing
on `[0, ∞)` and, since `E → 0`, `E ≥ 0` there (`WeberData.E_nonneg`).  Consequences on the forbidden region `x ≥ s = √L`:
`f²` is nonincreasing (`WeberData.sq_antitone`) and decays like `exp(-(4/3) √(2s) (x - s)^{3/2})`
(`WeberData.sq_exp_decay`).

Used by `HermiteKappaEnvelope` (W1 `lem:PR(b)`), where `WeberData` is instantiated by `φ_n` with `L = 2n + 1`
(`HermiteKappaOde`).  **Claim class: proved.**
-/

@[expose] public section

open Real Filter Topology

namespace FormalResearch.Special

/-- The data of an `L²`-normalised solution of `f'' = (x² - L) f` decaying at `+∞`: `g = f'`, and a mass function `V`
(`V' = f²`, `V(0) = 0`, `V ≤ 1` on `[0, ∞)`). -/
structure WeberData (L : ℝ) (f g V : ℝ → ℝ) : Prop where
  hf : ∀ x, HasDerivAt f (g x) x
  hg : ∀ x, HasDerivAt g ((x ^ 2 - L) * f x) x
  tf : Tendsto f atTop (𝓝 0)
  tg : Tendsto g atTop (𝓝 0)
  tE : Tendsto (fun x => x ^ 2 * f x ^ 2) atTop (𝓝 0)
  hV : ∀ x, HasDerivAt V (f x ^ 2) x
  V0 : V 0 = 0
  Vle : ∀ x, 0 ≤ x → V x ≤ 1

namespace WeberData

variable {L : ℝ} {f g V : ℝ → ℝ}

/-- The energy `E = f'² + (L - x²) f²`. -/
def E (L : ℝ) (f g : ℝ → ℝ) (x : ℝ) : ℝ := g x ^ 2 + (L - x ^ 2) * f x ^ 2

lemma hasDerivAt_E (h : WeberData L f g V) (x : ℝ) :
    HasDerivAt (E L f g) (-2 * x * f x ^ 2) x := by
  have h3 := (h.hg x).mul (h.hg x)
  have h2 := (h.hf x).mul (h.hf x)
  have hxx : HasDerivAt (fun y : ℝ => L - y * y) (-(x + x)) x := by
    have := ((hasDerivAt_id x).mul (hasDerivAt_id x)).const_sub L
    simpa using this
  have h4 := hxx.mul h2
  have h5 := h3.add h4
  have hfun : E L f g = fun y => g y * g y + (L - y * y) * (f y * f y) := by
    funext y; simp only [E]; ring
  rw [hfun]
  refine h5.congr_deriv ?_
  simp only [Pi.mul_apply]
  ring

lemma E_antitoneOn (h : WeberData L f g V) : AntitoneOn (E L f g) (Set.Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
  · exact fun x _ => (h.hasDerivAt_E x).continuousAt.continuousWithinAt
  · exact fun x _ => (h.hasDerivAt_E x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(h.hasDerivAt_E x).deriv]
    have : (0 : ℝ) < x := hx
    nlinarith [sq_nonneg (f x)]

lemma tendsto_E (h : WeberData L f g V) : Tendsto (E L f g) atTop (𝓝 0) := by
  have h1 := h.tg.pow 2
  have h2 := (h.tf.pow 2).const_mul L
  have h3 := h.tE
  have := (h1.add h2).sub h3
  simp only [zero_pow two_ne_zero, mul_zero, add_zero, sub_zero] at this
  refine this.congr (fun x => ?_)
  simp only [E]; ring

lemma E_nonneg (h : WeberData L f g V) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ E L f g x := by
  refine le_of_tendsto h.tendsto_E ?_
  filter_upwards [eventually_ge_atTop x] with y hy
  exact h.E_antitoneOn hx (hx.trans hy) hy

/-- `(f f')' = f'² + (x² - L) f²`. -/
lemma hasDerivAt_ffg (h : WeberData L f g V) (x : ℝ) :
    HasDerivAt (fun y => f y * g y) (g x ^ 2 + (x ^ 2 - L) * f x ^ 2) x := by
  have := (h.hf x).mul (h.hg x)
  refine this.congr_deriv ?_
  ring

/-- On the forbidden region `x ≥ s` (`s ≥ 0`, `s² = L`) `f f' ≤ 0`. -/
lemma ffg_nonpos (h : WeberData L f g V) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ^ 2 = L) {x : ℝ} (hx : s ≤ x) :
    f x * g x ≤ 0 := by
  have hmono : MonotoneOn (fun y => f y * g y) (Set.Ici s) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici s) ?_ ?_ ?_
    · exact fun x _ => (h.hasDerivAt_ffg x).continuousAt.continuousWithinAt
    · exact fun x _ => (h.hasDerivAt_ffg x).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(h.hasDerivAt_ffg y).deriv]
      have hy' : s < y := hy
      have : L ≤ y ^ 2 := by nlinarith
      nlinarith [sq_nonneg (g y), sq_nonneg (f y)]
  have hlim : Tendsto (fun y => f y * g y) atTop (𝓝 0) := by
    simpa using h.tf.mul h.tg
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop x] with y hy
  exact hmono hx (hx.trans hy) hy

lemma hasDerivAt_sq (h : WeberData L f g V) (x : ℝ) :
    HasDerivAt (fun y => f y ^ 2) (2 * f x * g x) x := by
  have := (h.hf x).mul (h.hf x)
  have e : (fun y => f y ^ 2) = f * f := by funext y; simp [sq]
  rw [e]
  refine this.congr_deriv ?_
  ring

/-- `f²` is nonincreasing on the forbidden region `x ≥ s`. -/
lemma sq_antitone (h : WeberData L f g V) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ^ 2 = L) :
    AntitoneOn (fun y => f y ^ 2) (Set.Ici s) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici s) ?_ ?_ ?_
  · exact fun x _ => (h.hasDerivAt_sq x).continuousAt.continuousWithinAt
  · exact fun x _ => (h.hasDerivAt_sq x).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    have hy' : s < y := hy
    rw [(h.hasDerivAt_sq y).deriv]
    have := h.ffg_nonpos hs0 hs hy'.le
    nlinarith

/-- On the forbidden region `g² ≥ (x² - L) f²` (from `E ≥ 0`). -/
lemma g_sq_ge (h : WeberData L f g V) {x : ℝ} (hx : 0 ≤ x) :
    (x ^ 2 - L) * f x ^ 2 ≤ g x ^ 2 := by
  have := h.E_nonneg hx
  simp only [E] at this
  nlinarith

/-- **Exponential decay on the forbidden region**:
`f(x)² exp((4/3) √(2s) (√(x-s))³) ≤ f(s)²` for `x ≥ s`, `s² = L`. -/
lemma sq_exp_decay (h : WeberData L f g V) {s : ℝ} (hs0 : 0 < s) (hs : s ^ 2 = L) {x : ℝ} (hx : s ≤ x) :
    f x ^ 2 * Real.exp ((4 / 3) * √(2 * s) * (√(x - s)) ^ 3) ≤ f s ^ 2 := by
  set c : ℝ := (4 / 3) * √(2 * s) with hc
  set H : ℝ → ℝ := fun y => f y ^ 2 * Real.exp (c * (√(y - s)) ^ 3) with hH
  have hanti : AntitoneOn H (Set.Ici s) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici s) ?_ ?_ ?_
    · intro y _
      have hc1 : ContinuousAt (fun y => f y ^ 2) y := (h.hasDerivAt_sq y).continuousAt
      have hc2 : Continuous (fun y : ℝ => Real.exp (c * (√(y - s)) ^ 3)) := by fun_prop
      exact (hc1.mul hc2.continuousAt).continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy' : s < y := hy
      have hpos : 0 < y - s := sub_pos.2 hy'
      have hsq : HasDerivAt (fun y => √(y - s)) (1 / (2 * √(y - s))) y := by
        have := ((hasDerivAt_id y).sub_const s).sqrt hpos.ne'
        simpa using this
      have hcube := ((hsq.pow 3).const_mul c).exp
      exact (((h.hasDerivAt_sq y).mul hcube).differentiableAt).differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy' : s < y := hy
      have hpos : 0 < y - s := sub_pos.2 hy'
      have hrpos : 0 < √(y - s) := Real.sqrt_pos.2 hpos
      have hsq : HasDerivAt (fun y => √(y - s)) (1 / (2 * √(y - s))) y := by
        have := ((hasDerivAt_id y).sub_const s).sqrt hpos.ne'
        simpa using this
      have hcube := ((hsq.pow 3).const_mul c).exp
      have hd := (h.hasDerivAt_sq y).mul hcube
      have hHd : HasDerivAt H _ y := hd
      rw [hHd.deriv]
      have hfg := h.ffg_nonpos hs0.le hs hy'.le
      have hge := h.g_sq_ge (hs0.le.trans hy'.le)
      set κ : ℝ := √(2 * s) with hκ
      set r : ℝ := √(y - s) with hr
      have hκ2 : κ ^ 2 = 2 * s := Real.sq_sqrt (by linarith)
      have hr2 : r ^ 2 = y - s := Real.sq_sqrt hpos.le
      have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
      have h1 : (κ * r * f y) ^ 2 ≤ g y ^ 2 := by
        have : (κ * r * f y) ^ 2 = (2 * s) * (y - s) * f y ^ 2 := by
          rw [mul_pow, mul_pow, hκ2, hr2]
        rw [this]
        have h3 : 2 * s * (y - s) ≤ y ^ 2 - L := by nlinarith
        nlinarith [sq_nonneg (f y)]
      have h2 : |κ * r * f y| ≤ |g y| := sq_le_sq.1 h1
      have h3 : κ * r * f y ^ 2 ≤ -(f y * g y) := by
        have e1 : |κ * r * f y| = κ * r * |f y| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hκ0, abs_of_nonneg hrpos.le]
        rw [e1] at h2
        have e2 : f y * g y = -(|f y| * |g y|) := by
          rw [← abs_mul, abs_of_nonpos hfg]; ring
        rw [e2]
        have := mul_le_mul_of_nonneg_left h2 (abs_nonneg (f y))
        have e3 : f y ^ 2 = |f y| * |f y| := by rw [← sq, sq_abs]
        nlinarith [e3]
      have hpow : ((fun y => √(y - s)) ^ 3) y = r ^ 3 := by simp [hr]
      rw [hpow]
      have hexp := Real.exp_pos (c * r ^ 3)
      have hc' : c * (((3 : ℕ) : ℝ) * r ^ (3 - 1) * (1 / (2 * r))) = 2 * κ * r := by
        rw [hc]; field_simp; ring
      have e4 : 2 * f y * g y * rexp (c * r ^ 3) +
          f y ^ 2 * (rexp (c * r ^ 3) * (c * (((3 : ℕ) : ℝ) * r ^ (3 - 1) * (1 / (2 * r))))) =
          2 * rexp (c * r ^ 3) * (f y * g y + κ * r * f y ^ 2) := by
        rw [hc']; ring
      rw [e4]
      have : f y * g y + κ * r * f y ^ 2 ≤ 0 := by linarith
      nlinarith
  have := hanti (le_refl s |> fun _ => Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simp only [hH, sub_self, Real.sqrt_zero] at this
  simpa using this

end WeberData

end FormalResearch.Special
