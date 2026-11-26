module

public import FormalResearch.SignUncertainty.CtOuterBdryDeriv

/-!
# The conjugate-function functional `F_b` for amplitudes with bounded derivative (phase-free)

`F_b(τ) = ∫ (b(τ+s) - b(τ)) / sinh(πs) ds` (`bdryF`, Paper I) is the boundary value of the imaginary part of the
strip Schwarz integral.  Paper I proves `F_b' = F_{b'}` for *bounded* `b` (`hasDerivAt_bdryF`) and a decay bound for
`b, b' = O((1+|t|) e^{-π|t|})`.  The amplitudes of Paper II (`aAmp`) grow linearly, so this file proves the versions
that need only a bounded derivative, and the decay of `F_g` for `g` bounded with `g' = O(e^{-π|t|/2})`.

* `hasDerivAt_bdryF_lin`: `b' ` bounded and `b''` bounded give `F_b' = F_{b'}` (no bound on `b`);
* `abs_bdryF_le_lin`: `|F_g(τ)| ≤ C B` if `|g'| ≤ B`;
* `abs_bdryF_decay_half`: `|g'(t)| ≤ A e^{-π|t|/2}`, `|g| ≤ B` give `|F_g(τ)| ≤ C (A + B) e^{-πτ/2}` for `τ ≥ 0`,
  with an absolute `C`.

All proved unconditionally.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.StripBdry

/-- Majorant `(B/π) 1_{[-1,1]} + 4 B |s| e^{-π|s|}`. -/
noncomputable def majL (B s : ℝ) : ℝ :=
  B / π * (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) s + 4 * B * (|s| * Real.exp (-π * |s|))

lemma integrable_majL (B : ℝ) : Integrable (majL B) := by
  have h1 : Integrable fun s : ℝ => B / π * (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) s :=
    (((integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))).const_mul _)
  exact h1.add ((integrable_abs_exp Real.pi_pos).const_mul _)

lemma majL_eq (B s : ℝ) : majL B s = B * majL 1 s := by unfold majL; ring

lemma majL_nonneg {B : ℝ} (hB : 0 ≤ B) (s : ℝ) : 0 ≤ majL B s := by
  unfold majL
  have : 0 ≤ (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) s := indicator_nonneg (fun _ _ => zero_le_one) s
  have := Real.pi_pos
  positivity

/-- Pointwise bound of the integrand of `F_h` for `|h'| ≤ B`. -/
lemma shift_integrand_le_lin {h h' : ℝ → ℝ} (hd : ∀ t, HasDerivAt h (h' t) t) {B : ℝ}
    (hB : ∀ t, |h' t| ≤ B) (τ s : ℝ) : |(h (τ + s) - h τ) / Real.sinh (π * s)| ≤ majL B s := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hmaj0 : 0 ≤ 4 * B * (|s| * Real.exp (-π * |s|)) := by positivity
  rw [abs_div]
  by_cases hs : |s| ≤ 1
  · have hmem : s ∈ Icc (-1 : ℝ) 1 := abs_le.mp hs
    unfold majL
    rw [indicator_of_mem hmem]
    by_cases h0 : s = 0
    · subst h0; simp; positivity
    have := abs_shift_sub_le hd hB τ s
    have h2 := abs_div_sinh_le_near h0
    have hpos : 0 < |Real.sinh (π * s)| := by
      rw [abs_sinh_pi]; exact Real.sinh_pos_iff.mpr (by have := abs_pos.mpr h0; positivity)
    calc |h (τ + s) - h τ| / |Real.sinh (π * s)| ≤ (B * |s|) / |Real.sinh (π * s)| :=
          div_le_div_of_nonneg_right this hpos.le
      _ = B * (|s| / |Real.sinh (π * s)|) := by ring
      _ ≤ B * (1 / π) := mul_le_mul_of_nonneg_left h2 hB0
      _ ≤ B / π * 1 + 4 * B * (|s| * Real.exp (-π * |s|)) := by
          linarith [show B * (1 / π) = B / π * 1 by ring]
  · have hfar := abs_inv_sinh_le_far (not_le.mp hs).le
    have hmem : s ∉ Icc (-1 : ℝ) 1 := fun h => hs (abs_le.mpr ⟨h.1, h.2⟩)
    unfold majL
    rw [indicator_of_notMem hmem, mul_zero, zero_add]
    have hnum := abs_shift_sub_le hd hB τ s
    calc |h (τ + s) - h τ| / |Real.sinh (π * s)| = |h (τ + s) - h τ| * (1 / |Real.sinh (π * s)|) := by ring
      _ ≤ (B * |s|) * (4 * Real.exp (-π * |s|)) := mul_le_mul hnum hfar (by positivity) (by positivity)
      _ = 4 * B * (|s| * Real.exp (-π * |s|)) := by ring

/-- **`d/dτ F_b = F_{b'}`** for `b'`, `b''` bounded (no bound on `b` itself). -/
theorem hasDerivAt_bdryF_lin {b b' b'' : ℝ → ℝ} (hb : ∀ t, HasDerivAt b (b' t) t)
    (hb' : ∀ t, HasDerivAt b' (b'' t) t) {B1 B2 : ℝ} (h1 : ∀ t, |b' t| ≤ B1)
    (h2 : ∀ t, |b'' t| ≤ B2) (τ : ℝ) : HasDerivAt (bdryF b) (bdryF b' τ) τ := by
  have hfun : bdryF b = fun x : ℝ => ∫ s : ℝ, (b (x + s) - b x) / Real.sinh (π * s) :=
    funext (bdryF_eq_shift b)
  rw [hfun, bdryF_eq_shift b']
  have hsm : ∀ x : ℝ, Measurable fun s : ℝ => (b (x + s) - b x) / Real.sinh (π * s) := by
    intro x
    have hc : Continuous b := continuous_iff_continuousAt.2 fun t => (hb t).continuousAt
    exact ((hc.comp (continuous_const.add continuous_id)).measurable.sub measurable_const).div (by fun_prop)
  have hsm' : ∀ x : ℝ, Measurable fun s : ℝ => (b' (x + s) - b' x) / Real.sinh (π * s) := by
    intro x
    have hc : Continuous b' := continuous_iff_continuousAt.2 fun t => (hb' t).continuousAt
    exact ((hc.comp (continuous_const.add continuous_id)).measurable.sub measurable_const).div (by fun_prop)
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (s := univ) (x₀ := τ)
    (F := fun x s => (b (x + s) - b x) / Real.sinh (π * s))
    (F' := fun x s => (b' (x + s) - b' x) / Real.sinh (π * s))
    (bound := majL B2) Filter.univ_mem
    (Eventually.of_forall fun x => (hsm x).aestronglyMeasurable)
    (by
      refine Integrable.mono' (integrable_majL B1) (hsm τ).aestronglyMeasurable
        (Eventually.of_forall fun s => ?_)
      rw [Real.norm_eq_abs]; exact shift_integrand_le_lin hb h1 τ s)
    (hsm' τ).aestronglyMeasurable
    (Eventually.of_forall fun s x _ => by
      rw [Real.norm_eq_abs]; exact shift_integrand_le_lin hb' h2 x s)
    (integrable_majL _)
    (Eventually.of_forall fun s x _ => by
      have h3 : HasDerivAt (fun y : ℝ => b (y + s) - b y) (b' (x + s) - b' x) x := by
        have := ((hb (x + s)).comp x ((hasDerivAt_id x).add_const s)).sub (hb x)
        exact this.congr_deriv (by simp)
      have := h3.div_const (Real.sinh (π * s))
      simpa [add_comm] using this)
  exact this.2

/-- The absolute constant `∫ majL 1`. -/
noncomputable def cL : ℝ := ∫ s : ℝ, majL 1 s

lemma cL_nonneg : 0 ≤ cL := integral_nonneg (fun s => majL_nonneg zero_le_one s)

/-- `|F_g(τ)| ≤ cL B` if `|g'| ≤ B`. -/
theorem abs_bdryF_le_lin {g g' : ℝ → ℝ} (hd : ∀ t, HasDerivAt g (g' t) t) {B : ℝ}
    (hB : ∀ t, |g' t| ≤ B) (τ : ℝ) : |bdryF g τ| ≤ cL * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  rw [bdryF_eq_shift]
  have hmeas : Measurable fun s : ℝ => (g (τ + s) - g τ) / Real.sinh (π * s) := by
    have hc : Continuous g := continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
    exact ((hc.comp (continuous_const.add continuous_id)).measurable.sub measurable_const).div (by fun_prop)
  have := norm_integral_le_of_norm_le (integrable_majL B) (Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs]; exact shift_integrand_le_lin hd hB τ s) (f := fun s : ℝ => (g (τ + s) - g τ) / Real.sinh (π * s))
  rw [Real.norm_eq_abs] at this
  refine this.trans ?_
  have e : ∫ s, majL B s = B * cL := by
    unfold cL; rw [← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall fun s => majL_eq B s)
  rw [e]; ring_nf; exact le_rfl

/-- Majorant for the near part of the decay estimate: `(e^{π/2}/π) 1_{[-1,1]} + 4 |s| e^{-π|s|/2}`. -/
noncomputable def majD (s : ℝ) : ℝ :=
  Real.exp (π / 2) / π * (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) s + 4 * (|s| * Real.exp (-(π / 2) * |s|))

lemma integrable_majD : Integrable majD := by
  have h1 : Integrable fun s : ℝ => Real.exp (π / 2) / π * (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) s :=
    (((integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))).const_mul _)
  exact h1.add ((integrable_abs_exp (by positivity : (0 : ℝ) < π / 2)).const_mul _)

lemma majD_nonneg (s : ℝ) : 0 ≤ majD s := by
  unfold majD
  have : 0 ≤ (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) s := indicator_nonneg (fun _ _ => zero_le_one) s
  have := Real.pi_pos
  positivity

/-- `|s| e^{π|s|/2} / |sinh(πs)| ≤ majD s`. -/
lemma phi_le_majD (s : ℝ) : |s| * Real.exp ((π / 2) * |s|) / |Real.sinh (π * s)| ≤ majD s := by
  by_cases hs : |s| ≤ 1
  · have hmem : s ∈ Icc (-1 : ℝ) 1 := abs_le.mp hs
    unfold majD
    rw [indicator_of_mem hmem]
    by_cases h0 : s = 0
    · subst h0; simp; positivity
    have h2 := abs_div_sinh_le_near h0
    have he : Real.exp ((π / 2) * |s|) ≤ Real.exp (π / 2) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have hpos : 0 < |Real.sinh (π * s)| := by
      rw [abs_sinh_pi]; exact Real.sinh_pos_iff.mpr (by have := abs_pos.mpr h0; positivity)
    calc |s| * Real.exp ((π / 2) * |s|) / |Real.sinh (π * s)|
        = (|s| / |Real.sinh (π * s)|) * Real.exp ((π / 2) * |s|) := by ring
      _ ≤ (1 / π) * Real.exp (π / 2) := mul_le_mul h2 he (by positivity) (by positivity)
      _ ≤ Real.exp (π / 2) / π * 1 + 4 * (|s| * Real.exp (-(π / 2) * |s|)) := by
          have : 0 ≤ 4 * (|s| * Real.exp (-(π / 2) * |s|)) := by positivity
          have e : 1 / π * Real.exp (π / 2) = Real.exp (π / 2) / π * 1 := by ring
          linarith
  · have hfar := abs_inv_sinh_le_far (not_le.mp hs).le
    have hmem : s ∉ Icc (-1 : ℝ) 1 := fun h => hs (abs_le.mpr ⟨h.1, h.2⟩)
    unfold majD
    rw [indicator_of_notMem hmem, mul_zero, zero_add]
    calc |s| * Real.exp ((π / 2) * |s|) / |Real.sinh (π * s)|
        = (|s| * Real.exp ((π / 2) * |s|)) * (1 / |Real.sinh (π * s)|) := by ring
      _ ≤ (|s| * Real.exp ((π / 2) * |s|)) * (4 * Real.exp (-π * |s|)) :=
          mul_le_mul_of_nonneg_left hfar (by positivity)
      _ = 4 * (|s| * Real.exp (-(π / 2) * |s|)) := by
          have : Real.exp ((π / 2) * |s|) * Real.exp (-π * |s|) = Real.exp (-(π / 2) * |s|) := by
            rw [← Real.exp_add]; ring_nf
          calc (|s| * Real.exp ((π / 2) * |s|)) * (4 * Real.exp (-π * |s|))
              = 4 * (|s| * (Real.exp ((π / 2) * |s|) * Real.exp (-π * |s|))) := by ring
            _ = _ := by rw [this]

/-- The decay constant. -/
noncomputable def cD : ℝ := ∫ s : ℝ, majD s

/-- **Decay of `F_g`**: `|g'(t)| ≤ A e^{-π|t|/2}` and `|g| ≤ B` give `|F_g(τ)| ≤ C (A + B) e^{-πτ/2}`, `τ ≥ 0`,
with `C` absolute. -/
theorem abs_bdryF_decay_half : ∃ C : ℝ, 0 < C ∧ ∀ {g g' : ℝ → ℝ} {A B : ℝ}, (∀ t, HasDerivAt g (g' t) t) →
    (∀ t, |g' t| ≤ A * Real.exp (-(π / 2) * |t|)) → (∀ t, |g t| ≤ B) → ∀ τ : ℝ, 0 ≤ τ →
    |bdryF g τ| ≤ C * (A + B) * Real.exp (-(π / 2) * τ) := by
  have hcD : 0 ≤ cD := integral_nonneg majD_nonneg
  have hI00 : 0 ≤ ∫ s : ℝ, Real.exp (-(π / 2) * |s|) := integral_nonneg (fun s => by positivity)
  refine ⟨cL * Real.exp (π / 2) + cD + 8 * (∫ s : ℝ, Real.exp (-(π / 2) * |s|)) + 1,
    by have := mul_nonneg cL_nonneg (Real.exp_pos (π / 2)).le; linarith, ?_⟩
  intro g g' A B hd hg' hg τ hτ
  have hA0 : 0 ≤ A := by
    have := (abs_nonneg (g' 0)).trans (hg' 0)
    simpa using this
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hg 0)
  have hcL := cL_nonneg
  have hI0 : 0 ≤ ∫ s : ℝ, Real.exp (-(π / 2) * |s|) := integral_nonneg (fun s => by positivity)
  have hint1 : (0 : ℝ) ≤ Real.exp (-(π / 2) * τ) := (Real.exp_pos _).le
  by_cases hτ1 : τ < 1
  · -- near the tip: global bound
    have h := abs_bdryF_le_lin hd (B := A) (fun t => (hg' t).trans (by
      have : Real.exp (-(π / 2) * |t|) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg t, Real.pi_pos])
      nlinarith)) τ
    have he : Real.exp (π / 2) * Real.exp (-(π / 2) * τ) ≥ 1 := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith [Real.pi_pos])
    have : cL * A ≤ cL * Real.exp (π / 2) * (A * Real.exp (-(π / 2) * τ)) := by
      calc cL * A ≤ cL * (A * (Real.exp (π / 2) * Real.exp (-(π / 2) * τ))) :=
            mul_le_mul_of_nonneg_left (by nlinarith) hcL
        _ = _ := by ring
    have hmono : cL * Real.exp (π / 2) * (A * Real.exp (-(π / 2) * τ)) ≤
        (cL * Real.exp (π / 2) + cD + 8 * (∫ s : ℝ, Real.exp (-(π / 2) * |s|)) + 1) * (A + B) *
          Real.exp (-(π / 2) * τ) := by
      have hp : 0 ≤ Real.exp (-(π / 2) * τ) := hint1
      have : 0 ≤ (cD + 8 * (∫ s : ℝ, Real.exp (-(π / 2) * |s|)) + 1) * (A + B) * Real.exp (-(π / 2) * τ) := by positivity
      nlinarith [mul_nonneg hB0 (mul_nonneg hcL (Real.exp_pos (π / 2)).le), mul_nonneg hB0 hp,
        mul_nonneg (mul_nonneg hB0 hcL) (mul_nonneg (Real.exp_pos (π / 2)).le hp)]
    linarith
  · push Not at hτ1
    rw [bdryF_eq_shift]
    set M : ℝ → ℝ := fun s => A * Real.exp (-(π / 2) * τ) * majD s + 8 * B * Real.exp (-(π / 2) * τ) *
      Real.exp (-(π / 2) * |s|) with hM
    have hMint : Integrable M := by
      refine (integrable_majD.const_mul _).add ((integrable_exp_neg_abs' (by positivity : (0 : ℝ) < π / 2)).const_mul _)
    have hmeas : Measurable fun s : ℝ => (g (τ + s) - g τ) / Real.sinh (π * s) := by
      have hc : Continuous g := continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
      exact ((hc.comp (continuous_const.add continuous_id)).measurable.sub measurable_const).div (by fun_prop)
    have hpt : ∀ s : ℝ, |(g (τ + s) - g τ) / Real.sinh (π * s)| ≤ M s := by
      intro s
      rw [abs_div]
      by_cases hs : |s| ≤ τ
      · -- near part
        have hdiff : |g (τ + s) - g τ| ≤ (A * Real.exp (-(π / 2) * τ) * Real.exp ((π / 2) * |s|)) * |s| := by
          have hd' : ∀ x : ℝ, HasDerivAt (fun x : ℝ => g (τ + x)) (g' (τ + x)) x := fun x =>
            ((hd (τ + x)).comp x ((hasDerivAt_id x).const_add τ)).congr_deriv (by simp)
          have := abs_sub_le_of_deriv hd' (r := |s|)
            (K := A * Real.exp (-(π / 2) * τ) * Real.exp ((π / 2) * |s|))
            (x := s) (fun y hy => by
              have hy' : |y| ≤ |s| := abs_le.mpr ⟨hy.1, hy.2⟩
              refine (hg' (τ + y)).trans ?_
              have hτy : τ - |s| ≤ |τ + y| := by
                have : |y| ≤ |s| := hy'
                have h1 : τ - |y| ≤ τ + y := by linarith [neg_abs_le y]
                have h2 : τ + y ≤ |τ + y| := le_abs_self _
                linarith
              calc A * Real.exp (-(π / 2) * |τ + y|) ≤ A * Real.exp (-(π / 2) * (τ - |s|)) :=
                    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])) hA0
                _ = A * Real.exp (-(π / 2) * τ) * Real.exp ((π / 2) * |s|) := by
                    rw [mul_assoc, ← Real.exp_add]; ring_nf) le_rfl
          simpa using this
        by_cases h0 : s = 0
        · subst h0; simp; unfold M; have := majD_nonneg 0; positivity
        have hpos : 0 < |Real.sinh (π * s)| := by
          rw [abs_sinh_pi]; exact Real.sinh_pos_iff.mpr (by have := abs_pos.mpr h0; positivity)
        calc |g (τ + s) - g τ| / |Real.sinh (π * s)|
            ≤ ((A * Real.exp (-(π / 2) * τ) * Real.exp ((π / 2) * |s|)) * |s|) / |Real.sinh (π * s)| :=
              div_le_div_of_nonneg_right hdiff hpos.le
          _ = A * Real.exp (-(π / 2) * τ) * (|s| * Real.exp ((π / 2) * |s|) / |Real.sinh (π * s)|) := by ring
          _ ≤ A * Real.exp (-(π / 2) * τ) * majD s :=
              mul_le_mul_of_nonneg_left (phi_le_majD s) (by positivity)
          _ ≤ M s := by
              unfold M; have : 0 ≤ 8 * B * Real.exp (-(π / 2) * τ) * Real.exp (-(π / 2) * |s|) := by positivity
              linarith
      · -- far part
        have hs' : τ < |s| := not_le.mp hs
        have hs1 : 1 ≤ |s| := hτ1.trans hs'.le
        have hfar := abs_inv_sinh_le_far hs1
        have hnum : |g (τ + s) - g τ| ≤ 2 * B := by
          calc _ ≤ |g (τ + s)| + |g τ| := abs_sub _ _
            _ ≤ B + B := add_le_add (hg _) (hg _)
            _ = 2 * B := by ring
        have hexp : Real.exp (-π * |s|) ≤ Real.exp (-(π / 2) * τ) * Real.exp (-(π / 2) * |s|) := by
          rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
        calc |g (τ + s) - g τ| / |Real.sinh (π * s)| = |g (τ + s) - g τ| * (1 / |Real.sinh (π * s)|) := by ring
          _ ≤ (2 * B) * (4 * Real.exp (-π * |s|)) := mul_le_mul hnum hfar (by positivity) (by positivity)
          _ ≤ (2 * B) * (4 * (Real.exp (-(π / 2) * τ) * Real.exp (-(π / 2) * |s|))) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = 8 * B * Real.exp (-(π / 2) * τ) * Real.exp (-(π / 2) * |s|) := by ring
          _ ≤ M s := by
              unfold M; have : 0 ≤ A * Real.exp (-(π / 2) * τ) * majD s := by
                have := majD_nonneg s; positivity
              linarith
    have h := norm_integral_le_of_norm_le hMint (Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]; exact hpt s) (f := fun s : ℝ => (g (τ + s) - g τ) / Real.sinh (π * s))
    rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    have hI : ∫ s, M s = A * Real.exp (-(π / 2) * τ) * cD +
        8 * B * Real.exp (-(π / 2) * τ) * (∫ s : ℝ, Real.exp (-(π / 2) * |s|)) := by
      unfold M cD
      rw [integral_add (integrable_majD.const_mul _)
        ((integrable_exp_neg_abs' (by positivity : (0 : ℝ) < π / 2)).const_mul _), integral_const_mul,
        integral_const_mul]
    rw [hI]
    have hp : 0 ≤ Real.exp (-(π / 2) * τ) := hint1
    set E := Real.exp (-(π / 2) * τ) with hE
    set I0 := ∫ s : ℝ, Real.exp (-(π / 2) * |s|) with hI0'
    have he0 := (Real.exp_pos (π / 2)).le
    have key : (cL * Real.exp (π / 2) + cD + 8 * I0 + 1) * (A + B) * E -
        (A * E * cD + 8 * B * E * I0) =
        E * ((cL * Real.exp (π / 2) + 1) * (A + B) + cD * B + 8 * I0 * A) := by ring
    have : 0 ≤ E * ((cL * Real.exp (π / 2) + 1) * (A + B) + cD * B + 8 * I0 * A) := by positivity
    linarith

end FormalResearch.StripBdry

/-- info: 'FormalResearch.StripBdry.hasDerivAt_bdryF_lin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.StripBdry.hasDerivAt_bdryF_lin

/-- info: 'FormalResearch.StripBdry.abs_bdryF_le_lin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.StripBdry.abs_bdryF_le_lin

/-- info: 'FormalResearch.StripBdry.abs_bdryF_decay_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.StripBdry.abs_bdryF_decay_half
