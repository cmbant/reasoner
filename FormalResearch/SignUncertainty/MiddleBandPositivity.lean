module

public import FormalResearch.SignUncertainty.MiddleBandPosHelpers

/-!
# `O.6`: positivity of `I_main + σ I_dual` at width `δ = K c^{-1/3}`

Source: `CFT/sign_uncertainty/paper/u1c_o1_upper.tex`, Proposition `O.6` (`u1co:O6`).  The proof there fixes the quantifiers in the order
`M₁ → S_w → K_* → c_*(K)` and covers `S_eff ≥ s_min` by three bands: the *high band* `S ≥ max(S_w, M₁ K⁻² c^{2/3})` (`(e4)` and `(e3)`), the *middle band*
`S_w ≤ S ≤ M₁ K⁻² c^{2/3}` (`(e6)`, the floor `(e2)` for the reference and `(e3)`), and the *window* `s_min ≤ S ≤ S_w` (`(e5)` and the floor `(e2)`).

* `O6Est m R g0`: the five analytic estimates the bands use, for the one-level seeds `airySeedU2 a b c₀` with `|a|, |b|, |c₀| ≤ R`: the convolution form of
  `windowSmooth`, `(e4)` with its leading coefficient `(c₀ - a) g0`, `g0 > 0`, `(e3)`, `(e5)` with dual seed `σ X`, and `(e6)`.
* `o6_positivity`: for a seed family `δ ↦ airySeedU2 (fa δ) (fb δ) (fc δ)` with `fc - fa ≥ 1` and the floor `(e2)` for the B-spline smoothing
  (convolution form), there are `K₀, c₀` such that for `K ≥ K₀`, `c ≥ max(c₀, 8K³, (K/δ₁)³)`, `σ = ±1` and every `ξ` with
  `S_eff(ξ) ≥ s_min := (U₀ + U₁ δ + β₁ δ/2)/β₁` (`δ = K c^{-1/3}`), `Re(I_main[X] + σ I_dual[X])(ξ) > 0`.  The threshold constants do not depend on `K`
  except through the displayed conditions.

Status: proved.  Not formalised here: `O6Est` itself (it is assembled from `(e3)`, `(e4)`, `(e5)`, `(e6)` in `MiddleBandE6.lean`, `SeedUniformE3E5.lean`,
`HighBandUniform.lean`, `WindowSmoothConv.lean`), and the identification of `g0` with `c_s^{1/2} 2^{2/3} π^{-1/2}`-type constants.
-/

@[expose] public section

open Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- The analytic estimates behind the three bands of `O.6`, for the one-level seeds with coefficients bounded by `R`. -/
structure O6Est (m : ℕ) (R g0 : ℝ) : Prop where
  g0_pos : 0 < g0
  conv : ∀ {X : ℝ → ℝ}, Continuous X → ∀ {δ₀ : ℝ}, 0 < δ₀ → ∀ x : ℝ,
    windowSmooth δ₀ m X x = ∫ t in Icc (0 : ℝ) δ₀, X (x + t) * bspline m δ₀ t
  e4 : ∃ C > 0, ∀ {a b c₀ K M₁ c ξ : ℝ}, |a| ≤ R → |b| ≤ R → |c₀| ≤ R → 1 ≤ K → 1 ≤ M₁ → 8 * K ^ 3 ≤ c →
    2000 ≤ c → 0 < ξ → 100 ≤ hbS c ξ → M₁ * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ) ≤ hbS c ξ →
    ‖iMain (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ -
        ((((c₀ - a) * g0) * Real.sqrt Real.pi * hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ)‖ ≤
      C * (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) + hbS c ξ ^ (-(1 / 2 : ℝ))) *
        (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ))
  e3 : ∃ C > 0, ∀ {a b c₀ δ₀ c ξ : ℝ}, |a| ≤ R → |b| ≤ R → |c₀| ≤ R → δ₀ ∈ Ioc (0 : ℝ) 2 → 2 ≤ c → 0 < ξ →
    1 ≤ hbS c ξ →
    ‖iDual (airySeedU2 a b c₀) δ₀ m c ξ‖ ≤ C * ξ⁻¹ * (1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) * c⁻¹ *
      min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)))
  e5 : ∀ Sw : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ {a b c₀ σ δ₀ c ξ : ℝ}, |a| ≤ R → |b| ≤ R → |c₀| ≤ R → (σ = 1 ∨ σ = -1) →
    0 ≤ δ₀ → 32768 ≤ c → 0 < ξ → |hbS c ξ| ≤ Sw →
    ‖iMain (airySeedU2 a b c₀) δ₀ m c ξ + (σ : ℂ) * iDual (airySeedU2 a b c₀) δ₀ m c ξ -
        ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) *
          windowSmooth δ₀ m (airySeedU2 a b c₀) (-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs)) : ℝ) : ℂ)‖ ≤
      C * ξ⁻¹ * (liftEps c ^ 2 + ((1 + δ₀ * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ * c ^ (-(1 / 2 : ℝ)))
  e6 : ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b c₀ δ₀ c ξ L : ℝ}, |a| ≤ R → |b| ≤ R → |c₀| ≤ R → δ₀ ∈ Icc (0 : ℝ) 2 → 2 ≤ c →
    0 < ξ → L = Real.log (Real.pi ^ 2 * ξ) → 0 < L → L ≤ 0.002 → 100 ≤ hbS c ξ →
    ‖iMain (airySeedU2 a b c₀) δ₀ m c ξ - ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) : ℝ) : ℂ) *
        ((windowSmooth δ₀ m (airySeedU2 a b c₀)
          (-(edgeKappa0 L * ceBeta1 * hbS c ξ + liftEps c / (2 * ceCs))) : ℝ) : ℂ)‖ ≤
      C * ξ⁻¹ * (hbS c ξ ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * hbS c ξ) + c ^ (-(5 / 2 : ℝ)))

set_option maxHeartbeats 4000000 in
/-- **`O.6`** (`u1co:O6`) for a one-level seed family with the floor `(e2)`; see the module docstring. -/
theorem o6_positivity {m : ℕ} (hm : 3 ≤ m) {R g0 : ℝ} (E : O6Est m R g0)
    {δ₁ c₁ c₂ U0 U1 : ℝ} (hδ₁ : 0 < δ₁) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hU0 : 0 ≤ U0) (hU1 : 0 ≤ U1)
    {fa fb fc : ℝ → ℝ}
    (hbd : ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → |fa δ| ≤ R ∧ |fb δ| ≤ R ∧ |fc δ| ≤ R)
    (hlead : ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → 1 ≤ fc δ - fa δ)
    (hfloor : ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → ∀ x : ℝ, U0 + U1 * δ + ceBeta1 * δ / 2 ≤ x →
      (1 + x) ^ (-(3 / 2 : ℝ)) * (c₁ * δ + c₂ * min 1 ((ceBeta1 * δ / 2) ^ 2 * x)) ≤
        ∫ t in Icc (0 : ℝ) (ceBeta1 * δ / 2),
          airySeedU2 (fa δ) (fb δ) (fc δ) (-x + t) * bspline m (ceBeta1 * δ / 2) t) :
    ∃ K₀ c₀ : ℝ, 1 ≤ K₀ ∧ 2000 ≤ c₀ ∧ ∀ {K c σ ξ : ℝ}, K₀ ≤ K → c₀ ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c →
      (σ = 1 ∨ σ = -1) → 0 < ξ →
      (U0 + U1 * (K * liftEps c) + ceBeta1 * (K * liftEps c) / 2) / ceBeta1 ≤ hbS c ξ →
      0 < (iMain (airySeedU2 (fa (K * liftEps c)) (fb (K * liftEps c)) (fc (K * liftEps c)))
              (ceBeta1 * K * liftEps c / 2) m c ξ +
            (σ : ℂ) * iDual (airySeedU2 (fa (K * liftEps c)) (fb (K * liftEps c)) (fc (K * liftEps c)))
              (ceBeta1 * K * liftEps c / 2) m c ξ).re := by
  obtain ⟨CH, hCH, h4⟩ := E.e4
  obtain ⟨CD, hCD, h3⟩ := E.e3
  obtain ⟨C6, hC6, h6⟩ := E.e6
  have hg0 := E.g0_pos
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hpi := Real.pi_pos
  have hβ := ceBeta1_pos
  have hβ2 := ceBeta1_gt_two
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = g0 * Real.sqrt Real.pi := ⟨_, rfl⟩
  have hGpos : 0 < G := by rw [hGdef]; positivity
  obtain ⟨M₁, hM₁1, hM₁⟩ := exists_rpow_neg_le (p := (m : ℝ) / 2) (by positivity) (ε := G / (8 * CH)) (by positivity)
  obtain ⟨Kh, hKh1, hKh⟩ := exists_rpow_neg_le (p := (m : ℝ)) hm0 (ε := G / (8 * (CH + 2 * Real.pi * CD))) (by positivity)
  obtain ⟨Sh, hSh1, hSh⟩ := exists_rpow_neg_le (p := (1 / 2 : ℝ)) (by norm_num) (ε := G / (8 * CH)) (by positivity)
  obtain ⟨Sw, hSwdef⟩ : ∃ Sw : ℝ, Sw = max (max 100 Sh) ((U0 + U1 + ceBeta1) / ceBeta1) := ⟨_, rfl⟩
  have hSw100 : 100 ≤ Sw := by rw [hSwdef]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hSwSh : Sh ≤ Sw := by rw [hSwdef]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hSwU : (U0 + U1 + ceBeta1) / ceBeta1 ≤ Sw := by rw [hSwdef]; exact le_max_right _ _
  obtain ⟨CW, hCW, h5⟩ := E.e5 Sw
  -- constants of the middle band
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = (2 * ceBeta1 + 2) ^ (-(3 / 2 : ℝ)) := ⟨_, rfl⟩
  have hq : 0 < q := by rw [hqdef]; positivity
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = ceK * ceBeta1 * q / Real.pi ^ 2 := ⟨_, rfl⟩
  have hκ : 0 < κ := by have := ceK_pos; rw [hκdef]; positivity
  obtain ⟨Cm, hCmdef⟩ : ∃ Cm : ℝ, Cm = 2 * C6 + CD := ⟨_, rfl⟩
  have hCm : 0 ≤ Cm := by rw [hCmdef]; positivity
  -- constants of the window
  have hSw0 : 0 < Sw := by linarith
  obtain ⟨qw, hqwdef⟩ : ∃ qw : ℝ, qw = (2 + ceBeta1 * Sw) ^ (-(3 / 2 : ℝ)) := ⟨_, rfl⟩
  have hqw : 0 < qw := by rw [hqwdef]; positivity
  obtain ⟨κw, hκwdef⟩ : ∃ κw : ℝ, κw = ceK * ceBeta1 * qw / Real.pi ^ 2 := ⟨_, rfl⟩
  have hκw : 0 < κw := by have := ceK_pos; rw [hκwdef]; positivity
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = κw * c₁ / (4 * CW) := ⟨_, rfl⟩
  have hθ : 0 < θ := by rw [hθdef]; positivity
  obtain ⟨Mw, hMw1, hMw⟩ := exists_rpow_neg_le (p := (1 / 6 : ℝ)) (by norm_num) (ε := θ) hθ
  refine ⟨max (max Kh M₁) (max (500 * Real.pi ^ 2 * M₁) (2 * Cm * M₁ / (κ * c₂) + 1)),
    max (max 2000 32768) Mw, ?_, ?_, ?_⟩
  · exact hKh1.trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (le_max_left _ _).trans (le_max_left _ _)
  intro K c σ ξ hK hc hc8 hcδ hσ hξ hSmin
  have hKKh : Kh ≤ K := (le_max_left _ _).trans ((le_max_left _ _).trans hK)
  have hKM : M₁ ≤ K := (le_max_right _ _).trans ((le_max_left _ _).trans hK)
  have hK500 : 500 * Real.pi ^ 2 * M₁ ≤ K := (le_max_left _ _).trans ((le_max_right _ _).trans hK)
  have hKbig : 2 * Cm * M₁ / (κ * c₂) + 1 ≤ K := (le_max_right _ _).trans ((le_max_right _ _).trans hK)
  have hK1 : 1 ≤ K := hKh1.trans hKKh
  have hK0 : 0 < K := by linarith only [hK1]
  have hc2000 : 2000 ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hc32768 : 32768 ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hcMw : Mw ≤ c := (le_max_right _ _).trans hc
  have hc0 : 0 < c := by linarith
  have hε : 0 < liftEps c := liftEps_pos hc0
  have hcube : liftEps c ^ 3 * c = 1 := liftEps_cube_mul hc0
  have hKe3 : (K * liftEps c) ^ 3 * c = K ^ 3 := by
    calc (K * liftEps c) ^ 3 * c = K ^ 3 * (liftEps c ^ 3 * c) := by ring
      _ = K ^ 3 := by rw [hcube, mul_one]
  have hKε : K * liftEps c ≤ 1 / 2 := by
    by_contra hcon
    push Not at hcon
    have h2 : (1 / 2 : ℝ) ^ 3 < (K * liftEps c) ^ 3 := pow_lt_pow_left₀ hcon (by norm_num) (by norm_num)
    have h3 := mul_lt_mul_of_pos_right h2 hc0
    rw [hKe3] at h3
    norm_num at h3
    linarith
  have hKεδ : K * liftEps c ≤ δ₁ := by
    have h2 : K ^ 3 ≤ δ₁ ^ 3 * c := by
      have := hcδ
      rw [div_pow, div_le_iff₀ (by positivity)] at this
      linarith
    have h3 : (K * liftEps c) ^ 3 ≤ δ₁ ^ 3 := by
      by_contra hcon
      push Not at hcon
      have := mul_lt_mul_of_pos_right hcon hc0
      rw [hKe3] at this
      linarith
    exact le_of_pow_le_pow_left₀ (by norm_num) hδ₁.le h3
  have hε2 : liftEps c ≤ 1 / 2 := by nlinarith only [hKε, hK1, hε]
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = K * liftEps c := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδ2 : δ ≤ 1 / 2 := by rw [hδdef]; exact hKε
  have hδδ₁ : δ ≤ δ₁ := by rw [hδdef]; exact hKεδ
  rw [← hδdef] at hSmin ⊢
  obtain ⟨hba, hbb, hbc⟩ := hbd δ hδpos hδδ₁
  have hld := hlead δ hδpos hδδ₁
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = fa δ := ⟨_, rfl⟩
  obtain ⟨bb, hbbdef⟩ : ∃ bb : ℝ, bb = fb δ := ⟨_, rfl⟩
  obtain ⟨cc, hccdef⟩ : ∃ cc : ℝ, cc = fc δ := ⟨_, rfl⟩
  rw [← hadef, ← hccdef] at hld
  rw [← hadef, ← hbbdef, ← hccdef]
  rw [← hadef] at hba
  rw [← hbbdef] at hbb
  rw [← hccdef] at hbc
  have hXc : Continuous (airySeedU2 a bb cc) :=
    ((continuous_const.mul continuous_ceF1).add (continuous_const.mul (continuous_ceG1 _))).add
      (continuous_const.mul (continuous_ceG1Deriv _))
  have hδ₀def : ceBeta1 * K * liftEps c / 2 = ceBeta1 * δ / 2 := by rw [hδdef]; ring
  have hδ₀pos : 0 < ceBeta1 * K * liftEps c / 2 := by positivity
  have hδ₀le : ceBeta1 * K * liftEps c / 2 ≤ 2 := by
    rw [hδ₀def]; nlinarith only [ceBeta1_lt_eight, hδ2, hδpos, hβ]
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = hbS c ξ := ⟨_, rfl⟩
  have hSmin' : U0 + U1 * δ + ceBeta1 * δ / 2 ≤ ceBeta1 * S := by
    rw [hSdef]; exact (div_le_iff₀ hβ).mp hSmin |>.trans_eq (by ring)
  have hSpos : 0 < S := by
    have h0 : 0 < U0 + U1 * δ + ceBeta1 * δ / 2 := by positivity
    exact (mul_pos_iff_of_pos_left hβ).mp (lt_of_lt_of_le h0 hSmin')
  have hLeq : Real.log (Real.pi ^ 2 * ξ) = Real.pi ^ 2 * liftEps c ^ 2 * S := by rw [hSdef]; exact log_eq_hbS hc0
  have hLpos : 0 < Real.log (Real.pi ^ 2 * ξ) := by rw [hLeq]; positivity
  have hσn : ‖(σ : ℂ)‖ = 1 := by rcases hσ with rfl | rfl <;> simp
  have hcs := ceCs_one_lt
  have hεcs : liftEps c / (2 * ceCs) ≤ 1 := by
    refine (div_le_self hε.le (by linarith)).trans (by linarith)
  have hKe : 0 < K * liftEps c := by positivity
  by_cases hwin : S ≤ Sw
  · -- window
    have hS5 : |hbS c ξ| ≤ Sw := by rw [← hSdef, abs_of_pos hSpos]; exact hwin
    have e5 := h5 (a := a) (b := bb) (c₀ := cc) (σ := σ) (δ₀ := ceBeta1 * K * liftEps c / 2) (c := c) (ξ := ξ)
      hba hbb hbc hσ hδ₀pos.le hc32768 hξ hS5
    rw [← hSdef] at e5
    obtain ⟨x₀, hx₀def⟩ : ∃ x₀ : ℝ, x₀ = ceBeta1 * S + liftEps c / (2 * ceCs) := ⟨_, rfl⟩
    have harg : -(ceBeta1 * S) - liftEps c / (2 * ceCs) = -x₀ := by rw [hx₀def]; ring
    rw [harg] at e5
    have hconv := E.conv hXc hδ₀pos (-x₀)
    have hx₀ge : U0 + U1 * δ + ceBeta1 * δ / 2 ≤ x₀ := by
      rw [hx₀def]; have : 0 ≤ liftEps c / (2 * ceCs) := by positivity
      linarith
    have hx₀pos : 0 < x₀ := by rw [hx₀def]; positivity
    have hf := hfloor δ hδpos hδδ₁ x₀ hx₀ge
    rw [← hδ₀def] at hf
    rw [← hadef, ← hbbdef, ← hccdef] at hf
    have hFge : qw * (c₁ * δ) ≤ windowSmooth (ceBeta1 * K * liftEps c / 2) m (airySeedU2 a bb cc) (-x₀) := by
      rw [hconv]
      refine le_trans ?_ hf
      have h1 : qw ≤ (1 + x₀) ^ (-(3 / 2 : ℝ)) := by
        rw [hqwdef]
        refine Real.rpow_le_rpow_of_nonpos (by linarith) ?_ (by norm_num)
        have hh := mul_le_mul_of_nonneg_left hwin hβ.le
        rw [hx₀def]; linarith only [hh, hεcs]
      have h2 : 0 ≤ c₂ * min 1 ((ceBeta1 * K * liftEps c / 2) ^ 2 * x₀) :=
        mul_nonneg hc₂.le (le_min zero_le_one (by positivity))
      have h4 : 0 ≤ (1 + x₀) ^ (-(3 / 2 : ℝ)) := by positivity
      calc qw * (c₁ * δ) ≤ (1 + x₀) ^ (-(3 / 2 : ℝ)) * (c₁ * δ) := by gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right h2) h4
    refine re_pos_of_norm_lt (A := ceK * ceBeta1 / (Real.pi ^ 2 * ξ) *
      windowSmooth (ceBeta1 * K * liftEps c / 2) m (airySeedU2 a bb cc) (-x₀)) (lt_of_le_of_lt e5 ?_)
    -- error
    have ht0 : 0 < c ^ (-(1 / 6 : ℝ)) := by positivity
    have ht : c ^ (-(1 / 6 : ℝ)) ≤ θ := hMw c hcMw
    have hεt : liftEps c ≤ c ^ (-(1 / 6 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hc12 : c ^ (-(1 / 2 : ℝ)) = liftEps c * c ^ (-(1 / 6 : ℝ)) := by
      unfold liftEps; rw [← Real.rpow_add hc0]; norm_num
    have hinv : ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ ≤ 1 := by
      refine inv_le_one_of_one_le₀ (one_le_pow₀ ?_)
      have : 0 ≤ ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ) := by positivity
      linarith
    have herr : liftEps c ^ 2 + ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ * c ^ (-(1 / 2 : ℝ)) ≤
        2 * (liftEps c * θ) := by
      rw [hc12]
      have h1 : liftEps c ^ 2 ≤ liftEps c * θ := by
        calc liftEps c ^ 2 = liftEps c * liftEps c := by ring
          _ ≤ liftEps c * θ := by gcongr; exact hεt.trans ht
      have h2 : ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ * (liftEps c * c ^ (-(1 / 6 : ℝ))) ≤
          liftEps c * θ := by
        calc _ ≤ 1 * (liftEps c * c ^ (-(1 / 6 : ℝ))) := by gcongr
          _ ≤ liftEps c * θ := by rw [one_mul]; gcongr
      linarith
    have hξi : 0 < ξ⁻¹ := inv_pos.mpr hξ
    have hlow : ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * (qw * (c₁ * δ)) = ξ⁻¹ * (κw * c₁ * δ) := by
      rw [hκwdef]; field_simp
    have hupper : CW * ξ⁻¹ * (2 * (liftEps c * θ)) = ξ⁻¹ * (κw * c₁ * liftEps c / 2) := by
      rw [hθdef]; field_simp; ring
    have hA : ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * (qw * (c₁ * δ)) ≤ ceK * ceBeta1 / (Real.pi ^ 2 * ξ) *
        windowSmooth (ceBeta1 * K * liftEps c / 2) m (airySeedU2 a bb cc) (-x₀) := by
      gcongr
      exact (by have := ceK_pos; positivity)
    have hεδ : liftEps c ≤ δ := by rw [hδdef]; exact le_mul_of_one_le_left hε.le hK1
    have hkc : 0 < κw * c₁ := by positivity
    calc CW * ξ⁻¹ * (liftEps c ^ 2 + ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ * c ^ (-(1 / 2 : ℝ)))
        ≤ CW * ξ⁻¹ * (2 * (liftEps c * θ)) := by gcongr
      _ = ξ⁻¹ * (κw * c₁ * liftEps c / 2) := hupper
      _ < ξ⁻¹ * (κw * c₁ * δ) := by
          apply mul_lt_mul_of_pos_left _ hξi
          have h2 : liftEps c / 2 < δ := by linarith only [hεδ, hε]
          calc κw * c₁ * liftEps c / 2 = κw * c₁ * (liftEps c / 2) := by ring
            _ < κw * c₁ * δ := mul_lt_mul_of_pos_left h2 hkc
      _ = _ := hlow.symm
      _ ≤ _ := hA
  by_cases hmid : S ≤ M₁ * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ)
  · -- middle
    have hwin' := not_le.mp hwin
    have hS100 : 100 ≤ S := by linarith
    have hS1 : 1 ≤ S := by linarith
    have hc23 : c ^ (2 / 3 : ℝ) = (liftEps c)⁻¹ ^ 2 := by
      rw [← rpow_third_eq hc0, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    have hK2 : 0 < K ^ 2 := by positivity
    have hy : liftEps c ^ 2 * S ≤ M₁ / K ^ 2 := by
      have := mul_le_mul_of_nonneg_left hmid (sq_nonneg (liftEps c))
      calc liftEps c ^ 2 * S ≤ liftEps c ^ 2 * (M₁ * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ)) := this
        _ = M₁ / K ^ 2 := by rw [hc23]; field_simp
    have hy0 : 0 < liftEps c ^ 2 * S := by positivity
    have hKK : K ≤ K ^ 2 := le_self_pow₀ hK1 (by norm_num)
    have hy1 : liftEps c ^ 2 * S ≤ 1 := by
      refine hy.trans ?_
      rw [div_le_one hK2]; linarith
    have hL2 : Real.log (Real.pi ^ 2 * ξ) ≤ 0.002 := by
      rw [hLeq]
      have h1 : Real.pi ^ 2 * (liftEps c ^ 2 * S) ≤ Real.pi ^ 2 * (M₁ / K ^ 2) :=
        mul_le_mul_of_nonneg_left hy (by positivity)
      have h2 : Real.pi ^ 2 * (M₁ / K ^ 2) ≤ 0.002 := by
        rw [← mul_div_assoc, div_le_iff₀ hK2]
        linarith only [hK500, hKK, hK1]
      linarith
    have e6 := h6 (a := a) (b := bb) (c₀ := cc) (δ₀ := ceBeta1 * K * liftEps c / 2) (c := c) (ξ := ξ)
      (L := Real.log (Real.pi ^ 2 * ξ)) hba hbb hbc ⟨hδ₀pos.le, hδ₀le⟩ (by linarith) hξ rfl hLpos hL2
      (by rw [← hSdef]; exact hS100)
    rw [← hSdef] at e6
    obtain ⟨hκ1, hκ2⟩ := edgeKappa0_bounds hLpos hL2
    obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = edgeKappa0 (Real.log (Real.pi ^ 2 * ξ)) * ceBeta1 * S + liftEps c / (2 * ceCs) :=
      ⟨_, rfl⟩
    rw [← hxdef] at e6
    have hxge : ceBeta1 * S ≤ x := by
      rw [hxdef]
      have : 0 ≤ liftEps c / (2 * ceCs) := by positivity
      have hh := mul_le_mul_of_nonneg_right hκ1.le (mul_pos hβ hSpos).le
      linarith only [hh, this]
    have hxup : 1 + x ≤ (2 * ceBeta1 + 2) * S := by
      rw [hxdef]
      have h1 : edgeKappa0 (Real.log (Real.pi ^ 2 * ξ)) ≤ 2 := by linarith
      have h2 : edgeKappa0 (Real.log (Real.pi ^ 2 * ξ)) * ceBeta1 * S ≤ 2 * ceBeta1 * S := by
        have := mul_le_mul_of_nonneg_right h1 (mul_pos hβ hSpos).le
        linarith only [this]
      linarith only [h2, hεcs, hS1]
    have hx0 : 0 < x := by have := mul_pos hβ hSpos; linarith
    have hxfl : U0 + U1 * δ + ceBeta1 * δ / 2 ≤ x := by
      have h1 : U0 + U1 * δ + ceBeta1 * δ / 2 ≤ U0 + U1 + ceBeta1 := by
        have ha := mul_le_mul_of_nonneg_left (by linarith only [hδ2] : δ ≤ 1) hU1
        have hb := mul_le_mul_of_nonneg_left (by linarith only [hδ2] : δ ≤ 1) hβ.le
        linarith only [ha, hb, hβ]
      have h2 : U0 + U1 + ceBeta1 ≤ ceBeta1 * Sw := by
        have := (div_le_iff₀ hβ).mp hSwU; linarith only [this]
      have h3 := mul_le_mul_of_nonneg_left hwin'.le hβ.le
      linarith only [h1, h2, h3, hxge]
    have hconv := E.conv hXc hδ₀pos (-x)
    have hf := hfloor δ hδpos hδδ₁ x hxfl
    rw [← hδ₀def] at hf
    rw [← hadef, ← hbbdef, ← hccdef] at hf
    obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = liftEps c ^ 2 * S := ⟨_, rfl⟩
    rw [← hydef] at hy hy0 hy1
    have hFge : q * S ^ (-(3 / 2 : ℝ)) * (c₂ * min 1 (K ^ 2 * y)) ≤
        windowSmooth (ceBeta1 * K * liftEps c / 2) m (airySeedU2 a bb cc) (-x) := by
      rw [hconv]
      refine le_trans ?_ hf
      have h1 : q * S ^ (-(3 / 2 : ℝ)) ≤ (1 + x) ^ (-(3 / 2 : ℝ)) := by
        have := Real.rpow_le_rpow_of_nonpos (by linarith : (0 : ℝ) < 1 + x) hxup (by norm_num : -(3 / 2 : ℝ) ≤ 0)
        rw [Real.mul_rpow (by positivity) hSpos.le, ← hqdef] at this
        exact this
      have h2 : min 1 (K ^ 2 * y) ≤ min 1 ((ceBeta1 * K * liftEps c / 2) ^ 2 * x) := by
        refine min_le_min le_rfl ?_
        have h3 : (ceBeta1 * K * liftEps c / 2) ^ 2 * (ceBeta1 * S) ≤ (ceBeta1 * K * liftEps c / 2) ^ 2 * x :=
          mul_le_mul_of_nonneg_left hxge (sq_nonneg _)
        have h4 : (ceBeta1 * K * liftEps c / 2) ^ 2 * (ceBeta1 * S) = (ceBeta1 ^ 3 / 4) * (K ^ 2 * y) := by
          rw [hydef]; ring
        have h5' := one_le_ceBeta1_cube_div
        have h6' : 0 ≤ K ^ 2 * y := by positivity
        calc K ^ 2 * y = 1 * (K ^ 2 * y) := by ring
          _ ≤ (ceBeta1 ^ 3 / 4) * (K ^ 2 * y) := mul_le_mul_of_nonneg_right h5' h6'
          _ = _ := h4.symm
          _ ≤ _ := h3
      have h7 : 0 ≤ c₂ * min 1 (K ^ 2 * y) := mul_nonneg hc₂.le (le_min zero_le_one (by positivity))
      have h8 : 0 ≤ (1 + x) ^ (-(3 / 2 : ℝ)) := by positivity
      have h9 : 0 ≤ c₁ * δ := by positivity
      calc q * S ^ (-(3 / 2 : ℝ)) * (c₂ * min 1 (K ^ 2 * y))
          ≤ (1 + x) ^ (-(3 / 2 : ℝ)) * (c₂ * min 1 (K ^ 2 * y)) := by gcongr
        _ ≤ (1 + x) ^ (-(3 / 2 : ℝ)) * (c₂ * min 1 ((ceBeta1 * K * liftEps c / 2) ^ 2 * x)) := by gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left h9) h8
    have hcast : ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) : ℝ) : ℂ) *
        ((windowSmooth (ceBeta1 * K * liftEps c / 2) m (airySeedU2 a bb cc) (-x) : ℝ) : ℂ) =
        ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) *
          windowSmooth (ceBeta1 * K * liftEps c / 2) m (airySeedU2 a bb cc) (-x) : ℝ) : ℂ) := by push_cast; ring
    rw [hcast] at e6
    refine re_pos_of_norm_lt (A := ceK * ceBeta1 / (Real.pi ^ 2 * ξ) *
      windowSmooth (ceBeta1 * K * liftEps c / 2) m (airySeedU2 a bb cc) (-x)) ?_
    refine lt_of_le_of_lt (norm_sub_split _ _ _ _ hσn) ?_
    -- the dual term
    have e3 := h3 (a := a) (b := bb) (c₀ := cc) (δ₀ := ceBeta1 * K * liftEps c / 2) (c := c) (ξ := ξ)
      hba hbb hbc ⟨hδ₀pos, hδ₀le⟩ (by linarith) hξ (by rw [← hSdef]; linarith)
    have hKm : K ^ (-(m : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hK1 (by linarith)
    have hBm : (1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
      have : 0 ≤ ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ) := by positivity
      linarith
    have hlogq : c⁻¹ * (Real.pi ^ 2 * y) ^ (-(1 / 4 : ℝ)) ≤ S ^ (-(3 / 2 : ℝ)) * y := by
      rw [hydef]; exact inv_mul_log_quarter_le hc0 hSpos (by rw [← hydef]; exact hy1)
    have hLy : Real.log (Real.pi ^ 2 * ξ) = Real.pi ^ 2 * y := by rw [hLeq, hydef]; ring
    have hξi : 0 < ξ⁻¹ := inv_pos.mpr hξ
    have hSr : 0 < S ^ (-(3 / 2 : ℝ)) := by positivity
    have hdual : ‖iDual (airySeedU2 a bb cc) (ceBeta1 * K * liftEps c / 2) m c ξ‖ ≤
        CD * (ξ⁻¹ * (S ^ (-(3 / 2 : ℝ)) * y)) := by
      refine e3.trans ?_
      have hmin : min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) ≤
          Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ)) := min_le_left _ _
      have hm0 : 0 ≤ min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) :=
        le_min (by positivity) (by positivity)
      calc CD * ξ⁻¹ * (1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) * c⁻¹ *
            min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)))
          ≤ CD * ξ⁻¹ * 1 * c⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ)) := by
            have hc' : 0 < c⁻¹ := inv_pos.mpr hc0
            gcongr
        _ = CD * (ξ⁻¹ * (c⁻¹ * (Real.pi ^ 2 * y) ^ (-(1 / 4 : ℝ)))) := by rw [hLy]; ring
        _ ≤ CD * (ξ⁻¹ * (S ^ (-(3 / 2 : ℝ)) * y)) := by gcongr
    -- the main-term error
    have hc52 : c ^ (-(5 / 2 : ℝ)) ≤ S ^ (-(3 / 2 : ℝ)) * y := by
      have h1 := c_rpow_mul_S_le (by linarith : 1 ≤ c) hSpos (by rw [← hydef]; exact hy1)
      rw [← hydef] at h1
      have h2 : S ^ (-(3 / 2 : ℝ)) * S ^ (3 / 2 : ℝ) = 1 := by
        rw [← Real.rpow_add hSpos]; norm_num
      calc c ^ (-(5 / 2 : ℝ)) = S ^ (-(3 / 2 : ℝ)) * (c ^ (-(5 / 2 : ℝ)) * S ^ (3 / 2 : ℝ)) := by
            rw [← mul_assoc, mul_comm (S ^ (-(3 / 2 : ℝ))), mul_assoc, h2, mul_one]
        _ ≤ S ^ (-(3 / 2 : ℝ)) * y := by gcongr
    have herr6 : C6 * ξ⁻¹ * (S ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * S) + c ^ (-(5 / 2 : ℝ))) ≤
        2 * C6 * (ξ⁻¹ * (S ^ (-(3 / 2 : ℝ)) * y)) := by
      rw [← hydef]
      have : S ^ (-(3 / 2 : ℝ)) * y + c ^ (-(5 / 2 : ℝ)) ≤ 2 * (S ^ (-(3 / 2 : ℝ)) * y) := by linarith
      calc C6 * ξ⁻¹ * (S ^ (-(3 / 2 : ℝ)) * y + c ^ (-(5 / 2 : ℝ))) ≤ C6 * ξ⁻¹ * (2 * (S ^ (-(3 / 2 : ℝ)) * y)) := by gcongr
        _ = _ := by ring
    -- the main term
    have hmain : ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * (q * S ^ (-(3 / 2 : ℝ)) * (c₂ * min 1 (K ^ 2 * y))) =
        κ * (ξ⁻¹ * (S ^ (-(3 / 2 : ℝ)) * (c₂ * min 1 (K ^ 2 * y)))) := by
      rw [hκdef]; field_simp
    have hbig : 2 * Cm * M₁ < κ * c₂ * K ^ 2 := by
      have h1 : 2 * Cm * M₁ / (κ * c₂) < K := by linarith
      rw [div_lt_iff₀ (by positivity)] at h1
      have h2 := mul_le_mul_of_nonneg_right hKK (mul_pos hκ hc₂).le
      linarith only [h1, h2]
    have hscal := middle_scalar hκ hc₂ hCm hM₁1 hK1 hbig hy0 hy
    have hcore : (2 * C6 + CD) * y < κ * (c₂ * min 1 (K ^ 2 * y)) := by
      rw [← hCmdef]; linarith only [hscal, mul_nonneg hCm hy0.le]
    have hA : ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * (q * S ^ (-(3 / 2 : ℝ)) * (c₂ * min 1 (K ^ 2 * y))) ≤
        ceK * ceBeta1 / (Real.pi ^ 2 * ξ) *
          windowSmooth (ceBeta1 * K * liftEps c / 2) m (airySeedU2 a bb cc) (-x) := by
      gcongr
      exact (by have := ceK_pos; positivity)
    have hSξ : 0 < ξ⁻¹ * S ^ (-(3 / 2 : ℝ)) := by positivity
    calc ‖iMain (airySeedU2 a bb cc) (ceBeta1 * K * liftEps c / 2) m c ξ - ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) *
            windowSmooth (ceBeta1 * K * liftEps c / 2) m (airySeedU2 a bb cc) (-x) : ℝ) : ℂ)‖ +
          ‖iDual (airySeedU2 a bb cc) (ceBeta1 * K * liftEps c / 2) m c ξ‖
        ≤ C6 * ξ⁻¹ * (S ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * S) + c ^ (-(5 / 2 : ℝ))) +
          CD * (ξ⁻¹ * (S ^ (-(3 / 2 : ℝ)) * y)) := add_le_add e6 hdual
      _ ≤ 2 * C6 * (ξ⁻¹ * (S ^ (-(3 / 2 : ℝ)) * y)) + CD * (ξ⁻¹ * (S ^ (-(3 / 2 : ℝ)) * y)) := by linarith
      _ = (ξ⁻¹ * S ^ (-(3 / 2 : ℝ))) * ((2 * C6 + CD) * y) := by ring
      _ < (ξ⁻¹ * S ^ (-(3 / 2 : ℝ))) * (κ * (c₂ * min 1 (K ^ 2 * y))) := mul_lt_mul_of_pos_left hcore hSξ
      _ = ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * (q * S ^ (-(3 / 2 : ℝ)) * (c₂ * min 1 (K ^ 2 * y))) := by
          rw [hmain]; ring
      _ ≤ _ := hA

  · -- high
    have hmid' := not_le.mp hmid
    have hwin' := not_le.mp hwin
    have hS100 : 100 ≤ S := by linarith
    have e4 := h4 (a := a) (b := bb) (c₀ := cc) (K := K) (M₁ := M₁) (c := c) (ξ := ξ) hba hbb hbc hK1 hM₁1 hc8
      (by linarith) hξ (by rw [← hSdef]; exact hS100) (by rw [← hSdef]; exact hmid'.le)
    rw [← hSdef] at e4
    have hA' : hbA c ξ = Real.pi ^ 2 * S := by rw [hSdef]; exact hbA_eq hc0
    obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) := ⟨_, rfl⟩
    have hPpos : 0 < P := by rw [hPdef, hA']; positivity
    have hAeq : ((cc - a) * g0) * Real.sqrt Real.pi * hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) =
        (cc - a) * G * P := by rw [hPdef, hGdef]; ring
    rw [hAeq, ← hPdef] at e4
    refine re_pos_of_norm_lt (A := (cc - a) * G * P) ?_
    refine lt_of_le_of_lt (norm_sub_split _ _ _ _ hσn) ?_
    have e3 := h3 (a := a) (b := bb) (c₀ := cc) (δ₀ := ceBeta1 * K * liftEps c / 2) (c := c) (ξ := ξ)
      hba hbb hbc ⟨hδ₀pos, hδ₀le⟩ (by linarith) hξ (by rw [← hSdef]; linarith)
    have hεc : liftEps c * c ^ (1 / 3 : ℝ) = 1 := by rw [rpow_third_eq hc0]; field_simp
    have hbase : K ≤ 1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ) := by
      have : ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ) = ceBeta1 / 2 * K * (liftEps c * c ^ (1 / 3 : ℝ)) := by ring
      rw [this, hεc]; nlinarith only [hβ2, hK0]
    have hB : (1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) ≤ K ^ (-(m : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hbase (by linarith)
    have hSb : 0 < hbS c ξ := by rw [← hSdef]; exact hSpos
    have hdual : ‖iDual (airySeedU2 a bb cc) (ceBeta1 * K * liftEps c / 2) m c ξ‖ ≤
        2 * Real.pi * CD * K ^ (-(m : ℝ)) * P := by
      refine e3.trans ?_
      have hmin : min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) ≤
          Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := min_le_right _ _
      calc CD * ξ⁻¹ * (1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) * c⁻¹ *
            min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)))
          ≤ CD * ξ⁻¹ * K ^ (-(m : ℝ)) * c⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by
            have hc' : 0 < c⁻¹ := inv_pos.mpr hc0
            gcongr
        _ = CD * K ^ (-(m : ℝ)) * (ξ⁻¹ * (c⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)))) := by ring
        _ = CD * K ^ (-(m : ℝ)) * (ξ⁻¹ * (Real.pi ^ 2 * S) ^ (-(3 / 2 : ℝ))) := by
            rw [inv_mul_log_rpow hc0 hSb, ← hSdef]
        _ = 2 * Real.pi * CD * K ^ (-(m : ℝ)) * P := by
            rw [hPdef, hA']; field_simp
    have hb1 : CH * M₁ ^ (-((m : ℝ) / 2)) ≤ G / 8 := by
      calc CH * M₁ ^ (-((m : ℝ) / 2)) ≤ CH * (G / (8 * CH)) := by gcongr; exact hM₁ M₁ le_rfl
        _ = G / 8 := by field_simp
    have hb2 : (CH + 2 * Real.pi * CD) * K ^ (-(m : ℝ)) ≤ G / 8 := by
      calc (CH + 2 * Real.pi * CD) * K ^ (-(m : ℝ)) ≤ (CH + 2 * Real.pi * CD) * (G / (8 * (CH + 2 * Real.pi * CD))) := by
            gcongr; exact hKh K hKKh
        _ = G / 8 := by field_simp
    have hb3 : CH * S ^ (-(1 / 2 : ℝ)) ≤ G / 8 := by
      calc CH * S ^ (-(1 / 2 : ℝ)) ≤ CH * (G / (8 * CH)) := by gcongr; exact hSh S (hSwSh.trans hwin'.le)
        _ = G / 8 := by field_simp
    have hlead' : G * P ≤ (cc - a) * G * P := by
      have := mul_pos hGpos hPpos
      nlinarith only [this, hld]
    calc ‖iMain (airySeedU2 a bb cc) (ceBeta1 * K * liftEps c / 2) m c ξ - (((cc - a) * G * P : ℝ) : ℂ)‖ +
          ‖iDual (airySeedU2 a bb cc) (ceBeta1 * K * liftEps c / 2) m c ξ‖
        ≤ CH * (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) + S ^ (-(1 / 2 : ℝ))) * P +
          2 * Real.pi * CD * K ^ (-(m : ℝ)) * P := add_le_add e4 hdual
      _ = (CH * M₁ ^ (-((m : ℝ) / 2)) + (CH + 2 * Real.pi * CD) * K ^ (-(m : ℝ)) + CH * S ^ (-(1 / 2 : ℝ))) * P := by ring
      _ ≤ (G / 8 + G / 8 + G / 8) * P := by gcongr
      _ < G * P := by linarith only [mul_pos hGpos hPpos]
      _ ≤ _ := hlead'

/-- info: 'FormalResearch.SignUncertainty.o6_positivity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms o6_positivity

end FormalResearch.SignUncertainty
