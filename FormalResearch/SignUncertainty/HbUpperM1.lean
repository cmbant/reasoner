module

public import FormalResearch.SignUncertainty.MiddleBandPositivity
public import FormalResearch.SignUncertainty.MiddleBandE6
public import FormalResearch.SignUncertainty.Gt1Interface
public import FormalResearch.CohnElkies.HighBandUniform
public import FormalResearch.SignUncertainty.MellinLiftTail
public import FormalResearch.SignUncertainty.Headlines
public import FormalResearch.SignUncertainty.LiftSymbolOriginEdge
public import FormalResearch.SignUncertainty.SeedUniformE3E5
public import FormalResearch.CohnElkies.WindowSmoothConv

/-!
# `O.9'` at `m₀ = 1` (`N = Ai`): the upper half of `thm:hb-thresholds`

Source: `CFT/sign_uncertainty/paper/u1c_o1_upper.tex`, Theorem `O.9'` (`u1co:O9p`) at `(P, Q) = (1, 0)`, `m₀ = 1`, `R_off` irrelevant (no prescribed levels).
The proof there lifts the Hermite--Biehler seed `F_δ` of `lem:hb-seed-mass` (`v = 1`, `r_δ = 0`) at `δ = K c^{-1/3}`; `O.6` (`o6_positivity`) gives
`c^{1/3}(f ρ₀)(cξ) > 0` for `S_eff(ξ) ≥ s_min`, and the origin formula `σ f(0) = -kδ + O(K^{-m} c^{-5/6})` gives the origin sign.

* `O6Bricks m`: the single named hypothesis, `O6Est m R g0` for every coefficient bound `R` (with one `g0 > 0`); it packages the analytic bricks
  `(e3)`, `(e4)` (pinned leading coefficient), `(e5)`, `(e6)` and the convolution form of `windowSmooth` (see `MiddleBandPositivity.lean`).
* `hbThresholdsUpper_of_bricks`: `O6Bricks 4 → HbThresholdsUpper` (`m = 4` is the spline order of the paper's `m ≥ 4`).

Status: proved, conditional on `O6Bricks 4`.  Not formalised here: `O6Bricks 4`.
-/

@[expose] public section

open Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- The single named hypothesis of `O.9'` at `m₀ = 1`: the analytic estimates of `O6Est` for every coefficient bound. -/
def O6Bricks (m : ℕ) : Prop := ∃ g0 : ℝ, 0 < g0 ∧ ∀ R : ℝ, 0 ≤ R → O6Est m R g0

set_option maxHeartbeats 4000000 in
/-- **`O.9'` at `m₀ = 1`** (`N = Ai`): the upper half of `thm:hb-thresholds` for the Bessel-kernel Hankel thresholds, from `O6Bricks 4`. -/
theorem hbThresholdsUpper_of_bricks (h : O6Bricks 4) : HbThresholdsUpper := by
  obtain ⟨g0, hg0, hE⟩ := h
  obtain ⟨δ₁', hδ₁', γ₂, hγ₂, γ₁f, c₁, hc₁, c₂, hc₂, hgain⟩ :=
    hbSeedSpec_airy_smoothing_gain (m := 4) (by norm_num) (V_max := 1) (ε₀ := 0) zero_le_one le_rfl
  obtain ⟨γ₁, hγ₁⟩ : ∃ γ₁ : ℝ, γ₁ = γ₁f 1 := ⟨_, rfl⟩
  obtain ⟨δ₁, hδ₁def⟩ : ∃ δ₁ : ℝ, δ₁ = min δ₁' (1 / 2) := ⟨_, rfl⟩
  have hδ₁ : 0 < δ₁ := by rw [hδ₁def]; exact lt_min hδ₁' (by norm_num)
  have hδ₁2 : δ₁ ≤ 1 / 2 := by rw [hδ₁def]; exact min_le_right _ _
  have hδ₁1 : δ₁ ≤ δ₁' := by rw [hδ₁def]; exact min_le_left _ _
  -- the mass and the floor of the seed at `v = 1`
  have hseed : ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ →
      (∫ u : ℝ, airySeedU2 (-1 - γ₂ * δ) (-γ₁ * δ + γ₂ * δ + 0) (γ₂ * δ) u = -δ) ∧
      (∀ x : ℝ, |airyZero 1 - 2 * γ₁ * δ| + ceBeta1 * δ / 2 ≤ x →
        (1 + x) ^ (-(3 / 2 : ℝ)) * (c₁ * δ + c₂ * min 1 ((ceBeta1 * δ / 2) ^ 2 * x)) ≤
          ∫ t in Icc (0 : ℝ) (ceBeta1 * δ / 2),
            airySeedU2 (-1 - γ₂ * δ) (-γ₁ * δ + γ₂ * δ + 0) (γ₂ * δ) (-x + t) * bspline 4 (ceBeta1 * δ / 2) t) := by
    intro δ hδ hδle
    have h1 := hgain 1 ⟨zero_le_one, le_rfl⟩ δ ⟨hδ, hδle.trans hδ₁1⟩ 0 (by simp)
    dsimp only at h1
    have hF' : ∀ u : ℝ, -ceF1 u - γ₁f 1 * δ * ceG1 (airyZero 1) u + γ₂ * δ * ceSb 1 u + 0 * ceG1 (airyZero 1) u =
        airySeedU2 (-1 - γ₂ * δ) (-(γ₁f 1) * δ + γ₂ * δ + 0) (γ₂ * δ) u := fun u =>
      congrFun (hbSeed_m1_eq_airySeedU2 (γ₁f 1) γ₂ δ 0) u
    simp only [hF'] at h1
    rw [← hγ₁] at h1
    obtain ⟨hint, hfl⟩ := h1
    refine ⟨by linarith, fun x hx => hfl x ?_⟩
    rw [show airyZero 1 - 2 * γ₁ * δ = airyZero 1 - 2 * γ₁ * δ from rfl]
    exact hx
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 1 + |γ₁| + γ₂ := ⟨_, rfl⟩
  have hR : 0 ≤ R := by rw [hRdef]; positivity
  have E := hE R hR
  obtain ⟨K, c₀, hK, hc₀, hpos⟩ := o6_positivity (m := 4) (by norm_num) E
    (δ₁ := δ₁) (c₁ := c₁) (c₂ := c₂) (U0 := |airyZero 1|) (U1 := 2 * |γ₁|) hδ₁ hc₁ hc₂ (abs_nonneg _)
    (by positivity) (fa := fun δ => -1 - γ₂ * δ) (fb := fun δ => -γ₁ * δ + γ₂ * δ + 0) (fc := fun δ => γ₂ * δ)
    (fun δ hδ hδle => by
      have hδ1 : δ ≤ 1 := by linarith
      refine ⟨?_, ?_, ?_⟩
      · rw [abs_le]; constructor <;> nlinarith [abs_nonneg γ₁]
      · rw [abs_le]; constructor <;> nlinarith [abs_nonneg γ₁, neg_abs_le γ₁, le_abs_self γ₁]
      · rw [abs_le]; constructor <;> nlinarith [abs_nonneg γ₁])
    (fun δ hδ _ => by nlinarith)
    (fun δ hδ hδle x hx => by
      have : |airyZero 1 - 2 * γ₁ * δ| ≤ |airyZero 1| + 2 * |γ₁| * δ := by
        calc |airyZero 1 - 2 * γ₁ * δ| ≤ |airyZero 1| + |2 * γ₁ * δ| := abs_sub _ _
          _ = |airyZero 1| + 2 * |γ₁| * δ := by
              rw [abs_mul, abs_mul, abs_of_pos hδ]; norm_num
      exact (hseed δ hδ hδle).2 x (by linarith))
  have hK0 : 0 < K := by linarith
  have hβ := ceBeta1_pos
  have hpi := Real.pi_pos
  have hπ2 : 0 < Real.pi ^ 2 := by positivity
  obtain ⟨Ce, hCe, hedge⟩ := liftSymbol_edge_bound (m := 4) (by norm_num) R hR
  obtain ⟨s_max, hsmax⟩ : ∃ s : ℝ, s = (|airyZero 1| + 2 * |γ₁| + ceBeta1) / ceBeta1 := ⟨_, rfl⟩
  have hsmax0 : 0 < s_max := by
    rw [hsmax]; exact div_pos (by have := abs_nonneg (airyZero 1); have := abs_nonneg γ₁; linarith) hβ
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = 1 / (2 * Real.pi ^ 2 * s_max) := ⟨_, rfl⟩
  have hτ : 0 < τ := by rw [hτdef]; positivity
  obtain ⟨θe, hθedef⟩ : ∃ θe : ℝ, θe = ceK * K / (2 * (Ce * K ^ (-((4 : ℕ) : ℝ)) + 1)) := ⟨_, rfl⟩
  have hθe : 0 < θe := by
    have := ceK_pos
    rw [hθedef]; positivity
  obtain ⟨Mτ, hMτ1, hMτ⟩ := exists_rpow_neg_le (p := (1 / 3 : ℝ)) (by norm_num) (ε := τ) hτ
  obtain ⟨Me, hMe1, hMe⟩ := exists_rpow_neg_le (p := (1 / 2 : ℝ)) (by norm_num) (ε := θe) hθe
  refine ⟨K * (2 * |γ₁| + ceBeta1 / 2) / ceBeta1 + 2 * Real.pi ^ 2 * s_max ^ 2,
    max (max (max c₀ (8 * K ^ 3)) ((K / δ₁) ^ 3)) (max Mτ Me), ?_⟩
  intro c hc σ hσ
  have hcc₀ : c₀ ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _) |>.trans hc)
  have hc8 : 8 * K ^ 3 ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _) |>.trans hc)
  have hcδ : (K / δ₁) ^ 3 ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
  have hcτ : Mτ ≤ c := (le_max_left _ _).trans (le_max_right _ _ |>.trans hc)
  have hcMe : Me ≤ c := (le_max_right _ _).trans (le_max_right _ _ |>.trans hc)
  have hc2000 : 2000 ≤ c := hc₀.trans hcc₀
  have hc0 : 0 < c := by linarith
  have hε : 0 < liftEps c := liftEps_pos hc0
  have hcube : liftEps c ^ 3 * c = 1 := liftEps_cube_mul hc0
  have hKe3 : (K * liftEps c) ^ 3 * c = K ^ 3 := by
    calc (K * liftEps c) ^ 3 * c = K ^ 3 * (liftEps c ^ 3 * c) := by ring
      _ = K ^ 3 := by rw [hcube, mul_one]
  have hKε : K * liftEps c ≤ 1 / 2 := by
    by_contra hcon
    push_neg at hcon
    have h2 : (1 / 2 : ℝ) ^ 3 < (K * liftEps c) ^ 3 := pow_lt_pow_left₀ hcon (by norm_num) (by norm_num)
    have h3 := mul_lt_mul_of_pos_right h2 hc0
    rw [hKe3] at h3
    norm_num at h3
    linarith
  have hεK : liftEps c ≤ 1 / 2 := by nlinarith
  have hKεpos : 0 < K * liftEps c := by positivity
  -- the lift
  obtain ⟨f, hfeig, hfrep, -, hf0⟩ := exists_hankelEigenfn_lift (m := 4) (by norm_num) (-1 - γ₂ * (K * liftEps c))
    (-γ₁ * (K * liftEps c) + γ₂ * (K * liftEps c) + 0) (γ₂ * (K * liftEps c)) (K := K) (c := c) hK hc2000 hc8 hσ
  obtain ⟨smin, hsmin⟩ : ∃ s : ℝ, s = (|airyZero 1| + 2 * |γ₁| * (K * liftEps c) + ceBeta1 * (K * liftEps c) / 2) / ceBeta1 :=
    ⟨_, rfl⟩
  have hsmin0 : 0 < smin := by
    rw [hsmin]; exact div_pos (by have := abs_nonneg (airyZero 1); have := abs_nonneg γ₁; positivity) hβ
  have hsminle : smin ≤ s_max := by
    rw [hsmin, hsmax]
    refine div_le_div_of_nonneg_right ?_ hβ.le
    have := abs_nonneg γ₁
    nlinarith
  obtain ⟨y₀, hy₀⟩ : ∃ y : ℝ, y = Real.pi ^ 2 * liftEps c ^ 2 * smin := ⟨_, rfl⟩
  have hy₀0 : 0 < y₀ := by rw [hy₀]; positivity
  have hy₀half : y₀ ≤ 1 / 2 := by
    have hτc : liftEps c ≤ τ := hMτ c hcτ
    have h1 : liftEps c ^ 2 ≤ liftEps c := by nlinarith
    have h2 : y₀ ≤ Real.pi ^ 2 * s_max * τ := by
      rw [hy₀]
      calc Real.pi ^ 2 * liftEps c ^ 2 * smin ≤ Real.pi ^ 2 * τ * s_max := by
            have : liftEps c ^ 2 ≤ τ := h1.trans hτc
            gcongr
        _ = Real.pi ^ 2 * s_max * τ := by ring
    have h3 : Real.pi ^ 2 * s_max * τ = 1 / 2 := by rw [hτdef]; field_simp
    linarith
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = c / Real.pi ^ 2 * Real.exp y₀ := ⟨_, rfl⟩
  have hTpos0 : 0 < T := by rw [hTdef]; positivity
  -- positivity beyond `T`
  have hpos' : ∀ Δ : ℝ, T ≤ Δ → 0 < f Δ := by
    intro Δ hΔ
    have hΔ0 : 0 < Δ := hTpos0.trans_le hΔ
    obtain ⟨ξ, hξdef⟩ : ∃ ξ : ℝ, ξ = Δ / c := ⟨_, rfl⟩
    have hξ : 0 < ξ := by rw [hξdef]; positivity
    have hcξ : c * ξ = Δ := by rw [hξdef]; field_simp
    have hS : (|airyZero 1| + 2 * |γ₁| * (K * liftEps c) + ceBeta1 * (K * liftEps c) / 2) / ceBeta1 ≤ hbS c ξ := by
      rw [← hsmin]
      have hexp : Real.exp y₀ ≤ Real.pi ^ 2 * ξ := by
        have h1 : Real.pi ^ 2 * T / c ≤ Real.pi ^ 2 * Δ / c := by gcongr
        have h2 : Real.pi ^ 2 * T / c = Real.exp y₀ := by rw [hTdef]; field_simp
        rw [hξdef]; rw [h2] at h1; calc Real.exp y₀ ≤ Real.pi ^ 2 * Δ / c := h1
          _ = Real.pi ^ 2 * (Δ / c) := by ring
      have hlog : y₀ ≤ Real.log (Real.pi ^ 2 * ξ) := (Real.le_log_iff_exp_le (by positivity)).mpr hexp
      unfold hbS
      have hsm : smin = y₀ / (Real.pi ^ 2 * liftEps c ^ 2) := by rw [hy₀]; field_simp
      rw [hsm]
      exact div_le_div_of_nonneg_right hlog (by positivity)
    have hz : 0 < (iMain (airySeedU2 (-1 - γ₂ * (K * liftEps c)) (-γ₁ * (K * liftEps c) + γ₂ * (K * liftEps c) + 0)
          (γ₂ * (K * liftEps c))) (ceBeta1 * K * liftEps c / 2) 4 c ξ +
        (σ : ℂ) * iDual (airySeedU2 (-1 - γ₂ * (K * liftEps c)) (-γ₁ * (K * liftEps c) + γ₂ * (K * liftEps c) + 0)
          (γ₂ * (K * liftEps c))) (ceBeta1 * K * liftEps c / 2) 4 c ξ).re :=
      hpos (K := K) (c := c) (σ := σ) (ξ := ξ) le_rfl hcc₀ hc8 hcδ hσ hξ hS
    rw [← hfrep ξ hξ, Complex.ofReal_re, hcξ] at hz
    have h1 : 0 < c ^ (1 / 3 : ℝ) * hankelRho0 c Δ :=
      mul_pos (Real.rpow_pos_of_pos hc0 _) (hankelRho0_pos hc0 hΔ0)
    exact (mul_pos_iff_of_pos_left h1).mp hz
  have hfT : 0 < f T := hpos' T le_rfl
  have hKεδ : K * liftEps c ≤ δ₁ := by
    have h2 : K ^ 3 ≤ δ₁ ^ 3 * c := by
      have := hcδ
      rw [div_pow, div_le_iff₀ (by positivity)] at this
      linarith
    have h3 : (K * liftEps c) ^ 3 ≤ δ₁ ^ 3 := by
      by_contra hcon
      push_neg at hcon
      have := mul_lt_mul_of_pos_right hcon hc0
      rw [hKe3] at this
      linarith
    exact le_of_pow_le_pow_left₀ (by norm_num) hδ₁.le h3
  -- the origin
  have hint := (hseed (K * liftEps c) hKεpos hKεδ).1
  have hbdc := (by
    have hδ1 : K * liftEps c ≤ 1 := by linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_le]; constructor <;> nlinarith [abs_nonneg γ₁]
    · rw [abs_le]; constructor <;> nlinarith [abs_nonneg γ₁, neg_abs_le γ₁, le_abs_self γ₁]
    · rw [abs_le]; constructor <;> nlinarith [abs_nonneg γ₁] :
    |(-1 - γ₂ * (K * liftEps c))| ≤ R ∧ |(-γ₁ * (K * liftEps c) + γ₂ * (K * liftEps c) + 0)| ≤ R ∧
      |γ₂ * (K * liftEps c)| ≤ R)
  have hedge' := hedge hbdc.1 hbdc.2.1 hbdc.2.2 hK (by linarith : (2 : ℝ) ≤ c)
  have hW0 := liftSymbol_zero_eq (hasU2_airySeedU2 (-1 - γ₂ * (K * liftEps c))
    (-γ₁ * (K * liftEps c) + γ₂ * (K * liftEps c) + 0) (γ₂ * (K * liftEps c))) (ceBeta1 * K * liftEps c / 2) 4
  rw [hint] at hW0
  rw [hW0] at hf0
  have hc56 : c ^ (-(5 / 6 : ℝ)) = liftEps c * c ^ (-(1 / 2 : ℝ)) := by
    unfold liftEps; rw [← Real.rpow_add hc0]; norm_num
  have hc12 : c ^ (-(1 / 2 : ℝ)) ≤ θe := hMe c hcMe
  have hKe4 : 0 < K ^ (-((4 : ℕ) : ℝ)) := by positivity
  have hpθ : Ce * K ^ (-((4 : ℕ) : ℝ)) * θe ≤ ceK * K / 2 := by
    rw [hθedef]
    have hp : 0 ≤ Ce * K ^ (-((4 : ℕ) : ℝ)) := by positivity
    have hk : 0 < ceK * K := by have := ceK_pos; positivity
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hWle : ‖liftSymbol (airySeedU2 (-1 - γ₂ * (K * liftEps c)) (-γ₁ * (K * liftEps c) + γ₂ * (K * liftEps c) + 0)
      (γ₂ * (K * liftEps c))) (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖ ≤
      ceK * (K * liftEps c) := by
    refine hedge'.trans ?_
    rw [hc56]
    have h1 : Ce * K ^ (-((4 : ℕ) : ℝ)) * (liftEps c * c ^ (-(1 / 2 : ℝ))) ≤ liftEps c * (ceK * K / 2) := by
      calc Ce * K ^ (-((4 : ℕ) : ℝ)) * (liftEps c * c ^ (-(1 / 2 : ℝ)))
          = liftEps c * (Ce * K ^ (-((4 : ℕ) : ℝ)) * c ^ (-(1 / 2 : ℝ))) := by ring
        _ ≤ liftEps c * (Ce * K ^ (-((4 : ℕ) : ℝ)) * θe) := by gcongr
        _ ≤ _ := by gcongr
    have hk : 0 < ceK * (K * liftEps c) := by have := ceK_pos; positivity
    nlinarith
  have hσn : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  have horigin : σ * f 0 ≤ 0 := by
    have hre := congrArg Complex.re hf0
    rw [Complex.ofReal_re, Complex.add_re] at hre
    have h2 : (((σ : ℂ)) * (((ceK * -(K * liftEps c) : ℝ)) : ℂ)).re = σ * (ceK * -(K * liftEps c)) := by
      rw [← Complex.ofReal_mul, Complex.ofReal_re]
    rw [h2] at hre
    have h3 : |(liftSymbol (airySeedU2 (-1 - γ₂ * (K * liftEps c)) (-γ₁ * (K * liftEps c) + γ₂ * (K * liftEps c) + 0)
      (γ₂ * (K * liftEps c))) (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)).re| ≤
        ceK * (K * liftEps c) := (Complex.abs_re_le_norm _).trans hWle
    have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
    have hsr : σ * (liftSymbol (airySeedU2 (-1 - γ₂ * (K * liftEps c)) (-γ₁ * (K * liftEps c) + γ₂ * (K * liftEps c) + 0)
      (γ₂ * (K * liftEps c))) (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)).re ≤ ceK * (K * liftEps c) := by
      calc _ ≤ |σ * (liftSymbol _ _ 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)).re| := le_abs_self _
        _ = |σ| * |(liftSymbol _ _ 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)).re| := abs_mul _ _
        _ ≤ _ := by rw [hσn, one_mul]; exact h3
    rw [hre]
    have e : ∀ w x : ℝ, σ * (w + σ * x) = σ * w + (σ * σ) * x := fun w x => by ring
    rw [e, hσ2]
    linarith
  refine ⟨T, f, { hfeig with
    nonzero := ⟨T, hTpos0.le, hfT.ne'⟩
    origin_sign := horigin
    tail_nonneg := fun Δ hΔ => (hpos' Δ hΔ).le }, ?_⟩
  -- the threshold
  have hexp : Real.exp y₀ ≤ 1 + y₀ + 2 * y₀ ^ 2 := by
    have h1 := Real.exp_bound_div_one_sub_of_interval' hy₀0 (by linarith : y₀ < 1)
    refine h1.le.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg y₀, mul_nonneg (sq_nonneg y₀) (by linarith : (0 : ℝ) ≤ 1 - 2 * y₀)]
  have hεc : liftEps c * c ^ (1 / 3 : ℝ) = 1 := by rw [rpow_third_eq hc0]; field_simp
  have hcε2 : c * liftEps c ^ 2 = c ^ (1 / 3 : ℝ) := by
    rw [rpow_third_eq hc0]; field_simp; linarith
  have e1 : c / Real.pi ^ 2 * y₀ = c ^ (1 / 3 : ℝ) * smin := by
    rw [hy₀, ← hcε2]; field_simp
  have e2 : c / Real.pi ^ 2 * (2 * y₀ ^ 2) = 2 * Real.pi ^ 2 * (liftEps c * smin ^ 2) := by
    rw [hy₀]; field_simp
    linear_combination hcube
  have e3 : c ^ (1 / 3 : ℝ) * smin = |airyZero 1| / ceBeta1 * c ^ (1 / 3 : ℝ) + K * (2 * |γ₁| + ceBeta1 / 2) / ceBeta1 := by
    rw [hsmin]; field_simp
    linear_combination (2 * (2 * |γ₁| * K + ceBeta1 * K / 2)) * hεc
  have e4 : 2 * Real.pi ^ 2 * (liftEps c * smin ^ 2) ≤ 2 * Real.pi ^ 2 * s_max ^ 2 := by
    have h1 : liftEps c * smin ^ 2 ≤ 1 * s_max ^ 2 := by
      have : smin ^ 2 ≤ s_max ^ 2 := by gcongr
      have h0 : 0 ≤ smin ^ 2 := sq_nonneg _
      nlinarith
    nlinarith
  have hβeq : hankelBeta1 = ceBeta1 := rfl
  calc T = c / Real.pi ^ 2 * Real.exp y₀ := hTdef
    _ ≤ c / Real.pi ^ 2 * (1 + y₀ + 2 * y₀ ^ 2) := by gcongr
    _ = c / Real.pi ^ 2 + c / Real.pi ^ 2 * y₀ + c / Real.pi ^ 2 * (2 * y₀ ^ 2) := by ring
    _ ≤ c / Real.pi ^ 2 + airyOrderCoeff * c ^ (1 / 3 : ℝ) +
        (K * (2 * |γ₁| + ceBeta1 / 2) / ceBeta1 + 2 * Real.pi ^ 2 * s_max ^ 2) := by
      rw [e1, e2, e3, airyOrderCoeff, hβeq]
      linarith

/-- **The named hypotheses of the middle band, in one place**: the `GT.1` bounds of the three basis seeds (`Gt1BasisInput m`, the `GT.1`
formalisation task) and the quotient bound `O4QuotientBound L` for `0 < L ≤ 0.002` (`M_F ≤ 0.13`, `[O4C (B)]`).  Discharging a field changes no
downstream statement. -/
structure MiddleBandInputs (m : ℕ) : Prop where
  gt1 : Gt1BasisInput m
  o4 : ∀ L : ℝ, 0 < L → L ≤ 0.002 → O4QuotientBound L

/-- The analytic bricks of `O.6` from the named hypotheses `MiddleBandInputs m` (`m ≥ 3`). -/
theorem o6Bricks_of_inputs {m : ℕ} (hm : 3 ≤ m) (hin : MiddleBandInputs m) : O6Bricks m := by
  obtain ⟨ϑ, K1, K2, hϑ⟩ := prof_exists
  refine ⟨2 * ceK * cA * ceCs ^ (1 / 2 : ℝ), hb_leading_pos, fun R hR => ?_⟩
  refine ⟨hb_leading_pos, fun {X} hX {δ₀} hδ x => windowSmooth_eq_bspline_integral hX hδ (by omega) x, ?_, ?_, ?_, ?_⟩
  · obtain ⟨C, hC, h⟩ := hb_estimate_airySeed_uniform_val (m := m) (by omega) R hR
    exact ⟨C, hC, fun {a b c₀ K M₁ c ξ} ha hb hc hK hM hc8 hc2k hξ hS hMS => h ha hb hc hK hM hc8 hc2k hξ hS hMS⟩
  · obtain ⟨C, hC, h⟩ := iDual_bound_e3_airySeed hm R hR
    exact ⟨C, hC, fun {a b c₀ δ₀ c ξ} ha hb hc hδ h2 hξ hS => h ha hb hc hδ h2 hξ hS⟩
  · intro Sw
    obtain ⟨C, hC, h⟩ := window_translation_airySeed (m := m) (by omega) Sw R hR
    exact ⟨C, hC, fun {a b c₀ σ δ₀ c ξ} ha hb hc hσ hδ h2 hξ hS => h ha hb hc hσ hδ h2 hξ hS⟩
  · obtain ⟨C, hC0, h⟩ := o5_e6_airySeed hϑ hin.gt1 R hR
    exact ⟨C, hC0, fun {a b c₀ δ₀ c ξ L} ha hb hc hδ hc2 hξ hL hL0 hL2 hS =>
      h ha hb hc hδ hc2 hξ hL (hin.o4 L hL0 hL2) hL0 hL2 hS⟩

/-- **`O.9'` at `m₀ = 1`** from the two named hypotheses of the middle band. -/
theorem hbThresholdsUpper_of_inputs (hin : MiddleBandInputs 4) : HbThresholdsUpper :=
  hbThresholdsUpper_of_bricks (o6Bricks_of_inputs (by norm_num) hin)

/-- info: 'FormalResearch.SignUncertainty.hbThresholdsUpper_of_bricks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hbThresholdsUpper_of_bricks
/-- info: 'FormalResearch.SignUncertainty.o6Bricks_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms o6Bricks_of_inputs
/-- info: 'FormalResearch.SignUncertainty.hbThresholdsUpper_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hbThresholdsUpper_of_inputs

end FormalResearch.SignUncertainty
