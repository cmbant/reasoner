module

public import FormalResearch.SignUncertainty.CeLiftSign
public import FormalResearch.SignUncertainty.CeLiftEdge

/-!
# The physical sign of `thm:ce-hb-lift` (M6): the edge sign, the origin and the threshold

`ceLift_physical`: from `O6Bricks 4` (the analytic bricks of `O.6`, a consequence of the open quotient bound `O4QuotientBound`) and the
source-family input `CeSourceFamily`, there are `K₁, c₁` such that for every `c ≥ c₁` there are Hankel eigenfunctions `f₊` (`σ = +1`) and
`f₋` (`σ = -1`), a threshold `T ≤ c/π² + A c^{1/3} + K₁` (`A` the Airy order coefficient), `f₋(0) = 0 < f₊(0)` and
`f₊ + f₋ ≤ 0` on `[T, ∞)`.  Then `h = (f₊ + f₋)/2` has `h ≤ 0` beyond `T`, `ĥ = (f₊ - f₋)/2`, `h(0) = ĥ(0) > 0`; the remaining
input of `CeHankelPair` is the Fourier sign `f₋ ≤ f₊` (not proved here, see `ceHankelPair_of_eigenfns`).  Conditional on `O6Bricks 4` and `CeSourceFamily`
(the latter is not instantiated for `convSource`).  `CeHankelPair` and the headline `ce_hb_lift_m1` remain open.  Proof: the tuning `η` of `ceLift_tune` at the
edge `c^{1/3}` (its size from the `edge` field and `liftSymbol_edge_bound`), the pair of `ceLift_pair`, and `o6_positivity_dual_Kc` for the main seed
`-D_η` and the reflected seed `-S_c` (`h = -(I_main[-D_η] + I_dual[-S_c])`, so `f₊ + f₋ = 2h ≤ 0` where `S_eff ≥ s_min`, i.e. `Δ ≥ T`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

set_option maxHeartbeats 8000000 in
theorem ceLift_physical (h : O6Bricks 4) {S : ℝ → ℝ → ℝ} (hS : CeSourceFamily S) :
    ∃ K₁ c₁ : ℝ, ∀ {c : ℝ}, c₁ ≤ c → ∃ (fp fm : ℝ → ℝ) (T : ℝ),
      IsHankelEigenfn c 1 fp ∧ IsHankelEigenfn c (-1) fm ∧ fm 0 = 0 ∧ 0 < fp 0 ∧
      T ≤ c / Real.pi ^ 2 + airyOrderCoeff * c ^ (1 / 3 : ℝ) + K₁ ∧
      ∀ Δ : ℝ, T ≤ Δ → fp Δ + fm Δ ≤ 0 := by
  classical
  obtain ⟨g0, hg0, hE⟩ := h
  obtain ⟨m₀, M₀, hm₀, hM₀, hmass⟩ := hS.mass
  have hk := ceK_pos
  have hβ := ceBeta1_pos
  have hpi := Real.pi_pos
  obtain ⟨δ₁', hδ₁', γ₂, hγ₂, γ₁f, c₁, hc₁, c₂, hc₂, hgain⟩ :=
    hbSeedSpec_airy_smoothing_gain (m := 4) (by norm_num) (V_max := 1) (ε₀ := 2 + M₀) zero_le_one (by positivity)
  obtain ⟨γ₁, hγ₁⟩ : ∃ γ₁ : ℝ, γ₁ = γ₁f 1 := ⟨_, rfl⟩
  obtain ⟨δ₁, hδ₁def⟩ : ∃ δ₁ : ℝ, δ₁ = min δ₁' (1 / 2) := ⟨_, rfl⟩
  have hδ₁ : 0 < δ₁ := by rw [hδ₁def]; exact lt_min hδ₁' (by norm_num)
  have hδ₁1 : δ₁ ≤ δ₁' := by rw [hδ₁def]; exact min_le_left _ _
  have hseed : ∀ δ r : ℝ, 0 < δ → δ ≤ δ₁ → |r| ≤ (2 + M₀) * δ →
      (∫ u : ℝ, airySeedU2 (-1 - γ₂ * δ) (-γ₁ * δ + γ₂ * δ + r) (γ₂ * δ) u = -δ + r) ∧
      (∀ x : ℝ, |airyZero 1 - 2 * γ₁ * δ| + ceBeta1 * δ / 2 ≤ x →
        (1 + x) ^ (-(3 / 2 : ℝ)) * (c₁ * δ + c₂ * min 1 ((ceBeta1 * δ / 2) ^ 2 * x)) ≤
          ∫ t in Icc (0 : ℝ) (ceBeta1 * δ / 2),
            airySeedU2 (-1 - γ₂ * δ) (-γ₁ * δ + γ₂ * δ + r) (γ₂ * δ) (-x + t) * bspline 4 (ceBeta1 * δ / 2) t) := by
    intro δ r hδ hδle hr
    have h1 := hgain 1 ⟨zero_le_one, le_rfl⟩ δ ⟨hδ, hδle.trans hδ₁1⟩ r hr
    dsimp only at h1
    have hF' : ∀ u : ℝ, -ceF1 u - γ₁f 1 * δ * ceG1 (airyZero 1) u + γ₂ * δ * ceSb 1 u + r * ceG1 (airyZero 1) u =
        airySeedU2 (-1 - γ₂ * δ) (-(γ₁f 1) * δ + γ₂ * δ + r) (γ₂ * δ) u := fun u =>
      congrFun (hbSeed_m1_eq_airySeedU2 (γ₁f 1) γ₂ δ r) u
    simp only [hF'] at h1
    rw [← hγ₁] at h1
    obtain ⟨hint, hfl⟩ := h1
    exact ⟨by linarith, fun x hx => hfl x hx⟩
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 1 + |γ₁| + γ₂ + (2 + M₀) := ⟨_, rfl⟩
  have hR : 0 ≤ R := by rw [hRdef]; positivity
  have E := hE R hR
  -- the residual `r₀ = Kε - ∫ S_c` is small
  have hMpos : ∀ {c : ℝ}, 2000 ≤ c → 0 ≤ ∫ u : ℝ, S c u ∧ ∫ u : ℝ, S c u ≤ M₀ * liftEps c := fun {c} hc =>
    ⟨(mul_pos hm₀ (liftEps_pos (by linarith))).le.trans (hmass hc).1, (hmass hc).2⟩
  have hr0 : ∀ {K c : ℝ}, 1 ≤ K → 2000 ≤ c → |K * liftEps c - ∫ u : ℝ, S c u| ≤ (1 + M₀) * (K * liftEps c) := by
    intro K c hK hc
    have hε := liftEps_pos (show 0 < c by linarith)
    obtain ⟨h1, h2⟩ := hMpos hc
    have hεK : liftEps c ≤ K * liftEps c := by nlinarith
    rw [abs_le]; constructor <;> nlinarith
  -- the tuning
  obtain ⟨etaF, hetaFdef⟩ : ∃ f : ℝ → ℝ → ℝ, f = fun K c =>
      if hh : ∃ η, CeTune γ₁ γ₂ S K c η then hh.choose else 0 := ⟨_, rfl⟩
  have hetaF : ∀ {K c : ℝ}, 0 ≤ K → 0 < c → |etaF K c| ≤ K * liftEps c := by
    intro K c hK hc
    by_cases hh : ∃ η, CeTune γ₁ γ₂ S K c η
    · rw [hetaFdef]; simp only [dif_pos hh]; exact hh.choose_spec.1
    · rw [hetaFdef]; simp only [dif_neg hh, abs_zero]; have := liftEps_pos hc; positivity
  have hetaF_tune : ∀ {K c : ℝ}, (∃ η, CeTune γ₁ γ₂ S K c η) → CeTune γ₁ γ₂ S K c (etaF K c) := by
    intro K c hh; rw [hetaFdef]; simp only [dif_pos hh]; exact hh.choose_spec
  have hr : ∀ {K c : ℝ}, 1 ≤ K → 2000 ≤ c →
      |(K * liftEps c - ∫ u : ℝ, S c u) - etaF K c| ≤ (2 + M₀) * (K * liftEps c) := by
    intro K c hK hc
    have h1 := hr0 hK hc
    have h2 := hetaF (by linarith) (show 0 < c by linarith) (K := K)
    calc _ ≤ |K * liftEps c - ∫ u : ℝ, S c u| + |etaF K c| := abs_sub _ _
      _ ≤ _ := by linarith
  have hb_bd : ∀ {δ r : ℝ}, 0 < δ → δ ≤ 1 → |r| ≤ (2 + M₀) * δ → |-γ₁ * δ + γ₂ * δ + r| ≤ R := by
    intro δ r hδ hδ1 hr
    have h1 : |-γ₁ * δ + γ₂ * δ + r| ≤ |γ₁| * δ + γ₂ * δ + (2 + M₀) * δ := by
      calc _ ≤ |-γ₁ * δ| + |γ₂ * δ| + |r| := abs_add_three _ _ _
        _ = |γ₁| * δ + γ₂ * δ + |r| := by
          rw [abs_mul, abs_mul, abs_neg, abs_of_pos hδ, abs_of_pos hγ₂]
        _ ≤ _ := by linarith
    have h2 : (|γ₁| + γ₂ + (2 + M₀)) * δ ≤ |γ₁| + γ₂ + (2 + M₀) :=
      mul_le_of_le_one_right (by positivity) hδ1
    rw [hRdef]; nlinarith
  -- the main-seed families of `o6_positivity_dual_Kc`
  obtain ⟨K₀, c₀, hK₀, hc₀, hpos⟩ := o6_positivity_dual_Kc (m := 4) (by norm_num) E (fun _ c u => -S c u) hS.dual
    (δ₁ := δ₁) (c₁ := c₁) (c₂ := c₂) (U0 := |airyZero 1|) (U1 := 2 * |γ₁|) hδ₁ hc₁ hc₂ (abs_nonneg _)
    (by positivity)
    (fa := fun K c => -1 - γ₂ * (K * liftEps c))
    (fb := fun K c => -γ₁ * (K * liftEps c) + γ₂ * (K * liftEps c) +
      ((K * liftEps c - ∫ u : ℝ, S c u) - etaF K c))
    (fc := fun K c => γ₂ * (K * liftEps c))
    (fun {K c} hK hc hc8 hcδ => by
      have hc0 : (0 : ℝ) < c := by linarith
      have hδ := ce_delta_half hK hc0 hc8
      have hδ0 : 0 < K * liftEps c := by have := liftEps_pos hc0; positivity
      have hbb := hb_bd hδ0 (by linarith) (hr hK hc)
      refine ⟨?_, hbb, ?_⟩
      · rw [abs_le]; constructor <;> nlinarith [abs_nonneg γ₁]
      · rw [abs_le]; constructor <;> nlinarith [abs_nonneg γ₁])
    (fun {K c} hK hc hc8 hcδ => by
      have hδ0 : 0 < K * liftEps c := by have := liftEps_pos (show (0 : ℝ) < c by linarith); positivity
      nlinarith)
    (fun {K c} hK hc hc8 hcδ x hx => by
      have hc0 : (0 : ℝ) < c := by linarith
      have hδ0 : 0 < K * liftEps c := by have := liftEps_pos hc0; positivity
      have hδle := ce_delta_le (by linarith) hδ₁ hc0 hcδ
      have : |airyZero 1 - 2 * γ₁ * (K * liftEps c)| ≤ |airyZero 1| + 2 * |γ₁| * (K * liftEps c) := by
        calc |airyZero 1 - 2 * γ₁ * (K * liftEps c)| ≤ |airyZero 1| + |2 * γ₁ * (K * liftEps c)| := abs_sub _ _
          _ = |airyZero 1| + 2 * |γ₁| * (K * liftEps c) := by
              rw [abs_mul, abs_mul, abs_of_pos hδ0]; norm_num
      exact (hseed (K * liftEps c) _ hδ0 hδle (hr hK hc)).2 x (by linarith))
  -- thresholds for the fixed `K = K₀`
  have hK0 : 0 < K₀ := by linarith
  obtain ⟨Ce, hCe, hedge⟩ := liftSymbol_edge_bound (m := 4) (by norm_num) R hR
  obtain ⟨CS, hCS0, hSedge⟩ := hS.edge K₀ hK₀
  obtain ⟨Pn, hPndef⟩ : ∃ P : ℝ, P = Ce * K₀ ^ (-((4 : ℕ) : ℝ)) + CS := ⟨_, rfl⟩
  have hKe4 : 0 < K₀ ^ (-((4 : ℕ) : ℝ)) := by positivity
  have hPn : 0 < Pn := by rw [hPndef]; positivity
  have hCeP : Ce * K₀ ^ (-((4 : ℕ) : ℝ)) ≤ Pn := by rw [hPndef]; linarith
  have hCSP : CS ≤ Pn := by rw [hPndef]; have : 0 < Ce * K₀ ^ (-((4 : ℕ) : ℝ)) := by positivity
                            linarith
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = ceK * min (1 / 2) (m₀ / 4) / Pn := ⟨_, rfl⟩
  have hθ : 0 < θ := by rw [hθdef]; have := lt_min (show (0 : ℝ) < 1 / 2 by norm_num) (show 0 < m₀ / 4 by positivity); positivity
  obtain ⟨Mθ, hMθ1, hMθ⟩ := exists_rpow_neg_le (p := (1 / 2 : ℝ)) (by norm_num) (ε := θ) hθ
  obtain ⟨s_max, hsmax⟩ : ∃ s : ℝ, s = (|airyZero 1| + 2 * |γ₁| + ceBeta1) / ceBeta1 := ⟨_, rfl⟩
  have hsmax0 : 0 < s_max := by
    rw [hsmax]; exact div_pos (by have := abs_nonneg (airyZero 1); have := abs_nonneg γ₁; linarith) hβ
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = 1 / (2 * Real.pi ^ 2 * s_max) := ⟨_, rfl⟩
  have hτ : 0 < τ := by rw [hτdef]; positivity
  obtain ⟨Mτ, hMτ1, hMτ⟩ := exists_rpow_neg_le (p := (1 / 3 : ℝ)) (by norm_num) (ε := τ) hτ
  refine ⟨K₀ * (2 * |γ₁| + ceBeta1 / 2) / ceBeta1 + 2 * Real.pi ^ 2 * s_max ^ 2,
    max (max (max c₀ (8 * K₀ ^ 3)) ((K₀ / δ₁) ^ 3)) (max Mτ Mθ), ?_⟩
  intro c hc
  have hcc₀ : c₀ ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _) |>.trans hc)
  have hc8 : 8 * K₀ ^ 3 ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _) |>.trans hc)
  have hcδ : (K₀ / δ₁) ^ 3 ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
  have hcτ : Mτ ≤ c := (le_max_left _ _).trans (le_max_right _ _ |>.trans hc)
  have hcθ : Mθ ≤ c := (le_max_right _ _).trans (le_max_right _ _ |>.trans hc)
  have hc2000 : 2000 ≤ c := hc₀.trans hcc₀
  have hc0 : 0 < c := by linarith
  have hε : 0 < liftEps c := liftEps_pos hc0
  have hcube : liftEps c ^ 3 * c = 1 := liftEps_cube_mul hc0
  have hKε : K₀ * liftEps c ≤ 1 / 2 := ce_delta_half hK₀ hc0 hc8
  have hεK : liftEps c ≤ 1 / 2 := by nlinarith
  have hKεpos : 0 < K₀ * liftEps c := by positivity
  have hKεδ : K₀ * liftEps c ≤ δ₁ := ce_delta_le hK0 hδ₁ hc0 hcδ
  -- the coefficients of `D₀`
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = 1 + γ₂ * (K₀ * liftEps c) := ⟨_, rfl⟩
  obtain ⟨b₀, hb₀def⟩ : ∃ b : ℝ, b = ceDb0 γ₁ γ₂ S K₀ c := ⟨_, rfl⟩
  obtain ⟨c₀', hc₀'def⟩ : ∃ b : ℝ, b = -(γ₂ * (K₀ * liftEps c)) := ⟨_, rfl⟩
  have hb₀r : b₀ = -(-γ₁ * (K₀ * liftEps c) + γ₂ * (K₀ * liftEps c) + (K₀ * liftEps c - ∫ u : ℝ, S c u)) := by
    rw [hb₀def, ceDb0]; ring
  have hD0F : ∀ r : ℝ, (fun u => airySeedU2 a (b₀ + (((K₀ * liftEps c - ∫ u : ℝ, S c u) - r) - (K₀ * liftEps c - ∫ u : ℝ, S c u)) * 0) c₀' u) =
      fun u => airySeedU2 a b₀ c₀' u := fun r => by funext u; simp
  have hDF : ∀ η : ℝ, airySeedU2 a (b₀ + η) c₀' = fun u =>
      -(airySeedU2 (-1 - γ₂ * (K₀ * liftEps c))
        (-γ₁ * (K₀ * liftEps c) + γ₂ * (K₀ * liftEps c) + ((K₀ * liftEps c - ∫ u : ℝ, S c u) - η)) (γ₂ * (K₀ * liftEps c)) u) := by
    intro η; funext u
    simp only [airySeedU2, hb₀def, ceDb0, hadef, hc₀'def]; ring
  have hmassD : ∫ u : ℝ, airySeedU2 a b₀ c₀' u = ∫ u : ℝ, S c u := by
    have h0 := (hseed (K₀ * liftEps c) (K₀ * liftEps c - ∫ u : ℝ, S c u) hKεpos hKεδ
      (by have := hr0 hK₀ hc2000; nlinarith)).1
    have e := hDF (0 : ℝ)
    have e' : airySeedU2 a b₀ c₀' = fun u => -(airySeedU2 (-1 - γ₂ * (K₀ * liftEps c))
        (-γ₁ * (K₀ * liftEps c) + γ₂ * (K₀ * liftEps c) + (K₀ * liftEps c - ∫ u : ℝ, S c u)) (γ₂ * (K₀ * liftEps c)) u) := by
      have := hDF 0
      simpa using this
    rw [e', integral_neg, h0]; ring
  -- the edge bounds
  have hc56 : c ^ (-(5 / 6 : ℝ)) = liftEps c * c ^ (-(1 / 2 : ℝ)) := by
    unfold liftEps; rw [← Real.rpow_add hc0]; norm_num
  have hc12 : c ^ (-(1 / 2 : ℝ)) ≤ θ := hMθ c hcθ
  have hc12p : 0 ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hc0.le _
  have hcoef0 : |a| ≤ R ∧ |b₀| ≤ R ∧ |c₀'| ≤ R := by
    have hδ0 := hKεpos
    refine ⟨?_, ?_, ?_⟩
    · rw [hadef, abs_le]; constructor <;> nlinarith [abs_nonneg γ₁]
    · rw [hb₀r, abs_neg]
      refine hb_bd hKεpos (by linarith) ?_
      have := hr0 hK₀ hc2000
      have h3 : 0 ≤ K₀ * liftEps c := hKεpos.le
      nlinarith
    · rw [hc₀'def, abs_le]; constructor <;> nlinarith [abs_nonneg γ₁]
  have hWD0 : ‖liftSymbol (airySeedU2 a b₀ c₀') (ceBeta1 * K₀ * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖ ≤
      Ce * K₀ ^ (-((4 : ℕ) : ℝ)) * c ^ (-(5 / 6 : ℝ)) :=
    hedge hcoef0.1 hcoef0.2.1 hcoef0.2.2 hK₀ (by linarith)
  have hWg : ‖liftSymbol (ceG1 (airyZero 1)) (ceBeta1 * K₀ * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖ ≤
      Ce * K₀ ^ (-((4 : ℕ) : ℝ)) * c ^ (-(5 / 6 : ℝ)) := by
    rw [← airySeedU2_zero_one_zero]
    have h1R : (1 : ℝ) ≤ R := by rw [hRdef]; have := abs_nonneg γ₁; linarith
    exact hedge (by simpa using hR) (by simpa using h1R) (by simpa using hR) hK₀ (by linarith)
  have hWS : ‖liftSymbol (S c) (ceBeta1 * K₀ * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖ ≤
      CS * c ^ (-(5 / 6 : ℝ)) := hSedge hc2000 hc8
  obtain ⟨Qe, hQedef⟩ : ∃ Q : ℝ, Q = ‖liftSymbol (airySeedU2 a b₀ c₀') (ceBeta1 * K₀ * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖ +
      ‖liftSymbol (S c) (ceBeta1 * K₀ * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖ := ⟨_, rfl⟩
  have hQe : Qe ≤ Pn * (liftEps c * θ) := by
    have h1 : Qe ≤ Pn * c ^ (-(5 / 6 : ℝ)) := by
      rw [hQedef]
      have := mul_le_mul_of_nonneg_right hCeP (Real.rpow_nonneg hc0.le (-(5 / 6 : ℝ)))
      have := mul_le_mul_of_nonneg_right hCSP (Real.rpow_nonneg hc0.le (-(5 / 6 : ℝ)))
      rw [hPndef]; nlinarith
    refine h1.trans ?_
    rw [hc56]
    gcongr
  have hQe_k : Qe ≤ ceK * min (1 / 2) (m₀ / 4) * liftEps c := by
    refine hQe.trans ?_
    have : Pn * (liftEps c * θ) = ceK * min (1 / 2) (m₀ / 4) * liftEps c := by
      rw [hθdef]; field_simp
    rw [this]
  have hQe_nn : 0 ≤ Qe := by rw [hQedef]; positivity
  have hmin1 : min (1 / 2 : ℝ) (m₀ / 4) ≤ 1 / 2 := min_le_left _ _
  have hmin2 : min (1 / 2 : ℝ) (m₀ / 4) ≤ m₀ / 4 := min_le_right _ _
  have hWg_half : ‖liftSymbol (ceG1 (airyZero 1)) (ceBeta1 * K₀ * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖ ≤ ceK / 2 := by
    refine hWg.trans ?_
    have h1 : Ce * K₀ ^ (-((4 : ℕ) : ℝ)) * c ^ (-(5 / 6 : ℝ)) ≤ Pn * (liftEps c * θ) := by
      rw [hc56]; gcongr
    have h2 : Pn * (liftEps c * θ) = ceK * min (1 / 2) (m₀ / 4) * liftEps c := by rw [hθdef]; field_simp
    have h3 : min (1 / 2 : ℝ) (m₀ / 4) * liftEps c ≤ 1 / 2 * (1 / 2) := mul_le_mul hmin1 hεK hε.le (by norm_num)
    calc _ ≤ Pn * (liftEps c * θ) := h1
      _ = ceK * (min (1 / 2 : ℝ) (m₀ / 4) * liftEps c) := by rw [h2]; ring
      _ ≤ ceK * (1 / 2 * (1 / 2)) := mul_le_mul_of_nonneg_left h3 hk.le
      _ ≤ ceK / 2 := by linarith
  have hgx : |(liftSymbol (ceG1 (airyZero 1)) (ceBeta1 * K₀ * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)).re| ≤ ceK / 2 :=
    (Complex.abs_re_le_norm _).trans hWg_half
  have hsmall : 2 / ceK * Qe ≤ K₀ * liftEps c := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hk]
    have h4 : ceK * min (1 / 2 : ℝ) (m₀ / 4) * liftEps c ≤ ceK * (1 / 2) * liftEps c :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin1 hk.le) hε.le
    have h5 : ceK * liftEps c ≤ ceK * (K₀ * liftEps c) := mul_le_mul_of_nonneg_left (by nlinarith) hk.le
    nlinarith
  obtain ⟨η₀, hη₀⟩ := ceTune_exists γ₁ γ₂ S hK0 hc0 (hS.hasU2 hc2000) (by rw [← hadef, ← hb₀def, ← hc₀'def]; exact hmassD)
    (by simpa using hgx) (by rw [← hadef, ← hb₀def, ← hc₀'def, ← hQedef]; exact hsmall)
  have hη := hetaF_tune ⟨η₀, hη₀⟩
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = etaF K₀ c := ⟨_, rfl⟩
  rw [← hηdef] at hη
  obtain ⟨hη1, hη2, hη3⟩ := hη
  rw [← hadef, ← hb₀def, ← hc₀'def, ← hQedef] at hη2
  rw [← hadef, ← hb₀def, ← hc₀'def] at hη3
  have hrη : |(K₀ * liftEps c - ∫ u : ℝ, S c u) - η| ≤ (2 + M₀) * (K₀ * liftEps c) := by
    rw [hηdef]; exact hr hK₀ hc2000
  -- the eigenfunction pair
  obtain ⟨fp, fm, hfp, hfm, hrp, -, h0p, h0m⟩ :=
    ceLift_pair (m := 4) (by norm_num) a (b₀ + η) c₀' hK₀ hc2000 hc8 (hS.tail hK₀ hc2000 hc8)
  have hfm0 : fm 0 = 0 := by
    have : ((fm 0 : ℝ) : ℂ) = 0 := by rw [h0m]; exact hη3
    exact_mod_cast this
  -- the origin value of `f₊`
  have hD2 := hasU2_airySeedU2 a (b₀ + η) c₀'
  have hSU := hS.hasU2 hc2000
  have hYU : HasU2 (fun u => airySeedU2 a (b₀ + η) c₀' u + 1 * S c u) := hD2.add (hSU.smul 1)
  have hint_eta : ∫ u : ℝ, airySeedU2 a (b₀ + η) c₀' u = (∫ u : ℝ, S c u) + η := by
    have h0 := (hseed (K₀ * liftEps c) ((K₀ * liftEps c - ∫ u : ℝ, S c u) - η) hKεpos hKεδ hrη).1
    rw [hDF η, integral_neg, h0]; ring
  have hW0 : liftSymbol (fun u => airySeedU2 a (b₀ + η) c₀' u + 1 * S c u) (ceBeta1 * K₀ * liftEps c / 2) 4 0 =
      ((ceK * ((∫ u : ℝ, S c u) + η + ∫ u : ℝ, S c u) : ℝ) : ℂ) := by
    have hi : ∫ u : ℝ, (airySeedU2 a (b₀ + η) c₀' u + 1 * S c u) = (∫ u : ℝ, S c u) + η + ∫ u : ℝ, S c u := by
      rw [integral_add (hasU2_integrable_real hD2) (hasU2_integrable_real (hSU.smul 1))]
      simp only [one_mul]; rw [hint_eta]
    rw [liftSymbol_zero_eq hYU, hi]
  have hxre : 0 ≤ ((((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)).re := by simpa using Real.rpow_nonneg hc0.le _
  have hWx : ‖liftSymbol (fun u => airySeedU2 a (b₀ + η) c₀' u + 1 * S c u) (ceBeta1 * K₀ * liftEps c / 2) 4
      (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖ ≤ 2 * Qe := by
    have hsplit : liftSymbol (fun u => airySeedU2 a (b₀ + η) c₀' u + 1 * S c u) (ceBeta1 * K₀ * liftEps c / 2) 4
        (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) =
        liftSymbol (airySeedU2 a b₀ c₀') (ceBeta1 * K₀ * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
        (η : ℂ) * liftSymbol (ceG1 (airyZero 1)) (ceBeta1 * K₀ * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
        ((1 : ℝ) : ℂ) * liftSymbol (S c) (ceBeta1 * K₀ * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) := by
      rw [liftSymbol_add_seed hD2 (hSU.smul 1) _ 4 hxre, liftSymbol_const_mul_seed, airySeedU2_add_b,
        liftSymbol_add_seed (hasU2_airySeedU2 a b₀ c₀') (hasU2_ceG1.smul η) _ 4 hxre, liftSymbol_const_mul_seed]
    rw [hsplit]
    have hηg : |η| * ‖liftSymbol (ceG1 (airyZero 1)) (ceBeta1 * K₀ * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖ ≤ Qe := by
      calc _ ≤ (2 / ceK * Qe) * (ceK / 2) := mul_le_mul hη2 hWg_half (norm_nonneg _) (by positivity)
        _ = Qe := by field_simp
    calc _ ≤ ‖liftSymbol (airySeedU2 a b₀ c₀') (ceBeta1 * K₀ * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
          (η : ℂ) * liftSymbol (ceG1 (airyZero 1)) (ceBeta1 * K₀ * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖ +
          ‖((1 : ℝ) : ℂ) * liftSymbol (S c) (ceBeta1 * K₀ * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖ := norm_add_le _ _
      _ ≤ (‖liftSymbol (airySeedU2 a b₀ c₀') (ceBeta1 * K₀ * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖ +
          ‖(η : ℂ) * liftSymbol (ceG1 (airyZero 1)) (ceBeta1 * K₀ * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖) +
          ‖((1 : ℝ) : ℂ) * liftSymbol (S c) (ceBeta1 * K₀ * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖ := by
        gcongr; exact norm_add_le _ _
      _ ≤ 2 * Qe := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_one, one_mul]
        rw [hQedef] at hηg ⊢
        linarith
  have hfp0 : 0 < fp 0 := by
    have hre := congrArg Complex.re h0p
    rw [Complex.ofReal_re, Complex.add_re, hW0, Complex.ofReal_re] at hre
    have h1 := neg_abs_le (liftSymbol (fun u => airySeedU2 a (b₀ + η) c₀' u + 1 * S c u) (ceBeta1 * K₀ * liftEps c / 2) 4
      (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)).re
    have h2 := (Complex.abs_re_le_norm (liftSymbol (fun u => airySeedU2 a (b₀ + η) c₀' u + 1 * S c u)
      (ceBeta1 * K₀ * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)))
    have hA : ceK * |η| ≤ 2 * Qe := by
      have := mul_le_mul_of_nonneg_left hη2 hk.le
      have e : ceK * (2 / ceK * Qe) = 2 * Qe := by field_simp
      linarith
    have hB : -(ceK * |η|) ≤ ceK * η := by
      have := mul_le_mul_of_nonneg_left (neg_abs_le η) hk.le
      linarith
    have hC : Qe ≤ ceK * (m₀ / 4) * liftEps c := by
      refine hQe_k.trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmin2 hk.le) hε.le
    have hD : ceK * (m₀ * liftEps c) ≤ ceK * ∫ u : ℝ, S c u := mul_le_mul_of_nonneg_left (hmass hc2000).1 hk.le
    have hpp : 0 < ceK * m₀ * liftEps c := by positivity
    nlinarith
  -- the threshold
  obtain ⟨smin, hsmin⟩ : ∃ s : ℝ, s = (|airyZero 1| + 2 * |γ₁| * (K₀ * liftEps c) + ceBeta1 * (K₀ * liftEps c) / 2) / ceBeta1 :=
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
  -- the sign beyond `T`
  have hsign : ∀ Δ : ℝ, T ≤ Δ → fp Δ + fm Δ ≤ 0 := by
    intro Δ hΔ
    have hΔ0 : 0 < Δ := hTpos0.trans_le hΔ
    obtain ⟨ξ, hξdef⟩ : ∃ ξ : ℝ, ξ = Δ / c := ⟨_, rfl⟩
    have hξ : 0 < ξ := by rw [hξdef]; positivity
    have hcξ : c * ξ = Δ := by rw [hξdef]; field_simp
    have hSm : (|airyZero 1| + 2 * |γ₁| * (K₀ * liftEps c) + ceBeta1 * (K₀ * liftEps c) / 2) / ceBeta1 ≤ hbS c ξ := by
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
    have hz := hpos (K := K₀) (c := c) (ξ := ξ) le_rfl hcc₀ hc8 hcδ hξ (by simpa using hSm)
    have hF' : airySeedU2 (-1 - γ₂ * (K₀ * liftEps c))
        (-γ₁ * (K₀ * liftEps c) + γ₂ * (K₀ * liftEps c) + ((K₀ * liftEps c - ∫ u : ℝ, S c u) - etaF K₀ c))
        (γ₂ * (K₀ * liftEps c)) = fun u => (-1 : ℝ) * airySeedU2 a (b₀ + η) c₀' u := by
      funext u
      have := congrFun (hDF η) u
      rw [← hηdef, this]; ring
    have hneg : (fun u => -S c u) = fun u => (-1 : ℝ) * S c u := by funext u; ring
    rw [hF', hneg, iMain_const_mul, iDual_const_mul] at hz
    have e := congrArg Complex.re (hrp ξ hξ)
    rw [Complex.ofReal_re, Complex.add_re, hcξ] at e
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at hz
    have h1 : 0 < c ^ (1 / 3 : ℝ) * hankelRho0 c Δ :=
      mul_pos (Real.rpow_pos_of_pos hc0 _) (hankelRho0_pos hc0 hΔ0)
    by_contra hcon
    push_neg at hcon
    have h2 := mul_pos h1 (show 0 < (fp Δ + fm Δ) / 2 by linarith)
    nlinarith
  refine ⟨fp, fm, T, hfp, hfm, hfm0, hfp0, ?_, hsign⟩
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
  have e3 : c ^ (1 / 3 : ℝ) * smin = |airyZero 1| / ceBeta1 * c ^ (1 / 3 : ℝ) + K₀ * (2 * |γ₁| + ceBeta1 / 2) / ceBeta1 := by
    rw [hsmin]; field_simp
    linear_combination (2 * (2 * |γ₁| * K₀ + ceBeta1 * K₀ / 2)) * hεc
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
        (K₀ * (2 * |γ₁| + ceBeta1 / 2) / ceBeta1 + 2 * Real.pi ^ 2 * s_max ^ 2) := by
      rw [e1, e2, e3, airyOrderCoeff, hβeq]
      linarith

/-- info: 'FormalResearch.SignUncertainty.ceLift_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceLift_physical

end FormalResearch.SignUncertainty
