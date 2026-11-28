module

public import FormalResearch.SignUncertainty.CePostEdge
public import FormalResearch.SignUncertainty.ConvSourceLaplace
public import FormalResearch.SignUncertainty.UctPosFloorWpos

/-!
# Pre-edge convolution source bounds (`ceo:conv` (6))

* `convSource_preEdge_bounds`: for `p ∈ (1/2, 1)`, `γ > 0`, `0 ≤ θ`, `0 < λ`, `1 ≤ m`, `1 ≤ K`,
  the convolution source multiplier
  `W_S(w) = liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) m w`
  satisfies:
  - holomorphy on `{Re w > 0}` and real positivity `0 < (W_S x).re`, `(W_S x).im = 0` on `(0, ∞)`;
  - uniform half-plane bound `‖W_S w‖ ≤ C_S * liftEps c * (1 + w.re) ^ (-(9 / 2 : ℝ))` (`Re w ≥ 0`);
  - uniform vertical ratio `‖W_S (x + i y)‖ ≤ Λ_S * (W_S x).re` for `0 < x ≤ c^{1/3}`;
  - uniform Cauchy variation `‖W_S (x + i y) - W_S x‖ ≤ 4 * M_S * (|y| / x) * (W_S x).re` for
    `0 < x ≤ c^{1/3}`, `|y| ≤ x / 4`, with constants independent of `K ≥ 1` and `c ≥ max 8 (8 * K ^ 3)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

private lemma exp_half_factor_le {t : ℝ} (_ht : 0 ≤ t) :
    (1 + t) * Real.exp (-(t / 2)) ≤ 2 := by
  have hexp : 1 + t / 2 ≤ Real.exp (t / 2) := by linarith [Real.add_one_le_exp (t / 2)]
  have hexp_pos : 0 < Real.exp (t / 2) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hexp_pos]
  nlinarith

private lemma integral_gamma_eps_exp (γ ε s : ℝ) (hs : 0 ≤ s) :
    IntegrableOn (fun y : ℝ => (γ * ε * Real.exp (-y) : ℝ) * Real.exp (-s * y)) (Ioi 0) ∧
      ∫ y in Ioi (0 : ℝ), (γ * ε * Real.exp (-y) : ℝ) * Real.exp (-s * y) = γ * ε / (1 + s) := by
  have h1s : 0 < 1 + s := by linarith
  have heq : EqOn (fun y : ℝ => γ * ε * Real.exp (-(1 + s) * y))
      (fun y : ℝ => (γ * ε * Real.exp (-y) : ℝ) * Real.exp (-s * y)) (Ioi 0) := fun y _ => by
    dsimp only
    rw [show -(1 + s) * y = -y + -s * y by ring, Real.exp_add, ← mul_assoc]
  have hint0 := integral_exp_neg_lin_Ioi (a := (0 : ℝ)) h1s
  rw [neg_mul, mul_zero, neg_zero, Real.exp_zero] at hint0
  have hint : IntegrableOn (fun y : ℝ => (γ * ε * Real.exp (-y) : ℝ) * Real.exp (-s * y)) (Ioi 0) :=
    IntegrableOn.congr_fun (hint0.1.const_mul (γ * ε)) heq measurableSet_Ioi
  refine ⟨hint, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul, hint0.2]
  ring

private lemma lapW_convWc_re_bounds {p γ θ lam ε x : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1)
    (hγ : 0 < γ) (hθ : 0 ≤ θ) (hlam : 0 < lam) (hε : 0 < ε) (hx : 0 ≤ x) :
    let h := lam * ε ^ 2
    let w := convWc p γ θ ε h
    let A := 2 + 1 / (p - 1 / 2)
    γ * ε / (1 + x) ≤ (lapW w (x : ℂ)).re ∧
      (lapW w (x : ℂ)).re ≤ (γ + 2 * θ * A * Real.sqrt lam) * ε / (1 + x) ∧
      (∀ z : ℂ, x / 2 ≤ z.re →
        ‖lapW w z‖ ≤ (2 * γ + 2 * θ * A * Real.sqrt lam) * ε / (1 + x)) := by
  dsimp only
  set h : ℝ := lam * ε ^ 2
  set w : ℝ → ℝ := convWc p γ θ ε h
  set A : ℝ := 2 + 1 / (p - 1 / 2)
  have hA0 : 0 < A := by have : 0 < 1 / (p - 1 / 2) := one_div_pos.mpr (by linarith); positivity
  have hh : 0 < h := by positivity
  have hw_int : IntegrableOn w (Ioi 0) := convWc_integrableOn hp hp1 hh
  have hre_z : ∀ s : ℝ, 0 ≤ s →
      (lapW w (s : ℂ)).re = ∫ y in Ioi (0 : ℝ), w y * Real.exp (-s * y) := fun s _ => by
    unfold lapW
    have hcongr : EqOn (fun y : ℝ => (w y : ℂ) * Complex.exp (-((s : ℂ) * (y : ℂ))))
        (fun y : ℝ => ((w y * Real.exp (-s * y) : ℝ) : ℂ)) (Ioi 0) := fun y _ => by
      dsimp only
      calc (w y : ℂ) * Complex.exp (-((s : ℂ) * (y : ℂ)))
          = (w y : ℂ) * Complex.exp (((-s * y : ℝ) : ℂ)) := by congr 2; push_cast; ring
        _ = ((w y * Real.exp (-s * y) : ℝ) : ℂ) := by rw [← Complex.ofReal_exp, ← Complex.ofReal_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_complex_ofReal, Complex.ofReal_re]
  have hwh_int : IntegrableOn (convWh p h) (Ioi 0) := convW_integrable hp hp1 hh
  have hwh_L1 : ∫ y in Ioi (0 : ℝ), convWh p h y ≤ A * Real.sqrt lam * ε := by
    have hL := convW_L1_le hp hp1 hh
    have hsq : Real.sqrt h = Real.sqrt lam * ε := by
      dsimp [h]; rw [Real.sqrt_mul hlam.le, Real.sqrt_sq hε.le]
    rw [hsq] at hL; linarith [hL]
  have hsplit : ∀ {s : ℝ}, 0 ≤ s →
      IntegrableOn (fun y : ℝ => (γ * ε * Real.exp (-y) : ℝ) * Real.exp (-s * y)) (Ioi 0) ∧
      IntegrableOn (fun y : ℝ => (θ * convWh p h y : ℝ) * Real.exp (-s * y)) (Ioi 0) ∧
      (lapW w (s : ℂ)).re =
        (∫ y in Ioi (0 : ℝ), (γ * ε * Real.exp (-y) : ℝ) * Real.exp (-s * y)) +
        (∫ y in Ioi (0 : ℝ), (θ * convWh p h y : ℝ) * Real.exp (-s * y)) ∧
      0 ≤ ∫ y in Ioi (0 : ℝ), (θ * convWh p h y : ℝ) * Real.exp (-s * y) ∧
      ∫ y in Ioi (0 : ℝ), (θ * convWh p h y : ℝ) * Real.exp (-s * y) ≤
        θ * Real.exp (-s) * (A * Real.sqrt lam * ε) := by
    intro s hs
    have hg := integral_gamma_eps_exp γ ε s hs
    have hwh_s : IntegrableOn (fun y : ℝ => (θ * convWh p h y : ℝ) * Real.exp (-s * y)) (Ioi 0) := by
      refine (hwh_int.const_mul θ).mono' ((hwh_int.1.const_mul θ).mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy0 : 0 < y := hy
      have hwh_nn : 0 ≤ convWh p h y := convWh_nonneg hh.le hy0
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hθ hwh_nn) (Real.exp_pos _).le)]
      exact mul_le_of_le_one_right (mul_nonneg hθ hwh_nn) (Real.exp_le_one_iff.mpr (by nlinarith))
    have hsum_eq : (lapW w (s : ℂ)).re =
        (∫ y in Ioi (0 : ℝ), (γ * ε * Real.exp (-y) : ℝ) * Real.exp (-s * y)) +
        (∫ y in Ioi (0 : ℝ), (θ * convWh p h y : ℝ) * Real.exp (-s * y)) := by
      rw [hre_z s hs]
      have hsub : ∫ y in Ioi (0 : ℝ), w y * Real.exp (-s * y) =
          ∫ y in Ioi (0 : ℝ), ((γ * ε * Real.exp (-y)) * Real.exp (-s * y) + (θ * convWh p h y) * Real.exp (-s * y)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
        dsimp only [w, convWc]; ring
      rw [hsub]
      exact MeasureTheory.integral_add hg.1 hwh_s
    have hnn : 0 ≤ ∫ y in Ioi (0 : ℝ), (θ * convWh p h y : ℝ) * Real.exp (-s * y) :=
      setIntegral_nonneg measurableSet_Ioi fun y hy =>
        mul_nonneg (mul_nonneg hθ (convWh_nonneg hh.le hy)) (Real.exp_pos _).le
    have hle_wh : ∫ y in Ioi (0 : ℝ), (θ * convWh p h y : ℝ) * Real.exp (-s * y) ≤
        θ * Real.exp (-s) * (A * Real.sqrt lam * ε) := by
      have hpt : ∀ y ∈ Ioi (0 : ℝ), (θ * convWh p h y : ℝ) * Real.exp (-s * y) ≤
          (θ * Real.exp (-s)) * convWh p h y := fun y hy => by
        rcases le_or_gt y 1 with hy1 | hy1
        · rw [convWh_eq_zero hy1]; simp
        · have hexp : Real.exp (-s * y) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by nlinarith)
          calc (θ * convWh p h y) * Real.exp (-s * y) ≤ (θ * convWh p h y) * Real.exp (-s) :=
                mul_le_mul_of_nonneg_left hexp (mul_nonneg hθ (convWh_nonneg hh.le hy))
            _ = (θ * Real.exp (-s)) * convWh p h y := by ring
      have hmono := setIntegral_mono_on hwh_s (hwh_int.const_mul (θ * Real.exp (-s))) measurableSet_Ioi hpt
      rw [integral_const_mul] at hmono
      exact hmono.trans (mul_le_mul_of_nonneg_left hwh_L1 (mul_nonneg hθ (Real.exp_pos _).le))
    exact ⟨hg.1, hwh_s, hsum_eq, hnn, hle_wh⟩
  have h1 := hsplit hx
  have h1g := integral_gamma_eps_exp γ ε x hx
  have hx2 : 0 ≤ x / 2 := by linarith
  have h2 := hsplit hx2
  have h2g := integral_gamma_eps_exp γ ε (x / 2) hx2
  have hlow : γ * ε / (1 + x) ≤ (lapW w (x : ℂ)).re := by
    rw [h1.2.2.1, h1g.2]; linarith [h1.2.2.2.1]
  have hexp_x : Real.exp (-x) ≤ 2 / (1 + x) := by
    rw [le_div_iff₀ (by linarith)]
    calc Real.exp (-x) * (1 + x) ≤ Real.exp (-(x / 2)) * (1 + x) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by linarith)
      _ = (1 + x) * Real.exp (-(x / 2)) := by ring
      _ ≤ 2 := exp_half_factor_le hx
  have hexp_x2 : Real.exp (-(x / 2)) ≤ 2 / (1 + x) := by
    rw [le_div_iff₀ (by linarith), mul_comm]
    exact exp_half_factor_le hx
  have hup_x : (lapW w (x : ℂ)).re ≤ (γ + 2 * θ * A * Real.sqrt lam) * ε / (1 + x) := by
    rw [h1.2.2.1, h1g.2]
    have hwh' : θ * Real.exp (-x) * (A * Real.sqrt lam * ε) ≤ 2 * θ * A * Real.sqrt lam * ε / (1 + x) := by
      have := mul_le_mul_of_nonneg_left hexp_x (by positivity : 0 ≤ θ * (A * Real.sqrt lam * ε))
      calc θ * Real.exp (-x) * (A * Real.sqrt lam * ε)
          = θ * (A * Real.sqrt lam * ε) * Real.exp (-x) := by ring
        _ ≤ θ * (A * Real.sqrt lam * ε) * (2 / (1 + x)) := this
        _ = 2 * θ * A * Real.sqrt lam * ε / (1 + x) := by ring
    have := h1.2.2.2.2.trans hwh'
    linarith [show (γ + 2 * θ * A * Real.sqrt lam) * ε / (1 + x) =
      γ * ε / (1 + x) + 2 * θ * A * Real.sqrt lam * ε / (1 + x) by ring]
  refine ⟨hlow, hup_x, fun z hz => ?_⟩
  have hz0 : 0 ≤ z.re := le_trans hx2 hz
  have h_re_int : ∀ {s : ℝ}, 0 ≤ s → IntegrableOn (fun y : ℝ => w y * Real.exp (-s * y)) (Ioi 0) := fun {s} hs => by
    refine hw_int.mono' (hw_int.1.mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hw0 : 0 ≤ w y := convWc_nonneg hγ.le hθ hε.le hh.le hy
    rw [Real.norm_of_nonneg (mul_nonneg hw0 (Real.exp_pos _).le)]
    exact mul_le_of_le_one_right hw0 (Real.exp_le_one_iff.mpr (by nlinarith [hs, mem_Ioi.mp hy]))
  have hnorm_z : ‖lapW w z‖ ≤ (lapW w (z.re : ℂ)).re := by
    rw [hre_z z.re hz0]
    unfold lapW
    refine norm_integral_le_of_norm_le (h_re_int hz0) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hw0 : 0 ≤ w y := convWc_nonneg hγ.le hθ hε.le hh.le hy
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0, Complex.norm_exp,
      show (-(z * (y : ℂ))).re = -(z.re * y) by simp [Complex.mul_re]]
    ring_nf; rfl
  have hre_mono : (lapW w (z.re : ℂ)).re ≤ (lapW w ((x / 2 : ℝ) : ℂ)).re := by
    rw [hre_z z.re hz0, hre_z (x / 2) hx2]
    refine setIntegral_mono_on (h_re_int hz0) (h_re_int hx2) measurableSet_Ioi fun y hy => ?_
    have hw0 : 0 ≤ w y := convWc_nonneg hγ.le hθ hε.le hh.le hy
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [hz, mem_Ioi.mp hy])) hw0
  have hup_x2 : (lapW w ((x / 2 : ℝ) : ℂ)).re ≤ (2 * γ + 2 * θ * A * Real.sqrt lam) * ε / (1 + x) := by
    rw [h2.2.2.1, h2g.2]
    have hg2 : γ * ε / (1 + x / 2) ≤ 2 * γ * ε / (1 + x) := by
      have hden : 1 + x ≤ 2 * (1 + x / 2) := by linarith
      calc γ * ε / (1 + x / 2) = 2 * γ * ε / (2 * (1 + x / 2)) := by field_simp
        _ ≤ 2 * γ * ε / (1 + x) := div_le_div_of_nonneg_left (by positivity) (by linarith) hden
    have hwh' : θ * Real.exp (-(x / 2)) * (A * Real.sqrt lam * ε) ≤ 2 * θ * A * Real.sqrt lam * ε / (1 + x) := by
      have := mul_le_mul_of_nonneg_left hexp_x2 (by positivity : 0 ≤ θ * (A * Real.sqrt lam * ε))
      calc θ * Real.exp (-(x / 2)) * (A * Real.sqrt lam * ε)
          = θ * (A * Real.sqrt lam * ε) * Real.exp (-(x / 2)) := by ring
        _ ≤ θ * (A * Real.sqrt lam * ε) * (2 / (1 + x)) := this
        _ = 2 * θ * A * Real.sqrt lam * ε / (1 + x) := by ring
    have := h2.2.2.2.2.trans hwh'
    linarith [show (2 * γ + 2 * θ * A * Real.sqrt lam) * ε / (1 + x) =
      2 * γ * ε / (1 + x) + 2 * θ * A * Real.sqrt lam * ε / (1 + x) by ring]
  exact hnorm_z.trans (hre_mono.trans hup_x2)

/-- **`ceo:conv` (6):** uniform pre-edge real positivity, vertical ratio bound, Cauchy variation bound,
and half-plane bound for `W_{S_c^{(0)}}(w) = liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) m w`. -/
theorem convSource_preEdge_bounds {p γ θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1)
    (hγ : 0 < γ) (hθ : 0 ≤ θ) (hlam : 0 < lam) {m : ℕ} (hm : 1 ≤ m) {K : ℝ} (hK : 1 ≤ K) :
    let W_S : ℝ → ℂ → ℂ := fun c w =>
      liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) m w
    ∃ C_S M_S Λ_S : ℝ, 0 < C_S ∧ 1 ≤ M_S ∧ 1 ≤ Λ_S ∧
      (∀ {c : ℝ}, max 8 (8 * K ^ 3) ≤ c → DifferentiableOn ℂ (W_S c) {w : ℂ | 0 < w.re}) ∧
      (∀ {c x : ℝ}, max 8 (8 * K ^ 3) ≤ c → 0 < x → (W_S c (x : ℂ)).im = 0 ∧ 0 < (W_S c (x : ℂ)).re) ∧
      (∀ {c : ℝ} {w : ℂ}, max 8 (8 * K ^ 3) ≤ c → 0 ≤ w.re → ‖W_S c w‖ ≤ C_S * liftEps c * (1 + w.re) ^ (-(9 / 2 : ℝ))) ∧
      (∀ {c x y : ℝ}, max 8 (8 * K ^ 3) ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → |y| ≤ x / 4 →
        ‖W_S c ((x : ℂ) + (y : ℂ) * Complex.I) - W_S c (x : ℂ)‖ ≤ 4 * M_S * (|y| / x) * (W_S c (x : ℂ)).re) ∧
      (∀ {c x y : ℝ}, max 8 (8 * K ^ 3) ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) →
        ‖W_S c ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Λ_S * (W_S c (x : ℂ)).re) := by
  dsimp only
  obtain ⟨bg, Cg, hbg, _, hG_bd, hG_low⟩ := ceG1_twisted_bounds
  set A : ℝ := 2 + 1 / (p - 1 / 2)
  have hA0 : 0 < A := by have : 0 < 1 / (p - 1 / 2) := one_div_pos.mpr (by linarith); positivity
  have hcs0 : 0 < ceCs := ceCs_pos
  have hβ0 : 0 < ceBeta1 := ceBeta1_pos
  let R_lap : ℝ := (2 * γ + 2 * θ * A * Real.sqrt lam) / γ
  have hR_lap : 1 ≤ R_lap := by
    rw [one_le_div hγ]
    have : 0 ≤ θ * A * Real.sqrt lam := by positivity
    linarith
  let Λ_loc : ℝ := max 1 ((2 : ℝ) ^ m * (2 ^ (9 / 2 : ℝ) * (Cg / bg)) * R_lap)
  have hΛ_loc : 1 ≤ Λ_loc := le_max_left _ _
  let C_S : ℝ := (γ + 2 * θ * A * Real.sqrt lam) * Cg + 1
  have hC_S : 0 < C_S := by
    dsimp [C_S]
    have h1 : 0 ≤ (γ + 2 * θ * A * Real.sqrt lam) * Cg := mul_nonneg (by positivity) (by linarith [hbg])
    linarith
  have hdiff : ∀ {c : ℝ}, max 8 (8 * K ^ 3) ≤ c →
      DifferentiableOn ℂ (fun w => liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) m w) {w : ℂ | 0 < w.re} := by
    intro c hc
    have hc0 : 0 < c := by linarith [(le_max_left 8 (8 * K ^ 3)).trans hc]
    have hh : 0 < lam * liftEps c ^ 2 := by have := liftEps_pos hc0; positivity
    exact liftSymbol_differentiableOn (hasU2_convSource hp hp1 hh) _ m
  have hreal_form : ∀ {c x : ℝ}, max 8 (8 * K ^ 3) ≤ c → 0 < x →
      (liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).im = 0 ∧
      (liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re =
        uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x) ^ m *
          (lapW (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2)) ((ceCs : ℂ) * (x : ℂ))).re *
          airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * x) ∧
      0 < (liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re := by
    intro c x hc hx
    have hc0 : 0 < c := by linarith [(le_max_left 8 (8 * K ^ 3)).trans hc]
    have hε : 0 < liftEps c := liftEps_pos hc0
    have hh : 0 < lam * liftEps c ^ 2 := by positivity
    have him := liftSymbol_im_eq_zero_of_real (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) m x
    have hre0 : 0 ≤ ((ceCs : ℂ) * (x : ℂ)).re := by simp; exact mul_nonneg hcs0.le hx.le
    have hprod := airyTwistedLaplaceC_convR (w := convWc p γ θ (liftEps c) (lam * liftEps c ^ 2))
      (convWc_integrableOn (γ := γ) (θ := θ) (ε := liftEps c) hp hp1 hh) (continuous_ceG1 _) hasU2_ceG1 hre0
    have hlap := lapW_convWc_re_bounds hp hp1 hγ hθ hlam hε (mul_nonneg hcs0.le hx.le)
    have hmult_re : liftMultiplier (ceBeta1 * K * liftEps c / 2) m (x : ℂ) =
        ((uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x) ^ m : ℝ) : ℂ) := by
      unfold liftMultiplier
      rw [show (((ceCs * (ceBeta1 * K * liftEps c / 2) / m : ℝ) : ℂ) * (x : ℂ)) =
        ((ceCs * (ceBeta1 * K * liftEps c / 2) / m * x : ℝ) : ℂ) by push_cast; ring, uctE1r_cast, ← Complex.ofReal_pow]
    have hW_eq : (liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re =
        uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x) ^ m *
          (lapW (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2)) ((ceCs : ℂ) * (x : ℂ))).re *
          airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * x) := by
      unfold liftSymbol convSourceFamily
      rw [convSource_eq_convR, hprod, hmult_re, ← mul_assoc,
        show ((ceCs : ℂ) * (x : ℂ)) = ((ceCs * x : ℝ) : ℂ) by push_cast; ring,
        airyTwistedLaplaceC_ofReal, Complex.mul_re, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul]
    have hm_pos : 0 < uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x) ^ m :=
      pow_pos (uctE1r_pos _) m
    have hg_pos : 0 < airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * x) :=
      lt_of_lt_of_le (by positivity) (hG_low (ceCs * x) (mul_nonneg hcs0.le hx.le))
    have hl_pos : 0 < (lapW (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2)) ((ceCs : ℂ) * (x : ℂ))).re := by
      rw [show ((ceCs : ℂ) * (x : ℂ)) = ((ceCs * x : ℝ) : ℂ) by push_cast; ring]
      exact lt_of_lt_of_le (by positivity) hlap.1
    exact ⟨him, hW_eq, by rw [hW_eq]; exact mul_pos (mul_pos hm_pos hl_pos) hg_pos⟩
  have hre_half : ∀ {c x : ℝ} {z : ℂ}, max 8 (8 * K ^ 3) ≤ c → 0 < x → x / 2 ≤ z.re →
      ‖liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) m z‖ ≤
        Λ_loc * (liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re := by
    intro c x z hc hx hzx
    have hc0 : 0 < c := by linarith [(le_max_left 8 (8 * K ^ 3)).trans hc]
    have hε : 0 < liftEps c := liftEps_pos hc0
    have hh : 0 < lam * liftEps c ^ 2 := by positivity
    have hz0 : 0 ≤ z.re := by linarith
    have hre_z : 0 ≤ ((ceCs : ℂ) * z).re := by rw [Complex.re_ofReal_mul]; exact mul_nonneg hcs0.le hz0
    have hre_x : 0 ≤ ceCs * x := mul_nonneg hcs0.le hx.le
    have hprod_z := airyTwistedLaplaceC_convR (w := convWc p γ θ (liftEps c) (lam * liftEps c ^ 2))
      (convWc_integrableOn (γ := γ) (θ := θ) (ε := liftEps c) hp hp1 hh) (continuous_ceG1 _) hasU2_ceG1 hre_z
    have hlap := lapW_convWc_re_bounds hp hp1 hγ hθ hlam hε hre_x
    have hlap_z := hlap.2.2 ((ceCs : ℂ) * z) (by rw [Complex.re_ofReal_mul]; nlinarith [hcs0, hzx])
    have hlap_ratio : ‖lapW (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2)) ((ceCs : ℂ) * z)‖ ≤
        R_lap * (lapW (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2)) ((ceCs : ℂ) * (x : ℂ))).re := by
      refine hlap_z.trans ?_
      have hmul := mul_le_mul_of_nonneg_left hlap.1 (by linarith [hR_lap] : 0 ≤ R_lap)
      rw [show (ceCs : ℂ) * (x : ℂ) = ((ceCs * x : ℝ) : ℂ) by push_cast; ring]
      calc (2 * γ + 2 * θ * A * Real.sqrt lam) * liftEps c / (1 + ceCs * x)
          = R_lap * (γ * liftEps c / (1 + ceCs * x)) := by dsimp [R_lap]; field_simp [hγ.ne']
        _ ≤ R_lap * (lapW (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2)) ((ceCs * x : ℝ) : ℂ)).re := hmul
    have hG_ratio : ‖airyTwistedLaplaceC (ceG1 (airyZero 1)) ((ceCs : ℂ) * z)‖ ≤
        2 ^ (9 / 2 : ℝ) * (Cg / bg) * airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * x) := by
      have h1 := hG_bd ((ceCs : ℂ) * z) hre_z
      have h2 := hG_low (ceCs * x) hre_x
      have hden : 1 + ceCs * x ≤ 2 * (1 + ((ceCs : ℂ) * z).re) := by
        rw [Complex.re_ofReal_mul]; nlinarith [hcs0, hzx]
      have hp_neg : (2 * (1 + ((ceCs : ℂ) * z).re)) ^ (-(9 / 2 : ℝ)) ≤ (1 + ceCs * x) ^ (-(9 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hden (by norm_num)
      rw [Real.mul_rpow zero_le_two (by rw [Complex.re_ofReal_mul]; nlinarith [hcs0, hz0]),
        Real.rpow_neg zero_le_two] at hp_neg
      have hpow : (1 + ((ceCs : ℂ) * z).re) ^ (-(9 / 2 : ℝ)) ≤ 2 ^ (9 / 2 : ℝ) * (1 + ceCs * x) ^ (-(9 / 2 : ℝ)) := by
        have hmul := mul_le_mul_of_nonneg_left hp_neg (by positivity : (0 : ℝ) ≤ 2 ^ (9 / 2 : ℝ))
        have h2inv : (2 : ℝ) ^ (9 / 2 : ℝ) * ((2 : ℝ) ^ (9 / 2 : ℝ))⁻¹ = 1 :=
          mul_inv_cancel₀ (by positivity)
        calc (1 + ((ceCs : ℂ) * z).re) ^ (-(9 / 2 : ℝ))
            = (2 : ℝ) ^ (9 / 2 : ℝ) * (((2 : ℝ) ^ (9 / 2 : ℝ))⁻¹ * (1 + ((ceCs : ℂ) * z).re) ^ (-(9 / 2 : ℝ))) := by
              rw [← mul_assoc, h2inv, one_mul]
          _ ≤ 2 ^ (9 / 2 : ℝ) * (1 + ceCs * x) ^ (-(9 / 2 : ℝ)) := hmul
      have hCg0 : 0 ≤ Cg := by linarith
      calc ‖airyTwistedLaplaceC (ceG1 (airyZero 1)) ((ceCs : ℂ) * z)‖
          ≤ Cg * (2 ^ (9 / 2 : ℝ) * (1 + ceCs * x) ^ (-(9 / 2 : ℝ))) :=
            h1.trans (mul_le_mul_of_nonneg_left hpow hCg0)
        _ = 2 ^ (9 / 2 : ℝ) * (Cg / bg) * (bg * (1 + ceCs * x) ^ (-(9 / 2 : ℝ))) := by field_simp [hbg.ne']
        _ ≤ 2 ^ (9 / 2 : ℝ) * (Cg / bg) * airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * x) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
    have hmult_ratio : ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m z‖ ≤
        (2 : ℝ) ^ m * uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x) ^ m := by
      have ha_pos : 0 < ceCs * (ceBeta1 * K * liftEps c / 2) / m * x := by positivity
      have h1 := norm_liftMultiplier_le_pow (ceBeta1 * K * liftEps c / 2) m z
      have h2 : uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * z.re) ≤
          uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x / 2) :=
        uctE1r_anti (by nlinarith [show 0 ≤ ceCs * (ceBeta1 * K * liftEps c / 2) / (m : ℝ) by positivity])
      have h3 : uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x / 2) ≤
          2 * uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x) := uctE1r_half ha_pos
      calc ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m z‖
          ≤ uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * z.re) ^ m := h1
        _ ≤ (2 * uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x)) ^ m :=
            pow_le_pow_left₀ (uctE1r_pos _).le (h2.trans h3) m
        _ = (2 : ℝ) ^ m * uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x) ^ m := by ring
    have hrf := (hreal_form hc hx).2.1
    have hlap_x_nn : 0 ≤ (lapW (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2)) ((ceCs : ℂ) * (x : ℂ))).re :=
      (hlap.1.trans' (by positivity)).trans_eq (by rw [show (ceCs : ℂ) * (x : ℂ) = ((ceCs * x : ℝ) : ℂ) by push_cast; ring])
    have hg_x_nn : 0 ≤ airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * x) :=
      (by positivity : 0 ≤ bg * (1 + ceCs * x) ^ (-(9 / 2 : ℝ))).trans (hG_low (ceCs * x) hre_x)
    unfold liftSymbol convSourceFamily
    rw [convSource_eq_convR, norm_mul, hprod_z, norm_mul]
    have hCg0 : 0 ≤ Cg := by linarith
    calc ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m z‖ *
          (‖lapW (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2)) ((ceCs : ℂ) * z)‖ *
            ‖airyTwistedLaplaceC (ceG1 (airyZero 1)) ((ceCs : ℂ) * z)‖)
        ≤ ((2 : ℝ) ^ m * uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x) ^ m) *
          ((R_lap * (lapW (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2)) ((ceCs : ℂ) * (x : ℂ))).re) *
            (2 ^ (9 / 2 : ℝ) * (Cg / bg) * airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * x))) :=
          mul_le_mul hmult_ratio
            (mul_le_mul hlap_ratio hG_ratio (norm_nonneg _) (mul_nonneg (by linarith [hR_lap]) hlap_x_nn))
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            (mul_nonneg (by positivity) (pow_nonneg (uctE1r_pos _).le m))
      _ = ((2 : ℝ) ^ m * (2 ^ (9 / 2 : ℝ) * (Cg / bg)) * R_lap) *
            (uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x) ^ m *
              (lapW (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2)) ((ceCs : ℂ) * (x : ℂ))).re *
              airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * x)) := by ring
      _ ≤ Λ_loc * (liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re := by
          have hpos_x : 0 ≤ (liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re :=
            (hreal_form hc hx).2.2.le
          rw [hrf] at hpos_x
          calc ((2 : ℝ) ^ m * (2 ^ (9 / 2 : ℝ) * (Cg / bg)) * R_lap) *
                (uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x) ^ m *
                  (lapW (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2)) ((ceCs : ℂ) * (x : ℂ))).re *
                  airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * x))
              ≤ Λ_loc * (uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x) ^ m *
                  (lapW (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2)) ((ceCs : ℂ) * (x : ℂ))).re *
                  airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * x)) :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) hpos_x
            _ = Λ_loc * (liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re := by
                rw [← hrf]
  refine ⟨C_S, Λ_loc, Λ_loc, hC_S, hΛ_loc, hΛ_loc, hdiff, ?_, ?_, ?_, ?_⟩
  · intro c x hc hx
    exact ⟨(hreal_form hc hx).1, (hreal_form hc hx).2.2⟩
  · intro c w hc hw
    have hc0 : 0 < c := by linarith [(le_max_left 8 (8 * K ^ 3)).trans hc]
    have hε : 0 < liftEps c := liftEps_pos hc0
    have hh : 0 < lam * liftEps c ^ 2 := by positivity
    have hδ0 : 0 ≤ ceBeta1 * K * liftEps c / 2 := by positivity
    have hre0 : 0 ≤ ((ceCs : ℂ) * w).re := by
      rw [Complex.re_ofReal_mul]; exact mul_nonneg hcs0.le hw
    have hprod := airyTwistedLaplaceC_convR (w := convWc p γ θ (liftEps c) (lam * liftEps c ^ 2))
      (convWc_integrableOn (γ := γ) (θ := θ) (ε := liftEps c) hp hp1 hh) (continuous_ceG1 _) hasU2_ceG1 hre0
    have hlap := lapW_convWc_re_bounds hp hp1 hγ hθ hlam hε (x := ceCs * w.re) (mul_nonneg hcs0.le hw)
    have hlap_le : ‖lapW (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2)) ((ceCs : ℂ) * w)‖ ≤
        (γ + 2 * θ * A * Real.sqrt lam) * liftEps c := by
      have hw_int := convWc_integrableOn (γ := γ) (θ := θ) (ε := liftEps c) hp hp1 hh
      have hre_z : (lapW (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2)) ((ceCs : ℂ) * (w.re : ℂ))).re ≤
          (γ + 2 * θ * A * Real.sqrt lam) * liftEps c / (1 + ceCs * w.re) := by
        simpa [Complex.ofReal_mul, A] using hlap.2.1
      have hnorm_z : ‖lapW (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2)) ((ceCs : ℂ) * w)‖ ≤
          (lapW (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2)) ((ceCs : ℂ) * (w.re : ℂ))).re := by
        have hcongr : (lapW (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2)) ((ceCs : ℂ) * (w.re : ℂ))).re =
            ∫ y in Ioi (0 : ℝ), convWc p γ θ (liftEps c) (lam * liftEps c ^ 2) y * Real.exp (-(ceCs * w.re) * y) := by
          unfold lapW
          have hc1 : EqOn (fun y : ℝ => (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2) y : ℂ) *
                Complex.exp (-((ceCs : ℂ) * (w.re : ℂ) * (y : ℂ))))
              (fun y : ℝ => ((convWc p γ θ (liftEps c) (lam * liftEps c ^ 2) y *
                Real.exp (-(ceCs * w.re) * y) : ℝ) : ℂ)) (Ioi 0) := fun y _ => by
            dsimp only
            calc (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2) y : ℂ) * Complex.exp (-((ceCs : ℂ) * (w.re : ℂ) * (y : ℂ)))
                = (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2) y : ℂ) * Complex.exp (((-(ceCs * w.re) * y : ℝ) : ℂ)) := by
                  congr 2; push_cast; ring
              _ = ((convWc p γ θ (liftEps c) (lam * liftEps c ^ 2) y * Real.exp (-(ceCs * w.re) * y) : ℝ) : ℂ) := by
                  rw [← Complex.ofReal_exp, ← Complex.ofReal_mul]
          rw [setIntegral_congr_fun measurableSet_Ioi hc1, integral_complex_ofReal, Complex.ofReal_re]
        rw [hcongr]
        unfold lapW
        have hint_dom : IntegrableOn (fun y : ℝ => convWc p γ θ (liftEps c) (lam * liftEps c ^ 2) y *
            Real.exp (-(ceCs * w.re) * y)) (Ioi 0) := by
          refine hw_int.mono' (hw_int.1.mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
          have hw0 : 0 ≤ convWc p γ θ (liftEps c) (lam * liftEps c ^ 2) y :=
            convWc_nonneg hγ.le hθ hε.le hh.le hy
          rw [Real.norm_of_nonneg (mul_nonneg hw0 (Real.exp_pos _).le)]
          exact mul_le_of_le_one_right hw0 (Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hcs0.le hw, mem_Ioi.mp hy]))
        refine norm_integral_le_of_norm_le hint_dom ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        have hw0 : 0 ≤ convWc p γ θ (liftEps c) (lam * liftEps c ^ 2) y :=
          convWc_nonneg hγ.le hθ hε.le hh.le hy
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0, Complex.norm_exp,
          show (-((ceCs : ℂ) * w * (y : ℂ))).re = -(ceCs * w.re) * y by simp [Complex.mul_re]]
      refine hnorm_z.trans (hre_z.trans ?_)
      have hAnn : 0 ≤ A := hA0.le
      exact div_le_self (by positivity) (by linarith [mul_nonneg hcs0.le hw])
    have hG := hG_bd ((ceCs : ℂ) * w) hre0
    have hCg0 : 0 ≤ Cg := by linarith
    have hG_w : Cg * (1 + ((ceCs : ℂ) * w).re) ^ (-(9 / 2 : ℝ)) ≤ Cg * (1 + w.re) ^ (-(9 / 2 : ℝ)) := by
      have hcs1 : 1 ≤ ceCs := convEdge_one_le_ceCs
      have h1 : 1 + w.re ≤ 1 + ((ceCs : ℂ) * w).re := by
        rw [Complex.re_ofReal_mul]; nlinarith
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by linarith) h1 (by norm_num)) hCg0
    unfold liftSymbol convSourceFamily
    rw [convSource_eq_convR, norm_mul, hprod, norm_mul]
    have hAnn : 0 ≤ A := hA0.le
    calc ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ *
          (‖lapW (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2)) ((ceCs : ℂ) * w)‖ *
            ‖airyTwistedLaplaceC (ceG1 (airyZero 1)) ((ceCs : ℂ) * w)‖)
        ≤ 1 * (((γ + 2 * θ * A * Real.sqrt lam) * liftEps c) * (Cg * (1 + w.re) ^ (-(9 / 2 : ℝ)))) :=
          mul_le_mul (norm_liftMultiplier_le_one hδ0 m hw)
            (mul_le_mul hlap_le (hG.trans hG_w) (norm_nonneg _) (by positivity))
            (by positivity) zero_le_one
      _ ≤ C_S * liftEps c * (1 + w.re) ^ (-(9 / 2 : ℝ)) := by
          have h1 : (γ + 2 * θ * A * Real.sqrt lam) * Cg ≤ C_S := by dsimp [C_S]; linarith
          calc _ = ((γ + 2 * θ * A * Real.sqrt lam) * Cg) * (liftEps c * (1 + w.re) ^ (-(9 / 2 : ℝ))) := by ring
            _ ≤ C_S * (liftEps c * (1 + w.re) ^ (-(9 / 2 : ℝ))) := mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = _ := by ring
  · intro c x y hc hx _ hy
    have hdiff_c := hdiff hc
    have hderiv : ∀ z₀ ∈ Metric.closedBall (x : ℂ) (x / 4),
        ‖deriv (fun w => liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) m w) z₀‖ ≤
          (Λ_loc * (liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re) / (x / 4) := by
      intro z₀ hz₀
      have hr : 0 < x / 4 := by linarith
      have hcl : Metric.closedBall z₀ (x / 4) ⊆ {w : ℂ | 0 < w.re} := fun ζ hζ => by
        have h1 : ‖ζ - (x : ℂ)‖ ≤ x / 2 := by
          calc ‖ζ - (x : ℂ)‖ = ‖(ζ - z₀) + (z₀ - (x : ℂ))‖ := by ring_nf
            _ ≤ ‖ζ - z₀‖ + ‖z₀ - (x : ℂ)‖ := norm_add_le _ _
            _ ≤ x / 4 + x / 4 := add_le_add (mem_closedBall_iff_norm.mp hζ) (mem_closedBall_iff_norm.mp hz₀)
            _ = x / 2 := by ring
        have hre : |ζ.re - x| ≤ x / 2 := by
          calc |ζ.re - x| = |(ζ - (x : ℂ)).re| := by simp
            _ ≤ ‖ζ - (x : ℂ)‖ := Complex.abs_re_le_norm _
            _ ≤ x / 2 := h1
        change 0 < ζ.re
        linarith [(abs_le.mp hre).1]
      refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
        ⟨hdiff_c.mono (Metric.ball_subset_closedBall.trans hcl),
          by rw [closure_ball z₀ hr.ne']; exact hdiff_c.continuousOn.mono hcl⟩
        fun ζ hζ => ?_
      have h1 : ‖ζ - (x : ℂ)‖ ≤ x / 2 := by
        calc ‖ζ - (x : ℂ)‖ = ‖(ζ - z₀) + (z₀ - (x : ℂ))‖ := by ring_nf
          _ ≤ ‖ζ - z₀‖ + ‖z₀ - (x : ℂ)‖ := norm_add_le _ _
          _ ≤ x / 4 + x / 4 := add_le_add (le_of_eq (mem_sphere_iff_norm.mp hζ)) (mem_closedBall_iff_norm.mp hz₀)
          _ = x / 2 := by ring
      have hre : |ζ.re - x| ≤ x / 2 := by
        calc |ζ.re - x| = |(ζ - (x : ℂ)).re| := by simp
          _ ≤ ‖ζ - (x : ℂ)‖ := Complex.abs_re_le_norm _
          _ ≤ x / 2 := h1
      exact hre_half hc hx (by linarith [(abs_le.mp hre).1])
    have hball_sub : Metric.closedBall (x : ℂ) (x / 4) ⊆ {w : ℂ | 0 < w.re} := fun ζ hζ => by
      have hre : |ζ.re - x| ≤ x / 4 := by
        calc |ζ.re - x| = |(ζ - (x : ℂ)).re| := by simp
          _ ≤ ‖ζ - (x : ℂ)‖ := Complex.abs_re_le_norm _
          _ ≤ x / 4 := mem_closedBall_iff_norm.mp hζ
      change 0 < ζ.re; linarith [(abs_le.mp hre).1]
    have hpt1 : (x : ℂ) ∈ Metric.closedBall (x : ℂ) (x / 4) :=
      Metric.mem_closedBall_self (by linarith)
    have hpt2 : (x : ℂ) + (y : ℂ) * Complex.I ∈ Metric.closedBall (x : ℂ) (x / 4) := by
      simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
      exact hy
    have hmv := (convex_closedBall (x : ℂ) (x / 4)).norm_image_sub_le_of_norm_deriv_le
      (fun ζ hζ => (hdiff_c ζ (hball_sub hζ)).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (hball_sub hζ)))
      hderiv hpt1 hpt2
    have hdist_eq : ‖((x : ℂ) + (y : ℂ) * Complex.I) - (x : ℂ)‖ = |y| := by
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    rw [hdist_eq] at hmv
    calc ‖liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) m ((x : ℂ) + (y : ℂ) * Complex.I) -
          liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)‖
        ≤ (Λ_loc * (liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re) / (x / 4) * |y| := hmv
      _ = 4 * Λ_loc * (|y| / x) * (liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re := by
          field_simp [hx.ne']
  · intro c x y hc hx _
    exact hre_half hc hx (by simp; linarith)

/-- info: 'FormalResearch.SignUncertainty.convSource_preEdge_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convSource_preEdge_bounds

end FormalResearch.SignUncertainty
