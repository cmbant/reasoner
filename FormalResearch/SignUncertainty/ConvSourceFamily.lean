module

public import FormalResearch.SignUncertainty.CeLiftSign
public import FormalResearch.SignUncertainty.CeLiftSignMain
public import FormalResearch.SignUncertainty.ConvSourceEdgeTail
public import FormalResearch.SignUncertainty.ConvSourceSign
public import FormalResearch.SignUncertainty.WindowTranslation

/-!
# The convolution source family satisfies `CeSourceFamily` (M6 step (a), `ceo:conv`)

For the convolution source `S_c = convSource p γ θ ε (λ ε²)`, `ε = c^{-1/3}` (`convSourceFamily p γ θ lam`), this module proves the remaining
fields of `CeSourceFamily` (`CeLiftSign`) and assembles the instance theorem `ceSourceFamily_convSource`, for every `p ∈ (1/2, 1)`, `γ > 0`, `θ ≥ 0`,
`λ > 0` (the paper's choice is `p = 3/4`, `λ = γ = θ = 1`, `ceSourceFamily_convSource_paper`; `ce_hb_lift.tex`, proof of `thm:ce-hb-lift`).

* `convSourceFamily_mass` (`mass`, `O.12(1)`-`(2)`): `γ ε ≤ ∫ S_c = ∫ w_c ≤ (γ + θ B ε-constant) ε`, from `∫ w_h ≥ 0` and `convW_L1_le`;
* `convSource_twisted_unif`: the **uniform `U.2` bound** `‖S̃_c(c_s w)‖ ≤ C_D ‖1 + w‖^{-5/2}` on `Re w ≥ 0`, with `C_D` independent of `ε ∈ (0, 1]`
  (product formula `airyTwistedLaplaceC_convSource` and `‖lapW w_c‖ ≤ ‖w_c‖₁ ≤ C ε`).  This single estimate is all that `edge` and `dual` need;
* `convSourceFamily_edge` (`edge`, `O.12(6)` at `w = ε⁻¹` in its weak form): `‖W_{S_c}(c^{1/3})‖ ≤ C_D c^{-5/6}`, from `|M_ψ| ≤ 1` and the bound above;
* `convSourceFamily_dual` (`dual`, `O6DualEst 4 (-S_c)`): `(e3)` from `iDual_bound_e3` (the dual-line symbol bound with the uniform constant `C_D`), and the window
  bound `(e5)` from `dual_bound_window` (absolute reflected integration, `‖I_dual‖ ≲ ξ⁻¹ c^{-1/2}`);
* `ceSourceFamily_convSource`: `CeSourceFamily (convSourceFamily p γ θ lam)`, with `hasU2` from `hasU2_convSource` and `tail` from
  `ceSourceFamily_tail_convSource`;
* `ceLift_physical_unconditional`: `ceLift_physical` with both of its hypotheses discharged (`O6Bricks 4` by `o6Bricks_holds`, `CeSourceFamily` by
  `ceSourceFamily_convSource_paper`): the edge sign / origin tuning / threshold of the lift, for every large `c`.

Class: proved, unconditional (no hypothesis structure).  The uniform far transfer `O.12(7)` and `GT.2b` with the sharper amplitude `ε^{9/2}`/`ε^{7/2}` are **not**
needed: the fields ask for the weaker bounds `c^{-5/6}` (`edge`) and `ξ⁻¹ c^{-1/2}` (`e5`), which already follow from the `U.2` bound.  The sharper statements
`O.12(5)`, `O.12(6)` (the factor `(1 + Re w)^{-11/2} ε`) are not formalised here.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- The convolution-source family `c ↦ S_c(u) = ∫₀^∞ w_c(y) g₁(u + y) dy` with `ε = c^{-1/3}` and `h = λ ε²` (`ceo:conv`, (`ceo:conv.1`)). -/
noncomputable def convSourceFamily (p γ θ lam : ℝ) (c u : ℝ) : ℝ :=
  convSource p γ θ (liftEps c) (lam * liftEps c ^ 2) u

/-- The integral of the full weight: `∫ w_c = γ ε + θ ∫ w_h`. -/
lemma convWc_integral_eq {p γ θ ε h : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hh : 0 < h) :
    ∫ y in Ioi (0 : ℝ), convWc p γ θ ε h y = γ * ε + θ * ∫ y in Ioi (0 : ℝ), convWh p h y := by
  have h1 : IntegrableOn (fun y : ℝ => γ * ε * Real.exp (-y)) (Ioi 0) :=
    ((exp_neg_integrableOn_Ioi 0 one_pos).congr_fun (fun y _ => by simp) measurableSet_Ioi).const_mul (γ * ε)
  unfold convWc
  rw [integral_add h1 ((convW_integrable hp hp1 hh).const_mul θ), integral_const_mul, integral_const_mul,
    integral_exp_neg_Ioi_zero]
  ring

/-- The mass of the weight: `γ ε ≤ ∫ w_c ≤ (γ + θ A √λ) ε`, `A = 2 + 1/(p - 1/2)`, for `h = λ ε²`. -/
lemma convWc_integral_bounds {p γ θ lam ε : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hθ : 0 ≤ θ)
    (hlam : 0 < lam) (hε : 0 < ε) :
    γ * ε ≤ ∫ y in Ioi (0 : ℝ), convWc p γ θ ε (lam * ε ^ 2) y ∧
      ∫ y in Ioi (0 : ℝ), convWc p γ θ ε (lam * ε ^ 2) y ≤
        (γ + θ * ((2 + 1 / (p - 1 / 2)) * Real.sqrt lam)) * ε := by
  have hh : 0 < lam * ε ^ 2 := by positivity
  rw [convWc_integral_eq hp hp1 hh]
  have hnn : 0 ≤ ∫ y in Ioi (0 : ℝ), convWh p (lam * ε ^ 2) y :=
    setIntegral_nonneg measurableSet_Ioi (fun y hy => convWh_nonneg hh.le hy)
  have hup := convW_L1_le hp hp1 hh
  have hsq : Real.sqrt (lam * ε ^ 2) = Real.sqrt lam * ε := by
    rw [Real.sqrt_mul hlam.le, Real.sqrt_sq hε.le]
  rw [hsq] at hup
  refine ⟨by nlinarith, ?_⟩
  have := mul_le_mul_of_nonneg_left hup hθ
  nlinarith

/-- **`mass` field**: `m₀ ε ≤ ∫ S_c ≤ M₀ ε` with `m₀ = γ`, `M₀ = γ + θ (2 + 1/(p - 1/2)) √λ`, for every `c ≥ 1`. -/
theorem convSourceFamily_mass {p γ θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 < γ) (hθ : 0 ≤ θ)
    (hlam : 0 < lam) :
    ∃ m₀ M₀ : ℝ, 0 < m₀ ∧ 0 < M₀ ∧ ∀ {c : ℝ}, 2000 ≤ c →
      m₀ * liftEps c ≤ ∫ u : ℝ, convSourceFamily p γ θ lam c u ∧
        ∫ u : ℝ, convSourceFamily p γ θ lam c u ≤ M₀ * liftEps c := by
  refine ⟨γ, γ + θ * ((2 + 1 / (p - 1 / 2)) * Real.sqrt lam), hγ, ?_, fun {c} hc => ?_⟩
  · have : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
    have : 0 < 1 / (p - 1 / 2) := one_div_pos.mpr (by linarith)
    positivity
  · have hc0 : 0 < c := by linarith
    have hε := liftEps_pos hc0
    have hh : 0 < lam * liftEps c ^ 2 := by positivity
    have hI := (convSource_integral (γ := γ) (θ := θ) (ε := liftEps c) hp hp1 hh).2
    have hI' : ∫ u : ℝ, convSourceFamily p γ θ lam c u =
        ∫ y in Ioi (0 : ℝ), convWc p γ θ (liftEps c) (lam * liftEps c ^ 2) y := hI
    rw [hI']
    exact convWc_integral_bounds hp hp1 hθ hlam hε

/-- **The uniform `U.2` bound for the convolution source**: `‖S̃_c(c_s w)‖ ≤ C_D ‖1 + w‖^{-5/2}` on `Re w ≥ 0`, with `C_D` independent of
`ε ∈ (0, 1]` (and of `h = λ ε²`).  From the product formula `S̃_c = ŵ_c-Laplace · g̃₁` and `‖L w_c‖ ≤ ‖w_c‖₁ ≤ (γ + θ A √λ) ε`. -/
theorem convSource_twisted_unif {p γ θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 ≤ γ) (hθ : 0 ≤ θ)
    (hlam : 0 < lam) :
    ∃ CD : ℝ, 0 < CD ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ {w : ℂ}, 0 ≤ w.re →
      ‖airyTwistedLaplaceC (convSource p γ θ ε (lam * ε ^ 2)) ((ceCs : ℂ) * w)‖ ≤ CD * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨Cg, hCg, hg⟩ := hasU2_ceG1.rhp
  set M : ℝ := γ + θ * ((2 + 1 / (p - 1 / 2)) * Real.sqrt lam) with hM
  have hM0 : 0 ≤ M := by
    have : 0 ≤ Real.sqrt lam := Real.sqrt_nonneg _
    have : 0 ≤ 1 / (p - 1 / 2) := (one_div_pos.mpr (by linarith)).le
    rw [hM]; positivity
  refine ⟨M * Cg + 1, by positivity, fun {ε} hε hε1 {w} hw => ?_⟩
  have hh : 0 < lam * ε ^ 2 := by positivity
  have hz : 0 ≤ ((ceCs : ℂ) * w).re := by
    rw [Complex.re_ofReal_mul]; exact mul_nonneg ceCs_pos.le hw
  rw [airyTwistedLaplaceC_convSource hp hp1 hh hz, norm_mul]
  have hT : 0 ≤ ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  have hlap : ‖lapW (convWc p γ θ ε (lam * ε ^ 2)) ((ceCs : ℂ) * w)‖ ≤ M * ε := by
    refine (lapW_norm_le (convWc_integrableOn hp hp1 hh) hz).trans ?_
    have hn : ∫ y in Ioi (0 : ℝ), ‖convWc p γ θ ε (lam * ε ^ 2) y‖ =
        ∫ y in Ioi (0 : ℝ), convWc p γ θ ε (lam * ε ^ 2) y :=
      setIntegral_congr_fun measurableSet_Ioi (fun y hy => Real.norm_of_nonneg (convWc_nonneg hγ hθ hε.le hh.le hy))
    rw [hn]
    exact (convWc_integral_bounds hp hp1 hθ hlam hε).2
  have hG := hg w hw
  calc ‖lapW (convWc p γ θ ε (lam * ε ^ 2)) ((ceCs : ℂ) * w)‖ *
        ‖airyTwistedLaplaceC (ceG1 (airyZero 1)) ((ceCs : ℂ) * w)‖
      ≤ (M * ε) * (Cg * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) :=
        mul_le_mul hlap hG (norm_nonneg _) (by positivity)
    _ ≤ (M * 1) * (Cg * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) := by gcongr
    _ ≤ (M * Cg + 1) * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by nlinarith

/-- Negation preserves `HasU2`. -/
lemma hasU2_neg_fun {X : ℝ → ℝ} (h : HasU2 X) : HasU2 (fun u => -X u) := by
  have := h.smul (-1)
  simpa only [neg_mul, one_mul] using this

lemma airyTwistedLaplaceC_neg_fun (X : ℝ → ℝ) (y : ℂ) :
    airyTwistedLaplaceC (fun u => -X u) y = -airyTwistedLaplaceC X y := by
  have := airyTwistedLaplaceC_const_mul (-1) X y
  simpa only [neg_mul, one_mul, Complex.ofReal_neg, Complex.ofReal_one] using this

/-- **`edge` field** (`O.12(6)` at `w = ε⁻¹`, weak form): `‖W_{S_c}(c^{1/3})‖ ≤ C_D c^{-5/6}` at every spline width `δ₀ ≥ 0`, order `m`, `c ≥ 8`;
the constant does not depend on `K`. -/
theorem convSourceFamily_edge {p γ θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 ≤ γ) (hθ : 0 ≤ θ)
    (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {δ₀ : ℝ} (m : ℕ) {c : ℝ}, 0 ≤ δ₀ → 8 ≤ c →
      ‖liftSymbol (convSourceFamily p γ θ lam c) δ₀ m (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖ ≤ C * c ^ (-(5 / 6 : ℝ)) := by
  obtain ⟨CD, hCD, hb⟩ := convSource_twisted_unif hp hp1 hγ hθ hlam
  refine ⟨CD, hCD.le, fun {δ₀} m {c} hδ hc => ?_⟩
  have hc0 : 0 < c := by linarith
  have hε := liftEps_pos hc0
  have hε1 : liftEps c ≤ 1 := liftEps_le_one (by linarith)
  have hR : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hw : 0 ≤ (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ).re := by simpa using hR.le
  unfold liftSymbol
  rw [norm_mul]
  have h1 := norm_liftMultiplier_le_one hδ m hw
  have h2 := hb hε hε1 hw
  have hnorm : ‖1 + (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖ = 1 + c ^ (1 / 3 : ℝ) := by
    rw [show (1 : ℂ) + (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) = ((1 + c ^ (1 / 3 : ℝ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hpow : (1 + c ^ (1 / 3 : ℝ)) ^ (-(5 / 2 : ℝ)) ≤ c ^ (-(5 / 6 : ℝ)) := by
    refine (Real.rpow_le_rpow_of_nonpos hR (by linarith) (by norm_num)).trans_eq ?_
    rw [← Real.rpow_mul hc0.le]; norm_num
  rw [hnorm] at h2
  have h3 : ‖airyTwistedLaplaceC (convSourceFamily p γ θ lam c) ((ceCs : ℂ) * (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ))‖ ≤
      CD * c ^ (-(5 / 6 : ℝ)) :=
    h2.trans (mul_le_mul_of_nonneg_left hpow hCD.le)
  calc ‖liftMultiplier δ₀ m (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖ *
        ‖airyTwistedLaplaceC (convSourceFamily p γ θ lam c) ((ceCs : ℂ) * (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ))‖
      ≤ 1 * (CD * c ^ (-(5 / 6 : ℝ))) := mul_le_mul h1 h3 (norm_nonneg _) zero_le_one
    _ = CD * c ^ (-(5 / 6 : ℝ)) := one_mul _

/-- **`dual` field**: `O6DualEst 4 (-S_c)`.  `(e3)` is `iDual_bound_e3` with the uniform dual-line constant of `convSource_twisted_unif`; the window bound
`(e5)` is `dual_bound_window` (absolute reflected integration of the dual integral), `‖I_dual[-S_c]‖ ≤ C ξ⁻¹ c^{-1/2}`. -/
theorem convSourceFamily_dual {p γ θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 ≤ γ) (hθ : 0 ≤ θ)
    (hlam : 0 < lam) :
    O6DualEst 4 (fun _ c u => -convSourceFamily p γ θ lam c u) := by
  obtain ⟨CD, hCD, hb⟩ := convSource_twisted_unif hp hp1 hγ hθ hlam
  have hbd : ∀ {c : ℝ}, 1 ≤ c → ∀ {w : ℂ}, 0 ≤ w.re →
      ‖airyTwistedLaplaceC (fun u => -convSourceFamily p γ θ lam c u) ((ceCs : ℂ) * w)‖ ≤
        CD * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
    intro c hc w hw
    have hc0 : 0 < c := by linarith
    rw [airyTwistedLaplaceC_neg_fun, norm_neg]
    exact hb (liftEps_pos hc0) (liftEps_le_one hc) hw
  constructor
  · obtain ⟨C, hC, h⟩ := iDual_bound_e3 (m := 4) (by norm_num) hCD.le
    refine ⟨C, hC, fun {K c ξ} hδ hc hξ hS => ?_⟩
    have hc0 : 0 < c := by linarith
    have hdiff : DifferentiableOn ℂ (airyTwistedLaplaceC (fun u => -convSourceFamily p γ θ lam c u)) {y : ℂ | 0 < y.re} :=
      (hasU2_neg_fun (hasU2_convSource hp hp1 (mul_pos hlam (pow_pos (liftEps_pos hc0) 2)))).differentiable
    exact h hdiff (fun {w} hw => hbd (by linarith) hw) hδ hc hξ hS
  · intro Sw
    obtain ⟨C, hC, h⟩ := dual_bound_window 4 (by norm_num) CD hCD
    refine ⟨C, hC, fun {K c ξ} hK hc hξ _ => ?_⟩
    have hc0 : 0 < c := by linarith
    have hδ : 0 ≤ ceBeta1 * K * liftEps c / 2 := by
      have := ceBeta1_pos
      have := liftEps_pos hc0
      have : 0 < K := by linarith
      positivity
    have h1 := h (D := fun u => -convSourceFamily p γ θ lam c u) (fun {w} hw => hbd (by linarith) hw) hδ hc0 hξ
    refine h1.trans ?_
    have hc12 : 0 ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hc0.le _
    have hinv : ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ ≤ 1 := by
      refine inv_le_one_of_one_le₀ (one_le_pow₀ ?_)
      have : 0 ≤ ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ) :=
        mul_nonneg hδ (Real.rpow_nonneg hc0.le _)
      linarith
    have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hξ1 : (2 * Real.pi * ξ)⁻¹ ≤ ξ⁻¹ := by
      rw [mul_inv]
      have : (2 * Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpi
      have hξi : 0 ≤ ξ⁻¹ := inv_nonneg.mpr hξ.le
      nlinarith
    have hrest : C * ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ * c ^ (-(1 / 2 : ℝ)) ≤
        C * c ^ (-(1 / 2 : ℝ)) := by
      have : 0 ≤ C * c ^ (-(1 / 2 : ℝ)) := by positivity
      calc _ ≤ C * 1 * c ^ (-(1 / 2 : ℝ)) := by gcongr
        _ = _ := by ring
    calc (2 * Real.pi * ξ)⁻¹ * (C * ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ * c ^ (-(1 / 2 : ℝ)))
        ≤ ξ⁻¹ * (C * c ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul hξ1 hrest (by positivity) (inv_nonneg.mpr hξ.le)
      _ = C * ξ⁻¹ * c ^ (-(1 / 2 : ℝ)) := by ring

/-- **M6 step (a): the convolution source family satisfies `CeSourceFamily`** (`ceo:conv`, `thm:ce-hb-lift`): for every `p ∈ (1/2, 1)`, `γ > 0`, `θ ≥ 0`, `λ > 0`,
the family `S_c = convSource p γ θ (c^{-1/3}) (λ c^{-2/3})` has the five fields `hasU2`, `mass`, `tail`, `edge`, `dual`.  Hence `ceLift_physical` and the
reductions that assume `CeSourceFamily` apply to the actual convolution source.  The paper's parameters (`p = 3/4`, `λ = γ = θ = 1`, spline order 4) are the
case `ceSourceFamily_convSource_paper`.  Scope: the statement is the Lean field set of `CeSourceFamily`; the sharper paper bounds `O.12(5)`-`(7)` are not
formalised and not needed. -/
theorem ceSourceFamily_convSource {p γ θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 < γ) (hθ : 0 ≤ θ)
    (hlam : 0 < lam) : CeSourceFamily (convSourceFamily p γ θ lam) where
  hasU2 {c} hc := by
    have hc0 : 0 < c := by linarith
    exact hasU2_convSource hp hp1 (by have := liftEps_pos hc0; positivity)
  mass := convSourceFamily_mass hp hp1 hγ hθ hlam
  tail {K c} hK hc hcK := ceSourceFamily_tail_convSource (γ := γ) (θ := θ) hp hp1 hlam hK hc hcK
  edge K _ := by
    obtain ⟨C, hC, h⟩ := convSourceFamily_edge hp hp1 hγ.le hθ hlam
    refine ⟨C, hC, fun {c} hc hcK => ?_⟩
    have hc0 : 0 < c := by linarith
    refine h 4 ?_ (by linarith)
    have := ceBeta1_pos
    have := liftEps_pos hc0
    have : 0 < K := by linarith
    positivity
  dual := convSourceFamily_dual hp hp1 hγ.le hθ hlam

/-- The paper's parameters (`ce_hb_lift.tex`, proof of `thm:ce-hb-lift`): `p = 3/4`, `λ = γ = θ = 1`. -/
theorem ceSourceFamily_convSource_paper : CeSourceFamily (convSourceFamily (3 / 4) 1 1 1) :=
  ceSourceFamily_convSource (by norm_num) (by norm_num) one_pos zero_le_one one_pos

/-- **The physical half of `thm:ce-hb-lift` at `m₀ = 1`, unconditional** (`ceLift_physical` with `O6Bricks 4` from `o6Bricks_holds` and `CeSourceFamily` from
`ceSourceFamily_convSource_paper`, i.e. the convolution source with the paper's parameters): there are `K₁, c₁` such that for every `c ≥ c₁` there are Hankel
eigenfunctions `f₊` (`σ = +1`), `f₋` (`σ = -1`) with `f₋(0) = 0 < f₊(0)` and `f₊ + f₋ ≤ 0` on `[T, ∞)`, `T ≤ c/π² + A c^{1/3} + K₁`.  Not included: the Fourier sign
`f₋ ≤ f₊` on `[0, ∞)` (`ĥ ≥ 0`; `thm:ce-post-edge`, `cepe:general`), hence `CeHankelPair` and `ce_hb_lift_m1` are still open. -/
theorem ceLift_physical_unconditional :
    ∃ K₁ c₁ : ℝ, ∀ {c : ℝ}, c₁ ≤ c → ∃ (fp fm : ℝ → ℝ) (T : ℝ),
      IsHankelEigenfn c 1 fp ∧ IsHankelEigenfn c (-1) fm ∧ fm 0 = 0 ∧ 0 < fp 0 ∧
      T ≤ c / Real.pi ^ 2 + airyOrderCoeff * c ^ (1 / 3 : ℝ) + K₁ ∧
      ∀ Δ : ℝ, T ≤ Δ → fp Δ + fm Δ ≤ 0 :=
  ceLift_physical (o6Bricks_holds (by norm_num)) ceSourceFamily_convSource_paper

/-- info: 'FormalResearch.SignUncertainty.convSourceFamily_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convSourceFamily_mass

/-- info: 'FormalResearch.SignUncertainty.convSource_twisted_unif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convSource_twisted_unif

/-- info: 'FormalResearch.SignUncertainty.convSourceFamily_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convSourceFamily_edge

/-- info: 'FormalResearch.SignUncertainty.convSourceFamily_dual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convSourceFamily_dual

/-- info: 'FormalResearch.SignUncertainty.ceSourceFamily_convSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceSourceFamily_convSource

/-- info: 'FormalResearch.SignUncertainty.ceSourceFamily_convSource_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceSourceFamily_convSource_paper

/-- info: 'FormalResearch.SignUncertainty.ceLift_physical_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceLift_physical_unconditional

end FormalResearch.SignUncertainty
