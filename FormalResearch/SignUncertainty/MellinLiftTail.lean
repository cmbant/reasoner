module

public import FormalResearch.SignUncertainty.MellinLiftSymbol
public import FormalResearch.CohnElkies.HighBandUniform
public import FormalResearch.CohnElkies.DualBoundE3

/-!
# `O.11ak`: the edge representation `(e1)` and the tail of the lift

Source: `CFT/sign_uncertainty/paper/u1c_o1_upper.tex`, Theorem `O.11ak`, `(e1)` (`u1co:O1`/`u1c:U3`) and `(ceo:O11ak.4)`.

* `lift_edge_repr`: for the lift `f = L^σ_c[X]` of a seed with the `U.2` package, `c^{1/3} ρ₀(cξ) f(cξ) = I_main[X](ξ) + σ I_dual[X](ξ)`
  (the inverse Mellin integral on `Re z = c`, the kernel identity `mellin_strip_kernel_eq` and the substitution `y = -c^{2/3} v`).

* `iMain_add_iDual_tail`: the uniform bound `|c^{1/3} ρ₀ f|(cξ) ≲ ξ⁻¹ (log π²ξ)^{-3/2}` from `(e4)` (`hb_estimate_airySeed_uniform`) and `(e3)` (`iDual_bound_e3`).
* `exists_hankelEigenfn_lift`: for one-level seeds `X = airySeedU2 a b c₀`, `δ₀ = β₁Kε/2`, `c ≥ max(2000, 8K³)`, `m ≥ 3`, `σ = ±1`, there is
  `f ∈ 𝒜_c^σ` (`IsHankelEigenfn c σ f`) with the edge representation and `f(0) = σ∫fρ₀`.

Status: proved, unconditional.
Not formalised here: the value `f(0) = W(c^{1/3}) + σW(0)` (Mellin transform at the endpoint `z = c`), the general fixed-`c`
fixed-`δ₀` statement with `K_c ∈ L¹` (Proof 2), and the explicit constants of Remark `O.11ak.a`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

section

variable {W : ℂ → ℂ} {c σ : ℝ}

/-- The integrand of the inverse Mellin integral on `Re z = c`, in the kernel form. -/
theorem edge_integrand_eq {c : ℝ} (hc : 0 < c) {ξ : ℝ} (hξ : 0 < ξ) (y : ℝ) :
    ((c * ξ : ℝ) : ℂ) ^ (-((c : ℂ) + (y : ℂ) * Complex.I)) • liftPhi W c σ ((c : ℂ) + (y : ℂ) * Complex.I) =
      (Complex.Gamma (c : ℂ) * ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) ^ (-(c : ℂ))) *
        (mellinK0 c (1 - ((c : ℂ) + (y : ℂ) * Complex.I) / c) ξ * liftS W c σ ((c : ℂ) + (y : ℂ) * Complex.I)) := by
  set z : ℂ := (c : ℂ) + (y : ℂ) * Complex.I with hz
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hzre : z.re = c := by simp [hz]
  have hz0 : 0 < z.re := by rw [hzre]; exact hc
  have hζ0 : 0 ≤ (1 - z / (c : ℂ)).re := by rw [re_one_sub_div hc, hzre, div_self hc.ne']; simp
  have hζ1 : (1 - z / (c : ℂ)).re < 1 := by
    rw [re_one_sub_div hc]; have : 0 < z.re / c := by positivity
    linarith
  have key := mellin_strip_kernel_eq hc hξ hζ0 hζ1
  have e1 : (c : ℂ) * (1 - (1 - z / (c : ℂ))) = z := by field_simp; ring
  have e0 : (c : ℂ) * (1 - z / c) = (c : ℂ) - z := by field_simp
  rw [e1, e0] at key
  have hr : (0 : ℝ) < 2 * Real.pi := by positivity
  have hD : (0 : ℝ) < c * ξ := by positivity
  have hP : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hDn : ((c * ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hTeq : ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * ((c * ξ : ℝ) : ℂ) := by push_cast; ring
  have hTkey : (2 * (Real.pi : ℂ) * c * ξ : ℂ) = ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) := by push_cast; ring
  rw [hTkey] at key
  have hT : ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) ≠ 0 := by rw [hTeq]; exact mul_ne_zero hP hDn
  have hGc : Complex.Gamma (c : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hc)
  have hTz : ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) ^ (-z) =
      ((2 * Real.pi : ℝ) : ℂ) ^ (-z) * ((c * ξ : ℝ) : ℂ) ^ (-z) := by
    rw [hTeq, Complex.mul_cpow_ofReal_nonneg hr.le hD.le]
  have hTadd : ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) ^ (-(c : ℂ)) * ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) ^ ((c : ℂ) - z) =
      ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) ^ (-z) := by
    rw [← Complex.cpow_add _ _ hT]; congr 1; ring
  unfold liftPhi
  rw [← key, smul_eq_mul]
  calc ((c * ξ : ℝ) : ℂ) ^ (-z) * (((2 * Real.pi : ℝ) : ℂ) ^ (-z) * Complex.Gamma z * Complex.exp ((c : ℂ) * stripH (1 - z / c)) * liftS W c σ z)
      = (((2 * Real.pi : ℝ) : ℂ) ^ (-z) * ((c * ξ : ℝ) : ℂ) ^ (-z)) * Complex.Gamma z * Complex.exp ((c : ℂ) * stripH (1 - z / c)) * liftS W c σ z := by ring
    _ = ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) ^ (-(c : ℂ)) * ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) ^ ((c : ℂ) - z) * Complex.Gamma z *
          Complex.exp ((c : ℂ) * stripH (1 - z / c)) * liftS W c σ z := by rw [hTadd, ← hTz]
    _ = _ := by field_simp

end


section

lemma cpow_two_thirds_mul {c : ℝ} (hc : 0 < c) : c ^ (2 / 3 : ℝ) * c ^ (1 / 3 : ℝ) = c := by
  rw [← Real.rpow_add hc]; norm_num

lemma cpow_two_thirds_eq {c : ℝ} (hc : 0 < c) : c ^ (2 / 3 : ℝ) = c * liftEps c := by
  unfold liftEps
  calc c ^ (2 / 3 : ℝ) = c ^ (1 + (-(1 / 3 : ℝ))) := by norm_num
    _ = c * c ^ (-(1 / 3 : ℝ)) := by rw [Real.rpow_add hc, Real.rpow_one]

/-- The point `1 - (c + y i)/c` for `y = -c^{2/3} v` is `i ε v`. -/
lemma kernel_arg_eq {c : ℝ} (hc : 0 < c) (v : ℝ) :
    1 - ((c : ℂ) + (((-(c ^ (2 / 3 : ℝ) * v) : ℝ) : ℂ)) * Complex.I) / c = (((liftEps c * v : ℝ) : ℂ)) * Complex.I := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have h := cpow_two_thirds_eq hc
  have h' : ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) = (c : ℂ) * ((liftEps c : ℝ) : ℂ) := by exact_mod_cast h
  push_cast
  rw [h']
  field_simp
  ring

lemma liftS_arg_eq {c : ℝ} (hc : 0 < c) (W : ℂ → ℂ) (σ v : ℝ) :
    liftS W c σ ((c : ℂ) + (((-(c ^ (2 / 3 : ℝ) * v) : ℝ) : ℂ)) * Complex.I) =
      W ((v : ℂ) * Complex.I) + (σ : ℂ) * W (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) - (v : ℂ) * Complex.I) := by
  have hs : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have hs' : ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hcs : (c : ℂ) / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) = ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by
    have hr : c = c ^ (1 / 3 : ℝ) * c ^ (2 / 3 : ℝ) := by rw [mul_comm]; exact (cpow_two_thirds_mul hc).symm
    rw [div_eq_iff hs']
    exact_mod_cast hr
  unfold liftS
  congr 2
  · push_cast; field_simp; ring
  · rw [show ((c : ℂ) + ((-(c ^ (2 / 3 : ℝ) * v) : ℝ) : ℂ) * Complex.I) / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) =
        (c : ℂ) / ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) - (v : ℂ) * Complex.I by push_cast; field_simp; ring, hcs]

end


section

/-- **`(e1)` for a single lift.** -/
theorem lift_edge_repr {X : ℝ → ℝ} (hX : HasU2 X) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ) {c : ℝ} (hc : 3 / 2 < c)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {ξ : ℝ} (hξ : 0 < ξ) :
    (((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) *
        liftFun (liftPhi (liftSymbol X δ₀ m) c σ) (c / 2) (c * ξ) : ℝ)) : ℂ) =
      iMain X δ₀ m c ξ + (σ : ℂ) * iDual X δ₀ m c ξ := by
  have hc0 : 0 < c := by linarith
  have hWd := liftSymbolData_of_hasU2 hX hδ m
  set Φ := liftPhi (liftSymbol X δ₀ m) c σ with hΦdef
  have hΦ : MellinLiftData c Φ := liftPhi_mellinLiftData hWd hc σ hσ
  have hΔ : 0 < c * ξ := by positivity
  have hs : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have e1 : (liftFun Φ (c / 2) (c * ξ) : ℂ) = mellinInv c Φ (c * ξ) := by
    rw [ofReal_liftFun hΦ (x₀ := c / 2) (x := c / 2) (by linarith) (by linarith) (by linarith) (by linarith) hΔ,
      mellinInv_liftPhi_edge hWd hc σ hσ hΔ]
  -- the integral on `Re z = c`
  set G : ℝ → ℂ := fun y => mellinK0 c (1 - ((c : ℂ) + (y : ℂ) * Complex.I) / c) ξ *
    liftS (liftSymbol X δ₀ m) c σ ((c : ℂ) + (y : ℂ) * Complex.I) with hG
  have e2 : mellinInv c Φ (c * ξ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ((Complex.Gamma (c : ℂ) * ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) ^ (-(c : ℂ))) * ∫ y : ℝ, G y) := by
    unfold mellinInv
    rw [Complex.real_smul]
    congr 1
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    exact edge_integrand_eq hc0 hξ y
  have e3 : ∫ y : ℝ, G y = ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
      ∫ v : ℝ, (iMainIntegrand X δ₀ m c ξ v + (σ : ℂ) * iDualIntegrand X δ₀ m c ξ v) := by
    have h := Measure.integral_comp_mul_left G (-(c ^ (2 / 3 : ℝ)))
    have hpt : ∀ v : ℝ, G (-(c ^ (2 / 3 : ℝ)) * v) =
        iMainIntegrand X δ₀ m c ξ v + (σ : ℂ) * iDualIntegrand X δ₀ m c ξ v := by
      intro v
      simp only [hG]
      rw [show -(c ^ (2 / 3 : ℝ)) * v = -(c ^ (2 / 3 : ℝ) * v) by ring, kernel_arg_eq hc0 v, liftS_arg_eq hc0 _ σ v]
      unfold iMainIntegrand iDualIntegrand
      ring
    simp_rw [hpt] at h
    rw [h]
    have : |(-(c ^ (2 / 3 : ℝ)))⁻¹| = (c ^ (2 / 3 : ℝ))⁻¹ := by
      rw [abs_inv, abs_neg, abs_of_pos hs]
    rw [this, Complex.real_smul]
    have hs' : ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast
    field_simp
  have iM := hX.integrable_iMainIntegrand hδ m hc0 hξ
  have iD := hX.integrable_iDualIntegrand hδ m hc0 hξ
  rw [integral_add iM (iD.const_mul (σ : ℂ)), integral_const_mul] at e3
  -- constants
  have hΔr : (0 : ℝ) < c * ξ := hΔ
  have hT : ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) ^ (-(c : ℂ)) = (((2 * Real.pi * (c * ξ)) ^ (-c) : ℝ) : ℂ) := by
    rw [show -(c : ℂ) = ((-c : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (by positivity)]
  have hΓ : (Real.Gamma c : ℂ) = Complex.Gamma (c : ℂ) := (Complex.Gamma_ofReal c).symm
  have hGpos : 0 < Real.Gamma c := Real.Gamma_pos_of_pos hc0
  have hconst : c ^ (1 / 3 : ℝ) * ((2 * Real.pi) ^ c / Real.Gamma c * (c * ξ) ^ (c - 1)) * (1 / (2 * Real.pi)) *
      (Real.Gamma c * (2 * Real.pi * (c * ξ)) ^ (-c)) * c ^ (2 / 3 : ℝ) = (2 * Real.pi * ξ)⁻¹ := by
    have hr : (0 : ℝ) < 2 * Real.pi := by positivity
    rw [Real.mul_rpow hr.le hΔ.le, Real.rpow_neg (by positivity), Real.rpow_sub hΔ, Real.rpow_one]
    have h1 : c ^ (1 / 3 : ℝ) * c ^ (2 / 3 : ℝ) = c := cpow_two_thirds_mul hc0 |> fun h => by rw [mul_comm]; exact h
    field_simp
    have h2 : (c * ξ) ^ c * (c * ξ) ^ (-c) = 1 := by rw [← Real.rpow_add hΔ]; simp
    calc c ^ (1 / 3 : ℝ) * (c * ξ) ^ c * (c * ξ) ^ (-c) * c ^ (2 / 3 : ℝ)
        = c ^ (1 / 3 : ℝ) * c ^ (2 / 3 : ℝ) * ((c * ξ) ^ c * (c * ξ) ^ (-c)) := by ring
      _ = c := by rw [h2, h1]; ring
  unfold iMain iDual
  rw [Complex.ofReal_mul, Complex.ofReal_mul, e1, e2, e3, hT]
  unfold hankelRho0
  have hc13 : ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ((((2 * Real.pi) ^ c / Real.Gamma c * (c * ξ) ^ (c - 1) : ℝ)) : ℂ) *
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * ((Complex.Gamma (c : ℂ) * (((2 * Real.pi * (c * ξ)) ^ (-c) : ℝ) : ℂ)) *
        (((c ^ (2 / 3 : ℝ) : ℝ) : ℂ)))) = (((2 * Real.pi * ξ)⁻¹ : ℝ) : ℂ) := by
    rw [← hconst]; push_cast; rw [← hΓ]; ring
  set J1 := ∫ a : ℝ, iMainIntegrand X δ₀ m c ξ a
  set J2 := ∫ a : ℝ, iDualIntegrand X δ₀ m c ξ a
  calc _ = (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ((((2 * Real.pi) ^ c / Real.Gamma c * (c * ξ) ^ (c - 1) : ℝ)) : ℂ) *
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * ((Complex.Gamma (c : ℂ) * (((2 * Real.pi * (c * ξ)) ^ (-c) : ℝ) : ℂ)) *
        (((c ^ (2 / 3 : ℝ) : ℝ) : ℂ))))) * (J1 + (σ : ℂ) * J2) := by ring
    _ = _ := by rw [hc13]; push_cast; ring

end



lemma tail_norm_aux {Y : ℂ} {A1 s T C₄ E : ℝ} (h : ‖Y - ((A1 * s * T : ℝ) : ℂ)‖ ≤ C₄ * E * T) (hC : 0 ≤ C₄)
    (hT : 0 ≤ T) (hE : E ≤ 3) (hs : 0 ≤ s) :
    ‖Y‖ ≤ (|A1| * s + 3 * C₄) * T := by
  have h1 := norm_le_insert' Y ((A1 * s * T : ℝ) : ℂ)
  have h2 : ‖((A1 * s * T : ℝ) : ℂ)‖ = |A1| * s * T := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg hT]
  have h3 : C₄ * E * T ≤ 3 * C₄ * T := by nlinarith [mul_nonneg hC hT]
  nlinarith

section

/-- **The tail of the lift** (`(ceo:O11ak.4)` for the one-level seeds): for fixed `c ≥ max(2000, 8K³)`, `K ≥ 1`, `m ≥ 3`, the seed
`X = a f₁ + b g₁ + c₀ g₁'` and the width `δ₀ = β₁ K ε / 2`, `|I_main + σ I_dual| ≤ C ξ⁻¹ (log π²ξ)^{-3/2}` for large `ξ`. -/
theorem iMain_add_iDual_tail {m : ℕ} (hm : 3 ≤ m) (a b c₀ : ℝ) {K c : ℝ} (hK : 1 ≤ K) (hc : 2000 ≤ c)
    (hcK : 8 * K ^ 3 ≤ c) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∀ ξ : ℝ, ξ₀ ≤ ξ →
      ‖iMain (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ +
          (σ : ℂ) * iDual (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ‖ ≤
        C * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hε := liftEps_pos hc0
  have hσ1 : |σ| ≤ 1 := by rcases hσ with rfl | rfl <;> simp
  set R : ℝ := max |a| (max |b| |c₀|) with hR
  have hR0 : 0 ≤ R := le_max_of_le_left (abs_nonneg _)
  obtain ⟨γ₁, γ₂, γ₃, C₄, hC₄, h4⟩ := hb_estimate_airySeed_uniform (m := m) (by omega) R hR0
  obtain ⟨C₃, hC₃, h3⟩ := iDual_bound_e3_hasU2 hm (hasU2_airySeedU2 a b c₀)
  set H : ℝ := max 100 (c ^ (2 / 3 : ℝ)) with hH
  have hH0 : 0 < H := lt_max_of_lt_left (by norm_num)
  set L₁ : ℝ := Real.pi ^ 2 * liftEps c ^ 2 * H with hL₁
  have hL₁0 : 0 < L₁ := by positivity
  set A0 : ℝ := |a * γ₁ + b * γ₂ + c₀ * γ₃| * Real.sqrt Real.pi with hA0
  refine ⟨(A0 + 3 * C₄) * (c * liftEps c) ^ (-(3 / 2 : ℝ)) / (2 * Real.pi) + C₃ / c, by positivity,
    Real.exp L₁ / Real.pi ^ 2, by positivity, fun ξ hξ => ?_⟩
  have hξ0 : 0 < ξ := lt_of_lt_of_le (by positivity) hξ
  have hLge : L₁ ≤ Real.log (Real.pi ^ 2 * ξ) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hξ
    linarith
  set L := Real.log (Real.pi ^ 2 * ξ) with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le hL₁0 hLge
  have hS : H ≤ hbS c ξ := by
    unfold hbS
    rw [le_div_iff₀ (by positivity)]
    rw [hL₁] at hLge; nlinarith
  have hS100 : 100 ≤ hbS c ξ := (le_max_left _ _).trans hS
  have hSc : (1 : ℝ) * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ) ≤ hbS c ξ := by
    have h1 : (1 : ℝ) * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ) ≤ c ^ (2 / 3 : ℝ) := by
      have : (K ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
      have hp : 0 ≤ c ^ (2 / 3 : ℝ) := by positivity
      nlinarith
    exact h1.trans ((le_max_right _ _).trans hS)
  -- the main term
  have hKε : K * liftEps c ≤ 1 / 2 := by
    have h3 : (K * liftEps c) ^ 3 ≤ (1 / 2) ^ 3 := by
      have : (K * liftEps c) ^ 3 = K ^ 3 * liftEps c ^ 3 := by ring
      rw [this]
      have h := liftEps_cube_mul hc0
      nlinarith [pow_pos hε 3, pow_pos (by linarith : (0 : ℝ) < K) 3]
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) h3
  have hδ : ceBeta1 * K * liftEps c / 2 ∈ Set.Ioc (0 : ℝ) 2 := by
    refine ⟨by have := ceBeta1_pos; positivity, ?_⟩
    have := ceBeta1_lt_eight
    nlinarith [ceBeta1_pos, mul_le_mul_of_nonneg_left hKε ceBeta1_pos.le]
  have haR : |a| ≤ R := le_max_left _ _
  have hbR : |b| ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hcR : |c₀| ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have e4 := h4 haR hbR hcR (K := K) (M₁ := 1) (c := c) (ξ := ξ) hK le_rfl hcK hc hξ0 hS100 hSc
  have hA : hbA c ξ = (c * liftEps c) * L := rfl
  have hcε : 0 < c * liftEps c := by positivity
  have hT : hbA c ξ ^ (-(3 / 2 : ℝ)) = (c * liftEps c) ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ)) := by
    rw [hA, Real.mul_rpow hcε.le hL0.le]
  have hAp : 0 < hbA c ξ := by rw [hA]; exact mul_pos hcε hL0
  set T : ℝ := hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) with hTdef
  have hT0 : 0 ≤ T := by positivity
  have hTe : T = (c * liftEps c) ^ (-(3 / 2 : ℝ)) / (2 * Real.pi) * (ξ⁻¹ * L ^ (-(3 / 2 : ℝ))) := by
    rw [hTdef, hT]; field_simp
  have hKm : K ^ (-(m : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hK (by simp)
  have hSm : hbS c ξ ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have h1m : (1 : ℝ) ^ (-((m : ℝ) / 2)) = 1 := Real.one_rpow _
  have hMain : ‖iMain (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ‖ ≤ (A0 + 3 * C₄) * T := by
    have eq : (a * γ₁ + b * γ₂ + c₀ * γ₃) * Real.sqrt Real.pi * hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) =
        (a * γ₁ + b * γ₂ + c₀ * γ₃) * Real.sqrt Real.pi * T := by rw [hTdef]; ring
    rw [eq, h1m] at e4
    have h2 : 1 + K ^ (-(m : ℝ)) + hbS c ξ ^ (-(1 / 2 : ℝ)) ≤ 3 := by linarith
    exact tail_norm_aux e4 hC₄.le hT0 h2 (Real.sqrt_nonneg _)
  -- the dual term
  have hD := h3 (c := c) (ξ := ξ) hδ (by linarith) hξ0 (by
    have : (1 : ℝ) ≤ H := le_trans (by norm_num) (le_max_left _ _)
    exact this.trans hS)
  have hDual : ‖iDual (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ‖ ≤ C₃ / c * (ξ⁻¹ * L ^ (-(3 / 2 : ℝ))) := by
    refine hD.trans ?_
    have hc13 : 0 < c ^ (1 / 3 : ℝ) := by positivity
    have hδ1 : 0 < ceBeta1 * K * liftEps c / 2 := hδ.1
    have hbase : 1 ≤ 1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ) := by
      have := mul_pos hδ1 hc13; linarith
    have hp : (1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase (by simp)
    have hmin : min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) ≤ L ^ (-(3 / 2 : ℝ)) := min_le_right _ _
    have hLp : 0 ≤ L ^ (-(3 / 2 : ℝ)) := by positivity
    have hpow0 : 0 ≤ (1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) :=
      Real.rpow_nonneg (by linarith) _
    calc C₃ * ξ⁻¹ * (1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) * c⁻¹ * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ)))
        ≤ C₃ * ξ⁻¹ * 1 * c⁻¹ * L ^ (-(3 / 2 : ℝ)) := by
          gcongr
      _ = _ := by field_simp
  have hsum : ‖iMain (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ +
      (σ : ℂ) * iDual (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ‖ ≤
      (A0 + 3 * C₄) * T + C₃ / c * (ξ⁻¹ * L ^ (-(3 / 2 : ℝ))) := by
    refine (norm_add_le _ _).trans (add_le_add hMain ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |σ| * _ ≤ 1 * (C₃ / c * (ξ⁻¹ * L ^ (-(3 / 2 : ℝ)))) := mul_le_mul hσ1 hDual (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  refine hsum.trans (le_of_eq ?_)
  rw [hTe]
  ring

end


section

/-- `Δ⁻¹ (log kΔ)^{-3/2}` is integrable on `[Δ₁, ∞)` when `log kΔ₁ > 0`. -/
theorem integrableOn_inv_log_rpow {k Δ₁ : ℝ} (hk : 0 < k) (hΔ₁ : 0 < Δ₁) (hL : 0 < Real.log (k * Δ₁)) :
    IntegrableOn (fun Δ : ℝ => Δ⁻¹ * Real.log (k * Δ) ^ (-(3 / 2 : ℝ))) (Ioi Δ₁) := by
  set g : ℝ → ℝ := fun Δ => -2 * Real.log (k * Δ) ^ (-(1 / 2 : ℝ)) with hg
  have hpos : ∀ Δ : ℝ, Δ₁ ≤ Δ → 0 < Real.log (k * Δ) := fun Δ hΔ =>
    lt_of_lt_of_le hL (Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hΔ hk.le))
  have hder : ∀ Δ ∈ Ioi Δ₁, HasDerivAt g (Δ⁻¹ * Real.log (k * Δ) ^ (-(3 / 2 : ℝ))) Δ := by
    intro Δ hΔ
    have hΔ0 : 0 < Δ := lt_trans hΔ₁ hΔ
    have hlp := hpos Δ (le_of_lt hΔ)
    have h1 : HasDerivAt (fun x : ℝ => Real.log (k * x)) Δ⁻¹ Δ := by
      have := ((hasDerivAt_id Δ).const_mul k).log (by simp only [id_eq]; exact (mul_pos hk hΔ0).ne')
      convert this using 1
      · rfl
      · show Δ⁻¹ = k * 1 / (k * Δ)
        field_simp
    have h2 := (h1.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hlp.ne')).const_mul (-2)
    convert h2 using 1
    rw [show -(1 / 2 : ℝ) - 1 = -(3 / 2) by norm_num]
    ring
  refine integrableOn_Ioi_deriv_of_nonneg (g := g) (l := 0) ?_ hder (fun Δ hΔ => ?_) ?_
  · refine ContinuousAt.continuousWithinAt ?_
    have hΔ0 : 0 < Δ₁ := hΔ₁
    refine (continuousAt_const.mul ?_)
    refine ContinuousAt.rpow_const (ContinuousAt.log (by fun_prop) (by positivity)) (Or.inl hL.ne')
  · have := hpos Δ (le_of_lt hΔ)
    have hΔ0 : 0 < Δ := lt_trans hΔ₁ hΔ
    positivity
  · have h1 : Tendsto (fun Δ : ℝ => Real.log (k * Δ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_id.const_mul_atTop hk)
    have h2 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp h1
    have := h2.const_mul (-2)
    rw [mul_zero] at this
    exact this

end


section

/-- Finite mass from a power bound at `0` and the log-tail bound at `∞`. -/
theorem integrableOn_mass_of_bounds {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c) (hcont : ContinuousOn f (Ioi 0)) {C₀ : ℝ}
    (hC₀ : ∀ Δ : ℝ, 0 < Δ → |f Δ| ≤ C₀ * Δ ^ (-(c / 2))) {Δ₁ k C : ℝ} (hΔ₁ : 0 < Δ₁) (hk : 0 < k)
    (hL : 0 < Real.log (k * Δ₁))
    (htail : ∀ Δ : ℝ, Δ₁ ≤ Δ → |f Δ * hankelRho0 c Δ| ≤ C * (Δ⁻¹ * Real.log (k * Δ) ^ (-(3 / 2 : ℝ)))) :
    IntegrableOn (fun Δ => f Δ * hankelRho0 c Δ) (Ioi 0) := by
  have hmeas : ContinuousOn (fun Δ => f Δ * hankelRho0 c Δ) (Ioi 0) :=
    hcont.mul (continuousOn_hankelRho0 c)
  rw [← Ioc_union_Ioi_eq_Ioi (le_of_lt hΔ₁)]
  refine IntegrableOn.union ?_ ?_
  · set a : ℝ := (2 * Real.pi) ^ c / Real.Gamma c with ha
    have hint : IntegrableOn (fun Δ : ℝ => |C₀| * a * Δ ^ (c / 2 - 1)) (Ioc 0 Δ₁) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hΔ₁.le).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < c / 2 - 1))).const_mul (|C₀| * a)
    refine Integrable.mono' hint (hmeas.mono Ioc_subset_Ioi_self |>.aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with Δ hΔ
    have hΔ0 : 0 < Δ := hΔ.1
    rw [Real.norm_eq_abs, abs_mul]
    have hρ : |hankelRho0 c Δ| = a * Δ ^ (c - 1) := by
      rw [abs_of_nonneg (hankelRho0_nonneg hc hΔ0.le)]; rfl
    rw [hρ]
    have hGa : 0 ≤ a := by rw [ha]; have := Real.Gamma_pos_of_pos hc; positivity
    calc |f Δ| * (a * Δ ^ (c - 1)) ≤ (C₀ * Δ ^ (-(c / 2))) * (a * Δ ^ (c - 1)) := by
          gcongr
          exact hC₀ Δ hΔ0
      _ ≤ |C₀| * Δ ^ (-(c / 2)) * (a * Δ ^ (c - 1)) := by
          gcongr
          exact le_abs_self _
      _ = |C₀| * a * Δ ^ (c / 2 - 1) := by
          have : Δ ^ (-(c / 2)) * Δ ^ (c - 1) = Δ ^ (c / 2 - 1) := by
            rw [← Real.rpow_add hΔ0]; congr 1; ring
          calc |C₀| * Δ ^ (-(c / 2)) * (a * Δ ^ (c - 1)) = |C₀| * a * (Δ ^ (-(c / 2)) * Δ ^ (c - 1)) := by ring
            _ = _ := by rw [this]
  · have hint := (integrableOn_inv_log_rpow hk hΔ₁ hL).const_mul C
    refine Integrable.mono' hint (hmeas.mono (fun x hx => lt_of_lt_of_le hΔ₁ (le_of_lt hx)) |>.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with Δ hΔ
    rw [Real.norm_eq_abs]
    exact htail Δ (le_of_lt hΔ)

end


section

/-- **Theorem `O.11ak` for the one-level seeds** (`(ceo:O11ak.3)`, `(ceo:O11ak.4)` and `(e1)`).  For `m ≥ 3`, real `a, b, c₀`, `K ≥ 1`, `c ≥ max(2000, 8K³)`
(so the width `δ₀ = β₁ K ε / 2` is the one of `u1co:O6`, `u1co:O9p`) and `σ = ±1`, the lift `L^σ_c[X]` of `X = a f₁ + b g₁ + c₀ g₁'` is a Hankel eigenfunction
`f ∈ 𝒜_c^σ` with `c^{1/3} ρ₀(cξ) f(cξ) = I_main[X](ξ) + σ I_dual[X](ξ)` for all `ξ > 0` and `f(0) = σ ∫ f ρ₀`. -/
theorem exists_hankelEigenfn_lift {m : ℕ} (hm : 3 ≤ m) (a b c₀ : ℝ) {K c : ℝ} (hK : 1 ≤ K) (hc : 2000 ≤ c)
    (hcK : 8 * K ^ 3 ≤ c) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ f : ℝ → ℝ, IsHankelEigenfn c σ f ∧
      (∀ ξ : ℝ, 0 < ξ → ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * f (c * ξ) : ℝ) : ℂ) =
        iMain (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ +
          (σ : ℂ) * iDual (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ) ∧
      f 0 = σ * ∫ Δ in Ioi (0 : ℝ), f Δ * hankelRho0 c Δ := by
  have hc0 : 0 < c := by linarith
  have hc32 : 3 / 2 < c := by linarith
  have hX := hasU2_airySeedU2 a b c₀
  have hδ : 0 ≤ ceBeta1 * K * liftEps c / 2 := by have := ceBeta1_pos; have := liftEps_pos hc0; positivity
  have hWd := liftSymbolData_of_hasU2 hX hδ m
  set Φ := liftPhi (liftSymbol (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m) c σ with hΦdef
  have hΦ : MellinLiftData c Φ := liftPhi_mellinLiftData hWd hc32 σ hσ
  obtain ⟨C, hC0, ξ₀, hξ₀, htail⟩ := iMain_add_iDual_tail hm a b c₀ hK hc hcK σ hσ
  obtain ⟨C₀, hC₀0, hC₀⟩ := norm_liftFun_le hΦ (x₀ := c / 2) (x := c / 2) (by linarith) (by linarith) (by linarith) (by linarith)
  set ξ₁ : ℝ := max ξ₀ (Real.exp 1 / Real.pi ^ 2) with hξ₁
  have hξ₁0 : 0 < ξ₁ := lt_max_of_lt_left hξ₀
  have hmass : IntegrableOn (fun Δ => liftFun Φ (c / 2) Δ * hankelRho0 c Δ) (Ioi 0) := by
    refine integrableOn_mass_of_bounds (C := c ^ (-(1 / 3 : ℝ)) * C * c) hc0 (continuousOn_liftFun hΦ (by linarith) (by linarith))
      hC₀ (Δ₁ := c * ξ₁) (k := Real.pi ^ 2 / c) (by positivity) (by positivity) ?_ ?_
    · have : Real.pi ^ 2 / c * (c * ξ₁) = Real.pi ^ 2 * ξ₁ := by field_simp
      rw [this]
      have : Real.exp 1 ≤ Real.pi ^ 2 * ξ₁ := by
        have := le_max_right ξ₀ (Real.exp 1 / Real.pi ^ 2)
        rw [← hξ₁] at this
        rw [div_le_iff₀ (by positivity)] at this
        linarith
      exact Real.log_pos (by have := Real.exp_one_gt_d9; linarith)
    · intro Δ hΔ
      have hΔ0 : 0 < Δ := lt_of_lt_of_le (by positivity) hΔ
      set ξ := Δ / c with hξdef
      have hξpos : 0 < ξ := div_pos hΔ0 hc0
      have hξge : ξ₀ ≤ ξ := by
        have : ξ₁ ≤ ξ := by rw [hξdef, le_div_iff₀ hc0]; linarith
        exact (le_max_left _ _).trans this
      have hcξ : c * ξ = Δ := by rw [hξdef]; field_simp
      have hrepr := lift_edge_repr hX hδ m hc32 hσ hξpos
      rw [hcξ] at hrepr
      have hnorm := htail ξ hξge
      rw [← hrepr, Complex.norm_real, Real.norm_eq_abs] at hnorm
      have hlog : Real.log (Real.pi ^ 2 / c * Δ) = Real.log (Real.pi ^ 2 * ξ) := by
        congr 1; rw [hξdef]; ring
      rw [hlog]
      have hc13 : 0 < c ^ (1 / 3 : ℝ) := by positivity
      have e : |c ^ (1 / 3 : ℝ) * hankelRho0 c Δ * liftFun Φ (c / 2) Δ| = c ^ (1 / 3 : ℝ) * |liftFun Φ (c / 2) Δ * hankelRho0 c Δ| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hc13, abs_of_nonneg (hankelRho0_nonneg hc0 hΔ0.le)]
        ring
      rw [e] at hnorm
      have hΔξ : ξ⁻¹ = c * Δ⁻¹ := by rw [hξdef]; field_simp
      rw [hΔξ] at hnorm
      have h13 : c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ) = 1 := by rw [← Real.rpow_add hc0]; simp
      have := mul_le_mul_of_nonneg_left hnorm (le_of_lt (Real.rpow_pos_of_pos hc0 (-(1 / 3 : ℝ))))
      calc |liftFun Φ (c / 2) Δ * hankelRho0 c Δ|
          = c ^ (-(1 / 3 : ℝ)) * (c ^ (1 / 3 : ℝ) * |liftFun Φ (c / 2) Δ * hankelRho0 c Δ|) := by
            rw [← mul_assoc, h13, one_mul]
        _ ≤ _ := this
        _ = _ := by ring
  obtain ⟨f, hf, hfeq, hf0⟩ := exists_isHankelEigenfn_of_lift hΦ hc32 hσ (x₀ := c / 2) (by linarith) (by linarith)
    (fun z hz0 hz1 => mellinMult_liftPhi_reflect hσ hc0 hz0 hz1) hmass
  refine ⟨f, hf, ?_, ?_⟩
  · intro ξ hξ
    have h := lift_edge_repr hX hδ m hc32 hσ hξ
    rw [← h, hfeq (c * ξ) (by positivity)]
  · rw [hf0]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun Δ hΔ => ?_
    rw [hfeq Δ hΔ]

end

/-- info: 'FormalResearch.SignUncertainty.lift_edge_repr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.lift_edge_repr

/-- info: 'FormalResearch.SignUncertainty.iMain_add_iDual_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.iMain_add_iDual_tail

/-- info: 'FormalResearch.SignUncertainty.exists_hankelEigenfn_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.exists_hankelEigenfn_lift

end FormalResearch.SignUncertainty
