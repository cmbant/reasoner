module

public import FormalResearch.SignUncertainty.CeLiftBase
public import FormalResearch.SignUncertainty.CeGauss2
public import FormalResearch.SignUncertainty.GenRationalAiryTail

/-!
# General two-edge Mellin–Hankel lift assembly (`lem:ce-lift-assembly`, `ce_lift_proofs.tex`)

Assembles `ce_twoEdge_lift_of_K`: for any generalized Airy seed `X_base` satisfying the
hypotheses of `CeDualFloors` together with a left-ray `c₀ (1 + |u|)^{-3/2}` negative lower
bound, and any convolution source `S_c = convSourceFamily p γ θ lam c`, there is a threshold
`K_post ≥ 1` such that every `K ≥ K_post` yields a tuned Mellin–Hankel eigenfunction pair
`(fp c, fm c)` for `D_lift c ± S_c` (`CeTwoEdgeLiftWitness X_base p γ θ lam K`) with:
* `fm c 0 = 0 < fp c 0`;
* `0 < (fp c Δ - fm c Δ) / 2` for ALL `Δ ≥ 0` (stitching `TwoEdgeOriginBridge` + `PreEdgeTangency`
  with `ce_post_edge_convSource_unif` with zero gap);
* exact physical identity `c^{1/3} ρ₀(c ξ) (fp + fm)/2 = I_main[D_lift] + I_dual[S_c]`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- Nonnegative `WKB` upper tail on `airySeedG 0`: `(airySeedG 0 (u : ℂ)).re ≤ C * (1 + |u|)^{-3/2}`
on a left ray `u ≤ -R_g`. -/
private lemma airySeedG0_neg_ray_le :
    ∃ R_g C_g : ℝ, 5 ≤ R_g ∧ 0 < C_g ∧
      ∀ u : ℝ, u ≤ -R_g →
        (airySeedG 0 (u : ℂ)).re ≤ C_g * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨R₀, K₀, hR5, hK0, hwkb⟩ := (hasGenRationalAiryCoeffs_airySeedG 0).neg_axis_wkb
  refine ⟨R₀, (2 : ℝ) ^ (3 / 2 : ℝ) * (K₀ + 1) / Real.pi, hR5, by positivity, fun u hu => ?_⟩
  let x : ℝ := -u
  have hxR : R₀ ≤ x := by dsimp [x]; linarith
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hw := hwkb x hxR
  simp only [zero_mul, add_zero, sub_zero] at hw
  have hxw : π * x ^ (3 / 2 : ℝ) * (airySeedG 0 (u : ℂ)).re ≤ K₀ + 1 := by
    have h1 : K₀ * x ^ (-(1 / 2 : ℝ)) ≤ K₀ :=
      mul_le_of_le_one_right hK0 (Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num))
    have h2 : π * x ^ (3 / 2 : ℝ) * (airySeedG 0 ((-x : ℝ) : ℂ)).re ≤ K₀ * x ^ (-(1 / 2 : ℝ)) :=
      (abs_le.mp hw).2
    have hux : ((-x : ℝ) : ℂ) = (u : ℂ) := by dsimp [x]; simp
    rw [hux] at h2
    linarith
  have hgu : (airySeedG 0 (u : ℂ)).re ≤ ((K₀ + 1) / π) * x ^ (-(3 / 2 : ℝ)) := by
    have hinv_p : π⁻¹ * π = 1 := inv_mul_cancel₀ hpi0.ne'
    have hinv_x : x ^ (-(3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add hx0]; simp
    calc (airySeedG 0 (u : ℂ)).re
        = (π * x ^ (3 / 2 : ℝ) * (airySeedG 0 (u : ℂ)).re) * (π⁻¹ * x ^ (-(3 / 2 : ℝ))) := by
            calc (airySeedG 0 (u : ℂ)).re
                = 1 * 1 * (airySeedG 0 (u : ℂ)).re := by ring
              _ = (π⁻¹ * π) * (x ^ (-(3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ)) * (airySeedG 0 (u : ℂ)).re := by
                  rw [hinv_p, hinv_x]
              _ = (π * x ^ (3 / 2 : ℝ) * (airySeedG 0 (u : ℂ)).re) * (π⁻¹ * x ^ (-(3 / 2 : ℝ))) := by
                  ring
      _ ≤ (K₀ + 1) * (π⁻¹ * x ^ (-(3 / 2 : ℝ))) := mul_le_mul_of_nonneg_right hxw (by positivity)
      _ = ((K₀ + 1) / π) * x ^ (-(3 / 2 : ℝ)) := by ring
  have h1u : 0 < 1 + |u| := by linarith [abs_nonneg u]
  have h1x : 1 + |u| ≤ 2 * x := by
    rw [abs_of_neg (by linarith : u < 0)]
    change 1 + x ≤ 2 * x; linarith
  have hrpow : x ^ (-(3 / 2 : ℝ)) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by
    have hle := Real.rpow_le_rpow_of_nonpos h1u h1x (by norm_num : -(3 / 2 : ℝ) ≤ 0)
    rw [Real.mul_rpow (by norm_num) hx0.le] at hle
    calc x ^ (-(3 / 2 : ℝ))
        = (2 : ℝ) ^ (3 / 2 : ℝ) * ((2 : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (-(3 / 2 : ℝ))) := by
            rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; simp
      _ ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * (1 + |u|) ^ (-(3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
  calc (airySeedG 0 (u : ℂ)).re ≤ ((K₀ + 1) / π) * x ^ (-(3 / 2 : ℝ)) := hgu
    _ ≤ ((K₀ + 1) / π) * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 + |u|) ^ (-(3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hrpow (by positivity)
    _ = ((2 : ℝ) ^ (3 / 2 : ℝ) * (K₀ + 1) / π) * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by ring

/-- Tail estimate for `D_lift c + σ' * S_c` (`σ' ∈ {1, -1}`) required by `exists_hankelEigenfn_lift_general`. -/
private lemma lift_sum_tail_bound {X_base : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF_base : HasGenRationalAiryCoeffs X_base β₀₀ β₁₁)
    {p γ θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hlam : 0 < lam)
    {K c : ℝ} (hK : 1 ≤ K) (hc2k : 2000 ≤ c) (hcK : 8 * K ^ 3 ≤ c)
    (α₁ : ℝ) {σ σ' : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    let g₁ : ℝ → ℝ := fun u => (airySeedG 0 (u : ℂ)).re
    let S_c : ℝ → ℝ → ℝ := convSourceFamily p γ θ lam
    let Y : ℝ → ℝ := fun u => ((X_base (u : ℂ)).re + liftEps c * α₁ * g₁ u) + σ' * S_c c u
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∀ ξ : ℝ, ξ₀ ≤ ξ →
      ‖iMain Y (ceBeta1 * K * liftEps c / 2) 4 c ξ +
          (σ : ℂ) * iDual Y (ceBeta1 * K * liftEps c / 2) 4 c ξ‖ ≤
        C * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by
  dsimp only
  have hc0 : 0 < c := by linarith
  have hc8 : 8 ≤ c := by linarith
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  have hβ0 : 0 < ceBeta1 := ceBeta1_pos
  set δ₀ : ℝ := ceBeta1 * K * liftEps c / 2
  have hδ0 : 0 ≤ δ₀ := by positivity
  have hδ2 : δ₀ ≤ 2 := by
    have h1 := liftEps_mul_le_half (by linarith) hcK
    have h2 := ceBeta1_lt_eight
    have hKε0 : 0 ≤ K * liftEps c := mul_nonneg (by linarith) hε0.le
    calc δ₀ = ceBeta1 * (K * liftEps c) / 2 := by dsimp [δ₀]; ring
      _ ≤ 8 * (1 / 2) / 2 := by gcongr
      _ = 2 := by norm_num
  have hUX : HasU2 (fun u => (X_base (u : ℂ)).re) := hasU2_of_genRational hF_base
  have hUg : HasU2 (fun u => (airySeedG 0 (u : ℂ)).re) := by
    rw [airySeedG0_eq_ceG1]; exact hasU2_ceG1
  have hUS : HasU2 (convSourceFamily p γ θ lam c) :=
    hasU2_convSource hp hp1 (by positivity : 0 < lam * liftEps c ^ 2)
  have htX : ConvTailData (fun u => (X_base (u : ℂ)).re) δ₀ 4 c :=
    convTailData_of_genRational hF_base (by norm_num : 3 ≤ 4) ⟨hδ0, hδ2⟩ hc8
  have htG : ConvTailData (fun u => (airySeedG 0 (u : ℂ)).re) δ₀ 4 c :=
    convTailData_of_genRational (hasGenRationalAiryCoeffs_airySeedG 0) (by norm_num : 3 ≤ 4)
      ⟨hδ0, hδ2⟩ hc8
  have htS : ConvTailData (convSourceFamily p γ θ lam c) δ₀ 4 c := by
    unfold convSourceFamily
    exact convTailData_convSource hp hp1 (by positivity : 0 < lam * liftEps c ^ 2)
      (by norm_num : 3 ≤ 4) hK hc2k hcK
  obtain ⟨CXm, hCXm, ξXm, hξXm, hmX⟩ := htX.main
  obtain ⟨CXd, hCXd, ξXd, hξXd, hdX⟩ := htX.dual
  obtain ⟨CGm, hCGm, ξGm, hξGm, hmG⟩ := htG.main
  obtain ⟨CGd, hCGd, ξGd, hξGd, hdG⟩ := htG.dual
  obtain ⟨CSm, hCSm, ξSm, hξSm, hmS⟩ := htS.main
  obtain ⟨CSd, hCSd, ξSd, hξSd, hdS⟩ := htS.dual
  let β_c : ℝ := liftEps c * α₁
  let C_tot : ℝ := (CXm + CXd) + |β_c| * (CGm + CGd) + |σ'| * (CSm + CSd)
  let ξ_tot : ℝ := max (max ξXm ξXd) (max (max ξGm ξGd) (max ξSm ξSd))
  have hξ_tot : 0 < ξ_tot := lt_max_of_lt_left (lt_max_of_lt_left hξXm)
  refine ⟨C_tot, by positivity, ξ_tot, hξ_tot, fun ξ hξ => ?_⟩
  have hξ0 : 0 < ξ := lt_of_lt_of_le hξ_tot hξ
  have hσ1 : ‖(σ : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    rcases hσ with rfl | rfl <;> simp
  have hUD : HasU2 (fun u => (X_base (u : ℂ)).re + β_c * (airySeedG 0 (u : ℂ)).re) :=
    hUX.add (hUg.smul β_c)
  have hiM_split :
      iMain (fun u => ((X_base (u : ℂ)).re + β_c * (airySeedG 0 (u : ℂ)).re) +
          σ' * convSourceFamily p γ θ lam c u) δ₀ 4 c ξ =
        iMain (fun u => (X_base (u : ℂ)).re) δ₀ 4 c ξ +
          (β_c : ℂ) * iMain (fun u => (airySeedG 0 (u : ℂ)).re) δ₀ 4 c ξ +
          (σ' : ℂ) * iMain (convSourceFamily p γ θ lam c) δ₀ 4 c ξ := by
    rw [iMain_add hUD (hUS.smul σ') hδ0 4 hc0 hξ0,
      iMain_add hUX (hUg.smul β_c) hδ0 4 hc0 hξ0,
      iMain_const_mul, iMain_const_mul]
  have hiD_split :
      iDual (fun u => ((X_base (u : ℂ)).re + β_c * (airySeedG 0 (u : ℂ)).re) +
          σ' * convSourceFamily p γ θ lam c u) δ₀ 4 c ξ =
        iDual (fun u => (X_base (u : ℂ)).re) δ₀ 4 c ξ +
          (β_c : ℂ) * iDual (fun u => (airySeedG 0 (u : ℂ)).re) δ₀ 4 c ξ +
          (σ' : ℂ) * iDual (convSourceFamily p γ θ lam c) δ₀ 4 c ξ := by
    rw [iDual_add hUD (hUS.smul σ') hδ0 4 hc0 hξ0,
      iDual_add hUX (hUg.smul β_c) hδ0 4 hc0 hξ0,
      iDual_const_mul, iDual_const_mul]
  let tail : ℝ := ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))
  have h1 : ‖iMain (fun u => (X_base (u : ℂ)).re) δ₀ 4 c ξ‖ ≤ CXm * tail :=
    (hmX ξ ((le_max_left _ _).trans ((le_max_left _ _).trans hξ))).trans_eq (mul_assoc _ _ _)
  have h2 : ‖iDual (fun u => (X_base (u : ℂ)).re) δ₀ 4 c ξ‖ ≤ CXd * tail :=
    (hdX ξ ((le_max_right _ _).trans ((le_max_left _ _).trans hξ))).trans_eq (mul_assoc _ _ _)
  have h3 : ‖iMain (fun u => (airySeedG 0 (u : ℂ)).re) δ₀ 4 c ξ‖ ≤ CGm * tail :=
    (hmG ξ ((le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hξ)))).trans_eq
      (mul_assoc _ _ _)
  have h4 : ‖iDual (fun u => (airySeedG 0 (u : ℂ)).re) δ₀ 4 c ξ‖ ≤ CGd * tail :=
    (hdG ξ ((le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hξ)))).trans_eq
      (mul_assoc _ _ _)
  have h5 : ‖iMain (convSourceFamily p γ θ lam c) δ₀ 4 c ξ‖ ≤ CSm * tail :=
    (hmS ξ ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hξ)))).trans_eq
      (mul_assoc _ _ _)
  have h6 : ‖iDual (convSourceFamily p γ θ lam c) δ₀ 4 c ξ‖ ≤ CSd * tail :=
    (hdS ξ ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hξ)))).trans_eq
      (mul_assoc _ _ _)
  rw [hiM_split, hiD_split]
  have hcomb : ‖(iMain (fun u => (X_base (u : ℂ)).re) δ₀ 4 c ξ +
          (β_c : ℂ) * iMain (fun u => (airySeedG 0 (u : ℂ)).re) δ₀ 4 c ξ +
          (σ' : ℂ) * iMain (convSourceFamily p γ θ lam c) δ₀ 4 c ξ) +
        (σ : ℂ) * (iDual (fun u => (X_base (u : ℂ)).re) δ₀ 4 c ξ +
          (β_c : ℂ) * iDual (fun u => (airySeedG 0 (u : ℂ)).re) δ₀ 4 c ξ +
          (σ' : ℂ) * iDual (convSourceFamily p γ θ lam c) δ₀ 4 c ξ)‖ ≤
      ((‖iMain (fun u => (X_base (u : ℂ)).re) δ₀ 4 c ξ‖ +
          ‖(β_c : ℂ) * iMain (fun u => (airySeedG 0 (u : ℂ)).re) δ₀ 4 c ξ‖ +
          ‖(σ' : ℂ) * iMain (convSourceFamily p γ θ lam c) δ₀ 4 c ξ‖) +
        (‖iDual (fun u => (X_base (u : ℂ)).re) δ₀ 4 c ξ‖ +
          ‖(β_c : ℂ) * iDual (fun u => (airySeedG 0 (u : ℂ)).re) δ₀ 4 c ξ‖ +
          ‖(σ' : ℂ) * iDual (convSourceFamily p γ θ lam c) δ₀ 4 c ξ‖)) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    · rw [norm_mul, hσ1, one_mul]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  refine hcomb.trans ?_
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc _ ≤ (CXm * tail + |β_c| * (CGm * tail) + |σ'| * (CSm * tail)) +
          (CXd * tail + |β_c| * (CGd * tail) + |σ'| * (CSd * tail)) := by gcongr
    _ = C_tot * tail := by dsimp [C_tot]; ring
    _ = C_tot * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by dsimp [tail]; ring

/-- Pre-edge positivity `0 < fhat c Δ` up to the moving pre-edge cutoff. -/
private lemma twoEdge_preEdge_pos
    {X_base : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF_base : HasGenRationalAiryCoeffs X_base β₀₀ β₁₁)
    (hX_mass : ∫ u : ℝ, (X_base (u : ℂ)).re = 0)
    (hX_lap : ∀ y : ℝ, 0 < y → 0 ≤ airyLaplace (fun u => (X_base (u : ℂ)).re) y)
    (_hbinf : airyBetaInf X_base < 0) (_hbplus : 0 < airyBetaPlus X_base)
    (hX_neg_tail : ∃ c_neg > 0, ∃ w_neg ≤ (0 : ℝ),
      ∀ u : ℝ, u ≤ w_neg → c_neg * (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ -(X_base (u : ℂ)).re)
    {p γ θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 < γ) (hθ : 0 < θ) (hlam : 0 < lam)
    {x₀ B₀ c₁' d₀ : ℝ} (hx₀ : 0 < x₀) (hx₀B : x₀ < B₀) (hc₁' : 0 < c₁') (hd₀ : 0 < d₀)
    (hX_small : ∀ x ∈ Icc (0 : ℝ) x₀,
      c₁' * Real.sqrt x ≤ (airyTwistedLaplaceC (fun u => (X_base (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ)).re)
    (hX_tail : ∀ x : ℝ, B₀ / 2 ≤ x →
      d₀ * (1 + x) ^ (-(5 / 2 : ℝ)) ≤ (airyTwistedLaplaceC (fun u => (X_base (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ)).re)
    {K c_α_floor m_α M_α : ℝ} (hK1 : 1 ≤ K) (hc_α2k : 2000 ≤ c_α_floor)
    (hm_α : 0 < m_α) (hM_α : m_α ≤ M_α)
    (α₁ : ℝ → ℝ)
    (hα₁_bd : ∀ {c : ℝ}, c_α_floor ≤ c → m_α ≤ α₁ c ∧ α₁ c ≤ M_α) :
    ∃ U_pre c_pre : ℝ, 1 ≤ U_pre ∧ 2000 ≤ c_pre ∧ 8 * K ^ 3 ≤ c_pre ∧ c_α_floor ≤ c_pre ∧
      ∀ {c Δ : ℝ}, c_pre ≤ c → 0 ≤ Δ →
        Δ ≤ (c / π ^ 2) * Real.exp (-π ^ 2 * U_pre * c ^ (-(2 / 3 : ℝ))) →
        0 < (if Δ = 0 then
          (liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
            liftSymbol (fun u => (X_base (u : ℂ)).re + liftEps c * α₁ c * (airySeedG 0 (u : ℂ)).re)
              (ceBeta1 * K * liftEps c / 2) 4 0).re
        else
          admissLift c (fun ζ =>
            liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) 4 (ζ / (liftEps c : ℂ)) +
            liftSymbol (fun u => (X_base (u : ℂ)).re + liftEps c * α₁ c * (airySeedG 0 (u : ℂ)).re)
              (ceBeta1 * K * liftEps c / 2) 4 ((1 - ζ) / (liftEps c : ℂ))) Δ) := by
  classical
  let X : ℝ → ℝ := fun u => (X_base (u : ℂ)).re
  let g₁ : ℝ → ℝ := fun u => (airySeedG 0 (u : ℂ)).re
  let S_c : ℝ → ℝ → ℝ := convSourceFamily p γ θ lam
  have hUX : HasU2 X := hasU2_of_genRational hF_base
  have hUg : HasU2 g₁ := by
    change HasU2 (fun u => (airySeedG 0 (u : ℂ)).re)
    rw [airySeedG0_eq_ceG1]; exact hasU2_ceG1
  have hM_α_pos : 0 < M_α := hm_α.trans_le hM_α
  let D_lift : ℝ → ℝ → ℝ := fun c u => X u + liftEps c * α₁ c * g₁ u
  have hD_eq : ∀ {c u : ℝ},
      D_lift c u = X u + (liftEps c) * (∑ _i : Fin 1, α₁ c * (airySeedG 0 (u : ℂ)).re) :=
    fun {_ _} => by simp [D_lift, g₁, X, mul_assoc]
  have hZ_mass : ∀ c : ℝ, c_α_floor ≤ c →
      m_α ≤ ∫ u : ℝ, ∑ _i : Fin 1, α₁ c * (airySeedG 0 (u : ℂ)).re := fun c hc => by
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    rw [integral_const_mul, integral_airySeedG 0, mul_one]
    exact (hα₁_bd hc).1
  obtain ⟨bg, Cg_seed, hbg, _, _, hG_low⟩ := ceG1_twisted_bounds
  let z₀ : ℝ := m_α * bg * (1 + 2 * ceCs * B₀) ^ (-(9 / 2 : ℝ))
  have hz₀ : 0 < z₀ := by
    have hcs0 : 0 < ceCs := ceCs_pos
    have hB_pos : 0 < ceCs * B₀ := mul_pos hcs0 (hx₀.trans hx₀B)
    have : 0 < 1 + 2 * ceCs * B₀ := by linarith
    positivity
  have hZ_J : ∀ c : ℝ, c_α_floor ≤ c → ∀ x ∈ Icc (x₀ / 3) (2 * B₀), z₀ ≤
      (airyTwistedLaplaceC (fun u => ∑ _i : Fin 1, α₁ c * (airySeedG 0 (u : ℂ)).re)
        ((ceCs * x : ℝ) : ℂ)).re := fun c hc x hx => by
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    have hx_nn : 0 ≤ ceCs * x := mul_nonneg ceCs_pos.le (le_trans (by positivity) hx.1)
    rw [show (fun u : ℝ => α₁ c * (airySeedG 0 (u : ℂ)).re) = fun u : ℝ => α₁ c * g₁ u from rfl,
      airyTwistedLaplaceC_const_mul, airyTwistedLaplaceC_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hglow := hG_low (ceCs * x) hx_nn
    rw [← airySeedG0_eq_ceG1] at hglow
    have h1x : 1 + ceCs * x ≤ 1 + 2 * ceCs * B₀ := by
      have : ceCs * x ≤ ceCs * (2 * B₀) := mul_le_mul_of_nonneg_left hx.2 ceCs_pos.le
      linarith
    have hrp : (1 + 2 * ceCs * B₀) ^ (-(9 / 2 : ℝ)) ≤ (1 + ceCs * x) ^ (-(9 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) h1x (by norm_num)
    have hα_pos : 0 ≤ α₁ c := hm_α.le.trans (hα₁_bd hc).1
    have h1_nn : 0 ≤ (1 + 2 * ceCs * B₀) ^ (-(9 / 2 : ℝ)) :=
      Real.rpow_nonneg (by have := mul_pos ceCs_pos (hx₀.trans hx₀B); linarith) _
    calc z₀ = m_α * (bg * (1 + 2 * ceCs * B₀) ^ (-(9 / 2 : ℝ))) := by dsimp [z₀]; ring
      _ ≤ α₁ c * (bg * (1 + ceCs * x) ^ (-(9 / 2 : ℝ))) :=
          mul_le_mul (hα₁_bd hc).1 (mul_le_mul_of_nonneg_left hrp hbg.le) (mul_nonneg hbg.le h1_nn) hα_pos
      _ ≤ α₁ c * airyTwistedLaplace g₁ (ceCs * x) := mul_le_mul_of_nonneg_left hglow hα_pos
  have hdl := ce_dual_line hF_base hX_mass hX_lap (Finset.univ : Finset (Fin 1))
    (fun _ => airySeedG 0) (fun _ => 0) (fun _ => 0)
    (fun _ _ => hasGenRationalAiryCoeffs_airySeedG 0)
    (fun _ => α₁) M_α c_α_floor m_α z₀ hM_α_pos.le (by linarith : 2 ≤ c_α_floor) hm_α hz₀
    (fun _ _ c hc => abs_le.mpr ⟨by linarith [(hα₁_bd hc).1], (hα₁_bd hc).2⟩)
    hZ_mass hx₀ hx₀B hc₁' hd₀ hX_small hX_tail hZ_J hK1 (m := 4) (by norm_num)
  obtain ⟨c_D0, M_D, Λ_D, Λ_add_D, b_D, c_J, d_tail, K_D,
    hc_D0_ge, hM_D, hΛ_D, hΛ_add_D, hb_D, hc_J, hd_tail, hK_D,
    hWD_diff, hWD_real, hWD_nn, hWD_floor, _, hWD_tan_floor, hWD_A1, hWD_A2, hWD_bd⟩ := hdl
  obtain ⟨C_S, M_S, Λ_S, hCS, hM_S, hΛ_S,
    hWS_diff, hWS_real, hWS_bd_full, hWS_A1, hWS_A2⟩ :=
    convSource_preEdge_bounds hp hp1 hγ hθ.le hlam (m := 4) (by norm_num : 1 ≤ 4) hK1
  let δ₀_fn : ℝ → ℝ := fun c => ceBeta1 * K * liftEps c / 2
  let M : ℝ := max M_S M_D
  let Λ : ℝ := max Λ_S Λ_D
  let Δ₁ : ℝ := preEdgeDelta1 M Λ Λ_add_D b_D
  have hM1 : 1 ≤ M := hM_S.trans (le_max_left _ _)
  have hΛ1 : 1 ≤ Λ := hΛ_S.trans (le_max_left _ _)
  have hΔ₁_pos : 0 < Δ₁ := by positivity [one_le_preEdgeDelta1 M Λ Λ_add_D b_D]
  let fhat : ℝ → ℝ → ℝ := fun c Δ =>
    if Δ = 0 then
      (liftSymbol (S_c c) (δ₀_fn c) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
        liftSymbol (D_lift c) (δ₀_fn c) 4 0).re
    else
      admissLift c (fun ζ => liftSymbol (S_c c) (δ₀_fn c) 4 (ζ / (liftEps c : ℂ)) +
        liftSymbol (D_lift c) (δ₀_fn c) 4 ((1 - ζ) / (liftEps c : ℂ))) Δ
  let fhat_tang : ℝ → ℝ → ℝ := fun c Δ =>
    if Δ < Δ₁ then fhat c Δ else hankelRho0 c Δ * fhat c Δ
  obtain ⟨c_neg, hc_neg, w_neg, hw_neg, hX_neg⟩ := hX_neg_tail
  obtain ⟨R_g, C_g_neg, hRg5, hCg_neg, hg_neg_le⟩ := airySeedG0_neg_ray_le
  let w_cut : ℝ := min w_neg (-R_g)
  have hw_cut : w_cut ≤ 0 := le_trans (min_le_left _ _) hw_neg
  let c_neg_cut : ℝ := max (max c_D0 (max 8 (8 * K ^ 3))) ((M_α * C_g_neg / c_neg + 1) ^ 3)
  have hc_neg_D0 : c_D0 ≤ c_neg_cut := (le_max_left _ _).trans (le_max_left _ _)
  have hc_neg_α : c_α_floor ≤ c_neg_cut := hc_D0_ge.trans hc_neg_D0
  have hc_neg_2k : 2000 ≤ c_neg_cut := hc_α2k.trans hc_neg_α
  have hc_neg_K : 8 * K ^ 3 ≤ c_neg_cut :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
  let W_S : ℝ → ℂ → ℂ := fun c w => liftSymbol (S_c c) (δ₀_fn c) 4 w
  let W_D : ℝ → ℂ → ℂ := fun c w => liftSymbol (D_lift c) (δ₀_fn c) 4 w
  have hWS_bd_unif : ∀ {c : ℝ} {w : ℂ}, max 8 (8 * K ^ 3) ≤ c → 0 ≤ w.re → ‖W_S c w‖ ≤ C_S := by
    intro c w hc hw
    have hc1 : 1 ≤ c := by linarith [(le_max_left 8 (8 * K ^ 3)).trans hc]
    have h1 := hWS_bd_full hc hw
    have h2 : liftEps c ≤ 1 := liftEps_le_one hc1
    have h3 : (1 + w.re) ^ (-(9 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    calc ‖W_S c w‖ ≤ C_S * liftEps c * (1 + w.re) ^ (-(9 / 2 : ℝ)) := h1
      _ ≤ C_S * 1 * 1 := by gcongr
      _ = C_S := by ring
  have hD_neg_cut : ∀ {c u : ℝ}, c_neg_cut ≤ c → u ≤ w_cut → D_lift c u ≤ 0 := by
    intro c u hc hu
    have hu_X : u ≤ w_neg := hu.trans (min_le_left _ _)
    have hu_g : u ≤ -R_g := hu.trans (min_le_right _ _)
    have hc_α : c_α_floor ≤ c := hc_neg_α.trans hc
    have hc2k : 2000 ≤ c := hc_neg_2k.trans hc
    have hc0 : 0 < c := by linarith
    have hX_le : X u ≤ -c_neg * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by
      have h1 := hX_neg u hu_X; dsimp [X]; linarith
    have hg_le : g₁ u ≤ C_g_neg * (1 + |u|) ^ (-(3 / 2 : ℝ)) := hg_neg_le u hu_g
    have hε_le : liftEps c * α₁ c * C_g_neg ≤ c_neg := by
      have hc_cube : (M_α * C_g_neg / c_neg + 1) ^ 3 ≤ c := (le_max_right _ _).trans hc
      have hc13 : M_α * C_g_neg / c_neg ≤ c ^ (1 / 3 : ℝ) := by
        have h1 : M_α * C_g_neg / c_neg + 1 ≤ c ^ (1 / 3 : ℝ) := by
          have hpow := Real.rpow_le_rpow (by positivity) hc_cube (by norm_num : (0 : ℝ) ≤ 1 / 3)
          rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)] at hpow
          simpa using hpow
        linarith
      have hε_inv : liftEps c = (c ^ (1 / 3 : ℝ))⁻¹ := by unfold liftEps; rw [Real.rpow_neg hc0.le]
      have hεM : liftEps c * (M_α * C_g_neg) ≤ c_neg := by
        rw [hε_inv, mul_comm, ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hc0 _)]
        calc M_α * C_g_neg = c_neg * (M_α * C_g_neg / c_neg) := by field_simp [hc_neg.ne']
          _ ≤ c_neg * c ^ (1 / 3 : ℝ) := mul_le_mul_of_nonneg_left hc13 hc_neg.le
      calc liftEps c * α₁ c * C_g_neg
          ≤ liftEps c * M_α * C_g_neg := by
            gcongr; exact (liftEps_pos hc0).le; exact (hα₁_bd hc_α).2
        _ = liftEps c * (M_α * C_g_neg) := by ring
        _ ≤ c_neg := hεM
    have hrp0 : 0 ≤ (1 + |u|) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
    calc D_lift c u = X u + liftEps c * α₁ c * g₁ u := rfl
      _ ≤ (-c_neg) * (1 + |u|) ^ (-(3 / 2 : ℝ)) + (liftEps c * α₁ c) * (C_g_neg * (1 + |u|) ^ (-(3 / 2 : ℝ))) :=
          add_le_add hX_le (mul_le_mul_of_nonneg_left hg_le (mul_nonneg (liftEps_pos hc0).le (hm_α.le.trans (hα₁_bd hc_α).1)))
      _ = (liftEps c * α₁ c * C_g_neg - c_neg) * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by ring
      _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hrp0
  have hJ₀_pos : ∀ {c : ℝ}, c_neg_cut ≤ c →
      (ceK * m_α) * liftEps c ≤
        (liftSymbol (S_c c) (δ₀_fn c) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
          liftSymbol (D_lift c) (δ₀_fn c) 4 0).re := by
    intro c hc
    have hc_α : c_α_floor ≤ c := hc_neg_α.trans hc
    have hc2k : 2000 ≤ c := hc_neg_2k.trans hc
    have hcK_c : 8 * K ^ 3 ≤ c := hc_neg_K.trans hc
    have hc0 : 0 < c := by linarith
    have hUD_c : HasU2 (D_lift c) := hUX.add (hUg.smul (liftEps c * α₁ c))
    have hWD0 : liftSymbol (D_lift c) (δ₀_fn c) 4 0 = ((ceK * (liftEps c * α₁ c) : ℝ) : ℂ) := by
      have hintX : Integrable X :=
        (Complex.reCLM.integrable_comp (hUX.integrable 0 le_rfl)).congr (ae_of_all _ fun u => by simp)
      have hintG : Integrable g₁ :=
        (Complex.reCLM.integrable_comp (hUg.integrable 0 le_rfl)).congr (ae_of_all _ fun u => by simp)
      have hintD : ∫ u : ℝ, D_lift c u = liftEps c * α₁ c := by
        calc ∫ u : ℝ, D_lift c u
            = (∫ u : ℝ, X u) + ∫ u : ℝ, (liftEps c * α₁ c) * g₁ u :=
              integral_add hintX (hintG.const_mul _)
          _ = 0 + (liftEps c * α₁ c) * 1 := by
              rw [hX_mass, integral_const_mul, show (∫ u : ℝ, g₁ u) = 1 from integral_airySeedG 0]
          _ = liftEps c * α₁ c := by ring
      rw [liftSymbol_zero_eq hUD_c (δ₀_fn c) 4, hintD]
    have hWS_c : 0 < (liftSymbol (S_c c) (δ₀_fn c) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)).re :=
      (hWS_real (max_le (by linarith) hcK_c) (Real.rpow_pos_of_pos hc0 _)).2
    rw [Complex.add_re, hWD0, Complex.ofReal_re]
    have hk0 : 0 < ceK := ceK_pos
    have hα_lo : m_α ≤ α₁ c := (hα₁_bd hc_α).1
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hα_lo (liftEps_pos hc0).le) hk0.le]
  let s₂ : Finset (Fin 2) := Finset.univ
  let B₂ : Fin 2 → ℂ → ℂ := fun i => if i = 0 then X_base else airySeedG 0
  let b₂₀ : Fin 2 → ℝ := fun i => if i = 0 then β₀₀ else 0
  let b₂₁ : Fin 2 → ℝ := fun i => if i = 0 then β₁₁ else 0
  let α₂ : Fin 2 → ℝ → ℝ := fun i c => if i = 0 then 1 else liftEps c * α₁ c
  have horig_raw : Nonempty (PE3OriginData fhat (Icc 0 Δ₁)) :=
    pe3OriginData_of_twoEdge s₂ B₂ b₂₀ b₂₁
      (fun i _ => by fin_cases i <;> [exact hF_base; exact hasGenRationalAiryCoeffs_airySeedG 0])
      α₂ (R := max 1 M_α) (c_min := c_neg_cut) (w_cut := w_cut) (b_J := ceK * m_α)
      (C_S := C_S) (C_δ := ceBeta1 * K / 2) (Δ₁ := Δ₁)
      (by positivity) (by linarith) hw_cut (mul_pos ceK_pos hm_α) hCS.le
      (by have := ceBeta1_pos; positivity) hΔ₁_pos
      4 (by norm_num) δ₀_fn
      (fun {c} hc => by have := ceBeta1_pos; have := liftEps_pos (by linarith : 0 < c); positivity)
      (fun {c} _ => by dsimp [δ₀_fn]; exact le_of_eq (by ring))
      S_c (fun {c} hc => hasU2_convSource hp hp1 (by
        have := liftEps_pos (by linarith : 0 < c); positivity))
      (fun {c w} hc hw => hWS_bd_unif (max_le (by linarith) (hc_neg_K.trans hc)) hw)
      D_lift (fun {c u} => by simp [D_lift, B₂, α₂, s₂, X, g₁, Fin.sum_univ_two])
      (fun i _ c hc => by
        dsimp [α₂]; split_ifs
        · simp
        · have hc_α : c_α_floor ≤ c := hc_neg_α.trans hc
          have hc0 : 0 < c := by linarith
          have hε0 : 0 < liftEps c := liftEps_pos hc0
          have hε1 : liftEps c ≤ 1 := liftEps_le_one (by linarith)
          rw [abs_mul, abs_of_pos hε0, abs_of_nonneg (hm_α.le.trans (hα₁_bd hc_α).1)]
          exact (mul_le_of_le_one_left (hm_α.le.trans (hα₁_bd hc_α).1) hε1).trans
            ((hα₁_bd hc_α).2.trans (le_max_right _ _)))
      (fun {c u} hc hu => hD_neg_cut hc hu)
      (fun {c} hc => hJ₀_pos hc)
      fhat (fun {c} _ => by simp [fhat])
      (fun {c Δ} _ hΔ0 _ => by simp [fhat, hΔ0.ne'])
  obtain ⟨d_orig⟩ := horig_raw
  let d_orig_tang : PE3OriginData fhat_tang (Ico 0 Δ₁) :=
    { (d_orig.mono Ico_subset_Icc_self) with
      hat0 := fun hc _ => by
        dsimp [fhat_tang]; simp only [hΔ₁_pos, ↓reduceIte]
        exact d_orig.hat0 hc ⟨le_rfl, hΔ₁_pos.le⟩
      h_mellin := fun hc hΔ hΔ0 => by
        dsimp [fhat_tang]; simp only [hΔ.2, ↓reduceIte]
        exact d_orig.h_mellin hc ⟨hΔ.1, hΔ.2.le⟩ hΔ0 }
  have hW_D_eq : ∀ c : ℝ, W_D c = fun w =>
      liftSymbol (fun u => (X_base (u : ℂ)).re +
        liftEps c * ∑ _i : Fin 1, α₁ c * (airySeedG 0 (u : ℂ)).re)
        (ceBeta1 * K * liftEps c / 2) 4 w := fun c => by
    ext w
    dsimp only [W_D, δ₀_fn]
    exact congrArg (fun fn => liftSymbol fn (ceBeta1 * K * liftEps c / 2) 4 w)
      (funext fun u => hD_eq)
  have hd_tan : Nonempty (PreEdgeTangencyData fhat_tang) := by
    refine ⟨{
      W_S := W_S
      W_D := W_D
      c_min := c_neg_cut
      M := M
      Λ := Λ
      Λ_add_max := Λ_add_D
      x₀ := x₀
      b := b_D
      a_tan := x₀ / 3
      b_tan := 2 * B₀
      c_J := c_J
      C_S := C_S
      K_D := K_D
      hc_min := by linarith
      hM := hM1
      hΛ := hΛ1
      hΛ_add := hΛ_add_D
      hx₀ := hx₀
      hb := hb_D
      ha_tan := by positivity
      hab_tan := by linarith
      hc_J := hc_J
      hCS := hCS.le
      hKD := hK_D
      hW_S_diff := fun {c} hc => hWS_diff (max_le (by linarith) (hc_neg_K.trans hc))
      hW_D_diff := fun {c} hc => by rw [hW_D_eq c]; exact hWD_diff (hc_neg_D0.trans hc)
      hW_S_real := fun {c x} hc hx => (hWS_real (max_le (by linarith) (hc_neg_K.trans hc)) hx).1
      hW_D_real := fun {c x} hc hx => by rw [hW_D_eq c]; exact hWD_real (hc_neg_D0.trans hc) hx
      hW_S_nonneg := fun {c x} hc hx _ =>
        (hWS_real (max_le (by linarith) (hc_neg_K.trans hc)) hx).2.le
      hW_D_nonneg := fun {c x} hc hx hx_c => by
        rw [hW_D_eq c]; exact hWD_nn (hc_neg_D0.trans hc) hx hx_c
      hW0_pos := fun {c x_pos x_neg} hc hxp _ hxn hxn_c _ => by
        have h1 := (hWS_real (max_le (by linarith) (hc_neg_K.trans hc)) hxp).2
        have h2 : 0 ≤ (W_D c (x_neg : ℂ)).re := by
          rw [hW_D_eq c]; exact hWD_nn (hc_neg_D0.trans hc) hxn hxn_c
        linarith
      hD_floor := fun {c x} hc hx hx0 hxtan => by
        rw [hW_D_eq c]; exact hWD_floor (hc_neg_D0.trans hc) hx hx0 hxtan
      hA1_S := fun {c x y} hc hx hx_c hy => by
        have h1 := hWS_A1 (max_le (by linarith) (hc_neg_K.trans hc)) hx hx_c hy
        have hSn : 0 ≤ (W_S c (x : ℂ)).re :=
          (hWS_real (max_le (by linarith) (hc_neg_K.trans hc)) hx).2.le
        exact h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_left M_S M_D) (by norm_num))
          (div_nonneg (abs_nonneg y) hx.le)) hSn)
      hA1_D := fun {c x y} hc hx hx_c hxtan hy => by
        rw [hW_D_eq c]
        have h1 := hWD_A1 (hc_neg_D0.trans hc) hx hx_c hxtan hy
        have hDn := hWD_nn (hc_neg_D0.trans hc) hx hx_c
        exact h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_right M_S M_D) (by norm_num))
          (div_nonneg (abs_nonneg y) hx.le)) hDn)
      hA2_S := fun {c x y} hc hx hx_c => by
        have h1 := hWS_A2 (y := y) (max_le (by linarith) (hc_neg_K.trans hc)) hx hx_c
        have hSn : 0 ≤ (W_S c (x : ℂ)).re :=
          (hWS_real (max_le (by linarith) (hc_neg_K.trans hc)) hx).2.le
        exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left Λ_S Λ_D) hSn)
      hA2_D := fun {c x y} hc hx hx_c hxtan => by
        rw [hW_D_eq c]
        have h1 := hWD_A2 (y := y) (hc_neg_D0.trans hc) hx hx_c hxtan
        have hDn := hWD_nn (hc_neg_D0.trans hc) hx hx_c
        refine h1.trans (add_le_add (mul_le_mul_of_nonneg_right (le_max_right Λ_S Λ_D) hDn) le_rfl)
      hD_tan_floor := fun {c x} hc hxtan hx_c => by
        rw [hW_D_eq c]; exact hWD_tan_floor (hc_neg_D0.trans hc) hxtan hx_c
      hW_S_bd := fun {c w} hc hw => hWS_bd_unif (max_le (by linarith) (hc_neg_K.trans hc)) hw.le
      hW_D_bd := fun {c w} hc hw => by
        rw [hW_D_eq c]; exact hWD_bd (hc_neg_D0.trans hc) hw
      orig := d_orig_tang
      h_saddle := fun {c Δ ξ σ_star} hc hΔ1 _ hξ hσ0 hσ1 _ => by
        have hnot : ¬ (Δ < Δ₁) := not_lt.mpr hΔ1
        have hΔ0 : 0 < Δ := lt_of_lt_of_le hΔ₁_pos hΔ1
        have hc4 : 4 ≤ c := by linarith [hc_neg_2k.trans hc]
        have hc0 : 0 < c := by linarith
        have hξ0 : 0 < ξ := by rw [hξ]; exact div_pos hΔ0 hc0
        have hcξ : c * ξ = Δ := by rw [hξ]; field_simp [hc0.ne']
        have hUD_c : HasU2 (D_lift c) := hUX.add (hUg.smul (liftEps c * α₁ c))
        have hUS_c : HasU2 (S_c c) :=
          hasU2_convSource hp hp1 (by have := liftEps_pos hc0; positivity)
        have hδ0_c : 0 ≤ δ₀_fn c := by
          unfold δ₀_fn; have := liftEps_pos hc0; have := ceBeta1_pos; positivity
        have hsm := twoEdge_W_tilde_stripM1 (S := fun _ => S_c c) (D := fun _ => D_lift c)
          (δ₀ := fun _ => δ₀_fn c) (m := 4) hc4 hUS_c hUD_c hδ0_c
        have hrep := admiss_vert_rep (by linarith : 1 ≤ c) hsm hσ0.le hσ1 hξ0
        simp only [fhat_tang, fhat, hnot, hΔ0.ne', ↓reduceIte]; rw [← hcξ]
        have hre := congrArg Complex.re hrep
        rw [Complex.ofReal_re] at hre
        rw [hre]
        unfold lobeSaddleIntegral W_S W_D
        have hε_eq : (c ^ (-(1 / 3 : ℝ)) : ℝ) = liftEps c := rfl
        simp_rw [hε_eq] }⟩
  obtain ⟨d_tan⟩ := hd_tan
  obtain ⟨U_pre, hU_pre, c_pre, hc_pre2, hpre_pos⟩ := preEdge_tangency_pos d_tan
  refine ⟨U_pre, max c_neg_cut c_pre, hU_pre,
    hc_neg_2k.trans (le_max_left _ _), hc_neg_K.trans (le_max_left _ _),
    hc_neg_α.trans (le_max_left _ _), fun {c Δ} hc hΔ hΔ_le => ?_⟩
  have hpos_t := hpre_pos c ((le_max_right _ _).trans hc) Δ ⟨hΔ, hΔ_le⟩
  have hc0 : 0 < c := by linarith [hc_neg_2k.trans ((le_max_left _ _).trans hc)]
  dsimp [fhat_tang] at hpos_t
  by_cases hlt : Δ < Δ₁
  · simpa [hlt, fhat, S_c, D_lift, δ₀_fn, X, g₁] using hpos_t
  · simp only [hlt, ↓reduceIte] at hpos_t
    have hΔ0 : 0 < Δ := lt_of_lt_of_le hΔ₁_pos (not_lt.mp hlt)
    have hpos_f := pos_of_mul_pos_right hpos_t (hankelRho0_pos hc0 hΔ0).le
    simpa [fhat, S_c, D_lift, δ₀_fn, X, g₁] using hpos_f

/-- Pre-edge + post-edge strict positivity `0 < fhat c Δ` for all `Δ ≥ 0` above an explicit `c_min`. -/
private lemma twoEdge_fhat_pos
    {X_base : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF_base : HasGenRationalAiryCoeffs X_base β₀₀ β₁₁)
    (hX_mass : ∫ u : ℝ, (X_base (u : ℂ)).re = 0)
    (hX_lap : ∀ y : ℝ, 0 < y → 0 ≤ airyLaplace (fun u => (X_base (u : ℂ)).re) y)
    (hbinf : airyBetaInf X_base < 0) (hbplus : 0 < airyBetaPlus X_base)
    (hX_neg_tail : ∃ c_neg > 0, ∃ w_neg ≤ (0 : ℝ),
      ∀ u : ℝ, u ≤ w_neg → c_neg * (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ -(X_base (u : ℂ)).re)
    {p γ θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 < γ) (hθ : 0 < θ) (hlam : 0 < lam)
    {x₀ B₀ c₁' d₀ : ℝ} (hx₀ : 0 < x₀) (hx₀B : x₀ < B₀) (hc₁' : 0 < c₁') (hd₀ : 0 < d₀)
    (hX_small : ∀ x ∈ Icc (0 : ℝ) x₀,
      c₁' * Real.sqrt x ≤ (airyTwistedLaplaceC (fun u => (X_base (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ)).re)
    (hX_tail : ∀ x : ℝ, B₀ / 2 ≤ x →
      d₀ * (1 + x) ^ (-(5 / 2 : ℝ)) ≤ (airyTwistedLaplaceC (fun u => (X_base (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ)).re)
    {K c_α_floor m_α M_α : ℝ} (hK1 : 1 ≤ K) (hc_α2k : 2000 ≤ c_α_floor)
    (hm_α : 0 < m_α) (hM_α : m_α ≤ M_α)
    (α₁ : ℝ → ℝ)
    (hα₁_bd : ∀ {c : ℝ}, c_α_floor ≤ c → m_α ≤ α₁ c ∧ α₁ c ≤ M_α)
    (hα₁_all : ∀ {c : ℝ}, m_α ≤ α₁ c ∧ α₁ c ≤ M_α)
    {CX Cg κ₀ : ℝ}
    (hCX : ∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC (fun u => (X_base (u : ℂ)).re) ((ceCs : ℂ) * w)‖ ≤ CX * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    (hCg : ∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC (fun u => (airySeedG 0 (u : ℂ)).re) ((ceCs : ℂ) * w)‖ ≤ Cg * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    (hκ_ge : κ₀ ≤ ceBeta1 * K / 2)
    (hpost_unif : ∀ {κ : ℝ}, κ₀ ≤ κ → ∀ {U : ℝ}, 0 ≤ U → ∀ {D : ℝ → ℝ → ℝ},
      (∀ {c : ℝ}, 2 ≤ c → DifferentiableOn ℂ (airyTwistedLaplaceC (D c)) {y : ℂ | 0 < y.re}) →
      (∀ {c : ℝ} {w : ℂ}, 2 ≤ c → 0 ≤ w.re →
        ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤ (CX + M_α * Cg) * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) →
      ∃ c₀ ≥ (2 : ℝ), ∀ {c ξ : ℝ}, c₀ ≤ c → 0 < ξ → -U ≤ hbS c ξ →
        0 < (iMain (convSourceFamily p γ θ lam c) (κ * liftEps c) 4 c ξ +
          iDual (D c) (κ * liftEps c) 4 c ξ).re) :
    ∃ c_min : ℝ, 2000 ≤ c_min ∧ 8 * K ^ 3 ≤ c_min ∧ c_α_floor ≤ c_min ∧
      ∀ {c Δ : ℝ}, c_min ≤ c → 0 ≤ Δ →
        0 < (if Δ = 0 then
          (liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
            liftSymbol (fun u => (X_base (u : ℂ)).re + liftEps c * α₁ c * (airySeedG 0 (u : ℂ)).re)
              (ceBeta1 * K * liftEps c / 2) 4 0).re
        else
          admissLift c (fun ζ =>
            liftSymbol (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) 4 (ζ / (liftEps c : ℂ)) +
            liftSymbol (fun u => (X_base (u : ℂ)).re + liftEps c * α₁ c * (airySeedG 0 (u : ℂ)).re)
              (ceBeta1 * K * liftEps c / 2) 4 ((1 - ζ) / (liftEps c : ℂ))) Δ) := by
  classical
  let X : ℝ → ℝ := fun u => (X_base (u : ℂ)).re
  let g₁ : ℝ → ℝ := fun u => (airySeedG 0 (u : ℂ)).re
  let S_c : ℝ → ℝ → ℝ := convSourceFamily p γ θ lam
  let D_lift : ℝ → ℝ → ℝ := fun c u => X u + liftEps c * α₁ c * g₁ u
  let δ₀_fn : ℝ → ℝ := fun c => ceBeta1 * K * liftEps c / 2
  let fhat : ℝ → ℝ → ℝ := fun c Δ =>
    if Δ = 0 then
      (liftSymbol (S_c c) (δ₀_fn c) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
        liftSymbol (D_lift c) (δ₀_fn c) 4 0).re
    else
      admissLift c (fun ζ => liftSymbol (S_c c) (δ₀_fn c) 4 (ζ / (liftEps c : ℂ)) +
        liftSymbol (D_lift c) (δ₀_fn c) 4 ((1 - ζ) / (liftEps c : ℂ))) Δ
  have hUX : HasU2 X := hasU2_of_genRational hF_base
  have hUg : HasU2 g₁ := by
    change HasU2 (fun u => (airySeedG 0 (u : ℂ)).re)
    rw [airySeedG0_eq_ceG1]; exact hasU2_ceG1
  have hM_α_pos : 0 < M_α := hm_α.trans_le hM_α
  let CD : ℝ := CX + M_α * Cg
  let κ : ℝ := ceBeta1 * K / 2
  obtain ⟨U_pre, c_pre, hU_pre, hc_pre_2k, hc_pre_K, hc_pre_α, hpre_pos⟩ :=
    twoEdge_preEdge_pos hF_base hX_mass hX_lap hbinf hbplus hX_neg_tail hp hp1 hγ hθ hlam
      hx₀ hx₀B hc₁' hd₀ hX_small hX_tail hK1 hc_α2k hm_α hM_α α₁ hα₁_bd
  have hdiffD : ∀ {c : ℝ}, 2 ≤ c → DifferentiableOn ℂ (airyTwistedLaplaceC (D_lift c)) {y : ℂ | 0 < y.re} :=
    fun {c} _ => (hUX.add (hUg.smul (liftEps c * α₁ c))).differentiable
  have hbdD : ∀ {c : ℝ} {w : ℂ}, 2 ≤ c → 0 ≤ w.re →
      ‖airyTwistedLaplaceC (D_lift c) ((ceCs : ℂ) * w)‖ ≤ CD * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
    intro c w hc hw
    have hc0 : 0 < c := by linarith
    have hε0 : 0 < liftEps c := liftEps_pos hc0
    have hε1 : liftEps c ≤ 1 := liftEps_le_one (by linarith)
    have hre : 0 ≤ ((ceCs : ℂ) * w).re := by
      simpa [Complex.mul_re] using mul_nonneg ceCs_pos.le hw
    rw [show D_lift c = fun u => X u + (liftEps c * α₁ c) * g₁ u from rfl,
      airyTwistedLaplaceC_add (hUX.integrable _ hre) ((hUg.smul _).integrable _ hre),
      airyTwistedLaplaceC_const_mul]
    have h1 := hCX w hw
    have h2 := hCg w hw
    have hα_bd : |liftEps c * α₁ c| ≤ M_α := by
      rw [abs_mul, abs_of_pos hε0, abs_of_nonneg (hm_α.le.trans hα₁_all.1)]
      exact (mul_le_of_le_one_left (hm_α.le.trans hα₁_all.1) hε1).trans hα₁_all.2
    calc ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w) +
            ((liftEps c * α₁ c : ℝ) : ℂ) * airyTwistedLaplaceC g₁ ((ceCs : ℂ) * w)‖
        ≤ ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ +
            ‖((liftEps c * α₁ c : ℝ) : ℂ) * airyTwistedLaplaceC g₁ ((ceCs : ℂ) * w)‖ := norm_add_le _ _
      _ ≤ CX * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) + M_α * (Cg * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) := by
          refine add_le_add h1 ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul hα_bd h2 (norm_nonneg _) hM_α_pos.le
      _ = CD * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by dsimp [CD]; ring
  obtain ⟨c_post, hc_post2, hpost⟩ :=
    hpost_unif hκ_ge (by linarith : 0 ≤ U_pre) hdiffD hbdD
  let c_min : ℝ := max c_pre c_post
  refine ⟨c_min, hc_pre_2k.trans (le_max_left _ _), hc_pre_K.trans (le_max_left _ _),
    hc_pre_α.trans (le_max_left _ _), fun {c Δ} hc hΔ => ?_⟩
  have hc_pre : c_pre ≤ c := (le_max_left _ _).trans hc
  have hc_post : c_post ≤ c := (le_max_right _ _).trans hc
  have hc4 : 4 ≤ c := by linarith [hc_pre_2k.trans hc_pre]
  have hc0 : 0 < c := by linarith
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  let Δ_cut : ℝ := (c / π ^ 2) * Real.exp (-π ^ 2 * U_pre * c ^ (-(2 / 3 : ℝ)))
  rcases le_or_gt Δ Δ_cut with hΔ_le | hΔ_gt
  · exact hpre_pos hc_pre hΔ hΔ_le
  · have hΔ_cut0 : 0 ≤ Δ_cut := by dsimp [Δ_cut]; positivity
    have hΔ0 : 0 < Δ := lt_of_le_of_lt hΔ_cut0 hΔ_gt
    let ξ : ℝ := Δ / c
    have hξ0 : 0 < ξ := div_pos hΔ0 hc0
    have hcξ : c * ξ = Δ := by dsimp [ξ]; field_simp [hc0.ne']
    have hexp : Real.exp (-π ^ 2 * U_pre * c ^ (-(2 / 3 : ℝ))) < π ^ 2 * ξ := by
      have h1 : Δ_cut * (π ^ 2 / c) = Real.exp (-π ^ 2 * U_pre * c ^ (-(2 / 3 : ℝ))) := by
        dsimp [Δ_cut]; field_simp [hc0.ne', Real.pi_pos.ne']
      have h2 : Δ * (π ^ 2 / c) = π ^ 2 * ξ := by
        dsimp [ξ]; field_simp [hc0.ne']
      calc Real.exp (-π ^ 2 * U_pre * c ^ (-(2 / 3 : ℝ)))
          = Δ_cut * (π ^ 2 / c) := h1.symm
        _ < Δ * (π ^ 2 / c) := mul_lt_mul_of_pos_right hΔ_gt (by positivity)
        _ = π ^ 2 * ξ := h2
    have hlog_gt : -π ^ 2 * U_pre * c ^ (-(2 / 3 : ℝ)) < Real.log (π ^ 2 * ξ) := by
      calc -π ^ 2 * U_pre * c ^ (-(2 / 3 : ℝ))
          = Real.log (Real.exp (-π ^ 2 * U_pre * c ^ (-(2 / 3 : ℝ)))) := (Real.log_exp _).symm
        _ < Real.log (π ^ 2 * ξ) := Real.log_lt_log (Real.exp_pos _) hexp
    have hc23_eq : c ^ (-(2 / 3 : ℝ)) = liftEps c ^ 2 := by
      unfold liftEps; rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hc0.le]; norm_num
    have hUlo : -U_pre ≤ hbS c ξ := by
      rw [log_eq_hbS hc0, hc23_eq] at hlog_gt
      have hden : 0 < π ^ 2 * liftEps c ^ 2 := by positivity
      have h1 : (-U_pre) * (π ^ 2 * liftEps c ^ 2) < (hbS c ξ) * (π ^ 2 * liftEps c ^ 2) := by
        linarith
      exact le_of_lt (lt_of_mul_lt_mul_right h1 hden.le)
    have hpost_pos := hpost hc_post hξ0 hUlo
    have hδ0_c : 0 ≤ δ₀_fn c := by have := ceBeta1_pos; positivity
    have hκ_eq : κ * liftEps c = δ₀_fn c := by dsimp [κ, δ₀_fn]; ring
    rw [hκ_eq] at hpost_pos
    have hUD_c : HasU2 (D_lift c) := hUX.add (hUg.smul (liftEps c * α₁ c))
    have hUS_c : HasU2 (S_c c) := hasU2_convSource hp hp1 (by positivity)
    have heq := congrArg Complex.re (admissLift_twoEdge_eq hUS_c hUD_c hδ0_c 4 hc4 hξ0)
    rw [Complex.ofReal_re] at heq
    simp only [hΔ0.ne', ↓reduceIte]; rw [← hcξ]
    have hmul : 0 < c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) *
        admissLift c (fun ζ => liftSymbol (S_c c) (δ₀_fn c) 4 (ζ / (liftEps c : ℂ)) +
          liftSymbol (D_lift c) (δ₀_fn c) 4 ((1 - ζ) / (liftEps c : ℂ))) (c * ξ) := by
      rw [heq]; exact hpost_pos
    exact pos_of_mul_pos_right hmul (mul_pos (Real.rpow_pos_of_pos hc0 _)
      (hankelRho0_pos hc0 (by positivity))).le

/-- **Uniform-amplitude variant of `lem:ce-lift-assembly` (`ce_lift_proofs.tex`):**
exposes a single upper bound `M_α_unif > 0` independent of `K ≥ K_post` with `W.M_α ≤ M_α_unif`. -/
theorem ce_twoEdge_lift_unif_of_K
    {X_base : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF_base : HasGenRationalAiryCoeffs X_base β₀₀ β₁₁)
    (hX_mass : ∫ u : ℝ, (X_base (u : ℂ)).re = 0)
    (hX_lap : ∀ y : ℝ, 0 < y → 0 ≤ airyLaplace (fun u => (X_base (u : ℂ)).re) y)
    (hbinf : airyBetaInf X_base < 0) (hbplus : 0 < airyBetaPlus X_base)
    (hX_neg_tail : ∃ c_neg > 0, ∃ w_neg ≤ (0 : ℝ),
      ∀ u : ℝ, u ≤ w_neg → c_neg * (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ -(X_base (u : ℂ)).re)
    {p γ θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 < γ) (hθ : 0 < θ) (hlam : 0 < lam) :
    ∃ M_α_unif > (0 : ℝ), ∃ K_post ≥ (1 : ℝ), ∀ K : ℝ, K_post ≤ K →
      ∃ W : CeTwoEdgeLiftWitness X_base p γ θ lam K, W.M_α ≤ M_α_unif := by
  classical
  let X : ℝ → ℝ := fun u => (X_base (u : ℂ)).re
  let g₁ : ℝ → ℝ := fun u => (airySeedG 0 (u : ℂ)).re
  let S_c : ℝ → ℝ → ℝ := convSourceFamily p γ θ lam
  let D₀ : ℝ → ℝ → ℝ := fun c u => X u + (∫ v : ℝ, S_c c v) * g₁ u
  have hUX : HasU2 X := hasU2_of_genRational hF_base
  have hUg : HasU2 g₁ := by
    change HasU2 (fun u => (airySeedG 0 (u : ℂ)).re)
    rw [airySeedG0_eq_ceG1]; exact hasU2_ceG1
  obtain ⟨x₀, B₀, c₁', d₀, hx₀, hx₀B, hc₁', hd₀, hX_small, hX_tail⟩ :=
    ce_dual_floors hF_base hX_mass hbinf hbplus
  obtain ⟨m₀, M₀, hm₀, hM₀, hmass⟩ := convSourceFamily_mass hp hp1 hγ hθ.le hlam
  let m_α : ℝ := m₀ / 2
  let M_α : ℝ := M₀ + m₀ / 2
  have hm_α : 0 < m_α := by positivity
  have hM_α : m_α ≤ M_α := by dsimp [m_α, M_α]; linarith
  have hM_α_pos : 0 < M_α := hm_α.trans_le hM_α
  obtain ⟨c_η, C_η, hc_η2k, hC_η, hη_prop⟩ :=
    eta_tune_convSource hUX hX_mass hp hp1 hγ hθ.le hlam 4
  let c_α_floor : ℝ := max c_η ((2 * C_η / m₀ + 1) ^ 2)
  have hc_α2k : 2000 ≤ c_α_floor := hc_η2k.trans (le_max_left _ _)
  obtain ⟨CX, hCX0, hCX⟩ := hUX.rhp
  obtain ⟨Cg, hCg0, hCg⟩ := hUg.rhp
  let CD : ℝ := CX + M_α * Cg
  have hCD : 0 ≤ CD := by positivity
  obtain ⟨κ₀, hκ₀, hpost_unif⟩ :=
    ce_post_edge_convSource_unif hp hp1 hγ hθ hlam (m := 4) (by norm_num) hCD
  let K_post : ℝ := max 1 (2 * κ₀ / ceBeta1)
  have hK_post1 : 1 ≤ K_post := le_max_left _ _
  refine ⟨M_α, hM_α_pos, K_post, hK_post1, fun K hK => ?_⟩
  have hK1 : 1 ≤ K := hK_post1.trans hK
  have hβ0 : 0 < ceBeta1 := ceBeta1_pos
  have hκ_ge : κ₀ ≤ ceBeta1 * K / 2 := by
    have hK2 : 2 * κ₀ / ceBeta1 ≤ K := (le_max_right _ _).trans hK
    calc κ₀ = ceBeta1 * (2 * κ₀ / ceBeta1) / 2 := by field_simp [hβ0.ne']
      _ ≤ ceBeta1 * K / 2 := by gcongr
  let η_fn : ℝ → ℝ := fun c =>
    if hc : c_η ≤ c then Classical.choose (hη_prop hK1 hc) else 0
  have hη_spec : ∀ {c : ℝ}, c_η ≤ c →
      liftSymbol (fun u => (D₀ c u - S_c c u) + η_fn c * g₁ u)
          (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) -
        liftSymbol (fun u => (D₀ c u - S_c c u) + η_fn c * g₁ u)
          (ceBeta1 * K * liftEps c / 2) 4 0 = 0 ∧
      |η_fn c| ≤ C_η * c ^ (-(5 / 6 : ℝ)) := fun {c} hc => by
    dsimp [η_fn]; split_ifs
    exact Classical.choose_spec (hη_prop hK1 hc)
  let α₁ : ℝ → ℝ := fun c =>
    if c_α_floor ≤ c then ((∫ v : ℝ, S_c c v) + η_fn c) / liftEps c else m_α
  have hα₁_bd : ∀ {c : ℝ}, c_α_floor ≤ c → m_α ≤ α₁ c ∧ α₁ c ≤ M_α := by
    intro c hc
    have hc_η : c_η ≤ c := (le_max_left _ _).trans hc
    have hc2k : 2000 ≤ c := hc_η2k.trans hc_η
    have hc0 : 0 < c := by linarith
    have hε0 : 0 < liftEps c := liftEps_pos hc0
    have hM_c := hmass hc2k
    have hη_bd := (hη_spec hc_η).2
    have hη_eps : |η_fn c| ≤ (m₀ / 2) * liftEps c := by
      have hsqrt : 2 * C_η / m₀ ≤ √c := by
        have h1 : 2 * C_η / m₀ + 1 ≤ √c := by
          rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * C_η / m₀ + 1)]
          exact Real.sqrt_le_sqrt ((le_max_right _ _).trans hc)
        linarith
      have hc12 : c ^ (-(1 / 2 : ℝ)) ≤ m₀ / (2 * C_η) := by
        rw [show c ^ (-(1 / 2 : ℝ)) = 1 / √c by rw [Real.sqrt_eq_rpow, Real.rpow_neg hc0.le, ← one_div],
          div_le_iff₀ (Real.sqrt_pos.mpr hc0)]
        calc 1 = (m₀ / (2 * C_η)) * (2 * C_η / m₀) := by field_simp [hm₀.ne', hC_η.ne']
          _ ≤ (m₀ / (2 * C_η)) * √c := mul_le_mul_of_nonneg_left hsqrt (by positivity)
      have hc56_eq : c ^ (-(5 / 6 : ℝ)) = liftEps c * c ^ (-(1 / 2 : ℝ)) := by
        unfold liftEps; rw [← Real.rpow_add hc0]; norm_num
      calc |η_fn c| ≤ C_η * (liftEps c * c ^ (-(1 / 2 : ℝ))) := hc56_eq ▸ hη_bd
        _ ≤ C_η * (liftEps c * (m₀ / (2 * C_η))) := by gcongr
        _ = (m₀ / 2) * liftEps c := by field_simp [hC_η.ne']
    have hlo_η : -(m₀ / 2) * liftEps c ≤ η_fn c := by linarith [(abs_le.mp hη_eps).1]
    have hhi_η : η_fn c ≤ (m₀ / 2) * liftEps c := (abs_le.mp hη_eps).2
    dsimp [α₁]; split_ifs
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hε0]; dsimp [m_α]; linarith [hM_c.1]
    · rw [div_le_iff₀ hε0]; dsimp [M_α]; linarith [hM_c.2]
  have hα₁_all : ∀ {c : ℝ}, m_α ≤ α₁ c ∧ α₁ c ≤ M_α := fun {c} => by
    by_cases hc : c_α_floor ≤ c
    · exact hα₁_bd hc
    · dsimp [α₁]; split_ifs; exact ⟨le_rfl, hM_α⟩
  obtain ⟨c_min, hc_min_2k, hc_min_K, hc_min_α, hfhat_pos⟩ :=
    twoEdge_fhat_pos hF_base hX_mass hX_lap hbinf hbplus hX_neg_tail hp hp1 hγ hθ hlam
      hx₀ hx₀B hc₁' hd₀ hX_small hX_tail hK1 hc_α2k hm_α hM_α α₁ hα₁_bd hα₁_all
      hCX hCg hκ_ge hpost_unif
  let δ₀_fn : ℝ → ℝ := fun c => ceBeta1 * K * liftEps c / 2
  let D_lift : ℝ → ℝ → ℝ := fun c u => X u + liftEps c * α₁ c * g₁ u
  let fhat : ℝ → ℝ → ℝ := fun c Δ =>
    if Δ = 0 then
      (liftSymbol (S_c c) (δ₀_fn c) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
        liftSymbol (D_lift c) (δ₀_fn c) 4 0).re
    else
      admissLift c (fun ζ => liftSymbol (S_c c) (δ₀_fn c) 4 (ζ / (liftEps c : ℂ)) +
        liftSymbol (D_lift c) (δ₀_fn c) 4 ((1 - ζ) / (liftEps c : ℂ))) Δ
  have hp_exists : ∀ c : ℝ, c_min ≤ c →
      ∃ f : ℝ → ℝ, IsHankelEigenfn c 1 f ∧
        (∀ ξ : ℝ, 0 < ξ → ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * f (c * ξ) : ℝ) : ℂ) =
          iMain (fun u => D_lift c u + S_c c u) (δ₀_fn c) 4 c ξ +
            (1 : ℂ) * iDual (fun u => D_lift c u + S_c c u) (δ₀_fn c) 4 c ξ) ∧
        ((f 0 : ℝ) : ℂ) = liftSymbol (fun u => D_lift c u + S_c c u) (δ₀_fn c) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
          (1 : ℂ) * liftSymbol (fun u => D_lift c u + S_c c u) (δ₀_fn c) 4 0 := by
    intro c hc
    have hc2k : 2000 ≤ c := hc_min_2k.trans hc
    have hcK_c : 8 * K ^ 3 ≤ c := hc_min_K.trans hc
    have hc0 : 0 < c := by linarith
    have hUD_c : HasU2 (D_lift c) := hUX.add (hUg.smul (liftEps c * α₁ c))
    have hUS_c : HasU2 (S_c c) :=
      hasU2_convSource hp hp1 (by have := liftEps_pos hc0; positivity)
    have hδ0_c : 0 ≤ δ₀_fn c := by
      have := ceBeta1_pos; have := liftEps_pos hc0; positivity
    have htail_p := lift_sum_tail_bound hF_base hp hp1 (γ := γ) (θ := θ) hlam hK1 hc2k hcK_c
      (α₁ c) (σ := 1) (σ' := 1) (Or.inl rfl)
    obtain ⟨f, hf, hfeq, _, hf0⟩ := exists_hankelEigenfn_lift_general
      (X := fun u => D_lift c u + S_c c u) (hUD_c.add hUS_c) hδ0_c 4 (c := c) (by linarith) (Or.inl rfl)
      (by simpa [one_mul] using htail_p)
    exact ⟨f, hf, by simpa using hfeq, by simpa using hf0⟩
  have hm_exists : ∀ c : ℝ, c_min ≤ c →
      ∃ f : ℝ → ℝ, IsHankelEigenfn c (-1) f ∧
        (∀ ξ : ℝ, 0 < ξ → ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * f (c * ξ) : ℝ) : ℂ) =
          iMain (fun u => D_lift c u - S_c c u) (δ₀_fn c) 4 c ξ +
            (-1 : ℂ) * iDual (fun u => D_lift c u - S_c c u) (δ₀_fn c) 4 c ξ) ∧
        ((f 0 : ℝ) : ℂ) = liftSymbol (fun u => D_lift c u - S_c c u) (δ₀_fn c) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
          (-1 : ℂ) * liftSymbol (fun u => D_lift c u - S_c c u) (δ₀_fn c) 4 0 := by
    intro c hc
    have hc2k : 2000 ≤ c := hc_min_2k.trans hc
    have hcK_c : 8 * K ^ 3 ≤ c := hc_min_K.trans hc
    have hc0 : 0 < c := by linarith
    have hUD_c : HasU2 (D_lift c) := hUX.add (hUg.smul (liftEps c * α₁ c))
    have hUS_c : HasU2 (S_c c) :=
      hasU2_convSource hp hp1 (by have := liftEps_pos hc0; positivity)
    have hδ0_c : 0 ≤ δ₀_fn c := by
      have := ceBeta1_pos; have := liftEps_pos hc0; positivity
    have htail_m := lift_sum_tail_bound hF_base hp hp1 (γ := γ) (θ := θ) hlam hK1 hc2k hcK_c
      (α₁ c) (σ := -1) (σ' := -1) (Or.inr rfl)
    have hfn : (fun u => D_lift c u - S_c c u) = fun u => D_lift c u + (-1) * S_c c u := by
      ext u; ring
    obtain ⟨f, hf, hfeq, _, hf0⟩ := exists_hankelEigenfn_lift_general
      (X := fun u => D_lift c u - S_c c u) (by rw [hfn]; exact hUD_c.add (hUS_c.smul (-1)))
      hδ0_c 4 (c := c) (by linarith) (Or.inr rfl) (by simpa [sub_eq_add_neg] using htail_m)
    exact ⟨f, hf, by simpa using hfeq, by simpa using hf0⟩
  let fp : ℝ → ℝ → ℝ := fun c => if hc : c_min ≤ c then Classical.choose (hp_exists c hc) else fun _ => 0
  let fm : ℝ → ℝ → ℝ := fun c => if hc : c_min ≤ c then Classical.choose (hm_exists c hc) else fun _ => 0
  have hfp_spec : ∀ {c : ℝ}, c_min ≤ c → IsHankelEigenfn c 1 (fp c) ∧
      (∀ ξ : ℝ, 0 < ξ → ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * fp c (c * ξ) : ℝ) : ℂ) =
        iMain (fun u => D_lift c u + S_c c u) (δ₀_fn c) 4 c ξ +
          (1 : ℂ) * iDual (fun u => D_lift c u + S_c c u) (δ₀_fn c) 4 c ξ) ∧
      ((fp c 0 : ℝ) : ℂ) = liftSymbol (fun u => D_lift c u + S_c c u) (δ₀_fn c) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
        (1 : ℂ) * liftSymbol (fun u => D_lift c u + S_c c u) (δ₀_fn c) 4 0 := fun {c} hc => by
    dsimp [fp]; split_ifs; exact Classical.choose_spec (hp_exists c hc)
  have hfm_spec : ∀ {c : ℝ}, c_min ≤ c → IsHankelEigenfn c (-1) (fm c) ∧
      (∀ ξ : ℝ, 0 < ξ → ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * fm c (c * ξ) : ℝ) : ℂ) =
        iMain (fun u => D_lift c u - S_c c u) (δ₀_fn c) 4 c ξ +
          (-1 : ℂ) * iDual (fun u => D_lift c u - S_c c u) (δ₀_fn c) 4 c ξ) ∧
      ((fm c 0 : ℝ) : ℂ) = liftSymbol (fun u => D_lift c u - S_c c u) (δ₀_fn c) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
        (-1 : ℂ) * liftSymbol (fun u => D_lift c u - S_c c u) (δ₀_fn c) 4 0 := fun {c} hc => by
    dsimp [fm]; split_ifs; exact Classical.choose_spec (hm_exists c hc)
  have hm0 : ∀ {c : ℝ}, c_min ≤ c → fm c 0 = 0 := by
    intro c hc
    have hc_α : c_α_floor ≤ c := hc_min_α.trans hc
    have hc_η : c_η ≤ c := (le_max_left _ _).trans hc_α
    have hc0 : 0 < c := by linarith [hc_min_2k.trans hc]
    have hε0 : 0 < liftEps c := liftEps_pos hc0
    have hD_eq_diff : (fun u => D_lift c u - S_c c u) =
        fun u => (D₀ c u - S_c c u) + η_fn c * g₁ u := by
      ext u
      have hmul : liftEps c * α₁ c = (∫ v : ℝ, S_c c v) + η_fn c := by
        dsimp [α₁]; split_ifs; exact mul_div_cancel₀ _ hε0.ne'
      calc D_lift c u - S_c c u = X u + (liftEps c * α₁ c) * g₁ u - S_c c u := rfl
        _ = X u + ((∫ v : ℝ, S_c c v) + η_fn c) * g₁ u - S_c c u := by rw [hmul]
        _ = (D₀ c u - S_c c u) + η_fn c * g₁ u := by dsimp [D₀]; ring
    have hfm0 := (hfm_spec hc).2.2
    rw [hD_eq_diff] at hfm0
    have hzero : liftSymbol (fun u => (D₀ c u - S_c c u) + η_fn c * g₁ u)
          (δ₀_fn c) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
        (-1 : ℂ) * liftSymbol (fun u => (D₀ c u - S_c c u) + η_fn c * g₁ u) (δ₀_fn c) 4 0 = 0 := by
      have h1 := (hη_spec hc_η).1
      dsimp [δ₀_fn]; linear_combination h1
    rw [hzero] at hfm0
    exact_mod_cast hfm0
  have heq_fhat : ∀ {c Δ : ℝ}, c_min ≤ c → 0 ≤ Δ → (fp c Δ - fm c Δ) / 2 = fhat c Δ := by
    intro c Δ hc hΔ
    have hc0 : 0 < c := by linarith [hc_min_2k.trans hc]
    have hUD_c : HasU2 (D_lift c) := hUX.add (hUg.smul (liftEps c * α₁ c))
    have hUS_c : HasU2 (S_c c) :=
      hasU2_convSource hp hp1 (by have := liftEps_pos hc0; positivity)
    have hδ0_c : 0 ≤ δ₀_fn c := by
      have := ceBeta1_pos; have := liftEps_pos hc0; positivity
    rcases eq_or_lt_of_le hΔ with rfl | hΔ0
    · have hfp0 := (hfp_spec hc).2.2
      have hfm0 := (hfm_spec hc).2.2
      have hxw : 0 ≤ (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ).re := by simp [(Real.rpow_pos_of_pos hc0 _).le]
      have hxm : (fun u => D_lift c u - S_c c u) = fun u => D_lift c u + (-1) * S_c c u := by
        ext u; ring
      rw [liftSymbol_add_seed hUD_c hUS_c _ 4 hxw, liftSymbol_add_seed hUD_c hUS_c _ 4 le_rfl] at hfp0
      rw [hxm, liftSymbol_add_seed hUD_c (hUS_c.smul (-1)) _ 4 hxw,
        liftSymbol_add_seed hUD_c (hUS_c.smul (-1)) _ 4 le_rfl,
        liftSymbol_const_mul_seed (-1) (S_c c) _ 4 _,
        liftSymbol_const_mul_seed (-1) (S_c c) _ 4 _] at hfm0
      have hsub : (((fp c 0 - fm c 0 : ℝ)) : ℂ) =
          (2 : ℂ) * (liftSymbol (S_c c) (δ₀_fn c) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
            liftSymbol (D_lift c) (δ₀_fn c) 4 0) := by
        rw [Complex.ofReal_sub, hfp0, hfm0]; push_cast; ring
      have hre := congrArg Complex.re hsub
      simp only [Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hre
      simp only [fhat, ↓reduceIte]; linarith
    · let ξ : ℝ := Δ / c
      have hξ0 : 0 < ξ := div_pos hΔ0 hc0
      have hcξ : c * ξ = Δ := by dsimp [ξ]; field_simp [hc0.ne']
      have hfpeq := (hfp_spec hc).2.1 ξ hξ0
      have hfmeq := (hfm_spec hc).2.1 ξ hξ0
      have hxm : (fun u => D_lift c u - S_c c u) = fun u => D_lift c u + (-1) * S_c c u := by
        ext u; ring
      rw [iMain_add hUD_c hUS_c hδ0_c 4 hc0 hξ0, iDual_add hUD_c hUS_c hδ0_c 4 hc0 hξ0] at hfpeq
      rw [hxm, iMain_add hUD_c (hUS_c.smul (-1)) hδ0_c 4 hc0 hξ0,
        iDual_add hUD_c (hUS_c.smul (-1)) hδ0_c 4 hc0 hξ0,
        iMain_const_mul, iDual_const_mul] at hfmeq
      have hdiff_c : (((c ^ (1 / 3 : ℝ) * hankelRho0 c Δ * ((fp c Δ - fm c Δ) / 2) : ℝ)) : ℂ) =
          iMain (S_c c) (δ₀_fn c) 4 c ξ + iDual (D_lift c) (δ₀_fn c) 4 c ξ := by
        have hL : (((c ^ (1 / 3 : ℝ) * hankelRho0 c Δ * ((fp c Δ - fm c Δ) / 2) : ℝ)) : ℂ) =
            ((1 / 2 : ℝ) : ℂ) * ((((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * fp c (c * ξ) : ℝ)) : ℂ) -
              (((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * fm c (c * ξ) : ℝ)) : ℂ)) := by
          rw [hcξ]; push_cast; ring
        rw [hL, hfpeq, hfmeq]; push_cast; ring
      rw [← hcξ, ← admissLift_twoEdge_eq hUS_c hUD_c hδ0_c 4 (by linarith [hc_min_2k.trans hc]) hξ0] at hdiff_c
      have hre := congrArg Complex.re hdiff_c
      simp only [Complex.ofReal_re] at hre
      have hpos : c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) ≠ 0 :=
        (mul_pos (Real.rpow_pos_of_pos hc0 _) (hankelRho0_pos hc0 (by positivity))).ne'
      simp only [fhat, hΔ0.ne', ↓reduceIte]; rw [← hcξ]; exact mul_left_cancel₀ hpos hre
  refine ⟨⟨c_min, hc_min_2k, hc_min_K, m_α, M_α, hm_α, hM_α, α₁,
    fun {c} hc => hα₁_bd (hc_min_α.trans hc), fp, fm,
    fun {c} hc => (hfp_spec hc).1, fun {c} hc => (hfm_spec hc).1,
    fun {c} hc => hm0 hc, ?_, fun {c Δ} hc hΔ => ?_, fun {c ξ} hc hξ => ?_, fun {c} hc => ?_⟩, le_rfl⟩
  · intro c hc
    have h1 := heq_fhat hc le_rfl
    have h2 := hfhat_pos hc le_rfl
    simp only [↓reduceIte, Complex.add_re] at h2
    have h3 := hm0 hc
    dsimp [fhat, X, g₁, S_c, δ₀_fn, D_lift] at h1
    simp only [↓reduceIte] at h1
    linarith
  · rw [heq_fhat hc hΔ]; exact hfhat_pos hc hΔ
  · have hc0 : 0 < c := by linarith [hc_min_2k.trans hc]
    have hUD_c : HasU2 (D_lift c) := hUX.add (hUg.smul (liftEps c * α₁ c))
    have hUS_c : HasU2 (S_c c) :=
      hasU2_convSource hp hp1 (by have := liftEps_pos hc0; positivity)
    have hδ0_c : 0 ≤ δ₀_fn c := by
      have := ceBeta1_pos; have := liftEps_pos hc0; positivity
    have hfpeq := (hfp_spec hc).2.1 ξ hξ
    have hfmeq := (hfm_spec hc).2.1 ξ hξ
    have hxm : (fun u => D_lift c u - S_c c u) = fun u => D_lift c u + (-1) * S_c c u := by
      ext u; ring
    rw [iMain_add hUD_c hUS_c hδ0_c 4 hc0 hξ, iDual_add hUD_c hUS_c hδ0_c 4 hc0 hξ] at hfpeq
    rw [hxm, iMain_add hUD_c (hUS_c.smul (-1)) hδ0_c 4 hc0 hξ,
      iDual_add hUD_c (hUS_c.smul (-1)) hδ0_c 4 hc0 hξ,
      iMain_const_mul, iDual_const_mul] at hfmeq
    have hL : (((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * ((fp c (c * ξ) + fm c (c * ξ)) / 2) : ℝ)) : ℂ) =
        ((1 / 2 : ℝ) : ℂ) * ((((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * fp c (c * ξ) : ℝ)) : ℂ) +
          (((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * fm c (c * ξ) : ℝ)) : ℂ)) := by
      push_cast; ring
    rw [hL, hfpeq, hfmeq]
    simp only [D_lift, X, g₁, S_c, δ₀_fn]
    push_cast; ring
  · rw [hm0 hc]; ring

/-- **Lemma `lem:ce-lift-assembly` (`ce_lift_proofs.tex`):**
given any generalized Airy seed `X_base` satisfying the `CeDualFloors` conditions and a
negative `c_neg (1 + |u|)^{-3/2}` lower tail on a left ray `u ≤ w_neg`, together with
convolution-source parameters `p ∈ (1/2, 1)`, `γ, θ, lam > 0`, there is a threshold `K_post ≥ 1`
such that every `K ≥ K_post` yields a `CeTwoEdgeLiftWitness X_base p γ θ lam K`. -/
theorem ce_twoEdge_lift_of_K
    {X_base : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF_base : HasGenRationalAiryCoeffs X_base β₀₀ β₁₁)
    (hX_mass : ∫ u : ℝ, (X_base (u : ℂ)).re = 0)
    (hX_lap : ∀ y : ℝ, 0 < y → 0 ≤ airyLaplace (fun u => (X_base (u : ℂ)).re) y)
    (hbinf : airyBetaInf X_base < 0) (hbplus : 0 < airyBetaPlus X_base)
    (hX_neg_tail : ∃ c_neg > 0, ∃ w_neg ≤ (0 : ℝ),
      ∀ u : ℝ, u ≤ w_neg → c_neg * (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ -(X_base (u : ℂ)).re)
    {p γ θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 < γ) (hθ : 0 < θ) (hlam : 0 < lam) :
    ∃ K_post ≥ (1 : ℝ), ∀ K : ℝ, K_post ≤ K →
      Nonempty (CeTwoEdgeLiftWitness X_base p γ θ lam K) := by
  obtain ⟨_, _, K_post, hKp, hW⟩ :=
    ce_twoEdge_lift_unif_of_K hF_base hX_mass hX_lap hbinf hbplus hX_neg_tail hp hp1 hγ hθ hlam
  exact ⟨K_post, hKp, fun K hK => ⟨Classical.choose (hW K hK)⟩⟩

/-- info: 'FormalResearch.SignUncertainty.ce_twoEdge_lift_of_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.ce_twoEdge_lift_of_K

end FormalResearch.SignUncertainty
