module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWNodes

/-!
# The Shared Core of the Concrete `BootstrapHBInstance` Constructions (Theorem `FT-L.FW`, Steps 0-4)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Theorem `FT-L.FW` (`wone:ftlfw`), Steps 0-4, and
`CFT/common/two_edge_bootstrap.tex`, Theorem `TE.2(4)` (`teb:bootstrap`).

* `bootstrapHB_core`: the `BootstrapHBInstance P W_top` at a good radius `R` and a violator `T`, with the band moments
  `B₁, B₂`, the line bound and the band feedback `YVInputAtForWThr` built once; the node family, the arc estimate,
  the node-slope bounds, `x̃` and `W_top` are inputs.  It serves the Airy (`m₀ = 1`) and Clark (`m₀ = 2`) instances.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap Crossing PoissonJensen TipFront
  ConcreteBootstrap FixedWeightTip

variable {prob : FixedWeightProblem} [Q : LemmaQData prob]

/-- **The shared core of the `BootstrapHBInstance` constructions.**  For a good radius `R` (`48 ≤ R`, `b² c'^{2/3} ≤ R`,
`R + 1 ≤ A_{c'}(b)²`) and a violator `T` with the band facts `Δ(-1), Δ(0) ≤ T ≤ Δ(-A_thr), Δ(-R)`, `u_T ≤ -1`, the instance has
`L = C_fb (c^{1/3} (B₁ + B₂) + 1)`, `c = c'`, `x̃` as prescribed.  The parameters `P` are constrained only through the
listed field equations; the arc estimate `hArcB` (with the arc factor `μ₀`) and the node bounds are inputs. -/
noncomputable def bootstrapHB_core
    (P : BootstrapParams) {W_top A_thr b C_fb c_YV C_gap κ_gap C_line μ₀ R T x_tilde : ℝ}
    (hPb : P.b = b) (hPCL : P.C_L = 4 * C_fb) (hPγ : P.γ = 1)
    (hPκ : P.κ = κ_gap) (hPC0 : C_gap ≤ P.C_0)
    (hPCa_line : C_line + 3 * Q.C0 ≤ P.C_a) (hPCa_cov : μ₀ * virasoroArcCovConst ≤ P.C_a)
    (hPCunc : P.C_unc = μ₀ * Q.arcUncConst) (hμ₀ : 0 ≤ μ₀) (hPD1 : 0 < P.D_1)
    (hPδ : P.δ_star ≤ 1 / 2) (hP_k0 : P.k_0 = 5)
    (hC_fb : 1 ≤ C_fb) (hC_gap : 0 < C_gap)
    (hA1 : 1 ≤ A_thr) (hA47 : A_thr ≤ 47) (hC_line : lineCaW A_thr ≤ C_line)
    (hb_pos : 0 < b)
    (hYVat : YVInputAtForWThr prob A_thr b (psiTilde prob) C_fb c_YV)
    {c' : ℝ} (hc'_Qenv : Q.cQ ≤ c') (hc'_YV : c_YV ≤ c')
    (hς_half : Q.sigma c' ≤ 1 / 2)
    {g : ℝ → ℝ} (hg : prob.IsWeaklyFeasible (c' / 12) T g)
    (hdl_half_full : deltaLobe prob Q.D.r_1 c' g < 1 / 2)
    (hdl_bd_full : deltaLobe prob Q.D.r_1 c' g ≤ C_gap * Real.exp (-κ_gap * c'))
    (hT_A2_full : virasoroDeltaChart c' (Q.AC c' ^ 2) < T)
    (hR_48 : 48 ≤ R) (hR_bv : b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_ub_2b : R ≤ 2 * b ^ 2 * c' ^ (2 / 3 : ℝ) + 1)
    (hR_ub_b : R + 1 ≤ chartACAt b c' ^ 2) (hR_ub : R + 1 ≤ Q.AC c' ^ 2) (hR_thr : A_thr ≤ R)
    (hu_m1 : virasoroUT c' T ≤ -1)
    (hT_lo_m1 : virasoroDeltaChart c' (-1) ≤ T) (hT_lo_0 : virasoroDeltaChart c' 0 ≤ T)
    (hT_hi_AThr : T ≤ virasoroDeltaChart c' (-A_thr)) (hT_hi_R : T ≤ virasoroDeltaChart c' (-R))
    (hx_pos : 0 < x_tilde) (hx_ub : x_tilde ≤ min P.δ_star (min P.η_0 1))
    (hW_top : 0 ≤ W_top)
    (P_nodes : ℕ → ℝ → ℝ)
    (hArcB : ∀ {k : ℕ} {ℓ : ℝ}, P.k_0 ≤ k → 0 ≤ ℓ → ℓ ≤ 1 / 2 →
      YVEnvBound (psiTilde prob c' g) c' R
        (C_fb * (c' ^ (1 / 3 : ℝ) * (bandB1W prob c' R T g + bandB2W prob c' R g) + 1)) →
      0 ≤ C_fb * (c' ^ (1 / 3 : ℝ) * (bandB1W prob c' R T g + bandB2W prob c' R g) + 1) →
      P_nodes k ℓ ≤ (∫ x in (-R)..R, (shiftedFunW prob c' R ℓ g k (x : ℂ)).re) +
        μ₀ * virasoroArcCov c' R T
          (C_fb * (c' ^ (1 / 3 : ℝ) * (bandB1W prob c' R T g + bandB2W prob c' R g) + 1)) ℓ g k +
        μ₀ * (Q.arcUncConst * c' ^ (-(3 / 8 : ℝ))))
    (hP_nodes_lb_hb : ∀ k : ℕ, ∀ ℓ : ℝ, P.k_0 ≤ k → (k : ℝ) ≤ R / 5 →
      ℓ ∈ Set.Icc (P.D_1 * c' ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
      -tebLambdaN P W_top * ℓ - P.C_α * R ^ (3 / 2 : ℝ) * 0 ≤ P_nodes k ℓ)
    (P_theta_bound : (P.k_0 : ℝ) ≤ R / 5 →
      tebThetaHB P W_top * x_tilde ∈
        Set.Icc (P.D_1 * c' ^ (-(1 / 3 : ℝ))) (min P.δ_star (min P.η_0 1)) →
      (P.κ_star / (4 * P.w_star)) * x_tilde - P.C_α * R ^ (3 / 2 : ℝ) * 0 ≤
        P_nodes P.k_0 (tebThetaHB P W_top * x_tilde)) :
    { I : BootstrapHBInstance P W_top //
      I.L = C_fb * (I.c ^ (1 / 3 : ℝ) * (I.B_1 + I.B_2) + 1) ∧ I.c = c' ∧ I.x_tilde = x_tilde } := by
  have hc'_10000 : 10000 ≤ c' := Q.hcQ_10000.trans hc'_Qenv
  have hc'_pos : 0 < c' := by linarith
  have hc'_ge1 : 1 ≤ c' := by linarith
  have hR_pos : 0 < R := by linarith
  have hA_pos : 0 < A_thr := by linarith
  have hB_sums := band_sums_leW_thr hA_pos hc'_Qenv hR_thr hR_ub hg hdl_half_full hT_lo_0 hT_hi_AThr
  have hB1_nn : 0 ≤ bandB1W prob c' R T g :=
    bandB1W_nonneg_thr hA_pos hc'_Qenv hR_thr (by linarith) hg hT_lo_0 hT_hi_AThr
  have hB2_nn : 0 ≤ bandB2W prob c' R g :=
    bandB2W_nonneg_thr hA_pos hc'_Qenv hR_thr (by linarith) hg hT_hi_AThr
  set B_1 := bandB1W prob c' R T g
  set B_2 := bandB2W prob c' R g
  set L := C_fb * (c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1) with hL
  have hL_lb : 1 ≤ L := by
    have h1 : 1 ≤ c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1 := by
      have : 0 ≤ c' ^ (1 / 3 : ℝ) * (B_1 + B_2) :=
        mul_nonneg (Real.rpow_nonneg hc'_pos.le _) (by linarith)
      linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ C_fb * (c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1) := mul_le_mul hC_fb h1 zero_le_one (by linarith)
  have hL_ub : L ≤ P.C_L * c' ^ P.γ := by
    have hc13_le : c' ^ (1 / 3 : ℝ) ≤ c' := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hc'_ge1 (by norm_num : (1 / 3 : ℝ) ≤ 1)
    have h1 : c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1 ≤ 4 * c' := by
      have hB3_le : B_1 + B_2 ≤ 3 := by linarith [hB_sums.1, hB_sums.2]
      calc c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1
          ≤ c' * 3 + c' := add_le_add
              (mul_le_mul hc13_le hB3_le (by linarith) hc'_pos.le) hc'_ge1
        _ = 4 * c' := by ring
    rw [hPCL, hPγ, Real.rpow_one]
    calc C_fb * (c' ^ (1 / 3 : ℝ) * (B_1 + B_2) + 1)
        ≤ C_fb * (4 * c') := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = 4 * C_fb * c' := by ring
  have hYV_env : YVEnvBound (psiTilde prob c' g) c' R L :=
    hYVat hc'_YV hR_thr hR_bv hR_ub_b hg hT_lo_0 hT_hi_AThr
  have hL0 : 0 ≤ L := zero_le_one.trans hL_lb
  refine ⟨{
    c := c'
    R := R
    a := √R
    B_1 := B_1
    B_2 := B_2
    L := L
    x_tilde := x_tilde
    r_inf := 0
    C_err := C_gap
    hc := by linarith
    ha_lb := by
      calc P.b * c' ^ (1 / 3 : ℝ)
          = √(b ^ 2 * c' ^ (2 / 3 : ℝ)) := by
            rw [hPb, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hb_pos.le,
              show c' ^ (2 / 3 : ℝ) = (c' ^ (1 / 3 : ℝ)) ^ 2 by
                rw [← Real.rpow_natCast (c' ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc'_pos.le]; norm_num,
              Real.sqrt_sq (Real.rpow_nonneg hc'_pos.le _)]
        _ ≤ √R := Real.sqrt_le_sqrt hR_bv
    ha_sq := Real.sq_sqrt hR_pos.le
    hR_ub := by rw [hPb]; exact hR_ub_2b
    hB1 := hB1_nn
    hB2 := hB2_nn
    hL_lb := hL_lb
    hL_ub := hL_ub
    hx_pos := hx_pos
    hx_ub := hx_ub
    hr_inf_nn := le_rfl
    hr_inf_ub := by have := P.hC0; positivity
    hC_err_nn := hC_gap.le
    hC_err_ub := hPC0
    B_1k := fun k => bandB1kW prob c' R T g k
    B_2' := fun _ => B_2
    P_nodes := P_nodes
    I_line := fun k ℓ => ∫ x in (-R)..R, (shiftedFunW prob c' R ℓ g k (x : ℂ)).re
    Arc_cov := fun k ℓ => μ₀ * virasoroArcCov c' R T L ℓ g k
    Arc_unc := μ₀ * (Q.arcUncConst * c' ^ (-(3 / 8 : ℝ)))
    hB1k_nn := fun k _ _ => bandB1kW_nonneg hc'_Qenv hR_pos.le (by linarith) hg hT_A2_full.le
      hT_hi_R (by linarith [hu_m1]) k
    hB2'_nn := fun _ _ _ => hB2_nn
    hB_sum := fun k _ _ => by
      have := bandB1W_le_B1k hc'_Qenv hR_pos (by linarith) hg hT_lo_0 hT_hi_R k
      linarith
    hP_le := fun k ℓ hk0 _ hℓ_mem => by
      have hℓ_nn : 0 ≤ ℓ := (mul_nonneg hPD1.le (Real.rpow_nonneg hc'_pos.le _)).trans hℓ_mem.1
      have hℓ_half : ℓ ≤ 1 / 2 := hℓ_mem.2.trans ((min_le_left _ _).trans hPδ)
      exact hArcB hk0 hℓ_nn hℓ_half hYV_env hL0
    hArc_cov := fun k ℓ hk0 _ hℓ_mem => by
      have hℓ_pos : 0 < ℓ :=
        lt_of_lt_of_le (mul_pos hPD1 (Real.rpow_pos_of_pos hc'_pos _)) hℓ_mem.1
      have hk5 : 5 ≤ k := hP_k0 ▸ hk0
      have hle := virasoroArcCov_le (c' := c') (T := T)
        ((by norm_num : (10 : ℝ) ≤ 48).trans hR_48) hL0 hℓ_pos g hk5
      calc μ₀ * virasoroArcCov c' R T L ℓ g k
          ≤ μ₀ * (virasoroArcCovConst * L * (√R)⁻¹ *
              ((2 : ℝ) ^ (k + 1) * Real.Gamma ((k : ℝ) + 1 / 2) *
                (π / (4 * ℓ * √R)) ^ ((k : ℝ) + 1 / 2))) :=
            mul_le_mul_of_nonneg_left hle hμ₀
        _ = (μ₀ * virasoroArcCovConst) * L * (√R)⁻¹ *
              ((2 : ℝ) ^ (k + 1) * Real.Gamma ((k : ℝ) + 1 / 2) *
                (π / (4 * ℓ * √R)) ^ ((k : ℝ) + 1 / 2)) := by ring
        _ ≤ P.C_a * L * (√R)⁻¹ *
              ((2 : ℝ) ^ (k + 1) * Real.Gamma ((k : ℝ) + 1 / 2) *
                (π / (4 * ℓ * √R)) ^ ((k : ℝ) + 1 / 2)) := by
            have hGam : 0 < Real.Gamma ((k : ℝ) + 1 / 2) := Real.Gamma_pos_of_pos (by positivity)
            have hX : 0 ≤ (2 : ℝ) ^ (k + 1) * Real.Gamma ((k : ℝ) + 1 / 2) *
                (π / (4 * ℓ * √R)) ^ ((k : ℝ) + 1 / 2) := by positivity
            have hsq : 0 ≤ (√R)⁻¹ := by positivity
            gcongr
    hArc_unc := le_of_eq (by rw [hPCunc]; ring)
    hI_line := fun k ℓ hk0 hkR hℓ_mem => by
      have hℓ_nn : 0 ≤ ℓ := (mul_nonneg hPD1.le (Real.rpow_nonneg hc'_pos.le _)).trans hℓ_mem.1
      have hℓ_half : ℓ ≤ 1 / 2 := hℓ_mem.2.trans ((min_le_left _ _).trans hPδ)
      have hk5 : 5 ≤ k := hP_k0 ▸ hk0
      have hlb := line_boundW_thr hA1 hc'_Qenv (Q.sigma_nonneg hc'_ge1) hς_half
        (by linarith) (by linarith) hR_ub hℓ_nn hℓ_half hg hT_lo_m1 hT_hi_AThr hk5 hkR
      have hCa : lineCaW A_thr + 3 * Q.C0 ≤ P.C_a :=
        (by linarith : lineCaW A_thr + 3 * Q.C0 ≤ C_line + 3 * Q.C0).trans hPCa_line
      have h_ca_term : (lineCaW A_thr + 3 * Q.C0) * ((k : ℝ) + 1) / R ≤
          P.C_a * ((k : ℝ) + 1) / R := by gcongr
      have h_exp_le : deltaLobe prob Q.D.r_1 c' g ≤ C_gap * c' * Real.exp (-P.κ * c') := by
        rw [hPκ]
        calc deltaLobe prob Q.D.r_1 c' g ≤ C_gap * Real.exp (-κ_gap * c') := hdl_bd_full
          _ = 1 * (C_gap * Real.exp (-κ_gap * c')) := (one_mul _).symm
          _ ≤ c' * (C_gap * Real.exp (-κ_gap * c')) :=
              mul_le_mul_of_nonneg_right hc'_ge1 (mul_nonneg hC_gap.le (Real.exp_pos _).le)
          _ = C_gap * c' * Real.exp (-κ_gap * c') := by ring
      linarith
    hW_top := hW_top
    hP_nodes_lb_hb := hP_nodes_lb_hb
    P_theta_bound := P_theta_bound
  }, rfl, rfl, rfl⟩

end FormalResearch.ModularBootstrap.FixedWeightBand
