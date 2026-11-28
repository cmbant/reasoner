module

public import FormalResearch.SignUncertainty.CeHbDualPair
public import FormalResearch.SignUncertainty.CeHankelPairFromEigen
public import FormalResearch.SignUncertainty.EuclidCELift
public import FormalResearch.SignUncertainty.HeadlineDefs

/-!
# Proof of `CeHbLift` (`thm:ce-hb-lift`, all Hermite–Biehler levels `m₀ ≥ 1`)

Discharges `CeHbLift D : Prop` (`ce_hb_lift_proved`) for every `D : ShellHBData`:
under weak Laplace positivity `∀ y > 0, 0 ≤ airyLaplace (fun u => -(D.G u).re) y`,
for any offset bound `R_off ≥ 0`, all sufficiently large dimensions `d` possess a
radial continuous `L¹` Cohn–Elkies function of radius `R` with
`R²/2 ≤ d/(2π²) - (D.tm / β₁)(d/2)^{1/3} + K₀` and `h(x) ≤ 0` at every prescribed
shell `‖x‖²/2 = shellSite t (r t) d` (`t ∈ D.S \ {D.tm}`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

private noncomputable def ceHbBasis (D : ShellHBData) (b : ℝ) : Fin 4 → ℂ → ℂ :=
  ![D.G, dslope (fun z => -D.G z) (D.tm : ℂ), airySbC b, airySeedG 0]

private noncomputable def ceHbAlpha {D : ShellHBData} (ds : CeHbDualScales D) (C_scale : ℝ) :
    Fin 4 → ℝ → ℝ → ℝ := fun i K c =>
  match i with
  | ⟨0, _⟩ => C_scale
  | ⟨1, _⟩ => -(C_scale * (K * liftEps c * ds.γ₁))
  | ⟨2, _⟩ => C_scale * (K * liftEps c * ds.γ₂)
  | ⟨3, _⟩ => C_scale * (-ds.r_eta K c)

private lemma ceHbFseed_eq_sum {D : ShellHBData} (ds : CeHbDualScales D) (C_scale K c u : ℝ) :
    C_scale * ceHbFseed ds K c u =
      ∑ i ∈ (Finset.univ : Finset (Fin 4)), ceHbAlpha ds C_scale i K c * (ceHbBasis D ds.b i (u : ℂ)).re := by
  have hGN := congr_fun (ceHb_GN_eq ds) u
  have hHN := congr_fun (ceHb_HN_eq ds) u
  simp only [Fin.sum_univ_four, ceHbBasis, ceHbAlpha, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, airySbC_re]
  rw [← hGN, ← hHN]
  dsimp [ceHbFseed]
  ring

private lemma ceHbFamilyEst {D : ShellHBData} (ds : CeHbDualScales D) {C_scale : ℝ} (hCs : 0 < C_scale) :
    let δ₁_t := min ds.δ₁ (1 / ds.c_η)
    O6FamilyEst 4 δ₁_t (fun K c u => C_scale * ceHbFseed ds K c u)
      (fun K c => C_scale * D.P.leadingCoeff ^ 2 + C_scale * (K * liftEps c * ds.γ₂) * (ds.b + 1))
      (2 * ceK * cA * ceCs ^ (1 / 2 : ℝ)) := by
  intro δ₁_t
  have hδ₁_t : 0 < δ₁_t := lt_min ds.hδ₁ (div_pos one_pos (by linarith [ds.hc_η]))
  have hB4 : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      HasGenRationalAiryCoeffs (ceHbBasis D ds.b i) (![D.P.leadingCoeff ^ 2, 0, ds.b, 0] i)
        (![0, 0, 1, 0] i) := fun i _ => by
    fin_cases i
    · exact hasGenRationalAiryCoeffs_shellHBData_G D ds.hOdd
    · exact hasGenRationalAiryCoeffs_terminal_cardinal D ds.hOdd
    · exact hasGenRationalAiryCoeffs_airySbC ds.b
    · exact hasGenRationalAiryCoeffs_airySeedG 0
  let R4 : ℝ := C_scale * max 1 (max (ds.γ₁ / 2 + 1) (ds.γ₂ / 2 + 1))
  have hR4 : 0 ≤ R4 := by have := ds.hγ₁; have := ds.hγ₂; positivity
  have hα4 : ∀ i ∈ (Finset.univ : Finset (Fin 4)), ∀ K c : ℝ,
      1 ≤ K → 2000 ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁_t) ^ 3 ≤ c → |ceHbAlpha ds C_scale i K c| ≤ R4 := by
    intro i _ K c hK hc2k hc8K hcδ
    have hc0 : 0 < c := by linarith
    have hKε0 : 0 ≤ K * liftEps c := by have := liftEps_pos hc0; positivity
    have hKeps : K * liftEps c ≤ 1 / 2 := liftEps_mul_le_half (by linarith) hc8K
    have hc_η : ds.c_η ≤ c := by
      have hcη0 : 0 < ds.c_η := by linarith [ds.hc_η]
      have h1 : 1 ≤ K / δ₁_t := by
        have hle : δ₁_t ≤ 1 / ds.c_η := min_le_right _ _
        calc (1 : ℝ) ≤ ds.c_η := by linarith [ds.hc_η]
          _ ≤ K * ds.c_η := le_mul_of_one_le_left hcη0.le hK
          _ = K / (1 / ds.c_η) := by field_simp [hcη0.ne']
          _ ≤ K / δ₁_t := div_le_div_of_nonneg_left (by linarith) hδ₁_t hle
      have hpow : K / δ₁_t ≤ (K / δ₁_t) ^ 3 := by
        calc K / δ₁_t = (K / δ₁_t) * 1 * 1 := by ring
          _ ≤ (K / δ₁_t) * (K / δ₁_t) * (K / δ₁_t) := by gcongr
          _ = (K / δ₁_t) ^ 3 := by ring
      have hK_c : K * ds.c_η ≤ K / δ₁_t := by
        calc K * ds.c_η = K / (1 / ds.c_η) := by field_simp [hcη0.ne']
          _ ≤ K / δ₁_t := div_le_div_of_nonneg_left (by linarith) hδ₁_t (min_le_right _ _)
      calc ds.c_η ≤ K * ds.c_η := le_mul_of_one_le_left hcη0.le hK
        _ ≤ K / δ₁_t := hK_c
        _ ≤ (K / δ₁_t) ^ 3 := hpow
        _ ≤ c := hcδ
    fin_cases i
    · dsimp [ceHbAlpha, R4]; rw [abs_of_pos hCs]
      calc C_scale = C_scale * 1 := (mul_one _).symm
        _ ≤ C_scale * max 1 (max (ds.γ₁ / 2 + 1) (ds.γ₂ / 2 + 1)) :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) hCs.le
    · dsimp [ceHbAlpha, R4]; rw [abs_neg, abs_mul, abs_of_pos hCs, abs_of_nonneg (mul_nonneg hKε0 ds.hγ₁.le)]
      exact mul_le_mul_of_nonneg_left ((le_trans (by nlinarith [ds.hγ₁]) (le_max_left _ _)).trans (le_max_right _ _)) hCs.le
    · dsimp [ceHbAlpha, R4]; rw [abs_mul, abs_of_pos hCs, abs_of_nonneg (mul_nonneg hKε0 ds.hγ₂.le)]
      exact mul_le_mul_of_nonneg_left ((le_trans (by nlinarith [ds.hγ₂]) (le_max_right _ _)).trans (le_max_right _ _)) hCs.le
    · dsimp [ceHbAlpha, R4]; rw [abs_mul, abs_neg, abs_of_pos hCs]
      have hr := (ds.hr_eta_eps hK hc_η hc8K).trans hKeps
      exact mul_le_mul_of_nonneg_left (hr.trans ((by norm_num : (1 / 2 : ℝ) ≤ 1).trans (le_max_left _ _))) hCs.le
  have hEst := o6FamilyEst_of_genRational_family (Finset.univ : Finset (Fin 4)) (ceHbBasis D ds.b)
    (![D.P.leadingCoeff ^ 2, 0, ds.b, 0]) (![0, 0, 1, 0]) hB4 (ceHbAlpha ds C_scale) R4 δ₁_t hR4 hδ₁_t hα4
    (m := 4) (by norm_num)
  have hF_eq : (fun K c (u : ℝ) => ∑ i ∈ (Finset.univ : Finset (Fin 4)),
      ceHbAlpha ds C_scale i K c * (ceHbBasis D ds.b i (u : ℂ)).re) =
      fun K c (u : ℝ) => C_scale * ceHbFseed ds K c u := by
    ext K c u; exact (ceHbFseed_eq_sum ds C_scale K c u).symm
  have hβ_eq : (fun K c => ∑ i ∈ (Finset.univ : Finset (Fin 4)),
      ceHbAlpha ds C_scale i K c * (![D.P.leadingCoeff ^ 2, 0, ds.b, 0] i + ![0, 0, 1, 0] i)) =
      fun K c => C_scale * D.P.leadingCoeff ^ 2 + C_scale * (K * liftEps c * ds.γ₂) * (ds.b + 1) := by
    ext K c
    simp only [Fin.sum_univ_four, ceHbAlpha, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  rwa [hF_eq, hβ_eq] at hEst

private lemma ceHb_tail_pos_exists {D : ShellHBData} (sys : CeHbDualSystem D) :
    ∃ K_o6 : ℝ, 1 ≤ K_o6 ∧ ∀ {K : ℝ}, K_o6 ≤ K →
      ∃ K₀_tail c_tail : ℝ, 0 < K₀_tail ∧ 2000 ≤ c_tail ∧ 8 * K ^ 3 ≤ c_tail ∧
        (K / sys.scales.δ₁) ^ 3 ≤ c_tail ∧ sys.scales.c_η ≤ c_tail ∧
        ∀ {c Δ : ℝ}, c_tail ≤ c →
          c / π ^ 2 - (D.tm / hankelBeta1) * c ^ (1 / 3 : ℝ) + K₀_tail ≤ Δ →
          0 < (iMain (ceHbFseed sys.scales K c) (ceBeta1 * K * liftEps c / 2) 4 c (Δ / c) +
            iDual (fun u => -(ceHbSsrc sys.scales K c u)) (ceBeta1 * K * liftEps c / 2) 4 c (Δ / c)).re := by
  let ds := sys.scales
  have hP_pos : 0 < D.P.leadingCoeff ^ 2 :=
    sq_pos_of_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr (shellHBData_P_degree_of_odd D ds.hOdd).1)
  let C_G : ℝ := max 1 (2 / D.P.leadingCoeff ^ 2)
  have hCG_pos : 0 < C_G := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let δ₁_t := min ds.δ₁ (1 / ds.c_η)
  have hδ₁_t : 0 < δ₁_t := lt_min ds.hδ₁ (div_pos one_pos (by linarith [ds.hc_η]))
  have hE := ceHbFamilyEst ds hCG_pos
  have hDE := o6DualEst_const_mul ds.hS_dual_est hCG_pos
  have htm_neg : D.tm < 0 := lt_of_le_of_lt D.tm_le_airyZero_one (by linarith [airyZero_one.2])
  have hPlc : D.P.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (shellHBData_P_degree_of_odd D ds.hOdd).1
  have hU0 : 0 ≤ -D.tm := by linarith
  have hU1 : 0 ≤ 2 * ds.γ₁ := by positivity [ds.hγ₁]
  have hlead : ∀ {K c : ℝ}, 1 ≤ K → 2000 ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁_t) ^ 3 ≤ c →
      1 ≤ C_G * D.P.leadingCoeff ^ 2 + C_G * (K * liftEps c * ds.γ₂) * (ds.b + 1) := by
    intro K c hK hc2k _ _
    have hc0 : 0 < c := by linarith
    have hterm1 : 2 ≤ C_G * D.P.leadingCoeff ^ 2 := by
      have h1 : 2 / D.P.leadingCoeff ^ 2 ≤ C_G := le_max_right _ _
      calc (2 : ℝ) = (2 / D.P.leadingCoeff ^ 2) * D.P.leadingCoeff ^ 2 := by field_simp [hPlc]
        _ ≤ C_G * D.P.leadingCoeff ^ 2 := mul_le_mul_of_nonneg_right h1 hP_pos.le
    have hterm2 : 0 ≤ C_G * (K * liftEps c * ds.γ₂) * (ds.b + 1) := by
      have := liftEps_pos hc0; have := ds.hγ₂; have := ds.hb; positivity
    linarith
  have hfloor : ∀ {K c : ℝ}, 1 ≤ K → 2000 ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁_t) ^ 3 ≤ c →
      ∀ x : ℝ, -D.tm + (2 * ds.γ₁) * (K * liftEps c) + ceBeta1 * (K * liftEps c) / 2 ≤ x →
      (1 + x) ^ (-(3 / 2 : ℝ)) *
          ((C_G * ds.c₁) * (K * liftEps c) + (C_G * ds.c₂) * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x)) ≤
        ∫ t in Icc (0 : ℝ) (ceBeta1 * (K * liftEps c) / 2),
          (C_G * ceHbFseed ds K c (-x + t)) * bspline 4 (ceBeta1 * (K * liftEps c) / 2) t := by
    intro K c hK hc2k hc8K hcδ x hx
    have hKε0 : 0 ≤ K * liftEps c := by have := liftEps_pos (by linarith : 0 < c); positivity
    have hcδ0 : (K / ds.δ₁) ^ 3 ≤ c := by
      have hle : K / ds.δ₁ ≤ K / δ₁_t := div_le_div_of_nonneg_left (by linarith) hδ₁_t (min_le_left _ _)
      exact (pow_le_pow_left₀ (by positivity [ds.hδ₁]) hle 3).trans hcδ
    have hc_η : ds.c_η ≤ c := by
      have hcη0 : 0 < ds.c_η := by linarith [ds.hc_η]
      have h1 : 1 ≤ K / δ₁_t := by
        calc (1 : ℝ) ≤ ds.c_η := by linarith [ds.hc_η]
          _ ≤ K * ds.c_η := le_mul_of_one_le_left hcη0.le hK
          _ = K / (1 / ds.c_η) := by field_simp [hcη0.ne']
          _ ≤ K / δ₁_t := div_le_div_of_nonneg_left (by linarith) hδ₁_t (min_le_right _ _)
      have hpow : K / δ₁_t ≤ (K / δ₁_t) ^ 3 := calc K / δ₁_t = (K / δ₁_t) * 1 * 1 := by ring
        _ ≤ (K / δ₁_t) * (K / δ₁_t) * (K / δ₁_t) := by gcongr
        _ = (K / δ₁_t) ^ 3 := by ring
      have hKc : K * ds.c_η ≤ K / δ₁_t := by
        calc K * ds.c_η = K / (1 / ds.c_η) := by field_simp [hcη0.ne']
          _ ≤ K / δ₁_t := div_le_div_of_nonneg_left (by linarith) hδ₁_t (min_le_right _ _)
      exact ((le_mul_of_one_le_left hcη0.le hK).trans hKc).trans (hpow.trans hcδ)
    have hlast : ds.S.lastNode = D.tm := by rw [ds.hS_eq, hbSeedSpec_of_shellHBData_lastNode D ds.hOdd]
    have hu₀ : |ds.S.lastNode - 2 * ds.γ₁ * (K * liftEps c)| = -D.tm + (2 * ds.γ₁) * (K * liftEps c) := by
      rw [hlast, abs_of_nonpos (by nlinarith [ds.hγ₁, hKε0])]; ring
    have hfl := (ds.hF_mass_floor hK hc_η hc8K hcδ0).2.1 x (by linarith)
    have hint_eq : ∫ t in Icc (0 : ℝ) (ceBeta1 * (K * liftEps c) / 2),
        (C_G * ceHbFseed ds K c (-x + t)) * bspline 4 (ceBeta1 * (K * liftEps c) / 2) t =
        C_G * ∫ t in Icc (0 : ℝ) (ceBeta1 * (K * liftEps c) / 2),
          ceHbFseed ds K c (-x + t) * bspline 4 (ceBeta1 * (K * liftEps c) / 2) t := by
      simp_rw [mul_assoc]; exact integral_const_mul _ _
    rw [hint_eq]
    calc (1 + x) ^ (-(3 / 2 : ℝ)) *
          ((C_G * ds.c₁) * (K * liftEps c) + (C_G * ds.c₂) * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x))
        = C_G * ((1 + x) ^ (-(3 / 2 : ℝ)) *
            (ds.c₁ * (K * liftEps c) + ds.c₂ * min 1 ((ceBeta1 * (K * liftEps c) / 2) ^ 2 * x))) := by ring
      _ ≤ C_G * ∫ t in Icc (0 : ℝ) (ceBeta1 * (K * liftEps c) / 2),
            ceHbFseed ds K c (-x + t) * bspline 4 (ceBeta1 * (K * liftEps c) / 2) t := by
          refine mul_le_mul_of_nonneg_left ?_ hCG_pos.le
          simpa only [ceHbFseed, mul_assoc] using hfl
  obtain ⟨K_o6, c_o6, hKo6, hco6, ho6⟩ := o6_positivity_dual_family (m := 4) (by norm_num) hE _ hDE
    hδ₁_t (mul_pos hCG_pos ds.hc₁) (mul_pos hCG_pos ds.hc₂) hU0 hU1 hlead hfloor
  refine ⟨K_o6, hKo6, fun {K} hK => ?_⟩
  have hK1 : 1 ≤ K := hKo6.trans hK
  let η_tail : ℝ := (2 * ds.γ₁ / ceBeta1 + 1 / 2) * K + 1
  have hη : 0 < η_tail := by have := ds.hγ₁; have := ceBeta1_pos; positivity
  let K₀_tail : ℝ := η_tail + 1
  let B_tl : ℝ := max (2 * Real.pi ^ 2 * (|D.tm| / ceBeta1 + η_tail))
    (2 * Real.pi ^ 2 * (|D.tm| / ceBeta1 + η_tail) ^ 2) + 1
  have hB_tl : 0 ≤ B_tl := by positivity
  let c_tail : ℝ := max (max c_o6 ds.c_η) (max (max (8 * K ^ 3) ((K / δ₁_t) ^ 3)) (B_tl ^ 3))
  have hc_o6 : c_o6 ≤ c_tail := (le_max_left _ _).trans (le_max_left _ _)
  have hc_η : ds.c_η ≤ c_tail := (le_max_right _ _).trans (le_max_left _ _)
  have hc_8K : 8 * K ^ 3 ≤ c_tail := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hc_δt : (K / δ₁_t) ^ 3 ≤ c_tail := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hc_δ : (K / ds.δ₁) ^ 3 ≤ c_tail := by
    have hle : K / ds.δ₁ ≤ K / δ₁_t := div_le_div_of_nonneg_left (by linarith) hδ₁_t (min_le_left _ _)
    exact (pow_le_pow_left₀ (by positivity [ds.hδ₁]) hle 3).trans hc_δt
  refine ⟨K₀_tail, c_tail, by linarith, hco6.trans hc_o6, hc_8K, hc_δ, hc_η, fun {c Δ} hc hΔ => ?_⟩
  have hc0 : 0 < c := by linarith [hco6.trans (hc_o6.trans hc)]
  have hc2 : 2 ≤ c := by linarith [hco6.trans (hc_o6.trans hc)]
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  have hε1 : liftEps c ≤ 1 := liftEps_le_one (by linarith)
  have hcB3 : B_tl ^ 3 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  have hB_eps : B_tl * liftEps c ≤ 1 := by
    have hle13 : B_tl ≤ c ^ (1 / 3 : ℝ) := by
      have h := Real.rpow_le_rpow (by positivity) hcB3 (by norm_num : (0 : ℝ) ≤ 1 / 3)
      rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul hB_tl] at h; simpa using h
    rw [show liftEps c = (c ^ (1 / 3 : ℝ))⁻¹ by unfold liftEps; rw [Real.rpow_neg hc0.le],
      ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hc0 _)]
    exact hle13
  have hy_half : Real.pi ^ 2 * ((|D.tm| / ceBeta1) * liftEps c ^ 2 + η_tail * liftEps c ^ 3) ≤ 1 / 2 := by
    have hε32 : liftEps c ^ 3 ≤ liftEps c ^ 2 := by nlinarith
    have hε21 : liftEps c ^ 2 ≤ liftEps c := by nlinarith
    calc Real.pi ^ 2 * ((|D.tm| / ceBeta1) * liftEps c ^ 2 + η_tail * liftEps c ^ 3)
        ≤ Real.pi ^ 2 * ((|D.tm| / ceBeta1) * liftEps c ^ 2 + η_tail * liftEps c ^ 2) := by gcongr
      _ = (Real.pi ^ 2 * (|D.tm| / ceBeta1 + η_tail)) * liftEps c ^ 2 := by ring
      _ ≤ (Real.pi ^ 2 * (|D.tm| / ceBeta1 + η_tail)) * liftEps c := by
          gcongr; have := ceBeta1_pos; positivity
      _ ≤ (B_tl / 2) * liftEps c := by
          have : 2 * Real.pi ^ 2 * (|D.tm| / ceBeta1 + η_tail) ≤ B_tl :=
            (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
          nlinarith
      _ = (B_tl * liftEps c) / 2 := by ring
      _ ≤ 1 / 2 := by linarith
  have hquad : 2 * Real.pi ^ 2 * liftEps c * (|D.tm| / ceBeta1 + η_tail) ^ 2 ≤ 1 := by
    have : 2 * Real.pi ^ 2 * (|D.tm| / ceBeta1 + η_tail) ^ 2 ≤ B_tl :=
      (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
    calc 2 * Real.pi ^ 2 * liftEps c * (|D.tm| / ceBeta1 + η_tail) ^ 2
        = (2 * Real.pi ^ 2 * (|D.tm| / ceBeta1 + η_tail) ^ 2) * liftEps c := by ring
      _ ≤ B_tl * liftEps c := by gcongr
      _ ≤ 1 := hB_eps
  have hΔ' : c / Real.pi ^ 2 - (D.tm / ceBeta1) * c ^ (1 / 3 : ℝ) + (η_tail + 1) ≤ Δ := by
    simpa only [show hankelBeta1 = ceBeta1 from rfl] using hΔ
  obtain ⟨hΔ_pos, hS_lo⟩ := hbS_tail_lower hη hc2 hy_half hquad hΔ'
  have hS_o6 : (-D.tm + 2 * ds.γ₁ * (K * liftEps c) + ceBeta1 * (K * liftEps c) / 2) / ceBeta1 ≤ hbS c (Δ / c) := by
    have hβ0 := ceBeta1_pos
    have h_eq : (-D.tm + 2 * ds.γ₁ * (K * liftEps c) + ceBeta1 * (K * liftEps c) / 2) / ceBeta1 =
        -D.tm / ceBeta1 + (2 * ds.γ₁ / ceBeta1 + 1 / 2) * K * liftEps c := by
      field_simp [hβ0.ne']; ring
    rw [h_eq]
    have h_diff : (2 * ds.γ₁ / ceBeta1 + 1 / 2) * K * liftEps c ≤ η_tail * liftEps c := by
      dsimp [η_tail]; nlinarith [hε0]
    linarith
  have ho6_pos := ho6 hK (hc_o6.trans hc) (hc_8K.trans hc) (hc_δt.trans hc) (div_pos hΔ_pos hc0) hS_o6
  have hKeps : K * liftEps c ≤ 1 / 2 := liftEps_mul_le_half (by linarith) (hc_8K.trans hc)
  have hcond : 0 < K ∧ 2000 ≤ c ∧ K * liftEps c ≤ 2 :=
    ⟨by linarith, (hco6.trans hc_o6).trans hc, by linarith⟩
  have hD_eq : (fun u => -(if 0 < K ∧ 2000 ≤ c ∧ K * liftEps c ≤ 2 then ceHbSsrc ds K c u else 0)) =
      fun u => -(ceHbSsrc ds K c u) := by ext u; simp [hcond]
  rw [iMain_const_mul,
    show (fun u : ℝ => C_G * -(if 0 < K ∧ 2000 ≤ c ∧ K * liftEps c ≤ 2 then ds.M_K K c * convSourceFamily (3 / 4) 1 1 1 c u else 0)) =
      fun u => C_G * -(ceHbSsrc ds K c u) from by ext u; dsimp [ceHbSsrc]; simp [hcond],
    iDual_const_mul] at ho6_pos
  have hfac : (((C_G : ℝ) : ℂ) * iMain (ceHbFseed ds K c) (ceBeta1 * K * liftEps c / 2) 4 c (Δ / c) +
      ((C_G : ℝ) : ℂ) * iDual (fun u => -(ceHbSsrc ds K c u)) (ceBeta1 * K * liftEps c / 2) 4 c (Δ / c)).re =
      C_G * (iMain (ceHbFseed ds K c) (ceBeta1 * K * liftEps c / 2) 4 c (Δ / c) +
        iDual (fun u => -(ceHbSsrc ds K c u)) (ceBeta1 * K * liftEps c / 2) 4 c (Δ / c)).re := by
    rw [← mul_add, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hfac] at ho6_pos
  exact pos_of_mul_pos_right ho6_pos hCG_pos.le

private lemma ceHb_window_pos_exists {D : ShellHBData} (sys : CeHbDualSystem D) {R_off : ℝ} (hR : 0 ≤ R_off) :
    ∃ K_win : ℝ, 1 ≤ K_win ∧ ∀ {K : ℝ}, K_win ≤ K →
      ∃ c_win : ℝ, 32768 ≤ c_win ∧ 8 * K ^ 3 ≤ c_win ∧ (K / sys.scales.δ₁) ^ 3 ≤ c_win ∧
        sys.scales.c_η ≤ c_win ∧
        ∀ {c t r : ℝ}, c_win ≤ c → t ∈ D.S → t ≠ D.tm → |r| ≤ R_off →
          let Δ := c / π ^ 2 - (t / hankelBeta1) * c ^ (1 / 3 : ℝ) + r
          0 < Δ ∧
            0 < (iMain (ceHbFseed sys.scales K c) (ceBeta1 * K * liftEps c / 2) 4 c (Δ / c) +
              iDual (fun u => -(ceHbSsrc sys.scales K c u)) (ceBeta1 * K * liftEps c / 2) 4 c (Δ / c)).re := by
  let ds := sys.scales
  let δ₁_t := min ds.δ₁ (1 / ds.c_η)
  have hδ₁_t : 0 < δ₁_t := lt_min ds.hδ₁ (div_pos one_pos (by linarith [ds.hc_η]))
  have hE := ceHbFamilyEst ds one_pos
  have hE_eq : (fun K c u => 1 * ceHbFseed ds K c u) = fun K c u => ceHbFseed ds K c u := by
    ext K c u; ring
  rw [hE_eq] at hE
  let B_t : ℝ := D.S.sup' D.S_nonempty (fun t => |t|)
  have hBt : 0 ≤ B_t := le_trans (abs_nonneg D.tm) (Finset.le_sup' (fun t => |t|) D.tm_mem)
  let C_drift : ℝ := ceBeta1 * R_off + 2 * ceBeta1 * Real.pi ^ 2 * (B_t / ceBeta1 + R_off) ^ 2
  have hCd : 0 ≤ C_drift := by have := ceBeta1_pos; positivity
  let K_win : ℝ := max 1 (2 * (C_drift + 1 / (2 * ceCs)) / ceBeta1 + 1)
  have hK_win : 1 ≤ K_win := le_max_left _ _
  refine ⟨K_win, hK_win, fun {K} hK => ?_⟩
  have hK1 : 1 ≤ K := hK_win.trans hK
  let Sw : ℝ := 1 + B_t / ceBeta1
  obtain ⟨C_m, hCm, he5_m⟩ := hE.e5 Sw
  obtain ⟨C_d, hCd5, he5_d⟩ := ds.hS_dual_est.e5 Sw
  let η_main : ℝ := ceK * ceBeta1 * K / (2 * Real.pi ^ 2)
  have hη_main : 0 < η_main := by have := ceK_pos; have := ceBeta1_pos; positivity
  let C_err : ℝ := 2 * C_m + C_d
  have hC_err : 0 < C_err := by positivity
  let B_shell : ℝ := max (2 * Real.pi ^ 2 * (B_t / ceBeta1 + R_off) + 1)
    (max (C_drift / ceBeta1 + 1) (2 * C_err / η_main + 1))
  have hB_sh : 0 ≤ B_shell := by have := ceBeta1_pos; positivity
  let c_win : ℝ := max (max 32768 ds.c_η) (max (max (8 * K ^ 3) ((K / δ₁_t) ^ 3)) (B_shell ^ 6))
  have hc32 : 32768 ≤ c_win := (le_max_left _ _).trans (le_max_left _ _)
  have hc_η : ds.c_η ≤ c_win := (le_max_right _ _).trans (le_max_left _ _)
  have hc_8K : 8 * K ^ 3 ≤ c_win := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hc_δt : (K / δ₁_t) ^ 3 ≤ c_win := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hc_δ : (K / ds.δ₁) ^ 3 ≤ c_win := by
    have hle : K / ds.δ₁ ≤ K / δ₁_t := div_le_div_of_nonneg_left (by linarith) hδ₁_t (min_le_left _ _)
    exact (pow_le_pow_left₀ (by positivity [ds.hδ₁]) hle 3).trans hc_δt
  refine ⟨c_win, hc32, hc_8K, hc_δ, hc_η, fun {c t r} hc htS htm hr => ?_⟩
  have hc0 : 0 < c := by linarith [hc32.trans hc]
  have hc2 : 2 ≤ c := by linarith [hc32.trans hc]
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  have hε1 : liftEps c ≤ 1 := liftEps_le_one (by linarith)
  have ht_bd : |t| ≤ B_t := Finset.le_sup' (fun t => |t|) htS
  have hcB6 : B_shell ^ 6 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  have hB_c16 : B_shell ≤ c ^ (1 / 6 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity) hcB6 (by norm_num : (0 : ℝ) ≤ 1 / 6)
    rw [← Real.rpow_natCast _ 6, ← Real.rpow_mul hB_sh] at h; simpa using h
  have h_eps_inv6 : B_shell * c ^ (-(1 / 6 : ℝ)) ≤ 1 := by
    have hc16 : 0 < c ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hc0 _
    rw [Real.rpow_neg hc0.le, ← div_eq_mul_inv, div_le_one hc16]; exact hB_c16
  have h_c13_le : B_shell * liftEps c ≤ 1 := by
    have hc13 : B_shell ≤ c ^ (1 / 3 : ℝ) := calc B_shell ≤ c ^ (1 / 6 : ℝ) := hB_c16
      _ ≤ c ^ (1 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    rw [show liftEps c = (c ^ (1 / 3 : ℝ))⁻¹ by unfold liftEps; rw [Real.rpow_neg hc0.le],
      ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hc0 _)]
    exact hc13
  have hy_half : Real.pi ^ 2 * ((B_t / ceBeta1) * liftEps c ^ 2 + R_off * liftEps c ^ 3) ≤ 1 / 2 := by
    have hε32 : liftEps c ^ 3 ≤ liftEps c ^ 2 := by nlinarith
    have hε21 : liftEps c ^ 2 ≤ liftEps c := by nlinarith
    have h1 : 2 * Real.pi ^ 2 * (B_t / ceBeta1 + R_off) ≤ B_shell :=
      (le_add_of_nonneg_right zero_le_one).trans (le_max_left _ _)
    calc Real.pi ^ 2 * ((B_t / ceBeta1) * liftEps c ^ 2 + R_off * liftEps c ^ 3)
        ≤ Real.pi ^ 2 * ((B_t / ceBeta1) * liftEps c ^ 2 + R_off * liftEps c ^ 2) := by gcongr
      _ = (Real.pi ^ 2 * (B_t / ceBeta1 + R_off)) * liftEps c ^ 2 := by ring
      _ ≤ (Real.pi ^ 2 * (B_t / ceBeta1 + R_off)) * liftEps c := by
          gcongr; have := ceBeta1_pos; positivity
      _ ≤ (B_shell / 2) * liftEps c := by nlinarith [h1]
      _ ≤ 1 / 2 := by linarith [h_c13_le]
  have hΔ_lo : c / (2 * Real.pi ^ 2) ≤ c / Real.pi ^ 2 - (t / ceBeta1) * c ^ (1 / 3 : ℝ) + r := by
    have hΔ' : Real.pi ^ 2 * (|t| / ceBeta1 * liftEps c ^ 2 + |r| * liftEps c ^ 3) ≤ 1 / 2 := by
      refine le_trans ?_ hy_half
      have := ceBeta1_pos; gcongr
    have hmul := mul_le_mul_of_nonneg_left hΔ' (div_nonneg hc0.le (sq_nonneg Real.pi))
    have hcube : liftEps c ^ 3 * c = 1 := liftEps_cube_mul hc0
    have hc13_eq : c ^ (1 / 3 : ℝ) = liftEps c ^ 2 * c := by
      have hc_eq : c ^ (1 / 3 : ℝ) * liftEps c = 1 := by
        unfold liftEps; rw [← Real.rpow_add hc0]; norm_num
      calc c ^ (1 / 3 : ℝ) = c ^ (1 / 3 : ℝ) * (liftEps c * (liftEps c ^ 2 * c)) := by
            have : liftEps c * (liftEps c ^ 2 * c) = 1 := by linarith [hcube]
            rw [this, mul_one]
        _ = (c ^ (1 / 3 : ℝ) * liftEps c) * (liftEps c ^ 2 * c) := by ring
        _ = liftEps c ^ 2 * c := by rw [hc_eq, one_mul]
    have hpi_ne : Real.pi ^ 2 ≠ 0 := (sq_pos_of_ne_zero Real.pi_ne_zero).ne'
    have h1 : (c / Real.pi ^ 2) * (Real.pi ^ 2 * (|t| / ceBeta1 * liftEps c ^ 2 + |r| * liftEps c ^ 3)) =
        (|t| / ceBeta1) * c ^ (1 / 3 : ℝ) + |r| := by
      rw [hc13_eq]; field_simp [hpi_ne]; linear_combination |r| * hcube
    have h2 : (c / Real.pi ^ 2) * (1 / 2) = c / (2 * Real.pi ^ 2) := by ring
    have hbd_tr : |t| / ceBeta1 * c ^ (1 / 3 : ℝ) + |r| ≤ c / (2 * Real.pi ^ 2) := by linarith
    have ht_tr : (t / ceBeta1) * c ^ (1 / 3 : ℝ) ≤ (|t| / ceBeta1) * c ^ (1 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_abs_self t) ceBeta1_pos.le)
        (Real.rpow_nonneg hc0.le _)
    linarith [neg_abs_le r]
  have hnb := hbS_near_shell hBt hR ht_bd hr hc2 hΔ_lo hy_half
  dsimp only at hnb
  dsimp only
  set Δ : ℝ := c / Real.pi ^ 2 - (t / ceBeta1) * c ^ (1 / 3 : ℝ) + r
  have hΔ_pos : 0 < Δ := lt_of_lt_of_le (by positivity) hΔ_lo
  have hξ_pos : 0 < Δ / c := hnb.1
  have hSw : |hbS c (Δ / c)| ≤ Sw := by
    have h1 : |ceBeta1 * hbS c (Δ / c) + t| ≤ C_drift * liftEps c := hnb.2
    have hdiv : |hbS c (Δ / c) + t / ceBeta1| ≤ (C_drift / ceBeta1) * liftEps c := by
      rw [show hbS c (Δ / c) + t / ceBeta1 = (ceBeta1 * hbS c (Δ / c) + t) / ceBeta1 by
        field_simp [ceBeta1_pos.ne']]
      rw [abs_div, abs_of_pos ceBeta1_pos, div_le_iff₀ ceBeta1_pos]
      exact h1.trans_eq (by field_simp [ceBeta1_pos.ne'])
    have hCd1 : (C_drift / ceBeta1) * liftEps c ≤ 1 := by
      have : C_drift / ceBeta1 ≤ B_shell :=
        (le_add_of_nonneg_right zero_le_one).trans ((le_max_left _ _).trans (le_max_right _ _))
      calc (C_drift / ceBeta1) * liftEps c ≤ B_shell * liftEps c := mul_le_mul_of_nonneg_right this hε0.le
        _ ≤ 1 := h_c13_le
    have hts : |t / ceBeta1| ≤ B_t / ceBeta1 := by
      rw [abs_div, abs_of_pos ceBeta1_pos]; exact div_le_div_of_nonneg_right ht_bd ceBeta1_pos.le
    calc |hbS c (Δ / c)| = |(hbS c (Δ / c) + t / ceBeta1) - t / ceBeta1| := by ring_nf
      _ ≤ |hbS c (Δ / c) + t / ceBeta1| + |t / ceBeta1| := abs_sub _ _
      _ ≤ 1 + B_t / ceBeta1 := add_le_add (hdiv.trans hCd1) hts
  have hΔ_rew : c / π ^ 2 - (t / hankelBeta1) * c ^ (1 / 3 : ℝ) + r = Δ := rfl
  rw [hΔ_rew]
  refine ⟨hΔ_pos, ?_⟩
  set ξ : ℝ := Δ / c
  have hFcont : Continuous (ceHbFseed ds K c) := hE.F_cont hK1 (by linarith) (hc_8K.trans hc) (hc_δt.trans hc)
  have hδ₀_pos : 0 < ceBeta1 * K * liftEps c / 2 := by have := ceBeta1_pos; positivity
  have hwin_eq := hE.conv hFcont hδ₀_pos (-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs))
  obtain ⟨j, hj', hjt'⟩ : ∃ j : Fin ds.S.m₀, j.val + 1 < ds.S.m₀ ∧ ds.S.nodes j = t := by
    rw [ds.hS_eq]; exact hbSeedSpec_of_shellHBData_exists_site D ds.hOdd htS htm
  have hfloor_val : (K / 2) * liftEps c ≤
      windowSmooth (ceBeta1 * K * liftEps c / 2) 4 (ceHbFseed ds K c) (-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs)) := by
    rw [hwin_eq]
    have hint_c := integrableOn_bspline_const (by norm_num : 1 ≤ 4) hδ₀_pos ((K / 2) * liftEps c)
    have hint_F := integrableOn_continuous_shift_bspline (by norm_num : 1 ≤ 4) hδ₀_pos
      (x := ceBeta1 * hbS c ξ + liftEps c / (2 * ceCs)) hFcont
    have hint_F' : IntegrableOn (fun t' : ℝ => ceHbFseed ds K c (-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs) + t') *
        bspline 4 (ceBeta1 * K * liftEps c / 2) t') (Icc 0 (ceBeta1 * K * liftEps c / 2)) :=
      hint_F.congr_fun (fun t' _ => by ring_nf) measurableSet_Icc
    calc (K / 2) * liftEps c = ((K / 2) * liftEps c) * 1 := (mul_one _).symm
      _ = ((K / 2) * liftEps c) * ∫ t' in Icc (0 : ℝ) (ceBeta1 * K * liftEps c / 2),
            bspline 4 (ceBeta1 * K * liftEps c / 2) t' := by rw [bspline_setIntegral_one (by norm_num) hδ₀_pos]
      _ = ∫ t' in Icc (0 : ℝ) (ceBeta1 * K * liftEps c / 2),
            ((K / 2) * liftEps c) * bspline 4 (ceBeta1 * K * liftEps c / 2) t' := (integral_const_mul _ _).symm
      _ ≤ _ := by
          refine setIntegral_mono_on hint_c hint_F' measurableSet_Icc fun t' ht' => ?_
          refine mul_le_mul_of_nonneg_right ?_ (bspline_nonneg 4 hδ₀_pos t')
          let u : ℝ := -(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs) + t'
          have hu_dist : |u - t| ≤ ceBeta1 * (K * liftEps c) := by
            have hK2 : C_drift + 1 / (2 * ceCs) ≤ ceBeta1 * K / 2 := by
              have h1 : 2 * (C_drift + 1 / (2 * ceCs)) / ceBeta1 ≤ K :=
                (le_add_of_nonneg_right zero_le_one).trans ((le_max_right _ _).trans hK)
              have hβ0 := ceBeta1_pos
              calc C_drift + 1 / (2 * ceCs) = ceBeta1 * (2 * (C_drift + 1 / (2 * ceCs)) / ceBeta1) / 2 := by
                    field_simp [hβ0.ne']
                _ ≤ ceBeta1 * K / 2 := by gcongr
            have ht'_bd : |t'| ≤ (ceBeta1 * K / 2) * liftEps c := by
              rw [abs_of_nonneg ht'.1]; exact ht'.2.trans_eq (by ring)
            have hcs_bd : |liftEps c / (2 * ceCs)| = (1 / (2 * ceCs)) * liftEps c := by
              have := ceCs_pos; rw [abs_of_nonneg (by positivity)]; ring
            calc |u - t| = |-(ceBeta1 * hbS c ξ + t) - liftEps c / (2 * ceCs) + t'| := congrArg abs (by dsimp [u]; ring)
              _ ≤ |-(ceBeta1 * hbS c ξ + t) - liftEps c / (2 * ceCs)| + |t'| := abs_add_le _ _
              _ ≤ (|ceBeta1 * hbS c ξ + t| + |liftEps c / (2 * ceCs)|) + |t'| :=
                  add_le_add_left ((abs_sub (-(ceBeta1 * hbS c ξ + t)) _).trans_eq (by rw [abs_neg])) _
              _ ≤ C_drift * liftEps c + (1 / (2 * ceCs)) * liftEps c + (ceBeta1 * K / 2) * liftEps c := by
                  rw [hcs_bd]; exact add_le_add (add_le_add hnb.2 le_rfl) ht'_bd
              _ = (C_drift + 1 / (2 * ceCs) + ceBeta1 * K / 2) * liftEps c := by ring
              _ ≤ (ceBeta1 * K / 2 + ceBeta1 * K / 2) * liftEps c := by gcongr
              _ = ceBeta1 * (K * liftEps c) := by ring
          have hfl := (ds.hF_mass_floor hK1 (hc_η.trans hc) (hc_8K.trans hc) (hc_δ.trans hc)).2.2
            j hj' u (by rw [hjt']; exact hu_dist)
          dsimp only at hfl
          have hFeq : ceHbFseed ds K c u = ds.S.G_N u - ds.γ₁ * (K * liftEps c) * ds.S.H_N u +
              ds.γ₂ * (K * liftEps c) * ceSb ds.b u + (-ds.r_eta K c) * (airySeedG 0 (u : ℂ)).re := rfl
          rw [hFeq]; linarith
  have he_m := he5_m hK1 (hc_8K.trans hc) (hc_δt.trans hc) (hc32.trans hc) hξ_pos hSw
  have he_d := he5_d hK1 (hc32.trans hc) hξ_pos hSw
  have hKeps : K * liftEps c ≤ 1 / 2 := liftEps_mul_le_half (by linarith) (hc_8K.trans hc)
  have hcond : 0 < K ∧ 2000 ≤ c ∧ K * liftEps c ≤ 2 := ⟨by linarith, by linarith, by linarith⟩
  have hD_eq : (fun u : ℝ => -(if 0 < K ∧ 2000 ≤ c ∧ K * liftEps c ≤ 2 then
      ds.M_K K c * convSourceFamily (3 / 4) 1 1 1 c u else 0)) =
      fun u => -(ceHbSsrc ds K c u) := by ext u; dsimp [ceHbSsrc]; simp [hcond]
  rw [hD_eq] at he_d
  have hinv_le : ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ ≤ 1 := by
    have : 0 ≤ ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ) := by have := ceBeta1_pos; positivity
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have hc23_le : liftEps c ^ 2 ≤ c ^ (-(1 / 2 : ℝ)) := by
    unfold liftEps; rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hc0.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have herr_m : C_m * ξ⁻¹ * (liftEps c ^ 2 + ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ *
      c ^ (-(1 / 2 : ℝ))) ≤ 2 * C_m * ξ⁻¹ * c ^ (-(1 / 2 : ℝ)) := by
    have : liftEps c ^ 2 + ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ * c ^ (-(1 / 2 : ℝ)) ≤
        2 * c ^ (-(1 / 2 : ℝ)) := by
      have hc12 : 0 ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hc0.le _
      calc _ ≤ c ^ (-(1 / 2 : ℝ)) + 1 * c ^ (-(1 / 2 : ℝ)) := by gcongr
        _ = 2 * c ^ (-(1 / 2 : ℝ)) := by ring
    calc C_m * ξ⁻¹ * _ ≤ C_m * ξ⁻¹ * (2 * c ^ (-(1 / 2 : ℝ))) := by gcongr
      _ = 2 * C_m * ξ⁻¹ * c ^ (-(1 / 2 : ℝ)) := by ring
  let targ : ℝ := ceK * ceBeta1 / (Real.pi ^ 2 * ξ) *
    windowSmooth (ceBeta1 * K * liftEps c / 2) 4 (ceHbFseed ds K c) (-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs))
  have htarg_lo : η_main * liftEps c * ξ⁻¹ ≤ targ := by
    have hpref : 0 ≤ ceK * ceBeta1 / (Real.pi ^ 2 * ξ) := by have := ceK_pos; have := ceBeta1_pos; positivity
    calc η_main * liftEps c * ξ⁻¹ = ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * ((K / 2) * liftEps c) := by
          dsimp [η_main]; field_simp [hξ_pos.ne', Real.pi_ne_zero]
      _ ≤ targ := mul_le_mul_of_nonneg_left hfloor_val hpref
  have hnorm_tot : ‖iMain (ceHbFseed ds K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ +
      iDual (fun u => -(ceHbSsrc ds K c u)) (ceBeta1 * K * liftEps c / 2) 4 c ξ - (targ : ℂ)‖ < targ := by
    have htri : ‖(iMain (ceHbFseed ds K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ +
        iDual (fun u => -(ceHbSsrc ds K c u)) (ceBeta1 * K * liftEps c / 2) 4 c ξ) - (targ : ℂ)‖ ≤
        ‖iMain (ceHbFseed ds K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ - (targ : ℂ)‖ +
          ‖iDual (fun u => -(ceHbSsrc ds K c u)) (ceBeta1 * K * liftEps c / 2) 4 c ξ‖ := by
      simpa only [add_sub_right_comm] using norm_add_le
        (iMain (ceHbFseed ds K c) (ceBeta1 * K * liftEps c / 2) 4 c ξ - (targ : ℂ))
        (iDual (fun u => -(ceHbSsrc ds K c u)) (ceBeta1 * K * liftEps c / 2) 4 c ξ)
    have hc16_bound : c ^ (-(1 / 6 : ℝ)) ≤ η_main / (2 * C_err) := by
      have hc16_pos : 0 < c ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hc0 _
      rw [Real.rpow_neg hc0.le, ← one_div, div_le_iff₀ hc16_pos]
      have h1 : 2 * C_err / η_main ≤ B_shell :=
        (le_add_of_nonneg_right zero_le_one).trans ((le_max_right _ _).trans (le_max_right _ _))
      calc (1 : ℝ) = (η_main / (2 * C_err)) * (2 * C_err / η_main) := by field_simp [hη_main.ne', hC_err.ne']
        _ ≤ (η_main / (2 * C_err)) * B_shell := by gcongr
        _ ≤ (η_main / (2 * C_err)) * c ^ (1 / 6 : ℝ) := by gcongr
    have herr_c13 : C_err * c ^ (-(1 / 2 : ℝ)) < η_main * liftEps c := by
      have hprod : liftEps c * c ^ (-(1 / 6 : ℝ)) = c ^ (-(1 / 2 : ℝ)) := by
        unfold liftEps; rw [← Real.rpow_add hc0]; norm_num
      have hlt : C_err * c ^ (-(1 / 6 : ℝ)) ≤ η_main / 2 := by
        calc C_err * c ^ (-(1 / 6 : ℝ)) ≤ C_err * (η_main / (2 * C_err)) := by gcongr
          _ = η_main / 2 := by field_simp [hC_err.ne']
      calc C_err * c ^ (-(1 / 2 : ℝ)) = (C_err * c ^ (-(1 / 6 : ℝ))) * liftEps c := by rw [← hprod]; ring
        _ ≤ (η_main / 2) * liftEps c := mul_le_mul_of_nonneg_right hlt hε0.le
        _ < η_main * liftEps c := by linarith [mul_pos hη_main hε0]
    calc ‖_‖ ≤ 2 * C_m * ξ⁻¹ * c ^ (-(1 / 2 : ℝ)) + C_d * ξ⁻¹ * c ^ (-(1 / 2 : ℝ)) :=
          htri.trans (add_le_add (he_m.trans herr_m) he_d)
      _ = (C_err * c ^ (-(1 / 2 : ℝ))) * ξ⁻¹ := by dsimp [C_err]; ring
      _ < (η_main * liftEps c) * ξ⁻¹ := mul_lt_mul_of_pos_right herr_c13 (inv_pos.mpr hξ_pos)
      _ ≤ targ := htarg_lo
  exact re_pos_of_norm_lt hnorm_tot

/-- **Theorem `thm:ce-hb-lift`** (`ce_hb_lift.tex`, all Hermite–Biehler levels `m₀ ≥ 1`):
unconditional proof of `CeHbLift D` for every `D : ShellHBData`. -/
theorem ce_hb_lift_proved (D : ShellHBData) : CeHbLift D := by
  intro hL R_off hR
  obtain ⟨sys⟩ := ce_hb_dual_system_exists D hL
  obtain ⟨K_o6, hKo6, htail_of_K⟩ := ceHb_tail_pos_exists sys
  obtain ⟨K_win, hKwin, hwin_of_K⟩ := ceHb_window_pos_exists sys hR
  let K : ℝ := max sys.K_post (max K_o6 K_win)
  have hK_post : sys.K_post ≤ K := le_max_left _ _
  have hK_o6 : K_o6 ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hK_win : K_win ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨K₀_tail, c_tail, hK₀t, hct_2k, hct_8K, hct_δ, hct_η, htail_pos⟩ := htail_of_K hK_o6
  obtain ⟨c_win, hcw_32k, hcw_8K, hcw_δ, hcw_η, hwin_pos⟩ := hwin_of_K hK_win
  let c_req : ℝ := max (sys.c_min K) (max c_tail c_win)
  let K₀ : ℝ := max K₀_tail 1
  let d₀ : ℕ := max (⌈2 * c_req⌉₊ + 2) (⌈2 * Real.pi ^ 2 * (|K₀| + 1)⌉₊ + 2)
  refine ⟨K₀, d₀, fun d hd r hr => ?_⟩
  let c : ℝ := (d : ℝ) / 2
  have hc_ge : c_req ≤ c := by
    have hd_r : 2 * c_req ≤ (d : ℝ) := by
      have hceil : 2 * c_req ≤ (⌈2 * c_req⌉₊ : ℝ) := Nat.le_ceil _
      have hdd : (⌈2 * c_req⌉₊ : ℝ) ≤ (d : ℝ) := by exact_mod_cast le_trans (Nat.le_add_right _ 2) (le_trans (le_max_left _ _) hd)
      linarith
    dsimp [c]; linarith
  have hc_min : sys.c_min K ≤ c := (le_max_left _ _).trans hc_ge
  have hc_tail : c_tail ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hc_ge)
  have hc_win : c_win ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans hc_ge)
  have hc0 : 0 < c := by linarith [sys.hc_min_2k hK_post]
  have hd2 : 2 ≤ d := le_trans (le_trans (by omega : 2 ≤ ⌈2 * c_req⌉₊ + 2) (le_max_left _ _)) hd
  let n : ℕ := d - 1
  have hn : 1 ≤ n := by omega
  have hnd : n + 1 = d := by omega
  have hc_eq : ((n : ℝ) + 1) / 2 = c := by
    have : ((n + 1 : ℕ) : ℝ) = (d : ℝ) := by exact_mod_cast hnd
    push_cast at this; dsimp [c]; linarith
  have hc12 : 1 / 2 < c := by linarith [sys.hc_min_2k hK_post]
  let G : ℝ → ℝ := fun Δ => (sys.fp K c Δ + sys.fm K c Δ) / 2
  let T : ℝ := (d : ℝ) / (2 * π ^ 2) - (D.tm / hankelBeta1) * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) + K₀
  have hT_pos : 0 < T := by
    have hK₀1 : 1 ≤ K₀ := le_max_right _ _
    have htm_nn : 0 ≤ -(D.tm / hankelBeta1) * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) := by
      have htm_neg : D.tm < 0 := lt_of_le_of_lt D.tm_le_airyZero_one (by linarith [airyZero_one.2])
      have hdiv_nn : 0 ≤ -(D.tm / hankelBeta1) :=
        neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg htm_neg.le hankelBeta1_pos.le)
      exact mul_nonneg hdiv_nn (Real.rpow_nonneg hc0.le _)
    have hd_pos : 0 < (d : ℝ) / (2 * π ^ 2) := by positivity
    dsimp [T]; linarith
  have hG_tail : ∀ Δ : ℝ, T ≤ Δ → G Δ ≤ 0 := by
    intro Δ hΔ
    have hT' : c / π ^ 2 - (D.tm / hankelBeta1) * c ^ (1 / 3 : ℝ) + K₀_tail ≤ Δ := by
      have h1 : K₀_tail ≤ K₀ := le_max_left _ _
      have h2 : (d : ℝ) / (2 * π ^ 2) = c / π ^ 2 := by dsimp [c]; ring
      dsimp [T] at hΔ; linarith
    have hΔ0 : 0 < Δ := lt_of_lt_of_le hT_pos hΔ
    have hξ0 : 0 < Δ / c := div_pos hΔ0 hc0
    have hphys := congrArg Complex.re (sys.hphys_neg_eq hK_post hc_min hξ0)
    rw [Complex.ofReal_re] at hphys
    have hpos := htail_pos hc_tail hT'
    rw [← hphys] at hpos
    have hpre : 0 < c ^ (1 / 3 : ℝ) * hankelRho0 c (c * (Δ / c)) :=
      mul_pos (Real.rpow_pos_of_pos hc0 _) (hankelRho0_pos hc0 (by positivity))
    have hcξ : c * (Δ / c) = Δ := by field_simp [hc0.ne']
    rw [hcξ] at hpos hpre
    have hneg : 0 < -(sys.fp K c Δ + sys.fm K c Δ) / 2 := pos_of_mul_pos_right hpos hpre.le
    dsimp [G]; linarith
  have hpair := ceHankelPair_of_eigenfns (T := T) hc12 (sys.hp hK_post hc_min) (sys.hm hK_post hc_min)
    (sys.hfm0 hK_post hc_min) (sys.hfp0 hK_post hc_min)
    (fun Δ hΔ => by linarith [sys.hhat_pos hK_post hc_min hΔ])
    (fun Δ hΔ => by linarith [show (sys.fp K c Δ + sys.fm K c Δ) / 2 ≤ 0 from hG_tail Δ hΔ])
  have hL1 := ceAdmissible_of_hankelPair n hn hT_pos hpair.1
    (by simpa [hc_eq] using hpair.2.1) (by simpa [hc_eq] using hpair.2.2.1)
    (by simpa [hc_eq] using hpair.2.2.2.1) hpair.2.2.2.2.1
    (by simpa [hc_eq] using hpair.2.2.2.2.2.1) hpair.2.2.2.2.2.2
  have hL1d : IsContinuousL1CEAdmissible d (√(2 * T)) (fun x : Euc d => G (‖x‖ ^ 2 / 2)) := by
    have hd_eq : n + 1 = d := hnd
    rw [← hd_eq]; exact hL1
  have hsh : IsShellAdmissible D r d (√(2 * T)) (fun x : Euc d => G (‖x‖ ^ 2 / 2)) := by
    refine ⟨hL1d, fun x y hxy => by rw [hxy], fun t htS htm x hx => ?_⟩
    rw [hx]
    have hsite_eq : shellSite t (r t) d = c / π ^ 2 - (t / hankelBeta1) * c ^ (1 / 3 : ℝ) + r t d := by
      dsimp [shellSite, c]; ring
    rw [hsite_eq]
    obtain ⟨hΔ_pos, hpos⟩ := hwin_pos (hc_win.trans (le_rfl)) htS htm (hr t d)
    have hξ0 : 0 < (c / π ^ 2 - (t / hankelBeta1) * c ^ (1 / 3 : ℝ) + r t d) / c := div_pos hΔ_pos hc0
    have hphys := congrArg Complex.re (sys.hphys_neg_eq hK_post hc_min hξ0)
    rw [Complex.ofReal_re] at hphys
    rw [← hphys] at hpos
    set Δ := c / π ^ 2 - (t / hankelBeta1) * c ^ (1 / 3 : ℝ) + r t d
    have hpre : 0 < c ^ (1 / 3 : ℝ) * hankelRho0 c (c * (Δ / c)) :=
      mul_pos (Real.rpow_pos_of_pos hc0 _) (hankelRho0_pos hc0 (by positivity))
    have hcξ : c * (Δ / c) = Δ := by field_simp [hc0.ne']
    rw [hcξ] at hpos hpre
    have hneg : 0 < -(sys.fp K c Δ + sys.fm K c Δ) / 2 := pos_of_mul_pos_right hpos hpre.le
    dsimp [G]; linarith
  refine ⟨√(2 * T), ⟨_, hsh⟩, ?_⟩
  rw [Real.sq_sqrt (by linarith)]
  dsimp [T]; linarith

/-- info: 'FormalResearch.SignUncertainty.ce_hb_lift_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.ce_hb_lift_proved

end FormalResearch.SignUncertainty
