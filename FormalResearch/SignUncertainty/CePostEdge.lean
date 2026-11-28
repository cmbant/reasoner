module

public import FormalResearch.SignUncertainty.ConvSourceFarTransfer
public import FormalResearch.SignUncertainty.MiddleBandTransfer
public import FormalResearch.SignUncertainty.UctPosFloorSeed
public import FormalResearch.CohnElkies.DualBoundE3

/-!
# Post-edge Fourier positivity (`thm:ce-post-edge`)

Reference: `CFT/sign_uncertainty/paper/ce_o1_global_transfer.tex` (`thm:ce-post-edge`, `cegt:GT3`),
with the far-range transfer `ceo:conv` (7) from `ConvSourceFarTransfer`.

Proves:
1. `gt1Bounds_convSource_unif`: uniform `GT.1` symbol bounds for `convSourceFamily p γ θ lam c`
   with constant independent of `c ≥ 1` and `δ₀ ∈ [0, 2]`;
2. `ce_post_edge` (`thm:ce-post-edge`): abstract post-edge Fourier sign for any family `(S_c, D_c)`
   satisfying the moving-source symbol, floor, far-transfer hypotheses and uniform dual `U.2`
   bound;
3. `ce_post_edge_convSource`: instantiation of `ce_post_edge` for `S_c = convSourceFamily p γ θ lam c`
   with `p ∈ (1/2, 1)`, `γ > 0`, `θ > 0`, `λ > 0`, `m ≥ 4`.
-/

@[expose] public section

open Real Complex MeasureTheory Set Filter Topology

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-! ### 1. Uniform `GT.1` symbol bounds and `convRho` floor for `convSourceFamily` -/

/-- Uniform `GT.1` symbol bounds for `convSourceFamily p γ θ lam c` across all `c ≥ 1` and
`δ₀ ∈ [0, 2]`, obtained by monotonicity of `LapBounds` from `0 < liftEps c ≤ 1`. -/
theorem gt1Bounds_convSource_unif {p γ θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1)
    (hlam : 0 < lam) {m : ℕ} (hm : 3 ≤ m) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {c δ₀ : ℝ}, 1 ≤ c → δ₀ ∈ Icc (0 : ℝ) 2 →
      Gt1Bounds A (liftW (convSourceFamily p γ θ lam c) δ₀ m) := by
  obtain ⟨A1, hA1, hb⟩ := gt1BasisInput m hm
  obtain ⟨C, hC⟩ := convInterior_convWh hp hp1
  have hC0 : 0 ≤ C := (hC 1 one_pos).nonneg
  have ha : 1 ≤ ceCs := convEdge_one_le_ceCs
  set B : ℝ := 2 * (24 * |γ|) * ceCs ^ 3 + |θ| * (2 * C * ceCs ^ 3)
  have hB0 : 0 ≤ B := by positivity
  refine ⟨9 * A1 * B, by positivity, fun {c δ₀} hc hδ => ?_⟩
  have hc0 : 0 < c := by linarith
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  have hε1 : liftEps c ≤ 1 := liftEps_le_one hc
  have hh : 0 < lam * liftEps c ^ 2 := by positivity
  have hE := (lapBounds_of_interior ha (convInterior_exp γ (liftEps c))).mono (show 2 * (24 * |γ * liftEps c|) * ceCs ^ 3 ≤ 2 * (24 * |γ|) * ceCs ^ 3 by
    have habs : |γ * liftEps c| ≤ |γ| := by
      rw [abs_mul, abs_of_pos hε0]
      exact mul_le_of_le_one_right (abs_nonneg γ) hε1
    have hcs3 : 0 ≤ ceCs ^ 3 := pow_nonneg (by positivity) 3
    gcongr)
  have hW := (lapBounds_of_interior ha (hC (lam * liftEps c ^ 2) hh)).smul (θ : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs] at hW
  have hL_tot : LapBounds B (fun v : ℝ => lapW (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2))
      ((((ceCs * v : ℝ)) : ℂ) * Complex.I)) := by
    have hsum : LapBounds B (fun s : ℝ =>
        lapW (convWe γ (liftEps c)) ((((ceCs * s : ℝ)) : ℂ) * Complex.I) +
          (θ : ℂ) * lapW (convWh p (lam * liftEps c ^ 2)) ((((ceCs * s : ℝ)) : ℂ) * Complex.I)) :=
      (hE.add hW).mono (by dsimp [B]; nlinarith [pow_nonneg (by positivity : 0 ≤ ceCs) 3])
    have hfun : (fun v : ℝ => lapW (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2))
        ((((ceCs * v : ℝ)) : ℂ) * Complex.I)) = fun s =>
          lapW (convWe γ (liftEps c)) ((((ceCs * s : ℝ)) : ℂ) * Complex.I) +
            (θ : ℂ) * lapW (convWh p (lam * liftEps c ^ 2)) ((((ceCs * s : ℝ)) : ℂ) * Complex.I) :=
      funext fun v => lapW_convWc hp hp1 hh (by simp)
    rw [hfun]; exact hsum
  have hU : Gt1Bounds A1 (liftW (ceG1 (airyZero 1)) δ₀ m) := by
    have := (hb δ₀ hδ).2.1
    rwa [show airySeedU2 0 1 0 = ceG1 (airyZero 1) from funext fun u => by simp [airySeedU2]] at this
  have hmul := hU.mul_lap hL_tot
  have hfam : convSourceFamily p γ θ lam c = convSource p γ θ (liftEps c) (lam * liftEps c ^ 2) := rfl
  have hfun : liftW (convSourceFamily p γ θ lam c) δ₀ m = fun v =>
      liftW (ceG1 (airyZero 1)) δ₀ m v *
        lapW (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2)) ((((ceCs * v : ℝ)) : ℂ) * Complex.I) := by
    funext v; rw [hfam]; exact liftW_convSource_eq hp hp1 hh δ₀ m v
  rw [hfun]; exact hmul

lemma convRho_min_lower {p t : ℝ} (hp : 0 ≤ p) (ht : 0 ≤ t) :
    (1 / 2 : ℝ) ^ p * (min 1 t) ^ p ≤ convRho p t := by
  unfold convRho
  rw [← Real.mul_rpow (by norm_num) (le_min zero_le_one ht)]
  refine Real.rpow_le_rpow (by positivity) ?_ hp
  by_cases h1 : t ≤ 1
  · rw [min_eq_right h1, show (1 / 2 : ℝ) * t = t / 2 by ring]
    exact div_le_div_of_nonneg_left ht (by linarith) (by linarith)
  · have ht1 : 1 ≤ t := (not_le.mp h1).le
    rw [min_eq_left ht1, show (1 / 2 : ℝ) * 1 = 1 / 2 by ring, div_le_div_iff₀ two_pos (by linarith)]
    linarith

private lemma liftSymbol_norm_of_rhp_unif {X : ℝ → ℝ} {CS : ℝ} (hCS : 0 ≤ CS)
    (hb : ∀ {w : ℂ}, 0 ≤ w.re → ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ CS * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖liftSymbol X δ₀ m w‖ ≤ (CS * 2 ^ (5 / 2 : ℝ) + 1) * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by
  have h1 : 0 < 1 + |w.im| := by positivity
  have h2 := one_add_abs_im_le_two_mul_norm_one_add hw
  have hpow : ‖1 + w‖ ^ (-(5 / 2 : ℝ)) ≤ 2 ^ (5 / 2 : ℝ) * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by
    have h3 : (1 + |w.im|) / 2 ≤ ‖1 + w‖ := by linarith
    calc ‖1 + w‖ ^ (-(5 / 2 : ℝ)) ≤ ((1 + |w.im|) / 2) ^ (-(5 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h3 (by norm_num)
      _ = 2 ^ (5 / 2 : ℝ) * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by
          rw [Real.div_rpow h1.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]; ring
  unfold liftSymbol
  rw [norm_mul]
  have hT_nn : 0 ≤ (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg h1.le _
  calc ‖liftMultiplier δ₀ m w‖ * ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖
      ≤ 1 * (CS * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) :=
        mul_le_mul (norm_liftMultiplier_le_one hδ m hw) (hb hw) (norm_nonneg _) zero_le_one
    _ = CS * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := one_mul _
    _ ≤ CS * (2 ^ (5 / 2 : ℝ) * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) := by gcongr
    _ ≤ (CS * 2 ^ (5 / 2 : ℝ) + 1) * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by nlinarith

/-! ### 2. Post-edge regimes (`ce_post_edge`, `thm:ce-post-edge`) -/

private lemma ce_post_edge_small_L
    {p lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hlam : 0 < lam)
    {m : ℕ} (hm : 4 ≤ m)
    {S : ℝ → ℝ → ℝ}
    (hU2S : ∀ {c : ℝ}, 2 ≤ c → HasU2 (S c))
    (hcontS : ∀ {c : ℝ}, 2 ≤ c → Continuous (S c))
    (hgt1S : ∃ AS : ℝ, 0 ≤ AS ∧ ∀ {c δ₀ : ℝ}, 2 ≤ c → δ₀ ∈ Icc (0 : ℝ) 2 →
      Gt1Bounds AS (liftW (S c) δ₀ m))
    (hrayS : ∃ b_ray > 0, ∃ x₁ ≥ (1 : ℝ), ∀ {c x : ℝ}, 2 ≤ c → x₁ ≤ x →
      b_ray * (min 1 (lam * liftEps c ^ 2 * x)) ^ p * x ^ (-(3 / 2 : ℝ)) ≤ S c (-x))
    {CD : ℝ} (hCD : 0 ≤ CD) :
    ∃ L_F S_star : ℝ, 0 < L_F ∧ L_F ≤ 0.002 ∧ 100 ≤ S_star ∧
      ∀ {κ : ℝ}, 1 ≤ κ → ∀ {D : ℝ → ℝ → ℝ},
        (∀ {c : ℝ}, 2 ≤ c → DifferentiableOn ℂ (airyTwistedLaplaceC (D c)) {y : ℂ | 0 < y.re}) →
        (∀ {c : ℝ} {w : ℂ}, 2 ≤ c → 0 ≤ w.re →
          ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤ CD * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) →
        ∃ c₁ ≥ (2 : ℝ), ∀ {c ξ : ℝ}, c₁ ≤ c → 0 < ξ →
          S_star ≤ hbS c ξ → Real.log (Real.pi ^ 2 * ξ) ≤ L_F →
          0 < (iMain (S c) (κ * liftEps c) m c ξ + iDual (D c) (κ * liftEps c) m c ξ).re := by
  obtain ⟨ϑ, K1, K2, hϑ⟩ := prof_exists
  obtain ⟨AS, hAS, hgt⟩ := hgt1S
  obtain ⟨C_mt, hCmt, hmid⟩ := middle_transfer_gt1 hϑ AS hAS
  obtain ⟨b_ray, hbray, x₁, hx₁, hray⟩ := hrayS
  obtain ⟨C_e3, hCe3, he3⟩ := iDual_bound_e3 (by omega : 3 ≤ m) hCD
  have hcs0 : 0 < ceCs := ceCs_pos
  have hβ0 : 0 < ceBeta1 := ceBeta1_pos
  have hβ2 : 2 < ceBeta1 := ceBeta1_gt_two
  have hk0 : 0 < ceK := ceK_pos
  have hpi0 : 0 < Real.pi := Real.pi_pos
  obtain ⟨b_mid, hbmid_def⟩ : ∃ b_mid : ℝ,
      b_mid = (ceK / ceCs) * b_ray * (lam / (2 * ceCs)) ^ p * (3 * ceBeta1) ^ (-(3 / 2 : ℝ)) := ⟨_, rfl⟩
  have hbmid : 0 < b_mid := by rw [hbmid_def]; positivity
  set L_cap : ℝ := min 0.002 (2 * ceCs / lam)
  have hLcap : 0 < L_cap := by positivity
  set q₁ : ℝ := 1 - p
  set q₂ : ℝ := 5 / 4 - p
  have hq₁ : 0 < q₁ := by dsimp [q₁]; linarith
  have hq₂ : 0 < q₂ := by dsimp [q₂]; linarith
  obtain ⟨A₁, hA1_def⟩ : ∃ A₁ : ℝ, A₁ = (b_mid / (4 * (C_mt + 1))) ^ q₁⁻¹ := ⟨_, rfl⟩
  obtain ⟨A₂, hA2_def⟩ : ∃ A₂ : ℝ, A₂ = (b_mid * Real.pi ^ 3 / (4 * C_e3)) ^ q₂⁻¹ := ⟨_, rfl⟩
  obtain ⟨L_F, hLF_def⟩ : ∃ L_F : ℝ, L_F = min L_cap (min A₁ A₂) := ⟨_, rfl⟩
  have hA1_pos : 0 < A₁ := by rw [hA1_def]; positivity
  have hA2_pos : 0 < A₂ := by rw [hA2_def]; positivity
  have hLF_pos : 0 < L_F := by rw [hLF_def]; exact lt_min hLcap (lt_min hA1_pos hA2_pos)
  have hLF_cap : L_F ≤ L_cap := by rw [hLF_def]; exact min_le_left _ _
  have hLF_002 : L_F ≤ 0.002 := hLF_cap.trans (min_le_left _ _)
  have hLF_lam : L_F ≤ 2 * ceCs / lam := hLF_cap.trans (min_le_right _ _)
  have hLF_A1 : L_F ≤ A₁ := by rw [hLF_def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hLF_A2 : L_F ≤ A₂ := by rw [hLF_def]; exact (min_le_right _ _).trans (min_le_right _ _)
  set S_star : ℝ := max 100 ((x₁ + 4) / ceBeta1)
  have hSstar : 100 ≤ S_star := le_max_left _ _
  refine ⟨L_F, S_star, hLF_pos, hLF_002, hSstar, fun {κ} hκ {D} hdiffD hbdD => ?_⟩
  obtain ⟨R_c2, hRc2_def⟩ : ∃ R_c2 : ℝ,
      R_c2 = ((4 * (C_mt + 1)) / (b_mid * Real.pi ^ 3 * L_F ^ (p - 3 / 2))) ^ (2 / 3 : ℝ) := ⟨_, rfl⟩
  set c₁ : ℝ := max 2 (max ((κ / 2) ^ 3 + 1) (R_c2 + 1))
  refine ⟨c₁, le_max_left _ _, fun {c ξ} hc hξ hS hL => ?_⟩
  have hc2 : 2 ≤ c := (le_max_left _ _).trans hc
  have hc0 : 0 < c := by linarith
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  have hε1 : liftEps c ≤ 1 := liftEps_le_one (by linarith)
  have hδ_pos : 0 < κ * liftEps c := by positivity
  have hδ_le2 : κ * liftEps c ≤ 2 := by
    have hκc : (κ / 2) ^ 3 ≤ c := by
      linarith [le_max_left ((κ / 2) ^ 3 + 1) (R_c2 + 1),
        le_max_right 2 (max ((κ / 2) ^ 3 + 1) (R_c2 + 1))]
    have hκr : κ / 2 ≤ c ^ (1 / 3 : ℝ) := by
      have h1 := Real.rpow_le_rpow (by positivity) hκc (by norm_num : (0 : ℝ) ≤ 1 / 3)
      have h_eq : ((κ / 2) ^ (3 : ℕ) : ℝ) ^ (1 / 3 : ℝ) = κ / 2 := by
        rw [← Real.rpow_natCast (κ / 2) 3, ← Real.rpow_mul (by positivity),
          show ((3 : ℕ) : ℝ) * (1 / 3 : ℝ) = 1 by norm_num, Real.rpow_one]
      exact h_eq.symm.trans_le h1
    have hεc : liftEps c = (c ^ (1 / 3 : ℝ))⁻¹ := by
      unfold liftEps; rw [Real.rpow_neg hc0.le]
    rw [hεc, ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hc0 _)]
    linarith [(div_le_iff₀ (two_pos : (0 : ℝ) < 2)).mp hκr]
  set L : ℝ := Real.log (Real.pi ^ 2 * ξ)
  have hL_eq_S : L = Real.pi ^ 2 * liftEps c ^ 2 * hbS c ξ := log_eq_hbS hc0
  have hS100 : 100 ≤ hbS c ξ := hSstar.trans hS
  have hL_pos : 0 < L := by rw [hL_eq_S]; positivity
  have hL_002 : L ≤ 0.002 := hL.trans hLF_002
  have hmain_mt := hmid (hU2S hc2) (hcontS hc2) hδ_pos.le hc2 hξ rfl hL_pos hL_002 hS100
    (hgt hc2 ⟨hδ_pos.le, hδ_le2⟩)
  -- WindowSmooth floor
  obtain ⟨x_arg, hxarg_def⟩ : ∃ x_arg : ℝ,
      x_arg = (c * liftEps c * edgeAlphaTilde L + liftEps c / 2) / ceCs := ⟨_, rfl⟩
  have hκ_bd := edgeKappa0_bounds hL_pos hL_002
  have hα_lo : L ≤ edgeAlphaTilde L := by
    have h1 := hκ_bd.1; unfold edgeKappa0 at h1
    rw [lt_div_iff₀ hL_pos, one_mul] at h1
    exact h1.le
  have hα_hi : edgeAlphaTilde L ≤ 2 * L := by
    have := hκ_bd.2; unfold edgeKappa0 at this; rw [div_le_iff₀ hL_pos] at this; nlinarith
  have hcε_cube : c * liftEps c ^ 3 = 1 := by linarith [liftEps_cube_mul hc0]
  have hcε_L_eq : c * liftEps c * L / ceCs = ceBeta1 * hbS c ξ := by
    have hcm : Real.pi ^ 2 = ceCs * ceBeta1 := ceCs_mul_ceBeta1.symm
    rw [hL_eq_S, hcm]
    calc c * liftEps c * (ceCs * ceBeta1 * liftEps c ^ 2 * hbS c ξ) / ceCs
        = (ceCs * ceBeta1 * hbS c ξ * (c * liftEps c ^ 3)) / ceCs := by ring
      _ = (ceCs * ceBeta1 * hbS c ξ * 1) / ceCs := by rw [hcε_cube]
      _ = ceBeta1 * hbS c ξ := by field_simp [hcs0.ne']
  have hx_arg_lo : ceBeta1 * hbS c ξ ≤ x_arg := by
    rw [hxarg_def]
    have h1 : c * liftEps c * L ≤ c * liftEps c * edgeAlphaTilde L + liftEps c / 2 := by
      have : 0 ≤ c * liftEps c := by positivity
      linarith [mul_le_mul_of_nonneg_left hα_lo this]
    calc ceBeta1 * hbS c ξ = c * liftEps c * L / ceCs := hcε_L_eq.symm
      _ ≤ (c * liftEps c * edgeAlphaTilde L + liftEps c / 2) / ceCs := by gcongr
  have hx_arg_hi : x_arg ≤ 2 * ceBeta1 * hbS c ξ + 1 := by
    rw [hxarg_def]
    have h1 : c * liftEps c * edgeAlphaTilde L / ceCs ≤ 2 * (c * liftEps c * L / ceCs) := by
      rw [show 2 * (c * liftEps c * L / ceCs) = c * liftEps c * (2 * L) / ceCs by ring]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hα_hi (by positivity)) hcs0.le
    have h2 : liftEps c / 2 / ceCs ≤ 1 := by
      have hcs1 : 1 ≤ ceCs := convEdge_one_le_ceCs
      calc liftEps c / 2 / ceCs ≤ 1 / 2 / 1 := by gcongr
        _ ≤ 1 := by norm_num
    calc (c * liftEps c * edgeAlphaTilde L + liftEps c / 2) / ceCs
        = c * liftEps c * edgeAlphaTilde L / ceCs + liftEps c / 2 / ceCs := by ring
      _ ≤ 2 * (c * liftEps c * L / ceCs) + 1 := add_le_add h1 h2
      _ = 2 * ceBeta1 * hbS c ξ + 1 := by rw [hcε_L_eq]; ring
  have hS_x1 : (x₁ + 4) / ceBeta1 ≤ hbS c ξ := (le_max_right _ _).trans hS
  have hβS : x₁ + 4 ≤ ceBeta1 * hbS c ξ := by rw [mul_comm]; exact (div_le_iff₀ hβ0).mp hS_x1
  have hβS_200 : 200 ≤ ceBeta1 * hbS c ξ := by
    have hmul := mul_le_mul hβ2.le hS100 (by norm_num) hβ0.le
    linarith only [hmul]
  have hwin_ge : (ceK / ceCs) * (b_ray * ((lam / (2 * ceCs)) * L) ^ p * (3 * ceBeta1 * hbS c ξ) ^ (-(3 / 2 : ℝ))) ≤
      (ceK / ceCs) * windowSmooth (κ * liftEps c) m (S c) (-x_arg) := by
    refine mul_le_mul_of_nonneg_left (windowSmooth_ge (hcontS hc2) hδ_pos (by omega) (-x_arg) _ fun t ht => ?_) (by positivity)
    set x : ℝ := x_arg - t
    have h_neg : -x_arg + t = -x := by dsimp [x]; ring
    rw [h_neg]
    have hx_lo : ceBeta1 * hbS c ξ / 2 ≤ x := by
      dsimp [x]; linarith only [ht.2, hδ_le2, hx_arg_lo, hβS_200]
    have hx_x1 : x₁ ≤ x := by
      dsimp [x]; linarith only [ht.2, hδ_le2, hx_arg_lo, hβS]
    have hx_hi : x ≤ 3 * ceBeta1 * hbS c ξ := by
      dsimp [x]; linarith only [ht.1, hx_arg_hi, hβS_200]
    have hx0 : 0 < x := by linarith only [hx₁, hx_x1]
    have hmin_ge : (lam / (2 * ceCs)) * L ≤ min 1 (lam * liftEps c ^ 2 * x) := by
      refine le_min ?_ ?_
      · have : L ≤ 2 * ceCs / lam := hL.trans hLF_lam
        calc (lam / (2 * ceCs)) * L ≤ (lam / (2 * ceCs)) * (2 * ceCs / lam) := by gcongr
          _ = 1 := by field_simp [hlam.ne', hcs0.ne']
      · have hcm : Real.pi ^ 2 = ceCs * ceBeta1 := ceCs_mul_ceBeta1.symm
        calc (lam / (2 * ceCs)) * L = lam * (ceBeta1 / (2 * Real.pi ^ 2)) * (Real.pi ^ 2 * liftEps c ^ 2 * hbS c ξ) := by
              rw [← hL_eq_S, hcm]; field_simp [hcs0.ne', hβ0.ne']
          _ = lam * liftEps c ^ 2 * (ceBeta1 * hbS c ξ / 2) := by
              have hpi_ne : Real.pi ≠ 0 := hpi0.ne'; field_simp [hpi_ne]
          _ ≤ lam * liftEps c ^ 2 * x := by gcongr
    have hpow_ge : (3 * ceBeta1 * hbS c ξ) ^ (-(3 / 2 : ℝ)) ≤ x ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hx0 hx_hi (by norm_num)
    have hmin_pow : ((lam / (2 * ceCs)) * L) ^ p ≤ (min 1 (lam * liftEps c ^ 2 * x)) ^ p :=
      Real.rpow_le_rpow (by positivity) hmin_ge (by linarith)
    calc b_ray * ((lam / (2 * ceCs)) * L) ^ p * (3 * ceBeta1 * hbS c ξ) ^ (-(3 / 2 : ℝ))
        ≤ b_ray * (min 1 (lam * liftEps c ^ 2 * x)) ^ p * x ^ (-(3 / 2 : ℝ)) := by gcongr
      _ ≤ S c (-x) := hray hc2 hx_x1
  have hfloor_val : b_mid * L ^ p * hbS c ξ ^ (-(3 / 2 : ℝ)) ≤
      (ceK / ceCs) * windowSmooth (κ * liftEps c) m (S c) (-x_arg) := by
    refine le_trans ?_ hwin_ge
    have h1 : ((lam / (2 * ceCs)) * L) ^ p = (lam / (2 * ceCs)) ^ p * L ^ p :=
      Real.mul_rpow (by positivity) hL_pos.le
    have h2 : (3 * ceBeta1 * hbS c ξ) ^ (-(3 / 2 : ℝ)) =
        (3 * ceBeta1) ^ (-(3 / 2 : ℝ)) * hbS c ξ ^ (-(3 / 2 : ℝ)) :=
      Real.mul_rpow (by positivity) (by linarith : 0 ≤ hbS c ξ)
    rw [h1, h2, hbmid_def]
    exact le_of_eq (by ring)
  -- Main and dual error bounds
  have hS_pow : hbS c ξ ^ (-(3 / 2 : ℝ)) = c⁻¹ * Real.pi ^ 3 * L ^ (-(3 / 2 : ℝ)) := by
    have hS0 : 0 < hbS c ξ := by linarith only [hS100]
    have h1 := inv_mul_log_rpow hc0 hS0
    have h2 : (Real.pi ^ 2 * hbS c ξ) ^ (-(3 / 2 : ℝ)) = Real.pi ^ (-3 : ℝ) * hbS c ξ ^ (-(3 / 2 : ℝ)) := by
      rw [Real.mul_rpow (by positivity) hS0.le, ← Real.rpow_natCast Real.pi 2, ← Real.rpow_mul hpi0.le]; norm_num
    rw [h2] at h1
    have hpi3 : Real.pi ^ (3 : ℝ) * Real.pi ^ (-3 : ℝ) = 1 := by
      rw [← Real.rpow_add hpi0, add_neg_cancel, Real.rpow_zero]
    have hpi3n : Real.pi ^ (3 : ℝ) = Real.pi ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc hbS c ξ ^ (-(3 / 2 : ℝ))
        = Real.pi ^ (3 : ℝ) * (Real.pi ^ (-3 : ℝ) * hbS c ξ ^ (-(3 / 2 : ℝ))) := by
          rw [← mul_assoc, hpi3, one_mul]
      _ = Real.pi ^ 3 * (c⁻¹ * L ^ (-(3 / 2 : ℝ))) := by rw [← h1, hpi3n]
      _ = _ := by ring
  have hc_ge_R : R_c2 ≤ c := by
    linarith only [hc, le_max_right ((κ / 2) ^ 3 + 1) (R_c2 + 1), le_max_right (2 : ℝ) (max ((κ / 2) ^ 3 + 1) (R_c2 + 1))]
  have hmain_err1 : C_mt * (hbS c ξ ^ (-(3 / 2 : ℝ)) * L) ≤ (b_mid / 4) * (L ^ p * hbS c ξ ^ (-(3 / 2 : ℝ))) := by
    have hLq1 : L ^ q₁ ≤ b_mid / (4 * (C_mt + 1)) := by
      have h1 := Real.rpow_le_rpow hL_pos.le (hL.trans hLF_A1) hq₁.le
      have h2 : A₁ ^ q₁ = b_mid / (4 * (C_mt + 1)) := by
        rw [hA1_def, ← Real.rpow_mul (by positivity), inv_mul_cancel₀ hq₁.ne', Real.rpow_one]
      exact h1.trans_eq h2
    have hC1 : C_mt * L ^ q₁ ≤ b_mid / 4 := by
      have hC1p : 0 < C_mt + 1 := by linarith only [hCmt]
      calc C_mt * L ^ q₁ ≤ (C_mt + 1) * (b_mid / (4 * (C_mt + 1))) :=
            mul_le_mul (by linarith only [hCmt]) hLq1 (Real.rpow_nonneg hL_pos.le _) hC1p.le
        _ = b_mid / 4 := by field_simp [hC1p.ne']
    have hL_eq : L = L ^ q₁ * L ^ p := by
      rw [← Real.rpow_add hL_pos, show q₁ + p = 1 by dsimp [q₁]; ring, Real.rpow_one]
    have hLpS_nn : 0 ≤ L ^ p * hbS c ξ ^ (-(3 / 2 : ℝ)) := by positivity
    calc C_mt * (hbS c ξ ^ (-(3 / 2 : ℝ)) * L)
        = (C_mt * L ^ q₁) * (L ^ p * hbS c ξ ^ (-(3 / 2 : ℝ))) := by
          nth_rw 1 [hL_eq]; ring
      _ ≤ (b_mid / 4) * (L ^ p * hbS c ξ ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_right hC1 hLpS_nn
  have hmain_err2 : C_mt * c ^ (-(5 / 2 : ℝ)) ≤ (b_mid / 4) * (L ^ p * hbS c ξ ^ (-(3 / 2 : ℝ))) := by
    have hc32 : c ^ (-(3 / 2 : ℝ)) ≤ (b_mid * Real.pi ^ 3 * L_F ^ (p - 3 / 2)) / (4 * (C_mt + 1)) := by
      have hLF_pow_pos : 0 < L_F ^ (p - 3 / 2) := Real.rpow_pos_of_pos hLF_pos _
      have hRc_pos : 0 < R_c2 := by rw [hRc2_def]; positivity
      have h1' := Real.rpow_le_rpow_of_nonpos hRc_pos hc_ge_R (by norm_num : -(3 / 2 : ℝ) ≤ 0)
      have h2 : R_c2 ^ (-(3 / 2 : ℝ)) = (b_mid * Real.pi ^ 3 * L_F ^ (p - 3 / 2)) / (4 * (C_mt + 1)) := by
        rw [hRc2_def, ← Real.rpow_mul (by positivity), show (2 / 3 : ℝ) * -(3 / 2 : ℝ) = -1 by norm_num,
          Real.rpow_neg_one, inv_div]
      exact h1'.trans_eq h2
    have hLp32 : L_F ^ (p - 3 / 2) ≤ L ^ (p - 3 / 2) :=
      Real.rpow_le_rpow_of_nonpos hL_pos hL (by linarith only [hp1])
    have hpow_c : c ^ (-(5 / 2 : ℝ)) = c ^ (-(3 / 2 : ℝ)) * c⁻¹ := by
      rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0]; norm_num
    have hpow_L : L ^ p * L ^ (-(3 / 2 : ℝ)) = L ^ (p - 3 / 2) := by
      rw [← Real.rpow_add hL_pos, show p + -(3 / 2 : ℝ) = p - 3 / 2 by ring]
    have hC1p : 0 < C_mt + 1 := by linarith only [hCmt]
    have hc32c : c ^ (-(3 / 2 : ℝ)) * c⁻¹ ≤ (b_mid * Real.pi ^ 3 * L_F ^ (p - 3 / 2)) / (4 * (C_mt + 1)) * c⁻¹ :=
      mul_le_mul_of_nonneg_right hc32 (inv_nonneg.mpr hc0.le)
    have hCmt_cancel : (C_mt + 1) * ((b_mid * Real.pi ^ 3 * L_F ^ (p - 3 / 2)) / (4 * (C_mt + 1)) * c⁻¹) =
        (b_mid / 4) * (Real.pi ^ 3 * L_F ^ (p - 3 / 2) * c⁻¹) := by
      field_simp [hC1p.ne']
    calc C_mt * c ^ (-(5 / 2 : ℝ))
        = C_mt * (c ^ (-(3 / 2 : ℝ)) * c⁻¹) := by rw [hpow_c]
      _ ≤ (C_mt + 1) * (c ^ (-(3 / 2 : ℝ)) * c⁻¹) :=
          mul_le_mul_of_nonneg_right (by linarith only [hCmt]) (mul_nonneg (Real.rpow_nonneg hc0.le _) (inv_nonneg.mpr hc0.le))
      _ ≤ (C_mt + 1) * ((b_mid * Real.pi ^ 3 * L_F ^ (p - 3 / 2)) / (4 * (C_mt + 1)) * c⁻¹) :=
          mul_le_mul_of_nonneg_left hc32c hC1p.le
      _ = (b_mid / 4) * (Real.pi ^ 3 * L_F ^ (p - 3 / 2) * c⁻¹) := hCmt_cancel
      _ ≤ (b_mid / 4) * (Real.pi ^ 3 * L ^ (p - 3 / 2) * c⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLp32 (by positivity)) (inv_nonneg.mpr hc0.le)) (by positivity)
      _ = (b_mid / 4) * (L ^ p * hbS c ξ ^ (-(3 / 2 : ℝ))) := by rw [hS_pow, ← hpow_L]; ring
  have hdual_err : ξ * ‖iDual (D c) (κ * liftEps c) m c ξ‖ ≤ (b_mid / 4) * (L ^ p * hbS c ξ ^ (-(3 / 2 : ℝ))) := by
    have he := he3 (hdiffD hc2) (hbdD hc2) ⟨hδ_pos, hδ_le2⟩ hc2 hξ (by linarith only [hS100] : 1 ≤ hbS c ξ)
    have h_m1 : (1 + κ * liftEps c * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) ≤ 1 := by
      have h_nn : 0 ≤ κ * liftEps c * c ^ (1 / 3 : ℝ) :=
        mul_nonneg hδ_pos.le (Real.rpow_nonneg hc0.le (1 / 3 : ℝ))
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [h_nn]) (neg_nonpos.mpr (Nat.cast_nonneg m))
    have hLq2 : L ^ q₂ ≤ b_mid * Real.pi ^ 3 / (4 * C_e3) := by
      have h1 := Real.rpow_le_rpow hL_pos.le (hL.trans hLF_A2) hq₂.le
      have h2 : A₂ ^ q₂ = b_mid * Real.pi ^ 3 / (4 * C_e3) := by
        rw [hA2_def, ← Real.rpow_mul (by positivity), inv_mul_cancel₀ hq₂.ne', Real.rpow_one]
      exact h1.trans_eq h2
    have hL_eq : L ^ (-(1 / 4 : ℝ)) = L ^ q₂ * (L ^ p * L ^ (-(3 / 2 : ℝ))) := by
      rw [← Real.rpow_add hL_pos, ← Real.rpow_add hL_pos]; dsimp [q₂]; congr 1; ring
    have hmin_le : min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) ≤ L ^ (-(1 / 4 : ℝ)) := min_le_left _ _
    have hbd_ξ : ξ * ‖iDual (D c) (κ * liftEps c) m c ξ‖ ≤
        C_e3 * c⁻¹ * L ^ (-(1 / 4 : ℝ)) := by
      have := mul_le_mul_of_nonneg_left he hξ.le
      have h_min_nn : 0 ≤ min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) :=
        le_min (Real.rpow_nonneg hL_pos.le _) (Real.rpow_nonneg hL_pos.le _)
      have hc1_nn : 0 ≤ C_e3 * c⁻¹ := by positivity
      calc ξ * ‖iDual (D c) (κ * liftEps c) m c ξ‖
          ≤ ξ * (C_e3 * ξ⁻¹ * (1 + κ * liftEps c * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) * c⁻¹ *
              min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ)))) := this
        _ = C_e3 * (ξ * ξ⁻¹) * (1 + κ * liftEps c * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) * c⁻¹ *
              min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) := by ring
        _ = (C_e3 * c⁻¹) * ((1 + κ * liftEps c * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) *
              min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ)))) := by
            rw [mul_inv_cancel₀ hξ.ne', mul_one]; ring
        _ ≤ (C_e3 * c⁻¹) * (1 * L ^ (-(1 / 4 : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul h_m1 hmin_le h_min_nn zero_le_one) hc1_nn
        _ = C_e3 * c⁻¹ * L ^ (-(1 / 4 : ℝ)) := by ring
    have hLpL_nn : 0 ≤ L ^ p * L ^ (-(3 / 2 : ℝ)) := by positivity
    have hCe3_c : 0 ≤ C_e3 * c⁻¹ := mul_nonneg hCe3.le (inv_nonneg.mpr hc0.le)
    have hCe3_eq : C_e3 * c⁻¹ * (b_mid * Real.pi ^ 3 / (4 * C_e3) * (L ^ p * L ^ (-(3 / 2 : ℝ)))) =
        (b_mid / 4) * (L ^ p * (c⁻¹ * Real.pi ^ 3 * L ^ (-(3 / 2 : ℝ)))) := by
      have h1 : C_e3 * (b_mid * Real.pi ^ 3 / (4 * C_e3)) = b_mid * Real.pi ^ 3 / 4 := by
        field_simp [hCe3.ne']
      calc C_e3 * c⁻¹ * (b_mid * Real.pi ^ 3 / (4 * C_e3) * (L ^ p * L ^ (-(3 / 2 : ℝ))))
          = (C_e3 * (b_mid * Real.pi ^ 3 / (4 * C_e3))) * (c⁻¹ * (L ^ p * L ^ (-(3 / 2 : ℝ)))) := by ring
        _ = (b_mid * Real.pi ^ 3 / 4) * (c⁻¹ * (L ^ p * L ^ (-(3 / 2 : ℝ)))) := by rw [h1]
        _ = _ := by ring
    calc ξ * ‖iDual (D c) (κ * liftEps c) m c ξ‖
        ≤ C_e3 * c⁻¹ * (L ^ q₂ * (L ^ p * L ^ (-(3 / 2 : ℝ)))) := hbd_ξ.trans_eq (by rw [hL_eq])
      _ ≤ C_e3 * c⁻¹ * ((b_mid * Real.pi ^ 3 / (4 * C_e3)) * (L ^ p * L ^ (-(3 / 2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLq2 hLpL_nn) hCe3_c
      _ = (b_mid / 4) * (L ^ p * (c⁻¹ * Real.pi ^ 3 * L ^ (-(3 / 2 : ℝ)))) := hCe3_eq
      _ = (b_mid / 4) * (L ^ p * hbS c ξ ^ (-(3 / 2 : ℝ))) := by rw [hS_pow]
  obtain ⟨M_ref, hMref_def⟩ : ∃ M_ref : ℝ,
      M_ref = (ceK / ceCs) * windowSmooth (κ * liftEps c) m (S c) (-x_arg) := ⟨_, rfl⟩
  have hdiff_ξ : ‖(ξ : ℂ) * (iMain (S c) (κ * liftEps c) m c ξ + iDual (D c) (κ * liftEps c) m c ξ) -
      (M_ref : ℂ)‖ ≤ (3 / 4 : ℝ) * (b_mid * L ^ p * hbS c ξ ^ (-(3 / 2 : ℝ))) := by
    have heq : (ξ : ℂ) * (iMain (S c) (κ * liftEps c) m c ξ + iDual (D c) (κ * liftEps c) m c ξ) - (M_ref : ℂ) =
        ((ξ : ℂ) * iMain (S c) (κ * liftEps c) m c ξ - (M_ref : ℂ)) + (ξ : ℂ) * iDual (D c) (κ * liftEps c) m c ξ := by
      ring
    have hm1 : ‖(ξ : ℂ) * iMain (S c) (κ * liftEps c) m c ξ - (M_ref : ℂ)‖ ≤
        C_mt * (hbS c ξ ^ (-(3 / 2 : ℝ)) * L) + C_mt * c ^ (-(5 / 2 : ℝ)) := by
      have hcast : ((ceK : ℂ) / (ceCs : ℂ)) *
          ((windowSmooth (κ * liftEps c) m (S c) (-((c * liftEps c * edgeAlphaTilde L + liftEps c / 2) / ceCs)) : ℝ) : ℂ) = (M_ref : ℂ) := by
        rw [hMref_def, hxarg_def]; push_cast; rfl
      rw [← hcast]; exact hmain_mt.trans_eq (by ring)
    have hm2 : ‖(ξ : ℂ) * iDual (D c) (κ * liftEps c) m c ξ‖ = ξ * ‖iDual (D c) (κ * liftEps c) m c ξ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ]
    calc ‖(ξ : ℂ) * (iMain (S c) (κ * liftEps c) m c ξ + iDual (D c) (κ * liftEps c) m c ξ) - (M_ref : ℂ)‖
        ≤ ‖(ξ : ℂ) * iMain (S c) (κ * liftEps c) m c ξ - (M_ref : ℂ)‖ +
            ‖(ξ : ℂ) * iDual (D c) (κ * liftEps c) m c ξ‖ := by rw [heq]; exact norm_add_le _ _
      _ ≤ (C_mt * (hbS c ξ ^ (-(3 / 2 : ℝ)) * L) + C_mt * c ^ (-(5 / 2 : ℝ))) +
            (b_mid / 4) * (L ^ p * hbS c ξ ^ (-(3 / 2 : ℝ))) := by rw [hm2]; exact add_le_add hm1 hdual_err
      _ ≤ ((b_mid / 4) * (L ^ p * hbS c ξ ^ (-(3 / 2 : ℝ))) + (b_mid / 4) * (L ^ p * hbS c ξ ^ (-(3 / 2 : ℝ)))) +
            (b_mid / 4) * (L ^ p * hbS c ξ ^ (-(3 / 2 : ℝ))) := add_le_add (add_le_add hmain_err1 hmain_err2) le_rfl
      _ = (3 / 4 : ℝ) * (b_mid * L ^ p * hbS c ξ ^ (-(3 / 2 : ℝ))) := by ring
  have hre_ξ : 0 < ((ξ : ℂ) * (iMain (S c) (κ * liftEps c) m c ξ + iDual (D c) (κ * liftEps c) m c ξ)).re := by
    have hlt : ‖(ξ : ℂ) * (iMain (S c) (κ * liftEps c) m c ξ + iDual (D c) (κ * liftEps c) m c ξ) - (M_ref : ℂ)‖ < M_ref := by
      have hb_pos : 0 < b_mid * L ^ p * hbS c ξ ^ (-(3 / 2 : ℝ)) := by
        exact mul_pos (mul_pos hbmid (Real.rpow_pos_of_pos hL_pos _)) (Real.rpow_pos_of_pos (by linarith only [hS100]) _)
      rw [← hMref_def] at hfloor_val
      exact lt_of_le_of_lt hdiff_ξ (lt_of_lt_of_le (by linarith only [hb_pos]) hfloor_val)
    exact re_pos_of_norm_lt hlt
  rw [Complex.re_ofReal_mul] at hre_ξ
  exact pos_of_mul_pos_right hre_ξ hξ.le

private lemma ce_post_edge_far_L
    {m : ℕ} (hm : 4 ≤ m) {L_F : ℝ} (hLF : 0 < L_F)
    {S : ℝ → ℝ → ℝ}
    (hfarS : ∃ b_F > 0, ∀ {κ : ℝ}, 0 < κ → ∃ C_err > 0, ∃ c₀ ≥ (2 : ℝ),
      ∀ {c ξ : ℝ}, c₀ ≤ c → 0 < ξ → L_F ≤ Real.log (Real.pi ^ 2 * ξ) →
        (c * ξ) * (iMain (S c) (κ * liftEps c) m c ξ).re ≥
          (b_F - C_err * c ^ (-(1 / 6 : ℝ))) * (1 + Real.log (Real.pi ^ 2 * ξ)) ^ (-(3 / 2 : ℝ)))
    {CD : ℝ} (hCD : 0 ≤ CD) :
    ∃ κ₀ ≥ (1 : ℝ), ∀ {κ : ℝ}, κ₀ ≤ κ → ∀ {D : ℝ → ℝ → ℝ},
      (∀ {c : ℝ}, 2 ≤ c → DifferentiableOn ℂ (airyTwistedLaplaceC (D c)) {y : ℂ | 0 < y.re}) →
      (∀ {c : ℝ} {w : ℂ}, 2 ≤ c → 0 ≤ w.re →
        ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤ CD * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) →
      ∃ c₀ ≥ (2 : ℝ), ∀ {c ξ : ℝ}, c₀ ≤ c → 0 < ξ →
        L_F ≤ Real.log (Real.pi ^ 2 * ξ) →
        0 < (iMain (S c) (κ * liftEps c) m c ξ + iDual (D c) (κ * liftEps c) m c ξ).re := by
  obtain ⟨b_F, hbF, hfar⟩ := hfarS
  obtain ⟨C_e3, hCe3, he3⟩ := iDual_bound_e3 (by omega : 3 ≤ m) hCD
  set C_LF : ℝ := C_e3 * 2 ^ (3 / 2 : ℝ) * max 1 (L_F ^ (-(1 / 4 : ℝ)))
  have hCLF : 0 < C_LF := by positivity
  set κ₀ : ℝ := max 1 ((4 * C_LF / b_F) ^ (1 / (m : ℝ)) + 1)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  refine ⟨κ₀, le_max_left _ _, fun {κ} hκ {D} hdiffD hbdD => ?_⟩
  obtain ⟨C_err, hCerr, c_f, hcf, hmain_f⟩ :=
    hfar (by linarith [le_max_left (1 : ℝ) ((4 * C_LF / b_F) ^ (1 / (m : ℝ)) + 1), hκ] : 0 < κ)
  set c_err6 : ℝ := (4 * C_err / b_F) ^ 6
  set c_S1 : ℝ := (Real.pi ^ 2 / L_F) ^ (3 / 2 : ℝ)
  set c₀ : ℝ := max (max c_f c_S1) (max ((κ / 2) ^ 3 + 1) (c_err6 + 1))
  refine ⟨c₀, hcf.trans ((le_max_left _ _).trans (le_max_left _ _)), fun {c ξ} hc hξ hL => ?_⟩
  have hcf_c : c_f ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hc)
  have hcS1 : c_S1 ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
  have hc2 : 2 ≤ c := hcf.trans hcf_c
  have hc0 : 0 < c := by linarith
  have hκ1 : 1 ≤ κ := (le_max_left _ _).trans hκ
  have hδ_pos : 0 < κ * liftEps c := by have := liftEps_pos hc0; positivity
  have hδ_le2 : κ * liftEps c ≤ 2 := by
    have hκc : (κ / 2) ^ 3 ≤ c := by
      linarith [le_max_left ((κ / 2) ^ 3 + 1) (c_err6 + 1),
        le_max_right (max c_f c_S1) (max ((κ / 2) ^ 3 + 1) (c_err6 + 1))]
    have hκr : κ / 2 ≤ c ^ (1 / 3 : ℝ) := by
      have h1 := Real.rpow_le_rpow (by positivity) hκc (by norm_num : (0 : ℝ) ≤ 1 / 3)
      have h_eq : ((κ / 2) ^ (3 : ℕ) : ℝ) ^ (1 / 3 : ℝ) = κ / 2 := by
        rw [← Real.rpow_natCast (κ / 2) 3, ← Real.rpow_mul (by positivity),
          show ((3 : ℕ) : ℝ) * (1 / 3 : ℝ) = 1 by norm_num, Real.rpow_one]
      exact h_eq.symm.trans_le h1
    have hεc : liftEps c = (c ^ (1 / 3 : ℝ))⁻¹ := by
      unfold liftEps; rw [Real.rpow_neg hc0.le]
    rw [hεc, ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hc0 _)]
    linarith [(div_le_iff₀ (two_pos : (0 : ℝ) < 2)).mp hκr]
  set L : ℝ := Real.log (Real.pi ^ 2 * ξ)
  have hL_pos : 0 < L := hLF.trans_le hL
  have hS1 : 1 ≤ hbS c ξ := by
    have hc23 : Real.pi ^ 2 / L_F ≤ c ^ (2 / 3 : ℝ) := by
      have h1 := Real.rpow_le_rpow (by positivity) hcS1 (by norm_num : (0 : ℝ) ≤ 2 / 3)
      have h2 : c_S1 ^ (2 / 3 : ℝ) = Real.pi ^ 2 / L_F := by
        dsimp [c_S1]; rw [← Real.rpow_mul (by positivity), show (3 / 2 : ℝ) * (2 / 3 : ℝ) = 1 by norm_num, Real.rpow_one]
      exact h2.symm.trans_le h1
    have hε2_eq : liftEps c ^ 2 = (c ^ (2 / 3 : ℝ))⁻¹ := by
      unfold liftEps; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le, show (-(1 / 3 : ℝ) * ((2 : ℕ) : ℝ)) = -(2 / 3 : ℝ) by norm_num,
        Real.rpow_neg hc0.le]
    have hpi0 : 0 < Real.pi := Real.pi_pos
    have hε0 : 0 < liftEps c := liftEps_pos hc0
    unfold hbS
    rw [le_div_iff₀ (by positivity)]
    calc 1 * (Real.pi ^ 2 * liftEps c ^ 2) = Real.pi ^ 2 * (c ^ (2 / 3 : ℝ))⁻¹ := by rw [hε2_eq, one_mul]
      _ ≤ Real.pi ^ 2 * (Real.pi ^ 2 / L_F)⁻¹ := by gcongr
      _ = L_F := by field_simp [hpi0.ne', hLF.ne']
      _ ≤ L := hL
  have hmain_lb := hmain_f hcf_c hξ hL
  have hc_ge_err6 : c_err6 ≤ c := by
    linarith [le_max_right ((κ / 2) ^ 3 + 1) (c_err6 + 1),
      le_max_right (max c_f c_S1) (max ((κ / 2) ^ 3 + 1) (c_err6 + 1))]
  have hErr_le : C_err * c ^ (-(1 / 6 : ℝ)) ≤ b_F / 4 := by
    have h1 := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < c_err6) hc_ge_err6 (by norm_num : -(1 / 6 : ℝ) ≤ 0)
    have h2 : c_err6 ^ (-(1 / 6 : ℝ)) = b_F / (4 * C_err) := by
      dsimp [c_err6]
      rw [← Real.rpow_natCast _ 6, ← Real.rpow_mul (by positivity), show ((6 : ℕ) : ℝ) * -(1 / 6 : ℝ) = -1 by norm_num,
        Real.rpow_neg_one, inv_div]
    rw [h2] at h1
    calc C_err * c ^ (-(1 / 6 : ℝ)) ≤ C_err * (b_F / (4 * C_err)) := by gcongr
      _ = b_F / 4 := by field_simp [hCerr.ne']
  have hκ_pow : (1 + κ * liftEps c * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) ≤ b_F / (4 * C_LF) := by
    have hεc_prod : liftEps c * c ^ (1 / 3 : ℝ) = 1 := by
      unfold liftEps; rw [Real.rpow_neg hc0.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hc0 _).ne']
    rw [mul_assoc, hεc_prod, mul_one]
    have hκ_ge : (4 * C_LF / b_F) ^ (1 / (m : ℝ)) ≤ 1 + κ := by
      linarith [le_max_right (1 : ℝ) ((4 * C_LF / b_F) ^ (1 / (m : ℝ)) + 1)]
    have h1 := Real.rpow_le_rpow_of_nonpos (by positivity) hκ_ge (by linarith : -(m : ℝ) ≤ 0)
    have h2 : ((4 * C_LF / b_F) ^ (1 / (m : ℝ))) ^ (-(m : ℝ)) = b_F / (4 * C_LF) := by
      rw [← Real.rpow_mul (by positivity), show (1 / (m : ℝ)) * -(m : ℝ) = -1 by field_simp [hm0.ne'],
        Real.rpow_neg_one, inv_div]
    exact h1.trans_eq h2
  have hmin_bound : min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) ≤
      2 ^ (3 / 2 : ℝ) * max 1 (L_F ^ (-(1 / 4 : ℝ))) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
    by_cases hL1 : 1 ≤ L
    · have h1L : 1 + L ≤ 2 * L := by linarith
      have h1L' : (2 * L) ^ (-(3 / 2 : ℝ)) ≤ (1 + L) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1L (by norm_num)
      rw [Real.mul_rpow (by norm_num) hL_pos.le] at h1L'
      have hL32 : L ^ (-(3 / 2 : ℝ)) ≤ 2 ^ (3 / 2 : ℝ) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
        have hmul := mul_le_mul_of_nonneg_left h1L' (by positivity : 0 ≤ (2 : ℝ) ^ (3 / 2 : ℝ))
        have h2pow : (2 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (-(3 / 2 : ℝ)) = 1 := by
          rw [← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero]
        calc L ^ (-(3 / 2 : ℝ)) = ((2 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (-(3 / 2 : ℝ))) * L ^ (-(3 / 2 : ℝ)) := by
              rw [h2pow, one_mul]
          _ = (2 : ℝ) ^ (3 / 2 : ℝ) * ((2 : ℝ) ^ (-(3 / 2 : ℝ)) * L ^ (-(3 / 2 : ℝ))) := by ring
          _ ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * (1 + L) ^ (-(3 / 2 : ℝ)) := hmul
      calc min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ)))
          ≤ L ^ (-(3 / 2 : ℝ)) := min_le_right _ _
        _ ≤ 2 ^ (3 / 2 : ℝ) * (1 + L) ^ (-(3 / 2 : ℝ)) := hL32
        _ ≤ 2 ^ (3 / 2 : ℝ) * max 1 (L_F ^ (-(1 / 4 : ℝ))) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
            have : (1 : ℝ) ≤ max 1 (L_F ^ (-(1 / 4 : ℝ))) := le_max_left _ _
            have hnn : 0 ≤ (1 + L) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
            nlinarith [mul_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ (3 / 2 : ℝ)) hnn]
    · have hL_lt : L ≤ 1 := (not_le.mp hL1).le
      have h1L : 1 + L ≤ 2 := by linarith
      have h2_le : 1 ≤ 2 ^ (3 / 2 : ℝ) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
        have h1 := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 1 + L) h1L (by norm_num : -(3 / 2 : ℝ) ≤ 0)
        have hmul := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ (2 : ℝ) ^ (3 / 2 : ℝ))
        have h2pow : (2 : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ (-(3 / 2 : ℝ)) = 1 := by
          rw [← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero]
        linarith [h2pow]
      have hL14 : L ^ (-(1 / 4 : ℝ)) ≤ L_F ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hLF hL (by norm_num)
      calc min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ)))
          ≤ L ^ (-(1 / 4 : ℝ)) := min_le_left _ _
        _ ≤ max 1 (L_F ^ (-(1 / 4 : ℝ))) := hL14.trans (le_max_right _ _)
        _ = max 1 (L_F ^ (-(1 / 4 : ℝ))) * 1 := (mul_one _).symm
        _ ≤ max 1 (L_F ^ (-(1 / 4 : ℝ))) * (2 ^ (3 / 2 : ℝ) * (1 + L) ^ (-(3 / 2 : ℝ))) := by gcongr
        _ = _ := by ring
  have hdual_le : (c * ξ) * ‖iDual (D c) (κ * liftEps c) m c ξ‖ ≤ (b_F / 4) * (1 + L) ^ (-(3 / 2 : ℝ)) := by
    have he := he3 (hdiffD hc2) (hbdD hc2) ⟨hδ_pos, hδ_le2⟩ hc2 hξ hS1
    calc (c * ξ) * ‖iDual (D c) (κ * liftEps c) m c ξ‖
        ≤ (c * ξ) * (C_e3 * ξ⁻¹ * (1 + κ * liftEps c * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) * c⁻¹ *
            min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ)))) := by gcongr
      _ = C_e3 * ((c * c⁻¹) * (ξ * ξ⁻¹)) * (1 + κ * liftEps c * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) *
            min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) := by ring
      _ = C_e3 * (1 + κ * liftEps c * c ^ (1 / 3 : ℝ)) ^ (-(m : ℝ)) *
            min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) := by
          rw [mul_inv_cancel₀ hc0.ne', mul_inv_cancel₀ hξ.ne', mul_one, mul_one]
      _ ≤ C_e3 * (b_F / (4 * C_LF)) * (2 ^ (3 / 2 : ℝ) * max 1 (L_F ^ (-(1 / 4 : ℝ))) * (1 + L) ^ (-(3 / 2 : ℝ))) := by
          gcongr
      _ = (C_LF * (b_F / (4 * C_LF))) * (1 + L) ^ (-(3 / 2 : ℝ)) := by dsimp [C_LF]; ring
      _ = (b_F / 4) * (1 + L) ^ (-(3 / 2 : ℝ)) := by field_simp [hCLF.ne']
  have hre_dual : -((c * ξ) * ‖iDual (D c) (κ * liftEps c) m c ξ‖) ≤ (c * ξ) * (iDual (D c) (κ * liftEps c) m c ξ).re := by
    have h1 := Complex.abs_re_le_norm (iDual (D c) (κ * liftEps c) m c ξ)
    have h2 : -‖iDual (D c) (κ * liftEps c) m c ξ‖ ≤ (iDual (D c) (κ * liftEps c) m c ξ).re :=
      by linarith [neg_abs_le (iDual (D c) (κ * liftEps c) m c ξ).re]
    have hmul := mul_le_mul_of_nonneg_left h2 (mul_pos hc0 hξ).le
    linarith
  have htot : (b_F / 2) * (1 + L) ^ (-(3 / 2 : ℝ)) ≤
      (c * ξ) * (iMain (S c) (κ * liftEps c) m c ξ + iDual (D c) (κ * liftEps c) m c ξ).re := by
    rw [Complex.add_re, mul_add]
    have hmain_pos : (3 / 4 : ℝ) * b_F * (1 + L) ^ (-(3 / 2 : ℝ)) ≤
        (c * ξ) * (iMain (S c) (κ * liftEps c) m c ξ).re := by
      have hL_nn : 0 ≤ (1 + L) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
      calc (3 / 4 : ℝ) * b_F * (1 + L) ^ (-(3 / 2 : ℝ))
          = (b_F - b_F / 4) * (1 + L) ^ (-(3 / 2 : ℝ)) := by ring
        _ ≤ (b_F - C_err * c ^ (-(1 / 6 : ℝ))) * (1 + L) ^ (-(3 / 2 : ℝ)) := by gcongr
        _ ≤ (c * ξ) * (iMain (S c) (κ * liftEps c) m c ξ).re := hmain_lb
    linarith
  have hpos_lhs : 0 < (b_F / 2) * (1 + L) ^ (-(3 / 2 : ℝ)) := by positivity
  exact pos_of_mul_pos_right (lt_of_lt_of_le hpos_lhs htot) (mul_pos hc0 hξ).le

private lemma ce_post_edge_window
    {m : ℕ} (hm : 4 ≤ m) {κ U S_star : ℝ} (hκ : 1 ≤ κ) (hU : 0 ≤ U) (_hSstar : 0 ≤ S_star)
    {S D : ℝ → ℝ → ℝ}
    (hU2S : ∀ {c : ℝ}, 2 ≤ c → HasU2 (S c))
    (hcontS : ∀ {c : ℝ}, 2 ≤ c → Continuous (S c))
    {CS CD : ℝ} (hCS : 0 ≤ CS) (hCD : 0 ≤ CD)
    (hbdS : ∀ {c : ℝ} {w : ℂ}, 2 ≤ c → 0 ≤ w.re →
      ‖airyTwistedLaplaceC (S c) ((ceCs : ℂ) * w)‖ ≤ CS * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    (hbdD : ∀ {c : ℝ} {w : ℂ}, 2 ≤ c → 0 ≤ w.re →
      ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤ CD * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    (hcompS : ∀ {A B : ℝ}, 0 ≤ A → A ≤ B → ∃ b_comp > 0, ∀ {c u : ℝ}, 2 ≤ c →
      u ∈ Icc (-A) B → b_comp * liftEps c ≤ S c u) :
    ∃ c₃ ≥ (2 : ℝ), ∀ {c ξ : ℝ}, c₃ ≤ c → 0 < ξ → -U ≤ hbS c ξ → hbS c ξ ≤ S_star →
      0 < (iMain (S c) (κ * liftEps c) m c ξ + iDual (D c) (κ * liftEps c) m c ξ).re := by
  set Sw : ℝ := max U S_star
  have hSw : 0 ≤ Sw := le_max_of_le_left hU
  set CW : ℝ := CS * 2 ^ (5 / 2 : ℝ) + 1
  set CD' : ℝ := CD + 1
  obtain ⟨C_wt, hCwt, hwt⟩ := window_translation m (by omega : 1 ≤ m) Sw CW CD' (by positivity) (by positivity)
  set A_c : ℝ := ceBeta1 * Sw + 1
  set B_c : ℝ := ceBeta1 * Sw + κ
  have hβ0 : 0 < ceBeta1 := ceBeta1_pos
  have hcs0 : 0 < ceCs := ceCs_pos
  have hk0 : 0 < ceK := ceK_pos
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hAc0 : 0 ≤ A_c := by positivity
  have hAB : A_c ≤ B_c := by dsimp [A_c, B_c]; linarith
  obtain ⟨b_comp, hbcomp, hcomp⟩ := hcompS hAc0 hAB
  set c_wt : ℝ := (4 * C_wt * Real.pi ^ 2 / (ceK * ceBeta1 * b_comp)) ^ 6
  set c₃ : ℝ := max 32768 (c_wt + 1)
  refine ⟨c₃, by linarith [le_max_left 32768 (c_wt + 1)], fun {c ξ} hc hξ hlo hhi => ?_⟩
  have hc32k : 32768 ≤ c := (le_max_left _ _).trans hc
  have hc2 : 2 ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  have hε1 : liftEps c ≤ 1 := liftEps_le_one (by linarith)
  have hδ0 : 0 < κ * liftEps c := by positivity
  have hS_bd : |hbS c ξ| ≤ Sw := abs_le.mpr ⟨by linarith [le_max_left U S_star], hhi.trans (le_max_right _ _)⟩
  have hW_S : ∀ {δ₀ : ℝ} {w : ℂ}, 0 ≤ δ₀ → 0 ≤ w.re →
      ‖liftSymbol (S c) δ₀ m w‖ ≤ CW * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := fun {δ₀ w} hδ hw =>
    liftSymbol_norm_of_rhp_unif hCS (hbdS hc2) hδ m hw
  have hW_D : ∀ {w : ℂ}, 0 ≤ w.re →
      ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤ CD' * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := fun {w} hw =>
    (hbdD hc2 hw).trans (by
      have : 0 ≤ ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
      dsimp [CD']; nlinarith)
  have htrans := hwt (hU2S hc2) (hcontS hc2) hW_S hW_D hδ0.le hc32k hξ hS_bd
  set y_arg : ℝ := -(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs)
  have hwin : b_comp * liftEps c ≤ windowSmooth (κ * liftEps c) m (S c) y_arg := by
    refine windowSmooth_ge (hcontS hc2) hδ0 (by omega) y_arg _ fun t ht => ?_
    refine hcomp hc2 ⟨?_, ?_⟩
    · have hS_hi : hbS c ξ ≤ Sw := (abs_le.mp hS_bd).2
      have hβ_hi : -(ceBeta1 * Sw) ≤ -(ceBeta1 * hbS c ξ) := by
        have := mul_le_mul_of_nonneg_left hS_hi hβ0.le; linarith
      have : liftEps c / (2 * ceCs) ≤ 1 := by
        have hcs1 : 1 ≤ ceCs := convEdge_one_le_ceCs
        calc liftEps c / (2 * ceCs) ≤ 1 / (2 * 1) := by gcongr
          _ ≤ 1 := by norm_num
      dsimp [A_c, y_arg]; linarith [ht.1]
    · have hS_lo : -Sw ≤ hbS c ξ := (abs_le.mp hS_bd).1
      have hβ_lo : -(ceBeta1 * hbS c ξ) ≤ ceBeta1 * Sw := by
        have := mul_le_mul_of_nonneg_left hS_lo hβ0.le; linarith
      have : 0 ≤ liftEps c / (2 * ceCs) := by positivity
      have ht_κ : t ≤ κ := ht.2.trans (mul_le_of_le_one_right (by linarith) hε1)
      dsimp [B_c, y_arg]; linarith [ht.1]
  set M_win : ℝ := ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * windowSmooth (κ * liftEps c) m (S c) y_arg
  have hM_floor : (ceK * ceBeta1 * b_comp / Real.pi ^ 2) * ξ⁻¹ * liftEps c ≤ M_win := by
    dsimp [M_win]
    calc (ceK * ceBeta1 * b_comp / Real.pi ^ 2) * ξ⁻¹ * liftEps c
        = (ceK * ceBeta1 / (Real.pi ^ 2 * ξ)) * (b_comp * liftEps c) := by ring
      _ ≤ ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * windowSmooth (κ * liftEps c) m (S c) y_arg := by
          gcongr
  have hc_ge_wt : c_wt ≤ c := by linarith [le_max_right 32768 (c_wt + 1)]
  have hc16 : c ^ (-(1 / 6 : ℝ)) ≤ (ceK * ceBeta1 * b_comp) / (4 * C_wt * Real.pi ^ 2) := by
    have hcwt_pos : 0 < c_wt := by positivity
    have h1 := Real.rpow_le_rpow_of_nonpos hcwt_pos hc_ge_wt (by norm_num : -(1 / 6 : ℝ) ≤ 0)
    have h2 : c_wt ^ (-(1 / 6 : ℝ)) = (ceK * ceBeta1 * b_comp) / (4 * C_wt * Real.pi ^ 2) := by
      dsimp [c_wt]
      rw [← Real.rpow_natCast _ 6, ← Real.rpow_mul (by positivity), show ((6 : ℕ) : ℝ) * -(1 / 6 : ℝ) = -1 by norm_num,
        Real.rpow_neg_one, inv_div]
    exact h1.trans_eq h2
  have hε_le_c16 : liftEps c ≤ c ^ (-(1 / 6 : ℝ)) := by
    unfold liftEps; exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hc12_eq : c ^ (-(1 / 2 : ℝ)) = c ^ (-(1 / 6 : ℝ)) * liftEps c := by
    unfold liftEps; rw [← Real.rpow_add hc0]; norm_num
  have hκm_le1 : ((1 + κ * liftEps c * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ ≤ 1 := by
    refine inv_le_one_of_one_le₀ (one_le_pow₀ ?_)
    nlinarith [mul_nonneg hδ0.le (Real.rpow_nonneg hc0.le (1 / 3 : ℝ))]
  have herr_le : C_wt * ξ⁻¹ * (liftEps c ^ 2 + ((1 + κ * liftEps c * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ * c ^ (-(1 / 2 : ℝ))) <
      M_win := by
    have hpar : liftEps c ^ 2 + ((1 + κ * liftEps c * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ * c ^ (-(1 / 2 : ℝ)) ≤
        2 * c ^ (-(1 / 6 : ℝ)) * liftEps c := by
      have hκ_nn : 0 ≤ ((1 + κ * liftEps c * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ := by positivity
      have hc12_nn : 0 ≤ c ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hc0.le _
      calc liftEps c ^ 2 + ((1 + κ * liftEps c * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ * c ^ (-(1 / 2 : ℝ))
          ≤ liftEps c * liftEps c + c ^ (-(1 / 6 : ℝ)) * liftEps c := by
            rw [_root_.sq, ← hc12_eq]
            exact add_le_add le_rfl ((mul_le_mul hκm_le1 le_rfl (by positivity) zero_le_one).trans_eq (one_mul _))
        _ ≤ c ^ (-(1 / 6 : ℝ)) * liftEps c + c ^ (-(1 / 6 : ℝ)) * liftEps c := by gcongr
        _ = 2 * c ^ (-(1 / 6 : ℝ)) * liftEps c := by ring
    have h_half : C_wt * ξ⁻¹ * (2 * c ^ (-(1 / 6 : ℝ)) * liftEps c) ≤
        ((ceK * ceBeta1 * b_comp / Real.pi ^ 2) / 2) * ξ⁻¹ * liftEps c := by
      calc C_wt * ξ⁻¹ * (2 * c ^ (-(1 / 6 : ℝ)) * liftEps c)
          = (2 * C_wt * c ^ (-(1 / 6 : ℝ))) * ξ⁻¹ * liftEps c := by ring
        _ ≤ (2 * C_wt * ((ceK * ceBeta1 * b_comp) / (4 * C_wt * Real.pi ^ 2))) * ξ⁻¹ * liftEps c := by
            gcongr
        _ = ((ceK * ceBeta1 * b_comp / Real.pi ^ 2) / 2) * ξ⁻¹ * liftEps c := by
            field_simp [hCwt.ne', hpi0.ne']; ring
    have hpos_half : 0 < ((ceK * ceBeta1 * b_comp / Real.pi ^ 2) / 2) * ξ⁻¹ * liftEps c := by positivity
    calc C_wt * ξ⁻¹ * (liftEps c ^ 2 + ((1 + κ * liftEps c * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ * c ^ (-(1 / 2 : ℝ)))
        ≤ C_wt * ξ⁻¹ * (2 * c ^ (-(1 / 6 : ℝ)) * liftEps c) := by gcongr
      _ ≤ ((ceK * ceBeta1 * b_comp / Real.pi ^ 2) / 2) * ξ⁻¹ * liftEps c := h_half
      _ < (ceK * ceBeta1 * b_comp / Real.pi ^ 2) * ξ⁻¹ * liftEps c := by linarith
      _ ≤ M_win := hM_floor
  exact re_pos_of_norm_lt (lt_of_le_of_lt htrans herr_le)

/-- **Post-edge Fourier sign (`thm:ce-post-edge`), uniform over dual families `D`**:
version of `ce_post_edge` in which the threshold `κ₀ ≥ 1` depends only on `CD` and not on the choice of `D`. -/
theorem ce_post_edge_unif
    {p lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hlam : 0 < lam)
    {m : ℕ} (hm : 4 ≤ m)
    {S : ℝ → ℝ → ℝ}
    (hU2S : ∀ {c : ℝ}, 2 ≤ c → HasU2 (S c))
    (hcontS : ∀ {c : ℝ}, 2 ≤ c → Continuous (S c))
    (hgt1S : ∃ AS : ℝ, 0 ≤ AS ∧ ∀ {c δ₀ : ℝ}, 2 ≤ c → δ₀ ∈ Icc (0 : ℝ) 2 →
      Gt1Bounds AS (liftW (S c) δ₀ m))
    {CS : ℝ} (hCS : 0 ≤ CS)
    (hbdS : ∀ {c : ℝ} {w : ℂ}, 2 ≤ c → 0 ≤ w.re →
      ‖airyTwistedLaplaceC (S c) ((ceCs : ℂ) * w)‖ ≤ CS * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    (hcompS : ∀ {A B : ℝ}, 0 ≤ A → A ≤ B → ∃ b_comp > 0, ∀ {c u : ℝ}, 2 ≤ c →
      u ∈ Icc (-A) B → b_comp * liftEps c ≤ S c u)
    (hrayS : ∃ b_ray > 0, ∃ x₁ ≥ (1 : ℝ), ∀ {c x : ℝ}, 2 ≤ c → x₁ ≤ x →
      b_ray * (min 1 (lam * liftEps c ^ 2 * x)) ^ p * x ^ (-(3 / 2 : ℝ)) ≤ S c (-x))
    (hfarS : ∀ {L_F : ℝ}, 0 < L_F → ∃ b_F > 0, ∀ {κ : ℝ}, 0 < κ → ∃ C_err > 0, ∃ c₀ ≥ (2 : ℝ),
      ∀ {c ξ : ℝ}, c₀ ≤ c → 0 < ξ → L_F ≤ Real.log (Real.pi ^ 2 * ξ) →
        (c * ξ) * (iMain (S c) (κ * liftEps c) m c ξ).re ≥
          (b_F - C_err * c ^ (-(1 / 6 : ℝ))) * (1 + Real.log (Real.pi ^ 2 * ξ)) ^ (-(3 / 2 : ℝ)))
    {CD : ℝ} (hCD : 0 ≤ CD) :
    ∃ κ₀ : ℝ, 1 ≤ κ₀ ∧ ∀ {κ : ℝ}, κ₀ ≤ κ → ∀ {U : ℝ}, 0 ≤ U → ∀ {D : ℝ → ℝ → ℝ},
      (∀ {c : ℝ}, 2 ≤ c → DifferentiableOn ℂ (airyTwistedLaplaceC (D c)) {y : ℂ | 0 < y.re}) →
      (∀ {c : ℝ} {w : ℂ}, 2 ≤ c → 0 ≤ w.re →
        ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤ CD * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) →
      ∃ c₀ ≥ (2 : ℝ),
        ∀ {c ξ : ℝ}, c₀ ≤ c → 0 < ξ → -U ≤ hbS c ξ →
          0 < (iMain (S c) (κ * liftEps c) m c ξ + iDual (D c) (κ * liftEps c) m c ξ).re := by
  obtain ⟨L_F, S_star, hLF_pos, _, hSstar, hsmall⟩ :=
    ce_post_edge_small_L hp hp1 hlam hm hU2S hcontS hgt1S hrayS hCD
  obtain ⟨κ₀, hκ₀, hfar⟩ := ce_post_edge_far_L hm hLF_pos (hfarS hLF_pos) hCD
  refine ⟨κ₀, hκ₀, fun {κ} hκ {U} hU {D} hdiffD hbdD => ?_⟩
  have hκ1 : 1 ≤ κ := hκ₀.trans hκ
  obtain ⟨c₁, hc₁, h1⟩ := hsmall hκ1 hdiffD hbdD
  obtain ⟨c₂, hc₂, h2⟩ := hfar hκ hdiffD hbdD
  obtain ⟨c₃, hc₃, h3⟩ :=
    ce_post_edge_window hm hκ1 hU (by linarith : 0 ≤ S_star) hU2S hcontS hCS hCD hbdS hbdD hcompS
  refine ⟨max c₁ (max c₂ c₃), hc₁.trans (le_max_left _ _), fun {c ξ} hc hξ hUlo => ?_⟩
  have hc_1 : c₁ ≤ c := (le_max_left _ _).trans hc
  have hc_2 : c₂ ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hc_3 : c₃ ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  rcases le_or_gt (hbS c ξ) S_star with hS_le | hS_gt
  · exact h3 hc_3 hξ hUlo hS_le
  · rcases le_or_gt (Real.log (Real.pi ^ 2 * ξ)) L_F with hL_le | hL_gt
    · exact h1 hc_1 hξ hS_gt.le hL_le
    · exact h2 hc_2 hξ hL_gt.le

theorem ce_post_edge
    {p lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hlam : 0 < lam)
    {m : ℕ} (hm : 4 ≤ m)
    {S D : ℝ → ℝ → ℝ}
    (hU2S : ∀ {c : ℝ}, 2 ≤ c → HasU2 (S c))
    (hcontS : ∀ {c : ℝ}, 2 ≤ c → Continuous (S c))
    (hgt1S : ∃ AS : ℝ, 0 ≤ AS ∧ ∀ {c δ₀ : ℝ}, 2 ≤ c → δ₀ ∈ Icc (0 : ℝ) 2 →
      Gt1Bounds AS (liftW (S c) δ₀ m))
    {CS : ℝ} (hCS : 0 ≤ CS)
    (hbdS : ∀ {c : ℝ} {w : ℂ}, 2 ≤ c → 0 ≤ w.re →
      ‖airyTwistedLaplaceC (S c) ((ceCs : ℂ) * w)‖ ≤ CS * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    (hcompS : ∀ {A B : ℝ}, 0 ≤ A → A ≤ B → ∃ b_comp > 0, ∀ {c u : ℝ}, 2 ≤ c →
      u ∈ Icc (-A) B → b_comp * liftEps c ≤ S c u)
    (hrayS : ∃ b_ray > 0, ∃ x₁ ≥ (1 : ℝ), ∀ {c x : ℝ}, 2 ≤ c → x₁ ≤ x →
      b_ray * (min 1 (lam * liftEps c ^ 2 * x)) ^ p * x ^ (-(3 / 2 : ℝ)) ≤ S c (-x))
    (hfarS : ∀ {L_F : ℝ}, 0 < L_F → ∃ b_F > 0, ∀ {κ : ℝ}, 0 < κ → ∃ C_err > 0, ∃ c₀ ≥ (2 : ℝ),
      ∀ {c ξ : ℝ}, c₀ ≤ c → 0 < ξ → L_F ≤ Real.log (Real.pi ^ 2 * ξ) →
        (c * ξ) * (iMain (S c) (κ * liftEps c) m c ξ).re ≥
          (b_F - C_err * c ^ (-(1 / 6 : ℝ))) * (1 + Real.log (Real.pi ^ 2 * ξ)) ^ (-(3 / 2 : ℝ)))
    {CD : ℝ} (hCD : 0 ≤ CD)
    (hdiffD : ∀ {c : ℝ}, 2 ≤ c → DifferentiableOn ℂ (airyTwistedLaplaceC (D c)) {y : ℂ | 0 < y.re})
    (hbdD : ∀ {c : ℝ} {w : ℂ}, 2 ≤ c → 0 ≤ w.re →
      ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤ CD * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) :
    ∃ κ₀ : ℝ, 1 ≤ κ₀ ∧ ∀ {κ : ℝ}, κ₀ ≤ κ → ∀ {U : ℝ}, 0 ≤ U → ∃ c₀ ≥ (2 : ℝ),
      ∀ {c ξ : ℝ}, c₀ ≤ c → 0 < ξ → -U ≤ hbS c ξ →
        0 < (iMain (S c) (κ * liftEps c) m c ξ + iDual (D c) (κ * liftEps c) m c ξ).re := by
  obtain ⟨κ₀, hκ₀, h⟩ :=
    ce_post_edge_unif hp hp1 hlam hm hU2S hcontS hgt1S hCS hbdS hcompS hrayS hfarS hCD
  exact ⟨κ₀, hκ₀, fun {κ} hκ {U} hU => h hκ hU (fun {c} => hdiffD) (fun {c w} => hbdD)⟩

/-- **Post-edge Fourier sign for `convSourceFamily`**, uniform over all dual families `D`
sharing the right-half-plane bound `CD`. -/
theorem ce_post_edge_convSource_unif
    {p γ θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 < γ) (hθ : 0 < θ) (hlam : 0 < lam)
    {m : ℕ} (hm : 4 ≤ m)
    {CD : ℝ} (hCD : 0 ≤ CD) :
    ∃ κ₀ : ℝ, 1 ≤ κ₀ ∧ ∀ {κ : ℝ}, κ₀ ≤ κ → ∀ {U : ℝ}, 0 ≤ U → ∀ {D : ℝ → ℝ → ℝ},
      (∀ {c : ℝ}, 2 ≤ c → DifferentiableOn ℂ (airyTwistedLaplaceC (D c)) {y : ℂ | 0 < y.re}) →
      (∀ {c : ℝ} {w : ℂ}, 2 ≤ c → 0 ≤ w.re →
        ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤ CD * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) →
      ∃ c₀ ≥ (2 : ℝ),
        ∀ {c ξ : ℝ}, c₀ ≤ c → 0 < ξ → -U ≤ hbS c ξ →
          0 < (iMain (convSourceFamily p γ θ lam c) (κ * liftEps c) m c ξ +
            iDual (D c) (κ * liftEps c) m c ξ).re := by
  have hU2S : ∀ {c : ℝ}, 2 ≤ c → HasU2 (convSourceFamily p γ θ lam c) := fun {c} hc =>
    hasU2_convSource hp hp1 (by have := liftEps_pos (show 0 < c by linarith); positivity)
  have hcontS : ∀ {c : ℝ}, 2 ≤ c → Continuous (convSourceFamily p γ θ lam c) := fun {c} hc => by
    have hc0 : 0 < c := by linarith
    have hε0 : 0 < liftEps c := liftEps_pos hc0
    have hh : 0 < lam * liftEps c ^ 2 := by positivity
    have hw_int : IntegrableOn (convWc p γ θ (liftEps c) (lam * liftEps c ^ 2)) (Ioi 0) :=
      convWc_integrableOn hp hp1 hh
    obtain ⟨Cg, hCg, hG_poly⟩ := convG1_le_poly
    have hG_bd : ∀ z : ℝ, ‖ceG1 (airyZero 1) z‖ ≤ Cg := fun z => by
      rw [Real.norm_of_nonneg (convG1_nonneg z)]
      exact (hG_poly z).trans (mul_le_of_le_one_right hCg.le
        (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg z]) (by norm_num)))
    refine continuous_of_dominated (bound := fun y => ‖convWc p γ θ (liftEps c) (lam * liftEps c ^ 2) y‖ * Cg) ?_ ?_ (hw_int.norm.mul_const Cg) ?_
    · intro u
      exact hw_int.aestronglyMeasurable.mul
        ((continuous_ceG1 (airyZero 1)).comp (continuous_const.add continuous_id)).aestronglyMeasurable.restrict
    · intro u
      refine ae_of_all _ fun y => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hG_bd _) (norm_nonneg _)
    · exact ae_of_all _ fun y => Continuous.mul continuous_const ((continuous_ceG1 (airyZero 1)).comp (continuous_id.add continuous_const))
  obtain ⟨AS, hAS, hgt⟩ := gt1Bounds_convSource_unif (p := p) (γ := γ) (θ := θ) hp hp1 hlam (by omega : 3 ≤ m)
  obtain ⟨CS, hCS, hS_rhp⟩ := convSource_twisted_unif (p := p) (γ := γ) (θ := θ) (lam := lam) hp hp1 hγ.le hθ.le hlam
  obtain ⟨b_r0, hbr0, hray0⟩ := convSource_neg_tail_lower
  refine ce_post_edge_unif hp hp1 hlam hm hU2S hcontS ⟨AS, hAS, fun {c δ₀} hc hδ => hgt (by linarith) hδ⟩
    hCS.le (fun {c w} hc hw => hS_rhp (liftEps_pos (by linarith)) (liftEps_le_one (by linarith)) hw)
    (fun {A B} hA hAB => ?_) ?_
    (fun {L_F} hLF => convSourceFamily_far_transfer hp hp1 hγ.le hθ hlam hLF hm)
    hCD
  · set U_ab : ℝ := max A B
    obtain ⟨b_c0, hbc0, hfl⟩ := convSource_compact_floor U_ab
    refine ⟨b_c0 * γ, mul_pos hbc0 hγ, fun {c u} hc hu => ?_⟩
    have hc0 : 0 < c := by linarith
    have hε0 : 0 < liftEps c := liftEps_pos hc0
    have hu_ab : |u| ≤ U_ab := abs_le.mpr ⟨by linarith [hu.1, le_max_left A B], hu.2.trans (le_max_right A B)⟩
    have hfl' := hfl p γ θ (liftEps c) (lam * liftEps c ^ 2) hp hp1 hγ hθ hε0 (by positivity) u hu_ab
    exact le_of_eq_of_le (by ring) hfl'
  · refine ⟨b_r0 * θ * (1 / 2 : ℝ) ^ p, mul_pos (mul_pos hbr0 hθ) (Real.rpow_pos_of_pos (by norm_num) p),
      4, by norm_num, fun {c x} hc hx => ?_⟩
    have hc0 : 0 < c := by linarith
    have hε0 : 0 < liftEps c := liftEps_pos hc0
    have hh : 0 < lam * liftEps c ^ 2 := by positivity
    have hlow := hray0 p γ θ (liftEps c) (lam * liftEps c ^ 2) hp hp1 hγ hθ hε0 hh x hx
    have hrho := convRho_min_lower (p := p) (t := lam * liftEps c ^ 2 * x) (by linarith) (by positivity)
    have hxp : 0 ≤ x ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
    have hbt : 0 ≤ b_r0 * θ := by positivity
    calc b_r0 * θ * (1 / 2 : ℝ) ^ p * (min 1 (lam * liftEps c ^ 2 * x)) ^ p * x ^ (-(3 / 2 : ℝ))
        = b_r0 * θ * ((1 / 2 : ℝ) ^ p * (min 1 (lam * liftEps c ^ 2 * x)) ^ p) * x ^ (-(3 / 2 : ℝ)) := by ring
      _ ≤ b_r0 * θ * convRho p (lam * liftEps c ^ 2 * x) * x ^ (-(3 / 2 : ℝ)) := by gcongr
      _ ≤ convSourceFamily p γ θ lam c (-x) := hlow

/-- **Post-edge Fourier sign for the convolution source `convSourceFamily`**:
specialization of `ce_post_edge` to `S_c = convSourceFamily p γ θ lam c` for
`p ∈ (1/2, 1)`, `γ > 0`, `θ > 0`, `λ > 0`, `m ≥ 4`. -/
theorem ce_post_edge_convSource
    {p γ θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 < γ) (hθ : 0 < θ) (hlam : 0 < lam)
    {m : ℕ} (hm : 4 ≤ m)
    {D : ℝ → ℝ → ℝ} {CD : ℝ} (hCD : 0 ≤ CD)
    (hdiffD : ∀ {c : ℝ}, 2 ≤ c → DifferentiableOn ℂ (airyTwistedLaplaceC (D c)) {y : ℂ | 0 < y.re})
    (hbdD : ∀ {c : ℝ} {w : ℂ}, 2 ≤ c → 0 ≤ w.re →
      ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤ CD * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) :
    ∃ κ₀ : ℝ, 1 ≤ κ₀ ∧ ∀ {κ : ℝ}, κ₀ ≤ κ → ∀ {U : ℝ}, 0 ≤ U → ∃ c₀ ≥ (2 : ℝ),
      ∀ {c ξ : ℝ}, c₀ ≤ c → 0 < ξ → -U ≤ hbS c ξ →
        0 < (iMain (convSourceFamily p γ θ lam c) (κ * liftEps c) m c ξ +
          iDual (D c) (κ * liftEps c) m c ξ).re := by
  obtain ⟨κ₀, hκ₀, h⟩ := ce_post_edge_convSource_unif hp hp1 hγ hθ hlam hm hCD
  exact ⟨κ₀, hκ₀, fun {κ} hκ {U} hU => h hκ hU (fun {c} => hdiffD) (fun {c w} => hbdD)⟩

/-- info: 'FormalResearch.SignUncertainty.gt1Bounds_convSource_unif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gt1Bounds_convSource_unif

/-- info: 'FormalResearch.SignUncertainty.ce_post_edge_unif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_post_edge_unif

/-- info: 'FormalResearch.SignUncertainty.ce_post_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_post_edge

/-- info: 'FormalResearch.SignUncertainty.ce_post_edge_convSource_unif' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_post_edge_convSource_unif

/-- info: 'FormalResearch.SignUncertainty.ce_post_edge_convSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_post_edge_convSource

end FormalResearch.SignUncertainty
