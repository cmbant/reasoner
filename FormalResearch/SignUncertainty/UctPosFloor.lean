module

public import FormalResearch.SignUncertainty.UctPosFloorSeed

/-!
# `uct:pos-floor` (2): main-edge floor, reflected-edge bounds and the lift of `S_pos` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:pos-floor` (2) (`(uct:pos-main-lb)`, `(uct:pos-dual-ub)`).

The seed `S_pos = airySeedU2 (-1/4) 1 1` is in the one-level family, so the whole analytic input is the structure `O6Est 4 1 g₀`
(`o6Bricks_holds`: `(e3)`, `(e4)`, `(e5)`, `(e6)` and the convolution form of the smoothing) and `exists_hankelEigenfn_lift`.  With `m = 4`,
`δ₀ = β₁ K ε / 2` (`ε = c^{-1/3}`, `S_eff = hbS c ξ`), the three bands of the TeX proof (high `S ≥ max(100, M₁K^{-2}c^{2/3})`, middle, window)
give the floor; the floor of the smoothing is `windowSmooth_floor_ray` (`S_pos(-x) ≥ c_pos (1+x)^{-3/2}`, `uct_pos_floor_one`) resp. its minimum on a
compact interval (`windowSmooth_floor_compact`).

Class: proved.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

set_option maxHeartbeats 4000000 in
/-- **`uct:pos-floor` (2), main-edge floor**. -/
theorem uct_pos_floor_main_lower :
    ∃ Kst : ℝ, 1 ≤ Kst ∧ ∃ cabs : ℝ, 0 < cabs ∧ ∃ Sw : ℝ, 100 ≤ Sw ∧ ∀ U : ℝ, 1 ≤ U → ∃ cU : ℝ, 0 < cU ∧ ∀ K : ℝ, Kst ≤ K →
      ∃ c0 : ℝ, ∀ c ξ : ℝ, c0 ≤ c → 0 < ξ → -U ≤ hbS c ξ →
      (Sw < hbS c ξ → cabs * hbS c ξ ^ (-(3 / 2 : ℝ)) ≤ (ξ * iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ).re) ∧
      (hbS c ξ ≤ Sw → cU ≤ (ξ * iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ).re) := by
  obtain ⟨g0, hg0, hE⟩ := o6Bricks_holds (m := 4) (by norm_num)
  have E := hE 1 zero_le_one
  obtain ⟨CH, hCH, h4⟩ := E.e4
  obtain ⟨C6, hC6, h6⟩ := E.e6
  obtain ⟨cpos, hcpos, hfl⟩ := uct_pos_floor_one.2.1
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hpi := Real.pi_pos
  have hβ := ceBeta1_pos
  have hβ2 := ceBeta1_gt_two
  have hβ8 := ceBeta1_lt_eight
  have hk := ceK_pos
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = g0 * Real.sqrt Real.pi := ⟨_, rfl⟩
  have hGpos : 0 < G := by rw [hGdef]; positivity
  obtain ⟨M₁, hM₁1, hM₁⟩ := exists_rpow_neg_le (p := ((4 : ℕ) : ℝ) / 2) (by norm_num) (ε := G / (8 * CH)) (by positivity)
  obtain ⟨Kh, hKh1, hKh⟩ := exists_rpow_neg_le (p := ((4 : ℕ) : ℝ)) (by norm_num) (ε := G / (8 * CH)) (by positivity)
  obtain ⟨Sh, hSh1, hSh⟩ := exists_rpow_neg_le (p := (1 / 2 : ℝ)) (by norm_num) (ε := G / (8 * CH)) (by positivity)
  obtain ⟨Sw, hSwdef⟩ : ∃ Sw : ℝ, Sw = max (max 100 Sh) ((|airyZero 1| + 1) / ceBeta1) := ⟨_, rfl⟩
  have hSw100 : 100 ≤ Sw := by rw [hSwdef]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hSwSh : Sh ≤ Sw := by rw [hSwdef]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hSwA : (|airyZero 1| + 1) / ceBeta1 ≤ Sw := by rw [hSwdef]; exact le_max_right _ _
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = (2 * ceBeta1 + 2) ^ (-(3 / 2 : ℝ)) := ⟨_, rfl⟩
  have hq : 0 < q := by rw [hqdef]; positivity
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = ceK * ceBeta1 * (cpos * q) / Real.pi ^ 2 := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; positivity
  obtain ⟨cabs, hcabsdef⟩ : ∃ cabs : ℝ, cabs = min (G / (4 * Real.pi ^ 4)) (κ / 2) := ⟨_, rfl⟩
  have hcabs : 0 < cabs := by rw [hcabsdef]; exact lt_min (by positivity) (by positivity)
  refine ⟨max (max Kh M₁) (max (500 * Real.pi ^ 2 * M₁) (4 * C6 * M₁ / κ + 1)), ?_, cabs, hcabs, Sw, hSw100, fun U hU => ?_⟩
  · exact hKh1.trans ((le_max_left _ _).trans (le_max_left _ _))
  -- window constants
  obtain ⟨CW, hCW, h5⟩ := E.e5 (max Sw U)
  obtain ⟨mU, hmU, hfloorU⟩ := windowSmooth_floor_compact (ceBeta1 * max Sw U + 2) (ceBeta1 * U + 2)
  refine ⟨ceK * ceBeta1 * mU / (2 * Real.pi ^ 2), by positivity, fun K hK => ?_⟩
  have hKKh : Kh ≤ K := (le_max_left _ _).trans ((le_max_left _ _).trans hK)
  have hKM : M₁ ≤ K := (le_max_right _ _).trans ((le_max_left _ _).trans hK)
  have hK500 : 500 * Real.pi ^ 2 * M₁ ≤ K := (le_max_left _ _).trans ((le_max_right _ _).trans hK)
  have hKbig : 4 * C6 * M₁ / κ + 1 ≤ K := (le_max_right _ _).trans ((le_max_right _ _).trans hK)
  have hK1 : 1 ≤ K := hKh1.trans hKKh
  have hK0 : 0 < K := by linarith only [hK1]
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = ceK * ceBeta1 * mU / (4 * Real.pi ^ 2 * CW) := ⟨_, rfl⟩
  have hθ : 0 < θ := by rw [hθdef]; positivity
  obtain ⟨Mw, hMw1, hMw⟩ := exists_rpow_neg_le (p := (1 / 2 : ℝ)) (by norm_num) (ε := θ) hθ
  refine ⟨max (max (max 2000 32768) (64 * K ^ 3)) Mw, fun c ξ hc hξ hSU => ?_⟩
  have hc2000 : 2000 ≤ c := ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hc
  have hc32768 : 32768 ≤ c := ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hc
  have hc64 : 64 * K ^ 3 ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hcMw : Mw ≤ c := (le_max_right _ _).trans hc
  have hc0 : 0 < c := by linarith
  have hε : 0 < liftEps c := liftEps_pos hc0
  have hcube : liftEps c ^ 3 * c = 1 := liftEps_cube_mul hc0
  have hKe3 : (K * liftEps c) ^ 3 * c = K ^ 3 := by
    calc (K * liftEps c) ^ 3 * c = K ^ 3 * (liftEps c ^ 3 * c) := by ring
      _ = K ^ 3 := by rw [hcube, mul_one]
  have hKε : K * liftEps c ≤ 1 / 4 := by
    by_contra hcon
    have hcon := not_le.mp hcon
    have h2 : (1 / 4 : ℝ) ^ 3 < (K * liftEps c) ^ 3 := pow_lt_pow_left₀ hcon (by norm_num) (by norm_num)
    have h3 := mul_lt_mul_of_pos_right h2 hc0
    rw [hKe3] at h3
    norm_num at h3
    linarith
  have hε4 : liftEps c ≤ 1 / 4 := by nlinarith only [hKε, hK1, hε]
  have hδ₀pos : 0 < ceBeta1 * K * liftEps c / 2 := by positivity
  have hδ₀le : ceBeta1 * K * liftEps c / 2 ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_right hβ8.le (by positivity : 0 ≤ K * liftEps c)
    have : ceBeta1 * K * liftEps c = ceBeta1 * (K * liftEps c) := by ring
    linarith
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = hbS c ξ := ⟨_, rfl⟩
  rw [← hSdef] at hSU ⊢
  have hcs := ceCs_one_lt
  have hεcs : liftEps c / (2 * ceCs) ≤ 1 := by
    refine (div_le_self hε.le (by linarith)).trans (by linarith)
  have hLeq : Real.log (Real.pi ^ 2 * ξ) = Real.pi ^ 2 * liftEps c ^ 2 * S := by rw [hSdef]; exact log_eq_hbS hc0
  have hRK : (ceK : ℝ) * ceBeta1 / Real.pi ^ 2 > 0 := by positivity
  refine ⟨?_, ?_⟩
  swap
  · intro hwin -- window
    have hS5 : |hbS c ξ| ≤ max Sw U := by
      rw [← hSdef, abs_le]; exact ⟨by linarith [le_max_right Sw U], by linarith [le_max_left Sw U]⟩
    have hR1 : |(-1 / 4 : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
    have hR2 : |(1 : ℝ)| ≤ 1 := by simp
    have e5p := h5 (a := -1 / 4) (b := 1) (c₀ := 1) (σ := 1) (δ₀ := ceBeta1 * K * liftEps c / 2) (c := c) (ξ := ξ)
      hR1 hR2 hR2 (Or.inl rfl) hδ₀pos.le hc32768 hξ hS5
    have e5m := h5 (a := -1 / 4) (b := 1) (c₀ := 1) (σ := -1) (δ₀ := ceBeta1 * K * liftEps c / 2) (c := c) (ξ := ξ)
      hR1 hR2 hR2 (Or.inr rfl) hδ₀pos.le hc32768 hξ hS5
    rw [← hSdef] at e5p e5m
    obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = windowSmooth (ceBeta1 * K * liftEps c / 2) 4 uctSpos (-(ceBeta1 * S) - liftEps c / (2 * ceCs)) := ⟨_, rfl⟩
    rw [← hWdef] at e5p e5m
    obtain ⟨Er, hErdef⟩ : ∃ Er : ℝ, Er = CW * ξ⁻¹ * (liftEps c ^ 2 + (((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ * c ^ (-(1 / 2 : ℝ)))) := ⟨_, rfl⟩
    have hW : mU ≤ W := by
      rw [hWdef]
      refine hfloorU hδ₀pos (m := 4) (by norm_num) _ ?_ ?_
      · have h1 : ceBeta1 * S ≤ ceBeta1 * max Sw U := mul_le_mul_of_nonneg_left (hwin.trans (le_max_left _ _)) hβ.le
        linarith
      · have h1 : -(ceBeta1 * S) ≤ ceBeta1 * U := by nlinarith only [hSU, hβ]
        have : 0 ≤ liftEps c / (2 * ceCs) := by positivity
        linarith
    have hcnorm : ‖iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ - ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * W : ℝ) : ℂ)‖ ≤ Er := by
      have e : iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ - ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * W : ℝ) : ℂ) =
          (1 / 2 : ℂ) * ((iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ + ((1 : ℝ) : ℂ) * iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ -
              ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * W : ℝ) : ℂ)) +
            (iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ + ((-1 : ℝ) : ℂ) * iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ -
              ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * W : ℝ) : ℂ))) := by push_cast; ring
      rw [e, norm_mul]
      have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
      rw [h12]
      calc 1 / 2 * ‖(_ : ℂ) + _‖ ≤ 1 / 2 * (‖(_ : ℂ)‖ + ‖(_ : ℂ)‖) := by gcongr; exact norm_add_le _ _
        _ ≤ 1 / 2 * (Er + Er) := by gcongr; exact e5p.trans_eq hErdef.symm; exact e5m.trans_eq hErdef.symm
        _ = Er := by ring
    have hξEr : ξ * Er ≤ ceK * ceBeta1 * mU / (2 * Real.pi ^ 2) := by
      have hc12 : c ^ (-(1 / 2 : ℝ)) ≤ θ := hMw c hcMw
      have hε2 : liftEps c ^ 2 ≤ c ^ (-(1 / 2 : ℝ)) := by
        have : liftEps c ^ 2 = c ^ (-(2 / 3 : ℝ)) := by
          unfold liftEps; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
        rw [this]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have hinv : ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ ≤ 1 := by
        refine inv_le_one_of_one_le₀ (one_le_pow₀ ?_)
        have : 0 ≤ ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ) := by positivity
        linarith
      have hc12' : 0 ≤ c ^ (-(1 / 2 : ℝ)) := by positivity
      have h2 : liftEps c ^ 2 + ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ * c ^ (-(1 / 2 : ℝ)) ≤ 2 * θ := by
        have : ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ * c ^ (-(1 / 2 : ℝ)) ≤ 1 * c ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hinv hc12'
        linarith
      rw [hErdef]
      calc ξ * (CW * ξ⁻¹ * (liftEps c ^ 2 + ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ * c ^ (-(1 / 2 : ℝ))))
          = CW * (liftEps c ^ 2 + ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ * c ^ (-(1 / 2 : ℝ))) := by field_simp
        _ ≤ CW * (2 * θ) := by gcongr
        _ = ceK * ceBeta1 * mU / (2 * Real.pi ^ 2) := by rw [hθdef]; field_simp; ring
    have hre : ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * W : ℝ)) - Er ≤ (iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ).re := by
      have h1 := Complex.abs_re_le_norm (iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ - ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * W : ℝ) : ℂ))
      simp only [Complex.sub_re, Complex.ofReal_re] at h1
      have := (abs_le.mp h1).1
      linarith [hcnorm]
    rw [Complex.re_ofReal_mul]
    have hξA : ξ * (ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * W) = ceK * ceBeta1 / Real.pi ^ 2 * W := by field_simp
    have hmain : ceK * ceBeta1 * mU / (2 * Real.pi ^ 2) ≤ ξ * (iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ).re := by
      have h3 := mul_le_mul_of_nonneg_left hre hξ.le
      have h4 : ceK * ceBeta1 / Real.pi ^ 2 * mU ≤ ceK * ceBeta1 / Real.pi ^ 2 * W := mul_le_mul_of_nonneg_left hW hRK.le
      have h5' : ceK * ceBeta1 / Real.pi ^ 2 * mU = 2 * (ceK * ceBeta1 * mU / (2 * Real.pi ^ 2)) := by field_simp
      nlinarith only [h3, h4, hξA, hξEr, h5']
    exact hmain
  intro hwin'
  have hS100 : 100 ≤ S := by linarith
  have hS1 : 1 ≤ S := by linarith
  have hSpos : 0 < S := by linarith
  have hLpos : 0 < Real.log (Real.pi ^ 2 * ξ) := by rw [hLeq]; positivity
  have hR1 : |(-1 / 4 : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hR2 : |(1 : ℝ)| ≤ 1 := by simp
  by_cases hmid : S ≤ M₁ * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ)
  · -- middle band
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
      have h3 : Real.pi ^ 2 * liftEps c ^ 2 * S = Real.pi ^ 2 * (liftEps c ^ 2 * S) := by ring
      linarith
    have e6 := h6 (a := -1 / 4) (b := 1) (c₀ := 1) (δ₀ := ceBeta1 * K * liftEps c / 2) (c := c) (ξ := ξ)
      (L := Real.log (Real.pi ^ 2 * ξ)) hR1 hR2 hR2 ⟨hδ₀pos.le, by linarith⟩ (by linarith) hξ rfl hLpos hL2
      (by rw [← hSdef]; exact hS100)
    rw [← hSdef] at e6
    obtain ⟨hκ1, hκ2⟩ := edgeKappa0_bounds hLpos hL2
    obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = edgeKappa0 (Real.log (Real.pi ^ 2 * ξ)) * ceBeta1 * S + liftEps c / (2 * ceCs) := ⟨_, rfl⟩
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
    have hxA : |airyZero 1| + 1 ≤ x := by
      have h1 : (|airyZero 1| + 1) ≤ ceBeta1 * Sw := by
        have := (div_le_iff₀ hβ).mp hSwA; linarith only [this]
      have h2 := mul_le_mul_of_nonneg_left hwin'.le hβ.le
      linarith only [h1, h2, hxge]
    have hfx := windowSmooth_floor_ray hδ₀pos hδ₀le (m := 4) (by norm_num) hfl hcpos.le hxA
    obtain ⟨Wv, hWvdef⟩ : ∃ Wv : ℝ, Wv = windowSmooth (ceBeta1 * K * liftEps c / 2) 4 uctSpos (-x) := ⟨_, rfl⟩
    rw [← hWvdef] at hfx
    have hqS : q * S ^ (-(3 / 2 : ℝ)) ≤ (1 + x) ^ (-(3 / 2 : ℝ)) := by
      have := Real.rpow_le_rpow_of_nonpos (by linarith [hxA, abs_nonneg (airyZero 1)] : (0 : ℝ) < 1 + x) hxup (by norm_num : -(3 / 2 : ℝ) ≤ 0)
      rw [Real.mul_rpow (by positivity) hSpos.le, ← hqdef] at this
      exact this
    have hWlow : cpos * (q * S ^ (-(3 / 2 : ℝ))) ≤ Wv :=
      le_trans (mul_le_mul_of_nonneg_left hqS hcpos.le) hfx
    have hcast : ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) : ℝ) : ℂ) * ((windowSmooth (ceBeta1 * K * liftEps c / 2) 4 uctSpos (-x) : ℝ) : ℂ) =
        ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * Wv : ℝ) : ℂ) := by rw [hWvdef]; push_cast; ring
    rw [hcast] at e6
    -- error terms
    have hc52 : c ^ (-(5 / 2 : ℝ)) ≤ S ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * S) := by
      have h1 := c_rpow_mul_S_le (by linarith : 1 ≤ c) hSpos hy1
      have h2 : S ^ (-(3 / 2 : ℝ)) * S ^ (3 / 2 : ℝ) = 1 := by
        rw [← Real.rpow_add hSpos]; norm_num
      calc c ^ (-(5 / 2 : ℝ)) = S ^ (-(3 / 2 : ℝ)) * (c ^ (-(5 / 2 : ℝ)) * S ^ (3 / 2 : ℝ)) := by
            rw [← mul_assoc, mul_comm (S ^ (-(3 / 2 : ℝ))), mul_assoc, h2, mul_one]
        _ ≤ S ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * S) := by gcongr
    have hξi : 0 < ξ⁻¹ := inv_pos.mpr hξ
    have herr : ξ * (C6 * ξ⁻¹ * (S ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * S) + c ^ (-(5 / 2 : ℝ)))) ≤
        (κ / 2) * S ^ (-(3 / 2 : ℝ)) := by
      have hbig : 4 * C6 * M₁ < κ * K := by
        have h1 : 4 * C6 * M₁ / κ < K := by linarith
        have := (div_lt_iff₀ hκ).mp h1
        linarith [mul_comm K κ]
      have hbig2 : 4 * C6 * M₁ ≤ κ * K ^ 2 := by nlinarith only [hbig, hKK, hκ]
      have hSr : 0 < S ^ (-(3 / 2 : ℝ)) := by positivity
      calc ξ * (C6 * ξ⁻¹ * (S ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * S) + c ^ (-(5 / 2 : ℝ))))
          = C6 * (S ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * S) + c ^ (-(5 / 2 : ℝ))) := by field_simp
        _ ≤ C6 * (2 * (S ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * S))) := by gcongr; linarith
        _ = 2 * C6 * S ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * S) := by ring
        _ ≤ 2 * C6 * S ^ (-(3 / 2 : ℝ)) * (M₁ / K ^ 2) := by gcongr
        _ = (2 * C6 * M₁ / K ^ 2) * S ^ (-(3 / 2 : ℝ)) := by ring
        _ ≤ (κ / 2) * S ^ (-(3 / 2 : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ hSr.le
            rw [div_le_iff₀ hK2]; linarith
    have hre : ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * Wv : ℝ)) - C6 * ξ⁻¹ * (S ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * S) + c ^ (-(5 / 2 : ℝ))) ≤
        (iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ).re := by
      have h1 := Complex.abs_re_le_norm (iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ - ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * Wv : ℝ) : ℂ))
      simp only [Complex.sub_re, Complex.ofReal_re] at h1
      have := (abs_le.mp h1).1
      have e6' : ‖iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ - ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * Wv : ℝ) : ℂ)‖ ≤
          C6 * ξ⁻¹ * (S ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * S) + c ^ (-(5 / 2 : ℝ))) := e6
      linarith [this, e6']
    rw [Complex.re_ofReal_mul]
    have hξA : ξ * (ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * Wv) = ceK * ceBeta1 / Real.pi ^ 2 * Wv := by field_simp
    have hA : κ * S ^ (-(3 / 2 : ℝ)) ≤ ceK * ceBeta1 / Real.pi ^ 2 * Wv := by
      have := mul_le_mul_of_nonneg_left hWlow hRK.le
      calc κ * S ^ (-(3 / 2 : ℝ)) = ceK * ceBeta1 / Real.pi ^ 2 * (cpos * (q * S ^ (-(3 / 2 : ℝ)))) := by rw [hκdef]; ring
        _ ≤ _ := this
    have h3 := mul_le_mul_of_nonneg_left hre hξ.le
    have h2 : cabs ≤ κ / 2 := by rw [hcabsdef]; exact min_le_right _ _
    have hSr : 0 < S ^ (-(3 / 2 : ℝ)) := by positivity
    have h4 : cabs * S ^ (-(3 / 2 : ℝ)) ≤ κ / 2 * S ^ (-(3 / 2 : ℝ)) := mul_le_mul_of_nonneg_right h2 hSr.le
    nlinarith only [h3, hξA, hA, herr, h4]
  · -- high band
    have hmid' := not_le.mp hmid
    have e4 := h4 (a := -1 / 4) (b := 1) (c₀ := 1) (K := K) (M₁ := M₁) (c := c) (ξ := ξ) hR1 hR2 hR2 hK1 hM₁1
      (by nlinarith only [hc64, pow_pos hK0 3]) hc2000 hξ (by rw [← hSdef]; exact hS100)
      (by rw [← hSdef]; exact hmid'.le)
    rw [← hSdef] at e4
    have hA' : hbA c ξ = Real.pi ^ 2 * S := by rw [hSdef]; exact hbA_eq hc0
    obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) := ⟨_, rfl⟩
    have hPpos : 0 < P := by rw [hPdef, hA']; positivity
    have hAeq : ((1 - (-1 / 4 : ℝ)) * g0) * Real.sqrt Real.pi * hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) = (5 / 4) * G * P := by
      rw [hPdef, hGdef]; ring
    rw [hAeq, ← hPdef] at e4
    have hb1 : CH * M₁ ^ (-(((4 : ℕ) : ℝ) / 2)) ≤ G / 8 := by
      calc CH * M₁ ^ (-(((4 : ℕ) : ℝ) / 2)) ≤ CH * (G / (8 * CH)) := by gcongr; exact hM₁ M₁ le_rfl
        _ = G / 8 := by field_simp
    have hb2 : CH * K ^ (-((4 : ℕ) : ℝ)) ≤ G / 8 := by
      calc CH * K ^ (-((4 : ℕ) : ℝ)) ≤ CH * (G / (8 * CH)) := by gcongr; exact hKh K hKKh
        _ = G / 8 := by field_simp
    have hb3 : CH * S ^ (-(1 / 2 : ℝ)) ≤ G / 8 := by
      calc CH * S ^ (-(1 / 2 : ℝ)) ≤ CH * (G / (8 * CH)) := by gcongr; exact hSh S (hSwSh.trans hwin'.le)
        _ = G / 8 := by field_simp
    have hnorm : ‖iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ - (((5 / 4) * G * P : ℝ) : ℂ)‖ ≤ (3 * G / 8) * P := by
      have e4' : ‖iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ - (((5 / 4) * G * P : ℝ) : ℂ)‖ ≤
          CH * (M₁ ^ (-(((4 : ℕ) : ℝ) / 2)) + K ^ (-((4 : ℕ) : ℝ)) + S ^ (-(1 / 2 : ℝ))) * P := e4
      refine e4'.trans ?_
      have : CH * (M₁ ^ (-(((4 : ℕ) : ℝ) / 2)) + K ^ (-((4 : ℕ) : ℝ)) + S ^ (-(1 / 2 : ℝ))) ≤ 3 * G / 8 := by
        have := mul_add CH (M₁ ^ (-(((4 : ℕ) : ℝ) / 2)) + K ^ (-((4 : ℕ) : ℝ))) (S ^ (-(1 / 2 : ℝ)))
        have := mul_add CH (M₁ ^ (-(((4 : ℕ) : ℝ) / 2))) (K ^ (-((4 : ℕ) : ℝ)))
        linarith
      exact mul_le_mul_of_nonneg_right this hPpos.le
    have hre : (5 / 4) * G * P - (3 * G / 8) * P ≤ (iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ).re := by
      have h1 := Complex.abs_re_le_norm (iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ - (((5 / 4) * G * P : ℝ) : ℂ))
      simp only [Complex.sub_re, Complex.ofReal_re] at h1
      have := (abs_le.mp h1).1
      linarith [hnorm]
    rw [Complex.re_ofReal_mul]
    have hξP : ξ * P = (Real.pi ^ 3)⁻¹ * S ^ (-(3 / 2 : ℝ)) / (2 * Real.pi) := by
      have h1 : (Real.pi ^ 2 * S) ^ (-(3 / 2 : ℝ)) = (Real.pi ^ 3)⁻¹ * S ^ (-(3 / 2 : ℝ)) := by
        rw [Real.mul_rpow (by positivity) hSpos.le]
        congr 1
        rw [show (Real.pi ^ 2 : ℝ) = Real.pi ^ (2 : ℝ) by norm_cast, ← Real.rpow_mul hpi.le,
          show (2 : ℝ) * (-(3 / 2)) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hpi.le, Real.rpow_natCast]
      rw [hPdef, hA', h1]; field_simp
    have hSr : 0 < S ^ (-(3 / 2 : ℝ)) := by positivity
    have h2 : cabs ≤ G / (4 * Real.pi ^ 4) := by rw [hcabsdef]; exact min_le_left _ _
    have h3 := mul_le_mul_of_nonneg_left hre hξ.le
    have hlow : G / (4 * Real.pi ^ 4) * S ^ (-(3 / 2 : ℝ)) ≤ ξ * ((5 / 4) * G * P - (3 * G / 8) * P) := by
      have : ξ * ((5 / 4) * G * P - (3 * G / 8) * P) = (7 / 8) * G * (ξ * P) := by ring
      rw [this, hξP]
      have : (7 / 8) * G * ((Real.pi ^ 3)⁻¹ * S ^ (-(3 / 2 : ℝ)) / (2 * Real.pi)) = (7 / 16) * G / Real.pi ^ 4 * S ^ (-(3 / 2 : ℝ)) := by
        field_simp; norm_num
      rw [this]
      apply mul_le_mul_of_nonneg_right _ hSr.le
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ G * Real.pi ^ 4 := by positivity
      nlinarith only [this]
    have h4 : cabs * S ^ (-(3 / 2 : ℝ)) ≤ G / (4 * Real.pi ^ 4) * S ^ (-(3 / 2 : ℝ)) := mul_le_mul_of_nonneg_right h2 hSr.le
    linarith [h3, hlow, h4]

set_option maxHeartbeats 1000000 in
/-- **`(uct:pos-dual-ub)`** (far reflected bound): for `S_eff ≥ 1`. -/
theorem uct_pos_floor_dual_far : ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K → ∃ c0 : ℝ, ∀ c ξ : ℝ, c0 ≤ c → 0 < ξ → 1 ≤ hbS c ξ →
    ‖(ξ : ℂ) * iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ‖ ≤
      C * K ^ (-(4 : ℝ)) * c⁻¹ * min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨g0, hg0, hE⟩ := o6Bricks_holds (m := 4) (by norm_num)
  have E := hE 1 zero_le_one
  obtain ⟨CD, hCD, h3⟩ := E.e3
  have hR1 : |(-1 / 4 : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hR2 : |(1 : ℝ)| ≤ 1 := by simp
  have hβ2 := ceBeta1_gt_two
  have hβ8 := ceBeta1_lt_eight
  refine ⟨CD, hCD, fun K hK => ⟨max 2000 (64 * K ^ 3), fun c ξ hc hξ hS => ?_⟩⟩
  have hc2000 : 2000 ≤ c := (le_max_left _ _).trans hc
  have hc64 : 64 * K ^ 3 ≤ c := (le_max_right _ _).trans hc
  have hc0 : 0 < c := by linarith
  have hK0 : 0 < K := by linarith
  have hε : 0 < liftEps c := liftEps_pos hc0
  have hcube : liftEps c ^ 3 * c = 1 := liftEps_cube_mul hc0
  have hKe3 : (K * liftEps c) ^ 3 * c = K ^ 3 := by
    calc (K * liftEps c) ^ 3 * c = K ^ 3 * (liftEps c ^ 3 * c) := by ring
      _ = K ^ 3 := by rw [hcube, mul_one]
  have hKε : K * liftEps c ≤ 1 / 4 := by
    by_contra hcon
    have hcon := not_le.mp hcon
    have h2 : (1 / 4 : ℝ) ^ 3 < (K * liftEps c) ^ 3 := pow_lt_pow_left₀ hcon (by norm_num) (by norm_num)
    have h3 := mul_lt_mul_of_pos_right h2 hc0
    rw [hKe3] at h3
    norm_num at h3
    linarith
  have hδ₀pos : 0 < ceBeta1 * K * liftEps c / 2 := by have := ceBeta1_pos; positivity
  have hδ₀le : ceBeta1 * K * liftEps c / 2 ≤ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hβ8.le (by positivity : 0 ≤ K * liftEps c)
    have : ceBeta1 * K * liftEps c = ceBeta1 * (K * liftEps c) := by ring
    linarith
  have e3 := h3 (a := -1 / 4) (b := 1) (c₀ := 1) (δ₀ := ceBeta1 * K * liftEps c / 2) (c := c) (ξ := ξ) hR1 hR2 hR2
    ⟨hδ₀pos, hδ₀le⟩ (by linarith) hξ hS
  have hεc : liftEps c * c ^ (1 / 3 : ℝ) = 1 := by rw [rpow_third_eq hc0]; field_simp
  have hbase : K ≤ 1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ) := by
    have : ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ) = ceBeta1 / 2 * K * (liftEps c * c ^ (1 / 3 : ℝ)) := by ring
    rw [this, hεc]; nlinarith only [hβ2, hK0]
  have hB : (1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ (-(((4 : ℕ) : ℝ))) ≤ K ^ (-(4 : ℝ)) := by
    have := Real.rpow_le_rpow_of_nonpos hK0 hbase (by norm_num : -(((4 : ℕ) : ℝ)) ≤ 0)
    simpa using this
  have hmin0 : 0 ≤ min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by
    have hL : 0 < Real.log (Real.pi ^ 2 * ξ) := by
      have := log_eq_hbS (ξ := ξ) hc0
      rw [this]; have := ceBeta1_pos; positivity
    exact le_min (by positivity) (by positivity)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ]
  calc ξ * ‖iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ‖
      ≤ ξ * (CD * ξ⁻¹ * (1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ (-(((4 : ℕ) : ℝ))) * c⁻¹ *
        min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)))) := by
          gcongr
    _ = CD * (1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ (-(((4 : ℕ) : ℝ))) * c⁻¹ *
        min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by field_simp
    _ ≤ CD * K ^ (-(4 : ℝ)) * c⁻¹ * min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by
          have hc' : 0 < c⁻¹ := inv_pos.mpr hc0
          gcongr


set_option maxHeartbeats 1000000 in
/-- **`uct:pos-floor` (2), reflected bound on `-U ≤ S_eff ≤ S_m`** (the paper's `S_m = 100`): `|ξ I_dual| ≤ C_U K^{-4} c^{-1/2}`. -/
theorem uct_pos_floor_dual_near (U Sm : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K → ∃ c0 : ℝ, ∀ c ξ : ℝ, c0 ≤ c → 0 < ξ →
    -U ≤ hbS c ξ → hbS c ξ ≤ Sm →
    ‖(ξ : ℂ) * iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ‖ ≤ C * K ^ (-(4 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨g0, hg0, hE⟩ := o6Bricks_holds (m := 4) (by norm_num)
  have E := hE 1 zero_le_one
  obtain ⟨CW, hCW, h5⟩ := E.e5 (max |U| |Sm|)
  have hR1 : |(-1 / 4 : ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hR2 : |(1 : ℝ)| ≤ 1 := by simp
  have hβ2 := ceBeta1_gt_two
  have hβ8 := ceBeta1_lt_eight
  refine ⟨2 * CW, by positivity, fun K hK => ⟨max (max 32768 (64 * K ^ 3)) (K ^ 24), fun c ξ hc hξ hSU hSm => ?_⟩⟩
  have hc32768 : 32768 ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hc)
  have hc64 : 64 * K ^ 3 ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
  have hc24 : K ^ 24 ≤ c := (le_max_right _ _).trans hc
  have hc0 : 0 < c := by linarith
  have hK0 : 0 < K := by linarith
  have hε : 0 < liftEps c := liftEps_pos hc0
  have hcube : liftEps c ^ 3 * c = 1 := liftEps_cube_mul hc0
  have hKe3 : (K * liftEps c) ^ 3 * c = K ^ 3 := by
    calc (K * liftEps c) ^ 3 * c = K ^ 3 * (liftEps c ^ 3 * c) := by ring
      _ = K ^ 3 := by rw [hcube, mul_one]
  have hKε : K * liftEps c ≤ 1 / 4 := by
    by_contra hcon
    have hcon := not_le.mp hcon
    have h2 : (1 / 4 : ℝ) ^ 3 < (K * liftEps c) ^ 3 := pow_lt_pow_left₀ hcon (by norm_num) (by norm_num)
    have h3 := mul_lt_mul_of_pos_right h2 hc0
    rw [hKe3] at h3
    norm_num at h3
    linarith
  have hδ₀pos : 0 < ceBeta1 * K * liftEps c / 2 := by have := ceBeta1_pos; positivity
  have hS5 : |hbS c ξ| ≤ max |U| |Sm| := by
    rw [abs_le]; constructor
    · have := neg_abs_le U; have := le_max_left |U| |Sm|; have := le_abs_self U; linarith
    · have := le_abs_self Sm; have := le_max_right |U| |Sm|; linarith
  have e5p := h5 (a := -1 / 4) (b := 1) (c₀ := 1) (σ := 1) (δ₀ := ceBeta1 * K * liftEps c / 2) (c := c) (ξ := ξ)
    hR1 hR2 hR2 (Or.inl rfl) hδ₀pos.le hc32768 hξ hS5
  have e5m := h5 (a := -1 / 4) (b := 1) (c₀ := 1) (σ := -1) (δ₀ := ceBeta1 * K * liftEps c / 2) (c := c) (ξ := ξ)
    hR1 hR2 hR2 (Or.inr rfl) hδ₀pos.le hc32768 hξ hS5
  obtain ⟨Er, hErdef⟩ : ∃ Er : ℝ, Er = CW * ξ⁻¹ * (liftEps c ^ 2 + (((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ * c ^ (-(1 / 2 : ℝ)))) := ⟨_, rfl⟩
  have hdual : ‖iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ‖ ≤ Er := by
    have e : iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ =
        (1 / 2 : ℂ) * ((iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ + ((1 : ℝ) : ℂ) * iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ -
            ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * windowSmooth (ceBeta1 * K * liftEps c / 2) 4 uctSpos (-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs)) : ℝ) : ℂ)) -
          (iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ + ((-1 : ℝ) : ℂ) * iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ -
            ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) * windowSmooth (ceBeta1 * K * liftEps c / 2) 4 uctSpos (-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs)) : ℝ) : ℂ))) := by
      push_cast; ring
    rw [e, norm_mul]
    have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [h12]
    calc 1 / 2 * ‖(_ : ℂ) - _‖ ≤ 1 / 2 * (‖(_ : ℂ)‖ + ‖(_ : ℂ)‖) := by gcongr; exact norm_sub_le _ _
      _ ≤ 1 / 2 * (Er + Er) := by gcongr; exact e5p.trans_eq hErdef.symm; exact e5m.trans_eq hErdef.symm
      _ = Er := by ring
  have hεc : liftEps c * c ^ (1 / 3 : ℝ) = 1 := by rw [rpow_third_eq hc0]; field_simp
  have hbase : K ≤ 1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ) := by
    have : ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ) = ceBeta1 / 2 * K * (liftEps c * c ^ (1 / 3 : ℝ)) := by ring
    rw [this, hεc]; nlinarith only [hβ2, hK0]
  have hinv : ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ ≤ K ^ (-(4 : ℝ)) := by
    have h1 : K ^ 4 ≤ (1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4 := pow_le_pow_left₀ hK0.le hbase 4
    rw [show K ^ (-(4 : ℝ)) = (K ^ 4)⁻¹ by rw [Real.rpow_neg hK0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
    exact inv_anti₀ (by positivity) h1
  have hc12 : 0 ≤ c ^ (-(1 / 2 : ℝ)) := by positivity
  have hε2 : liftEps c ^ 2 ≤ K ^ (-(4 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
    have e1 : liftEps c ^ 2 = c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 6 : ℝ)) := by
      unfold liftEps; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; norm_num
    have e2 : c ^ (-(1 / 6 : ℝ)) ≤ K ^ (-(4 : ℝ)) := by
      have h1 : (K ^ 24) ^ (-(1 / 6 : ℝ)) ≤ K ^ (-(4 : ℝ)) := by
        rw [show (K ^ 24 : ℝ) = K ^ ((24 : ℕ) : ℝ) by rw [Real.rpow_natCast], ← Real.rpow_mul hK0.le]; norm_num
      exact (Real.rpow_le_rpow_of_nonpos (by positivity) hc24 (by norm_num)).trans h1
    rw [e1, mul_comm]; exact mul_le_mul_of_nonneg_right e2 hc12
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ]
  have hξEr : ξ * Er ≤ 2 * CW * (K ^ (-(4 : ℝ)) * c ^ (-(1 / 2 : ℝ))) := by
    rw [hErdef]
    calc ξ * (CW * ξ⁻¹ * (liftEps c ^ 2 + ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ * c ^ (-(1 / 2 : ℝ))))
        = CW * (liftEps c ^ 2 + ((1 + ceBeta1 * K * liftEps c / 2 * c ^ (1 / 3 : ℝ)) ^ 4)⁻¹ * c ^ (-(1 / 2 : ℝ))) := by field_simp
      _ ≤ CW * (K ^ (-(4 : ℝ)) * c ^ (-(1 / 2 : ℝ)) + K ^ (-(4 : ℝ)) * c ^ (-(1 / 2 : ℝ))) := by
          gcongr
      _ = 2 * CW * (K ^ (-(4 : ℝ)) * c ^ (-(1 / 2 : ℝ))) := by ring
  calc ξ * ‖iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ‖ ≤ ξ * Er := mul_le_mul_of_nonneg_left hdual hξ.le
    _ ≤ _ := hξEr.trans_eq (by ring)


set_option maxHeartbeats 2000000 in
/-- **`uct:pos-floor` (2), the lift** `f^σ_pos = L_c^σ[S_pos] ∈ 𝒜_c^σ`: the floor of the normalised density
`h_norm^{fl}(L) = c^{1/3} ξ (f ρ₀)(c ξ) = ξ (I_main + σ I_dual)(ξ)` and the vacuum value `σ f(0) = k (1 + |a₁'|) + O(c^{-5/6})`.
The threshold `K_*` is absolute (it depends only on the fixed constants of the three bands). -/
theorem uct_pos_floor_lift :
    ∃ Kst : ℝ, 1 ≤ Kst ∧ ∃ Cv : ℝ, 0 < Cv ∧ ∀ U : ℝ, 1 ≤ U → ∃ cfl : ℝ, 0 < cfl ∧ ∀ K : ℝ, Kst ≤ K → ∃ c0 : ℝ, ∀ c : ℝ, c0 ≤ c →
      ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∃ f : ℝ → ℝ, IsHankelEigenfn c σ f ∧
        (∀ ξ : ℝ, 0 < ξ → ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * f (c * ξ) : ℝ) : ℂ) =
          iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ + (σ : ℂ) * iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ) ∧
        (∀ ξ : ℝ, 0 < ξ → -U ≤ hbS c ξ →
          1 / 2 * cfl * (1 + max (hbS c ξ) 0) ^ (-(3 / 2 : ℝ)) ≤ ξ * (c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * f (c * ξ))) ∧
        |σ * f 0 - ceK * (1 + |airyDerivFirstZero|)| ≤ Cv * c ^ (-(5 / 6 : ℝ)) := by
  obtain ⟨Kst0, hKst0, cabs, hcabs, Sw, hSw, hmain⟩ := uct_pos_floor_main_lower
  obtain ⟨Cfar, hCfar, hfar⟩ := uct_pos_floor_dual_far
  obtain ⟨Cv, hCv, hrhp⟩ := airySeedU2_rhp (-1 / 4) 1 1
  have hpi := Real.pi_pos
  obtain ⟨Kf, hKf1, hKf⟩ := exists_rpow_neg_le (p := (4 : ℝ)) (by norm_num) (ε := cabs * Real.pi ^ 3 / (2 * Cfar)) (by positivity)
  refine ⟨max Kst0 Kf, hKst0.trans (le_max_left _ _), Cv, hCv, fun U hU => ?_⟩
  obtain ⟨cU, hcU, hmainU⟩ := hmain U hU
  obtain ⟨Cnear, hCnear, hnear⟩ := uct_pos_floor_dual_near U Sw
  refine ⟨min cabs cU, lt_min hcabs hcU, fun K hK => ?_⟩
  have hKst : Kst0 ≤ K := (le_max_left _ _).trans hK
  have hKf' : Kf ≤ K := (le_max_right _ _).trans hK
  have hK1 : 1 ≤ K := hKst0.trans hKst
  obtain ⟨c1, hc1⟩ := hmainU K hKst
  obtain ⟨c2, hc2⟩ := hfar K hK1
  obtain ⟨c3, hc3⟩ := hnear K hK1
  obtain ⟨Mw, hMw1, hMw⟩ := exists_rpow_neg_le (p := (1 / 2 : ℝ)) (by norm_num) (ε := cU / (2 * Cnear)) (by positivity)
  refine ⟨max (max (max c1 c2) (max c3 Mw)) (max 2000 (8 * K ^ 3)), fun c hc σ hσ => ?_⟩
  have hc1' : c1 ≤ c := ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hc
  have hc2' : c2 ≤ c := ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hc
  have hc3' : c3 ≤ c := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hc
  have hMw' : Mw ≤ c := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hc
  have hc2000 : 2000 ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hc8 : 8 * K ^ 3 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  have hc0 : 0 < c := by linarith
  obtain ⟨f, hf, hrep, hf0, hfv⟩ := exists_hankelEigenfn_lift (m := 4) (by norm_num) (-1 / 4) 1 1 hK1 hc2000 hc8 hσ
  refine ⟨f, hf, hrep, ?_, ?_⟩
  · intro ξ hξ hSU
    obtain ⟨hA1, hA2⟩ := hc1 c ξ hc1' hξ hSU
    have hrepre : c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * f (c * ξ) =
        (iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ).re + σ * (iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ).re := by
      have := congrArg Complex.re (hrep ξ hξ)
      simpa [Complex.re_ofReal_mul] using this
    have hMre : (((ξ : ℂ) * iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ)).re = ξ * (iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ).re :=
      Complex.re_ofReal_mul _ _
    have hDre : |ξ * (iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ).re| ≤ ‖(ξ : ℂ) * iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ‖ := by
      have := Complex.abs_re_le_norm ((ξ : ℂ) * iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ)
      rwa [Complex.re_ofReal_mul] at this
    have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
    have hsplit : ξ * (c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * f (c * ξ)) =
        ξ * (iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ).re + σ * (ξ * (iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ).re) := by
      rw [hrepre]; ring
    have hσD : |σ * (ξ * (iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ).re)| ≤ ‖(ξ : ℂ) * iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ‖ := by
      rw [abs_mul, hσ1, one_mul]; exact hDre
    rw [hMre] at hA1 hA2
    have hmaxp : 0 ≤ max (hbS c ξ) 0 := le_max_right _ _
    have hp1 : (1 + max (hbS c ξ) 0) ^ (-(3 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have hcf : min cabs cU ≤ cabs := min_le_left _ _
    have hcf' : min cabs cU ≤ cU := min_le_right _ _
    by_cases hS : hbS c ξ ≤ Sw
    · have h1 := hA2 hS
      have hd := hc3 c ξ hc3' hξ hSU hS
      have hMw2 := hMw c hMw'
      have hK4 : K ^ (-(4 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hK1 (by norm_num)
      have hdd : ‖(ξ : ℂ) * iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ‖ ≤ cU / 2 := by
        refine hd.trans ?_
        have hc12 : 0 ≤ c ^ (-(1 / 2 : ℝ)) := by positivity
        calc Cnear * K ^ (-(4 : ℝ)) * c ^ (-(1 / 2 : ℝ)) ≤ Cnear * 1 * c ^ (-(1 / 2 : ℝ)) := by gcongr
          _ ≤ Cnear * (cU / (2 * Cnear)) := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hMw2 hCnear.le
          _ = cU / 2 := by field_simp
      have : 1 / 2 * min cabs cU * (1 + max (hbS c ξ) 0) ^ (-(3 / 2 : ℝ)) ≤ 1 / 2 * min cabs cU * 1 :=
        mul_le_mul_of_nonneg_left hp1 (by have := lt_min hcabs hcU; positivity)
      have habs := (abs_le.mp hσD).1
      linarith
    · have hS' := not_le.mp hS
      have h1 := hA1 hS'
      have hd := hc2 c ξ hc2' hξ (by linarith)
      have hL : 0 < Real.log (Real.pi ^ 2 * ξ) := by
        have := log_eq_hbS (ξ := ξ) hc0
        have hSp : 0 < hbS c ξ := by linarith
        rw [this]
        exact mul_pos (mul_pos (by positivity) (pow_pos (liftEps_pos hc0) 2)) hSp
      have hSpos : 0 < hbS c ξ := by linarith
      have hmin : min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) ≤
          Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := min_le_right _ _
      have hcL : c⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) = (Real.pi ^ 2 * hbS c ξ) ^ (-(3 / 2 : ℝ)) :=
        inv_mul_log_rpow hc0 hSpos
      have hpi32 : (Real.pi ^ 2 * hbS c ξ) ^ (-(3 / 2 : ℝ)) = (Real.pi ^ 3)⁻¹ * hbS c ξ ^ (-(3 / 2 : ℝ)) := by
        rw [Real.mul_rpow (by positivity) hSpos.le]
        congr 1
        rw [show (Real.pi ^ 2 : ℝ) = Real.pi ^ (2 : ℝ) by norm_cast, ← Real.rpow_mul hpi.le,
          show (2 : ℝ) * (-(3 / 2)) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hpi.le, Real.rpow_natCast]
      have hKf2 := hKf K hKf'
      have hSr : 0 < hbS c ξ ^ (-(3 / 2 : ℝ)) := by positivity
      have hdd : ‖(ξ : ℂ) * iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ‖ ≤ cabs / 2 * hbS c ξ ^ (-(3 / 2 : ℝ)) := by
        refine hd.trans ?_
        have hc' : 0 < c⁻¹ := inv_pos.mpr hc0
        calc Cfar * K ^ (-(4 : ℝ)) * c⁻¹ * min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)))
            ≤ Cfar * K ^ (-(4 : ℝ)) * c⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by gcongr
          _ = Cfar * K ^ (-(4 : ℝ)) * ((Real.pi ^ 3)⁻¹ * hbS c ξ ^ (-(3 / 2 : ℝ))) := by rw [mul_assoc, hcL, hpi32]
          _ ≤ Cfar * (cabs * Real.pi ^ 3 / (2 * Cfar)) * ((Real.pi ^ 3)⁻¹ * hbS c ξ ^ (-(3 / 2 : ℝ))) := by gcongr
          _ = cabs / 2 * hbS c ξ ^ (-(3 / 2 : ℝ)) := by field_simp
      have hpow : (1 + max (hbS c ξ) 0) ^ (-(3 / 2 : ℝ)) ≤ hbS c ξ ^ (-(3 / 2 : ℝ)) := by
        rw [max_eq_left hSpos.le]
        exact Real.rpow_le_rpow_of_nonpos hSpos (by linarith) (by norm_num)
      have : 1 / 2 * min cabs cU * (1 + max (hbS c ξ) 0) ^ (-(3 / 2 : ℝ)) ≤ 1 / 2 * cabs * hbS c ξ ^ (-(3 / 2 : ℝ)) := by
        have h5 : 1 / 2 * min cabs cU ≤ 1 / 2 * cabs := by linarith
        have hp0 : 0 ≤ (1 + max (hbS c ξ) 0) ^ (-(3 / 2 : ℝ)) := by positivity
        calc 1 / 2 * min cabs cU * (1 + max (hbS c ξ) 0) ^ (-(3 / 2 : ℝ)) ≤ 1 / 2 * cabs * (1 + max (hbS c ξ) 0) ^ (-(3 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right h5 hp0
          _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
      have habs := (abs_le.mp hσD).1
      linarith
  · -- value at the origin
    have hX := hasU2_airySeedU2 (-1 / 4) 1 1
    have hδ0 : 0 ≤ ceBeta1 * K * liftEps c / 2 := by have := ceBeta1_pos; have := liftEps_pos hc0; positivity
    have h0 := liftSymbol_zero_eq hX (ceBeta1 * K * liftEps c / 2) 4
    have hint : ∫ u : ℝ, uctSpos u = 1 + |airyDerivFirstZero| := uct_pos_floor_one.2.2.1
    have hW : ‖liftSymbol uctSpos (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖ ≤ Cv * c ^ (-(5 / 6 : ℝ)) := by
      unfold liftSymbol
      rw [norm_mul]
      have hm := norm_liftMultiplier_le_one hδ0 4 (w := ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ)) (by simpa using (Real.rpow_pos_of_pos hc0 _).le)
      have he := airyTwistedLaplaceC_edge_bound (X := uctSpos) hCv.le hrhp hc0
      calc _ ≤ 1 * (Cv * c ^ (-(5 / 6 : ℝ))) := mul_le_mul hm he (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
    have e : (((σ * f 0 - ceK * (1 + |airyDerivFirstZero|) : ℝ)) : ℂ) = (σ : ℂ) * liftSymbol uctSpos (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) := by
      have h1 : ((f 0 : ℝ) : ℂ) = liftSymbol uctSpos (ceBeta1 * K * liftEps c / 2) 4 (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) +
          (σ : ℂ) * liftSymbol uctSpos (ceBeta1 * K * liftEps c / 2) 4 0 := hfv
      rw [h0, hint] at h1
      have h2 : ((σ : ℝ) : ℂ) * ((σ : ℝ) : ℂ) = 1 := by exact_mod_cast hσ2
      push_cast
      rw [h1]
      push_cast
      linear_combination (↑ceK * (1 + ↑|airyDerivFirstZero|)) * h2
    have := congrArg norm e
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs] at this
    have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
    rw [hσ1, one_mul] at this
    rw [this]; exact hW


/-- **`uct:pos-floor` (2), main-edge floor and reflected-edge bounds, in the form of the paper** (`(uct:pos-main-lb)`,
`(uct:pos-dual-ub)`): with `m = 4`, `δ₀ = β₁ K ε / 2`, `S_eff = hbS c ξ`, `ξ I_main[S_pos] ≥ c_fl (1 + S_eff⁺)^{-3/2}` for all `S_eff ≥ -U`,
`|ξ I_dual| ≤ C_U K^{-4} c^{-1/2}` on `-U ≤ S_eff ≤ 100` and `|ξ I_dual| ≤ C K^{-4} c^{-1} min(L^{-1/4}, L^{-3/2})` for `S_eff ≥ 1`
(`I_main` is complex in Lean; the floor is for its real part).  `K_*` and `C` are absolute, `c_fl`, `C_U` depend on `U` only
(`c_fl` not on `K`), `c₀` on `K, U`. -/
theorem uct_pos_floor_main :
    ∃ Kst : ℝ, 1 ≤ Kst ∧ ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U → ∃ cfl CU : ℝ, 0 < cfl ∧ 0 < CU ∧ ∀ K : ℝ, Kst ≤ K → ∃ c0 : ℝ,
      ∀ c ξ : ℝ, c0 ≤ c → 0 < ξ → -U ≤ hbS c ξ →
        cfl * (1 + max (hbS c ξ) 0) ^ (-(3 / 2 : ℝ)) ≤ (ξ * iMain uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ).re ∧
        (hbS c ξ ≤ 100 → ‖(ξ : ℂ) * iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ‖ ≤ CU * K ^ (-(4 : ℝ)) * c ^ (-(1 / 2 : ℝ))) ∧
        (1 ≤ hbS c ξ → ‖(ξ : ℂ) * iDual uctSpos (ceBeta1 * K * liftEps c / 2) 4 c ξ‖ ≤
          C * K ^ (-(4 : ℝ)) * c⁻¹ * min (Real.log (Real.pi ^ 2 * ξ) ^ (-(1 / 4 : ℝ))) (Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)))) := by
  obtain ⟨Kst0, hKst0, cabs, hcabs, Sw, hSw, hmain⟩ := uct_pos_floor_main_lower
  obtain ⟨Cfar, hCfar, hfar⟩ := uct_pos_floor_dual_far
  refine ⟨Kst0, hKst0, Cfar, hCfar, fun U hU => ?_⟩
  obtain ⟨cU, hcU, hmainU⟩ := hmain U hU
  obtain ⟨Cnear, hCnear, hnear⟩ := uct_pos_floor_dual_near U 100
  refine ⟨min cabs cU, Cnear, lt_min hcabs hcU, hCnear, fun K hK => ?_⟩
  have hK1 : 1 ≤ K := hKst0.trans hK
  obtain ⟨c1, hc1⟩ := hmainU K hK
  obtain ⟨c2, hc2⟩ := hfar K hK1
  obtain ⟨c3, hc3⟩ := hnear K hK1
  refine ⟨max (max c1 c2) c3, fun c ξ hc hξ hSU => ⟨?_, fun hS => ?_, fun hS => ?_⟩⟩
  · obtain ⟨hA1, hA2⟩ := hc1 c ξ ((le_max_left _ _).trans ((le_max_left _ _).trans hc)) hξ hSU
    have hmaxp : 0 ≤ max (hbS c ξ) 0 := le_max_right _ _
    by_cases hS : hbS c ξ ≤ Sw
    · have h1 := hA2 hS
      have hp1 : (1 + max (hbS c ξ) 0) ^ (-(3 / 2 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
      have : min cabs cU * (1 + max (hbS c ξ) 0) ^ (-(3 / 2 : ℝ)) ≤ min cabs cU * 1 :=
        mul_le_mul_of_nonneg_left hp1 (lt_min hcabs hcU).le
      linarith [min_le_right cabs cU]
    · have hS' := not_le.mp hS
      have h1 := hA1 hS'
      have hSpos : 0 < hbS c ξ := by linarith
      have hpow : (1 + max (hbS c ξ) 0) ^ (-(3 / 2 : ℝ)) ≤ hbS c ξ ^ (-(3 / 2 : ℝ)) := by
        rw [max_eq_left hSpos.le]
        exact Real.rpow_le_rpow_of_nonpos hSpos (by linarith) (by norm_num)
      have hp0 : 0 ≤ (1 + max (hbS c ξ) 0) ^ (-(3 / 2 : ℝ)) := by positivity
      calc min cabs cU * (1 + max (hbS c ξ) 0) ^ (-(3 / 2 : ℝ)) ≤ cabs * (1 + max (hbS c ξ) 0) ^ (-(3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hp0
        _ ≤ cabs * hbS c ξ ^ (-(3 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hpow hcabs.le
        _ ≤ _ := h1
  · exact hc3 c ξ ((le_max_right _ _).trans hc) hξ hSU hS
  · exact hc2 c ξ (((le_max_right c1 c2).trans (le_max_left _ c3)).trans hc) hξ hS


/-- info: 'FormalResearch.SignUncertainty.uct_pos_floor_main_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_pos_floor_main_lower

/-- info: 'FormalResearch.SignUncertainty.uct_pos_floor_dual_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_pos_floor_dual_far

/-- info: 'FormalResearch.SignUncertainty.uct_pos_floor_dual_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_pos_floor_dual_near

/-- info: 'FormalResearch.SignUncertainty.uct_pos_floor_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_pos_floor_lift

/-- info: 'FormalResearch.SignUncertainty.uct_pos_floor_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_pos_floor_main

end FormalResearch.SignUncertainty
