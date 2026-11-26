module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroBump
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroRegionOne
public import FormalResearch.ModularBootstrap.Upper.Positivity.RegionOne

/-!
# Region I for the bumped two-zero comb at every weight (`ut:T2`, `ut:III`, `fw:e1.3`, `fw:e3.3`)

Source: `upper_transfer.tex`, Theorem T2 (`ut:T2`), Region I, and Proposition III (`ut:III`) Region I at `w > 1`.

* `twoZero_regionOne_a_lower`, `twoZero_regionOne_b_lower`: the lower bounds that Region I(a), I(b) of `TwoZeroRegionOne`
  prove before comparing with the transform, for an arbitrary threshold `K₁`:
  `K₁ √c' < Re (sech² T_{χ(p)} B₁)(x) e^{c'L(x)}` on `χ(q) + C λ c'^{-7/6} ≤ x ≤ ξ_* + λ Σ₀` and on
  `ξ_* + λ Σ₀ ≤ x ≤ ξ_* + c'^{-2/5}` (`twoZero_regionOne_a`, `twoZero_regionOne_b` are these with `K₁ = K √(2/ξ_*)`
  and `pos_of_lower_hankel`; recommended re-derivation in place);
* `re_profile_bump`: at real `x ≥ 0`, `Re (sech² T_{χ(p)} B₁^{(p)})(x) = R_bump(x) · Re (sech² T_{χ(p)} B₁)(x)` with
  `1 ≤ R_bump ≤ C_p`, `R_bump ≤ 1 + C/c'` on `x ≤ ξ_* + r_p` (`fw:e3.3`), for every cut `N' ≥ n + 2`;
* `twoZeroBump_regionOne`: Region I at every order `p`: `2 g_w(c' x²/3) > 0` for
  `χ(q) + C λ c'^{-7/6} ≤ x ≤ ξ_* + c'^{-2/5}` (the bump only raises the real value; the order-`p` transform is bounded by
  `twoZeroBump_globalP`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.Upper.Hankel FormalResearch.ModularBootstrap.Upper.Saddle
  FormalResearch.ModularBootstrap.Upper.Bump FormalResearch.ModularBootstrap.Upper.Ramped
  FormalResearch.ModularBootstrap.Upper.Positivity

/-! ### 1. The lower bounds of Region I -/

/-- **Region I(a)** (`ut:T2`, `eq:ut:T2-Ia`): for every `Σ₀` there is `C > 0` such that for `c'` large, `d ∈ 𝒦` and
`χ(q) + C λ c'^{-7/6} ≤ x ≤ ξ_* + λ Σ₀`, `2 g(c'x²/3) > 0` (`2g = Re h₂ - Re ĥ₂`).  The uniform Lemma R with
`T_{χ(q)}/(σ - σ_q)` divided out, times `T_{χ(p)} ≥ c₂ λ`, beats `SD_G` once `σ - σ_q ≥ C c'^{-7/6}`
(`t - t(q) = O(c'^{-5/6})`). -/
theorem twoZero_regionOne_a_lower {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : TwoZeroDesign.IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) (Sg0 K₁ : ℝ) (hK₁ : 0 ≤ K₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ,
      xiStar + lambdaComb c' * d.sigmaF + C * lambdaComb c' * c' ^ (-(7 / 6 : ℝ)) ≤ x →
      x ≤ xiStar + lambdaComb c' * Sg0 →
      xiStar / 2 ≤ x ∧ K₁ * √c' <
        (sechSqProfile (x : ℂ) * d.twoZeroComb c' (x : ℂ)).re * Real.exp (c' * edgeL x) := by
  obtain ⟨c₂, hc₂, hT⟩ := TwoZeroDesign.twoZeroT_ge_window hK hA Sg0
  obtain ⟨w0, hw0, C₀, hR⟩ := TwoZeroDesign.lemma_R_lower_two_unif hK hA Sg0
  obtain ⟨cK, hcK, hlK⟩ := lambda_mul_normK_two
  obtain ⟨M, E, hM, hE, hb⟩ := hK.exists_comb_bounds hA
  have hξ := xiStar_pos
  obtain ⟨A, hA0⟩ : ∃ A : ℝ, A = K₁ := ⟨_, rfl⟩
  have hApos : 0 ≤ A := by rw [hA0]; exact hK₁
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (A + 1) / (c₂ * w0 * cK) := ⟨_, rfl⟩
  have hCpos : 0 < C := by rw [hC]; positivity
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [hT, eventually_ge_atTop C₀, TwoZeroDesign.eventually_lambda_small M,
    eventually_gt_atTop (0 : ℝ)] with c' hTc hc0 ⟨hl, hlM⟩ hcpos d hd x hx1 hx2
  set σ : ℝ := (x - xiStar) / lambdaComb c' with hσ
  have hxσ : xiStar + lambdaComb c' * σ = x := by rw [hσ]; field_simp; ring
  have hc76 : 0 < c' ^ (-(7 / 6 : ℝ)) := Real.rpow_pos_of_pos hcpos _
  have hgap : C * c' ^ (-(7 / 6 : ℝ)) ≤ σ - d.sigmaF := by
    have h1 : C * lambdaComb c' * c' ^ (-(7 / 6 : ℝ)) ≤ lambdaComb c' * (σ - d.sigmaF) := by
      have : lambdaComb c' * (σ - d.sigmaF) = x - xiStar - lambdaComb c' * d.sigmaF := by
        rw [mul_sub, ← hxσ]; ring
      rw [this]; linarith
    have h2 : lambdaComb c' * (C * c' ^ (-(7 / 6 : ℝ))) ≤ lambdaComb c' * (σ - d.sigmaF) := by
      linarith
    exact le_of_mul_le_mul_left h2 hl
  have hσF : d.sigmaF < σ := lt_of_lt_of_le (by positivity) hgap |> fun h => by linarith
  have hσS : σ ≤ Sg0 := by
    have : lambdaComb c' * σ ≤ lambdaComb c' * Sg0 := by linarith
    exact le_of_mul_le_mul_left this hl
  have hσFM : |d.sigmaF| ≤ M := by
    have := (hb d hd).1 2 le_rfl (by omega)
    simpa [TwoZeroDesign.sigmaSeq] using this
  have hxhalf : xiStar / 2 ≤ x := by
    have h1 : 0 ≤ C * lambdaComb c' * c' ^ (-(7 / 6 : ℝ)) := by positivity
    have h2 : -(lambdaComb c' * M) ≤ lambdaComb c' * d.sigmaF := by
      have := mul_le_mul_of_nonneg_left (neg_le_of_abs_le hσFM) hl.le
      linarith
    linarith
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hxhalf
  have hRlow := hR hc0 d hd σ hσF hσS
  rw [hxσ, exp_slitL_eq_edgeL hx0.le] at hRlow
  have hTlow := hTc d hd σ hσF.le hσS
  rw [hxσ] at hTlow
  have hK' := windowNormKTilde_pos 2 hcpos
  have hs : 0 < σ - d.sigmaF := sub_pos.2 hσF
  have hEpos := Real.exp_pos (c' * edgeL x)
  have hre := d.re_profile_eq c' x
  rw [d.re_sech_comb_eq] at hre
  have hTpos : 0 ≤ tFac (d.chiP c') x := (mul_pos hc₂ hl).le.trans hTlow
  have hQ : c₂ * lambdaComb c' * (windowNormKTilde 2 c' * w0 * (σ - d.sigmaF)) ≤
      (sechSqProfile (x : ℂ) * d.twoZeroComb c' (x : ℂ)).re * Real.exp (c' * edgeL x) := by
    rw [hre]
    have h0 : 0 ≤ windowNormKTilde 2 c' * w0 * (σ - d.sigmaF) := by positivity
    calc c₂ * lambdaComb c' * (windowNormKTilde 2 c' * w0 * (σ - d.sigmaF))
        ≤ tFac (d.chiP c') x * (windowNormKTilde 2 c' * w0 * (σ - d.sigmaF)) :=
          mul_le_mul_of_nonneg_right hTlow h0
      _ ≤ tFac (d.chiP c') x * (modifiedH0 2 (n + 2) d.toModified c' x * Real.exp (c' * edgeL x)) :=
          mul_le_mul_of_nonneg_left hRlow hTpos
      _ = _ := by ring
  have hsqrt : c' ^ (5 / 3 : ℝ) * c' ^ (-(7 / 6 : ℝ)) = √c' := by
    rw [← Real.rpow_add hcpos, Real.sqrt_eq_rpow]; norm_num
  have hbig : K₁ * √c' < c₂ * lambdaComb c' * (windowNormKTilde 2 c' * w0 * (σ - d.sigmaF)) := by
    have hsc : 0 < √c' := Real.sqrt_pos.2 hcpos
    have e1 : c₂ * lambdaComb c' * (windowNormKTilde 2 c' * w0 * (σ - d.sigmaF)) =
        c₂ * w0 * (cK * c' ^ (5 / 3 : ℝ)) * (σ - d.sigmaF) := by
      rw [← hlK hcpos]; ring
    rw [e1]
    have e2 : c₂ * w0 * (cK * c' ^ (5 / 3 : ℝ)) * (C * c' ^ (-(7 / 6 : ℝ))) = (A + 1) * √c' := by
      rw [← hsqrt, hC]
      field_simp
    have hpos : 0 < c₂ * w0 * (cK * c' ^ (5 / 3 : ℝ)) := by
      have := Real.rpow_pos_of_pos hcpos (5 / 3 : ℝ); positivity
    calc K₁ * √c' = A * √c' := by rw [hA0]
      _ < (A + 1) * √c' := by nlinarith
      _ = c₂ * w0 * (cK * c' ^ (5 / 3 : ℝ)) * (C * c' ^ (-(7 / 6 : ℝ))) := e2.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hgap hpos.le
  exact ⟨hxhalf, lt_of_lt_of_le hbig hQ⟩

/-- **Region I(b)** (`ut:T2`, `eq:ut:T2-Ib`): there is `Σ₀ > 0` such that for `c'` large, `d ∈ 𝒦` and
`ξ_* + λΣ₀ ≤ x ≤ ξ_* + c'^{-2/5}`, `2 g(c'x²/3) > 0`.  `Σ₀` is chosen so that `lemma_P_b` gives `B₁ ≥ ½ B_ref^{(2)}`, `x` lies
in a cell `n ≥ max(N_ov, 3)` of `K5` (`designProfile_overshoot_lower`, `2n₁ = 7/2`) and `x - χ(p) ≥ ½ (x - ξ_*)`
(`twoZeroT_ge_beyond`): `Re h₂ e^{c'L} ≥ c (x - ξ_*)^{-5/2} ≥ c c' ≫ √c'`. -/
theorem twoZero_regionOne_b_lower {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : TwoZeroDesign.IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) (K₁ : ℝ) :
    ∃ Sg0 : ℝ, 0 < Sg0 ∧ ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ,
      xiStar + lambdaComb c' * Sg0 ≤ x → x ≤ xiStar + c' ^ (-(2 / 5 : ℝ)) →
      xiStar / 2 ≤ x ∧ K₁ * √c' <
        (sechSqProfile (x : ℂ) * d.twoZeroComb c' (x : ℂ)).re * Real.exp (c' * edgeL x) := by
  obtain ⟨M, E, hM, hE, hb⟩ := hK.exists_comb_bounds hA
  obtain ⟨Sgb, cc, hSgb, hcc, hov⟩ := designProfile_overshoot_lower 2 (n + 2) (by norm_num) (by omega) M E
  obtain ⟨c₁, Sg1, hc₁, hSg1, hT⟩ := TwoZeroDesign.twoZeroT_ge_beyond hK
  have hξ := xiStar_pos
  have hπ := Real.pi_pos
  refine ⟨max Sgb Sg1, lt_of_lt_of_le hSgb (le_max_left _ _), ?_⟩
  obtain ⟨κ₂, hκ₂⟩ : ∃ κ₂ : ℝ, κ₂ = c₁ * cc * ((2 / π) * (2 / π) ^ (5 / 2 : ℝ)) := ⟨_, rfl⟩
  have hκ₂pos : 0 < κ₂ := by rw [hκ₂]; positivity
  obtain ⟨A, hA0⟩ : ∃ A : ℝ, A = K₁ := ⟨_, rfl⟩
  have hbigc : ∀ᶠ c' : ℝ in atTop, A / κ₂ < c' ^ (1 / 2 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_gt_atTop _
  filter_upwards [hov, hT, hbigc, eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (1 : ℝ)] with
    c' hovc hTc hbc hcpos hc1 d hd x hx1 hx2
  have hl : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hcpos) _
  have hu1 : c' ^ (-(2 / 5 : ℝ)) ≤ 1 := rpow_neg_two_fifths_le_one hc1
  have hSgb' : xiStar + lambdaComb c' * Sgb ≤ x :=
    le_trans (by have := mul_le_mul_of_nonneg_left (le_max_left Sgb Sg1) hl.le; linarith) hx1
  have hSg1' : xiStar + lambdaComb c' * Sg1 ≤ x :=
    le_trans (by have := mul_le_mul_of_nonneg_left (le_max_right Sgb Sg1) hl.le; linarith) hx1
  have hupos : 0 < x - xiStar := by
    have := mul_pos hl (lt_of_lt_of_le hSgb (le_max_left Sgb Sg1))
    have h2 := mul_le_mul_of_nonneg_left (le_max_left Sgb Sg1) hl.le
    linarith
  have hx0 : 0 < x := by linarith
  have huup : x - xiStar ≤ c' ^ (-(2 / 5 : ℝ)) := by linarith
  obtain ⟨hσ, hε⟩ := TwoZeroDesign.comb_family_bounds hl (hb d hd)
  have hov' := hovc d.sigmaSeq (fun k => lambdaComb c' * d.epsHatSite k)
    (fun k hk hkN => hσ k hk hkN) (fun k hk hkN => hε k hk hkN) x hSgb' hx2
  have hTlow := hTc d hd x hSg1' (by linarith)
  have hre := d.re_profile_eq c' x
  have hT0 : 0 ≤ tFac (d.chiP c') x := (mul_nonneg hc₁.le hupos.le).trans hTlow
  have hn1 : 2 * n1Comb 2 = (7 / 2 : ℝ) := by unfold n1Comb; norm_num
  rw [hn1] at hov'
  have hEpos := Real.exp_pos (c' * edgeL x)
  have hPi : 0 < 2 / (π * (x - xiStar)) := by positivity
  have h52 := pow_overshoot_gen (a := 5 / 2) hcpos hupos huup (by norm_num)
  rw [show (2 / 5 : ℝ) * (5 / 2) = 1 by norm_num, Real.rpow_one] at h52
  have hsplit : (2 / (π * (x - xiStar))) ^ (7 / 2 : ℝ) =
      (2 / (π * (x - xiStar))) ^ (5 / 2 : ℝ) * (2 / (π * (x - xiStar))) := by
    rw [← Real.rpow_add_one hPi.ne' (5 / 2 : ℝ)]; norm_num
  have hQ : κ₂ * c' ≤ (sechSqProfile (x : ℂ) * d.twoZeroComb c' (x : ℂ)).re *
      Real.exp (c' * edgeL x) := by
    rw [hre]
    have hP0 : 0 ≤ cc * (2 / (π * (x - xiStar))) ^ (7 / 2 : ℝ) :=
      mul_nonneg hcc.le (Real.rpow_nonneg hPi.le _)
    have hPe : (sechSqProfile (x : ℂ) * d.comb c' (x : ℂ)).re * Real.exp (c' * edgeL x) =
        (designProfile c' 2 (n + 2) (1 / 4) d.sigmaSeq (fun k => lambdaComb c' * d.epsHatSite k)
          (x : ℂ)).re * Real.exp (c' * edgeL x) := rfl
    calc κ₂ * c' ≤ c₁ * (x - xiStar) * (cc * (2 / (π * (x - xiStar))) ^ (7 / 2 : ℝ)) := by
          rw [hsplit, hκ₂]
          have e : c₁ * (x - xiStar) * (cc * ((2 / (π * (x - xiStar))) ^ (5 / 2 : ℝ) *
              (2 / (π * (x - xiStar))))) = c₁ * cc * (2 / π) * (2 / (π * (x - xiStar))) ^ (5 / 2 : ℝ) := by
            field_simp
          rw [e]
          have h1 : c₁ * cc * (2 / π) * ((2 / π) ^ (5 / 2 : ℝ) * c') ≤
              c₁ * cc * (2 / π) * (2 / (π * (x - xiStar))) ^ (5 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left h52 (by positivity)
          nlinarith [h1]
      _ ≤ tFac (d.chiP c') x * (cc * (2 / (π * (x - xiStar))) ^ (7 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hTlow hP0
      _ ≤ tFac (d.chiP c') x * ((designProfile c' 2 (n + 2) (1 / 4) d.sigmaSeq
            (fun k => lambdaComb c' * d.epsHatSite k) (x : ℂ)).re * Real.exp (c' * edgeL x)) :=
          mul_le_mul_of_nonneg_left hov' hT0
      _ = _ := by rw [← hPe]; ring
  have hbig : K₁ * √c' < κ₂ * c' := by
    have hsc : 0 < √c' := Real.sqrt_pos.2 hcpos
    have h1 : A < κ₂ * √c' := by
      rw [← Real.sqrt_eq_rpow] at hbc
      rwa [div_lt_iff₀ hκ₂pos, mul_comm] at hbc
    have h2 : c' = √c' * √c' := (Real.mul_self_sqrt hcpos.le).symm
    calc K₁ * √c' = A * √c' := by rw [hA0]
      _ < κ₂ * √c' * √c' := mul_lt_mul_of_pos_right h1 hsc
      _ = κ₂ * c' := by rw [mul_assoc, ← h2]
  exact ⟨by linarith, lt_of_lt_of_le hbig hQ⟩


/-! ### 2. The bump on the real axis -/

open TwoZeroDesign

/-- **`R_bump` for the two-zero profile** (`fw:e3.3`): for `c` large, every `d`, cut `N' ≥ n + 2` and `x ≥ 0`,
`Re (sech² T_{χ(p)} B₁^{(p)})(x) = R · Re (sech² T_{χ(p)} B₁)(x)` with `1 ≤ R ≤ C_p` and `R ≤ 1 + C'/c` for
`x ≤ ξ_* + r_p`. -/
theorem re_profile_bump (bd : BumpData) {n : ℕ} :
    ∃ Cp C' : ℝ, ∀ᶠ c in atTop, ∀ d : TwoZeroDesign n, ∀ N' : ℕ, n + 2 ≤ N' → ∀ x : ℝ, 0 ≤ x →
      ∃ R : ℝ, 1 ≤ R ∧ R ≤ Cp ∧ (x ≤ xiStar + bd.r → R ≤ 1 + C' / c) ∧
        (sechSqProfile (x : ℂ) * d.bumpComb bd c N' (x : ℂ)).re =
          R * (sechSqProfile (x : ℂ) * d.twoZeroComb c (x : ℂ)).re := by
  refine ⟨bumpC bd (1 / 4), bumpC' bd (1 / 4), ?_⟩
  filter_upwards [bump_lemma bd (η₀ := 1 / 4) (by norm_num) le_rfl] with c hb d N' hN' x hx
  obtain ⟨hc, hbm, h1, h2, h3⟩ := hb 2 (n + 2) N' d.sigmaSeq (fun k => lambdaComb c * d.epsHatSite k) x
    (by omega) hN' hx
  refine ⟨_, h1, h2, h3, ?_⟩
  have e1 : d.bumpComb bd c N' (x : ℂ) = (((tFac (d.chiP c) x *
      (bumpFactor bd c (1 / 4) (n + 2) N' x *
        combReal c 2 (n + 2) (1 / 4) d.sigmaSeq (fun k => lambdaComb c * d.epsHatSite k) x)) : ℝ) : ℂ) := by
    unfold bumpComb bumpedBase
    rw [hbm, tFac_eq]; push_cast; ring
  have e2 : d.twoZeroComb c (x : ℂ) = (((tFac (d.chiP c) x *
        combReal c 2 (n + 2) (1 / 4) d.sigmaSeq (fun k => lambdaComb c * d.epsHatSite k) x) : ℝ) : ℂ) := by
    unfold twoZeroComb comb
    rw [hc, tFac_eq]; push_cast; ring
  rw [e1, e2, Upper.Positivity.sechSqProfile_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.ofReal_re]
  ring

/-! ### 3. Region I at every order -/

/-- **Region I at every weight** (`ut:T2`, `ut:III`; `fw:e1.3`, `fw:e3.3`): for every order `p` there is `C > 0` such that
for `c` large, `d ∈ 𝒦`, every cut `N' ≥ n + 2` and every real `x` with
`χ(q) + C λ c^{-7/6} ≤ x ≤ ξ_* + c^{-2/5}`, `2 g_w(c x²/3) = Re h₂^{(p)}(x) - Re (𝓗_{p+1} h₂^{(p)})(c x²/3) > 0`. -/
theorem twoZeroBump_regionOne (bd : BumpData) (p : ℕ) {n : ℕ} {𝒦 : Set (TwoZeroDesign n)}
    (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' → ∀ x : ℝ,
      xiStar + lambdaComb c * d.sigmaF + C * lambdaComb c * c ^ (-(7 / 6 : ℝ)) ≤ x →
      x ≤ xiStar + c ^ (-(2 / 5 : ℝ)) →
      0 < (sechSqProfile (x : ℂ) * d.bumpComb bd c N' (x : ℂ) -
        edgeHankelP p c (fun b => sechSqProfile b * d.bumpComb bd c N' b) (c * x ^ 2 / 3)).re := by
  obtain ⟨Kg, hKg0, hKg⟩ := twoZeroBump_globalP bd p hK hA
  have hξ := xiStar_pos
  obtain ⟨A, hA0⟩ : ∃ A : ℝ, A = Kg * (2 / xiStar) ^ p * √(2 / xiStar) := ⟨_, rfl⟩
  have hApos : 0 ≤ A := by rw [hA0]; positivity
  obtain ⟨Sg0, hSg0, hb⟩ := twoZero_regionOne_b_lower hK hA A
  obtain ⟨C, hC, ha⟩ := twoZero_regionOne_a_lower hK hA Sg0 A hApos
  obtain ⟨Cp, C', hRb⟩ := re_profile_bump (n := n) bd
  refine ⟨C, hC, ?_⟩
  filter_upwards [ha, hb, hKg, hRb, eventually_ge_atTop (3 / (2 * π * xiStar)),
    eventually_gt_atTop (0 : ℝ)] with c hac hbc hKc hR hc3 hcpos d hd N' hN' x hx1 hx2
  have hlow : xiStar / 2 ≤ x ∧ A * √c <
      (sechSqProfile (x : ℂ) * d.twoZeroComb c (x : ℂ)).re * Real.exp (c * edgeL x) := by
    by_cases h : x ≤ xiStar + lambdaComb c * Sg0
    · exact hac d hd x hx1 h
    · exact hbc d hd x (not_le.1 h).le hx2
  obtain ⟨hxhalf, hlow⟩ := hlow
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hxhalf
  obtain ⟨R, hR1, -, -, hRe⟩ := hR d N' hN' x hx0.le
  have hE := Real.exp_pos (c * edgeL x)
  have hQ : A * √c < (sechSqProfile (x : ℂ) * d.bumpComb bd c N' (x : ℂ)).re * Real.exp (c * edgeL x) := by
    rw [hRe]
    have hre : 0 ≤ (sechSqProfile (x : ℂ) * d.twoZeroComb c (x : ℂ)).re := by
      by_contra hneg
      push Not at hneg
      have := mul_neg_of_neg_of_pos hneg hE
      have : 0 ≤ A * √c := by positivity
      linarith
    calc A * √c < (sechSqProfile (x : ℂ) * d.twoZeroComb c (x : ℂ)).re * Real.exp (c * edgeL x) := hlow
      _ ≤ (R * (sechSqProfile (x : ℂ) * d.twoZeroComb c (x : ℂ)).re) * Real.exp (c * edgeL x) := by
          gcongr
          nlinarith
  have hpi := Real.pi_pos
  have hk : 1 ≤ 4 * π * c * x / 3 := by
    have h1 : 3 / (2 * π * xiStar) * (2 * π * xiStar) = 3 := by field_simp
    have h2 : 3 ≤ c * (2 * π * xiStar) := by
      calc (3 : ℝ) = 3 / (2 * π * xiStar) * (2 * π * xiStar) := h1.symm
        _ ≤ c * (2 * π * xiStar) := mul_le_mul_of_nonneg_right hc3 (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hxhalf (by positivity : (0 : ℝ) ≤ 4 * π * c / 3)]
  have hglob := hKc d hd N' hN' x hx0 hk
  have hpow : (1 / x) ^ p ≤ (2 / xiStar) ^ p := by
    refine pow_le_pow_left₀ (by positivity) ?_ p
    rw [div_le_div_iff₀ hx0 hξ]
    linarith
  have hglob' : Real.exp (c * edgeL x) *
      ‖edgeHankelP p c (fun b => sechSqProfile b * d.bumpComb bd c N' b) (c * x ^ 2 / 3)‖ ≤
        (Kg * (2 / xiStar) ^ p) * √(c / x) := by
    refine hglob.trans ?_
    calc Kg * √(c / x) * (1 / x) ^ p ≤ Kg * √(c / x) * (2 / xiStar) ^ p :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring
  rw [Complex.sub_re]
  have hAeq : Kg * (2 / xiStar) ^ p * √(2 / xiStar) * √c = A * √c := by rw [hA0]
  exact pos_of_lower_hankel (Hre := (sechSqProfile (x : ℂ) * d.bumpComb bd c N' (x : ℂ)).re)
    (Q := (sechSqProfile (x : ℂ) * d.bumpComb bd c N' (x : ℂ)).re * Real.exp (c * edgeL x))
    hcpos hxhalf (by positivity) hE hglob' le_rfl (by rw [hAeq]; exact hQ)

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_regionOne_a_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_regionOne_a_lower

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_regionOne_b_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_regionOne_b_lower

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.re_profile_bump' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms re_profile_bump

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroBump_regionOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_regionOne

end FormalResearch.ModularBootstrap.TwoLevel
