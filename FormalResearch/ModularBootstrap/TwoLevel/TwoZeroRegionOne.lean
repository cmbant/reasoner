module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroCombK7
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroRegionOneUnif
public import FormalResearch.ModularBootstrap.Upper.Positivity.RegionOne

/-!
# Region I for the two-zero comb: the window `ut:W`/`ut:R` and the overshoot `K5` at `f = 2` (`upper_transfer.tex`, `ut:T2`)

Source: `upper_transfer.tex`, Theorem T2 (`ut:T2`), paragraph "Region I".  The test is `h₂ = sech²(πb/2) B₂`,
`B₂ = T_{χ(p)} B₁` (`twoZeroComb`), `2 g = Re h₂ - Re ĥ₂` at `t = c' x²/3`, `χ(q) = ξ_* + λσ_q`.  For every compact
family `𝒦` of admissible designs and every `Σ₀`:

* `tFac_ge_sub`, `twoZeroT_ge_window`: `T_{χ(p)}(ξ_* + λσ) ≥ c₂ λ` for `σ_q ≤ σ ≤ Σ₀` (the zero `σ_p < σ_q` is separated
  from the window: `p - q ≥ c₀`), uniformly on `𝒦`;
* `twoZeroComb_global_bound`: `SD_G` for `h₂`: `e^{c'L} ‖ĥ₂‖ ≤ K √(c'/x)` (`|B₂| = 1` on `E₊`);
* `lambda_mul_normK_two`: `λ K̃_c^{(2)} = c_K c'^{5/3}`;
* `twoZero_regionOne_a` (`eq:ut:T2-Ia`): `2g > 0` for `χ(q) + C λ c'^{-7/6} ≤ x ≤ ξ_* + λ Σ₀`: the uniform Lemma R
  (`lemma_R_lower_two_unif`, with `(σ - σ_q)` divided out) times `T_{χ(p)} ≥ c₂ λ` beats `K√c'` once
  `σ - σ_q ≥ C c'^{-7/6}`;
* `twoZero_regionOne_b` (`eq:ut:T2-Ib`): `2g > 0` for `ξ_* + λΣ₀ ≤ x ≤ ξ_* + c'^{-2/5}`: the `K5` overshoot
  (`designProfile_overshoot_lower`, `2n₁ = 7/2`) times `T_{χ(p)} ≥ c (x - ξ_*)` gives `≥ c (x - ξ_*)^{-5/2} ≥ c c'`;
* `twoZero_regionOne`: the union, `2g > 0` for `χ(q) + C λ c'^{-7/6} ≤ x ≤ ξ_* + c'^{-2/5}`.

The statements spell out `2 g(c'x²/3) = Re (sech² B₂)(x) - Re ĥ₂(c'x²/3)` (`h₂ = fun b => sechSqProfile b * twoZeroComb`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Saddle FormalResearch.ModularBootstrap.Upper.Window.Tail

/-! ### 1. The real factor in the window -/

/-- `T_χ(x) ≥ c₁ (x - χ)` for `ξ_*/2 ≤ χ ≤ x ≤ χ + 1`. -/
lemma tFac_ge_sub : ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ {χ x : ℝ}, xiStar / 2 ≤ χ → χ ≤ x → x - χ ≤ 1 →
    c₁ * (x - χ) ≤ tFac χ x := by
  have hpi := Real.pi_pos
  have hξ := xiStar_pos
  set τ₀ : ℝ := Real.tanh (π * xiStar / 2) with hτ₀
  have hτ₀pos : 0 < τ₀ := tanh_pos_of_pos (by positivity)
  have hcz : 0 < Real.cosh (π / 2) := Real.cosh_pos _
  refine ⟨τ₀ * (π / 2 / Real.cosh (π / 2)), by positivity, fun {χ x} hχ hχx hx1 => ?_⟩
  have hxχ : 0 ≤ x - χ := by linarith
  unfold tFac
  have ha : (π / 2 / Real.cosh (π / 2)) * (x - χ) ≤ Real.tanh (π * (x - χ) / 2) := by
    have := tanh_ge_div_cosh (z := π * (x - χ) / 2) (z₀ := π / 2) (by positivity)
      (by nlinarith)
    refine le_trans (le_of_eq ?_) this
    ring
  have hb : τ₀ ≤ Real.tanh (π * (x + χ) / 2) := by
    refine tanh_mono_real ?_
    have : xiStar ≤ x + χ := by linarith
    nlinarith
  have hapos : 0 ≤ (π / 2 / Real.cosh (π / 2)) * (x - χ) := by positivity
  calc τ₀ * (π / 2 / Real.cosh (π / 2)) * (x - χ)
      = (π / 2 / Real.cosh (π / 2)) * (x - χ) * τ₀ := by ring
    _ ≤ Real.tanh (π * (x - χ) / 2) * Real.tanh (π * (x + χ) / 2) :=
        mul_le_mul ha hb hτ₀pos.le (hapos.trans ha)

namespace TwoZeroDesign

variable {n : ℕ}

lemma sigmaF_sub_sigmaP (d : TwoZeroDesign n) : d.sigmaF - d.sigmaP = (d.p - d.q) / kappaAiry := by
  unfold sigmaF sigmaP; ring

/-- **`T_{χ(p)}(ξ_* + λσ) ≥ c₂ λ` in the window** `σ_q ≤ σ ≤ Σ₀` (`ut:T2`, Region I): the zero `χ(p)` of the extra factor
lies to the left of the window by `λ(σ_q - σ_p) = λ (p - q)/κ ≥ λ c₀/κ`; uniform on a compact family. -/
theorem twoZeroT_ge_window {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm)
    (Sg0 : ℝ) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ σ : ℝ, d.sigmaF ≤ σ → σ ≤ Sg0 →
      c₂ * lambdaComb c' ≤ tFac (d.chiP c') (xiStar + lambdaComb c' * σ) := by
  obtain ⟨S, hS0, hS⟩ := hK.exists_sigmaP_bound
  obtain ⟨c₀, hc₀, hmar⟩ := hK.exists_margins hA
  obtain ⟨c₁, hc₁, hlow⟩ := tFac_ge_sub
  have hκ := kappaAiry_pos
  refine ⟨c₁ * (c₀ / kappaAiry), by positivity, ?_⟩
  have h1 : ∀ᶠ c' : ℝ in atTop, lambdaComb c' * (|Sg0| + S) ≤ 1 := by
    have h := tendsto_lambdaComb_atTop.mul_const (|Sg0| + S)
    rw [zero_mul] at h
    exact h.eventually_le_const one_pos
  filter_upwards [eventually_lambda_small S, h1] with c' ⟨hl, hlS⟩ hl1 d hd σ hσ1 hσ2
  have hχ := chiP_ge (hS d hd) hl hlS
  have hx : xiStar + lambdaComb c' * σ - d.chiP c' = lambdaComb c' * (σ - d.sigmaP) := by
    unfold chiP; ring
  have hgap : c₀ / kappaAiry ≤ σ - d.sigmaP := by
    have := d.sigmaF_sub_sigmaP
    have h2 : c₀ / kappaAiry ≤ (d.p - d.q) / kappaAiry :=
      div_le_div_of_nonneg_right (hmar d hd).1 hκ.le
    linarith
  have hup : σ - d.sigmaP ≤ |Sg0| + S := by
    have := (abs_le.1 (hS d hd)).2
    have h3 : σ ≤ |Sg0| := hσ2.trans (le_abs_self _)
    linarith [(abs_le.1 (hS d hd)).1]
  have hpos : 0 ≤ σ - d.sigmaP := (div_nonneg hc₀.le hκ.le).trans hgap
  have hxle : xiStar + lambdaComb c' * σ - d.chiP c' ≤ 1 := by
    rw [hx]
    calc lambdaComb c' * (σ - d.sigmaP) ≤ lambdaComb c' * (|Sg0| + S) :=
          mul_le_mul_of_nonneg_left hup hl.le
      _ ≤ 1 := hl1
  have hxge : 0 ≤ xiStar + lambdaComb c' * σ - d.chiP c' := by
    rw [hx]; exact mul_nonneg hl.le hpos
  have := hlow hχ (by linarith) hxle
  refine le_trans ?_ this
  rw [hx]
  calc c₁ * (c₀ / kappaAiry) * lambdaComb c' = c₁ * (lambdaComb c' * (c₀ / kappaAiry)) := by ring
    _ ≤ c₁ * (lambdaComb c' * (σ - d.sigmaP)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgap hl.le) hc₁.le

end TwoZeroDesign

/-! ### 2. `SD_G` for `h₂` and the normalisation -/

/-- **Lemma `SD_G` for `h₂ = sech² T_{χ(p)} B₁`** (`ut:T2`, Region I): `e^{c'L(x)} ‖ĥ₂(c'x²/3)‖ ≤ K √(c'/x)` for all
`x > 0`, uniformly on a compact family (`|B₂| = 1` on `E₊`, `C_E = 1`). -/
theorem twoZeroComb_global_bound {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : TwoZeroDesign.IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ, 0 < x →
      Real.exp (c' * edgeL x) *
        ‖edgeHankel c' (fun b => sechSqProfile b * d.twoZeroComb c' b) (c' * x ^ 2 / 3)‖ ≤
          K * √(c' / x) := by
  obtain ⟨K, hK0, hKe⟩ := edge_global_bound
  refine ⟨K, hK0, ?_⟩
  filter_upwards [twoZeroComb_innerCombHyp hK hA, eventually_gt_atTop (0 : ℝ)] with c' hI hc' d hd x hx
  have h := hKe (combH0 (d.twoZeroComb c')) π 8 1 Real.pi_pos (hI d hd).edgeHankelHyp zero_le_one
    (hI d hd).edgeSechBound c' x hc' hx
  rw [mul_one] at h
  exact h

/-- `λ K̃_c^{(2)} = c_K c'^{5/3}`: `K̃_c^{(2)} = sech²(π ξ_*/2) (2√2/(πλ))^{7/2}`, `λ = (k_tip c')^{-2/3}`. -/
lemma lambda_mul_normK_two : ∃ cK : ℝ, 0 < cK ∧ ∀ {c' : ℝ}, 0 < c' →
    lambdaComb c' * windowNormKTilde 2 c' = cK * c' ^ (5 / 3 : ℝ) := by
  have hξ := xiStar_pos
  refine ⟨(1 / Real.cosh (π * xiStar / 2) ^ 2) * (2 * √2 / π) ^ (7 / 2 : ℝ) * kTip ^ (5 / 3 : ℝ),
    by have := kTip_pos; positivity, fun {c'} hc' => ?_⟩
  have hk : 0 < kTip * c' := mul_pos kTip_pos hc'
  have hl : lambdaComb c' = ((kTip * c') ^ (2 / 3 : ℝ))⁻¹ := by
    unfold lambdaComb; rw [Real.rpow_neg hk.le]
  have hu : 0 < (kTip * c') ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hk _
  have e : 2 * √2 / (π * lambdaComb c') = (2 * √2 / π) * (kTip * c') ^ (2 / 3 : ℝ) := by
    rw [hl]; field_simp
  have hexp : (2 * (((2 : ℕ) : ℝ) - 1 / 4) : ℝ) = 7 / 2 := by norm_num
  unfold windowNormKTilde
  rw [hexp, e, Real.mul_rpow (by positivity) hu.le, ← Real.rpow_mul hk.le,
    show (2 / 3 : ℝ) * (7 / 2) = 5 / 3 + 2 / 3 by norm_num, Real.rpow_add hk, hl,
    Real.mul_rpow kTip_pos.le hc'.le]
  have h2 : (kTip : ℝ) ^ (2 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos kTip_pos _).ne'
  field_simp
  exact Real.mul_rpow kTip_pos.le hc'.le

/-! ### 3. The real part of `h₂` -/

namespace TwoZeroDesign

variable {n : ℕ}

/-- `Re (sech² T_{χ(p)} B₁)(x) = T_{χ(p)}(x) · Re (sech² B₁)(x)` for real `x`. -/
lemma re_profile_eq (d : TwoZeroDesign n) (c' x : ℝ) :
    (sechSqProfile (x : ℂ) * d.twoZeroComb c' (x : ℂ)).re =
      tFac (d.chiP c') x * (sechSqProfile (x : ℂ) * d.comb c' (x : ℂ)).re := by
  unfold twoZeroComb
  rw [tFac_eq, ← mul_assoc, mul_comm (sechSqProfile (x : ℂ)), mul_assoc, Complex.re_ofReal_mul]

/-- `Re (sech² B₁)(x) = h₀(x)` of the window form (`modifiedH0`). -/
lemma re_sech_comb_eq (d : TwoZeroDesign n) (c' x : ℝ) :
    (sechSqProfile (x : ℂ) * d.comb c' (x : ℂ)).re = modifiedH0 2 (n + 2) d.toModified c' x := by
  rw [d.comb_eq_modifiedCombB, Upper.Positivity.sechSqProfile_ofReal, Complex.re_ofReal_mul]
  rfl

end TwoZeroDesign

/-! ### 4. Region I(a): the window -/

/-- **Region I(a)** (`ut:T2`, `eq:ut:T2-Ia`): for every `Σ₀` there is `C > 0` such that for `c'` large, `d ∈ 𝒦` and
`χ(q) + C λ c'^{-7/6} ≤ x ≤ ξ_* + λ Σ₀`, `2 g(c'x²/3) > 0` (`2g = Re h₂ - Re ĥ₂`).  The uniform Lemma R with
`T_{χ(q)}/(σ - σ_q)` divided out, times `T_{χ(p)} ≥ c₂ λ`, beats `SD_G` once `σ - σ_q ≥ C c'^{-7/6}`
(`t - t(q) = O(c'^{-5/6})`). -/
theorem twoZero_regionOne_a {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : TwoZeroDesign.IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) (Sg0 : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ,
      xiStar + lambdaComb c' * d.sigmaF + C * lambdaComb c' * c' ^ (-(7 / 6 : ℝ)) ≤ x →
      x ≤ xiStar + lambdaComb c' * Sg0 →
      0 < (sechSqProfile (x : ℂ) * d.twoZeroComb c' (x : ℂ) -
        edgeHankel c' (fun b => sechSqProfile b * d.twoZeroComb c' b) (c' * x ^ 2 / 3)).re := by
  obtain ⟨K, hK0, hKe⟩ := twoZeroComb_global_bound hK hA
  obtain ⟨c₂, hc₂, hT⟩ := TwoZeroDesign.twoZeroT_ge_window hK hA Sg0
  obtain ⟨w0, hw0, C₀, hR⟩ := TwoZeroDesign.lemma_R_lower_two_unif hK hA Sg0
  obtain ⟨cK, hcK, hlK⟩ := lambda_mul_normK_two
  obtain ⟨M, E, hM, hE, hb⟩ := hK.exists_comb_bounds hA
  have hξ := xiStar_pos
  obtain ⟨A, hA0⟩ : ∃ A : ℝ, A = K * √(2 / xiStar) := ⟨_, rfl⟩
  have hApos : 0 ≤ A := by rw [hA0]; positivity
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (A + 1) / (c₂ * w0 * cK) := ⟨_, rfl⟩
  have hCpos : 0 < C := by rw [hC]; positivity
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [hKe, hT, eventually_ge_atTop C₀, TwoZeroDesign.eventually_lambda_small M,
    eventually_gt_atTop (0 : ℝ)] with c' hKc hTc hc0 ⟨hl, hlM⟩ hcpos d hd x hx1 hx2
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
  have hbig : K * √(2 / xiStar) * √c' < c₂ * lambdaComb c' * (windowNormKTilde 2 c' * w0 * (σ - d.sigmaF)) := by
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
    calc K * √(2 / xiStar) * √c' = A * √c' := by rw [hA0]
      _ < (A + 1) * √c' := by nlinarith
      _ = c₂ * w0 * (cK * c' ^ (5 / 3 : ℝ)) * (C * c' ^ (-(7 / 6 : ℝ))) := e2.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hgap hpos.le
  have hglob := hKc d hd x hx0
  have := pos_of_lower_hankel hcpos hxhalf hK0 hEpos hglob hQ hbig
  rw [Complex.sub_re]
  exact this


/-! ### 5. Region I(b): the overshoot window -/

/-- **Region I(b)** (`ut:T2`, `eq:ut:T2-Ib`): there is `Σ₀ > 0` such that for `c'` large, `d ∈ 𝒦` and
`ξ_* + λΣ₀ ≤ x ≤ ξ_* + c'^{-2/5}`, `2 g(c'x²/3) > 0`.  `Σ₀` is chosen so that `lemma_P_b` gives `B₁ ≥ ½ B_ref^{(2)}`, `x` lies
in a cell `n ≥ max(N_ov, 3)` of `K5` (`designProfile_overshoot_lower`, `2n₁ = 7/2`) and `x - χ(p) ≥ ½ (x - ξ_*)`
(`twoZeroT_ge_beyond`): `Re h₂ e^{c'L} ≥ c (x - ξ_*)^{-5/2} ≥ c c' ≫ √c'`. -/
theorem twoZero_regionOne_b {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : TwoZeroDesign.IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ Sg0 : ℝ, 0 < Sg0 ∧ ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ,
      xiStar + lambdaComb c' * Sg0 ≤ x → x ≤ xiStar + c' ^ (-(2 / 5 : ℝ)) →
      0 < (sechSqProfile (x : ℂ) * d.twoZeroComb c' (x : ℂ) -
        edgeHankel c' (fun b => sechSqProfile b * d.twoZeroComb c' b) (c' * x ^ 2 / 3)).re := by
  obtain ⟨K, hK0, hKe⟩ := twoZeroComb_global_bound hK hA
  obtain ⟨M, E, hM, hE, hb⟩ := hK.exists_comb_bounds hA
  obtain ⟨Sgb, cc, hSgb, hcc, hov⟩ := designProfile_overshoot_lower 2 (n + 2) (by norm_num) (by omega) M E
  obtain ⟨c₁, Sg1, hc₁, hSg1, hT⟩ := TwoZeroDesign.twoZeroT_ge_beyond hK
  have hξ := xiStar_pos
  have hπ := Real.pi_pos
  refine ⟨max Sgb Sg1, lt_of_lt_of_le hSgb (le_max_left _ _), ?_⟩
  obtain ⟨κ₂, hκ₂⟩ : ∃ κ₂ : ℝ, κ₂ = c₁ * cc * ((2 / π) * (2 / π) ^ (5 / 2 : ℝ)) := ⟨_, rfl⟩
  have hκ₂pos : 0 < κ₂ := by rw [hκ₂]; positivity
  obtain ⟨A, hA0⟩ : ∃ A : ℝ, A = K * √(2 / xiStar) := ⟨_, rfl⟩
  have hbigc : ∀ᶠ c' : ℝ in atTop, A / κ₂ < c' ^ (1 / 2 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_gt_atTop _
  filter_upwards [hKe, hov, hT, hbigc, eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (1 : ℝ)] with
    c' hKc hovc hTc hbc hcpos hc1 d hd x hx1 hx2
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
  have hbig : K * √(2 / xiStar) * √c' < κ₂ * c' := by
    have hsc : 0 < √c' := Real.sqrt_pos.2 hcpos
    have h1 : A < κ₂ * √c' := by
      rw [← Real.sqrt_eq_rpow] at hbc
      rwa [div_lt_iff₀ hκ₂pos, mul_comm] at hbc
    have h2 : c' = √c' * √c' := (Real.mul_self_sqrt hcpos.le).symm
    calc K * √(2 / xiStar) * √c' = A * √c' := by rw [hA0]
      _ < κ₂ * √c' * √c' := mul_lt_mul_of_pos_right h1 hsc
      _ = κ₂ * c' := by rw [mul_assoc, ← h2]
  have hglob := hKc d hd x hx0
  have := pos_of_lower_hankel hcpos (by linarith) hK0 hEpos hglob hQ hbig
  rw [Complex.sub_re]
  exact this

/-! ### 6. Region I -/

/-- **Region I** (`ut:T2`): there is `C > 0` such that for `c'` large, `d ∈ 𝒦` and every real `x` with
`χ(q) + C λ c'^{-7/6} ≤ x ≤ ξ_* + c'^{-2/5}` (`χ(q) = ξ_* + λσ_q`), `2 g(c'x²/3) > 0`
(`2g = Re h₂ - Re ĥ₂`, `h₂ = sech² B₂`), uniformly on a compact family of admissible designs. -/
theorem twoZero_regionOne {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : TwoZeroDesign.IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ,
      xiStar + lambdaComb c' * d.sigmaF + C * lambdaComb c' * c' ^ (-(7 / 6 : ℝ)) ≤ x →
      x ≤ xiStar + c' ^ (-(2 / 5 : ℝ)) →
      0 < (sechSqProfile (x : ℂ) * d.twoZeroComb c' (x : ℂ) -
        edgeHankel c' (fun b => sechSqProfile b * d.twoZeroComb c' b) (c' * x ^ 2 / 3)).re := by
  obtain ⟨Sg0, hSg0, hb⟩ := twoZero_regionOne_b hK hA
  obtain ⟨C, hC, ha⟩ := twoZero_regionOne_a hK hA Sg0
  refine ⟨C, hC, ?_⟩
  filter_upwards [ha, hb] with c' hac hbc d hd x hx1 hx2
  by_cases h : x ≤ xiStar + lambdaComb c' * Sg0
  · exact hac d hd x hx1 h
  · exact hbc d hd x (not_le.1 h).le hx2

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.tFac_ge_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tFac_ge_sub

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.TwoZeroDesign.twoZeroT_ge_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoZeroDesign.twoZeroT_ge_window

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroComb_global_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroComb_global_bound

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.lambda_mul_normK_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lambda_mul_normK_two

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_regionOne_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_regionOne_a

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_regionOne_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_regionOne_b

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_regionOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_regionOne

end FormalResearch.ModularBootstrap.TwoLevel
