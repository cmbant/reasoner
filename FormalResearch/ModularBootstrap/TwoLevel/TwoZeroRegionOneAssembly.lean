module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroRegionOne
public import FormalResearch.ModularBootstrap.Upper.Positivity.RegionOneAssembly
public import FormalResearch.ModularBootstrap.Upper.Assembly.Chart
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroTransfer

/-!
# Region I and Region II: positivity of `g` for `t ≥ t(q) + 1` (`upper_transfer.tex`, `ut:T2`)

Source: `upper_transfer.tex`, Theorem T2 (`ut:T2`): "`g_c > 0` on `t ≥ t(q) + 1` uniformly on `𝒦` at `w = 1`", from Region I
(`TwoZeroRegionOne`, `x ≤ ξ_* + c'^{-2/5}`) and Region II (`x ≥ ξ_* + c'^{-2/5}`, Lemma II-F, package `TwoZeroRegionTwo`).

* `tendsto_lambda_mul_rpow`: `λ c'^{-1/6} → 0`;
* `tAiry_eq_chi`: `t(q) = c' χ(q)²/3` with `χ(q) = ξ_* + λσ_q`;
* `twoZero_regionOne_t`: **Region I in the form `t ≥ t(q) + 1`**: for `c'` large, `d ∈ 𝒦`, `x ≥ 0` with
  `c' χ(q)²/3 + 1 ≤ c' x²/3` and `x ≤ ξ_* + c'^{-2/5}`, `2g(c'x²/3) > 0`;
* `twoZero_pos_of_regionTwo`: Region I together with the Region II statement `twoZero_regionII_pos` (taken as the
  hypothesis `hII`, the statement of that theorem verbatim) gives `2g > 0` for every `x ≥ 0` with `c' x²/3 ≥ t(q) + 1` and,
  in the variable of the `pos` field of `TwoZeroTransferData`, for every `t ≥ tAiry c' q + 1` at `x = √(3t/c')`.

All results are proved unconditionally (`twoZero_pos_of_regionTwo` for any `hII`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Membership
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Hankel
  FormalResearch.ModularBootstrap.Upper.Saddle FormalResearch.ModularBootstrap.Upper.Assembly
  FormalResearch.ModularBootstrap.Upper.Rigidity

/-- `λ c'^{-1/6} → 0`. -/
lemma tendsto_lambda_mul_rpow :
    Tendsto (fun c' : ℝ => lambdaComb c' * c' ^ (-(1 / 6 : ℝ))) atTop (𝓝 0) := by
  have h : Tendsto (fun c' : ℝ => kTip ^ (-(2 / 3 : ℝ)) * c' ^ (-(5 / 6 : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5 / 6)).const_mul (kTip ^ (-(2 / 3 : ℝ)))
    simpa using this
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c' hc'
  unfold lambdaComb
  rw [Real.mul_rpow kTip_pos.le hc'.le, mul_assoc, ← Real.rpow_add hc']
  norm_num

namespace TwoZeroDesign

variable {n : ℕ}

/-- `t(q) = c' χ(q)²/3`, `χ(q) = ξ_* + λ σ_q`, as soon as `χ(q) ≥ 0`. -/
lemma tAiry_eq_chi (d : TwoZeroDesign n) {c' : ℝ} (hc' : 0 < c')
    (hχ : 0 ≤ xiStar + lambdaComb c' * d.sigmaF) :
    tAiry c' d.q = c' * (xiStar + lambdaComb c' * d.sigmaF) ^ 2 / 3 :=
  tAiry_eq hc' hχ

end TwoZeroDesign

/-- **Region I in the form `t ≥ t(q) + 1`** (`ut:T2`): for `c'` large, `d ∈ 𝒦`, and every `x ≥ 0` with
`c' χ(q)²/3 + 1 ≤ c' x²/3` and `x ≤ ξ_* + c'^{-2/5}`, `2 g(c'x²/3) > 0`; uniformly on a compact family. -/
theorem twoZero_regionOne_t {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : TwoZeroDesign.IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ, 0 ≤ x →
      c' * (xiStar + lambdaComb c' * d.sigmaF) ^ 2 / 3 + 1 ≤ c' * x ^ 2 / 3 →
      x ≤ xiStar + c' ^ (-(2 / 5 : ℝ)) →
      0 < (sechSqProfile (x : ℂ) * d.twoZeroComb c' (x : ℂ) -
        edgeHankel c' (fun b => sechSqProfile b * d.twoZeroComb c' b) (c' * x ^ 2 / 3)).re := by
  obtain ⟨C, hC, hI⟩ := twoZero_regionOne hK hA
  obtain ⟨M, E, hM, hE, hb⟩ := hK.exists_comb_bounds hA
  have hξ := xiStar_pos
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 * xiStar + 2 := ⟨_, rfl⟩
  have hB1 : 1 ≤ B := by rw [hB]; linarith
  have hlim := tendsto_lambda_mul_rpow.const_mul (C * (2 * B + 1))
  rw [mul_zero] at hlim
  filter_upwards [hI, TwoZeroDesign.eventually_lambda_small M,
    hlim.eventually_le_const (by norm_num : (0 : ℝ) < 3),
    tendsto_lambdaComb_atTop.eventually_le_const (zero_lt_one : (0 : ℝ) < 1),
    eventually_gt_atTop (1 : ℝ)] with c' hIc ⟨hl, hlM⟩ hlc hl1 hc1 d hd x hx0 hx hx2
  have hcpos : 0 < c' := by linarith
  have hσFM : |d.sigmaF| ≤ M := by
    have := (hb d hd).1 2 le_rfl (by omega)
    simpa [TwoZeroDesign.sigmaSeq] using this
  set χ : ℝ := xiStar + lambdaComb c' * d.sigmaF with hχdef
  have hχ1 : xiStar / 2 ≤ χ := by
    have h2 : -(lambdaComb c' * M) ≤ lambdaComb c' * d.sigmaF := by
      have := mul_le_mul_of_nonneg_left (neg_le_of_abs_le hσFM) hl.le
      linarith
    rw [hχdef]; linarith
  have hχpos : 0 < χ := by linarith
  have hχB : χ ≤ B := by
    have h2 : lambdaComb c' * d.sigmaF ≤ lambdaComb c' * M := by
      have := mul_le_mul_of_nonneg_left (le_of_abs_le hσFM) hl.le
      linarith
    rw [hχdef, hB]; linarith
  have hxsq : c' * χ ^ 2 + 3 ≤ c' * x ^ 2 := by linarith
  have hχx : χ ≤ x := by
    by_contra hlt
    push Not at hlt
    have h1 : x ^ 2 < χ ^ 2 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left h1 hcpos]
  have hgapC : C * lambdaComb c' * c' ^ (-(7 / 6 : ℝ)) ≤ 3 / (c' * (2 * B + 1)) := by
    have hB3 : 0 < c' * (2 * B + 1) := by positivity
    rw [le_div_iff₀ hB3]
    have e : C * lambdaComb c' * c' ^ (-(7 / 6 : ℝ)) * (c' * (2 * B + 1)) =
        C * (2 * B + 1) * (lambdaComb c' * c' ^ (-(1 / 6 : ℝ))) := by
      have h7 : c' ^ (-(7 / 6 : ℝ)) * c' = c' ^ (-(1 / 6 : ℝ)) := by
        have h1 : c' = c' ^ (1 : ℝ) := (Real.rpow_one c').symm
        calc c' ^ (-(7 / 6 : ℝ)) * c' = c' ^ (-(7 / 6 : ℝ)) * c' ^ (1 : ℝ) := by rw [← h1]
          _ = c' ^ (-(1 / 6 : ℝ)) := by rw [← Real.rpow_add hcpos]; norm_num
      rw [← h7]; ring
    rw [e]; exact hlc
  refine hIc d hd x ?_ hx2
  by_cases hx1 : x ≤ χ + 1
  · have := sqrt_gap_lower hcpos hχpos hχB hχx hx1 hB1 hxsq
    rw [hχdef] at this
    linarith
  · push Not at hx1
    have : 3 / (c' * (2 * B + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    rw [hχdef] at hx1
    linarith

/-- **`2 g > 0` for `c' x²/3 ≥ t(q) + 1`** (`ut:T2`): Region I (`twoZero_regionOne_t`) and the Region II statement `hII`
(`twoZero_regionII_pos` of `TwoZeroRegionTwo`: `2g > 0` for `x ≥ ξ_* + c'^{-2/5}`); uniform on `𝒦`. -/
theorem twoZero_pos_x_of_regionTwo {n : ℕ} {𝒦 : Set (TwoZeroDesign n)}
    (hK : TwoZeroDesign.IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm)
    (hII : ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ, xiStar + c' ^ (-(2 / 5 : ℝ)) ≤ x →
      0 < (sechSqProfile (x : ℂ) * d.twoZeroComb c' (x : ℂ) -
        edgeHankel c' (fun b => sechSqProfile b * d.twoZeroComb c' b) (c' * x ^ 2 / 3)).re) :
    ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ, 0 ≤ x →
      c' * (xiStar + lambdaComb c' * d.sigmaF) ^ 2 / 3 + 1 ≤ c' * x ^ 2 / 3 →
      0 < (sechSqProfile (x : ℂ) * d.twoZeroComb c' (x : ℂ) -
        edgeHankel c' (fun b => sechSqProfile b * d.twoZeroComb c' b) (c' * x ^ 2 / 3)).re := by
  filter_upwards [twoZero_regionOne_t hK hA, hII] with c' hI hII' d hd x hx0 hx
  by_cases h : x ≤ xiStar + c' ^ (-(2 / 5 : ℝ))
  · exact hI d hd x hx0 hx h
  · exact hII' d hd x (not_le.1 h).le

/-- **`g > 0` for `t ≥ t(q) + 1` at `w = 1`** (`ut:T2`, "Thus `g_c > 0` on `t ≥ t(q) + 1` uniformly on `𝒦`"), in the
variable `t = c' x²/3`, `x = √(3t/c')`, `t ≥ tAiry c' q + 1` of the `pos` field of `TwoZeroTransferData`. -/
theorem twoZero_pos_of_regionTwo {n : ℕ} {𝒦 : Set (TwoZeroDesign n)}
    (hK : TwoZeroDesign.IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm)
    (hII : ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ, xiStar + c' ^ (-(2 / 5 : ℝ)) ≤ x →
      0 < (sechSqProfile (x : ℂ) * d.twoZeroComb c' (x : ℂ) -
        edgeHankel c' (fun b => sechSqProfile b * d.twoZeroComb c' b) (c' * x ^ 2 / 3)).re) :
    ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ t : ℝ, tAiry c' d.q + 1 ≤ t →
      0 < (sechSqProfile ((xOf c' t : ℝ) : ℂ) * d.twoZeroComb c' ((xOf c' t : ℝ) : ℂ) -
        edgeHankel c' (fun b => sechSqProfile b * d.twoZeroComb c' b) t).re := by
  obtain ⟨M, E, hM, hE, hb⟩ := hK.exists_comb_bounds hA
  filter_upwards [twoZero_pos_x_of_regionTwo hK hA hII, TwoZeroDesign.eventually_lambda_small M,
    eventually_gt_atTop (0 : ℝ)] with c' hP ⟨hl, hlM⟩ hcpos d hd t ht
  have hξ := xiStar_pos
  have hσFM : |d.sigmaF| ≤ M := by
    have := (hb d hd).1 2 le_rfl (by omega)
    simpa [TwoZeroDesign.sigmaSeq] using this
  have hχ0 : 0 ≤ xiStar + lambdaComb c' * d.sigmaF := by
    have h2 : -(lambdaComb c' * M) ≤ lambdaComb c' * d.sigmaF := by
      have := mul_le_mul_of_nonneg_left (neg_le_of_abs_le hσFM) hl.le
      linarith
    linarith
  have htq := d.tAiry_eq_chi hcpos hχ0
  have ht0 : 0 ≤ t := by
    have : 0 ≤ c' * (xiStar + lambdaComb c' * d.sigmaF) ^ 2 / 3 := by positivity
    linarith
  have hx0 : 0 ≤ xOf c' t := Real.sqrt_nonneg _
  have hxsq : c' * xOf c' t ^ 2 / 3 = t := by
    rw [sq_xOf hcpos ht0]; field_simp
  have key := hP d hd (xOf c' t) hx0 (by rw [hxsq]; rw [htq] at ht; exact ht)
  rwa [hxsq] at key

/-! ### Non-vacuity -/

/-- Non-vacuity of `twoZero_regionOne_t`: for an admissible design (the singleton compact family) and `c'` large, the
window `{x ≥ 0 : c' χ(q)²/3 + 1 ≤ c' x²/3, x ≤ ξ_* + c'^{-2/5}}` is non-empty (it contains `x = ξ_* + c'^{-2/5}`), so the
conclusion is a statement about actual points. -/
theorem twoZero_regionOne_t_nonvacuous :
    ∃ d : TwoZeroDesign 1, d.Adm ∧ ∀ᶠ c' : ℝ in atTop, ∃ x : ℝ, 0 ≤ x ∧
      c' * (xiStar + lambdaComb c' * d.sigmaF) ^ 2 / 3 + 1 ≤ c' * x ^ 2 / 3 ∧
      x ≤ xiStar + c' ^ (-(2 / 5 : ℝ)) ∧
      0 < (sechSqProfile (x : ℂ) * d.twoZeroComb c' (x : ℂ) -
        edgeHankel c' (fun b => sechSqProfile b * d.twoZeroComb c' b) (c' * x ^ 2 / 3)).re := by
  obtain ⟨d, hd⟩ := twoZeroDesign_adm_nonempty
  refine ⟨d, hd, ?_⟩
  have hξ := xiStar_pos
  have hK1 := isCompactFamily_singleton d
  have hA1 : ∀ e ∈ ({d} : Set (TwoZeroDesign 1)), e.Adm := fun e he => by
    rw [Set.mem_singleton_iff.1 he]; exact hd
  have hbig : ∀ᶠ c' : ℝ in atTop, 6 / xiStar ≤ c' ^ (3 / 5 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 5)).eventually_ge_atTop _
  filter_upwards [twoZero_regionOne_t hK1 hA1, eventually_mul_lambda_le |d.sigmaF| (1 / 2) (by norm_num),
    hbig, eventually_gt_atTop (1 : ℝ)] with c' hI hr hb hc1
  have hcpos : 0 < c' := by linarith
  have hl : 0 < lambdaComb c' := Real.rpow_pos_of_pos (mul_pos kTip_pos hcpos) _
  have hu0 : 0 < c' ^ (-(2 / 5 : ℝ)) := Real.rpow_pos_of_pos hcpos _
  have hx0 : 0 ≤ xiStar + c' ^ (-(2 / 5 : ℝ)) := by positivity
  have hlσ : lambdaComb c' * |d.sigmaF| ≤ c' ^ (-(2 / 5 : ℝ)) / 2 := by linarith
  have hσ1 : lambdaComb c' * d.sigmaF ≤ lambdaComb c' * |d.sigmaF| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) hl.le
  have hσ2 : -(lambdaComb c' * |d.sigmaF|) ≤ lambdaComb c' * d.sigmaF := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le d.sigmaF) hl.le
    linarith
  set u : ℝ := c' ^ (-(2 / 5 : ℝ)) with hu
  set χ : ℝ := xiStar + lambdaComb c' * d.sigmaF with hχ
  have hd1 : u / 2 ≤ (xiStar + u) - χ := by rw [hχ]; linarith
  have hs : xiStar ≤ (xiStar + u) + χ := by rw [hχ]; linarith
  have e : c' * u = c' ^ (3 / 5 : ℝ) := by
    conv_lhs => rw [show c' = c' ^ (1 : ℝ) from (Real.rpow_one c').symm]
    rw [hu, ← Real.rpow_add hcpos]; norm_num
  have h1 : c' * (u / 2 * xiStar) ≤ c' * (((xiStar + u) - χ) * ((xiStar + u) + χ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hd1 hs hξ.le (by linarith)) hcpos.le
  have h2 : c' * (u / 2 * xiStar) = xiStar / 2 * c' ^ (3 / 5 : ℝ) := by rw [← e]; ring
  have h3 : 3 ≤ xiStar / 2 * c' ^ (3 / 5 : ℝ) := by
    have := (div_le_iff₀ hξ).1 hb
    nlinarith
  have h4 : c' * (((xiStar + u) - χ) * ((xiStar + u) + χ)) = c' * (xiStar + u) ^ 2 - c' * χ ^ 2 := by ring
  have hwin : c' * χ ^ 2 / 3 + 1 ≤ c' * (xiStar + u) ^ 2 / 3 := by linarith
  exact ⟨xiStar + u, hx0, hwin, le_rfl, hI d (Set.mem_singleton d) (xiStar + u) hx0 hwin le_rfl⟩

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_regionOne_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_regionOne_t

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_pos_x_of_regionTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_pos_x_of_regionTwo

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_regionOne_t_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_regionOne_t_nonvacuous

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_pos_of_regionTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_pos_of_regionTwo

end FormalResearch.ModularBootstrap.TwoLevel
