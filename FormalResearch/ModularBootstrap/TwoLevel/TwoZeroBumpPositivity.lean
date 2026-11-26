module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroBumpRegionTwo
public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroRegionOneAssembly

/-!
# `g_w > 0` for `t ≥ t(q) + 1` at every weight (`ut:T2`, `ut:III`)

Source: `upper_transfer.tex`, Theorem T2 (`ut:T2`) and Proposition III (`ut:III`) at fixed `(w, Q)`.  The test of `ut:T2`
at weight `w = prob.w` is `g_w = ½(h₂^{(p)} - 𝓗_w h₂^{(p)})` (`twoZeroBumpG`), `h₂^{(p)} = sech² T_{χ(p)} B₁^{(p)}` with
the bump of `rpParams (prob.w - 1)` and the cut `bumpCut` above its block.

* `twoZeroBumpB`, `twoZeroBumpG`: the bumped comb and the test of `TwoZeroTransferData` at weight `prob.w`;
* `regionOne_t_abstract`: the passage from Region I in the form `χ(q) + C λ c^{-7/6} ≤ x` to `c x²/3 ≥ t(q) + 1`
  (the proof of `twoZero_regionOne_t`, for an arbitrary predicate indexed by a type of data);
* `twoZeroBump_pos_x`, `twoZeroBump_pos_t`: `2 g_w > 0` for `c x²/3 ≥ t(q) + 1`, resp. `t ≥ tAiry c q + 1`;
* `twoZeroBump_pos_g`: the `pos` field of `TwoZeroTransferData`: `g_w(t) > 0` for `t ≥ tAiry c q + 1`.

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
  FormalResearch.ModularBootstrap.Upper.Positivity FormalResearch.ModularBootstrap.Upper.Assembly
  FormalResearch.ModularBootstrap.Upper.Rigidity
open TwoZeroDesign

/-! ### 1. The test at weight `prob.w` -/

/-- The bump of the weight `prob.w` (`rpParams (prob.w - 1)`, `fw:e2.2`, `fw:e2.3`). -/
noncomputable def probBump (prob : FixedWeightProblem) : BumpData := (rpParams (prob.w - 1)).bumpData

/-- The bumped two-zero comb at weight `prob.w`: the bump of `probBump` and the cut `bumpCut` above its block. -/
noncomputable def twoZeroBumpB (prob : FixedWeightProblem) {n : ℕ} (d : TwoZeroDesign n) (c : ℝ) : ℂ → ℂ :=
  d.bumpComb (probBump prob) c (bumpCut (probBump prob) (n + 2) c)

/-- The test `g_w = ½(h₂^{(p)} - 𝓗_w h₂^{(p)})` of `ut:T2` at weight `prob.w`. -/
noncomputable def twoZeroBumpG (prob : FixedWeightProblem) {n : ℕ} (d : TwoZeroDesign n) (c : ℝ) : ℝ → ℝ :=
  pairOdd (combProfile c (twoZeroBumpB prob d c))
    (hankelTransform prob.w (combProfile c (twoZeroBumpB prob d c)))

/-! ### 2. Region I in the form `t ≥ t(q) + 1` -/

theorem regionOne_t_abstract {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : TwoZeroDesign.IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) {ι : Type} {Q : ℝ → TwoZeroDesign n → ι → ℝ → Prop} {C : ℝ} (_hC : 0 < C)
    (hI : ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ i : ι, ∀ x : ℝ,
      xiStar + lambdaComb c' * d.sigmaF + C * lambdaComb c' * c' ^ (-(7 / 6 : ℝ)) ≤ x →
      x ≤ xiStar + c' ^ (-(2 / 5 : ℝ)) → Q c' d i x) :
    ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ i : ι, ∀ x : ℝ, 0 ≤ x →
      c' * (xiStar + lambdaComb c' * d.sigmaF) ^ 2 / 3 + 1 ≤ c' * x ^ 2 / 3 →
      x ≤ xiStar + c' ^ (-(2 / 5 : ℝ)) → Q c' d i x := by
  obtain ⟨M, E, hM, hE, hb⟩ := hK.exists_comb_bounds hA
  have hξ := xiStar_pos
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 * xiStar + 2 := ⟨_, rfl⟩
  have hB1 : 1 ≤ B := by rw [hB]; linarith
  have hlim := tendsto_lambda_mul_rpow.const_mul (C * (2 * B + 1))
  rw [mul_zero] at hlim
  filter_upwards [hI, TwoZeroDesign.eventually_lambda_small M,
    hlim.eventually_le_const (by norm_num : (0 : ℝ) < 3),
    tendsto_lambdaComb_atTop.eventually_le_const (zero_lt_one : (0 : ℝ) < 1),
    eventually_gt_atTop (1 : ℝ)] with c' hIc ⟨hl, hlM⟩ hlc hl1 hc1 d hd i x hx0 hx hx2
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
  refine hIc d hd i x ?_ hx2
  by_cases hx1 : x ≤ χ + 1
  · have := sqrt_gap_lower hcpos hχpos hχB hχx hx1 hB1 hxsq
    rw [hχdef] at this
    linarith
  · push Not at hx1
    have : 3 / (c' * (2 * B + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    rw [hχdef] at hx1
    linarith


/-- **`2 g_w > 0` for `c x²/3 ≥ t(q) + 1`** (`ut:T2`, first line of `eq:ut:T2`, every weight): Region I
(`twoZeroBump_regionOne`) and Region II (`twoZeroBump_regionII_pos`); uniform on `𝒦` and for every cut above the block. -/
theorem twoZeroBump_pos_x (p : ℕ) (P : RpParams p) {n : ℕ} {𝒦 : Set (TwoZeroDesign n)}
    (hK : TwoZeroDesign.IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' →
      (∀ k : ℕ, 1 ≤ k → chiQuantile c (k : ℝ) ≤ P.X → k ≤ N') → ∀ x : ℝ, 0 ≤ x →
      c * (xiStar + lambdaComb c * d.sigmaF) ^ 2 / 3 + 1 ≤ c * x ^ 2 / 3 →
      0 < (sechSqProfile (x : ℂ) * d.bumpComb P.bumpData c N' (x : ℂ) -
        edgeHankelP p c (fun b => sechSqProfile b * d.bumpComb P.bumpData c N' b) (c * x ^ 2 / 3)).re := by
  obtain ⟨C, hC, hI⟩ := twoZeroBump_regionOne P.bumpData p hK hA
  have hI' := regionOne_t_abstract hK hA (ι := ℕ)
    (Q := fun c d N' x => n + 2 ≤ N' →
      0 < (sechSqProfile (x : ℂ) * d.bumpComb P.bumpData c N' (x : ℂ) -
        edgeHankelP p c (fun b => sechSqProfile b * d.bumpComb P.bumpData c N' b) (c * x ^ 2 / 3)).re)
    hC (hI.mono fun c h d hd N' x h1 h2 hN => h d hd N' hN x h1 h2)
  filter_upwards [hI', twoZeroBump_regionII_pos p P hK hA] with c hI1 hII d hd N' hN' hcut x hx0 hx
  by_cases h : x ≤ xiStar + c ^ (-(2 / 5 : ℝ))
  · exact hI1 d hd N' x hx0 hx h hN'
  · exact hII d hd N' hN' hcut x (not_le.1 h).le

/-- **`2 g_w > 0` for `t ≥ tAiry c q + 1`** (variable `t = c x²/3`, `x = √(3t/c)`). -/
theorem twoZeroBump_pos_t (p : ℕ) (P : RpParams p) {n : ℕ} {𝒦 : Set (TwoZeroDesign n)}
    (hK : TwoZeroDesign.IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ N' : ℕ, n + 2 ≤ N' →
      (∀ k : ℕ, 1 ≤ k → chiQuantile c (k : ℝ) ≤ P.X → k ≤ N') → ∀ t : ℝ, tAiry c d.q + 1 ≤ t →
      0 < (sechSqProfile ((xOf c t : ℝ) : ℂ) * d.bumpComb P.bumpData c N' ((xOf c t : ℝ) : ℂ) -
        edgeHankelP p c (fun b => sechSqProfile b * d.bumpComb P.bumpData c N' b) t).re := by
  obtain ⟨M, E, hM, hE, hb⟩ := hK.exists_comb_bounds hA
  filter_upwards [twoZeroBump_pos_x p P hK hA, TwoZeroDesign.eventually_lambda_small M,
    eventually_gt_atTop (0 : ℝ)] with c hP ⟨hl, hlM⟩ hcpos d hd N' hN' hcut t ht
  have hξ := xiStar_pos
  have hσFM : |d.sigmaF| ≤ M := by
    have := (hb d hd).1 2 le_rfl (by omega)
    simpa [TwoZeroDesign.sigmaSeq] using this
  have hχ0 : 0 ≤ xiStar + lambdaComb c * d.sigmaF := by
    have h2 : -(lambdaComb c * M) ≤ lambdaComb c * d.sigmaF := by
      have := mul_le_mul_of_nonneg_left (neg_le_of_abs_le hσFM) hl.le
      linarith
    linarith
  have htq := d.tAiry_eq_chi hcpos hχ0
  have ht0 : 0 ≤ t := by
    have : 0 ≤ c * (xiStar + lambdaComb c * d.sigmaF) ^ 2 / 3 := by positivity
    linarith
  have hx0 : 0 ≤ xOf c t := Real.sqrt_nonneg _
  have hxsq : c * xOf c t ^ 2 / 3 = t := by
    rw [sq_xOf hcpos ht0]; field_simp
  have key := hP d hd N' hN' hcut (xOf c t) hx0 (by rw [hxsq]; rw [htq] at ht; exact ht)
  rwa [hxsq] at key

/-- **The `pos` field of `ut:T2` at every weight**: for `c` large and `d ∈ 𝒦`, `g_w(t) > 0` for `t ≥ tAiry c q + 1`. -/
theorem twoZeroBump_pos_g (prob : FixedWeightProblem) {n : ℕ} {𝒦 : Set (TwoZeroDesign n)}
    (hK : TwoZeroDesign.IsCompactFamily 𝒦) (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ t : ℝ, tAiry c d.q + 1 ≤ t → 0 < twoZeroBumpG prob d c t := by
  filter_upwards [twoZeroBump_pos_t (prob.w - 1) (rpParams (prob.w - 1)) hK hA,
    twoZeroBump_k7W prob (probBump prob) hK hA, twoZeroBump_innerCombHyp (probBump prob) hK hA,
    eventually_gt_atTop (0 : ℝ)] with c hP hk7 hin hc d hd t ht
  have hN' := le_bumpCut (probBump prob) (n + 2) c
  have hcut := bumpCut_spec (probBump prob) (n + 2) hc
  have hI := hin d hd _ hN'
  obtain ⟨C, hC0, hd1, hd2, -⟩ := hk7 d hd _ hN'
  have hq0 : 0 ≤ tAiry c d.q := tAiry_nonneg hc d.q
  have ht0 : 0 < t := by linarith
  have h1 := hP d hd _ hN' hcut t ht
  have e1 : combH0 (twoZeroBumpB prob d c) ((xOf c t : ℝ) : ℂ) = (combProfile c (twoZeroBumpB prob d c) t : ℂ) :=
    hI.combProfile_eq ht0
  have e2 := hI.edgeHankelP_eq (prob.w - 1) hc hd1 ht0
  rw [Nat.sub_add_cancel prob.hw] at e2
  have e1' : sechSqProfile ((xOf c t : ℝ) : ℂ) * d.bumpComb (probBump prob) c
      (bumpCut (probBump prob) (n + 2) c) ((xOf c t : ℝ) : ℂ) =
      (combProfile c (twoZeroBumpB prob d c) t : ℂ) := e1
  have e2' : edgeHankelP (prob.w - 1) c (fun b => sechSqProfile b * d.bumpComb (probBump prob) c
      (bumpCut (probBump prob) (n + 2) c) b) t =
      (hankelTransform prob.w (combProfile c (twoZeroBumpB prob d c)) t : ℂ) := e2
  show 0 < pairOdd (combProfile c (twoZeroBumpB prob d c))
    (hankelTransform prob.w (combProfile c (twoZeroBumpB prob d c))) t
  unfold pairOdd
  have h1' : 0 < (((combProfile c (twoZeroBumpB prob d c) t : ℝ) : ℂ) -
      ((hankelTransform prob.w (combProfile c (twoZeroBumpB prob d c)) t : ℝ) : ℂ)).re := by
    rw [← e1', ← e2']
    exact h1
  rw [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re] at h1'
  linarith

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.regionOne_t_abstract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms regionOne_t_abstract

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroBump_pos_x' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_pos_x

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroBump_pos_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_pos_t

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroBump_pos_g' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroBump_pos_g

end FormalResearch.ModularBootstrap.TwoLevel
