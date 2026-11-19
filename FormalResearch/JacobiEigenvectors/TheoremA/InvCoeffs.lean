module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.InvExpand

/-!
# Paper J, Layer 2: `InvCoeffs` (cor:eigen (b)(iii)) from the slope input (L2.E)

Source: Paper J `thmA.tex`, proof of `cor:eigen` (b)(iii) and Step 5.

## Proved here

* **`invCoeffs_of_slope : InvCoeffs F K M S`** for `M >= 1`, `IsCompact K`, `HypOn`, `DM F K M`, `0 < delta`, `SmoothExt`, `EigenRule`, `ActionFormula` and `BandSlope` (the same premises as `invLevel_of_slope`): the expansion data
  `x_r = xs r r` of `InvReg` (`C^{M+1-r}` with the uniform bound `Cx`, `x_0` an inverse of `S_0`), `hat X_k = sum_{r <= M} h^r x_r(y_k) + O(h^{M+1})` (the root `hat X_k` of `InvLevel` is within `C h^{M+1}` of `P(h) = sum_r h^r x_r(y_k)`
  by the mean value theorem for `F_M(., h)` and `InvCtx.expand_key`), and the formulas for `x_1`, `x_2`.
* `InvCtx.iter_two`, `invC_zero/one/two`: the conversion of the Taylor coefficients to `S_j`, `S_j'`, `S_0''`.

## Differences from the paper

The recursion is solved coefficient by coefficient (`InvAlg`) instead of through the implicit function `X(y, h)`; the constants are explicit.

## Not formalised

The premise `BandSlope` is the output of the window assembly (`CorEigenWindows.bandSlope_of_windows`), not proved here.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set Filter Topology FormalResearch.JacobiEigenvectors.Setting InvBD InvAlg

variable {Par : Type*} [TopologicalSpace Par]

section Final

variable {F : SymbolFamily Par} {K : Set Par} {M : ℕ} {S : ℕ → Par → ℝ → ℝ} {δ Cn c0 : ℝ} (ctx : InvCtx F K M S δ Cn c0)

include ctx

lemma InvCtx.iter_two {μ : Par} (hμ : μ ∈ K) {j : ℕ} (hj : j ≤ M) {X : ℝ} (hX : X ∈ Ioo (F.bandLo μ - δ) (F.bandHi μ + δ)) :
    iteratedDerivWithin 2 (S j μ) (Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) X = deriv (deriv (S j μ)) X := by
  have hn : Icc (F.bandLo μ - δ) (F.bandHi μ + δ) ∈ 𝓝 X := Icc_mem_nhds hX.1 hX.2
  rw [iteratedDerivWithin_succ, derivWithin_of_mem_nhds hn]
  have hev : iteratedDerivWithin 1 (S j μ) (Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) =ᶠ[𝓝 X] deriv (S j μ) := by
    filter_upwards [Ioo_mem_nhds hX.1 hX.2] with Y hY using ctx.iter_one hY
  exact hev.deriv_eq

lemma InvCtx.invC_zero {μ : Par} (j : ℕ) (y : ℝ) :
    invC F S δ (invDelta δ Cn c0) j 0 μ y = S j μ (invX0 F S (invDelta δ Cn c0) μ y) := by
  simp [invC, invW, iteratedDerivWithin_zero]

lemma InvCtx.invC_one {μ : Par} (hμ : μ ∈ K) (j : ℕ) {y : ℝ} (hy : y ∈ Icc 0 (Real.pi * F.L)) :
    invC F S δ (invDelta δ Cn c0) j 1 μ y = deriv (S j μ) (invX0 F S (invDelta δ Cn c0) μ y) := by
  simp only [invC, invW, Nat.factorial_one, Nat.cast_one, inv_one, one_mul]
  exact ctx.iter_one (ctx.Iprime_sub (ctx.x0_mem hμ hy))

lemma InvCtx.invC_two {μ : Par} (hμ : μ ∈ K) {j : ℕ} (hj : j ≤ M) {y : ℝ} (hy : y ∈ Icc 0 (Real.pi * F.L)) :
    invC F S δ (invDelta δ Cn c0) j 2 μ y = (1 / 2) * deriv (deriv (S j μ)) (invX0 F S (invDelta δ Cn c0) μ y) := by
  simp only [invC, invW]
  rw [ctx.iter_two hμ hj (ctx.Iprime_sub (ctx.x0_mem hμ hy))]
  norm_num [Nat.factorial]

lemma InvCtx.sum_eq_P (μ : Par) (y h : ℝ) :
    ∑ r ∈ range (M + 1), h ^ r * xs F S δ (invDelta δ Cn c0) M μ r r y =
      invX0 F S (invDelta δ Cn c0) μ y + (Dp M (fun r => xs F S δ (invDelta δ Cn c0) M μ M r y)).eval h := by
  rw [Finset.sum_range_succ', InvAlg.eval_Dp M _ h]
  have h0 : h ^ 0 * xs F S δ (invDelta δ Cn c0) M μ 0 0 y = invX0 F S (invDelta δ Cn c0) μ y := by simp [xs, st]
  rw [h0, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrM : r + 1 ≤ M := Finset.mem_range.1 hr
  have : xs F S δ (invDelta δ Cn c0) M μ (r + 1) (r + 1) y = xs F S δ (invDelta δ Cn c0) M μ M (r + 1) y :=
    (st_stable M _ _ M hrM).symm
  rw [this]; ring

end Final

section Main

variable {F : SymbolFamily Par} {K : Set Par} {M : ℕ} {S : ℕ → Par → ℝ → ℝ} {δ Cn : ℝ}

/-- `x_r = d_h^r X(., 0)/r!`, the recursion: `InvCoeffs` (**cor:eigen (b)(iii)**) from the slope input `BandSlope`. -/
theorem invCoeffs_of_slope (hK : IsCompact K) (hH : HypOn F K) (hD : DM F K M) (hM : 1 ≤ M)
    (hδ : 0 < δ) (hS : SmoothExt F K M S δ Cn) {hM' C : ℝ} (hR : EigenRule F K M S hM' C) (hA : ActionFormula F K S)
    (hsl : BandSlope F K S) : InvCoeffs F K M S := by
  have hsl0 := hsl
  obtain ⟨c0, hc0, hsl'⟩ := hsl
  have hD0 := dm_zero_of_dm F K M hK hD
  have ctx : InvCtx F K M S δ Cn c0 := ⟨hδ, hM, hc0, hS, hA, hH, hD0, hsl'⟩
  obtain ⟨Cb, hB⟩ := band_bdd hK hH hD0
  have hlev := invLevel_of_slope hK hH hD hM hδ hS hR hA hsl0
  have hab : (0 : ℝ) < Real.pi * F.L := by have := F.L_pos; positivity
  have hI : (Icc (0 : ℝ) (Real.pi * F.L)).Nonempty := ⟨0, le_rfl, hab.le⟩
  refine ⟨fun r μ y => xs F S δ (invDelta δ Cn c0) M μ r r y, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro μ hμ r hr
    obtain ⟨Cr, hCr⟩ := ctx.reg hB r hr
    exact (BD.contDiffOn_bound hab (M + 1 - r) Cr _ (hCr μ hμ r le_rfl)).1
  · have hex : ∀ r : ℕ, ∃ Cr : ℝ, r ≤ M → ∀ μ ∈ K, BD (Icc 0 (Real.pi * F.L)) (M + 1 - r) Cr (xs F S δ (invDelta δ Cn c0) M μ r r) := by
      intro r
      by_cases hr : r ≤ M
      · obtain ⟨Cr, hCr⟩ := ctx.reg hB r hr
        exact ⟨Cr, fun _ μ hμ => hCr μ hμ r le_rfl⟩
      · exact ⟨0, fun h => absurd h hr⟩
    choose Cr hCr using hex
    refine ⟨∑ r ∈ range (M + 1), |Cr r|, fun μ hμ r hr i hi y hy => ?_⟩
    have hrm : r ≤ M := hr
    have h1 := (BD.contDiffOn_bound hab (M + 1 - r) (Cr r) _ (hCr r hrm μ hμ)).2 i hi y hy
    refine h1.trans ((le_abs_self _).trans ?_)
    exact Finset.single_le_sum (f := fun r => |Cr r|) (fun i _ => abs_nonneg _) (Finset.mem_range.2 (by omega))
  · intro μ hμ y hy
    have : xs F S δ (invDelta δ Cn c0) M μ 0 0 y = invX0 F S (invDelta δ Cn c0) μ y := by simp [xs, st]
    beta_reduce
    rw [this]
    exact ctx.x0_band hμ hy
  · obtain ⟨Cd, Ck, hCd, hkey⟩ := ctx.expand_key hB
    obtain ⟨δ3, c2, Cc, hs, hδ3, hδ3δ, hc2, hhs, hlev'⟩ := hlev
    refine ⟨Cc + Ck / c2, min hs (min 1 (δ3 / (Cd + 1))), lt_min hhs (lt_min one_pos (by positivity)), ?_⟩
    intro μ hμ N hN Xs Um hE k
    beta_reduce
    have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
    have hN1 : F.step N ≤ hs := hN.trans (min_le_left _ _)
    have hN2 : F.step N ≤ 1 := hN.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hN3 : F.step N ≤ δ3 / (Cd + 1) := hN.trans ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨hslope, hroot⟩ := hlev' μ hμ N hN1
    obtain ⟨Xh, hXh, ⟨hXeq, -⟩, hdist⟩ := hroot Xs Um hE k
    -- the level `y_k`
    have hstep := step_mul_succ_aux F N
    have hkN : ((k : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 k.2
    have hy : Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2) ∈ Icc 0 (Real.pi * F.L) := by
      refine ⟨by positivity, ?_⟩
      calc Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2) ≤ Real.pi * F.step N * ((N : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = Real.pi * F.L := by rw [← hstep]; ring
    obtain ⟨hδb, hest⟩ := hkey μ hμ _ hy (F.step N) hpos hN2
    rw [ctx.sum_eq_P]
    -- the position of `P`
    have hX0 := (ctx.x0_band hμ hy).1
    have hδ' : |(Dp M (fun r => xs F S δ (invDelta δ Cn c0) M μ M r (Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2)))).eval (F.step N)| ≤ δ3 := by
      refine hδb.trans ?_
      calc Cd * F.step N ≤ Cd * (δ3 / (Cd + 1)) := mul_le_mul_of_nonneg_left hN3 hCd
        _ ≤ δ3 := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith
    have hPmem := abs_le.1 hδ'
    have hP3 : invX0 F S (invDelta δ Cn c0) μ (Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2)) +
        (Dp M (fun r => xs F S δ (invDelta δ Cn c0) M μ M r (Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2)))).eval (F.step N) ∈
        Icc (F.bandLo μ - δ3) (F.bandHi μ + δ3) := ⟨by linarith [hX0.1, hPmem.1], by linarith [hX0.2, hPmem.2]⟩
    have hPbig : invX0 F S (invDelta δ Cn c0) μ (Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2)) +
        (Dp M (fun r => xs F S δ (invDelta δ Cn c0) M μ M r (Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2)))).eval (F.step N) ∈
        Icc (F.bandLo μ - δ) (F.bandHi μ + δ) := ⟨by linarith [hP3.1], by linarith [hP3.2]⟩
    have hFP := hest hPbig
    -- mean value theorem for `F_M(., h)` on `I_3`
    have hmvt : c2 * |(invX0 F S (invDelta δ Cn c0) μ (Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2)) +
        (Dp M (fun r => xs F S δ (invDelta δ Cn c0) M μ M r (Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2)))).eval (F.step N)) - Xh| ≤
        |Fsum S M μ (F.step N) (invX0 F S (invDelta δ Cn c0) μ (Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2)) +
          (Dp M (fun r => xs F S δ (invDelta δ Cn c0) M μ M r (Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2)))).eval (F.step N)) -
        Fsum S M μ (F.step N) Xh| := by
      refine abs_sub_ge_of_deriv_le (f := Fsum S M μ (F.step N)) (p := F.bandLo μ - δ3) (q := F.bandHi μ + δ3) (c := c2) ?_ ?_ ?_ hc2.le hP3 hXh
      · exact (Fsum_continuousOn hS hμ).mono (Icc_subset_Icc (by linarith) (by linarith))
      · intro z hz
        exact (Fsum_hasDerivAt hS hμ (x := z) ⟨by linarith [hz.1], by linarith [hz.2]⟩).differentiableAt
      · intro z hz
        rw [(Fsum_hasDerivAt hS hμ (x := z) ⟨by linarith [hz.1], by linarith [hz.2]⟩).deriv]
        linarith [hslope z (Ioo_subset_Icc_self hz)]
    have hFX : Fsum S M μ (F.step N) Xh = Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2) := hXeq
    rw [hFX] at hmvt
    have hq : |(invX0 F S (invDelta δ Cn c0) μ (Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2)) +
        (Dp M (fun r => xs F S δ (invDelta δ Cn c0) M μ M r (Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2)))).eval (F.step N)) - Xh| ≤
        Ck * F.step N ^ (M + 1) / c2 := by
      rw [le_div_iff₀ hc2]
      linarith
    calc _ ≤ |Xs k - Xh| + |Xh - (invX0 F S (invDelta δ Cn c0) μ (Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2)) +
        (Dp M (fun r => xs F S δ (invDelta δ Cn c0) M μ M r (Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2)))).eval (F.step N))| := by
          have := abs_add_le (Xs k - Xh) (Xh - (invX0 F S (invDelta δ Cn c0) μ (Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2)) +
            (Dp M (fun r => xs F S δ (invDelta δ Cn c0) M μ M r (Real.pi * F.step N * (((k : ℕ) : ℝ) + 1 / 2)))).eval (F.step N)))
          simpa using this
      _ ≤ Cc * F.step N ^ (M + 1) + Ck * F.step N ^ (M + 1) / c2 := by
          refine add_le_add hdist ?_
          rw [abs_sub_comm]; exact hq
      _ = (Cc + Ck / c2) * F.step N ^ (M + 1) := by ring
  · intro μ hμ y hy
    beta_reduce
    have h0 : xs F S δ (invDelta δ Cn c0) M μ 0 0 y = invX0 F S (invDelta δ Cn c0) μ y := by simp [xs, st]
    have h1 : xs F S δ (invDelta δ Cn c0) M μ 1 1 y = -(invC F S δ (invDelta δ Cn c0) 1 0 μ y) / invC F S δ (invDelta δ Cn c0) 0 1 μ y :=
      st_one M _ _ hM
    rw [h0, h1, ctx.invC_zero, ctx.invC_one hμ 0 hy, neg_div]
  · intro hM2 μ hμ y hy
    beta_reduce
    have h0 : xs F S δ (invDelta δ Cn c0) M μ 0 0 y = invX0 F S (invDelta δ Cn c0) μ y := by simp [xs, st]
    have h1 : xs F S δ (invDelta δ Cn c0) M μ 1 1 y = -(invC F S δ (invDelta δ Cn c0) 1 0 μ y) / invC F S δ (invDelta δ Cn c0) 0 1 μ y :=
      st_one M _ _ hM
    have h2 : xs F S δ (invDelta δ Cn c0) M μ 2 2 y = -(invC F S δ (invDelta δ Cn c0) 2 0 μ y +
        invC F S δ (invDelta δ Cn c0) 1 1 μ y * xs F S δ (invDelta δ Cn c0) M μ 1 1 y +
        invC F S δ (invDelta δ Cn c0) 0 2 μ y * xs F S δ (invDelta δ Cn c0) M μ 1 1 y ^ 2) / invC F S δ (invDelta δ Cn c0) 0 1 μ y :=
      st_two M _ _ hM2
    rw [h0, h2, ctx.invC_zero, ctx.invC_one hμ 0 hy, ctx.invC_one hμ 1 hy, ctx.invC_two hμ (Nat.zero_le _) hy]

end Main

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.invCoeffs_of_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.invCoeffs_of_slope

end FormalResearch.JacobiEigenvectors.TheoremA
