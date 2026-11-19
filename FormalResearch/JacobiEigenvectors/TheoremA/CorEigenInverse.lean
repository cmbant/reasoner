module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.CorEigenCount

/-!
# Paper J, Layer 2: cor:eigen (b) level equation and (c) first-order gaps (L2.E)

Source: Paper J `thmA.tex`, proof of `cor:eigen`, Steps 4 and 5; statements `InvLevel`, `CorEigenGap1` of `TheoremA/EigenvalueStatements.lean` (`eq:cor-inv`, `eq:cor-err`, `eq:cor-gap`).
Chain of lemmas: `CorEigenBase.lean` (B1--B5).

## Proved here (axiom-pinned)

* `tail_bound`: `|sum_{j <= M} h^j f_j - f_0| <= M C h` for `|f_j| <= C`, `0 < h <= 1`.
* `slope_near_band`: `S_0' <= -3 c_0/2` on `[X_s^- - delta', X_s^+ + delta']` when `Cn delta' <= c_0/2` (Lipschitz `S_0'`, `M >= 1`).
* `invLevel_of_slope : InvLevel F K M S delta` (**cor:eigen (b), part (ii)**, and the first conjunct `-S_0' >= 2 c_0` of part (i) is the input `BandSlope`): `delta' = min(delta/2, c_0/(2(|Cn|+1)))`,
  `-partial_X F_M >= c_0` on `I'`, the level equation `F_M(hat X_k, h) = y_k` has exactly one root in `I'` (intermediate value theorem with `S_0(X_s^+) = 0`, `S_0(X_s^-) = pi L`,
  `0 < y_k < pi L`; uniqueness from the strict decrease), and `|X_k - hat X_k| <= (|C|/c_0) h^{M+1}` (Step 0 puts `X_k` in `I'`, mean value theorem).
* `corEigenGap1_of_slope` (**cor:eigen (c), first part**, `CorEigenGap1`): from the level equation with `M = 1` and the mean value theorem for `F_1(., h)` between the roots `hat X_k > hat X_{k+1}`:
  `X_k - X_{k+1} = pi h/(-F_1'(xi))`, `-F_1'(xi) in [c, 2 Cn + 1]`, and `|(-F_1'(xi)) - (-S_0'(x_0(y_k)))| <= C h` (Lipschitz `S_0'`, `|xi - x_0(y_k)| <= C h`).  This avoids `x_1` altogether
  (the paper's route through `x_1 in C^1` is not needed for the first part).  Constants: `c_1 = pi/(2(2|Cn|+1))`, `C_2 = pi/c + 2(|Cc|+1)`.

## Differences from the paper

* Premises of the theorems here: `0 < delta` (F-BB-1, now also a premise of the frozen statements) and `BandSlope` (F-BB-2; discharged from the windows in `Assembly/CorEigen.lean`, `bandSlope_of_layer4`).  `delta' <= delta/2` (so that `I'` lies in the interior of the smoothness domain and `deriv` is the two-sided derivative); `InvLevel` only asks `delta' <= delta`.

## Not formalised (exact missing statements)

* `InvCoeffs` and the edge values of `InvS0` are proved in `InvCoeffs.lean` and `ActionDerivativeEdgeS0.lean`, and bundled in `CorEigenInverseSlope.lean` (`corEigenInverse_of_slope`) under `0 < delta` and `BandSlope`.
* Nothing of cor:eigen (a)-(d) remains modulo the Layer-4 chart inputs: `corEigen_proved` (`Assembly/CorEigen.lean`) proves the frozen `CorEigen` (with `0 < delta`) from `Layer4Inputs`; here `BandSlope` is still an explicit premise of the theorems of this file.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting

variable {Par : Type*} [TopologicalSpace Par]

/-- The truncated action `F_M(X, h) = sum_{j <= M} h^j S_j(X)`. -/
def Fsum (S : ℕ → Par → ℝ → ℝ) (M : ℕ) (μ : Par) (h : ℝ) (X : ℝ) : ℝ := ∑ j ∈ range (M + 1), h ^ j * S j μ X

/-- A sum `sum_{j <= M} h^j f_j` with `|f_j| <= C` is within `M C h` of `f_0` (`0 < h <= 1`). -/
lemma tail_bound {f : ℕ → ℝ} {C h : ℝ} (M : ℕ) (hh : 0 < h) (h1 : h ≤ 1) (hf : ∀ j ≤ M, |f j| ≤ C) :
    |∑ j ∈ range (M + 1), h ^ j * f j - f 0| ≤ M * C * h := by
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, add_sub_cancel_right]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ range M, |h ^ (j + 1) * f (j + 1)| ≤ ∑ j ∈ range M, C * h := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        have hj' : j + 1 ≤ M := Finset.mem_range.mp hj
        rw [abs_mul, abs_of_pos (pow_pos hh _)]
        calc h ^ (j + 1) * |f (j + 1)| ≤ h * C :=
              mul_le_mul (pow_le_of_le_one hh.le h1 (Nat.succ_ne_zero j)) (hf _ hj') (abs_nonneg _) hh.le
          _ = C * h := by ring
    _ = M * C * h := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

section Level

variable {F : SymbolFamily Par} {K : Set Par} {S : ℕ → Par → ℝ → ℝ} {M : ℕ} {δ Cn : ℝ}

lemma SmoothExt.mono_C {C' : ℝ} (hS : SmoothExt F K M S δ Cn) (h : Cn ≤ C') : SmoothExt F K M S δ C' :=
  fun μ hμ j hj => ⟨(hS μ hμ j hj).1, fun i hi x hx => ((hS μ hμ j hj).2 i hi x hx).trans h⟩

lemma SmoothExt.val_bound (hS : SmoothExt F K M S δ Cn) {μ : Par} (hμ : μ ∈ K) {j : ℕ} (hj : j ≤ M) {x : ℝ}
    (hx : x ∈ Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) : |S j μ x| ≤ Cn := by
  have := (hS μ hμ j hj).2 0 (Nat.zero_le _) x hx
  simpa using this

lemma SmoothExt.continuousOn_j (hS : SmoothExt F K M S δ Cn) {μ : Par} (hμ : μ ∈ K) {j : ℕ} (hj : j ≤ M) :
    ContinuousOn (S j μ) (Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) := (hS μ hμ j hj).1.continuousOn

lemma Fsum_hasDerivAt (hS : SmoothExt F K M S δ Cn) {μ : Par} (hμ : μ ∈ K) {h x : ℝ}
    (hx : x ∈ Ioo (F.bandLo μ - δ) (F.bandHi μ + δ)) :
    HasDerivAt (Fsum S M μ h) (∑ j ∈ range (M + 1), h ^ j * deriv (S j μ) x) x := by
  unfold Fsum
  exact HasDerivAt.fun_sum (fun j hj => ((hS.diffAt hμ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hx).hasDerivAt).const_mul (h ^ j))

lemma Fsum_continuousOn (hS : SmoothExt F K M S δ Cn) {μ : Par} (hμ : μ ∈ K) {h : ℝ} :
    ContinuousOn (Fsum S M μ h) (Icc (F.bandLo μ - δ) (F.bandHi μ + δ)) := by
  unfold Fsum
  exact continuousOn_finset_sum _ (fun j hj => continuousOn_const.mul (hS.continuousOn_j hμ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))))

/-- Near the band the slope of `S_0` is at most `-3 c_0 / 2` (needs `M >= 1`: `S_0'` is `Cn`-Lipschitz). -/
lemma slope_near_band (hS : SmoothExt F K M S δ Cn) (hM : 1 ≤ M) {μ : Par} (hμ : μ ∈ K) (hδ : 0 < δ) (hlt : F.bandLo μ < F.bandHi μ)
    {c0 δ' : ℝ} (hδ'0 : 0 < δ') (hδ'δ : δ' < δ) (hCn : Cn * δ' ≤ c0 / 2)
    (hsl : ∀ X ∈ Icc (F.bandLo μ) (F.bandHi μ), 2 * c0 ≤ -deriv (S 0 μ) X) {X : ℝ}
    (hX : X ∈ Icc (F.bandLo μ - δ') (F.bandHi μ + δ')) : deriv (S 0 μ) X ≤ -(3 * c0 / 2) := by
  have hCn0 : 0 ≤ Cn := by
    have := hS.val_bound hμ (Nat.zero_le _) (x := F.bandLo μ) ⟨by linarith, by linarith⟩
    exact (abs_nonneg _).trans this
  have hAB : F.bandLo μ - δ < F.bandHi μ + δ := by linarith
  set Xc := clampB (F.bandLo μ) (F.bandHi μ) X with hXc
  have hcm := clampB_mem hlt.le X
  have hd := clampB_dist hlt.le hδ'0.le hX.1 hX.2
  rw [← hXc] at hd hcm
  have hXI : X ∈ Ioo (F.bandLo μ - δ) (F.bandHi μ + δ) := ⟨by linarith [hX.1], by linarith [hX.2]⟩
  have hcI : Xc ∈ Ioo (F.bandLo μ - δ) (F.bandHi μ + δ) := ⟨by linarith [hcm.1], by linarith [hcm.2]⟩
  have hl := hS.deriv_lip hμ (Nat.zero_le _) hM hAB hXI hcI
  have h1 := hsl Xc hcm
  have h2 : Cn * |X - Xc| ≤ c0 / 2 := (mul_le_mul_of_nonneg_left hd hCn0).trans hCn
  have := (abs_le.mp (hl.trans h2)).2
  linarith

end Level

section Level2

variable {F : SymbolFamily Par} {K : Set Par} {S : ℕ → Par → ℝ → ℝ} {M : ℕ} {δ Cn : ℝ}

/-- **cor:eigen (b), parts (i) first conjunct and (ii)** (`InvLevel`): the truncated action `F_M(., h)` is strictly decreasing on `I'` with `-F_M' >= c_0`, and its level equation at
`y_k` has exactly one solution in `I'`, within `(|C|/c_0) h^{M+1}` of `X_k`.  Hypotheses: `M >= 1`, `0 < delta` (F-BB-1), `BandSlope` (F-BB-2). -/
theorem invLevel_of_slope (hK : IsCompact K) (hH : HypOn F K) (hD : DM F K M) (hM : 1 ≤ M)
    (hδ : 0 < δ) (hS : SmoothExt F K M S δ Cn) {hM' C : ℝ} (hR : EigenRule F K M S hM' C) (hA : ActionFormula F K S) (hsl : BandSlope F K S) :
    InvLevel F K M S δ := by
  obtain ⟨c0, hc0, hsl⟩ := hsl
  have hD0 := dm_zero_of_dm F K M hK hD
  obtain ⟨Cz, hz0, hzp, hzero⟩ := stepZeroD0 F K hK hH hD0
  obtain ⟨hMpos, hrule⟩ := hR
  have hlt := bandLo_lt_bandHi F K M hH hD
  obtain hS' := hS.mono_C (le_abs_self Cn)
  set Cn' : ℝ := |Cn| with hCn'
  have hCn0 : 0 ≤ Cn' := abs_nonneg _
  set Q : ℝ := (M : ℝ) * Cn' + 1 with hQ
  have hQpos : 0 < Q := by positivity
  set δ' : ℝ := min (δ / 2) (c0 / (2 * (Cn' + 1))) with hδ'
  have hδ'pos : 0 < δ' := lt_min (by positivity) (by positivity)
  have hδ'δ : δ' < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hCnδ' : Cn' * δ' ≤ c0 / 2 := by
    calc Cn' * δ' ≤ Cn' * (c0 / (2 * (Cn' + 1))) := mul_le_mul_of_nonneg_left (min_le_right _ _) hCn0
      _ ≤ c0 / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  set η : ℝ := min δ' 1 with hη
  have hηpos : 0 < η := lt_min hδ'pos one_pos
  refine ⟨δ', c0, |C| / c0, min (min hM' hz0) (min (δ' / (|Cz| + 1)) (min 1 (c0 * η / (2 * Q)))),
    hδ'pos, hδ'δ.le, hc0, lt_min (lt_min hMpos hzp) (lt_min (div_pos hδ'pos (by positivity)) (lt_min one_pos (by positivity))), ?_⟩
  intro μ hμ N hN
  have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  set h := F.step N with hh
  have hN1 : h ≤ hM' := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hN2 : h ≤ hz0 := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hN3 : h ≤ δ' / (|Cz| + 1) := hN.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hN4 : h ≤ 1 := hN.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hN5 : h ≤ c0 * η / (2 * Q) := hN.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hCzh : |Cz| * h ≤ δ' := by
    rw [le_div_iff₀ (by positivity)] at hN3
    nlinarith [abs_nonneg Cz]
  have hMh : (M : ℝ) * Cn' * h ≤ c0 * η / 2 := by
    have h5 : Q * h ≤ c0 * η / 2 := by
      rw [le_div_iff₀ (by positivity)] at hN5
      linarith
    have : (M : ℝ) * Cn' * h ≤ Q * h := by
      apply mul_le_mul_of_nonneg_right _ hpos.le
      rw [hQ]; linarith
    linarith
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηδ : η ≤ δ' := min_le_left _ _
  have hlth := hlt μ hμ
  have hAB : F.bandLo μ - δ < F.bandHi μ + δ := by linarith
  set lo := F.bandLo μ with hlo
  set hi := F.bandHi μ with hhi
  have hI'sub : Icc (lo - δ') (hi + δ') ⊆ Ioo (lo - δ) (hi + δ) := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hI'subD : Icc (lo - δ') (hi + δ') ⊆ Icc (lo - δ) (hi + δ) := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- slope of S_0 near the band
  have hs0 : ∀ X ∈ Icc (lo - δ') (hi + δ'), deriv (S 0 μ) X ≤ -(3 * c0 / 2) := fun X hX =>
    slope_near_band hS' hM hμ hδ hlth hδ'pos hδ'δ hCnδ' (hsl μ hμ) hX
  -- slope of F
  have hFder : ∀ X ∈ Icc (lo - δ') (hi + δ'), c0 ≤ -∑ j ∈ range (M + 1), h ^ j * deriv (S j μ) X := by
    intro X hX
    have hXI := hI'sub hX
    have := tail_bound (f := fun j => deriv (S j μ) X) (C := Cn') M hpos hN4 (fun j hj => hS'.deriv_bound hμ hj hXI)
    have hb := (abs_le.mp this).2
    have h0 := hs0 X hX
    beta_reduce at hb
    have h3 := mul_le_mul_of_nonneg_left hη1 hc0.le
    linarith
  refine ⟨hFder, ?_⟩
  intro Xs Um hE k
  have hcontS0 : ContinuousOn (S 0 μ) (Icc (lo - δ') (hi + δ')) := (hS'.continuousOn_j hμ (Nat.zero_le _)).mono hI'subD
  have hanti0 : StrictAntiOn (S 0 μ) (Icc (lo - δ') (hi + δ')) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) hcontS0 (fun z hz => ?_)
    rw [interior_Icc] at hz
    have := hs0 z (Ioo_subset_Icc_self hz)
    linarith
  have hderS0 : ∀ z ∈ Ioo (lo - δ') (hi + δ'), DifferentiableAt ℝ (S 0 μ) z := fun z hz =>
    hS'.diffAt hμ (Nat.zero_le _) (hI'sub (Ioo_subset_Icc_self hz))
  have hFcont := (Fsum_continuousOn (h := h) hS' hμ).mono hI'subD
  have hFder' : ∀ z ∈ Ioo (lo - δ') (hi + δ'), HasDerivAt (Fsum S M μ h) (∑ j ∈ range (M + 1), h ^ j * deriv (S j μ) z) z :=
    fun z hz => Fsum_hasDerivAt hS' hμ (hI'sub (Ioo_subset_Icc_self hz))
  have hFdiff : ∀ z ∈ Ioo (lo - δ') (hi + δ'), DifferentiableAt ℝ (Fsum S M μ h) z := fun z hz => (hFder' z hz).differentiableAt
  have hFderle : ∀ z ∈ Ioo (lo - δ') (hi + δ'), deriv (Fsum S M μ h) z ≤ -c0 := by
    intro z hz
    rw [(hFder' z hz).deriv]
    have := hFder z (Ioo_subset_Icc_self hz)
    linarith
  have hFsl : ∀ x ∈ Icc (lo - δ') (hi + δ'), ∀ y ∈ Icc (lo - δ') (hi + δ'), c0 * |x - y| ≤ |Fsum S M μ h x - Fsum S M μ h y| :=
    fun x hx y hy => abs_sub_ge_of_deriv_le hFcont hFdiff hFderle hc0.le hx hy
  -- the nominal point
  set yk : ℝ := Real.pi * h * (((k : ℕ) : ℝ) + 1 / 2) with hyk
  have hL : h * ((N : ℝ) + 1) = F.L := step_mul_succ_aux F N
  have hyk0 : 0 < yk := by positivity
  have hykL : yk < Real.pi * F.L := by
    have hk1 : ((k : ℕ) : ℝ) + 1 / 2 < (N : ℝ) + 1 := by
      have : ((k : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp k.isLt
      linarith
    rw [← hL, hyk]
    have := mul_lt_mul_of_pos_left hk1 (mul_pos Real.pi_pos hpos)
    nlinarith
  -- values at the ends of I'
  have hS0hi : S 0 μ hi = 0 := by rw [hA μ hμ _ ⟨hlth.le, le_rfl⟩]; exact actionS0_bandHi F K hH hD0 hμ
  have hS0lo : S 0 μ lo = Real.pi * F.L := by rw [hA μ hμ _ ⟨le_rfl, hlth.le⟩]; exact actionS0_bandLo F K hH hD0 hμ
  have hmemhi : hi ∈ Icc (lo - δ') (hi + δ') := ⟨by linarith, by linarith⟩
  have hmemlo : lo ∈ Icc (lo - δ') (hi + δ') := ⟨by linarith, by linarith⟩
  have hmemhi' : hi + δ' ∈ Icc (lo - δ') (hi + δ') := ⟨by linarith, by linarith⟩
  have hmemlo' : lo - δ' ∈ Icc (lo - δ') (hi + δ') := ⟨by linarith, by linarith⟩
  have hdhi : (3 * c0 / 2) * δ' ≤ S 0 μ hi - S 0 μ (hi + δ') := by
    have h1 := abs_sub_ge_of_deriv_le (c := 3 * c0 / 2) hcontS0 hderS0 (fun z hz => hs0 z (Ioo_subset_Icc_self hz)) (by positivity) hmemhi' hmemhi
    have h2 : S 0 μ (hi + δ') < S 0 μ hi := hanti0 hmemhi hmemhi' (by linarith)
    have e1 : |hi + δ' - hi| = δ' := by rw [add_sub_cancel_left, abs_of_pos hδ'pos]
    have e2 : |S 0 μ (hi + δ') - S 0 μ hi| = S 0 μ hi - S 0 μ (hi + δ') := by rw [abs_of_neg (by linarith), neg_sub]
    rw [e1, e2] at h1
    exact h1
  have hdlo : (3 * c0 / 2) * δ' ≤ S 0 μ (lo - δ') - S 0 μ lo := by
    have h1 := abs_sub_ge_of_deriv_le (c := 3 * c0 / 2) hcontS0 hderS0 (fun z hz => hs0 z (Ioo_subset_Icc_self hz)) (by positivity) hmemlo' hmemlo
    have h2 : S 0 μ lo < S 0 μ (lo - δ') := hanti0 hmemlo' hmemlo (by linarith)
    have e1 : |lo - δ' - lo| = δ' := by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hδ'pos]
    have e2 : |S 0 μ (lo - δ') - S 0 μ lo| = S 0 μ (lo - δ') - S 0 μ lo := abs_of_pos (by linarith)
    rw [e1, e2] at h1
    exact h1
  have hFhi : Fsum S M μ h (hi + δ') ≤ S 0 μ (hi + δ') + (M : ℝ) * Cn' * h := by
    have := tail_bound (f := fun j => S j μ (hi + δ')) (C := Cn') M hpos hN4 (fun j hj => hS'.val_bound hμ hj (hI'subD hmemhi'))
    have := (abs_le.mp this).2
    unfold Fsum
    beta_reduce at this
    linarith
  have hFlo : S 0 μ (lo - δ') - (M : ℝ) * Cn' * h ≤ Fsum S M μ h (lo - δ') := by
    have := tail_bound (f := fun j => S j μ (lo - δ')) (C := Cn') M hpos hN4 (fun j hj => hS'.val_bound hμ hj (hI'subD hmemlo'))
    have := (abs_le.mp this).1
    unfold Fsum
    beta_reduce at this
    linarith
  have hcd : c0 * η ≤ c0 * δ' := mul_le_mul_of_nonneg_left hηδ hc0.le
  have hcd0 : 0 < c0 * δ' := mul_pos hc0 hδ'pos
  have hlow1 : Fsum S M μ h (hi + δ') < yk := by
    linarith
  have hlow2 : yk < Fsum S M μ h (lo - δ') := by
    linarith
  have hivt := intermediate_value_Icc' (show lo - δ' ≤ hi + δ' by linarith) hFcont
  obtain ⟨Xh, hXh, hXhe⟩ := hivt ⟨hlow1.le, hlow2.le⟩
  have hFanti : StrictAntiOn (Fsum S M μ h) (Icc (lo - δ') (hi + δ')) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) hFcont (fun z hz => ?_)
    rw [interior_Icc] at hz
    have := hFderle z hz
    linarith
  -- the eigenvalue lies in I'
  obtain ⟨hz1, hz2⟩ := hzero μ hμ N hN2 Xs Um hE k
  have hXk : Xs k ∈ Icc (lo - δ') (hi + δ') := by
    have hle : Cz * h ≤ |Cz| * h := mul_le_mul_of_nonneg_right (le_abs_self _) hpos.le
    have hle2 : -(Cz * h) ≤ |Cz| * h := by
      have := mul_le_mul_of_nonneg_right (neg_le_abs Cz) hpos.le
      linarith
    exact ⟨by linarith, by linarith⟩
  have hr := hrule μ hμ N hN1 Xs Um hE k
  have hrF : |Fsum S M μ h (Xs k) - yk| ≤ C * h ^ (M + 1) := hr
  refine ⟨Xh, hXh, ⟨hXhe, fun Y hY hYe => ?_⟩, ?_⟩
  · exact hFanti.injOn hY hXh (hYe.trans hXhe.symm)
  · have h1 := hFsl _ hXk _ hXh
    have h2 : |Fsum S M μ h (Xs k) - Fsum S M μ h Xh| ≤ |C| * h ^ (M + 1) := by
      rw [hXhe]
      exact hrF.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hpos.le _))
    rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
    calc |Xs k - Xh| * c0 = c0 * |Xs k - Xh| := by ring
      _ ≤ _ := h1.trans h2

end Level2

section Gap

variable {F : SymbolFamily Par} {K : Set Par} {S : ℕ → Par → ℝ → ℝ} {δ Cn : ℝ}

/-- **cor:eigen (c), first part** (`CorEigenGap1`): `X_k - X_{k+1} = pi h/(-S_0'(x_0(y_k))) + O(h^2)` and `c h <= X_k - X_{k+1} <= C h`, from the level equation of `(b)` with `M = 1`
(mean value theorem for `F_1(., h)` between the two roots; no `x_1` is needed).  Hypotheses: `(D_1)`, `0 < delta` (F-BB-1), `BandSlope` (F-BB-2). -/
theorem corEigenGap1_of_slope (hK : IsCompact K) (hH : HypOn F K) (hD : DM F K 1)
    (hδ : 0 < δ) (hS : SmoothExt F K 1 S δ Cn) {hM' C : ℝ} (hR : EigenRule F K 1 S hM' C) (hA : ActionFormula F K S) (hsl : BandSlope F K S)
    (x0 : Par → ℝ → ℝ) (hx0 : ∀ μ ∈ K, ∀ y ∈ Icc 0 (Real.pi * F.L), x0 μ y ∈ Icc (F.bandLo μ) (F.bandHi μ) ∧ S 0 μ (x0 μ y) = y) :
    ∃ C1 c1 C2 h0 : ℝ, 0 < h0 ∧ 0 < c1 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ i j : Fin (N + 1), (j : ℕ) = (i : ℕ) + 1 →
          |(X i - X j) - Real.pi * F.step N / (-deriv (S 0 μ) (x0 μ (Real.pi * F.step N * ((i : ℕ) + 1 / 2))))| ≤ C1 * F.step N ^ 2 ∧
          c1 * F.step N ≤ X i - X j ∧ X i - X j ≤ C2 * F.step N := by
  obtain ⟨δ', c, Cc, hs, hδ'0, hδ'δ, hc, hs0, hlev⟩ := invLevel_of_slope hK hH hD le_rfl hδ hS hR hA hsl
  obtain ⟨c0, hc0, hsl0⟩ := hsl
  obtain hS' := hS.mono_C (le_abs_self Cn)
  set Cn' : ℝ := |Cn| with hCn'
  have hCn0 : 0 ≤ Cn' := abs_nonneg _
  have hlt := bandLo_lt_bandHi F K 1 hH hD
  set U : ℝ := 2 * Cn' + 1 with hU
  have hUpos : 0 < U := by positivity
  set Cc' : ℝ := |Cc| + 1 with hCc'
  have hCc'pos : 0 < Cc' := by positivity
  set E : ℝ := Cn' * (Real.pi / c + Cn' / c + 1) with hE
  have hE0 : 0 ≤ E := by positivity
  refine ⟨2 * Cc' + Real.pi * E / (2 * c0 * c), Real.pi / (2 * U), Real.pi / c + 2 * Cc',
    min hs (min 1 (Real.pi / (4 * U * Cc'))), lt_min hs0 (lt_min one_pos (by positivity)), by positivity, ?_⟩
  intro μ hμ N hN X Um hE' i j hij
  have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  set h := F.step N with hh
  have hN1 : h ≤ hs := hN.trans (min_le_left _ _)
  have hN2 : h ≤ 1 := hN.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hN3 : h ≤ Real.pi / (4 * U * Cc') := hN.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hder, hex⟩ := hlev μ hμ N hN1
  obtain ⟨Xi, hXi, ⟨hXie, -⟩, hXierr⟩ := hex X Um hE' i
  obtain ⟨Xj, hXj, ⟨hXje, -⟩, hXjerr⟩ := hex X Um hE' j
  set lo := F.bandLo μ with hlo
  set hi := F.bandHi μ with hhi
  have hlth := hlt μ hμ
  have hAB : lo - δ < hi + δ := by linarith
  have hI'o : Ioo (lo - δ') (hi + δ') ⊆ Ioo (lo - δ) (hi + δ) := Ioo_subset_Ioo (by linarith) (by linarith)
  have hI'D : Icc (lo - δ') (hi + δ') ⊆ Icc (lo - δ) (hi + δ) := Icc_subset_Icc (by linarith) (by linarith)
  have hbandI' : Icc lo hi ⊆ Icc (lo - δ') (hi + δ') := Icc_subset_Icc (by linarith) (by linarith)
  have hsum2 : ∀ f : ℕ → ℝ, ∑ j ∈ range (1 + 1), h ^ j * f j = f 0 + h * f 1 := by
    intro f; simp [Finset.sum_range_succ]
  set Fh := Fsum S 1 μ h with hFh
  have hFcont : ContinuousOn Fh (Icc (lo - δ') (hi + δ')) := (Fsum_continuousOn (h := h) hS' hμ).mono hI'D
  have hFderv : ∀ z ∈ Ioo (lo - δ') (hi + δ'), HasDerivAt Fh (∑ j ∈ range (1 + 1), h ^ j * deriv (S j μ) z) z :=
    fun z hz => Fsum_hasDerivAt hS' hμ (hI'o hz)
  have hFle : ∀ z ∈ Ioo (lo - δ') (hi + δ'), deriv Fh z ≤ -c := by
    intro z hz
    rw [(hFderv z hz).deriv]
    have := hder z (Ioo_subset_Icc_self hz)
    linarith
  have hFdiff : ∀ z ∈ Ioo (lo - δ') (hi + δ'), DifferentiableAt ℝ Fh z := fun z hz => (hFderv z hz).differentiableAt
  have hFsl : ∀ x ∈ Icc (lo - δ') (hi + δ'), ∀ y ∈ Icc (lo - δ') (hi + δ'), c * |x - y| ≤ |Fh x - Fh y| :=
    fun x hx y hy => abs_sub_ge_of_deriv_le hFcont hFdiff hFle hc.le hx hy
  have hFanti : StrictAntiOn Fh (Icc (lo - δ') (hi + δ')) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) hFcont (fun z hz => ?_)
    rw [interior_Icc] at hz
    have := hFle z hz
    linarith
  -- nominal points
  have hk1 : ∀ k : Fin (N + 1), Real.pi * h * (((k : ℕ) : ℝ) + 1 / 2) ∈ Icc (0 : ℝ) (Real.pi * F.L) := by
    intro k
    have hL : h * ((N : ℝ) + 1) = F.L := step_mul_succ_aux F N
    have hk1 : ((k : ℕ) : ℝ) + 1 / 2 ≤ (N : ℝ) + 1 := by
      have : ((k : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp k.isLt
      linarith only [this]
    refine ⟨by positivity, ?_⟩
    rw [← hL]
    have := mul_le_mul_of_nonneg_left hk1 (mul_nonneg Real.pi_pos.le hpos.le)
    linarith only [this]
  have hyd : Real.pi * h * (((j : ℕ) : ℝ) + 1 / 2) - Real.pi * h * (((i : ℕ) : ℝ) + 1 / 2) = Real.pi * h := by
    rw [hij]; push_cast; ring
  obtain ⟨hZm, hZe⟩ := hx0 μ hμ _ (hk1 i)
  set Z := x0 μ (Real.pi * h * (((i : ℕ) : ℝ) + 1 / 2)) with hZ
  have hXiF : Fh Xi = Real.pi * h * (((i : ℕ) : ℝ) + 1 / 2) := hXie
  have hXjF : Fh Xj = Real.pi * h * (((j : ℕ) : ℝ) + 1 / 2) := hXje
  have hXji : Xj < Xi := by
    by_contra hcon
    have hle : Xi ≤ Xj := not_lt.mp hcon
    have := hFanti.antitoneOn hXi hXj hle
    rw [hXiF, hXjF] at this
    linarith only [this, hyd, mul_pos Real.pi_pos hpos]
  -- the mean value point
  obtain ⟨ξ, hξ, hξd⟩ := exists_deriv_eq_slope Fh hXji (hFcont.mono (Icc_subset_Icc (by linarith [hXj.1]) (by linarith [hXi.2])))
    (fun z hz => (hFdiff z ⟨by linarith [hXj.1, hz.1], by linarith [hXi.2, hz.2]⟩).differentiableWithinAt)
  have hξI : ξ ∈ Ioo (lo - δ') (hi + δ') := ⟨by linarith [hXj.1, hξ.1], by linarith [hXi.2, hξ.2]⟩
  have hξD : ξ ∈ Ioo (lo - δ) (hi + δ) := hI'o hξI
  set G := Xi - Xj with hG
  have hGpos : 0 < G := by rw [hG]; linarith
  set P := -deriv Fh ξ with hP
  have hPG : P * G = Real.pi * h := by
    rw [hP, hξd, hXiF, hXjF]
    have : Real.pi * h * (((i : ℕ) : ℝ) + 1 / 2) - Real.pi * h * (((j : ℕ) : ℝ) + 1 / 2) = -(Real.pi * h) := by
      linarith only [hyd]
    rw [this]
    field_simp
  have hPc : c ≤ P := by rw [hP]; linarith [hFle ξ hξI]
  have hPexp : P = -(deriv (S 0 μ) ξ + h * deriv (S 1 μ) ξ) := by
    rw [hP, (hFderv ξ hξI).deriv, hsum2 (fun j => deriv (S j μ) ξ)]
  have hd0 := hS'.deriv_bound hμ (Nat.zero_le 1) hξD
  have hd1 := hS'.deriv_bound hμ le_rfl hξD
  have hPU : P ≤ U := by
    rw [hPexp]
    have h0 := (abs_le.mp hd0).2
    have h0' := (abs_le.mp hd0).1
    have h1 := (abs_le.mp hd1).1
    have h1' := (abs_le.mp hd1).2
    have : h * Cn' ≤ Cn' := mul_le_of_le_one_left hCn0 hN2
    linarith only [h0', mul_le_mul_of_nonneg_left h1 hpos.le, this, hU, hCn0]
  have hPpos : 0 < P := lt_of_lt_of_le hc hPc
  have hGeq : G = Real.pi * h / P := by field_simp; linarith
  have hGup : G ≤ Real.pi * h / c := by
    rw [hGeq]; exact div_le_div_of_nonneg_left (by positivity) hc hPc
  have hGlo : Real.pi * h / U ≤ G := by
    rw [hGeq]; exact div_le_div_of_nonneg_left (by positivity) hPpos hPU
  -- eigenvalue errors
  have herr : |(X i - X j) - G| ≤ 2 * Cc' * h ^ 2 := by
    have e1 : |X i - Xi| ≤ Cc * h ^ 2 := hXierr
    have e2 : |X j - Xj| ≤ Cc * h ^ 2 := hXjerr
    have hcc : Cc * h ^ 2 ≤ Cc' * h ^ 2 := by
      have : Cc ≤ Cc' := by rw [hCc']; linarith [le_abs_self Cc]
      exact mul_le_mul_of_nonneg_right this (sq_nonneg h)
    have : (X i - X j) - G = (X i - Xi) - (X j - Xj) := by rw [hG]; ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    linarith
  have hZD : Z ∈ Ioo (lo - δ) (hi + δ) := ⟨by linarith [hZm.1], by linarith [hZm.2]⟩
  have hZI' : Z ∈ Icc (lo - δ') (hi + δ') := hbandI' hZm
  have hXiZ : c * |Xi - Z| ≤ h * Cn' := by
    have h1 := hFsl _ hXi _ hZI'
    have h2 : Fh Z = Real.pi * h * (((i : ℕ) : ℝ) + 1 / 2) + h * S 1 μ Z := by
      rw [hFh]; unfold Fsum
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      have := hZe
      simp only [pow_zero, one_mul, pow_one, zero_add]
      rw [this]
    have h3 := hS'.val_bound hμ (le_refl 1) (hI'D hZI') (j := 1)
    rw [hXiF, h2] at h1
    have : |Real.pi * h * (((i : ℕ) : ℝ) + 1 / 2) - (Real.pi * h * (((i : ℕ) : ℝ) + 1 / 2) + h * S 1 μ Z)| = h * |S 1 μ Z| := by
      rw [show Real.pi * h * (((i : ℕ) : ℝ) + 1 / 2) - (Real.pi * h * (((i : ℕ) : ℝ) + 1 / 2) + h * S 1 μ Z) = -(h * S 1 μ Z) by ring,
        abs_neg, abs_mul, abs_of_pos hpos]
    rw [this] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h3 hpos.le)
  have hAP : |(-deriv (S 0 μ) Z) - P| ≤ h * E := by
    have hl := hS'.deriv_lip hμ (Nat.zero_le 1) le_rfl hAB hξD hZD
    have hξZ : |ξ - Z| ≤ Real.pi * h / c + h * Cn' / c := by
      have h1 : |ξ - Xi| ≤ G := by
        rw [abs_le]; constructor <;> linarith [hξ.1, hξ.2]
      have h2 : |Xi - Z| ≤ h * Cn' / c := by rw [le_div_iff₀ hc]; linarith
      calc |ξ - Z| = |(ξ - Xi) + (Xi - Z)| := by ring_nf
        _ ≤ |ξ - Xi| + |Xi - Z| := abs_add_le _ _
        _ ≤ G + h * Cn' / c := add_le_add h1 h2
        _ ≤ _ := by linarith
    have e : (-deriv (S 0 μ) Z) - P = (deriv (S 0 μ) ξ - deriv (S 0 μ) Z) + h * deriv (S 1 μ) ξ := by
      rw [hPexp]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have b1 : |deriv (S 0 μ) ξ - deriv (S 0 μ) Z| ≤ Cn' * (Real.pi * h / c + h * Cn' / c) :=
      hl.trans (mul_le_mul_of_nonneg_left hξZ hCn0)
    have b2 : |h * deriv (S 1 μ) ξ| ≤ h * Cn' := by
      rw [abs_mul, abs_of_pos hpos]; exact mul_le_mul_of_nonneg_left hd1 hpos.le
    have : Cn' * (Real.pi * h / c + h * Cn' / c) + h * Cn' = h * E := by rw [hE]; field_simp
    linarith
  have hAge : 2 * c0 ≤ -deriv (S 0 μ) Z := hsl0 μ hμ Z hZm
  have hAposv : 0 < -deriv (S 0 μ) Z := by linarith
  have hdiffGA : |G - Real.pi * h / (-deriv (S 0 μ) Z)| ≤ Real.pi * E / (2 * c0 * c) * h ^ 2 := by
    rw [hGeq]
    have e : Real.pi * h / P - Real.pi * h / (-deriv (S 0 μ) Z) = Real.pi * h * ((-deriv (S 0 μ) Z) - P) / (P * (-deriv (S 0 μ) Z)) := by
      rw [div_sub_div _ _ hPpos.ne' hAposv.ne']
      congr 1
      ring
    rw [e, abs_div, abs_mul, abs_of_pos (by positivity : 0 < Real.pi * h), abs_of_pos (mul_pos hPpos hAposv), div_le_iff₀ (mul_pos hPpos hAposv)]
    have h1 : 2 * c0 * c ≤ P * (-deriv (S 0 μ) Z) := by
      have := mul_le_mul hAge hPc hc.le hAposv.le
      linarith only [this]
    calc Real.pi * h * |(-deriv (S 0 μ) Z) - P| ≤ Real.pi * h * (h * E) := mul_le_mul_of_nonneg_left hAP (by positivity)
      _ = Real.pi * E * h ^ 2 := by ring
      _ = Real.pi * E / (2 * c0 * c) * h ^ 2 * (2 * c0 * c) := by field_simp
      _ ≤ Real.pi * E / (2 * c0 * c) * h ^ 2 * (P * (-deriv (S 0 μ) Z)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · have : (X i - X j) - Real.pi * h / (-deriv (S 0 μ) Z) = ((X i - X j) - G) + (G - Real.pi * h / (-deriv (S 0 μ) Z)) := by ring
    show |(X i - X j) - Real.pi * h / (-deriv (S 0 μ) Z)| ≤ (2 * Cc' + Real.pi * E / (2 * c0 * c)) * h ^ 2
    rw [this]
    refine (abs_add_le _ _).trans ?_
    have := add_le_add herr hdiffGA
    linarith
  · have h1 := (abs_le.mp herr).1
    have h2 : 2 * Cc' * h ^ 2 ≤ Real.pi * h / (2 * U) := by
      have : h * (4 * U * Cc') ≤ Real.pi := by rwa [le_div_iff₀ (by positivity)] at hN3
      have h3 : 2 * Cc' * h ^ 2 = h * (2 * Cc' * h) := by ring
      have h4 : Real.pi * h / (2 * U) = h * (Real.pi / (2 * U)) := by ring
      rw [h3, h4]
      apply mul_le_mul_of_nonneg_left _ hpos.le
      rw [le_div_iff₀ (by positivity)]
      linarith only [this]
    have h5 : Real.pi * h / U = 2 * (Real.pi * h / (2 * U)) := by field_simp
    show Real.pi / (2 * U) * h ≤ X i - X j
    have : Real.pi / (2 * U) * h = Real.pi * h / (2 * U) := by ring
    rw [this]
    linarith
  · have h1 := (abs_le.mp herr).2
    have h2 : 2 * Cc' * h ^ 2 ≤ 2 * Cc' * h :=
      mul_le_mul_of_nonneg_left (pow_le_of_le_one hpos.le hN2 (by norm_num)) (by positivity)
    have : Real.pi * h / c = Real.pi / c * h := by ring
    show X i - X j ≤ (Real.pi / c + 2 * Cc') * h
    linarith

end Gap

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.invLevel_of_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.invLevel_of_slope

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.corEigenGap1_of_slope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.corEigenGap1_of_slope

end FormalResearch.JacobiEigenvectors.TheoremA
