import FormalResearch.FourQubitEntropy.RenyiFullHsConst
import FormalResearch.FourQubitEntropy.RenyiFullDetChart
import FormalResearch.FourQubitEntropy.ThirdMoment

/-!
# `lem:fqe-hs-polynomial` (`HsSupporting`), proved

Paper E, `renyi_hs_analytic.tex`: at `q_u = 8/5` every four-point probability vector with `p ≤ 9/16`
satisfies `Λ_{(α,1/12,10/3)}(λ) ≤ h_{8/5}`, with equality only at HS.

Proof (the paper's): `det_reduction` replaces `λ` by a chart spectrum (same `p, t`, no smaller `H`);
`lowTilt_reduce` (`lem:fqe-low-tilt-reduction`, `ω = 12β = 1`) moves `(a,a,b,c)` to two equal pairs
`(a,b,c,c)`; `hsTilt_reduce` (`lem:fqe-hs-tilt`) moves `(a,b,c,c)` to the one-large spectrum
`(a,b,b,b) = olv x`; `PhiX_le` is the one-variable supporting inequality (curvature identity (HCJ),
tangent argument, uniform gap).  Equality: all steps are strict unless trivial, so `p, t` of `λ`
are those of HS; the sharp third-moment bound (`third_moment`) forces `λ` to be one-large with
`s = 1/3`.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open Set

theorem hsSpec_ne_zero {j : Fin 4} (hj : j ≠ 0) : hsSpec j = 1 / 6 := by
  fin_cases j
  · exact absurd rfl hj
  all_goals simp [hsSpec]

theorem isHsPerm_of_pattern {l : Fin 4 → ℝ} (i : Fin 4) (h0 : l i = 1 / 2)
    (h1 : ∀ j, j ≠ i → l j = 1 / 6) : IsHsPerm l := by
  refine ⟨Equiv.swap 0 i, fun k => ?_⟩
  by_cases hk : k = i
  · subst hk
    simp [hsSpec, h0]
  · have hne : Equiv.swap 0 i k ≠ 0 := by
      intro h
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
      exact hk h
    rw [h1 k hk, hsSpec_ne_zero hne]

theorem hsSpec_nonneg (i : Fin 4) : 0 ≤ hsSpec i := by
  fin_cases i <;> simp [hsSpec] <;> norm_num

theorem hsSpec_sum : ∑ i, hsSpec i = 1 := by
  simp [hsSpec, Fin.sum_univ_four]; norm_num

/-- A probability vector with `p = 1/3` and `t = 5/36` is a permutation of HS
(equality in the sharp third-moment bound). -/
theorem hs_of_pur_cub {l : Fin 4 → ℝ} (hl : IsProb4 l) (hp : pur l = 1 / 3) (ht : cub l = 5 / 36) :
    IsHsPerm l := by
  have hsq : Real.sqrt (4 * (1 / 12 : ℝ) / 3) = 1 / 3 := by
    rw [show 4 * (1 / 12 : ℝ) / 3 = (1 / 3) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hhs2 : ∑ i, hsSpec i ^ 2 = 1 / 4 + 1 / 12 := by
    simp [hsSpec, Fin.sum_univ_four]; norm_num
  have hhs3 : ∑ i, hsSpec i ^ 3 = 5 / 36 := by
    simp [hsSpec, Fin.sum_univ_four]; norm_num
  have T1 := third_moment hsSpec hsSpec_nonneg hsSpec_sum hhs2
  have T2 := third_moment l hl.1 hl.2 (x := 1 / 12) (by unfold pur at hp; linarith)
  have eq_hs := T1.2.2.1.2 (by
    refine ⟨0, ?_, ?_⟩
    · rw [hsq]; simp [hsSpec]; norm_num
    · intro j hj
      rw [hsq, hsSpec_ne_zero hj]; norm_num)
  have hl3 : ∑ i, l i ^ 3 = 5 / 36 := by unfold cub at ht; exact ht
  have eq_l : ∑ i, l i ^ 3 - 1 / 16 - 3 * (1 / 12) / 4 = (1 / 12 : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt 3 := by
    rw [hl3]
    rw [hhs3] at eq_hs
    exact eq_hs
  obtain ⟨i, hi, hj⟩ := T2.2.2.1.1 eq_l
  rw [hsq] at hi hj
  exact isHsPerm_of_pattern i (by rw [hi]; norm_num) (fun j hj' => by rw [hj j hj']; norm_num)

/-- A one-large spectrum of purity `≤ 9/16` is `olv x` for some `x ∈ [1,2]`. -/
theorem exists_x_of_oneLarge {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) (hs : a + 3 * b = 1)
    (hp : a ^ 2 + 3 * b ^ 2 ≤ 9 / 16) : ∃ x ∈ Icc (1 : ℝ) 2, olv x = ![a, b, b, b] := by
  have hb1 : 1 / 12 < b := by
    by_contra hle
    push Not at hle
    have ha : a = 1 - 3 * b := by linarith
    subst ha
    nlinarith
  have hr1 : 1 ≤ a / b := by rw [le_div_iff₀ hb]; linarith
  have hr9 : a / b < 9 := by
    rw [div_lt_iff₀ hb]; linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (a / b) ^ (1 / 5 : ℝ) := ⟨_, rfl⟩
  have hx5 : x ^ 5 = a / b := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hx1 : 1 ≤ x := by
    rw [hx]; exact Real.one_le_rpow hr1 (by norm_num)
  have hx2 : x ≤ 2 := by
    by_contra hgt
    push Not at hgt
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hgt.le 5
    rw [hx5] at this
    norm_num at this
    linarith
  refine ⟨x, ⟨hx1, hx2⟩, ?_⟩
  have hbne : b ≠ 0 := hb.ne'
  have hden : a / b + 3 = 1 / b := by
    field_simp; linarith
  funext i
  unfold olv
  rw [hx5, hden]
  fin_cases i <;> simp <;> field_simp

/-- **`lem:fqe-hs-polynomial`**: `HsSupporting`, proved. -/
theorem hsSupporting : HsSupporting := by
  intro l hl hp
  have hq1 : (1 : ℝ) < qU := by unfold qU; norm_num
  have hq2 : qU < 2 := by unfold qU; norm_num
  -- Step 1: determinant chart
  obtain ⟨μ, hμc, hpμ, hcμ, hHμ⟩ := det_reduction qU hq1 hq2 l hl
  have hL1 : Lam qU aU bU gU l ≤ Lam qU aU bU gU μ := by
    unfold Lam; rw [hpμ, hcμ]; linarith
  -- Step 2: low tilt, (a,a,b,c) -> (a,b,c,c)
  obtain ⟨ν, hνp, ⟨a, b, c, hc, hcb, hba, hνe⟩, hpν, hL2, hL2'⟩ :=
    lowTilt_reduce (q := qU) (β := bU) aU gU (by unfold qU; norm_num) (by unfold qU; norm_num)
      (by unfold bU; norm_num) (by unfold bU; norm_num) hμc
  have hνs : a + b + 2 * c = 1 := by
    obtain ⟨-, h⟩ := hνp
    rw [hνe] at h
    simp [Fin.sum_univ_four] at h
    linarith
  have hpν' : a ^ 2 + b ^ 2 + 2 * c ^ 2 ≤ 9 / 16 := by
    have : pur ν = a ^ 2 + b ^ 2 + 2 * c ^ 2 := by rw [hνe, pur_abcc]
    rw [← this, hpν, hpμ]; exact hp
  -- Step 3: HS tilt, (a,b,c,c) -> (a',b',b',b')
  have hsT := hsTilt_reduce aU gU hc hcb hba hνs hpν'
  obtain ⟨a', b', hb', hab', hs', hpν'', hL3, hL3'⟩ := hsT
  have hνeq : ν = ![a, b, c, c] := hνe
  rw [← hνeq] at hpν'' hL3 hL3'
  -- Step 4: the one-variable inequality
  have hpb : a' ^ 2 + 3 * b' ^ 2 ≤ 9 / 16 := by
    have : pur ![a', b', b', b'] = a' ^ 2 + 3 * b' ^ 2 := pur_abbb a' b'
    rw [← this, hpν'', hpν, hpμ]; exact hp
  have hbpos : 0 < b' := by
    rcases hb'.eq_or_lt with h | h
    · exfalso
      have ha : a' = 1 := by rw [← h] at hs'; linarith
      rw [← h, ha] at hpb
      norm_num at hpb
    · exact h
  obtain ⟨x, hx, hxo⟩ := exists_x_of_oneLarge hbpos hab' hs' hpb
  have hL4 : Lam qU aU bU gU ![a', b', b', b'] = PhiX aU x := by
    rw [← hxo]; exact Lam_olv (by linarith [hx.1])
  have hPhi := PhiX_le hx
  have hh : renyiSpec qU hsSpec = PhiX aU xs := PhiX_xs.symm
  constructor
  · rw [hh]
    have : Lam qU aU bU gU ν ≤ Lam qU aU bU gU ![a', b', b', b'] := hL3
    have h2 : Lam qU aU bU gU μ ≤ Lam qU aU bU gU ν := hL2
    linarith [hPhi.1]
  · intro heq
    rw [hh] at heq
    have h3 : Lam qU aU bU gU ν ≤ Lam qU aU bU gU ![a', b', b', b'] := hL3
    have h2 : Lam qU aU bU gU μ ≤ Lam qU aU bU gU ν := hL2
    have e4 : PhiX aU x = PhiX aU xs := by linarith [hPhi.1]
    have hxx : x = xs := hPhi.2 e4
    -- equality throughout
    have eνν' : Lam qU aU bU gU ν = Lam qU aU bU gU ![a', b', b', b'] := by linarith [hPhi.1]
    have eμν : Lam qU aU bU gU μ = Lam qU aU bU gU ν := by linarith [hPhi.1]
    have hν_eq : ν = ![a', b', b', b'] := by
      rcases hL3' with h | h
      · exact h
      · exact absurd eνν' h.ne
    have hμ_eq : ν = μ := by
      rcases hL2' with h | h
      · exact h
      · exact absurd eμν h.ne
    have hμhs : μ = hsSpec := by
      rw [← hμ_eq, hν_eq, ← hxo, hxx, olv_xs]
    have hpl : pur l = 1 / 3 := by
      rw [← hpμ, hμhs]
      unfold pur hsSpec; simp [Fin.sum_univ_four]; norm_num
    have hcl : cub l = 5 / 36 := by
      rw [← hcμ, hμhs]
      unfold cub hsSpec; simp [Fin.sum_univ_four]; norm_num
    exact hs_of_pur_cub hl hpl hcl

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.hsSupporting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hsSupporting

end FormalResearch.FourQubitEntropy.RenyiFull
