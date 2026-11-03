module

public import FormalResearch.FourQubitEntropy.RenyiFullCCCells
public import FormalResearch.FourQubitEntropy.RenyiFullNU

/-!
# Capped cubic lemma: the moment case `x = p - 1/4 ≤ 17/100`

Paper E, `lem:fqe-capped-cubic`, paragraph *The moment argument*.  With `N = 1 + xV + x²W`
(`ccN`), `2 - H_{q_s} ≥ ln N/(rL)`; we show `ln N ≥ r L⁺ x (171/40 - (8/3) v - (11/10) x)` on
`0 ≤ x ≤ 17/100`, `|v| ≤ 6/25`:  the function `F(x) = ln N - r L⁺ x(...)` vanishes at `0`, is concave
(`(ln N)_xx ≤ -1`, certificate CC-1) and nonnegative at `x = 17/100` (certificate CC-2).  This replaces
the paper's monotonicity in `x` of `Φ = ln N/(rLx) + …` by the equivalent concavity.
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy Finset

theorem log_ge_taylor8 {z : ℝ} (hz : 0 ≤ z) :
    z - z ^ 2 / 2 + z ^ 3 / 3 - z ^ 4 / 4 + z ^ 5 / 5 - z ^ 6 / 6 + z ^ 7 / 7 - z ^ 8 / 8 ≤
      Real.log (1 + z) := by
  set f : ℝ → ℝ := fun z => Real.log (1 + z) -
    (z - z ^ 2 / 2 + z ^ 3 / 3 - z ^ 4 / 4 + z ^ 5 / 5 - z ^ 6 / 6 + z ^ 7 / 7 - z ^ 8 / 8) with hf
  have hder : ∀ s : ℝ, -1 < s → HasDerivAt f (s ^ 8 / (1 + s)) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + s)) s := by
      have := ((hasDerivAt_id s).const_add 1).log (by simp; linarith)
      simpa using this
    have h2 : HasDerivAt (fun s : ℝ => s - s ^ 2 / 2 + s ^ 3 / 3 - s ^ 4 / 4 + s ^ 5 / 5 - s ^ 6 / 6 +
        s ^ 7 / 7 - s ^ 8 / 8) (1 - s + s ^ 2 - s ^ 3 + s ^ 4 - s ^ 5 + s ^ 6 - s ^ 7) s := by
      have h : HasDerivAt (fun s : ℝ => s - s ^ 2 / 2 + s ^ 3 / 3 - s ^ 4 / 4 + s ^ 5 / 5 - s ^ 6 / 6 +
          s ^ 7 / 7 - s ^ 8 / 8) (deriv (fun s : ℝ => s - s ^ 2 / 2 + s ^ 3 / 3 - s ^ 4 / 4 + s ^ 5 / 5 -
          s ^ 6 / 6 + s ^ 7 / 7 - s ^ 8 / 8) s) s :=
        (by fun_prop : DifferentiableAt ℝ (fun s : ℝ => s - s ^ 2 / 2 + s ^ 3 / 3 - s ^ 4 / 4 + s ^ 5 / 5 -
          s ^ 6 / 6 + s ^ 7 / 7 - s ^ 8 / 8) s).hasDerivAt
      refine h.congr_deriv ?_
      simp (disch := fun_prop)
      ring
    have := h1.sub h2
    convert this using 1
    have h1s : (1 + s) ≠ 0 := by linarith
    field_simp
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (f' := fun s => s ^ 8 / (1 + s))
    · intro s hs
      have hs0 : -1 < s := by
        have : 0 ≤ s := hs
        linarith
      exact (hder s hs0).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have hs0 : -1 < s := by
        have : 0 < s := by simpa using hs
        linarith
      exact (hder s hs0).hasDerivWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      have : 0 < s := by simpa using hs
      positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hz) hz
  simp [hf] at this
  linarith

/-! ### Elementary bounds on `V`, `W`, `N` -/

theorem ccV_ge {v : ℝ} (hv : |v| ≤ 6 / 25) : 8 / 5 ≤ ccA + ccB * v + ccC * v ^ 2 := by
  obtain ⟨h1, h2⟩ := abs_le.1 hv
  have hC : 0 ≤ ccC * v ^ 2 := mul_nonneg (by unfold ccC; norm_num) (sq_nonneg v)
  have : 8 / 5 ≤ ccA + ccB * v := by unfold ccA ccB; linarith
  linarith

theorem ccW_ge {v : ℝ} (hv : |v| ≤ 6 / 25) : -(1 / 4 : ℝ) ≤ ccC / 4 + ccT * v := by
  obtain ⟨h1, h2⟩ := abs_le.1 hv
  unfold ccC ccT
  linarith

theorem ccN_ge_one {x v : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 17 / 100) (hv : |v| ≤ 6 / 25) :
    1 ≤ ccN x v := by
  have hV := ccV_ge hv
  have hW := ccW_ge hv
  unfold ccN
  have : 0 ≤ x * ((ccA + ccB * v + ccC * v ^ 2) + x * (ccC / 4 + ccT * v)) := by
    apply mul_nonneg hx0
    nlinarith
  linarith

theorem hasDerivAt_ccN (x v : ℝ) : HasDerivAt (fun x => ccN x v) (ccNx x v) x := by
  have h : HasDerivAt (fun x => ccN x v) (deriv (fun x => ccN x v) x) x :=
    (by unfold ccN; fun_prop : DifferentiableAt ℝ (fun x => ccN x v) x).hasDerivAt
  refine h.congr_deriv ?_
  unfold ccN ccNx
  simp (disch := fun_prop)
  ring

theorem hasDerivAt_ccNx (x v : ℝ) : HasDerivAt (fun x => ccNx x v) (ccNxx v) x := by
  have h : HasDerivAt (fun x => ccNx x v) (deriv (fun x => ccNx x v) x) x :=
    (by unfold ccNx; fun_prop : DifferentiableAt ℝ (fun x => ccNx x v) x).hasDerivAt
  refine h.congr_deriv ?_
  unfold ccNx ccNxx
  simp (disch := fun_prop)

/-- The constant `r L⁺` with `L⁺ = 6931471808/10^10 > ln 2`. -/
noncomputable def ccK : ℝ := 587 / 1000 * (6931471808 / 10 ^ 10)

theorem ccK_lt : ccK < 2 / 5 + 1 / 100 := by unfold ccK; norm_num

/-- **Concavity argument**: `r L⁺ x (171/40 - (8/3) v - (11/10) x) ≤ ln N(x, v)` on the box. -/
theorem cc_log_ge {x v : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 17 / 100) (hv : |v| ≤ 6 / 25) :
    ccK * (x * (171 / 40 - 8 / 3 * v - 11 / 10 * x)) ≤ Real.log (ccN x v) := by
  obtain ⟨hv0, hv1⟩ := abs_le.1 hv
  set F : ℝ → ℝ := fun x => Real.log (ccN x v) - ccK * (x * (171 / 40 - 8 / 3 * v - 11 / 10 * x)) with hF
  have hNpos : ∀ x : ℝ, 0 ≤ x → x ≤ 17 / 100 → 0 < ccN x v := fun x a b =>
    lt_of_lt_of_le one_pos (ccN_ge_one a b hv)
  have hd1 : ∀ x : ℝ, 0 ≤ x → x ≤ 17 / 100 →
      HasDerivAt F (ccNx x v / ccN x v - ccK * (171 / 40 - 8 / 3 * v - 11 / 5 * x)) x := by
    intro x a b
    have h1 := (hasDerivAt_ccN x v).log (hNpos x a b).ne'
    have h2 : HasDerivAt (fun x : ℝ => ccK * (x * (171 / 40 - 8 / 3 * v - 11 / 10 * x)))
        (ccK * (171 / 40 - 8 / 3 * v - 11 / 5 * x)) x := by
      have := ((hasDerivAt_id x).mul (((hasDerivAt_id x).const_mul (11 / 10 : ℝ)).const_sub
        (171 / 40 - 8 / 3 * v))).const_mul ccK
      refine this.congr_deriv ?_
      simp only [id]
      ring
    exact h1.sub h2
  have hd2 : ∀ x : ℝ, 0 ≤ x → x ≤ 17 / 100 →
      HasDerivAt (fun x => ccNx x v / ccN x v - ccK * (171 / 40 - 8 / 3 * v - 11 / 5 * x))
        ((ccNxx v * ccN x v - ccNx x v * ccNx x v) / ccN x v ^ 2 + ccK * (11 / 5)) x := by
    intro x a b
    have h1 := (hasDerivAt_ccNx x v).div (hasDerivAt_ccN x v) (hNpos x a b).ne'
    have h2 : HasDerivAt (fun x : ℝ => ccK * (171 / 40 - 8 / 3 * v - 11 / 5 * x)) (ccK * (-(11 / 5))) x := by
      have := ((hasDerivAt_id x).const_mul (11 / 5 : ℝ)).const_sub (171 / 40 - 8 / 3 * v)
      have := this.const_mul ccK
      refine this.congr_deriv ?_
      simp
    have := h1.sub h2
    refine this.congr_deriv ?_
    ring
  have hconc : ConcaveOn ℝ (Set.Icc 0 (17 / 100)) F := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 (17 / 100))
      (f' := fun x => ccNx x v / ccN x v - ccK * (171 / 40 - 8 / 3 * v - 11 / 5 * x))
      (f'' := fun x => (ccNxx v * ccN x v - ccNx x v * ccNx x v) / ccN x v ^ 2 + ccK * (11 / 5))
    · intro x hx
      have := hd1 x hx.1 hx.2
      exact this.continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd1 x hx.1.le hx.2.le).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd2 x hx.1.le hx.2.le).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hN := hNpos x hx.1.le hx.2.le
      have hE := ccE_nonpos hx.1.le hx.2.le hv0 hv1
      have key : (ccNxx v * ccN x v - ccNx x v * ccNx x v) / ccN x v ^ 2 =
          ccE x v / ccN x v ^ 2 - 1 := by
        unfold ccE
        field_simp
        ring
      rw [key]
      have h1 : ccE x v / ccN x v ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hE (by positivity)
      have h2 := ccK_lt
      nlinarith
  -- value at 0 and at X
  have hF0 : F 0 = 0 := by
    simp only [hF, ccN, zero_mul, add_zero, Real.log_one]; ring
  have hFX : 0 ≤ F (17 / 100) := by
    simp only [hF]
    have hNX : 1 ≤ ccN (17 / 100) v := ccN_ge_one (by norm_num) le_rfl hv
    have hz : 0 ≤ ccTz v := by
      have : ccN (17 / 100) v = 1 + ccTz v := by unfold ccN ccTz; ring
      linarith
    have hT := log_ge_taylor8 hz
    have hTay := ccTay_nonneg hv0 hv1
    have e : ccN (17 / 100) v = 1 + ccTz v := by unfold ccN ccTz; ring
    rw [e]
    unfold ccTay at hTay
    have : ccK = (587 / 1000 * (6931471808 / 10 ^ 10) : ℝ) := rfl
    rw [this]
    norm_num at hTay ⊢
    linarith
  have h := hconc.2 (Set.mem_Icc.2 ⟨le_rfl, by norm_num⟩) (Set.mem_Icc.2 ⟨by norm_num, le_rfl⟩)
    (show 0 ≤ 1 - x / (17 / 100) by
      rw [sub_nonneg, div_le_one (by norm_num)]; exact hx1)
    (show 0 ≤ x / (17 / 100) by positivity) (by ring)
  simp only [smul_eq_mul] at h
  have hx' : (1 - x / (17 / 100)) * 0 + x / (17 / 100) * (17 / 100) = x := by field_simp; ring
  rw [hx', hF0] at h
  have : 0 ≤ F x := by
    have := mul_nonneg (show 0 ≤ x / (17 / 100) by positivity) hFX
    nlinarith [this]
  simp only [hF] at this
  linarith

/-- `|y| ≤ (6/25) x` for `0 ≤ x ≤ 17/100` (third-moment lemma). -/
theorem y_le_cc {l : Fin 4 → ℝ} (hl : IsProb4 l) (hx1 : pur l - 1 / 4 ≤ 17 / 100) :
    |cub l - 1 / 16 - 3 / 4 * (pur l - 1 / 4)| ≤ 6 / 25 * (pur l - 1 / 4) := by
  have hx0 : 0 ≤ pur l - 1 / 4 := by have := pur_ge_quarter hl; linarith
  obtain ⟨-, h3, -, -⟩ := third_moment l hl.1 hl.2 (x := pur l - 1 / 4) (by unfold pur; ring)
  have e : cub l = ∑ i, l i ^ 3 := rfl
  rw [e, show (3 : ℝ) / 4 * (pur l - 1 / 4) = 3 * (pur l - 1 / 4) / 4 by ring]
  refine h3.trans ?_
  set x := pur l - 1 / 4 with hx
  rw [rpow_three_halves_eq_nu hx0]
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs33 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hsx : Real.sqrt x ≤ 6 / 25 * Real.sqrt 3 := by
    apply Real.sqrt_le_iff.2
    constructor
    · positivity
    · nlinarith [hs33]
  rw [div_le_iff₀ hs3]
  have : x * Real.sqrt x ≤ x * (6 / 25 * Real.sqrt 3) := mul_le_mul_of_nonneg_left hsx hx0
  nlinarith

set_option maxHeartbeats 8000000 in
/-- **The moment case of `lem:fqe-capped-cubic`**: for `0 < x = p - 1/4 ≤ 17/100`,
`(171/40) x - (8/3) y - (11/10) x² ≤ 2 - H_{q_s}(λ)`, `y = t - 1/16 - (3/4) x`. -/
theorem cc_moment {l : Fin 4 → ℝ} (hl : IsProb4 l) (hx0 : 0 < pur l - 1 / 4)
    (hx1 : pur l - 1 / 4 ≤ 17 / 100) :
    171 / 40 * (pur l - 1 / 4) - 8 / 3 * (cub l - 1 / 16 - 3 / 4 * (pur l - 1 / 4)) -
      11 / 10 * (pur l - 1 / 4) ^ 2 ≤ 2 - renyiSpec qS l := by
  obtain ⟨x, hxdef⟩ : ∃ x, x = pur l - 1 / 4 := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y, y = cub l - 1 / 16 - 3 / 4 * (pur l - 1 / 4) := ⟨_, rfl⟩
  rw [← hydef]
  rw [← hxdef] at hx0 hx1 ⊢
  have hw := w_sums hl.2
  rw [← hydef] at hw
  rw [← hxdef] at hw
  obtain ⟨hw2, hw3⟩ := hw
  have hN := nu_taylor_sum hl
  rw [hw2, hw3] at hN
  obtain ⟨S4, hS4def⟩ : ∃ S, S = ∑ i, (l i - 1 / 4) ^ 4 := ⟨_, rfl⟩
  rw [← hS4def] at hN
  have hsum0 : (l 0 - 1 / 4) + (l 1 - 1 / 4) + (l 2 - 1 / 4) + (l 3 - 1 / 4) = 0 := by
    have := hl.2; simp only [Fin.sum_univ_four] at this; linarith
  have hS := sum_w4_ge hsum0
  have hS' : x * S4 ≥ x ^ 3 / 4 + y ^ 2 := by
    have e2 : x = (l 0 - 1 / 4) ^ 2 + (l 1 - 1 / 4) ^ 2 + (l 2 - 1 / 4) ^ 2 + (l 3 - 1 / 4) ^ 2 := by
      rw [← hw2]; simp [Fin.sum_univ_four]
    have e3 : y = (l 0 - 1 / 4) ^ 3 + (l 1 - 1 / 4) ^ 3 + (l 2 - 1 / 4) ^ 3 + (l 3 - 1 / 4) ^ 3 := by
      rw [← hw3]; simp [Fin.sum_univ_four]
    have e4 : S4 = (l 0 - 1 / 4) ^ 4 + (l 1 - 1 / 4) ^ 4 + (l 2 - 1 / 4) ^ 4 + (l 3 - 1 / 4) ^ 4 := by
      rw [hS4def]; simp [Fin.sum_univ_four]
    rw [e2, e3, e4] at *
    exact hS
  obtain ⟨v, hv⟩ : ∃ v, v = y / x := ⟨_, rfl⟩
  have hyv : y = x * v := by rw [hv]; field_simp
  have hyb : |y| ≤ 6 / 25 * x := by
    rw [hydef, hxdef]; exact y_le_cc hl (by rw [← hxdef]; exact hx1)
  have hvb : |v| ≤ 6 / 25 := by
    rw [hv, abs_div, abs_of_pos hx0, div_le_iff₀ hx0]; linarith
  have hS4v : S4 ≥ x ^ 2 / 4 + x * v ^ 2 := by
    have : x * S4 ≥ x * (x ^ 2 / 4 + x * v ^ 2) := by
      rw [hyv] at hS'; linarith [hS']
    exact le_of_mul_le_mul_left this hx0
  have hC := nuC_pos
  -- N_tot ≥ ccN x v
  have hNz : ccN x v ≤ (4 : ℝ) ^ (qS - 1) * ∑ i, l i ^ qS := by
    have hC4 := mul_le_mul_of_nonneg_left hS4v hC.le
    have e1 : ccN x v = 1 + nuA qS * x + nuB qS * (x * v) + nuC qS * (x ^ 2 / 4 + x * v ^ 2) +
        nuT qS * x * (x * v) := by
      unfold ccN ccA ccB ccC ccT nuA nuB nuT nuC qS; ring
    rw [hyv] at hN
    linarith [hN, hC4, e1]
  have hN1 := ccN_ge_one hx0.le hx1 hvb
  have hZq : 0 < ∑ i, l i ^ qS := sum_rpow_pos hl.1 hl.2
  have hlogN : Real.log (ccN x v) ≤ Real.log ((4 : ℝ) ^ (qS - 1) * ∑ i, l i ^ qS) :=
    Real.log_le_log (by linarith) hNz
  have hcc := cc_log_ge hx0.le hx1 hvb
  have hL2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hLlt : Real.log 2 < 6931471808 / 10 ^ 10 := by
    have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
  have hlogNeq : Real.log ((4 : ℝ) ^ (qS - 1) * ∑ i, l i ^ qS) =
      (qS - 1) * Real.log 2 * (2 - renyiSpec qS l) := by
    rw [Real.log_mul (by positivity) hZq.ne', Real.log_rpow (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    unfold renyiSpec Real.logb
    have h1 : (1 - qS) ≠ 0 := by unfold qS; norm_num
    field_simp
    push_cast
    ring
  rw [hlogNeq] at hlogN
  have hK : 0 ≤ 171 / 40 - 8 / 3 * v - 11 / 10 * x := by
    obtain ⟨h1, h2⟩ := abs_le.1 hvb; linarith
  have hr : 0 < qS - 1 := by unfold qS; norm_num
  have hxK : 0 ≤ x * (171 / 40 - 8 / 3 * v - 11 / 10 * x) := mul_nonneg hx0.le hK
  have step : (qS - 1) * Real.log 2 * (x * (171 / 40 - 8 / 3 * v - 11 / 10 * x)) ≤
      (qS - 1) * Real.log 2 * (2 - renyiSpec qS l) := by
    refine le_trans ?_ (hcc.trans hlogN)
    have e : (587 / 1000 : ℝ) = qS - 1 := by unfold qS; norm_num
    unfold ccK
    rw [e]
    have := mul_le_mul_of_nonneg_left hLlt.le (mul_nonneg hr.le hxK)
    linarith [this]
  have hpos : 0 < (qS - 1) * Real.log 2 := mul_pos hr hL2
  have := le_of_mul_le_mul_left step hpos
  rw [hyv]
  linarith [this]

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.cc_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cc_moment

end FormalResearch.FourQubitEntropy.RenyiFull
