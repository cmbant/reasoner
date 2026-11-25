module

public import FormalResearch.SignUncertainty.MiddleBandAmplitude
public import FormalResearch.SignUncertainty.MiddleBandZones

/-!
# GT.2a: smoothness and small-zone bounds of the inner difference

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `cegt:GT2a`, inner difference `𝒟` near `u = 0`.

With `𝒟 = innerDiff c ε τ W` (`MiddleBandAmplitude`):

* `innerDiff_contDiffAt`: `𝒟` is `C²` at every `u ≠ 0` with `|εu| < 0.22` (the symbol `W` having a derivative chain off `0`);
* `innerDiff_largeZone`: the `(e8)` bounds of `innerDiff_bounds` together with `innerDiff_contDiffAt` give `LargeZone 𝒟 C L ε`;
* `innerDiff_small`: the hypotheses of `inner_integral_bound` near `0` (`0 < |u| < 3`): `‖𝒟(0)‖ ≤ C(L+ε²)`, the Hölder bound
  `‖𝒟(u) - 𝒟(0)‖ ≤ C(L+ε²)|u|^{1/2}`, `‖𝒟'‖ ≤ C(L+ε²)|u|^{-1/2}`, `‖𝒟''‖ ≤ C(L+ε²)|u|^{-3/2}`, for a symbol with
  `‖W(s) - W(0)‖ ≤ A|s|^{1/2}`, `‖W^{(j)}(s)‖ ≤ A|s|^{1/2-j}` (`0 < |s| ≤ 9`), `ε ≤ 0.05`.

The proof of the last uses `innerDiff_local` for `W - W(0)` with `ρ = |u|^{1/2}` and `𝒟[W] = 𝒟[W - W(0)] + q W(0)`, `q = ampQ0`.

Status: proved, unconditional given `O4NormalForm L τ` (which exists for every `0 < L ≤ 0.002` by `o4_normal_form` and `o4QuotientBound`).  Not formalised here: the
reference and `τ`-line outer pieces and the assembly `middle_transfer`.
-/

@[expose] public section

open Set Filter Topology Complex Function

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `f` has derivative `D` nearby and `D` is `C^n` at `x`, so `f` is `C^{n+1}` at `x` (vector-valued version). -/
lemma contDiffAt_succ_of_hasDerivAt' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f D : ℝ → F} {x : ℝ} {n : ℕ}
    (h : ∀ᶠ y in 𝓝 x, HasDerivAt f (D y) y) (hD : ContDiffAt ℝ n D x) :
    ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f x := by
  rw [Nat.cast_succ, contDiffAt_succ_iff_hasFDerivAt]
  refine ⟨fun y => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (D y),
    ⟨_, h, fun y hy => hy.hasFDerivAt⟩, ?_⟩
  exact ((ContinuousLinearMap.smulRightL ℝ ℝ F (1 : ℝ →L[ℝ] ℝ)).contDiff.contDiffAt).comp x hD

/-- A derivative chain `W → W1 → W2 → W3` valid on a neighbourhood gives `C²`. -/
lemma contDiffAt_two_of_chain {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {W W1 W2 W3 : ℝ → F} {s : ℝ}
    (hs : s ≠ 0)
    (hWd : ∀ s, s ≠ 0 → HasDerivAt W (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s) :
    ContDiffAt ℝ 2 W s := by
  have hU : ∀ᶠ y in 𝓝 s, y ≠ 0 := isOpen_ne.mem_nhds hs
  have h2 : ContDiffAt ℝ ((0 : ℕ) : WithTop ℕ∞) W2 s := by
    exact_mod_cast contDiffAt_zero.2 ⟨{y | y ≠ 0}, isOpen_ne.mem_nhds hs,
      fun y hy => (hWd y hy).2.2.continuousAt.continuousWithinAt⟩
  have h1 : ContDiffAt ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) W1 s :=
    contDiffAt_succ_of_hasDerivAt' (by filter_upwards [hU] with y hy using (hWd y hy).2.1) h2
  have h0 : ContDiffAt ℝ ((0 + 1 + 1 : ℕ) : WithTop ℕ∞) W s :=
    contDiffAt_succ_of_hasDerivAt' (by filter_upwards [hU] with y hy using (hWd y hy).1) h1
  exact_mod_cast h0

/-- Every `trF τ n` is `C^k` on `|θ| < 0.22`. -/
lemma trF_contDiffAt {L : ℝ} {τ : ℂ → ℂ} (h : O4NormalForm L τ) {θ : ℝ} (hθ : |θ| < 0.22) :
    ∀ k : ℕ, ∀ n : ℕ, ContDiffAt ℝ (k : WithTop ℕ∞) (trF τ n) θ := by
  intro k
  induction k with
  | zero =>
    intro n
    exact_mod_cast contDiffAt_zero.2 ⟨{y | |y| < 0.22}, (isOpen_lt continuous_abs continuous_const).mem_nhds hθ,
      fun y hy => (trF_hasDerivAt h n (show |y| < 0.22 from hy)).continuousAt.continuousWithinAt⟩
  | succ k ih =>
    intro n
    have hU : ∀ᶠ y in 𝓝 θ, HasDerivAt (trF τ n) (trF τ (n + 1) y) y := by
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hθ] with y hy using trF_hasDerivAt h n hy
    exact contDiffAt_succ_of_hasDerivAt' hU (ih (n + 1))

/-- `|t(θ)| ≤ 1.013 |θ|` and `t(θ) ≠ 0` for real `0 < |θ| < 0.22`. -/
lemma trF_ratio {L : ℝ} {τ : ℂ → ℂ} (h : O4NormalForm L τ) (hL0 : 0 < L) (hL2 : L ≤ 0.002) {θ : ℝ} (hθ0 : θ ≠ 0)
    (hθ : |θ| < 0.22) : 0.989 * |θ| ≤ |trF τ 0 θ| ∧ |trF τ 0 θ| ≤ 1.013 * |θ| := by
  obtain ⟨h1, h2⟩ := h.ratio hL0 hL2 hθ0 hθ
  have htr : trF τ 0 θ = (τ (θ : ℂ)).re := by simp [trF]
  rw [htr]
  have hpos : 0 < (τ (θ : ℂ)).re / θ := by linarith
  have hab : |(τ (θ : ℂ)).re / θ| = |(τ (θ : ℂ)).re| / |θ| := abs_div _ _
  rw [abs_of_pos hpos] at hab
  have hθp : 0 < |θ| := abs_pos.mpr hθ0
  constructor
  · rw [hab] at h1; rw [lt_div_iff₀ hθp] at h1; linarith
  · rw [hab] at h2; rw [div_lt_iff₀ hθp] at h2; linarith

/-- **`𝒟` is `C²` off `0`.** -/
theorem innerDiff_contDiffAt {L : ℝ} {τ : ℂ → ℂ} (h : O4NormalForm L τ) (hL0 : 0 < L) (hL2 : L ≤ 0.002)
    {c ε : ℝ} (hc : 2 ≤ c) (hε : 0 < ε) {W W1 W2 W3 : ℝ → ℂ}
    (hWd : ∀ s, s ≠ 0 → HasDerivAt W (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s)
    {u : ℝ} (hu : u ≠ 0) (hεu : |ε * u| < 0.22) : ContDiffAt ℝ 2 (innerDiff c ε τ W) u := by
  have hθ0 : ε * u ≠ 0 := mul_ne_zero hε.ne' hu
  have hlin : ContDiffAt ℝ 2 (fun s : ℝ => ε * s) u := (contDiff_const.mul contDiff_id).contDiffAt
  have hlin' : ∀ n : ℕ, ContDiffAt ℝ 2 (fun s => trF τ n (ε * s)) u := fun n => by
    have := trF_contDiffAt h hεu 2 n
    exact (by exact_mod_cast this : ContDiffAt ℝ 2 (trF τ n) (ε * u)).comp u hlin
  have t0 := hlin' 0
  have t1 := hlin' 1
  have hK : ContDiffAt ℝ 2 (outerK c) (trF τ 0 (ε * u)) := ((outerK_bounds.choose_spec.2 hc).1).contDiffAt
  have hKc : ContDiffAt ℝ 2 (fun s => outerK c (trF τ 0 (ε * s))) u := ContDiffAt.comp (g := outerK c) (f := fun s => trF τ 0 (ε * s)) u hK t0
  have ht1c : ContDiffAt ℝ 2 (fun s => ((trF τ 1 (ε * s) : ℝ) : ℂ)) u :=
    (Complex.ofRealCLM.contDiff.contDiffAt).comp u t1
  have hw : ContDiffAt ℝ 2 (fun s => trF τ 0 (ε * s) / ε) u := t0.div_const ε
  have hwne : trF τ 0 (ε * u) / ε ≠ 0 := by
    have := (trF_ratio h hL0 hL2 hθ0 hεu).1
    have hp : 0 < |trF τ 0 (ε * u)| := by
      have : 0 < 0.989 * |ε * u| := by have := abs_pos.mpr hθ0; positivity
      linarith
    exact div_ne_zero (abs_pos.mp hp) hε.ne'
  have hWw : ContDiffAt ℝ 2 (fun s => W (trF τ 0 (ε * s) / ε)) u :=
    (contDiffAt_two_of_chain hwne hWd).comp u hw
  have hWu : ContDiffAt ℝ 2 W u := contDiffAt_two_of_chain hu hWd
  have hE : ContDiffAt ℝ 2 (fun s : ℝ => Complex.exp (Complex.I * ((ε * s : ℝ) : ℂ) / 2)) u := by
    have : ContDiff ℝ 2 (fun s : ℝ => Complex.exp (Complex.I * ((ε * s : ℝ) : ℂ) / 2)) :=
      ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id))).div_const 2).cexp
    exact this.contDiffAt
  exact ((hKc.mul ht1c).mul hWw).sub (hE.mul hWu)

/-- `LargeZone` for the inner difference: `(e8)` plus smoothness. -/
theorem innerDiff_largeZone (AW : ℝ) (hAW : 1 ≤ AW) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {L : ℝ} {τ : ℂ → ℂ}, O4NormalForm L τ → 0 < L → L ≤ 0.002 → ∀ {c ε : ℝ}, 2 ≤ c → 0 < ε → 1 / c ≤ L →
    ∀ {W W1 W2 W3 : ℝ → ℂ},
      (∀ s, s ≠ 0 → HasDerivAt W (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s) →
      (∀ s, 1 / 2 ≤ |s| → ‖W s‖ ≤ AW * |s| ^ (-(5 / 2 : ℝ)) ∧ ‖W1 s‖ ≤ AW * |s| ^ (-(7 / 2 : ℝ)) ∧
        ‖W2 s‖ ≤ AW * |s| ^ (-(9 / 2 : ℝ)) ∧ ‖W3 s‖ ≤ AW * |s| ^ (-(11 / 2 : ℝ))) →
      LargeZone (innerDiff c ε τ W) C L ε := by
  obtain ⟨C, hC0, hC⟩ := innerDiff_bounds AW hAW
  refine ⟨C, hC0, ?_⟩
  intro L τ h hL0 hL2 c ε hc hε hcL W W1 W2 W3 hWd hWb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu1 hu18
    refine innerDiff_contDiffAt h hL0 hL2 hc hε hWd (abs_pos.mp (by linarith)) ?_
    rw [abs_mul, abs_of_pos hε]; linarith
  · intro u hu1 hu18; exact (hC h hL0 hL2 hc hε hcL hWd hWb hu1 hu18).1
  · intro u hu1 hu18; exact (hC h hL0 hL2 hc hε hcL hWd hWb hu1 hu18).2.1
  · intro u hu1 hu18; exact (hC h hL0 hL2 hc hε hcL hWd hWb hu1 hu18).2.2

/-- Derivatives of a sum of two `C²` functions. -/
lemma deriv_add_two {f h : ℝ → ℂ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x) (hh : ContDiffAt ℝ 2 h x) :
    deriv (fun s => f s + h s) x = deriv f x + deriv h x ∧
    deriv (deriv (fun s => f s + h s)) x = deriv (deriv f) x + deriv (deriv h) x := by
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f y ∧ ContDiffAt ℝ 2 h y :=
    (hf.eventually (by simp)).and (hh.eventually (by simp))
  have h1 : ∀ᶠ y in 𝓝 x, deriv (fun s => f s + h s) y = deriv f y + deriv h y := by
    filter_upwards [hev] with y hy
    exact deriv_add (hy.1.differentiableAt (by simp)) (hy.2.differentiableAt (by simp))
  refine ⟨h1.self_of_nhds, ?_⟩
  rw [Filter.EventuallyEq.deriv_eq h1]
  have d1 : ContDiffAt ℝ 1 (deriv f) x := hf.derivWithin (m := 1) (by norm_num)
  have d2 : ContDiffAt ℝ 1 (deriv h) x := hh.derivWithin (m := 1) (by norm_num)
  exact deriv_add (d1.differentiableAt (by simp)) (d2.differentiableAt (by simp))

/-- Negative half-integer powers in terms of `q = m^{-1/2}`. -/
lemma rpow_half_aux {m : ℝ} (hm : 0 < m) :
    m ^ (1 / 2 : ℝ) * m ^ (-(1 / 2) : ℝ) = 1 ∧ m ^ (1 / 2 : ℝ) * m ^ (1 / 2 : ℝ) = m ∧
    m ^ (-(3 / 2) : ℝ) = m⁻¹ * m ^ (-(1 / 2) : ℝ) ∧ m ^ (-(5 / 2) : ℝ) = m⁻¹ * (m⁻¹ * m ^ (-(1 / 2) : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Real.rpow_add hm]; norm_num
  · rw [← Real.rpow_add hm]; norm_num
  · rw [show (-(3 / 2) : ℝ) = -1 + -(1 / 2) by norm_num, Real.rpow_add hm, Real.rpow_neg_one]
  · rw [show (-(5 / 2) : ℝ) = -1 + (-1 + -(1 / 2)) by norm_num, Real.rpow_add hm, Real.rpow_add hm, Real.rpow_neg_one]

set_option maxHeartbeats 6400000 in
/-- **Small zone** (`0 < |u| < 3`): the hypotheses of `inner_integral_bound` near `0` for `g = 𝒟`. -/
theorem innerDiff_small (AW : ℝ) (hAW : 1 ≤ AW) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {L : ℝ} {τ : ℂ → ℂ}, O4NormalForm L τ → 0 < L → L ≤ 0.002 → ∀ {c ε : ℝ}, 2 ≤ c → 0 < ε → ε ≤ 0.05 → 1 / c ≤ L →
    ∀ {W W1 W2 W3 : ℝ → ℂ},
      (∀ s, s ≠ 0 → HasDerivAt W (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s) →
      ‖W 0‖ ≤ AW →
      (∀ s, 0 < |s| → |s| ≤ 9 → ‖W s - W 0‖ ≤ AW * |s| ^ (1 / 2 : ℝ) ∧ ‖W1 s‖ ≤ AW * |s| ^ (-(1 / 2) : ℝ) ∧
        ‖W2 s‖ ≤ AW * |s| ^ (-(3 / 2) : ℝ) ∧ ‖W3 s‖ ≤ AW * |s| ^ (-(5 / 2) : ℝ)) →
      ‖innerDiff c ε τ W 0‖ ≤ C * (L + ε ^ 2) ∧
      ∀ u : ℝ, 0 < |u| → |u| < 3 →
        ‖innerDiff c ε τ W u - innerDiff c ε τ W 0‖ ≤ C * (L + ε ^ 2) * |u| ^ (1 / 2 : ℝ) ∧
        ‖deriv (innerDiff c ε τ W) u‖ ≤ C * (L + ε ^ 2) * |u| ^ (-(1 / 2) : ℝ) ∧
        ‖deriv (deriv (innerDiff c ε τ W)) u‖ ≤ C * (L + ε ^ 2) * |u| ^ (-(3 / 2) : ℝ) := by
  obtain ⟨C1, hC1, hloc⟩ := innerDiff_local (128 * AW) (by linarith)
  obtain ⟨M, hM1, hMb⟩ := amp_q_bounds
  have hAW0 : 0 ≤ AW := by linarith
  have hMA : 0 ≤ M * AW := by positivity
  refine ⟨9 * C1 + 8 * M * AW, by positivity, ?_⟩
  intro L τ h hL0 hL2 c ε hc hε hε5 hcL W W1 W2 W3 hWd hW0 hSm
  set Wt : ℝ → ℂ := fun s => W s - W 0 with hWt
  have hWtd : ∀ s, s ≠ 0 → HasDerivAt Wt (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s :=
    fun s hs => ⟨(hWd s hs).1.sub_const _, (hWd s hs).2.1, (hWd s hs).2.2⟩
  have hsplit : innerDiff c ε τ W = fun s => innerDiff c ε τ Wt s + ampQ0 c τ (ε * s) * W 0 := by
    funext s; simp only [innerDiff, ampQ0, hWt]; ring
  have hg0 : innerDiff c ε τ W 0 = ampQ0 c τ 0 * W 0 := by
    have : innerDiff c ε τ Wt 0 = 0 := by simp [innerDiff, hWt, trF, h.zero]
    have h0 := congrFun hsplit 0
    rw [h0, this]; simp
  have hCnn : 0 ≤ 9 * C1 + 8 * M * AW := by positivity
  set C : ℝ := 9 * C1 + 8 * M * AW with hC
  refine ⟨?_, ?_⟩
  · rw [hg0, norm_mul]
    obtain ⟨b0, -, -⟩ := hMb h hL0 hL2 hc hcL (θ := 0) (by norm_num)
    calc ‖ampQ0 c τ 0‖ * ‖W 0‖ ≤ (M * (L + 0 ^ 2)) * AW := by gcongr
      _ ≤ C * (L + ε ^ 2) := by
        rw [hC]; nlinarith only [mul_nonneg hMA (sq_nonneg ε), mul_nonneg hMA hL0.le, mul_nonneg hC1 (add_nonneg hL0.le (sq_nonneg ε))]
  intro u hu0 hu3
  have hu_ne : u ≠ 0 := abs_pos.mp hu0
  have hεu : ε * |u| ≤ 0.15 := by nlinarith only [hε5, hu3, mul_nonneg (sub_nonneg.2 hε5) hu0.le]
  have hθabs : |ε * u| = ε * |u| := by rw [abs_mul, abs_of_pos hε]
  have hθ18 : |ε * u| ≤ 0.18 := by rw [hθabs]; linarith only [hεu]
  have hθ22 : |ε * u| < 0.22 := by linarith only [hθ18]
  -- the half-power variables
  set m : ℝ := |u| with hm
  obtain ⟨hsq, hss, hr3, hr5⟩ := rpow_half_aux hu0
  set s : ℝ := m ^ (1 / 2 : ℝ) with hs
  set q : ℝ := m ^ (-(1 / 2) : ℝ) with hq
  have hs0 : 0 < s := Real.rpow_pos_of_pos hu0 _
  have hq0 : 0 < q := Real.rpow_pos_of_pos hu0 _
  have hs2 : s < 2 := by nlinarith only [hss, hu3, hs0]
  have hq2 : 1 / 2 < q := by nlinarith only [hsq, hs2, hs0, hq0]
  have hsq2 : s * q * (s * q) = 1 := by rw [hsq, one_mul]
  have hmi : m⁻¹ = q * q := by
    have : m = s * s := hss.symm
    rw [this]; field_simp; nlinarith only [hsq2]
  have hr3' : m ^ (-(3 / 2) : ℝ) = q ^ 3 := by rw [hr3, hmi]; ring
  have hr5' : m ^ (-(5 / 2) : ℝ) = q ^ 5 := by rw [hr5, hmi]; ring
  have hsmi : s * m⁻¹ = q := by
    rw [hmi]
    have : s * (q * q) = (s * q) * q := by ring
    rw [this, hsq, one_mul]
  have hsmi2 : s * (m⁻¹) ^ 2 = q ^ 3 := by
    rw [hmi]
    have : s * (q * q) ^ 2 = (s * q) * q ^ 3 := by ring
    rw [this, hsq, one_mul]
  have hsmi3 : s * (m⁻¹) ^ 3 = q ^ 5 := by
    rw [hmi]
    have : s * (q * q) ^ 3 = (s * q) * q ^ 5 := by ring
    rw [this, hsq]; ring
  have hmle : m ≤ 2 * s := by nlinarith only [hss, hs2, hs0, mul_pos hs0 (sub_pos.2 hs2)]
  have hm2 : m ^ 2 ≤ 6 * s := by
    nlinarith only [mul_nonneg hu0.le (sub_nonneg.2 hu3.le), hmle]
  -- region for the local bound
  have hwle : |trF τ 0 (ε * u) / ε| ≤ 1.013 * m := by
    rw [abs_div, abs_of_pos hε, div_le_iff₀ hε]
    have := (trF_ratio h hL0 hL2 (mul_ne_zero hε.ne' hu_ne) hθ22).2
    rw [hθabs] at this; linarith only [this]
  have hSl : ∀ x, m / 2 ≤ |x| → |x| ≤ m + |trF τ 0 (ε * u) / ε| →
      ‖Wt x‖ ≤ (128 * AW) * s ∧ ‖W1 x‖ ≤ (128 * AW) * (s * m⁻¹) ∧
      ‖W2 x‖ ≤ (128 * AW) * (s * (m⁻¹) ^ 2) ∧ ‖W3 x‖ ≤ (128 * AW) * (s * (m⁻¹) ^ 3) := by
    intro x hx hxR
    have hx3 : |x| ≤ 3 * m := by linarith only [hxR, hwle, hu0]
    have hx9 : |x| ≤ 9 := by linarith only [hx3, hu3]
    have hx0 : 0 < |x| := by linarith only [hx, hu0]
    obtain ⟨a0, a1, a2, a3⟩ := hSm x hx0 hx9
    have r1 : |x| ^ (-(1 / 2) : ℝ) ≤ 64 * q := mbd_rpow_le hu0 hx (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have r3 : |x| ^ (-(3 / 2) : ℝ) ≤ 64 * q ^ 3 := by
      rw [← hr3']; exact mbd_rpow_le hu0 hx (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num)
    have r5 : |x| ^ (-(5 / 2) : ℝ) ≤ 64 * q ^ 5 := by
      rw [← hr5']; exact mbd_rpow_le hu0 hx (by norm_num : (0 : ℝ) < 5 / 2) (by norm_num)
    have hxs : |x| ^ (1 / 2 : ℝ) ≤ 2 * s := by
      rw [← Real.sqrt_eq_rpow]
      refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
      nlinarith only [hss, hx3, hu0]
    rw [hsmi, hsmi2, hsmi3]
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc ‖Wt x‖ = ‖W x - W 0‖ := rfl
        _ ≤ AW * |x| ^ (1 / 2 : ℝ) := a0
        _ ≤ AW * (2 * s) := by gcongr
        _ ≤ _ := by nlinarith only [mul_pos hs0 (by linarith only [hAW] : (0 : ℝ) < AW)]
    · calc ‖W1 x‖ ≤ AW * |x| ^ (-(1 / 2) : ℝ) := a1
        _ ≤ AW * (64 * q) := by gcongr
        _ ≤ _ := by nlinarith only [mul_pos hq0 (by linarith only [hAW] : (0 : ℝ) < AW)]
    · calc ‖W2 x‖ ≤ AW * |x| ^ (-(3 / 2) : ℝ) := a2
        _ ≤ AW * (64 * q ^ 3) := by gcongr
        _ ≤ _ := by nlinarith only [mul_pos (pow_pos hq0 3) (by linarith only [hAW] : (0 : ℝ) < AW)]
    · calc ‖W3 x‖ ≤ AW * |x| ^ (-(5 / 2) : ℝ) := a3
        _ ≤ AW * (64 * q ^ 5) := by gcongr
        _ ≤ _ := by nlinarith only [mul_pos (pow_pos hq0 5) (by linarith only [hAW] : (0 : ℝ) < AW)]
  obtain ⟨k0, k1, k2⟩ := hloc h hL0 hL2 hc hε hcL hWtd hu0 (hεu.trans (by norm_num)) hs0 hSl
  rw [hsmi] at k1; rw [hsmi2] at k2
  -- smoothness and splitting of derivatives
  set g : ℝ → ℂ := innerDiff c ε τ W with hg
  set gt : ℝ → ℂ := innerDiff c ε τ Wt with hgt
  set Qf : ℝ → ℂ := fun s => ampQ0 c τ (ε * s) * W 0 with hQf
  have hcdg : ContDiffAt ℝ 2 g u := innerDiff_contDiffAt h hL0 hL2 hc hε hWd hu_ne hθ22
  have hcdt : ContDiffAt ℝ 2 gt u := innerDiff_contDiffAt h hL0 hL2 hc hε hWtd hu_ne hθ22
  have hQeq : Qf = fun s => g s - gt s := by
    funext s
    have := congrFun hsplit s
    beta_reduce at this
    show ampQ0 c τ (ε * s) * W 0 = g s - gt s
    rw [this]; ring
  have hcdQ : ContDiffAt ℝ 2 Qf u := by rw [hQeq]; exact hcdg.sub hcdt
  have hgsum : g = fun s => gt s + Qf s := hsplit
  obtain ⟨dd1, dd2⟩ := deriv_add_two hcdt hcdQ
  have hQd : ∀ s, |ε * s| < 0.22 → HasDerivAt Qf ((ε : ℂ) * ampQ1 c τ (ε * s) * W 0) s ∧
      HasDerivAt (fun s => (ε : ℂ) * ampQ1 c τ (ε * s) * W 0) ((ε : ℂ) ^ 2 * ampQ2 c τ (ε * s) * W 0) s := by
    intro s hs
    obtain ⟨a0, a1⟩ := ampQ_hasDerivAt h hc hs
    have b0 := (hasDerivAt_dilate a0).mul_const (W 0)
    have b1 := ((hasDerivAt_dilate a1).const_mul (ε : ℂ)).mul_const (W 0)
    refine ⟨b0.congr_deriv ?_, b1.congr_deriv ?_⟩
    · simp only [Complex.real_smul]
    · simp only [Complex.real_smul]; ring
  have hdQ1 : deriv Qf u = (ε : ℂ) * ampQ1 c τ (ε * u) * W 0 := (hQd u hθ22).1.deriv
  have hdQ2 : deriv (deriv Qf) u = (ε : ℂ) ^ 2 * ampQ2 c τ (ε * u) * W 0 := by
    have hUo : IsOpen {s : ℝ | |ε * s| < 0.22} :=
      isOpen_lt (continuous_abs.comp (continuous_const.mul continuous_id)) continuous_const
    have hev : deriv Qf =ᶠ[𝓝 u] fun s => (ε : ℂ) * ampQ1 c τ (ε * s) * W 0 := by
      filter_upwards [hUo.mem_nhds hθ22] with s hs using (hQd s hs).1.deriv
    rw [hev.deriv_eq]; exact (hQd u hθ22).2.deriv
  have hdg1 : deriv g u = deriv gt u + deriv Qf u := by rw [hgsum]; exact dd1
  have hdg2 : deriv (deriv g) u = deriv (deriv gt) u + deriv (deriv Qf) u := by rw [hgsum]; exact dd2
  -- amplitude bounds
  obtain ⟨b0, b1, b2⟩ := hMb h hL0 hL2 hc hcL hθ18
  set X : ℝ := L + ε ^ 2 with hX
  have hX0 : 0 ≤ X := by positivity
  have hε1 : ε ≤ 1 := by linarith only [hε5]
  have hδ : L + ε ^ 2 * u ^ 2 ≤ 9 * X := by
    have : u ^ 2 ≤ 9 := by
      rw [← sq_abs]; show m ^ 2 ≤ 9
      nlinarith only [mul_nonneg hu0.le (sub_nonneg.2 hu3.le), hu3]
    nlinarith only [hX, hL0, mul_nonneg (sq_nonneg ε) (sub_nonneg.2 this)]
  have hδ0 : 0 ≤ L + ε ^ 2 * u ^ 2 := by positivity
  have hXq : X ≤ 2 * (X * q) := by nlinarith only [mul_nonneg hX0 (sub_nonneg.2 hq2.le)]
  have hq3 : 1 / 8 < q ^ 3 := by
    have : (1 / 2 : ℝ) ^ 3 < q ^ 3 := pow_lt_pow_left₀ hq2 (by norm_num) (by norm_num)
    linarith only [this]
  have hXq3 : X ≤ 8 * (X * q ^ 3) := by nlinarith only [mul_nonneg hX0 (sub_nonneg.2 hq3.le)]
  refine ⟨?_, ?_, ?_⟩
  · -- Hölder bound
    have hsplit_u : g u - g 0 = gt u + (ampQ0 c τ (ε * u) - ampQ0 c τ 0) * W 0 := by
      have h1 := congrFun hsplit u
      rw [hg0, h1]; ring
    have hmv : ‖ampQ0 c τ (ε * u) - ampQ0 c τ 0‖ ≤ (M * (L + |ε * u|)) * |ε * u - 0| := by
      refine mbd_mvt (f := ampQ0 c τ) (f' := ampQ1 c τ) (u := 0) (w := ε * u) (fun x hx => ?_) (fun x hx => ?_)
      · have := mbd_seg_le (u := 0) (w := ε * u) (R := |ε * u|) (by rw [abs_zero]; exact abs_nonneg _) le_rfl hx
        exact (ampQ_hasDerivAt h hc (by linarith)).1
      · have hx' := mbd_seg_le (u := 0) (w := ε * u) (R := |ε * u|) (by rw [abs_zero]; exact abs_nonneg _) le_rfl hx
        obtain ⟨-, c1, -⟩ := hMb h hL0 hL2 hc hcL (θ := x) (by linarith)
        exact c1.trans (by gcongr)
    have hmv2 : ‖ampQ0 c τ (ε * u) - ampQ0 c τ 0‖ ≤ 6 * M * X * s := by
      refine hmv.trans ?_
      rw [sub_zero, hθabs]
      have e1 : (M * (L + ε * m)) * (ε * m) = M * (L * (ε * m) + ε ^ 2 * m ^ 2) := by ring
      rw [e1]
      have g1 : ε * m ≤ 2 * s := by nlinarith only [mul_nonneg (sub_nonneg.2 hε1) hu0.le, hmle]
      have f1 : L * (ε * m) ≤ 2 * L * s := by nlinarith only [mul_le_mul_of_nonneg_left g1 hL0.le]
      have f2 : ε ^ 2 * m ^ 2 ≤ 6 * ε ^ 2 * s := by nlinarith only [mul_le_mul_of_nonneg_left hm2 (sq_nonneg ε)]
      have : M * (L * (ε * m) + ε ^ 2 * m ^ 2) ≤ M * (6 * X * s) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith only [hM1])
        rw [hX]; nlinarith only [f1, f2, mul_nonneg hL0.le hs0.le]
      linarith only [this]
    rw [hsplit_u]
    calc ‖gt u + (ampQ0 c τ (ε * u) - ampQ0 c τ 0) * W 0‖ ≤ ‖gt u‖ + ‖ampQ0 c τ (ε * u) - ampQ0 c τ 0‖ * ‖W 0‖ :=
          (norm_add_le _ _).trans (by rw [norm_mul])
      _ ≤ C1 * (9 * X) * s + (6 * M * X * s) * AW := by
        gcongr
        · exact k0.trans (by gcongr)
      _ ≤ C * X * s := by
        rw [hC]; nlinarith only [mul_nonneg (mul_nonneg hMA hX0) hs0.le, mul_nonneg (mul_nonneg hC1 hX0) hs0.le]
  · rw [hdg1, hdQ1]
    have h1 : ‖(ε : ℂ) * ampQ1 c τ (ε * u) * W 0‖ ≤ 3 * M * AW * X := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      calc ε * ‖ampQ1 c τ (ε * u)‖ * ‖W 0‖ ≤ ε * (M * (L + |ε * u|)) * AW := by gcongr
        _ ≤ 3 * M * AW * X := by
          rw [hθabs, hX]
          nlinarith only [mul_nonneg hMA hL0.le, mul_nonneg hMA (mul_nonneg hL0.le (sub_nonneg.2 hε1)),
            mul_nonneg (mul_nonneg hMA (sq_nonneg ε)) (sub_nonneg.2 hu3.le)]
    calc ‖deriv gt u + (ε : ℂ) * ampQ1 c τ (ε * u) * W 0‖ ≤ ‖deriv gt u‖ + 3 * M * AW * X := (norm_add_le _ _).trans (by gcongr)
      _ ≤ C1 * (9 * X) * q + 3 * M * AW * X := by gcongr; exact k1.trans (by gcongr)
      _ ≤ C * X * q := by
        rw [hC]; nlinarith only [mul_nonneg hMA hX0, mul_nonneg (mul_nonneg hMA hX0) (sub_nonneg.2 hq2.le)]
  · rw [hr3', hdg2, hdQ2]
    have h1 : ‖(ε : ℂ) ^ 2 * ampQ2 c τ (ε * u) * W 0‖ ≤ M * AW * X := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      calc ε ^ 2 * ‖ampQ2 c τ (ε * u)‖ * ‖W 0‖ ≤ ε ^ 2 * M * AW := by gcongr
        _ ≤ M * AW * X := by rw [hX]; nlinarith only [mul_nonneg hMA hL0.le]
    calc ‖deriv (deriv gt) u + (ε : ℂ) ^ 2 * ampQ2 c τ (ε * u) * W 0‖ ≤ ‖deriv (deriv gt) u‖ + M * AW * X :=
          (norm_add_le _ _).trans (by gcongr)
      _ ≤ C1 * (9 * X) * q ^ 3 + M * AW * X := by gcongr; exact k2.trans (by gcongr)
      _ ≤ C * X * q ^ 3 := by
        rw [hC]; nlinarith only [mul_nonneg hMA hX0, mul_nonneg (mul_nonneg hMA hX0) (sub_nonneg.2 hq3.le)]

/-- info: 'FormalResearch.SignUncertainty.contDiffAt_two_of_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.contDiffAt_two_of_chain

/-- info: 'FormalResearch.SignUncertainty.trF_contDiffAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.trF_contDiffAt

/-- info: 'FormalResearch.SignUncertainty.trF_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.trF_ratio

/-- info: 'FormalResearch.SignUncertainty.innerDiff_contDiffAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.innerDiff_contDiffAt

/-- info: 'FormalResearch.SignUncertainty.innerDiff_largeZone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.innerDiff_largeZone

/-- info: 'FormalResearch.SignUncertainty.deriv_add_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.deriv_add_two

/-- info: 'FormalResearch.SignUncertainty.innerDiff_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.innerDiff_small

end FormalResearch.SignUncertainty
