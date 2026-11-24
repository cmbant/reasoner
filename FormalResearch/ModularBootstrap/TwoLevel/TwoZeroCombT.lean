module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroDictT
public import FormalResearch.ModularBootstrap.Upper.Design.DesignCombProps
public import FormalResearch.ModularBootstrap.Upper.Comb.EdgePhase

/-!
# The strip factor `T_{χ(p)}` of `ut:T2`: real-axis and phase lemmas (`upper_transfer.tex`, `ut:T2`)

The comb of `ut:T2` is `B₂ = T_{χ(p)} B₁`, `χ(p) = ξ_* - λp/κ = ξ_* + λσ_p`, `σ_p = -p/κ`, with `B₁ = d.comb c'`
the `f = 2` finite modification (`TwoZeroDict`).  This module defines `twoZeroComb` and proves the factor
lemmas used in Regions I and II, for real `χ` and `x`:

* `tFac_eq`, `abs_tFac_le`, `tFac_pos`: `T_χ(x) = tanh(π(x-χ)/2) tanh(π(x+χ)/2)` (real), `|T_χ(x)| ≤ π|x - χ|/2`
  (so `T ≤ C λ σ` in window coordinates), `T_χ(x) > 0` for `x > χ ≥ 0`;
* `norm_twoZeroT_le_one`, `norm_twoZeroT_eq_one`: `|T| ≤ 1` on the closed strip and `|T| = 1` on `E_±`;
* `tFac_ge_of_window`: `T_{χ(p)}(x) ≥ c (x - ξ_*)` for `ξ_* + λΣ₀ ≤ x ≤ ξ_* + 1` (`Σ₀ ≥ 2 sup |σ_p|`);
* `tFac_ratio_sub_one_le`: `|T_{χ(p)}(x)/T_{ξ_*}(x) - 1| ≤ C λ/(x - ξ_*)` on the same range;
* `combPhiDeriv_sub_le`, `combPhiDeriv_sub_xiStar_abs_le`: `‖∂_b^i(φ_y - φ_{ξ_*})‖ ≤ C |y - ξ_*|` on `combNMid`,
  `i ≤ 2`, `y ≥ 0` (two-sided form of `combPhiDeriv_sub_xiStar_le`);
* `blaschkeT_eq_exp`: `T_ζ = exp (iπ + φ_ζ)` on `𝒩` (`K1(d)`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Positivity
  FormalResearch.ModularBootstrap.Upper.Window.Tail

/-! ### 1. The real factor -/

/-- The real value `T_χ(x) = tanh(π(x-χ)/2) tanh(π(x+χ)/2)` of the strip factor. -/
noncomputable def tFac (χ x : ℝ) : ℝ := Real.tanh (π * (x - χ) / 2) * Real.tanh (π * (x + χ) / 2)

lemma tFac_eq (χ x : ℝ) : blaschkeT (χ : ℂ) (x : ℂ) = ((tFac χ x : ℝ) : ℂ) :=
  blaschkeT_ofReal_eq χ x

lemma tanh_nonneg_of_nonneg {a : ℝ} (h : 0 ≤ a) : 0 ≤ Real.tanh a := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr h) (Real.cosh_pos a).le

lemma abs_tanh_le_abs (a : ℝ) : |Real.tanh a| ≤ |a| := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (tanh_nonneg_of_nonneg h)]
    exact tanh_le_self' h
  · have h1 := tanh_le_self' (neg_nonneg.mpr h)
    have h0 := tanh_nonneg_of_nonneg (neg_nonneg.mpr h)
    rw [Real.tanh_neg] at h1 h0
    rw [abs_of_nonpos h, abs_of_nonpos (by linarith)]
    linarith

/-- `|T_χ(x)| ≤ π |x - χ| / 2`. -/
lemma abs_tFac_le (χ x : ℝ) : |tFac χ x| ≤ π * |x - χ| / 2 := by
  unfold tFac
  rw [abs_mul]
  have h1 := abs_tanh_le_abs (π * (x - χ) / 2)
  have h2 : |Real.tanh (π * (x + χ) / 2)| ≤ 1 := (Real.abs_tanh_lt_one _).le
  calc |Real.tanh (π * (x - χ) / 2)| * |Real.tanh (π * (x + χ) / 2)|
      ≤ |π * (x - χ) / 2| * 1 :=
        mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg _)
    _ = π * |x - χ| / 2 := by
        rw [mul_one, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]

/-- `T_χ(x) > 0` for `x > χ ≥ 0`. -/
lemma tFac_pos {χ x : ℝ} (hχ : 0 ≤ χ) (hx : χ < x) : 0 < tFac χ x := by
  have hpi := Real.pi_pos
  unfold tFac
  exact mul_pos (tanh_pos_of_pos (by nlinarith)) (tanh_pos_of_pos (by nlinarith))

lemma tFac_le_one (χ x : ℝ) : tFac χ x ≤ 1 := by
  have h1 : tFac χ x ≤ |Real.tanh (π * (x - χ) / 2)| * |Real.tanh (π * (x + χ) / 2)| := by
    unfold tFac; exact le_abs_self _ |>.trans (abs_mul _ _).le
  have h2 := (Real.abs_tanh_lt_one (π * (x - χ) / 2)).le
  have h3 := (Real.abs_tanh_lt_one (π * (x + χ) / 2)).le
  exact h1.trans (by nlinarith [abs_nonneg (Real.tanh (π * (x - χ) / 2)), abs_nonneg (Real.tanh (π * (x + χ) / 2))])

/-- **K1(a), real factor**: `|T_χ| ≤ 1` on `|Im b| ≤ 1/2`. -/
lemma norm_twoZeroT_le_one (χ : ℝ) {b : ℂ} (hb : |b.im| ≤ 1 / 2) : ‖blaschkeT (χ : ℂ) b‖ ≤ 1 :=
  norm_blaschkeT_real_le_one χ hb

/-- **K1(a), real factor**: `|T_χ| = 1` on `E_±`. -/
lemma norm_twoZeroT_eq_one (χ : ℝ) {b : ℂ} (hb : |b.im| = 1 / 2) : ‖blaschkeT (χ : ℂ) b‖ = 1 :=
  norm_blaschkeT_real_eq_one χ hb

/-! ### 2. The factor in window coordinates, beyond the window -/

lemma abs_tanh_sub_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) : |Real.tanh u - Real.tanh v| ≤ |u - v| := by
  rcases le_total v u with h | h
  · rw [abs_of_nonneg (by linarith [tanh_mono_real h]), abs_of_nonneg (by linarith)]
    exact tanh_sub_le' hv h
  · rw [abs_sub_comm, abs_sub_comm u v, abs_of_nonneg (by linarith [tanh_mono_real h]),
      abs_of_nonneg (by linarith)]
    exact tanh_sub_le' hu h

/-- **`T_{χ(p)}(x) ≥ c (x - ξ_*)` beyond the window.**  With `χ = ξ_* + λσ_p`, `|σ_p| ≤ S`, `λ S ≤ ξ_*/2`
and `ξ_* + 2λS ≤ x ≤ ξ_* + 1` one has `T_χ(x) ≥ c₁ (x - ξ_*)` with an absolute `c₁ > 0`. -/
lemma tFac_ge_of_window :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ {l S σp x : ℝ}, 0 < l → |σp| ≤ S → l * S ≤ xiStar / 2 →
      xiStar + 2 * l * S ≤ x → x ≤ xiStar + 1 →
        c₁ * (x - xiStar) ≤ tFac (xiStar + l * σp) x := by
  have hpi := Real.pi_pos
  have hξ := xiStar_pos
  set τ₀ : ℝ := Real.tanh (π * xiStar / 2) with hτ₀
  have hτ₀pos : 0 < τ₀ := tanh_pos_of_pos (by positivity)
  set z₀ : ℝ := π / 4 with hz₀
  have hcz : 0 < Real.cosh z₀ := Real.cosh_pos _
  refine ⟨τ₀ * (π / 4 / Real.cosh z₀), by positivity, fun {l S σp x} hl hσ hlS hx1 hx2 => ?_⟩
  have hS0 : 0 ≤ S := (abs_nonneg _).trans hσ
  have hσle : l * σp ≤ l * S := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hσ) hl.le
  have hσge : -(l * S) ≤ l * σp := by
    have := mul_le_mul_of_nonneg_left (neg_le_of_abs_le hσ) hl.le
    linarith
  have hlS0 : 0 ≤ l * S := mul_nonneg hl.le hS0
  have hxξ : 0 ≤ x - xiStar := by nlinarith
  unfold tFac
  set χ : ℝ := xiStar + l * σp with hχ
  have hχ0 : xiStar / 2 ≤ χ := by rw [hχ]; linarith
  have hxχ : (x - xiStar) / 2 ≤ x - χ := by rw [hχ]; nlinarith
  have hb : τ₀ ≤ Real.tanh (π * (x + χ) / 2) := by
    refine tanh_mono_real ?_
    have : xiStar ≤ x + χ := by
      have : xiStar ≤ x := by linarith
      linarith
    nlinarith
  have ha : (π / 4 / Real.cosh z₀) * (x - xiStar) ≤ Real.tanh (π * (x - χ) / 2) := by
    have hz : π * (x - xiStar) / 4 ≤ π * (x - χ) / 2 := by nlinarith
    refine le_trans ?_ (tanh_mono_real hz)
    have := tanh_ge_div_cosh (z := π * (x - xiStar) / 4) (z₀ := z₀) (by positivity)
      (by rw [hz₀]; nlinarith)
    refine le_trans (le_of_eq ?_) this
    ring
  have hapos : 0 ≤ (π / 4 / Real.cosh z₀) * (x - xiStar) := by positivity
  calc τ₀ * (π / 4 / Real.cosh z₀) * (x - xiStar)
      = (π / 4 / Real.cosh z₀) * (x - xiStar) * τ₀ := by ring
    _ ≤ Real.tanh (π * (x - χ) / 2) * Real.tanh (π * (x + χ) / 2) :=
        mul_le_mul ha hb hτ₀pos.le (hapos.trans ha)

/-- **`T_{χ(p)}/T_{ξ_*} = 1 + O(λ/(x - ξ_*))`** on `ξ_* + 2λS ≤ x ≤ ξ_* + 1` (`|σ_p| ≤ S`, `λ S ≤ ξ_*/2`). -/
lemma tFac_ratio_sub_one_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {l S σp x : ℝ}, 0 < l → |σp| ≤ S → l * S ≤ xiStar / 2 →
      xiStar + 2 * l * S ≤ x → x ≤ xiStar + 1 → xiStar < x →
        |tFac (xiStar + l * σp) x / tFac xiStar x - 1| ≤ C * (l * S / (x - xiStar)) := by
  obtain ⟨c₁, hc₁, hlow⟩ := tFac_ge_of_window
  have hpi := Real.pi_pos
  have hξ := xiStar_pos
  refine ⟨π / c₁, by positivity, fun {l S σp x} hl hσ hlS hx1 hx2 hxξ => ?_⟩
  have hS0 : 0 ≤ S := (abs_nonneg _).trans hσ
  have hlS0 : 0 ≤ l * S := mul_nonneg hl.le hS0
  have hδ : |l * σp| ≤ l * S := by
    rw [abs_mul, abs_of_pos hl]; exact mul_le_mul_of_nonneg_left hσ hl.le
  have hdpos : 0 < x - xiStar := by linarith
  have hQ : c₁ * (x - xiStar) ≤ tFac xiStar x := by
    have := hlow (l := 1) (S := 0) (σp := 0) one_pos (by simp) (by simp; positivity)
      (by linarith) hx2
    simpa using this
  have hQpos : 0 < tFac xiStar x := lt_of_lt_of_le (by positivity) hQ
  have hσle : l * σp ≤ l * S := (le_abs_self _).trans hδ
  have hσge : -(l * S) ≤ l * σp := neg_le_of_abs_le hδ
  have ha : 0 ≤ π * (x - (xiStar + l * σp)) / 2 := by
    have : 0 ≤ x - (xiStar + l * σp) := by linarith
    positivity
  have hb : 0 ≤ π * (x + (xiStar + l * σp)) / 2 := by
    have : 0 ≤ x + (xiStar + l * σp) := by linarith
    positivity
  have ha0 : 0 ≤ π * (x - xiStar) / 2 := by positivity
  have hb0 : 0 ≤ π * (x + xiStar) / 2 := by
    have : 0 ≤ x + xiStar := by linarith
    positivity
  have h1 := abs_tanh_sub_le ha ha0
  have h2 := abs_tanh_sub_le hb hb0
  have e1 : π * (x - (xiStar + l * σp)) / 2 - π * (x - xiStar) / 2 = -(π * (l * σp) / 2) := by ring
  have e2 : π * (x + (xiStar + l * σp)) / 2 - π * (x + xiStar) / 2 = π * (l * σp) / 2 := by ring
  rw [e1, abs_neg, abs_div, abs_mul, abs_of_pos hpi, abs_two] at h1
  rw [e2, abs_div, abs_mul, abs_of_pos hpi, abs_two] at h2
  have hPQ : |tFac (xiStar + l * σp) x - tFac xiStar x| ≤ π * (l * S) := by
    unfold tFac
    set u := Real.tanh (π * (x - (xiStar + l * σp)) / 2)
    set v := Real.tanh (π * (x + (xiStar + l * σp)) / 2)
    set u0 := Real.tanh (π * (x - xiStar) / 2)
    set v0 := Real.tanh (π * (x + xiStar) / 2)
    have hv : |v| ≤ 1 := (Real.abs_tanh_lt_one _).le
    have hu0 : |u0| ≤ 1 := (Real.abs_tanh_lt_one _).le
    have hid : u * v - u0 * v0 = (u - u0) * v + u0 * (v - v0) := by ring
    rw [hid]
    calc |(u - u0) * v + u0 * (v - v0)| ≤ |(u - u0) * v| + |u0 * (v - v0)| := abs_add_le _ _
      _ = |u - u0| * |v| + |u0| * |v - v0| := by rw [abs_mul, abs_mul]
      _ ≤ π * |l * σp| / 2 * 1 + 1 * (π * |l * σp| / 2) :=
          add_le_add (mul_le_mul h1 hv (abs_nonneg _) (by positivity))
            (mul_le_mul hu0 h2 (abs_nonneg _) zero_le_one)
      _ = π * |l * σp| := by ring
      _ ≤ π * (l * S) := mul_le_mul_of_nonneg_left hδ hpi.le
  have hid : tFac (xiStar + l * σp) x / tFac xiStar x - 1 =
      (tFac (xiStar + l * σp) x - tFac xiStar x) / tFac xiStar x := by
    field_simp
  rw [hid, abs_div, abs_of_pos hQpos, div_le_iff₀ hQpos]
  calc |tFac (xiStar + l * σp) x - tFac xiStar x| ≤ π * (l * S) := hPQ
    _ = π / c₁ * (l * S / (x - xiStar)) * (c₁ * (x - xiStar)) := by
        field_simp
    _ ≤ π / c₁ * (l * S / (x - xiStar)) * tFac xiStar x :=
        mul_le_mul_of_nonneg_left hQ (by positivity)

/-! ### 3. The phase of `T_ζ` and the dependence on the site -/

lemma ofReal_mem_combZ' {x : ℝ} (hx : 0 ≤ x) : (x : ℂ) ∈ combZ := ⟨by simpa using hx, by simp⟩

lemma ofReal_mem_combZOpen' {x : ℝ} (hx : -1 / 4 < x) : (x : ℂ) ∈ combZOpen :=
  ⟨by simpa using hx, by simp⟩

/-- **`K1(d)`**: `T_ζ = exp (iπ + φ_ζ)` on `𝒩`, `Re ζ ≥ 0`, `|Im ζ| ≤ 1/8`. -/
lemma blaschkeT_eq_exp {ζ b : ℂ} (hb : b ∈ combN) (hζ : ζ ∈ combZ) :
    blaschkeT ζ b = Complex.exp ((π : ℂ) * Complex.I + phiZeta ζ b) := by
  rw [Complex.exp_add, Complex.exp_pi_mul_I, cexp_phiZeta hb hζ]
  ring

/-- `‖∂_b^i φ_y - ∂_b^i φ_{ξ_*}‖ ≤ C |y - ξ_*|` for every `y ≥ 0` (both sides of `ξ_*`): the site `χ(p)` of
`ut:T2` may lie on either side of `ξ_*`. -/
lemma combPhiDeriv_sub_xiStar_abs_le :
    ∃ C > 0, ∀ (i : ℕ), i ≤ 2 → ∀ {y : ℝ} {b : ℂ}, 0 ≤ y → b ∈ combNMid →
      ‖combPhiDeriv i 0 (y : ℂ) b - combPhiDeriv i 0 (xiStar : ℂ) b‖ ≤ C * |y - xiStar| := by
  obtain ⟨C, hC, h⟩ := combPhiDeriv_sub_le
  refine ⟨C, hC, fun i hi y b hy hb => ?_⟩
  rcases le_total xiStar y with hxy | hxy
  · rw [abs_of_nonneg (by linarith)]
    exact h i hi xiStar_pos.le hxy hb
  · rw [abs_of_nonpos (by linarith), norm_sub_rev]
    have := h i hi hy hxy hb
    linarith

/-- The same in `iteratedDeriv` form: `‖∂_b^i (φ_y - φ_{ξ_*})(b)‖ ≤ C |y - ξ_*|`, `b ∈ 𝒩`, `i ≤ 2`. -/
lemma iteratedDeriv_phiZeta_sub_xiStar_le :
    ∃ C > 0, ∀ (i : ℕ), i ≤ 2 → ∀ {y : ℝ} {b : ℂ}, 0 ≤ y → b ∈ combN →
      ‖iteratedDeriv i (fun b' => phiZeta (y : ℂ) b' - phiZeta (xiStar : ℂ) b') b‖ ≤ C * |y - xiStar| := by
  obtain ⟨C, hC, h⟩ := combPhiDeriv_sub_xiStar_abs_le
  refine ⟨C, hC, fun i hi y b hy hb => ?_⟩
  have hbo : b ∈ combNOpen := combN_subset_combNOpen hb
  have hbm : b ∈ combNMid := combN_subset_combNMid hb
  have hy' : (y : ℂ) ∈ combZOpen := ofReal_mem_combZOpen' (by linarith)
  have hx' : (xiStar : ℂ) ∈ combZOpen := ofReal_mem_combZOpen' (by linarith [xiStar_pos])
  have hdy : ∀ b' ∈ combNOpen, DifferentiableAt ℂ (fun w => phiZeta (y : ℂ) w) b' := fun b' hb' =>
    (hasDerivAt_phiZeta_b hb' hy').differentiableAt
  have hdx : ∀ b' ∈ combNOpen, DifferentiableAt ℂ (fun w => phiZeta (xiStar : ℂ) w) b' := fun b' hb' =>
    (hasDerivAt_phiZeta_b hb' hx').differentiableAt
  have hAy : AnalyticOnNhd ℂ (fun w => phiZeta (y : ℂ) w) combNOpen :=
    DifferentiableOn.analyticOnNhd (fun b' hb' => (hdy b' hb').differentiableWithinAt) isOpen_combNOpen
  have hAx : AnalyticOnNhd ℂ (fun w => phiZeta (xiStar : ℂ) w) combNOpen :=
    DifferentiableOn.analyticOnNhd (fun b' hb' => (hdx b' hb').differentiableWithinAt) isOpen_combNOpen
  have hcy : ContDiffAt ℂ i (fun w => phiZeta (y : ℂ) w) b :=
    ((hAy b hbo).contDiffAt).of_le (by exact_mod_cast le_top)
  have hcx : ContDiffAt ℂ i (fun w => phiZeta (xiStar : ℂ) w) b :=
    ((hAx b hbo).contDiffAt).of_le (by exact_mod_cast le_top)
  rw [iteratedDeriv_fun_sub hcy hcx]
  have e1 := iteratedDeriv_combPhiDeriv_b i 0 hbo hy'
  have e2 := iteratedDeriv_combPhiDeriv_b i 0 hbo hx'
  have e3 : (fun b' => combPhiDeriv 0 0 (y : ℂ) b') = fun b' => phiZeta (y : ℂ) b' := by
    funext b'; exact combPhiDeriv_zero _ _
  have e4 : (fun b' => combPhiDeriv 0 0 (xiStar : ℂ) b') = fun b' => phiZeta (xiStar : ℂ) b' := by
    funext b'; exact combPhiDeriv_zero _ _
  rw [e3] at e1
  rw [e4] at e2
  rw [e1, e2]
  exact h i hi hy hbm

/-! ### 4. The comb `T_{χ(p)} B₁` and the factor lemmas uniform on a compact family -/

namespace TwoZeroDesign

variable {n : ℕ}

/-- The scaled position `σ_p = -p/κ` of the zero `p`. -/
noncomputable def sigmaP (d : TwoZeroDesign n) : ℝ := -d.p / kappaAiry

/-- The site `χ(p) = ξ_* - λ p/κ = ξ_* + λ σ_p` of the extra real factor. -/
noncomputable def chiP (d : TwoZeroDesign n) (c' : ℝ) : ℝ := xiStar + lambdaComb c' * d.sigmaP

/-- The comb `B₂ = T_{χ(p)} B₁` of `ut:T2` (`eq:ut:T2-factor`). -/
noncomputable def twoZeroComb (d : TwoZeroDesign n) (c' : ℝ) (b : ℂ) : ℂ :=
  blaschkeT (d.chiP c' : ℂ) b * d.comb c' b

lemma chiP_eq (d : TwoZeroDesign n) (c' : ℝ) :
    d.chiP c' = xiStar + lambdaComb c' * (-d.p / kappaAiry) := rfl

/-- A compact family has uniformly bounded `|σ_p|`. -/
lemma IsCompactFamily.exists_sigmaP_bound {𝒦 : Set (TwoZeroDesign n)} (h : IsCompactFamily 𝒦) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ d ∈ 𝒦, |d.sigmaP| ≤ S := by
  obtain ⟨R, hR, hb⟩ := h.exists_bound
  have hκ := kappaAiry_pos
  refine ⟨R / kappaAiry, by positivity, fun d hd => ?_⟩
  unfold sigmaP
  rw [abs_div, abs_neg, abs_of_pos hκ]
  exact div_le_div_of_nonneg_right (hb d hd).1 hκ.le

/-- For `c'` large: `λ > 0`, `λ S ≤ ξ_*/2`, hence `χ(p) ≥ ξ_*/2 > 0` (also for `p > 0`). -/
lemma eventually_lambda_small (S : ℝ) :
    ∀ᶠ c' : ℝ in atTop, 0 < lambdaComb c' ∧ lambdaComb c' * S ≤ xiStar / 2 := by
  have h := tendsto_lambdaComb_atTop.mul_const S
  simp only [zero_mul] at h
  filter_upwards [h.eventually_le_const (by have := xiStar_pos; positivity : (0 : ℝ) < xiStar / 2),
    eventually_gt_atTop (0 : ℝ)] with c' h1 h2
  exact ⟨Real.rpow_pos_of_pos (mul_pos kTip_pos h2) _, h1⟩

lemma chiP_ge {d : TwoZeroDesign n} {c' S : ℝ} (hS : |d.sigmaP| ≤ S) (hl : 0 < lambdaComb c')
    (hlS : lambdaComb c' * S ≤ xiStar / 2) : xiStar / 2 ≤ d.chiP c' := by
  unfold chiP
  have := neg_le_of_abs_le hS
  nlinarith

/-- `|T_{χ(p)}| ≤ 1` on the closed strip. -/
lemma norm_chiP_T_le_one (d : TwoZeroDesign n) (c' : ℝ) {b : ℂ} (hb : |b.im| ≤ 1 / 2) :
    ‖blaschkeT (d.chiP c' : ℂ) b‖ ≤ 1 := norm_blaschkeT_real_le_one _ hb

/-- `|T_{χ(p)}| = 1` on `E_±`. -/
lemma norm_chiP_T_eq_one (d : TwoZeroDesign n) (c' : ℝ) {b : ℂ} (hb : |b.im| = 1 / 2) :
    ‖blaschkeT (d.chiP c' : ℂ) b‖ = 1 := norm_blaschkeT_real_eq_one _ hb

/-- **`T ≤ C λ σ`** (`ut:T2`, Region II, `Σ₀`-lobe): `|T_{χ(p)}(ξ_* + λσ)| ≤ C λ σ` for `σ ≥ 1`,
uniformly on a compact family, `c'` large. -/
theorem twoZeroT_le_lam_mul {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ σ : ℝ, 1 ≤ σ →
      |tFac (d.chiP c') (xiStar + lambdaComb c' * σ)| ≤ C * lambdaComb c' * σ := by
  obtain ⟨S, hS0, hS⟩ := hK.exists_sigmaP_bound
  refine ⟨π / 2 * (1 + S), by positivity, ?_⟩
  filter_upwards [eventually_lambda_small S] with c' ⟨hl, _⟩ d hd σ hσ
  refine (abs_tFac_le _ _).trans ?_
  have hx : xiStar + lambdaComb c' * σ - d.chiP c' = lambdaComb c' * (σ - d.sigmaP) := by
    unfold chiP; ring
  rw [hx, abs_mul, abs_of_pos hl]
  have h1 : |σ - d.sigmaP| ≤ (1 + S) * σ := by
    calc |σ - d.sigmaP| ≤ |σ| + |d.sigmaP| := abs_sub _ _
      _ ≤ σ + S := by rw [abs_of_nonneg (by linarith)]; linarith [hS d hd]
      _ ≤ (1 + S) * σ := by nlinarith
  calc π * (lambdaComb c' * |σ - d.sigmaP|) / 2 ≤ π * (lambdaComb c' * ((1 + S) * σ)) / 2 := by
        gcongr
    _ = π / 2 * (1 + S) * lambdaComb c' * σ := by ring

/-- **`T_{χ(p)}(x) ≥ c (x - ξ_*)` beyond `Σ₀`** (`ut:T2`, Region II): with `Σ₀ = 2 sup |σ_p|`, uniformly on a
compact family, for `ξ_* + λ Σ₀ ≤ x ≤ ξ_* + 1`. -/
theorem twoZeroT_ge_beyond {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) :
    ∃ c₁ Sg0 : ℝ, 0 < c₁ ∧ 0 ≤ Sg0 ∧ ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ,
      xiStar + lambdaComb c' * Sg0 ≤ x → x ≤ xiStar + 1 → c₁ * (x - xiStar) ≤ tFac (d.chiP c') x := by
  obtain ⟨S, hS0, hS⟩ := hK.exists_sigmaP_bound
  obtain ⟨c₁, hc₁, hlow⟩ := tFac_ge_of_window
  refine ⟨c₁, 2 * S, hc₁, by positivity, ?_⟩
  filter_upwards [eventually_lambda_small S] with c' ⟨hl, hlS⟩ d hd x hx1 hx2
  exact hlow hl (hS d hd) hlS (by linarith) hx2

/-- **`T_{χ(p)}/T_{ξ_*} = 1 + O(λ/(x - ξ_*))`** for `ξ_* + λ Σ₀ ≤ x ≤ ξ_* + 1` (`ut:T2`, Region II, `eq:ut:T2-IIa`),
uniformly on a compact family. -/
theorem twoZeroT_ratio {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) :
    ∃ C Sg0 : ℝ, 0 ≤ C ∧ 0 ≤ Sg0 ∧ ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ,
      xiStar + lambdaComb c' * Sg0 ≤ x → x ≤ xiStar + 1 → xiStar < x →
      |tFac (d.chiP c') x / tFac xiStar x - 1| ≤ C * (lambdaComb c' / (x - xiStar)) := by
  obtain ⟨S, hS0, hS⟩ := hK.exists_sigmaP_bound
  obtain ⟨C, hC, hr⟩ := tFac_ratio_sub_one_le
  refine ⟨C * S, 2 * S, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_lambda_small S] with c' ⟨hl, hlS⟩ d hd x hx1 hx2 hx3
  have := hr hl (hS d hd) hlS (by linarith) hx2 hx3
  calc _ ≤ C * (lambdaComb c' * S / (x - xiStar)) := this
    _ = C * S * (lambdaComb c' / (x - xiStar)) := by ring

/-- `T_{χ(p)}(x) > 0` for real `x > χ(p)` (`c'` large, so that `χ(p) > 0`). -/
theorem twoZeroT_pos {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) :
    ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ, d.chiP c' < x → 0 < tFac (d.chiP c') x := by
  obtain ⟨S, hS0, hS⟩ := hK.exists_sigmaP_bound
  filter_upwards [eventually_lambda_small S] with c' ⟨hl, hlS⟩ d hd x hx
  have := chiP_ge (hS d hd) hl hlS
  exact tFac_pos (by linarith [xiStar_pos]) hx

/-- **`φ_{χ(p)} - φ_{ξ_*} = O(λ)` in `C²(𝒩)`** (`K1(d)`, `ut:T2`, phase): `‖∂_b^i(φ_{χ(p)} - φ_{ξ_*})‖ ≤ C λ`
on `𝒩`, `i ≤ 2`, uniformly on a compact family, for `c'` large. -/
theorem phiZeta_chiP_sub_le {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ c' : ℝ in atTop, ∀ d ∈ 𝒦, ∀ i : ℕ, i ≤ 2 → ∀ b ∈ combN,
      ‖iteratedDeriv i (fun b' => phiZeta (d.chiP c' : ℂ) b' - phiZeta (xiStar : ℂ) b') b‖ ≤
        C * lambdaComb c' := by
  obtain ⟨S, hS0, hS⟩ := hK.exists_sigmaP_bound
  obtain ⟨C, hC, h⟩ := iteratedDeriv_phiZeta_sub_xiStar_le
  refine ⟨C * S, by positivity, ?_⟩
  filter_upwards [eventually_lambda_small S] with c' ⟨hl, hlS⟩ d hd i hi b hb
  have hge := chiP_ge (hS d hd) hl hlS
  refine (h i hi (by linarith [xiStar_pos]) hb).trans ?_
  have : |d.chiP c' - xiStar| ≤ lambdaComb c' * S := by
    have : d.chiP c' - xiStar = lambdaComb c' * d.sigmaP := by unfold chiP; ring
    rw [this, abs_mul, abs_of_pos hl]
    exact mul_le_mul_of_nonneg_left (hS d hd) hl.le
  calc C * |d.chiP c' - xiStar| ≤ C * (lambdaComb c' * S) := mul_le_mul_of_nonneg_left this hC.le
    _ = C * S * lambdaComb c' := by ring

end TwoZeroDesign

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.iteratedDeriv_phiZeta_sub_xiStar_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms iteratedDeriv_phiZeta_sub_xiStar_le

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.tFac_ge_of_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tFac_ge_of_window

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.tFac_ratio_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tFac_ratio_sub_one_le

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.combPhiDeriv_sub_xiStar_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms combPhiDeriv_sub_xiStar_abs_le

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.TwoZeroDesign.twoZeroT_le_lam_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoZeroDesign.twoZeroT_le_lam_mul

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.TwoZeroDesign.twoZeroT_ge_beyond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoZeroDesign.twoZeroT_ge_beyond

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.TwoZeroDesign.twoZeroT_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoZeroDesign.twoZeroT_ratio

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.TwoZeroDesign.twoZeroT_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoZeroDesign.twoZeroT_pos

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.TwoZeroDesign.phiZeta_chiP_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoZeroDesign.phiZeta_chiP_sub_le

end FormalResearch.ModularBootstrap.TwoLevel
