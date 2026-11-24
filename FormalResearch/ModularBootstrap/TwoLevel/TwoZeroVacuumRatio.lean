module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoZeroVacuumPrelim
public import FormalResearch.ModularBootstrap.Upper.Window.Tail

/-!
# `|B₁/B_ref^{(2)}| ≤ C_𝒦` on the lobe `[0, ξ_*]` (`upper_transfer.tex`, `ut:T2`, "Absolute far-left estimate")

For a compact family `𝒦` of admissible designs there is `C` such that for `c` large, `d ∈ 𝒦` and `0 ≤ x ≤ ξ_*`,
`‖B₁(x)‖ ≤ C ‖B_ref^{(2)}(x)‖` (`twoZero_comb_le_ref_lobe`), where `B₁ = d.comb c` is the `f = 2` design comb and
`B_ref^{(2)} = refComb c 2 (1/4)`.  The proof is that of the paper, factor by factor, with `d = ξ_* - x`,
`a_k = |χ'_k - ξ_*| ≤ Mλ`, `b_k = χ_k - ξ_* ≥ λ/2` (`K0`(c)):

* the simple zero: `|T_{χ'}(x)| ≤ (π/2)(a + d)` and `|T_{χ₀}(x)| ≥ c_lin (b + d)`, so the ratio is
  `≤ (π/2) max(2M, 1)/c_lin` (`abs_tFac_ratio_le`; this is `tanh z/z` decreasing on `z > 0`);
* a conjugate pair: `Q(χ', ε', x) ≤ 2(sinh² z + sin²(π ε'/2))`, `z = π(x - χ')/2`, and `Q(χ₀, ε₀, x) ≥ T_{χ₀}(x)²`,
  so the ratio is bounded by `2(π/2)²(cosh²(z_max) max(2M, 1)² + 4E²)/c_lin²` (`pair_ratio_le`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design FormalResearch.ModularBootstrap.Upper.Holes
  FormalResearch.ModularBootstrap.Upper.Membership FormalResearch.ModularBootstrap.Upper.Window.Cardy FormalResearch.ModularBootstrap.Upper.Window.Tail
open TwoZeroDesign

/-- `zm = π(ξ_* + 1)/2`, the largest argument of the hyperbolic functions on the lobe. -/
noncomputable def lobeZ : ℝ := π * (xiStar + 1) / 2

/-- `c_lin = tanh(πξ_*/2) · (π/2)/cosh(zm)`: `|T_χ(x)| ≥ c_lin (χ - x)` on the lobe. -/
noncomputable def lobeCLin : ℝ := Real.tanh (π * xiStar / 2) * ((π / 2) / Real.cosh lobeZ)

lemma lobeCLin_pos : 0 < lobeCLin := by
  have hπ := Real.pi_pos
  have hξ := xiStar_pos
  unfold lobeCLin
  have : 0 < Real.tanh (π * xiStar / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by positivity)) (Real.cosh_pos _)
  have := Real.cosh_pos lobeZ
  positivity

/-- `|T_χ(x)| ≥ c_lin (χ - x)` for `0 ≤ x ≤ χ`, `ξ_* ≤ χ`, `χ - x ≤ ξ_* + 1`. -/
lemma abs_tFac_ge {χ x : ℝ} (hx : 0 ≤ x) (hxχ : x ≤ χ) (hχ : xiStar ≤ χ) (hχx : χ - x ≤ xiStar + 1) :
    lobeCLin * (χ - x) ≤ |tFac χ x| := by
  have hπ := Real.pi_pos
  have hξ := xiStar_pos
  unfold tFac lobeCLin
  have h1 : (π / 2 / Real.cosh lobeZ) * (χ - x) ≤ Real.tanh (π * (χ - x) / 2) := by
    have := tanh_ge_div_cosh (z := π * (χ - x) / 2) (z₀ := lobeZ) (by nlinarith) (by
      unfold lobeZ; nlinarith)
    refine le_trans (le_of_eq ?_) this
    ring
  have h2 : Real.tanh (π * xiStar / 2) ≤ Real.tanh (π * (x + χ) / 2) :=
    tanh_mono_real (by nlinarith)
  have h3 : Real.tanh (π * (x - χ) / 2) = -Real.tanh (π * (χ - x) / 2) := by
    rw [← Real.tanh_neg]; congr 1; ring
  have hp1 : 0 ≤ Real.tanh (π * (χ - x) / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr (by nlinarith)) (Real.cosh_pos _).le
  have hp2 : 0 < Real.tanh (π * xiStar / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by positivity)) (Real.cosh_pos _)
  rw [h3, neg_mul, abs_neg, abs_of_nonneg (mul_nonneg hp1 (hp2.le.trans h2))]
  have hc : 0 ≤ (π / 2 / Real.cosh lobeZ) * (χ - x) := by
    have := Real.cosh_pos lobeZ
    have : 0 ≤ χ - x := by linarith
    positivity
  calc Real.tanh (π * xiStar / 2) * (π / 2 / Real.cosh lobeZ) * (χ - x)
      = Real.tanh (π * xiStar / 2) * ((π / 2 / Real.cosh lobeZ) * (χ - x)) := by ring
    _ ≤ Real.tanh (π * (x + χ) / 2) * Real.tanh (π * (χ - x) / 2) :=
        mul_le_mul h2 h1 hc (hp2.le.trans h2)
    _ = _ := by ring

/-- The simple zero: `|T_{χ'}(x)| ≤ C_z |T_{χ₀}(x)|` on the lobe, `|χ' - ξ_*| ≤ Mλ`, `χ₀ ≥ ξ_* + λ/2`. -/
lemma abs_tFac_ratio_le {x χ' χ₀ lam M : ℝ} (hx0 : 0 ≤ x) (hxξ : x ≤ xiStar) (hlam : 0 < lam)
    (hχ' : |χ' - xiStar| ≤ M * lam) (hχ₀ : xiStar + lam / 2 ≤ χ₀) (hχ₀u : χ₀ ≤ xiStar + 1) :
    |tFac χ' x| ≤ ((π / 2) * max (2 * M) 1 / lobeCLin) * |tFac χ₀ x| := by
  have hπ := Real.pi_pos
  have hcl := lobeCLin_pos
  have hM : 0 ≤ M * lam := (abs_nonneg _).trans hχ'
  have hM0 : 0 ≤ M := nonneg_of_mul_nonneg_left hM hlam
  have hlow := abs_tFac_ge (χ := χ₀) hx0 (by linarith) (by linarith) (by linarith)
  refine (abs_tFac_le _ _).trans ?_
  have h1 : |x - χ'| ≤ M * lam + (xiStar - x) := by
    have : x - χ' = (x - xiStar) - (χ' - xiStar) := by ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonpos (by linarith : x - xiStar ≤ 0)]
    linarith
  have h2 : M * lam + (xiStar - x) ≤ max (2 * M) 1 * (lam / 2 + (xiStar - x)) := by
    have hm1 : 2 * M ≤ max (2 * M) 1 := le_max_left _ _
    have hm2 : 1 ≤ max (2 * M) 1 := le_max_right _ _
    nlinarith [mul_nonneg hlam.le (sub_nonneg.mpr hm1), mul_nonneg (by linarith : (0 : ℝ) ≤ xiStar - x) (sub_nonneg.mpr hm2)]
  have h3 : lam / 2 + (xiStar - x) ≤ χ₀ - x := by linarith
  have hmax : 0 ≤ max (2 * M) 1 := by positivity
  calc π * |x - χ'| / 2 ≤ π * (max (2 * M) 1 * (χ₀ - x)) / 2 := by
        have : |x - χ'| ≤ max (2 * M) 1 * (χ₀ - x) :=
          h1.trans (h2.trans (mul_le_mul_of_nonneg_left h3 hmax))
        gcongr
    _ = (π / 2 * max (2 * M) 1 / lobeCLin) * (lobeCLin * (χ₀ - x)) := by field_simp
    _ ≤ _ := by gcongr

/-- `sinh² z ≤ z² cosh²(z_m)` for `|z| ≤ z_m`. -/
lemma sinh_sq_le {z zm : ℝ} (hz : |z| ≤ zm) : Real.sinh z ^ 2 ≤ z ^ 2 * Real.cosh zm ^ 2 := by
  have hz0 : 0 ≤ |z| := abs_nonneg z
  have h1 : Real.sinh |z| = Real.tanh |z| * Real.cosh |z| := by
    rw [Real.tanh_eq_sinh_div_cosh]; field_simp
  have h2 : Real.tanh |z| ≤ |z| := tanh_le_self' hz0
  have h3 : Real.cosh |z| ≤ Real.cosh zm := by
    rw [Real.cosh_le_cosh, abs_abs, abs_of_nonneg (hz0.trans hz)]; exact hz
  have h4 : 0 ≤ Real.tanh |z| := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hz0) (Real.cosh_pos _).le
  have hs : Real.sinh |z| ≤ |z| * Real.cosh zm := by
    rw [h1]; exact mul_le_mul h2 h3 (Real.cosh_pos _).le hz0
  have hsz : Real.sinh z ^ 2 = Real.sinh |z| ^ 2 := by
    rcases abs_cases z with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, Real.sinh_neg, neg_sq]
  rw [hsz]
  have hsn : 0 ≤ Real.sinh |z| := Real.sinh_nonneg_iff.mpr hz0
  calc Real.sinh |z| ^ 2 ≤ (|z| * Real.cosh zm) ^ 2 := pow_le_pow_left₀ hsn hs 2
    _ = z ^ 2 * Real.cosh zm ^ 2 := by rw [mul_pow, sq_abs]

/-- The upper bound for a pair modulus: `Q(χ, ε, x) ≤ 2 (sinh² z + sin²(π ε/2))`, `z = π(x - χ)/2`, `0 ≤ ε ≤ 1/2`. -/
lemma blaschkePairQ_le_aux {χ ε x : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) :
    blaschkePairQ χ ε x ≤ 2 * (Real.sinh (π * (x - χ) / 2) ^ 2 + Real.sin (π * ε / 2) ^ 2) := by
  have hπ := Real.pi_pos
  have hS : Real.sin (π * ε / 2) ^ 2 ≤ 1 / 2 := by
    have hs : Real.sin (π * ε / 2) ≤ Real.sin (π / 4) :=
      Real.strictMonoOn_sin.monotoneOn
        ⟨by nlinarith, by nlinarith⟩ ⟨by nlinarith, by nlinarith⟩ (by nlinarith)
    have hs0 : 0 ≤ Real.sin (π * ε / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith) (by nlinarith)
    rw [Real.sin_pi_div_four] at hs
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hfac : ∀ z : ℝ, (Real.sinh z ^ 2 + Real.sin (π * ε / 2) ^ 2) /
      (Real.cosh z ^ 2 - Real.sin (π * ε / 2) ^ 2) ≤ 1 := by
    intro z
    have hcs : Real.cosh z ^ 2 = Real.sinh z ^ 2 + 1 := by linarith [Real.cosh_sq_sub_sinh_sq z]
    have hden : 0 < Real.cosh z ^ 2 - Real.sin (π * ε / 2) ^ 2 := by rw [hcs]; nlinarith [sq_nonneg (Real.sinh z)]
    rw [div_le_one hden, hcs]
    nlinarith
  have hnn : ∀ z : ℝ, 0 ≤ (Real.sinh z ^ 2 + Real.sin (π * ε / 2) ^ 2) /
      (Real.cosh z ^ 2 - Real.sin (π * ε / 2) ^ 2) := by
    intro z
    have hcs : Real.cosh z ^ 2 = Real.sinh z ^ 2 + 1 := by linarith [Real.cosh_sq_sub_sinh_sq z]
    have hden : 0 < Real.cosh z ^ 2 - Real.sin (π * ε / 2) ^ 2 := by rw [hcs]; nlinarith [sq_nonneg (Real.sinh z)]
    positivity
  rw [blaschkePairQ_eq]
  set z₁ := π * (x - χ) / 2
  set z₂ := π * (x + χ) / 2
  have h1 : (Real.sinh z₁ ^ 2 + Real.sin (π * ε / 2) ^ 2) /
      (Real.cosh z₁ ^ 2 - Real.sin (π * ε / 2) ^ 2) ≤
      2 * (Real.sinh z₁ ^ 2 + Real.sin (π * ε / 2) ^ 2) := by
    have hcs : Real.cosh z₁ ^ 2 = Real.sinh z₁ ^ 2 + 1 := by linarith [Real.cosh_sq_sub_sinh_sq z₁]
    have hden : 1 / 2 ≤ Real.cosh z₁ ^ 2 - Real.sin (π * ε / 2) ^ 2 := by rw [hcs]; nlinarith [sq_nonneg (Real.sinh z₁)]
    rw [div_le_iff₀ (by linarith)]
    have hn : 0 ≤ Real.sinh z₁ ^ 2 + Real.sin (π * ε / 2) ^ 2 := by positivity
    nlinarith
  calc _ ≤ (2 * (Real.sinh z₁ ^ 2 + Real.sin (π * ε / 2) ^ 2)) * 1 :=
        mul_le_mul h1 (hfac z₂) (hnn z₂) (by positivity)
    _ = _ := by ring

/-- The constant of the pair ratio. -/
noncomputable def pairRatioConst (M E : ℝ) : ℝ :=
  2 * (π / 2) ^ 2 * (Real.cosh lobeZ ^ 2 * max (2 * M) 1 ^ 2 + 4 * E ^ 2) / lobeCLin ^ 2

lemma pairRatioConst_nonneg (M E : ℝ) : 0 ≤ pairRatioConst M E := by
  have := lobeCLin_pos
  unfold pairRatioConst
  positivity

/-- Lower bound of a pair on the lobe: `Q(χ₀, ε₀, x) ≥ (c_lin (χ₀ - x))²`. -/
lemma pair_lower_lobe {x χ₀ ε₀ : ℝ} (hx0 : 0 ≤ x) (hxχ : x ≤ χ₀) (hχ₀ : xiStar ≤ χ₀)
    (hχ₀u : χ₀ - x ≤ xiStar + 1) (hε₀0 : 0 ≤ ε₀) (hε₀ : ε₀ ≤ 1 / 2) :
    (lobeCLin * (χ₀ - x)) ^ 2 ≤ blaschkePairQ χ₀ ε₀ x := by
  have hlow := blaschkePairQ_ge_sq χ₀ ε₀ x hε₀0 hε₀
  have hT := abs_tFac_ge (χ := χ₀) hx0 hxχ hχ₀ hχ₀u
  have h0 : 0 ≤ lobeCLin * (χ₀ - x) := mul_nonneg lobeCLin_pos.le (by linarith)
  refine le_trans ?_ hlow
  have : (Real.tanh (π * (x - χ₀) / 2) * Real.tanh (π * (x + χ₀) / 2)) ^ 2 = |tFac χ₀ x| ^ 2 := by
    unfold tFac; rw [sq_abs]
  rw [this]
  exact pow_le_pow_left₀ h0 hT 2

/-- Upper bound of a displaced pair on the lobe. -/
lemma pair_upper_lobe {x χ' ε' : ℝ} (hz : |x - χ'| ≤ xiStar + 1) (hε'0 : 0 ≤ ε') (hε'h : ε' ≤ 1 / 2) :
    blaschkePairQ χ' ε' x ≤
      2 * (π / 2) ^ 2 * (Real.cosh lobeZ ^ 2 * (x - χ') ^ 2 + ε' ^ 2) := by
  have hπ := Real.pi_pos
  have hz' : |π * (x - χ') / 2| ≤ lobeZ := by
    unfold lobeZ
    rw [abs_div, abs_mul, abs_of_pos hπ, abs_two]
    nlinarith
  have hsh := sinh_sq_le hz'
  have hsin : Real.sin (π * ε' / 2) ^ 2 ≤ (π * ε' / 2) ^ 2 := Real.sin_sq_le_sq
  have hup := blaschkePairQ_le_aux (χ := χ') (x := x) hε'0 hε'h
  refine hup.trans ?_
  have e : (π * (x - χ') / 2) ^ 2 * Real.cosh lobeZ ^ 2 =
      (π / 2) ^ 2 * (Real.cosh lobeZ ^ 2 * (x - χ') ^ 2) := by ring
  have e2 : (π * ε' / 2) ^ 2 = (π / 2) ^ 2 * ε' ^ 2 := by ring
  nlinarith

/-- The algebra of the pair comparison. -/
lemma pair_key {x χ' χ₀ ε' lam M E : ℝ} (hxξ : x ≤ xiStar) (hlam : 0 < lam)
    (hx1 : |x - χ'| ≤ M * lam + (xiStar - x)) (hE0 : 0 ≤ E)
    (hχ₀ : xiStar + lam / 2 ≤ χ₀) (hε'0 : 0 ≤ ε') (hε' : ε' ≤ E * lam) :
    Real.cosh lobeZ ^ 2 * (x - χ') ^ 2 + ε' ^ 2 ≤
      (Real.cosh lobeZ ^ 2 * max (2 * M) 1 ^ 2 + 4 * E ^ 2) * (χ₀ - x) ^ 2 := by
  have hd : 0 ≤ xiStar - x := by linarith
  have hm : 0 ≤ max (2 * M) 1 := by positivity
  have h1 : |x - χ'| ≤ max (2 * M) 1 * (χ₀ - x) := by
    have h2 : M * lam + (xiStar - x) ≤ max (2 * M) 1 * (lam / 2 + (xiStar - x)) := by
      have hm1 : 2 * M ≤ max (2 * M) 1 := le_max_left _ _
      have hm2 : 1 ≤ max (2 * M) 1 := le_max_right _ _
      nlinarith [mul_nonneg hlam.le (sub_nonneg.mpr hm1), mul_nonneg hd (sub_nonneg.mpr hm2)]
    exact hx1.trans (h2.trans (mul_le_mul_of_nonneg_left (by linarith) hm))
  have h3 : (x - χ') ^ 2 ≤ max (2 * M) 1 ^ 2 * (χ₀ - x) ^ 2 := by
    rw [← sq_abs, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h4 : ε' ^ 2 ≤ 4 * E ^ 2 * (χ₀ - x) ^ 2 := by
    have : ε' ≤ 2 * E * (χ₀ - x) := by nlinarith
    have h5 : ε' ^ 2 ≤ (2 * E * (χ₀ - x)) ^ 2 := pow_le_pow_left₀ hε'0 this 2
    nlinarith
  have hc2 : 0 ≤ Real.cosh lobeZ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h3 hc2]

/-- A conjugate pair: `Q(χ', ε', x) ≤ C_p Q(χ₀, ε₀, x)` on the lobe (`|χ' - ξ_*| ≤ Mλ`, `χ₀ ≥ ξ_* + λ/2`,
`0 ≤ ε' ≤ Eλ`). -/
lemma pair_ratio_le {x χ' χ₀ ε' ε₀ lam M E : ℝ} (hx0 : 0 ≤ x) (hxξ : x ≤ xiStar) (hlam : 0 < lam)
    (hχ' : |χ' - xiStar| ≤ M * lam) (hMl : M * lam ≤ 1) (hχ₀ : xiStar + lam / 2 ≤ χ₀)
    (hχ₀u : χ₀ ≤ xiStar + 1) (hε'0 : 0 ≤ ε') (hε' : ε' ≤ E * lam) (hE : E * lam ≤ 1 / 2)
    (hε₀0 : 0 ≤ ε₀) (hε₀ : ε₀ ≤ 1 / 2) :
    blaschkePairQ χ' ε' x ≤ pairRatioConst M E * blaschkePairQ χ₀ ε₀ x := by
  have hcl := lobeCLin_pos
  have hM : 0 ≤ M * lam := (abs_nonneg _).trans hχ'
  have hM0 : 0 ≤ M := nonneg_of_mul_nonneg_left hM hlam
  have hE0 : 0 ≤ E := nonneg_of_mul_nonneg_left (hε'0.trans hε') hlam
  have hx1 : |x - χ'| ≤ M * lam + (xiStar - x) := by
    have : x - χ' = (x - xiStar) - (χ' - xiStar) := by ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonpos (by linarith : x - xiStar ≤ 0)]
    linarith
  have hup := pair_upper_lobe (x := x) (χ' := χ') (ε' := ε') (by linarith) hε'0 (hε'.trans hE)
  have hlo := pair_lower_lobe (x := x) (χ₀ := χ₀) (ε₀ := ε₀) hx0 (by linarith) (by linarith)
    (by linarith) hε₀0 hε₀
  have hkey := pair_key hxξ hlam hx1 hE0 hχ₀ hε'0 hε'
  have hden : 0 < lobeCLin ^ 2 := by positivity
  unfold pairRatioConst
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  have hK : 0 ≤ 2 * (π / 2) ^ 2 := by positivity
  calc blaschkePairQ χ' ε' x * lobeCLin ^ 2
      ≤ (2 * (π / 2) ^ 2 * (Real.cosh lobeZ ^ 2 * (x - χ') ^ 2 + ε' ^ 2)) * lobeCLin ^ 2 :=
        mul_le_mul_of_nonneg_right hup hden.le
    _ ≤ (2 * (π / 2) ^ 2 * ((Real.cosh lobeZ ^ 2 * max (2 * M) 1 ^ 2 + 4 * E ^ 2) * (χ₀ - x) ^ 2)) *
          lobeCLin ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey hK) hden.le
    _ = (2 * (π / 2) ^ 2 * (Real.cosh lobeZ ^ 2 * max (2 * M) 1 ^ 2 + 4 * E ^ 2)) *
          (lobeCLin * (χ₀ - x)) ^ 2 := by ring
    _ ≤ (2 * (π / 2) ^ 2 * (Real.cosh lobeZ ^ 2 * max (2 * M) 1 ^ 2 + 4 * E ^ 2)) *
          blaschkePairQ χ₀ ε₀ x := by
        refine mul_le_mul_of_nonneg_left hlo ?_
        have := pairRatioConst_nonneg M E
        unfold pairRatioConst at this
        have h2 : 0 ≤ 2 * (π / 2) ^ 2 * (Real.cosh lobeZ ^ 2 * max (2 * M) 1 ^ 2 + 4 * E ^ 2) := by positivity
        exact h2

/-- `K0`(c) lower bound: `χ_k ≥ ξ_* + λ/2` for `k ≥ 2` and `λ Φ_k ≤ 1`. -/
lemma chiQuantile_ge_half {c : ℝ} (hc : 0 < c) {k : ℕ} (hk : 2 ≤ k)
    (hΦ : lambdaComb c * phiQuantile (k : ℝ) ≤ 1) : xiStar + lambdaComb c / 2 ≤ chiQuantile c (k : ℝ) := by
  have hk4 : (1 / 4 : ℝ) ≤ (k : ℝ) := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hlam := lambdaComb_pos' hc
  obtain ⟨hlo, -⟩ := siteRadius_bounds hc hk4
  unfold siteRadius at hlo
  have hΦ1 : 1 ≤ phiQuantile (k : ℝ) := by
    unfold phiQuantile
    exact Real.one_le_rpow (by have : (2 : ℝ) ≤ k := by exact_mod_cast hk
                               linarith) (by norm_num)
  have hc1 := c1K0_le
  have hc0 := c1K0_pos
  set u := lambdaComb c * phiQuantile (k : ℝ) with hu
  have hu1 : lambdaComb c ≤ u := by
    rw [hu]; nlinarith
  have hu0 : 0 ≤ u := hlam.le.trans hu1
  have h1 : u * (1 - (2 * c1K0 / 3) * u) ≥ u / 2 := by
    have : (2 * c1K0 / 3) * u ≤ 1 / 2 := by nlinarith
    nlinarith
  linarith

/-- **`|B₁| ≤ C |B_ref^{(2)}|` on the lobe** (`ut:T2`, `|B₁/B_ref^{(2)}| ≤ C_𝒦` on `[0, ξ_*]`). -/
theorem twoZero_comb_le_ref_lobe {n : ℕ} {𝒦 : Set (TwoZeroDesign n)} (hK : IsCompactFamily 𝒦)
    (hA : ∀ d ∈ 𝒦, d.Adm) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ c in atTop, ∀ d ∈ 𝒦, ∀ x : ℝ, 0 ≤ x → x ≤ xiStar →
      ‖d.comb c (x : ℂ)‖ ≤ C * ‖refComb c 2 (1 / 4) (x : ℂ)‖ := by
  obtain ⟨M, E, hM, hE, hb⟩ := hK.exists_comb_bounds hA
  obtain ⟨Cg, -, hgev⟩ := siteGap_eventually_le
  have hCz : 0 ≤ (π / 2) * max (2 * M) 1 / lobeCLin := by
    have := lobeCLin_pos; have := Real.pi_pos; positivity
  have hCp := pairRatioConst_nonneg M E
  refine ⟨((π / 2) * max (2 * M) 1 / lobeCLin) * pairRatioConst M E ^ (n + 2 - 2), by positivity, ?_⟩
  obtain ⟨Φm, hΦm⟩ : ∃ Φm : ℝ, Φm = phiQuantile (((n + 2 : ℕ) : ℝ) + 2) := ⟨_, rfl⟩
  have hΦm0 : 0 < Φm := by rw [hΦm]; exact phiQuantile_succ_succ_pos (n + 2)
  have hsm : ∀ᶠ c in atTop, lambdaComb c * Φm ≤ 1 ∧ lambdaComb c * M ≤ 1 ∧ lambdaComb c * E ≤ 1 / 2 := by
    have h := tendsto_lambdaComb_atTop
    have h1 := (h.mul_const Φm); have h2 := (h.mul_const M); have h3 := (h.mul_const E)
    rw [zero_mul] at h1 h2 h3
    exact (h1.eventually_le_const (by norm_num : (0 : ℝ) < 1)).and
      ((h2.eventually_le_const (by norm_num : (0 : ℝ) < 1)).and
        (h3.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)))
  filter_upwards [refComb_eq_split 2 (n + 2) (by omega) (η₀ := 1 / 4) (by norm_num) le_rfl, hgev, hsm,
    eventually_gt_atTop (0 : ℝ)] with c hsp hgap hsm hc d hd x hx0 hxξ
  obtain ⟨hlΦ, hlM, hlE⟩ := hsm
  obtain ⟨hgk, -, -, hg1⟩ := hgap
  have hlam := lambdaComb_pos' hc
  have hbim : |((x : ℂ)).im| < 7 / 8 := by simp
  have hFb := comb_family_bounds hlam (hb d hd)
  have hsp' := hsp hbim
  have hphi : ∀ k : ℕ, 2 ≤ k → k ≤ n + 2 → lambdaComb c * phiQuantile (k : ℝ) ≤ 1 ∧
      xiStar + lambdaComb c / 2 ≤ chiQuantile c (k : ℝ) ∧ chiQuantile c (k : ℝ) ≤ xiStar + 1 := fun k hk2 hk => by
    have hk2r : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    have hle : phiQuantile (k : ℝ) ≤ Φm := by
      rw [hΦm]; unfold phiQuantile
      apply Real.rpow_le_rpow (by linarith) _ (by norm_num)
      have : (k : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast hk
      linarith
    have h1 : lambdaComb c * phiQuantile (k : ℝ) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hle hlam.le).trans hlΦ
    refine ⟨h1, chiQuantile_ge_half hc hk2 h1, ?_⟩
    have := (refSite_bounds hc (k := k) (N := n + 2) (by omega) hk).2
    rw [← hΦm] at this
    linarith
  have hzero : ‖blaschkeT (designSite c d.sigmaSeq 2 : ℂ) (x : ℂ)‖ ≤
      ((π / 2) * max (2 * M) 1 / lobeCLin) * ‖blaschkeT (chiQuantile c ((2 : ℕ) : ℝ) : ℂ) (x : ℂ)‖ := by
    rw [tFac_eq, tFac_eq, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    obtain ⟨-, h2, h3⟩ := hphi 2 le_rfl (by omega)
    refine abs_tFac_ratio_le (lam := lambdaComb c) (M := M) hx0 hxξ hlam ?_ h2 h3
    have := (hb d hd).1 2 le_rfl (by omega)
    unfold designSite
    rw [add_sub_cancel_left, abs_mul, abs_of_pos hlam, mul_comm]
    exact mul_le_mul_of_nonneg_right this hlam.le
  have hpair : ∀ i ∈ Finset.range (n + 2 - 2),
      ‖pairT (designSite c d.sigmaSeq (2 + 1 + i)) (lambdaComb c * d.epsHatSite (2 + 1 + i)) (x : ℂ)‖ ≤
        pairRatioConst M E *
          ‖pairT (chiQuantile c ((2 + 1 + i : ℕ) : ℝ)) (1 / 4 * siteGap c (2 + 1 + i)) (x : ℂ)‖ := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [norm_pairT_ofReal, norm_pairT_ofReal]
    obtain ⟨-, h2, h3⟩ := hphi (2 + 1 + i) (by omega) (by omega)
    have hε := (hb d hd).2 (2 + 1 + i) (by omega) (by omega)
    have hsg0 := siteGap_nonneg hc (k := 2 + 1 + i) (by omega)
    have hsg1 := (hgk (2 + 1 + i) (by omega)).trans hg1
    refine pair_ratio_le (lam := lambdaComb c) (M := M) (E := E) hx0 hxξ hlam ?_ (by rw [mul_comm]; exact hlM) h2 h3
      (mul_nonneg hlam.le hε.1) ?_ (by rw [mul_comm]; exact hlE) (by positivity) (by linarith)
    · have := (hb d hd).1 (2 + 1 + i) (by omega) (by omega)
      unfold designSite
      rw [add_sub_cancel_left, abs_mul, abs_of_pos hlam, mul_comm]
      exact mul_le_mul_of_nonneg_right this hlam.le
    · have := mul_le_mul_of_nonneg_left hε.2 hlam.le
      linarith
  have hprod : ∏ i ∈ Finset.range (n + 2 - 2),
      ‖pairT (designSite c d.sigmaSeq (2 + 1 + i)) (lambdaComb c * d.epsHatSite (2 + 1 + i)) (x : ℂ)‖ ≤
      pairRatioConst M E ^ (n + 2 - 2) * ∏ i ∈ Finset.range (n + 2 - 2),
        ‖pairT (chiQuantile c ((2 + 1 + i : ℕ) : ℝ)) (1 / 4 * siteGap c (2 + 1 + i)) (x : ℂ)‖ := by
    calc _ ≤ ∏ i ∈ Finset.range (n + 2 - 2), (pairRatioConst M E *
          ‖pairT (chiQuantile c ((2 + 1 + i : ℕ) : ℝ)) (1 / 4 * siteGap c (2 + 1 + i)) (x : ℂ)‖) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hpair
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  unfold TwoZeroDesign.comb designComb
  rw [hsp', norm_mul, norm_mul, norm_mul, norm_mul, norm_prod, norm_prod]
  have ht := norm_nonneg (combTail c (n + 2) (1 / 4) (x : ℂ))
  have hP0 : 0 ≤ ∏ i ∈ Finset.range (n + 2 - 2),
      ‖pairT (designSite c d.sigmaSeq (2 + 1 + i)) (lambdaComb c * d.epsHatSite (2 + 1 + i)) (x : ℂ)‖ :=
    Finset.prod_nonneg fun _ _ => norm_nonneg _
  calc ‖blaschkeT (designSite c d.sigmaSeq 2 : ℂ) (x : ℂ)‖ * _ * ‖combTail c (n + 2) (1 / 4) (x : ℂ)‖
      ≤ (((π / 2) * max (2 * M) 1 / lobeCLin) * ‖blaschkeT (chiQuantile c ((2 : ℕ) : ℝ) : ℂ) (x : ℂ)‖) *
        (pairRatioConst M E ^ (n + 2 - 2) * ∏ i ∈ Finset.range (n + 2 - 2),
          ‖pairT (chiQuantile c ((2 + 1 + i : ℕ) : ℝ)) (1 / 4 * siteGap c (2 + 1 + i)) (x : ℂ)‖) *
        ‖combTail c (n + 2) (1 / 4) (x : ℂ)‖ := by
        refine mul_le_mul (mul_le_mul hzero hprod hP0 (by positivity)) le_rfl ht (by positivity)
    _ = _ := by ring

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZero_comb_le_ref_lobe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZero_comb_le_ref_lobe

end FormalResearch.ModularBootstrap.TwoLevel
