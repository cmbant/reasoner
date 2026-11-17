module

public import FormalResearch.Special.AiryTransformBasis
public import FormalResearch.Special.AiryGoodCircles
public import FormalResearch.Special.AiryAsymReal
public import FormalResearch.Special.AiryCftSignEqualityMain

/-!
# Completeness of `{K(·,a_n)}` in the Airy Paley–Wiener space without Hardy-space estimates

Let `F = Aφ ∈ PW` (`φ ∈ L²(0,∞)`) be orthogonal to every `e_n = K(·,a_n)/|Ai'(a_n)|`, i.e. `Ψφ(a_n) = 0` for all `n`.
Then `F = 0` (`airyPW_eq_zero_of_inner_liouville`).  Proof (the "good circles + Liouville" argument of
`LOCAL_AIRY_MODEL` Lemma Q2; it replaces the Hardy-space proof of Theorem Q by the growth bound of `Ψφ` and the lower bound
of `Ai` on good circles):

1. `Ψφ` is entire (`differentiable_airyPsiC`), the zeros of `Ai` are exactly the real simple zeros `a_n`
   (`airyAiC_eq_zero_iff`, `airyZero_deriv_ne_zero`), and `Ψφ(a_n) = 0`; hence `g = Ψφ/Ai` extends to an entire function
   (`exists_entire_quotient`: factor `f = (z-a)·dslope f a`, `h = (z-a)·dslope h a` at each zero).
2. On the good circle `|u| = r_k ∈ [k,k+1]` (`good_circle_exists`): `‖Ai(u)‖² ≥ (1/25π)(1+r)^{-1/2} e(u)` and
   `‖Ψφ(u)‖² ≤ 23‖φ‖²(1+r) e(u)` (`norm_airyPsiC_sq_le`), so `‖g(u)‖² ≤ 575π‖φ‖²(1+r)^{3/2}`.
3. `dslope g 0` is entire and, by the maximum modulus principle on `|z| < r_k`, `‖dslope g 0 (z)‖ ≤ (‖g‖_∞ + ‖g(0)‖)/r_k → 0`;
   so `g` is constant, `Ψφ = c·Ai`.
4. `Aφ = c·Ai` on `ℝ` and `Aφ ∈ L²` force `c = 0` because `∫_{-y}^0 Ai² = K(-y,-y) - K(0,0) → ∞`
   (`airyKer_diag_neg`: `K(-y,-y) = √y/π + O(1/y)`).

No Hardy-space / Fejér–Riesz input is used: only `AiryGoodCircles`, the envelope `airyAiC_norm_sq_le` and the elementary
`κ`-bound of `AiryTransformEnv`.

**Not formalised:** nothing beyond the completeness statement is claimed here (the ONB and Parseval are in `AiryTransformHilbert`).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set Metric
open scoped ComplexInnerProductSpace Real

namespace FormalResearch.Special

/-- **Entire quotient**: if `f, h` are entire, `f` vanishes at every (simple) zero of `h`, then `f/h` extends to an entire
function. -/
lemma exists_entire_quotient {f h : ℂ → ℂ} (hf : Differentiable ℂ f) (hh : Differentiable ℂ h)
    (hz : ∀ a, h a = 0 → f a = 0) (hs : ∀ a, h a = 0 → deriv h a ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, h z ≠ 0 → g z = f z / h z := by
  classical
  refine ⟨fun z => if h z = 0 then deriv f z / deriv h z else f z / h z, ?_, fun z hz => by simp [hz]⟩
  intro b
  by_cases hb : h b = 0
  · have hF1 : Differentiable ℂ (dslope f b) := fun z =>
      ((differentiableOn_dslope (s := Set.univ) Filter.univ_mem).mpr hf.differentiableOn).differentiableAt
        Filter.univ_mem
    have hH1 : Differentiable ℂ (dslope h b) := fun z =>
      ((differentiableOn_dslope (s := Set.univ) Filter.univ_mem).mpr hh.differentiableOn).differentiableAt
        Filter.univ_mem
    have hH1b : dslope h b b ≠ 0 := by rw [dslope_same]; exact hs b hb
    have hev : ∀ᶠ z in 𝓝 b, dslope h b z ≠ 0 := hH1.continuous.continuousAt.eventually_ne hH1b
    have hfb : f b = 0 := hz b hb
    have heq : (fun z => if h z = 0 then deriv f z / deriv h z else f z / h z) =ᶠ[𝓝 b]
        fun z => dslope f b z / dslope h b z := by
      filter_upwards [hev] with z hz1
      by_cases hzb : z = b
      · subst hzb
        simp [hb, dslope_same]
      · have e1 := sub_smul_dslope h b z
        have e2 := sub_smul_dslope f b z
        simp only [smul_eq_mul, hb, hfb, sub_zero] at e1 e2
        have hzb' : z - b ≠ 0 := sub_ne_zero.mpr hzb
        have hhz : h z ≠ 0 := by rw [← e1]; exact mul_ne_zero hzb' hz1
        simp only [hhz, ↓reduceIte]
        rw [← e1, ← e2]
        field_simp
    exact ((hF1 b).div (hH1 b) hH1b).congr_of_eventuallyEq heq
  · have hev : ∀ᶠ z in 𝓝 b, h z ≠ 0 := hh.continuous.continuousAt.eventually_ne hb
    have heq : (fun z => if h z = 0 then deriv f z / deriv h z else f z / h z) =ᶠ[𝓝 b]
        fun z => f z / h z := by
      filter_upwards [hev] with z hz1
      simp only [hz1, ↓reduceIte]
    exact ((hf b).div (hh b) hb).congr_of_eventuallyEq heq

/-- On a good circle: `‖Ψφ(u)‖² ≤ 575π ‖φ‖² (1+r) √(1+r) · ‖Ai(u)‖²`. -/
lemma airyPsiC_sq_le_good (φ : AiryL2) {r : ℝ} (hr : 0 ≤ r) {u : ℂ} (hu : ‖u‖ = r)
    (hgood : 1 / (25 * π) * (1 + r) ^ (-(1 / 2) : ℝ) * airyEnv u ≤ ‖airyAiC u‖ ^ 2) :
    ‖airyPsiC φ u‖ ^ 2 ≤ 575 * π * ‖φ‖ ^ 2 * ((1 + r) * √(1 + r)) * ‖airyAiC u‖ ^ 2 := by
  have h1 := norm_airyPsiC_sq_le φ u
  rw [hu] at h1
  have hs : 0 < √(1 + r) := Real.sqrt_pos.mpr (by linarith)
  have hrp : (1 + r) ^ (-(1 / 2) : ℝ) = 1 / √(1 + r) := by
    rw [Real.rpow_neg (by linarith), Real.sqrt_eq_rpow, one_div (_ ^ _ : ℝ)]
  rw [hrp] at hgood
  have he : airyEnv u ≤ 25 * π * √(1 + r) * ‖airyAiC u‖ ^ 2 := by
    have hpi := Real.pi_pos
    have : airyEnv u / (25 * π * √(1 + r)) ≤ ‖airyAiC u‖ ^ 2 := by
      calc airyEnv u / (25 * π * √(1 + r)) = 1 / (25 * π) * (1 / √(1 + r)) * airyEnv u := by
            field_simp
        _ ≤ _ := hgood
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  calc ‖airyPsiC φ u‖ ^ 2 ≤ 23 * ‖φ‖ ^ 2 * (1 + r) * airyEnv u := h1
    _ ≤ 23 * ‖φ‖ ^ 2 * (1 + r) * (25 * π * √(1 + r) * ‖airyAiC u‖ ^ 2) := by gcongr
    _ = _ := by ring

/-- **Liouville step**: if `Ψφ` vanishes at all zeros `a_n` of `Ai`, then `Ψφ = c · Ai`. -/
theorem airyPsiC_eq_const_mul (φ : AiryL2) (hφ : ∀ n, airyPsi φ (airyZ n) = 0) :
    ∃ c : ℂ, ∀ z, airyPsiC φ z = c * airyAiC z := by
  have hz : ∀ a, airyAiC a = 0 → airyPsiC φ a = 0 := by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := (airyAiC_eq_zero_iff a).mp ha
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [airyPsiC_ofReal]
    exact hφ m
  have hs : ∀ a, airyAiC a = 0 → deriv airyAiC a ≠ 0 := by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := (airyAiC_eq_zero_iff a).mp ha
    exact airyZero_deriv_ne_zero n
  obtain ⟨g, hg, hgq⟩ := exists_entire_quotient (differentiable_airyPsiC φ) differentiable_airyAiC hz hs
  have hprod : ∀ z, airyPsiC φ z = g z * airyAiC z := by
    intro z
    by_cases h0 : airyAiC z = 0
    · rw [h0, mul_zero]; exact hz z h0
    · rw [hgq z h0]; field_simp
  set D : ℝ := 575 * π * ‖φ‖ ^ 2 with hD
  set c0 : ℝ := ‖g 0‖ ^ 2 with hc0
  have hD0 : 0 ≤ D := by positivity
  -- `G = dslope g 0` is entire and tends to `0`
  set G := dslope g 0 with hG
  have hGd : Differentiable ℂ G := fun z =>
    ((differentiableOn_dslope (s := Set.univ) Filter.univ_mem).mpr hg.differentiableOn).differentiableAt
      Filter.univ_mem
  -- bound on good circles
  have hcircle : ∀ k : ℕ, 10 ≤ k → ∃ r : ℝ, (k : ℝ) ≤ r ∧ ∀ z : ℂ, ‖z‖ ≤ r →
      ‖G z‖ ^ 2 ≤ 2 * (D * ((1 + r) * √(1 + r)) + c0) / r ^ 2 := by
    intro k hk
    obtain ⟨r, hr1, hr2, hgood⟩ := good_circle_exists k hk
    have hk10 : (10 : ℝ) ≤ k := by exact_mod_cast hk
    have hrpos : 0 < r := by linarith
    refine ⟨r, hr1, fun z hz => ?_⟩
    have hbd : ∀ u : ℂ, ‖u‖ = r → ‖G u‖ ≤ Real.sqrt (2 * (D * ((1 + r) * √(1 + r)) + c0) / r ^ 2) := by
      intro u hu
      have hAi : airyAiC u ≠ 0 := by
        intro h0
        have := hgood u hu
        rw [h0, norm_zero] at this
        have h1 : 0 < 1 / (25 * π) * (1 + r) ^ (-(1 / 2) : ℝ) * airyEnv u := by
          have := airyEnv_pos u
          have : 0 < (1 + r) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos (by linarith) _
          positivity
        rw [zero_pow two_ne_zero] at this
        linarith
      have h1 := airyPsiC_sq_le_good φ hrpos.le hu (hgood u hu)
      rw [hprod u, norm_mul, mul_pow] at h1
      have hAipos : 0 < ‖airyAiC u‖ ^ 2 := by positivity
      have h2 : ‖g u‖ ^ 2 ≤ D * ((1 + r) * √(1 + r)) := by
        have := h1
        rw [hD] at *
        nlinarith [mul_comm (‖g u‖ ^ 2) (‖airyAiC u‖ ^ 2)]
      have hu0 : u ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hu; linarith
      have h3 : G u = (u - 0)⁻¹ • (g u - g 0) := by rw [hG, dslope_of_ne _ hu0]; rfl
      have h4 : ‖G u‖ = ‖g u - g 0‖ / r := by
        rw [h3, norm_smul, norm_inv, sub_zero, hu]; ring
      have h5 : ‖g u - g 0‖ ^ 2 ≤ 2 * (‖g u‖ ^ 2 + ‖g 0‖ ^ 2) := by
        nlinarith [norm_sub_le (g u) (g 0), norm_nonneg (g u), norm_nonneg (g 0),
          sq_nonneg (‖g u‖ - ‖g 0‖), norm_nonneg (g u - g 0)]
      apply Real.le_sqrt_of_sq_le
      rw [h4, div_pow]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      calc ‖g u - g 0‖ ^ 2 ≤ 2 * (‖g u‖ ^ 2 + ‖g 0‖ ^ 2) := h5
        _ ≤ 2 * (D * ((1 + r) * √(1 + r)) + c0) := by rw [hc0]; linarith
    have hmax : ‖G z‖ ≤ Real.sqrt (2 * (D * ((1 + r) * √(1 + r)) + c0) / r ^ 2) := by
      refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) r) isBounded_ball
        hGd.diffContOnCl ?_ (by rw [closure_ball _ hrpos.ne']; exact mem_closedBall_zero_iff.mpr hz)
      intro u hu
      rw [frontier_ball _ hrpos.ne'] at hu
      exact hbd u (by simpa using hu)
    have := pow_le_pow_left₀ (norm_nonneg _) hmax 2
    rw [Real.sq_sqrt (by positivity)] at this
    exact this
  have hGzero : ∀ z, G z = 0 := by
    intro z
    by_contra hz0
    have hpos : 0 < ‖G z‖ := norm_pos_iff.mpr hz0
    set ε := ‖G z‖ with hε
    set M : ℝ := 8 * D + 2 * c0 with hM
    have hM0 : 0 ≤ M := by positivity
    set R : ℝ := max (max 10 ‖z‖) ((M / ε ^ 2 + 1) ^ 2) with hR
    set k : ℕ := ⌈R⌉₊ with hk
    have hkR : R ≤ k := Nat.le_ceil R
    have hk10 : 10 ≤ k := by
      have : (10 : ℝ) ≤ k := (le_max_left _ _ |>.trans (le_max_left _ _)).trans hkR
      exact_mod_cast this
    obtain ⟨r, hr1, hbound⟩ := hcircle k hk10
    have hrR : R ≤ r := hkR.trans hr1
    have hr10 : (10 : ℝ) ≤ r := (le_max_left _ _ |>.trans (le_max_left _ _)).trans hrR
    have hzr : ‖z‖ ≤ r := ((le_max_right _ _ |>.trans (le_max_left _ _)).trans hrR)
    have hs2 : (M / ε ^ 2 + 1) ^ 2 ≤ r := (le_max_right _ _).trans hrR
    have h1 := hbound z hzr
    set s := √r with hs
    have hspos : 0 < s := Real.sqrt_pos.mpr (by linarith)
    have hsr : s ^ 2 = r := Real.sq_sqrt (by linarith)
    have hs1 : 1 ≤ s := by nlinarith
    have hsM : M / ε ^ 2 + 1 ≤ s := by
      rw [hs]
      exact Real.le_sqrt_of_sq_le hs2
    have h2 : (1 + r) * √(1 + r) ≤ 4 * s ^ 3 := by
      have ha : 1 + r ≤ 2 * s ^ 2 := by nlinarith
      have hb : √(1 + r) ≤ 2 * s := by
        apply Real.sqrt_le_iff.mpr
        constructor
        · positivity
        · nlinarith
      calc (1 + r) * √(1 + r) ≤ (2 * s ^ 2) * (2 * s) :=
            mul_le_mul ha hb (Real.sqrt_nonneg _) (by positivity)
        _ = 4 * s ^ 3 := by ring
    have h3 : 2 * (D * ((1 + r) * √(1 + r)) + c0) / r ^ 2 ≤ M / s := by
      rw [← hsr, div_le_div_iff₀ (by positivity) hspos]
      have h4 : D * ((1 + s ^ 2) * √(1 + s ^ 2)) ≤ D * (4 * s ^ 3) := by
        have := h2; rw [← hsr] at this; exact mul_le_mul_of_nonneg_left this hD0
      have hc00 : 0 ≤ c0 := by positivity
      have hs4 : s ≤ s ^ 4 := by nlinarith [pow_le_pow_right₀ hs1 (show 1 ≤ 4 by norm_num)]
      have h5 : c0 * s ≤ c0 * s ^ 4 := mul_le_mul_of_nonneg_left hs4 hc00
      rw [hM]
      nlinarith [mul_nonneg hD0 (pow_nonneg hspos.le 4)]
    have h6 : M / s < ε ^ 2 := by
      rw [div_lt_iff₀ hspos]
      have : M / ε ^ 2 < s := by linarith
      rw [div_lt_iff₀ (by positivity)] at this
      linarith
    linarith
  have hconst : ∀ z, g z = g 0 := by
    intro z
    by_cases hz0 : z = 0
    · rw [hz0]
    · have := hGzero z
      rw [hG, dslope_of_ne _ hz0] at this
      simp only [slope, vsub_eq_sub, sub_zero, smul_eq_mul] at this
      have h3 : g z - g 0 = 0 := by
        rcases mul_eq_zero.mp this with h | h
        · exact absurd (inv_eq_zero.mp h) hz0
        · exact h
      exact sub_eq_zero.mp h3
  exact ⟨g 0, fun z => by rw [hprod z, hconst z]⟩

/-- **Completeness without Hardy spaces**: `F ∈ PW` orthogonal to every `e_n` is zero. -/
theorem airyPW_eq_zero_of_inner_liouville {F : AiryL2} (hF : F ∈ airyPW)
    (h : ∀ n, inner ℂ (airyBasisVec n) F = 0) : F = 0 := by
  obtain ⟨φ, hφ, rfl⟩ := (mem_airyPW_iff_exists F).mp hF
  have hpsi : ∀ n, airyPsi φ (airyZ n) = 0 := by
    intro n
    have h1 := h n
    rw [inner_airyBasisVec_airyA] at h1
    have hn := airyAi'_airyZ_ne_zero n
    have h2 : (((1 / |airyAi' (airyZ n)| : ℝ) : ℂ)) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; positivity
    exact (mul_eq_zero.mp h1).resolve_left h2
  obtain ⟨c, hc⟩ := airyPsiC_eq_const_mul φ hpsi
  have hAe : airyA φ =ᵐ[volume] airyPsi φ := by
    have := airyA_indProj_ae φ
    rwa [← airyPL_apply, hφ] at this
  have hAc : airyA φ =ᵐ[volume] fun x : ℝ => c * (airyAi x : ℂ) := by
    filter_upwards [hAe] with x hx
    rw [hx, ← airyPsiC_ofReal, hc, airyAiC_ofReal]
  by_cases hc0 : c = 0
  · have : airyA φ =ᵐ[volume] (0 : ℝ → ℂ) := by
      filter_upwards [hAc] with x hx
      rw [hx, hc0]; simp
    exact Lp.eq_zero_iff_ae_eq_zero.mpr this
  · exfalso
    have hint : Integrable (fun x : ℝ => ‖airyA φ x‖ ^ 2) :=
      (Lp.memLp (airyA φ)).integrable_norm_pow (by norm_num)
    have hcpos : 0 < ‖c‖ ^ 2 := by positivity
    apply airyAi_sq_not_integrableOn_Iic 0
    have hI : IntegrableOn (fun x : ℝ => ‖airyA φ x‖ ^ 2 / ‖c‖ ^ 2) (Iic (-0)) :=
      (hint.div_const _).integrableOn
    refine hI.congr_fun_ae ?_
    refine (ae_restrict_of_ae ?_)
    filter_upwards [hAc] with x hx
    rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp

/-- info: 'FormalResearch.Special.airyPsiC_eq_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPsiC_eq_const_mul

/-- info: 'FormalResearch.Special.airyPW_eq_zero_of_inner_liouville' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPW_eq_zero_of_inner_liouville

end FormalResearch.Special
