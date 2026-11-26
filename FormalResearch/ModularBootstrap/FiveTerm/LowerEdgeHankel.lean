module

public import FormalResearch.ModularBootstrap.Integration.StripKernel
public import FormalResearch.ModularBootstrap.FixedWeightTip.PoissonJensenGeneral
public import FormalResearch.ModularBootstrap.Bessel.VCorollaries


/-!
# `cts:edge-hankel` (1): the sharp strip bound for the Hankel continuation (FIVE-L, Lemma C5(1))

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, Lemma C5 (`cts:edge-hankel`) (1):
`∫₀^{c'(ξ_*/2)²/3}|g|K_a dt ≤ C e^{-κ₀c'} M[g]`, `∫₀^∞|g|K_a dt ≤ C M[g]` and
`sup_{|Im b|≤1/2}|G(b)| ≤ C M[g]` with *absolute* constants.  Lean's `Integration.lemmaB_d_integral` /
`lemmaB_d_sup` only have `C = 2e^{92}c'²`.

* `kernelK_le_sixteen_cardyV`: `K_a ≤ 16 V` on `x ≥ ξ_*/2` (from `besselV_comparison` and `I₀(z) ≤ 2e^z/√z`);
* `edge_hankel_integral_sharp`: `∫₀^∞|g|K_a ≤ C M[g]` (head `K_a ≤ e^5`, middle by Lemma G at gap `ξ_*/2` and the crude `c'²`
  comparison, tail by `K_a ≤ 16 V`);
* `edge_hankel_sup_sharp`: `‖hankelContinuation c' g b‖ ≤ C M[g]` for `|Im b| ≤ 1/2`;
* `edge_hankel_exp_small` (generic in `prob`): the exponentially small head, a copy-adaptation of the proof of
  `FixedWeightTip.lemmaG_of_problem` with the weight `K_a ≤ e^{c'(2π/3)x}` (pointwise Poisson-Jensen bound
  `proposition_M_exp_general` and `majorantReal_g_deficit`);
* `edge_hankel_one_virasoro`: the bundle.

Proved, unconditional.  **Not here**: `cts:edge-hankel` (2), the two-term complex Bessel asymptotic of `G(v+i/2)`
(`besselI0C_sector_asymptotic` has the leading term only).  As in `lemmaB_d_sup`, `G` is the *defined* Hankel integral;
agreement with `g(c'b²/3)` on the real axis is the Hankel inversion formula, not formalised here.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.WeightAxioms
open FormalResearch.ModularBootstrap.FixedWeightTip FormalResearch.ModularBootstrap.PoissonJensen

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- `K_a ≤ 16 V` on the outer range `x ≥ ξ_*/2`. -/
theorem kernelK_le_sixteen_cardyV {c' t : ℝ} (hc : 10000 ≤ c')
    (ht : c' * (xiStar / 2) ^ 2 / 3 ≤ t) :
    kernelK 1 (c' / 12) t ≤ 16 * virasoroProblem.cardyV (c' / 12) t := by
  have hc0 : 0 < c' := by linarith
  have hξ := xiStar_pos
  obtain ⟨x, hx, rfl⟩ : ∃ x, xiStar / 2 ≤ x ∧ t = c' * x ^ 2 / 3 := by
    refine ⟨√(3 * t / c'), ?_, ?_⟩
    · apply Real.le_sqrt_of_sq_le
      rw [le_div_iff₀ hc0]; nlinarith
    · have h0 : 0 ≤ 3 * t / c' := by
        have : 0 ≤ t := le_trans (by positivity) ht
        positivity
      rw [Real.sq_sqrt h0]; field_simp
  have hx0 : 0 < x := by linarith
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  have ht0 : 0 ≤ c' * x ^ 2 / 3 := by positivity
  rw [Integration.kernelK_one_eq_besselK (by positivity),
    Integration.virasoro_cardyV_eq_besselV ha ht0]
  have hK : Bessel.besselK (c' / 12) (c' * x ^ 2 / 3) = Bessel.besselI0 (c' * Bessel.besselL x) := by
    have := Bessel.besselK_shift (c' := c') (x := x) (j := 0) hc0 hx0.le
    simpa using this
  rw [hK]
  have hcmp := (Bessel.besselV_comparison (c' := c') (x := x) hc hx).2
  have hz0 : 0 < c' * Bessel.besselL x := by unfold Bessel.besselL; positivity
  have hI := Bessel.besselI0_le_two_mul_exp_div_sqrt hz0
  have hVpos : 0 < Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) := by
    have := Integration.virasoro_cardyV_ge ha ht0
    rw [Integration.virasoro_cardyV_eq_besselV ha ht0] at this
    have : 0 < 8 * π ^ 4 * (c' * x ^ 2 / 3) ^ 2 := by positivity
    linarith
  set z := c' * Bessel.besselL x with hz
  set V := Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) with hV
  set A := √(c' * x ^ 2 / 3) with hA
  have hA0 : 0 < A := Real.sqrt_pos.2 (by positivity)
  have hsx : 0 < √x := Real.sqrt_pos.2 hx0
  have hB : 0 < √z := Real.sqrt_pos.2 hz0
  -- `exp z ≤ 6π A V / √x`
  have hexp : Real.exp z ≤ 6 * π * A * V / √x := by
    have h1 : 1 / A * Real.exp (c' * Bessel.besselL x) / V ≤ 6 * π / √x := hcmp
    rw [← hz] at h1
    rw [div_le_div_iff₀ hVpos hsx] at h1
    rw [le_div_iff₀ hsx]
    have h2 : Real.exp z * √x ≤ 6 * π * V * A := by
      have := mul_le_mul_of_nonneg_right h1 hA0.le
      calc Real.exp z * √x = 1 / A * Real.exp z * √x * A := by field_simp
        _ ≤ 6 * π * V * A := by nlinarith [this]
    linarith
  -- `12 π A ≤ 16 √x √z`
  have hsq : 12 * π * A ≤ 16 * (√x * √z) := by
    have hA2 : A ^ 2 = c' * x ^ 2 / 3 := Real.sq_sqrt (by positivity)
    have hz2 : √z ^ 2 = z := Real.sq_sqrt hz0.le
    have hx2 : √x ^ 2 = x := Real.sq_sqrt hx0.le
    have hzz : z = 2 * π * c' * x / 3 := by rw [hz]; unfold Bessel.besselL; ring
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) (two_ne_zero)).1 ?_
    have hpi := Real.pi_lt_d2
    have hpi0 := Real.pi_pos
    calc (12 * π * A) ^ 2 = 144 * π ^ 2 * (c' * x ^ 2 / 3) := by rw [mul_pow, hA2]; ring
      _ ≤ 256 * (x * z) := by
          rw [hzz]
          have : 0 < c' * x ^ 2 := by positivity
          nlinarith [mul_pos this hpi0]
      _ = (16 * (√x * √z)) ^ 2 := by rw [mul_pow, mul_pow, hz2, hx2]; ring
  calc Bessel.besselI0 z ≤ 2 * Real.exp z / √z := hI
    _ ≤ 2 * (6 * π * A * V / √x) / √z := by gcongr
    _ = (12 * π * A / (√x * √z)) * V := by field_simp; ring
    _ ≤ 16 * V := by
        have h16 : 12 * π * A / (√x * √z) ≤ 16 := by
          rw [div_le_iff₀ (by positivity)]; linarith
        exact mul_le_mul_of_nonneg_right h16 hVpos.le


/-- Decay: `e^{92} c'² C e^{-κ c'} ≤ 1` for large `c'`. -/
lemma exists_decay_le_one (C κ : ℝ) (hκ : 0 < κ) :
    ∃ c₂ : ℝ, ∀ c' : ℝ, c₂ ≤ c' → Real.exp 92 * c' ^ 2 * C * Real.exp (-κ * c') ≤ 1 := by
  have h1 : Tendsto (fun c' : ℝ => c' ^ 2 * Real.exp (-c')) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have h2 : Tendsto (fun c' : ℝ => (κ * c') ^ 2 * Real.exp (-(κ * c'))) atTop (𝓝 0) :=
    h1.comp (tendsto_id.const_mul_atTop hκ)
  have h3 : Tendsto (fun c' : ℝ => Real.exp 92 * C / κ ^ 2 * ((κ * c') ^ 2 * Real.exp (-(κ * c'))))
      atTop (𝓝 0) := by simpa using h2.const_mul (Real.exp 92 * C / κ ^ 2)
  obtain ⟨c₂, hc₂⟩ := eventually_atTop.1 (h3.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨c₂, fun c' hc' => ?_⟩
  have := hc₂ c' hc'
  have heq : Real.exp 92 * C / κ ^ 2 * ((κ * c') ^ 2 * Real.exp (-(κ * c'))) =
      Real.exp 92 * c' ^ 2 * C * Real.exp (-κ * c') := by
    field_simp
  rw [heq] at this
  exact this

/-- **`cts:edge-hankel` (1), integral form, sharp constant (Virasoro).**  For `c' ≥ c₀` and every test
`g`, `∫₀^∞ |g| K_a dt ≤ C M[g]` with an *absolute* `C` (Lean's `lemmaB_d_integral` has `C = 2e^{92}c'²`). -/
theorem edge_hankel_integral_sharp :
    ∃ c₀ C : ℝ, 10000 ≤ c₀ ∧ 0 < C ∧ ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {g : ℝ → ℝ},
      TestClass virasoroProblem (c' / 12) g →
        ∫ t in Ioi 0, |g t| * kernelK 1 (c' / 12) t ≤ C * virasoroProblem.cardyNorm (c' / 12) g := by
  have hξ := xiStar_pos
  obtain ⟨c_deep, C_deep, κ, hcd1, hCd, hκ, hG⟩ :=
    FixedWeightTip.lemmaG_of_problem virasoroProblem (δ := xiStar / 2) (by positivity)
      (by linarith)
  obtain ⟨c₂, hc₂⟩ := exists_decay_le_one C_deep κ hκ
  refine ⟨max (max 10000 c_deep) c₂, Real.exp 5 + 17, le_trans (le_max_left _ _) (le_max_left _ _),
    by positivity, fun {c'} hc' {g} hg => ?_⟩
  have hc10 : 10000 ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hc')
  have hcd : c_deep ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans hc')
  have hc2 : c₂ ≤ c' := (le_max_right _ _).trans hc'
  have hc0 : 0 < c' := by linarith
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  have hshift : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; exact ha
  set M : ℝ := virasoroProblem.cardyNorm (c' / 12) g with hM
  have hMnn : 0 ≤ M := virasoroProblem.cardyNorm_nonneg hshift g
  have hf : IntegrableOn (fun t => |g t| * kernelK 1 (c' / 12) t) (Ioi 0) :=
    (Integration.lemmaB_d_integral (by linarith) hg).1
  have hh : IntegrableOn (fun t => |g t| * virasoroProblem.cardyV (c' / 12) t) (Ioi 0) := hg.int_cardy
  have hgabs : IntegrableOn (fun t => |g t|) (Ioi 0) := Integration.testClass_integrableOn_abs hg
  have hV0 : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ virasoroProblem.cardyV (c' / 12) t := fun t ht =>
    virasoroProblem.cardyV_nonneg hshift (mem_Ioi.mp ht).le
  set t₁ : ℝ := 1 / c' with ht₁
  set t₀ : ℝ := c' * (xiStar / 2) ^ 2 / 3 with ht₀
  have ht₁pos : 0 < t₁ := by positivity
  have ht₀pos : 0 < t₀ := by positivity
  have ht₁₀ : t₁ ≤ t₀ := by
    rw [ht₁, ht₀, div_le_iff₀ hc0]
    have h5 := Bessel.one_fifth_le_xiStar
    have : (1 / 10 : ℝ) ≤ xiStar / 2 := by linarith
    have h2 : (1 / 100 : ℝ) ≤ (xiStar / 2) ^ 2 := by nlinarith
    nlinarith
  -- the three pieces
  have hsplit : Ioi (0 : ℝ) = (Ioc 0 t₁ ∪ Ioc t₁ t₀) ∪ Ioi t₀ := by
    rw [Ioc_union_Ioc_eq_Ioc ht₁pos.le ht₁₀, Ioc_union_Ioi_eq_Ioi ht₀pos.le]
  have hI1 : IntegrableOn (fun t => |g t| * kernelK 1 (c' / 12) t) (Ioc 0 t₁) :=
    hf.mono_set Ioc_subset_Ioi_self
  have hI2 : IntegrableOn (fun t => |g t| * kernelK 1 (c' / 12) t) (Ioc t₁ t₀) :=
    hf.mono_set (fun t ht => ht₁pos.trans ht.1)
  have hI3 : IntegrableOn (fun t => |g t| * kernelK 1 (c' / 12) t) (Ioi t₀) :=
    hf.mono_set (Ioi_subset_Ioi ht₀pos.le)
  have hsplitI : ∫ t in Ioi 0, |g t| * kernelK 1 (c' / 12) t =
      (∫ t in Ioc 0 t₁, |g t| * kernelK 1 (c' / 12) t) +
      (∫ t in Ioc t₁ t₀, |g t| * kernelK 1 (c' / 12) t) +
      ∫ t in Ioi t₀, |g t| * kernelK 1 (c' / 12) t := by
    rw [hsplit, setIntegral_union (Disjoint.union_left (Ioc_disjoint_Ioi ht₁₀)
        Ioc_disjoint_Ioi_same) measurableSet_Ioi (hI1.union hI2) hI3,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hI1 hI2]
  -- piece 1: head
  have hK1 : ∀ t ∈ Ioc 0 t₁, |g t| * kernelK 1 (c' / 12) t ≤ Real.exp 5 * |g t| := by
    intro t ht
    have hK := Integration.kernelK_le_of_le_inv hc0 ht.1.le ht.2
    have hI0 : Bessel.besselI0 (4 * π / √12) ≤ Real.exp 5 := by
      refine (Bessel.besselI0_le_exp (by positivity)).trans (Real.exp_le_exp.mpr ?_)
      have h12 : (3 : ℝ) ≤ √12 := by
        rw [show (3 : ℝ) = √9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num)
      rw [div_le_iff₀ (by linarith)]
      nlinarith [Real.pi_lt_d2]
    calc |g t| * kernelK 1 (c' / 12) t ≤ |g t| * Real.exp 5 := by gcongr; exact hK.trans hI0
      _ = _ := by ring
  have hP1 : ∫ t in Ioc 0 t₁, |g t| * kernelK 1 (c' / 12) t ≤ Real.exp 5 * M := by
    calc ∫ t in Ioc 0 t₁, |g t| * kernelK 1 (c' / 12) t
        ≤ ∫ t in Ioc 0 t₁, Real.exp 5 * |g t| :=
          setIntegral_mono_on hI1 ((hgabs.mono_set Ioc_subset_Ioi_self).const_mul _)
            measurableSet_Ioc hK1
      _ = Real.exp 5 * ∫ t in Ioc 0 t₁, |g t| := integral_const_mul _ _
      _ ≤ Real.exp 5 * ((4 / π ^ 2) * M) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 5).le
          refine le_trans ?_ (Integration.lemmaB_b_integral ha hg)
          refine setIntegral_mono_set hgabs ?_ Ioc_subset_Ioi_self.eventuallySubset
          exact ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => abs_nonneg _
      _ ≤ Real.exp 5 * M := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 5).le
          have hpi := Real.pi_gt_three
          have : 4 / π ^ 2 ≤ 1 := by
            rw [div_le_one (by positivity)]; nlinarith
          nlinarith
  -- piece 2: middle, via Lemma G with gap `ξ_*/2`
  have hP2 : ∫ t in Ioc t₁ t₀, |g t| * kernelK 1 (c' / 12) t ≤ M := by
    have hpt : ∀ t ∈ Ioc t₁ t₀, |g t| * kernelK 1 (c' / 12) t ≤
        Real.exp 92 * c' ^ 2 * (|g t| * virasoroProblem.cardyV (c' / 12) t) := by
      intro t ht
      have h := Integration.kernelK_le_mul_cardyV (by linarith) ht.1.le
      calc |g t| * kernelK 1 (c' / 12) t
          ≤ |g t| * (Real.exp 92 * c' ^ 2 * virasoroProblem.cardyV (c' / 12) t) := by
            gcongr
        _ = _ := by ring
    have hhI2 : IntegrableOn (fun t => |g t| * virasoroProblem.cardyV (c' / 12) t) (Ioc t₁ t₀) :=
      hh.mono_set (fun t ht => ht₁pos.trans ht.1)
    have hGap := hG hcd hg
    rw [show xiStar - xiStar / 2 = xiStar / 2 by ring, intervalIntegral.integral_of_le ht₀pos.le]
      at hGap
    calc ∫ t in Ioc t₁ t₀, |g t| * kernelK 1 (c' / 12) t
        ≤ ∫ t in Ioc t₁ t₀, Real.exp 92 * c' ^ 2 * (|g t| * virasoroProblem.cardyV (c' / 12) t) :=
          setIntegral_mono_on hI2 (hhI2.const_mul _) measurableSet_Ioc hpt
      _ = Real.exp 92 * c' ^ 2 * ∫ t in Ioc t₁ t₀, |g t| * virasoroProblem.cardyV (c' / 12) t :=
          integral_const_mul _ _
      _ ≤ Real.exp 92 * c' ^ 2 * (C_deep * Real.exp (-κ * c') * M) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine le_trans ?_ hGap
          refine setIntegral_mono_set (hh.mono_set Ioc_subset_Ioi_self) ?_
            (Ioc_subset_Ioc_left ht₁pos.le).eventuallySubset
          exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
            mul_nonneg (abs_nonneg _) (hV0 t ht.1)
      _ = (Real.exp 92 * c' ^ 2 * C_deep * Real.exp (-κ * c')) * M := by ring
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right (hc₂ c' hc2) hMnn
      _ = M := one_mul M
  -- piece 3: tail, `K_a ≤ 16 V`
  have hP3 : ∫ t in Ioi t₀, |g t| * kernelK 1 (c' / 12) t ≤ 16 * M := by
    have hpt : ∀ t ∈ Ioi t₀, |g t| * kernelK 1 (c' / 12) t ≤
        16 * (|g t| * virasoroProblem.cardyV (c' / 12) t) := by
      intro t ht
      have h := kernelK_le_sixteen_cardyV hc10 (mem_Ioi.mp ht).le
      calc |g t| * kernelK 1 (c' / 12) t ≤ |g t| * (16 * virasoroProblem.cardyV (c' / 12) t) := by
            gcongr
        _ = _ := by ring
    calc ∫ t in Ioi t₀, |g t| * kernelK 1 (c' / 12) t
        ≤ ∫ t in Ioi t₀, 16 * (|g t| * virasoroProblem.cardyV (c' / 12) t) :=
          setIntegral_mono_on hI3 ((hh.mono_set (Ioi_subset_Ioi ht₀pos.le)).const_mul _)
            measurableSet_Ioi hpt
      _ = 16 * ∫ t in Ioi t₀, |g t| * virasoroProblem.cardyV (c' / 12) t := integral_const_mul _ _
      _ ≤ 16 * M := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine setIntegral_mono_set hh ?_ (Ioi_subset_Ioi ht₀pos.le).eventuallySubset
          exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
            mul_nonneg (abs_nonneg _) (hV0 t ht)
  rw [hsplitI]
  nlinarith only [hP1, hP2, hP3]


/-- **`cts:edge-hankel` (1), strip bound (`cts:strip-unif`), sharp constant (Virasoro).**  For `c' ≥ c₀`,
every test `g` and `|Im b| ≤ 1/2`, `|G(b)| ≤ C M[g]` with an absolute `C`, where `G = hankelContinuation c' g`
(defined by the Hankel-continuation integral; its agreement with `g(c'b²/3)` on the real axis is the Hankel inversion
formula, not formalised, as for `lemmaB_d_sup`). -/
theorem edge_hankel_sup_sharp :
    ∃ c₀ C : ℝ, 10000 ≤ c₀ ∧ 0 < C ∧ ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {g : ℝ → ℝ},
      TestClass virasoroProblem (c' / 12) g → ∀ {b : ℂ}, |b.im| ≤ 1 / 2 →
        ‖Integration.hankelContinuation c' g b‖ ≤ C * virasoroProblem.cardyNorm (c' / 12) g := by
  obtain ⟨c₀, C, hc₀, hC, hbound⟩ := edge_hankel_integral_sharp
  refine ⟨c₀, 2 * π * C, hc₀, by positivity, fun {c'} hc' {g} hg {b} hb => ?_⟩
  have hc0 : 0 < c' := by linarith
  have hint := (Integration.lemmaB_d_integral (by linarith) hg).1
  have hle := hbound hc' hg
  unfold Integration.hankelContinuation
  rw [norm_mul]
  have h2pi : ‖(-2 * (π : ℂ))‖ = 2 * π := by
    rw [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [h2pi]
  have hbd : ‖∫ t in Ioi (0 : ℝ), (g t : ℂ) *
      Integration.besselI0C (4 * (π : ℂ) * Complex.I * b * (Real.sqrt (c' * t / 3) : ℝ))‖ ≤
      ∫ t in Ioi (0 : ℝ), |g t| * kernelK 1 (c' / 12) t := by
    refine norm_integral_le_of_norm_le hint ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact Integration.besselI0C_strip_le hc0 (le_of_lt ht) hb
  calc 2 * π * _ ≤ 2 * π * (C * virasoroProblem.cardyNorm (c' / 12) g) := by
        gcongr
        exact hbd.trans hle
    _ = 2 * π * C * virasoroProblem.cardyNorm (c' / 12) g := by ring


/-- `K_a(φ x) = I₀(c'L(x)) ≤ e^{c'(2π/3)x}` for the concrete kernel. -/
lemma kernelK_le_exp_slit {c' x : ℝ} (hc : 0 < c') (hx : 0 ≤ x) :
    kernelK 1 (c' / 12) (c' * x ^ 2 / 3) ≤ Real.exp (c' * (2 * π / 3) * x) := by
  have ht0 : 0 ≤ c' * x ^ 2 / 3 := by positivity
  rw [Integration.kernelK_one_eq_besselI0 (by positivity) ht0]
  refine (Bessel.besselI0_le_exp (by positivity)).trans (Real.exp_le_exp.2 ?_)
  have heq : (c' / 12) * (c' * x ^ 2 / 3) = (c' * x / 6) ^ 2 := by ring
  rw [heq, Real.sqrt_sq (by positivity)]
  nlinarith [Real.pi_pos]

/-- **`cts:edge-hankel` (1), exponentially small head** (generic in `prob`, at gap `δ = ξ_*/2`): for `c'` large and
every test `g` with `M[g] > 0`, `∫₀^{c'(ξ_*/2)²/3} |g| K_a dt ≤ C e^{-κ₀ c'} M[g]`. -/
theorem edge_hankel_exp_small (prob : FixedWeightProblem) :
    ∃ c₀ C κ : ℝ, 1 ≤ c₀ ∧ 0 < C ∧ 0 < κ ∧ ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {g : ℝ → ℝ},
      TestClass prob (c' / 12) g → 0 < prob.cardyNorm (c' / 12) g →
        ∫ t in (0 : ℝ)..(c' * (xiStar / 2) ^ 2 / 3), |g t| * kernelK 1 (c' / 12) t ≤
          C * Real.exp (-κ * c') * prob.cardyNorm (c' / 12) g := by
  have hξ := xiStar_pos
  obtain ⟨U⟩ := WeightAxioms.fixedWeightAxioms_of_problem prob
  obtain ⟨c_Kw, C_Klo, hcKw8, hCKlo, hPJ_thm⟩ := stripPoissonJensen_general prob
  set δ : ℝ := xiStar / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < xiStar := by linarith
  let C_PJ : ℝ := pjConstOf U.C_e U.c_band C_Klo (slitL xiStar)
  let c_PJ : ℝ := max (max 1 U.c₀) c_Kw
  have hcPJ1 : 1 ≤ c_PJ := (le_max_left 1 U.c₀).trans (le_max_left _ _)
  obtain ⟨C_M1, C_M2, hCM1, hpropM⟩ := proposition_M_exp_general realSliceData
    (C_PJ := C_PJ) (p_e := U.p_e) hcPJ1 U.hp_e_nn
  let κ₀ : ℝ := 2.228 * δ ^ ((3 : ℝ) / 2)
  have hκ₀ : 0 < κ₀ := by positivity
  obtain ⟨C₄, hC₄, hC₄le⟩ := Integration.exists_rpow_le_mul_exp (p := C_M1 + 1) (κ := κ₀ / 2) (by positivity)
  have hC₄_pos : 0 < C₄ := by
    have h1 := hC₄le 1 le_rfl
    simp only [Real.one_rpow] at h1
    have hexp_pos : 0 < Real.exp (κ₀ / 2 * 1) := Real.exp_pos _
    nlinarith
  let x₀ : ℝ := δ
  have hx₀_pos : 0 < x₀ := hδ0
  refine ⟨c_PJ, (1 / δ) * Real.exp C_M2 * C₄, κ₀ / 2, hcPJ1,
    by positivity, half_pos hκ₀, fun {c'} hc' {g} hg hMpos => ?_⟩
  have hc₀' : max 1 U.c₀ ≤ c' := (le_max_left _ _).trans hc'
  have hcKw' : c_Kw ≤ c' := (le_max_right _ _).trans hc'
  have hc1 : 1 ≤ c' := hcPJ1.trans hc'
  have hc0 : 0 < c' := by linarith
  obtain ⟨P, hPCe, hPpe, hPcb, -, -⟩ : ∃ P : PropositionPAxioms prob c',
      P.C_e = U.C_e ∧ P.p_e = U.p_e ∧ P.c_band = U.c_band ∧ P.C_up = U.C_up ∧ P.p_u = U.p_u := by
    have hc₀ : U.c₀ ≤ c' := (le_max_right _ _).trans hc₀'
    exact ⟨(U.axioms_at hc₀).toPropositionPAxioms, U.uniform_C_e hc₀, U.uniform_p_e hc₀,
      U.uniform_c_band hc₀, U.uniform_C_up hc₀, U.uniform_p_u hc₀⟩
  set M : ℝ := prob.cardyNorm (c' / 12) g with hM
  have hPJ_at : ∀ x ∈ Ico 0 xiStar, g (c' * x ^ 2 / 3) ≠ 0 →
      Real.log |g (c' * x ^ 2 / 3)| ≤ c' * majorantReal x + Real.log M -
        (1 / 2 : ℝ) * Real.log c' +
        (U.p_e + 1 / 2) * (1 - realSliceData.slitMassAt x) * Real.log c' +
        realSliceData.slitEntropyAt x + C_PJ := by
    intro x hx hx_ne
    have h := hPJ_thm P hcKw' hg hMpos x hx hx_ne
    rwa [hPCe, hPpe, hPcb] at h
  have hexp_bd := hpropM hc' hMpos hPJ_at
  let t₀ : ℝ := c' * x₀ ^ 2 / 3
  let φ : ℝ → ℝ := fun x => c' * x ^ 2 / 3
  let φ' : ℝ → ℝ := fun x => (2 / 3 : ℝ) * c' * x
  have hφ_nn : ∀ x : ℝ, 0 ≤ φ x := fun x => div_nonneg (mul_nonneg hc0.le (sq_nonneg x)) (by norm_num)
  have hsub : ∫ x in (0 : ℝ)..x₀, (|g (φ x)| * kernelK 1 (c' / 12) (φ x)) * φ' x =
      ∫ t in (0 : ℝ)..t₀, |g t| * kernelK 1 (c' / 12) t := by
    have hd : ∀ x ∈ uIcc (0 : ℝ) x₀, HasDerivAt φ (φ' x) x := fun x _ => by
      dsimp [φ, φ']
      exact ((hasDerivAt_pow 2 x).const_mul c' |>.div_const 3).congr_deriv (by ring)
    have hcont_φ' : ContinuousOn φ' (uIcc (0 : ℝ) x₀) := by dsimp [φ']; fun_prop
    have hcont_f : ContinuousOn (fun t => |g t| * kernelK 1 (c' / 12) t) (φ '' uIcc 0 x₀) := by
      refine (hg.cont.abs.mul (continuous_kernelK 1 (c' / 12)).continuousOn).mono ?_
      rintro t ⟨x, _, rfl⟩
      exact mem_Ici.mpr (hφ_nn x)
    have hcov := intervalIntegral.integral_comp_mul_deriv' hd hcont_φ' hcont_f
    simpa [φ, t₀] using hcov
  rw [← hsub]
  have hpt : ∀ x ∈ Icc (0 : ℝ) x₀,
      (|g (φ x)| * kernelK 1 (c' / 12) (φ x)) * φ' x ≤
        Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * δ⁻¹ * c' *
          Real.exp (-κ₀ * c' + C_M1 * Real.log c') := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hx_pos
    · have hφ0 : φ' 0 = 0 := by dsimp [φ']; ring
      rw [hφ0, mul_zero]
      positivity
    have hx_mem : x ∈ Ico 0 xiStar := ⟨hx.1, hx.2.trans_lt (by linarith)⟩
    have hx_lt1 : x < 1 := hx_mem.2.trans xiStar_lt_one
    have hx_pos_δ : δ ≤ xiStar - x := by dsimp [x₀] at hx; linarith [hx.2]
    have hMexp := hexp_bd x hx_mem
    have hUdef : majorantReal x + (2 * π / 3) * x ≤ -slitDeficit (xiStar - x) :=
      majorantReal_g_deficit hx_mem
    have hslit_def := slitDeficit_ge (le_trans hδ0.le hx_pos_δ) (by linarith [hx.1])
    have hδ_rpow : δ ^ ((3 : ℝ) / 2) ≤ (xiStar - x) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow hδ0.le hx_pos_δ (by norm_num)
    have hU_le : majorantReal x + (2 * π / 3) * x ≤ -κ₀ := by
      calc majorantReal x + (2 * π / 3) * x
          ≤ -slitDeficit (xiStar - x) := hUdef
        _ ≤ -(2.228 * (xiStar - x) ^ ((3 : ℝ) / 2)) := neg_le_neg hslit_def
        _ ≤ -(2.228 * δ ^ ((3 : ℝ) / 2)) :=
            neg_le_neg (mul_le_mul_of_nonneg_left hδ_rpow (by norm_num))
        _ = -κ₀ := rfl
    have hsqrt_le : Real.sqrt (xiStar - x) ≤ 1 := by
      have hle1 : xiStar - x ≤ 1 := by linarith [hx.1, xiStar_lt_one]
      calc Real.sqrt (xiStar - x) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hle1
        _ = 1 := Real.sqrt_one
    have hinv_le : (xiStar - x)⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ0 hx_pos_δ
    have hdx_pos : 0 < xiStar - x := lt_of_lt_of_le hδ0 hx_pos_δ
    have hK_le : kernelK 1 (c' / 12) (φ x) ≤ Real.exp (c' * (2 * π / 3) * x) :=
      kernelK_le_exp_slit hc0 hx.1
    have hK_nn : 0 ≤ kernelK 1 (c' / 12) (φ x) := kernelK_nonneg (by positivity) (hφ_nn x)
    have hexp_comb :
        Real.exp (c' * majorantReal x + C_M1 * Real.sqrt (xiStar - x) * Real.log c') *
          Real.exp (c' * (2 * π / 3) * x) ≤
          Real.exp (-κ₀ * c' + C_M1 * Real.log c') := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : c' * (majorantReal x + (2 * π / 3) * x) ≤ c' * (-κ₀) :=
        mul_le_mul_of_nonneg_left hU_le hc0.le
      have hlogc'_nn : 0 ≤ Real.log c' := Real.log_nonneg hc1
      have h2 : C_M1 * Real.sqrt (xiStar - x) * Real.log c' ≤ C_M1 * Real.log c' := by
        calc C_M1 * Real.sqrt (xiStar - x) * Real.log c'
            ≤ C_M1 * 1 * Real.log c' := by gcongr
          _ = C_M1 * Real.log c' := by ring
      linarith
    have hgK : |g (φ x)| * kernelK 1 (c' / 12) (φ x) ≤
        Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * δ⁻¹ *
          Real.exp (-κ₀ * c' + C_M1 * Real.log c') := by
      calc |g (φ x)| * kernelK 1 (c' / 12) (φ x)
          ≤ (Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * (xiStar - x)⁻¹ *
              Real.exp (c' * majorantReal x + C_M1 * Real.sqrt (xiStar - x) * Real.log c')) *
              Real.exp (c' * (2 * π / 3) * x) :=
            mul_le_mul hMexp hK_le hK_nn (by positivity [hdx_pos])
        _ = (Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * (xiStar - x)⁻¹) *
              (Real.exp (c' * majorantReal x + C_M1 * Real.sqrt (xiStar - x) * Real.log c') *
                Real.exp (c' * (2 * π / 3) * x)) := by ring
        _ ≤ (Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * δ⁻¹) *
              Real.exp (-κ₀ * c' + C_M1 * Real.log c') := by gcongr
    have hφ'_le : φ' x ≤ c' := by
      dsimp [φ']
      nlinarith [hx_lt1, hc0]
    have hφ'_nn : 0 ≤ φ' x := by dsimp [φ']; positivity [hx_pos]
    calc (|g (φ x)| * kernelK 1 (c' / 12) (φ x)) * φ' x
        ≤ (Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * δ⁻¹ *
            Real.exp (-κ₀ * c' + C_M1 * Real.log c')) * c' :=
          mul_le_mul hgK hφ'_le hφ'_nn (by positivity)
      _ = _ := by ring
  have hcont_lhs : ContinuousOn (fun x => (|g (φ x)| * kernelK 1 (c' / 12) (φ x)) * φ' x)
      (uIcc 0 x₀) := by
    have h1 : ContinuousOn (fun x => g (φ x)) (uIcc 0 x₀) :=
      hg.cont.comp (by dsimp [φ]; fun_prop) (fun x _ => mem_Ici.mpr (hφ_nn x))
    exact ((h1.abs.mul ((continuous_kernelK 1 (c' / 12)).continuousOn.comp
      (by dsimp [φ]; fun_prop) (fun _ _ => mem_univ _)))).mul (by dsimp [φ']; fun_prop)
  have hint_bd : ∫ x in (0 : ℝ)..x₀, (|g (φ x)| * kernelK 1 (c' / 12) (φ x)) * φ' x ≤
      x₀ * (Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * δ⁻¹ * c' *
        Real.exp (-κ₀ * c' + C_M1 * Real.log c')) := by
    have hmono := intervalIntegral.integral_mono_on hx₀_pos.le
      (hcont_lhs.intervalIntegrable (μ := volume)) (intervalIntegrable_const (μ := volume)) hpt
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
    exact hmono
  have hx₀_le1 : x₀ ≤ 1 := by dsimp [x₀, δ]; linarith [xiStar_lt_one]
  have hcm_eq : Real.exp (C_M1 * Real.log c') = c' ^ C_M1 := by
    rw [Real.rpow_def_of_pos hc0]; ring_nf
  have hpow_comb : c' ^ (-(1 / 2 : ℝ)) * c' * Real.exp (-κ₀ * c' + C_M1 * Real.log c') ≤
      C₄ * Real.exp (-(κ₀ / 2) * c') := by
    have hcm1_nn : c' ^ (-(1 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
    have hpow_tot : c' ^ (-(1 / 2 : ℝ)) * (c' ^ C_M1 * c') ≤ c' ^ (C_M1 + 1) := by
      have heq : c' ^ C_M1 * c' = c' ^ (C_M1 + 1) := by
        calc c' ^ C_M1 * c' = c' ^ C_M1 * c' ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = c' ^ (C_M1 + 1) := by rw [← Real.rpow_add hc0]
      calc c' ^ (-(1 / 2 : ℝ)) * (c' ^ C_M1 * c') ≤ 1 * (c' ^ C_M1 * c') := by gcongr
        _ = c' ^ (C_M1 + 1) := by rw [one_mul, heq]
    have hc4 := hC₄le c' hc1
    calc c' ^ (-(1 / 2 : ℝ)) * c' * Real.exp (-κ₀ * c' + C_M1 * Real.log c')
        = (c' ^ (-(1 / 2 : ℝ)) * (c' ^ C_M1 * c')) * Real.exp (-κ₀ * c') := by
          rw [Real.exp_add, hcm_eq]; ring
      _ ≤ (C₄ * Real.exp ((κ₀ / 2) * c')) * Real.exp (-κ₀ * c') :=
          mul_le_mul (hpow_tot.trans hc4) le_rfl (Real.exp_pos _).le (by positivity)
      _ = C₄ * Real.exp (-(κ₀ / 2) * c') := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  calc ∫ x in (0 : ℝ)..x₀, (|g (φ x)| * kernelK 1 (c' / 12) (φ x)) * φ' x
      ≤ x₀ * (Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * δ⁻¹ * c' *
          Real.exp (-κ₀ * c' + C_M1 * Real.log c')) := hint_bd
    _ ≤ 1 * (Real.exp C_M2 * M * c' ^ (-(1 / 2 : ℝ)) * δ⁻¹ * c' *
          Real.exp (-κ₀ * c' + C_M1 * Real.log c')) := by gcongr
    _ = ((1 / δ) * Real.exp C_M2 * M) *
          (c' ^ (-(1 / 2 : ℝ)) * c' * Real.exp (-κ₀ * c' + C_M1 * Real.log c')) := by
          rw [one_div]; ring
    _ ≤ ((1 / δ) * Real.exp C_M2 * M) * (C₄ * Real.exp (-(κ₀ / 2) * c')) := by
          gcongr
    _ = (1 / δ) * Real.exp C_M2 * C₄ * Real.exp (-(κ₀ / 2) * c') * M := by ring


/-- **`cts:edge-hankel` (1) at spinless Virasoro (Lemma C5(1))**, bundled.  There are `c₀, C, κ₀ > 0` such that for every
`c' ≥ c₀` and every test `g` (with `M[g] > 0` in the first clause):
* `∫₀^{c'(ξ_*/2)²/3} |g| K_a dt ≤ C e^{-κ₀ c'} M[g]` (`edge_hankel_exp_small`);
* `∫₀^∞ |g| K_a dt ≤ C M[g]` (`edge_hankel_integral_sharp`);
* `sup_{|Im b| ≤ 1/2} |G(b)| ≤ C M[g]` (`edge_hankel_sup_sharp`; `G` the Hankel-continuation integral). -/
theorem edge_hankel_one_virasoro :
    ∃ c₀ C κ₀ : ℝ, 10000 ≤ c₀ ∧ 0 < C ∧ 0 < κ₀ ∧ ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {g : ℝ → ℝ},
      TestClass virasoroProblem (c' / 12) g →
        (0 < virasoroProblem.cardyNorm (c' / 12) g →
          ∫ t in (0 : ℝ)..(c' * (xiStar / 2) ^ 2 / 3), |g t| * kernelK 1 (c' / 12) t ≤
            C * Real.exp (-κ₀ * c') * virasoroProblem.cardyNorm (c' / 12) g) ∧
        ∫ t in Ioi 0, |g t| * kernelK 1 (c' / 12) t ≤ C * virasoroProblem.cardyNorm (c' / 12) g ∧
        ∀ {b : ℂ}, |b.im| ≤ 1 / 2 →
          ‖Integration.hankelContinuation c' g b‖ ≤ C * virasoroProblem.cardyNorm (c' / 12) g := by
  obtain ⟨c₁, C₁, κ, hc₁, hC₁, hκ, h1⟩ := edge_hankel_exp_small virasoroProblem
  obtain ⟨c₂, C₂, hc₂, hC₂, h2⟩ := edge_hankel_integral_sharp
  obtain ⟨c₃, C₃, hc₃, hC₃, h3⟩ := edge_hankel_sup_sharp
  refine ⟨max (max c₁ c₂) c₃, max (max C₁ C₂) C₃, κ, ?_, ?_, hκ, fun {c'} hc' {g} hg => ?_⟩
  · exact hc₂.trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact lt_max_of_lt_left (lt_max_of_lt_left hC₁)
  have hM : 0 ≤ virasoroProblem.cardyNorm (c' / 12) g := by
    have hc0 : (10000 : ℝ) ≤ c' :=
      hc₂.trans ((le_max_right _ _).trans ((le_max_left _ _).trans hc'))
    have hshift : virasoroProblem.totalShift ≤ c' / 12 := by
      rw [virasoroProblem_totalShift]; linarith
    exact virasoroProblem.cardyNorm_nonneg hshift g
  refine ⟨fun hMpos => ?_, ?_, fun {b} hb => ?_⟩
  · refine (h1 ((le_max_left _ _).trans ((le_max_left _ _).trans hc')) hg hMpos).trans ?_
    gcongr
    exact (le_max_left _ _).trans (le_max_left _ _)
  · refine (h2 ((le_max_right _ _).trans ((le_max_left _ _).trans hc')) hg).trans ?_
    gcongr
    exact (le_max_right _ _).trans (le_max_left _ _)
  · refine (h3 (le_max_right _ _ |>.trans hc') hg hb).trans ?_
    gcongr
    exact le_max_right _ _

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.kernelK_le_sixteen_cardyV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.kernelK_le_sixteen_cardyV

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.edge_hankel_integral_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.edge_hankel_integral_sharp

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.edge_hankel_sup_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.edge_hankel_sup_sharp

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.edge_hankel_exp_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.edge_hankel_exp_small

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.edge_hankel_one_virasoro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.edge_hankel_one_virasoro
