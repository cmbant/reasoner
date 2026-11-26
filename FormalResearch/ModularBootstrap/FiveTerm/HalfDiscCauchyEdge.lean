module

public import FormalResearch.ModularBootstrap.FiveTerm.HalfDiscCauchy
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Edge evaluation for the half-disc Cauchy identity (FIVE-0 tool)

Real-symmetry on the boundary, the two edge integrands of `cauchyPsi`, and the change of variables
`y = tanh(π τ / 4)` carrying `τ ∈ (0, ∞)` to `y ∈ (0, 1)`.

* `wPt y = (1 - y²)/(1 + y²) + i 2y/(1 + y²) = e^{iψ}`, `ψ = 2 arctan y`; `conj (wPt y) = e^{-iψ}` is the
  edge point of `cts:s3`; `sTan (1 + τ i) = wPt (tanh(π τ/4))` (`sTan_one_add_eq_wPt`).
* `CauchyClass.conj_boundary`: `H (z̄) = conj (H z)` on the closure off `{±i, 1}`.
* `cauchyPsi_conj`: `Ψ_H (s̄) = conj (Ψ_H s)` on the closed strip off `{0, 1}`.
* `re_cauchyPsi_left`, `re_cauchyPsi_right`: the real parts of the two edge integrands.
* `integral_eq_two_re`: `∫_ℝ g = 2 ∫_{(0,∞)} Re g` for `g(-τ) = conj g(τ)`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- `e^{iψ}` with `ψ = 2 arctan y`, as an explicit point of the unit circle. -/
noncomputable def wPt (y : ℝ) : ℂ :=
  (((1 - y ^ 2) / (1 + y ^ 2) : ℝ) : ℂ) + ((2 * y / (1 + y ^ 2) : ℝ) : ℂ) * Complex.I

lemma re_wPt (y : ℝ) : (wPt y).re = (1 - y ^ 2) / (1 + y ^ 2) := by
  simp only [wPt, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]

lemma im_wPt (y : ℝ) : (wPt y).im = 2 * y / (1 + y ^ 2) := by
  simp only [wPt, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, zero_add, add_zero]

lemma wPt_mul_conj (y : ℝ) : wPt y * starRingEnd ℂ (wPt y) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_apply, re_wPt, im_wPt]
  have : (1 + y ^ 2 : ℝ) ≠ 0 := by positivity
  have h : ((1 - y ^ 2) / (1 + y ^ 2)) * ((1 - y ^ 2) / (1 + y ^ 2)) +
      (2 * y / (1 + y ^ 2)) * (2 * y / (1 + y ^ 2)) = 1 := by
    field_simp; ring
  rw [h]; simp

lemma wPt_eq (y : ℝ) : wPt y = (1 + Complex.I * (y : ℂ)) / (1 - Complex.I * (y : ℂ)) := by
  have h1 : (1 - Complex.I * (y : ℂ)) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h2 : (1 + (y : ℂ) ^ 2) ≠ 0 := by
    have : (1 + y ^ 2 : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  rw [eq_div_iff h1, wPt]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

lemma sTan_one_add_eq_wPt (τ : ℝ) : sTan (1 + (τ : ℂ) * Complex.I) = wPt (Real.tanh (π * τ / 4)) := by
  rw [sTan_one_add, wPt_eq]

lemma tanh_pi_mul_div_four_mem {τ : ℝ} : |Real.tanh (π * τ / 4)| < 1 := by
  rw [abs_lt]; exact ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩

lemma sTan_conj (s : ℂ) : sTan (starRingEnd ℂ s) = starRingEnd ℂ (sTan s) := by
  unfold sTan
  rw [← Complex.tan_conj]
  congr 1
  rw [map_div₀, map_mul, Complex.conj_ofReal, map_ofNat]

section

variable {H : ℂ → ℂ} {h1 : ℝ}

lemma closure_halfDisc_conj {z : ℂ} (hz : z ∈ closure halfDisc) : starRingEnd ℂ z ∈ closure halfDisc := by
  have hne : (𝓝[halfDisc] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hz
  refine mem_closure_of_tendsto (f := fun z => starRingEnd ℂ z) (b := 𝓝[halfDisc] z) ?_ ?_
  · exact (Complex.continuous_conj.tendsto z).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    refine ⟨by simpa using hx.1, by simpa using hx.2⟩

lemma halfDisc_subset_cont : halfDisc ⊆ closure halfDisc \ {Complex.I, -Complex.I, 1} := by
  intro z hz
  refine ⟨subset_closure hz, ?_⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or]
  have h1 := hz.1
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> rw [h] at h1 <;> simp at h1

/-- Real symmetry persists on the closure off the three singular points. -/
lemma CauchyClass.conj_boundary (hH : CauchyClass H h1) {z : ℂ}
    (hz : z ∈ closure halfDisc \ {Complex.I, -Complex.I, 1}) :
    H (starRingEnd ℂ z) = starRingEnd ℂ (H z) := by
  have hne : (𝓝[halfDisc] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hz.1
  have hzbar : starRingEnd ℂ z ∈ closure halfDisc \ {Complex.I, -Complex.I, 1} := by
    refine ⟨closure_halfDisc_conj hz.1, ?_⟩
    have hz' := hz.2
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz' ⊢
    obtain ⟨a, b, c⟩ := hz'
    refine ⟨?_, ?_, ?_⟩
    · intro h; apply b
      have := congrArg (starRingEnd ℂ) h
      simpa using this
    · intro h; apply a
      have := congrArg (starRingEnd ℂ) h
      simpa using this
    · intro h; apply c
      have := congrArg (starRingEnd ℂ) h
      simpa using this
  have t1 : Tendsto H (𝓝[halfDisc] z) (𝓝 (H z)) :=
    (hH.cont z hz).tendsto.mono_left (nhdsWithin_mono z halfDisc_subset_cont)
  have t2 : Tendsto (fun x => H (starRingEnd ℂ x)) (𝓝[halfDisc] z) (𝓝 (H (starRingEnd ℂ z))) := by
    have hmap : Tendsto (fun x => starRingEnd ℂ x) (𝓝[halfDisc] z) (𝓝[halfDisc] (starRingEnd ℂ z)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (Complex.continuous_conj.tendsto z).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        exact ⟨by simpa using hx.1, by simpa using hx.2⟩
    have t0 : Tendsto H (𝓝[halfDisc] (starRingEnd ℂ z)) (𝓝 (H (starRingEnd ℂ z))) :=
      (hH.cont _ hzbar).tendsto.mono_left (nhdsWithin_mono _ halfDisc_subset_cont)
    exact t0.comp hmap
  have t3 : Tendsto (fun x => starRingEnd ℂ (H x)) (𝓝[halfDisc] z) (𝓝 (starRingEnd ℂ (H z))) :=
    (Complex.continuous_conj.tendsto _).comp t1
  have t4 : Tendsto (fun x => H (starRingEnd ℂ x)) (𝓝[halfDisc] z) (𝓝 (starRingEnd ℂ (H z))) :=
    t3.congr' (by
      filter_upwards [self_mem_nhdsWithin] with x hx using (hH.conj x hx).symm)
  exact tendsto_nhds_unique t2 t4

lemma sTan_mem_cont {s : ℂ} (hs : s ∈ unitStripCl \ {0, 1}) :
    sTan s ∈ closure halfDisc \ {Complex.I, -Complex.I, 1} := by
  refine ⟨sTan_mem_closure hs.1, ?_⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or]
  have h0 : s ≠ 1 := fun h => hs.2 (Or.inr h)
  exact ⟨sTan_ne_I s hs.1, sTan_ne_neg_I s hs.1, fun h => h0 ((sTan_eq_one_iff hs.1).1 h)⟩

lemma conj_mem_unitStripCl {s : ℂ} (hs : s ∈ unitStripCl \ {0, 1}) :
    starRingEnd ℂ s ∈ unitStripCl \ {0, 1} := by
  refine ⟨⟨by simpa using hs.1.1, by simpa using hs.1.2⟩, ?_⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or]
  have := hs.2
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at this
  refine ⟨fun h => this.1 ?_, fun h => this.2 ?_⟩
  · have := congrArg (starRingEnd ℂ) h; simpa using this
  · have := congrArg (starRingEnd ℂ) h; simpa using this

/-- `Ψ_H (s̄) = conj (Ψ_H s)` on the closed strip off `{0, 1}`. -/
lemma cauchyPsi_conj (hH : CauchyClass H h1) {s : ℂ} (hs : s ∈ unitStripCl \ {0, 1}) :
    cauchyPsi H h1 (starRingEnd ℂ s) = starRingEnd ℂ (cauchyPsi H h1 s) := by
  have hc := hH.conj_boundary (sTan_mem_cont hs)
  unfold cauchyPsi
  rw [sTan_conj, hc]
  simp only [map_mul, map_div₀, map_add, map_sub, map_one, map_pow, Complex.conj_ofReal]

/-! ### The substitution `y = tanh(π τ / 4)` -/

lemma tanh_pos_iff' {x : ℝ} : 0 < Real.tanh x ↔ 0 < x := by
  rw [Real.tanh_eq_sinh_div_cosh, div_pos_iff_of_pos_right (Real.cosh_pos x), Real.sinh_pos_iff]

lemma hasDerivAt_tanhScaled (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => Real.tanh (π * τ / 4)) (π / 4 * (1 - Real.tanh (π * τ / 4) ^ 2)) τ := by
  have hl : HasDerivAt (fun τ : ℝ => π * τ / 4) (π / 4) τ := by
    simpa [mul_comm, div_eq_mul_inv, mul_assoc] using ((hasDerivAt_id τ).const_mul π).div_const 4
  have hs := (Real.hasDerivAt_sinh (π * τ / 4)).comp τ hl
  have hc := (Real.hasDerivAt_cosh (π * τ / 4)).comp τ hl
  have hq : HasDerivAt (fun τ : ℝ => Real.sinh (π * τ / 4) / Real.cosh (π * τ / 4)) _ τ :=
    hs.div hc (Real.cosh_pos _).ne'
  have e : (fun τ : ℝ => Real.tanh (π * τ / 4)) = fun τ => Real.sinh (π * τ / 4) / Real.cosh (π * τ / 4) := by
    funext τ; rw [Real.tanh_eq_sinh_div_cosh]
  rw [e]
  refine hq.congr_deriv ?_
  have hcosh : Real.cosh (π * τ / 4) ≠ 0 := (Real.cosh_pos _).ne'
  have := Real.cosh_sq (π * τ / 4)
  simp only [Function.comp, Real.tanh_eq_sinh_div_cosh]
  field_simp

lemma tanhScaled_image : (fun τ : ℝ => Real.tanh (π * τ / 4)) '' Ioi 0 = Ioo 0 1 := by
  ext y
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨tanh_pos_iff'.2 (by have := Real.pi_pos; have : (0 : ℝ) < τ := hτ; positivity),
      Real.tanh_lt_one _⟩
  · intro hy
    obtain ⟨x, -, hx⟩ := Real.tanh_surjOn ⟨by linarith [hy.1], hy.2⟩
    have hx0 : 0 < x := tanh_pos_iff'.1 (by rw [hx]; exact hy.1)
    refine ⟨4 * x / π, ?_, ?_⟩
    · have := Real.pi_pos; show (0 : ℝ) < 4 * x / π; positivity
    · have hπ : π ≠ 0 := Real.pi_pos.ne'
      show Real.tanh (π * (4 * x / π) / 4) = y
      rw [← hx]; congr 1; field_simp

lemma tanhScaled_injOn : InjOn (fun τ : ℝ => Real.tanh (π * τ / 4)) (Ioi 0) := by
  intro a _ b _ h
  have h2 := Real.tanh_injective h
  have hπ : π ≠ 0 := Real.pi_pos.ne'
  field_simp at h2
  exact h2

/-- Change of variables `y = tanh(π τ/4)`, `(0,∞) → (0,1)`. -/
lemma integral_Ioo_eq_Ioi (G : ℝ → ℝ) :
    ∫ y in Ioo (0 : ℝ) 1, G y =
      ∫ τ in Ioi (0 : ℝ), π / 4 * (1 - Real.tanh (π * τ / 4) ^ 2) * G (Real.tanh (π * τ / 4)) := by
  have := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ))
    (f := fun τ : ℝ => Real.tanh (π * τ / 4))
    (f' := fun τ => π / 4 * (1 - Real.tanh (π * τ / 4) ^ 2)) measurableSet_Ioi
    (fun τ _ => (hasDerivAt_tanhScaled τ).hasDerivWithinAt) tanhScaled_injOn G
  rw [tanhScaled_image] at this
  rw [this]
  refine setIntegral_congr_fun measurableSet_Ioi (fun τ _ => ?_)
  have h1 : 0 ≤ π / 4 * (1 - Real.tanh (π * τ / 4) ^ 2) := by
    have := Real.tanh_lt_one (π * τ / 4)
    have := Real.neg_one_lt_tanh (π * τ / 4)
    have := Real.pi_pos
    have h3 : 0 ≤ 1 - Real.tanh (π * τ / 4) ^ 2 := by nlinarith
    positivity
  rw [abs_of_nonneg h1, smul_eq_mul]

lemma integrableOn_Ioo_iff_Ioi (G : ℝ → ℝ) :
    IntegrableOn G (Ioo (0 : ℝ) 1) ↔
      IntegrableOn (fun τ : ℝ => π / 4 * (1 - Real.tanh (π * τ / 4) ^ 2) * G (Real.tanh (π * τ / 4)))
        (Ioi (0 : ℝ)) := by
  have := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Ioi (0 : ℝ))
    (f := fun τ : ℝ => Real.tanh (π * τ / 4))
    (f' := fun τ => π / 4 * (1 - Real.tanh (π * τ / 4) ^ 2)) measurableSet_Ioi
    (fun τ _ => (hasDerivAt_tanhScaled τ).hasDerivWithinAt) tanhScaled_injOn G
  rw [tanhScaled_image] at this
  rw [this]
  refine integrableOn_congr_fun (fun τ _ => ?_) measurableSet_Ioi
  have h1 : 0 ≤ π / 4 * (1 - Real.tanh (π * τ / 4) ^ 2) := by
    have := Real.tanh_lt_one (π * τ / 4)
    have := Real.neg_one_lt_tanh (π * τ / 4)
    have := Real.pi_pos
    have h3 : 0 ≤ 1 - Real.tanh (π * τ / 4) ^ 2 := by nlinarith
    positivity
  simp only [abs_of_nonneg h1, smul_eq_mul]

/-- The real line is twice the half line for a conjugate-symmetric integrable function. -/
lemma integral_eq_two_re {g : ℝ → ℂ} (hg : Integrable g)
    (hsym : ∀ τ : ℝ, 0 < τ → g (-τ) = starRingEnd ℂ (g τ)) :
    ∫ τ, g τ = ((2 * ∫ τ in Ioi (0 : ℝ), (g τ).re : ℝ) : ℂ) := by
  have h1 := integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hg
  rw [Set.compl_Ioi] at h1
  have h2 : ∫ τ in Iic (0 : ℝ), g τ = ∫ τ in Ioi (0 : ℝ), starRingEnd ℂ (g τ) := by
    have := integral_comp_neg_Iic (0 : ℝ) (fun x => g (-x))
    simp only [neg_neg] at this
    rw [this, neg_zero]
    exact setIntegral_congr_fun measurableSet_Ioi (fun τ hτ => hsym τ hτ)
  rw [← h1, h2]
  have hgi : Integrable g (volume.restrict (Ioi (0 : ℝ))) := hg.integrableOn
  rw [integral_conj, Complex.add_conj]
  have := integral_re hgi
  simp only [RCLike.re_to_complex] at this
  rw [← this]

/-! ### The two edge integrands -/

lemma cauchyPsi_left (H : ℂ → ℂ) (h1 : ℝ) (τ : ℝ) :
    cauchyPsi H h1 ((τ : ℂ) * Complex.I) =
      ((π / 4 * (1 - Real.tanh (π * τ / 4) ^ 2) / (-(Real.tanh (π * τ / 4) ^ 2)) : ℝ) : ℂ) *
        (H (Complex.I * (Real.tanh (π * τ / 4) : ℂ)) - 1 - h1 * (Complex.I * (Real.tanh (π * τ / 4) : ℂ))) := by
  unfold cauchyPsi
  rw [sTan_I_mul]
  set y := Real.tanh (π * τ / 4) with hy
  have h2 : (Complex.I * (y : ℂ)) ^ 2 = -(y : ℂ) ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
  rw [h2]
  push_cast
  ring

lemma re_cauchyPsi_left (H : ℂ → ℂ) (h1 : ℝ) (τ : ℝ) :
    (cauchyPsi H h1 ((τ : ℂ) * Complex.I)).re =
      π / 4 * (1 - Real.tanh (π * τ / 4) ^ 2) / (-(Real.tanh (π * τ / 4) ^ 2)) *
        ((H (Complex.I * (Real.tanh (π * τ / 4) : ℂ))).re - 1) := by
  rw [cauchyPsi_left, Complex.re_ofReal_mul]
  congr 1
  generalize Real.tanh (π * τ / 4) = y
  simp [Complex.mul_re]

lemma cauchyPsi_right (H : ℂ → ℂ) (h1 : ℝ) (τ : ℝ) :
    cauchyPsi H h1 (1 + (τ : ℂ) * Complex.I) =
      ((π / 4 * (2 * ((1 - Real.tanh (π * τ / 4) ^ 2) / (1 + Real.tanh (π * τ / 4) ^ 2))) : ℝ) : ℂ) *
        (starRingEnd ℂ (wPt (Real.tanh (π * τ / 4))) *
          (H (wPt (Real.tanh (π * τ / 4))) - 1 - h1 * wPt (Real.tanh (π * τ / 4)))) := by
  unfold cauchyPsi
  rw [sTan_one_add_eq_wPt]
  set y := Real.tanh (π * τ / 4) with hy
  set w := wPt y with hw
  have hw1 : w * starRingEnd ℂ w = 1 := wPt_mul_conj y
  have hw0 : w ≠ 0 := by
    intro h; rw [h, zero_mul] at hw1; exact zero_ne_one hw1
  have hc : starRingEnd ℂ w + w = ((2 * ((1 - y ^ 2) / (1 + y ^ 2)) : ℝ) : ℂ) := by
    rw [add_comm, Complex.add_conj, hw, re_wPt]
  have hinv : starRingEnd ℂ w = w⁻¹ := eq_inv_of_mul_eq_one_right hw1
  have h1w : 1 + w ^ 2 = w * (starRingEnd ℂ w + w) := by linear_combination (-1 : ℂ) * hw1
  rw [h1w, hc, hinv]
  push_cast
  field_simp

lemma re_cauchyPsi_right (H : ℂ → ℂ) (h1 : ℝ) (τ : ℝ) :
    (cauchyPsi H h1 (1 + (τ : ℂ) * Complex.I)).re =
      π / 4 * (2 * ((1 - Real.tanh (π * τ / 4) ^ 2) / (1 + Real.tanh (π * τ / 4) ^ 2))) *
        ((starRingEnd ℂ (wPt (Real.tanh (π * τ / 4))) * H (wPt (Real.tanh (π * τ / 4)))).re
          - (1 - Real.tanh (π * τ / 4) ^ 2) / (1 + Real.tanh (π * τ / 4) ^ 2) - h1) := by
  rw [cauchyPsi_right, Complex.re_ofReal_mul]
  congr 1
  set y := Real.tanh (π * τ / 4) with hy
  set w := wPt y with hw
  have hw1 : w * starRingEnd ℂ w = 1 := wPt_mul_conj y
  have e : starRingEnd ℂ w * (H w - 1 - h1 * w) = starRingEnd ℂ w * H w - starRingEnd ℂ w - h1 := by
    linear_combination (-(h1 : ℂ)) * hw1
  rw [e]
  have hre : (starRingEnd ℂ w).re = (1 - y ^ 2) / (1 + y ^ 2) := by rw [Complex.conj_re, hw, re_wPt]
  simp only [Complex.sub_re, hre, Complex.ofReal_re]

/-- Real symmetry at the edge point: `Re(conj w · H w) = Re(w · H (conj w))`. -/
lemma re_conj_mul_eq {H : ℂ → ℂ} {h1 : ℝ} (hH : CauchyClass H h1) {τ : ℝ} (hτ : τ ≠ 0) :
    (starRingEnd ℂ (wPt (Real.tanh (π * τ / 4))) * H (wPt (Real.tanh (π * τ / 4)))).re =
      (wPt (Real.tanh (π * τ / 4)) * H (starRingEnd ℂ (wPt (Real.tanh (π * τ / 4))))).re := by
  set w := wPt (Real.tanh (π * τ / 4)) with hw
  have hmem : (1 + (τ : ℂ) * Complex.I) ∈ unitStripCl \ {0, 1} := edge_right_mem hτ
  have hz : sTan (starRingEnd ℂ (1 + (τ : ℂ) * Complex.I)) ∈ closure halfDisc \ {Complex.I, -Complex.I, 1} :=
    sTan_mem_cont (conj_mem_unitStripCl hmem)
  rw [sTan_conj, sTan_one_add_eq_wPt] at hz
  have h := hH.conj_boundary hz
  rw [Complex.conj_conj] at h
  rw [← hw] at hz h
  have : starRingEnd ℂ w * H w = starRingEnd ℂ (w * H (starRingEnd ℂ w)) := by
    rw [map_mul, h]
  rw [this, Complex.conj_re]

end

end FormalResearch.ModularBootstrap.FiveTerm
