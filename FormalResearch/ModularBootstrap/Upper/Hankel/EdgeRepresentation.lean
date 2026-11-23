module

public import FormalResearch.ModularBootstrap.Upper.Hankel.HankelBoundary
public import FormalResearch.ModularBootstrap.Upper.Hankel.ContourShift

/-!
# Lemma `SD_H`: upper-edge Hankel representation (order `0`)

Source: `CFT/modular_bootstrap/paper/edge_transform_sd.tex`, Lemma `SD_H` (`esd:hankel`, lines 15--58).

For `h` even, continuous on `0 ≤ Im b ≤ 1/2`, holomorphic in `0 < Im b < 1/2`, with
`‖h(v + iy)‖ ≤ C e^{-a|v|}` on `0 ≤ y ≤ 1/2`, put
`ĥ(t) = 2π ∫₀^∞ h(√(3s/c')) J₀(4π√(s t)) ds` (`edgeHankel`).  Then for `k = 4π c' x/3 > 0`,
`t = c' x²/3`:

`ĥ(t) = (2π c'/3) ∫_{E₊} h(b) H₀¹(k b) b db`   (`edge_hankel_representation`, (SD.H)).

Route: shift `E₊ = ℝ + i/2` down to `ℝ + iη` (`integral_horizontal_shift`), let `η → 0⁺` by dominated
convergence (the integrand is bounded by `C' e^{-(a/2)|v|}` uniformly in `η`, thanks to the uniform
bound `‖H₀¹(z)‖ ≤ √(2/π) ‖z‖^{-1/2}`), identify the boundary values by the rotated form
`hankelRay` and the reflection `H₀¹(-z̄) = -conj H₀¹(z)`, and use `hankelRay x + conj hankelRay x =
2 J₀(x)`.  No logarithmic semicircle estimate is needed: `‖b H₀¹(k b)‖ ≲ ‖b‖^{1/2}` is bounded near `0`.

The hypotheses differ from the TeX as follows: holomorphy is used only on `0 < Im b < 1/2` (not up to
`1/2 + δ`), "real on `ℝ`" and "bounded near `0`" are not needed (the latter follows from the decay
bound), and continuity of `h` up to the real axis is made explicit: it is necessary, since `ĥ` involves
`h` on `ℝ` only while `h` is otherwise a holomorphic function of the open strip.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Hankel

/-- Hypotheses of Lemma `SD_H` on `h` (decay rate `a`, constant `C`). -/
structure EdgeHankelHyp (h : ℂ → ℂ) (a C : ℝ) : Prop where
  /-- `h` is even on the real axis. -/
  even : ∀ r : ℝ, h (-(r : ℂ)) = h (r : ℂ)
  /-- `h` is holomorphic in the open strip `0 < Im b < 1/2`. -/
  holo : DifferentiableOn ℂ h {b : ℂ | 0 < b.im ∧ b.im < 1 / 2}
  /-- `h` is continuous up to the real axis and up to `E₊ = ℝ + i/2`. -/
  cont : ContinuousOn h {b : ℂ | 0 ≤ b.im ∧ b.im ≤ 1 / 2}
  /-- Exponential decay on the closed substrip. -/
  decay : ∀ b : ℂ, 0 ≤ b.im → b.im ≤ 1 / 2 → ‖h b‖ ≤ C * Real.exp (-a * |b.re|)

/-- The Hankel transform in the physical variable `s = c' b²/3`:
`ĥ(t) = 2π ∫₀^∞ h(√(3s/c')) J₀(4π√(s t)) ds`, with `J₀ = Complex.besselJ 0`. -/
noncomputable def edgeHankel (c' : ℝ) (h : ℂ → ℂ) (t : ℝ) : ℂ :=
  2 * (π : ℂ) * ∫ s in Ioi (0 : ℝ),
    h ((√(3 * s / c') : ℝ) : ℂ) * Complex.besselJ 0 ((4 * π * √(s * t) : ℝ) : ℂ)

/-- The integrand `h(b) H₀¹(k b) b` of (SD.H). -/
noncomputable def edgeIntegrand (h : ℂ → ℂ) (k : ℝ) (b : ℂ) : ℂ :=
  h b * hankel0 ((k : ℂ) * b) * b

/-! ### The uniform majorant -/

/-- The integrable majorant of `‖edgeIntegrand h k b‖` on the strip. -/
noncomputable def edgeMajorant (a C k : ℝ) (v : ℝ) : ℝ :=
  C * √(2 / π) * k ^ (-(1 / 2 : ℝ)) * (1 + 2 / a) * Real.exp (-(a / 2) * |v|)

lemma rpow_half_le {y : ℝ} (hy : 0 ≤ y) : y ^ (1 / 2 : ℝ) ≤ (1 + y) / 2 := by
  rw [← Real.sqrt_eq_rpow]
  nlinarith [Real.sq_sqrt hy, sq_nonneg (√y - 1), Real.sqrt_nonneg y]

lemma one_add_mul_exp_le {a : ℝ} (ha : 0 < a) (u : ℝ) (hu : 0 ≤ u) :
    Real.exp (-a * u) * (1 + u) ≤ (1 + 2 / a) * Real.exp (-(a / 2) * u) := by
  have h1 : (a / 2) * u ≤ Real.exp ((a / 2) * u) := by
    linarith [Real.add_one_le_exp ((a / 2) * u)]
  have hu' : u ≤ (2 / a) * Real.exp ((a / 2) * u) := by
    have : (a / 2) * u ≤ (a / 2) * ((2 / a) * Real.exp ((a / 2) * u)) := by
      calc (a / 2) * u ≤ Real.exp ((a / 2) * u) := h1
        _ = (a / 2) * ((2 / a) * Real.exp ((a / 2) * u)) := by field_simp
    exact le_of_mul_le_mul_left this (by positivity)
  have e1 : Real.exp (-a * u) ≤ Real.exp (-(a / 2) * u) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have e2 : Real.exp (-a * u) * u ≤ (2 / a) * Real.exp (-(a / 2) * u) := by
    calc Real.exp (-a * u) * u ≤ Real.exp (-a * u) * ((2 / a) * Real.exp ((a / 2) * u)) :=
          mul_le_mul_of_nonneg_left hu' (Real.exp_pos _).le
      _ = (2 / a) * (Real.exp (-a * u) * Real.exp ((a / 2) * u)) := by ring
      _ = (2 / a) * Real.exp (-(a / 2) * u) := by
          rw [← Real.exp_add]; congr 2; ring
  nlinarith

/-- Pointwise bound of the integrand on the strip `0 < Im b ≤ 1/2`. -/
theorem norm_edgeIntegrand_le {h : ℂ → ℂ} {a C : ℝ} (ha : 0 < a) (hh : EdgeHankelHyp h a C)
    {k : ℝ} (hk : 0 < k) {b : ℂ} (hb0 : 0 < b.im) (hb1 : b.im ≤ 1 / 2) :
    ‖edgeIntegrand h k b‖ ≤ edgeMajorant a C k b.re := by
  have hdec := hh.decay b hb0.le hb1
  have hC : 0 ≤ C := by
    have := hh.decay b hb0.le hb1
    have h0 : 0 ≤ ‖h b‖ := norm_nonneg _
    have : 0 < Real.exp (-a * |b.re|) := Real.exp_pos _
    nlinarith
  have hb : b ≠ 0 := by intro h; rw [h] at hb0; simp at hb0
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hkb : (k : ℂ) * b ∈ {z : ℂ | 0 < z.im} := by
    show 0 < ((k : ℂ) * b).im
    rw [Complex.im_ofReal_mul]; positivity
  have hH := norm_hankel0_le (z := (k : ℂ) * b) hkb
  have hn : ‖(k : ℂ) * b‖ = k * ‖b‖ := by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hk.le]
  have hexp : Real.exp (-((k : ℂ) * b).im) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 < ((k : ℂ) * b).im := hkb
    linarith
  rw [hn] at hH
  unfold edgeIntegrand
  rw [norm_mul, norm_mul]
  have hnb : ‖b‖ ≤ |b.re| + 1 / 2 := by
    have := Complex.norm_le_abs_re_add_abs_im b
    rw [abs_of_pos hb0] at this
    linarith
  have hsq : ‖b‖ ^ (1 / 2 : ℝ) ≤ 1 + |b.re| := by
    refine (Real.rpow_le_rpow hbn.le hnb (by norm_num)).trans ?_
    have := rpow_half_le (y := |b.re| + 1 / 2) (by positivity)
    linarith [abs_nonneg b.re]
  have hkb' : (k * ‖b‖) ^ (-(1 / 2 : ℝ)) * ‖b‖ = k ^ (-(1 / 2 : ℝ)) * ‖b‖ ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow hk.le hbn.le]
    have : ‖b‖ ^ (1 / 2 : ℝ) = ‖b‖ ^ (-(1 / 2 : ℝ)) * ‖b‖ := by
      rw [← Real.rpow_add_one hbn.ne']; norm_num
    rw [this]; ring
  have hk12 : 0 < k ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hk _
  have hs2 : 0 ≤ √(2 / π) := Real.sqrt_nonneg _
  calc ‖h b‖ * ‖hankel0 ((k : ℂ) * b)‖ * ‖b‖
      ≤ (C * Real.exp (-a * |b.re|)) * (√(2 / π) * (k * ‖b‖) ^ (-(1 / 2 : ℝ)) * 1) * ‖b‖ := by
        gcongr
        exact hH.trans (by gcongr)
    _ = C * √(2 / π) * Real.exp (-a * |b.re|) * ((k * ‖b‖) ^ (-(1 / 2 : ℝ)) * ‖b‖) := by ring
    _ = C * √(2 / π) * k ^ (-(1 / 2 : ℝ)) * (Real.exp (-a * |b.re|) * ‖b‖ ^ (1 / 2 : ℝ)) := by
        rw [hkb']; ring
    _ ≤ C * √(2 / π) * k ^ (-(1 / 2 : ℝ)) * (Real.exp (-a * |b.re|) * (1 + |b.re|)) := by
        gcongr
    _ ≤ C * √(2 / π) * k ^ (-(1 / 2 : ℝ)) * ((1 + 2 / a) * Real.exp (-(a / 2) * |b.re|)) := by
        exact mul_le_mul_of_nonneg_left (one_add_mul_exp_le ha _ (abs_nonneg _)) (by positivity)
    _ = edgeMajorant a C k b.re := by unfold edgeMajorant; ring

lemma integrable_edgeMajorant (a C k : ℝ) (ha : 0 < a) : Integrable (edgeMajorant a C k) := by
  unfold edgeMajorant
  exact (integrable_exp_neg_abs (c := a / 2) (by positivity)).const_mul _

lemma tendsto_edgeMajorant (a C k : ℝ) (ha : 0 < a) :
    Tendsto (edgeMajorant a C k) (cocompact ℝ) (𝓝 0) := by
  unfold edgeMajorant
  simpa using (tendsto_exp_neg_abs (c := a / 2) (by positivity)).const_mul
    (C * √(2 / π) * k ^ (-(1 / 2 : ℝ)) * (1 + 2 / a))

/-! ### Continuity and holomorphy of the integrand -/

lemma continuousOn_edgeIntegrand {h : ℂ → ℂ} {a C : ℝ} (hh : EdgeHankelHyp h a C) {k : ℝ} (hk : 0 < k) :
    ContinuousOn (edgeIntegrand h k) {b : ℂ | 0 < b.im ∧ b.im ≤ 1 / 2} := by
  unfold edgeIntegrand
  have h1 : ContinuousOn h {b : ℂ | 0 < b.im ∧ b.im ≤ 1 / 2} :=
    hh.cont.mono fun b hb => ⟨hb.1.le, hb.2⟩
  have h2 : ContinuousOn (fun b : ℂ => hankel0 ((k : ℂ) * b)) {b : ℂ | 0 < b.im ∧ b.im ≤ 1 / 2} := by
    refine differentiableOn_hankel0.continuousOn.comp (by fun_prop) fun b hb => ?_
    show 0 < ((k : ℂ) * b).im
    rw [Complex.im_ofReal_mul]; exact mul_pos hk hb.1
  exact (h1.mul h2).mul continuousOn_id

lemma differentiableOn_edgeIntegrand {h : ℂ → ℂ} {a C : ℝ} (hh : EdgeHankelHyp h a C) {k : ℝ} (hk : 0 < k) :
    DifferentiableOn ℂ (edgeIntegrand h k) {b : ℂ | 0 < b.im ∧ b.im < 1 / 2} := by
  unfold edgeIntegrand
  have h2 : DifferentiableOn ℂ (fun b : ℂ => hankel0 ((k : ℂ) * b)) {b : ℂ | 0 < b.im ∧ b.im < 1 / 2} := by
    refine differentiableOn_hankel0.comp (by fun_prop) fun b hb => ?_
    show 0 < ((k : ℂ) * b).im
    rw [Complex.im_ofReal_mul]; exact mul_pos hk hb.1
  exact (hh.holo.mul h2).mul differentiableOn_id

/-! ### Shifting `E₊` down to `ℝ + iη` -/

theorem integral_edge_eq_line {h : ℂ → ℂ} {a C : ℝ} (ha : 0 < a) (hh : EdgeHankelHyp h a C)
    {k : ℝ} (hk : 0 < k) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2) :
    ∫ v : ℝ, edgeIntegrand h k ((v : ℂ) + ((1 / 2 : ℝ) : ℂ) * I) =
      ∫ v : ℝ, edgeIntegrand h k ((v : ℂ) + (η : ℂ) * I) := by
  symm
  refine integral_horizontal_shift (F := edgeIntegrand h k) hη1 ?_ ?_
    (integrable_edgeMajorant a C k ha) (tendsto_edgeMajorant a C k ha) ?_
  · exact (continuousOn_edgeIntegrand hh hk).mono fun b hb => ⟨hη0.trans_le hb.1, hb.2⟩
  · exact (differentiableOn_edgeIntegrand hh hk).mono fun b hb => ⟨hη0.trans hb.1, hb.2⟩
  · intro b hb1 hb2
    exact norm_edgeIntegrand_le ha hh hk (hη0.trans_le hb1) hb2

/-! ### The boundary function and the limit `η → 0⁺` -/

lemma tendsto_hankel0_ray' {ι : Type*} {l : Filter ι} {z : ι → ℂ} {x : ℝ} (hx : 0 < x)
    (hz : Tendsto z l (𝓝 (x : ℂ))) (him : ∀ᶠ i in l, 0 < (z i).im) :
    Tendsto (fun i => hankel0 (z i)) l (𝓝 (hankelRay (x : ℂ))) := by
  have h1 : Tendsto (fun i => hankelRay (z i)) l (𝓝 (hankelRay (x : ℂ))) :=
    (continuousAt_hankelRay (by simpa using hx)).tendsto.comp hz
  have hre : ∀ᶠ i in l, 0 < (z i).re := by
    have := (Complex.continuous_re.tendsto _).comp hz
    simp only [Function.comp_def, Complex.ofReal_re] at this
    exact Filter.Tendsto.eventually_const_lt (by simpa using hx) this
  refine h1.congr' ?_
  filter_upwards [hre, him] with i h1 h2
  exact (hankel0_eq_ray h1 h2).symm

/-- The boundary values `h(v) · H₀¹(k v + i0) · v`, with `H₀¹(-r + i0) = -conj H₀¹(r + i0)`. -/
noncomputable def edgeBoundary (h : ℂ → ℂ) (k : ℝ) (v : ℝ) : ℂ :=
  h (v : ℂ) * (if 0 < v then hankelRay ((k * v : ℝ) : ℂ)
    else -(starRingEnd ℂ) (hankelRay ((k * (-v) : ℝ) : ℂ))) * (v : ℂ)

lemma eventually_mem_nhdsGT_half : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), 0 < η ∧ η < 1 / 2 := by
  have := Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [this] with η hη using hη

lemma tendsto_edgeIntegrand_line {h : ℂ → ℂ} {a C : ℝ} (hh : EdgeHankelHyp h a C) {k : ℝ} (hk : 0 < k)
    {v : ℝ} (hv : v ≠ 0) :
    Tendsto (fun η : ℝ => edgeIntegrand h k ((v : ℂ) + (η : ℂ) * I)) (𝓝[>] (0 : ℝ))
      (𝓝 (edgeBoundary h k v)) := by
  have hpath := tendsto_vertical_path (v : ℂ)
  have hh1 : Tendsto (fun η : ℝ => h ((v : ℂ) + (η : ℂ) * I)) (𝓝[>] (0 : ℝ)) (𝓝 (h (v : ℂ))) := by
    have hmem : (v : ℂ) ∈ {b : ℂ | 0 ≤ b.im ∧ b.im ≤ 1 / 2} := by
      show 0 ≤ (v : ℂ).im ∧ (v : ℂ).im ≤ 1 / 2
      simp
    refine ((hh.cont (v : ℂ) hmem).tendsto).comp ?_
    refine tendsto_nhdsWithin_iff.mpr ⟨hpath, ?_⟩
    filter_upwards [eventually_mem_nhdsGT_half] with η hη
    show 0 ≤ ((v : ℂ) + (η : ℂ) * I).im ∧ ((v : ℂ) + (η : ℂ) * I).im ≤ 1 / 2
    rw [im_line]; exact ⟨hη.1.le, hη.2.le⟩
  have hz : Tendsto (fun η : ℝ => (k : ℂ) * ((v : ℂ) + (η : ℂ) * I)) (𝓝[>] (0 : ℝ))
      (𝓝 (((k * v : ℝ)) : ℂ)) := by
    have := hpath.const_mul (k : ℂ)
    simpa using this
  have hzim : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), 0 < ((k : ℂ) * ((v : ℂ) + (η : ℂ) * I)).im := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    rw [Complex.im_ofReal_mul, im_line]
    exact mul_pos hk hη
  by_cases hvp : 0 < v
  · have hH := tendsto_hankel0_ray' (mul_pos hk hvp) hz hzim
    have := (hh1.mul hH).mul hpath
    unfold edgeBoundary edgeIntegrand
    simp only [hvp, ↓reduceIte]
    exact this
  · have hvn : v < 0 := lt_of_le_of_ne (not_lt.mp hvp) hv
    -- reflection: `H(k(v + iη)) = -conj H(k(-v + iη))`
    have hz' : Tendsto (fun η : ℝ => (k : ℂ) * ((((-v : ℝ)) : ℂ) + (η : ℂ) * I)) (𝓝[>] (0 : ℝ))
        (𝓝 (((k * (-v) : ℝ)) : ℂ)) := by
      have := (tendsto_vertical_path (((-v : ℝ)) : ℂ)).const_mul (k : ℂ)
      simpa using this
    have hzim' : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), 0 < ((k : ℂ) * ((((-v : ℝ)) : ℂ) + (η : ℂ) * I)).im := by
      filter_upwards [self_mem_nhdsWithin] with η hη
      rw [Complex.im_ofReal_mul, im_line]
      exact mul_pos hk hη
    have hH := tendsto_hankel0_ray' (mul_pos hk (neg_pos.mpr hvn)) hz' hzim'
    have hH2 : Tendsto (fun η : ℝ => hankel0 ((k : ℂ) * ((v : ℂ) + (η : ℂ) * I))) (𝓝[>] (0 : ℝ))
        (𝓝 (-(starRingEnd ℂ) (hankelRay ((k * (-v) : ℝ) : ℂ)))) := by
      refine (((Complex.continuous_conj.tendsto _).comp hH).neg).congr fun η => ?_
      simp only [Function.comp_apply]
      rw [← hankel0_reflection]
      congr 1
      simp only [map_mul, map_add, map_neg, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
      ring
    have := (hh1.mul hH2).mul hpath
    unfold edgeBoundary edgeIntegrand
    simp only [hvp, ↓reduceIte]
    exact this

lemma exists_seq_nhdsGT : ∃ η : ℕ → ℝ, (∀ n, 0 < η n ∧ η n < 1 / 2) ∧ Tendsto η atTop (𝓝[>] (0 : ℝ)) := by
  refine ⟨fun n => 1 / (((n + 2 : ℕ) : ℝ) + 1), fun n => ⟨by positivity, ?_⟩, ?_⟩
  · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    push_cast
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
    · exact (tendsto_one_div_add_atTop_nhds_zero_nat).comp (tendsto_add_atTop_nat 2)
    · show (0 : ℝ) < 1 / (((n + 2 : ℕ) : ℝ) + 1)
      positivity

theorem tendsto_line_integral {h : ℂ → ℂ} {a C : ℝ} (ha : 0 < a) (hh : EdgeHankelHyp h a C)
    {k : ℝ} (hk : 0 < k) :
    Tendsto (fun η : ℝ => ∫ v : ℝ, edgeIntegrand h k ((v : ℂ) + (η : ℂ) * I)) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ v : ℝ, edgeBoundary h k v)) := by
  refine tendsto_integral_filter_of_dominated_convergence (edgeMajorant a C k) ?_ ?_
    (integrable_edgeMajorant a C k ha) ?_
  · filter_upwards [eventually_mem_nhdsGT_half] with η hη
    have hcont : Continuous fun v : ℝ => edgeIntegrand h k ((v : ℂ) + (η : ℂ) * I) := by
      refine (continuousOn_edgeIntegrand hh hk).comp_continuous (by fun_prop) fun v => ?_
      show 0 < _ ∧ _ ≤ 1 / 2
      rw [im_line]; exact ⟨hη.1, hη.2.le⟩
    exact hcont.aestronglyMeasurable
  · filter_upwards [eventually_mem_nhdsGT_half] with η hη
    refine Filter.Eventually.of_forall fun v => ?_
    have := norm_edgeIntegrand_le ha hh hk (b := (v : ℂ) + (η : ℂ) * I) (by rw [im_line]; exact hη.1)
      (by rw [im_line]; exact hη.2.le)
    rwa [re_line] at this
  · filter_upwards [(Set.countable_singleton (0 : ℝ)).ae_notMem volume] with v hv
    exact tendsto_edgeIntegrand_line hh hk (by simpa using hv)

theorem integral_edge_eq_boundary {h : ℂ → ℂ} {a C : ℝ} (ha : 0 < a) (hh : EdgeHankelHyp h a C)
    {k : ℝ} (hk : 0 < k) :
    ∫ v : ℝ, edgeIntegrand h k ((v : ℂ) + ((1 / 2 : ℝ) : ℂ) * I) = ∫ v : ℝ, edgeBoundary h k v := by
  have h1 := tendsto_line_integral ha hh hk
  have h2 : Tendsto (fun η : ℝ => ∫ v : ℝ, edgeIntegrand h k ((v : ℂ) + (η : ℂ) * I)) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ v : ℝ, edgeIntegrand h k ((v : ℂ) + ((1 / 2 : ℝ) : ℂ) * I))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_mem_nhdsGT_half] with η hη
    exact integral_edge_eq_line ha hh hk hη.1 hη.2.le
  exact tendsto_nhds_unique h2 h1

/-! ### The boundary function: bound, measurability, folding -/

lemma norm_edgeBoundary_le {h : ℂ → ℂ} {a C : ℝ} (ha : 0 < a) (hh : EdgeHankelHyp h a C)
    {k : ℝ} (hk : 0 < k) {v : ℝ} (hv : v ≠ 0) : ‖edgeBoundary h k v‖ ≤ edgeMajorant a C k v := by
  refine le_of_tendsto (tendsto_edgeIntegrand_line hh hk hv).norm ?_
  filter_upwards [eventually_mem_nhdsGT_half] with η hη
  have := norm_edgeIntegrand_le ha hh hk (b := (v : ℂ) + (η : ℂ) * I) (by rw [im_line]; exact hη.1)
    (by rw [im_line]; exact hη.2.le)
  rwa [re_line] at this

lemma aestronglyMeasurable_edgeBoundary {h : ℂ → ℂ} {a C : ℝ} (hh : EdgeHankelHyp h a C)
    {k : ℝ} (hk : 0 < k) : AEStronglyMeasurable (edgeBoundary h k) volume := by
  obtain ⟨η, hη, hlim⟩ := exists_seq_nhdsGT
  refine aestronglyMeasurable_of_tendsto_ae atTop (g := edgeBoundary h k) (f := fun (n : ℕ) (v : ℝ) => edgeIntegrand h k ((v : ℂ) + (η n : ℂ) * I))
    (fun n => ?_) ?_
  · have hcont : Continuous fun v : ℝ => edgeIntegrand h k ((v : ℂ) + (η n : ℂ) * I) := by
      refine (continuousOn_edgeIntegrand hh hk).comp_continuous (by fun_prop) fun v => ?_
      show 0 < _ ∧ _ ≤ 1 / 2
      rw [im_line]; exact ⟨(hη n).1, (hη n).2.le⟩
    exact hcont.aestronglyMeasurable
  · filter_upwards [(Set.countable_singleton (0 : ℝ)).ae_notMem volume] with v hv
    exact (tendsto_edgeIntegrand_line hh hk (by simpa using hv)).comp hlim

lemma integrable_edgeBoundary {h : ℂ → ℂ} {a C : ℝ} (ha : 0 < a) (hh : EdgeHankelHyp h a C)
    {k : ℝ} (hk : 0 < k) : Integrable (edgeBoundary h k) := by
  refine Integrable.mono' (integrable_edgeMajorant a C k ha) (aestronglyMeasurable_edgeBoundary hh hk) ?_
  filter_upwards [(Set.countable_singleton (0 : ℝ)).ae_notMem volume] with v hv
  exact norm_edgeBoundary_le ha hh hk (by simpa using hv)

lemma edgeBoundary_add_neg {h : ℂ → ℂ} {a C : ℝ} (hh : EdgeHankelHyp h a C) {k : ℝ} {x : ℝ} (hx : 0 < x) :
    edgeBoundary h k x + edgeBoundary h k (-x) =
      2 * (x : ℂ) * h (x : ℂ) * Complex.besselJ 0 ((k * x : ℝ) : ℂ) := by
  have hnx : ¬ (0 < -x) := not_lt.mpr (by linarith)
  unfold edgeBoundary
  simp only [hx, hnx, ↓reduceIte, neg_neg, Complex.ofReal_neg]
  rw [hh.even x]
  have := hankelRay_add_conj (k * x)
  linear_combination (x : ℂ) * h (x : ℂ) * this

theorem integral_edgeBoundary {h : ℂ → ℂ} {a C : ℝ} (ha : 0 < a) (hh : EdgeHankelHyp h a C)
    {k : ℝ} (hk : 0 < k) :
    ∫ v : ℝ, edgeBoundary h k v =
      2 * ∫ x in Ioi (0 : ℝ), (x : ℂ) * h (x : ℂ) * Complex.besselJ 0 ((k * x : ℝ) : ℂ) := by
  have hi := integrable_edgeBoundary ha hh hk
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hi.integrableOn hi.integrableOn]
  have hneg : ∫ v in Iic (0 : ℝ), edgeBoundary h k v = ∫ x in Ioi (0 : ℝ), edgeBoundary h k (-x) := by
    rw [integral_comp_neg_Ioi]; simp
  rw [hneg, ← integral_add (hi.comp_neg.integrableOn) hi.integrableOn]
  have : ∀ x ∈ Ioi (0 : ℝ), edgeBoundary h k (-x) + edgeBoundary h k x =
      2 * ((x : ℂ) * h (x : ℂ) * Complex.besselJ 0 ((k * x : ℝ) : ℂ)) := by
    intro x hx
    rw [add_comm, edgeBoundary_add_neg hh (mem_Ioi.mp hx)]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi this, integral_const_mul]

/-! ### The left-hand side: substitution `s = c' r²/3` -/

lemma edgeHankel_eq (h : ℂ → ℂ) {c' x : ℝ} (hc : 0 < c') (hx : 0 < x) :
    edgeHankel c' h (c' * x ^ 2 / 3) =
      (4 * π * c' / 3 : ℂ) * ∫ r in Ioi (0 : ℝ), (r : ℂ) * h (r : ℂ) *
        Complex.besselJ 0 (((4 * π * c' * x / 3) * r : ℝ) : ℂ) := by
  have hderiv : ∀ r ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun r : ℝ => c' * r ^ 2 / 3) (2 * c' * r / 3) (Ioi 0) r := by
    intro r _
    have := ((hasDerivAt_pow 2 r).const_mul c').div_const 3
    simpa [mul_assoc, mul_comm, mul_left_comm] using this.hasDerivWithinAt
  have hinj : InjOn (fun r : ℝ => c' * r ^ 2 / 3) (Ioi 0) := by
    intro r hr s hs hrs
    have hr0 : 0 < r := hr
    have hs0 : 0 < s := hs
    have h1 : r ^ 2 = s ^ 2 := by
      have : c' * r ^ 2 = c' * s ^ 2 := by linarith
      exact mul_left_cancel₀ hc.ne' this
    nlinarith [sq_nonneg (r - s), sq_nonneg (r + s)]
  have himg : (fun r : ℝ => c' * r ^ 2 / 3) '' Ioi 0 = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨r, hr, rfl⟩
      have : 0 < r := hr
      exact div_pos (mul_pos hc (pow_pos this 2)) (by norm_num)
    · intro hy
      have hy' : 0 < y := hy
      refine ⟨√(3 * y / c'), Real.sqrt_pos.mpr (by positivity), ?_⟩
      show c' * (√(3 * y / c')) ^ 2 / 3 = y
      rw [Real.sq_sqrt (by positivity)]
      field_simp
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun s : ℝ => h ((√(3 * s / c') : ℝ) : ℂ) *
      Complex.besselJ 0 ((4 * π * √(s * (c' * x ^ 2 / 3)) : ℝ) : ℂ))
  rw [himg] at key
  unfold edgeHankel
  rw [key]
  have : ∀ r ∈ Ioi (0 : ℝ), |2 * c' * r / 3| • (h ((√(3 * (c' * r ^ 2 / 3) / c') : ℝ) : ℂ) *
      Complex.besselJ 0 ((4 * π * √(c' * r ^ 2 / 3 * (c' * x ^ 2 / 3)) : ℝ) : ℂ)) =
      (2 * c' / 3 : ℂ) * ((r : ℂ) * h (r : ℂ) *
        Complex.besselJ 0 (((4 * π * c' * x / 3) * r : ℝ) : ℂ)) := by
    intro r hr
    have hr0 : 0 < r := hr
    have e1 : √(3 * (c' * r ^ 2 / 3) / c') = r := by
      rw [show 3 * (c' * r ^ 2 / 3) / c' = r ^ 2 by field_simp]
      exact Real.sqrt_sq hr0.le
    have e2 : √(c' * r ^ 2 / 3 * (c' * x ^ 2 / 3)) = c' * r * x / 3 := by
      rw [show c' * r ^ 2 / 3 * (c' * x ^ 2 / 3) = (c' * r * x / 3) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    rw [e1, e2, abs_of_pos (by positivity : 0 < 2 * c' * r / 3), Complex.real_smul]
    have e3 : (4 * π * (c' * r * x / 3) : ℝ) = (4 * π * c' * x / 3) * r := by ring
    rw [e3]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi this, integral_const_mul]
  ring

/-! ### Lemma `SD_H` -/

/-- **Lemma `SD_H`** (`esd:hankel`, (SD.H)): the upper-edge Hankel representation, order `0`.
For `k = 4π c' x/3 > 0`, `t = c' x²/3`:
`ĥ(t) = (2π c'/3) ∫_{E₊} h(b) H₀¹(k b) b db`, `E₊ = ℝ + i/2`. -/
theorem edge_hankel_representation {h : ℂ → ℂ} {a C : ℝ} (ha : 0 < a) (hh : EdgeHankelHyp h a C)
    {c' x : ℝ} (hc : 0 < c') (hx : 0 < x) :
    edgeHankel c' h (c' * x ^ 2 / 3) =
      (2 * π * c' / 3 : ℂ) * ∫ v : ℝ, h ((v : ℂ) + I / 2) *
        hankel0 (((4 * π * c' * x / 3 : ℝ) : ℂ) * ((v : ℂ) + I / 2)) * ((v : ℂ) + I / 2) := by
  have hk : 0 < 4 * π * c' * x / 3 := by positivity
  have h1 : ∀ v : ℝ, h ((v : ℂ) + I / 2) *
        hankel0 (((4 * π * c' * x / 3 : ℝ) : ℂ) * ((v : ℂ) + I / 2)) * ((v : ℂ) + I / 2) =
      edgeIntegrand h (4 * π * c' * x / 3) ((v : ℂ) + ((1 / 2 : ℝ) : ℂ) * I) := by
    intro v
    unfold edgeIntegrand
    have : ((v : ℂ) + ((1 / 2 : ℝ) : ℂ) * I) = (v : ℂ) + I / 2 := by push_cast; ring
    rw [this]
  simp only [h1]
  rw [integral_edge_eq_boundary ha hh hk, integral_edgeBoundary ha hh hk, edgeHankel_eq h hc hx]
  ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.edge_hankel_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edge_hankel_representation

end FormalResearch.ModularBootstrap.Upper.Hankel
