module

public import FormalResearch.ModularBootstrap.Upper.Hankel.HankelOrderPAsym

/-!
# The Hankel-side fields of `FWSDHypotheses`, for `H_p¹` and `ε_p`

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, proof of Lemma `FW-SD` (`fw:SDp`), step (2):
for `b` in the edge strip (`Im b ≥ 1/4`) and `k` large, the factor `1 + ε_p(k b)` of the order-`p` amplitude
`A_p(b) = e^{-iπp/2} (b/x)^p A_0^∘(b) (1 + ε_p(k b))` is analytic, zero-free, bounded, and has
logarithmic derivatives of order one and two bounded by `1`.

`exists_hankelEpsOrd_fwsd_fields` states this for the functions `εp = hankelEpsOrd p` and the dilation `k`
in the form of the corresponding fields of `FWSDHypotheses` (`Upper/Saddle/FWSD.lean`):
`eps_nonzero`, `eps_logDeriv`, `eps_logDeriv2`, `eps_strip_bound` and the size
`‖ε_p(k b)‖ ≤ C_p/k` behind `eps_saddle_bound` (`k = sdvWave n x ≍ n x`); `hankel_p` is
`hankelOrd_expansion` and `eps_analytic` is `analyticOnNhd_one_add_hankelEpsOrd`.  The constants `C_p`,
`K_p` depend only on `p`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex Set Filter Topology Metric
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.Upper.Hankel

lemma isOpen_im_pos : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im

lemma analyticOnNhd_hankelEpsOrd (p : ℕ) : AnalyticOnNhd ℂ (hankelEpsOrd p) {z : ℂ | 0 < z.im} :=
  (differentiableOn_hankelEpsOrd p).analyticOnNhd isOpen_im_pos

/-- `b ↦ 1 + ε_p(k b)` is analytic on `Im b > 0` for `k > 0` (`FWSDHypotheses.eps_analytic`). -/
theorem analyticOnNhd_one_add_hankelEpsOrd (p : ℕ) {k : ℝ} (hk : 0 < k) :
    AnalyticOnNhd ℂ (fun b : ℂ => 1 + hankelEpsOrd p ((k : ℂ) * b)) {b : ℂ | 0 < b.im} := by
  intro b hb
  have hb' : (k : ℂ) * b ∈ {z : ℂ | 0 < z.im} := by
    show 0 < ((k : ℂ) * b).im
    rw [Complex.im_ofReal_mul]; exact mul_pos hk hb
  have := (analyticOnNhd_hankelEpsOrd p) _ hb'
  exact analyticAt_const.add (this.comp (analyticAt_const.mul analyticAt_id))

lemma im_ofReal_mul_pos {k : ℝ} (hk : 0 < k) {b : ℂ} (hb : 0 < b.im) : 0 < ((k : ℂ) * b).im := by
  rw [Complex.im_ofReal_mul]; exact mul_pos hk hb

lemma hasDerivAt_one_add_eps (p : ℕ) {k : ℝ} (hk : 0 < k) {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt (fun z : ℂ => 1 + hankelEpsOrd p ((k : ℂ) * z))
      ((k : ℂ) * deriv (hankelEpsOrd p) ((k : ℂ) * w)) w := by
  have hd : DifferentiableAt ℂ (hankelEpsOrd p) ((k : ℂ) * w) :=
    (analyticOnNhd_hankelEpsOrd p _ (im_ofReal_mul_pos hk hw)).differentiableAt
  have hlin : HasDerivAt (fun z : ℂ => (k : ℂ) * z) (k : ℂ) w := by
    simpa using (hasDerivAt_id w).const_mul (k : ℂ)
  have := (hd.hasDerivAt.scomp w hlin).const_add 1
  refine this.congr_deriv ?_
  simp only [smul_eq_mul]

lemma deriv_one_add_eps (p : ℕ) {k : ℝ} (hk : 0 < k) {w : ℂ} (hw : 0 < w.im) :
    deriv (fun z : ℂ => 1 + hankelEpsOrd p ((k : ℂ) * z)) w =
      (k : ℂ) * deriv (hankelEpsOrd p) ((k : ℂ) * w) :=
  (hasDerivAt_one_add_eps p hk hw).deriv

lemma hasDerivAt_deriv_one_add_eps (p : ℕ) {k : ℝ} (hk : 0 < k) {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt (deriv (fun z : ℂ => 1 + hankelEpsOrd p ((k : ℂ) * z)))
      ((k : ℂ) ^ 2 * deriv (deriv (hankelEpsOrd p)) ((k : ℂ) * w)) w := by
  have hd : DifferentiableAt ℂ (deriv (hankelEpsOrd p)) ((k : ℂ) * w) :=
    ((analyticOnNhd_hankelEpsOrd p).deriv _ (im_ofReal_mul_pos hk hw)).differentiableAt
  have hlin : HasDerivAt (fun z : ℂ => (k : ℂ) * z) (k : ℂ) w := by
    simpa using (hasDerivAt_id w).const_mul (k : ℂ)
  have h1 := (hd.hasDerivAt.scomp w hlin).const_mul (k : ℂ)
  have hev : deriv (fun z : ℂ => 1 + hankelEpsOrd p ((k : ℂ) * z)) =ᶠ[𝓝 w]
      fun z : ℂ => (k : ℂ) * deriv (hankelEpsOrd p) ((k : ℂ) * z) := by
    filter_upwards [isOpen_im_pos.mem_nhds hw] with z hz
    exact deriv_one_add_eps p hk hz
  refine (h1.congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [smul_eq_mul]; ring

/-- The Hankel-side fields of `FWSDHypotheses` for `ε_p`: constants `C, K₀` depending only on `p` such that
for every `k ≥ K₀` and every `b` with `Im b ≥ 1/4`:
`‖ε_p(k b)‖ ≤ C/k`, `‖1 + ε_p(k b)‖ ≤ 2`, `1 + ε_p(k b) ≠ 0`, and the first and second logarithmic
derivatives of `z ↦ 1 + ε_p(k z)` at `b` have norm `≤ 1`. -/
theorem exists_hankelEpsOrd_fwsd_fields (p : ℕ) :
    ∃ C K₀ : ℝ, 0 ≤ C ∧ 0 < K₀ ∧ ∀ k : ℝ, K₀ ≤ k → ∀ b : ℂ, 1 / 4 ≤ b.im →
      ‖hankelEpsOrd p ((k : ℂ) * b)‖ ≤ C / k ∧
      ‖1 + hankelEpsOrd p ((k : ℂ) * b)‖ ≤ 2 ∧
      1 + hankelEpsOrd p ((k : ℂ) * b) ≠ 0 ∧
      ‖deriv (fun z : ℂ => 1 + hankelEpsOrd p ((k : ℂ) * z)) b /
        (1 + hankelEpsOrd p ((k : ℂ) * b))‖ ≤ 1 ∧
      ‖deriv (fun w : ℂ => deriv (fun z : ℂ => 1 + hankelEpsOrd p ((k : ℂ) * z)) w /
        (1 + hankelEpsOrd p ((k : ℂ) * w))) b‖ ≤ 1 := by
  obtain ⟨C₁, hC₁, hb⟩ := exists_hankelEpsOrd_bounds p
  refine ⟨4 * C₁, 8 + 200 * C₁, by positivity, by positivity, fun k hk b hb4 => ?_⟩
  have hk0 : 0 < k := by linarith [hC₁]
  have hkb : 4 ≤ k := by linarith
  have hbim : 0 < b.im := by linarith
  set z : ℂ := (k : ℂ) * b with hz
  have hzim : k / 4 ≤ z.im := by
    rw [hz, Complex.im_ofReal_mul]; nlinarith
  have hznorm : k / 4 ≤ ‖z‖ := hzim.trans (Complex.im_le_norm z)
  have hz2 : 2 ≤ ‖z‖ := by linarith
  have hzpos : 0 < z.im := by linarith
  obtain ⟨h0, h1, h2⟩ := hb z hzpos
  have e0 := h0 (by linarith)
  have e1 := h1 (by linarith)
  have e2 := h2 hz2
  have hk4 : (0 : ℝ) < k / 4 := by positivity
  -- bounds in terms of `k`
  have b0 : ‖hankelEpsOrd p z‖ ≤ 4 * C₁ / k := by
    refine e0.trans ?_
    rw [div_le_div_iff₀ (by linarith) hk0]; nlinarith
  have b0' : ‖hankelEpsOrd p z‖ ≤ 1 / 2 := by
    refine b0.trans ?_
    rw [div_le_iff₀ hk0]; nlinarith
  have b1 : ‖deriv (hankelEpsOrd p) z‖ ≤ 16 * C₁ / k ^ 2 := by
    refine e1.trans ?_
    have : (k / 4) * (k / 4) ≤ ‖z‖ * z.im := mul_le_mul hznorm hzim hk4.le (by linarith)
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith
  have b2 : ‖deriv (deriv (hankelEpsOrd p)) z‖ ≤ 64 * C₁ / k ^ 3 := by
    refine e2.trans ?_
    have h3 : (k / 4) * (k / 4) ^ 2 ≤ ‖z‖ * z.im ^ 2 :=
      mul_le_mul hznorm (pow_le_pow_left₀ hk4.le hzim 2) (by positivity) (by linarith)
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith
  have hg : ‖1 + hankelEpsOrd p z‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one]; linarith
  have hg1 : 1 / 2 ≤ ‖1 + hankelEpsOrd p z‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-(hankelEpsOrd p z))
    rw [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  have hgne : 1 + hankelEpsOrd p z ≠ 0 := by
    intro h; rw [h, norm_zero] at hg1; linarith
  have hgpos : 0 < ‖1 + hankelEpsOrd p z‖ := by linarith
  -- the derivatives of `g(w) = 1 + ε(k w)`
  have hd1 : ‖deriv (fun w : ℂ => 1 + hankelEpsOrd p ((k : ℂ) * w)) b‖ ≤ 16 * C₁ / k := by
    rw [deriv_one_add_eps p hk0 hbim, norm_mul, Complex.norm_real, Real.norm_of_nonneg hk0.le]
    calc k * ‖deriv (hankelEpsOrd p) z‖ ≤ k * (16 * C₁ / k ^ 2) := by gcongr
      _ = 16 * C₁ / k := by field_simp
  have hd2 : ‖(k : ℂ) ^ 2 * deriv (deriv (hankelEpsOrd p)) z‖ ≤ 64 * C₁ / k := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hk0.le]
    calc k ^ 2 * ‖deriv (deriv (hankelEpsOrd p)) z‖ ≤ k ^ 2 * (64 * C₁ / k ^ 3) := by gcongr
      _ = 64 * C₁ / k := by field_simp
  have hkC : 200 * C₁ ≤ k := by linarith
  have hqlog : 16 * C₁ / k / (1 / 2) ≤ 1 / 5 := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1 / 2), div_le_iff₀ hk0]; nlinarith
  have hlog1 : ‖deriv (fun w : ℂ => 1 + hankelEpsOrd p ((k : ℂ) * w)) b /
      (1 + hankelEpsOrd p z)‖ ≤ 1 / 5 := by
    rw [norm_div]
    calc _ ≤ (16 * C₁ / k) / (1 / 2) := by
          gcongr
      _ ≤ 1 / 5 := hqlog
  refine ⟨b0, hg, hgne, hlog1.trans (by norm_num), ?_⟩
  -- second logarithmic derivative
  have hgd : HasDerivAt (fun w : ℂ => 1 + hankelEpsOrd p ((k : ℂ) * w))
      (deriv (fun w : ℂ => 1 + hankelEpsOrd p ((k : ℂ) * w)) b) b :=
    (hasDerivAt_one_add_eps p hk0 hbim).congr_deriv (deriv_one_add_eps p hk0 hbim).symm
  have hgdd := hasDerivAt_deriv_one_add_eps p hk0 hbim
  have hq0 := hgdd.div hgd hgne
  have hq : HasDerivAt (fun w : ℂ => deriv (fun z : ℂ => 1 + hankelEpsOrd p ((k : ℂ) * z)) w /
      (1 + hankelEpsOrd p ((k : ℂ) * w))) _ b := hq0
  rw [hq.deriv]
  set g' := deriv (fun w : ℂ => 1 + hankelEpsOrd p ((k : ℂ) * w)) b with hg'
  set G := 1 + hankelEpsOrd p z with hG
  have e : ((k : ℂ) ^ 2 * deriv (deriv (hankelEpsOrd p)) z * G - g' * g') / G ^ 2 =
      ((k : ℂ) ^ 2 * deriv (deriv (hankelEpsOrd p)) z) / G - (g' / G) ^ 2 := by
    field_simp
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have n1 : ‖((k : ℂ) ^ 2 * deriv (deriv (hankelEpsOrd p)) z) / G‖ ≤ 64 * C₁ / k / (1 / 2) := by
    rw [norm_div]
    gcongr
  have n2 : ‖(g' / G) ^ 2‖ ≤ (1 / 5) ^ 2 := by
    rw [norm_pow]; gcongr
  have hq2 : 64 * C₁ / k / (1 / 2) ≤ 4 / 5 := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1 / 2), div_le_iff₀ hk0]; nlinarith
  linarith [n1, n2]

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.exists_hankelEpsOrd_fwsd_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_hankelEpsOrd_fwsd_fields

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.analyticOnNhd_one_add_hankelEpsOrd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms analyticOnNhd_one_add_hankelEpsOrd

end FormalResearch.ModularBootstrap.Upper.Hankel
