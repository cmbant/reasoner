module

public import FormalResearch.SignUncertainty.CtSdEval0

/-!
# Integration by parts along a chain (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3 ("integrating by parts once via
`(s²+â)e^{ic(âs+s³/3)} = (ic)^{-1}∂_s e^{…}`").  **Proved.**  In the `w`-plane (`s = c^{-1/3}w`) the identity is
`d/dw e^{iPh_U} = i(κU + w²) e^{iPh_U}`; for `G` holomorphic on `B(0,R₀)` the primitive `Ψ = w^{1/2} G e^{iPh_U}` of
`(w^{1/2}G)' e^{iPh_U} + i w^{1/2} G (κU + w²) e^{iPh_U}` vanishes at `0`, so along any chain
`∫ (w^{1/2}G)' e^{iPh} + i ∫ w^{1/2} G (κU+w²) e^{iPh} = Ψ(p)`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real

namespace FormalResearch.SignUncertainty.CtSd

lemma norm_csr_rpow (z : ℂ) : ‖csr z‖ = ‖z‖ ^ (1 / 2 : ℝ) := by
  rw [norm_csr, Real.sqrt_eq_rpow]

lemma norm_csr_div {z : ℂ} (hz : z ≠ 0) : ‖csr z / (2 * z)‖ = (1 / 2) * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
  have hx : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [norm_div, norm_mul, norm_csr_rpow, Real.rpow_neg hx.le]
  have h2 : ‖z‖ ^ (1 / 2 : ℝ) * ‖z‖ ^ (1 / 2 : ℝ) = ‖z‖ := by
    rw [← Real.rpow_add hx]; norm_num
  have hs : 0 < ‖z‖ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
  have : ‖(2 : ℂ)‖ = 2 := by simp
  rw [this]
  field_simp
  nlinarith [h2]

lemma PieceBd.of_pointwise {R₀ : ℝ} {q : Piece} (hq : q.Ok R₀) {h : ℂ → ℂ} {K1 α1 K2 α2 K3 α3 : ℝ}
    (hc : ∀ z ∈ ball (0 : ℂ) R₀, 0 ≤ z.re → z ≠ 0 → ContinuousAt h z)
    (hb : ∀ z ∈ ball (0 : ℂ) R₀, 0 ≤ z.re → z ≠ 0 →
      ‖h z‖ ≤ K1 * ‖z‖ ^ α1 + K2 * ‖z‖ ^ α2 + K3 * ‖z‖ ^ α3) : PieceBd h q K1 α1 K2 α2 K3 α3 := by
  have hcp : Continuous q.pt := by unfold Piece.pt; fun_prop
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have hm := hq.2.1 t ⟨ht.1.le, ht.2⟩
    exact ((hc (q.pt t) hm.1 hm.2 (hq.2.2 t ht)).comp (hcp.continuousAt (x := t))).continuousWithinAt
  · have hm := hq.2.1 t ⟨ht.1.le, ht.2⟩
    exact hb (q.pt t) hm.1 hm.2 (hq.2.2 t ht)

lemma Chain3.Bd.of_pointwise {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) {h : ℂ → ℂ} {K1 α1 K2 α2 K3 α3 : ℝ}
    (hc : ∀ z ∈ ball (0 : ℂ) R₀, 0 ≤ z.re → z ≠ 0 → ContinuousAt h z)
    (hb : ∀ z ∈ ball (0 : ℂ) R₀, 0 ≤ z.re → z ≠ 0 →
      ‖h z‖ ≤ K1 * ‖z‖ ^ α1 + K2 * ‖z‖ ^ α2 + K3 * ‖z‖ ^ α3) : ch.Bd h K1 α1 K2 α2 K3 α3 :=
  ⟨PieceBd.of_pointwise ch.ok1 hc hb, PieceBd.of_pointwise ch.ok2 hc hb, PieceBd.of_pointwise ch.ok3 hc hb⟩

lemma hasDerivAt_PhU (U : ℝ) (w : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.exp (Complex.I * PhU U w))
      (Complex.exp (Complex.I * PhU U w) * (Complex.I * ((kap : ℂ) * U + w ^ 2))) w := by
  have hP : HasDerivAt (fun w : ℂ => PhU U w) ((kap : ℂ) * U + w ^ 2) w := by
    have h1 : HasDerivAt (fun w : ℂ => (kap : ℂ) * U * w) ((kap : ℂ) * U) w := by
      simpa using (hasDerivAt_id w).const_mul ((kap : ℂ) * U)
    have h2 : HasDerivAt (fun w : ℂ => w ^ 3 / 3) (w ^ 2) w := by
      have := (hasDerivAt_pow 3 w).div_const 3
      convert this using 1
      norm_num
    exact h1.add h2
  exact (hP.const_mul Complex.I).cexp

lemma csr_zero : csr 0 = 0 := by
  unfold csr; exact Complex.zero_cpow (by norm_num)

/-- **Integration by parts along a chain.** -/
theorem Chain3.ibp {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) (U : ℝ) {G G' : ℂ → ℂ} {KG KG' : ℝ}
    (hKG : 0 ≤ KG) (hKG' : 0 ≤ KG')
    (hG : ∀ w ∈ ball (0 : ℂ) R₀, HasDerivAt G (G' w) w) (hG' : ContinuousOn G' (ball 0 R₀))
    (hGb : ∀ w ∈ ball (0 : ℂ) R₀, ‖G w‖ ≤ KG) (hGb' : ∀ w ∈ ball (0 : ℂ) R₀, ‖G' w‖ ≤ KG') :
    ch.intE U (fun w => csr w / (2 * w) * G w + csr w * G' w) +
      Complex.I * ch.intE U (fun w => csr w * G w * ((kap : ℂ) * U + w ^ 2)) =
      csr p * G p * Complex.exp (Complex.I * PhU U p) := by
  set hX : ℂ → ℂ := fun w => csr w / (2 * w) * G w + csr w * G' w with hXd
  set h3 : ℂ → ℂ := fun w => csr w * G w * ((kap : ℂ) * U + w ^ 2) with h3d
  set Ψ : ℂ → ℂ := fun w => csr w * G w * Complex.exp (Complex.I * PhU U w) with hΨ
  set Ψ' : ℂ → ℂ := fun w => (hX w + Complex.I * h3 w) * Complex.exp (Complex.I * PhU U w) with hΨ'
  have hK2 : 0 ≤ KG * (kap * |U| + R₀ ^ 2) :=
    mul_nonneg hKG (add_nonneg (mul_nonneg kap_pos.le (abs_nonneg _)) (sq_nonneg _))
  -- regularity
  have hGc : ∀ w ∈ ball (0 : ℂ) R₀, ContinuousAt G w := fun w hw => (hG w hw).continuousAt
  have hXc : ∀ z ∈ ball (0 : ℂ) R₀, 0 ≤ z.re → z ≠ 0 → ContinuousAt hX z := by
    intro z hz hre hz0
    have h1 : ContinuousAt (fun w => csr w / (2 * w)) z :=
      (continuousAt_csr (Or.inl hre)).div (continuousAt_const.mul continuousAt_id) (by simpa using hz0)
    have h2 : ContinuousAt G' z := hG'.continuousAt (isOpen_ball.mem_nhds hz)
    exact (h1.mul (hGc z hz)).add ((continuousAt_csr (Or.inl hre)).mul h2)
  have hXb : ∀ z ∈ ball (0 : ℂ) R₀, 0 ≤ z.re → z ≠ 0 →
      ‖hX z‖ ≤ (KG / 2) * ‖z‖ ^ (-(1 / 2 : ℝ)) + KG' * ‖z‖ ^ (1 / 2 : ℝ) + 0 * ‖z‖ ^ (0 : ℝ) := by
    intro z hz hre hz0
    have e1 : ‖csr z / (2 * z) * G z‖ ≤ (KG / 2) * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
      rw [norm_mul, norm_csr_div hz0]
      have := mul_le_mul_of_nonneg_left (hGb z hz) (by positivity : 0 ≤ (1 / 2) * ‖z‖ ^ (-(1 / 2 : ℝ)))
      linarith only [this]
    have e2 : ‖csr z * G' z‖ ≤ KG' * ‖z‖ ^ (1 / 2 : ℝ) := by
      rw [norm_mul, norm_csr_rpow]
      have := mul_le_mul_of_nonneg_left (hGb' z hz) (by positivity : 0 ≤ ‖z‖ ^ (1 / 2 : ℝ))
      linarith only [this]
    calc ‖hX z‖ ≤ ‖csr z / (2 * z) * G z‖ + ‖csr z * G' z‖ := norm_add_le _ _
      _ ≤ _ := by simp only [zero_mul, add_zero]; linarith only [e1, e2]
  have h3c : ∀ z ∈ ball (0 : ℂ) R₀, 0 ≤ z.re → z ≠ 0 → ContinuousAt (fun w => Complex.I * h3 w) z := by
    intro z hz hre hz0
    exact continuousAt_const.mul (((continuousAt_csr (Or.inl hre)).mul (hGc z hz)).mul
      (continuousAt_const.add (continuousAt_id.pow 2)))
  have h3b : ∀ z ∈ ball (0 : ℂ) R₀, 0 ≤ z.re → z ≠ 0 →
      ‖Complex.I * h3 z‖ ≤ 0 * ‖z‖ ^ (-(1 / 2 : ℝ)) + (KG * (kap * |U| + R₀ ^ 2)) * ‖z‖ ^ (1 / 2 : ℝ) +
        0 * ‖z‖ ^ (0 : ℝ) := by
    intro z hz hre hz0
    have hzR : ‖z‖ < R₀ := by rwa [mem_ball_zero_iff] at hz
    have hq : ‖(kap : ℂ) * U + z ^ 2‖ ≤ kap * |U| + R₀ ^ 2 := by
      calc ‖(kap : ℂ) * U + z ^ 2‖ ≤ ‖(kap : ℂ) * U‖ + ‖z ^ 2‖ := norm_add_le _ _
        _ ≤ kap * |U| + R₀ ^ 2 := by
          have h1 : ‖(kap : ℂ) * U‖ = kap * |U| := by
            rw [norm_mul]; simp [abs_of_pos kap_pos]
          rw [h1, norm_pow]
          have := norm_nonneg z
          nlinarith
    simp only [h3d]
    rw [norm_mul, Complex.norm_I, one_mul, norm_mul, norm_mul, norm_csr_rpow]
    have h1 := mul_le_mul (hGb z hz) hq (norm_nonneg _) hKG
    have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ ‖z‖ ^ (1 / 2 : ℝ))
    simp only [zero_mul, zero_add, add_zero]
    linarith only [this]
  have hbX : ch.Bd hX (KG / 2) (-(1 / 2)) KG' (1 / 2) 0 0 := Chain3.Bd.of_pointwise ch hXc hXb
  have hb3 : ch.Bd (fun w => Complex.I * h3 w) 0 (-(1 / 2)) (KG * (kap * |U| + R₀ ^ 2)) (1 / 2) 0 0 :=
    Chain3.Bd.of_pointwise ch h3c h3b
  have hbs : ch.Bd (fun w => hX w + Complex.I * h3 w) (KG / 2) (-(1 / 2))
      (KG' + KG * (kap * |U| + R₀ ^ 2)) (1 / 2) 0 0 := by
    refine Chain3.Bd.of_pointwise ch (fun z hz hre hz0 => (hXc z hz hre hz0).add (h3c z hz hre hz0)) ?_
    intro z hz hre hz0
    have a := hXb z hz hre hz0
    have b := h3b z hz hre hz0
    calc ‖hX z + Complex.I * h3 z‖ ≤ ‖hX z‖ + ‖Complex.I * h3 z‖ := norm_add_le _ _
      _ ≤ _ := by linarith only [a, b]
  -- FTC
  have hftc : ch.int Ψ' = Ψ p - Ψ 0 := by
    have hderiv : ∀ z ∈ ball (0 : ℂ) R₀, 0 ≤ z.re → z ≠ 0 → HasDerivAt Ψ (Ψ' z) z := by
      intro z hz hre hz0
      have hs : z ∈ slitPlane := mem_slit_of_re_nonneg hre hz0
      have h := ((hasDerivAt_csr hs).mul (hG z hz)).mul (hasDerivAt_PhU U z)
      refine h.congr_deriv ?_
      simp only [hΨ', hXd, h3d, Pi.mul_apply]
      ring
    have hcontΨ : ∀ z ∈ ball (0 : ℂ) R₀, 0 ≤ z.re → ContinuousAt Ψ z := by
      intro z hz hre
      exact ((continuousAt_csr (Or.inl hre)).mul (hGc z hz)).mul (hasDerivAt_PhU U z).continuousAt
    have hok : ∀ q ∈ [ch.q1, ch.q2, ch.q3], q.Ok R₀ := by
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      exacts [ch.ok1, ch.ok2, ch.ok3]
    refine Chain3.int_ftc ch ?_ ?_ ?_
    · intro q hq
      have hqok := hok q hq
      have hcp : Continuous q.pt := by unfold Piece.pt; fun_prop
      intro t ht
      have hm := hqok.2.1 t ht
      exact ((hcontΨ (q.pt t) hm.1 hm.2).comp (hcp.continuousAt (x := t))).continuousWithinAt
    · intro q hq t ht
      have hqok := hok q hq
      have hm := hqok.2.1 t ⟨ht.1.le, ht.2.le⟩
      exact hderiv _ hm.1 hm.2 (hqok.2.2 t ⟨ht.1, ht.2.le⟩)
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      have hint : ∀ q : Piece, q.Ok R₀ → PieceBd (fun w => hX w + Complex.I * h3 w) q (KG / 2) (-(1 / 2))
          (KG' + KG * (kap * |U| + R₀ ^ 2)) (1 / 2) 0 0 → IntervalIntegrable
          (fun t : ℝ => Ψ' (q.z0 + (t : ℂ) * q.d) * q.d) volume q.a q.b := by
        intro q hq hb
        exact PieceBd.integrable hq (by linarith) (by linarith) le_rfl (by norm_num) (by norm_num) (by norm_num) U hb
      rcases hq with rfl | rfl | rfl
      exacts [hint _ ch.ok1 hbs.1, hint _ ch.ok2 hbs.2.1, hint _ ch.ok3 hbs.2.2]
  have hΨ0 : Ψ 0 = 0 := by simp [hΨ, csr_zero]
  have hint' : ch.int Ψ' = ch.intE U hX + Complex.I * ch.intE U h3 := by
    have e1 : ch.int Ψ' = ch.intE U (fun w => hX w + Complex.I * h3 w) := rfl
    rw [e1, Chain3.intE_add ch (K1 := KG / 2) (α1 := -(1 / 2)) (K2 := KG') (α2 := 1 / 2) (K3 := 0) (α3 := 0)
      (L1 := 0) (β1 := -(1 / 2)) (L2 := KG * (kap * |U| + R₀ ^ 2)) (β2 := 1 / 2) (L3 := 0) (β3 := 0)
      ⟨by linarith, hKG', le_rfl⟩ ⟨le_rfl, hK2, le_rfl⟩ le_rfl (by norm_num) (by norm_num)
      le_rfl (by norm_num) (by norm_num) hbX hb3]
    rw [show ch.intE U (fun w => Complex.I * h3 w) = Complex.I * ch.intE U h3 from
      Chain3.intE_const_mul ch U Complex.I h3]
  rw [hΨ0, sub_zero] at hftc
  rw [← hint', hftc]

end FormalResearch.SignUncertainty.CtSd
