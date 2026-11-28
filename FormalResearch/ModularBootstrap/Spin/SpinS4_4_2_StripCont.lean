module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_4_2_Strip
public import FormalResearch.ModularBootstrap.TipFront.ComplexPoissonJensen

/-!
# Closed-strip continuity, `γ_N` bounds, and slit Jensen helpers for `SpinS4_4_2`

Leaf helper module isolating:
- `spinGamma_pow_bounds`: `γ_N = (spinGamma a)^N ∈ [3/4, 1]` and `γ_N⁻¹ - 1 ≤ 48 * N / n`;
- `continuousOn_spinQSlice_closedStrip`: continuity of `spinQSlice` on `{b : ℂ | |b.im| ≤ γ_N / 2}`;
- `confB_add_I_norm_fourth_lb`, `confB_add_I_ne_zero_of_im`, `spinQSlice_bdy_ne_zero_ae`;
- `slitMass_pos_s4`, `slitMass_le_one_s4`, `log_integral_jensen_slitPreimage_s4`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.Special

private lemma one_sub_mul_le_pow_s4 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∀ k : ℕ, 1 - (k : ℝ) * x ≤ (1 - x) ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Nat.cast_succ]
    have h1mx : 0 ≤ 1 - x := by linarith
    calc 1 - ((m : ℝ) + 1) * x
        ≤ (1 - (m : ℝ) * x) * (1 - x) := by nlinarith [mul_nonneg (Nat.cast_nonneg m : 0 ≤ (m : ℝ)) (sq_nonneg x)]
      _ ≤ (1 - x) ^ m * (1 - x) := mul_le_mul_of_nonneg_right ih h1mx

lemma spinGamma_pow_bounds {c : ℝ} {N : ℕ} (hc : 49 ≤ c) (hN_pos : 1 ≤ N)
    (hN_n : 768 * (N : ℝ) ≤ c - 1) :
    let n := c - 1
    let a := n / 12
    let γN := spinGamma a * (spinLambda a ^ (N - 1))⁻¹
    γN = spinGamma a ^ N ∧ 3 / 4 ≤ γN ∧ γN ≤ 1 ∧ γN⁻¹ - 1 ≤ 48 * (N : ℝ) / n := by
  intro n a γN
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have hgam_pos : 0 < spinGamma a := spinGamma_pos (by linarith)
  have h2a_le : 2 / a ≤ 1 / 2 := by
    have ha4 : 4 ≤ a := by dsimp [a, n]; linarith
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hgam_le1 : spinGamma a ≤ 1 := by
    unfold spinGamma
    exact (Real.sqrt_le_one).mpr (by linarith [show 0 < 2 / a by positivity])
  have hgam_ge : 1 - 24 / n ≤ spinGamma a := by
    have h24 : 2 / a = 24 / n := by dsimp [a]; field_simp [hn_pos.ne']; norm_num
    have hsq : 1 - 24 / n ≤ Real.sqrt (1 - 2 / a) := by
      rw [← h24]
      exact Real.le_sqrt_of_sq_le (by nlinarith [h2a_le, show (0 : ℝ) < 2 / a by positivity])
    exact hsq
  have hγ_eq : γN = spinGamma a ^ N := by
    dsimp [γN]; unfold spinLambda; rw [inv_pow, inv_inv]
    have hN1 : N = (N - 1) + 1 := (Nat.sub_add_cancel hN_pos).symm
    nth_rw 2 [hN1]; rw [pow_succ']
  have hγ_le1 : γN ≤ 1 := by rw [hγ_eq]; exact pow_le_one₀ hgam_pos.le hgam_le1
  have h24n_le1 : 24 / n ≤ 1 := by
    rw [div_le_one hn_pos]; linarith [show (48 : ℝ) ≤ n by dsimp [n]; linarith]
  have hbern : 1 - (N : ℝ) * (24 / n) ≤ (1 - 24 / n) ^ N :=
    one_sub_mul_le_pow_s4 (by positivity) h24n_le1 N
  have h24N_n : (N : ℝ) * (24 / n) ≤ 1 / 32 := by
    rw [← mul_div_assoc, mul_comm (N : ℝ) 24, div_le_iff₀ hn_pos]; linarith
  have hγ_ge_pow : 1 - 24 * (N : ℝ) / n ≤ γN := by
    calc 1 - 24 * (N : ℝ) / n = 1 - (N : ℝ) * (24 / n) := by ring
      _ ≤ (1 - 24 / n) ^ N := hbern
      _ ≤ spinGamma a ^ N := pow_le_pow_left₀ (by linarith) hgam_ge N
      _ = γN := hγ_eq.symm
  have hγ_34 : 3 / 4 ≤ γN := by
    have h24_eq : (N : ℝ) * (24 / n) = 24 * (N : ℝ) / n := by ring
    linarith only [hγ_ge_pow, h24N_n, h24_eq]
  have hinv_sub : γN⁻¹ - 1 ≤ 48 * (N : ℝ) / n := by
    have hγ_pos : 0 < γN := by linarith
    have h48n : 0 ≤ 48 * (N : ℝ) / n := div_nonneg (by positivity) hn_pos.le
    rw [inv_eq_one_div, div_sub_one hγ_pos.ne', div_le_iff₀ hγ_pos]
    calc 1 - γN ≤ 24 * (N : ℝ) / n := by linarith
      _ = (48 * (N : ℝ) / n) * (1 / 2) := by ring
      _ ≤ (48 * (N : ℝ) / n) * γN := mul_le_mul_of_nonneg_left (by linarith) h48n
  exact ⟨hγ_eq, hγ_34, hγ_le1, hinv_sub⟩

private lemma continuousOn_spinDaC_closed {a : ℝ} (ha : 2 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) :
    ContinuousOn (fun q : ℂ × ℂ => spinDaC a Φ q.1 q.2)
      ({z : ℂ | |z.im| ≤ 1 / 2} ×ˢ {z : ℂ | |z.im| ≤ 1 / 2}) := by
  let S : Set (ℂ × ℂ) := {z : ℂ | |z.im| ≤ 1 / 2} ×ˢ {z : ℂ | |z.im| ≤ 1 / 2}
  intro q₀ _hq₀
  let R_re : ℝ := max |q₀.1.re| |q₀.2.re| + 1
  let C_bd : ℝ := (1 + 4 * R_re ^ 2) ^ 2
  let F : (ℂ × ℂ) → (ℝ × ℝ) → ℂ := fun q p =>
    (Φ p : ℂ) * spinWa a p.1 q.1 * spinWa a p.2 q.2
  have hF_meas : ∀ᶠ q in 𝓝[S] q₀, AEStronglyMeasurable (F q) volume :=
    Eventually.of_forall fun q => by
      have h1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
      have h2 : Continuous (fun p : ℝ × ℝ => spinWa a p.1 q.1) := by unfold spinWa; fun_prop
      have h3 : Continuous (fun p : ℝ × ℝ => spinWa a p.2 q.2) := by unfold spinWa; fun_prop
      exact ((h1.mul h2).mul h3).aestronglyMeasurable
  have hF_bd : ∀ᶠ q in 𝓝[S] q₀, ∀ᵐ p : ℝ × ℝ ∂volume,
      ‖F q p‖ ≤ C_bd * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by
    have hnb : {q : ℂ × ℂ | ‖q.1 - q₀.1‖ < 1 ∧ ‖q.2 - q₀.2‖ < 1} ∈ 𝓝 q₀ := by
      have ho : IsOpen {q : ℂ × ℂ | ‖q.1 - q₀.1‖ < 1 ∧ ‖q.2 - q₀.2‖ < 1} :=
        (isOpen_lt (continuous_fst.sub continuous_const).norm continuous_const).inter
          (isOpen_lt (continuous_snd.sub continuous_const).norm continuous_const)
      exact ho.mem_nhds (by simp)
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hnb] with q ⟨hq1_b, hq2_b⟩ hqS
    refine Eventually.of_forall fun p => ?_
    have hre1 : |q.1.re| ≤ R_re := by
      have hdiff : |q.1.re - q₀.1.re| ≤ 1 := by
        calc |q.1.re - q₀.1.re| = |(q.1 - q₀.1).re| := by simp
          _ ≤ ‖q.1 - q₀.1‖ := Complex.abs_re_le_norm _
          _ ≤ 1 := hq1_b.le
      calc |q.1.re| ≤ |q₀.1.re| + |q.1.re - q₀.1.re| := by
            simpa [sub_eq_add_neg, add_comm] using abs_sub_le q.1.re q₀.1.re 0
        _ ≤ max |q₀.1.re| |q₀.2.re| + 1 := add_le_add (le_max_left _ _) hdiff
    have hre2 : |q.2.re| ≤ R_re := by
      have hdiff : |q.2.re - q₀.2.re| ≤ 1 := by
        calc |q.2.re - q₀.2.re| = |(q.2 - q₀.2).re| := by simp
          _ ≤ ‖q.2 - q₀.2‖ := Complex.abs_re_le_norm _
          _ ≤ 1 := hq2_b.le
      calc |q.2.re| ≤ |q₀.2.re| + |q.2.re - q₀.2.re| := by
            simpa [sub_eq_add_neg, add_comm] using abs_sub_le q.2.re q₀.2.re 0
        _ ≤ max |q₀.1.re| |q₀.2.re| + 1 := add_le_add (le_max_right _ _) hdiff
    have h1 := norm_spinWa_le ha p.1 hqS.1
    have h2 := norm_spinWa_le ha p.2 hqS.2
    have hsq1 : q.1.re ^ 2 ≤ R_re ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre1 2
    have hsq2 : q.2.re ^ 2 ≤ R_re ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre2 2
    have h1' : ‖spinWa a p.1 q.1‖ ≤ (1 + 4 * R_re ^ 2) * spinV1 a p.1 := by
      refine h1.trans ?_; have := spinV1_nonneg ha p.1; gcongr
    have h2' : ‖spinWa a p.2 q.2‖ ≤ (1 + 4 * R_re ^ 2) * spinV1 a p.2 := by
      refine h2.trans ?_; have := spinV1_nonneg ha p.2; gcongr
    dsimp [F, C_bd]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hprod := mul_le_mul h1' h2' (norm_nonneg _) (mul_nonneg (by positivity) (spinV1_nonneg ha p.1))
    calc |Φ p| * ‖spinWa a p.1 q.1‖ * ‖spinWa a p.2 q.2‖
        = |Φ p| * (‖spinWa a p.1 q.1‖ * ‖spinWa a p.2 q.2‖) := by ring
      _ ≤ |Φ p| * (((1 + 4 * R_re ^ 2) * spinV1 a p.1) * ((1 + 4 * R_re ^ 2) * spinV1 a p.2)) :=
          mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
      _ = (1 + 4 * R_re ^ 2) ^ 2 * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by ring
  have hF_cont : ∀ᵐ p : ℝ × ℝ ∂volume, ContinuousWithinAt (fun q : ℂ × ℂ => F q p) S q₀ :=
    Eventually.of_forall fun p => by
      dsimp [F]
      have h1 : Continuous (fun q : ℂ × ℂ => spinWa a p.1 q.1) := by unfold spinWa; fun_prop
      have h2 : Continuous (fun q : ℂ × ℂ => spinWa a p.2 q.2) := by unfold spinWa; fun_prop
      exact ((continuous_const.mul h1).mul h2).continuousAt.continuousWithinAt
  have hint_c := continuousWithinAt_of_dominated hF_meas hF_bd (hΦ.int_M2.const_mul C_bd) hF_cont
  have heq : (fun q : ℂ × ℂ => spinDaC a Φ q.1 q.2) = fun q => -(∫ p : ℝ × ℝ, F q p) := by
    ext q; rw [spinDaC_eq_spinWa]
  rw [heq]
  exact hint_c.neg

lemma continuousOn_spinQSlice_closedStrip {c V C_V : ℝ} (hc : 49 ≤ c) (hV : 0 < V)
    (_hCV : 0 ≤ C_V)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass ((c - 1) / 12) Φ)
    {χ : ℝ → ℝ} (hχ_meas : Measurable χ) (hχ_bd : ∀ v, 0 ≤ χ v ∧ χ v ≤ 1)
    (hχ_supp : ∀ v, V < |v| → χ v = 0)
    (h41_poly : ∀ (d : ℝ) (b : ℂ), |d| ≤ V * Real.sqrt ((c - 1) ^ (-(2 / 3 : ℝ))) →
      |b.im| ≤ (spinGamma ((c - 1) / 12) *
        (spinLambda ((c - 1) / 12) ^ (Nat.ceil (Real.log (c - 1)) - 1))⁻¹) / 2 →
      ‖spinTruncInvC ((c - 1) / 12) (Nat.ceil (Real.log (c - 1))) Φ (b + (d : ℂ)) (b - (d : ℂ))‖ ≤
        C_V * (Nat.ceil (Real.log (c - 1)) : ℝ) ^ 2 * (1 + |b.re| ^ 2) ^ 2) :
    let n := c - 1
    let a := n / 12
    let N := Nat.ceil (Real.log n)
    let γN := spinGamma a * (spinLambda a ^ (N - 1))⁻¹
    ContinuousOn (spinQSlice c N Φ χ) {b : ℂ | |b.im| ≤ γN / 2} := by
  intro n a N γN
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have hlam_gt1 : 1 < spinLambda a := spinLambda_gt_one_s4 ha2
  have hN_pos : 1 ≤ N := Nat.ceil_pos.mpr (Real.log_pos (by linarith))
  have hglam : spinLambda a ^ N * γN = 1 := by
    have hN1 : N = (N - 1) + 1 := (Nat.sub_add_cancel hN_pos).symm
    dsimp [γN]; nth_rw 1 [hN1]
    rw [pow_succ', mul_assoc, mul_left_comm (spinLambda a ^ (N - 1)) (spinGamma a)]
    calc spinLambda a * (spinGamma a * (spinLambda a ^ (N - 1) * (spinLambda a ^ (N - 1))⁻¹))
        = (spinGamma a * spinLambda a) * (spinLambda a ^ (N - 1) * (spinLambda a ^ (N - 1))⁻¹) := by ring
      _ = 1 * 1 := by
          rw [spinGamma_mul_spinLambda ha2, mul_inv_cancel₀ (pow_ne_zero _ (lt_trans zero_lt_one hlam_gt1).ne')]
      _ = 1 := one_mul 1
  let ε : ℝ := n ^ (-(2 / 3 : ℝ))
  have hε_pos : 0 < ε := Real.rpow_pos_of_pos hn_pos _
  let V_bd : ℝ := V * Real.sqrt ε
  let S_c : Set ℂ := {b : ℂ | |b.im| ≤ γN / 2}
  have hDa_cont := continuousOn_spinDaC_closed ha2.le hΦ
  intro b₀ hb₀
  let M_b : ℝ := C_V * (N : ℝ) ^ 2 * (1 + (|b₀.re| + 1) ^ 2) ^ 2
  let bound : ℝ → ℝ := (Icc (-V_bd) V_bd).indicator (fun _ => M_b)
  have hbd_int : Integrable bound volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (hs := measure_Icc_lt_top.ne))
  let Fq : ℂ → ℝ → ℂ := fun b d =>
    (χ (d / Real.sqrt ε) : ℂ) * spinTruncInvC a N Φ (b + (d : ℂ)) (b - (d : ℂ))
  have hFq_meas : ∀ᶠ b in 𝓝[S_c] b₀, AEStronglyMeasurable (Fq b) volume := by
    rw [eventually_nhdsWithin_iff]
    refine Eventually.of_forall fun b hbS => ?_
    have hm1 : Measurable (fun d : ℝ => (χ (d / Real.sqrt ε) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (hχ_meas.comp (measurable_id.div_const _))
    have hm2 : Continuous (fun d : ℝ => spinTruncInvC a N Φ (b + (d : ℂ)) (b - (d : ℂ))) :=
      continuous_spinTruncInvC_d hc hΦ hbS
    exact (hm1.mul hm2.measurable).aestronglyMeasurable
  have hFq_bd : ∀ᶠ b in 𝓝[S_c] b₀, ∀ᵐ d : ℝ ∂volume, ‖Fq b d‖ ≤ bound d := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds b₀ zero_lt_one] with b hb_ball hbS
    refine Eventually.of_forall fun d => ?_
    by_cases hd : d ∈ Icc (-V_bd) V_bd
    · dsimp [bound]
      rw [Set.indicator_of_mem hd]
      have hre : |b.re| ≤ |b₀.re| + 1 := by
        have h1 : |b.re - b₀.re| ≤ 1 := by
          calc |b.re - b₀.re| = |(b - b₀).re| := by simp
            _ ≤ ‖b - b₀‖ := Complex.abs_re_le_norm _
            _ ≤ 1 := by rw [← dist_eq_norm]; exact (Metric.mem_ball.mp hb_ball).le
        calc |b.re| = |(b.re - b₀.re) + b₀.re| := by ring_nf
          _ ≤ |b.re - b₀.re| + |b₀.re| := abs_add_le _ _
          _ ≤ |b₀.re| + 1 := by linarith only [h1]
      have h41 := h41_poly d b (abs_le.mpr hd) hbS
      have hχ1 : |χ (d / Real.sqrt ε)| ≤ 1 := by
        have := hχ_bd (d / Real.sqrt ε); exact abs_le.mpr ⟨by linarith, this.2⟩
      dsimp [Fq, M_b]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |χ (d / Real.sqrt ε)| * ‖spinTruncInvC a N Φ (b + (d : ℂ)) (b - (d : ℂ))‖
          ≤ 1 * (C_V * (N : ℝ) ^ 2 * (1 + |b.re| ^ 2) ^ 2) :=
            mul_le_mul hχ1 h41 (norm_nonneg _) zero_le_one
        _ ≤ C_V * (N : ℝ) ^ 2 * (1 + (|b₀.re| + 1) ^ 2) ^ 2 := by rw [one_mul]; gcongr
    · have hVbd0 : 0 ≤ V_bd := by dsimp [V_bd]; positivity
      have hnot : V_bd < |d| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hd
        rcases hd with h1 | h2
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_nonneg (by linarith)]; linarith
      have hχ0 : χ (d / Real.sqrt ε) = 0 := by
        apply hχ_supp
        rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr hε_pos), lt_div_iff₀ (Real.sqrt_pos.mpr hε_pos)]
        exact hnot
      dsimp [Fq, bound]
      rw [Set.indicator_of_notMem hd, hχ0, Complex.ofReal_zero, zero_mul, norm_zero]
  have hFq_cont : ∀ᵐ d : ℝ ∂volume, ContinuousWithinAt (fun b : ℂ => Fq b d) S_c b₀ := by
    refine Eventually.of_forall fun d => ?_
    have hT_cont : ContinuousWithinAt
        (fun b : ℂ => spinTruncInvC a N Φ (b + (d : ℂ)) (b - (d : ℂ))) S_c b₀ := by
      have hsum_c : ∀ (j ℓ : ℕ), j < N → ℓ < N → ContinuousWithinAt
          (fun b : ℂ => spinDeltaAC a Φ ((spinLambda a ^ j : ℝ) * (b + (d : ℂ)))
            ((spinLambda a ^ ℓ : ℝ) * (b - (d : ℂ)))) S_c b₀ := fun j ℓ hj hℓ => by
        have hpair_m : ContinuousOn
            (fun b : ℂ => (((spinLambda a ^ (j + 1) : ℝ) : ℂ) * (b + (d : ℂ)),
              ((spinLambda a ^ (ℓ + 1) : ℝ) : ℂ) * (b - (d : ℂ)))) S_c := by
          have h1 : Continuous (fun b : ℂ => (((spinLambda a ^ (j + 1) : ℝ) : ℂ) * (b + (d : ℂ)))) := by
            fun_prop
          have h2 : Continuous (fun b : ℂ => (((spinLambda a ^ (ℓ + 1) : ℝ) : ℂ) * (b - (d : ℂ)))) := by
            fun_prop
          exact (h1.prodMk h2).continuousOn
        have hmaps : MapsTo
            (fun b : ℂ => (((spinLambda a ^ (j + 1) : ℝ) : ℂ) * (b + (d : ℂ)),
              ((spinLambda a ^ (ℓ + 1) : ℝ) : ℂ) * (b - (d : ℂ))))
            S_c ({z : ℂ | |z.im| ≤ 1 / 2} ×ˢ {z : ℂ | |z.im| ≤ 1 / 2}) := by
          intro b hbS
          have him : ∀ m : ℕ, m < N → |(((spinLambda a ^ (m + 1) : ℝ) : ℂ) * (b + (d : ℂ))).im| ≤ 1 / 2 :=
            fun m hm => by
              rw [Complex.im_ofReal_mul, Complex.add_im, Complex.ofReal_im, add_zero, abs_mul,
                abs_of_pos (pow_pos (lt_trans zero_lt_one hlam_gt1) _)]
              have hpow : spinLambda a ^ (m + 1) ≤ spinLambda a ^ N := pow_le_pow_right₀ hlam_gt1.le hm
              calc spinLambda a ^ (m + 1) * |b.im| ≤ spinLambda a ^ N * |b.im| :=
                    mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
                _ ≤ spinLambda a ^ N * (γN / 2) :=
                    mul_le_mul_of_nonneg_left hbS (pow_nonneg (lt_trans zero_lt_one hlam_gt1).le _)
                _ = (spinLambda a ^ N * γN) / 2 := by ring
                _ = 1 / 2 := by rw [hglam]
          have him' : |(((spinLambda a ^ (ℓ + 1) : ℝ) : ℂ) * (b - (d : ℂ))).im| ≤ 1 / 2 := by
            rw [Complex.im_ofReal_mul, Complex.sub_im, Complex.ofReal_im, sub_zero, abs_mul,
              abs_of_pos (pow_pos (lt_trans zero_lt_one hlam_gt1) _)]
            have hpow : spinLambda a ^ (ℓ + 1) ≤ spinLambda a ^ N := pow_le_pow_right₀ hlam_gt1.le hℓ
            calc spinLambda a ^ (ℓ + 1) * |b.im| ≤ spinLambda a ^ N * |b.im| :=
                  mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
              _ ≤ spinLambda a ^ N * (γN / 2) :=
                  mul_le_mul_of_nonneg_left hbS (pow_nonneg (lt_trans zero_lt_one hlam_gt1).le _)
              _ = (spinLambda a ^ N * γN) / 2 := by ring
              _ = 1 / 2 := by rw [hglam]
          exact ⟨him j hj, him'⟩
        have hcomp : ContinuousWithinAt
            ((fun q : ℂ × ℂ => spinDaC a Φ q.1 q.2) ∘
              (fun b : ℂ => (((spinLambda a ^ (j + 1) : ℝ) : ℂ) * (b + (d : ℂ)),
                ((spinLambda a ^ (ℓ + 1) : ℝ) : ℂ) * (b - (d : ℂ))))) S_c b₀ :=
          ContinuousWithinAt.comp
            (g := fun q : ℂ × ℂ => spinDaC a Φ q.1 q.2)
            (f := fun b : ℂ => (((spinLambda a ^ (j + 1) : ℝ) : ℂ) * (b + (d : ℂ)),
              ((spinLambda a ^ (ℓ + 1) : ℝ) : ℂ) * (b - (d : ℂ))))
            (hDa_cont _ (hmaps hb₀)) (hpair_m b₀ hb₀) hmaps
        refine hcomp.congr_of_eventuallyEq (Eventually.of_forall fun b => ?_) ?_
        · unfold spinDeltaAC; rw [pow_succ', pow_succ']
          exact congr_arg₂ (spinDaC a Φ) (by push_cast; ring) (by push_cast; ring)
        · unfold spinDeltaAC; rw [pow_succ', pow_succ']
          exact congr_arg₂ (spinDaC a Φ) (by push_cast; ring) (by push_cast; ring)
      have hcw_sum : ∀ (M : ℕ) (F : ℕ → ℂ → ℂ),
          (∀ m < M, ContinuousWithinAt (F m) S_c b₀) →
          ContinuousWithinAt (fun b => ∑ m ∈ Finset.range M, F m b) S_c b₀ := fun M F hF => by
        induction M with
        | zero => simpa using continuousWithinAt_const
        | succ k ih =>
          simp_rw [Finset.sum_range_succ]
          exact (ih fun m hm => hF m (Nat.lt_succ_of_lt hm)).add (hF k (Nat.lt_succ_self k))
      have heq : (fun b : ℂ => spinTruncInvC a N Φ (b + (d : ℂ)) (b - (d : ℂ))) =
          fun b : ℂ => ∑ j ∈ Finset.range N, ∑ ℓ ∈ Finset.range N,
            spinDeltaAC a Φ ((spinLambda a ^ j : ℝ) * (b + (d : ℂ)))
              ((spinLambda a ^ ℓ : ℝ) * (b - (d : ℂ))) := rfl
      rw [heq]
      exact hcw_sum N _ fun j hj => hcw_sum N _ fun ℓ hℓ => hsum_c j ℓ hj hℓ
    exact continuousWithinAt_const.mul hT_cont
  have hres := continuousWithinAt_of_dominated hFq_meas hFq_bd hbd_int hFq_cont
  exact hres

lemma confB_add_I_norm_fourth_lb {b : ℂ} (hb : |b.im| ≤ 1 / 2) :
    (1 + |b.re| ^ 2) ^ 2 ≤ 16 * ‖(b + I) ^ 4‖ := by
  have him_ge : 1 / 2 ≤ (b + I).im := by
    have := (abs_le.mp hb).1; rw [Complex.add_im, Complex.I_im]; linarith
  have hsq : 1 / 4 * (1 + |b.re| ^ 2) ≤ ‖b + I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have h1 : (b + I).re ^ 2 = |b.re| ^ 2 := by rw [Complex.add_re, Complex.I_re, add_zero, sq_abs]
    have h2 : 1 / 4 ≤ (b + I).im ^ 2 := by nlinarith
    nlinarith
  have h4 : (1 / 4 * (1 + |b.re| ^ 2)) ^ 2 ≤ (‖b + I‖ ^ 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsq 2
  rw [norm_pow]
  linarith [show (1 / 4 * (1 + |b.re| ^ 2)) ^ 2 = (1 + |b.re| ^ 2) ^ 2 / 16 by ring,
    show (‖b + I‖ ^ 2) ^ 2 = ‖b + I‖ ^ 4 by ring]

lemma confB_add_I_ne_zero_of_im {b : ℂ} (hb : |b.im| ≤ 1 / 2) : b + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at this
  linarith [(abs_le.mp hb).1]

lemma spinQSlice_bdy_ne_zero_ae {c V : ℝ} (hc : 49 ≤ c) (hV : 0 < V)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass ((c - 1) / 12) Φ)
    {χ : ℝ → ℝ} (hχ_meas : Measurable χ) (hχ_bd : ∀ v, 0 ≤ χ v ∧ χ v ≤ 1)
    (hχ_supp : ∀ v, V < |v| → χ v = 0)
    {b₀ : ℂ}
    (hb₀ : |b₀.im| < (spinGamma ((c - 1) / 12) *
      (spinLambda ((c - 1) / 12) ^ (Nat.ceil (Real.log (c - 1)) - 1))⁻¹) / 2)
    (hb₀_ne : spinQSlice c (Nat.ceil (Real.log (c - 1))) Φ χ b₀ ≠ 0) :
    let n := c - 1
    let a := n / 12
    let N := Nat.ceil (Real.log n)
    let γN := spinGamma a * (spinLambda a ^ (N - 1))⁻¹
    ∀ᵐ σ ∂(volume.restrict slitPreimage),
      spinQSlice c N Φ χ ((γN : ℂ) * (slitBoundaryMap σ : ℂ)) ≠ 0 := by
  intro n a N γN
  have hγN_pos : 0 < γN := by
    have ha2 : 2 < a := by dsimp [a, n]; linarith
    exact mul_pos (spinGamma_pos ha2) (inv_pos.mpr (pow_pos (lt_trans zero_lt_one (spinLambda_gt_one_s4 ha2)) _))
  have han : AnalyticOnNhd ℂ (spinQSlice c N Φ χ) {w : ℂ | |w.im| < γN / 2} :=
    (spinQSlice_differentiableOn hc hV hΦ hχ_meas hχ_bd hχ_supp).analyticOnNhd
      (isOpen_lt Complex.continuous_im.abs continuous_const)
  have hpre : IsPreconnected {w : ℂ | |w.im| < γN / 2} := by
    have hconv : Convex ℝ {w : ℂ | |w.im| < γN / 2} := by
      intro x hx y hy u v hu hv huv
      change |(u • x + v • y).im| < γN / 2
      have him : (u • x + v • y).im = u * x.im + v * y.im := by simp [Complex.add_im, Complex.real_smul]
      rw [him]
      have hx' : |x.im| < γN / 2 := hx
      have hy' : |y.im| < γN / 2 := hy
      have hbd : u * |x.im| + v * |y.im| < γN / 2 := by
        rcases eq_or_lt_of_le hu with rfl | hu_pos
        · have hv1 : v = 1 := by linarith
          subst hv1; simpa using hy'
        · have hv0 : 0 ≤ v := hv
          have h1 : u * |x.im| < u * (γN / 2) := mul_lt_mul_of_pos_left hx' hu_pos
          have h2 : v * |y.im| ≤ v * (γN / 2) := mul_le_mul_of_nonneg_left hy'.le hv0
          nlinarith [show u + v = 1 from huv]
      calc |u * x.im + v * y.im| ≤ |u * x.im| + |v * y.im| := abs_add_le _ _
        _ = u * |x.im| + v * |y.im| := by rw [abs_mul, abs_mul, abs_of_nonneg hu, abs_of_nonneg hv]
        _ < γN / 2 := hbd
    exact hconv.isPreconnected
  have hz_re_cnt : {r : ℝ | spinQSlice c N Φ χ ((γN : ℂ) * (r : ℂ)) = 0}.Countable := by
    have heq : {r : ℝ | spinQSlice c N Φ χ ((γN : ℂ) * (r : ℂ)) = 0} =
        ⋃ k : ℕ, {r : ℝ | r ∈ Icc (-(k : ℝ)) k ∧ spinQSlice c N Φ χ ((γN : ℂ) * (r : ℂ)) = 0} := by
      ext r; simp only [Set.mem_ofPred_eq, mem_iUnion, mem_Icc]
      refine ⟨fun hr => ?_, fun ⟨_, _, hr⟩ => hr⟩
      obtain ⟨k, hk⟩ := exists_nat_ge |r|
      exact ⟨k, ⟨by linarith [abs_le.mp hk], by linarith [abs_le.mp hk]⟩, hr⟩
    rw [heq]
    have hfin : ∀ k : ℕ,
        {r : ℝ | r ∈ Icc (-(k : ℝ)) k ∧ spinQSlice c N Φ χ ((γN : ℂ) * (r : ℂ)) = 0}.Finite := by
      intro k; by_contra hinf; rw [Set.not_finite] at hinf
      obtain ⟨r₀, _, hacc⟩ := hinf.exists_accPt_of_subset_isCompact isCompact_Icc (fun _ hr => hr.1)
      have hr₀_mem : ((γN : ℂ) * (r₀ : ℂ)) ∈ {w : ℂ | |w.im| < γN / 2} := by
        simp [Complex.mul_im, half_pos hγN_pos]
      have hfreq : ∃ᶠ z in 𝓝[≠] ((γN : ℂ) * (r₀ : ℂ)), spinQSlice c N Φ χ z = 0 := by
        rw [Filter.frequently_iff]
        intro U hU
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU
        obtain ⟨V', hV', hVU⟩ := hU
        obtain ⟨δ, hδ_pos, hball⟩ := Metric.mem_nhds_iff.mp hV'
        rw [accPt_iff_frequently] at hacc
        obtain ⟨r, ⟨hr_ne, hr_mem⟩, hr_ball⟩ :=
          (hacc.and_eventually (Metric.ball_mem_nhds r₀ (div_pos hδ_pos hγN_pos))).exists
        have hrC_ne : (γN : ℂ) * (r : ℂ) ≠ (γN : ℂ) * (r₀ : ℂ) := by
          intro he
          have : (r : ℂ) = (r₀ : ℂ) := mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hγN_pos.ne') he
          exact hr_ne (Complex.ofReal_injective this)
        have hrC_ball : (γN : ℂ) * (r : ℂ) ∈ Metric.ball ((γN : ℂ) * (r₀ : ℂ)) δ := by
          rw [Metric.mem_ball, Complex.dist_eq, ← mul_sub, norm_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hγN_pos, ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs]
          have hrb : |r - r₀| < δ / γN := by simpa [Metric.mem_ball, Real.dist_eq] using hr_ball
          exact (lt_div_iff₀' hγN_pos).mp hrb
        exact ⟨(γN : ℂ) * (r : ℂ), hVU ⟨hball hrC_ball, hrC_ne⟩, hr_mem.2⟩
      have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hpre hr₀_mem hfreq
      exact hb₀_ne (hzero hb₀)
    exact Set.countable_iUnion fun k => (hfin k).countable
  have hσ_cnt : {σ : ℝ | σ ∈ slitPreimage ∧
      spinQSlice c N Φ χ ((γN : ℂ) * (slitBoundaryMap σ : ℂ)) = 0}.Countable := by
    have hsub : {σ : ℝ | σ ∈ slitPreimage ∧
          spinQSlice c N Φ χ ((γN : ℂ) * (slitBoundaryMap σ : ℂ)) = 0} ⊆
        ⋃ r ∈ {r : ℝ | spinQSlice c N Φ χ ((γN : ℂ) * (r : ℂ)) = 0},
          {σ : ℝ | σ ∈ slitPreimage ∧ slitBoundaryMap σ = r} := fun σ ⟨hσ, h0⟩ =>
      mem_iUnion₂.mpr ⟨slitBoundaryMap σ, h0, hσ, rfl⟩
    exact (hz_re_cnt.biUnion fun r _ => (slitBoundaryMap_preimage_finite r).countable).mono hsub
  have hnull : volume {σ : ℝ | σ ∈ slitPreimage ∧
      spinQSlice c N Φ χ ((γN : ℂ) * (slitBoundaryMap σ : ℂ)) = 0} = 0 :=
    hσ_cnt.measure_zero volume
  change ∀ᵐ σ ∂volume.restrict (Ioo (-1 : ℝ) 0 ∪ Ioi 1),
      spinQSlice c N Φ χ ((γN : ℂ) * (slitBoundaryMap σ : ℂ)) ≠ 0
  rw [ae_restrict_iff' (measurableSet_Ioo.union measurableSet_Ioi)]
  filter_upwards [compl_mem_ae_iff.mpr hnull] with σ hσ hmem h0
  exact hσ ⟨hmem, h0⟩

lemma slitMass_pos_s4 {x y : ℝ} (hy : 0 < y) : 0 < slitMass x y := by
  have h1 : 0 < ∫ σ in slitPreimage, poissonKernel x y σ := by
    refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ (integrable_poissonKernel x hy).integrableOn).mpr ?_
    · exact Eventually.of_forall fun σ => poissonKernel_nonneg hy.le σ
    · have heq : (Function.support fun σ => poissonKernel x y σ) ∩ slitPreimage = slitPreimage := by
        ext σ; simp only [mem_inter_iff, Function.mem_support, ne_eq, and_iff_right_iff_imp]
        intro _; exact (poissonKernel_pos (x := x) hy σ).ne'
      rw [heq]
      exact lt_of_lt_of_le (by rw [Real.volume_Ioo]; norm_num : (0 : ℝ≥0∞) < volume (Ioo (-1 : ℝ) 0))
        (measure_mono Set.subset_union_left)
  exact h1

lemma slitMass_le_one_s4 {x y : ℝ} (hy : 0 < y) : slitMass x y ≤ 1 := by
  have h1 : ∫ σ in slitPreimage, poissonKernel x y σ ≤ ∫ σ : ℝ, poissonKernel x y σ :=
    setIntegral_le_integral (integrable_poissonKernel x hy)
      (Eventually.of_forall fun σ => poissonKernel_nonneg hy.le σ)
  rwa [integral_poissonKernel x hy] at h1

lemma log_integral_jensen_slitPreimage_s4 {x y : ℝ} (hy : 0 < y)
    {f : ℝ → ℝ} (hf_pos : ∀ᵐ σ ∂(volume.restrict slitPreimage), 0 < f σ)
    (hf_int : IntegrableOn (fun σ => f σ * poissonKernel x y σ) slitPreimage)
    (hlog_int : IntegrableOn (fun σ => Real.log (f σ) * poissonKernel x y σ) slitPreimage)
    {B : ℝ} (_hB_pos : 0 < B)
    (hI_le : ∫ σ in slitPreimage, f σ * poissonKernel x y σ ≤ B) :
    ∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x y σ ≤
      slitMass x y * Real.log B + (1 - slitMass x y) := by
  have hm_pos : 0 < slitMass x y := slitMass_pos_s4 hy
  set m := slitMass x y
  set I_f := ∫ σ in slitPreimage, f σ * poissonKernel x y σ
  have hIf_pos : 0 < I_f := by
    refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ hf_int).mpr ?_
    · filter_upwards [hf_pos] with σ hσ
      exact mul_nonneg hσ.le (poissonKernel_nonneg hy.le σ)
    · have hIoo_sub : Ioo (-1 : ℝ) 0 ⊆ slitPreimage := Set.subset_union_left
      have hIoo_pos : 0 < volume (Ioo (-1 : ℝ) 0) := by rw [Real.volume_Ioo]; norm_num
      have hae_pos : ∀ᵐ σ ∂volume, σ ∈ Ioo (-1 : ℝ) 0 → 0 < f σ * poissonKernel x y σ := by
        have h1 : ∀ᵐ σ ∂(volume.restrict (Ioo (-1 : ℝ) 0)), 0 < f σ :=
          hf_pos.filter_mono (ae_mono (Measure.restrict_mono hIoo_sub le_rfl))
        rw [ae_restrict_iff' measurableSet_Ioo] at h1
        filter_upwards [h1] with σ hσ hm
        exact mul_pos (hσ hm) (poissonKernel_pos (x := x) hy σ)
      by_contra h0
      have hzero : volume ((Function.support fun σ => f σ * poissonKernel x y σ) ∩ slitPreimage) = 0 :=
        nonpos_iff_eq_zero.mp (not_lt.mp h0)
      have hnull1 : ∀ᵐ σ ∂volume, ¬(σ ∈ Ioo (-1 : ℝ) 0 ∧ f σ * poissonKernel x y σ ≠ 0) := by
        rw [← compl_mem_ae_iff] at hzero
        filter_upwards [hzero] with σ hσ ⟨h1, h2⟩
        exact hσ ⟨h2, hIoo_sub h1⟩
      have hsub_empty : ∀ᵐ σ ∂volume, σ ∉ Ioo (-1 : ℝ) 0 := by
        filter_upwards [hae_pos, hnull1] with σ hp hn hm
        exact hn ⟨hm, (hp hm).ne'⟩
      have hv0 : volume (Ioo (-1 : ℝ) 0) = 0 := by
        rw [ae_iff] at hsub_empty
        convert hsub_empty using 2
        ext σ; simp
      exact hIoo_pos.ne' hv0
  set c_avg := I_f / m
  have hc_pos : 0 < c_avg := div_pos hIf_pos hm_pos
  have hlog_bd : ∀ᵐ σ ∂(volume.restrict slitPreimage),
      Real.log (f σ) * poissonKernel x y σ ≤
        (Real.log c_avg - 1) * poissonKernel x y σ + c_avg⁻¹ * (f σ * poissonKernel x y σ) := by
    filter_upwards [hf_pos] with σ hσ
    have h1 : Real.log (f σ / c_avg) ≤ f σ / c_avg - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hσ hc_pos)
    rw [Real.log_div hσ.ne' hc_pos.ne'] at h1
    have h2 : Real.log (f σ) ≤ (Real.log c_avg - 1) + c_avg⁻¹ * f σ := by
      linarith [show f σ / c_avg = c_avg⁻¹ * f σ by ring]
    have hP0 := poissonKernel_nonneg (x := x) hy.le σ
    calc Real.log (f σ) * poissonKernel x y σ
        ≤ ((Real.log c_avg - 1) + c_avg⁻¹ * f σ) * poissonKernel x y σ := by gcongr
      _ = (Real.log c_avg - 1) * poissonKernel x y σ + c_avg⁻¹ * (f σ * poissonKernel x y σ) := by ring
  have hpk_int : IntegrableOn (poissonKernel x y) slitPreimage :=
    (integrable_poissonKernel x hy).integrableOn
  have hrhs_int : IntegrableOn
      (fun σ => (Real.log c_avg - 1) * poissonKernel x y σ + c_avg⁻¹ * (f σ * poissonKernel x y σ))
      slitPreimage := (hpk_int.const_mul _).add (hf_int.const_mul _)
  have hint_mono : ∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x y σ ≤
      ∫ σ in slitPreimage,
        ((Real.log c_avg - 1) * poissonKernel x y σ + c_avg⁻¹ * (f σ * poissonKernel x y σ)) :=
    setIntegral_mono_ae_restrict hlog_int hrhs_int hlog_bd
  have heval : ∫ σ in slitPreimage,
        ((Real.log c_avg - 1) * poissonKernel x y σ + c_avg⁻¹ * (f σ * poissonKernel x y σ)) =
      m * Real.log (I_f / m) := by
    rw [integral_add (hpk_int.const_mul _) (hf_int.const_mul _), integral_const_mul, integral_const_mul]
    change (Real.log c_avg - 1) * m + c_avg⁻¹ * I_f = m * Real.log (I_f / m)
    have hc_eq : c_avg⁻¹ * I_f = m := by dsimp [c_avg]; field_simp [hm_pos.ne', hIf_pos.ne']
    rw [hc_eq]; change (Real.log (I_f / m) - 1) * m + m = m * Real.log (I_f / m); ring
  have hlogm_le : -m * Real.log m ≤ 1 - m := by
    have hm1 : Real.log (1 / m) ≤ 1 / m - 1 := Real.log_le_sub_one_of_pos (one_div_pos.mpr hm_pos)
    rw [one_div, Real.log_inv] at hm1
    have := mul_le_mul_of_nonneg_left hm1 hm_pos.le
    calc -m * Real.log m = m * (-Real.log m) := by ring
      _ ≤ m * (m⁻¹ - 1) := this
      _ = 1 - m := by field_simp [hm_pos.ne']
  calc ∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x y σ
      ≤ m * Real.log (I_f / m) := hint_mono.trans_eq heval
    _ = m * Real.log I_f - m * Real.log m := by rw [Real.log_div hIf_pos.ne' hm_pos.ne']; ring
    _ ≤ m * Real.log B + (1 - m) := by
        have := mul_le_mul_of_nonneg_left (Real.log_le_log hIf_pos hI_le) hm_pos.le
        linarith only [this, hlogm_le]

end FormalResearch.ModularBootstrap.Spin
