module

public import FormalResearch.SignUncertainty.HankelBootMultilevelNodes
public import FormalResearch.Special.AiryCft2ComboBounds

/-!
# Real-Window `(P, Q)` Good Circles and Quadrature-Arc Estimate (`R2c`)

* `airyPQ_good_circle_real`: for `Q ≠ 0`, every real window `[t, t + 1]` (`t ≥ T₀`) contains a
  good circle `r` on which `W² e / (64 π √r) ≤ ‖N‖²` and `‖M/N ∓ i‖ e ≤ 168 √π`.
* `hankelBootMultilevel_arc`: `(P, Q)` quadrature-arc estimate (`(28/5)` scaling of `virasoroArcCov`
  and `hankelArcUncConst`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric Polynomial
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.Special FormalResearch.ModularBootstrap.ConcreteBootstrap

private lemma airyC2_radius_real_exists (t0 : ℝ) (ht : 10 ≤ t0) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ π) :
    ∃ r : ℝ, t0 ≤ r ∧ r ≤ t0 + 1 ∧ ∃ m : ℕ, 2 / 3 * r ^ (3 / 2 : ℝ) = c + m * π := by
  have htpos : (0 : ℝ) < t0 := by linarith
  set G : ℝ := 2 / 3 * t0 ^ (3 / 2 : ℝ) with hG
  have ht32 := airyRpow_three_halves_eq htpos
  have hs3 := airyGC_three_le_sqrt ht
  have hG20 : 20 ≤ G := by rw [hG, ht32]; nlinarith
  have hpi := Real.pi_lt_d2
  have hpipos := Real.pi_pos
  set a : ℝ := (G - c) / π with ha
  have ha0 : 0 ≤ a := by rw [ha]; exact div_nonneg (by linarith) hpipos.le
  set m : ℕ := ⌈a⌉₊ with hm
  have hm1 : a ≤ m := Nat.le_ceil a
  have hm2 : (m : ℝ) < a + 1 := Nat.ceil_lt_add_one ha0
  have hmπ1 : G - c ≤ m * π := by
    have := mul_le_mul_of_nonneg_right hm1 hpipos.le
    rwa [ha, div_mul_cancel₀ _ hpipos.ne'] at this
  have hmπ2 : (m : ℝ) * π < G - c + π := by
    have := mul_lt_mul_of_pos_right hm2 hpipos
    rwa [add_mul, ha, div_mul_cancel₀ _ hpipos.ne', one_mul] at this
  set t : ℝ := c + m * π with ht_def
  have ht0 : 0 ≤ 3 / 2 * t := by positivity
  set r : ℝ := (3 / 2 * t) ^ (2 / 3 : ℝ) with hr
  have hr32 : r ^ (3 / 2 : ℝ) = 3 / 2 * t := by rw [hr, ← Real.rpow_mul ht0]; norm_num
  have hr0 : 0 ≤ r := Real.rpow_nonneg ht0 _
  refine ⟨r, ?_, ?_, m, ?_⟩
  · rw [← Real.rpow_le_rpow_iff htpos.le hr0 (by norm_num : (0 : ℝ) < 3 / 2), hr32]
    rw [hG] at hmπ1; nlinarith
  · have hsucc := airyRpow_three_halves_succ_ge htpos
    have hs3' : π ≤ √t0 := le_trans hpi.le (Real.le_sqrt_of_sq_le (by norm_num; linarith))
    rw [← Real.rpow_le_rpow_iff hr0 (by positivity) (by norm_num : (0 : ℝ) < 3 / 2), hr32]
    rw [hG] at hmπ2; nlinarith
  · rw [hr32]; ring

/-- Real-window good circles `[t, t + 1]` for `N = P Ai + Q Ai'` (`Q ≠ 0`). -/
theorem airyPQ_good_circle_real (P Q : ℝ[X]) (hQ : Q ≠ 0) :
    ∃ T₀ : ℝ, 100 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t → ∃ r : ℝ, t ≤ r ∧ r ≤ t + 1 ∧
      ∀ u : ℂ, ‖u‖ = r → 0 < airyPQW P Q u ∧
        airyPQW P Q u ^ 2 * airyEnv u / (64 * π * √r) ≤ ‖airyPQN P Q u‖ ^ 2 ∧
        (0 ≤ u.im → ‖airyPQM P Q u / airyPQN P Q u - I‖ * airyEnv u ≤ 168 * √π) ∧
        (u.im ≤ 0 → ‖airyPQM P Q u / airyPQN P Q u + I‖ * airyEnv u ≤ 168 * √π) := by
  have hPQ : P ≠ 0 ∨ Q ≠ 0 := Or.inr hQ
  obtain ⟨T, hT1, hT⟩ := airyPQ_dominance P Q
  refine ⟨max T 100, le_max_right _ _, fun t ht => ?_⟩
  have hk100 : (100 : ℝ) ≤ t := (le_max_right _ _).trans ht
  have hkT : T ≤ t := (le_max_left _ _).trans ht
  have hk10 : (10 : ℝ) ≤ t := by linarith
  obtain ⟨c, hc0, hcπ, hdom⟩ : ∃ c : ℝ, 0 ≤ c ∧ c ≤ π ∧ ∀ (r : ℝ) (m : ℕ), 2 / 3 * r ^ (3 / 2 : ℝ) = c + m * π →
      T ≤ r → 25 ≤ r →
      (AiryPQDomP P Q → ∀ ξ : ℂ, 0 ≤ ξ.re → ‖ξ‖ = 2 / 3 * r ^ (3 / 2 : ℝ) →
        Real.exp |ξ.im| / 4 ≤ ‖Complex.cos (ξ - (π / 4 : ℂ))‖) ∧
      (AiryPQDomQ P Q → ∀ ξ : ℂ, 0 ≤ ξ.re → ‖ξ‖ = 2 / 3 * r ^ (3 / 2 : ℝ) →
        Real.exp |ξ.im| / 4 ≤ ‖Complex.sin (ξ - (π / 4 : ℂ))‖) := by
    rcases airyPQ_domP_or_domQ P Q hPQ with hP | hQ'
    · refine ⟨π / 4, by positivity, by linarith [Real.pi_pos], fun r m hm hrT hr25 => ⟨fun _ ξ hre hξ => ?_, fun hq => ?_⟩⟩
      · refine airyPQ_cos_good hre ?_ m (by rw [hξ, hm])
        rw [hξ]
        have hr32 := airyRpow_three_halves_eq (by linarith : 0 < r)
        have : 5 ≤ √r := Real.le_sqrt_of_sq_le (by nlinarith)
        rw [hr32]; nlinarith
      · exact absurd ⟨hP, hq⟩ (airyPQ_not_domP_domQ P Q)
    · refine ⟨3 * π / 4, by positivity, by linarith [Real.pi_pos], fun r m hm hrT hr25 => ⟨fun hp => ?_, fun _ ξ hre hξ => ?_⟩⟩
      · exact absurd ⟨hp, hQ'⟩ (airyPQ_not_domP_domQ P Q)
      · exact airyC2_sin_good hre m (by rw [hξ, hm])
  obtain ⟨r, hr1, hr2, m, hm⟩ := airyC2_radius_real_exists t hk10 hc0 hcπ
  have hrT : T ≤ r := hkT.trans hr1
  have hr100 : (100 : ℝ) ≤ r := hk100.trans hr1
  have hrpos : 0 < r := by linarith
  have hsr : 10 ≤ √r := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsr0 : 0 < √r := by linarith
  have hD := hdom r m hm hrT (by linarith)
  refine ⟨r, hr1, hr2, fun u hu => ?_⟩
  have hlow : ∀ v : ℂ, ‖v‖ = r →
      airyPQW P Q v ^ 2 * airyEnv v / (64 * π * √r) ≤ ‖airyPQN P Q v‖ ^ 2 := by
    intro v hv
    obtain ⟨hdP, hdQ⟩ := hT v (by rw [hv]; exact hrT)
    have hdom' : 16 * ‖airyPQc Q v‖ * √‖v‖ ≤ ‖airyPQc P v‖ ∨ 16 * ‖airyPQc P v‖ ≤ ‖airyPQc Q v‖ * √‖v‖ := by
      rcases airyPQ_domP_or_domQ P Q hPQ with h | h
      · exact Or.inl (hdP h).1
      · exact Or.inr (hdQ h).1
    have hW : airyPQW P Q v = max ‖airyPQc P v‖ (‖airyPQc Q v‖ * √‖v‖) := rfl
    by_cases hcase : -(‖v‖ / 2) ≤ v.re
    · have := airyAB_sector_ge (airyPQc P v) (airyPQc Q v) hcase (by rw [hv]; linarith) hdom'
      rw [hv] at this hW; rw [hW]
      refine le_trans ?_ this
      have hh : 0 ≤ max ‖airyPQc P v‖ (‖airyPQc Q v‖ * √r) ^ 2 * airyEnv v := by
        have := airyEnv_pos v; positivity
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg hh (mul_nonneg Real.pi_pos.le hsr0.le)]
    · have hlt : v.re < -(‖v‖ / 2) := not_le.mp hcase
      set q : ℂ := (-v) ^ (1 / 2 : ℂ) with hqdef
      have hq : NegSector q := NegSector_of_re_lt hlt
      have hq2 : q ^ 2 = -v := cpow_half_sq _
      have hqn : ‖q‖ ^ 2 = r := by rw [hqdef, norm_cpow_half_sq, norm_neg, hv]
      have hq3 : ‖q‖ ^ 3 = r ^ (3 / 2 : ℝ) := by
        rw [hqdef, airyNorm_cpow_half_pow_three, norm_neg, hv]
      have hqs : ‖q‖ = √r := by rw [← hqn, Real.sqrt_sq (norm_nonneg _)]
      have hξre : 0 ≤ ((2 / 3 : ℂ) * q ^ 3).re := by
        have h1 := hq.re_sq_ge; have h0 := hq.re_nonneg
        have : ((2 / 3 : ℂ) * q ^ 3).re = 2 / 3 * (q.re * (q.re ^ 2 - 3 * q.im ^ 2)) := by
          simp [Complex.mul_re, re_cube]; ring
        rw [this]
        have : 0 ≤ q.re * (q.re ^ 2 - 3 * q.im ^ 2) := mul_nonneg h0 (by linarith)
        positivity
      have hnξ : ‖(2 / 3 : ℂ) * q ^ 3‖ = 2 / 3 * r ^ (3 / 2 : ℝ) := by
        rw [norm_mul, norm_pow, hq3]; norm_num
      have hsq5 : 5 ≤ ‖q‖ := by rw [hqs]; linarith
      have hdom2 : (Real.exp |((2 / 3 : ℂ) * q ^ 3).im| / 4 ≤ ‖Complex.cos ((2 / 3 : ℂ) * q ^ 3 - (π / 4 : ℂ))‖ ∧
          16 * ‖airyPQc Q v‖ * ‖q‖ ≤ ‖airyPQc P v‖) ∨
          (Real.exp |((2 / 3 : ℂ) * q ^ 3).im| / 4 ≤ ‖Complex.sin ((2 / 3 : ℂ) * q ^ 3 - (π / 4 : ℂ))‖ ∧
          16 * ‖airyPQc P v‖ ≤ ‖airyPQc Q v‖ * ‖q‖) := by
        rw [hqs, ← hv]
        rcases airyPQ_domP_or_domQ P Q hPQ with h | h
        · exact Or.inl ⟨(hD.1 h) _ hξre (by rw [hnξ]), (hdP h).1⟩
        · exact Or.inr ⟨(hD.2 h) _ hξre (by rw [hnξ]), (hdQ h).1⟩
      have := airyAB_neg_sq_ge (airyPQc P v) (airyPQc Q v) hq hsq5 hdom2
      have e : -(q ^ 2) = v := by rw [hq2, neg_neg]
      rw [e, hqs] at this
      have hW' : airyPQW P Q v = max ‖airyPQc P v‖ (‖airyPQc Q v‖ * √r) := by rw [airyPQW, hv]
      rw [hW']; refine le_trans (le_of_eq ?_) this; ring
  have hWposAll : ∀ v : ℂ, ‖v‖ = r → 0 < airyPQW P Q v := fun v hv => by
    obtain ⟨hdP, hdQ⟩ := hT v (by rw [hv]; exact hrT)
    rcases airyPQ_domP_or_domQ P Q hPQ with h | h
    · exact lt_of_lt_of_le (hdP h).2.2 (le_max_left _ _)
    · exact lt_of_lt_of_le (mul_pos (hdQ h).2.2 (by rw [hv]; exact hsr0)) (le_max_right _ _)
  have hup : ∀ v : ℂ, ‖v‖ = r → 0 ≤ v.im →
      ‖airyPQM P Q v / airyPQN P Q v - I‖ * airyEnv v ≤ 168 * √π := fun v hv hvi => by
    have hLv := hlow v hv
    have hen := airyEnv_pos v
    have hWpos := hWposAll v hv
    have hN2 : 0 < ‖airyPQN P Q v‖ ^ 2 := lt_of_lt_of_le (by positivity) hLv
    have hN : 0 < ‖airyPQN P Q v‖ := by
      rcases (norm_nonneg (airyPQN P Q v)).lt_or_eq with h | h
      · exact h
      · rw [← h] at hN2; simp at hN2
    have hnum := airyPQ_num_le P Q hvi (by rw [hv]; linarith)
    rw [hv] at hnum
    have hN0 : airyPQN P Q v ≠ 0 := norm_ne_zero_iff.mp hN.ne'
    have e : airyPQM P Q v / airyPQN P Q v - I = (airyPQM P Q v - I * airyPQN P Q v) / airyPQN P Q v := by
      field_simp [hN0]
    rw [e, norm_div]
    exact airyPQ_ratio_le hN hen hsr0 hnum hLv (norm_nonneg _)
  refine ⟨hWposAll u hu, hlow u hu, fun hi => hup u hu hi, fun hi => ?_⟩
  have h := hup ((starRingEnd ℂ) u) (by rw [Complex.norm_conj, hu]) (by simpa using hi)
  have e : ‖airyPQM P Q u / airyPQN P Q u + I‖ =
      ‖airyPQM P Q ((starRingEnd ℂ) u) / airyPQN P Q ((starRingEnd ℂ) u) - I‖ := by
    have : airyPQM P Q ((starRingEnd ℂ) u) / airyPQN P Q ((starRingEnd ℂ) u) - I =
        (starRingEnd ℂ) (airyPQM P Q u / airyPQN P Q u + I) := by
      rw [map_add, map_div₀, conj_airyPQM, conj_airyPQN, Complex.conj_I]; ring
    rw [this, Complex.norm_conj]
  rw [e, ← airyEnv_conj u]; exact h

/-- `(P, Q)` quadrature and arc estimate (`hP_le`, `hArc_cov`, `hArc_unc`) for `D : ShellHBData`
with `D.Q ≠ 0`, `k ≥ 9`: `(28 / 5)` scaling of `virasoroArcCov` and `hankelArcUncConst`. -/
theorem hankelBootMultilevel_arc (D : ShellHBData) (hQ : D.Q ≠ 0) {c ε R L' ℓ : ℝ} {f : ℝ → ℝ}
    (hc : 3e6 ≤ c) (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1)
    (hc12 : (3 * π) ^ (12 : ℕ) ≤ c) (hR10 : 10 ≤ R) (hRA : R + 1 ≤ langerRadius c)
    (hRc : R ≤ c ^ (2 / 3 : ℝ)) (hL' : 0 ≤ L') (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1 / 2)
    (hYV : YVEnvBound (hankelPsi c f) c R L')
    (hR_low : ∀ u : ℂ, ‖u‖ = R → 0 < airyPQW D.P D.Q u ∧
      airyPQW D.P D.Q u ^ 2 * airyEnv u / (64 * π * √R) ≤ ‖airyPQN D.P D.Q u‖ ^ 2 ∧
      (0 ≤ u.im → ‖airyPQM D.P D.Q u / airyPQN D.P D.Q u - I‖ * airyEnv u ≤ 168 * √π) ∧
      (u.im ≤ 0 → ‖airyPQM D.P D.Q u / airyPQN D.P D.Q u + I‖ * airyEnv u ≤ 168 * √π))
    {k : ℕ} (hk9 : 9 ≤ k) :
    hankelBootMultilevelNodes D c f R ℓ k ≤
      (∫ x in (-R)..R, (hankelBootShifted c f R ℓ k (x : ℂ)).re) +
        (28 / 5 : ℝ) * virasoroArcCov c R 0 L' ℓ (fun _ => 0) k +
        ((28 / 5 : ℝ) * hankelArcUncConst) * c ^ (-(3 / 8 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hR_pos : 0 < R := by linarith
  have hk5 : 5 ≤ k := by omega
  have hR_pow := hankelBoot_R_pow_le hc0 hR_pos hRc
  set F : ℂ → ℂ := hankelBootShifted c f R ℓ k with hF_def
  set δ₀ : ℝ := 3 * π * c ^ (-(1 / 12 : ℝ)) with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := by rw [hδ₀_def]; positivity
  have hδ₀_le_1 : δ₀ ≤ 1 := by
    have h_rpow : 3 * π ≤ c ^ (1 / 12 : ℝ) := by
      have h3pi_nn : 0 ≤ 3 * π := by positivity
      calc 3 * π = ((3 * π) ^ (12 : ℕ)) ^ (1 / 12 : ℝ) := by
            rw [← Real.rpow_natCast (3 * π) 12, ← Real.rpow_mul h3pi_nn]; norm_num
        _ ≤ c ^ (1 / 12 : ℝ) := Real.rpow_le_rpow (by positivity) hc12 (by positivity)
    calc δ₀ = 3 * π * (c ^ (1 / 12 : ℝ))⁻¹ := by
          rw [hδ₀_def, Real.rpow_neg hc0.le, mul_assoc]
      _ = 3 * π / c ^ (1 / 12 : ℝ) := (div_eq_mul_inv _ _).symm
      _ ≤ 1 := (div_le_one (Real.rpow_pos_of_pos hc0 _)).mpr h_rpow
  have hδ_pow : δ₀ * δ₀ ^ ((k : ℝ) + 1 / 2) ≤ (3 * π) ^ (21 / 2 : ℝ) * c ^ (-(7 / 8 : ℝ)) := by
    have hx : δ₀ * δ₀ ^ ((k : ℝ) + 1 / 2) = δ₀ ^ ((1 : ℝ) + ((k : ℝ) + 1 / 2)) := by
      rw [Real.rpow_add hδ₀_pos (1 : ℝ) ((k : ℝ) + 1 / 2), Real.rpow_one]
    have hk' : (21 / 2 : ℝ) ≤ 1 + ((k : ℝ) + 1 / 2) := by
      have : (9 : ℝ) ≤ k := by exact_mod_cast hk9
      linarith
    have h1 : δ₀ ^ ((1 : ℝ) + ((k : ℝ) + 1 / 2)) ≤ δ₀ ^ (21 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hδ₀_pos hδ₀_le_1 hk'
    have h2 : δ₀ ^ (21 / 2 : ℝ) = (3 * π) ^ (21 / 2 : ℝ) * c ^ (-(7 / 8 : ℝ)) := by
      rw [hδ₀_def, Real.mul_rpow (by positivity) (Real.rpow_nonneg hc0.le _),
        ← Real.rpow_mul hc0.le]
      norm_num
    rw [hx]; exact h1.trans h2.le
  have hf_diff : DifferentiableOn ℂ F (ball (0 : ℂ) (R + 1 / 3)) := by
    intro u hu
    have hu_shift : u + (ℓ : ℂ) ∈ closedBall (0 : ℂ) (langerRadius c) := by
      rw [mem_closedBall_zero_iff]; rw [mem_ball_zero_iff] at hu
      calc ‖u + (ℓ : ℂ)‖ ≤ ‖u‖ + ‖(ℓ : ℂ)‖ := norm_add_le _ _
        _ ≤ (R + 1 / 3) + ℓ := by rw [Complex.norm_real, Real.norm_of_nonneg hℓ0]; linarith
        _ ≤ R + 1 := by linarith
        _ ≤ langerRadius c := hRA
    have hPsi_at : AnalyticAt ℂ (hankelPsi c f) (u + (ℓ : ℂ)) :=
      analyticOnNhd_hankelPsi hc0 hf _ hu_shift
    have h1 : DifferentiableAt ℂ (fun z : ℂ => hankelPsi c f (z + (ℓ : ℂ))) u :=
      DifferentiableAt.comp (g := hankelPsi c f) (f := fun z : ℂ => z + (ℓ : ℂ)) u
        hPsi_at.differentiableAt (by fun_prop)
    have h2 : DifferentiableAt ℂ (fun z : ℂ => (1 + z / (R : ℂ)) ^ (k + 1)) u :=
      ((differentiableAt_const _).add (differentiableAt_id.div_const _)).pow _
    exact (h1.mul h2).differentiableWithinAt
  set a : ℝ := √R with ha_def
  have ha_pos : 0 < a := Real.sqrt_pos.mpr hR_pos
  set M_c : ℝ := 2 ^ (3 / 4 : ℝ) * L' * a ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1) with hM_c_def
  have hM_c_nn : 0 ≤ M_c := by rw [hM_c_def]; positivity
  let B_cov : ℝ → ℝ := fun θ =>
    M_c * ((π - |θ|) / 2) ^ ((k : ℝ) - 1 / 2) * Real.exp (-(4 * ℓ * a / π) * ((π - |θ|) / 2))
  set M_unc : ℝ := 60 * (2 : ℝ) ^ (k + 1) * a ^ (-(1 / 2 : ℝ)) * (δ₀ / 2) ^ ((k : ℝ) + 1 / 2)
    with hM_unc_def
  have hM_unc_nn : 0 ≤ M_unc := by
    rw [hM_unc_def]
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg ha_pos.le _))
      (Real.rpow_nonneg (by linarith) _)
  let W_unc : Set ℝ := {θ : ℝ | π - δ₀ < |θ|}
  have hW_meas : MeasurableSet W_unc := measurableSet_lt measurable_const continuous_abs.measurable
  let B_unc : ℝ → ℝ := W_unc.indicator (fun _ => M_unc)
  let B : ℝ → ℝ := fun θ => B_cov θ + B_unc θ
  have hk_half_pos : (0 : ℝ) < (k : ℝ) - 1 / 2 := by
    have : (5 : ℝ) ≤ k := by exact_mod_cast hk5
    linarith
  have hB_cov_cont : ContinuousOn B_cov (Icc (-π) π) := fun θ _ =>
    Continuous.continuousWithinAt <|
      (continuous_const.mul ((Continuous.rpow_const ((continuous_const.sub continuous_abs).div_const 2)
        (fun _ => Or.inr hk_half_pos.le)))).mul
      (Real.continuous_exp.comp (continuous_const.mul ((continuous_const.sub continuous_abs).div_const 2)))
  have hB_cov_int : IntervalIntegrable B_cov volume (-π) π :=
    hB_cov_cont.intervalIntegrable_of_Icc (by linarith [Real.pi_pos])
  have hB_unc_int : IntervalIntegrable B_unc volume (-π) π := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])]
    exact ((continuousOn_const (c := M_unc)).integrableOn_Icc.mono_set Ioc_subset_Icc_self).indicator hW_meas
  have hB_int : IntervalIntegrable B volume (-π) π := hB_cov_int.add hB_unc_int
  have hB_bd : ∀ θ ∈ Icc (-π) π, ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) ≤ B θ := by
    intro θ hθ
    have hB_cov_nn : 0 ≤ B_cov θ := by
      dsimp [B_cov]
      exact mul_nonneg (mul_nonneg hM_c_nn (Real.rpow_nonneg (by linarith [abs_le.mpr hθ]) _))
        (Real.exp_pos _).le
    have hB_unc_nn : 0 ≤ B_unc θ := by
      dsimp [B_unc]; by_cases h : θ ∈ W_unc <;> simp [h, hM_unc_nn]
    have he_pos : 0 < airyEnv (circleMap 0 R θ) := airyEnv_pos _
    rw [div_le_iff₀ he_pos]
    have h1w : ‖1 + circleMap 0 R θ / (R : ℂ)‖ = 2 * Real.cos (θ / 2) :=
      norm_one_add_circleMap_div hR_pos hθ
    by_cases hpi : |θ| = π
    · have hcos0 : Real.cos (θ / 2) = 0 := by
        rcases abs_eq Real.pi_pos.le |>.mp hpi with rfl | rfl
        · simp [Real.cos_pi_div_two]
        · simp [neg_div, Real.cos_neg, Real.cos_pi_div_two]
      have hpow0 : ‖(1 + circleMap 0 R θ / (R : ℂ)) ^ (k + 1)‖ = 0 := by
        rw [norm_pow, h1w, hcos0, mul_zero, zero_pow (Nat.succ_ne_zero k)]
      have hf0 : ‖F (circleMap 0 R θ)‖ = 0 := by
        dsimp only [F, hankelBootShifted]; rw [norm_mul, hpow0, mul_zero]
      rw [hf0]
      exact mul_nonneg (add_nonneg hB_cov_nn hB_unc_nn) he_pos.le
    · have h_abs_lt : |θ| < π := lt_of_le_of_ne (abs_le.mpr hθ) hpi
      by_cases hcov : |θ| ≤ π - δ₀
      · have h_pt := hankelBoot_cov_pt hc0 hf hR10 hRA hL' hℓ0 hℓ1 hYV hk5 hθ h_abs_lt
          (by rw [hδ₀_def] at hcov; exact hcov)
        have h1 : B_cov θ * airyEnv (circleMap 0 R θ) ≤ B θ * airyEnv (circleMap 0 R θ) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB_unc_nn) he_pos.le
        exact h_pt.trans h1
      · push Not at hcov
        have hB_unc_eq : B_unc θ = M_unc := Set.indicator_of_mem (show θ ∈ W_unc from hcov) _
        have h_pt := hankelBoot_unc_pt hc hf hε hM hR10 hRA hℓ0 hℓ1 k hθ h_abs_lt
          (by rw [hδ₀_def] at hcov; exact hcov)
        have h1 : M_unc * airyEnv (circleMap 0 R θ) ≤ B θ * airyEnv (circleMap 0 R θ) := by
          rw [← hB_unc_eq]
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB_cov_nn) he_pos.le
        exact h_pt.trans h1
  have hN_sphere : ∀ u : ℂ, ‖u‖ = R → airyPQN D.P D.Q u ≠ 0 := fun u hu h0 => by
    obtain ⟨hWpos, hWlow, _, _⟩ := hR_low u hu
    rw [h0, norm_zero, zero_pow (by decide)] at hWlow
    have hpos : 0 < airyPQW D.P D.Q u ^ 2 * airyEnv u / (64 * π * √R) :=
      div_pos (mul_pos (sq_pos_of_pos hWpos) (airyEnv_pos u)) (mul_pos (by positivity) ha_pos)
    linarith
  have hin : ∀ z ∈ hbZerosInDisc D R, ‖z‖ < R := fun z hz => by
    obtain ⟨h0, h1⟩ := (mem_hbZerosInDisc D).mp hz
    exact lt_of_le_of_ne h1 fun heq => hN_sphere z heq h0
  have hder : ∀ z ∈ hbZerosInDisc D R, deriv (airyPQN D.P D.Q) z ≠ 0 := fun z hz => by
    obtain ⟨h0, _⟩ := (mem_hbZerosInDisc D).mp hz
    have hzr := airyPQ_zero_eq_ofReal D.hHB h0
    rw [deriv_airyPQN, hzr]
    exact (airyPQ_zero_weight_pos D.hHB hQ (hzr ▸ h0)).2
  obtain ⟨c_seq, s_fin, hCircle, hsum_eq⟩ := cft2_circleData_of_finset
    (differentiable_airyPQN D.P D.Q) hR_pos (hbZerosInDisc D R) hin
    (fun z hz => ((mem_hbZerosInDisc D).mp hz).1) hder
    (fun w hw h0 => (mem_hbZerosInDisc D).mpr ⟨h0, hw⟩)
  have h_def := cft2_defect_ball_split hCircle (differentiable_airyPQM D.P D.Q)
    (by linarith : R < R + 1 / 3) hf_diff airyEnv_pos
    (fun w hw him => (hR_low w hw).2.2.1 him) (fun w hw him => (hR_low w hw).2.2.2 him)
    hB_int hB_bd
  have hsum_pq : (-(π : ℂ)) * (∑ i ∈ s_fin, F (c_seq i) * airyPQM D.P D.Q (c_seq i) /
        deriv (airyPQN D.P D.Q) (c_seq i)) =
      ∑ z ∈ hbZerosInDisc D R, F z * (airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2) := by
    rw [hsum_eq (fun z => F z * airyPQM D.P D.Q z / deriv (airyPQN D.P D.Q) z), Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    obtain ⟨hz0, _⟩ := (mem_hbZerosInDisc D).mp hz
    have hd := hder z hz
    rw [deriv_airyPQN] at hd ⊢
    rw [← airyPQ_weight_eq D.P D.Q hz0 hd]
    ring
  have h_nodes_re : (∑ z ∈ hbZerosInDisc D R,
      F z * (airyPQD D.P D.Q z / airyPQN' D.P D.Q z ^ 2)).re =
      hankelBootMultilevelNodes D c f R ℓ k := by
    unfold hankelBootMultilevelNodes; exact Complex.re_sum _ _
  have h_int_eq : (∫ x in (-R)..R, F (x : ℂ)).re = ∫ x in (-R)..R, (F (x : ℂ)).re := by
    have hf_cont_R : ContinuousOn (fun x : ℝ => F (x : ℂ)) (Icc (-R) R) := by
      refine hf_diff.continuousOn.comp continuous_ofReal.continuousOn fun x hx => ?_
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact (abs_le.mpr hx).trans_lt (by linarith)
    exact (Complex.reCLM.intervalIntegral_comp_comm (hf_cont_R.intervalIntegrable_of_Icc (by linarith))).symm
  rw [hsum_pq] at h_def
  have h_quad_re : hankelBootMultilevelNodes D c f R ℓ k - (∫ x in (-R)..R, (F (x : ℂ)).re) ≤
      (84 * √π * R) * ∫ θ in (-π)..π, B θ := by
    have hre := (Complex.abs_re_le_norm _).trans h_def
    rw [Complex.sub_re, h_nodes_re, h_int_eq] at hre
    have h84 : 168 * √π / 2 * R = 84 * √π * R := by ring
    linarith [(abs_le.mp hre).2, h84]
  have h_unc_int : (84 * √π * R) * ∫ θ in (-π)..π, B_unc θ ≤
      ((28 / 5 : ℝ) * hankelArcUncConst) * c ^ (-(3 / 8 : ℝ)) := by
    have h_meas_le : ∫ θ in (-π)..π, B_unc θ ≤ 4 * δ₀ * M_unc := by
      let J₁ := Icc (-π) (-(π - δ₀))
      let J₂ := Icc (π - δ₀) π
      have h_sub_W : W_unc ∩ Ioc (-π) π ⊆ J₁ ∪ J₂ := by
        intro θ ⟨hW, hIoc⟩
        rcases le_total θ 0 with h0 | h0
        · left; refine ⟨hIoc.1.le, ?_⟩
          have : |θ| = -θ := abs_of_nonpos h0
          rw [Set.mem_ofPred_eq, this] at hW; linarith
        · right; refine ⟨?_, hIoc.2⟩
          have : |θ| = θ := abs_of_nonneg h0
          rw [Set.mem_ofPred_eq, this] at hW; linarith
      rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
      have h_ind_eq : ∫ θ in Ioc (-π) π, B_unc θ = M_unc * (volume (W_unc ∩ Ioc (-π) π)).toReal := by
        dsimp [B_unc]
        rw [setIntegral_indicator hW_meas, setIntegral_const, smul_eq_mul, Measure.real_def, Set.inter_comm]
        ring
      have h_vol : (volume (W_unc ∩ Ioc (-π) π)).toReal ≤ 4 * δ₀ := by
        have hm1 : volume (W_unc ∩ Ioc (-π) π) ≤ volume (J₁ ∪ J₂) := measure_mono h_sub_W
        have hm2 : volume (J₁ ∪ J₂) ≤ volume J₁ + volume J₂ := measure_union_le J₁ J₂
        have hJ1 : volume J₁ = ENNReal.ofReal δ₀ := by dsimp [J₁]; rw [Real.volume_Icc]; congr 1; ring
        have hJ2 : volume J₂ = ENNReal.ofReal δ₀ := by dsimp [J₂]; rw [Real.volume_Icc]; congr 1; ring
        have hlt : volume (W_unc ∩ Ioc (-π) π) ≤ ENNReal.ofReal (4 * δ₀) := by
          calc volume (W_unc ∩ Ioc (-π) π) ≤ ENNReal.ofReal δ₀ + ENNReal.ofReal δ₀ := by
                exact hm1.trans (hm2.trans_eq (by rw [hJ1, hJ2]))
            _ = ENNReal.ofReal (2 * δ₀) := by
                rw [← ENNReal.ofReal_add hδ₀_pos.le hδ₀_pos.le, two_mul]
            _ ≤ ENNReal.ofReal (4 * δ₀) := ENNReal.ofReal_le_ofReal (by linarith)
        exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlt
      rw [h_ind_eq]
      nlinarith [mul_le_mul_of_nonneg_left h_vol hM_unc_nn]
    have hC_nn : 0 ≤ 84 * √π * 4 * 60 * √2 := by positivity
    have hpos84 : 0 ≤ 84 * √π * R := by positivity
    have hM_eq : M_unc = 60 * a ^ (-(1 / 2 : ℝ)) * (√2 * δ₀ ^ ((k : ℝ) + 1 / 2)) := by
      rw [hM_unc_def, ← hankelBoot_two_pow_half δ₀ hδ₀_pos k]; ring
    calc (84 * √π * R) * ∫ θ in (-π)..π, B_unc θ
        ≤ (84 * √π * R) * (4 * δ₀ * M_unc) := mul_le_mul_of_nonneg_left h_meas_le hpos84
      _ = (84 * √π * 4 * 60 * √2) * (R * a ^ (-(1 / 2 : ℝ))) * (δ₀ * δ₀ ^ ((k : ℝ) + 1 / 2)) := by
          rw [hM_eq]; ring
      _ ≤ (84 * √π * 4 * 60 * √2) * c ^ (1 / 2 : ℝ) * ((3 * π) ^ (21 / 2 : ℝ) * c ^ (-(7 / 8 : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hR_pow hC_nn) hδ_pow
            (mul_nonneg hδ₀_pos.le (Real.rpow_nonneg hδ₀_pos.le _))
            (mul_nonneg hC_nn (Real.rpow_nonneg hc0.le _))
      _ = ((28 / 5 : ℝ) * hankelArcUncConst) * c ^ (-(3 / 8 : ℝ)) := by
          have hc_exp : c ^ (1 / 2 : ℝ) * c ^ (-(7 / 8 : ℝ)) = c ^ (-(3 / 8 : ℝ)) := by
            rw [← Real.rpow_add hc0]; norm_num
          unfold hankelArcUncConst
          rw [← hc_exp]; ring
  have hB_split : ∫ θ in (-π)..π, B θ =
      (∫ θ in (-π)..π, B_cov θ) + ∫ θ in (-π)..π, B_unc θ :=
    intervalIntegral.integral_add hB_cov_int hB_unc_int
  have h_cov_eq : (84 * √π * R) * ∫ θ in (-π)..π, B_cov θ =
      (28 / 5 : ℝ) * virasoroArcCov c R 0 L' ℓ (fun _ => 0) k := by
    unfold virasoroArcCov
    dsimp only
    have hint_eq : ∫ θ in (-π)..π, B_cov θ = ∫ θ in (-π)..π,
        (2 ^ (3 / 4 : ℝ) * L' * a ^ (-(3 : ℤ)) * (2 : ℝ) ^ (k + 1)) *
          ((π - |θ|) / 2) ^ ((k : ℝ) - 1 / 2) *
          Real.exp (-(4 * ℓ * a / π) * ((π - |θ|) / 2)) := rfl
    rw [hint_eq]
    have hmul_out : (84 * √π * R) = (28 / 5 : ℝ) * (15 * √π * R) := by ring
    rw [hmul_out, mul_assoc]
  rw [hB_split, mul_add] at h_quad_re
  linarith only [h_quad_re, h_cov_eq, h_unc_int]

/-- info: 'FormalResearch.SignUncertainty.airyPQ_good_circle_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyPQ_good_circle_real

/-- info: 'FormalResearch.SignUncertainty.hankelBootMultilevel_arc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBootMultilevel_arc

end FormalResearch.SignUncertainty
