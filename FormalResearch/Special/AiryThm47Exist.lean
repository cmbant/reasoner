module

public import FormalResearch.Special.AiryThm47Uniq

/-!
# Theorem 4.7, existence half (`SOFT_EDGE_THEOREMS.md`, Theorem 4.7, admissibility of the extremal)

`at47_existence`: for a set `S` of `m = at47_m P Q` zeros of `N = P Ai + Q Ai'` (`(P, Q)` Hermite-Biehler, `Q ≠ 0`), the function
`F = (-1)^m N²/∏_{t∈S}(u - t)` is entire (`at47_div_finset`), has the class bound `C (1+|u|)^ν e(u)` (`at47_N_class`), decays like
`|x|^{-3/2}` at `-∞` (`at47_Nf_neg_sq`, `at47_F_neg_decay`: `N(-s)² ≲ s^e √s`, `|∏| ≳ s^m`, `m = e + 2`) and super-polynomially
at `+∞` (`at47_F_pos_decay`), so it is integrable; it vanishes on `S`, is `≥ 0` on `(-∞, min S]`, and `∫F = 0` by the quadrature
`airyPQ_hasSum_unc` (all terms vanish).  `at47_no_admissible_above`: with `at47_uniqueness`, an admissible `f` with `um > tm` is zero,
so `sup um = tm`.  All proved.  Not formalised: existence of the ordered `m` largest zeros (`S` is a hypothesis).
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

lemma at47_cpoly_norm_le (q : ℝ[X]) (u : ℂ) :
    ‖airyPQc q u‖ ≤ (∑ k ∈ Finset.range (q.natDegree + 1), |q.coeff k|) * (1 + ‖u‖) ^ q.natDegree := by
  rw [airyPQc_eq_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hk' : k ≤ q.natDegree := by have := Finset.mem_range.mp hk; omega
  gcongr
  calc ‖u‖ ^ k ≤ (1 + ‖u‖) ^ k := by gcongr; linarith
    _ ≤ (1 + ‖u‖) ^ q.natDegree := pow_le_pow_right₀ (by linarith [norm_nonneg u]) hk'

/-- Global class bound for `N²`: `‖N(u)²‖ ≤ C (1+|u|)^ν e(u)`. -/
lemma at47_N_class (P Q : ℝ[X]) :
    ∃ C ν : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖airyPQN P Q u ^ 2‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u := by
  set BP := ∑ k ∈ Finset.range (P.natDegree + 1), |P.coeff k| with hBP
  set BQ := ∑ k ∈ Finset.range (Q.natDegree + 1), |Q.coeff k| with hBQ
  have hBP0 : 0 ≤ BP := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hBQ0 : 0 ≤ BQ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set D : ℕ := max P.natDegree Q.natDegree with hD
  refine ⟨2 * (BP ^ 2 * 9 + BQ ^ 2 * 25), 2 * D + 1 / 2, by positivity, fun u => ?_⟩
  set x : ℝ := 1 + ‖u‖ with hx
  have hx1 : 1 ≤ x := by linarith [norm_nonneg u]
  have hx0 : 0 < x := by linarith
  have hpP : ‖airyPQc P u‖ ≤ BP * x ^ D :=
    (at47_cpoly_norm_le P u).trans (by gcongr; exact le_max_left _ _)
  have hpQ : ‖airyPQc Q u‖ ≤ BQ * x ^ D :=
    (at47_cpoly_norm_le Q u).trans (by gcongr; exact le_max_right _ _)
  have hA := airyAiC_norm_sq_le u
  have hB := at47_airyAiC_deriv_norm_sq_le u
  have hen := airyEnv_pos u
  have hneg : x ^ (-(1 / 2) : ℝ) ≤ x ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hA' : ‖airyAiC u‖ ^ 2 ≤ 9 * x ^ (1 / 2 : ℝ) * airyEnv u := by
    refine hA.trans ?_
    gcongr
  have hexp : (x ^ D) ^ 2 * x ^ (1 / 2 : ℝ) = x ^ (2 * D + 1 / 2 : ℝ) := by
    rw [Real.rpow_add hx0, ← pow_mul, mul_comm D 2]
    have : x ^ (2 * (D : ℝ)) = x ^ (2 * D) := by
      rw [show (2 * (D : ℝ)) = ((2 * D : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [this]
  have hN : ‖airyPQN P Q u‖ ≤ ‖airyPQc P u‖ * ‖airyAiC u‖ + ‖airyPQc Q u‖ * ‖deriv airyAiC u‖ := by
    unfold airyPQN
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
  rw [norm_pow]
  have h1 : ‖airyPQN P Q u‖ ^ 2 ≤ 2 * (‖airyPQc P u‖ ^ 2 * ‖airyAiC u‖ ^ 2 + ‖airyPQc Q u‖ ^ 2 * ‖deriv airyAiC u‖ ^ 2) := by
    have h0 := norm_nonneg (airyPQN P Q u)
    calc ‖airyPQN P Q u‖ ^ 2 ≤ (‖airyPQc P u‖ * ‖airyAiC u‖ + ‖airyPQc Q u‖ * ‖deriv airyAiC u‖) ^ 2 :=
          pow_le_pow_left₀ h0 hN 2
      _ ≤ _ := by nlinarith [sq_nonneg (‖airyPQc P u‖ * ‖airyAiC u‖ - ‖airyPQc Q u‖ * ‖deriv airyAiC u‖)]
  have h2 : ‖airyPQc P u‖ ^ 2 * ‖airyAiC u‖ ^ 2 ≤ BP ^ 2 * (x ^ D) ^ 2 * (9 * x ^ (1 / 2 : ℝ) * airyEnv u) := by
    have : ‖airyPQc P u‖ ^ 2 ≤ BP ^ 2 * (x ^ D) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hpP 2
    exact mul_le_mul this hA' (sq_nonneg _) (by positivity)
  have h3 : ‖airyPQc Q u‖ ^ 2 * ‖deriv airyAiC u‖ ^ 2 ≤ BQ ^ 2 * (x ^ D) ^ 2 * (25 * x ^ (1 / 2 : ℝ) * airyEnv u) := by
    have : ‖airyPQc Q u‖ ^ 2 ≤ BQ ^ 2 * (x ^ D) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hpQ 2
    exact mul_le_mul this hB (sq_nonneg _) (by positivity)
  calc ‖airyPQN P Q u‖ ^ 2 ≤ 2 * (BP ^ 2 * (x ^ D) ^ 2 * (9 * x ^ (1 / 2 : ℝ) * airyEnv u) +
        BQ ^ 2 * (x ^ D) ^ 2 * (25 * x ^ (1 / 2 : ℝ) * airyEnv u)) := by linarith
    _ = 2 * (BP ^ 2 * 9 + BQ ^ 2 * 25) * ((x ^ D) ^ 2 * x ^ (1 / 2 : ℝ)) * airyEnv u := by ring
    _ = _ := by rw [hexp]

/-- Integrability on `ℝ` from `|x|^{-3/2}` decay at `-∞` and `x^{-2}` decay at `+∞`. -/
lemma at47_integrable_of_decay {F : ℂ → ℂ} (hF : Differentiable ℂ F) {A K1 K2 : ℝ} (hA : 1 ≤ A)
    (h1 : ∀ x : ℝ, x ≤ -A → ‖F (x : ℂ)‖ ≤ K1 * (-x) ^ (-(3 / 2) : ℝ))
    (h2 : ∀ x : ℝ, A ≤ x → ‖F (x : ℂ)‖ ≤ K2 * x ^ (-2 : ℝ)) :
    Integrable (fun x : ℝ => F (x : ℂ)) := by
  have hc : Continuous (fun x : ℝ => F (x : ℂ)) := hF.continuous.comp Complex.continuous_ofReal
  have hA0 : 0 < A := by linarith
  have hneg : IntegrableOn (fun x : ℝ => F (x : ℂ)) (Iio (-A)) := by
    have hg : IntegrableOn (fun s : ℝ => K1 * s ^ (-(3 / 2) : ℝ)) (Ioi A) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hA0).const_mul K1
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (MeasurableEquiv.neg ℝ).measurableEmbedding (f := fun s : ℝ => K1 * s ^ (-(3 / 2) : ℝ)) (s := Ioi A)
    have e : (fun x : ℝ => -x) ⁻¹' (Ioi A) = Iio (-A) := by ext x; simp
    have hg'' : IntegrableOn (fun x : ℝ => K1 * (-x) ^ (-(3 / 2) : ℝ)) (Iio (-A)) := by
      have := h.mpr hg
      simpa [e, Function.comp_def] using this
    refine Integrable.mono' hg'' hc.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    exact h1 x (le_of_lt hx)
  have hpos : IntegrableOn (fun x : ℝ => F (x : ℂ)) (Ioi A) := by
    have hg : IntegrableOn (fun s : ℝ => K2 * s ^ (-2 : ℝ)) (Ioi A) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hA0).const_mul K2
    refine Integrable.mono' hg hc.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact h2 x (le_of_lt hx)
  have hmid : IntegrableOn (fun x : ℝ => F (x : ℂ)) (Icc (-A) A) :=
    hc.continuousOn.integrableOn_Icc
  have : (univ : Set ℝ) = Iio (-A) ∪ Icc (-A) A ∪ Ioi A := by
    ext x; simp only [mem_univ, mem_union, mem_Iio, mem_Icc, mem_Ioi, true_iff]
    by_cases h : x < -A
    · exact Or.inl (Or.inl h)
    · by_cases h' : x ≤ A
      · exact Or.inl (Or.inr ⟨by linarith, h'⟩)
      · exact Or.inr (by linarith)
  rw [← integrableOn_univ, this]
  exact (hneg.union hmid).union hpos

/-- Upper bound for `N²` on the negative axis: `N(-s)² ≤ K s^e √s`. -/
lemma at47_Nf_neg_sq (P Q : ℝ[X]) (hQ : Q ≠ 0) :
    ∃ K S1 : ℝ, 0 ≤ K ∧ 1 ≤ S1 ∧ ∀ s : ℝ, S1 ≤ s → at47_Nf P Q (-s) ^ 2 ≤ K * (s ^ (at47_e P Q) * √s) := by
  obtain ⟨C, c, S, hC, hc, hS, hsz⟩ := at47_sizes P Q hQ
  refine ⟨2 * (9 * C + 38 * C), S, by positivity, hS, fun s hs => ?_⟩
  have hs1 : 1 ≤ s := hS.trans hs
  have hs0 : 0 < s := by linarith
  obtain ⟨hq, hp, -, -, -⟩ := hsz s hs
  obtain ⟨hA, hB⟩ := at47_neg_bounds hs1
  have hr : 0 < √s := Real.sqrt_pos.mpr hs0
  have hrr : √s * √s = s := Real.mul_self_sqrt hs0.le
  set p := P.eval (-s)
  set q := Q.eval (-s)
  set A := airyAi (-s)
  set B := airyAi' (-s)
  have hA2 : A ^ 2 ≤ 9 / √s := by rw [le_div_iff₀ hr]; linarith
  have h1 : p ^ 2 * A ^ 2 ≤ 9 * C * (s ^ (at47_e P Q) * √s) := by
    have : p ^ 2 * A ^ 2 ≤ (C * s ^ (at47_e P Q + 1)) * (9 / √s) := mul_le_mul hp hA2 (sq_nonneg _) (by positivity)
    refine this.trans (le_of_eq ?_)
    rw [pow_succ]
    field_simp
    nlinarith [hrr]
  have h2 : q ^ 2 * B ^ 2 ≤ 38 * C * (s ^ (at47_e P Q) * √s) := by
    have : q ^ 2 * B ^ 2 ≤ (C * s ^ (at47_e P Q)) * (38 * √s) := mul_le_mul hq hB (sq_nonneg _) (by positivity)
    refine this.trans (le_of_eq ?_); ring
  unfold at47_Nf
  nlinarith [sq_nonneg (p * A - q * B)]

lemma at47_F_real_formula {P Q : ℝ[X]} {S : Finset ℝ} {F : ℂ → ℂ}
    (hFeq : ∀ z, F z * at47_pr S z = (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * airyPQN P Q z ^ 2) {x : ℝ} (hx : x ∉ S) :
    F (x : ℂ) = (((-1 : ℝ) ^ S.card * at47_Nf P Q x ^ 2 / ∏ t ∈ S, (x - t) : ℝ) : ℂ) := by
  have h := hFeq (x : ℂ)
  have hpr := at47_pr_ne_zero hx
  rw [at47_pr_ofReal, airyPQN_ofReal] at h
  rw [at47_pr_ofReal] at hpr
  push_cast
  rw [eq_div_iff (by simpa using hpr)]
  unfold at47_Nf
  push_cast at h ⊢
  exact h

lemma at47_rpow_neg_three_halves {s : ℝ} (hs : 0 < s) : s ^ (-(3 / 2) : ℝ) = 1 / (s * √s) := by
  rw [Real.rpow_neg hs.le, one_div]
  congr 1
  have : s ^ (3 / 2 : ℝ) = s ^ (1 : ℝ) * s ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add hs]; norm_num
  rw [this, Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- Decay of the extremal on the negative axis: `‖F(x)‖ ≤ K (-x)^{-3/2}` for `x ≤ -A`. -/
lemma at47_F_neg_decay {P Q : ℝ[X]} (hQ : Q ≠ 0) (S : Finset ℝ) (hcard : S.card = at47_m P Q) {F : ℂ → ℂ}
    (hFeq : ∀ z, F z * at47_pr S z = (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * airyPQN P Q z ^ 2) :
    ∃ K A : ℝ, 1 ≤ A ∧ ∀ x : ℝ, x ≤ -A → ‖F (x : ℂ)‖ ≤ K * (-x) ^ (-(3 / 2) : ℝ) := by
  obtain ⟨K, S1, hK, hS1, hN⟩ := at47_Nf_neg_sq P Q hQ
  have hm : S.card = at47_e P Q + 2 := hcard.trans (at47_m_eq P Q)
  set T : ℝ := ∑ t ∈ S, |t| with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨K * 2 ^ S.card, max S1 (2 * T + 1), le_trans hS1 (le_max_left _ _), fun x hx => ?_⟩
  set s : ℝ := -x with hs
  have hsA : max S1 (2 * T + 1) ≤ s := by linarith
  have hs1 : 1 ≤ s := (le_trans hS1 (le_max_left _ _)).trans hsA
  have hs0 : 0 < s := by linarith
  have hsT : 2 * T + 1 ≤ s := (le_max_right _ _).trans hsA
  have hxs : x = -s := by rw [hs]; ring
  have hxS : x ∉ S := by
    intro hxm
    have h1 : |x| ≤ T := Finset.single_le_sum (f := fun t => |t|) (fun _ _ => abs_nonneg _) hxm
    rw [hxs, abs_neg, abs_of_pos hs0] at h1
    linarith
  have hprne := at47_pr_ne_zero hxS
  have hpr : ∏ t ∈ S, (x - t) ≠ 0 := by
    intro h; apply hprne; rw [at47_pr_ofReal, h]; simp
  have hprlow : (s / 2) ^ S.card ≤ |∏ t ∈ S, (x - t)| := by
    rw [Finset.abs_prod]
    calc (s / 2) ^ S.card = ∏ t ∈ S, (s / 2) := by rw [Finset.prod_const]
      _ ≤ ∏ t ∈ S, |x - t| := by
          gcongr with t ht
          have h1 : |t| ≤ T := Finset.single_le_sum (f := fun t => |t|) (fun _ _ => abs_nonneg _) ht
          have hxabs : |x| = s := by rw [hxs, abs_neg, abs_of_pos hs0]
          have := abs_sub_abs_le_abs_sub x t
          linarith
  have hFx := at47_F_real_formula hFeq hxS
  have hNs := hN s (le_trans (le_max_left _ _) hsA)
  rw [← hxs] at hNs
  rw [hFx, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (sq_nonneg _), at47_rpow_neg_three_halves hs0]
  have hpos : 0 < (s / 2) ^ S.card := by positivity
  calc at47_Nf P Q x ^ 2 / |∏ t ∈ S, (x - t)| ≤ (K * (s ^ at47_e P Q * √s)) / (s / 2) ^ S.card := by
        apply div_le_div₀ (by positivity) hNs hpos hprlow
    _ = K * 2 ^ S.card * (1 / (s * √s)) := by
        rw [hm, div_pow]
        have hr : 0 < √s := Real.sqrt_pos.mpr hs0
        have hrr : √s * √s = s := Real.mul_self_sqrt hs0.le
        field_simp
        rw [sq, hrr, pow_add]; ring

lemma at47_one_add_rpow_le {x ν : ℝ} (hx : 1 ≤ x) : (1 + x) ^ ν ≤ 2 ^ |ν| * x ^ ν := by
  have hx0 : 0 < x := by linarith
  have h2x : 1 + x ≤ 2 * x := by linarith
  rcases le_or_gt 0 ν with hν | hν
  · calc (1 + x) ^ ν ≤ (2 * x) ^ ν := Real.rpow_le_rpow (by linarith) h2x hν
      _ = 2 ^ ν * x ^ ν := Real.mul_rpow (by norm_num) hx0.le
      _ ≤ 2 ^ |ν| * x ^ ν := by
          gcongr
          · norm_num
          · exact le_abs_self ν
  · calc (1 + x) ^ ν ≤ x ^ ν := Real.rpow_le_rpow_of_nonpos hx0 (by linarith) hν.le
      _ ≤ 2 ^ |ν| * x ^ ν := by
          have : 1 ≤ (2 : ℝ) ^ |ν| := Real.one_le_rpow (by norm_num) (abs_nonneg _)
          have : 0 ≤ x ^ ν := (Real.rpow_pos_of_pos hx0 ν).le
          nlinarith

lemma at47_env_ofReal_nonneg {u : ℝ} (hu : 0 ≤ u) :
    airyEnv (u : ℂ) = Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) := by
  unfold airyEnv
  have : ((u : ℂ) ^ (3 / 2 : ℂ)).re = u ^ (3 / 2 : ℝ) := by
    have := Complex.ofReal_cpow hu (3 / 2 : ℝ)
    rw [show (((3 / 2 : ℝ)) : ℂ) = (3 / 2 : ℂ) by push_cast; ring] at this
    rw [← this, Complex.ofReal_re]
  rw [this]

/-- Decay of a class function on the positive axis: `‖F(x)‖ ≤ K x^{-2}` for `x ≥ A`. -/
lemma at47_F_pos_decay {F : ℂ → ℂ} {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℂ, ‖F u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    ∃ K A : ℝ, 1 ≤ A ∧ ∀ x : ℝ, A ≤ x → ‖F (x : ℂ)‖ ≤ K * x ^ (-2 : ℝ) := by
  have h := (tendsto_rpow_mul_exp_rpow (ν + 2) (b := 4 / 3) (by norm_num)).eventually
    (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))
  obtain ⟨A0, hA0⟩ := Filter.eventually_atTop.mp h
  refine ⟨C * 2 ^ |ν|, max 1 A0, le_max_left _ _, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hxA : A0 ≤ x := (le_max_right _ _).trans hx
  have hlt := hA0 x hxA
  have hn : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
  have hE : airyEnv (x : ℂ) = Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ)) := at47_env_ofReal_nonneg hx0.le
  have h1 := hb (x : ℂ)
  rw [hn, hE] at h1
  have h2 := at47_one_add_rpow_le (ν := ν) hx1
  have hexp : 0 ≤ Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ)) := (Real.exp_pos _).le
  have h3 : x ^ ν * Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ)) ≤ x ^ (-2 : ℝ) := by
    have : x ^ ν * Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ)) =
        x ^ (-2 : ℝ) * (x ^ (ν + 2) * Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ))) := by
      rw [Real.rpow_add hx0]
      have : x ^ (-2 : ℝ) * x ^ (2 : ℝ) = 1 := by rw [← Real.rpow_add hx0]; norm_num
      calc _ = (x ^ (-2 : ℝ) * x ^ (2 : ℝ)) * (x ^ ν * Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ))) := by rw [this]; ring
        _ = _ := by ring
    rw [this]
    have hp : 0 < x ^ (-2 : ℝ) := Real.rpow_pos_of_pos hx0 _
    nlinarith
  calc ‖F (x : ℂ)‖ ≤ C * (1 + x) ^ ν * Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ)) := h1
    _ ≤ C * (2 ^ |ν| * x ^ ν) * Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ)) := by gcongr
    _ = C * 2 ^ |ν| * (x ^ ν * Real.exp (-(4 / 3) * x ^ (3 / 2 : ℝ))) := by ring
    _ ≤ C * 2 ^ |ν| * x ^ (-2 : ℝ) := by gcongr

/-- **Theorem 4.7, existence half** (`SOFT_EDGE_THEOREMS.md`).  Let `S` be a set of `m = at47_m P Q` zeros of `N = P Ai + Q Ai'`
(`(P, Q)` Hermite-Biehler, `Q ≠ 0`) with minimum `tm`.  Then `F = (-1)^m N² / ∏_{t ∈ S}(u - t)` (the entire function with
`F ∏ = (-1)^m N²`) is entire, integrable on `ℝ` (decay `|x|^{-3/2}`), in the class `‖F(u)‖ ≤ C (1+|u|)^ν e(u)`, real on `ℝ`,
`≥ 0` on `(-∞, tm]`, vanishes on `S`, has `∫ F = 0`, and is not identically zero.  So `F` is admissible for `um = tm`.  Not formalised:
that the `m` largest zeros exist (this is a hypothesis on `S`). -/
theorem at47_existence {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) (S : Finset ℝ)
    (hcard : S.card = at47_m P Q) (hSz : ∀ t ∈ S, airyPQN P Q (t : ℂ) = 0)
    {tm : ℝ} (htm : tm ∈ S) (hmin : ∀ t ∈ S, tm ≤ t) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ z, F z * at47_pr S z = (((-1 : ℝ) ^ S.card : ℝ) : ℂ) * airyPQN P Q z ^ 2) ∧
      Integrable (fun x : ℝ => F (x : ℂ)) ∧
      (∃ C ν : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖F u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) ∧
      (∀ x : ℝ, (F (x : ℂ)).im = 0) ∧ (∀ x : ℝ, x ≤ tm → 0 ≤ (F (x : ℂ)).re) ∧
      (∀ t ∈ S, F (t : ℂ) = 0) ∧ (∫ x : ℝ, F (x : ℂ)) = 0 ∧ ∃ x : ℝ, F (x : ℂ) ≠ 0 := by
  classical
  obtain ⟨C0, ν0, hC0, hcl⟩ := at47_N_class P Q
  have hNd := differentiable_airyPQN P Q
  obtain ⟨ψ, hψ, hψe, C1, hC1, hb1⟩ := at47_div_finset S (φ := fun z => airyPQN P Q z ^ 2) (by fun_prop)
    (fun t ht => by simp [hSz t ht]) hC0 (fun u => by simpa using hcl u)
  set ε : ℝ := (-1 : ℝ) ^ S.card with hε
  have hε2 : ε * ε = 1 := by rw [hε, ← mul_pow]; simp
  set F : ℂ → ℂ := fun z => (ε : ℂ) * ψ z with hFdef
  have hFd : Differentiable ℂ F := by fun_prop
  have hFeq : ∀ z, F z * at47_pr S z = (ε : ℂ) * airyPQN P Q z ^ 2 := by
    intro z; simp only [hFdef, at47_pr]; rw [mul_assoc, ← hψe z]
  have hFb : ∀ u : ℂ, ‖F u‖ ≤ C1 * (1 + ‖u‖) ^ ν0 * airyEnv u := by
    intro u
    have : ‖F u‖ = ‖ψ u‖ := by
      simp only [hFdef, norm_mul, hε, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [this]; exact hb1 u
  -- F vanishes on S
  have hFS : ∀ t ∈ S, F (t : ℂ) = 0 := by
    intro t ht
    have hprt : at47_pr S (t : ℂ) = 0 := at47_pr_eq_zero ht
    have e : (fun z => F z * at47_pr S z) = fun z => (ε : ℂ) * airyPQN P Q z ^ 2 := funext hFeq
    have hd1 : deriv (fun z => F z * at47_pr S z) (t : ℂ) =
        deriv F (t : ℂ) * at47_pr S (t : ℂ) + F (t : ℂ) * deriv (at47_pr S) (t : ℂ) :=
      deriv_mul (hFd _) (at47_pr_differentiable S _)
    have hd2 : deriv (fun z => (ε : ℂ) * airyPQN P Q z ^ 2) (t : ℂ) = 0 := by
      have e2 : (fun z => airyPQN P Q z ^ 2) = fun z => airyPQN P Q z * airyPQN P Q z := by funext w; ring
      have hdd : deriv (fun z => airyPQN P Q z ^ 2) (t : ℂ) = 0 := by
        rw [e2]
        have : deriv (fun z => airyPQN P Q z * airyPQN P Q z) (t : ℂ) =
            deriv (airyPQN P Q) (t : ℂ) * airyPQN P Q (t : ℂ) + airyPQN P Q (t : ℂ) * deriv (airyPQN P Q) (t : ℂ) :=
          deriv_mul (hNd _) (hNd _)
        rw [this, hSz t ht]; simp
      have hdd' : DifferentiableAt ℂ (fun z => airyPQN P Q z ^ 2) (t : ℂ) := by fun_prop
      rw [deriv_const_mul _ hdd', hdd]; simp
    rw [e, hd2, hprt] at hd1
    simp at hd1
    rcases hd1 with h | h
    · exact h
    · exact absurd h (at47_pr_deriv_ne_zero ht)
  have hFzero : ∀ x : ℝ, airyPQN P Q (x : ℂ) = 0 → F (x : ℂ) = 0 := by
    intro x hx
    by_cases hxS : x ∈ S
    · exact hFS x hxS
    · have h := hFeq (x : ℂ)
      rw [hx] at h
      simp at h
      rcases h with h | h
      · exact h
      · exact absurd h (at47_pr_ne_zero hxS)
  -- integrability
  obtain ⟨K1, A1, hA1, h1⟩ := at47_F_neg_decay hQ S hcard hFeq
  obtain ⟨K2, A2, hA2, h2⟩ := at47_F_pos_decay hC1 hFb
  have hFi : Integrable (fun x : ℝ => F (x : ℂ)) := by
    refine at47_integrable_of_decay hFd (A := max A1 A2) (K1 := K1) (K2 := K2) (le_trans hA1 (le_max_left _ _))
      (fun x hx => h1 x (by linarith [le_max_left A1 A2])) (fun x hx => h2 x (le_trans (le_max_right _ _) hx))
  -- the quadrature gives the zero integral
  have hint : (∫ x : ℝ, F (x : ℂ)) = 0 := by
    have hs := airyPQ_hasSum_unc hHB hQ hFd hFi hC1 hFb
    have hz : ∀ z : {z : ℂ // airyPQN P Q z = 0}, F z * (airyPQD P Q z / airyPQN' P Q z ^ 2) = 0 := by
      intro z
      have hzr := airyPQ_zero_eq_ofReal hHB z.2
      have : F z = 0 := by
        have := hFzero z.1.re (by rw [← hzr]; exact z.2)
        rwa [← hzr] at this
      rw [this, zero_mul]
    have h0 : HasSum (fun z : {z : ℂ // airyPQN P Q z = 0} => F z * (airyPQD P Q z / airyPQN' P Q z ^ 2)) 0 := by
      simp only [hz]; exact hasSum_zero
    exact hs.unique h0
  -- real values
  have hFr : ∀ x : ℝ, (F (x : ℂ)).im = 0 := by
    intro x
    by_cases hxS : x ∈ S
    · rw [hFS x hxS]; simp
    · rw [at47_F_real_formula hFeq hxS, Complex.ofReal_im]
  have hFnn : ∀ x : ℝ, x ≤ tm → 0 ≤ (F (x : ℂ)).re := by
    intro x hx
    by_cases hxS : x ∈ S
    · rw [hFS x hxS]; simp
    · rw [at47_F_real_formula hFeq hxS, Complex.ofReal_re]
      have hs := at47_pr_sign (S := S) (x := x) (fun t ht => hx.trans (hmin t ht))
      have hpr := at47_pr_ne_zero hxS
      rw [at47_pr_ofReal] at hpr
      have hpr' : ∏ t ∈ S, (x - t) ≠ 0 := by intro h; apply hpr; rw [h]; simp
      have hw : 0 < ε * ∏ t ∈ S, (x - t) :=
        lt_of_le_of_ne hs (fun h => hpr' (by
          have := h.symm
          rcases mul_eq_zero.mp this with h' | h'
          · rw [hε] at h'; simp at h'
          · exact h'))
      have : ε * at47_Nf P Q x ^ 2 / ∏ t ∈ S, (x - t) = at47_Nf P Q x ^ 2 / (ε * ∏ t ∈ S, (x - t)) := by
        rw [div_eq_div_iff hpr' hw.ne']
        calc ε * at47_Nf P Q x ^ 2 * (ε * ∏ t ∈ S, (x - t)) = (ε * ε) * at47_Nf P Q x ^ 2 * ∏ t ∈ S, (x - t) := by ring
          _ = _ := by rw [hε2]; ring
      rw [this]
      positivity
  obtain ⟨x1, hx1lt, hx1⟩ := at47_exists_real_ne_zero hHB tm
  have hx1S : x1 ∉ S := fun h => absurd (hmin x1 h) (not_le.mpr hx1lt)
  have hne : ∃ x : ℝ, F (x : ℂ) ≠ 0 := by
    refine ⟨x1, fun h0 => ?_⟩
    have h := hFeq (x1 : ℂ)
    rw [h0, zero_mul] at h
    have hε0 : (ε : ℂ) ≠ 0 := by rw [hε]; simp
    exact hx1 (pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp h.symm).resolve_left hε0))
  exact ⟨F, hFd, hFeq, hFi, ⟨C1, ν0, hC1, hFb⟩, hFr, hFnn, hFS, hint, hne⟩

/-- info: 'FormalResearch.Special.at47_existence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.at47_existence

/-- **`u_m^* ≤ t_m`** (Theorem 4.7): an admissible `f` (hypotheses of `at47_uniqueness`) with `um > tm` is identically zero.
Together with `at47_existence` (the extremal `F` is admissible for `um = tm`) this says
`sup {um : ∃ f ≠ 0 admissible} = tm`, for the set `S` of the `m` largest zeros. -/
theorem at47_no_admissible_above {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) (S : Finset ℝ)
    (hcard : S.card = at47_m P Q) (hSz : ∀ t ∈ S, airyPQN P Q (t : ℂ) = 0)
    (hS_top : ∀ x : ℝ, airyPQN P Q (x : ℂ) = 0 → x ∉ S → ∀ t ∈ S, x < t)
    {tm : ℝ} (htm : tm ∈ S) (hmin : ∀ t ∈ S, tm ≤ t) {um : ℝ} (hum : tm < um)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) (hint : (∫ x : ℝ, f (x : ℂ)).re ≤ 0)
    (hfS : ∀ t ∈ S, 0 ≤ (f (t : ℂ)).re) (hfneg : ∀ x : ℝ, x ≤ um → 0 ≤ (f (x : ℂ)).re) :
    ∀ z : ℂ, f z = 0 := by
  obtain ⟨c, -, hfc, hcz⟩ := at47_uniqueness hHB hQ S hcard hSz hS_top htm hmin hum.le hf hfi hC hb hreal hint hfS hfneg
  have hc := hcz hum
  have hz : ∀ z, at47_pr S z ≠ 0 → f z = 0 := by
    intro z hz
    have := hfc z
    rw [hc] at this
    simp at this
    rcases this with h | h
    · exact h
    · exact absurd h hz
  have hfin : {z : ℂ | at47_pr S z = 0}.Finite := by
    refine (S.finite_toSet.image (fun t : ℝ => (t : ℂ))).subset fun z hz => ?_
    unfold at47_pr at hz
    obtain ⟨t, ht, h0⟩ := Finset.prod_eq_zero_iff.mp hz
    exact ⟨t, ht, (sub_eq_zero.mp h0).symm⟩
  have hdense : Dense {z : ℂ | at47_pr S z = 0}ᶜ := hfin.countable.dense_compl ℝ
  have := Continuous.ext_on hdense hf.continuous continuous_const (g := fun _ => (0 : ℂ))
    (fun z hz' => hz z hz')
  intro z; exact congrFun this z

/-- info: 'FormalResearch.Special.at47_no_admissible_above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.at47_no_admissible_above

end FormalResearch.Special
