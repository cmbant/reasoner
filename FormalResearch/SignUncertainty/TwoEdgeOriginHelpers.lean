module

public import FormalResearch.SignUncertainty.GenRationalO6Family
public import FormalResearch.SignUncertainty.CeDualFloors
public import FormalResearch.SignUncertainty.CeGenOrigin
public import FormalResearch.SignUncertainty.StripAdmissLift
public import FormalResearch.CohnElkies.PreEdgeTangency

/-!
# Helpers for the two-edge origin Mellin bridge (`cepe:PE3`)

Modular tail, moment, Hölder, and oscillatory-remainder estimates factored out of
`TwoEdgeOriginBridge.lean` so each module stays compact and fast to elaborate.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

lemma finset_sum_continuous {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) : Continuous fun u : ℝ => ∑ i ∈ s, f i u := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuous_const
  | @insert a t hat ih =>
      have hfn : (fun u : ℝ => ∑ i ∈ insert a t, f i u) = fun u : ℝ => f a u + ∑ i ∈ t, f i u :=
        funext fun u => Finset.sum_insert hat
      rw [hfn]
      exact (hf a (Finset.mem_insert_self a t)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma finset_sum_integrableOn {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (A : Set ℝ)
    (hf : ∀ i ∈ s, IntegrableOn (f i) A) : IntegrableOn (fun u : ℝ => ∑ i ∈ s, f i u) A := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t hat ih =>
      have hfn : (fun u : ℝ => ∑ i ∈ insert a t, f i u) = fun u : ℝ => f a u + ∑ i ∈ t, f i u :=
        funext fun u => Finset.sum_insert hat
      rw [hfn]
      exact (hf a (Finset.mem_insert_self a t)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma finset_sum_setIntegral {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (A : Set ℝ)
    (hf : ∀ i ∈ s, IntegrableOn (f i) A) :
    ∫ u in A, (∑ i ∈ s, f i u) = ∑ i ∈ s, ∫ u in A, f i u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t hat ih =>
      have hfn : (fun u : ℝ => ∑ i ∈ insert a t, f i u) = fun u : ℝ => f a u + ∑ i ∈ t, f i u :=
        funext fun u => Finset.sum_insert hat
      rw [hfn, integral_add (hf a (Finset.mem_insert_self a t))
        (finset_sum_integrableOn t f A fun i hi => hf i (Finset.mem_insert_of_mem hi)),
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi), Finset.sum_insert hat]

/-- Negative-axis `O((1 + |u|)^{-3/2})` bound for any `HasGenRationalAiryCoeffs F β₀₀ β₁₁`. -/
lemma genRational_neg_tail_bound {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF : HasGenRationalAiryCoeffs F β₀₀ β₁₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, u ≤ 0 → |(F (u : ℂ)).re| ≤ C * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨R₀, K, hR5, hK0, hwkb⟩ := hF.neg_axis_wkb
  let C₁ : ℝ := 2 ^ (3 / 2 : ℝ) * (|β₀₀| + |β₁₁| + K) / π + 1
  have hC₁ : 0 < C₁ := by positivity
  have hcont : Continuous fun u : ℝ => (1 + |u|) ^ (3 / 2 : ℝ) * |(F (u : ℂ)).re| :=
    ((continuous_const.add continuous_abs).rpow_const fun _ => Or.inr (by norm_num)).mul
      (Complex.continuous_re.comp (hF.1.1.continuous.comp Complex.continuous_ofReal)).abs
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun u : ℝ => (1 + |u|) ^ (3 / 2 : ℝ) * |(F (u : ℂ)).re|)
    (s := Icc (-R₀) 0) hcont.continuousOn
  let C : ℝ := max C₁ |M₀|
  have hC : 0 ≤ C := le_trans hC₁.le (le_max_left _ _)
  refine ⟨C, hC, fun u hu => ?_⟩
  rcases le_or_gt u (-R₀) with hfar | hnear
  · set x : ℝ := -u
    have hxR : R₀ ≤ x := by dsimp [x]; linarith
    have hx1 : 1 ≤ x := by linarith
    have hx0 : 0 < x := by linarith
    have hfx := hwkb x hxR
    have hsincos : |β₀₀ * Real.sin (cohnTheta x) ^ 2 + β₁₁ * Real.cos (cohnTheta x) ^ 2| ≤ |β₀₀| + |β₁₁| := by
      calc |β₀₀ * Real.sin (cohnTheta x) ^ 2 + β₁₁ * Real.cos (cohnTheta x) ^ 2|
          ≤ |β₀₀ * Real.sin (cohnTheta x) ^ 2| + |β₁₁ * Real.cos (cohnTheta x) ^ 2| := abs_add_le _ _
        _ = |β₀₀| * Real.sin (cohnTheta x) ^ 2 + |β₁₁| * Real.cos (cohnTheta x) ^ 2 := by
            rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin (cohnTheta x))),
              abs_of_nonneg (sq_nonneg (Real.cos (cohnTheta x)))]
        _ ≤ |β₀₀| * 1 + |β₁₁| * 1 := by
            gcongr
            · exact Real.sin_sq_le_one _
            · exact Real.cos_sq_le_one _
        _ = |β₀₀| + |β₁₁| := by ring
    have hkx : K * x ^ (-(1 / 2 : ℝ)) ≤ K := by
      calc K * x ^ (-(1 / 2 : ℝ)) ≤ K * 1 :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)) hK0
        _ = K := mul_one K
    have hpow_abs : π * x ^ (3 / 2 : ℝ) * |(F (u : ℂ)).re| ≤ |β₀₀| + |β₁₁| + K := by
      have htri : |π * x ^ (3 / 2 : ℝ) * (F ((-x : ℝ) : ℂ)).re| ≤
          |β₀₀ * Real.sin (cohnTheta x) ^ 2 + β₁₁ * Real.cos (cohnTheta x) ^ 2| + K * x ^ (-(1 / 2 : ℝ)) := by
        calc |π * x ^ (3 / 2 : ℝ) * (F ((-x : ℝ) : ℂ)).re|
            = |(π * x ^ (3 / 2 : ℝ) * (F ((-x : ℝ) : ℂ)).re -
                (β₀₀ * Real.sin (cohnTheta x) ^ 2 + β₁₁ * Real.cos (cohnTheta x) ^ 2)) +
                (β₀₀ * Real.sin (cohnTheta x) ^ 2 + β₁₁ * Real.cos (cohnTheta x) ^ 2)| := by ring_nf
          _ ≤ |π * x ^ (3 / 2 : ℝ) * (F ((-x : ℝ) : ℂ)).re -
                (β₀₀ * Real.sin (cohnTheta x) ^ 2 + β₁₁ * Real.cos (cohnTheta x) ^ 2)| +
              |β₀₀ * Real.sin (cohnTheta x) ^ 2 + β₁₁ * Real.cos (cohnTheta x) ^ 2| := abs_add_le _ _
          _ ≤ _ := by linarith [hfx]
      have heq : (-x : ℝ) = u := by dsimp [x]; ring
      rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ π * x ^ (3 / 2 : ℝ))] at htri
      linarith
    have h1x : (1 + |u|) ^ (3 / 2 : ℝ) ≤ 2 ^ (3 / 2 : ℝ) * x ^ (3 / 2 : ℝ) := by
      have habs : 1 + |u| ≤ 2 * x := by rw [abs_of_nonpos hu]; dsimp [x]; linarith
      calc (1 + |u|) ^ (3 / 2 : ℝ) ≤ (2 * x) ^ (3 / 2 : ℝ) :=
            Real.rpow_le_rpow (by positivity) habs (by norm_num)
        _ = 2 ^ (3 / 2 : ℝ) * x ^ (3 / 2 : ℝ) := Real.mul_rpow zero_le_two hx0.le
    have hmain : (1 + |u|) ^ (3 / 2 : ℝ) * |(F (u : ℂ)).re| ≤ C₁ := by
      have hden : 0 < π := Real.pi_pos
      calc (1 + |u|) ^ (3 / 2 : ℝ) * |(F (u : ℂ)).re|
          ≤ (2 ^ (3 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) * |(F (u : ℂ)).re| :=
            mul_le_mul_of_nonneg_right h1x (abs_nonneg _)
        _ = (2 ^ (3 / 2 : ℝ) / π) * (π * x ^ (3 / 2 : ℝ) * |(F (u : ℂ)).re|) := by
            field_simp [hden.ne']
        _ ≤ (2 ^ (3 / 2 : ℝ) / π) * (|β₀₀| + |β₁₁| + K) :=
            mul_le_mul_of_nonneg_left hpow_abs (by positivity)
        _ ≤ C₁ := by dsimp [C₁]; linarith [show 2 ^ (3 / 2 : ℝ) / π * (|β₀₀| + |β₁₁| + K) =
            2 ^ (3 / 2 : ℝ) * (|β₀₀| + |β₁₁| + K) / π by ring]
    calc |(F (u : ℂ)).re| = (1 + |u|) ^ (3 / 2 : ℝ) * |(F (u : ℂ)).re| * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by
          rw [mul_assoc, mul_comm |(F (u : ℂ)).re|, ← mul_assoc, Real.rpow_neg (by positivity),
            mul_inv_cancel₀ (by positivity), one_mul]
      _ ≤ C₁ * (1 + |u|) ^ (-(3 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hmain (by positivity)
      _ ≤ C * (1 + |u|) ^ (-(3 / 2 : ℝ)) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hu_mem : u ∈ Icc (-R₀) 0 := ⟨hnear.le, hu⟩
    have hbound := hM₀ u hu_mem
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (abs_nonneg _))] at hbound
    have hmain : (1 + |u|) ^ (3 / 2 : ℝ) * |(F (u : ℂ)).re| ≤ C :=
      hbound.trans ((le_abs_self M₀).trans (le_max_right _ _))
    calc |(F (u : ℂ)).re| = (1 + |u|) ^ (3 / 2 : ℝ) * |(F (u : ℂ)).re| * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by
          rw [mul_assoc, mul_comm |(F (u : ℂ)).re|, ← mul_assoc, Real.rpow_neg (by positivity),
            mul_inv_cancel₀ (by positivity), one_mul]
      _ ≤ C * (1 + |u|) ^ (-(3 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hmain (by positivity)

/-- Right-axis first moment `(1 + |u|) |F(u)| ∈ L¹([w, ∞))` for any `F ∈ ℛ_Ai^gen`. -/
lemma genRational_weighted_integrableOn {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF : HasGenRationalAiryCoeffs F β₀₀ β₁₁) (w : ℝ) :
    IntegrableOn (fun u : ℝ => (1 + |u|) * |(F (u : ℂ)).re|) (Ici w) := by
  obtain ⟨C, ν, hC, hpos⟩ := hF.1.2.2.1
  have hcont : Continuous fun u : ℝ => (1 + |u|) * |(F (u : ℂ)).re| :=
    (continuous_const.add continuous_abs).mul
      (Complex.continuous_re.comp (hF.1.1.continuous.comp Complex.continuous_ofReal)).abs
  have h1 : IntegrableOn (fun u : ℝ => (1 + |u|) * |(F (u : ℂ)).re|) (Icc w (max w 0)) :=
    hcont.continuousOn.integrableOn_Icc
  let k : ℕ := Nat.ceil (max (ν + 1) 0)
  have hk_ge : ν + 1 ≤ (k : ℝ) := (le_max_left _ _).trans (Nat.le_ceil _)
  let M_pos : ℝ := C * (Nat.factorial k : ℝ) * (3 : ℝ) ^ k * Real.exp 1
  have hM_pos : 0 ≤ M_pos := by positivity
  have hint_exp : IntegrableOn (fun u : ℝ => M_pos * Real.exp (-(1 / 3 : ℝ) * u)) (Ioi (max w 0)) := by
    have he := integrableOn_exp_mul_Ioi (a := -(1 / 3 : ℝ)) (by norm_num) (max w 0)
    exact (he.const_mul M_pos).congr (ae_of_all _ fun u => by simp)
  have h2 : IntegrableOn (fun u : ℝ => (1 + |u|) * |(F (u : ℂ)).re|) (Ioi (max w 0)) := by
    refine hint_exp.mono' (hcont.aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := (le_max_right w 0).trans (mem_Ioi.mp hu).le
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (abs_nonneg _)), abs_of_nonneg hu0]
    have hFu : |(F (u : ℂ)).re| ≤ C * (1 + u) ^ ν * airyEnv (u : ℂ) := by
      have hFuC := hpos (u : ℂ)
      rw [Complex.norm_real, Real.norm_of_nonneg hu0] at hFuC
      exact (Complex.abs_re_le_norm _).trans hFuC
    have h1u : (1 + u) ^ (ν + 1) ≤ (1 + u) ^ (k : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hk_ge
    have hpow_k : (1 + u) ^ (k : ℝ) = (1 + u) ^ k := Real.rpow_natCast _ k
    have hexp_env : airyEnv (u : ℂ) ≤ Real.exp (2 / 3) * Real.exp (-(2 / 3) * u) := by
      simpa using exp_mul_airyEnv_le le_rfl hu0
    have hfac : (1 + u) ^ k ≤ (Nat.factorial k : ℝ) * (3 : ℝ) ^ k * Real.exp (1 / 3 + (1 / 3) * u) := by
      have hp := Real.pow_div_factorial_le_exp ((1 / 3 : ℝ) * (1 + u)) (by positivity) k
      have hmul : ((1 / 3 : ℝ) * (1 + u)) ^ k = (1 + u) ^ k / (3 : ℝ) ^ k := by
        rw [mul_pow, one_div, inv_pow, div_eq_mul_inv]; ring
      rw [hmul, div_div, div_le_iff₀ (by positivity)] at hp
      calc (1 + u) ^ k ≤ Real.exp ((1 / 3 : ℝ) * (1 + u)) * ((3 : ℝ) ^ k * (Nat.factorial k : ℝ)) := hp
        _ = (Nat.factorial k : ℝ) * (3 : ℝ) ^ k * Real.exp (1 / 3 + (1 / 3) * u) := by
            rw [show (1 / 3 : ℝ) * (1 + u) = 1 / 3 + (1 / 3) * u by ring]; ring
    calc (1 + u) * |(F (u : ℂ)).re|
        ≤ (1 + u) * (C * (1 + u) ^ ν * airyEnv (u : ℂ)) :=
          mul_le_mul_of_nonneg_left hFu (by positivity)
      _ = C * ((1 + u) ^ ν * (1 + u)) * airyEnv (u : ℂ) := by ring
      _ = C * (1 + u) ^ (ν + 1) * airyEnv (u : ℂ) := by
          rw [Real.rpow_add (by linarith), Real.rpow_one]
      _ ≤ C * (1 + u) ^ k * (Real.exp (2 / 3) * Real.exp (-(2 / 3) * u)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (h1u.trans_eq hpow_k) hC) hexp_env
            (airyEnv_pos _).le (mul_nonneg hC (pow_nonneg (by linarith) k))
      _ ≤ C * ((Nat.factorial k : ℝ) * (3 : ℝ) ^ k * Real.exp (1 / 3 + (1 / 3) * u)) *
            (Real.exp (2 / 3) * Real.exp (-(2 / 3) * u)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac hC) (by positivity)
      _ = M_pos * Real.exp (-(1 / 3 : ℝ) * u) := by
          dsimp [M_pos]
          have hexp_eq : Real.exp (1 / 3 + (1 / 3) * u) * (Real.exp (2 / 3) * Real.exp (-(2 / 3) * u)) =
              Real.exp 1 * Real.exp (-(1 / 3 : ℝ) * u) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
            congr 1; ring
          calc C * ((Nat.factorial k : ℝ) * (3 : ℝ) ^ k * Real.exp (1 / 3 + (1 / 3) * u)) *
                (Real.exp (2 / 3) * Real.exp (-(2 / 3) * u))
              = C * (Nat.factorial k : ℝ) * (3 : ℝ) ^ k *
                  (Real.exp (1 / 3 + (1 / 3) * u) * (Real.exp (2 / 3) * Real.exp (-(2 / 3) * u))) := by ring
            _ = _ := by rw [hexp_eq]; ring
  rw [← Icc_union_Ioi_eq_Ici (le_max_left w 0)]
  exact h1.union h2

lemma norm_bsplineE1_pow_sub_one_le (m : ℕ) {R_b : ℝ} (hRb : 0 ≤ R_b) :
    ∃ C_m : ℝ, 0 ≤ C_m ∧ ∀ z : ℂ, ‖z‖ ≤ R_b → ‖bsplineE1 z ^ m - 1‖ ≤ C_m * ‖z‖ := by
  have hcd : ContDiff ℂ (⊤ : ℕ∞) (fun z : ℂ => bsplineE1 z ^ m) := contDiff_bsplineE1.pow m
  have hderiv_cont : Continuous (deriv fun z : ℂ => bsplineE1 z ^ m) :=
    hcd.continuous_deriv (by simp)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R_b).exists_bound_of_continuousOn hderiv_cont.continuousOn
  refine ⟨|M|, abs_nonneg M, fun z hz => ?_⟩
  have h0 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R_b := Metric.mem_closedBall_self hRb
  have hz_mem : z ∈ Metric.closedBall (0 : ℂ) R_b := mem_closedBall_zero_iff.mpr hz
  have hmv := (convex_closedBall (0 : ℂ) R_b).norm_image_sub_le_of_norm_deriv_le
    (fun ζ _ => (hcd.differentiable (by simp) ζ)) (fun ζ hζ => (hM ζ hζ).trans (le_abs_self M)) h0 hz_mem
  simpa [bsplineE1_zero] using hmv

lemma hB_neg_even (ν : ℝ) : hB (-ν) = hB ν := by
  unfold hB
  rw [Real.arctan_neg, neg_mul_neg, neg_sq]

lemma integrableOn_neg_tail_rpow_three_halves (C : ℝ) (hC : 0 ≤ C) :
    IntegrableOn (fun u : ℝ => C * (1 + |u|) ^ (-(3 / 2 : ℝ))) (Iic 0) := by
  have hcont_pos : ContinuousOn (fun x : ℝ => C * (1 + x) ^ (-(3 / 2 : ℝ))) (Ioi 0) :=
    continuousOn_const.mul ((continuousOn_const.add continuousOn_id).rpow_const fun x hx =>
      Or.inl (by change (1 + x : ℝ) ≠ 0; linarith [mem_Ioi.mp hx]))
  have hpos1 : IntegrableOn (fun x : ℝ => C * (1 + x) ^ (-(3 / 2 : ℝ))) (Ioc 0 1) :=
    ((continuousOn_const : ContinuousOn (fun _ : ℝ => C) (Icc (0 : ℝ) 1)).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self).mono'
      ((hcont_pos.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          have h1x : 1 ≤ 1 + x := by linarith [hx.1]
          rw [Real.norm_of_nonneg (mul_nonneg hC (Real.rpow_nonneg (by linarith) _))]
          exact mul_le_of_le_one_right hC (Real.rpow_le_one_of_one_le_of_nonpos h1x (by norm_num)))
  have hpos2 : IntegrableOn (fun x : ℝ => C * (1 + x) ^ (-(3 / 2 : ℝ))) (Ioi 1) :=
    ((integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) one_pos).const_mul C).mono'
      ((hcont_pos.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          have hx0 : 0 < x := lt_trans zero_lt_one (mem_Ioi.mp hx)
          rw [Real.norm_of_nonneg (mul_nonneg hC (Real.rpow_nonneg (by linarith) _))]
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by norm_num)) hC)
  have hpos : IntegrableOn (fun x : ℝ => C * (1 + |x|) ^ (-(3 / 2 : ℝ))) (Ioi 0) :=
    ((Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)) ▸ hpos1.union hpos2).congr_fun
      (fun x hx => by dsimp only; rw [abs_of_pos hx]) measurableSet_Ioi
  have hneg : IntegrableOn (fun u : ℝ => C * (1 + |u|) ^ (-(3 / 2 : ℝ))) (Iio 0) := by
    simpa [Set.neg_Ioi, abs_neg] using IntegrableOn.comp_neg hpos
  have h0 : IntegrableOn (fun u : ℝ => C * (1 + |u|) ^ (-(3 / 2 : ℝ))) {(0 : ℝ)} := by
    rw [IntegrableOn, Measure.restrict_eq_zero.mpr Real.volume_singleton]
    exact integrable_zero_measure
  refine (hneg.union h0).mono_set (s := Iic (0 : ℝ)) fun u hu => ?_
  rcases eq_or_lt_of_le (mem_Iic.mp hu) with rfl | hu'
  · exact Or.inr rfl
  · exact Or.inl hu'

/-- Bundled uniform bounds on the dual perturbation `D c` spanned by a bounded finite subset of
`ℛ_Ai^gen`. -/
structure TwoEdgeDualBounds {ι : Type*} (s : Finset ι) (B : ι → ℂ → ℂ) (b₀₀ b₁₁ : ι → ℝ)
    (α : ι → ℝ → ℝ) (D : ℝ → ℝ → ℝ) (δ₀ : ℝ → ℝ) (m : ℕ) (w_cut c_min : ℝ) where
  C_neg : ℝ
  hC_neg : 0 ≤ C_neg
  M_mom : ℝ
  hM_mom : 0 ≤ M_mom
  L1_D : ℝ
  hL1_D : 0 ≤ L1_D
  C_D : ℝ
  hC_D : 0 < C_D
  CL_D : ℝ
  hCL_D : 0 ≤ CL_D
  hUD : ∀ {c : ℝ}, HasU2 (D c)
  hD_cont : ∀ {c : ℝ}, Continuous (D c)
  hD_neg_bd : ∀ {c u : ℝ}, c_min ≤ c → u ≤ 0 → |D c u| ≤ C_neg * (1 + |u|) ^ (-(3 / 2 : ℝ))
  hD_mom_int : ∀ {c : ℝ}, IntegrableOn (fun u : ℝ => (1 + |u|) * |D c u|) (Ici w_cut)
  hD_mom_bd : ∀ {c : ℝ}, c_min ≤ c → ∫ u in Ici w_cut, (1 + |u|) * |D c u| ≤ M_mom
  hD_L1_int : ∀ {c : ℝ}, Integrable (fun u : ℝ => |D c u|)
  hD_L1_bd : ∀ {c : ℝ}, c_min ≤ c → ∫ u : ℝ, |D c u| ≤ L1_D
  hWD_unif : ∀ {c : ℝ} {w : ℂ}, c_min ≤ c → 0 ≤ w.re → ‖liftSymbol (D c) (δ₀ c) m w‖ ≤ C_D
  hD_lap_unif : ∀ {c : ℝ} {w : ℂ}, c_min ≤ c → 0 ≤ w.re →
    ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤ C_D
  hD_lap_int_bd : ∀ {c v : ℝ}, c_min ≤ c →
    ‖∫ u : ℝ, (D c u : ℂ) * Complex.exp (((ceCs : ℂ) * ((v : ℂ) * Complex.I)) * (u : ℂ))‖ ≤ L1_D
  hD_osc_right : ∀ {c v : ℝ}, c_min ≤ c →
    ‖∫ u in Ici w_cut, (D c u : ℂ) * (Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ)) - 1)‖ ≤
      ceCs * M_mom * |v|

lemma twoEdge_dual_bounds {ι : Type*} (s : Finset ι) (B : ι → ℂ → ℂ) (b₀₀ b₁₁ : ι → ℝ)
    (hB : ∀ i ∈ s, HasGenRationalAiryCoeffs (B i) (b₀₀ i) (b₁₁ i))
    (α : ι → ℝ → ℝ) {R c_min w_cut : ℝ}
    (hR : 0 ≤ R) (hw_cut : w_cut ≤ 0)
    (m : ℕ) (δ₀ : ℝ → ℝ) (hδ0 : ∀ {c : ℝ}, c_min ≤ c → 0 ≤ δ₀ c)
    (D : ℝ → ℝ → ℝ) (hD_eq : ∀ {c u : ℝ}, D c u = ∑ i ∈ s, α i c * (B i (u : ℂ)).re)
    (hα : ∀ i ∈ s, ∀ c : ℝ, c_min ≤ c → |α i c| ≤ R) :
    Nonempty (TwoEdgeDualBounds s B b₀₀ b₁₁ α D δ₀ m w_cut c_min) := by
  classical
  have hcs0 : 0 < ceCs := ceCs_pos
  have hUD : ∀ {c : ℝ}, HasU2 (D c) := fun {c} => by
    have hfeq : D c = fun u : ℝ => ∑ i ∈ s, α i c * (B i (u : ℂ)).re := funext fun u => hD_eq
    rw [hfeq]
    exact hasU2_finset_sum s B b₀₀ b₁₁ hB (fun i => α i c)
  have hD_cont : ∀ {c : ℝ}, Continuous (D c) := fun {c} => by
    have hfeq : D c = fun u : ℝ => ∑ i ∈ s, α i c * (B i (u : ℂ)).re := funext fun u => hD_eq
    rw [hfeq]
    exact finset_sum_continuous s (fun i u => α i c * (B i (u : ℂ)).re) fun i hi =>
      continuous_const.mul (Complex.continuous_re.comp ((hB i hi).1.1.continuous.comp Complex.continuous_ofReal))
  have hneg_i : ∀ i ∈ s, ∃ C > 0, ∀ u : ℝ, u ≤ 0 → |(B i (u : ℂ)).re| ≤ C * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by
    intro i hi
    obtain ⟨C, hC0, hb⟩ := genRational_neg_tail_bound (hB i hi)
    exact ⟨C + 1, by linarith, fun u hu => (hb u hu).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))⟩
  choose CN hCN_pos hCN_bd using hneg_i
  let C_neg : ℝ := R * ∑ i ∈ s, if hi : i ∈ s then CN i hi else 0
  have hC_neg : 0 ≤ C_neg := mul_nonneg hR (Finset.sum_nonneg fun i hi => by split_ifs; exact (hCN_pos i hi).le)
  have hD_neg_bd : ∀ {c u : ℝ}, c_min ≤ c → u ≤ 0 → |D c u| ≤ C_neg * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by
    intro c u hc hu
    rw [hD_eq]
    calc |∑ i ∈ s, α i c * (B i (u : ℂ)).re|
        ≤ ∑ i ∈ s, |α i c * (B i (u : ℂ)).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ s, R * ((if hi : i ∈ s then CN i hi else 0) * (1 + |u|) ^ (-(3 / 2 : ℝ))) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [abs_mul]; split_ifs
          exact mul_le_mul (hα i hi c hc) (hCN_bd i hi u hu) (abs_nonneg _) hR
      _ = C_neg * (1 + |u|) ^ (-(3 / 2 : ℝ)) := by
          dsimp [C_neg]; simp_rw [← mul_assoc, ← Finset.sum_mul, ← Finset.mul_sum]
  have hmom_i : ∀ i ∈ s, IntegrableOn (fun u : ℝ => (1 + |u|) * |(B i (u : ℂ)).re|) (Ici w_cut) :=
    fun i hi => genRational_weighted_integrableOn (hB i hi) w_cut
  let M_mom : ℝ := R * ∑ i ∈ s, ∫ u in Ici w_cut, (1 + |u|) * |(B i (u : ℂ)).re|
  have hM_mom : 0 ≤ M_mom :=
    mul_nonneg hR (Finset.sum_nonneg fun i _ => setIntegral_nonneg measurableSet_Ici fun _ _ => by positivity)
  have hD_mom_int : ∀ {c : ℝ}, IntegrableOn (fun u : ℝ => (1 + |u|) * |D c u|) (Ici w_cut) := fun {c} => by
    have hdom : IntegrableOn (fun u : ℝ => ∑ i ∈ s, |α i c| * ((1 + |u|) * |(B i (u : ℂ)).re|)) (Ici w_cut) :=
      finset_sum_integrableOn s _ _ fun i hi => (hmom_i i hi).const_mul _
    refine hdom.mono' (((continuous_const.add continuous_abs).mul hD_cont.abs).aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u _
    rw [Real.norm_of_nonneg (by positivity), hD_eq]
    calc (1 + |u|) * |∑ i ∈ s, α i c * (B i (u : ℂ)).re|
        ≤ (1 + |u|) * ∑ i ∈ s, |α i c| * |(B i (u : ℂ)).re| := by
          refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans_eq ?_) (by positivity)
          exact Finset.sum_congr rfl fun i _ => abs_mul _ _
      _ = ∑ i ∈ s, |α i c| * ((1 + |u|) * |(B i (u : ℂ)).re|) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have hD_mom_bd : ∀ {c : ℝ}, c_min ≤ c → ∫ u in Ici w_cut, (1 + |u|) * |D c u| ≤ M_mom := by
    intro c hc
    have hsum_int : IntegrableOn (fun u : ℝ => ∑ i ∈ s, (1 + |u|) * |(B i (u : ℂ)).re|) (Ici w_cut) :=
      finset_sum_integrableOn s _ _ fun i hi => hmom_i i hi
    have hdom : IntegrableOn (fun u : ℝ => R * ∑ i ∈ s, (1 + |u|) * |(B i (u : ℂ)).re|) (Ici w_cut) :=
      hsum_int.const_mul R
    have hpt : ∀ u ∈ Ici w_cut, (1 + |u|) * |D c u| ≤ R * ∑ i ∈ s, (1 + |u|) * |(B i (u : ℂ)).re| := fun u _ => by
      rw [hD_eq]
      calc (1 + |u|) * |∑ i ∈ s, α i c * (B i (u : ℂ)).re|
          ≤ (1 + |u|) * ∑ i ∈ s, R * |(B i (u : ℂ)).re| := by
            refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans ?_) (by positivity)
            refine Finset.sum_le_sum fun i hi => ?_
            rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hα i hi c hc) (abs_nonneg _)
        _ = R * ∑ i ∈ s, (1 + |u|) * |(B i (u : ℂ)).re| := by
            rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    refine (setIntegral_mono_on hD_mom_int hdom measurableSet_Ici hpt).trans_eq ?_
    rw [integral_const_mul, finset_sum_setIntegral s _ _ fun i hi => hmom_i i hi]
  let L1_D : ℝ := C_neg * (∫ u in Iic (0 : ℝ), (1 + |u|) ^ (-(3 / 2 : ℝ))) + M_mom
  have hL1_D : 0 ≤ L1_D := by
    have : 0 ≤ ∫ u in Iic (0 : ℝ), (1 + |u|) ^ (-(3 / 2 : ℝ)) :=
      setIntegral_nonneg measurableSet_Iic fun _ _ => by positivity
    positivity
  have hD_L1_int : ∀ {c : ℝ}, Integrable (fun u : ℝ => |D c u|) := fun {c} => by
    have h_eq : (fun u : ℝ => ‖(D c u : ℂ) * Complex.exp (0 * (u : ℂ))‖) =ᵐ[volume] fun u : ℝ => |D c u| :=
      ae_of_all _ fun u => by simp [Complex.norm_real]
    exact (hUD.integrable 0 le_rfl).norm.congr h_eq
  have hD_L1_bd : ∀ {c : ℝ}, c_min ≤ c → ∫ u : ℝ, |D c u| ≤ L1_D := by
    intro c hc
    have hsplit : ∫ u : ℝ, |D c u| = (∫ u in Iic (0 : ℝ), |D c u|) + ∫ u in Ioi (0 : ℝ), |D c u| := by
      rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        hD_L1_int.integrableOn hD_L1_int.integrableOn, Iic_union_Ioi, setIntegral_univ]
    have hleft : ∫ u in Iic (0 : ℝ), |D c u| ≤ C_neg * ∫ u in Iic (0 : ℝ), (1 + |u|) ^ (-(3 / 2 : ℝ)) := by
      have hdom := integrableOn_neg_tail_rpow_three_halves C_neg hC_neg
      have := setIntegral_mono_on hD_L1_int.integrableOn hdom measurableSet_Iic fun u hu => hD_neg_bd hc hu
      rwa [integral_const_mul] at this
    have hright : ∫ u in Ioi (0 : ℝ), |D c u| ≤ M_mom := by
      have hsub : Ioi (0 : ℝ) ⊆ Ici w_cut := fun u hu => hw_cut.trans (mem_Ioi.mp hu).le
      have h1 : ∫ u in Ioi (0 : ℝ), |D c u| ≤ ∫ u in Ioi (0 : ℝ), (1 + |u|) * |D c u| := by
        refine setIntegral_mono_on hD_L1_int.integrableOn (hD_mom_int.mono_set hsub) measurableSet_Ioi fun u _ => ?_
        exact le_mul_of_one_le_left (abs_nonneg _) (by linarith [abs_nonneg u])
      have h2 : ∫ u in Ioi (0 : ℝ), (1 + |u|) * |D c u| ≤ ∫ u in Ici w_cut, (1 + |u|) * |D c u| :=
        setIntegral_mono_set hD_mom_int (ae_of_all _ fun _ => by positivity) hsub.eventuallySubset
      exact h1.trans (h2.trans (hD_mom_bd hc))
    rw [hsplit]; exact add_le_add hleft hright
  have hWD_i_exists : ∀ i ∈ s, ∃ C > 0, ∀ w : ℂ, 0 ≤ w.re →
      ‖airyTwistedLaplaceC (fun u : ℝ => (B i (u : ℂ)).re) ((ceCs : ℂ) * w)‖ ≤ C * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) :=
    fun i hi => (hasU2_of_genRational (hB i hi)).rhp
  choose CW_i hCW_pos hCW_bd using hWD_i_exists
  let C_D : ℝ := R * (∑ i ∈ s, if hi : i ∈ s then CW_i i hi else 0) + 1
  have hC_D : 0 < C_D := by
    have hnn : 0 ≤ ∑ i ∈ s, if hi : i ∈ s then CW_i i hi else 0 :=
      Finset.sum_nonneg fun i hi => by split_ifs; exact (hCW_pos i hi).le
    positivity
  have hD_lap_unif : ∀ {c : ℝ} {w : ℂ}, c_min ≤ c → 0 ≤ w.re →
      ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤ C_D := by
    intro c w hc hw
    have h1w : 1 ≤ ‖1 + w‖ := by
      have := Complex.re_le_norm (1 + w)
      simp only [Complex.add_re, Complex.one_re] at this; linarith
    have hpow1 : ‖1 + w‖ ^ (-(5 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos h1w (by norm_num)
    have hsplit : airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w) =
        ∑ i ∈ s, (α i c : ℂ) * airyTwistedLaplaceC (fun u : ℝ => (B i (u : ℂ)).re) ((ceCs : ℂ) * w) := by
      have hfn : D c = fun u : ℝ => ∑ i ∈ s, α i c * (B i (u : ℂ)).re := funext fun u => hD_eq
      rw [hfn]
      exact airyTwistedLaplaceC_finset_sum s B b₀₀ b₁₁ hB (fun i => α i c) hw
    rw [hsplit]
    calc ‖∑ i ∈ s, (α i c : ℂ) * airyTwistedLaplaceC (fun u : ℝ => (B i (u : ℂ)).re) ((ceCs : ℂ) * w)‖
        ≤ ∑ i ∈ s, ‖(α i c : ℂ) * airyTwistedLaplaceC (fun u : ℝ => (B i (u : ℂ)).re) ((ceCs : ℂ) * w)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i ∈ s, R * ((if hi : i ∈ s then CW_i i hi else 0) * 1) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; split_ifs
          have hbi := (hCW_bd i hi w hw).trans (mul_le_of_le_one_right (hCW_pos i hi).le hpow1)
          exact mul_le_mul (hα i hi c hc) (by simpa using hbi) (norm_nonneg _) hR
      _ = R * (∑ i ∈ s, if hi : i ∈ s then CW_i i hi else 0) := by
          simp_rw [mul_one, ← Finset.mul_sum]
      _ ≤ C_D := by dsimp [C_D]; linarith
  have hWD_unif : ∀ {c : ℝ} {w : ℂ}, c_min ≤ c → 0 ≤ w.re →
      ‖liftSymbol (D c) (δ₀ c) m w‖ ≤ C_D := by
    intro c w hc hw
    unfold liftSymbol
    rw [norm_mul]
    exact (mul_le_mul (norm_liftMultiplier_le_one (hδ0 hc) m hw) (hD_lap_unif hc hw)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hD_lap_int_bd : ∀ {c v : ℝ}, c_min ≤ c →
      ‖∫ u : ℝ, (D c u : ℂ) * Complex.exp (((ceCs : ℂ) * ((v : ℂ) * Complex.I)) * (u : ℂ))‖ ≤ L1_D := by
    intro c v hc
    refine (norm_integral_le_of_norm_le hD_L1_int (ae_of_all _ fun u => ?_)).trans (hD_L1_bd hc)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
      show (((ceCs : ℂ) * ((v : ℂ) * Complex.I)) * (u : ℂ)).re = 0 by simp, Real.exp_zero, mul_one]
  have hD_osc_right : ∀ {c v : ℝ}, c_min ≤ c →
      ‖∫ u in Ici w_cut, (D c u : ℂ) * (Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ)) - 1)‖ ≤
        ceCs * M_mom * |v| := by
    intro c v hc
    have hdom : IntegrableOn (fun u : ℝ => ceCs * |v| * ((1 + |u|) * |D c u|)) (Ici w_cut) :=
      hD_mom_int.const_mul _
    refine (norm_integral_le_of_norm_le hdom ?_).trans ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with u _
      have hosc : ‖Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ)) - 1‖ ≤ ceCs * |v| * (1 + |u|) := by
        have heq : Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ) = -((-(((ceCs * v * u : ℝ) : ℂ)) * Complex.I)) := by
          push_cast; ring
        have h1 := norm_one_sub_exp_neg_le (v := (-(((ceCs * v * u : ℝ) : ℂ)) * Complex.I)) (by simp)
        rw [norm_sub_rev, ← heq] at h1
        have hn : ‖-(((ceCs * v * u : ℝ) : ℂ)) * Complex.I‖ = ceCs * |v| * |u| := by
          rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
            abs_of_pos hcs0, Complex.norm_I, mul_one]
        rw [hn] at h1
        exact (h1.trans (min_le_left _ _)).trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |D c u| * ‖Complex.exp (Complex.I * ((ceCs * v : ℝ) : ℂ) * (u : ℂ)) - 1‖
          ≤ |D c u| * (ceCs * |v| * (1 + |u|)) := mul_le_mul_of_nonneg_left hosc (abs_nonneg _)
        _ = ceCs * |v| * ((1 + |u|) * |D c u|) := by ring
    · rw [integral_const_mul]
      calc ceCs * |v| * ∫ u in Ici w_cut, (1 + |u|) * |D c u|
          ≤ ceCs * |v| * M_mom := mul_le_mul_of_nonneg_left (hD_mom_bd hc) (by positivity)
        _ = ceCs * M_mom * |v| := by ring
  exact ⟨⟨C_neg, hC_neg, M_mom, hM_mom, L1_D, hL1_D, C_D, hC_D, 0, le_rfl, hUD, hD_cont,
    hD_neg_bd, hD_mom_int, hD_mom_bd, hD_L1_int, hD_L1_bd, hWD_unif, hD_lap_unif, hD_lap_int_bd, hD_osc_right⟩⟩

/-- Verify `StripM1 (W_tilde c)` for `W_tilde c ζ = liftSymbol (S c) (δ₀ c) m (ζ/ε) + liftSymbol (D c) (δ₀ c) m ((1-ζ)/ε)`. -/
lemma twoEdge_W_tilde_stripM1 {S D : ℝ → ℝ → ℝ} {δ₀ : ℝ → ℝ} {m : ℕ} {c : ℝ}
    (hc4 : 4 ≤ c) (hUS : HasU2 (S c)) (hUD : HasU2 (D c)) (hδ0 : 0 ≤ δ₀ c) :
    StripM1 (fun ζ => liftSymbol (S c) (δ₀ c) m (ζ / (liftEps c : ℂ)) +
      liftSymbol (D c) (δ₀ c) m ((1 - ζ) / (liftEps c : ℂ))) := by
  have hc0 : 0 < c := by linarith
  have hε : 0 < liftEps c := liftEps_pos hc0
  have hε1 : liftEps c ≤ 1 := liftEps_le_one (by linarith)
  have hSdata := liftSymbolData_of_hasU2 hUS hδ0 m
  have hDdata := liftSymbolData_of_hasU2 hUD hδ0 m
  obtain ⟨BS, hBS⟩ := hSdata.bound
  obtain ⟨BD, hBD⟩ := hDdata.bound
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine DifferentiableOn.add ?_ ?_
    · exact hSdata.diff.comp ((differentiableOn_id).div_const _) fun ζ hζ => by
        change 0 < (ζ / (liftEps c : ℂ)).re; rw [Complex.div_ofReal_re]; exact div_pos hζ.1 hε
    · exact hDdata.diff.comp (((differentiableOn_const 1).sub differentiableOn_id).div_const _) fun ζ hζ => by
        change 0 < ((1 - ζ) / (liftEps c : ℂ)).re
        rw [Complex.div_ofReal_re, Complex.sub_re, Complex.one_re]; exact div_pos (sub_pos.mpr hζ.2) hε
  · refine ContinuousOn.add ?_ ?_
    · exact hSdata.cont.comp (continuousOn_id.div_const _) fun ζ hζ => by
        change 0 ≤ (ζ / (liftEps c : ℂ)).re; rw [Complex.div_ofReal_re]; exact div_nonneg hζ.1 hε.le
    · exact hDdata.cont.comp ((continuousOn_const.sub continuousOn_id).div_const _) fun ζ hζ => by
        change 0 ≤ ((1 - ζ) / (liftEps c : ℂ)).re
        rw [Complex.div_ofReal_re, Complex.sub_re, Complex.one_re]; exact div_nonneg (sub_nonneg.mpr hζ.2) hε.le
  · intro ζ _ _
    have hconj_div : starRingEnd ℂ ζ / (liftEps c : ℂ) = starRingEnd ℂ (ζ / (liftEps c : ℂ)) := by simp
    have hconj_sub : (1 - starRingEnd ℂ ζ) / (liftEps c : ℂ) = starRingEnd ℂ ((1 - ζ) / (liftEps c : ℂ)) := by simp
    rw [hconj_div, hconj_sub, liftSymbol_conj, liftSymbol_conj, map_add]
  · refine ⟨max BS 0 + max BD 0, fun ζ h0 h1 => ?_⟩
    have hS0 : 0 ≤ (ζ / (liftEps c : ℂ)).re := by rw [Complex.div_ofReal_re]; exact div_nonneg h0 hε.le
    have hD0 : 0 ≤ ((1 - ζ) / (liftEps c : ℂ)).re := by
      rw [Complex.div_ofReal_re, Complex.sub_re, Complex.one_re]; exact div_nonneg (sub_nonneg.mpr h1) hε.le
    have him_eq : |(ζ / (liftEps c : ℂ)).im| = |ζ.im| / liftEps c := by
      rw [Complex.div_ofReal_im, abs_div, abs_of_pos hε]
    have him_eq2 : |((1 - ζ) / (liftEps c : ℂ)).im| = |ζ.im| / liftEps c := by
      rw [Complex.div_ofReal_im, Complex.sub_im, Complex.one_im, zero_sub, abs_div, abs_neg, abs_of_pos hε]
    have hpow_le : (1 + |ζ.im| / liftEps c) ^ (-(5 / 2 : ℝ)) ≤ (1 + |ζ.im|) ^ (-(2 : ℝ)) := by
      have h1_le : 1 + |ζ.im| ≤ 1 + |ζ.im| / liftEps c := by
        have : |ζ.im| ≤ |ζ.im| / liftEps c := le_div_self (abs_nonneg _) hε hε1
        linarith
      calc (1 + |ζ.im| / liftEps c) ^ (-(5 / 2 : ℝ)) ≤ (1 + |ζ.im|) ^ (-(5 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) h1_le (by norm_num)
        _ ≤ (1 + |ζ.im|) ^ (-(2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg ζ.im]) (by norm_num)
    have hbS' : ‖liftSymbol (S c) (δ₀ c) m (ζ / (liftEps c : ℂ))‖ ≤ max BS 0 * (1 + |ζ.im|) ^ (-(2 : ℝ)) := by
      have h := hBS _ hS0; rw [him_eq] at h
      exact h.trans (mul_le_mul (le_max_left _ _) hpow_le (by positivity) (le_max_right _ _))
    have hbD' : ‖liftSymbol (D c) (δ₀ c) m ((1 - ζ) / (liftEps c : ℂ))‖ ≤ max BD 0 * (1 + |ζ.im|) ^ (-(2 : ℝ)) := by
      have h := hBD _ hD0; rw [him_eq2] at h
      exact h.trans (mul_le_mul (le_max_left _ _) hpow_le (by positivity) (le_max_right _ _))
    exact (norm_add_le _ _).trans ((add_le_add hbS' hbD').trans_eq (by ring))

/-- `1/2`-Hölder continuity of `W_tilde c` at `ζ = 1` for fixed `c ≥ 216`. -/
lemma twoEdge_W_tilde_holder {ι : Type*} (s : Finset ι) (B : ι → ℂ → ℂ) (b₀₀ b₁₁ : ι → ℝ)
    (hB : ∀ i ∈ s, HasGenRationalAiryCoeffs (B i) (b₀₀ i) (b₁₁ i))
    (α : ι → ℝ → ℝ) {R w_cut c_min : ℝ} (hR : 0 ≤ R) (hc216 : 216 ≤ c_min)
    (m : ℕ) (hm : 1 ≤ m) (δ₀ : ℝ → ℝ) (hδ0 : ∀ {c : ℝ}, c_min ≤ c → 0 ≤ δ₀ c)
    (S D : ℝ → ℝ → ℝ) (hUS : ∀ {c : ℝ}, c_min ≤ c → HasU2 (S c))
    (hD_eq : ∀ {c u : ℝ}, D c u = ∑ i ∈ s, α i c * (B i (u : ℂ)).re)
    (hα : ∀ i ∈ s, ∀ c : ℝ, c_min ≤ c → |α i c| ≤ R)
    (db : TwoEdgeDualBounds s B b₀₀ b₁₁ α D δ₀ m w_cut c_min)
    {c : ℝ} (hc : c_min ≤ c) :
    ∃ CH : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖1 - ζ‖ ≤ 1 / 2 →
      ‖(liftSymbol (S c) (δ₀ c) m (ζ / (liftEps c : ℂ)) + liftSymbol (D c) (δ₀ c) m ((1 - ζ) / (liftEps c : ℂ))) -
        (liftSymbol (S c) (δ₀ c) m ((1 : ℂ) / (liftEps c : ℂ)) + liftSymbol (D c) (δ₀ c) m ((1 - (1 : ℂ)) / (liftEps c : ℂ)))‖ ≤
        CH * ‖1 - ζ‖ ^ (1 / 2 : ℝ) := by
  classical
  have hcs0 : 0 < ceCs := ceCs_pos
  have hc0 : 0 < c := by linarith
  have hε : 0 < liftEps c := liftEps_pos hc0
  have hδc : 0 ≤ δ₀ c := hδ0 hc
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hSdata := liftSymbolData_of_hasU2 (hUS hc) hδc m
  have hdiffS : DifferentiableOn ℂ (fun ζ => liftSymbol (S c) (δ₀ c) m (ζ / (liftEps c : ℂ))) {ζ : ℂ | 0 < ζ.re} :=
    hSdata.diff.comp (differentiableOn_id.div_const _) fun ζ hζ => by
      change 0 < (ζ / (liftEps c : ℂ)).re; rw [Complex.div_ofReal_re]; exact div_pos hζ hε
  have hballS : Metric.closedBall (1 : ℂ) (1 / 2) ⊆ {ζ : ℂ | 0 < ζ.re} := fun ζ hζ => by
    have hre : |ζ.re - 1| ≤ 1 / 2 :=
      (by simp : |ζ.re - 1| = |(ζ - 1).re|) ▸ (Complex.abs_re_le_norm _).trans (mem_closedBall_iff_norm.mp hζ)
    change 0 < ζ.re; linarith [(abs_le.mp hre).1]
  have hderivS_cont : ContinuousOn (deriv fun ζ => liftSymbol (S c) (δ₀ c) m (ζ / (liftEps c : ℂ)))
      (Metric.closedBall (1 : ℂ) (1 / 2)) :=
    (hdiffS.deriv (isOpen_lt continuous_const Complex.continuous_re)).continuousOn.mono hballS
  obtain ⟨MS, hMS⟩ := (isCompact_closedBall (1 : ℂ) (1 / 2)).exists_bound_of_continuousOn hderivS_cont
  have hS_lip : ∀ ζ : ℂ, ‖1 - ζ‖ ≤ 1 / 2 →
      ‖liftSymbol (S c) (δ₀ c) m (ζ / (liftEps c : ℂ)) - liftSymbol (S c) (δ₀ c) m ((1 : ℂ) / (liftEps c : ℂ))‖ ≤
        |MS| * ‖1 - ζ‖ := fun ζ hζ => by
    have hmem1 : (1 : ℂ) ∈ Metric.closedBall (1 : ℂ) (1 / 2) := Metric.mem_closedBall_self (by norm_num)
    have hmemζ : ζ ∈ Metric.closedBall (1 : ℂ) (1 / 2) := by
      rw [mem_closedBall_iff_norm, norm_sub_rev]; exact hζ
    have hmv := (convex_closedBall (1 : ℂ) (1 / 2)).norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hdiffS z (hballS hz)).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (hballS hz)))
      (fun z hz => (hMS z hz).trans (le_abs_self MS)) hmem1 hmemζ
    rwa [norm_sub_rev ζ 1] at hmv
  let R_loc : ℝ := ceCs / (2 * liftEps c) + 1
  have hR_loc : 0 ≤ R_loc := by positivity
  have hBi_loc : ∀ i ∈ s, ∃ Ci > 0, ∀ y : ℂ, 0 ≤ y.re → ‖y‖ ≤ R_loc →
      ‖airyTwistedLaplaceC (fun u : ℝ => (B i (u : ℂ)).re) y -
        airyTwistedLaplaceC (fun u : ℝ => (B i (u : ℂ)).re) 0‖ ≤ Ci * ‖y‖ ^ (1 / 2 : ℝ) := by
    intro i hi
    obtain ⟨Ce, _, hce⟩ := u1c_expansion_of_genRational (hB i hi) R_loc hR_loc
    let Ci : ℝ := |(b₀₀ i + b₁₁ i) * (2 * ceK * cA)| + Ce * Real.sqrt R_loc + 1
    refine ⟨Ci, by positivity, fun y hy hyn => ?_⟩
    have hy_pow : ‖y‖ ≤ Real.sqrt R_loc * ‖y‖ ^ (1 / 2 : ℝ) := by
      calc ‖y‖ = ‖y‖ ^ (1 / 2 : ℝ) * ‖y‖ ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_add_of_nonneg (norm_nonneg y) (by norm_num) (by norm_num)]; norm_num
        _ ≤ Real.sqrt R_loc * ‖y‖ ^ (1 / 2 : ℝ) := by
            rw [Real.sqrt_eq_rpow]
            exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (norm_nonneg y) hyn (by norm_num)) (by positivity)
    have hterm : ‖(((b₀₀ i + b₁₁ i) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)‖ =
        |(b₀₀ i + b₁₁ i) * (2 * ceK * cA)| * ‖y‖ ^ (1 / 2 : ℝ) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cpow_half_eq]
    calc ‖airyTwistedLaplaceC (fun u : ℝ => (B i (u : ℂ)).re) y -
            airyTwistedLaplaceC (fun u : ℝ => (B i (u : ℂ)).re) 0‖
        = ‖(airyTwistedLaplaceC (fun u : ℝ => (B i (u : ℂ)).re) y -
            airyTwistedLaplaceC (fun u : ℝ => (B i (u : ℂ)).re) 0 +
            (((b₀₀ i + b₁₁ i) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)) -
            (((b₀₀ i + b₁₁ i) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)‖ := by ring_nf
      _ ≤ ‖airyTwistedLaplaceC (fun u : ℝ => (B i (u : ℂ)).re) y -
            airyTwistedLaplaceC (fun u : ℝ => (B i (u : ℂ)).re) 0 +
            (((b₀₀ i + b₁₁ i) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)‖ +
            ‖(((b₀₀ i + b₁₁ i) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)‖ := norm_sub_le _ _
      _ ≤ Ce * ‖y‖ + |(b₀₀ i + b₁₁ i) * (2 * ceK * cA)| * ‖y‖ ^ (1 / 2 : ℝ) := by
          rw [hterm]; exact add_le_add (hce hy hyn) le_rfl
      _ ≤ Ci * ‖y‖ ^ (1 / 2 : ℝ) := by
          have h1 : Ce * ‖y‖ ≤ Ce * Real.sqrt R_loc * ‖y‖ ^ (1 / 2 : ℝ) :=
            (mul_le_mul_of_nonneg_left hy_pow (by positivity)).trans_eq (by ring)
          have h2 : |(b₀₀ i + b₁₁ i) * (2 * ceK * cA)| + Ce * Real.sqrt R_loc ≤ Ci := by
            dsimp [Ci]; linarith
          calc Ce * ‖y‖ + |(b₀₀ i + b₁₁ i) * (2 * ceK * cA)| * ‖y‖ ^ (1 / 2 : ℝ)
              ≤ (|(b₀₀ i + b₁₁ i) * (2 * ceK * cA)| + Ce * Real.sqrt R_loc) * ‖y‖ ^ (1 / 2 : ℝ) := by linarith
            _ ≤ Ci * ‖y‖ ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_right h2 (by positivity)
  choose CL_i hCL_pos hCL_bd using hBi_loc
  let CL_D : ℝ := R * ∑ i ∈ s, if hi : i ∈ s then CL_i i hi else 0
  let Rb : ℝ := ceCs * δ₀ c / (m : ℝ) / (2 * liftEps c) + 1
  have hRb_nn : 0 ≤ Rb := by positivity
  obtain ⟨Cm_c, hCm_c, hbm_c⟩ := norm_bsplineE1_pow_sub_one_le m hRb_nn
  let CH : ℝ := |MS| + Cm_c * (ceCs * δ₀ c / (m : ℝ) / liftEps c) * db.C_D + CL_D * (ceCs / liftEps c) ^ (1 / 2 : ℝ)
  refine ⟨CH, fun ζ _ h1 hζ => ?_⟩
  have hD_re0 : 0 ≤ ((1 - ζ) / (liftEps c : ℂ)).re := by
    rw [Complex.div_ofReal_re, Complex.sub_re, Complex.one_re]; exact div_nonneg (sub_nonneg.mpr h1) hε.le
  have hw_norm : ‖(1 - ζ) / (liftEps c : ℂ)‖ ≤ 1 / (2 * liftEps c) := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hε.le, div_eq_mul_inv,
      show (1 : ℝ) / (2 * liftEps c) = (1 / 2) * (liftEps c)⁻¹ by ring]
    exact mul_le_mul_of_nonneg_right hζ (inv_nonneg.mpr hε.le)
  have hmult_sub : ‖liftMultiplier (δ₀ c) m ((1 - ζ) / (liftEps c : ℂ)) - 1‖ ≤
      Cm_c * (ceCs * δ₀ c / (m : ℝ) / liftEps c) * ‖1 - ζ‖ := by
    unfold liftMultiplier
    have harg_le : ‖(((ceCs * δ₀ c / (m : ℝ) : ℝ) : ℂ) * ((1 - ζ) / (liftEps c : ℂ)))‖ ≤ Rb := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      calc (ceCs * δ₀ c / (m : ℝ)) * ‖(1 - ζ) / (liftEps c : ℂ)‖
          ≤ (ceCs * δ₀ c / (m : ℝ)) * (1 / (2 * liftEps c)) := mul_le_mul_of_nonneg_left hw_norm (by positivity)
        _ = ceCs * δ₀ c / (m : ℝ) / (2 * liftEps c) := by ring
        _ ≤ Rb := by dsimp [Rb]; linarith
    calc ‖bsplineE1 (((ceCs * δ₀ c / (m : ℝ) : ℝ) : ℂ) * ((1 - ζ) / (liftEps c : ℂ))) ^ m - 1‖
        ≤ Cm_c * ‖(((ceCs * δ₀ c / (m : ℝ) : ℝ) : ℂ) * ((1 - ζ) / (liftEps c : ℂ)))‖ := hbm_c _ harg_le
      _ = Cm_c * ((ceCs * δ₀ c / (m : ℝ)) * (‖1 - ζ‖ / liftEps c)) := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
            norm_div, Complex.norm_real, Real.norm_of_nonneg hε.le]
      _ = Cm_c * (ceCs * δ₀ c / (m : ℝ) / liftEps c) * ‖1 - ζ‖ := by ring
  have hD0_eq : liftSymbol (D c) (δ₀ c) m ((1 - (1 : ℂ)) / (liftEps c : ℂ)) = airyTwistedLaplaceC (D c) 0 := by
    simp [liftSymbol, liftMultiplier, bsplineE1_zero]
  have hD_lap_sub : ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * ((1 - ζ) / (liftEps c : ℂ))) -
        airyTwistedLaplaceC (D c) 0‖ ≤ CL_D * (ceCs / liftEps c) ^ (1 / 2 : ℝ) * ‖1 - ζ‖ ^ (1 / 2 : ℝ) := by
    have hfn : D c = fun u : ℝ => ∑ i ∈ s, α i c * (B i (u : ℂ)).re := funext fun u => hD_eq
    have hsplit_w := airyTwistedLaplaceC_finset_sum s B b₀₀ b₁₁ hB (fun i => α i c) hD_re0
    have hsplit_0 := airyTwistedLaplaceC_finset_sum s B b₀₀ b₁₁ hB (fun i => α i c) (w := 0) le_rfl
    rw [hfn, hsplit_w, show airyTwistedLaplaceC (fun u : ℝ => ∑ i ∈ s, α i c * (B i (u : ℂ)).re) 0 =
        ∑ i ∈ s, (α i c : ℂ) * airyTwistedLaplaceC (fun u : ℝ => (B i (u : ℂ)).re) 0 by
      simpa [mul_zero] using hsplit_0, ← Finset.sum_sub_distrib]
    have hy_le : ‖(ceCs : ℂ) * ((1 - ζ) / (liftEps c : ℂ))‖ ≤ R_loc := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hcs0.le]
      calc ceCs * ‖(1 - ζ) / (liftEps c : ℂ)‖ ≤ ceCs * (1 / (2 * liftEps c)) := mul_le_mul_of_nonneg_left hw_norm hcs0.le
        _ = ceCs / (2 * liftEps c) := by ring
        _ ≤ R_loc := by dsimp [R_loc]; linarith
    have hy_re : 0 ≤ ((ceCs : ℂ) * ((1 - ζ) / (liftEps c : ℂ))).re := by
      rw [Complex.re_ofReal_mul]; exact mul_nonneg hcs0.le hD_re0
    have hnorm_y : ‖(ceCs : ℂ) * ((1 - ζ) / (liftEps c : ℂ))‖ ^ (1 / 2 : ℝ) =
        (ceCs / liftEps c) ^ (1 / 2 : ℝ) * ‖1 - ζ‖ ^ (1 / 2 : ℝ) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hcs0.le, norm_div, Complex.norm_real,
        Real.norm_of_nonneg hε.le, show ceCs * (‖1 - ζ‖ / liftEps c) = (ceCs / liftEps c) * ‖1 - ζ‖ by ring,
        Real.mul_rpow (by positivity) (norm_nonneg _)]
    calc ‖∑ i ∈ s, ((α i c : ℂ) * airyTwistedLaplaceC (fun u : ℝ => (B i (u : ℂ)).re) ((ceCs : ℂ) * ((1 - ζ) / (liftEps c : ℂ))) -
            (α i c : ℂ) * airyTwistedLaplaceC (fun u : ℝ => (B i (u : ℂ)).re) 0)‖
        ≤ ∑ i ∈ s, ‖(α i c : ℂ) * (airyTwistedLaplaceC (fun u : ℝ => (B i (u : ℂ)).re) ((ceCs : ℂ) * ((1 - ζ) / (liftEps c : ℂ))) -
            airyTwistedLaplaceC (fun u : ℝ => (B i (u : ℂ)).re) 0)‖ := by
          refine (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun i _ => ?_); rw [mul_sub]
      _ ≤ ∑ i ∈ s, R * ((if hi : i ∈ s then CL_i i hi else 0) * ((ceCs / liftEps c) ^ (1 / 2 : ℝ) * ‖1 - ζ‖ ^ (1 / 2 : ℝ))) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; split_ifs
          exact mul_le_mul (hα i hi c hc) ((hCL_bd i hi _ hy_re hy_le).trans_eq (by rw [hnorm_y]))
            (norm_nonneg _) hR
      _ = CL_D * (ceCs / liftEps c) ^ (1 / 2 : ℝ) * ‖1 - ζ‖ ^ (1 / 2 : ℝ) := by
          dsimp [CL_D]; simp_rw [← mul_assoc, ← Finset.sum_mul, ← Finset.mul_sum]
  have hD_lap_bd : ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * ((1 - ζ) / (liftEps c : ℂ)))‖ ≤ db.C_D :=
    db.hD_lap_unif hc hD_re0
  have h1ζ_sqrt : ‖1 - ζ‖ ≤ ‖1 - ζ‖ ^ (1 / 2 : ℝ) := by
    have h11 : ‖1 - ζ‖ ≤ 1 := by linarith
    calc ‖1 - ζ‖ = ‖1 - ζ‖ ^ (1 / 2 : ℝ) * ‖1 - ζ‖ ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add_of_nonneg (norm_nonneg _) (by norm_num) (by norm_num)]; norm_num
      _ ≤ 1 * ‖1 - ζ‖ ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_one (norm_nonneg _) h11 (by norm_num)) (by positivity)
      _ = ‖1 - ζ‖ ^ (1 / 2 : ℝ) := one_mul _
  have hD_sub : ‖liftSymbol (D c) (δ₀ c) m ((1 - ζ) / (liftEps c : ℂ)) -
        liftSymbol (D c) (δ₀ c) m ((1 - (1 : ℂ)) / (liftEps c : ℂ))‖ ≤
      (Cm_c * (ceCs * δ₀ c / (m : ℝ) / liftEps c) * db.C_D + CL_D * (ceCs / liftEps c) ^ (1 / 2 : ℝ)) *
        ‖1 - ζ‖ ^ (1 / 2 : ℝ) := by
    rw [hD0_eq]
    have hdecomp : liftSymbol (D c) (δ₀ c) m ((1 - ζ) / (liftEps c : ℂ)) - airyTwistedLaplaceC (D c) 0 =
        (liftMultiplier (δ₀ c) m ((1 - ζ) / (liftEps c : ℂ)) - 1) *
          airyTwistedLaplaceC (D c) ((ceCs : ℂ) * ((1 - ζ) / (liftEps c : ℂ))) +
          (airyTwistedLaplaceC (D c) ((ceCs : ℂ) * ((1 - ζ) / (liftEps c : ℂ))) - airyTwistedLaplaceC (D c) 0) := by
      unfold liftSymbol; ring
    rw [hdecomp]
    calc ‖(liftMultiplier (δ₀ c) m ((1 - ζ) / (liftEps c : ℂ)) - 1) *
            airyTwistedLaplaceC (D c) ((ceCs : ℂ) * ((1 - ζ) / (liftEps c : ℂ))) +
            (airyTwistedLaplaceC (D c) ((ceCs : ℂ) * ((1 - ζ) / (liftEps c : ℂ))) - airyTwistedLaplaceC (D c) 0)‖
        ≤ ‖liftMultiplier (δ₀ c) m ((1 - ζ) / (liftEps c : ℂ)) - 1‖ *
            ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * ((1 - ζ) / (liftEps c : ℂ)))‖ +
            ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * ((1 - ζ) / (liftEps c : ℂ))) - airyTwistedLaplaceC (D c) 0‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
      _ ≤ (Cm_c * (ceCs * δ₀ c / (m : ℝ) / liftEps c) * ‖1 - ζ‖) * db.C_D +
            CL_D * (ceCs / liftEps c) ^ (1 / 2 : ℝ) * ‖1 - ζ‖ ^ (1 / 2 : ℝ) :=
          add_le_add (mul_le_mul hmult_sub hD_lap_bd (norm_nonneg _) (by positivity)) hD_lap_sub
      _ ≤ (Cm_c * (ceCs * δ₀ c / (m : ℝ) / liftEps c) * ‖1 - ζ‖ ^ (1 / 2 : ℝ)) * db.C_D +
            CL_D * (ceCs / liftEps c) ^ (1 / 2 : ℝ) * ‖1 - ζ‖ ^ (1 / 2 : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h1ζ_sqrt (mul_nonneg hCm_c (by positivity))) db.hC_D.le) le_rfl
      _ = _ := by ring
  calc ‖(liftSymbol (S c) (δ₀ c) m (ζ / (liftEps c : ℂ)) + liftSymbol (D c) (δ₀ c) m ((1 - ζ) / (liftEps c : ℂ))) -
          (liftSymbol (S c) (δ₀ c) m ((1 : ℂ) / (liftEps c : ℂ)) + liftSymbol (D c) (δ₀ c) m ((1 - (1 : ℂ)) / (liftEps c : ℂ)))‖
      ≤ ‖liftSymbol (S c) (δ₀ c) m (ζ / (liftEps c : ℂ)) - liftSymbol (S c) (δ₀ c) m ((1 : ℂ) / (liftEps c : ℂ))‖ +
          ‖liftSymbol (D c) (δ₀ c) m ((1 - ζ) / (liftEps c : ℂ)) -
            liftSymbol (D c) (δ₀ c) m ((1 - (1 : ℂ)) / (liftEps c : ℂ))‖ := by
        rw [show (a b c d : ℂ) → (a + b) - (c + d) = (a - c) + (b - d) by intros; ring]
        exact norm_add_le _ _
    _ ≤ |MS| * ‖1 - ζ‖ ^ (1 / 2 : ℝ) +
          (Cm_c * (ceCs * δ₀ c / (m : ℝ) / liftEps c) * db.C_D + CL_D * (ceCs / liftEps c) ^ (1 / 2 : ℝ)) *
            ‖1 - ζ‖ ^ (1 / 2 : ℝ) :=
        add_le_add ((hS_lip ζ hζ).trans (mul_le_mul_of_nonneg_left h1ζ_sqrt (abs_nonneg _))) hD_sub
    _ = CH * ‖1 - ζ‖ ^ (1 / 2 : ℝ) := by dsimp [CH]; ring

end FormalResearch.SignUncertainty
