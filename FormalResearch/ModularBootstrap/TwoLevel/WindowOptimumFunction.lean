module

public import FormalResearch.SignUncertainty.ClarkTwoNode

/-!
# The Airy window function `f_K` of the two-level curve (`virasoro_two_level.tex`, Proposition 2.3 `gt:2.3`)

For a Clark angle `α` (`sin α ≠ 0`), `K ≥ 3` and `u₂ ∈ ℝ` the window function is
`f_K(u) = Ai(u)² (u - z₁)(u - u₂) / ((u - a₁)²(u - a₂)²) · ∏_{k=3}^K ((u - z_k)/(u - a_k))²`
with `z_k = clarkNode α k`, `a_k = airyZero k`.  It is the entire function `windowF α K u₂` characterised by
`f_K(u) · ∏_{k=1}^K (u - a_k)² = Ai(u)² (u - z₁)(u - u₂) ∏_{k=3}^K (u - z_k)²`.

* `windowF_spec`: existence of the entire solution, `windowF_bound`: `‖f_K(u)‖ ≤ C (1 + ‖u‖)^{-5/2} e(u)`.
* `windowF_node_hasSum`: the Clark-Airy summation of `f_K` in real node form.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty

/-- `∏_{k=1}^K (u - a_k)`. -/
noncomputable def windowD (K : ℕ) (u : ℂ) : ℂ := ∏ k ∈ Finset.Icc 1 K, (u - (airyZero k : ℂ))

/-- `(u - z₁)(u - u₂) ∏_{k=3}^K (u - z_k)²`. -/
noncomputable def windowN (α : ℝ) (K : ℕ) (u₂ : ℝ) (u : ℂ) : ℂ :=
  (u - (clarkNode α 1 : ℂ)) * (u - (u₂ : ℂ)) * ∏ k ∈ Finset.Icc 3 K, (u - (clarkNode α k : ℂ)) ^ 2

lemma differentiable_windowD (K : ℕ) : Differentiable ℂ (windowD K) := by
  unfold windowD
  fun_prop

lemma differentiable_windowN (α : ℝ) (K : ℕ) (u₂ : ℝ) : Differentiable ℂ (windowN α K u₂) := by
  unfold windowN
  fun_prop


lemma norm_prod_sub_le (s : Finset ℕ) (t : ℕ → ℝ) (u : ℂ) :
    ‖∏ k ∈ s, (u - (t k : ℂ))‖ ≤ (∏ k ∈ s, (1 + |t k|)) * (1 + ‖u‖) ^ s.card := by
  rw [norm_prod]
  calc ∏ k ∈ s, ‖u - (t k : ℂ)‖ ≤ ∏ k ∈ s, ((1 + |t k|) * (1 + ‖u‖)) := by
        refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun k _ => ?_)
        calc ‖u - (t k : ℂ)‖ ≤ ‖u‖ + ‖(t k : ℂ)‖ := norm_sub_le _ _
          _ = ‖u‖ + |t k| := by rw [Complex.norm_real, Real.norm_eq_abs]
          _ ≤ (1 + |t k|) * (1 + ‖u‖) := by nlinarith [abs_nonneg (t k), norm_nonneg u]
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]

lemma norm_prod_sub_ge (s : Finset ℕ) (t : ℕ → ℝ) {u : ℂ} (hu : ∀ k ∈ s, |t k| + 1 ≤ ‖u‖) :
    (1 + ‖u‖) ^ s.card ≤ (∏ k ∈ s, (2 + |t k|)) * ‖∏ k ∈ s, (u - (t k : ℂ))‖ := by
  rw [norm_prod, ← Finset.prod_mul_distrib]
  calc (1 + ‖u‖) ^ s.card = ∏ k ∈ s, (1 + ‖u‖) := by rw [Finset.prod_const]
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => by linarith [norm_nonneg u])
        (fun k hk => by
          have := (norm_sub_ofReal_ge (t := t k) (u := u) (hu k hk)).1
          linarith)

/-- Division of a class-`𝒢` function by the square of a real-rooted polynomial keeps the class and lowers the
exponent by twice the degree. -/
theorem div_bound {φ H : ℂ → ℂ} (hH : Differentiable ℂ H) {s : Finset ℕ} {t : ℕ → ℝ} {C μ : ℝ}
    (hC : 0 ≤ C) (hφ : ∀ u, ‖φ u‖ ≤ C * (1 + ‖u‖) ^ μ * airyEnv u)
    (h : ∀ u, φ u = H u * (∏ k ∈ s, (u - (t k : ℂ))) ^ 2) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ u, ‖H u‖ ≤ C' * (1 + ‖u‖) ^ (μ - 2 * (s.card : ℝ)) * airyEnv u := by
  set ν : ℝ := μ - 2 * (s.card : ℝ) with hν
  set B : ℝ := 1 + ∑ k ∈ s, |t k| with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) B).exists_bound_of_continuousOn hH.continuous.continuousOn
  set e0 : ℝ := Real.exp (-(4 / 3) * B ^ (3 / 2 : ℝ)) with he0
  set m1 : ℝ := min 1 ((1 + B) ^ ν) with hm1
  have he0p : 0 < e0 := Real.exp_pos _
  have hm1p : 0 < m1 := lt_min one_pos (Real.rpow_pos_of_pos (by linarith) _)
  set P : ℝ := ∏ k ∈ s, (2 + |t k|) with hP
  have hPpos : 0 < P := Finset.prod_pos (fun k _ => by positivity)
  refine ⟨max (C * P ^ 2) (|M| / (m1 * e0)), by positivity, fun u => ?_⟩
  by_cases hu : ‖u‖ ≤ B
  · have h1 : ‖H u‖ ≤ |M| := (hM u (by simpa using hu)).trans (le_abs_self _)
    have h2 : m1 * e0 ≤ (1 + ‖u‖) ^ ν * airyEnv u :=
      mul_le_mul (at47_rpow_lower hu) (at47_env_lower hu hB0) he0p.le
        (Real.rpow_nonneg (by linarith [norm_nonneg u]) _)
    have h3 : |M| ≤ |M| / (m1 * e0) * ((1 + ‖u‖) ^ ν * airyEnv u) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    calc ‖H u‖ ≤ |M| / (m1 * e0) * ((1 + ‖u‖) ^ ν * airyEnv u) := h1.trans h3
      _ ≤ max (C * P ^ 2) (|M| / (m1 * e0)) * ((1 + ‖u‖) ^ ν * airyEnv u) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _)
            (mul_nonneg (Real.rpow_nonneg (by positivity) _) (airyEnv_pos u).le)
      _ = _ := by ring
  · replace hu := not_le.mp hu
    have hux : ∀ k ∈ s, |t k| + 1 ≤ ‖u‖ := fun k hk => by
      have : |t k| ≤ ∑ j ∈ s, |t j| := Finset.single_le_sum (f := fun j => |t j|) (fun _ _ => abs_nonneg _) hk
      linarith
    have hge := norm_prod_sub_ge s t hux
    set Dn : ℝ := ‖∏ k ∈ s, (u - (t k : ℂ))‖ with hDn
    have hx : 0 < 1 + ‖u‖ := by positivity
    have hDpos : 0 < Dn := by
      have : 0 < (1 + ‖u‖) ^ s.card := by positivity
      by_contra hle
      have : Dn = 0 := le_antisymm (not_lt.mp hle) (norm_nonneg _)
      rw [this, mul_zero] at hge
      linarith
    have hnorm : ‖φ u‖ = ‖H u‖ * Dn ^ 2 := by rw [h u, norm_mul, norm_pow]
    have hen := airyEnv_pos u
    have hpow : (1 + ‖u‖) ^ ν * (1 + ‖u‖) ^ (2 * (s.card : ℝ)) = (1 + ‖u‖) ^ μ := by
      rw [← Real.rpow_add hx, hν]; ring_nf
    have hpow2 : (1 + ‖u‖) ^ (2 * (s.card : ℝ)) = ((1 + ‖u‖) ^ s.card) ^ 2 := by
      rw [← pow_mul, mul_comm s.card 2, pow_mul, ← Real.rpow_natCast ((1 + ‖u‖) ^ 2) s.card]
      rw [← Real.rpow_natCast (1 + ‖u‖) 2, ← Real.rpow_mul hx.le]
      ring_nf
    have hsq : ((1 + ‖u‖) ^ s.card) ^ 2 ≤ P ^ 2 * Dn ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hge 2
      rw [mul_pow] at this; exact this
    have hkey : ‖H u‖ * (1 + ‖u‖) ^ (2 * (s.card : ℝ)) ≤ C * P ^ 2 * (1 + ‖u‖) ^ μ * airyEnv u := by
      have h1 : ‖H u‖ * Dn ^ 2 ≤ C * (1 + ‖u‖) ^ μ * airyEnv u := hnorm ▸ hφ u
      calc ‖H u‖ * (1 + ‖u‖) ^ (2 * (s.card : ℝ)) = ‖H u‖ * ((1 + ‖u‖) ^ s.card) ^ 2 := by rw [hpow2]
        _ ≤ ‖H u‖ * (P ^ 2 * Dn ^ 2) := mul_le_mul_of_nonneg_left hsq (norm_nonneg _)
        _ = P ^ 2 * (‖H u‖ * Dn ^ 2) := by ring
        _ ≤ P ^ 2 * (C * (1 + ‖u‖) ^ μ * airyEnv u) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = _ := by ring
    have hxs : 0 < (1 + ‖u‖) ^ (2 * (s.card : ℝ)) := Real.rpow_pos_of_pos hx _
    have : ‖H u‖ ≤ C * P ^ 2 * (1 + ‖u‖) ^ ν * airyEnv u := by
      rw [← hpow] at hkey
      have : ‖H u‖ * (1 + ‖u‖) ^ (2 * (s.card : ℝ)) ≤
          (C * P ^ 2 * (1 + ‖u‖) ^ ν * airyEnv u) * (1 + ‖u‖) ^ (2 * (s.card : ℝ)) := by
        calc _ ≤ _ := hkey
          _ = _ := by ring
      exact le_of_mul_le_mul_right this hxs
    calc ‖H u‖ ≤ C * P ^ 2 * (1 + ‖u‖) ^ ν * airyEnv u := this
      _ ≤ max (C * P ^ 2) (|M| / (m1 * e0)) * (1 + ‖u‖) ^ ν * airyEnv u :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx.le _)) hen.le


lemma airyZero_inj {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) (h : airyZero j = airyZero k) : j = k := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hl | hl
  · exact (airyZero_lt_of_lt hj hl).ne' h
  · exact (airyZero_lt_of_lt hk hl).ne h

lemma airyAiC_airyZero (k : ℕ) : airyAiC (airyZero k : ℂ) = 0 := by
  rw [airyAiC_ofReal, airyAi_airyZero]; simp

/-- Existence of the window function as an entire solution of the cleared-denominator identity. -/
theorem window_exists (α : ℝ) {K : ℕ} (u₂ : ℝ) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ u, airyAiC u ^ 2 * windowN α K u₂ u = H u * windowD K u ^ 2 := by
  refine FormalResearch.EntireDiv.entire_exists_div_sq
    (φ := fun u => airyAiC u ^ 2 * windowN α K u₂ u) (ψ := windowD K)
    (differentiable_airyAiC.pow 2 |>.mul (differentiable_windowN α K u₂))
    (differentiable_windowD K) ?_
  intro z hz
  unfold windowD at hz
  obtain ⟨k, hk, hzk⟩ := Finset.prod_eq_zero_iff.mp hz
  have hzk' : z = (airyZero k : ℂ) := sub_eq_zero.mp hzk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hA : airyAiC z = 0 := by rw [hzk']; exact airyAiC_airyZero k
  refine ⟨by simp [hA], ?_, ?_⟩
  · have hd : HasDerivAt (fun u => airyAiC u ^ 2 * windowN α K u₂ u)
        (2 * airyAiC z * deriv airyAiC z * windowN α K u₂ z + airyAiC z ^ 2 * deriv (windowN α K u₂) z) z := by
      have h1 := (differentiable_airyAiC.differentiableAt (x := z)).hasDerivAt.pow 2
      have h2 := ((differentiable_windowN α K u₂).differentiableAt (x := z)).hasDerivAt
      convert h1.mul h2 using 1
      simp
    rw [hd.deriv, hA]; simp
  · have hfun : windowD K = fun u => (u - (airyZero k : ℂ)) *
        ∏ j ∈ (Finset.Icc 1 K).erase k, (u - (airyZero j : ℂ)) := by
      funext u; unfold windowD; rw [Finset.mul_prod_erase _ (fun j => u - (airyZero j : ℂ)) hk]
    have hd : HasDerivAt (windowD K) (∏ j ∈ (Finset.Icc 1 K).erase k, (z - (airyZero j : ℂ))) z := by
      rw [hfun]
      have h1 : HasDerivAt (fun u : ℂ => u - (airyZero k : ℂ)) 1 z := (hasDerivAt_id z).sub_const _
      have h2 : Differentiable ℂ (fun u : ℂ => ∏ j ∈ (Finset.Icc 1 K).erase k, (u - (airyZero j : ℂ))) := by
        fun_prop
      have := h1.mul (h2.differentiableAt (x := z)).hasDerivAt
      convert this using 1
      rw [hzk']; simp
    rw [hd.deriv]
    refine Finset.prod_ne_zero_iff.mpr (fun j hj => ?_)
    obtain ⟨hjk, hj'⟩ := Finset.mem_erase.mp hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj').1
    rw [hzk']
    intro h0
    have : airyZero k = airyZero j := Complex.ofReal_injective (sub_eq_zero.mp h0)
    exact hjk (airyZero_inj hj1 hk1 this.symm)

/-- The window function `f_K` (an entire solution of the cleared-denominator identity; unique by continuity). -/
noncomputable def windowF (α : ℝ) (K : ℕ) (u₂ : ℝ) : ℂ → ℂ := Classical.choose (window_exists α (K := K) u₂)

lemma differentiable_windowF (α : ℝ) (K : ℕ) (u₂ : ℝ) : Differentiable ℂ (windowF α K u₂) :=
  (Classical.choose_spec (window_exists α (K := K) u₂)).1

/-- `f_K(u) · ∏_{k=1}^K (u - a_k)² = Ai(u)² (u - z₁)(u - u₂) ∏_{k=3}^K (u - z_k)²`. -/
lemma windowF_spec (α : ℝ) (K : ℕ) (u₂ : ℝ) (u : ℂ) :
    airyAiC u ^ 2 * windowN α K u₂ u = windowF α K u₂ u * windowD K u ^ 2 :=
  (Classical.choose_spec (window_exists α (K := K) u₂)).2 u


lemma norm_windowN_le (α : ℝ) {K : ℕ} (hK : 3 ≤ K) (u₂ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ‖windowN α K u₂ u‖ ≤ C * (1 + ‖u‖) ^ (2 * K - 2) := by
  set P : ℝ := ∏ k ∈ Finset.Icc 3 K, (1 + |clarkNode α k|) with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg (fun k _ => by positivity)
  refine ⟨(1 + |clarkNode α 1|) * (1 + |u₂|) * P ^ 2, by positivity, fun u => ?_⟩
  have h1 : ‖u - (clarkNode α 1 : ℂ)‖ ≤ (1 + |clarkNode α 1|) * (1 + ‖u‖) := by
    have := norm_prod_sub_le {1} (fun _ => clarkNode α 1) u
    simpa using this
  have h2 : ‖u - (u₂ : ℂ)‖ ≤ (1 + |u₂|) * (1 + ‖u‖) := by
    have := norm_prod_sub_le {0} (fun _ => u₂) u
    simpa using this
  have h3 := norm_prod_sub_le (Finset.Icc 3 K) (fun k => clarkNode α k) u
  have hcard : (Finset.Icc 3 K).card = K - 2 := by simp
  rw [hcard] at h3
  unfold windowN
  rw [norm_mul, norm_mul, Finset.prod_pow, norm_pow]
  have hx : 0 ≤ 1 + ‖u‖ := by positivity
  have h3' : ‖∏ k ∈ Finset.Icc 3 K, (u - (clarkNode α k : ℂ))‖ ^ 2 ≤ (P * (1 + ‖u‖) ^ (K - 2)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h3 2
  have hexp : (1 + ‖u‖) ^ (2 * K - 2) = (1 + ‖u‖) * (1 + ‖u‖) * ((1 + ‖u‖) ^ (K - 2)) ^ 2 := by
    rw [← pow_mul, ← pow_two, ← pow_add]; congr 1; omega
  rw [hexp]
  calc ‖u - (clarkNode α 1 : ℂ)‖ * ‖u - (u₂ : ℂ)‖ * ‖∏ k ∈ Finset.Icc 3 K, (u - (clarkNode α k : ℂ))‖ ^ 2
      ≤ ((1 + |clarkNode α 1|) * (1 + ‖u‖)) * ((1 + |u₂|) * (1 + ‖u‖)) * (P * (1 + ‖u‖) ^ (K - 2)) ^ 2 := by
        gcongr
    _ = _ := by ring

/-- **`f_K ∈ 𝒢_{-5/2}`**: `‖f_K(u)‖ ≤ C (1 + ‖u‖)^{-5/2} e(u)`. -/
theorem windowF_bound (α : ℝ) {K : ℕ} (hK : 3 ≤ K) (u₂ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ‖windowF α K u₂ u‖ ≤ C * (1 + ‖u‖) ^ (-(5 / 2) : ℝ) * airyEnv u := by
  obtain ⟨CN, hCN, hN⟩ := norm_windowN_le α hK u₂
  have hφ : ∀ u : ℂ, ‖airyAiC u ^ 2 * windowN α K u₂ u‖ ≤
      (9 * CN) * (1 + ‖u‖) ^ ((-(1 / 2) : ℝ) + (2 * K - 2 : ℕ)) * airyEnv u := by
    intro u
    have hx : 0 < 1 + ‖u‖ := by positivity
    rw [norm_mul, norm_pow]
    have hA := airyAiC_norm_sq_le u
    have hpow : (1 + ‖u‖) ^ ((-(1 / 2) : ℝ) + (2 * K - 2 : ℕ)) =
        (1 + ‖u‖) ^ (-(1 / 2) : ℝ) * (1 + ‖u‖) ^ (2 * K - 2) := by
      rw [Real.rpow_add hx, Real.rpow_natCast]
    rw [hpow]
    calc ‖airyAiC u‖ ^ 2 * ‖windowN α K u₂ u‖
        ≤ (9 * (1 + ‖u‖) ^ (-(1 / 2) : ℝ) * airyEnv u) * (CN * (1 + ‖u‖) ^ (2 * K - 2)) :=
          mul_le_mul hA (hN u) (norm_nonneg _) (by have := airyEnv_pos u; positivity)
      _ = _ := by ring
  obtain ⟨C', hC', hb⟩ := div_bound (differentiable_windowF α K u₂) (s := Finset.Icc 1 K)
    (t := fun k => airyZero k) (by positivity) hφ (fun u => by
      have := windowF_spec α K u₂ u
      unfold windowD at this
      exact this)
  refine ⟨C', hC', fun u => ?_⟩
  have hcard : ((Finset.Icc 1 K).card : ℝ) = K := by simp
  have hexp : (-(1 / 2) : ℝ) + ((2 * K - 2 : ℕ) : ℝ) - 2 * ((Finset.Icc 1 K).card : ℝ) = -(5 / 2) := by
    rw [hcard]
    have : ((2 * K - 2 : ℕ) : ℝ) = 2 * K - 2 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this]; ring
  have := hb u
  rwa [hexp] at this


/-! ### Real node data and the Clark-Airy summation -/

/-- `cot α`, the slope `Ai'(z_n) = cot α · Ai(z_n)` at the Clark nodes. -/
noncomputable def cotC (α : ℝ) : ℝ := Real.cos α / Real.sin α

lemma clarkNode_airyAi' {α : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    airyAi' (clarkNode α n) = cotC α * airyAi (clarkNode α n) :=
  (airyClarkNode_spec hn (Real.cos α / Real.sin α)).2

lemma clarkNode_airyAi_ne {α : ℝ} {n : ℕ} (hn : 1 ≤ n) : airyAi (clarkNode α n) ≠ 0 :=
  airyAi_ne_zero_of_clark (clarkNode_airyAi' hn)

lemma clarkNode_ne_airyZero (α : ℝ) {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    clarkNode α n ≠ airyZero k := by
  intro h
  rcases lt_or_ge k n with hkn | hkn
  · have h1 : clarkNode α n < airyZero (n - 1) := airyClarkNode_lt_airyZero (by omega) _
    have h2 : airyZero (n - 1) ≤ airyZero k := airyZero_le_of_le hk (by omega)
    linarith
  · have h1 : airyZero n < clarkNode α n := airyZero_lt_airyClarkNode hn _
    have h2 : airyZero k ≤ airyZero n := airyZero_le_of_le hn hkn
    linarith

/-- Real form of `∏_{k=1}^K (x - a_k)`. -/
noncomputable def windowDr (K : ℕ) (x : ℝ) : ℝ := ∏ k ∈ Finset.Icc 1 K, (x - airyZero k)

/-- Real form of `(x - z₁)(x - u₂) ∏_{k=3}^K (x - z_k)²`. -/
noncomputable def windowNr (α : ℝ) (K : ℕ) (u₂ x : ℝ) : ℝ :=
  (x - clarkNode α 1) * (x - u₂) * ∏ k ∈ Finset.Icc 3 K, (x - clarkNode α k) ^ 2

lemma windowD_ofReal (K : ℕ) (x : ℝ) : windowD K (x : ℂ) = ((windowDr K x : ℝ) : ℂ) := by
  unfold windowD windowDr; push_cast; rfl

lemma windowN_ofReal (α : ℝ) (K : ℕ) (u₂ x : ℝ) :
    windowN α K u₂ (x : ℂ) = ((windowNr α K u₂ x : ℝ) : ℂ) := by
  unfold windowN windowNr; push_cast; rfl

lemma windowDr_node_ne (α : ℝ) (K : ℕ) {n : ℕ} (hn : 1 ≤ n) : windowDr K (clarkNode α n) ≠ 0 := by
  unfold windowDr
  refine Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)
  exact sub_ne_zero.mpr (clarkNode_ne_airyZero α hn (Finset.mem_Icc.mp hk).1)

/-- The `n`-th term `f_K(z_n)/K(z_n, z_n)` of the Clark-Airy summation of `f_K`, in real form:
`N(z_n) / (D(z_n)² (cot²α - z_n))`. -/
noncomputable def windowTerm (α : ℝ) (K : ℕ) (u₂ : ℝ) (n : ℕ) : ℝ :=
  windowNr α K u₂ (clarkNode α n) /
    (windowDr K (clarkNode α n) ^ 2 * (cotC α ^ 2 - clarkNode α n))

lemma windowF_node {α : ℝ} (K : ℕ) (u₂ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    windowF α K u₂ (clarkNode α n : ℂ) /
      (deriv airyAiC (clarkNode α n : ℂ) ^ 2 - (clarkNode α n : ℂ) * airyAiC (clarkNode α n : ℂ) ^ 2) =
      ((windowTerm α K u₂ n : ℝ) : ℂ) := by
  set x := clarkNode α n with hx
  have hspec := windowF_spec α K u₂ (x : ℂ)
  rw [windowD_ofReal, windowN_ofReal, airyAiC_ofReal] at hspec
  have hD := windowDr_node_ne α K hn
  have hA := clarkNode_airyAi_ne (α := α) hn
  have hd := clarkNode_airyAi' (α := α) hn
  rw [← hx] at hD hA hd
  have hDc : ((windowDr K x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD
  have hfx : windowF α K u₂ (x : ℂ) =
      ((airyAi x ^ 2 * windowNr α K u₂ x / windowDr K x ^ 2 : ℝ) : ℂ) := by
    push_cast
    field_simp
    linear_combination (-1 : ℂ) * hspec
  have hK : (airyAi' x ^ 2 - x * airyAi x ^ 2) = airyAi x ^ 2 * (cotC α ^ 2 - x) := by
    rw [hd]; ring
  have hKpos : airyAi x ^ 2 * (cotC α ^ 2 - x) ≠ 0 := by
    rw [← hK]; exact (airyKer_pos' x).ne'
  rw [deriv_airyAiC_ofReal, airyAiC_ofReal, hfx]
  have hcast : (airyAi' x : ℂ) ^ 2 - (x : ℂ) * (airyAi x : ℂ) ^ 2 =
      ((airyAi x ^ 2 * (cotC α ^ 2 - x) : ℝ) : ℂ) := by
    rw [← hK]; push_cast; ring
  rw [hcast, ← Complex.ofReal_div]
  congr 1
  unfold windowTerm
  rw [← hx]
  have hA2 : airyAi x ^ 2 ≠ 0 := pow_ne_zero 2 hA
  have hc : cotC α ^ 2 - x ≠ 0 := fun h => hKpos (by rw [h, mul_zero])
  field_simp


/-- **Clark-Airy summation indexed by the nodes**: `∫ f = Σ_{n ≥ 1} f(z_n)/K(z_n, z_n)`. -/
theorem clark_node_hasSum {α : ℝ} (hα : Real.sin α ≠ 0) {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C ν : ℝ}
    (hC : 0 ≤ C) (hν : ν < -1) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    HasSum (fun n : ℕ => f (clarkNode α (n + 1) : ℂ) /
      (deriv airyAiC (clarkNode α (n + 1) : ℂ) ^ 2 -
        (clarkNode α (n + 1) : ℂ) * airyAiC (clarkNode α (n + 1) : ℂ) ^ 2)) (∫ x : ℝ, f (x : ℂ)) := by
  have h := airyClark_quadrature α hα hf hC hν hb
  let g : ℕ → {z : ℂ // (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0} :=
    fun n => ⟨(clarkNode α (n + 1) : ℂ), clarkNode_zero hα (by omega)⟩
  have hinj : Function.Injective g := by
    intro n m hnm
    have h1 : clarkNode α (n + 1) = clarkNode α (m + 1) := by
      have h1 : ((clarkNode α (n + 1) : ℝ) : ℂ) = (clarkNode α (m + 1) : ℂ) := congrArg Subtype.val hnm
      exact Complex.ofReal_injective h1
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · have := clarkNode_lt_of_lt (n := n + 1) (m := m + 1) (by omega) (by omega) α
      linarith
    · have := clarkNode_lt_of_lt (n := m + 1) (m := n + 1) (by omega) (by omega) α
      linarith
  have hsurj : Function.Surjective g := by
    rintro ⟨z, hz⟩
    obtain ⟨n, hn, rfl⟩ := (psiClark_zero_iff hα z).1 hz
    exact ⟨n - 1, Subtype.ext (by simp only [g]; rw [Nat.sub_add_cancel hn])⟩
  let e := Equiv.ofBijective g ⟨hinj, hsurj⟩
  exact (e.hasSum_iff (f := fun z : {z : ℂ // (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0} =>
      f z / (deriv airyAiC z ^ 2 - z * airyAiC z ^ 2))).2 h

/-- **Clark-Airy summation of the window function**: `∫ f_K = Σ_{n ≥ 1} N(z_n) / (D(z_n)² (cot²α - z_n))`. -/
theorem windowF_hasSum {α : ℝ} (hα : Real.sin α ≠ 0) {K : ℕ} (hK : 3 ≤ K) (u₂ : ℝ) :
    HasSum (fun n : ℕ => windowTerm α K u₂ (n + 1)) (∫ x : ℝ, (windowF α K u₂ (x : ℂ)).re) := by
  obtain ⟨C, hC, hb⟩ := windowF_bound α hK u₂
  have hb' : ∀ u : ℂ, ‖windowF α K u₂ u‖ ≤ C * (1 + ‖u‖) ^ (-(5 / 2) : ℝ) * airyEnv u := hb
  have h := clark_node_hasSum hα (differentiable_windowF α K u₂) hC (by norm_num : (-(5 / 2) : ℝ) < -1) hb'
  have hre := Complex.hasSum_re h
  have hfi := airy_integrable_real (differentiable_windowF α K u₂) hC (by norm_num : (-(5 / 2) : ℝ) < -1) hb'
  have hint : (∫ x : ℝ, windowF α K u₂ (x : ℂ)).re = ∫ x : ℝ, (windowF α K u₂ (x : ℂ)).re := by
    simpa using (integral_re hfi).symm
  rw [hint] at hre
  convert hre using 1
  funext n
  show _ = (windowF α K u₂ (clarkNode α (n + 1) : ℂ) /
      (deriv airyAiC (clarkNode α (n + 1) : ℂ) ^ 2 -
        (clarkNode α (n + 1) : ℂ) * airyAiC (clarkNode α (n + 1) : ℂ) ^ 2)).re
  rw [windowF_node K u₂ (by omega : 1 ≤ n + 1), Complex.ofReal_re]

end FormalResearch.ModularBootstrap.TwoLevel
