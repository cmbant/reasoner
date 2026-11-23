module

public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedRegionOneAiry
public import FormalResearch.ModularBootstrap.Upper.Window.AiryProdPositive
public import FormalResearch.ModularBootstrap.Upper.Ramped.ProfileProducts

/-!
# Lower bound for the Airy product at a real point (`rem:thmU`, Step (2))

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Step (2): "for real `u`, `1 + z_j = ((u - u_j)² +
ε_{j,u}²)/(u - a_j)²`, which is `≥ 1` for `j ≤ N_Ai` (`u_j = a_j`) and `≥ (1 - |δ_j|/|u - a_j|)²` for `j > N_Ai`; so
`log ∏_{j ≠ k}(1 + z_j) ≥ -4 ∑ |δ_j|/|u - a_j| ≥ -C'`".

For a profile with `u_j = a_j` for `2 ≤ j ≤ M`, `|a_j - u_j| ≤ C_Z j^{-4/3}` beyond, and a real `u ≥ a_K` with
`M ≥ 2K` (so that every `j > M` is at distance `≥ (3/10) j^{2/3}` from `u`; in Region I the index `K` is `O(N_tr)`
and `M = N_Ai ≫ N_tr`, which replaces the three-range sum of Lemma E by `∑ j^{-2}`):

* `airyProdTail_lower`: `‖∏_{j ≥ 2}(1 + z_j(u))‖ ≥ e^{-R} · (1 + z_{k_0}(u))` for every `2 ≤ k_0 ≤ M`, with `R`
  depending only on `C_Z`;
* `norm_airyWindowProd_real`: `‖W(u)‖ = Ai(u)² |u - u_f|/(u - a_1)² · ‖∏_{j ≥ 2}(1 + z_j(u))‖` off the zeros.

All results are proved unconditionally.
-/

@[expose] public section

open Set Filter Topology
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window

lemma three_halves_le_two_rpow : (3 / 2 : ℝ) ≤ (2 : ℝ) ^ (2 / 3 : ℝ) := by
  by_contra h
  push Not at h
  have h0 : 0 ≤ (2 : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have h3 : ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 < (3 / 2 : ℝ) ^ 3 := pow_lt_pow_left₀ h h0 (by norm_num)
  have h4 : ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  rw [h4] at h3
  norm_num at h3

/-- Distance from `u ≥ a_K` to a far zero: `u - a_j ≥ (3/10) j^{2/3}` for `j ≥ 2K`. -/
lemma sub_airyZero_ge {K j : ℕ} (hK : 1 ≤ K) (hj : 2 * K ≤ j) {u : ℝ} (hu : airyZero K ≤ u) :
    (3 / 10 : ℝ) * (j : ℝ) ^ (2 / 3 : ℝ) ≤ u - airyZero j := by
  have hj1 : 1 ≤ j := by omega
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have h1 := airyZero_abs_ge_pow hj1
  have h2 := airyZero_abs_le_pow hK
  rw [abs_of_neg (airyZero_neg j)] at h1
  rw [abs_of_neg (airyZero_neg K)] at h2
  have hKj : (K : ℝ) ≤ (j : ℝ) / 2 := by
    have : (2 * K : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have h3 : (K : ℝ) ^ (2 / 3 : ℝ) ≤ ((j : ℝ) / 2) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hK0.le hKj (by norm_num)
  rw [Real.div_rpow hj0.le (by norm_num)] at h3
  have h4 := three_halves_le_two_rpow
  have hq : 0 < (j : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hj0 _
  have h5 : (j : ℝ) ^ (2 / 3 : ℝ) / (2 : ℝ) ^ (2 / 3 : ℝ) ≤ (j : ℝ) ^ (2 / 3 : ℝ) / (3 / 2) :=
    div_le_div_of_nonneg_left hq.le (by norm_num) h4
  have h6 : 3 * (K : ℝ) ^ (2 / 3 : ℝ) ≤ 2 * (j : ℝ) ^ (2 / 3 : ℝ) := by
    have : 3 * ((j : ℝ) ^ (2 / 3 : ℝ) / (3 / 2)) = 2 * (j : ℝ) ^ (2 / 3 : ℝ) := by ring
    nlinarith
  linarith

/-- The real factor `((u - u_j)² + ε_j²)/(u - a_j)²` of the Airy product. -/
noncomputable def prodFactorR (uSite epsU : ℕ → ℝ) (u : ℝ) (j : ℕ) : ℝ :=
  ((u - uSite j) ^ 2 + epsU j ^ 2) / (u - airyZero j) ^ 2

lemma norm_airyProdFactor_real (uSite epsU : ℕ → ℝ) (u : ℝ) (j : ℕ) :
    ‖airyProdFactor uSite epsU j (u : ℂ)‖ = prodFactorR uSite epsU u j := by
  rw [airyProdFactor_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rfl

/-- A far factor (`j > M ≥ 2K`, `u ≥ a_K`) is at least `exp(-16 C_Z / j²)`. -/
lemma prodFactorR_far {uSite epsU : ℕ → ℝ} {C_Z : ℝ} (hCZ : 0 < C_Z) {K j : ℕ} (hK : 1 ≤ K)
    (hj : 2 * K ≤ j) (hj8 : 8 * C_Z ≤ (j : ℝ) ^ 2)
    (hdel : |airyZero j - uSite j| ≤ C_Z * (j : ℝ) ^ (-(4 / 3 : ℝ))) {u : ℝ} (hu : airyZero K ≤ u) :
    Real.exp (-(16 * C_Z / (j : ℝ) ^ 2)) ≤ prodFactorR uSite epsU u j := by
  have hj1 : 1 ≤ j := by omega
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have hq : 0 < (j : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hj0 _
  have hd := sub_airyZero_ge hK hj hu
  have hpos : 0 < u - airyZero j := lt_of_lt_of_le (by positivity) hd
  set t : ℝ := 4 * C_Z / (j : ℝ) ^ 2 with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 / 2 := by
    rw [ht, div_le_iff₀ (by positivity)]; linarith
  -- `|δ| ≤ t (u - a_j)`
  have hex : (j : ℝ) ^ (-(2 : ℝ)) * (j : ℝ) ^ (2 / 3 : ℝ) = (j : ℝ) ^ (-(4 / 3 : ℝ)) := by
    rw [← Real.rpow_add hj0]; norm_num
  have hinv : (j : ℝ) ^ (-(2 : ℝ)) = 1 / (j : ℝ) ^ 2 := by
    rw [Real.rpow_neg hj0.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  have hδ : |airyZero j - uSite j| ≤ t * (u - airyZero j) := by
    refine hdel.trans ?_
    have h1 : t * ((3 / 10 : ℝ) * (j : ℝ) ^ (2 / 3 : ℝ)) ≤ t * (u - airyZero j) :=
      mul_le_mul_of_nonneg_left hd ht0
    have h2 : C_Z * (j : ℝ) ^ (-(4 / 3 : ℝ)) ≤ t * ((3 / 10 : ℝ) * (j : ℝ) ^ (2 / 3 : ℝ)) := by
      rw [← hex, hinv, ht]
      have : 4 * C_Z / (j : ℝ) ^ 2 * (3 / 10 * (j : ℝ) ^ (2 / 3 : ℝ)) =
          (6 / 5 : ℝ) * (C_Z * (1 / (j : ℝ) ^ 2 * (j : ℝ) ^ (2 / 3 : ℝ))) := by ring
      rw [this]
      have hnn : 0 ≤ C_Z * (1 / (j : ℝ) ^ 2 * (j : ℝ) ^ (2 / 3 : ℝ)) := by positivity
      linarith
    linarith
  have hnum : (1 - t) ^ 2 * (u - airyZero j) ^ 2 ≤ (u - uSite j) ^ 2 + epsU j ^ 2 := by
    have h1 : (1 - t) * (u - airyZero j) ≤ u - uSite j := by
      have := (abs_le.mp hδ).2
      nlinarith [(abs_le.mp hδ).1]
    have h2 : 0 ≤ (1 - t) * (u - airyZero j) := mul_nonneg (by linarith) hpos.le
    have h3 : ((1 - t) * (u - airyZero j)) ^ 2 ≤ (u - uSite j) ^ 2 := pow_le_pow_left₀ h2 h1 2
    nlinarith [sq_nonneg (epsU j)]
  have hge : (1 - t) ^ 2 ≤ prodFactorR uSite epsU u j := by
    unfold prodFactorR
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hexp := exp_neg_two_mul_le_one_sub ht0 ht1
  have hexp0 : 0 ≤ Real.exp (-2 * t) := (Real.exp_pos _).le
  have h4 : Real.exp (-(16 * C_Z / (j : ℝ) ^ 2)) = Real.exp (-2 * t) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    rw [ht]; push_cast; ring
  rw [h4]
  exact (pow_le_pow_left₀ hexp0 hexp 2).trans hge

/-- **Lower bound for the tail product at a real point** (`rem:thmU` Step (2)). -/
theorem airyProdTail_lower {C_Z : ℝ} (hCZ : 0 < C_Z) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (uSite epsU : ℕ → ℝ), AiryProdTailHypothesis 1 uSite epsU →
      ∀ (M K : ℕ), 1 ≤ K → 2 * K ≤ M → 8 * C_Z ≤ (M : ℝ) ^ 2 →
      (∀ j : ℕ, 2 ≤ j → j ≤ M → uSite j = airyZero j) →
      (∀ j : ℕ, M < j → |airyZero j - uSite j| ≤ C_Z * (j : ℝ) ^ (-(4 / 3 : ℝ))) →
      ∀ u : ℝ, airyZero K ≤ u → (∀ j : ℕ, 1 ≤ j → u ≠ airyZero j) →
      ∀ k₀ : ℕ, 2 ≤ k₀ → k₀ ≤ M →
        Real.exp (-R) * (((u - airyZero k₀) ^ 2 + epsU k₀ ^ 2) / (u - airyZero k₀) ^ 2) ≤
          ‖airyProdTail 1 uSite epsU (u : ℂ)‖ := by
  have hZs : Summable (fun m : ℕ => 1 / ((m : ℝ) + 2) ^ 2) := by
    have := (summable_nat_add_iff 2).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simpa using this
  set Z : ℝ := ∑' m : ℕ, 1 / ((m : ℝ) + 2) ^ 2 with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun _ => by positivity
  refine ⟨16 * C_Z * Z, by positivity, fun uSite epsU hH M K hK hMK hM hsite hdel u hu hne k₀ hk2 hkM => ?_⟩
  have hne' : ∀ k : ℕ, 1 < k → (u : ℂ) ≠ (airyZero k : ℂ) := fun k hk h =>
    hne k (by omega) (Complex.ofReal_injective h)
  have hP := hasProd_airyProdTail hH hne'
  set pr : ℕ → ℝ := fun m => prodFactorR uSite epsU u (m + 2) with hpr
  have hnorm : ∀ m : ℕ, ‖airyProdFactor uSite epsU (1 + 1 + m) (u : ℂ)‖ = pr m := fun m => by
    rw [show 1 + 1 + m = m + 2 by ring]; exact norm_airyProdFactor_real uSite epsU u (m + 2)
  have hpr0 : ∀ m, 0 ≤ pr m := fun m => by simp only [hpr]; unfold prodFactorR; positivity
  set m0 : ℕ := k₀ - 2 with hm0
  have hm0k : m0 + 2 = k₀ := by omega
  set g : ℕ → ℝ := fun m => if m + 2 ≤ M then 0 else -(16 * C_Z / ((m : ℝ) + 2) ^ 2) with hg
  have hβ : ∀ m, m ≠ m0 → Real.exp (g m) ≤ pr m := by
    intro m hm
    by_cases hmM : m + 2 ≤ M
    · simp only [hg, hmM, ↓reduceIte, Real.exp_zero]
      have hsm := hsite (m + 2) (by omega) hmM
      simp only [hpr]; unfold prodFactorR; rw [hsm]
      have hpos : 0 < (u - airyZero (m + 2)) ^ 2 := by
        have := sub_ne_zero.mpr (hne (m + 2) (by omega)); positivity
      rw [le_div_iff₀ hpos]; nlinarith [sq_nonneg (epsU (m + 2))]
    · simp only [hg, hmM, ↓reduceIte]
      have h8 : 8 * C_Z ≤ ((m + 2 : ℕ) : ℝ) ^ 2 := by
        refine hM.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ 2)
        exact_mod_cast (by omega : M ≤ m + 2)
      have := prodFactorR_far (uSite := uSite) (epsU := epsU) hCZ hK (j := m + 2) (by omega) h8
        (hdel (m + 2) (by omega)) hu
      push_cast at this ⊢
      exact this
  have hsumg : ∀ t : Finset ℕ, -(16 * C_Z * Z) ≤ ∑ m ∈ t, g m := by
    intro t
    have h1 : ∀ m : ℕ, -(16 * C_Z * (1 / ((m : ℝ) + 2) ^ 2)) ≤ g m := fun m => by
      simp only [hg]; split_ifs
      · have : 0 ≤ 16 * C_Z * (1 / ((m : ℝ) + 2) ^ 2) := by positivity
        linarith
      · apply le_of_eq; ring
    have hle := hZs.sum_le_tsum t (fun m _ => by positivity)
    calc -(16 * C_Z * Z) ≤ -(16 * C_Z * ∑ m ∈ t, 1 / ((m : ℝ) + 2) ^ 2) := by
          have := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 16 * C_Z)
          linarith
      _ = ∑ m ∈ t, -(16 * C_Z * (1 / ((m : ℝ) + 2) ^ 2)) := by
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      _ ≤ ∑ m ∈ t, g m := Finset.sum_le_sum fun m _ => h1 m
  have hlim : Tendsto (fun s : Finset ℕ => ‖∏ m ∈ s, airyProdFactor uSite epsU (1 + 1 + m) (u : ℂ)‖)
      atTop (𝓝 ‖airyProdTail 1 uSite epsU (u : ℂ)‖) := (continuous_norm.tendsto _).comp hP
  refine ge_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop ({m0} : Finset ℕ)] with s hs
  have hm0s : m0 ∈ s := hs (Finset.mem_singleton_self m0)
  rw [norm_prod]
  simp_rw [hnorm]
  rw [← Finset.mul_prod_erase s pr hm0s]
  have h1 : ∏ m ∈ s.erase m0, Real.exp (g m) ≤ ∏ m ∈ s.erase m0, pr m :=
    Finset.prod_le_prod₀ (fun m _ => (Real.exp_pos _).le) (fun m hm => hβ m (Finset.ne_of_mem_erase hm))
  rw [← Real.exp_sum] at h1
  have h2 : Real.exp (-(16 * C_Z * Z)) ≤ Real.exp (∑ m ∈ s.erase m0, g m) := Real.exp_le_exp.2 (hsumg _)
  have hprm0 : pr m0 = ((u - airyZero k₀) ^ 2 + epsU k₀ ^ 2) / (u - airyZero k₀) ^ 2 := by
    simp only [hpr, prodFactorR, hm0k, hsite k₀ hk2 hkM]
  rw [← hprm0]
  rw [mul_comm (Real.exp _)]
  exact mul_le_mul_of_nonneg_left (h2.trans h1) (hpr0 m0)

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.airyProdTail_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyProdTail_lower

end FormalResearch.ModularBootstrap.Upper.Ramped
