/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctCuspEdgeInner

/-!
# `fct:cusp-edge` (Lemma FCT.7a): absolute edge estimate for a cusp profile (F2a)

Formalizes **Lemma FCT.7a** (`fct:cusp-edge`) of Paper I
(`CFT/sign_uncertainty/paper/constant_terms_five.tex`, lines 1025–1092):

Put `ς = c^{-1/3}` and `Φ(τ; L) = Lτ - ∫_0^τ m(v) dv = edgePhi L τ`.
Let `0 < α < 2`, `q = 2α + 3/2`, `η > 0`, and suppose that:
* `A_c ∈ C³(ℝ, ℂ)` obeys `‖∂_τ^j A_c(τ)‖ ≤ C_A e^{-η|τ|}` (`0 ≤ j ≤ 3`);
* `Y ∈ C³(ℝ \ {0}, ℂ)` obeys `‖Y^{(j)}(u)‖ ≤ C_Y |u|^{-q-j}` for `|u| ≥ 1` (`0 ≤ j ≤ 3`);
* on `|u| ≤ 2`, `Y = Y₀ + R` with `Y₀ ∈ C³((-2, 2), ℂ)` having `‖Y₀^{(j)}(u)‖ ≤ C_Y`
  and `‖R^{(j)}(u)‖ ≤ C_Y |u|^{α-j}` for `0 < |u| < 2` (`0 ≤ j ≤ 3`).

Then, uniformly in `c ≥ 1` and `L ∈ ℝ` (with constant depending only on `α, η, C_A, C_Y`),
`J_c(L) = (c^{1/3} / (2π)) ∫_ℝ e^{icΦ(τ; L)} A_c(τ) Y(c^{1/3} τ) dτ` satisfies:
* `‖J_c(L)‖ ≤ C` for all `L ∈ ℝ`, and
* `‖J_c(L)‖ ≤ C (1 + c^{2/3} L)^{-α-1}` for all `L ≥ 0`.

Class: proved, no hypotheses. Axiom guard at the end.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty.FctCuspEdge

open FormalResearch.CohnElkies FormalResearch.Analysis

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### Elementary total-variation and exponential-absorption helpers -/

/-- If `f` is `C³` on open `U` and vanishes on `(a, b)` (`a < b`), then `f^{(j)}(x) = 0`
for all `x ∈ [a, b] ∩ U` and `j ≤ 2`. -/
lemma iteratedDeriv_eq_zero_of_eq_zero_on_Ioo {f : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 3 f U) {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) (hxU : x ∈ U)
    (hzero : ∀ y ∈ Ioo a b, f y = 0) : ∀ j ≤ 2, iteratedDeriv j f x = 0 := by
  intro j hj
  have hcont : ContinuousAt (iteratedDeriv j f) x := by
    have h1 := hf.continuousOn_iteratedDerivWithin (m := j) (by exact_mod_cast (show j ≤ 3 by omega)) hU.uniqueDiffOn
    have h2 : ContinuousOn (iteratedDeriv j f) U :=
      h1.congr fun y hy => (iteratedDerivWithin_of_isOpen hU hy).symm
    exact h2.continuousAt (hU.mem_nhds hxU)
  have hzero_j : ∀ y ∈ Ioo a b, iteratedDeriv j f y = 0 := by
    intro y hy
    have hev : f =ᶠ[𝓝 y] 0 := by
      filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz using hzero z hz
    rw [hev.iteratedDeriv_eq j, iteratedDeriv_const_zero]
  have hmem_cl : x ∈ closure (Ioo a b) := by rw [closure_Ioo hab.ne]; exact hx
  rw [mem_closure_iff_nhdsWithin_neBot] at hmem_cl
  have ht1 : Tendsto (iteratedDeriv j f) (𝓝[Ioo a b] x) (𝓝 (iteratedDeriv j f x)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have ht2 : Tendsto (iteratedDeriv j f) (𝓝[Ioo a b] x) (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun y hy => (hzero_j y hy).symm)
  exact tendsto_nhds_unique ht1 ht2

/-- Bounded variation bound from a uniform `C¹` derivative bound on `[a, b]`. -/
lemma eVariationOn_le_of_deriv_bound {a b M' : ℝ} (hab : a ≤ b) (hM' : 0 ≤ M')
    {f : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U) (hsub : Icc a b ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (hbd : ∀ x ∈ Icc a b, ‖deriv f x‖ ≤ M') :
    BoundedVariationOn f (Icc a b) ∧ (eVariationOn f (Icc a b)).toReal ≤ M' * (b - a) := by
  let Mnn : NNReal := ⟨M', hM'⟩
  have hlip : LipschitzOnWith Mnn f (Icc a b) := by
    refine Convex.lipschitzOnWith_of_nnNorm_deriv_le (fun x hx => ?_) (fun x hx => ?_) (convex_Icc a b)
    · exact (hf.differentiableOn one_ne_zero x (hsub hx)).differentiableAt (hU.mem_nhds (hsub hx))
    · exact hbd x hx
  have hev : eVariationOn f (Icc a b) ≤ ENNReal.ofReal (M' * (b - a)) := by
    rw [eVariationOn]
    refine iSup_le fun ⟨n, ⟨u, hu_mono, hu_mem⟩⟩ => ?_
    have hstep : ∀ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ≤
        ENNReal.ofReal (M' * (u (i + 1) - u i)) := by
      intro i _
      have h1 := hlip (hu_mem (i + 1)) (hu_mem i)
      have hle : u i ≤ u (i + 1) := hu_mono (Nat.le_succ i)
      have hed : edist (u (i + 1)) (u i) = ENNReal.ofReal (u (i + 1) - u i) := by
        rw [edist_dist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hle)]
      have hM_coe : (Mnn : ENNReal) = ENNReal.ofReal M' := (ENNReal.ofReal_eq_coe_nnreal hM').symm
      rw [hed, hM_coe, ← ENNReal.ofReal_mul hM'] at h1
      exact h1
    have hsum_le : ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ≤
        ENNReal.ofReal (∑ i ∈ Finset.range n, M' * (u (i + 1) - u i)) := by
      calc ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))
          ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (M' * (u (i + 1) - u i)) := Finset.sum_le_sum hstep
        _ = ENNReal.ofReal (∑ i ∈ Finset.range n, M' * (u (i + 1) - u i)) := by
            rw [ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg hM' (sub_nonneg.mpr (hu_mono (Nat.le_succ i)))]
    have htele : ∑ i ∈ Finset.range n, M' * (u (i + 1) - u i) ≤ M' * (b - a) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub u n]
      exact mul_le_mul_of_nonneg_left (by linarith [(hu_mem n).2, (hu_mem 0).1]) hM'
    exact hsum_le.trans (ENNReal.ofReal_le_ofReal htele)
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hev, ?_⟩
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hM' (sub_nonneg.mpr hab)) hev

/-- For `κ > 0`, `p ≥ 0`, there is `C ≥ 0` such that `x^p * exp(-κ x) ≤ C` for all `x ≥ 0`. -/
lemma rpow_mul_exp_neg_bdd {κ p : ℝ} (hκ : 0 < κ) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → x ^ p * Real.exp (-κ * x) ≤ C := by
  set n : ℕ := ⌈p⌉₊
  have hn : p ≤ (n : ℝ) := Nat.le_ceil p
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ x : ℝ, 0 ≤ x → x ^ n * Real.exp (-κ * x) ≤ C₀ := by
    refine ⟨(n.factorial : ℝ) * (1 / κ) ^ n, by positivity, fun x hx => ?_⟩
    have h1 := pow_mul_exp_neg_le n (η := 2 * κ) (by positivity) hx
    have heq : -(2 * κ / 2) * x = -κ * x := by ring
    have heq2 : 2 / (2 * κ) = 1 / κ := by field_simp [hκ.ne']
    rw [heq, heq2] at h1
    exact h1
  refine ⟨max 1 C₀, by positivity, fun x hx => ?_⟩
  rcases le_or_gt x 1 with hx1 | hx1
  · have hp1 : x ^ p ≤ 1 := Real.rpow_le_one hx hx1 hp
    have he1 : Real.exp (-κ * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    calc x ^ p * Real.exp (-κ * x) ≤ 1 * 1 := mul_le_mul hp1 he1 (Real.exp_pos _).le zero_le_one
      _ = 1 := mul_one 1
      _ ≤ max 1 C₀ := le_max_left _ _
  · have hpn : x ^ p ≤ x ^ n := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hx1.le hn
    calc x ^ p * Real.exp (-κ * x) ≤ x ^ n * Real.exp (-κ * x) :=
          mul_le_mul_of_nonneg_right hpn (Real.exp_pos _).le
      _ ≤ C₀ := hC₀.2 x hx
      _ ≤ max 1 C₀ := le_max_right _ _

/-- For `κ > 0`, `p ≥ 0`, `exp(-κ * exp(L/2)) ≤ C * L^{-p}` for `L ≥ 1`. -/
lemma exp_neg_exp_half_le_rpow {κ p : ℝ} (hκ : 0 < κ) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L → Real.exp (-κ * Real.exp (L / 2)) ≤ C * L ^ (-p) := by
  obtain ⟨C, hC0, hC⟩ := rpow_mul_exp_neg_bdd (κ := κ / 2) (p := p) (by positivity) hp
  refine ⟨C, hC0, fun L hL => ?_⟩
  have hL0 : 0 < L := by linarith
  have hexp_ge : L / 2 ≤ Real.exp (L / 2) := by linarith [Real.add_one_le_exp (L / 2)]
  have h1 : Real.exp (-κ * Real.exp (L / 2)) ≤ Real.exp (-(κ / 2) * L) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h2 := hC L hL0.le
  rw [Real.rpow_neg hL0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hL0 p)]
  calc Real.exp (-κ * Real.exp (L / 2)) * L ^ p
      ≤ Real.exp (-(κ / 2) * L) * L ^ p := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hL0.le p)
    _ = L ^ p * Real.exp (-(κ / 2) * L) := mul_comm _ _
    _ ≤ C := h2

/-! ### Outer amplitude derivative bounds on `u > 0` -/

/-- Derivative bounds for `g(u) = (1 - chi0 u) * A(ς u) * Y(u)` on `u ≥ 1`. -/
lemma outer_amp_deriv_bound {α η C_A C_Y Bχ : ℝ} (_hα0 : 0 < α) (hη : 0 < η)
    (hCA : 0 ≤ C_A) (hCY : 0 ≤ C_Y) (hBχ1 : 1 ≤ Bχ)
    (hBχ : ∀ j ≤ 3, ∀ x : ℝ, |iteratedDeriv j chi0 x| ≤ Bχ)
    {c : ℝ} (hc : 1 ≤ c) {A Y Y₀ R : ℝ → ℂ}
    (hA : CuspAmplitude η C_A A) (hY : CuspProfile α C_Y Y Y₀ R)
    {u : ℝ} (hu : 1 ≤ u) :
    ∀ j ≤ 3, ‖iteratedDeriv j (fun t => ((1 - chi0 t : ℝ) : ℂ) * A (c ^ (-(1 : ℝ) / 3) * t) * Y t) u‖ ≤
      (64 * (2 * Bχ) * (6 * max 1 ((2 / η) ^ 3) * C_A) * C_Y) *
        (u ^ (-(2 * α + 3 / 2)) * Real.exp (-(η / 2) * c ^ (-(1 : ℝ) / 3) * u)) * u ^ (-(j : ℤ)) := by
  have hc0 : 0 < c := by linarith
  set ς : ℝ := c ^ (-(1 : ℝ) / 3)
  have hς_pos : 0 < ς := Real.rpow_pos_of_pos hc0 _
  have hu0 : 0 < u := by linarith
  have hcut : ∀ j ≤ 3, |iteratedDeriv j (fun t => 1 - chi0 t) u| ≤ 2 * Bχ * u ^ (-(j : ℤ)) := by
    intro j hj
    rcases eq_or_ne j 0 with rfl | hj0
    · simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one]
      have h1 : |1 - chi0 u| ≤ 1 := by
        rw [abs_of_nonneg (by linarith [chi0_le_one u])]; linarith [chi0_nonneg u]
      linarith
    · have hsub : iteratedDeriv j (fun t => 1 - chi0 t) u = -iteratedDeriv j chi0 u := by
        have h1 := iteratedDeriv_sub (n := j) (x := u) (contDiffAt_const (c := (1 : ℝ)))
          (contDiff_chi0.contDiffAt.of_le (by simp))
        have hc0' : iteratedDeriv j (fun _ : ℝ => (1 : ℝ)) u = 0 := by
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
          rw [iteratedDeriv_succ', show deriv (fun _ : ℝ => (1 : ℝ)) = 0 from funext fun _ => deriv_const _ _,
            iteratedDeriv_const_zero]
        rw [show (fun t => 1 - chi0 t) = (fun _ => (1 : ℝ)) - chi0 from rfl, h1, hc0', zero_sub]
      rw [hsub, abs_neg]
      by_cases h54 : u ≤ 5 / 4
      · have hpow : u ^ j ≤ 2 := by
          calc u ^ j ≤ (5 / 4 : ℝ) ^ j := pow_le_pow_left₀ hu0.le h54 j
            _ ≤ (5 / 4 : ℝ) ^ 3 := pow_le_pow_right₀ (by norm_num) hj
            _ ≤ 2 := by norm_num
        have h1 : (1 : ℝ) ≤ 2 * u ^ (-(j : ℤ)) := by
          rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, one_le_div (pow_pos hu0 j)]
          exact hpow
        calc |iteratedDeriv j chi0 u| ≤ Bχ * 1 := by rw [mul_one]; exact hBχ j hj u
          _ ≤ Bχ * (2 * u ^ (-(j : ℤ))) := mul_le_mul_of_nonneg_left h1 (by linarith)
          _ = 2 * Bχ * u ^ (-(j : ℤ)) := by ring
      · push Not at h54
        have hev : chi0 =ᶠ[𝓝 u] 0 := by
          filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds
            (show 5 / 4 < |u| by rw [abs_of_pos hu0]; exact h54)] with y hy
          exact chi0_eq_zero hy.le
        rw [hev.iteratedDeriv_eq j, iteratedDeriv_const_zero, abs_zero]
        positivity
  have hA_bd : ∀ j ≤ 3, ‖iteratedDeriv j (fun t => A (ς * t)) u‖ ≤
      (6 * max 1 ((2 / η) ^ 3) * C_A * Real.exp (-(η / 2) * ς * u)) * u ^ (-(j : ℤ)) := by
    intro j hj
    have h := scaled_amp_deriv_bound hη hCA hς_pos hA hu0.ne' j hj
    rw [abs_of_pos hu0] at h
    exact h
  have hY_bd : ∀ j ≤ 3, ‖iteratedDeriv j Y u‖ ≤ (C_Y * u ^ (-(2 * α + 3 / 2))) * u ^ (-(j : ℤ)) := by
    intro j hj
    have h := hY.far_bound j hj u (by rw [abs_of_pos hu0]; exact hu)
    rw [abs_of_pos hu0] at h
    have hrpow : u ^ (-(2 * α + 3 / 2) - (j : ℝ)) = u ^ (-(2 * α + 3 / 2)) * u ^ (-(j : ℤ)) := by
      rw [Real.rpow_sub hu0, Real.rpow_natCast, zpow_neg, zpow_natCast, div_eq_mul_inv]
    rw [hrpow] at h
    linarith
  have h12 := leibniz3_real_mul_bound (f := fun t => 1 - chi0 t) (g := fun t => A (ς * t)) (x := u)
    (M₁ := 2 * Bχ) (M₂ := 6 * max 1 ((2 / η) ^ 3) * C_A * Real.exp (-(η / 2) * ς * u)) (w := u)
    ((contDiff_const.sub contDiff_chi0).contDiffAt.of_le (by simp))
    ((hA.contDiff.comp ((contDiff_const.mul contDiff_id).of_le le_top)).contDiffAt)
    (by positivity) (by positivity) hu0 hcut hA_bd
  have h123 := leibniz3_bound
    (f := fun t => ((1 - chi0 t : ℝ) : ℂ) * A (ς * t)) (g := Y) (x := u)
    (M₁ := 8 * (2 * Bχ) * (6 * max 1 ((2 / η) ^ 3) * C_A * Real.exp (-(η / 2) * ς * u)))
    (M₂ := C_Y * u ^ (-(2 * α + 3 / 2))) (w := u)
    (((Complex.ofRealCLM.contDiff.comp (contDiff_const.sub contDiff_chi0)).contDiffAt.of_le (by simp)).mul
      ((hA.contDiff.comp ((contDiff_const.mul contDiff_id).of_le le_top)).contDiffAt))
    (hY.contDiffOn_Y.contDiffAt (isOpen_compl_singleton.mem_nhds hu0.ne'))
    (by positivity) (by positivity) hu0 h12 hY_bd
  intro j hj
  refine (h123 j hj).trans (le_of_eq ?_); ring

/-! ### Regime A: positive outer half-line for `0 < L ≤ 1` and `S ≥ 16` -/

set_option maxHeartbeats 1200000 in
theorem cusp_outer_pos_small {α η C_A C_Y : ℝ} (hα0 : 0 < α) (hα2 : α < 2) (hη : 0 < η)
    (hCA : 0 ≤ C_A) (hCY : 0 ≤ C_Y) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c L : ℝ), 1 ≤ c → 0 < L → L ≤ 1 → 16 ≤ c ^ ((2 : ℝ) / 3) * L →
      ∀ (A Y Y₀ R : ℝ → ℂ), CuspAmplitude η C_A A → CuspProfile α C_Y Y Y₀ R →
        ‖∫ u in Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) *
          (((1 - chi0 u : ℝ) : ℂ) * A (c ^ (-(1 : ℝ) / 3) * u) * Y u)‖ ≤
          C * (c ^ ((2 : ℝ) / 3) * L) ^ (-α - 1) := by
  obtain ⟨Bχ, hBχ1, hBχ⟩ := chi0_deriv_bound
  obtain ⟨Bρ, hBρ1, hBρ⟩ := rhoSaddle_deriv_bound
  obtain ⟨C2, hC2_nn, hC2⟩ := edgePhi_iteratedDeriv_bound 2 (by norm_num)
  obtain ⟨C3, hC3_nn, hC3⟩ := edgePhi_iteratedDeriv_bound 3 (by norm_num)
  obtain ⟨C4, hC4_nn, hC4⟩ := edgePhi_iteratedDeriv_bound 4 (by norm_num)
  set M₀ := 64 * (2 * Bχ) * (6 * max 1 ((2 / η) ^ 3) * C_A) * C_Y
  set q := 2 * α + 3 / 2
  set K_ns := max 1 (max (64 * 8 * (π ^ 2 / 6)) (max (64 * 16 * C3) (max (64 * 64 * C4) (max (2 * C2) (max (2 * C3) (2 * C4))))))
  -- Saddle constant + nonstationary IBP constant
  set C_sad := 8 * (Bρ * M₀ * 2 ^ q + 8 * Bρ * M₀ * 2 ^ (q + 1) * 4) / Real.sqrt (1 / 34)
  set C_ibp := 2 * ((104 * K_ns ^ 3) ^ 3 * (32 ^ 3) * (8 * (2 * 8 * Bρ) * M₀) * (2 ^ (q + 2) / (q + 2)))
  refine ⟨C_sad + C_ibp, by positivity, fun c L hc hL0 hL1 hS A Y Y₀ R hA hY => ?_⟩
  have hc0 : 0 < c := by linarith
  set ς : ℝ := c ^ (-(1 : ℝ) / 3)
  set S : ℝ := c ^ ((2 : ℝ) / 3) * L
  have hς_pos : 0 < ς := Real.rpow_pos_of_pos hc0 _
  have hς_le : ς ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc (by norm_num)
  have hS_pos : 0 < S := by linarith
  have hS_ge1 : 1 ≤ S := by linarith
  have hς_sq : c ^ ((2 : ℝ) / 3) * ς ^ 2 = 1 := by
    dsimp [ς]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; norm_num
  have hς_inv : ς⁻¹ = c ^ ((1 : ℝ) / 3) := by
    dsimp [ς]; rw [← Real.rpow_neg hc0.le]; congr 1; ring
  -- Saddle location `u₀ = tau0 L / ς ≥ √S ≥ 4`
  obtain ⟨ht_lo, ht_hi, ht_le2⟩ := tau0_small_bounds hL0 hL1
  set t : ℝ := tau0 L
  set u₀ : ℝ := t / ς
  have ht0 : 0 < t := tau0_pos hL0
  have hu0_lo : Real.sqrt S ≤ u₀ := by
    have hrt : Real.sqrt S = c ^ ((1 : ℝ) / 3) * Real.sqrt L := by
      dsimp [S]
      rw [Real.sqrt_mul (Real.rpow_nonneg hc0.le _),
        show Real.sqrt (c ^ ((2 : ℝ) / 3)) = c ^ ((1 : ℝ) / 3) by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hc0.le]; norm_num]
    have hu0_eq : u₀ = t * c ^ ((1 : ℝ) / 3) := by dsimp [u₀]; rw [div_eq_mul_inv, hς_inv]
    rw [hrt, hu0_eq]
    nlinarith [ht_lo, Real.rpow_pos_of_pos hc0 ((1 : ℝ) / 3)]
  have hu0_hi : u₀ ≤ 4 * Real.sqrt S := by
    have hrt : Real.sqrt S = c ^ ((1 : ℝ) / 3) * Real.sqrt L := by
      dsimp [S]
      rw [Real.sqrt_mul (Real.rpow_nonneg hc0.le _),
        show Real.sqrt (c ^ ((2 : ℝ) / 3)) = c ^ ((1 : ℝ) / 3) by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hc0.le]; norm_num]
    have hu0_eq : u₀ = t * c ^ ((1 : ℝ) / 3) := by dsimp [u₀]; rw [div_eq_mul_inv, hς_inv]
    rw [hrt, hu0_eq]
    nlinarith [ht_hi, Real.rpow_pos_of_pos hc0 ((1 : ℝ) / 3)]
  have hu0_ge4 : 4 ≤ u₀ := by
    have h4 : 4 ≤ Real.sqrt S := by rw [show (4 : ℝ) = Real.sqrt 16 by norm_num]; exact Real.sqrt_le_sqrt hS
    linarith
  have hu0_pos : 0 < u₀ := by linarith
  let g : ℝ → ℂ := fun u => ((1 - chi0 u : ℝ) : ℂ) * A (ς * u) * Y u
  have hg_cd : ContDiffOn ℝ 3 g (Ioi 0) :=
    (((Complex.ofRealCLM.contDiff.comp (contDiff_const.sub contDiff_chi0)).of_le (by simp)).contDiffOn.mul
      ((hA.contDiff.comp ((contDiff_const.mul contDiff_id).of_le le_top)).contDiffOn)).mul
      (hY.contDiffOn_Y.mono fun u (hu : 0 < u) => hu.ne')
  have hg_zero : ∀ u : ℝ, 0 < u → u ≤ 1 → g u = 0 := fun u _ hu1 => by
    simp [g, chi0_eq_one (by rw [abs_of_pos (by linarith : 0 < u)]; exact hu1)]
  have hg_bd : ∀ u : ℝ, 1 ≤ u → ∀ j ≤ 3, ‖iteratedDeriv j g u‖ ≤ M₀ * u ^ (-q) * u ^ (-(j : ℤ)) := by
    intro u hu j hj
    have h := outer_amp_deriv_bound hα0 hη hCA hCY hBχ1 hBχ hc hA hY hu j hj
    have hexp : Real.exp (-(η / 2) * ς * u) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ (η / 2) * ς * u := by positivity
      linarith
    calc ‖iteratedDeriv j g u‖ ≤ M₀ * (u ^ (-q) * Real.exp (-(η / 2) * ς * u)) * u ^ (-(j : ℤ)) := h
      _ ≤ M₀ * (u ^ (-q) * 1) * u ^ (-(j : ℤ)) := by gcongr
      _ = M₀ * u ^ (-q) * u ^ (-(j : ℤ)) := by ring
  let g_sad : ℝ → ℂ := fun u => (rhoSaddle (u / u₀) : ℂ) * g u
  let g_ns : ℝ → ℂ := fun u => ((1 - rhoSaddle (u / u₀) : ℝ) : ℂ) * g u
  have hsplit_pt : ∀ u : ℝ, Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g u =
      Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_sad u +
      Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_ns u := fun u => by
    dsimp [g_sad, g_ns]; push_cast; ring
  have hg_int_Ioi : ∀ (w : ℝ → ℝ), Continuous w → (∀ u, |w u| ≤ 1) →
      IntegrableOn (fun u => Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * ((w u : ℂ) * g u)) (Ioi 0) := by
    intro w hw hw1
    have hcont : ContinuousOn (fun u => Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * ((w u : ℂ) * g u)) (Ioi 0) :=
      ((Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        (contDiff_scaledPsi c L).continuous))).continuousOn).mul
        ((Complex.continuous_ofReal.comp hw).continuousOn.mul hg_cd.continuousOn)
    have hdom_int : IntegrableOn (fun u : ℝ => if u ≤ 1 then (0 : ℝ) else M₀ * u ^ (-q)) (Ioi 0) := by
      have h1 : IntegrableOn (fun u : ℝ => M₀ * u ^ (-q)) (Ioi 1) :=
        (integrableOn_Ioi_rpow_of_lt (show -q < -1 by dsimp [q]; linarith) zero_lt_one).const_mul M₀
      have h2 : IntegrableOn (fun u : ℝ => (Ioi (1 : ℝ)).indicator (fun x => M₀ * x ^ (-q)) u) (Ioi 0) :=
        (h1.integrable_indicator measurableSet_Ioi).integrableOn
      refine h2.congr_fun (fun u _ => ?_) measurableSet_Ioi
      by_cases hu : u ≤ 1
      · simp [hu]
      · push Not at hu
        simp [not_le.mpr hu, Set.indicator_of_mem (show u ∈ Ioi (1 : ℝ) from hu)]
    refine hdom_int.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hu1 : u ≤ 1
    · rw [ite_eq_left_iff.mpr (fun h => absurd hu1 h), hg_zero u hu hu1, norm_zero, mul_zero]
    · push Not at hu1
      rw [ite_eq_right_iff.mpr (fun h => absurd h (not_le.mpr hu1))]
      have h0 := hg_bd u hu1.le 0 (by omega)
      simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one] at h0
      calc |w u| * ‖g u‖ ≤ 1 * (M₀ * u ^ (-q)) := mul_le_mul (hw1 u) h0 (norm_nonneg _) zero_le_one
        _ = M₀ * u ^ (-q) := one_mul _
  have hint_sad := hg_int_Ioi (fun u => rhoSaddle (u / u₀))
    (contDiff_rhoSaddle.continuous.comp (continuous_id.div_const u₀))
    (fun u => by rw [abs_of_nonneg (rhoSaddle_nonneg _)]; exact rhoSaddle_le_one _)
  have hint_ns := hg_int_Ioi (fun u => 1 - rhoSaddle (u / u₀))
    (continuous_const.sub (contDiff_rhoSaddle.continuous.comp (continuous_id.div_const u₀)))
    (fun u => by rw [abs_of_nonneg (by linarith [rhoSaddle_le_one (u / u₀)])]; linarith [rhoSaddle_nonneg (u / u₀)])
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hsplit_pt u),
    integral_add hint_sad hint_ns]
  -- (1) Saddle piece on `[u₀/2, 2 u₀]` via `van_der_corput_second`
  have hSad : ‖∫ u in Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_sad u‖ ≤
      C_sad * S ^ (-α - 1) := by
    have hzero_sad : ∀ u : ℝ, u ≤ u₀ / 2 ∨ 2 * u₀ ≤ u → g_sad u = 0 := by
      intro u hu
      rcases hu with h1 | h1
      · have hle : u / u₀ ≤ 1 / 2 := (div_le_iff₀ hu0_pos).mpr (by linarith)
        simp [g_sad, rhoSaddle_eq_zero_of_le hle]
      · have hge : 7 / 4 ≤ u / u₀ := (le_div_iff₀ hu0_pos).mpr (by linarith)
        simp [g_sad, rhoSaddle_eq_zero_of_ge hge]
    have heq_int : ∫ u in Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_sad u =
        ∫ u in (u₀ / 2)..(2 * u₀), g_sad u * Complex.exp (Complex.I * (1 : ℝ) * (scaledPsi c L u : ℂ)) := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      have hcongr : ∫ u in Ioc (u₀ / 2) (2 * u₀), g_sad u * Complex.exp (Complex.I * (1 : ℝ) * (scaledPsi c L u : ℂ)) =
          ∫ u in Ioc (u₀ / 2) (2 * u₀), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_sad u := by
        refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
        simp [mul_comm]
      rw [hcongr]
      exact setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (s := Ioc (u₀ / 2) (2 * u₀)) (t := Ioi 0)
        (f := fun u => Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_sad u)
        measurableSet_Ioi.nullMeasurableSet
        (fun u hu => lt_of_lt_of_le (by positivity) hu.1.le)
        (Filter.Eventually.of_forall fun u hu => by
          have hnot : u ≤ u₀ / 2 ∨ 2 * u₀ < u := by
            have := hu.2; rw [mem_Ioc] at this; push Not at this
            rcases le_or_gt u (u₀ / 2) with h | h
            · exact Or.inl h
            · exact Or.inr (this h)
          rcases hnot with h1 | h1
          · rw [hzero_sad u (Or.inl h1), mul_zero]
          · rw [hzero_sad u (Or.inr h1.le), mul_zero])
    rw [heq_int]
    -- Verify `van_der_corput_second` on `[u₀/2, 2 u₀]` with `lam = u₀ / 34`
    have hφ : ∀ y ∈ Icc (u₀ / 2) (2 * u₀), HasDerivAt (scaledPsi c L) (deriv (scaledPsi c L) y) y :=
      fun y _ => ((contDiff_scaledPsi c L).differentiable (by simp) y).hasDerivAt
    have hφ' : ∀ y ∈ Icc (u₀ / 2) (2 * u₀), HasDerivAt (deriv (scaledPsi c L)) (iteratedDeriv 2 (scaledPsi c L) y) y :=
      fun y _ => by
        have hd := (((contDiff_scaledPsi c L).iterate_deriv 1).differentiable (by simp) y).hasDerivAt
        simpa [iteratedDeriv_succ, iteratedDeriv_one] using hd
    have hφ''_neg : ∀ y ∈ Icc (u₀ / 2) (2 * u₀), iteratedDeriv 2 (scaledPsi c L) y ≤ -(u₀ / 34) := by
      intro y hy
      have hy0 : 0 < y := by linarith [hy.1]
      rw [iteratedDeriv_scaledPsi hc0 2 y, edgePhi_iteratedDeriv_ge_two L 2 le_rfl,
        show (2 - 2 : ℕ) = 0 by rfl, iteratedDeriv_zero]
      have hςy_pos : 0 < ς * y := mul_pos hς_pos hy0
      have hςy_le4 : ς * y ≤ 4 := by
        have h1 : ς * y ≤ ς * (2 * u₀) := mul_le_mul_of_nonneg_left hy.2 hς_pos.le
        have h2 : ς * (2 * u₀) = 2 * t := by dsimp [u₀]; field_simp [hς_pos.ne']
        linarith
      have hm' := (hankelEdgeM'_bounds hςy_pos).1
      have hden : 1 + (ς * y) ^ 2 ≤ 17 := by nlinarith
      have hlb : ς * y / 17 ≤ hankelEdgeM' (ς * y) :=
        (div_le_div_of_nonneg_left hςy_pos.le (by positivity) hden).trans hm'
      have hed2 : edgePhiDeriv2 (ς * y) = -hankelEdgeM' (ς * y) := by unfold hankelEdgeM'; ring
      have hc1 : c * ς ^ 2 * ς = 1 := by
        dsimp [ς]; rw [mul_assoc, ← pow_succ, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le,
          show (-(1 : ℝ) / 3) * (3 : ℕ) = -1 by norm_num, Real.rpow_neg_one, mul_inv_cancel₀ hc0.ne']
      rw [hed2]
      have hmul : c * ς ^ 2 * (ς * y / 17) = y / 17 := by
        calc c * ς ^ 2 * (ς * y / 17) = (c * ς ^ 2 * ς) * (y / 17) := by ring
          _ = y / 17 := by rw [hc1, one_mul]
      have hprod : c * ς ^ 2 * (-hankelEdgeM' (ς * y)) ≤ -(y / 17) := by
        have h1 := mul_le_mul_of_nonneg_left hlb (show 0 ≤ c * ς ^ 2 by positivity)
        linarith
      calc c * ς ^ 2 * -hankelEdgeM' (ς * y) ≤ -(y / 17) := hprod
        _ ≤ -(u₀ / 34) := by linarith [hy.1]
    have hφ'_anti : AntitoneOn (deriv (scaledPsi c L)) (Icc (u₀ / 2) (2 * u₀)) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
        ((contDiff_scaledPsi c L).continuous_deriv (by simp)).continuousOn
        (fun y hy => (hφ' y (interior_subset hy)).hasDerivWithinAt)
        (fun y hy => by linarith [hφ''_neg y (interior_subset hy)])
    have hg_sad_cd : ContDiffOn ℝ 3 g_sad (Ioi 0) :=
      ((Complex.ofRealCLM.contDiff.comp (contDiff_rhoSaddle.comp (contDiff_id.div_const u₀))).of_le (by simp)).contDiffOn.mul hg_cd
    have hg_sad_bd : ∀ y ∈ Icc (u₀ / 2) (2 * u₀), ‖g_sad y‖ ≤ Bρ * M₀ * 2 ^ q * u₀ ^ (-q) := by
      intro y hy
      have hy1 : 1 ≤ y := by linarith [hy.1]
      dsimp only [g_sad]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hρ0 := hBρ 0 (by omega) (y / u₀)
      simp only [iteratedDeriv_zero] at hρ0
      have hg0 := hg_bd y hy1 0 (by omega)
      simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one] at hg0
      have hy_rpow : y ^ (-q) ≤ 2 ^ q * u₀ ^ (-q) := by
        have h1 : y ^ (-q) ≤ (u₀ / 2) ^ (-q) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hy.1 (by dsimp [q]; linarith)
        have h2 : (u₀ / 2) ^ (-q) = 2 ^ q * u₀ ^ (-q) := by
          rw [div_eq_mul_inv, Real.mul_rpow hu0_pos.le (by positivity),
            Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_neg, mul_comm]
        linarith
      calc |rhoSaddle (y / u₀)| * ‖g y‖ ≤ Bρ * (M₀ * y ^ (-q)) := mul_le_mul hρ0 hg0 (norm_nonneg _) (by linarith)
        _ ≤ Bρ * (M₀ * (2 ^ q * u₀ ^ (-q))) := by gcongr
        _ = Bρ * M₀ * 2 ^ q * u₀ ^ (-q) := by ring
    have hg_sad_deriv_bd : ∀ y ∈ Icc (u₀ / 2) (2 * u₀),
        ‖deriv g_sad y‖ ≤ 8 * Bρ * M₀ * 2 ^ (q + 1) * u₀ ^ (-q - 1) := by
      intro y hy
      have hy1 : 1 ≤ y := by linarith [hy.1]
      have hy0 : 0 < y := by linarith
      have hρ_bd : ∀ j ≤ 3, |iteratedDeriv j (fun t => rhoSaddle (t / u₀)) y| ≤ (8 * Bρ) * y ^ (-(j : ℤ)) := by
        intro j hj
        have hdiv : (fun t => rhoSaddle (t / u₀)) = fun t => rhoSaddle (u₀⁻¹ * t) := by ext t; ring_nf
        rw [hdiv, iteratedDeriv_comp_mul_left_R, abs_mul, abs_of_pos (pow_pos (inv_pos.mpr hu0_pos) j)]
        have h1 : (u₀⁻¹) ^ j ≤ 8 * y ^ (-(j : ℤ)) := by
          rw [zpow_neg, zpow_natCast, inv_pow, ← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (pow_pos hu0_pos j) (pow_pos hy0 j)]
          have hyj : y ^ j ≤ 8 * u₀ ^ j := by
            calc y ^ j ≤ (2 * u₀) ^ j := pow_le_pow_left₀ hy0.le hy.2 j
              _ = 2 ^ j * u₀ ^ j := mul_pow 2 u₀ j
              _ ≤ 2 ^ 3 * u₀ ^ j := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) (pow_nonneg hu0_pos.le j)
              _ = 8 * u₀ ^ j := by norm_num
          linarith
        calc (u₀⁻¹) ^ j * |iteratedDeriv j rhoSaddle (u₀⁻¹ * y)|
            ≤ (8 * y ^ (-(j : ℤ))) * Bρ := mul_le_mul h1 (hBρ j hj _) (abs_nonneg _) (by positivity)
          _ = 8 * Bρ * y ^ (-(j : ℤ)) := by ring
      have hleib := leibniz3_real_mul_bound (f := fun t => rhoSaddle (t / u₀)) (g := g) (x := y)
        (M₁ := 8 * Bρ) (M₂ := M₀ * y ^ (-q)) (w := y)
        ((contDiff_rhoSaddle.comp (contDiff_id.div_const u₀)).contDiffAt.of_le (by simp))
        (hg_cd.contDiffAt (isOpen_Ioi.mem_nhds hy0))
        (by positivity) (by positivity) hy0 hρ_bd (hg_bd y hy1) 1 (by omega)
      rw [iteratedDeriv_one, Nat.cast_one, zpow_neg_one] at hleib
      have hy_rpow : y ^ (-q) * y⁻¹ ≤ 2 ^ (q + 1) * u₀ ^ (-q - 1) := by
        have h1 : y ^ (-q) * y⁻¹ = y ^ (-q - 1) := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hy0]; rfl
        rw [h1]
        have h2 : y ^ (-q - 1) ≤ (u₀ / 2) ^ (-q - 1) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hy.1 (by dsimp [q]; linarith)
        have h3 : (u₀ / 2) ^ (-q - 1) = 2 ^ (q + 1) * u₀ ^ (-q - 1) := by
          rw [div_eq_mul_inv, Real.mul_rpow hu0_pos.le (by positivity),
            Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num),
            show -(-q - 1) = q + 1 by ring, mul_comm]
        linarith
      -- Wait: `8 * (8 * Bρ) = 64 * Bρ` vs `8 * Bρ`! Let's check `C_sad`: use `64 * Bρ`!
      -- Even simpler: direct product rule for `deriv g_sad y` (only order 1, gives factor 2 instead of 64)!
      have hdρ : HasDerivAt (fun t => rhoSaddle (t / u₀)) (deriv rhoSaddle (y / u₀) / u₀) y := by
        have h1 : HasDerivAt (fun t => t / u₀) (1 / u₀) y := (hasDerivAt_id y).div_const u₀
        have h2 := ((contDiff_rhoSaddle.differentiable (by simp) (y / u₀)).hasDerivAt).comp y h1
        exact h2.congr_deriv (by ring)
      have hdg : HasDerivAt g (deriv g y) y :=
        ((hg_cd.differentiableOn (by norm_num) y hy0).differentiableAt (isOpen_Ioi.mem_nhds hy0)).hasDerivAt
      have hprod := (hdρ.ofReal_comp).mul hdg
      rw [show deriv g_sad y = ((deriv rhoSaddle (y / u₀) / u₀ : ℝ) : ℂ) * g y + (rhoSaddle (y / u₀) : ℂ) * deriv g y from hprod.deriv]
      have hρ0 := hBρ 0 (by omega) (y / u₀); simp only [iteratedDeriv_zero] at hρ0
      have hρ1 := hBρ 1 (by omega) (y / u₀); rw [iteratedDeriv_one] at hρ1
      have hg0 := hg_bd y hy1 0 (by omega); simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one] at hg0
      have hg1 := hg_bd y hy1 1 (by omega); rw [iteratedDeriv_one, Nat.cast_one, zpow_neg_one] at hg1
      have hu0_inv : u₀⁻¹ ≤ 2 * y⁻¹ := by
        rw [inv_le_iff_one_le_mul₀ hu0_pos]; field_simp [hy0.ne']; linarith [hy.2]
      calc ‖((deriv rhoSaddle (y / u₀) / u₀ : ℝ) : ℂ) * g y + (rhoSaddle (y / u₀) : ℂ) * deriv g y‖
          ≤ ‖((deriv rhoSaddle (y / u₀) / u₀ : ℝ) : ℂ) * g y‖ + ‖(rhoSaddle (y / u₀) : ℂ) * deriv g y‖ := norm_add_le _ _
        _ = |deriv rhoSaddle (y / u₀)| * u₀⁻¹ * ‖g y‖ + |rhoSaddle (y / u₀)| * ‖deriv g y‖ := by
            simp [Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv, abs_of_pos hu0_pos]
        _ ≤ Bρ * (2 * y⁻¹) * (M₀ * y ^ (-q)) + Bρ * (M₀ * y ^ (-q) * y⁻¹) := by
            have h1 : |deriv rhoSaddle (y / u₀)| * u₀⁻¹ * ‖g y‖ ≤ Bρ * (2 * y⁻¹) * (M₀ * y ^ (-q)) :=
              mul_le_mul (mul_le_mul hρ1 hu0_inv (by positivity) (by linarith)) hg0 (norm_nonneg _) (by positivity)
            have h2 : |rhoSaddle (y / u₀)| * ‖deriv g y‖ ≤ Bρ * (M₀ * y ^ (-q) * y⁻¹) :=
              mul_le_mul hρ0 hg1 (norm_nonneg _) (by linarith)
            linarith
        _ = 3 * Bρ * M₀ * (y ^ (-q) * y⁻¹) := by ring
        _ ≤ 8 * Bρ * M₀ * (2 ^ (q + 1) * u₀ ^ (-q - 1)) := by
            have h38 : 3 * Bρ * M₀ ≤ 8 * Bρ * M₀ := by nlinarith [show 0 ≤ Bρ * M₀ by positivity]
            exact mul_le_mul h38 hy_rpow (by positivity) (by positivity)
        _ = 8 * Bρ * M₀ * 2 ^ (q + 1) * u₀ ^ (-q - 1) := by ring
    obtain ⟨hbv, hev_le⟩ := eVariationOn_le_of_deriv_bound (a := u₀ / 2) (b := 2 * u₀)
      (M' := 8 * Bρ * M₀ * 2 ^ (q + 1) * u₀ ^ (-q - 1)) (by linarith) (by positivity)
      isOpen_Ioi (fun y hy => lt_of_lt_of_le (by positivity) hy.1) (hg_sad_cd.of_le (by norm_num))
      hg_sad_deriv_bd
    have hvdc := van_der_corput_second (a := u₀ / 2) (b := 2 * u₀) (c := 1) (lam := u₀ / 34)
      (M := Bρ * M₀ * 2 ^ q * u₀ ^ (-q)) (by linarith) one_pos (by positivity)
      hφ hφ' (Or.inr hφ'_anti)
      (fun y hy => by rw [abs_of_neg (by linarith [hφ''_neg y hy])]; linarith [hφ''_neg y hy])
      (hg_sad_cd.continuousOn.mono fun y hy => lt_of_lt_of_le (by positivity) hy.1)
      hbv hg_sad_bd
    have hev_simp : (eVariationOn g_sad (Icc (u₀ / 2) (2 * u₀))).toReal ≤
        8 * Bρ * M₀ * 2 ^ (q + 1) * 4 * u₀ ^ (-q) := by
      have hlen : 2 * u₀ - u₀ / 2 ≤ 4 * u₀ := by linarith
      have hpow : u₀ ^ (-q - 1) * u₀ = u₀ ^ (-q) := by
        conv_rhs => rw [show -q = (-q - 1) + 1 by ring]
        rw [Real.rpow_add hu0_pos, Real.rpow_one]
      calc (eVariationOn g_sad (Icc (u₀ / 2) (2 * u₀))).toReal
          ≤ 8 * Bρ * M₀ * 2 ^ (q + 1) * u₀ ^ (-q - 1) * (2 * u₀ - u₀ / 2) := hev_le
        _ ≤ 8 * Bρ * M₀ * 2 ^ (q + 1) * u₀ ^ (-q - 1) * (4 * u₀) := by gcongr
        _ = 8 * Bρ * M₀ * 2 ^ (q + 1) * 4 * (u₀ ^ (-q - 1) * u₀) := by ring
        _ = 8 * Bρ * M₀ * 2 ^ (q + 1) * 4 * u₀ ^ (-q) := by rw [hpow]
    have hsqrt_eq : Real.sqrt (1 * (u₀ / 34)) = Real.sqrt (1 / 34) * u₀ ^ ((1 : ℝ) / 2) := by
      rw [one_mul, show u₀ / 34 = (1 / 34) * u₀ by ring, Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow u₀]
    have hu0_S : u₀ ^ (-q) / u₀ ^ ((1 : ℝ) / 2) ≤ S ^ (-α - 1) := by
      rw [← Real.rpow_sub hu0_pos, show -q - 1 / 2 = 2 * (-α - 1) by dsimp [q]; ring]
      have h1 : u₀ ^ (2 * (-α - 1)) ≤ (Real.sqrt S) ^ (2 * (-α - 1)) :=
        Real.rpow_le_rpow_of_nonpos (Real.sqrt_pos.mpr hS_pos) hu0_lo (by linarith)
      have h2 : (Real.sqrt S) ^ (2 * (-α - 1)) = S ^ (-α - 1) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hS_pos.le]; congr 1; ring
      linarith
    calc ‖∫ u in (u₀ / 2)..(2 * u₀), g_sad u * Complex.exp (Complex.I * (1 : ℝ) * (scaledPsi c L u : ℂ))‖
        ≤ 8 * (Bρ * M₀ * 2 ^ q * u₀ ^ (-q) + (eVariationOn g_sad (Icc (u₀ / 2) (2 * u₀))).toReal) /
            Real.sqrt (1 * (u₀ / 34)) := hvdc
      _ ≤ 8 * (Bρ * M₀ * 2 ^ q * u₀ ^ (-q) + 8 * Bρ * M₀ * 2 ^ (q + 1) * 4 * u₀ ^ (-q)) /
            (Real.sqrt (1 / 34) * u₀ ^ ((1 : ℝ) / 2)) := by
            rw [hsqrt_eq]; gcongr
      _ = C_sad * (u₀ ^ (-q) / u₀ ^ ((1 : ℝ) / 2)) := by dsimp [C_sad]; ring
      _ ≤ C_sad * S ^ (-α - 1) := mul_le_mul_of_nonneg_left hu0_S (by positivity)
  -- (2) Non-stationary pieces on `[1/2, 3 u₀ / 4]` and `[3 u₀ / 2, ∞)` via `ibp3_interval` and `ibp3_Ioi`
  have hNS : ‖∫ u in Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_ns u‖ ≤
      C_ibp * S ^ (-α - 1) := by
    -- Split `Ioi 0` into `[1/2, 3 u₀ / 4]` and `Ioi (3 u₀ / 2)` (vanishes on `(0, 1]` and `[3 u₀ / 4, 3 u₀ / 2]`)
    have hns_zero_in : ∀ u : ℝ, 0 < u → u ≤ 1 → g_ns u = 0 := fun u hu hu1 => by
      simp [g_ns, hg_zero u hu hu1]
    have hns_zero_mid : ∀ u : ℝ, 3 / 4 * u₀ ≤ u → u ≤ 3 / 2 * u₀ → g_ns u = 0 := fun u h1 h2 => by
      have hρ : rhoSaddle (u / u₀) = 1 :=
        rhoSaddle_eq_one (by rw [le_div_iff₀ hu0_pos]; linarith) (by rw [div_le_iff₀ hu0_pos]; linarith)
      simp [g_ns, hρ]
    have hsplit_ns : ∫ u in Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_ns u =
        (∫ u in (1 / 2 : ℝ)..(3 / 4 * u₀), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_ns u) +
        (∫ u in Ioi (3 / 2 * u₀), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_ns u) := by
      have h1 : (∫ u in Ioc (0 : ℝ) (3 / 2 * u₀), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_ns u) +
          (∫ u in Ioi (3 / 2 * u₀), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_ns u) =
          ∫ u in Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_ns u := by
        rw [← setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, mem_Ioi.mp h2])
          measurableSet_Ioi (hint_ns.mono_set Ioc_subset_Ioi_self) (hint_ns.mono_set (Ioi_subset_Ioi (by positivity))),
          Ioc_union_Ioi_eq_Ioi (by positivity)]
      rw [← h1]
      congr 1
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (s := Ioc (1 / 2) (3 / 4 * u₀)) (t := Ioc 0 (3 / 2 * u₀))
        (f := fun u => Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_ns u)
        measurableSet_Ioc.nullMeasurableSet
        (Ioc_subset_Ioc (by norm_num) (by linarith))
        (Filter.Eventually.of_forall fun u hu => by
          have hnot : u ≤ 1 / 2 ∨ 3 / 4 * u₀ < u := by
            have := hu.2; rw [mem_Ioc] at this; push Not at this
            rcases le_or_gt u (1 / 2) with h | h
            · exact Or.inl h
            · exact Or.inr (this h)
          rcases hnot with h1 | h1
          · rw [hns_zero_in u hu.1.1 (by linarith), mul_zero]
          · rw [hns_zero_mid u h1.le hu.1.2, mul_zero])
    -- Derivative bound on `g_ns` for `u ≥ 1`
    have hg_ns_cd : ContDiffOn ℝ 3 g_ns (Ioi 0) :=
      ((Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (contDiff_rhoSaddle.comp (contDiff_id.div_const u₀)))).of_le
        (by simp)).contDiffOn.mul hg_cd
    have hg_ns_bd : ∀ u : ℝ, 1 ≤ u → ∀ j ≤ 3,
        ‖iteratedDeriv j g_ns u‖ ≤ (8 * (2 * 8 * Bρ) * M₀) * u ^ (-q) * u ^ (-(j : ℤ)) := by
      intro u hu
      have hu0 : 0 < u := by linarith
      have hcut : ∀ j ≤ 3, |iteratedDeriv j (fun s => 1 - rhoSaddle (s / u₀)) u| ≤ (2 * 8 * Bρ) * u ^ (-(j : ℤ)) := by
        intro j hj
        rcases eq_or_ne j 0 with rfl | hj0
        · simp only [iteratedDeriv_zero, Nat.cast_zero, neg_zero, zpow_zero, mul_one]
          have h1 : |1 - rhoSaddle (u / u₀)| ≤ 1 := by
            rw [abs_of_nonneg (by linarith [rhoSaddle_le_one (u / u₀)])]; linarith [rhoSaddle_nonneg (u / u₀)]
          linarith
        · have hdiv : (fun s => rhoSaddle (s / u₀)) = fun s => rhoSaddle (u₀⁻¹ * s) := by ext s; ring_nf
          have hsub : iteratedDeriv j (fun s => 1 - rhoSaddle (s / u₀)) u =
              -iteratedDeriv j (fun s => rhoSaddle (u₀⁻¹ * s)) u := by
            have h1 := iteratedDeriv_sub (n := j) (x := u) (contDiffAt_const (c := (1 : ℝ)))
              ((contDiff_rhoSaddle.comp (contDiff_const (c := u₀⁻¹) |>.mul contDiff_id)).contDiffAt.of_le (by simp))
            dsimp only [Function.comp_def, id_eq] at h1
            have hc0' : iteratedDeriv j (fun _ : ℝ => (1 : ℝ)) u = 0 := by
              obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
              rw [iteratedDeriv_succ', show deriv (fun _ : ℝ => (1 : ℝ)) = 0 from funext fun _ => deriv_const _ _,
                iteratedDeriv_const_zero]
            rw [show (fun s => 1 - rhoSaddle (s / u₀)) = (fun _ => (1 : ℝ)) - (fun s => rhoSaddle (u₀⁻¹ * s)) by
              ext s; simp [div_eq_mul_inv, mul_comm], h1, hc0', zero_sub]
          rw [hsub, abs_neg, iteratedDeriv_comp_mul_left_R, abs_mul, abs_of_pos (pow_pos (inv_pos.mpr hu0_pos) j)]
          by_cases h2u : u ≤ 2 * u₀
          · have h1 : (u₀⁻¹) ^ j ≤ 8 * u ^ (-(j : ℤ)) := by
              rw [zpow_neg, zpow_natCast, inv_pow, ← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (pow_pos hu0_pos j) (pow_pos hu0 j)]
              have huj : u ^ j ≤ 8 * u₀ ^ j := by
                calc u ^ j ≤ (2 * u₀) ^ j := pow_le_pow_left₀ hu0.le h2u j
                  _ = 2 ^ j * u₀ ^ j := mul_pow 2 u₀ j
                  _ ≤ 2 ^ 3 * u₀ ^ j := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) (pow_nonneg hu0_pos.le j)
                  _ = 8 * u₀ ^ j := by norm_num
              linarith
            calc (u₀⁻¹) ^ j * |iteratedDeriv j rhoSaddle (u₀⁻¹ * u)|
                ≤ (8 * u ^ (-(j : ℤ))) * Bρ := mul_le_mul h1 (hBρ j hj _) (abs_nonneg _) (by positivity)
              _ ≤ 2 * 8 * Bρ * u ^ (-(j : ℤ)) := by nlinarith [show 0 ≤ Bρ * u ^ (-(j : ℤ)) by positivity]
          · push Not at h2u
            have hev : rhoSaddle =ᶠ[𝓝 (u₀⁻¹ * u)] 0 := by
              filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds
                (show 7 / 4 < u₀⁻¹ * u by rw [inv_mul_eq_div, lt_div_iff₀ hu0_pos]; linarith)] with y hy
              exact rhoSaddle_eq_zero_of_ge hy.le
            rw [hev.iteratedDeriv_eq j, iteratedDeriv_const_zero, abs_zero, mul_zero]; positivity
      have hleib := leibniz3_real_mul_bound (f := fun s => 1 - rhoSaddle (s / u₀)) (g := g) (x := u)
        (M₁ := 2 * 8 * Bρ) (M₂ := M₀ * u ^ (-q)) (w := u)
        ((contDiff_const.sub (contDiff_rhoSaddle.comp (contDiff_id.div_const u₀))).contDiffAt.of_le (by simp))
        (hg_cd.contDiffAt (isOpen_Ioi.mem_nhds hu0))
        (by positivity) (by positivity) hu0 hcut (hg_bd u hu)
      intro j hj
      refine (hleib j hj).trans (le_of_eq ?_); ring
    -- Also for `u ∈ [1/2, 1]`, `g_ns` and all its derivatives vanish!
    have hg_ns_bd_all : ∀ u : ℝ, 1 / 2 ≤ u → ∀ j ≤ 3,
        ‖iteratedDeriv j g_ns u‖ ≤ (8 * (2 * 8 * Bρ) * M₀) * u ^ (-q) * u ^ (-(j : ℤ)) := by
      intro u hu j hj
      rcases le_or_gt 1 u with h1 | h1
      · exact hg_ns_bd u h1 j hj
      · have hev : g_ns =ᶠ[𝓝 u] 0 := by
          filter_upwards [(isOpen_Ioo (a := (0 : ℝ)) (b := 1)).mem_nhds ⟨by linarith, h1⟩] with y hy
          exact hns_zero_in y hy.1 hy.2.le
        rw [hev.iteratedDeriv_eq j, iteratedDeriv_const_zero, norm_zero]
        have hu0 : 0 < u := by linarith
        positivity
    -- Helper: phase derivative ratios on `(0, 3 u₀ / 4]` and `[3 u₀ / 2, ∞)`
    have hψ_inner_ratio : ∀ u ∈ Icc (1 / 2 : ℝ) (3 / 4 * u₀),
        S / 32 ≤ |deriv (scaledPsi c L) u| ∧
        ∀ j ∈ ({1, 2, 3} : Finset ℕ),
          |iteratedDeriv (j + 1) (scaledPsi c L) u| ≤ K_ns * u ^ (-(j : ℤ)) * |deriv (scaledPsi c L) u| := by
      intro u hu
      have hu0 : 0 < u := by linarith [hu.1]
      have hςu_le : ς * u ≤ 3 / 4 * t := by
        have := mul_le_mul_of_nonneg_left hu.2 hς_pos.le
        rwa [show ς * (3 / 4 * u₀) = 3 / 4 * t by dsimp [u₀]; field_simp [hς_pos.ne']] at this
      have hdiff := hankelEdgeM_diff_small_inner hL0 hL1 (by positivity) hςu_le
      have hψ1 : S / 32 ≤ deriv (scaledPsi c L) u := by
        rw [deriv_scaledPsi hc0, edgePhiDeriv_eq_sub_m]
        have := mul_le_mul_of_nonneg_left hdiff (Real.rpow_nonneg hc0.le ((2 : ℝ) / 3))
        dsimp [S, ς] at this ⊢
        calc c ^ ((2 : ℝ) / 3) * L / 32 = c ^ ((2 : ℝ) / 3) * (1 / 32 * L) := by ring
          _ ≤ c ^ ((2 : ℝ) / 3) * (L - hankelEdgeM (c ^ (-(1 : ℝ) / 3) * u)) := this
      have habs1 : S / 32 ≤ |deriv (scaledPsi c L) u| := by rw [abs_of_pos (by linarith)]; exact hψ1
      refine ⟨habs1, fun j hj => ?_⟩
      rw [iteratedDeriv_scaledPsi hc0]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      have hu_le_4rtS : u ≤ 4 * Real.sqrt S := hu.2.trans (by linarith)
      have hu2_le : u ^ 2 ≤ 16 * S := by
        have := mul_self_le_mul_self hu0.le hu_le_4rtS
        rw [mul_assoc, ← _root_.sq, mul_comm (Real.sqrt S), mul_assoc, Real.mul_self_sqrt hS_pos.le] at this
        nlinarith
      rcases hj with rfl | rfl | rfl
      · -- j = 1: |ψ''(u)| ≤ (π²/6) u ≤ 64 * 4 * (π²/6) * u⁻¹ * (S/32)
        rw [edgePhi_iteratedDeriv_ge_two L 2 le_rfl, show (2 - 2 : ℕ) = 0 by rfl, iteratedDeriv_zero,
          abs_mul, abs_of_nonneg (by positivity)]
        have hςu_pos : 0 < ς * u := mul_pos hς_pos hu0
        have h2 : |edgePhiDeriv2 (ς * u)| ≤ π ^ 2 / 6 * (ς * u) := by
          have := (edgePhiDeriv2_abs_le hςu_pos.ne').trans (min_le_left _ _)
          simpa only [abs_of_pos hςu_pos] using this
        have hc1 : c * ς ^ 2 * ς = 1 := by
          dsimp [ς]; rw [mul_assoc, ← pow_succ, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le,
            show (-(1 : ℝ) / 3) * (3 : ℕ) = -1 by norm_num, Real.rpow_neg_one, mul_inv_cancel₀ hc0.ne']
        have hbd : c * ς ^ 2 * |edgePhiDeriv2 (ς * u)| ≤ π ^ 2 / 6 * u := by
          calc c * ς ^ 2 * |edgePhiDeriv2 (ς * u)| ≤ c * ς ^ 2 * (π ^ 2 / 6 * (ς * u)) :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
            _ = (c * ς ^ 2 * ς) * (π ^ 2 / 6 * u) := by ring
            _ = π ^ 2 / 6 * u := by rw [hc1, one_mul]
        have hK : 64 * 8 * (π ^ 2 / 6) ≤ K_ns := le_trans (le_max_left _ _) (le_max_right _ _)
        have hu_inv : u ≤ 16 * S * u ^ (-1 : ℤ) := by
          rw [zpow_neg_one, ← div_eq_mul_inv, le_div_iff₀ hu0]; nlinarith
        calc c * ς ^ 2 * |edgePhiDeriv2 (ς * u)| ≤ π ^ 2 / 6 * u := hbd
          _ ≤ π ^ 2 / 6 * (16 * S * u ^ (-1 : ℤ)) := mul_le_mul_of_nonneg_left hu_inv (by positivity)
          _ = (64 * 8 * (π ^ 2 / 6)) * u ^ (-1 : ℤ) * (S / 32) := by ring
          _ ≤ K_ns * u ^ (-1 : ℤ) * |deriv (scaledPsi c L) u| := by gcongr
      · -- j = 2: |ψ'''(u)| ≤ C3 ≤ 64 * 16 * C3 * u⁻² * (S/32)
        have hc1 : c * ς ^ 3 = 1 := by
          dsimp [ς]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le,
            show (-(1 : ℝ) / 3) * (3 : ℕ) = -1 by norm_num, Real.rpow_neg_one, mul_inv_cancel₀ hc0.ne']
        rw [hc1, one_mul]
        have h3 := (hC3 L (ς * u)).trans (div_le_self hC3_nn (one_le_pow₀ (by linarith [abs_nonneg (ς * u)])))
        have hK : 64 * 16 * C3 ≤ K_ns := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
        have h1 : (1 : ℝ) ≤ 16 * S * u ^ (-2 : ℤ) := by
          rw [zpow_neg, show (2 : ℤ) = (2 : ℕ) from rfl, zpow_natCast, ← div_eq_mul_inv, one_le_div (pow_pos hu0 2)]
          exact hu2_le
        calc |iteratedDeriv 3 (edgePhi L) (ς * u)| ≤ C3 * 1 := by rw [mul_one]; exact h3
          _ ≤ C3 * (16 * S * u ^ (-2 : ℤ)) := mul_le_mul_of_nonneg_left h1 hC3_nn
          _ ≤ (64 * 16 * C3) * u ^ (-2 : ℤ) * (S / 32) := by
              have : 0 ≤ C3 * S * u ^ (-2 : ℤ) := by positivity
              nlinarith
          _ ≤ K_ns * u ^ (-2 : ℤ) * |deriv (scaledPsi c L) u| := by gcongr
      · -- j = 3: |ψ^{(4)}(u)| = ς |Φ^{(4)}(ς u)| ≤ ς C4; note ς u³ = (ς u) u² ≤ 2 * 16 S = 32 S
        have hc1 : c * ς ^ 4 = ς := by
          have h3 : c * ς ^ 3 = 1 := by
            dsimp [ς]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le,
              show (-(1 : ℝ) / 3) * (3 : ℕ) = -1 by norm_num, Real.rpow_neg_one, mul_inv_cancel₀ hc0.ne']
          calc c * ς ^ 4 = (c * ς ^ 3) * ς := by ring
            _ = ς := by rw [h3, one_mul]
        rw [hc1, abs_mul, abs_of_pos hς_pos]
        have h4 := (hC4 L (ς * u)).trans (div_le_self hC4_nn (one_le_pow₀ (by linarith [abs_nonneg (ς * u)])))
        have hK : 64 * 64 * C4 ≤ K_ns :=
          le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
        have hςu3 : ς * u ^ 3 ≤ 32 * S := by
          have hςu2 : ς * u ≤ 2 := hςu_le.trans (by linarith)
          calc ς * u ^ 3 = (ς * u) * u ^ 2 := by ring
            _ ≤ 2 * (16 * S) := mul_le_mul hςu2 hu2_le (sq_nonneg u) (by norm_num)
            _ = 32 * S := by ring
        have h1 : ς ≤ 32 * S * u ^ (-3 : ℤ) := by
          rw [zpow_neg, show (3 : ℤ) = (3 : ℕ) from rfl, zpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hu0 3)]
          exact hςu3
        calc ς * |iteratedDeriv 4 (edgePhi L) (ς * u)| ≤ (32 * S * u ^ (-3 : ℤ)) * C4 :=
              mul_le_mul h1 h4 (abs_nonneg _) (by positivity)
          _ ≤ (64 * 64 * C4) * u ^ (-3 : ℤ) * (S / 32) := by
              have : 0 ≤ C4 * S * u ^ (-3 : ℤ) := by positivity
              nlinarith
          _ ≤ K_ns * u ^ (-3 : ℤ) * |deriv (scaledPsi c L) u| := by gcongr
    have hψ_outer_ratio : ∀ u ∈ Ici (3 / 2 * u₀),
        S / 32 ≤ |deriv (scaledPsi c L) u| ∧
        ∀ j ∈ ({1, 2, 3} : Finset ℕ),
          |iteratedDeriv (j + 1) (scaledPsi c L) u| ≤ K_ns * u ^ (-(j : ℤ)) * |deriv (scaledPsi c L) u| := by
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le (by positivity) hu
      have hςu_ge : 3 / 2 * t ≤ ς * u := by
        have := mul_le_mul_of_nonneg_left hu hς_pos.le
        rwa [show ς * (3 / 2 * u₀) = 3 / 2 * t by dsimp [u₀]; field_simp [hς_pos.ne']] at this
      obtain ⟨hle4, hge4, hgeL⟩ := hankelEdgeM_diff_small_outer hL0 hL1 hςu_ge
      have hψ_neg : deriv (scaledPsi c L) u ≤ -(S / 32) := by
        rw [deriv_scaledPsi hc0, edgePhiDeriv_eq_sub_m]
        have := mul_le_mul_of_nonneg_left hgeL (Real.rpow_nonneg hc0.le ((2 : ℝ) / 3))
        have hneg : c ^ ((2 : ℝ) / 3) * (L - hankelEdgeM (ς * u)) = -(c ^ ((2 : ℝ) / 3) * (hankelEdgeM (ς * u) - L)) := by ring
        dsimp [S, ς] at this hneg ⊢; linarith
      have habs1 : S / 32 ≤ |deriv (scaledPsi c L) u| := by rw [abs_of_neg (by linarith)]; linarith
      refine ⟨habs1, fun j hj => ?_⟩
      rw [iteratedDeriv_scaledPsi hc0]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases le_or_gt (ς * u) 4 with hv4 | hv4
      · -- `ς * u ≤ 4`: `|ψ'(u)| ≥ c^{2/3} * (ς u)² / 64 = u² / 64`
        have habs_u2 : u ^ 2 / 64 ≤ |deriv (scaledPsi c L) u| := by
          rw [abs_of_neg (by linarith), deriv_scaledPsi hc0, edgePhiDeriv_eq_sub_m]
          have h1 := mul_le_mul_of_nonneg_left (hle4 hv4) (Real.rpow_nonneg hc0.le ((2 : ℝ) / 3))
          have h2 : c ^ ((2 : ℝ) / 3) * (1 / 64 * (ς * u) ^ 2) = u ^ 2 / 64 := by
            calc c ^ ((2 : ℝ) / 3) * (1 / 64 * (ς * u) ^ 2)
                = (c ^ ((2 : ℝ) / 3) * ς ^ 2) * (u ^ 2 / 64) := by ring
              _ = u ^ 2 / 64 := by rw [hς_sq, one_mul]
          have hneg : -(c ^ ((2 : ℝ) / 3) * (L - hankelEdgeM (ς * u))) = c ^ ((2 : ℝ) / 3) * (hankelEdgeM (ς * u) - L) := by ring
          dsimp [ς] at h1 h2 hneg ⊢; linarith
        rcases hj with rfl | rfl | rfl
        · rw [edgePhi_iteratedDeriv_ge_two L 2 le_rfl, show (2 - 2 : ℕ) = 0 by rfl, iteratedDeriv_zero,
            abs_mul, abs_of_nonneg (by positivity)]
          have hςu_pos : 0 < ς * u := mul_pos hς_pos hu0
          have h2 : |edgePhiDeriv2 (ς * u)| ≤ π ^ 2 / 6 * (ς * u) := by
            have := (edgePhiDeriv2_abs_le hςu_pos.ne').trans (min_le_left _ _)
            simpa only [abs_of_pos hςu_pos] using this
          have hc1 : c * ς ^ 2 * ς = 1 := by
            dsimp [ς]; rw [mul_assoc, ← pow_succ, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le,
              show (-(1 : ℝ) / 3) * (3 : ℕ) = -1 by norm_num, Real.rpow_neg_one, mul_inv_cancel₀ hc0.ne']
          have hK : 64 * 8 * (π ^ 2 / 6) ≤ K_ns := le_trans (le_max_left _ _) (le_max_right _ _)
          have hu_eq : u = u ^ (-1 : ℤ) * u ^ 2 := by
            rw [zpow_neg_one]; field_simp [hu0.ne']
          calc c * ς ^ 2 * |edgePhiDeriv2 (ς * u)| ≤ (c * ς ^ 2 * ς) * (π ^ 2 / 6 * u) := by
                have := mul_le_mul_of_nonneg_left h2 (show 0 ≤ c * ς ^ 2 by positivity); linarith
            _ = π ^ 2 / 6 * (u ^ (-1 : ℤ) * u ^ 2) := by rw [hc1, one_mul, ← hu_eq]
            _ ≤ (64 * 8 * (π ^ 2 / 6)) * u ^ (-1 : ℤ) * (u ^ 2 / 64) := by
                have : 0 ≤ π ^ 2 / 6 * u ^ (-1 : ℤ) * u ^ 2 := by positivity
                nlinarith
            _ ≤ K_ns * u ^ (-1 : ℤ) * |deriv (scaledPsi c L) u| := by gcongr
        · have hc1 : c * ς ^ 3 = 1 := by
            dsimp [ς]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le,
              show (-(1 : ℝ) / 3) * (3 : ℕ) = -1 by norm_num, Real.rpow_neg_one, mul_inv_cancel₀ hc0.ne']
          rw [hc1, one_mul]
          have h3 := (hC3 L (ς * u)).trans (div_le_self hC3_nn (one_le_pow₀ (by linarith [abs_nonneg (ς * u)])))
          have hK : 64 * 16 * C3 ≤ K_ns := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
          have h1 : (1 : ℝ) = u ^ (-2 : ℤ) * u ^ 2 := by
            rw [zpow_neg, show (2 : ℤ) = (2 : ℕ) from rfl, zpow_natCast]; field_simp [hu0.ne']
          calc |iteratedDeriv 3 (edgePhi L) (ς * u)| ≤ C3 * (u ^ (-2 : ℤ) * u ^ 2) := by rw [← h1, mul_one]; exact h3
            _ ≤ (64 * 16 * C3) * u ^ (-2 : ℤ) * (u ^ 2 / 64) := by
                have : 0 ≤ C3 * u ^ (-2 : ℤ) * u ^ 2 := by positivity
                nlinarith
            _ ≤ K_ns * u ^ (-2 : ℤ) * |deriv (scaledPsi c L) u| := by gcongr
        · have hc1 : c * ς ^ 4 = ς := by
            have h3 : c * ς ^ 3 = 1 := by
              dsimp [ς]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le,
                show (-(1 : ℝ) / 3) * (3 : ℕ) = -1 by norm_num, Real.rpow_neg_one, mul_inv_cancel₀ hc0.ne']
            calc c * ς ^ 4 = (c * ς ^ 3) * ς := by ring
              _ = ς := by rw [h3, one_mul]
          rw [hc1, abs_mul, abs_of_pos hς_pos]
          have h4 := (hC4 L (ς * u)).trans (div_le_self hC4_nn (one_le_pow₀ (by linarith [abs_nonneg (ς * u)])))
          have hK : 64 * 64 * C4 ≤ K_ns :=
            le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
          have hς_le' : ς ≤ 4 * u ^ (-3 : ℤ) * u ^ 2 := by
            rw [zpow_neg, show (3 : ℤ) = (3 : ℕ) from rfl, zpow_natCast, ← div_eq_mul_inv,
              div_mul_eq_mul_div, le_div_iff₀ (pow_pos hu0 3)]
            nlinarith [sq_nonneg u]
          calc ς * |iteratedDeriv 4 (edgePhi L) (ς * u)| ≤ (4 * u ^ (-3 : ℤ) * u ^ 2) * C4 :=
                mul_le_mul hς_le' h4 (abs_nonneg _) (by positivity)
            _ ≤ (64 * 64 * C4) * u ^ (-3 : ℤ) * (u ^ 2 / 64) := by
                have : 0 ≤ C4 * u ^ (-3 : ℤ) * u ^ 2 := by positivity
                nlinarith
            _ ≤ K_ns * u ^ (-3 : ℤ) * |deriv (scaledPsi c L) u| := by gcongr
      · -- `ς * u > 4`: `|ψ'(u)| ≥ c^{2/3} / 2` and `|Φ^{(j+1)}(ς u)| ≤ C_{j+1} (ς u)^{-j}`
        have habs_c23 : c ^ ((2 : ℝ) / 3) / 2 ≤ |deriv (scaledPsi c L) u| := by
          rw [abs_of_neg (by linarith), deriv_scaledPsi hc0, edgePhiDeriv_eq_sub_m]
          have h1 := mul_le_mul_of_nonneg_left (hge4 hv4.le) (Real.rpow_nonneg hc0.le ((2 : ℝ) / 3))
          have hneg : -(c ^ ((2 : ℝ) / 3) * (L - hankelEdgeM (ς * u))) = c ^ ((2 : ℝ) / 3) * (hankelEdgeM (ς * u) - L) := by ring
          dsimp [ς] at h1 hneg ⊢; linarith
        have hstep : ∀ (k : ℕ) (Ck : ℝ), 0 ≤ Ck → 2 * Ck ≤ K_ns →
            |iteratedDeriv (k + 1) (edgePhi L) (ς * u)| ≤ Ck / (1 + |ς * u|) ^ k →
            |c * ς ^ (k + 1) * iteratedDeriv (k + 1) (edgePhi L) (ς * u)| ≤
              K_ns * u ^ (-(k : ℤ)) * |deriv (scaledPsi c L) u| := by
          intro k Ck hCk hK_le hbound
          rw [abs_mul, abs_of_nonneg (by positivity)]
          have hden : (ς * u) ^ k ≤ (1 + |ς * u|) ^ k := by
            rw [abs_of_pos (by positivity)]
            exact pow_le_pow_left₀ (by positivity) (by linarith) k
          have h1 : |iteratedDeriv (k + 1) (edgePhi L) (ς * u)| ≤ Ck / (ς * u) ^ k :=
            hbound.trans (div_le_div_of_nonneg_left hCk (pow_pos (by positivity) k) hden)
          have hc_pow : c * ς ^ (k + 1) / (ς * u) ^ k = c ^ ((2 : ℝ) / 3) * u ^ (-(k : ℤ)) := by
            rw [mul_pow, zpow_neg, zpow_natCast, pow_succ]
            have hcs : c * ς = c ^ ((2 : ℝ) / 3) := by
              dsimp [ς]
              calc c * c ^ (-(1 : ℝ) / 3) = c ^ (1 : ℝ) * c ^ (-(1 : ℝ) / 3) := by rw [Real.rpow_one]
                _ = c ^ ((1 : ℝ) + (-(1 : ℝ) / 3)) := (Real.rpow_add hc0 _ _).symm
                _ = c ^ ((2 : ℝ) / 3) := by norm_num
            have hςk : ς ^ k ≠ 0 := pow_ne_zero k hς_pos.ne'
            have huk : u ^ k ≠ 0 := pow_ne_zero k hu0.ne'
            field_simp [hςk, huk]; rw [← hcs]
          calc c * ς ^ (k + 1) * |iteratedDeriv (k + 1) (edgePhi L) (ς * u)|
              ≤ c * ς ^ (k + 1) * (Ck / (ς * u) ^ k) := mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = Ck * (c * ς ^ (k + 1) / (ς * u) ^ k) := by ring
            _ = (2 * Ck) * u ^ (-(k : ℤ)) * (c ^ ((2 : ℝ) / 3) / 2) := by rw [hc_pow]; ring
            _ ≤ K_ns * u ^ (-(k : ℤ)) * |deriv (scaledPsi c L) u| := by gcongr
        rcases hj with rfl | rfl | rfl
        · exact hstep 1 C2 hC2_nn (by simp only [K_ns]; exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))) (hC2 L (ς * u))
        · exact hstep 2 C3 hC3_nn (by simp only [K_ns]; exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))))) (hC3 L (ς * u))
        · exact hstep 3 C4 hC4_nn (by simp only [K_ns]; exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))))) (hC4 L (ς * u))
    -- Apply `ibp3_interval` on `[1/2, 3/4 * u₀]` and `ibp3_Ioi` on `Ioi (3/2 * u₀)`
    set M_ns := 8 * (2 * 8 * Bρ) * M₀
    have hvan_half : ∀ j ≤ 2, iteratedDeriv j g_ns (1 / 2) = 0 := by
      intro j _
      have hev : g_ns =ᶠ[𝓝 (1 / 2 : ℝ)] 0 := by
        filter_upwards [(isOpen_Ioo (a := (0 : ℝ)) (b := 1)).mem_nhds (by norm_num)] with y hy
        exact hns_zero_in y hy.1 hy.2.le
      rw [hev.iteratedDeriv_eq j, iteratedDeriv_const_zero]
    have hvan_34 : ∀ j ≤ 2, iteratedDeriv j g_ns (3 / 4 * u₀) = 0 :=
      iteratedDeriv_eq_zero_of_eq_zero_on_Ioo isOpen_Ioi hg_ns_cd
        (a := 3 / 4 * u₀) (b := 3 / 2 * u₀) (by linarith)
        ⟨le_rfl, by linarith⟩ (mem_Ioi.mpr (by positivity)) (fun y hy => hns_zero_mid y hy.1.le hy.2.le)
    have hvan_32 : ∀ j ≤ 2, iteratedDeriv j g_ns (3 / 2 * u₀) = 0 :=
      iteratedDeriv_eq_zero_of_eq_zero_on_Ioo isOpen_Ioi hg_ns_cd
        (a := 3 / 4 * u₀) (b := 3 / 2 * u₀) (by linarith)
        ⟨by linarith, le_rfl⟩ (mem_Ioi.mpr (by positivity)) (fun y hy => hns_zero_mid y hy.1.le hy.2.le)
    have hU_in : IsOpen (Ioo (0 : ℝ) (7 / 8 * u₀)) := isOpen_Ioo
    have hne_in : ∀ x ∈ Ioo (0 : ℝ) (7 / 8 * u₀), deriv (scaledPsi c L) x ≠ 0 := by
      intro x hx
      rw [deriv_scaledPsi hc0, edgePhiDeriv_eq_sub_m]
      have hςx_lt : ς * x < t := by
        have h1 : ς * x < ς * (7 / 8 * u₀) := mul_lt_mul_of_pos_left hx.2 hς_pos
        have h2 : ς * (7 / 8 * u₀) = 7 / 8 * t := by dsimp [u₀]; field_simp [hς_pos.ne']
        linarith
      have hm_lt : hankelEdgeM (ς * x) < L := by
        rw [← ceEll_tau0 hL0]
        exact hankelEdgeM_strictMonoOn (mul_nonneg hς_pos.le hx.1.le) ht0.le hςx_lt
      exact ne_of_gt (mul_pos (Real.rpow_pos_of_pos hc0 _) (sub_pos.mpr hm_lt))
    have hU_out : IsOpen (Ioi (5 / 4 * u₀)) := isOpen_Ioi
    have hne_out : ∀ x ∈ Ioi (5 / 4 * u₀), deriv (scaledPsi c L) x ≠ 0 := by
      intro x hx
      have hx0 : 0 < x := lt_trans (by positivity) hx
      rw [deriv_scaledPsi hc0, edgePhiDeriv_eq_sub_m]
      have hςx_gt : t < ς * x := by
        have h1 : ς * (5 / 4 * u₀) < ς * x := mul_lt_mul_of_pos_left hx hς_pos
        have h2 : ς * (5 / 4 * u₀) = 5 / 4 * t := by dsimp [u₀]; field_simp [hς_pos.ne']
        linarith
      have hm_gt : L < hankelEdgeM (ς * x) := by
        rw [← ceEll_tau0 hL0]
        exact hankelEdgeM_strictMonoOn ht0.le (mul_nonneg hς_pos.le hx0.le) hςx_gt
      exact ne_of_lt (mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos hc0 _) (sub_neg.mpr hm_gt))
    have hibp_in := ibp3_interval (a := 1 / 2) (b := 3 / 4 * u₀) (by linarith) hU_in
      (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      (φ := scaledPsi c L) (h := g_ns) (B := fun u => M_ns * u ^ (-q)) (w := fun u => u)
      (Λ := S / 32) (K := K_ns)
      (((contDiff_scaledPsi c L).of_le (by simp)).contDiffOn)
      (hg_ns_cd.mono fun x hx => hx.1) hne_in (by positivity) (le_max_left _ _)
      hvan_half hvan_34 (fun x hx => by linarith [hx.1]) (fun x hx => by
        have hx0 : 0 < x := by linarith [hx.1]
        positivity)
      (fun x hx => (hψ_inner_ratio x hx).1) (fun x hx => (hψ_inner_ratio x hx).2)
      (fun x hx => hg_ns_bd_all x hx.1)
      (by
        have hcont : ContinuousOn (fun u : ℝ => M_ns * u ^ (-q) * u ^ (-3 : ℤ)) (Icc (1 / 2) (3 / 4 * u₀)) :=
          (continuousOn_const.mul (continuousOn_id.rpow_const fun x hx => Or.inl (show x ≠ 0 by linarith [hx.1]))).mul
            (continuousOn_id.zpow₀ (-3) fun x hx => Or.inl (show x ≠ 0 by linarith [hx.1]))
        exact hcont.intervalIntegrable_of_Icc (by linarith))
    have hibp_out := ibp3_Ioi (a := 3 / 2 * u₀) hU_out (fun x hx => lt_of_lt_of_le (by linarith) hx)
      (φ := scaledPsi c L) (h := g_ns) (B := fun u => M_ns * u ^ (-q)) (w := fun u => u)
      (Λ := S / 32) (K := K_ns)
      (((contDiff_scaledPsi c L).of_le (by simp)).contDiffOn)
      (hg_ns_cd.mono fun x hx => lt_trans (by positivity) hx) hne_out (by positivity) (le_max_left _ _)
      hvan_32 (fun x hx => lt_of_lt_of_le (by positivity) hx)
      (fun x hx => by have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx; positivity)
      (fun x hx => (hψ_outer_ratio x hx).1) (fun x hx => (hψ_outer_ratio x hx).2)
      (fun x hx => hg_ns_bd_all x (by linarith [mem_Ici.mp hx]))
      (hint_ns.mono_set (Ioi_subset_Ioi (by positivity)))
      (by
        have heq : EqOn (fun u : ℝ => M_ns * u ^ (-q) * u ^ (-3 : ℤ))
            (fun u : ℝ => M_ns * u ^ (-q - 3)) (Ioi (3 / 2 * u₀)) := fun u hu => by
          have hu0 : 0 < u := lt_trans (by positivity) hu
          dsimp only
          rw [zpow_neg, show (3 : ℤ) = (3 : ℕ) from rfl, zpow_natCast, ← Real.rpow_natCast u 3,
            ← Real.rpow_neg hu0.le, mul_assoc, ← Real.rpow_add hu0, show -q + -(3 : ℕ) = -q - 3 by push_cast; ring]
        exact IntegrableOn.congr_fun
          ((integrableOn_Ioi_rpow_of_lt (show -q - 3 < -1 by dsimp [q]; linarith) (by positivity)).const_mul M_ns)
          (fun u hu => (heq hu).symm) measurableSet_Ioi)
      (fun j hj => by
        have ht : Tendsto (fun u : ℝ => M_ns * u ^ (-q - (j : ℝ))) atTop (𝓝 0) := by
          have hpos : 0 < q + (j : ℝ) := by dsimp [q]; linarith [Nat.cast_nonneg (α := ℝ) j]
          simpa [show -(q + (j : ℝ)) = -q - (j : ℝ) by ring] using (tendsto_rpow_neg_atTop hpos).const_mul M_ns
        refine ht.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
        have hu_zpow : u ^ (-(j : ℤ)) = u ^ (-(j : ℝ)) := by
          rw [zpow_neg, zpow_natCast, Real.rpow_neg hu.le, Real.rpow_natCast]
        calc M_ns * u ^ (-q - (j : ℝ)) = M_ns * (u ^ (-q) * u ^ (-(j : ℝ))) := by
              rw [← Real.rpow_add hu]; rfl
          _ = M_ns * u ^ (-q) * u ^ (-(j : ℤ)) := by rw [← hu_zpow]; dsimp only [M_ns]; ring)
    -- Bound both integrals by `M_ns * (1 / (q + 2))` (note `g_ns = 0` on `[1/2, 1]`, or use `1 / (q + 2)` with `1/2` -> `2^{q+2}`?
    -- Wait: on `[1/2, 3/4 u₀]`, `∫_{1/2}^{3/4 u₀} u^{-q-3} du ≤ 2^{q+2} / (q+2)`! Better: integrate from `a = 1` instead of `1/2`,
    -- since `g_ns` vanishes on `(0, 1]` so `iteratedDeriv j g_ns 1 = 0` by `iteratedDeriv_eq_zero_of_eq_zero_on_Ioo`!!)
    -- Let's bound `∫_{1/2}^{3/4 u₀}` using `a = 1`: actually `ibp_in` already ran on `[1/2, 3/4 u₀]` where `∫` is `≤ (1/2)^{-q-2}/(q+2)`,
    -- OR we just change `1/2` to `1` right above! Even cleaner! Let's check: with `1` instead of `1/2`, `∫_1^∞ u^{-q-3} = 1/(q+2)`!
    have hint_in_le : ∫ u in (1 / 2 : ℝ)..(3 / 4 * u₀), M_ns * u ^ (-q) * u ^ (-3 : ℤ) ≤
        M_ns * (2 ^ (q + 2) / (q + 2)) := by
      have hcongr : ∫ u in (1 / 2 : ℝ)..(3 / 4 * u₀), M_ns * u ^ (-q) * u ^ (-3 : ℤ) =
          M_ns * ∫ u in (1 / 2 : ℝ)..(3 / 4 * u₀), u ^ (-q - 3) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun u hu => ?_
        rw [uIcc_of_le (by linarith)] at hu
        have hu0 : 0 < u := by linarith [hu.1]
        rw [zpow_neg, show (3 : ℤ) = (3 : ℕ) from rfl, zpow_natCast, ← Real.rpow_natCast u 3,
          ← Real.rpow_neg hu0.le, mul_assoc, ← Real.rpow_add hu0, show -q + -(3 : ℕ) = -q - 3 by push_cast; ring]
      rw [hcongr, integral_rpow (Or.inr ⟨by dsimp [q]; linarith, fun h => by rw [uIcc_of_le (by linarith)] at h; linarith [h.1]⟩)]
      have h1 : ((3 / 4 * u₀) ^ (-q - 3 + 1) - (1 / 2 : ℝ) ^ (-q - 3 + 1)) / (-q - 3 + 1) ≤
          2 ^ (q + 2) / (q + 2) := by
        rw [show -q - 3 + 1 = -(q + 2) by ring, div_neg, ← neg_div, neg_sub, sub_div]
        have h2 : (1 / 2 : ℝ) ^ (-(q + 2)) = 2 ^ (q + 2) := by
          rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_neg]
        rw [h2]
        have hnn : 0 ≤ (3 / 4 * u₀) ^ (-(q + 2)) / (q + 2) := by dsimp [q]; positivity
        linarith
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have hint_out_le : ∫ u in Ioi (3 / 2 * u₀), M_ns * u ^ (-q) * u ^ (-3 : ℤ) ≤
        M_ns * (1 / (q + 2)) := by
      have hcongr : ∫ u in Ioi (3 / 2 * u₀), M_ns * u ^ (-q) * u ^ (-3 : ℤ) =
          M_ns * ∫ u in Ioi (3 / 2 * u₀), u ^ (-q - 3) := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
        have hu0 : 0 < u := lt_trans (by positivity) hu
        rw [zpow_neg, show (3 : ℤ) = (3 : ℕ) from rfl, zpow_natCast, ← Real.rpow_natCast u 3,
          ← Real.rpow_neg hu0.le, mul_assoc, ← Real.rpow_add hu0, show -q + -(3 : ℕ) = -q - 3 by push_cast; ring]
      rw [hcongr, integral_Ioi_rpow_of_lt (show -q - 3 < -1 by dsimp [q]; linarith) (by positivity),
        show -q - 3 + 1 = -(q + 2) by ring, div_neg, ← neg_div, neg_neg]
      have hpow_le : (3 / 2 * u₀) ^ (-(q + 2)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by dsimp [q]; linarith)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact div_le_div_of_nonneg_right hpow_le (by dsimp [q]; linarith)
    -- Wait: `hint_in_le` has `2^{q+2}` whereas `C_ibp` had `1`, let's bump `C_ibp` to have `2^{q+2}` (since `1 ≤ 2^{q+2}`!).
    have hS3 : (S / 32) ^ (-3 : ℤ) ≤ 32 ^ 3 * S ^ (-α - 1) := by
      have h1 : (S / 32) ^ (-3 : ℤ) = 32 ^ 3 * S ^ (-3 : ℝ) := by
        rw [zpow_neg, show (3 : ℤ) = (3 : ℕ) from rfl, zpow_natCast, div_pow, inv_div,
          Real.rpow_neg hS_pos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        ring_nf
      rw [h1]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hS_ge1 (by linarith)) (by positivity)
    rw [hsplit_ns]
    have h2q : (1 : ℝ) ≤ 2 ^ (q + 2) := Real.one_le_rpow (by norm_num) (by dsimp [q]; linarith)
    -- Oops! Let's fix `C_ibp` in the `set` above to include `2 ^ (q + 2)` in the next edit!
    calc ‖(∫ u in (1 / 2 : ℝ)..(3 / 4 * u₀), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_ns u) +
            ∫ u in Ioi (3 / 2 * u₀), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_ns u‖
        ≤ ‖∫ u in (1 / 2 : ℝ)..(3 / 4 * u₀), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_ns u‖ +
          ‖∫ u in Ioi (3 / 2 * u₀), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_ns u‖ := norm_add_le _ _
      _ ≤ (104 * K_ns ^ 3) ^ 3 * (S / 32) ^ (-3 : ℤ) * (M_ns * (2 ^ (q + 2) / (q + 2))) +
          (104 * K_ns ^ 3) ^ 3 * (S / 32) ^ (-3 : ℤ) * (M_ns * (1 / (q + 2))) := by
          have h1 := hibp_in.trans (mul_le_mul_of_nonneg_left hint_in_le (by positivity))
          have h2 := hibp_out.trans (mul_le_mul_of_nonneg_left hint_out_le (by positivity))
          linarith
      _ ≤ 2 * ((104 * K_ns ^ 3) ^ 3 * (32 ^ 3 * S ^ (-α - 1)) * (M_ns * (2 ^ (q + 2) / (q + 2)))) := by
          have h12 : M_ns * (1 / (q + 2)) ≤ M_ns * (2 ^ (q + 2) / (q + 2)) := by
            gcongr
          have hsum : (104 * K_ns ^ 3) ^ 3 * (S / 32) ^ (-3 : ℤ) * (M_ns * (2 ^ (q + 2) / (q + 2))) +
              (104 * K_ns ^ 3) ^ 3 * (S / 32) ^ (-3 : ℤ) * (M_ns * (1 / (q + 2))) ≤
              2 * ((104 * K_ns ^ 3) ^ 3 * (S / 32) ^ (-3 : ℤ) * (M_ns * (2 ^ (q + 2) / (q + 2)))) := by
            have : 0 ≤ (104 * K_ns ^ 3) ^ 3 * (S / 32) ^ (-3 : ℤ) := by positivity
            nlinarith
          exact hsum.trans (by gcongr)
      _ = C_ibp * S ^ (-α - 1) := by dsimp [C_ibp, M_ns]; ring
  calc ‖(∫ u in Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_sad u) +
          ∫ u in Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_ns u‖
      ≤ ‖∫ u in Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_sad u‖ +
        ‖∫ u in Ioi (0 : ℝ), Complex.exp (Complex.I * (scaledPsi c L u : ℂ)) * g_ns u‖ := norm_add_le _ _
    _ ≤ C_sad * S ^ (-α - 1) + C_ibp * S ^ (-α - 1) := add_le_add hSad hNS
    _ = (C_sad + C_ibp) * S ^ (-α - 1) := by ring


end FormalResearch.SignUncertainty.FctCuspEdge
