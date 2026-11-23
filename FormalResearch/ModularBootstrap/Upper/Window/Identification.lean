/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalResearch
-/
module

public import FormalResearch.ModularBootstrap.Upper.Window.WindowLimit
public import FormalResearch.Special.AiryAsymPos
public import FormalResearch.Complex.HadamardAiry

/-!
# Identification of the Window Limit with the Airy Product (`ut:ID`, Lemma ID)

This module proves **Lemma ID** (`ut:ID`) of `upper_transfer.tex` (lines 521–572):

* `CStar` (`C_* = 4π √κ`) and `CStarF` (`C_*^{(f)} = C_* κ^{2(f - 1)}`);
* `refApprox`, `refApproxLimit`: the reference-comb approximant and its `K → ∞` limit;
* `refApproxLimit_eq_exp_mul_airyAi_sq` (**Step 2**): combining Step 1 (`continuumFQ_sub_lobe_asymptotic`)
  with the Hadamard product of `Ai` (`airyAiC_hadamard`) yields
  `refApproxLimit σ = refApproxLimit 0 * (airyAi (-κ σ) / airyAi 0)^2 * exp (2 β κ σ)` with
  `0 < refApproxLimit 0`;
* `beta_eq_zero_and_cStar` (**Step 3**): comparing Step 3 continuum bounds
  (`continuumFQ_AK_add_sum_phiQuantile_bound`, `sum_log_site_shift_neg_bound`) with the
  positive-axis asymptotics of `Ai` (`airyAi_sub_leading_le`) at `x = κ a → +∞` forces `β = 0`
  and `refApproxLimit 0 = C_* Ai(0)^2`, so `refApproxLimit σ = C_* Ai(-κ σ)^2` for all `σ : ℝ`;
* `lemma_ID` (**Step 4**): for any finite modification `(σ_f^*, σ_k^*, ε̂_k^*)` satisfying the
  reference tail bounds, `W̃^{±(f)}(σ) = C_*^{(f)} κ (W^{(f)}(-κ σ)).re` for all `σ : ℝ`;
* `lemma_ID_design`: specialization to the `f = 1` design `designWindowW N etaStar d`.
-/

namespace FormalResearch.ModularBootstrap.Upper.Window

open Complex Real Filter Topology Set
open scoped BigOperators
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Holes
open FormalResearch.Special
open FormalResearch.Hadamard

@[expose] public section

/-! ### Section 1: Normalization Constants and Reference Approximant -/

/-- Normalization constant `C_* = 4π √κ` of Lemma ID (`ut:ID`). -/
noncomputable def CStar : ℝ := 4 * π * Real.sqrt kappaAiry

/-- Level-`f` normalization constant `C_*^{(f)} = C_* κ^{2(f - 1)}` (`ut:ID`). -/
noncomputable def CStarF (f : ℕ) : ℝ := CStar * kappaAiry ^ (2 * ((f : ℤ) - 1))

lemma CStar_pos : 0 < CStar := by
  unfold CStar
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (Real.sqrt_pos.mpr kappaAiry_pos)

lemma CStarF_pos (f : ℕ) : 0 < CStarF f := by
  unfold CStarF
  have hκ := kappaAiry_pos
  exact mul_pos CStar_pos (zpow_pos hκ _)

/-- Finite-`K` reference approximant `exp(FQ_{A_K}(σ) - 2π σ_-^{3/2}) ∏_{k=1}^K (σ - s_k)^2`. -/
noncomputable def refApprox (K : ℕ) (σ : ℝ) : ℝ :=
  Real.exp (continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ)) *
    ∏ k ∈ Finset.Icc 1 K, (σ - sNodeAiry k) ^ 2

/-- Reference window limit `W̃_{ref}(σ) = lim_{K → ∞} refApprox K σ`. -/
noncomputable def refApproxLimit (σ : ℝ) : ℝ :=
  limUnder atTop (fun K : ℕ => refApprox K σ)

lemma sNodeAiry_pos (k : ℕ) : 0 < sNodeAiry k := by
  unfold sNodeAiry
  exact div_pos (abs_pos.mpr (airyZero_neg k).ne) kappaAiry_pos

lemma airyAi_pos_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 < airyAi x :=
  airyAi_pos_of_gt_first (lt_of_lt_of_le airyZero_one.2 (by linarith))

private lemma sNodeAiry_tail_hyp :
    ∃ C_t > 0, ∀ k : ℕ, 1 < k →
      |sNodeAiry k - phiWKB k| ≤ C_t * (k : ℝ) ^ (-(4 / 3 : ℝ)) ∧
        |(0 : ℝ)| ≤ C_t * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨C₀, hC₀, hδ⟩ := deltaWKB_le_exists
  refine ⟨C₀ / kappaAiry, div_pos hC₀ kappaAiry_pos, fun k hk => ?_⟩
  rw [sNodeAiry_sub_phiWKB (by omega), neg_div, abs_neg, abs_div, abs_of_pos kappaAiry_pos]
  refine ⟨?_, ?_⟩
  · calc |deltaWKB k| / kappaAiry ≤ (C₀ * (k : ℝ) ^ (-(4 / 3 : ℝ))) / kappaAiry :=
          div_le_div_of_nonneg_right (hδ k (by omega)) kappaAiry_pos.le
      _ = (C₀ / kappaAiry) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by ring
  · rw [abs_zero]
    exact mul_nonneg (div_pos hC₀ kappaAiry_pos).le (Real.rpow_nonneg (Nat.cast_nonneg k) _)

lemma refApprox_eq_windowFiniteProd {K : ℕ} (hK : 1 ≤ K) (σ : ℝ) :
    refApprox K σ = windowFiniteProd 1 (sNodeAiry 1) sNodeAiry (fun _ => 0) K σ * (σ - sNodeAiry 1) := by
  unfold refApprox windowFiniteProd
  have hIcc : Finset.Icc 1 K = insert 1 (Finset.Icc 2 K) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : 1 ∉ Finset.Icc 2 K := by simp
  rw [hIcc, Finset.prod_insert hnot]
  have hprod_eq : ∏ k ∈ Finset.Icc 2 K, ((σ - sNodeAiry k) ^ 2 + (0 : ℝ) ^ 2) =
      ∏ k ∈ Finset.Icc 2 K, (σ - sNodeAiry k) ^ 2 := by
    refine Finset.prod_congr rfl fun k _ => by ring
  rw [show (1 + 1 : ℕ) = 2 by rfl, hprod_eq]
  ring

private lemma tendsto_tildeW_of_bounds (f N : ℕ) (hf : 1 ≤ f) (hN : f ≤ N)
    {M C_t : ℝ} (hM : 0 < M) (hCt : 0 < C_t)
    {σf : ℝ} {σSeq εHat : ℕ → ℝ}
    (hσf : |σf| ≤ M)
    (hmod : ∀ k ∈ Finset.Icc (f + 1) N, |σSeq k| ≤ M ∧ |εHat k| ≤ M)
    (htail : ∀ k : ℕ, N < k →
      |σSeq k - phiWKB k| ≤ C_t * (k : ℝ) ^ (-(4 / 3 : ℝ)) ∧ |εHat k| ≤ C_t * (k : ℝ) ^ (-(1 / 3 : ℝ)))
    (σ : ℝ) :
    Tendsto (fun K : ℕ => windowFiniteProd f σf σSeq εHat K σ) atTop
      (𝓝 (tildeW f σf σSeq εHat σ)) := by
  set S : ℝ := |σ| + 1
  obtain ⟨K_min, C, _, hKmin1, _, hrate⟩ :=
    tendsto_windowFiniteProd_uniform f N hf hN hM hCt (by positivity : 0 ≤ S)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt (C / ε)
  refine ⟨max K_min (K₀ + 1), fun K hK => ?_⟩
  have hKm : K_min ≤ K := (le_max_left _ _).trans hK
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKmin1.trans hKm
  have hlt : C / (K : ℝ) < ε := by
    rw [div_lt_iff₀ hK_pos]
    have hK₀_lt : (K₀ : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : K₀ < K)
    have h1 : C / ε < (K : ℝ) := hK₀.trans hK₀_lt
    rw [div_lt_iff₀ hε] at h1
    linarith
  have hS_eq : S = |σ| + 1 := rfl
  have hbd := ((hrate hσf hmod htail).2 (σ := σ) hKm
    ⟨by linarith [neg_abs_le σ, hS_eq], by linarith [le_abs_self σ, hS_eq]⟩).trans_lt hlt
  simpa [Real.dist_eq] using hbd

lemma tendsto_refApprox (σ : ℝ) :
    Tendsto (fun K : ℕ => refApprox K σ) atTop (𝓝 (refApproxLimit σ)) := by
  obtain ⟨C_t, hCt, htail⟩ := sNodeAiry_tail_hyp
  set M : ℝ := |sNodeAiry 1| + 1
  have hconv := tendsto_tildeW_of_bounds 1 1 le_rfl le_rfl (by positivity : 0 < M) hCt
    (by dsimp [M]; linarith) (fun k hk => by simp only [Finset.mem_Icc] at hk; omega) htail σ
  have hconv_mul := hconv.mul_const (σ - sNodeAiry 1)
  have hconv_ref : Tendsto (fun K : ℕ => refApprox K σ) atTop
      (𝓝 (tildeW 1 (sNodeAiry 1) sNodeAiry (fun _ => 0) σ * (σ - sNodeAiry 1))) := by
    refine hconv_mul.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with K hK
    exact (refApprox_eq_windowFiniteProd hK σ).symm
  rw [refApproxLimit, hconv_ref.limUnder_eq]
  exact hconv_ref

lemma refApproxLimit_eq_tildeW_mul (σ : ℝ) :
    refApproxLimit σ = tildeW 1 (sNodeAiry 1) sNodeAiry (fun _ => 0) σ * (σ - sNodeAiry 1) := by
  obtain ⟨C_t, hCt, htail⟩ := sNodeAiry_tail_hyp
  set M : ℝ := |sNodeAiry 1| + 1
  have hconv := tendsto_tildeW_of_bounds 1 1 le_rfl le_rfl (by positivity : 0 < M) hCt
    (by dsimp [M]; linarith) (fun k hk => by simp only [Finset.mem_Icc] at hk; omega) htail σ
  have hconv_ref : Tendsto (fun K : ℕ => refApprox K σ) atTop
      (𝓝 (tildeW 1 (sNodeAiry 1) sNodeAiry (fun _ => 0) σ * (σ - sNodeAiry 1))) := by
    refine (hconv.mul_const (σ - sNodeAiry 1)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with K hK
    exact (refApprox_eq_windowFiniteProd hK σ).symm
  exact tendsto_nhds_unique (tendsto_refApprox σ) hconv_ref

lemma continuous_refApproxLimit : Continuous refApproxLimit := by
  obtain ⟨C_t, hCt, htail⟩ := sNodeAiry_tail_hyp
  set M : ℝ := |sNodeAiry 1| + 1
  have hc := continuous_tildeW 1 1 le_rfl le_rfl (by positivity : 0 < M) hCt
    (by dsimp [M]; linarith) (fun k hk => by simp only [Finset.mem_Icc] at hk; omega) htail
  have heq : refApproxLimit = fun σ => tildeW 1 (sNodeAiry 1) sNodeAiry (fun _ => 0) σ * (σ - sNodeAiry 1) :=
    funext refApproxLimit_eq_tildeW_mul
  rw [heq]
  exact hc.mul (continuous_id.sub continuous_const)

/-! ### Section 2: Step 2 via the Hadamard Product of `Ai` -/

/-- Partial real Hadamard product `∏_{k=1}^K (1 - σ / s_k) exp(σ / s_k)`. -/
private noncomputable def hadamardPartialReal (K : ℕ) (σ : ℝ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 K, (1 - σ / sNodeAiry k) * Real.exp (σ / sNodeAiry k)

private lemma hadamardPartialReal_cast (K : ℕ) (σ : ℝ) :
    (hadamardPartialReal K σ : ℂ) =
      ∏ n ∈ Finset.range K,
        (1 - ((-kappaAiry * σ : ℝ) : ℂ) / airyA n) *
          Complex.exp (((-kappaAiry * σ : ℝ) : ℂ) / airyA n) := by
  unfold hadamardPartialReal
  rw [show Finset.Icc 1 K = (Finset.range K).image (· + 1) by
    ext k; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro ⟨hk1, hkK⟩; exact ⟨k - 1, by omega, by omega⟩
    · rintro ⟨n, hn, rfl⟩; omega]
  rw [Finset.prod_image (fun a _ b _ h => by omega), Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun n _ => ?_
  have hneg : airyZero (n + 1) < 0 := airyZero_neg (n + 1)
  have hκ_ne : kappaAiry ≠ 0 := kappaAiry_pos.ne'
  have hs_ne : sNodeAiry (n + 1) ≠ 0 := (sNodeAiry_pos (n + 1)).ne'
  have ha_eq : airyA n = ((-kappaAiry * sNodeAiry (n + 1) : ℝ) : ℂ) := by
    unfold airyA sNodeAiry
    rw [abs_of_neg hneg]
    push_cast
    field_simp [hκ_ne]
  rw [ha_eq]
  have hdiv : ((-kappaAiry * σ : ℝ) : ℂ) / ((-kappaAiry * sNodeAiry (n + 1) : ℝ) : ℂ) =
      ((σ / sNodeAiry (n + 1) : ℝ) : ℂ) := by
    push_cast
    field_simp [hκ_ne, hs_ne]
  rw [hdiv]
  push_cast
  rfl

private lemma tendsto_hadamardPartialReal (σ : ℝ) :
    Tendsto (fun K : ℕ => hadamardPartialReal K σ) atTop
      (𝓝 ((airyAi (-kappaAiry * σ) / airyAi 0) * Real.exp ((airyAi' 0 / airyAi 0) * kappaAiry * σ))) := by
  have ⟨_, hprod, hid⟩ := airyAiC_hadamard
  have hp := hprod.hasProd (Set.mem_univ ((-kappaAiry * σ : ℝ) : ℂ))
  have hrange : Tendsto Finset.range atTop (atTop : Filter (Finset ℕ)) := by
    rw [Filter.tendsto_atTop]
    intro s₀
    refine eventually_atTop.mpr ⟨s₀.sup (· + 1), fun K hK x hx => Finset.mem_range.mpr ?_⟩
    exact lt_of_lt_of_le (Finset.le_sup (f := (· + 1)) hx) hK
  have ht_complex : Tendsto (fun K : ℕ => ∏ n ∈ Finset.range K,
      (1 - ((-kappaAiry * σ : ℝ) : ℂ) / airyA n) *
        Complex.exp (((-kappaAiry * σ : ℝ) : ℂ) / airyA n)) atTop
      (𝓝 (∏' n : ℕ, (1 - ((-kappaAiry * σ : ℝ) : ℂ) / airyA n) *
        Complex.exp (((-kappaAiry * σ : ℝ) : ℂ) / airyA n))) :=
    hp.comp hrange
  have ht_re := (Complex.continuous_re.continuousAt.tendsto.comp ht_complex).congr
    (fun K => by simpa [Function.comp] using congrArg Complex.re (hadamardPartialReal_cast K σ).symm)
  have hlim_eq : (∏' n : ℕ, (1 - ((-kappaAiry * σ : ℝ) : ℂ) / airyA n) *
      Complex.exp (((-kappaAiry * σ : ℝ) : ℂ) / airyA n)).re =
      (airyAi (-kappaAiry * σ) / airyAi 0) * Real.exp ((airyAi' 0 / airyAi 0) * kappaAiry * σ) := by
    have h0_ne : (airyAi 0 : ℂ) ≠ 0 := by
      exact_mod_cast (airyAi_pos_nonneg le_rfl).ne'
    have hidz := hid ((-kappaAiry * σ : ℝ) : ℂ)
    rw [airyAiC_ofReal] at hidz
    have h_solve : ∏' n : ℕ, (1 - ((-kappaAiry * σ : ℝ) : ℂ) / airyA n) *
        Complex.exp (((-kappaAiry * σ : ℝ) : ℂ) / airyA n) =
        ((airyAi (-kappaAiry * σ) : ℝ) : ℂ) / (airyAi 0 : ℂ) *
          Complex.exp (((airyAi' 0 / airyAi 0 * kappaAiry * σ : ℝ) : ℂ)) := by
      have hmul : (airyAi 0 : ℂ) * Complex.exp (((airyAi' 0 / airyAi 0 : ℝ) : ℂ) * ((-kappaAiry * σ : ℝ) : ℂ)) *
          ∏' n : ℕ, (1 - ((-kappaAiry * σ : ℝ) : ℂ) / airyA n) *
            Complex.exp (((-kappaAiry * σ : ℝ) : ℂ) / airyA n) =
          (airyAi 0 : ℂ) * Complex.exp (((airyAi' 0 / airyAi 0 : ℝ) : ℂ) * ((-kappaAiry * σ : ℝ) : ℂ)) *
            (((airyAi (-kappaAiry * σ) : ℝ) : ℂ) / (airyAi 0 : ℂ) *
              Complex.exp (((airyAi' 0 / airyAi 0 * kappaAiry * σ : ℝ) : ℂ))) := by
        rw [← hidz]
        have heq_exp : Complex.exp (((airyAi' 0 / airyAi 0 : ℝ) : ℂ) * ((-kappaAiry * σ : ℝ) : ℂ)) *
            Complex.exp (((airyAi' 0 / airyAi 0 * kappaAiry * σ : ℝ) : ℂ)) = 1 := by
          rw [← Complex.exp_add]
          convert Complex.exp_zero using 2
          push_cast; ring
        calc ((airyAi (-kappaAiry * σ) : ℝ) : ℂ)
            = ((airyAi (-kappaAiry * σ) : ℝ) : ℂ) * 1 := (mul_one _).symm
          _ = ((airyAi (-kappaAiry * σ) : ℝ) : ℂ) *
                (Complex.exp (((airyAi' 0 / airyAi 0 : ℝ) : ℂ) * ((-kappaAiry * σ : ℝ) : ℂ)) *
                Complex.exp (((airyAi' 0 / airyAi 0 * kappaAiry * σ : ℝ) : ℂ))) := by rw [heq_exp]
          _ = (airyAi 0 : ℂ) * Complex.exp (((airyAi' 0 / airyAi 0 : ℝ) : ℂ) * ((-kappaAiry * σ : ℝ) : ℂ)) *
                (((airyAi (-kappaAiry * σ) : ℝ) : ℂ) / (airyAi 0 : ℂ) *
                Complex.exp (((airyAi' 0 / airyAi 0 * kappaAiry * σ : ℝ) : ℂ))) := by
              field_simp [h0_ne]
      exact mul_left_cancel₀ (mul_ne_zero h0_ne (Complex.exp_ne_zero _)) hmul
    rw [h_solve, ← Complex.ofReal_exp, ← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.ofReal_re]
  rwa [hlim_eq] at ht_re

private lemma refApprox_identity (K : ℕ) (σ : ℝ) :
    let remK : ℝ := continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) -
      continuumFQ (continuumAK K) 0 - 6 * Real.sqrt (continuumAK K) * σ
    let cK : ℝ := 6 * Real.sqrt (continuumAK K) - ∑ k ∈ Finset.Icc 1 K, 2 / sNodeAiry k
    refApprox K σ = refApprox K 0 * Real.exp (remK + cK * σ) * hadamardPartialReal K σ ^ 2 := by
  intro remK cK
  unfold refApprox hadamardPartialReal
  rw [show max (-(0 : ℝ)) 0 = 0 by norm_num, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0),
    mul_zero, sub_zero]
  have hprod_id : (∏ k ∈ Finset.Icc 1 K, (0 - sNodeAiry k) ^ 2) *
      Real.exp (-(∑ k ∈ Finset.Icc 1 K, 2 * σ / sNodeAiry k)) *
      (∏ k ∈ Finset.Icc 1 K, (1 - σ / sNodeAiry k) * Real.exp (σ / sNodeAiry k)) ^ 2 =
      ∏ k ∈ Finset.Icc 1 K, (σ - sNodeAiry k) ^ 2 := by
    have hsq2 : (∏ k ∈ Finset.Icc 1 K, (1 - σ / sNodeAiry k) * Real.exp (σ / sNodeAiry k)) ^ 2 =
        (∏ k ∈ Finset.Icc 1 K, (1 - σ / sNodeAiry k) ^ 2) *
          ∏ k ∈ Finset.Icc 1 K, (Real.exp (σ / sNodeAiry k)) ^ 2 := by
      rw [← Finset.prod_pow]
      simp only [mul_pow, Finset.prod_mul_distrib]
    have he1 : ∏ k ∈ Finset.Icc 1 K, (Real.exp (σ / sNodeAiry k)) ^ 2 =
        Real.exp (∑ k ∈ Finset.Icc 1 K, 2 * σ / sNodeAiry k) := by
      have h_in : ∀ k ∈ Finset.Icc 1 K, (Real.exp (σ / sNodeAiry k)) ^ 2 =
          Real.exp (2 * σ / sNodeAiry k) := fun k _ => by
        rw [← Real.exp_nat_mul]; congr 1; ring
      rw [Finset.prod_congr rfl h_in, ← Real.exp_sum]
    have hprod_mul1 : (∏ k ∈ Finset.Icc 1 K, (0 - sNodeAiry k) ^ 2) *
        (∏ k ∈ Finset.Icc 1 K, (1 - σ / sNodeAiry k) ^ 2) =
        ∏ k ∈ Finset.Icc 1 K, (σ - sNodeAiry k) ^ 2 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      have hs := (sNodeAiry_pos k).ne'
      field_simp [hs]
      ring
    rw [hsq2, he1]
    calc (∏ k ∈ Finset.Icc 1 K, (0 - sNodeAiry k) ^ 2) *
          Real.exp (-(∑ k ∈ Finset.Icc 1 K, 2 * σ / sNodeAiry k)) *
          ((∏ k ∈ Finset.Icc 1 K, (1 - σ / sNodeAiry k) ^ 2) *
          Real.exp (∑ k ∈ Finset.Icc 1 K, 2 * σ / sNodeAiry k))
        = ((∏ k ∈ Finset.Icc 1 K, (0 - sNodeAiry k) ^ 2) *
            (∏ k ∈ Finset.Icc 1 K, (1 - σ / sNodeAiry k) ^ 2)) *
            (Real.exp (-(∑ k ∈ Finset.Icc 1 K, 2 * σ / sNodeAiry k)) *
            Real.exp (∑ k ∈ Finset.Icc 1 K, 2 * σ / sNodeAiry k)) := by ring
      _ = (∏ k ∈ Finset.Icc 1 K, (σ - sNodeAiry k) ^ 2) * 1 := by
          rw [hprod_mul1, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
      _ = ∏ k ∈ Finset.Icc 1 K, (σ - sNodeAiry k) ^ 2 := mul_one _
  have hexp_split : Real.exp (remK + cK * σ) =
      Real.exp (continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) -
        continuumFQ (continuumAK K) 0) * Real.exp (-(∑ k ∈ Finset.Icc 1 K, 2 * σ / sNodeAiry k)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [remK, cK]
    rw [sub_mul, Finset.sum_mul]
    have hs : (∑ k ∈ Finset.Icc 1 K, 2 / sNodeAiry k * σ) = ∑ k ∈ Finset.Icc 1 K, 2 * σ / sNodeAiry k := by
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [hs]; ring
  rw [hexp_split]
  have hexp_fq : Real.exp (continuumFQ (continuumAK K) 0) *
      Real.exp (continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) -
        continuumFQ (continuumAK K) 0) =
      Real.exp (continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ)) := by
    rw [← Real.exp_add]; congr 1; ring
  symm
  calc Real.exp (continuumFQ (continuumAK K) 0) * (∏ k ∈ Finset.Icc 1 K, (0 - sNodeAiry k) ^ 2) *
        (Real.exp (continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) -
          continuumFQ (continuumAK K) 0) * Real.exp (-(∑ k ∈ Finset.Icc 1 K, 2 * σ / sNodeAiry k))) *
        (∏ k ∈ Finset.Icc 1 K, (1 - σ / sNodeAiry k) * Real.exp (σ / sNodeAiry k)) ^ 2
      = (Real.exp (continuumFQ (continuumAK K) 0) *
          Real.exp (continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) -
            continuumFQ (continuumAK K) 0)) *
        ((∏ k ∈ Finset.Icc 1 K, (0 - sNodeAiry k) ^ 2) *
          Real.exp (-(∑ k ∈ Finset.Icc 1 K, 2 * σ / sNodeAiry k)) *
          (∏ k ∈ Finset.Icc 1 K, (1 - σ / sNodeAiry k) * Real.exp (σ / sNodeAiry k)) ^ 2) := by ring
    _ = Real.exp (continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ)) *
          ∏ k ∈ Finset.Icc 1 K, (σ - sNodeAiry k) ^ 2 := by rw [hexp_fq, hprod_id]

private lemma tendsto_continuumFQ_remK (σ : ℝ) :
    Tendsto (fun K : ℕ => continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) -
      continuumFQ (continuumAK K) 0 - 6 * Real.sqrt (continuumAK K) * σ) atTop (𝓝 0) := by
  have ht_inv : Tendsto (fun K : ℕ => (continuumAK K) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    have hK : Tendsto (fun K : ℕ => ((K : ℝ) + 1 / 4) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun K : ℕ => ((K : ℝ) + 1 / 4)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp h1
    refine hK.congr fun K => ?_
    unfold continuumAK
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (K : ℝ) + 1 / 4)]
    congr 1; norm_num
  have ht_32 : Tendsto (fun K : ℕ => (continuumAK K) ^ (-(3 / 2 : ℝ))) atTop (𝓝 0) := by
    have hK : Tendsto (fun K : ℕ => ((K : ℝ) + 1 / 4) ^ (-1 : ℝ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun K : ℕ => ((K : ℝ) + 1 / 4)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      exact (tendsto_rpow_neg_atTop zero_lt_one).comp h1
    refine hK.congr fun K => ?_
    unfold continuumAK
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (K : ℝ) + 1 / 4)]
    congr 1; norm_num
  have hAK_top : Tendsto continuumAK atTop atTop := by
    unfold continuumAK
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hbd_ev : ∀ᶠ K : ℕ in atTop,
      |continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) -
        continuumFQ (continuumAK K) 0 - 6 * Real.sqrt (continuumAK K) * σ| ≤
        3 * σ ^ 2 * (continuumAK K) ^ (-(1 / 2 : ℝ)) +
          4 * |σ| ^ 3 * (continuumAK K) ^ (-(3 / 2 : ℝ)) := by
    filter_upwards [hAK_top.eventually_ge_atTop (max (4 * |σ|) 1)] with K hK
    have h1 := continuumFQ_sub_lobe_asymptotic σ (continuumAK K) hK
    have h2 : |continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) -
        continuumFQ (continuumAK K) 0 - 6 * Real.sqrt (continuumAK K) * σ| ≤
        |(continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) -
          (continuumFQ (continuumAK K) 0 + 6 * Real.sqrt (continuumAK K) * σ -
            3 * σ ^ 2 * (continuumAK K) ^ (-(1 / 2 : ℝ))))| +
        |3 * σ ^ 2 * (continuumAK K) ^ (-(1 / 2 : ℝ))| := by
      have hid : continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) -
          continuumFQ (continuumAK K) 0 - 6 * Real.sqrt (continuumAK K) * σ =
          (continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) -
            (continuumFQ (continuumAK K) 0 + 6 * Real.sqrt (continuumAK K) * σ -
              3 * σ ^ 2 * (continuumAK K) ^ (-(1 / 2 : ℝ)))) -
            3 * σ ^ 2 * (continuumAK K) ^ (-(1 / 2 : ℝ)) := by ring
      rw [hid]
      exact (abs_sub _ _).trans (le_of_eq (by ring_nf))
    have h3_nn : 0 ≤ 3 * σ ^ 2 * (continuumAK K) ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg (continuumAK_nonneg K) _)
    rw [abs_of_nonneg h3_nn] at h2
    linarith [h1, h2]
  have hlim_rhs : Tendsto (fun K : ℕ => 3 * σ ^ 2 * (continuumAK K) ^ (-(1 / 2 : ℝ)) +
      4 * |σ| ^ 3 * (continuumAK K) ^ (-(3 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa using (ht_inv.const_mul (3 * σ ^ 2)).add (ht_32.const_mul (4 * |σ| ^ 3))
  have ht_abs : Tendsto (fun K : ℕ =>
      |continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) -
        continuumFQ (continuumAK K) 0 - 6 * Real.sqrt (continuumAK K) * σ|) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim_rhs
      (Eventually.of_forall fun _ => abs_nonneg _) hbd_ev
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp ht_abs ε hε
  refine ⟨N₀, fun K hK => by simpa [Real.dist_eq] using hN₀ K hK⟩

private lemma neg_log_refApproxLimit_bound :
    ∃ C₃ > 0, ∃ A₀ ≥ (1 : ℝ), ∀ a ≥ A₀,
      0 < refApproxLimit (-a) ∧
        |Real.log (refApproxLimit (-a)) + (1 / 2 : ℝ) * Real.log a + 2 * π * a ^ (3 / 2 : ℝ)| ≤ C₃ / a := by
  obtain ⟨Cδ, hCδ, hδ⟩ := deltaWKB_le_exists
  have hs_shift : ∀ k : ℕ, 1 ≤ k → |sNodeAiry k - phiQuantile k| ≤ (Cδ / kappaAiry) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
    intro k hk
    have hphi : phiQuantile k = phiWKB k := rfl
    rw [hphi, sNodeAiry_sub_phiWKB hk, neg_div, abs_neg, abs_div, abs_of_pos kappaAiry_pos]
    calc |deltaWKB k| / kappaAiry ≤ (Cδ * (k : ℝ) ^ (-(4 / 3 : ℝ))) / kappaAiry :=
          div_le_div_of_nonneg_right (hδ k hk) kappaAiry_pos.le
      _ = (Cδ / kappaAiry) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by ring
  obtain ⟨C₁, hC₁, hfq_bd⟩ := continuumFQ_AK_add_sum_phiQuantile_bound
  obtain ⟨C₂, hC₂, hsum_bd⟩ := sum_log_site_shift_neg_bound (div_pos hCδ kappaAiry_pos) hs_shift
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, max (2 * (Cδ / kappaAiry)) 1, le_max_right _ _, fun a ha => ?_⟩
  have ha1 : 1 ≤ a := (le_max_right _ _).trans ha
  have ha_pos : 0 < a := by linarith
  have hK_log : ∀ K : ℕ, 0 < refApprox K (-a) ∧
      |Real.log (refApprox K (-a)) + (1 / 2 : ℝ) * Real.log a + 2 * π * a ^ (3 / 2 : ℝ)| ≤ (C₁ + C₂) / a := by
    intro K
    have hprod_pos : 0 < ∏ k ∈ Finset.Icc 1 K, (-a - sNodeAiry k) ^ 2 :=
      Finset.prod_pos fun k _ => sq_pos_of_ne_zero (by linarith [sNodeAiry_pos k])
    have href_pos : 0 < refApprox K (-a) := mul_pos (Real.exp_pos _) hprod_pos
    refine ⟨href_pos, ?_⟩
    have hlog_eq : Real.log (refApprox K (-a)) =
        continuumFQ (continuumAK K) (-a) - 2 * π * a ^ (3 / 2 : ℝ) +
          ∑ k ∈ Finset.Icc 1 K, 2 * Real.log (a + sNodeAiry k) := by
      unfold refApprox
      rw [Real.log_mul (Real.exp_pos _).ne' hprod_pos.ne', Real.log_exp,
        show max (-(-a)) 0 = a by simp [ha_pos.le],
        Real.log_prod (fun k _ => (sq_pos_of_ne_zero (by linarith [sNodeAiry_pos k])).ne')]
      have hterm : ∑ k ∈ Finset.Icc 1 K, Real.log ((-a - sNodeAiry k) ^ 2) =
          ∑ k ∈ Finset.Icc 1 K, 2 * Real.log (a + sNodeAiry k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have hpos_as : 0 < a + sNodeAiry k := by linarith [sNodeAiry_pos k]
        rw [show (-a - sNodeAiry k) ^ 2 = (a + sNodeAiry k) ^ 2 by ring,
          Real.log_pow, Nat.cast_ofNat]
      rw [hterm]
    have h1 := hfq_bd a ha1 K
    have h2 := hsum_bd a ha K
    have hsplit : Real.log (refApprox K (-a)) + (1 / 2 : ℝ) * Real.log a + 2 * π * a ^ (3 / 2 : ℝ) =
        (continuumFQ (continuumAK K) (-a) + ∑ k ∈ Finset.Icc 1 K, 2 * Real.log (a + phiQuantile k) +
          (1 / 2 : ℝ) * Real.log a) +
        ∑ k ∈ Finset.Icc 1 K, (2 * Real.log (a + sNodeAiry k) - 2 * Real.log (a + phiQuantile k)) := by
      rw [hlog_eq, Finset.sum_sub_distrib]
      ring
    rw [hsplit]
    calc |(_ + _)| ≤ |continuumFQ (continuumAK K) (-a) +
            ∑ k ∈ Finset.Icc 1 K, 2 * Real.log (a + phiQuantile k) + (1 / 2 : ℝ) * Real.log a| +
          |∑ k ∈ Finset.Icc 1 K, (2 * Real.log (a + sNodeAiry k) - 2 * Real.log (a + phiQuantile k))| :=
          abs_add_le _ _
      _ ≤ C₁ / a + C₂ / a := add_le_add h1 h2
      _ = (C₁ + C₂) / a := by ring
  have href_lim := tendsto_refApprox (-a)
  set lb : ℝ := Real.exp (-((1 / 2 : ℝ) * Real.log a + 2 * π * a ^ (3 / 2 : ℝ) + (C₁ + C₂) / a))
  have hlb_pos : 0 < lb := Real.exp_pos _
  have hge_lb : ∀ K : ℕ, lb ≤ refApprox K (-a) := fun K => by
    have hlow := (abs_le.mp (hK_log K).2).1
    have hlog_ge : -((1 / 2 : ℝ) * Real.log a + 2 * π * a ^ (3 / 2 : ℝ) + (C₁ + C₂) / a) ≤
        Real.log (refApprox K (-a)) := by linarith
    simpa [lb, Real.exp_log (hK_log K).1] using Real.exp_le_exp.mpr hlog_ge
  have href_lim_ge : lb ≤ refApproxLimit (-a) :=
    ge_of_tendsto href_lim (Eventually.of_forall hge_lb)
  have href_lim_pos : 0 < refApproxLimit (-a) := lt_of_lt_of_le hlb_pos href_lim_ge
  refine ⟨href_lim_pos, ?_⟩
  have hlog_tend : Tendsto (fun K : ℕ =>
      |Real.log (refApprox K (-a)) + (1 / 2 : ℝ) * Real.log a + 2 * π * a ^ (3 / 2 : ℝ)|) atTop
      (𝓝 |Real.log (refApproxLimit (-a)) + (1 / 2 : ℝ) * Real.log a + 2 * π * a ^ (3 / 2 : ℝ)|) :=
    (((href_lim.log href_lim_pos.ne').add tendsto_const_nhds).add tendsto_const_nhds).abs
  exact le_of_tendsto hlog_tend (Eventually.of_forall fun K => (hK_log K).2)

/-- **Lemma ID, Step 2** (`ut:ID`):
`refApproxLimit σ = refApproxLimit 0 * (airyAi (-κ σ) / airyAi 0)^2 * exp (2 β κ σ)`
for some real constant `β`, with `0 < refApproxLimit 0`. -/
theorem refApproxLimit_eq_exp_mul_airyAi_sq :
    ∃ β : ℝ, 0 < refApproxLimit 0 ∧
      ∀ σ : ℝ, refApproxLimit σ =
        refApproxLimit 0 * (airyAi (-kappaAiry * σ) / airyAi 0) ^ 2 *
          Real.exp (2 * β * kappaAiry * σ) := by
  obtain ⟨_, _, A₀, hA₀, hneg_bd⟩ := neg_log_refApproxLimit_bound
  have ha0_pos : 0 < A₀ := by linarith
  have ha1_pos : 0 < A₀ + 1 := by linarith
  obtain ⟨href_a0_pos, _⟩ := hneg_bd A₀ le_rfl
  obtain ⟨href_a1_pos, _⟩ := hneg_bd (A₀ + 1) (by linarith)
  have hP_pos_of_nonneg : ∀ a : ℝ, 0 ≤ a →
      0 < (airyAi (-kappaAiry * (-a)) / airyAi 0) *
        Real.exp ((airyAi' 0 / airyAi 0) * kappaAiry * (-a)) := fun a ha => by
    rw [mul_neg (airyAi' 0 / airyAi 0 * kappaAiry) a, show -kappaAiry * -a = kappaAiry * a by ring]
    exact mul_pos (div_pos (airyAi_pos_nonneg (mul_nonneg kappaAiry_pos.le ha))
      (airyAi_pos_nonneg le_rfl)) (Real.exp_pos _)
  let remK : ℕ → ℝ → ℝ := fun K σ =>
    continuumFQ (continuumAK K) σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) -
      continuumFQ (continuumAK K) 0 - 6 * Real.sqrt (continuumAK K) * σ
  let cK : ℕ → ℝ := fun K =>
    6 * Real.sqrt (continuumAK K) - ∑ k ∈ Finset.Icc 1 K, 2 / sNodeAiry k
  -- Show `cK` converges using the ratio `refApprox K (-(A₀ + 1)) / refApprox K (-A₀)`:
  have hP0_pos := hP_pos_of_nonneg A₀ ha0_pos.le
  have hP1_pos := hP_pos_of_nonneg (A₀ + 1) ha1_pos.le
  have href_K_pos : ∀ K : ℕ, 0 < refApprox K 0 := fun K =>
    mul_pos (Real.exp_pos _) (Finset.prod_pos fun k _ => sq_pos_of_ne_zero (by linarith [sNodeAiry_pos k]))
  have hP_neg_ne : ∀ (K : ℕ) (a : ℝ), 0 < a → hadamardPartialReal K (-a) ≠ 0 := by
    intro K a ha
    unfold hadamardPartialReal
    refine Finset.prod_ne_zero_iff.mpr fun k _ => mul_ne_zero ?_ (Real.exp_ne_zero _)
    have hpos : 0 < 1 - (-a) / sNodeAiry k := by
      rw [neg_div, sub_neg_eq_add]
      linarith [div_pos ha (sNodeAiry_pos k)]
    exact hpos.ne'
  have hratio_exp : ∀ K : ℕ,
      Real.exp (cK K) =
        (refApprox K (-A₀) / refApprox K (-(A₀ + 1))) *
          Real.exp (remK K (-(A₀ + 1)) - remK K (-A₀)) *
          (hadamardPartialReal K (-(A₀ + 1)) / hadamardPartialReal K (-A₀)) ^ 2 := by
    intro K
    have hid0 := refApprox_identity K (-A₀)
    have hid1 := refApprox_identity K (-(A₀ + 1))
    dsimp [remK, cK] at hid0 hid1 ⊢
    have hP_a0_ne : hadamardPartialReal K (-A₀) ≠ 0 := hP_neg_ne K A₀ ha0_pos
    have hP_a1_ne : hadamardPartialReal K (-(A₀ + 1)) ≠ 0 := hP_neg_ne K (A₀ + 1) ha1_pos
    have href_0_ne : (refApprox K 0) ≠ 0 := (href_K_pos K).ne'
    rw [hid0, hid1]
    field_simp [href_0_ne, hP_a0_ne, hP_a1_ne, Real.exp_ne_zero]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hP0_tend := tendsto_hadamardPartialReal (-A₀)
  have hP1_tend := tendsto_hadamardPartialReal (-(A₀ + 1))
  set L_P0 := (airyAi (-kappaAiry * -A₀) / airyAi 0) * Real.exp ((airyAi' 0 / airyAi 0) * kappaAiry * -A₀)
  set L_P1 := (airyAi (-kappaAiry * -(A₀ + 1)) / airyAi 0) * Real.exp ((airyAi' 0 / airyAi 0) * kappaAiry * -(A₀ + 1))
  set L_exp_c := (refApproxLimit (-A₀) / refApproxLimit (-(A₀ + 1))) * Real.exp (0 - 0) * (L_P1 / L_P0) ^ 2
  have hL_exp_c_pos : 0 < L_exp_c :=
    mul_pos (mul_pos (div_pos href_a0_pos href_a1_pos) (Real.exp_pos _))
      (sq_pos_of_ne_zero (div_pos hP1_pos hP0_pos).ne')
  have ht_exp_c : Tendsto (fun K : ℕ => Real.exp (cK K)) atTop (𝓝 L_exp_c) := by
    have ht_rhs := (((tendsto_refApprox (-A₀)).div (tendsto_refApprox (-(A₀ + 1))) href_a1_pos.ne').mul
      (Real.continuous_exp.continuousAt.tendsto.comp ((tendsto_continuumFQ_remK (-(A₀ + 1))).sub (tendsto_continuumFQ_remK (-A₀))))).mul
      ((hP1_tend.div hP0_tend hP0_pos.ne').pow 2)
    exact ht_rhs.congr (fun K => (hratio_exp K).symm)
  have ht_cK : Tendsto cK atTop (𝓝 (Real.log L_exp_c)) := by
    have hlog := ht_exp_c.log hL_exp_c_pos.ne'
    simpa [Real.log_exp] using hlog
  set c_lim := Real.log L_exp_c
  -- Now deduce `0 < refApproxLimit 0`:
  have h0_from_a0 : ∀ K : ℕ,
      refApprox K 0 = refApprox K (-A₀) / (Real.exp (remK K (-A₀) + cK K * (-A₀)) * hadamardPartialReal K (-A₀) ^ 2) := by
    intro K
    have hid := refApprox_identity K (-A₀)
    have hP_ne : hadamardPartialReal K (-A₀) ≠ 0 := hP_neg_ne K A₀ ha0_pos
    have hden_ne : Real.exp (remK K (-A₀) + cK K * (-A₀)) * hadamardPartialReal K (-A₀) ^ 2 ≠ 0 :=
      mul_ne_zero (Real.exp_ne_zero _) (pow_ne_zero 2 hP_ne)
    exact (eq_div_iff hden_ne).mpr (by dsimp [remK, cK] at hid ⊢; linarith)
  have ht_0_pos_lim : Tendsto (fun K : ℕ => refApprox K 0) atTop
      (𝓝 (refApproxLimit (-A₀) / (Real.exp (0 + c_lim * (-A₀)) * L_P0 ^ 2))) := by
    have ht_den := (Real.continuous_exp.continuousAt.tendsto.comp ((tendsto_continuumFQ_remK (-A₀)).add (ht_cK.mul_const (-A₀)))).mul
      (hP0_tend.pow 2)
    have hden_pos : 0 < Real.exp (0 + c_lim * (-A₀)) * L_P0 ^ 2 :=
      mul_pos (Real.exp_pos _) (sq_pos_of_ne_zero hP0_pos.ne')
    exact ((tendsto_refApprox (-A₀)).div ht_den hden_pos.ne').congr (fun K => (h0_from_a0 K).symm)
  have href0_eq : refApproxLimit 0 = refApproxLimit (-A₀) / (Real.exp (0 + c_lim * (-A₀)) * L_P0 ^ 2) :=
    tendsto_nhds_unique (tendsto_refApprox 0) ht_0_pos_lim
  have href0_pos : 0 < refApproxLimit 0 := by
    rw [href0_eq]
    exact div_pos href_a0_pos (mul_pos (Real.exp_pos _) (sq_pos_of_ne_zero hP0_pos.ne'))
  -- Verify for all `σ`:
  have h_all : ∀ σ : ℝ, refApproxLimit σ =
      refApproxLimit 0 * (airyAi (-kappaAiry * σ) / airyAi 0) ^ 2 *
        Real.exp (2 * ((c_lim + 2 * (airyAi' 0 / airyAi 0) * kappaAiry) / (2 * kappaAiry)) * kappaAiry * σ) := by
    intro σ
    have ht_prod : Tendsto (fun K : ℕ => refApprox K σ) atTop
        (𝓝 (refApproxLimit 0 * Real.exp (0 + c_lim * σ) *
          ((airyAi (-kappaAiry * σ) / airyAi 0) *
            Real.exp ((airyAi' 0 / airyAi 0) * kappaAiry * σ)) ^ 2)) := by
      have ht1 := tendsto_refApprox 0
      have ht2 := Real.continuous_exp.continuousAt.tendsto.comp ((tendsto_continuumFQ_remK σ).add (ht_cK.mul_const σ))
      have ht3 := (tendsto_hadamardPartialReal σ).pow 2
      exact ((ht1.mul ht2).mul ht3).congr (fun K => (refApprox_identity K σ).symm)
    have hlim_σ := tendsto_nhds_unique (tendsto_refApprox σ) ht_prod
    rw [hlim_σ]
    have hκ_ne : kappaAiry ≠ 0 := kappaAiry_pos.ne'
    have hexp_comb : Real.exp (0 + c_lim * σ) * (Real.exp ((airyAi' 0 / airyAi 0) * kappaAiry * σ)) ^ 2 =
        Real.exp (2 * ((c_lim + 2 * (airyAi' 0 / airyAi 0) * kappaAiry) / (2 * kappaAiry)) * kappaAiry * σ) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      field_simp [hκ_ne]
      ring
    calc refApproxLimit 0 * Real.exp (0 + c_lim * σ) *
          ((airyAi (-kappaAiry * σ) / airyAi 0) * Real.exp ((airyAi' 0 / airyAi 0) * kappaAiry * σ)) ^ 2
        = refApproxLimit 0 * (airyAi (-kappaAiry * σ) / airyAi 0) ^ 2 *
            (Real.exp (0 + c_lim * σ) * (Real.exp ((airyAi' 0 / airyAi 0) * kappaAiry * σ)) ^ 2) := by ring
      _ = refApproxLimit 0 * (airyAi (-kappaAiry * σ) / airyAi 0) ^ 2 *
            Real.exp (2 * ((c_lim + 2 * (airyAi' 0 / airyAi 0) * kappaAiry) / (2 * kappaAiry)) * kappaAiry * σ) := by
          rw [hexp_comb]
  exact ⟨(c_lim + 2 * (airyAi' 0 / airyAi 0) * kappaAiry) / (2 * kappaAiry), href0_pos, h_all⟩

/-! ### Section 3: Step 3 via Positive-Axis Airy Asymptotics (`AiryAsymPos`) -/

/-- **Lemma ID, Step 3** (`ut:ID`): `refApproxLimit σ = C_* Ai(-κ σ)^2` for all `σ : ℝ`. -/
theorem refApproxLimit_eq_cStar_mul_airyAi_sq (σ : ℝ) :
    refApproxLimit σ = CStar * airyAi (-kappaAiry * σ) ^ 2 := by
  obtain ⟨β, href0_pos, href_formula⟩ := refApproxLimit_eq_exp_mul_airyAi_sq
  obtain ⟨C₃, hC₃, A₀, hA₀, hneg_bd⟩ := neg_log_refApproxLimit_bound
  set c₀ : ℝ := refApproxLimit 0 / airyAi 0 ^ 2
  have hai0_pos : 0 < airyAi 0 := airyAi_pos_nonneg le_rfl
  have hc₀_pos : 0 < c₀ := div_pos href0_pos (sq_pos_of_ne_zero hai0_pos.ne')
  have hcStar_pos : 0 < CStar := CStar_pos
  have hκ_pos : 0 < kappaAiry := kappaAiry_pos
  -- Large-`a` log comparison combining Step 3 continuum bound with `airyAi_sub_leading_le`:
  have h_asym_diff : ∃ C_asym > 0, ∀ a ≥ max A₀ (1 / kappaAiry),
      |Real.log (c₀ / CStar) - 2 * β * kappaAiry * a| ≤ C_asym / a := by
    set C_asym : ℝ := C₃ + 4 * (5 / 48) / kappaAiry ^ (3 / 2 : ℝ)
    refine ⟨C_asym, by positivity, fun a ha => ?_⟩
    have haA₀ : A₀ ≤ a := (le_max_left _ _).trans ha
    have ha1 : 1 ≤ a := hA₀.trans haA₀
    have ha_inv_κ : 1 / kappaAiry ≤ a := (le_max_right _ _).trans ha
    have ha_pos : 0 < a := by linarith
    have hx_ge1 : 1 ≤ kappaAiry * a := by
      have h1 : kappaAiry * (1 / kappaAiry) ≤ kappaAiry * a :=
        mul_le_mul_of_nonneg_left ha_inv_κ hκ_pos.le
      rwa [mul_one_div_cancel hκ_pos.ne'] at h1
    set x : ℝ := kappaAiry * a
    have hx_pos : 0 < x := by positivity
    set P : ℝ := 1 / (2 * Real.sqrt π) * x ^ (-(1 / 4) : ℝ) * Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ))
    have hP_pos : 0 < P := by dsimp [P]; positivity
    have hAi_asym := airyAi_sub_leading_le hx_pos
    change |airyAi x - P| ≤ 5 / 48 / x ^ (3 / 2 : ℝ) * P at hAi_asym
    set θ : ℝ := airyAi x / P - 1
    have hθ_bd : |θ| ≤ 5 / 48 / x ^ (3 / 2 : ℝ) := by
      rw [show θ = (airyAi x - P) / P by dsimp [θ]; field_simp [hP_pos.ne'],
        abs_div, abs_of_pos hP_pos]
      exact (div_le_iff₀ hP_pos).mpr hAi_asym
    have hx32_ge1 : 1 ≤ x ^ (3 / 2 : ℝ) := Real.one_le_rpow hx_ge1 (by norm_num)
    have hθ_half : |θ| ≤ 1 / 2 := by
      calc |θ| ≤ 5 / 48 / x ^ (3 / 2 : ℝ) := hθ_bd
        _ ≤ 5 / 48 / 1 := by gcongr
        _ ≤ 1 / 2 := by norm_num
    have hAi_eq : airyAi x = P * (1 + θ) := by
      dsimp [θ]; field_simp [hP_pos.ne']; ring
    have h1θ_pos : 0 < 1 + θ := by linarith [(abs_le.mp hθ_half).1]
    -- Compute `P^2`:
    have hP_sq : P ^ 2 = CStar⁻¹ * a ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * a ^ (3 / 2 : ℝ)) := by
      have hsqrt_k : Real.sqrt kappaAiry * Real.sqrt kappaAiry = kappaAiry := Real.mul_self_sqrt hκ_pos.le
      have hsqrt_π : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt Real.pi_pos.le
      have hC_inv : (1 / (2 * Real.sqrt π)) ^ 2 * kappaAiry ^ (-(1 / 2 : ℝ)) = CStar⁻¹ := by
        unfold CStar
        rw [Real.rpow_neg hκ_pos.le, ← Real.sqrt_eq_rpow]
        rw [show (1 / (2 * Real.sqrt π)) ^ 2 = 1 / (4 * (Real.sqrt π * Real.sqrt π)) by ring, hsqrt_π]
        rw [div_eq_mul_inv, one_mul]
        rw [← mul_inv]
      have hx_pow_sq : (x ^ (-(1 / 4) : ℝ)) ^ 2 = kappaAiry ^ (-(1 / 2 : ℝ)) * a ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le]
        rw [show (-(1 / 4) : ℝ) * (2 : ℕ) = -(1 / 2 : ℝ) by norm_num]
        dsimp [x]
        exact Real.mul_rpow hκ_pos.le ha_pos.le
      have hx_exp_sq : (Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ))) ^ 2 =
          Real.exp (-2 * π * a ^ (3 / 2 : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        dsimp [x]
        rw [Real.mul_rpow hκ_pos.le ha_pos.le]
        have h43 := four_thirds_kappaAiry_rpow
        calc ((2 : ℕ) : ℝ) * (-(2 / 3) * (kappaAiry ^ (3 / 2 : ℝ) * a ^ (3 / 2 : ℝ)))
            = -((4 / 3 : ℝ) * kappaAiry ^ (3 / 2 : ℝ)) * a ^ (3 / 2 : ℝ) := by ring
          _ = -(2 * π) * a ^ (3 / 2 : ℝ) := by rw [h43]
          _ = -2 * π * a ^ (3 / 2 : ℝ) := by ring
      calc P ^ 2 = (1 / (2 * Real.sqrt π)) ^ 2 * (x ^ (-(1 / 4) : ℝ)) ^ 2 *
            (Real.exp (-(2 / 3) * x ^ (3 / 2 : ℝ))) ^ 2 := by dsimp [P]; ring
        _ = ((1 / (2 * Real.sqrt π)) ^ 2 * kappaAiry ^ (-(1 / 2 : ℝ))) *
              a ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * a ^ (3 / 2 : ℝ)) := by
            rw [hx_pow_sq, hx_exp_sq]; ring
        _ = CStar⁻¹ * a ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * a ^ (3 / 2 : ℝ)) := by rw [hC_inv]
    have href_formula_a : refApproxLimit (-a) =
        (c₀ / CStar) * a ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * a ^ (3 / 2 : ℝ)) *
          Real.exp (-2 * β * kappaAiry * a) * (1 + θ) ^ 2 := by
      have hf := href_formula (-a)
      rw [show -kappaAiry * -a = x by dsimp [x]; ring, hAi_eq] at hf
      calc refApproxLimit (-a)
          = (refApproxLimit 0 / airyAi 0 ^ 2) * (P * (1 + θ)) ^ 2 * Real.exp (2 * β * kappaAiry * -a) := by
              rw [hf, div_pow]; ring
        _ = c₀ * P ^ 2 * Real.exp (-2 * β * kappaAiry * a) * (1 + θ) ^ 2 := by
              rw [show 2 * β * kappaAiry * -a = -2 * β * kappaAiry * a by ring]
              dsimp [c₀]; ring
        _ = (c₀ * CStar⁻¹) * a ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * a ^ (3 / 2 : ℝ)) *
              Real.exp (-2 * β * kappaAiry * a) * (1 + θ) ^ 2 := by rw [hP_sq]; ring_nf
        _ = (c₀ / CStar) * a ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * a ^ (3 / 2 : ℝ)) *
              Real.exp (-2 * β * kappaAiry * a) * (1 + θ) ^ 2 := by rw [← div_eq_mul_inv]
    have hlog_a : Real.log (refApproxLimit (-a)) + (1 / 2 : ℝ) * Real.log a + 2 * π * a ^ (3 / 2 : ℝ) =
        Real.log (c₀ / CStar) - 2 * β * kappaAiry * a + 2 * Real.log (1 + θ) := by
      rw [href_formula_a]
      have hpos1 : (0 : ℝ) < c₀ / CStar := div_pos hc₀_pos hcStar_pos
      have hpos2 : (0 : ℝ) < a ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos ha_pos _
      have hpos3 : (0 : ℝ) < Real.exp (-2 * π * a ^ (3 / 2 : ℝ)) := Real.exp_pos _
      have hpos4 : (0 : ℝ) < Real.exp (-2 * β * kappaAiry * a) := Real.exp_pos _
      have hpos5 : (0 : ℝ) < (1 + θ) ^ 2 := sq_pos_of_pos h1θ_pos
      rw [Real.log_mul (mul_pos (mul_pos (mul_pos hpos1 hpos2) hpos3) hpos4).ne' hpos5.ne',
        Real.log_mul (mul_pos (mul_pos hpos1 hpos2) hpos3).ne' hpos4.ne',
        Real.log_mul (mul_pos hpos1 hpos2).ne' hpos3.ne',
        Real.log_mul hpos1.ne' hpos2.ne',
        Real.log_rpow ha_pos, Real.log_exp, Real.log_exp, Real.log_pow, Nat.cast_ofNat]
      ring
    have hneg_a := (hneg_bd a haA₀).2
    rw [hlog_a] at hneg_a
    have hlog_θ : |2 * Real.log (1 + θ)| ≤ (4 * (5 / 48) / kappaAiry ^ (3 / 2 : ℝ)) / a := by
      have h2θ := abs_log_one_add_le_two_mul hθ_half
      have ha_le_32 : a ≤ a ^ (3 / 2 : ℝ) := by
        simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le ha1 (by norm_num : (1 : ℝ) ≤ 3 / 2)
      calc |2 * Real.log (1 + θ)| = 2 * |Real.log (1 + θ)| := by rw [abs_mul, abs_of_pos (by norm_num)]
        _ ≤ 2 * (2 * |θ|) := mul_le_mul_of_nonneg_left h2θ (by norm_num)
        _ ≤ 4 * (5 / 48 / x ^ (3 / 2 : ℝ)) := by linarith [hθ_bd]
        _ = 4 * (5 / 48) / (kappaAiry ^ (3 / 2 : ℝ) * a ^ (3 / 2 : ℝ)) := by
            dsimp [x]; rw [Real.mul_rpow hκ_pos.le ha_pos.le]; ring
        _ ≤ 4 * (5 / 48) / (kappaAiry ^ (3 / 2 : ℝ) * a) := by gcongr
        _ = (4 * (5 / 48) / kappaAiry ^ (3 / 2 : ℝ)) / a := by ring
    calc |Real.log (c₀ / CStar) - 2 * β * kappaAiry * a|
        = |(Real.log (c₀ / CStar) - 2 * β * kappaAiry * a + 2 * Real.log (1 + θ)) - 2 * Real.log (1 + θ)| := by
            congr 1; ring
      _ ≤ |Real.log (c₀ / CStar) - 2 * β * kappaAiry * a + 2 * Real.log (1 + θ)| + |2 * Real.log (1 + θ)| :=
            abs_sub _ _
      _ ≤ C₃ / a + (4 * (5 / 48) / kappaAiry ^ (3 / 2 : ℝ)) / a := add_le_add hneg_a hlog_θ
      _ = C_asym / a := by dsimp [C_asym]; ring
  obtain ⟨C_asym, hCa_pos, hCa_bd⟩ := h_asym_diff
  -- Deduce `β = 0`:
  have hβ : β = 0 := by
    have hdiv_bd : ∀ a ≥ max A₀ (max (1 / kappaAiry) 1),
        |Real.log (c₀ / CStar) / a - 2 * β * kappaAiry| ≤ C_asym / a ^ 2 := by
      intro a ha
      have ha_ge : max A₀ (1 / kappaAiry) ≤ a := max_le ((le_max_left _ _).trans ha)
        ((le_max_left _ _).trans ((le_max_right _ _).trans ha))
      have ha_pos : 0 < a := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans ((le_max_right _ _).trans ha))
      have h1 := hCa_bd a ha_ge
      rw [show Real.log (c₀ / CStar) / a - 2 * β * kappaAiry =
          (Real.log (c₀ / CStar) - 2 * β * kappaAiry * a) / a by field_simp [ha_pos.ne'],
        abs_div, abs_of_pos ha_pos]
      calc |Real.log (c₀ / CStar) - 2 * β * kappaAiry * a| / a ≤ (C_asym / a) / a :=
            div_le_div_of_nonneg_right h1 ha_pos.le
        _ = C_asym / a ^ 2 := by ring
    have ht_lhs : Tendsto (fun n : ℕ => |Real.log (c₀ / CStar) / (n : ℝ) - 2 * β * kappaAiry|)
        atTop (𝓝 |0 - 2 * β * kappaAiry|) :=
      (((tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).sub tendsto_const_nhds)).abs
    have ht_rhs : Tendsto (fun n : ℕ => C_asym / (n : ℝ) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop)
    have hle_ev : ∀ᶠ n : ℕ in atTop,
        |Real.log (c₀ / CStar) / (n : ℝ) - 2 * β * kappaAiry| ≤ C_asym / (n : ℝ) ^ 2 := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (max A₀ (max (1 / kappaAiry) 1))] with n hn
      exact hdiv_bd n hn
    have hzero : |0 - 2 * β * kappaAiry| ≤ 0 := le_of_tendsto_of_tendsto ht_lhs ht_rhs hle_ev
    have hmul0 : 2 * β * kappaAiry = 0 := by linarith [abs_nonneg (0 - 2 * β * kappaAiry), abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))]
    rcases mul_eq_zero.mp hmul0 with h2β | hκ0
    · linarith
    · exact absurd hκ0 hκ_pos.ne'
  -- Deduce `c₀ = CStar`:
  have hc₀_eq : c₀ = CStar := by
    have hlog_bd : ∀ᶠ n : ℕ in atTop, |Real.log (c₀ / CStar)| ≤ C_asym / (n : ℝ) := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (max A₀ (1 / kappaAiry))] with n hn
      have h1 := hCa_bd n hn
      simpa [hβ] using h1
    have ht_rhs : Tendsto (fun n : ℕ => C_asym / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hzero : |Real.log (c₀ / CStar)| ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds ht_rhs hlog_bd
    have hlog0 : Real.log (c₀ / CStar) = 0 := abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))
    have hdiv1 : c₀ / CStar = 1 := by
      have hpos_div : 0 < c₀ / CStar := div_pos hc₀_pos hcStar_pos
      rcases Real.log_eq_zero.mp hlog0 with h0 | h1 | hn1
      · linarith
      · exact h1
      · linarith
    exact (div_eq_one_iff_eq hcStar_pos.ne').mp hdiv1
  -- Conclude for all `σ`:
  rw [href_formula σ, hβ]
  simp only [mul_zero, zero_mul, Real.exp_zero, mul_one]
  have href0_eq : refApproxLimit 0 = CStar * airyAi 0 ^ 2 := by
    dsimp [c₀] at hc₀_eq
    field_simp [hai0_pos.ne'] at hc₀_eq ⊢
    linarith [hc₀_eq]
  rw [href0_eq]
  have hai0_ne : airyAi 0 ≠ 0 := hai0_pos.ne'
  field_simp [hai0_ne]

/-! ### Section 4: Step 4 — General `W̃^{±(f)}(σ) = C_*^{(f)} κ W^{(f)}(-κ σ)` and Design Case -/

lemma airyProdTailHypothesis_of_tail {f N : ℕ} (_hN : f ≤ N) {C_t : ℝ} (_hCt : 0 < C_t)
    {σSeq εHat : ℕ → ℝ}
    (htail : ∀ k : ℕ, N < k →
      |σSeq k - phiWKB k| ≤ C_t * (k : ℝ) ^ (-(4 / 3 : ℝ)) ∧
        |εHat k| ≤ C_t * (k : ℝ) ^ (-(1 / 3 : ℝ))) :
    AiryProdTailHypothesis f (fun k => -kappaAiry * σSeq k) (fun k => kappaAiry * εHat k) := by
  have hκ := kappaAiry_pos
  set B_fin : ℝ := (Finset.Icc (f + 1) N).sum fun k =>
    (kappaAiry * |σSeq k - phiWKB k|) * (k : ℝ) ^ (4 / 3 : ℝ) +
      (kappaAiry * |εHat k|) * (k : ℝ) ^ (1 / 3 : ℝ)
  refine ⟨kappaAiry * C_t + B_fin + 1, by positivity, fun k hk => ?_⟩
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  by_cases hkN : k ≤ N
  · have hmem : k ∈ Finset.Icc (f + 1) N := Finset.mem_Icc.mpr ⟨by omega, hkN⟩
    have hterm_le : (kappaAiry * |σSeq k - phiWKB k|) * (k : ℝ) ^ (4 / 3 : ℝ) +
        (kappaAiry * |εHat k|) * (k : ℝ) ^ (1 / 3 : ℝ) ≤ B_fin :=
      Finset.single_le_sum (f := fun j => (kappaAiry * |σSeq j - phiWKB j|) * (j : ℝ) ^ (4 / 3 : ℝ) +
        (kappaAiry * |εHat j|) * (j : ℝ) ^ (1 / 3 : ℝ)) (fun _ _ => by positivity) hmem
    have hk43 : (k : ℝ) ^ (-(4 / 3 : ℝ)) = ((k : ℝ) ^ (4 / 3 : ℝ))⁻¹ := Real.rpow_neg hk_pos.le _
    have hk13 : (k : ℝ) ^ (-(1 / 3 : ℝ)) = ((k : ℝ) ^ (1 / 3 : ℝ))⁻¹ := Real.rpow_neg hk_pos.le _
    constructor
    · rw [show -kappaAiry * σSeq k - uWKB k = -kappaAiry * (σSeq k - phiWKB k) by unfold uWKB; ring,
        abs_mul, abs_neg, abs_of_pos hκ, hk43, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      have h1 : kappaAiry * |σSeq k - phiWKB k| * (k : ℝ) ^ (4 / 3 : ℝ) ≤ B_fin := by
        linarith [hterm_le, (by positivity : 0 ≤ (kappaAiry * |εHat k|) * (k : ℝ) ^ (1 / 3 : ℝ))]
      linarith [h1, (by positivity : 0 ≤ kappaAiry * C_t)]
    · rw [abs_mul, abs_of_pos hκ, hk13, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      have h1 : kappaAiry * |εHat k| * (k : ℝ) ^ (1 / 3 : ℝ) ≤ B_fin := by
        linarith [hterm_le, (by positivity : 0 ≤ (kappaAiry * |σSeq k - phiWKB k|) * (k : ℝ) ^ (4 / 3 : ℝ))]
      linarith [h1, (by positivity : 0 ≤ kappaAiry * C_t)]
  · have hNk : N < k := by omega
    obtain ⟨hs, he⟩ := htail k hNk
    constructor
    · rw [show -kappaAiry * σSeq k - uWKB k = -kappaAiry * (σSeq k - phiWKB k) by unfold uWKB; ring,
        abs_mul, abs_neg, abs_of_pos hκ]
      calc kappaAiry * |σSeq k - phiWKB k| ≤ kappaAiry * (C_t * (k : ℝ) ^ (-(4 / 3 : ℝ))) :=
            mul_le_mul_of_nonneg_left hs hκ.le
        _ = (kappaAiry * C_t) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by ring
        _ ≤ (kappaAiry * C_t + B_fin + 1) * (k : ℝ) ^ (-(4 / 3 : ℝ)) :=
            mul_le_mul_of_nonneg_right (by linarith [(by positivity : 0 ≤ B_fin)]) (by positivity)
    · rw [abs_mul, abs_of_pos hκ]
      calc kappaAiry * |εHat k| ≤ kappaAiry * (C_t * (k : ℝ) ^ (-(1 / 3 : ℝ))) :=
            mul_le_mul_of_nonneg_left he hκ.le
        _ = (kappaAiry * C_t) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by ring
        _ ≤ (kappaAiry * C_t + B_fin + 1) * (k : ℝ) ^ (-(1 / 3 : ℝ)) :=
            mul_le_mul_of_nonneg_right (by linarith [(by positivity : 0 ≤ B_fin)]) (by positivity)

/-- **Lemma ID (`ut:ID`), general level `f`**:
`W̃^{±(f)}(σ) = C_*^{(f)} κ Re(W^{(f)}(-κ σ))` for every `σ : ℝ`, under the `ut:P(b)`
reference-tail bounds of Lemma W. -/
theorem lemma_ID (f N : ℕ) (hf : 1 ≤ f) (hN : f ≤ N)
    {M C_t : ℝ} (hM : 0 < M) (hC_t : 0 < C_t)
    {σf : ℝ} {σSeq εHat : ℕ → ℝ}
    (hσf : |σf| ≤ M)
    (hmod : ∀ k ∈ Finset.Icc (f + 1) N, |σSeq k| ≤ M ∧ |εHat k| ≤ M)
    (htail : ∀ k : ℕ, N < k →
      |σSeq k - phiWKB k| ≤ C_t * (k : ℝ) ^ (-(4 / 3 : ℝ)) ∧
        |εHat k| ≤ C_t * (k : ℝ) ^ (-(1 / 3 : ℝ))) (σ : ℝ) :
    tildeW f σf σSeq εHat σ =
      CStarF f * kappaAiry *
        (airyWindowProd f (-kappaAiry * σf) (fun k => -kappaAiry * σSeq k)
          (fun k => kappaAiry * εHat k) ((-kappaAiry * σ : ℝ) : ℂ)).re := by
  let uSite : ℕ → ℝ := fun k => -kappaAiry * σSeq k
  let epsU : ℕ → ℝ := fun k => kappaAiry * εHat k
  let uF : ℝ := -kappaAiry * σf
  have hH : AiryProdTailHypothesis f uSite epsU := airyProdTailHypothesis_of_tail hN hC_t htail
  have hκ := kappaAiry_pos
  have hκ_ne : kappaAiry ≠ 0 := hκ.ne'
  -- Step 4a: prove equality off `{sNodeAiry k | k ≥ 1}`:
  have h_off : ∀ σ' : ℝ, (∀ k : ℕ, 1 ≤ k → σ' ≠ sNodeAiry k) →
      tildeW f σf σSeq εHat σ' =
        CStarF f * kappaAiry * (airyWindowProd f uF uSite epsU ((-kappaAiry * σ' : ℝ) : ℂ)).re := by
    intro σ' hσ'_ne
    have hu_ne : ∀ k : ℕ, 1 ≤ k → ((-kappaAiry * σ' : ℝ) : ℂ) ≠ (airyZero k : ℂ) := by
      intro k hk heq
      have hreq := Complex.ofReal_injective heq
      have hzero_eq : airyZero k = -kappaAiry * sNodeAiry k := by
        unfold sNodeAiry; rw [abs_of_neg (airyZero_neg k)]; field_simp [hκ_ne]
      rw [hzero_eq] at hreq
      exact hσ'_ne k hk (mul_left_cancel₀ (neg_ne_zero.mpr hκ_ne) hreq)
    have hprod_f_ne : ∏ k ∈ Finset.Icc 1 f, (σ' - sNodeAiry k) ^ 2 ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k hk =>
        pow_ne_zero 2 (sub_ne_zero.mpr (hσ'_ne k (Finset.mem_Icc.mp hk).1))
    -- Convergence of `windowFiniteProd f σf σSeq εHat K σ'`:
    have hconv_W : Tendsto (fun K : ℕ => windowFiniteProd f σf σSeq εHat K σ') atTop
        (𝓝 (tildeW f σf σSeq εHat σ')) :=
      tendsto_tildeW_of_bounds f N hf hN hM hC_t hσf hmod htail σ'
    -- Tail ratio convergence from `hasProd_airyProdTail`:
    have hp_tail := hasProd_airyProdTail hH (fun k _ => hu_ne k (by omega))
    have hrange_shift : Tendsto (fun K : ℕ => Finset.range (K - f)) atTop (atTop : Filter (Finset ℕ)) := by
      rw [Filter.tendsto_atTop]
      intro s₀
      refine eventually_atTop.mpr ⟨s₀.sup (· + 1) + f, fun K hK x hx => Finset.mem_range.mpr ?_⟩
      have hx_lt : x < s₀.sup (· + 1) := Finset.le_sup (f := (· + 1)) hx
      omega
    have ht_tail_C := hp_tail.comp hrange_shift
    have ht_tail_R := (Complex.continuous_re.continuousAt.tendsto.comp ht_tail_C).congr
      fun K => rfl
    have h_fac_re : ∀ k : ℕ, 1 ≤ k →
        (airyProdFactor uSite epsU k ((-kappaAiry * σ' : ℝ) : ℂ)).re =
          ((σ' - σSeq k) ^ 2 + (εHat k) ^ 2) / (σ' - sNodeAiry k) ^ 2 := by
      intro k hk
      have hzero_eq : airyZero k = -kappaAiry * sNodeAiry k := by
        unfold sNodeAiry; rw [abs_of_neg (airyZero_neg k)]; field_simp [hκ_ne]
      have hfac_C : airyProdFactor uSite epsU k ((-kappaAiry * σ' : ℝ) : ℂ) =
          ((((σ' - σSeq k) ^ 2 + (εHat k) ^ 2) / (σ' - sNodeAiry k) ^ 2 : ℝ) : ℂ) := by
        unfold airyProdFactor uSite epsU
        rw [hzero_eq]
        have hs_ne : σ' - sNodeAiry k ≠ 0 := sub_ne_zero.mpr (hσ'_ne k hk)
        push_cast
        field_simp [hκ_ne, hs_ne]
        ring
      rw [hfac_C, Complex.ofReal_re]
    have h_ratio_ev : ∀ᶠ K : ℕ in atTop,
        windowFiniteProd f σf σSeq εHat K σ' =
          refApprox K σ' * ((σ' - σf) / (∏ k ∈ Finset.Icc 1 f, (σ' - sNodeAiry k) ^ 2)) *
            (∏ m ∈ Finset.range (K - f),
              airyProdFactor uSite epsU (f + 1 + m) ((-kappaAiry * σ' : ℝ) : ℂ)).re := by
      filter_upwards [eventually_ge_atTop f] with K hKf
      have h_prod_re : (∏ m ∈ Finset.range (K - f),
            airyProdFactor uSite epsU (f + 1 + m) ((-kappaAiry * σ' : ℝ) : ℂ)).re =
          ∏ m ∈ Finset.range (K - f),
            (((σ' - σSeq (f + 1 + m)) ^ 2 + (εHat (f + 1 + m)) ^ 2) /
              (σ' - sNodeAiry (f + 1 + m)) ^ 2) := by
        have h_all : ∏ m ∈ Finset.range (K - f),
            airyProdFactor uSite epsU (f + 1 + m) ((-kappaAiry * σ' : ℝ) : ℂ) =
            ((∏ m ∈ Finset.range (K - f),
              (((σ' - σSeq (f + 1 + m)) ^ 2 + (εHat (f + 1 + m)) ^ 2) /
                (σ' - sNodeAiry (f + 1 + m)) ^ 2) : ℝ) : ℂ) := by
          rw [Complex.ofReal_prod]
          refine Finset.prod_congr rfl fun m _ => ?_
          have hfac := h_fac_re (f + 1 + m) (by omega)
          exact Complex.ext (by rw [hfac, Complex.ofReal_re]) (by
            unfold airyProdFactor uSite epsU
            have : (((( -kappaAiry * σ' : ℝ) : ℂ) - ((-kappaAiry * σSeq (f + 1 + m) : ℝ) : ℂ)) ^ 2 +
                ((kappaAiry * εHat (f + 1 + m) : ℝ) : ℂ) ^ 2) /
                (((-kappaAiry * σ' : ℝ) : ℂ) - (airyZero (f + 1 + m) : ℂ)) ^ 2 =
                (((((-kappaAiry * σ' - (-kappaAiry * σSeq (f + 1 + m))) ^ 2 +
                  (kappaAiry * εHat (f + 1 + m)) ^ 2) /
                  (-kappaAiry * σ' - airyZero (f + 1 + m)) ^ 2 : ℝ)) : ℂ) := by push_cast; rfl
            rw [this, Complex.ofReal_im, Complex.ofReal_im])
        rw [h_all, Complex.ofReal_re]
      rw [h_prod_re]
      have hIcc_split : Finset.Icc 1 K = Finset.Icc 1 f ∪ Finset.Icc (f + 1) K := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Icc 1 f) (Finset.Icc (f + 1) K) := by
        rw [Finset.disjoint_left]; intro k hk1 hk2; simp only [Finset.mem_Icc] at hk1 hk2; omega
      have hIcc_img : Finset.Icc (f + 1) K = (Finset.range (K - f)).image (fun m => f + 1 + m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
        constructor
        · intro ⟨h1, h2⟩; exact ⟨k - f - 1, by omega, by omega⟩
        · rintro ⟨m, hm, rfl⟩; omega
      have hprod_tail_ne : ∏ m ∈ Finset.range (K - f), (σ' - sNodeAiry (f + 1 + m)) ^ 2 ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun m _ =>
          pow_ne_zero 2 (sub_ne_zero.mpr (hσ'_ne (f + 1 + m) (by omega)))
      have h_range_eq : ∏ m ∈ Finset.range (K - f),
          (((σ' - σSeq (f + 1 + m)) ^ 2 + (εHat (f + 1 + m)) ^ 2) / (σ' - sNodeAiry (f + 1 + m)) ^ 2) =
          (∏ k ∈ Finset.Icc (f + 1) K, ((σ' - σSeq k) ^ 2 + (εHat k) ^ 2)) /
            (∏ m ∈ Finset.range (K - f), (σ' - sNodeAiry (f + 1 + m)) ^ 2) := by
        rw [Finset.prod_div_distrib, hIcc_img, Finset.prod_image (fun a _ b _ h => by omega)]
      have h_ref_split : ∏ k ∈ Finset.Icc 1 K, (σ' - sNodeAiry k) ^ 2 =
          (∏ k ∈ Finset.Icc 1 f, (σ' - sNodeAiry k) ^ 2) *
            ∏ m ∈ Finset.range (K - f), (σ' - sNodeAiry (f + 1 + m)) ^ 2 := by
        rw [hIcc_split, Finset.prod_union hdisj, hIcc_img,
          Finset.prod_image (fun a _ b _ h => by omega)]
      unfold windowFiniteProd refApprox
      rw [h_range_eq, h_ref_split]
      field_simp [hprod_f_ne, hprod_tail_ne]
    have ht_rhs := (((tendsto_refApprox σ').mul_const ((σ' - σf) / (∏ k ∈ Finset.Icc 1 f, (σ' - sNodeAiry k) ^ 2))).mul
      ht_tail_R).congr' (h_ratio_ev.mono fun _ h => h.symm)
    have hid_lim := tendsto_nhds_unique hconv_W ht_rhs
    rw [hid_lim, refApproxLimit_eq_cStar_mul_airyAi_sq]
    -- Compare with `airyWindowProd` off the Airy zeros:
    rw [airyWindowProd_eq_of_ne f uF uSite epsU hu_ne, airyAiC_ofReal]
    have hden_C : (∏ k ∈ Finset.Icc 1 f, (((-kappaAiry * σ' : ℝ) : ℂ) - (airyZero k : ℂ)) ^ 2) =
        (((kappaAiry ^ (2 * f) * ∏ k ∈ Finset.Icc 1 f, (σ' - sNodeAiry k) ^ 2 : ℝ)) : ℂ) := by
      have hterm : ∀ k ∈ Finset.Icc 1 f,
          ((((-kappaAiry * σ' : ℝ) : ℂ) - (airyZero k : ℂ)) ^ 2) =
            (((kappaAiry ^ 2 * (σ' - sNodeAiry k) ^ 2 : ℝ)) : ℂ) := by
        intro k _
        have hzero_eq : airyZero k = -kappaAiry * sNodeAiry k := by
          unfold sNodeAiry; rw [abs_of_neg (airyZero_neg k)]; field_simp [hκ_ne]
        rw [hzero_eq]; push_cast; ring
      rw [Finset.prod_congr rfl hterm, ← Complex.ofReal_prod, Finset.prod_mul_distrib, Finset.prod_const,
        Nat.card_Icc, show f + 1 - 1 = f by omega, ← pow_mul]
    rw [hden_C]
    set T_re : ℝ := (airyProdTail f uSite epsU ((-kappaAiry * σ' : ℝ) : ℂ)).re
    have hC_re : (-((airyAi (-kappaAiry * σ') : ℝ) : ℂ) ^ 2 * (((-kappaAiry * σ' : ℝ) : ℂ) - (uF : ℂ)) /
        (((kappaAiry ^ (2 * f) * ∏ k ∈ Finset.Icc 1 f, (σ' - sNodeAiry k) ^ 2 : ℝ)) : ℂ) *
        airyProdTail f uSite epsU ((-kappaAiry * σ' : ℝ) : ℂ)).re =
        (kappaAiry * airyAi (-kappaAiry * σ') ^ 2 * (σ' - σf) /
          (kappaAiry ^ (2 * f) * ∏ k ∈ Finset.Icc 1 f, (σ' - sNodeAiry k) ^ 2)) * T_re := by
      have h_pref_real : -((airyAi (-kappaAiry * σ') : ℝ) : ℂ) ^ 2 * (((-kappaAiry * σ' : ℝ) : ℂ) - (uF : ℂ)) /
          (((kappaAiry ^ (2 * f) * ∏ k ∈ Finset.Icc 1 f, (σ' - sNodeAiry k) ^ 2 : ℝ)) : ℂ) =
          (((kappaAiry * airyAi (-kappaAiry * σ') ^ 2 * (σ' - σf) /
            (kappaAiry ^ (2 * f) * ∏ k ∈ Finset.Icc 1 f, (σ' - sNodeAiry k) ^ 2) : ℝ)) : ℂ) := by
        dsimp [uF]; push_cast; ring
      rw [h_pref_real, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hC_re]
    have hzpow : kappaAiry ^ (2 * ((f : ℤ) - 1)) * kappaAiry * kappaAiry / kappaAiry ^ (2 * f) = 1 := by
      rw [← zpow_natCast kappaAiry (2 * f), show (2 : ℤ) * ((f : ℤ) - 1) = (2 * (f : ℤ)) - 2 by ring,
        zpow_sub₀ hκ_ne, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
      push_cast
      field_simp [hκ_ne]
    calc CStar * airyAi (-kappaAiry * σ') ^ 2 *
          ((σ' - σf) / ∏ k ∈ Finset.Icc 1 f, (σ' - sNodeAiry k) ^ 2) * T_re
        = (CStar * kappaAiry ^ (2 * ((f : ℤ) - 1))) * kappaAiry *
            (kappaAiry * airyAi (-kappaAiry * σ') ^ 2 * (σ' - σf) /
              (kappaAiry ^ (2 * f) * ∏ k ∈ Finset.Icc 1 f, (σ' - sNodeAiry k) ^ 2) * T_re) *
            (kappaAiry ^ (2 * ((f : ℤ) - 1)) * kappaAiry * kappaAiry / kappaAiry ^ (2 * f))⁻¹ := by
              have hz_ne : (kappaAiry ^ (2 * ((f : ℤ) - 1)) * kappaAiry * kappaAiry / kappaAiry ^ (2 * f)) ≠ 0 := by
                rw [hzpow]; exact one_ne_zero
              field_simp [hz_ne, hprod_f_ne, hκ_ne]
      _ = CStarF f * kappaAiry *
            (kappaAiry * airyAi (-kappaAiry * σ') ^ 2 * (σ' - σf) /
              (kappaAiry ^ (2 * f) * ∏ k ∈ Finset.Icc 1 f, (σ' - sNodeAiry k) ^ 2) * T_re) := by
            rw [hzpow, inv_one, mul_one]; unfold CStarF; rfl
  -- Step 4b: extend to all `σ : ℝ` by continuity and density of `(Set.range sNodeAiry)ᶜ`:
  have h_lhs_cont : Continuous (tildeW f σf σSeq εHat) :=
    continuous_tildeW f N hf hN hM hC_t hσf hmod htail
  have h_rhs_cont : Continuous (fun σ' : ℝ =>
      CStarF f * kappaAiry * (airyWindowProd f uF uSite epsU ((-kappaAiry * σ' : ℝ) : ℂ)).re) := by
    have hdiff := airyWindowProd_differentiable f hf uF uSite epsU hH
    have hu_cont : Continuous (fun σ' : ℝ => ((-kappaAiry * σ' : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)
    exact continuous_const.mul (Complex.continuous_re.comp (hdiff.continuous.comp hu_cont))
  have hdense : Dense (Set.range sNodeAiry)ᶜ :=
    (Set.countable_range sNodeAiry).dense_compl ℝ
  exact congrFun (Continuous.ext_on hdense h_lhs_cont h_rhs_cont fun σ' hσ' =>
    h_off σ' fun k _ h => hσ' ⟨k, h.symm⟩) σ

lemma CStarF_one : CStarF 1 = CStar := by
  unfold CStarF
  norm_num

private lemma airyProdTail_congr {f : ℕ} {uSite₁ uSite₂ epsU₁ epsU₂ : ℕ → ℝ}
    (hu : ∀ k : ℕ, f < k → uSite₁ k = uSite₂ k)
    (he : ∀ k : ℕ, f < k → epsU₁ k = epsU₂ k) (u : ℂ) :
    airyProdTail f uSite₁ epsU₁ u = airyProdTail f uSite₂ epsU₂ u := by
  unfold airyProdTail airyProdFactor
  congr 1; ext m
  rw [hu (f + 1 + m) (by omega), he (f + 1 + m) (by omega)]

private lemma airyProdTailExcept_congr {f n : ℕ} {uSite₁ uSite₂ epsU₁ epsU₂ : ℕ → ℝ}
    (hu : ∀ k : ℕ, f < k → uSite₁ k = uSite₂ k)
    (he : ∀ k : ℕ, f < k → epsU₁ k = epsU₂ k) (u : ℂ) :
    airyProdTailExcept f n uSite₁ epsU₁ u = airyProdTailExcept f n uSite₂ epsU₂ u := by
  unfold airyProdTailExcept airyProdFactor
  congr 1; ext m
  split_ifs
  · rfl
  · rw [hu (f + 1 + m) (by omega), he (f + 1 + m) (by omega)]

private lemma airyWindowProd_congr {f : ℕ} {uF : ℝ} {uSite₁ uSite₂ epsU₁ epsU₂ : ℕ → ℝ}
    (hu : ∀ k : ℕ, f < k → uSite₁ k = uSite₂ k)
    (he : ∀ k : ℕ, f < k → epsU₁ k = epsU₂ k) (u : ℂ) :
    airyWindowProd f uF uSite₁ epsU₁ u = airyWindowProd f uF uSite₂ epsU₂ u := by
  unfold airyWindowProd
  by_cases h1 : ∃ n : ℕ, 1 ≤ n ∧ u = (airyZero n : ℂ)
  · simp only [h1, ↓reduceDIte]
    by_cases h2 : Nat.find h1 ≤ f
    · simp only [h2, ↓reduceIte, airyProdTail_congr hu he u]
    · simp only [h2, ↓reduceIte, hu (Nat.find h1) (by omega), he (Nat.find h1) (by omega),
        airyProdTailExcept_congr hu he u]
  · simp only [h1, ↓reduceDIte, airyProdTail_congr hu he u]

/-- **Lemma ID (`ut:ID`), `f = 1` design specialization** (`designWindowW`):
For every `N ≥ 1`, `η_* ∈ ℝ`, `d ∈ ℝ`, and `σ : ℝ`, the window limit of `designCombData N etaStar d`
equals `C_* κ Re(designWindowW N etaStar d (-κ σ))`. -/
theorem lemma_ID_design (N : ℕ) (hN : 1 ≤ N) (etaStar d σ : ℝ) :
    let dc := designCombData N etaStar d
    tildeW 1 dc.sigmaFLim dc.allSigmaLim dc.allEpsLim σ =
      CStar * kappaAiry * (designWindowW N etaStar d ((-kappaAiry * σ : ℝ) : ℂ)).re := by
  intro dc
  have hκ := kappaAiry_pos
  have hκ_ne : kappaAiry ≠ 0 := hκ.ne'
  set M : ℝ := |dc.sigmaFLim| + 1 +
    (Finset.Icc 2 N).sum (fun k => |dc.allSigmaLim k| + |dc.allEpsLim k|)
  have hM : 0 < M := by
    have hs : 0 ≤ (Finset.Icc 2 N).sum (fun k => |dc.allSigmaLim k| + |dc.allEpsLim k|) :=
      Finset.sum_nonneg fun _ _ => by positivity
    dsimp [M]; positivity
  obtain ⟨C₀, hC₀, hδ⟩ := deltaWKB_le_exists
  set C_t : ℝ := max (C₀ / kappaAiry) (1 / 3 : ℝ)
  have hCt : 0 < C_t := by positivity
  have hσf : |dc.sigmaFLim| ≤ M := by
    have hs : 0 ≤ (Finset.Icc 2 N).sum (fun k => |dc.allSigmaLim k| + |dc.allEpsLim k|) :=
      Finset.sum_nonneg fun _ _ => by positivity
    dsimp [M]; linarith
  have hmod : ∀ k ∈ Finset.Icc 2 N, |dc.allSigmaLim k| ≤ M ∧ |dc.allEpsLim k| ≤ M := by
    intro k hk
    have hle := Finset.single_le_sum (f := fun j => |dc.allSigmaLim j| + |dc.allEpsLim j|)
      (fun _ _ => by positivity) hk
    constructor <;> dsimp [M] <;> linarith [abs_nonneg dc.sigmaFLim, abs_nonneg (dc.allSigmaLim k), abs_nonneg (dc.allEpsLim k)]
  have htail : ∀ k : ℕ, N < k →
      |dc.allSigmaLim k - phiWKB k| ≤ C_t * (k : ℝ) ^ (-(4 / 3 : ℝ)) ∧
        |dc.allEpsLim k| ≤ C_t * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
    intro k hk
    have hnot : ¬ k ≤ N := by omega
    simp only [dc, ModifiedCombData.allSigmaLim, ModifiedCombData.allEpsLim, designCombData,
      hnot, ↓reduceIte, sub_self, abs_zero]
    refine ⟨by positivity, ?_⟩
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    have hphi_gap : 0 ≤ phiWKB (k + 1) - phiWKB k ∧
        phiWKB (k + 1) - phiWKB k ≤ (4 / 3 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
      have hgap := (gapWKB_bounds (by omega : 1 ≤ k)).2
      have h_ge : (1 : ℝ) ≤ (k : ℝ) := hk1
      have h_eq : phiWKB (k + 1) - phiWKB k = gapWKB k / kappaAiry := by
        unfold gapWKB uWKB; field_simp [hκ_ne]; ring
      have hk_half : (k : ℝ) / 2 ≤ (k : ℝ) - 1 / 4 := by linarith
      have h_low : (0 : ℝ) ≤ phiWKB (k + 1) - phiWKB k := by
        unfold phiWKB
        exact sub_nonneg.mpr (Real.rpow_le_rpow (by linarith) (by push_cast; linarith) (by norm_num))
      refine ⟨h_low, ?_⟩
      rw [h_eq]
      calc gapWKB k / kappaAiry ≤ ((2 / 3 : ℝ) * kappaAiry * ((k : ℝ) - 1 / 4) ^ (-(1 / 3 : ℝ))) / kappaAiry :=
            div_le_div_of_nonneg_right hgap hκ.le
        _ = (2 / 3 : ℝ) * ((k : ℝ) - 1 / 4) ^ (-(1 / 3 : ℝ)) := by field_simp [hκ_ne]
        _ ≤ (2 / 3 : ℝ) * ((k : ℝ) / 2) ^ (-(1 / 3 : ℝ)) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos (div_pos hk_pos zero_lt_two) hk_half (by norm_num))
              (by norm_num)
        _ = (2 / 3 : ℝ) * (2 : ℝ) ^ (1 / 3 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
            rw [div_eq_mul_inv (k : ℝ) 2, Real.mul_rpow hk_pos.le (by positivity),
              show ((2 : ℝ)⁻¹) ^ (-(1 / 3 : ℝ)) = (2 : ℝ) ^ (1 / 3 : ℝ) by
                rw [Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv]]
            ring
        _ ≤ (4 / 3 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
            have h2_13 : (2 : ℝ) ^ (1 / 3 : ℝ) ≤ 2 := by
              simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 3 : ℝ) ≤ 1)
            have hk_nneg : 0 ≤ (k : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
            nlinarith
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4), abs_of_nonneg hphi_gap.1]
    calc (1 / 4 : ℝ) * (phiWKB (k + 1) - phiWKB k)
        ≤ (1 / 4 : ℝ) * ((4 / 3 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ))) := mul_le_mul_of_nonneg_left hphi_gap.2 (by norm_num)
      _ = (1 / 3 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by ring
      _ ≤ C_t * (k : ℝ) ^ (-(1 / 3 : ℝ)) := by
          gcongr; exact le_max_right _ _
  have hid := lemma_ID 1 N le_rfl hN hM hCt hσf hmod htail σ
  have huF_eq : -kappaAiry * dc.sigmaFLim = airyZero 1 - d := by
    dsimp [dc, designCombData]
    unfold sNodeAiry
    rw [abs_of_neg (airyZero_neg 1)]
    field_simp [hκ_ne]
    ring
  have huSite_eq : ∀ k : ℕ, 1 < k → -kappaAiry * dc.allSigmaLim k = designSiteU N k := by
    intro k hk
    dsimp [dc, ModifiedCombData.allSigmaLim, designCombData]
    unfold designSiteU
    split_ifs with hkN
    · unfold sNodeAiry; rw [abs_of_neg (airyZero_neg k)]; field_simp [hκ_ne]
    · unfold uWKB; rfl
  have heps_eq : ∀ k : ℕ, 1 < k → kappaAiry * dc.allEpsLim k = designWidthU N etaStar k := by
    intro k hk
    dsimp [dc, ModifiedCombData.allEpsLim, designCombData]
    unfold designWidthU gapWKB uWKB
    split_ifs <;> ring
  rw [hid, CStarF_one, huF_eq]
  unfold designWindowW
  rw [airyWindowProd_congr huSite_eq heps_eq ((-kappaAiry * σ : ℝ) : ℂ)]

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.refApproxLimit_eq_exp_mul_airyAi_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refApproxLimit_eq_exp_mul_airyAi_sq

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.refApproxLimit_eq_cStar_mul_airyAi_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms refApproxLimit_eq_cStar_mul_airyAi_sq

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.lemma_ID' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_ID

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.lemma_ID_design' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_ID_design

end

end FormalResearch.ModularBootstrap.Upper.Window
