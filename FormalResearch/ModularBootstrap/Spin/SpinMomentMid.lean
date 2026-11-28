module

public import FormalResearch.ModularBootstrap.Spin.SpinMomentTail

/-!
# Far Volterra tail decay and mid-band domination for `SPIN-M`

Source: `CFT/modular_bootstrap/paper/spinning_airy_moment_proof.tex`
(`sd:spinmoment-tail`, `sd:spinmoment-window-pair`).

* `spinMoment_volterra_tail_far`: for any sequence of `SpinCrossingMeasureOn` satisfying
  `GapCondition` (with no uniform bound assumed on the cone opening `B j`),
  `(∫ r in Ici (c_j (xiStar + 1)²/3), |K^* g₅(r)| dν₀) / (c_j FKc 1 1 c_j) → 0`.
* `spinMoment_mid_band_dom`: on the mid-band `x ∈ [xiStar + λ Σ₀, xiStar + 1]`,
  `0 < g₁(c' x²/3)` and `|K^* g₅(c' x²/3)| ≤ C_mid c' g₁(c' x²/3)` where
  `g₁ = bumpG virasoroProblem (rpParams 0).bumpData 1 (1/4) (designSigma1 0) c'`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Integration
open FormalResearch.ModularBootstrap.Bessel
open FormalResearch.ModularBootstrap.Upper
open FormalResearch.ModularBootstrap.Upper.Rigidity
open FormalResearch.ModularBootstrap.Upper.Assembly
open FormalResearch.ModularBootstrap.Upper.Positivity
open FormalResearch.ModularBootstrap.Upper.Ramped
open FormalResearch.ModularBootstrap.Upper.Design
open FormalResearch.ModularBootstrap.Upper.Hankel
open FormalResearch.ModularBootstrap.Upper.Membership
open FormalResearch.ModularBootstrap.Upper.Window
open FormalResearch.ModularBootstrap.Upper.Window.Tail
open FormalResearch.ModularBootstrap.Upper.Window.Cardy
open FormalResearch.ModularBootstrap.Upper.Bump
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Holes
open FormalResearch.ModularBootstrap.Upper.Saddle

/-! ### 1. Far `x ≥ xiStar + 1` Volterra tail is `o(c' FKc 1 1 c')` -/

private noncomputable def cFV1 : ℝ :=
  √xiStar * (1 - Real.exp (-(4 * π * xiStar))) ^ 2 *
    (1 / Real.cosh (π * xiStar / 2) ^ 2) / (√3 * π)

private noncomputable def kFK1 : ℝ :=
  cFV1 * (2 * √2 / π) ^ (3 / 2 : ℝ) * kTip ^ (1 / 3 : ℝ)

private lemma kFK1_pos : 0 < kFK1 := by
  have hcFV : 0 < cFV1 := by
    unfold cFV1
    have h1 : 0 < 1 - Real.exp (-(4 * π * xiStar)) := by
      have : Real.exp (-(4 * π * xiStar)) < 1 :=
        Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (by have := Real.pi_pos; have := xiStar_pos; positivity))
      linarith
    have hcsh : 0 < 1 / Real.cosh (π * xiStar / 2) ^ 2 :=
      one_div_pos.mpr (pow_pos (Real.cosh_pos _) 2)
    exact div_pos (mul_pos (mul_pos (Real.sqrt_pos.mpr xiStar_pos) (pow_pos h1 2)) hcsh)
      (mul_pos (Real.sqrt_pos.mpr (by norm_num)) Real.pi_pos)
  unfold kFK1
  have := kTip_pos; have := Real.pi_pos
  positivity

private lemma FKc_one_exact (c' : ℝ) (hc' : 0 < c') :
    c' * FKc 1 1 c' = kFK1 * c' ^ (11 / 6 : ℝ) := by
  rw [FKc_one]
  have hFV : FVc 1 c' = cFV1 * (√c' * lambdaComb c') := by
    unfold FVc cFV1
    ring
  have hlam0 : 0 < lambdaComb c' := by unfold lambdaComb; have := kTip_pos; positivity
  have hrpow1 : (2 * √2 / (π * lambdaComb c')) ^ (3 / 2 : ℝ) =
      (2 * √2 / π) ^ (3 / 2 : ℝ) * (lambdaComb c') ^ (-(3 / 2 : ℝ)) := by
    rw [show 2 * √2 / (π * lambdaComb c') = (2 * √2 / π) * (lambdaComb c')⁻¹ by field_simp,
      Real.mul_rpow (by positivity) (inv_nonneg.mpr hlam0.le), Real.inv_rpow hlam0.le,
      Real.rpow_neg hlam0.le]
  have hrpow2 : lambdaComb c' * (lambdaComb c') ^ (-(3 / 2 : ℝ)) =
      kTip ^ (1 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) := by
    calc lambdaComb c' * (lambdaComb c') ^ (-(3 / 2 : ℝ))
        = (lambdaComb c') ^ (1 : ℝ) * (lambdaComb c') ^ (-(3 / 2 : ℝ)) := by rw [Real.rpow_one]
      _ = (lambdaComb c') ^ ((1 : ℝ) + -(3 / 2 : ℝ)) := by rw [← Real.rpow_add hlam0]
      _ = ((kTip * c') ^ (-(2 / 3 : ℝ))) ^ (-(1 / 2 : ℝ)) := by
          unfold lambdaComb; norm_num
      _ = (kTip * c') ^ (-(2 / 3 : ℝ) * -(1 / 2 : ℝ)) := by
          rw [← Real.rpow_mul (by have := kTip_pos; positivity)]
      _ = (kTip * c') ^ (1 / 3 : ℝ) := by norm_num
      _ = kTip ^ (1 / 3 : ℝ) * c' ^ (1 / 3 : ℝ) :=
          Real.mul_rpow (le_of_lt kTip_pos) hc'.le
  have hrpow3 : c' * (√c' * (kTip ^ (1 / 3 : ℝ) * c' ^ (1 / 3 : ℝ))) =
      kTip ^ (1 / 3 : ℝ) * c' ^ (11 / 6 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc c' * (c' ^ (1 / 2 : ℝ) * (kTip ^ (1 / 3 : ℝ) * c' ^ (1 / 3 : ℝ)))
        = kTip ^ (1 / 3 : ℝ) * (c' ^ (1 : ℝ) * c' ^ (1 / 2 : ℝ) * c' ^ (1 / 3 : ℝ)) := by
          rw [Real.rpow_one]; ring
      _ = kTip ^ (1 / 3 : ℝ) * (c' ^ ((1 : ℝ) + 1 / 2) * c' ^ (1 / 3 : ℝ)) := by
          rw [← Real.rpow_add hc']
      _ = kTip ^ (1 / 3 : ℝ) * c' ^ (((1 : ℝ) + 1 / 2) + 1 / 3 : ℝ) := by
          rw [← Real.rpow_add hc']
      _ = kTip ^ (1 / 3 : ℝ) * c' ^ (11 / 6 : ℝ) := by congr 1; norm_num
  rw [hFV, hrpow1]
  calc c' * (cFV1 * (√c' * lambdaComb c') *
          ((2 * √2 / π) ^ (3 / 2 : ℝ) * (lambdaComb c') ^ (-(3 / 2 : ℝ))))
      = cFV1 * (2 * √2 / π) ^ (3 / 2 : ℝ) *
          (c' * (√c' * (lambdaComb c' * (lambdaComb c') ^ (-(3 / 2 : ℝ))))) := by ring
    _ = cFV1 * (2 * √2 / π) ^ (3 / 2 : ℝ) * (kTip ^ (1 / 3 : ℝ) * c' ^ (11 / 6 : ℝ)) := by
        rw [hrpow2, hrpow3]
    _ = kFK1 * c' ^ (11 / 6 : ℝ) := by unfold kFK1; ring

private lemma one_add_pow4_mul_exp_neg_le {x : ℝ} (hx : 1 ≤ x) :
    (1 + x) ^ 4 * Real.exp (-π * x) ≤ 384 * (2 / π) ^ 4 * Real.exp (-(π / 2 * x)) := by
  have hx0 : 0 ≤ π / 2 * x := by have := Real.pi_pos; positivity
  have hpow := Real.pow_div_factorial_le_exp (π / 2 * x) hx0 4
  have hfact : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num
  rw [hfact] at hpow
  have hx4 : x ^ 4 ≤ 24 * (2 / π) ^ 4 * Real.exp (π / 2 * x) := by
    have h1 : (π / 2 * x) ^ 4 ≤ 24 * Real.exp (π / 2 * x) := by linarith
    have h2 : (π / 2) ^ 4 * x ^ 4 ≤ 24 * Real.exp (π / 2 * x) := by
      simpa [mul_pow] using h1
    have hpi : 0 < (π / 2) ^ 4 := by have := Real.pi_pos; positivity
    calc x ^ 4 ≤ (24 * Real.exp (π / 2 * x)) / (π / 2) ^ 4 := (le_div_iff₀' hpi).mpr h2
      _ = 24 * (2 / π) ^ 4 * Real.exp (π / 2 * x) := by
          rw [div_eq_mul_inv, ← inv_pow, inv_div]; ring
  have h1x : (1 + x) ^ 4 ≤ 16 * x ^ 4 := by
    have : 1 + x ≤ 2 * x := by linarith
    have h4 := pow_le_pow_left₀ (by linarith) this 4
    linarith [show (2 * x) ^ 4 = 16 * x ^ 4 by ring]
  have hexp : Real.exp (π / 2 * x) * Real.exp (-π * x) = Real.exp (-(π / 2 * x)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc (1 + x) ^ 4 * Real.exp (-π * x)
      ≤ (16 * x ^ 4) * Real.exp (-π * x) := mul_le_mul_of_nonneg_right h1x (Real.exp_pos _).le
    _ ≤ (16 * (24 * (2 / π) ^ 4 * Real.exp (π / 2 * x))) * Real.exp (-π * x) := by gcongr
    _ = 384 * (2 / π) ^ 4 * (Real.exp (π / 2 * x) * Real.exp (-π * x)) := by ring
    _ = 384 * (2 / π) ^ 4 * Real.exp (-(π / 2 * x)) := by rw [hexp]

private lemma tsum_exp_bin_le {x₀ c' : ℝ} (hc' : 1 ≤ c') :
    Summable (fun i : ℕ => Real.exp (-(π / 2 * (x₀ + (i : ℝ) / √c')))) ∧
      (∑' i : ℕ, Real.exp (-(π / 2 * (x₀ + (i : ℝ) / √c')))) ≤
        Real.exp (-(π / 2 * x₀)) * (1 + 2 / π) * √c' := by
  have hc'0 : 0 < c' := by linarith
  have hsq : 1 ≤ √c' := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hc'
  set a := π / (2 * √c')
  have ha : 0 < a := by have := Real.pi_pos; positivity
  set q := Real.exp (-a)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hfun : (fun i : ℕ => Real.exp (-(π / 2 * (x₀ + (i : ℝ) / √c')))) =
      fun i : ℕ => Real.exp (-(π / 2 * x₀)) * q ^ i := by
    ext i
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    dsimp [a]
    ring
  rw [hfun]
  have hsum : Summable (fun i : ℕ => Real.exp (-(π / 2 * x₀)) * q ^ i) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  refine ⟨hsum, ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  have hadd : a + 1 ≤ Real.exp a := Real.add_one_le_exp a
  have hq_le : q ≤ (1 + a)⁻¹ := by
    have : (Real.exp a)⁻¹ ≤ (a + 1)⁻¹ := inv_anti₀ (by positivity) hadd
    rwa [← Real.exp_neg, add_comm a 1] at this
  have h1q : a / (1 + a) ≤ 1 - q := by
    have : 1 - (1 + a)⁻¹ = a / (1 + a) := by field_simp; ring
    linarith
  have hinv_le : (1 - q)⁻¹ ≤ 1 + 1 / a := by
    have hpos : 0 < a / (1 + a) := by positivity
    calc (1 - q)⁻¹ ≤ (a / (1 + a))⁻¹ := inv_anti₀ hpos h1q
      _ = (1 + a) / a := inv_div a (1 + a)
      _ = 1 + 1 / a := by field_simp; ring
  have h1a : 1 + 1 / a ≤ (1 + 2 / π) * √c' := by
    have : 1 / a = 2 / π * √c' := by dsimp [a]; field_simp
    rw [this]
    nlinarith [hsq]
  calc Real.exp (-(π / 2 * x₀)) * (1 - q)⁻¹
      ≤ Real.exp (-(π / 2 * x₀)) * ((1 + 2 / π) * √c') :=
        mul_le_mul_of_nonneg_left (hinv_le.trans h1a) (Real.exp_pos _).le
    _ = Real.exp (-(π / 2 * x₀)) * (1 + 2 / π) * √c' := by ring

private lemma spinMoment_volterra_tail_step
    {c' τ B C_V κ : ℝ} (hc' : 1 ≤ c') (ha : 2 ≤ c' / 12) (hB : 0 ≤ B)
    (hτ_pos : 0 < τ) (hτ_lin : κ * (c' / 12) ≤ 2 * π * τ - 1 / 2) (hκ : 0 < κ) (hCV : 0 ≤ C_V)
    {X : Set (ℝ × ℝ)} (hX : X ⊆ spinConeB B ∩ {p | τ ≤ p.1 + p.2})
    (meas : SpinCrossingMeasureOn (c' / 12) X) {g : ℝ → ℝ}
    (hg_int : IntegrableOn (spinVolterraAdjoint g) (Ici 0) (spinRadMarginal meas.ν))
    (hg_far : ∀ x : ℝ, xiStar + 1 ≤ x →
      |spinVolterraAdjoint g (c' * x ^ 2 / 3)| ≤
        C_V * c' * (1 + x) ^ 3 * Real.exp (-c' * besselL x - π * x)) :
    ∫ r in Ici (c' * (xiStar + 1) ^ 2 / 3), |spinVolterraAdjoint g r| ∂(spinRadMarginal meas.ν) ≤
      (16 * C_V * Real.exp (π / 3) * (5 * π / κ + 1) * (384 * (2 / π) ^ 4) *
        Real.exp (-(π / 2 * (xiStar + 1))) * (1 + 2 / π)) * c' ^ (3 / 2 : ℝ) := by
  have hc'0 : 0 < c' := by linarith
  set x₀ := xiStar + 1
  have hx₀1 : 1 ≤ x₀ := by linarith [xiStar_pos]
  set ν₀ := spinRadMarginal meas.ν
  set rSeq : ℕ → ℝ := fun i => c' * (x₀ + (i : ℝ) / √c') ^ 2 / 3
  have hrSeq_mono : Monotone rSeq := by
    intro i j hij
    dsimp [rSeq]
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have h0 : 0 ≤ x₀ + (i : ℝ) / √c' := by positivity
    gcongr
  have hrSeq_top : Tendsto rSeq atTop atTop := by
    dsimp [rSeq]
    have h1 : Tendsto (fun i : ℕ => x₀ + (i : ℝ) / √c') atTop atTop :=
      tendsto_const_nhds.add_atTop (Tendsto.atTop_div_const (Real.sqrt_pos.mpr hc'0)
        tendsto_natCast_atTop_atTop)
    have h2 : Tendsto (fun u : ℝ => c' * u ^ 2 / 3) atTop atTop :=
      ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).const_mul_atTop hc'0).atTop_div_const
        (by norm_num)
    exact h2.comp h1
  have hUnion : Ici (c' * x₀ ^ 2 / 3) = ⋃ i : ℕ, Ico (rSeq i) (rSeq (i + 1)) := by
    ext r
    simp only [mem_Ici, mem_iUnion, mem_Ico]
    constructor
    · intro hr
      have h0 : rSeq 0 = c' * x₀ ^ 2 / 3 := by simp [rSeq]
      obtain ⟨N, hN⟩ := (hrSeq_top.eventually_gt_atTop r).exists
      have hmin : ∃ k : ℕ, r < rSeq k := ⟨N, hN⟩
      classical
      let k := Nat.find hmin
      have hk_gt : r < rSeq k := Nat.find_spec hmin
      have hk_pos : 0 < k := by
        by_contra hk0
        have hk' : k = 0 := by omega
        rw [hk', h0] at hk_gt
        linarith
      refine ⟨k - 1, ?_, by rwa [Nat.sub_add_cancel hk_pos]⟩
      by_cases hk1 : k - 1 = 0
      · rw [hk1, h0]; exact hr
      · exact not_lt.mp (Nat.find_min hmin (by omega))
    · rintro ⟨i, hri, -⟩
      exact le_trans (by simp only [rSeq, Nat.cast_zero, zero_div, add_zero]; rfl)
        (le_trans (hrSeq_mono (Nat.zero_le i)) hri)
  have hPair : Pairwise (Function.onFun Disjoint fun i : ℕ => Ico (rSeq i) (rSeq (i + 1))) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_iff]
    intro r ⟨hi, hj⟩
    rcases lt_or_gt_of_ne hij with hij' | hij'
    · have := hrSeq_mono (Nat.succ_le_of_lt hij')
      linarith [hi.2, hj.1]
    · have := hrSeq_mono (Nat.succ_le_of_lt hij')
      linarith [hj.2, hi.1]
  have hInt_tail : IntegrableOn (fun r => |spinVolterraAdjoint g r|) (Ici (c' * x₀ ^ 2 / 3)) ν₀ :=
    (hg_int.mono_set (Ici_subset_Ici.mpr (by positivity))).abs
  rw [show c' * (xiStar + 1) ^ 2 / 3 = c' * x₀ ^ 2 / 3 from rfl, hUnion]
  rw [MeasureTheory.integral_iUnion (fun _ => measurableSet_Ico) hPair (hUnion ▸ hInt_tail)]
  set C_L := 5 * π / κ + 1
  set C_bin := 16 * C_V * Real.exp (π / 3) * C_L * (384 * (2 / π) ^ 4)
  have hbin : ∀ i : ℕ,
      ∫ r in Ico (rSeq i) (rSeq (i + 1)), |spinVolterraAdjoint g r| ∂ν₀ ≤
        C_bin * c' * Real.exp (-(π / 2 * (x₀ + (i : ℝ) / √c'))) := by
    intro i
    set x_i := x₀ + (i : ℝ) / √c'
    have hxi1 : 1 ≤ x_i := by
      have : 0 ≤ (i : ℝ) / √c' := by positivity
      linarith
    set b_i := 1 / (2 * x_i)
    have hb0 : 0 < b_i := by positivity
    have hb1 : b_i ≤ 1 := by
      dsimp [b_i]
      rw [div_le_one (by positivity)]
      linarith
    have hLap := spinRadMarginal_laplace_uniform κ hκ ha hB hτ_pos hτ_lin hX meas hb0 hb1
    have hInt_bi : Integrable (fun r => Real.exp (-2 * π * b_i * r)) ν₀ := by
      have hmeas_sum : Measurable (fun p : ℝ × ℝ => p.1 + p.2) := measurable_fst.add measurable_snd
      have hmap : Integrable (fun r => Real.exp (-2 * π * b_i * r))
          (Measure.map (fun p : ℝ × ℝ => p.1 + p.2) meas.ν) ↔
          Integrable (fun p : ℝ × ℝ => Real.exp (-2 * π * b_i * (p.1 + p.2))) meas.ν :=
        integrable_map_measure
          ((Continuous.stronglyMeasurable (by continuity)).aestronglyMeasurable)
          hmeas_sum.aemeasurable
      exact hmap.mpr (meas.finite_laplace hb0)
    have hInt_ico : IntegrableOn (fun r => |spinVolterraAdjoint g r|)
        (Ico (rSeq i) (rSeq (i + 1))) ν₀ :=
      IntegrableOn.mono_set (hUnion ▸ hInt_tail)
        (subset_iUnion (fun i : ℕ => Ico (rSeq i) (rSeq (i + 1))) i)
    have hInt_exp_ico : IntegrableOn (fun r =>
        (8 * C_V * Real.exp (π / 3) * c' * (1 + x_i) ^ 3 * Real.exp (-π * x_i) *
          Real.exp (-(2 * π * (c' / 12) / b_i))) * Real.exp (-2 * π * b_i * r))
        (Ico (rSeq i) (rSeq (i + 1))) ν₀ :=
      (hInt_bi.integrableOn).const_mul _
    have hpt_ico : ∀ r ∈ Ico (rSeq i) (rSeq (i + 1)),
        |spinVolterraAdjoint g r| ≤
          (8 * C_V * Real.exp (π / 3) * c' * (1 + x_i) ^ 3 * Real.exp (-π * x_i) *
            Real.exp (-(2 * π * (c' / 12) / b_i))) * Real.exp (-2 * π * b_i * r) := by
      intro r ⟨hri, hrn⟩
      have hr0 : 0 ≤ r := le_trans (by positivity) hri
      set x := √(3 * r / c')
      have hx_sq : c' * x ^ 2 / 3 = r := by
        dsimp [x]
        rw [Real.sq_sqrt (by positivity)]
        field_simp
      have hx_lo : x_i ≤ x := by
        dsimp [rSeq] at hri
        have h1 : x_i ^ 2 ≤ 3 * r / c' := by
          rw [le_div_iff₀ hc'0]; linarith
        have h2 := Real.sqrt_le_sqrt h1
        rwa [Real.sqrt_sq (by linarith)] at h2
      have hx_hi : x ≤ x_i + 1 / √c' := by
        have hnx : (x₀ + ((i : ℕ) + 1 : ℕ) / √c') = x_i + 1 / √c' := by
          push_cast; dsimp [x_i]; ring
        have h1 : 3 * r / c' ≤ (x_i + 1 / √c') ^ 2 := by
          dsimp [rSeq] at hrn
          rw [div_le_iff₀ hc'0, ← hnx]; linarith
        have h2 := Real.sqrt_le_sqrt h1
        rwa [Real.sqrt_sq (by positivity)] at h2
      have hx_far : xiStar + 1 ≤ x := by
        have h1 : xiStar + 1 ≤ x_i := by
          dsimp [x_i, x₀]; linarith [show (0 : ℝ) ≤ (i : ℝ) / √c' by positivity]
        exact h1.trans hx_lo
      have hV := hg_far x hx_far
      rw [hx_sq] at hV
      have h1x : 1 + x ≤ 2 * (1 + x_i) := by
        have : 1 / √c' ≤ 1 := div_le_one_of_le₀ (by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hc')
          (Real.sqrt_nonneg _)
        linarith
      have hcube : (1 + x) ^ 3 ≤ 8 * (1 + x_i) ^ 3 := by
        have := pow_le_pow_left₀ (by linarith [hxi1]) h1x 3
        linarith [show (2 * (1 + x_i)) ^ 3 = 8 * (1 + x_i) ^ 3 by ring]
      have hexppi : Real.exp (-π * x) ≤ Real.exp (-π * x_i) :=
        Real.exp_le_exp.mpr (by have := Real.pi_pos; nlinarith)
      have hsq_err : (x - x_i) ^ 2 ≤ 1 / c' := by
        have h1 : 0 ≤ x - x_i := sub_nonneg.mpr hx_lo
        have h2 : x - x_i ≤ 1 / √c' := by linarith
        calc (x - x_i) ^ 2 ≤ (1 / √c') ^ 2 := pow_le_pow_left₀ h1 h2 2
          _ = 1 / c' := by rw [one_div, inv_pow, Real.sq_sqrt hc'0.le, one_div]
      have hexp_comp : Real.exp (-c' * besselL x) ≤
          Real.exp (π / 3) * Real.exp (-(2 * π * (c' / 12) / b_i)) * Real.exp (-2 * π * b_i * r) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hident : -c' * besselL x =
            π * c' / (3 * x_i) * (x - x_i) ^ 2 + -(2 * π * (c' / 12) / b_i) + -2 * π * b_i * r := by
          rw [← hx_sq]
          unfold besselL
          dsimp [b_i]
          field_simp
          ring
        have hbd : π * c' / (3 * x_i) * (x - x_i) ^ 2 ≤ π / 3 := by
          have h1 : π * c' / (3 * x_i) * (x - x_i) ^ 2 ≤ π * c' / (3 * x_i) * (1 / c') :=
            mul_le_mul_of_nonneg_left hsq_err (by have := Real.pi_pos; positivity)
          have h2 : π * c' / (3 * x_i) * (1 / c') = π / (3 * x_i) := by field_simp
          have h3 : π / (3 * x_i) ≤ π / 3 :=
            div_le_div_of_nonneg_left (Real.pi_pos.le) zero_lt_three (by linarith)
          linarith
        linarith
      calc |spinVolterraAdjoint g r|
          ≤ C_V * c' * (1 + x) ^ 3 * Real.exp (-c' * besselL x - π * x) := hV
        _ = C_V * c' * (1 + x) ^ 3 * (Real.exp (-c' * besselL x) * Real.exp (-π * x)) := by
            rw [sub_eq_add_neg, Real.exp_add, show -(π * x) = -π * x by ring]
        _ ≤ C_V * c' * (8 * (1 + x_i) ^ 3) *
              ((Real.exp (π / 3) * Real.exp (-(2 * π * (c' / 12) / b_i)) *
                Real.exp (-2 * π * b_i * r)) * Real.exp (-π * x_i)) := by
            gcongr
        _ = (8 * C_V * Real.exp (π / 3) * c' * (1 + x_i) ^ 3 * Real.exp (-π * x_i) *
              Real.exp (-(2 * π * (c' / 12) / b_i))) * Real.exp (-2 * π * b_i * r) := by ring
    have hmono1 := setIntegral_mono_on hInt_ico hInt_exp_ico measurableSet_Ico hpt_ico
    rw [integral_const_mul] at hmono1
    have hmono2 : ∫ r in Ico (rSeq i) (rSeq (i + 1)), Real.exp (-2 * π * b_i * r) ∂ν₀ ≤
        ∫ r in Ici (0 : ℝ), Real.exp (-2 * π * b_i * r) ∂ν₀ := by
      refine setIntegral_mono_set hInt_bi.integrableOn
        (Eventually.of_forall fun _ => (Real.exp_pos _).le) ?_
      exact Eventually.of_forall fun r hr => mem_Ici.mpr (le_trans (by positivity) hr.1)
    have hcancel : Real.exp (-(2 * π * (c' / 12) / b_i)) * Real.exp (2 * π * (c' / 12) / b_i) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hpow4 := one_add_pow4_mul_exp_neg_le hxi1
    have hpre_nn : 0 ≤ 8 * C_V * Real.exp (π / 3) * c' * (1 + x_i) ^ 3 * Real.exp (-π * x_i) *
        Real.exp (-(2 * π * (c' / 12) / b_i)) := by positivity
    calc ∫ r in Ico (rSeq i) (rSeq (i + 1)), |spinVolterraAdjoint g r| ∂ν₀
        ≤ (8 * C_V * Real.exp (π / 3) * c' * (1 + x_i) ^ 3 * Real.exp (-π * x_i) *
            Real.exp (-(2 * π * (c' / 12) / b_i))) *
            ∫ r in Ico (rSeq i) (rSeq (i + 1)), Real.exp (-2 * π * b_i * r) ∂ν₀ := hmono1
      _ ≤ (8 * C_V * Real.exp (π / 3) * c' * (1 + x_i) ^ 3 * Real.exp (-π * x_i) *
            Real.exp (-(2 * π * (c' / 12) / b_i))) *
            (C_L / b_i * Real.exp (2 * π * (c' / 12) / b_i)) := by
          gcongr
          exact hmono2.trans hLap
      _ = 8 * C_V * Real.exp (π / 3) * C_L * c' * ((1 + x_i) ^ 3 * (2 * x_i)) *
            Real.exp (-π * x_i) *
            (Real.exp (-(2 * π * (c' / 12) / b_i)) * Real.exp (2 * π * (c' / 12) / b_i)) := by
          dsimp [b_i]; field_simp
      _ ≤ 16 * C_V * Real.exp (π / 3) * C_L * c' * ((1 + x_i) ^ 4 * Real.exp (-π * x_i)) := by
          rw [hcancel, mul_one]
          have : (1 + x_i) ^ 3 * (2 * x_i) ≤ 2 * (1 + x_i) ^ 4 := by
            have : x_i ≤ 1 + x_i := by linarith
            nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 1 + x_i) 3]
          have hc1 : 0 ≤ 8 * C_V * Real.exp (π / 3) * C_L * c' := by positivity
          have he0 : 0 ≤ Real.exp (-π * x_i) := (Real.exp_pos _).le
          calc 8 * C_V * Real.exp (π / 3) * C_L * c' * ((1 + x_i) ^ 3 * (2 * x_i)) *
                Real.exp (-π * x_i)
              ≤ 8 * C_V * Real.exp (π / 3) * C_L * c' * (2 * (1 + x_i) ^ 4) *
                  Real.exp (-π * x_i) := by gcongr
            _ = 16 * C_V * Real.exp (π / 3) * C_L * c' * ((1 + x_i) ^ 4 * Real.exp (-π * x_i)) := by
                ring
      _ ≤ 16 * C_V * Real.exp (π / 3) * C_L * c' *
            (384 * (2 / π) ^ 4 * Real.exp (-(π / 2 * x_i))) := by gcongr
      _ = C_bin * c' * Real.exp (-(π / 2 * (x₀ + (i : ℝ) / √c'))) := by
          dsimp [C_bin, x_i]; ring
  obtain ⟨hsum_e, hsum_le⟩ := tsum_exp_bin_le (x₀ := x₀) hc'
  have hsum_int : Summable (fun i : ℕ =>
      ∫ r in Ico (rSeq i) (rSeq (i + 1)), |spinVolterraAdjoint g r| ∂ν₀) := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun _ => abs_nonneg _) hbin
      (hsum_e.mul_left (C_bin * c'))
  have htsum := Summable.tsum_le_tsum hbin hsum_int (hsum_e.mul_left (C_bin * c'))
  rw [tsum_mul_left] at htsum
  have hsq32 : c' * (Real.exp (-(π / 2 * x₀)) * (1 + 2 / π) * √c') =
      (Real.exp (-(π / 2 * x₀)) * (1 + 2 / π)) * c' ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    have hrp : c' * c' ^ (1 / 2 : ℝ) = c' ^ (3 / 2 : ℝ) := by
      calc c' * c' ^ (1 / 2 : ℝ) = c' ^ (1 : ℝ) * c' ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
        _ = c' ^ ((1 : ℝ) + 1 / 2) := by rw [← Real.rpow_add hc'0]
        _ = c' ^ (3 / 2 : ℝ) := by norm_num
    calc c' * (Real.exp (-(π / 2 * x₀)) * (1 + 2 / π) * c' ^ (1 / 2 : ℝ))
        = Real.exp (-(π / 2 * x₀)) * (1 + 2 / π) * (c' * c' ^ (1 / 2 : ℝ)) := by ring
      _ = Real.exp (-(π / 2 * x₀)) * (1 + 2 / π) * c' ^ (3 / 2 : ℝ) := by rw [hrp]
  calc ∑' i : ℕ, ∫ r in Ico (rSeq i) (rSeq (i + 1)), |spinVolterraAdjoint g r| ∂ν₀
      ≤ C_bin * c' * ∑' i : ℕ, Real.exp (-(π / 2 * (x₀ + (i : ℝ) / √c'))) := htsum
    _ ≤ C_bin * c' * (Real.exp (-(π / 2 * x₀)) * (1 + 2 / π) * √c') := by
        gcongr
    _ = (16 * C_V * Real.exp (π / 3) * (5 * π / κ + 1) * (384 * (2 / π) ^ 4) *
          Real.exp (-(π / 2 * (xiStar + 1))) * (1 + 2 / π)) * c' ^ (3 / 2 : ℝ) := by
        rw [mul_assoc, hsq32]
        dsimp [C_bin, C_L, x₀]
        ring

/-- **`sd:spinmoment-tail`**: for any crossing-measure sequence with `(Gap)` and no uniform bound
assumed on the cone openings `B j`, the far Volterra tail `x ≥ xiStar + 1` is `o(c_j FKc 1 1 c_j)`. -/
theorem spinMoment_volterra_tail_far (N : ℕ) (hN : 1 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (σs : ℕ → ℝ) (cSeq τSeq B : ℕ → ℝ)
    (hc : Tendsto cSeq atTop atTop) (hGap : GapCondition cSeq τSeq)
    (hτ_pos : ∀ j, 0 < τSeq j) (hB : ∀ j, 0 ≤ B j)
    (meas : ∀ j, SpinCrossingMeasureOn (cSeq j / 12) (spinConeB (B j) ∩ {p | τSeq j ≤ p.1 + p.2})) :
    Tendsto (fun j =>
      (∫ r in Ici (cSeq j * (xiStar + 1) ^ 2 / 3),
        |spinVolterraAdjoint (bumpG spinMomentW5Prob (rpParams 4).bumpData N η σs (cSeq j)) r|
          ∂(spinRadMarginal (meas j).ν)) /
        (cSeq j * FKc 1 1 (cSeq j))) atTop (nhds 0) := by
  set d5 := (rpParams 4).bumpData
  obtain ⟨C_V, hCV, hVfar⟩ := volterraAdjoint_bumpG_far_le N hN hη0 hη1 σs zero_lt_one
  have hgood := hc.eventually (bumpG_good spinMomentW5Prob d5 N hN hη0 hη1 σs)
  have hVfar' := hc.eventually hVfar
  have hc1 := hc.eventually_ge_atTop (1 : ℝ)
  have hc24 := hc.eventually_ge_atTop (24 : ℝ)
  have hxiBar : 0 < xiBar := by unfold xiBar; have := xiStar_pos; positivity
  set κ := 6 * π * xiBar
  have hκ : 0 < κ := by positivity
  have hGap1 := hGap 1 zero_lt_one
  have hlin_c : ∀ᶠ c' : ℝ in atTop,
      κ * (c' / 12) ≤ 2 * π * (FixedWeight.TStar c' - 1 * c' ^ (1 / 3 : ℝ)) - 1 / 2 := by
    have hrpow : Tendsto (fun c' : ℝ => (Aopt - 1) * c' ^ (-(2 / 3 : ℝ))) atTop (nhds 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul (Aopt - 1)
    have hsmall : ∀ᶠ c' : ℝ in atTop, (Aopt - 1) * c' ^ (-(2 / 3 : ℝ)) ≤ xiBar / 2 :=
      hrpow.eventually_le_const (half_pos hxiBar)
    have hneg_small : ∀ᶠ c' : ℝ in atTop, -(xiBar / 2) ≤ (Aopt - 1) * c' ^ (-(2 / 3 : ℝ)) := by
      have h0 : Tendsto (fun c' : ℝ => -((Aopt - 1) * c' ^ (-(2 / 3 : ℝ)))) atTop (nhds 0) := by
        simpa using hrpow.neg
      filter_upwards [h0.eventually_le_const (half_pos hxiBar)] with c' hc'
      linarith
    have hc_big : ∀ᶠ c' : ℝ in atTop, 1 / (π * xiBar) ≤ c' := eventually_ge_atTop _
    filter_upwards [hneg_small, hc_big, eventually_ge_atTop (1 : ℝ)] with c' hns hcb hc1'
    have hc0 : 0 < c' := by linarith
    have h13 : c' ^ (1 / 3 : ℝ) = c' * c' ^ (-(2 / 3 : ℝ)) := by
      calc c' ^ (1 / 3 : ℝ) = c' ^ ((1 : ℝ) + -(2 / 3 : ℝ)) := by norm_num
        _ = c' ^ (1 : ℝ) * c' ^ (-(2 / 3 : ℝ)) := Real.rpow_add hc0 1 _
        _ = c' * c' ^ (-(2 / 3 : ℝ)) := by rw [Real.rpow_one]
    have hT : xiBar / 2 * c' ≤ FixedWeight.TStar c' - 1 * c' ^ (1 / 3 : ℝ) := by
      unfold FixedWeight.TStar
      have hm : -(xiBar / 2) * c' ≤ (Aopt - 1) * c' ^ (-(2 / 3 : ℝ)) * c' :=
        mul_le_mul_of_nonneg_right hns hc0.le
      calc xiBar / 2 * c' = xiBar * c' + -(xiBar / 2) * c' := by ring
        _ ≤ xiBar * c' + (Aopt - 1) * c' ^ (-(2 / 3 : ℝ)) * c' := by linarith
        _ = xiBar * c' + (Aopt - 1) * (c' * c' ^ (-(2 / 3 : ℝ))) := by ring
        _ = xiBar * c' + Aopt * c' ^ (1 / 3 : ℝ) - 1 * c' ^ (1 / 3 : ℝ) := by rw [← h13]; ring
    have hpi : 1 / 2 ≤ π * xiBar * c' / 2 := by
      have : 1 / (π * xiBar) ≤ c' := hcb
      have hpos : 0 < π * xiBar := by positivity
      have := (div_le_iff₀ hpos).mp this
      linarith
    have hpi0 : 0 ≤ 2 * π := by positivity
    have h2T : π * xiBar * c' ≤ 2 * π * (FixedWeight.TStar c' - 1 * c' ^ (1 / 3 : ℝ)) := by
      calc π * xiBar * c' = 2 * π * (xiBar / 2 * c') := by ring
        _ ≤ 2 * π * (FixedWeight.TStar c' - 1 * c' ^ (1 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hT hpi0
    dsimp [κ]
    linarith
  have hk_FK := kFK1_pos
  set C_step := 16 * C_V * Real.exp (π / 3) * (5 * π / κ + 1) * (384 * (2 / π) ^ 4) *
      Real.exp (-(π / 2 * (xiStar + 1))) * (1 + 2 / π)
  have hC_step : 0 ≤ C_step := by positivity
  have hUpper : Tendsto (fun j : ℕ => (C_step / kFK1) * (cSeq j) ^ (-(1 / 3 : ℝ))) atTop (nhds 0) := by
    have h0 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul (C_step / kFK1)
    rw [mul_zero] at h0
    exact h0.comp hc
  refine squeeze_zero' ?_ ?_ hUpper
  · filter_upwards [hc1] with j hc1'
    have hc_pos : 0 < cSeq j := lt_of_lt_of_le zero_lt_one hc1'
    have hnum : 0 ≤ ∫ r in Ici (cSeq j * (xiStar + 1) ^ 2 / 3),
        |spinVolterraAdjoint (bumpG spinMomentW5Prob d5 N η σs (cSeq j)) r|
          ∂(spinRadMarginal (meas j).ν) :=
      integral_nonneg fun _ => abs_nonneg _
    have hden : 0 < cSeq j * FKc 1 1 (cSeq j) :=
      mul_pos hc_pos (FKc_pos zero_lt_one 1 hc_pos)
    exact div_nonneg hnum hden.le
  · filter_upwards [hgood, hVfar', hc1, hc24, hGap1, hc.eventually hlin_c]
      with j ⟨hc_pos, htest, C_g, hCg, hdec⟩ hVf hc1' hc24' hg1 hlin'
    have ha : 2 ≤ cSeq j / 12 := by linarith
    have hτ_lin : κ * (cSeq j / 12) ≤ 2 * π * τSeq j - 1 / 2 := by
      have : 0 ≤ 2 * π := by positivity
      linarith [mul_le_mul_of_nonneg_left hg1 this]
    have hpair := spinMoment_pair ha (hB j) (hτ_pos j) Set.Subset.rfl (meas j) htest
      (show 0 < π * √(3 / cSeq j) by positivity) hCg (fun t ht => by
        have := hdec t ht
        rwa [show π * √(3 * t / cSeq j) = π * √(3 / cSeq j) * √t by
          rw [show 3 * t / cSeq j = (3 / cSeq j) * t by ring, Real.sqrt_mul (by positivity),
            mul_assoc]] at this)
    have hstep := spinMoment_volterra_tail_step hc1' ha (hB j) (hτ_pos j) hτ_lin hκ hCV.le
      Set.Subset.rfl (meas j) hpair.2.2.1 hVf
    have hFKj := FKc_one_exact (cSeq j) hc_pos
    have hden : 0 < cSeq j * FKc 1 1 (cSeq j) :=
      mul_pos hc_pos (FKc_pos zero_lt_one 1 hc_pos)
    rw [hFKj]
    have hrpow_div : (cSeq j) ^ (3 / 2 : ℝ) / (kFK1 * (cSeq j) ^ (11 / 6 : ℝ)) =
        (cSeq j) ^ (-(1 / 3 : ℝ)) / kFK1 := by
      rw [div_eq_mul_inv, mul_inv, ← mul_assoc, mul_comm (cSeq j ^ (3 / 2 : ℝ)) kFK1⁻¹,
        mul_assoc, ← Real.rpow_neg hc_pos.le, ← Real.rpow_add hc_pos]
      ring_nf
    calc (∫ r in Ici (cSeq j * (xiStar + 1) ^ 2 / 3),
            |spinVolterraAdjoint (bumpG spinMomentW5Prob d5 N η σs (cSeq j)) r|
              ∂(spinRadMarginal (meas j).ν)) / (kFK1 * (cSeq j) ^ (11 / 6 : ℝ))
        ≤ (C_step * (cSeq j) ^ (3 / 2 : ℝ)) / (kFK1 * (cSeq j) ^ (11 / 6 : ℝ)) := by
          refine div_le_div_of_nonneg_right hstep ?_
          rw [← hFKj]
          exact hden.le
      _ = (C_step / kFK1) * (cSeq j) ^ (-(1 / 3 : ℝ)) := by
          have : C_step * (cSeq j) ^ (3 / 2 : ℝ) / (kFK1 * (cSeq j) ^ (11 / 6 : ℝ)) =
              C_step * ((cSeq j) ^ (3 / 2 : ℝ) / (kFK1 * (cSeq j) ^ (11 / 6 : ℝ))) := by ring
          rw [this, hrpow_div]
          ring

/-! ### 2. Mid-band domination `|K^* g₅| ≤ C_mid c' g₁` on `[xiStar + λ Σ₀, xiStar + 1]` -/

lemma besselV_mul_deriv_lower :
    ∃ c_V > 0, ∀ᶠ c' in atTop, ∀ y ∈ Icc (xiStar / 2) (xiStar + 1),
      c_V * √c' * Real.exp (c' * besselL y) ≤
        virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) * (2 * c' * y / 3) := by
  have hx₀ : 0 < xiStar / 2 := half_pos xiStar_pos
  set c_V := √(xiStar / 2) / (3 * √3 * π)
  have hcV : 0 < c_V := by have := Real.pi_pos; positivity
  refine ⟨c_V, hcV, ?_⟩
  filter_upwards [eventually_ge_atTop (10000 : ℝ)] with c' hc' y hy
  have ha : 2 ≤ c' / 12 := by linarith
  have hc'0 : 0 < c' := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le hx₀ hy.1
  have ht0 : 0 ≤ c' * y ^ 2 / 3 := by positivity
  rw [virasoro_cardyV_eq_besselV ha ht0]
  have hcmp := besselV_comparison hc' hy.1
  have hbV_pos : 0 < besselV (c' / 12) (c' * y ^ 2 / 3) := by
    by_contra hle
    push Not at hle
    have hdiv : 1 / √(c' * y ^ 2 / 3) * Real.exp (c' * besselL y) /
        besselV (c' / 12) (c' * y ^ 2 / 3) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (by positivity) hle
    have hpos : 0 < 5 * π / 3 / √y := by have := Real.pi_pos; positivity
    linarith [hcmp.1]
  have h1 : Real.exp (c' * besselL y) / √(c' * y ^ 2 / 3) ≤
      6 * π / √y * besselV (c' / 12) (c' * y ^ 2 / 3) := by
    have hdiv := (div_le_iff₀ hbV_pos).mp hcmp.2
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
  have hsqrt : √(c' * y ^ 2 / 3) = √c' * y / √3 := by
    rw [show c' * y ^ 2 / 3 = (c' / 3) * y ^ 2 by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hy0.le, Real.sqrt_div hc'0.le]
    ring
  have hmul : √y / (6 * π) * (Real.exp (c' * besselL y) * (2 * c' * y / 3) / √(c' * y ^ 2 / 3)) ≤
      besselV (c' / 12) (c' * y ^ 2 / 3) * (2 * c' * y / 3) := by
    have hpos1 : 0 ≤ √y / (6 * π) := by have := Real.pi_pos; positivity
    have hpos2 : 0 ≤ 2 * c' * y / 3 := by positivity
    have h1' : √y / (6 * π) * (Real.exp (c' * besselL y) / √(c' * y ^ 2 / 3)) ≤
        besselV (c' / 12) (c' * y ^ 2 / 3) := by
      have hp : 0 < 6 * π / √y := by have := Real.pi_pos; positivity
      have := (div_le_iff₀' hp).mpr h1
      calc √y / (6 * π) * (Real.exp (c' * besselL y) / √(c' * y ^ 2 / 3))
          = (Real.exp (c' * besselL y) / √(c' * y ^ 2 / 3)) / (6 * π / √y) := by
            field_simp
        _ ≤ besselV (c' / 12) (c' * y ^ 2 / 3) := this
    calc √y / (6 * π) * (Real.exp (c' * besselL y) * (2 * c' * y / 3) / √(c' * y ^ 2 / 3))
        = (√y / (6 * π) * (Real.exp (c' * besselL y) / √(c' * y ^ 2 / 3))) * (2 * c' * y / 3) := by
          ring
      _ ≤ besselV (c' / 12) (c' * y ^ 2 / 3) * (2 * c' * y / 3) :=
          mul_le_mul_of_nonneg_right h1' hpos2
  have hLHS_simp : √y / (6 * π) * (Real.exp (c' * besselL y) * (2 * c' * y / 3) / √(c' * y ^ 2 / 3)) =
      (√y / (3 * √3 * π)) * √c' * Real.exp (c' * besselL y) := by
    rw [hsqrt]
    have hsq3 : √3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hsqc : √c' ≠ 0 := (Real.sqrt_pos.mpr hc'0).ne'
    have hpi : π ≠ 0 := Real.pi_ne_zero
    have hy_ne : y ≠ 0 := hy0.ne'
    field_simp
    rw [Real.sq_sqrt (by norm_num), Real.sq_sqrt hc'0.le]
    ring
  have hy_lo : c_V ≤ √y / (3 * √3 * π) := by
    dsimp [c_V]
    gcongr
    exact hy.1
  calc c_V * √c' * Real.exp (c' * besselL y)
      ≤ (√y / (3 * √3 * π)) * √c' * Real.exp (c' * besselL y) := by gcongr
    _ = √y / (6 * π) * (Real.exp (c' * besselL y) * (2 * c' * y / 3) / √(c' * y ^ 2 / 3)) :=
        hLHS_simp.symm
    _ ≤ besselV (c' / 12) (c' * y ^ 2 / 3) * (2 * c' * y / 3) := hmul

lemma kernelK5_mul_deriv_lower :
    ∃ c_K > 0, ∀ᶠ c' in atTop, ∀ y ∈ Icc (xiStar / 2) (xiStar + 1),
      c_K * √c' * Real.exp (c' * besselL y) ≤
        kernelK 5 (c' / 12) (c' * y ^ 2 / 3) * (2 * c' * y / 3) := by
  obtain ⟨c_V, hcV, hV⟩ := besselV_mul_deriv_lower
  obtain ⟨C, hC0, hK⟩ := kernelK5_div_virasoro_bound (x₀ := xiStar / 2) (X := xiStar + 1)
    (half_pos xiStar_pos) (by linarith [xiStar_pos])
  set q := qProb spinMomentW5Prob
  have hq : 0 < q := qProb_pos spinMomentW5Prob
  have hxi : 0 < xiStar := xiStar_pos
  have hpi : 0 < π := Real.pi_pos
  set M := q / xiStar ^ 4 + 1
  have hM : 0 < M := by positivity
  set δ₀ := q * ((1 - Real.exp (-2 * π * xiStar)) ^ 2 / (2 * (xiStar + 1)) ^ 4)
  have hxi : 0 < xiStar := xiStar_pos
  have hpi : 0 < π := Real.pi_pos
  have hδ₀ : 0 < δ₀ := by
    have h1 : 0 < 1 - Real.exp (-2 * π * xiStar) := by
      have : Real.exp (-2 * π * xiStar) < 1 :=
        Real.exp_lt_one_iff.mpr (by nlinarith)
      linarith
    exact mul_pos hq (div_pos (pow_pos h1 2) (by positivity))
  refine ⟨q * c_V / M, div_pos (mul_pos hq hcV) hM, ?_⟩
  filter_upwards [hV, hK, eventually_ge_atTop (max (max C 1) (2 * C / δ₀))] with c' hcV' hcK' hcmax y hy
  have hc' : 1 ≤ c' := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hcmax
  have hc'0 : 0 < c' := by linarith
  have hy0 : 0 < y := by linarith [hy.1]
  have hcK := hcK' y hy
  have hquot_le : q * virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) /
      kernelK 5 (c' / 12) (c' * y ^ 2 / 3) ≤ M := by
    have hCc' : C / c' ≤ 1 :=
      div_le_one_of_le₀ (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hcmax) hc'0.le
    have h1 := (abs_le.mp hcK).2
    have h2 : (1 - Real.exp (-4 * π * y)) ^ 2 / (2 * y) ^ 4 ≤ 1 / xiStar ^ 4 := by
      have hnum : (1 - Real.exp (-4 * π * y)) ^ 2 ≤ 1 := by
        have hp : 0 ≤ 1 - Real.exp (-4 * π * y) := by
          have : Real.exp (-4 * π * y) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
          linarith
        have hle : 1 - Real.exp (-4 * π * y) ≤ 1 := by linarith [Real.exp_pos (-4 * π * y)]
        nlinarith
      have hden : xiStar ^ 4 ≤ (2 * y) ^ 4 := pow_le_pow_left₀ xiStar_pos.le (by linarith [hy.1]) 4
      have hxi4 : 0 < xiStar ^ 4 := pow_pos xiStar_pos 4
      calc (1 - Real.exp (-4 * π * y)) ^ 2 / (2 * y) ^ 4
          ≤ 1 / (2 * y) ^ 4 := div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ 1 / xiStar ^ 4 := one_div_le_one_div_of_le hxi4 hden
    have h3 : q * ((1 - Real.exp (-4 * π * y)) ^ 2 / (2 * y) ^ 4) ≤ q / xiStar ^ 4 := by
      rw [div_eq_mul_inv (a := q), ← one_div]
      exact mul_le_mul_of_nonneg_left h2 hq.le
    dsimp [q, M] at h1 h3 ⊢
    linarith
  have hK_pos : 0 < kernelK 5 (c' / 12) (c' * y ^ 2 / 3) := by
    have hV_pos : 0 < virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) := by
      have hder : 0 < 2 * c' * y / 3 := by positivity
      have hle := hcV' y hy
      nlinarith [mul_pos hcV (Real.sqrt_pos.mpr hc'0), Real.exp_pos (c' * besselL y)]
    by_contra hle
    push Not at hle
    have hdiv0 : q * virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) /
        kernelK 5 (c' / 12) (c' * y ^ 2 / 3) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (mul_nonneg hq.le hV_pos.le) hle
    have hlo := (abs_le.mp hcK).1
    have hδ_le : δ₀ ≤ q * ((1 - Real.exp (-4 * π * y)) ^ 2 / (2 * y) ^ 4) := by
      have h1 : 1 - Real.exp (-2 * π * xiStar) ≤ 1 - Real.exp (-4 * π * y) := by
        have : Real.exp (-4 * π * y) ≤ Real.exp (-2 * π * xiStar) :=
          Real.exp_le_exp.mpr (by nlinarith [hy.1])
        linarith
      have h0 : 0 ≤ 1 - Real.exp (-2 * π * xiStar) := by
        have : Real.exp (-2 * π * xiStar) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        linarith
      have hnum : (1 - Real.exp (-2 * π * xiStar)) ^ 2 ≤ (1 - Real.exp (-4 * π * y)) ^ 2 :=
        pow_le_pow_left₀ h0 h1 2
      have hden : (2 * y) ^ 4 ≤ (2 * (xiStar + 1)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) (by linarith [hy.2]) 4
      have hfrac := div_le_div₀ (sq_nonneg _) hnum (by positivity) hden
      exact mul_le_mul_of_nonneg_left hfrac hq.le
    have hCc_half : C / c' ≤ δ₀ / 2 := by
      have h1 : 2 * C / δ₀ ≤ c' := le_trans (le_max_right _ _) hcmax
      rw [div_le_iff₀ hc'0]
      have h2 := (div_le_iff₀ hδ₀).mp h1
      linarith
    linarith
  have hKV : q / M * virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) ≤
      kernelK 5 (c' / 12) (c' * y ^ 2 / 3) := by
    have h1 := (div_le_iff₀ hK_pos).mp hquot_le
    rw [div_mul_eq_mul_div, div_le_iff₀ hM]
    linarith
  calc q * c_V / M * √c' * Real.exp (c' * besselL y)
      = (q / M) * (c_V * √c' * Real.exp (c' * besselL y)) := by ring
    _ ≤ (q / M) * (virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3) * (2 * c' * y / 3)) :=
        mul_le_mul_of_nonneg_left (hcV' y hy) (div_nonneg hq.le hM.le)
    _ = (q / M * virasoroProblem.cardyV (c' / 12) (c' * y ^ 2 / 3)) * (2 * c' * y / 3) := by ring
    _ ≤ kernelK 5 (c' / 12) (c' * y ^ 2 / 3) * (2 * c' * y / 3) :=
        mul_le_mul_of_nonneg_right hKV (by positivity)

lemma sdvPrefactor_mid_regionII_bound :
    ∃ Cs > 0, ∀ᶠ c' in atTop, ∀ y : ℝ, xiStar < y → y ≤ xiStar + 1 →
      combAmplitude c' y * fwsdRatio 4 y ≤
        Cs * (y - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL y) := by
  set D := 1 + Real.sinh (π * (xiStar + 1)) ^ 2
  have hD : 0 < D := by positivity
  set E_c := √(2 * π / D)
  have hEc : 0 < E_c := by have := Real.pi_pos; positivity
  set Cs := 2 * 8 * 3 * 2 * √((1 + 1 / (2 * xiStar)) / E_c) * (1 + 1 / (2 * xiStar)) ^ 4
  have hCs : 0 < Cs :=
    mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (div_pos (by have := xiStar_pos; positivity) hEc)))
      (pow_pos (by have := xiStar_pos; positivity) 4)
  refine ⟨Cs, hCs, ?_⟩
  filter_upwards [eventually_ge_atTop (3 / (8 * π * xiStar))] with c' hc' y hy_gt hy_le
  have hc'0 : 0 < c' := lt_of_lt_of_le (by have := Real.pi_pos; have := xiStar_pos; positivity) hc'
  have hy0 : 0 < y := xiStar_pos.trans hy_gt
  have hk : 1 / 2 ≤ 4 * π * c' * y / 3 := by
    have h1 : 1 / 2 ≤ 4 * π * c' * xiStar / 3 := by
      have := Real.pi_pos; have := xiStar_pos
      calc (1 / 2 : ℝ) = 4 * π * (3 / (8 * π * xiStar)) * xiStar / 3 := by field_simp; ring
        _ ≤ 4 * π * c' * xiStar / 3 := by gcongr
    have h2 : 4 * π * c' * xiStar / 3 ≤ 4 * π * c' * y / 3 := by gcongr
    linarith
  have hsdv := sdvPrefactor_le (Φ₁ := fun _ => 0) hc'0 hy_gt le_rfl hk (fun _ => rfl)
  -- Lower bound `edgeF' (edgeV y) ≥ E_c * √(y - xiStar)`
  have hsinh_xi : Real.sinh (π * xiStar) = 1 := by
    unfold xiStar
    rw [mul_div_cancel₀ _ Real.pi_ne_zero, Real.sinh_arsinh]
  have hsinh_ge1 : 1 ≤ Real.sinh (π * y) := by
    rw [← hsinh_xi]
    exact (Real.sinh_strictMono (by have := Real.pi_pos; nlinarith)).le
  have hsinh_diff : π * (y - xiStar) ≤ Real.sinh (π * y) - 1 := by
    have hpi_lt : π * xiStar < π * y := by have := Real.pi_pos; nlinarith
    obtain ⟨ξ, _, hξ⟩ := exists_hasDerivAt_eq_slope Real.sinh Real.cosh hpi_lt
      Real.continuous_sinh.continuousOn (fun t _ => Real.hasDerivAt_sinh t)
    have hcosh : 1 ≤ Real.cosh ξ := Real.one_le_cosh ξ
    rw [hsinh_xi, eq_div_iff (by linarith)] at hξ
    nlinarith
  have hcosh_ev : Real.cosh (π * edgeV y) = Real.sinh (π * y) := by
    unfold edgeV
    rw [mul_div_cancel₀ _ Real.pi_ne_zero, Real.cosh_arcosh hsinh_ge1]
  have hev_pos : 0 < edgeV y := edgeV_pos hy_gt
  have hsinh_ev_nn : 0 ≤ Real.sinh (π * edgeV y) := by
    rw [Real.sinh_nonneg_iff]; have := Real.pi_pos; positivity
  have hsinh_ev_sq : 2 * π * (y - xiStar) ≤ Real.sinh (π * edgeV y) ^ 2 := by
    have hsq := Real.cosh_sq_sub_sinh_sq (π * edgeV y)
    have hfac : Real.sinh (π * y) ^ 2 - 1 = (Real.sinh (π * y) - 1) * (Real.sinh (π * y) + 1) := by ring
    have h1 : Real.sinh (π * edgeV y) ^ 2 = Real.sinh (π * y) ^ 2 - 1 := by rw [← hcosh_ev]; linarith
    rw [h1, hfac]
    nlinarith [hsinh_diff, hsinh_ge1]
  have hsinh_ev_lb : √(2 * π * (y - xiStar)) ≤ Real.sinh (π * edgeV y) := by
    have := Real.sqrt_le_sqrt hsinh_ev_sq
    rwa [Real.sqrt_sq hsinh_ev_nn] at this
  have hden_ev : 1 + Real.cosh (π * edgeV y) ^ 2 ≤ D := by
    rw [hcosh_ev]
    have hs1 : Real.sinh (π * y) ≤ Real.sinh (π * (xiStar + 1)) :=
      Real.sinh_strictMono.monotone (by have := Real.pi_pos; nlinarith)
    have hs0 : 0 ≤ Real.sinh (π * y) := by linarith
    dsimp [D]
    gcongr
  have hFp_lb : E_c * √(y - xiStar) ≤ edgeF' (edgeV y) := by
    unfold edgeF'
    have h1 : √(2 * π * (y - xiStar)) / √D ≤ Real.sinh (π * edgeV y) / √(1 + Real.cosh (π * edgeV y) ^ 2) :=
      div_le_div₀ hsinh_ev_nn hsinh_ev_lb (Real.sqrt_pos.mpr (by positivity))
        (Real.sqrt_le_sqrt hden_ev)
    calc E_c * √(y - xiStar) = √(2 * π) / √D * √(y - xiStar) := by
          dsimp [E_c]; rw [Real.sqrt_div (by have := Real.pi_pos; positivity)]
      _ = √(2 * π * (y - xiStar)) / √D := by
          rw [div_mul_eq_mul_div, ← Real.sqrt_mul (by have := Real.pi_pos; positivity)]
      _ ≤ _ := h1
  have hFp_pos : 0 < edgeF' (edgeV y) := edgeF'_pos hev_pos
  have hyx_pos : 0 < y - xiStar := sub_pos.mpr hy_gt
  have hyx_le1 : y - xiStar ≤ 1 := by linarith
  have hxi : 0 < xiStar := xiStar_pos
  have hsqrt_comb : √((1 + 1 / (2 * y)) / edgeF' (edgeV y)) ≤
      √((1 + 1 / (2 * xiStar)) / E_c) * (y - xiStar) ^ (-(1 / 4 : ℝ)) := by
    have hnum : 1 + 1 / (2 * y) ≤ 1 + 1 / (2 * xiStar) := by
      gcongr
    have hfrac : (1 + 1 / (2 * y)) / edgeF' (edgeV y) ≤
        (1 + 1 / (2 * xiStar)) / (E_c * √(y - xiStar)) :=
      div_le_div₀ (by positivity) hnum (mul_pos hEc (Real.sqrt_pos.mpr hyx_pos)) hFp_lb
    have hsq := Real.sqrt_le_sqrt hfrac
    have hs2 : √(√(y - xiStar)) = (y - xiStar) ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hyx_pos.le]
      norm_num
    calc √((1 + 1 / (2 * y)) / edgeF' (edgeV y))
        ≤ √((1 + 1 / (2 * xiStar)) / (E_c * √(y - xiStar))) := hsq
      _ = √((1 + 1 / (2 * xiStar)) / E_c) * (√(√(y - xiStar)))⁻¹ := by
          rw [div_mul_eq_div_div, Real.sqrt_div (by positivity), div_eq_mul_inv]
      _ = √((1 + 1 / (2 * xiStar)) / E_c) * (y - xiStar) ^ (-(1 / 4 : ℝ)) := by
          rw [hs2, ← Real.rpow_neg hyx_pos.le]
  have hrpow_comp : (y - xiStar) ^ (-(1 / 4 : ℝ)) ≤ (y - xiStar) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hyx_pos hyx_le1 (by norm_num)
  have hfws := fwsdRatio_le (p := 4) hy_gt
  have hamp_le : combAmplitude c' y ≤
      2 * 8 * 3 * 2 * √((1 + 1 / (2 * xiStar)) / E_c) * (y - xiStar) ^ (-(3 / 2 : ℝ)) *
        Real.exp (-c' * besselL y - π * y) := by
    unfold combAmplitude besselL
    rw [show -c' * (2 * π * y / 3) - π * y = -(c' * (2 * π * y / 3)) - π * y by ring]
    calc sdvPrefactor c' y sechSqProfile (fun _ => 0) hankelEps
        ≤ 2 * 8 * 3 * 2 * √((1 + 1 / (2 * y)) / edgeF' (edgeV y)) *
            Real.exp (-(c' * (2 * π * y / 3)) - π * y) := hsdv
      _ ≤ 2 * 8 * 3 * 2 * (√((1 + 1 / (2 * xiStar)) / E_c) * (y - xiStar) ^ (-(3 / 2 : ℝ))) *
            Real.exp (-(c' * (2 * π * y / 3)) - π * y) := by
          gcongr
          exact hsqrt_comb.trans (mul_le_mul_of_nonneg_left hrpow_comp (Real.sqrt_nonneg _))
      _ = _ := by ring
  have hexp_le : Real.exp (-c' * besselL y - π * y) ≤ Real.exp (-c' * besselL y) := by
    apply Real.exp_le_exp.mpr
    have hpi := Real.pi_pos
    nlinarith [hy0]
  have hfws0 : 0 ≤ fwsdRatio 4 y := by unfold fwsdRatio; have := xiStar_pos; positivity
  calc combAmplitude c' y * fwsdRatio 4 y
      ≤ (2 * 8 * 3 * 2 * √((1 + 1 / (2 * xiStar)) / E_c) * (y - xiStar) ^ (-(3 / 2 : ℝ)) *
          Real.exp (-c' * besselL y - π * y)) * (1 + 1 / (2 * xiStar)) ^ 4 :=
        mul_le_mul hamp_le hfws hfws0 (by positivity)
    _ ≤ (2 * 8 * 3 * 2 * √((1 + 1 / (2 * xiStar)) / E_c) * (y - xiStar) ^ (-(3 / 2 : ℝ)) *
          Real.exp (-c' * besselL y)) * (1 + 1 / (2 * xiStar)) ^ 4 := by gcongr
    _ = Cs * (y - xiStar) ^ (-(3 / 2 : ℝ)) * Real.exp (-c' * besselL y) := by ring

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinMoment_volterra_tail_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spinMoment_volterra_tail_far

end FormalResearch.ModularBootstrap.Spin

