module

public import FormalResearch.ModularBootstrap.Integrality.HankelSonine
public import FormalResearch.ModularBootstrap.Integrality.RepairIdentity
public import FormalResearch.ModularBootstrap.Integrality.RepairTaylor

/-!
# Linear Crossing Repair Theorem (`int:repair`, `int:sonine`)

Discharges `int:repair` and `int:sonine` unconditionally for every integer weight `1 ≤ w : ℕ`:
* `sonineRepairConst : ℝ`: explicit universal constant `max 1 (24576 * π ^ 3 + 16 * π + 1)`.
* `hankel_repair`: given `0 < B₀ < B`, `M : ℕ`, and finite measures `σ, μ` on `[B₀, B]` matching all
  polynomial moments of degree `≤ M`, constructs `r : ℝ → ℝ` continuous on `(B, ∞)` satisfying:
  1. `exp (-2π β t) * |r t|` integrable on `(B, ∞)` and the exact crossing repair identity
     `∫ Ξ_β dσ - ∫ Ξ_β dμ + ∫_{B}^∞ Ξ_β(t) r(t) dt = 0` for every `β > 0`;
  2. the quantitative Hankel–Taylor + Sonine decay bound with constant `sonineRepairConst`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped ENNReal Polynomial

namespace FormalResearch.ModularBootstrap.Integrality

open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.WeightAxioms

/-- Universal constant `C_son` entering the Hankel–Sonine tail bound of `int:repair`. -/
noncomputable def sonineRepairConst : ℝ :=
  max 1 (24576 * π ^ 3 + 16 * π + 1)

lemma sonineRepairConst_nonneg : 0 ≤ sonineRepairConst := by
  unfold sonineRepairConst
  exact le_trans zero_le_one (le_max_left _ _)

private lemma pow_div_factorial_le_exp_pow (m : ℕ) (hm : 1 ≤ m) {x : ℝ} (hx : 0 ≤ x) :
    x ^ m / (Nat.factorial m : ℝ) ≤ (Real.exp 1 * x / (m : ℝ)) ^ m := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hexp : (m : ℝ) ^ m / (Nat.factorial m : ℝ) ≤ Real.exp m :=
    Real.pow_div_factorial_le_exp (m : ℝ) hm_pos.le m
  have hexp_pow : Real.exp (m : ℝ) = (Real.exp 1) ^ m := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hexp_pow] at hexp
  have hm_pow_pos : (0 : ℝ) < (m : ℝ) ^ m := pow_pos hm_pos m
  have h1 : 1 / (Nat.factorial m : ℝ) ≤ (Real.exp 1 / (m : ℝ)) ^ m := by
    rw [div_pow, le_div_iff₀ hm_pow_pos]
    calc 1 / (Nat.factorial m : ℝ) * (m : ℝ) ^ m = (m : ℝ) ^ m / (Nat.factorial m : ℝ) := by ring
      _ ≤ (Real.exp 1) ^ m := hexp
  calc x ^ m / (Nat.factorial m : ℝ) = x ^ m * (1 / (Nat.factorial m : ℝ)) := by ring
    _ ≤ x ^ m * (Real.exp 1 / (m : ℝ)) ^ m := mul_le_mul_of_nonneg_left h1 (pow_nonneg hx m)
    _ = (Real.exp 1 * x / (m : ℝ)) ^ m := by rw [← mul_pow]; congr 1; ring

private lemma sonine_const_absorb (w : ℕ) {B : ℝ} (hB : 0 < B) :
    2 * π * B * max 4 (2048 * π ^ 2 * B ^ 2 * Real.exp (16 * π * B)) ≤
      sonineRepairConst * Real.exp (sonineRepairConst * (B + (w : ℝ))) := by
  have hC1 : 1 ≤ sonineRepairConst := le_max_left _ _
  have hC_ge : 24576 * π ^ 3 + 16 * π + 1 ≤ sonineRepairConst := le_max_right _ _
  have hpi : 1 ≤ π := by linarith [Real.two_le_pi]
  have hpi3 : 1 ≤ π ^ 3 := one_le_pow₀ hpi
  have h8pi : 8 * π ≤ sonineRepairConst := by linarith
  have h24 : 24576 * π ^ 3 ≤ sonineRepairConst := by linarith
  have h16pi1 : 16 * π + 1 ≤ sonineRepairConst := by linarith
  have hw0 : 0 ≤ sonineRepairConst * (w : ℝ) :=
    mul_nonneg sonineRepairConst_nonneg (Nat.cast_nonneg w)
  have hexp_Bw : Real.exp (sonineRepairConst * B) ≤
      Real.exp (sonineRepairConst * (B + (w : ℝ))) := by
    refine Real.exp_le_exp.mpr ?_
    rw [mul_add]
    linarith
  have hexp_B_le : Real.exp B ≤ Real.exp (sonineRepairConst * B) :=
    Real.exp_le_exp.mpr (le_mul_of_one_le_left hB.le hC1)
  have hB_le_exp : B ≤ Real.exp B := (Real.add_one_le_exp B).trans' (by linarith)
  have hB3_le_exp : B ^ 3 ≤ 6 * Real.exp B := by
    have h := Real.pow_div_factorial_le_exp B hB.le 3
    have h3f : (Nat.factorial 3 : ℝ) = 6 := by norm_num
    rw [h3f] at h
    linarith
  have hcase1 : 2 * π * B * 4 ≤ sonineRepairConst * Real.exp (sonineRepairConst * (B + (w : ℝ))) := by
    calc 2 * π * B * 4 = (8 * π) * B := by ring
      _ ≤ sonineRepairConst * Real.exp B := mul_le_mul h8pi hB_le_exp hB.le sonineRepairConst_nonneg
      _ ≤ sonineRepairConst * Real.exp (sonineRepairConst * (B + (w : ℝ))) :=
          mul_le_mul_of_nonneg_left (hexp_B_le.trans hexp_Bw) sonineRepairConst_nonneg
  have hcase2 : 2 * π * B * (2048 * π ^ 2 * B ^ 2 * Real.exp (16 * π * B)) ≤
      sonineRepairConst * Real.exp (sonineRepairConst * (B + (w : ℝ))) := by
    have hexp_sum : Real.exp ((16 * π + 1) * B) ≤ Real.exp (sonineRepairConst * B) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h16pi1 hB.le)
    calc 2 * π * B * (2048 * π ^ 2 * B ^ 2 * Real.exp (16 * π * B))
        = 4096 * π ^ 3 * B ^ 3 * Real.exp (16 * π * B) := by ring
      _ ≤ 4096 * π ^ 3 * (6 * Real.exp B) * Real.exp (16 * π * B) := by gcongr
      _ = (24576 * π ^ 3) * (Real.exp (16 * π * B) * Real.exp B) := by ring
      _ = (24576 * π ^ 3) * Real.exp ((16 * π + 1) * B) := by
          rw [← Real.exp_add]; congr 2; ring
      _ ≤ sonineRepairConst * Real.exp (sonineRepairConst * (B + (w : ℝ))) :=
          mul_le_mul h24 (hexp_sum.trans hexp_Bw) (Real.exp_pos _).le sonineRepairConst_nonneg
  rw [mul_max_of_nonneg _ _ (by positivity)]
  exact max_le hcase1 hcase2

private lemma continuous_kerDual_of_compact {w : ℕ} {B₀ B : ℝ}
    {σ μ : Measure ℝ} [IsFiniteMeasure σ] [IsFiniteMeasure μ]
    (hσ : σ (Icc B₀ B)ᶜ = 0) (hμ : μ (Icc B₀ B)ᶜ = 0) :
    Continuous (kerDual (hankelKernel w) σ μ) := by
  have hk_fst : ∀ s : ℝ, Continuous (fun t => hankelKernel w t s) := fun s =>
    (continuous_hankelKernel w).comp (continuous_id.prodMk continuous_const)
  have hk_snd : ∀ t : ℝ, Continuous (fun s => hankelKernel w t s) := fun t =>
    (continuous_hankelKernel w).comp (continuous_const.prodMk continuous_id)
  have hcont_m : ∀ (η : Measure ℝ) [IsFiniteMeasure η], η (Icc B₀ B)ᶜ = 0 →
      Continuous (fun t => ∫ s, hankelKernel w t s ∂η) := by
    intro η _ hη
    rw [continuous_iff_continuousAt]
    intro t₀
    by_cases hne : (Icc B₀ B).Nonempty
    · obtain ⟨s₀, hs₀⟩ := hne
      have hcompact : IsCompact ((Icc (t₀ - 1) (t₀ + 1)) ×ˢ (Icc B₀ B)) :=
        isCompact_Icc.prod isCompact_Icc
      have hne_prod : ((Icc (t₀ - 1) (t₀ + 1)) ×ˢ (Icc B₀ B)).Nonempty :=
        ⟨(t₀, s₀), ⟨⟨by linarith, by linarith⟩, hs₀⟩⟩
      have hcont_abs : Continuous (fun p : ℝ × ℝ => |hankelKernel w p.1 p.2|) :=
        continuous_abs.comp (continuous_hankelKernel w)
      obtain ⟨p₀, _, hp₀⟩ := hcompact.exists_isMaxOn hne_prod hcont_abs.continuousOn
      let Mbd : ℝ := |hankelKernel w p₀.1 p₀.2|
      refine tendsto_integral_filter_of_dominated_convergence (fun _ => Mbd) ?_ ?_ ?_ ?_
      · exact Eventually.of_forall fun t => (hk_snd t).aestronglyMeasurable
      · filter_upwards [Icc_mem_nhds (by linarith : t₀ - 1 < t₀) (by linarith : t₀ < t₀ + 1)] with t ht
        filter_upwards [ae_iff.mpr hη] with s hs
        exact hp₀ (⟨ht, hs⟩ : (t, s) ∈ (Icc (t₀ - 1) (t₀ + 1)) ×ˢ (Icc B₀ B))
      · exact integrable_const Mbd
      · exact Eventually.of_forall fun s => (hk_fst s).continuousAt
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      have h0 : η = 0 := Measure.measure_univ_eq_zero.mp (by simpa [hne] using hη)
      have h_eq : (fun t => ∫ s, hankelKernel w t s ∂η) = fun _ => 0 := by
        ext t; simp [h0]
      rw [h_eq]
      exact continuousAt_const
  exact (hcont_m σ hσ).sub (hcont_m μ hμ)

private lemma integrableOn_rpow_mul_exp_rate {r : ℝ} (hr : 0 < r) (w : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ (((w - 1 : ℕ) : ℝ) / 2) * Real.exp (-r * t)) (Ioi 0) := by
  have hpow_dom : IntegrableOn (fun t : ℝ =>
      (1 + (Nat.factorial (w - 1) : ℝ) / (r / 2) ^ (w - 1)) * Real.exp (-(r / 2) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -(r / 2) < 0) 0).const_mul _
  refine hpow_dom.mono' ((by fun_prop : Continuous fun t : ℝ =>
      t ^ (((w - 1 : ℕ) : ℝ) / 2) * Real.exp (-r * t)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := mem_Ioi.mp ht
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_pos _).le)]
  have hpow_le_exp : t ^ (w - 1) ≤
      ((Nat.factorial (w - 1) : ℝ) / (r / 2) ^ (w - 1)) * Real.exp ((r / 2) * t) := by
    have hx := Real.pow_div_factorial_le_exp (r / 2 * t) (by positivity) (w - 1)
    have hfac : (0 : ℝ) < (Nat.factorial (w - 1) : ℝ) := by positivity
    have hr2 : (0 : ℝ) < (r / 2) ^ (w - 1) := by positivity
    calc t ^ (w - 1)
        = ((r / 2) ^ (w - 1))⁻¹ * (r / 2 * t) ^ (w - 1) := by
            rw [mul_pow, ← mul_assoc, inv_mul_cancel₀ hr2.ne', one_mul]
      _ ≤ ((r / 2) ^ (w - 1))⁻¹ * ((Nat.factorial (w - 1) : ℝ) * Real.exp (r / 2 * t)) := by
            gcongr
            simpa [mul_comm] using (div_le_iff₀ hfac).mp hx
      _ = ((Nat.factorial (w - 1) : ℝ) / (r / 2) ^ (w - 1)) * Real.exp ((r / 2) * t) := by ring
  have hle : t ^ (((w - 1 : ℕ) : ℝ) / 2) ≤ 1 + t ^ (w - 1) := by
    rcases le_or_gt t 1 with ht1 | ht1
    · linarith [Real.rpow_le_one ht0.le ht1 (by positivity : 0 ≤ (((w - 1 : ℕ) : ℝ) / 2)),
        pow_nonneg ht0.le (w - 1)]
    · have hexp_le : (((w - 1 : ℕ) : ℝ) / 2) ≤ ((w - 1 : ℕ) : ℝ) := by
        have : (0 : ℝ) ≤ ((w - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      have h1' : t ^ (((w - 1 : ℕ) : ℝ) / 2) ≤ t ^ ((w - 1 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le ht1.le hexp_le
      rw [Real.rpow_natCast] at h1'
      linarith
  have h1exp : (1 : ℝ) ≤ Real.exp ((r / 2) * t) := Real.one_le_exp (by positivity)
  calc t ^ (((w - 1 : ℕ) : ℝ) / 2) * Real.exp (-r * t)
      ≤ (1 + t ^ (w - 1)) * Real.exp (-r * t) := mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    _ ≤ (Real.exp ((r / 2) * t) +
          ((Nat.factorial (w - 1) : ℝ) / (r / 2) ^ (w - 1)) * Real.exp ((r / 2) * t)) *
          Real.exp (-r * t) := by gcongr
    _ = (1 + (Nat.factorial (w - 1) : ℝ) / (r / 2) ^ (w - 1)) *
          (Real.exp ((r / 2) * t) * Real.exp (-r * t)) := by ring
    _ = (1 + (Nat.factorial (w - 1) : ℝ) / (r / 2) ^ (w - 1)) * Real.exp (-(r / 2) * t) := by
          rw [← Real.exp_add]; congr 2; ring

private lemma hankelMeasure_Ioi_compl (w : ℕ) :
    (hankelMeasure w) (Ioi (0 : ℝ))ᶜ = 0 := by
  unfold hankelMeasure
  rw [withDensity_apply _ measurableSet_Ioi.compl,
    Measure.restrict_restrict measurableSet_Ioi.compl, compl_inter_self,
    Measure.restrict_empty, lintegral_zero_measure]

private lemma inv_sqrt_prod_rpow (w : ℕ) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    (1 / Real.sqrt (t * s)) ^ (w - 1) = (t * s) ^ (-((w - 1 : ℕ) : ℝ) / 2) := by
  rw [one_div, Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity),
    ← Real.rpow_natCast ((t * s) ^ (-(1 / 2 : ℝ))) (w - 1), ← Real.rpow_mul (by positivity)]
  congr 1; ring

private lemma kerDual_abs_triv {w : ℕ} {B₀ B : ℝ} (hB₀ : 0 < B₀)
    {σ μ : Measure ℝ} [IsFiniteMeasure σ] [IsFiniteMeasure μ]
    (hσ : σ (Icc B₀ B)ᶜ = 0) (hμ : μ (Icc B₀ B)ᶜ = 0) {t : ℝ} (ht : 0 < t) :
    |kerDual (hankelKernel w) σ μ t| ≤
      2 * π * (σ.real univ + μ.real univ) * (t * B₀) ^ (-((w - 1 : ℕ) : ℝ) / 2) := by
  have h_m : ∀ (η : Measure ℝ) [IsFiniteMeasure η], η (Icc B₀ B)ᶜ = 0 →
      |∫ s, hankelKernel w t s ∂η| ≤
        2 * π * η.real univ * (t * B₀) ^ (-((w - 1 : ℕ) : ℝ) / 2) := by
    intro η _ hηc
    have hbd_ae : ∀ᵐ s ∂η, ‖hankelKernel w t s‖ ≤
        2 * π * (t * B₀) ^ (-((w - 1 : ℕ) : ℝ) / 2) := by
      filter_upwards [ae_iff.mpr hηc] with s hs
      have hs0 : 0 < s := hB₀.trans_le hs.1
      rw [Real.norm_eq_abs]
      have h1 : (1 / Real.sqrt (t * s)) ^ (w - 1) ≤ (1 / Real.sqrt (t * B₀)) ^ (w - 1) := by
        gcongr; exact hs.1
      exact (hankelKernel_abs_le w ht hs0).trans
        (by rw [← inv_sqrt_prod_rpow w ht hB₀]; gcongr)
    calc |∫ s, hankelKernel w t s ∂η|
        = ‖∫ s, hankelKernel w t s ∂η‖ := (Real.norm_eq_abs _).symm
      _ ≤ 2 * π * (t * B₀) ^ (-((w - 1 : ℕ) : ℝ) / 2) * η.real univ :=
          norm_integral_le_of_norm_le_const hbd_ae
      _ = 2 * π * η.real univ * (t * B₀) ^ (-((w - 1 : ℕ) : ℝ) / 2) := by ring
  calc |kerDual (hankelKernel w) σ μ t|
      ≤ |∫ s, hankelKernel w t s ∂σ| + |∫ s, hankelKernel w t s ∂μ| := abs_sub _ _
    _ ≤ 2 * π * σ.real univ * (t * B₀) ^ (-((w - 1 : ℕ) : ℝ) / 2) +
          2 * π * μ.real univ * (t * B₀) ^ (-((w - 1 : ℕ) : ℝ) / 2) :=
        add_le_add (h_m σ hσ) (h_m μ hμ)
    _ = 2 * π * (σ.real univ + μ.real univ) * (t * B₀) ^ (-((w - 1 : ℕ) : ℝ) / 2) := by ring

private lemma kerDual_abs_taylor {w : ℕ} {B₀ B : ℝ} (hB₀ : 0 < B₀) (hB : B₀ ≤ B) (M : ℕ)
    {σ μ : Measure ℝ} [IsFiniteMeasure σ] [IsFiniteMeasure μ]
    (hσ : σ (Icc B₀ B)ᶜ = 0) (hμ : μ (Icc B₀ B)ᶜ = 0)
    (hmom : ∀ P : ℝ[X], P.degree ≤ M → ∫ s, P.eval s ∂σ = ∫ s, P.eval s ∂μ)
    {t : ℝ} (ht : 0 < t) :
    |kerDual (hankelKernel w) σ μ t| ≤
      2 * π * (σ.real univ + μ.real univ) * (t * B₀) ^ (-((w - 1 : ℕ) : ℝ) / 2) *
        (2 * π * Real.exp 1 * ((B - B₀) / 2) * Real.sqrt t / (((M + 1 : ℕ) : ℝ) * Real.sqrt B₀)) ^ (M + 1) := by
  let h : ℝ := (B - B₀) / 2
  let m : ℕ := M + 1
  have hm1 : 1 ≤ m := Nat.succ_le_succ (Nat.zero_le M)
  have hh_nn : 0 ≤ h := by dsimp [h]; linarith
  have hker_σ : ∫ s, hankelKernel w t s ∂σ =
      2 * π * (1 / Real.sqrt t) ^ (w - 1) * ∫ s, besselKernelR (w - 1) t s ∂σ := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_iff.mpr hσ] with s hs
    exact hankelKernel_eq_besselKernelR w ht (hB₀.trans_le hs.1)
  have hker_μ : ∫ s, hankelKernel w t s ∂μ =
      2 * π * (1 / Real.sqrt t) ^ (w - 1) * ∫ s, besselKernelR (w - 1) t s ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_iff.mpr hμ] with s hs
    exact hankelKernel_eq_besselKernelR w ht (hB₀.trans_le hs.1)
  have hbd := hankelDual_bound (w - 1) ht hB₀ hB M hσ hμ hmom
  have hfac := pow_div_factorial_le_exp_pow m hm1
    (by positivity : 0 ≤ 2 * π * Real.sqrt t * h / Real.sqrt B₀)
  have hpow_comb : (1 / Real.sqrt t) ^ (w - 1) * (1 / Real.sqrt B₀) ^ (w - 1) =
      (t * B₀) ^ (-((w - 1 : ℕ) : ℝ) / 2) := by
    rw [← mul_pow, one_div, one_div, ← mul_inv, ← Real.sqrt_mul ht.le B₀,
      ← one_div, inv_sqrt_prod_rpow w ht hB₀]
  have h_m_eq : (2 * π * Real.sqrt t / Real.sqrt B₀) ^ m * h ^ m / (Nat.factorial m : ℝ) ≤
      (2 * π * Real.exp 1 * h * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m := by
    have h1 : (2 * π * Real.sqrt t / Real.sqrt B₀) ^ m * h ^ m / (Nat.factorial m : ℝ) =
        (2 * π * Real.sqrt t * h / Real.sqrt B₀) ^ m / (Nat.factorial m : ℝ) := by
      rw [← mul_pow]; congr 2; ring
    rw [h1]
    refine hfac.trans_eq ?_
    congr 1; ring
  calc |kerDual (hankelKernel w) σ μ t|
      = |(2 * π * (1 / Real.sqrt t) ^ (w - 1)) *
          (∫ s, besselKernelR (w - 1) t s ∂σ - ∫ s, besselKernelR (w - 1) t s ∂μ)| := by
        dsimp [kerDual]; rw [hker_σ, hker_μ, mul_sub]
    _ = 2 * π * (1 / Real.sqrt t) ^ (w - 1) *
          |∫ s, besselKernelR (w - 1) t s ∂σ - ∫ s, besselKernelR (w - 1) t s ∂μ| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ 2 * π * (1 / Real.sqrt t) ^ (w - 1) *
          ((σ.real univ + μ.real univ) * ((1 / Real.sqrt B₀) ^ (w - 1) *
            ((2 * π * Real.sqrt t / Real.sqrt B₀) ^ m * h ^ m / (Nat.factorial m : ℝ)))) := by gcongr
    _ = 2 * π * (σ.real univ + μ.real univ) *
          ((1 / Real.sqrt t) ^ (w - 1) * (1 / Real.sqrt B₀) ^ (w - 1)) *
          ((2 * π * Real.sqrt t / Real.sqrt B₀) ^ m * h ^ m / (Nat.factorial m : ℝ)) := by ring
    _ ≤ 2 * π * (σ.real univ + μ.real univ) * (t * B₀) ^ (-((w - 1 : ℕ) : ℝ) / 2) *
          (2 * π * Real.exp 1 * h * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m := by
        rw [hpow_comb]; gcongr

/-- **Exact linear crossing repair at weight `1 ≤ w : ℕ` (`int:repair`, `int:sonine`)**. -/
theorem hankel_repair {w : ℕ} (hw : 1 ≤ w) {B₀ B : ℝ} (hB₀ : 0 < B₀) (hB : B₀ < B) (M : ℕ)
    {σ μ : Measure ℝ} [IsFiniteMeasure σ] [IsFiniteMeasure μ]
    (hσ : σ (Icc B₀ B)ᶜ = 0) (hμ : μ (Icc B₀ B)ᶜ = 0)
    (hmom : ∀ P : ℝ[X], P.degree ≤ M → ∫ s, P.eval s ∂σ = ∫ s, P.eval s ∂μ) :
    ∃ r : ℝ → ℝ, ContinuousOn r (Ioi B) ∧
      (∀ {β : ℝ}, 0 < β →
        IntegrableOn (fun t => Real.exp (-2 * π * β * t) * |r t|) (Ioi B) ∧
        (∫ s, thermalDiff w β s ∂σ - ∫ s, thermalDiff w β s ∂μ +
          ∫ t in Ioi B, thermalDiff w β t * r t = 0)) ∧
      (∀ {t : ℝ}, B < t →
        let h := (B - B₀) / 2
        let m : ℕ := M + 1
        |r t| ≤ 2 * π * (σ.real univ + μ.real univ) * (t / B₀) ^ (((w - 1 : ℕ) : ℝ) / 2) *
          (min 1 ((2 * π * Real.exp 1 * h * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m) +
            sonineRepairConst * Real.exp (sonineRepairConst * (B + w)) *
              (2 * π * Real.exp 1 * h * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m)) := by
  have hB_pos : 0 < B := hB₀.trans hB
  let h : ℝ := (B - B₀) / 2
  let m : ℕ := M + 1
  have hh_nn : 0 ≤ h := by dsimp [h]; linarith
  let hη : ℝ → ℝ := kerDual (hankelKernel w) σ μ
  have hhη_cont : Continuous hη := continuous_kerDual_of_compact hσ hμ
  have hhη_mem : MemLp hη 2 (hankelBandMeasure w B) := by
    obtain ⟨t₀, _, ht₀⟩ := isCompact_Icc.exists_isMaxOn ⟨0, left_mem_Icc.mpr hB_pos.le⟩
      (continuous_abs.comp hhη_cont).continuousOn
    refine MemLp.of_bound hhη_cont.aestronglyMeasurable |hη t₀| ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ht₀ ⟨ht.1.le, ht.2⟩
  obtain ⟨A_inv, hA_right, _, hA_norm⟩ := hankelSonine_inv hw hB_pos
  let f_L2 : Lp ℝ 2 (hankelBandMeasure w B) := A_inv (hhη_mem.toLp hη)
  let f₀ : ℝ → ℝ := (Ioc (0 : ℝ) B).indicator (f_L2 : ℝ → ℝ)
  have hf_raw_eq : ∀ t : ℝ, kerTransform (hankelMeasure w) (hankelKernel w) f₀ t =
      rawHankelBand w B f_L2 t := by
    intro t
    unfold kerTransform rawHankelBand
    rw [integral_hankelMeasure_eq, integral_hankelBandMeasure_eq,
      ← integral_indicator (measurableSet_Ioi (a := (0 : ℝ))),
      ← integral_indicator (measurableSet_Ioc (a := (0 : ℝ)) (b := B))]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    by_cases hs : s ∈ Ioc 0 B
    · simp [f₀, hs, hs.1]
    · simp [f₀, hs]
  let r : ℝ → ℝ := fun t =>
    t ^ (w - 1) * (hη t - kerTransform (hankelMeasure w) (hankelKernel w) f₀ t)
  have hr_cont : Continuous r := by
    have hU_cont : Continuous (kerTransform (hankelMeasure w) (hankelKernel w) f₀) := by
      rw [show kerTransform (hankelMeasure w) (hankelKernel w) f₀ = rawHankelBand w B f_L2 from
        funext hf_raw_eq]
      exact continuous_rawHankelBand
    exact (continuous_pow _).mul (hhη_cont.sub hU_cont)
  have hhη_triv : ∀ {t : ℝ}, 0 < t →
      |hη t| ≤ 2 * π * (σ.real univ + μ.real univ) * (t * B₀) ^ (-((w - 1 : ℕ) : ℝ) / 2) :=
    fun ht => kerDual_abs_triv hB₀ hσ hμ ht
  have hhη_tay : ∀ {t : ℝ}, 0 < t →
      |hη t| ≤ 2 * π * (σ.real univ + μ.real univ) * (t * B₀) ^ (-((w - 1 : ℕ) : ℝ) / 2) *
        (2 * π * Real.exp 1 * h * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m :=
    fun ht => kerDual_abs_taylor hB₀ hB.le M hσ hμ hmom ht
  have hpow_ratio : ∀ {t : ℝ}, 0 < t →
      t ^ (w - 1) * (t * B₀) ^ (-((w - 1 : ℕ) : ℝ) / 2) =
        (t / B₀) ^ (((w - 1 : ℕ) : ℝ) / 2) := by
    intro t ht
    have hb_neg : B₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) = (B₀ ^ (((w - 1 : ℕ) : ℝ) / 2))⁻¹ := by
      rw [show -((w - 1 : ℕ) : ℝ) / 2 = -(((w - 1 : ℕ) : ℝ) / 2) from by ring, Real.rpow_neg hB₀.le]
    have ht_eq : t ^ (w - 1) * t ^ (-((w - 1 : ℕ) : ℝ) / 2) = t ^ (((w - 1 : ℕ) : ℝ) / 2) := by
      rw [← Real.rpow_natCast t (w - 1), ← Real.rpow_add ht]
      congr 2; ring
    calc t ^ (w - 1) * (t * B₀) ^ (-((w - 1 : ℕ) : ℝ) / 2)
        = t ^ (w - 1) * (t ^ (-((w - 1 : ℕ) : ℝ) / 2) * B₀ ^ (-((w - 1 : ℕ) : ℝ) / 2)) := by
          rw [Real.mul_rpow ht.le hB₀.le]
      _ = (t ^ (w - 1) * t ^ (-((w - 1 : ℕ) : ℝ) / 2)) * B₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) := by ring
      _ = t ^ (((w - 1 : ℕ) : ℝ) / 2) * (B₀ ^ (((w - 1 : ℕ) : ℝ) / 2))⁻¹ := by rw [ht_eq, hb_neg]
      _ = (t / B₀) ^ (((w - 1 : ℕ) : ℝ) / 2) := by rw [← div_eq_mul_inv, Real.div_rpow ht.le hB₀.le]
  have hhη_L2_le : ‖hhη_mem.toLp hη‖ ≤
      Real.sqrt B * (2 * π * (σ.real univ + μ.real univ) * B₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) *
        (2 * π * Real.exp 1 * h * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m) := by
    let C_band : ℝ := 2 * π * (σ.real univ + μ.real univ) * B₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) *
      (2 * π * Real.exp 1 * h * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m
    have hCb : 0 ≤ C_band := by positivity
    rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hCb),
      lp_norm_sq_hankelBandMeasure hhη_mem]
    have hconst_int : IntegrableOn (fun _ : ℝ => C_band ^ 2) (Ioc 0 B) :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    have hlhs_int : IntegrableOn (fun t => t ^ (w - 1) * (hη t) ^ 2) (Ioc 0 B) :=
      (integrable_hankelBandMeasure_iff _).mp hhη_mem.integrable_sq
    have hpt : ∀ t ∈ Ioc (0 : ℝ) B, t ^ (w - 1) * (hη t) ^ 2 ≤ C_band ^ 2 := by
      intro t ht
      have ht0 := ht.1
      have h_t := hhη_tay ht0
      have h_tB : |hη t| ≤ t ^ (-((w - 1 : ℕ) : ℝ) / 2) * C_band := by
        have hsqrt : Real.sqrt t ≤ Real.sqrt B := Real.sqrt_le_sqrt ht.2
        have hmul : (t * B₀) ^ (-((w - 1 : ℕ) : ℝ) / 2) =
            t ^ (-((w - 1 : ℕ) : ℝ) / 2) * B₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) :=
          Real.mul_rpow ht0.le hB₀.le
        calc |hη t| ≤ 2 * π * (σ.real univ + μ.real univ) * (t * B₀) ^ (-((w - 1 : ℕ) : ℝ) / 2) *
              (2 * π * Real.exp 1 * h * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m := by
              refine h_t.trans ?_; gcongr
          _ = t ^ (-((w - 1 : ℕ) : ℝ) / 2) * C_band := by rw [hmul]; dsimp [C_band]; ring
      have hsq : (hη t) ^ 2 ≤ t ^ (-((w - 1 : ℕ) : ℝ)) * C_band ^ 2 := by
        calc (hη t) ^ 2 = |hη t| ^ 2 := (sq_abs _).symm
          _ ≤ (t ^ (-((w - 1 : ℕ) : ℝ) / 2) * C_band) ^ 2 := by gcongr
          _ = (t ^ (-((w - 1 : ℕ) : ℝ) / 2)) ^ 2 * C_band ^ 2 := by ring
          _ = t ^ (-((w - 1 : ℕ) : ℝ)) * C_band ^ 2 := by
              rw [← Real.rpow_natCast (t ^ _), ← Real.rpow_mul ht0.le]; congr 2; ring
      have hpow_1 : t ^ (w - 1) * t ^ (-((w - 1 : ℕ) : ℝ)) = 1 := by
        rw [Real.rpow_neg ht0.le, Real.rpow_natCast, mul_inv_cancel₀ (pow_pos ht0 _).ne']
      calc t ^ (w - 1) * (hη t) ^ 2
          ≤ t ^ (w - 1) * (t ^ (-((w - 1 : ℕ) : ℝ)) * C_band ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (pow_nonneg ht0.le _)
        _ = (t ^ (w - 1) * t ^ (-((w - 1 : ℕ) : ℝ))) * C_band ^ 2 := by ring
        _ = C_band ^ 2 := by rw [hpow_1, one_mul]
    calc ∫ t in Ioc (0 : ℝ) B, t ^ (w - 1) * (hη t) ^ 2
        ≤ ∫ _t in Ioc (0 : ℝ) B, C_band ^ 2 := setIntegral_mono_on hlhs_int hconst_int measurableSet_Ioc hpt
      _ = volume.real (Ioc (0 : ℝ) B) • (C_band ^ 2) := setIntegral_const _
      _ = B * C_band ^ 2 := by rw [smul_eq_mul, Real.volume_real_Ioc_of_le hB_pos.le, sub_zero]
      _ = (Real.sqrt B) ^ 2 * C_band ^ 2 := by rw [Real.sq_sqrt hB_pos.le]
      _ = (Real.sqrt B * C_band) ^ 2 := by rw [← mul_pow]
  have hr_bd : ∀ {t : ℝ}, B < t →
      |r t| ≤ 2 * π * (σ.real univ + μ.real univ) * (t / B₀) ^ (((w - 1 : ℕ) : ℝ) / 2) *
        (min 1 ((2 * π * Real.exp 1 * h * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m) +
          sonineRepairConst * Real.exp (sonineRepairConst * (B + w)) *
            (2 * π * Real.exp 1 * h * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m) := by
    intro t ht
    have ht0 : 0 < t := hB_pos.trans ht
    have hr_term1 : t ^ (w - 1) * |hη t| ≤
        2 * π * (σ.real univ + μ.real univ) * (t / B₀) ^ (((w - 1 : ℕ) : ℝ) / 2) *
          min 1 ((2 * π * Real.exp 1 * h * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m) := by
      have h1' : t ^ (w - 1) * |hη t| ≤
          2 * π * (σ.real univ + μ.real univ) * (t / B₀) ^ (((w - 1 : ℕ) : ℝ) / 2) * 1 := by
        calc t ^ (w - 1) * |hη t|
            ≤ t ^ (w - 1) * (2 * π * (σ.real univ + μ.real univ) * (t * B₀) ^ (-((w - 1 : ℕ) : ℝ) / 2)) :=
              mul_le_mul_of_nonneg_left (hhη_triv ht0) (pow_nonneg ht0.le (w - 1))
          _ = 2 * π * (σ.real univ + μ.real univ) * (t ^ (w - 1) * (t * B₀) ^ (-((w - 1 : ℕ) : ℝ) / 2)) := by ring
          _ = 2 * π * (σ.real univ + μ.real univ) * (t / B₀) ^ (((w - 1 : ℕ) : ℝ) / 2) * 1 := by
              rw [hpow_ratio ht0, mul_one]
      have h2' : t ^ (w - 1) * |hη t| ≤
          2 * π * (σ.real univ + μ.real univ) * (t / B₀) ^ (((w - 1 : ℕ) : ℝ) / 2) *
            (2 * π * Real.exp 1 * h * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m := by
        calc t ^ (w - 1) * |hη t|
            ≤ t ^ (w - 1) * (2 * π * (σ.real univ + μ.real univ) * (t * B₀) ^ (-((w - 1 : ℕ) : ℝ) / 2) *
                (2 * π * Real.exp 1 * h * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m) :=
              mul_le_mul_of_nonneg_left (hhη_tay ht0) (pow_nonneg ht0.le (w - 1))
          _ = 2 * π * (σ.real univ + μ.real univ) * (t ^ (w - 1) * (t * B₀) ^ (-((w - 1 : ℕ) : ℝ) / 2)) *
                (2 * π * Real.exp 1 * h * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m := by ring
          _ = _ := by rw [hpow_ratio ht0]
      have hpref_nn1 : 0 ≤ 2 * π * (σ.real univ + μ.real univ) * (t / B₀) ^ (((w - 1 : ℕ) : ℝ) / 2) :=
        mul_nonneg (mul_nonneg (by positivity) (add_nonneg measureReal_nonneg measureReal_nonneg))
          (Real.rpow_nonneg (div_nonneg ht0.le hB₀.le) _)
      rw [mul_min_of_nonneg _ _ hpref_nn1]
      exact le_min h1' h2'
    have hr_term2 : t ^ (w - 1) * |kerTransform (hankelMeasure w) (hankelKernel w) f₀ t| ≤
        2 * π * (σ.real univ + μ.real univ) * (t / B₀) ^ (((w - 1 : ℕ) : ℝ) / 2) *
          (sonineRepairConst * Real.exp (sonineRepairConst * (B + w)) *
            (2 * π * Real.exp 1 * h * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m) := by
      have hU_sq := rawHankelBand_sq_le hw hB_pos f_L2 ht0
      have hsq_t : Real.sqrt (t ^ (-((w - 1 : ℕ) : ℝ))) = t ^ (-((w - 1 : ℕ) : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht0.le]; congr 1; ring
      have hU_abs : |kerTransform (hankelMeasure w) (hankelKernel w) f₀ t| ≤
          2 * π * Real.sqrt B * t ^ (-((w - 1 : ℕ) : ℝ) / 2) * ‖f_L2‖ := by
        rw [hf_raw_eq t, ← Real.sqrt_sq (abs_nonneg _), sq_abs]
        calc Real.sqrt ((rawHankelBand w B f_L2 t) ^ 2)
            ≤ Real.sqrt ((2 * π) ^ 2 * B * t ^ (-((w - 1 : ℕ) : ℝ)) * ‖f_L2‖ ^ 2) :=
              Real.sqrt_le_sqrt hU_sq
          _ = 2 * π * Real.sqrt B * Real.sqrt (t ^ (-((w - 1 : ℕ) : ℝ))) * ‖f_L2‖ := by
              rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
                Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_sq (norm_nonneg _)]
          _ = 2 * π * Real.sqrt B * t ^ (-((w - 1 : ℕ) : ℝ) / 2) * ‖f_L2‖ := by rw [hsq_t]
      have hf_norm : ‖f_L2‖ ≤ ‖A_inv‖ * ‖hhη_mem.toLp hη‖ :=
        ContinuousLinearMap.le_opNorm A_inv (hhη_mem.toLp hη)
      have hson := sonine_const_absorb w hB_pos
      have hpow_tr : t ^ (w - 1) * t ^ (-((w - 1 : ℕ) : ℝ) / 2) * B₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) =
          (t / B₀) ^ (((w - 1 : ℕ) : ℝ) / 2) := by
        have ht_rpow : t ^ (w - 1) * t ^ (-((w - 1 : ℕ) : ℝ) / 2) = t ^ (((w - 1 : ℕ) : ℝ) / 2) := by
          rw [← Real.rpow_natCast t (w - 1), ← Real.rpow_add ht0]; congr 2; ring
        have hb_inv : B₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) = (B₀ ^ (((w - 1 : ℕ) : ℝ) / 2))⁻¹ := by
          rw [show -((w - 1 : ℕ) : ℝ) / 2 = -(((w - 1 : ℕ) : ℝ) / 2) from by ring, Real.rpow_neg hB₀.le]
        rw [ht_rpow, hb_inv, ← div_eq_mul_inv, Real.div_rpow ht0.le hB₀.le]
      calc t ^ (w - 1) * |kerTransform (hankelMeasure w) (hankelKernel w) f₀ t|
          ≤ t ^ (w - 1) * (2 * π * Real.sqrt B * t ^ (-((w - 1 : ℕ) : ℝ) / 2) * ‖f_L2‖) :=
            mul_le_mul_of_nonneg_left hU_abs (pow_nonneg ht0.le _)
        _ ≤ t ^ (w - 1) * (2 * π * Real.sqrt B * t ^ (-((w - 1 : ℕ) : ℝ) / 2) *
              (‖A_inv‖ * (Real.sqrt B * (2 * π * (σ.real univ + μ.real univ) *
                B₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) *
                (2 * π * Real.exp 1 * h * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m)))) := by
            gcongr; exact hf_norm.trans (mul_le_mul_of_nonneg_left hhη_L2_le (norm_nonneg _))
        _ = 2 * π * (σ.real univ + μ.real univ) *
              (t ^ (w - 1) * t ^ (-((w - 1 : ℕ) : ℝ) / 2) * B₀ ^ (-((w - 1 : ℕ) : ℝ) / 2)) *
              (2 * π * (Real.sqrt B * Real.sqrt B) * ‖A_inv‖) *
              (2 * π * Real.exp 1 * h * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m := by ring
        _ = 2 * π * (σ.real univ + μ.real univ) * (t / B₀) ^ (((w - 1 : ℕ) : ℝ) / 2) *
              (2 * π * B * ‖A_inv‖) *
              (2 * π * Real.exp 1 * h * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m := by
            rw [hpow_tr, Real.mul_self_sqrt hB_pos.le]
        _ ≤ 2 * π * (σ.real univ + μ.real univ) * (t / B₀) ^ (((w - 1 : ℕ) : ℝ) / 2) *
              (2 * π * B * max 4 (2048 * π ^ 2 * B ^ 2 * Real.exp (16 * π * B))) *
              (2 * π * Real.exp 1 * h * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m := by gcongr
        _ ≤ 2 * π * (σ.real univ + μ.real univ) * (t / B₀) ^ (((w - 1 : ℕ) : ℝ) / 2) *
              (sonineRepairConst * Real.exp (sonineRepairConst * (B + w))) *
              (2 * π * Real.exp 1 * h * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m := by gcongr
        _ = _ := by ring
    calc |r t| = |t ^ (w - 1)| * |hη t - kerTransform (hankelMeasure w) (hankelKernel w) f₀ t| := by
          dsimp [r]; exact abs_mul _ _
      _ ≤ t ^ (w - 1) * (|hη t| + |kerTransform (hankelMeasure w) (hankelKernel w) f₀ t|) := by
          rw [abs_of_nonneg (pow_nonneg ht0.le _)]
          exact mul_le_mul_of_nonneg_left (abs_sub _ _) (pow_nonneg ht0.le _)
      _ = t ^ (w - 1) * |hη t| +
            t ^ (w - 1) * |kerTransform (hankelMeasure w) (hankelKernel w) f₀ t| := by ring
      _ ≤ _ := by linarith [hr_term1, hr_term2]
  refine ⟨r, hr_cont.continuousOn, fun {β} hβ => ?_, hr_bd⟩
  have hr_int_exp : IntegrableOn (fun t => Real.exp (-2 * π * β * t) * |r t|) (Ioi B) := by
    let C_exp_bd : ℝ := 2 * π * (σ.real univ + μ.real univ) * B₀ ^ (-(((w - 1 : ℕ) : ℝ) / 2)) *
      (1 + sonineRepairConst * Real.exp (sonineRepairConst * (B + w)) *
        (2 * π * Real.exp 1 * h * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m)
    have h_dom : IntegrableOn (fun t =>
        C_exp_bd * (t ^ (((w - 1 : ℕ) : ℝ) / 2) * Real.exp (-(2 * π * β) * t))) (Ioi 0) :=
      (integrableOn_rpow_mul_exp_rate (by positivity) w).const_mul C_exp_bd
    have h_cont_exp_r : Continuous (fun t => Real.exp (-2 * π * β * t) * |r t|) :=
      (Real.continuous_exp.comp (by fun_prop)).mul (continuous_abs.comp hr_cont)
    refine (h_dom.mono_set (Ioi_subset_Ioi hB_pos.le)).mono' h_cont_exp_r.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htB : B < t := mem_Ioi.mp ht
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))]
    have hmin1 : min 1 ((2 * π * Real.exp 1 * h * Real.sqrt t / ((m : ℝ) * Real.sqrt B₀)) ^ m) ≤ 1 :=
      min_le_left _ _
    have hσμ_nn : 0 ≤ σ.real univ + μ.real univ := add_nonneg measureReal_nonneg measureReal_nonneg
    have hpref_nn : 0 ≤ 2 * π * (σ.real univ + μ.real univ) * (t / B₀) ^ (((w - 1 : ℕ) : ℝ) / 2) :=
      mul_nonneg (mul_nonneg (by positivity) hσμ_nn)
        (Real.rpow_nonneg (div_nonneg (hB_pos.trans htB).le hB₀.le) _)
    have hbd1 : |r t| ≤ 2 * π * (σ.real univ + μ.real univ) * (t / B₀) ^ (((w - 1 : ℕ) : ℝ) / 2) *
        (1 + sonineRepairConst * Real.exp (sonineRepairConst * (B + w)) *
          (2 * π * Real.exp 1 * h * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m) :=
      (hr_bd htB).trans (mul_le_mul_of_nonneg_left (add_le_add hmin1 (le_refl _)) hpref_nn)
    calc Real.exp (-2 * π * β * t) * |r t|
        ≤ Real.exp (-2 * π * β * t) *
            (2 * π * (σ.real univ + μ.real univ) * (t / B₀) ^ (((w - 1 : ℕ) : ℝ) / 2) *
              (1 + sonineRepairConst * Real.exp (sonineRepairConst * (B + w)) *
                (2 * π * Real.exp 1 * h * Real.sqrt B / ((m : ℝ) * Real.sqrt B₀)) ^ m)) := by
          gcongr
      _ = C_exp_bd * (t ^ (((w - 1 : ℕ) : ℝ) / 2) * Real.exp (-(2 * π * β) * t)) := by
          rw [Real.div_rpow (hB_pos.trans htB).le hB₀.le, div_eq_mul_inv, ← Real.rpow_neg hB₀.le]
          dsimp [C_exp_bd]; ring_nf
  refine ⟨hr_int_exp, ?_⟩
  have hm_ae_Ioi : ∀ᵐ t ∂(hankelMeasure w), t ∈ Ioi (0 : ℝ) := ae_iff.mpr (hankelMeasure_Ioi_compl w)
  let g₁_raw : ℝ → ℝ := fun t =>
    2 * π * ((Ioi 0).indicator (fun x => |thermalDiff w β x| * x ^ (-((w - 1 : ℕ) : ℝ) / 2)) t)
  have hg₁_int : Integrable g₁_raw (hankelMeasure w) := by
    rw [integrable_hankelMeasure_iff]
    refine IntegrableOn.congr_fun ((integrableOn_rpow_mul_abs_thermalDiff (w := w) hβ).const_mul (2 * π))
      (fun t ht => ?_) measurableSet_Ioi
    have ht0 := mem_Ioi.mp ht
    dsimp [g₁_raw]
    rw [Set.indicator_of_mem ht]
    have hpow_eq : t ^ (w - 1) * (|thermalDiff w β t| * t ^ (-((w - 1 : ℕ) : ℝ) / 2)) =
        t ^ (((w - 1 : ℕ) : ℝ) / 2) * |thermalDiff w β t| := by
      rw [← Real.rpow_natCast t (w - 1)]
      calc t ^ ((w - 1 : ℕ) : ℝ) * (|thermalDiff w β t| * t ^ (-((w - 1 : ℕ) : ℝ) / 2))
          = (t ^ ((w - 1 : ℕ) : ℝ) * t ^ (-((w - 1 : ℕ) : ℝ) / 2)) * |thermalDiff w β t| := by ring
        _ = t ^ (((w - 1 : ℕ) : ℝ) / 2) * |thermalDiff w β t| := by
            rw [← Real.rpow_add ht0]; congr 2; ring
    calc 2 * π * (t ^ (((w - 1 : ℕ) : ℝ) / 2) * |thermalDiff w β t|)
        = 2 * π * (t ^ (w - 1) * (|thermalDiff w β t| * t ^ (-((w - 1 : ℕ) : ℝ) / 2))) := by
          rw [hpow_eq]
      _ = t ^ (w - 1) * (2 * π * (|thermalDiff w β t| * t ^ (-((w - 1 : ℕ) : ℝ) / 2))) := by ring
  have htd_cont : Continuous (thermalDiff w β) := by unfold thermalDiff; fun_prop
  have hF_meas_ker : Continuous (fun p : ℝ × ℝ => thermalDiff w β p.1 * hankelKernel w p.1 p.2) :=
    (htd_cont.comp continuous_fst).mul (continuous_hankelKernel w)
  have hF_compact : ∀ {η : Measure ℝ} [IsFiniteMeasure η], η (Icc B₀ B)ᶜ = 0 →
      Integrable (fun p : ℝ × ℝ => thermalDiff w β p.1 * hankelKernel w p.1 p.2)
        ((hankelMeasure w).prod η) := by
    intro η _ hηc
    have hprod_dom : Integrable (fun p : ℝ × ℝ => (B₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) * g₁_raw p.1) * (1 : ℝ))
        ((hankelMeasure w).prod η) :=
      (hg₁_int.const_mul _).mul_prod (integrable_const 1)
    have hfst : ∀ᵐ p : ℝ × ℝ ∂((hankelMeasure w).prod η), p.1 ∈ Ioi (0 : ℝ) :=
      Measure.quasiMeasurePreserving_fst.ae hm_ae_Ioi
    have hsnd : ∀ᵐ p : ℝ × ℝ ∂((hankelMeasure w).prod η), p.2 ∈ Icc B₀ B :=
      Measure.quasiMeasurePreserving_snd.ae (ae_iff.mpr hηc)
    refine hprod_dom.mono' hF_meas_ker.aestronglyMeasurable ?_
    filter_upwards [hfst, hsnd] with p hp1 hp2
    have ht0 : 0 < p.1 := mem_Ioi.mp hp1
    have hs0 : 0 < p.2 := hB₀.trans_le hp2.1
    rw [Real.norm_eq_abs, abs_mul]
    have hker := hankelKernel_abs_le w ht0 hs0
    have hpow_ts : (1 / Real.sqrt (p.1 * p.2)) ^ (w - 1) ≤
        B₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) * p.1 ^ (-((w - 1 : ℕ) : ℝ) / 2) := by
      have h1 : (1 / Real.sqrt (p.1 * p.2)) ^ (w - 1) ≤ (1 / Real.sqrt (p.1 * B₀)) ^ (w - 1) := by
        gcongr; exact hp2.1
      have h2 : (1 / Real.sqrt (p.1 * B₀)) ^ (w - 1) =
          B₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) * p.1 ^ (-((w - 1 : ℕ) : ℝ) / 2) := by
        rw [inv_sqrt_prod_rpow w ht0 hB₀, Real.mul_rpow ht0.le hB₀.le]
        ring
      exact h1.trans_eq h2
    calc |thermalDiff w β p.1| * |hankelKernel w p.1 p.2|
        ≤ |thermalDiff w β p.1| * (2 * π * (1 / Real.sqrt (p.1 * p.2)) ^ (w - 1)) := by gcongr
      _ ≤ |thermalDiff w β p.1| *
            (2 * π * (B₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) * p.1 ^ (-((w - 1 : ℕ) : ℝ) / 2))) := by gcongr
      _ = (B₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) * g₁_raw p.1) * 1 := by
          dsimp [g₁_raw]; rw [Set.indicator_of_mem hp1]; ring
  have hF1 : Integrable (fun p : ℝ × ℝ => thermalDiff w β p.1 * hankelKernel w p.1 p.2)
      ((hankelMeasure w).prod σ) := hF_compact hσ
  have hF2 : Integrable (fun p : ℝ × ℝ => thermalDiff w β p.1 * hankelKernel w p.1 p.2)
      ((hankelMeasure w).prod μ) := hF_compact hμ
  have hf_L2_meas : Measurable (f_L2 : ℝ → ℝ) := (Lp.stronglyMeasurable f_L2).measurable
  have hf0_meas : Measurable f₀ := hf_L2_meas.indicator measurableSet_Ioc
  have hg₃_int : Integrable (fun s => (Ioc 0 B).indicator
      (fun y => y ^ (-((w - 1 : ℕ) : ℝ) / 2) * |f₀ y|) s) (hankelMeasure w) := by
    rw [integrable_hankelMeasure_iff]
    have hL2_int : IntegrableOn (fun s => s ^ (w - 1) * (f_L2 s) ^ 2) (Ioc 0 B) :=
      (integrable_hankelBandMeasure_iff _).mp (Lp.memLp f_L2).integrable_sq
    have hdom_band : IntegrableOn (fun s : ℝ => 1 / 2 + 1 / 2 * (s ^ (w - 1) * (f_L2 s) ^ 2)) (Ioc 0 B) :=
      (integrableOn_const (hs := measure_Ioc_lt_top.ne)).add (hL2_int.const_mul _)
    have hdom_Ioi : IntegrableOn (fun s : ℝ =>
        (Ioc 0 B).indicator (fun y => 1 / 2 + 1 / 2 * (y ^ (w - 1) * (f_L2 y) ^ 2)) s) (Ioi 0) :=
      (integrableOn_indicator_iff measurableSet_Ioc.nullMeasurableSet).mpr
        (hdom_band.mono_set inter_subset_left)
    have hmeas_g3 : Measurable (fun s : ℝ => s ^ (w - 1) *
        (Ioc 0 B).indicator (fun y => y ^ (-((w - 1 : ℕ) : ℝ) / 2) * |f₀ y|) s) :=
      (measurable_id.pow_const _).mul
        (((by fun_prop : Measurable fun y : ℝ => y ^ (-((w - 1 : ℕ) : ℝ) / 2)).mul hf0_meas.abs).indicator
          measurableSet_Ioc)
    refine hdom_Ioi.mono' hmeas_g3.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 := mem_Ioi.mp hs
    by_cases hsm : s ∈ Ioc 0 B
    · rw [Set.indicator_of_mem hsm, Set.indicator_of_mem hsm,
        Real.norm_of_nonneg (mul_nonneg (pow_nonneg hs0.le _)
          (mul_nonneg (Real.rpow_nonneg hs0.le _) (abs_nonneg _)))]
      have hf0s : f₀ s = (f_L2 : ℝ → ℝ) s := Set.indicator_of_mem hsm _
      have hsq_eq : (s ^ (((w - 1 : ℕ) : ℝ) / 2) * |f₀ s|) ^ 2 = s ^ (w - 1) * (f_L2 s) ^ 2 := by
        have h2e : (((w - 1 : ℕ) : ℝ) / 2) * ((2 : ℕ) : ℝ) = ((w - 1 : ℕ) : ℝ) := by norm_num
        rw [mul_pow, sq_abs, hf0s, ← Real.rpow_natCast (s ^ (((w - 1 : ℕ) : ℝ) / 2)) 2,
          ← Real.rpow_mul hs0.le, h2e, Real.rpow_natCast]
      have hamgm : s ^ (((w - 1 : ℕ) : ℝ) / 2) * |f₀ s| ≤
          1 / 2 + 1 / 2 * (s ^ (((w - 1 : ℕ) : ℝ) / 2) * |f₀ s|) ^ 2 := by
        nlinarith [sq_nonneg (s ^ (((w - 1 : ℕ) : ℝ) / 2) * |f₀ s| - 1)]
      have hpow_s : s ^ (w - 1) * (s ^ (-((w - 1 : ℕ) : ℝ) / 2) * |f₀ s|) =
          s ^ (((w - 1 : ℕ) : ℝ) / 2) * |f₀ s| := by
        rw [← Real.rpow_natCast s (w - 1), ← mul_assoc, ← Real.rpow_add hs0]
        congr 2; ring
      rw [hpow_s, ← hsq_eq]
      exact hamgm
    · simp [hsm]
  have hF3 : Integrable (fun p : ℝ × ℝ => thermalDiff w β p.1 * (hankelKernel w p.1 p.2 * f₀ p.2))
      ((hankelMeasure w).prod (hankelMeasure w)) := by
    have hprod_dom := hg₁_int.mul_prod hg₃_int
    have hmeas3 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        thermalDiff w β p.1 * (hankelKernel w p.1 p.2 * f₀ p.2))
        ((hankelMeasure w).prod (hankelMeasure w)) := by
      have hm : Measurable (fun p : ℝ × ℝ =>
          (thermalDiff w β p.1 * hankelKernel w p.1 p.2) * f₀ p.2) :=
        hF_meas_ker.measurable.mul (hf0_meas.comp measurable_snd)
      exact hm.aestronglyMeasurable.congr (Eventually.of_forall fun p => by ring)
    have hfst : ∀ᵐ p : ℝ × ℝ ∂((hankelMeasure w).prod (hankelMeasure w)), p.1 ∈ Ioi (0 : ℝ) :=
      Measure.quasiMeasurePreserving_fst.ae hm_ae_Ioi
    refine hprod_dom.mono' hmeas3 ?_
    filter_upwards [hfst] with p hp1
    have ht0 := mem_Ioi.mp hp1
    rw [Real.norm_eq_abs]
    by_cases hp2 : p.2 ∈ Ioc 0 B
    · have hs0 := hp2.1
      rw [abs_mul, abs_mul]
      have hker := hankelKernel_abs_le w ht0 hs0
      have hpow_ts : (1 / Real.sqrt (p.1 * p.2)) ^ (w - 1) =
          p.1 ^ (-((w - 1 : ℕ) : ℝ) / 2) * p.2 ^ (-((w - 1 : ℕ) : ℝ) / 2) := by
        rw [inv_sqrt_prod_rpow w ht0 hs0, Real.mul_rpow ht0.le hs0.le]
      calc |thermalDiff w β p.1| * (|hankelKernel w p.1 p.2| * |f₀ p.2|)
          ≤ |thermalDiff w β p.1| * ((2 * π * (1 / Real.sqrt (p.1 * p.2)) ^ (w - 1)) * |f₀ p.2|) := by
            gcongr
        _ = (2 * π * (|thermalDiff w β p.1| * p.1 ^ (-((w - 1 : ℕ) : ℝ) / 2))) *
              (p.2 ^ (-((w - 1 : ℕ) : ℝ) / 2) * |f₀ p.2|) := by rw [hpow_ts]; ring
        _ = g₁_raw p.1 * (Ioc 0 B).indicator (fun y => y ^ (-((w - 1 : ℕ) : ℝ) / 2) * |f₀ y|) p.2 := by
            dsimp [g₁_raw]; rw [Set.indicator_of_mem hp1, Set.indicator_of_mem hp2]
    · have hf0_zero : f₀ p.2 = 0 := Set.indicator_of_notMem hp2 _
      rw [hf0_zero, mul_zero, mul_zero, abs_zero]
      have hg1_nn : 0 ≤ g₁_raw p.1 := by
        dsimp [g₁_raw]
        refine mul_nonneg (by positivity) (Set.indicator_nonneg (fun x hx => ?_) p.1)
        exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (mem_Ioi.mp hx).le _)
      have hg3_nn : 0 ≤ (Ioc (0 : ℝ) B).indicator
          (fun y => y ^ (-((w - 1 : ℕ) : ℝ) / 2) * |f₀ y|) p.2 := by
        refine Set.indicator_nonneg (fun y hy => ?_) p.2
        exact mul_nonneg (Real.rpow_nonneg hy.1.le _) (abs_nonneg _)
      exact mul_nonneg hg1_nn hg3_nn
  have : SigmaFinite (hankelMeasure w) := sigmaFinite_hankelMeasure w
  have hcross := repair_identity_cross
    (hankelKernel_symm w) (kerTransform_thermalDiff hw hβ) hF1 hF2 hF3
  have hsol : ∀ᵐ t ∂(hankelMeasure w), t ∈ Ioc 0 B →
      f₀ t + kerTransform (hankelMeasure w) (hankelKernel w) f₀ t = hη t := by
    have h_ae_band : (f_L2 : ℝ → ℝ) + (hankelBandOp hw hB_pos f_L2 : ℝ → ℝ) =ᵐ[hankelBandMeasure w B] hη := by
      have hsum : f_L2 + hankelBandOp hw hB_pos f_L2 = hhη_mem.toLp hη := by
        have h1 : (1 + hankelBandOp hw hB_pos) f_L2 = hhη_mem.toLp hη :=
          congrArg (fun L => L (hhη_mem.toLp hη)) hA_right
        simpa [add_apply] using h1
      filter_upwards [Lp.coeFn_add f_L2 (hankelBandOp hw hB_pos f_L2), hhη_mem.coeFn_toLp] with t ht1 ht2
      rw [← ht1, hsum, ht2]
    have h_ae_band2 : ∀ᵐ t ∂(hankelBandMeasure w B),
        f₀ t + kerTransform (hankelMeasure w) (hankelKernel w) f₀ t = hη t := by
      filter_upwards [h_ae_band, hankelBandOp_apply_ae hw hB_pos f_L2,
        ae_restrict_mem measurableSet_Ioc] with t ht1 ht2 htm
      have hf₀t : f₀ t = (f_L2 : ℝ → ℝ) t := Set.indicator_of_mem htm _
      rw [hf₀t, hf_raw_eq t]
      unfold rawHankelBand
      rw [← ht2]
      exact ht1
    exact (ae_restrict_iff' measurableSet_Ioc).mp h_ae_band2
  have hi_dual1 : Integrable (fun t => thermalDiff w β t * ∫ s, hankelKernel w t s ∂σ) (hankelMeasure w) := by
    simpa [integral_const_mul] using hF1.integral_prod_left
  have hi_dual2 : Integrable (fun t => thermalDiff w β t * ∫ s, hankelKernel w t s ∂μ) (hankelMeasure w) := by
    simpa [integral_const_mul] using hF2.integral_prod_left
  have hi_dual3 : Integrable (fun t => thermalDiff w β t *
      kerTransform (hankelMeasure w) (hankelKernel w) f₀ t) (hankelMeasure w) := by
    simpa [kerTransform, integral_const_mul] using hF3.integral_prod_left
  have hi_dual : Integrable (fun t => thermalDiff w β t *
      (hη t - kerTransform (hankelMeasure w) (hankelKernel w) f₀ t)) (hankelMeasure w) := by
    have heq : (fun t => thermalDiff w β t *
        (hη t - kerTransform (hankelMeasure w) (hankelKernel w) f₀ t)) =
        fun t => (thermalDiff w β t * ∫ s, hankelKernel w t s ∂σ -
          thermalDiff w β t * ∫ s, hankelKernel w t s ∂μ) -
          thermalDiff w β t * kerTransform (hankelMeasure w) (hankelKernel w) f₀ t := by
      ext t; dsimp [hη, kerDual]; ring
    rw [heq]
    exact (hi_dual1.sub hi_dual2).sub hi_dual3
  have hi_f : Integrable (fun s => thermalDiff w β s * f₀ s) (hankelMeasure w) := by
    rw [integrable_hankelMeasure_iff]
    obtain ⟨t₁, _, ht₁⟩ := isCompact_Icc.exists_isMaxOn ⟨0, left_mem_Icc.mpr hB_pos.le⟩
      htd_cont.abs.continuousOn
    let M_g : ℝ := |thermalDiff w β t₁|
    have hg_bd : ∀ s ∈ Ioc 0 B, |thermalDiff w β s| ≤ M_g := fun s hs => ht₁ ⟨hs.1.le, hs.2⟩
    have hg3_Ioi : IntegrableOn (fun s => s ^ (w - 1) * ((Ioc 0 B).indicator
        (fun y => y ^ (-((w - 1 : ℕ) : ℝ) / 2) * |f₀ y|) s)) (Ioi 0) :=
      (integrable_hankelMeasure_iff _).mp hg₃_int
    have hdom_f : IntegrableOn (fun s => (B ^ (((w - 1 : ℕ) : ℝ) / 2) * M_g) *
        (s ^ (w - 1) * ((Ioc 0 B).indicator
          (fun y => y ^ (-((w - 1 : ℕ) : ℝ) / 2) * |f₀ y|) s))) (Ioi 0) :=
      hg3_Ioi.const_mul _
    have hmeas_f : Measurable (fun s : ℝ => s ^ (w - 1) * (thermalDiff w β s * f₀ s)) :=
      (measurable_id.pow_const _).mul (htd_cont.measurable.mul hf0_meas)
    refine hdom_f.mono' hmeas_f.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 := mem_Ioi.mp hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hs0.le _)]
    by_cases hsm : s ∈ Ioc 0 B
    · rw [Set.indicator_of_mem hsm, abs_mul]
      have hpow_sB : s ^ (((w - 1 : ℕ) : ℝ) / 2) ≤ B ^ (((w - 1 : ℕ) : ℝ) / 2) :=
        Real.rpow_le_rpow hs0.le hsm.2 (by positivity)
      have hsplit : s ^ (w - 1) =
          s ^ (((w - 1 : ℕ) : ℝ) / 2) * (s ^ (w - 1) * s ^ (-((w - 1 : ℕ) : ℝ) / 2)) := by
        rw [← Real.rpow_natCast s (w - 1), ← mul_assoc, ← Real.rpow_add hs0,
          ← Real.rpow_add hs0]
        congr 2; ring
      calc s ^ (w - 1) * (|thermalDiff w β s| * |f₀ s|)
          = s ^ (((w - 1 : ℕ) : ℝ) / 2) * |thermalDiff w β s| *
              (s ^ (w - 1) * (s ^ (-((w - 1 : ℕ) : ℝ) / 2) * |f₀ s|)) := by
            conv_lhs => rw [hsplit]
            ring
        _ ≤ (B ^ (((w - 1 : ℕ) : ℝ) / 2) * M_g) *
              (s ^ (w - 1) * (s ^ (-((w - 1 : ℕ) : ℝ) / 2) * |f₀ s|)) := by
            gcongr
            exact hg_bd s hsm
    · have hf0_zero : f₀ s = 0 := Set.indicator_of_notMem hsm _
      simp [hf0_zero, hsm]
  have hsplit_dual := integral_add_compl (measurableSet_Ioc (a := (0 : ℝ)) (b := B)) hi_dual
  have hsplit_f := integral_add_compl (measurableSet_Ioc (a := (0 : ℝ)) (b := B)) hi_f
  have hband_match :
      ∫ t in Ioc 0 B, thermalDiff w β t * (hη t - kerTransform (hankelMeasure w) (hankelKernel w) f₀ t) ∂(hankelMeasure w) =
        ∫ s in Ioc 0 B, thermalDiff w β s * f₀ s ∂(hankelMeasure w) := by
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    filter_upwards [hsol] with t htm ht_mem
    have ht_eq := htm ht_mem
    congr 1
    linarith
  have hcompl_f : ∫ s in (Ioc (0 : ℝ) B)ᶜ, thermalDiff w β s * f₀ s ∂(hankelMeasure w) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
    dsimp [f₀]; rw [Set.indicator_of_notMem hs, mul_zero]
  have hcompl_tail :
      ∫ t in (Ioc (0 : ℝ) B)ᶜ, thermalDiff w β t *
          (hη t - kerTransform (hankelMeasure w) (hankelKernel w) f₀ t) ∂(hankelMeasure w) =
        ∫ t in Ioi B, thermalDiff w β t * r t := by
    rw [← integral_indicator measurableSet_Ioc.compl, integral_hankelMeasure_eq,
      ← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    congr 1; ext t
    by_cases htB : B < t
    · have ht0 : 0 < t := hB_pos.trans htB
      have htc : t ∈ (Ioc (0 : ℝ) B)ᶜ := fun h => not_le_of_gt htB h.2
      rw [Set.indicator_of_mem ht0, Set.indicator_of_mem htc, Set.indicator_of_mem htB]
      dsimp [r]; ring
    · conv_rhs => rw [Set.indicator_of_notMem htB]
      by_cases ht0 : 0 < t
      · have hmem : t ∈ Ioc (0 : ℝ) B := ⟨ht0, not_lt.mp htB⟩
        rw [Set.indicator_of_mem ht0, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hmem), mul_zero]
      · rw [Set.indicator_of_notMem ht0]
  have hcross' :
      ∫ s, thermalDiff w β s ∂σ - ∫ s, thermalDiff w β s ∂μ -
        ∫ s, thermalDiff w β s * f₀ s ∂(hankelMeasure w) +
        ∫ t, thermalDiff w β t * (hη t - kerTransform (hankelMeasure w) (hankelKernel w) f₀ t) ∂(hankelMeasure w) = 0 := by
    simpa [hη, repairPairing] using hcross
  have h0 :
      ∫ s, thermalDiff w β s ∂σ - ∫ s, thermalDiff w β s ∂μ +
        ∫ t in Ioi B, thermalDiff w β t * r t =
        ∫ s, thermalDiff w β s ∂σ - ∫ s, thermalDiff w β s ∂μ -
          ∫ s, thermalDiff w β s * f₀ s ∂(hankelMeasure w) +
          ∫ t, thermalDiff w β t * (hη t - kerTransform (hankelMeasure w) (hankelKernel w) f₀ t) ∂(hankelMeasure w) := by
    have hD := hsplit_dual.symm
    have hF : ∫ s, thermalDiff w β s * f₀ s ∂(hankelMeasure w) =
        ∫ s in Ioc 0 B, thermalDiff w β s * f₀ s ∂(hankelMeasure w) := by
      rw [← hsplit_f, hcompl_f, add_zero]
    rw [← hcompl_tail, hD, hF, hband_match]; ring
  rw [h0]; exact hcross'

/-- info: 'FormalResearch.ModularBootstrap.Integrality.hankel_repair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_repair

end FormalResearch.ModularBootstrap.Integrality
