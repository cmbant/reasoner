module

public import FormalResearch.ModularBootstrap.Spin.SpinMomentPair
public import FormalResearch.ModularBootstrap.Upper.Assembly.BumpedDesignWindow
public import FormalResearch.ModularBootstrap.Upper.Positivity.AmplitudeLevel
public import FormalResearch.ModularBootstrap.Upper.Window.TailBand
public import FormalResearch.ModularBootstrap.Upper.Ramped.LangerTauSpec

/-!
# SPIN-M part 3a: Cardy asymptotics and vacuum-source limit

Formalises the Cardy ratios and vacuum-source limit in
`CFT/modular_bootstrap/paper/spinning_airy_moment_proof.tex` (`sd:spinmoment-proof-sec`):

* **Section 1 (`sd:spinmoment-Cardy`)**: uniform Cardy asymptotics of `spinVacuumD`, `spinVacHC`,
  and the ratios `spinVacHC / (2π c virasoroProblem.cardyV) → x³/(3π)`,
  `kernelK 5 / virasoroProblem.cardyV`, and `kernelK 5(a, t) / kernelK 5(a, t + z) → e^{-π z / ξ_*}`.
* **Section 2 (`sd:spinmoment-ref-limit`)**: left-lobe exponential bound (`0 ≤ x ≤ ξ_*/2` via
  `lobe_upper_K6b_blaschke` + `neg_majorant_add_slitL_eq`), `ĥ₅ H_C` bound (`O(c)` via
  `StripContinuation.vacuum_kernel`), and the vacuum-source upper limit
  `limsup (π c C_* FKc 1 1 c)⁻¹ ∫ g₅ H_C ≤ (v_*/2) V_D`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Design
open FormalResearch.ModularBootstrap.Upper.Holes
open FormalResearch.ModularBootstrap.Upper.Membership
open FormalResearch.ModularBootstrap.Upper.Positivity
open FormalResearch.ModularBootstrap.Upper.Bump
open FormalResearch.ModularBootstrap.Upper.Ramped
open FormalResearch.ModularBootstrap.Upper.Window
open FormalResearch.ModularBootstrap.Upper.Window.Cardy
open FormalResearch.ModularBootstrap.Upper.Window.Tail
open FormalResearch.ModularBootstrap.Upper.Assembly
open FormalResearch.ModularBootstrap.Upper.Rigidity
open FormalResearch.ModularBootstrap.WeightAxioms

/-! ### Section 1: Cardy asymptotics (`sd:spinmoment-Cardy`) -/

private def zeroShiftProb (w : ℕ) (hw : 1 ≤ w) : FixedWeightProblem where
  w := w
  hw := hw
  m := 0
  μ := fun l => Fin.elim0 l
  hμ := fun l => Fin.elim0 l

private lemma zeroShiftProb_totalShift (w : ℕ) (hw : 1 ≤ w) :
    (zeroShiftProb w hw).totalShift = 0 := by
  simp [FixedWeightProblem.totalShift, zeroShiftProb, Finset.sum_eq_zero (fun l _ => Fin.elim0 l)]

private lemma zeroShiftProb_nullPoly (w : ℕ) (hw : 1 ≤ w) (q : ℝ) :
    (zeroShiftProb w hw).nullPoly q = 1 := by
  simp [FixedWeightProblem.nullPoly, zeroShiftProb, Finset.prod_eq_one (fun l _ => Fin.elim0 l)]

private lemma zeroShiftProb_cardyV (w : ℕ) (hw : 1 ≤ w) (a t : ℝ) :
    (zeroShiftProb w hw).cardyV a t = kernelK w a t := by
  unfold FixedWeightProblem.cardyV FixedWeightProblem.shiftSum zeroShiftProb
  rw [Finset.sum_eq_single (∅ : Finset (Fin 0))]
  · simp
  · intro s _ hs; exfalso; exact hs (Finset.eq_empty_of_forall_notMem fun x _ => Fin.elim0 x)
  · intro h; exact absurd (Finset.mem_univ _) h

private def oneShiftProb (w : ℕ) (hw : 1 ≤ w) (r : ℝ) (hr : 0 < r) : FixedWeightProblem where
  w := w
  hw := hw
  m := 1
  μ := fun _ => r
  hμ := fun _ => hr

private lemma oneShiftProb_totalShift (w : ℕ) (hw : 1 ≤ w) (r : ℝ) (hr : 0 < r) :
    (oneShiftProb w hw r hr).totalShift = r := by
  unfold FixedWeightProblem.totalShift oneShiftProb
  change (Finset.univ : Finset (Fin 1)).sum (fun _ => r) = r
  simp

private lemma oneShiftProb_nullPoly (w : ℕ) (hw : 1 ≤ w) (r : ℝ) (hr : 0 < r) (q : ℝ) :
    (oneShiftProb w hw r hr).nullPoly q = 1 - q ^ r := by
  unfold FixedWeightProblem.nullPoly oneShiftProb
  change (Finset.univ : Finset (Fin 1)).prod (fun _ => 1 - q ^ r) = 1 - q ^ r
  simp

private lemma oneShiftProb_cardyV (w : ℕ) (hw : 1 ≤ w) (r : ℝ) (hr : 0 < r) (a t : ℝ) :
    (oneShiftProb w hw r hr).cardyV a t = kernelK w a t - kernelK w (a - r) t := by
  unfold FixedWeightProblem.cardyV FixedWeightProblem.shiftSum oneShiftProb
  change ∑ s : Finset (Fin 1), (-1 : ℝ) ^ s.card * kernelK w (a - ∑ _l ∈ s, r) t =
    kernelK w a t - kernelK w (a - r) t
  have h01 : ∀ s : Finset (Fin 1), s = ∅ ∨ s = {0} := fun s => by
    by_cases h : (0 : Fin 1) ∈ s
    · right; ext i; rw [Fin.fin_one_eq_zero i]; simp [h]
    · left; ext i; rw [Fin.fin_one_eq_zero i]; simp [h]
  rw [Fintype.sum_eq_add (∅ : Finset (Fin 1)) ({0} : Finset (Fin 1)) (by decide)
    (fun s hs => by
      rcases h01 s with rfl | rfl
      · exact absurd rfl hs.1
      · exact absurd rfl hs.2)]
  simp [sub_eq_add_neg]

/-- Uniform real Cardy asymptotic for `spinVacuumD w (c'/12 - r) (c' x²/3)` (`r ≥ 0`, `x ≥ x₀ > 0`). -/
theorem spinVacuumD_asymptotic_real (w : ℕ) (hw : 1 ≤ w) {r : ℝ} (hr : 0 ≤ r) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c' x : ℝ}, max 1 (24 * r) ≤ c' → x₀ ≤ x →
      |spinVacuumD w (c' / 12 - r) (c' * x ^ 2 / 3) /
          (2 * π * (2 * x) ^ (w - 1) * Bessel.besselAs (c' * (2 * π * x / 3))) -
        Real.exp (-4 * π * r * x)| ≤ C / c' := by
  have h0 := cardyV_asymptotic_real (zeroShiftProb w hw) hx₀
  rcases eq_or_lt_of_le hr with rfl | hrpos
  · obtain ⟨C, hC0, hC⟩ := h0
    refine ⟨C, hC0, fun {c' x} hc' hx => ?_⟩
    have hc0' : max 1 (24 * (zeroShiftProb w hw).totalShift) ≤ c' := by
      rw [zeroShiftProb_totalShift]; simpa using hc'
    have h1 := hC hc0' hx
    have hw' : (zeroShiftProb w hw).w = w := rfl
    rw [zeroShiftProb_cardyV, zeroShiftProb_nullPoly, hw'] at h1
    have hrw : spinVacuumD w (c' / 12 - 0) (c' * x ^ 2 / 3) /
          (2 * π * (2 * x) ^ (w - 1) * Bessel.besselAs (c' * (2 * π * x / 3))) =
        kernelK w (c' / 12) (c' * x ^ 2 / 3) /
          ((2 * x) ^ (w - 1) * Bessel.besselAs (c' * (2 * π * x / 3))) := by
      unfold spinVacuumD; rw [sub_zero]; field_simp [Real.pi_ne_zero]
    rw [hrw]
    simpa using h1
  · obtain ⟨C₀, hC₀, h0'⟩ := h0
    obtain ⟨C₁, hC₁, h1'⟩ := cardyV_asymptotic_real (oneShiftProb w hw r hrpos) hx₀
    refine ⟨C₀ + C₁, add_nonneg hC₀ hC₁, fun {c' x} hc' hx => ?_⟩
    have hc1_le : 1 ≤ c' := (le_max_left _ _).trans hc'
    have hc0 : max 1 (24 * (zeroShiftProb w hw).totalShift) ≤ c' := by
      rw [zeroShiftProb_totalShift, mul_zero]; exact max_le hc1_le (by linarith)
    have hc1 : max 1 (24 * (oneShiftProb w hw r hrpos).totalShift) ≤ c' := by
      rw [oneShiftProb_totalShift]; exact hc'
    have e0 := h0' hc0 hx
    have e1 := h1' hc1 hx
    have hw' : (zeroShiftProb w hw).w = w := rfl
    have hw1' : (oneShiftProb w hw r hrpos).w = w := rfl
    rw [zeroShiftProb_cardyV, zeroShiftProb_nullPoly, hw'] at e0
    rw [oneShiftProb_cardyV, oneShiftProb_nullPoly, hw1'] at e1
    have hsub : spinVacuumD w (c' / 12 - r) (c' * x ^ 2 / 3) /
          (2 * π * (2 * x) ^ (w - 1) * Bessel.besselAs (c' * (2 * π * x / 3))) -
        Real.exp (-4 * π * r * x) =
      (kernelK w (c' / 12) (c' * x ^ 2 / 3) / ((2 * x) ^ (w - 1) * Bessel.besselAs (c' * (2 * π * x / 3))) - 1) -
      ((kernelK w (c' / 12) (c' * x ^ 2 / 3) - kernelK w (c' / 12 - r) (c' * x ^ 2 / 3)) /
        ((2 * x) ^ (w - 1) * Bessel.besselAs (c' * (2 * π * x / 3))) -
        (1 - (Real.exp (-4 * π * x)) ^ r)) := by
      have hrw : (Real.exp (-4 * π * x)) ^ r = Real.exp (-4 * π * r * x) := by
        rw [← Real.exp_mul]; ring_nf
      rw [hrw]
      unfold spinVacuumD
      have hden : 2 * π * ((2 * x) ^ (w - 1) * Bessel.besselAs (c' * (2 * π * x / 3))) =
          2 * π * (2 * x) ^ (w - 1) * Bessel.besselAs (c' * (2 * π * x / 3)) := by ring
      rw [← hden, mul_div_mul_left _ _ (by positivity : 2 * π ≠ 0)]
      ring
    rw [hsub]
    calc |(_ - _) - (_ - _)| ≤ |_| + |_| := abs_sub _ _
      _ ≤ C₀ / c' + C₁ / c' := add_le_add e0 e1
      _ = (C₀ + C₁) / c' := (add_div C₀ C₁ c').symm

private lemma spinVacuumD_div_as_le (w : ℕ) {r C c' x X : ℝ} (hC : 0 ≤ C) (hc1 : 1 ≤ c')
    (ha : 0 ≤ c' / 12 - r) (hx0 : 0 < x) (hxX : x ≤ X)
    (hbd : |spinVacuumD w (c' / 12 - r) (c' * x ^ 2 / 3) /
        (2 * π * (2 * x) ^ (w - 1) * Bessel.besselAs (c' * (2 * π * x / 3))) -
        Real.exp (-4 * π * r * x)| ≤ C / c') (hr : 0 ≤ r) :
    |spinVacuumD w (c' / 12 - r) (c' * x ^ 2 / 3) /
        (2 * π * Bessel.besselAs (c' * (2 * π * x / 3)))| ≤ (2 * X) ^ (w - 1) * (1 + C) := by
  let As : ℝ := Bessel.besselAs (c' * (2 * π * x / 3))
  have hAs : 0 < As := Bessel.besselAs_pos (by positivity)
  have hnn : 0 ≤ spinVacuumD w (c' / 12 - r) (c' * x ^ 2 / 3) / (2 * π * As) :=
    div_nonneg (spinVacuumD_nonneg ha (by positivity)) (by positivity)
  have hexp : Real.exp (-4 * π * r * x) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := Real.pi_pos; nlinarith [mul_nonneg hr hx0.le])
  have hCc : C / c' ≤ C := div_le_self hC hc1
  have hup : spinVacuumD w (c' / 12 - r) (c' * x ^ 2 / 3) /
      (2 * π * (2 * x) ^ (w - 1) * As) ≤ 1 + C := by linarith [(abs_le.mp hbd).2]
  have hid : spinVacuumD w (c' / 12 - r) (c' * x ^ 2 / 3) / (2 * π * As) =
      (2 * x) ^ (w - 1) * (spinVacuumD w (c' / 12 - r) (c' * x ^ 2 / 3) /
        (2 * π * (2 * x) ^ (w - 1) * As)) := by
    field_simp [Real.pi_ne_zero, hAs.ne', (by positivity : (2 * x) ^ (w - 1) ≠ 0)]
  have hXpow : (2 * x) ^ (w - 1) ≤ (2 * X) ^ (w - 1) :=
    pow_le_pow_left₀ (by positivity) (by linarith) (w - 1)
  have hXpos : 0 < X := hx0.trans_le hxX
  have hup_nn : 0 ≤ spinVacuumD w (c' / 12 - r) (c' * x ^ 2 / 3) /
      (2 * π * (2 * x) ^ (w - 1) * As) :=
    div_nonneg (spinVacuumD_nonneg ha (by positivity)) (by positivity)
  rw [abs_of_nonneg hnn, hid]
  exact mul_le_mul hXpow hup hup_nn (by positivity)

private lemma spinVacuumD4_diff_le {r C c' x X : ℝ} (hcpos : 0 < c')
    (hx0 : 0 < x) (hxX : x ≤ X)
    (hbd : |spinVacuumD 4 (c' / 12 - r) (c' * x ^ 2 / 3) /
        (2 * π * (2 * x) ^ (4 - 1) * Bessel.besselAs (c' * (2 * π * x / 3))) -
        Real.exp (-4 * π * r * x)| ≤ C / c') :
    |spinVacuumD 4 (c' / 12 - r) (c' * x ^ 2 / 3) /
        (2 * π * Bessel.besselAs (c' * (2 * π * x / 3))) -
        (2 * x) ^ 3 * Real.exp (-4 * π * r * x)| ≤ (2 * X) ^ 3 * (C / c') := by
  let As : ℝ := Bessel.besselAs (c' * (2 * π * x / 3))
  have hAs : 0 < As := Bessel.besselAs_pos (by positivity)
  have hXpos : 0 < X := hx0.trans_le hxX
  have hCc_nn : 0 ≤ C / c' := (abs_nonneg _).trans hbd
  have hX3 : (2 * x) ^ 3 ≤ (2 * X) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hmul : |(2 * x) ^ 3 * (spinVacuumD 4 (c' / 12 - r) (c' * x ^ 2 / 3) /
      (2 * π * (2 * x) ^ (4 - 1) * As) - Real.exp (-4 * π * r * x))| ≤ (2 * x) ^ 3 * (C / c') := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left hbd (by positivity)
  have hid : (2 * x) ^ 3 * (spinVacuumD 4 (c' / 12 - r) (c' * x ^ 2 / 3) /
      (2 * π * (2 * x) ^ (4 - 1) * As) - Real.exp (-4 * π * r * x)) =
      spinVacuumD 4 (c' / 12 - r) (c' * x ^ 2 / 3) / (2 * π * As) -
        (2 * x) ^ 3 * Real.exp (-4 * π * r * x) := by
    rw [show (4 - 1 : ℕ) = 3 by rfl]
    field_simp [Real.pi_ne_zero, hAs.ne']
  rw [hid] at hmul
  exact hmul.trans (mul_le_mul_of_nonneg_right hX3 hCc_nn)

/-- Asymptotic `(sd:spinmoment-Cardy)`: uniformly for `x ∈ [x₀, X]` (`0 < x₀`),
`H_C(c' x²/3) / (2π c' V_vir(c'/12, c' x²/3)) → x³/(3π)` with rate `O_X(1/c')`. -/
theorem spinVacHC_div_cardy_bound {x₀ X : ℝ} (hx₀ : 0 < x₀) (hX : x₀ ≤ X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ c' in atTop, ∀ x ∈ Icc x₀ X,
      |spinVacHC (c' / 12) (c' * x ^ 2 / 3) /
          (2 * π * c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3)) -
        x ^ 3 / (3 * π)| ≤ C / c' := by
  have hXpos : 0 < X := hx₀.trans_le hX
  obtain ⟨C40, hC40, h40⟩ := spinVacuumD_asymptotic_real 4 (by norm_num) (r := 0) le_rfl hx₀
  obtain ⟨C41, hC41, h41⟩ := spinVacuumD_asymptotic_real 4 (by norm_num) (r := 1) zero_le_one hx₀
  obtain ⟨C42, hC42, h42⟩ := spinVacuumD_asymptotic_real 4 (by norm_num) (r := 2) (by norm_num) hx₀
  obtain ⟨C30, hC30, h30⟩ := spinVacuumD_asymptotic_real 3 (by norm_num) (r := 0) le_rfl hx₀
  obtain ⟨C31, hC31, h31⟩ := spinVacuumD_asymptotic_real 3 (by norm_num) (r := 1) zero_le_one hx₀
  obtain ⟨C32, hC32, h32⟩ := spinVacuumD_asymptotic_real 3 (by norm_num) (r := 2) (by norm_num) hx₀
  obtain ⟨C51, hC51, h51⟩ := spinVacuumD_asymptotic_real 5 (by norm_num) (r := 1) zero_le_one hx₀
  obtain ⟨Cv, hCv, hv⟩ := cardyV_asymptotic_real virasoroProblem hx₀
  have hQmin : 0 < (1 - Real.exp (-4 * π * x₀)) ^ 2 := by
    have : Real.exp (-4 * π * x₀) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
    exact sq_pos_of_pos (sub_pos.mpr this)
  let qmin : ℝ := (1 - Real.exp (-4 * π * x₀)) ^ 2
  let M4 : ℝ := (2 * X) ^ 3 * (C40 + 2 * C41 + C42)
  let B3 : ℝ := (2 * X) ^ 2 * (1 + C30) + 2 * ((2 * X) ^ 2 * (1 + C31)) + (2 * X) ^ 2 * (1 + C32)
  let B4 : ℝ := 2 * ((2 * X) ^ 3 * (1 + C41)) + 2 * ((2 * X) ^ 3 * (1 + C42))
  let B5 : ℝ := 2 * ((2 * X) ^ 4 * (1 + C51))
  let Mrem : ℝ := M4 / (24 * π) + B3 / (8 * π ^ 2) + B4 / (2 * π) + B5
  let Ctot : ℝ := (Mrem + (X ^ 3 / (3 * π)) * Cv) / (qmin / 2)
  have hMrem_nn : 0 ≤ Mrem := by dsimp [Mrem, M4, B3, B4, B5]; positivity
  refine ⟨Ctot, by dsimp [Ctot, qmin]; positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (48 : ℝ), eventually_ge_atTop (2 * Cv / qmin + 1),
    eventually_ge_atTop (24 * virasoroProblem.totalShift)] with c' hc48 hcCv hcS x hx
  have hxpos : 0 < x := lt_of_lt_of_le hx₀ hx.1
  have hc1 : 1 ≤ c' := by linarith
  have hcpos : 0 < c' := by linarith
  have hV := hv (max_le hc1 hcS) hx.1
  rw [virasoroProblem_nullPoly] at hV
  have hq_lo : qmin ≤ (1 - Real.exp (-4 * π * x)) ^ 2 := by
    have h1 : Real.exp (-4 * π * x) ≤ Real.exp (-4 * π * x₀) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hx.1])
    have h2 : 0 ≤ 1 - Real.exp (-4 * π * x₀) := by
      have : Real.exp (-4 * π * x₀) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
      linarith
    exact pow_le_pow_left₀ h2 (by linarith) 2
  let As : ℝ := Bessel.besselAs (c' * (2 * π * x / 3))
  have hAs : 0 < As := Bessel.besselAs_pos (by positivity)
  have hVv_pos : 0 < virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) :=
    virasoroProblem.cardyV_pos (by linarith [virasoroProblem_totalShift]) (by positivity)
  have hden_eq : (2 * x) ^ (virasoroProblem.w - 1) * As = As := by simp [virasoroProblem]
  have hQ_ge : qmin / 2 ≤ virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) / As := by
    have hCv_le : Cv / c' ≤ qmin / 2 := by
      rw [div_le_iff₀ hcpos]
      have hle : 2 * Cv / qmin ≤ c' := by linarith
      rw [div_le_iff₀ hQmin] at hle; nlinarith
    have hlow := (abs_le.mp hV).1
    rw [hden_eq] at hlow
    linarith
  have e40 := h40 (max_le hc1 (by linarith)) hx.1
  have e41 := h41 (max_le hc1 (by linarith)) hx.1
  have e42 := h42 (max_le hc1 (by linarith)) hx.1
  have e30 := h30 (max_le hc1 (by linarith)) hx.1
  have e31 := h31 (max_le hc1 (by linarith)) hx.1
  have e32 := h32 (max_le hc1 (by linarith)) hx.1
  have e51 := h51 (max_le hc1 (by linarith)) hx.1
  let D4r : ℕ → ℝ := fun k => spinVacuumD 4 (c' / 12 - k) (c' * x ^ 2 / 3) / (2 * π * As)
  let D3r : ℕ → ℝ := fun k => spinVacuumD 3 (c' / 12 - k) (c' * x ^ 2 / 3) / (2 * π * As)
  let D5r : ℝ := spinVacuumD 5 (c' / 12 - 1) (c' * x ^ 2 / 3) / (2 * π * As)
  have hr40 : |D4r 0 - (2 * x) ^ 3| ≤ (2 * X) ^ 3 * (C40 / c') := by
    simpa [D4r, As] using spinVacuumD4_diff_le hcpos hxpos hx.2 e40
  have hr41 : |D4r 1 - (2 * x) ^ 3 * Real.exp (-4 * π * x)| ≤ (2 * X) ^ 3 * (C41 / c') := by
    simpa [D4r, As] using spinVacuumD4_diff_le hcpos hxpos hx.2 e41
  have hr42 : |D4r 2 - (2 * x) ^ 3 * Real.exp (-8 * π * x)| ≤ (2 * X) ^ 3 * (C42 / c') := by
    have h42' := spinVacuumD4_diff_le hcpos hxpos hx.2 e42
    rw [show -4 * π * (2 : ℝ) * x = -8 * π * x by ring] at h42'
    exact h42'
  have hD30 := spinVacuumD_div_as_le 3 hC30 hc1 (by linarith) hxpos hx.2 e30 le_rfl
  have hD31 := spinVacuumD_div_as_le 3 hC31 hc1 (by linarith) hxpos hx.2 e31 zero_le_one
  have hD32 := spinVacuumD_div_as_le 3 hC32 hc1 (by linarith) hxpos hx.2 e32 (by norm_num)
  have hD41 := spinVacuumD_div_as_le 4 hC41 hc1 (by linarith) hxpos hx.2 e41 zero_le_one
  have hD42 := spinVacuumD_div_as_le 4 hC42 hc1 (by linarith) hxpos hx.2 e42 (by norm_num)
  have hD51 := spinVacuumD_div_as_le 5 hC51 hc1 (by linarith) hxpos hx.2 e51 zero_le_one
  have hexp_poly : (1 - Real.exp (-4 * π * x)) ^ 2 = 1 - 2 * Real.exp (-4 * π * x) + Real.exp (-8 * π * x) := by
    have : Real.exp (-4 * π * x) ^ 2 = Real.exp (-8 * π * x) := by rw [← Real.exp_nat_mul]; ring_nf
    linarith [show (1 - Real.exp (-4 * π * x)) ^ 2 = 1 - 2 * Real.exp (-4 * π * x) + Real.exp (-4 * π * x) ^ 2 by ring]
  have hidHC : spinVacHC (c' / 12) (c' * x ^ 2 / 3) / (2 * π * c' * As) =
      ((D4r 0 - 2 * D4r 1 + D4r 2) / (24 * π)) +
      ((D3r 0 - 2 * D3r 1 + D3r 2) / (8 * π ^ 2 * c') +
        (2 * D4r 1 - 2 * D4r 2) / (2 * π * c') - 2 * D5r / c') := by
    unfold spinVacHC spinVacB
    dsimp [D4r, D3r, D5r]
    simp only [Nat.cast_zero, sub_zero, Nat.cast_one]
    field_simp [Real.pi_ne_zero, hcpos.ne', hAs.ne']
    ring
  have hmain4 : |(D4r 0 - 2 * D4r 1 + D4r 2) / (24 * π) - (x ^ 3 / (3 * π)) * (1 - Real.exp (-4 * π * x)) ^ 2| ≤
      M4 / (24 * π) / c' := by
    have hid4 : (D4r 0 - 2 * D4r 1 + D4r 2) / (24 * π) - (x ^ 3 / (3 * π)) * (1 - Real.exp (-4 * π * x)) ^ 2 =
        ((D4r 0 - (2 * x) ^ 3) - 2 * (D4r 1 - (2 * x) ^ 3 * Real.exp (-4 * π * x)) +
          (D4r 2 - (2 * x) ^ 3 * Real.exp (-8 * π * x))) / (24 * π) := by
      rw [hexp_poly]; field_simp [Real.pi_ne_zero]; ring
    rw [hid4, abs_div, abs_of_pos (show 0 < 24 * π by positivity)]
    have hnum4 : |(D4r 0 - (2 * x) ^ 3) - 2 * (D4r 1 - (2 * x) ^ 3 * Real.exp (-4 * π * x)) +
        (D4r 2 - (2 * x) ^ 3 * Real.exp (-8 * π * x))| ≤ M4 / c' := by
      have ha1 := abs_add_le (D4r 0 - (2 * x) ^ 3 - 2 * (D4r 1 - (2 * x) ^ 3 * Real.exp (-4 * π * x)))
        (D4r 2 - (2 * x) ^ 3 * Real.exp (-8 * π * x))
      have ha2 := abs_sub (D4r 0 - (2 * x) ^ 3) (2 * (D4r 1 - (2 * x) ^ 3 * Real.exp (-4 * π * x)))
      rw [abs_mul, show |(2 : ℝ)| = 2 by norm_num] at ha2
      have hM4_eq : (2 * X) ^ 3 * (C40 / c') + 2 * ((2 * X) ^ 3 * (C41 / c')) + (2 * X) ^ 3 * (C42 / c') = M4 / c' := by
        dsimp [M4]; ring
      linarith
    calc _ ≤ (M4 / c') / (24 * π) := div_le_div_of_nonneg_right hnum4 (by positivity)
      _ = M4 / (24 * π) / c' := by ring
  have hrem_bd : |(D3r 0 - 2 * D3r 1 + D3r 2) / (8 * π ^ 2 * c') +
      (2 * D4r 1 - 2 * D4r 2) / (2 * π * c') - 2 * D5r / c'| ≤
      (B3 / (8 * π ^ 2) + B4 / (2 * π) + B5) / c' := by
    have t1 : |(D3r 0 - 2 * D3r 1 + D3r 2) / (8 * π ^ 2 * c')| ≤ (B3 / (8 * π ^ 2)) / c' := by
      rw [abs_div, abs_of_pos (show 0 < 8 * π ^ 2 * c' by positivity)]
      have hnum : |D3r 0 - 2 * D3r 1 + D3r 2| ≤ B3 := by
        have ha1 := abs_add_le (D3r 0 - 2 * D3r 1) (D3r 2)
        have ha2 := abs_sub (D3r 0) (2 * D3r 1)
        rw [abs_mul, show |(2 : ℝ)| = 2 by norm_num] at ha2
        have d0 : |D3r 0| ≤ (2 * X) ^ 2 * (1 + C30) := by simpa [D3r, As] using hD30
        have d1 : |D3r 1| ≤ (2 * X) ^ 2 * (1 + C31) := by simpa [D3r, As] using hD31
        have d2 : |D3r 2| ≤ (2 * X) ^ 2 * (1 + C32) := by simpa [D3r, As] using hD32
        dsimp [B3]; linarith
      calc _ ≤ B3 / (8 * π ^ 2 * c') := div_le_div_of_nonneg_right hnum (by positivity)
        _ = (B3 / (8 * π ^ 2)) / c' := by ring
    have t2 : |(2 * D4r 1 - 2 * D4r 2) / (2 * π * c')| ≤ (B4 / (2 * π)) / c' := by
      rw [abs_div, abs_of_pos (show 0 < 2 * π * c' by positivity)]
      have hnum : |2 * D4r 1 - 2 * D4r 2| ≤ B4 := by
        have ha := abs_sub (2 * D4r 1) (2 * D4r 2)
        rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num] at ha
        have d1 : |D4r 1| ≤ (2 * X) ^ 3 * (1 + C41) := by simpa [D4r, As] using hD41
        have d2 : |D4r 2| ≤ (2 * X) ^ 3 * (1 + C42) := by simpa [D4r, As] using hD42
        dsimp [B4]; linarith
      calc _ ≤ B4 / (2 * π * c') := div_le_div_of_nonneg_right hnum (by positivity)
        _ = (B4 / (2 * π)) / c' := by ring
    have t3 : |2 * D5r / c'| ≤ B5 / c' := by
      rw [abs_div, abs_of_pos hcpos, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
      have d5 : |D5r| ≤ (2 * X) ^ 4 * (1 + C51) := by simpa [D5r, As] using hD51
      have hB5 : 2 * |D5r| ≤ B5 := by dsimp [B5]; linarith
      exact div_le_div_of_nonneg_right hB5 hcpos.le
    have ha := abs_sub ((D3r 0 - 2 * D3r 1 + D3r 2) / (8 * π ^ 2 * c') + (2 * D4r 1 - 2 * D4r 2) / (2 * π * c')) (2 * D5r / c')
    have hb := abs_add_le ((D3r 0 - 2 * D3r 1 + D3r 2) / (8 * π ^ 2 * c')) ((2 * D4r 1 - 2 * D4r 2) / (2 * π * c'))
    have hsum_eq : (B3 / (8 * π ^ 2)) / c' + (B4 / (2 * π)) / c' + B5 / c' =
        (B3 / (8 * π ^ 2) + B4 / (2 * π) + B5) / c' := by ring
    linarith
  have hHC_As : |spinVacHC (c' / 12) (c' * x ^ 2 / 3) / (2 * π * c' * As) -
      (x ^ 3 / (3 * π)) * (1 - Real.exp (-4 * π * x)) ^ 2| ≤ Mrem / c' := by
    rw [hidHC]
    have hsum : (D4r 0 - 2 * D4r 1 + D4r 2) / (24 * π) +
        ((D3r 0 - 2 * D3r 1 + D3r 2) / (8 * π ^ 2 * c') +
          (2 * D4r 1 - 2 * D4r 2) / (2 * π * c') - 2 * D5r / c') -
        (x ^ 3 / (3 * π)) * (1 - Real.exp (-4 * π * x)) ^ 2 =
        ((D4r 0 - 2 * D4r 1 + D4r 2) / (24 * π) - (x ^ 3 / (3 * π)) * (1 - Real.exp (-4 * π * x)) ^ 2) +
        ((D3r 0 - 2 * D3r 1 + D3r 2) / (8 * π ^ 2 * c') +
          (2 * D4r 1 - 2 * D4r 2) / (2 * π * c') - 2 * D5r / c') := by ring
    rw [hsum]
    calc _ ≤ |_ - _| + |_| := abs_add_le _ _
      _ ≤ M4 / (24 * π) / c' + (B3 / (8 * π ^ 2) + B4 / (2 * π) + B5) / c' := add_le_add hmain4 hrem_bd
      _ = Mrem / c' := by dsimp [Mrem]; ring
  have hHC_As' : |spinVacHC (c' / 12) (c' * x ^ 2 / 3) / (2 * π * c' * As) -
      (x ^ 3 / (3 * π)) * (virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) / As)| ≤
      (Mrem + (X ^ 3 / (3 * π)) * Cv) / c' := by
    have hid : spinVacHC (c' / 12) (c' * x ^ 2 / 3) / (2 * π * c' * As) -
        (x ^ 3 / (3 * π)) * (virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) / As) =
        (spinVacHC (c' / 12) (c' * x ^ 2 / 3) / (2 * π * c' * As) -
          (x ^ 3 / (3 * π)) * (1 - Real.exp (-4 * π * x)) ^ 2) -
        (x ^ 3 / (3 * π)) * (virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) / As -
          (1 - Real.exp (-4 * π * x)) ^ 2) := by ring
    have hV' : |virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) / As -
        (1 - Real.exp (-4 * π * x)) ^ 2| ≤ Cv / c' := by simpa [As, hden_eq] using hV
    have hx3 : x ^ 3 / (3 * π) ≤ X ^ 3 / (3 * π) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hxpos.le hx.2 3) (by positivity)
    rw [hid]
    have hmul_le : |(x ^ 3 / (3 * π)) * (virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) / As -
        (1 - Real.exp (-4 * π * x)) ^ 2)| ≤ (X ^ 3 / (3 * π)) * (Cv / c') := by
      rw [abs_mul, abs_of_pos (by positivity)]
      exact mul_le_mul hx3 hV' (abs_nonneg _) (by positivity)
    have ha := abs_sub (spinVacHC (c' / 12) (c' * x ^ 2 / 3) / (2 * π * c' * As) -
        (x ^ 3 / (3 * π)) * (1 - Real.exp (-4 * π * x)) ^ 2)
      ((x ^ 3 / (3 * π)) * (virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) / As -
        (1 - Real.exp (-4 * π * x)) ^ 2))
    linarith [show Mrem / c' + X ^ 3 / (3 * π) * (Cv / c') = (Mrem + X ^ 3 / (3 * π) * Cv) / c' by ring]
  have hQ_pos : 0 < virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) / As := div_pos hVv_pos hAs
  have hdiv_eq : spinVacHC (c' / 12) (c' * x ^ 2 / 3) /
        (2 * π * c' * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3)) - x ^ 3 / (3 * π) =
      (spinVacHC (c' / 12) (c' * x ^ 2 / 3) / (2 * π * c' * As) -
        (x ^ 3 / (3 * π)) * (virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) / As)) /
      (virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) / As) := by
    field_simp [Real.pi_ne_zero, hcpos.ne', hAs.ne', hVv_pos.ne']
  rw [hdiv_eq, abs_div, abs_of_pos hQ_pos]
  have hden_pos : 0 < qmin / 2 := by positivity
  calc _ ≤ ((Mrem + (X ^ 3 / (3 * π)) * Cv) / c') / (virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) / As) :=
        div_le_div_of_nonneg_right hHC_As' hQ_pos.le
    _ ≤ ((Mrem + (X ^ 3 / (3 * π)) * Cv) / c') / (qmin / 2) :=
        div_le_div_of_nonneg_left (by positivity) hden_pos hQ_ge
    _ = Ctot / c' := by dsimp [Ctot]; ring

/-- Uniform ratio bound between `virasoroProblem.cardyV` and `kernelK 5` on `[x₀, X]`:
`qProb spinMomentW5Prob * V_vir / K_5 → qProb * (1 - e^{-4πx})² / (2x)⁴` (equals `1` at `x = ξ_*`). -/
theorem kernelK5_div_virasoro_bound {x₀ X : ℝ} (hx₀ : 0 < x₀) (_hX : x₀ ≤ X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ c' in atTop, ∀ x ∈ Icc x₀ X,
      |(qProb spinMomentW5Prob * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3)) /
          kernelK 5 (c' / 12) (c' * x ^ 2 / 3) -
        qProb spinMomentW5Prob * ((1 - Real.exp (-4 * π * x)) ^ 2 / (2 * x) ^ 4)| ≤ C / c' := by
  obtain ⟨Cv, hCv, hv⟩ := cardyV_asymptotic_real virasoroProblem hx₀
  obtain ⟨C5, hC5, h5⟩ := cardyV_asymptotic_real (zeroShiftProb 5 (by norm_num)) hx₀
  let q5 := qProb spinMomentW5Prob
  have hq5_pos : 0 < q5 := qProb_pos spinMomentW5Prob
  let Ctot : ℝ := 2 * q5 * (Cv + 4 * C5) / (2 * x₀) ^ 4
  refine ⟨Ctot, by dsimp [Ctot]; positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max 1 (24 * virasoroProblem.totalShift)),
    eventually_ge_atTop (2 * C5 + 1)] with c' hc' hc5 x hx
  have hxpos : 0 < x := lt_of_lt_of_le hx₀ hx.1
  have hc1 : 1 ≤ c' := (le_max_left _ _).trans hc'
  have hcpos : 0 < c' := by linarith
  have hc0' : max 1 (24 * (zeroShiftProb 5 (by norm_num)).totalShift) ≤ c' := by
    rw [zeroShiftProb_totalShift, mul_zero]; exact max_le hc1 (by linarith)
  have hV := hv hc' hx.1
  have hK5 := h5 hc0' hx.1
  rw [virasoroProblem_nullPoly] at hV
  have hw5 : (zeroShiftProb 5 (by norm_num)).w = 5 := rfl
  rw [zeroShiftProb_cardyV, zeroShiftProb_nullPoly, hw5] at hK5
  let As : ℝ := Bessel.besselAs (c' * (2 * π * x / 3))
  have hAs : 0 < As := Bessel.besselAs_pos (by positivity)
  have hK5_pos : 0 < kernelK 5 (c' / 12) (c' * x ^ 2 / 3) := by
    rw [← zeroShiftProb_cardyV 5 (by norm_num)]
    exact (zeroShiftProb 5 (by norm_num)).cardyV_pos (by rw [zeroShiftProb_totalShift]; linarith) (by positivity)
  have hdenV : (2 * x) ^ (virasoroProblem.w - 1) * As = As := by simp [virasoroProblem]
  have hden5 : (2 * x) ^ (5 - 1) * As = (2 * x) ^ 4 * As := rfl
  rw [hdenV] at hV
  rw [hden5] at hK5
  set r5 := kernelK 5 (c' / 12) (c' * x ^ 2 / 3) / ((2 * x) ^ 4 * As)
  set rV := virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) / As
  have hr5_ge : 1 / 2 ≤ r5 := by
    have : C5 / c' ≤ 1 / 2 := by rw [div_le_iff₀ hcpos]; linarith
    linarith [(abs_le.mp hK5).1]
  have hQ_le : (1 - Real.exp (-4 * π * x)) ^ 2 ≤ 1 := by
    have h0 : 0 ≤ Real.exp (-4 * π * x) := (Real.exp_pos _).le
    have h1 : Real.exp (-4 * π * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hxpos.le])
    have h2 : 0 ≤ 1 - Real.exp (-4 * π * x) := by linarith
    nlinarith
  have hid : (q5 * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3)) /
        kernelK 5 (c' / 12) (c' * x ^ 2 / 3) -
      q5 * ((1 - Real.exp (-4 * π * x)) ^ 2 / (2 * x) ^ 4) =
      (q5 / (2 * x) ^ 4) * ((rV - (1 - Real.exp (-4 * π * x)) ^ 2) +
        (1 - Real.exp (-4 * π * x)) ^ 2 * (1 - r5)) / r5 := by
    dsimp [r5, rV]
    field_simp [hAs.ne', hK5_pos.ne']
    ring
  rw [hid, abs_div, abs_mul, abs_of_pos (by positivity : 0 < q5 / (2 * x) ^ 4),
    abs_of_pos (by linarith : 0 < r5)]
  have hnum : |rV - (1 - Real.exp (-4 * π * x)) ^ 2 + (1 - Real.exp (-4 * π * x)) ^ 2 * (1 - r5)| ≤
      (Cv + C5) / c' := by
    have h1 := abs_add_le (rV - (1 - Real.exp (-4 * π * x)) ^ 2) ((1 - Real.exp (-4 * π * x)) ^ 2 * (1 - r5))
    have h2 : |(1 - Real.exp (-4 * π * x)) ^ 2 * (1 - r5)| ≤ 1 * (C5 / c') := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_sub_comm]
      exact mul_le_mul hQ_le hK5 (abs_nonneg _) zero_le_one
    linarith [add_div Cv C5 c']
  have hx4 : (2 * x₀) ^ 4 ≤ (2 * x) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith [hx.1]) 4
  have hr1 : q5 / (2 * x) ^ 4 ≤ q5 / (2 * x₀) ^ 4 :=
    div_le_div_of_nonneg_left hq5_pos.le (by positivity) hx4
  calc (q5 / (2 * x) ^ 4) * |_| / r5
      ≤ (q5 / (2 * x₀) ^ 4) * ((Cv + C5) / c') / (1 / 2) := by
        refine div_le_div₀ (by positivity) (mul_le_mul hr1 hnum (abs_nonneg _) (by positivity))
          (by norm_num) hr5_ge
    _ ≤ Ctot / c' := by
        have hstep : q5 / (2 * x₀) ^ 4 * ((Cv + C5) / c') / (1 / 2) =
            (2 * q5 * (Cv + C5) / (2 * x₀) ^ 4) / c' := by ring
        rw [hstep]
        dsimp [Ctot]
        gcongr
        linarith

private lemma abs_exp_sub_exp_le_of_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b| := by
  wlog hab : b ≤ a generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a b]
    exact this hb ha (le_of_not_ge hab)
  have hdiff_nn : 0 ≤ Real.exp a - Real.exp b := sub_nonneg.mpr (Real.exp_le_exp.mpr hab)
  rw [abs_of_nonneg hdiff_nn, abs_of_nonneg (sub_nonneg.mpr hab)]
  have hexp_eq : Real.exp a - Real.exp b = Real.exp a * (1 - Real.exp (b - a)) := by
    rw [mul_sub, mul_one, ← Real.exp_add]; simp
  have h1 : 1 - Real.exp (b - a) ≤ a - b := by
    linarith [Real.add_one_le_exp (b - a)]
  have h2 : 0 ≤ 1 - Real.exp (b - a) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (sub_nonpos.mpr hab))
  have ha1 : Real.exp a ≤ 1 := Real.exp_le_one_iff.mpr ha
  calc Real.exp a - Real.exp b
      = Real.exp a * (1 - Real.exp (b - a)) := hexp_eq
    _ ≤ 1 * (a - b) := mul_le_mul ha1 h1 h2 zero_le_one
    _ = a - b := one_mul _

private lemma kernelK5_ratio_algebra {x y Ax Ay Kx Ky z Z R_lam zc ε : ℝ}
    (hxi : 0 < xiStar) (hZ : 0 ≤ Z) (hε : 0 < ε)
    (hx_half : xiStar / 2 ≤ x) (hy_ge_x : x ≤ y) (hy_half : xiStar / 2 ≤ y)
    (hx_abs : |x - xiStar| ≤ R_lam) (hy_abs : |y - xiStar| ≤ R_lam + zc)
    (hy_sub_x_le : y - x ≤ zc) (hlam : R_lam ≤ ε * xiStar ^ 2 / (32 * π * Z + 1))
    (hzc1 : zc ≤ xiStar * ε / 128) (hzc2 : zc ≤ ε * xiStar ^ 2 / (32 * π * Z + 1))
    (hz0 : 0 ≤ z) (hzZ : z ≤ Z)
    (hAx : 0 < Ax) (hAy : 0 < Ay) (hKy_pos : 0 < Ky)
    (hKx_bd : |Kx / ((2 * x) ^ 4 * Ax) - 1| ≤ min (1 / 4) (ε / 16))
    (hKy_bd : |Ky / ((2 * y) ^ 4 * Ay) - 1| ≤ min (1 / 4) (ε / 16))
    (hAs_ratio : Ax / Ay = (y / x) ^ (1 / 2 : ℝ) * Real.exp (-2 * π * z / (y + x))) :
    |Kx / Ky - Real.exp (-π * z / xiStar)| ≤ ε := by
  set rx : ℝ := Kx / ((2 * x) ^ 4 * Ax)
  set ry : ℝ := Ky / ((2 * y) ^ 4 * Ay)
  have hry_ge : 3 / 4 ≤ ry := by linarith [(abs_le.mp hKy_bd).1, min_le_left (1 / 4 : ℝ) (ε / 16)]
  have hr_diff : |rx / ry - 1| ≤ ε / 4 := by
    rw [show rx / ry - 1 = ((rx - 1) - (ry - 1)) / ry by
        field_simp [(by linarith : 0 < ry).ne']; ring,
      abs_div, abs_of_pos (by linarith : 0 < ry)]
    have hnum : |(rx - 1) - (ry - 1)| ≤ ε / 8 := by
      have := abs_sub (rx - 1) (ry - 1)
      have hmin : min (1 / 4) (ε / 16) ≤ ε / 16 := min_le_right _ _
      linarith
    calc _ ≤ (ε / 8) / (3 / 4) := div_le_div₀ (by positivity) hnum (by norm_num) hry_ge
      _ ≤ ε / 4 := by linarith
  have hx_pos : 0 < x := by linarith
  have hy_pos : 0 < y := by linarith
  have hpow_ratio : ((2 * x) ^ 4 * Ax) / ((2 * y) ^ 4 * Ay) =
      (x / y) ^ (7 / 2 : ℝ) * Real.exp (-2 * π * z / (y + x)) := by
    have hr1 : (2 * x) ^ 4 / (2 * y) ^ 4 = (x / y) ^ (4 : ℝ) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_pow]; ring
    have hr2 : (y / x) ^ (1 / 2 : ℝ) = (x / y) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.rpow_neg (div_pos hx_pos hy_pos).le, Real.div_rpow hx_pos.le hy_pos.le,
        inv_div, Real.div_rpow hy_pos.le hx_pos.le]
    calc ((2 * x) ^ 4 * Ax) / ((2 * y) ^ 4 * Ay)
        = ((2 * x) ^ 4 / (2 * y) ^ 4) * (Ax / Ay) := by ring
      _ = (x / y) ^ (4 : ℝ) * ((x / y) ^ (-(1 / 2 : ℝ)) * Real.exp (-2 * π * z / (y + x))) := by
          rw [hr1, hAs_ratio, hr2]
      _ = ((x / y) ^ (4 : ℝ) * (x / y) ^ (-(1 / 2 : ℝ))) * Real.exp (-2 * π * z / (y + x)) := by ring
      _ = (x / y) ^ (7 / 2 : ℝ) * Real.exp (-2 * π * z / (y + x)) := by
          rw [← Real.rpow_add (div_pos hx_pos hy_pos)]; norm_num
  have hxy_pos : 0 < x / y := div_pos hx_pos hy_pos
  have hxy_le1 : x / y ≤ 1 := (div_le_one hy_pos).mpr hy_ge_x
  have hxy_ge : 1 - (y - x) / y = x / y := by field_simp [hy_pos.ne']; ring
  have hxy_lo : 1 - ε / 32 ≤ x / y := by
    have h1 : (y - x) / y ≤ zc / (xiStar / 2) :=
      div_le_div₀ (by linarith) hy_sub_x_le (by positivity) hy_half
    have h3 : (y - x) / y ≤ ε / 32 := by
      calc (y - x) / y ≤ (xiStar * ε / 128) / (xiStar / 2) :=
            h1.trans (div_le_div_of_nonneg_right hzc1 (by positivity))
        _ = ε / 64 := by field_simp [hxi.ne']; ring
        _ ≤ ε / 32 := by linarith
    linarith [hxy_ge]
  have hpow_bd : |(x / y) ^ (7 / 2 : ℝ) - 1| ≤ ε / 4 := by
    have h01 : 0 ≤ x / y := hxy_pos.le
    have h4_le : (x / y) ^ 4 ≤ (x / y) ^ (7 / 2 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hxy_pos hxy_le1 (by norm_num : (7 / 2 : ℝ) ≤ 4)
    have h_le1 : (x / y) ^ (7 / 2 : ℝ) ≤ 1 := Real.rpow_le_one h01 hxy_le1 (by norm_num)
    have h2 : (x / y) ^ 2 ≤ 1 := pow_le_one₀ h01 hxy_le1
    have h3 : (x / y) ^ 3 ≤ 1 := pow_le_one₀ h01 hxy_le1
    have hpow4 : 1 - (x / y) ^ 4 ≤ 4 * (1 - x / y) := by
      calc 1 - (x / y) ^ 4 = (1 - x / y) * (1 + x / y + (x / y) ^ 2 + (x / y) ^ 3) := by ring
        _ ≤ (1 - x / y) * 4 := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        _ = 4 * (1 - x / y) := by ring
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  have hexp_bd : |Real.exp (-2 * π * z / (y + x)) - Real.exp (-π * z / xiStar)| ≤ ε / 4 := by
    have ha_np : -2 * π * z / (y + x) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) Real.pi_pos.le) hz0) (by linarith)
    have hb_np : -π * z / xiStar ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) hz0) hxi.le
    have hdiff_exp : |Real.exp (-2 * π * z / (y + x)) - Real.exp (-π * z / xiStar)| ≤
        |-2 * π * z / (y + x) - (-π * z / xiStar)| :=
      abs_exp_sub_exp_le_of_nonpos ha_np hb_np
    have hid_arg : -2 * π * z / (y + x) - (-π * z / xiStar) =
        π * z * ((y - xiStar) + (x - xiStar)) / ((y + x) * xiStar) := by
      have hyx_ne : y + x ≠ 0 := (by linarith : 0 < y + x).ne'
      field_simp [hyx_ne, hxi.ne']; ring
    have hyx_ge : xiStar ^ 2 ≤ (y + x) * xiStar := by
      have : xiStar ≤ y + x := by linarith
      rw [sq]
      exact mul_le_mul_of_nonneg_right this hxi.le
    have hnum_le : |π * z * ((y - xiStar) + (x - xiStar))| ≤ π * Z * (2 * R_lam + zc) := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      have hsum_abs : |(y - xiStar) + (x - xiStar)| ≤ 2 * R_lam + zc := by
        have := abs_add_le (y - xiStar) (x - xiStar)
        linarith
      exact mul_le_mul (mul_le_mul_of_nonneg_left hzZ Real.pi_pos.le) hsum_abs (abs_nonneg _) (by positivity)
    have harg_le : |-2 * π * z / (y + x) - (-π * z / xiStar)| ≤ ε / 4 := by
      have hRz_nn : 0 ≤ 2 * R_lam + zc := by linarith [abs_nonneg (y - xiStar), abs_nonneg (x - xiStar), hz0]
      rw [hid_arg, abs_div, abs_of_pos (by positivity : 0 < (y + x) * xiStar)]
      calc _ ≤ (π * Z * (2 * R_lam + zc)) / xiStar ^ 2 :=
            div_le_div₀ (by positivity) hnum_le (sq_pos_of_pos hxi) hyx_ge
        _ ≤ ε / 4 := by
            have hs_le : 2 * R_lam + zc ≤ 3 * (ε * xiStar ^ 2 / (32 * π * Z + 1)) := by linarith
            calc _ ≤ (π * Z * (3 * (ε * xiStar ^ 2 / (32 * π * Z + 1)))) / xiStar ^ 2 :=
                  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs_le (by positivity)) (by positivity)
              _ = (3 * π * Z / (32 * π * Z + 1)) * ε := by field_simp [hxi.ne']
              _ ≤ (3 / 32) * ε := by
                  have hrat : 3 * π * Z / (32 * π * Z + 1) ≤ 3 / 32 := by
                    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
                    linarith [show 0 ≤ π * Z by positivity]
                  exact mul_le_mul_of_nonneg_right hrat hε.le
              _ ≤ ε / 4 := by linarith
    exact hdiff_exp.trans harg_le
  have hK_eq : Kx / Ky = (rx / ry) * ((x / y) ^ (7 / 2 : ℝ) * Real.exp (-2 * π * z / (y + x))) := by
    rw [← hpow_ratio]
    dsimp [rx, ry]
    field_simp [hAx.ne', hAy.ne', hKy_pos.ne']
  rw [hK_eq]
  have h_e1 : Real.exp (-2 * π * z / (y + x)) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) Real.pi_pos.le) hz0) (by linarith))
  have h_e0 : 0 ≤ Real.exp (-2 * π * z / (y + x)) := (Real.exp_pos _).le
  have h_p0 : 0 ≤ (x / y) ^ (7 / 2 : ℝ) := by positivity
  have h_p1 : (x / y) ^ (7 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hxy_pos.le hxy_le1 (by norm_num)
  have hsplit : (rx / ry) * ((x / y) ^ (7 / 2 : ℝ) * Real.exp (-2 * π * z / (y + x))) -
        Real.exp (-π * z / xiStar) =
      (rx / ry - 1) * ((x / y) ^ (7 / 2 : ℝ) * Real.exp (-2 * π * z / (y + x))) +
      ((x / y) ^ (7 / 2 : ℝ) - 1) * Real.exp (-2 * π * z / (y + x)) +
      (Real.exp (-2 * π * z / (y + x)) - Real.exp (-π * z / xiStar)) := by ring
  rw [hsplit]
  have t1 : |(rx / ry - 1) * ((x / y) ^ (7 / 2 : ℝ) * Real.exp (-2 * π * z / (y + x)))| ≤ ε / 4 := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg h_p0 h_e0)]
    have hpe : (x / y) ^ (7 / 2 : ℝ) * Real.exp (-2 * π * z / (y + x)) ≤ 1 :=
      (mul_le_mul h_p1 h_e1 h_e0 zero_le_one).trans (by norm_num)
    exact (mul_le_mul hr_diff hpe (mul_nonneg h_p0 h_e0) (by positivity)).trans (by linarith)
  have t2 : |((x / y) ^ (7 / 2 : ℝ) - 1) * Real.exp (-2 * π * z / (y + x))| ≤ ε / 4 := by
    rw [abs_mul, abs_of_nonneg h_e0]
    exact (mul_le_mul hpow_bd h_e1 h_e0 (by positivity)).trans (by linarith)
  have ha1 := abs_add_le ((rx / ry - 1) * ((x / y) ^ (7 / 2 : ℝ) * Real.exp (-2 * π * z / (y + x))) +
    ((x / y) ^ (7 / 2 : ℝ) - 1) * Real.exp (-2 * π * z / (y + x)))
    (Real.exp (-2 * π * z / (y + x)) - Real.exp (-π * z / xiStar))
  have ha2 := abs_add_le ((rx / ry - 1) * ((x / y) ^ (7 / 2 : ℝ) * Real.exp (-2 * π * z / (y + x))))
    (((x / y) ^ (7 / 2 : ℝ) - 1) * Real.exp (-2 * π * z / (y + x)))
  linarith

/-- Uniform ratio along the Airy shift `tAiry c' u + z` (`sd:spinmoment-endpoint`):
for fixed `R, Z ≥ 0`, `kernelK 5 (c'/12) (tAiry c' u) / kernelK 5 (c'/12) (tAiry c' u + z) → e^{-π z / ξ_*}`
uniformly for `(u, z) ∈ [-R, R] × [0, Z]`. -/
theorem kernelK5_ratio_shift_tendsto {R Z : ℝ} (_hR : 0 ≤ R) (hZ : 0 ≤ Z) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ c' in atTop, ∀ u ∈ Icc (-R) R, ∀ z ∈ Icc 0 Z,
      |kernelK 5 (c' / 12) (tAiry c' u) / kernelK 5 (c' / 12) (tAiry c' u + z) -
        Real.exp (-π * z / xiStar)| ≤ ε := by
  intro ε hε
  obtain ⟨C5, _, h5⟩ := cardyV_asymptotic_real (zeroShiftProb 5 (by norm_num)) (half_pos xiStar_pos)
  have hxi := xiStar_pos
  have hsl : Tendsto slopeAiry atTop (𝓝 0) := by
    unfold slopeAiry epsAiry
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).div_const betaTip
  have huEnd_gt : ∀ᶠ c' in atTop, R < uEnd c' := by
    filter_upwards [(hsl.const_mul R).eventually (eventually_lt_nhds (by rw [mul_zero]; exact hxi)),
      eventually_gt_atTop (0 : ℝ)] with c' hRlt hcpos
    rw [lt_uEnd_iff hcpos]; linarith
  have h_lam : ∀ᶠ c' in atTop, R * slopeAiry c' ≤ min (xiStar / 4) (ε * xiStar ^ 2 / (32 * π * Z + 1)) := by
    have h1 := hsl.const_mul R
    rw [mul_zero] at h1
    exact h1.eventually_le_const (lt_min (by positivity) (by positivity))
  have h_zc : ∀ᶠ c' in atTop, 3 * Z / (c' * xiStar) ≤
      min (xiStar / 4) (min (xiStar * ε / 128) (ε * xiStar ^ 2 / (32 * π * Z + 1))) := by
    have ht : Tendsto (fun c' : ℝ => 3 * Z / (c' * xiStar)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_id.atTop_mul_const hxi)
    exact ht.eventually_le_const (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have h_C5 : ∀ᶠ c' in atTop, C5 / c' ≤ min (1 / 4) (ε / 16) := by
    have ht : Tendsto (fun c' : ℝ => C5 / c') atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    exact ht.eventually_le_const (lt_min (by norm_num) (by positivity))
  filter_upwards [huEnd_gt, h_lam, h_zc, h_C5,
    eventually_ge_atTop (max 1 (24 * (zeroShiftProb 5 (by norm_num)).totalShift)),
    eventually_gt_atTop (0 : ℝ)] with c' huEnd hlam hzc hC5 hc5 hcpos u hu z hz
  have hu_end : u < uEnd c' := lt_of_le_of_lt hu.2 huEnd
  let x : ℝ := bAiry c' u
  let y : ℝ := √(x ^ 2 + 3 * z / c')
  have hx_eq : x = xiStar - u * slopeAiry c' := bAiry_eq_of_lt hcpos hu_end
  have hx_abs : |x - xiStar| ≤ R * slopeAiry c' := by
    rw [hx_eq, show xiStar - u * slopeAiry c' - xiStar = -(u * slopeAiry c') by ring,
      abs_neg, abs_mul, abs_of_pos (slopeAiry_pos hcpos)]
    exact mul_le_mul_of_nonneg_right (abs_le.mpr hu) (slopeAiry_pos hcpos).le
  have hx_half : xiStar / 2 ≤ x := by
    have := (abs_le.mp hx_abs).1
    have := hlam.trans (min_le_left _ _)
    linarith
  have hy_ge_x : x ≤ y := by
    dsimp [y]
    have hx0 : 0 ≤ x := by linarith
    calc x = √(x ^ 2) := (Real.sqrt_sq hx0).symm
      _ ≤ √(x ^ 2 + 3 * z / c') :=
        Real.sqrt_le_sqrt (le_add_of_nonneg_right (div_nonneg (mul_nonneg (by norm_num) hz.1) hcpos.le))
  have hy_arg : 0 ≤ x ^ 2 + 3 * z / c' := add_nonneg (sq_nonneg x) (div_nonneg (mul_nonneg (by norm_num) hz.1) hcpos.le)
  have hy_half : xiStar / 2 ≤ y := hx_half.trans hy_ge_x
  have hy_sq : y ^ 2 = x ^ 2 + 3 * z / c' := Real.sq_sqrt hy_arg
  have hy_sub_x : y - x = 3 * z / (c' * (y + x)) := by
    have hyx : 0 < y + x := by linarith
    have hdiff : (y - x) * (y + x) = 3 * z / c' := by nlinarith [hy_sq]
    field_simp [hyx.ne', hcpos.ne'] at hdiff ⊢
    linarith
  have hy_sub_x_le : y - x ≤ 3 * Z / (c' * xiStar) := by
    rw [hy_sub_x]
    have h1 : 3 * z ≤ 3 * Z := by linarith [hz.2]
    have h2 : c' * xiStar ≤ c' * (y + x) := mul_le_mul_of_nonneg_left (by linarith) hcpos.le
    exact div_le_div₀ (by have := hz.1; positivity) h1 (by positivity) h2
  have hy_abs : |y - xiStar| ≤ R * slopeAiry c' + 3 * Z / (c' * xiStar) := by
    have htr := abs_add_le (y - x) (x - xiStar)
    rw [show (y - x) + (x - xiStar) = y - xiStar by ring,
      abs_of_nonneg (sub_nonneg.mpr hy_ge_x)] at htr
    linarith
  have ht_x : tAiry c' u = c' * x ^ 2 / 3 := by unfold tAiry; ring
  have ht_y : tAiry c' u + z = c' * y ^ 2 / 3 := by rw [ht_x, hy_sq]; field_simp
  rw [ht_y, ht_x]
  have hKx := h5 hc5 hx_half
  have hKy := h5 hc5 hy_half
  have hw5 : (zeroShiftProb 5 (by norm_num)).w = 5 := rfl
  rw [zeroShiftProb_cardyV, zeroShiftProb_nullPoly, hw5] at hKx hKy
  let Ax : ℝ := Bessel.besselAs (c' * (2 * π * x / 3))
  let Ay : ℝ := Bessel.besselAs (c' * (2 * π * y / 3))
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hAx : 0 < Ax := Bessel.besselAs_pos (by positivity)
  have hAy : 0 < Ay := Bessel.besselAs_pos (by positivity)
  have hKy_pos : 0 < kernelK 5 (c' / 12) (c' * y ^ 2 / 3) := by
    rw [← zeroShiftProb_cardyV 5 (by norm_num)]
    exact (zeroShiftProb 5 (by norm_num)).cardyV_pos (by rw [zeroShiftProb_totalShift]; linarith) (by positivity)
  have hAs_ratio : Ax / Ay = (y / x) ^ (1 / 2 : ℝ) * Real.exp (-2 * π * z / (y + x)) := by
    dsimp [Ax, Ay]; unfold Bessel.besselAs
    have hz1 : 0 < 2 * π * (c' * (2 * π * x / 3)) := by positivity
    have hz2 : 0 < 2 * π * (c' * (2 * π * y / 3)) := by positivity
    have hdiv_sqrt : Real.sqrt (2 * π * (c' * (2 * π * y / 3))) /
        Real.sqrt (2 * π * (c' * (2 * π * x / 3))) = (y / x) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_div hz2.le, Real.sqrt_eq_rpow]
      congr 1; field_simp [hcpos.ne', Real.pi_ne_zero]
    have hexp_sub : Real.exp (c' * (2 * π * x / 3)) / Real.exp (c' * (2 * π * y / 3)) =
        Real.exp (-2 * π * z / (y + x)) := by
      rw [← Real.exp_sub]; congr 1
      have hcyx : c' * (2 * π * x / 3) - c' * (2 * π * y / 3) = -(2 * π * c' / 3) * (y - x) := by ring
      rw [hcyx, hy_sub_x]
      have hyx_ne : y + x ≠ 0 := (by linarith : 0 < y + x).ne'
      field_simp [hcpos.ne', hyx_ne]
    calc (Real.exp (c' * (2 * π * x / 3)) / Real.sqrt (2 * π * (c' * (2 * π * x / 3)))) /
          (Real.exp (c' * (2 * π * y / 3)) / Real.sqrt (2 * π * (c' * (2 * π * y / 3))))
        = (Real.sqrt (2 * π * (c' * (2 * π * y / 3))) / Real.sqrt (2 * π * (c' * (2 * π * x / 3)))) *
            (Real.exp (c' * (2 * π * x / 3)) / Real.exp (c' * (2 * π * y / 3))) := by field_simp
      _ = _ := by rw [hdiv_sqrt, hexp_sub]
  exact kernelK5_ratio_algebra hxi hZ hε hx_half hy_ge_x hy_half hx_abs hy_abs
    hy_sub_x_le (hlam.trans (min_le_right _ _))
    (hzc.trans (min_le_right _ _ |>.trans (min_le_left _ _)))
    (hzc.trans (min_le_right _ _ |>.trans (min_le_right _ _)))
    hz.1 hz.2 hAx hAy hKy_pos
    (by simpa [Ax] using hKx.trans hC5)
    (by simpa [Ay] using hKy.trans hC5)
    hAs_ratio


/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinVacuumD_asymptotic_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spinVacuumD_asymptotic_real

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinVacHC_div_cardy_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms spinVacHC_div_cardy_bound

/-- info: 'FormalResearch.ModularBootstrap.Spin.kernelK5_div_virasoro_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernelK5_div_virasoro_bound

/-- info: 'FormalResearch.ModularBootstrap.Spin.kernelK5_ratio_shift_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernelK5_ratio_shift_tendsto

end FormalResearch.ModularBootstrap.Spin
