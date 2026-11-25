module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.ParabolicCylinder
public import FormalResearch.JacobiEigenvectors.Charts.SoftParabolicCylinder

/-!
# Paper J, Layer 2 (L2.C6): calculus on the barrier weights `E_well`, `E_bar`, `E_-`

Source: Paper J `charts.tex` eq:cha-Ewell, `app_thmA.tex` "The soft edges", Step 3 (W2) (one-step comparison of the parabolic-cylinder weight) and the absorption paragraph
(`Lambda h^{-m} (E_{j_1}/E_n)^2 <= e^{-c/h}`).

## Proved here (explicit integrals only; no special-function fact)

* `Ewell_eq_exp`: `E_well(a,z) = exp(-int_{2 sqrt|a|}^z sqrt(t^2/4 - |a|) dt)` for **every** `z >= 0` (the integral vanishes below the turning point).
* `Ewell_pos`, `Ewell_le_one`, `Ewell_ge_exp`: `exp(-z^2/4) <= E_well(a,z) <= 1`, `z >= 0`.
* `Eminus_mono`, `Eminus_le_one`: `E_-(a,Z) = E_well(a,|Z|)` (`a <= 0`) or `E_bar(a,Z)^{-1}` (`a > 0`) is non-decreasing in `Z <= 0` and `<= 1` there.
* `Eminus_ratio`: **one-step comparison** `E_-(a,z_2) <= exp((z_2 - z_1)(|z_1|/2 + sqrt(max a 0))) E_-(a,z_1)` for `z_1 <= z_2 <= 0` (Step 3 (W2): `e^{-C} <= E_{-,n+1}/E_{-,n} <= e^C`).
* `Eminus_decay`: if `gamma^2 <= z_2^2/4 + a` then `E_-(a,z_1) <= exp(-gamma (z_2 - z_1)) E_-(a,z_2)` for `z_1 <= z_2 <= 0` (the absorption estimate).
* `exp_neg_div_le`: `exp(-c/h) <= (m+1)!/c^{m+1} h^{m+1}`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open Set intervalIntegral

/-- the integrand of `E_well`. -/
def gWell (a t : ℝ) : ℝ := Real.sqrt (t ^ 2 / 4 - |a|)

/-- the integrand of `E_bar`. -/
def gBar (a t : ℝ) : ℝ := Real.sqrt (t ^ 2 / 4 + a)

lemma gWell_cont (a : ℝ) : Continuous (gWell a) := by
  unfold gWell; fun_prop

lemma gBar_cont (a : ℝ) : Continuous (gBar a) := by
  unfold gBar; fun_prop

lemma gWell_nonneg (a t : ℝ) : 0 ≤ gWell a t := Real.sqrt_nonneg _

lemma gBar_nonneg (a t : ℝ) : 0 ≤ gBar a t := Real.sqrt_nonneg _

/-- `g_well(t) <= |t|/2`. -/
lemma gWell_le (a t : ℝ) : gWell a t ≤ |t| / 2 := by
  unfold gWell
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have : |t| ^ 2 = t ^ 2 := sq_abs t
  nlinarith [abs_nonneg a, sq_nonneg (|t|)]

/-- `g_bar(t) <= |t|/2 + sqrt(max a 0)`. -/
lemma gBar_le (a t : ℝ) : gBar a t ≤ |t| / 2 + Real.sqrt (max a 0) := by
  unfold gBar
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have h1 : (Real.sqrt (max a 0)) ^ 2 = max a 0 := Real.sq_sqrt (le_max_right _ _)
  have h2 : a ≤ max a 0 := le_max_left _ _
  have h3 : |t| ^ 2 = t ^ 2 := sq_abs t
  nlinarith [abs_nonneg t, Real.sqrt_nonneg (max a 0), mul_nonneg (abs_nonneg t) (Real.sqrt_nonneg (max a 0))]

lemma gWell_zero_of_le {a t : ℝ} (h : t ^ 2 / 4 ≤ |a|) : gWell a t = 0 := by
  unfold gWell
  exact Real.sqrt_eq_zero_of_nonpos (by linarith)

/-- **`E_well` as one exponential of an integral** valid for all `z >= 0` (below the turning point the integral is zero). -/
lemma Ewell_eq_exp (a : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    Ewell a z = Real.exp (-(∫ t in (2 * Real.sqrt |a|)..z, gWell a t)) := by
  unfold Ewell
  split_ifs with h
  · rfl
  · have hle : z ≤ 2 * Real.sqrt |a| := not_lt.mp h
    have : (∫ t in (2 * Real.sqrt |a|)..z, gWell a t) = 0 := by
      rw [integral_symm]
      have : (∫ t in z..(2 * Real.sqrt |a|), gWell a t) = 0 := by
        have hc : ∀ t ∈ Set.uIcc z (2 * Real.sqrt |a|), gWell a t = 0 := by
          intro t ht
          rw [Set.uIcc_of_le hle] at ht
          apply gWell_zero_of_le
          have ht0 : 0 ≤ t := le_trans hz ht.1
          have h1 : t ≤ 2 * Real.sqrt |a| := ht.2
          have h2 : t ^ 2 ≤ (2 * Real.sqrt |a|) ^ 2 := by nlinarith
          have h3 : (2 * Real.sqrt |a|) ^ 2 = 4 * |a| := by
            rw [mul_pow, Real.sq_sqrt (abs_nonneg a)]; ring
          linarith
        rw [intervalIntegral.integral_congr hc]
        simp
      rw [this, neg_zero]
    rw [this, neg_zero, Real.exp_zero]

lemma Ewell_pos (a z : ℝ) : 0 < Ewell a z := by
  unfold Ewell
  split_ifs
  · exact Real.exp_pos _
  · exact one_pos

lemma Ebar_pos (a z : ℝ) : 0 < Ebar a z := Real.exp_pos _

lemma Eminus_pos (a z : ℝ) : 0 < Eminus a z := by
  unfold Eminus
  split_ifs
  · exact Ewell_pos _ _
  · exact inv_pos.mpr (Ebar_pos _ _)

lemma Eminus_of_nonpos {a : ℝ} (ha : a ≤ 0) (z : ℝ) : Eminus a z = Ewell a |z| := by
  unfold Eminus; rw [ite_eq_left ha]

/-- `E_well(a,z) <= 1` for `z >= 0`. -/
lemma Ewell_le_one (a : ℝ) {z : ℝ} (_hz : 0 ≤ z) : Ewell a z ≤ 1 := by
  unfold Ewell
  split_ifs with h
  · rw [Real.exp_le_one_iff, neg_nonpos]
    exact intervalIntegral.integral_nonneg h.le (fun t _ => Real.sqrt_nonneg _)
  · exact le_rfl

/-- the integral of `g_well` over `[z_1, z_2]` is at most `(z_2^2 - z_1^2)/4`. -/
lemma integral_gWell_le (a : ℝ) {z1 z2 : ℝ} (h0 : 0 ≤ z1) (h12 : z1 ≤ z2) :
    ∫ t in z1..z2, gWell a t ≤ (z2 ^ 2 - z1 ^ 2) / 4 := by
  have hI : IntervalIntegrable (fun t => t / 2) MeasureTheory.volume z1 z2 := by
    apply Continuous.intervalIntegrable; fun_prop
  have hg : IntervalIntegrable (gWell a) MeasureTheory.volume z1 z2 := (gWell_cont a).intervalIntegrable _ _
  have h1 : ∫ t in z1..z2, gWell a t ≤ ∫ t in z1..z2, t / 2 := by
    apply intervalIntegral.integral_mono_on h12 hg hI
    intro t ht
    have := gWell_le a t
    rw [abs_of_nonneg (le_trans h0 ht.1)] at this
    exact this
  have h2 : ∫ t in z1..z2, t / 2 = (z2 ^ 2 - z1 ^ 2) / 4 := by
    simp only [div_eq_mul_inv]
    rw [intervalIntegral.integral_mul_const, integral_id]
    ring
  linarith

/-- `E_well(a,z) >= exp(-z^2/4)`, `z >= 0`. -/
lemma Ewell_ge_exp (a : ℝ) {z : ℝ} (hz : 0 ≤ z) : Real.exp (-(z ^ 2 / 4)) ≤ Ewell a z := by
  rw [Ewell_eq_exp a hz]
  apply Real.exp_le_exp.mpr
  rw [neg_le_neg_iff]
  by_cases h : 2 * Real.sqrt |a| ≤ z
  · have := integral_gWell_le a (le_trans (by positivity) (le_refl _) : 0 ≤ 2 * Real.sqrt |a|) h
    have h4 : 0 ≤ (2 * Real.sqrt |a|) ^ 2 := sq_nonneg _
    linarith
  · have hle : z ≤ 2 * Real.sqrt |a| := (not_le.mp h).le
    rw [integral_symm]
    have : (0 : ℝ) ≤ ∫ t in z..(2 * Real.sqrt |a|), gWell a t :=
      intervalIntegral.integral_nonneg hle (fun t _ => gWell_nonneg a t)
    nlinarith [sq_nonneg z]

/-- the integral form of `E_-` for `a > 0`: `E_-(a,z) = exp(int_0^z g_bar)` (`E_bar^{-1}`). -/
lemma Eminus_bar (a z : ℝ) (ha : 0 < a) : Eminus a z = Real.exp (∫ t in (0 : ℝ)..z, gBar a t) := by
  unfold Eminus Ebar
  rw [ite_eq_right (not_le.mpr ha), ← Real.exp_neg, neg_neg]
  rfl

/-- `E_-` is non-decreasing on `z <= 0` (towards the fold). -/
lemma Eminus_mono (a : ℝ) {z1 z2 : ℝ} (h12 : z1 ≤ z2) (h2 : z2 ≤ 0) : Eminus a z1 ≤ Eminus a z2 := by
  by_cases ha : a ≤ 0
  · unfold Eminus
    rw [ite_eq_left ha, ite_eq_left ha]
    have e1 : |z1| = -z1 := abs_of_nonpos (by linarith)
    have e2 : |z2| = -z2 := abs_of_nonpos h2
    rw [e1, e2, Ewell_eq_exp a (by linarith), Ewell_eq_exp a (by linarith)]
    apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff]
    have hint := intervalIntegral.integral_add_adjacent_intervals
      ((gWell_cont a).intervalIntegrable (μ := MeasureTheory.volume) (2 * Real.sqrt |a|) (-z2))
      ((gWell_cont a).intervalIntegrable (μ := MeasureTheory.volume) (-z2) (-z1))
    have hnn : 0 ≤ ∫ t in (-z2)..(-z1), gWell a t :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => gWell_nonneg a t)
    linarith
  · have ha' : 0 < a := not_le.mp ha
    rw [Eminus_bar a z1 ha', Eminus_bar a z2 ha']
    apply Real.exp_le_exp.mpr
    have hint := intervalIntegral.integral_add_adjacent_intervals
      ((gBar_cont a).intervalIntegrable (μ := MeasureTheory.volume) 0 z1)
      ((gBar_cont a).intervalIntegrable (μ := MeasureTheory.volume) z1 z2)
    have hnn : 0 ≤ ∫ t in z1..z2, gBar a t :=
      intervalIntegral.integral_nonneg h12 (fun t _ => gBar_nonneg a t)
    linarith

lemma Eminus_le_one (a : ℝ) {z : ℝ} (hz : z ≤ 0) : Eminus a z ≤ 1 := by
  by_cases ha : a ≤ 0
  · unfold Eminus
    rw [ite_eq_left ha]
    exact Ewell_le_one a (abs_nonneg _)
  · have ha' : 0 < a := not_le.mp ha
    rw [Eminus_bar a z ha', Real.exp_le_one_iff]
    rw [integral_symm]
    have : (0 : ℝ) ≤ ∫ t in z..(0 : ℝ), gBar a t :=
      intervalIntegral.integral_nonneg hz (fun t _ => gBar_nonneg a t)
    linarith

/-- **One-step comparison of the parabolic-cylinder weight** (Step 3 (W2)): for `z_1 <= z_2 <= 0`,
`E_-(a,z_2) <= exp((z_2 - z_1)(|z_1|/2 + sqrt(max a 0))) E_-(a,z_1)`. -/
lemma Eminus_ratio (a : ℝ) {z1 z2 : ℝ} (h12 : z1 ≤ z2) (h2 : z2 ≤ 0) :
    Eminus a z2 ≤ Real.exp ((z2 - z1) * (|z1| / 2 + Real.sqrt (max a 0))) * Eminus a z1 := by
  have hz1 : z1 ≤ 0 := le_trans h12 h2
  have e1 : |z1| = -z1 := abs_of_nonpos hz1
  have hs := Real.sqrt_nonneg (max a 0)
  by_cases ha : a ≤ 0
  · unfold Eminus
    rw [ite_eq_left ha, ite_eq_left ha]
    have e2 : |z2| = -z2 := abs_of_nonpos h2
    rw [e2, e1, Ewell_eq_exp a (by linarith), Ewell_eq_exp a (by linarith), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hint := intervalIntegral.integral_add_adjacent_intervals
      ((gWell_cont a).intervalIntegrable (μ := MeasureTheory.volume) (2 * Real.sqrt |a|) (-z2))
      ((gWell_cont a).intervalIntegrable (μ := MeasureTheory.volume) (-z2) (-z1))
    -- ∫_{-z1}^{-z2}... : int_{c}^{-z1} - int_{c}^{-z2} = int_{-z2}^{-z1}
    have hle : ∫ t in (-z2)..(-z1), gWell a t ≤ (z2 - z1) * (-z1 / 2) := by
      have hI : IntervalIntegrable (fun _ : ℝ => -z1 / 2) MeasureTheory.volume (-z2) (-z1) := by
        apply Continuous.intervalIntegrable; fun_prop
      have hg : IntervalIntegrable (gWell a) MeasureTheory.volume (-z2) (-z1) := (gWell_cont a).intervalIntegrable _ _
      have h1 : ∫ t in (-z2)..(-z1), gWell a t ≤ ∫ t in (-z2)..(-z1), (-z1 / 2) := by
        apply intervalIntegral.integral_mono_on (by linarith) hg hI
        intro t ht
        have := gWell_le a t
        rw [abs_of_nonneg (by linarith [ht.1] : 0 ≤ t)] at this
        linarith [ht.2]
      have h2' : ∫ t in (-z2)..(-z1), (-z1 / 2) = (-z1 - -z2) * (-z1 / 2) := by
        rw [intervalIntegral.integral_const]; simp [smul_eq_mul]
      rw [h2'] at h1
      nlinarith
    have : (2 * Real.sqrt |a|) = (2 * Real.sqrt |a|) := rfl
    have hmul : (z2 - z1) * (-z1 / 2) ≤ (z2 - z1) * (-z1 / 2 + Real.sqrt (max a 0)) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith [hint, hle, hmul]
  · have ha' : 0 < a := not_le.mp ha
    rw [Eminus_bar a z1 ha', Eminus_bar a z2 ha', ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hint := intervalIntegral.integral_add_adjacent_intervals
      ((gBar_cont a).intervalIntegrable (μ := MeasureTheory.volume) 0 z1)
      ((gBar_cont a).intervalIntegrable (μ := MeasureTheory.volume) z1 z2)
    have hle : ∫ t in z1..z2, gBar a t ≤ (z2 - z1) * (|z1| / 2 + Real.sqrt (max a 0)) := by
      have hI : IntervalIntegrable (fun _ : ℝ => |z1| / 2 + Real.sqrt (max a 0)) MeasureTheory.volume z1 z2 := by
        apply Continuous.intervalIntegrable; fun_prop
      have hg : IntervalIntegrable (gBar a) MeasureTheory.volume z1 z2 := (gBar_cont a).intervalIntegrable _ _
      have h1 : ∫ t in z1..z2, gBar a t ≤ ∫ t in z1..z2, (|z1| / 2 + Real.sqrt (max a 0)) := by
        apply intervalIntegral.integral_mono_on h12 hg hI
        intro t ht
        have := gBar_le a t
        have hat : |t| ≤ |z1| := by
          rw [abs_of_nonpos (by linarith [ht.2] : t ≤ 0), e1]; linarith [ht.1]
        linarith
      rw [intervalIntegral.integral_const] at h1
      simpa [smul_eq_mul] using h1
    linarith

/-- **Absorption estimate**: if `gamma >= 0` and `gamma^2 <= z_2^2/4 + a`, then for `z_1 <= z_2 <= 0`: `E_-(a,z_1) <= exp(-gamma (z_2 - z_1)) E_-(a,z_2)`. -/
lemma Eminus_decay (a γ : ℝ) {z1 z2 : ℝ} (h12 : z1 ≤ z2) (h2 : z2 ≤ 0) (hγ : 0 ≤ γ) (hlow : γ ^ 2 ≤ z2 ^ 2 / 4 + a) :
    Eminus a z1 ≤ Real.exp (-(γ * (z2 - z1))) * Eminus a z2 := by
  have hz1 : z1 ≤ 0 := le_trans h12 h2
  by_cases ha : a ≤ 0
  · unfold Eminus
    rw [ite_eq_left ha, ite_eq_left ha]
    have e1 : |z1| = -z1 := abs_of_nonpos hz1
    have e2 : |z2| = -z2 := abs_of_nonpos h2
    rw [e1, e2, Ewell_eq_exp a (by linarith), Ewell_eq_exp a (by linarith), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hint := intervalIntegral.integral_add_adjacent_intervals
      ((gWell_cont a).intervalIntegrable (μ := MeasureTheory.volume) (2 * Real.sqrt |a|) (-z2))
      ((gWell_cont a).intervalIntegrable (μ := MeasureTheory.volume) (-z2) (-z1))
    have hge : γ * (-z1 - -z2) ≤ ∫ t in (-z2)..(-z1), gWell a t := by
      have hI : IntervalIntegrable (fun _ : ℝ => γ) MeasureTheory.volume (-z2) (-z1) := by
        apply Continuous.intervalIntegrable; fun_prop
      have hg : IntervalIntegrable (gWell a) MeasureTheory.volume (-z2) (-z1) := (gWell_cont a).intervalIntegrable _ _
      have h1 : ∫ t in (-z2)..(-z1), γ ≤ ∫ t in (-z2)..(-z1), gWell a t := by
        apply intervalIntegral.integral_mono_on (by linarith) hI hg
        intro t ht
        unfold gWell
        apply Real.le_sqrt_of_sq_le
        have ht0 : -z2 ≤ t := ht.1
        have : z2 ^ 2 ≤ t ^ 2 := by nlinarith
        have : |a| = -a := abs_of_nonpos ha
        linarith
      rw [intervalIntegral.integral_const] at h1
      simpa [smul_eq_mul, mul_comm] using h1
    nlinarith [hint, hge]
  · have ha' : 0 < a := not_le.mp ha
    rw [Eminus_bar a z1 ha', Eminus_bar a z2 ha', ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hint := intervalIntegral.integral_add_adjacent_intervals
      ((gBar_cont a).intervalIntegrable (μ := MeasureTheory.volume) 0 z1)
      ((gBar_cont a).intervalIntegrable (μ := MeasureTheory.volume) z1 z2)
    have hge : γ * (z2 - z1) ≤ ∫ t in z1..z2, gBar a t := by
      have hI : IntervalIntegrable (fun _ : ℝ => γ) MeasureTheory.volume z1 z2 := by
        apply Continuous.intervalIntegrable; fun_prop
      have hg : IntervalIntegrable (gBar a) MeasureTheory.volume z1 z2 := (gBar_cont a).intervalIntegrable _ _
      have h1 : ∫ t in z1..z2, γ ≤ ∫ t in z1..z2, gBar a t := by
        apply intervalIntegral.integral_mono_on h12 hI hg
        intro t ht
        unfold gBar
        apply Real.le_sqrt_of_sq_le
        have : z2 ^ 2 ≤ t ^ 2 := by nlinarith [ht.2]
        linarith
      rw [intervalIntegral.integral_const] at h1
      simpa [smul_eq_mul, mul_comm] using h1
    linarith

/-- `E_bar(a,-z) = E_bar(a,z)^{-1}` (the integrand is even). -/
lemma Ebar_neg (a z : ℝ) : Ebar a (-z) = (Ebar a z)⁻¹ := by
  have h1 : (∫ t in (0 : ℝ)..z, gBar a (-t)) = ∫ t in (-z)..(-(0 : ℝ)), gBar a t := intervalIntegral.integral_comp_neg (gBar a)
  have h2 : ∀ t, gBar a (-t) = gBar a t := fun t => by unfold gBar; rw [neg_sq]
  simp only [h2, neg_zero] at h1
  have h3 : (∫ t in (0 : ℝ)..(-z), gBar a t) = -∫ t in (0 : ℝ)..z, gBar a t := by
    rw [intervalIntegral.integral_symm (-z) 0, h1]
  have e : ∀ w, Ebar a w = Real.exp (-(∫ t in (0 : ℝ)..w, gBar a t)) := fun w => rfl
  rw [e, e, h3, ← Real.exp_neg]

/-- The weight of `M_Olv`: `W_well(a,Z)` (`a <= 0`) or `E_bar(a,Z)` (`a > 0`). -/
def Wmol (a z : ℝ) : ℝ := if a ≤ 0 then Wwell a z else Ebar a z

/-- `W_mol(a,-Z) = E_-(a,Z)` on the patch `Z <= 0`. -/
lemma Wmol_neg_of_nonpos (a : ℝ) {z : ℝ} (hz : z ≤ 0) : Wmol a (-z) = Eminus a z := by
  unfold Wmol Eminus
  by_cases ha : a ≤ 0
  · rw [ite_eq_left ha, ite_eq_left ha]
    unfold Wwell
    rw [ite_eq_left (by linarith), abs_of_nonpos hz]
  · rw [ite_eq_right ha, ite_eq_right ha, Ebar_neg]

/-- `W_mol(a,-Z) = E_swap(a,Z)` on the patch `Z > 0`. -/
lemma Wmol_neg_of_pos (a : ℝ) {z : ℝ} (hz : 0 < z) : Wmol a (-z) = Eswap a z := by
  unfold Wmol Eswap
  by_cases ha : a ≤ 0
  · rw [ite_eq_left ha, ite_eq_left ha]
    unfold Wwell
    rw [ite_eq_right (by linarith), abs_neg, abs_of_pos hz]
  · rw [ite_eq_right ha, ite_eq_right ha, Ebar_neg]

lemma k2_neg (a z : ℝ) : k2 a (-z) = k2 a z := by unfold k2; rw [neg_sq]

lemma Mbal_neg (a z : ℝ) : Mbal a (-z) = Mbal a z := by unfold Mbal; rw [k2_neg]

/-- **`M_Olv` from below** (R3): `c_PC kappa^{-1} W_mol M_bal <= M_Olv` (`molv_well`, `molv_bar`). -/
lemma molv_lower {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (a z : ℝ) :
    cPC * (kappaBal a)⁻¹ * Wmol a z * Mbal a z ≤ Molv U V a z := by
  unfold Wmol
  by_cases ha : a ≤ 0
  · rw [ite_eq_left ha]; exact (hf.molv_well a ha z).1
  · rw [ite_eq_right ha]; exact (hf.molv_bar a (not_le.mp ha) z).1

/-- `E_swap(a,z) >= 1` for `z >= 0` (the swapped weight is the inverse of a recessive one). -/
lemma Eswap_ge_one (a : ℝ) {z : ℝ} (hz : 0 ≤ z) : 1 ≤ Eswap a z := by
  unfold Eswap
  by_cases ha : a ≤ 0
  · rw [ite_eq_left ha]
    exact (one_le_inv₀ (Ewell_pos _ _)).mpr (Ewell_le_one a (abs_nonneg _))
  · rw [ite_eq_right ha]
    refine (one_le_inv₀ (Ebar_pos _ _)).mpr ?_
    unfold Ebar
    rw [Real.exp_le_one_iff, neg_nonpos]
    exact intervalIntegral.integral_nonneg hz (fun t _ => Real.sqrt_nonneg _)

lemma Eswap_pos (a z : ℝ) : 0 < Eswap a z := by
  unfold Eswap
  split_ifs
  · exact inv_pos.mpr (Ewell_pos _ _)
  · exact inv_pos.mpr (Ebar_pos _ _)

/-- `exp(-c/h) <= (m+1)!/c^{m+1} h^{m+1}` for `c, h > 0`. -/
lemma exp_neg_div_le (c h : ℝ) (hc : 0 < c) (hh : 0 < h) (m : ℕ) :
    Real.exp (-(c / h)) ≤ (Nat.factorial (m + 1) : ℝ) / c ^ (m + 1) * h ^ (m + 1) := by
  have hx : 0 ≤ c / h := by positivity
  have h1 : (c / h) ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) ≤ Real.exp (c / h) :=
    Real.pow_div_factorial_le_exp (c / h) hx (m + 1)
  have hpos : 0 < Real.exp (c / h) := Real.exp_pos _
  have hf : (0 : ℝ) < Nat.factorial (m + 1) := by exact_mod_cast Nat.factorial_pos _
  rw [Real.exp_neg, inv_le_comm₀ hpos (by positivity)]
  have e : ((Nat.factorial (m + 1) : ℝ) / c ^ (m + 1) * h ^ (m + 1))⁻¹ = (c / h) ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) := by
    rw [div_pow]
    field_simp
  rw [e]
  exact h1

end FormalResearch.JacobiEigenvectors.Charts
