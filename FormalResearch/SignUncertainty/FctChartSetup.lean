/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctHomotopyJets
public import FormalResearch.SignUncertainty.FctJCBound

/-!
# The chart setup of the uniform compensated cubic chart (F2a, `fct:comp-cfu`)

`ChartSetup`: the output of `cfu_chart` (`FctCfuTheta`, `ChartOut`: the chart data `B, d, R, Z` with their `JB` bounds) together with
the smallness `c·ε ≤ 1/100` needed to use it, and the derived chart objects `D = Dfun B d R`, `A = d² B` and `V(p, Y) = 1/D(p, Z(p, Y))`
with their stage-bounded jets (`ChartSetup.D_bounds`, `V_jc`, `A_jc`) and the hypothesis of the homotopy ODE of `FctHomotopyJets`
(`ChartSetup.hode`).  This is the interface between the abstract `CfuTheta` and the weighted jets `E_jets`.

Class: proved, no hypotheses beyond those stated (`ChartSetup` is a structure of hypotheses, not discharged: it is instantiated by
`cfu_chart` once `CfuTheta` is instantiated from `fct:comp-D`).
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace FormalResearch.SignUncertainty
section ChartSetup
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The chart of `cfu_chart_core` together with the smallness (`c ε ≤ 1/100`) needed to use it. -/
structure ChartSetup (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P] where
  Ω : Set P
  hΩ : IsOpen Ω
  r : P × ℝ → ℝ
  ℓ : P → ℝ
  cB : ℝ
  cd : ℝ
  cR : ℝ
  cD : ℝ
  cZ : ℝ
  cV : ℝ
  ε : ℝ
  B : P → ℝ
  d : P → ℝ
  R : P × ℝ → ℝ
  Z : P × ℝ → ℝ
  out : ChartOut cB cd cR cD cZ cV Ω r ℓ ε B d R Z
  hr : JC 18 (Ω ×ˢ Ioo (-1 : ℝ) 6) r ε
  hℓ : ∀ p ∈ Ω, ℓ p ∈ Ioo (-(1 / 10) : ℝ) (27 / 10)
  hℓd : DifferentiableOn ℝ ℓ Ω
  hℓj : JC 16 Ω ℓ 3
  hcV : cV * ε ≤ 1 / 100
  hcV0 : 0 ≤ cV
  hε : 0 ≤ ε
  hcB : cB * ε ≤ 1 / 100
  hcd : cd * ε ≤ 1 / 100
  hcD : cD * ε ≤ 1 / 100
  hcB0 : 0 ≤ cB
  hcd0 : 0 ≤ cd
  hcD0 : 0 ≤ cD

namespace ChartSetup
variable (S : ChartSetup P)

/-- The chart function `D(p,z) = d(p) + (z - B(p)) R(p,z)`. -/
noncomputable def D : P × ℝ → ℝ := Dfun S.B S.d S.R
/-- `A = d² B`. -/
noncomputable def A : P → ℝ := fun p => S.d p ^ 2 * S.B p
/-- `V(p,Y) = 1/D(p, Z(p,Y))`. -/
noncomputable def V : P × ℝ → ℝ := fun y => (S.D (y.1, S.Z y))⁻¹

lemma D_bounds {q : P × ℝ} (hq : q ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6) : 92 / 100 ≤ S.D q ∧ S.D q ≤ 95 / 100 := by
  have h := JB.apply_le S.out.2.2.2.2.2.2.1.2 hq
  have hd := dStar_bounds
  have := S.hcD
  rw [abs_le] at h
  constructor <;> simp only [ChartSetup.D] <;> linarith [h.1, h.2, hd.1, hd.2]

lemma D_diff : DifferentiableOn ℝ S.D (S.Ω ×ˢ Ioo (-1 : ℝ) 6) := by
  have h := S.out.2.2.2.2.2.2.1.1.differentiableOn (by norm_num)
  exact (h.add_const dStar).congr fun q _ => by simp [ChartSetup.D]

lemma Dz_bound {q : P × ℝ} (hq : q ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6) : |fderiv ℝ (S.D) q (0, 1)| ≤ 1 / 100 := by
  have hW : IsOpen (S.Ω ×ˢ Ioo (-1 : ℝ) 6) := S.hΩ.prod isOpen_Ioo
  have h := JB.fderiv_apply_le hW (k := 16) (by norm_num) (N := fun q => S.D q - dStar) S.out.2.2.2.2.2.2.1.2 hq
  have hdf : fderiv ℝ (fun q => S.D q - dStar) q = fderiv ℝ S.D q := fderiv_sub_const _
  rw [hdf] at h
  exact h.trans (S.hcD)

lemma Yz_pos {q : P × ℝ} (hq : q ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6) :
    0 < S.D q ^ 2 + 2 * q.2 * S.D q * fderiv ℝ S.D q (0, 1) := by
  have h1 := S.D_bounds hq
  have h2 := S.Dz_bound hq
  have h3 := hq.2
  rw [abs_le] at h2
  have hD := h1.1
  have hDu := h1.2
  have hz1 : |q.2| ≤ 6 := by rw [abs_le]; constructor <;> linarith [h3.1, h3.2]
  have : |2 * q.2 * S.D q * fderiv ℝ S.D q (0, 1)| ≤ 2 * 6 * 0.95 * (1 / 100) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < S.D q)]
    have : |fderiv ℝ S.D q (0, 1)| ≤ 1 / 100 := abs_le.mpr h2
    have h4 : |q.2| ≤ 6 := hz1
    have : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
    rw [this]
    gcongr
    · linarith
  rw [abs_le] at this
  nlinarith [this.1]

lemma d_dev {p : P} (hp : p ∈ S.Ω) : |S.d p - dStar| ≤ 1 / 100 :=
  (JB.apply_le S.out.2.2.1.2 hp).trans S.hcd

lemma B_dev {p : P} (hp : p ∈ S.Ω) : |S.B p - 12 / Real.pi ^ 2 * S.ℓ p| ≤ 1 / 100 :=
  (JB.apply_le S.out.1.2 hp).trans S.hcB

lemma A_mem {p : P} (hp : p ∈ S.Ω) : S.A p ∈ Yint := by
  have h1 := S.d_dev hp
  have h2 := S.B_dev hp
  have hd := dStar_bounds
  have hl := S.hℓ p hp
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  rw [abs_le] at h1 h2
  have hp2 : (9.8596 : ℝ) < Real.pi ^ 2 := by nlinarith
  have hp3 : Real.pi ^ 2 < 9.9225 := by nlinarith
  have hk1 : (12 : ℝ) / Real.pi ^ 2 < 1.2171 := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hk2 : (1.2093 : ℝ) < 12 / Real.pi ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  set k : ℝ := 12 / Real.pi ^ 2 with hk
  have hBu : S.B p ≤ 3.30 := by nlinarith [hl.2]
  have hBl : -0.14 ≤ S.B p := by nlinarith [hl.1]
  have hdl : 0.92 ≤ S.d p := by linarith [h1.1, hd.1]
  have hdu : S.d p ≤ 0.95 := by linarith [h1.2, hd.2]
  unfold ChartSetup.A
  constructor
  · by_cases hB : 0 ≤ S.B p
    · nlinarith [mul_nonneg (sq_nonneg (S.d p)) hB]
    · push Not at hB
      nlinarith [sq_nonneg (S.d p)]
  · by_cases hB : 0 ≤ S.B p
    · nlinarith [mul_nonneg (sq_nonneg (S.d p)) hB, sq_nonneg (S.d p)]
    · push Not at hB
      nlinarith [sq_nonneg (S.d p)]

lemma d_diff : DifferentiableOn ℝ S.d S.Ω :=
  ((S.out.2.2.1.1.differentiableOn (by norm_num)).add_const dStar).congr fun p _ => by simp

lemma B_diff : DifferentiableOn ℝ S.B S.Ω := by
  have h := (S.out.1.1.differentiableOn (by norm_num)).add (S.hℓd.const_mul (12 / Real.pi ^ 2))
  exact h.congr fun p _ => by simp

lemma A_diff : DifferentiableOn ℝ S.A S.Ω := (S.d_diff.pow 2).mul S.B_diff

lemma D_pos {q : P × ℝ} (hq : q ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6) : 0 < S.D q := by
  have := (S.D_bounds hq).1; linarith

lemma D_at_B (p : P) : S.D (p, S.B p) = S.d p := by
  simp [ChartSetup.D, Dfun]

lemma Z_diff : DifferentiableOn ℝ S.Z (S.Ω ×ˢ Yint) := by
  have h := S.out.2.2.2.2.2.2.2.1.1.differentiableOn (by norm_num)
  have h2 : DifferentiableOn ℝ (fun y : P × ℝ => (dStar ^ 2)⁻¹ * y.2) (S.Ω ×ˢ Yint) :=
    (differentiableOn_snd).const_mul _
  exact (h.add h2).congr fun y _ => by simp

lemma Z_mem {y : P × ℝ} (hy : y ∈ S.Ω ×ˢ Yint) : S.Z y ∈ Ioo (-1 : ℝ) 6 := (S.out.2.2.2.2.2.2.2.2.1 y hy).1

lemma Z_D {y : P × ℝ} (hy : y ∈ S.Ω ×ˢ Yint) : S.Z y * S.D (y.1, S.Z y) ^ 2 = y.2 :=
  (S.out.2.2.2.2.2.2.2.2.1 y hy).2

lemma V_eq {y : P × ℝ} (hy : y ∈ S.Ω ×ˢ Yint) : y.2 * S.V y ^ 2 = S.Z y := by
  have hD := S.D_pos (q := (y.1, S.Z y)) ⟨hy.1, S.Z_mem hy⟩
  have h := S.Z_D hy
  simp only [ChartSetup.V]
  rw [← h]; field_simp

lemma hz {y : P × ℝ} (hy : y ∈ S.Ω ×ˢ Yint) : y.2 * S.V y ^ 2 ∈ Ioo (-1 : ℝ) 6 := by
  rw [S.V_eq hy]; exact S.Z_mem hy

lemma hB {p : P} (hp : p ∈ S.Ω) : S.B p ∈ Ioo (-1 : ℝ) 6 ∧ S.D (p, S.B p) = S.d p ∧ S.A p = S.d p ^ 2 * S.B p :=
  ⟨(S.out.2.1 p hp).1, S.D_at_B p, rfl⟩

lemma hid {q : P × ℝ} (hq : q ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6) :
    S.ℓ q.1 - Real.pi ^ 2 / 36 * q.2 + S.r q = S.A q.1 * S.D q - q.2 * S.D q ^ 3 / 3 := by
  have h := S.out.2.2.2.2.2.2.2.2.2.2 q hq
  simp only [ChartSetup.A, ChartSetup.D]
  rw [h]

/-- The pointwise homotopy ODE for the chart, in direction `v`. -/
theorem hode (v : P) (θ : P × ℝ → ℝ) (e : ℝ)
    (hψ : ∀ q ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6,
      fderiv ℝ (fun q : P × ℝ => S.ℓ q.1 - Real.pi ^ 2 / 36 * q.2 + S.r q) q (v, 0) = e * q.2 ^ 5 * θ q) :
    ∀ q ∈ S.Ω ×ˢ Yint, (S.A q.1 - q.2) * fderiv ℝ S.V q (v, 0) =
      e * (S.V q + 2 * q.2 * fderiv ℝ S.V q (0, 1)) *
        (S.A q.1 ^ 5 * S.V (q.1, S.A q.1) ^ 11 * θ (q.1, S.A q.1 * S.V (q.1, S.A q.1) ^ 2) -
          q.2 ^ 5 * S.V q ^ 11 * θ (q.1, q.2 * S.V q ^ 2)) := fun _ hy =>
  ode_pointwise S.hΩ isOpen_Ioo (ψ := fun q : P × ℝ => S.ℓ q.1 - Real.pi ^ 2 / 36 * q.2 + S.r q) (D := S.D)
    (V := S.V) (Z := S.Z) (θ := θ) (A := S.A) (B := S.B) (d := S.d) v hψ S.D_diff S.A_diff (fun _ hq => S.hid hq)
    S.Z_diff (fun _ hy => S.Z_mem hy) (fun _ hy => S.Z_D hy) (fun _ _ => rfl) (fun _ hq => S.D_pos hq)
    (fun _ hq => S.Yz_pos hq) (fun _ hp => S.hB hp) hy (S.A_mem hy.1)

lemma V_jc {β : ℝ} (hβ : 4 ≤ β) : JCΦ 16 (S.Ω ×ˢ Yint) S.V β 1 := by
  have hO : UniqueDiffOn ℝ (S.Ω ×ˢ Yint) := (S.hΩ.prod isOpen_Ioo).uniqueDiffOn
  have h0 : JCΦ 16 (S.Ω ×ˢ Yint) (fun y => (S.D (y.1, S.Z y))⁻¹ - dStar⁻¹) β 0 :=
    JC.mono S.out.2.2.2.2.2.2.2.2.2.1 (by
      have := S.hcV
      have : (0 : ℝ) ≤ β := by linarith
      simp only [Function.iterate_zero, id]; linarith)
  have hc : JCΦ 16 (S.Ω ×ˢ Yint) (fun _ : P × ℝ => dStar⁻¹) β 0 := JCΦ.const hO (by
    have hd := dStar_bounds
    rw [abs_of_pos (inv_pos.mpr (by linarith [hd.1]))]
    simp only [Function.iterate_zero, id]
    have : dStar⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith [hd.1]) (by norm_num)]; linarith [hd.1]
    linarith)
  exact (JCΦ.add hO h0 hc (by norm_num)).congr fun y _ => by simp [ChartSetup.V, ChartSetup.D]

lemma A_jc {β : ℝ} (hβ : 4 ≤ β) : JCΦ 16 S.Ω S.A β 3 := by
  have hβ0 : 0 ≤ β := by linarith
  have hO : UniqueDiffOn ℝ S.Ω := S.hΩ.uniqueDiffOn
  have hd0 : JCΦ 16 S.Ω (fun p => S.d p - dStar) β 0 :=
    JC.mono S.out.2.2.1 (by simp only [Function.iterate_zero, id]; linarith [S.hcd])
  have hdc : JCΦ 16 S.Ω (fun _ : P => dStar) β 0 := JCΦ.const hO (by
    have hd := dStar_bounds
    rw [abs_of_pos (by linarith [hd.1])]
    simp only [Function.iterate_zero, id]; linarith [hd.2])
  have hd1 : JCΦ 16 S.Ω S.d β 1 := (JCΦ.add hO hd0 hdc (by norm_num)).congr fun p _ => by simp
  have hd2 : JCΦ 16 S.Ω (fun p => S.d p ^ 2) β 2 :=
    (JCΦ.mul hO hβ0 (by norm_num) hd1 hd1 (by norm_num)).congr fun p _ => by ring
  have hB0 : JCΦ 16 S.Ω (fun p => S.B p - 12 / Real.pi ^ 2 * S.ℓ p) β 0 :=
    JC.mono S.out.1 (by simp only [Function.iterate_zero, id]; linarith [S.hcB])
  have hk : |12 / Real.pi ^ 2| ≤ β := by
    have hpi1 := Real.pi_gt_d2
    have : 12 / Real.pi ^ 2 ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    rw [abs_of_pos (by positivity)]; linarith
  have hℓ0 : JCΦ 16 S.Ω S.ℓ β 0 := JC.mono S.hℓj (by simp only [Function.iterate_zero, id]; linarith)
  have hkl : JCΦ 16 S.Ω (fun p => 12 / Real.pi ^ 2 * S.ℓ p) β 1 :=
    JCΦ.mul hO hβ0 (by norm_num) (JCΦ.const hO (m := 0) (by simpa using hk)) hℓ0 (by norm_num)
  have hB1 : JCΦ 16 S.Ω S.B β 2 :=
    (JCΦ.add hO (hB0.mono_m (Nat.zero_le 1)) hkl (by norm_num)).congr fun p _ => by ring
  exact JCΦ.mul hO hβ0 (by norm_num) hd2 hB1 (by norm_num)

end ChartSetup
end ChartSetup

/-- info: 'FormalResearch.SignUncertainty.ChartSetup.hode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChartSetup.hode

/-- info: 'FormalResearch.SignUncertainty.ChartSetup.V_jc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChartSetup.V_jc

/-- info: 'FormalResearch.SignUncertainty.ChartSetup.A_jc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChartSetup.A_jc

end FormalResearch.SignUncertainty
