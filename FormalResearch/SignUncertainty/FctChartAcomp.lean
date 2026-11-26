module

public import FormalResearch.SignUncertainty.FctEJetsU

/-!
# `A_λ ≍ A_0` for the compensated chart, and `(fct:V-diff-jets)` with the `A_0` weight (F2a, `fct:comp-cfu`)

* `ChartSetup.B_zero`: at `ℓ = 0` the chart value `B` vanishes, if `|ρ_F r(p, z)| ≤ |z|/2` (this holds for `r = λ ε_D z⁵ Θ`);
  proved from the defining equation `π²/12 · B - ℓ - ρ_F r(p, B) = 0` of `ChartOut`.
* `ChartSetup.B_comp`, `ChartSetup.A_comp`: along an `ℓ`-ray ending at `ℓ = 0` (`ZeroPath`), `|B - (12/π²) ℓ| ≤ ℓ/100`, so
  `0 ≤ A` and `A(q) ≤ 2 A(p)` for two points with the same `ℓ`.
* `ChartSetup.V_diff_jets_A0`, `ChartSetup.V_diff_jets_u_A0`: both lines of `(fct:V-diff-jets)` with the weight `max(Y, A_0)`,
  `A_0 = A(p₀)`, for the segment `p₀ + t v` at constant `ℓ`.

Class: proved, no hypotheses beyond those stated.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace FormalResearch.SignUncertainty
section ChartAcomp
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

namespace ChartSetup
variable (S : ChartSetup P)

/-- `B = 0` at `ℓ = 0`, when `|ρ_F r(p, z)| ≤ |z|/2`. -/
lemma B_zero (hρ : ∀ p ∈ S.Ω, ∀ z ∈ Ioo (-1 : ℝ) 6, |rhoF S.r (p, z)| ≤ 1 / 2 * |z|) {p : P} (hp : p ∈ S.Ω)
    (hℓ0 : S.ℓ p = 0) : S.B p = 0 := by
  obtain ⟨hBm, heq⟩ := S.out.2.1 p hp
  have h := hρ p hp _ hBm
  rw [hℓ0, sub_zero] at heq
  have hr : rhoF S.r (p, S.B p) = Real.pi ^ 2 / 12 * S.B p := by linarith
  rw [hr, abs_mul, abs_of_pos (by positivity : 0 < Real.pi ^ 2 / 12)] at h
  have hp2 : (9.8596 : ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_gt_d2]
  have : |S.B p| * (Real.pi ^ 2 / 12 - 1 / 2) ≤ 0 := by nlinarith [abs_nonneg (S.B p)]
  have hpos : 0 < Real.pi ^ 2 / 12 - 1 / 2 := by linarith
  have : |S.B p| ≤ 0 := by
    by_contra hc
    push Not at hc
    nlinarith
  exact abs_nonpos_iff.mp this

/-- A point from which an `ℓ`-ray (direction `w`, `‖w‖ ≤ 1`, `ℓ` decreasing at unit speed) stays in `Ω` down to `ℓ = 0`. -/
def ZeroPath (p : P) : Prop :=
  p ∈ S.Ω ∧ 0 ≤ S.ℓ p ∧ ∃ w : P, ‖w‖ ≤ 1 ∧ ∀ t ∈ Icc (0 : ℝ) (S.ℓ p), p - t • w ∈ S.Ω ∧ S.ℓ (p - t • w) = S.ℓ p - t

lemma B_comp (hρ : ∀ p ∈ S.Ω, ∀ z ∈ Ioo (-1 : ℝ) 6, |rhoF S.r (p, z)| ≤ 1 / 2 * |z|) {p : P}
    (hz : S.ZeroPath p) : |S.B p - 12 / Real.pi ^ 2 * S.ℓ p| ≤ 1 / 100 * S.ℓ p := by
  obtain ⟨hp, hl0, w, hw, hray⟩ := hz
  set T : ℝ := S.ℓ p with hT
  set N : P → ℝ := fun x => S.B x - 12 / Real.pi ^ 2 * S.ℓ x with hN
  have hNc : JC 16 S.Ω N (S.cB * S.ε) := S.out.1
  have hNd : ∀ x ∈ S.Ω, DifferentiableAt ℝ N x := fun x hx =>
    (hNc.1.contDiffAt (S.hΩ.mem_nhds hx)).differentiableAt (by norm_num)
  have hNbd : ∀ x ∈ S.Ω, ‖fderiv ℝ N x‖ ≤ 1 / 100 := by
    intro x hx
    have h1 := hNc.2 1 (by norm_num) x hx
    rw [norm_iteratedFDerivWithin_one _ (S.hΩ.uniqueDiffOn x hx), fderivWithin_of_isOpen S.hΩ hx] at h1
    exact h1.trans S.hcB
  have hder : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun s : ℝ => N (p - s • w)) (-(fderiv ℝ N (p - t • w) w))
      (Icc (0 : ℝ) T) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => p - s • w) (-w) t := by
      simpa using ((hasDerivAt_id t).smul_const w).const_sub p
    have h2 := (hNd _ (hray t ht).1).hasFDerivAt.comp_hasDerivAt t h1
    have h3 := h2.hasDerivWithinAt (s := Icc (0 : ℝ) T)
    rw [map_neg] at h3
    exact h3
  have hbd : ∀ t ∈ Icc (0 : ℝ) T, ‖-(fderiv ℝ N (p - t • w) w)‖ ≤ 1 / 100 := by
    intro t ht
    rw [norm_neg]
    calc ‖fderiv ℝ N (p - t • w) w‖ ≤ ‖fderiv ℝ N (p - t • w)‖ * ‖w‖ := (fderiv ℝ N _).le_opNorm w
      _ ≤ 1 / 100 * 1 := mul_le_mul (hNbd _ (hray t ht).1) hw (norm_nonneg _) (by norm_num)
      _ = 1 / 100 := by norm_num
  have hmv := (convex_Icc (0 : ℝ) T).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd
    (left_mem_Icc.mpr hl0) (right_mem_Icc.mpr hl0)
  have hend : N (p - T • w) = 0 := by
    obtain ⟨hmem, hℓ⟩ := hray T (right_mem_Icc.mpr hl0)
    have hb := S.B_zero hρ hmem (by rw [hℓ]; ring)
    simp only [hN, hb, hℓ]
    ring
  simp only [zero_smul, sub_zero, hend] at hmv
  rw [norm_sub_rev, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl0] at hmv
  simpa [hN, sub_zero] using hmv

lemma A_comp (hρ : ∀ p ∈ S.Ω, ∀ z ∈ Ioo (-1 : ℝ) 6, |rhoF S.r (p, z)| ≤ 1 / 2 * |z|) {p q : P}
    (hp : S.ZeroPath p) (hq : S.ZeroPath q) (hℓ : S.ℓ q = S.ℓ p) : 0 ≤ S.A p ∧ S.A q ≤ 2 * S.A p := by
  have hBp := S.B_comp hρ hp
  have hBq := S.B_comp hρ hq
  rw [hℓ] at hBq
  have hl0 := hp.2.1
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  have hp2 : (9.8596 : ℝ) < Real.pi ^ 2 := by nlinarith
  have hp3 : Real.pi ^ 2 < 9.9225 := by nlinarith
  have hk1 : (12 : ℝ) / Real.pi ^ 2 < 1.2171 := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hk2 : (1.2093 : ℝ) < 12 / Real.pi ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  set k : ℝ := 12 / Real.pi ^ 2 with hk
  have hd := dStar_bounds
  have hdp := S.d_dev hp.1
  have hdq := S.d_dev hq.1
  rw [abs_le] at hBp hBq hdp hdq
  have hdp1 : 0.92 ≤ S.d p := by linarith [hdp.1, hd.1]
  have hdp2 : S.d p ≤ 0.95 := by linarith [hdp.2, hd.2]
  have hdq1 : 0.92 ≤ S.d q := by linarith [hdq.1, hd.1]
  have hdq2 : S.d q ≤ 0.95 := by linarith [hdq.2, hd.2]
  have hBp1 : 1.19 * S.ℓ p ≤ S.B p := by nlinarith
  have hBq2 : S.B q ≤ 1.23 * S.ℓ p := by nlinarith
  have hBq1 : 0 ≤ S.B q := by nlinarith
  unfold ChartSetup.A
  have hdp3 : 0.8464 ≤ S.d p ^ 2 := by nlinarith
  have hdq3 : S.d q ^ 2 ≤ 0.9025 := by nlinarith
  have hB0 : 0 ≤ S.B p := by nlinarith
  refine ⟨mul_nonneg (sq_nonneg _) hB0, ?_⟩
  have h1 : S.d q ^ 2 * S.B q ≤ 0.9025 * (1.23 * S.ℓ p) :=
    mul_le_mul hdq3 hBq2 hBq1 (by norm_num)
  have h2 : 0.8464 * (1.19 * S.ℓ p) ≤ S.d p ^ 2 * S.B p :=
    mul_le_mul hdp3 hBp1 (by positivity) (sq_nonneg _)
  nlinarith

lemma max_two_pow_le {Y A0 : ℝ} (hY : 0 ≤ Y) (hA : 0 ≤ A0) {m : ℕ} (hm : m ≤ 4) :
    max Y (2 * A0) ^ m ≤ 16 * max Y A0 ^ m := by
  have h1 : max Y (2 * A0) ≤ 2 * max Y A0 := max_le (by linarith [le_max_left Y A0]) (by linarith [le_max_right Y A0])
  have h0 : 0 ≤ max Y (2 * A0) := le_max_of_le_left hY
  calc max Y (2 * A0) ^ m ≤ (2 * max Y A0) ^ m := pow_le_pow_left₀ h0 h1 m
    _ = 2 ^ m * max Y A0 ^ m := mul_pow _ _ _
    _ ≤ 16 * max Y A0 ^ m := by
        gcongr
        calc (2 : ℝ) ^ m ≤ 2 ^ 4 := pow_le_pow_right₀ (by norm_num) hm
          _ = 16 := by norm_num

/-- `(fct:V-diff-jets)`, first line, with the weight `max(Y, A_0)`, `A_0 = A(p₀)`: the segment `p₀ + t v` lies on rays down to
`ℓ = 0` (`ZeroPath`) at constant `ℓ`. -/
theorem V_diff_jets_A0 {β : ℝ} (hβ : 4 ≤ β)
    (hρ : ∀ p ∈ S.Ω, ∀ z ∈ Ioo (-1 : ℝ) 6, |rhoF S.r (p, z)| ≤ 1 / 2 * |z|) (v : P) (θ : P × ℝ → ℝ) (e : ℝ)
    (hψ : ∀ q ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6,
      fderiv ℝ (fun q : P × ℝ => S.ℓ q.1 - Real.pi ^ 2 / 36 * q.2 + S.r q) q (v, 0) = e * q.2 ^ 5 * θ q)
    (hθ : JCΦ 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) θ (Φb^[3] β) 0)
    {p0 : P} (hzp : ∀ t ∈ Icc (0 : ℝ) 1, S.ZeroPath (p0 + t • v))
    (hℓ : ∀ t ∈ Icc (0 : ℝ) 1, S.ℓ (p0 + t • v) = S.ℓ p0) {Y : ℝ} (hY : Y ∈ Yint) (hY0 : 0 ≤ Y) {n : ℕ}
    (hn : n ≤ 14) :
    |iteratedDeriv n (fun s : ℝ => S.V (p0 + v, s)) Y - iteratedDeriv n (fun s : ℝ => S.V (p0, s)) Y| ≤
      |e| * (16 * ((n + 1) * 2 ^ n * 1000000 * ((Nat.factorial 15 : ℝ) * Φb^[8] (Φb^[3] β)) *
        max Y (S.A p0) ^ (4 - n))) := by
  have h00 : S.ZeroPath p0 := by simpa using hzp 0 (left_mem_Icc.mpr zero_le_one)
  have hc : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ S.A (p0 + t • v) ∧ S.A (p0 + t • v) ≤ 2 * S.A p0 := fun t ht => by
    have := S.A_comp hρ h00 (hzp t ht) (hℓ t ht)
    exact ⟨(S.A_comp hρ (hzp t ht) (hzp t ht) rfl).1, this.2⟩
  have h := S.V_diff_jets hβ v θ e hψ hθ (fun t ht => (hzp t ht).1) (fun t ht => (hc t ht).1)
    (fun t ht => (hc t ht).2) hY hY0 hn
  have hA0 : 0 ≤ S.A p0 := (S.A_comp hρ h00 h00 rfl).1
  refine h.trans ?_
  have hK : 0 ≤ |e| * ((n + 1) * 2 ^ n * 1000000 * ((Nat.factorial 15 : ℝ) * Φb^[8] (Φb^[3] β))) := by
    have : 0 ≤ Φb^[8] (Φb^[3] β) := Φb_iter_nonneg (Φb_iter_nonneg (by linarith) 3) 8
    positivity
  have := max_two_pow_le hY0 hA0 (m := 4 - n) (by omega)
  calc _ = |e| * ((n + 1) * 2 ^ n * 1000000 * ((Nat.factorial 15 : ℝ) * Φb^[8] (Φb^[3] β))) *
        max Y (2 * S.A p0) ^ (4 - n) := by ring
    _ ≤ |e| * ((n + 1) * 2 ^ n * 1000000 * ((Nat.factorial 15 : ℝ) * Φb^[8] (Φb^[3] β))) *
        (16 * max Y (S.A p0) ^ (4 - n)) := mul_le_mul_of_nonneg_left this hK
    _ = _ := by ring

/-- `(fct:V-diff-jets)`, second line, with the weight `max(Y, A_0)` (`n ≤ 13`). -/
theorem V_diff_jets_u_A0 {β : ℝ} (hβ : 4 ≤ β)
    (hρ : ∀ p ∈ S.Ω, ∀ z ∈ Ioo (-1 : ℝ) 6, |rhoF S.r (p, z)| ≤ 1 / 2 * |z|) (v u : P) (hu : ‖u‖ ≤ 1)
    (θ : P × ℝ → ℝ) (e : ℝ)
    (hψ : ∀ q ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6,
      fderiv ℝ (fun q : P × ℝ => S.ℓ q.1 - Real.pi ^ 2 / 36 * q.2 + S.r q) q (v, 0) = e * q.2 ^ 5 * θ q)
    (hθ : JCΦ 16 (S.Ω ×ˢ Ioo (-1 : ℝ) 6) θ (Φb^[3] β) 0)
    {p0 : P} (hzp : ∀ t ∈ Icc (0 : ℝ) 1, S.ZeroPath (p0 + t • v))
    (hℓ : ∀ t ∈ Icc (0 : ℝ) 1, S.ℓ (p0 + t • v) = S.ℓ p0) {Y : ℝ} (hY : Y ∈ Yint) (hY0 : 0 ≤ Y) {n : ℕ}
    (hn : n ≤ 13) :
    |iteratedDeriv n (fun s : ℝ => fderiv ℝ S.V (p0 + v, s) (u, 0)) Y -
        iteratedDeriv n (fun s : ℝ => fderiv ℝ S.V (p0, s) (u, 0)) Y| ≤
      |e| * (16 * ((n + 1) * 2 ^ n * 10000000 * ((Nat.factorial 14 : ℝ) * Φb^[9] (Φb^[3] β)) *
        max Y (S.A p0) ^ (3 - n))) := by
  have h00 : S.ZeroPath p0 := by simpa using hzp 0 (left_mem_Icc.mpr zero_le_one)
  have hc : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ S.A (p0 + t • v) ∧ S.A (p0 + t • v) ≤ 2 * S.A p0 := fun t ht => by
    have := S.A_comp hρ h00 (hzp t ht) (hℓ t ht)
    exact ⟨(S.A_comp hρ (hzp t ht) (hzp t ht) rfl).1, this.2⟩
  have h := S.V_diff_jets_u hβ v u hu θ e hψ hθ (fun t ht => (hzp t ht).1) (fun t ht => (hc t ht).1)
    (fun t ht => (hc t ht).2) hY hY0 hn
  have hA0 : 0 ≤ S.A p0 := (S.A_comp hρ h00 h00 rfl).1
  refine h.trans ?_
  have hK : 0 ≤ |e| * ((n + 1) * 2 ^ n * 10000000 * ((Nat.factorial 14 : ℝ) * Φb^[9] (Φb^[3] β))) := by
    have : 0 ≤ Φb^[9] (Φb^[3] β) := Φb_iter_nonneg (Φb_iter_nonneg (by linarith) 3) 9
    positivity
  have := max_two_pow_le hY0 hA0 (m := 3 - n) (by omega)
  calc _ = |e| * ((n + 1) * 2 ^ n * 10000000 * ((Nat.factorial 14 : ℝ) * Φb^[9] (Φb^[3] β))) *
        max Y (2 * S.A p0) ^ (3 - n) := by ring
    _ ≤ |e| * ((n + 1) * 2 ^ n * 10000000 * ((Nat.factorial 14 : ℝ) * Φb^[9] (Φb^[3] β))) *
        (16 * max Y (S.A p0) ^ (3 - n)) := mul_le_mul_of_nonneg_left this hK
    _ = _ := by ring

end ChartSetup

/-- info: 'FormalResearch.SignUncertainty.ChartSetup.A_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChartSetup.A_comp

/-- info: 'FormalResearch.SignUncertainty.ChartSetup.V_diff_jets_A0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChartSetup.V_diff_jets_A0

/-- info: 'FormalResearch.SignUncertainty.ChartSetup.V_diff_jets_u_A0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChartSetup.V_diff_jets_u_A0

end ChartAcomp
end FormalResearch.SignUncertainty
