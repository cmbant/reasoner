module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.InvReg

/-!
# Paper J, Layer 2: the expansion estimate for the recursion `x_r` (L2.E, `InvCoeffs`)

Source: Paper J `thmA.tex`, proof of `cor:eigen` (b)(iii): `hat X_k = sum_{r <= M} h^r x_r(y_k) + O(h^{M+1})`.

## Proved here

* `taylor_Icc_abs`: Lagrange Taylor with the points in either order.
* `expand_pointwise`: if the coefficients `1..M` of `Qp M c M (Dp M a)` vanish, `|sum_j h^j f_j(x_0 + delta(h)) - y| <= C h^{M+1}` (Taylor of each `S_j` to order `M-j`, the remainder bound, `InvAlg.tail_eval`).
* `InvCtx.expand_key`: the estimate for the recursion of `InvReg`, with constants uniform in `mu in K` and `y in [0, pi L]`.

## Differences from the paper

The paper obtains the expansion from the implicit function `X(y, h)`; here `P(h) = sum_r h^r x_r` is compared directly with the level equation (`F_M(P(h), h) = y + O(h^{M+1})` and `-partial_X F_M >= c`).

## Not formalised

Nothing for this file.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set Filter Topology FormalResearch.JacobiEigenvectors.Setting InvBD InvAlg

/-- Lagrange Taylor with the points in either order: `|f y' - sum_{i <= n} (y' - y)^i f^{(i)}(y)/i!| <= C |y' - y|^{n+1}/(n+1)!`. -/
lemma taylor_Icc_abs {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (n : ℕ) (hf : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f (Icc a b)) {C : ℝ}
    (hC : ∀ z ∈ Icc a b, |iteratedDerivWithin (n + 1) f (Icc a b) z| ≤ C) {y y' : ℝ} (hy : y ∈ Icc a b) (hy' : y' ∈ Icc a b) :
    |f y' - ∑ i ∈ range (n + 1), (i.factorial : ℝ)⁻¹ * (y' - y) ^ i * iteratedDerivWithin i f (Icc a b) y| ≤
      C * |y' - y| ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  rcases eq_or_ne y y' with e | hne
  · subst e
    simp [Finset.sum_range_succ', zero_pow, iteratedDerivWithin_zero]
  have hsub : uIcc y y' ⊆ Icc a b := uIcc_subset_Icc hy hy'
  have hUt : UniqueDiffOn ℝ (uIcc y y') := uniqueDiffOn_Icc (inf_lt_sup.2 hne)
  have hUs : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have huo : uIoo y y' ⊆ uIcc y y' := Ioo_subset_Icc_self
  have hf0 : ContDiffOn ℝ n f (uIcc y y') := (hf.mono hsub).of_le (by exact_mod_cast Nat.le_succ n)
  have hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc y y')) (uIoo y y') :=
    ((hf.mono hsub).differentiableOn_iteratedDerivWithin (by exact_mod_cast Nat.lt_succ_self n) hUt).mono huo
  obtain ⟨x', hx', hT⟩ := taylor_mean_remainder_lagrange (n := n) hne hf0 hf'
  rw [taylor_within_apply] at hT
  have hconv : ∀ k : ℕ, k ≤ n + 1 → ∀ z ∈ uIcc y y', iteratedDerivWithin k f (uIcc y y') z = iteratedDerivWithin k f (Icc a b) z := by
    intro k hk z hz
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDerivWithin_eq_iteratedFDerivWithin,
      iteratedFDerivWithin_subset hsub hUt hUs (hf.of_le (by exact_mod_cast hk)) hz]
  have hsum : ∑ k ∈ range (n + 1), ((k.factorial : ℝ)⁻¹ * (y' - y) ^ k) • iteratedDerivWithin k f (uIcc y y') y =
      ∑ i ∈ range (n + 1), (i.factorial : ℝ)⁻¹ * (y' - y) ^ i * iteratedDerivWithin i f (Icc a b) y := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [smul_eq_mul, hconv k (by have := Finset.mem_range.mp hk; omega) y left_mem_uIcc]
  rw [hsum] at hT
  have hx'I : x' ∈ Icc a b := hsub (huo hx')
  rw [hT, hconv (n + 1) le_rfl x' (huo hx'), abs_div, abs_mul, abs_pow,
    abs_of_pos (by positivity : (0 : ℝ) < ((n + 1).factorial : ℝ))]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact mul_le_mul_of_nonneg_right (hC x' hx'I) (pow_nonneg (abs_nonneg _) _)

open Polynomial in
lemma abs_eval_Dp_le {M : ℕ} {a : ℕ → ℝ} {Cr h : ℝ} (ha : ∀ r ≤ M, |a r| ≤ Cr) (hCr : 0 ≤ Cr) (hh : 0 < h) (hh1 : h ≤ 1) :
    |(InvAlg.Dp M a).eval h| ≤ M * Cr * h := by
  rw [InvAlg.eval_Dp]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ r ∈ range M, |a (r + 1) * h ^ (r + 1)| ≤ ∑ r ∈ range M, Cr * h := by
        refine Finset.sum_le_sum fun r hr => ?_
        have hrM : r + 1 ≤ M := Finset.mem_range.1 hr
        rw [abs_mul, abs_pow, abs_of_pos hh]
        exact mul_le_mul (ha _ hrM) (pow_le_of_le_one hh.le hh1 (Nat.succ_ne_zero r)) (by positivity) hCr
    _ = M * Cr * h := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

open Polynomial in
/-- The pointwise Taylor estimate behind `InvCoeffs`: `|sum_j h^j f_j(x_0 + delta(h)) - y| <= C h^{M+1}` once the coefficients of the Taylor polynomial vanish. -/
lemma expand_pointwise {M : ℕ} (hM : 1 ≤ M) (f : ℕ → ℝ → ℝ) {A B : ℝ} (hAB : A < B) {Cn Cr Cq y : ℝ}
    (hf : ∀ j ≤ M, ContDiffOn ℝ ((M + 1 : ℕ) : WithTop ℕ∞) (f j) (Icc A B))
    (hfb : ∀ j ≤ M, ∀ i ≤ M + 1, ∀ x ∈ Icc A B, |iteratedDerivWithin i (f j) (Icc A B) x| ≤ Cn)
    {X0 : ℝ} (hX0 : X0 ∈ Icc A B) (c : ℕ → ℕ → ℝ)
    (hc : ∀ j k, c j k = (k.factorial : ℝ)⁻¹ * iteratedDerivWithin k (f j) (Icc A B) X0)
    (a : ℕ → ℝ) (ha : ∀ r ≤ M, |a r| ≤ Cr) (hCr : 0 ≤ Cr) (hc00 : c 0 0 = y)
    (hvan : ∀ n, 1 ≤ n → n ≤ M → (InvAlg.Qp M c M (InvAlg.Dp M a)).coeff n = 0)
    (hcoef : ∀ n ≤ M * M, |(InvAlg.Qp M c M (InvAlg.Dp M a)).coeff n| ≤ Cq)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (hP : X0 + (InvAlg.Dp M a).eval h ∈ Icc A B) :
    |∑ j ∈ range (M + 1), h ^ j * f j (X0 + (InvAlg.Dp M a).eval h) - y| ≤
      ((M * M + 1) * Cq + (M + 1) * |Cn| * (M * Cr + 1) ^ (M + 1)) * h ^ (M + 1) := by
  obtain ⟨δh, hδdef⟩ : ∃ δh, δh = (InvAlg.Dp M a).eval h := ⟨_, rfl⟩
  rw [← hδdef] at hP ⊢
  have hδ : |δh| ≤ M * Cr * h := by
    rw [hδdef]; exact abs_eval_Dp_le ha hCr hh hh1
  -- Taylor for each `j`
  have hR : ∀ j ∈ range (M + 1), |f j (X0 + δh) - ∑ k ∈ range (M - j + 1), c j k * δh ^ k| ≤ |Cn| * (M * Cr * h) ^ (M - j + 1) := by
    intro j hj
    have hjM : j ≤ M := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hcd : ContDiffOn ℝ ((M - j + 1 : ℕ) : WithTop ℕ∞) (f j) (Icc A B) :=
      (hf j hjM).of_le (by exact_mod_cast (by omega : M - j + 1 ≤ M + 1))
    have hT := taylor_Icc_abs hAB (M - j) hcd (C := Cn) (fun z hz => hfb j hjM (M - j + 1) (by omega) z hz) hX0 hP
    have e1 : ∀ i, (i.factorial : ℝ)⁻¹ * (X0 + δh - X0) ^ i * iteratedDerivWithin i (f j) (Icc A B) X0 = c j i * δh ^ i := by
      intro i; rw [hc j i]; ring_nf
    simp only [e1] at hT
    refine hT.trans ?_
    have hfac : (1 : ℝ) ≤ ((M - j + 1).factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    rw [show X0 + δh - X0 = δh by ring]
    calc Cn * |δh| ^ (M - j + 1) / ((M - j + 1).factorial : ℝ) ≤ |Cn * |δh| ^ (M - j + 1)| / ((M - j + 1).factorial : ℝ) := by
          exact div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |Cn * |δh| ^ (M - j + 1)| := div_le_self (abs_nonneg _) hfac
      _ = |Cn| * |δh| ^ (M - j + 1) := by rw [abs_mul, abs_pow, abs_abs]
      _ ≤ |Cn| * (M * Cr * h) ^ (M - j + 1) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hδ _) (abs_nonneg _)
  have hdeg : (InvAlg.Qp M c M (InvAlg.Dp M a)).natDegree ≤ M * M := InvAlg.natDegree_Qp_le M c hM (InvAlg.natDegree_Dp_le M a)
  have hcoef0 : (InvAlg.Qp M c M (InvAlg.Dp M a)).coeff 0 = y := by
    rw [InvAlg.Qp_coeff_zero M c (InvAlg.X_dvd_Dp M a)]; exact hc00
  have htail := InvAlg.tail_eval hdeg hcoef0 hvan hcoef hh hh1
  have hQeval : (InvAlg.Qp M c M (InvAlg.Dp M a)).eval h =
      ∑ j ∈ range (M + 1), h ^ j * ∑ k ∈ range (M - j + 1), c j k * δh ^ k := by
    rw [InvAlg.eval_Qp, ← hδdef]
    refine Finset.sum_congr rfl fun j hj => ?_
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [ite_eq_left (by have := Finset.mem_range.1 hk; omega)]
  rw [hQeval] at htail
  have hsplit : ∑ j ∈ range (M + 1), h ^ j * f j (X0 + δh) - y =
      (∑ j ∈ range (M + 1), h ^ j * ∑ k ∈ range (M - j + 1), c j k * δh ^ k - y) +
        ∑ j ∈ range (M + 1), h ^ j * (f j (X0 + δh) - ∑ k ∈ range (M - j + 1), c j k * δh ^ k) := by
    simp only [mul_sub, Finset.sum_sub_distrib]; ring
  have hrem : |∑ j ∈ range (M + 1), h ^ j * (f j (X0 + δh) - ∑ k ∈ range (M - j + 1), c j k * δh ^ k)| ≤
      (M + 1) * |Cn| * (M * Cr + 1) ^ (M + 1) * h ^ (M + 1) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ range (M + 1), |h ^ j * (f j (X0 + δh) - ∑ k ∈ range (M - j + 1), c j k * δh ^ k)|
        ≤ ∑ j ∈ range (M + 1), |Cn| * (M * Cr + 1) ^ (M + 1) * h ^ (M + 1) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjM : j ≤ M := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
          rw [abs_mul, abs_pow, abs_of_pos hh]
          have h1 := hR j hj
          have hb : 0 ≤ (M : ℝ) * Cr := by positivity
          have h2 : (M * Cr) ^ (M - j + 1) ≤ (M * Cr + 1) ^ (M + 1) :=
            (pow_le_pow_left₀ hb (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (by omega))
          calc h ^ j * |f j (X0 + δh) - ∑ k ∈ range (M - j + 1), c j k * δh ^ k|
              ≤ h ^ j * (|Cn| * (M * Cr * h) ^ (M - j + 1)) := mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = |Cn| * (M * Cr) ^ (M - j + 1) * h ^ (M + 1) := by
                rw [mul_pow, show M + 1 = j + (M - j + 1) by omega, pow_add]; ring_nf
            _ ≤ |Cn| * (M * Cr + 1) ^ (M + 1) * h ^ (M + 1) := by gcongr
      _ = (M + 1) * |Cn| * (M * Cr + 1) ^ (M + 1) * h ^ (M + 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  rw [hsplit]
  calc _ ≤ |∑ j ∈ range (M + 1), h ^ j * ∑ k ∈ range (M - j + 1), c j k * δh ^ k - y| +
        |∑ j ∈ range (M + 1), h ^ j * (f j (X0 + δh) - ∑ k ∈ range (M - j + 1), c j k * δh ^ k)| := abs_add_le _ _
    _ ≤ ((M * M + 1) * Cq + (M + 1) * |Cn| * (M * Cr + 1) ^ (M + 1)) * h ^ (M + 1) := by
        push_cast at htail; nlinarith [htail, hrem]

section Key

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {M : ℕ} {S : ℕ → Par → ℝ → ℝ} {δ Cn c0 : ℝ}
  (ctx : InvCtx F K M S δ Cn c0)

include ctx

/-- The expansion estimate for the recursion `x_r` (uniform in `mu` and `y`). -/
theorem InvCtx.expand_key {Cb : ℝ} (hB : ∀ μ ∈ K, |F.bandLo μ| ≤ Cb ∧ |F.bandHi μ| ≤ Cb) :
    ∃ Cd C : ℝ, 0 ≤ Cd ∧ ∀ μ ∈ K, ∀ y ∈ Icc 0 (Real.pi * F.L), ∀ h : ℝ, 0 < h → h ≤ 1 →
      |(Dp M (fun r => xs F S δ (invDelta δ Cn c0) M μ M r y)).eval h| ≤ Cd * h ∧
      (invX0 F S (invDelta δ Cn c0) μ y + (Dp M (fun r => xs F S δ (invDelta δ Cn c0) M μ M r y)).eval h ∈
          Icc (F.bandLo μ - δ) (F.bandHi μ + δ) →
        |Fsum S M μ h (invX0 F S (invDelta δ Cn c0) μ y + (Dp M (fun r => xs F S δ (invDelta δ Cn c0) M μ M r y)).eval h) - y| ≤
          C * h ^ (M + 1)) := by
  have hI : (Icc (0 : ℝ) (Real.pi * F.L)).Nonempty := ⟨0, le_rfl, by have := F.L_pos; positivity⟩
  obtain ⟨Cr0, hCr0⟩ := ctx.reg hB M le_rfl
  set Cr := max Cr0 0 with hCr
  have hCr0' : 0 ≤ Cr := le_max_right _ _
  obtain ⟨C1, hC1⟩ := ctx.invC_bd 0
  obtain ⟨C3, hC3⟩ := PB.Qp_exists hI M 0 M (M * M) C1 Cr
  refine ⟨M * Cr, (M * M + 1) * C3 + (M + 1) * |Cn| * (M * Cr + 1) ^ (M + 1), by positivity, fun μ hμ y hy h hh hh1 => ?_⟩
  have ha : ∀ r ≤ M, |xs F S δ (invDelta δ Cn c0) M μ M r y| ≤ Cr := fun r hr =>
    ((hCr0 μ hμ r hr).bound y hy).trans (le_max_left _ _)
  refine ⟨abs_eval_Dp_le ha hCr0' hh hh1, fun hP => ?_⟩
  have hcbd : ∀ j ≤ M, ∀ k ≤ M, k ≤ M - j → BD (Icc 0 (Real.pi * F.L)) 0 C1 (fun y => invC F S δ (invDelta δ Cn c0) j k μ y) :=
    fun j hj k hk _ => hC1 μ hμ j hj k (by omega)
  have habd : ∀ r, 1 ≤ r → r ≤ M → BD (Icc 0 (Real.pi * F.L)) 0 Cr (fun y => xs F S δ (invDelta δ Cn c0) M μ M r y) := by
    intro r _ hr
    have := (hCr0 μ hμ r hr).mono_le (show 0 ≤ M + 1 - M by omega)
    exact this.mono_C (le_max_left _ _)
  have hpb := hC3 (fun j k y => invC F S δ (invDelta δ Cn c0) j k μ y) (fun r y => xs F S δ (invDelta δ Cn c0) M μ M r y) hcbd habd
  have hcoef : ∀ n ≤ M * M, |(Qp M (fun j k => invC F S δ (invDelta δ Cn c0) j k μ y) M
      (Dp M (fun r => xs F S δ (invDelta δ Cn c0) M μ M r y))).coeff n| ≤ C3 := fun n hn => (hpb n hn).bound y hy
  have hX := ctx.x0_mem hμ hy
  have hXo := ctx.Iprime_sub hX
  have hlt := ctx.lt_band hμ
  have hAB : F.bandLo μ - δ < F.bandHi μ + δ := by linarith [ctx.hδ]
  have hc01 : invC F S δ (invDelta δ Cn c0) 0 1 μ y ≠ 0 := by
    intro h0
    have := ctx.invC01 hμ hy
    rw [h0, abs_zero] at this
    linarith [ctx.hc0]
  have hc00 : invC F S δ (invDelta δ Cn c0) 0 0 μ y = y := by
    unfold invC invW
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, iteratedDerivWithin_zero]
    exact (ctx.x0_band hμ hy).2
  have hvan := Qp_vanish M (fun j k => invC F S δ (invDelta δ Cn c0) j k μ y) (invX0 F S (invDelta δ Cn c0) μ y) ctx.hM hc01
    M le_rfl
  exact expand_pointwise ctx.hM (fun j => S j μ) hAB (Cn := Cn) (Cr := Cr) (Cq := C3) (y := y)
    (fun j hj => (ctx.hS μ hμ j hj).1) (fun j hj i hi x hx => (ctx.hS μ hμ j hj).2 i hi x hx)
    (Ioo_subset_Icc_self hXo) (fun j k => invC F S δ (invDelta δ Cn c0) j k μ y) (fun j k => rfl)
    (fun r => xs F S δ (invDelta δ Cn c0) M μ M r y) ha hCr0' hc00 hvan hcoef hh hh1 hP

end Key

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.taylor_Icc_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.taylor_Icc_abs

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.expand_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.expand_pointwise

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.InvCtx.expand_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.InvCtx.expand_key

end FormalResearch.JacobiEigenvectors.TheoremA
