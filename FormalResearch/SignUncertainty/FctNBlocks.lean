/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctTau0Comp
public import FormalResearch.SignUncertainty.FctPhiKillSymbol
public import FormalResearch.SignUncertainty.FctSymUnif

/-!
# The two regimes of `φ_kill(iτ₀(L̃); a)` as `L`-symbols (`fct:bump-sym-check` (a), fourth item)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (a): by `fct:phikill` (1) with `a = c^{-1/12}`, `t = τ₀(L̃)`:
`|φ_kill| ≤ C (t/a)^8` for `t ≤ a` (here `τ₀² ≍ L` gives `L⁴ a^{-8}`), and `1 - φ_kill = O((a/t)^8)`, `t ≍ e^L`, for `L ≥ 1`.

For the real and imaginary parts `p.L` of the parameter `p = (L, a, s, x₀)` (`a ≤ 1`, `x₀ ≤ 1/2`, `|s| ≤ x₀/2`):

* `block_small`: `L(φ_kill(iτ₀(x - s))) ∈ SymW [x₀, 1/2]` of weight `Θ a^{-8} x⁴`;
* `block_large`: `L(1 - φ_kill(iτ₀(x - s))) ∈ SymW [1/2, ∞)` of weight `1` (super-exponential decay, `τ₀ ≳ e^{x/2}`);

each with **one** constant sequence `K` for all parameters (`USym`).

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Filter Topology Finset
open scoped ContDiff Real

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter
  FormalResearch.SignUncertainty.FctPhiKill

/-- The parameters of the `φ_kill` factor: a linear functional `L` (`Re` or `Im`), the width `a`, the shift `s`, the left end `x₀`
and the amplitude `L₁`. -/
structure NPar where
  L : ℂ →L[ℝ] ℝ
  a : ℝ
  s : ℝ
  x₀ : ℝ
  L₁ : ℝ

/-- Admissible parameters for the two blocks. -/
def NHyp (p : NPar) : Prop :=
  (∀ z, |p.L z| ≤ ‖z‖) ∧ 0 < p.a ∧ p.a ≤ 1 ∧ 0 < p.x₀ ∧ p.x₀ ≤ 1 / 2 ∧ |p.s| ≤ p.x₀ / 2

lemma NHyp.s_le {p : NPar} (h : NHyp p) : |p.s| ≤ 1 / 4 := h.2.2.2.2.2.trans (by linarith [h.2.2.2.2.1])

lemma lamL_eq_inv {x : ℝ} (hx : 0 < x) (h1 : x ≤ 1) : lamL x = x⁻¹ := by
  unfold lamL; exact max_eq_right (one_le_inv_iff₀.mpr ⟨hx, h1⟩)

lemma lamL_le_two {x : ℝ} (hx : 1 / 2 ≤ x) : lamL x ≤ 2 := by
  unfold lamL
  refine max_le (by norm_num) ?_
  have : (0 : ℝ) < x := by linarith
  rw [inv_le_comm₀ this (by norm_num)]; linarith

lemma contDiff_L_phiKill {a : ℝ} (ha : 0 < a) (L : ℂ →L[ℝ] ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => L (phiKill a ((t : ℂ) * Complex.I))) :=
  L.contDiff.comp (contDiff_phiKill_imag ha)

lemma contDiff_L_one_sub_phiKill {a : ℝ} (ha : 0 < a) (L : ℂ →L[ℝ] ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => L (1 - phiKill a ((t : ℂ) * Complex.I))) :=
  L.contDiff.comp (contDiff_const.sub (contDiff_phiKill_imag ha))

lemma contDiffOn_comp_tau0 {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (s : ℝ) :
    ContDiffOn ℝ ∞ (fun x => g (tau0 (x - s))) (Ioi s) :=
  hg.contDiffOn.comp (contDiffOn_tau0.comp (contDiffOn_id.sub contDiffOn_const) (fun y hy => sub_pos.mpr hy))
    (fun _ _ => mem_univ _)

/-- **Small regime**: `L(φ_kill(iτ₀(x - s); a)) ∈ SymW [x₀, 1/2]` of weight `Θ a^{-8} x⁴`. -/
theorem block_small : ∃ Θ : ℝ, 0 ≤ Θ ∧ USym NHyp (fun p => Icc p.x₀ (1 / 2)) (fun p x => Θ * (p.a ^ 8)⁻¹ * x ^ 4)
    (fun p x => p.L (phiKill p.a ((tau0 (x - p.s) : ℂ) * Complex.I))) := by
  obtain ⟨C, hC0, hC⟩ := phiKill_tsymbol
  obtain ⟨A, hA0, hcomp⟩ := comp_tau0_shift
  obtain ⟨Cu, hCu, hsq⟩ := tau0_sq_le
  set Θ : ℝ := max 4 ((3 / 2 * Cu) ^ 4) with hΘ
  refine ⟨Θ, (by norm_num : (0 : ℝ) ≤ 4).trans (le_max_left _ _),
    fun r => chainM C (fun j => (j : ℝ)) A 1 r 0, fun p hp => ?_⟩
  have hs4 := NHyp.s_le hp
  obtain ⟨hL, ha, ha1, hx₀, hx₀h, hs⟩ := hp
  set om : ℝ → ℝ := fun x => min 1 (Θ * (p.a ^ 8)⁻¹ * x ^ 4) with hom
  have hΘ0 : 0 ≤ Θ := (by norm_num : (0 : ℝ) ≤ 4).trans (le_max_left _ _)
  have ha8 : 0 < (p.a ^ 8)⁻¹ := by positivity
  have hbase : ∀ j, ∀ x, p.x₀ ≤ x → |tau0 (x - p.s) ^ j * iteratedDeriv j (fun t : ℝ => p.L (phiKill p.a ((t : ℂ) * Complex.I)))
      (tau0 (x - p.s))| ≤ C j * om x := by
    intro j x hx
    have hx0 : 0 < x := lt_of_lt_of_le hx₀ hx
    have hxs : 0 < x - p.s := by linarith [(abs_le.mp hs).2]
    have h1 := (hC p.a (tau0 (x - p.s)) ha (tau0_pos hxs) p.L hL j).1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (hC0 j))
    rw [hom]
    simp only
    refine le_min (min_le_left _ _) ?_
    rcases le_or_gt (x - p.s) 1 with h | h
    · refine (min_le_right _ _).trans ?_
      have h2 := hsq (x - p.s) ⟨hxs, h⟩
      have h3 : x - p.s ≤ 3 / 2 * x := by linarith [(abs_le.mp hs).1]
      have h4 : tau0 (x - p.s) ^ 2 ≤ 3 / 2 * Cu * x := by
        calc _ ≤ Cu * (x - p.s) := h2
          _ ≤ Cu * (3 / 2 * x) := mul_le_mul_of_nonneg_left h3 hCu.le
          _ = _ := by ring
      have h5 : (tau0 (x - p.s) / p.a) ^ 8 = (tau0 (x - p.s) ^ 2) ^ 4 * (p.a ^ 8)⁻¹ := by
        rw [div_pow, ← pow_mul]; ring
      rw [h5]
      calc (tau0 (x - p.s) ^ 2) ^ 4 * (p.a ^ 8)⁻¹ ≤ (3 / 2 * Cu * x) ^ 4 * (p.a ^ 8)⁻¹ :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sq_nonneg _) h4 4) ha8.le
        _ = (3 / 2 * Cu) ^ 4 * (p.a ^ 8)⁻¹ * x ^ 4 := by ring
        _ ≤ Θ * (p.a ^ 8)⁻¹ * x ^ 4 := by
            have : (3 / 2 * Cu) ^ 4 ≤ Θ := le_max_right _ _
            have h0 : 0 ≤ x ^ 4 := by positivity
            nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg ha8.le h0)]
    · refine (min_le_left _ _).trans ?_
      have hx34 : 3 / 4 < x := by linarith [(abs_le.mp hs4).1]
      have h1a : (1 : ℝ) ≤ (p.a ^ 8)⁻¹ := one_le_inv_iff₀.mpr ⟨by positivity, pow_le_one₀ ha.le ha1⟩
      have h4 : (3 / 4 : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) hx34.le 4
      have h5 : 4 ≤ Θ := le_max_left _ _
      have : (1 : ℝ) ≤ Θ * (p.a ^ 8)⁻¹ * x ^ 4 := by
        have h6 : 4 * 1 * (3 / 4 : ℝ) ^ 4 ≤ Θ * (p.a ^ 8)⁻¹ * x ^ 4 := by
          gcongr
        nlinarith [h6]
      exact this
  have hb := hcomp (x₀ := p.x₀) (s := p.s) (g := fun t : ℝ => p.L (phiKill p.a ((t : ℂ) * Complex.I))) (om := om) (P := C)
    hx₀ hs (contDiff_L_phiKill ha p.L).contDiffOn hC0 (fun x _ => by simp only [hom]; exact le_min zero_le_one (by positivity)) hbase
  refine ⟨?_, ?_, fun r => chainM_nonneg hC0 r 0, fun x _ => by positivity, fun r x hx => ?_⟩
  · exact fun x hx => lt_of_lt_of_le hx₀ hx.1
  · refine ⟨Ioi p.s, isOpen_Ioi, fun x hx => ?_, contDiffOn_comp_tau0 (contDiff_L_phiKill ha p.L) p.s⟩
    exact mem_Ioi.mpr (by linarith [(abs_le.mp hs).2, hx.1])
  · have hx0 : 0 < x := lt_of_lt_of_le hx₀ hx.1
    have := hb r x hx.1
    refine this.trans ?_
    rw [lamL_eq_inv hx0 (hx.2.trans (by norm_num)), inv_pow]
    have hM := chainM_nonneg (κ := fun j : ℕ => (j : ℝ)) (A := A) (B := 1) hC0 r 0
    have : om x ≤ Θ * (p.a ^ 8)⁻¹ * x ^ 4 := min_le_right _ _
    have hinv : 0 ≤ (x ^ r)⁻¹ := by positivity
    calc chainM C (fun j => (j : ℝ)) A 1 r 0 * om x * (x ^ r)⁻¹
        ≤ chainM C (fun j => (j : ℝ)) A 1 r 0 * (Θ * (p.a ^ 8)⁻¹ * x ^ 4) * (x ^ r)⁻¹ := by gcongr
      _ = _ := rfl


/-- The growth constant of `τ₀`: `τ₀(y) ≥ γ e^{x/2}` for `y = x - s ≥ x/2`, `x ≥ 1/2`. -/
noncomputable def gammaTau : ℝ := 2 / π * (1 - Real.exp (-(1 / 4)))

lemma gammaTau_pos : 0 < gammaTau := by
  unfold gammaTau
  have : Real.exp (-(1 / 4)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have := Real.pi_pos
  positivity

lemma tau0_ge_gamma {x s : ℝ} (hx : 1 / 2 ≤ x) (hs : |s| ≤ 1 / 4) : gammaTau * Real.exp (x / 2) ≤ tau0 (x - s) := by
  have hxs : x / 2 ≤ x - s := by linarith [(abs_le.mp hs).2]
  have hpos : 0 < x - s := by linarith
  refine le_trans ?_ (tau0_ge_exp hpos)
  have h1 : Real.exp (x / 2) ≤ Real.exp (x - s) := Real.exp_le_exp.mpr hxs
  have h3 : 1 ≤ Real.exp (-(1 / 4)) * Real.exp (x / 2) := by
    rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
  have hπ : 0 < 2 / π := by have := Real.pi_pos; positivity
  unfold gammaTau
  calc 2 / π * (1 - Real.exp (-(1 / 4))) * Real.exp (x / 2)
      = 2 / π * (Real.exp (x / 2) - Real.exp (-(1 / 4)) * Real.exp (x / 2)) := by ring
    _ ≤ 2 / π * (Real.exp (x / 2) - 1) := mul_le_mul_of_nonneg_left (by linarith) hπ.le
    _ ≤ 2 / π * (Real.exp (x - s) - 1) := mul_le_mul_of_nonneg_left (by linarith) hπ.le

/-- The decay `((γ e^{x/2})⁻¹)^8 ≤ γ^{-8} r! x^{-r}` for `x ≥ 1/2`. -/
lemma om2_decay {x : ℝ} (hx : 1 / 2 ≤ x) (r : ℕ) :
    ((gammaTau * Real.exp (x / 2))⁻¹) ^ 8 ≤ (gammaTau⁻¹) ^ 8 * (r.factorial : ℝ) * (x ^ r)⁻¹ := by
  have hγ := gammaTau_pos
  have hx0 : 0 < x := by linarith
  have hE1 : 1 ≤ Real.exp (x / 2) := Real.one_le_exp (by linarith)
  have hxr : x ^ r ≤ (r.factorial : ℝ) * Real.exp (x / 2) ^ 2 := by
    have h := Real.pow_div_factorial_le_exp x hx0.le r
    have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
    rw [div_le_iff₀ hf] at h
    calc x ^ r ≤ Real.exp x * r.factorial := h
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num; ring_nf
  have hE0 : 0 < Real.exp (x / 2) := Real.exp_pos _
  have e1 : ((gammaTau * Real.exp (x / 2))⁻¹) ^ 8 = (gammaTau⁻¹) ^ 8 * ((Real.exp (x / 2))⁻¹) ^ 8 := by
    simp only [mul_inv, mul_pow]
  have e2 : ((Real.exp (x / 2))⁻¹) ^ 8 * Real.exp (x / 2) ^ 2 ≤ 1 := by
    rw [inv_pow, ← div_eq_inv_mul, div_le_one (by positivity)]
    exact pow_le_pow_right₀ hE1 (by norm_num)
  have hkey : ((gammaTau * Real.exp (x / 2))⁻¹) ^ 8 * x ^ r ≤ (gammaTau⁻¹) ^ 8 * (r.factorial : ℝ) := by
    calc ((gammaTau * Real.exp (x / 2))⁻¹) ^ 8 * x ^ r
        ≤ (gammaTau⁻¹) ^ 8 * ((Real.exp (x / 2))⁻¹) ^ 8 * ((r.factorial : ℝ) * Real.exp (x / 2) ^ 2) := by
          rw [e1]; exact mul_le_mul_of_nonneg_left hxr (by positivity)
      _ = (gammaTau⁻¹) ^ 8 * (r.factorial : ℝ) * (((Real.exp (x / 2))⁻¹) ^ 8 * Real.exp (x / 2) ^ 2) := by ring
      _ ≤ (gammaTau⁻¹) ^ 8 * (r.factorial : ℝ) * 1 := by gcongr
      _ = _ := mul_one _
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hx0 r)]; exact hkey

/-- **Large regime**: `L(1 - φ_kill(iτ₀(x - s); a)) ∈ SymW [1/2, ∞)` of weight `1` (`τ₀ ≳ e^{x/2}`). -/
theorem block_large : USym NHyp (fun _ => Ici (1 / 2 : ℝ)) (fun _ _ => 1)
    (fun p x => p.L (1 - phiKill p.a ((tau0 (x - p.s) : ℂ) * Complex.I))) := by
  obtain ⟨C, hC0, hC⟩ := phiKill_tsymbol
  obtain ⟨A, hA0, hcomp⟩ := comp_tau0_shift
  have hγ := gammaTau_pos
  refine ⟨fun r => chainM C (fun j => (j : ℝ)) A 1 r 0 * 2 ^ r * ((gammaTau⁻¹) ^ 8 * (r.factorial : ℝ)), fun p hp => ?_⟩
  have hs4 := NHyp.s_le hp
  obtain ⟨hL, ha, ha1, hx₀, hx₀h, hs⟩ := hp
  set om : ℝ → ℝ := fun x => ((gammaTau * Real.exp (x / 2))⁻¹) ^ 8 with hom
  have hbase : ∀ j, ∀ x, (1 / 2 : ℝ) ≤ x → |tau0 (x - p.s) ^ j * iteratedDeriv j
      (fun t : ℝ => p.L (1 - phiKill p.a ((t : ℂ) * Complex.I))) (tau0 (x - p.s))| ≤ C j * om x := by
    intro j x hx
    have hxs : 0 < x - p.s := by linarith [(abs_le.mp hs4).2]
    have h1 := (hC p.a (tau0 (x - p.s)) ha (tau0_pos hxs) p.L hL j).2
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (hC0 j))
    refine (min_le_right _ _).trans ?_
    have hτ := tau0_ge_gamma hx hs4
    have hE : 0 < gammaTau * Real.exp (x / 2) := by positivity
    have hτ0 : 0 < tau0 (x - p.s) := tau0_pos hxs
    refine pow_le_pow_left₀ (by positivity) ?_ 8
    calc p.a / tau0 (x - p.s) ≤ 1 / tau0 (x - p.s) := by gcongr
      _ = (tau0 (x - p.s))⁻¹ := one_div _
      _ ≤ (gammaTau * Real.exp (x / 2))⁻¹ := inv_anti₀ hE hτ
  have hb := hcomp (x₀ := 1 / 2) (s := p.s) (g := fun t : ℝ => p.L (1 - phiKill p.a ((t : ℂ) * Complex.I))) (om := om) (P := C)
    (by norm_num) (by linarith [hs4]) (contDiff_L_one_sub_phiKill ha p.L).contDiffOn hC0
    (fun x _ => by simp only [hom]; positivity) hbase
  refine ⟨fun x hx => by have : (1 / 2 : ℝ) ≤ x := hx; linarith, ?_, fun r => ?_, fun x _ => zero_le_one, fun r x hx => ?_⟩
  · refine ⟨Ioi p.s, isOpen_Ioi, fun x hx => ?_, contDiffOn_comp_tau0 (contDiff_L_one_sub_phiKill ha p.L) p.s⟩
    have : (1 / 2 : ℝ) ≤ x := hx
    exact mem_Ioi.mpr (by linarith [(abs_le.mp hs4).2])
  · have := chainM_nonneg (κ := fun j : ℕ => (j : ℝ)) (A := A) (B := 1) hC0 r 0
    positivity
  · have hx' : (1 / 2 : ℝ) ≤ x := hx
    have hx0 : 0 < x := by linarith
    have := hb r x hx'
    refine this.trans ?_
    have hl : lamL x ^ r ≤ 2 ^ r := pow_le_pow_left₀ (lamL_nonneg x) (lamL_le_two hx') r
    have hM := chainM_nonneg (κ := fun j : ℕ => (j : ℝ)) (A := A) (B := 1) hC0 r 0
    have hom0 : 0 ≤ om x := by simp only [hom]; positivity
    have hom2 : om x ≤ (gammaTau⁻¹) ^ 8 * (r.factorial : ℝ) * (x ^ r)⁻¹ := om2_decay hx' r
    calc chainM C (fun j => (j : ℝ)) A 1 r 0 * om x * lamL x ^ r
        ≤ chainM C (fun j => (j : ℝ)) A 1 r 0 * ((gammaTau⁻¹) ^ 8 * (r.factorial : ℝ) * (x ^ r)⁻¹) * 2 ^ r :=
          mul_le_mul (mul_le_mul_of_nonneg_left hom2 hM) hl (pow_nonneg (lamL_nonneg x) r) (by positivity)
      _ = _ := by ring

/-- info: 'FormalResearch.SignUncertainty.FctSym.block_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms block_small

/-- info: 'FormalResearch.SignUncertainty.FctSym.block_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms block_large

end FormalResearch.SignUncertainty.FctSym
