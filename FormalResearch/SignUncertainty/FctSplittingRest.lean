/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSplittingConj
public import FormalResearch.SignUncertainty.FctSplittingCont
public import FormalResearch.SignUncertainty.FctSplittingEdgeDeriv
public import FormalResearch.SignUncertainty.FctSplittingLeftC2
public import FormalResearch.SignUncertainty.FctSplittingNearDeriv

/-!
# `FctSplittingStmt` and `WarpLeftFar` from the remaining `fct:splitting` clauses

Paper I (`constant_terms_five.tex`), `fct:splitting` (1)-(3) and `fct:s4-proof` Step 1.
Holomorphy (`fctPhiHat_differentiableOn`), real symmetry (`fctPhiHat_conj`), continuity on `S̄`
and corner bound `O(ζ³)` (`fctPhiHat_cont_cubic`), right-edge derivatives (`fctPhiHat_right_deriv`,
`(fct:Eminus-edge)`), `C²` left-edge trace off `0` (`fctPhiHat_left_c2`), small-`|τ|` left-edge
derivatives (`fctPhiHat_left_near_deriv`, `(fct:Psi-edge)`), and the `F_-`/`q₁` left-edge tail
(`fctPhiHat_left_tail_EJ`, `(fct:Fminus-edge)`) are **proved** from `FctDescentStmt` (`K₄ ≥ 1`).

The remaining open clauses of `fct:splitting` (2)-(3) are collected in `SplittingRest` /
`FctSplittingRestStmt`:
* `loglog` (`|Φ̂_c| ≤ M log log(4 + |τ|)` on `S̄`);
* `FctPsiFarStmt` (`‖∂_τ^j Ψ_c(iτ)‖ ≤ M (1 + |τ|)^N e^{-π|τ|}` for `|τ| ≥ 1/2`, `fct:splitting` (3)).

`fctSplitting_of_rest` produces `FctSplittingStmt (fctPhiHat h)` and `fctWarp_far_of_rest`
produces the separated large-`|τ|` left-edge bound `WarpLeftFar` used by `fctWarp_admissible`.

Class: proved from `FctDescentStmt` (named input) and `FctSplittingRestStmt` (named input).
-/
@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

/-- The clause of `SplittingData Φ` not yet proved from the descent bound:
the `log log` growth on `S̄`.
(Holomorphy, real symmetry, continuity on `S̄`, `O(ζ³)` at `0`, `C²` left-edge trace off `0`,
`(fct:Psi-edge)` small-`|τ|` left-edge derivatives, and `(fct:Eminus-edge)` right-edge
derivative bounds are **proved** from `FctDescentStmt`.) -/
structure SplittingRest (Φ : ℂ → ℂ) : Prop where
  loglog : ∃ M : ℝ, 0 ≤ M ∧ ∀ ζ ∈ closedStrip, ‖Φ ζ‖ ≤ M * Real.log (Real.log (4 + |ζ.im|))

/-- **`fct:splitting` (3), far-edge trace bound for `Ψ_c`** (`constant_terms_five.tex`, line 1007):
for `c ≥ c₀`, `ε = ±1`, and `|τ| ≥ 1/2`, `‖∂_τ^j Ψ_c(iτ)‖ ≤ M (1 + |τ|)^N e^{-π|τ|}` (`j = 0, 1, 2`). -/
def FctPsiFarStmt {K4 : ℝ} (h : FctWarpSolveStmt K4) : Prop :=
  ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
    let ψ := fun t : ℝ => fctPsi K4 ε c (fctWarpL1 h ε c) (fctWarpAlpha h ε c) ((t : ℂ) * Complex.I)
    ∃ (N : ℕ) (M : ℝ), 0 ≤ M ∧ ∀ τ : ℝ, 1 / 2 ≤ |τ| →
      ‖ψ τ‖ ≤ M * (1 + |τ|) ^ N * Real.exp (-(π * |τ|)) ∧
      ‖deriv ψ τ‖ ≤ M * (1 + |τ|) ^ N * Real.exp (-(π * |τ|)) ∧
      ‖deriv (deriv ψ) τ‖ ≤ M * (1 + |τ|) ^ N * Real.exp (-(π * |τ|))

/-- The remaining open clauses of `fct:splitting` (2)-(3) for `fctPhiHat h` / `fctPsi`. -/
def FctSplittingRestStmt {K4 : ℝ} (h : FctWarpSolveStmt K4) : Prop :=
  (∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → SplittingRest (fctPhiHat h ε c)) ∧
  FctPsiFarStmt h

/-- **`FctSplittingStmt` from the remaining clauses**: holomorphy, real symmetry, continuity on `S̄`,
`Φ̂_c = O(ζ³)`, and right-edge derivatives `(fct:Eminus-edge)` are proved from `FctDescentStmt` (`K₄ ≥ 1`). -/
theorem fctSplitting_of_rest {K4 : ℝ} (hK4 : 1 ≤ K4) {h : FctWarpSolveStmt K4} (hD : FctDescentStmt h)
    (hR : FctSplittingRestStmt h) : FctSplittingStmt (fctPhiHat h) := by
  obtain ⟨ch, hh⟩ := fctPhiHat_differentiableOn hK4 hD
  obtain ⟨cc, hc⟩ := fctPhiHat_conj hK4 hD
  obtain ⟨ct, ht⟩ := fctPhiHat_cont_cubic hK4 hD
  obtain ⟨crt, hrt⟩ := fctPhiHat_right_deriv hK4 hD
  obtain ⟨cc2, hc2⟩ := fctPhiHat_left_c2 hK4 hD
  obtain ⟨cld, hld⟩ := fctPhiHat_left_near_deriv hK4 hD
  obtain ⟨cr, hr⟩ := hR.1
  refine ⟨max (max (max ch cc) (max ct crt)) (max (max cc2 cld) cr), fun ε c hε hcb => ?_⟩
  have hr' := hr ε c hε ((le_max_right _ _).trans (le_max_right _ _) |>.trans hcb)
  have hld' := hld ε c hε ((le_max_right _ _).trans (le_max_left _ _) |>.trans (le_max_right _ _) |>.trans hcb)
  have hrt' := hrt ε c hε ((le_max_right _ _).trans (le_max_right _ _) |>.trans (le_max_left _ _) |>.trans hcb)
  have ht' := ht ε c hε ((le_max_left _ _).trans (le_max_right _ _) |>.trans (le_max_left _ _) |>.trans hcb)
  obtain ⟨Mll, hMll, hloglog⟩ := hr'.loglog
  obtain ⟨Mcub, hMcub, hcub⟩ := ht'.2
  obtain ⟨Mld, hMld, hl⟩ := hld'
  obtain ⟨Mrt, hMrt, hrtd⟩ := hrt'
  refine ⟨hh ε c hε ((le_max_left _ _).trans (le_max_left _ _) |>.trans (le_max_left _ _) |>.trans hcb), ht'.1,
    hc ε c hε ((le_max_right _ _).trans (le_max_left _ _) |>.trans (le_max_left _ _) |>.trans hcb),
    hc2 ε c hε ((le_max_left _ _).trans (le_max_left _ _) |>.trans (le_max_right _ _) |>.trans hcb),
    ⟨max (max Mll Mcub) (max Mld Mrt), by positivity, ?_, ?_, ?_, ?_⟩⟩
  · intro ζ hζ
    have hnn : 0 ≤ Real.log (Real.log (4 + |ζ.im|)) := by
      have : 1 ≤ Real.log (4 + |ζ.im|) :=
        Real.le_log_iff_exp_le (by linarith [abs_nonneg ζ.im]) |>.mpr
          (Real.exp_one_lt_d9.le.trans (by linarith [abs_nonneg ζ.im]))
      exact Real.log_nonneg this
    exact (hloglog ζ hζ).trans (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) hnn)
  · intro ζ hζ hb
    exact (hcub ζ hζ hb).trans (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) (by positivity))
  · intro τ hτ hτ1
    obtain ⟨a, b⟩ := hl τ hτ hτ1
    have hMle : Mld ≤ max (max Mll Mcub) (max Mld Mrt) := (le_max_left _ _).trans (le_max_right _ _)
    exact ⟨a.trans (mul_le_mul_of_nonneg_right hMle (by positivity)),
      b.trans (mul_le_mul_of_nonneg_right hMle (abs_nonneg _))⟩
  · intro τ
    obtain ⟨a, b⟩ := hrtd τ
    have hMle : Mrt ≤ max (max Mll Mcub) (max Mld Mrt) := (le_max_right _ _).trans (le_max_right _ _)
    exact ⟨a.trans hMle, b.trans hMle⟩

private lemma ej_far_poly_exp {f : ℝ → ℂ} {a M : ℝ} {N : ℕ}
    (hf : EJ f a N 1 M) (ha : -3 ≤ a) (ha0 : a ≤ 0) :
    ∀ τ : ℝ, 1 / 2 ≤ |τ| →
      ‖f τ‖ ≤ (32 * M) * (1 + |τ|) ^ (N + 2) * Real.exp (-(π * |τ|)) ∧
      ‖deriv f τ‖ ≤ (32 * M) * (1 + |τ|) ^ (N + 2) * Real.exp (-(π * |τ|)) ∧
      ‖deriv (deriv f) τ‖ ≤ (32 * M) * (1 + |τ|) ^ (N + 2) * Real.exp (-(π * |τ|)) := by
  intro τ hτ
  have hτ' : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ; linarith
  have h0 : 0 < |τ| := abs_pos.mpr hτ'
  have hM := hf.hM
  have key : ∀ j : ℕ, j ≤ 2 → ejW a N 1 j τ ≤ 32 * ((1 + |τ|) ^ (N + 2) * Real.exp (-(π * |τ|))) := by
    intro j hj
    unfold ejW
    have hpa : |τ| ^ a ≤ 8 := by
      calc |τ| ^ a ≤ (1 / 2 : ℝ) ^ a := Real.rpow_le_rpow_of_nonpos (by norm_num) hτ ha0
        _ ≤ (1 / 2 : ℝ) ^ (-3 : ℝ) := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) ha
        _ = 8 := by norm_num
    have hpn : |τ| ^ (-(j : ℝ)) ≤ 4 := by
      rw [Real.rpow_neg h0.le, Real.rpow_natCast]
      have hpow : (1 / 4 : ℝ) ≤ |τ| ^ j := by
        rcases le_or_gt |τ| 1 with h | h
        · calc (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 := by norm_num
            _ ≤ (1 / 2 : ℝ) ^ j := pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
            _ ≤ |τ| ^ j := pow_le_pow_left₀ (by norm_num) hτ j
        · have : 1 ≤ |τ| ^ j := one_le_pow₀ h.le
          linarith
      exact inv_le_of_inv_le₀ (by norm_num : (0 : ℝ) < 4) (by norm_num; exact hpow)
    have hrw : |τ| ^ (a - (j : ℝ)) = |τ| ^ a * |τ| ^ (-(j : ℝ)) := by
      rw [← Real.rpow_add h0]; ring_nf
    have hpoly : (1 + |τ|) ^ (N + j) ≤ (1 + |τ|) ^ (N + 2) := pow_le_pow_right₀ (by linarith) (by omega)
    have hexp : Real.exp (-(π * 1 * |τ|)) = Real.exp (-(π * |τ|)) := by ring_nf
    rw [hrw, hexp]
    have hp2 : |τ| ^ a * |τ| ^ (-(j : ℝ)) ≤ 32 :=
      (mul_le_mul hpa hpn (by positivity) (by positivity)).trans (by norm_num)
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul hp2 hpoly (by positivity) (by positivity)) (Real.exp_pos (-(π * |τ|))).le).trans_eq (by ring)
  refine ⟨?_, ?_, ?_⟩
  · calc ‖f τ‖ ≤ M * ejW a N 1 0 τ := hf.b0 τ hτ'
      _ ≤ M * (32 * ((1 + |τ|) ^ (N + 2) * Real.exp (-(π * |τ|)))) := by gcongr; exact key 0 (by norm_num)
      _ = _ := by ring
  · calc ‖deriv f τ‖ ≤ M * ejW a N 1 1 τ := hf.b1 τ hτ'
      _ ≤ M * (32 * ((1 + |τ|) ^ (N + 2) * Real.exp (-(π * |τ|)))) := by gcongr; exact key 1 (by norm_num)
      _ = _ := by ring
  · calc ‖deriv (deriv f) τ‖ ≤ M * ejW a N 1 2 τ := hf.b2 τ hτ'
      _ ≤ M * (32 * ((1 + |τ|) ^ (N + 2) * Real.exp (-(π * |τ|)))) := by gcongr; exact key 2 (by norm_num)
      _ = _ := by ring

/-- **Separated far-edge trace bound `WarpLeftFar` from `FctSplittingRestStmt` and `FctDescentStmt`**
(`fct:s4-proof` Step 1 for `|τ| ≥ 1/2`): decomposes `Φ̂_c(iτ) D_{τ₁}(iτ) (H_*/G_ε)(iτ) = (c/N_c) Ψ_c(iτ) + tail(τ) D_{τ₁}(iτ) (H_*/G_ε)(iτ)`,
using `FctPsiFarStmt` for `Ψ_c` and `fctPhiHat_left_tail_EJ` (`(fct:Fminus-edge)`) for the tail. -/
theorem fctWarp_far_of_rest {K4 : ℝ} (hK4 : 1 ≤ K4) {h : FctWarpSolveStmt K4} (hD : FctDescentStmt h)
    (hR : FctSplittingRestStmt h) :
    ∃ c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
      WarpLeftFar ε (fctPhiHat h ε c) (fctDcomp K4 (fctWarpAlpha h) ε c) := by
  obtain ⟨Cz, cz, hz⟩ := fctWarpZero_of_solve h
  obtain ⟨c0D, hcD⟩ := fctDcomp_compData hK4 ⟨Cz, cz, fun ε c hε hc => (hz ε c hε hc).2⟩
  obtain ⟨c0N, hNc⟩ := fctNcC_inv_bound hK4 hD
  obtain ⟨c0T, hTail⟩ := fctPhiHat_left_tail_EJ hK4 hD
  obtain ⟨c0R, hC2⟩ := fctPhiHat_left_c2 hK4 hD
  obtain ⟨c0P, hPsi⟩ := hR.2
  refine ⟨max (max (max c0D c0N) c0T) (max c0R c0P), fun ε c hε hc => ?_⟩
  have hDD := hcD ε c hε (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _) |>.trans hc)
  have hNc_inv := hNc ε c hε (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _) |>.trans hc)
  obtain ⟨Mt, hTail_EJ⟩ := hTail ε c hε ((le_max_right _ _).trans (le_max_left _ _) |>.trans hc)
  have hc2' := hC2 ε c hε ((le_max_left _ _).trans (le_max_right _ _) |>.trans hc)
  obtain ⟨N1, M1, hM10, hPsi'⟩ := hPsi ε c hε ((le_max_right _ _).trans (le_max_right _ _) |>.trans hc)
  set L1 := fctWarpL1 h ε c
  set α := fctWarpAlpha h ε c
  set Nc := fctNcC K4 ε c L1 α
  set Dd := fctDcomp K4 (fctWarpAlpha h) ε c
  obtain ⟨P, hP0, hE⟩ := hDD.env
  obtain ⟨MZ, hZE⟩ := ejZE ε
  have hDe : EJ (fun τ : ℝ => Dd ((τ : ℂ) * Complex.I)) 0 0 0 P :=
    EJ.of_env2 hE hP0 0 (fun _ => by simp)
  have hDHG_EJ : EJ (fun τ : ℝ => Dd ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)) (-(5 / 2)) 10 1
      (4 * (4 * (4 * P * MZ) * 9) * 9) := by
    have hbase := (((hDe.mul hZE).mul edgeR_EJ).mul edgeS_EJ).cast (a' := -(5 / 2)) (b' := 1) (by norm_num) (by norm_num)
    have hDHG_eq : (fun s : ℝ => Dd ((s : ℂ) * Complex.I) * ctHG ε ((s : ℂ) * Complex.I)) =
        fun s : ℝ => Dd ((s : ℂ) * Complex.I) *
          (uctSeedZ ε ((s : ℂ) * Complex.I) * Complex.exp (-outerHbar ((s : ℂ) * Complex.I))) *
          edgeR s * edgeS s := funext fun s => by
      rw [ctHG_edge]; ring
    rw [hDHG_eq]
    exact hbase
  have hT2_EJ := (hTail_EJ.mul hDHG_EJ).cast (a' := -(5 / 2)) (b' := 1) (by norm_num) (by norm_num)
  set t1 : ℝ → ℂ := fun τ => ((c : ℂ) / Nc) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I)
  set t2 : ℝ → ℂ := fun τ => fctLeftTail K4 ε c L1 α τ * (Dd ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I))
  set g : ℝ → ℂ := fun τ => fctPhiHat h ε c ((τ : ℂ) * Complex.I) * Dd ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)
  have hg_split : ∀ τ : ℝ, τ ≠ 0 → g τ = t1 τ + t2 τ := fun τ hτ => by
    have hDne : Dd ((τ : ℂ) * Complex.I) ≠ 0 := fctDcompAt_ne_zero _
    have hHne : ctHG ε ((τ : ℂ) * Complex.I) ≠ 0 :=
      ctHG_ne_zero_of_closed_band ε (by simp) (by simp) (by simp [hτ])
    have hhat : fctPhiHat h ε c ((τ : ℂ) * Complex.I) =
        fctPhiC K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc + fctLeftTail K4 ε c L1 α τ :=
      fctPhiHatAt_left_eq_add_tail K4 ε c L1 α τ
    dsimp only [g, t1, t2]
    rw [hhat, add_mul, add_mul, mul_assoc (fctLeftTail K4 ε c L1 α τ)]
    congr 1
    show (fctPhiC K4 ε c L1 α ((τ : ℂ) * Complex.I) / Nc) * Dd ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I) = _
    unfold fctPhiC
    change ((c : ℂ) * fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I) / (Dd ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I)) / Nc) *
        Dd ((τ : ℂ) * Complex.I) * ctHG ε ((τ : ℂ) * Complex.I) = _
    field_simp
  have hg_c2 : ContDiffOn ℝ 2 g {τ : ℝ | τ ≠ 0} := hc2'.mul hDHG_EJ.c2 |>.congr fun τ _ => by
    dsimp only [g]; ring
  have ht2_c2 : ContDiffOn ℝ 2 t2 {τ : ℝ | τ ≠ 0} := hT2_EJ.c2
  have ht1_c2 : ContDiffOn ℝ 2 t1 {τ : ℝ | τ ≠ 0} :=
    (hg_c2.sub ht2_c2).congr fun τ hτ => by rw [hg_split τ hτ]; ring
  have hS : IsOpen {τ : ℝ | τ ≠ 0} := isOpen_ne
  have hd_diff : ∀ {f : ℝ → ℂ}, ContDiffOn ℝ 2 f {τ : ℝ | τ ≠ 0} → ∀ τ : ℝ, τ ≠ 0 →
      DifferentiableAt ℝ f τ ∧ DifferentiableAt ℝ (deriv f) τ := fun {f} hf τ hτ =>
    ⟨(hf.differentiableOn (by norm_num) τ hτ).differentiableAt (hS.mem_nhds hτ),
     ((hf.deriv_of_isOpen hS (m := 1) (by norm_num) : ContDiffOn ℝ 1 (deriv f) _).differentiableOn
        (by norm_num) τ hτ).differentiableAt (hS.mem_nhds hτ)⟩
  set M2 := 4 * Mt * (4 * (4 * (4 * P * MZ) * 9) * 9)
  have ht2_far := ej_far_poly_exp hT2_EJ (by norm_num) (by norm_num)
  refine ⟨max N1 13, 2 * |c| * M1 + 32 * M2, by have := hT2_EJ.hM; positivity, fun τ hτ => ?_⟩
  have hτ' : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ; linarith
  obtain ⟨ht1_d, ht1_dd⟩ := hd_diff ht1_c2 τ hτ'
  obtain ⟨ht2_d, ht2_dd⟩ := hd_diff ht2_c2 τ hτ'
  have hg_d1 : deriv g τ = deriv t1 τ + deriv t2 τ := by
    have hev : g =ᶠ[𝓝 τ] fun t => t1 t + t2 t :=
      Filter.eventually_of_mem (hS.mem_nhds hτ') fun t ht => hg_split t ht
    rw [hev.deriv_eq]
    exact (ht1_d.hasDerivAt.add ht2_d.hasDerivAt).deriv
  have hg_d2 : deriv (deriv g) τ = deriv (deriv t1) τ + deriv (deriv t2) τ := by
    have hev1 : deriv g =ᶠ[𝓝 τ] fun t => deriv t1 t + deriv t2 t := by
      filter_upwards [hS.mem_nhds hτ'] with t ht
      have hsub : g =ᶠ[𝓝 t] fun s => t1 s + t2 s :=
        Filter.eventually_of_mem (hS.mem_nhds ht) fun s hs => hg_split s hs
      rw [hsub.deriv_eq]
      exact ((hd_diff ht1_c2 t ht).1.hasDerivAt.add (hd_diff ht2_c2 t ht).1.hasDerivAt).deriv
    rw [hev1.deriv_eq]
    exact (ht1_dd.hasDerivAt.add ht2_dd.hasDerivAt).deriv
  have hk_bd : ‖(c : ℂ) / Nc‖ ≤ 2 * |c| := by
    rw [div_eq_mul_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |c| * ‖Nc⁻¹‖ ≤ |c| * 2 := mul_le_mul_of_nonneg_left hNc_inv (abs_nonneg _)
      _ = 2 * |c| := by ring
  obtain ⟨hp0, hp1, hp2⟩ := hPsi' τ hτ
  obtain ⟨hq0, hq1, hq2⟩ := ht2_far τ hτ
  have hpow1 : (1 + |τ|) ^ N1 ≤ (1 + |τ|) ^ max N1 13 := pow_le_pow_right₀ (by linarith [abs_nonneg τ]) (le_max_left _ _)
  have hpow2 : (1 + |τ|) ^ 13 ≤ (1 + |τ|) ^ max N1 13 := pow_le_pow_right₀ (by linarith [abs_nonneg τ]) (le_max_right _ _)
  have hexp0 : 0 ≤ Real.exp (-(π * |τ|)) := (Real.exp_pos _).le
  have ht1_0 : ‖t1 τ‖ ≤ 2 * |c| * M1 * (1 + |τ|) ^ max N1 13 * Real.exp (-(π * |τ|)) := by
    dsimp only [t1]; rw [norm_mul]
    calc ‖(c : ℂ) / Nc‖ * ‖fctPsi K4 ε c L1 α ((τ : ℂ) * Complex.I)‖
        ≤ (2 * |c|) * (M1 * (1 + |τ|) ^ N1 * Real.exp (-(π * |τ|))) :=
          mul_le_mul hk_bd hp0 (norm_nonneg _) (by positivity)
      _ ≤ (2 * |c|) * (M1 * (1 + |τ|) ^ max N1 13 * Real.exp (-(π * |τ|))) := by gcongr
      _ = _ := by ring
  have ht1_1 : ‖deriv t1 τ‖ ≤ 2 * |c| * M1 * (1 + |τ|) ^ max N1 13 * Real.exp (-(π * |τ|)) := by
    have heq : deriv t1 τ = ((c : ℂ) / Nc) * deriv (fun s : ℝ => fctPsi K4 ε c L1 α ((s : ℂ) * Complex.I)) τ :=
      deriv_const_mul_field ((c : ℂ) / Nc)
    rw [heq, norm_mul]
    calc ‖(c : ℂ) / Nc‖ * ‖deriv (fun s : ℝ => fctPsi K4 ε c L1 α ((s : ℂ) * Complex.I)) τ‖
        ≤ (2 * |c|) * (M1 * (1 + |τ|) ^ N1 * Real.exp (-(π * |τ|))) :=
          mul_le_mul hk_bd hp1 (norm_nonneg _) (by positivity)
      _ ≤ (2 * |c|) * (M1 * (1 + |τ|) ^ max N1 13 * Real.exp (-(π * |τ|))) := by gcongr
      _ = _ := by ring
  have ht1_2 : ‖deriv (deriv t1) τ‖ ≤ 2 * |c| * M1 * (1 + |τ|) ^ max N1 13 * Real.exp (-(π * |τ|)) := by
    have h1 : deriv t1 = fun s : ℝ => ((c : ℂ) / Nc) * deriv (fun u : ℝ => fctPsi K4 ε c L1 α ((u : ℂ) * Complex.I)) s :=
      funext fun s => deriv_const_mul_field ((c : ℂ) / Nc)
    rw [h1]
    have heq : deriv (fun s : ℝ => ((c : ℂ) / Nc) * deriv (fun u : ℝ => fctPsi K4 ε c L1 α ((u : ℂ) * Complex.I)) s) τ =
        ((c : ℂ) / Nc) * deriv (deriv (fun u : ℝ => fctPsi K4 ε c L1 α ((u : ℂ) * Complex.I))) τ :=
      deriv_const_mul_field ((c : ℂ) / Nc)
    rw [heq, norm_mul]
    calc ‖(c : ℂ) / Nc‖ * ‖deriv (deriv (fun u : ℝ => fctPsi K4 ε c L1 α ((u : ℂ) * Complex.I))) τ‖
        ≤ (2 * |c|) * (M1 * (1 + |τ|) ^ N1 * Real.exp (-(π * |τ|))) :=
          mul_le_mul hk_bd hp2 (norm_nonneg _) (by positivity)
      _ ≤ (2 * |c|) * (M1 * (1 + |τ|) ^ max N1 13 * Real.exp (-(π * |τ|))) := by gcongr
      _ = _ := by ring
  have hM2nn : 0 ≤ M2 := hT2_EJ.hM
  have ht2_0 : ‖t2 τ‖ ≤ 32 * M2 * (1 + |τ|) ^ max N1 13 * Real.exp (-(π * |τ|)) := by
    calc ‖t2 τ‖ ≤ 32 * M2 * (1 + |τ|) ^ (11 + 2) * Real.exp (-(π * |τ|)) := hq0
      _ ≤ 32 * M2 * (1 + |τ|) ^ max N1 13 * Real.exp (-(π * |τ|)) := by gcongr
  have ht2_1 : ‖deriv t2 τ‖ ≤ 32 * M2 * (1 + |τ|) ^ max N1 13 * Real.exp (-(π * |τ|)) := by
    calc ‖deriv t2 τ‖ ≤ 32 * M2 * (1 + |τ|) ^ (11 + 2) * Real.exp (-(π * |τ|)) := hq1
      _ ≤ 32 * M2 * (1 + |τ|) ^ max N1 13 * Real.exp (-(π * |τ|)) := by gcongr
  have ht2_2 : ‖deriv (deriv t2) τ‖ ≤ 32 * M2 * (1 + |τ|) ^ max N1 13 * Real.exp (-(π * |τ|)) := by
    calc ‖deriv (deriv t2) τ‖ ≤ 32 * M2 * (1 + |τ|) ^ (11 + 2) * Real.exp (-(π * |τ|)) := hq2
      _ ≤ 32 * M2 * (1 + |τ|) ^ max N1 13 * Real.exp (-(π * |τ|)) := by gcongr
  refine ⟨?_, ?_, ?_⟩
  · show ‖g τ‖ ≤ _
    rw [hg_split τ hτ']
    calc ‖t1 τ + t2 τ‖ ≤ ‖t1 τ‖ + ‖t2 τ‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  · show ‖deriv g τ‖ ≤ _
    rw [hg_d1]
    calc ‖deriv t1 τ + deriv t2 τ‖ ≤ ‖deriv t1 τ‖ + ‖deriv t2 τ‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  · show ‖deriv (deriv g) τ‖ ≤ _
    rw [hg_d2]
    calc ‖deriv (deriv t1) τ + deriv (deriv t2) τ‖ ≤ ‖deriv (deriv t1) τ‖ + ‖deriv (deriv t2) τ‖ := norm_add_le _ _
      _ ≤ _ := by linarith

/-- info: 'FormalResearch.SignUncertainty.fctSplitting_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctSplitting_of_rest

/-- info: 'FormalResearch.SignUncertainty.fctWarp_far_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctWarp_far_of_rest

end FormalResearch.SignUncertainty
