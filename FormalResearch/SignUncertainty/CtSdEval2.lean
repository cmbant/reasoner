module

public import FormalResearch.SignUncertainty.CtSdEval1

/-!
# Amplitude classes for the steepest-descent evaluation (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3.  **Proved.**
The standard class `B3 A B C` of amplitudes `h` with `|h(w)| ≤ A|w|^{-1/2} + B|w|^{1/2} + C|w|^{3/2}` along a chain
(continuous away from the chain's start), closed under sums and constant multiples, with integrable `h e^{iPh}`,
linear chain integral, and `|∫_Γ h e^{iPh}| ≤ A m_{-1/2} + B m_{1/2} + C m_{3/2}`.  Also the amplitude hypotheses
`SdAmp` on the pulled-back symbol `Q`, the Binet factor `E`, and the bracket `1 + (s²+a)Q`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real

namespace FormalResearch.SignUncertainty.CtSd

/-- The standard amplitude class `A|w|^{-1/2} + B|w|^{1/2} + C|w|^{3/2}`. -/
def Chain3.B3 {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) (h : ℂ → ℂ) (A B C : ℝ) : Prop :=
  0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C ∧ ch.Bd h A (-(1 / 2)) B (1 / 2) C (3 / 2)

lemma Chain3.B3.of_pointwise {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) {h : ℂ → ℂ} {A B C : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hc : ∀ z ∈ ball (0 : ℂ) R₀, 0 ≤ z.re → z ≠ 0 → ContinuousAt h z)
    (hb : ∀ z ∈ ball (0 : ℂ) R₀, 0 ≤ z.re → z ≠ 0 →
      ‖h z‖ ≤ A * ‖z‖ ^ (-(1 / 2 : ℝ)) + B * ‖z‖ ^ (1 / 2 : ℝ) + C * ‖z‖ ^ (3 / 2 : ℝ)) :
    ch.B3 h A B C :=
  ⟨hA, hB, hC, Chain3.Bd.of_pointwise ch hc hb⟩

lemma PieceBd.add {q : Piece} {h g : ℂ → ℂ} {K1 α1 K2 α2 K3 α3 L1 L2 L3 : ℝ}
    (hh : PieceBd h q K1 α1 K2 α2 K3 α3) (hg : PieceBd g q L1 α1 L2 α2 L3 α3) :
    PieceBd (fun w => h w + g w) q (K1 + L1) α1 (K2 + L2) α2 (K3 + L3) α3 := by
  refine ⟨hh.1.add hg.1, fun t ht => ?_⟩
  have := norm_add_le (h (q.pt t)) (g (q.pt t))
  have a := hh.2 t ht
  have b := hg.2 t ht
  show ‖h (q.pt t) + g (q.pt t)‖ ≤ _
  linarith only [this, a, b]

lemma PieceBd.smul {q : Piece} {h : ℂ → ℂ} {K1 α1 K2 α2 K3 α3 : ℝ} (k : ℂ)
    (hh : PieceBd h q K1 α1 K2 α2 K3 α3) :
    PieceBd (fun w => k * h w) q (‖k‖ * K1) α1 (‖k‖ * K2) α2 (‖k‖ * K3) α3 := by
  refine ⟨continuousOn_const.mul hh.1, fun t ht => ?_⟩
  have a := mul_le_mul_of_nonneg_left (hh.2 t ht) (norm_nonneg k)
  show ‖k * h (q.pt t)‖ ≤ _
  rw [norm_mul]
  linarith only [a]

lemma Chain3.B3.add {R₀ : ℝ} {p : ℂ} {ch : Chain3 R₀ p} {h g : ℂ → ℂ} {A B C A' B' C' : ℝ}
    (hh : ch.B3 h A B C) (hg : ch.B3 g A' B' C') : ch.B3 (fun w => h w + g w) (A + A') (B + B') (C + C') :=
  ⟨by linarith [hh.1, hg.1], by linarith [hh.2.1, hg.2.1], by linarith [hh.2.2.1, hg.2.2.1],
    (hh.2.2.2.1).add (hg.2.2.2.1), (hh.2.2.2.2.1).add (hg.2.2.2.2.1), (hh.2.2.2.2.2).add (hg.2.2.2.2.2)⟩

lemma Chain3.B3.smul {R₀ : ℝ} {p : ℂ} {ch : Chain3 R₀ p} {h : ℂ → ℂ} {A B C : ℝ} (k : ℂ)
    (hh : ch.B3 h A B C) : ch.B3 (fun w => k * h w) (‖k‖ * A) (‖k‖ * B) (‖k‖ * C) :=
  ⟨mul_nonneg (norm_nonneg k) hh.1, mul_nonneg (norm_nonneg k) hh.2.1, mul_nonneg (norm_nonneg k) hh.2.2.1,
    (hh.2.2.2.1).smul k, (hh.2.2.2.2.1).smul k, (hh.2.2.2.2.2).smul k⟩

theorem Chain3.B3.intE_add {R₀ : ℝ} {p : ℂ} {ch : Chain3 R₀ p} {U : ℝ} {h g : ℂ → ℂ} {A B C A' B' C' : ℝ}
    (hh : ch.B3 h A B C) (hg : ch.B3 g A' B' C') :
    ch.intE U (fun w => h w + g w) = ch.intE U h + ch.intE U g :=
  Chain3.intE_add ch ⟨hh.1, hh.2.1, hh.2.2.1⟩ ⟨hg.1, hg.2.1, hg.2.2.1⟩ le_rfl (by norm_num) (by norm_num)
    le_rfl (by norm_num) (by norm_num) hh.2.2.2 hg.2.2.2

theorem Chain3.B3.norm_intE_le {R₀ : ℝ} {p : ℂ} {ch : Chain3 R₀ p} {U : ℝ} {h : ℂ → ℂ} {A B C : ℝ}
    (hh : ch.B3 h A B C) :
    ‖ch.intE U h‖ ≤ A * ch.mom U (-(1 / 2)) + B * ch.mom U (1 / 2) + C * ch.mom U (3 / 2) :=
  Chain3.norm_intE_le ch le_rfl (by norm_num) (by norm_num) hh.2.2.2

/-- Hypotheses on the pulled-back symbol `Q`, the Binet factor `E` and the bracket `1 + (s²+a)Q` on `B(0,ρ₀)`. -/
structure SdAmp (lam ρ0 : ℝ) (a Q0 Q1 : ℂ) (Q Q' E : ℂ → ℂ) (CQ CE CB : ℝ) : Prop where
  hCQ : 0 ≤ CQ
  hCE : 0 ≤ CE
  hCB : 0 ≤ CB
  hQd : ∀ s ∈ ball (0 : ℂ) ρ0, HasDerivAt Q (Q' s) s
  hQ'c : ContinuousOn Q' (ball 0 ρ0)
  hQ1 : ∀ s ∈ ball (0 : ℂ) ρ0, ‖Q s - Q0 - Q1 * s‖ ≤ CQ * (‖a‖ + ‖s‖ ^ 2)
  hQ2 : ∀ s ∈ ball (0 : ℂ) ρ0, ‖Q' s - Q1‖ ≤ CQ * (‖s‖ + ‖a‖)
  hEc : ContinuousOn E (ball 0 ρ0)
  hE : ∀ s ∈ ball (0 : ℂ) ρ0, ‖E s - 1‖ ≤ CE * lam ^ 3 * ‖s‖
  hB : ∀ s ∈ ball (0 : ℂ) ρ0, ‖1 + (s ^ 2 + a) * Q s‖ ≤ CB

end FormalResearch.SignUncertainty.CtSd
