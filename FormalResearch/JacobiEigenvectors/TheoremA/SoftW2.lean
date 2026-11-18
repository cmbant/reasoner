module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftCountChart
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftItem1
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftAssembly5

/-!
# Paper J, Layer 2 (L2.C7): the assembly of `PropThaW2` (`propThaW2_proved_of_signs`)

Source: Paper J, `thmA.tex` prop:tha-W2 (1)--(4), proof in `app_thmA.tex` (Steps 1--6, item (4) as the same statements with `Lm = 1 + log (1/h)`).

Proved here (axiom-pinned): `propThaW2_proved_of_signs`: for every `ParabolicCylinderFacts U V cPC CPC` and every `Cs0`, if `SoftCountHyps CL CR Cs0`
(hypotheses (ii), (iii) of `lem:tha-count`, i.e. the sign analysis of Step 6, `TheoremA/SoftCountHyps.lean`) holds, then the frozen statement
`PropThaW2 Fz P m q U V CL CR Cs0` holds, for every `Lm` (so items (1)--(3) and, with `Lm = 1 + log (1/h)`, item (4)).
The conjuncts come from: item (1) `propThaW2_item1`; (2) `soft_eigen_clause`; (3) quantisation (label = index) and existence from `soft_count_chart`
(`propThaCount`, `soft_window_label`, `order_label_real`, `casD_zero_exists_eig`).

Differences from the paper: the premise `ParabolicCylinderFacts U V cPC CPC` (the frozen `PropThaW2` has none; `propThaW2_item1` takes it too, finding F-W2-11/PLAN); the premise `SoftCountHyps`
(until the sign analysis of Step 6 (ii), (iii) discharges it); counting windows `Phi = pi mu_0`, `eps = pi h/8` (see `SoftCountHyps`).  The hypothesis `StdAssump` of the frozen
statement is not used.  Not formalised: the proof of `SoftCountHyps`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

section Assembly

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

lemma mono4 {C1 C2 a b w : ℝ} (hC : C1 ≤ C2) (ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 ≤ w) :
    C1 * a * b * w ≤ C2 * a * b * w :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC ha) hb) hw

lemma mono5 {C1 C2 a b w v : ℝ} (hC : C1 ≤ C2) (ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 ≤ w) (hv : 0 ≤ v) :
    C1 * a * b * w * v ≤ C2 * a * b * w * v :=
  mul_le_mul_of_nonneg_right (mono4 hC ha hb hw) hv

/-- **`PropThaW2`, assembled modulo the sign facts of Step 6**. -/
theorem propThaW2_proved_of_signs {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (Cs0 : ℝ)
    (hS : SoftCountHyps CL CR Cs0) : PropThaW2 Fz P m q U V CL CR Cs0 := by
  intro hm hLm hM r _
  obtain ⟨C1, h1, c1, Cl1, h1p, hc1, H1⟩ := propThaW2_item1 (C := CL) hf hm hLm
  obtain ⟨C2, h2, h2p, H2⟩ := soft_eigen_clause CL CR hM hf hm hLm Cs0
  obtain ⟨C3, h3, h3p, H3⟩ := soft_count_chart CL CR hM hf hm hLm Cs0 hS
  obtain ⟨Cc, hC1, hC2, hC3⟩ : ∃ Cc : ℝ, C1 ≤ Cc ∧ C2 ≤ Cc ∧ C3 ≤ Cc :=
    ⟨max C1 (max C2 C3), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  refine ⟨Cc, min 1 (min h1 (min h2 h3)), c1, Cl1, lt_min one_pos (lt_min h1p (lt_min h2p h3p)), hc1, ?_⟩
  intro p hp N hN hstep
  have hs0 : Fz.step N ≤ 1 := hstep.trans (min_le_left _ _)
  have hs1 : Fz.step N ≤ h1 := hstep.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs2 : Fz.step N ≤ h2 := hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hs3 : Fz.step N ≤ h3 := hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hN0 : CL.N0 ≤ N := (le_max_left _ _).trans hN
  have hh : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have ha : 0 ≤ Fz.step N ^ m := pow_nonneg hh.le m
  have hb : 0 ≤ Lm (Fz.step N) := le_trans zero_le_one (hLm _ hh hs0)
  have hpa : 0 ≤ Fz.step N ^ (m + 1) := pow_nonneg hh.le _
  refine ⟨fun X hX => ?_, ?_, ?_⟩
  · obtain ⟨hψ, hlo, hup⟩ := H1 p hp N hN0 hs1 X hX
    refine ⟨fun ψ hJ hseed => ⟨fun k hk hku => ?_, fun k hk hku1 hku2 => ?_⟩, hlo, hup, ?_⟩
    · exact ((hψ ψ hJ hseed).1 k hk hku).trans (mono4 hC1 ha hb (softEnvWeb_nonneg CL p X N k))
    · have hMo := molv_nonneg hf (CL.aOf p X N) (-(CL.Zof p X N k))
      exact ((hψ ψ hJ hseed).2 k hk hku1 hku2).trans (mono5 hC1 ha hb (abs_nonneg _) hMo)
    · intro Xs Um hE hS0 k hk
      subst hk
      obtain ⟨e1, e2, e3⟩ := H2 p hp N hN hs2 Xs Um hE hS0 k hX
      refine ⟨fun n hn => (e1 n hn).trans (mono4 hC2 ha hb (softEnv_nonneg CL CR hf p (Xs k) N n)), e2.trans hC2,
        fun n hn hΩ => (e3 n hn hΩ).trans (mul_le_mul_of_nonneg_right hC2 (abs_nonneg _))⟩
  · intro Xs Um hE hS0 i hi
    obtain ⟨q3, -⟩ := H3 p hp N hN hs3 Xs Um hE hS0
    exact (q3 i hi).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC3 hpa) hb)
  · intro Xs Um hE hS0 k hk hex
    obtain ⟨-, e3⟩ := H3 p hp N hN hs3 Xs Um hE hS0
    exact e3 k hk hex

end Assembly

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.propThaW2_proved_of_signs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms propThaW2_proved_of_signs

end FormalResearch.JacobiEigenvectors.TheoremA

end
