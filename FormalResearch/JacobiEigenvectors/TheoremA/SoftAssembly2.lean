module


public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftAssembly
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftEigen
public import FormalResearch.JacobiEigenvectors.TheoremA.StepZero
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkNormalisation

/-!
# Soft-edge assembly, part B: Step 0 inputs (preparatory for `PropThaW2` (3)-(4))

Paper source: app_thmA, proof of prop:tha-W2, Step 0 and the bond positivity used in Steps 3-6.

Proved here:
* `mu0Lip`: one-sided Lipschitz bound of `mu_0` on `[-delta_0, 0]` from `mu0_slope`, `mu0_zero` (mean value theorem).
* `aOf_le_of_step0`: Step 0 (`X <= bandHi + Cs0 h^2`) gives `a <= asmAplus` (no extra hypothesis).
* `Zof_pos_of_far`, `lt_of_Zof_nonpos`: `Z_n > 0` once `u_n - u_c >= eta/4` (`zeta_far`, `zeta_far_out`, `zeta_sign_out`).
* `bondA_pos_all`: all bonds `A_n`, `0 <= n < N`, are positive for a `SoftMirror` pair (left chart on
  the left patches, mirror chart on the right).

Differences from the paper: none (chart fields `mu0_slope`, `zeta_sign_out` carry lem:cha-PCcoord).

Not formalised: the pointwise envelope comparison off the window (needs the zeta-sign hypothesis,
finding F-W2-14), the T4 tail sum, E7 and the final assembly of `PropThaW2` (2)-(4).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

section StepZeroA

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

/-- the one-sided Lipschitz bound of `mu_0` at `0` on `alpha <= 0`. -/
def Mu0Lip : Prop := ∃ cL : ℝ, 0 ≤ cL ∧ ∀ μ ∈ P, ∀ α : ℝ, -C.δ0 ≤ α → α ≤ 0 → -(cL * |α|) ≤ C.muS 0 μ α

/-- `Mu0Lip` from `mu0_slope`, `mu0_zero` and `mu0_deriv` (mean value theorem on `[-delta_0, 0]`). -/
theorem mu0Lip : Mu0Lip C := by
  have hc := C.consts_pos5
  refine ⟨C.Cmu0, by linarith [hc.1, hc.2], ?_⟩
  intro μ hμ α hα1 hα0
  have hdiff : Differentiable ℝ (C.muS 0 μ) :=
    ((C.mu0_deriv μ hμ).1.differentiable (by norm_num))
  have hD : Convex ℝ (Set.Icc (-C.δ0) 0) := convex_Icc _ _
  have hδ : 0 ≤ C.δ0 := by linarith
  have hmv := hD.image_sub_le_mul_sub_of_deriv_le (f := C.muS 0 μ) (C := C.Cmu0) hdiff.continuous.continuousOn
    hdiff.differentiableOn
    (fun x hx => by
      rw [interior_Icc] at hx
      exact ((C.mu0_slope μ hμ x (abs_le.mpr ⟨hx.1.le, by linarith [hx.2]⟩)).2))
    α (Set.mem_Icc.mpr ⟨hα1, hα0⟩) 0 (Set.mem_Icc.mpr ⟨by linarith, le_refl 0⟩) hα0
  rw [C.mu0_zero μ hμ] at hmv
  rw [abs_of_nonpos hα0]
  linarith

/-- the `a_+` of the assembly. -/
def asmAplus : ℝ := ((q / 2 : ℕ) : ℝ) * C.Cmu + 1

/-- **Step 0 consequence**: an energy with `X <= X_s^+ + Cs0 h^2` has `a <= a_+` (`a = -mu~/h`, `mu_0 >= 0` for `alpha >= 0` by `mu0_S0`, `mu_0 >= -cL |alpha|` for `alpha <= 0`). -/
theorem aOf_le_of_step0 (Cs0 : ℝ) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ N : ℕ, Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ C.δ0 →
      X ≤ Fz.bandHi p + Cs0 * Fz.step N ^ 2 → C.aOf p X N ≤ asmAplus C := by
  obtain ⟨cL, hcL, HL⟩ := mu0Lip C
  refine ⟨min 1 (1 / (cL * |Cs0| + 1)), lt_min one_pos (by positivity), ?_⟩
  intro p hp N hstep X hX hX0
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hh1 : Fz.step N ≤ 1 := hstep.trans (min_le_left _ _)
  have hh2 : Fz.step N ≤ 1 / (cL * |Cs0| + 1) := hstep.trans (min_le_right _ _)
  have hα := C.abs_alpha_le hX
  have hsub := C.muTilde_sub_le hp hX hh1
  have hmu0 : -(cL * |Cs0| * Fz.step N ^ 2) ≤ C.muS 0 p (Fz.bandHi p - X) := by
    by_cases hneg : Fz.bandHi p - X ≤ 0
    · have h1 := HL p hp (Fz.bandHi p - X) (abs_le.mp hα).1 hneg
      have h2 : |Fz.bandHi p - X| ≤ |Cs0| * Fz.step N ^ 2 := by
        rw [abs_of_nonpos hneg]
        calc -(Fz.bandHi p - X) = X - Fz.bandHi p := by ring
          _ ≤ Cs0 * Fz.step N ^ 2 := by linarith
          _ ≤ |Cs0| * Fz.step N ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
      have h3 : cL * |Fz.bandHi p - X| ≤ cL * (|Cs0| * Fz.step N ^ 2) := mul_le_mul_of_nonneg_left h2 hcL
      linarith
    · push_neg at hneg
      have hS := C.mu0_S0 p hp X (by linarith) (abs_le.mp hα).2
      have hint : 0 ≤ ∫ u in (0 : ℝ)..Fz.L, Real.arccos ((X - Fz.B 0 p u) / (2 * Real.sqrt (E0 Fz.L (Fz.G 0 p) u))) :=
        intervalIntegral.integral_nonneg Fz.L_pos.le (fun u _ => Real.arccos_nonneg _)
      rw [← hS] at hint
      have : 0 ≤ C.muS 0 p (Fz.bandHi p - X) := nonneg_of_mul_nonneg_right hint Real.pi_pos
      have : 0 ≤ cL * |Cs0| * Fz.step N ^ 2 := by positivity
      linarith
  have hmt : -(cL * |Cs0| * Fz.step N ^ 2 + ((q / 2 : ℕ) : ℝ) * C.Cmu * Fz.step N) ≤ C.muTilde p X N := by
    have := (abs_le.mp hsub).1
    linarith
  rw [SoftEdgeCore.aOf_eq]
  unfold asmAplus
  have hcc : cL * |Cs0| * Fz.step N ≤ 1 := by
    have h1 : (cL * |Cs0|) * Fz.step N ≤ (cL * |Cs0|) * (1 / (cL * |Cs0| + 1)) :=
      mul_le_mul_of_nonneg_left hh2 (by positivity)
    have h2 : (cL * |Cs0|) * (1 / (cL * |Cs0| + 1)) ≤ 1 := by
      rw [← div_eq_mul_one_div, div_le_one (by positivity)]; linarith
    linarith
  have e : -(1 / Fz.step N) * C.muTilde p X N ≤ (1 / Fz.step N) * (cL * |Cs0| * Fz.step N ^ 2 + ((q / 2 : ℕ) : ℝ) * C.Cmu * Fz.step N) := by
    have := mul_le_mul_of_nonneg_left hmt (by positivity : (0 : ℝ) ≤ 1 / Fz.step N)
    linarith
  have e2 : (1 / Fz.step N) * (cL * |Cs0| * Fz.step N ^ 2 + ((q / 2 : ℕ) : ℝ) * C.Cmu * Fz.step N) =
      cL * |Cs0| * Fz.step N + ((q / 2 : ℕ) : ℝ) * C.Cmu := by field_simp
  linarith

end StepZeroA


section ZSign

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

/-- a row has `0 <= u_n <= L`. -/
lemma uNode_row_mem {N : ℕ} {n : ℤ} (hn : n ∈ rowsOf N) : 0 ≤ uNode (Fz.step N) n ∧ uNode (Fz.step N) n ≤ Fz.L := by
  have hn' := Finset.mem_Icc.mp hn
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hL := step_mul_succ Fz N
  unfold uNode
  have h1 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'.1
  have h2 : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn'.2
  constructor
  · positivity
  · rw [← hL]; nlinarith

/-- **(F-W2-14, used by T4)** `Z_n > 0` as soon as `x_n = u_n - u_c >= eta/4` (`zeta_far`, `zeta_far_out` for `zeta^2 > 0`, `zeta_sign_out` for the sign). -/
theorem Zof_pos_of_far {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ C.δ0) {N : ℕ} {n : ℤ} (hn : n ∈ rowsOf N)
    (hx : C.η / 4 ≤ uNode (Fz.step N) n - C.uc p) : 0 < C.Zof p X N n := by
  have hα := C.abs_alpha_le hX
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hη := C.consts_pos.2.1
  have hcz := C.consts_pos2.2
  obtain ⟨hn0, hnL⟩ := uNode_row_mem (Fz := Fz) hn
  have hxabs : C.η / 4 ≤ |uNode (Fz.step N) n - C.uc p| := le_trans hx (le_abs_self _)
  have hz2 : 0 < C.zeta p (Fz.bandHi p - X) (uNode (Fz.step N) n - C.uc p) ^ 2 := by
    have hmax : 0 ≤ 4 * max (C.muS 0 p (Fz.bandHi p - X)) 0 := by positivity
    by_cases h2 : |uNode (Fz.step N) n - C.uc p| ≤ 2 * C.η
    · have := C.zeta_far p hp _ hα _ h2 hxabs
      linarith
    · have := C.zeta_far_out p hp _ hα _ (by linarith [not_le.mp h2]) (by linarith) (by linarith)
      linarith
  have hsg := (C.zeta_sign_out p hp _ hα _ hxabs (by linarith) (by linarith)).2 (by linarith)
  have hne : C.zeta p (Fz.bandHi p - X) (uNode (Fz.step N) n - C.uc p) ≠ 0 := by
    intro h; rw [h] at hz2; simp at hz2
  unfold SoftEdgeCore.Zof
  exact div_pos (lt_of_le_of_ne hsg (Ne.symm hne)) (Real.sqrt_pos.mpr hh0)

/-- `Z_n <= 0` forces `x_n < eta/4`. -/
theorem lt_of_Zof_nonpos {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ C.δ0) {N : ℕ} {n : ℤ} (hn : n ∈ rowsOf N)
    (hZ : C.Zof p X N n ≤ 0) : uNode (Fz.step N) n - C.uc p < C.η / 4 := by
  by_contra h
  exact absurd (Zof_pos_of_far C hp hX hn (not_lt.mp h)) (not_lt.mpr hZ)

end ZSign

section BondPos

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

/-- the bonds of the chain are positive on `0 <= n < N_R`. -/
lemma bondA_pos_chain {C : SoftEdgeChart Fz P m q U V Lm} {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ C.δ0)
    {N : ℕ} (hN : C.N0 ≤ N) (hh : Fz.step N ≤ C.softH1) {n : ℤ} (hn0 : 0 ≤ n) (hn : n < (C.chain p X N).NR) :
    0 < Fz.bondA p N n := by
  have hV := C.valid p hp X hX N hN
  have hne := A_ne_zero_rows C hp hX hN hh hV n hn0 hn
  have hA := C.A_bond p hp X hX N hN n (Finset.mem_Icc.mpr ⟨by omega, hn.le⟩)
  rw [hA] at hne
  exact lt_of_le_of_ne (bondA_nonneg' Fz p N n) (Ne.symm hne)

/-- **the bonds `a_n`, `0 <= n < N`, are positive** (the left chain covers `n < N_R^L`, the mirror chain the rest). -/
theorem bondA_pos_all (hM : SoftMirror CL CR) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ CL.δ0)
    {N : ℕ} (hN : CL.N0 ≤ N) (hh : Fz.step N ≤ CL.softH1) (hhR : Fz.step N ≤ CR.softH1) :
    ∀ n : ℤ, 0 ≤ n → n < N → 0 < Fz.bondA p N n := by
  intro n hn0 hnN
  obtain ⟨hNR, hXR⟩ := mirror_ctx hM hp hX hN
  by_cases hl : n < (CL.chain p X N).NR
  · exact bondA_pos_chain hp hX hN hh hn0 hl
  · push_neg at hl
    have hmir := bondA_mirror Fz p N ((N : ℤ) - 1 - n)
    have e : (N : ℤ) - 1 - ((N : ℤ) - 1 - n) = n := by ring
    rw [e] at hmir
    rw [← hmir]
    have hstepR : (mirrorFamily Fz).step N = Fz.step N := rfl
    have hlt : (N : ℤ) - 1 - n < (CR.chain p X N).NR := by
      by_contra hcon
      push_neg at hcon
      have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
      obtain ⟨-, hη, -⟩ := CL.consts_pos
      obtain ⟨-, -, -, -, -, -, hNRu, hNRv⟩ := CL.shape p hp X hX N hN
      obtain ⟨-, -, -, -, -, -, hNRuR, hNRvR⟩ := CR.shape p hp X hXR N hNR
      have hucR : CR.uc p = Fz.L - CL.uc p := hM.1 p hp
      have hηR : CR.η = CL.η := hM.2.2.2.1
      have hLm := step_mul_succ Fz N
      have hm1 := uNode_mirror Fz.L (Fz.step N) N (n + 1) hLm
      have e2 : (N : ℤ) - (n + 1) = (N : ℤ) - 1 - n := by ring
      rw [e2] at hm1
      -- u_{N-1-n} >= u_{NR_R}
      have h1 : uNode (Fz.step N) (CR.chain p X N).NR ≤ uNode (Fz.step N) ((N : ℤ) - 1 - n) :=
        SoftEdgeChart.uNode_mono_le hh0.le hcon
      have h2 : uNode (Fz.step N) ((CR.chain p X N).NR + 1) = uNode (Fz.step N) (CR.chain p X N).NR + Fz.step N := by
        unfold uNode; push_cast; ring
      have hNRvR' : CR.uc p + 2 * CR.η < uNode (Fz.step N) ((CR.chain p X N).NR + 1) := hNRvR
      rw [hucR, hηR] at hNRvR'
      have h3 : uNode (Fz.step N) (n + 1) ≥ uNode (Fz.step N) ((CL.chain p X N).NR + 1) :=
        SoftEdgeChart.uNode_mono_le hh0.le (by omega)
      have hhη : Fz.step N ≤ CL.η / 2 := hh.trans CL.softH1_le_eta
      linarith
    exact bondA_pos_chain (C := CR) hp hXR hNR (by rw [hstepR]; exact hhR) (by omega) hlt

end BondPos

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.aOf_le_of_step0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms aOf_le_of_step0

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bondA_pos_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bondA_pos_all

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.mu0Lip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mu0Lip

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.Zof_pos_of_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Zof_pos_of_far

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.lt_of_Zof_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lt_of_Zof_nonpos

end FormalResearch.JacobiEigenvectors.TheoremA

end
