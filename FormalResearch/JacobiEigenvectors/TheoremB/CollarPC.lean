module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftTails
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftAssembly4
public import FormalResearch.JacobiEigenvectors.TheoremA.WindowMass2

/-!
# Paper J, Theorem B, L3.4 (part 1): the recessive PC profile at an exterior row

Source: Paper J `app_thmB.tex`, proof of `lem:tha-collar` (1), second paragraph ("At the left exterior neighbour `n_1`, `-Z_{n_1} > 0` ... `|psi-hat^{PC,-}_{n_1}| <= C M_Olv(a,-Z_{n_1}) <= C kappa_bal^{-1} e^{-c_E/h}`,
and the same for the companion `h^{1/2} U'(a,-Z_{n_1})`, since `h^{1/2}|U'| <= (h k_2)^{1/2} E_U <= C_Lambda E_U`").

## Proved here

* `pcMinus0_env`: for `Z <= 0` the recessive member of the `-` pair, `pcMinus 0 Z = kappa_bal U(a, -Z)`, and its derivative obey `|.| <= C_PC E_-(a,Z) M_bal(a,Z)` and `|.'| <= C_PC E_- M_bal k_2^{1/2}`
  (`lem:cha-PCenv` (1b) for `a <= 0`, (2) for `a > 0`, from `ParabolicCylinderFacts.env_well`, `env_bar`).
* `pc_ext_row`: for a row `j` of patch 2 with `-2 eta <= x_j <= -5 eta/16` (`x = u - u_c`), `|phi^{(1)}_{2,j}|` and the second component of the model pair `wf 2 0` are at most `B e^{-c_Q/h}`, `B = (K_A + C_B C_Lambda + C_Lambda) C_PC`
  (`phi = A y + (h B)(h^{1/2} y')` with `wm_phi2_decomp`, `|A| <= K_A` (`wm_AA_le`), `|B| <= C_B` (`corr_PC`), `h k_2 <= C_Lambda^2` (`win_row`), `E_- <= e^{-c_Q/h}` (`Eminus_left_small`), `M_bal <= 1`).

## Differences from the paper

None of substance; `h^{1/2}|U'| <= C_Lambda E_U` is `h k_2 <= C_Lambda^2` of `win_row`, as in the paper.

## Not formalised

The glue to `softNorm` and the assembly of `PropThaCollar` (`Collar.lean`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

section PCEnv

variable {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- the recessive member of the `-` pair at `Z <= 0`, with its derivative, against `E_- M_bal` (`lem:cha-PCenv` (1b), (2)). -/
theorem pcMinus0_env (pc : ParabolicCylinderFacts U V cPC CPC) (a Z : ℝ) (hZ : Z ≤ 0) :
    |kappaBal a * U a (-Z)| ≤ CPC * Eminus a Z * Mbal a Z ∧
    |deriv (fun w => kappaBal a * U a (-w)) Z| ≤ CPC * Eminus a Z * Mbal a Z * Real.sqrt (k2 a Z) := by
  have hw : 0 ≤ -Z := neg_nonneg.mpr hZ
  have hd : deriv (fun w => kappaBal a * U a (-w)) Z = -(kappaBal a * deriv (U a) (-Z)) := by
    have h2 := deriv_comp_neg (fun v => kappaBal a * U a v) Z
    exact h2.trans (by rw [deriv_const_mul _ (pc_diffU pc a (-Z))])
  have hk : 0 < k2 a (-Z) := lt_of_lt_of_le one_pos (win_k2_ge_one a (-Z))
  have hM : Mbal a (-Z) = Mbal a Z := TheoremA.Mbal_neg a Z
  have hk2 : k2 a (-Z) = k2 a Z := TheoremA.k2_neg a Z
  rw [hd, abs_neg]
  by_cases ha : a ≤ 0
  · obtain ⟨e1, e2, -, -⟩ := pc_pair_well pc a ha (-Z) hw
    have hE : Eminus a Z = Ewell a (-Z) := by rw [Eminus_of_nonpos ha, abs_of_nonpos hZ]
    rw [hE, ← hM, ← hk2]
    exact ⟨e1, e2⟩
  · have ha' : 0 < a := not_le.mp ha
    obtain ⟨e1, -⟩ := pc.env_bar a ha' (-Z)
    obtain ⟨s1, s2⟩ := sqrt_split _ _ _ _ hk e1
    have hE : Eminus a Z = Ebar a (-Z) := by
      unfold Eminus
      rw [ite_eq_right ha, Ebar_neg]
    rw [hE, ← hM, ← hk2]
    exact ⟨s1, s2⟩

end PCEnv

section Row

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

/-- the constant of `pc_ext_row`. -/
def extB (CPC : ℝ) : ℝ := (C.cs.KA + C.CBc * winCLam C + winCLam C) * CPC

lemma extB_nonneg {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) : 0 ≤ extB C CPC := by
  have hCPC : 0 ≤ CPC := le_trans hf.cPC_pos.le hf.cPC_le
  have h1 := C.cs.KA_nonneg
  have h2 := C.consts_pos4.2
  have h3 := winCLam_nonneg C
  unfold extB
  positivity

/-- **the recessive PC profile at an exterior row is exponentially small** (paper: `lem:tha-collar` (1), second paragraph). -/
theorem pc_ext_row {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ C.δ0) {N : ℕ} (hN : C.N0 ≤ N) (hh : Fz.step N ≤ min (winH1 C) (min C.softH2 1)) {j : ℤ}
    (hj0 : 0 ≤ j) (hjN : j ≤ N) (hj1 : (C.chain p X N).jj 1 ≤ j) (hj2 : j ≤ (C.chain p X N).NR)
    (hlo : -(2 * C.η) ≤ uNode (Fz.step N) j - C.uc p) (hhi : uNode (Fz.step N) j - C.uc p ≤ -(5 * C.η / 16)) :
    |(C.chain p X N).phi (Fz.step N) 0 2 j| ≤ extB C CPC * Real.exp (-(softCQ C / Fz.step N)) ∧
    |(C.chain p X N).wf 2 0 (uNode (Fz.step N) j) (Fz.step N) 1| ≤ extB C CPC * Real.exp (-(softCQ C / Fz.step N)) := by
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hs1 : Fz.step N ≤ winH1 C := hh.trans (min_le_left _ _)
  have hs2 : Fz.step N ≤ C.softH2 := (hh.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hs3 : Fz.step N ≤ 1 := (hh.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hη := C.consts_pos.2.1
  have hCPC : 0 ≤ CPC := le_trans hf.cPC_pos.le hf.cPC_le
  have hjr : j ∈ rowsOf N := by unfold rowsOf; exact Finset.mem_Icc.mpr ⟨hj0, hjN⟩
  have hZ : C.Zof p X N j ≤ 0 := Zof_nonpos_of_near C hp hX hjr (by linarith)
  have hc2 : |uNode (Fz.step N) j - C.uc p| ≤ 2 * C.η := abs_le.mpr ⟨hlo, by linarith⟩
  obtain ⟨-, hBB⟩ := C.corr_PC p hp X hX N hN j hj0 hjN hc2
  have hAA := wm_AA_le C hp hX hN hj1 hj2
  have hj2' : j ≤ (C.chain p X N).NR + 1 := by omega
  have hdec := wm_phi2_decomp C hp hX hN hj1 hj2' 0
  rw [wm_pcMinus0] at hdec
  have hderiv : deriv (fun z => kappaBal (C.aOf p X N) * U (C.aOf p X N) (-z)) (C.Zof p X N j) =
      deriv (fun w => kappaBal (C.aOf p X N) * U (C.aOf p X N) (-w)) (C.Zof p X N j) := rfl
  obtain ⟨e1, e2⟩ := pcMinus0_env hf (C.aOf p X N) (C.Zof p X N j) hZ
  have hk2 := (win_row C p hp X hX N hh0 hs1 j hc2).2.1
  have hΛ := winCLam_nonneg C
  have hsq : Real.sqrt (Fz.step N) * Real.sqrt (k2 (C.aOf p X N) (C.Zof p X N j)) ≤ winCLam C := by
    rw [← Real.sqrt_mul hh0.le]
    exact Real.sqrt_le_iff.mpr ⟨hΛ, hk2⟩
  obtain ⟨lam, hV⟩ : ∃ lam, ((C.chain p X N).rescale1 lam).PreValid C.cs (Fz.step N) m := ⟨_, C.valid p hp X hX N hN⟩
  have hE := Eminus_left_small C hp hX hN hs2 hV hlo hhi
  have hEp := Eminus_pos (C.aOf p X N) (C.Zof p X N j)
  have hM1 := Mbal_le_one (C.aOf p X N) (C.Zof p X N j)
  have hM0 := Mbal_pos (C.aOf p X N) (C.Zof p X N j)
  set E := Eminus (C.aOf p X N) (C.Zof p X N j) with hEdef
  set M := Mbal (C.aOf p X N) (C.Zof p X N j) with hMdef
  set y := kappaBal (C.aOf p X N) * U (C.aOf p X N) (-(C.Zof p X N j)) with hy
  set y' := deriv (fun w => kappaBal (C.aOf p X N) * U (C.aOf p X N) (-w)) (C.Zof p X N j) with hy'
  set Av := (C.chain p X N).AA 2 (uNode (Fz.step N) j) (Fz.step N) with hAv
  set Bv := (C.chain p X N).BB 2 (uNode (Fz.step N) j) (Fz.step N) with hBv
  have hEM : E * M ≤ Real.exp (-(softCQ C / Fz.step N)) := by
    calc E * M ≤ E * 1 := mul_le_mul_of_nonneg_left hM1 hEp.le
      _ = E := mul_one _
      _ ≤ _ := hE
  have hEM0 : 0 ≤ E * M := by positivity
  have hsk : 0 ≤ Real.sqrt (k2 (C.aOf p X N) (C.Zof p X N j)) := Real.sqrt_nonneg _
  have hsh : 0 ≤ Real.sqrt (Fz.step N) := Real.sqrt_nonneg _
  -- the derivative term
  have hyd : Real.sqrt (Fz.step N) * |y'| ≤ winCLam C * (CPC * (E * M)) := by
    calc Real.sqrt (Fz.step N) * |y'| ≤ Real.sqrt (Fz.step N) * (CPC * E * M * Real.sqrt (k2 (C.aOf p X N) (C.Zof p X N j))) :=
          mul_le_mul_of_nonneg_left e2 hsh
      _ = (Real.sqrt (Fz.step N) * Real.sqrt (k2 (C.aOf p X N) (C.Zof p X N j))) * (CPC * (E * M)) := by ring
      _ ≤ winCLam C * (CPC * (E * M)) := mul_le_mul_of_nonneg_right hsq (by positivity)
  have hfin : CPC * (E * M) ≤ CPC * Real.exp (-(softCQ C / Fz.step N)) := mul_le_mul_of_nonneg_left hEM hCPC
  have hexp0 := Real.exp_pos (-(softCQ C / Fz.step N))
  have hT0 : 0 ≤ CPC * (E * M) := by positivity
  constructor
  · rw [hdec]
    have t1 : |Av * y| ≤ C.cs.KA * (CPC * (E * M)) := by
      rw [abs_mul]
      refine mul_le_mul hAA ?_ (abs_nonneg _) C.cs.KA_nonneg
      calc |y| ≤ CPC * E * M := e1
        _ = CPC * (E * M) := by ring
    have t2 : |Fz.step N * Bv * (Real.sqrt (Fz.step N) * y')| ≤ C.CBc * winCLam C * (CPC * (E * M)) := by
      have : |Fz.step N * Bv * (Real.sqrt (Fz.step N) * y')| = Fz.step N * |Bv| * (Real.sqrt (Fz.step N) * |y'|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hh0, abs_of_nonneg hsh]
      rw [this]
      have h3 : Fz.step N * |Bv| ≤ 1 * C.CBc := mul_le_mul hs3 hBB (abs_nonneg _) zero_le_one
      calc Fz.step N * |Bv| * (Real.sqrt (Fz.step N) * |y'|) ≤ (1 * C.CBc) * (winCLam C * (CPC * (E * M))) :=
            mul_le_mul h3 hyd (by positivity) (by have := C.consts_pos4.2; positivity)
        _ = C.CBc * winCLam C * (CPC * (E * M)) := by ring
    calc |Av * y + Fz.step N * Bv * (Real.sqrt (Fz.step N) * y')|
        ≤ |Av * y| + |Fz.step N * Bv * (Real.sqrt (Fz.step N) * y')| := abs_add_le _ _
      _ ≤ C.cs.KA * (CPC * (E * M)) + C.CBc * winCLam C * (CPC * (E * M)) := add_le_add t1 t2
      _ = (C.cs.KA + C.CBc * winCLam C) * (CPC * (E * M)) := by ring
      _ ≤ (C.cs.KA + C.CBc * winCLam C + winCLam C) * (CPC * (E * M)) :=
          mul_le_mul_of_nonneg_right (by linarith) hT0
      _ ≤ (C.cs.KA + C.CBc * winCLam C + winCLam C) * (CPC * Real.exp (-(softCQ C / Fz.step N))) :=
          mul_le_mul_of_nonneg_left hfin (by have := C.cs.KA_nonneg; have := C.consts_pos4.2; positivity)
      _ = extB C CPC * Real.exp (-(softCQ C / Fz.step N)) := by unfold extB; ring
  · have hw := C.wf2_eq p hp X hX N hN j (Finset.mem_Icc.mpr ⟨hj1, hj2'⟩) 0
    have h1 : (C.chain p X N).wf 2 0 (uNode (Fz.step N) j) (Fz.step N) 1 =
        Real.sqrt (Fz.step N) * y' := by
      rw [hw]
      show Real.sqrt (Fz.step N) * deriv (pcMinus U V (C.aOf p X N) 0) (C.Zof p X N j) = Real.sqrt (Fz.step N) * y'
      rw [wm_pcMinus0]
    rw [h1, abs_mul, abs_of_nonneg hsh]
    calc Real.sqrt (Fz.step N) * |y'| ≤ winCLam C * (CPC * (E * M)) := hyd
      _ ≤ (C.cs.KA + C.CBc * winCLam C + winCLam C) * (CPC * (E * M)) :=
          mul_le_mul_of_nonneg_right (by have := C.cs.KA_nonneg; have := C.consts_pos4.2; nlinarith [mul_nonneg C.consts_pos4.2 hΛ]) hT0
      _ ≤ (C.cs.KA + C.CBc * winCLam C + winCLam C) * (CPC * Real.exp (-(softCQ C / Fz.step N))) :=
          mul_le_mul_of_nonneg_left hfin (by have := C.cs.KA_nonneg; have := C.consts_pos4.2; positivity)
      _ = extB C CPC * Real.exp (-(softCQ C / Fz.step N)) := by unfold extB; ring

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.pc_ext_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pc_ext_row

end Row

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.pcMinus0_env' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pcMinus0_env

end FormalResearch.JacobiEigenvectors.TheoremB

end
