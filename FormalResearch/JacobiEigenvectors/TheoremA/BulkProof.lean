module

public import FormalResearch.JacobiEigenvectors.TheoremA.Statements
public import FormalResearch.JacobiEigenvectors.Engine.LadderStability

/-!
# Paper J, Layer 2: the bulk comparison bound (L2.C1, `BulkSolutionBound`) and the bulk eigenvector statement (L2.C2, `PropThaW`)

Source: Paper J `charts.tex` `thm:cha-I` (hard-edge comparison through the collision, every order, `Fix m >= 1`) and
`cor:cha-I-general`; `thmA.tex` `prop:tha-W` (1) and (2) (`Fix m >= 1`); `app_thmA.tex` "The bulk: proof of Proposition prop:tha-W", Steps 1--3.

## Proved here

* `FormalResearch.JacobiEigenvectors.TheoremA.psiHat_one_eq`: on patch `1` the comparison sequence of a ladder chain is the first comparison
  pair, `psiHat h 1 j = phi h 0 1 j` (no transfer matrix is involved).
* `FormalResearch.JacobiEigenvectors.TheoremA.bulkSolutionBound_of_one_le`: for a bulk Weber chart `C` of order `m` with `1 <= m`,
  `BulkSolutionBound C` (the frozen statement, `TheoremA/Statements.lean`).  Proof: the exact solution `psi` of `JacSol` with the seed
  `psi_0 = psi-hat_0` is a solution of the engine's equations (`Lh h A Q psi k = 0` on `[s0, NR-1]`, the bonds and diagonal of the chain
  being those of `F` by `A_bond`, `Q_diag`); `LadderData.stability` (proved, `Engine/LadderStability.lean`) with `P = 1`, `s0 = 0` gives
  `|psi_j - psi-hat_j| <= mvC (2 K_D K_w h^m Theta) W_j M_j` on the rows `0 <= j <= NR`; `Theta <= C_sum` (`theta_le`), `W_j M_j = envL`,
  and the smallness `2 K_D K_w h^m Theta <= c_*` holds for `h <= h_0` because `h^m <= h` for `m >= 1`.

## Differences from the paper and the frozen statements (findings)

* **F-C1 (`m >= 1`).**  `BulkSolutionBound` (and `PropThaW`) are stated for every `m`, but `thm:cha-I` and `prop:tha-W` are stated for `m >= 1`
  and the proof needs it: the engine's smallness `2 K_D K_w h^m Theta <= c_*` is not available for `m = 0` (the bound `Theta <= C_sum` does not make
  it small).  The statement proved here is `bulkSolutionBound_of_one_le (hm : 1 <= m)`; the frozen `BulkSolutionBound` needs the hypothesis
  `1 <= m` (the main session's fix, not made here).
* No hypothesis is added: the chart fields used are `valid`, `shape`, `A_bond`, `Q_diag`, `theta_le`, `W_pos`-type facts of `Valid`, and `seed`
  is the chart's own `psiHatL`.

## Not formalised

`PropThaW` (L2.C2) is not proved in this module; see the report.  Its collar conjunct and the normalisation need the overlap coupling
`CR.c = L - CL.c'`, `CR.c' = L - CL.c` (`ChartInputs.overlap_match`), which the frozen statement does not carry.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.Engine

/-- On patch `1` the comparison sequence of a ladder chain is the first comparison pair (`cvec 1 = (1,0)`). -/
lemma psiHat_one_eq (D : LadderData) (h : ℝ) (j : ℤ) : D.psiHat h 1 j = D.phi h 0 1 j := by
  unfold LadderData.psiHat Engine.psiHat
  rw [cvec_one]
  simp

/-- **L2.C1: the bulk comparison bound** (`thm:cha-I` with `cor:cha-I-general`, prop:tha-W (1)).  The frozen statement `BulkSolutionBound`
with the hypothesis `1 <= m` that the paper states and the proof uses (finding F-C1). -/
theorem bulkSolutionBound_of_one_le {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart Fz P Jlo Jhi m U V) (hm : 1 ≤ m) :
    BulkSolutionBound C := by
  obtain ⟨-, -, -, -, -, -, -, -, hCsum, -⟩ := C.consts_pos
  set cs := C.cs with hcs
  set K : ℝ := (cs.KA + cs.KB) * cs.Kw with hK
  have hKnn : 0 ≤ K := mul_nonneg (add_nonneg cs.KA_nonneg cs.KB_nonneg) cs.Kw_nonneg
  have hE : 0 ≤ 2 * cs.KD * cs.Kw := mul_nonneg (mul_nonneg (by norm_num) cs.KD_nonneg) cs.Kw_nonneg
  have hq : 0 ≤ 1 + cs.CE ^ 2 := by positivity
  have hcmq : 0 ≤ (1 + cs.CE ^ 2) / cs.cm := div_nonneg hq cs.cm_pos.le
  have hDst : 0 < mvCstar cs.cm cs.CE K := by
    unfold mvCstar
    have h1 : 0 ≤ 2 * ((1 + cs.CE ^ 2) / cs.cm) * K :=
      mul_nonneg (mul_nonneg (by norm_num) hcmq) hKnn
    exact div_pos one_pos (by linarith)
  set M0 : ℝ := 2 * cs.KD * cs.Kw * C.Csum with hM0
  have hM0nn : 0 ≤ M0 := mul_nonneg hE hCsum
  have hden : 0 < M0 + 1 := by linarith
  set h0 : ℝ := min 1 (mvCstar cs.cm cs.CE K / (M0 + 1)) with hh0
  have hh0pos : 0 < h0 := lt_min one_pos (div_pos hDst hden)
  have hmvC : 0 ≤ mvC cs.cm cs.CE K cs.Λ 1 := by
    unfold mvC mvCrStar mvKappa
    have hΛ : 0 ≤ cs.Λ := by linarith [cs.Λ_ge]
    have hR : 0 ≤ (cs.Λ * (1 + cs.CE ^ 2)) ^ 1 * (1 + cs.CE ^ 2) :=
      mul_nonneg (pow_nonneg (mul_nonneg hΛ hq) 1) hq
    have hκ : 0 ≤ (2 * cs.Λ ^ 2 * (1 + cs.CE ^ 2) + 1) ^ 1 + 1 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcmq) hKnn)
      (mul_nonneg (mul_nonneg hKnn hR) hκ)
  refine ⟨mvC cs.cm cs.CE K cs.Λ 1 * (2 * cs.KD * cs.Kw * C.Csum), h0, hh0pos, ?_⟩
  intro p hp X hX N hN hstep ψ hJ hseed k hk
  -- the chain at `(p, X, N)`
  have hV : (C.chain p X N).Valid cs (Fz.step N) m := C.valid p hp X hX N hN
  obtain ⟨hP1, hs0, -, -, -⟩ := C.shape p hp X hX N hN
  have hθ : (C.chain p X N).theta (Fz.step N) ≤ C.Csum := C.theta_le p hp X hX N hN
  have hstep_pos : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hstep1 : Fz.step N ≤ 1 := le_trans hstep (le_trans (min_le_left _ _) le_rfl)
  have hsmall_h : Fz.step N ≤ mvCstar cs.cm cs.CE K / (M0 + 1) :=
    le_trans hstep (min_le_right _ _)
  have hpowle : (Fz.step N) ^ m ≤ Fz.step N := pow_le_of_le_one hstep_pos.le hstep1 (by omega)
  -- smallness of the engine threshold `2 K_D K_w h^m Theta <= c_*`
  have hsmall : 2 * cs.KD * cs.Kw * (Fz.step N) ^ m * (C.chain p X N).theta (Fz.step N)
      ≤ mvCstar cs.cm cs.CE K := by
    have hpow0 : 0 ≤ (Fz.step N) ^ m := pow_nonneg hstep_pos.le m
    have h1 : 2 * cs.KD * cs.Kw * (Fz.step N) ^ m * (C.chain p X N).theta (Fz.step N)
        ≤ 2 * cs.KD * cs.Kw * (Fz.step N) ^ m * C.Csum :=
      mul_le_mul_of_nonneg_left hθ (mul_nonneg hE hpow0)
    have h2 : 2 * cs.KD * cs.Kw * (Fz.step N) ^ m * C.Csum ≤ Fz.step N * M0 := by
      calc 2 * cs.KD * cs.Kw * (Fz.step N) ^ m * C.Csum = M0 * (Fz.step N) ^ m := by rw [hM0]; ring
        _ ≤ M0 * Fz.step N := mul_le_mul_of_nonneg_left hpowle hM0nn
        _ = Fz.step N * M0 := by ring
    have h3 : Fz.step N * M0 ≤ mvCstar cs.cm cs.CE K := by
      have hs := mul_le_mul_of_nonneg_right hsmall_h hM0nn
      have hfrac : mvCstar cs.cm cs.CE K / (M0 + 1) * M0 ≤ mvCstar cs.cm cs.CE K := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hden]
        nlinarith [hDst]
      linarith
    linarith
  -- the exact solution satisfies the engine's equations on `[s0, NR - 1]`
  have hsol : ∀ j ∈ Icc (C.chain p X N).s0 ((C.chain p X N).NR - 1),
      Lh (Fz.step N) (C.chain p X N).A (C.chain p X N).Q ψ j = 0 := by
    intro j hj
    rw [hs0] at hj
    obtain ⟨hj0, hj1⟩ := mem_Icc.mp hj
    have hL : Lop (Fz.bondA p N) (Fz.diagQ p N X) ψ j = 0 :=
      hJ j hj0 (by show j < (C.chain p X N).NR; omega)
    have hA0 : (C.chain p X N).A j = Fz.bondA p N j :=
      C.A_bond p hp X hX N hN j (mem_Icc.mpr ⟨by omega, by omega⟩)
    have hA1 : (C.chain p X N).A (j - 1) = Fz.bondA p N (j - 1) :=
      C.A_bond p hp X hX N hN (j - 1) (mem_Icc.mpr ⟨by omega, by omega⟩)
    have hQ0 : (C.chain p X N).Q j = Fz.diagQ p N X j :=
      C.Q_diag p hp X hX N hN j (mem_Icc.mpr ⟨hj0, by omega⟩)
    rw [Lh_congr_site hA0 hA1 hQ0]
    unfold Lh
    rw [hL, mul_zero]
  -- the seed
  have hseed' : ∀ j ∈ Icc (0 : ℤ) (C.chain p X N).s0, ψ j = (C.chain p X N).phi (Fz.step N) 0 1 j := by
    intro j hj
    rw [hs0] at hj
    have hj0 : j = 0 := by
      obtain ⟨h1, h2⟩ := mem_Icc.mp hj
      omega
    subst hj0
    rw [hseed]
    exact psiHat_one_eq _ _ _
  -- the engine: `LadderData.stability` for the single-patch chain
  have hcon := LadderData.stability (C.chain p X N) cs (Fz.step N) m hV ψ hsol hseed' hsmall
  obtain ⟨-, -, hcon3⟩ := hcon
  obtain ⟨q, hq, hbd⟩ := hcon3 k hk
  have hq1 : q = 1 := by
    have := Finset.mem_Icc.mp hq
    omega
  subst hq1
  rw [hP1] at hbd
  have hWk : 0 < (C.chain p X N).W k := hV.W_pos k hk
  have hMk : 0 < (C.chain p X N).M k := hV.M_pos k hk
  have hWM : 0 ≤ (C.chain p X N).W k * (C.chain p X N).M k := (mul_pos hWk hMk).le
  have hθbd : 2 * cs.KD * cs.Kw * (Fz.step N) ^ m * (C.chain p X N).theta (Fz.step N)
      ≤ 2 * cs.KD * cs.Kw * (Fz.step N) ^ m * C.Csum :=
    mul_le_mul_of_nonneg_left hθ (mul_nonneg hE (pow_nonneg hstep_pos.le m))
  have key := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθbd hmvC) hWM
  show |ψ k - (C.chain p X N).psiHat (Fz.step N) 1 k| ≤
    mvC cs.cm cs.CE K cs.Λ 1 * (2 * cs.KD * cs.Kw * C.Csum) * (Fz.step N) ^ m *
      ((C.chain p X N).W k * (C.chain p X N).M k)
  refine le_trans hbd ?_
  have e : mvC cs.cm cs.CE K cs.Λ 1 * (2 * cs.KD * cs.Kw * C.Csum) * (Fz.step N) ^ m *
      ((C.chain p X N).W k * (C.chain p X N).M k)
      = mvC cs.cm cs.CE K cs.Λ 1 * (2 * cs.KD * cs.Kw * (Fz.step N) ^ m * C.Csum) *
        ((C.chain p X N).W k * (C.chain p X N).M k) := by ring
  rw [e]
  linarith [key]

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bulkSolutionBound_of_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bulkSolutionBound_of_one_le

end FormalResearch.JacobiEigenvectors.TheoremA
