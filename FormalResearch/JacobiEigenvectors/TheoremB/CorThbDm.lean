module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbStable
public import FormalResearch.JacobiEigenvectors.TheoremA.SmoothSpectrum
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumAssemblyBulk
public import FormalResearch.JB.JBPolar
public import FormalResearch.JB.JBFermion

/-!
# Paper J, Theorem B, L3.Dm: `cor:thb-Dm` (`CorThbDm`) from `ThmB` for the truncated family and `cor:thb-stable`

Source: Paper J `thmB.tex`, Corollary `cor:thb-Dm` ("The eigenvector matrix from `(D_m)`"), proof; statement frozen as `CorThbDm`
in `TheoremB/Statements.lean` (finding F-B6).

Claim class: **proved under explicit hypotheses** (the two premises below).

## Proved here (axiom-pinned)

* `corThbDm_of_thmB : ThmBConcl CP spl → EigGapBound (truncFamily F m) K → CorThbDm CP spl`: the frozen statement, with
  `ThmBConcl CP spl` the conclusion of `ThmB` for the chart pair `CP` of `truncFamily F m` (premise 1) and the gap bound of
  `cor:eigen (c)` for `truncFamily F m` (premise 2).  The proof is the paper's: `thb_stable_family` for the base matrix
  `tilde J_h` with `Ĝ^{jet}_m`, the real Jacobi matrix `J'_h := J_h` and `K0 := C'`, `‖J_h - tilde J_h‖ ≤ C' h^{m+1}`
  (`jacobiMat_trunc_norm_le`, from `smo_SM` and `(D_m)`), the Jacobi gauge `Δ = I` (the eigen-system `(X, U)` of `J_h`, in the
  gauge `(Ψ_k)_0 > 0`, is that of a real Jacobi matrix with positive bonds, `jacobiMat_isJacobiPos`), giving
  `‖Ĝ^{jet}_m - U_h‖ ≤ (C_m + C_* C') h^m`; then `lem:thb-polar` (`FormalResearch.JB.jb_polar`) gives the orthogonal polar factor and
  the bound `2 C h^m`, once `C h_m^m < 1`.
* `thmBConcl_of_thmB`: `ThmB CP spl` is `hypotheses → ThmBConcl CP spl`.
* `corFermions_of_thmB : ThmB CP spl → CorFermions CP spl` (`cor:fermions` for `Ĝ_m`, from `jb_fermions`).
* `jacobiMat_trunc_norm_le`: `‖J_h - tilde J_h‖_op ≤ C' h^{m+1}` (eq:l2-trunc) under `(H1)`, `(D_m)` on a compact `K`.

## The two premises

1. `ThmBConcl CP spl` for `CP : ChartPair` of `truncFamily F m`.  `ThmB CP spl` needs the hypothesis `StdDM (truncFamily F m) K Kidx` (finding **F-DD1**): the consequences of `(D_{2 Kidx+1})` that the proof uses, namely `(D_1)` and
   `FrozenReg` (the paper's `(E_Kbar)` of the frozen truncated matrices, budget `r(m) >= r(max(2 Kbar - 1, 0))`, remainder after the jet `2 Kidx + 1`).  `stdDM_trunc` derives it from `DM F K m`, `1 <= m`, `Kidx = (m+1)/2`.
   (`DM (truncFamily F m) K (2 Kidx + 1)` itself is **not** a consequence of `DM F K m`: the truncated jets keep the regularity `C^{r(m) - 10 floor(j/2)}` of `F`, whereas it asks `C^{r(2 Kidx + 1) - 10 floor(j/2)}` and
   `r(2 Kidx + 1) > r(m)` (`regBudget`); this is why the frozen `ThmB` is stated with `StdDM`.)  `corThbDm_of_thmB` takes `ThmBConcl CP spl`; it is discharged by `thmBConcl_of_thmB` from `ThmB CP spl`.
2. `EigGapBound (truncFamily F m) K`: the gap bound `c h ≤ X_i - X_{i+1}` for `tilde J_h`, i.e. the conclusion of `CorEigenGap1 (truncFamily F m) K`.  `CorThbGap.lean` (`eigGapBound_of_layer4`) derives it from the Layer-4 chart
   inputs `Layer4Inputs (truncFamily F m) K 1` (`thmAi_assembled` gives `S`, `bandSlope_of_layer4` the slope, `BandSlope.surj` the inverse `x_0`) and `DM (truncFamily F m) K 1` (`stdDM_trunc`, `.d1`); `CorThbFinal.lean`
   (`corThbDm_proved`) takes the Layer-4 inputs, `corThbDm_of_gap` the gap bound itself.

## Differences from the paper

* The constants: `C = max(C_m, 0) + C_* C'`, `h_m` small enough that `C h_m^m < 1`.  `C_* = 2 c_f / c` with `c_f` of `ThbStableMult`.
* `Ĝ^{jet}_m` is `compMatrix CP.CI0 spl μ N Xt`, built from the eigenvalues `Xt` of `tilde J_h` (an eigen-system `(Xt, Ut)` of `tilde J_h` is
  only used through its eigenvalues and the estimate of `ThmBConcl`), as in the frozen statement.
* The final `Corollary cor:fermions holds with Ĝ^{jet}_m and its polar factor` part of the paper's statement is the last conjunct of `CorThbDm`: `JB.FermionConcl Ĝ^{jet}_m U_h (C h^m)` (`FormalResearch/JB/JBFermion.lean`:
  the compression bounds `3 C h^m` and, for the polar factor, `4 C h^m`; the eigenvalue comparison `3 C h^m`; the entanglement energies `8 C h^m/τ`), from the two bounds of (D_m) by `jb_fermions`.  Real `F`, `P`, `J` only (the paper allows complex `F`).

## Not formalised

Nothing beyond the premises above.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.TheoremA
open scoped Matrix.Norms.L2Operator MatrixOrder Matrix

variable {Par : Type*} [TopologicalSpace Par]

/-- the `ℓ²` bound is the operator norm bound -/
lemma norm_le_of_sq_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ x : Fin n → ℝ, ∑ i, (A *ᵥ x) i ^ 2 ≤ r ^ 2 * ∑ i, x i ^ 2) : ‖A‖ ≤ r := by
  rw [Matrix.l2_opNorm_def, ContinuousLinearMap.opNorm_le_iff hr]
  intro x
  have hx := h x.ofLp
  have e1 : ‖(((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) (n := Fin n)).trans
      LinearMap.toContinuousLinearMap) A) x‖ ^ 2 = ∑ i, (A *ᵥ x.ofLp) i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) (n := Fin n)).trans LinearMap.toContinuousLinearMap A x).ofLp i
        = (A *ᵥ x.ofLp) i := rfl
    rw [e, Real.norm_eq_abs, sq_abs]
  have e2 : ‖x‖ ^ 2 = ∑ i, x.ofLp i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]
  have : ‖(((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin n) (n := Fin n)).trans
      LinearMap.toContinuousLinearMap) A) x‖ ^ 2 ≤ (r * ‖x‖) ^ 2 := by
    rw [e1, mul_pow, e2]; exact hx
  exact le_of_sq_le_sq (by simpa using this) (mul_nonneg hr (norm_nonneg _))


/-- **`‖J_h - tilde J_h‖ ≤ C' h^{m+1}`** (eq:l2-trunc) from `(H1)`, `(D_m)` on a compact `K`: `smo_SM` with its operator-norm
conclusion (b), the truncated matrix `truncSM E j = truncFamily E j`. -/
theorem jacobiMat_trunc_norm_le (E : SymbolFamily Par) (K : Set Par) (j : ℕ) (hK : IsCompact K)
    (hH : HypOn E K) (hD : DM E K j) :
    ∃ C' h0 : ℝ, 0 < C' ∧ 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, E.step N ≤ h0 →
      ‖E.jacobiMat μ N - (truncFamily E j).jacobiMat μ N‖ ≤ C' * E.step N ^ (j + 1) := by
  obtain ⟨g, hg⟩ := hH
  obtain ⟨KG, hKG⟩ := jet_bdd K hK E.L j _ E.G (fun i hi => (hD.reg i hi).1)
  obtain ⟨C0, hC0⟩ := hD.rem
  by_cases hKe : K = ∅
  · exact ⟨1, 1, one_pos, one_pos, fun μ hμ => by simp [hKe] at hμ⟩
  obtain ⟨μ0, hμ0⟩ := Set.nonempty_iff_ne_empty.mpr hKe
  have hgpos : 0 < g := (hg μ0 hμ0).gstar_pos
  obtain ⟨C', h0, hC', hh0, hmain⟩ := smo_SM E K j g hgpos (fun μ hμ s hs => (hg μ hμ).G0_lb s hs)
    (fun i hi => ⟨KG i, fun μ hμ s hs => hKG i hi μ hμ s hs⟩) C0
    (fun μ hμ N n h0 h1 => (hC0 μ hμ N _ (sNode_mem_Icc E N n h0 h1)).1)
    (fun μ hμ N n h0 h1 => (hC0 μ hμ N _ (uNode_mem_Icc E N n h0 h1)).2)
  refine ⟨C', h0, hC', hh0, fun μ hμ N hN => ?_⟩
  obtain ⟨-, hb, -⟩ := hmain μ hμ N hN
  have hst : 0 < E.step N := FormalResearch.JB.stepSize_pos E.L_pos N
  exact norm_le_of_sq_bound _ (by positivity) hb


section Dm

/-- **F-DD1 discharged**: `(D_m)`, `1 <= m` and `Kidx = (m+1)/2` give `StdDM (truncFamily F m) K Kidx`, the part of `(D_{2 Kidx+1})` that `ThmB` uses, for the truncated family `tilde J_h`
(jets beyond `m` zero, no remainder; `(D_1)` by `dm_truncSM`, `dm_mono`; the regularity and remainder data of the frozen matrices by `frozenReg_trunc`, with the budget `r(m) >= r(max(2 Kidx - 1, 0))`).
`DM (truncFamily F m) K (2 Kidx + 1)` is not a consequence of `DM F K m`. -/
theorem stdDM_trunc {F : SymbolFamily Par} {K : Set Par} {m Kidx : ℕ} (h1m : 1 ≤ m) (hKidx : Kidx = (m + 1) / 2) (hK : IsCompact K)
    (hD : DM F K m) : StdDM (truncFamily F m) K Kidx :=
  ⟨dm_mono _ K h1m hK (dm_truncSM F K m hD), regBudget m, frozenReg_trunc F K m Kidx hKidx hD⟩

variable {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- The conclusion of `ThmB` for a chart pair (without the hypotheses of `ThmB`): constants `C`, `h_m` with `C h_m^m < 1`
and, for `h ≤ h_m` and every eigen-system, `‖Ĝ_m - U_h‖ ≤ C h^m` and the polar factor of `Ĝ_m` is orthogonal and within
`2 C h^m` of `U_h`.  `ThmB CP spl` is `hypotheses → ThmBConcl CP spl` (`thmBConcl_of_thmB`). -/
def ThmBConcl (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (spl : Fin CP.CI0.nb → ℝ) : Prop :=
  ∃ C hm : ℝ, 0 < hm ∧ C * hm ^ m < 1 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hm → F.step N ≤ t0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ‖compMatrix CP.CI0 spl μ N Xs - Um‖ ≤ C * F.step N ^ m ∧
        (compMatrix CP.CI0 spl μ N Xs * (CFC.sqrt ((compMatrix CP.CI0 spl μ N Xs)ᵀ * compMatrix CP.CI0 spl μ N Xs))⁻¹)ᵀ *
            (compMatrix CP.CI0 spl μ N Xs * (CFC.sqrt ((compMatrix CP.CI0 spl μ N Xs)ᵀ * compMatrix CP.CI0 spl μ N Xs))⁻¹) = 1 ∧
        ‖compMatrix CP.CI0 spl μ N Xs * (CFC.sqrt ((compMatrix CP.CI0 spl μ N Xs)ᵀ * compMatrix CP.CI0 spl μ N Xs))⁻¹ - Um‖
          ≤ 2 * C * F.step N ^ m

theorem thmBConcl_of_thmB (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (spl : Fin CP.CI0.nb → ℝ) (hB : ThmB CP spl) (h1m : 1 ≤ m) (hK : Kidx = (m + 1) / 2) (hq : q = 2 * Kidx)
    (hcpt : IsCompact K) (hH : HypOn F K) (hD : StdDM F K Kidx) (hspl : CP.SplicesInWindow spl) :
    ThmBConcl CP spl :=
  hB h1m hK hq hcpt hH hD hspl

/-- **`cor:fermions`** (`CorFermions`) from `ThmB` (`‖Ĝ_m - U_h‖ ≤ C h^m < 1`) by the matrix statement `JB.jb_fermions`. -/
theorem corFermions_of_thmB (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (spl : Fin CP.CI0.nb → ℝ) (hB : ThmB CP spl) : CorFermions CP spl := by
  intro h1m hK hq hcpt hH hD hspl
  obtain ⟨C, hm, hm0, hCm, hall⟩ := hB h1m hK hq hcpt hH hD hspl
  refine ⟨C, hm, hm0, hCm, fun μ hμ N hN hN0 Xs Um hE => ?_⟩
  have hb := (hall μ hμ N hN hN0 Xs Um hE).1
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hlt : C * F.step N ^ m < 1 := by
    rcases le_or_gt 0 C with hC | hC
    · exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hst.le hN m) hC).trans_lt hCm
    · have : C * F.step N ^ m ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC.le (by positivity)
      linarith
  exact FormalResearch.JB.jb_fermions _ Um hE.orth hb hlt

/-- **`cor:thb-Dm`** (`CorThbDm`, frozen in `Statements.lean`) from `ThmB` for the truncated chart pair (`ThmBConcl`), the gap bound of
`cor:eigen (c)` for the truncated family (`EigGapBound`), and the cor:thb-stable argument (`thb_stable_family`, Jacobi gauge
`Δ = I`) with `J_h := tilde J_h`, `J'_h := J_h`, `‖J_h - tilde J_h‖ ≤ C' h^{m+1}` (`jacobiMat_trunc_norm_le`), then the polar lemma
`lem:thb-polar` (`FormalResearch.JB.jb_polar`). -/
theorem corThbDm_of_thmB
    (CP : ChartPair (F := truncFamily F m) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (spl : Fin CP.CI0.nb → ℝ) (hB : ThmBConcl CP spl) (hgap : EigGapBound (truncFamily F m) K) :
    CorThbDm CP spl := by
  intro h1m hK hq hcpt hH hD hspl
  obtain ⟨C0, hm0, hm0pos, hCm0, hall⟩ := hB
  obtain ⟨C', h0', hC', hh0', hnorm⟩ := jacobiMat_trunc_norm_le F K m hcpt hH hD
  obtain ⟨Cs, h', hCs, hh', hh'm, hfam⟩ := thb_stable_family (F := truncFamily F m) (K := K) (m := m)
    (t0 := t0) (C := C0) (hm := hm0) (fun μ N Xs => compMatrix CP.CI0 spl μ N Xs) h1m hm0pos
    (fun μ hμ N hN hN0 Xs Um hE => (hall μ hμ N hN hN0 Xs Um hE).1) hgap C' hC'.le
  set Cf : ℝ := max C0 0 + Cs * C' with hCf
  have hCf0 : 0 ≤ Cf := by
    have : 0 ≤ Cs * C' := mul_nonneg hCs hC'.le
    have := le_max_right C0 0
    linarith
  set hf : ℝ := min (min h' h0') (min 1 (1 / (2 * (Cf + 1)))) with hhf
  have hfpos : 0 < hf := lt_min (lt_min hh' hh0') (lt_min one_pos (by positivity))
  have hf1 : hf ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hf2 : hf ≤ 1 / (2 * (Cf + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hfm : hf ^ m ≤ hf := pow_le_of_le_one hfpos.le hf1 (by omega)
  refine ⟨Cf, hf, hfpos, ?_, ?_⟩
  · have h1 : Cf * hf ^ m ≤ Cf * (1 / (2 * (Cf + 1))) :=
      mul_le_mul_of_nonneg_left (hfm.trans hf2) hCf0
    have h2 : Cf * (1 / (2 * (Cf + 1))) < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith
    exact h1.trans_lt h2
  · intro μ hμ N hN hN0 Xt Ut hEt Xs Um hEs
    have hhf' : F.step N ≤ hf := hN
    have hh'N : (truncFamily F m).step N ≤ h' := hhf'.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hh0N : F.step N ≤ h0' := hhf'.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
    have key := hfam μ hμ N hh'N hN0 Xt Ut hEt
    have hJ' : IsJacobiPos (F.jacobiMat μ N) := jacobiMat_isJacobiPos F μ N Xs Um hEs
    have hb := hnorm μ hμ N hh0N
    have hG := key.2 (F.jacobiMat μ N) Um Xs hJ' hEs hb
    have hpow : 0 ≤ F.step N ^ m := by positivity
    have hGf : ‖compMatrix CP.CI0 spl μ N Xt - Um‖ ≤ Cf * F.step N ^ m := by
      refine hG.trans (mul_le_mul_of_nonneg_right ?_ hpow)
      have := le_max_left C0 0
      linarith
    have hε1 : Cf * F.step N ^ m < 1 := by
      have : Cf * F.step N ^ m ≤ Cf * hf ^ m :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hst.le hhf' m) hCf0
      refine this.trans_lt ?_
      have h1 : Cf * hf ^ m ≤ Cf * (1 / (2 * (Cf + 1))) :=
        mul_le_mul_of_nonneg_left (hfm.trans hf2) hCf0
      refine h1.trans_lt ?_
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith
    have hlt : ‖compMatrix CP.CI0 spl μ N Xt - Um‖ < 1 := hGf.trans_lt hε1
    obtain ⟨-, horth, -, -, hpol, -⟩ := FormalResearch.JB.jb_polar (compMatrix CP.CI0 spl μ N Xt) Um hEs.orth hlt
    refine ⟨hGf, horth, hpol.trans ?_, FormalResearch.JB.jb_fermions _ Um hEs.orth hGf hε1⟩
    nlinarith

end Dm

end FormalResearch.JacobiEigenvectors.TheoremB

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.corFermions_of_thmB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.corFermions_of_thmB

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.corThbDm_of_thmB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.corThbDm_of_thmB

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.jacobiMat_trunc_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.jacobiMat_trunc_norm_le

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.thmBConcl_of_thmB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.thmBConcl_of_thmB
