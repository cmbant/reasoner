module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.Statements
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbStableGauge
public import FormalResearch.JacobiEigenvectors.TheoremA.EigenvalueStatements
public import FormalResearch.JacobiEigenvectors.Setting.EigenSystem

/-!
# Paper J, Theorem B, L3.D: `cor:thb-stable` (stability of `Ĝ_m` under perturbations of order `h^{m+1}`)

Source: Paper J `thmB.tex`, Section `sec:thb-stable`, Corollary `cor:thb-stable` (after Bhatia--Davis--McIntosh, 1983):
"Assume the hypotheses of Theorem B, let `K ≥ 0`, and let `J'_h` be any Hermitian `(N+1) × (N+1)` matrix with
`‖J'_h - J_h‖ ≤ K h^{m+1}`.  For `0 < h ≤ h'_m(K)`, with `h'_m(K) ≤ h_m` and below the threshold of Corollary
`cor:eigen (c)`, the eigenvalues `X'_0 > ... > X'_N` of `J'_h` are simple, and for every unitary eigenvector matrix `U'_h` of
`J'_h` there is a diagonal unitary `Δ` with `‖Ĝ_m - U'_h Δ‖_op ≤ (C_m + C_* K) h^m`, where `C_*` depends only on the constant `c`
of `(eq:cor-gap)`.  If `J'_h` is a real Jacobi matrix with positive off-diagonal entries and `U'_h` is taken in the gauge
`(Ψ'_k)_0 > 0`, then `Δ = I`."

Claim class: **proved under explicit hypotheses** (`ThmB CP spl` and the gap bound `EigGapBound`, both explicit premises).

## Proved here (axiom-pinned)

* `corThbStable`: the corollary, from `ThmB CP spl` (its estimate `‖compMatrix - Um‖ ≤ C h^m`) and `EigGapBound F K`.  The
  conclusion is `ThbStableAt`: (a) simplicity of the eigenvalues of every Hermitian `J'` within `K0 h^{m+1}` of `J_h` and, for every
  unitary `U'` diagonalising `J'` with decreasing eigenvalues, a diagonal unitary `Δ` with `‖Ĝ_m - U' Δ‖ ≤ (C + C_* K0) h^m`
  (complex operator norm; `Ĝ_m` real), `C_* = 2 c_f / c`; (b) `Δ = I` for a real Jacobi `J'` (`IsJacobiPos`) with `IsEigenSystem`.
* `thb_stable_family`: the same for an arbitrary family `G` of reference matrices satisfying the Theorem B estimate (used by
  `CorThbDm`).  `thbStableAt_of`: the pointwise form.
* `EigGapBound F K`: the gap bound `c h ≤ X_i - X_{i+1}` of cor:eigen (c) (for the eigen-systems of `J_h`, `h ≤ h0`);
  `eigGapBound_of_corEigenGap1` derives it from the conclusion of `CorEigenGap1`.
* `jacobiMat_isJacobiPos`: `F.jacobiMat μ N` has positive bonds as soon as it has an `IsEigenSystem`
  (`isJacobiPos_of_eigenSystem`), so no positivity hypothesis is needed.

## Where the analysis is

`ThbStableWeyl.lean` (Weyl), `ThbStableSchur.lean` and `ThbStableMult.lean` (the multiplier `f = χ/x`, `‖(f_γ(x_j - y_k) E_jk)‖ ≤
(c_f/γ) ‖E‖`), `ThbStableCore.lean` (Sylvester identity, unit columns, phase, `thb_stable_pointwise`), `ThbStableGauge.lean`
(`Δ = I`).  This file only does the choice of `h'_m(K0)`: `h' = min(h_m, h_0, 1, c / (8 (K0+1)(c_f+1)))`, so that
`8 K0 h^{m+1} ≤ c h` and `c_f K0 h^m / c ≤ 1/2`.

## Differences from the paper

* `ThmB CP spl` and `EigGapBound F K` are premises (the paper's "hypotheses of Theorem B" and "threshold of cor:eigen (c)");
  `h'_m(K0)` is produced, `C_* = 2 c_f / c` with `c_f` the constant of `ThbStableMult` (existence, not computed).
* The paper's `J'_h` is a Hermitian matrix over `ℂ` and `Ĝ_m` is real: `‖Ĝ_m - U'Δ‖` is the complex operator norm of
  `cplx Ĝ_m - U' Δ`; the Jacobi case is stated for real matrices and the real operator norm (the two coincide on real matrices,
  `norm_cplx`).  "Eigenvalues simple" is `StrictAnti (thbEig hJ')`.
* The statement is for the eigen-systems of `J_h` and every unitary eigenvector matrix of `J'` with the eigenvalues in
  decreasing order (the paper's "columns ordered as the eigenvalues").

## Not formalised

Nothing of the corollary; `ThmB` and the gap bound for a given family are inputs.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.TheoremA
open scoped Matrix.Norms.L2Operator Matrix

variable {Par : Type*} [TopologicalSpace Par]

/-- The gap bound of `cor:eigen (c)` in the form used by `cor:thb-stable`. -/
def EigGapBound (F : SymbolFamily Par) (K : Set Par) : Prop :=
  ∃ c h0 : ℝ, 0 < c ∧ 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 →
    ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
      IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ i j : Fin (N + 1), (j : ℕ) = (i : ℕ) + 1 → c * F.step N ≤ X i - X j

theorem eigGapBound_of_corEigenGap1 {F : SymbolFamily Par} {K : Set Par} (hG : CorEigenGap1 F K)
    (hK : IsCompact K) (hH : HypOn F K) (hD : DM F K 1)
    (S : ℕ → Par → ℝ → ℝ) (δ Cn hM C : ℝ) (hδ : 0 < δ) (hS : SmoothExt F K 1 S δ Cn)
    (hR : EigenRule F K 1 S hM C) (hA : ActionFormula F K S) (x0 : Par → ℝ → ℝ)
    (hx0 : ∀ μ ∈ K, ∀ y ∈ Set.Icc 0 (Real.pi * F.L),
      x0 μ y ∈ Set.Icc (F.bandLo μ) (F.bandHi μ) ∧ S 0 μ (x0 μ y) = y) : EigGapBound F K := by
  obtain ⟨C1, c1, C2, h0, hh0, hc1, H⟩ := hG hK hH hD S δ Cn hM C hδ hS hR hA x0 hx0
  exact ⟨c1, h0, hc1, hh0, fun μ hμ N hN X Um hE i j hij => (H μ hμ N hN X Um hE i j hij).2.1⟩

lemma jacobiMat_symm (F : SymbolFamily Par) (μ : Par) (N : ℕ) :
    (F.jacobiMat μ N)ᵀ = F.jacobiMat μ N := by
  have := FormalResearch.JacobiEigenvectors.Setting.jacobiMat_isHermitian F μ N
  rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this

lemma jacobiMat_tri (F : SymbolFamily Par) (μ : Par) (N : ℕ) (i j : Fin (N + 1))
    (h : (i : ℕ) + 1 < (j : ℕ)) : F.jacobiMat μ N i j = 0 := by
  unfold SymbolFamily.jacobiMat
  simp only [Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> first | omega | rfl

lemma jacobiMat_super_nonneg (F : SymbolFamily Par) (μ : Par) (N : ℕ) (i j : Fin (N + 1))
    (h : (j : ℕ) = (i : ℕ) + 1) : 0 ≤ F.jacobiMat μ N i j := by
  have hij : i ≠ j := by intro e; subst e; omega
  unfold SymbolFamily.jacobiMat
  simp only [Matrix.of_apply, hij, h, ↓reduceIte]
  unfold SymbolFamily.bondA
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact le_rfl

/-- The Jacobi matrix of any family with an eigen-system has positive bonds. -/
theorem jacobiMat_isJacobiPos (F : SymbolFamily Par) (μ : Par) (N : ℕ) (X : Fin (N + 1) → ℝ)
    (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hE : IsEigenSystem (F.jacobiMat μ N) X Um) :
    IsJacobiPos (F.jacobiMat μ N) :=
  isJacobiPos_of_eigenSystem (jacobiMat_symm F μ N) (jacobiMat_tri F μ N) (jacobiMat_super_nonneg F μ N) hE


section Stable

variable {N : ℕ}

/-- **The conclusion of `cor:thb-stable` at one pair `(J, G)`**, for perturbations of size `b` and the bound `r`:
(a) for every Hermitian `J'` with `‖J' - J‖ ≤ b` the eigenvalues of `J'` are simple, and for every unitary eigenvector
matrix `U'` of `J'` (columns ordered as the decreasing eigenvalues) there is a diagonal unitary `Δ` with
`‖G - U' Δ‖ ≤ r`; (b) if `J'` is a real Jacobi matrix with positive off-diagonal entries and `U'` its eigenvector matrix in
the gauge `(Ψ'_k)_0 > 0`, then `Δ = I`: `‖G - U'‖ ≤ r`. -/
def ThbStableAt (J G : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (b r : ℝ) : Prop :=
  (∀ (J' : CMat N) (hJ' : J'.IsHermitian), ‖J' - cplx J‖ ≤ b →
      StrictAnti (thbEig hJ') ∧
      ∀ (U' : CMat N) (X' : Fin (N + 1) → ℝ), U'ᴴ * U' = 1 →
        J' * U' = U' * Matrix.diagonal (fun k => (X' k : ℂ)) → Antitone X' →
          ∃ Δ : Fin (N + 1) → ℂ, (∀ k, ‖Δ k‖ = 1) ∧ ‖cplx G - U' * Matrix.diagonal Δ‖ ≤ r) ∧
  (∀ (J' U' : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (X' : Fin (N + 1) → ℝ), IsJacobiPos J' →
      IsEigenSystem J' X' U' → ‖J' - J‖ ≤ b → ‖G - U'‖ ≤ r)

lemma ThbStableAt.mono {J G : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} {b r r' : ℝ}
    (h : ThbStableAt J G b r) (hr : r ≤ r') : ThbStableAt J G b r' := by
  refine ⟨fun J' hJ' hb => ?_, fun J' U' X' hJ'p hE hb => (h.2 J' U' X' hJ'p hE hb).trans hr⟩
  obtain ⟨h1, h2⟩ := h.1 J' hJ' hb
  refine ⟨h1, fun U' X' hU hX hA => ?_⟩
  obtain ⟨Δ, hΔ, hn⟩ := h2 U' X' hU hX hA
  exact ⟨Δ, hΔ, hn.trans hr⟩

/-- **`cor:thb-stable`, pointwise form**: `J` a real Jacobi matrix with an eigen-system `(X, U)` whose consecutive gaps
are at least `γ`, `G` with `‖G - U‖ ≤ R`, `b` with `8 b ≤ γ` and `c_f b/γ ≤ 1/2`: then `ThbStableAt J G b (R + 2 c_f b/γ)`. -/
theorem thbStableAt_of {J G U : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} {X : Fin (N + 1) → ℝ} {γ b R : ℝ}
    (hJ : IsJacobiPos J) (hE : IsEigenSystem J X U) (hγ : 0 < γ)
    (hcons : ∀ i j : Fin (N + 1), (j : ℕ) = (i : ℕ) + 1 → γ ≤ X i - X j)
    (hG : ‖G - U‖ ≤ R) (h8 : 8 * b ≤ γ) (hη : thbCf / γ * b ≤ 1 / 2) :
    ThbStableAt J G b (R + 2 * (thbCf / γ * b)) := by
  have hcUU : (cplx U)ᴴ * cplx U = 1 := by
    rw [cplx_conjTranspose, ← cplx_mul, hE.orth, cplx_one]
  have hcJU : cplx J * cplx U = cplx U * Matrix.diagonal (fun l => (X l : ℂ)) := by
    rw [← cplx_mul, hE.eig, cplx_mul, cplx_diagonal]
  have hJh : (cplx J).IsHermitian := cplx_isHermitian hJ.symm
  have hGU : ‖cplx G - cplx U‖ ≤ R := by rw [← cplx_sub, norm_cplx]; exact hG
  refine ⟨fun J' hJ' hb => ?_, fun J' U' X' hJ'p hE' hb => ?_⟩
  · have hb' : ‖cplx J - J'‖ ≤ b := by rw [norm_sub_rev]; exact hb
    obtain ⟨W, hW, hAW⟩ := exists_eigSystem_thbEig hJ'
    refine ⟨(thb_stable_pointwise hJh hJ' hcUU hW hcJU hAW hE.anti.antitone
      (thbEig_antitone hJ') hγ (fun i j hij => hcons i j hij) hb' h8 hη).1, ?_⟩
    intro U' X' hU' hX' hA'
    obtain ⟨-, hne, hbound⟩ := thb_stable_pointwise hJh hJ' hcUU hU' hcJU hX' hE.anti.antitone hA' hγ
      (fun i j hij => hcons i j hij) hb' h8 hη
    refine ⟨fun k => ((‖((cplx U)ᴴ * U') k k‖ : ℝ) : ℂ) / ((cplx U)ᴴ * U') k k, fun k => ?_, ?_⟩
    · have : ‖((cplx U)ᴴ * U') k k‖ ≠ 0 := norm_ne_zero_iff.2 (hne k)
      simp [norm_div, this]
    · calc ‖cplx G - U' * Matrix.diagonal (fun k => ((‖((cplx U)ᴴ * U') k k‖ : ℝ) : ℂ) /
            ((cplx U)ᴴ * U') k k)‖
          ≤ ‖cplx G - cplx U‖ + ‖U' * Matrix.diagonal (fun k => ((‖((cplx U)ᴴ * U') k k‖ : ℝ) : ℂ) /
            ((cplx U)ᴴ * U') k k) - cplx U‖ := by
              rw [← norm_neg (U' * _ - cplx U), neg_sub]
              exact norm_sub_le_norm_sub_add_norm_sub _ _ _ |>.trans_eq (by rw [norm_sub_rev (cplx U)])
        _ ≤ R + 2 * (thbCf / γ * b) := add_le_add hGU hbound
  · have hb' : ‖J - J'‖ ≤ b := by rw [norm_sub_rev]; exact hb
    have h2 := thb_jacobi_gauge hJ hJ'p hE hE' hγ (fun i j hij => hcons i j hij) hb' h8 hη
    calc ‖G - U'‖ ≤ ‖G - U‖ + ‖U' - U‖ := by
          rw [← norm_neg (U' - U), neg_sub]
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ R + 2 * (thbCf / γ * b) := add_le_add hG h2

end Stable


/-- **`cor:thb-stable`, family form.**  Let `G μ N X` be a family of reference matrices (the paper's `Ĝ_m`) with
`‖G - U‖ ≤ C h^m` for every eigen-system of `J_h` and `h ≤ h_m` (the estimate `(eq:thmB)` of Theorem B), `1 ≤ m`, and let the
gaps of `J_h` be at least `c h` (`EigGapBound`, cor:eigen (c)).  Then for every `K0 ≥ 0` there are `C_* = 2 c_f / c` and
`h' ≤ h_m` such that, for `h ≤ h'`, `ThbStableAt J_h G (K0 h^{m+1}) ((C + C_* K0) h^m)`: every Hermitian `J'` with
`‖J' - J_h‖ ≤ K0 h^{m+1}` has simple eigenvalues and for every unitary eigenvector matrix `U'` a diagonal unitary `Δ` with
`‖G - U' Δ‖ ≤ (C + C_* K0) h^m`, and `Δ = I` for a real Jacobi `J'` in the gauge `(Ψ'_k)_0 > 0`. -/
theorem thb_stable_family {F : SymbolFamily Par} {K : Set Par} {m : ℕ} {t0 C hm : ℝ}
    (G : ∀ (μ : Par) (N : ℕ), (Fin (N + 1) → ℝ) → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hm1 : 1 ≤ m) (hmpos : 0 < hm)
    (hB : ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ hm → F.step N ≤ t0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
        IsEigenSystem (F.jacobiMat μ N) Xs Um → ‖G μ N Xs - Um‖ ≤ C * F.step N ^ m)
    (hgap : EigGapBound F K) (K0 : ℝ) (hK0 : 0 ≤ K0) :
    ∃ Cs h' : ℝ, 0 ≤ Cs ∧ 0 < h' ∧ h' ≤ hm ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h' → F.step N ≤ t0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
        IsEigenSystem (F.jacobiMat μ N) Xs Um →
          ThbStableAt (F.jacobiMat μ N) (G μ N Xs) (K0 * F.step N ^ (m + 1))
            ((C + Cs * K0) * F.step N ^ m) := by
  obtain ⟨c, h0, hc, hh0, hg⟩ := hgap
  have hcf := thbCf_nonneg
  set M : ℝ := c / (8 * (K0 + 1) * (thbCf + 1)) with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  refine ⟨2 * thbCf / c, min (min hm h0) (min 1 M), by positivity,
    lt_min (lt_min hmpos hh0) (lt_min one_pos hMpos),
    (min_le_left _ _).trans (min_le_left _ _), fun μ hμ N hN hN0 Xs Um hE => ?_⟩
  set h := F.step N with hh
  have hhpos : 0 < h := FormalResearch.JB.stepSize_pos F.L_pos N
  have hhm : h ≤ hm := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hhh0 : h ≤ h0 := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hh1 : h ≤ 1 := hN.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhM : h ≤ M := hN.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hhm_le : h ^ m ≤ h := pow_le_of_le_one hhpos.le hh1 (by omega)
  have hT : 8 * ((K0 + 1) * (thbCf + 1) * h) ≤ c := by
    rw [hM, le_div_iff₀ (by positivity)] at hhM
    nlinarith
  have hKh : K0 * h ^ m ≤ K0 * h := mul_le_mul_of_nonneg_left hhm_le hK0
  have hKh' : K0 * h ≤ (K0 + 1) * (thbCf + 1) * h := by
    apply mul_le_mul_of_nonneg_right _ hhpos.le; nlinarith
  have hcKh : thbCf * (K0 * h) ≤ (K0 + 1) * (thbCf + 1) * h := by
    nlinarith [mul_nonneg hK0 hcf, hhpos]
  have hcKh2 : thbCf * (K0 * h ^ m) ≤ thbCf * (K0 * h) := mul_le_mul_of_nonneg_left hKh hcf
  have hJ : IsJacobiPos (F.jacobiMat μ N) := jacobiMat_isJacobiPos F μ N Xs Um hE
  have hcons : ∀ i j : Fin (N + 1), (j : ℕ) = (i : ℕ) + 1 → c * h ≤ Xs i - Xs j :=
    fun i j hij => hg μ hμ N hhh0 Xs Um hE i j hij
  have hch : 0 < c * h := mul_pos hc hhpos
  have hbpow : K0 * h ^ (m + 1) = (K0 * h ^ m) * h := by ring
  have h8 : 8 * (K0 * h ^ (m + 1)) ≤ c * h := by
    rw [hbpow]
    have : 8 * (K0 * h ^ m) ≤ c := by nlinarith
    nlinarith
  have hη : thbCf / (c * h) * (K0 * h ^ (m + 1)) ≤ 1 / 2 := by
    rw [hbpow, div_mul_eq_mul_div, div_le_iff₀ hch]
    nlinarith
  have key := thbStableAt_of hJ hE hch hcons (hB μ hμ N hhm hN0 Xs Um hE) h8 hη
  refine key.mono (le_of_eq ?_)
  field_simp
  ring


section Cor

variable {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- **`cor:thb-stable`** (Paper J `thmB.tex`, Section `sec:thb-stable`): from `ThmB` for the chart pair `CP` and the gap bound of
`cor:eigen (c)`, for every `K0 ≥ 0` there are `C` and `h_m` (those of `ThmB`, `C h_m^m < 1`), `C_*` and `h'_m(K0) ≤ h_m` such that
for `h ≤ h'_m` and every eigen-system of `J_h`, `ThbStableAt J_h Ĝ_m (K0 h^{m+1}) ((C + C_* K0) h^m)`
(simplicity of the eigenvalues of every Hermitian `J'` within `K0 h^{m+1}`, the diagonal unitary `Δ` with
`‖Ĝ_m - U'_h Δ‖ ≤ (C + C_* K0) h^m`, and `Δ = I` in the Jacobi gauge). -/
theorem corThbStable (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (spl : Fin CP.CI0.nb → ℝ) (hB : ThmB CP spl)
    (h1m : 1 ≤ m) (hK : Kidx = (m + 1) / 2) (hq : q = 2 * Kidx) (hcpt : IsCompact K) (hH : HypOn F K)
    (hD : DM F K (2 * Kidx + 1)) (hspl : CP.SplicesInWindow spl) (hgap : EigGapBound F K)
    (K0 : ℝ) (hK0 : 0 ≤ K0) :
    ∃ C hm Cs h' : ℝ, 0 < hm ∧ C * hm ^ m < 1 ∧ 0 ≤ Cs ∧ 0 < h' ∧ h' ≤ hm ∧
      ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h' → F.step N ≤ t0 →
        ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
          IsEigenSystem (F.jacobiMat μ N) Xs Um →
            ThbStableAt (F.jacobiMat μ N) (compMatrix CP.CI0 spl μ N Xs) (K0 * F.step N ^ (m + 1))
              ((C + Cs * K0) * F.step N ^ m) := by
  obtain ⟨C, hm, hmpos, hCm, hall⟩ := hB h1m hK hq hcpt hH hD hspl
  obtain ⟨Cs, h', hCs, hh', hh'm, hfam⟩ := thb_stable_family (F := F) (K := K) (m := m) (t0 := t0) (C := C) (hm := hm)
    (fun μ N Xs => compMatrix CP.CI0 spl μ N Xs) h1m hmpos
    (fun μ hμ N hN hN0 Xs Um hE => (hall μ hμ N hN hN0 Xs Um hE).1) hgap K0 hK0
  exact ⟨C, hm, Cs, h', hmpos, hCm, hCs, hh', hh'm, hfam⟩

end Cor

end FormalResearch.JacobiEigenvectors.TheoremB

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.corThbStable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.corThbStable

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.thb_stable_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.thb_stable_family

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.thbStableAt_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.thbStableAt_of

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.jacobiMat_isJacobiPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.jacobiMat_isJacobiPos

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.eigGapBound_of_corEigenGap1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.eigGapBound_of_corEigenGap1
