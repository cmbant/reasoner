module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Setting.EigenSystem
public import FormalResearch.JacobiEigenvectors.TheoremA.Statements
public import FormalResearch.JacobiEigenvectors.TheoremA.EigenvalueStatements
public import FormalResearch.JacobiEigenvectors.TheoremA.SpectrumUnique

/-!
# Paper J, Layer 2: the eigenvalue rule `thm:smo-spec`: the chain of lemmas, and the uniqueness part (L2.S6 (b), (c))

Source: Paper J `thmA.tex` `thm:smo-spec` (Section "Every eigenvalue"), `app_thmA.tex` Section "The eigenvalue rule from the real charts"
(`lem:smo-bulkphase`, `lem:smo-SM`, `lem:smo-S0`, `thm:smo-BSr`, proof of `thm:smo-spec`).  Frozen statements: `ThmSmoSpec`, `ThmAi` (`TheoremA/Statements.lean`).

## The chain (names; `[P]` proved here or in the cited module, `[H]` a hypothesis of the next link, `[O]` open, with its owner)

1. **Windows, bulk (`lem:smo-bulkphase` (1)--(3)), S1** `[O]`.  (1) the oscillatory phases of `psi-hat^{L,R}` (from `ParabolicCylinderFacts.phase_osc`),
   (2) `C(X) = a rho_L rho_R [sin theta sin(S_0/h - pi/2) + O(h)]`, (3) the labelled windows: *every eigenvalue* `X_k(t)` in a block satisfies
   `S_0^{(t)}(X_k) = pi h (k + 1/2) + O(h^2)` with `k` its index from the top (`PropThaCount` + the soft-edge labels `PropThaW2` (3)).
   Its conclusion enters here as the Prop `BulkWindowLabels` (`TheoremA/BulkPhase.lean`), and (1), (2) are *not* needed by (4) below as formalised: the frozen field
   `BulkPhaseInputs.casoratian` is the all-orders form (4).
2. **Phase at an eigenvalue, S2** `[P]` `TheoremA/BulkPhase.lean`: `bulk_eigen_sin`, `bulk_eigen_quant`, `bulk_BSr2` = `eq:smo-BSr2` on a bulk block
   `Sigma(X_k(t), t, h) = pi h (k + 1/2) + O(h^{M+1})`, from `BulkPhaseInputs` (with the prefactor lower bound `BulkCasPre`, finding F-S2-1), `bulkSolutionBound_of_one_le`,
   positive bonds, `BulkWindowLabels`, `BulkSigmaBdd` (finding F-S2-2).  The soft windows `Sigma_pm` (`PropThaW2` (3)/(4), `muS`) are `[O]` (L2.C7 / L2.S6).
3. **Taylor substitution `t = h`, S3** `[P]` `TheoremA/SpectrumTaylor.lean`: `phase_substitution`: `S_l = Scoef Sigma l` is `C^{M+1}` and
   `Sigma(X, h, h) = sum_l h^l S_l(X) + O(h^{M+1})`; on a soft window the same lemma applies to `Sigma_pm` (also `C^{2M+1}`).  Needs the `t`-derivative bound (finding F-S2-2).
4. **`t = h` is the matrix** `[P]` `frozenFamily_jacobiMat_at_step` (`Setting/JacobiFamily.lean`): `J^{(h)}_h = J_h`; `smo_SM` (`TheoremA/TruncationSM.lean`, L2.S4):
   `|X_k - tilde X_k| <= C h^{M+1}`.  Chain of local statements `[H]`: for each interval `I` of the cover (bulk blocks and the two soft windows) and every eigenvalue `X_k`
   of `tilde J_h` in `I`: `sum_{l<=M} h^l S^I_l(X_k) = pi h (k + 1/2) + O(h^{M+1})` (`eq:smo-BSr3` with 2. and 3.).
5. **Step 0, density, matching, S5** `[O]` (not mine): `StepZero`/`StepZeroD0` (`EigenvalueStatements.lean`), the density statement `EigDensity` below
   (every point of the band is within `C h` of an eigenvalue: `S_0^I` has `|S_0'| >= c`, the numbers `pi h (k+1/2)` are `pi h`-dense in `[0, pi L]`), and the matching
   `S^I_l = S^{I'}_l` on overlaps (the *same* argument as 6., applied to `d_l = S^I_l - S^{I'}_l` on `I cap I'`, with the eigenvalues of `tilde J_h` in `I cap I'`).
6. **Uniqueness, extensions, S6 (b), (c)** `[P]` here: `smo_unique`, `smo_extend`, from `unique_core` (`TheoremA/SpectrumUnique.lean`) and the inputs 5.
7. **Dependence on the jets, S7** `[P]` here (`smo_jets`), from 6., `smo_SM` and the reduction of the rule to a lower order.
8. **The assembly, S6** `ThmSmoSpec`, `ThmAi` `[O]`: cover the band by `J_nu`, `I_+`, `I_-` (finitely many localising neighbourhoods in `mu`), glue the local `S^I_l` by 5.,
   extend to `[X_s^- - delta, X_s^+ + delta]` as `C^{M+1}` functions (the barrier-side extension of `thm:smo-MPS`), pass from `tilde J_h` to `J_h` by `smo_SM`.
   `C^infty` jets: apply the theorem at every `M' >= M` to `truncSM F M` (needs `smo_jets` and `smo_SM`).

## Statement-level findings (precise minimal corrections; the frozen statements are not edited)

* **F-S6-1** `ThmSmoSpec` (b), (c) quantify `SmoothExt F K M S delta Cn` with no `0 < delta` (it is in `ThmAi` only).  For `delta <= 0` the smoothness domain
  `[X_s^- - delta, X_s^+ + delta]` is contained in the band, the eigenvalues just outside the band are unconstrained, and the uniqueness argument (flat bound at the eigenvalues outside the band)
  breaks down.  **Correction:** add `0 < delta`, `0 < delta'` to (b) and (c).  (`smo_unique`, `smo_extend` have them as hypotheses.)
* **F-S6-2** (b), (c) need `X_s^- < X_s^+` (a non-degenerate band): it follows from (H1)--(H3) (`f_- < f_+` at the maximiser of `f_+`), not formalised; here a hypothesis `hband`.
* **F-S6-3** `StepZeroD0`, `EigDensity` take `DM F K 0`; `ThmSmoSpec` has `DM F K M`.  `DM F K 0` follows from `DM F K M` (jets bounded on `[0, L]` by continuity); here a hypothesis `hD0`.

## Not formalised

The chain items marked `[O]`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting

variable {Par : Type*} [TopologicalSpace Par]

/-! ### Inputs of the uniqueness argument -/

/-- **Density of the eigenvalues in the band** (`thm:smo-spec` proof, paragraph "Density"; L2.S5, the input of the uniqueness): every `Y in [X_s^-, X_s^+]` lies within `C h`
of an eigenvalue of `J_h`, for every eigen-system, uniformly in `mu in K`. -/
def EigDensity (F : SymbolFamily Par) (K : Set Par) : Prop :=
  IsCompact K → HypOn F K → DM F K 0 →
    ∃ C h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ∀ Y ∈ Icc (F.bandLo μ) (F.bandHi μ), ∃ k : Fin (N + 1), |Xs k - Y| ≤ C * F.step N

/-- The set of eigenvalues of `J_h(mu)`, `h = L/(N+1)` (over all eigen-systems; they all give the same spectrum). -/
def eigSet (F : SymbolFamily Par) (μ : Par) (N : ℕ) : Set ℝ :=
  {x | ∃ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
    IsEigenSystem (F.jacobiMat μ N) Xs Um ∧ ∃ k : Fin (N + 1), Xs k = x}

/-- The steps `h = L/(N+1)` tend to `0`. -/
lemma step_small (F : SymbolFamily Par) {ε : ℝ} (hε : 0 < ε) : ∃ N0 : ℕ, ∀ N ≥ N0, F.step N < ε := by
  refine ⟨⌈F.L / ε⌉₊, fun N hN => ?_⟩
  unfold SymbolFamily.step FormalResearch.JB.stepSize
  have h1 : F.L / ε ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  rw [div_lt_iff₀ (by positivity)]
  rw [div_le_iff₀ hε] at h1
  nlinarith [F.L_pos]

/-- Eigen-systems exist for small `h` (positive `G_h` at the nodes, from `(H1)` and `(D_0)`). -/
lemma exists_eig_small (F : SymbolFamily Par) (K : Set Par) (hH : HypOn F K) (hD : DM F K 0) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 →
      ∃ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um := by
  obtain ⟨g, hg⟩ := hH
  obtain ⟨C, hC⟩ := hD.rem
  by_cases hK : K = ∅
  · exact ⟨1, one_pos, fun μ hμ => by simp [hK] at hμ⟩
  obtain ⟨μ0, hμ0⟩ := Set.nonempty_iff_ne_empty.mpr hK
  have hgpos : 0 < g := (hg μ0 hμ0).gstar_pos
  refine ⟨g / (2 * (|C| + 1)), div_pos hgpos (by positivity), ?_⟩
  intro μ hμ N hN
  apply exists_eigenSystem
  intro n hn0 hnN
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hL : F.step N * ((N : ℝ) + 1) = F.L := by
    unfold SymbolFamily.step FormalResearch.JB.stepSize
    exact div_mul_cancel₀ F.L (by positivity)
  have hnR : (n : ℝ) + 1 ≤ (N : ℝ) := by
    have : n + 1 ≤ (N : ℤ) := by omega
    exact_mod_cast this
  have hn0R : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
  have hs : sNode (F.step N) n ∈ Icc 0 F.L := by
    unfold sNode
    constructor
    · positivity
    · nlinarith
  have h1 := (hC μ hμ N _ hs).1
  have h2 := (hg μ hμ).G0_lb _ hs
  simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, pow_one] at h1
  have h3 : F.step N * (|C| + 1) ≤ g / 2 := by
    have := mul_le_mul_of_nonneg_right hN (by positivity : (0 : ℝ) ≤ 2 * (|C| + 1))
    have e : g / (2 * (|C| + 1)) * (2 * (|C| + 1)) = g := by field_simp
    nlinarith [this, e]
  have h4 : C * F.step N ≤ |C| * F.step N := mul_le_mul_of_nonneg_right (le_abs_self _) hst.le
  have h5 := (abs_le.mp h1).1
  nlinarith [abs_nonneg C]

/-- A point within `e` of `[a, b]`... : the clamp. -/
lemma near_band {a b x C h : ℝ} (hab : a ≤ b) (hCh : 0 ≤ C * h) (hx : a - C * h ≤ x ∧ x ≤ b + C * h) :
    ∃ y ∈ Icc a b, |x - y| ≤ C * h := by
  refine ⟨max a (min x b), ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩, ?_⟩
  rcases le_total x a with h1 | h1
  · have : max a (min x b) = a := by
      apply le_antisymm (max_le le_rfl ((min_le_left _ _).trans h1)) (le_max_left _ _)
    rw [this, abs_of_nonpos (by linarith)]
    linarith [hx.1]
  · rcases le_total x b with h2 | h2
    · have : max a (min x b) = x := by
        rw [min_eq_left h2]; exact max_eq_right h1
      rw [this, sub_self, abs_zero]
      linarith [hx.1, hx.2]
    · have : max a (min x b) = b := by
        rw [min_eq_right h2]; exact max_eq_right hab
      rw [this, abs_of_nonneg (by linarith)]
      linarith [hx.2]

/-- Derivative bound inside the closed smoothness interval, transferred to `iteratedDeriv` at interior points. -/
lemma iterDeriv_of_within {f : ℝ → ℝ} {p q Cn : ℝ} {n : ℕ} (hpq : p < q) (hf : ContDiffOn ℝ (n : WithTop ℕ∞) f (Icc p q))
    (hb : ∀ i ≤ n, ∀ x ∈ Icc p q, |iteratedDerivWithin i f (Icc p q) x| ≤ Cn) {x : ℝ} (hx : x ∈ Ioo p q) {i : ℕ} (hi : i ≤ n) :
    ContDiffAt ℝ (n : WithTop ℕ∞) f x ∧ |iteratedDeriv i f x| ≤ Cn := by
  have hmem : Icc p q ∈ nhds x := Icc_mem_nhds hx.1 hx.2
  have hca : ContDiffAt ℝ (n : WithTop ℕ∞) f x := hf.contDiffAt hmem
  refine ⟨hca, ?_⟩
  have := iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hpq) (hca.of_le (by exact_mod_cast hi)) (Ioo_subset_Icc_self hx)
  rw [← this]
  exact hb i hi x (Ioo_subset_Icc_self hx)

/-- Regularity and derivative bounds of a difference of two coefficient families on the common open interval (fixed `mu`). -/
lemma smoothExt_diff {S S' : ℕ → ℝ → ℝ} {a b δ δ' Cn Cn' : ℝ} {M : ℕ} (hδ : 0 < δ) (hδ' : 0 < δ') (hab : a < b)
    (h1 : ∀ j ≤ M, ContDiffOn ℝ ((M + 1 : ℕ) : WithTop ℕ∞) (S j) (Icc (a - δ) (b + δ)) ∧
      ∀ i ≤ M + 1, ∀ x ∈ Icc (a - δ) (b + δ), |iteratedDerivWithin i (S j) (Icc (a - δ) (b + δ)) x| ≤ Cn)
    (h3 : ∀ j ≤ M, ContDiffOn ℝ ((M + 1 : ℕ) : WithTop ℕ∞) (S' j) (Icc (a - δ') (b + δ')) ∧
      ∀ i ≤ M + 1, ∀ x ∈ Icc (a - δ') (b + δ'), |iteratedDerivWithin i (S' j) (Icc (a - δ') (b + δ')) x| ≤ Cn') :
    (∀ j ≤ M, ContDiffOn ℝ ((M + 1 : ℕ) : WithTop ℕ∞) (fun x => S j x - S' j x) (Ioo (a - min δ δ') (b + min δ δ'))) ∧
    (∀ j ≤ M, ∀ i ≤ M + 1, ∀ x ∈ Ioo (a - min δ δ') (b + min δ δ'),
      |iteratedDeriv i (fun x => S j x - S' j x) x| ≤ Cn + Cn') := by
  have hpq1 : a - δ < b + δ := by linarith
  have hpq2 : a - δ' < b + δ' := by linarith
  have hm1 := min_le_left δ δ'
  have hm2 := min_le_right δ δ'
  refine ⟨fun j hj => ?_, fun j hj i hi x hx => ?_⟩
  · have e1 := (h1 j hj).1.mono (fun x (hx : x ∈ Ioo (a - min δ δ') (b + min δ δ')) =>
      (⟨by linarith [hx.1], by linarith [hx.2]⟩ : x ∈ Icc (a - δ) (b + δ)))
    have e2 := (h3 j hj).1.mono (fun x (hx : x ∈ Ioo (a - min δ δ') (b + min δ δ')) =>
      (⟨by linarith [hx.1], by linarith [hx.2]⟩ : x ∈ Icc (a - δ') (b + δ')))
    exact e1.sub e2
  · have u1 := iterDeriv_of_within hpq1 (h1 j hj).1 (h1 j hj).2
      (show x ∈ Ioo (a - δ) (b + δ) from ⟨by linarith [hx.1], by linarith [hx.2]⟩) hi
    have u2 := iterDeriv_of_within hpq2 (h3 j hj).1 (h3 j hj).2
      (show x ∈ Ioo (a - δ') (b + δ') from ⟨by linarith [hx.1], by linarith [hx.2]⟩) hi
    have c1 : ContDiffAt ℝ (i : WithTop ℕ∞) (S j) x := u1.1.of_le (by exact_mod_cast hi)
    have c2 : ContDiffAt ℝ (i : WithTop ℕ∞) (S' j) x := u2.1.of_le (by exact_mod_cast hi)
    rw [iteratedDeriv_fun_sub c1 c2]
    exact (abs_sub _ _).trans (add_le_add u1.2 u2.2)

/-! ### Uniqueness (`ThmSmoSpec` (b)) -/

/-- **`thm:smo-spec`, uniqueness of the `S_j` on the band** (`ThmSmoSpec` (b)), from the density of the eigenvalues (`EigDensity`, L2.S5) and Step 0 (`StepZeroD0`, L2.C8):
two families `S, S'` with `SmoothExt` and `EigenRule` agree on `[X_s^-, X_s^+]`.  `0 < delta, delta'`, `X_s^- < X_s^+` and `DM F K 0` are hypotheses (findings F-S6-1..3). -/
theorem smo_unique (F : SymbolFamily Par) (K : Set Par) (M : ℕ) (hden : EigDensity F K) (hz : StepZeroD0 F K)
    (hband : ∀ μ ∈ K, F.bandLo μ < F.bandHi μ) (hK : IsCompact K) (hH : HypOn F K) (hD0 : DM F K 0)
    (S S' : ℕ → Par → ℝ → ℝ) (δ δ' Cn Cn' hM hM' C C' : ℝ) (hδ : 0 < δ) (hδ' : 0 < δ')
    (h1 : SmoothExt F K M S δ Cn) (h2 : EigenRule F K M S hM C) (h3 : SmoothExt F K M S' δ' Cn') (h4 : EigenRule F K M S' hM' C') :
    ∀ μ ∈ K, ∀ j ≤ M, ∀ X ∈ Icc (F.bandLo μ) (F.bandHi μ), S j μ X = S' j μ X := by
  classical
  obtain ⟨Cd, hd0, hdp, hdens⟩ := hden hK hH hD0
  obtain ⟨Cz, hz0, hzp, hzero⟩ := hz hK hH hD0
  obtain ⟨he0, hep, hex⟩ := exists_eig_small F K hH hD0
  obtain ⟨hMp, hrS⟩ := h2
  obtain ⟨hMp', hrS'⟩ := h4
  intro μ hμ j hj X hX
  set a := F.bandLo μ with ha
  set b := F.bandHi μ with hb
  have hab : a < b := hband μ hμ
  have hδ2 : 0 < min δ δ' := lt_min hδ hδ'
  obtain ⟨hreg, hbd⟩ := smoothExt_diff (S := fun j => S j μ) (S' := fun j => S' j μ) hδ hδ' hab (h1 μ hμ) (h3 μ hμ)
  refine sub_eq_zero.mp (unique_core a b (min δ δ') hab hδ2 M (fun j x => S j μ x - S' j μ x) hreg (Cn + Cn') hbd
    (fun N => F.step N) (fun N => FormalResearch.JB.stepSize_pos F.L_pos N) (fun ε hε => step_small F hε)
    (eigSet F μ) (C + C') (min (min hM hM') (min (min hd0 hz0) he0)) |Cz| Cd (lt_min (lt_min hMp hMp') (lt_min (lt_min hdp hzp) hep)) ?_ ?_ ?_ j hj X hX)
  · -- the rule for the difference
    intro N hN x hx
    obtain ⟨Xs, Um, hE, k, rfl⟩ := hx
    have hN1 : F.step N ≤ hM := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hN2 : F.step N ≤ hM' := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
    have r1 := hrS μ hμ N hN1 Xs Um hE k
    have r2 := hrS' μ hμ N hN2 Xs Um hE k
    have e : ∑ j ∈ range (M + 1), F.step N ^ j * (S j μ (Xs k) - S' j μ (Xs k))
        = (∑ j ∈ range (M + 1), F.step N ^ j * S j μ (Xs k) - Real.pi * F.step N * ((k : ℕ) + 1 / 2))
          - (∑ j ∈ range (M + 1), F.step N ^ j * S' j μ (Xs k) - Real.pi * F.step N * ((k : ℕ) + 1 / 2)) := by
      simp only [mul_sub, Finset.sum_sub_distrib]; ring
    rw [e]
    calc _ ≤ _ := abs_sub _ _
      _ ≤ C * F.step N ^ (M + 1) + C' * F.step N ^ (M + 1) := add_le_add r1 r2
      _ = (C + C') * F.step N ^ (M + 1) := by ring
  · -- near the band
    intro N hN x hx
    obtain ⟨Xs, Um, hE, k, rfl⟩ := hx
    have hN3 : F.step N ≤ hz0 := hN.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
    have hzz := hzero μ hμ N hN3 Xs Um hE k
    have hCz : Cz * F.step N ≤ |Cz| * F.step N :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (FormalResearch.JB.stepSize_pos F.L_pos N).le
    exact near_band hab.le (mul_nonneg (abs_nonneg _) (FormalResearch.JB.stepSize_pos F.L_pos N).le) ⟨by linarith [hzz.1], by linarith [hzz.2]⟩
  · -- density
    intro N hN Y hY
    have hN3 : F.step N ≤ hd0 := hN.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
    have hN4 : F.step N ≤ he0 := hN.trans ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨Xs, Um, hE⟩ := hex μ hμ N hN4
    obtain ⟨k, hk⟩ := hdens μ hμ N hN3 Xs Um hE Y hY
    exact ⟨Xs k, ⟨Xs, Um, hE, k, rfl⟩, hk⟩

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.smo_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.smo_unique


/-- **`thm:smo-spec`, extensions** (`ThmSmoSpec` (c)): a family `S'` with `SmoothExt` that agrees with a family `S` satisfying the rule on the band also satisfies the rule
(other constants).  From Step 0 (`StepZeroD0`) only (no density needed). -/
theorem smo_extend (F : SymbolFamily Par) (K : Set Par) (M : ℕ) (hz : StepZeroD0 F K)
    (hband : ∀ μ ∈ K, F.bandLo μ < F.bandHi μ) (hK : IsCompact K) (hH : HypOn F K) (hD0 : DM F K 0)
    (S S' : ℕ → Par → ℝ → ℝ) (δ δ' Cn Cn' hM C : ℝ) (hδ : 0 < δ) (hδ' : 0 < δ')
    (h1 : SmoothExt F K M S δ Cn) (h2 : EigenRule F K M S hM C) (h3 : SmoothExt F K M S' δ' Cn')
    (hag : ∀ μ ∈ K, ∀ j ≤ M, ∀ X ∈ Icc (F.bandLo μ) (F.bandHi μ), S' j μ X = S j μ X) :
    ∃ hM' C' : ℝ, EigenRule F K M S' hM' C' := by
  classical
  obtain ⟨Cz, hz0, hzp, hzero⟩ := hz hK hH hD0
  obtain ⟨hMp, hrS⟩ := h2
  have hδ2 : 0 < min δ δ' := lt_min hδ hδ'
  obtain ⟨CP, hCP⟩ : ∃ x : ℝ, x = |Cz| := ⟨_, rfl⟩
  have hCP0 : 0 ≤ CP := by rw [hCP]; exact abs_nonneg _
  refine ⟨min hM (min 1 (min hz0 (min δ δ' / (CP + 1)))), C + (M + 1) * ((Cn' + Cn) * CP ^ (M + 1)), lt_min hMp (lt_min one_pos
    (lt_min hzp (div_pos hδ2 (by linarith)))), ?_⟩
  intro μ hμ N hN Xs Um hE k
  set a := F.bandLo μ with ha
  set b := F.bandHi μ with hb
  have hab : a < b := hband μ hμ
  have hpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hN1 : F.step N ≤ hM := hN.trans (min_le_left _ _)
  have hN2 : F.step N ≤ 1 := hN.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hN3 : F.step N ≤ hz0 := hN.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hN4 : F.step N ≤ min δ δ' / (CP + 1) :=
    hN.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hP : CP * F.step N < min δ δ' := by
    rw [le_div_iff₀ (by linarith)] at hN4
    nlinarith
  have hzz := hzero μ hμ N hN3 Xs Um hE k
  have hCz : Cz * F.step N ≤ CP * F.step N := mul_le_mul_of_nonneg_right (by rw [hCP]; exact le_abs_self _) hpos.le
  obtain ⟨y, hy, hxy⟩ := near_band hab.le (mul_nonneg hCP0 hpos.le) (x := Xs k) (C := CP) (h := F.step N)
    ⟨by linarith [hzz.1], by linarith [hzz.2]⟩
  have hxdom : Xs k ∈ Ioo (a - min δ δ') (b + min δ δ') := by
    have := abs_le.mp hxy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  obtain ⟨hreg, hbd⟩ := smoothExt_diff (S := fun j => S' j μ) (S' := fun j => S j μ) hδ' hδ hab (h3 μ hμ) (h1 μ hμ)
  have hflat : ∀ j ≤ M, |S' j μ (Xs k) - S j μ (Xs k)| ≤ (Cn' + Cn) * (CP * F.step N) ^ (M + 1) := by
    intro j hj
    have hbd' : ∀ x ∈ Ioo (a - min δ' δ) (b + min δ' δ), |iteratedDeriv (M + 1) (fun x => S' j μ x - S j μ x) x| ≤ Cn' + Cn :=
      fun x hx => hbd j hj (M + 1) le_rfl x hx
    rw [min_comm δ' δ] at hreg hbd'
    exact flat_bound (fun x => S' j μ x - S j μ x) hab hδ2 M (hreg j hj) hbd'
      (fun x hx => by simp only [hag μ hμ j hj x hx, sub_self]) hxdom y hy hxy
  have hr := hrS μ hμ N hN1 Xs Um hE k
  have e : ∑ j ∈ range (M + 1), F.step N ^ j * S' j μ (Xs k) - Real.pi * F.step N * ((k : ℕ) + 1 / 2)
      = (∑ j ∈ range (M + 1), F.step N ^ j * S j μ (Xs k) - Real.pi * F.step N * ((k : ℕ) + 1 / 2))
        + ∑ j ∈ range (M + 1), F.step N ^ j * (S' j μ (Xs k) - S j μ (Xs k)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]; ring
  rw [e]
  have hterm : ∀ j ∈ range (M + 1), |F.step N ^ j * (S' j μ (Xs k) - S j μ (Xs k))|
      ≤ (Cn' + Cn) * CP ^ (M + 1) * F.step N ^ (M + 1) := by
    intro j hj
    have hjM : j ≤ M := by have := Finset.mem_range.mp hj; omega
    rw [abs_mul, abs_of_pos (pow_pos hpos _)]
    have h5 := hflat j hjM
    rw [mul_pow] at h5
    calc F.step N ^ j * |S' j μ (Xs k) - S j μ (Xs k)|
        ≤ 1 * ((Cn' + Cn) * (CP ^ (M + 1) * F.step N ^ (M + 1))) :=
          mul_le_mul (pow_le_one₀ hpos.le hN2) h5 (abs_nonneg _) zero_le_one
      _ = (Cn' + Cn) * CP ^ (M + 1) * F.step N ^ (M + 1) := by ring
  have hsum : |∑ j ∈ range (M + 1), F.step N ^ j * (S' j μ (Xs k) - S j μ (Xs k))|
      ≤ (M + 1) * ((Cn' + Cn) * CP ^ (M + 1)) * F.step N ^ (M + 1) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ range (M + 1), |F.step N ^ j * (S' j μ (Xs k) - S j μ (Xs k))|
        ≤ ∑ j ∈ range (M + 1), (Cn' + Cn) * CP ^ (M + 1) * F.step N ^ (M + 1) := Finset.sum_le_sum hterm
      _ = (M + 1) * ((Cn' + Cn) * CP ^ (M + 1)) * F.step N ^ (M + 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ C * F.step N ^ (M + 1) + (M + 1) * ((Cn' + Cn) * CP ^ (M + 1)) * F.step N ^ (M + 1) := add_le_add hr hsum
    _ = (C + (M + 1) * ((Cn' + Cn) * CP ^ (M + 1))) * F.step N ^ (M + 1) := by ring

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.smo_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.smo_extend

end FormalResearch.JacobiEigenvectors.TheoremA
