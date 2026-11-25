module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.EigenvalueStatements
public import FormalResearch.JacobiEigenvectors.TheoremA.StepZeroCore

/-!
# Paper J, Layer 2: Step 0, where the eigenvalues are (`StepZero`, `StepZeroD0`)

Source: Paper J `app_thmA.tex`, Section "The soft edges: proof of Proposition prop:tha-W2", *Step 0* (with `thmA.tex`, "Standing assumptions and parity freezing").  Plan item L2.C8 of `PLAN.md`.
Frozen statements: `StepZero`, `StepZeroD0` of `TheoremA/EigenvalueStatements.lean` (unchanged).  Companion modules: `StepZeroAux` (Gershgorin, real analysis), `StepZeroCore` (the analytic core),
`StepZeroCovered` (`SpectrumCovered`).

## Proved

* `stepZero : StepZero F P Kd r`: under `StdAssump F P Kd r` every eigenvalue of `J_h(p)`, `p in P`, `h <= h_0`, lies in `[X_s^-(p) - C h^2, X_s^+(p) + C h^2]`.
* `stepZeroD0 : StepZeroD0 F K`: under `(D_0)` (and (H1)--(H3), `K` compact) the same with `C h`.
* `eigen_loc` (the common core, any `e <= 2`), `coreReg_of_EK` (`e = 2`), `coreReg_of_DM` (`e = 1`, any `M`), `upHyp_of_hypOn`, `upHyp_neg_of_hypOn`, `CoreReg.neg` (gauge family `negFamily`).

Chain of lemmas: (i) `eig_gershgorin`: `|X_k - B_i| <= a_i + a_{i-1}`; (ii) `CoreReg.upper` (`StepZeroCore`): `B_n + a_n + a_{n-1} <= X_s^+ + C h^e` uniformly; (iii) the lower bound is (ii) for
`negFamily F` (diagonal `-B_n`, same bonds; `bandHi (negFamily F) = - bandLo F` by `negFamily_bandHi`, `Xsp_neg`, `Real.sSup_neg`), used with `|X_k - B_i| <= a_i + a_{i-1}`;
(iv) `coreReg_of_EK` / `coreReg_of_DM`: `|G_h - G_0|, |B_h - B_0| <= C h^2` (resp. `C h`) from the even-jet expansion (resp. `(D_0)`) and the jet bounds on the compact set (`sum_tail_bound`).

## Differences from the paper

* The upper bound uses the Gershgorin form `X <= max_n (B_n + a_n + a_{n-1})` (the quadratic-form bound of the paper, evaluated at the site of the largest eigenvector component), and the edges are handled by
  compactness (see `StepZeroCore`) instead of the explicit `O(h^2 u^{-3/2})` bound; same conclusion.
* `StepZeroD0` is proved directly (the same argument with `e = 1`), not through Weyl's inequality and `StepZero` for the samples `J^{[0]}_h`; `smo_SM` (`TruncationSM.lean`) is not needed (so its
  added hypothesis of bounded jets plays no role: the jets are bounded on the compact `P x [0,L]` by their continuity).
* (H2) and `f_+'' < 0` are not used; only `G_0 >= g_*` and uniqueness/interiority of the maximiser of `f_+` (resp. minimiser of `f_-`).

## Findings

* **F-E1 confirmed, both statements are correct as frozen** (no correction needed): `StepZero` is relative to the family's own principal symbols `G_0, B_0` (for `F = frozenFamily` at `t = h`: `O(h^2)` from the
  frozen band, `O(h)` from the plain band), and `StepZeroD0` is the `O(h)` statement for the plain band.  Applied to `frozenFamily F Kidx` on `paramSet K t0` the premise `StdAssump` is the unproved
  `FrozenStandard`; `SpectrumCovered` (`StepZeroCovered`) does not need it.

## Not formalised

Explicit constants; the consequences `a <= C h <= a_+ = 1` of Step 0 for the Weber/PC charts (they are premises `Cs0` of `PropThaW2`, L2.C7).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting
open scoped Pointwise

variable {Par : Type*} [TopologicalSpace Par]

/-! ### From the standing assumptions to the core hypotheses -/

lemma JetReg.continuousOn0 {f : Par → ℝ → ℝ} {K : Set Par} {L : ℝ} {r : ℕ} (h : JetReg f K L r) :
    ContinuousOn (fun p : Par × ℝ => f p.1 p.2) (K ×ˢ Icc 0 L) := by
  have := h.2 0 (Nat.zero_le _)
  simpa [iteratedDerivWithin_zero] using this

/-- The tail of an expansion `sum_{j <= n} h^{p_j} a_j` is `O(h^q)`: `|sum - a_0| <= (sum |M_j|) h^q` for `0 <= h <= 1`, `p_0 = 0`, `p_j >= q` for `j >= 1`. -/
lemma sum_tail_bound (n q : ℕ) (p : ℕ → ℕ) (hp0 : p 0 = 0) (hpq : ∀ j, 1 ≤ j → q ≤ p j) (a Mb : ℕ → ℝ)
    (hab : ∀ j ≤ n, |a j| ≤ Mb j) {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    |∑ j ∈ range (n + 1), h ^ p j * a j - a 0| ≤ (∑ j ∈ range n, |Mb (j + 1)|) * h ^ q := by
  rw [Finset.sum_range_succ', hp0]
  simp only [pow_zero, one_mul, add_sub_cancel_right]
  calc |∑ j ∈ range n, h ^ p (j + 1) * a (j + 1)| ≤ ∑ j ∈ range n, |h ^ p (j + 1) * a (j + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range n, h ^ q * |Mb (j + 1)| := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_of_nonneg (pow_nonneg hh0 _)]
        have h1 : h ^ p (j + 1) ≤ h ^ q := pow_le_pow_of_le_one hh0 hh1 (hpq _ (by omega))
        have h2 : |a (j + 1)| ≤ |Mb (j + 1)| := (hab (j + 1) (by have := Finset.mem_range.mp hj; omega)).trans (le_abs_self _)
        exact mul_le_mul h1 h2 (abs_nonneg _) (pow_nonneg hh0 _)
    _ = (∑ j ∈ range n, |Mb (j + 1)|) * h ^ q := by rw [← Finset.mul_sum, mul_comm]

/-- Bounds of the jets `f_j`, `j <= n`, over `P x [0,L]` (compactness), chosen as a function of `j`. -/
lemma jets_bound_choose {P : Set Par} (hP : IsCompact P) {L : ℝ} {n : ℕ} (f : ℕ → Par → ℝ → ℝ) (r : ℕ → ℕ)
    (hf : ∀ j ≤ n, JetReg (f j) P L (r j)) :
    ∃ Mb : ℕ → ℝ, ∀ j ≤ n, ∀ μ ∈ P, ∀ x ∈ Icc 0 L, |f j μ x| ≤ Mb j := by
  have : ∀ j, ∃ M : ℝ, j ≤ n → ∀ μ ∈ P, ∀ x ∈ Icc 0 L, |f j μ x| ≤ M := by
    intro j
    by_cases hj : j ≤ n
    · obtain ⟨M, hM⟩ := jet_bound hP (hf j hj) (k := 0) (Nat.zero_le _)
      exact ⟨M, fun _ μ hμ x hx => by simpa [iteratedDerivWithin_zero] using hM μ hμ x hx⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose Mb hMb using this
  exact ⟨Mb, hMb⟩

/-- Under `(E_K)` on a compact set the symbols are `O(h^2)`-close to the principal symbols (even jets only), for `h <= 1`. -/
lemma coreReg_of_EK {F : SymbolFamily Par} {P : Set Par} {Kd r : ℕ} (hP : IsCompact P) (hE : EK F P Kd r) : CoreReg F P 2 := by
  have hr : 14 ≤ r := le_trans (by unfold regBudget; omega) hE.budget
  have hreg0 := hE.reg 0 (Nat.zero_le _)
  simp only [Nat.mul_zero, Nat.sub_zero] at hreg0
  refine ⟨hP, JetReg.mono hreg0.1 (by omega), JetReg.continuousOn0 hreg0.2, ?_⟩
  obtain ⟨C, hC⟩ := hE.rem
  obtain ⟨Mg, hMg⟩ := jets_bound_choose hP (n := Kd) (fun j => F.G (2 * j)) (fun j => r - 10 * j) (fun j hj => (hE.reg j hj).1)
  obtain ⟨Mb, hMb⟩ := jets_bound_choose hP (n := Kd) (fun j => F.B (2 * j)) (fun j => r - 10 * j) (fun j hj => (hE.reg j hj).2)
  have hSG : 0 ≤ ∑ j ∈ range Kd, |Mg (j + 1)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hSB : 0 ≤ ∑ j ∈ range Kd, |Mb (j + 1)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨|C| + (∑ j ∈ range Kd, |Mg (j + 1)|) + ∑ j ∈ range Kd, |Mb (j + 1)|, fun μ hμ N hN1 s hs => ?_⟩
  have hh0 := (step_pos F N).le
  obtain ⟨hCG, hCB⟩ := hC μ hμ N s hs
  have hpow : F.step N ^ (2 * Kd + 2) ≤ F.step N ^ 2 := pow_le_pow_of_le_one hh0 hN1 (by omega)
  have hpow0 : 0 ≤ F.step N ^ 2 := by positivity
  have tG := sum_tail_bound Kd 2 (fun j => 2 * j) (by simp) (fun j hj => by show 2 ≤ 2 * j; omega) (fun j => F.G (2 * j) μ s) Mg
    (fun j hj => hMg j hj μ hμ s hs) hh0 hN1
  have tB := sum_tail_bound Kd 2 (fun j => 2 * j) (by simp) (fun j hj => by show 2 ≤ 2 * j; omega) (fun j => F.B (2 * j) μ s) Mb
    (fun j hj => hMb j hj μ hμ s hs) hh0 hN1
  simp only [Nat.mul_zero] at tG tB
  have c1 : C * F.step N ^ (2 * Kd + 2) ≤ |C| * F.step N ^ 2 :=
    mul_le_mul (le_abs_self C) hpow (by positivity) (abs_nonneg C)
  have hSGB := mul_nonneg hSB hpow0
  have hSGG := mul_nonneg hSG hpow0
  constructor
  · have := abs_sub_le (F.Gh μ (F.step N) s) (∑ j ∈ range (Kd + 1), F.step N ^ (2 * j) * F.G (2 * j) μ s) (F.G 0 μ s)
    linarith
  · have := abs_sub_le (F.Bh μ (F.step N) s) (∑ j ∈ range (Kd + 1), F.step N ^ (2 * j) * F.B (2 * j) μ s) (F.B 0 μ s)
    linarith

/-- Under `(D_M)` on a compact set the symbols are `O(h)`-close to the principal symbols, for `h <= 1`. -/
lemma coreReg_of_DM {F : SymbolFamily Par} {K : Set Par} {M : ℕ} (hK : IsCompact K) (hD : DM F K M) : CoreReg F K 1 := by
  have hreg0 := hD.reg 0 (Nat.zero_le _)
  simp only [Nat.zero_div, Nat.mul_zero, Nat.sub_zero] at hreg0
  have hr : 2 ≤ regBudget M := by unfold regBudget; omega
  refine ⟨hK, JetReg.mono hreg0.1 hr, JetReg.continuousOn0 hreg0.2, ?_⟩
  obtain ⟨C, hC⟩ := hD.rem
  obtain ⟨Mg, hMg⟩ := jets_bound_choose hK (n := M) (fun j => F.G j) (fun j => regBudget M - 10 * (j / 2)) (fun j hj => (hD.reg j hj).1)
  obtain ⟨Mb, hMb⟩ := jets_bound_choose hK (n := M) (fun j => F.B j) (fun j => regBudget M - 10 * (j / 2)) (fun j hj => (hD.reg j hj).2)
  have hSG : 0 ≤ ∑ j ∈ range M, |Mg (j + 1)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hSB : 0 ≤ ∑ j ∈ range M, |Mb (j + 1)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨|C| + (∑ j ∈ range M, |Mg (j + 1)|) + ∑ j ∈ range M, |Mb (j + 1)|, fun μ hμ N hN1 s hs => ?_⟩
  have hh0 := (step_pos F N).le
  obtain ⟨hCG, hCB⟩ := hC μ hμ N s hs
  have hpow : F.step N ^ (M + 1) ≤ F.step N ^ 1 := pow_le_pow_of_le_one hh0 hN1 (by omega)
  have hpow0 : 0 ≤ F.step N ^ 1 := by positivity
  have tG := sum_tail_bound M 1 (fun j => j) (by simp) (fun j hj => hj) (fun j => F.G j μ s) Mg
    (fun j hj => hMg j hj μ hμ s hs) hh0 hN1
  have tB := sum_tail_bound M 1 (fun j => j) (by simp) (fun j hj => hj) (fun j => F.B j μ s) Mb
    (fun j hj => hMb j hj μ hμ s hs) hh0 hN1
  have c1 : C * F.step N ^ (M + 1) ≤ |C| * F.step N ^ 1 :=
    mul_le_mul (le_abs_self C) hpow (by positivity) (abs_nonneg C)
  have hSGB := mul_nonneg hSB hpow0
  have hSGG := mul_nonneg hSG hpow0
  constructor
  · have := abs_sub_le (F.Gh μ (F.step N) s) (∑ j ∈ range (M + 1), F.step N ^ j * F.G j μ s) (F.G 0 μ s)
    linarith
  · have := abs_sub_le (F.Bh μ (F.step N) s) (∑ j ∈ range (M + 1), F.step N ^ j * F.B j μ s) (F.B 0 μ s)
    linarith

/-! ### The gauge family and the lower bound -/

omit [TopologicalSpace Par] in
lemma fPlus_neg (L : ℝ) (G0 B0 : ℝ → ℝ) (u : ℝ) : fPlus L G0 (fun s => -B0 s) u = -fMinus L G0 B0 u := by
  unfold fPlus fMinus; ring

lemma Xsp_neg (L : ℝ) (G0 B0 : ℝ → ℝ) : Xsp L G0 (fun s => -B0 s) = -Xsm L G0 B0 := by
  unfold Xsp Xsm
  have : fPlus L G0 (fun s => -B0 s) '' Icc 0 L = -(fMinus L G0 B0 '' Icc 0 L) := by
    ext y
    simp only [Set.mem_image, Set.mem_neg, fPlus_neg]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, by ring⟩
    · rintro ⟨u, hu, h⟩; exact ⟨u, hu, by linarith⟩
  rw [this, Real.sSup_neg]

omit [TopologicalSpace Par] in
lemma negFamily_bandHi (F : SymbolFamily Par) (μ : Par) : (negFamily F).bandHi μ = -F.bandLo μ := by
  unfold SymbolFamily.bandHi SymbolFamily.bandLo
  exact Xsp_neg F.L (F.G 0 μ) (F.B 0 μ)

omit [TopologicalSpace Par] in
lemma negFamily_entryB (F : SymbolFamily Par) (μ : Par) (N : ℕ) (n : ℤ) : (negFamily F).entryB μ N n = -F.entryB μ N n := by
  rfl

lemma CoreReg.neg {F : SymbolFamily Par} {P : Set Par} {e : ℕ} (hR : CoreReg F P e) : CoreReg (negFamily F) P e := by
  obtain ⟨C0, hC0⟩ := hR.rem
  refine ⟨hR.compact, hR.regG, hR.regB.neg, C0, fun μ hμ N hN1 s hs => ?_⟩
  obtain ⟨a, b⟩ := hC0 μ hμ N hN1 s hs
  refine ⟨a, ?_⟩
  have : |-F.Bh μ (F.step N) s - -F.B 0 μ s| = |F.Bh μ (F.step N) s - F.B 0 μ s| := by
    rw [← abs_neg]; ring_nf
  show |-F.Bh μ (F.step N) s - -F.B 0 μ s| ≤ _
  rw [this]; exact b

omit [TopologicalSpace Par] in
lemma upHyp_of_hypOn {F : SymbolFamily Par} {P : Set Par} (h : HypOn F P) : UpHyp F P := by
  obtain ⟨g, hg⟩ := h
  rcases P.eq_empty_or_nonempty with hP | ⟨μ0, hμ0⟩
  · exact ⟨1, one_pos, fun μ hμ => by simp [hP] at hμ⟩
  · refine ⟨g, (hg μ0 hμ0).gstar_pos, fun μ hμ => ⟨(hg μ hμ).G0_lb, ?_⟩⟩
    obtain ⟨uc, h1, h2, h3, -⟩ := (hg μ hμ).H3p
    exact ⟨uc, h1, h2, h3⟩

omit [TopologicalSpace Par] in
lemma upHyp_neg_of_hypOn {F : SymbolFamily Par} {P : Set Par} (h : HypOn F P) : UpHyp (negFamily F) P := by
  obtain ⟨g, hg⟩ := h
  rcases P.eq_empty_or_nonempty with hP | ⟨μ0, hμ0⟩
  · exact ⟨1, one_pos, fun μ hμ => by simp [hP] at hμ⟩
  · refine ⟨g, (hg μ0 hμ0).gstar_pos, fun μ hμ => ⟨(hg μ hμ).G0_lb, ?_⟩⟩
    obtain ⟨uc, h1, h2, h3, -⟩ := (hg μ hμ).H3m
    refine ⟨uc, h1, h2, fun u hu => ?_⟩
    have e1 : fPlus (negFamily F).L ((negFamily F).G 0 μ) ((negFamily F).B 0 μ) u = -fMinus F.L (F.G 0 μ) (F.B 0 μ) u :=
      fPlus_neg F.L (F.G 0 μ) (F.B 0 μ) u
    rw [e1, negFamily_bandHi, neg_inj]
    exact h3 u hu

/-- **Eigenvalue location from the core bounds**: every eigenvalue lies within `C h^e` of the band `[X_s^-, X_s^+]` (Gershgorin bound + `CoreReg.upper` for `F` and the gauge family). -/
theorem eigen_loc {F : SymbolFamily Par} {P : Set Par} {e : ℕ} (hR : CoreReg F P e) (he : e ≤ 2) (hU : UpHyp F P)
    (hU' : UpHyp (negFamily F) P) :
    ∃ C h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ P, ∀ N : ℕ, F.step N ≤ h0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1), F.bandLo μ - C * F.step N ^ e ≤ X k ∧ X k ≤ F.bandHi μ + C * F.step N ^ e := by
  obtain ⟨C1, h1, hh1, H1⟩ := hR.upper he hU
  obtain ⟨C2, h2, hh2, H2⟩ := hR.neg.upper he hU'
  refine ⟨max C1 C2, min h1 h2, lt_min hh1 hh2, fun μ hμ N hN X Um hE k => ?_⟩
  have hpow := pow_nonneg (step_pos F N).le e
  obtain ⟨i, hi⟩ := eig_gershgorin F μ N hE k
  have hu := H1 μ hμ N (hN.trans (min_le_left _ _)) i
  have hl := H2 μ hμ N (hN.trans (min_le_right _ _)) i
  rw [negFamily_entryB, negFamily_bandHi] at hl
  have hl' : -F.entryB μ N (i : ℤ) + F.bondA μ N (i : ℤ) + F.bondA μ N ((i : ℤ) - 1) ≤ -F.bandLo μ + C2 * F.step N ^ e := hl
  have c1 : C1 * F.step N ^ e ≤ max C1 C2 * F.step N ^ e := mul_le_mul_of_nonneg_right (le_max_left _ _) hpow
  have c2 : C2 * F.step N ^ e ≤ max C1 C2 * F.step N ^ e := mul_le_mul_of_nonneg_right (le_max_right _ _) hpow
  rw [abs_le] at hi
  constructor <;> linarith [hi.1, hi.2]

/-- **Step 0** (app_thmA, Step 0; frozen statement `StepZero`): under the standing assumptions every eigenvalue of `J_h(p)` lies in `[X_s^- - C h^2, X_s^+ + C h^2]`. -/
theorem stepZero (F : SymbolFamily Par) (P : Set Par) (Kd r : ℕ) : StepZero F P Kd r := by
  rintro ⟨hP, hE, hH⟩
  exact eigen_loc (coreReg_of_EK hP hE) le_rfl (upHyp_of_hypOn hH) (upHyp_neg_of_hypOn hH)

/-- **Step 0 under `(D_0)` only** (frozen statement `StepZeroD0`): the eigenvalues lie within `C h` of the band of the principal symbols. -/
theorem stepZeroD0 (F : SymbolFamily Par) (K : Set Par) : StepZeroD0 F K := by
  intro hK hH hD
  obtain ⟨C, h0, hh0, H⟩ := eigen_loc (coreReg_of_DM hK hD) (by norm_num) (upHyp_of_hypOn hH) (upHyp_neg_of_hypOn hH)
  exact ⟨C, h0, hh0, fun μ hμ N hN X Um hE k => by simpa using H μ hμ N hN X Um hE k⟩

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.stepZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.stepZero

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.stepZeroD0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.stepZeroD0

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.eigen_loc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.eigen_loc

end FormalResearch.JacobiEigenvectors.TheoremA
