module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.BulkWeber
public import FormalResearch.JacobiEigenvectors.TheoremA.Statements
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkConj1

/-!
# Paper J, Layer 2: the bulk phase at an eigenvalue (L2.S2; the bulk part of L2.S1)

Source: Paper J `app_thmA.tex`, `lem:smo-bulkphase` (4) (the Casoratian of the two edge sequences is a positive factor times
`sin(Sigma/h - pi/2) + O(h^m)`), `thm:smo-BSr`, proof, paragraph "Bulk phases" ("at an eigenvalue the Casoratian vanishes, so
`|sin(Sigma/h - pi/2)| <= C h^m` and `Sigma(X_k(t), t, h) = pi h (k' + 1/2) + O(h^{M+1})` for an integer `k'`; ... the labels give `k' = k`").

## Proved here (all axiom-pinned)

* `exists_int_near`: `|sin y| <= eps` gives an integer `j` with `|y - pi j| <= (pi/2) eps` (Jordan's inequality).
* `cas_hat_bound`: pure algebra, a Casoratian of exact sequences that vanishes differs from that of their comparison sequences by
  `O(e_f B_g + B_f e_g + e_f e_g)`.
* `chart_overlap_row`: on a row of the oscillatory overlap, `|psi-hat_j| <= K C_M h^{1/4}` and `E_Web M_Web <= C_M h^{1/4}`
  (from `W_osc`, `M_osc`, `ladder_phi_bound`).
* `bulk_eigen_sin` (**L2.S2, first half**): for an eigenvalue `X_k(t)` of the frozen matrix at `(mu, t)` lying in the energy range of a
  bulk block, `|sin(Sigma(X_k, t, h)/h - pi/2)| <= C h^{max M 1}`, uniformly in `mu in K`, `|t| <= t0`.  Proof: the eigenvector, rescaled,
  is the exact left solution on the left chart rows (seed `psi-hat^L_0`) and (reflected, rescaled) the exact right solution
  (this uses `Psi_N != 0`, from positive bonds); `bulkSolutionBound_of_one_le` (L2.C1) compares both with the comparison sequences on one
  overlap pair; the exact Casoratian vanishes; the frozen field `casoratian` of `BulkPhaseInputs` gives the sine.
* `bulk_eigen_quant` (**L2.S2, second half**): the quantisation `Sigma(X_k, t, h) = pi h (j + 1/2) + O(h^{max M 1 + 1})` with an integer `j`.
* `bulk_BSr2` (**eq:smo-BSr2 on a bulk block**): `j = k` and `|Sigma(X_k, t, h) - pi h (k + 1/2)| <= C h^{M+1}`, from the windows statement
  `BulkWindowLabels` (`lem:smo-bulkphase` (3), proved by L2.S1 (3), *not* here) and the bound `bulkSigmaBdd` (from the field `Sigma_bdd`).

## Differences from the paper and findings (round 5: both of agent M's proposed corrections confirmed and applied to the structure `BulkPhaseInputs`, `Charts/BulkWeber.lean`)

* **F-S2-1 (prefactor lower bound): CONFIRMED, applied.**  The frozen field had `exists pre, 0 < pre /\ ...`, no size for `pre`.  Without a lower bound the field does not imply
  that the exact Casoratian (which vanishes at an eigenvalue) forces the sine to be small: the comparison Casoratian is `O(h^m)` times the product of two envelopes `<= C h^{1/4}`,
  so `pre` must be `>= c0 h^{1/2}`.  The paper has this: `pre = a_n w_n e^{Re c/h}` with `w_n ~ |chi_n|^2`, `|chi_L chi_R| = e^{Re c/h} |chi_L|^2 ~ h^{1/2}` (the Weber branch has amplitude
  `h^{1/4}`; `lem:smo-bulkphase` (2), (4); `M_osc`), and `a_n >= c > 0` on the overlap (H1).  The field is now `exists Ccas c0 N0, 0 < c0 /\ forall .., exists pre, c0 * sqrt h <= pre /\ forall n, ...`;
  the auxiliary Prop `BulkCasPre` is deleted and `bulk_eigen_sin`, `bulk_eigen_quant`, `bulk_BSr2` use `PI.casoratian` directly.
* **F-S2-2 (uniform bound of the phase coefficients): CONFIRMED (not derivable), applied as the field `BulkPhaseInputs.Sigma_bdd`.**  `Sigma_reg` (`JetRegJ`) is pointwise in `mu in K` and no
  continuity in `mu` is part of the structure, so compactness gives a bound for each `mu` but not uniform in `mu`; the paper's uniformity ("`C^{M+1}` norms bounded uniformly in `mu`", chart norms
  uniform on a localising neighbourhood, finitely many cover `K`) is therefore a field: `exists C, forall mu in K, j <= M, i <= 2M+1, p in J x [-t0,t0], ||iteratedFDerivWithin R i (Sigma mu j) (J x [-t0,t0]) p|| <= C`.
  `bulkSigmaBdd` (here) is its `i = 0` part (`|Sigma_j| <= C`); `taylor_bound_of_Sigma_bdd` (`SpectrumTaylor.lean`) is the `t`-derivative bound `hC` of `phase_substitution`.
* **Positive bonds.**  `bulk_eigen_sin` takes `0 < a_n` (`0 <= n < N`) for the frozen matrix as a hypothesis (it gives `Psi_N != 0`); the paper has it from (H1) and `(D_M)` for
  `h <= h_0`; `PropThaCount` takes the same hypothesis (F-A7).
* The energy `X_k` is assumed in `[Jlo, Jhi]`, the energy range of the block; the cover and Step 0 (the eigenvalues lie in some block or soft window) are in L2.C8/L2.S6.

## Not formalised

`lem:smo-bulkphase` (1)--(3) (the trigonometric phases from DLMF 12.10.18 and the windows/labels via `PropThaCount`), (4) itself (it is the *field* `BulkPhaseInputs`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.Engine

/-! ### Pure real-analysis helpers -/

/-- If `|sin y| <= eps` then `y` is within `(pi/2) eps` of `pi * j` for an integer `j`. -/
lemma exists_int_near (y ε : ℝ) (h : |Real.sin y| ≤ ε) : ∃ j : ℤ, |y - Real.pi * j| ≤ Real.pi / 2 * ε := by
  refine ⟨round (y / Real.pi), ?_⟩
  set j := round (y / Real.pi) with hj
  have hpi := Real.pi_pos
  have h1 : |y / Real.pi - (j : ℝ)| ≤ 1 / 2 := abs_sub_round (y / Real.pi)
  set z := y - Real.pi * j with hz
  have hzr : z = Real.pi * (y / Real.pi - j) := by rw [hz]; field_simp
  have hzb : |z| ≤ Real.pi / 2 := by
    rw [hzr, abs_mul, abs_of_pos hpi]
    nlinarith
  have hsin : |Real.sin z| = |Real.sin y| := by
    have : Real.sin y = Real.sin (z + j * Real.pi) := by
      congr 1; rw [hz]; ring
    rw [this, Real.sin_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  have hjord : 2 / Real.pi * |z| ≤ |Real.sin z| := by
    have hb := abs_le.mp hzb
    rcases le_total 0 z with hz0 | hz0
    · have hs0 : 0 ≤ Real.sin z := Real.sin_nonneg_of_nonneg_of_le_pi hz0 (by linarith [hb.2])
      rw [abs_of_nonneg hz0, abs_of_nonneg hs0]
      exact Real.mul_le_sin hz0 hb.2
    · have hs0 : 0 ≤ Real.sin (-z) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hb.1])
      have h2 : 2 / Real.pi * (-z) ≤ Real.sin (-z) := Real.mul_le_sin (by linarith) (by linarith [hb.1])
      rw [Real.sin_neg] at hs0 h2
      rw [abs_of_nonpos hz0, abs_of_nonpos (by linarith)]
      linarith
  have h4 : |z| ≤ Real.pi / 2 * |Real.sin z| := by
    have h5 : |z| = Real.pi / 2 * (2 / Real.pi * |z|) := by field_simp
    calc |z| = Real.pi / 2 * (2 / Real.pi * |z|) := h5
      _ ≤ Real.pi / 2 * |Real.sin z| := mul_le_mul_of_nonneg_left hjord (by positivity)
  calc |y - Real.pi * j| = |z| := rfl
    _ ≤ Real.pi / 2 * |Real.sin z| := h4
    _ ≤ Real.pi / 2 * ε := by rw [hsin]; exact mul_le_mul_of_nonneg_left h (by positivity)

/-- **Casoratian of the comparison sequences from a vanishing exact Casoratian.**  If `f1 g1 - f2 g2 = 0` for the exact sequences, `f, g` are within
`ef, eg` of the comparison values `F, G`, and these are bounded by `BF, BG`, then
`|a (F1 G1 - F2 G2)| <= CA * 2 (ef BG + BF eg + ef eg)` for `|a| <= CA`. -/
lemma cas_hat_bound (a F1 F2 G1 G2 f1 f2 g1 g2 CA ef eg BF BG : ℝ)
    (hCA : |a| ≤ CA) (hex : f1 * g1 - f2 * g2 = 0)
    (hf1 : |f1 - F1| ≤ ef) (hf2 : |f2 - F2| ≤ ef) (hg1 : |g1 - G1| ≤ eg) (hg2 : |g2 - G2| ≤ eg)
    (hF1 : |F1| ≤ BF) (hF2 : |F2| ≤ BF) (hG1 : |G1| ≤ BG) (hG2 : |G2| ≤ BG)
    (hef : 0 ≤ ef) (heg : 0 ≤ eg) (hBF : 0 ≤ BF) (hBG : 0 ≤ BG) :
    |a * (F1 * G1 - F2 * G2)| ≤ CA * (2 * (ef * BG + BF * eg + ef * eg)) := by
  have key : ∀ f F g G : ℝ, |f - F| ≤ ef → |g - G| ≤ eg → |F| ≤ BF → |G| ≤ BG →
      |F * G - f * g| ≤ ef * BG + BF * eg + ef * eg := by
    intro f F g G hf hg hF hG
    have e : F * G - f * g = (F - f) * G + f * (G - g) := by ring
    have hfF : |f| ≤ BF + ef := by
      have := abs_sub_abs_le_abs_sub f F
      have h2 := abs_sub_comm f F
      linarith
    rw [e]
    calc |(F - f) * G + f * (G - g)| ≤ |(F - f) * G| + |f * (G - g)| := abs_add_le _ _
      _ = |F - f| * |G| + |f| * |G - g| := by rw [abs_mul, abs_mul]
      _ ≤ ef * BG + (BF + ef) * eg := by
          apply add_le_add
          · exact mul_le_mul (by rw [abs_sub_comm]; exact hf) hG (abs_nonneg _) hef
          · exact mul_le_mul hfF (by rw [abs_sub_comm]; exact hg) (abs_nonneg _) (by linarith)
      _ = ef * BG + BF * eg + ef * eg := by ring
  have e : F1 * G1 - F2 * G2 = (F1 * G1 - f1 * g1) - (F2 * G2 - f2 * g2) := by linarith
  have h1 := key f1 F1 g1 G1 hf1 hg1 hF1 hG1
  have h2 := key f2 F2 g2 G2 hf2 hg2 hF2 hG2
  have hCA0 : 0 ≤ CA := (abs_nonneg _).trans hCA
  rw [abs_mul]
  calc |a| * |F1 * G1 - F2 * G2| ≤ CA * (2 * (ef * BG + BF * eg + ef * eg)) := by
        apply mul_le_mul hCA _ (abs_nonneg _) hCA0
        rw [e]
        calc |(F1 * G1 - f1 * g1) - (F2 * G2 - f2 * g2)|
            ≤ |F1 * G1 - f1 * g1| + |F2 * G2 - f2 * g2| := abs_sub _ _
          _ ≤ 2 * (ef * BG + BF * eg + ef * eg) := by linarith

/-- **Numerical form of the Casoratian bound**: with `ef = A1 h^m q`, `eg = A2 h^m q`, `BF = B1 q`, `BG = B2 q` (`q^2 = sqrt h`), `0 <= h^m <= 1`:
`|a (F1 G1 - F2 G2)| <= CA * (Cx h^m q^2)` with `Cx = 2 (A1 B2 + B1 A2 + A1 A2)`. -/
lemma hat_cas_numeric (a F1 F2 G1 G2 f1 f2 g1 g2 CA q hm A1 A2 B1 B2 : ℝ)
    (hCA : |a| ≤ CA) (hex : f1 * g1 - f2 * g2 = 0)
    (hf1 : |f1 - F1| ≤ A1 * hm * q) (hf2 : |f2 - F2| ≤ A1 * hm * q)
    (hg1 : |g1 - G1| ≤ A2 * hm * q) (hg2 : |g2 - G2| ≤ A2 * hm * q)
    (hF1 : |F1| ≤ B1 * q) (hF2 : |F2| ≤ B1 * q) (hG1 : |G1| ≤ B2 * q) (hG2 : |G2| ≤ B2 * q)
    (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (hq : 0 ≤ q) (hm0 : 0 ≤ hm) (hm1 : hm ≤ 1) :
    |a * (F1 * G1 - F2 * G2)| ≤ CA * ((2 * (A1 * B2 + B1 * A2 + A1 * A2)) * hm * q ^ 2) := by
  have h := cas_hat_bound a F1 F2 G1 G2 f1 f2 g1 g2 CA (A1 * hm * q) (A2 * hm * q) (B1 * q) (B2 * q) hCA hex
    hf1 hf2 hg1 hg2 hF1 hF2 hG1 hG2 (by positivity) (by positivity) (by positivity) (by positivity)
  have hCA0 : 0 ≤ CA := (abs_nonneg _).trans hCA
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hCA0)
  have h4 : 0 ≤ A1 * A2 * q ^ 2 * (hm - hm * hm) :=
    mul_nonneg (mul_nonneg (mul_nonneg hA1 hA2) (sq_nonneg _)) (by nlinarith)
  nlinarith [h4]

/-- **From the Casoratian to the sine** (pure algebra): `|Chat| <= CA Cx h^m s` and `|Chat - pre sin| <= Ccas h^m pre`, `pre >= c0 s`, `s > 0`
give `|sin| <= (CA Cx / c0 + |Ccas|) h^m`. -/
lemma sin_from_cas (Chat pre sn c0 Ccas CA Cx hm sq : ℝ) (hc0 : 0 < c0) (hsq : 0 < sq) (hpre : c0 * sq ≤ pre)
    (hm0 : 0 ≤ hm) (hCA : 0 ≤ CA) (hCx : 0 ≤ Cx) (hCh : |Chat| ≤ CA * (Cx * hm * sq))
    (hfield : |Chat - pre * sn| ≤ Ccas * hm * pre) : |sn| ≤ (CA * Cx / c0 + |Ccas|) * hm := by
  have hprepos : 0 < pre := lt_of_lt_of_le (mul_pos hc0 hsq) hpre
  have hsq_le : sq ≤ pre / c0 := by rw [le_div_iff₀ hc0]; linarith
  have h1 : pre * |sn| = |pre * sn| := by rw [abs_mul, abs_of_pos hprepos]
  have hfield' : |Chat - pre * sn| ≤ |Ccas| * hm * pre :=
    hfield.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hm0) hprepos.le)
  have h2 : |pre * sn| ≤ |Chat| + |Chat - pre * sn| := by
    have := abs_sub_abs_le_abs_sub (pre * sn) Chat
    rw [abs_sub_comm] at this
    linarith
  have h3 : CA * (Cx * hm * sq) ≤ CA * Cx / c0 * hm * pre := by
    have : CA * Cx * hm * sq ≤ CA * Cx * hm * (pre / c0) :=
      mul_le_mul_of_nonneg_left hsq_le (mul_nonneg (mul_nonneg hCA hCx) hm0)
    calc CA * (Cx * hm * sq) = CA * Cx * hm * sq := by ring
      _ ≤ CA * Cx * hm * (pre / c0) := this
      _ = CA * Cx / c0 * hm * pre := by ring
  have hmain : pre * |sn| ≤ (CA * Cx / c0 + |Ccas|) * hm * pre := by
    rw [h1]
    nlinarith [h2, hCh, h3, hfield']
  by_contra hcon
  rw [not_le] at hcon
  have := mul_lt_mul_of_pos_left hcon hprepos
  nlinarith [hmain, this]

/-! ### Chart facts on an overlap row -/

/-- **Overlap row bounds**: on a chart row `j` with `c' <= u_j` (`0 <= j <= N_R`): `W = 1`, `|psi-hat_j| <= K C_M h^{1/4}`, `E_Web M_Web <= C_M h^{1/4}`
(`K = (K_A + K_B) K_w`). -/
lemma chart_overlap_row {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (p : Par × ℝ) (hp : p ∈ P)
    (X : ℝ) (hX : X ∈ Set.Icc Jlo Jhi) (N : ℕ) (hN : C.N0 ≤ N) (j : ℤ) (hj0 : 0 ≤ j)
    (hjN : j ≤ (C.chain p X N).NR) (hov : C.c' ≤ uNode (G.step N) j) :
    |C.psiHatL p X N j| ≤ (C.cs.KA + C.cs.KB) * C.cs.Kw * (C.CM * G.step N ^ ((1 : ℝ) / 4)) ∧
      C.envL p X N j ≤ C.CM * G.step N ^ ((1 : ℝ) / 4) := by
  have hV := C.valid p hp X hX N hN
  obtain ⟨hP1, -, -, -, -⟩ := C.shape p hp X hX N hN
  have hjm : j ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR := Finset.mem_Icc.mpr ⟨hj0, hjN⟩
  have hW := C.W_osc p hp X hX N hN j hjm hov
  have hM := (C.M_osc p hp X hX N hN j hjm hov).2
  have hb := (ladder_phi_bound (C.chain p X N) C.cs (G.step N) m hV hP1 j hj0 hjN).1
  rw [hW, mul_one] at hb
  have hK : 0 ≤ (C.cs.KA + C.cs.KB) * C.cs.Kw :=
    mul_nonneg (add_nonneg C.cs.KA_nonneg C.cs.KB_nonneg) C.cs.Kw_nonneg
  refine ⟨?_, ?_⟩
  · rw [show C.psiHatL p X N j = (C.chain p X N).phi (G.step N) 0 1 j from psiHat_one_eq _ _ _]
    exact hb.trans (mul_le_mul_of_nonneg_left hM hK)
  · unfold BulkWeberChart.envL
    rw [hW, one_mul]
    exact hM

/-! ### The corrected Casoratian field -/

section Phase

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {K : Set Par} {t0 : ℝ}
  {Jlo Jhi : ℝ} {M : ℕ} {U V : ℝ → ℝ → ℝ}
  {CL : BulkWeberChart F P Jlo Jhi (max M 1) U V} {CR : BulkWeberChart (mirrorFamily F) P Jlo Jhi (max M 1) U V}

/-- The phase `Sigma(X, t, h) = sum_{j <= M} h^j Sigma_j(X, t)` of `lem:smo-bulkphase` (4) at the step `h = F.step N`. -/
def bulkPhaseSum (PI : BulkPhaseInputs F P K t0 Jlo Jhi M U V CL CR) (μ : Par) (t X : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ range (M + 1), F.step N ^ j * PI.Sigma μ j X t

/-- **L2.S2 (first half): at an eigenvalue the sine of the phase is `O(h^m)`.**  `m = max M 1`. -/
theorem bulk_eigen_sin (PI : BulkPhaseInputs F P K t0 Jlo Jhi M U V CL CR)
    (hP : ∀ μ ∈ K, ∀ t ∈ Set.Icc (-t0) t0, (μ, t) ∈ P)
    (hcoup : CR.c = F.L - CL.c' ∧ CR.c' = F.L - CL.c) (r : ℕ) (hr : StdAssump F P (max M 1 / 2) r) :
    ∃ Cs h0 : ℝ, 0 < h0 ∧ ∃ N1 : ℕ, ∀ μ ∈ K, ∀ t ∈ Set.Icc (-t0) t0, ∀ N : ℕ, N1 ≤ N → F.step N ≤ h0 →
      (∀ n : ℤ, 0 ≤ n → n < N → 0 < F.bondA (μ, t) N n) →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
        IsEigenSystem (F.jacobiMat (μ, t) N) Xs Um → ∀ k : Fin (N + 1), Xs k ∈ Set.Icc Jlo Jhi →
          |Real.sin (bulkPhaseSum PI μ t (Xs k) N / F.step N - Real.pi / 2)| ≤ Cs * F.step N ^ (max M 1) := by
  classical
  obtain ⟨Ccas, c0, N0r, hc0, hpre⟩ := PI.casoratian
  obtain ⟨hPc, hEK, -⟩ := hr
  obtain ⟨CA, hCA0, hCA⟩ := bondA_bound_of_EK F P (max M 1 / 2) r hPc hEK
  have hm1 : 1 ≤ max M 1 := le_max_right _ _
  obtain ⟨CcL, h0L, hh0L, hBL⟩ := bulkSolutionBound_of_one_le CL hm1
  obtain ⟨CcR, h0R, hh0R, hBR⟩ := bulkSolutionBound_of_one_le CR hm1
  obtain ⟨hc'L, hc'cL, hσL, hcσL, -, hcML, hcMCML, hc3L, hCsumL, -⟩ := CL.consts_pos
  obtain ⟨hc'R, hc'cR, hσR, hcσR, -, hcMR, hcMCMR, hc3R, hCsumR, -⟩ := CR.consts_pos
  have hKL : 0 ≤ (CL.cs.KA + CL.cs.KB) * CL.cs.Kw :=
    mul_nonneg (add_nonneg CL.cs.KA_nonneg CL.cs.KB_nonneg) CL.cs.Kw_nonneg
  have hKR : 0 ≤ (CR.cs.KA + CR.cs.KB) * CR.cs.Kw :=
    mul_nonneg (add_nonneg CR.cs.KA_nonneg CR.cs.KB_nonneg) CR.cs.Kw_nonneg
  -- constants
  obtain ⟨A1, hA1⟩ : ∃ x : ℝ, x = |CcL| * CL.CM := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ x : ℝ, x = |CcR| * CR.CM := ⟨_, rfl⟩
  obtain ⟨B1, hB1⟩ : ∃ x : ℝ, x = (CL.cs.KA + CL.cs.KB) * CL.cs.Kw * CL.CM := ⟨_, rfl⟩
  obtain ⟨B2, hB2⟩ : ∃ x : ℝ, x = (CR.cs.KA + CR.cs.KB) * CR.cs.Kw * CR.CM := ⟨_, rfl⟩
  have hA1n : 0 ≤ A1 := by rw [hA1]; exact mul_nonneg (abs_nonneg _) (by linarith)
  have hA2n : 0 ≤ A2 := by rw [hA2]; exact mul_nonneg (abs_nonneg _) (by linarith)
  have hB1n : 0 ≤ B1 := by rw [hB1]; exact mul_nonneg hKL (by linarith)
  have hB2n : 0 ≤ B2 := by rw [hB2]; exact mul_nonneg hKR (by linarith)
  obtain ⟨Cx, hCx⟩ : ∃ x : ℝ, x = 2 * (A1 * B2 + B1 * A2 + A1 * A2) := ⟨_, rfl⟩
  have hCxn : 0 ≤ Cx := by rw [hCx]; positivity
  refine ⟨CA * Cx / c0 + |Ccas|, min (min (min 1 h0L) h0R) (min ((CL.c - CL.c') / 6) CL.σ), ?_,
    max (max CL.N0 CR.N0) ⌈N0r⌉₊, ?_⟩
  · refine lt_min (lt_min (lt_min one_pos hh0L) hh0R) (lt_min (by linarith) hσL)
  intro μ hμ t ht N hN hstep hpos Xs Um hE k hXk
  have hp : (μ, t) ∈ P := hP μ hμ t ht
  have hN1 : CL.N0 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : CR.N0 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN0r : N0r ≤ N := le_trans (Nat.le_ceil N0r) (by exact_mod_cast le_trans (le_max_right _ _) hN)
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hstepR : (mirrorFamily F).step N = F.step N := rfl
  have hh1 : F.step N ≤ 1 := hstep.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hhL : F.step N ≤ h0L := hstep.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hhR : F.step N ≤ h0R := hstep.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hhd : F.step N ≤ (CL.c - CL.c') / 6 := hstep.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhσ : F.step N ≤ CL.σ := hstep.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hLs : F.step N * ((N : ℝ) + 1) = F.L := step_mul_succ F N
  set X := Xs k with hX
  have hXk' : X ∈ Set.Icc Jlo Jhi := hXk
  obtain ⟨hJ0, hψ0, hψn⟩ := eigen_col_facts F (μ, t) N Xs Um hE k
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℤ → ℝ, ψ = eigVec Um k := ⟨_, rfl⟩
  rw [← hψ] at hJ0 hψ0 hψn
  have hJm : JacSol (mirrorFamily F) (μ, t) N X ((N : ℤ) + 1) (fun i => ψ ((N : ℤ) - i)) := by
    intro n hn0 hnN
    exact lop_mirror F (μ, t) N X ψ (fun j h0 h1 => hJ0 j h0 h1) n hn0 hnN
  have hℓ0 : 0 < CL.psiHatL (μ, t) X N 0 := by
    rw [show CL.psiHatL (μ, t) X N 0 = (CL.chain (μ, t) X N).phi (F.step N) 0 1 0 from
      psiHat_one_eq (CL.chain (μ, t) X N) (F.step N) 0]
    exact CL.seed_pos _ hp X hXk' N hN1
  have hr0 : 0 < CR.psiHatL (μ, t) X N 0 := by
    rw [show CR.psiHatL (μ, t) X N 0 = (CR.chain (μ, t) X N).phi ((mirrorFamily F).step N) 0 1 0 from
      psiHat_one_eq (CR.chain (μ, t) X N) ((mirrorFamily F).step N) 0]
    exact CR.seed_pos _ hp X hXk' N hN2
  -- `Psi_N != 0` (positive bonds)
  have hψN : ψ (N : ℤ) ≠ 0 := by
    intro hN0
    have hA : ∀ k : ℤ, 0 ≤ k → k < (N : ℤ) → (mirrorFamily F).bondA (μ, t) N k ≠ 0 := by
      intro k hk0 hkN
      rw [bondA_mirror]
      exact (hpos _ (by omega) (by omega)).ne'
    have hz := seed_zero_eq_zero (jacSol_mono hJm (show (N : ℤ) ≤ (N : ℤ) + 1 by omega)) hA (by
      show ψ ((N : ℤ) - 0) = 0
      rw [sub_zero]
      exact hN0)
    have hall : ∀ n ∈ rowsOf N, ψ n = 0 := by
      intro n hn
      obtain ⟨hn0, hnN⟩ := Finset.mem_Icc.mp hn
      have hk : (((N : ℤ) - n).toNat : ℤ) = (N : ℤ) - n := Int.toNat_of_nonneg (by omega)
      have := hz ((N : ℤ) - n).toNat (by rw [hk]; omega)
      simp only [hk, sub_sub_cancel] at this
      exact this
    have h0 : ∑ n ∈ rowsOf N, ψ n ^ 2 = 0 := Finset.sum_eq_zero (fun n hn => by rw [hall n hn]; ring)
    linarith
  -- left and right exact solutions
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ψ 0 / CL.psiHatL (μ, t) X N 0 := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; exact div_pos hψ0 hℓ0
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = ψ (N : ℤ) / CR.psiHatL (μ, t) X N 0 := ⟨_, rfl⟩
  have hb0 : b ≠ 0 := by rw [hb]; exact div_ne_zero hψN hr0.ne'
  have hseedL : (fun n => (1 / a) * ψ n) 0 = CL.psiHatL (μ, t) X N 0 := by
    show (1 / a) * ψ 0 = CL.psiHatL (μ, t) X N 0
    rw [ha]; field_simp
  have hseedR : (fun i => (1 / b) * ψ ((N : ℤ) - i)) 0 = CR.psiHatL (μ, t) X N 0 := by
    show (1 / b) * ψ ((N : ℤ) - 0) = CR.psiHatL (μ, t) X N 0
    rw [sub_zero, hb]; field_simp
  have hJL : JacSol F (μ, t) N X (CL.chain (μ, t) X N).NR (fun n => (1 / a) * ψ n) :=
    jacSol_mono (jacSol_smul hJ0 (1 / a)) (chain_NR_le CL (μ, t) hp X hXk' N hN1)
  have hJR : JacSol (mirrorFamily F) (μ, t) N X (CR.chain (μ, t) X N).NR (fun i => (1 / b) * ψ ((N : ℤ) - i)) :=
    jacSol_mono (jacSol_smul hJm (1 / b)) (chain_NR_le CR (μ, t) hp X hXk' N hN2)
  -- an overlap pair
  obtain ⟨S, hS, hScard⟩ := count_pairs (F.step N) F.L CL.c' CL.c N hst hLs hc'L hc'cL (by linarith)
  have h6 : 6 ≤ (CL.c - CL.c') / F.step N := by
    rw [le_div_iff₀ hst]; linarith
  have hSne : S.Nonempty := by
    apply Finset.card_pos.mp
    have : (0 : ℝ) < (S.card : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨n, hnS⟩ := hSne
  obtain ⟨hn0, hn1, hc1, hc2⟩ := hS n hnS
  obtain ⟨pre, hpre1, hpre2⟩ := hpre μ hμ t ht X hXk' N (le_trans hN0r (by exact_mod_cast le_refl _))
  have hcn := hpre2 n hn0 (by omega) hc1 (le_trans (uNode_le_of_le hst.le (by omega)) hc2)
  -- chart rows
  have hL1 : n ≤ (CL.chain (μ, t) X N).NR :=
    le_NR_of CL (μ, t) hp X hXk' N hN1 hst n (le_trans (uNode_le_of_le hst.le (by omega)) hc2)
  have hL2 : n + 1 ≤ (CL.chain (μ, t) X N).NR := le_NR_of CL (μ, t) hp X hXk' N hN1 hst (n + 1) hc2
  have hov1 : CL.c' ≤ uNode (F.step N) (n + 1) := le_trans hc1 (uNode_le_of_le hst.le (by omega))
  have hmir1 : uNode (F.step N) ((N : ℤ) - (n + 1)) = F.L - uNode (F.step N) (n + 1) := uNode_mirror F.L (F.step N) N (n + 1) hLs
  have hmir0 : uNode (F.step N) ((N : ℤ) - n) = F.L - uNode (F.step N) n := uNode_mirror F.L (F.step N) N n hLs
  have hu01 : uNode (F.step N) n ≤ uNode (F.step N) (n + 1) := uNode_le_of_le hst.le (by omega)
  have hR1c : uNode ((mirrorFamily F).step N) ((N : ℤ) - (n + 1)) ≤ CR.c := by
    rw [hstepR, hmir1, hcoup.1]; linarith
  have hR0c : uNode ((mirrorFamily F).step N) ((N : ℤ) - n) ≤ CR.c := by
    rw [hstepR, hmir0, hcoup.1]; linarith
  have hR1' : CR.c' ≤ uNode ((mirrorFamily F).step N) ((N : ℤ) - (n + 1)) := by
    rw [hstepR, hmir1, hcoup.2]; linarith
  have hR0' : CR.c' ≤ uNode ((mirrorFamily F).step N) ((N : ℤ) - n) := by
    rw [hstepR, hmir0, hcoup.2]; linarith
  have hR1 : (N : ℤ) - (n + 1) ≤ (CR.chain (μ, t) X N).NR :=
    le_NR_of CR (μ, t) hp X hXk' N hN2 hst _ hR1c
  have hR0 : (N : ℤ) - n ≤ (CR.chain (μ, t) X N).NR := le_NR_of CR (μ, t) hp X hXk' N hN2 hst _ hR0c
  -- row bounds
  have hbL0 := chart_overlap_row CL (μ, t) hp X hXk' N hN1 n hn0 hL1 hc1
  have hbL1 := chart_overlap_row CL (μ, t) hp X hXk' N hN1 (n + 1) (by omega) hL2 hov1
  have hbR1 := chart_overlap_row CR (μ, t) hp X hXk' N hN2 ((N : ℤ) - (n + 1)) (by omega) hR1 hR1'
  have hbR0 := chart_overlap_row CR (μ, t) hp X hXk' N hN2 ((N : ℤ) - n) (by omega) hR0 hR0'
  rw [hstepR] at hbR1 hbR0
  -- distances of the exact sequences from the comparison sequences
  have dL : ∀ j : ℤ, 0 ≤ j → j ≤ (CL.chain (μ, t) X N).NR → CL.envL (μ, t) X N j ≤ CL.CM * F.step N ^ ((1 : ℝ) / 4) →
      |(1 / a) * ψ j - CL.psiHatL (μ, t) X N j| ≤ |CcL| * F.step N ^ (max M 1) * (CL.CM * F.step N ^ ((1 : ℝ) / 4)) := by
    intro j hj0 hjN hE
    have h1 := hBL (μ, t) hp X hXk' N hN1 (hhL.trans le_rfl) (fun n => (1 / a) * ψ n) hJL hseedL j
      (Finset.mem_Icc.mpr ⟨hj0, hjN⟩)
    refine h1.trans ?_
    have hE0 : 0 ≤ CL.envL (μ, t) X N j := by
      have := (hbL0.2); unfold BulkWeberChart.envL
      exact mul_nonneg (CL.valid _ hp X hXk' N hN1 |>.W_pos j (Finset.mem_Icc.mpr ⟨hj0, hjN⟩)).le
        (CL.valid _ hp X hXk' N hN1 |>.M_pos j (Finset.mem_Icc.mpr ⟨hj0, hjN⟩)).le
    calc CcL * F.step N ^ (max M 1) * CL.envL (μ, t) X N j
        ≤ |CcL| * F.step N ^ (max M 1) * CL.envL (μ, t) X N j :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hst.le _)) hE0
      _ ≤ _ := mul_le_mul_of_nonneg_left hE (mul_nonneg (abs_nonneg _) (pow_nonneg hst.le _))
  have dR : ∀ j : ℤ, 0 ≤ j → j ≤ (CR.chain (μ, t) X N).NR → CR.envL (μ, t) X N j ≤ CR.CM * F.step N ^ ((1 : ℝ) / 4) →
      |(1 / b) * ψ ((N : ℤ) - j) - CR.psiHatL (μ, t) X N j| ≤ |CcR| * F.step N ^ (max M 1) * (CR.CM * F.step N ^ ((1 : ℝ) / 4)) := by
    intro j hj0 hjN hE
    have h1 := hBR (μ, t) hp X hXk' N hN2 (hhR.trans le_rfl) (fun i => (1 / b) * ψ ((N : ℤ) - i)) hJR hseedR j
      (Finset.mem_Icc.mpr ⟨hj0, hjN⟩)
    refine h1.trans ?_
    have hE0 : 0 ≤ CR.envL (μ, t) X N j := by
      unfold BulkWeberChart.envL
      exact mul_nonneg (CR.valid _ hp X hXk' N hN2 |>.W_pos j (Finset.mem_Icc.mpr ⟨hj0, hjN⟩)).le
        (CR.valid _ hp X hXk' N hN2 |>.M_pos j (Finset.mem_Icc.mpr ⟨hj0, hjN⟩)).le
    have hstR : (mirrorFamily F).step N = F.step N := rfl
    rw [hstR]
    calc CcR * F.step N ^ (max M 1) * CR.envL (μ, t) X N j
        ≤ |CcR| * F.step N ^ (max M 1) * CR.envL (μ, t) X N j :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hst.le _)) hE0
      _ ≤ _ := mul_le_mul_of_nonneg_left hE (mul_nonneg (abs_nonneg _) (pow_nonneg hst.le _))
  have hq := fourth_root_sq (F.step N) hst
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = F.step N ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
  rw [← hqdef] at hbL0 hbL1 hbR1 hbR0 dL dR hq
  have hq0 : 0 < q := hq.2
  have hq2 : q ^ 2 = Real.sqrt (F.step N) := hq.1
  have e1 := dL n hn0 hL1 hbL0.2
  have e2 := dL (n + 1) (by omega) hL2 hbL1.2
  have e3 := dR ((N : ℤ) - (n + 1)) (by omega) hR1 hbR1.2
  have e4 := dR ((N : ℤ) - n) (by omega) hR0 hbR0.2
  have eN1 : (N : ℤ) - ((N : ℤ) - (n + 1)) = n + 1 := by ring
  have eN0 : (N : ℤ) - ((N : ℤ) - n) = n := by ring
  rw [eN1] at e3
  rw [eN0] at e4
  have hex : ((1 / a) * ψ n) * ((1 / b) * ψ (n + 1)) - ((1 / a) * ψ (n + 1)) * ((1 / b) * ψ n) = 0 := by ring
  set hm : ℝ := F.step N ^ (max M 1) with hhm
  have hm0 : 0 ≤ hm := pow_nonneg hst.le _
  have hm1' : hm ≤ 1 := pow_le_one₀ hst.le hh1
  have hq0' : 0 ≤ q := hq0.le
  have hCML0 : 0 ≤ CL.CM := by linarith
  have hCMR0 : 0 ≤ CR.CM := by linarith
  have e1' : |(1 / a) * ψ n - CL.psiHatL (μ, t) X N n| ≤ A1 * hm * q :=
    e1.trans (le_of_eq (by rw [hA1]; ring))
  have e2' : |(1 / a) * ψ (n + 1) - CL.psiHatL (μ, t) X N (n + 1)| ≤ A1 * hm * q :=
    e2.trans (le_of_eq (by rw [hA1]; ring))
  have e3' : |(1 / b) * ψ (n + 1) - CR.psiHatL (μ, t) X N ((N : ℤ) - (n + 1))| ≤ A2 * hm * q :=
    e3.trans (le_of_eq (by rw [hA2]; ring))
  have e4' : |(1 / b) * ψ n - CR.psiHatL (μ, t) X N ((N : ℤ) - n)| ≤ A2 * hm * q :=
    e4.trans (le_of_eq (by rw [hA2]; ring))
  have b1 : |CL.psiHatL (μ, t) X N n| ≤ B1 * q := hbL0.1.trans (le_of_eq (by rw [hB1]; ring))
  have b2 : |CL.psiHatL (μ, t) X N (n + 1)| ≤ B1 * q := hbL1.1.trans (le_of_eq (by rw [hB1]; ring))
  have b3 : |CR.psiHatL (μ, t) X N ((N : ℤ) - (n + 1))| ≤ B2 * q := hbR1.1.trans (le_of_eq (by rw [hB2]; ring))
  have b4 : |CR.psiHatL (μ, t) X N ((N : ℤ) - n)| ≤ B2 * q := hbR0.1.trans (le_of_eq (by rw [hB2]; ring))
  have hcas := hat_cas_numeric (F.bondA (μ, t) N n) (CL.psiHatL (μ, t) X N n) (CL.psiHatL (μ, t) X N (n + 1))
    (CR.psiHatL (μ, t) X N ((N : ℤ) - (n + 1))) (CR.psiHatL (μ, t) X N ((N : ℤ) - n))
    ((1 / a) * ψ n) ((1 / a) * ψ (n + 1)) ((1 / b) * ψ (n + 1)) ((1 / b) * ψ n) CA q hm A1 A2 B1 B2
    (hCA (μ, t) hp N n) hex e1' e2' e3' e4' b1 b2 b3 b4 hA1n hA2n hB1n hB2n hq0' hm0 hm1'
  have hChat : |F.bondA (μ, t) N n * (CL.psiHatL (μ, t) X N n * (CR.psiHatL (μ, t) X N ((N : ℤ) - (n + 1))) -
          CL.psiHatL (μ, t) X N (n + 1) * (CR.psiHatL (μ, t) X N ((N : ℤ) - n)))|
        ≤ CA * (Cx * hm * Real.sqrt (F.step N)) := by
    rw [← hq2, hCx]; exact hcas
  exact sin_from_cas _ pre _ c0 Ccas CA Cx hm (Real.sqrt (F.step N)) hc0 (Real.sqrt_pos.mpr hst) hpre1 hm0 hCA0 hCxn
    hChat hcn

/-- **L2.S2 (second half): quantisation.**  `Sigma(X_k, t, h) = pi h (j + 1/2) + O(h^{max M 1 + 1})` for an integer `j` (the label `k'` of `thm:smo-BSr`). -/
theorem bulk_eigen_quant (PI : BulkPhaseInputs F P K t0 Jlo Jhi M U V CL CR)
    (hP : ∀ μ ∈ K, ∀ t ∈ Set.Icc (-t0) t0, (μ, t) ∈ P)
    (hcoup : CR.c = F.L - CL.c' ∧ CR.c' = F.L - CL.c) (r : ℕ) (hr : StdAssump F P (max M 1 / 2) r) :
    ∃ Cq h0 : ℝ, 0 < h0 ∧ ∃ N1 : ℕ, ∀ μ ∈ K, ∀ t ∈ Set.Icc (-t0) t0, ∀ N : ℕ, N1 ≤ N → F.step N ≤ h0 →
      (∀ n : ℤ, 0 ≤ n → n < N → 0 < F.bondA (μ, t) N n) →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
        IsEigenSystem (F.jacobiMat (μ, t) N) Xs Um → ∀ k : Fin (N + 1), Xs k ∈ Set.Icc Jlo Jhi →
          ∃ j : ℤ, |bulkPhaseSum PI μ t (Xs k) N - Real.pi * F.step N * ((j : ℝ) + 1 / 2)|
            ≤ Cq * F.step N ^ (max M 1 + 1) := by
  obtain ⟨Cs, h0, hh0, N1, hmain⟩ := bulk_eigen_sin PI hP hcoup r hr
  refine ⟨Real.pi / 2 * |Cs|, h0, hh0, N1, ?_⟩
  intro μ hμ t ht N hN hstep hpos Xs Um hE k hXk
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hs := hmain μ hμ t ht N hN hstep hpos Xs Um hE k hXk
  have hsin : |Real.sin (bulkPhaseSum PI μ t (Xs k) N / F.step N - Real.pi / 2)| ≤ |Cs| * F.step N ^ (max M 1) :=
    hs.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hst.le _))
  obtain ⟨j, hj⟩ := exists_int_near _ _ hsin
  refine ⟨j, ?_⟩
  have e : bulkPhaseSum PI μ t (Xs k) N - Real.pi * F.step N * ((j : ℝ) + 1 / 2)
      = F.step N * (bulkPhaseSum PI μ t (Xs k) N / F.step N - Real.pi / 2 - Real.pi * j) := by
    field_simp
    ring
  rw [e, abs_mul, abs_of_pos hst]
  calc F.step N * |bulkPhaseSum PI μ t (Xs k) N / F.step N - Real.pi / 2 - Real.pi * j|
      ≤ F.step N * (Real.pi / 2 * (|Cs| * F.step N ^ (max M 1))) := mul_le_mul_of_nonneg_left hj hst.le
    _ = Real.pi / 2 * |Cs| * F.step N ^ (max M 1 + 1) := by ring

/-- **`lem:smo-bulkphase` (3), the labelled windows, for the frozen matrices** (the *input* of `bulk_BSr2`, not proved here):
at an eigenvalue `X_k(t)` in the block, `S_0^{(t)}(X_k(t)) = pi h (k + 1/2) + O(h^2)` with `k` its index from the top. -/
def BulkWindowLabels (F : SymbolFamily (Par × ℝ)) (K : Set Par) (t0 Jlo Jhi : ℝ) : Prop :=
  ∃ Cl h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ t ∈ Set.Icc (-t0) t0, ∀ N : ℕ, F.step N ≤ h0 →
    ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
      IsEigenSystem (F.jacobiMat (μ, t) N) Xs Um → ∀ k : Fin (N + 1), Xs k ∈ Set.Icc Jlo Jhi →
        |actionS0 F (μ, t) (Xs k) - Real.pi * F.step N * ((k : ℕ) + 1 / 2)| ≤ Cl * F.step N ^ 2

/-- **Uniform bound of the phase coefficients** (`i = 0` part of the field `Sigma_bdd`, finding F-S2-2, now a field of `BulkPhaseInputs`). -/
theorem bulkSigmaBdd (PI : BulkPhaseInputs F P K t0 Jlo Jhi M U V CL CR) :
    ∃ Cσ : ℝ, 0 ≤ Cσ ∧ ∀ μ ∈ K, ∀ t ∈ Set.Icc (-t0) t0, ∀ X ∈ Set.Icc Jlo Jhi, ∀ j ≤ M, |PI.Sigma μ j X t| ≤ Cσ := by
  obtain ⟨C, hC⟩ := PI.Sigma_bdd
  refine ⟨max C 0, le_max_right _ _, fun μ hμ t ht X hX j hj => ?_⟩
  have h := hC μ hμ j hj 0 (Nat.zero_le _) (X, t) ⟨hX, ht⟩
  rw [norm_iteratedFDerivWithin_zero] at h
  exact (by simpa [Real.norm_eq_abs] using h : |PI.Sigma μ j X t| ≤ C).trans (le_max_left _ _)

/-- `Sigma - Sigma_0 = O(h^2)`: `Sigma_1 = 0` and the other coefficients are bounded. -/
lemma phaseSum_sub_zero (PI : BulkPhaseInputs F P K t0 Jlo Jhi M U V CL CR) (Cσ : ℝ) (hC : 0 ≤ Cσ) (μ : Par) (hμ : μ ∈ K)
    (t : ℝ) (ht : t ∈ Set.Icc (-t0) t0) (X : ℝ) (hX : X ∈ Set.Icc Jlo Jhi) (N : ℕ)
    (hbd : ∀ j ≤ M, |PI.Sigma μ j X t| ≤ Cσ) (hh1 : F.step N ≤ 1) :
    |bulkPhaseSum PI μ t X N - PI.Sigma μ 0 X t| ≤ M * Cσ * F.step N ^ 2 := by
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  unfold bulkPhaseSum
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, add_sub_cancel_right]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ j ∈ range M, |F.step N ^ (j + 1) * PI.Sigma μ (j + 1) X t| ≤ Cσ * F.step N ^ 2 := by
    intro j hj
    have hj' : j < M := Finset.mem_range.mp hj
    rw [abs_mul, abs_of_pos (pow_pos hst _)]
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      rw [PI.Sigma_one μ hμ X hX t ht]
      simp only [abs_zero, mul_zero]
      exact mul_nonneg hC (by positivity)
    · have hp : F.step N ^ (j + 1) ≤ F.step N ^ 2 := pow_le_pow_of_le_one hst.le hh1 (by omega)
      calc F.step N ^ (j + 1) * |PI.Sigma μ (j + 1) X t| ≤ F.step N ^ 2 * Cσ :=
            mul_le_mul hp (hbd _ (by omega)) (abs_nonneg _) (by positivity)
        _ = Cσ * F.step N ^ 2 := by ring
  calc ∑ j ∈ range M, |F.step N ^ (j + 1) * PI.Sigma μ (j + 1) X t| ≤ ∑ j ∈ range M, Cσ * F.step N ^ 2 :=
        Finset.sum_le_sum hterm
    _ = M * Cσ * F.step N ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **`eq:smo-BSr2` on a bulk block.**  With the labelled windows `BulkWindowLabels`, `j = k` and
`|Sigma(X_k, t, h) - pi h (k + 1/2)| <= C h^{M+1}`. -/
theorem bulk_BSr2 (PI : BulkPhaseInputs F P K t0 Jlo Jhi M U V CL CR)
    (hP : ∀ μ ∈ K, ∀ t ∈ Set.Icc (-t0) t0, (μ, t) ∈ P)
    (hcoup : CR.c = F.L - CL.c' ∧ CR.c' = F.L - CL.c) (r : ℕ) (hr : StdAssump F P (max M 1 / 2) r)
    (hlab : BulkWindowLabels F K t0 Jlo Jhi) :
    ∃ C h0 : ℝ, 0 < h0 ∧ ∃ N1 : ℕ, ∀ μ ∈ K, ∀ t ∈ Set.Icc (-t0) t0, ∀ N : ℕ, N1 ≤ N → F.step N ≤ h0 →
      (∀ n : ℤ, 0 ≤ n → n < N → 0 < F.bondA (μ, t) N n) →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
        IsEigenSystem (F.jacobiMat (μ, t) N) Xs Um → ∀ k : Fin (N + 1), Xs k ∈ Set.Icc Jlo Jhi →
          |bulkPhaseSum PI μ t (Xs k) N - Real.pi * F.step N * ((k : ℕ) + 1 / 2)| ≤ C * F.step N ^ (M + 1) := by
  obtain ⟨Cq, h0q, hh0q, N1, hquant⟩ := bulk_eigen_quant PI hP hcoup r hr
  obtain ⟨Cl, h0l, hh0l, hlab⟩ := hlab
  obtain ⟨Cσ, hCσ, hσ⟩ := bulkSigmaBdd PI
  obtain ⟨C2, hC2⟩ : ∃ x : ℝ, x = M * Cσ + |Cl| + |Cq| := ⟨_, rfl⟩
  have hC2n : 0 ≤ C2 := by rw [hC2]; positivity
  refine ⟨|Cq|, min (min (min h0q h0l) 1) (Real.pi / (2 * (C2 + 1))), ?_, N1, ?_⟩
  · refine lt_min (lt_min (lt_min hh0q hh0l) one_pos) (div_pos Real.pi_pos (by linarith))
  intro μ hμ t ht N hN hstep hpos Xs Um hE k hXk
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hhq : F.step N ≤ h0q := hstep.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hhl : F.step N ≤ h0l := hstep.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hh1 : F.step N ≤ 1 := hstep.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hhp : F.step N ≤ Real.pi / (2 * (C2 + 1)) := hstep.trans (min_le_right _ _)
  obtain ⟨j, hj⟩ := hquant μ hμ t ht N hN hhq hpos Xs Um hE k hXk
  have hl := hlab μ hμ t ht N hhl Xs Um hE k hXk
  have hS0 : PI.Sigma μ 0 (Xs k) t = actionS0 F (μ, t) (Xs k) := PI.Sigma_zero μ hμ (Xs k) hXk t ht
  have hSig := phaseSum_sub_zero PI Cσ hCσ μ hμ t ht (Xs k) hXk N (fun i hi => hσ μ hμ t ht (Xs k) hXk i hi) hh1
  rw [hS0] at hSig
  have hm1 : 1 ≤ max M 1 := le_max_right _ _
  have hpow : F.step N ^ (max M 1 + 1) ≤ F.step N ^ 2 := pow_le_pow_of_le_one hst.le hh1 (by omega)
  have hpowM : F.step N ^ (max M 1 + 1) ≤ F.step N ^ (M + 1) :=
    pow_le_pow_of_le_one hst.le hh1 (by omega)
  have hjk : (j : ℤ) = ((k : ℕ) : ℤ) := by
    have hdiff : Real.pi * F.step N * |((k : ℕ) : ℝ) - (j : ℝ)| ≤ C2 * F.step N ^ 2 := by
      have e : Real.pi * F.step N * (((k : ℕ) : ℝ) - (j : ℝ)) =
          (Real.pi * F.step N * ((k : ℕ) + 1 / 2) - actionS0 F (μ, t) (Xs k))
          + (actionS0 F (μ, t) (Xs k) - bulkPhaseSum PI μ t (Xs k) N)
          + (bulkPhaseSum PI μ t (Xs k) N - Real.pi * F.step N * ((j : ℝ) + 1 / 2)) := by ring
      have hpos' : 0 < Real.pi * F.step N := mul_pos Real.pi_pos hst
      rw [← abs_of_pos hpos', ← abs_mul, e]
      have h1 := abs_sub_comm (actionS0 F (μ, t) (Xs k)) (Real.pi * F.step N * ((k : ℕ) + 1 / 2))
      have h2 := abs_sub_comm (actionS0 F (μ, t) (Xs k)) (bulkPhaseSum PI μ t (Xs k) N)
      calc _ ≤ |Real.pi * F.step N * ((k : ℕ) + 1 / 2) - actionS0 F (μ, t) (Xs k)|
              + |actionS0 F (μ, t) (Xs k) - bulkPhaseSum PI μ t (Xs k) N|
              + |bulkPhaseSum PI μ t (Xs k) N - Real.pi * F.step N * ((j : ℝ) + 1 / 2)| :=
            (abs_add_three _ _ _)
        _ ≤ |Cl| * F.step N ^ 2 + M * Cσ * F.step N ^ 2 + |Cq| * F.step N ^ (max M 1 + 1) := by
            refine add_le_add (add_le_add ?_ ?_) ?_
            · rw [abs_sub_comm]; exact hl.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hst.le 2))
            · rw [abs_sub_comm]; exact hSig
            · exact hj.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hst.le _))
        _ ≤ C2 * F.step N ^ 2 := by
            have := mul_le_mul_of_nonneg_left hpow (abs_nonneg Cq)
            rw [hC2]; nlinarith [this, sq_nonneg (F.step N)]
    have hlt : |((k : ℕ) : ℝ) - (j : ℝ)| < 1 := by
      by_contra hcon
      rw [not_lt] at hcon
      have h3 : Real.pi * F.step N ≤ Real.pi * F.step N * |((k : ℕ) : ℝ) - (j : ℝ)| := by
        nlinarith [mul_pos Real.pi_pos hst]
      have h4 : Real.pi * F.step N ≤ C2 * F.step N ^ 2 := h3.trans hdiff
      have h5 : Real.pi ≤ C2 * F.step N := by
        have : Real.pi * F.step N ≤ C2 * F.step N * F.step N := by nlinarith [h4]
        exact le_of_mul_le_mul_right this hst
      have h6 : C2 * F.step N ≤ Real.pi / 2 := by
        have h7 : F.step N * (2 * (C2 + 1)) ≤ Real.pi := by
          rw [le_div_iff₀ (by positivity)] at hhp; exact hhp
        nlinarith [mul_nonneg hC2n hst.le]
      linarith [Real.pi_pos]
    have hz : |((k : ℕ) : ℤ) - (j : ℤ)| < 1 := by exact_mod_cast hlt
    have := Int.abs_lt_one_iff.mp hz
    omega
  have hjkR : (j : ℝ) = ((k : ℕ) : ℝ) := by exact_mod_cast hjk
  rw [hjkR] at hj
  exact hj.trans (mul_le_mul_of_nonneg_left hpowM (abs_nonneg _) |>.trans' (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hst.le _)))

end Phase

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.exists_int_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.exists_int_near

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.cas_hat_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.cas_hat_bound

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.chart_overlap_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.chart_overlap_row

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bulk_eigen_sin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bulk_eigen_sin

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bulk_eigen_quant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bulk_eigen_quant

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.phaseSum_sub_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.phaseSum_sub_zero

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bulk_BSr2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bulk_BSr2

end FormalResearch.JacobiEigenvectors.TheoremA
