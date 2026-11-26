module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftTails2
public import FormalResearch.JacobiEigenvectors.TheoremA.WindowMass2
public import FormalResearch.JacobiEigenvectors.TheoremA.WindowEnvelopes
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftAssemblyAlg

/-!
# Paper J, Layer 2 (L2.C7): assembly of `prop:tha-W2` (2), part 1: envelopes on the window, masses, matching (chain steps E3, E4, E5)

Source: `app_thmA.tex`, "The soft edges: proof of Proposition prop:tha-W2", Step 4 (a) `(S4env)`, (b) matching, (c) `(S4mass)`; statements as frozen in `Statements.lean` (`PropThaWin`, `PropThaM`, `SoftMirror`).

## The exact chain of lemmas (written before the proofs)

Notation: `C` a soft chart (`CL`, or `CR` of the mirror family, `SoftMirror CL CR`), `a = aOf`, `kappa_b = kappaBal a`, `Omega = softWindow C p X N = {n in rows : |Z_n| <= rho(a)}`,
`T = |lam|/kappa_b`, `m_Omega = wmMass = sum_Omega M_bal(a,Z_n)^2`, `eps = h^m Lm(h)`, `psi` the exact solution seeded by `psi-hat_0`.  Hypotheses of every step: `ParabolicCylinderFacts U V cPC CPC`,
`1 <= m`, `1 <= Lm` on `(0,1]`, `mu in P`, `|X - X_s^+| <= delta_0`, `N >= N_0`, `h <= h_0`, **`a <= a_+`** (a premise: it is the output of Step 0, `Cs0`, see `SoftAssembly2.lean`).

* **E3.0** `soft_win_loc` (a window row is in `|u_n - u_c| < eta/4`: `farChart` + `win_row`); `molv_win_two` (`c kappa^{-1} M <= M_Olv(a,z) <= C kappa^{-1} M` for `|z| <= rho`, from `molv_lower/upper` and `weights_conj`
  through `Wmol_win_bounds`: `W_mol in [e^{-c_W}, e^{c_W}]`).
* **E3.1** `soft_win_psihat`: `|psi-hat_n| <= K T M_bal(a,Z_n)` on `Omega` (`wm_row2`: `|phi^{(1)}_2 - A y| <= h C_B C_1 C_Lambda M` with `y = kappa_b U(a,-Z)`, `|A| <= K_A` (`wm_AA_le`), `|y| <= C_1 M` (`wm_env_two`)).
* **E3.2** `soft_win_err`: `|psi_n - psi-hat_n| <= K eps T M_bal(a,Z_n)` on `Omega` (item (1) of `propThaW2_item1`, PC range, and `molv_win_two`).
* **E4.1** `soft_win_massw`: `c h^{-1/2} <= m_Omega <= C h^{-1/2}` (`win_chart_sums`, i.e. `PropThaWin` (5)); **E4.2** `soft_win_mass`: `c_0 T^2 m_Omega <= sum_Omega psi-hat^2` (`PropThaM`, third conjunct at the cut `s = 0`).
  Both are the proofs of `propThaWin`, `propThaM_of_facts` **without their premise `StdAssump`**, which those proofs do not use (so they apply to the chart `CR` of `mirrorFamily Fz`, for which `StdAssump` is not available).
* **E3.3** `soft_win_sums`: the four `l^2` facts in one statement (`0 < m_Omega`, `sum (psi - psi-hat)^2 <= (K eps T)^2 m_Omega`, `sum psi-hat^2 <= (K T)^2 m_Omega`, `(c T)^2 m_Omega <= sum psi-hat^2`).
* **E5.0** `window_reflect`, `sum_window_reflect`, `wmMass_mirror` (`n in Omega_L <-> N - n in Omega_R`, from `Zof_mirror`, `aOf_mirror`); `match_alg` (`SoftAssemblyAlg.lean`: the `l^2` algebra of Step 4 (b)).
* **E5** `soft_match`: with `psi^L = kappa psi^R` on the rows, `|kappa| |lam_R| <= C_k |lam_L|` (the premise `hkap` of `soft_quant`), `|lam_L| <= C_k |kappa| |lam_R|`, `|kappa-hat - kappa| <= D_k h^m Lm |kappa|`,
  `|kappa-hat| |lam_R| <= (1 + D_k) C_k |lam_L|`, and the normalisation lower bound (E7) `c_n (|lam_L|/kappa_b)^2 h^{-1/2} <= hat N^2` (`glueNorm_ge`, `norm_lower_alg`).

## Differences from the paper

* `StdAssump` is dropped from the window facts (unused by `propThaWin`, `propThaM_of_facts`).  The paper's `|kappa-hat - kappa| <= C h^m |lam_L/lam_R|` is stated with the equivalent `|kappa|` (E5 second inequality).
* constants: `K, c, K_E` are not explicit; `eps small` is `h Lm(h) <= eps_0` through `softHL`.

## Not formalised here

The envelope sum and its `l^2` bound (`SoftAssembly3.lean`), the pointwise comparison with the exact eigenvector, the off-window relative bound, the counting.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

/-! ### Window rows -/

section WindowRows

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

/-- the step threshold of the window lemmas. -/
def asmH0 : ℝ := min (winH1 C) (farThr C)

lemma asmH0_pos : 0 < asmH0 C := lt_min (winH1_pos C) (farThr_pos C)

lemma asmH0_le_one : asmH0 C ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)

/-- a window row is inside the fold collar `|u_n - u_c| < eta/4`. -/
lemma soft_win_loc {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ C.δ0) {N : ℕ}
    (hs : Fz.step N ≤ asmH0 C) {n : ℤ} (hn : n ∈ softWindow C p X N) :
    |uNode (Fz.step N) n - C.uc p| < C.η / 4 := by
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hs1 : Fz.step N ≤ winH1 C := hs.trans (min_le_left _ _)
  have hs3 : Fz.step N ≤ farThr C := hs.trans (min_le_right _ _)
  have hmem : n ∈ rowsOf N ∧ |C.Zof p X N n| ≤ rhoWin (C.aOf p X N) := by
    unfold softWindow at hn
    exact Finset.mem_filter.mp hn
  obtain ⟨hr, hZ⟩ := hmem
  have hr' : 0 ≤ n ∧ n ≤ (N : ℤ) := by
    unfold rowsOf at hr
    exact Finset.mem_Icc.mp hr
  have hc2 : |uNode (Fz.step N) n - C.uc p| ≤ 2 * C.η := by
    by_contra hcon
    have h1 := farChart C p hp X hX N hs3 n hr'.1 hr'.2 (not_le.mp hcon)
    linarith
  exact (win_row C p hp X hX N hh0 hs1 n hc2).2.2.2 (le_trans hZ (by linarith [ell_nonneg' (C.aOf p X N)]))

end WindowRows

/-! ### `M_Olv` against `kappa^{-1} M_bal` on the window (a function lemma) -/

/-- the exponent bound of the weights on the window. -/
def cWt (aplus : ℝ) : ℝ := max (5 / 2) (2 * Real.sqrt (1 + aplus))

lemma Wmol_win_bounds (aplus a z : ℝ) (ha : a ≤ aplus) (hz : |z| ≤ rhoWin a) :
    Real.exp (-cWt aplus) ≤ Wmol a z ∧ Wmol a z ≤ Real.exp (cWt aplus) := by
  have hz' : |z| ≤ rhoWin a + (1 + max (-a) 0) ^ (-(1 : ℝ) / 6) :=
    le_trans hz (by linarith [ell_nonneg' a])
  obtain ⟨hw1, hw2⟩ := weights_conj a aplus z ha hz'
  have hc1 : (5 : ℝ) / 2 ≤ cWt aplus := le_max_left _ _
  have hc2 : 2 * Real.sqrt (1 + aplus) ≤ cWt aplus := le_max_right _ _
  unfold Wmol
  by_cases ha0 : a ≤ 0
  · rw [ite_eq_left ha0]
    obtain ⟨l1, l2⟩ := hw1 ha0
    unfold Wwell
    by_cases hz0 : 0 ≤ z
    · rw [ite_eq_left hz0, abs_of_nonneg hz0] at *
      refine ⟨le_trans (Real.exp_le_exp.mpr (by linarith)) l1, le_trans l2 (Real.one_le_exp (by linarith))⟩
    · rw [ite_eq_right hz0]
      have hl : Real.exp (-(5 : ℝ) / 2) ≤ Ewell a |z| := l1
      have hpos := Ewell_pos a |z|
      have h1 : (1 : ℝ) ≤ (Ewell a |z|)⁻¹ := (one_le_inv₀ hpos).mpr l2
      exact ⟨le_trans (Real.exp_le_one_iff.mpr (by linarith)) h1,
        le_trans (inv_le_exp_five_half _ hl) (Real.exp_le_exp.mpr hc1)⟩
  · rw [ite_eq_right ha0]
    obtain ⟨l1, l2⟩ := hw2 (not_le.mp ha0)
    exact ⟨le_trans (Real.exp_le_exp.mpr (by linarith)) l1, le_trans l2 (Real.exp_le_exp.mpr hc2)⟩


lemma molv_win_two {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (aplus a z : ℝ)
    (ha : a ≤ aplus) (hz : |z| ≤ rhoWin a) :
    cPC * Real.exp (-cWt aplus) * ((kappaBal a)⁻¹ * Mbal a z) ≤ Molv U V a z ∧
      Molv U V a z ≤ CPC * Real.exp (cWt aplus) * ((kappaBal a)⁻¹ * Mbal a z) := by
  obtain ⟨w1, w2⟩ := Wmol_win_bounds aplus a z ha hz
  have hl := molv_lower hf a z
  have hu := molv_upper hf a z
  have hκ := kappaBal_pos a
  have hM := Mbal_pos a z
  have hc := hf.cPC_pos
  have hC : 0 ≤ CPC := le_trans hc.le hf.cPC_le
  have hk : 0 < (kappaBal a)⁻¹ * Mbal a z := mul_pos (inv_pos.mpr hκ) hM
  constructor
  · calc cPC * Real.exp (-cWt aplus) * ((kappaBal a)⁻¹ * Mbal a z)
        ≤ cPC * Wmol a z * ((kappaBal a)⁻¹ * Mbal a z) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left w1 hc.le) hk.le
      _ = cPC * (kappaBal a)⁻¹ * Wmol a z * Mbal a z := by ring
      _ ≤ _ := hl
  · calc Molv U V a z ≤ CPC * (kappaBal a)⁻¹ * Wmol a z * Mbal a z := hu
      _ = CPC * Wmol a z * ((kappaBal a)⁻¹ * Mbal a z) := by ring
      _ ≤ CPC * Real.exp (cWt aplus) * ((kappaBal a)⁻¹ * Mbal a z) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left w2 hC) hk.le

section WindowEnv

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

/-- **E3 (i): the comparison sequence on the window**: `|psi-hat^L_n| <= K (|lam_L|/kappa_b) M_bal(a, Z_n)` for `n` in `Omega`, `a <= a_+`. -/
theorem soft_win_psihat {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (aplus : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p ∈ P, ∀ N : ℕ, C.N0 ≤ N → Fz.step N ≤ asmH0 C → ∀ X, |X - Fz.bandHi p| ≤ C.δ0 →
      C.aOf p X N ≤ aplus → ∀ n ∈ softWindow C p X N,
        |C.psiHatL p X N n| ≤ K * (|C.lamL p X N| / kappaBal (C.aOf p X N)) * Mbal (C.aOf p X N) (C.Zof p X N n) := by
  have hCPC : 0 < CPC := lt_of_lt_of_le hf.cPC_pos hf.cPC_le
  have hC1 : 0 < winCB CPC aplus := by unfold winCB; positivity
  have hKA : 0 ≤ C.cs.KA := C.cs.KA_nonneg
  have hCBc : 0 ≤ C.CBc := C.consts_pos4.2
  have hLam := winCLam_nonneg C
  refine ⟨C.cs.KA * winCB CPC aplus + C.CBc * winCB CPC aplus * winCLam C, by positivity, ?_⟩
  intro p hp N hN hs X hX ha n hn
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hh1 : Fz.step N ≤ 1 := hs.trans (asmH0_le_one C)
  have hs1 : Fz.step N ≤ winH1 C := hs.trans (min_le_left _ _)
  have hcol := soft_win_loc C hp hX hs hn
  obtain ⟨h0, hNn, hZ, hj1, hNR, hc2, hkz⟩ := wm_rowfacts C hp hX hN hs1 hn hcol
  obtain ⟨hcl, -⟩ := abs_lt.mp hcol
  have hgt : C.uc p - C.η / 2 < uNode (Fz.step N) n := by
    have := C.consts_pos.2.1; linarith
  obtain ⟨-, hrow⟩ := wm_row2 hf C aplus hp hX hN ha hs1 hn hcol
  have hAA := wm_AA_le C hp hX hN hj1.le hNR
  have hy := (wm_env_two hf aplus (C.aOf p X N) ha (C.Zof p X N n) hZ).2.1
  have hκ := kappaBal_pos (C.aOf p X N)
  have hM0 := Mbal_nonneg' (C.aOf p X N) (C.Zof p X N n)
  set Mv := Mbal (C.aOf p X N) (C.Zof p X N n) with hMv
  set yv := kappaBal (C.aOf p X N) * U (C.aOf p X N) (-(C.Zof p X N n)) with hyv
  set Av := (C.chain p X N).AA 2 (uNode (Fz.step N) n) (Fz.step N) with hAv
  set φ := (C.chain p X N).phi (Fz.step N) 0 2 n with hφ
  have h1 : |Av * yv| ≤ C.cs.KA * (winCB CPC aplus * Mv) := by
    rw [abs_mul]
    exact mul_le_mul hAA hy (abs_nonneg _) hKA
  have h2 : |φ| ≤ (C.cs.KA * winCB CPC aplus + C.CBc * winCB CPC aplus * winCLam C) * Mv := by
    have e : φ = Av * yv + (φ - Av * yv) := by ring
    have h3 : Fz.step N * (C.CBc * winCB CPC aplus * winCLam C) * Mv ≤ (C.CBc * winCB CPC aplus * winCLam C) * Mv := by
      have : 0 ≤ (C.CBc * winCB CPC aplus * winCLam C) * Mv := by positivity
      nlinarith
    calc |φ| = |Av * yv + (φ - Av * yv)| := by rw [← e]
      _ ≤ |Av * yv| + |φ - Av * yv| := abs_add_le _ _
      _ ≤ C.cs.KA * (winCB CPC aplus * Mv) + (C.CBc * winCB CPC aplus * winCLam C) * Mv := by linarith [h1, hrow, h3]
      _ = _ := by ring
  rw [psiHatL_of_gt C p X N hgt, abs_mul, abs_div, abs_of_pos hκ]
  calc |C.lamL p X N| * (|φ| / kappaBal (C.aOf p X N))
      ≤ |C.lamL p X N| * (((C.cs.KA * winCB CPC aplus + C.CBc * winCB CPC aplus * winCLam C) * Mv) / kappaBal (C.aOf p X N)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h2 hκ.le) (abs_nonneg _)
    _ = _ := by ring

/-- **E3 (ii): the exact solution on the window**: `|psi_n - psi-hat^L_n| <= K h^m Lm (|lam_L|/kappa_b) M_bal(a,Z_n)`. -/
theorem soft_win_err {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) (aplus : ℝ) :
    ∃ K h0 : ℝ, 0 < h0 ∧ 0 ≤ K ∧ ∀ p ∈ P, ∀ N : ℕ, C.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ C.δ0 →
      C.aOf p X N ≤ aplus → ∀ ψ : ℤ → ℝ, JacSol Fz p N X (C.chain p X N).NR ψ → ψ 0 = C.psiHatL p X N 0 →
        ∀ n ∈ softWindow C p X N,
          |ψ n - C.psiHatL p X N n| ≤
            K * (Fz.step N ^ m * Lm (Fz.step N)) * (|C.lamL p X N| / kappaBal (C.aOf p X N)) * Mbal (C.aOf p X N) (C.Zof p X N n) := by
  obtain ⟨Cc, h0a, clam, Clam, h0apos, hclam, H1⟩ := propThaW2_item1 C hf hm hLm
  have hCPC : 0 < CPC := lt_of_lt_of_le hf.cPC_pos hf.cPC_le
  refine ⟨|Cc| * (CPC * Real.exp (cWt aplus)), min h0a (asmH0 C), lt_min h0apos (asmH0_pos C), by positivity, ?_⟩
  intro p hp N hN hstep X hX ha ψ hJ hseed n hn
  have hs0 : Fz.step N ≤ h0a := hstep.trans (min_le_left _ _)
  have hs : Fz.step N ≤ asmH0 C := hstep.trans (min_le_right _ _)
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hh1 : Fz.step N ≤ 1 := hs.trans (asmH0_le_one C)
  have hcol := soft_win_loc C hp hX hs hn
  have hs1 : Fz.step N ≤ winH1 C := hs.trans (min_le_left _ _)
  obtain ⟨h0, hNn, hZ, hj1, hNR, hc2, hkz⟩ := wm_rowfacts C hp hX hN hs1 hn hcol
  obtain ⟨hcl, hcu⟩ := abs_lt.mp hcol
  have hη := C.consts_pos.2.1
  obtain ⟨hmain, -, -⟩ := H1 p hp N hN hs0 X hX
  obtain ⟨-, hPC⟩ := hmain ψ hJ hseed
  have hmem : n ∈ Finset.Icc (0 : ℤ) (C.chain p X N).NR := Finset.mem_Icc.mpr ⟨h0, hNR⟩
  have herr := hPC n hmem (by linarith) (by linarith)
  obtain ⟨-, hmo⟩ := molv_win_two hf aplus (C.aOf p X N) (-(C.Zof p X N n)) ha (by rw [abs_neg]; exact hZ)
  rw [Mbal_neg] at hmo
  have hpow := powLm_nonneg C hh0 hh1
  have hl0 := abs_nonneg (C.lamL p X N)
  have hκ := kappaBal_pos (C.aOf p X N)
  have hM0 := Mbal_nonneg' (C.aOf p X N) (C.Zof p X N n)
  refine herr.trans ?_
  have hCc : Cc ≤ |Cc| := le_abs_self _
  have e0 : 0 ≤ Fz.step N ^ m * Lm (Fz.step N) * |C.lamL p X N| := mul_nonneg hpow hl0
  calc Cc * Fz.step N ^ m * Lm (Fz.step N) * |C.lamL p X N| * Molv U V (C.aOf p X N) (-(C.Zof p X N n))
      = Cc * (Fz.step N ^ m * Lm (Fz.step N) * |C.lamL p X N|) * Molv U V (C.aOf p X N) (-(C.Zof p X N n)) := by ring
    _ ≤ |Cc| * (Fz.step N ^ m * Lm (Fz.step N) * |C.lamL p X N|) * (CPC * Real.exp (cWt aplus) * ((kappaBal (C.aOf p X N))⁻¹ * Mbal (C.aOf p X N) (C.Zof p X N n))) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hCc e0) hmo (molv_nonneg hf _ _)
          (mul_nonneg (abs_nonneg _) e0)
    _ = _ := by field_simp


/-- **E3 (iii): the lattice mass of the window**, `c h^{-1/2} <= m_Omega <= C h^{-1/2}` (`PropThaWin` (5)).  The proof is that of `propThaWin` (`win_chart_sums`), without the premise
`StdAssump`, which `propThaWin` does not use (so that it can be applied to the mirror chart `CR` of the mirror family). -/
theorem soft_win_massw {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (aplus : ℝ) :
    ∃ cM CM h0 : ℝ, 0 < cM ∧ 0 < h0 ∧ ∀ p ∈ P, ∀ N : ℕ, C.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ C.δ0 →
      C.aOf p X N ≤ aplus →
        cM * Fz.step N ^ (-(1 : ℝ) / 2) ≤ wmMass C p X N ∧ wmMass C p X N ≤ CM * Fz.step N ^ (-(1 : ℝ) / 2) := by
  obtain ⟨-, hη, hdm, hdmp, -, -, -, -⟩ := C.consts_pos
  have hdp : 0 < C.dp := lt_of_lt_of_le hdm hdmp
  have hM1 : 1 ≤ max 1 aplus := le_max_left _ _
  have hc0pos : 0 < 1 / (2 * max 1 aplus) := by apply div_pos one_pos; linarith
  have hfpos := farThr_pos C
  have hh0pos : 0 < min (winH1 C) (min C.η (farThr C)) := lt_min (winH1_pos C) (lt_min hη hfpos)
  have hsq : 0 < (1 / (2 * max 1 aplus) / (10 * C.dp)) ^ 2 := pow_pos (div_pos hc0pos (by linarith)) 2
  refine ⟨(1 / (2 * max 1 aplus)) / (2 * C.dp), 11 / C.dm,
    min (min (winH1 C) (min C.η (farThr C))) ((1 / (2 * max 1 aplus) / (10 * C.dp)) ^ 2),
    by positivity, lt_min hh0pos hsq, ?_⟩
  intro p hp N hN hstep X hX haplus
  have hstep1 : Fz.step N ≤ winH1 C := le_trans hstep (le_trans (min_le_left _ _) (min_le_left _ _))
  have hstep2 : Fz.step N ≤ C.η :=
    le_trans hstep (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hstep3 : Fz.step N ≤ farThr C :=
    le_trans hstep (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hstep4 : Fz.step N ≤ (1 / (2 * max 1 aplus) / (10 * C.dp)) ^ 2 := le_trans hstep (min_le_right _ _)
  have hsm : C.dp * Real.sqrt (Fz.step N) ≤ 1 / (2 * max 1 aplus) / 10 := by
    have hq : Real.sqrt (Fz.step N) ≤ 1 / (2 * max 1 aplus) / (10 * C.dp) := by
      have hpos : 0 ≤ 1 / (2 * max 1 aplus) / (10 * C.dp) := by
        apply div_nonneg hc0pos.le; linarith
      rw [← Real.sqrt_sq hpos]
      exact Real.sqrt_le_sqrt hstep4
    calc C.dp * Real.sqrt (Fz.step N) ≤ C.dp * (1 / (2 * max 1 aplus) / (10 * C.dp)) :=
          mul_le_mul_of_nonneg_left hq hdp.le
      _ = 1 / (2 * max 1 aplus) / 10 := by field_simp
  have hfarN : ∀ n : ℤ, 0 ≤ n → n ≤ (N : ℤ) → 2 * C.η < |uNode (Fz.step N) n - C.uc p| →
      rhoWin (C.aOf p X N) < |C.Zof p X N n| :=
    fun n h0 hN' hfn => farChart C p hp X hX N hstep3 n h0 hN' hfn
  obtain ⟨hup, hlow⟩ := win_chart_sums C p hp X hX N hN aplus hstep1 hstep2 hsm haplus hfarN
  exact ⟨hlow, hup⟩

/-- **E4: the mass of `psi-hat^L` on the window**: `c_0 (|lam_L|/kappa_b)^2 m_Omega <= sum_Omega (psi-hat^L)^2` (`PropThaM`, third conjunct at the cut `s = 0`; the proof of `propThaM_of_facts`
without its unused premise `StdAssump`). -/
theorem soft_win_mass {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (aplus : ℝ) :
    ∃ c0 h0 : ℝ, 0 < c0 ∧ 0 < h0 ∧ ∀ p ∈ P, ∀ N : ℕ, C.N0 ≤ N → Fz.step N ≤ min h0 (asmH0 C) → ∀ X, |X - Fz.bandHi p| ≤ C.δ0 →
      C.aOf p X N ≤ aplus →
        c0 * (|C.lamL p X N| / kappaBal (C.aOf p X N)) ^ 2 * wmMass C p X N ≤
          ∑ n ∈ softWindow C p X N, (C.psiHatL p X N n) ^ 2 := by
  obtain ⟨-, hη, hdm, hdmp, -, -, -, -⟩ := C.consts_pos
  have hdp : 0 < C.dp := lt_of_lt_of_le hdm hdmp
  have hCPC : 0 < CPC := lt_of_lt_of_le hf.cPC_pos hf.cPC_le
  have hC1pos : 0 < winCB CPC aplus := by unfold winCB; positivity
  obtain ⟨c1, hc1pos, hc1⟩ := wm_c1 hf aplus
  have hΔ : 0 < wmDelta c1 (winCB CPC aplus ^ 2) C.dp := wmDelta_pos hc1pos (by positivity) hdp
  obtain ⟨cs, hs0, hcs, hhs, hsm⟩ := wm_small hf C aplus hc1pos hc1
  obtain ⟨cl, hl0, hcl, hhl, hlg⟩ := wm_large hf C aplus hΔ
  refine ⟨min cs cl, min hs0 hl0, lt_min hcs hcl, lt_min hhs hhl, ?_⟩
  intro p hp N hN hstep X hX haplus
  have hstep' : Fz.step N ≤ min hs0 hl0 := hstep.trans (min_le_left _ _)
  have hs : Fz.step N ≤ asmH0 C := hstep.trans (min_le_right _ _)
  have hsmall := (le_min_iff.mp hstep').1
  have hlarge := (le_min_iff.mp hstep').2
  have hclaims : WmClaims C p X N (min cs cl) := by
    by_cases hA : Fz.step N * max (-C.aOf p X N) 0 ≤ wmDelta c1 (winCB CPC aplus ^ 2) C.dp
    · exact (hsm p hp X hX N hN hsmall haplus hA).mono (min_le_left _ _) (wmMass_nonneg C p X N)
    · push Not at hA
      exact (hlg p hp X hX N hN hlarge haplus hA).mono (min_le_right _ _) (wmMass_nonneg C p X N)
  obtain ⟨-, -, h3⟩ := hclaims
  have hκ := kappaBal_pos (C.aOf p X N)
  have hcut : 0 ≤ wmCut (C.aOf p X N) := add_nonneg (Real.sqrt_nonneg _) (div_nonneg (ell_nonneg' _) (by norm_num))
  set Ω := softWindow C p X N with hΩ
  have h3' : min cs cl * (kappaBal (C.aOf p X N))⁻¹ ^ 2 * wmMass C p X N ≤
      ∑ n ∈ Ω.filter (fun n => C.Zof p X N n ≤ 0), ((C.chain p X N).phi (Fz.step N) 0 2 n / kappaBal (C.aOf p X N)) ^ 2 := by
    refine wm_unscale3 _ _ _ hκ _ _ (fun n => (C.chain p X N).phi (Fz.step N) 0 2 n) ?_ h3
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, le_trans hn.2 (by linarith)⟩
  have hsub : Ω.filter (fun n => C.Zof p X N n ≤ 0) ⊆ Ω := Finset.filter_subset _ _
  have hmono : ∑ n ∈ Ω.filter (fun n => C.Zof p X N n ≤ 0), (C.psiHatL p X N n) ^ 2 ≤ ∑ n ∈ Ω, (C.psiHatL p X N n) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => sq_nonneg _)
  refine le_trans ?_ hmono
  have hrew : ∑ n ∈ Ω.filter (fun n => C.Zof p X N n ≤ 0), (C.psiHatL p X N n) ^ 2 =
      C.lamL p X N ^ 2 * ∑ n ∈ Ω.filter (fun n => C.Zof p X N n ≤ 0),
        ((C.chain p X N).phi (Fz.step N) 0 2 n / kappaBal (C.aOf p X N)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hnΩ := (Finset.mem_filter.mp hn).1
    have hcol := soft_win_loc C hp hX hs hnΩ
    have hgt : C.uc p - C.η / 2 < uNode (Fz.step N) n := by
      have := (abs_lt.mp hcol).1
      linarith
    rw [psiHatL_of_gt C p X N hgt]; ring
  rw [hrew]
  have hl2 : (|C.lamL p X N| / kappaBal (C.aOf p X N)) ^ 2 = C.lamL p X N ^ 2 * (kappaBal (C.aOf p X N))⁻¹ ^ 2 := by
    rw [div_pow, sq_abs]; field_simp
  rw [hl2]
  calc min cs cl * (C.lamL p X N ^ 2 * (kappaBal (C.aOf p X N))⁻¹ ^ 2) * wmMass C p X N
      = C.lamL p X N ^ 2 * (min cs cl * (kappaBal (C.aOf p X N))⁻¹ ^ 2 * wmMass C p X N) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3' (sq_nonneg _)

end WindowEnv


/-! ### The mirror window -/

section MirrorWin

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  {CL : SoftEdgeChart Fz P m q U V Lm} {CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm}

lemma rowsOf_reflect (N : ℕ) (n : ℤ) : (N : ℤ) - n ∈ rowsOf N ↔ n ∈ rowsOf N := by
  unfold rowsOf
  simp only [Finset.mem_Icc]
  omega

/-- `n in Omega_L` iff `N - n in Omega_R`. -/
lemma window_reflect (hM : SoftMirror CL CR) {p : Par × ℝ} (hp : p ∈ P) (X : ℝ) (N : ℕ) (n : ℤ) :
    n ∈ softWindow CL p X N ↔ (N : ℤ) - n ∈ softWindow CR p X N := by
  unfold softWindow
  simp only [Finset.mem_filter]
  rw [rowsOf_reflect, Zof_mirror hM hp X N n, aOf_mirror hM hp X N, abs_neg]

lemma sum_window_reflect (hM : SoftMirror CL CR) {p : Par × ℝ} (hp : p ∈ P) (X : ℝ) (N : ℕ) (f : ℤ → ℝ) :
    ∑ n ∈ softWindow CL p X N, f ((N : ℤ) - n) = ∑ k ∈ softWindow CR p X N, f k := by
  apply Finset.sum_nbij' (fun n => (N : ℤ) - n) (fun k => (N : ℤ) - k)
  · intro n hn; exact (window_reflect hM hp X N n).mp hn
  · intro k hk
    have := (window_reflect hM hp X N ((N : ℤ) - k)).mpr (by simpa using hk)
    exact this
  · intro n _; simp
  · intro k _; simp
  · intro n _; rfl

lemma wmMass_mirror (hM : SoftMirror CL CR) {p : Par × ℝ} (hp : p ∈ P) (X : ℝ) (N : ℕ) :
    wmMass CR p X N = wmMass CL p X N := by
  unfold wmMass
  rw [← sum_window_reflect hM hp X N (fun k => Mbal (CR.aOf p X N) (CR.Zof p X N k) ^ 2)]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  show Mbal (CR.aOf p X N) (CR.Zof p X N ((N : ℤ) - n)) ^ 2 = _
  rw [Zof_mirror hM hp X N n, aOf_mirror hM hp X N, Mbal_neg]


lemma mirror_ctx (hM : SoftMirror CL CR) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ}
    (hN : CL.N0 ≤ N) :
    CR.N0 ≤ N ∧ |X - (mirrorFamily Fz).bandHi p| ≤ CR.δ0 := by
  obtain ⟨-, -, -, -, hδ, hN0⟩ := hM
  refine ⟨by rw [hN0]; exact hN, ?_⟩
  rw [bandHi_mirror, hδ]; exact hX

end MirrorWin


lemma sumsq_le_of_pointwise (S : Finset ℤ) (f M : ℤ → ℝ) (B : ℝ) (hB : 0 ≤ B) (h : ∀ n ∈ S, |f n| ≤ B * M n) :
    ∑ n ∈ S, f n ^ 2 ≤ B ^ 2 * ∑ n ∈ S, M n ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun n hn => ?_)
  have h1 := h n hn
  have h2 : f n ^ 2 = |f n| ^ 2 := (sq_abs _).symm
  rw [h2]
  calc |f n| ^ 2 ≤ (B * M n) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = B ^ 2 * M n ^ 2 := by ring

lemma sq_scale_le (A B mm : ℝ) (hA : 0 ≤ A) (hAB : A ≤ B) (hmm : 0 ≤ mm) : A ^ 2 * mm ≤ B ^ 2 * mm :=
  mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA hAB 2) hmm

section WinSums

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

/-- **The `l^2` facts of the window for one chart** (E3, E4 in sum form).  With `T = |lam|/kappa_b`, `m_Omega = sum_Omega M_bal^2`, `eps = h^m Lm(h)`:
`0 < m_Omega`, `sum_Omega (psi - psi-hat)^2 <= (K_E eps T)^2 m_Omega`, `sum_Omega psi-hat^2 <= (K T)^2 m_Omega`, `(c T)^2 m_Omega <= sum_Omega psi-hat^2`. -/
theorem soft_win_sums {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) (aplus : ℝ) :
    ∃ K c KE h0 : ℝ, 0 ≤ K ∧ 0 < c ∧ 0 ≤ KE ∧ 0 < h0 ∧ ∀ p ∈ P, ∀ N : ℕ, C.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ C.δ0 →
      C.aOf p X N ≤ aplus →
        0 < wmMass C p X N ∧
        (∀ ψ : ℤ → ℝ, JacSol Fz p N X (C.chain p X N).NR ψ → ψ 0 = C.psiHatL p X N 0 →
          ∑ n ∈ softWindow C p X N, (ψ n - C.psiHatL p X N n) ^ 2 ≤
            (KE * (Fz.step N ^ m * Lm (Fz.step N)) * (|C.lamL p X N| / kappaBal (C.aOf p X N))) ^ 2 * wmMass C p X N) ∧
        ∑ n ∈ softWindow C p X N, (C.psiHatL p X N n) ^ 2 ≤ (K * (|C.lamL p X N| / kappaBal (C.aOf p X N))) ^ 2 * wmMass C p X N ∧
        (c * (|C.lamL p X N| / kappaBal (C.aOf p X N))) ^ 2 * wmMass C p X N ≤ ∑ n ∈ softWindow C p X N, (C.psiHatL p X N n) ^ 2 := by
  obtain ⟨K2, hK2, Hp⟩ := soft_win_psihat C hf aplus
  obtain ⟨K1, h0e, h0ep, hK1, He⟩ := soft_win_err C hf hm hLm aplus
  obtain ⟨c0, h0m, hc0, h0mp, Hm⟩ := soft_win_mass C hf aplus
  obtain ⟨cM, CM, h0w, hcM, h0wp, Hw⟩ := soft_win_massw C hf aplus
  refine ⟨K2, Real.sqrt c0, K1, min (min h0e (min h0m h0w)) (asmH0 C), hK2, Real.sqrt_pos.mpr hc0, hK1,
    lt_min (lt_min h0ep (lt_min h0mp h0wp)) (asmH0_pos C), ?_⟩
  intro p hp N hN hstep X hX ha
  have s1 : Fz.step N ≤ h0e := (hstep.trans (min_le_left _ _)).trans (min_le_left _ _)
  have s2 : Fz.step N ≤ h0m := ((hstep.trans (min_le_left _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have s3 : Fz.step N ≤ h0w := ((hstep.trans (min_le_left _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have s4 : Fz.step N ≤ asmH0 C := hstep.trans (min_le_right _ _)
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hκ := kappaBal_pos (C.aOf p X N)
  have hT0 : 0 ≤ |C.lamL p X N| / kappaBal (C.aOf p X N) := div_nonneg (abs_nonneg _) hκ.le
  have hmpos : 0 < wmMass C p X N := by
    have h1 := (Hw p hp N hN s3 X hX ha).1
    have h2 : 0 < Fz.step N ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hh0 _
    have : 0 < cM * Fz.step N ^ (-(1 : ℝ) / 2) := mul_pos hcM h2
    linarith
  have hh1 : Fz.step N ≤ 1 := s4.trans (asmH0_le_one C)
  have hε0 : 0 ≤ Fz.step N ^ m * Lm (Fz.step N) := powLm_nonneg C hh0 hh1
  refine ⟨hmpos, ?_, ?_, ?_⟩
  · intro ψ hJ hseed
    have := sumsq_le_of_pointwise (softWindow C p X N) (fun n => ψ n - C.psiHatL p X N n)
      (fun n => Mbal (C.aOf p X N) (C.Zof p X N n))
      (K1 * (Fz.step N ^ m * Lm (Fz.step N)) * (|C.lamL p X N| / kappaBal (C.aOf p X N)))
      (by positivity) (fun n hn => by
        have h1 := He p hp N hN s1 X hX ha ψ hJ hseed n hn
        calc |ψ n - C.psiHatL p X N n| ≤ _ := h1
          _ = _ := by ring)
    simpa [wmMass] using this
  · have := sumsq_le_of_pointwise (softWindow C p X N) (C.psiHatL p X N)
      (fun n => Mbal (C.aOf p X N) (C.Zof p X N n)) (K2 * (|C.lamL p X N| / kappaBal (C.aOf p X N)))
      (by positivity) (fun n hn => by
        have h1 := Hp p hp N hN s4 X hX ha n hn
        calc |C.psiHatL p X N n| ≤ _ := h1
          _ = _ := by ring)
    simpa [wmMass] using this
  · have h1 := Hm p hp N hN (le_min_iff.mpr ⟨s2, s4⟩) X hX ha
    have hc : Real.sqrt c0 ^ 2 = c0 := Real.sq_sqrt hc0.le
    calc (Real.sqrt c0 * (|C.lamL p X N| / kappaBal (C.aOf p X N))) ^ 2 * wmMass C p X N
        = c0 * (|C.lamL p X N| / kappaBal (C.aOf p X N)) ^ 2 * wmMass C p X N := by rw [mul_pow, hc]
      _ ≤ _ := h1

end WinSums


section GlueNormLower

open scoped Classical in
/-- the glued vector restricted to a subset `Omega` of the rows has norm at most `hat N`. -/
lemma glueNorm_ge (aL bR : ℤ → ℝ) (Ω rows : Finset ℤ) (isLeft : ℤ → Prop) (hΩ : Ω ⊆ rows) :
    nrm Ω (fun n => if isLeft n then aL n else glueKappa aL bR Ω * bR n) ≤ glueNorm aL bR Ω rows isLeft := by
  unfold nrm glueNorm
  refine Real.sqrt_le_sqrt ?_
  rw [← Finset.sum_filter_add_sum_filter_not Ω isLeft]
  have e1 : ∑ n ∈ Ω.filter isLeft, (if isLeft n then aL n else glueKappa aL bR Ω * bR n) ^ 2 = ∑ n ∈ Ω.filter isLeft, aL n ^ 2 :=
    Finset.sum_congr rfl (fun n hn => by rw [ite_eq_left (Finset.mem_filter.mp hn).2])
  have e2 : ∑ n ∈ Ω.filter (fun n => ¬ isLeft n), (if isLeft n then aL n else glueKappa aL bR Ω * bR n) ^ 2 =
      glueKappa aL bR Ω ^ 2 * ∑ n ∈ Ω.filter (fun n => ¬ isLeft n), bR n ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun n hn => by rw [ite_eq_right (Finset.mem_filter.mp hn).2]; ring)
  rw [e1, e2]
  have h1 : ∑ n ∈ Ω.filter isLeft, aL n ^ 2 ≤ ∑ n ∈ rows.filter isLeft, aL n ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ hΩ) (fun n _ _ => sq_nonneg _)
  have h2 : ∑ n ∈ Ω.filter (fun n => ¬ isLeft n), bR n ^ 2 ≤ ∑ n ∈ rows.filter (fun n => ¬ isLeft n), bR n ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ hΩ) (fun n _ _ => sq_nonneg _)
  have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (glueKappa aL bR Ω))
  linarith

open scoped Classical in
/-- **E7 (normalisation lower bound, abstract)**: `hat N >= (c/2) T_L sqrt(m)` from the `l^2` closeness of `psi-hat`, `psi` on `Omega`, the matching `psi^L = kappa psi^R`, and `|kappa-hat - kappa| <= D e |kappa|`. -/
lemma norm_lower_alg (Ω rows : Finset ℤ) (hΩ : Ω ⊆ rows) (isLeft : ℤ → Prop) (aL bR uL uR : ℤ → ℝ)
    (κ TL TR mm KK KE cc ε Dk Ck : ℝ) (hmm : 0 < mm) (hTL : 0 ≤ TL) (hTR : 0 ≤ TR) (hcc : 0 < cc) (hKK : 0 ≤ KK) (hKE : 0 ≤ KE)
    (hε : 0 ≤ ε) (hDk : 0 ≤ Dk) (hCk : 0 ≤ Ck) (hrel : ∀ n ∈ Ω, uL n = κ * uR n)
    (hA : ∑ n ∈ Ω, (uL n - aL n) ^ 2 ≤ ((KE * ε) * TL) ^ 2 * mm)
    (hB : ∑ n ∈ Ω, (uR n - bR n) ^ 2 ≤ ((KE * ε) * TR) ^ 2 * mm)
    (hB1 : ∑ n ∈ Ω, bR n ^ 2 ≤ (KK * TR) ^ 2 * mm) (hA0 : (cc * TL) ^ 2 * mm ≤ ∑ n ∈ Ω, aL n ^ 2)
    (m1 : |κ| * TR ≤ Ck * TL) (c3 : |glueKappa aL bR Ω - κ| ≤ Dk * ε * |κ|)
    (hcz : (KE + KE * Ck + Dk * KK * Ck) * ε ≤ cc / 2) :
    (cc / 2) * (TL * Real.sqrt mm) ≤ glueNorm aL bR Ω rows isLeft := by
  have hSp : 0 < Real.sqrt mm := Real.sqrt_pos.mpr hmm
  set S := Real.sqrt mm with hS
  set κh := glueKappa aL bR Ω with hκh
  have nA := nrm_le_of_sq Ω (fun n => uL n - aL n) (KE * ε * TL) mm (by positivity) hmm.le hA
  have nB := nrm_le_of_sq Ω (fun n => uR n - bR n) (KE * ε * TR) mm (by positivity) hmm.le hB
  have nR1 := nrm_le_of_sq Ω bR (KK * TR) mm (by positivity) hmm.le hB1
  have nL0 := le_nrm_of_sq Ω aL (cc * TL) mm (by positivity) hmm.le hA0
  have hid : nrm Ω (fun n => aL n - κh * bR n) =
      nrm Ω (fun n => ((-1) * (uL n - aL n) + κ * (uR n - bR n)) + (κ - κh) * bR n) :=
    nrm_congr Ω _ _ (fun n hn => by rw [hrel n hn]; ring)
  have tri := nrm_add_le Ω (fun n => (-1) * (uL n - aL n) + κ * (uR n - bR n)) (fun n => (κ - κh) * bR n)
  have tri2 := nrm_add_le Ω (fun n => (-1) * (uL n - aL n)) (fun n => κ * (uR n - bR n))
  rw [nrm_smul, nrm_smul] at tri2
  rw [nrm_smul] at tri
  simp only [abs_neg, abs_one, one_mul] at tri2
  have hb1 : |κ - κh| * nrm Ω bR ≤ (Dk * ε * |κ|) * ((KK * TR) * S) := by
    rw [abs_sub_comm]
    exact mul_le_mul c3 nR1 (nrm_nonneg _ _) (by positivity)
  have hb2 : |κ| * nrm Ω (fun n => uR n - bR n) ≤ |κ| * ((KE * ε * TR) * S) :=
    mul_le_mul_of_nonneg_left nB (abs_nonneg _)
  have t1 := mul_le_mul_of_nonneg_left m1 (by positivity : 0 ≤ KE * ε * S)
  have t2 := mul_le_mul_of_nonneg_left m1 (by positivity : 0 ≤ Dk * ε * KK * S)
  have hfres : nrm Ω (fun n => aL n - κh * bR n) ≤ ((KE + KE * Ck + Dk * KK * Ck) * ε) * (TL * S) := by
    rw [hid]
    have h5 : nrm Ω (fun n => ((-1) * (uL n - aL n) + κ * (uR n - bR n)) + (κ - κh) * bR n) ≤
        nrm Ω (fun n => uL n - aL n) + |κ| * nrm Ω (fun n => uR n - bR n) + |κ - κh| * nrm Ω bR := by linarith
    refine h5.trans ?_
    have h6 : nrm Ω (fun n => uL n - aL n) + |κ| * nrm Ω (fun n => uR n - bR n) + |κ - κh| * nrm Ω bR ≤
        (KE * ε * TL) * S + |κ| * ((KE * ε * TR) * S) + (Dk * ε * |κ|) * ((KK * TR) * S) := by linarith
    refine h6.trans ?_
    nlinarith [t1, t2]
  have hmono : nrm Ω (fun n => aL n - (if isLeft n then aL n else κh * bR n)) ≤ nrm Ω (fun n => aL n - κh * bR n) := by
    apply nrm_mono
    intro n _
    by_cases hz : isLeft n
    · simp [hz]
    · simp [hz]
  have hge := glueNorm_ge aL bR Ω rows isLeft hΩ
  have hrev := nrm_sub_le Ω aL (fun n => if isLeft n then aL n else κh * bR n)
  beta_reduce at hrev
  have h1 := (abs_le.mp hrev).2
  have h6 : ((KE + KE * Ck + Dk * KK * Ck) * ε) * (TL * S) ≤ (cc / 2) * (TL * S) :=
    mul_le_mul_of_nonneg_right hcz (by positivity)
  have h4 : (cc * TL) * S ≤ nrm Ω aL := nL0
  linarith

end GlueNormLower

section Match

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (CL : SoftEdgeChart Fz P m q U V Lm) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V Lm)

/-- **E5 (matching, app_thmA Step 4 (a)--(b)) on the charts.**  For `a <= a_+` and exact solutions `psi^L`, `psi'` (`psi^R_n = psi'_{N-n}`) with `psi^L = kappa psi^R`:
`|kappa| |lam_R| <= C_k |lam_L|`, `|lam_L| <= C_k |kappa| |lam_R|`, `|kappa-hat - kappa| <= D_k h^m Lm |kappa|`, and `|kappa-hat| |lam_R| <= (1 + D_k) C_k |lam_L|`. -/
theorem soft_match {cPC CPC : ℝ} (hf : ParabolicCylinderFacts U V cPC CPC) (hm : 1 ≤ m)
    (hLm : ∀ h : ℝ, 0 < h → h ≤ 1 → 1 ≤ Lm h) (hM : SoftMirror CL CR) (aplus : ℝ) :
    ∃ Ck Dk cn h0 : ℝ, 0 < h0 ∧ 0 ≤ Ck ∧ 0 ≤ Dk ∧ 0 < cn ∧ ∀ p ∈ P, ∀ N : ℕ, CL.N0 ≤ N → Fz.step N ≤ h0 → ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 →
      CL.aOf p X N ≤ aplus →
      ∀ (ψL ψ' : ℤ → ℝ) (κ : ℝ),
        JacSol Fz p N X (CL.chain p X N).NR ψL → ψL 0 = CL.psiHatL p X N 0 →
        JacSol (mirrorFamily Fz) p N X (CR.chain p X N).NR ψ' → ψ' 0 = CR.psiHatL p X N 0 →
        (∀ n ∈ rowsOf N, ψL n = κ * ψ' ((N : ℤ) - n)) →
        |κ| * |CR.lamL p X N| ≤ Ck * |CL.lamL p X N| ∧ |CL.lamL p X N| ≤ Ck * (|κ| * |CR.lamL p X N|) ∧
          |softKappa CL CR p X N - κ| ≤ Dk * (Fz.step N ^ m * Lm (Fz.step N)) * |κ| ∧
          |softKappa CL CR p X N| * |CR.lamL p X N| ≤ (1 + Dk) * Ck * |CL.lamL p X N| ∧
          cn * ((|CL.lamL p X N| / kappaBal (CL.aOf p X N)) ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2)) ≤ softNorm CL CR p X N ^ 2 := by
  obtain ⟨KL, cL, KEL, h0L, hKL, hcL, hKEL, h0Lp, HL⟩ := soft_win_sums CL hf hm hLm aplus
  obtain ⟨KR, cR, KER, h0R, hKR, hcR, hKER, h0Rp, HR⟩ := soft_win_sums CR hf hm hLm aplus
  obtain ⟨CcR, h0aR, clamR, ClamR, h0aRp, hclamR, H1R⟩ := propThaW2_item1 CR hf hm hLm
  obtain ⟨cM, CM, h0M, hcM, h0Mp, HM⟩ := soft_win_massw CL hf aplus
  set cc : ℝ := min cL cR with hcc
  have hcc0 : 0 < cc := lt_min hcL hcR
  set KK : ℝ := max KL KR with hKK
  have hKK0 : 0 ≤ KK := le_trans hKL (le_max_left _ _)
  set KE : ℝ := max KEL KER with hKE
  have hKE0 : 0 ≤ KE := le_trans hKEL (le_max_left _ _)
  set Dk : ℝ := KE * ((1 + 2 * (KK + cc / 2) / cc) / cc) with hDk
  set Ck : ℝ := 2 * (KK + cc / 2) / cc with hCk
  have hCk0 : 0 ≤ Ck := by positivity
  have hDk0 : 0 ≤ Dk := by positivity
  set Cz : ℝ := KE + KE * Ck + Dk * KK * Ck with hCz
  have hCz0 : 0 ≤ Cz := by positivity
  set Cw : ℝ := KE + 1 + Cz with hCw
  set eps0 : ℝ := cc / (2 * Cw) with heps0
  have hCwpos : 0 < Cw := by positivity
  have heps0p : 0 < eps0 := by positivity
  refine ⟨Ck, Dk, (cc / 2) ^ 2 * cM, min (min h0L h0R) (min (min h0aR h0M) (min (softHL CL eps0) (min (softHL CL 1) (min (asmH0 CL) 1)))), ?_, hCk0, hDk0, by positivity, ?_⟩
  · exact lt_min (lt_min h0Lp h0Rp) (lt_min (lt_min h0aRp h0Mp) (lt_min (softHL_pos CL eps0) (lt_min (softHL_pos CL 1) (lt_min (asmH0_pos CL) one_pos))))
  intro p hp N hN hstep X hX ha ψL ψ' κ hJL hsL hJR hsR hrel
  obtain ⟨hNR, hXR⟩ := mirror_ctx hM hp hX hN
  have haR : CR.aOf p X N = CL.aOf p X N := aOf_mirror hM hp X N
  have hstepR : (mirrorFamily Fz).step N = Fz.step N := rfl
  have sL : Fz.step N ≤ h0L := (hstep.trans (min_le_left _ _)).trans (min_le_left _ _)
  have sR : Fz.step N ≤ h0R := (hstep.trans (min_le_left _ _)).trans (min_le_right _ _)
  have sa : Fz.step N ≤ h0aR := hstep.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have sM : Fz.step N ≤ h0M := hstep.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have se : Fz.step N ≤ softHL CL eps0 := hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have s1 : Fz.step N ≤ softHL CL 1 := hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have s7 : Fz.step N ≤ 1 := hstep.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  have hh0 : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hκ := kappaBal_pos (CL.aOf p X N)
  have hlamRpos : 0 < |CR.lamL p X N| := by
    obtain ⟨-, hlowR, -⟩ := H1R p hp N hNR (by rw [hstepR]; exact sa) X hXR
    have h1 := softLam_pos CR p X N
    have h2 := kappaBal_pos (CR.aOf p X N)
    have : 0 < clamR * (softLam CR p X N * kappaBal (CR.aOf p X N)) := by positivity
    linarith
  obtain ⟨hmL, hAL, hL1, hL0⟩ := HL p hp N hN sL X hX ha
  obtain ⟨hmR, hAR, hR1, hR0⟩ := HR p hp N hNR (by rw [hstepR]; exact sR) X hXR (by rw [haR]; exact ha)
  have hmmR : wmMass CR p X N = wmMass CL p X N := wmMass_mirror hM hp X N
  simp only [haR, hstepR, hmmR] at hmR hAR hR1 hR0
  set a := CL.aOf p X N with ha_def
  set TL := |CL.lamL p X N| / kappaBal a with hTL
  set TR := |CR.lamL p X N| / kappaBal a with hTR
  set mm := wmMass CL p X N with hmm
  set ε := Fz.step N ^ m * Lm (Fz.step N) with hε
  have hh1 : Fz.step N ≤ 1 := s7
  have hLm1 := hLm (Fz.step N) hh0 hh1
  have hε0 : 0 ≤ ε := powLm_nonneg CL hh0 hh1
  have hεle : ε ≤ Fz.step N * Lm (Fz.step N) := by
    have h1 : Fz.step N ^ m ≤ Fz.step N := pow_le_of_le_one hh0.le hh1 (by omega)
    exact mul_le_mul_of_nonneg_right h1 (by linarith)
  have hεeps : ε ≤ eps0 := hεle.trans (softHL_spec CL heps0p hh0 se)
  have hε1 : ε ≤ 1 := hεle.trans (softHL_spec CL one_pos hh0 s1)
  have he0 : 0 ≤ KE * ε := mul_nonneg hKE0 hε0
  have hCwε : Cw * ε ≤ cc / 2 := by
    calc Cw * ε ≤ Cw * eps0 := mul_le_mul_of_nonneg_left hεeps hCwpos.le
      _ = cc / 2 := by rw [heps0]; field_simp
  have hec : KE * ε ≤ cc / 2 :=
    le_trans (mul_le_mul_of_nonneg_right (by rw [hCw]; linarith [hCz0]) hε0) hCwε
  have hcz : Cz * ε ≤ cc / 2 :=
    le_trans (mul_le_mul_of_nonneg_right (by rw [hCw]; linarith [hKE0]) hε0) hCwε
  have hTL0 : 0 ≤ TL := div_nonneg (abs_nonneg _) hκ.le
  have hTRpos : 0 < TR := div_pos hlamRpos hκ
  -- the exact solutions on the window
  set Ω := softWindow CL p X N with hΩ
  have hΩrows : ∀ n ∈ Ω, n ∈ rowsOf N := fun n hn => (Finset.mem_filter.mp hn).1
  have hAL' := hAL ψL hJL hsL
  have hAR' := hAR ψ' hJR hsR
  -- reflect the right sums
  have hsumB : ∑ n ∈ Ω, (ψ' ((N : ℤ) - n) - softSeqR CR p X N n) ^ 2 =
      ∑ k ∈ softWindow CR p X N, (ψ' k - CR.psiHatL p X N k) ^ 2 := by
    rw [← sum_window_reflect hM hp X N (fun k => (ψ' k - CR.psiHatL p X N k) ^ 2)]
    rfl
  have hsumR1 : ∑ n ∈ Ω, (softSeqR CR p X N n) ^ 2 = ∑ k ∈ softWindow CR p X N, (CR.psiHatL p X N k) ^ 2 := by
    rw [← sum_window_reflect hM hp X N (fun k => (CR.psiHatL p X N k) ^ 2)]
    rfl
  have hB : ∑ n ∈ Ω, (ψ' ((N : ℤ) - n) - softSeqR CR p X N n) ^ 2 ≤ ((KE * ε) * TR) ^ 2 * mm := by
    rw [hsumB]
    refine hAR'.trans (sq_scale_le _ _ _ (mul_nonneg (mul_nonneg hKER hε0) hTRpos.le) ?_ hmL.le)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hε0) hTRpos.le
  have hB1 : ∑ n ∈ Ω, (softSeqR CR p X N n) ^ 2 ≤ (KK * TR) ^ 2 * mm := by
    rw [hsumR1]
    exact hR1.trans (sq_scale_le _ _ _ (mul_nonneg hKR hTRpos.le) (mul_le_mul_of_nonneg_right (le_max_right _ _) hTRpos.le) hmL.le)
  have hB0 : (cc * TR) ^ 2 * mm ≤ ∑ n ∈ Ω, (softSeqR CR p X N n) ^ 2 := by
    rw [hsumR1]
    exact le_trans (sq_scale_le _ _ _ (mul_nonneg hcc0.le hTRpos.le) (mul_le_mul_of_nonneg_right (min_le_right _ _) hTRpos.le) hmL.le) hR0
  have hA : ∑ n ∈ Ω, (ψL n - CL.psiHatL p X N n) ^ 2 ≤ ((KE * ε) * TL) ^ 2 * mm := by
    refine hAL'.trans (sq_scale_le _ _ _ (mul_nonneg (mul_nonneg hKEL hε0) hTL0) ?_ hmL.le)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hε0) hTL0
  have hA1 : ∑ n ∈ Ω, (CL.psiHatL p X N n) ^ 2 ≤ (KK * TL) ^ 2 * mm :=
    hL1.trans (sq_scale_le _ _ _ (mul_nonneg hKL hTL0) (mul_le_mul_of_nonneg_right (le_max_left _ _) hTL0) hmL.le)
  have hA0 : (cc * TL) ^ 2 * mm ≤ ∑ n ∈ Ω, (CL.psiHatL p X N n) ^ 2 :=
    le_trans (sq_scale_le _ _ _ (mul_nonneg hcc0.le hTL0) (mul_le_mul_of_nonneg_right (min_le_left _ _) hTL0) hmL.le) hL0
  have hrelΩ : ∀ n ∈ Ω, ψL n = κ * ψ' ((N : ℤ) - n) := fun n hn => hrel n (hΩrows n hn)
  obtain ⟨m1, m2, m3⟩ := match_alg Ω (CL.psiHatL p X N) (softSeqR CR p X N) ψL (fun n => ψ' ((N : ℤ) - n)) κ TL TR mm KK cc
    (KE * ε) hmL hTL0 hTRpos hcc0 he0 hKK0 hec hrelΩ hA hB hA1 hA0 hB1 hB0
  have hTLe : |CL.lamL p X N| = kappaBal a * TL := by rw [hTL]; field_simp
  have hTRe : |CR.lamL p X N| = kappaBal a * TR := by rw [hTR]; field_simp
  have c1 : |κ| * |CR.lamL p X N| ≤ Ck * |CL.lamL p X N| := by
    rw [hTLe, hTRe]
    have := mul_le_mul_of_nonneg_left m1 hκ.le
    calc |κ| * (kappaBal a * TR) = kappaBal a * (|κ| * TR) := by ring
      _ ≤ kappaBal a * (Ck * TL) := this
      _ = Ck * (kappaBal a * TL) := by ring
  have c2 : |CL.lamL p X N| ≤ Ck * (|κ| * |CR.lamL p X N|) := by
    rw [hTLe, hTRe]
    have := mul_le_mul_of_nonneg_left m2 hκ.le
    calc kappaBal a * TL ≤ kappaBal a * (Ck * (|κ| * TR)) := this
      _ = Ck * (|κ| * (kappaBal a * TR)) := by ring
  have c3 : |softKappa CL CR p X N - κ| ≤ Dk * ε * |κ| := by
    have h : softKappa CL CR p X N = glueKappa (CL.psiHatL p X N) (softSeqR CR p X N) Ω := rfl
    rw [h]
    refine m3.trans (le_of_eq ?_)
    rw [hDk]; ring
  have hnorm : ((cc / 2) ^ 2 * cM) * (TL ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2)) ≤ softNorm CL CR p X N ^ 2 := by
    have hlow := norm_lower_alg Ω (rowsOf N) hΩrows (fun n => CL.Zof p X N n ≤ 0) (CL.psiHatL p X N) (softSeqR CR p X N) ψL
      (fun n => ψ' ((N : ℤ) - n)) κ TL TR mm KK KE cc ε Dk Ck hmL hTL0 hTRpos.le hcc0 hKK0 hKE0 hε0 hDk0 hCk0 hrelΩ hA hB hB1 hA0 m1 c3 hcz
    have hSq : Real.sqrt mm ^ 2 = mm := Real.sq_sqrt hmL.le
    have hmm0 := (HM p hp N hN sM X hX ha).1
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ (cc / 2) * (TL * Real.sqrt mm)) hlow 2
    calc ((cc / 2) ^ 2 * cM) * (TL ^ 2 * Fz.step N ^ (-(1 : ℝ) / 2)) = (cc / 2) ^ 2 * TL ^ 2 * (cM * Fz.step N ^ (-(1 : ℝ) / 2)) := by ring
      _ ≤ (cc / 2) ^ 2 * TL ^ 2 * mm := mul_le_mul_of_nonneg_left hmm0 (by positivity)
      _ = ((cc / 2) * (TL * Real.sqrt mm)) ^ 2 := by rw [mul_pow, mul_pow, hSq]; ring
      _ ≤ _ := hsq
  refine ⟨c1, c2, c3, ?_, hnorm⟩
  generalize softKappa CL CR p X N = kh at c3 ⊢
  have hk1 : |kh| ≤ (1 + Dk) * |κ| := by
    have h1 : |kh| ≤ |κ| + |kh - κ| := by
      have := abs_add_le κ (kh - κ)
      rwa [add_sub_cancel] at this
    have h2 : Dk * ε * |κ| ≤ Dk * |κ| :=
      mul_le_mul_of_nonneg_right (by simpa using mul_le_mul_of_nonneg_left hε1 hDk0) (abs_nonneg κ)
    linarith
  calc |kh| * |CR.lamL p X N| ≤ ((1 + Dk) * |κ|) * |CR.lamL p X N| :=
        mul_le_mul_of_nonneg_right hk1 (abs_nonneg _)
    _ = (1 + Dk) * (|κ| * |CR.lamL p X N|) := by ring
    _ ≤ (1 + Dk) * (Ck * |CL.lamL p X N|) := mul_le_mul_of_nonneg_left c1 (by linarith)
    _ = (1 + Dk) * Ck * |CL.lamL p X N| := by ring

end Match


/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_win_loc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_win_loc

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.molv_win_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms molv_win_two

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_win_psihat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_win_psihat

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_win_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_win_err

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_win_massw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_win_massw

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_win_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_win_mass

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_win_sums' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_win_sums

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.window_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms window_reflect

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.wmMass_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wmMass_mirror

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.soft_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms soft_match

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.glueNorm_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms glueNorm_ge

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.norm_lower_alg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_lower_alg

end FormalResearch.JacobiEigenvectors.TheoremA

end
