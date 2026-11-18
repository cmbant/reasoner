module

public import FormalResearch.JacobiEigenvectors.TheoremA.Statements
public import FormalResearch.JacobiEigenvectors.Engine.LadderStability
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkNormalisation

/-!
# Paper J, Layer 2: the bulk comparison bound (L2.C1, `BulkSolutionBound`) and the collar part of the bulk eigenvector statement (L2.C2, `PropThaW`)

Source: Paper J `charts.tex` `thm:cha-I` (hard-edge comparison through the collision, every order, `Fix m >= 1`) and
`cor:cha-I-general`; `thmA.tex` `prop:tha-W` (1) and (2) (`Fix m >= 1`); `app_thmA.tex` "The bulk: proof of Proposition prop:tha-W", Steps 1--3.

## Proved here

* `psiHat_one_eq`: on patch `1` the comparison sequence of a ladder chain is the first comparison pair (`psiHat h 1 j = phi h 0 1 j`).
* `bulkSolutionBound_of_one_le` (**L2.C1**): for a bulk Weber chart `C` of order `m` with `1 <= m`, `BulkSolutionBound C` (the frozen statement).
  Proof: the exact solution `psi` of `JacSol` with the chart's seed solves the engine's equations (`A_bond`, `Q_diag`, `Lh_congr_site`);
  `LadderData.stability` (proved, `Engine/LadderStability.lean`) with one patch and a hard-edge seed gives
  `|psi_j - psihat_j| <= mvC (2 K_D K_w h^m Theta) W_j M_j` on `0 <= j <= NR`; `Theta <= C_sum` (`theta_le`), `W_j M_j = envL`, and the smallness
  `2 K_D K_w h^m Theta <= c_*` holds for `h <= h_0` because `h^m <= h` for `m >= 1`.
* `tfun_mirror`, `uMinus_mirror`: the allowed set of the mirror family is the reflection of the original one, `u_-^{mirror} = L - u_+`.
* `bulk_collar_bound` (**L2.C2, third conjunct of `PropThaW`**, the collar relative accuracy): for `delta > 0`, on the rows
  `u_n <= u_- - delta` and `u_n >= u_+ + delta`, `bulkEnv <= Cdelta |bulkVec|` with `Cdelta = 1 / min(c_3^L, c_3^R)`, uniform in `delta`, `h`, `X`, `mu`.
  It uses `collar_lb` of both charts, the shape of both chains and the mirror identity; it does not need the overlap coupling below and does not need `1 <= m`.

## Findings (frozen statements; recorded here, not patched)

* **F-C1 (`m >= 1`).**  `BulkSolutionBound` and `PropThaW` are stated for every `m`; `thm:cha-I` and `prop:tha-W` are stated for `m >= 1` and the proof
  needs it (the engine's smallness `2 K_D K_w h^m Theta <= c_*` is not available for `m = 0`).  Proved under `1 <= m`; the frozen statements need the hypothesis.
* **F-C2 (overlap coupling).**  `PropThaW` takes two independent charts `CL`, `CR`, but the bulk glue (`bulkKappa`, `bulkNorm`, `bulkVec`, `bulkEnv`) and
  the eigenvector comparison need the mirror overlap to be the mirror of the left one: `CR.c = L - CL.c'` and `CR.c' = L - CL.c`
  (`ChartInputs.overlap_match`, which the frozen `ChartInputs` carries but `PropThaW` does not).  Without it the right chart need not cover the rows
  `u_n > CL.c` (its rows stop at `CR.NR`), and `bulkVec`, `bulkEnv` on those rows are unconstrained, so the first conjunct of `PropThaW` is not
  implied by the hypotheses.

## Not formalised

* `PropThaW` conjunct 1 (`BulkSolutionBound CL`, `BulkSolutionBound CR` (`bulkSolutionBound_of_one_le`, needs F-C1), and the normalisation, `kappa`
  bounds and eigenvector comparison (L2.C2 proper)): blocked by F-C1 and F-C2.  The remaining proof is the Step 2 argument of the paper (exact
  eigenvector `= alpha psi^L_exact` on the left, `= beta psi^R_exact` on the right, lower bounds `sum_overlap psihat^2 >= c h^{-1/2}` from the
  Casoratian `cas_lb`/`ladder_S1` and `M_osc`, `W_osc`, the norm and `kappa` comparison).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.Engine

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

/-! ### L2.C2: the collar relative bound of `PropThaW` -/

/-- The mirror symbols: `T^{mirror}(X; u) = T(X; L - u)`. -/
lemma tfun_mirror (G0 B0 : ℝ → ℝ) (L X u : ℝ) :
    Tfun L (fun s => G0 (L - s)) (fun s => B0 (L - s)) X u = Tfun L G0 B0 X (L - u) := by
  unfold Tfun E0
  simp only [sub_sub_cancel]
  ring

/-- The left end of the allowed set of the mirror family is the mirror of the right end: `u_-^{mirror} = L - u_+`, when the allowed set is
nonempty (for `X` in the band, `u_+ >= c + sigma > 0` forces this). -/
theorem uMinus_mirror {Par : Type*} (F : SymbolFamily Par) (μ : Par) (X : ℝ)
    (hne : (Set.Icc 0 F.L ∩ {u | 0 ≤ Tfun F.L (F.G 0 μ) (F.B 0 μ) X u}).Nonempty) :
    (mirrorFamily F).uMinus μ X = F.L - F.uPlus μ X := by
  set S := Set.Icc 0 F.L ∩ {u | 0 ≤ Tfun F.L (F.G 0 μ) (F.B 0 μ) X u} with hS
  have hSm : Set.Icc 0 (mirrorFamily F).L ∩
      {u | 0 ≤ Tfun (mirrorFamily F).L ((mirrorFamily F).G 0 μ) ((mirrorFamily F).B 0 μ) X u}
      = (fun v => F.L - v) '' S := by
    ext u
    show (u ∈ Set.Icc 0 F.L ∧ 0 ≤ Tfun F.L (fun s => F.G 0 μ (F.L - s)) (fun s => F.B 0 μ (F.L - s)) X u)
      ↔ u ∈ (fun v => F.L - v) '' S
    constructor
    · rintro ⟨⟨hu0, huL⟩, hT⟩
      have hT' : 0 ≤ Tfun F.L (F.G 0 μ) (F.B 0 μ) X (F.L - u) := by
        rw [← tfun_mirror]
        exact hT
      exact ⟨F.L - u, ⟨⟨by linarith, by linarith⟩, hT'⟩, by simp⟩
    · rintro ⟨v, ⟨⟨hv0, hvL⟩, hT⟩, hv⟩
      have hu : u = F.L - v := hv.symm
      subst hu
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      rw [tfun_mirror, sub_sub_cancel]
      exact hT
  have hbdd : BddAbove S := ⟨F.L, fun u hu => hu.1.2⟩
  have hanti : Antitone (fun v : ℝ => F.L - v) := fun a b hab => by
    simp only
    linarith
  have hcont : ContinuousAt (fun v : ℝ => F.L - v) (sSup S) :=
    (continuous_const.sub continuous_id).continuousAt
  have key := hanti.map_csSup_of_continuousAt hcont hne hbdd
  unfold SymbolFamily.uMinus SymbolFamily.uPlus
  rw [hSm]
  exact key.symm


/-- A collar bound `c3 W M <= |x|` gives `W M <= |x| / mn` for any `0 < mn <= c3`. -/
lemma env_le_of_collar {W M c3 mn x : ℝ} (hmn : 0 < mn) (hmin : mn ≤ c3) (hWM : 0 ≤ W * M)
    (hc : c3 * W * M ≤ |x|) : W * M ≤ 1 / mn * |x| := by
  have h1 : mn * (W * M) ≤ |x| :=
    calc mn * (W * M) ≤ c3 * (W * M) := mul_le_mul_of_nonneg_right hmin hWM
      _ = c3 * W * M := by ring
      _ ≤ |x| := hc
  calc W * M = 1 / mn * (mn * (W * M)) := by field_simp
    _ ≤ 1 / mn * |x| := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- **L2.C2 (collar part of `prop:tha-W` (2))**: on the forbidden collars `u_n <= u_- - delta` and `u_n >= u_+ + delta` the normalised glued
vector is bounded below by the Weber envelope: `E M <= Cδ |hat Psi_n|`, with `Cδ = 1 / min(c_3^L, c_3^R)` (uniform in `delta`).  This is
the third conjunct of the frozen `PropThaW`, which is proved here (it needs no overlap coupling between the two charts). -/
theorem bulk_collar_bound {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}
    (CL : BulkWeberChart Fz P Jlo Jhi m U V) (CR : BulkWeberChart (mirrorFamily Fz) P Jlo Jhi m U V) :
    ∀ δ : ℝ, 0 < δ → ∃ Cδ h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ X ∈ Set.Icc Jlo Jhi, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h0 →
      ∀ n ∈ rowsOf N, (uNode (Fz.step N) n ≤ Fz.uMinus p X - δ ∨ Fz.uPlus p X + δ ≤ uNode (Fz.step N) n) →
        bulkEnv CL CR p X N n ≤ Cδ * |bulkVec CL CR p X N n| := by
  intro δ hδ
  obtain ⟨hc'L, hc'cL, hσL, -, -, -, -, hc3L, -, -⟩ := CL.consts_pos
  obtain ⟨hc'R, hc'cR, hσR, -, -, -, -, hc3R, -, -⟩ := CR.consts_pos
  have hmin : 0 < min CL.c3 CR.c3 := lt_min hc3L hc3R
  refine ⟨1 / min CL.c3 CR.c3, 1, one_pos, ?_⟩
  intro p hp X hX N hN hstep n hn hcol
  have hNL : CL.N0 ≤ N := le_trans (le_max_left _ _) hN
  have hNR : CR.N0 ≤ N := le_trans (le_max_right _ _) hN
  have hstep_pos : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hLN : Fz.step N * ((N : ℝ) + 1) = Fz.L := step_mul_succ Fz N
  obtain ⟨hn0, hnN⟩ := Finset.mem_Icc.mp hn
  -- the allowed set is nonempty (otherwise `u_+ = 0`, but `u_+ >= c + sigma > 0`)
  obtain ⟨hOWl1, hOWl2⟩ := CL.overlap_in_well p hp X hX
  have hSne : (Set.Icc 0 Fz.L ∩ {u | 0 ≤ Tfun Fz.L (Fz.G 0 p) (Fz.B 0 p) X u}).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : Fz.uPlus p X = 0 := by
      unfold SymbolFamily.uPlus
      rw [hne]
      exact Real.sSup_empty
    linarith
  have hmir : (mirrorFamily Fz).uMinus p X = Fz.L - Fz.uPlus p X := uMinus_mirror Fz p X hSne
  obtain ⟨hOWr1, -⟩ := CR.overlap_in_well p hp X hX
  have hshapeL := CL.shape p hp X hX N hNL
  have hshapeR : (CR.chain p X N).P = 1 ∧ (CR.chain p X N).s0 = 0 ∧ 0 ≤ (CR.chain p X N).NR ∧
      uNode (Fz.step N) (CR.chain p X N).NR ≤ CR.c ∧ CR.c < uNode (Fz.step N) ((CR.chain p X N).NR + 1) :=
    CR.shape p hp X hX N hNR
  rcases hcol with hleft | hright
  · -- left collar: `u_n <= u_- - delta <= c`
    have hu_le : uNode (Fz.step N) n ≤ CL.c := by linarith
    have hnNR : n ≤ (CL.chain p X N).NR := by
      by_contra hcon
      rw [not_le] at hcon
      have h1 : uNode (Fz.step N) ((CL.chain p X N).NR + 1) ≤ uNode (Fz.step N) n :=
        uNode_le_of_le hstep_pos.le (by omega)
      have h2 := hshapeL.2.2.2.2
      linarith
    have hcl := CL.collar_lb p hp X hX N hNL n (Finset.mem_Icc.mpr ⟨hn0, hnNR⟩) (by linarith)
    have hψ : CL.psiHatL p X N n = (CL.chain p X N).phi (Fz.step N) 0 1 n :=
      psiHat_one_eq (CL.chain p X N) (Fz.step N) n
    have hWM : 0 ≤ CL.envL p X N n := by
      have hV := CL.valid p hp X hX N hNL
      have hW := hV.W_pos n (Finset.mem_Icc.mpr ⟨hn0, hnNR⟩)
      have hM := hV.M_pos n (Finset.mem_Icc.mpr ⟨hn0, hnNR⟩)
      unfold BulkWeberChart.envL
      exact (mul_pos hW hM).le
    have hcle : CL.envL p X N n ≤ 1 / min CL.c3 CR.c3 * |CL.psiHatL p X N n| := by
      rw [hψ]
      exact env_le_of_collar hmin (min_le_left _ _) hWM (by simpa [BulkWeberChart.envL] using hcl)
    have hNn : 0 ≤ bulkNorm CL CR p X N := by
      unfold bulkNorm glueNorm
      exact Real.sqrt_nonneg _
    have e1 : bulkEnv CL CR p X N n = CL.envL p X N n / bulkNorm CL CR p X N := by
      simp only [bulkEnv, hu_le, ↓reduceIte]
    have e2 : bulkVec CL CR p X N n = CL.psiHatL p X N n / bulkNorm CL CR p X N := by
      simp only [bulkVec, glueVec, bulkNorm, hu_le, ↓reduceIte]
    rw [e1, e2, abs_div, abs_of_nonneg hNn]
    rcases hNn.eq_or_lt with h0 | hpos
    · rw [← h0]
      simp
    · rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hcle hNn
  · -- right collar: `u_n >= u_+ + delta > c`, the mirror row `r = N - n`
    have hu_gt : CL.c < uNode (Fz.step N) n := by linarith
    have hnc : ¬ uNode (Fz.step N) n ≤ CL.c := not_le.mpr hu_gt
    have hr0 : 0 ≤ (N : ℤ) - n := by omega
    have hur : uNode (Fz.step N) ((N : ℤ) - n) = Fz.L - uNode (Fz.step N) n := uNode_mirror Fz.L (Fz.step N) N n hLN
    have hrmin : uNode (Fz.step N) ((N : ℤ) - n) ≤ (mirrorFamily Fz).uMinus p X := by
      rw [hur, hmir]
      linarith
    have hrNR : (N : ℤ) - n ≤ (CR.chain p X N).NR := by
      by_contra hcon
      rw [not_le] at hcon
      have h1 : uNode (Fz.step N) ((CR.chain p X N).NR + 1) ≤ uNode (Fz.step N) ((N : ℤ) - n) :=
        uNode_le_of_le hstep_pos.le (by omega)
      have h2 := hshapeR.2.2.2.2
      linarith
    have hcr := CR.collar_lb p hp X hX N hNR ((N : ℤ) - n) (Finset.mem_Icc.mpr ⟨hr0, hrNR⟩) hrmin
    have hψR : CR.psiHatL p X N ((N : ℤ) - n) = (CR.chain p X N).phi (Fz.step N) 0 1 ((N : ℤ) - n) :=
      psiHat_one_eq (CR.chain p X N) (Fz.step N) ((N : ℤ) - n)
    have hWM : 0 ≤ CR.envL p X N ((N : ℤ) - n) := by
      have hV := CR.valid p hp X hX N hNR
      have hW := hV.W_pos ((N : ℤ) - n) (Finset.mem_Icc.mpr ⟨hr0, hrNR⟩)
      have hM := hV.M_pos ((N : ℤ) - n) (Finset.mem_Icc.mpr ⟨hr0, hrNR⟩)
      unfold BulkWeberChart.envL
      exact (mul_pos hW hM).le
    have hcle : CR.envL p X N ((N : ℤ) - n) ≤ 1 / min CL.c3 CR.c3 * |CR.psiHatL p X N ((N : ℤ) - n)| := by
      rw [hψR]
      exact env_le_of_collar hmin (min_le_right _ _) hWM (by exact hcr)
    have hNn : 0 ≤ bulkNorm CL CR p X N := by
      unfold bulkNorm glueNorm
      exact Real.sqrt_nonneg _
    have e1 : bulkEnv CL CR p X N n
        = |bulkKappa CL CR p X N| * CR.envL p X N ((N : ℤ) - n) / bulkNorm CL CR p X N := by
      simp only [bulkEnv, hnc, ↓reduceIte]
    have e2 : bulkVec CL CR p X N n
        = bulkKappa CL CR p X N * CR.psiHatL p X N ((N : ℤ) - n) / bulkNorm CL CR p X N := by
      unfold bulkVec glueVec
      simp only [hnc, ↓reduceIte]
      rfl
    rw [e1, e2, abs_div, abs_mul, abs_of_nonneg hNn]
    rcases hNn.eq_or_lt with h0 | hpos
    · rw [← h0]
      simp
    · calc |bulkKappa CL CR p X N| * CR.envL p X N ((N : ℤ) - n) / bulkNorm CL CR p X N
          ≤ |bulkKappa CL CR p X N| * (1 / min CL.c3 CR.c3 * |CR.psiHatL p X N ((N : ℤ) - n)|)
              / bulkNorm CL CR p X N :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcle (abs_nonneg _)) hNn
        _ = 1 / min CL.c3 CR.c3 * (|bulkKappa CL CR p X N| * |CR.psiHatL p X N ((N : ℤ) - n)|
              / bulkNorm CL CR p X N) := by ring


/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bulk_collar_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bulk_collar_bound

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bulkSolutionBound_of_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bulkSolutionBound_of_one_le

/-- The chain of a bulk chart has at most `N + 1` rows (its last row lies below `c < L`). -/
lemma chain_NR_le {Par : Type*} [TopologicalSpace Par] {G : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)}
    {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ} (C : BulkWeberChart G P Jlo Jhi m U V) (p : Par × ℝ) (hp : p ∈ P)
    (X : ℝ) (hX : X ∈ Set.Icc Jlo Jhi) (N : ℕ) (hN : C.N0 ≤ N) :
    (C.chain p X N).NR ≤ (N : ℤ) + 1 := by
  obtain ⟨-, -, -, hNRc, -⟩ := C.shape p hp X hX N hN
  obtain ⟨-, -, -, hcσ, -, -, -, -, -, -⟩ := C.consts_pos
  have hst : 0 < G.step N := FormalResearch.JB.stepSize_pos G.L_pos N
  have hL : G.step N * ((N : ℝ) + 1) = G.L := step_mul_succ G N
  by_contra hcon
  rw [not_le] at hcon
  have h1 : uNode (G.step N) ((N : ℤ) + 1) ≤ uNode (G.step N) ((C.chain p X N).NR) :=
    uNode_le_of_le hst.le (by omega)
  have e : uNode (G.step N) ((N : ℤ) + 1) = G.L + G.step N / 2 := by
    unfold uNode
    push_cast
    linear_combination hL
  have hσ := C.consts_pos
  have hσpos : 0 < C.σ := hσ.2.2.1
  linarith

end FormalResearch.JacobiEigenvectors.TheoremA
