module

public import FormalResearch.JacobiEigenvectors.TheoremA.WindowMass
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftTransfer
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftRescale

/-!
# Paper J, Layer 2: the window mass, assembly (`lem:tha-M`, `PropThaM`, plan item L2.C4), continued from `WindowMass.lean`

Source: app_thmA, lemma `lem:tha-M` (Steps 2, 3 and the corrector step of its proof; Step 1 is `wm_c1` in `WindowMass.lean`).
Frozen statement: `PropThaM` (`TheoremA/Statements.lean`).

## What is proved

`propThaM_of_facts : PropThaM Fz P m q U V CL aplus cPC CPC` (the frozen statement, corrected in round 7: F-PW7 added the premise `ParabolicCylinderFacts`), for the soft chart `CL` (with the
corrector field `corr_PC`).  The premise on `U`, `V` is missing from the frozen `PropThaM` (see the finding in `WindowMass.lean`).  Structure: put `A = max(-a,0)`, `Delta = wmDelta c1 (winCB^2) dp`.
* branch `h A <= Delta` (`wm_small`, via `wm_small12`, `wm_small3`): Step 2 lattice transfer of the continuous mass `c_1`
  (`wm_step2_abstract`, with `WmBlock`/`wm_ctx`) for the uncorrected `U`, then the corrector step `wm_corr_lower` for the
  third conjunct (`gm <= AA`, `|phi - AA y| <= h E M`, `wm_row2`);
* branch `h A > Delta` (`wm_large`, via `wm_large2`, `wm_large1`, `wm_conj1_large`, `wm_conj2_large`): Step 3, the two-site
  Casoratian: `cas_lb` at the sites of the corrected pair (`wm_cas_site`) gives `c_3 M_n^2 <= phi_n^2 + phi_{n+1}^2` on
  patch 2 (`wm_pair2_row`) and patch 3 (`wm_pair3_row`) rows with `5/4 sqrt A < |Z| <= 7/4 sqrt A`; summing over the lattice
  rows (`wm_count`, `wm_mass_rows`, `wm_pair_sum`) gives the third conjunct for `phi^{(1)}_2` and the first for `phi^{(1)}_3`;
  `wm_corr_upper` transfers these to `y` (`wm_conj_from_phi`, `|AA| <= K_A` from `A_bd`: `wm_AA_le`).
* the final assembly unscales `kappaBal`, enlarges the index sets by monotonicity in the cut, and takes the minimum of the two
  constants (`wm_unscale`, `wm_unscale3`, `propThaM_of_facts`).

## Differences from the paper

* The paper's Step 3 states the bound on the whole of `Omega` with the corrected pair at the sites; here the pair bound is
  proved on rows of the `5/4 <= |Z|/sqrt A <= 7/4` annulus only (a sufficient part of the window; `M_bal^2 >= 1/sqrt A` there),
  and the conclusions for `y` come from the corrector transfer with the chart bounds `|AA| <= K_A` (`A_bd`), `gm <= AA`,
  `|BB| <= CBc` (new chart fields, see `WindowMass.lean`).
* The two branches are separated by `h A` against the explicit threshold `wmDelta`; in the paper the split is at
  `tilde mu = delta`, with unspecified constants.
* The `r` of `PropThaM` (`StdAssump`) is not used: the constants depend on the chart, `a_+` and the Parabolic-cylinder facts only.

## Not formalised

Nothing of the lemma.  `corr_PC` (paper lem:cha-PCcoord) is a chart hypothesis.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Real intervalIntegral
open FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.Setting
open FormalResearch.JacobiEigenvectors.Engine (cas dot vrow)

section Block

lemma wm_block_extract (N : ℕ) (h η uc L ρ dm dp : ℝ) (hh : 0 < h) (hηpos : 0 < η) (hdm : 0 < dm) (hdmp : dm ≤ dp)
    (hLh : h * ((N : ℝ) + 1) = L) (huc1 : 2 * η < uc) (huc2 : uc + 2 * η < L) (hηh : h ≤ η)
    (hsm : dp * Real.sqrt h ≤ 1 / 20) (hρ : 1 / 2 ≤ ρ)
    (Z u : ℤ → ℝ) (hu : ∀ n : ℤ, u n = ((n : ℝ) + 1 / 2) * h)
    (hspc : ∀ n : ℤ, |u n - uc| ≤ 2 * η → |u (n + 1) - uc| ≤ 2 * η →
      dm * Real.sqrt h ≤ Z (n + 1) - Z n ∧ Z (n + 1) - Z n ≤ dp * Real.sqrt h)
    (hcol : ∀ n : ℤ, |u n - uc| ≤ 2 * η → |Z n| ≤ ρ → |u n - uc| < η / 4)
    (J2 : ℤ) (hJ2a : 0 ≤ J2) (hJ2b : J2 + 1 ≤ (N : ℤ)) (hJ2c : |u J2 - uc| ≤ 2 * η)
    (hJ2d : |u (J2 + 1) - uc| ≤ 2 * η) (hJ2e : Z J2 ≤ 0) (hJ2f : 0 < Z (J2 + 1))
    (hfar : ∀ n : ℤ, 0 ≤ n → n ≤ (N : ℤ) → 2 * η < |u n - uc| → ρ < |Z n|) :
    ∃ na nb : ℤ, WmBlock Z na nb ρ (dp * Real.sqrt h) ∧
      (Finset.Icc 0 (N : ℤ)).filter (fun n => |Z n| ≤ ρ) = Finset.Icc na nb ∧
      (∀ n : ℤ, na ≤ n → n ≤ nb → |u n - uc| < η / 4) := by
  have hs0 : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hdp : 0 < dp := lt_of_lt_of_le hdm hdmp
  have hdps : 0 < dp * Real.sqrt h := mul_pos hdp hs0
  have hdms : 0 < dm * Real.sqrt h := mul_pos hdm hs0
  -- the collar rows of the window
  let Wc : Finset ℤ := (Finset.Icc 0 (N : ℤ)).filter (fun n => |u n - uc| ≤ 2 * η ∧ |Z n| ≤ ρ)
  have hmemWc : ∀ n, n ∈ Wc ↔ (0 ≤ n ∧ n ≤ (N : ℤ)) ∧ |u n - uc| ≤ 2 * η ∧ |Z n| ≤ ρ := by
    intro n; simp only [Wc, Finset.mem_filter, Finset.mem_Icc]
  have hJ2mem : J2 ∈ Wc := by
    rw [hmemWc]
    refine ⟨⟨hJ2a, by omega⟩, hJ2c, ?_⟩
    have hsp := (hspc J2 hJ2c hJ2d).2
    rw [abs_le]
    constructor <;> linarith
  have hne : Wc.Nonempty := ⟨J2, hJ2mem⟩
  obtain ⟨na, hna⟩ : ∃ n, n = Wc.min' hne := ⟨_, rfl⟩
  obtain ⟨nb, hnb⟩ : ∃ n, n = Wc.max' hne := ⟨_, rfl⟩
  have hna_mem : na ∈ Wc := by rw [hna]; exact Finset.min'_mem Wc hne
  have hnb_mem : nb ∈ Wc := by rw [hnb]; exact Finset.max'_mem Wc hne
  have hna_le : ∀ n ∈ Wc, na ≤ n := fun n hn => by rw [hna]; exact Finset.min'_le Wc n hn
  have hnb_ge : ∀ n ∈ Wc, n ≤ nb := fun n hn => by rw [hnb]; exact Finset.le_max' Wc n hn
  have hnab : na ≤ nb := le_trans (hna_le J2 hJ2mem) (hnb_ge J2 hJ2mem)
  rw [hmemWc] at hna_mem hnb_mem
  obtain ⟨⟨hna0, hnaN⟩, hnacol, hnaZ⟩ := hna_mem
  obtain ⟨⟨hnb0, hnbN⟩, hnbcol, hnbZ⟩ := hnb_mem
  have hna_str : |u na - uc| < η / 4 := hcol na hnacol hnaZ
  have hnb_str : |u nb - uc| < η / 4 := hcol nb hnbcol hnbZ
  -- the block lies in the collar
  have hblk : ∀ n : ℤ, na ≤ n → n ≤ nb → |u n - uc| < η / 4 := by
    intro n h1 h2
    have c1 : (na : ℝ) ≤ n := by exact_mod_cast h1
    have c2 : (n : ℝ) ≤ nb := by exact_mod_cast h2
    have e1 : u na ≤ u n := by rw [hu, hu]; nlinarith
    have e2 : u n ≤ u nb := by rw [hu, hu]; nlinarith
    obtain ⟨l1, l2⟩ := abs_lt.mp hna_str
    obtain ⟨r1, r2⟩ := abs_lt.mp hnb_str
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hblk2 : ∀ n : ℤ, na ≤ n → n ≤ nb → |u n - uc| ≤ 2 * η := fun n h1 h2 =>
    le_trans (hblk n h1 h2).le (by linarith)
  have hsp_blk : ∀ n : ℤ, na ≤ n → n < nb →
      dm * Real.sqrt h ≤ Z (n + 1) - Z n ∧ Z (n + 1) - Z n ≤ dp * Real.sqrt h :=
    fun n h1 h2 => hspc n (hblk2 n h1 (by omega)) (hblk2 (n + 1) (by omega) (by omega))
  have hZmono : ∀ n : ℤ, na ≤ n → n < nb → Z n ≤ Z (n + 1) := fun n h1 h2 => by
    linarith [(hsp_blk n h1 h2).1]
  have hZblk : ∀ n : ℤ, na ≤ n → n ≤ nb → -ρ ≤ Z n ∧ Z n ≤ ρ := fun n h1 h2 => by
    have l1 := int_chain_mono hZmono na le_rfl n h1 h2
    have l2 := int_chain_mono hZmono n h1 nb h2 le_rfl
    have za := abs_le.mp hnaZ
    have zb := abs_le.mp hnbZ
    exact ⟨by linarith [za.1], by linarith [zb.2]⟩
  -- boundary rows: the row below the block is left of the window, the row above is right of it
  have hna1 : 1 ≤ na := by
    by_contra hc
    have h0 : na = 0 := by omega
    have hu0 : u na = h / 2 := by rw [h0, hu]; push_cast; ring
    rw [hu0] at hna_str
    have := abs_lt.mp hna_str
    linarith [this.1, this.2]
  have hnb1N : nb + 1 ≤ (N : ℤ) := by
    by_contra hc
    have h0 : nb = (N : ℤ) := by omega
    have hunb : u nb = L - h / 2 := by
      rw [hu, h0]; push_cast; linear_combination hLh
    rw [hunb] at hnb_str
    have := abs_lt.mp hnb_str
    linarith [this.1, this.2]
  have hnt_col : |u (nb + 1) - uc| ≤ 2 * η := by
    have e : u (nb + 1) = u nb + h := by rw [hu, hu]; push_cast; ring
    rw [e]
    have := abs_lt.mp hnb_str
    rw [abs_le]
    constructor <;> linarith [this.1, this.2]
  have hZt : ρ < |Z (nb + 1)| := by
    by_contra hc
    have hmem : nb + 1 ∈ Wc := (hmemWc _).2 ⟨⟨by omega, hnb1N⟩, hnt_col, not_lt.mp hc⟩
    have := hnb_ge (nb + 1) hmem
    omega
  have hsp_t := hspc nb (hblk2 nb hnab le_rfl) hnt_col
  have hZt' : ρ < Z (nb + 1) := by
    rcases lt_abs.mp hZt with h1 | h1
    · exact h1
    · linarith [(hZblk nb hnab le_rfl).1, hsp_t.1]
  have hnb' : ρ - dp * Real.sqrt h < Z nb := by linarith [hsp_t.2]
  have hna_col' : |u (na - 1) - uc| ≤ 2 * η := by
    have e : u (na - 1) = u na - h := by rw [hu, hu]; push_cast; ring
    rw [e]
    have := abs_lt.mp hna_str
    rw [abs_le]
    constructor <;> linarith [this.1, this.2]
  have hZb : ρ < |Z (na - 1)| := by
    by_contra hc
    have hmem : na - 1 ∈ Wc := (hmemWc _).2 ⟨⟨by omega, by omega⟩, hna_col', not_lt.mp hc⟩
    have := hna_le (na - 1) hmem
    omega
  have hna_nb : na - 1 + 1 = na := by ring
  have hsp_b := hspc (na - 1) hna_col' (by rw [hna_nb]; exact hnacol)
  rw [hna_nb] at hsp_b
  have hZb' : Z (na - 1) < -ρ := by
    rcases lt_abs.mp hZb with h1 | h1
    · linarith [(hZblk na le_rfl hnab).2, hsp_b.1]
    · linarith
  have hna' : Z na < -ρ + dp * Real.sqrt h := by linarith [hsp_b.2]
  -- the window is exactly the block
  have hW : (Finset.Icc 0 (N : ℤ)).filter (fun n => |Z n| ≤ ρ) = Finset.Icc na nb := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h0, hN⟩, hZn⟩
      by_cases hc : |u n - uc| ≤ 2 * η
      · have hmem : n ∈ Wc := (hmemWc n).2 ⟨⟨h0, hN⟩, hc, hZn⟩
        exact ⟨hna_le n hmem, hnb_ge n hmem⟩
      · exfalso
        have := hfar n h0 hN (not_le.mp hc)
        exact absurd hZn (not_le.mpr this)
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by omega, by omega⟩, abs_le.mpr (hZblk n h1 h2)⟩
  exact ⟨na, nb, ⟨hnab, fun n h1 h2 => ⟨lt_of_lt_of_le hdms (hsp_blk n h1 h2).1, (hsp_blk n h1 h2).2⟩, hZblk, hna', hnb'⟩, hW, hblk⟩

end Block

section Chart

variable {Par : Type*} [TopologicalSpace Par] {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ}
  {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}

lemma wm_kappa_pos' (a : ℝ) : 0 < kappaBal a := by
  rcases le_or_gt a 0 with ha | ha
  · rw [wm_kappa_eq1 ha]; exact wmK1_pos a
  · rw [wm_kappa_eq2 ha]; exact wmK2_pos a

/-- the window of the soft chart is a block of rows with the lattice facts of `lem:tha-win` (1). -/
lemma wm_ctx (CL : SoftEdgeChart Fz P m q U V Lm) (p : Par × ℝ) (hp : p ∈ P) (X : ℝ)
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) (N : ℕ) (hN : CL.N0 ≤ N)
    (hh1 : Fz.step N ≤ winH1 CL) (hηh : Fz.step N ≤ CL.η)
    (hsm : CL.dp * Real.sqrt (Fz.step N) ≤ 1 / 20)
    (hfar : ∀ n : ℤ, 0 ≤ n → n ≤ (N : ℤ) → 2 * CL.η < |uNode (Fz.step N) n - CL.uc p| →
      rhoWin (CL.aOf p X N) < |CL.Zof p X N n|) :
    ∃ na nb : ℤ, WmBlock (CL.Zof p X N) na nb (rhoWin (CL.aOf p X N)) (CL.dp * Real.sqrt (Fz.step N)) ∧
      softWindow CL p X N = Finset.Icc na nb ∧
      (∀ n : ℤ, na ≤ n → n ≤ nb → |uNode (Fz.step N) n - CL.uc p| < CL.η / 4) := by
  obtain ⟨-, hη, hdm, hdmp, -, -, -, -⟩ := CL.consts_pos
  have hh0 : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hρ := rhoWin_ge_half (CL.aOf p X N)
  have hLh : Fz.step N * ((N : ℝ) + 1) = Fz.L := by
    unfold SymbolFamily.step FormalResearch.JB.stepSize
    field_simp
  have hspc : ∀ n : ℤ, |uNode (Fz.step N) n - CL.uc p| ≤ 2 * CL.η →
      |uNode (Fz.step N) (n + 1) - CL.uc p| ≤ 2 * CL.η →
      CL.dm * Real.sqrt (Fz.step N) ≤ CL.Zof p X N (n + 1) - CL.Zof p X N n ∧
        CL.Zof p X N (n + 1) - CL.Zof p X N n ≤ CL.dp * Real.sqrt (Fz.step N) :=
    fun n h1 h2 => ⟨((win_row CL p hp X hX N hh0 hh1 n h1).1 h2).1,
      ((win_row CL p hp X hX N hh0 hh1 n h1).1 h2).2.1⟩
  have hcol : ∀ n : ℤ, |uNode (Fz.step N) n - CL.uc p| ≤ 2 * CL.η →
      |CL.Zof p X N n| ≤ rhoWin (CL.aOf p X N) →
      |uNode (Fz.step N) n - CL.uc p| < CL.η / 4 := fun n h1 h2 =>
    (win_row CL p hp X hX N hh0 hh1 n h1).2.2.2 (le_trans h2 (by linarith [ell_nonneg' (CL.aOf p X N)]))
  obtain ⟨-, -, -, -, hz1, hz2, -, -⟩ := CL.shape p hp X hX N hN
  obtain ⟨hj0, hjN, hc1, hc2⟩ := CL.switch_in p hp X hX N hN
  obtain ⟨-, hr⟩ := CL.ucη_in p hp
  obtain ⟨na, nb, hB, hW, hcl⟩ := wm_block_extract N (Fz.step N) CL.η (CL.uc p) Fz.L (rhoWin (CL.aOf p X N))
    CL.dm CL.dp hh0 hη hdm hdmp hLh (by linarith [(CL.ucη_in p hp).1]) hr hηh hsm hρ
    (fun n => CL.Zof p X N n) (fun n => uNode (Fz.step N) n) (fun n => rfl) hspc hcol
    ((CL.chain p X N).jj 2) hj0 hjN hc1 hc2 hz1 hz2 hfar
  exact ⟨na, nb, hB, hW, hcl⟩

section Rows

lemma wm_pcMinus0 (a : ℝ) : pcMinus U V a 0 = fun z => kappaBal a * U a (-z) := by
  funext z
  by_cases ha : a ≤ 0 <;> simp [pcMinus, ha, ut]

lemma wm_pcPlus0 (a : ℝ) : pcPlus U V a 0 = fun z => kappaBal a * U a z := by
  funext z
  by_cases ha : a ≤ 0 <;> simp [pcPlus, ha, ut]

lemma wm_pcSwap1 (a : ℝ) : pcSwap U V a 1 = fun z => -(kappaBal a * U a z) := by
  funext z
  by_cases ha : a ≤ 0 <;> simp [pcSwap, ha, ut]

/-- squares of the envelope-bounded functions: `0 <= f^2 <= C1^2` and `f^2` is `2 C1^2`-Lipschitz on `[-rho, rho]`. -/
lemma wm_sq_facts (f : ℝ → ℝ) (hfd : Differentiable ℝ f) (a ρ C1 : ℝ) (hC1 : 0 ≤ C1)
    (henv : ∀ z ∈ Set.Icc (-ρ) ρ, |f z| ≤ C1 * Mbal a z ∧ |deriv f z| ≤ C1 * Real.sqrt (k2 a z) * Mbal a z) :
    (∀ x ∈ Set.Icc (-ρ) ρ, f x ^ 2 ≤ C1 ^ 2) ∧
    (∀ δ : ℝ, ∀ x ∈ Set.Icc (-ρ) ρ, ∀ y ∈ Set.Icc (-ρ) ρ, y ≤ x → x - y ≤ δ →
      f x ^ 2 ≤ f y ^ 2 + (2 * C1 ^ 2) * δ) := by
  have hM1 : ∀ z, Mbal a z ≤ 1 := fun z => by
    have h1 := mbal_sq_le_one a z
    have h0 := Mbal_nonneg' a z
    nlinarith
  constructor
  · intro x hx
    have h1 := (henv x hx).1
    have h0 := Mbal_nonneg' a x
    have h2 : |f x| ≤ C1 := le_trans h1 (by nlinarith [hM1 x])
    calc f x ^ 2 = |f x| ^ 2 := (sq_abs _).symm
      _ ≤ C1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
  · intro δ x hx y hy hyx hd
    have hg : ∀ z, HasDerivAt (fun w => f w ^ 2) (2 * f z * deriv f z) z := fun z => by
      have := ((hfd z).hasDerivAt).pow 2
      convert this using 1
      simp
    have hbd : ∀ z ∈ Set.Icc (-ρ) ρ, ‖deriv (fun w => f w ^ 2) z‖ ≤ 2 * C1 ^ 2 := by
      intro z hz
      rw [(hg z).deriv, Real.norm_eq_abs]
      obtain ⟨e1, e2⟩ := henv z hz
      have hMz := Mbal_nonneg' a z
      have hs := Real.sqrt_nonneg (k2 a z)
      have hmk := wm_mbal_sq_sqrt a z
      calc |2 * f z * deriv f z| = 2 * (|f z| * |deriv f z|) := by rw [abs_mul, abs_mul]; simp; ring
        _ ≤ 2 * ((C1 * Mbal a z) * (C1 * Real.sqrt (k2 a z) * Mbal a z)) := by
            gcongr
        _ = 2 * C1 ^ 2 * (Mbal a z ^ 2 * Real.sqrt (k2 a z)) := by ring
        _ = 2 * C1 ^ 2 := by rw [hmk]; ring
    have hdiff : ∀ z ∈ Set.Icc (-ρ) ρ, DifferentiableAt ℝ (fun w => f w ^ 2) z :=
      fun z _ => (hg z).differentiableAt
    have := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbd (convex_Icc (-ρ) ρ) hy hx
    simp only [Real.norm_eq_abs] at this
    have h2 : f x ^ 2 - f y ^ 2 ≤ 2 * C1 ^ 2 * (x - y) := by
      calc f x ^ 2 - f y ^ 2 ≤ |f x ^ 2 - f y ^ 2| := le_abs_self _
        _ ≤ 2 * C1 ^ 2 * |x - y| := this
        _ = 2 * C1 ^ 2 * (x - y) := by rw [abs_of_nonneg (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 2 * C1 ^ 2)]

/-- the corrector error `|h B (sqrt h f')| <= h C_B C_1 C_Lambda M`. -/
lemma wm_err (h BB CB C1 CLm k2v Mv fp : ℝ) (hh : 0 < h) (hBB : |BB| ≤ CB) (hk : h * k2v ≤ CLm ^ 2)
    (hCL : 0 ≤ CLm) (hk2 : 0 ≤ k2v) (hfp : |fp| ≤ C1 * Real.sqrt k2v * Mv) (hC1 : 0 ≤ C1) (hM : 0 ≤ Mv) :
    |(h * BB) * (Real.sqrt h * fp)| ≤ h * (CB * C1 * CLm) * Mv := by
  have hCB : 0 ≤ CB := le_trans (abs_nonneg _) hBB
  have hs : Real.sqrt h * Real.sqrt k2v ≤ CLm := by
    rw [← Real.sqrt_mul hh.le]
    exact Real.sqrt_le_iff.mpr ⟨hCL, hk⟩
  have hsh := Real.sqrt_nonneg h
  have hsk := Real.sqrt_nonneg k2v
  calc |(h * BB) * (Real.sqrt h * fp)| = h * (|BB| * (Real.sqrt h * |fp|)) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hh, abs_of_nonneg hsh]; ring
    _ ≤ h * (CB * (Real.sqrt h * (C1 * Real.sqrt k2v * Mv))) := by
        gcongr
    _ = h * (CB * C1 * (Real.sqrt h * Real.sqrt k2v) * Mv) := by ring
    _ ≤ h * (CB * C1 * CLm * Mv) := by
        gcongr
    _ = h * (CB * C1 * CLm) * Mv := by ring

end Rows

section Claims

/-- `m_Omega = sum_Omega M_bal^2`. -/
def wmMass (CL : SoftEdgeChart Fz P m q U V Lm) (p : Par × ℝ) (X : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ softWindow CL p X N, Mbal (CL.aOf p X N) (CL.Zof p X N n) ^ 2

/-- the three half-window mass bounds at the worst cut `s = ± s_A` (each is monotone in the cut), in the normalisation `y = kappa U`:
`sum_{Z_n > s_A} y_1^2`, `sum_{Z_n <= -s_A} y_2^2` (`y_2(Z) = kappa U(a,-Z)`) and the corrected sequence `phi^{(1)}_2`. -/
def WmClaims (CL : SoftEdgeChart Fz P m q U V Lm) (p : Par × ℝ) (X : ℝ) (N : ℕ) (c : ℝ) : Prop :=
  c * wmMass CL p X N ≤ ∑ n ∈ (softWindow CL p X N).filter (fun n => wmCut (CL.aOf p X N) < CL.Zof p X N n),
      (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (CL.Zof p X N n)) ^ 2 ∧
    c * wmMass CL p X N ≤ ∑ n ∈ (softWindow CL p X N).filter (fun n => CL.Zof p X N n ≤ -wmCut (CL.aOf p X N)),
      (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-(CL.Zof p X N n))) ^ 2 ∧
    c * wmMass CL p X N ≤ ∑ n ∈ (softWindow CL p X N).filter (fun n => CL.Zof p X N n ≤ -wmCut (CL.aOf p X N)),
      ((CL.chain p X N).phi (Fz.step N) 0 2 n) ^ 2

lemma WmClaims.mono {CL : SoftEdgeChart Fz P m q U V Lm} {p : Par × ℝ} {X : ℝ} {N : ℕ} {c c' : ℝ}
    (h : WmClaims CL p X N c) (hc : c' ≤ c) (hm : 0 ≤ wmMass CL p X N) : WmClaims CL p X N c' := by
  obtain ⟨h1, h2, h3⟩ := h
  have := mul_le_mul_of_nonneg_right hc hm
  exact ⟨le_trans this h1, le_trans this h2, le_trans this h3⟩

lemma wmMass_nonneg (CL : SoftEdgeChart Fz P m q U V Lm) (p : Par × ℝ) (X : ℝ) (N : ℕ) : 0 ≤ wmMass CL p X N :=
  Finset.sum_nonneg (fun n _ => sq_nonneg _)

lemma wm_u_lt {h : ℝ} (hh : 0 < h) {n m : ℤ} (hnm : uNode h n < uNode h m) : n < m := by
  unfold uNode at hnm
  by_contra hc
  have : (m : ℝ) ≤ n := by exact_mod_cast not_lt.mp hc
  nlinarith

lemma wm_sqrt_small (dp ε h : ℝ) (hdp : 0 < dp) (hε : 0 < ε) (hh : h ≤ (ε / dp) ^ 2) : dp * Real.sqrt h ≤ ε := by
  have h1 : Real.sqrt h ≤ ε / dp := by
    calc Real.sqrt h ≤ Real.sqrt ((ε / dp) ^ 2) := Real.sqrt_le_sqrt hh
      _ = ε / dp := Real.sqrt_sq (by positivity)
  calc dp * Real.sqrt h ≤ dp * (ε / dp) := mul_le_mul_of_nonneg_left h1 hdp.le
    _ = ε := by field_simp

/-- the corrector decomposition: `sum phi^2 >= gm^2/2 sum f^2 - eps^2 mm`. -/
lemma wm_corr_lower (S : Finset ℤ) (φ f e M a : ℤ → ℝ) (gm ε mm : ℝ) (hgm : 0 ≤ gm)
    (hA : ∀ n ∈ S, gm ≤ a n) (hφ : ∀ n ∈ S, φ n = a n * f n + e n) (he : ∀ n ∈ S, |e n| ≤ ε * M n)
    (hM : ∑ n ∈ S, M n ^ 2 ≤ mm) :
    gm ^ 2 / 2 * ∑ n ∈ S, f n ^ 2 - ε ^ 2 * mm ≤ ∑ n ∈ S, φ n ^ 2 := by
  have hpt : ∀ n ∈ S, gm ^ 2 / 2 * f n ^ 2 - ε ^ 2 * M n ^ 2 ≤ φ n ^ 2 := by
    intro n hn
    rw [hφ n hn]
    have h1 := hA n hn
    have h2 : gm ^ 2 ≤ a n ^ 2 := pow_le_pow_left₀ hgm h1 2
    have h3 : e n ^ 2 ≤ (ε * M n) ^ 2 := by
      calc e n ^ 2 = |e n| ^ 2 := (sq_abs _).symm
        _ ≤ (ε * M n) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (he n hn) 2
    nlinarith [sq_nonneg (a n * f n + 2 * e n), mul_le_mul_of_nonneg_right h2 (sq_nonneg (f n))]
  calc gm ^ 2 / 2 * ∑ n ∈ S, f n ^ 2 - ε ^ 2 * mm ≤ gm ^ 2 / 2 * ∑ n ∈ S, f n ^ 2 - ε ^ 2 * ∑ n ∈ S, M n ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hM (sq_nonneg ε)]
    _ = ∑ n ∈ S, (gm ^ 2 / 2 * f n ^ 2 - ε ^ 2 * M n ^ 2) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ ∑ n ∈ S, φ n ^ 2 := Finset.sum_le_sum hpt

/-- the corrector decomposition, upper form: `sum phi^2 <= 2 K_A^2 sum f^2 + 2 eps^2 mm`. -/
lemma wm_corr_upper (S : Finset ℤ) (φ f e M a : ℤ → ℝ) (KA ε mm : ℝ)
    (hA : ∀ n ∈ S, |a n| ≤ KA) (hφ : ∀ n ∈ S, φ n = a n * f n + e n) (he : ∀ n ∈ S, |e n| ≤ ε * M n)
    (hM : ∑ n ∈ S, M n ^ 2 ≤ mm) :
    ∑ n ∈ S, φ n ^ 2 ≤ 2 * KA ^ 2 * ∑ n ∈ S, f n ^ 2 + 2 * ε ^ 2 * mm := by
  have hpt : ∀ n ∈ S, φ n ^ 2 ≤ 2 * KA ^ 2 * f n ^ 2 + 2 * ε ^ 2 * M n ^ 2 := by
    intro n hn
    rw [hφ n hn]
    have h2 : a n ^ 2 ≤ KA ^ 2 := by
      calc a n ^ 2 = |a n| ^ 2 := (sq_abs _).symm
        _ ≤ KA ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hA n hn) 2
    have h3 : e n ^ 2 ≤ (ε * M n) ^ 2 := by
      calc e n ^ 2 = |e n| ^ 2 := (sq_abs _).symm
        _ ≤ (ε * M n) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (he n hn) 2
    nlinarith [sq_nonneg (a n * f n - e n), mul_le_mul_of_nonneg_right h2 (sq_nonneg (f n))]
  calc ∑ n ∈ S, φ n ^ 2 ≤ ∑ n ∈ S, (2 * KA ^ 2 * f n ^ 2 + 2 * ε ^ 2 * M n ^ 2) := Finset.sum_le_sum hpt
    _ = 2 * KA ^ 2 * ∑ n ∈ S, f n ^ 2 + 2 * ε ^ 2 * ∑ n ∈ S, M n ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * KA ^ 2 * ∑ n ∈ S, f n ^ 2 + 2 * ε ^ 2 * mm := by
        nlinarith [mul_le_mul_of_nonneg_left hM (by positivity : (0 : ℝ) ≤ 2 * ε ^ 2)]

end Claims

section Rows2

/-- the patch-2 comparison sequence is `A f(Z) + (h B) (sqrt h f'(Z))` with the `-` pair of `U` (`wf2_eq`). -/
lemma wm_phi2_decomp (CL : SoftEdgeChart Fz P m q U V Lm) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N) {n : ℤ}
    (hn1 : (CL.chain p X N).jj 1 ≤ n) (hn2 : n ≤ (CL.chain p X N).NR + 1) (α : Fin 2) :
    (CL.chain p X N).phi (Fz.step N) α 2 n =
      (CL.chain p X N).AA 2 (uNode (Fz.step N) n) (Fz.step N) * pcMinus U V (CL.aOf p X N) α (CL.Zof p X N n) +
      (Fz.step N * (CL.chain p X N).BB 2 (uNode (Fz.step N) n) (Fz.step N)) *
        (Real.sqrt (Fz.step N) * deriv (pcMinus U V (CL.aOf p X N) α) (CL.Zof p X N n)) := by
  rw [SoftEdgeChart.phi_eq_dot, CL.wf2_eq p hp X hX N hN n (Finset.mem_Icc.mpr ⟨hn1, hn2⟩) α]
  simp [dot, vrow, SoftEdgeCore.aOf, SoftEdgeCore.Zof]

/-- the patch-3 comparison sequence (`wf3_eq`, `shared_PC`: patches 2 and 3 share the corrector rows). -/
lemma wm_phi3_decomp (CL : SoftEdgeChart Fz P m q U V Lm) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N) {n : ℤ}
    (hn1 : (CL.chain p X N).jj 2 ≤ n) (hn2 : n ≤ (CL.chain p X N).NR + 1) (α : Fin 2) :
    (CL.chain p X N).phi (Fz.step N) α 3 n =
      (CL.chain p X N).AA 2 (uNode (Fz.step N) n) (Fz.step N) * pcSwap U V (CL.aOf p X N) α (CL.Zof p X N n) +
      (Fz.step N * (CL.chain p X N).BB 2 (uNode (Fz.step N) n) (Fz.step N)) *
        (Real.sqrt (Fz.step N) * deriv (pcSwap U V (CL.aOf p X N) α) (CL.Zof p X N n)) := by
  obtain ⟨-, -, -, -, -, -, -, -, hAA, hBB⟩ := CL.shared_PC p hp X hX N hN
  rw [SoftEdgeChart.phi_eq_dot, CL.wf3_eq p hp X hX N hN n (Finset.mem_Icc.mpr ⟨hn1, hn2⟩) α, hAA, hBB]
  simp [dot, vrow, SoftEdgeCore.aOf, SoftEdgeCore.Zof]

end Rows2

section SmallBranch

lemma wm_row_loc (CL : SoftEdgeChart Fz P m q U V Lm) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N) {n : ℤ}
    (hcol : |uNode (Fz.step N) n - CL.uc p| < CL.η / 4) :
    (CL.chain p X N).jj 1 < n ∧ n ≤ (CL.chain p X N).NR := by
  obtain ⟨-, -, hj1a, -, -, -, -, hNR2⟩ := CL.shape p hp X hX N hN
  have hη := CL.consts_pos.2.1
  have hh0 : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  obtain ⟨l1, l2⟩ := abs_lt.mp hcol
  constructor
  · exact wm_u_lt hh0 (by linarith)
  · by_contra hc
    have : (CL.chain p X N).NR + 1 ≤ n := by omega
    have h1 : uNode (Fz.step N) ((CL.chain p X N).NR + 1) ≤ uNode (Fz.step N) n := by
      unfold uNode
      have : (((CL.chain p X N).NR + 1 : ℤ) : ℝ) ≤ n := by exact_mod_cast this
      nlinarith
    linarith

/-- numerical thresholds are fine: the constants of `Claim 1`, `Claim 2` in the branch `h A <= delta_0`. -/
def wmDelta (c1 K1 dp : ℝ) : ℝ := min 1 ((c1 / (32 * K1 * dp)) ^ 2)

lemma wmDelta_pos {c1 K1 dp : ℝ} (hc1 : 0 < c1) (hK1 : 0 < K1) (hdp : 0 < dp) : 0 < wmDelta c1 K1 dp := by
  unfold wmDelta
  exact lt_min one_pos (by positivity)

/-- the envelope bounds of `lem:tha-win` (3) on `|z| <= rho`, for the two functions `kappa U(a,z)` and `kappa U(a,-z)`, in the form needed by `wm_sq_facts`. -/
lemma wm_env_two {cPC CPC : ℝ} (pc : ParabolicCylinderFacts U V cPC CPC) (aplus a : ℝ) (haplus : a ≤ aplus) (z : ℝ)
    (hz : |z| ≤ rhoWin a) :
    (|kappaBal a * U a z| ≤ winCB CPC aplus * Mbal a z ∧
      |deriv (fun w => kappaBal a * U a w) z| ≤ winCB CPC aplus * Real.sqrt (k2 a z) * Mbal a z) ∧
    (|kappaBal a * U a (-z)| ≤ winCB CPC aplus * Mbal a z ∧
      |deriv (fun w => kappaBal a * U a (-w)) z| ≤ winCB CPC aplus * Real.sqrt (k2 a z) * Mbal a z) := by
  have hz' : |z| ≤ winR a := le_trans hz (by unfold winR; linarith [ell_nonneg' a])
  obtain ⟨⟨p1, p2⟩, ⟨m1, m2⟩⟩ := envelope_conj3 pc aplus a z haplus hz' 0
  rw [wm_pcPlus0] at p1 p2
  rw [wm_pcMinus0] at m1 m2
  exact ⟨⟨p1, p2⟩, ⟨m1, m2⟩⟩

lemma wm_diff_two {cPC CPC : ℝ} (pc : ParabolicCylinderFacts U V cPC CPC) (a : ℝ) :
    Differentiable ℝ (fun w => kappaBal a * U a w) ∧ Differentiable ℝ (fun w => kappaBal a * U a (-w)) := by
  have hd : Differentiable ℝ (U a) := (wm_slice_smooth pc a).differentiable (by simp)
  exact ⟨hd.const_mul _, (hd.comp differentiable_neg).const_mul _⟩

lemma wm_gap (c1 K1 δ ρ t : ℝ) (hc1 : 0 < c1) (hK1 : 0 < K1) (hK : c1 ≤ K1 * (ρ - t))
    (hS : δ ≤ c1 / (24 * K1)) : 2 * δ < ρ - t := by
  by_contra hc
  push Not at hc
  have h1 : K1 * (ρ - t) ≤ K1 * (2 * δ) := mul_le_mul_of_nonneg_left hc hK1.le
  have h2 : K1 * δ ≤ c1 / 24 := by
    calc K1 * δ ≤ K1 * (c1 / (24 * K1)) := mul_le_mul_of_nonneg_left hS hK1.le
      _ = c1 / 24 := by field_simp
  linarith

lemma wm_err_bound (c1 K1 dp h δ ρ A : ℝ) (hc1 : 0 < c1) (hK1 : 0 < K1) (hdp : 0 < dp)
    (hδ : δ = dp * Real.sqrt h) (hS : δ ≤ c1 / (24 * K1)) (hAS : Real.sqrt A * Real.sqrt h ≤ c1 / (32 * K1 * dp))
    (hρle : ρ ≤ 2 * Real.sqrt A + 1) : 4 * K1 * δ * ρ + 2 * K1 * δ ≤ c1 / 2 := by
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have h1 : 4 * K1 * δ * ρ ≤ 4 * K1 * δ * (2 * Real.sqrt A + 1) :=
    mul_le_mul_of_nonneg_left hρle (by positivity)
  have h2 : 4 * K1 * δ * (2 * Real.sqrt A + 1) =
      8 * K1 * dp * (Real.sqrt A * Real.sqrt h) + 4 * K1 * δ := by
    rw [hδ]; ring
  have h3 : 8 * K1 * dp * (Real.sqrt A * Real.sqrt h) ≤ c1 / 4 := by
    calc 8 * K1 * dp * (Real.sqrt A * Real.sqrt h) ≤ 8 * K1 * dp * (c1 / (32 * K1 * dp)) :=
          mul_le_mul_of_nonneg_left hAS (by positivity)
      _ = c1 / 4 := by field_simp; ring
  have h4 : K1 * δ ≤ c1 / 24 := by
    calc K1 * δ ≤ K1 * (c1 / (24 * K1)) := mul_le_mul_of_nonneg_left hS hK1.le
      _ = c1 / 24 := by field_simp
  nlinarith

/-- the abstract core of Step 2: from the continuous mass `c1` and the lattice, `c1/(2δ) <= sum` for the two half-windows. -/
lemma wm_step2_abstract {Z : ℤ → ℝ} {na nb : ℤ} {ρ δ t c1 K1 : ℝ} (hB : WmBlock Z na nb ρ δ) (hδ : 0 < δ)
    {g1 g2 : ℝ → ℝ} (hg10 : ∀ x, 0 ≤ g1 x) (hg20 : ∀ x, 0 ≤ g2 x)
    (hint1 : ∀ x y : ℝ, IntervalIntegrable g1 MeasureTheory.volume x y)
    (hint2 : ∀ x y : ℝ, IntervalIntegrable g2 MeasureTheory.volume x y) (hK1 : 0 ≤ K1)
    (hg1B : ∀ x ∈ Set.Icc (-ρ) ρ, g1 x ≤ K1) (hg2B : ∀ x ∈ Set.Icc (-ρ) ρ, g2 x ≤ K1)
    (hg1L : ∀ x ∈ Set.Icc (-ρ) ρ, ∀ y ∈ Set.Icc (-ρ) ρ, y ≤ x → x - y ≤ δ → g1 x ≤ g1 y + (2 * K1) * δ)
    (hg2L : ∀ x ∈ Set.Icc (-ρ) ρ, ∀ y ∈ Set.Icc (-ρ) ρ, y ≤ x → x - y ≤ δ → g2 x ≤ g2 y + (2 * K1) * δ)
    (ht1 : -ρ + δ ≤ t) (ht0 : 0 ≤ t) (ht2 : t + 2 * δ < ρ) (hρ : 1 / 2 ≤ ρ) (hδ20 : δ ≤ 1 / 20)
    (hneg : (∫ x in (-ρ)..(-t), g2 x) = ∫ x in t..ρ, g1 x) (hcI : c1 ≤ ∫ x in t..ρ, g1 x)
    (herr : 4 * K1 * δ * ρ + 2 * K1 * δ ≤ c1 / 2) :
    c1 / (2 * δ) ≤ ∑ n ∈ (Finset.Icc na nb).filter (fun n => t < Z n), g1 (Z n) ∧
      c1 / (2 * δ) ≤ ∑ n ∈ (Finset.Icc na nb).filter (fun n => Z n ≤ -t), g2 (Z n) := by
  have hlow1 := wm_lower_U hB hδ hg10 hint1 (B := K1) (D := 2 * K1) (by positivity) hg1B hg1L ht1 ht2
  have hlow2 := wm_lower_L hB hδ hg20 hint2 (B := K1) (D := 2 * K1) (by positivity) hg2B hg2L
    (t := -t) (by linarith) (by linarith)
  rw [hneg] at hlow2
  constructor
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [hlow1, hcI, herr]
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [hlow2, hcI, herr]

lemma winCLam_nonneg (CL : SoftEdgeChart Fz P m q U V Lm) : 0 ≤ winCLam CL := by
  have h1 := winB_nonneg CL
  have h2 := CL.consts_pos2.1
  have h3 : 0 ≤ winKq q := by unfold winKq; positivity
  unfold winCLam
  nlinarith [sq_nonneg (winB CL), mul_nonneg (add_nonneg h3 zero_le_one) h2]

/-- the per-row facts of a window row inside the collar. -/
lemma wm_rowfacts (CL : SoftEdgeChart Fz P m q U V Lm) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N) (hh1 : Fz.step N ≤ winH1 CL) {n : ℤ}
    (hn : n ∈ softWindow CL p X N) (hcol : |uNode (Fz.step N) n - CL.uc p| < CL.η / 4) :
    0 ≤ n ∧ n ≤ (N : ℤ) ∧ |CL.Zof p X N n| ≤ rhoWin (CL.aOf p X N) ∧
      (CL.chain p X N).jj 1 < n ∧ n ≤ (CL.chain p X N).NR ∧
      |uNode (Fz.step N) n - CL.uc p| ≤ 2 * CL.η ∧
      Fz.step N * k2 (CL.aOf p X N) (CL.Zof p X N n) ≤ winCLam CL ^ 2 := by
  have hη := CL.consts_pos.2.1
  have hh0 : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hmem : n ∈ rowsOf N ∧ |CL.Zof p X N n| ≤ rhoWin (CL.aOf p X N) := by
    unfold softWindow at hn
    exact Finset.mem_filter.mp hn
  obtain ⟨hr, hZ⟩ := hmem
  have hr' : 0 ≤ n ∧ n ≤ (N : ℤ) := by
    unfold rowsOf at hr
    exact Finset.mem_Icc.mp hr
  have hc2 : |uNode (Fz.step N) n - CL.uc p| ≤ 2 * CL.η := by linarith
  obtain ⟨l1, l2⟩ := wm_row_loc CL hp hX hN hcol
  exact ⟨hr'.1, hr'.2, hZ, l1, l2, hc2, (win_row CL p hp X hX N hh0 hh1 n hc2).2.1⟩

/-- the patch-2 corrector rows: `gm <= A` and `|phi^{(1)}_2 - A y_2| <= h E M` on a collar row. -/
lemma wm_row2 {cPC CPC : ℝ} (pc : ParabolicCylinderFacts U V cPC CPC) (CL : SoftEdgeChart Fz P m q U V Lm) (aplus : ℝ)
    {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N)
    (haplus : CL.aOf p X N ≤ aplus) (hh1 : Fz.step N ≤ winH1 CL) {n : ℤ}
    (hn : n ∈ softWindow CL p X N) (hcol : |uNode (Fz.step N) n - CL.uc p| < CL.η / 4) :
    CL.gm ≤ (CL.chain p X N).AA 2 (uNode (Fz.step N) n) (Fz.step N) ∧
      |(CL.chain p X N).phi (Fz.step N) 0 2 n -
          (CL.chain p X N).AA 2 (uNode (Fz.step N) n) (Fz.step N) *
            (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-(CL.Zof p X N n)))| ≤
        Fz.step N * (CL.CBc * winCB CPC aplus * winCLam CL) * Mbal (CL.aOf p X N) (CL.Zof p X N n) := by
  have hCPC : 0 < CPC := lt_of_lt_of_le pc.cPC_pos pc.cPC_le
  have hC1 : 0 < winCB CPC aplus := by unfold winCB; positivity
  have hh0 : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  obtain ⟨h0, hNn, hZ, hj1, hNR, hc2, hkz⟩ := wm_rowfacts CL hp hX hN hh1 hn hcol
  obtain ⟨hAA, hBB⟩ := CL.corr_PC p hp X hX N hN n h0 hNn hc2
  have hdec := wm_phi2_decomp CL hp hX hN (n := n) hj1.le (by omega) 0
  have hfp := (wm_env_two pc aplus (CL.aOf p X N) haplus (CL.Zof p X N n) hZ).2.2
  have hfe : pcMinus U V (CL.aOf p X N) 0 (CL.Zof p X N n) =
      kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-(CL.Zof p X N n)) := by
    rw [wm_pcMinus0]
  have hderiv : deriv (pcMinus U V (CL.aOf p X N) 0) (CL.Zof p X N n) =
      deriv (fun w => kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-w)) (CL.Zof p X N n) := by
    rw [wm_pcMinus0]
  refine ⟨hAA, ?_⟩
  rw [hdec, hfe, add_sub_cancel_left, hderiv]
  exact wm_err _ _ _ _ _ _ _ _ hh0 hBB hkz (winCLam_nonneg CL) (le_trans zero_le_one (win_k2_ge_one _ _)) hfp hC1.le
    (Mbal_nonneg' _ _)

/-- Step 2, conjuncts 1 and 2 (uncorrected `U`): the Riemann transfer of the continuous mass. -/
lemma wm_small12 {cPC CPC : ℝ} (pc : ParabolicCylinderFacts U V cPC CPC) (CL : SoftEdgeChart Fz P m q U V Lm) (aplus : ℝ)
    {c1 : ℝ} (hc1pos : 0 < c1)
    (hc1 : ∀ a : ℝ, a ≤ aplus → ∀ s : ℝ, |s| ≤ wmCut a → c1 ≤ ∫ z in s..(wmRho a), (kappaBal a * U a z) ^ 2)
    {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N)
    (haplus : CL.aOf p X N ≤ aplus)
    (hs1 : Fz.step N ≤ winH1 CL) (hs2 : Fz.step N ≤ CL.η) (hs3 : Fz.step N ≤ farThr CL)
    (hsm0 : CL.dp * Real.sqrt (Fz.step N) ≤ 1 / (2 * max 1 aplus) / 10)
    (hS5 : CL.dp * Real.sqrt (Fz.step N) ≤ c1 / (24 * winCB CPC aplus ^ 2))
    (hAsm : Fz.step N * max (-CL.aOf p X N) 0 ≤ wmDelta c1 (winCB CPC aplus ^ 2) CL.dp) :
    c1 * CL.dm / (22 * CL.dp) * wmMass CL p X N ≤
        ∑ n ∈ (softWindow CL p X N).filter (fun n => wmCut (CL.aOf p X N) < CL.Zof p X N n),
          (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (CL.Zof p X N n)) ^ 2 ∧
      c1 * CL.dm / (22 * CL.dp) * wmMass CL p X N ≤
        ∑ n ∈ (softWindow CL p X N).filter (fun n => CL.Zof p X N n ≤ -wmCut (CL.aOf p X N)),
          (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-(CL.Zof p X N n))) ^ 2 := by
  obtain ⟨-, hη, hdm, hdmp, -, -, -, -⟩ := CL.consts_pos
  have hdp : 0 < CL.dp := lt_of_lt_of_le hdm hdmp
  have hCPC : 0 < CPC := lt_of_lt_of_le pc.cPC_pos pc.cPC_le
  have hC1pos : 0 < winCB CPC aplus := by unfold winCB; positivity
  have hc2 : 0 < c1 * CL.dm / (22 * CL.dp) := by positivity
  have hh0 : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hM1 : 1 ≤ max 1 aplus := le_max_left _ _
  have hsm20 : CL.dp * Real.sqrt (Fz.step N) ≤ 1 / 20 := by
    refine le_trans hsm0 ?_
    have : 1 / (2 * max 1 aplus) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hfarN : ∀ n : ℤ, 0 ≤ n → n ≤ (N : ℤ) → 2 * CL.η < |uNode (Fz.step N) n - CL.uc p| →
      rhoWin (CL.aOf p X N) < |CL.Zof p X N n| :=
    fun n h0 hN' hfn => farChart CL p hp X hX N hs3 n h0 hN' hfn
  obtain ⟨na, nb, hB, hW, hcl⟩ := wm_ctx CL p hp X hX N hN hs1 hs2 hsm20 hfarN
  have hsqh : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
  have hδ : 0 < CL.dp * Real.sqrt (Fz.step N) := mul_pos hdp hsqh
  have hmm : wmMass CL p X N ≤ 11 / (CL.dm * Real.sqrt (Fz.step N)) := by
    have := (win_chart_sums CL p hp X hX N hN aplus hs1 hs2 hsm0 haplus hfarN).1
    rw [rpow_neg_half _ hh0.le] at this
    calc wmMass CL p X N ≤ 11 / CL.dm * (Real.sqrt (Fz.step N))⁻¹ := this
      _ = 11 / (CL.dm * Real.sqrt (Fz.step N)) := by field_simp
  have hρ12 := rhoWin_ge_half (CL.aOf p X N)
  have henv : ∀ z ∈ Set.Icc (-rhoWin (CL.aOf p X N)) (rhoWin (CL.aOf p X N)),
      (|kappaBal (CL.aOf p X N) * U (CL.aOf p X N) z| ≤ winCB CPC aplus * Mbal (CL.aOf p X N) z ∧
        |deriv (fun w => kappaBal (CL.aOf p X N) * U (CL.aOf p X N) w) z| ≤
          winCB CPC aplus * Real.sqrt (k2 (CL.aOf p X N) z) * Mbal (CL.aOf p X N) z) ∧
      (|kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-z)| ≤ winCB CPC aplus * Mbal (CL.aOf p X N) z ∧
        |deriv (fun w => kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-w)) z| ≤
          winCB CPC aplus * Real.sqrt (k2 (CL.aOf p X N) z) * Mbal (CL.aOf p X N) z) :=
    fun z hz => wm_env_two pc aplus _ haplus z (abs_le.mpr hz)
  obtain ⟨hd1, hd2⟩ := wm_diff_two pc (CL.aOf p X N)
  obtain ⟨hg1B, hg1L⟩ := wm_sq_facts _ hd1 _ (rhoWin (CL.aOf p X N)) _ hC1pos.le (fun z hz => (henv z hz).1)
  obtain ⟨hg2B, hg2L⟩ := wm_sq_facts _ hd2 _ (rhoWin (CL.aOf p X N)) _ hC1pos.le (fun z hz => (henv z hz).2)
  have hU : Continuous (U (CL.aOf p X N)) := (wm_slice_smooth pc _).continuous
  have hint1 : ∀ x y : ℝ, IntervalIntegrable (fun z => (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) z) ^ 2)
      MeasureTheory.volume x y :=
    fun x y => (by fun_prop : Continuous fun z => (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) z) ^ 2).intervalIntegrable _ _
  have hint2 : ∀ x y : ℝ, IntervalIntegrable (fun z => (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-z)) ^ 2)
      MeasureTheory.volume x y :=
    fun x y => (by fun_prop : Continuous fun z => (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-z)) ^ 2).intervalIntegrable _ _
  have ht0 : 0 ≤ wmCut (CL.aOf p X N) :=
    add_nonneg (Real.sqrt_nonneg _) (div_nonneg (ell_nonneg' _) (by norm_num))
  have htρ : wmCut (CL.aOf p X N) ≤ rhoWin (CL.aOf p X N) := by
    unfold wmCut rhoWin
    linarith [Real.sqrt_nonneg (max (-CL.aOf p X N) 0), ell_nonneg' (CL.aOf p X N)]
  have hcI : c1 ≤ ∫ z in (wmCut (CL.aOf p X N))..(rhoWin (CL.aOf p X N)),
      (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) z) ^ 2 :=
    hc1 _ haplus _ (by rw [abs_of_nonneg ht0])
  have hbdI := wm_int_le _ (winCB CPC aplus ^ 2) (wmCut (CL.aOf p X N)) (rhoWin (CL.aOf p X N)) htρ hint1
    (fun x hx => hg1B x ⟨by linarith [hx.1], hx.2⟩)
  have hρt := wm_gap c1 (winCB CPC aplus ^ 2) _ _ _ hc1pos (by positivity) (le_trans hcI hbdI) hS5
  have hA0 : 0 ≤ max (-CL.aOf p X N) 0 := le_max_right _ _
  have hAS : Real.sqrt (max (-CL.aOf p X N) 0) * Real.sqrt (Fz.step N) ≤
      c1 / (32 * winCB CPC aplus ^ 2 * CL.dp) := by
    rw [← Real.sqrt_mul hA0]
    have h1 : max (-CL.aOf p X N) 0 * Fz.step N ≤ (c1 / (32 * winCB CPC aplus ^ 2 * CL.dp)) ^ 2 := by
      have := le_trans hAsm (min_le_right _ _)
      linarith [mul_comm (max (-CL.aOf p X N) 0) (Fz.step N)]
    calc Real.sqrt (max (-CL.aOf p X N) 0 * Fz.step N) ≤ Real.sqrt ((c1 / (32 * winCB CPC aplus ^ 2 * CL.dp)) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = c1 / (32 * winCB CPC aplus ^ 2 * CL.dp) := Real.sqrt_sq (by positivity)
  have hρle : rhoWin (CL.aOf p X N) ≤ 2 * Real.sqrt (max (-CL.aOf p X N) 0) + 1 := by
    unfold rhoWin
    linarith [wm_ell_le_one (CL.aOf p X N)]
  have herr := wm_err_bound c1 (winCB CPC aplus ^ 2) CL.dp (Fz.step N) _ _ _ hc1pos (by positivity) hdp rfl hS5 hAS hρle
  have hneg : (∫ x in (-rhoWin (CL.aOf p X N))..(-wmCut (CL.aOf p X N)),
      (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-x)) ^ 2) =
      ∫ z in (wmCut (CL.aOf p X N))..(rhoWin (CL.aOf p X N)), (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) z) ^ 2 := by
    have := intervalIntegral.integral_comp_neg (a := -rhoWin (CL.aOf p X N)) (b := -wmCut (CL.aOf p X N))
      (fun z => (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) z) ^ 2)
    simpa using this
  obtain ⟨hsum1, hsum2⟩ := wm_step2_abstract hB hδ (fun x => sq_nonneg _) (fun x => sq_nonneg _) hint1 hint2
    (by positivity) hg1B hg2B (fun x hx y hy hyx hd => by simpa using hg1L _ x hx y hy hyx hd)
    (fun x hx y hy hyx hd => by simpa using hg2L _ x hx y hy hyx hd)
    (by linarith) ht0 (by linarith) hρ12 hsm20 hneg hcI herr
  have hc2mm : c1 * CL.dm / (22 * CL.dp) * wmMass CL p X N ≤ c1 / (2 * (CL.dp * Real.sqrt (Fz.step N))) := by
    calc c1 * CL.dm / (22 * CL.dp) * wmMass CL p X N ≤
          c1 * CL.dm / (22 * CL.dp) * (11 / (CL.dm * Real.sqrt (Fz.step N))) :=
          mul_le_mul_of_nonneg_left hmm hc2.le
      _ = c1 / (2 * (CL.dp * Real.sqrt (Fz.step N))) := by field_simp; ring
  rw [hW]
  exact ⟨le_trans hc2mm hsum1, le_trans hc2mm hsum2⟩

/-- Step 2, conjunct 3: the corrector step (`g_- / 2 <= A^{[m]}`, `|B^{[m]}| <= C_B`). -/
lemma wm_small3 {cPC CPC : ℝ} (pc : ParabolicCylinderFacts U V cPC CPC) (CL : SoftEdgeChart Fz P m q U V Lm) (aplus : ℝ)
    {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N)
    (haplus : CL.aOf p X N ≤ aplus)
    (hs1 : Fz.step N ≤ winH1 CL) (hs2 : Fz.step N ≤ CL.η) (hs3 : Fz.step N ≤ farThr CL)
    (hsm20 : CL.dp * Real.sqrt (Fz.step N) ≤ 1 / 20) {c2 : ℝ}
    (hclaim2 : c2 * wmMass CL p X N ≤
        ∑ n ∈ (softWindow CL p X N).filter (fun n => CL.Zof p X N n ≤ -wmCut (CL.aOf p X N)),
          (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-(CL.Zof p X N n))) ^ 2)
    (hsq : (Fz.step N * (CL.CBc * winCB CPC aplus * winCLam CL)) ^ 2 ≤ CL.gm ^ 2 * c2 / 4) :
    CL.gm ^ 2 * c2 / 4 * wmMass CL p X N ≤
      ∑ n ∈ (softWindow CL p X N).filter (fun n => CL.Zof p X N n ≤ -wmCut (CL.aOf p X N)),
        ((CL.chain p X N).phi (Fz.step N) 0 2 n) ^ 2 := by
  have hgm : 0 < CL.gm := CL.consts_pos4.1
  have hfarN : ∀ n : ℤ, 0 ≤ n → n ≤ (N : ℤ) → 2 * CL.η < |uNode (Fz.step N) n - CL.uc p| →
      rhoWin (CL.aOf p X N) < |CL.Zof p X N n| :=
    fun n h0 hN' hfn => farChart CL p hp X hX N hs3 n h0 hN' hfn
  obtain ⟨na, nb, hB, hW, hcl⟩ := wm_ctx CL p hp X hX N hN hs1 hs2 hsm20 hfarN
  have hmm0 := wmMass_nonneg CL p X N
  have hmemS : ∀ n ∈ (Finset.Icc na nb).filter (fun n => CL.Zof p X N n ≤ -wmCut (CL.aOf p X N)),
      n ∈ softWindow CL p X N ∧ |uNode (Fz.step N) n - CL.uc p| < CL.η / 4 := by
    intro n hn
    obtain ⟨h1, -⟩ := Finset.mem_filter.mp hn
    exact ⟨by rw [hW]; exact h1, hcl n (Finset.mem_Icc.mp h1).1 (Finset.mem_Icc.mp h1).2⟩
  have hcorr := wm_corr_lower ((Finset.Icc na nb).filter (fun n => CL.Zof p X N n ≤ -wmCut (CL.aOf p X N)))
    (fun n => (CL.chain p X N).phi (Fz.step N) 0 2 n)
    (fun n => kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-(CL.Zof p X N n)))
    (fun n => (CL.chain p X N).phi (Fz.step N) 0 2 n -
      (CL.chain p X N).AA 2 (uNode (Fz.step N) n) (Fz.step N) *
        (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-(CL.Zof p X N n))))
    (fun n => Mbal (CL.aOf p X N) (CL.Zof p X N n))
    (fun n => (CL.chain p X N).AA 2 (uNode (Fz.step N) n) (Fz.step N))
    CL.gm (Fz.step N * (CL.CBc * winCB CPC aplus * winCLam CL)) (wmMass CL p X N) hgm.le
    (fun n hn => (wm_row2 pc CL aplus hp hX hN haplus hs1 (hmemS n hn).1 (hmemS n hn).2).1)
    (fun n _ => by ring)
    (fun n hn => (wm_row2 pc CL aplus hp hX hN haplus hs1 (hmemS n hn).1 (hmemS n hn).2).2)
    (by
      unfold wmMass
      rw [← hW]
      exact Finset.sum_le_sum_of_subset_of_nonneg (by rw [hW]; exact Finset.filter_subset _ _)
        (fun n _ _ => sq_nonneg _))
  have hclaim2' : c2 * wmMass CL p X N ≤ ∑ n ∈ (Finset.Icc na nb).filter
      (fun n => CL.Zof p X N n ≤ -wmCut (CL.aOf p X N)),
      (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-(CL.Zof p X N n))) ^ 2 := by
    rw [hW] at hclaim2; exact hclaim2
  rw [hW]
  have h1 := mul_le_mul_of_nonneg_left hclaim2' (by positivity : (0 : ℝ) ≤ CL.gm ^ 2 / 2)
  have h2 := mul_le_mul_of_nonneg_right hsq hmm0
  nlinarith [hcorr, h1, h2]

/-- **Step 2 of lem:tha-M**, all three conjuncts, in the branch `h A <= delta_0` (`tilde mu <= delta`). -/
lemma wm_small {cPC CPC : ℝ} (pc : ParabolicCylinderFacts U V cPC CPC) (CL : SoftEdgeChart Fz P m q U V Lm) (aplus : ℝ)
    {c1 : ℝ} (hc1pos : 0 < c1)
    (hc1 : ∀ a : ℝ, a ≤ aplus → ∀ s : ℝ, |s| ≤ wmCut a → c1 ≤ ∫ z in s..(wmRho a), (kappaBal a * U a z) ^ 2) :
    ∃ c h0 : ℝ, 0 < c ∧ 0 < h0 ∧ ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 → ∀ N : ℕ, CL.N0 ≤ N →
      Fz.step N ≤ h0 → CL.aOf p X N ≤ aplus →
      Fz.step N * max (-CL.aOf p X N) 0 ≤ wmDelta c1 (winCB CPC aplus ^ 2) CL.dp →
      WmClaims CL p X N c := by
  obtain ⟨-, hη, hdm, hdmp, -, -, -, -⟩ := CL.consts_pos
  have hdp : 0 < CL.dp := lt_of_lt_of_le hdm hdmp
  have hCPC : 0 < CPC := lt_of_lt_of_le pc.cPC_pos pc.cPC_le
  have hC1pos : 0 < winCB CPC aplus := by unfold winCB; positivity
  have hgm : 0 < CL.gm := CL.consts_pos4.1
  have hCLm := winCLam_nonneg CL
  have hc2 : 0 < c1 * CL.dm / (22 * CL.dp) := by positivity
  have hM1 : 1 ≤ max 1 aplus := le_max_left _ _
  have hM0 : 0 < max 1 aplus := by linarith
  have hT4p : 0 < ((1 / (2 * max 1 aplus) / 10) / CL.dp) ^ 2 := by positivity
  have hT5p : 0 < ((c1 / (24 * winCB CPC aplus ^ 2)) / CL.dp) ^ 2 := by positivity
  have hT6p : 0 < CL.gm ^ 2 * (c1 * CL.dm / (22 * CL.dp)) /
      (4 * ((CL.CBc * winCB CPC aplus * winCLam CL) ^ 2 + 1)) := by positivity
  refine ⟨min (c1 * CL.dm / (22 * CL.dp)) (CL.gm ^ 2 * (c1 * CL.dm / (22 * CL.dp)) / 4),
    min (winH1 CL) (min CL.η (min (farThr CL) (min (((1 / (2 * max 1 aplus) / 10) / CL.dp) ^ 2)
      (min (((c1 / (24 * winCB CPC aplus ^ 2)) / CL.dp) ^ 2) (min (CL.gm ^ 2 * (c1 * CL.dm / (22 * CL.dp)) /
      (4 * ((CL.CBc * winCB CPC aplus * winCLam CL) ^ 2 + 1))) 1))))),
    lt_min hc2 (by positivity),
    lt_min (winH1_pos CL) (lt_min hη (lt_min (farThr_pos CL) (lt_min hT4p (lt_min hT5p (lt_min hT6p one_pos))))), ?_⟩
  intro p hp X hX N hN hstep haplus hAsm
  have hh0 : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7⟩ := by simpa only [le_min_iff] using hstep
  have hsm0 : CL.dp * Real.sqrt (Fz.step N) ≤ 1 / (2 * max 1 aplus) / 10 :=
    wm_sqrt_small _ _ _ hdp (by positivity) hs4
  have hsm20 : CL.dp * Real.sqrt (Fz.step N) ≤ 1 / 20 := by
    refine le_trans hsm0 ?_
    have : 1 / (2 * max 1 aplus) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hS5 : CL.dp * Real.sqrt (Fz.step N) ≤ c1 / (24 * winCB CPC aplus ^ 2) :=
    wm_sqrt_small _ _ _ hdp (by positivity) hs5
  obtain ⟨hsum1, hsum2⟩ := wm_small12 pc CL aplus hc1pos hc1 hp hX hN haplus hs1 hs2 hs3 hsm0 hS5 hAsm
  have hsq : (Fz.step N * (CL.CBc * winCB CPC aplus * winCLam CL)) ^ 2 ≤
      CL.gm ^ 2 * (c1 * CL.dm / (22 * CL.dp)) / 4 := by
    have h6 : Fz.step N * ((CL.CBc * winCB CPC aplus * winCLam CL) ^ 2 + 1) ≤
        CL.gm ^ 2 * (c1 * CL.dm / (22 * CL.dp)) / 4 := by
      have := hs6
      rw [le_div_iff₀ (by positivity)] at this
      linarith [mul_comm (Fz.step N) (4 * ((CL.CBc * winCB CPC aplus * winCLam CL) ^ 2 + 1))]
    have h2 : Fz.step N ^ 2 ≤ Fz.step N := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg (CL.CBc * winCB CPC aplus * winCLam CL))]
  have hsum3 := wm_small3 pc CL aplus hp hX hN haplus hs1 hs2 hs3 hsm20 hsum2 hsq
  have hmm0 := wmMass_nonneg CL p X N
  have hmin1 : min (c1 * CL.dm / (22 * CL.dp)) (CL.gm ^ 2 * (c1 * CL.dm / (22 * CL.dp)) / 4) * wmMass CL p X N ≤
      c1 * CL.dm / (22 * CL.dp) * wmMass CL p X N :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) hmm0
  have hmin2 : min (c1 * CL.dm / (22 * CL.dp)) (CL.gm ^ 2 * (c1 * CL.dm / (22 * CL.dp)) / 4) * wmMass CL p X N ≤
      CL.gm ^ 2 * (c1 * CL.dm / (22 * CL.dp)) / 4 * wmMass CL p X N :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hmm0
  exact ⟨le_trans hmin1 hsum1, le_trans hmin1 hsum2, le_trans hmin2 hsum3⟩

end SmallBranch

section LargeFacts

/-- `Z_n` is nondecreasing along rows of the collar. -/
lemma wm_Z_mono (CL : SoftEdgeChart Fz P m q U V Lm) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hh1 : Fz.step N ≤ winH1 CL) {m' n : ℤ} (hmn : m' ≤ n)
    (hm : |uNode (Fz.step N) m' - CL.uc p| ≤ 2 * CL.η) (hn : |uNode (Fz.step N) n - CL.uc p| ≤ 2 * CL.η) :
    CL.Zof p X N m' ≤ CL.Zof p X N n := by
  have hh0 : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hdm := CL.consts_pos.2.2.1
  have hs0 : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
  have hu : ∀ k l : ℤ, k ≤ l → uNode (Fz.step N) k ≤ uNode (Fz.step N) l := by
    intro k l hkl
    unfold uNode
    have : (k : ℝ) ≤ l := by exact_mod_cast hkl
    nlinarith
  refine int_chain_mono (Z := CL.Zof p X N) (a := m') (b := n) ?_ m' le_rfl n hmn le_rfl
  intro k hk1 hk2
  have c1 : |uNode (Fz.step N) k - CL.uc p| ≤ 2 * CL.η := by
    have := hu m' k hk1
    have := hu k n hk2.le
    rw [abs_le] at hm hn ⊢
    constructor <;> linarith
  have c2 : |uNode (Fz.step N) (k + 1) - CL.uc p| ≤ 2 * CL.η := by
    have := hu m' (k + 1) (by omega)
    have := hu (k + 1) n (by omega)
    rw [abs_le] at hm hn ⊢
    constructor <;> linarith
  have := ((win_row CL p hp X hX N hh0 hh1 k c1).1 c2).1
  nlinarith [mul_pos hdm hs0]

/-- the switch bond splits the window rows by the sign of `Z`. -/
lemma wm_split2 (CL : SoftEdgeChart Fz P m q U V Lm) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N) (hh1 : Fz.step N ≤ winH1 CL) {n : ℤ}
    (hn : |uNode (Fz.step N) n - CL.uc p| ≤ 2 * CL.η) :
    (CL.Zof p X N n ≤ 0 → n ≤ (CL.chain p X N).jj 2) ∧ (0 < CL.Zof p X N n → (CL.chain p X N).jj 2 < n) := by
  obtain ⟨-, -, -, -, hz1, hz2, -, -⟩ := CL.shape p hp X hX N hN
  obtain ⟨-, -, hc1, hc2⟩ := CL.switch_in p hp X hX N hN
  constructor
  · intro hZ
    by_contra hc
    have hle : (CL.chain p X N).jj 2 + 1 ≤ n := by omega
    have := wm_Z_mono CL hp hX hh1 hle hc2 hn
    have hz2' : 0 < CL.Zof p X N ((CL.chain p X N).jj 2 + 1) := hz2
    linarith
  · intro hZ
    by_contra hc
    have hle : n ≤ (CL.chain p X N).jj 2 := by omega
    have := wm_Z_mono CL hp hX hh1 hle hn hc1
    have hz1' : CL.Zof p X N ((CL.chain p X N).jj 2) ≤ 0 := hz1
    linarith

/-- (S1) on the bonds of patches 2 and 3: `c_- sqrt h <= |W_n(phi^{(1)}_p, phi^{(2)}_p)|` (`PreValid.cas_lb_site`, `|omega_*| = sqrt h`). -/
lemma wm_cas_site (CL : SoftEdgeChart Fz P m q U V Lm) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N) {n : ℤ} {p' : ℕ} (hp2 : 2 ≤ p') (hp3 : p' ≤ 3)
    (hl : (CL.chain p X N).jj (p' - 1) ≤ n) (hu : n ≤ (CL.chain p X N).jj p') :
    CL.cs.cm * Real.sqrt (Fz.step N) ≤
      |cas (CL.chain p X N).A ((CL.chain p X N).phi (Fz.step N) 0 p') ((CL.chain p X N).phi (Fz.step N) 1 p') n| := by
  obtain ⟨hP3, -⟩ := CL.shape p hp X hX N hN
  obtain ⟨lam, hV⟩ : ∃ lam, ((CL.chain p X N).rescale1 lam).PreValid CL.cs (Fz.step N) m :=
    ⟨_, CL.valid p hp X hX N hN⟩
  have hpm : p' ∈ Finset.Icc 1 ((CL.chain p X N).rescale1 lam).P :=
    Finset.mem_Icc.mpr ⟨by omega, by show p' ≤ (CL.chain p X N).P; omega⟩
  have hjm : n ∈ Finset.Icc (((CL.chain p X N).rescale1 lam).jj (p' - 1)) (((CL.chain p X N).rescale1 lam).jj p') :=
    Finset.mem_Icc.mpr ⟨hl, hu⟩
  have h1 := hV.cas_lb_site hpm hjm
  have e0 : ((CL.chain p X N).rescale1 lam).phi (Fz.step N) 0 p' = (CL.chain p X N).phi (Fz.step N) 0 p' :=
    funext (LadderData.phi_rescale1_of_ne _ lam _ 0 (by omega))
  have e1 : ((CL.chain p X N).rescale1 lam).phi (Fz.step N) 1 p' = (CL.chain p X N).phi (Fz.step N) 1 p' :=
    funext (LadderData.phi_rescale1_of_ne _ lam _ 1 (by omega))
  rw [e0, e1] at h1
  have hω : (CL.chain p X N).ω 1 (Fz.step N) = Real.sqrt (Fz.step N) := by
    obtain ⟨-, -, -, -, -, h6, -⟩ := CL.patch1_eq p hp X hX N hN
    rw [h6]
    exact CL.omega_sqrtW p hp X hX N hN
  have hsq : |((CL.chain p X N).rescale1 lam).ω 1 (Fz.step N)| = Real.sqrt (Fz.step N) := by
    show |(CL.chain p X N).ω 1 (Fz.step N)| = _
    rw [hω, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [hsq] at h1
  exact h1

/-- (S2) envelopes of the pair of patch `p'`. -/
lemma wm_phibd (CL : SoftEdgeChart Fz P m q U V Lm) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N) {j : ℤ} {p' : ℕ} (hp2 : 2 ≤ p') (hp3 : p' ≤ 3)
    (hl : (CL.chain p X N).jj (p' - 1) ≤ j) (hu : j ≤ (CL.chain p X N).jj p' + 1) :
    |(CL.chain p X N).phi (Fz.step N) 0 p' j| ≤
        (CL.cs.KA + CL.cs.KB) * CL.cs.Kw * (CL.chain p X N).W j * (CL.chain p X N).M j ∧
      |(CL.chain p X N).phi (Fz.step N) 1 p' j| ≤
        (CL.cs.KA + CL.cs.KB) * CL.cs.Kw * ((CL.chain p X N).W j)⁻¹ * (CL.chain p X N).M j := by
  obtain ⟨hP3, -⟩ := CL.shape p hp X hX N hN
  obtain ⟨lam, hV⟩ : ∃ lam, ((CL.chain p X N).rescale1 lam).PreValid CL.cs (Fz.step N) m :=
    ⟨_, CL.valid p hp X hX N hN⟩
  have hpm : p' ∈ Finset.Icc 1 ((CL.chain p X N).rescale1 lam).P :=
    Finset.mem_Icc.mpr ⟨by omega, by show p' ≤ (CL.chain p X N).P; omega⟩
  have hjm : j ∈ Finset.Icc (((CL.chain p X N).rescale1 lam).jj (p' - 1)) (((CL.chain p X N).rescale1 lam).jj p' + 1) :=
    Finset.mem_Icc.mpr ⟨hl, hu⟩
  have h1 := hV.phi_bd hpm hjm
  have e0 : ((CL.chain p X N).rescale1 lam).phi (Fz.step N) 0 p' = (CL.chain p X N).phi (Fz.step N) 0 p' :=
    funext (LadderData.phi_rescale1_of_ne _ lam _ 0 (by omega))
  have e1 : ((CL.chain p X N).rescale1 lam).phi (Fz.step N) 1 p' = (CL.chain p X N).phi (Fz.step N) 1 p' :=
    funext (LadderData.phi_rescale1_of_ne _ lam _ 1 (by omega))
  rw [e0, e1] at h1
  exact h1

/-- `|A^{[m]}| <= K_A` on all rows of the PC patches (`A_bd`; patches 2, 3 share `AA`). -/
lemma wm_AA_le (CL : SoftEdgeChart Fz P m q U V Lm) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N) {n : ℤ}
    (hl : (CL.chain p X N).jj 1 ≤ n) (hu : n ≤ (CL.chain p X N).NR) :
    |(CL.chain p X N).AA 2 (uNode (Fz.step N) n) (Fz.step N)| ≤ CL.cs.KA := by
  obtain ⟨hP3, -⟩ := CL.shape p hp X hX N hN
  obtain ⟨lam, hV⟩ : ∃ lam, ((CL.chain p X N).rescale1 lam).PreValid CL.cs (Fz.step N) m :=
    ⟨_, CL.valid p hp X hX N hN⟩
  have hj0 : 0 ≤ (CL.chain p X N).jj 1 := hV.jj_nonneg (p := 1) (by show 1 ≤ (CL.chain p X N).P; omega)
  have hj2 : 0 ≤ (CL.chain p X N).jj 2 := hV.jj_nonneg (p := 2) (by show 2 ≤ (CL.chain p X N).P; omega)
  have hj3 : (CL.chain p X N).jj 3 = (CL.chain p X N).NR - 1 := by
    have := hV.jj_last
    have h3 : ((CL.chain p X N).rescale1 lam).P = 3 := hP3
    rw [h3] at this
    exact this
  by_cases hc : n ≤ (CL.chain p X N).jj 2 + 1
  · have hpm : 2 ∈ Finset.Icc 1 ((CL.chain p X N).rescale1 lam).P :=
      Finset.mem_Icc.mpr ⟨by norm_num, by show 2 ≤ (CL.chain p X N).P; omega⟩
    have hnm : n ∈ Finset.Icc (max (((CL.chain p X N).rescale1 lam).jj (2 - 1)) 0)
        (((CL.chain p X N).rescale1 lam).jj 2 + 1) :=
      Finset.mem_Icc.mpr ⟨max_le (by show (CL.chain p X N).jj 1 ≤ n; exact hl) (by omega), hc⟩
    exact hV.A_bd 2 hpm n hnm
  · have hj2' : (CL.chain p X N).jj 2 + 1 ≤ n := by omega
    obtain ⟨-, -, -, -, -, -, -, -, hAA, -⟩ := CL.shared_PC p hp X hX N hN
    have hpm : 3 ∈ Finset.Icc 1 ((CL.chain p X N).rescale1 lam).P :=
      Finset.mem_Icc.mpr ⟨by norm_num, by show 3 ≤ (CL.chain p X N).P; omega⟩
    have hnm : n ∈ Finset.Icc (max (((CL.chain p X N).rescale1 lam).jj (3 - 1)) 0)
        (((CL.chain p X N).rescale1 lam).jj 3 + 1) :=
      Finset.mem_Icc.mpr ⟨max_le (by show (CL.chain p X N).jj 2 ≤ n; omega) (by omega),
        by show n ≤ (CL.chain p X N).jj 3 + 1; omega⟩
    have h := hV.A_bd 3 hpm n hnm
    have h' : |(CL.chain p X N).AA 3 (((n : ℝ) + 1 / 2) * Fz.step N) (Fz.step N)| ≤ CL.cs.KA := h
    rw [hAA] at h'
    exact h'

lemma wm_W2_bd (CL : SoftEdgeChart Fz P m q U V Lm) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N) (aplus : ℝ) (haplus : CL.aOf p X N ≤ aplus)
    (ha0 : CL.aOf p X N ≤ 0) {j : ℤ} (hl : (CL.chain p X N).jj 1 < j) (hu : j ≤ (CL.chain p X N).jj 2)
    (hZ : |CL.Zof p X N j| ≤ rhoWin (CL.aOf p X N)) :
    ((CL.chain p X N).W j)⁻¹ ≤ Real.exp (5 / 2) := by
  rw [CL.W2_def p hp X hX N hN j (Finset.mem_Icc.mpr ⟨by omega, hu⟩)]
  have hw := (weights_conj (CL.aOf p X N) aplus (CL.Zof p X N j) haplus
    (le_trans hZ (by linarith [ell_nonneg' (CL.aOf p X N)]))).1 ha0
  have : Eminus (CL.aOf p X N) (CL.Zof p X N j) = Ewell (CL.aOf p X N) |CL.Zof p X N j| := by
    unfold Eminus; rw [ite_eq_left ha0]
  show (Eminus (CL.aOf p X N) (CL.Zof p X N j))⁻¹ ≤ _
  rw [this]
  exact inv_le_exp_five_half _ (by simpa [neg_div] using hw.1)

lemma wm_W3_bd (CL : SoftEdgeChart Fz P m q U V Lm) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N) (aplus : ℝ) (haplus : CL.aOf p X N ≤ aplus)
    (ha0 : CL.aOf p X N ≤ 0) {j : ℤ} (hl : (CL.chain p X N).jj 2 < j) (hu : j ≤ (CL.chain p X N).NR)
    (hZ : |CL.Zof p X N j| ≤ rhoWin (CL.aOf p X N)) :
    (CL.chain p X N).W j ≤ Real.exp (5 / 2) := by
  rw [CL.W3_def p hp X hX N hN j (Finset.mem_Icc.mpr ⟨by omega, hu⟩)]
  have hw := (weights_conj (CL.aOf p X N) aplus (CL.Zof p X N j) haplus
    (le_trans hZ (by linarith [ell_nonneg' (CL.aOf p X N)]))).1 ha0
  have : Eswap (CL.aOf p X N) (CL.Zof p X N j) = (Ewell (CL.aOf p X N) |CL.Zof p X N j|)⁻¹ := by
    unfold Eswap; rw [ite_eq_left ha0]
  show Eswap (CL.aOf p X N) (CL.Zof p X N j) ≤ _
  rw [this]
  exact inv_le_exp_five_half _ (by simpa [neg_div] using hw.1)

end LargeFacts

section Pure

lemma wm_Mbal_pos (a z : ℝ) : 0 < Mbal a z :=
  Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (win_k2_ge_one a z)) _

lemma wm_M4 (a z : ℝ) : Mbal a z ^ 4 * k2 a z = 1 := by
  have h := wm_mbal_sq_sqrt a z
  have hk : 0 ≤ k2 a z := le_trans zero_le_one (win_k2_ge_one a z)
  have hs : Real.sqrt (k2 a z) ^ 2 = k2 a z := Real.sq_sqrt hk
  calc Mbal a z ^ 4 * k2 a z = (Mbal a z ^ 2 * Real.sqrt (k2 a z)) ^ 2 := by rw [mul_pow, hs]; ring
    _ = 1 := by rw [h]; norm_num

/-- `15 A / 64 <= k_2 <= A` on `5/4 sqrt A <= |Z| <= 7/4 sqrt A`, `a = -A`, `A >= 1`. -/
lemma wm_k2_bounds (a Z A r : ℝ) (hA : A = -a) (hA1 : 1 ≤ A) (hr : r = Real.sqrt A)
    (hZ1 : 5 / 4 * r ≤ |Z|) (hZ2 : |Z| ≤ 7 / 4 * r) :
    15 / 64 * A ≤ k2 a Z ∧ k2 a Z ≤ A := by
  have hr0 : 0 ≤ r := by rw [hr]; exact Real.sqrt_nonneg _
  have hr2 : r ^ 2 = A := by rw [hr]; exact Real.sq_sqrt (by linarith)
  have hZ2' : Z ^ 2 ≤ 49 / 16 * A := by
    have : |Z| ^ 2 ≤ (7 / 4 * r) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hZ2 2
    rw [sq_abs] at this
    nlinarith
  have hZ1' : 25 / 16 * A ≤ Z ^ 2 := by
    have : (5 / 4 * r) ^ 2 ≤ |Z| ^ 2 := pow_le_pow_left₀ (by positivity) hZ1 2
    rw [sq_abs] at this
    nlinarith
  have hcube : max |a| 1 ^ ((1 : ℝ) / 3) ≤ A := by
    have : max |a| 1 = A := by
      rw [abs_of_nonpos (by linarith : a ≤ 0), ← hA]; exact max_eq_left hA1
    rw [this]; exact rpow_third_le A hA1
  unfold k2
  constructor
  · refine le_trans ?_ (le_max_left _ _)
    have : A - Z ^ 2 / 4 ≤ |Z ^ 2 / 4 + a| := by
      have := neg_abs_le (Z ^ 2 / 4 + a)
      linarith
    nlinarith
  · refine max_le ?_ hcube
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg Z]

lemma wm_Msq_lower (a Z A r : ℝ) (hA : A = -a) (hA1 : 1 ≤ A) (hr : r = Real.sqrt A)
    (hZ1 : 5 / 4 * r ≤ |Z|) (hZ2 : |Z| ≤ 7 / 4 * r) : 1 / r ≤ Mbal a Z ^ 2 := by
  obtain ⟨-, hk⟩ := wm_k2_bounds a Z A r hA hA1 hr hZ1 hZ2
  have hk1 : 0 < Real.sqrt (k2 a Z) := Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos (win_k2_ge_one a Z))
  have : Real.sqrt (k2 a Z) ≤ r := by rw [hr]; exact Real.sqrt_le_sqrt hk
  rw [mbal_sq_eq', one_div]
  exact inv_anti₀ hk1 this

lemma wm_mass_rows (M : ℤ → ℝ) (k0 : ℤ) (K : ℕ) (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hrδ : 4 * δ ≤ r)
    (hK : r / 2 < ((K : ℝ) + 2) * δ) (hM : ∀ i : ℕ, i ≤ K → 1 / r ≤ M (k0 + i) ^ 2) :
    1 / (4 * δ) ≤ ∑ i ∈ Finset.range (K + 1), M (k0 + i) ^ 2 := by
  have h1 : ∑ i ∈ Finset.range (K + 1), (1 / r) ≤ ∑ i ∈ Finset.range (K + 1), M (k0 + i) ^ 2 :=
    Finset.sum_le_sum (fun i hi => hM i (by simp at hi; omega))
  refine le_trans ?_ h1
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  rw [div_le_iff₀ (by positivity)]
  have h2 : r ≤ ((K : ℝ) + 1) * (4 * δ) := by nlinarith
  calc 1 = (1 / r) * r := by field_simp
    _ ≤ (1 / r) * (((K : ℝ) + 1) * (4 * δ)) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ((K : ℝ) + 1) * (1 / r) * (4 * δ) := by ring

/-- the pointwise two-site Casoratian bound: `c_3 M_n^2 <= phi_n^2 + phi_{n+1}^2`. -/
lemma wm_pair_pt (φ ψ A : ℤ → ℝ) (n : ℤ) (h cm CA1 T1 Mn k2n κ0 : ℝ) (hh : 0 < h) (hcm : 0 < cm) (hCA : 1 ≤ CA1)
    (hT : 1 ≤ T1) (hA0 : 0 ≤ A n) (hA : A n ≤ CA1) (hMn : 0 < Mn) (hψ0 : |ψ n| ≤ T1 * Mn)
    (hψ1 : |ψ (n + 1)| ≤ T1 * Mn) (hcas : cm * Real.sqrt h ≤ |cas A φ ψ n|) (hM4 : Mn ^ 4 * k2n = 1)
    (hκ : κ0 ≤ h * k2n) (hκ0 : 0 ≤ κ0) :
    cm ^ 2 * κ0 / (2 * CA1 ^ 2 * T1 ^ 2) * Mn ^ 2 ≤ φ n ^ 2 + φ (n + 1) ^ 2 := by
  have hsq := Real.sq_sqrt hh.le
  have hc0 : 0 < cm * Real.sqrt h := mul_pos hcm (Real.sqrt_pos.mpr hh)
  have key := wm_cas_two φ ψ A n (cm * Real.sqrt h) CA1 (T1 * Mn) hc0 hA0 hA (by positivity) hψ0 hψ1 hcas
  have e1 : (cm * Real.sqrt h) ^ 2 = cm ^ 2 * h := by rw [mul_pow, hsq]
  rw [e1] at key
  have hh' : κ0 * Mn ^ 4 ≤ h := by
    have : h = Mn ^ 4 * (h * k2n) := by
      calc h = h * (Mn ^ 4 * k2n) := by rw [hM4]; ring
        _ = Mn ^ 4 * (h * k2n) := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hκ (by positivity : (0 : ℝ) ≤ Mn ^ 4)]
  have hMn2 : 0 < Mn ^ 2 := by positivity
  have h3 : cm ^ 2 * κ0 * Mn ^ 4 ≤ 2 * (CA1 * (T1 * Mn)) ^ 2 * (φ n ^ 2 + φ (n + 1) ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hh' (sq_nonneg cm)]
  have h4 : cm ^ 2 * κ0 * Mn ^ 2 ≤ 2 * (CA1 * T1) ^ 2 * (φ n ^ 2 + φ (n + 1) ^ 2) := by
    have : (cm ^ 2 * κ0 * Mn ^ 2) * Mn ^ 2 ≤ (2 * (CA1 * T1) ^ 2 * (φ n ^ 2 + φ (n + 1) ^ 2)) * Mn ^ 2 := by
      calc (cm ^ 2 * κ0 * Mn ^ 2) * Mn ^ 2 = cm ^ 2 * κ0 * Mn ^ 4 := by ring
        _ ≤ 2 * (CA1 * (T1 * Mn)) ^ 2 * (φ n ^ 2 + φ (n + 1) ^ 2) := h3
        _ = (2 * (CA1 * T1) ^ 2 * (φ n ^ 2 + φ (n + 1) ^ 2)) * Mn ^ 2 := by ring
    exact le_of_mul_le_mul_right this hMn2
  have hpos : 0 < 2 * CA1 ^ 2 * T1 ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  nlinarith [h4]

end Pure

section LargePairs

/-- `K = (K_A + K_B) K_w`, the envelope constant of the engine. -/
def wmK (CL : SoftEdgeChart Fz P m q U V Lm) : ℝ := (CL.cs.KA + CL.cs.KB) * CL.cs.Kw

lemma wmK_nonneg (CL : SoftEdgeChart Fz P m q U V Lm) : 0 ≤ wmK CL :=
  mul_nonneg (add_nonneg CL.cs.KA_nonneg CL.cs.KB_nonneg) CL.cs.Kw_nonneg

/-- the envelope constant of the site bound `|psi_j| <= T1 M_n`, `j in {n, n+1}`. -/
def wmT1 (CL : SoftEdgeChart Fz P m q U V Lm) : ℝ := max (wmK CL * Real.exp (5 / 2) * max 1 (winCnb CL)) 1

/-- `c_3 = c_-^2 kappa_0 / (2 C_A^2 T_1^2)`, the constant of the pair bound. -/
def wmC3 (CL : SoftEdgeChart Fz P m q U V Lm) (κ0 : ℝ) : ℝ :=
  CL.cs.cm ^ 2 * κ0 / (2 * (max CL.CA 1) ^ 2 * wmT1 CL ^ 2)

lemma wmC3_pos (CL : SoftEdgeChart Fz P m q U V Lm) {κ0 : ℝ} (hκ : 0 < κ0) : 0 < wmC3 CL κ0 := by
  unfold wmC3
  have := CL.cs.cm_pos
  have h1 : 0 < max CL.CA 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h2 : 0 < wmT1 CL := lt_of_lt_of_le one_pos (le_max_right _ _)
  positivity

lemma wm_jj3 (CL : SoftEdgeChart Fz P m q U V Lm) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N) :
    (CL.chain p X N).jj 3 = (CL.chain p X N).NR - 1 := by
  obtain ⟨hP3, -⟩ := CL.shape p hp X hX N hN
  obtain ⟨lam, hV⟩ : ∃ lam, ((CL.chain p X N).rescale1 lam).PreValid CL.cs (Fz.step N) m :=
    ⟨_, CL.valid p hp X hX N hN⟩
  have := hV.jj_last
  have h3 : ((CL.chain p X N).rescale1 lam).P = 3 := hP3
  rw [h3] at this
  exact this

/-- the pair bound on patch 2 at a window row `n` with `Z_{n+1} <= 0`. -/
lemma wm_pair2_row (CL : SoftEdgeChart Fz P m q U V Lm) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N) (hh1 : Fz.step N ≤ winH1 CL) (aplus : ℝ)
    (haplus : CL.aOf p X N ≤ aplus) (ha0 : CL.aOf p X N ≤ 0) {n : ℤ}
    (hn : n ∈ softWindow CL p X N) (hn1 : n + 1 ∈ softWindow CL p X N)
    (hc : |uNode (Fz.step N) n - CL.uc p| < CL.η / 4) (hc1 : |uNode (Fz.step N) (n + 1) - CL.uc p| < CL.η / 4)
    (hZ1 : CL.Zof p X N (n + 1) ≤ 0) {κ0 : ℝ} (hκ0 : 0 ≤ κ0)
    (hκ : κ0 ≤ Fz.step N * k2 (CL.aOf p X N) (CL.Zof p X N n)) :
    wmC3 CL κ0 * Mbal (CL.aOf p X N) (CL.Zof p X N n) ^ 2 ≤
      ((CL.chain p X N).phi (Fz.step N) 0 2 n) ^ 2 + ((CL.chain p X N).phi (Fz.step N) 0 2 (n + 1)) ^ 2 := by
  have hh0 : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  obtain ⟨h0n, hNn, hZn, hj1n, hNRn, hc2n, hkn⟩ := wm_rowfacts CL hp hX hN hh1 hn hc
  obtain ⟨h0n1, hNn1, hZn1, hj1n1, hNRn1, hc2n1, hkn1⟩ := wm_rowfacts CL hp hX hN hh1 hn1 hc1
  have hjn1 : n + 1 ≤ (CL.chain p X N).jj 2 := ((wm_split2 CL hp hX hN hh1 hc2n1).1 hZ1)
  have hK := wmK_nonneg CL
  have hnb := (win_row CL p hp X hX N hh0 hh1 n hc2n).1 hc2n1
  have hMn := wm_Mbal_pos (CL.aOf p X N) (CL.Zof p X N n)
  have hCn1 : 0 ≤ max 1 (winCnb CL) := le_trans zero_le_one (le_max_left _ _)
  -- the bounds on `psi = phi^{(2)}_2`
  have hb0 := (wm_phibd CL hp hX hN (j := n) (p' := 2) le_rfl (by norm_num) hj1n.le (by omega)).2
  have hb1 := (wm_phibd CL hp hX hN (j := n + 1) (p' := 2) le_rfl (by norm_num) hj1n1.le (by omega)).2
  have hM0 : (CL.chain p X N).M n = Mbal (CL.aOf p X N) (CL.Zof p X N n) :=
    CL.M2_def p hp X hX N hN n (Finset.mem_Icc.mpr ⟨by omega, hNRn⟩)
  have hM1 : (CL.chain p X N).M (n + 1) = Mbal (CL.aOf p X N) (CL.Zof p X N (n + 1)) :=
    CL.M2_def p hp X hX N hN (n + 1) (Finset.mem_Icc.mpr ⟨by omega, hNRn1⟩)
  have hW0 := wm_W2_bd CL hp hX hN aplus haplus ha0 hj1n (by omega) hZn
  have hW1 := wm_W2_bd CL hp hX hN aplus haplus ha0 hj1n1 hjn1 hZn1
  have hTT : wmK CL * Real.exp (5 / 2) * max 1 (winCnb CL) ≤ wmT1 CL := le_max_left _ _
  have hψ0 : |(CL.chain p X N).phi (Fz.step N) 1 2 n| ≤ wmT1 CL * Mbal (CL.aOf p X N) (CL.Zof p X N n) := by
    unfold wmK at hb0
    rw [hM0] at hb0
    have : (CL.cs.KA + CL.cs.KB) * CL.cs.Kw * ((CL.chain p X N).W n)⁻¹ * Mbal (CL.aOf p X N) (CL.Zof p X N n) ≤
        wmK CL * Real.exp (5 / 2) * max 1 (winCnb CL) * Mbal (CL.aOf p X N) (CL.Zof p X N n) := by
      unfold wmK
      have h1 : ((CL.chain p X N).W n)⁻¹ ≤ Real.exp (5 / 2) * max 1 (winCnb CL) := by
        calc ((CL.chain p X N).W n)⁻¹ ≤ Real.exp (5 / 2) := hW0
          _ = Real.exp (5 / 2) * 1 := (mul_one _).symm
          _ ≤ Real.exp (5 / 2) * max 1 (winCnb CL) :=
              mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.exp_pos _).le
      have h2 : (CL.cs.KA + CL.cs.KB) * CL.cs.Kw ≥ 0 := hK
      nlinarith [mul_le_mul_of_nonneg_left h1 h2, hMn.le]
    nlinarith [mul_le_mul_of_nonneg_right hTT hMn.le]
  have hψ1 : |(CL.chain p X N).phi (Fz.step N) 1 2 (n + 1)| ≤ wmT1 CL * Mbal (CL.aOf p X N) (CL.Zof p X N n) := by
    unfold wmK at hb1
    rw [hM1] at hb1
    have h1 : ((CL.chain p X N).W (n + 1))⁻¹ * Mbal (CL.aOf p X N) (CL.Zof p X N (n + 1)) ≤
        Real.exp (5 / 2) * (max 1 (winCnb CL) * Mbal (CL.aOf p X N) (CL.Zof p X N n)) := by
      have hnb' : Mbal (CL.aOf p X N) (CL.Zof p X N (n + 1)) ≤ max 1 (winCnb CL) * Mbal (CL.aOf p X N) (CL.Zof p X N n) :=
        le_trans hnb.2.2 (mul_le_mul_of_nonneg_right (le_max_right _ _) hMn.le)
      exact mul_le_mul hW1 hnb' (wm_Mbal_pos _ _).le (Real.exp_pos _).le
    have h2 : (CL.cs.KA + CL.cs.KB) * CL.cs.Kw * ((CL.chain p X N).W (n + 1))⁻¹ *
        Mbal (CL.aOf p X N) (CL.Zof p X N (n + 1)) ≤
        wmK CL * (Real.exp (5 / 2) * (max 1 (winCnb CL) * Mbal (CL.aOf p X N) (CL.Zof p X N n))) := by
      unfold wmK
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h1 hK
    have h3 : wmK CL * Real.exp (5 / 2) * max 1 (winCnb CL) * Mbal (CL.aOf p X N) (CL.Zof p X N n) ≤
        wmT1 CL * Mbal (CL.aOf p X N) (CL.Zof p X N n) := mul_le_mul_of_nonneg_right hTT hMn.le
    nlinarith [h2, h3, hb1]
  have hA : (CL.chain p X N).A n = Fz.bondA p N n := by
    have h00 : 0 ≤ n := h0n
    exact CL.A_bond p hp X hX N hN n (Finset.mem_Icc.mpr ⟨by omega, hNRn⟩)
  have hA0 : 0 ≤ (CL.chain p X N).A n := by
    rw [hA]; unfold SymbolFamily.bondA; split_ifs
    · exact Real.sqrt_nonneg _
    · exact le_rfl
  have hAle : (CL.chain p X N).A n ≤ max CL.CA 1 := by
    rw [hA]; exact le_trans (CL.bondA_le p hp N (by omega) n) (le_max_left _ _)
  have hcas := wm_cas_site CL hp hX hN (n := n) (p' := 2) le_rfl (by norm_num) hj1n.le (by omega)
  exact wm_pair_pt _ _ _ n (Fz.step N) CL.cs.cm (max CL.CA 1) (wmT1 CL) _ _ κ0 hh0 CL.cs.cm_pos
    (le_max_right _ _) (le_max_right _ _) hA0 hAle hMn hψ0 hψ1 hcas (wm_M4 _ _) hκ hκ0

/-- the pair bound on patch 3 at a window row `n` with `Z_n > 0` (the lower bound is for `phi^{(2)}_3`, the second member of the swapped pair). -/
lemma wm_pair3_row (CL : SoftEdgeChart Fz P m q U V Lm) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N) (hh1 : Fz.step N ≤ winH1 CL) (aplus : ℝ)
    (haplus : CL.aOf p X N ≤ aplus) (ha0 : CL.aOf p X N ≤ 0) {n : ℤ}
    (hn : n ∈ softWindow CL p X N) (hn1 : n + 1 ∈ softWindow CL p X N)
    (hc : |uNode (Fz.step N) n - CL.uc p| < CL.η / 4) (hc1 : |uNode (Fz.step N) (n + 1) - CL.uc p| < CL.η / 4)
    (hZ0 : 0 < CL.Zof p X N n) {κ0 : ℝ} (hκ0 : 0 ≤ κ0)
    (hκ : κ0 ≤ Fz.step N * k2 (CL.aOf p X N) (CL.Zof p X N n)) :
    wmC3 CL κ0 * Mbal (CL.aOf p X N) (CL.Zof p X N n) ^ 2 ≤
      ((CL.chain p X N).phi (Fz.step N) 1 3 n) ^ 2 + ((CL.chain p X N).phi (Fz.step N) 1 3 (n + 1)) ^ 2 := by
  have hh0 : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  obtain ⟨h0n, hNn, hZn, hj1n, hNRn, hc2n, hkn⟩ := wm_rowfacts CL hp hX hN hh1 hn hc
  obtain ⟨h0n1, hNn1, hZn1, hj1n1, hNRn1, hc2n1, hkn1⟩ := wm_rowfacts CL hp hX hN hh1 hn1 hc1
  have hjn : (CL.chain p X N).jj 2 < n := ((wm_split2 CL hp hX hN hh1 hc2n).2 hZ0)
  have hjn1 : (CL.chain p X N).jj 2 < n + 1 := by omega
  have hj3 := wm_jj3 CL hp hX hN
  have hK := wmK_nonneg CL
  have hnb := (win_row CL p hp X hX N hh0 hh1 n hc2n).1 hc2n1
  have hMn := wm_Mbal_pos (CL.aOf p X N) (CL.Zof p X N n)
  have hb0 := (wm_phibd CL hp hX hN (j := n) (p' := 3) (by norm_num) le_rfl hjn.le (by omega)).1
  have hb1 := (wm_phibd CL hp hX hN (j := n + 1) (p' := 3) (by norm_num) le_rfl hjn1.le (by omega)).1
  have hM0 : (CL.chain p X N).M n = Mbal (CL.aOf p X N) (CL.Zof p X N n) :=
    CL.M2_def p hp X hX N hN n (Finset.mem_Icc.mpr ⟨by omega, hNRn⟩)
  have hM1 : (CL.chain p X N).M (n + 1) = Mbal (CL.aOf p X N) (CL.Zof p X N (n + 1)) :=
    CL.M2_def p hp X hX N hN (n + 1) (Finset.mem_Icc.mpr ⟨by omega, hNRn1⟩)
  have hW0 := wm_W3_bd CL hp hX hN aplus haplus ha0 hjn hNRn hZn
  have hW1 := wm_W3_bd CL hp hX hN aplus haplus ha0 hjn1 hNRn1 hZn1
  have hTT : wmK CL * Real.exp (5 / 2) * max 1 (winCnb CL) ≤ wmT1 CL := le_max_left _ _
  have hψ0 : |(CL.chain p X N).phi (Fz.step N) 0 3 n| ≤ wmT1 CL * Mbal (CL.aOf p X N) (CL.Zof p X N n) := by
    unfold wmK at hb0
    rw [hM0] at hb0
    have : (CL.cs.KA + CL.cs.KB) * CL.cs.Kw * (CL.chain p X N).W n * Mbal (CL.aOf p X N) (CL.Zof p X N n) ≤
        wmK CL * Real.exp (5 / 2) * max 1 (winCnb CL) * Mbal (CL.aOf p X N) (CL.Zof p X N n) := by
      unfold wmK
      have h1 : (CL.chain p X N).W n ≤ Real.exp (5 / 2) * max 1 (winCnb CL) := by
        calc (CL.chain p X N).W n ≤ Real.exp (5 / 2) := hW0
          _ = Real.exp (5 / 2) * 1 := (mul_one _).symm
          _ ≤ Real.exp (5 / 2) * max 1 (winCnb CL) :=
              mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.exp_pos _).le
      have h2 : 0 ≤ (CL.cs.KA + CL.cs.KB) * CL.cs.Kw := hK
      nlinarith [mul_le_mul_of_nonneg_left h1 h2, hMn.le]
    nlinarith [mul_le_mul_of_nonneg_right hTT hMn.le]
  have hψ1 : |(CL.chain p X N).phi (Fz.step N) 0 3 (n + 1)| ≤ wmT1 CL * Mbal (CL.aOf p X N) (CL.Zof p X N n) := by
    unfold wmK at hb1
    rw [hM1] at hb1
    have h1 : (CL.chain p X N).W (n + 1) * Mbal (CL.aOf p X N) (CL.Zof p X N (n + 1)) ≤
        Real.exp (5 / 2) * (max 1 (winCnb CL) * Mbal (CL.aOf p X N) (CL.Zof p X N n)) := by
      have hnb' : Mbal (CL.aOf p X N) (CL.Zof p X N (n + 1)) ≤ max 1 (winCnb CL) * Mbal (CL.aOf p X N) (CL.Zof p X N n) :=
        le_trans hnb.2.2 (mul_le_mul_of_nonneg_right (le_max_right _ _) hMn.le)
      exact mul_le_mul hW1 hnb' (wm_Mbal_pos _ _).le (Real.exp_pos _).le
    have h2 : (CL.cs.KA + CL.cs.KB) * CL.cs.Kw * (CL.chain p X N).W (n + 1) *
        Mbal (CL.aOf p X N) (CL.Zof p X N (n + 1)) ≤
        wmK CL * (Real.exp (5 / 2) * (max 1 (winCnb CL) * Mbal (CL.aOf p X N) (CL.Zof p X N n))) := by
      unfold wmK
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h1 hK
    have h3 : wmK CL * Real.exp (5 / 2) * max 1 (winCnb CL) * Mbal (CL.aOf p X N) (CL.Zof p X N n) ≤
        wmT1 CL * Mbal (CL.aOf p X N) (CL.Zof p X N n) := mul_le_mul_of_nonneg_right hTT hMn.le
    nlinarith [h2, h3, hb1]
  have hA : (CL.chain p X N).A n = Fz.bondA p N n :=
    CL.A_bond p hp X hX N hN n (Finset.mem_Icc.mpr ⟨by omega, hNRn⟩)
  have hA0 : 0 ≤ (CL.chain p X N).A n := by
    rw [hA]; unfold SymbolFamily.bondA; split_ifs
    · exact Real.sqrt_nonneg _
    · exact le_rfl
  have hAle : (CL.chain p X N).A n ≤ max CL.CA 1 := by
    rw [hA]; exact le_trans (CL.bondA_le p hp N (by omega) n) (le_max_left _ _)
  have hcas := wm_cas_site CL hp hX hN (n := n) (p' := 3) (by norm_num) le_rfl hjn.le (by omega)
  -- the casoratian is antisymmetric: use the pair `(phi^{(2)}_3, phi^{(1)}_3)`
  have hcas' : CL.cs.cm * Real.sqrt (Fz.step N) ≤
      |cas (CL.chain p X N).A ((CL.chain p X N).phi (Fz.step N) 1 3) ((CL.chain p X N).phi (Fz.step N) 0 3) n| := by
    have : cas (CL.chain p X N).A ((CL.chain p X N).phi (Fz.step N) 1 3) ((CL.chain p X N).phi (Fz.step N) 0 3) n =
        -cas (CL.chain p X N).A ((CL.chain p X N).phi (Fz.step N) 0 3) ((CL.chain p X N).phi (Fz.step N) 1 3) n := by
      unfold cas; ring
    rw [this, abs_neg]; exact hcas
  exact wm_pair_pt _ _ _ n (Fz.step N) CL.cs.cm (max CL.CA 1) (wmT1 CL) _ _ κ0 hh0 CL.cs.cm_pos
    (le_max_right _ _) (le_max_right _ _) hA0 hAle hMn hψ0 hψ1 hcas' (wm_M4 _ _) hκ hκ0

end LargePairs

section LargeSums

/-- the facts shared by the large-branch sum lemmas: the block, the mass bound and `rho >= 2 sqrt A`. -/
lemma wm_large_ctx (CL : SoftEdgeChart Fz P m q U V Lm) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N) (aplus : ℝ) (haplus : CL.aOf p X N ≤ aplus)
    (hs1 : Fz.step N ≤ winH1 CL) (hs2 : Fz.step N ≤ CL.η) (hs3 : Fz.step N ≤ farThr CL)
    (hsm0 : CL.dp * Real.sqrt (Fz.step N) ≤ 1 / (2 * max 1 aplus) / 10) :
    ∃ na nb : ℤ, WmBlock (CL.Zof p X N) na nb (rhoWin (CL.aOf p X N)) (CL.dp * Real.sqrt (Fz.step N)) ∧
      softWindow CL p X N = Finset.Icc na nb ∧
      (∀ n : ℤ, na ≤ n → n ≤ nb → |uNode (Fz.step N) n - CL.uc p| < CL.η / 4) ∧
      wmMass CL p X N ≤ 11 / (CL.dm * Real.sqrt (Fz.step N)) := by
  obtain ⟨-, hη, hdm, hdmp, -, -, -, -⟩ := CL.consts_pos
  have hdp : 0 < CL.dp := lt_of_lt_of_le hdm hdmp
  have hh0 : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hM1 : 1 ≤ max 1 aplus := le_max_left _ _
  have hsm20 : CL.dp * Real.sqrt (Fz.step N) ≤ 1 / 20 := by
    refine le_trans hsm0 ?_
    have : 1 / (2 * max 1 aplus) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hfarN : ∀ n : ℤ, 0 ≤ n → n ≤ (N : ℤ) → 2 * CL.η < |uNode (Fz.step N) n - CL.uc p| →
      rhoWin (CL.aOf p X N) < |CL.Zof p X N n| :=
    fun n h0 hN' hfn => farChart CL p hp X hX N hs3 n h0 hN' hfn
  obtain ⟨na, nb, hB, hW, hcl⟩ := wm_ctx CL p hp X hX N hN hs1 hs2 hsm20 hfarN
  refine ⟨na, nb, hB, hW, hcl, ?_⟩
  have := (win_chart_sums CL p hp X hX N hN aplus hs1 hs2 hsm0 haplus hfarN).1
  rw [rpow_neg_half _ hh0.le] at this
  have hsqh : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
  calc wmMass CL p X N ≤ 11 / CL.dm * (Real.sqrt (Fz.step N))⁻¹ := this
    _ = 11 / (CL.dm * Real.sqrt (Fz.step N)) := by field_simp

/-- **Step 3, conjunct 3 / 2 (patch 2)**: the two-site Casoratian lower bound for `phi^{(1)}_2` on the left half of the window (`tilde mu > delta`). -/
lemma wm_large2 (CL : SoftEdgeChart Fz P m q U V Lm) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N) (aplus : ℝ) (haplus : CL.aOf p X N ≤ aplus)
    (hs1 : Fz.step N ≤ winH1 CL) (hs2 : Fz.step N ≤ CL.η) (hs3 : Fz.step N ≤ farThr CL)
    (hsm0 : CL.dp * Real.sqrt (Fz.step N) ≤ 1 / (2 * max 1 aplus) / 10)
    (hr : 4 * (CL.dp * Real.sqrt (Fz.step N)) + 1 ≤ Real.sqrt (max (-CL.aOf p X N) 0))
    {κ0 : ℝ} (hκ0 : 0 < κ0) (hκA : κ0 ≤ 15 / 64 * (Fz.step N * max (-CL.aOf p X N) 0)) :
    wmC3 CL κ0 * (CL.dm / (44 * CL.dp)) * wmMass CL p X N / 2 ≤
      ∑ n ∈ (softWindow CL p X N).filter (fun n => CL.Zof p X N n ≤ -wmCut (CL.aOf p X N)),
        ((CL.chain p X N).phi (Fz.step N) 0 2 n) ^ 2 := by
  obtain ⟨-, hη, hdm, hdmp, -, -, -, -⟩ := CL.consts_pos
  have hdp : 0 < CL.dp := lt_of_lt_of_le hdm hdmp
  have hh0 : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hM1 : 1 ≤ max 1 aplus := le_max_left _ _
  have hsm20 : CL.dp * Real.sqrt (Fz.step N) ≤ 1 / 20 := by
    refine le_trans hsm0 ?_
    have : 1 / (2 * max 1 aplus) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  obtain ⟨na, nb, hB, hW, hcl, hmm⟩ := wm_large_ctx CL hp hX hN aplus haplus hs1 hs2 hs3 hsm0
  have hsqh : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
  have hδ : 0 < CL.dp * Real.sqrt (Fz.step N) := mul_pos hdp hsqh
  -- `A`, `r = sqrt A`
  have hA0 : 0 ≤ max (-CL.aOf p X N) 0 := le_max_right _ _
  obtain ⟨A, hAdef⟩ : ∃ A, A = max (-CL.aOf p X N) 0 := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r, r = Real.sqrt A := ⟨_, rfl⟩
  rw [← hAdef, ← hrdef] at hr
  rw [← hAdef] at hκA
  have hδ20 : CL.dp * Real.sqrt (Fz.step N) ≤ 1 / 20 := hsm20
  have hr1 : 1 ≤ r := by linarith
  have hr2 : r ^ 2 = A := by rw [hrdef]; exact Real.sq_sqrt (by rw [hAdef]; exact hA0)
  have hA1 : 1 ≤ A := by nlinarith
  have hapos' : A = -CL.aOf p X N := by
    rcases le_total 0 (-CL.aOf p X N) with h | h
    · rw [hAdef]; exact max_eq_left h
    · have : A = 0 := by rw [hAdef]; exact max_eq_right h
      linarith
  have hapos : CL.aOf p X N = -A := by linarith
  have ha0 : CL.aOf p X N ≤ 0 := by rw [hapos]; linarith
  have hρ2r : 2 * r ≤ rhoWin (CL.aOf p X N) := by
    unfold rhoWin
    rw [← hAdef, ← hrdef]
    linarith [Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 1 + A) (-(1 : ℝ) / 6)]
  -- the rows in the window `(-7r/4, -5r/4]`
  have hlowZ : (CL.Zof p X N na) ≤ -7 / 4 * r := by
    have := hB.low
    linarith [hρ2r, hδ20]
  have hupZ : -5 / 4 * r < CL.Zof p X N nb := by
    have := hB.up
    linarith [hρ2r, hδ20]
  obtain ⟨k0, K, hk0, hkK, hrows, hKc⟩ := wm_count hB hδ (α := -7 / 4 * r) (β := -5 / 4 * r) (by linarith) hlowZ hupZ
  have hmemW : ∀ n : ℤ, na ≤ n → n ≤ nb → n ∈ softWindow CL p X N := fun n h1 h2 => by
    rw [hW]; exact Finset.mem_Icc.mpr ⟨h1, h2⟩
  have hrowfacts : ∀ i : ℕ, i ≤ K →
      (-7 / 4 * r < CL.Zof p X N (k0 + i) ∧ CL.Zof p X N (k0 + i) ≤ -5 / 4 * r) ∧
      CL.Zof p X N (k0 + i + 1) ≤ CL.Zof p X N (k0 + i) + CL.dp * Real.sqrt (Fz.step N) := by
    intro i hi
    refine ⟨hrows i hi, ?_⟩
    have := (hB.sp (k0 + i) (by omega) (by omega)).2
    linarith
  refine le_trans ?_ (wm_pair_sum (fun n => (CL.chain p X N).phi (Fz.step N) 0 2 n)
    (fun n => Mbal (CL.aOf p X N) (CL.Zof p X N n))
    ((softWindow CL p X N).filter (fun n => CL.Zof p X N n ≤ -wmCut (CL.aOf p X N))) k0 K (wmC3 CL κ0)
    (CL.dm / (44 * CL.dp)) (wmMass CL p X N) (wmC3_pos CL hκ0).le ?_ ?_ ?_)
  · exact le_rfl
  · -- the rows lie in the cut
    intro i hi
    have hcut : wmCut (CL.aOf p X N) ≤ r + 1 / 4 := by
      unfold wmCut
      rw [← hAdef, ← hrdef]
      have := wm_ell_le_one (CL.aOf p X N)
      rw [← hAdef] at this
      linarith
    rw [Finset.mem_filter]
    refine ⟨hmemW _ (by omega) (by omega), ?_⟩
    by_cases hiK : i ≤ K
    · have := (hrowfacts i hiK).1.2
      linarith
    · have hiK' : i = K + 1 := by omega
      subst hiK'
      have h1 := hrowfacts K le_rfl
      have e : k0 + ((K + 1 : ℕ) : ℤ) = k0 + (K : ℤ) + 1 := by push_cast; ring
      rw [e]
      linarith [h1.1.2, h1.2]
  · -- the pointwise pair bounds
    intro i hi
    have hZ := (hrowfacts i hi).1
    have hn : k0 + (i : ℤ) ∈ softWindow CL p X N := hmemW _ (by omega) (by omega)
    have hn1 : k0 + (i : ℤ) + 1 ∈ softWindow CL p X N := hmemW _ (by omega) (by omega)
    have hZabs1 : 5 / 4 * r ≤ |CL.Zof p X N (k0 + i)| := by
      rw [abs_of_nonpos (by linarith [hZ.2])]; linarith [hZ.2]
    have hZabs2 : |CL.Zof p X N (k0 + i)| ≤ 7 / 4 * r := by
      rw [abs_of_nonpos (by linarith [hZ.2])]; linarith [hZ.1]
    obtain ⟨hk1, -⟩ := wm_k2_bounds (CL.aOf p X N) (CL.Zof p X N (k0 + i)) A r hapos' hA1 hrdef hZabs1 hZabs2
    have hκ : κ0 ≤ Fz.step N * k2 (CL.aOf p X N) (CL.Zof p X N (k0 + i)) := by
      have := mul_le_mul_of_nonneg_left hk1 hh0.le
      nlinarith
    have hZ1 : CL.Zof p X N (k0 + i + 1) ≤ 0 := by
      have := (hrowfacts i hi).2
      linarith [hZ.2]
    exact wm_pair2_row CL hp hX hN hs1 aplus haplus ha0 hn hn1
      (hcl _ (by omega) (by omega)) (hcl _ (by omega) (by omega)) hZ1 hκ0.le hκ
  · -- the mass of the rows
    have hrows_mass : ∀ i : ℕ, i ≤ K → 1 / r ≤ Mbal (CL.aOf p X N) (CL.Zof p X N (k0 + i)) ^ 2 := by
      intro i hi
      have hZ := (hrowfacts i hi).1
      have hZabs1 : 5 / 4 * r ≤ |CL.Zof p X N (k0 + i)| := by
        rw [abs_of_nonpos (by linarith [hZ.2])]; linarith [hZ.2]
      have hZabs2 : |CL.Zof p X N (k0 + i)| ≤ 7 / 4 * r := by
        rw [abs_of_nonpos (by linarith [hZ.2])]; linarith [hZ.1]
      exact wm_Msq_lower _ _ A r hapos' hA1 hrdef hZabs1 hZabs2
    have hm := wm_mass_rows (fun n => Mbal (CL.aOf p X N) (CL.Zof p X N n)) k0 K r
      (CL.dp * Real.sqrt (Fz.step N)) (by linarith) hδ (by linarith) (by linarith [hKc]) hrows_mass
    refine le_trans ?_ hm
    calc CL.dm / (44 * CL.dp) * wmMass CL p X N ≤ CL.dm / (44 * CL.dp) * (11 / (CL.dm * Real.sqrt (Fz.step N))) :=
          mul_le_mul_of_nonneg_left hmm (by positivity)
      _ = 1 / (4 * (CL.dp * Real.sqrt (Fz.step N))) := by field_simp; ring

/-- **Step 3, conjunct 1 (patch 3)**: the two-site Casoratian lower bound for `phi^{(1)}_3` on the right half of the window (`tilde mu > delta`). -/
lemma wm_large1 (CL : SoftEdgeChart Fz P m q U V Lm) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ}
    (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N) (aplus : ℝ) (haplus : CL.aOf p X N ≤ aplus)
    (hs1 : Fz.step N ≤ winH1 CL) (hs2 : Fz.step N ≤ CL.η) (hs3 : Fz.step N ≤ farThr CL)
    (hsm0 : CL.dp * Real.sqrt (Fz.step N) ≤ 1 / (2 * max 1 aplus) / 10)
    (hr : 4 * (CL.dp * Real.sqrt (Fz.step N)) + 1 ≤ Real.sqrt (max (-CL.aOf p X N) 0))
    {κ0 : ℝ} (hκ0 : 0 < κ0) (hκA : κ0 ≤ 15 / 64 * (Fz.step N * max (-CL.aOf p X N) 0)) :
    wmC3 CL κ0 * (CL.dm / (44 * CL.dp)) * wmMass CL p X N / 2 ≤
      ∑ n ∈ (softWindow CL p X N).filter (fun n => wmCut (CL.aOf p X N) < CL.Zof p X N n),
        ((CL.chain p X N).phi (Fz.step N) 1 3 n) ^ 2 := by
  obtain ⟨-, hη, hdm, hdmp, -, -, -, -⟩ := CL.consts_pos
  have hdp : 0 < CL.dp := lt_of_lt_of_le hdm hdmp
  have hh0 : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hM1 : 1 ≤ max 1 aplus := le_max_left _ _
  have hsm20 : CL.dp * Real.sqrt (Fz.step N) ≤ 1 / 20 := by
    refine le_trans hsm0 ?_
    have : 1 / (2 * max 1 aplus) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  obtain ⟨na, nb, hB, hW, hcl, hmm⟩ := wm_large_ctx CL hp hX hN aplus haplus hs1 hs2 hs3 hsm0
  have hsqh : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
  have hδ : 0 < CL.dp * Real.sqrt (Fz.step N) := mul_pos hdp hsqh
  -- `A`, `r = sqrt A`
  have hA0 : 0 ≤ max (-CL.aOf p X N) 0 := le_max_right _ _
  obtain ⟨A, hAdef⟩ : ∃ A, A = max (-CL.aOf p X N) 0 := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r, r = Real.sqrt A := ⟨_, rfl⟩
  rw [← hAdef, ← hrdef] at hr
  rw [← hAdef] at hκA
  have hδ20 : CL.dp * Real.sqrt (Fz.step N) ≤ 1 / 20 := hsm20
  have hr1 : 1 ≤ r := by linarith
  have hr2 : r ^ 2 = A := by rw [hrdef]; exact Real.sq_sqrt (by rw [hAdef]; exact hA0)
  have hA1 : 1 ≤ A := by nlinarith
  have hapos' : A = -CL.aOf p X N := by
    rcases le_total 0 (-CL.aOf p X N) with h | h
    · rw [hAdef]; exact max_eq_left h
    · have : A = 0 := by rw [hAdef]; exact max_eq_right h
      linarith
  have hapos : CL.aOf p X N = -A := by linarith
  have ha0 : CL.aOf p X N ≤ 0 := by rw [hapos]; linarith
  have hρ2r : 2 * r ≤ rhoWin (CL.aOf p X N) := by
    unfold rhoWin
    rw [← hAdef, ← hrdef]
    linarith [Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 1 + A) (-(1 : ℝ) / 6)]
  -- the rows in the window `(5r/4, 7r/4]`
  have hlowZ : (CL.Zof p X N na) ≤ 5 / 4 * r := by
    have := hB.low
    linarith [hρ2r, hδ20]
  have hupZ : 7 / 4 * r < CL.Zof p X N nb := by
    have := hB.up
    linarith [hρ2r, hδ20]
  obtain ⟨k0, K, hk0, hkK, hrows, hKc⟩ := wm_count hB hδ (α := 5 / 4 * r) (β := 7 / 4 * r) (by linarith) hlowZ hupZ
  have hmemW : ∀ n : ℤ, na ≤ n → n ≤ nb → n ∈ softWindow CL p X N := fun n h1 h2 => by
    rw [hW]; exact Finset.mem_Icc.mpr ⟨h1, h2⟩
  have hrowfacts : ∀ i : ℕ, i ≤ K →
      (5 / 4 * r < CL.Zof p X N (k0 + i) ∧ CL.Zof p X N (k0 + i) ≤ 7 / 4 * r) ∧
      CL.Zof p X N (k0 + i) < CL.Zof p X N (k0 + i + 1) := by
    intro i hi
    exact ⟨hrows i hi, (hB.sp (k0 + i) (by omega) (by omega)).1 |> fun h => by linarith⟩
  refine le_trans ?_ (wm_pair_sum (fun n => (CL.chain p X N).phi (Fz.step N) 1 3 n)
    (fun n => Mbal (CL.aOf p X N) (CL.Zof p X N n))
    ((softWindow CL p X N).filter (fun n => wmCut (CL.aOf p X N) < CL.Zof p X N n)) k0 K (wmC3 CL κ0)
    (CL.dm / (44 * CL.dp)) (wmMass CL p X N) (wmC3_pos CL hκ0).le ?_ ?_ ?_)
  · exact le_rfl
  · -- the rows lie in the cut
    intro i hi
    have hcut : wmCut (CL.aOf p X N) ≤ r + 1 / 4 := by
      unfold wmCut
      rw [← hAdef, ← hrdef]
      have := wm_ell_le_one (CL.aOf p X N)
      rw [← hAdef] at this
      linarith
    rw [Finset.mem_filter]
    refine ⟨hmemW _ (by omega) (by omega), ?_⟩
    by_cases hiK : i ≤ K
    · have := (hrowfacts i hiK).1.1
      linarith
    · have hiK' : i = K + 1 := by omega
      subst hiK'
      have h1 := hrowfacts K le_rfl
      have e : k0 + ((K + 1 : ℕ) : ℤ) = k0 + (K : ℤ) + 1 := by push_cast; ring
      rw [e]
      linarith [h1.1.1, h1.2]
  · -- the pointwise pair bounds
    intro i hi
    have hZ := (hrowfacts i hi).1
    have hn : k0 + (i : ℤ) ∈ softWindow CL p X N := hmemW _ (by omega) (by omega)
    have hn1 : k0 + (i : ℤ) + 1 ∈ softWindow CL p X N := hmemW _ (by omega) (by omega)
    have hZabs1 : 5 / 4 * r ≤ |CL.Zof p X N (k0 + i)| := by
      rw [abs_of_pos (by linarith [hZ.1])]; linarith [hZ.1]
    have hZabs2 : |CL.Zof p X N (k0 + i)| ≤ 7 / 4 * r := by
      rw [abs_of_pos (by linarith [hZ.1])]; linarith [hZ.2]
    obtain ⟨hk1, -⟩ := wm_k2_bounds (CL.aOf p X N) (CL.Zof p X N (k0 + i)) A r hapos' hA1 hrdef hZabs1 hZabs2
    have hκ : κ0 ≤ Fz.step N * k2 (CL.aOf p X N) (CL.Zof p X N (k0 + i)) := by
      have := mul_le_mul_of_nonneg_left hk1 hh0.le
      nlinarith
    have hZ0 : 0 < CL.Zof p X N (k0 + i) := by linarith [hZ.1]
    exact wm_pair3_row CL hp hX hN hs1 aplus haplus ha0 hn hn1
      (hcl _ (by omega) (by omega)) (hcl _ (by omega) (by omega)) hZ0 hκ0.le hκ
  · -- the mass of the rows
    have hrows_mass : ∀ i : ℕ, i ≤ K → 1 / r ≤ Mbal (CL.aOf p X N) (CL.Zof p X N (k0 + i)) ^ 2 := by
      intro i hi
      have hZ := (hrowfacts i hi).1
      have hZabs1 : 5 / 4 * r ≤ |CL.Zof p X N (k0 + i)| := by
        rw [abs_of_pos (by linarith [hZ.1])]; linarith [hZ.1]
      have hZabs2 : |CL.Zof p X N (k0 + i)| ≤ 7 / 4 * r := by
        rw [abs_of_pos (by linarith [hZ.1])]; linarith [hZ.2]
      exact wm_Msq_lower _ _ A r hapos' hA1 hrdef hZabs1 hZabs2
    have hm := wm_mass_rows (fun n => Mbal (CL.aOf p X N) (CL.Zof p X N n)) k0 K r
      (CL.dp * Real.sqrt (Fz.step N)) (by linarith) hδ (by linarith) (by linarith [hKc]) hrows_mass
    refine le_trans ?_ hm
    calc CL.dm / (44 * CL.dp) * wmMass CL p X N ≤ CL.dm / (44 * CL.dp) * (11 / (CL.dm * Real.sqrt (Fz.step N))) :=
          mul_le_mul_of_nonneg_left hmm (by positivity)
      _ = 1 / (4 * (CL.dp * Real.sqrt (Fz.step N))) := by field_simp; ring


/-- the patch-3 corrector rows: `|phi^{(1)}_3 - A y_1^-| <= h E M` on a collar row with `Z_n > 0` (`y_1^- = -kappa U(a,Z)`). -/
lemma wm_row3 {cPC CPC : ℝ} (pc : ParabolicCylinderFacts U V cPC CPC) (CL : SoftEdgeChart Fz P m q U V Lm) (aplus : ℝ)
    {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N)
    (haplus : CL.aOf p X N ≤ aplus) (hh1 : Fz.step N ≤ winH1 CL) {n : ℤ}
    (hn : n ∈ softWindow CL p X N) (hcol : |uNode (Fz.step N) n - CL.uc p| < CL.η / 4)
    (hZ0 : 0 < CL.Zof p X N n) :
    |(CL.chain p X N).phi (Fz.step N) 1 3 n -
        (CL.chain p X N).AA 2 (uNode (Fz.step N) n) (Fz.step N) *
          (-(kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (CL.Zof p X N n)))| ≤
      Fz.step N * (CL.CBc * winCB CPC aplus * winCLam CL) * Mbal (CL.aOf p X N) (CL.Zof p X N n) := by
  have hCPC : 0 < CPC := lt_of_lt_of_le pc.cPC_pos pc.cPC_le
  have hC1 : 0 < winCB CPC aplus := by unfold winCB; positivity
  have hh0 : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  obtain ⟨h0, hNn, hZ, hj1, hNR, hc2, hkz⟩ := wm_rowfacts CL hp hX hN hh1 hn hcol
  obtain ⟨-, hBB⟩ := CL.corr_PC p hp X hX N hN n h0 hNn hc2
  have hjn : (CL.chain p X N).jj 2 < n := ((wm_split2 CL hp hX hN hh1 hc2).2 hZ0)
  have hdec := wm_phi3_decomp CL hp hX hN (n := n) hjn.le (by omega) 1
  have hfp := (wm_env_two pc aplus (CL.aOf p X N) haplus (CL.Zof p X N n) hZ).1.2
  have hfe : pcSwap U V (CL.aOf p X N) 1 (CL.Zof p X N n) =
      -(kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (CL.Zof p X N n)) := by
    rw [wm_pcSwap1]
  have hderiv : |deriv (pcSwap U V (CL.aOf p X N) 1) (CL.Zof p X N n)| =
      |deriv (fun w => kappaBal (CL.aOf p X N) * U (CL.aOf p X N) w) (CL.Zof p X N n)| := by
    rw [wm_pcSwap1]
    have e : (fun z => -(kappaBal (CL.aOf p X N) * U (CL.aOf p X N) z)) =
        -(fun w => kappaBal (CL.aOf p X N) * U (CL.aOf p X N) w) := rfl
    rw [e, deriv.neg, abs_neg]
  rw [hdec, hfe, add_sub_cancel_left]
  exact wm_err _ _ _ _ _ _ _ _ hh0 hBB hkz (winCLam_nonneg CL) (le_trans zero_le_one (win_k2_ge_one _ _))
    (by rw [hderiv]; exact hfp) hC1.le (Mbal_nonneg' _ _)

/-- the corrector transfer `sum phi^2 >= C mm  ==>  sum f^2 >= C / (4 K_A^2) mm`, for `phi = a f + e`, `|a| <= K_A`, `|e| <= eps M`. -/
lemma wm_conj_from_phi (S : Finset ℤ) (φ f e M a : ℤ → ℝ) (KA ε mm C : ℝ) (hKA : 1 ≤ KA) (hC : 0 ≤ C)
    (hA : ∀ n ∈ S, |a n| ≤ KA) (hφ : ∀ n ∈ S, φ n = a n * f n + e n) (he : ∀ n ∈ S, |e n| ≤ ε * M n)
    (hM : ∑ n ∈ S, M n ^ 2 ≤ mm) (hmm : 0 ≤ mm) (hε : ε ^ 2 ≤ C / 4) (hlow : C * mm ≤ ∑ n ∈ S, φ n ^ 2) :
    C / (4 * KA ^ 2) * mm ≤ ∑ n ∈ S, f n ^ 2 := by
  have hup := wm_corr_upper S φ f e M a KA ε mm hA hφ he hM
  have h1 : 2 * ε ^ 2 * mm ≤ C / 2 * mm := by nlinarith
  have hK : 0 < 4 * KA ^ 2 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hK]
  nlinarith [hup, h1, hlow, sq_nonneg KA]

/-- the cut is positive. -/
lemma wm_cut_pos (a : ℝ) : 0 < wmCut a := by
  unfold wmCut
  have := Real.sqrt_nonneg (max (-a) 0)
  have h1 := le_max_right (-a) 0
  have h2 : 0 < (1 + max (-a) 0) ^ (-(1 : ℝ) / 6) := Real.rpow_pos_of_pos (by linarith) _
  linarith

/-- conjunct 1 in the large branch: transfer from `phi^{(1)}_3`. -/
lemma wm_conj1_large {cPC CPC : ℝ} (pc : ParabolicCylinderFacts U V cPC CPC) (CL : SoftEdgeChart Fz P m q U V Lm)
    (aplus : ℝ) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N)
    (haplus : CL.aOf p X N ≤ aplus) (hs1 : Fz.step N ≤ winH1 CL) {KA1 Cc : ℝ} (hKA1 : 1 ≤ KA1) (hCc : 0 ≤ Cc)
    (hAbd : ∀ n ∈ softWindow CL p X N, |(CL.chain p X N).AA 2 (uNode (Fz.step N) n) (Fz.step N)| ≤ KA1)
    (hcolS : ∀ n ∈ softWindow CL p X N, |uNode (Fz.step N) n - CL.uc p| < CL.η / 4)
    (hε2 : (Fz.step N * (CL.CBc * winCB CPC aplus * winCLam CL)) ^ 2 ≤ Cc / 4)
    (hLow : Cc * wmMass CL p X N ≤
      ∑ n ∈ (softWindow CL p X N).filter (fun n => wmCut (CL.aOf p X N) < CL.Zof p X N n),
        ((CL.chain p X N).phi (Fz.step N) 1 3 n) ^ 2) :
    Cc / (4 * KA1 ^ 2) * wmMass CL p X N ≤
      ∑ n ∈ (softWindow CL p X N).filter (fun n => wmCut (CL.aOf p X N) < CL.Zof p X N n),
        (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (CL.Zof p X N n)) ^ 2 := by
  have := wm_conj_from_phi ((softWindow CL p X N).filter (fun n => wmCut (CL.aOf p X N) < CL.Zof p X N n))
    (fun n => (CL.chain p X N).phi (Fz.step N) 1 3 n)
    (fun n => -(kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (CL.Zof p X N n)))
    (fun n => (CL.chain p X N).phi (Fz.step N) 1 3 n -
      (CL.chain p X N).AA 2 (uNode (Fz.step N) n) (Fz.step N) *
        (-(kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (CL.Zof p X N n))))
    (fun n => Mbal (CL.aOf p X N) (CL.Zof p X N n))
    (fun n => (CL.chain p X N).AA 2 (uNode (Fz.step N) n) (Fz.step N))
    KA1 (Fz.step N * (CL.CBc * winCB CPC aplus * winCLam CL)) (wmMass CL p X N) Cc hKA1 hCc
    (fun n hn => hAbd n (Finset.mem_filter.mp hn).1)
    (fun n _ => by ring)
    (fun n hn => by
      obtain ⟨hn1, hn2⟩ := Finset.mem_filter.mp hn
      have hZ0 : 0 < CL.Zof p X N n := lt_trans (wm_cut_pos _) hn2
      exact wm_row3 pc CL aplus hp hX hN haplus hs1 hn1 (hcolS n hn1) hZ0)
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun n _ _ => sq_nonneg _))
    (wmMass_nonneg CL p X N) hε2 hLow
  simpa only [neg_sq] using this

/-- conjunct 2 in the large branch: transfer from `phi^{(1)}_2`. -/
lemma wm_conj2_large {cPC CPC : ℝ} (pc : ParabolicCylinderFacts U V cPC CPC) (CL : SoftEdgeChart Fz P m q U V Lm)
    (aplus : ℝ) {p : Par × ℝ} (hp : p ∈ P) {X : ℝ} (hX : |X - Fz.bandHi p| ≤ CL.δ0) {N : ℕ} (hN : CL.N0 ≤ N)
    (haplus : CL.aOf p X N ≤ aplus) (hs1 : Fz.step N ≤ winH1 CL) {KA1 Cc : ℝ} (hKA1 : 1 ≤ KA1) (hCc : 0 ≤ Cc)
    (hAbd : ∀ n ∈ softWindow CL p X N, |(CL.chain p X N).AA 2 (uNode (Fz.step N) n) (Fz.step N)| ≤ KA1)
    (hcolS : ∀ n ∈ softWindow CL p X N, |uNode (Fz.step N) n - CL.uc p| < CL.η / 4)
    (hε2 : (Fz.step N * (CL.CBc * winCB CPC aplus * winCLam CL)) ^ 2 ≤ Cc / 4)
    (hLow : Cc * wmMass CL p X N ≤
      ∑ n ∈ (softWindow CL p X N).filter (fun n => CL.Zof p X N n ≤ -wmCut (CL.aOf p X N)),
        ((CL.chain p X N).phi (Fz.step N) 0 2 n) ^ 2) :
    Cc / (4 * KA1 ^ 2) * wmMass CL p X N ≤
      ∑ n ∈ (softWindow CL p X N).filter (fun n => CL.Zof p X N n ≤ -wmCut (CL.aOf p X N)),
        (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-(CL.Zof p X N n))) ^ 2 :=
  wm_conj_from_phi ((softWindow CL p X N).filter (fun n => CL.Zof p X N n ≤ -wmCut (CL.aOf p X N)))
    (fun n => (CL.chain p X N).phi (Fz.step N) 0 2 n)
    (fun n => kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-(CL.Zof p X N n)))
    (fun n => (CL.chain p X N).phi (Fz.step N) 0 2 n -
      (CL.chain p X N).AA 2 (uNode (Fz.step N) n) (Fz.step N) *
        (kappaBal (CL.aOf p X N) * U (CL.aOf p X N) (-(CL.Zof p X N n))))
    (fun n => Mbal (CL.aOf p X N) (CL.Zof p X N n))
    (fun n => (CL.chain p X N).AA 2 (uNode (Fz.step N) n) (Fz.step N))
    KA1 (Fz.step N * (CL.CBc * winCB CPC aplus * winCLam CL)) (wmMass CL p X N) Cc hKA1 hCc
    (fun n hn => hAbd n (Finset.mem_filter.mp hn).1)
    (fun n _ => by ring)
    (fun n hn => (wm_row2 pc CL aplus hp hX hN haplus hs1 (Finset.mem_filter.mp hn).1
      (hcolS n (Finset.mem_filter.mp hn).1)).2)
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun n _ _ => sq_nonneg _))
    (wmMass_nonneg CL p X N) hε2 hLow

/-- the arithmetic of the large branch: `r sqrt h >= sqrt Delta_0` forces `r >= 4 dp sqrt h + 1`. -/
lemma wm_r_ge (dp h Δ0 A : ℝ) (hdp : 0 < dp) (hh : 0 < h) (hΔ0 : 0 < Δ0) (hA : 0 ≤ A) (h1 : h ≤ Δ0 / 4)
    (h2 : h ≤ Real.sqrt Δ0 / (8 * dp)) (hAh : Δ0 < h * A) : 4 * (dp * Real.sqrt h) + 1 ≤ Real.sqrt A := by
  have hsqh : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hsqΔ : 0 < Real.sqrt Δ0 := Real.sqrt_pos.mpr hΔ0
  have hsh : Real.sqrt h ≤ Real.sqrt Δ0 / 2 := by
    by_contra hc
    push Not at hc
    have h2' : (Real.sqrt Δ0 / 2) ^ 2 < Real.sqrt h ^ 2 := pow_lt_pow_left₀ hc (by positivity) (by norm_num)
    rw [Real.sq_sqrt hh.le, div_pow, Real.sq_sqrt hΔ0.le] at h2'
    linarith
  have hdh : 4 * dp * h ≤ Real.sqrt Δ0 / 2 := by
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * dp)
    calc 4 * dp * h ≤ 4 * dp * (Real.sqrt Δ0 / (8 * dp)) := this
      _ = Real.sqrt Δ0 / 2 := by field_simp; ring
  have hrs : Real.sqrt Δ0 ≤ Real.sqrt A * Real.sqrt h := by
    rw [← Real.sqrt_mul hA, mul_comm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsq : Real.sqrt h * Real.sqrt h = h := Real.mul_self_sqrt hh.le
  refine le_of_mul_le_mul_right ?_ hsqh
  nlinarith

/-- **Step 3 of lem:tha-M, assembled (branch `h A > Delta_0`)**: for every `Delta_0 > 0` the three half-window mass bounds hold
for `h` small and `h A > Delta_0`. -/
lemma wm_large {cPC CPC : ℝ} (pc : ParabolicCylinderFacts U V cPC CPC) (CL : SoftEdgeChart Fz P m q U V Lm) (aplus : ℝ)
    {Δ0 : ℝ} (hΔ0 : 0 < Δ0) :
    ∃ c h0 : ℝ, 0 < c ∧ 0 < h0 ∧ ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 → ∀ N : ℕ, CL.N0 ≤ N →
      Fz.step N ≤ h0 → CL.aOf p X N ≤ aplus →
      Δ0 < Fz.step N * max (-CL.aOf p X N) 0 → WmClaims CL p X N c := by
  obtain ⟨-, hη, hdm, hdmp, -, -, -, -⟩ := CL.consts_pos
  have hdp : 0 < CL.dp := lt_of_lt_of_le hdm hdmp
  have hCPC : 0 < CPC := lt_of_lt_of_le pc.cPC_pos pc.cPC_le
  have hC1pos : 0 < winCB CPC aplus := by unfold winCB; positivity
  have hCLm := winCLam_nonneg CL
  have hM1 : 1 ≤ max 1 aplus := le_max_left _ _
  have hM0 : 0 < max 1 aplus := by linarith
  obtain ⟨κ0, hκ0def⟩ : ∃ κ0 : ℝ, κ0 = 15 / 64 * Δ0 := ⟨_, rfl⟩
  have hκ0 : 0 < κ0 := by rw [hκ0def]; positivity
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℝ, Cc = wmC3 CL κ0 * (CL.dm / (44 * CL.dp)) / 2 := ⟨_, rfl⟩
  have hCcpos : 0 < Cc := by
    have := wmC3_pos CL hκ0
    rw [hCc]; positivity
  obtain ⟨KA1, hKA1⟩ : ∃ KA1 : ℝ, KA1 = max CL.cs.KA 1 := ⟨_, rfl⟩
  have hKA1' : 1 ≤ KA1 := by rw [hKA1]; exact le_max_right _ _
  obtain ⟨Ec, hEc⟩ : ∃ Ec : ℝ, Ec = CL.CBc * winCB CPC aplus * winCLam CL := ⟨_, rfl⟩
  have hT4p : 0 < ((1 / (2 * max 1 aplus) / 10) / CL.dp) ^ 2 := by positivity
  have hTr1 : 0 < Δ0 / 4 := by positivity
  have hTr2 : 0 < Real.sqrt Δ0 / (8 * CL.dp) := by
    have := Real.sqrt_pos.mpr hΔ0
    positivity
  have hTe : 0 < Cc / (4 * (Ec ^ 2 + 1)) := by positivity
  refine ⟨Cc / (4 * KA1 ^ 2),
    min (winH1 CL) (min CL.η (min (farThr CL) (min (((1 / (2 * max 1 aplus) / 10) / CL.dp) ^ 2)
      (min (Δ0 / 4) (min (Real.sqrt Δ0 / (8 * CL.dp)) (min (Cc / (4 * (Ec ^ 2 + 1))) 1)))))),
    by positivity,
    lt_min (winH1_pos CL) (lt_min hη (lt_min (farThr_pos CL) (lt_min hT4p (lt_min hTr1
      (lt_min hTr2 (lt_min hTe one_pos)))))), ?_⟩
  intro p hp X hX N hN hstep haplus hAlarge
  have hh0 : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8⟩ := by simpa only [le_min_iff] using hstep
  have hsm0 : CL.dp * Real.sqrt (Fz.step N) ≤ 1 / (2 * max 1 aplus) / 10 :=
    wm_sqrt_small _ _ _ hdp (by positivity) hs4
  have hsqh : 0 < Real.sqrt (Fz.step N) := Real.sqrt_pos.mpr hh0
  have hr : 4 * (CL.dp * Real.sqrt (Fz.step N)) + 1 ≤ Real.sqrt (max (-CL.aOf p X N) 0) :=
    wm_r_ge _ _ _ _ hdp hh0 hΔ0 (le_max_right _ _) hs5 hs6 hAlarge
  have hκA : κ0 ≤ 15 / 64 * (Fz.step N * max (-CL.aOf p X N) 0) := by
    rw [hκ0def]; linarith
  have hL2 := wm_large2 CL hp hX hN aplus haplus hs1 hs2 hs3 hsm0 hr hκ0 hκA
  have hL1 := wm_large1 CL hp hX hN aplus haplus hs1 hs2 hs3 hsm0 hr hκ0 hκA
  obtain ⟨na, nb, hB, hW, hcl, hmmb⟩ := wm_large_ctx CL hp hX hN aplus haplus hs1 hs2 hs3 hsm0
  have hε2 : (Fz.step N * (CL.CBc * winCB CPC aplus * winCLam CL)) ^ 2 ≤ Cc / 4 := by
    rw [← hEc]
    have h6 : Fz.step N * (Ec ^ 2 + 1) ≤ Cc / 4 := by
      have := hs7
      rw [le_div_iff₀ (by positivity)] at this
      linarith [mul_comm (Fz.step N) (4 * (Ec ^ 2 + 1))]
    have h2 : Fz.step N ^ 2 ≤ Fz.step N := by nlinarith only [hs8, hh0]
    nlinarith only [mul_le_mul_of_nonneg_right h2 (sq_nonneg Ec), h6, sq_nonneg Ec, hh0]
  have hLow2 : Cc * wmMass CL p X N ≤
      ∑ n ∈ (softWindow CL p X N).filter (fun n => CL.Zof p X N n ≤ -wmCut (CL.aOf p X N)),
        ((CL.chain p X N).phi (Fz.step N) 0 2 n) ^ 2 := by
    refine le_trans (le_of_eq ?_) hL2
    rw [hCc]; ring
  have hLow1 : Cc * wmMass CL p X N ≤
      ∑ n ∈ (softWindow CL p X N).filter (fun n => wmCut (CL.aOf p X N) < CL.Zof p X N n),
        ((CL.chain p X N).phi (Fz.step N) 1 3 n) ^ 2 := by
    refine le_trans (le_of_eq ?_) hL1
    rw [hCc]; ring
  have hcolS : ∀ n ∈ softWindow CL p X N, |uNode (Fz.step N) n - CL.uc p| < CL.η / 4 := by
    intro n hn
    rw [hW] at hn
    exact hcl n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
  have hAbd : ∀ n ∈ softWindow CL p X N,
      |(CL.chain p X N).AA 2 (uNode (Fz.step N) n) (Fz.step N)| ≤ KA1 := by
    intro n hn
    obtain ⟨-, -, -, hj1, hNR, -, -⟩ := wm_rowfacts CL hp hX hN hs1 hn (hcolS n hn)
    rw [hKA1]
    exact le_trans (wm_AA_le CL hp hX hN hj1.le hNR) (le_max_left _ _)
  have hcle : Cc / (4 * KA1 ^ 2) ≤ Cc := by
    refine div_le_self hCcpos.le ?_
    have h := one_le_pow₀ (n := 2) hKA1'
    linarith only [h]
  have hLow3 := le_trans (mul_le_mul_of_nonneg_right hcle (wmMass_nonneg CL p X N)) hLow2
  refine ⟨?_, ?_, hLow3⟩
  · exact wm_conj1_large pc CL aplus hp hX hN haplus hs1 hKA1' hCcpos.le hAbd hcolS hε2 hLow1
  · exact wm_conj2_large pc CL aplus hp hX hN haplus hs1 hKA1' hCcpos.le hAbd hcolS hε2 hLow2

end LargeSums


section Final

/-- unscaling `(kappa g)^2` and shrinking the index set. -/
lemma wm_unscale (κ c mm : ℝ) (hκ : 0 < κ) (T T' : Finset ℤ) (g : ℤ → ℝ) (hT : T ⊆ T')
    (h : c * mm ≤ ∑ n ∈ T, (κ * g n) ^ 2) : c * κ⁻¹ ^ 2 * mm ≤ ∑ n ∈ T', g n ^ 2 := by
  have h1 : ∑ n ∈ T, (κ * g n) ^ 2 = κ ^ 2 * ∑ n ∈ T, g n ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by ring)
  have h2 : ∑ n ∈ T, g n ^ 2 ≤ ∑ n ∈ T', g n ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hT (fun n _ _ => sq_nonneg _)
  have hκ2 : 0 < κ⁻¹ ^ 2 := by positivity
  have h3 : κ⁻¹ ^ 2 * (c * mm) ≤ κ⁻¹ ^ 2 * (κ ^ 2 * ∑ n ∈ T, g n ^ 2) := by
    rw [← h1]; exact mul_le_mul_of_nonneg_left h hκ2.le
  have h4 : κ⁻¹ ^ 2 * (κ ^ 2 * ∑ n ∈ T, g n ^ 2) = ∑ n ∈ T, g n ^ 2 := by
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hκ.ne']; ring
  calc c * κ⁻¹ ^ 2 * mm = κ⁻¹ ^ 2 * (c * mm) := by ring
    _ ≤ ∑ n ∈ T, g n ^ 2 := by rw [h4] at h3; exact h3
    _ ≤ _ := h2

lemma wm_unscale3 (κ c mm : ℝ) (hκ : 0 < κ) (T T' : Finset ℤ) (φ : ℤ → ℝ) (hT : T ⊆ T')
    (h : c * mm ≤ ∑ n ∈ T, φ n ^ 2) : c * κ⁻¹ ^ 2 * mm ≤ ∑ n ∈ T', (φ n / κ) ^ 2 := by
  have h1 : ∑ n ∈ T, (φ n / κ) ^ 2 = κ⁻¹ ^ 2 * ∑ n ∈ T, φ n ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by rw [div_eq_inv_mul, mul_pow])
  have h2 : ∑ n ∈ T, (φ n / κ) ^ 2 ≤ ∑ n ∈ T', (φ n / κ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hT (fun n _ _ => sq_nonneg _)
  have hκ2 : 0 < κ⁻¹ ^ 2 := by positivity
  calc c * κ⁻¹ ^ 2 * mm = κ⁻¹ ^ 2 * (c * mm) := by ring
    _ ≤ κ⁻¹ ^ 2 * ∑ n ∈ T, φ n ^ 2 := mul_le_mul_of_nonneg_left h hκ2.le
    _ = ∑ n ∈ T, (φ n / κ) ^ 2 := h1.symm
    _ ≤ _ := h2

/-- **lem:tha-M** (`PropThaM`), from the parabolic-cylinder facts and the chart (with the corrector field `corr_PC`). -/
theorem propThaM_of_facts {cPC CPC : ℝ} (CL : SoftEdgeChart Fz P m q U V Lm)
    (aplus : ℝ) : PropThaM Fz P m q U V CL aplus cPC CPC := by
  intro pc r _
  obtain ⟨-, hη, hdm, hdmp, -, -, -, -⟩ := CL.consts_pos
  have hdp : 0 < CL.dp := lt_of_lt_of_le hdm hdmp
  have hCPC : 0 < CPC := lt_of_lt_of_le pc.cPC_pos pc.cPC_le
  have hC1pos : 0 < winCB CPC aplus := by unfold winCB; positivity
  obtain ⟨c1, hc1pos, hc1⟩ := wm_c1 pc aplus
  have hΔ : 0 < wmDelta c1 (winCB CPC aplus ^ 2) CL.dp := wmDelta_pos hc1pos (by positivity) hdp
  obtain ⟨cs, hs0, hcs, hhs, hsm⟩ := wm_small pc CL aplus hc1pos hc1
  obtain ⟨cl, hl0, hcl, hhl, hlg⟩ := wm_large pc CL aplus hΔ
  refine ⟨min cs cl, min hs0 hl0, lt_min hcs hcl, lt_min hhs hhl, ?_⟩
  intro p hp X hX N hN hstep haplus s hs
  have hsmall := (le_min_iff.mp hstep).1
  have hlarge := (le_min_iff.mp hstep).2
  have hclaims : WmClaims CL p X N (min cs cl) := by
    by_cases hA : Fz.step N * max (-CL.aOf p X N) 0 ≤ wmDelta c1 (winCB CPC aplus ^ 2) CL.dp
    · exact (hsm p hp X hX N hN hsmall haplus hA).mono (min_le_left _ _) (wmMass_nonneg CL p X N)
    · push Not at hA
      exact (hlg p hp X hX N hN hlarge haplus hA).mono (min_le_right _ _) (wmMass_nonneg CL p X N)
  obtain ⟨h1, h2, h3⟩ := hclaims
  have hκ := wm_kappa_pos' (CL.aOf p X N)
  have hsl := abs_le.mp hs
  have hcutdef : wmCut (CL.aOf p X N) = Real.sqrt (max (-CL.aOf p X N) 0) +
      (1 + max (-CL.aOf p X N) 0) ^ (-(1 : ℝ) / 6) / 4 := rfl
  rw [← hcutdef] at hsl
  refine ⟨?_, ?_, ?_⟩
  · refine wm_unscale _ _ _ hκ _ _ (fun n => U (CL.aOf p X N) (CL.Zof p X N n)) ?_ h1
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, lt_of_le_of_lt hsl.2 hn.2⟩
  · refine wm_unscale _ _ _ hκ _ _ (fun n => U (CL.aOf p X N) (-(CL.Zof p X N n))) ?_ h2
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, le_trans hn.2 (by linarith [hsl.1])⟩
  · refine wm_unscale3 _ _ _ hκ _ _ (fun n => (CL.chain p X N).phi (Fz.step N) 0 2 n) ?_ h3
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, le_trans hn.2 (by linarith [hsl.1])⟩

end Final

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.wm_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.wm_small

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.wm_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.wm_large

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.propThaM_of_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.propThaM_of_facts

end Chart

end FormalResearch.JacobiEigenvectors.TheoremA

end

end
