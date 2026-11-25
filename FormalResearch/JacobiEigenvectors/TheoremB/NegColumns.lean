module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.NegTransport
public import FormalResearch.JacobiEigenvectors.TheoremA.StepZeroCovered
public import FormalResearch.JacobiEigenvectors.TheoremB.TwoOrdersBulk

/-!
# Paper J, Theorem B, L3.2 (soft columns): the lower-edge reduction by `negFamily`, and the soft analogue of `bulk_col_clause`

Source: Paper J `app_thmB.tex`, proof of `prop:thb-inputs` (I1) ("A soft column in `Sigma^+` is the vector of Proposition tha-W2 (2), with the fixed scalars ..., sewn at the fixed row `n_c` instead of `u_*`; this row lies in
the window for every soft column (Proposition tha-splice (b), Lemma tha-Mflat), and the same estimate (I1), with `n_c` in place of `n_nu`, holds.  A column in `Sigma^-` is `D_-` times such a vector for `-D_- J_h D_-`, and `D_- Psi_k` is the eigenvector
of `-D_- J_h D_-` in the gauge `(.)_0 > 0`, so (I1) holds for it as well").  This is the soft half of `PropThaSpliceTwoOrders` (L3.2); the bulk half is `twoOrders_bulk_columns`.

## Proved here (axiom-pinned)

* **The lower-edge reduction (unconditional).**  `compColumn_lower`: for an energy outside all blocks and not above `Jhi`, `compColumn = (-1)^n softColAt softLoL softLoR (-X) ..`.  `compColumn_lower_sub`: its difference to the eigenvector
  `Psi_k` of `J_h` is `(-1)^n` times the difference of the `softLoL` column at `-X_k` to `eigVec (negU U) (rev k)`, the eigenvector of the transported system (`eigVec_negU_rev`).  `compMatrix_lower_col_l2`: hence the `l^2` column error of `compMatrix`
  equals that of the upper-edge column of the chart family `negFamily (frozenFamily F Kidx)` against the eigen-system `(negX X, negU U)` (a genuine eigen-system of its matrix at `atStep F mu N`, `IsEigenSystem.neg_frozen`).
* **`soft_col_clause`** (the soft analogue of `bulk_col_clause`, for any soft chart pair `(CL, CR)` of any family `Fz`, hence for the upper edge and, with `Fz = negFamily (frozenFamily F Kidx)`, the lower one): the column `softColAt CL CR p X N n_c` with the **fixed
  fold row** `n_c = nearestRow u_c` is within `C eta` of the eigenvector in `l^2`.  It is `(hat N(n_c)/hat N) hat Psi^{(n_c)}` (the paper's route): from the three clauses of `PropThaSpliceSoft` (normaliser ratio, `n_c in Omega`, `|Psi - spliced| <= C eta softEnv`),
  `sum softEnv^2 <= CS` and `||Psi_k||_2 = 1`.  The matching clause of `PropThaSpliceSoft` is not needed (the normaliser ratio replaces the matching on the rows between `n_c` and the standard split).
* **`compMatrix_lower_col`**: the lower soft columns of `compMatrix CI spl`: `l^2` error `<= C eta(h)`, from `soft_col_clause` for `(softLoL, softLoR)` and the transport.  Window membership of the lower soft energies is `spectrumCovered` (proved, `StepZeroCovered.lean`);
  `N >= N_0` is encoded in `h <= h_0`.
* `stdAssump_neg`: `StdAssump F P Kd r -> StdAssump (negFamily F) P Kd r` (bridge (a) for the gauge family: `hyp_neg`, `ek_neg`), so `StdAssump (negFamily (frozenFamily F Kidx)) ..` follows from that of the frozen family.

## What the lower edge needs (premises of `compMatrix_lower_col`, all paper statements, none proved here)

(i) `PropThaSpliceSoft CI.softLoL CI.softLoR eta` (statement frozen, `1 <= m`, `SoftMirror` = `CI.mirror_lo`): it is the *upper-edge* statement `PropThaSpliceSoft` for the family `negFamily (frozenFamily F Kidx)`, so it is proved by the same proof as the upper
edge (agent X's soft assembly, `PropThaW2` (2)-(4)); (ii) `sum softEnv^2 <= CS` (second clause of `PropThaW2` (2) for the chart `softLoL`, composed with Step 0); (iii) `a <= 1` at every lower soft eigenvalue (Step 0 gives `X_k >= X_s^- - C h^2`, hence `alpha >= -C h^2` and
`a = -(mu_0 + ...)/h <= C h`; not formalised); (iv) `StdAssump (negFamily (frozenFamily F Kidx)) (paramSet K t0) (q/2) r` (`stdAssump_neg` from the frozen family's, with the F-t0 restriction); (v) `eta` is `o(1)` and nonnegative on `(0, 1]`.
The upper soft columns are the same statement with `(softUpL, softUpR)` and no transport (`soft_col_clause`).

## Differences from the paper

The paper shows `||(G^{[r]} - U) e_k||_2 <= C eta_r` for the soft columns via the normaliser ratio `hat N(n_c)/hat N` of `prop:tha-splice` (b) and the `l^2` norm of `Psi_k`; so does `soft_col_clause` (this is a different route from that of
`bulk_col_clause`, which uses the matching on the rows between the splice and the standard split).  `eta` is a parameter (`h^m` or `etaR m (m+1)`), required small (`hetas`) so that `hat N(n_c) != 0`.

## Not formalised

`PropThaSpliceSoft` and the `sum softEnv^2` clause themselves (soft assembly), the bound `a <= 1`, the F-t0 restriction of the soft charts, and the assembly of `propThaSpliceTwoOrders` (columns are bulk, upper soft or lower soft: `compColumn` splits on these in this order).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA

open scoped Classical

variable {Par : Type*} [TopologicalSpace Par]

/-! ### The lower-edge reduction -/

section Reduction

variable {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- The third case of `compColumn`: the lower soft edge is the gauge vector `(-1)^n` times the column of the gauge family at `-X`, sewn at the fold row of the chart `softLoL`. -/
theorem compColumn_lower (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (spl : Fin CI.nb → ℝ) (μ : Par) (N : ℕ) (X : ℝ)
    (hb : ¬ ∃ ν : Fin CI.nb, CI.lo ν ≤ X ∧ X ≤ CI.hi ν) (hu : ¬ CI.Jhi < X) (n : ℤ) :
    compColumn CI spl μ N X n = (-1 : ℝ) ^ n *
      softColAt CI.softLoL CI.softLoR (atStep F μ N) (-X) N (nearestRow (F.step N) (CI.softLoL.uc (atStep F μ N))) n := by
  unfold compColumn
  rw [dite_eq_right hb, ite_eq_right hu]

/-- **The lower column minus the eigenvector is `D_-` times the upper-edge column of the gauge family minus the transported eigenvector** (`eigVec_negU_rev`). -/
theorem compColumn_lower_sub (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (spl : Fin CI.nb → ℝ) (μ : Par) (N : ℕ)
    (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (k : Fin (N + 1)) (X : ℝ)
    (hb : ¬ ∃ ν : Fin CI.nb, CI.lo ν ≤ X ∧ X ≤ CI.hi ν) (hu : ¬ CI.Jhi < X) (n : ℤ) :
    compColumn CI spl μ N X n - eigVec Um k n = (-1 : ℝ) ^ n *
      (softColAt CI.softLoL CI.softLoR (atStep F μ N) (-X) N (nearestRow (F.step N) (CI.softLoL.uc (atStep F μ N))) n -
        eigVec (negU Um) (Fin.rev k) n) := by
  rw [compColumn_lower CI spl μ N X hb hu n, eigVec_negU_rev]
  have h : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; norm_num
  calc _ = (-1 : ℝ) ^ n * softColAt CI.softLoL CI.softLoR (atStep F μ N) (-X) N (nearestRow (F.step N) (CI.softLoL.uc (atStep F μ N))) n
        - ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) * eigVec Um k n := by rw [h]; ring
    _ = _ := by ring

/-- **The `l^2` error of a lower soft column of `compMatrix` is the `l^2` error of the upper-edge column of the gauge family against the transported eigenvector.** -/
theorem compMatrix_lower_col_l2 (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (spl : Fin CI.nb → ℝ) (μ : Par) (N : ℕ)
    (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (k : Fin (N + 1))
    (hb : ¬ ∃ ν : Fin CI.nb, CI.lo ν ≤ Xs k ∧ Xs k ≤ CI.hi ν) (hu : ¬ CI.Jhi < Xs k) :
    FormalResearch.JB.jbL2 Finset.univ (fun i : Fin (N + 1) => compMatrix CI spl μ N Xs i k - Um i k) =
      FormalResearch.JB.jbL2 Finset.univ (fun i : Fin (N + 1) =>
        softColAt CI.softLoL CI.softLoR (atStep F μ N) (-(Xs k)) N (nearestRow (F.step N) (CI.softLoL.uc (atStep F μ N))) ((i : ℕ) : ℤ) -
          negU Um i (Fin.rev k)) := by
  unfold FormalResearch.JB.jbL2
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  beta_reduce
  have hc : compMatrix CI spl μ N Xs i k = compColumn CI spl μ N (Xs k) ((i : ℕ) : ℤ) := rfl
  rw [hc, compColumn_lower CI spl μ N (Xs k) hb hu, negU_rev]
  have h : (-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  rw [zpow_natCast]
  calc ((-1 : ℝ) ^ (i : ℕ) * softColAt CI.softLoL CI.softLoR (atStep F μ N) (-(Xs k)) N
          (nearestRow (F.step N) (CI.softLoL.uc (atStep F μ N))) ((i : ℕ) : ℤ) - Um i k) ^ 2
      = ((-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ)) * (softColAt CI.softLoL CI.softLoR (atStep F μ N) (-(Xs k)) N
          (nearestRow (F.step N) (CI.softLoL.uc (atStep F μ N))) ((i : ℕ) : ℤ) - (-1 : ℝ) ^ (i : ℕ) * Um i k) ^ 2 := by
        have : (-1 : ℝ) ^ (i : ℕ) * softColAt CI.softLoL CI.softLoR (atStep F μ N) (-(Xs k)) N
            (nearestRow (F.step N) (CI.softLoL.uc (atStep F μ N))) ((i : ℕ) : ℤ) - Um i k =
          (-1 : ℝ) ^ (i : ℕ) * (softColAt CI.softLoL CI.softLoR (atStep F μ N) (-(Xs k)) N
            (nearestRow (F.step N) (CI.softLoL.uc (atStep F μ N))) ((i : ℕ) : ℤ) - (-1 : ℝ) ^ (i : ℕ) * Um i k) := by
          calc _ = (-1 : ℝ) ^ (i : ℕ) * softColAt CI.softLoL CI.softLoR (atStep F μ N) (-(Xs k)) N
                (nearestRow (F.step N) (CI.softLoL.uc (atStep F μ N))) ((i : ℕ) : ℤ)
                - ((-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ)) * Um i k := by rw [h]; ring
            _ = _ := by ring
        rw [this]; ring
    _ = _ := by rw [h]; ring

end Reduction

/-! ### The soft analogue of `bulk_col_clause` -/

/-- **The soft column with the fixed fold row is within `C eta` of the eigenvector in `l^2`** (prop:tha-splice (b), (c) for one soft edge and one order; `app_thmB`: the column is
`(hat N(n_c)/hat N) hat Psi^{(n_c)}`).  Premises: `PropThaSpliceSoft CL CR eta` (the paper's own intermediate statement, proved by the soft assembly), and the `l^2` bound `sum softEnv^2 <= CS` of `PropThaW2` (2); `eta` nonnegative on `(0,1]` and
small.  `softColAt .. n_c` has the standard normaliser `softNorm` and standard `hat kappa`, so it equals `rho * splicedVec` with `rho = hat N(n_c)/hat N`, `|rho - 1| <= C eta` (first clause of `PropThaSpliceSoft`). -/
theorem soft_col_clause {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}
    (hf : ParabolicCylinderFacts U V cPC CPC) (CL : SoftEdgeChart Fz P m q U V (fun _ => 1)) (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1)) (η : ℝ → ℝ)
    (hη0 : ∀ h : ℝ, 0 < h → h ≤ 1 → 0 ≤ η h)
    (hetas : ∀ ε : ℝ, 0 < ε → ∃ h1 : ℝ, 0 < h1 ∧ ∀ h : ℝ, 0 < h → h ≤ h1 → |η h| ≤ ε)
    (hS : PropThaSpliceSoft CL CR η cPC CPC) (hm : 1 ≤ m) (hmir : SoftMirror CL CR) (r : ℕ) (hr : StdAssump Fz P (q / 2) r)
    (hEnv : ∃ CS h1 : ℝ, 0 < h1 ∧ ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 → ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 → CL.aOf p X N ≤ 1 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
        ∀ k : Fin (N + 1), Xs k = X → ∑ n ∈ rowsOf N, softEnv CL CR p X N n ^ 2 ≤ CS) :
    ∃ C h1 : ℝ, 0 < h1 ∧ ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 → ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 → CL.aOf p X N ≤ 1 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
        ∀ k : Fin (N + 1), Xs k = X →
          FormalResearch.JB.jbL2 Finset.univ (fun i : Fin (N + 1) =>
            softColAt CL CR p X N (nearestRow (Fz.step N) (CL.uc p)) ((i : ℕ) : ℤ) - Um i k) ≤ C * η (Fz.step N) := by
  obtain ⟨C0, h0, hh0, hmain⟩ := hS hf hm hmir r hr
  obtain ⟨CS, h1, hh1, hSum⟩ := hEnv
  obtain ⟨hη1, hhη1, hηsmall⟩ := hetas (1 / (2 * (|C0| + 1))) (by positivity)
  refine ⟨|C0| * Real.sqrt (8 * |CS| + 2), min (min (min h0 h1) hη1) 1, lt_min (lt_min (lt_min hh0 hh1) hhη1) one_pos, ?_⟩
  intro p hp X hX N hN hstep ha Xs Um hE k hk
  have hst : 0 < Fz.step N := FormalResearch.JB.stepSize_pos Fz.L_pos N
  have hs0 : Fz.step N ≤ h0 := hstep.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hs1 : Fz.step N ≤ h1 := hstep.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hsη : Fz.step N ≤ hη1 := hstep.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hs1' : Fz.step N ≤ 1 := hstep.trans (min_le_right _ _)
  obtain ⟨hns, hrest⟩ := (hmain p hp X hX N hN hs0 ha)
  set ns : ℤ := nearestRow (Fz.step N) (CL.uc p) with hnsdef
  obtain ⟨⟨hc1, -⟩, hev⟩ := hrest ns hns Xs Um hE k hk
  have hsum := hSum p hp X hX N hN hs1 ha Xs Um hE k hk
  set ηh : ℝ := η (Fz.step N) with hηh
  have hηnn : 0 ≤ ηh := hη0 _ hst hs1'
  have hηab : |ηh| ≤ 1 / (2 * (|C0| + 1)) := hηsmall _ hst hsη
  set A : ℝ := |C0| * ηh with hA
  have hA0 : 0 ≤ A := mul_nonneg (abs_nonneg _) hηnn
  have hAhalf : A ≤ 1 / 2 := by
    rw [abs_of_nonneg hηnn] at hηab
    calc A = |C0| * ηh := rfl
      _ ≤ |C0| * (1 / (2 * (|C0| + 1))) := mul_le_mul_of_nonneg_left hηab (abs_nonneg _)
      _ ≤ 1 / 2 := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [abs_nonneg C0]
  have hC0A : |C0 * ηh| ≤ A := by rw [abs_mul, abs_of_nonneg hηnn]
  -- the notation
  set ψL := CL.psiHatL p X N with hψL
  set ψR := softSeqR CR p X N with hψR
  set Ω := softWindow CL p X N with hΩ
  set gN := glueNormAt ψL ψR Ω (rowsOf N) ns with hgN
  set sN := softNorm CL CR p X N with hsN
  have hρ1 : |gN / sN - 1| ≤ A := hc1.trans ((le_abs_self _).trans hC0A)
  have hgN0 : gN ≠ 0 := by
    intro h0'
    rw [h0', zero_div] at hρ1
    have : |(0 : ℝ) - 1| = 1 := by norm_num
    rw [this] at hρ1
    linarith
  set ρ : ℝ := gN / sN with hρ
  have hρ2 : |ρ| ≤ 2 := by
    have := abs_sub_abs_le_abs_sub ρ 1
    rw [abs_one] at this
    linarith
  -- the column is `rho` times the spliced vector
  have hcol : ∀ n : ℤ, softColAt CL CR p X N ns n = ρ * splicedVec ψL ψR Ω (rowsOf N) ns n := by
    intro n
    unfold softColAt glueVecAt splicedVec
    by_cases hn : n ≤ ns
    · rw [ite_eq_left hn, ite_eq_left hn]
      show ψL n / sN = gN / sN * (ψL n / gN)
      field_simp
    · rw [ite_eq_right hn, ite_eq_right hn]
      show glueKappa ψL ψR Ω * ψR n / sN = gN / sN * (glueKappa ψL ψR Ω * ψR n / gN)
      field_simp
  -- the row bound, squared
  have hrow : ∀ n ∈ rowsOf N, (softColAt CL CR p X N ns n - eigVec Um k n) ^ 2 ≤
      8 * A ^ 2 * softEnv CL CR p X N n ^ 2 + 2 * A ^ 2 * eigVec Um k n ^ 2 := by
    intro n hn
    set sp := splicedVec ψL ψR Ω (rowsOf N) ns n with hsp
    have hb := hev n hn
    -- |Psi - sp| <= C0 eta env
    have hb0 : (eigVec Um k n - sp) ^ 2 ≤ (C0 * ηh) ^ 2 * softEnv CL CR p X N n ^ 2 := by
      rw [← mul_pow, ← sq_abs (eigVec Um k n - sp)]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have hCsq : (C0 * ηh) ^ 2 ≤ A ^ 2 := by
      rw [← sq_abs (C0 * ηh)]
      exact pow_le_pow_left₀ (abs_nonneg _) hC0A 2
    have hρsq : ρ ^ 2 ≤ 4 := by
      rw [← sq_abs ρ]
      have := pow_le_pow_left₀ (abs_nonneg ρ) hρ2 2
      linarith
    have hρ1sq : (ρ - 1) ^ 2 ≤ A ^ 2 := by
      rw [← sq_abs (ρ - 1)]
      exact pow_le_pow_left₀ (abs_nonneg _) hρ1 2
    have e : softColAt CL CR p X N ns n - eigVec Um k n = ρ * (sp - eigVec Um k n) + (ρ - 1) * eigVec Um k n := by
      rw [hcol n]; ring
    rw [e]
    have hE2 : 0 ≤ softEnv CL CR p X N n ^ 2 := sq_nonneg _
    calc (ρ * (sp - eigVec Um k n) + (ρ - 1) * eigVec Um k n) ^ 2
        ≤ 2 * (ρ * (sp - eigVec Um k n)) ^ 2 + 2 * ((ρ - 1) * eigVec Um k n) ^ 2 := by
          linarith [sq_nonneg (ρ * (sp - eigVec Um k n) - (ρ - 1) * eigVec Um k n)]
      _ = 2 * (ρ ^ 2 * (eigVec Um k n - sp) ^ 2) + 2 * ((ρ - 1) ^ 2 * eigVec Um k n ^ 2) := by ring
      _ ≤ 2 * (4 * ((C0 * ηh) ^ 2 * softEnv CL CR p X N n ^ 2)) + 2 * (A ^ 2 * eigVec Um k n ^ 2) := by
          have h1 : ρ ^ 2 * (eigVec Um k n - sp) ^ 2 ≤ 4 * ((C0 * ηh) ^ 2 * softEnv CL CR p X N n ^ 2) :=
            mul_le_mul hρsq hb0 (sq_nonneg _) (by norm_num)
          have h2 : (ρ - 1) ^ 2 * eigVec Um k n ^ 2 ≤ A ^ 2 * eigVec Um k n ^ 2 :=
            mul_le_mul_of_nonneg_right hρ1sq (sq_nonneg _)
          linarith
      _ ≤ 8 * A ^ 2 * softEnv CL CR p X N n ^ 2 + 2 * A ^ 2 * eigVec Um k n ^ 2 := by
          have : (C0 * ηh) ^ 2 * softEnv CL CR p X N n ^ 2 ≤ A ^ 2 * softEnv CL CR p X N n ^ 2 :=
            mul_le_mul_of_nonneg_right hCsq hE2
          linarith
  -- from rows to the `l^2` norm
  have hCS0 : 0 ≤ CS := (Finset.sum_nonneg fun n _ => sq_nonneg (softEnv CL CR p X N n)).trans hsum
  have hΨ : ∑ n ∈ rowsOf N, eigVec Um k n ^ 2 = 1 := eigVec_sq_sum N Um hE.orth k
  have hsq : ∑ n ∈ rowsOf N, (softColAt CL CR p X N ns n - eigVec Um k n) ^ 2 ≤ A ^ 2 * (8 * |CS| + 2) := by
    calc _ ≤ ∑ n ∈ rowsOf N, (8 * A ^ 2 * softEnv CL CR p X N n ^ 2 + 2 * A ^ 2 * eigVec Um k n ^ 2) :=
          Finset.sum_le_sum hrow
      _ = 8 * A ^ 2 * ∑ n ∈ rowsOf N, softEnv CL CR p X N n ^ 2 + 2 * A ^ 2 * ∑ n ∈ rowsOf N, eigVec Um k n ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 8 * A ^ 2 * CS + 2 * A ^ 2 * 1 := by
          rw [hΨ]
          have := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 8 * A ^ 2)
          linarith
      _ ≤ A ^ 2 * (8 * |CS| + 2) := by
          have := mul_le_mul_of_nonneg_left (le_abs_self CS) (by positivity : (0 : ℝ) ≤ 8 * A ^ 2)
          linarith
  unfold FormalResearch.JB.jbL2
  have hconv : ∑ i : Fin (N + 1), (softColAt CL CR p X N ns ((i : ℕ) : ℤ) - Um i k) ^ 2 =
      ∑ n ∈ rowsOf N, (softColAt CL CR p X N ns n - eigVec Um k n) ^ 2 := by
    rw [sum_rowsOf_eq_fin N (fun n => (softColAt CL CR p X N ns n - eigVec Um k n) ^ 2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hev' : eigVec Um k (i.val : ℤ) = Um i k := extV_fin (fun j => Um j k) i
    rw [hev']
  rw [hconv]
  calc Real.sqrt _ ≤ Real.sqrt (A ^ 2 * (8 * |CS| + 2)) := Real.sqrt_le_sqrt hsq
    _ = A * Real.sqrt (8 * |CS| + 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA0]
    _ = |C0| * Real.sqrt (8 * |CS| + 2) * η (Fz.step N) := by rw [hA]; ring

/-! ### The lower soft columns of `compMatrix` -/

/-- `n_0 <= N` once `h <= L/(n_0 + 1)`. -/
theorem le_of_step_le (G : SymbolFamily Par) (n0 N : ℕ) (h : G.step N ≤ G.L / ((n0 : ℝ) + 1)) : n0 ≤ N := by
  have hpos : 0 < G.step N := FormalResearch.JB.stepSize_pos G.L_pos N
  have h1 : G.step N * ((n0 : ℝ) + 1) ≤ G.L := by
    rwa [le_div_iff₀ (by positivity)] at h
  rw [← step_mul_succ G N] at h1
  have h2 := le_of_mul_le_mul_left h1 hpos
  have h3 : (n0 : ℝ) ≤ N := by linarith
  exact_mod_cast h3

section LowerCols

variable {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- **The lower soft columns of `hat G^{[m]}`** (the third case of `compColumn`; `prop:tha-splice` (c) for `Sigma^-`): for every energy outside all blocks and not above `J_hi`, the `l^2` column error is `<= C eta`.  Premises (see the module docstring):
`PropThaSpliceSoft CI.softLoL CI.softLoR eta`, the `l^2` envelope bound for the chart `softLoL`, `a <= 1` at the lower soft eigenvalues, `StdAssump` of the gauge chart family; window membership is `spectrumCovered` (proved).
The proof is the transport: the eigen-system `(negX X, negU U)` of the matrix of `negFamily (frozenFamily F Kidx)` at `atStep F mu N`, whose column `rev k` is at the energy `-X_k` and is `D Psi_k`, and `soft_col_clause` for the chart pair `(softLoL, softLoR)`. -/
theorem compMatrix_lower_col (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (spl : Fin CI.nb → ℝ) (η : ℝ → ℝ)
    (hη0 : ∀ h : ℝ, 0 < h → h ≤ 1 → 0 ≤ η h)
    (hetas : ∀ ε : ℝ, 0 < ε → ∃ h1 : ℝ, 0 < h1 ∧ ∀ h : ℝ, 0 < h → h ≤ h1 → |η h| ≤ ε)
    (hS : PropThaSpliceSoft CI.softLoL CI.softLoR η cPC CPC) (hm : 1 ≤ m) (r : ℕ)
    (hr : StdAssump (negFamily (frozenFamily F Kidx)) (paramSet K t0) (q / 2) r)
    (hEnv : ∃ CS h1 : ℝ, 0 < h1 ∧ ∀ p ∈ paramSet K t0, ∀ X, |X - (negFamily (frozenFamily F Kidx)).bandHi p| ≤ CI.softLoL.δ0 →
      ∀ N : ℕ, max CI.softLoL.N0 CI.softLoR.N0 ≤ N → (negFamily (frozenFamily F Kidx)).step N ≤ h1 → CI.softLoL.aOf p X N ≤ 1 →
        ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ),
          IsEigenSystem ((negFamily (frozenFamily F Kidx)).jacobiMat p N) Xs Um →
          ∀ k : Fin (N + 1), Xs k = X → ∑ n ∈ rowsOf N, softEnv CI.softLoL CI.softLoR p X N n ^ 2 ≤ CS)
    (hA1 : ∃ h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ∀ j : Fin (N + 1), (¬ ∃ ν : Fin CI.nb, CI.lo ν ≤ Xs j ∧ Xs j ≤ CI.hi ν) → ¬ CI.Jhi < Xs j →
          CI.softLoL.aOf (atStep F μ N) (-(Xs j)) N ≤ 1)
    (hK : IsCompact K) (hH : HypOn F K) (hD : DM F K 1) :
    ∃ C h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 → F.step N ≤ t0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ∀ j : Fin (N + 1), (¬ ∃ ν : Fin CI.nb, CI.lo ν ≤ Xs j ∧ Xs j ≤ CI.hi ν) → ¬ CI.Jhi < Xs j →
          FormalResearch.JB.jbL2 Finset.univ (fun i : Fin (N + 1) => compMatrix CI spl μ N Xs i j - Um i j) ≤ C * η (F.step N) := by
  obtain ⟨C, h1, hh1, hcl⟩ := soft_col_clause CI.pc CI.softLoL CI.softLoR η hη0 hetas hS hm CI.mirror_lo r hr hEnv
  obtain ⟨h0c, hh0c, hcov⟩ := spectrumCovered_of_dm1 CI hK hH hD
  obtain ⟨hA0, hhA0, hAh⟩ := hA1
  have hLp : 0 < F.L / ((max CI.softLoL.N0 CI.softLoR.N0 : ℕ) + 1 : ℝ) := div_pos F.L_pos (by positivity)
  refine ⟨C, min (min (min h1 h0c) hA0) (F.L / (((max CI.softLoL.N0 CI.softLoR.N0 : ℕ) : ℝ) + 1)),
    lt_min (lt_min (lt_min hh1 hh0c) hhA0) hLp, ?_⟩
  intro μ hμ N hN ht Xs Um hE j hb hu
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hs1 : F.step N ≤ h1 := hN.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hsc : F.step N ≤ h0c := hN.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hsA : F.step N ≤ hA0 := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hsN : F.step N ≤ F.L / (((max CI.softLoL.N0 CI.softLoR.N0 : ℕ) : ℝ) + 1) := hN.trans (min_le_right _ _)
  have hN0 : max CI.softLoL.N0 CI.softLoR.N0 ≤ N := le_of_step_le F _ N hsN
  have hwin : |-(Xs j) - (negFamily (frozenFamily F Kidx)).bandHi (atStep F μ N)| ≤ CI.softLoL.δ0 := by
    rcases hcov μ hμ N hsc ht Xs Um hE j with h | ⟨_, hJ, _⟩ | ⟨_, _, h⟩
    · exact absurd h hb
    · exact absurd hJ hu
    · exact h
  have hp : atStep F μ N ∈ paramSet K t0 := ⟨hμ, ⟨by unfold atStep; linarith, ht⟩⟩
  have hE' : IsEigenSystem ((negFamily (frozenFamily F Kidx)).jacobiMat (atStep F μ N) N) (negX Xs) (negU Um) :=
    hE.neg_frozen (Kidx := Kidx)
  have hres := hcl (atStep F μ N) hp (-(Xs j)) hwin N hN0 hs1 (hAh μ hμ N hsA Xs Um hE j hb hu) (negX Xs) (negU Um) hE'
    (Fin.rev j) (negX_rev Xs j)
  rw [compMatrix_lower_col_l2 CI spl μ N Xs Um j hb hu]
  exact hres

end LowerCols

/-! ### Bridge (a) for the gauge family: `StdAssump` of `negFamily` -/

section StdNeg

open Set
open scoped Pointwise

theorem Xsp_neg (L : ℝ) (G0 B0 : ℝ → ℝ) : Xsp L G0 (fun u => -B0 u) = -Xsm L G0 B0 := by
  unfold Xsp Xsm
  have himg : fPlus L G0 (fun u => -B0 u) '' Icc 0 L = -(fMinus L G0 B0 '' Icc 0 L) := by
    ext y
    simp only [Set.mem_image, Set.mem_neg]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, by simp only [fPlus, fMinus]; ring⟩
    · rintro ⟨u, hu, hy⟩
      exact ⟨u, hu, by simp only [fPlus, fMinus] at hy ⊢; linarith⟩
  rw [himg, Real.sSup_neg]

theorem Xsm_neg (L : ℝ) (G0 B0 : ℝ → ℝ) : Xsm L G0 (fun u => -B0 u) = -Xsp L G0 B0 := by
  unfold Xsp Xsm
  have himg : fMinus L G0 (fun u => -B0 u) '' Icc 0 L = -(fPlus L G0 B0 '' Icc 0 L) := by
    ext y
    simp only [Set.mem_image, Set.mem_neg]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, by simp only [fPlus, fMinus]; ring⟩
    · rintro ⟨u, hu, hy⟩
      exact ⟨u, hu, by simp only [fPlus, fMinus] at hy ⊢; linarith⟩
  rw [himg, Real.sInf_neg]

theorem Tfun_neg (L : ℝ) (G0 B0 : ℝ → ℝ) (X u : ℝ) : Tfun L G0 (fun u => -B0 u) X u = Tfun L G0 B0 (-X) u := by
  simp only [Tfun]; ring

theorem fPlus_neg (L : ℝ) (G0 B0 : ℝ → ℝ) : fPlus L G0 (fun u => -B0 u) = fun u => -fMinus L G0 B0 u := by
  funext u; simp only [fPlus, fMinus]; ring

theorem fMinus_neg (L : ℝ) (G0 B0 : ℝ → ℝ) : fMinus L G0 (fun u => -B0 u) = fun u => -fPlus L G0 B0 u := by
  funext u; simp only [fPlus, fMinus]; ring

/-- (H1)--(H3) are invariant under `B_0 -> -B_0` (`f_+ <-> -f_-`, `T(.; X) <-> T(.; -X)`). -/
theorem hyp_neg {L : ℝ} {G0 B0 : ℝ → ℝ} {g : ℝ} (h : Hyp L G0 B0 g) : Hyp L G0 (fun u => -B0 u) g where
  gstar_pos := h.gstar_pos
  G0_lb := h.G0_lb
  H2 := by
    intro X hX1 hX2
    rw [Xsm_neg] at hX1
    rw [Xsp_neg] at hX2
    obtain ⟨a, b, ha0, hab, hbL, hset, ha, hb, ha0', hbL'⟩ := h.H2 (-X) (by linarith) (by linarith)
    have heq : Tfun L G0 (fun u => -B0 u) X = Tfun L G0 B0 (-X) := funext (Tfun_neg L G0 B0 X)
    refine ⟨a, b, ha0, hab, hbL, ?_, ?_, ?_, ?_, ?_⟩
    · rw [heq]; exact hset
    · intro hpos; rw [heq]; exact ha hpos
    · intro hlt; rw [heq]; exact hb hlt
    · intro h0; have := ha0' h0; show X = -B0 0; linarith
    · intro h0; have := hbL' h0; show X = -B0 L; linarith
  H3p := by
    obtain ⟨uc, h0, hL, hu, hd⟩ := h.H3m
    refine ⟨uc, h0, hL, fun u hu' => ?_, ?_⟩
    · rw [fPlus_neg, Xsp_neg]
      simp only [neg_inj]
      exact hu u hu'
    · rw [fPlus_neg]
      have e1 : deriv (fun u => -fMinus L G0 B0 u) = fun x => -deriv (fMinus L G0 B0) x := deriv.neg'
      rw [e1, deriv.fun_neg]
      linarith
  H3m := by
    obtain ⟨uc, h0, hL, hu, hd⟩ := h.H3p
    refine ⟨uc, h0, hL, fun u hu' => ?_, ?_⟩
    · rw [fMinus_neg, Xsm_neg]
      simp only [neg_inj]
      exact hu u hu'
    · rw [fMinus_neg]
      have e1 : deriv (fun u => -fPlus L G0 B0 u) = fun x => -deriv (fPlus L G0 B0) x := deriv.neg'
      rw [e1, deriv.fun_neg]
      linarith

theorem hypOn_neg {F : SymbolFamily Par} {K : Set Par} (h : HypOn F K) : HypOn (negFamily F) K := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, fun μ hμ => hyp_neg (hg μ hμ)⟩

theorem jetReg_neg {f : Par → ℝ → ℝ} {K : Set Par} {L : ℝ} {r : ℕ} (h : JetReg f K L r) :
    JetReg (fun μ s => -f μ s) K L r := by
  refine ⟨fun μ hμ => (h.1 μ hμ).neg, fun i hi => ?_⟩
  have := (h.2 i hi).neg
  refine this.congr (fun p _ => ?_)
  simp only [Pi.neg_apply]
  exact iteratedDerivWithin_fun_neg (f := f p.1) (n := i) (s := Set.Icc 0 L) (x := p.2)

theorem ek_neg {F : SymbolFamily Par} {P : Set Par} {Kd r : ℕ} (h : EK F P Kd r) : EK (negFamily F) P Kd r where
  budget := h.budget
  reg := fun j hj => ⟨h.reg j hj |>.1, jetReg_neg (h.reg j hj).2⟩
  rem := by
    obtain ⟨C, hC⟩ := h.rem
    refine ⟨C, fun μ hμ N s hs => ⟨(hC μ hμ N s hs).1, ?_⟩⟩
    have h2 := (hC μ hμ N s hs).2
    have e : (negFamily F).Bh μ ((negFamily F).step N) s - ∑ j ∈ range (Kd + 1), (negFamily F).step N ^ (2 * j) * (negFamily F).B (2 * j) μ s =
        -(F.Bh μ (F.step N) s - ∑ j ∈ range (Kd + 1), F.step N ^ (2 * j) * F.B (2 * j) μ s) := by
      have hstep : (negFamily F).step N = F.step N := rfl
      rw [hstep]
      simp only [negFamily, mul_neg, Finset.sum_neg_distrib]
      ring
    rw [e, abs_neg]
    exact h2

/-- **Bridge (a) for the gauge family**: the standing assumptions of `F` give those of `negFamily F` (same compact set, `(E_K)` with `B -> -B`, `(H1)`--`(H3)` for `-B_0`). -/
theorem stdAssump_neg {F : SymbolFamily Par} {P : Set Par} {Kd r : ℕ} (h : StdAssump F P Kd r) : StdAssump (negFamily F) P Kd r :=
  ⟨h.1, ek_neg h.2.1, hypOn_neg h.2.2⟩

end StdNeg

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.compColumn_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.compColumn_lower

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.compColumn_lower_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.compColumn_lower_sub

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.compMatrix_lower_col_l2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.compMatrix_lower_col_l2

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.soft_col_clause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.soft_col_clause

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.compMatrix_lower_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.compMatrix_lower_col

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.hyp_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.hyp_neg

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.ek_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.ek_neg

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.stdAssump_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.stdAssump_neg

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.le_of_step_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.le_of_step_le

end FormalResearch.JacobiEigenvectors.TheoremB
