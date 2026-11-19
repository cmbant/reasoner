module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.NegColumns
public import FormalResearch.JacobiEigenvectors.TheoremB.SpliceSoft
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbRestrict
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftW2Proved
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftAssembly6

/-!
# Paper J, Theorem B, L3.5c, part 6: the soft columns of both orders, and `PropThaSpliceTwoOrders` itself

Source: Paper J `app_thmB.tex`, `prop:tha-splice` (c) ("a soft column in `Sigma^+` is the vector of Proposition tha-W2 (2), with the fixed scalars, sewn at the fixed row `n_c`; a column in `Sigma^-` is `D_-` times such a vector for `-D_- J_h D_-`").

## Proved here (axiom-pinned)

* `soft_env_data`, `soft_a_data`: for any soft chart pair `(CL, CR)` of any family under `StdAssump`, (i) `sum softEnv^2 <= CS` at every eigenvalue in the window with `a <= 1` (`propThaW2_proved` and `stepZero`), (ii) `a <= 0` at every
  eigenvalue in the window (`soft_window_label`).  These discharge the premises `hEnv`, `hA1` of `compMatrix_lower_col`.
* `soft_columns`: for a `ChartInputs` of order `M >= 1`, the soft columns of `compMatrix CI spl` (energy outside all blocks, upper or lower) have `l^2` error `<= C h^M`.  The upper edge is `soft_col_clause` for `(softUpL, softUpR)` with `propThaSpliceSoft_proved`;
  the lower edge is the transport of `NegColumns` (`compMatrix_lower_col_l2`).  Premises: `StdAssump` of the frozen family and the spectrum cover `SoftCovers CI` (a consequence of `spectrumCovered`).
* `twoOrders_soft_columns`: both orders for a chart pair (the cover of the order-`(m+1)` chart is transported from the order-`m` chart: same `Jhi`, `lo`, `hi`, `delta_0`); the F-t0 restriction is done inside.
* **`propThaSpliceTwoOrders_proved : PropThaSpliceTwoOrders CP spl`**, the frozen statement, with its own premises only: bulk columns (`twoOrders_bulk_columns`) and soft columns.

## Differences from the paper

The frozen-family standing assumption holds only for small `t0` (finding F-t0): the soft charts are restricted to `min t0 t1` (`ChartInputs.restrict`, `compMatrix_restrict` is `rfl`).  `eta_{m+1}` is bounded below by `h^{m+1}` (`etaR_succ_ge`).

## Not formalised

Nothing of the statement `PropThaSpliceTwoOrders`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA

open scoped Classical

variable {Par : Type*} [TopologicalSpace Par]

section Generic

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- **The envelope sum of a soft chart is bounded** at every eigenvalue in the window with `a <= 1` (`PropThaW2` (2) composed with Step 0). -/
theorem soft_env_data (hf : ParabolicCylinderFacts U V cPC CPC) (CL : SoftEdgeChart Fz P m q U V (fun _ => 1))
    (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1)) (hm : 1 ≤ m) (hM : SoftMirror CL CR) (r : ℕ)
    (hr : StdAssump Fz P (q / 2) r) :
    ∃ CS h1 : ℝ, 0 < h1 ∧ ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ CL.δ0 → ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 → CL.aOf p X N ≤ 1 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
        ∀ k : Fin (N + 1), Xs k = X → ∑ n ∈ rowsOf N, softEnv CL CR p X N n ^ 2 ≤ CS := by
  obtain ⟨Cs, hs0, hs0p, hsp⟩ := stepZero Fz P (q / 2) r hr
  obtain ⟨Cc, h0, clam, Clam, hh0, hclam, H⟩ := propThaW2_proved CL CR Cs cPC CPC hf hm (fun h _ _ => le_rfl) hM r hr
  refine ⟨Cc, min h0 hs0, lt_min hh0 hs0p, ?_⟩
  intro p hp X hX N hN hst _ Xs Um hE k hk
  have hS0 : ∀ i, Xs i ≤ Fz.bandHi p + Cs * Fz.step N ^ 2 :=
    fun i => (hsp p hp N (hst.trans (min_le_right _ _)) Xs Um hE i).2
  obtain ⟨hA, -, -⟩ := H p hp N hN (hst.trans (min_le_left _ _))
  obtain ⟨-, -, -, hEc⟩ := hA X hX
  obtain ⟨-, h2, -⟩ := hEc Xs Um hE hS0 k hk
  exact h2

/-- **`a <= 0` at every eigenvalue in the window** (`soft_window_label` composed with Step 0). -/
theorem soft_a_data (hf : ParabolicCylinderFacts U V cPC CPC) (CL : SoftEdgeChart Fz P m q U V (fun _ => 1))
    (CR : SoftEdgeChart (mirrorFamily Fz) P m q U V (fun _ => 1)) (hm : 1 ≤ m) (hM : SoftMirror CL CR) (r : ℕ)
    (hr : StdAssump Fz P (q / 2) r) :
    ∃ h1 : ℝ, 0 < h1 ∧ ∀ p ∈ P, ∀ N : ℕ, max CL.N0 CR.N0 ≤ N → Fz.step N ≤ h1 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (Fz.jacobiMat p N) Xs Um →
        ∀ k : Fin (N + 1), |Xs k - Fz.bandHi p| ≤ CL.δ0 → CL.aOf p (Xs k) N ≤ 0 := by
  obtain ⟨Cs, hs0, hs0p, hsp⟩ := stepZero Fz P (q / 2) r hr
  obtain ⟨Cc, h0, hh0, H⟩ := soft_window_label CL CR hM hf hm (fun h _ _ => le_rfl) Cs
  refine ⟨min h0 hs0, lt_min hh0 hs0p, ?_⟩
  intro p hp N hN hst Xs Um hE k hk
  exact (H p hp N hN (hst.trans (min_le_left _ _)) Xs Um hE
    (fun i => (hsp p hp N (hst.trans (min_le_right _ _)) Xs Um hE i).2) k hk).1

end Generic

theorem pow_small {m : ℕ} (hm : 1 ≤ m) : (∀ h : ℝ, 0 < h → h ≤ 1 → 0 ≤ (fun h : ℝ => h ^ m) h) ∧
    (∀ ε : ℝ, 0 < ε → ∃ h1 : ℝ, 0 < h1 ∧ ∀ h : ℝ, 0 < h → h ≤ h1 → |(fun h : ℝ => h ^ m) h| ≤ ε) := by
  refine ⟨fun h h0 _ => pow_nonneg h0.le _, fun ε hε => ⟨min ε 1, lt_min hε one_pos, fun h h0 h1 => ?_⟩⟩
  show |h ^ m| ≤ ε
  rw [abs_of_nonneg (pow_nonneg h0.le _)]
  exact (pow_le_of_le_one h0.le (h1.trans (min_le_right _ _)) (by omega)).trans (h1.trans (min_le_left _ _))

section Cols

variable {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- The cover of the spectrum by the bulk blocks and the two soft windows (`SpectrumCovered` without the index premise). -/
def SoftCovers (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) : Prop :=
  ∃ h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 → F.step N ≤ t0 →
      ∀ (X : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) X Um →
        ∀ k : Fin (N + 1),
          (∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) ∨
          ((¬ ∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) ∧ CI.Jhi < X k ∧
            |X k - (frozenFamily F Kidx).bandHi (atStep F μ N)| ≤ CI.softUpL.δ0) ∨
          ((¬ ∃ ν, CI.lo ν ≤ X k ∧ X k ≤ CI.hi ν) ∧ ¬ CI.Jhi < X k ∧
            |-X k - (negFamily (frozenFamily F Kidx)).bandHi (atStep F μ N)| ≤ CI.softLoL.δ0)

theorem softCovers_of_spectrumCovered (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (hKidx : Kidx = (m + 1) / 2) (hK : IsCompact K)
    (hH : HypOn F K) (hD : DM F K (2 * Kidx + 1)) : SoftCovers CI :=
  spectrumCovered CI hKidx hK hH hD

theorem SoftCovers.restrict {CI : ChartInputs F K Kidx t0 m q U V cPC CPC} (h : SoftCovers CI) {t0' : ℝ} (ht : t0' ≤ t0) :
    SoftCovers (CI.restrict ht) := by
  obtain ⟨h0, hh0, H⟩ := h
  exact ⟨h0, hh0, fun μ hμ N hN hNt => H μ hμ N hN (hNt.trans ht)⟩

/-- **The upper soft columns of `compMatrix`** (`l^2` error `<= C h^m`). -/
theorem soft_cols_upper (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (spl : Fin CI.nb → ℝ) (hm : 1 ≤ m) (r : ℕ)
    (hr : StdAssump (frozenFamily F Kidx) (paramSet K t0) (q / 2) r) (hcov : SoftCovers CI) :
    ∃ C h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 → F.step N ≤ t0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ∀ j : Fin (N + 1), (¬ ∃ ν : Fin CI.nb, CI.lo ν ≤ Xs j ∧ Xs j ≤ CI.hi ν) → CI.Jhi < Xs j →
          FormalResearch.JB.jbL2 Finset.univ (fun i : Fin (N + 1) => compMatrix CI spl μ N Xs i j - Um i j) ≤ C * F.step N ^ m := by
  obtain ⟨hη0, hetas⟩ := pow_small hm
  have hS := propThaSpliceSoft_proved (m := m) CI.softUpL CI.softUpR (cPC := cPC) (CPC := CPC)
  obtain ⟨CS, hCS, hhCS, hEnv⟩ := soft_env_data CI.pc CI.softUpL CI.softUpR hm CI.mirror_up r hr
  obtain ⟨C, h1, hh1, hcl⟩ := soft_col_clause CI.pc CI.softUpL CI.softUpR (fun h => h ^ m) hη0 hetas hS hm CI.mirror_up r hr
    ⟨CS, hCS, hhCS, hEnv⟩
  obtain ⟨hA, hhA, HA⟩ := soft_a_data CI.pc CI.softUpL CI.softUpR hm CI.mirror_up r hr
  obtain ⟨h0c, hh0c, hcv⟩ := hcov
  have hLp : 0 < F.L / ((max CI.softUpL.N0 CI.softUpR.N0 : ℕ) + 1 : ℝ) := div_pos F.L_pos (by positivity)
  refine ⟨C, min (min (min h1 h0c) hA) (F.L / (((max CI.softUpL.N0 CI.softUpR.N0 : ℕ) : ℝ) + 1)),
    lt_min (lt_min (lt_min hh1 hh0c) hhA) hLp, ?_⟩
  intro μ hμ N hN ht Xs Um hE j hb hu
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hs1 : F.step N ≤ h1 := hN.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hsc : F.step N ≤ h0c := hN.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hsA : F.step N ≤ hA := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hsN : F.step N ≤ F.L / (((max CI.softUpL.N0 CI.softUpR.N0 : ℕ) : ℝ) + 1) := hN.trans (min_le_right _ _)
  have hN0 : max CI.softUpL.N0 CI.softUpR.N0 ≤ N := le_of_step_le F _ N hsN
  have hwin : |Xs j - (frozenFamily F Kidx).bandHi (atStep F μ N)| ≤ CI.softUpL.δ0 := by
    rcases hcv μ hμ N hsc ht Xs Um hE j with h | ⟨_, _, h⟩ | ⟨_, hJ, _⟩
    · exact absurd h hb
    · exact h
    · exact absurd hu hJ
  have hp : atStep F μ N ∈ paramSet K t0 := ⟨hμ, ⟨by unfold atStep; linarith, ht⟩⟩
  have hE' : IsEigenSystem ((frozenFamily F Kidx).jacobiMat (atStep F μ N) N) Xs Um := by
    unfold atStep
    rw [frozenFamily_jacobiMat_at_step]
    exact hE
  have ha : CI.softUpL.aOf (atStep F μ N) (Xs j) N ≤ 1 :=
    (HA (atStep F μ N) hp N hN0 hsA Xs Um hE' j hwin).trans zero_le_one
  have hres := hcl (atStep F μ N) hp (Xs j) hwin N hN0 hs1 ha Xs Um hE' j rfl
  have e : ∀ i : Fin (N + 1), compMatrix CI spl μ N Xs i j =
      softColAt CI.softUpL CI.softUpR (atStep F μ N) (Xs j) N (nearestRow (F.step N) (CI.softUpL.uc (atStep F μ N))) ((i : ℕ) : ℤ) := by
    intro i
    show compColumn CI spl μ N (Xs j) ((i : ℕ) : ℤ) = _
    unfold compColumn
    rw [dif_neg hb, if_pos hu]
  simp only [e]
  exact hres

/-- **The lower soft columns of `compMatrix`** (`l^2` error `<= C h^m`), by the gauge transport of `NegColumns`. -/
theorem soft_cols_lower (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (spl : Fin CI.nb → ℝ) (hm : 1 ≤ m) (r : ℕ)
    (hr : StdAssump (frozenFamily F Kidx) (paramSet K t0) (q / 2) r) (hcov : SoftCovers CI) :
    ∃ C h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 → F.step N ≤ t0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ∀ j : Fin (N + 1), (¬ ∃ ν : Fin CI.nb, CI.lo ν ≤ Xs j ∧ Xs j ≤ CI.hi ν) → ¬ CI.Jhi < Xs j →
          FormalResearch.JB.jbL2 Finset.univ (fun i : Fin (N + 1) => compMatrix CI spl μ N Xs i j - Um i j) ≤ C * F.step N ^ m := by
  obtain ⟨hη0, hetas⟩ := pow_small hm
  have hrn : StdAssump (negFamily (frozenFamily F Kidx)) (paramSet K t0) (q / 2) r := stdAssump_neg hr
  have hS := propThaSpliceSoft_proved (m := m) CI.softLoL CI.softLoR (cPC := cPC) (CPC := CPC)
  obtain ⟨CS, hCS, hhCS, hEnv⟩ := soft_env_data CI.pc CI.softLoL CI.softLoR hm CI.mirror_lo r hrn
  obtain ⟨C, h1, hh1, hcl⟩ := soft_col_clause CI.pc CI.softLoL CI.softLoR (fun h => h ^ m) hη0 hetas hS hm CI.mirror_lo r hrn
    ⟨CS, hCS, hhCS, hEnv⟩
  obtain ⟨hA, hhA, HA⟩ := soft_a_data CI.pc CI.softLoL CI.softLoR hm CI.mirror_lo r hrn
  obtain ⟨h0c, hh0c, hcv⟩ := hcov
  have hLp : 0 < F.L / ((max CI.softLoL.N0 CI.softLoR.N0 : ℕ) + 1 : ℝ) := div_pos F.L_pos (by positivity)
  refine ⟨C, min (min (min h1 h0c) hA) (F.L / (((max CI.softLoL.N0 CI.softLoR.N0 : ℕ) : ℝ) + 1)),
    lt_min (lt_min (lt_min hh1 hh0c) hhA) hLp, ?_⟩
  intro μ hμ N hN ht Xs Um hE j hb hu
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hs1 : F.step N ≤ h1 := hN.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hsc : F.step N ≤ h0c := hN.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hsA : F.step N ≤ hA := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hsN : F.step N ≤ F.L / (((max CI.softLoL.N0 CI.softLoR.N0 : ℕ) : ℝ) + 1) := hN.trans (min_le_right _ _)
  have hN0 : max CI.softLoL.N0 CI.softLoR.N0 ≤ N := le_of_step_le F _ N hsN
  have hwin : |-(Xs j) - (negFamily (frozenFamily F Kidx)).bandHi (atStep F μ N)| ≤ CI.softLoL.δ0 := by
    rcases hcv μ hμ N hsc ht Xs Um hE j with h | ⟨_, hJ, _⟩ | ⟨_, _, h⟩
    · exact absurd h hb
    · exact absurd hJ hu
    · exact h
  have hp : atStep F μ N ∈ paramSet K t0 := ⟨hμ, ⟨by unfold atStep; linarith, ht⟩⟩
  have hE' : IsEigenSystem ((negFamily (frozenFamily F Kidx)).jacobiMat (atStep F μ N) N) (negX Xs) (negU Um) :=
    hE.neg_frozen (Kidx := Kidx)
  have hwin' : |negX Xs (Fin.rev j) - (negFamily (frozenFamily F Kidx)).bandHi (atStep F μ N)| ≤ CI.softLoL.δ0 := by
    rw [negX_rev]; exact hwin
  have ha : CI.softLoL.aOf (atStep F μ N) (-(Xs j)) N ≤ 1 := by
    have := HA (atStep F μ N) hp N hN0 hsA (negX Xs) (negU Um) hE' (Fin.rev j) hwin'
    rw [negX_rev] at this
    exact this.trans zero_le_one
  have hres := hcl (atStep F μ N) hp (-(Xs j)) hwin N hN0 hs1 ha (negX Xs) (negU Um) hE' (Fin.rev j) (negX_rev Xs j)
  rw [compMatrix_lower_col_l2 CI spl μ N Xs Um j hb hu]
  exact hres

/-- **The soft columns of `compMatrix`**: every column whose energy lies in no block. -/
theorem soft_columns (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (spl : Fin CI.nb → ℝ) (hm : 1 ≤ m) (r : ℕ)
    (hr : StdAssump (frozenFamily F Kidx) (paramSet K t0) (q / 2) r) (hcov : SoftCovers CI) :
    ∃ C h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 → F.step N ≤ t0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ∀ j : Fin (N + 1), (¬ ∃ ν : Fin CI.nb, CI.lo ν ≤ Xs j ∧ Xs j ≤ CI.hi ν) →
          FormalResearch.JB.jbL2 Finset.univ (fun i : Fin (N + 1) => compMatrix CI spl μ N Xs i j - Um i j) ≤ C * F.step N ^ m := by
  obtain ⟨Cu, hu0, hhu, Hu⟩ := soft_cols_upper CI spl hm r hr hcov
  obtain ⟨Cl, hl0, hhl, Hl⟩ := soft_cols_lower CI spl hm r hr hcov
  refine ⟨|Cu| + |Cl|, min hu0 hl0, lt_min hhu hhl, ?_⟩
  intro μ hμ N hN ht Xs Um hE j hb
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hp : 0 ≤ F.step N ^ m := pow_nonneg hst.le _
  by_cases hu : CI.Jhi < Xs j
  · refine (Hu μ hμ N (hN.trans (min_le_left _ _)) ht Xs Um hE j hb hu).trans (mul_le_mul_of_nonneg_right ?_ hp)
    linarith [le_abs_self Cu, abs_nonneg Cl]
  · refine (Hl μ hμ N (hN.trans (min_le_right _ _)) ht Xs Um hE j hb hu).trans (mul_le_mul_of_nonneg_right ?_ hp)
    linarith [le_abs_self Cl, abs_nonneg Cu]

end Cols

section Pair

variable {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- The cover of the order-`(m+1)` chart from that of the order-`m` chart. -/
theorem softCovers_pair (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (h : SoftCovers CP.CI0) : SoftCovers CP.CI1 := by
  obtain ⟨h0, hh0, H⟩ := h
  refine ⟨h0, hh0, fun μ hμ N hN ht Xs Um hE k => ?_⟩
  have hlo : ∀ ν : Fin CP.CI1.nb, CP.CI1.lo ν = CP.CI0.lo (Fin.cast CP.nb_eq ν) := CP.lo_eq
  have hhi : ∀ ν : Fin CP.CI1.nb, CP.CI1.hi ν = CP.CI0.hi (Fin.cast CP.nb_eq ν) := CP.hi_eq
  have e1 : (∃ ν : Fin CP.CI1.nb, CP.CI1.lo ν ≤ Xs k ∧ Xs k ≤ CP.CI1.hi ν) ↔ (∃ ν : Fin CP.CI0.nb, CP.CI0.lo ν ≤ Xs k ∧ Xs k ≤ CP.CI0.hi ν) := by
    constructor
    · rintro ⟨ν, h1, h2⟩
      exact ⟨Fin.cast CP.nb_eq ν, by rw [← hlo]; exact h1, by rw [← hhi]; exact h2⟩
    · rintro ⟨ν, h1, h2⟩
      refine ⟨Fin.cast CP.nb_eq.symm ν, ?_, ?_⟩
      · rw [hlo]; simpa using h1
      · rw [hhi]; simpa using h2
  have hJ : CP.CI1.Jhi = CP.CI0.Jhi := CP.J_eq.2
  rw [e1, hJ, CP.soft_up_eq.2.1, CP.soft_lo_eq.2.1]
  exact H μ hμ N hN ht Xs Um hE k

/-- **The soft columns of both orders** (F-t0: the standing assumptions hold on `paramSet K (min t0 t1)`, to which the charts are restricted). -/
theorem twoOrders_soft_columns (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (spl : Fin CP.CI0.nb → ℝ) (hm : 1 ≤ m) (hK : Kidx = (m + 1) / 2) (hq : q = 2 * Kidx) (hKc : IsCompact K) (hH : HypOn F K)
    (hDM : DM F K (2 * Kidx + 1)) :
    ∃ C h0 : ℝ, 0 < h0 ∧ ∀ μ ∈ K, ∀ N : ℕ, F.step N ≤ h0 → F.step N ≤ t0 →
      ∀ (Xs : Fin (N + 1) → ℝ) (Um : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ), IsEigenSystem (F.jacobiMat μ N) Xs Um →
        ∀ j : Fin (N + 1), (¬ ∃ ν, CP.CI0.lo ν ≤ Xs j ∧ Xs j ≤ CP.CI0.hi ν) →
          FormalResearch.JB.jbL2 Finset.univ (fun i => compMatrix CP.CI0 spl μ N Xs i j - Um i j) ≤ C * etaR m m (F.step N) ∧
          FormalResearch.JB.jbL2 Finset.univ (fun i => compMatrix CP.CI1 (CP.spl1 spl) μ N Xs i j - Um i j) ≤ C * etaR m (m + 1) (F.step N) := by
  obtain ⟨t1, ht1, r, hr⟩ := stdAssump_frozen_all F K Kidx hKc hH hDM
  have hcov0 : SoftCovers CP.CI0 := softCovers_of_spectrumCovered CP.CI0 hK hKc hH hDM
  have hcov1 : SoftCovers CP.CI1 := softCovers_pair CP hcov0
  by_cases ht0 : 0 < t0
  swap
  · refine ⟨0, 1, one_pos, fun μ hμ N _ hNt => ?_⟩
    have := FormalResearch.JB.stepSize_pos F.L_pos N
    exact absurd (this.trans_le hNt) ht0
  have ht' : 0 < min t0 t1 := lt_min ht0 ht1
  have hrq : StdAssump (frozenFamily F Kidx) (paramSet K (min t0 t1)) (q / 2) r := by
    rw [hq, Nat.mul_div_cancel_left Kidx (by norm_num)]
    exact hr _ ht' (min_le_right _ _) Kidx le_rfl
  obtain ⟨C0, h00, hh00, H0⟩ := soft_columns (CP.CI0.restrict (min_le_left t0 t1)) spl hm r hrq (hcov0.restrict (min_le_left t0 t1))
  obtain ⟨C1, h01, hh01, H1⟩ := soft_columns (CP.CI1.restrict (min_le_left t0 t1)) (CP.spl1 spl) (by omega) r hrq
    (hcov1.restrict (min_le_left t0 t1))
  refine ⟨|C0| + |C1|, min (min (min h00 h01) (Real.exp (-1))) (min t0 t1), lt_min (lt_min (lt_min hh00 hh01) (Real.exp_pos _)) ht', ?_⟩
  intro μ hμ N hN hNt Xs Um hE j hj
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hs0 : F.step N ≤ h00 := hN.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hs1 : F.step N ≤ h01 := hN.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hse : F.step N ≤ Real.exp (-1) := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hsm : F.step N ≤ min t0 t1 := hN.trans (min_le_right _ _)
  have hj1 : ¬ ∃ ν : Fin CP.CI1.nb, CP.CI1.lo ν ≤ Xs j ∧ Xs j ≤ CP.CI1.hi ν := by
    rintro ⟨ν, h1, h2⟩
    exact hj ⟨Fin.cast CP.nb_eq ν, by rw [← CP.lo_eq]; exact h1, by rw [← CP.hi_eq]; exact h2⟩
  have e0 := H0 μ hμ N hs0 hsm Xs Um hE j hj
  have e1 := H1 μ hμ N hs1 hsm Xs Um hE j hj1
  have a0 : C0 ≤ |C0| + |C1| := by linarith [le_abs_self C0, abs_nonneg C1]
  have a1 : C1 ≤ |C0| + |C1| := by linarith [le_abs_self C1, abs_nonneg C0]
  constructor
  · rw [etaR_self]
    exact e0.trans (mul_le_mul_of_nonneg_right a0 (pow_nonneg hst.le _))
  · refine e1.trans ?_
    have hge := etaR_succ_ge m (F.step N) hst hse
    calc C1 * F.step N ^ (m + 1) ≤ (|C0| + |C1|) * F.step N ^ (m + 1) := mul_le_mul_of_nonneg_right a1 (pow_nonneg hst.le _)
      _ ≤ (|C0| + |C1|) * etaR m (m + 1) (F.step N) := mul_le_mul_of_nonneg_left hge (by positivity)

end Pair

section Final

variable {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- **`prop:tha-splice` (c) (`PropThaSpliceTwoOrders`), proved**: bulk columns (`twoOrders_bulk_columns`) and soft columns (`twoOrders_soft_columns`). -/
theorem propThaSpliceTwoOrders_proved (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (spl : Fin CP.CI0.nb → ℝ) : PropThaSpliceTwoOrders CP spl := by
  intro hm hK hq hKc hH hDM hs
  obtain ⟨Cb, hb0, hhb, Hb⟩ := twoOrders_bulk_columns CP spl hm hK hKc hH hDM hs
  obtain ⟨Cs, hs0, hhs, Hs⟩ := twoOrders_soft_columns CP spl hm hK hq hKc hH hDM
  refine ⟨|Cb| + |Cs|, min (min hb0 hs0) (Real.exp (-1)), lt_min (lt_min hhb hhs) (Real.exp_pos _), ?_⟩
  intro μ hμ N hN hNt Xs Um hE j
  have hst : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hse : F.step N ≤ Real.exp (-1) := hN.trans (min_le_right _ _)
  have hN' : F.step N ≤ min hb0 hs0 := hN.trans (min_le_left _ _)
  have a0 : Cb ≤ |Cb| + |Cs| := by linarith [le_abs_self Cb, abs_nonneg Cs]
  have a1 : Cs ≤ |Cb| + |Cs| := by linarith [le_abs_self Cs, abs_nonneg Cb]
  have p0 : 0 ≤ etaR m m (F.step N) := by rw [etaR_self]; exact pow_nonneg hst.le _
  have p1 : 0 ≤ etaR m (m + 1) (F.step N) := (pow_pos hst _).le.trans (etaR_succ_ge m (F.step N) hst hse)
  have hC : 0 ≤ |Cb| + |Cs| := by positivity
  by_cases hj : ∃ ν, CP.CI0.lo ν ≤ Xs j ∧ Xs j ≤ CP.CI0.hi ν
  · obtain ⟨e0, e1⟩ := Hb μ hμ N (hN'.trans (min_le_left _ _)) hNt Xs Um hE j hj
    exact ⟨e0.trans (mul_le_mul_of_nonneg_right a0 p0), e1.trans (mul_le_mul_of_nonneg_right a0 p1)⟩
  · obtain ⟨e0, e1⟩ := Hs μ hμ N (hN'.trans (min_le_right _ _)) hNt Xs Um hE j hj
    exact ⟨e0.trans (mul_le_mul_of_nonneg_right a1 p0), e1.trans (mul_le_mul_of_nonneg_right a1 p1)⟩

end Final

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.soft_env_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.soft_env_data

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.soft_a_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.soft_a_data

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.soft_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.soft_columns

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.twoOrders_soft_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.twoOrders_soft_columns

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.propThaSpliceTwoOrders_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.propThaSpliceTwoOrders_proved


end FormalResearch.JacobiEigenvectors.TheoremB

end
