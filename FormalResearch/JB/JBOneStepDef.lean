module

public import Mathlib
public import FormalResearch.JB.JBDefs
public import FormalResearch.JB.JBGlue
public import FormalResearch.JB.JBPolar

/-!
# Paper J, Theorem B reduction: the one-step criterion (statement freeze)

Source: Paper J, `/home/user/scratch/paperJ2/thmB.tex`, Section "The comparison matrices" (`sec:thb-matrices`),
Definition `def:thb-inputs` ((I1)-(I5)), Theorem `thm:thb-onestep` (Steps 1-5), the parity identity
`eq:thb-parity`; consumer: Theorem `thm:B` (`main_results.tex`), via Proposition `prop:thb-inputs`.

This module contains definitions only: the data of the comparison matrices (`Chart`), the properties that the
proof of `thm:thb-onestep` uses (`Chart.Ok`, `OneStepInputs`), the explicit smallness conditions
(`OneStepInputs.Small`), the toy instance showing that `OneStepInputs` and `Small` are satisfiable
(`toyInputs`, `toyInputs_small`), and the statement of the reduction as a proposition
(`OneStepReduction`, a definition, proved in the next stage).

## Dictionary: Lean setting to paper

* `D` is the number of columns (`N + 1 = L/h`); rows and columns are `Fin D`; `U` is `U_h`; `G0 = Ĝ^{[m]}`,
  `G1 = Ĝ^{[m+1]}` at the fixed splices.  Matrix norm: `L2` operator norm; `⊙` is the Hadamard product.
* A *block* `ν : Fin cs.nb` is a column set `Σ_ν` (a bulk interval `J_ν`, or a soft edge `Σ^±`); the
  blocks have pairwise disjoint column sets.  Each block carries exactly two charts (`Fin 2`): bulk left and
  bulk right, or soft left half and soft right half.
* A `Chart` on columns `Σ` has rows `I⁺ = [lo, lo + R)` re-indexed `Fin R`, direction `τ` (`true` is `+1`),
  used rows `I_c ⊆ I⁺`, model pair `(y, ỹ)`, exterior row `y_ext`, transfer data `ω, t₁₁, t₁₂`, the
  coefficients `A^{[m]}, A^{[m+1]}, B^{[m]}, B^{[m+1]}` and the changed coefficient `κ_m`
  sampled at `(u_n, X_k)`, the scalars `σ^{[m]}, σ^{[m+1]}`, the overlap sets `P_k`, and the *host* matrices
  (`Ĝ^{[r]}(n_ν^+)`, `Ĝ^{[r]}(n_ν^-)`, or `Ĝ^{[r]}` for a soft half) of which `H^{[r]}_c` is a submatrix.
* `Chart.H0 h`, `Chart.H1 h` are `H^{[m]}_c`, `H^{[m+1]}_c = (σ^{[r]}_k φ^{[r]}_{nk})`, with
  `φ^{[r]} = A^{[r]} ⊙ y + h B^{[r]} ⊙ ỹ` (`eq:thb-profile`).

## Which paper statement discharges which field

* (I1) `Chart.Ok.host0_col`, `host1_col`, `OneStepInputs.G1_col`: `prop:tha-splice` (c) (columns of
  `Ĝ^{[r]}(n_s)` for every splice `n_s` in the window, `η_m = h^m`, `η_{m+1} = h^{m+1} log(1/h)`), which rests on
  `prop:tha-W` (bulk) and `prop:tha-W2` (soft), hence on Theorem A(ii) and the charts.  The hosts are the
  matrices at the two extreme splices (F4: (I1) is used for the splice-moved matrices, the final `G1` is one more).
* Chart structure (`host0_eq`, `host1_eq`, `match0`, `match1`): the definition of `Ĝ^{[r]}` in
  `eq:thb-bulkcol` and the paragraph "Charts, bootstrap blocks and directions" (the scalars do not depend on
  the splice, so `H_c` is a submatrix of the host and of `Ĝ^{[r]}` on the used rows).  This is **not** in
  `def:thb-inputs` (F3 (a), (c), (d)): it is by construction in `prop:thb-inputs`.
* Parity (`parity_A`, `parity_B`): `eq:thb-parity` (F3 (b)); `κ_m` is `g_m` for even `m` and `B_m` for odd `m`;
  the paper's `h^{m-1}` is written `h * (B1 - B0) = ε_m h^m κ_m`, equivalent for `h > 0`.
* (I2) `ω_pos`, `transfer`, `t12_lb`, `α_lb`, `schur_*`: `prop:thb-inputs` (Appendix `app:thmB`, "Verification of the
  inputs"), using the exact model transfer of the Weber ladder / parabolic-cylinder charts
  (`lem:cha-weber-ladder`, `thm:cha-PC`) and, for the soft halves, `lem:tha-collar` (2) (`|T_{±,12}| ≥ c_1`,
  quotients of uniformly bounded mixed variation).  The paper asks for restrictions of `C²` functions on a
  compact rectangle with `C²`-norm bounded in `h`; here the *consequence* is taken, `IsSchurBdd ≤ K` for the
  four quotients and `κ_m` (`lem:thb-schur`, formalised as `jb_schur_of_C2`, `jb_schur_inv`, `jb_schur_div`),
  which is weaker than the `C²` hypothesis, so the reduction is stronger (design choice D3).  The paper's
  `ω ≡ 1` for soft halves and the `A^{[m+1]}` lower bound `g_0 > 0` are not used by Steps 1-5 and are not fields.
* (I3) `Chart.Ok.ext_row`: `ℓ²`-norm of the exterior row `(ω σ^{[m+1]} y_ext)`; F6: discharged by
  `prop:tha-W` (2) / `prop:tha-W2` (2) (`N̂ ≍ h^{-1/4}`, `σ = O(h^{1/4})`) and the Weber / PC envelope bound; the
  step `√|Σ| · sup = O(1)` is an input here.
* (I4) `overlap_lb`, `overlap_ub`: `lem:tha-Mflat` (soft half-windows carry a fixed fraction of the
  window mass, `P_k` a half-window), `prop:tha-W` (1) / `lem:tha-M` (bulk window mass, `P_k` the window
  `Ω_ν`).  The paper's "same `P_k` for a bulk block" is not used and is not a field.
* (I5) `OneStepInputs.outside`: `lem:tha-collar` (1) (entries of `Ψ` and `Ĝ e_k` off the collar are
  `≤ C h^{-K} e^{-c/h}`), and the bulk charts cover all rows.  `ε5` stands for `C h^{-K} e^{-c/h}` (F12);
  only `D · ε5 ≤ h^m` is used (`Small`).
* `cols_disjoint`, `chart_ok`, `U_orth`: structure of the block decomposition of `thm:thb-onestep` Step 5 and
  `U_h` orthogonal.

## Uniformity and jet-budget points (F-findings that fix a quantifier)

* F2 / F10: the constants `cs` (`C, K, ωmax, cT, cα, c0, C4, CE, nb`) are fixed before `D, h, m` vary:
  `OneStepReduction` is `∀ m, ∃ Cstar, ∀ D h inputs`, so `Cstar` is independent of `h` and of `D`; the
  `h`-dependent quantities (`D = L/h`, `ε5`) enter only through `Small`.  The paper's uniformity in `μ ∈ 𝒦`
  is the statement that the same `cs` serves all `μ`.
* F3 (a)-(d): `host*_eq`, `match*`, `parity_*`, `outside` above.  F4: hosts.  F5: (I1) at order `m+1`, `m` even,
  carries `log(1/h)` and is `prop:tha-W2` (4)/`prop:tha-splice` (c), not Theorem A(ii).  F6: (I3).
  F8: `outside` is required of both `G0` and `G1` and of `U`.  F12: `ε5`.
* F1: nothing here fixes how `X_k` is chosen; the matrices are data (explicit given the exact spectrum).
* F13 (jet budget of Theorem A(i)) does not enter this module.

## Not formalised

The proof of `OneStepReduction` (Steps 1-5), the passage from `C²` data to the Schur fields, the quantified
instantiation `thm_B_conditional` (`D = L/(N+1)`, `∃ C h₀ ∀ h ≤ h₀`), and everything that discharges the
fields.  The toy instance is degenerate (`G = U`), it only shows the hypotheses are consistent.
-/

@[expose] public section

namespace FormalResearch.JB

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

/-- Euclidean norm of a vector restricted to the index set `S` (`ℓ²`-norm of `P v`). -/
noncomputable def jbL2 {ι : Type*} (S : Finset ι) (v : ι → ℝ) : ℝ := √(∑ n ∈ S, v n ^ 2)

/-- The constants of the one-step criterion (the paper's generic `C`, `c`, `K`, fixed before `h → 0`).
`nb` is the number of blocks; all other fields are positive reals. -/
structure OneStepConsts where
  nb : ℕ
  C : ℝ
  K : ℝ
  ωmax : ℝ
  cT : ℝ
  cα : ℝ
  c0 : ℝ
  C4 : ℝ
  CE : ℝ
  C_nonneg : 0 ≤ C
  K_nonneg : 0 ≤ K
  ωmax_pos : 0 < ωmax
  cT_pos : 0 < cT
  cα_pos : 0 < cα
  c0_pos : 0 < c0
  C4_nonneg : 0 ≤ C4
  CE_nonneg : 0 ≤ CE

/-- A chart of the comparison matrices on the column set `cols`: the data of
`H^{[r]}_c = (σ^{[r]}_k φ^{[r]}_{nk})` on the rows `I⁺ = [lo, lo + R)` (re-indexed `Fin R`), see the module
docstring for the dictionary.  Data only; the properties are in `Chart.Ok`. -/
structure Chart (D R : ℕ) (cols : Finset (Fin D)) where
  lo : ℕ
  lo_add : lo + R ≤ D
  /-- direction `τ`: `true` is `+1` (exterior row after the last row), `false` is `-1`. -/
  τ : Bool
  /-- the rows `I_c ⊆ I⁺` actually used by `Ĝ^{[r]}` at the fixed splice. -/
  used : Finset (Fin R)
  y : Matrix (Fin R) cols ℝ
  yt : Matrix (Fin R) cols ℝ
  yext : cols → ℝ
  ω : Fin R → ℝ
  t11 : Matrix (Fin R) cols ℝ
  t12 : Matrix (Fin R) cols ℝ
  A0 : Matrix (Fin R) cols ℝ
  A1 : Matrix (Fin R) cols ℝ
  B0 : Matrix (Fin R) cols ℝ
  B1 : Matrix (Fin R) cols ℝ
  κ : Matrix (Fin R) cols ℝ
  σ0 : cols → ℝ
  σ1 : cols → ℝ
  P : cols → Finset (Fin R)
  host0 : Matrix (Fin D) (Fin D) ℝ
  host1 : Matrix (Fin D) (Fin D) ℝ

namespace Chart

variable {D R : ℕ} {cols : Finset (Fin D)}

/-- The global row `lo + n` of the chart row `n`. -/
def row (c : Chart D R cols) (n : Fin R) : Fin D := ⟨c.lo + n.val, by have := c.lo_add; omega⟩

/-- The shifted carrier `n ↦ Y_{n+τ,k}` with the exterior row `y_ext` (`Ysh` / `YshRev` of `JBGlue`). -/
def shifted (c : Chart D R cols) (Y : Matrix (Fin R) cols ℝ) : Matrix (Fin R) cols ℝ :=
  Matrix.of fun n k => if c.τ then Ysh c.yext Y n k else YshRev c.yext Y n k

/-- Chart profile of order `m`: `φ^{[m]} = A^{[m]} ⊙ y + h B^{[m]} ⊙ ỹ` (`eq:thb-profile`). -/
def phi0 (c : Chart D R cols) (h : ℝ) : Matrix (Fin R) cols ℝ := c.A0 ⊙ c.y + h • (c.B0 ⊙ c.yt)

/-- Chart profile of order `m + 1`. -/
def phi1 (c : Chart D R cols) (h : ℝ) : Matrix (Fin R) cols ℝ := c.A1 ⊙ c.y + h • (c.B1 ⊙ c.yt)

/-- `H^{[m]}_c = (σ^{[m]}_k φ^{[m]}_{nk})`. -/
def H0 (c : Chart D R cols) (h : ℝ) : Matrix (Fin R) cols ℝ := Matrix.of fun n k => c.σ0 k * c.phi0 h n k

/-- `H^{[m+1]}_c = (σ^{[m+1]}_k φ^{[m+1]}_{nk})`. -/
def H1 (c : Chart D R cols) (h : ℝ) : Matrix (Fin R) cols ℝ := Matrix.of fun n k => c.σ1 k * c.phi1 h n k

theorem phi0_apply (c : Chart D R cols) (h : ℝ) (n : Fin R) (k : cols) :
    c.phi0 h n k = c.A0 n k * c.y n k + h * (c.B0 n k * c.yt n k) := rfl

theorem phi1_apply (c : Chart D R cols) (h : ℝ) (n : Fin R) (k : cols) :
    c.phi1 h n k = c.A1 n k * c.y n k + h * (c.B1 n k * c.yt n k) := rfl

theorem H0_apply (c : Chart D R cols) (h : ℝ) (n : Fin R) (k : cols) :
    c.H0 h n k = c.σ0 k * c.phi0 h n k := rfl

theorem H1_apply (c : Chart D R cols) (h : ℝ) (n : Fin R) (k : cols) :
    c.H1 h n k = c.σ1 k * c.phi1 h n k := rfl

/-- The properties of one chart used by the proof of `thm:thb-onestep`: the paper's (I1)-(I4) for the chart, the
host/submatrix structure (F3 (a), (d)) and the parity identity (F3 (b)).  `ε_m = m mod 2`. -/
structure Ok (cs : OneStepConsts) (m : ℕ) (h : ℝ) (U : Matrix (Fin D) (Fin D) ℝ) (c : Chart D R cols) :
    Prop where
  /-- `H^{[m]}_c` is the submatrix of the host `host0` on the rows of the chart. -/
  host0_eq : ∀ n k, c.H0 h n k = c.host0 (c.row n) k
  /-- `H^{[m+1]}_c` is the submatrix of the host `host1`. -/
  host1_eq : ∀ n k, c.H1 h n k = c.host1 (c.row n) k
  /-- (I1) for the order-`m` host: `‖(host0 - U) e_j‖ ≤ C h^m`. -/
  host0_col : ∀ j : Fin D, jbL2 Finset.univ (fun i => c.host0 i j - U i j) ≤ cs.C * h ^ m
  /-- (I1) for the order-`(m+1)` host: `‖(host1 - U) e_j‖ ≤ C h^{m+1} log(1/h)`. -/
  host1_col : ∀ j : Fin D,
    jbL2 Finset.univ (fun i => c.host1 i j - U i j) ≤ cs.C * h ^ (m + 1) * Real.log (1 / h)
  /-- Parity identity `eq:thb-parity`, `A` part: `A^{[m+1]} - A^{[m]} = (1 - ε_m) h^m κ_m`. -/
  parity_A : ∀ n k, c.A1 n k - c.A0 n k = (1 - ((m % 2 : ℕ) : ℝ)) * h ^ m * c.κ n k
  /-- Parity identity, `B` part: `h (B^{[m+1]} - B^{[m]}) = ε_m h^m κ_m` (paper: `ε_m h^{m-1} B_m`). -/
  parity_B : ∀ n k, h * (c.B1 n k - c.B0 n k) = ((m % 2 : ℕ) : ℝ) * h ^ m * c.κ n k
  /-- (I2): `0 < ω ≤ ω_max`. -/
  ω_pos : ∀ n, 0 < c.ω n ∧ c.ω n ≤ cs.ωmax
  /-- (I2): exact model transfer `ω_n y_{n+τ,k} = t₁₁ y_{nk} + t₁₂ ỹ_{nk}`. -/
  transfer : ∀ n k, c.ω n * c.shifted c.y n k = c.t11 n k * c.y n k + c.t12 n k * c.yt n k
  /-- (I2): `|t₁₂| ≥ c`. -/
  t12_lb : ∀ n k, cs.cT ≤ |c.t12 n k|
  /-- (I2): `α = A^{[m+1]} - h B^{[m+1]} t₁₁/t₁₂ ≥ c > 0`. -/
  α_lb : ∀ n k, cs.cα ≤ jbAlpha c.A1 c.B1 c.t11 c.t12 h n k
  /-- (I2): Schur bound for `1/α`. -/
  schur_inv_α : IsSchurBdd (Matrix.of fun n k => 1 / jbAlpha c.A1 c.B1 c.t11 c.t12 h n k) cs.K
  /-- (I2): Schur bound for `B^{[m+1]}/(t₁₂ α)`. -/
  schur_B : IsSchurBdd (Matrix.of fun n k => c.B1 n k / (c.t12 n k * jbAlpha c.A1 c.B1 c.t11 c.t12 h n k)) cs.K
  /-- (I2): Schur bound for `1/t₁₂`. -/
  schur_inv_t12 : IsSchurBdd (Matrix.of fun n k => 1 / c.t12 n k) cs.K
  /-- (I2): Schur bound for `t₁₁/t₁₂`. -/
  schur_t11 : IsSchurBdd (Matrix.of fun n k => c.t11 n k / c.t12 n k) cs.K
  /-- (I2): Schur bound for the changed coefficient `κ_m`. -/
  schur_κ : IsSchurBdd c.κ cs.K
  /-- (I3): the exterior row `(ω_n σ^{[m+1]}_k y_ext,k)_k` (on the row of `I⁺` next to it) has `ℓ²`-norm `≤ C_E`. -/
  ext_row : ∀ n : Fin R, (c.τ = true → n.val + 1 = R) → (c.τ = false → n.val = 0) →
    jbL2 Finset.univ (fun k => c.ω n * c.σ1 k * c.yext k) ≤ cs.CE
  /-- (I4): `‖P_k Ψ_k‖ ≥ c₀`, `Ψ_k` the `k`-th column of `U`. -/
  overlap_lb : ∀ k : cols, cs.c0 ≤ jbL2 (c.P k) (fun n => U (c.row n) k)
  /-- (I4): `‖P_k y‖ + ‖P_k ỹ‖ ≤ C ‖P_k φ^{[m+1]}‖`. -/
  overlap_ub : ∀ k : cols,
    jbL2 (c.P k) (fun n => c.y n k) + jbL2 (c.P k) (fun n => c.yt n k) ≤
      cs.C4 * jbL2 (c.P k) (fun n => c.phi1 h n k)

end Chart

/-- **The inputs of the one-step criterion** (Paper J, `def:thb-inputs` (I1)-(I5) together with the structural
facts of F3), for the constants `cs`, `D` columns, order `m` and step `h`.  See the module docstring for which
paper statement discharges each field. -/
structure OneStepInputs (cs : OneStepConsts) (D m : ℕ) (h : ℝ) where
  /-- `U_h`, `Ĝ^{[m]}` and `Ĝ^{[m+1]}` at the fixed splices. -/
  U : Matrix (Fin D) (Fin D) ℝ
  G0 : Matrix (Fin D) (Fin D) ℝ
  G1 : Matrix (Fin D) (Fin D) ℝ
  /-- the column set `Σ_ν` of block `ν`. -/
  cols : Fin cs.nb → Finset (Fin D)
  /-- the number of rows `|I⁺|` of each chart. -/
  R : Fin cs.nb → Fin 2 → ℕ
  /-- the two charts of block `ν` (bulk left/right, or soft left/right half). -/
  ch : (ν : Fin cs.nb) → (j : Fin 2) → Chart D (R ν j) (cols ν)
  /-- the bound `ε5` of (I5) (`C h^{-K} e^{-c/h}`). -/
  ε5 : ℝ
  h_pos : 0 < h
  one_le_m : 1 ≤ m
  U_orth : Uᵀ * U = 1
  cols_disjoint : ∀ ν ν', ν ≠ ν' → Disjoint (cols ν) (cols ν')
  chart_ok : ∀ ν j, (ch ν j).Ok cs m h U
  /-- (I1) for the final `Ĝ^{[m+1]}`: `‖(Ĝ^{[m+1]} - U) e_k‖ ≤ C h^{m+1} log(1/h)`. -/
  G1_col : ∀ j : Fin D, jbL2 Finset.univ (fun i => G1 i j - U i j) ≤ cs.C * h ^ (m + 1) * Real.log (1 / h)
  /-- `Ĝ^{[m]}` agrees with `H^{[m]}_c` on the used rows of every chart and its columns. -/
  match0 : ∀ ν j n, n ∈ (ch ν j).used → ∀ k : cols ν, G0 ((ch ν j).row n) k = (ch ν j).H0 h n k
  /-- `Ĝ^{[m+1]}` agrees with `H^{[m+1]}_c` there. -/
  match1 : ∀ ν j n, n ∈ (ch ν j).used → ∀ k : cols ν, G1 ((ch ν j).row n) k = (ch ν j).H1 h n k
  ε5_nonneg : 0 ≤ ε5
  /-- (I5): entries of `Ĝ^{[m]}`, `Ĝ^{[m+1]}` and `U` outside all used chart blocks are at most `ε5`. -/
  outside : ∀ i k : Fin D,
    (¬ ∃ (ν : Fin cs.nb) (j : Fin 2) (n : Fin (R ν j)),
        n ∈ (ch ν j).used ∧ (ch ν j).row n = i ∧ k ∈ cols ν) →
      |G0 i k| ≤ ε5 ∧ |G1 i k| ≤ ε5 ∧ |U i k| ≤ ε5

/-- The explicit smallness conditions ("for `h` small") of `thm:thb-onestep`: all are `h`-dependent numbers
made small by `h → 0` with `D = L/h` (`√D h^{m+1} log(1/h) = O(h^{m+1/2} log(1/h))`, `D ε5 = O(h^{-1-K} e^{-c/h})`):
`h ≤ 1`, Step 1 (`‖Ĝ^{[m+1]} - U‖_F ≤ √D η₁ ≤ 1`, so every host has norm `≤ 2`), Step 2
(uniform margins `ε = K C₄ h^m ≤ 1/2`, `δ = C h^m ≤ c₀/2`; the condition `C h^{m+1} log(1/h) < c₀` is
not needed, it follows from `C h^m ≤ c₀/2` and `h log(1/h) ≤ 1`), Step 3 (`h K ω_max ≤ 1/2`), Step 5
(`2 D ε5 ≤ h^m`). -/
def OneStepInputs.Small {cs : OneStepConsts} {D m : ℕ} {h : ℝ} (I : OneStepInputs cs D m h) : Prop :=
  h ≤ 1 ∧
  √(D : ℝ) * (cs.C * h ^ (m + 1) * Real.log (1 / h)) ≤ 1 ∧
  cs.K * cs.C4 * h ^ m ≤ 1 / 2 ∧
  cs.C * h ^ m ≤ cs.c0 / 2 ∧
  h * cs.K * cs.ωmax ≤ 1 / 2 ∧
  2 * (D : ℝ) * I.ε5 ≤ h ^ m

/-- **The one-step criterion** (Paper J, `thm:thb-onestep`), stated as a proposition: for every order `m` there
is a constant `C*`, depending only on the constants `cs` (and `m`), such that for every admissible `D, h` and every
`OneStepInputs` satisfying `Small`,
`‖Ĝ^{[m]} - Ĝ^{[m+1]}‖ ≤ C* h^m`, `‖Ĝ^{[m]} - U‖ ≤ C* h^m + √D C h^{m+1} log(1/h)`, and, when this is `< 1`,
the polar factor `Ĝ^{[m]} (Ĝ^{[m]ᵀ} Ĝ^{[m]})^{-1/2}` is orthogonal and within twice that distance of `U`
(the third inequality of `eq:thb-onestep`, which is `jb_polar`).  Proved in the next stage. -/
def OneStepReduction (cs : OneStepConsts) : Prop :=
  ∀ m : ℕ, ∃ Cstar : ℝ, ∀ (D : ℕ) (h : ℝ) (I : OneStepInputs cs D m h), I.Small →
    ‖I.G0 - I.G1‖ ≤ Cstar * h ^ m ∧
    ‖I.G0 - I.U‖ ≤ Cstar * h ^ m + √(D : ℝ) * (cs.C * h ^ (m + 1) * Real.log (1 / h)) ∧
    (‖I.G0 - I.U‖ < 1 →
      (I.G0 * (CFC.sqrt (I.G0ᵀ * I.G0))⁻¹)ᵀ * (I.G0 * (CFC.sqrt (I.G0ᵀ * I.G0))⁻¹) = 1 ∧
      ‖I.G0 * (CFC.sqrt (I.G0ᵀ * I.G0))⁻¹ - I.U‖ ≤ 2 * ‖I.G0 - I.U‖)

/-! ### Non-vacuity: a degenerate toy instance (`D = 1`, `G = U = 1`)

One block, two charts on the single column and single row; model pair `y = 1`, `ỹ = 0`, `y_ext = 1`,
`ω = t₁₁ = t₁₂ = A = σ = 1`, `B = κ = 0`, `m = 1`, `h = 1/2`.  It shows that `OneStepInputs` and `Small` are
jointly satisfiable; it does not exercise the estimates (`H = U`). -/

section Toy

/-- The constants of the toy instance (all equal to `1`, one block). -/
def toyConsts : OneStepConsts where
  nb := 1
  C := 1
  K := 1
  ωmax := 1
  cT := 1
  cα := 1
  c0 := 1
  C4 := 1
  CE := 1
  C_nonneg := zero_le_one
  K_nonneg := zero_le_one
  ωmax_pos := one_pos
  cT_pos := one_pos
  cα_pos := one_pos
  c0_pos := one_pos
  C4_nonneg := zero_le_one
  CE_nonneg := zero_le_one

/-- The column type of the toy charts. -/
abbrev ToyCols : Type := ↥(Finset.univ : Finset (Fin 1))

/-- The toy chart; the second chart of the block (`used = ∅`) differs only in `used`. -/
def toyChart (u : Finset (Fin 1)) : Chart 1 1 Finset.univ where
  lo := 0
  lo_add := le_rfl
  τ := true
  used := u
  y := Matrix.of fun _ _ => 1
  yt := Matrix.of fun _ _ => 0
  yext := fun _ => 1
  ω := fun _ => 1
  t11 := Matrix.of fun _ _ => 1
  t12 := Matrix.of fun _ _ => 1
  A0 := Matrix.of fun _ _ => 1
  A1 := Matrix.of fun _ _ => 1
  B0 := Matrix.of fun _ _ => 0
  B1 := Matrix.of fun _ _ => 0
  κ := Matrix.of fun _ _ => 0
  σ0 := fun _ => 1
  σ1 := fun _ => 1
  P := fun _ => Finset.univ
  host0 := 1
  host1 := 1

theorem jbAlpha_apply {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (A B t11 t12 : Matrix ι κ ℝ)
    (h : ℝ) (n : ι) (k : κ) : jbAlpha A B t11 t12 h n k = A n k - h * B n k * t11 n k / t12 n k := rfl

section ToyEntries
variable (u : Finset (Fin 1))
@[simp] theorem toyChart_row (n : Fin 1) : (toyChart u).row n = 0 := Subsingleton.elim _ _
@[simp] theorem toyChart_τ : (toyChart u).τ = true := rfl
@[simp] theorem toyChart_used : (toyChart u).used = u := rfl
@[simp] theorem toyChart_P (k : ToyCols) : (toyChart u).P k = Finset.univ := rfl
@[simp] theorem toyChart_ω (n : Fin 1) : (toyChart u).ω n = 1 := rfl
@[simp] theorem toyChart_σ0 (k : ToyCols) : (toyChart u).σ0 k = 1 := rfl
@[simp] theorem toyChart_σ1 (k : ToyCols) : (toyChart u).σ1 k = 1 := rfl
@[simp] theorem toyChart_yext (k : ToyCols) : (toyChart u).yext k = 1 := rfl
@[simp] theorem toyChart_host0 : (toyChart u).host0 = 1 := rfl
@[simp] theorem toyChart_host1 : (toyChart u).host1 = 1 := rfl
@[simp] theorem toyChart_y (n : Fin 1) (k : ToyCols) : (toyChart u).y n k = 1 := rfl
@[simp] theorem toyChart_yt (n : Fin 1) (k : ToyCols) : (toyChart u).yt n k = 0 := rfl
@[simp] theorem toyChart_t11 (n : Fin 1) (k : ToyCols) : (toyChart u).t11 n k = 1 := rfl
@[simp] theorem toyChart_t12 (n : Fin 1) (k : ToyCols) : (toyChart u).t12 n k = 1 := rfl
@[simp] theorem toyChart_A0 (n : Fin 1) (k : ToyCols) : (toyChart u).A0 n k = 1 := rfl
@[simp] theorem toyChart_A1 (n : Fin 1) (k : ToyCols) : (toyChart u).A1 n k = 1 := rfl
@[simp] theorem toyChart_B0 (n : Fin 1) (k : ToyCols) : (toyChart u).B0 n k = 0 := rfl
@[simp] theorem toyChart_B1 (n : Fin 1) (k : ToyCols) : (toyChart u).B1 n k = 0 := rfl
@[simp] theorem toyChart_κ (n : Fin 1) (k : ToyCols) : (toyChart u).κ n k = 0 := rfl
end ToyEntries

theorem one_apply_fin1 (i j : Fin 1) : (1 : Matrix (Fin 1) (Fin 1) ℝ) i j = 1 := by
  rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]; simp

theorem toyChart_ok (u : Finset (Fin 1)) :
    (toyChart u).Ok toyConsts 1 (1 / 2 : ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  have hlog : 0 ≤ Real.log (1 / (1 / 2 : ℝ)) := Real.log_nonneg (by norm_num)
  have hα : ∀ (h : ℝ) n k,
      jbAlpha (toyChart u).A1 (toyChart u).B1 (toyChart u).t11 (toyChart u).t12 h n k = 1 := by
    intro h n k; simp [jbAlpha_apply]
  have hφ : ∀ (h : ℝ) n k, (toyChart u).phi1 h n k = 1 := by
    intro h n k; simp [Chart.phi1_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n k; simp [Chart.H0_apply, Chart.phi0_apply, one_apply_fin1]
  · intro n k; simp [Chart.H1_apply, Chart.phi1_apply, one_apply_fin1]
  · intro j; simp [jbL2, toyConsts, one_apply_fin1]
  · intro j; simp [jbL2, toyConsts, one_apply_fin1]; positivity
  · intro n k; simp
  · intro n k; simp
  · intro n; simp [toyConsts]
  · intro n k; simp [Chart.shifted, Ysh]
  · intro n k; simp [toyConsts]
  · intro n k; rw [hα]; simp [toyConsts]
  · have e : (Matrix.of fun n k => 1 / jbAlpha (toyChart u).A1 (toyChart u).B1 (toyChart u).t11
        (toyChart u).t12 (1 / 2 : ℝ) n k) = Matrix.of fun _ _ => (1 : ℝ) := by
      ext n k; simp [hα]
    rw [e]; exact (isSchurBdd_const 1).mono (by simp [toyConsts])
  · have e : (Matrix.of fun n k => (toyChart u).B1 n k / ((toyChart u).t12 n k *
        jbAlpha (toyChart u).A1 (toyChart u).B1 (toyChart u).t11 (toyChart u).t12 (1 / 2 : ℝ) n k)) =
        Matrix.of fun _ _ => (0 : ℝ) := by
      ext n k; simp
    rw [e]; exact (isSchurBdd_const 0).mono (by simp [toyConsts])
  · have e : (Matrix.of fun n k => 1 / (toyChart u).t12 n k) = Matrix.of fun _ _ => (1 : ℝ) := by
      ext n k; simp
    rw [e]; exact (isSchurBdd_const 1).mono (by simp [toyConsts])
  · have e : (Matrix.of fun n k => (toyChart u).t11 n k / (toyChart u).t12 n k) =
        Matrix.of fun _ _ => (1 : ℝ) := by
      ext n k; simp
    rw [e]; exact (isSchurBdd_const 1).mono (by simp [toyConsts])
  · have e : (toyChart u).κ = Matrix.of fun _ _ => (0 : ℝ) := by ext n k; simp
    rw [e]; exact (isSchurBdd_const 0).mono (by simp [toyConsts])
  · intro n _ _; simp [jbL2, toyConsts]
  · intro k; simp [jbL2, toyConsts, one_apply_fin1]
  · intro k; simp [jbL2, toyConsts, hφ]

/-- The toy inputs: `D = 1`, `m = 1`, `h = 1/2`, `G = U = 1`; chart `0` uses the row, chart `1` none. -/
def toyInputs : OneStepInputs toyConsts 1 1 (1 / 2 : ℝ) where
  U := 1
  G0 := 1
  G1 := 1
  cols := fun _ => Finset.univ
  R := fun _ _ => 1
  ch := fun _ j => toyChart (if j = 0 then Finset.univ else ∅)
  ε5 := 0
  h_pos := by norm_num
  one_le_m := le_rfl
  U_orth := by simp
  cols_disjoint := fun ν ν' h => absurd (Fin.ext (by have := ν.2; have := ν'.2; simp [toyConsts] at *; omega)) h
  chart_ok := fun _ _ => toyChart_ok _
  G1_col := fun j => by simp [jbL2, toyConsts, one_apply_fin1]; positivity
  match0 := fun ν j n hn k => by
    simp [Chart.H0_apply, Chart.phi0_apply, one_apply_fin1]
  match1 := fun ν j n hn k => by
    simp [Chart.H1_apply, Chart.phi1_apply, one_apply_fin1]
  ε5_nonneg := le_rfl
  outside := fun i k h => by
    exfalso; apply h
    exact ⟨⟨0, Nat.one_pos⟩, 0, 0, by simp, Subsingleton.elim _ _, Finset.mem_univ _⟩

theorem toyInputs_small : toyInputs.Small := by
  have hlog : Real.log (1 / (1 / 2 : ℝ)) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 / (1 / 2) by norm_num)
    linarith
  have hlog0 : 0 ≤ Real.log (1 / (1 / 2 : ℝ)) := Real.log_nonneg (by norm_num)
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [toyConsts, toyInputs] <;> nlinarith

/-- info: 'FormalResearch.JB.toyInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JB.toyInputs

/-- info: 'FormalResearch.JB.toyInputs_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JB.toyInputs_small

end Toy

end FormalResearch.JB
