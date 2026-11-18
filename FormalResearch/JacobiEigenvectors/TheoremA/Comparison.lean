module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.ChartInputs

/-!
# Paper J, Theorem A: the explicit comparison vectors `Psi-hat_k^{(m)}` and envelopes `V_{k,n}` (definitions)

Source: Paper J `thmA.tex`: eq:tha-kappahat (bulk gluing), eq:tha-kappa2 (soft gluing), eq:tha-G14, eq:tha-W2-2 (the envelopes `V_n`),
`def:tha-Psihat` (the three cases `X_k in J`, `X_k > X_s^+ - delta_0`, `X_k < X_s^- + delta_0`, the last through the gauge `(-1)^n`).

Everything here is a *definition* from the chart inputs; there is no statement.  The vectors are explicit: they use only the chart data at the
frozen parameter `(mu, t = h)` and the energy `X_k` (an eigenvalue), never an eigenvector.

## Dictionary

| Lean | paper |
|---|---|
| `glueKappa`, `glueNorm`, `glueVec` | `hat kappa`, `hat N`, `hat Psi` (the matched, normalised glued vector) |
| `bulkVec`, `bulkEnv` | `hat Psi` and `V_n / hat N` of prop:tha-W (2) (eq:tha-G14) |
| `softVec`, `softEnv` | `hat Psi` and `V_n / hat N` of prop:tha-W2 (2) (eq:tha-W2-2) |
| `psiHatVec`, `envVec` | `hat Psi^{(m)}_k`, `V_{k,n}` of def:tha-Psihat (all three cases) |
| `bulkWindow`, `softWindow` | `Omega_nu = {c' <= u_n <= c}`, `Omega = {|Z_n| <= 2 sqrt(max(-a,0)) + (1+max(-a,0))^{-1/6}}` |

## Conventions

* rows are `n in {0,...,N}` as integers; the right chart is a chart of the mirror family and `psi-hat^R_n` is its left sequence at row `N - n`;
* the glued vector is `psi-hat^L / hat N` for `n <= n_s` and `hat kappa psi-hat^R / hat N` beyond, where the split is
  `u_n <= c` (bulk) or `Z_n <= 0` (soft: `u_n <= u_*`, `zeta(u_* - u_c) = 0`);
* `hat N = sqrt(sum_{left} (psi-hat^L)^2 + hat kappa^2 sum_{right} (psi-hat^R)^2)` (positive square root);
* at a lower soft edge the vector is built for the gauge family at energy `-X` and multiplied by `(-1)^n`; the envelope is unchanged.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts
open scoped Classical

/-- `hat kappa = sum_Omega psi^L psi^R / sum_Omega (psi^R)^2` (eq:tha-kappahat, eq:tha-kappa2). -/
def glueKappa (ψL ψR : ℤ → ℝ) (Ω : Finset ℤ) : ℝ := (∑ n ∈ Ω, ψL n * ψR n) / ∑ n ∈ Ω, ψR n ^ 2

/-- `hat N`: the normaliser of the glued vector. `rows` are all rows, `isLeft n` says that row `n` is taken from the left sequence. -/
def glueNorm (ψL ψR : ℤ → ℝ) (Ω rows : Finset ℤ) (isLeft : ℤ → Prop) : ℝ :=
  Real.sqrt ((∑ n ∈ rows.filter isLeft, ψL n ^ 2) + glueKappa ψL ψR Ω ^ 2 * ∑ n ∈ rows.filter (fun n => ¬ isLeft n), ψR n ^ 2)

/-- The glued, normalised vector `hat Psi`. -/
def glueVec (ψL ψR : ℤ → ℝ) (Ω rows : Finset ℤ) (isLeft : ℤ → Prop) (n : ℤ) : ℝ :=
  if isLeft n then ψL n / glueNorm ψL ψR Ω rows isLeft
  else glueKappa ψL ψR Ω * ψR n / glueNorm ψL ψR Ω rows isLeft

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ}
  {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- All rows `0..N`. -/
def rowsOf (N : ℕ) : Finset ℤ := Finset.Icc (0 : ℤ) (N : ℤ)

/-! ### Bulk -/

/-- The overlap window `Omega_nu = {n : c' <= u_n <= c}` of the bulk chart. -/
def bulkWindow (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (N : ℕ) : Finset ℤ :=
  (rowsOf N).filter (fun n => CI.bulkL.c' ≤ uNode (F.step N) n ∧ uNode (F.step N) n ≤ CI.bulkL.c)

/-- Left sequence of the bulk chart. -/
def bulkL (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (p : Par × ℝ) (X : ℝ) (N : ℕ) : ℤ → ℝ :=
  CI.bulkL.psiHatL p X N

/-- Right sequence of the bulk chart: the left sequence of the mirror chart at row `N - n`. -/
def bulkR (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (p : Par × ℝ) (X : ℝ) (N : ℕ) : ℤ → ℝ :=
  fun n => CI.bulkR.psiHatL p X N ((N : ℤ) - n)

/-- `hat kappa` of prop:tha-W (2). -/
def bulkKappa (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (p : Par × ℝ) (X : ℝ) (N : ℕ) : ℝ :=
  glueKappa (bulkL CI p X N) (bulkR CI p X N) (bulkWindow CI N)

/-- `hat N` of prop:tha-W (2). -/
def bulkNorm (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (p : Par × ℝ) (X : ℝ) (N : ℕ) : ℝ :=
  glueNorm (bulkL CI p X N) (bulkR CI p X N) (bulkWindow CI N) (rowsOf N) (fun n => uNode (F.step N) n ≤ CI.bulkL.c)

/-- `hat Psi` of prop:tha-W (2). -/
def bulkVec (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (p : Par × ℝ) (X : ℝ) (N : ℕ) : ℤ → ℝ :=
  glueVec (bulkL CI p X N) (bulkR CI p X N) (bulkWindow CI N) (rowsOf N) (fun n => uNode (F.step N) n ≤ CI.bulkL.c)

/-- `V_n / hat N` of eq:tha-G14: `E^L M^L` for `u_n <= c`, `|hat kappa| E^R M^R` beyond. -/
def bulkEnv (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (p : Par × ℝ) (X : ℝ) (N : ℕ) (n : ℤ) : ℝ :=
  (if uNode (F.step N) n ≤ CI.bulkL.c then CI.bulkL.envL p X N n
   else |bulkKappa CI p X N| * CI.bulkR.envL p X N ((N : ℤ) - n)) / bulkNorm CI p X N

/-! ### Soft edge (upper) -/

/-- `rho = 2 sqrt(max(-a,0)) + (1 + max(-a,0))^{-1/6}`: the half-width of the window in `Z` (eq:tha-winnot). -/
def rhoWin (a : ℝ) : ℝ := 2 * Real.sqrt (max (-a) 0) + (1 + max (-a) 0) ^ (-(1 : ℝ) / 6)

/-- The soft window `Omega = {n : |Z_n| <= rho}` (the well with an Airy layer). -/
def softWindow {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} (C : SoftEdgeChart Fz P m q U V) (p : Par × ℝ) (X : ℝ)
    (N : ℕ) : Finset ℤ :=
  (rowsOf N).filter (fun n => |C.Zof p X N n| ≤ rhoWin (C.aOf p X N))

/-- The Weber envelope `E_Web M_Web` of the soft chart at row `k` (patch 1). -/
def softEnvWeb {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} (C : SoftEdgeChart Fz P m q U V) (p : Par × ℝ) (X : ℝ)
    (N : ℕ) (k : ℤ) : ℝ :=
  Ewell (-((k : ℝ) + 1 / 2)) |C.Y p X (uNode (Fz.step N) k) / Real.sqrt (Fz.step N)|
    * Mbal (-((k : ℝ) + 1 / 2)) (C.Y p X (uNode (Fz.step N) k) / Real.sqrt (Fz.step N))

variable (CL : SoftEdgeChart (frozenFamily F Kidx) (paramSet K t0) m q U V)
  (CR : SoftEdgeChart (mirrorFamily (frozenFamily F Kidx)) (paramSet K t0) m q U V)

/-- The left sequence of the upper soft edge (`psi-hat^L`) and the right one (`psi-hat^R`, mirror chart at row `N - n`). -/
def softSeqR (p : Par × ℝ) (X : ℝ) (N : ℕ) : ℤ → ℝ := fun n => CR.psiHatL p X N ((N : ℤ) - n)

/-- `hat kappa` of eq:tha-kappa2. -/
def softKappa (p : Par × ℝ) (X : ℝ) (N : ℕ) : ℝ :=
  glueKappa (CL.psiHatL p X N) (softSeqR CR p X N) (softWindow CL p X N)

/-- `hat N` of eq:tha-kappa2 (left part `Z_n <= 0`, i.e. `u_n <= u_*`). -/
def softNorm (p : Par × ℝ) (X : ℝ) (N : ℕ) : ℝ :=
  glueNorm (CL.psiHatL p X N) (softSeqR CR p X N) (softWindow CL p X N) (rowsOf N) (fun n => CL.Zof p X N n ≤ 0)

/-- `hat Psi` of prop:tha-W2 (2). -/
def softVec (p : Par × ℝ) (X : ℝ) (N : ℕ) : ℤ → ℝ :=
  glueVec (CL.psiHatL p X N) (softSeqR CR p X N) (softWindow CL p X N) (rowsOf N) (fun n => CL.Zof p X N n ≤ 0)

/-- `V_n / hat N` of eq:tha-W2-2: four pieces (Weber, left PC, right PC, right Weber). -/
def softEnv (p : Par × ℝ) (X : ℝ) (N : ℕ) (n : ℤ) : ℝ :=
  (if uNode ((frozenFamily F Kidx).step N) n ≤ CL.uc p - CL.η / 2 then softEnvWeb CL p X N n
   else if CL.Zof p X N n ≤ 0 then |CL.lamL p X N| * Molv U V (CL.aOf p X N) (-(CL.Zof p X N n))
   else if uNode ((frozenFamily F Kidx).step N) n < CL.uc p + CL.η / 2 then
     |softKappa CL CR p X N * CR.lamL p X N| * Molv U V (CL.aOf p X N) (CL.Zof p X N n)
   else |softKappa CL CR p X N| * softEnvWeb CR p X N ((N : ℤ) - n)) / softNorm CL CR p X N

/-! ### The three cases of `def:tha-Psihat` -/

/-- The frozen parameter `(mu, t = h)` at which the vectors are evaluated (`h = L/(N+1)`). -/
def atStep (F : SymbolFamily Par) (μ : Par) (N : ℕ) : Par × ℝ := (μ, F.step N)

/-- `hat Psi^{(m)}`: for the energy `X` (an eigenvalue of `J_h`), the vector of prop:tha-W (2) if `X in [Jlo, Jhi]`, of prop:tha-W2 (2) at
the upper edge if `X > Jhi`, and the gauge vector `(-1)^n hat Psi` of the family `-(-1)^n J (-1)^n` at energy `-X` if `X < Jlo`
(`def:tha-Psihat`; the three cases exhaust the eigenvalues, `Step 0` of app_thmA). -/
def psiHatVec (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (μ : Par) (N : ℕ) (X : ℝ) (n : ℤ) : ℝ :=
  if CI.Jlo ≤ X ∧ X ≤ CI.Jhi then bulkVec CI (atStep F μ N) X N n
  else if CI.Jhi < X then softVec CI.softUpL CI.softUpR (atStep F μ N) X N n
  else (-1 : ℝ) ^ n * softVec CI.softLoL CI.softLoR (atStep F μ N) (-X) N n

/-- The envelope `V_{k,n} = V_n / hat N` of `def:tha-Psihat`. -/
def envVec (CI : ChartInputs F K Kidx t0 m q U V cPC CPC) (μ : Par) (N : ℕ) (X : ℝ) (n : ℤ) : ℝ :=
  if CI.Jlo ≤ X ∧ X ≤ CI.Jhi then bulkEnv CI (atStep F μ N) X N n
  else if CI.Jhi < X then softEnv CI.softUpL CI.softUpR (atStep F μ N) X N n
  else softEnv CI.softLoL CI.softLoR (atStep F μ N) (-X) N n

end FormalResearch.JacobiEigenvectors.TheoremA
