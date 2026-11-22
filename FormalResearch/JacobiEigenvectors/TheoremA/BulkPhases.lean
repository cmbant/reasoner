module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.BulkWeber
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkPhasesPC
public import FormalResearch.JacobiEigenvectors.TheoremA.BulkNormalisation
public import FormalResearch.JacobiEigenvectors.TheoremA.MonotoneAction

/-!
# Paper J, Layer 2: the phases of the bulk comparison sequences (`lem:smo-bulkphase` (1), L2.S1)

Source: Paper J `app_thmA.tex`, `lem:smo-bulkphase` (1) ("Phases"), proof: "`psi-hat^L_n = A^{[m]} w^{(1)}_n(Z_n) + h B^{[m]} h^{1/2} d_z w^{(1)}_n(Z_n)` with `A^{[m]} = g_0 + O(h^2)`, `g_0 > 0`.  Put `mu^2 = 2n+1`
... the trigonometric expansion DLMF 12.10.18 ... gives phase `Theta_L(u_n)/h - pi/4` ...; the corrector term is `O(h)` times the same envelope".

## Proved here (axiom-pinned)

* `bulk_phase_left` (**`lem:smo-bulkphase` (1), left sequence; the right sequence is the same theorem for the mirror chart**): for a bulk Weber chart `C` and `ParabolicCylinderFacts U V`, there are
  `c1 > 0`, `C1 >= 0`, `h0 > 0` such that on every overlap row `n` (`0 <= n <= N_R`, `c' <= u_n`) of every `(mu, X, N)` with `N >= N0`, `h <= h0`, there is `rho >= c1 h^{1/4}` with
  `|psi-hat^L_n - rho cos(Theta_L(u_n)/h - pi/4)| <= C1 h rho`, `Theta_L(u) = int_0^u arccos(...) = thetaL`.  The amplitude is explicit, `rho = A^{[m]}(u_n) kappa_bal 2 g(mu) (1-t^2)^{-1/4}`.
* `phase_arith`, `psiHatL_row`, `overlap_t_bound`, `thetaL_eq`: the pieces (arithmetic of the two error terms; the row formula from `wf_eq`; `|t| <= 1 - eps` from `turn_eq`, `Hz_lb`, `overlap_in_well`;
  `Theta_L = u (arccos t - t sqrt(1-t^2))` from `matchO` and the calculus identity of `TheoremA/BulkPhasesPC.lean`).

## Findings F-S1-1, F-S1-2 (checked against the paper; recorded in `PLAN.md`)

* **F-S1-1 (leading corrector row): CONFIRMED, added as the chart field `BulkWeberChart.corr_lead`** (`Charts/BulkWeber.lean`): `A^{[m]} = g_0 + O(h^2)` with `g_0 >= c_g > 0` and `|B^{[m]}| <= C_g`
  (i.e. `h B = O(h)`).  The paper has it (`prop:cha-halfrow`, `lem:cha-weber-coord` (3), `thm:eng-corr`: `g_0 = V_0^{-1/2}`, `B^{[m]} = sum h^{2i-2} B_{2i-1}`).  Refinement of agent Q's statement: besides `g_0 > 0` the
  *size of `h B`* is needed (`A_bd`, `B_bd` only say `|h B| <= K_B`), otherwise the row `(A, h B)` could be rotated by an angle `O(1)` and the phase would change.  It is not derivable from `Valid`.
* **F-S1-2 (derivative of `phase_osc`, DLMF 12.10.19): REFINED, no field needed.**  Only the *envelope bound* `|U'| <= C mu 2 g(mu)` is used (the term `h B h^{1/2} U'` is `O(h)` times the envelope), and that follows from
  `phase_osc` and the differential equation by interpolation on a window of length `1/mu` (`phase_value_deriv_bound`, `TheoremA/BulkPhasesPC.lean`); the *phase* of `U'` is not used by anything.
* **F-S1-4 (new): the uniform margin `theta in [eps, pi - eps]` of `lem:smo-bulkphase` (2) on the overlap** is not derivable from the chart fields; added as `BulkWeberChart.theta_margin`; it is used
  only in the sign argument (iii) (`TheoremA/BulkPhasesKappa.lean`, `BulkWindows.lean`), not here.

## Differences from the paper

* `rho` is existential with the explicit formula and the lower bound `rho >= c1 h^{1/4}` (`rho >~ h^{1/4}` of the paper); the paper's `rho(u_{n+1}) = rho(u_n) (1 + O(h))` and the continuity of `rho` in `X`
  are **not** proved (the first needs the shift relation `U(a-1, z) = (z/2) U - U'` with DLMF 12.10.19 for the ratio `g(mu_{n+1})/g(mu_n)`; they are used only in `lem:smo-bulkphase` (2), which the formalisation
  replaces by (4) with a positive prefactor, `BulkPhaseInputs.casoratian`).
* `O(h)` and the thresholds are uniform in `(mu, X, N)`; `h <= h0` (`h0` explicit, depends on `mu_1` of `phase_osc` and `c_g`).

## Not formalised

`rho(u_{n+1}) = rho(u_n)(1+O(h))`, continuity of `rho` in `X`, the trigonometric `sin theta` form (2) of the Casoratian.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.Engine

/-- Pure arithmetic of the phase expansion: amplitude `rho = A kappa G w` with `w >= 1`, error terms from the value expansion and from the derivative term. -/
lemma phase_arith {A κ G w cs Uv Ud h q Bc cg Cg Cp Cd c' cc : ℝ}
    (hA : cg / 2 ≤ A) (hcg : 0 < cg) (hκ : 0 < κ) (hG : 0 < G) (hw : 1 ≤ w) (hh : 0 < h)
    (hBc : |h * Bc| ≤ Cg * h) (hCg : 0 ≤ Cg) (hCp : 0 ≤ Cp) (hCd : 0 ≤ Cd) (hq : 0 < q)
    (hU : |Uv - G * w * cs| ≤ Cp * (h / (2 * c')) * (G * w)) (hc' : 0 < c')
    (hUd : |Ud| ≤ Cd * q * G) (hqh : q * Real.sqrt h ≤ Real.sqrt (2 * cc)) :
    |A * (κ * Uv) + (h * Bc) * (Real.sqrt h * (κ * Ud)) - (A * κ * (G * w)) * cs|
      ≤ (Cp / (2 * c') + 2 * Cg * Cd * Real.sqrt (2 * cc) / cg) * h * (A * κ * (G * w)) := by
  have hA0 : 0 < A := by linarith
  have hrho : 0 < A * κ * (G * w) := by positivity
  have hsq : 0 ≤ Real.sqrt h := Real.sqrt_nonneg _
  have e1 : A * (κ * Uv) - (A * κ * (G * w)) * cs = A * κ * (Uv - G * w * cs) := by ring
  have h1 : |A * κ * (Uv - G * w * cs)| ≤ (Cp / (2 * c')) * h * (A * κ * (G * w)) := by
    rw [abs_mul, abs_of_pos (mul_pos hA0 hκ)]
    calc A * κ * |Uv - G * w * cs| ≤ A * κ * (Cp * (h / (2 * c')) * (G * w)) :=
          mul_le_mul_of_nonneg_left hU (by positivity)
      _ = (Cp / (2 * c')) * h * (A * κ * (G * w)) := by ring
  -- derivative term
  have h2 : |(h * Bc) * (Real.sqrt h * (κ * Ud))| ≤ (2 * Cg * Cd * Real.sqrt (2 * cc) / cg) * h * (A * κ * (G * w)) := by
    rw [abs_mul (h * Bc) (Real.sqrt h * (κ * Ud)), abs_mul (Real.sqrt h) (κ * Ud), abs_mul κ Ud, abs_of_nonneg hsq, abs_of_pos hκ]
    have hκG : κ * G ≤ (2 / cg) * (A * κ * (G * w)) := by
      have : cg / 2 * (κ * G) ≤ A * κ * (G * w) := by
        have h1 : κ * G ≤ κ * G * w := le_mul_of_one_le_right (by positivity) hw
        calc cg / 2 * (κ * G) ≤ A * (κ * G) := mul_le_mul_of_nonneg_right hA (by positivity)
          _ ≤ A * (κ * G * w) := mul_le_mul_of_nonneg_left h1 hA0.le
          _ = A * κ * (G * w) := by ring
      rw [div_mul_eq_mul_div, le_div_iff₀ hcg]
      nlinarith
    have hUd' : |Ud| * Real.sqrt h ≤ Cd * Real.sqrt (2 * cc) * G := by
      calc |Ud| * Real.sqrt h ≤ Cd * q * G * Real.sqrt h := mul_le_mul_of_nonneg_right hUd hsq
        _ = Cd * G * (q * Real.sqrt h) := by ring
        _ ≤ Cd * G * Real.sqrt (2 * cc) := mul_le_mul_of_nonneg_left hqh (by positivity)
        _ = Cd * Real.sqrt (2 * cc) * G := by ring
    calc |h * Bc| * (Real.sqrt h * (κ * |Ud|)) = |h * Bc| * (κ * (|Ud| * Real.sqrt h)) := by ring
      _ ≤ (Cg * h) * (κ * (Cd * Real.sqrt (2 * cc) * G)) := by
          apply mul_le_mul hBc _ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hUd' hκ.le
      _ = (Cg * h * Cd * Real.sqrt (2 * cc)) * (κ * G) := by ring
      _ ≤ (Cg * h * Cd * Real.sqrt (2 * cc)) * ((2 / cg) * (A * κ * (G * w))) :=
          mul_le_mul_of_nonneg_left hκG (by positivity)
      _ = (2 * Cg * Cd * Real.sqrt (2 * cc) / cg) * h * (A * κ * (G * w)) := by ring
  have e3 : A * (κ * Uv) + (h * Bc) * (Real.sqrt h * (κ * Ud)) - (A * κ * (G * w)) * cs
      = A * κ * (Uv - G * w * cs) + (h * Bc) * (Real.sqrt h * (κ * Ud)) := by ring
  rw [e3]
  calc _ ≤ |A * κ * (Uv - G * w * cs)| + |(h * Bc) * (Real.sqrt h * (κ * Ud))| := abs_add_le _ _
    _ ≤ (Cp / (2 * c')) * h * (A * κ * (G * w)) + (2 * Cg * Cd * Real.sqrt (2 * cc) / cg) * h * (A * κ * (G * w)) :=
        add_le_add h1 h2
    _ = _ := by ring

section Chart

variable {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par} {Jlo Jhi : ℝ} {m : ℕ} {U V : ℝ → ℝ → ℝ}

/-- The comparison sequence of the chart at a row, in terms of the corrector row and the Weber function (`wf_eq`). -/
lemma psiHatL_row (C : BulkWeberChart F P Jlo Jhi m U V) {μ : Par} (hμ : μ ∈ P) {X : ℝ} (hX : X ∈ Icc Jlo Jhi) {N : ℕ}
    (hN : C.N0 ≤ N) {k : ℤ} (hk : k ∈ Finset.Icc (0 : ℤ) (C.chain μ X N).NR) :
    C.psiHatL μ X N k =
      (C.chain μ X N).AA 1 (uNode (F.step N) k) (F.step N) *
          (kappaBal (-((k : ℝ) + 1 / 2)) * U (-((k : ℝ) + 1 / 2)) (C.Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N)))
        + (F.step N * (C.chain μ X N).BB 1 (uNode (F.step N) k) (F.step N)) *
          (Real.sqrt (F.step N) * (kappaBal (-((k : ℝ) + 1 / 2)) *
            deriv (U (-((k : ℝ) + 1 / 2))) (C.Y μ X (uNode (F.step N) k) / Real.sqrt (F.step N)))) := by
  have hk' : k ∈ Finset.Icc (0 : ℤ) ((C.chain μ X N).NR + 1) := by
    rw [Finset.mem_Icc] at hk ⊢; omega
  have hw := (C.wf_eq μ hμ X hX N hN k hk').1
  have e : C.psiHatL μ X N k = (C.chain μ X N).phi (F.step N) 0 1 k := psiHat_one_eq _ _ _
  rw [e]
  unfold LadderData.phi ladderSeq
  have e2 : ((k : ℝ) + 1 / 2) * F.step N = uNode (F.step N) k := rfl
  rw [e2, dot, hw]
  simp [vrow, ut]

/-- On a row of the oscillatory overlap, with `u = (n + 1/2) h`, `Y` the Weber coordinate: `|t| <= 1 - eps0` for `t = Y/(2 sqrt u)` (from `turn_eq`, `Hz_lb`, `overlap_in_well`). -/
lemma overlap_t_bound (C : BulkWeberChart F P Jlo Jhi m U V) {μ : Par} (hμ : μ ∈ P) {X : ℝ} (hX : X ∈ Icc Jlo Jhi) {u : ℝ}
    (hu1 : C.c' ≤ u) (hu2 : u ≤ C.c) :
    (Real.sqrt u ≠ 0) ∧ (C.Y μ X u / (2 * Real.sqrt u)) ^ 2 ≤ 1 - C.σ * C.cH / (4 * C.c) := by
  obtain ⟨hc'pos, hc'c, hσ, hcσ, hcH, -, -, -, -, -⟩ := C.consts_pos
  have hupos : 0 < u := lt_of_lt_of_le hc'pos hu1
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hupos
  refine ⟨hsu.ne', ?_⟩
  have hcpos : 0 < C.c := lt_trans hc'pos hc'c
  have hmem : u ∈ Icc 0 (C.c + C.σ) := ⟨hupos.le, by linarith⟩
  have h1 := C.turn_eq μ hμ X hX u hmem
  have h2 := C.Hz_lb μ hμ X hX u hmem
  obtain ⟨hw1, -⟩ := C.overlap_in_well μ hμ X hX
  have h3 : C.σ ≤ u - F.uMinus μ X := by linarith
  have h4 : C.σ * C.cH ≤ (u - F.uMinus μ X) * C.Hz μ X u :=
    mul_le_mul h3 h2 hcH.le (by linarith)
  have h5 : C.Y μ X u ^ 2 ≤ 4 * u - C.σ * C.cH := by linarith
  rw [div_pow, mul_pow, Real.sq_sqrt hupos.le]
  have hc4 : C.σ * C.cH / (4 * C.c) ≤ C.σ * C.cH / (4 * u) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  calc C.Y μ X u ^ 2 / (2 ^ 2 * u) ≤ (4 * u - C.σ * C.cH) / (2 ^ 2 * u) :=
        div_le_div_of_nonneg_right h5 (by positivity)
    _ = 1 - C.σ * C.cH / (4 * u) := by field_simp; ring
    _ ≤ 1 - C.σ * C.cH / (4 * C.c) := by linarith

/-- `Theta_L(u) = u (arccos t - t sqrt(1-t^2))`, `t = Y/(2 sqrt u)`: `matchO` and the calculus identity `integral_sqrt_sub_sq`. -/
lemma thetaL_eq (C : BulkWeberChart F P Jlo Jhi m U V) {μ : Par} (hμ : μ ∈ P) {X : ℝ} (hX : X ∈ Icc Jlo Jhi) {u : ℝ}
    (hu1 : F.uMinus μ X ≤ u) (hu2 : u ≤ C.c) (hupos : 0 < u) (ht : |C.Y μ X u / (2 * Real.sqrt u)| ≤ 1) :
    thetaL F.L (F.G 0 μ) (F.B 0 μ) X u =
      u * (Real.arccos (C.Y μ X u / (2 * Real.sqrt u))
        - C.Y μ X u / (2 * Real.sqrt u) * Real.sqrt (1 - (C.Y μ X u / (2 * Real.sqrt u)) ^ 2)) := by
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hupos
  rw [← C.matchO μ hμ X hX u ⟨hu1, hu2⟩]
  have := integral_sqrt_sub_sq hupos (abs_le.mp ht).1 (abs_le.mp ht).2
  have e : 2 * Real.sqrt u * (C.Y μ X u / (2 * Real.sqrt u)) = C.Y μ X u := by field_simp
  rw [e] at this
  exact this

/-- **`lem:smo-bulkphase` (1), the left bulk comparison sequence has phase `Theta_L/h - pi/4`.**  There are `c1 > 0`, `C1 >= 0`, `h0 > 0` such that for every `mu in P`, `X` in the energy range, `N >= N0` with `h = F.step N <= h0`
and every row `0 <= n <= N_R` of the oscillatory overlap (`c' <= u_n`; automatically `u_n <= c`) there is an amplitude `rho >= c1 h^{1/4}` with
`|psi-hat^L_n - rho cos(Theta_L(u_n)/h - pi/4)| <= C1 h rho`.  The amplitude is `rho = A^{[m]}(u_n) kappa_bal 2 g(mu) (1 - t^2)^{-1/4}` (`mu^2 = 2n+1`, `t = Y/(2 sqrt u_n)`).
Inputs: `phase_pack` (DLMF 12.10.18 only through `phase_osc`), `corr_lead`, `turn_eq`/`Hz_lb`/`overlap_in_well`, `matchO`, `wf_eq`, `M_def`/`M_osc`. -/
theorem bulk_phase_left (C : BulkWeberChart F P Jlo Jhi m U V) {cPC CPC : ℝ} (PC : ParabolicCylinderFacts U V cPC CPC) :
    ∃ c1 C1 h0 : ℝ, 0 < c1 ∧ 0 ≤ C1 ∧ 0 < h0 ∧ ∀ μ ∈ P, ∀ X ∈ Icc Jlo Jhi, ∀ N : ℕ, C.N0 ≤ N → F.step N ≤ h0 →
      ∀ n : ℤ, 0 ≤ n → n ≤ (C.chain μ X N).NR → C.c' ≤ uNode (F.step N) n →
      ∃ ρ : ℝ, c1 * F.step N ^ ((1 : ℝ) / 4) ≤ ρ ∧
        |C.psiHatL μ X N n - ρ * Real.cos (thetaL F.L (F.G 0 μ) (F.B 0 μ) X (uNode (F.step N) n) / F.step N - Real.pi / 4)|
          ≤ C1 * F.step N * ρ := by
  obtain ⟨hc'pos, hc'c, hσ, hcσ, hcH, hcM, hcMCM, -, -, -⟩ := C.consts_pos
  have hcpos : 0 < C.c := lt_trans hc'pos hc'c
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = C.σ * C.cH / (4 * C.c) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨ε0, hε0⟩ : ∃ ε0 : ℝ, ε0 = min (δ / 2) (1 / 2) := ⟨_, rfl⟩
  have hε0pos : 0 < ε0 := by rw [hε0]; exact lt_min (by positivity) (by norm_num)
  have hε0lt : ε0 < 1 := by rw [hε0]; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hε0δ : ε0 ≤ δ / 2 := by rw [hε0]; exact min_le_left _ _
  obtain ⟨Cp, Cd, Cm, μ1, g, hCp, hCd, hCm, hμ1, hg, hpack⟩ := phase_pack PC hε0pos hε0lt
  obtain ⟨cg, Cg0, hcg, g0, hcorr⟩ := C.corr_lead
  obtain ⟨Cg, hCgdef⟩ : ∃ Cg : ℝ, Cg = max Cg0 0 := ⟨_, rfl⟩
  have hCg : 0 ≤ Cg := by rw [hCgdef]; exact le_max_right _ _
  have hCg0 : Cg0 ≤ Cg := by rw [hCgdef]; exact le_max_left _ _
  obtain ⟨C1, hC1⟩ : ∃ C1 : ℝ, C1 = Cp / (2 * C.c') + 2 * Cg * Cd * Real.sqrt (2 * C.c) / cg := ⟨_, rfl⟩
  have hC1nn : 0 ≤ C1 := by rw [hC1]; positivity
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℝ, c1 = cg / 2 * C.cM / (Cm + 1) := ⟨_, rfl⟩
  have hc1pos : 0 < c1 := by rw [hc1]; positivity
  have hμ1pos : 0 < μ1 := by linarith
  obtain ⟨h0, hh0⟩ : ∃ h0 : ℝ, h0 = min (min 1 (cg / (2 * (Cg + 1)))) (2 * C.c' / μ1 ^ 2) := ⟨_, rfl⟩
  have hh0pos : 0 < h0 := by rw [hh0]; exact lt_min (lt_min one_pos (by positivity)) (by positivity)
  refine ⟨c1, C1, h0, hc1pos, hC1nn, hh0pos, ?_⟩
  intro μ hμ X hX N hN hstep n hn0 hnNR hov
  -- chart facts at the row
  have hnm : n ∈ Finset.Icc (0 : ℤ) (C.chain μ X N).NR := Finset.mem_Icc.mpr ⟨hn0, hnNR⟩
  obtain ⟨-, -, -, hNRc, -⟩ := C.shape μ hμ X hX N hN
  have hhpos : 0 < F.step N := FormalResearch.JB.stepSize_pos F.L_pos N
  have hu2 : uNode (F.step N) n ≤ C.c := (uNode_le_of_le hhpos.le hnNR).trans hNRc
  have hrow := psiHatL_row C hμ hX hN hnm
  have hcorr' := hcorr μ hμ X hX N hN n hnm
  have hMdef := C.M_def μ hμ X hX N hN n hnm
  have hMosc := (C.M_osc μ hμ X hX N hN n hnm hov).1
  obtain ⟨hw1, -⟩ := C.overlap_in_well μ hμ X hX
  have hth := thetaL_eq C hμ hX (u := uNode (F.step N) n) (by linarith) hu2 (lt_of_lt_of_le hc'pos hov)
  obtain ⟨hsu_ne, ht2⟩ := overlap_t_bound C hμ hX hov hu2
  -- abstract the numbers
  generalize hhdef : F.step N = h at *
  generalize hudef : uNode h n = u at *
  generalize hYdef : C.Y μ X u = Y at *
  generalize hAdef : (C.chain μ X N).AA 1 u h = A at *
  generalize hBdef : (C.chain μ X N).BB 1 u h = Bc at *
  generalize hΘ : thetaL F.L (F.G 0 μ) (F.B 0 μ) X u = Θ at *
  generalize hMn : (C.chain μ X N).M n = Mn at *
  have hhmin := hstep
  rw [hh0] at hhmin
  have hh1 : h ≤ 1 := hhmin.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hhA : h ≤ cg / (2 * (Cg + 1)) := hhmin.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hhB : h ≤ 2 * C.c' / μ1 ^ 2 := hhmin.trans (min_le_right _ _)
  have hupos : 0 < u := lt_of_lt_of_le hc'pos hov
  have hn12 : 0 < (n : ℝ) + 1 / 2 := by
    have : (0 : ℝ) ≤ n := by exact_mod_cast hn0
    linarith
  have hu_eq : u = ((n : ℝ) + 1 / 2) * h := by rw [← hudef]; rfl
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = Y / (2 * Real.sqrt u) := ⟨_, rfl⟩
  rw [← htdef] at ht2 hth
  have ht2' : t ^ 2 ≤ 1 - δ := by rw [hδ]; exact ht2
  have htabs : |t| ≤ 1 - ε0 := by
    have hsq : (1 - ε0) ^ 2 = 1 - 2 * ε0 + ε0 ^ 2 := by ring
    refine abs_le_of_sq_le_sq ?_ (by linarith only [hε0lt])
    rw [hsq]
    linarith only [ht2', hε0δ, sq_nonneg ε0]
  have ht1 : |t| ≤ 1 := by linarith only [htabs, hε0pos]
  have ht1sq : t ^ 2 < 1 := by linarith only [ht2', hδpos]
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Real.sqrt ((n : ℝ) + 1 / 2) := ⟨_, rfl⟩
  have hqpos : 0 < q := by rw [hq]; exact Real.sqrt_pos.mpr hn12
  have hq2 : q ^ 2 = (n : ℝ) + 1 / 2 := by rw [hq]; exact Real.sq_sqrt hn12.le
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt h := ⟨_, rfl⟩
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hhpos
  have hs2 : s ^ 2 = h := by rw [hs]; exact Real.sq_sqrt hhpos.le
  have hsqu : Real.sqrt u = q * s := by
    rw [hu_eq, ← hq2, ← hs2, ← mul_pow, Real.sqrt_sq (by positivity)]
  obtain ⟨μv, hμv⟩ : ∃ μv : ℝ, μv = Real.sqrt 2 * q := ⟨_, rfl⟩
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq2pos : 0 < Real.sqrt 2 := by positivity
  have hμv2 : μv ^ 2 = 2 * ((n : ℝ) + 1 / 2) := by rw [hμv, mul_pow, hsq2, hq2]
  have hμvpos : 0 < μv := by rw [hμv]; positivity
  have hμh : μv ^ 2 * h = 2 * u := by rw [hμv2, hu_eq]; ring
  have hμge : μ1 ≤ μv := by
    have h2 : h * μ1 ^ 2 ≤ 2 * C.c' := (le_div_iff₀ (by positivity : (0 : ℝ) < μ1 ^ 2)).mp hhB
    have h4 : μ1 ^ 2 * h ≤ μv ^ 2 * h := by
      rw [hμh]
      linarith only [h2, hov]
    have h5 : μ1 ^ 2 ≤ μv ^ 2 := le_of_mul_le_mul_right h4 hhpos
    exact (pow_le_pow_iff_left₀ hμ1pos.le hμvpos.le (by norm_num)).mp h5
  have ha_eq : -(μv ^ 2) / 2 = -((n : ℝ) + 1 / 2) := by rw [hμv2]; ring
  have hZ_eq : μv * t * Real.sqrt 2 = Y / Real.sqrt h := by
    rw [htdef, hsqu, hμv, ← hs]
    field_simp
    linear_combination Y * hsq2
  have hμvL : ∃ k : ℕ, μv ^ 2 = 2 * k + 1 :=
    ⟨n.toNat, by rw [hμv2]; have : ((n.toNat : ℕ) : ℝ) = n := by exact_mod_cast Int.toNat_of_nonneg hn0
                 rw [this]; ring⟩
  obtain ⟨hval, hder, hMb⟩ := hpack μv hμge hμvL t htabs
  rw [ha_eq, hZ_eq] at hval hder hMb
  clear hpack hcorr
  have hμinv : μv ^ 2 = 2 * u / h := by field_simp; linarith [hμh]
  have hphase : μv ^ 2 * ((Real.arccos t - t * Real.sqrt (1 - t ^ 2)) / 2) - Real.pi / 4 = Θ / h - Real.pi / 4 := by
    rw [hth ht1, hμinv]
    field_simp
  rw [hphase] at hval
  -- the amplitude
  have ha0 : -((n : ℝ) + 1 / 2) ≤ 0 := by linarith
  obtain ⟨hκ, -⟩ := kappaBal_nonpos ha0
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = kappaBal (-((n : ℝ) + 1 / 2)) := ⟨_, rfl⟩
  rw [← hκdef] at hMb hrow hκ
  have h1t : 0 < 1 - t ^ 2 := by linarith
  have hr0 : 0 < (1 - t ^ 2) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos h1t _
  have hr1 : (1 - t ^ 2) ^ ((1 : ℝ) / 4) ≤ 1 :=
    Real.rpow_le_one h1t.le (by have := sq_nonneg t; linarith only [this]) (by norm_num)
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = ((1 - t ^ 2) ^ ((1 : ℝ) / 4))⁻¹ := ⟨_, rfl⟩
  have hw1 : 1 ≤ w := by rw [hwdef]; exact one_le_inv_iff₀.mpr ⟨hr0, hr1⟩
  have hgp := hg μv
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = 2 * g μv := ⟨_, rfl⟩
  have hGpos : 0 < G := by rw [hG]; positivity
  have hampw : 2 * g μv / (1 - t ^ 2) ^ ((1 : ℝ) / 4) = G * w := by rw [hG, hwdef, div_eq_mul_inv]
  rw [hampw] at hval
  rw [← hG] at hder hMb
  -- corrector row
  obtain ⟨hg0, hAg, hBg⟩ := hcorr'
  have hCgh : Cg0 * h ^ 2 ≤ cg / 2 := by
    have h1 : Cg0 * h ^ 2 ≤ Cg * h := by
      calc Cg0 * h ^ 2 ≤ Cg * h ^ 2 := mul_le_mul_of_nonneg_right hCg0 (sq_nonneg _)
        _ ≤ Cg * h := by
          have : h ^ 2 ≤ h := pow_le_of_le_one hhpos.le hh1 (by norm_num)
          exact mul_le_mul_of_nonneg_left this hCg
    have h2 : Cg * h ≤ cg / 2 := by
      have := mul_le_mul_of_nonneg_left hhA hCg
      calc Cg * h ≤ Cg * (cg / (2 * (Cg + 1))) := this
        _ = cg / 2 * (Cg / (Cg + 1)) := by field_simp
        _ ≤ cg / 2 * 1 := mul_le_mul_of_nonneg_left (by rw [div_le_one (by linarith only [hCg])]; linarith only [hCg]) (by positivity)
        _ = cg / 2 := by ring
    linarith only [h1, h2]
  have hAcg : cg / 2 ≤ A := by
    have := (abs_le.mp hAg).1
    linarith only [this, hg0, hCgh]
  have hBc : |h * Bc| ≤ Cg * h := by
    rw [abs_mul, abs_of_pos hhpos]
    calc h * |Bc| ≤ h * Cg := mul_le_mul_of_nonneg_left (hBg.trans hCg0) hhpos.le
      _ = Cg * h := by ring
  -- error terms
  have hμinv2 : Cp * μv⁻¹ ^ 2 ≤ Cp * (h / (2 * C.c')) := by
    have : μv⁻¹ ^ 2 = h / (2 * u) := by rw [inv_pow, hμinv]; field_simp
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ hCp
    exact div_le_div_of_nonneg_left hhpos.le (by positivity) (by linarith only [hov])
  have hU' : |U (-((n : ℝ) + 1 / 2)) (Y / Real.sqrt h) - G * w * Real.cos (Θ / h - Real.pi / 4)|
      ≤ Cp * (h / (2 * C.c')) * (G * w) := by
    refine hval.trans ?_
    exact mul_le_mul_of_nonneg_right hμinv2 (by positivity)
  have hqh : μv * Real.sqrt h ≤ Real.sqrt (2 * C.c) := by
    rw [← hs]
    apply Real.le_sqrt_of_sq_le
    calc (μv * s) ^ 2 = μv ^ 2 * h := by rw [mul_pow, hs2]
      _ = 2 * u := hμh
      _ ≤ 2 * C.c := by linarith only [hu2]
  have hmain := phase_arith (A := A) (κ := κ) (G := G) (w := w)
    (cs := Real.cos (Θ / h - Real.pi / 4)) (Uv := U (-((n : ℝ) + 1 / 2)) (Y / Real.sqrt h))
    (Ud := deriv (U (-((n : ℝ) + 1 / 2))) (Y / Real.sqrt h)) (h := h) (q := μv) (Bc := Bc) (cg := cg) (Cg := Cg)
    (Cp := Cp) (Cd := Cd) (c' := C.c') (cc := C.c) hAcg hcg hκ hGpos hw1 hhpos hBc hCg hCp hCd hμvpos hU' hc'pos hder hqh
  refine ⟨A * κ * (G * w), ?_, ?_⟩
  · -- the lower bound `rho >= c1 h^{1/4}`
    have h1 : C.cM * h ^ ((1 : ℝ) / 4) ≤ (Cm + 1) * (κ * G) := by
      have h2 : Mn ≤ Cm * κ * G := by rw [hMdef]; exact hMb
      have h3 : Cm * κ * G ≤ (Cm + 1) * (κ * G) := by nlinarith only [mul_pos hκ hGpos]
      linarith only [hMosc, h2, h3]
    have h4 : cg / 2 * (κ * G) ≤ A * κ * (G * w) := by
      have h5 : κ * G ≤ κ * G * w := le_mul_of_one_le_right (by positivity) hw1
      calc cg / 2 * (κ * G) ≤ A * (κ * G) := mul_le_mul_of_nonneg_right hAcg (by positivity)
        _ ≤ A * (κ * G * w) := mul_le_mul_of_nonneg_left h5 (by linarith only [hAcg, hcg])
        _ = A * κ * (G * w) := by ring
    rw [hc1, div_mul_eq_mul_div, div_le_iff₀ (by linarith only [hCm])]
    have hcg2 : 0 ≤ cg / 2 := by positivity
    calc cg / 2 * C.cM * h ^ ((1 : ℝ) / 4) = cg / 2 * (C.cM * h ^ ((1 : ℝ) / 4)) := by ring
      _ ≤ cg / 2 * ((Cm + 1) * (κ * G)) := mul_le_mul_of_nonneg_left h1 hcg2
      _ = (Cm + 1) * (cg / 2 * (κ * G)) := by ring
      _ ≤ (Cm + 1) * (A * κ * (G * w)) := mul_le_mul_of_nonneg_left h4 (by linarith only [hCm])
      _ = A * κ * (G * w) * (Cm + 1) := by ring
  · rw [hrow]
    have e : C1 = Cp / (2 * C.c') + 2 * Cg * Cd * Real.sqrt (2 * C.c) / cg := hC1
    rw [e]
    exact hmain

end Chart

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.bulk_phase_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.bulk_phase_left

end FormalResearch.JacobiEigenvectors.TheoremA
