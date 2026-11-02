import FormalResearch.FourQubitEntropy.GOProbe.Check
import FormalResearch.FourQubitEntropy.GOGlue.DataCheck
import FormalResearch.FourQubitEntropy.GOGlue.ConsCheck
import FormalResearch.FourQubitEntropy.GOGlue.OrbitMaps
import FormalResearch.FourQubitEntropy.GOGlue.FrameCert
import FormalResearch.FourQubitEntropy.PaperEFidelityFloor

/-!
# `thm:fqe-global-overlap` for every unit four-qubit state (Paper E, `Q ≥ 1 - Φ`)

This module joins the two halves of the formalisation:

* the **reduction** (`PaperEGoSlice*`, `GOGlue/FrameCert.lean`): every unit state has a closest-point
  frame in the 19-coordinate normal slice, the positive constraints hold there, and
  `GOFrameCertificate` (`(Q - n²e)/36 ≥ 0` at frames) gives `Q ≥ 1 - Φ`;
* the **certificate** (`GOProbe/*`, generated data `GOData/*`): `go_target_nonneg`, from the single
  `native_decide` `GOProbe.check_all`.

Glue proved here: `lit_ev` (the generated target polynomial is `(mapDen·grid)(sliceTarget - R_sq - R_ax)`,
`identCheck_true`, `native_decide`), `cons_psd` (the 64 generated constraint matrices are positive
semidefinite at every constraint-satisfying point, `consCheck_true`, `native_decide`), and `frame_orbit`
(the 48 coordinate maps preserve closest-point frames, `GOGlue/OrbitMaps.lean`).

**Axioms.**  The three `native_decide` steps (`GOProbe.check_all`, `identCheck_true`, `consCheck_true`) are
the only uses of `Lean.ofReduceBool`; each is a decidable check of the generated data by ordinary
computable list functions.  The headline theorems depend on
`[propext, Classical.choice, Quot.sound, Lean.ofReduceBool]` (see the `#print axioms` audits below).

This module imports the generated data (not committed) and is **not** part of the aggregate
`FormalResearch` build; see `THEOREM_MAP.md` for the commands.  Claim class: proved
(modulo the three data checks).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Finset
open scoped Matrix

namespace FormalResearch.FourQubitEntropy.GO
open CO OD

theorem perms_sub : ∀ g ∈ GOProbe.perms, g ∈ permLists := by decide +kernel

theorem flips_sub : ∀ f ∈ GOProbe.flips, f ∈ flipLists := by decide +kernel

/-- **The certificate at closest-point frames.** -/
theorem go_frame_certificate : GOFrameCertificate := by
  intro v h hf
  set x : ℕ → ℝ := fun i => if hi : i < 19 then v ⟨i, hi⟩ else 0 with hx
  have hrx : restr x = v := funext fun i => by simp [restr, hx, i.2]
  have hfx : IsFrame (sState (restr x)) h := by rw [hrx]; exact hf
  have hc0 : SliceConstraints (restr x) := frame_constraints frameHess hfx
  have hpsd : ∀ g ∈ GOProbe.perms, ∀ f ∈ GOProbe.flips, ∀ c < GOProbe.cons.length,
      GOProbe.Psd (GOProbe.act g (GOProbe.flipPt f x)) (GOProbe.cons.getD c []) := by
    intro g hg f hf' c hc
    have hfr := frame_orbit hfx (perms_sub g hg) (flips_sub f hf')
    exact cons_psd consCheck_true _ (frame_constraints frameHess hfr) c hc
  have hh : 0 ≤ GOProbe.h0 x := by rw [h0_eq]; exact hc0.h0_nonneg
  have hL : ∀ w : ℕ → ℝ, 0 ≤ ∑ i ∈ range 3, ∑ j ∈ range 3, w i * GOProbe.Lstar x i j * w j := by
    intro w
    have := hc0.lower (-1) (-1) (-1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (fun i => w i)
    simp only [Finset.sum_range]
    simpa [Lstar_eq] using this
  have h1 := GOProbe.go_target_nonneg x hpsd hh hL
  have h2 := lit_ev identCheck_true x
  have hK : (litScale : ℝ) = GOProbe.goK := by
    unfold litScale GOProbe.goK; push_cast; rfl
  have hKpos : 0 < GOProbe.goK := by
    unfold GOProbe.goK
    have : (0 : ℝ) < GOProbe.mapDen := by exact_mod_cast (show 0 < GOProbe.mapDen by decide)
    have : (0 : ℝ) < GOProbe.gridC := by exact_mod_cast (show 0 < GOProbe.gridC by decide)
    positivity
  rw [h2, hK, mul_div_cancel_left₀ _ hKpos.ne'] at h1
  rw [← hrx]
  linarith

/-- **`thm:fqe-global-overlap`**: `Q ≥ 1 - Φ` for every unit four-qubit state. -/
theorem globalOverlap_all : ∀ ψ : Psi, normSqPsi ψ = 1 → GlobalOverlap ψ :=
  globalOverlap_of_frame_cert go_frame_certificate

/-! ### The downstream estimates, unconditional -/

theorem orbitDist_sq_le_Q_all {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    (6 + Real.sqrt 6) / 12 * orbitDist ψ ^ 2 ≤ sexticQ ψ ∧
      orbitDist ψ ^ 2 ≤ 12 / (6 + Real.sqrt 6) * sexticQ ψ ∧ 7 / 10 < (6 + Real.sqrt 6) / 12 :=
  orbitDist_sq_le_Q_of_overlap hψ (globalOverlap_all ψ hψ)

/-- **`thm:fqe-orbit-stability`, global part, unconditional.** -/
theorem entropy_gap_orbit_stability_dist_all {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    orbitDist ψ ^ 2 ≤ 12 / (6 + Real.sqrt 6) * sexticQ ψ ∧
    (Real.log 3 - 1) / (2 * Real.log 2) * ((6 + Real.sqrt 6) / 12 * orbitDist ψ ^ 2)
        ≤ 1 + Real.log 3 / (2 * Real.log 2) - meanEntropy ψ ∧
      1 / 20 < (Real.log 3 - 1) / (2 * Real.log 2) * ((6 + Real.sqrt 6) / 12) ∧
      1 / 20 * orbitDist ψ ^ 2 ≤ 1 + Real.log 3 / (2 * Real.log 2) - meanEntropy ψ :=
  entropy_gap_orbit_stability_dist_of_overlap hψ (globalOverlap_all ψ hψ)

theorem orbitDist_sq_le_Q_tau_all {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    (6 + Real.sqrt (6 * (1 + Real.sqrt (Complex.normSq (spinFlipForm ψ))))) / 12 * orbitDist ψ ^ 2
      ≤ sexticQ ψ :=
  orbitDist_sq_le_Q_tau hψ (globalOverlap_all ψ hψ)

theorem entropy_gap_dist_tau_all {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    (Real.log 3 - 1) / (2 * Real.log 2) *
        ((6 + Real.sqrt (6 * (1 + Real.sqrt (Complex.normSq (spinFlipForm ψ))))) / 12 *
          orbitDist ψ ^ 2) ≤ 1 + Real.log 3 / (2 * Real.log 2) - meanEntropy ψ :=
  entropy_gap_dist_tau hψ (globalOverlap_all ψ hψ)

theorem majorant_gap_orbit_all {f : ℝ → ℝ} {a b c d : ℝ} (hM : Majorant f a b c d)
    (ha : 0 ≤ a) (hα : 0 ≤ -b - 17 * a / 12) {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    (6 + Real.sqrt 6) / 12 / 3 * min (-b - 17 * a / 12) (a / 12) * orbitDist ψ ^ 2 ≤
      meanSpec f M4 - meanSpec f ψ :=
  majorant_gap_orbit_of_overlap hM ha hα hψ (globalOverlap_all ψ hψ)

theorem tsallis_gap_orbit_all {q : ℝ} (h0 : 0 < q) (h2 : q < 2) (h1 : q ≠ 1) {ψ : Psi}
    (hψ : normSqPsi ψ = 1) :
    0 < min (-tsB q - 17 * tsA q / 12) (tsA q / 12) ∧
    (6 + Real.sqrt 6) / 12 / 3 * min (-tsB q - 17 * tsA q / 12) (tsA q / 12) *
        orbitDist ψ ^ 2 ≤ tsallisCeiling q - meanTsallis q ψ :=
  tsallis_gap_orbit_of_overlap h0 h2 h1 hψ (globalOverlap_all ψ hψ)

/-- **`thm:fqe-critical-orbit-sharp`, unconditional** (the case `Φ ≥ 1/2` from `globalOverlap_all`). -/
theorem critical_orbit_sharp_dist_all {ψ : Psi} (hψ : normSqPsi ψ = 1) (hW : blochSq ψ = 0) :
    max (1 - Phi ψ) (3 / 2 - 2 * Phi ψ) ≤ sexticQ ψ ∧
    (2 + Real.sqrt 2) / 4 * orbitDist ψ ^ 2 ≤ sexticQ ψ ∧
    (Real.log 3 - 1) / (2 * Real.log 2) *
        (max (1 - Phi ψ) (3 / 2 - 2 * Phi ψ) + 5 / 2 * Complex.normSq (spinFlipForm ψ))
      ≤ 1 + Real.log 3 / (2 * Real.log 2) - meanEntropy ψ ∧
    (Real.log 3 - 1) / (2 * Real.log 2) *
        ((2 + Real.sqrt 2) / 4 * orbitDist ψ ^ 2 + 5 / 2 * Complex.normSq (spinFlipForm ψ))
      ≤ 1 + Real.log 3 / (2 * Real.log 2) - meanEntropy ψ :=
  OD.critical_orbit_sharp_dist hψ hW (fun _ => globalOverlap_all ψ hψ)

/-! ### Axiom audit

The three `native_decide` axioms are the data checks `consCheck_true`, `identCheck_true` and
`GOProbe.check_all`. -/

/-- info: 'FormalResearch.FourQubitEntropy.GO.go_frame_certificate' depends on axioms: [propext, Classical.choice, Quot.sound, consCheck_true._native.native_decide.ax_1_1, identCheck_true._native.native_decide.ax_1_1, GOProbe.check_all._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms go_frame_certificate

/-- info: 'FormalResearch.FourQubitEntropy.GO.globalOverlap_all' depends on axioms: [propext, Classical.choice, Quot.sound, consCheck_true._native.native_decide.ax_1_1, identCheck_true._native.native_decide.ax_1_1, GOProbe.check_all._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms globalOverlap_all

/-- info: 'FormalResearch.FourQubitEntropy.GO.orbitDist_sq_le_Q_all' depends on axioms: [propext, Classical.choice, Quot.sound, consCheck_true._native.native_decide.ax_1_1, identCheck_true._native.native_decide.ax_1_1, GOProbe.check_all._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms orbitDist_sq_le_Q_all

/-- info: 'FormalResearch.FourQubitEntropy.GO.entropy_gap_orbit_stability_dist_all' depends on axioms: [propext, Classical.choice, Quot.sound, consCheck_true._native.native_decide.ax_1_1, identCheck_true._native.native_decide.ax_1_1, GOProbe.check_all._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms entropy_gap_orbit_stability_dist_all

/-- info: 'FormalResearch.FourQubitEntropy.GO.orbitDist_sq_le_Q_tau_all' depends on axioms: [propext, Classical.choice, Quot.sound, consCheck_true._native.native_decide.ax_1_1, identCheck_true._native.native_decide.ax_1_1, GOProbe.check_all._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms orbitDist_sq_le_Q_tau_all

/-- info: 'FormalResearch.FourQubitEntropy.GO.entropy_gap_dist_tau_all' depends on axioms: [propext, Classical.choice, Quot.sound, consCheck_true._native.native_decide.ax_1_1, identCheck_true._native.native_decide.ax_1_1, GOProbe.check_all._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms entropy_gap_dist_tau_all

/-- info: 'FormalResearch.FourQubitEntropy.GO.majorant_gap_orbit_all' depends on axioms: [propext, Classical.choice, Quot.sound, consCheck_true._native.native_decide.ax_1_1, identCheck_true._native.native_decide.ax_1_1, GOProbe.check_all._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms majorant_gap_orbit_all

/-- info: 'FormalResearch.FourQubitEntropy.GO.tsallis_gap_orbit_all' depends on axioms: [propext, Classical.choice, Quot.sound, consCheck_true._native.native_decide.ax_1_1, identCheck_true._native.native_decide.ax_1_1, GOProbe.check_all._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms tsallis_gap_orbit_all

/-- info: 'FormalResearch.FourQubitEntropy.GO.critical_orbit_sharp_dist_all' depends on axioms: [propext, Classical.choice, Quot.sound, consCheck_true._native.native_decide.ax_1_1, identCheck_true._native.native_decide.ax_1_1, GOProbe.check_all._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms critical_orbit_sharp_dist_all

end FormalResearch.FourQubitEntropy.GO
