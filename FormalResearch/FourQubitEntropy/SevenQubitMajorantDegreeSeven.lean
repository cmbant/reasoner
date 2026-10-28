import Mathlib
import FormalResearch.FourQubitEntropy.SevenQubitMajorantDegreeConverse
import FormalResearch.FourQubitEntropy.SevenQubitIcoEntropy

/-!
# Seven-qubit application of the sharp-majorant degree proposition

The seven-qubit half of `prop:seven-entropy-majorant-degree`
(`ResearchNotes/QI/seven_qubit_entanglement/seven_qubit_entropy_joint.tex`): at the entropy
maximiser `ψ_{x_*}` of the icosahedral family a *single* scalar majorant of `-t log t` that is
sharp at every cut eigenvalue needs degree `≥ 7` (exactly `7`), because the cut spectra carry four
distinct nodes `u+x < 4u < 3u+x < 8u`.

Proved here: the node arithmetic (`1/32 < x < 37/524` gives four distinct nodes in `(0,1)`), the
bound `x_* > 1/32` (`E3d (1/32) > 0` plus antitonicity of `E3d` from `SevenQubitIcoEntropy`;
`x_* < 37/524` is `E3_unique_max`), and degree exactly `7` via `majorant_degree_isLeast` and its
base-2 variant.  Not proved here: that the cut spectra of `ψ_x` are these four values (that is
`SevenQubitIcoSpectrum`, taken as the definition of `E3`), and the paper's contrasting statement
that the joint degree-five majorant avoids this (`SevenQubitJointMajorant.lean`).
-/

open Set Polynomial

namespace FormalResearch.FourQubitEntropy

namespace MajorantDegree

open SevenQubitIco

/-- The four distinct cut eigenvalues `u+x < 4u < 3u+x < 8u` of the icosahedral family, for
`1/32 < x < 37/524` (equivalently `1 < x/u < 37/15`). -/
noncomputable def cutNodes (x : ℝ) : Finset ℝ := {4 * u x, 3 * u x + x, u x + x, 8 * u x}

theorem cutNodes_pos_lt {x : ℝ} (h1 : 1 / 32 < x) (h2 : x < 37 / 524) :
    0 < u x + x ∧ u x + x < 4 * u x ∧ 4 * u x < 3 * u x + x ∧ 3 * u x + x < 8 * u x ∧
      8 * u x < 1 := by
  unfold u
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem cutNodes_card {x : ℝ} (h1 : 1 / 32 < x) (h2 : x < 37 / 524) : (cutNodes x).card = 4 := by
  obtain ⟨a, b, c, d, e⟩ := cutNodes_pos_lt h1 h2
  unfold cutNodes
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem]
  · simp
  · simp only [Finset.mem_singleton]; linarith
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; constructor <;> linarith
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem cutNodes_mem {x : ℝ} (h1 : 1 / 32 < x) (h2 : x < 37 / 524) :
    ∀ a ∈ cutNodes x, 0 < a ∧ a < 1 := by
  obtain ⟨a, b, c, d, e⟩ := cutNodes_pos_lt h1 h2
  intro y hy
  simp only [cutNodes, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl <;> constructor <;> linarith

/-- **Seven-qubit application of `prop:seven-entropy-majorant-degree` (natural log).**
Let `1/32 < x < 37/524`, i.e. `1 < x/u < 37/15` (the range of the entropy maximiser `x_*`, see
`maximiser_gt_one_thirtysecond`).  The cut spectra of `ψ_x` carry the four distinct nodes
`4u, 3u+x, u+x, 8u ∈ (0,1)`; hence a single polynomial majorant of `-t log t` touching at all of
them has degree `≥ 7`, and degree `7` is attained (`IsLeast`).  Proved from the Rolle bound and the
Hermite converse.  NOT shown here: that these are the spectra of the cuts (that is
`SevenQubitIcoSpectrum`) and the paper's remark that the *joint* degree-five majorant avoids the
obstruction (`lem:seven-joint-scalar-majorant`, `SevenQubitJointMajorant`). -/
theorem single_majorant_degree_seven {x : ℝ} (h1 : 1 / 32 < x) (h2 : x < 37 / 524) :
    IsLeast {d : ℕ | ∃ q : ℝ[X], q.natDegree = d ∧
      (∀ t ∈ Icc (0:ℝ) 1, Real.negMulLog t ≤ q.eval t) ∧
      ∀ a ∈ cutNodes x, q.eval a = Real.negMulLog a} 7 := by
  have := majorant_degree_isLeast (cutNodes x) (by rw [cutNodes_card h1 h2]; norm_num)
    (cutNodes_mem h1 h2)
  rwa [cutNodes_card h1 h2] at this

/-- The same for the base-2 entropy `-t log₂ t`, exactly as in the paper's statement. -/
theorem single_majorant_degree_seven_logb_two {x : ℝ} (h1 : 1 / 32 < x) (h2 : x < 37 / 524) :
    IsLeast {d : ℕ | ∃ q : ℝ[X], q.natDegree = d ∧
      (∀ t ∈ Icc (0:ℝ) 1, -t * Real.logb 2 t ≤ q.eval t) ∧
      ∀ a ∈ cutNodes x, q.eval a = -a * Real.logb 2 a} 7 := by
  have := majorant_degree_isLeast_logb_two (cutNodes x)
    (by rw [cutNodes_card h1 h2]; norm_num) (cutNodes_mem h1 h2)
  rwa [cutNodes_card h1 h2] at this

/-- At `x = 1/32` (where `u = x`) the family derivative is positive: `E3d (1/32) = 36 ln 2 / 35`. -/
theorem E3d_one_thirtysecond_pos : 0 < E3d (1 / 32) := by
  rw [E3d_eq_log (by norm_num) (by norm_num)]
  apply div_pos _ (by norm_num)
  apply Real.log_pos
  rw [one_lt_div (by unfold u; positivity)]
  unfold u
  norm_num

/-- **`x_* > 1/32`** (paper: `E₃'(1/32) = 4 ln 512/(35 ln 2) > 0` plus concavity).  Any
maximiser `c ∈ (0, 37/524)` of the family mean entropy `E3` on `[0, 1/2]` satisfies `1/32 < c`.
Combined with `E3_unique_max` (which supplies the maximiser and `c < 37/524`) this puts `x_*/u_*`
in `(1, 37/15)`. -/
theorem maximiser_gt_one_thirtysecond {c : ℝ} (hc0 : 0 < c) (hc1 : c < 37 / 524)
    (hmax : ∀ y ∈ Icc (0:ℝ) (1 / 2), E3 y ≤ E3 c) : 1 / 32 < c := by
  have hc2 : c < 1 / 2 := by linarith
  have hloc : IsLocalMax E3 c :=
    Filter.mem_of_superset (Icc_mem_nhds hc0 hc2) fun y hy => hmax y hy
  have hz : E3d c = 0 := hloc.hasDerivAt_eq_zero (hasDerivAt_E3 hc0.le hc2)
  by_contra hle
  push Not at hle
  have := E3d_strictAntiOn.antitoneOn ⟨hc0.le, hc2⟩ ⟨by norm_num, by norm_num⟩ hle
  linarith [E3d_one_thirtysecond_pos]

/-- **Seven-qubit entropy maximiser: degree seven.**  There is an `x_*` (the unique maximiser of
the family mean entropy) with `1/32 < x_* < 37/524`, and at it a single scalar majorant sharp at
all cut eigenvalues has minimal degree exactly `7`. -/
theorem exists_maximiser_degree_seven : ∃ c : ℝ, 1 / 32 < c ∧ c < 37 / 524 ∧
    (∀ y ∈ Icc (0:ℝ) (1 / 2), y ≠ c → E3 y < E3 c) ∧
    IsLeast {d : ℕ | ∃ q : ℝ[X], q.natDegree = d ∧
      (∀ t ∈ Icc (0:ℝ) 1, Real.negMulLog t ≤ q.eval t) ∧
      ∀ a ∈ cutNodes c, q.eval a = Real.negMulLog a} 7 := by
  obtain ⟨c, hc0, hc1, hu, -, -⟩ := E3_unique_max
  have hgt := maximiser_gt_one_thirtysecond hc0 hc1 fun y hy => by
    rcases eq_or_ne y c with rfl | h
    · exact le_rfl
    · exact (hu y hy h).le
  exact ⟨c, hgt, hc1, hu, single_majorant_degree_seven hgt hc1⟩

end MajorantDegree

end FormalResearch.FourQubitEntropy
