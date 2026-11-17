module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.Sequences

/-!
# Montel's theorem

Generic complex analysis (no application content).  **Proved.**

Statement formalised (Montel 1907; Conway, *Functions of One Complex Variable*, VII.2.9; Stein–Shakarchi, Ch. 8 Thm 1.2):
if `U ⊆ ℂ` is open and `F n` (`n : ℕ`) are holomorphic on `U` and locally uniformly bounded (`LocallyBounded F U`: bounded on
every compact `K ⊆ U`, uniformly in `n`), then a subsequence converges locally uniformly on `U` to a function `f` that is
holomorphic on `U` (`FormalResearch.Montel.montel`).  Equivalently the family is *normal*.

Proof.  Cauchy's estimate gives `|F n w| ≤ M` on `closedBall x (2ρ) ⊆ U` implies `‖(F n)'‖ ≤ M/ρ` on `ball x ρ`, hence a
uniform Lipschitz bound near every point (`lipschitz_near`) and so equicontinuity of the family as continuous functions on the
open subspace `↥U` (`equicontinuous`).  Mathlib's Arzelà–Ascoli theorem (`ArzelaAscoli.isCompact_closure_of_isClosedEmbedding`)
makes the closure of the family compact in `C(↥U, ℂ)` with the compact-open topology; this space is first countable (its
uniformity of compact convergence is countably generated since `↥U` is locally compact and σ-compact), so compact sets are
sequentially compact.  Convergence in the compact-open topology is locally uniform convergence; holomorphy of the limit is
`TendstoLocallyUniformlyOn.differentiableOn` (Mathlib).

**Not formalised.** Montel's theorem for the *Fatou* / three-omitted-values form (a family omitting two values), the
version for meromorphic functions with the spherical metric, and quantitative equicontinuity moduli.  Mathlib has only the
abstract notion `MontelSpace` (Heine–Borel topological vector spaces), not the holomorphic theorem.
-/

@[expose] public section

open Complex Filter Topology Metric Set

namespace FormalResearch.Montel

/-- The family `F` (indexed by `ι`) is locally uniformly bounded on `U`: bounded on each compact subset, uniformly in the
index. -/
def LocallyBounded {ι : Type*} (F : ι → ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ K ⊆ U, IsCompact K → ∃ M : ℝ, ∀ i, ∀ z ∈ K, ‖F i z‖ ≤ M

variable {ι : Type*} {F : ι → ℂ → ℂ} {U : Set ℂ}

/-- **Cauchy estimate ⇒ local uniform Lipschitz bound.**  -/
lemma lipschitz_near (hU : IsOpen U) (hd : ∀ i, DifferentiableOn ℂ (F i) U) (hb : LocallyBounded F U)
    {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    ∃ ρ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ∀ y ∈ ball x₀ ρ, ‖F i y - F i x₀‖ ≤ C * ‖y - x₀‖ := by
  obtain ⟨ρ', hρ', hsub⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  set ρ := ρ' / 4 with hρdef
  have hρ : 0 < ρ := by positivity
  have hKsub : closedBall x₀ (2 * ρ) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hsub
  obtain ⟨M, hM⟩ := hb _ hKsub (isCompact_closedBall _ _)
  refine ⟨ρ, hρ, max M 0 / ρ, by positivity, fun i y hy => ?_⟩
  have hdi : ∀ w ∈ ball x₀ ρ, ‖deriv (F i) w‖ ≤ max M 0 / ρ := by
    intro w hw
    have hcl : closedBall w ρ ⊆ closedBall x₀ (2 * ρ) := by
      intro z hz
      rw [mem_closedBall] at hz ⊢
      have := mem_ball.mp hw
      calc dist z x₀ ≤ dist z w + dist w x₀ := dist_triangle _ _ _
        _ ≤ 2 * ρ := by linarith
    have hdc : DiffContOnCl ℂ (F i) (ball w ρ) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball w hρ.ne']
      exact (hd i).mono (hcl.trans hKsub)
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hdc fun z hz =>
      (hM i z (hcl (sphere_subset_closedBall hz))).trans (le_max_left _ _)
  have hdiff : ∀ w ∈ ball x₀ ρ, DifferentiableAt ℂ (F i) w := fun w hw =>
    (hd i).differentiableAt (hU.mem_nhds (hsub (ball_subset_ball (by linarith) hw)))
  exact Convex.norm_image_sub_le_of_norm_deriv_le hdiff hdi (convex_ball x₀ ρ) (mem_ball_self hρ) hy


/-- The family as continuous functions on the open subspace `↥U`. -/
noncomputable def toCont (hd : ∀ i, DifferentiableOn ℂ (F i) U) (i : ι) : C(U, ℂ) :=
  ⟨fun z => F i z, (hd i).continuousOn.comp_continuous continuous_subtype_val fun z => z.2⟩

/-- **Equicontinuity** of a locally uniformly bounded holomorphic family, on `↥U`. -/
lemma equicontinuous (hU : IsOpen U) (hd : ∀ i, DifferentiableOn ℂ (F i) U) (hb : LocallyBounded F U) :
    Equicontinuous (fun i : ι => ⇑(toCont hd i)) := by
  intro x₀
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨ρ, hρ, C, hC, hlip⟩ := lipschitz_near hU hd hb x₀.2
  refine ⟨min ρ (ε / (C + 1)), lt_min hρ (by positivity), fun x hx i => ?_⟩
  have hx' : dist (x : ℂ) (x₀ : ℂ) < min ρ (ε / (C + 1)) := by rwa [← Subtype.dist_eq]
  have hxρ : dist (x : ℂ) x₀ < ρ := lt_of_lt_of_le hx' (min_le_left _ _)
  have hxε : dist (x : ℂ) x₀ < ε / (C + 1) := lt_of_lt_of_le hx' (min_le_right _ _)
  have h1 := hlip i x (mem_ball.mpr hxρ)
  rw [← dist_eq_norm, ← dist_eq_norm] at h1
  show dist (F i x₀) (F i x) < ε
  rw [dist_comm]
  have h2 : C * dist (x : ℂ) x₀ < ε := by
    have h3 : dist (x : ℂ) x₀ * (C + 1) < ε := by
      rwa [lt_div_iff₀ (by positivity)] at hxε
    nlinarith [dist_nonneg (x := (x : ℂ)) (y := x₀)]
  exact lt_of_le_of_lt h1 h2

end FormalResearch.Montel
