module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# A Farkas-type lemma for finitely many moment constraints

Finite-dimensional separation argument behind Theorem E (`dual_spectrum.tex`, `ds:E`(a)):
if a point `a ∈ ℝⁿ` satisfies the dual inequalities
`l·a + μ C ≥ 0` for every `(l, μ)` with `μ ≥ 0` and `l·f(x) + μ ≥ 0` for all `x`, then `a` is a limit
of finite positive combinations `Σ_k c_k f(x_k)` of total weight `Σ_k c_k ≤ C`.

The proof is the separation of `a` from the closed convex set `closure K`, `K` the set of such
finite combinations (the paper separates in the closed cone of moments of measures on `[T, ∞]`).
Everything here is unconditional.
-/

@[expose] public section

open Set Filter Topology

namespace FormalResearch.ModularBootstrap.Duality

/-- The set of finite positive combinations `Σ_k c_k f(x_k)` with total weight `≤ C`. -/
def atomicCombos {ι X : Type*} [Fintype ι] (f : ι → X → ℝ) (C : ℝ) : Set (ι → ℝ) :=
  {v | ∃ (N : ℕ) (x : Fin N → X) (c : Fin N → ℝ), (∀ k, 0 ≤ c k) ∧ ∑ k, c k ≤ C ∧
    v = fun i => ∑ k, c k * f i (x k)}

lemma convex_atomicCombos {ι X : Type*} [Fintype ι] (f : ι → X → ℝ) {C : ℝ} :
    Convex ℝ (atomicCombos f C) := by
  rintro v ⟨N₁, x₁, c₁, hc₁, hs₁, rfl⟩ w ⟨N₂, x₂, c₂, hc₂, hs₂, rfl⟩ s t hs ht hst
  refine ⟨N₁ + N₂, Fin.append x₁ x₂, Fin.append (fun k => s * c₁ k) (fun k => t * c₂ k), ?_, ?_, ?_⟩
  · intro k
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · simp only [Fin.append_left]; exact mul_nonneg hs (hc₁ k)
    · simp only [Fin.append_right]; exact mul_nonneg ht (hc₂ k)
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have e : s * C + t * C = C := by rw [← add_mul, hst, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hs₁ hs, mul_le_mul_of_nonneg_left hs₂ ht]
  · ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun k _ => by ring

lemma zero_mem_atomicCombos {ι X : Type*} [Fintype ι] (f : ι → X → ℝ) {C : ℝ} (hC : 0 ≤ C) :
    (0 : ι → ℝ) ∈ atomicCombos f C :=
  ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, by simpa using hC, by ext i; simp⟩

lemma single_mem_atomicCombos {ι X : Type*} [Fintype ι] (f : ι → X → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (x : X) : (fun i => C * f i x) ∈ atomicCombos f C :=
  ⟨1, fun _ => x, fun _ => C, fun _ => hC, by simp, by ext i; simp⟩

/-- **Farkas-type lemma.** Let `f : ι → X → ℝ` (`ι` finite), `a : ι → ℝ`, `C > 0`. Suppose that for
every `l : ι → ℝ` and `μ ≥ 0` with `Σ_i l_i f_i(x) + μ ≥ 0` for all `x` one has
`Σ_i l_i a_i + μ C ≥ 0`. Then for every `ε > 0` there are points `x_k` and weights `c_k ≥ 0`,
`Σ c_k ≤ C`, with `|Σ_k c_k f_i(x_k) - a_i| < ε` for all `i`. -/
theorem farkas_approx {ι X : Type*} [Fintype ι] (f : ι → X → ℝ) (a : ι → ℝ) {C : ℝ} (hC : 0 < C)
    (H : ∀ (l : ι → ℝ) (μ : ℝ), 0 ≤ μ → (∀ x, 0 ≤ ∑ i, l i * f i x + μ) →
      0 ≤ ∑ i, l i * a i + μ * C) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (x : Fin N → X) (c : Fin N → ℝ), (∀ k, 0 ≤ c k) ∧ ∑ k, c k ≤ C ∧
      ∀ i, |∑ k, c k * f i (x k) - a i| < ε := by
  classical
  have hmem : a ∈ closure (atomicCombos f C) := by
    by_contra hna
    obtain ⟨l, u, hlu, hb⟩ := geometric_hahn_banach_point_closed
      (convex_atomicCombos f).closure isClosed_closure hna
    have hexp : ∀ v : ι → ℝ, l v = ∑ i, v i * l (Pi.single i 1) := fun v => by
      have := LinearMap.pi_apply_eq_sum_univ (l : (ι → ℝ) →ₗ[ℝ] ℝ) v
      rw [show (l : (ι → ℝ) →ₗ[ℝ] ℝ) v = l v from rfl] at this
      rw [this]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e : (fun j => if i = j then (1 : ℝ) else 0) = Pi.single i 1 := by
        funext j; simp [Pi.single_apply, eq_comm]
      simp [e]
    set li : ι → ℝ := fun i => l (Pi.single i 1) with hli
    have h0 : u < 0 := by
      have := hb 0 (subset_closure (zero_mem_atomicCombos f hC.le))
      simpa using this
    have hx : ∀ x, u < C * ∑ i, li i * f i x := by
      intro x
      have := hb _ (subset_closure (single_mem_atomicCombos f hC.le x))
      rw [hexp] at this
      calc u < ∑ i, (C * f i x) * li i := this
        _ = C * ∑ i, li i * f i x := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    set μ : ℝ := -u / C with hμ
    have hμ0 : 0 < μ := div_pos (by linarith) hC
    have hdual : ∀ x, 0 ≤ ∑ i, li i * f i x + μ := by
      intro x
      have h1 := hx x
      have h2 : C * μ = -u := by rw [hμ]; field_simp
      have h3 : 0 < C * (∑ i, li i * f i x + μ) := by nlinarith
      exact le_of_lt ((mul_pos_iff_of_pos_left hC).1 h3)
    have key := H li μ hμ0.le hdual
    have : l a = ∑ i, a i * li i := hexp a
    have e : C * μ = -u := by rw [hμ]; field_simp
    have : ∑ i, li i * a i = l a := by
      rw [this]; exact Finset.sum_congr rfl fun i _ => by ring
    nlinarith
  rw [Metric.mem_closure_iff] at hmem
  obtain ⟨v, ⟨N, x, c, hc, hs, rfl⟩, hd⟩ := hmem ε hε
  refine ⟨N, x, c, hc, hs, fun i => ?_⟩
  have := (dist_pi_lt_iff hε).1 hd i
  rw [Real.dist_eq] at this
  rw [abs_sub_comm]; exact this

/-- info: 'FormalResearch.ModularBootstrap.Duality.farkas_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.farkas_approx

end FormalResearch.ModularBootstrap.Duality
