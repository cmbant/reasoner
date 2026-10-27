import FormalResearch.FrameFree.SupportRateGelfand

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ComplexConjugate InnerProductSpace BigOperators IsMulCommutative

/-!
# Support rate: the compressed-shift algebra for an arbitrary set `O` of vectors

Namespace `FormalResearch.FrameFree.SupportRate`.  For a nonempty set `O ⊆ ℂ^N` with
`W_d = span {z^{⊗d} : z ∈ O}`, if `|⟨x,z⟩|² ≤ F ‖z‖²` for every `z` with `z^{⊗d} ∈ W_d` for all `d`
(the Zariski-closure cone of `O`), then `‖Π_{W_d} x^{⊗d}‖² ≤ c^d` eventually, for every `c > F`
(`eventually_proj_sq_le`).  This is the spectral-radius half of `thm:supportrate`, proved from the
compressed shifts `T_a` on `ℓ²(⊕_d W_d)`.
-/

namespace FormalResearch.FrameFree.SupportRate

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem ThB_T_eq (O : Set (V N)) :
    ∀ (k : ℕ) (r : Eg N k), ThB (fun j => T O (ev j)) k r = Th O k r
  | 0, r => rfl
  | k + 1, r => by
    show ∑ j, T O (ev j) * ThB (fun j => T O (ev j)) k (slice j r) =
      ∑ j, T O (ev j) * Th O k (slice j r)
    exact Finset.sum_congr rfl fun j _ => by rw [ThB_T_eq O k (slice j r)]

/-- **Spectral-radius half of `thm:supportrate`, abstract form.** -/
theorem eventually_proj_sq_le (O : Set (V N)) (hO : O.Nonempty) (x : V N) (F : ℝ) (hF0 : 0 ≤ F)
    (hF : ∀ z : V N, (∀ k, pw z k ∈ W O k) → ‖⟪x, z⟫_ℂ‖ ^ 2 ≤ F * ‖z‖ ^ 2) {c : ℝ} (hc : F < c) :
    ∀ᶠ d : ℕ in Filter.atTop, ‖(W O d).starProjection (pw x d)‖ ^ 2 ≤ c ^ d := by
  obtain ⟨z0, hz0⟩ := hO
  have : Nontrivial (H O) :=
    ⟨⟨one O hz0, 0, fun h => by have := norm_one O hz0; rw [h] at this; simp at this⟩⟩
  have hc0 : 0 < c := lt_of_le_of_lt hF0 hc
  have hcomm : ∀ i j, (fun j => T O (ev j)) i * (fun j => T O (ev j)) j =
      (fun j => T O (ev j)) j * (fun j => T O (ev j)) i := fun i j => T_comm O (ev i) (ev j)
  have := AlgB_comm (B := H O →L[ℂ] H O) (s := fun j => T O (ev j)) hcomm
  have hnorm : ∀ a : V N, ‖∑ j, a j • (fun j => T O (ev j)) j‖ ≤ ‖a‖ := fun a => by
    show ‖∑ j, a j • T O (ev j)‖ ≤ ‖a‖
    rw [← T_sum]; exact norm_T_le O a
  have h1 : ‖(1 : H O →L[ℂ] H O)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hJ : ∀ k (r : Eg N k), r ∈ (W O k)ᗮ → ThB (fun j => T O (ev j)) k r = 0 := fun k r hr => by
    rw [ThB_T_eq]; exact Th_eq_zero O hr
  have hF' : ∀ z : V N, (∀ k, pw z k ∈ ((W O k)ᗮ)ᗮ) → ‖⟪x, z⟫_ℂ‖ ^ 2 ≤ F * ‖z‖ ^ 2 := fun z hz =>
    hF z fun k => by simpa [Submodule.orthogonal_orthogonal] using hz k
  have key := eventually_norm_pow_le (s := fun j => T O (ev j)) (fun k => (W O k)ᗮ) hnorm h1 hJ x F hF0
    hF' hc
  filter_upwards [key] with d hd
  have hTx : (∑ j, x j • (fun j => T O (ev j)) j) = T O x := (T_sum O x).symm
  rw [hTx] at hd
  have h2 := (Rk_le_norm_pow O x hz0 d).trans hd
  calc ‖(W O d).starProjection (pw x d)‖ ^ 2 ≤ ((Real.sqrt c) ^ d) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ = c ^ d := by
        rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hc0.le]

end FormalResearch.FrameFree.SupportRate
