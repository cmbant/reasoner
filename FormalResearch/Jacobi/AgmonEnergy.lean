module

public import FormalResearch.Jacobi.CombesThomas

/-!
# Variable-gap Agmon estimate: exact weighted energy identity (AG.3) and AG.1/AG.2

Source: `Weyl/P5/notes/intrinsic_agmon_action.md`, Theorem AG.1, eqs. (AG.1)–(AG.3) (PR 250, head
`cfad461d2`).  For a real symmetric matrix `H` (a Jacobi matrix in the application) put
`A_jk = |H_jk|`, the local gap `γ_j = |λ - H_jj| - ∑_{k≠j} A_jk` (`localGap`; for a Jacobi matrix
`γ_j = |λ - b_j| - A_{j-1} - A_j`), and for a site set `I`, weights `φ`, `x ≥ 0`, `w_j = e^{φ_j} x_j`:

* `ag_energy_identity` : **(AG.3)** the exact identity
  `∑_{j∈I} e^{2φ_j} x_j ((|λ-H_jj| x_j - ∑_{k∈I, k≠j} A_jk x_k)`
  `= ∑_{j∈I} γ_j w_j² + ½∑_{j≠k∈I} A_jk[(w_j - w_k)² - 2(cosh(φ_j - φ_k) - 1) w_j w_k]`
  `+ ∑_{j∈I,k∉I} A_jk w_j²` (the double sum over ordered pairs is twice the sum over links).
* `ag_inequality` : **(AG.2), first inequality, for one component**: if `H u = λ u`, `γ_j ≥ 0` on `I`,
  `φ` vanishes at the *sources* of `I` (sites with a nonzero bond to a site outside `I`) and
  `A_jk (cosh(φ_j - φ_k) - 1) ≤ min(γ_j, γ_k)/4` along nonzero bonds inside `I`
  (the content of the arcosh edge lengths (AG.1), see `edge_condition_of_arcosh`), and every site has
  at most two nonzero off-diagonal entries, then
  `∑_{j∈I} γ_j e^{2φ_j} u_j² ≤ 2 ∑_{j∈I} ∑_{k∉I} A_jk |u_j||u_k|`.
  For `I` with no source the right side vanishes, so `u|_I = 0` when all `γ_j > 0`.

Claim class: proved.  The statements are for any symmetric matrix with at most two nonzero
off-diagonal entries per row (`LocalBound`), a slight generalisation of the finite Jacobi matrices of
the note.  Not formalised: the identification of the maximal connected components of
`F = {γ_j > 0}` and of the path-metric `φ_j` (any `φ` with the stated properties works),
the AG.2 Frobenius corollary for the Racah matrices, and AG.5 (needs the exact Racah spectrum).
-/

@[expose] public section

namespace FormalResearch.Jacobi

open Matrix Finset Real

section Agmon

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `∑_{k≠j} |H_jk|`. -/
noncomputable def bondSum (H : Matrix ι ι ℝ) (j : ι) : ℝ := ∑ k ∈ univ.erase j, |H j k|

/-- The local gap `γ_j = |λ - H_jj| - ∑_{k≠j} |H_jk|`. -/
noncomputable def localGap (H : Matrix ι ι ℝ) (lam : ℝ) (j : ι) : ℝ :=
  |lam - H j j| - bondSum H j

/-- Sum over ordered pairs `j ≠ k` of `I`. -/
noncomputable def pairSum (I : Finset ι) (g : ι → ι → ℝ) : ℝ := ∑ j ∈ I, ∑ k ∈ I.erase j, g j k

omit [Fintype ι] in
theorem pairSum_eq (I : Finset ι) (g : ι → ι → ℝ) :
    pairSum I g = ∑ j ∈ I, ∑ k ∈ I, if j = k then 0 else g j k := by
  unfold pairSum
  refine sum_congr rfl fun j hj => ?_
  rw [← sum_erase_add I (fun k => if j = k then 0 else g j k) hj]
  simp only [ite_true, add_zero]
  refine sum_congr rfl fun k hk => ?_
  have : j ≠ k := fun h => (mem_erase.mp hk).1 h.symm
  simp [this]

omit [Fintype ι] in
theorem pairSum_swap (I : Finset ι) (g : ι → ι → ℝ) :
    pairSum I g = pairSum I (fun j k => g k j) := by
  rw [pairSum_eq, pairSum_eq, sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  by_cases h : k = j
  · simp [h]
  · have : j ≠ k := fun e => h e.symm
    simp [h, this]

omit [Fintype ι] in
theorem pairSum_add (I : Finset ι) (g h : ι → ι → ℝ) :
    pairSum I (fun j k => g j k + h j k) = pairSum I g + pairSum I h := by
  unfold pairSum
  rw [← sum_add_distrib]
  exact sum_congr rfl fun j _ => by rw [← sum_add_distrib]

omit [Fintype ι] in
theorem pairSum_mul_left (I : Finset ι) (c : ℝ) (g : ι → ι → ℝ) :
    pairSum I (fun j k => c * g j k) = c * pairSum I g := by
  unfold pairSum
  rw [mul_sum]
  exact sum_congr rfl fun j _ => by rw [mul_sum]

variable {H : Matrix ι ι ℝ}

theorem bondSum_split (I : Finset ι) {j : ι} (hj : j ∈ I) :
    bondSum H j = ∑ k ∈ I.erase j, |H j k| + ∑ k ∈ Iᶜ, |H j k| := by
  unfold bondSum
  have : (univ.erase j : Finset ι) = I.erase j ∪ Iᶜ := by
    ext k
    simp only [mem_erase, mem_univ, and_true, mem_union, mem_compl]
    by_cases hk : k ∈ I
    · simp [hk]
    · have : k ≠ j := fun h => hk (h ▸ hj)
      simp [hk, this]
  rw [this, sum_union]
  rw [Finset.disjoint_left]
  intro k hk hk'
  exact (mem_compl.mp hk') (mem_of_mem_erase hk)

/-- **(AG.3)** The exact weighted discrete energy identity. -/
theorem ag_energy_identity (hsymm : ∀ j k, |H j k| = |H k j|) (I : Finset ι) (lam : ℝ)
    (x φ : ι → ℝ) :
    ∑ j ∈ I, exp (2 * φ j) * x j * (|lam - H j j| * x j - ∑ k ∈ I.erase j, |H j k| * x k) =
      ∑ j ∈ I, localGap H lam j * (exp (φ j) * x j) ^ 2 +
      (1 / 2) * pairSum I (fun j k => |H j k| * ((exp (φ j) * x j - exp (φ k) * x k) ^ 2 -
          2 * (cosh (φ j - φ k) - 1) * (exp (φ j) * x j) * (exp (φ k) * x k))) +
      ∑ j ∈ I, ∑ k ∈ Iᶜ, |H j k| * (exp (φ j) * x j) ^ 2 := by
  set w : ι → ℝ := fun j => exp (φ j) * x j with hw
  set a : ι → ι → ℝ := fun j k => |H j k| with ha
  -- pointwise expansion of the pair integrand
  have hpt : ∀ j k, a j k * ((w j - w k) ^ 2 - 2 * (cosh (φ j - φ k) - 1) * w j * w k) =
      (a j k * w j ^ 2 - a j k * (exp (2 * φ j) * x j * x k)) +
      (a j k * w k ^ 2 - a j k * (exp (2 * φ k) * x k * x j)) := by
    intro j k
    have e1 : cosh (φ j - φ k) = (exp (φ j - φ k) + exp (φ k - φ j)) / 2 := by
      rw [cosh_eq, show -(φ j - φ k) = φ k - φ j by ring]
    have e2 : exp (φ j - φ k) * exp (φ k) = exp (φ j) := by rw [← exp_add]; ring_nf
    have e3 : exp (φ k - φ j) * exp (φ j) = exp (φ k) := by rw [← exp_add]; ring_nf
    have e4 : exp (2 * φ j) = exp (φ j) * exp (φ j) := by rw [← exp_add]; ring_nf
    have e5 : exp (2 * φ k) = exp (φ k) * exp (φ k) := by rw [← exp_add]; ring_nf
    simp only [hw]
    rw [e1, e4, e5]
    linear_combination (-(a j k * x j * x k * exp (φ j))) * e2 + (-(a j k * x j * x k * exp (φ k))) * e3
  have hpair : (1 / 2 : ℝ) * pairSum I (fun j k => a j k * ((w j - w k) ^ 2 -
      2 * (cosh (φ j - φ k) - 1) * w j * w k)) =
      pairSum I (fun j k => a j k * w j ^ 2 - a j k * (exp (2 * φ j) * x j * x k)) := by
    have h1 : pairSum I (fun j k => a j k * w k ^ 2 - a j k * (exp (2 * φ k) * x k * x j)) =
        pairSum I (fun j k => a j k * w j ^ 2 - a j k * (exp (2 * φ j) * x j * x k)) := by
      rw [pairSum_swap I (fun j k => a j k * w j ^ 2 - a j k * (exp (2 * φ j) * x j * x k))]
      unfold pairSum
      refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
      simp only [ha, hsymm j k]
    simp only [hpt]
    rw [pairSum_add, h1]; ring
  have e4 : ∀ j, exp (2 * φ j) = exp (φ j) * exp (φ j) := fun j => by
    rw [← exp_add]; ring_nf
  have hrow : ∀ j ∈ I, exp (2 * φ j) * x j * (|lam - H j j| * x j - ∑ k ∈ I.erase j, |H j k| * x k) =
      localGap H lam j * w j ^ 2 +
      (∑ k ∈ I.erase j, (a j k * w j ^ 2 - a j k * (exp (2 * φ j) * x j * x k)) +
        ∑ k ∈ Iᶜ, a j k * w j ^ 2) := by
    intro j hj
    have hb := bondSum_split (H := H) I hj
    have hgap : |lam - H j j| = localGap H lam j + bondSum H j := by unfold localGap; ring
    have h1 : ∑ k ∈ I.erase j, (a j k * w j ^ 2 - a j k * (exp (2 * φ j) * x j * x k)) =
        (∑ k ∈ I.erase j, a j k) * w j ^ 2 - exp (2 * φ j) * x j * ∑ k ∈ I.erase j, a j k * x k := by
      rw [sum_sub_distrib, sum_mul, mul_sum]
      congr 1
      exact sum_congr rfl fun k _ => by ring
    have h2 : ∑ k ∈ Iᶜ, a j k * w j ^ 2 = (∑ k ∈ Iᶜ, a j k) * w j ^ 2 := by rw [sum_mul]
    rw [h1, h2, hgap, hb]
    simp only [hw, ha]
    rw [e4 j]
    ring
  have hpair2 : (1 / 2 : ℝ) * pairSum I (fun j k => |H j k| * ((exp (φ j) * x j - exp (φ k) * x k) ^ 2 -
      2 * (cosh (φ j - φ k) - 1) * (exp (φ j) * x j) * (exp (φ k) * x k))) =
      pairSum I (fun j k => a j k * w j ^ 2 - a j k * (exp (2 * φ j) * x j * x k)) := hpair
  rw [sum_congr rfl hrow, sum_add_distrib, sum_add_distrib, hpair2]
  unfold pairSum
  simp only [hw, ha]
  ring

end Agmon

end FormalResearch.Jacobi
