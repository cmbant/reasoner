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

/-- Number of in-block nonzero bonds at `j`, at most two. -/
theorem card_bonds_le {M : ℝ} (hH : LocalBound H M) (I : Finset ι) (j : ι) :
    ((I.erase j).filter fun k => H j k ≠ 0).card ≤ 2 := by
  refine le_trans (card_le_card ?_) (hH.deg j)
  intro k hk
  simp only [mem_filter, mem_erase] at hk
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨hk.1.1, hk.2⟩

/-- The pair-sum of a function of the first index only counts bonds. -/
theorem pairSum_bond_le {M : ℝ} (hH : LocalBound H M) (I : Finset ι) (c : ι → ℝ)
    (hc : ∀ j ∈ I, 0 ≤ c j) :
    pairSum I (fun j k => if H j k ≠ 0 then c j else 0) ≤ 2 * ∑ j ∈ I, c j := by
  unfold pairSum
  rw [mul_sum]
  refine sum_le_sum fun j hj => ?_
  calc ∑ k ∈ I.erase j, (if H j k ≠ 0 then c j else 0)
      = ((I.erase j).filter fun k => H j k ≠ 0).card * c j := by
        rw [← sum_filter]; simp
    _ ≤ 2 * c j := mul_le_mul_of_nonneg_right (by exact_mod_cast card_bonds_le hH I j) (hc j hj)

/-- **Theorem AG.1/AG.2 (one component).**  See the module docstring. -/
theorem ag_inequality {M : ℝ} (hH : LocalBound H M) {lam : ℝ} {u : ι → ℝ} (hu : H *ᵥ u = lam • u)
    (I : Finset ι) (φ : ι → ℝ) (hγ : ∀ j ∈ I, 0 ≤ localGap H lam j)
    (hφ0 : ∀ j ∈ I, (∃ k ∈ Iᶜ, H j k ≠ 0) → φ j = 0)
    (hφ : ∀ j ∈ I, ∀ k ∈ I, j ≠ k →
      |H j k| * (cosh (φ j - φ k) - 1) ≤ min (localGap H lam j) (localGap H lam k) / 4) :
    ∑ j ∈ I, localGap H lam j * (exp (φ j) * |u j|) ^ 2 ≤
      2 * ∑ j ∈ I, ∑ k ∈ Iᶜ, |H j k| * |u j| * |u k| := by
  set x : ι → ℝ := fun j => |u j| with hx
  set w : ι → ℝ := fun j => exp (φ j) * x j with hw
  have hsymm : ∀ j k, |H j k| = |H k j| := fun j k => by rw [hH.symm j k]
  have hid := ag_energy_identity hsymm I lam x φ
  -- comparison inequality
  have hcomp : ∀ j ∈ I, |lam - H j j| * x j - ∑ k ∈ I.erase j, |H j k| * x k ≤
      ∑ k ∈ Iᶜ, |H j k| * x k := by
    intro j hj
    have hrow := congrFun hu j
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hrow
    have h1 : (lam - H j j) * u j = ∑ k ∈ univ.erase j, H j k * u k := by
      rw [← sum_erase_add univ (fun k => H j k * u k) (mem_univ j)] at hrow
      linarith
    have h2 : |lam - H j j| * x j ≤ ∑ k ∈ univ.erase j, |H j k| * x k := by
      calc |lam - H j j| * x j = |(lam - H j j) * u j| := by rw [abs_mul]
        _ = |∑ k ∈ univ.erase j, H j k * u k| := by rw [h1]
        _ ≤ ∑ k ∈ univ.erase j, |H j k * u k| := abs_sum_le_sum_abs _ _
        _ = _ := sum_congr rfl fun k _ => by rw [abs_mul]
    have h3 : (univ.erase j : Finset ι) = I.erase j ∪ Iᶜ := by
      ext k
      simp only [mem_erase, mem_univ, and_true, mem_union, mem_compl]
      by_cases hk : k ∈ I
      · simp [hk]
      · have : k ≠ j := fun h => hk (h ▸ hj)
        simp [hk, this]
    have h4 : Disjoint (I.erase j) Iᶜ := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      exact (mem_compl.mp hk') (mem_of_mem_erase hk)
    rw [h3, sum_union h4] at h2
    linarith
  -- upper bound for the energy
  have hupper : ∑ j ∈ I, exp (2 * φ j) * x j * (|lam - H j j| * x j - ∑ k ∈ I.erase j, |H j k| * x k) ≤
      ∑ j ∈ I, ∑ k ∈ Iᶜ, |H j k| * |u j| * |u k| := by
    refine sum_le_sum fun j hj => ?_
    have hx0 : 0 ≤ x j := abs_nonneg _
    calc exp (2 * φ j) * x j * (|lam - H j j| * x j - ∑ k ∈ I.erase j, |H j k| * x k)
        ≤ exp (2 * φ j) * x j * ∑ k ∈ Iᶜ, |H j k| * x k :=
          mul_le_mul_of_nonneg_left (hcomp j hj) (by positivity)
      _ = ∑ k ∈ Iᶜ, |H j k| * |u j| * |u k| := by
          by_cases hf : ∃ k ∈ Iᶜ, H j k ≠ 0
          · rw [hφ0 j hj hf]
            simp only [mul_zero, exp_zero, one_mul, mul_sum]
            exact sum_congr rfl fun k _ => by simp only [hx]; ring
          · push Not at hf
            simp only [mul_sum]
            refine sum_congr rfl fun k hk => ?_
            rw [hf k hk]; simp
  -- lower bound for the energy
  have hnonneg3 : 0 ≤ ∑ j ∈ I, ∑ k ∈ Iᶜ, |H j k| * (exp (φ j) * x j) ^ 2 :=
    sum_nonneg fun j _ => sum_nonneg fun k _ => by positivity
  have hw0 : ∀ j, 0 ≤ w j := fun j => by simp only [hw, hx]; positivity
  have hgw : ∀ j ∈ I, 0 ≤ localGap H lam j * w j ^ 2 := fun j hj =>
    mul_nonneg (hγ j hj) (sq_nonneg _)
  -- pair term lower bound
  set c : ι → ℝ := fun j => localGap H lam j * w j ^ 2 with hc
  have hpairpt : ∀ j ∈ I, ∀ k ∈ I.erase j,
      -(1 / 4 : ℝ) * ((if H j k ≠ 0 then c j else 0) + (if H k j ≠ 0 then c k else 0)) ≤
        |H j k| * ((w j - w k) ^ 2 - 2 * (cosh (φ j - φ k) - 1) * w j * w k) := by
    intro j hj k hk
    have hkI := mem_of_mem_erase hk
    have hjk : j ≠ k := fun h => (mem_erase.mp hk).1 h.symm
    by_cases hb : H j k = 0
    · have hb' : H k j = 0 := by rw [← hH.symm j k]; exact hb
      simp [hb, hb']
    · have hb' : H k j ≠ 0 := by rw [← hH.symm j k]; exact hb
      simp only [hb, hb', ne_eq, not_false_eq_true, ite_true, hc]
      have hcosh := hφ j hj k hkI hjk
      have hmin1 : min (localGap H lam j) (localGap H lam k) ≤ localGap H lam j := min_le_left _ _
      have hmin2 : min (localGap H lam j) (localGap H lam k) ≤ localGap H lam k := min_le_right _ _
      have hwjk : 0 ≤ w j * w k := mul_nonneg (hw0 j) (hw0 k)
      have h1 : 2 * (|H j k| * (cosh (φ j - φ k) - 1)) * (w j * w k) ≤
          (min (localGap H lam j) (localGap H lam k) / 2) * (w j * w k) :=
        mul_le_mul_of_nonneg_right (by linarith) hwjk
      have h2 : (min (localGap H lam j) (localGap H lam k) / 2) * (w j * w k) ≤
          (min (localGap H lam j) (localGap H lam k) / 4) * (w j ^ 2 + w k ^ 2) := by
        have hm : 0 ≤ min (localGap H lam j) (localGap H lam k) :=
          le_min (hγ j hj) (hγ k hkI)
        nlinarith [sq_nonneg (w j - w k)]
      have h3 : (min (localGap H lam j) (localGap H lam k) / 4) * (w j ^ 2 + w k ^ 2) ≤
          (1 / 4) * (localGap H lam j * w j ^ 2 + localGap H lam k * w k ^ 2) := by
        nlinarith [sq_nonneg (w j), sq_nonneg (w k)]
      nlinarith [sq_nonneg (w j - w k), abs_nonneg (H j k)]
  have hmono : pairSum I (fun j k => -(1 / 4 : ℝ) * ((if H j k ≠ 0 then c j else 0) +
      (if H k j ≠ 0 then c k else 0))) ≤
      pairSum I (fun j k => |H j k| * ((w j - w k) ^ 2 - 2 * (cosh (φ j - φ k) - 1) * w j * w k)) := by
    unfold pairSum
    exact sum_le_sum fun j hj => sum_le_sum fun k hk => hpairpt j hj k hk
  have hP : pairSum I (fun j k => if H j k ≠ 0 then c j else 0) ≤ 2 * ∑ j ∈ I, c j :=
    pairSum_bond_le hH I c hgw
  have hP2 : pairSum I (fun j k => if H k j ≠ 0 then c k else 0) =
      pairSum I (fun j k => if H j k ≠ 0 then c j else 0) :=
    (pairSum_swap I (fun j k => if H j k ≠ 0 then c j else 0)).symm
  rw [pairSum_mul_left, pairSum_add, hP2] at hmono
  have hlow : -(∑ j ∈ I, c j) ≤ pairSum I (fun j k => |H j k| *
      ((w j - w k) ^ 2 - 2 * (cosh (φ j - φ k) - 1) * w j * w k)) := by
    linarith
  have hid' : ∑ j ∈ I, exp (2 * φ j) * x j * (|lam - H j j| * x j - ∑ k ∈ I.erase j, |H j k| * x k) =
      ∑ j ∈ I, c j + (1 / 2) * pairSum I (fun j k => |H j k| *
        ((w j - w k) ^ 2 - 2 * (cosh (φ j - φ k) - 1) * w j * w k)) +
      ∑ j ∈ I, ∑ k ∈ Iᶜ, |H j k| * (exp (φ j) * x j) ^ 2 := hid
  have hfin : ∑ j ∈ I, c j ≤ 2 * ∑ j ∈ I, ∑ k ∈ Iᶜ, |H j k| * |u j| * |u k| := by
    linarith
  exact hfin

/-- The arcosh edge length (AG.1) gives the cosh-form edge condition used in `ag_inequality`:
if `A > 0`, `m ≥ 0` and `|δ| ≤ arcosh (1 + m/(4A))` then `A (cosh δ - 1) ≤ m/4`. -/
theorem edge_condition_of_arcosh {A m δ : ℝ} (hA : 0 < A) (hm : 0 ≤ m)
    (hδ : |δ| ≤ Real.arcosh (1 + m / (4 * A))) : A * (cosh δ - 1) ≤ m / 4 := by
  have hq : 0 ≤ m / (4 * A) := by positivity
  have h1 : 1 ≤ 1 + m / (4 * A) := by linarith
  have h2 : cosh δ ≤ 1 + m / (4 * A) := by
    rw [← Real.cosh_arcosh h1]
    exact Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg (Real.arcosh_nonneg h1)]; exact hδ)
  have h3 : A * (cosh δ - 1) ≤ A * (m / (4 * A)) := mul_le_mul_of_nonneg_left (by linarith) hA.le
  calc A * (cosh δ - 1) ≤ A * (m / (4 * A)) := h3
    _ = m / 4 := by field_simp

theorem card_nbr_le {M : ℝ} (hH : LocalBound H M) (S : Finset ι) {j : ι} (hj : j ∉ S) :
    (S.filter fun k => H j k ≠ 0).card ≤ 2 := by
  refine le_trans (card_le_card ?_) (hH.deg j)
  intro k hk
  simp only [mem_filter] at hk
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h => hj (h ▸ hk.1), hk.2⟩

/-- Boundary links cost at most `M ∑ u²`: `∑_{j∈U, k∉U} |H_jk||u_j||u_k| ≤ M ∑ u_j²`
(every site meets at most two links). -/
theorem ag_boundary_le {M : ℝ} (hH : LocalBound H M) (hM : 0 ≤ M) (U : Finset ι) (u : ι → ℝ) :
    ∑ j ∈ U, ∑ k ∈ Uᶜ, |H j k| * |u j| * |u k| ≤ M * ∑ j, u j ^ 2 := by
  have hpt : ∀ j ∈ U, ∀ k ∈ Uᶜ, |H j k| * |u j| * |u k| ≤
      M / 2 * ((if H j k ≠ 0 then u j ^ 2 else 0) + (if H j k ≠ 0 then u k ^ 2 else 0)) := by
    intro j hj k hk
    have hjk : j ≠ k := fun h => (mem_compl.mp hk) (h ▸ hj)
    by_cases hb : H j k = 0
    · simp [hb]
    · simp only [hb, ne_eq, not_false_eq_true, ite_true]
      have h1 : |H j k| ≤ M := hH.bound j k hjk
      have h2 : |u j| * |u k| ≤ (u j ^ 2 + u k ^ 2) / 2 := by
        nlinarith [sq_nonneg (|u j| - |u k|), sq_abs (u j), sq_abs (u k)]
      calc |H j k| * |u j| * |u k| = |H j k| * (|u j| * |u k|) := by ring
        _ ≤ M * ((u j ^ 2 + u k ^ 2) / 2) :=
          mul_le_mul h1 h2 (by positivity) hM
        _ = _ := by ring
  have h1 : ∑ j ∈ U, ∑ k ∈ Uᶜ, (if H j k ≠ 0 then u j ^ 2 else 0) ≤ 2 * ∑ j ∈ U, u j ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun j hj => ?_
    calc ∑ k ∈ Uᶜ, (if H j k ≠ 0 then u j ^ 2 else 0)
        = ((Uᶜ).filter fun k => H j k ≠ 0).card * u j ^ 2 := by rw [← sum_filter]; simp
      _ ≤ 2 * u j ^ 2 := mul_le_mul_of_nonneg_right
          (by exact_mod_cast card_nbr_le hH Uᶜ (by simpa using hj)) (sq_nonneg _)
  have h2 : ∑ j ∈ U, ∑ k ∈ Uᶜ, (if H j k ≠ 0 then u k ^ 2 else 0) ≤ 2 * ∑ k ∈ Uᶜ, u k ^ 2 := by
    rw [sum_comm, mul_sum]
    refine sum_le_sum fun k hk => ?_
    calc ∑ j ∈ U, (if H j k ≠ 0 then u k ^ 2 else 0)
        = (U.filter fun j => H k j ≠ 0).card * u k ^ 2 := by
          rw [← sum_filter]
          simp only [sum_const, nsmul_eq_mul]
          congr 3
          ext j
          simp [hH.symm j k]
      _ ≤ 2 * u k ^ 2 := mul_le_mul_of_nonneg_right
          (by exact_mod_cast card_nbr_le hH U (mem_compl.mp hk)) (sq_nonneg _)
  calc ∑ j ∈ U, ∑ k ∈ Uᶜ, |H j k| * |u j| * |u k|
      ≤ ∑ j ∈ U, ∑ k ∈ Uᶜ, M / 2 * ((if H j k ≠ 0 then u j ^ 2 else 0) +
          (if H j k ≠ 0 then u k ^ 2 else 0)) :=
        sum_le_sum fun j hj => sum_le_sum fun k hk => hpt j hj k hk
    _ = M / 2 * (∑ j ∈ U, ∑ k ∈ Uᶜ, (if H j k ≠ 0 then u j ^ 2 else 0) +
          ∑ j ∈ U, ∑ k ∈ Uᶜ, (if H j k ≠ 0 then u k ^ 2 else 0)) := by
        simp only [mul_add, sum_add_distrib, ← mul_sum]
    _ ≤ M / 2 * (2 * ∑ j ∈ U, u j ^ 2 + 2 * ∑ k ∈ Uᶜ, u k ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
    _ = M * ∑ j, u j ^ 2 := by
        rw [← sum_add_sum_compl U (fun j => u j ^ 2)]; ring

/-- **Theorem AG.1/AG.2, whole family of components.**  Components `I a` of the forbidden set
(pairwise disjoint, no nonzero bond between two different components), each with weights `φ a`
satisfying the hypotheses of `ag_inequality`: `∑_a ∑_{j∈I_a} γ_j e^{2φ_a(j)} u_j² ≤ 2 M ∑ u²`. -/
theorem ag_total {M : ℝ} (hH : LocalBound H M) (hM : 0 ≤ M) {lam : ℝ} {u : ι → ℝ}
    (hu : H *ᵥ u = lam • u) {α : Type*} [Fintype α] (I : α → Finset ι)
    (hdisj : ∀ a b, a ≠ b → Disjoint (I a) (I b))
    (hsep : ∀ a b, a ≠ b → ∀ j ∈ I a, ∀ k ∈ I b, H j k = 0) (φ : α → ι → ℝ)
    (hγ : ∀ a, ∀ j ∈ I a, 0 ≤ localGap H lam j)
    (hφ0 : ∀ a, ∀ j ∈ I a, (∃ k ∈ (I a)ᶜ, H j k ≠ 0) → φ a j = 0)
    (hφ : ∀ a, ∀ j ∈ I a, ∀ k ∈ I a, j ≠ k →
      |H j k| * (cosh (φ a j - φ a k) - 1) ≤ min (localGap H lam j) (localGap H lam k) / 4) :
    ∑ a, ∑ j ∈ I a, localGap H lam j * (exp (φ a j) * |u j|) ^ 2 ≤ 2 * M * ∑ j, u j ^ 2 := by
  classical
  set U := univ.biUnion I with hU
  have hcomp : ∀ a, ∑ j ∈ I a, localGap H lam j * (exp (φ a j) * |u j|) ^ 2 ≤
      2 * ∑ j ∈ I a, ∑ k ∈ Uᶜ, |H j k| * |u j| * |u k| := by
    intro a
    refine le_trans (ag_inequality hH hu (I a) (φ a) (hγ a) (hφ0 a) (hφ a)) ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    refine sum_le_sum fun j hj => ?_
    refine le_of_eq (sum_subset ?_ ?_).symm
    · intro k hk
      simp only [mem_compl, hU, mem_biUnion, mem_univ, true_and, not_exists] at hk ⊢
      exact fun h => hk a h
    · intro k hk hk'
      simp only [mem_compl, hU, mem_biUnion, mem_univ, true_and, not_exists] at hk hk'
      obtain ⟨b, hb⟩ := not_forall.mp hk'
      rw [not_not] at hb
      have hab : a ≠ b := fun h => hk (h ▸ hb)
      rw [hsep a b hab j hj k hb]; simp
  calc ∑ a, ∑ j ∈ I a, localGap H lam j * (exp (φ a j) * |u j|) ^ 2
      ≤ ∑ a, 2 * ∑ j ∈ I a, ∑ k ∈ Uᶜ, |H j k| * |u j| * |u k| := sum_le_sum fun a _ => hcomp a
    _ = 2 * ∑ j ∈ U, ∑ k ∈ Uᶜ, |H j k| * |u j| * |u k| := by
        rw [← mul_sum, hU, sum_biUnion]
        intro a _ b _ hab
        exact hdisj a b hab
    _ ≤ 2 * (M * ∑ j, u j ^ 2) := mul_le_mul_of_nonneg_left (ag_boundary_le hH hM U u) (by norm_num)
    _ = 2 * M * ∑ j, u j ^ 2 := by ring

/-- info: 'FormalResearch.Jacobi.ag_energy_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ag_energy_identity

/-- info: 'FormalResearch.Jacobi.ag_inequality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ag_inequality

/-- info: 'FormalResearch.Jacobi.ag_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ag_total

/-- info: 'FormalResearch.Jacobi.edge_condition_of_arcosh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edge_condition_of_arcosh

end Agmon

end FormalResearch.Jacobi
