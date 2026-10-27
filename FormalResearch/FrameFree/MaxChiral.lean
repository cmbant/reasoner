import FormalResearch.FrameFree.WeylVertex
import FormalResearch.FrameFree.Design

/-!
# Maximal chirality on the critical locus: the bound

Paper P, Lemma `lem:polarisedlongroot` and the bound part of Theorem `thm:maxchiral`
(`critical_chirality_proof.tex`).  For `q, x ∈ ℂ⁴` there is `w ∈ W(D₄)` with
`|xᵀ w q|² ≥ (‖q‖²‖x‖² + 7|x†q|² + |x·q|²)/18`; with `x = q`, `‖q‖ = 1`,
`F_K ≥ 4/9 + |q·q|²/18 ≥ 4/9`.

The analytic input is the planar sign inequality for four complex numbers (`PlanarSign4`,
`planar_sign_inequality.tex`), taken here as a hypothesis; `FrameFree/PlanarSign.lean` proves it.
-/

open Finset

namespace FormalResearch.FrameFree

/-- `xᵀ w q = ∑_k (-1)^{e k} x_k q_{σ k}`. -/
def bil (x q : Fin 4 → ℂ) (w : SP) : ℂ := ∑ k, (sg (w.2 k) : ℂ) * x k * q (w.1 k)

theorem weylVal_eq_bil (d : Fin 4 → ℂ) (w : SP) : weylVal d w = bil d d w := rfl

/-- The planar sign inequality for four complex numbers (`lem:planarsign`, `m = 4`). -/
def PlanarSign4 : Prop :=
  ∀ v : Fin 4 → ℂ, ∃ s : Fin 4 → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
    (1 / 3 : ℝ) * ((∑ i, ‖v i‖) ^ 2 + ∑ i, ‖v i‖ ^ 2) ≤ ‖∑ i, (s i : ℂ) * v i‖ ^ 2

/-- The three pairings `{ab|ce}` of the four coordinates. -/
def pairing : Fin 3 → Fin 4 × Fin 4 × Fin 4 × Fin 4
  | 0 => (0, 1, 2, 3)
  | 1 => (0, 2, 1, 3)
  | 2 => (0, 3, 1, 2)

/-- Components `(x_a ± x_b)`, `(x_c ± x_e)` of `x` along the long basis of the pairing `P`
(the unit vectors are `u = (e_a ± e_b)/√2`, so `u·x = cx/√2`). -/
def cx (P : Fin 3) (x : Fin 4 → ℂ) : Fin 4 → ℂ := fun i =>
  match i with
  | 0 => x (pairing P).1 + x (pairing P).2.1
  | 1 => x (pairing P).1 - x (pairing P).2.1
  | 2 => x (pairing P).2.2.1 + x (pairing P).2.2.2
  | 3 => x (pairing P).2.2.1 - x (pairing P).2.2.2

/-- The four products `(u·x)(u·q)` over the long basis of the pairing `P`. -/
noncomputable def vP (P : Fin 3) (x q : Fin 4 → ℂ) : Fin 4 → ℂ := fun i => cx P x i * cx P q i / 2

/-- The signed permutation `∑ s_u u uᵀ` of a long basis (`b i = true` for `s_i = -1`). -/
def longW (P : Fin 3) (b1 b2 b3 b4 : Bool) : SP :=
  ((if b1 = b2 then 1 else Equiv.swap (pairing P).1 (pairing P).2.1) *
     (if b3 = b4 then 1 else Equiv.swap (pairing P).2.2.1 (pairing P).2.2.2),
   fun k => if k = (pairing P).1 ∨ k = (pairing P).2.1 then b1 else b3)

theorem longW_mem (P : Fin 3) (b1 b2 b3 b4 : Bool) : longW P b1 b2 b3 b4 ∈ weylSet := by
  revert P b1 b2 b3 b4
  decide +kernel

/-- `s_i = 1 - 2 [b_i]`. -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

theorem bil_longW (P : Fin 3) (x q : Fin 4 → ℂ) (b1 b2 b3 b4 : Bool) :
    bil x q (longW P b1 b2 b3 b4) =
      (sgn b1 : ℂ) * vP P x q 0 + (sgn b2 : ℂ) * vP P x q 1 + (sgn b3 : ℂ) * vP P x q 2 +
        (sgn b4 : ℂ) * vP P x q 3 := by
  unfold bil longW vP cx sgn sg
  fin_cases P <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    simp [pairing, Fin.sum_univ_four, Equiv.swap_apply_def] <;> ring

theorem hdot_cx (P : Fin 3) (x q : Fin 4 → ℂ) :
    hdot x q = ∑ i, (starRingEnd ℂ) (cx P x i) * cx P q i / 2 := by
  unfold hdot cx
  fin_cases P <;> simp [pairing, Fin.sum_univ_four] <;> ring

theorem norm_hdot_le (P : Fin 3) (x q : Fin 4 → ℂ) : ‖hdot x q‖ ≤ ∑ i, ‖vP P x q i‖ := by
  rw [hdot_cx P]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [vP, norm_div, norm_mul]

theorem sum_vP_sq (x q : Fin 4 → ℂ) :
    ∑ P : Fin 3, ∑ i, Complex.normSq (vP P x q i) = longSum q x := by
  have hf : ((univ : Finset (Fin 4 × Fin 4)).filter (fun p => p.1 < p.2)) =
      {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} := by decide
  unfold longSum
  rw [hf]
  have h2 : Complex.normSq (2 : ℂ) = 4 := by simp [Complex.normSq_apply]; norm_num
  simp only [vP, cx, Fin.sum_univ_three, Fin.sum_univ_four, pairing, map_mul, map_div₀, h2]
  simp [Finset.sum_insert]
  ring

theorem norm_sq_eq_normSq (z : ℂ) : ‖z‖ ^ 2 = Complex.normSq z := (Complex.normSq_eq_norm_sq z).symm

/-- **Polarised long-root bound** (`lem:polarisedlongroot`), given the planar sign inequality. -/
theorem polarised_long_root (hP : PlanarSign4) (q x : Fin 4 → ℂ) :
    ∃ w ∈ weylSet, (nrm2 q * nrm2 x + 7 * Complex.normSq (hdot x q) + Complex.normSq (bdot x q)) / 18 ≤
      Complex.normSq (bil x q w) := by
  set S : Fin 3 → ℝ := fun P => ∑ i, Complex.normSq (vP P x q i) with hS
  have hsum : ∑ P, S P = longSum q x := sum_vP_sq x q
  have hdes := design_identity q x
  -- some pairing carries at least a third of the total
  obtain ⟨P, hPS⟩ : ∃ P : Fin 3, longSum q x / 3 ≤ S P := by
    by_contra hcon
    push Not at hcon
    have h0 := hcon 0; have h1 := hcon 1; have h2 := hcon 2
    rw [Fin.sum_univ_three] at hsum
    linarith
  obtain ⟨s, hs, hineq⟩ := hP (vP P x q)
  have hb : ∀ i, s i = sgn (decide (s i = -1)) := by
    intro i
    rcases hs i with h | h
    · rw [h]; simp [sgn]
    · rw [h]; simp [sgn]
  refine ⟨longW P (decide (s 0 = -1)) (decide (s 1 = -1)) (decide (s 2 = -1)) (decide (s 3 = -1)),
    longW_mem _ _ _ _ _, ?_⟩
  rw [← norm_sq_eq_normSq (bil x q _), bil_longW]
  have hsumv : ∑ i, (s i : ℂ) * vP P x q i =
      (sgn (decide (s 0 = -1)) : ℂ) * vP P x q 0 + (sgn (decide (s 1 = -1)) : ℂ) * vP P x q 1 +
      (sgn (decide (s 2 = -1)) : ℂ) * vP P x q 2 + (sgn (decide (s 3 = -1)) : ℂ) * vP P x q 3 := by
    rw [Fin.sum_univ_four, ← hb 0, ← hb 1, ← hb 2, ← hb 3]
  rw [hsumv] at hineq
  have hn1 : ‖hdot x q‖ ^ 2 ≤ (∑ i, ‖vP P x q i‖) ^ 2 := by
    gcongr
    exact norm_hdot_le P x q
  have hn2 : ∑ i, ‖vP P x q i‖ ^ 2 = S P := by
    simp only [hS, norm_sq_eq_normSq]
  rw [hn2] at hineq
  have hh : ‖hdot x q‖ ^ 2 = Complex.normSq (hdot x q) := norm_sq_eq_normSq _
  rw [hh] at hn1
  linarith [hdes, hPS, hn1, hineq]

/-- **`thm:maxchiral` (bound)**: for `‖q‖ = 1`, `F_K ≥ 4/9 + |q·q|²/18`, given `PlanarSign4`. -/
theorem FKmag_ge_maxchiral (hP : PlanarSign4) (q : Fin 4 → ℂ) (hq : nrm2 q = 1) :
    4 / 9 + Complex.normSq (bdot q q) / 18 ≤ FKmag q := by
  obtain ⟨w, hw, h⟩ := polarised_long_root hP q q
  have h1 : Complex.normSq (hdot q q) = 1 := by
    have : hdot q q = (nrm2 q : ℂ) := by
      unfold hdot nrm2
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.normSq_eq_conj_mul_self]
    rw [this, hq]; simp
  rw [hq, h1] at h
  have := le_FKmag q hw
  rw [weylVal_eq_bil] at this
  linarith

theorem FKmag_ge_four_ninths (hP : PlanarSign4) (q : Fin 4 → ℂ) (hq : nrm2 q = 1) :
    4 / 9 ≤ FKmag q := by
  have := FKmag_ge_maxchiral hP q hq
  have := Complex.normSq_nonneg (bdot q q)
  linarith

end FormalResearch.FrameFree
