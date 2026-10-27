import Mathlib
import FormalResearch.QIB.BlockDecomp
import FormalResearch.QIB.EasyAbelianCarriers

/-!
# Rank-one blocks: the sandwich `¼ S ≤ P_e ≤ ½ S` (`thm:abelian`, `prop:collapseregimes` (i))

Namespace `FormalResearch.QIB`.  Claim class: **proved** (finite linear algebra; no new axiom).

Source: `QI-B/paper/invariant_discrimination_exponents.tex`, `thm:abelian` (the Helstrom part of its
proof: "if `q ≤ p` and `F = |⟨u|v⟩|²`, the sector contribution lies in `[qF/4, qF/2]`") and
`prop:collapseregimes` (i) (rank-one blocks).

* `rankOneTerm u v = |⟨u,v⟩|² / max(‖u‖², ‖v‖²)` (with `x/0 = 0`, the paper's convention for zero
  denominators); for `u = c_μ`-type vectors with `‖u‖² = p_x(μ)`, `‖v‖² = p_y(μ)`,
  `|⟨u,v⟩|² = |c_μ|²`, this is the summand of `S_d`.
* `half_le_trMin_rankOne`, `trMin_rankOne_le`:
  `½ s ≤ Tr min(|u⟩⟨u|, |v⟩⟨v|) ≤ s` with `s = rankOneTerm u v`, for arbitrary vectors `u, v`
  (not necessarily unit, possibly zero).
* `invErr_rankOne_sandwich`: if every multiplicity block of `a`, `b` is rank one, `τ_λ(a) = |u_λ⟩⟨u_λ|`,
  `τ_λ(b) = |v_λ⟩⟨v_λ|`, then `¼ S ≤ invErr G a b ≤ ½ S`, `S = Σ_λ rankOneTerm u_λ v_λ`.
* `invErr_abelian_sandwich`: the same for any pairwise commuting `G` (every `A λ` is a point by
  `EasyAbelianCarriers`), with `u_λ = a_λ`, `v_λ = b_λ` the sector components.

Not formalized: the identification of `u_λ, v_λ` with the weight projections of `x^{⊗d}, y^{⊗d}` for a
torus acting on `(⊕ V_i)^{⊗d}`, and the exponent consequence ("the rates of `P_e^T` equal those of `S_d`").
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix
open scoped MatrixOrder ComplexOrder

namespace FormalResearch.QIB

open FormalResearch.FrameFree.Helstrom (IsEffect qf err quarter_le_err tr_mul_vecMulVec projMat
  projMat_isEffect projMat_posSemidef qf_projMat_self qf_one_sub_projMat_of_mem one_sub_projMat
  qf_re_nonneg qf_smul_left qf_smul_right)

section RankOne

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- `‖u‖²` as a real number. -/
noncomputable def nsq (u : m → ℂ) : ℝ := (star u ⬝ᵥ u).re

theorem nsq_eq_sum (u : m → ℂ) : nsq u = ∑ i, Complex.normSq (u i) := by
  unfold nsq
  simp [dotProduct, Complex.re_sum, Complex.normSq_apply]

theorem nsq_nonneg (u : m → ℂ) : 0 ≤ nsq u := by
  rw [nsq_eq_sum]; exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _

theorem eq_zero_of_nsq_eq_zero {u : m → ℂ} (h : nsq u = 0) : u = 0 := by
  rw [nsq_eq_sum] at h
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg (u i)).1 h i
    (Finset.mem_univ i)
  simpa using this

theorem star_dotProduct_self_eq (u : m → ℂ) : star u ⬝ᵥ u = (nsq u : ℂ) := by
  rw [nsq_eq_sum]; push_cast
  simp only [dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]; rfl

/-- The paper's `|c|²/max(p,q)` for the pair of rank-one blocks `|u⟩⟨u|`, `|v⟩⟨v|`. -/
noncomputable def rankOneTerm (u v : m → ℂ) : ℝ :=
  Complex.normSq (star u ⬝ᵥ v) / max (nsq u) (nsq v)

theorem rankOneTerm_nonneg (u v : m → ℂ) : 0 ≤ rankOneTerm u v :=
  div_nonneg (Complex.normSq_nonneg _) (le_trans (nsq_nonneg u) (le_max_left _ _))

theorem norm_toLp_sq (u : m → ℂ) : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ m)‖ ^ 2 = nsq u := by
  rw [EuclideanSpace.norm_sq_eq, nsq_eq_sum]
  simp [Complex.sq_norm]

theorem inner_toLp_toLp' (u v : m → ℂ) :
    inner ℂ (WithLp.toLp 2 u : EuclideanSpace ℂ m) (WithLp.toLp 2 v) = star u ⬝ᵥ v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

/-- `⟨v|Π_u|v⟩ = |⟨u,v⟩|²/‖u‖²` for the projector onto the line through `u`. -/
theorem qf_proj_line (u v : m → ℂ) :
    (qf (projMat (Submodule.span ℂ {(WithLp.toLp 2 u : EuclideanSpace ℂ m)})) v v).re =
      Complex.normSq (star u ⬝ᵥ v) / nsq u := by
  rw [qf_projMat_self, Submodule.starProjection_singleton, norm_smul, mul_pow, inner_toLp_toLp',
    norm_toLp_sq, norm_div]
  by_cases h : nsq u = 0
  · simp [h]
  · rw [RCLike.norm_ofReal, abs_of_nonneg (nsq_nonneg u), Complex.normSq_eq_norm_sq]
    field_simp

/-- Upper bound with the line through `u` as the test. -/
theorem trMin_rankOne_le_div (u v : m → ℂ) :
    trMin (Matrix.vecMulVec u (star u)) (Matrix.vecMulVec v (star v)) ≤
      Complex.normSq (star u ⬝ᵥ v) / nsq u := by
  set P := projMat (Submodule.span ℂ {(WithLp.toLp 2 u : EuclideanSpace ℂ m)}) with hP
  have hX : IsEffect (1 - P) :=
    ⟨by rw [hP, one_sub_projMat]; exact projMat_posSemidef _,
      by rw [sub_sub_cancel]; exact projMat_posSemidef _⟩
  have h := sector_ge (Matrix.posSemidef_vecMulVec_self_star u).isHermitian
    (Matrix.posSemidef_vecMulVec_self_star v).isHermitian hX
  rw [tr_mul_vecMulVec, tr_mul_vecMulVec] at h
  have h1 : qf (1 - P) u u = 0 :=
    qf_one_sub_projMat_of_mem _ (Submodule.mem_span_singleton_self _)
  have h2 : (star v ⬝ᵥ ((1 - (1 - P)) *ᵥ v)) = qf P v v := by rw [sub_sub_cancel]; rfl
  have h3 : (star u ⬝ᵥ ((1 - P) *ᵥ u)) = 0 := h1
  rw [h2, h3] at h
  rw [hP, qf_proj_line] at h
  simpa using h

theorem isEffect_one_sub {E : Matrix m m ℂ} (h : IsEffect E) : IsEffect (1 - E) :=
  ⟨h.2, by rw [sub_sub_cancel]; exact h.1⟩

theorem trMin_le_swap {A B : Matrix m m ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    trMin A B ≤ trMin B A := by
  obtain ⟨X, hX, hv⟩ := sector_attain hB hA
  have h := sector_ge hA hB (isEffect_one_sub hX)
  rw [sub_sub_cancel] at h
  linarith

theorem trMin_comm {A B : Matrix m m ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    trMin A B = trMin B A :=
  le_antisymm (trMin_le_swap hA hB) (trMin_le_swap hB hA)

theorem normSq_star_dotProduct_comm (u v : m → ℂ) :
    Complex.normSq (star v ⬝ᵥ u) = Complex.normSq (star u ⬝ᵥ v) := by
  have : star v ⬝ᵥ u = star (star u ⬝ᵥ v) := by
    simp [dotProduct, mul_comm]
  rw [this, Complex.star_def, Complex.normSq_conj]

/-- **Upper bound** `Tr min(|u⟩⟨u|,|v⟩⟨v|) ≤ |⟨u,v⟩|²/max(‖u‖²,‖v‖²)`. -/
theorem trMin_rankOne_le (u v : m → ℂ) :
    trMin (Matrix.vecMulVec u (star u)) (Matrix.vecMulVec v (star v)) ≤ rankOneTerm u v := by
  unfold rankOneTerm
  rcases le_total (nsq v) (nsq u) with h | h
  · rw [max_eq_left h]; exact trMin_rankOne_le_div u v
  · rw [max_eq_right h]
    have := trMin_rankOne_le_div v u
    rw [trMin_comm (Matrix.posSemidef_vecMulVec_self_star v).isHermitian
      (Matrix.posSemidef_vecMulVec_self_star u).isHermitian, normSq_star_dotProduct_comm] at this
    exact this

theorem qf_smul_real_self_re (M : Matrix m m ℂ) (c : ℝ) (v : m → ℂ) :
    (qf M ((c : ℂ) • v) ((c : ℂ) • v)).re = c ^ 2 * (qf M v v).re := by
  rw [qf_smul_left, qf_smul_right, ← mul_assoc, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul]
  ring

/-- Unit normalisation of a nonzero vector. -/
theorem star_dotProduct_normalize {u : m → ℂ} (hp : 0 < nsq u) :
    star ((((Real.sqrt (nsq u))⁻¹ : ℝ) : ℂ) • u) ⬝ᵥ ((((Real.sqrt (nsq u))⁻¹ : ℝ) : ℂ) • u) = 1 := by
  rw [star_smul, smul_dotProduct, dotProduct_smul, star_dotProduct_self_eq, Complex.star_def,
    Complex.conj_ofReal]
  have h : ((Real.sqrt (nsq u))⁻¹) ^ 2 * nsq u = 1 := by
    rw [inv_pow, Real.sq_sqrt hp.le]; exact inv_mul_cancel₀ hp.ne'
  simp only [smul_eq_mul]
  have h' : (Real.sqrt (nsq u))⁻¹ * ((Real.sqrt (nsq u))⁻¹ * nsq u) = 1 := by
    rw [← mul_assoc, ← sq]; exact h
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, h']
  simp

theorem normSq_smul_real_dotProduct (c d : ℝ) (u v : m → ℂ) :
    Complex.normSq (star ((c : ℂ) • u) ⬝ᵥ ((d : ℂ) • v)) = (c * d) ^ 2 * Complex.normSq (star u ⬝ᵥ v) := by
  rw [star_smul, smul_dotProduct, dotProduct_smul, Complex.star_def, Complex.conj_ofReal]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

/-- **Lower bound** `½ |⟨u,v⟩|²/max(‖u‖²,‖v‖²) ≤ Tr min(|u⟩⟨u|,|v⟩⟨v|)`. -/
theorem half_le_trMin_rankOne (u v : m → ℂ) :
    rankOneTerm u v / 2 ≤ trMin (Matrix.vecMulVec u (star u)) (Matrix.vecMulVec v (star v)) := by
  obtain ⟨X, hX, hval⟩ := sector_attain (Matrix.posSemidef_vecMulVec_self_star u).isHermitian
    (Matrix.posSemidef_vecMulVec_self_star v).isHermitian
  rw [tr_mul_vecMulVec, tr_mul_vecMulVec] at hval
  have hx : 0 ≤ (qf X u u).re := qf_re_nonneg hX.1 u
  have hy : 0 ≤ (qf (1 - X) v v).re := qf_re_nonneg hX.2 v
  change (qf X u u).re + (qf (1 - X) v v).re = _ at hval
  rw [← hval]
  set x := (qf X u u).re with hxdef
  set y := (qf (1 - X) v v).re with hydef
  by_cases hp : nsq u = 0
  · have hu0 : u = 0 := eq_zero_of_nsq_eq_zero hp
    subst hu0
    simp [rankOneTerm]
    linarith
  by_cases hq : nsq v = 0
  · have hv0 : v = 0 := eq_zero_of_nsq_eq_zero hq
    subst hv0
    simp [rankOneTerm]
    linarith
  have hp' : 0 < nsq u := lt_of_le_of_ne (nsq_nonneg u) (Ne.symm hp)
  have hq' : 0 < nsq v := lt_of_le_of_ne (nsq_nonneg v) (Ne.symm hq)
  set cu : ℝ := (Real.sqrt (nsq u))⁻¹ with hcu
  set cv : ℝ := (Real.sqrt (nsq v))⁻¹ with hcv
  have e1 : cu ^ 2 * nsq u = 1 := by
    rw [hcu, inv_pow, Real.sq_sqrt hp'.le]; exact inv_mul_cancel₀ hp'.ne'
  have e2 : cv ^ 2 * nsq v = 1 := by
    rw [hcv, inv_pow, Real.sq_sqrt hq'.le]; exact inv_mul_cancel₀ hq'.ne'
  have ha := star_dotProduct_normalize hp'
  have hb := star_dotProduct_normalize hq'
  have quarter := quarter_le_err hX ha hb
  unfold err at quarter
  rw [qf_smul_real_self_re, qf_smul_real_self_re, normSq_smul_real_dotProduct] at quarter
  set N := Complex.normSq (star u ⬝ᵥ v) with hN
  set p := nsq u
  set q := nsq v
  have hpq : 0 ≤ 4 * p * q := by positivity
  have h4 := mul_le_mul_of_nonneg_left quarter hpq
  have l1 : 4 * p * q * ((cu * cv) ^ 2 * N / 4) = (cu ^ 2 * p) * (cv ^ 2 * q) * N := by ring
  have l2 : 4 * p * q * (cu ^ 2 * x / 2 + cv ^ 2 * y / 2) =
      2 * (cu ^ 2 * p) * q * x + 2 * (cv ^ 2 * q) * p * y := by ring
  rw [l1, l2, e1, e2] at h4
  have key : N ≤ 2 * x * q + 2 * y * p := by linarith
  unfold rankOneTerm
  rw [div_div, div_le_iff₀ (by positivity : 0 < max p q * 2)]
  have m1 := mul_le_mul_of_nonneg_left (le_max_right p q) hx
  have m2 := mul_le_mul_of_nonneg_left (le_max_left p q) hy
  nlinarith

end RankOne

section Sandwich

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {A B : Λ → Type*}
  [∀ l, Fintype (A l)] [∀ l, DecidableEq (A l)] [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]

/-- **`thm:abelian` (Helstrom half) and `prop:collapseregimes` (i): rank-one blocks.**  If every
multiplicity block of `a` and of `b` is rank one, `τ_λ(a) = |u_λ⟩⟨u_λ|`, `τ_λ(b) = |v_λ⟩⟨v_λ|`, then
`¼ S ≤ P_e ≤ ½ S` with `S = Σ_λ |⟨u_λ,v_λ⟩|²/max(‖u_λ‖²,‖v_λ‖²)`. -/
theorem invErr_rankOne_sandwich [∀ l, Nonempty (A l)] {G : Set (Matrix (Idx A B) (Idx A B) ℂ)}
    (hG : IsotypicInvariants A G) (a b : Idx A B → ℂ) (u v : ∀ l, B l → ℂ)
    (hu : ∀ l, tau a l = Matrix.vecMulVec (u l) (star (u l)))
    (hv : ∀ l, tau b l = Matrix.vecMulVec (v l) (star (v l))) :
    (1 / 4) * ∑ l, rankOneTerm (u l) (v l) ≤ invErr G a b ∧
      invErr G a b ≤ (1 / 2) * ∑ l, rankOneTerm (u l) (v l) := by
  rw [invErr_eq hG]
  constructor
  · have : ∑ l, rankOneTerm (u l) (v l) / 2 ≤ ∑ l, trMin (tau a l) (tau b l) :=
      Finset.sum_le_sum fun l _ => by rw [hu l, hv l]; exact half_le_trMin_rankOne _ _
    rw [← Finset.sum_div] at this
    linarith
  · have : ∑ l, trMin (tau a l) (tau b l) ≤ ∑ l, rankOneTerm (u l) (v l) :=
      Finset.sum_le_sum fun l _ => by rw [hu l, hv l]; exact trMin_rankOne_le _ _
    linarith

/-- **`thm:abelian`, abstract form.**  For any pairwise commuting `G` (a torus, an abelian group) in
isotypic coordinates, every multiplicity block is rank one and `¼ S ≤ P_e ≤ ½ S` with
`S = Σ_λ |⟨a_λ,b_λ⟩|²/max(‖a_λ‖²,‖b_λ‖²)`, `a_λ = (a_{λ,α₀,·})`. -/
theorem invErr_abelian_sandwich [∀ l, Nonempty (A l)] {G : Set (Matrix (Idx A B) (Idx A B) ℂ)}
    (hG : IsotypicInvariants A G) (hcomm : ∀ U ∈ G, ∀ V ∈ G, U * V = V * U)
    (a b : Idx A B → ℂ) :
    (1 / 4) * ∑ l, rankOneTerm (slice a l (Classical.arbitrary (A l)))
        (slice b l (Classical.arbitrary (A l))) ≤ invErr G a b ∧
      invErr G a b ≤ (1 / 2) * ∑ l, rankOneTerm (slice a l (Classical.arbitrary (A l)))
        (slice b l (Classical.arbitrary (A l))) := by
  have key : ∀ (w : Idx A B → ℂ) (l : Λ), tau w l = Matrix.vecMulVec (slice w l (Classical.arbitrary (A l)))
      (star (slice w l (Classical.arbitrary (A l)))) := by
    intro w l
    by_cases hB : Nonempty (B l)
    · obtain ⟨b0⟩ := hB
      exact tau_eq_vecMulVec_of_subsingleton w l _ (subsingleton_carrier_of_comm hG hcomm l b0)
    · rw [not_nonempty_iff] at hB
      exact Subsingleton.elim _ _
  exact invErr_rankOne_sandwich hG a b _ _ (key a) (key b)

end Sandwich

end FormalResearch.QIB
