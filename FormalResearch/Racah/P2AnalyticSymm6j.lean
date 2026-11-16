module

public import FormalResearch.Racah.P2AnalyticBulk6j
public import FormalResearch.Racah.P2AnalyticUniform6j

/-!
# `A ↔ B` symmetry of the one-small `6j` carrier germ and of the homogeneous coefficients
(Weyl P2, `lem:sqrtfreecarrier6j`, `thm:6jallorderlocal`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`.  `lem:sqrtfreecarrier6j` states that the coefficients of
the carrier polynomial `P̃_f` are "symmetric under `A ↔ B`", and `thm:6jallorderlocal` that the first
chamber reduction exchanges `A` and `B` and is immaterial because `x`, `q`, `η_k` and the stretched seed are
symmetric, "so by induction every `𝒢_{2r}(A,B,C)` is" symmetric (the operator-level instance of
`thm:6jallorderlocal` in the canonical sector is `P2AnalyticAllOrder6j`; this file is the coefficient-level
symmetry).

`ptilde6_symm_uv` (`P2AnalyticCarrier6jPoly`) is the polynomial statement.  Here it is carried through the
closed-form germ and its Taylor coefficients:

* `G6c_swap`: `G6c m n d α β γ t = G6c m n d β α γ t` (the edge factor, `Π_f`, the angle and the carrier
  are symmetric);
* `G6_swap`: the same for `G6 f m n` in all four chambers (the chambers III and IV already contain an
  `α ↔ β` exchange; the statement holds at fixed `(f, m, n)` without exchanging `m` and `n`);
* `a6_swap`, `G6even_swap` (**the coefficient `G_{f,2r}(A,B,C)` of `thm:6jeven` is symmetric under
  `A ↔ B`** at fixed `(f,m,n)`), for every `r`;
* `Hc_neg_delta`, `s6c_neg_delta`, `s6_neg_delta`: the uniform germ and the coefficients `s_r(τ; δ)` of
  `thm:uniformedge`(b) are even in `δ = (A-B)/(A+B)` (so the `δ ↦ -δ` in the definitions of `Hall` and `s6` for
  the chambers III and IV is immaterial).

This is the coefficient-level form of the paper's operator statement ("every `𝒢_{2r}(A,B,C)` is
symmetric"): this file has no differential operators `𝒢_{2r}` (they are in `P2AnalyticAllOrder6j`, canonical
sector only, without the `A ↔ B` symmetry statement).  Exact algebraic identities, no
analysis beyond the definition of the Taylor coefficient.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Racah.SixJ

/-- The edge radicand is symmetric under `α ↔ β`. -/
lemma edgeSqT_swap (m n : ℚ) (α β γ t : ℝ) :
    edgeSqT m n α β γ t = edgeSqT m n β α γ t := by
  unfold edgeSqT
  have e1 : -β + α + γ = α - β + γ := by ring
  have e2 : -α + β + γ = β - α + γ := by ring
  have e3 : β + α - γ = α + β - γ := by ring
  have e4 : β + α + γ = α + β + γ := by ring
  rw [e1, e2, e3, e4, show 4 * β * α = 4 * α * β by ring]
  ring

/-- `Π_f` is symmetric under `α ↔ β`. -/
lemma piSixT_swap (f : ℚ) (α β t : ℝ) : piSixT f α β t = piSixT f β α t := by
  unfold piSixT
  refine Finset.prod_congr rfl fun k _ => ?_
  ring

/-- The law-of-cosines angle of the shape is symmetric under `α ↔ β`. -/
lemma cosA_swap_shape (α β γ : ℝ) : cosA α β γ = cosA β α γ := by
  unfold cosA
  rw [mul_comm (2 * α) β, add_comm (α ^ 2) (β ^ 2)]
  ring

/-- **`A ↔ B` symmetry of the canonical-sector germ** (`lem:sqrtfreecarrier6j`). -/
theorem G6c_swap (m n : ℚ) (d : ℕ) (α β γ t : ℝ) :
    G6c m n d α β γ t = G6c m n d β α γ t := by
  unfold G6c
  rw [edgeSqT_swap m n α β γ t, piSixT_swap (m + d) α β t, cosA_swap_shape α β γ,
    ptilde6_symm_uv m n _ _ _ _ d]
  have : t / (β * α) = t / (α * β) := by rw [mul_comm]
  rw [this]

/-- **`A ↔ B` symmetry of the germ `G6` in all four chambers.** -/
theorem G6_swap (f m n : ℚ) (α β γ t : ℝ) : G6 f m n α β γ t = G6 f m n β α γ t := by
  unfold G6
  split_ifs
  · exact G6c_swap _ _ _ _ _ _ _
  · rw [G6c_swap _ _ _ α β]
  · rw [G6c_swap _ _ _ α β]
  · rw [G6c_swap _ _ _ α β]

/-- The Taylor coefficients `a_{f,r}` of the germ are symmetric under `α ↔ β`. -/
theorem a6_swap (f m n : ℚ) (r : ℕ) (α β γ : ℝ) :
    a6 f m n r (α, β, γ) = a6 f m n r (β, α, γ) := by
  unfold a6 taylorCoeff
  have : (fun t => G6 f m n α β γ t) = fun t => G6 f m n β α γ t := funext fun t => G6_swap f m n α β γ t
  simp only [this]

/-- **The homogeneous coefficient `G_{f,2r}(A,B,C)` of `thm:6jeven` is symmetric under `A ↔ B`** (at
fixed `f, m, n`), for every `r`. -/
theorem G6even_swap (f m n : ℚ) (r : ℕ) (A B C : ℝ) :
    G6even f m n r A B C = G6even f m n r B A C := by
  unfold G6even
  rw [show B + A + C = A + B + C by ring, a6_swap f m n r]

/-- The uniform germ is even in `δ` (`A ↔ B` is `δ ↦ -δ`). -/
theorem Hc_neg_delta (m n : ℚ) (d : ℕ) (τ δ t : ℝ) : Hc m n d τ (-δ) t = Hc m n d τ δ t := by
  unfold Hc
  have e1 : (1 + -δ) / 2 = (1 - δ) / 2 := by ring
  have e2 : (1 - -δ) / 2 = (1 + δ) / 2 := by ring
  rw [e1, e2, piSixT_swap (m + d) ((1 - δ) / 2) ((1 + δ) / 2) t,
    ptilde6_symm_uv m n τ _ _ _ d, mul_comm ((1 - δ) / 2) ((1 + δ) / 2)]

/-- The Taylor coefficients `s_r(τ; δ)` of the canonical-sector uniform germ are even in `δ`. -/
theorem s6c_neg_delta (m n : ℚ) (d r : ℕ) (τ δ : ℝ) : s6c m n d r τ (-δ) = s6c m n d r τ δ := by
  unfold s6c taylorCoeff
  have : (fun t => Hc m n d τ (-δ) t) = fun t => Hc m n d τ δ t :=
    funext fun t => Hc_neg_delta m n d τ δ t
  simp only [this]

/-- The coefficients `s_r(τ; δ)` of `thm:uniformedge`(b), all chambers, are even in `δ`. -/
theorem s6_neg_delta (f m n : ℚ) (r : ℕ) (τ δ : ℝ) : s6 f m n r τ (-δ) = s6 f m n r τ δ := by
  unfold s6
  split_ifs
  · exact s6c_neg_delta _ _ _ _ _ _
  · rw [s6c_neg_delta]
  · rw [s6c_neg_delta]
  · rw [s6c_neg_delta]

/-- info: 'FormalResearch.Racah.G6even_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms G6even_swap

/-- info: 'FormalResearch.Racah.s6_neg_delta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms s6_neg_delta

end FormalResearch.Racah
