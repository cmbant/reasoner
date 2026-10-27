import Mathlib
import FormalResearch.FrameFree.Helstrom

/-!
# QI-B `thm:finite`: one finite projective orbit suffices

Namespace `FormalResearch.QIB`.  Claim class: **proved** (no hypothesis beyond the stated finiteness of an orbit).

Formalises `thm:finite` of `QI-B/paper/invariant_discrimination_exponents.tex` (label `thm:finite`) for an
**arbitrary group of unitaries** `K = G ≤ U(ι)` acting diagonally on `k` copies (`u ↦ u^{⊗k}`): if at least
one of the two projective `G`-orbits `{u y}`, `{u x}` of unit vectors `x, y ∈ ℂ^ι` is finite, then
`F_G(x,y)^k / 4 ≤ P_e^G(k) ≤ s F_G(x,y)^k` (the upper bound for all large `k`, `s` the number of rays of the
finite orbit), hence `-(1/k) log P_e^G(k) → -log F_G(x,y)` whenever `F_G(x,y) > 0`.

**Definitions.**
* `tp k v = v^{⊗k}` and `tm k u = u^{⊗k}` on the basis `Fin k → ι` (`tm_mulVec_tp`, `tm_mul`, `tm_unitary`).
* `G : Subgroup (Matrix.unitaryGroup ι ℂ)`; `IsInvEff G k E`: `0 ≤ E ≤ 1` and `E` commutes with every `u^{⊗k}`,
  `u ∈ G` (a `G`-invariant test); `PeG G k x y = inf_E err E x^{⊗k} y^{⊗k}` over invariant tests;
  `FG G x y = sup_{u ∈ G} |⟨x|u y⟩|²`.
* `FiniteOrbit G y s b`: the rays of the orbit `{u y : u ∈ G}` are exactly the `s` pairwise non-proportional
  rays `b 0, …, b (s-1)`, each of which is an orbit point.

**Proof, as in the paper.**  Lower bound: `PeG_ge_of_act` (the closest-pair converse `|⟨x|u y⟩|^{2k}/4 ≤ P_e`),
which needs `F_G` to be attained; for a finite orbit it is (`FG_attained`).  Upper bound: the test that accepts
`x` on the orthogonal complement of the support space `span{b_j^{⊗k}}` is `G`-invariant (`suppB_isInv`), never
errs on `y`, and `‖Π x^{⊗k}‖² ≤ 2 Σ_j |⟨b_j,x⟩|^{2k} ≤ 2 s F^k` once the Gram matrix of the `b_j^{⊗k}` is
`⪰ I/2` (`proj_sq_le`: the paper's `‖G_k - I‖ ≤ (s-1) α^k` estimate, done with the cruder constant
`s α^k ≤ 1/2`, which also holds for large `k`).

**Non-vacuity.**
* `exists_finiteOrbit_of_finite`: for a *finite* subgroup `G` and any unit `y`, the orbit hypothesis holds for
  some `(s, b)`.  Hence `thm_finite_group`: for every finite group of unitaries, every unit `x, y` with
  `F_G(x,y) > 0`, `-(1/k) log P_e^G(k) → -log F_G(x,y)`.
* `permOrbit`: the symmetric group `S_d` acting on `ℂ^d` by permutation matrices has the finite orbit
  `{e_j}` (`s = d`) of `y = e_i`; `thm_finite_perm` is the resulting theorem (here `F_G(x, e_i) = max_j |x_j|²`
  by `FG_perm`).

The hypothesis is not satisfiable for the connected group `SU(2)^n` (`SU(2)` fixes no ray of `ℂ²`), which is why
the theorem is formulated for an abstract group of unitaries (finite groups, stabiliser-type groups); the earlier
`SU(2)^n`-specific statements were vacuous and have been removed.

**Cross-references (not re-proved).**  `prop:supportstruct`'s elementary part `R_k ≥ F_C^k` is
`FrameFree/HelstromSupport.lean: FCΘ_pow_le_Rk`; its spectral-radius half is `FrameFree/SupportRate*.lean`.
`prop:orbitideal` (`W_{y,k} = I_k(X_y)^⊥`) is Zariski/Bombieri-pairing algebra and is not formalised; `thm:finite`
does not use it (only the elementary support space `span{(b_j)^{⊗k}}`, which here is `suppB`).

**Notes on the paper's statement.**  `F < 1` is not used by the proof (for `F = 1` both bounds are trivial and the
limit is `0 = -log 1`); `0 < F` is a hypothesis of the limit statement for a general pair.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped ComplexConjugate Matrix BigOperators InnerProductSpace ComplexOrder
open Matrix FormalResearch.FrameFree.NQubit FormalResearch.FrameFree.Helstrom
open Filter

namespace FormalResearch.QIB

/-! ### An abstract projection estimate -/

/-- Projection of `x` onto the span of `s` unit vectors with pairwise overlaps `≤ ε`, `s ε ≤ 1/2`:
`‖Π x‖² ≤ 2 Σ_j |⟨v_j, x⟩|²`. -/
theorem proj_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ℕ} (v : Fin s → EuclideanSpace ℂ ι)
    (hv : ∀ j, ‖v j‖ = 1) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ i j, i ≠ j → ‖⟪v i, v j⟫_ℂ‖ ≤ ε) (hs : (s : ℝ) * ε ≤ 1 / 2)
    (x : EuclideanSpace ℂ ι) :
    ‖(Submodule.span ℂ (Set.range v)).starProjection x‖ ^ 2 ≤ 2 * ∑ j, ‖⟪v j, x⟫_ℂ‖ ^ 2 := by
  set W := Submodule.span ℂ (Set.range v) with hW
  set w := W.starProjection x with hw
  have hwW : w ∈ W := Submodule.starProjection_apply_mem W x
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hwW
  set a : Fin s → ℝ := fun j => ‖c j‖ with ha
  set A : ℝ := ∑ j, a j ^ 2 with hA
  set S : ℝ := ∑ j, ‖⟪v j, x⟫_ℂ‖ ^ 2 with hS
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h0 : ⟪x - w, w⟫_ℂ = 0 := Submodule.starProjection_inner_eq_zero x w hwW
  have hxw : ⟪x, w⟫_ℂ = ⟪w, w⟫_ℂ := by
    have := inner_sub_left x w w (𝕜 := ℂ)
    rw [h0] at this
    exact sub_eq_zero.1 this.symm
  have hww : ⟪w, w⟫_ℂ = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have hwx : ⟪w, x⟫_ℂ = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [← inner_conj_symm, hxw, hww]; simp
  set t : ℝ := ‖w‖ ^ 2 with ht
  have ht0 : 0 ≤ t := sq_nonneg _
  -- upper bound on t
  have hup : t ^ 2 ≤ A * S := by
    have h1 : t = ‖⟪w, x⟫_ℂ‖ := by rw [hwx]; simp [abs_of_nonneg ht0]
    have h2 : ⟪w, x⟫_ℂ = ∑ j, conj (c j) * ⟪v j, x⟫_ℂ := by
      rw [← hc, sum_inner]
      exact Finset.sum_congr rfl fun j _ => by rw [inner_smul_left]
    have h3 : t ≤ ∑ j, a j * ‖⟪v j, x⟫_ℂ‖ := by
      rw [h1, h2]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun j _ => by rw [norm_mul, RCLike.norm_conj]
    have h4 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun j => ‖⟪v j, x⟫_ℂ‖)
    calc t ^ 2 ≤ (∑ j, a j * ‖⟪v j, x⟫_ℂ‖) ^ 2 := pow_le_pow_left₀ ht0 h3 2
      _ ≤ A * S := h4
  -- lower bound on t
  have hlow : A - ε * (s * A) ≤ t := by
    have h1 : ⟪w, w⟫_ℂ = ∑ i, ∑ j, conj (c i) * (c j * ⟪v i, v j⟫_ℂ) := by
      conv_lhs => rw [← hc]
      rw [sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inner_smul_left, inner_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [inner_smul_right]
    have h2 : t = ∑ i, ∑ j, (conj (c i) * (c j * ⟪v i, v j⟫_ℂ)).re := by
      have := congrArg Complex.re (hww.symm.trans h1)
      rw [Complex.ofReal_re, Complex.re_sum] at this
      rw [this]
      exact Finset.sum_congr rfl fun i _ => by rw [Complex.re_sum]
    have h3 : ∀ i j, (if i = j then a i ^ 2 else 0) - ε * (a i * a j)
        ≤ (conj (c i) * (c j * ⟪v i, v j⟫_ℂ)).re := by
      intro i j
      by_cases hij : i = j
      · subst hij
        have hone : ⟪v i, v i⟫_ℂ = 1 := by
          rw [inner_self_eq_norm_sq_to_K, hv i]; simp
        have hi : (if i = i then a i ^ 2 else 0) = a i ^ 2 := by simp
        rw [hone, hi]
        have : (conj (c i) * (c i * 1)).re = a i ^ 2 := by
          rw [mul_one, mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
        rw [this]
        have : 0 ≤ ε * (a i * a i) := by positivity
        linarith
      · have hi : (if i = j then a i ^ 2 else 0) = 0 := by simp [hij]
        rw [hi, zero_sub]
        have hb := hε i j hij
        have h5 : ‖conj (c i) * (c j * ⟪v i, v j⟫_ℂ)‖ ≤ a i * a j * ε := by
          rw [norm_mul, RCLike.norm_conj, norm_mul]
          have : 0 ≤ a i * a j := by positivity
          calc ‖c i‖ * (‖c j‖ * ‖⟪v i, v j⟫_ℂ‖) = a i * a j * ‖⟪v i, v j⟫_ℂ‖ := by
                simp [ha]; ring
            _ ≤ a i * a j * ε := mul_le_mul_of_nonneg_left hb this
        have h6 := (abs_le.1 (Complex.abs_re_le_norm (conj (c i) * (c j * ⟪v i, v j⟫_ℂ)))).1
        linarith
    have h4 : ∑ i, ∑ j, ((if i = j then a i ^ 2 else 0) - ε * (a i * a j))
        = A - ε * (∑ i, a i) ^ 2 := by
      simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      simp only [Finset.mul_sum]
      rfl
    have h5 : (∑ i, a i) ^ 2 ≤ s * A := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
      simpa using this
    have h6 : t ≥ ∑ i, ∑ j, ((if i = j then a i ^ 2 else 0) - ε * (a i * a j)) := by
      rw [h2]
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h3 i j
    rw [h4] at h6
    have := mul_le_mul_of_nonneg_left h5 hε0
    linarith
  have hA2 : A / 2 ≤ t := by
    have : ε * (s * A) ≤ A / 2 := by
      have := mul_le_mul_of_nonneg_right hs hA0
      nlinarith
    linarith
  by_cases ht' : t = 0
  · rw [ht']; linarith
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht')
    have : t * t ≤ t * (2 * S) := by nlinarith
    exact le_of_mul_le_mul_left this htpos


/-! ### Tensor powers and the diagonal action of a unitary group -/

section Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `v^{⊗k}` in the basis `Fin k → ι`. -/
def tp (k : ℕ) (v : ι → ℂ) : (Fin k → ι) → ℂ := fun x => ∏ j, v (x j)

/-- `u^{⊗k}` in the basis `Fin k → ι`. -/
def tm (k : ℕ) (u : Matrix ι ι ℂ) : Matrix (Fin k → ι) (Fin k → ι) ℂ :=
  kron (fun _ : Fin k => u)

theorem tm_mulVec_tp (k : ℕ) (u : Matrix ι ι ℂ) (v : ι → ℂ) :
    tm k u *ᵥ tp k v = tp k (u *ᵥ v) :=
  kron_mulVec_prod (fun _ : Fin k => u) (fun _ => v)

theorem star_tp_dot (k : ℕ) (v w : ι → ℂ) : star (tp k v) ⬝ᵥ tp k w = (star v ⬝ᵥ w) ^ k := by
  refine (star_dot_prod (fun _ : Fin k => v) (fun _ : Fin k => w)).trans ?_
  simp

theorem tp_smul (k : ℕ) (c : ℂ) (v : ι → ℂ) : tp k (c • v) = c ^ k • tp k v := by
  funext i
  simp [tp, Finset.prod_mul_distrib]

theorem tm_mul (k : ℕ) (u v : Matrix ι ι ℂ) : tm k u * tm k v = tm k (u * v) := by
  ext x z
  simp only [Matrix.mul_apply, tm, kron]
  simp_rw [← Finset.prod_mul_distrib]
  rw [sum_prod_pi (fun i b => u (x i) b * v b (z i))]

theorem tm_conjTranspose (k : ℕ) (u : Matrix ι ι ℂ) : (tm k u)ᴴ = tm k uᴴ := by
  ext x y
  simp [tm, kron, Matrix.conjTranspose_apply, star_prod]

theorem tm_unitary (k : ℕ) {u : Matrix ι ι ℂ} (hu : uᴴ * u = 1) : (tm k u)ᴴ * tm k u = 1 :=
  kron_unitary (fun _ : Fin k => u) (fun _ => hu)

theorem star_mulVec_dot_unitary {U : Matrix ι ι ℂ} (hU : Uᴴ * U = 1) (v w : ι → ℂ) :
    star (U *ᵥ v) ⬝ᵥ (U *ᵥ w) = star v ⬝ᵥ w := by
  have := qf_frame (M := (1 : Matrix ι ι ℂ)) hU (by simp) v w
  simpa only [qf_one] using this

theorem dot_star_comm (x y : ι → ℂ) : star x ⬝ᵥ y = conj (star y ⬝ᵥ x) := by
  simp [dotProduct, mul_comm]

theorem dot_act_adj (A : Matrix ι ι ℂ) (x y : ι → ℂ) :
    star x ⬝ᵥ (A *ᵥ y) = star (Aᴴ *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]

theorem unit_smul {c : ℂ} {w : ι → ℂ} (hw : star w ⬝ᵥ w = 1) (h : star (c • w) ⬝ᵥ (c • w) = 1) :
    Complex.normSq c = 1 := by
  rw [star_smul, smul_dotProduct, dotProduct_smul, hw] at h
  have h2 : ((Complex.normSq c : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]; simpa using h
  exact_mod_cast h2

theorem inner_toLp' (v w : ι → ℂ) :
    ⟪WithLp.toLp 2 v, WithLp.toLp 2 w⟫_ℂ = star v ⬝ᵥ w := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

theorem norm_toLp_unit {x : ι → ℂ} (hx : star x ⬝ᵥ x = 1) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ = 1 := by
  have h : ⟪(WithLp.toLp 2 x : EuclideanSpace ℂ ι), WithLp.toLp 2 x⟫_ℂ = 1 := by
    rw [inner_toLp', hx]
  rw [inner_self_eq_norm_sq_to_K] at h
  have h3 : ((‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_one, Complex.ofReal_pow]; exact h
  have h2 := Complex.ofReal_injective h3
  nlinarith [norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℂ ι)]

/-- Two unit vectors that are not proportional have `|⟨φ,ψ⟩|² < 1` (strict Cauchy-Schwarz). -/
theorem normSq_dot_lt_one {φ ψ : ι → ℂ} (hφ : star φ ⬝ᵥ φ = 1) (hψ : star ψ ⬝ᵥ ψ = 1)
    (h : ¬ ∃ c : ℂ, φ = c • ψ) : Complex.normSq (star φ ⬝ᵥ ψ) < 1 := by
  refine lt_of_le_of_ne (normSq_le_one hφ hψ) fun heq => h ?_
  have hn : ‖⟪(WithLp.toLp 2 φ : EuclideanSpace ℂ ι), WithLp.toLp 2 ψ⟫_ℂ‖ =
      ‖(WithLp.toLp 2 φ : EuclideanSpace ℂ ι)‖ * ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ ι)‖ := by
    rw [norm_toLp_unit hφ, norm_toLp_unit hψ, inner_toLp', mul_one]
    have : ‖star φ ⬝ᵥ ψ‖ ^ 2 = 1 := by rw [Complex.sq_norm]; exact heq
    nlinarith [norm_nonneg (star φ ⬝ᵥ ψ)]
  have hφ0 : (WithLp.toLp 2 φ : EuclideanSpace ℂ ι) ≠ 0 := by
    intro h0; have := norm_toLp_unit hφ; rw [h0] at this; simp at this
  have hψ0 : (WithLp.toLp 2 ψ : EuclideanSpace ℂ ι) ≠ 0 := by
    intro h0; have := norm_toLp_unit hψ; rw [h0] at this; simp at this
  obtain ⟨r, hr0, hr⟩ := (norm_inner_eq_norm_iff hφ0 hψ0).1 hn
  refine ⟨r⁻¹, ?_⟩
  have : ψ = r • φ := by
    have := congrArg WithLp.ofLp hr
    simpa using this
  rw [this, smul_smul, inv_mul_cancel₀ hr0, one_smul]

end Setting

/-! ### Invariant tests, the pair error and `F_G` -/

section Orbit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ug_adj_mul (u : Matrix.unitaryGroup ι ℂ) :
    (u : Matrix ι ι ℂ)ᴴ * (u : Matrix ι ι ℂ) = 1 :=
  Matrix.UnitaryGroup.star_mul_self u

theorem unit_act (u : Matrix.unitaryGroup ι ℂ) {y : ι → ℂ} (hy : star y ⬝ᵥ y = 1) :
    star ((u : Matrix ι ι ℂ) *ᵥ y) ⬝ᵥ ((u : Matrix ι ι ℂ) *ᵥ y) = 1 := by
  rw [star_mulVec_dot_unitary (ug_adj_mul u), hy]

/-- A `G`-invariant test on `k` copies: an effect commuting with every `u^{⊗k}`, `u ∈ G`. -/
def IsInvEff (G : Subgroup (Matrix.unitaryGroup ι ℂ)) (k : ℕ)
    (E : Matrix (Fin k → ι) (Fin k → ι) ℂ) : Prop :=
  IsEffect E ∧ ∀ u ∈ G, tm k (u : Matrix ι ι ℂ) * E = E * tm k (u : Matrix ι ι ℂ)

/-- The best equal-prior error of a `G`-invariant test between `x^{⊗k}` and `y^{⊗k}`. -/
noncomputable def PeG (G : Subgroup (Matrix.unitaryGroup ι ℂ)) (k : ℕ) (x y : ι → ℂ) : ℝ :=
  sInf {r | ∃ E, IsInvEff G k E ∧ r = err E (tp k x) (tp k y)}

/-- The overlap `F_G(x,y) = sup_{u ∈ G} |⟨x|u y⟩|²`. -/
noncomputable def FG (G : Subgroup (Matrix.unitaryGroup ι ℂ)) (x y : ι → ℂ) : ℝ :=
  sSup {r | ∃ u ∈ G, r = Complex.normSq (star x ⬝ᵥ ((u : Matrix ι ι ℂ) *ᵥ y))}

variable {G : Subgroup (Matrix.unitaryGroup ι ℂ)}

theorem isInvEff_zero (k : ℕ) : IsInvEff G k 0 :=
  ⟨⟨Matrix.PosSemidef.zero, by simpa using Matrix.PosSemidef.one⟩, fun u _ => by simp⟩

theorem isInvEff_one_sub {k : ℕ} {E : Matrix (Fin k → ι) (Fin k → ι) ℂ} (hE : IsInvEff G k E) :
    IsInvEff G k (1 - E) :=
  ⟨⟨hE.1.2, by simpa using hE.1.1⟩, fun u hu => by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hE.2 u hu]⟩

theorem PeG_bdd (k : ℕ) (x y : ι → ℂ) :
    BddBelow {r | ∃ E, IsInvEff G k E ∧ r = err E (tp k x) (tp k y)} :=
  ⟨0, by rintro r ⟨E, hE, rfl⟩; exact err_nonneg hE.1 _ _⟩

theorem PeG_le_err {k : ℕ} {E : Matrix (Fin k → ι) (Fin k → ι) ℂ} (hE : IsInvEff G k E)
    (x y : ι → ℂ) : PeG G k x y ≤ err E (tp k x) (tp k y) :=
  csInf_le (PeG_bdd k x y) ⟨E, hE, rfl⟩

theorem err_act_right {k : ℕ} {E : Matrix (Fin k → ι) (Fin k → ι) ℂ} (hE : IsInvEff G k E)
    {u : Matrix.unitaryGroup ι ℂ} (hu : u ∈ G) (a b : (Fin k → ι) → ℂ) :
    err E a (tm k (u : Matrix ι ι ℂ) *ᵥ b) = err E a b := by
  have hU := tm_unitary k (ug_adj_mul u)
  have hc : tm k (u : Matrix ι ι ℂ) * (1 - E) = (1 - E) * tm k (u : Matrix ι ι ℂ) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hE.2 u hu]
  unfold err
  rw [qf_frame hU hc]

/-- The closest-pair converse for any unit pair and any `u ∈ G`: `|⟨x|u y⟩|^{2k}/4 ≤ P_e^G(k)`. -/
theorem PeG_ge_of_act {x y : ι → ℂ} (hx : star x ⬝ᵥ x = 1) (hy : star y ⬝ᵥ y = 1)
    {u : Matrix.unitaryGroup ι ℂ} (hu : u ∈ G) (k : ℕ) :
    Complex.normSq (star x ⬝ᵥ ((u : Matrix ι ι ℂ) *ᵥ y)) ^ k / 4 ≤ PeG G k x y := by
  refine le_csInf ⟨_, 0, isInvEff_zero k, rfl⟩ ?_
  rintro r ⟨E, hE, rfl⟩
  rw [← err_act_right hE hu, tm_mulVec_tp]
  have h := quarter_le_err hE.1 (a := tp k x) (b := tp k ((u : Matrix ι ι ℂ) *ᵥ y))
    (by rw [star_tp_dot, hx, one_pow]) (by rw [star_tp_dot, unit_act u hy, one_pow])
  rw [star_tp_dot, map_pow] at h
  exact h

theorem err_one_sub {κ : Type*} [Fintype κ] [DecidableEq κ] (E : Matrix κ κ ℂ) (a b : κ → ℂ) :
    err (1 - E) b a = err E a b := by
  unfold err
  rw [sub_sub_cancel]
  ring

theorem PeG_le_swap (k : ℕ) (x y : ι → ℂ) : PeG G k x y ≤ PeG G k y x := by
  refine le_csInf ⟨_, 0, isInvEff_zero k, rfl⟩ ?_
  rintro r ⟨E, hE, rfl⟩
  have := PeG_le_err (isInvEff_one_sub hE) x y
  rwa [err_one_sub] at this

/-- Swapping the two hypotheses does not change the invariant error (replace `E` by `1 - E`). -/
theorem PeG_comm (k : ℕ) (x y : ι → ℂ) : PeG G k x y = PeG G k y x :=
  le_antisymm (PeG_le_swap k x y) (PeG_le_swap k y x)

theorem FG_bdd {x y : ι → ℂ} (hx : star x ⬝ᵥ x = 1) (hy : star y ⬝ᵥ y = 1) :
    BddAbove {r | ∃ u ∈ G, r = Complex.normSq (star x ⬝ᵥ ((u : Matrix ι ι ℂ) *ᵥ y))} :=
  ⟨1, by rintro r ⟨u, hu, rfl⟩; exact normSq_le_one hx (unit_act u hy)⟩

theorem le_FG {x y : ι → ℂ} (hx : star x ⬝ᵥ x = 1) (hy : star y ⬝ᵥ y = 1)
    {u : Matrix.unitaryGroup ι ℂ} (hu : u ∈ G) :
    Complex.normSq (star x ⬝ᵥ ((u : Matrix ι ι ℂ) *ᵥ y)) ≤ FG G x y :=
  le_csSup (FG_bdd hx hy) ⟨u, hu, rfl⟩

theorem FG_le_swap {x y : ι → ℂ} (hx : star x ⬝ᵥ x = 1) (hy : star y ⬝ᵥ y = 1) :
    FG G x y ≤ FG G y x := by
  refine csSup_le ⟨_, 1, G.one_mem, rfl⟩ ?_
  rintro r ⟨u, hu, rfl⟩
  have h := le_FG hy hx (G.inv_mem hu)
  refine le_trans (le_of_eq ?_) h
  rw [dot_act_adj, Matrix.UnitaryGroup.inv_val, dot_star_comm y, Complex.normSq_conj]
  rfl

theorem FG_comm {x y : ι → ℂ} (hx : star x ⬝ᵥ x = 1) (hy : star y ⬝ᵥ y = 1) :
    FG G x y = FG G y x :=
  le_antisymm (FG_le_swap hx hy) (FG_le_swap hy hx)

/-! ### Finite projective orbits -/

/-- `b 0, …, b (s-1)` are the `s` distinct rays of the orbit `{u y : u ∈ G}`: each is an orbit point, every
orbit point is proportional to one of them, and they are pairwise non-proportional. -/
structure FiniteOrbit (G : Subgroup (Matrix.unitaryGroup ι ℂ)) (y : ι → ℂ) (s : ℕ)
    (b : Fin s → ι → ℂ) : Prop where
  mem : ∀ j, ∃ u ∈ G, b j = (u : Matrix ι ι ℂ) *ᵥ y
  cover : ∀ u ∈ G, ∃ j, ∃ c : ℂ, (u : Matrix ι ι ℂ) *ᵥ y = c • b j
  sep : ∀ i j, i ≠ j → ¬ ∃ c : ℂ, b i = c • b j

namespace FiniteOrbit

variable {y : ι → ℂ} {s : ℕ} {b : Fin s → ι → ℂ}

theorem pos (hb : FiniteOrbit G y s b) : 0 < s := by
  obtain ⟨j, _⟩ := hb.cover 1 G.one_mem
  exact Fin.pos j

theorem unit_b (hb : FiniteOrbit G y s b) (hy : star y ⬝ᵥ y = 1) (j : Fin s) :
    star (b j) ⬝ᵥ b j = 1 := by
  obtain ⟨v, _, h⟩ := hb.mem j
  rw [h]; exact unit_act v hy

theorem sep_lt (hb : FiniteOrbit G y s b) (hy : star y ⬝ᵥ y = 1) (i j : Fin s) (hij : i ≠ j) :
    Complex.normSq (star (b i) ⬝ᵥ b j) < 1 :=
  normSq_dot_lt_one (hb.unit_b hy i) (hb.unit_b hy j) (hb.sep i j hij)

/-- The set of `s` rays is closed under the group action. -/
theorem closed (hb : FiniteOrbit G y s b) {u : Matrix.unitaryGroup ι ℂ} (hu : u ∈ G) (j : Fin s) :
    ∃ i, ∃ c : ℂ, (u : Matrix ι ι ℂ) *ᵥ b j = c • b i := by
  obtain ⟨v, hv, hbj⟩ := hb.mem j
  obtain ⟨i, c, hc⟩ := hb.cover (u * v) (G.mul_mem hu hv)
  refine ⟨i, c, ?_⟩
  rw [hbj, Matrix.mulVec_mulVec]
  exact hc

end FiniteOrbit

/-- If the orbit of `y` is finite, `F_G(x,y)` is attained (at an orbit point). -/
theorem FG_attained {x y : ι → ℂ} {s : ℕ} {b : Fin s → ι → ℂ} (hx : star x ⬝ᵥ x = 1)
    (hy : star y ⬝ᵥ y = 1) (hb : FiniteOrbit G y s b) :
    ∃ u ∈ G, FG G x y = Complex.normSq (star x ⬝ᵥ ((u : Matrix ι ι ℂ) *ᵥ y)) := by
  have : Nonempty (Fin s) := ⟨⟨0, hb.pos⟩⟩
  obtain ⟨j0, hj0⟩ := Finite.exists_max (fun j : Fin s => Complex.normSq (star x ⬝ᵥ b j))
  obtain ⟨u0, hu0, hb0⟩ := hb.mem j0
  refine ⟨u0, hu0, le_antisymm ?_ (le_FG hx hy hu0)⟩
  refine csSup_le ⟨_, 1, G.one_mem, rfl⟩ ?_
  rintro r ⟨u, hu, rfl⟩
  obtain ⟨j, c, hc⟩ := hb.cover u hu
  have hc1 : Complex.normSq c = 1 := unit_smul (hb.unit_b hy j) (hc ▸ unit_act u hy)
  rw [hc, dotProduct_smul, smul_eq_mul, Complex.normSq_mul, hc1, one_mul, ← hb0]
  exact hj0 j

/-- **Lower bound** (all `k`): `F_G(x,y)^k / 4 ≤ P_e^G(k)` for a finite orbit. -/
theorem PeG_ge_of_finiteOrbit {x y : ι → ℂ} {s : ℕ} {b : Fin s → ι → ℂ} (hx : star x ⬝ᵥ x = 1)
    (hy : star y ⬝ᵥ y = 1) (hb : FiniteOrbit G y s b) (k : ℕ) :
    FG G x y ^ k / 4 ≤ PeG G k x y := by
  obtain ⟨u, hu, hF⟩ := FG_attained hx hy hb
  rw [hF]
  exact PeG_ge_of_act hx hy hu k

/-! ### The support test -/

/-- The `k`-th tensor powers of the rays `b j`, as vectors. -/
def vecs {s : ℕ} (k : ℕ) (b : Fin s → ι → ℂ) : Fin s → EuclideanSpace ℂ (Fin k → ι) :=
  fun j => WithLp.toLp 2 (tp k (b j))

/-- The support space `span{b_j^{⊗k}}` of the finite orbit. -/
def suppB {s : ℕ} (k : ℕ) (b : Fin s → ι → ℂ) : Submodule ℂ (EuclideanSpace ℂ (Fin k → ι)) :=
  Submodule.span ℂ (Set.range (vecs k b))

theorem suppB_invariant {y : ι → ℂ} {s : ℕ} {b : Fin s → ι → ℂ} (hb : FiniteOrbit G y s b) (k : ℕ)
    {u : Matrix.unitaryGroup ι ℂ} (hu : u ∈ G) :
    ∀ v : (Fin k → ι) → ℂ, WithLp.toLp 2 v ∈ suppB k b →
      WithLp.toLp 2 (tm k (u : Matrix ι ι ℂ) *ᵥ v) ∈ suppB k b := by
  have key : ∀ x ∈ suppB k b,
      WithLp.toLp 2 (tm k (u : Matrix ι ι ℂ) *ᵥ WithLp.ofLp x) ∈ suppB k b := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      obtain ⟨i, c, hc⟩ := hb.closed hu j
      have h : tm k (u : Matrix ι ι ℂ) *ᵥ tp k (b j) = c ^ k • tp k (b i) := by
        rw [tm_mulVec_tp, hc, tp_smul]
      have e : WithLp.ofLp (vecs k b j) = tp k (b j) := rfl
      have hm : c ^ k • vecs k b i ∈ suppB k b :=
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      rw [e, h]
      exact hm
    | zero => simp
    | add x y _ _ hx hy =>
      have := Submodule.add_mem _ hx hy
      simpa [Matrix.mulVec_add] using this
    | smul a x _ hx =>
      have := Submodule.smul_mem _ a hx
      simpa [Matrix.mulVec_smul] using this
  intro v hv
  simpa using key _ hv

/-- The orthogonal projector onto the support space is a `G`-invariant test. -/
theorem suppB_isInv {y : ι → ℂ} {s : ℕ} {b : Fin s → ι → ℂ} (hb : FiniteOrbit G y s b) (k : ℕ) :
    IsInvEff G k (projMat (suppB k b)) := by
  refine ⟨projMat_isEffect _, fun u hu => ?_⟩
  refine projMat_commute _ (fun v hv => ?_) (fun v hv => ?_)
  · exact suppB_invariant hb k hu v hv
  · rw [tm_conjTranspose]
    have := suppB_invariant hb k (G.inv_mem hu) v hv
    rw [Matrix.UnitaryGroup.inv_val] at this
    exact this

/-- The support test never errs on `y`, so `P_e(k) ≤ ½ ‖Π x^{⊗k}‖²`. -/
theorem PeG_le_half_proj {x y : ι → ℂ} {s : ℕ} {b : Fin s → ι → ℂ} (hb : FiniteOrbit G y s b)
    (k : ℕ) :
    PeG G k x y ≤ ‖(suppB k b).starProjection (WithLp.toLp 2 (tp k x))‖ ^ 2 / 2 := by
  refine (PeG_le_err (suppB_isInv hb k) x y).trans (le_of_eq ?_)
  have hy : WithLp.toLp 2 (tp k y) ∈ suppB k b := by
    obtain ⟨j, c, hc⟩ := hb.cover 1 G.one_mem
    have hc' : y = c • b j := by simpa using hc
    rw [hc', tp_smul]
    have hm : c ^ k • vecs k b j ∈ suppB k b :=
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    exact hm
  unfold err
  rw [qf_one_sub_projMat_of_mem _ hy, qf_projMat_self]
  simp

/-- **Upper bound** (all large `k`): `P_e(k) ≤ s F_G(x,y)^k` when the orbit of `y` has `s` rays. -/
theorem PeG_eventually_le {x y : ι → ℂ} {s : ℕ} {b : Fin s → ι → ℂ} (hx : star x ⬝ᵥ x = 1)
    (hy : star y ⬝ᵥ y = 1) (hb : FiniteOrbit G y s b) :
    ∀ᶠ k : ℕ in atTop, PeG G k x y ≤ s * FG G x y ^ k := by
  classical
  -- a uniform separation constant α < 1
  obtain ⟨α, hα0, hα1, hα⟩ : ∃ α : ℝ, 0 ≤ α ∧ α < 1 ∧
      ∀ i j, i ≠ j → ‖star (b i) ⬝ᵥ b j‖ ≤ α := by
    have hne : Nonempty (Fin s × Fin s) := ⟨(⟨0, hb.pos⟩, ⟨0, hb.pos⟩)⟩
    let f : Fin s × Fin s → ℝ := fun p => if p.1 = p.2 then 0 else ‖star (b p.1) ⬝ᵥ b p.2‖
    have hf0 : ∀ p, 0 ≤ f p := fun p => by
      by_cases h : p.1 = p.2
      · simp [f, h]
      · simp [f, h]
    have hf1 : ∀ p, f p < 1 := by
      intro p
      by_cases h : p.1 = p.2
      · simp [f, h]
      · have h1 := hb.sep_lt hy p.1 p.2 h
        rw [Complex.normSq_eq_norm_sq] at h1
        have e : f p = ‖star (b p.1) ⬝ᵥ b p.2‖ := by simp [f, h]
        rw [e]
        rcases lt_or_ge ‖star (b p.1) ⬝ᵥ b p.2‖ 1 with h2 | h2
        · exact h2
        · nlinarith [norm_nonneg (star (b p.1) ⬝ᵥ b p.2)]
    obtain ⟨p0, hp0⟩ := Finite.exists_max f
    refine ⟨f p0, hf0 p0, hf1 p0, fun i j hij => ?_⟩
    have e : f (i, j) = ‖star (b i) ⬝ᵥ b j‖ := by simp [f, hij]
    rw [← e]
    exact hp0 (i, j)
  have hlim : Tendsto (fun k : ℕ => (s : ℝ) * α ^ k) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1).const_mul (s : ℝ)
  filter_upwards [hlim.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with k hk
  have hk' : (s : ℝ) * α ^ k ≤ 1 / 2 := hk
  have hvip : ∀ i j, ⟪vecs k b i, vecs k b j⟫_ℂ = (star (b i) ⬝ᵥ b j) ^ k := by
    intro i j
    simp only [vecs]
    rw [inner_toLp', star_tp_dot]
  have hv1 : ∀ j, ‖vecs k b j‖ = 1 := by
    intro j
    exact norm_toLp_unit (by rw [star_tp_dot, hb.unit_b hy j, one_pow])
  have hε : ∀ i j, i ≠ j → ‖⟪vecs k b i, vecs k b j⟫_ℂ‖ ≤ α ^ k := by
    intro i j hij
    rw [hvip, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hα i j hij) k
  have hproj := proj_sq_le (vecs k b) hv1 (pow_nonneg hα0 k) hε hk'
    (WithLp.toLp 2 (tp k x))
  have hterm : ∀ j, ‖⟪vecs k b j, (WithLp.toLp 2 (tp k x) : EuclideanSpace ℂ (Fin k → ι))⟫_ℂ‖ ^ 2
      ≤ FG G x y ^ k := by
    intro j
    have e : ⟪vecs k b j, (WithLp.toLp 2 (tp k x) : EuclideanSpace ℂ (Fin k → ι))⟫_ℂ
        = (star (b j) ⬝ᵥ x) ^ k := by
      simp only [vecs]
      rw [inner_toLp', star_tp_dot]
    rw [e, norm_pow, ← pow_mul, mul_comm, pow_mul, ← Complex.normSq_eq_norm_sq,
      dot_star_comm (b j) x, Complex.normSq_conj]
    obtain ⟨u, hu, hbj⟩ := hb.mem j
    refine pow_le_pow_left₀ (Complex.normSq_nonneg _) ?_ k
    rw [hbj]
    exact le_FG hx hy hu
  calc PeG G k x y
      ≤ ‖(suppB k b).starProjection (WithLp.toLp 2 (tp k x))‖ ^ 2 / 2 := PeG_le_half_proj hb k
    _ ≤ (2 * ∑ j, ‖⟪vecs k b j, (WithLp.toLp 2 (tp k x) : EuclideanSpace ℂ (Fin k → ι))⟫_ℂ‖ ^ 2) / 2 := by
        have : ‖(suppB k b).starProjection (WithLp.toLp 2 (tp k x))‖ ^ 2 ≤
            2 * ∑ j, ‖⟪vecs k b j, (WithLp.toLp 2 (tp k x) : EuclideanSpace ℂ (Fin k → ι))⟫_ℂ‖ ^ 2 :=
          hproj
        linarith
    _ = ∑ j, ‖⟪vecs k b j, (WithLp.toLp 2 (tp k x) : EuclideanSpace ℂ (Fin k → ι))⟫_ℂ‖ ^ 2 := by ring
    _ ≤ ∑ j : Fin s, FG G x y ^ k := Finset.sum_le_sum fun j _ => hterm j
    _ = s * FG G x y ^ k := by simp

/-! ### The exponent -/

/-- From `F^k/4 ≤ P_k` and eventually `P_k ≤ s F^k` (with `F, s > 0`) to
`-(1/k) log P_k → -log F`. -/
theorem tendsto_of_bounds {F : ℝ} {s : ℕ} {P : ℕ → ℝ} (hF : 0 < F) (hs : 0 < s)
    (hlow : ∀ k, F ^ k / 4 ≤ P k) (hup : ∀ᶠ k : ℕ in atTop, P k ≤ s * F ^ k) :
    Tendsto (fun k : ℕ => -(1 / (k : ℝ)) * Real.log (P k)) atTop (nhds (-Real.log F)) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hlim1 : Tendsto (fun k : ℕ => -Real.log F + Real.log 4 / k) atTop (nhds (-Real.log F)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (Real.log 4))
  have hlim2 : Tendsto (fun k : ℕ => -Real.log F - Real.log s / k) atTop (nhds (-Real.log F)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (Real.log s))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim2 hlim1 ?_ ?_
  · filter_upwards [hup, eventually_ge_atTop 1] with k hk hk1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    have hPpos : 0 < P k := lt_of_lt_of_le (by positivity) (hlow k)
    have h := Real.log_le_log hPpos hk
    rw [Real.log_mul hs'.ne' (by positivity), Real.log_pow] at h
    have h2 : -(1 / (k : ℝ)) * (Real.log s + k * Real.log F) ≤ -(1 / (k : ℝ)) * Real.log (P k) :=
      mul_le_mul_of_nonpos_left h (by have : 0 < 1 / (k : ℝ) := by positivity
                                      linarith)
    refine le_trans (le_of_eq ?_) h2
    field_simp
    ring
  · filter_upwards [eventually_ge_atTop 1] with k hk1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    have hPpos : 0 < P k := lt_of_lt_of_le (by positivity) (hlow k)
    have h := Real.log_le_log (by positivity) (hlow k)
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at h
    have h2 : -(1 / (k : ℝ)) * Real.log (P k) ≤ -(1 / (k : ℝ)) * (k * Real.log F - Real.log 4) :=
      mul_le_mul_of_nonpos_left h (by have : 0 < 1 / (k : ℝ) := by positivity
                                      linarith)
    refine h2.trans (le_of_eq ?_)
    field_simp
    ring


/-- **`thm:finite`, quantitative form.**  If the `G`-orbit of `y` or of `x` has `s` rays `b`, then for
unit `x, y`: `F^k/4 ≤ P_e^G(k)` for every `k` and `P_e^G(k) ≤ s F^k` for all large `k`
(`F = F_G(x,y)`). -/
theorem thm_finite_bounds {x y : ι → ℂ} (hx : star x ⬝ᵥ x = 1) (hy : star y ⬝ᵥ y = 1) {s : ℕ}
    {b : Fin s → ι → ℂ} (hb : FiniteOrbit G y s b ∨ FiniteOrbit G x s b) :
    (∀ k : ℕ, FG G x y ^ k / 4 ≤ PeG G k x y) ∧
      ∀ᶠ k : ℕ in atTop, PeG G k x y ≤ s * FG G x y ^ k := by
  rcases hb with hb | hb
  · exact ⟨PeG_ge_of_finiteOrbit hx hy hb, PeG_eventually_le hx hy hb⟩
  · refine ⟨fun k => ?_, ?_⟩
    · rw [PeG_comm, FG_comm hx hy]
      exact PeG_ge_of_finiteOrbit hy hx hb k
    · filter_upwards [PeG_eventually_le (G := G) (x := y) hy hx hb] with k hk
      rwa [PeG_comm, FG_comm hx hy]

/-- **`thm:finite`** (QI-B), for an arbitrary group of unitaries `G`.  For unit `x, y`, if the projective
`G`-orbit of `y` or of `x` is finite (`s` rays) and `0 < F_G(x,y)`, then
`ξ_inv(x,y) = lim_k -(1/k) log P_e^G(k) = -log F_G(x,y) = C_G(x,y)`; the hypothesis `F_G < 1` of the paper is
not needed. -/
theorem thm_finite {x y : ι → ℂ} (hx : star x ⬝ᵥ x = 1) (hy : star y ⬝ᵥ y = 1)
    (hF : 0 < FG G x y) {s : ℕ} {b : Fin s → ι → ℂ}
    (hb : FiniteOrbit G y s b ∨ FiniteOrbit G x s b) :
    Tendsto (fun k : ℕ => -(1 / (k : ℝ)) * Real.log (PeG G k x y)) atTop
      (nhds (-Real.log (FG G x y))) := by
  have hs : 0 < s := by rcases hb with hb | hb <;> exact hb.pos
  obtain ⟨hlow, hup⟩ := thm_finite_bounds hx hy hb
  exact tendsto_of_bounds hF hs hlow hup

/-! ### Non-vacuity: finite groups and permutation groups -/

/-- For a finite group `G` the orbit hypothesis holds for every unit `y`. -/
theorem exists_finiteOrbit_of_finite [Finite G] {y : ι → ℂ} (hy : star y ⬝ᵥ y = 1) :
    ∃ (s : ℕ) (b : Fin s → ι → ℂ), FiniteOrbit G y s b := by
  classical
  let act : G → ι → ℂ := fun u => ((u : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) *ᵥ y
  have hne : ∀ u v : G, ∀ c : ℂ, act u = c • act v → c ≠ 0 := by
    intro u v c h hc
    have h1 := unit_act (u : Matrix.unitaryGroup ι ℂ) hy
    change star (act u) ⬝ᵥ act u = 1 at h1
    rw [h, hc] at h1
    simp at h1
  let r : Setoid G :=
    { r := fun u v => ∃ c : ℂ, act u = c • act v
      iseqv :=
        { refl := fun u => ⟨1, by simp⟩
          symm := by
            rintro u v ⟨c, hc⟩
            refine ⟨c⁻¹, ?_⟩
            rw [hc, smul_smul, inv_mul_cancel₀ (hne u v c hc), one_smul]
          trans := by
            rintro u v w ⟨c, hc⟩ ⟨d, hd⟩
            exact ⟨c * d, by rw [hc, hd, smul_smul]⟩ } }
  have : Finite (Quotient r) := Finite.of_surjective (Quotient.mk r) Quotient.mk_surjective
  let e : Quotient r ≃ Fin (Nat.card (Quotient r)) := Finite.equivFin _
  refine ⟨Nat.card (Quotient r), fun j => act (Quotient.out (e.symm j)), ?_, ?_, ?_⟩
  · intro j
    exact ⟨_, (Quotient.out (e.symm j)).2, rfl⟩
  · intro u hu
    refine ⟨e (Quotient.mk r ⟨u, hu⟩), ?_⟩
    have h : r (⟨u, hu⟩ : G) (Quotient.out (Quotient.mk r ⟨u, hu⟩)) :=
      Quotient.exact (Quotient.out_eq (Quotient.mk r (⟨u, hu⟩ : G))).symm
    simp only [Equiv.symm_apply_apply]
    exact h
  · intro i j hij ⟨c, hc⟩
    apply hij
    have : Quotient.mk r (Quotient.out (e.symm i)) = Quotient.mk r (Quotient.out (e.symm j)) :=
      Quotient.sound ⟨c, hc⟩
    rw [Quotient.out_eq, Quotient.out_eq] at this
    exact e.symm.injective this

/-- **`thm:finite` for every finite group of unitaries**: for unit `x, y` with `F_G(x,y) > 0`,
`-(1/k) log P_e^G(k) → -log F_G(x,y)`, and `F_G^k/4 ≤ P_e^G(k) ≤ s F_G^k` eventually, `s` the number of rays. -/
theorem thm_finite_group [Finite G] {x y : ι → ℂ} (hx : star x ⬝ᵥ x = 1) (hy : star y ⬝ᵥ y = 1)
    (hF : 0 < FG G x y) :
    (∃ s : ℕ, 0 < s ∧ (∀ k : ℕ, FG G x y ^ k / 4 ≤ PeG G k x y) ∧
        ∀ᶠ k : ℕ in atTop, PeG G k x y ≤ s * FG G x y ^ k) ∧
      Tendsto (fun k : ℕ => -(1 / (k : ℝ)) * Real.log (PeG G k x y)) atTop
        (nhds (-Real.log (FG G x y))) := by
  obtain ⟨s, b, hb⟩ := exists_finiteOrbit_of_finite (G := G) hy
  exact ⟨⟨s, hb.pos, (thm_finite_bounds hx hy (Or.inl hb)).1,
    (thm_finite_bounds hx hy (Or.inl hb)).2⟩, thm_finite hx hy hF (Or.inl hb)⟩

end Orbit

/-! ### The symmetric group acting on `ℂ^d` by permutation matrices -/

section Perm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The permutation matrices as a homomorphism into the unitary group (`σ ↦ P_{σ⁻¹}`, so that
`permU σ e_i = e_{σ i}`). -/
noncomputable def permU : Equiv.Perm ι →* Matrix.unitaryGroup ι ℂ where
  toFun σ := ⟨Equiv.Perm.permMatrix ℂ σ⁻¹, by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
      inv_inv, ← Matrix.permMatrix_mul]
    simp⟩
  map_one' := Subtype.ext (by simp)
  map_mul' σ τ := Subtype.ext (by
    show Equiv.Perm.permMatrix ℂ (σ * τ)⁻¹ = Equiv.Perm.permMatrix ℂ σ⁻¹ * Equiv.Perm.permMatrix ℂ τ⁻¹
    rw [_root_.mul_inv_rev, Matrix.permMatrix_mul])

/-- The group `S_ι` of permutation matrices. -/
noncomputable def permGroup (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Subgroup (Matrix.unitaryGroup ι ℂ) := (permU (ι := ι)).range

theorem permU_mulVec_single (σ : Equiv.Perm ι) (i : ι) :
    ((permU σ : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) *ᵥ Pi.single i (1 : ℂ) =
      Pi.single (σ i) (1 : ℂ) := by
  show Equiv.Perm.permMatrix ℂ σ⁻¹ *ᵥ Pi.single i (1 : ℂ) = _
  rw [Matrix.permMatrix_mulVec]
  funext j
  simp only [Function.comp_apply, Pi.single_apply, Equiv.Perm.inv_eq_iff_eq]

/-- The orbit of the basis vector `e_i` under the permutation group is the `d = |ι|` rays `e_j`. -/
theorem permOrbit (i : ι) :
    FiniteOrbit (permGroup ι) (Pi.single i (1 : ℂ)) (Fintype.card ι)
      (fun j => Pi.single ((Fintype.equivFin ι).symm j) (1 : ℂ)) := by
  refine ⟨fun j => ?_, fun u hu => ?_, fun a c hac ⟨z, hz⟩ => ?_⟩
  · refine ⟨permU (Equiv.swap i ((Fintype.equivFin ι).symm j)), ⟨_, rfl⟩, ?_⟩
    rw [permU_mulVec_single, Equiv.swap_apply_left]
  · obtain ⟨σ, rfl⟩ := hu
    refine ⟨Fintype.equivFin ι (σ i), 1, ?_⟩
    rw [permU_mulVec_single]
    simp
  · have := congrFun hz ((Fintype.equivFin ι).symm a)
    have hne : (Fintype.equivFin ι).symm c ≠ (Fintype.equivFin ι).symm a := by
      intro h; exact hac (((Fintype.equivFin ι).symm.injective h).symm)
    simp [hne.symm] at this

theorem FG_perm_ge (x : ι → ℂ) (hx : star x ⬝ᵥ x = 1) (i j : ι) :
    Complex.normSq (x j) ≤ FG (permGroup ι) x (Pi.single i (1 : ℂ)) := by
  have hy : star (Pi.single i (1 : ℂ) : ι → ℂ) ⬝ᵥ Pi.single i (1 : ℂ) = 1 := by simp
  have := le_FG (G := permGroup ι) hx hy (u := permU (Equiv.swap i j)) ⟨_, rfl⟩
  rw [permU_mulVec_single, Equiv.swap_apply_left] at this
  simpa [dotProduct_single] using this

/-- **`thm:finite` for the symmetric group** `S_d ≤ U(d)` acting on `ℂ^d` by permutation matrices, `y = e_i`:
for every unit `x`, `F^k/4 ≤ P_e^{S_d}(k) ≤ d F^k` (large `k`) with `F = F_{S_d}(x, e_i) ≥ max_j |x_j|² > 0`,
and `-(1/k) log P_e^{S_d}(k) → -log F`. -/
theorem thm_finite_perm (x : ι → ℂ) (hx : star x ⬝ᵥ x = 1) (i : ι) :
    (∀ k : ℕ, FG (permGroup ι) x (Pi.single i (1 : ℂ)) ^ k / 4 ≤
        PeG (permGroup ι) k x (Pi.single i (1 : ℂ))) ∧
      (∀ᶠ k : ℕ in atTop, PeG (permGroup ι) k x (Pi.single i (1 : ℂ)) ≤
        Fintype.card ι * FG (permGroup ι) x (Pi.single i (1 : ℂ)) ^ k) ∧
      Tendsto (fun k : ℕ => -(1 / (k : ℝ)) * Real.log (PeG (permGroup ι) k x (Pi.single i (1 : ℂ))))
        atTop (nhds (-Real.log (FG (permGroup ι) x (Pi.single i (1 : ℂ))))) := by
  have hy : star (Pi.single i (1 : ℂ) : ι → ℂ) ⬝ᵥ Pi.single i (1 : ℂ) = 1 := by simp
  have hpos : 0 < FG (permGroup ι) x (Pi.single i (1 : ℂ)) := by
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : x = 0 := funext hcon
      rw [this] at hx
      simp at hx
    exact lt_of_lt_of_le (Complex.normSq_pos.2 hj) (FG_perm_ge x hx i j)
  have hb := permOrbit i
  obtain ⟨hlow, hup⟩ := thm_finite_bounds hx hy (Or.inl hb)
  exact ⟨hlow, hup, thm_finite hx hy hpos (Or.inl hb)⟩

end Perm

end FormalResearch.QIB
