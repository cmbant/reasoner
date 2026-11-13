module

public import FormalResearch.Racah.P2AnalyticCarrier6jShape

/-!
# Polynomiality of the `6j` carrier (Weyl P2, `lem:sqrtfreecarrier`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `lem:sqrtfreecarrier`: "`P̃_f` is a polynomial of
degree `f - f_0` in `τ = (1-x)/2` whose coefficients are polynomials in `A⁻²`, `B⁻²` and `(AB)⁻¹`",
"their leading coefficients are constants", and the symmetry under `A ↔ B`.

The carrier is *defined* as an element `ptPoly m n d` of `ℝ[u,v,w][τ]`
(`CarrierRing = Polynomial (MvPolynomial (Fin 3) ℝ)`), so polynomiality in `(τ,u,v,w)` is built in
(`ptilde6` is the evaluation); this file proves the degree statements, the explicit coefficient-array
form, the symmetry `u ↔ v`, and polynomiality in the single dilation variable `t` at fixed shape.

* `ptPoly_natDegree_le`: `deg_τ P̃_{m+d} ≤ d`.
* `ptPoly_coeff_top`: the coefficient of `τ^d` is the constant `kLead m n d`
  (`P̃`'s leading coefficient, `eq:WignerJacobiMonic`'s `k_{6j}` up to the monic normalisation).
* `ptPoly_natDegree`: exact degree `d` when the labels are physical.
* `ptilde6_eq_sum`: `P̃ = ∑_{i ≤ d} (coefficient array)_i τ^i` with `(coefficient array)_i` the
  evaluation of the polynomial `(ptPoly m n d).coeff i ∈ ℝ[u,v,w]`.
* `ptilde6_symm_uv`: `P̃(τ; u, v, w) = P̃(τ; v, u, w)`.
* `ptilde6_shape_poly`: for fixed `(τ, α, β)`, `t ↦ P̃(τ; t/α², t/β², t/(αβ))` is a polynomial in `t`.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner FormalResearch.Racah.SixJ

lemma natDegree_cc (r : ℝ) : (cc r).natDegree = 0 := by
  simp [cc]

lemma natDegree_diagP_le (m n : ℚ) (f : ℝ) : (diagP m n f).natDegree ≤ 1 := by
  unfold diagP cc wVar
  compute_degree

lemma natDegree_eta2P (f : ℝ) : (eta2P f).natDegree = 0 := by
  have : eta2P f = Polynomial.C ((1 - MvPolynomial.C (f ^ 2 / 4) * MvPolynomial.X 0) *
      (1 - MvPolynomial.C (f ^ 2 / 4) * MvPolynomial.X 1)) := by
    simp [eta2P, cc, uVar, vVar]
  rw [this]; exact Polynomial.natDegree_C _

lemma coeff_one_diagP (m n : ℚ) (f : ℝ) :
    (diagP m n f).coeff 1 = MvPolynomial.C (-2 * ((2 * f + 1) * f * (f + 1))) := by
  have : diagP m n f = Polynomial.C (MvPolynomial.C ((2 * f + 1) * f * (f + 1))) *
      (1 - Polynomial.C (MvPolynomial.C 2) * Polynomial.X -
        Polynomial.C (MvPolynomial.C ((2 * f * (f + 1) + 1 - (m : ℝ) ^ 2 - (n : ℝ) ^ 2) / 8)) *
          Polynomial.C (MvPolynomial.X 2)) -
      Polynomial.C (MvPolynomial.C ((2 * f + 1) * m * n)) := rfl
  rw [this]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_one,
    Polynomial.coeff_X_one, Polynomial.coeff_C]
  simp
  ring

lemma natDegree_pt0 (m n : ℚ) : (pt0 m n).natDegree = 0 := natDegree_cc _

lemma natDegree_pt1_le (m n : ℚ) : (pt1 m n).natDegree ≤ 1 := by
  unfold pt1
  split_ifs
  · unfold cc wVar
    compute_degree
  · calc (cc (1 / ((m : ℝ) * rootR m n ((m : ℝ) + 1))) * diagP m n (m : ℝ) * pt0 m n).natDegree
        ≤ (cc (1 / ((m : ℝ) * rootR m n ((m : ℝ) + 1))) * diagP m n (m : ℝ)).natDegree +
            (pt0 m n).natDegree := Polynomial.natDegree_mul_le
      _ ≤ ((cc (1 / ((m : ℝ) * rootR m n ((m : ℝ) + 1)))).natDegree +
            (diagP m n (m : ℝ)).natDegree) + (pt0 m n).natDegree :=
          Nat.add_le_add_right Polynomial.natDegree_mul_le _
      _ ≤ 1 := by
          rw [natDegree_cc, natDegree_pt0]
          have := natDegree_diagP_le m n (m : ℝ)
          omega

/-- `deg_τ P̃_{m+d} ≤ d` (`lem:sqrtfreecarrier`: polynomial of degree `f - f_0` in `τ`). -/
theorem ptPoly_natDegree_le (m n : ℚ) (d : ℕ) : (ptPoly m n d).natDegree ≤ d := by
  have key : ∀ d : ℕ, (ptPoly m n d).natDegree ≤ d ∧ (ptPoly m n (d + 1)).natDegree ≤ d + 1 := by
    intro d
    induction d with
    | zero => exact ⟨by simp [ptPoly, natDegree_pt0], by simpa [ptPoly] using natDegree_pt1_le m n⟩
    | succ d ih =>
      refine ⟨ih.2, ?_⟩
      show (ptPoly m n (d + 2)).natDegree ≤ d + 2
      rw [ptPoly]
      refine le_trans Polynomial.natDegree_mul_le ?_
      rw [natDegree_cc, zero_add]
      refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
      · refine le_trans Polynomial.natDegree_mul_le ?_
        have := natDegree_diagP_le m n ((m : ℝ) + d + 1)
        omega
      · refine le_trans Polynomial.natDegree_mul_le ?_
        refine le_trans (Nat.add_le_add_right Polynomial.natDegree_mul_le _) ?_
        rw [natDegree_cc, natDegree_eta2P]
        omega
  exact (key d).1

lemma rootR_succ_ne (m n : ℚ) (hmn : |n| ≤ m) (f : ℝ) (hf : (m : ℝ) ≤ f) :
    rootR m n (f + 1) ≠ 0 := by
  have hm0 : (0 : ℝ) ≤ m := by exact_mod_cast le_trans (abs_nonneg n) hmn
  obtain ⟨hn1, hn2⟩ := abs_le.mp hmn
  have hn1' : -(m : ℝ) ≤ n := by exact_mod_cast hn1
  have hn2' : (n : ℝ) ≤ m := by exact_mod_cast hn2
  unfold rootR
  apply (Real.sqrt_pos.mpr _).ne'
  apply mul_pos <;> nlinarith

/-- One factor of the leading coefficient: `-2(2f+1)(f+1)/R_{f+1}` (from `eq:6jrankpoly`, the
`τ`-coefficient of `(2f+1)λ_f(1-2τ-q_f)` divided by `f R_{f+1}`). -/
noncomputable def kStep (m n : ℚ) (f : ℝ) : ℝ := -2 * (2 * f + 1) * (f + 1) / rootR m n (f + 1)

/-- The leading coefficient of `P̃_{m+d}` in `τ`: `√C(2m,m+n) · ∏_{j<d} kStep (m+j)`. -/
noncomputable def kLead (m n : ℚ) : ℕ → ℝ
  | 0 => Real.sqrt ((Nat.choose ⌊2 * m⌋₊ ⌊m + n⌋₊ : ℕ) : ℝ)
  | d + 1 => kStep m n ((m : ℝ) + d) * kLead m n d

lemma coeff_cc_mul (c : ℝ) (p : CarrierRing) (i : ℕ) :
    (cc c * p).coeff i = MvPolynomial.C c * p.coeff i := by
  unfold cc
  rw [Polynomial.coeff_C_mul]

/-- The coefficient of `τ^d` in `P̃_{m+d}` is the constant `kLead m n d` (it does not depend on
`u, v, w`, i.e. on the large scale; `lem:sqrtfreecarrier`). -/
theorem ptPoly_coeff_top (m n : ℚ) (hmn : |n| ≤ m) (d : ℕ) :
    (ptPoly m n d).coeff d = MvPolynomial.C (kLead m n d) := by
  have hm0 : (0 : ℝ) ≤ m := by exact_mod_cast le_trans (abs_nonneg n) hmn
  have key : ∀ d : ℕ, (ptPoly m n d).coeff d = MvPolynomial.C (kLead m n d) ∧
      (ptPoly m n (d + 1)).coeff (d + 1) = MvPolynomial.C (kLead m n (d + 1)) := by
    intro d
    induction d with
    | zero =>
      refine ⟨by simp [ptPoly, pt0, cc, kLead], ?_⟩
      show (pt1 m n).coeff 1 = MvPolynomial.C (kLead m n 1)
      unfold pt1
      by_cases hm : m = 0
      · subst hm
        have hn : n = 0 := abs_nonpos_iff.mp hmn
        subst hn
        simp only [ite_true]
        have : (1 - cc 2 * Polynomial.X - cc (1 / 8) * wVar : CarrierRing) =
            1 - Polynomial.C (MvPolynomial.C 2) * Polynomial.X -
              Polynomial.C (MvPolynomial.C (1 / 8)) * Polynomial.C (MvPolynomial.X 2) := rfl
        rw [this]
        simp [kLead, kStep, rootR, Polynomial.coeff_one]
      · simp only [hm, ite_false]
        have hd : (cc (1 / ((m : ℝ) * rootR m n ((m : ℝ) + 1))) * diagP m n (m : ℝ)).natDegree ≤ 1 := by
          refine le_trans Polynomial.natDegree_mul_le ?_
          rw [natDegree_cc]
          have := natDegree_diagP_le m n (m : ℝ)
          omega
        have h1 := Polynomial.coeff_mul_add_eq_of_natDegree_le (df := 1) (dg := 0) hd
          (le_of_eq (natDegree_pt0 m n))
        rw [show (1 : ℕ) = 1 + 0 by rfl] at h1 ⊢
        rw [h1, coeff_cc_mul, coeff_one_diagP]
        have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
        have hR := rootR_succ_ne m n hmn (m : ℝ) le_rfl
        have e : 1 / ((m : ℝ) * rootR m n ((m : ℝ) + 1)) * (-2 * ((2 * (m : ℝ) + 1) * m * (m + 1))) =
            kStep m n (m : ℝ) := by
          unfold kStep; field_simp
        simp only [pt0, cc, Polynomial.coeff_C_zero, kLead, Nat.cast_zero, add_zero]
        rw [← map_mul, ← map_mul]
        congr 1
        rw [e]
    | succ d ih =>
      refine ⟨ih.2, ?_⟩
      show (ptPoly m n (d + 2)).coeff (d + 2) = MvPolynomial.C (kLead m n (d + 2))
      have hdeg1 : (diagP m n ((m : ℝ) + d + 1)).natDegree ≤ 1 := natDegree_diagP_le _ _ _
      have hdeg2 : (ptPoly m n (d + 1)).natDegree ≤ d + 1 := ptPoly_natDegree_le m n (d + 1)
      have hdeg3 : (cc ((((m : ℝ) + d + 1) + 1) * rootR m n ((m : ℝ) + d + 1)) *
          eta2P ((m : ℝ) + d + 1) * ptPoly m n d).natDegree ≤ d := by
        refine le_trans Polynomial.natDegree_mul_le ?_
        refine le_trans (Nat.add_le_add_right Polynomial.natDegree_mul_le _) ?_
        rw [natDegree_cc, natDegree_eta2P]
        have := ptPoly_natDegree_le m n d
        omega
      have h1 := Polynomial.coeff_mul_add_eq_of_natDegree_le hdeg1 hdeg2
      rw [show 1 + (d + 1) = d + 2 by ring] at h1
      rw [ptPoly, coeff_cc_mul, Polynomial.coeff_sub, h1,
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg3 (by omega)), sub_zero,
        coeff_one_diagP, ih.2]
      have hf : (m : ℝ) + d + 1 ≠ 0 := by positivity
      have hR := rootR_succ_ne m n hmn ((m : ℝ) + d + 1) (by
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        linarith)
      have e : 1 / (((m : ℝ) + d + 1) * rootR m n ((m : ℝ) + d + 1 + 1)) *
          (-2 * ((2 * ((m : ℝ) + d + 1) + 1) * ((m : ℝ) + d + 1) * (((m : ℝ) + d + 1) + 1))) =
          kStep m n ((m : ℝ) + ((d + 1 : ℕ) : ℝ)) := by
        unfold kStep
        push_cast
        have e1 : (m : ℝ) + ((d : ℝ) + 1) + 1 = (m : ℝ) + d + 1 + 1 := by ring
        rw [e1]
        field_simp
        ring
      have hk : kLead m n (d + 2) = kStep m n ((m : ℝ) + ((d + 1 : ℕ) : ℝ)) * kLead m n (d + 1) :=
        rfl
      rw [hk, ← map_mul, ← map_mul]
      congr 1
      rw [← e]
      ring
  exact (key d).1

lemma kLead_ne_zero (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q) (hmn : |n| ≤ m) (d : ℕ) :
    kLead m n d ≠ 0 := by
  have hm0 : (0 : ℝ) ≤ m := by exact_mod_cast le_trans (abs_nonneg n) hmn
  induction d with
  | zero =>
    obtain ⟨-, h2, h3⟩ := floor_labels m n p q hp hq
    simp only [kLead, h2, h3]
    apply Real.sqrt_ne_zero'.mpr
    exact_mod_cast Nat.choose_pos (by omega)
  | succ d ih =>
    show kStep m n ((m : ℝ) + d) * kLead m n d ≠ 0
    refine mul_ne_zero ?_ ih
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hR := rootR_succ_ne m n hmn ((m : ℝ) + d) (by linarith)
    unfold kStep
    have : (-2 * (2 * ((m : ℝ) + d) + 1) * ((m : ℝ) + d + 1)) ≠ 0 := by
      have : 0 < (2 * ((m : ℝ) + d) + 1) * ((m : ℝ) + d + 1) := by positivity
      intro h; nlinarith
    exact div_ne_zero this hR

/-- **Exact degree** (`lem:sqrtfreecarrier`): for physical labels `m ± n ∈ ℕ`, `|n| ≤ m`,
`P̃_{m+d}` has degree exactly `d` in `τ` and its leading coefficient is the constant `kLead m n d`
(independent of `u, v, w`). -/
theorem ptPoly_natDegree (m n : ℚ) (p q : ℕ) (hp : m - n = p) (hq : m + n = q) (hmn : |n| ≤ m)
    (d : ℕ) : (ptPoly m n d).natDegree = d := by
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (ptPoly_natDegree_le m n d) ?_
  rw [ptPoly_coeff_top m n hmn d]
  exact (MvPolynomial.C_eq_zero.not).mpr (kLead_ne_zero m n p q hp hq hmn d)

/-- The carrier as a polynomial in `τ` with an explicit coefficient array: the `i`th coefficient is
the evaluation at `(u,v,w)` of the polynomial `(ptPoly m n d).coeff i ∈ ℝ[u,v,w]`. -/
theorem ptilde6_eq_sum (m n : ℚ) (τ u v w : ℝ) (d : ℕ) :
    ptilde6 m n τ u v w d =
      ∑ i ∈ Finset.range (d + 1),
        MvPolynomial.eval ![u, v, w] ((ptPoly m n d).coeff i) * τ ^ i := by
  unfold ptilde6 evalC
  rw [Polynomial.coe_eval₂RingHom]
  exact Polynomial.eval₂_eq_sum_range' (MvPolynomial.eval ![u, v, w])
    (Nat.lt_succ_of_le (ptPoly_natDegree_le m n d)) τ

/-- Symmetry `A ↔ B` of the carrier: `P̃(τ; u, v, w) = P̃(τ; v, u, w)` (`lem:sqrtfreecarrier`:
"symmetric under `A ↔ B`"). -/
theorem ptilde6_symm_uv (m n : ℚ) (τ u v w : ℝ) (d : ℕ) :
    ptilde6 m n τ u v w d = ptilde6 m n τ v u w d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    match d, ih with
    | 0, _ => rw [ptilde6_zero, ptilde6_zero]
    | 1, _ =>
      by_cases hm : m = 0
      · subst hm; rw [ptilde6_one_of_eq, ptilde6_one_of_eq]
      · rw [ptilde6_one_of_ne m n hm, ptilde6_one_of_ne m n hm]
    | d + 2, ih =>
      rw [ptilde6_succ_succ, ptilde6_succ_succ, ih d (by omega), ih (d + 1) (by omega)]
      ring

/-- Polynomiality in the dilation variable: at fixed `(τ, u₀, v₀, w₀)` the function
`t ↦ P̃(τ; t u₀, t v₀, t w₀)` is a polynomial in `t` (with `t = S⁻²` and `u₀ = α⁻²`, `v₀ = β⁻²`,
`w₀ = (αβ)⁻¹` this is the carrier factor of `G6c`). -/
theorem ptilde6_poly_in_t (m n : ℚ) (τ u₀ v₀ w₀ : ℝ) (d : ℕ) :
    ∃ P : Polynomial ℝ, ∀ t : ℝ,
      ptilde6 m n τ (t * u₀) (t * v₀) (t * w₀) d = P.eval t := by
  let ψ : MvPolynomial (Fin 3) ℝ →+* Polynomial ℝ :=
    MvPolynomial.eval₂Hom (Polynomial.C : ℝ →+* Polynomial ℝ)
      (![Polynomial.C u₀ * Polynomial.X, Polynomial.C v₀ * Polynomial.X,
        Polynomial.C w₀ * Polynomial.X] : Fin 3 → Polynomial ℝ)
  let ι : CarrierRing →+* Polynomial ℝ := Polynomial.eval₂RingHom ψ (Polynomial.C τ)
  refine ⟨ι (ptPoly m n d), fun t => ?_⟩
  have hhom : evalC τ (t * u₀) (t * v₀) (t * w₀) = (Polynomial.evalRingHom t).comp ι := by
    apply Polynomial.ringHom_ext
    · intro a
      have : ((evalC τ (t * u₀) (t * v₀) (t * w₀)).comp Polynomial.C) =
          (((Polynomial.evalRingHom t).comp ι).comp Polynomial.C) := by
        apply MvPolynomial.ringHom_ext
        · intro r; simp [evalC, ι, ψ]
        · intro i
          fin_cases i <;> simp [evalC, ι, ψ] <;> ring
      exact RingHom.congr_fun this a
    · rw [evalC_X]
      simp only [RingHom.comp_apply, ι, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        Polynomial.coe_evalRingHom, Polynomial.eval_C]
  unfold ptilde6
  rw [hhom]
  rfl

/-- The carrier factor of `G6c` is a polynomial in the dilation variable `t` at fixed shape:
`t ↦ P̃(τ; t/α², t/β², t/(αβ))` (`τ = (1 - cosA α β γ)/2`) is `P.eval t` for some `P ∈ ℝ[t]`.
Consequently `G6c m n d α β γ t = √(edgeSqT) · Π^{-1/2} · P(t)` with `edgeSqT`, `piSixT` polynomial
in `t` as well (`Ct`, products of `1 - c t`); the only non-polynomial operations are the two square
roots, which are analytic wherever their (polynomial) radicands are positive. -/
theorem ptilde6_shape_poly (m n : ℚ) (d : ℕ) (α β γ : ℝ) :
    ∃ P : Polynomial ℝ, ∀ t : ℝ,
      ptilde6 m n ((1 - cosA α β γ) / 2) (t / α ^ 2) (t / β ^ 2) (t / (α * β)) d = P.eval t := by
  obtain ⟨P, hP⟩ := ptilde6_poly_in_t m n ((1 - cosA α β γ) / 2) (1 / α ^ 2) (1 / β ^ 2)
    (1 / (α * β)) d
  exact ⟨P, fun t => by rw [← hP t, mul_one_div, mul_one_div, mul_one_div]⟩

/-- info: 'FormalResearch.Racah.ptPoly_natDegree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ptPoly_natDegree

/-- info: 'FormalResearch.Racah.ptilde6_symm_uv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ptilde6_symm_uv

/-- info: 'FormalResearch.Racah.ptilde6_shape_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ptilde6_shape_poly

end FormalResearch.Racah
