module

public import FormalResearch.ModularBootstrap.Stability.MultilevelExpansion
public import FormalResearch.Special.AiryLogDerivAsym
public import FormalResearch.Special.AiryValues
public import Mathlib.Analysis.Calculus.Implicit

/-!
# Local Hermite–Biehler Coordinates & Boundary Differentiation (`se:terminal-stability`, \eqref{se:hb-boundary-diff})

Source: `CFT/modular_bootstrap/paper/soft_edge_two_level_stability.tex`, Theorem
`se:terminal-stability`, equation \eqref{se:hb-boundary-diff}.

For fixed strict Hermite–Biehler data `(P₀, Q₀)` (`AiryPQHB P₀ Q₀`, `Q₀ ≠ 0`) with top `m` zeros
`S₀ = hbTopZeros hHB₀ hQ₀` (`m = at47_m P₀ Q₀ ≥ 2`), terminal zero `t_m = hbMinZero hHB₀ hQ₀`, and
prescribed `(m - 1)`-tuple `y₀ : ↥(S₀.erase t_m) → ℝ`:
* `hb_interpolant_unique_up_to_scale`: the determinant polynomial `P₁ Q₂ - Q₁ P₂` has degree `≤ m - 2`
  and coprimality from `AiryPQHB` forces any two degree-bounded interpolants at `(m - 1)` distinct
  sites to be scalar multiples of each other (`ker = ⊥` in the fixed normalisation).
* `hbBoundaryChart`: near `y₀`, the real-analytic (`ContDiffAt ℝ ω`) pair `(P_y, Q_y)` in the fixed
  saturated-coefficient normalisation and its real-analytic `m`th zero `Z_m(y)`, preserving
  `AiryPQHB`, `Q_y ≠ 0`, `at47_m P_y Q_y = m`, `hbTopZeros = insert (Z_m y) (range y)`, and
  `hbMinZero = Z_m y`.
* `hb_local_boundary_signs`: the prescribed-sites infimum `hbPrescribedI y z` is `0` at `z = Z_m(y)`,
  strictly positive for every `z > Z_m(y)`, and strictly negative for every `z < Z_m(y)`.
* `hb_boundary_diff`: at `y₀`, `∂Z_m/∂y_i = -b_i / b_m` (\eqref{se:hb-boundary-diff}).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set Polynomial
open scoped Real ContDiff

namespace FormalResearch.ModularBootstrap.Stability

open FormalResearch.Special FormalResearch.ModularBootstrap.Blowup
  FormalResearch.ModularBootstrap.ConcreteBootstrap FormalResearch.SignUncertainty

/-! ### Part 1: Degree parity, coprimality, and `1D`-kernel uniqueness -/

section BoundaryAlgebra

lemma at47_m_ge_two (P Q : ℝ[X]) (_hQ : Q ≠ 0) : 2 ≤ at47_m P Q := by
  have := at47_m_ge_Q P Q
  omega

lemma at47_degP_degQ_bounds (P Q : ℝ[X]) (hQ : Q ≠ 0) :
    let m := at47_m P Q
    P.natDegree ≤ (m - 1) / 2 ∧ Q.natDegree ≤ (m - 2) / 2 ∧
      (m - 1) / 2 + (m - 2) / 2 = m - 2 ∧
      (m % 2 = 1 → P.natDegree = (m - 1) / 2 ∧ P.coeff ((m - 1) / 2) ≠ 0) ∧
      (m % 2 = 0 → Q.natDegree = (m - 2) / 2 ∧ Q.coeff ((m - 2) / 2) ≠ 0) := by
  have hm2 : 2 ≤ at47_m P Q := at47_m_ge_two P Q hQ
  have hP := at47_m_ge_P P Q
  have hQ' := at47_m_ge_Q P Q
  have hm_eq : at47_m P Q = max (2 * P.natDegree + 1) (2 * Q.natDegree + 2) := rfl
  rcases le_total (2 * P.natDegree + 1) (2 * Q.natDegree + 2) with hle | hge
  · have hm_val : at47_m P Q = 2 * Q.natDegree + 2 := hm_eq.trans (max_eq_right hle)
    rw [hm_val]
    refine ⟨by omega, by omega, by omega, fun hodd => by omega, fun _ => ?_⟩
    have hdeg : Q.natDegree = (2 * Q.natDegree + 2 - 2) / 2 := by omega
    refine ⟨hdeg, ?_⟩
    rw [← hdeg]
    exact Polynomial.leadingCoeff_ne_zero.mpr hQ
  · have hm_val : at47_m P Q = 2 * P.natDegree + 1 := hm_eq.trans (max_eq_left hge)
    rw [hm_val]
    refine ⟨by omega, by omega, by omega, fun _ => ?_, fun heven => by omega⟩
    have hdeg : P.natDegree = (2 * P.natDegree + 1 - 1) / 2 := by omega
    refine ⟨hdeg, ?_⟩
    rw [← hdeg]
    by_cases hP0 : P = 0
    · rw [hP0, Polynomial.natDegree_zero] at hge
      omega
    · exact Polynomial.leadingCoeff_ne_zero.mpr hP0

private lemma airyPQc_conj' (P : ℝ[X]) (w : ℂ) :
    airyPQc P ((starRingEnd ℂ) w) = (starRingEnd ℂ) (airyPQc P w) := by
  rw [airyPQc_eq_sum, airyPQc_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow, Complex.conj_ofReal]

/-- Real polynomial pair `(P, Q)` satisfying strict Hermite–Biehler has no common complex root,
so `IsCoprime P Q` in `ℝ[X]`. -/
lemma isCoprime_of_airyPQHB {P Q : ℝ[X]} (hHB : AiryPQHB P Q) : IsCoprime P Q := by
  by_contra hnc
  have hnot_unit : ¬IsUnit (EuclideanDomain.gcd P Q) := fun hu => by
    obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp hu
    have hbez := EuclideanDomain.gcd_eq_gcd_ab P Q
    exact hnc ⟨u * EuclideanDomain.gcdA P Q, u * EuclideanDomain.gcdB P Q,
      by linear_combination -u * hbez + hu⟩
  set g := EuclideanDomain.gcd P Q
  have hg0 : g ≠ 0 := by
    intro hg
    have := EuclideanDomain.gcd_eq_zero_iff.mp hg
    have h0 := hHB 0 (by simp [airyPQc, this.1, this.2])
    simp at h0
  have hg_pos : 0 < g.natDegree := by
    by_contra hle
    have hd0 : g.natDegree = 0 := Nat.eq_zero_of_not_pos hle
    have hg_const := Polynomial.eq_C_of_natDegree_eq_zero hd0
    have hcoeff0 : g.coeff 0 ≠ 0 := fun h0 => hg0 (by rw [hg_const, h0, map_zero])
    exact hnot_unit (hg_const ▸ isUnit_C.mpr (IsUnit.mk0 _ hcoeff0))
  have hgC_pos : 0 < (g.map (algebraMap ℝ ℂ)).natDegree := by
    rwa [Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective]
  obtain ⟨w, hw⟩ := Complex.exists_root (Polynomial.natDegree_pos_iff_degree_pos.mp hgC_pos)
  have hgw : airyPQc g w = 0 := by
    rw [Polynomial.IsRoot] at hw
    exact hw
  have hPw : airyPQc P w = 0 := by
    rcases EuclideanDomain.gcd_dvd_left P Q with ⟨r, hr⟩
    rw [hr, airyPQc_mul, hgw, zero_mul]
  have hQw : airyPQc Q w = 0 := by
    rcases EuclideanDomain.gcd_dvd_right P Q with ⟨r, hr⟩
    rw [hr, airyPQc_mul, hgw, zero_mul]
  have hw_im : w.im < 0 := hHB w (by simp [hPw, hQw])
  have hPconj : airyPQc P ((starRingEnd ℂ) w) = 0 := by rw [airyPQc_conj', hPw, map_zero]
  have hQconj : airyPQc Q ((starRingEnd ℂ) w) = 0 := by rw [airyPQc_conj', hQw, map_zero]
  have hconj_im : ((starRingEnd ℂ) w).im < 0 := hHB ((starRingEnd ℂ) w) (by simp [hPconj, hQconj])
  have him_neg : -w.im < 0 := by simpa using hconj_im
  linarith

/-- `(Ai x, Ai' x) ≠ (0, 0)` for every real `x`, by the Airy–Bairy Wronskian. -/
lemma airyAi_airyAi'_ne_zero (x : ℝ) : airyAi x ≠ 0 ∨ airyAi' x ≠ 0 := by
  by_contra h
  push Not at h
  have hw := airyAiC_wronskian_airyBiC_eq (x : ℂ)
  rw [airyAiC_ofReal, deriv_airyAiC_ofReal, h.1, h.2] at hw
  simp only [Complex.ofReal_zero, zero_mul, sub_zero] at hw
  have hne : ((1 / π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  exact hne hw.symm

/-- **Uniqueness up to common scaling (`se:terminal-stability` determinant argument):**
For any `m ≥ 2` and `m - 1` distinct real nodes `y : ι → ℝ`, if `(P₁, Q₁)` is a strict
Hermite–Biehler pair of intrinsic index `m` (`Q₁ ≠ 0`) and `(P₂, Q₂)` is any nonzero pair with
`P₂.natDegree ≤ (m - 1)/2`, `Q₂.natDegree ≤ (m - 2)/2`, and both `N₁ = P₁ Ai + Q₁ Ai'` and
`N₂ = P₂ Ai + Q₂ Ai'` vanish at every `y i`, then `(P₂, Q₂) = c • (P₁, Q₁)` for some `c ≠ 0`. -/
lemma hb_interpolant_unique_up_to_scale {m : ℕ} (hm2 : 2 ≤ m)
    {ι : Type*} [Fintype ι] (hcard : Fintype.card ι = m - 1)
    {y : ι → ℝ} (hy_inj : Function.Injective y)
    {P₁ Q₁ P₂ Q₂ : ℝ[X]} (hHB₁ : AiryPQHB P₁ Q₁) (hQ₁ : Q₁ ≠ 0) (hm₁ : at47_m P₁ Q₁ = m)
    (hP₂_deg : P₂.natDegree ≤ (m - 1) / 2) (hQ₂_deg : Q₂.natDegree ≤ (m - 2) / 2)
    (hnz₂ : P₂ ≠ 0 ∨ Q₂ ≠ 0)
    (hzero₁ : ∀ i : ι, airyPQN P₁ Q₁ (y i : ℂ) = 0)
    (hzero₂ : ∀ i : ι, airyPQN P₂ Q₂ (y i : ℂ) = 0) :
    ∃ c : ℝ, c ≠ 0 ∧ P₂ = Polynomial.C c * P₁ ∧ Q₂ = Polynomial.C c * Q₁ := by
  have hb₁ := at47_degP_degQ_bounds P₁ Q₁ hQ₁
  rw [hm₁] at hb₁
  obtain ⟨hP₁_deg, hQ₁_deg, hdeg_sum, hodd₁, heven₁⟩ := hb₁
  let det : ℝ[X] := P₁ * Q₂ - Q₁ * P₂
  have hdet_deg : det.natDegree ≤ m - 2 := by
    have h1 : (P₁ * Q₂).natDegree ≤ m - 2 := (Polynomial.natDegree_mul_le).trans (by linarith)
    have h2 : (Q₁ * P₂).natDegree ≤ m - 2 := (Polynomial.natDegree_mul_le).trans (by linarith)
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le h1 h2)
  have hdet_root : ∀ i : ι, det.eval (y i) = 0 := by
    intro i
    have hN₁ : P₁.eval (y i) * airyAi (y i) + Q₁.eval (y i) * airyAi' (y i) = 0 := by
      have h1 := hzero₁ i; rw [airyPQN_ofReal] at h1; exact Complex.ofReal_eq_zero.mp h1
    have hN₂ : P₂.eval (y i) * airyAi (y i) + Q₂.eval (y i) * airyAi' (y i) = 0 := by
      have h2 := hzero₂ i; rw [airyPQN_ofReal] at h2; exact Complex.ofReal_eq_zero.mp h2
    simp only [det, Polynomial.eval_sub, Polynomial.eval_mul]
    rcases airyAi_airyAi'_ne_zero (y i) with hAi | hAi'
    · apply mul_right_cancel₀ hAi
      linear_combination Q₂.eval (y i) * hN₁ - Q₁.eval (y i) * hN₂
    · apply mul_right_cancel₀ hAi'
      linear_combination -(P₂.eval (y i) * hN₁ - P₁.eval (y i) * hN₂)
  have hdet_zero : det = 0 := by
    by_contra hne
    have hsub : (Finset.univ.image y).val ⊆ det.roots := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_def.mpr hx)
      exact (Polynomial.mem_roots hne).mpr (hdet_root i)
    have hcard_roots : m - 1 ≤ det.roots.card := by
      have hsub' : Finset.univ.image y ⊆ det.roots.toFinset := fun x hx =>
        Multiset.mem_toFinset.mpr (hsub (Finset.mem_def.mp hx))
      calc m - 1 = (Finset.univ : Finset ι).card := hcard.symm
        _ = (Finset.univ.image y).card := (Finset.card_image_of_injective _ hy_inj).symm
        _ ≤ det.roots.toFinset.card := Finset.card_le_card hsub'
        _ ≤ det.roots.card := Multiset.toFinset_card_le det.roots
    have hbd := Polynomial.card_roots' det
    omega
  have hmul_eq : P₁ * Q₂ = Q₁ * P₂ := sub_eq_zero.mp hdet_zero
  have hcop : IsCoprime P₁ Q₁ := isCoprime_of_airyPQHB hHB₁
  obtain ⟨R, hR_eq⟩ : Q₁ ∣ Q₂ := hcop.symm.dvd_of_dvd_mul_left ⟨P₂, hmul_eq⟩
  have hP₁_eq : Q₁ * (P₁ * R) = Q₁ * P₂ := by
    calc Q₁ * (P₁ * R) = P₁ * (Q₁ * R) := by ring
      _ = P₁ * Q₂ := by rw [hR_eq]
      _ = Q₁ * P₂ := hmul_eq
  have hP₂_eq : P₂ = P₁ * R := (mul_left_cancel₀ hQ₁ hP₁_eq).symm
  have hR_ne0 : R ≠ 0 := by
    intro hR0
    rw [hR0, mul_zero] at hR_eq hP₂_eq
    rcases hnz₂ with hp | hq
    · exact hp hP₂_eq
    · exact hq hR_eq
  have hR_deg : R.natDegree = 0 := by
    rcases Nat.mod_two_eq_zero_or_one m with he | ho
    · obtain ⟨hQd, _⟩ := heven₁ he
      have hmul_deg : (Q₁ * R).natDegree = Q₁.natDegree + R.natDegree :=
        Polynomial.natDegree_mul hQ₁ hR_ne0
      rw [← hR_eq] at hmul_deg
      omega
    · obtain ⟨hPd, hPne⟩ := hodd₁ ho
      have hP₁0 : P₁ ≠ 0 := fun h0 => by simp [h0] at hPne
      have hmul_deg : (P₁ * R).natDegree = P₁.natDegree + R.natDegree :=
        Polynomial.natDegree_mul hP₁0 hR_ne0
      rw [← hP₂_eq] at hmul_deg
      omega
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hR_deg
  have hc0 : c ≠ 0 := fun h0 => hR_ne0 (by rw [← hc, h0, map_zero])
  refine ⟨c, hc0, ?_, ?_⟩
  · rw [hP₂_eq, ← hc, mul_comm]
  · rw [hR_eq, ← hc, mul_comm]

end BoundaryAlgebra

/-! ### Part 2: Smooth normalized `(P, Q)` parametrization and Airy analyticity -/

section BoundaryParam

variable {P₀ Q₀ : ℝ[X]} (hHB₀ : AiryPQHB P₀ Q₀) (hQ₀ : Q₀ ≠ 0)

/-- Number of free `P`-coefficients in the fixed saturated normalisation. -/
noncomputable def hbFreeP (P₀ Q₀ : ℝ[X]) : ℕ :=
  let m := at47_m P₀ Q₀
  if m % 2 = 1 then (m - 1) / 2 else (m - 1) / 2 + 1

/-- Number of free `Q`-coefficients in the fixed saturated normalisation. -/
noncomputable def hbFreeQ (P₀ Q₀ : ℝ[X]) : ℕ :=
  let m := at47_m P₀ Q₀
  if m % 2 = 1 then (m - 2) / 2 + 1 else (m - 2) / 2

lemma hbFreeP_add_hbFreeQ {P₀ Q₀ : ℝ[X]} (hQ : Q₀ ≠ 0) :
    hbFreeP P₀ Q₀ + hbFreeQ P₀ Q₀ = at47_m P₀ Q₀ - 1 := by
  have hm2 : 2 ≤ at47_m P₀ Q₀ := at47_m_ge_two P₀ Q₀ hQ
  unfold hbFreeP hbFreeQ
  rcases Nat.mod_two_eq_zero_or_one (at47_m P₀ Q₀) with h | h <;> simp [h] <;> omega

/-- Affine parameter space `(ΔP, ΔQ)` centered at `0` around `(P₀, Q₀)`, of dimension `m - 1`. -/
abbrev HbParam (P₀ Q₀ : ℝ[X]) :=
  (Fin (hbFreeP P₀ Q₀) → ℝ) × (Fin (hbFreeQ P₀ Q₀) → ℝ)

noncomputable def hbDeltaP (P₀ Q₀ : ℝ[X]) (v : Fin (hbFreeP P₀ Q₀) → ℝ) : ℝ[X] :=
  ∑ j : Fin (hbFreeP P₀ Q₀), Polynomial.C (v j) * Polynomial.X ^ (j : ℕ)

noncomputable def hbDeltaQ (P₀ Q₀ : ℝ[X]) (w : Fin (hbFreeQ P₀ Q₀) → ℝ) : ℝ[X] :=
  ∑ k : Fin (hbFreeQ P₀ Q₀), Polynomial.C (w k) * Polynomial.X ^ (k : ℕ)

noncomputable def hbPairP (P₀ Q₀ : ℝ[X]) (θ : HbParam P₀ Q₀) : ℝ[X] :=
  P₀ + hbDeltaP P₀ Q₀ θ.1

noncomputable def hbPairQ (P₀ Q₀ : ℝ[X]) (θ : HbParam P₀ Q₀) : ℝ[X] :=
  Q₀ + hbDeltaQ P₀ Q₀ θ.2

/-- Fixed-normalisation predicate for `(P, Q)` near `(P₀, Q₀)`. -/
def HbNormalized (P₀ Q₀ P Q : ℝ[X]) : Prop :=
  P.natDegree ≤ (at47_m P₀ Q₀ - 1) / 2 ∧
  Q.natDegree ≤ (at47_m P₀ Q₀ - 2) / 2 ∧
  (if at47_m P₀ Q₀ % 2 = 1 then
      P.coeff ((at47_m P₀ Q₀ - 1) / 2) = P₀.coeff ((at47_m P₀ Q₀ - 1) / 2)
    else
      Q.coeff ((at47_m P₀ Q₀ - 2) / 2) = Q₀.coeff ((at47_m P₀ Q₀ - 2) / 2))

private lemma poly_coeff_sum' {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) (k : ℕ) :
    (∑ i ∈ s, f i).coeff k = ∑ i ∈ s, (f i).coeff k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha]

private lemma poly_eval_sum' {R ι : Type*} [Semiring R] (s : Finset ι) (f : ι → R[X]) (x : R) :
    (∑ i ∈ s, f i).eval x = ∑ i ∈ s, (f i).eval x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

private lemma continuous_sum' {α ι E : Type*} [TopologicalSpace α]
    [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E]
    (s : Finset ι) {f : ι → α → E} (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [continuous_const]
  | @insert a s ha ih =>
      have heq : (fun x => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x := by
        ext x; exact Finset.sum_insert ha
      rw [heq]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma poly_continuous_eval' (p : ℝ[X]) : Continuous (fun x : ℝ => p.eval x) := by
  have heq : (fun x : ℝ => p.eval x) =
      fun x : ℝ => ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * x ^ k :=
    funext fun x => Polynomial.eval_eq_sum_range p x
  rw [heq]
  exact continuous_sum' _ fun k _ => continuous_const.mul (continuous_id.pow k)

lemma hasDerivAt_re_comp {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y : ℝ => (f y).re) f'.re x := by
  rw [hasDerivAt_iff_tendsto_slope]
  have ht := Complex.continuous_re.continuousAt.tendsto.comp (hasDerivAt_iff_tendsto_slope.mp h)
  convert ht using 1
  ext y
  simp only [Function.comp_apply, slope_def_module, smul_eq_mul, Complex.real_smul,
    Complex.re_ofReal_mul, Complex.sub_re]

lemma hbDeltaP_natDegree_le (v : Fin (hbFreeP P₀ Q₀) → ℝ) :
    (hbDeltaP P₀ Q₀ v).natDegree ≤ (at47_m P₀ Q₀ - 1) / 2 := by
  refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun j _ => ?_)
  refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_X_pow_le _).trans ?_)
  have hj := j.isLt
  dsimp only [hbFreeP] at hj
  split_ifs at hj <;> omega

lemma hbDeltaQ_natDegree_le (w : Fin (hbFreeQ P₀ Q₀) → ℝ) :
    (hbDeltaQ P₀ Q₀ w).natDegree ≤ (at47_m P₀ Q₀ - 2) / 2 := by
  refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun k _ => ?_)
  refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_X_pow_le _).trans ?_)
  have hk := k.isLt
  dsimp only [hbFreeQ] at hk
  split_ifs at hk <;> omega

lemma hbDeltaP_saturated_coeff_zero (hodd : at47_m P₀ Q₀ % 2 = 1)
    (v : Fin (hbFreeP P₀ Q₀) → ℝ) :
    (hbDeltaP P₀ Q₀ v).coeff ((at47_m P₀ Q₀ - 1) / 2) = 0 := by
  unfold hbDeltaP
  rw [poly_coeff_sum']
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have hj : (j : ℕ) < (at47_m P₀ Q₀ - 1) / 2 := by
    simpa [hbFreeP, hodd] using j.isLt
  simp [hj.ne']

lemma hbDeltaQ_saturated_coeff_zero (heven : at47_m P₀ Q₀ % 2 = 0)
    (w : Fin (hbFreeQ P₀ Q₀) → ℝ) :
    (hbDeltaQ P₀ Q₀ w).coeff ((at47_m P₀ Q₀ - 2) / 2) = 0 := by
  unfold hbDeltaQ
  rw [poly_coeff_sum']
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have hk : (k : ℕ) < (at47_m P₀ Q₀ - 2) / 2 := by
    simpa [hbFreeQ, show at47_m P₀ Q₀ % 2 ≠ 1 by omega] using k.isLt
  simp [hk.ne']

lemma hbDeltaP_eq_zero_iff (v : Fin (hbFreeP P₀ Q₀) → ℝ) :
    hbDeltaP P₀ Q₀ v = 0 ↔ v = 0 := by
  constructor
  · intro h
    ext j
    have hc := congrArg (fun p : ℝ[X] => p.coeff (j : ℕ)) h
    rw [hbDeltaP, poly_coeff_sum', Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single j] at hc
    · simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] using hc
    · intro b _ hbj
      have hne : (j : ℕ) ≠ (b : ℕ) := fun he => hbj (Fin.ext he.symm)
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  · intro hv; simp [hv, hbDeltaP]

lemma hbDeltaQ_eq_zero_iff (w : Fin (hbFreeQ P₀ Q₀) → ℝ) :
    hbDeltaQ P₀ Q₀ w = 0 ↔ w = 0 := by
  constructor
  · intro h
    ext k
    have hc := congrArg (fun p : ℝ[X] => p.coeff (k : ℕ)) h
    rw [hbDeltaQ, poly_coeff_sum', Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single k] at hc
    · simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] using hc
    · intro b _ hbk
      have hne : (k : ℕ) ≠ (b : ℕ) := fun he => hbk (Fin.ext he.symm)
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  · intro hw; simp [hw, hbDeltaQ]

lemma hbPairP_natDegree_le (hQ : Q₀ ≠ 0) (θ : HbParam P₀ Q₀) :
    (hbPairP P₀ Q₀ θ).natDegree ≤ (at47_m P₀ Q₀ - 1) / 2 :=
  (Polynomial.natDegree_add_le _ _).trans (max_le
    (at47_degP_degQ_bounds P₀ Q₀ hQ).1 (hbDeltaP_natDegree_le θ.1))

lemma hbPairQ_natDegree_le (hQ : Q₀ ≠ 0) (θ : HbParam P₀ Q₀) :
    (hbPairQ P₀ Q₀ θ).natDegree ≤ (at47_m P₀ Q₀ - 2) / 2 :=
  (Polynomial.natDegree_add_le _ _).trans (max_le
    (at47_degP_degQ_bounds P₀ Q₀ hQ).2.1 (hbDeltaQ_natDegree_le θ.2))

lemma hbPair_normalized (hQ : Q₀ ≠ 0) (θ : HbParam P₀ Q₀) :
    HbNormalized P₀ Q₀ (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) := by
  refine ⟨hbPairP_natDegree_le hQ θ, hbPairQ_natDegree_le hQ θ, ?_⟩
  split_ifs with hodd
  · simp [hbPairP, hbDeltaP_saturated_coeff_zero hodd θ.1]
  · have heven : at47_m P₀ Q₀ % 2 = 0 := by omega
    simp [hbPairQ, hbDeltaQ_saturated_coeff_zero heven θ.2]

/-- Analyticity (`ContDiff ℝ ω`) of `airyAi` and `airyAi'`. -/
lemma airyAi_contDiff_omega : ContDiff ℝ ω airyAi := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hAnC : AnalyticAt ℂ airyAiC (x : ℂ) := differentiable_airyAiC.analyticAt (x : ℂ)
  have hAnR : AnalyticAt ℝ (fun y : ℝ => airyAiC (y : ℂ)) x :=
    AnalyticAt.comp (hAnC.restrictScalars) (Complex.ofRealCLM.analyticAt x)
  have hRe : ContDiffAt ℝ ω (fun y : ℝ => (airyAiC (y : ℂ)).re) x :=
    (Complex.reCLM.contDiff.contDiffAt).comp x hAnR.contDiffAt
  have hEq : (fun y : ℝ => (airyAiC (y : ℂ)).re) = airyAi := by
    ext y; rw [airyAiC_ofReal, Complex.ofReal_re]
  rwa [hEq] at hRe

lemma airyAi'_contDiff_omega : ContDiff ℝ ω airyAi' := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hAnC : AnalyticAt ℂ (deriv airyAiC) (x : ℂ) :=
    differentiable_airyAiC.deriv.analyticAt (x : ℂ)
  have hAnR : AnalyticAt ℝ (fun y : ℝ => deriv airyAiC (y : ℂ)) x :=
    AnalyticAt.comp (hAnC.restrictScalars) (Complex.ofRealCLM.analyticAt x)
  have hRe : ContDiffAt ℝ ω (fun y : ℝ => (deriv airyAiC (y : ℂ)).re) x :=
    (Complex.reCLM.contDiff.contDiffAt).comp x hAnR.contDiffAt
  have hEq : (fun y : ℝ => (deriv airyAiC (y : ℂ)).re) = airyAi' := by
    ext y; rw [deriv_airyAiC_ofReal, Complex.ofReal_re]
  rwa [hEq] at hRe

private lemma poly_eval_contDiff_omega (p : ℝ[X]) : ContDiff ℝ ω (fun x : ℝ => p.eval x) := by
  have heq : (fun x : ℝ => p.eval x) =
      fun x : ℝ => ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * x ^ k :=
    funext fun x => Polynomial.eval_eq_sum_range p x
  rw [heq]
  exact ContDiff.sum fun k _ => contDiff_const.mul (contDiff_id.pow k)

/-- Joint real-analyticity of `(x, θ) ↦ (hbPairP θ).eval (g x) * airyAi (g x) + (hbPairQ θ).eval (g x) * airyAi' (g x)`. -/
lemma hbPair_real_eval_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} (hg : ContDiff ℝ ω g) :
    ContDiff ℝ ω (fun p : E × HbParam P₀ Q₀ =>
      (hbPairP P₀ Q₀ p.2).eval (g p.1) * airyAi (g p.1) +
        (hbPairQ P₀ Q₀ p.2).eval (g p.1) * airyAi' (g p.1)) := by
  have hg1 : ContDiff ℝ ω (fun p : E × HbParam P₀ Q₀ => g p.1) := hg.comp contDiff_fst
  have hP0 : ContDiff ℝ ω (fun p : E × HbParam P₀ Q₀ => P₀.eval (g p.1)) :=
    (poly_eval_contDiff_omega P₀).comp hg1
  have hQ0 : ContDiff ℝ ω (fun p : E × HbParam P₀ Q₀ => Q₀.eval (g p.1)) :=
    (poly_eval_contDiff_omega Q₀).comp hg1
  have hdP : ContDiff ℝ ω (fun p : E × HbParam P₀ Q₀ => (hbDeltaP P₀ Q₀ p.2.1).eval (g p.1)) := by
    have heq : (fun p : E × HbParam P₀ Q₀ => (hbDeltaP P₀ Q₀ p.2.1).eval (g p.1)) =
        fun p => ∑ j : Fin (hbFreeP P₀ Q₀), p.2.1 j * (g p.1) ^ (j : ℕ) := by
      ext p; rw [hbDeltaP, poly_eval_sum']; simp
    rw [heq]
    refine ContDiff.sum fun j _ => ?_
    have hcoord : ContDiff ℝ ω (fun p : E × HbParam P₀ Q₀ => p.2.1 j) :=
      ((ContinuousLinearMap.proj (R := ℝ) (ι := Fin (hbFreeP P₀ Q₀)) (φ := fun _ => ℝ) j).comp
        ((ContinuousLinearMap.fst ℝ (Fin (hbFreeP P₀ Q₀) → ℝ) (Fin (hbFreeQ P₀ Q₀) → ℝ)).comp
          (ContinuousLinearMap.snd ℝ E (HbParam P₀ Q₀)))).contDiff
    exact hcoord.mul (hg1.pow j)
  have hdQ : ContDiff ℝ ω (fun p : E × HbParam P₀ Q₀ => (hbDeltaQ P₀ Q₀ p.2.2).eval (g p.1)) := by
    have heq : (fun p : E × HbParam P₀ Q₀ => (hbDeltaQ P₀ Q₀ p.2.2).eval (g p.1)) =
        fun p => ∑ k : Fin (hbFreeQ P₀ Q₀), p.2.2 k * (g p.1) ^ (k : ℕ) := by
      ext p; rw [hbDeltaQ, poly_eval_sum']; simp
    rw [heq]
    refine ContDiff.sum fun k _ => ?_
    have hcoord : ContDiff ℝ ω (fun p : E × HbParam P₀ Q₀ => p.2.2 k) :=
      ((ContinuousLinearMap.proj (R := ℝ) (ι := Fin (hbFreeQ P₀ Q₀)) (φ := fun _ => ℝ) k).comp
        ((ContinuousLinearMap.snd ℝ (Fin (hbFreeP P₀ Q₀) → ℝ) (Fin (hbFreeQ P₀ Q₀) → ℝ)).comp
          (ContinuousLinearMap.snd ℝ E (HbParam P₀ Q₀)))).contDiff
    exact hcoord.mul (hg1.pow k)
  have hP : ContDiff ℝ ω (fun p : E × HbParam P₀ Q₀ => (hbPairP P₀ Q₀ p.2).eval (g p.1)) := by
    simpa [hbPairP, Polynomial.eval_add] using hP0.add hdP
  have hQ : ContDiff ℝ ω (fun p : E × HbParam P₀ Q₀ => (hbPairQ P₀ Q₀ p.2).eval (g p.1)) := by
    simpa [hbPairQ, Polynomial.eval_add] using hQ0.add hdQ
  exact (hP.mul (airyAi_contDiff_omega.comp hg1)).add
    (hQ.mul (airyAi'_contDiff_omega.comp hg1))

end BoundaryParam

/-! ### Part 3: Perturbation openness of `AiryPQHB`, tail sign, and compact node isolation -/

section BoundaryOpenness

variable {P₀ Q₀ : ℝ[X]} (hHB₀ : AiryPQHB P₀ Q₀) (hQ₀ : Q₀ ≠ 0)

private lemma poly_sum_eval_abs_le {d : ℕ} (p : ℝ[X]) (hp : p.natDegree ≤ d)
    {C : ℝ} (hC : ∀ k ≤ d, |p.coeff k| ≤ C) {x : ℝ} (hx : 1 ≤ x) :
    |p.eval x| ≤ ((d : ℝ) + 1) * C * x ^ d := by
  have hx0 : 0 ≤ x := by linarith
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0 (Nat.zero_le _))
  have heq : p.eval x = ∑ k ∈ Finset.range (d + 1), p.coeff k * x ^ k := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp)]
  rw [heq]
  calc |∑ k ∈ Finset.range (d + 1), p.coeff k * x ^ k|
      ≤ ∑ k ∈ Finset.range (d + 1), |p.coeff k * x ^ k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ Finset.range (d + 1), |p.coeff k| * x ^ k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [abs_mul, abs_of_nonneg (pow_nonneg hx0 _)]
    _ ≤ ∑ _k ∈ Finset.range (d + 1), C * x ^ d := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        exact mul_le_mul (hC k hkd) (pow_le_pow_right₀ hx hkd) (pow_nonneg hx0 _) hC0
    _ = ((d : ℝ) + 1) * C * x ^ d := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

private lemma poly_lower_of_lead {d : ℕ} (p : ℝ[X]) (hp : p.natDegree ≤ d)
    {C : ℝ} (hC : ∀ k, |p.coeff k| ≤ C) {x : ℝ} (hx : 1 ≤ x) :
    (|p.coeff d| - (d : ℝ) * C / x) * x ^ d ≤ |p.eval x| := by
  have hx0 : 0 < x := by linarith
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  have heq : p.eval x = p.coeff d * x ^ d + ∑ k ∈ Finset.range d, p.coeff k * x ^ k := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp), Finset.sum_range_succ, add_comm]
  have h_low : |p.coeff d| * x ^ d - |∑ k ∈ Finset.range d, p.coeff k * x ^ k| ≤ |p.eval x| := by
    have hcoeff : p.coeff d * x ^ d = p.eval x - ∑ k ∈ Finset.range d, p.coeff k * x ^ k := by
      rw [heq]; ring
    have h_abs : |p.coeff d| * x ^ d ≤ |p.eval x| + |∑ k ∈ Finset.range d, p.coeff k * x ^ k| := by
      calc |p.coeff d| * x ^ d = |p.coeff d * x ^ d| := by
              rw [abs_mul, abs_of_nonneg (pow_nonneg hx0.le _)]
        _ = |p.eval x - ∑ k ∈ Finset.range d, p.coeff k * x ^ k| := by rw [hcoeff]
        _ ≤ |p.eval x| + |∑ k ∈ Finset.range d, p.coeff k * x ^ k| := abs_sub _ _
    linarith
  have h_sum_x : x * |∑ k ∈ Finset.range d, p.coeff k * x ^ k| ≤ (d : ℝ) * C * x ^ d := by
    calc x * |∑ k ∈ Finset.range d, p.coeff k * x ^ k|
        ≤ x * ∑ k ∈ Finset.range d, |p.coeff k * x ^ k| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hx0.le
      _ = ∑ k ∈ Finset.range d, |p.coeff k| * x ^ (k + 1) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [abs_mul, abs_of_nonneg (pow_nonneg hx0.le _), pow_succ']
            ring
      _ ≤ ∑ _k ∈ Finset.range d, C * x ^ d := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hk1 : k + 1 ≤ d := Finset.mem_range.mp hk
            exact mul_le_mul (hC k) (pow_le_pow_right₀ hx hk1) (pow_nonneg hx0.le _) hC0
      _ = (d : ℝ) * C * x ^ d := by simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have h_sum_le : |∑ k ∈ Finset.range d, p.coeff k * x ^ k| ≤ ((d : ℝ) * C / x) * x ^ d := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hx0, mul_comm]
    exact h_sum_x
  linarith [show (|p.coeff d| - (d : ℝ) * C / x) * x ^ d =
      |p.coeff d| * x ^ d - ((d : ℝ) * C / x) * x ^ d by ring]

private lemma hbPair_coeff_bound (hQ : Q₀ ≠ 0) (θ : HbParam P₀ Q₀) (hθ : ‖θ‖ ≤ 1) :
    let d := max ((at47_m P₀ Q₀ - 1) / 2) ((at47_m P₀ Q₀ - 2) / 2)
    let C := Finset.sup' (Finset.range (d + 1)) ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
      (fun k => max |P₀.coeff k| |Q₀.coeff k|) + 1
    (∀ k, |(hbPairP P₀ Q₀ θ).coeff k| ≤ C) ∧ (∀ k, |(hbPairQ P₀ Q₀ θ).coeff k| ≤ C) := by
  intro d C
  let rng : Finset ℕ := Finset.range (d + 1)
  have h0_mem : 0 ∈ rng := Finset.mem_range.mpr (Nat.zero_lt_succ _)
  have hC1 : 1 ≤ C := by
    have hsup : 0 ≤ rng.sup' ⟨0, h0_mem⟩ (fun k => max |P₀.coeff k| |Q₀.coeff k|) :=
      le_trans (le_trans (abs_nonneg (P₀.coeff 0)) (le_max_left _ _))
        (Finset.le_sup' (fun k => max |P₀.coeff k| |Q₀.coeff k|) h0_mem)
    dsimp [C]; linarith
  have hC0 : 0 ≤ C := by linarith
  constructor
  · intro k
    by_cases hk : k ≤ d
    · have hk_mem : k ∈ rng := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
      have h0_sup : |P₀.coeff k| ≤ rng.sup' ⟨0, h0_mem⟩ (fun j => max |P₀.coeff j| |Q₀.coeff j|) :=
        (le_max_left |P₀.coeff k| |Q₀.coeff k|).trans
          (Finset.le_sup' (fun j => max |P₀.coeff j| |Q₀.coeff j|) hk_mem)
      have h0 : |P₀.coeff k| ≤ C - 1 := by dsimp [C]; linarith
      have hd_val : |(hbDeltaP P₀ Q₀ θ.1).coeff k| ≤ 1 := by
        unfold hbDeltaP
        rw [poly_coeff_sum']
        by_cases hlt : k < hbFreeP P₀ Q₀
        · let j : Fin (hbFreeP P₀ Q₀) := ⟨k, hlt⟩
          rw [Finset.sum_eq_single j]
          · simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, j, ↓reduceIte, mul_one]
            exact ((by simpa [Real.norm_eq_abs] using norm_le_pi_norm θ.1 j :
              |θ.1 j| ≤ ‖θ.1‖)).trans ((norm_fst_le θ).trans hθ)
          · intro b _ hbj
            have hne : k ≠ (b : ℕ) := fun he => hbj (Fin.ext he.symm)
            simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
          · intro hj; exact absurd (Finset.mem_univ j) hj
        · have h0sum : ∑ j : Fin (hbFreeP P₀ Q₀),
              (Polynomial.C (θ.1 j) * Polynomial.X ^ (j : ℕ)).coeff k = 0 :=
            Finset.sum_eq_zero fun j _ => by
              have hne : k ≠ (j : ℕ) := fun he => hlt (he ▸ j.isLt)
              simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
          rw [h0sum, abs_zero]; exact zero_le_one
      rw [hbPairP, Polynomial.coeff_add]
      exact (abs_add_le _ _).trans (by linarith)
    · have hkP : (hbPairP P₀ Q₀ θ).natDegree < k :=
        lt_of_le_of_lt ((hbPairP_natDegree_le hQ θ).trans (le_max_left _ _)) (not_le.mp hk)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hkP, abs_zero]; exact hC0
  · intro k
    by_cases hk : k ≤ d
    · have hk_mem : k ∈ rng := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
      have h0_sup : |Q₀.coeff k| ≤ rng.sup' ⟨0, h0_mem⟩ (fun j => max |P₀.coeff j| |Q₀.coeff j|) :=
        (le_max_right |P₀.coeff k| |Q₀.coeff k|).trans
          (Finset.le_sup' (fun j => max |P₀.coeff j| |Q₀.coeff j|) hk_mem)
      have h0 : |Q₀.coeff k| ≤ C - 1 := by dsimp [C]; linarith
      have hd_val : |(hbDeltaQ P₀ Q₀ θ.2).coeff k| ≤ 1 := by
        unfold hbDeltaQ
        rw [poly_coeff_sum']
        by_cases hlt : k < hbFreeQ P₀ Q₀
        · let j : Fin (hbFreeQ P₀ Q₀) := ⟨k, hlt⟩
          rw [Finset.sum_eq_single j]
          · simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, j, ↓reduceIte, mul_one]
            exact ((by simpa [Real.norm_eq_abs] using norm_le_pi_norm θ.2 j :
              |θ.2 j| ≤ ‖θ.2‖)).trans ((norm_snd_le θ).trans hθ)
          · intro b _ hbj
            have hne : k ≠ (b : ℕ) := fun he => hbj (Fin.ext he.symm)
            simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
          · intro hj; exact absurd (Finset.mem_univ j) hj
        · have h0sum : ∑ j : Fin (hbFreeQ P₀ Q₀),
              (Polynomial.C (θ.2 j) * Polynomial.X ^ (j : ℕ)).coeff k = 0 :=
            Finset.sum_eq_zero fun j _ => by
              have hne : k ≠ (j : ℕ) := fun he => hlt (he ▸ j.isLt)
              simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
          rw [h0sum, abs_zero]; exact zero_le_one
      rw [hbPairQ, Polynomial.coeff_add]
      exact (abs_add_le _ _).trans (by linarith)
    · have hkQ : (hbPairQ P₀ Q₀ θ).natDegree < k :=
        lt_of_le_of_lt ((hbPairQ_natDegree_le hQ θ).trans (le_max_right _ _)) (not_le.mp hk)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hkQ, abs_zero]; exact hC0

/-- Every parameter `θ` sufficiently close to `0` preserves strict Hermite–Biehler `AiryPQHB`,
`Q ≠ 0`, and intrinsic index `at47_m = at47_m P₀ Q₀`. -/
lemma hbPair_open_hb {P₀ Q₀ : ℝ[X]} (hHB₀ : AiryPQHB P₀ Q₀) (hQ₀ : Q₀ ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ θ : HbParam P₀ Q₀, ‖θ‖ < η →
      AiryPQHB (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) ∧
        hbPairQ P₀ Q₀ θ ≠ 0 ∧ at47_m (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) = at47_m P₀ Q₀ := by
  have hm2 : 2 ≤ at47_m P₀ Q₀ := at47_m_ge_two P₀ Q₀ hQ₀
  obtain ⟨hP₀_deg, hQ₀_deg, _, hodd₀, heven₀⟩ := at47_degP_degQ_bounds P₀ Q₀ hQ₀
  set m := at47_m P₀ Q₀
  set p_deg := if m % 2 = 1 then (m - 1) / 2 else (m - 2) / 2
  set c_lead : ℝ := if m % 2 = 1 then |P₀.coeff ((m - 1) / 2)| else |Q₀.coeff ((m - 2) / 2)|
  have hc_lead_pos : 0 < c_lead := by
    dsimp [c_lead]
    split_ifs with hodd
    · exact abs_pos.mpr (hodd₀ hodd).2
    · exact abs_pos.mpr (heven₀ (by omega)).2
  have hF_deg : ∀ θ : HbParam P₀ Q₀, (airyPQF (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ)).natDegree = p_deg := by
    intro θ
    have hPb := hbPairP_natDegree_le hQ₀ θ
    have hQb := hbPairQ_natDegree_le hQ₀ θ
    have hsat := hbPair_normalized hQ₀ θ
    have hcoeff_val : ∀ k : ℕ, (airyPQF (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ)).coeff k =
        (((hbPairQ P₀ Q₀ θ).coeff k : ℝ) : ℂ) + I * (((hbPairP P₀ Q₀ θ).coeff k : ℝ) : ℂ) := by
      intro k
      unfold airyPQF
      simp only [Polynomial.coeff_add, Polynomial.coeff_map, Polynomial.coeff_C_mul,
        Complex.coe_algebraMap]
    have h_le : (airyPQF (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ)).natDegree ≤ p_deg := by
      unfold airyPQF
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (Polynomial.natDegree_map_le).trans (hQb.trans ?_)
        dsimp [p_deg]; split_ifs <;> omega
      · refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_map_le).trans (hPb.trans ?_))
        dsimp [p_deg]; split_ifs <;> omega
    have h_ne_p : (airyPQF (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ)).coeff p_deg ≠ 0 := by
      rw [hcoeff_val p_deg]
      intro h0
      have hre : (hbPairQ P₀ Q₀ θ).coeff p_deg = 0 := by
        have := congrArg Complex.re h0; simpa using this
      have him : (hbPairP P₀ Q₀ θ).coeff p_deg = 0 := by
        have := congrArg Complex.im h0; simpa using this
      rcases Nat.mod_two_eq_zero_or_one m with he | ho
      · have hp : p_deg = (m - 2) / 2 := by dsimp [p_deg]; simp [he]
        rw [hp] at hre
        have hsatQ := hsat.2.2
        change (if m % 2 = 1 then _ else (hbPairQ P₀ Q₀ θ).coeff ((m - 2) / 2) = Q₀.coeff ((m - 2) / 2)) at hsatQ
        rw [if_neg (by omega)] at hsatQ
        rw [hsatQ] at hre
        exact (heven₀ he).2 hre
      · have hp : p_deg = (m - 1) / 2 := by dsimp [p_deg]; simp [ho]
        rw [hp] at him
        have hsatP := hsat.2.2
        change (if m % 2 = 1 then (hbPairP P₀ Q₀ θ).coeff ((m - 1) / 2) = P₀.coeff ((m - 1) / 2) else _) at hsatP
        rw [if_pos ho] at hsatP
        rw [hsatP] at him
        exact (hodd₀ ho).2 him
    exact le_antisymm h_le (Polynomial.le_natDegree_of_ne_zero h_ne_p)
  have hF_lead_ge : ∀ θ : HbParam P₀ Q₀,
      c_lead ≤ ‖(airyPQF (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ)).coeff p_deg‖ := by
    intro θ
    have hsat := hbPair_normalized hQ₀ θ
    have hcoeff_val : (airyPQF (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ)).coeff p_deg =
        (((hbPairQ P₀ Q₀ θ).coeff p_deg : ℝ) : ℂ) + I * (((hbPairP P₀ Q₀ θ).coeff p_deg : ℝ) : ℂ) := by
      unfold airyPQF
      simp only [Polynomial.coeff_add, Polynomial.coeff_map, Polynomial.coeff_C_mul,
        Complex.coe_algebraMap]
    rw [hcoeff_val]
    rcases Nat.mod_two_eq_zero_or_one m with he | ho
    · have hc_eq : c_lead = |Q₀.coeff ((m - 2) / 2)| := by dsimp [c_lead]; simp [he]
      have hp : p_deg = (m - 2) / 2 := by dsimp [p_deg]; simp [he]
      have hsatQ := hsat.2.2
      change (if m % 2 = 1 then _ else (hbPairQ P₀ Q₀ θ).coeff ((m - 2) / 2) = Q₀.coeff ((m - 2) / 2)) at hsatQ
      rw [if_neg (by omega)] at hsatQ
      rw [hc_eq, hp, ← hsatQ]
      simpa using Complex.abs_re_le_norm
        ((((hbPairQ P₀ Q₀ θ).coeff ((m - 2) / 2) : ℝ) : ℂ) +
          I * (((hbPairP P₀ Q₀ θ).coeff ((m - 2) / 2) : ℝ) : ℂ))
    · have hc_eq : c_lead = |P₀.coeff ((m - 1) / 2)| := by dsimp [c_lead]; simp [ho]
      have hp : p_deg = (m - 1) / 2 := by dsimp [p_deg]; simp [ho]
      have hsatP := hsat.2.2
      change (if m % 2 = 1 then (hbPairP P₀ Q₀ θ).coeff ((m - 1) / 2) = P₀.coeff ((m - 1) / 2) else _) at hsatP
      rw [if_pos ho] at hsatP
      rw [hc_eq, hp, ← hsatP]
      simpa using Complex.abs_im_le_norm
        ((((hbPairQ P₀ Q₀ θ).coeff ((m - 1) / 2) : ℝ) : ℂ) +
          I * (((hbPairP P₀ Q₀ θ).coeff ((m - 1) / 2) : ℝ) : ℂ))
  let d_max := max ((m - 1) / 2) ((m - 2) / 2)
  let C_c := Finset.sup' (Finset.range (d_max + 1))
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩ (fun k => max |P₀.coeff k| |Q₀.coeff k|) + 1
  let R_root : ℝ := max 1 (2 * ((p_deg : ℝ) + 1) * C_c / c_lead) + 1
  have hroot_bd : ∀ θ : HbParam P₀ Q₀, ‖θ‖ ≤ 1 → ∀ z : ℂ,
      airyPQc (hbPairQ P₀ Q₀ θ) z + I * airyPQc (hbPairP P₀ Q₀ θ) z = 0 → ‖z‖ ≤ R_root := by
    intro θ hθ z hz
    by_contra hgt
    push Not at hgt
    have hz1 : 1 < ‖z‖ := lt_of_le_of_lt
      (by linarith [le_max_left 1 (2 * ((p_deg : ℝ) + 1) * C_c / c_lead)]) hgt
    have hz_pos : 0 < ‖z‖ := by linarith
    have hFz : (airyPQF (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ)).eval z = 0 := by rwa [airyPQF_eval]
    have hsum := Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hF_deg θ).le) (x := z)
      (p := airyPQF (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ))
    rw [Finset.sum_range_succ, hFz] at hsum
    have hlead : -((airyPQF (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ)).coeff p_deg * z ^ p_deg) =
        ∑ k ∈ Finset.range p_deg,
          (airyPQF (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ)).coeff k * z ^ k := by
      exact neg_eq_iff_add_eq_zero.mpr (by rw [add_comm]; exact hsum.symm)
    obtain ⟨hPc, hQc⟩ := hbPair_coeff_bound hQ₀ θ hθ
    have hF_c_bd : ∀ k : ℕ, ‖(airyPQF (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ)).coeff k‖ ≤ 2 * C_c := by
      intro k
      unfold airyPQF
      simp only [Polynomial.coeff_add, Polynomial.coeff_map, Polynomial.coeff_C_mul,
        Complex.coe_algebraMap]
      calc ‖((hbPairQ P₀ Q₀ θ).coeff k : ℂ) + I * ((hbPairP P₀ Q₀ θ).coeff k : ℂ)‖
          ≤ ‖((hbPairQ P₀ Q₀ θ).coeff k : ℂ)‖ + ‖I * ((hbPairP P₀ Q₀ θ).coeff k : ℂ)‖ := norm_add_le _ _
        _ = |(hbPairQ P₀ Q₀ θ).coeff k| + |(hbPairP P₀ Q₀ θ).coeff k| := by
            simp [Complex.norm_real]
        _ ≤ C_c + C_c := add_le_add (hQc k) (hPc k)
        _ = 2 * C_c := by ring
    have hC_nn : 0 ≤ C_c := le_trans (abs_nonneg _) (hPc 0)
    have h_norm_eq := congrArg norm hlead
    rw [norm_neg, norm_mul, norm_pow] at h_norm_eq
    have hlhs : c_lead * ‖z‖ ^ p_deg ≤
        ‖(airyPQF (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ)).coeff p_deg‖ * ‖z‖ ^ p_deg :=
      mul_le_mul_of_nonneg_right (hF_lead_ge θ) (pow_nonneg hz_pos.le _)
    have hrhs : ‖∑ k ∈ Finset.range p_deg,
        (airyPQF (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ)).coeff k * z ^ k‖ ≤
        (p_deg : ℝ) * (2 * C_c) * ‖z‖ ^ (p_deg - 1) := by
      calc ‖∑ k ∈ Finset.range p_deg, _‖
          ≤ ∑ k ∈ Finset.range p_deg, ‖(airyPQF _ _).coeff k * z ^ k‖ := norm_sum_le _ _
        _ = ∑ k ∈ Finset.range p_deg, ‖(airyPQF _ _).coeff k‖ * ‖z‖ ^ k := by
            refine Finset.sum_congr rfl fun k _ => by rw [norm_mul, norm_pow]
        _ ≤ ∑ _k ∈ Finset.range p_deg, (2 * C_c) * ‖z‖ ^ (p_deg - 1) := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hk_lt : k < p_deg := Finset.mem_range.mp hk
            exact mul_le_mul (hF_c_bd k) (pow_le_pow_right₀ hz1.le (Nat.le_pred_of_lt hk_lt))
              (pow_nonneg hz_pos.le _) (by positivity)
        _ = (p_deg : ℝ) * (2 * C_c) * ‖z‖ ^ (p_deg - 1) := by
            simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    have hp_pos : 1 ≤ p_deg := by
      by_contra h0
      have hp0 : p_deg = 0 := by omega
      rw [hp0] at hlead
      simp only [pow_zero, mul_one, Finset.range_zero, Finset.sum_empty] at hlead
      have hne0 : (airyPQF (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ)).coeff 0 ≠ 0 := by
        intro hzero
        have := hF_lead_ge θ
        rw [hp0, hzero, norm_zero] at this
        linarith
      exact hne0 (neg_eq_zero.mp hlead)
    have hp_eq : ‖z‖ ^ p_deg = ‖z‖ ^ (p_deg - 1) * ‖z‖ := by
      conv_lhs => rw [show p_deg = (p_deg - 1) + 1 by omega, pow_succ]
    have hp_pow_pos : 0 < ‖z‖ ^ (p_deg - 1) := pow_pos hz_pos _
    have h_div : c_lead * ‖z‖ ≤ (p_deg : ℝ) * (2 * C_c) := by
      have h1 : c_lead * ‖z‖ * ‖z‖ ^ (p_deg - 1) ≤ (p_deg : ℝ) * (2 * C_c) * ‖z‖ ^ (p_deg - 1) := by
        calc c_lead * ‖z‖ * ‖z‖ ^ (p_deg - 1) = c_lead * ‖z‖ ^ p_deg := by rw [hp_eq]; ring
          _ ≤ ‖∑ k ∈ Finset.range p_deg, (airyPQF _ _).coeff k * z ^ k‖ := by linarith
          _ ≤ (p_deg : ℝ) * (2 * C_c) * ‖z‖ ^ (p_deg - 1) := hrhs
      exact le_of_mul_le_mul_right h1 hp_pow_pos
    have hR2 : 2 * ((p_deg : ℝ) + 1) * C_c / c_lead < ‖z‖ :=
      lt_of_le_of_lt (by linarith [le_max_right 1 (2 * ((p_deg : ℝ) + 1) * C_c / c_lead)]) hgt
    have h2 : 2 * ((p_deg : ℝ) + 1) * C_c < c_lead * ‖z‖ := by
      rw [mul_comm]
      exact (div_lt_iff₀ hc_lead_pos).mp hR2
    nlinarith
  have h_open_hb : ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ θ : HbParam P₀ Q₀, ‖θ‖ < η₁ →
      AiryPQHB (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) := by
    by_contra hcon
    push Not at hcon
    have hex : ∀ n : ℕ, ∃ θ : HbParam P₀ Q₀, ‖θ‖ < min 1 (1 / ((n : ℝ) + 1)) ∧
        ∃ z : ℂ, airyPQc (hbPairQ P₀ Q₀ θ) z + I * airyPQc (hbPairP P₀ Q₀ θ) z = 0 ∧ 0 ≤ z.im := by
      intro n
      obtain ⟨θ, hθ, hnot⟩ := hcon (min 1 (1 / ((n : ℝ) + 1))) (by positivity)
      refine ⟨θ, hθ, ?_⟩
      by_contra hno; push Not at hno; exact hnot hno
    choose θ hθ z hz_eq hz_im using hex
    have hz_in : ∀ n : ℕ, z n ∈ closedBall (0 : ℂ) R_root := fun n =>
      mem_closedBall_zero_iff.mpr (hroot_bd (θ n) ((hθ n).le.trans (min_le_left _ _)) (z n) (hz_eq n))
    obtain ⟨z₀, _, φ, hφ, hφ_lim⟩ := (isCompact_closedBall (0 : ℂ) R_root).isSeqCompact hz_in
    have hθ_tend : Tendsto (fun k : ℕ => θ (φ k)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun k =>
        ((hθ (φ k)).le.trans (min_le_right _ _)).trans ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact div_le_div_of_nonneg_left zero_le_one (by positivity)
        (by exact_mod_cast Nat.add_le_add_right (hφ.id_le k) 1)
    have h_cont_fn : Continuous (fun p : ℂ × HbParam P₀ Q₀ =>
        airyPQc (hbPairQ P₀ Q₀ p.2) p.1 + I * airyPQc (hbPairP P₀ Q₀ p.2) p.1) := by
      have hdP_cont : Continuous (fun p : ℂ × HbParam P₀ Q₀ =>
          airyPQc (hbDeltaP P₀ Q₀ p.2.1) p.1) := by
        have heq : (fun p : ℂ × HbParam P₀ Q₀ => airyPQc (hbDeltaP P₀ Q₀ p.2.1) p.1) =
            fun p => ∑ j : Fin (hbFreeP P₀ Q₀), ((p.2.1 j : ℝ) : ℂ) * p.1 ^ (j : ℕ) := by
          ext p
          unfold airyPQc hbDeltaP
          simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
            Polynomial.map_X, Complex.coe_algebraMap, poly_eval_sum', Polynomial.eval_mul,
            Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
        rw [heq]
        refine continuous_sum' _ fun j _ =>
          (Complex.continuous_ofReal.comp ((continuous_apply j).comp
            (continuous_fst.comp continuous_snd))).mul (continuous_fst.pow _)
      have hdQ_cont : Continuous (fun p : ℂ × HbParam P₀ Q₀ =>
          airyPQc (hbDeltaQ P₀ Q₀ p.2.2) p.1) := by
        have heq : (fun p : ℂ × HbParam P₀ Q₀ => airyPQc (hbDeltaQ P₀ Q₀ p.2.2) p.1) =
            fun p => ∑ k : Fin (hbFreeQ P₀ Q₀), ((p.2.2 k : ℝ) : ℂ) * p.1 ^ (k : ℕ) := by
          ext p
          unfold airyPQc hbDeltaQ
          simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
            Polynomial.map_X, Complex.coe_algebraMap, poly_eval_sum', Polynomial.eval_mul,
            Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
        rw [heq]
        refine continuous_sum' _ fun k _ =>
          (Complex.continuous_ofReal.comp ((continuous_apply k).comp
            (continuous_snd.comp continuous_snd))).mul (continuous_fst.pow _)
      have hQ_cont : Continuous (fun p : ℂ × HbParam P₀ Q₀ => airyPQc (hbPairQ P₀ Q₀ p.2) p.1) := by
        have heq : (fun p : ℂ × HbParam P₀ Q₀ => airyPQc (hbPairQ P₀ Q₀ p.2) p.1) =
            fun p => airyPQc Q₀ p.1 + airyPQc (hbDeltaQ P₀ Q₀ p.2.2) p.1 := by
          ext p; rw [hbPairQ, airyPQc_add]
        rw [heq]
        exact ((differentiable_airyPQc Q₀).continuous.comp continuous_fst).add hdQ_cont
      have hP_cont : Continuous (fun p : ℂ × HbParam P₀ Q₀ => airyPQc (hbPairP P₀ Q₀ p.2) p.1) := by
        have heq : (fun p : ℂ × HbParam P₀ Q₀ => airyPQc (hbPairP P₀ Q₀ p.2) p.1) =
            fun p => airyPQc P₀ p.1 + airyPQc (hbDeltaP P₀ Q₀ p.2.1) p.1 := by
          ext p; rw [hbPairP, airyPQc_add]
        rw [heq]
        exact ((differentiable_airyPQc P₀).continuous.comp continuous_fst).add hdP_cont
      exact hQ_cont.add (continuous_const.mul hP_cont)
    have hF_lim : Tendsto (fun k : ℕ =>
        airyPQc (hbPairQ P₀ Q₀ (θ (φ k))) (z (φ k)) +
          I * airyPQc (hbPairP P₀ Q₀ (θ (φ k))) (z (φ k))) atTop
        (𝓝 (airyPQc Q₀ z₀ + I * airyPQc P₀ z₀)) := by
      have hp_lim : Tendsto (fun k : ℕ => (z (φ k), θ (φ k))) atTop (𝓝 (z₀, (0 : HbParam P₀ Q₀))) :=
        hφ_lim.prodMk_nhds hθ_tend
      have h0_eq : (hbPairP P₀ Q₀ (0 : HbParam P₀ Q₀)) = P₀ ∧
          (hbPairQ P₀ Q₀ (0 : HbParam P₀ Q₀)) = Q₀ := by
        simp [hbPairP, hbPairQ, hbDeltaP, hbDeltaQ]
      have h_lim := h_cont_fn.continuousAt.tendsto.comp hp_lim
      rw [h0_eq.1, h0_eq.2] at h_lim
      exact h_lim
    have hz₀_eq : airyPQc Q₀ z₀ + I * airyPQc P₀ z₀ = 0 :=
      tendsto_nhds_unique hF_lim (by simp [hz_eq])
    have hz₀_im : 0 ≤ z₀.im := ge_of_tendsto (Complex.continuous_im.continuousAt.tendsto.comp hφ_lim)
      (Eventually.of_forall fun k => hz_im (φ k))
    linarith [hHB₀ z₀ hz₀_eq]
  obtain ⟨η₁, hη₁_pos, hη₁⟩ := h_open_hb
  have h_open_Q : ∃ η₂ : ℝ, 0 < η₂ ∧ ∀ θ : HbParam P₀ Q₀, ‖θ‖ < η₂ →
      hbPairQ P₀ Q₀ θ ≠ 0 ∧ at47_m (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) = m := by
    rcases Nat.mod_two_eq_zero_or_one m with he | ho
    · refine ⟨1, one_pos, fun θ _ => ?_⟩
      have hsatQ := (hbPair_normalized hQ₀ θ).2.2
      change (if m % 2 = 1 then _ else (hbPairQ P₀ Q₀ θ).coeff ((m - 2) / 2) = Q₀.coeff ((m - 2) / 2)) at hsatQ
      rw [if_neg (by omega)] at hsatQ
        have hQ_ne : hbPairQ P₀ Q₀ θ ≠ 0 := fun h0 => by
          rw [h0, Polynomial.coeff_zero] at hsatQ; exact (heven₀ he).2 hsatQ.symm
        have hQ_deg : (hbPairQ P₀ Q₀ θ).natDegree = (m - 2) / 2 :=
          le_antisymm (hbPairQ_natDegree_le hQ₀ θ)
            (Polynomial.le_natDegree_of_ne_zero (by rw [hsatQ]; exact (heven₀ he).2))
        have hP_deg := hbPairP_natDegree_le hQ₀ θ
        refine ⟨hQ_ne, ?_⟩
        unfold at47_m; omega
    · let k₀ := Q₀.natDegree
      have hQ0_k₀ : Q₀.coeff k₀ ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ₀
      refine ⟨|Q₀.coeff k₀|, abs_pos.mpr hQ0_k₀, fun θ hθ => ?_⟩
      have hk₀_lt : k₀ < hbFreeQ P₀ Q₀ := by
        unfold hbFreeQ
        change k₀ < if m % 2 = 1 then (m - 2) / 2 + 1 else (m - 2) / 2
        simp [ho]; omega
      let j₀ : Fin (hbFreeQ P₀ Q₀) := ⟨k₀, hk₀_lt⟩
      have hcoeff_Q : (hbPairQ P₀ Q₀ θ).coeff k₀ = Q₀.coeff k₀ + θ.2 j₀ := by
        rw [hbPairQ, Polynomial.coeff_add]; congr 1; unfold hbDeltaQ
        rw [poly_coeff_sum']
        rw [Finset.sum_eq_single j₀]
        · simp [j₀]
        · intro b _ hbj; simp [show k₀ ≠ (b : ℕ) from fun he => hbj (Fin.ext he.symm)]
        · intro hj; exact absurd (Finset.mem_univ j₀) hj
      have hθ_bd : |θ.2 j₀| < |Q₀.coeff k₀| :=
        lt_of_le_of_lt ((by simpa [Real.norm_eq_abs] using norm_le_pi_norm θ.2 j₀ :
          |θ.2 j₀| ≤ ‖θ.2‖).trans (norm_snd_le θ)) hθ
      have hQ_ne : hbPairQ P₀ Q₀ θ ≠ 0 := fun h0 => by
        rw [h0, Polynomial.coeff_zero] at hcoeff_Q
        have hneg : θ.2 j₀ = -Q₀.coeff k₀ := by linarith
        rw [hneg, abs_neg] at hθ_bd
        exact lt_irrefl _ hθ_bd
      have hsatP := (hbPair_normalized hQ₀ θ).2.2
      change (if m % 2 = 1 then (hbPairP P₀ Q₀ θ).coeff ((m - 1) / 2) = P₀.coeff ((m - 1) / 2) else _) at hsatP
      rw [if_pos ho] at hsatP
      have hP_deg : (hbPairP P₀ Q₀ θ).natDegree = (m - 1) / 2 :=
        le_antisymm (hbPairP_natDegree_le hQ₀ θ)
          (Polynomial.le_natDegree_of_ne_zero (by rw [hsatP]; exact (hodd₀ ho).2))
      have hQ_deg := hbPairQ_natDegree_le hQ₀ θ
      refine ⟨hQ_ne, ?_⟩
      unfold at47_m; omega
  obtain ⟨η₂, hη₂_pos, hη₂⟩ := h_open_Q
  exact ⟨min η₁ η₂, lt_min hη₁_pos hη₂_pos, fun θ hθ =>
    ⟨hη₁ θ (hθ.trans_le (min_le_left _ _)), hη₂ θ (hθ.trans_le (min_le_right _ _))⟩⟩

/-- Uniform large-`x` nonvanishing of `N_θ(x)` for all `‖θ‖ ≤ 1`. -/
lemma hbPair_tail_no_zero {P₀ Q₀ : ℝ[X]} (hHB₀ : AiryPQHB P₀ Q₀) (hQ₀ : Q₀ ≠ 0) :
    ∃ Tinf : ℝ, (∀ s ∈ hbTopZeros hHB₀ hQ₀, s + 1 ≤ Tinf) ∧ 4 ≤ Tinf ∧
      ∀ θ : HbParam P₀ Q₀, ‖θ‖ ≤ 1 → ∀ x : ℝ, Tinf ≤ x →
        airyPQN (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) (x : ℂ) ≠ 0 := by
  have hm2 : 2 ≤ at47_m P₀ Q₀ := at47_m_ge_two P₀ Q₀ hQ₀
  obtain ⟨hP₀_deg, hQ₀_deg, _, hodd₀, heven₀⟩ := at47_degP_degQ_bounds P₀ Q₀ hQ₀
  set m := at47_m P₀ Q₀
  let S₀ := hbTopZeros hHB₀ hQ₀
  let tm₀ := hbMinZero hHB₀ hQ₀
  have htm₀_mem : tm₀ ∈ S₀ := (hbTopZeros_spec hHB₀ hQ₀).2.2.2.1
  let R_top : ℝ := S₀.sup' ⟨tm₀, htm₀_mem⟩ (fun s => |s|) + 2
  have hR_top : ∀ s ∈ S₀, s + 1 ≤ R_top := fun s hs => by
    have : |s| ≤ S₀.sup' ⟨tm₀, htm₀_mem⟩ (fun t => |t|) := Finset.le_sup' (fun t => |t|) hs
    dsimp [R_top]; linarith [le_abs_self s]
  let d_max := max ((m - 1) / 2) ((m - 2) / 2)
  have h0_mem : 0 ∈ Finset.range (d_max + 1) := Finset.mem_range.mpr (Nat.zero_lt_succ _)
  let C_c := Finset.sup' (Finset.range (d_max + 1)) ⟨0, h0_mem⟩ (fun k => max |P₀.coeff k| |Q₀.coeff k|) + 1
  have hC_pos : 0 < C_c := by
    have hsup : 0 ≤ (Finset.range (d_max + 1)).sup' ⟨0, h0_mem⟩ (fun k => max |P₀.coeff k| |Q₀.coeff k|) :=
      le_trans (le_trans (abs_nonneg _) (le_max_left _ _))
        (Finset.le_sup' (fun k => max |P₀.coeff k| |Q₀.coeff k|) h0_mem)
    dsimp [C_c]; linarith
  rcases Nat.mod_two_eq_zero_or_one m with he | ho
  · set p := (m - 2) / 2
    set c₀ := |Q₀.coeff p|
    have hc₀ : 0 < c₀ := abs_pos.mpr (heven₀ he).2
    let B_thr : ℝ := max (max R_top 4) ((4 * (((p : ℝ) + 1) * C_c) / c₀ + 1) ^ 2)
    refine ⟨B_thr, fun s hs => (hR_top s hs).trans (le_trans (le_max_left _ _) (le_max_left _ _)),
      le_trans (le_max_right _ _) (le_max_left _ _), fun θ hθ x hx => ?_⟩
    have hx4 : 4 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have hx1 : 1 ≤ x := by linarith
    have hx0 : 0 < x := by linarith
    have hAi_pos : 0 < airyAi x := airyAi_pos hx0.le
    have hricc := riccG_sub_sqrt_le hx1
    have hricc_lb : √x / 2 ≤ riccG x := by
      have hsq2 : 2 ≤ √x := by rw [show (2 : ℝ) = √4 by norm_num]; exact Real.sqrt_le_sqrt hx4
      have h1 : √x - 22 / 43 / x ≤ riccG x := by linarith [(abs_le.mp hricc).1]
      have h2 : 22 / 43 / x ≤ 1 := div_le_one_of_le₀ (by linarith) hx0.le
      linarith
    obtain ⟨hPc, hQc⟩ := hbPair_coeff_bound hQ₀ θ hθ
    have hP_deg : (hbPairP P₀ Q₀ θ).natDegree ≤ p := by
      have := hbPairP_natDegree_le hQ₀ θ; omega
    have hP_le : |(hbPairP P₀ Q₀ θ).eval x| ≤ ((p : ℝ) + 1) * C_c * x ^ p :=
      poly_sum_eval_abs_le _ hP_deg (fun k _ => hPc k) hx1
    have hQ_deg : (hbPairQ P₀ Q₀ θ).natDegree ≤ p := hbPairQ_natDegree_le hQ₀ θ
    have hsatQ := (hbPair_normalized hQ₀ θ).2.2
    change (if m % 2 = 1 then _ else (hbPairQ P₀ Q₀ θ).coeff ((m - 2) / 2) = Q₀.coeff ((m - 2) / 2)) at hsatQ
    rw [if_neg (by omega)] at hsatQ
    have hQ_low := poly_lower_of_lead (hbPairQ P₀ Q₀ θ) hQ_deg hQc hx1
    rw [hsatQ] at hQ_low
    have h_sqrt_gt : 4 * (((p : ℝ) + 1) * C_c) / c₀ < √x := by
      have hpos : 0 < 4 * (((p : ℝ) + 1) * C_c) / c₀ + 1 := by positivity
      have hsq_le : (4 * (((p : ℝ) + 1) * C_c) / c₀ + 1) ^ 2 ≤ x :=
        le_trans (le_max_right _ _) hx
      have := Real.sqrt_le_sqrt hsq_le
      rw [Real.sqrt_sq hpos.le] at this
      linarith
    have h_coeff_half : c₀ / 2 ≤ c₀ - (p : ℝ) * C_c / x := by
      have hsq1 : √x ≤ x := by
        have h := Real.sqrt_le_sqrt (by nlinarith : x ≤ x ^ 2)
        rwa [Real.sqrt_sq hx0.le] at h
      have h_div : (p : ℝ) * C_c / x ≤ c₀ / 2 := by
        rw [div_le_iff₀ hx0]
        have h1 : 4 * (((p : ℝ) + 1) * C_c) < c₀ * √x := (div_lt_iff₀ hc₀).mp h_sqrt_gt
        nlinarith [hC_pos.le]
      linarith
    have hQ_ge : (c₀ / 2) * x ^ p ≤ |(hbPairQ P₀ Q₀ θ).eval x| :=
      le_trans (mul_le_mul_of_nonneg_right h_coeff_half (pow_nonneg hx0.le _)) hQ_low
    have h_dom : |(hbPairP P₀ Q₀ θ).eval x| < |(hbPairQ P₀ Q₀ θ).eval x * riccG x| := by
      have h1 : ((p : ℝ) + 1) * C_c < (c₀ / 4) * √x := by
        have := (div_lt_iff₀ hc₀).mp h_sqrt_gt
        linarith
      have hx_pow_pos : 0 < x ^ p := pow_pos hx0 _
      have h_ricc_pos : 0 < √x / 2 := by positivity
      calc |(hbPairP P₀ Q₀ θ).eval x|
          ≤ ((p : ℝ) + 1) * C_c * x ^ p := hP_le
        _ < ((c₀ / 4) * √x) * x ^ p := mul_lt_mul_of_pos_right h1 hx_pow_pos
        _ = ((c₀ / 2) * x ^ p) * (√x / 2) := by ring
        _ ≤ |(hbPairQ P₀ Q₀ θ).eval x| * riccG x :=
            mul_le_mul hQ_ge hricc_lb h_ricc_pos.le (abs_nonneg _)
        _ ≤ |(hbPairQ P₀ Q₀ θ).eval x| * |riccG x| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (abs_nonneg _)
        _ = |(hbPairQ P₀ Q₀ θ).eval x * riccG x| := (abs_mul _ _).symm
    rw [airyPQN_ofReal]
    intro h0
    have hr := Complex.ofReal_eq_zero.mp h0
    have h_mul_Ai : (hbPairP P₀ Q₀ θ).eval x = (hbPairQ P₀ Q₀ θ).eval x * riccG x := by
      unfold riccG
      field_simp [hAi_pos.ne']
      linarith
    rw [h_mul_Ai] at h_dom
    exact lt_irrefl _ h_dom
  · set p := (m - 1) / 2
    have hp1 : 1 ≤ p := by omega
    set c₀ := |P₀.coeff p|
    have hc₀ : 0 < c₀ := abs_pos.mpr (hodd₀ ho).2
    let B_thr : ℝ := max (max R_top 4) ((4 * (p : ℝ) * C_c / c₀ + 1) ^ 2)
    refine ⟨B_thr, fun s hs => (hR_top s hs).trans (le_trans (le_max_left _ _) (le_max_left _ _)),
      le_trans (le_max_right _ _) (le_max_left _ _), fun θ hθ x hx => ?_⟩
    have hx4 : 4 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have hx1 : 1 ≤ x := by linarith
    have hx0 : 0 < x := by linarith
    have hAi_pos : 0 < airyAi x := airyAi_pos hx0.le
    have hricc := riccG_sub_sqrt_le hx1
    have hricc_ub : |riccG x| ≤ 2 * √x := by
      have hsq2 : 2 ≤ √x := by rw [show (2 : ℝ) = √4 by norm_num]; exact Real.sqrt_le_sqrt hx4
      have h22 : 22 / 43 / x ≤ 1 := div_le_one_of_le₀ (by linarith) hx0.le
      have h_pos : 0 ≤ riccG x := by linarith [(abs_le.mp hricc).1, hsq2, h22]
      have h_ub : riccG x ≤ √x + 22 / 43 / x := by linarith [(abs_le.mp hricc).2]
      have h2 : 22 / 43 / x ≤ √x := by linarith [hsq2, h22]
      rw [abs_of_nonneg h_pos]; linarith
    obtain ⟨hPc, hQc⟩ := hbPair_coeff_bound hQ₀ θ hθ
    have hP_deg : (hbPairP P₀ Q₀ θ).natDegree ≤ p := hbPairP_natDegree_le hQ₀ θ
    have hsatP := (hbPair_normalized hQ₀ θ).2.2
    change (if m % 2 = 1 then (hbPairP P₀ Q₀ θ).coeff ((m - 1) / 2) = P₀.coeff ((m - 1) / 2) else _) at hsatP
    rw [if_pos ho] at hsatP
    have hP_low := poly_lower_of_lead (hbPairP P₀ Q₀ θ) hP_deg hPc hx1
    rw [hsatP] at hP_low
    have hQ_deg : (hbPairQ P₀ Q₀ θ).natDegree ≤ p - 1 := by
      have := hbPairQ_natDegree_le hQ₀ θ; omega
    have hQ_le : |(hbPairQ P₀ Q₀ θ).eval x| ≤ (p : ℝ) * C_c * x ^ (p - 1) := by
      have h1 := poly_sum_eval_abs_le (hbPairQ P₀ Q₀ θ) hQ_deg (fun k _ => hQc k) hx1
      have hcast : ((p - 1 : ℕ) : ℝ) + 1 = p := by
        rw [Nat.cast_sub hp1]; simp
      rwa [hcast] at h1
    have h_sqrt_gt : 4 * (p : ℝ) * C_c / c₀ < √x := by
      have hpos : 0 < 4 * (p : ℝ) * C_c / c₀ + 1 := by positivity
      have hsq_le : (4 * (p : ℝ) * C_c / c₀ + 1) ^ 2 ≤ x := le_trans (le_max_right _ _) hx
      have := Real.sqrt_le_sqrt hsq_le
      rw [Real.sqrt_sq hpos.le] at this
      linarith
    have h_coeff_half : c₀ / 2 ≤ c₀ - (p : ℝ) * C_c / x := by
      have hsq1 : √x ≤ x := by
        have h := Real.sqrt_le_sqrt (by nlinarith : x ≤ x ^ 2)
        rwa [Real.sqrt_sq hx0.le] at h
      have h_div : (p : ℝ) * C_c / x ≤ c₀ / 2 := by
        rw [div_le_iff₀ hx0]
        have h1 : 4 * (p : ℝ) * C_c < c₀ * √x := (div_lt_iff₀ hc₀).mp h_sqrt_gt
        nlinarith [hC_pos.le]
      linarith
    have hP_ge : (c₀ / 2) * x ^ p ≤ |(hbPairP P₀ Q₀ θ).eval x| :=
      le_trans (mul_le_mul_of_nonneg_right h_coeff_half (pow_nonneg hx0.le _)) hP_low
    have h_dom : |(hbPairQ P₀ Q₀ θ).eval x * riccG x| < |(hbPairP P₀ Q₀ θ).eval x| := by
      have h1 : 2 * (p : ℝ) * C_c < (c₀ / 2) * √x := by
        have := (div_lt_iff₀ hc₀).mp h_sqrt_gt
        linarith
      have h_p_eq : x ^ p = √x * √x * x ^ (p - 1) := by
        have hp_pow : x ^ p = x * x ^ (p - 1) := by
          conv_lhs => rw [show p = (p - 1) + 1 by omega, pow_succ']
        rw [hp_pow, Real.mul_self_sqrt hx0.le]
      have h_pos_rem : 0 < √x * x ^ (p - 1) := mul_pos (Real.sqrt_pos.mpr hx0) (pow_pos hx0 _)
      calc |(hbPairQ P₀ Q₀ θ).eval x * riccG x|
          = |(hbPairQ P₀ Q₀ θ).eval x| * |riccG x| := abs_mul _ _
        _ ≤ ((p : ℝ) * C_c * x ^ (p - 1)) * (2 * √x) :=
            mul_le_mul hQ_le hricc_ub (abs_nonneg _) (by positivity)
        _ = (2 * (p : ℝ) * C_c) * (√x * x ^ (p - 1)) := by ring
        _ < ((c₀ / 2) * √x) * (√x * x ^ (p - 1)) := mul_lt_mul_of_pos_right h1 h_pos_rem
        _ = (c₀ / 2) * x ^ p := by rw [h_p_eq]; ring
        _ ≤ |(hbPairP P₀ Q₀ θ).eval x| := hP_ge
    rw [airyPQN_ofReal]
    intro h0
    have hr := Complex.ofReal_eq_zero.mp h0
    have h_mul_Ai : (hbPairP P₀ Q₀ θ).eval x = (hbPairQ P₀ Q₀ θ).eval x * riccG x := by
      unfold riccG
      field_simp [hAi_pos.ne']
      linarith
    rw [h_mul_Ai] at h_dom
    exact lt_irrefl _ h_dom

/-- Uniform Lipschitz bound on `|N_θ(x) - N₀(x)|` over any compact interval `[a, b]`. -/
private lemma hbPair_N_diff_bound (P₀ Q₀ : ℝ[X]) {a b : ℝ} (_hab : a ≤ b) :
    ∃ C_d : ℝ, 0 < C_d ∧ ∀ θ : HbParam P₀ Q₀, ∀ x ∈ Icc a b,
      |(airyPQN (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) (x : ℂ)).re - (airyPQN P₀ Q₀ (x : ℂ)).re| ≤
        C_d * ‖θ‖ := by
  obtain ⟨M_Ai, hM_Ai⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (airyAi_contDiff_omega.continuous.continuousOn (s := Icc a b))
  obtain ⟨M_Ai', hM_Ai'⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (airyAi'_contDiff_omega.continuous.continuousOn (s := Icc a b))
  let M_x := max |a| |b| + 1
  have hMx1 : 1 ≤ M_x := by dsimp [M_x]; linarith [abs_nonneg a, le_max_left |a| |b|]
  let d_max := max (hbFreeP P₀ Q₀) (hbFreeQ P₀ Q₀)
  let C_d := ((d_max : ℝ) + 1) * M_x ^ d_max * (max M_Ai 0 + max M_Ai' 0 + 1) + 1
  refine ⟨C_d, by positivity, fun θ x hx => ?_⟩
  have hx_bd : |x| ≤ M_x := by
    have : |x| ≤ max |a| |b| := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, neg_abs_le a, le_abs_self b,
        le_max_left |a| |b|, le_max_right |a| |b|]
    dsimp [M_x]; linarith
  have hpow_le : ∀ k : ℕ, k ≤ d_max → |x ^ k| ≤ M_x ^ d_max := fun k hk => by
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg _) hx_bd k).trans (pow_le_pow_right₀ hMx1 hk)
  have hdP_le : |(hbDeltaP P₀ Q₀ θ.1).eval x| ≤ (hbFreeP P₀ Q₀ : ℝ) * M_x ^ d_max * ‖θ‖ := by
    unfold hbDeltaP
    rw [poly_eval_sum']
    calc |∑ j : Fin (hbFreeP P₀ Q₀), (Polynomial.C (θ.1 j) * Polynomial.X ^ (j : ℕ)).eval x|
        ≤ ∑ j : Fin (hbFreeP P₀ Q₀), |θ.1 j * x ^ (j : ℕ)| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
            refine Finset.sum_congr rfl fun j _ => by simp
      _ ≤ ∑ _j : Fin (hbFreeP P₀ Q₀), ‖θ‖ * M_x ^ d_max := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul]
            have h1 : |θ.1 j| ≤ ‖θ‖ :=
              (by simpa [Real.norm_eq_abs] using norm_le_pi_norm θ.1 j : |θ.1 j| ≤ ‖θ.1‖).trans
                (norm_fst_le θ)
            have h2 := hpow_le j (by exact le_trans j.isLt.le (le_max_left _ _))
            exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
      _ = (hbFreeP P₀ Q₀ : ℝ) * M_x ^ d_max * ‖θ‖ := by
            simp [Finset.sum_const, nsmul_eq_mul]; ring
  have hdQ_le : |(hbDeltaQ P₀ Q₀ θ.2).eval x| ≤ (hbFreeQ P₀ Q₀ : ℝ) * M_x ^ d_max * ‖θ‖ := by
    unfold hbDeltaQ
    rw [poly_eval_sum']
    calc |∑ k : Fin (hbFreeQ P₀ Q₀), (Polynomial.C (θ.2 k) * Polynomial.X ^ (k : ℕ)).eval x|
        ≤ ∑ k : Fin (hbFreeQ P₀ Q₀), |θ.2 k * x ^ (k : ℕ)| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
            refine Finset.sum_congr rfl fun k _ => by simp
      _ ≤ ∑ _k : Fin (hbFreeQ P₀ Q₀), ‖θ‖ * M_x ^ d_max := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [abs_mul]
            have h1 : |θ.2 k| ≤ ‖θ‖ :=
              (by simpa [Real.norm_eq_abs] using norm_le_pi_norm θ.2 k : |θ.2 k| ≤ ‖θ.2‖).trans
                (norm_snd_le θ)
            have h2 := hpow_le k (by exact le_trans k.isLt.le (le_max_right _ _))
            exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
      _ = (hbFreeQ P₀ Q₀ : ℝ) * M_x ^ d_max * ‖θ‖ := by
            simp [Finset.sum_const, nsmul_eq_mul]; ring
  have hsub_eq : (airyPQN (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) (x : ℂ)).re -
      (airyPQN P₀ Q₀ (x : ℂ)).re =
      (hbDeltaP P₀ Q₀ θ.1).eval x * airyAi x + (hbDeltaQ P₀ Q₀ θ.2).eval x * airyAi' x := by
    rw [airyPQN_ofReal, airyPQN_ofReal, Complex.ofReal_re, Complex.ofReal_re]
    simp only [hbPairP, hbPairQ, Polynomial.eval_add]
    ring
  rw [hsub_eq]
  have hAi_bd : |airyAi x| ≤ max M_Ai 0 :=
    (by simpa [Real.norm_eq_abs] using hM_Ai x hx : |airyAi x| ≤ M_Ai).trans (le_max_left _ _)
  have hAi'_bd : |airyAi' x| ≤ max M_Ai' 0 :=
    (by simpa [Real.norm_eq_abs] using hM_Ai' x hx : |airyAi' x| ≤ M_Ai').trans (le_max_left _ _)
  calc |(hbDeltaP P₀ Q₀ θ.1).eval x * airyAi x + (hbDeltaQ P₀ Q₀ θ.2).eval x * airyAi' x|
      ≤ |(hbDeltaP P₀ Q₀ θ.1).eval x| * |airyAi x| + |(hbDeltaQ P₀ Q₀ θ.2).eval x| * |airyAi' x| :=
          (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul])
    _ ≤ ((d_max : ℝ) * M_x ^ d_max * ‖θ‖) * (max M_Ai 0) +
          ((d_max : ℝ) * M_x ^ d_max * ‖θ‖) * (max M_Ai' 0) := by
          have hd1 : (hbFreeP P₀ Q₀ : ℝ) ≤ d_max := by exact_mod_cast le_max_left _ _
          have hd2 : (hbFreeQ P₀ Q₀ : ℝ) ≤ d_max := by exact_mod_cast le_max_right _ _
          have hM1 : 0 ≤ max M_Ai 0 := le_max_right _ _
          have hM2 : 0 ≤ max M_Ai' 0 := le_max_right _ _
          have hp1 := hdP_le.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hd1 (by positivity)) (norm_nonneg _))
          have hp2 := hdQ_le.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hd2 (by positivity)) (norm_nonneg _))
          gcongr
    _ ≤ C_d * ‖θ‖ := by
          have hle : ((d_max : ℝ) * M_x ^ d_max * ‖θ‖) * (max M_Ai 0) +
              ((d_max : ℝ) * M_x ^ d_max * ‖θ‖) * (max M_Ai' 0) =
              ((d_max : ℝ) * M_x ^ d_max * (max M_Ai 0 + max M_Ai' 0)) * ‖θ‖ := by ring
          rw [hle]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          have h_main : (d_max : ℝ) * M_x ^ d_max * (max M_Ai 0 + max M_Ai' 0) ≤
              ((d_max : ℝ) + 1) * M_x ^ d_max * (max M_Ai 0 + max M_Ai' 0 + 1) := by
            gcongr <;> linarith [show 0 ≤ max M_Ai 0 + max M_Ai' 0 by positivity]
          exact h_main.trans (by dsimp [C_d]; linarith)

/-- Near `0 : HbParam P₀ Q₀`, any family of `m` zeros `(Z_m y, y i)` close to `(tm₀, i.1)` IS
`hbTopZeros` and `Z_m y` IS `hbMinZero`. -/
lemma hbPair_nodes_identify {P₀ Q₀ : ℝ[X]} (hHB₀ : AiryPQHB P₀ Q₀) (hQ₀ : Q₀ ≠ 0) :
    ∃ r η : ℝ, 0 < r ∧ 0 < η ∧
      ∀ θ : HbParam P₀ Q₀, ‖θ‖ < η →
        ∃ hHB_θ : AiryPQHB (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ),
        ∃ hQ_θ : hbPairQ P₀ Q₀ θ ≠ 0,
        at47_m (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) = at47_m P₀ Q₀ ∧
        ∀ (y : ↥((hbTopZeros hHB₀ hQ₀).erase (hbMinZero hHB₀ hQ₀)) → ℝ) (zm : ℝ),
          |zm - hbMinZero hHB₀ hQ₀| < r →
          (∀ i, |y i - i.1| < r) →
          airyPQN (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) (zm : ℂ) = 0 →
          (∀ i, airyPQN (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) (y i : ℂ) = 0) →
          (∀ i, zm < y i) ∧
          hbTopZeros hHB_θ hQ_θ = insert zm (Finset.univ.image y) ∧
            hbMinZero hHB_θ hQ_θ = zm := by
  classical
  let S₀ := hbTopZeros hHB₀ hQ₀
  let tm₀ := hbMinZero hHB₀ hQ₀
  have hs₀ := hbTopZeros_spec hHB₀ hQ₀
  obtain ⟨η_hb, hη_hb_pos, hη_hb⟩ := hbPair_open_hb hHB₀ hQ₀
  obtain ⟨Tinf, hT_top, hT4, hT_nz⟩ := hbPair_tail_no_zero hHB₀ hQ₀
  obtain ⟨δ_gap, hδ_gap_pos, h_gap⟩ := hb_nodes_min_gap hHB₀ hQ₀
  obtain ⟨δ_sub, hδ_sub_pos, h_sub⟩ := hb_sub_below_gap hHB₀ hQ₀
  let r₀ : ℝ := min (min (δ_gap / 3) (δ_sub / 3)) (1 / 2)
  have hr₀_pos : 0 < r₀ := by positivity
  -- Local injectivity / monotonicity radius around each `t ∈ S₀` using nonzero derivative `N₀'(t)`
  have h_loc_mono : ∀ t ∈ S₀, ∃ r_t η_t : ℝ, 0 < r_t ∧ 0 < η_t ∧ r_t ≤ r₀ ∧
      ∀ θ : HbParam P₀ Q₀, ‖θ‖ < η_t →
        Function.Injective (fun x : Icc (t - r_t) (t + r_t) =>
          (airyPQN (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) (x.1 : ℂ)).re) := by
    intro t ht
    have hN'0 : (airyPQN' P₀ Q₀ (t : ℂ)).re ≠ 0 := by
      have hzw := airyPQ_zero_weight_pos hHB₀ hQ₀ (hs₀.2.1 t ht)
      intro h0
      have := hzw.2
      rw [airyPQN'_ofReal, Complex.ofReal_re] at h0
      rw [airyPQN'_ofReal, h0] at this
      simp at this
    let N'_fn : ℝ × HbParam P₀ Q₀ → ℝ := fun p =>
      (airyPQN' (hbPairP P₀ Q₀ p.2) (hbPairQ P₀ Q₀ p.2) (p.1 : ℂ)).re
    have h_cont_N' : Continuous N'_fn := by
      have h_eq : N'_fn = fun p =>
          ((hbPairP P₀ Q₀ p.2).derivative.eval p.1 * airyAi p.1 +
            ((hbPairP P₀ Q₀ p.2).eval p.1 + (hbPairQ P₀ Q₀ p.2).derivative.eval p.1) * airyAi' p.1 +
            p.1 * (hbPairQ P₀ Q₀ p.2).eval p.1 * airyAi p.1) := by
        ext p; dsimp [N'_fn]; rw [airyPQN'_ofReal, Complex.ofReal_re]
      rw [h_eq]
      have hP_c : Continuous (fun p : ℝ × HbParam P₀ Q₀ => (hbPairP P₀ Q₀ p.2).eval p.1) := by
        have : (fun p : ℝ × HbParam P₀ Q₀ => (hbPairP P₀ Q₀ p.2).eval p.1) =
            fun p => P₀.eval p.1 + ∑ j : Fin (hbFreeP P₀ Q₀), p.2.1 j * p.1 ^ (j : ℕ) := by
          ext p
          simp only [hbPairP, hbDeltaP, Polynomial.eval_add, poly_eval_sum',
            Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
        rw [this]
        exact ((poly_continuous_eval' P₀).comp continuous_fst).add
          (continuous_sum' _ fun j _ =>
            ((continuous_apply j).comp (continuous_fst.comp continuous_snd)).mul (continuous_fst.pow _))
      have hQ_c : Continuous (fun p : ℝ × HbParam P₀ Q₀ => (hbPairQ P₀ Q₀ p.2).eval p.1) := by
        have : (fun p : ℝ × HbParam P₀ Q₀ => (hbPairQ P₀ Q₀ p.2).eval p.1) =
            fun p => Q₀.eval p.1 + ∑ k : Fin (hbFreeQ P₀ Q₀), p.2.2 k * p.1 ^ (k : ℕ) := by
          ext p
          simp only [hbPairQ, hbDeltaQ, Polynomial.eval_add, poly_eval_sum',
            Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
        rw [this]
        exact ((poly_continuous_eval' Q₀).comp continuous_fst).add
          (continuous_sum' _ fun k _ =>
            ((continuous_apply k).comp (continuous_snd.comp continuous_snd)).mul (continuous_fst.pow _))
      have hdP_c : Continuous (fun p : ℝ × HbParam P₀ Q₀ => (hbPairP P₀ Q₀ p.2).derivative.eval p.1) := by
        have : (fun p : ℝ × HbParam P₀ Q₀ => (hbPairP P₀ Q₀ p.2).derivative.eval p.1) =
            fun p => P₀.derivative.eval p.1 +
              ∑ j : Fin (hbFreeP P₀ Q₀), (j : ℝ) * p.2.1 j * p.1 ^ ((j : ℕ) - 1) := by
          ext p
          simp only [hbPairP, hbDeltaP, Polynomial.derivative_add, Polynomial.derivative_sum,
            Polynomial.derivative_C_mul_X_pow, Polynomial.eval_add, poly_eval_sum',
            Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X_pow]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [Polynomial.eval_natCast]
          ring
        rw [this]
        exact ((poly_continuous_eval' P₀.derivative).comp continuous_fst).add
          (continuous_sum' _ fun j _ =>
            (continuous_const.mul ((continuous_apply j).comp
              (continuous_fst.comp continuous_snd))).mul (continuous_fst.pow _))
      have hdQ_c : Continuous (fun p : ℝ × HbParam P₀ Q₀ => (hbPairQ P₀ Q₀ p.2).derivative.eval p.1) := by
        have : (fun p : ℝ × HbParam P₀ Q₀ => (hbPairQ P₀ Q₀ p.2).derivative.eval p.1) =
            fun p => Q₀.derivative.eval p.1 +
              ∑ k : Fin (hbFreeQ P₀ Q₀), (k : ℝ) * p.2.2 k * p.1 ^ ((k : ℕ) - 1) := by
          ext p
          simp only [hbPairQ, hbDeltaQ, Polynomial.derivative_add, Polynomial.derivative_sum,
            Polynomial.derivative_C_mul_X_pow, Polynomial.eval_add, poly_eval_sum',
            Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X_pow]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [Polynomial.eval_natCast]
          ring
        rw [this]
        exact ((poly_continuous_eval' Q₀.derivative).comp continuous_fst).add
          (continuous_sum' _ fun k _ =>
            (continuous_const.mul ((continuous_apply k).comp
              (continuous_snd.comp continuous_snd))).mul (continuous_fst.pow _))
      have hAi_c : Continuous airyAi := airyAi_contDiff_omega.continuous
      have hAi'_c : Continuous airyAi' := airyAi'_contDiff_omega.continuous
      exact ((hdP_c.mul (hAi_c.comp continuous_fst)).add
        ((hP_c.add hdQ_c).mul (hAi'_c.comp continuous_fst))).add
        ((continuous_fst.mul hQ_c).mul (hAi_c.comp continuous_fst))
    have h_ne0 : N'_fn (t, 0) ≠ 0 := by
      dsimp [N'_fn]
      have : hbPairP P₀ Q₀ 0 = P₀ ∧ hbPairQ P₀ Q₀ 0 = Q₀ := by
        simp [hbPairP, hbPairQ, hbDeltaP, hbDeltaQ]
      rwa [this.1, this.2]
    have h_nhds : {p : ℝ × HbParam P₀ Q₀ | N'_fn p ≠ 0} ∈ 𝓝 (t, (0 : HbParam P₀ Q₀)) :=
      h_cont_N'.continuousAt.eventually_ne h_ne0
    rw [nhds_prod_eq, Filter.mem_prod_iff] at h_nhds
    obtain ⟨U₁, hU₁, U₂, hU₂, hUsub⟩ := h_nhds
    obtain ⟨r_t', hr_t'_pos, hr_t'⟩ := Metric.mem_nhds_iff.mp hU₁
    obtain ⟨η_t, hη_t_pos, hη_t⟩ := Metric.mem_nhds_iff.mp hU₂
    let r_t := min (r_t' / 2) r₀
    have hr_t_pos : 0 < r_t := by positivity
    refine ⟨r_t, η_t, hr_t_pos, hη_t_pos, min_le_right _ _, fun θ hθ => ?_⟩
    have h_deriv_ne : ∀ x ∈ Icc (t - r_t) (t + r_t), N'_fn (x, θ) ≠ 0 := fun x hx => by
      have hx1 : x ∈ ball t r_t' := by
        rw [mem_ball, Real.dist_eq, abs_lt]
        have : r_t ≤ r_t' / 2 := min_le_left _ _
        constructor <;> linarith [hx.1, hx.2]
      have hθ2 : θ ∈ ball (0 : HbParam P₀ Q₀) η_t := by
        simpa [mem_ball, dist_zero_right] using hθ
      exact hUsub ⟨hr_t' hx1, hη_t hθ2⟩
    have h_deriv_fn : ∀ x : ℝ, HasDerivAt
        (fun y : ℝ => (airyPQN (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) (y : ℂ)).re)
        (N'_fn (x, θ)) x := fun x => by
      have hC := (hasDerivAt_airyPQN (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) (x : ℂ)).comp_ofReal
      simpa only [N'_fn] using hasDerivAt_re_comp hC
    have h_conn : IsConnected (Icc (t - r_t) (t + r_t)) := isConnected_Icc (by linarith)
    have h_no_zero_iv : (∀ x ∈ Icc (t - r_t) (t + r_t), 0 < N'_fn (x, θ)) ∨
        (∀ x ∈ Icc (t - r_t) (t + r_t), N'_fn (x, θ) < 0) := by
      have h_cont_x : ContinuousOn (fun y : ℝ => N'_fn (y, θ)) (Icc (t - r_t) (t + r_t)) :=
        (h_cont_N'.comp (continuous_id.prodMk continuous_const)).continuousOn
      have ht_in : t ∈ Icc (t - r_t) (t + r_t) := ⟨by linarith, by linarith⟩
      by_cases hsign : 0 < N'_fn (t, θ)
      · left; intro x hx
        by_contra hle
        have hlt : N'_fn (x, θ) < 0 := lt_of_le_of_ne (not_lt.mp hle) (h_deriv_ne x hx)
        have h_uIcc_sub : uIcc x t ⊆ Icc (t - r_t) (t + r_t) :=
          uIcc_subset_Icc hx ht_in
        obtain ⟨y, hy_mem, hy0⟩ := intermediate_value_uIcc (h_cont_x.mono h_uIcc_sub)
          (Set.mem_uIcc.mpr (Or.inl ⟨hlt.le, hsign.le⟩))
        exact h_deriv_ne y (h_uIcc_sub hy_mem) hy0
      · right
        have ht_neg : N'_fn (t, θ) < 0 := lt_of_le_of_ne (not_lt.mp hsign) (h_deriv_ne t ht_in)
        intro x hx
        by_contra hge
        have hgt : 0 < N'_fn (x, θ) := lt_of_le_of_ne (not_lt.mp hge) (h_deriv_ne x hx).symm
        have h_uIcc_sub : uIcc t x ⊆ Icc (t - r_t) (t + r_t) :=
          uIcc_subset_Icc ht_in hx
        obtain ⟨y, hy_mem, hy0⟩ := intermediate_value_uIcc (h_cont_x.mono h_uIcc_sub)
          (Set.mem_uIcc.mpr (Or.inl ⟨ht_neg.le, hgt.le⟩))
        exact h_deriv_ne y (h_uIcc_sub hy_mem) hy0
    have h_diff_on : ∀ x ∈ Icc (t - r_t) (t + r_t), HasDerivAt
        (fun y : ℝ => (airyPQN (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) (y : ℂ)).re)
        (N'_fn (x, θ)) x := fun x _ => h_deriv_fn x
    have h_cont_fn_y : ContinuousOn
        (fun y : ℝ => (airyPQN (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) (y : ℂ)).re)
        (Icc (t - r_t) (t + r_t)) :=
      fun y hy => (h_deriv_fn y).continuousAt.continuousWithinAt
    rcases h_no_zero_iv with hpos | hneg
    · have hsm : StrictMonoOn
          (fun y : ℝ => (airyPQN (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) (y : ℂ)).re)
          (Icc (t - r_t) (t + r_t)) :=
        strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) h_cont_fn_y
          (fun x hx => (h_deriv_fn x).hasDerivWithinAt)
          (fun x hx => hpos x (interior_subset hx))
      exact fun a b hab => Subtype.ext (hsm.injOn a.2 b.2 hab)
    · have hsa : StrictAntiOn
          (fun y : ℝ => (airyPQN (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) (y : ℂ)).re)
          (Icc (t - r_t) (t + r_t)) :=
        strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _) h_cont_fn_y
          (fun x hx => (h_deriv_fn x).hasDerivWithinAt)
          (fun x hx => hneg x (interior_subset hx))
      exact fun a b hab => Subtype.ext (hsa.injOn a.2 b.2 hab)
  have hS₀_ne : S₀.Nonempty := ⟨tm₀, hs₀.2.2.2.1⟩
  choose r_t η_t hr_pos hη_pos hr_le h_mono using h_loc_mono
  let r_unif : ℝ := S₀.inf' hS₀_ne fun t => if ht : t ∈ S₀ then r_t t ht else 1
  have hr_unif_pos : 0 < r_unif := by
    rw [Finset.lt_inf'_iff]
    intro t ht
    simpa [ht] using hr_pos t ht
  have hr_unif_le_r₀ : r_unif ≤ r₀ := by
    have := Finset.inf'_le (f := fun t => if ht : t ∈ S₀ then r_t t ht else 1) hs₀.2.2.2.1
    simp only [hs₀.2.2.2.1, ↓reduceDIte] at this
    exact this.trans (hr_le tm₀ hs₀.2.2.2.1)
  let r : ℝ := r_unif / 2
  have hr_pos' : 0 < r := half_pos hr_unif_pos
  have hr_lt_r₀ : r < r₀ := by dsimp [r]; linarith [hr_unif_pos, hr_unif_le_r₀]
  let η_loc : ℝ := S₀.inf' hS₀_ne fun t => if ht : t ∈ S₀ then η_t t ht else 1
  have hη_loc_pos : 0 < η_loc := by
    rw [Finset.lt_inf'_iff]
    intro t ht
    simpa [ht] using hη_pos t ht
  have h_inj_interval : ∀ θ : HbParam P₀ Q₀, ‖θ‖ < η_loc → ∀ t ∈ S₀,
      ∀ x₁ x₂ : ℝ, x₁ ∈ Icc (t - r) (t + r) → x₂ ∈ Icc (t - r) (t + r) →
        airyPQN (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) (x₁ : ℂ) = 0 →
        airyPQN (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) (x₂ : ℂ) = 0 → x₁ = x₂ := by
    intro θ hθ t ht x₁ x₂ hx₁ hx₂ hz₁ hz₂
    have hη_le : η_loc ≤ η_t t ht := by
      simpa [ht] using Finset.inf'_le (f := fun s => if hs : s ∈ S₀ then η_t s hs else 1) ht
    have hr_le_rt : r ≤ r_t t ht := by
      have := Finset.inf'_le (f := fun s => if hs : s ∈ S₀ then r_t s hs else 1) ht
      simp only [ht, ↓reduceDIte] at this
      dsimp [r]; linarith
    have hx₁' : x₁ ∈ Icc (t - r_t t ht) (t + r_t t ht) := ⟨by linarith [hx₁.1], by linarith [hx₁.2]⟩
    have hx₂' : x₂ ∈ Icc (t - r_t t ht) (t + r_t t ht) := ⟨by linarith [hx₂.1], by linarith [hx₂.2]⟩
    have h_inj := h_mono t ht θ (hθ.trans_le hη_le)
    have h_eq_re : (airyPQN (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) (x₁ : ℂ)).re =
        (airyPQN (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) (x₂ : ℂ)).re := by
      rw [hz₁, hz₂]
    have h_eq_sub : (⟨x₁, hx₁'⟩ : Icc (t - r_t t ht) (t + r_t t ht)) = ⟨x₂, hx₂'⟩ := h_inj h_eq_re
    exact congrArg Subtype.val h_eq_sub
  -- Nonvanishing on `K_out = [tm₀ - δ_sub / 2, Tinf] \ ⋃_{t ∈ S₀} (t - r, t + r)`
  let K_out : Set ℝ := Icc (tm₀ - δ_sub / 2) Tinf ∩ ⋂ t ∈ S₀, {x : ℝ | r ≤ |x - t|}
  have hK_out_closed : IsClosed K_out :=
    isClosed_Icc.inter (isClosed_biInter fun t _ =>
      isClosed_le continuous_const (continuous_abs.comp (continuous_id.sub continuous_const)))
  have hK_out_compact : IsCompact K_out :=
    IsCompact.of_isClosed_subset isCompact_Icc hK_out_closed Set.inter_subset_left
  have h_N₀_cont : Continuous fun x : ℝ => |(airyPQN P₀ Q₀ (x : ℂ)).re| :=
    continuous_abs.comp (Complex.continuous_re.comp
      ((differentiable_airyPQN P₀ Q₀).continuous.comp continuous_ofReal))
  have h_N₀_pos_K : ∀ x ∈ K_out, 0 < |(airyPQN P₀ Q₀ (x : ℂ)).re| := by
    intro x hx
    refine abs_pos.mpr fun h0 => ?_
    have hxN : airyPQN P₀ Q₀ (x : ℂ) = 0 := by
      rw [airyPQN_ofReal, Complex.ofReal_re] at h0
      rw [airyPQN_ofReal]
      exact Complex.ofReal_eq_zero.mpr h0
    have hx_notin : x ∉ S₀ := fun hmem => by
      have hge := (Set.mem_iInter₂.mp hx.2 x hmem)
      rw [sub_self, abs_zero] at hge
      linarith
    have h_le_sub := h_sub x hxN hx_notin
    have h_ge_min := hx.1.1
    linarith
  have h_c_out : ∃ c_out : ℝ, 0 < c_out ∧ ∀ x ∈ K_out, c_out ≤ |(airyPQN P₀ Q₀ (x : ℂ)).re| := by
    by_cases hne : K_out.Nonempty
    · obtain ⟨x₀, hx₀, hmin⟩ := hK_out_compact.exists_isMinOn hne h_N₀_cont.continuousOn
      exact ⟨|(airyPQN P₀ Q₀ (x₀ : ℂ)).re|, h_N₀_pos_K x₀ hx₀, fun x hx => hmin hx⟩
    · refine ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩
  obtain ⟨c_out, hc_out_pos, hc_out⟩ := h_c_out
  -- Uniform bound on `|N_θ(x) - N₀(x)|` over `Icc (tm₀ - δ_sub / 2) Tinf`
  have h_N_diff : ∃ C_d : ℝ, 0 < C_d ∧ ∀ θ : HbParam P₀ Q₀, ∀ x ∈ Icc (tm₀ - δ_sub / 2) Tinf,
      |(airyPQN (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) (x : ℂ)).re - (airyPQN P₀ Q₀ (x : ℂ)).re| ≤
        C_d * ‖θ‖ :=
    hbPair_N_diff_bound P₀ Q₀ (by have := hT_top tm₀ hs₀.2.2.2.1; linarith)
  obtain ⟨C_d, hC_d_pos, h_N_diff_le⟩ := h_N_diff
  let η : ℝ := min (min η_hb η_loc) (min 1 (c_out / (2 * C_d)))
  have hη_pos : 0 < η := by positivity
  refine ⟨r, η, hr_pos', hη_pos, fun θ hθ => ?_⟩
  have hθ_hb : ‖θ‖ < η_hb := hθ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hθ_loc : ‖θ‖ < η_loc := hθ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hθ_1 : ‖θ‖ ≤ 1 := (hθ.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hθ_out : C_d * ‖θ‖ < c_out / 2 := by
    have hlt := hθ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have h1 := mul_lt_mul_of_pos_left hlt hC_d_pos
    have heq : C_d * (c_out / (2 * C_d)) = c_out / 2 := by field_simp [hC_d_pos.ne']
    linarith
  obtain ⟨hHB_θ, hQ_θ, hm_θ⟩ := hη_hb θ hθ_hb
  refine ⟨hHB_θ, hQ_θ, hm_θ, fun y zm hzm hy hzm0 hy0 => ?_⟩
  have h_gap_r : 3 * r ≤ δ_gap ∧ 3 * r ≤ δ_sub ∧ r ≤ 1 / 2 := by
    have hr_u : r < min (min (δ_gap / 3) (δ_sub / 3)) (1 / 2) := hr_lt_r₀
    refine ⟨?_, ?_, ?_⟩
    · linarith [hr_u.trans_le ((min_le_left _ _).trans (min_le_left _ _))]
    · linarith [hr_u.trans_le ((min_le_left _ _).trans (min_le_right _ _))]
    · linarith [hr_u.trans_le (min_le_right _ _)]
  -- Show `zm` and every `y i` belong to `[tm₀ - δ_sub / 2, Tinf]` and are pairwise separated
  have h_zm_lt_yi : ∀ i : ↥(S₀.erase tm₀), zm < y i := fun i => by
    have hi_ne : i.1 ≠ tm₀ := (Finset.mem_erase.mp i.2).1
    have hi_mem : i.1 ∈ S₀ := (Finset.mem_erase.mp i.2).2
    have htm_le : tm₀ ≤ i.1 := hs₀.2.2.2.2 i.1 hi_mem
    have h_g := h_gap tm₀ hs₀.2.2.2.1 i.1 hi_mem (Ne.symm hi_ne)
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htm_le)] at h_g
    linarith [abs_lt.mp hzm, abs_lt.mp (hy i), h_gap_r.1]
  have h_yi_inj : Function.Injective y := fun i j hij => by
    by_contra hne
    have hne1 : i.1 ≠ j.1 := fun h => hne (Subtype.ext h)
    have hi_mem : i.1 ∈ S₀ := (Finset.mem_erase.mp i.2).2
    have hj_mem : j.1 ∈ S₀ := (Finset.mem_erase.mp j.2).2
    have h_g := h_gap i.1 hi_mem j.1 hj_mem hne1
    have h1 := abs_lt.mp (hy i)
    have h2 := abs_lt.mp (hy j)
    have htri : |i.1 - j.1| ≤ |i.1 - y i| + |y j - j.1| := by
      have : i.1 - j.1 = (i.1 - y i) + (y j - j.1) := by linarith [hij]
      rw [this]; exact abs_add_le _ _
    have h_iy : |i.1 - y i| < r := by rw [abs_sub_comm]; exact hy i
    have h_yj : |y j - j.1| < r := hy j
    linarith [h_gap_r.1]
  let T_y : Finset ℝ := insert zm (Finset.univ.image y)
  have h_zm_notin : zm ∉ Finset.univ.image y := fun hmem => by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
    linarith [h_zm_lt_yi i]
  have h_Ty_card : T_y.card = at47_m P₀ Q₀ := by
    rw [Finset.card_insert_of_notMem h_zm_notin, Finset.card_image_of_injective _ h_yi_inj,
      Finset.card_univ, Fintype.card_coe, Finset.card_erase_of_mem hs₀.2.2.2.1, hs₀.1]
    have := at47_m_ge_two P₀ Q₀ hQ₀
    omega
  have h_Ty_zero : ∀ w ∈ T_y, airyPQN (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) (w : ℂ) = 0 := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hmem
    · exact hzm0
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem; exact hy0 i
  -- Every zero `x` of `N_θ` with `tm₀ - δ_sub / 2 ≤ x` must lie in `T_y`
  have h_no_other_above : ∀ x : ℝ, tm₀ - δ_sub / 2 ≤ x →
      airyPQN (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) (x : ℂ) = 0 → x ∈ T_y := by
    intro x hx_ge hx_zero
    have hx_lt_T : x < Tinf := by
      by_contra hge
      exact hT_nz θ hθ_1 x (not_lt.mp hge) hx_zero
    have hx_in_int : x ∈ Icc (tm₀ - δ_sub / 2) Tinf := ⟨hx_ge, hx_lt_T.le⟩
    have hx_not_K : x ∉ K_out := fun hK => by
      have hc := hc_out x hK
      have hd := h_N_diff_le θ x hx_in_int
      have hx_re0 : (airyPQN (hbPairP P₀ Q₀ θ) (hbPairQ P₀ Q₀ θ) (x : ℂ)).re = 0 := by
        rw [hx_zero]; rfl
      rw [hx_re0, zero_sub, abs_neg] at hd
      linarith
    have h_ex_t : ∃ t ∈ S₀, |x - t| < r := by
      by_contra hno
      push Not at hno
      exact hx_not_K ⟨hx_in_int, Set.mem_iInter₂.mpr hno⟩
    obtain ⟨t, ht_S, hxt⟩ := h_ex_t
    have hx_in_t : x ∈ Icc (t - r) (t + r) := ⟨by linarith [(abs_lt.mp hxt).1], by linarith [(abs_lt.mp hxt).2]⟩
    by_cases htm : t = tm₀
    · subst htm
      have hzm_in : zm ∈ Icc (tm₀ - r) (tm₀ + r) :=
        ⟨by linarith [(abs_lt.mp hzm).1], by linarith [(abs_lt.mp hzm).2]⟩
      have heq := h_inj_interval θ hθ_loc tm₀ ht_S x zm hx_in_t hzm_in hx_zero hzm0
      rw [heq]; exact Finset.mem_insert_self _ _
    · let i : ↥(S₀.erase tm₀) := ⟨t, Finset.mem_erase.mpr ⟨htm, ht_S⟩⟩
      have hyi_in : y i ∈ Icc (t - r) (t + r) :=
        ⟨by linarith [(abs_lt.mp (hy i)).1], by linarith [(abs_lt.mp (hy i)).2]⟩
      have heq := h_inj_interval θ hθ_loc t ht_S x (y i) hx_in_t hyi_in hx_zero (hy0 i)
      rw [heq]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem y (Finset.mem_univ i))
  -- Deduce `hbTopZeros hHB_θ hQ_θ = T_y` and `hbMinZero hHB_θ hQ_θ = zm`
  have hs_θ := hbTopZeros_spec hHB_θ hQ_θ
  let S_θ := hbTopZeros hHB_θ hQ_θ
  have hS_θ_card : S_θ.card = T_y.card := by rw [hs_θ.1, hm_θ, h_Ty_card]
  have h_sub_ST : T_y ⊆ S_θ := by
    intro w hw
    by_contra hw_out
    have h_ex_s : ∃ s ∈ S_θ, s ∉ T_y := by
      by_contra hno
      push Not at hno
      have hsub_TS : S_θ ⊆ T_y := hno
      have hlt_card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub_TS,
        fun heq => hw_out (heq ▸ hw)⟩)
      omega
    obtain ⟨s, hs_S, hs_nT⟩ := h_ex_s
    have hw_lt_s : w < s := hs_θ.2.2.1 w (h_Ty_zero w hw) hw_out s hs_S
    have hs_lt : s < tm₀ - δ_sub / 2 := by
      by_contra hge
      exact hs_nT (h_no_other_above s (not_lt.mp hge) (hs_θ.2.1 s hs_S))
    have hw_ge : tm₀ - δ_sub / 2 ≤ w := by
      rcases Finset.mem_insert.mp hw with rfl | hmem
      · linarith [abs_lt.mp hzm, h_gap_r.2.1]
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
        have := h_zm_lt_yi i
        linarith [abs_lt.mp hzm, h_gap_r.2.1]
    linarith
  have h_eq_ST : S_θ = T_y := (Finset.eq_of_subset_of_card_le h_sub_ST hS_θ_card.ge).symm
  refine ⟨h_zm_lt_yi, h_eq_ST, ?_⟩
  have hzm_in_S : zm ∈ S_θ := h_eq_ST ▸ Finset.mem_insert_self _ _
  have h_zm_le : ∀ w ∈ S_θ, zm ≤ w := fun w hw => by
    rw [h_eq_ST] at hw
    rcases Finset.mem_insert.mp hw with rfl | hmem
    · exact le_rfl
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem; exact (h_zm_lt_yi i).le
  exact le_antisymm (hs_θ.2.2.2.2 zm hzm_in_S) (h_zm_le _ hs_θ.2.2.2.1)

end BoundaryOpenness

/-! ### Part 4: Real-analytic local coordinates via `ContDiffAt.implicitFunction` -/

section ImplicitBoundary

variable {P₀ Q₀ : ℝ[X]} (hHB₀ : AiryPQHB P₀ Q₀) (hQ₀ : Q₀ ≠ 0)

/-- Local Hermite–Biehler coordinate chart around `(P₀, Q₀)`: maps nearby `(m - 1)`-tuples `y`
real-analytically to the normalised pair `(P_y, Q_y)` and terminal node `Z_m(y)`. -/
structure HbBoundaryChart {P₀ Q₀ : ℝ[X]} (hHB₀ : AiryPQHB P₀ Q₀) (hQ₀ : Q₀ ≠ 0) where
  θ : (↥((hbTopZeros hHB₀ hQ₀).erase (hbMinZero hHB₀ hQ₀)) → ℝ) → HbParam P₀ Q₀
  zm : (↥((hbTopZeros hHB₀ hQ₀).erase (hbMinZero hHB₀ hQ₀)) → ℝ) → ℝ
  θ_at_ref : θ (fun i => i.1) = 0
  zm_at_ref : zm (fun i => i.1) = hbMinZero hHB₀ hQ₀
  θ_analytic : ContDiffAt ℝ ω θ (fun i => i.1)
  zm_analytic : ContDiffAt ℝ ω zm (fun i => i.1)
  local_spec : ∀ᶠ y in 𝓝 (fun i => i.1),
    ∃ hHB_y : AiryPQHB (hbPairP P₀ Q₀ (θ y)) (hbPairQ P₀ Q₀ (θ y)),
    ∃ hQ_y : hbPairQ P₀ Q₀ (θ y) ≠ 0,
      at47_m (hbPairP P₀ Q₀ (θ y)) (hbPairQ P₀ Q₀ (θ y)) = at47_m P₀ Q₀ ∧
      (∀ i, zm y < y i) ∧
      hbTopZeros hHB_y hQ_y = insert (zm y) (Finset.univ.image y) ∧
      hbMinZero hHB_y hQ_y = zm y

/-- Existence of the real-analytic local coordinate chart `HbBoundaryChart` around `(P₀, Q₀)`. -/
noncomputable def hbBoundaryChart : HbBoundaryChart hHB₀ hQ₀ := by
  classical
  let S₀ := hbTopZeros hHB₀ hQ₀
  let tm₀ := hbMinZero hHB₀ hQ₀
  have hs₀ := hbTopZeros_spec hHB₀ hQ₀
  let Y₀ := ↥(S₀.erase tm₀)
  let y₀ : Y₀ → ℝ := fun i => i.1
  have hy₀_inj : Function.Injective y₀ := fun a b hab => Subtype.ext hab
  have hY₀_card : Fintype.card Y₀ = at47_m P₀ Q₀ - 1 := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem hs₀.2.2.2.1, hs₀.1]
  have hm2 : 2 ≤ at47_m P₀ Q₀ := at47_m_ge_two P₀ Q₀ hQ₀
  -- Map `Φ(y, θ) i = N_θ(y i)` for `(y, θ) : (Y₀ → ℝ) × HbParam P₀ Q₀`
  let Φ : (Y₀ → ℝ) × HbParam P₀ Q₀ → (Y₀ → ℝ) := fun p i =>
    (hbPairP P₀ Q₀ p.2).eval (p.1 i) * airyAi (p.1 i) +
      (hbPairQ P₀ Q₀ p.2).eval (p.1 i) * airyAi' (p.1 i)
  have hΦ_cd : ContDiffAt ℝ ω Φ (y₀, (0 : HbParam P₀ Q₀)) := by
    refine contDiffAt_pi.mpr fun i => ?_
    exact (hbPair_real_eval_contDiff (g := fun y : Y₀ → ℝ => y i)
      ((ContinuousLinearMap.proj (R := ℝ) (ι := Y₀) (φ := fun _ => ℝ) i).contDiff)).contDiffAt
  have hΦ_0 : Φ (y₀, 0) = 0 := by
    ext i
    dsimp [Φ, y₀]
    have h0P : hbPairP P₀ Q₀ 0 = P₀ := by simp [hbPairP, hbDeltaP]
    have h0Q : hbPairQ P₀ Q₀ 0 = Q₀ := by simp [hbPairQ, hbDeltaQ]
    rw [h0P, h0Q]
    have hi := hs₀.2.1 i.1 (Finset.mem_erase.mp i.2).2
    rw [airyPQN_ofReal] at hi
    exact Complex.ofReal_eq_zero.mp hi
  -- Derivative wrt `θ` at `(y₀, 0)` is linear map `J₀`
  let J₀_lin : HbParam P₀ Q₀ →ₗ[ℝ] (Y₀ → ℝ) :=
    { toFun := fun v i =>
        (hbDeltaP P₀ Q₀ v.1).eval (y₀ i) * airyAi (y₀ i) +
          (hbDeltaQ P₀ Q₀ v.2).eval (y₀ i) * airyAi' (y₀ i)
      map_add' := fun u v => by
        ext i
        have hP : hbDeltaP P₀ Q₀ (u.1 + v.1) = hbDeltaP P₀ Q₀ u.1 + hbDeltaP P₀ Q₀ v.1 := by
          unfold hbDeltaP; simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
        have hQ : hbDeltaQ P₀ Q₀ (u.2 + v.2) = hbDeltaQ P₀ Q₀ u.2 + hbDeltaQ P₀ Q₀ v.2 := by
          unfold hbDeltaQ; simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
        simp only [Prod.fst_add, Prod.snd_add, hP, hQ, Polynomial.eval_add, Pi.add_apply]
        ring
      map_smul' := fun r u => by
        ext i
        have hP : hbDeltaP P₀ Q₀ (r • u.1) = Polynomial.C r * hbDeltaP P₀ Q₀ u.1 := by
          unfold hbDeltaP
          simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
        have hQ : hbDeltaQ P₀ Q₀ (r • u.2) = Polynomial.C r * hbDeltaQ P₀ Q₀ u.2 := by
          unfold hbDeltaQ
          simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by ring
        simp only [Prod.smul_fst, Prod.smul_snd, hP, hQ, Polynomial.eval_mul, Polynomial.eval_C,
          RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        ring }
  let J₀_clm : HbParam P₀ Q₀ →L[ℝ] (Y₀ → ℝ) := J₀_lin.toContinuousLinearMap
  have hJ₀_eq : (fun θ : HbParam P₀ Q₀ => Φ (y₀, θ)) = J₀_clm := by
    ext θ i
    dsimp [Φ, J₀_clm, J₀_lin]
    have hi := hs₀.2.1 i.1 (Finset.mem_erase.mp i.2).2
    rw [airyPQN_ofReal] at hi
    have hi0 := Complex.ofReal_eq_zero.mp hi
    simp only [hbPairP, hbPairQ, Polynomial.eval_add]
    dsimp [y₀] at hi0 ⊢
    linarith
  have hΦ_fderiv_inr :
      fderiv ℝ Φ (y₀, (0 : HbParam P₀ Q₀)) ∘L ContinuousLinearMap.inr ℝ (Y₀ → ℝ) (HbParam P₀ Q₀) =
        J₀_clm := by
    have hω0 : (ω : ℕ∞ω) ≠ 0 := by simp
    have h_diff := hΦ_cd.differentiableAt hω0
    have h_inr : HasFDerivAt (fun θ : HbParam P₀ Q₀ => (y₀, θ))
        (ContinuousLinearMap.inr ℝ (Y₀ → ℝ) (HbParam P₀ Q₀)) 0 :=
      (hasFDerivAt_const y₀ 0).prodMk (hasFDerivAt_id 0)
    have h_comp := h_diff.hasFDerivAt.comp (0 : HbParam P₀ Q₀) h_inr
    have h_J0 : HasFDerivAt (fun θ : HbParam P₀ Q₀ => Φ (y₀, θ)) J₀_clm 0 := by
      rw [hJ₀_eq]; exact J₀_clm.hasFDerivAt
    exact h_comp.unique h_J0
  -- Injectivity of `J₀_lin` via `hb_interpolant_unique_up_to_scale`
  have hJ₀_inj : Function.Injective J₀_lin := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hv0
    have hP₂_nz : hbDeltaP P₀ Q₀ v.1 ≠ 0 ∨ hbDeltaQ P₀ Q₀ v.2 ≠ 0 := by
      by_contra hno; push Not at hno
      exact hv0 (Prod.ext ((hbDeltaP_eq_zero_iff v.1).mp hno.1) ((hbDeltaQ_eq_zero_iff v.2).mp hno.2))
    obtain ⟨c, hc0, hcP, hcQ⟩ := hb_interpolant_unique_up_to_scale hm2 hY₀_card hy₀_inj
      hHB₀ hQ₀ rfl (hbDeltaP_natDegree_le v.1) (hbDeltaQ_natDegree_le v.2) hP₂_nz
      (fun i => hs₀.2.1 i.1 (Finset.mem_erase.mp i.2).2)
      (fun i => by
        rw [airyPQN_ofReal]
        have hvi := congrFun hv i
        dsimp [J₀_lin] at hvi
        exact Complex.ofReal_eq_zero.mpr hvi)
    obtain ⟨_, _, _, hodd₀, heven₀⟩ := at47_degP_degQ_bounds P₀ Q₀ hQ₀
    rcases Nat.mod_two_eq_zero_or_one (at47_m P₀ Q₀) with he | ho
    · have h0 := hbDeltaQ_saturated_coeff_zero he v.2
      rw [hcQ, Polynomial.coeff_C_mul, mul_eq_zero] at h0
      rcases h0 with h | h
      · exact hc0 h
      · exact (heven₀ he).2 h
    · have h0 := hbDeltaP_saturated_coeff_zero ho v.1
      rw [hcP, Polynomial.coeff_C_mul, mul_eq_zero] at h0
      rcases h0 with h | h
      · exact hc0 h
      · exact (hodd₀ ho).2 h
  have hfin_eq : Module.finrank ℝ (HbParam P₀ Q₀) = Module.finrank ℝ (Y₀ → ℝ) := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun,
      Module.finrank_fintype_fun_eq_card, hY₀_card, hbFreeP_add_hbFreeQ hQ₀]
  have hJ₀_surj : Function.Surjective J₀_lin :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin_eq).mp hJ₀_inj
  let e₀ : HbParam P₀ Q₀ ≃ₗ[ℝ] (Y₀ → ℝ) := LinearEquiv.ofBijective J₀_lin ⟨hJ₀_inj, hJ₀_surj⟩
  let J₀_inv : (Y₀ → ℝ) →L[ℝ] HbParam P₀ Q₀ := e₀.symm.toLinearMap.toContinuousLinearMap
  have h_inv_Φ :
      (fderiv ℝ Φ (y₀, (0 : HbParam P₀ Q₀)) ∘L ContinuousLinearMap.inr ℝ (Y₀ → ℝ) (HbParam P₀ Q₀)).IsInvertible := by
    rw [hΦ_fderiv_inr]
    exact ContinuousLinearMap.IsInvertible.of_inverse (g := J₀_inv)
      (ContinuousLinearMap.ext fun y => e₀.apply_symm_apply y)
      (ContinuousLinearMap.ext fun θ => e₀.symm_apply_apply θ)
  have hω0 : (ω : ℕ∞ω) ≠ 0 := by simp
  let θ_fn := hΦ_cd.implicitFunction hω0 h_inv_Φ
  have hθ_cd : ContDiffAt ℝ ω θ_fn y₀ := hΦ_cd.contDiffAt_implicitFunction hω0 h_inv_Φ
  have hθ_0 : θ_fn y₀ = 0 := hΦ_cd.implicitFunction_apply_self hω0 h_inv_Φ
  have hθ_ev : ∀ᶠ y in 𝓝 y₀, Φ (y, θ_fn y) = Φ (y₀, 0) :=
    hΦ_cd.eventually_apply_implicitFunction hω0 h_inv_Φ
  -- Second implicit function: solve `Ψ(y, z) = N_{θ_fn y}(z) = 0` at `(y₀, tm₀)`
  let Ψ : (Y₀ → ℝ) × ℝ → ℝ := fun p =>
    (hbPairP P₀ Q₀ (θ_fn p.1)).eval p.2 * airyAi p.2 +
      (hbPairQ P₀ Q₀ (θ_fn p.1)).eval p.2 * airyAi' p.2
  have hΨ_cd : ContDiffAt ℝ ω Ψ (y₀, tm₀) := by
    have h_inner : ContDiffAt ℝ ω (fun p : (Y₀ → ℝ) × ℝ => (p.2, θ_fn p.1)) (y₀, tm₀) :=
      contDiffAt_snd.prodMk (hθ_cd.comp (y₀, tm₀) contDiffAt_fst)
    exact ((hbPair_real_eval_contDiff (g := fun x : ℝ => x) contDiff_id).contDiffAt).comp
      (y₀, tm₀) h_inner
  have hΨ_0 : Ψ (y₀, tm₀) = 0 := by
    dsimp [Ψ]; rw [hθ_0]
    have h0P : hbPairP P₀ Q₀ 0 = P₀ := by simp [hbPairP, hbDeltaP]
    have h0Q : hbPairQ P₀ Q₀ 0 = Q₀ := by simp [hbPairQ, hbDeltaQ]
    rw [h0P, h0Q]
    have htm := hs₀.2.1 tm₀ hs₀.2.2.2.1
    rw [airyPQN_ofReal] at htm
    exact Complex.ofReal_eq_zero.mp htm
  let c_zm : ℝ := (airyPQN' P₀ Q₀ (tm₀ : ℂ)).re
  have hc_zm_ne : c_zm ≠ 0 := by
    have hzw := airyPQ_zero_weight_pos hHB₀ hQ₀ (hs₀.2.1 tm₀ hs₀.2.2.2.1)
    intro h0
    have hne := hzw.2
    dsimp [c_zm] at h0
    rw [airyPQN'_ofReal, Complex.ofReal_re] at h0
    rw [airyPQN'_ofReal, h0] at hne
    simp at hne
  have hΨ_deriv : ∀ x : ℝ, (fderiv ℝ Ψ (y₀, tm₀) ∘L ContinuousLinearMap.inr ℝ (Y₀ → ℝ) ℝ) x = c_zm * x := by
    have h_diff := hΨ_cd.differentiableAt hω0
    have h_inr : HasFDerivAt (fun z : ℝ => (y₀, z)) (ContinuousLinearMap.inr ℝ (Y₀ → ℝ) ℝ) tm₀ :=
      (hasFDerivAt_const y₀ tm₀).prodMk (hasFDerivAt_id tm₀)
    have h_comp := h_diff.hasFDerivAt.comp tm₀ h_inr
    have h_z_eq : (fun z : ℝ => Ψ (y₀, z)) = fun z : ℝ => (airyPQN P₀ Q₀ (z : ℂ)).re := by
      ext z
      dsimp [Ψ]; rw [hθ_0]
      have h0P : hbPairP P₀ Q₀ 0 = P₀ := by simp [hbPairP, hbDeltaP]
      have h0Q : hbPairQ P₀ Q₀ 0 = Q₀ := by simp [hbPairQ, hbDeltaQ]
      rw [h0P, h0Q, airyPQN_ofReal, Complex.ofReal_re]
    have h_dz : HasDerivAt (fun z : ℝ => (airyPQN P₀ Q₀ (z : ℂ)).re) c_zm tm₀ := by
      have hC := (hasDerivAt_airyPQN P₀ Q₀ (tm₀ : ℂ)).comp_ofReal
      simpa only [c_zm] using hasDerivAt_re_comp hC
    have h_fderiv_inr_1 : (fderiv ℝ Ψ (y₀, tm₀) ∘L ContinuousLinearMap.inr ℝ (Y₀ → ℝ) ℝ) 1 = c_zm := by
      have h_dz' : HasDerivAt (fun z : ℝ => Ψ (y₀, z)) c_zm tm₀ := by
        rw [h_z_eq]
        exact h_dz
      have hh := h_dz'.hasFDerivAt.unique h_comp
      simpa using congrFun (congrArg DFunLike.coe hh.symm) 1
    intro x
    have : ((0 : Y₀ → ℝ), x) = x • ((0 : Y₀ → ℝ), (1 : ℝ)) := by simp
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inr_apply] at h_fderiv_inr_1 ⊢
    rw [this, map_smul, h_fderiv_inr_1, smul_eq_mul, mul_comm]
  have h_inv_Ψ :
      (fderiv ℝ Ψ (y₀, tm₀) ∘L ContinuousLinearMap.inr ℝ (Y₀ → ℝ) ℝ).IsInvertible := by
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := c_zm⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
    · ext; simp [hΨ_deriv, hc_zm_ne]
    · ext; simp [hΨ_deriv, hc_zm_ne]
  let zm_fn := hΨ_cd.implicitFunction hω0 h_inv_Ψ
  have hzm_cd : ContDiffAt ℝ ω zm_fn y₀ := hΨ_cd.contDiffAt_implicitFunction hω0 h_inv_Ψ
  have hzm_0 : zm_fn y₀ = tm₀ := hΨ_cd.implicitFunction_apply_self hω0 h_inv_Ψ
  have hzm_ev : ∀ᶠ y in 𝓝 y₀, Ψ (y, zm_fn y) = Ψ (y₀, tm₀) :=
    hΨ_cd.eventually_apply_implicitFunction hω0 h_inv_Ψ
  refine
    { θ := θ_fn
      zm := zm_fn
      θ_at_ref := hθ_0
      zm_at_ref := hzm_0
      θ_analytic := hθ_cd
      zm_analytic := hzm_cd
      local_spec := ?_ }
  obtain ⟨r, η, hr_pos, hη_pos, h_id⟩ := hbPair_nodes_identify hHB₀ hQ₀
  have h_ev_θ_norm : ∀ᶠ y in 𝓝 y₀, ‖θ_fn y‖ < η := by
    have h_nhds : {x : ℝ | x < η} ∈ 𝓝 ‖θ_fn y₀‖ := by
      rw [hθ_0, norm_zero]; exact Iio_mem_nhds hη_pos
    exact (hθ_cd.continuousAt.tendsto.norm).eventually h_nhds
  have h_ev_zm_dist : ∀ᶠ y in 𝓝 y₀, |zm_fn y - tm₀| < r := by
    have h_nhds : {x : ℝ | x < r} ∈ 𝓝 |zm_fn y₀ - tm₀| := by
      rw [hzm_0, sub_self, abs_zero]; exact Iio_mem_nhds hr_pos
    exact ((hzm_cd.continuousAt.tendsto.sub tendsto_const_nhds).abs).eventually h_nhds
  have h_ev_y_dist : ∀ᶠ y in 𝓝 y₀, ∀ i : Y₀, |y i - i.1| < r := by
    rw [Filter.eventually_all]
    intro i
    have hcont_i : ContinuousAt (fun y : Y₀ → ℝ => |y i - i.1|) y₀ :=
      ((continuous_apply i).sub continuous_const).abs.continuousAt
    exact (hcont_i.tendsto).eventually (by
      have := gt_mem_nhds hr_pos
      simpa [y₀])
  filter_upwards [hθ_ev, hzm_ev, h_ev_θ_norm, h_ev_zm_dist, h_ev_y_dist] with
    y hyθ hyzm hθn hzmd hyd
  obtain ⟨hHB_y, hQ_y, hm_y, h_nid⟩ := h_id (θ_fn y) hθn
  have hzm_zero : airyPQN (hbPairP P₀ Q₀ (θ_fn y)) (hbPairQ P₀ Q₀ (θ_fn y)) (zm_fn y : ℂ) = 0 := by
    rw [airyPQN_ofReal]
    have h1 : Ψ (y, zm_fn y) = 0 := hyzm.trans hΨ_0
    simpa [Ψ] using h1
  have hy_zero : ∀ i : Y₀, airyPQN (hbPairP P₀ Q₀ (θ_fn y)) (hbPairQ P₀ Q₀ (θ_fn y)) (y i : ℂ) = 0 := by
    intro i
    rw [airyPQN_ofReal]
    have h1 : Φ (y, θ_fn y) i = 0 := by rw [hyθ, hΦ_0]; simp
    simpa [Φ] using h1
  exact ⟨hHB_y, hQ_y, hm_y, h_nid y (zm_fn y) hzmd hyd hzm_zero hy_zero⟩

end ImplicitBoundary

/-! ### Part 5: Critical boundary signs (`hbPrescribedI`) and derivative `∂Z_m/∂y_i = -b_i/b_m` -/

section BoundaryConsequences

variable {P₀ Q₀ : ℝ[X]} (hHB₀ : AiryPQHB P₀ Q₀) (hQ₀ : Q₀ ≠ 0)

/-- Feasible normalized integrals for prescribed `(m - 1)`-tuple `y` and terminal threshold `z`. -/
def hbPrescribedSet
    (y : ↥((hbTopZeros hHB₀ hQ₀).erase (hbMinZero hHB₀ hQ₀)) → ℝ) (z : ℝ) : Set ℝ :=
  { r : ℝ | ∃ f : ℂ → ℂ, AiryG f ∧ (∃ x : ℝ, f (x : ℂ) ≠ 0) ∧
    (∀ i : ↥((hbTopZeros hHB₀ hQ₀).erase (hbMinZero hHB₀ hQ₀)), 0 ≤ (f (y i : ℂ)).re) ∧
    (∀ x : ℝ, x ≤ z → 0 ≤ (f (x : ℂ)).re) ∧
    r = (∫ x : ℝ, (f (x : ℂ)).re) / profileMass f }

/-- Critical infimum `I_y(z)` for prescribed sites `y` and terminal threshold `z`. -/
noncomputable def hbPrescribedI
    (y : ↥((hbTopZeros hHB₀ hQ₀).erase (hbMinZero hHB₀ hQ₀)) → ℝ) (z : ℝ) : ℝ :=
  sInf (hbPrescribedSet hHB₀ hQ₀ y z)

lemma hbPrescribedSet_bddBelow
    (y : ↥((hbTopZeros hHB₀ hQ₀).erase (hbMinZero hHB₀ hQ₀)) → ℝ) (z : ℝ) :
    BddBelow (hbPrescribedSet hHB₀ hQ₀ y z) := by
  refine ⟨-1, ?_⟩
  rintro r ⟨f, hf, hnz, _, _, rfl⟩
  have hm : 0 < ∫ x : ℝ, ‖f (x : ℂ)‖ := by
    obtain ⟨x₀, hx₀⟩ := hnz
    exact integral_pos_of_integrable_nonneg_ne_zero
      (hf.diff.continuous.comp continuous_ofReal).norm hf.integrable_norm
      (fun _ => norm_nonneg _) (norm_ne_zero_iff.mpr hx₀)
  have hle : -(∫ x : ℝ, ‖f (x : ℂ)‖) ≤ ∫ x : ℝ, (f (x : ℂ)).re := by
    rw [← integral_neg]
    refine integral_mono hf.integrable_norm.neg hf.integrable_re fun x => ?_
    rw [hf.norm_real x]; exact neg_abs_le _
  change -1 ≤ (∫ x : ℝ, (f (x : ℂ)).re) / ∫ x : ℝ, ‖f (x : ℂ)‖
  exact (le_div_iff₀ hm).mpr (by linarith)

lemma hbPrescribedSet_mono
    (y : ↥((hbTopZeros hHB₀ hQ₀).erase (hbMinZero hHB₀ hQ₀)) → ℝ) {z₁ z₂ : ℝ} (hle : z₁ ≤ z₂) :
    hbPrescribedSet hHB₀ hQ₀ y z₂ ⊆ hbPrescribedSet hHB₀ hQ₀ y z₁ :=
  fun _ ⟨f, hf, hnz, hy, hx, hr⟩ => ⟨f, hf, hnz, hy, fun x h => hx x (h.trans hle), hr⟩

lemma hbPrescribedSet_eq_termSet
    {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0)
    {y : ↥((hbTopZeros hHB₀ hQ₀).erase (hbMinZero hHB₀ hQ₀)) → ℝ} {zm : ℝ}
    (hy_lt : ∀ i, zm < y i)
    (hS : hbTopZeros hHB hQ = insert zm (Finset.univ.image y))
    (htm : hbMinZero hHB hQ = zm) (δ : ℝ) :
    hbPrescribedSet hHB₀ hQ₀ y (zm + δ) = termSet (hbTerminalData hHB hQ) δ := by
  ext r
  constructor
  · rintro ⟨f, hf, hnz, hy, hhalf, hr⟩
    refine ⟨f, hf, hnz, ?_, fun x hx => hhalf x (by simpa [hbTerminalData, htm] using hx), hr⟩
    intro j
    have hj_mem : j.1 ∈ insert zm (Finset.univ.image y) := hS ▸ j.2.1
    have hj_ne : j.1 ≠ zm := htm ▸ j.2.2
    rcases Finset.mem_insert.mp hj_mem with h0 | h1
    · exact absurd h0 hj_ne
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h1
      change 0 ≤ (f (j.1 : ℂ)).re
      rw [← hi]
      exact hy i
  · rintro ⟨f, hf, hnz, hnodes, hhalf, hr⟩
    refine ⟨f, hf, hnz, ?_, fun x hx => hhalf x (by simpa [hbTerminalData, htm] using hx), hr⟩
    intro i
    have hi_mem : y i ∈ (HermiteBiehlerData.ofQNeZero hHB hQ).S := by
      change y i ∈ hbTopZeros hHB hQ
      rw [hS]; exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem y (Finset.mem_univ i))
    have hi_ne : y i ≠ (HermiteBiehlerData.ofQNeZero hHB hQ).tm := by
      change y i ≠ hbMinZero hHB hQ; rw [htm]; exact (hy_lt i).ne'
    exact hnodes ⟨y i, hi_mem, hi_ne⟩

/-- **Local critical boundary signs (`se:terminal-stability`):**
Along `C : HbBoundaryChart hHB₀ hQ₀`, near `y₀`, `hbPrescribedI y z` equals `0` at `z = C.zm y`,
is strictly positive for every `z > C.zm y`, and is strictly negative for every `z < C.zm y`. -/
theorem hb_local_boundary_signs (C : HbBoundaryChart hHB₀ hQ₀) :
    ∀ᶠ y in 𝓝 (fun i => i.1),
      hbPrescribedI hHB₀ hQ₀ y (C.zm y) = 0 ∧
      (∀ z : ℝ, C.zm y < z → 0 < hbPrescribedI hHB₀ hQ₀ y z) ∧
      (∀ z : ℝ, z < C.zm y → hbPrescribedI hHB₀ hQ₀ y z < 0) := by
  filter_upwards [C.local_spec] with y ⟨hHB_y, hQ_y, _, hy_lt_y, hS_y, htm_y⟩
  have hI_eq : ∀ δ : ℝ, hbPrescribedI hHB₀ hQ₀ y (C.zm y + δ) = hbI hHB_y hQ_y δ := fun δ => by
    unfold hbPrescribedI hbI termI
    rw [hbPrescribedSet_eq_termSet hHB₀ hQ₀ hHB_y hQ_y hy_lt_y hS_y htm_y δ]
  have h_zero : hbPrescribedI hHB₀ hQ₀ y (C.zm y) = 0 := by
    have h0 := hI_eq 0
    rw [add_zero] at h0
    rw [h0]
    have hG := hbExtremal_spec hHB_y hQ_y
    have hAiryG : AiryG (hbExtremal hHB_y hQ_y) :=
      ⟨hG.1, hG.2.2.1, hG.2.2.2.1, hG.2.2.2.2.1⟩
    have hmem : (0 : ℝ) ∈ termSet (hbTerminalData hHB_y hQ_y) 0 := by
      refine ⟨hbExtremal hHB_y hQ_y, hAiryG, hG.2.2.2.2.2.2.2.2, ?_,
        fun x hx => hG.2.2.2.2.2.1 x (by simpa [hbTerminalData] using hx), ?_⟩
      · intro j
        have hj := hG.2.2.2.2.2.2.1 j.1 j.2.1
        change 0 ≤ (hbExtremal hHB_y hQ_y (j.1 : ℂ)).re
        rw [hj]; rfl
      · have hint := (hbExtremalProfile (HermiteBiehlerData.ofQNeZero hHB_y hQ_y)).integral_re
        change (∫ x : ℝ, (hbExtremal hHB_y hQ_y (x : ℂ)).re) = 0 at hint
        rw [hint, zero_div]
    exact le_antisymm
      (csInf_le (termSet_bdd (hbTerminalData hHB_y hQ_y) le_rfl) hmem)
      (le_csInf ⟨0, hmem⟩ fun r hr => by
        rcases hr with ⟨f, hf, hnz, hnodes, hhalf, rfl⟩
        have hq := (hb_quad hHB_y hQ_y hf (by simpa [hbTerminalData] using hhalf) hnodes).1
        have hm : 0 < profileMass f := by
          obtain ⟨x₀, hx₀⟩ := hnz
          exact integral_pos_of_integrable_nonneg_ne_zero
            (hf.diff.continuous.comp continuous_ofReal).norm hf.integrable_norm
            (fun _ => norm_nonneg _) (norm_ne_zero_iff.mpr hx₀)
        exact div_nonneg hq hm.le)
  refine ⟨h_zero, fun z hz => ?_, fun z hz => ?_⟩
  · have hδ : 0 < z - C.zm y := sub_pos.mpr hz
    have hpos := (hb_stability hHB_y hQ_y).1 (z - C.zm y) hδ
    have hz_eq := hI_eq (z - C.zm y)
    rw [add_sub_cancel] at hz_eq
    linarith
  · obtain ⟨C_up, δ_up, hC_up, hδ_up, h_up⟩ := hbMultiI_le hHB_y hQ_y
    have hbm := hbNodeCoeff_tm_pos hHB_y hQ_y
    let bm := hbNodeCoeff hHB_y hQ_y (hbMinZero hHB_y hQ_y)
    let ε₀ : ℝ := if C_up = 0 then δ_up / 2 else min (δ_up / 2) (bm / (2 * C_up))
    have hε₀_pos : 0 < ε₀ := by
      dsimp [ε₀]; split_ifs
      · positivity
      · exact lt_min (half_pos hδ_up) (div_pos hbm (by
          have hne : C_up ≠ 0 := by assumption
          have := lt_of_le_of_ne hC_up hne.symm
          linarith))
    let δ₀ : ℝ := max (z - C.zm y) (-ε₀)
    have hδ₀_neg : δ₀ < 0 := max_lt (sub_neg.mpr hz) (neg_lt_zero.mpr hε₀_pos)
    have hδ₀_ge : z ≤ C.zm y + δ₀ := by dsimp [δ₀]; linarith [le_max_left (z - C.zm y) (-ε₀)]
    have hδ₀_abs : |δ₀| < δ_up := by
      rw [abs_of_neg hδ₀_neg]
      have h1 : -δ₀ ≤ ε₀ := by dsimp [δ₀]; linarith [le_max_right (z - C.zm y) (-ε₀)]
      have h2 : ε₀ ≤ δ_up / 2 := by dsimp [ε₀]; split_ifs <;> [exact le_rfl; exact min_le_left _ _]
      linarith
    let h_vec : ↥(hbTopZeros hHB_y hQ_y) → ℝ := fun t =>
      if t.1 = hbMinZero hHB_y hQ_y then δ₀ else 0
    have hh_norm : ‖h_vec‖ = |δ₀| := by
      have h_le : ‖h_vec‖ ≤ |δ₀| := (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun t => by
        dsimp [h_vec]; split_ifs <;> simp [Real.norm_eq_abs]
      have h_ge : |δ₀| ≤ ‖h_vec‖ := by
        have := norm_le_pi_norm h_vec (hbMinNode hHB_y hQ_y)
        simpa [h_vec, hbMinNode] using this
      exact le_antisymm h_le h_ge
    obtain ⟨hne_m, hle_m⟩ := h_up h_vec (by rw [hh_norm]; exact hδ₀_abs)
    have hlin_eq : (∑ t : ↥(hbTopZeros hHB_y hQ_y), hbNodeCoeff hHB_y hQ_y t.1 * h_vec t) =
        bm * δ₀ := by
      rw [Finset.sum_eq_single (hbMinNode hHB_y hQ_y)]
      · simp [h_vec, hbMinNode, bm]
      · intro t _ hne
        have : t.1 ≠ hbMinZero hHB_y hQ_y := fun h => hne (Subtype.ext h)
        simp [h_vec, this]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    have hquad_neg : bm * δ₀ + C_up * |δ₀| ^ 2 < 0 := by
      by_cases hC0 : C_up = 0
      · rw [hC0, zero_mul, add_zero]
        exact mul_neg_of_pos_of_neg hbm hδ₀_neg
      · have hCpos : 0 < C_up := lt_of_le_of_ne hC_up (Ne.symm hC0)
        have h1 : ε₀ ≤ bm / (2 * C_up) := by dsimp [ε₀]; simp [hC0]
        have h2 : |δ₀| ≤ ε₀ := by dsimp [δ₀]; rw [abs_of_neg hδ₀_neg]; linarith [le_max_right (z - C.zm y) (-ε₀)]
        have h3 : C_up * |δ₀| ≤ bm / 2 := by
          calc C_up * |δ₀| ≤ C_up * (bm / (2 * C_up)) := mul_le_mul_of_nonneg_left (h2.trans h1) hCpos.le
            _ = bm / 2 := by field_simp [hCpos.ne']
        have h4 : C_up * |δ₀| ^ 2 ≤ -(bm / 2) * δ₀ := by
          rw [abs_of_neg hδ₀_neg] at h3
          have := mul_le_mul_of_nonneg_right h3 (neg_pos.mpr hδ₀_neg).le
          linarith [show C_up * (-δ₀) * (-δ₀) = C_up * |δ₀| ^ 2 by rw [abs_of_neg hδ₀_neg]; ring]
        linarith [mul_neg_of_pos_of_neg (half_pos hbm) hδ₀_neg]
    have hI_neg : hbI hHB_y hQ_y δ₀ < 0 := by
      rw [← hbMultiI_single_tm hHB_y hQ_y δ₀]
      change hbMultiI hHB_y hQ_y h_vec < 0
      rw [hlin_eq, hh_norm] at hle_m
      linarith
    have hne_δ₀ : (hbPrescribedSet hHB₀ hQ₀ y (C.zm y + δ₀)).Nonempty := by
      rw [hbPrescribedSet_eq_termSet hHB₀ hQ₀ hHB_y hQ_y hy_lt_y hS_y htm_y δ₀,
        ← hbMultiSet_single_tm hHB_y hQ_y δ₀]
      exact hne_m
    have hmono : hbPrescribedI hHB₀ hQ₀ y z ≤ hbPrescribedI hHB₀ hQ₀ y (C.zm y + δ₀) :=
      csInf_le_csInf (hbPrescribedSet_bddBelow hHB₀ hQ₀ y z) hne_δ₀
        (hbPrescribedSet_mono hHB₀ hQ₀ y hδ₀_ge)
    have heq := hI_eq δ₀
    linarith

/-- **Boundary derivative (`se:terminal-stability`, \eqref{se:hb-boundary-diff}):**
Along any real-analytic local coordinate chart `C : HbBoundaryChart hHB₀ hQ₀`, at the reference
`(m - 1)`-tuple `y₀`, `∂Z_m/∂y_i = -b_i / b_m` for every `i ∈ S₀ \ {t_m}`. -/
theorem hb_boundary_diff (C : HbBoundaryChart hHB₀ hQ₀)
    (i : ↥((hbTopZeros hHB₀ hQ₀).erase (hbMinZero hHB₀ hQ₀))) :
    fderiv ℝ C.zm (fun j => j.1) (Pi.single i 1) =
      -(hbNodeCoeff hHB₀ hQ₀ i.1) / hbNodeCoeff hHB₀ hQ₀ (hbMinZero hHB₀ hQ₀) := by
  classical
  let S₀ := hbTopZeros hHB₀ hQ₀
  let tm₀ := hbMinZero hHB₀ hQ₀
  let Y₀ := ↥(S₀.erase tm₀)
  let y₀ : Y₀ → ℝ := fun j => j.1
  let e_i : Y₀ → ℝ := Pi.single i 1
  have hω0 : (ω : ℕ∞ω) ≠ 0 := by simp
  have h_diff_zm : HasFDerivAt C.zm (fderiv ℝ C.zm y₀) y₀ :=
    (C.zm_analytic.differentiableAt hω0).hasFDerivAt
  let d_i : ℝ := fderiv ℝ C.zm y₀ e_i
  have h_deriv_line : HasDerivAt (fun s : ℝ => C.zm (y₀ + s • e_i)) d_i 0 := by
    have h_line : HasDerivAt (fun s : ℝ => y₀ + s • e_i) e_i 0 := by
      simpa using (hasDerivAt_id (0 : ℝ) |>.smul_const e_i).const_add y₀
    have h_diff_zm0 : HasFDerivAt C.zm (fderiv ℝ C.zm y₀) ((fun s : ℝ => y₀ + s • e_i) 0) := by
      simpa using h_diff_zm
    convert h_diff_zm0.comp_hasDerivAt 0 h_line using 1
    rfl
  -- Directional displacement `h_s : ↥S₀ → ℝ` along `y₀ + s • e_i`
  let h_s : ℝ → ↥S₀ → ℝ := fun s t =>
    if ht : t.1 = tm₀ then C.zm (y₀ + s • e_i) - tm₀
    else (y₀ + s • e_i) ⟨t.1, Finset.mem_erase.mpr ⟨ht, t.2⟩⟩ - t.1
  have h_hs_eq : ∀ s : ℝ, ∀ t : ↥S₀,
      h_s s t = if t.1 = tm₀ then C.zm (y₀ + s • e_i) - tm₀
        else if t.1 = i.1 then s else 0 := fun s t => by
    dsimp [h_s]
    split_ifs with h1
    · rfl
    · by_cases hti : t.1 = i.1
      · simp [y₀, e_i, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Subtype.ext_iff, hti]
      · simp [y₀, e_i, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Subtype.ext_iff, hti]
  have h_hs_tend : Tendsto h_s (𝓝 (0 : ℝ)) (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro t
    dsimp [h_s]
    split_ifs with h1
    · have hzm_l := h_deriv_line.continuousAt.tendsto.sub (tendsto_const_nhds (x := tm₀))
      dsimp [y₀, tm₀] at hzm_l ⊢
      rw [zero_smul, add_zero, C.zm_at_ref, sub_self] at hzm_l
      exact hzm_l
    · have h_cont_t : Continuous (fun s : ℝ =>
          (y₀ + s • e_i) ⟨t.1, Finset.mem_erase.mpr ⟨h1, t.2⟩⟩ - t.1) :=
        ((continuous_apply ⟨t.1, Finset.mem_erase.mpr ⟨h1, t.2⟩⟩).comp
          (continuous_const.add (continuous_id.smul continuous_const))).sub continuous_const
      have hct : ContinuousAt (fun s : ℝ =>
          (y₀ + s • e_i) ⟨t.1, Finset.mem_erase.mpr ⟨h1, t.2⟩⟩ - t.1) 0 := h_cont_t.continuousAt
      simpa [y₀] using hct.tendsto
  -- `h_s s` is `O(|s|)` near `0`
  have h_hs_bigO : h_s =O[𝓝 (0 : ℝ)] id := by
    have h_zm_o : (fun s : ℝ => C.zm (y₀ + s • e_i) - tm₀) =O[𝓝 (0 : ℝ)] id := by
      change (fun s : ℝ => C.zm (y₀ + s • e_i) - tm₀) =O[𝓝 (0 : ℝ)] (fun s : ℝ => s)
      dsimp [y₀, tm₀]
      simpa [C.zm_at_ref] using h_deriv_line.isBigO_sub
    rw [Asymptotics.isBigO_iff] at h_zm_o ⊢
    obtain ⟨C₁, hC₁⟩ := h_zm_o
    refine ⟨max C₁ 1, hC₁.mono fun s hs => ?_⟩
    rw [id_eq, pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity : 0 ≤ max C₁ 1) (norm_nonneg s))]
    intro t
    rw [h_hs_eq s t]
    split_ifs with h1 h2
    · exact hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg s))
    · simpa using mul_le_mul_of_nonneg_right (le_max_right C₁ 1) (norm_nonneg s)
    · simp only [norm_zero]; exact mul_nonneg (by positivity) (norm_nonneg s)
  -- `hbMultiI hHB₀ hQ₀ (h_s s) = 0` for `s` near `0`
  have h_line_tend : Tendsto (fun s : ℝ => y₀ + s • e_i) (𝓝 (0 : ℝ)) (𝓝 y₀) := by
    simpa using (tendsto_const_nhds (x := y₀)).add (tendsto_id.smul (tendsto_const_nhds (x := e_i)))
  have h_ev_I0 : ∀ᶠ s in 𝓝 (0 : ℝ), hbMultiI hHB₀ hQ₀ (h_s s) = 0 := by
    filter_upwards [h_line_tend (hb_local_boundary_signs hHB₀ hQ₀ C),
      h_line_tend C.local_spec] with s ⟨hI0, _, _⟩ ⟨_, _, _, _, _, _⟩
    have h_set_eq : hbMultiSet hHB₀ hQ₀ (h_s s) =
        hbPrescribedSet hHB₀ hQ₀ (y₀ + s • e_i) (C.zm (y₀ + s • e_i)) := by
      ext r
      constructor
      · rintro ⟨f, hf, hnz, hnodes, hhalf, hr⟩
        refine ⟨f, hf, hnz, ?_, fun x hx => ?_, hr⟩
        · intro j
          have hj_ne : j.1 ≠ tm₀ := (Finset.mem_erase.mp j.2).1
          have hj_mem : j.1 ∈ S₀ := (Finset.mem_erase.mp j.2).2
          have hnj := hnodes ⟨j.1, hj_mem⟩ hj_ne
          simp only [h_s, S₀, tm₀, hj_ne, ↓reduceDIte, ↓reduceIte] at hnj
          simpa [add_sub_cancel] using hnj
        · have hx' : x ≤ hbMinZero hHB₀ hQ₀ + h_s s (hbMinNode hHB₀ hQ₀) := by
            simp only [h_s, hbMinNode, tm₀, ↓reduceDIte, ↓reduceIte]
            linarith
          exact hhalf x hx'
      · rintro ⟨f, hf, hnz, hy, hhalf, hr⟩
        refine ⟨f, hf, hnz, ?_, fun x hx => ?_, hr⟩
        · intro t ht
          have hyt := hy ⟨t.1, Finset.mem_erase.mpr ⟨ht, t.2⟩⟩
          simp only [h_s, S₀, tm₀, ht, ↓reduceDIte, ↓reduceIte]
          simpa [add_sub_cancel] using hyt
        · have hx' : x ≤ C.zm (y₀ + s • e_i) := by
            simp only [h_s, hbMinNode, tm₀, ↓reduceDIte, ↓reduceIte] at hx
            linarith
          exact hhalf x hx'
    unfold hbMultiI
    rw [h_set_eq]
    exact hI0
  -- Compose `hbMultiI_expansion` with `h_s`
  have h_exp := (hbMultiI_expansion hHB₀ hQ₀).1.comp_tendsto h_hs_tend
  have h_o_s : (fun s : ℝ => hbMultiI hHB₀ hQ₀ (h_s s) -
      ∑ t : ↥S₀, hbNodeCoeff hHB₀ hQ₀ t.1 * h_s s t) =o[𝓝 (0 : ℝ)] id :=
    h_exp.trans_isBigO h_hs_bigO
  have h_lin_s : ∀ s : ℝ, ∑ t : ↥S₀, hbNodeCoeff hHB₀ hQ₀ t.1 * h_s s t =
      hbNodeCoeff hHB₀ hQ₀ i.1 * s +
        hbNodeCoeff hHB₀ hQ₀ tm₀ * (C.zm (y₀ + s • e_i) - tm₀) := by
    intro s
    let t_i : ↥S₀ := ⟨i.1, (Finset.mem_erase.mp i.2).2⟩
    let t_m : ↥S₀ := hbMinNode hHB₀ hQ₀
    have hne_im : t_i ≠ t_m := fun he => (Finset.mem_erase.mp i.2).1 (congrArg Subtype.val he)
    have hzero_off : ∀ t : ↥S₀, t ∉ ({t_i, t_m} : Finset ↥S₀) →
        hbNodeCoeff hHB₀ hQ₀ t.1 * h_s s t = 0 := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
      have ht1 : t.1 ≠ tm₀ := fun h => ht.2 (Subtype.ext h)
      have ht2 : t.1 ≠ i.1 := fun h => ht.1 (Subtype.ext h)
      simp [h_hs_eq s t, ht1, ht2]
    rw [← Finset.sum_subset (Finset.subset_univ {t_i, t_m}) (fun t _ ht => hzero_off t ht)]
    rw [Finset.sum_pair hne_im]
    have hti_val : h_s s t_i = s := by
      have hi_ne : t_i.1 ≠ tm₀ := (Finset.mem_erase.mp i.2).1
      simp [h_hs_eq s t_i, hi_ne, t_i]
    have htm_val : h_s s t_m = C.zm (y₀ + s • e_i) - tm₀ := by
      simp [h_s, t_m, hbMinNode, tm₀]
    rw [hti_val, htm_val]
    rfl
  have h_zm_o2 : (fun s : ℝ => (C.zm (y₀ + s • e_i) - tm₀) - s * d_i) =o[𝓝 (0 : ℝ)] id := by
    change (fun s : ℝ => (C.zm (y₀ + s • e_i) - tm₀) - s * d_i) =o[𝓝 (0 : ℝ)] (fun s : ℝ => s)
    dsimp [y₀, tm₀]
    simpa [sub_zero, smul_eq_mul, C.zm_at_ref] using hasDerivAt_iff_isLittleO.mp h_deriv_line
  have h_comb_o : (fun s : ℝ =>
      -(hbNodeCoeff hHB₀ hQ₀ i.1 + hbNodeCoeff hHB₀ hQ₀ tm₀ * d_i) * s) =o[𝓝 (0 : ℝ)] id := by
    have h1 := h_o_s.congr' (h_ev_I0.mono fun s hs => by simp only; rw [hs, h_lin_s s])
      EventuallyEq.rfl
    have h2 := h_zm_o2.const_mul_left (hbNodeCoeff hHB₀ hQ₀ tm₀)
    refine (h1.add h2).congr (fun s => by ring) (fun _ => rfl)
  have h_coeff0 : -(hbNodeCoeff hHB₀ hQ₀ i.1 + hbNodeCoeff hHB₀ hQ₀ tm₀ * d_i) = 0 := by
    by_contra hne
    rw [Asymptotics.isLittleO_iff] at h_comb_o
    have hpos : 0 < |-(hbNodeCoeff hHB₀ hQ₀ i.1 + hbNodeCoeff hHB₀ hQ₀ tm₀ * d_i)| / 2 :=
      half_pos (abs_pos.mpr hne)
    obtain ⟨δ, hδ_pos, hδ⟩ := Metric.eventually_nhds_iff.mp (h_comb_o hpos)
    have hs_in : dist (δ / 2) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ_pos)]; linarith
    have hs_bd := hδ hs_in
    rw [Real.norm_eq_abs, abs_mul, id_eq, Real.norm_eq_abs,
      abs_of_pos (half_pos hδ_pos)] at hs_bd
    have : |-(hbNodeCoeff hHB₀ hQ₀ i.1 + hbNodeCoeff hHB₀ hQ₀ tm₀ * d_i)| ≤
        |-(hbNodeCoeff hHB₀ hQ₀ i.1 + hbNodeCoeff hHB₀ hQ₀ tm₀ * d_i)| / 2 :=
      le_of_mul_le_mul_right hs_bd (half_pos hδ_pos)
    linarith [abs_pos.mpr hne]
  have hbm_pos := hbNodeCoeff_tm_pos hHB₀ hQ₀
  dsimp [d_i] at h_coeff0
  exact eq_div_of_mul_eq hbm_pos.ne' (by linarith)

/-- **Theorem `se:terminal-stability` (complete multilevel & local boundary statement):**
Combines the asymptotic expansion \eqref{se:multilevel-slope} (`hbMultiI_expansion`), global
uniqueness up to scaling (`hb_interpolant_unique_up_to_scale`), existence of the real-analytic
local Hermite–Biehler boundary chart `Z_m(y)`, local boundary sign characterization, and the
boundary differential formula \eqref{se:hb-boundary-diff} (`∂Z_m/∂y_i = -b_i / b_m`). -/
theorem se_terminal_stability_boundary :
    (fun h : ↥(hbTopZeros hHB₀ hQ₀) → ℝ =>
      hbMultiI hHB₀ hQ₀ h - ∑ t : ↥(hbTopZeros hHB₀ hQ₀), hbNodeCoeff hHB₀ hQ₀ t.1 * h t)
        =o[𝓝 0] id ∧
      0 < hbNodeCoeff hHB₀ hQ₀ (hbMinZero hHB₀ hQ₀) ∧
      ∃ C : HbBoundaryChart hHB₀ hQ₀,
        (∀ᶠ y in 𝓝 (fun i => i.1),
          hbPrescribedI hHB₀ hQ₀ y (C.zm y) = 0 ∧
          (∀ z : ℝ, C.zm y < z → 0 < hbPrescribedI hHB₀ hQ₀ y z) ∧
          (∀ z : ℝ, z < C.zm y → hbPrescribedI hHB₀ hQ₀ y z < 0)) ∧
        (∀ i : ↥((hbTopZeros hHB₀ hQ₀).erase (hbMinZero hHB₀ hQ₀)),
          fderiv ℝ C.zm (fun j => j.1) (Pi.single i 1) =
            -(hbNodeCoeff hHB₀ hQ₀ i.1) / hbNodeCoeff hHB₀ hQ₀ (hbMinZero hHB₀ hQ₀)) :=
  ⟨(hbMultiI_expansion hHB₀ hQ₀).1, (hbMultiI_expansion hHB₀ hQ₀).2.1,
    hbBoundaryChart hHB₀ hQ₀, hb_local_boundary_signs hHB₀ hQ₀ _,
    fun i => hb_boundary_diff hHB₀ hQ₀ _ i⟩

/-- info: 'FormalResearch.ModularBootstrap.Stability.se_terminal_stability_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms se_terminal_stability_boundary

end BoundaryConsequences

end FormalResearch.ModularBootstrap.Stability

