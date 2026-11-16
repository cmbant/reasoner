module

public import Mathlib

/-!
# Weierstrass elementary factors and canonical products (Hadamard factorization, milestone H1)

Statement formalised (Weierstrass 1876; e.g. Conway, *Functions of one complex variable*, VII.5; Titchmarsh,
*The theory of functions*, 8.2; Boas, *Entire functions*, Ch. 2): for `p : ℕ` the elementary factor is
`E_p(w) = (1 - w) exp (w + w²/2 + ⋯ + w^p/p)` (`Hadamard.E p`).

* `Hadamard.E_sub_one_le`: `‖E_p(w) - 1‖ ≤ e^p ‖w‖^{p+1}` for `‖w‖ ≤ 1`.
* `Hadamard.hasProd_E`: if `a : ι → ℂ` has no zero entry and `Σ_i ‖a i‖^{-(p+1)} < ∞`, then the products
  `∏_{i ∈ s} E_p(z / a_i)` converge locally uniformly on `ℂ` (as `s` runs through the finsets of `ι`) to the entire
  function `Hadamard.canonProd p a z = ∏' i, E_p(z / a i)`; `Hadamard.differentiable_canonProd`.
* `Hadamard.canonProd_ne_zero`: it does not vanish off the range of `a`; `Hadamard.canonProd_eq_zero`: it vanishes on the
  range of `a`.
* `Hadamard.logDeriv_canonProd`: off the range of `a`, `Φ'/Φ (z) = Σ_i (z/a_i)^p / (z - a_i)`
  (`Hadamard.logDeriv_E_comp`: the individual factor).

All of these are **proved**.  The order of vanishing of the canonical product at each `a_i` is not treated in this
module; it is `Hadamard.analyticOrderNatAt_canonProd` in `HadamardProductOrder`.
-/

@[expose] public section

open Complex Filter Topology Finset
open scoped BigOperators

namespace FormalResearch.Hadamard

/-- The partial sum `w + w²/2 + ⋯ + w^p/p` of `-log (1 - w)`. -/
noncomputable def S (p : ℕ) (w : ℂ) : ℂ := ∑ k ∈ range p, w ^ (k + 1) / ((k : ℂ) + 1)

/-- The Weierstrass elementary factor `E_p(w) = (1 - w) exp (w + ⋯ + w^p/p)`. -/
noncomputable def E (p : ℕ) (w : ℂ) : ℂ := (1 - w) * cexp (S p w)

lemma S_zero (w : ℂ) : S 0 w = 0 := by simp [S]

lemma E_zero_arg (p : ℕ) : E p 0 = 1 := by simp [E, S]

lemma hasDerivAt_S (p : ℕ) (w : ℂ) : HasDerivAt (S p) (∑ k ∈ range p, w ^ k) w := by
  unfold S
  refine HasDerivAt.fun_sum (fun k _ => ?_)
  have h := (hasDerivAt_pow (k + 1) w).div_const ((k : ℂ) + 1)
  convert h using 1
  have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  push_cast
  field_simp

lemma hasDerivAt_E (p : ℕ) (w : ℂ) : HasDerivAt (E p) (-(w ^ p * cexp (S p w))) w := by
  have h1 : HasDerivAt (fun w : ℂ => 1 - w) (-1) w := by simpa using (hasDerivAt_id w).const_sub 1
  have h2 := (hasDerivAt_S p w).cexp
  have h3 : HasDerivAt (E p) _ w := h1.mul h2
  convert h3 using 1
  have := mul_neg_geom_sum w p
  have e : (-1) * cexp (S p w) + (1 - w) * (cexp (S p w) * ∑ k ∈ range p, w ^ k)
      = -(cexp (S p w)) * (1 - ((1 - w) * ∑ k ∈ range p, w ^ k)) := by ring
  rw [e, this]; ring

lemma differentiable_E (p : ℕ) : Differentiable ℂ (E p) := fun w => (hasDerivAt_E p w).differentiableAt

lemma continuous_E (p : ℕ) : Continuous (E p) := (differentiable_E p).continuous

lemma norm_S_le (p : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖S p w‖ ≤ p := by
  unfold S
  calc ‖∑ k ∈ range p, w ^ (k + 1) / ((k : ℂ) + 1)‖
      ≤ ∑ k ∈ range p, ‖w ^ (k + 1) / ((k : ℂ) + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range p, (1 : ℝ) := by
        refine sum_le_sum fun k _ => ?_
        rw [norm_div, norm_pow]
        have hk : (1 : ℝ) ≤ ‖((k : ℂ) + 1)‖ := by
          have : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
          rw [this, Complex.norm_natCast]; exact_mod_cast Nat.succ_pos k
        calc ‖w‖ ^ (k + 1) / ‖((k : ℂ) + 1)‖ ≤ ‖w‖ ^ (k + 1) / 1 :=
              div_le_div_of_nonneg_left (by positivity) one_pos hk
          _ ≤ 1 := by rw [div_one]; exact pow_le_one₀ (norm_nonneg _) hw
    _ = p := by simp

/-- `‖E_p(w) - 1‖ ≤ e^p ‖w‖^{p+1}` for `‖w‖ ≤ 1`. -/
lemma E_sub_one_le (p : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖E p w - 1‖ ≤ Real.exp p * ‖w‖ ^ (p + 1) := by
  have hconv : Convex ℝ (Metric.closedBall (0 : ℂ) ‖w‖) := convex_closedBall _ _
  have key := hconv.norm_image_sub_le_of_norm_deriv_le (f := E p)
    (C := ‖w‖ ^ p * Real.exp p) (x := 0) (y := w)
    (fun u _ => (differentiable_E p u)) ?_ (by simp) (by simp)
  · simpa [E_zero_arg, pow_succ, mul_comm, mul_assoc, mul_left_comm] using key
  · intro u hu
    rw [(hasDerivAt_E p u).deriv, norm_neg, norm_mul, norm_pow, Complex.norm_exp]
    have hu' : ‖u‖ ≤ ‖w‖ := by simpa using hu
    have hu1 : ‖u‖ ≤ 1 := hu'.trans hw
    refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hu' p) ?_ (Real.exp_pos _).le
      (by positivity)
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (norm_S_le p hu1))

/-- The logarithmic derivative of `z ↦ E_p(z / a)`. -/
lemma logDeriv_E_comp (p : ℕ) {a z : ℂ} (ha : a ≠ 0) (hz : z ≠ a) :
    logDeriv (fun z => E p (z / a)) z = (z / a) ^ p / (z - a) := by
  have h1 : HasDerivAt (fun z : ℂ => z / a) (1 / a) z := by
    simpa using (hasDerivAt_id z).div_const a
  have h2 := (hasDerivAt_E p (z / a)).scomp z h1
  have h3 : deriv (fun z => E p (z / a)) z = _ := h2.deriv
  rw [logDeriv_apply, h3]
  have hza : z - a ≠ 0 := sub_ne_zero.mpr hz
  have hd : (1 - z / a) ≠ 0 := by
    intro h; apply hza; exact sub_eq_zero.mpr ((div_eq_one_iff_eq ha).mp (by linear_combination -h))
  simp only [E, smul_eq_mul]
  have hexp := Complex.exp_ne_zero (S p (z / a))
  field_simp
  ring

/-! ### The canonical product -/

variable {ι : Type*}

/-- The canonical product of genus `p` with zeros `a_i`. -/
noncomputable def canonProd (p : ℕ) (a : ι → ℂ) (z : ℂ) : ℂ := ∏' i, E p (z / a i)

/-- Summability hypothesis: `Σ_i ‖a_i‖^{-(p+1)} < ∞` and no zero entries. -/
structure CanonData (p : ℕ) (a : ι → ℂ) : Prop where
  ne_zero : ∀ i, a i ≠ 0
  summable : Summable fun i => (‖a i‖ ^ (p + 1))⁻¹

lemma CanonData.eventually_ge {p : ℕ} {a : ι → ℂ} (h : CanonData p a) (r : ℝ) :
    ∀ᶠ i in cofinite, r ≤ ‖a i‖ := by
  have ht := h.summable.tendsto_cofinite_zero
  rcases le_or_gt r 0 with hr | hr
  · exact Eventually.of_forall fun i => hr.trans (norm_nonneg _)
  have hpos : 0 < (r ^ (p + 1))⁻¹ := by positivity
  filter_upwards [ht.eventually (gt_mem_nhds hpos)] with i hi
  by_contra hlt
  push Not at hlt
  have hai : 0 < ‖a i‖ := norm_pos_iff.mpr (h.ne_zero i)
  have : r ^ (p + 1) > ‖a i‖ ^ (p + 1) := pow_lt_pow_left₀ hlt hai.le (by omega)
  have := inv_strictAnti₀ (pow_pos hai _) this
  linarith

lemma CanonData.norm_sub_one_le {p : ℕ} {a : ι → ℂ} (h : CanonData p a) {r : ℝ} (_hr : 0 < r)
    {i : ι} (hi : r ≤ ‖a i‖) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖E p (z / a i) - 1‖ ≤ Real.exp p * r ^ (p + 1) * (‖a i‖ ^ (p + 1))⁻¹ := by
  have hai : 0 < ‖a i‖ := norm_pos_iff.mpr (h.ne_zero i)
  have hw : ‖z / a i‖ ≤ 1 := by
    rw [norm_div, div_le_one hai]; exact hz.trans hi
  refine (E_sub_one_le p hw).trans ?_
  rw [norm_div, div_pow, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz _) (by positivity)

/-- The partial products converge locally uniformly on `ℂ` to the canonical product. -/
theorem hasProd_E {p : ℕ} {a : ι → ℂ} (h : CanonData p a) :
    HasProdLocallyUniformlyOn (fun i z => E p (z / a i)) (canonProd p a) Set.univ := by
  have key : HasProdLocallyUniformlyOn (fun i z => 1 + (E p (z / a i) - 1))
      (fun z => ∏' i, (1 + (E p (z / a i) - 1))) Set.univ := by
    apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
    intro K _ hK
    obtain ⟨r, hr⟩ := hK.isBounded.exists_norm_le
    set r' := max r 1 with hr'
    have hr0 : 0 < r' := lt_of_lt_of_le one_pos (le_max_right _ _)
    refine Summable.hasProdUniformlyOn_one_add hK
      (u := fun i => Real.exp p * r' ^ (p + 1) * (‖a i‖ ^ (p + 1))⁻¹)
      (h.summable.mul_left _) ?_ (fun i => ?_)
    · filter_upwards [h.eventually_ge r'] with i hi z hz
      exact h.norm_sub_one_le hr0 hi ((hr z hz).trans (le_max_left _ _))
    · exact (((continuous_E p).comp (continuous_id.div_const (a i))).sub continuous_const).continuousOn
  simp only [add_sub_cancel] at key
  exact key

lemma canonProd_hasProd_at {p : ℕ} {a : ι → ℂ} (h : CanonData p a) (z : ℂ) :
    HasProd (fun i => E p (z / a i)) (canonProd p a z) :=
  (hasProd_E h).hasProd (Set.mem_univ z)

theorem differentiable_canonProd {p : ℕ} {a : ι → ℂ} (h : CanonData p a) :
    Differentiable ℂ (canonProd p a) := by
  have := (hasProd_E h).differentiableOn (.of_forall fun s => ?_) isOpen_univ
  · exact differentiableOn_univ.mp this
  · have := DifferentiableOn.fun_finsetProd (u := s) (f := fun i z => E p (z / a i))
      (𝕜 := ℂ) (s := Set.univ) fun i _ =>
      ((differentiable_E p).comp (differentiable_id.div_const (a i))).differentiableOn
    simpa using this

lemma continuous_canonProd {p : ℕ} {a : ι → ℂ} (h : CanonData p a) :
    Continuous (canonProd p a) := (differentiable_canonProd h).continuous

lemma summable_norm_E_sub_one {p : ℕ} {a : ι → ℂ} (h : CanonData p a) (z : ℂ) :
    Summable fun i => ‖E p (z / a i) - 1‖ := by
  set r := max ‖z‖ 1 with hr
  have hr0 : 0 < r := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine Summable.of_norm_bounded_eventually (g := fun i =>
    Real.exp p * r ^ (p + 1) * (‖a i‖ ^ (p + 1))⁻¹) (h.summable.mul_left _) ?_
  filter_upwards [h.eventually_ge r] with i hi
  rw [norm_norm]
  exact h.norm_sub_one_le hr0 hi (le_max_left _ _)

/-- The canonical product does not vanish off the range of `a`. -/
theorem canonProd_ne_zero {p : ℕ} {a : ι → ℂ} (h : CanonData p a) {z : ℂ}
    (hz : ∀ i, z ≠ a i) : canonProd p a z ≠ 0 := by
  have := tprod_one_add_ne_zero_of_summable (f := fun i => E p (z / a i) - 1) (ι := ι)
    (fun i => ?_) (summable_norm_E_sub_one h z)
  · simpa [canonProd] using this
  · have hai := h.ne_zero i
    have : (1 - z / a i) ≠ 0 := by
      intro e; apply hz i; exact (div_eq_one_iff_eq hai).mp (by linear_combination -e)
    simp [E, this]

/-- The canonical product vanishes at every `a_j`. -/
theorem canonProd_eq_zero {p : ℕ} {a : ι → ℂ} (h : CanonData p a) (j : ι) :
    canonProd p a (a j) = 0 := by
  have hz : E p (a j / a j) = 0 := by simp [E, div_self (h.ne_zero j)]
  exact tprod_of_exists_eq_zero ⟨j, hz⟩

/-- Logarithmic derivative of the canonical product off the zeros. -/
theorem logDeriv_canonProd {p : ℕ} {a : ι → ℂ} (h : CanonData p a) {z : ℂ}
    (hz : ∀ i, z ≠ a i) :
    logDeriv (canonProd p a) z = ∑' i, (z / a i) ^ p / (z - a i) := by
  have hne : ∀ i, E p (z / a i) ≠ 0 := by
    intro i
    have hai := h.ne_zero i
    have : (1 - z / a i) ≠ 0 := by
      intro e; apply hz i; exact (div_eq_one_iff_eq hai).mp (by linear_combination -e)
    simp [E, this]
  have hsum : Summable fun i => logDeriv (fun z => E p (z / a i)) z := by
    set r := max ‖z‖ 1 with hr
    have hr0 : 0 < r := lt_of_lt_of_le one_pos (le_max_right _ _)
    refine Summable.of_norm_bounded_eventually (g := fun i =>
      2 * r ^ p * (‖a i‖ ^ (p + 1))⁻¹) (h.summable.mul_left _) ?_
    filter_upwards [h.eventually_ge (2 * r)] with i hi
    have hai : 0 < ‖a i‖ := norm_pos_iff.mpr (h.ne_zero i)
    have hzr : ‖z‖ ≤ r := le_max_left _ _
    have hza : ‖a i‖ / 2 ≤ ‖z - a i‖ := by
      have := norm_sub_norm_le (a i) z
      rw [norm_sub_rev] at this
      linarith
    rw [logDeriv_E_comp p (h.ne_zero i) (hz i), norm_div, norm_pow, norm_div]
    have hpos : 0 < ‖z - a i‖ := lt_of_lt_of_le (by positivity) hza
    rw [div_le_iff₀ hpos]
    calc (‖z‖ / ‖a i‖) ^ p ≤ (r / ‖a i‖) ^ p := by gcongr
      _ = r ^ p * (‖a i‖ ^ p)⁻¹ := by rw [div_pow, div_eq_mul_inv]
      _ = (2 * r ^ p * (‖a i‖ ^ (p + 1))⁻¹) * (‖a i‖ / 2) := by
        rw [pow_succ]; field_simp
      _ ≤ (2 * r ^ p * (‖a i‖ ^ (p + 1))⁻¹) * ‖z - a i‖ := by gcongr
  have := logDeriv_tprod_eq_tsum isOpen_univ (Set.mem_univ z) (f := fun i z => E p (z / a i))
    hne (fun i => ((differentiable_E p).comp (differentiable_id.div_const (a i))).differentiableOn)
    hsum (hasProd_E h).multipliableLocallyUniformlyOn (canonProd_ne_zero h hz)
  rw [show canonProd p a = fun z => ∏' i, E p (z / a i) from rfl, this]
  exact tsum_congr fun i => logDeriv_E_comp p (h.ne_zero i) (hz i)

end FormalResearch.Hadamard

/-- info: 'FormalResearch.Hadamard.E_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.E_sub_one_le

/-- info: 'FormalResearch.Hadamard.hasProd_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.hasProd_E

/-- info: 'FormalResearch.Hadamard.differentiable_canonProd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.differentiable_canonProd

/-- info: 'FormalResearch.Hadamard.canonProd_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.canonProd_ne_zero

/-- info: 'FormalResearch.Hadamard.canonProd_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.canonProd_eq_zero

/-- info: 'FormalResearch.Hadamard.logDeriv_canonProd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.logDeriv_canonProd
